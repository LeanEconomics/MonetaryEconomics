/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergBoundary

/-!
# Recurrent stationary sunspot equilibria of the exact Rotemberg model

Woodford (2003), *Interest and Prices*, Chapter 4, §2.2 (p. 255: when the Taylor principle fails,
"self-fulfilling" fluctuations driven by sunspots are possible) and Appendix A.3, for the exact
Rotemberg model of `NonlinearRotemberg`, with no fundamental disturbances.

The sunspot is a symmetric two-state Markov chain `P_q = [[1−q, q], [q, 1−q]]` (`Pq`), recurrent
and irreducible for `0 < q < 1`, with the uniform stationary distribution (`Pq_stationary`). The
linearised operator on this chain has a kernel exactly when `1 − 2q` is the root `λ₀ ∈ (0, 1)` of
`g(λ) = (φ_y + σ(1−λ))(1−λβ) + κ(φ_π − λ)`, which exists under strict failure of the Taylor
principle (`exists_lam0`). The nonlinear equilibria bifurcating from the steady state are found by
Lyapunov–Schmidt: writing `z = c(k + y)` and `q = q₀ + τ`, the rescaled conditions `c⁻¹Φ_q(z) = 0`
plus the pin `π(0) − π(1) = 2cθm(σ+ω)` form a map `G_c(τ, y)` that approximates an INVERTIBLE linear
map `A` (`Aop_injective`: the transversality term is positive), and Mathlib's
`ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse` gives a zero.

## Main result

* **`stationary_sunspots`**: under strict failure of the Taylor principle there are `q₀ ∈ (0, ½)`
  and `c₀ > 0` such that for every `0 < |c| < c₀` there is a transition probability
  `q ∈ (0, 1)` and an EXACT stationary Markov equilibrium `z` of the sunspot chain `P_q` with
  `π(0) − π(1) = 2cθm(σ+ω) ≠ 0` and `‖z‖ ≤ K|c|`: a one-parameter family of recurrent sunspot
  equilibria arbitrarily close to the steady state.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergSunspot

open Filter Topology
open scoped NNReal
open NonlinearNKMarkov (Mv IsMarkov chainOp Stochastic)
open NonlinearNKMarkovRamseyIFT (remainder_gen)
open NonlinearRotemberg NonlinearRotembergNewton
open NonlinearRotembergBoundary (norm_DN0_le)

variable {p : Par}

/-! ## The sunspot chain -/

/-- The other state of a two-state chain. -/
def ob (s : Fin 2) : Fin 2 := if s = 0 then 1 else 0

/-- Woodford (2003), Ch. 4, §2.2: the symmetric sunspot chain `[[1−q, q], [q, 1−q]]`. -/
noncomputable def Pq (q : ℝ) (s s' : Fin 2) : ℝ := if s = s' then 1 - q else q

/-- Woodford (2003), Ch. 4, §2.2 (**the sunspot chain is stochastic, irreducible and has the
uniform stationary distribution**) for `0 < q < 1`. -/
theorem Pq_stationary {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Stochastic (Pq q) ∧ 0 < Pq q 0 1 ∧ 0 < Pq q 1 0 ∧
      ∀ s', ∑ s : Fin 2, (1 / 2 : ℝ) * Pq q s s' = 1 / 2 := by
  refine ⟨⟨fun s s' => ?_, fun s => ?_⟩, by simp [Pq, hq0], by simp [Pq, hq0], fun s' => ?_⟩
  · unfold Pq; split_ifs <;> linarith
  · fin_cases s <;> simp [Pq, Fin.sum_univ_two]
  · fin_cases s' <;> simp [Pq, Fin.sum_univ_two] <;> ring

/-- The transition operator of the sunspot chain: `(P_q h)(s) = h(s) + q(h(s̄) − h(s))`. -/
theorem chainOp_Pq (q : ℝ) (h : Fin 2 → ℝ) (s : Fin 2) :
    chainOp (Pq q) h s = h s + q * (h (ob s) - h s) := by
  change ∑ s', Pq q s s' * h s' = _
  fin_cases s <;> simp [Pq, ob, Fin.sum_univ_two] <;> ring

/-! ## The conditions on the sunspot chain -/

/-- The current plus the expected part at the steady-state forecast, `Q(0, x) + N(0, x)`. -/
noncomputable def Psi (p : Par) (x : Fin 3 → ℝ) : Fin 3 → ℝ := Qmap p (0, x) + Nmap p (0, x)

/-- The expected part relative to the steady state, `N(0, x) − N(0, 0)`. -/
noncomputable def Nt (p : Par) (x : Fin 3 → ℝ) : Fin 3 → ℝ := Nmap p (0, x) - Nmap p (0, 0)

/-- Woodford (2003), App. A.3: the exact conditions on the sunspot chain,
`Ψ(z_s) + q(Ñ(z_{s̄}) − Ñ(z_s))`. -/
noncomputable def Phiq (p : Par) (q : ℝ) (z : Fin 2 → Fin 3 → ℝ) (s : Fin 2) : Fin 3 → ℝ :=
  Psi p (z s) + q • (Nt p (z (ob s)) - Nt p (z s))

/-- `Phiq` is the exact Markov-equilibrium map `PhiG` on the sunspot chain without fundamental
disturbances. -/
theorem phiG_eq (q : ℝ) (z : Fin 2 → Fin 3 → ℝ) :
    PhiG (Qmap p) (Nmap p) (chainOp (Pq q)) (fun _ => 0) z = Phiq p q z := by
  funext s i
  simp only [PhiG, Mv, Pi.add_apply, Phiq, Psi, Nt, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [chainOp_Pq]
  ring

/-- `Ψ(0) = 0` (the steady state). -/
theorem Psi_zero : Psi p 0 = 0 := steadyState_zero

/-- `Ñ(0) = 0`. -/
theorem Nt_zero : Nt p 0 = 0 := sub_self _

/-! ## Linear algebra -/

/-- The linearisation of `Ψ`: `DQ v + DN v`. -/
noncomputable def DPsi (p : Par) (v : Fin 3 → ℝ) : Fin 3 → ℝ := DQ0 p v + DN0 p v

/-- `DN` is linear. -/
theorem DN0_lin (a b : ℝ) (u v : Fin 3 → ℝ) :
    DN0 p (a • u + b • v) = a • DN0 p u + b • DN0 p v := by
  funext i; fin_cases i <;> simp [DN0] <;> ring

/-- `DΨ` is linear. -/
theorem DPsi_lin (a b : ℝ) (u v : Fin 3 → ℝ) :
    DPsi p (a • u + b • v) = a • DPsi p u + b • DPsi p v := by
  funext i; fin_cases i <;> simp [DPsi, DQ0, DN0] <;> ring

/-- `DN(u − v) = DNu − DNv`. -/
theorem DN0_sub (u v : Fin 3 → ℝ) : DN0 p (u - v) = DN0 p u - DN0 p v := by
  have := DN0_lin (p := p) 1 (-1) u v
  simpa [sub_eq_add_neg] using this

/-- `DΨ(u − v) = DΨu − DΨv`. -/
theorem DPsi_sub (u v : Fin 3 → ℝ) : DPsi p (u - v) = DPsi p u - DPsi p v := by
  have := DPsi_lin (p := p) 1 (-1) u v
  simpa [sub_eq_add_neg] using this

/-- `DΨ(cu) = c DΨu`. -/
theorem DPsi_smul (c : ℝ) (u : Fin 3 → ℝ) : DPsi p (c • u) = c • DPsi p u := by
  have := DPsi_lin (p := p) c 0 u 0
  simpa using this

/-- `DN(cu) = c DNu`. -/
theorem DN0_smul (c : ℝ) (u : Fin 3 → ℝ) : DN0 p (c • u) = c • DN0 p u := by
  have := DN0_lin (p := p) c 0 u 0
  simpa using this

/-- Woodford (2003), Prop. 4.3: the determinant of the antisymmetric block divided by `ψ`,
`g(λ) = (φ_y + σ(1−λ))(1−λβ) + κ(φ_π − λ)`. -/
noncomputable def gq (p : Par) (l : ℝ) : ℝ :=
  (p.φy + p.σ * (1 - l)) * (1 - l * p.β) + p.κ * (p.φ - l)

/-- Woodford (2003), Prop. 4.3 (**the sunspot root**): under strict failure of the Taylor
principle, `g` has a root `λ₀ ∈ (0, 1)`. -/
theorem exists_lam0 (hp : p.Basic) (hfail : p.κ * (p.φ - 1) + (1 - p.β) * p.φy < 0) :
    ∃ l0, 0 < l0 ∧ l0 < 1 ∧ gq p l0 = 0 := by
  have hκ := hp.κ_pos
  have h0 : 0 < gq p 0 := by
    unfold gq
    have := hp.σ_pos; have := hp.φy_nonneg; have := mul_nonneg hκ.le hp.φ_nonneg
    nlinarith
  have h1 : gq p 1 < 0 := by unfold gq; nlinarith
  have hc : ContinuousOn (gq p) (Set.Icc 0 1) := by unfold gq; fun_prop
  obtain ⟨l, hl, hgl⟩ := intermediate_value_Icc' (zero_le_one) hc
    (show (0 : ℝ) ∈ Set.Icc (gq p 1) (gq p 0) from ⟨h1.le, h0.le⟩)
  refine ⟨l, lt_of_le_of_ne hl.1 ?_, lt_of_le_of_ne hl.2 ?_, hgl⟩
  · rintro rfl; linarith
  · rintro rfl; linarith

/-- Woodford (2003), App. A.3: the kernel direction at a state, `(ψ(1−λ₀β), θm(σ+ω), ψ(1−λ₀β))`. -/
noncomputable def kv (p : Par) (l0 : ℝ) : Fin 3 → ℝ :=
  ![p.ψ * (1 - l0 * p.β), p.θ * p.m * (p.σ + p.ω), p.ψ * (1 - l0 * p.β)]

/-- Woodford (2003), App. A.3: the antisymmetric kernel vector on the chain, `(k, −k)`. -/
noncomputable def kk (p : Par) (l0 : ℝ) (s : Fin 2) : Fin 3 → ℝ :=
  if s = 0 then kv p l0 else -kv p l0

/-- `s̄` of state `0` is `1`. -/
theorem ob_zero : ob 0 = 1 := rfl

/-- `s̄` of state `1` is `0`. -/
theorem ob_one : ob 1 = 0 := rfl

/-- The kernel vector in state `0`. -/
theorem kk_zero (l0 : ℝ) : kk p l0 0 = kv p l0 := rfl

/-- The kernel vector in state `1`. -/
theorem kk_one (l0 : ℝ) : kk p l0 1 = -kv p l0 := rfl

/-- Woodford (2003), App. A.3 (**the kernel**): if `g(λ₀) = 0` and `q₀ = (1 − λ₀)/2`, then
`DΨ(k_s) + q₀(DN k_{s̄} − DN k_s) = 0` in both states. -/
theorem kernel (hp : p.Basic) {l0 : ℝ} (hg : gq p l0 = 0) (s : Fin 2) :
    DPsi p (kk p l0 s) + ((1 - l0) / 2) • (DN0 p (kk p l0 (ob s)) - DN0 p (kk p l0 s)) = 0 := by
  have hk := hp.κ_mul
  unfold gq at hg
  have K0 : (p.φy + p.σ * (1 - l0)) * (p.ψ * (1 - l0 * p.β)) +
      (p.φ - l0) * (p.θ * p.m * (p.σ + p.ω)) = 0 := by
    linear_combination p.ψ * hg - (p.φ - l0) * hk
  funext i
  fin_cases s <;> fin_cases i <;>
    simp [DPsi, DQ0, DN0, kv, ob_zero, ob_one, kk_zero, kk_one] <;> linarith [K0]

/-! ## The linear map `A` and its invertibility -/

/-- The unknowns `(τ, y)`. -/
abbrev Eu := ℝ × (Fin 2 → Fin 3 → ℝ)

/-- Woodford (2003), App. A.3 (**the bordered linearisation**): `A(τ, y) = (π_0 − π_1 of y,
τ(DN k_{s̄} − DN k_s) + DΨ y_s + q₀(DN y_{s̄} − DN y_s))`. -/
noncomputable def Aop (p : Par) (l0 : ℝ) : Eu →ₗ[ℝ] Eu where
  toFun u := (u.2 0 1 - u.2 1 1, fun s => u.1 • (DN0 p (kk p l0 (ob s)) - DN0 p (kk p l0 s)) +
    DPsi p (u.2 s) + ((1 - l0) / 2) • (DN0 p (u.2 (ob s)) - DN0 p (u.2 s)))
  map_add' u v := by
    refine Prod.ext (by simp; ring) ?_
    funext s i
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply]
    have h1 := congrFun (DPsi_lin (p := p) 1 1 (u.2 s) (v.2 s)) i
    have h2 := congrFun (DN0_lin (p := p) 1 1 (u.2 (ob s)) (v.2 (ob s))) i
    have h3 := congrFun (DN0_lin (p := p) 1 1 (u.2 s) (v.2 s)) i
    simp only [one_smul, Pi.add_apply] at h1 h2 h3
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h1, h2, h3]
    ring
  map_smul' c u := by
    refine Prod.ext (by simp; ring) ?_
    funext s i
    simp only [Prod.smul_snd, Prod.smul_fst, RingHom.id_apply, Pi.smul_apply]
    have h1 := congrFun (DPsi_smul (p := p) c (u.2 s)) i
    have h2 := congrFun (DN0_smul (p := p) c (u.2 (ob s))) i
    have h3 := congrFun (DN0_smul (p := p) c (u.2 s)) i
    simp only [Pi.smul_apply, smul_eq_mul] at h1 h2 h3
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h1, h2, h3]
    ring

/-- Woodford (2003), App. A.3 (**`A` is injective**): under strict failure of the Taylor principle
and `0 < λ₀ < 1`, the symmetric block is the nonsingular steady-state Jacobian, and on the
antisymmetric block the pin and the transversality term
`σψ(1−λ₀β) + θm(σ+ω) + (φ_y + σ(1−λ₀))βψ > 0` force `τ = 0` and `y = 0`. -/
theorem Aop_injective (hp : p.Basic) (hfail : p.κ * (p.φ - 1) + (1 - p.β) * p.φy < 0)
    {l0 : ℝ} (hl0 : 0 < l0) (hl1 : l0 < 1) : Function.Injective (Aop p l0) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨τ, y⟩ hu
  have hk := hp.κ_mul
  have hψ := hp.ψ_pos
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hs := hp.σ_pos
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hsω : 0 < p.σ + p.ω := by linarith [hp.ω_nonneg]
  have e0 : y 0 1 - y 1 1 = 0 := congrArg Prod.fst hu
  have e2 := congrArg Prod.snd hu
  have E : ∀ s i, (Aop p l0 (τ, y)).2 s i = 0 := fun s i => by rw [e2]; rfl
  have E00 := E 0 0; have E01 := E 0 1; have E02 := E 0 2
  have E10 := E 1 0; have E11 := E 1 1; have E12 := E 1 2
  simp only [Aop, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, DPsi, DQ0, DN0, kk_zero, kk_one, kv, ob_zero, ob_one, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.isValue, Pi.neg_apply] at E00 E01 E02 E10 E11 E12
  have a02 : y 0 2 = y 0 0 := by linarith
  have a12 : y 1 2 = y 1 0 := by linarith
  simp only [a02, a12] at E00 E01 E10 E11
  -- the symmetric block
  have hsym1 : p.φy * (y 0 0 + y 1 0) + (p.φ - 1) * (y 0 1 + y 1 1) = 0 := by linarith
  have hsym2 : (1 - p.β) * p.ψ * (y 0 1 + y 1 1) - p.θ * p.m * (p.σ + p.ω) * (y 0 0 + y 1 0) = 0 :=
    by linarith
  have hdet : p.ψ * (p.κ * (p.φ - 1) + (1 - p.β) * p.φy) ≠ 0 :=
    mul_ne_zero hψ.ne' (by linarith)
  have hA : y 0 0 + y 1 0 = 0 := by
    have : p.ψ * (p.κ * (p.φ - 1) + (1 - p.β) * p.φy) * (y 0 0 + y 1 0) = 0 := by
      linear_combination (1 - p.β) * p.ψ * hsym1 - (p.φ - 1) * hsym2 +
        (y 0 0 + y 1 0) * (p.φ - 1) * hk
    exact (mul_eq_zero.1 this).resolve_left hdet
  have hB : y 0 1 + y 1 1 = 0 := by
    have : p.ψ * (p.κ * (p.φ - 1) + (1 - p.β) * p.φy) * (y 0 1 + y 1 1) = 0 := by
      linear_combination p.θ * p.m * (p.σ + p.ω) * hsym1 + p.φy * hsym2 +
        (p.φ - 1) * (y 0 1 + y 1 1) * hk
    exact (mul_eq_zero.1 this).resolve_left hdet
  have b0 : y 0 1 = 0 := by linarith
  have b1 : y 1 1 = 0 := by linarith
  simp only [b0, b1] at E00 E01 E10 E11
  -- the antisymmetric block
  have hd1 : 4 * τ * (p.β * p.ψ * (p.θ * p.m * (p.σ + p.ω))) =
      p.θ * p.m * (p.σ + p.ω) * (y 0 0 - y 1 0) := by linarith
  have hd0 : 4 * τ * (p.σ * (p.ψ * (1 - l0 * p.β)) + p.θ * p.m * (p.σ + p.ω)) +
      (p.φy + 2 * ((1 - l0) / 2) * p.σ) * (y 0 0 - y 1 0) = 0 := by linarith
  have hdiff : y 0 0 - y 1 0 = 4 * τ * (p.β * p.ψ) := by
    have h := hd1
    have : p.θ * p.m * (p.σ + p.ω) * (y 0 0 - y 1 0 - 4 * τ * (p.β * p.ψ)) = 0 := by
      linear_combination -h
    have := (mul_eq_zero.1 this).resolve_left (by positivity)
    linarith
  rw [hdiff] at hd0
  clear E00 E01 E02 E10 E11 E12 E e2 hd1 hsym1 hsym2
  have hpos : 0 < p.σ * (p.ψ * (1 - l0 * p.β)) + p.θ * p.m * (p.σ + p.ω) +
      (p.φy + 2 * ((1 - l0) / 2) * p.σ) * (p.β * p.ψ) := by
    have h1 : 0 < 1 - l0 * p.β := by
      have : l0 * p.β < 1 * 1 := mul_lt_mul'' hl1 hβ1 hl0.le hβ.le
      linarith
    have h2 : 0 ≤ p.φy + 2 * ((1 - l0) / 2) * p.σ := by
      have := hp.φy_nonneg; have : 0 ≤ (1 - l0) * p.σ := mul_nonneg (by linarith) hs.le
      linarith
    have := mul_nonneg h2 (mul_pos hβ hψ).le
    have := mul_pos hs (mul_pos hψ h1)
    have := mul_pos hθm hsω
    linarith
  have hτ : τ = 0 := by
    have : 4 * τ * (p.σ * (p.ψ * (1 - l0 * p.β)) + p.θ * p.m * (p.σ + p.ω) +
        (p.φy + 2 * ((1 - l0) / 2) * p.σ) * (p.β * p.ψ)) = 0 := by linear_combination hd0
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  rw [hτ] at hdiff
  have y00 : y 0 0 = 0 := by linarith
  have y10 : y 1 0 = 0 := by linarith
  refine Prod.ext hτ ?_
  funext s i
  fin_cases s <;> fin_cases i <;> simp [y00, y10, b0, b1, a02, a12]


/-! ## First-order remainders -/

/-- Woodford (2003), App. A.3: the uniform first-order remainder of `Ψ`. -/
theorem rem_Psi {η : ℝ} (hη : 0 < η) : ∃ ρ > 0, ∀ a b : Fin 3 → ℝ, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ →
    ‖Psi p a - Psi p b - DPsi p (a - b)‖ ≤ η * ‖a - b‖ := by
  have hc : ContDiff ℝ 1 (fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => Qmap p q + Nmap p q) :=
    contDiff_Qmap.add contDiff_Nmap
  obtain ⟨ρ, hρ, h⟩ := remainder_gen hc hη
  refine ⟨ρ, hρ, fun a b ha hb => ?_⟩
  have h1 := h 0 a b (by simp [hρ.le]) ha hb
  have hd : fderiv ℝ (fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => Qmap p q + Nmap p q) (0, 0)
      (0, a - b) = DPsi p (a - b) := by
    rw [show (fun q : (Fin 3 → ℝ) × (Fin 3 → ℝ) => Qmap p q + Nmap p q) = Qmap p + Nmap p
      from rfl, fderiv_add ((contDiff_Qmap (p := p) (n := 1)).differentiable one_ne_zero _)
      ((contDiff_Nmap (p := p) (n := 1)).differentiable one_ne_zero _)]
    simp only [FunLike.coe_add, Pi.add_apply, fderiv_Qmap_inr, fderiv_Nmap_inr, DPsi]
  rw [hd] at h1
  exact h1

/-- Woodford (2003), App. A.3: the uniform first-order remainder of `Ñ`. -/
theorem rem_Nt {η : ℝ} (hη : 0 < η) : ∃ ρ > 0, ∀ a b : Fin 3 → ℝ, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ →
    ‖Nt p a - Nt p b - DN0 p (a - b)‖ ≤ η * ‖a - b‖ := by
  obtain ⟨ρ, hρ, h⟩ := remainder_gen (contDiff_Nmap (p := p) (n := 1)) hη
  refine ⟨ρ, hρ, fun a b ha hb => ?_⟩
  have h1 := h 0 a b (by simp [hρ.le]) ha hb
  rw [fderiv_Nmap_inr] at h1
  have e : Nt p a - Nt p b = Nmap p (0, a) - Nmap p (0, b) := by simp [Nt]
  rw [e]; exact h1

/-- Woodford (2003), App. A.3 (tool): a remainder bound survives the rescaling `x = c·a`. -/
theorem srem {F DF : (Fin 3 → ℝ) → (Fin 3 → ℝ)} (hDF : ∀ (c : ℝ) v, DF (c • v) = c • DF v)
    {η ρ c : ℝ}
    (hrem : ∀ a b, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ → ‖F a - F b - DF (a - b)‖ ≤ η * ‖a - b‖)
    (hc : c ≠ 0) {a b : Fin 3 → ℝ} (ha : ‖c • a‖ ≤ ρ) (hb : ‖c • b‖ ≤ ρ) :
    ‖c⁻¹ • (F (c • a) - F (c • b)) - DF (a - b)‖ ≤ η * ‖a - b‖ := by
  have h := hrem _ _ ha hb
  have e : c⁻¹ • (F (c • a) - F (c • b)) - DF (a - b) =
      c⁻¹ • (F (c • a) - F (c • b) - DF (c • a - c • b)) := by
    rw [← smul_sub c a b, hDF]
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [e, norm_smul, norm_inv, Real.norm_eq_abs]
  have hn : ‖c • a - c • b‖ = |c| * ‖a - b‖ := by rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  rw [hn] at h
  have hc0 : 0 < |c| := abs_pos.2 hc
  calc |c|⁻¹ * ‖F (c • a) - F (c • b) - DF (c • a - c • b)‖ ≤ |c|⁻¹ * (η * (|c| * ‖a - b‖)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = η * ‖a - b‖ := by field_simp

/-! ## The rescaled map and its linear approximation -/

/-- Woodford (2003), App. A.3 (**the Lyapunov–Schmidt map**): `G_c(τ, y) = (π-difference of y,
c⁻¹Φ_{q₀+τ}(c(k + y)))`. -/
noncomputable def Gc (p : Par) (l0 c : ℝ) (u : Eu) : Eu :=
  (u.2 0 1 - u.2 1 1, fun s => c⁻¹ • Phiq p ((1 - l0) / 2 + u.1) (c • (kk p l0 + u.2)) s)

/-- The state difference of the linearised expected part, `DN v_{s̄} − DN v_s`. -/
noncomputable def LD (p : Par) (v : Fin 2 → Fin 3 → ℝ) (s : Fin 2) : Fin 3 → ℝ :=
  DN0 p (v (ob s)) - DN0 p (v s)

/-- `‖DN v_{s̄} − DN v_s‖ ≤ 2(σ + 1 + βψ)‖v‖`. -/
theorem norm_LD_le (hp : p.Basic) (v : Fin 2 → Fin 3 → ℝ) (s : Fin 2) :
    ‖LD p v s‖ ≤ 2 * (p.σ + 1 + p.β * p.ψ) * ‖v‖ := by
  have h1 := (norm_DN0_le hp (v (ob s))).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v _)
    (by have := hp.σ_pos; have := mul_nonneg hp.β_pos.le hp.ψ_pos.le; linarith))
  have h2 := (norm_DN0_le hp (v s)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v _)
    (by have := hp.σ_pos; have := mul_nonneg hp.β_pos.le hp.ψ_pos.le; linarith))
  calc ‖LD p v s‖ ≤ ‖DN0 p (v (ob s))‖ + ‖DN0 p (v s)‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-- `LD` is linear. -/
theorem LD_sub (v w : Fin 2 → Fin 3 → ℝ) (s : Fin 2) : LD p (v - w) s = LD p v s - LD p w s := by
  simp only [LD, Pi.sub_apply, DN0_sub]; abel

/-- `LD` is additive. -/
theorem LD_add (v w : Fin 2 → Fin 3 → ℝ) (s : Fin 2) : LD p (v + w) s = LD p v s + LD p w s := by
  have h := LD_sub (p := p) (v + w) w s
  simp only [add_sub_cancel_right] at h
  rw [h]; abel

/-- The second block of `G_c` at a state. -/
theorem Gc_snd (l0 c : ℝ) (u : Eu) (s : Fin 2) :
    (Gc p l0 c u).2 s = c⁻¹ • Psi p (c • (kk p l0 + u.2) s) + ((1 - l0) / 2 + u.1) •
      (c⁻¹ • (Nt p (c • (kk p l0 + u.2) (ob s)) - Nt p (c • (kk p l0 + u.2) s))) := by
  simp only [Gc, Phiq, smul_add, Pi.smul_apply]
  rw [smul_comm]

/-- The second block of `A` at a state. -/
theorem Aop_snd (l0 : ℝ) (u : Eu) (s : Fin 2) :
    (Aop p l0 u).2 s = u.1 • LD p (kk p l0) s + DPsi p (u.2 s) + ((1 - l0) / 2) • LD p u.2 s :=
  rfl

/-- Woodford (2003), App. A.3 (**the approximation estimate**): if the remainders of `Ψ` and `Ñ`
are `η`-small on the `ρ`-ball and `|c|(‖k‖ + r₀) ≤ ρ`, then on the `r₀`-ball
`‖G_c u − G_c v − A(u − v)‖ ≤ (4η(‖k‖ + 2) + 4(σ+1+βψ)r₀)‖u − v‖`. -/
theorem approx (hp : p.Basic) {l0 η ρ c r0 : ℝ} (hl0 : 0 < l0) (hl1 : l0 < 1) (hη : 0 ≤ η)
    (hc : c ≠ 0) (hr0 : 0 ≤ r0) (hr01 : r0 ≤ 1)
    (hPsi : ∀ a b, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ → ‖Psi p a - Psi p b - DPsi p (a - b)‖ ≤ η * ‖a - b‖)
    (hN : ∀ a b, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ → ‖Nt p a - Nt p b - DN0 p (a - b)‖ ≤ η * ‖a - b‖)
    (hsm : |c| * (‖kk p l0‖ + r0) ≤ ρ) (u v : Eu) (hu : ‖u‖ ≤ r0) (hv : ‖v‖ ≤ r0) :
    ‖Gc p l0 c u - Gc p l0 c v - Aop p l0 (u - v)‖ ≤
      (4 * η * (‖kk p l0‖ + 2) + 4 * (p.σ + 1 + p.β * p.ψ) * r0) * ‖u - v‖ := by
  obtain ⟨τ, y⟩ := u
  obtain ⟨τ', y'⟩ := v
  set n0 := p.σ + 1 + p.β * p.ψ with hn0
  have hn0p : 0 < n0 := by have := hp.σ_pos; have := mul_nonneg hp.β_pos.le hp.ψ_pos.le; linarith
  set K := ‖kk p l0‖
  have hK : 0 ≤ K := norm_nonneg _
  have hτ : |τ - τ'| ≤ ‖(τ, y) - (τ', y')‖ := by
    have h := norm_fst_le ((τ, y) - (τ', y') : Eu)
    rw [Prod.fst_sub, Real.norm_eq_abs] at h; exact h
  have hy : ‖y - y'‖ ≤ ‖(τ, y) - (τ', y')‖ := by
    have h := norm_snd_le ((τ, y) - (τ', y') : Eu)
    rw [Prod.snd_sub] at h; exact h
  have hτ' : |τ'| ≤ r0 := by
    have h := norm_fst_le ((τ', y') : Eu)
    rw [Real.norm_eq_abs] at h; exact h.trans hv
  have hyn : ‖y‖ ≤ r0 := (norm_snd_le (τ, y)).trans hu
  have hy'n : ‖y'‖ ≤ r0 := (norm_snd_le (τ', y')).trans hv
  set w := kk p l0 + y
  set w' := kk p l0 + y'
  have hw : ∀ s, ‖c • w s‖ ≤ ρ := fun s => by
    rw [norm_smul, Real.norm_eq_abs]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)) hsm
    calc ‖w s‖ ≤ ‖kk p l0 s‖ + ‖y s‖ := norm_add_le _ _
      _ ≤ K + r0 := add_le_add (norm_le_pi_norm _ _) ((norm_le_pi_norm _ _).trans hyn)
  have hw' : ∀ s, ‖c • w' s‖ ≤ ρ := fun s => by
    rw [norm_smul, Real.norm_eq_abs]
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)) hsm
    calc ‖w' s‖ ≤ ‖kk p l0 s‖ + ‖y' s‖ := norm_add_le _ _
      _ ≤ K + r0 := add_le_add (norm_le_pi_norm _ _) ((norm_le_pi_norm _ _).trans hy'n)
  have hz0 : ∀ s : Fin 2, ‖c • (0 : Fin 3 → ℝ)‖ ≤ ρ := fun _ => by
    simp only [smul_zero, norm_zero]
    exact le_trans (by positivity) hsm
  have hww : ∀ s, w s - w' s = y s - y' s := fun s => by simp [w, w']
  have hwnorm : ∀ s, ‖w s - w' s‖ ≤ ‖y - y'‖ := fun s => by
    rw [hww]; exact norm_le_pi_norm (y - y') s
  have hwk : ∀ s, ‖w s‖ ≤ K + r0 := fun s =>
    (norm_add_le _ _).trans (add_le_add (norm_le_pi_norm _ _) ((norm_le_pi_norm _ _).trans hyn))
  set bound := (4 * η * (K + 2) + 4 * n0 * r0) * ‖(τ, y) - (τ', y')‖
  have hb0 : 0 ≤ bound := by positivity
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · have e : (Gc p l0 c (τ, y) - Gc p l0 c (τ', y') - Aop p l0 ((τ, y) - (τ', y'))).1 = 0 := by
      simp only [Gc, Aop, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_sub_mk, Pi.sub_apply]
      ring
    rw [e, norm_zero]; exact hb0
  refine (pi_norm_le_iff_of_nonneg hb0).2 fun s => ?_
  simp only [Prod.snd_sub, Pi.sub_apply]
  rw [Gc_snd, Gc_snd, Aop_snd]
  simp only [Prod.fst_sub, Prod.snd_sub]
  set q0 := (1 - l0) / 2
  have hq0 : 0 ≤ q0 := by simp only [q0]; linarith
  have hq1 : q0 ≤ 1 / 2 := by simp only [q0]; linarith
  set Dw := c⁻¹ • (Nt p (c • w (ob s)) - Nt p (c • w s))
  set Dw' := c⁻¹ • (Nt p (c • w' (ob s)) - Nt p (c • w' s))
  set RP := c⁻¹ • (Psi p (c • w s) - Psi p (c • w' s)) - DPsi p (w s - w' s)
  set R1 := Dw - Dw' - LD p (w - w') s
  set R2 := Dw - LD p w s
  have hLw : LD p w s = LD p (kk p l0) s + LD p y s := LD_add _ _ _
  have hLww : LD p (w - w') s = LD p (y - y') s := by
    congr 1; funext s'; simp [w, w']
  have hLyy : LD p (y - y') s = LD p y s - LD p y' s := LD_sub _ _ _
  have hDP : DPsi p (y s - y' s) = DPsi p (w s - w' s) := by rw [hww]
  have hcw : ∀ s', c • (kk p l0 + y) s' = c • w s' := fun _ => rfl
  have hcw' : ∀ s', c • (kk p l0 + y') s' = c • w' s' := fun _ => rfl
  have key : c⁻¹ • Psi p (c • (kk p l0 + y) s) + (q0 + τ) •
      (c⁻¹ • (Nt p (c • (kk p l0 + y) (ob s)) - Nt p (c • (kk p l0 + y) s))) -
      (c⁻¹ • Psi p (c • (kk p l0 + y') s) + (q0 + τ') •
      (c⁻¹ • (Nt p (c • (kk p l0 + y') (ob s)) - Nt p (c • (kk p l0 + y') s)))) -
      ((τ - τ') • LD p (kk p l0) s + DPsi p ((y - y') s) + q0 • LD p (y - y') s) =
      RP + q0 • R1 + (τ - τ') • (R2 + LD p y s) + τ' • (R1 + LD p (y - y') s) := by
    simp only [hcw, hcw', Pi.sub_apply, RP, R1, R2, hLw, hLww, hLyy, hDP, Dw, Dw']
    rw [smul_sub]
    module
  rw [key]
  -- the four bounds
  have bRP : ‖RP‖ ≤ η * ‖y - y'‖ :=
    (srem (fun c v => DPsi_smul c v) hPsi hc (hw s) (hw' s)).trans
      (mul_le_mul_of_nonneg_left (hwnorm s) hη)
  have bN : ∀ s', ‖c⁻¹ • (Nt p (c • w s') - Nt p (c • w' s')) - DN0 p (w s' - w' s')‖ ≤
      η * ‖y - y'‖ := fun s' =>
    (srem (fun c v => DN0_smul c v) hN hc (hw s') (hw' s')).trans
      (mul_le_mul_of_nonneg_left (hwnorm s') hη)
  have bN0 : ∀ s', ‖c⁻¹ • (Nt p (c • w s') - Nt p (c • 0)) - DN0 p (w s' - 0)‖ ≤
      η * (K + r0) := fun s' =>
    (srem (fun c v => DN0_smul c v) hN hc (hw s') (hz0 s')).trans
      (mul_le_mul_of_nonneg_left (by simpa using hwk s') hη)
  have bR1 : ‖R1‖ ≤ 2 * η * ‖y - y'‖ := by
    have e : R1 = (c⁻¹ • (Nt p (c • w (ob s)) - Nt p (c • w' (ob s))) -
        DN0 p (w (ob s) - w' (ob s))) -
        (c⁻¹ • (Nt p (c • w s) - Nt p (c • w' s)) - DN0 p (w s - w' s)) := by
      simp only [R1, Dw, Dw', LD, Pi.sub_apply, DN0_sub, smul_sub]; abel
    rw [e]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ η * ‖y - y'‖ + η * ‖y - y'‖ := add_le_add (bN _) (bN _)
      _ = _ := by ring
  have bR2 : ‖R2‖ ≤ 2 * η * (K + r0) := by
    have e : R2 = (c⁻¹ • (Nt p (c • w (ob s)) - Nt p (c • 0)) - DN0 p (w (ob s) - 0)) -
        (c⁻¹ • (Nt p (c • w s) - Nt p (c • 0)) - DN0 p (w s - 0)) := by
      simp only [R2, Dw, LD, smul_zero, Nt_zero, sub_zero, smul_sub]; abel
    rw [e]
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ η * (K + r0) + η * (K + r0) := add_le_add (bN0 _) (bN0 _)
      _ = _ := by ring
  have bLy : ‖LD p y s‖ ≤ 2 * n0 * r0 :=
    (norm_LD_le hp y s).trans (mul_le_mul_of_nonneg_left hyn (by positivity))
  have bLyy : ‖LD p (y - y') s‖ ≤ 2 * n0 * ‖y - y'‖ := norm_LD_le hp _ s
  have hyy := norm_nonneg (y - y')
  calc ‖RP + q0 • R1 + (τ - τ') • (R2 + LD p y s) + τ' • (R1 + LD p (y - y') s)‖
      ≤ ‖RP‖ + q0 * ‖R1‖ + |τ - τ'| * (‖R2‖ + ‖LD p y s‖) +
          |τ'| * (‖R1‖ + ‖LD p (y - y') s‖) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)) ?_)
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
    _ ≤ η * ‖y - y'‖ + 1 / 2 * (2 * η * ‖y - y'‖) +
          ‖(τ, y) - (τ', y')‖ * (2 * η * (K + r0) + 2 * n0 * r0) +
          r0 * (2 * η * ‖y - y'‖ + 2 * n0 * ‖y - y'‖) := by
        gcongr
    _ ≤ bound := by
        simp only [bound]
        have h1 : η * ‖y - y'‖ ≤ η * ‖(τ, y) - (τ', y')‖ := mul_le_mul_of_nonneg_left hy hη
        have h2 : r0 * (2 * η * ‖y - y'‖ + 2 * n0 * ‖y - y'‖) ≤
            r0 * (2 * η + 2 * n0) * ‖(τ, y) - (τ', y')‖ := by
          rw [show r0 * (2 * η * ‖y - y'‖ + 2 * n0 * ‖y - y'‖) =
            r0 * (2 * η + 2 * n0) * ‖y - y'‖ by ring]
          exact mul_le_mul_of_nonneg_left hy (by positivity)
        have h3 := norm_nonneg ((τ, y) - (τ', y'))
        have h4 : r0 * (2 * η) ≤ 2 * η := by nlinarith
        have h5 : η * r0 ≤ η := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right h4 h3, mul_le_mul_of_nonneg_right h5 h3,
          mul_nonneg hK hη, mul_nonneg (mul_nonneg hK hη) h3, mul_nonneg hη h3]

/-- Woodford (2003), App. A.3 (**the residual at the origin**): `‖G_c(0)‖ ≤ 2η‖k‖`. -/
theorem Gc_zero_le (hp : p.Basic) {l0 η ρ c : ℝ} (hl0 : 0 < l0) (hl1 : l0 < 1)
    (hg : gq p l0 = 0) (hη : 0 ≤ η) (hc : c ≠ 0)
    (hPsi : ∀ a b, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ → ‖Psi p a - Psi p b - DPsi p (a - b)‖ ≤ η * ‖a - b‖)
    (hN : ∀ a b, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ → ‖Nt p a - Nt p b - DN0 p (a - b)‖ ≤ η * ‖a - b‖)
    (hsm : |c| * ‖kk p l0‖ ≤ ρ) : ‖Gc p l0 c 0‖ ≤ 2 * η * ‖kk p l0‖ := by
  set K := ‖kk p l0‖
  have hK : 0 ≤ K := norm_nonneg _
  have hb0 : 0 ≤ 2 * η * K := by positivity
  have hk : ∀ s, ‖c • kk p l0 s‖ ≤ ρ := fun s => by
    rw [norm_smul, Real.norm_eq_abs]
    exact le_trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ _) (abs_nonneg c)) hsm
  have h0 : ‖c • (0 : Fin 3 → ℝ)‖ ≤ ρ := by
    simp only [smul_zero, norm_zero]; exact le_trans (by positivity) hsm
  rw [Prod.norm_def]
  refine max_le (by simp [Gc, hb0]) ((pi_norm_le_iff_of_nonneg hb0).2 fun s => ?_)
  rw [Gc_snd]
  simp only [Prod.snd_zero, Prod.fst_zero, add_zero]
  set q0 := (1 - l0) / 2
  have hq0 : 0 ≤ q0 := by simp only [q0]; linarith
  have hq1 : q0 ≤ 1 / 2 := by simp only [q0]; linarith
  have hker := kernel hp hg s
  have e : c⁻¹ • Psi p (c • kk p l0 s) + q0 • (c⁻¹ • (Nt p (c • kk p l0 (ob s)) -
      Nt p (c • kk p l0 s))) =
      (c⁻¹ • (Psi p (c • kk p l0 s) - Psi p (c • 0)) - DPsi p (kk p l0 s - 0)) +
      q0 • ((c⁻¹ • (Nt p (c • kk p l0 (ob s)) - Nt p (c • 0)) - DN0 p (kk p l0 (ob s) - 0)) -
        (c⁻¹ • (Nt p (c • kk p l0 s) - Nt p (c • 0)) - DN0 p (kk p l0 s - 0))) := by
    simp only [smul_zero, Psi_zero, Nt_zero, sub_zero]
    rw [← sub_eq_zero]
    have : DPsi p (kk p l0 s) = -(q0 • (DN0 p (kk p l0 (ob s)) - DN0 p (kk p l0 s))) := by
      rw [eq_neg_iff_add_eq_zero]; exact hker
    rw [this]
    simp only [smul_sub]
    abel
  rw [e]
  have b1 := srem (fun c v => DPsi_smul c v) hPsi hc (hk s) h0
  have b2 := srem (fun c v => DN0_smul c v) hN hc (hk (ob s)) h0
  have b3 := srem (fun c v => DN0_smul c v) hN hc (hk s) h0
  simp only [sub_zero] at b1 b2 b3
  have n1 : ‖kk p l0 s‖ ≤ K := norm_le_pi_norm _ _
  have n2 : ‖kk p l0 (ob s)‖ ≤ K := norm_le_pi_norm _ _
  calc _ ≤ ‖c⁻¹ • (Psi p (c • kk p l0 s) - Psi p (c • 0)) - DPsi p (kk p l0 s)‖ +
        q0 * (‖c⁻¹ • (Nt p (c • kk p l0 (ob s)) - Nt p (c • 0)) - DN0 p (kk p l0 (ob s))‖ +
          ‖c⁻¹ • (Nt p (c • kk p l0 s) - Nt p (c • 0)) - DN0 p (kk p l0 s)‖) := by
        simp only [sub_zero]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) hq0
    _ ≤ η * K + 1 / 2 * (η * K + η * K) := by
        gcongr
        · exact b1.trans (mul_le_mul_of_nonneg_left n1 hη)
        · exact b2.trans (mul_le_mul_of_nonneg_left n2 hη)
        · exact b3.trans (mul_le_mul_of_nonneg_left n1 hη)
    _ = 2 * η * K := by ring

/-! ## Existence of recurrent stationary sunspot equilibria -/

/-- Woodford (2003), Ch. 4, §2.2 and App. A.3 (**RECURRENT STATIONARY SUNSPOT EQUILIBRIA**): under
strict failure of the Taylor principle `κ(φ_π − 1) + (1 − β)φ_y < 0`, there are `q₀ ∈ (0, ½)`,
`c₀ > 0` and `K` such that for every `0 < |c| < c₀` there is a transition probability
`q ∈ (0, 1)` (so the sunspot chain `P_q` is irreducible and recurrent with the uniform stationary
distribution, `Pq_stationary`) and an exact Markov equilibrium `z` of the sunspot chain without
fundamental disturbances, with `π(0) − π(1) = 2cθm(σ+ω) ≠ 0` and `‖z_s‖ ≤ K|c|`. -/
theorem stationary_sunspots (hp : p.Basic) (hfail : p.κ * (p.φ - 1) + (1 - p.β) * p.φy < 0) :
    ∃ q0 : ℝ, 0 < q0 ∧ q0 < 1 / 2 ∧ ∃ c0 > 0, ∃ Kz : ℝ, ∀ c : ℝ, c ≠ 0 → |c| < c0 →
      ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ z : Fin 2 → Fin 3 → ℝ,
        PhiG (Qmap p) (Nmap p) (chainOp (Pq q)) (fun _ => 0) z = 0 ∧
        z 0 1 - z 1 1 = 2 * c * (p.θ * p.m * (p.σ + p.ω)) ∧ ∀ s, ‖z s‖ ≤ Kz * |c| := by
  obtain ⟨l0, hl0, hl1, hg⟩ := exists_lam0 hp hfail
  set q0 := (1 - l0) / 2 with hq0d
  have hq0 : 0 < q0 := by simp only [q0]; linarith
  have hq1 : q0 < 1 / 2 := by simp only [q0]; linarith
  set Ae := (LinearEquiv.ofInjectiveEndo (Aop p l0)
    (Aop_injective hp hfail hl0 hl1)).toContinuousLinearEquiv
  have hAe : ∀ x, Ae x = Aop p l0 x := fun x => rfl
  set N := ‖(Ae.symm : Eu →L[ℝ] Eu)‖ with hN
  have hNpos : 0 < N := by
    have h := (Ae.symm : Eu →L[ℝ] Eu).le_opNorm (Ae ((1 : ℝ), 0))
    have e : (Ae.symm : Eu →L[ℝ] Eu) (Ae ((1 : ℝ), 0)) = ((1 : ℝ), 0) := Ae.symm_apply_apply _
    rw [e] at h
    have h1 : ‖(((1 : ℝ), 0) : Eu)‖ = 1 := by simp [Prod.norm_def]
    rw [h1] at h
    by_contra hh
    push Not at hh
    have : N * ‖Ae ((1 : ℝ), 0)‖ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hh (norm_nonneg _)
    linarith
  set μ := N⁻¹ with hμ
  have hμ0 : 0 < μ := inv_pos.2 hNpos
  set n0 := p.σ + 1 + p.β * p.ψ with hn0
  have hn0p : 0 < n0 := by have := hp.σ_pos; have := mul_nonneg hp.β_pos.le hp.ψ_pos.le; linarith
  set K := ‖kk p l0‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  set r0 := min (q0 / 2) (μ / (16 * n0)) with hr0
  have hr00 : 0 < r0 := lt_min (by positivity) (by positivity)
  have hr0q : r0 ≤ q0 / 2 := min_le_left _ _
  have hr0n : r0 ≤ μ / (16 * n0) := min_le_right _ _
  have hr01 : r0 ≤ 1 := by linarith
  set η := μ * r0 / (16 * (K + 2)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρ1, hρ1, hP⟩ := rem_Psi (p := p) hη0
  obtain ⟨ρ2, hρ2, hNt⟩ := rem_Nt (p := p) hη0
  set ρ := min ρ1 ρ2
  have hρ : 0 < ρ := lt_min hρ1 hρ2
  have hP' : ∀ a b, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ → ‖Psi p a - Psi p b - DPsi p (a - b)‖ ≤ η * ‖a - b‖ :=
    fun a b ha hb => hP a b (ha.trans (min_le_left _ _)) (hb.trans (min_le_left _ _))
  have hN' : ∀ a b, ‖a‖ ≤ ρ → ‖b‖ ≤ ρ → ‖Nt p a - Nt p b - DN0 p (a - b)‖ ≤ η * ‖a - b‖ :=
    fun a b ha hb => hNt a b (ha.trans (min_le_right _ _)) (hb.trans (min_le_right _ _))
  refine ⟨q0, hq0, hq1, ρ / (K + r0 + 1), by positivity, K + r0, fun c hc hcs => ?_⟩
  have hsm : |c| * (K + r0) ≤ ρ := by
    rw [lt_div_iff₀ (by positivity)] at hcs
    nlinarith [abs_nonneg c]
  have hsm0 : |c| * K ≤ ρ := le_trans (by nlinarith [abs_nonneg c]) hsm
  -- the approximation on the `r₀`-ball
  have hcap : 4 * η * (K + 2) + 4 * n0 * r0 ≤ μ / 2 := by
    have e1 : 4 * η * (K + 2) = μ * r0 / 4 := by simp only [η]; field_simp; ring
    have e2 : 4 * n0 * r0 ≤ μ / 4 := by
      have := mul_le_mul_of_nonneg_left hr0n (by positivity : 0 ≤ 4 * n0)
      calc 4 * n0 * r0 ≤ 4 * n0 * (μ / (16 * n0)) := this
        _ = μ / 4 := by field_simp; ring
    have e3 : μ * r0 / 4 ≤ μ / 4 := by
      have := mul_le_mul_of_nonneg_left hr01 hμ0.le; linarith
    linarith
  have hμ2 : (0 : ℝ) ≤ μ / 2 := by positivity
  have hA : ApproximatesLinearOn (Gc p l0 c) (Ae : Eu →L[ℝ] Eu) (Metric.closedBall 0 r0)
      ⟨μ / 2, hμ2⟩ := by
    intro u hu v hv
    rw [Metric.mem_closedBall, dist_zero_right] at hu hv
    change ‖Gc p l0 c u - Gc p l0 c v - Ae (u - v)‖ ≤ μ / 2 * ‖u - v‖
    rw [hAe]
    exact (approx hp hl0 hl1 hη0.le hc hr00.le hr01 hP' hN' hsm u v hu hv).trans
      (mul_le_mul_of_nonneg_right hcap (norm_nonneg _))
  have hS := hA.surjOn_closedBall_of_nonlinearRightInverse Ae.toNonlinearRightInverse
    hr00.le subset_rfl
  have hnn : ((Ae.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ) = N := rfl
  have hmem : (0 : Eu) ∈ Metric.closedBall (Gc p l0 c 0)
      ((((Ae.toNonlinearRightInverse.nnnorm : ℝ≥0) : ℝ)⁻¹ - ((⟨μ / 2, hμ2⟩ : ℝ≥0) : ℝ)) * r0) := by
    rw [Metric.mem_closedBall, dist_comm, dist_zero_right, hnn]
    have h1 := Gc_zero_le hp hl0 hl1 hg hη0.le hc hP' hN' hsm0
    have h2 : 2 * η * K ≤ μ * r0 / 8 := by
      simp only [η]
      rw [show 2 * (μ * r0 / (16 * (K + 2))) * K = μ * r0 / 8 * (K / (K + 2)) by
        field_simp; ring]
      have : K / (K + 2) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ μ * r0 / 8)
      linarith
    change ‖Gc p l0 c 0‖ ≤ (N⁻¹ - μ / 2) * r0
    rw [← hμ]
    nlinarith
  obtain ⟨u, hu, hzero⟩ := hS hmem
  rw [Metric.mem_closedBall, dist_zero_right] at hu
  obtain ⟨τ, y⟩ := u
  have hτ : |τ| ≤ r0 := by
    have h := norm_fst_le ((τ, y) : Eu)
    rw [Real.norm_eq_abs] at h; exact h.trans hu
  have hyn : ‖y‖ ≤ r0 := (norm_snd_le (τ, y)).trans hu
  refine ⟨q0 + τ, ?_, ?_, c • (kk p l0 + y), ?_, ?_, fun s => ?_⟩
  · have := (abs_le.1 hτ).1; linarith
  · have := (abs_le.1 hτ).2; linarith
  · rw [phiG_eq]
    funext s
    have h2 := congrFun (congrArg Prod.snd hzero) s
    simp only [Gc, Prod.snd_zero, Pi.zero_apply] at h2
    exact (smul_eq_zero.1 h2).resolve_left (inv_ne_zero hc)
  · have h1 := congrArg Prod.fst hzero
    simp only [Gc, Prod.fst_zero] at h1
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, kk_zero, kk_one, kv, Pi.neg_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    linear_combination c * h1
  · rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg c)
    exact (norm_add_le _ _).trans (add_le_add (norm_le_pi_norm _ _)
      ((norm_le_pi_norm _ _).trans hyn))

end Woodford.StabilizationWelfare.NonlinearRotembergSunspot
