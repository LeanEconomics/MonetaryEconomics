/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.ExpectationsMeasure
import GainsFromCommitment.Noninertial

/-!
# Stabilization losses with genuine conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 7, §3, pp. 507–513 (the stabilization loss
`L^stab = ∑_{t ≥ t₀} β^{t−t₀} [var_{t₀}(π_t) + λ var_{t₀}(x_t)]` of p. 509, eqs. (3.2)–(3.8),
Proposition 7.11) and Appendix F.4, pp. 713–714.

The variance results of `VarianceFrontier` and `Noninertial` are stated for the core
`ExpectationSystem` and assume AR(1) disturbances whose innovations have constant conditional
variance, together with the pull-out property. On a finite state space such disturbances are
degenerate (`finite_innov_degenerate`, `tree_innov_degenerate`: the conditional variance must be
`0`), so those statements only have content for genuine probability models. Here they are proved
again for a `MeasExpectationSystem` (Mathlib's `condExp` on a filtered probability space): the
conditional variances are Mathlib's `Var[X; μ | 𝓕 t]` (genuine conditional expectations of
squared deviations), every identity holds almost everywhere, and the pull-out property is a
theorem, not a hypothesis. The genuine i.i.d. instance is in `NoninertialMeasureIID`.

## Main results

* `MeasAR1Innov` ((2.18), (2.27)): bounded adapted AR(1) disturbances with martingale-difference
  innovations of constant conditional variance.
* `E_cross_dev`, `condVar_plan2`, `condVar_plan1` (p. 509, p. 512): conditional (co)variances of
  AR(1) disturbances and of the plans (2.19), (3.6).
* `lstab12_hasSum`, `lstab12_eq` ((3.4)) and `lstab_hasSum`, `lstab_eq` ((3.7)–(3.8)): the
  stabilization loss as a genuine discounted sum of conditional variances, almost surely.
* `affine_zero1`, `affine_zero2`, `plan_AS_iff` ((3.2)–(3.3)), `plan2_iff` ((3.6) and the six
  restrictions): non-degeneracy is now a consequence of a positive innovation variance.
* `prop_7_11_lstab` (**Proposition 7.11**, stabilization form) and `f4_lstab` (**Appendix F.4**,
  stabilization optimality).
* Links to the core statements: on a finite fully supported space `toCore_AR1Innov`,
  `toCore_VF_AR1Innov`, `toCore_nondeg1`, `toCore_nondeg2`, `mAS_iff_core`, `mIS_iff_core`,
  `condVar_eq_condCov`, `lstab12_agree`, `lstab_agree`, and the core theorems applied through the
  bridge (`lstab12_link`, `lstab_link`, `prop_7_11_link`, `f4_link`, `Lstab_ar1_link`,
  `Lstab_two_shocks_link`); `finite_innov_degenerate`, `tree_innov_degenerate` show why the
  bridge cannot carry a nondegenerate disturbance.
-/

namespace Woodford.GainsFromCommitment.NoninertialMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure
open VarianceFrontier (plan2 plan2_apply)
open Noninertial (plan1 fpiOni fxOni uncondVar)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### AR(1) disturbances with innovations of constant conditional variance -/

/-- Woodford (2003), eqs. (2.18) and (2.27), pp. 496 and 504, with genuine conditional
expectations: `u` is a bounded adapted AR(1) process `u_{t+1} = ρ u_t + ε_{t+1}` whose innovation
is unforecastable, `E_t ε_{t+1} = 0`, with constant conditional variance `E_t ε_{t+1}² = s`
(both almost surely). -/
def MeasAR1Innov (ρ s : ℝ) (u ε : ℕ → Ω → ℝ) : Prop :=
  StronglyAdapted S.𝓕 u ∧ S.BddProc u ∧ (∀ t, u (t + 1) = ρ • u t + ε (t + 1)) ∧
    (∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) ∧
    ∀ t, S.E t (ε (t + 1) * ε (t + 1)) =ᵐ[S.μ] fun _ => s

namespace MeasAR1Innov

variable {S} {ρ s : ℝ} {u ε : ℕ → Ω → ℝ}

/-- Woodford (2003), eq. (2.18), p. 496: each `u_t` is a bounded random variable. -/
theorem bddRV (h : MeasAR1Innov S ρ s u ε) (t : ℕ) : S.BddRV (u t) := by
  obtain ⟨M, hM⟩ := h.2.1
  exact MeasExpectationSystem.BddRV.of_stronglyMeasurable (h.1 t) (hM t)

/-- Woodford (2003), eq. (2.18), p. 496: the innovation is `ε_{t+1} = u_{t+1} − ρ u_t`. -/
theorem innov_eq (h : MeasAR1Innov S ρ s u ε) (t : ℕ) : ε (t + 1) = u (t + 1) - ρ • u t := by
  rw [h.2.2.1 t, add_sub_cancel_left]

/-- Woodford (2003), eq. (2.18), p. 496: the innovation is a bounded random variable. -/
theorem innov_bddRV (h : MeasAR1Innov S ρ s u ε) (t : ℕ) : S.BddRV (ε (t + 1)) := by
  rw [h.innov_eq t]
  exact (h.bddRV _).sub ((h.bddRV t).smul ρ)

/-- Woodford (2003), eq. (2.18), p. 496: the innovation `ε_{t+1}` is known at `t + 1`. -/
theorem innov_meas (h : MeasAR1Innov S ρ s u ε) (t : ℕ) :
    StronglyMeasurable[S.𝓕 (t + 1)] (ε (t + 1)) := by
  rw [h.innov_eq t]
  exact (h.1 (t + 1)).sub (((h.1 t).mono (S.𝓕.mono (Nat.le_succ t))).const_smul ρ)

/-- Woodford (2003), eq. (2.18), p. 496: `E_t u_{t+j} = ρʲ u_t` almost surely. -/
theorem E_u (h : MeasAR1Innov S ρ s u ε) (t j : ℕ) :
    S.E t (u (t + j)) =ᵐ[S.μ] ρ ^ j • u t :=
  S.ar1_E h.2.2.1 h.1 h.2.1 h.2.2.2.1 t j

end MeasAR1Innov

/-- Woodford (2003), p. 509 (tool): on a probability space two constants that agree almost
surely are equal. -/
theorem const_eq_of_ae {c d : ℝ} (h : (fun _ : Ω => c) =ᵐ[S.μ] fun _ => d) : c = d := by
  obtain ⟨ω, hω⟩ := h.exists
  exact hω

/-- Woodford (2003), p. 509 (tool): if `W` is known at `t + k` and the bounded `e` has
`E_{t+k} e = 0`, then `E_t (W e) = 0` almost surely (pull-out, then iterated expectations). -/
theorem E_known_mul_zero {t k : ℕ} {W e : Ω → ℝ} (hWm : StronglyMeasurable[S.𝓕 (t + k)] W)
    (hWB : S.BddRV W) (heB : S.BddRV e) (he0 : S.E (t + k) e =ᵐ[S.μ] 0) :
    S.E t (W * e) =ᵐ[S.μ] 0 := by
  obtain ⟨-, C, hC⟩ := hWB
  have hz : W * S.E (t + k) e =ᵐ[S.μ] 0 := by
    filter_upwards [he0] with ω h
    rw [Pi.mul_apply, h, Pi.zero_apply, mul_zero]
  filter_upwards [(S.E_tower (Nat.le_add_right t k) (W * e)).symm,
    S.E_congr (S.E_pullOut hWm hC heB.integrable) t, S.E_congr hz t] with ω h1 h2 h3
  rw [h1, h2, h3, S.E_zero]

/-- Woodford (2003), pp. 509, 512 (the conditional covariance of two AR(1) disturbances): if the
innovations have constant conditional covariance `E_t(εᵘ_{t+1} εʳ_{t+1}) = c`, then the
`k`-step forecast errors satisfy
`E_t[(u_{t+k} − ρ_uᵏ u_t)(r_{t+k} − ρ_rᵏ r_t)] = c ∑_{j<k} (ρ_u ρ_r)ʲ` almost surely. -/
theorem E_cross_dev {ρu ρr su sr c : ℝ} {u εu r εr : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρu su u εu) (hr : MeasAR1Innov S ρr sr r εr)
    (hc : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => c) (t k : ℕ) :
    S.E t ((u (t + k) - ρu ^ k • u t) * (r (t + k) - ρr ^ k • r t)) =ᵐ[S.μ]
      fun _ => c * ∑ j ∈ Finset.range k, (ρu * ρr) ^ j := by
  induction k with
  | zero =>
    have h0 : (u (t + 0) - ρu ^ 0 • u t) * (r (t + 0) - ρr ^ 0 • r t) = 0 := by
      funext ω
      simp
    rw [h0, S.E_zero]
    exact Eventually.of_forall fun ω => by simp
  | succ k ih =>
    set U := u (t + k) - ρu ^ k • u t with hU
    set R := r (t + k) - ρr ^ k • r t with hR
    set eu := εu (t + k + 1) with heu
    set er := εr (t + k + 1) with her
    have hUB : S.BddRV U := (hu.bddRV _).sub ((hu.bddRV t).smul _)
    have hRB : S.BddRV R := (hr.bddRV _).sub ((hr.bddRV t).smul _)
    have hUm : StronglyMeasurable[S.𝓕 (t + k)] U :=
      (hu.1 (t + k)).sub (((hu.1 t).mono (S.𝓕.mono (Nat.le_add_right t k))).const_smul _)
    have hRm : StronglyMeasurable[S.𝓕 (t + k)] R :=
      (hr.1 (t + k)).sub (((hr.1 t).mono (S.𝓕.mono (Nat.le_add_right t k))).const_smul _)
    have heuB : S.BddRV eu := hu.innov_bddRV (t + k)
    have herB : S.BddRV er := hr.innov_bddRV (t + k)
    have hsplit : (u (t + (k + 1)) - ρu ^ (k + 1) • u t) * (r (t + (k + 1)) - ρr ^ (k + 1) • r t)
        = (ρu * ρr) • (U * R) + ρu • (U * er) + ρr • (R * eu) + eu * er := by
      have e1 : u (t + (k + 1)) = ρu • u (t + k) + εu (t + k + 1) := hu.2.2.1 (t + k)
      have e2 : r (t + (k + 1)) = ρr • r (t + k) + εr (t + k + 1) := hr.2.2.1 (t + k)
      rw [e1, e2]
      funext ω
      simp only [hU, hR, heu, her, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply,
        smul_eq_mul]
      ring
    have hc1 : S.E t (U * er) =ᵐ[S.μ] 0 :=
      E_known_mul_zero S hUm hUB herB (hr.2.2.2.1 (t + k))
    have hc2 : S.E t (R * eu) =ᵐ[S.μ] 0 :=
      E_known_mul_zero S hRm hRB heuB (hu.2.2.2.1 (t + k))
    have hee : S.E t (eu * er) =ᵐ[S.μ] fun _ => c := by
      filter_upwards [(S.E_tower (Nat.le_add_right t k) (eu * er)).symm,
        S.E_congr (hc (t + k)) t] with ω h1 h2
      rw [h1, h2, S.E_const]
    have I1 : Integrable ((ρu * ρr) • (U * R)) S.μ := (hUB.mul hRB).integrable.smul _
    have I2 : Integrable (ρu • (U * er)) S.μ := (hUB.mul herB).integrable.smul _
    have I3 : Integrable (ρr • (R * eu)) S.μ := (hRB.mul heuB).integrable.smul _
    have I4 : Integrable (eu * er) S.μ := (heuB.mul herB).integrable
    have hs : ∑ j ∈ Finset.range (k + 1), (ρu * ρr) ^ j =
        (ρu * ρr) * ∑ j ∈ Finset.range k, (ρu * ρr) ^ j + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsplit]
    filter_upwards [S.E_add ((I1.add I2).add I3) I4 t, S.E_add (I1.add I2) I3 t,
      S.E_add I1 I2 t, S.E_smul (ρu * ρr) (U * R) t, S.E_smul ρu (U * er) t,
      S.E_smul ρr (R * eu) t, ih, hc1, hc2, hee] with ω h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.add_apply, h4, h5, h6]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h7, h8, h9, h10, hs]
    simp only [Pi.zero_apply]
    ring

/-! ### Conditional variances of the plans (2.19) and (3.6) -/

/-- Woodford (2003), p. 509 and p. 512: for a plan (3.6) `y_t = ȳ + f u_t + g r_t` with AR(1)
disturbances whose innovations have conditional covariance `c`, the conditional variance at `t` of
`y_{t+k}` is `f² s_u ∑_{j<k} ρ_u^{2j} + 2 f g c ∑_{j<k} (ρ_u ρ_r)ʲ + g² s_r ∑_{j<k} ρ_r^{2j}`
almost surely (Mathlib's `Var[· ; μ | 𝓕 t]`). -/
theorem condVar_plan2 {ρu ρr su sr c : ℝ} {u εu r εr : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρu su u εu) (hr : MeasAR1Innov S ρr sr r εr)
    (hc : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => c) (ybar f g : ℝ) (t k : ℕ) :
    Var[plan2 ybar f g u r (t + k); S.μ | S.𝓕 t] =ᵐ[S.μ] fun _ =>
      f ^ 2 * (su * ∑ j ∈ Finset.range k, (ρu * ρu) ^ j) +
        2 * f * g * (c * ∑ j ∈ Finset.range k, (ρu * ρr) ^ j) +
        g ^ 2 * (sr * ∑ j ∈ Finset.range k, (ρr * ρr) ^ j) := by
  set U := u (t + k) - ρu ^ k • u t with hU
  set R := r (t + k) - ρr ^ k • r t with hR
  have hUB : S.BddRV U := (hu.bddRV _).sub ((hu.bddRV t).smul _)
  have hRB : S.BddRV R := (hr.bddRV _).sub ((hr.bddRV t).smul _)
  have Iu := (hu.bddRV (t + k)).integrable
  have Ir := (hr.bddRV (t + k)).integrable
  have hp : plan2 ybar f g u r (t + k) = (fun _ => ybar) + f • u (t + k) + g • r (t + k) := rfl
  have hdev : plan2 ybar f g u r (t + k) - S.E t (plan2 ybar f g u r (t + k)) =ᵐ[S.μ]
      f • U + g • R := by
    rw [hp]
    filter_upwards [S.E_add ((integrable_const ybar).add (Iu.smul f)) (Ir.smul g) t,
      S.E_add (integrable_const ybar) (Iu.smul f) t, S.E_smul f (u (t + k)) t,
      S.E_smul g (r (t + k)) t, hu.E_u t k, hr.E_u t k] with ω h1 h2 h3 h4 h5 h6
    rw [Pi.sub_apply, h1]
    simp only [Pi.add_apply]
    rw [h2]
    simp only [Pi.add_apply]
    rw [h3, h4]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h5, h6, S.E_const]
    simp only [hU, hR, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hsq : (plan2 ybar f g u r (t + k) - S.E t (plan2 ybar f g u r (t + k))) ^ 2 =ᵐ[S.μ]
      f ^ 2 • (U * U) + (2 * f * g) • (U * R) + g ^ 2 • (R * R) := by
    filter_upwards [hdev] with ω h
    rw [Pi.pow_apply, h]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have J1 : Integrable (f ^ 2 • (U * U)) S.μ := (hUB.mul hUB).integrable.smul _
  have J2 : Integrable ((2 * f * g) • (U * R)) S.μ := (hUB.mul hRB).integrable.smul _
  have J3 : Integrable (g ^ 2 • (R * R)) S.μ := (hRB.mul hRB).integrable.smul _
  change S.E t ((plan2 ybar f g u r (t + k) - S.E t (plan2 ybar f g u r (t + k))) ^ 2) =ᵐ[S.μ] _
  filter_upwards [S.E_congr hsq t, S.E_add (J1.add J2) J3 t, S.E_add J1 J2 t,
    S.E_smul (f ^ 2) (U * U) t, S.E_smul (2 * f * g) (U * R) t, S.E_smul (g ^ 2) (R * R) t,
    E_cross_dev S hu hu hu.2.2.2.2 t k, E_cross_dev S hu hr hc t k,
    E_cross_dev S hr hr hr.2.2.2.2 t k] with ω h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [h1, h2, Pi.add_apply, h3, Pi.add_apply, h4, h5, h6]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h7, h8, h9]

omit mΩ in
/-- Woodford (2003), eq. (2.19), p. 497: the plan (2.19) is the plan (3.6) with `g = 0`. -/
theorem plan1_eq_plan2 (ybar f : ℝ) (u : ℕ → Ω → ℝ) : plan1 ybar f u = plan2 ybar f 0 u u := by
  funext t ω
  simp [plan1, plan2_apply]

/-- Woodford (2003), p. 511: for a plan (2.19) `y_t = ȳ + f u_t`, the conditional variance at
`t` of `y_{t+k}` is `f² s ∑_{j<k} ρ^{2j}` almost surely. -/
theorem condVar_plan1 {ρ s : ℝ} {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (ybar f : ℝ)
    (t k : ℕ) :
    Var[plan1 ybar f u (t + k); S.μ | S.𝓕 t] =ᵐ[S.μ] fun _ =>
      f ^ 2 * (s * ∑ j ∈ Finset.range k, (ρ * ρ) ^ j) := by
  rw [plan1_eq_plan2]
  filter_upwards [condVar_plan2 S hu hu hu.2.2.2.2 ybar f 0 t k] with ω h
  rw [h]
  ring

/-! ### The stabilization loss (3.4), (3.7), (3.8) -/

/-- Woodford (2003), p. 509 (definition of `L^stab` for the loss (1.2)), with genuine conditional
variances: `∑_k βᵏ [var_{t₀}(π_{t₀+k}) + λ var_{t₀}(x_{t₀+k})]` in state `ω` at date `t₀`. -/
noncomputable def mLstab12 (β lam : ℝ) (t₀ : ℕ) (π x : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' k, β ^ k * (Var[π (t₀ + k); S.μ | S.𝓕 t₀] ω + lam * Var[x (t₀ + k); S.μ | S.𝓕 t₀] ω)

/-- Woodford (2003), p. 512 (definition of `L^stab` for the loss (2.24)), with genuine conditional
variances: `∑_k βᵏ [var_{t₀}(π) + λₓ var_{t₀}(x) + λᵢ var_{t₀}(i)]` in state `ω` at date `t₀`. -/
noncomputable def mLstab (β lx li : ℝ) (t₀ : ℕ) (π x i : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' k, β ^ k * (Var[π (t₀ + k); S.μ | S.𝓕 t₀] ω + lx * Var[x (t₀ + k); S.μ | S.𝓕 t₀] ω +
    li * Var[i (t₀ + k); S.μ | S.𝓕 t₀] ω)

/-- Woodford (2003), p. 511 (tool): `|ρ| < 1` gives `0 ≤ ρ² < 1`. -/
theorem sq_lt_one_of_abs {ρ : ℝ} (hρ : |ρ| < 1) : 0 ≤ ρ ^ 2 ∧ ρ ^ 2 < 1 :=
  ⟨sq_nonneg ρ, sq_abs ρ ▸ (pow_lt_one₀ (abs_nonneg ρ) hρ two_ne_zero)⟩

/-- **Equation (3.4)** (Woodford (2003), p. 511), with genuine conditional variances: for a plan
(2.19) and an AR(1) disturbance with innovation variance `s` (`|ρ| < 1`), almost surely the
stabilization loss is the genuine discounted sum
`β/(1 − β) · (1 − ρ²)/(1 − βρ²) · (f_π² + λ f_x²) σ_u²`, `σ_u² = s/(1 − ρ²)`. -/
theorem lstab12_hasSum {β lam ρ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (πbar xbar fπ fx : ℝ) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => β ^ k * (Var[plan1 πbar fπ u (t₀ + k); S.μ | S.𝓕 t₀] ω +
      lam * Var[plan1 xbar fx u (t₀ + k); S.μ | S.𝓕 t₀] ω))
      (β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
        uncondVar ρ s) := by
  obtain ⟨hq0, hq1⟩ := sq_lt_one_of_abs hρ
  have hG := (Noninertial.hasSum_disc_geomSum hβ0 hβ1 hq0 hq1).mul_left
    (s * (fπ ^ 2 + lam * fx ^ 2))
  filter_upwards [ae_all_iff.2 fun k => condVar_plan1 S hu πbar fπ t₀ k,
    ae_all_iff.2 fun k => condVar_plan1 S hu xbar fx t₀ k] with ω h1 h2
  convert hG using 1
  · funext k
    rw [h1 k, h2 k]
    simp only [← pow_two]
    ring
  · unfold uncondVar
    have : 1 - ρ ^ 2 ≠ 0 := by linarith
    have : 1 - β ≠ 0 := by linarith
    have : 1 - β * ρ ^ 2 ≠ 0 := by nlinarith
    field_simp

/-- Woodford (2003), eq. (3.4), p. 511: almost surely `L^stab` of a plan (2.19) equals
`β/(1 − β) · (1 − ρ²)/(1 − βρ²) · (f_π² + λ f_x²) σ_u²`. -/
theorem lstab12_eq {β lam ρ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (πbar xbar fπ fx : ℝ) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, mLstab12 S β lam t₀ (plan1 πbar fπ u) (plan1 xbar fx u) ω =
      β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
        uncondVar ρ s := by
  filter_upwards [lstab12_hasSum S hβ0 hβ1 hρ hu πbar xbar fπ fx t₀ (lam := lam)] with ω h
  exact h.tsum_eq

/-- **Equations (3.7)–(3.8)** (Woodford (2003), p. 513), with genuine conditional variances: for a
plan (3.6) and AR(1) disturbances with uncorrelated innovations (`E_t(εᵘ_{t+1} εʳ_{t+1}) = 0`)
of variances `s_u`, `s_r`, almost surely `L^stab = L^{stab,r} + L^{stab,u}` with
`L^{stab,j} = β/(1 − β) · (1 − ρ_j²)/(1 − βρ_j²) · (π_j² + λₓ x_j² + λᵢ i_j²) σ_j²`. -/
theorem lstab_hasSum {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρu : |ρu| < 1)
    (hρr : |ρr| < 1) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => β ^ k *
      (Var[plan2 πbar fπ gπ u r (t₀ + k); S.μ | S.𝓕 t₀] ω +
      lx * Var[plan2 xbar fx gx u r (t₀ + k); S.μ | S.𝓕 t₀] ω +
      li * Var[plan2 ibar fi gi u r (t₀ + k); S.μ | S.𝓕 t₀] ω))
      (β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su) := by
  obtain ⟨hu0, hu1⟩ := sq_lt_one_of_abs hρu
  obtain ⟨hr0, hr1⟩ := sq_lt_one_of_abs hρr
  have hGu := (Noninertial.hasSum_disc_geomSum hβ0 hβ1 hu0 hu1).mul_left
    (su * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2))
  have hGr := (Noninertial.hasSum_disc_geomSum hβ0 hβ1 hr0 hr1).mul_left
    (sr * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2))
  filter_upwards [ae_all_iff.2 fun k => condVar_plan2 S hu hr hind πbar fπ gπ t₀ k,
    ae_all_iff.2 fun k => condVar_plan2 S hu hr hind xbar fx gx t₀ k,
    ae_all_iff.2 fun k => condVar_plan2 S hu hr hind ibar fi gi t₀ k] with ω h1 h2 h3
  convert hGr.add hGu using 1
  · funext k
    rw [h1 k, h2 k, h3 k]
    simp only [← pow_two]
    ring
  · unfold uncondVar
    have : 1 - ρu ^ 2 ≠ 0 := by linarith
    have : 1 - ρr ^ 2 ≠ 0 := by linarith
    have : 1 - β ≠ 0 := by linarith
    have : 1 - β * ρu ^ 2 ≠ 0 := by nlinarith
    have : 1 - β * ρr ^ 2 ≠ 0 := by nlinarith
    field_simp

/-- Woodford (2003), eqs. (3.7)–(3.8), p. 513: almost surely `L^stab` of a plan (3.6) equals
`L^{stab,r} + L^{stab,u}`. -/
theorem lstab_eq {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρu : |ρu| < 1)
    (hρr : |ρr| < 1) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
      (plan2 ibar fi gi u r) ω =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su := by
  filter_upwards [lstab_hasSum S hβ0 hβ1 hρu hρr hu hr hind πbar xbar ibar fπ fx fi gπ gx gi t₀
    (lx := lx) (li := li)] with ω h
  exact h.tsum_eq


/-! ### The model equations and purely forward-looking plans -/

/-- Woodford (2003), eq. (2.1), p. 486, with genuine conditional expectations: the
aggregate-supply relation `π_t = κ x_t + β E_t π_{t+1} + u_t`, almost surely at every date. -/
def MAS (β κ : ℝ) (π x u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t =ᵐ[S.μ] κ • x t + β • S.E t (π (t + 1)) + u t

/-- Woodford (2003), eq. (2.23), p. 502, with genuine conditional expectations: the IS relation
`x_t = E_t x_{t+1} − σ (i_t − E_t π_{t+1} − r^n_t)`, almost surely at every date. -/
def MIS (σ : ℝ) (π x i rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - σ • (i t - S.E t (π (t + 1)) - rn t)

/-- Woodford (2003), eqs. (2.18) and (2.27), pp. 496 and 504: under AR(1) disturbances,
`E_t (ȳ + f u_{t+1} + g r_{t+1}) = ȳ + f ρ_u u_t + g ρ_r r_t` almost surely. -/
theorem E_plan2 {ρu ρr su sr : ℝ} {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr) (ybar f g : ℝ) (t : ℕ) :
    S.E t (plan2 ybar f g u r (t + 1)) =ᵐ[S.μ] plan2 ybar (f * ρu) (g * ρr) u r t := by
  have Iu := (hu.bddRV (t + 1)).integrable
  have Ir := (hr.bddRV (t + 1)).integrable
  have hp : plan2 ybar f g u r (t + 1) = (fun _ => ybar) + f • u (t + 1) + g • r (t + 1) := rfl
  rw [hp]
  filter_upwards [S.E_add ((integrable_const ybar).add (Iu.smul f)) (Ir.smul g) t,
    S.E_add (integrable_const ybar) (Iu.smul f) t, S.E_smul f (u (t + 1)) t,
    S.E_smul g (r (t + 1)) t, hu.E_u t 1, hr.E_u t 1] with ω h1 h2 h3 h4 h5 h6
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2]
  simp only [Pi.add_apply]
  rw [h3, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h5, h6, S.E_const]
  simp only [plan2_apply, Pi.smul_apply, smul_eq_mul, pow_one]
  ring

/-- Woodford (2003), eq. (2.18), p. 496: under an AR(1) disturbance,
`E_t (ȳ + f u_{t+1}) = ȳ + f ρ u_t` almost surely. -/
theorem E_plan1 {ρ s : ℝ} {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (ybar f : ℝ)
    (t : ℕ) : S.E t (plan1 ybar f u (t + 1)) =ᵐ[S.μ] plan1 ybar (f * ρ) u t := by
  have h := E_plan2 S hu hu ybar f 0 t
  rw [zero_mul, ← plan1_eq_plan2, ← plan1_eq_plan2] at h
  exact h

/-- Woodford (2003), p. 511 (non-degeneracy from a positive innovation variance): if
`a + b u_t = 0` almost surely at every date, and the innovation variance is `s ≠ 0`, then
`a = b = 0`. (The core statement needs the separate hypothesis `Noninertial.Nondeg1`.) -/
theorem affine_zero1 {ρ s : ℝ} {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (hs : s ≠ 0)
    {a b : ℝ} (h : ∀ t, (fun ω => a + b * u t ω) =ᵐ[S.μ] 0) : a = 0 ∧ b = 0 := by
  set K : Ω → ℝ := (fun _ => a) + (b * ρ) • u 0 with hK
  set D : Ω → ℝ := b • ε (0 + 1) with hD
  have hWKD : (fun ω => a + b * u (0 + 1) ω) = K + D := by
    funext ω
    rw [hu.2.2.1 0]
    simp only [hK, hD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hKB : S.BddRV K := (MeasExpectationSystem.BddRV.const a).add ((hu.bddRV 0).smul _)
  have hKm : StronglyMeasurable[S.𝓕 0] K :=
    stronglyMeasurable_const.add ((hu.1 0).const_smul _)
  have hDB : S.BddRV D := (hu.innov_bddRV 0).smul b
  have hEK : S.E 0 K = K := S.E_of_stronglyMeasurable hKm hKB.integrable
  have hED : S.E 0 D =ᵐ[S.μ] 0 := by
    filter_upwards [S.E_smul b (ε (0 + 1)) 0, hu.2.2.2.1 0] with ω h1 h2
    rw [h1, Pi.smul_apply, h2]
    simp
  have hW := h (0 + 1)
  rw [hWKD] at hW
  have hEW : S.E 0 (K + D) =ᵐ[S.μ] 0 := by
    have := S.E_congr hW 0
    rwa [S.E_zero] at this
  have hK0 : K =ᵐ[S.μ] 0 := by
    filter_upwards [hEW, S.E_add hKB.integrable hDB.integrable 0, hED] with ω h1 h2 h3
    rw [h2, Pi.add_apply, hEK, h3] at h1
    simpa using h1
  have hD0 : D =ᵐ[S.μ] 0 := by
    filter_upwards [hW, hK0] with ω h1 h2
    rw [Pi.add_apply, h2] at h1
    simpa using h1
  have hz : S.E 0 (ε (0 + 1) * D) =ᵐ[S.μ] 0 := by
    have hz : ε (0 + 1) * D =ᵐ[S.μ] 0 := by
      filter_upwards [hD0] with ω h
      simp [h]
    have := S.E_congr hz 0
    rwa [S.E_zero] at this
  have hεD : ε (0 + 1) * D = b • (ε (0 + 1) * ε (0 + 1)) := by
    funext ω
    simp only [hD, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb : b * s = 0 := by
    apply const_eq_of_ae S
    filter_upwards [hz, S.E_smul b (ε (0 + 1) * ε (0 + 1)) 0, hu.2.2.2.2 0] with ω h1 h2 h3
    rw [hεD, h2, Pi.smul_apply, h3] at h1
    simpa using h1
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right hs
  refine ⟨?_, hb0⟩
  apply const_eq_of_ae S
  filter_upwards [h 0] with ω h1
  rw [hb0] at h1
  simpa using h1

/-- Woodford (2003), p. 512 (non-degeneracy from positive, uncorrelated innovations): if
`a + b u_t + c r_t = 0` almost surely at every date, the innovation variances are nonzero and the
innovations are uncorrelated, then `a = b = c = 0`. (The core statement needs the separate
hypothesis `Noninertial.Nondeg2`.) -/
theorem affine_zero2 {ρu ρr su sr : ℝ} {u εu r εr : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρu su u εu) (hr : MeasAR1Innov S ρr sr r εr) (hsu : su ≠ 0)
    (hsr : sr ≠ 0) (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) {a b c : ℝ}
    (h : ∀ t, (fun ω => a + b * u t ω + c * r t ω) =ᵐ[S.μ] 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  set K : Ω → ℝ := (fun _ => a) + (b * ρu) • u 0 + (c * ρr) • r 0 with hK
  set D : Ω → ℝ := b • εu (0 + 1) + c • εr (0 + 1) with hD
  have hWKD : (fun ω => a + b * u (0 + 1) ω + c * r (0 + 1) ω) = K + D := by
    funext ω
    rw [hu.2.2.1 0, hr.2.2.1 0]
    simp only [hK, hD, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hKB : S.BddRV K :=
    ((MeasExpectationSystem.BddRV.const a).add ((hu.bddRV 0).smul _)).add ((hr.bddRV 0).smul _)
  have hKm : StronglyMeasurable[S.𝓕 0] K :=
    (stronglyMeasurable_const.add ((hu.1 0).const_smul _)).add ((hr.1 0).const_smul _)
  have Iu := (hu.innov_bddRV 0).integrable
  have Ir := (hr.innov_bddRV 0).integrable
  have hDB : S.BddRV D := ((hu.innov_bddRV 0).smul b).add ((hr.innov_bddRV 0).smul c)
  have hEK : S.E 0 K = K := S.E_of_stronglyMeasurable hKm hKB.integrable
  have hED : S.E 0 D =ᵐ[S.μ] 0 := by
    filter_upwards [S.E_add (Iu.smul b) (Ir.smul c) 0, S.E_smul b (εu (0 + 1)) 0,
      S.E_smul c (εr (0 + 1)) 0, hu.2.2.2.1 0, hr.2.2.2.1 0] with ω h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3]
    simp only [Pi.smul_apply]
    rw [h4, h5]
    simp
  have hW := h (0 + 1)
  rw [hWKD] at hW
  have hEW : S.E 0 (K + D) =ᵐ[S.μ] 0 := by
    have := S.E_congr hW 0
    rwa [S.E_zero] at this
  have hK0 : K =ᵐ[S.μ] 0 := by
    filter_upwards [hEW, S.E_add hKB.integrable hDB.integrable 0, hED] with ω h1 h2 h3
    rw [h2, Pi.add_apply, hEK, h3] at h1
    simpa using h1
  have hD0 : D =ᵐ[S.μ] 0 := by
    filter_upwards [hW, hK0] with ω h1 h2
    rw [Pi.add_apply, h2] at h1
    simpa using h1
  have hzero : ∀ e : Ω → ℝ, S.E 0 (e * D) =ᵐ[S.μ] 0 := by
    intro e
    have hz : e * D =ᵐ[S.μ] 0 := by
      filter_upwards [hD0] with ω h
      simp [h]
    have := S.E_congr hz 0
    rwa [S.E_zero] at this
  have Iuu := ((hu.innov_bddRV 0).mul (hu.innov_bddRV 0)).integrable
  have Iur := ((hu.innov_bddRV 0).mul (hr.innov_bddRV 0)).integrable
  have Irr := ((hr.innov_bddRV 0).mul (hr.innov_bddRV 0)).integrable
  have hb : b * su = 0 := by
    have hsplit : εu (0 + 1) * D =
        b • (εu (0 + 1) * εu (0 + 1)) + c • (εu (0 + 1) * εr (0 + 1)) := by
      funext ω
      simp only [hD, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    apply const_eq_of_ae S
    filter_upwards [hzero (εu (0 + 1)), S.E_add (Iuu.smul b) (Iur.smul c) 0,
      S.E_smul b (εu (0 + 1) * εu (0 + 1)) 0, S.E_smul c (εu (0 + 1) * εr (0 + 1)) 0,
      hu.2.2.2.2 0, hind 0] with ω h1 h2 h3 h4 h5 h6
    rw [hsplit, h2, Pi.add_apply, h3, h4] at h1
    simp only [Pi.smul_apply] at h1
    rw [h5, h6] at h1
    simpa using h1
  have hc : c * sr = 0 := by
    have hsplit : εr (0 + 1) * D =
        b • (εu (0 + 1) * εr (0 + 1)) + c • (εr (0 + 1) * εr (0 + 1)) := by
      funext ω
      simp only [hD, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    apply const_eq_of_ae S
    filter_upwards [hzero (εr (0 + 1)), S.E_add (Iur.smul b) (Irr.smul c) 0,
      S.E_smul b (εu (0 + 1) * εr (0 + 1)) 0, S.E_smul c (εr (0 + 1) * εr (0 + 1)) 0,
      hind 0, hr.2.2.2.2 0] with ω h1 h2 h3 h4 h5 h6
    rw [hsplit, h2, Pi.add_apply, h3, h4] at h1
    simp only [Pi.smul_apply] at h1
    rw [h5, h6] at h1
    simpa using h1
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right hsu
  have hc0 : c = 0 := (mul_eq_zero.mp hc).resolve_right hsr
  refine ⟨?_, hb0, hc0⟩
  apply const_eq_of_ae S
  filter_upwards [h 0] with ω h1
  rw [hb0, hc0] at h1
  simpa using h1

/-- Woodford (2003), eqs. (3.2)–(3.3), p. 511, with genuine conditional expectations: with an
AR(1) cost-push disturbance of innovation variance `s ≠ 0`, a plan `π = π̄ + f_π u`,
`x = x̄ + f_x u` satisfies (2.1) almost surely at every date iff `(1 − β) π̄ = κ x̄` and
`(1 − βρ) f_π = κ f_x + 1`. -/
theorem plan_AS_iff {β κ ρ s : ℝ} {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (hs : s ≠ 0)
    (πbar xbar fπ fx : ℝ) :
    MAS S β κ (plan1 πbar fπ u) (plan1 xbar fx u) u ↔
      (1 - β) * πbar = κ * xbar ∧ (1 - β * ρ) * fπ = κ * fx + 1 := by
  constructor
  · intro h
    have key : ∀ t, (fun ω => ((1 - β) * πbar - κ * xbar) +
        ((1 - β * ρ) * fπ - κ * fx - 1) * u t ω) =ᵐ[S.μ] 0 := by
      intro t
      filter_upwards [h t, E_plan1 S hu πbar fπ t] with ω h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [h2] at h1
      simp only [plan1, Pi.zero_apply] at h1 ⊢
      linear_combination h1
    obtain ⟨a1, a2⟩ := affine_zero1 S hu hs key
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ t
    filter_upwards [E_plan1 S hu πbar fπ t] with ω h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h]
    simp only [plan1]
    linear_combination h1 + u t ω * h2

/-- Woodford (2003), eq. (3.6), p. 512 and App. F.4, with genuine conditional expectations: with
AR(1) disturbances `u`, `r̂ⁿ` of nonzero innovation variances and uncorrelated innovations,
`r^n_t = r̄ + r̂ⁿ_t`, a plan (3.6) for `(π, x, i)` satisfies (2.1) and (2.23) almost surely at
every date iff `(1 − β) π̄ = κ x̄`, `ī = r̄ + π̄`, `(1 − β ρ_u) f_π = κ f_x + 1`,
`(1 − ρ_u) f_x = −σ (f_i − ρ_u f_π)`, `(1 − β ρ_r) g_π = κ g_x` and
`(1 − ρ_r) g_x = −σ (g_i − ρ_r g_π − 1)`. -/
theorem plan2_iff {β κ σ ρu ρr su sr rbar : ℝ} (hσ : σ ≠ 0) {u εu r εr : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρu su u εu) (hr : MeasAR1Innov S ρr sr r εr) (hsu : su ≠ 0)
    (hsr : sr ≠ 0) (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) :
    (MAS S β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u ∧
      MIS S σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
        (fun t ω => rbar + r t ω)) ↔
      ((1 - β) * πbar = κ * xbar ∧ ibar = rbar + πbar) ∧
      ((1 - β * ρu) * fπ = κ * fx + 1 ∧ (1 - ρu) * fx = -σ * (fi - ρu * fπ)) ∧
      ((1 - β * ρr) * gπ = κ * gx ∧ (1 - ρr) * gx = -σ * (gi - ρr * gπ - 1)) := by
  constructor
  · rintro ⟨hA, hI⟩
    have kAS : ∀ t, (fun ω => ((1 - β) * πbar - κ * xbar) +
        ((1 - β * ρu) * fπ - κ * fx - 1) * u t ω + ((1 - β * ρr) * gπ - κ * gx) * r t ω)
        =ᵐ[S.μ] 0 := by
      intro t
      filter_upwards [hA t, E_plan2 S hu hr πbar fπ gπ t] with ω h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [h2] at h1
      simp only [plan2_apply, Pi.zero_apply] at h1 ⊢
      linear_combination h1
    have kIS : ∀ t, (fun ω => σ * (ibar - πbar - rbar) +
        ((1 - ρu) * fx + σ * (fi - ρu * fπ)) * u t ω +
        ((1 - ρr) * gx + σ * (gi - ρr * gπ - 1)) * r t ω) =ᵐ[S.μ] 0 := by
      intro t
      filter_upwards [hI t, E_plan2 S hu hr xbar fx gx t, E_plan2 S hu hr πbar fπ gπ t]
        with ω h1 h2 h3
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
      rw [h2, h3] at h1
      simp only [plan2_apply, Pi.zero_apply] at h1 ⊢
      linear_combination h1
    obtain ⟨a1, a2, a3⟩ := affine_zero2 S hu hr hsu hsr hind kAS
    obtain ⟨i1, i2, i3⟩ := affine_zero2 S hu hr hsu hsr hind kIS
    have hi : ibar - πbar - rbar = 0 := (mul_eq_zero.mp i1).resolve_left hσ
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · filter_upwards [E_plan2 S hu hr πbar fπ gπ t] with ω h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h]
      simp only [plan2_apply]
      linear_combination h1 + u t ω * h3 + r t ω * h5
    · filter_upwards [E_plan2 S hu hr xbar fx gx t, E_plan2 S hu hr πbar fπ gπ t] with ω h h'
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [h, h']
      simp only [plan2_apply]
      linear_combination σ * h2 + u t ω * h4 + r t ω * h6

/-! ### Proposition 7.11 and Appendix F.4: stabilization optimality -/

/-- **Proposition 7.11, stabilization form** (Woodford (2003), pp. 509–511), with genuine
conditional expectations: let the cost-push disturbance be AR(1) with innovations of conditional
variance `s > 0` (`|ρ| < 1`). The plan `π = f_π^oni u`, `x = f_x^oni u` satisfies (2.1), and for
every plan (2.19) that satisfies (2.1), almost surely its stabilization loss `L^stab` (a genuine
discounted sum of conditional variances) is at least that of the optimal noninertial plan; the
two losses agree almost surely iff the plan has the responses (3.5). No pull-out or
non-degeneracy hypothesis is needed. -/
theorem prop_7_11_lstab {β κ lam ρ s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| < 1) (hs : 0 < s) {u ε : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρ s u ε) (t₀ : ℕ) :
    MAS S β κ (plan1 0 (fpiOni β κ lam ρ) u) (plan1 0 (fxOni β κ lam ρ) u) u ∧
    ∀ πbar xbar gπ gx, MAS S β κ (plan1 πbar gπ u) (plan1 xbar gx u) u →
      (∀ᵐ ω ∂S.μ,
        mLstab12 S β lam t₀ (plan1 0 (fpiOni β κ lam ρ) u) (plan1 0 (fxOni β κ lam ρ) u) ω ≤
          mLstab12 S β lam t₀ (plan1 πbar gπ u) (plan1 xbar gx u) ω) ∧
      (mLstab12 S β lam t₀ (plan1 πbar gπ u) (plan1 xbar gx u) =ᵐ[S.μ]
          mLstab12 S β lam t₀ (plan1 0 (fpiOni β κ lam ρ) u) (plan1 0 (fxOni β κ lam ρ) u) ↔
        gπ = fpiOni β κ lam ρ ∧ gx = fxOni β κ lam ρ) := by
  have hq1 : ρ ^ 2 < 1 := (sq_lt_one_of_abs hρ).2
  have hK : 0 < β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s := by
    have : 0 < 1 - β := by linarith
    have : 0 < 1 - ρ ^ 2 := by linarith
    have : 0 < 1 - β * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
    unfold uncondVar
    positivity
  set K := β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s
  have hL : ∀ πbar xbar fπ fx, ∀ᵐ ω ∂S.μ,
      mLstab12 S β lam t₀ (plan1 πbar fπ u) (plan1 xbar fx u) ω = K * (fπ ^ 2 + lam * fx ^ 2) := by
    intro πbar xbar fπ fx
    filter_upwards [lstab12_eq S hβ0.le hβ1 hρ hu πbar xbar fπ fx t₀ (lam := lam)] with ω h
    rw [h]
    ring
  refine ⟨(plan_AS_iff S hu hs.ne' 0 0 _ _).mpr ⟨by ring, Noninertial.oni_constraint hκ hlam⟩, ?_⟩
  intro πbar xbar gπ gx hAS
  have hg := ((plan_AS_iff S hu hs.ne' πbar xbar gπ gx).mp hAS).2
  have e := Noninertial.oni_objective_eq hκ hlam hg
  have hd : 0 ≤ (gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2 := by positivity
  refine ⟨?_, ⟨fun heq => ?_, fun ⟨h1, h2⟩ => ?_⟩⟩
  · filter_upwards [hL 0 0 (fpiOni β κ lam ρ) (fxOni β κ lam ρ), hL πbar xbar gπ gx]
      with ω h1 h2
    rw [h1, h2, e]
    nlinarith
  · obtain ⟨ω, h1, h2, h3⟩ :=
      ((hL πbar xbar gπ gx).and ((hL 0 0 (fpiOni β κ lam ρ) (fxOni β κ lam ρ)).and heq)).exists
    rw [h1, h2, e] at h3
    have hz : (gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2 = 0 := by
      have : K * ((gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2) = 0 := by
        linarith
      exact (mul_eq_zero.mp this).resolve_left hK.ne'
    have a2 : 0 ≤ lam * (gx - fxOni β κ lam ρ) ^ 2 := by positivity
    have e1 : (gπ - fpiOni β κ lam ρ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (gπ - fpiOni β κ lam ρ)]
    have e2 : (gx - fxOni β κ lam ρ) ^ 2 = 0 := by
      have : lam * (gx - fxOni β κ lam ρ) ^ 2 = 0 := by
        nlinarith [sq_nonneg (gπ - fpiOni β κ lam ρ)]
      exact (mul_eq_zero.mp this).resolve_left hlam.ne'
    exact ⟨by linarith [pow_eq_zero_iff two_ne_zero |>.mp e1],
      by linarith [pow_eq_zero_iff two_ne_zero |>.mp e2]⟩
  · filter_upwards [hL πbar xbar gπ gx, hL 0 0 (fpiOni β κ lam ρ) (fxOni β κ lam ρ)]
      with ω a1 a2
    rw [a1, a2, h1, h2]

/-- **Appendix F.4, stabilization optimality** (Woodford (2003), pp. 512–513 and 713–714), with
genuine conditional expectations: with AR(1) disturbances `u`, `r̂ⁿ` (innovation variances
`s_u, s_r > 0`, uncorrelated innovations, `|ρ_j| < 1`), the corrected optimal noninertial plan
(long-run values (3.11), F.4 responses) satisfies (2.1) and (2.23), and every plan (3.6) satisfying
(2.1) and (2.23) has almost surely a stabilization loss at least as large; the two losses agree
almost surely iff the plan has the F.4 response coefficients. No pull-out or non-degeneracy
hypothesis is needed. -/
theorem f4_lstab {β κ σ rbar lx li istar ρu ρr su sr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1) (hρr : |ρr| < 1)
    (hsu : 0 < su) (hsr : 0 < sr) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) (t₀ : ℕ) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (MAS S β κ (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
        (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) u ∧
      MIS S σ (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
        (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r)
        (fun t ω => rbar + r t ω)) ∧
    ∀ πbar xbar ibar fπ fx fi gπ gx gi,
      MAS S β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u →
      MIS S σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
        (fun t ω => rbar + r t ω) →
      (∀ᵐ ω ∂S.μ, mLstab S β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ω ≤
        mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
          (plan2 ibar fi gi u r) ω) ∧
      (mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
          (plan2 ibar fi gi u r) =ᵐ[S.μ]
        mLstab S β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ↔
        (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) := by
  have hρu1 : ρu < 1 := (abs_lt.mp hρu).2
  have hρr1 : ρr < 1 := (abs_lt.mp hρr).2
  have hK : ∀ ρ s : ℝ, |ρ| < 1 → 0 < s →
      0 < β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s := by
    intro ρ s hρ hs
    have hq1 : ρ ^ 2 < 1 := (sq_lt_one_of_abs hρ).2
    have : 0 < 1 - β := by linarith
    have : 0 < 1 - ρ ^ 2 := by linarith
    have : 0 < 1 - β * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
    unfold uncondVar
    positivity
  have hKu := hK ρu su hρu hsu
  have hKr := hK ρr sr hρr hsr
  set Ku := β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * uncondVar ρu su
  set Kr := β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * uncondVar ρr sr
  have hL : ∀ πbar xbar ibar fπ fx fi gπ gx gi, ∀ᵐ ω ∂S.μ, mLstab S β lx li t₀
      (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r) ω =
      Kr * Noninertial.objF4 lx li gπ gx gi + Ku * Noninertial.objF4 lx li fπ fx fi := by
    intro πbar xbar ibar fπ fx fi gπ gx gi
    filter_upwards [lstab_eq S hβ0.le hβ1 hρu hρr hu hr hind πbar xbar ibar fπ fx fi gπ gx gi t₀
      (lx := lx) (li := li)] with ω h
    rw [h]
    unfold Noninertial.objF4
    ring
  obtain ⟨cu1, cu2⟩ := Noninertial.f4_u_feasible (β := β) (ρ := ρu) hκ hσ hlx.le hli
  obtain ⟨cr1, cr2⟩ := Noninertial.f4_r_feasible (β := β) (ρ := ρr) hκ hσ hlx.le hli
  have hx2 : (1 - β) * Noninertial.piBar119 β li rbar istar = κ * xs := by
    rw [hxs]
    field_simp
  have hiff := plan2_iff S hσ.ne' hu hr hsu.ne' hsr.ne' hind (rbar := rbar) (β := β) (κ := κ)
  refine ⟨(hiff (Noninertial.piBar119 β li rbar istar) xs is _ _ _ _ _ _).mpr
    ⟨⟨hx2, his⟩, ⟨cu1, cu2⟩, ⟨cr1, cr2⟩⟩, ?_⟩
  intro πbar xbar ibar fπ fx fi gπ gx gi hA hI
  obtain ⟨-, ⟨f1, f2⟩, ⟨g1, g2⟩⟩ := (hiff πbar xbar ibar fπ fx fi gπ gx gi).mp ⟨hA, hI⟩
  have hfu := (Noninertial.f4_u_optimal hβ0 hβ1 hρu1 hκ hσ hlx hli
    (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.xUF4 β κ σ lx li ρu)
    (Noninertial.iUF4 β κ σ lx li ρu)).mpr ⟨rfl, rfl, rfl⟩
  have hgr := (Noninertial.f4_r_optimal hβ0 hβ1 hρr1 hκ hσ hlx hli
    (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
    (Noninertial.iRF4 β κ σ lx li ρr)).mpr ⟨rfl, rfl, rfl⟩
  have e1 := hfu.2 fπ fx fi ⟨f1, f2⟩
  have e2 := hgr.2 gπ gx gi ⟨g1, g2⟩
  set Pu := Noninertial.objF4 lx li (Noninertial.piUF4 β κ σ lx li ρu)
    (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.iUF4 β κ σ lx li ρu)
  set Pr := Noninertial.objF4 lx li (Noninertial.piRF4 β κ σ lx li ρr)
    (Noninertial.xRF4 β κ σ lx li ρr) (Noninertial.iRF4 β κ σ lx li ρr)
  set Fu := Noninertial.objF4 lx li fπ fx fi
  set Fr := Noninertial.objF4 lx li gπ gx gi
  have m1 : 0 ≤ Ku * (Fu - Pu) := mul_nonneg hKu.le (by linarith)
  have m2 : 0 ≤ Kr * (Fr - Pr) := mul_nonneg hKr.le (by linarith)
  have hLo := hL (Noninertial.piBar119 β li rbar istar) xs is (Noninertial.piUF4 β κ σ lx li ρu)
    (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.iUF4 β κ σ lx li ρu)
    (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
    (Noninertial.iRF4 β κ σ lx li ρr)
  have hLp := hL πbar xbar ibar fπ fx fi gπ gx gi
  refine ⟨?_, ⟨fun heq => ?_, fun ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ => ?_⟩⟩
  · filter_upwards [hLo, hLp] with ω h1 h2
    rw [h1, h2]
    linarith
  · obtain ⟨ω, h1, h2, h3⟩ := (hLp.and (hLo.and heq)).exists
    rw [h1, h2] at h3
    have z1 : Ku * (Fu - Pu) = 0 := by linarith
    have z2 : Kr * (Fr - Pr) = 0 := by linarith
    have hu0 : Fu = Pu := by linarith [(mul_eq_zero.mp z1).resolve_left hKu.ne']
    have hr0 : Fr = Pr := by linarith [(mul_eq_zero.mp z2).resolve_left hKr.ne']
    refine ⟨(Noninertial.f4_u_optimal hβ0 hβ1 hρu1 hκ hσ hlx hli fπ fx fi).mp
      ⟨⟨f1, f2⟩, fun a b c h => ?_⟩,
      (Noninertial.f4_r_optimal hβ0 hβ1 hρr1 hκ hσ hlx hli gπ gx gi).mp
      ⟨⟨g1, g2⟩, fun a b c h => ?_⟩⟩
    · change Fu ≤ _
      rw [hu0]
      exact hfu.2 a b c h
    · change Fr ≤ _
      rw [hr0]
      exact hgr.2 a b c h
  · filter_upwards [hLo, hLp] with ω h1 h2
    rw [h1, h2, a1, a2, a3, b1, b2, b3]


/-! ### Finite state spaces cannot carry a nondegenerate disturbance -/

/-- Woodford (2003), p. 509 (tool; the information structure behind `E_t`): on a finite state
space the filtration is eventually constant. -/
theorem filtration_stabilizes [Finite Ω] : ∃ T, ∀ t, T ≤ t → S.𝓕 T = S.𝓕 t := by
  have hinj : Function.Injective
      (fun m : MeasurableSpace Ω => {A : Set Ω | MeasurableSet[m] A}) := by
    intro m₁ m₂ h
    ext A
    exact Set.ext_iff.mp h A
  have : Finite (MeasurableSpace Ω) := Finite.of_injective _ hinj
  exact WellFoundedGT.monotone_chain_condition ⟨fun t => S.𝓕 t, fun _ _ h => S.𝓕.mono h⟩

/-- Woodford (2003), pp. 509–511 (why the variance results need a genuine probability model): on
a finite state space, innovations `ε_{t+1}` known at `t + 1` with `E_t ε_{t+1} = 0` and constant
conditional variance `E_t ε²_{t+1} = s` must have `s = 0` (once information stops arriving,
the innovation is known one period early). -/
theorem finite_innov_degenerate [Finite Ω] [MeasurableSingletonClass Ω] {s : ℝ}
    {ε : ℕ → Ω → ℝ} (hε : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (ε (t + 1)))
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hvar : ∀ t, S.E t (ε (t + 1) * ε (t + 1)) =ᵐ[S.μ] fun _ => s) : s = 0 := by
  obtain ⟨T, hT⟩ := filtration_stabilizes S
  have hm : StronglyMeasurable[S.𝓕 T] (ε (T + 1)) := by
    rw [hT (T + 1) (Nat.le_succ T)]
    exact hε T
  have h1 : S.E T (ε (T + 1)) = ε (T + 1) := S.E_of_stronglyMeasurable hm Integrable.of_finite
  have h2 : S.E T (ε (T + 1) * ε (T + 1)) = ε (T + 1) * ε (T + 1) :=
    S.E_of_stronglyMeasurable (hm.mul hm) Integrable.of_finite
  obtain ⟨ω, a, b⟩ := ((hmd T).and (hvar T)).exists
  rw [h1] at a
  rw [h2] at b
  simp only [Pi.zero_apply, Pi.mul_apply] at a b
  rw [a] at b
  linarith

/-- Woodford (2003), pp. 509–511: on a finite state space every `MeasAR1Innov` disturbance has
innovation variance `0`. -/
theorem finite_ar1Innov_degenerate [Finite Ω] [MeasurableSingletonClass Ω] {ρ s : ℝ}
    {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) : s = 0 :=
  finite_innov_degenerate S hu.innov_meas hu.2.2.2.1 hu.2.2.2.2

omit mΩ in
/-- Woodford (2003), pp. 509–511 (the core statements on event trees): no finite event tree
carries an AR(1) disturbance `Noninertial.AR1Innov` with innovation variance `s ≠ 0`, so the core
`lstab12_hasSum`, `prop_7_11_lstab`, `f4_lstab` have content on trees only at `s = 0`. -/
theorem tree_innov_degenerate {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω')
    {ρ s : ℝ} {u ε : ℕ → Ω' → ℝ} (h : Noninertial.AR1Innov T.toExpectationSystem ρ s u ε) :
    s = 0 := by
  let _ : MeasurableSpace Ω' := ⊤
  have : DiscreteMeasurableSpace Ω' := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hE : ∀ t x, (TreeBridge.treeSystem T).E t x = T.condE t x := TreeBridge.treeSystem_E T
  refine finite_innov_degenerate (TreeBridge.treeSystem T) (ε := ε) (fun t => ?_)
    (fun t => ?_) (fun t => ?_)
  · have hεe : ε (t + 1) = u (t + 1) - ρ • u t := by rw [h.2.1 t, add_sub_cancel_left]
    have hk : T.toExpectationSystem.E (t + 1) (ε (t + 1)) = ε (t + 1) := by
      rw [hεe, map_sub, map_smul, h.1 (t + 1), ← h.1 t,
        T.toExpectationSystem.known (Nat.le_succ t)]
    rw [← hk]
    exact TreeBridge.stronglyMeasurable_condE T (t + 1) _
  · rw [hE]
    exact Eventually.of_forall (congrFun (h.2.2.1 t))
  · rw [hE]
    exact Eventually.of_forall (congrFun (h.2.2.2 t))

/-! ### Links to the core statements on finite, fully supported state spaces -/

/-- Woodford (2003), eqs. (2.18) and (2.27): on a finite fully supported space a `MeasAR1Innov`
disturbance is a core `Noninertial.AR1Innov` disturbance of the bridged core system. -/
theorem toCore_AR1Innov [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {ρ s : ℝ} {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) :
    Noninertial.AR1Innov (S.toExpectationSystem hfull) ρ s u ε :=
  ⟨fun t => S.E_of_stronglyMeasurable (hu.1 t) Integrable.of_finite, hu.2.2.1,
    fun t => S.eq_of_ae_eq hfull (hu.2.2.2.1 t), fun t => S.eq_of_ae_eq hfull (hu.2.2.2.2 t)⟩

/-- Woodford (2003), eq. (2.18): on a finite fully supported space a `MeasAR1Innov` disturbance
whose date-0 innovation is known at 0 is a core `VarianceFrontier.AR1Innov` disturbance with
constant innovation variances. -/
theorem toCore_VF_AR1Innov [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {ρ s : ℝ} {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε)
    (hε0 : StronglyMeasurable[S.𝓕 0] (ε 0)) :
    VarianceFrontier.AR1Innov (S.toExpectationSystem hfull) ρ (fun _ => s) u ε := by
  refine ⟨fun t => S.E_of_stronglyMeasurable (hu.1 t) Integrable.of_finite, fun t => ?_,
    hu.2.2.1, fun t => S.eq_of_ae_eq hfull (hu.2.2.2.1 t),
    fun t => S.eq_of_ae_eq hfull (hu.2.2.2.2 t)⟩
  cases t with
  | zero => exact S.E_of_stronglyMeasurable hε0 Integrable.of_finite
  | succ t => exact S.E_of_stronglyMeasurable (hu.innov_meas t) Integrable.of_finite

/-- Woodford (2003), p. 511: on a finite fully supported space a disturbance with innovation
variance `s ≠ 0` is non-degenerate in the core sense `Noninertial.Nondeg1`. -/
theorem toCore_nondeg1 [Finite Ω] [DiscreteMeasurableSpace Ω] {ρ s : ℝ} {u ε : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρ s u ε) (hs : s ≠ 0) : Noninertial.Nondeg1 u := by
  by_contra hcon
  simp only [Noninertial.Nondeg1, not_exists, ne_eq, not_not] at hcon
  obtain ⟨ω₀, -⟩ := (Eventually.of_forall (f := ae S.μ) fun _ : Ω => True.intro).exists
  have key := affine_zero1 S hu hs (a := -u 0 ω₀) (b := 1) fun t =>
    Eventually.of_forall fun ω => by
      change -u 0 ω₀ + 1 * u t ω = 0
      rw [hcon t ω 0 ω₀]
      ring
  exact one_ne_zero key.2

/-- Woodford (2003), p. 512: on a finite fully supported space two disturbances with nonzero,
uncorrelated innovation variances are non-degenerate as a pair in the core sense
`Noninertial.Nondeg2`. -/
theorem toCore_nondeg2 [Finite Ω] [DiscreteMeasurableSpace Ω] {ρu ρr su sr : ℝ}
    {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu) (hr : MeasAR1Innov S ρr sr r εr)
    (hsu : su ≠ 0) (hsr : sr ≠ 0)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) :
    Noninertial.Nondeg2 u r := by
  by_contra hcon
  simp only [Noninertial.Nondeg2, not_exists, ne_eq, not_not] at hcon
  obtain ⟨ω₀, -⟩ := (Eventually.of_forall (f := ae S.μ) fun _ : Ω => True.intro).exists
  by_cases hex : ∃ t₂ ω₂, u t₂ ω₂ ≠ u 0 ω₀ ∨ r t₂ ω₂ ≠ r 0 ω₀
  · obtain ⟨t₂, ω₂, hne⟩ := hex
    have key := affine_zero2 S hu hr hsu hsr hind
      (a := -((r t₂ ω₂ - r 0 ω₀) * u 0 ω₀ - (u t₂ ω₂ - u 0 ω₀) * r 0 ω₀))
      (b := r t₂ ω₂ - r 0 ω₀) (c := -(u t₂ ω₂ - u 0 ω₀)) fun t =>
        Eventually.of_forall fun ω => by
          change -((r t₂ ω₂ - r 0 ω₀) * u 0 ω₀ - (u t₂ ω₂ - u 0 ω₀) * r 0 ω₀) +
            (r t₂ ω₂ - r 0 ω₀) * u t ω + -(u t₂ ω₂ - u 0 ω₀) * r t ω = 0
          linear_combination -hcon 0 ω₀ t₂ ω₂ t ω
    rcases hne with h | h
    · exact h (by linarith [key.2.2])
    · exact h (by linarith [key.2.1])
  · simp only [not_exists, not_or, ne_eq, not_not] at hex
    have key := affine_zero2 S hu hr hsu hsr hind (a := -u 0 ω₀) (b := 1) (c := 0) fun t =>
      Eventually.of_forall fun ω => by
        change -u 0 ω₀ + 1 * u t ω + 0 * r t ω = 0
        rw [(hex t ω).1]
        ring
    exact one_ne_zero key.2.1

/-- Woodford (2003), eq. (2.1), p. 486: on a finite fully supported space the almost-sure
aggregate-supply relation is the core relation `Noninertial.AS` of the bridged core system. -/
theorem mAS_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (β κ : ℝ) (π x u : ℕ → Ω → ℝ) :
    MAS S β κ π x u ↔ Noninertial.AS (S.toExpectationSystem hfull) β κ π x u :=
  ⟨fun h t => S.eq_of_ae_eq hfull (h t), fun h t => Eventually.of_forall (congrFun (h t))⟩

/-- Woodford (2003), eq. (2.23), p. 502: on a finite fully supported space the almost-sure IS
relation is the core relation `Noninertial.IS` of the bridged core system. -/
theorem mIS_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (σ : ℝ) (π x i rn : ℕ → Ω → ℝ) :
    MIS S σ π x i rn ↔ Noninertial.IS (S.toExpectationSystem hfull) σ π x i rn :=
  ⟨fun h t => S.eq_of_ae_eq hfull (h t), fun h t => Eventually.of_forall (congrFun (h t))⟩

/-- Woodford (2003), p. 509: on a finite fully supported space Mathlib's conditional variance
`Var[X; μ | 𝓕 t]` is, at every state, the core conditional variance
`E_t X² − (E_t X)²` (`VarianceFrontier.condCov`) of the bridged core system. -/
theorem condVar_eq_condCov [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (t : ℕ) (X : Ω → ℝ) :
    Var[X; S.μ | S.𝓕 t] = VarianceFrontier.condCov (S.toExpectationSystem hfull) t X X := by
  refine S.eq_of_ae_eq hfull ?_
  filter_upwards [condVar_ae_eq_condExp_sq_sub_sq_condExp (S.𝓕.le t)
    (MemLp.of_discrete (f := X) (p := 2) (μ := S.μ))] with ω h
  rw [h]
  simp only [VarianceFrontier.condCov, MeasExpectationSystem.toExpectationSystem_E, Pi.sub_apply,
    Pi.mul_apply, sq]

/-- Woodford (2003), p. 509: on a finite fully supported space the stabilization loss with
genuine conditional variances is, at every state, the core loss `Noninertial.Lstab12`. -/
theorem lstab12_agree [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (β lam : ℝ) (t₀ : ℕ) (π x : ℕ → Ω → ℝ) (ω : Ω) :
    mLstab12 S β lam t₀ π x ω = Noninertial.Lstab12 (S.toExpectationSystem hfull) β lam t₀ π x ω
    := by
  unfold mLstab12 Noninertial.Lstab12
  simp only [condVar_eq_condCov S hfull]

/-- Woodford (2003), p. 512: on a finite fully supported space the three-variable stabilization
loss with genuine conditional variances is, at every state, the core loss `Noninertial.Lstab`. -/
theorem lstab_agree [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (β lx li : ℝ) (t₀ : ℕ) (π x i : ℕ → Ω → ℝ) (ω : Ω) :
    mLstab S β lx li t₀ π x i ω =
      Noninertial.Lstab (S.toExpectationSystem hfull) β lx li t₀ π x i ω := by
  unfold mLstab Noninertial.Lstab
  simp only [condVar_eq_condCov S hfull]

/-- Woodford (2003), eq. (3.4), p. 511, through the bridge: on a finite fully supported space the
core theorem `Noninertial.lstab12_hasSum` applies to a `MeasAR1Innov` disturbance and gives
`L^stab` at every state (agreeing with the almost-sure `lstab12_eq`). -/
theorem lstab12_link [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {β lam ρ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1) {u ε : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρ s u ε) (πbar xbar fπ fx : ℝ) (t₀ : ℕ) (ω : Ω) :
    mLstab12 S β lam t₀ (plan1 πbar fπ u) (plan1 xbar fx u) ω =
      β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
        uncondVar ρ s := by
  rw [lstab12_agree S hfull]
  exact (Noninertial.lstab12_hasSum _ (S.toExpectationSystem_pullOut hfull) hβ0 hβ1 hρ
    (toCore_AR1Innov S hfull hu) πbar xbar fπ fx t₀ ω).tsum_eq

/-- Woodford (2003), eqs. (3.7)–(3.8), p. 513, through the bridge: on a finite fully supported
space the core theorem `Noninertial.lstab_hasSum` applies and gives `L^stab` at every state. -/
theorem lstab_link [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρu : |ρu| < 1) (hρr : |ρr| < 1)
    {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu) (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) (t₀ : ℕ) (ω : Ω) :
    mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r) ω =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su := by
  rw [lstab_agree S hfull]
  exact (Noninertial.lstab_hasSum _ (S.toExpectationSystem_pullOut hfull) hβ0 hβ1 hρu hρr
    (toCore_AR1Innov S hfull hu) (toCore_AR1Innov S hfull hr)
    (fun t => S.eq_of_ae_eq hfull (hind t)) πbar xbar ibar fπ fx fi gπ gx gi t₀ ω).tsum_eq

/-- Woodford (2003), eq. (3.4), p. 511, through the bridge to `VarianceFrontier.Lstab_ar1`: on a
finite fully supported space the stabilization loss of a plan (2.19) is, at every state, the
closed form (3.4). -/
theorem Lstab_ar1_link [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {β ρ s lam pibar xbar fπ fx : ℝ} {u ε : ℕ → Ω → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ : ρ ^ 2 < 1) (hu : MeasAR1Innov S ρ s u ε) (hε0 : StronglyMeasurable[S.𝓕 0] (ε 0))
    (t₀ : ℕ) (ω : Ω) :
    mLstab12 S β lam t₀ (VarianceFrontier.fwdPlan pibar fπ u) (VarianceFrontier.fwdPlan xbar fx u)
      ω = β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
        (s / (1 - ρ ^ 2)) := by
  unfold mLstab12
  simp only [condVar_eq_condCov S hfull]
  exact VarianceFrontier.Lstab_ar1 _ (S.toExpectationSystem_pullOut hfull) hβ0 hβ1 hρ
    (toCore_VF_AR1Innov S hfull hu hε0) (fun _ => rfl) t₀ ω

/-- Woodford (2003), eqs. (3.7)–(3.8), pp. 512–513, through the bridge to
`VarianceFrontier.Lstab_two_shocks`: on a finite fully supported space the stabilization loss of a
plan (3.6) splits, at every state, as `L^{stab,r} + L^{stab,u}`. -/
theorem Lstab_two_shocks_link [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {β ρu ρr su sr lamx lami : ℝ} {u εu r εr : ℕ → Ω → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρu : ρu ^ 2 < 1) (hρr : ρr ^ 2 < 1) (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr) (hεu0 : StronglyMeasurable[S.𝓕 0] (εu 0))
    (hεr0 : StronglyMeasurable[S.𝓕 0] (εr 0))
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0)
    (pibar xbar ibar fπ fx fi gπ gx gi : ℝ) (t₀ : ℕ) (ω : Ω) :
    mLstab S β lamx lami t₀ (plan2 pibar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
      ω =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lamx * gx ^ 2 + lami * gi ^ 2) *
          (sr / (1 - ρr ^ 2)) +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) *
          (fπ ^ 2 + lamx * fx ^ 2 + lami * fi ^ 2) * (su / (1 - ρu ^ 2)) := by
  unfold mLstab
  simp only [condVar_eq_condCov S hfull]
  exact VarianceFrontier.Lstab_two_shocks _ (S.toExpectationSystem_pullOut hfull) hβ0 hβ1 hρu hρr
    (toCore_VF_AR1Innov S hfull hu hεu0) (toCore_VF_AR1Innov S hfull hr hεr0) (fun _ => rfl)
    (fun _ => rfl) (fun t => S.eq_of_ae_eq hfull (hind t)) pibar xbar ibar fπ fx fi gπ gx gi t₀ ω

/-- **Proposition 7.11**, stabilization form, through the bridge (Woodford (2003), pp. 509–511):
on a finite fully supported space the measure-theoretic hypotheses (with `s > 0`) give every
hypothesis of the core `Noninertial.prop_7_11_lstab` (pull-out, `AR1Innov`, `Nondeg1`), so its
conclusion holds for the bridged core system. By `finite_ar1Innov_degenerate` these hypotheses
are never met on a finite space; the genuine content is `prop_7_11_lstab`. -/
theorem prop_7_11_link [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {β κ lam ρ s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (hρ : |ρ| < 1)
    (hs : 0 < s) {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (t₀ : ℕ) (ω : Ω) :
    Noninertial.AS (S.toExpectationSystem hfull) β κ (plan1 0 (fpiOni β κ lam ρ) u)
      (plan1 0 (fxOni β κ lam ρ) u) u ∧
    ∀ πbar xbar gπ gx, Noninertial.AS (S.toExpectationSystem hfull) β κ (plan1 πbar gπ u)
        (plan1 xbar gx u) u →
      Noninertial.Lstab12 (S.toExpectationSystem hfull) β lam t₀ (plan1 0 (fpiOni β κ lam ρ) u)
          (plan1 0 (fxOni β κ lam ρ) u) ω ≤
        Noninertial.Lstab12 (S.toExpectationSystem hfull) β lam t₀ (plan1 πbar gπ u)
          (plan1 xbar gx u) ω ∧
      (Noninertial.Lstab12 (S.toExpectationSystem hfull) β lam t₀ (plan1 πbar gπ u)
          (plan1 xbar gx u) ω =
        Noninertial.Lstab12 (S.toExpectationSystem hfull) β lam t₀ (plan1 0 (fpiOni β κ lam ρ) u)
          (plan1 0 (fxOni β κ lam ρ) u) ω ↔
        gπ = fpiOni β κ lam ρ ∧ gx = fxOni β κ lam ρ) :=
  Noninertial.prop_7_11_lstab _ (S.toExpectationSystem_pullOut hfull) hβ0 hβ1 hκ hlam hρ hs
    (toCore_AR1Innov S hfull hu) (toCore_nondeg1 S hu hs.ne') t₀ ω

/-- **Appendix F.4**, stabilization optimality, through the bridge (Woodford (2003),
pp. 512–513, 713–714): on a finite fully supported space the measure-theoretic hypotheses give
every hypothesis of the core `Noninertial.f4_lstab` (pull-out, two `AR1Innov`, uncorrelated
innovations, `Nondeg2`), so its conclusion holds for the bridged core system. By
`finite_ar1Innov_degenerate` these hypotheses are never met on a finite space; the genuine content
is `f4_lstab`. -/
theorem f4_link [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {β κ σ rbar lx li istar ρu ρr su sr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1) (hρr : |ρr| < 1) (hsu : 0 < su)
    (hsr : 0 < sr) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) (t₀ : ℕ) (ω : Ω)
    {xs is : ℝ} (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (Noninertial.AS (S.toExpectationSystem hfull) β κ
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) u ∧
      Noninertial.IS (S.toExpectationSystem hfull) σ
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r)
        (fun t ω => rbar + r t ω)) ∧
    ∀ πbar xbar ibar fπ fx fi gπ gx gi,
      Noninertial.AS (S.toExpectationSystem hfull) β κ (plan2 πbar fπ gπ u r)
        (plan2 xbar fx gx u r) u →
      Noninertial.IS (S.toExpectationSystem hfull) σ (plan2 πbar fπ gπ u r)
        (plan2 xbar fx gx u r) (plan2 ibar fi gi u r) (fun t ω => rbar + r t ω) →
      Noninertial.Lstab (S.toExpectationSystem hfull) β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ω ≤
        Noninertial.Lstab (S.toExpectationSystem hfull) β lx li t₀ (plan2 πbar fπ gπ u r)
          (plan2 xbar fx gx u r) (plan2 ibar fi gi u r) ω ∧
      (Noninertial.Lstab (S.toExpectationSystem hfull) β lx li t₀ (plan2 πbar fπ gπ u r)
          (plan2 xbar fx gx u r) (plan2 ibar fi gi u r) ω =
        Noninertial.Lstab (S.toExpectationSystem hfull) β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ω ↔
        (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) :=
  Noninertial.f4_lstab _ (S.toExpectationSystem_pullOut hfull) hβ0 hβ1 hκ hσ hlx hli hρu hρr
    hsu hsr (toCore_AR1Innov S hfull hu) (toCore_AR1Innov S hfull hr)
    (fun t => S.eq_of_ae_eq hfull (hind t)) (toCore_nondeg2 S hu hr hsu.ne' hsr.ne' hind) t₀ ω
    hxs his

end Woodford.GainsFromCommitment.NoninertialMeasure
