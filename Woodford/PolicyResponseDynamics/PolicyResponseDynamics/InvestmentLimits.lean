/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.Prop51

/-!
# The aggregate-supply block with investment: (3.16)–(3.19) and the large-`ε_ψ` limit

Woodford (2003), *Interest and Prices*, Chapter 5, §3.2–3.3, pp. 359–364.

Quasi-differencing the pricing relation (3.14) of Proposition 5.1 with the operator
`E_t(1 − αβL⁻¹)(1 − μ₂⁻¹L⁻¹)` gives (3.16); with `π_t = ((1 − α)/α) p̂*_t` this is the inflation
equation (3.17) `π_t = ξ₀ŝ_t − ξ₁E_tŝ_{t+1} + ψ₁E_tπ_{t+1} − ψ₂E_tπ_{t+2}`. Solving it forward gives
(3.19) `π_t = ∑ Ψ_j E_t ŝ_{t+j}`. As the adjustment cost `ε_ψ → ∞` the coefficients tend to those
of the basic model and the inflation equation has the same bounded solutions as
`π_t = ξŝ_t + βE_tπ_{t+1}`.

## Main results

* `qd2_eq_qd1`, `qd1_of_solves`: the quasi-difference operators `E_t(1 − rL⁻¹)` and
  `E_t(1 − r₁L⁻¹)(1 − r₂L⁻¹)`.
* `eq314_iff_eq316`: for bounded adapted processes, (3.14) at every date holds iff (3.16) holds
  at every date (the quasi-difference is exact, and invertible, on bounded sequences).
* `eq316_iff_eq317`, `eq314_iff_eq317`: with `π_t = ((1−α)/α)p̂*_t`, (3.16) is equivalent to
  (3.17) with the printed `ξ₀, ξ₁ = μ₂⁻¹ξ₀, ψ₁, ψ₂ = βμ₂⁻¹`.
* (3.19): `basic_eq319` (basic model, `Ψ_j = ξβʲ`, the unique bounded solution);
  `sol317_solves`, `eq_sol317`, `sol317_eq_Psi` (extended model: under the root condition of
  footnote 31 — Schur–Cohn for `z² − ψ₁z + ψ₂` — the unique bounded solution is
  `π_t = ∑ Ψ_j E_t ŝ_{t+j}` with `Ψ_0 = ξ₀`, `Ψ_{j+1} = ξ₀c_{j+1} − ξ₁c_j`, `c` the
  Cayley–Hamilton sequence); `determinate317_iff` (the root condition is also necessary).
* Limits as `ε_ψ → ∞` (genuine `Filter.Tendsto`): `tendsto_mu1` (`μ₁ → 1`), `tendsto_mu2`
  (`μ₂ → β⁻¹`), `tendsto_aM` (`a → (1+ωθ)/(1−αβ)`), `tendsto_bM` (`b → 0`), `tendsto_xi0M`
  (`ξ₀ → ξ`), `tendsto_xi1M` (`ξ₁ → βξ`), `tendsto_psi1M` (`ψ₁ → 2β`), `tendsto_psi2M`
  (`ψ₂ → β²`); `eventually_ab_pos` (for all large `ε_ψ`, `αβμ₂ < 1`, so `a, b > 0`);
  `eventually_schurStable` (for all large `ε_ψ` the root condition holds).
* `limit_relation_iff`: the limiting form of (3.17) has the same bounded solutions as
  `π_t = ξŝ_t + βE_tπ_{t+1}`; `Psi_limit`: in the limit `Ψ_j = ξβʲ`.
-/

namespace Woodford.PolicyResponseDynamics.InvestmentLimits

open Filter Topology Woodford.PolicyResponseDynamics.Prop51

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω) {P : Params}

/-! ### Quasi-difference operators -/

/-- Woodford (2003), (3.16) p. 360: `E_t(1 − rL⁻¹)X_t = E_t X_t − r E_t X_{t+1}`. -/
def qd1 (r : ℝ) (X : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := 𝔼.E t (X t) - r • 𝔼.E t (X (t + 1))

/-- Woodford (2003), (3.16) p. 360: `E_t(1 − r₁L⁻¹)(1 − r₂L⁻¹)X_t
= E_t X_t − (r₁ + r₂)E_t X_{t+1} + r₁r₂ E_t X_{t+2}`. -/
def qd2 (r₁ r₂ : ℝ) (X : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (X t) - (r₁ + r₂) • 𝔼.E t (X (t + 1)) + (r₁ * r₂) • 𝔼.E t (X (t + 2))

/-- Woodford (2003), (3.16) p. 360: the second-order operator is the composition of the two
first-order ones (law of iterated expectations). -/
theorem qd2_eq_qd1 (r₁ r₂ : ℝ) (X : ℕ → Ω → ℝ) (t : ℕ) :
    qd2 𝔼 r₁ r₂ X t = qd1 𝔼 r₁ (qd1 𝔼 r₂ X) t := by
  unfold qd1 qd2
  simp only [map_sub, map_smul, 𝔼.E_E_self, 𝔼.tower (Nat.le_succ t)]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (3.16) p. 360: the two factors commute. -/
theorem qd2_comm (r₁ r₂ : ℝ) (X : ℕ → Ω → ℝ) (t : ℕ) :
    qd2 𝔼 r₁ r₂ X t = qd2 𝔼 r₂ r₁ X t := by
  unfold qd2; rw [add_comm r₁, mul_comm r₁]

/-- Woodford (2003), (3.16) p. 360: if `F_t = r E_t F_{t+1} + u_t` with `u` adapted, then
`E_t(1 − rL⁻¹)F_t = u_t`. -/
theorem qd1_of_solves {r : ℝ} {u F : ℕ → Ω → ℝ} (hF : ForwardSolution.Solves 𝔼 r u F)
    (hu : 𝔼.Adapted u) (t : ℕ) : qd1 𝔼 r F t = u t := by
  unfold qd1
  conv_lhs => rw [hF t]
  rw [map_add, map_smul, 𝔼.E_E_self, hu t]
  abel

/-- Woodford (2003), (3.16) p. 360: `qd2` is linear. -/
theorem qd2_lin (r₁ r₂ c d e : ℝ) (X Y Z : ℕ → Ω → ℝ) (t : ℕ) :
    qd2 𝔼 r₁ r₂ (fun τ => c • X τ + d • Y τ - e • Z τ) t =
      c • qd2 𝔼 r₁ r₂ X t + d • qd2 𝔼 r₁ r₂ Y t - e • qd2 𝔼 r₁ r₂ Z t := by
  unfold qd2
  funext ω
  simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Woodford (2003), (3.16) p. 360: `qd1` is linear. -/
theorem qd1_lin (r c d : ℝ) (X Y : ℕ → Ω → ℝ) (t : ℕ) :
    qd1 𝔼 r (fun τ => c • X τ - d • Y τ) t = c • qd1 𝔼 r X t - d • qd1 𝔼 r Y t := by
  unfold qd1
  funext ω
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### (3.14) ⟺ (3.16) -/

/-- Woodford (2003), (3.14) p. 359: the forcing `u_τ = r E_τ π_{τ+1}`, so that
`∑_k rᵏ E_t u_{t+k} = ∑_{k ≥ 1} rᵏ E_t π_{t+k}`. -/
def uPi (r : ℝ) (infl : ℕ → Ω → ℝ) (τ : ℕ) : Ω → ℝ := r • 𝔼.E τ (infl (τ + 1))

/-- Woodford (2003), (3.14) p. 359: the right-hand side
`∑_{k≥0} xᵏ E_t ŝ_{t+k} + a ∑_{k≥1} xᵏ E_t π_{t+k} − b ∑_{k≥1} mᵏ E_t π_{t+k}`
(with `x = αβ`, `m = μ₂⁻¹`). -/
noncomputable def rhs314 (a b x m : ℝ) (s infl : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, x ^ k * 𝔼.E t (s (t + k)) ω +
    a * ∑' k, x ^ (k + 1) * 𝔼.E t (infl (t + k + 1)) ω -
    b * ∑' k, m ^ (k + 1) * 𝔼.E t (infl (t + k + 1)) ω

/-- Woodford (2003), (3.14) p. 359: the `π` sums are forward series of `uPi`. -/
theorem forwardSeries_uPi (r : ℝ) (infl : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries r (uPi 𝔼 r infl) t ω = ∑' k, r ^ (k + 1) * 𝔼.E t (infl (t + k + 1)) ω := by
  unfold ExpectationSystem.forwardSeries uPi
  refine tsum_congr fun k => ?_
  rw [map_smul, 𝔼.tower (Nat.le_add_right t k), Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-- Woodford (2003), (3.14) p. 359: the right-hand side as a combination of forward series. -/
theorem rhs314_eq (a b x m : ℝ) (s infl : ℕ → Ω → ℝ) (t : ℕ) :
    rhs314 𝔼 a b x m s infl t = 𝔼.forwardSeries x s t + a • 𝔼.forwardSeries x (uPi 𝔼 x infl) t -
      b • 𝔼.forwardSeries m (uPi 𝔼 m infl) t := by
  funext ω
  simp only [rhs314, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    forwardSeries_uPi]
  rfl

/-- Woodford (2003), (3.16) p. 360: `E_t(1 − αβL⁻¹)(1 − μ₂⁻¹L⁻¹)` applied to the right-hand side
of (3.14) gives the right-hand side of (3.16):
`E_t(1 − μ₂⁻¹L⁻¹)ŝ_t + aαβ E_t(1 − μ₂⁻¹L⁻¹)π_{t+1} − bμ₂⁻¹ E_t(1 − αβL⁻¹)π_{t+1}`. -/
theorem qd2_rhs314 {a b x m Bs Bπ : ℝ} (hx : |x| < 1) (hm : |m| < 1) {s infl : ℕ → Ω → ℝ}
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (hsa : 𝔼.Adapted s) (hπ : ∀ τ ω, |infl τ ω| ≤ Bπ) (t : ℕ) :
    qd2 𝔼 x m (rhs314 𝔼 a b x m s infl) t =
      qd1 𝔼 m s t + (a * x) • qd1 𝔼 m (fun τ => infl (τ + 1)) t -
        (b * m) • qd1 𝔼 x (fun τ => infl (τ + 1)) t := by
  have hub : ∀ r, |r| < 1 → ∀ τ ω, |uPi 𝔼 r infl τ ω| ≤ |r| * Bπ := fun r _ τ ω => by
    unfold uPi; rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hπ (τ + 1)) τ ω) (abs_nonneg _)
  have hua : ∀ r, 𝔼.Adapted (uPi 𝔼 r infl) := fun r τ => by
    unfold uPi; rw [map_smul, 𝔼.E_E_self]
  have hF := ForwardSolution.forwardSeries_solves_abs 𝔼 hx hs hsa
  have hG := ForwardSolution.forwardSeries_solves_abs 𝔼 hx (hub x hx) (hua x)
  have hH := ForwardSolution.forwardSeries_solves_abs 𝔼 hm (hub m hm) (hua m)
  have e : rhs314 𝔼 a b x m s infl = fun τ => (1 : ℝ) • 𝔼.forwardSeries x s τ +
      a • 𝔼.forwardSeries x (uPi 𝔼 x infl) τ - b • 𝔼.forwardSeries m (uPi 𝔼 m infl) τ := by
    funext τ; rw [rhs314_eq, one_smul]
  rw [e, qd2_lin, one_smul, qd2_comm 𝔼 x m (𝔼.forwardSeries x s),
    qd2_comm 𝔼 x m (𝔼.forwardSeries x (uPi 𝔼 x infl)), qd2_eq_qd1, qd2_eq_qd1, qd2_eq_qd1]
  have e1 : qd1 𝔼 x (𝔼.forwardSeries x s) = s := funext (qd1_of_solves 𝔼 hF hsa)
  have e2 : qd1 𝔼 x (𝔼.forwardSeries x (uPi 𝔼 x infl)) = uPi 𝔼 x infl :=
    funext (qd1_of_solves 𝔼 hG (hua x))
  have e3 : qd1 𝔼 m (𝔼.forwardSeries m (uPi 𝔼 m infl)) = uPi 𝔼 m infl :=
    funext (qd1_of_solves 𝔼 hH (hua m))
  rw [e1, e2, e3]
  unfold qd1 uPi
  funext ω
  simp only [map_smul, 𝔼.E_E_self, 𝔼.tower (Nat.le_succ t), Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (3.16) p. 360 (the quasi-difference is exact on bounded sequences): for
bounded adapted `ŝ`, `p̂*` and bounded `π`, with `|αβ| < 1` and `|μ₂⁻¹| < 1`, (3.14) holds at every
date iff (3.16) holds at every date. -/
theorem eq314_iff_eq316 {a b x m Bs Bπ Bp : ℝ} (hx : |x| < 1) (hm : |m| < 1)
    {s infl pstar : ℕ → Ω → ℝ} (hs : ∀ τ ω, |s τ ω| ≤ Bs) (hsa : 𝔼.Adapted s)
    (hπ : ∀ τ ω, |infl τ ω| ≤ Bπ) (hp : ∀ τ ω, |pstar τ ω| ≤ Bp) (hpa : 𝔼.Adapted pstar) :
    (∀ t, (a - b) • pstar t = rhs314 𝔼 a b x m s infl t) ↔
      ∀ t, (a - b) • qd2 𝔼 x m pstar t =
        qd1 𝔼 m s t + (a * x) • qd1 𝔼 m (fun τ => infl (τ + 1)) t -
          (b * m) • qd1 𝔼 x (fun τ => infl (τ + 1)) t := by
  have hlin : ∀ t, (a - b) • qd2 𝔼 x m pstar t =
      qd2 𝔼 x m (fun τ => (a - b) • pstar τ + (0 : ℝ) • pstar τ - (0 : ℝ) • pstar τ) t := by
    intro t; rw [qd2_lin]; simp
  constructor
  · intro h t
    rw [hlin, ← qd2_rhs314 𝔼 hx hm hs hsa hπ t]
    congr 1
    funext τ
    simp [h τ]
  · intro h
    -- the difference `e = (a − b)p̂* − rhs` is bounded, adapted and annihilated by `qd2`
    have hub : ∀ r, |r| < 1 → ∀ τ ω, |uPi 𝔼 r infl τ ω| ≤ |r| * Bπ := fun r _ τ ω => by
      unfold uPi; rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hπ (τ + 1)) τ ω) (abs_nonneg _)
    have hua : ∀ r, 𝔼.Adapted (uPi 𝔼 r infl) := fun r τ => by
      unfold uPi; rw [map_smul, 𝔼.E_E_self]
    obtain ⟨BF, hBF⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 hx hs
    obtain ⟨BG, hBG⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 hx (hub x hx)
    obtain ⟨BH, hBH⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 hm (hub m hm)
    have haF := ForwardSolution.forwardSeries_adapted_abs 𝔼 hx hs
    have haG := ForwardSolution.forwardSeries_adapted_abs 𝔼 hx (hub x hx)
    have haH := ForwardSolution.forwardSeries_adapted_abs 𝔼 hm (hub m hm)
    set e : ℕ → Ω → ℝ := fun τ => (a - b) • pstar τ + (0 : ℝ) • pstar τ -
      (1 : ℝ) • rhs314 𝔼 a b x m s infl τ with he
    have heb : ∀ τ ω, |e τ ω| ≤ |a - b| * Bp + (BF + |a| * BG + |b| * BH) := by
      intro τ ω
      simp only [he, rhs314_eq, one_smul, zero_smul, add_zero, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      have h1 : |(a - b) * pstar τ ω| ≤ |a - b| * Bp := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hp τ ω) (abs_nonneg _)
      have h2 : |a * 𝔼.forwardSeries x (uPi 𝔼 x infl) τ ω| ≤ |a| * BG := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hBG τ ω) (abs_nonneg _)
      have h3 : |b * 𝔼.forwardSeries m (uPi 𝔼 m infl) τ ω| ≤ |b| * BH := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hBH τ ω) (abs_nonneg _)
      have h4 := hBF τ ω
      have := abs_sub (a - b) 0
      calc _ ≤ |(a - b) * pstar τ ω| + (|𝔼.forwardSeries x s τ ω| +
            |a * 𝔼.forwardSeries x (uPi 𝔼 x infl) τ ω| +
            |b * 𝔼.forwardSeries m (uPi 𝔼 m infl) τ ω|) := by
            refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
            exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := by linarith
    have hea : 𝔼.Adapted e := by
      intro τ
      simp only [he, rhs314_eq, one_smul, zero_smul, add_zero, map_sub, map_add, map_smul,
        hpa τ, haF τ, haG τ, haH τ]
    have he2 : ∀ t, qd2 𝔼 x m e t = 0 := by
      intro t
      rw [he, qd2_lin 𝔼 x m (a - b) 0 1 pstar pstar, qd2_rhs314 𝔼 hx hm hs hsa hπ t, h t]
      simp only [zero_smul, add_zero, one_smul, sub_self]
    -- `Y = qd1 m e` solves `Y_t = x E_t Y_{t+1}` and is bounded, hence zero
    set Y : ℕ → Ω → ℝ := qd1 𝔼 m e with hY
    have hYa : 𝔼.Adapted Y := fun τ => by
      simp only [hY, qd1, map_sub, map_smul, 𝔼.E_E_self]
    have hYs : ∀ t, Y t = x • 𝔼.E t (Y (t + 1)) + 0 := by
      intro t
      have h1 : qd1 𝔼 x Y t = 0 := by rw [hY, ← qd2_eq_qd1]; exact he2 t
      unfold qd1 at h1
      rw [hYa t] at h1
      rw [add_zero]; exact sub_eq_zero.mp h1
    have hYb : BoundedProc Y := ⟨(1 + |m|) * (|a - b| * Bp + (BF + |a| * BG + |b| * BH)),
      fun τ ω => by
        simp only [hY, qd1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have h1 := 𝔼.abs_E_le (heb τ) τ ω
        have h2 := 𝔼.abs_E_le (heb (τ + 1)) τ ω
        calc _ ≤ |𝔼.E τ (e τ) ω| + |m * 𝔼.E τ (e (τ + 1)) ω| := abs_sub _ _
          _ ≤ _ := by
            rw [abs_mul]
            nlinarith [abs_nonneg m, abs_nonneg (𝔼.E τ (e (τ + 1)) ω)]⟩
    have hz : ∀ r : ℝ, ∀ t, (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) t =
        r • 𝔼.E t ((fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) (t + 1)) + 0 := by
      intro r t
      have : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
      simp only [this, map_zero, smul_zero, add_zero]
    have hY0 : Y = fun _ _ => 0 := 𝔼.forward_unique hx hYs (hz x) hYb
      ⟨0, fun _ _ => by simp⟩
    -- then `e_t = m E_t e_{t+1}`, so `e = 0`
    have hes : ∀ t, e t = m • 𝔼.E t (e (t + 1)) + 0 := by
      intro t
      have h0 : qd1 𝔼 m e t = 0 := by rw [← hY]; exact congrFun hY0 t
      unfold qd1 at h0
      rw [hea t] at h0
      rw [add_zero]; exact sub_eq_zero.mp h0
    have he0 : e = fun _ _ => 0 := 𝔼.forward_unique hm hes (hz m)
      ⟨_, heb⟩ ⟨0, fun _ _ => by simp⟩
    intro t
    have := congrFun he0 t
    simp only [he, one_smul, zero_smul, add_zero] at this
    exact sub_eq_zero.mp this

/-! ### (3.16) ⟺ (3.17) -/

/-- Woodford (2003), (3.17) p. 360: `ξ₀ = ((1 − α)/α) · 1/(a − b)`. -/
noncomputable def xi0 (α a b : ℝ) : ℝ := (1 - α) / α * (1 / (a - b))

/-- Woodford (2003), (3.17) p. 360: `ξ₁ = μ₂⁻¹ ξ₀`. -/
noncomputable def xi1 (α a b μ₂ : ℝ) : ℝ := μ₂⁻¹ * xi0 α a b

/-- Woodford (2003), (3.17) p. 360: `ψ₁ = [a(β + μ₂⁻¹) − b(αβ + α⁻¹μ₂⁻¹)]/(a − b)`. -/
noncomputable def psi1 (α β a b μ₂ : ℝ) : ℝ :=
  (a * (β + μ₂⁻¹) - b * (α * β + α⁻¹ * μ₂⁻¹)) / (a - b)

/-- Woodford (2003), (3.17) p. 360: `ψ₂ = βμ₂⁻¹`. -/
noncomputable def psi2 (β μ₂ : ℝ) : ℝ := β * μ₂⁻¹

/-- Woodford (2003), (3.17) p. 360:
`π_t = ξ₀ŝ_t − ξ₁E_tŝ_{t+1} + ψ₁E_tπ_{t+1} − ψ₂E_tπ_{t+2}` at every date. -/
def Solves317 (ξ₀ ξ₁ ψ₁ ψ₂ : ℝ) (s infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = ξ₀ • s t - ξ₁ • 𝔼.E t (s (t + 1)) + ψ₁ • 𝔼.E t (infl (t + 1)) -
    ψ₂ • 𝔼.E t (infl (t + 2))

/-- Woodford (2003), (3.16)–(3.17) p. 360: with `π_t = ((1−α)/α) p̂*_t` (the Calvo relation),
(3.16) at every date is equivalent to (3.17) at every date, with the printed coefficients
(`a ≠ b`, `0 < α < 1`, `μ₂ ≠ 0`). -/
theorem eq316_iff_eq317 {α β a b μ₂ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hab : a - b ≠ 0)
    (hμ : μ₂ ≠ 0) {s infl pstar : ℕ → Ω → ℝ} (hπp : ∀ τ, infl τ = ((1 - α) / α) • pstar τ)
    (hsa : 𝔼.Adapted s) (hpa : 𝔼.Adapted pstar) :
    (∀ t, (a - b) • qd2 𝔼 (α * β) μ₂⁻¹ pstar t =
        qd1 𝔼 μ₂⁻¹ s t + (a * (α * β)) • qd1 𝔼 μ₂⁻¹ (fun τ => infl (τ + 1)) t -
          (b * μ₂⁻¹) • qd1 𝔼 (α * β) (fun τ => infl (τ + 1)) t) ↔
      Solves317 𝔼 (xi0 α a b) (xi1 α a b μ₂) (psi1 α β a b μ₂) (psi2 β μ₂) s infl := by
  have hinfl : infl = fun τ => ((1 - α) / α) • pstar τ := funext hπp
  subst hinfl
  have hκ : (1 - α) / α ≠ 0 := div_ne_zero (by linarith) hα0.ne'
  have hα : α ≠ 0 := hα0.ne'
  have key : ∀ P0 P1 P2 S0 S1 : ℝ,
      (1 - α) / α * P0 - (xi0 α a b * S0 - xi1 α a b μ₂ * S1 +
        psi1 α β a b μ₂ * ((1 - α) / α * P1) - psi2 β μ₂ * ((1 - α) / α * P2)) =
      ((1 - α) / α / (a - b)) * ((a - b) * (P0 - (α * β + μ₂⁻¹) * P1 + α * β * μ₂⁻¹ * P2) -
        (S0 - μ₂⁻¹ * S1 + a * (α * β) * ((1 - α) / α * P1 - μ₂⁻¹ * ((1 - α) / α * P2)) -
          b * μ₂⁻¹ * ((1 - α) / α * P1 - α * β * ((1 - α) / α * P2)))) := by
    intro P0 P1 P2 S0 S1
    unfold xi1 xi0 psi1 psi2
    field_simp
    ring
  have hfac : (1 - α) / α / (a - b) ≠ 0 := div_ne_zero hκ hab
  constructor
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [qd1, qd2, map_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hpa t, hsa t] at e ⊢
    have k := key (pstar t ω) (𝔼.E t (pstar (t + 1)) ω) (𝔼.E t (pstar (t + 2)) ω) (s t ω)
      (𝔼.E t (s (t + 1)) ω)
    rw [show t + 1 + 1 = t + 2 from rfl] at e ⊢
    have : (a - b) * (pstar t ω - (α * β + μ₂⁻¹) * 𝔼.E t (pstar (t + 1)) ω +
        α * β * μ₂⁻¹ * 𝔼.E t (pstar (t + 2)) ω) -
        (s t ω - μ₂⁻¹ * 𝔼.E t (s (t + 1)) ω + a * (α * β) * ((1 - α) / α *
          𝔼.E t (pstar (t + 1)) ω - μ₂⁻¹ * ((1 - α) / α * 𝔼.E t (pstar (t + 2)) ω)) -
          b * μ₂⁻¹ * ((1 - α) / α * 𝔼.E t (pstar (t + 1)) ω -
            α * β * ((1 - α) / α * 𝔼.E t (pstar (t + 2)) ω))) = 0 := by
      rw [sub_eq_zero]; linear_combination e
    rw [this, mul_zero, sub_eq_zero] at k
    linear_combination k
  · intro h t
    funext ω
    have e := congrFun (h t) ω
    simp only [qd1, qd2, map_smul, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, hpa t, hsa t] at e ⊢
    have k := key (pstar t ω) (𝔼.E t (pstar (t + 1)) ω) (𝔼.E t (pstar (t + 2)) ω) (s t ω)
      (𝔼.E t (s (t + 1)) ω)
    rw [show t + 1 + 1 = t + 2 from rfl] at ⊢
    have h0 : (1 - α) / α * pstar t ω - (xi0 α a b * s t ω - xi1 α a b μ₂ * 𝔼.E t (s (t + 1)) ω +
        psi1 α β a b μ₂ * ((1 - α) / α * 𝔼.E t (pstar (t + 1)) ω) -
        psi2 β μ₂ * ((1 - α) / α * 𝔼.E t (pstar (t + 2)) ω)) = 0 := by
      rw [sub_eq_zero]; linear_combination e
    rw [h0, eq_comm, mul_eq_zero] at k
    rcases k with k | k
    · exact absurd k hfac
    · linear_combination k

/-- Woodford (2003), (3.14), (3.16), (3.17) pp. 359–360: for bounded adapted `ŝ`, `p̂*` and
`π_t = ((1−α)/α)p̂*_t`, (3.14) at every date is equivalent to (3.17) at every date. -/
theorem eq314_iff_eq317 {α β a b μ₂ Bs Bp : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hab : a - b ≠ 0) (hμ : 1 < μ₂) {s infl pstar : ℕ → Ω → ℝ}
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (hsa : 𝔼.Adapted s) (hp : ∀ τ ω, |pstar τ ω| ≤ Bp)
    (hpa : 𝔼.Adapted pstar) (hπp : ∀ τ, infl τ = ((1 - α) / α) • pstar τ) :
    (∀ t, (a - b) • pstar t = rhs314 𝔼 a b (α * β) μ₂⁻¹ s infl t) ↔
      Solves317 𝔼 (xi0 α a b) (xi1 α a b μ₂) (psi1 α β a b μ₂) (psi2 β μ₂) s infl := by
  have hx : |α * β| < 1 := by rw [abs_of_pos (by positivity)]; nlinarith
  have hm : |μ₂⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ
  have hπ : ∀ τ ω, |infl τ ω| ≤ |(1 - α) / α| * Bp := fun τ ω => by
    rw [hπp τ, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hp τ ω) (abs_nonneg _)
  rw [eq314_iff_eq316 𝔼 hx hm hs hsa hπ hp hpa]
  exact eq316_iff_eq317 𝔼 hα0 hα1 hab (by linarith) hπp hsa hpa

/-! ### (3.19): solving the inflation equation forward -/

/-- Woodford (2003), (3.17) p. 360 with a general forcing term:
`π_t = g_t + ψ₁E_tπ_{t+1} − ψ₂E_tπ_{t+2}` at every date. -/
def Solves317g (ψ₁ ψ₂ : ℝ) (g infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = g t + ψ₁ • 𝔼.E t (infl (t + 1)) - ψ₂ • 𝔼.E t (infl (t + 2))

/-- Woodford (2003), (3.17) p. 360: the forcing term `g_t = ξ₀ŝ_t − ξ₁E_tŝ_{t+1}`. -/
def g317 (ξ₀ ξ₁ : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := ξ₀ • s t - ξ₁ • 𝔼.E t (s (t + 1))

/-- Woodford (2003), (3.17) p. 360: (3.17) is the general form with `g = ξ₀ŝ − ξ₁E ŝ_{+1}`. -/
theorem solves317_iff (ξ₀ ξ₁ ψ₁ ψ₂ : ℝ) (s infl : ℕ → Ω → ℝ) :
    Solves317 𝔼 ξ₀ ξ₁ ψ₁ ψ₂ s infl ↔ Solves317g 𝔼 ψ₁ ψ₂ (g317 𝔼 ξ₀ ξ₁ s) infl := Iff.rfl

/-- Woodford (2003), (3.17) p. 360: `g` is adapted and bounded when `ŝ` is. -/
theorem g317_adapted_bounded {ξ₀ ξ₁ Bs : ℝ} {s : ℕ → Ω → ℝ} (hs : ∀ τ ω, |s τ ω| ≤ Bs)
    (hsa : 𝔼.Adapted s) :
    𝔼.Adapted (g317 𝔼 ξ₀ ξ₁ s) ∧ ∀ t ω, |g317 𝔼 ξ₀ ξ₁ s t ω| ≤ |ξ₀| * Bs + |ξ₁| * Bs := by
  refine ⟨fun t => ?_, fun t ω => ?_⟩
  · unfold g317; rw [map_sub, map_smul, map_smul, hsa t, 𝔼.E_E_self]
  · unfold g317
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hs t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + 1)) t ω) (abs_nonneg _)

/-- Woodford (2003), fn. 31 p. 361 (the root condition): under Schur–Cohn the Cayley–Hamilton
sequence `c_n` of `z² − ψ₁z + ψ₂` satisfies `|c_n| ≤ (n + 1)ρⁿ` with `ρ < 1`. -/
theorem chSeq_bound {ψ₁ ψ₂ : ℝ} (h : SchurStable ψ₁ ψ₂) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n, |chSeq ψ₁ ψ₂ n| ≤ (n + 1) * ρ ^ n := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots ψ₁ ψ₂).mp h
  exact ⟨_, le_max_of_le_left (norm_nonneg _), max_lt h1 h2, abs_chSeq_le ψ₁ ψ₂⟩

/-- Woodford (2003), (3.19) p. 362: `∑ (n + 1)ρⁿ` converges for `0 ≤ ρ < 1`. -/
theorem summable_succ_mul_geom {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) * ρ ^ n := by
  have hρ : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have := (summable_pow_mul_geometric_of_norm_lt_one 1 hρ).add
    (summable_geometric_of_lt_one h0 h1)
  refine this.congr fun n => ?_
  simp only [pow_one]; ring

/-- Woodford (2003), (3.19) p. 362: `∑ c_n G_n` converges for bounded `G` under Schur–Cohn. -/
theorem summable_chSeq_mul {ψ₁ ψ₂ B : ℝ} (h : SchurStable ψ₁ ψ₂) {G : ℕ → ℝ}
    (hG : ∀ n, |G n| ≤ B) : Summable fun n => chSeq ψ₁ ψ₂ n * G n := by
  obtain ⟨ρ, h0, h1, hc⟩ := chSeq_bound h
  refine Summable.of_norm_bounded ((summable_succ_mul_geom h0 h1).mul_right B) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hc n) (hG n) (abs_nonneg _) (by positivity)

/-- Woodford (2003), (3.19) p. 362 (the forward-solution identity): with `c_0 = 1`, `c_1 = ψ₁`,
`c_{n+2} = ψ₁c_{n+1} − ψ₂c_n`, `∑ c_n G_n = G_0 + ψ₁ ∑ c_n G_{n+1} − ψ₂ ∑ c_n G_{n+2}`. -/
theorem chSeq_shift {ψ₁ ψ₂ B : ℝ} (h : SchurStable ψ₁ ψ₂) {G : ℕ → ℝ}
    (hG : ∀ n, |G n| ≤ B) :
    ∑' n, chSeq ψ₁ ψ₂ n * G n =
      G 0 + ψ₁ * ∑' n, chSeq ψ₁ ψ₂ n * G (n + 1) - ψ₂ * ∑' n, chSeq ψ₁ ψ₂ n * G (n + 2) := by
  have S0 := summable_chSeq_mul h hG
  have S1 := summable_chSeq_mul h (G := fun n => G (n + 1)) (fun n => hG _)
  have S2 := summable_chSeq_mul h (G := fun n => G (n + 2)) (fun n => hG _)
  have S1' : Summable fun n => chSeq ψ₁ ψ₂ (n + 1) * G (n + 2) := (summable_nat_add_iff 1).mpr S1
  have S0' : Summable fun n => chSeq ψ₁ ψ₂ (n + 1) * G (n + 1) := (summable_nat_add_iff 1).mpr S0
  have e0 : ∑' n, chSeq ψ₁ ψ₂ n * G n =
      G 0 + ψ₁ * G 1 + ∑' n, chSeq ψ₁ ψ₂ (n + 2) * G (n + 2) := by
    rw [S0.tsum_eq_zero_add, S0'.tsum_eq_zero_add]
    simp only [chSeq, one_mul, zero_add]
    ring
  have e1 : ∑' n, chSeq ψ₁ ψ₂ n * G (n + 1) =
      G 1 + ∑' n, chSeq ψ₁ ψ₂ (n + 1) * G (n + 2) := by
    rw [S1.tsum_eq_zero_add]; simp [chSeq]
  have e2 : ∑' n, chSeq ψ₁ ψ₂ (n + 2) * G (n + 2) =
      ψ₁ * ∑' n, chSeq ψ₁ ψ₂ (n + 1) * G (n + 2) - ψ₂ * ∑' n, chSeq ψ₁ ψ₂ n * G (n + 2) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (S1'.mul_left _).tsum_sub (S2.mul_left _)]
    refine tsum_congr fun n => ?_
    simp only [chSeq]; ring
  rw [e0, e1, e2]; ring

/-- Woodford (2003), (3.19) p. 362: the forward solution `π_t = ∑_n c_n E_t g_{t+n}`. -/
noncomputable def sol317 (ψ₁ ψ₂ : ℝ) (g : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' n, chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + n)) ω

/-- Woodford (2003), (3.19) p. 362: `E_t` passes through the forward solution. -/
theorem E_sol317 {ψ₁ ψ₂ Bg : ℝ} (h : SchurStable ψ₁ ψ₂) {g : ℕ → Ω → ℝ}
    (hg : ∀ τ ω, |g τ ω| ≤ Bg) (t k : ℕ) (ω : Ω) :
    𝔼.E t (sol317 𝔼 ψ₁ ψ₂ g (t + k)) ω = ∑' n, chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + k + n)) ω := by
  obtain ⟨ρ, h0, h1, hc⟩ := chSeq_bound h
  set f : ℕ → Ω → ℝ := fun n => chSeq ψ₁ ψ₂ n • 𝔼.E (t + k) (g (t + k + n)) with hf
  have hsol : sol317 𝔼 ψ₁ ψ₂ g (t + k) = fun ω' => ∑' n, f n ω' := by
    funext ω'; simp only [sol317, hf, Pi.smul_apply, smul_eq_mul]
  have hb : ∀ n ω', |f n ω'| ≤ ((n : ℝ) + 1) * ρ ^ n * Bg := by
    intro n ω'
    simp only [hf, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul (hc n) (𝔼.abs_E_le (hg _) _ ω') (abs_nonneg _) (by positivity)
  rw [hsol, ForwardSolution.E_tsum_dom 𝔼 ((summable_succ_mul_geom h0 h1).mul_right Bg) hb]
  refine tsum_congr fun n => ?_
  simp only [hf, map_smul, 𝔼.tower (Nat.le_add_right t k), Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), (3.19) p. 362: the forward solution is adapted and bounded. -/
theorem sol317_adapted_bounded {ψ₁ ψ₂ Bg : ℝ} (h : SchurStable ψ₁ ψ₂) {g : ℕ → Ω → ℝ}
    (hg : ∀ τ ω, |g τ ω| ≤ Bg) : 𝔼.Adapted (sol317 𝔼 ψ₁ ψ₂ g) ∧ BoundedProc (sol317 𝔼 ψ₁ ψ₂ g) := by
  obtain ⟨ρ, h0, h1, hc⟩ := chSeq_bound h
  refine ⟨fun t => ?_, ⟨∑' n : ℕ, ((n : ℝ) + 1) * ρ ^ n * Bg, fun t ω => ?_⟩⟩
  · funext ω
    have := E_sol317 𝔼 h hg t 0 ω
    simp only [add_zero] at this
    rw [this]
    rfl
  · have hs : Summable fun n : ℕ => ((n : ℝ) + 1) * ρ ^ n * Bg :=
      (summable_succ_mul_geom h0 h1).mul_right Bg
    have hb : ∀ n, |chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + n)) ω| ≤ ((n : ℝ) + 1) * ρ ^ n * Bg := by
      intro n; rw [abs_mul]
      exact mul_le_mul (hc n) (𝔼.abs_E_le (hg _) _ ω) (abs_nonneg _) (by positivity)
    have hs' : Summable fun n => chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + n)) ω :=
      Summable.of_norm_bounded hs fun n => by rw [Real.norm_eq_abs]; exact hb n
    unfold sol317
    have hn := norm_tsum_le_tsum_norm hs'.norm
    rw [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    exact Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hb n) hs'.norm hs

/-- Woodford (2003), (3.19) p. 362 (existence): under the root condition (Schur–Cohn for
`z² − ψ₁z + ψ₂`), the forward solution solves (3.17) for bounded adapted forcing. -/
theorem sol317_solves {ψ₁ ψ₂ Bg : ℝ} (h : SchurStable ψ₁ ψ₂) {g : ℕ → Ω → ℝ}
    (hg : ∀ τ ω, |g τ ω| ≤ Bg) (hga : 𝔼.Adapted g) :
    Solves317g 𝔼 ψ₁ ψ₂ g (sol317 𝔼 ψ₁ ψ₂ g) := by
  intro t
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [E_sol317 𝔼 h hg t 1 ω, E_sol317 𝔼 h hg t 2 ω]
  change ∑' n, chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + n)) ω = _
  rw [chSeq_shift h (G := fun n => 𝔼.E t (g (t + n)) ω) (fun n => 𝔼.abs_E_le (hg _) t ω)]
  simp only [add_zero, hga t]
  have q1 : ∑' n, chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + (n + 1))) ω =
      ∑' n, chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + 1 + n)) ω :=
    tsum_congr fun n => by rw [show t + (n + 1) = t + 1 + n by omega]
  have q2 : ∑' n, chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + (n + 2))) ω =
      ∑' n, chSeq ψ₁ ψ₂ n * 𝔼.E t (g (t + 2 + n)) ω :=
    tsum_congr fun n => by rw [show t + (n + 2) = t + 2 + n by omega]
  rw [q1, q2]

/-- Woodford (2003), (3.19) p. 362 and fn. 31 (uniqueness): under the root condition, (3.17)
has at most one bounded adapted solution (Blanchard–Kahn for the companion matrix
`[[ψ₁, −ψ₂], [1, 0]]`, via `ExpectationSystem.system_unique`). -/
theorem unique317 {ψ₁ ψ₂ : ℝ} (h : SchurStable ψ₁ ψ₂) {g π₁ π₂ : ℕ → Ω → ℝ}
    (h1 : Solves317g 𝔼 ψ₁ ψ₂ g π₁) (h2 : Solves317g 𝔼 ψ₁ ψ₂ g π₂)
    (ha1 : 𝔼.Adapted π₁) (ha2 : 𝔼.Adapted π₂) (hb1 : BoundedProc π₁) (hb2 : BoundedProc π₂) :
    π₁ = π₂ := by
  set A : Matrix (Fin 2) (Fin 2) ℝ := !![ψ₁, -ψ₂; 1, 0] with hA
  have hAs : SchurStable (tr2 A) (det2 A) := by
    simpa [hA, tr2, det2] using h
  have hvec : ∀ π : ℕ → Ω → ℝ, Solves317g 𝔼 ψ₁ ψ₂ g π → 𝔼.Adapted π → BoundedProc π →
      𝔼.Solves A (fun t => ![g t, 0]) (fun t => ![π t, 𝔼.E t (π (t + 1))]) ∧
      𝔼.AdaptedVec (fun t => ![π t, 𝔼.E t (π (t + 1))]) ∧
      BoundedVec (fun t => ![π t, 𝔼.E t (π (t + 1))]) := by
    intro π hs ha hb
    obtain ⟨Bπ, hBπ⟩ := hb
    refine ⟨fun t i => ?_, fun t i => ?_, ⟨Bπ, fun t i ω => ?_⟩⟩
    · fin_cases i
      · simp only [hA, Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
          Matrix.empty_val']
        rw [𝔼.tower (Nat.le_succ t), show t + 1 + 1 = t + 2 from rfl, neg_smul]
        conv_lhs => rw [hs t]
        abel
      · simp [hA]
    · fin_cases i
      · simp [ha t]
      · simp [𝔼.E_E_self]
    · fin_cases i
      · simpa using hBπ t ω
      · simpa using 𝔼.abs_E_le (hBπ (t + 1)) t ω
  obtain ⟨s1, a1, b1⟩ := hvec π₁ h1 ha1 hb1
  obtain ⟨s2, a2, b2⟩ := hvec π₂ h2 ha2 hb2
  have := 𝔼.system_unique hAs s1 s2 a1 a2 b1 b2
  funext t
  simpa using congrFun (congrFun this t) 0

/-- Woodford (2003), (3.19) p. 362: under the root condition, every bounded adapted solution of
(3.17) is the forward solution `π_t = ∑ c_n E_t g_{t+n}`. -/
theorem eq_sol317 {ψ₁ ψ₂ Bg : ℝ} (h : SchurStable ψ₁ ψ₂) {g infl : ℕ → Ω → ℝ}
    (hg : ∀ τ ω, |g τ ω| ≤ Bg) (hga : 𝔼.Adapted g) (hs : Solves317g 𝔼 ψ₁ ψ₂ g infl)
    (ha : 𝔼.Adapted infl) (hb : BoundedProc infl) : infl = sol317 𝔼 ψ₁ ψ₂ g := by
  obtain ⟨a2, b2⟩ := sol317_adapted_bounded 𝔼 h hg
  exact unique317 𝔼 h hs (sol317_solves 𝔼 h hg hga) ha a2 hb b2

/-- Woodford (2003), (3.19) p. 362: the coefficients `Ψ_j` of `π_t = ∑ Ψ_j E_t ŝ_{t+j}`:
`Ψ_0 = ξ₀`, `Ψ_{j+1} = ξ₀c_{j+1} − ξ₁c_j`. -/
def Psi319 (ξ₀ ξ₁ ψ₁ ψ₂ : ℝ) : ℕ → ℝ
  | 0 => ξ₀
  | j + 1 => ξ₀ * chSeq ψ₁ ψ₂ (j + 1) - ξ₁ * chSeq ψ₁ ψ₂ j

/-- Woodford (2003), (3.19) p. 362: the forward solution of (3.17) is
`π_t = ∑_j Ψ_j E_t ŝ_{t+j}`, the series converging. -/
theorem sol317_eq_Psi {ξ₀ ξ₁ ψ₁ ψ₂ Bs : ℝ} (h : SchurStable ψ₁ ψ₂) {s : ℕ → Ω → ℝ}
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (t : ℕ) (ω : Ω) :
    sol317 𝔼 ψ₁ ψ₂ (g317 𝔼 ξ₀ ξ₁ s) t ω = ∑' j, Psi319 ξ₀ ξ₁ ψ₁ ψ₂ j * 𝔼.E t (s (t + j)) ω := by
  set S : ℕ → ℝ := fun n => 𝔼.E t (s (t + n)) ω with hS
  have hSb : ∀ n, |S n| ≤ Bs := fun n => 𝔼.abs_E_le (hs _) t ω
  have hS0 := summable_chSeq_mul h hSb
  have hS1 := summable_chSeq_mul h (G := fun n => S (n + 1)) (fun n => hSb _)
  have hS0' : Summable fun n => chSeq ψ₁ ψ₂ (n + 1) * S (n + 1) := (summable_nat_add_iff 1).mpr hS0
  have hP : Summable fun j => Psi319 ξ₀ ξ₁ ψ₁ ψ₂ (j + 1) * S (j + 1) := by
    refine ((hS0'.mul_left ξ₀).sub (hS1.mul_left ξ₁)).congr fun n => ?_
    simp only [Psi319]; ring
  have hP' : Summable fun j => Psi319 ξ₀ ξ₁ ψ₁ ψ₂ j * S j := (summable_nat_add_iff 1).mp hP
  have e1 : sol317 𝔼 ψ₁ ψ₂ (g317 𝔼 ξ₀ ξ₁ s) t ω =
      ξ₀ * ∑' n, chSeq ψ₁ ψ₂ n * S n - ξ₁ * ∑' n, chSeq ψ₁ ψ₂ n * S (n + 1) := by
    unfold sol317 g317
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hS0.mul_left _).tsum_sub (hS1.mul_left _)]
    refine tsum_congr fun n => ?_
    simp only [hS, map_sub, map_smul, 𝔼.tower (Nat.le_add_right t n), Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, add_assoc]
    ring
  have eP : ∑' j, Psi319 ξ₀ ξ₁ ψ₁ ψ₂ (j + 1) * S (j + 1) =
      ξ₀ * ∑' j, chSeq ψ₁ ψ₂ (j + 1) * S (j + 1) - ξ₁ * ∑' j, chSeq ψ₁ ψ₂ j * S (j + 1) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hS0'.mul_left _).tsum_sub (hS1.mul_left _)]
    refine tsum_congr fun n => ?_
    simp only [Psi319]; ring
  change _ = ∑' j, Psi319 ξ₀ ξ₁ ψ₁ ψ₂ j * S j
  rw [e1, hP'.tsum_eq_zero_add, hS0.tsum_eq_zero_add, eP]
  simp only [Psi319, chSeq]
  ring

/-- Woodford (2003), fn. 31 p. 361 (the root condition is also necessary): (3.17) has at most one
bounded adapted solution for every bounded adapted forcing iff both roots of `z² − ψ₁z + ψ₂` lie
inside the unit circle. -/
theorem determinate317_iff [Nonempty Ω] (ψ₁ ψ₂ : ℝ) :
    (∀ g π₁ π₂ : ℕ → Ω → ℝ, 𝔼.Adapted g → BoundedProc g → Solves317g 𝔼 ψ₁ ψ₂ g π₁ →
      Solves317g 𝔼 ψ₁ ψ₂ g π₂ → 𝔼.Adapted π₁ → 𝔼.Adapted π₂ → BoundedProc π₁ →
        BoundedProc π₂ → π₁ = π₂) ↔ SchurStable ψ₁ ψ₂ := by
  constructor
  · intro hdet
    by_contra hns
    set A : Matrix (Fin 2) (Fin 2) ℝ := !![ψ₁, -ψ₂; 1, 0] with hA
    have hAs : ¬ SchurStable (tr2 A) (det2 A) := by simpa [hA, tr2, det2] using hns
    obtain ⟨x, hx, ⟨Bx, hBx⟩, hx0⟩ := exists_bounded_homogeneous hAs
    have hrow : ∀ t, x t 0 = ψ₁ * x (t + 1) 0 - ψ₂ * x (t + 1) 1 ∧ x t 1 = x (t + 1) 0 := by
      intro t
      have h0 := congrFun (hx t) 0
      have h1 := congrFun (hx t) 1
      simp [hA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
      constructor <;> linarith
    have hsol1 : Solves317g 𝔼 ψ₁ ψ₂ (fun _ _ => 0) (fun t _ => x t 0) := by
      intro t; funext ω
      simp only [𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_add]
      rw [(hrow t).1, (hrow (t + 1)).2]
    have hsol2 : Solves317g 𝔼 ψ₁ ψ₂ (fun _ _ => 0) (fun _ _ => 0) := by
      intro t; funext ω
      simp only [𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have key := hdet (fun _ _ => 0) (fun t _ => x t 0) (fun _ _ => 0)
      (fun t => 𝔼.const t 0) ⟨0, fun _ _ => by simp⟩ hsol1 hsol2
      (fun t => 𝔼.const t _) (fun t => 𝔼.const t 0) ⟨Bx, fun t _ => hBx t 0⟩
      ⟨0, fun _ _ => by simp⟩
    apply hx0
    funext t i
    have h0 : ∀ t, x t 0 = 0 := fun t => by
      have := congrFun (congrFun key t) (Classical.arbitrary Ω)
      simpa using this
    fin_cases i
    · simpa using h0 t
    · simp [(hrow t).2, h0 (t + 1)]
  · intro h g π₁ π₂ _ _ h1 h2 a1 a2 b1 b2
    exact unique317 𝔼 h h1 h2 a1 a2 b1 b2

/-! ### The basic model and the limiting inflation equation -/

/-- Woodford (2003), (3.19) p. 362 and fn. 32 (the basic model, restated from Ch. 3 (2.13)): for
`|β| < 1` and bounded adapted `ŝ`, a bounded `π` solves `π_t = ξŝ_t + βE_tπ_{t+1}` iff
`π_t = ∑_j ξβʲ E_t ŝ_{t+j}`, i.e. (3.19) with `Ψ_j = ξβʲ` (and this solution exists:
`ForwardSolution.existsUnique_bounded`). -/
theorem basic_eq319 {β ξ Bs : ℝ} (hβ : |β| < 1) {s infl : ℕ → Ω → ℝ}
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (hsa : 𝔼.Adapted s) (hb : BoundedProc infl) :
    ForwardSolution.Solves 𝔼 β (fun τ => ξ • s τ) infl ↔
      ∀ t ω, infl t ω = ∑' j, ξ * β ^ j * 𝔼.E t (s (t + j)) ω := by
  have hu : ∀ τ ω, |(fun τ => ξ • s τ) τ ω| ≤ |ξ| * Bs := fun τ ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hs τ ω) (abs_nonneg _)
  have hua : 𝔼.Adapted (fun τ => ξ • s τ) := fun τ => by simp only [map_smul, hsa τ]
  rw [ForwardSolution.solves_iff_forwardSeries 𝔼 hβ hu hua hb]
  have e : ∀ t, 𝔼.forwardSeries β (fun τ => ξ • s τ) t =
      fun ω => ∑' j, ξ * β ^ j * 𝔼.E t (s (t + j)) ω := by
    intro t; funext ω
    unfold ExpectationSystem.forwardSeries
    refine tsum_congr fun j => ?_
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]; ring
  simp only [e, funext_iff]

/-- Woodford (2003), p. 363: in the limit the root condition holds, `SchurStable (2β) (β²)`. -/
theorem schurStable_limit {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) : SchurStable (2 * β) (β ^ 2) := by
  refine ⟨by rw [abs_of_pos (by positivity)]; nlinarith, ?_⟩
  rw [abs_of_pos (by positivity)]; nlinarith [sq_pos_of_pos (sub_pos.mpr hβ1)]

/-- Woodford (2003), p. 364: the Cayley–Hamilton sequence of `z² − 2βz + β²` is `(j + 1)βʲ`. -/
theorem chSeq_limit (β : ℝ) (j : ℕ) : chSeq (2 * β) (β ^ 2) j = (j + 1) * β ^ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp [chSeq]
    | 1, _ => simp only [chSeq]; push_cast; ring
    | k + 2, ih =>
      simp only [chSeq]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      push_cast; ring

/-- Woodford (2003), p. 364: "(3.19) holds with coefficients `Ψ_j = ξβʲ`" in the limit
(`ξ₀ = ξ`, `ξ₁ = βξ`, `ψ₁ = 2β`, `ψ₂ = β²`). -/
theorem Psi_limit (ξ β : ℝ) (j : ℕ) : Psi319 ξ (β * ξ) (2 * β) (β ^ 2) j = ξ * β ^ j := by
  cases j with
  | zero => simp [Psi319]
  | succ j => simp only [Psi319, chSeq_limit]; push_cast; ring

/-- Woodford (2003), pp. 363–364: the limiting form of (3.17),
`E_t(1 − βL⁻¹)π_t = ξE_t(1 − βL⁻¹)ŝ_t + βE_t(1 − βL⁻¹)π_{t+1}`, "has the same bounded solutions
as the simpler relation `π_t = ξŝ_t + βE_tπ_{t+1}`" (for bounded adapted `π`, `ŝ`, `|β| < 1`). -/
theorem limit_relation_iff {β ξ : ℝ} (hβ : |β| < 1) {s infl : ℕ → Ω → ℝ}
    (hsa : 𝔼.Adapted s) (hs : BoundedProc s) (hπa : 𝔼.Adapted infl) (hπ : BoundedProc infl) :
    Solves317 𝔼 ξ (β * ξ) (2 * β) (β ^ 2) s infl ↔
      ∀ t, infl t = ξ • s t + β • 𝔼.E t (infl (t + 1)) := by
  constructor
  · intro h
    set u : ℕ → Ω → ℝ := fun t => infl t - ξ • s t - β • 𝔼.E t (infl (t + 1)) with hu
    have hua : 𝔼.Adapted u := fun t => by
      simp only [hu, map_sub, map_smul, hπa t, hsa t, 𝔼.E_E_self]
    have hus : ∀ t, u t = β • 𝔼.E t (u (t + 1)) + 0 := by
      intro t
      funext ω
      have e := congrFun (h t) ω
      simp only [hu, map_sub, map_smul, 𝔼.tower (Nat.le_succ t),
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
      rw [show t + 1 + 1 = t + 2 from rfl]
      linear_combination e
    obtain ⟨Bs, hBs⟩ := hs
    obtain ⟨Bπ, hBπ⟩ := hπ
    have hub : BoundedProc u := ⟨Bπ + |ξ| * Bs + |β| * Bπ, fun t ω => by
      simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have h1 : |ξ * s t ω| ≤ |ξ| * Bs := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hBs t ω) (abs_nonneg _)
      have h2 : |β * 𝔼.E t (infl (t + 1)) ω| ≤ |β| * Bπ := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hBπ _) t ω) (abs_nonneg _)
      calc _ ≤ |infl t ω - ξ * s t ω| + |β * 𝔼.E t (infl (t + 1)) ω| := abs_sub _ _
        _ ≤ |infl t ω| + |ξ * s t ω| + |β * 𝔼.E t (infl (t + 1)) ω| := by
          gcongr; exact abs_sub _ _
        _ ≤ _ := by linarith [hBπ t ω]⟩
    have hz : ∀ t, (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) t =
        β • 𝔼.E t ((fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) (t + 1)) + 0 := by
      intro t
      have : (fun _ : Ω => (0 : ℝ)) = 0 := rfl
      simp only [this, map_zero, smul_zero, add_zero]
    have hu0 := 𝔼.forward_unique hβ hus hz hub ⟨0, fun _ _ => by simp⟩
    intro t
    have := congrFun hu0 t
    simp only [hu] at this
    funext ω
    have e := congrFun this ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith
  · intro h t
    funext ω
    have e0 := congrFun (h t) ω
    have e1 := congrFun (congrArg (𝔼.E t) (h (t + 1))) ω
    simp only [map_add, map_smul, 𝔼.tower (Nat.le_succ t), Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul] at e0 e1 ⊢
    rw [show t + 1 + 1 = t + 2 from rfl] at e1
    linear_combination e0 - β * e1

/-! ### The limit `ε_ψ → ∞` -/

/-- Woodford (2003), p. 363: `c = [1−β(1−δ)]ρ_k/ε_ψ → 0` as `ε_ψ → ∞`. -/
theorem tendsto_cD (P : Params) : Tendsto (fun ε => cD P ε) atTop (𝓝 0) := by
  unfold cD; exact tendsto_const_nhds.div_atTop tendsto_id

/-- Woodford (2003), p. 363: `M → 0` as `ε_ψ → ∞`. -/
theorem tendsto_MD (P : Params) : Tendsto (fun ε => MD P ε) atTop (𝓝 0) := by
  unfold MD; exact tendsto_const_nhds.div_atTop tendsto_id

/-- Woodford (2003), (D.3) p. 689: at `c = 0`, `√disc = 1 − β`. -/
theorem sqrt_discr_zero {β : ℝ} (hβ1 : β < 1) : √(discr β 0) = 1 - β := by
  rw [show discr β 0 = (1 - β) ^ 2 by unfold discr; ring, Real.sqrt_sq (by linarith)]

/-- Woodford (2003), p. 363: "as `ε_ψ` is made large … `μ₁ → 1`". -/
theorem tendsto_mu1 (hP : Admissible P) :
    Tendsto (fun ε => mu1 P.β (cD P ε)) atTop (𝓝 1) := by
  have hc : Continuous (fun c => mu1 P.β c) := by unfold mu1 discr; fun_prop
  have h0 : mu1 P.β 0 = 1 := by
    have := hP.hβ0
    unfold mu1; rw [sqrt_discr_zero hP.hβ1]; field_simp; ring
  have := (hc.tendsto 0).comp (tendsto_cD P)
  rwa [h0] at this

/-- Woodford (2003), p. 363: "as `ε_ψ` is made large … `μ₂ → β⁻¹`". -/
theorem tendsto_mu2 (hP : Admissible P) :
    Tendsto (fun ε => mu2 P.β (cD P ε)) atTop (𝓝 P.β⁻¹) := by
  have hc : Continuous (fun c => mu2 P.β c) := by unfold mu2 discr; fun_prop
  have h0 : mu2 P.β 0 = P.β⁻¹ := by
    have := hP.hβ0
    unfold mu2; rw [sqrt_discr_zero hP.hβ1]; field_simp; ring
  have := (hc.tendsto 0).comp (tendsto_cD P)
  rwa [h0] at this

/-- Woodford (2003), p. 363: `a → (1 + ωθ)/(1 − αβ)` as `ε_ψ → ∞`. -/
theorem tendsto_aM (hP : Admissible P) :
    Tendsto (fun ε => aM P ε) atTop (𝓝 ((1 + P.ω * P.θ) / (1 - P.α * P.β))) := by
  have hα1 := hP.hα1; have hβ0 := hP.hβ0; have hβ1 := hP.hβ1; have hα0 := hP.hα0
  have hne : (1 - P.α * P.β * 1) * (1 - P.α * P.β * P.β⁻¹) ≠ 0 := by
    rw [mul_one, mul_assoc, mul_inv_cancel₀ hβ0.ne', mul_one]
    exact mul_ne_zero (by nlinarith) (by linarith)
  have h := (tendsto_const_nhds (x := (1 + P.ω * P.θ) / (1 - P.α * P.β))).add
    ((tendsto_const_nhds (x := (P.ω - P.ν) * (P.α / (1 - P.α * P.β)))).mul
      ((tendsto_MD P).div ((tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_mu1 hP))).mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_mu2 hP)))) hne))
  simp only [mul_zero, zero_div, add_zero] at h
  exact h

/-- Woodford (2003), p. 363: `b → 0` as `ε_ψ → ∞`. -/
theorem tendsto_bM (hP : Admissible P) : Tendsto (fun ε => bM P ε) atTop (𝓝 0) := by
  have hα1 := hP.hα1; have hβ0 := hP.hβ0; have hβ1 := hP.hβ1; have hα0 := hP.hα0
  have hne : (1 - P.α * P.β * 1) * (1 - P.α * P.β * P.β⁻¹) ≠ 0 := by
    rw [mul_one, mul_assoc, mul_inv_cancel₀ hβ0.ne', mul_one]
    exact mul_ne_zero (by nlinarith) (by linarith)
  have hinv := (tendsto_mu2 hP).inv₀ (inv_ne_zero hβ0.ne')
  rw [inv_inv] at hinv
  have h := ((tendsto_const_nhds (x := P.ω - P.ν)).mul
      ((tendsto_const_nhds (x := P.α)).div (tendsto_const_nhds.sub hinv)
        (by linarith : (1 : ℝ) - P.β ≠ 0))).mul
      ((tendsto_MD P).div ((tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_mu1 hP))).mul
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul (tendsto_mu2 hP)))) hne)
  simp only [mul_zero, zero_div] at h
  exact h

variable (P) in
/-- Woodford (2003), (3.17) p. 360: `ξ₀` of the investment model at adjustment cost `ε_ψ`. -/
noncomputable def xi0M (ε : ℝ) : ℝ := xi0 P.α (aM P ε) (bM P ε)

variable (P) in
/-- Woodford (2003), (3.17) p. 360: `ξ₁` of the investment model. -/
noncomputable def xi1M (ε : ℝ) : ℝ := xi1 P.α (aM P ε) (bM P ε) (mu2 P.β (cD P ε))

variable (P) in
/-- Woodford (2003), (3.17) p. 360: `ψ₁` of the investment model. -/
noncomputable def psi1M (ε : ℝ) : ℝ := psi1 P.α P.β (aM P ε) (bM P ε) (mu2 P.β (cD P ε))

variable (P) in
/-- Woodford (2003), (3.17) p. 360: `ψ₂` of the investment model. -/
noncomputable def psi2M (ε : ℝ) : ℝ := psi2 P.β (mu2 P.β (cD P ε))

variable (P) in
/-- Woodford (2003), p. 363: the basic model's `ξ = ((1 − α)/α)(1 − αβ)/(1 + ωθ)`. -/
noncomputable def xiBasic : ℝ := (1 - P.α) / P.α * ((1 - P.α * P.β) / (1 + P.ω * P.θ))

/-- Woodford (2003), p. 363: `a − b → (1 + ωθ)/(1 − αβ) ≠ 0`. -/
theorem tendsto_aM_sub_bM (hP : Admissible P) :
    Tendsto (fun ε => aM P ε - bM P ε) atTop (𝓝 ((1 + P.ω * P.θ) / (1 - P.α * P.β))) := by
  simpa using (tendsto_aM hP).sub (tendsto_bM hP)

/-- Woodford (2003), p. 363: `1 + ωθ > 0` and `1 − αβ > 0`. -/
theorem limit_pos (hP : Admissible P) : 0 < (1 + P.ω * P.θ) / (1 - P.α * P.β) := by
  have := hP.hθ; have : 0 < P.ω := by linarith [hP.hν, hP.hων]
  have : P.α * P.β < 1 := by nlinarith [hP.hα0, hP.hα1, hP.hβ0, hP.hβ1]
  apply div_pos (by positivity) (by linarith)

/-- Woodford (2003), p. 363: `ξ₀ → ξ` as `ε_ψ → ∞`. -/
theorem tendsto_xi0M (hP : Admissible P) : Tendsto (fun ε => xi0M P ε) atTop (𝓝 (xiBasic P)) := by
  have hL := limit_pos hP
  have h := (tendsto_const_nhds (x := (1 - P.α) / P.α)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).div (tendsto_aM_sub_bM hP) hL.ne')
  have hv : (1 - P.α) / P.α * (1 / ((1 + P.ω * P.θ) / (1 - P.α * P.β))) = xiBasic P := by
    unfold xiBasic; rw [one_div_div]
  rw [hv] at h
  exact h

/-- Woodford (2003), p. 363: `ξ₁ → βξ` as `ε_ψ → ∞`. -/
theorem tendsto_xi1M (hP : Admissible P) :
    Tendsto (fun ε => xi1M P ε) atTop (𝓝 (P.β * xiBasic P)) := by
  have hinv := (tendsto_mu2 hP).inv₀ (inv_ne_zero hP.hβ0.ne')
  rw [inv_inv] at hinv
  exact hinv.mul (tendsto_xi0M hP)

/-- Woodford (2003), p. 363: `ψ₁ → 2β` as `ε_ψ → ∞`. -/
theorem tendsto_psi1M (hP : Admissible P) : Tendsto (fun ε => psi1M P ε) atTop (𝓝 (2 * P.β)) := by
  have hL := limit_pos hP
  have hinv := (tendsto_mu2 hP).inv₀ (inv_ne_zero hP.hβ0.ne')
  rw [inv_inv] at hinv
  have h := (((tendsto_aM hP).mul ((tendsto_const_nhds (x := P.β)).add hinv)).sub
    ((tendsto_bM hP).mul ((tendsto_const_nhds (x := P.α * P.β)).add
      ((tendsto_const_nhds (x := P.α⁻¹)).mul hinv)))).div
      (tendsto_aM_sub_bM hP) hL.ne'
  have hv : ((1 + P.ω * P.θ) / (1 - P.α * P.β) * (P.β + P.β) -
      0 * (P.α * P.β + P.α⁻¹ * P.β)) / ((1 + P.ω * P.θ) / (1 - P.α * P.β)) = 2 * P.β := by
    have h1 : 1 - P.α * P.β ≠ 0 := by nlinarith [hP.hα0, hP.hα1, hP.hβ0, hP.hβ1]
    have h2 : 1 + P.ω * P.θ ≠ 0 := by
      have := hP.hθ; have : 0 < P.ω := by linarith [hP.hν, hP.hων]
      positivity
    field_simp; ring
  rw [hv] at h
  exact h

/-- Woodford (2003), p. 363: `ψ₂ → β²` as `ε_ψ → ∞`. -/
theorem tendsto_psi2M (hP : Admissible P) : Tendsto (fun ε => psi2M P ε) atTop (𝓝 (P.β ^ 2)) := by
  have hinv := (tendsto_mu2 hP).inv₀ (inv_ne_zero hP.hβ0.ne')
  rw [inv_inv] at hinv
  have h := (tendsto_const_nhds (x := P.β)).mul hinv
  rw [← sq] at h
  exact h

/-- Woodford (2003), p. 363 with Prop. 5.1 corrected: for all sufficiently large `ε_ψ`,
`αβμ₂ < 1`, hence `a > 0` and `b > 0` (since `αβμ₂ → α < 1`). -/
theorem eventually_ab_pos (hP : Admissible P) :
    ∀ᶠ ε in atTop, P.α * P.β * mu2 P.β (cD P ε) < 1 ∧ 0 < aM P ε ∧ 0 < bM P ε := by
  have h := (tendsto_const_nhds (x := P.α * P.β)).mul (tendsto_mu2 hP)
  have hv : P.α * P.β * P.β⁻¹ = P.α := by field_simp [hP.hβ0.ne']
  rw [hv] at h
  filter_upwards [h.eventually_lt_const hP.hα1, eventually_gt_atTop 0] with ε h1 h2
  exact ⟨h1, a_pos_b_pos hP h2 h1⟩

/-- Woodford (2003), fn. 31 p. 361 and p. 363: for all sufficiently large `ε_ψ` the root
condition for (3.17) holds, so (3.19) is its unique bounded solution (`eq_sol317`). -/
theorem eventually_schurStable (hP : Admissible P) :
    ∀ᶠ ε in atTop, SchurStable (psi1M P ε) (psi2M P ε) := by
  have hβ0 := hP.hβ0; have hβ1 := hP.hβ1
  have h2 := (tendsto_psi2M hP).abs
  have h1 := (tendsto_psi1M hP).abs.sub (tendsto_psi2M hP)
  have hl2 : |P.β ^ 2| < 1 := by rw [abs_of_pos (by positivity)]; nlinarith
  have hl1 : |2 * P.β| - P.β ^ 2 < 1 := by
    rw [abs_of_pos (by positivity)]; nlinarith [sq_pos_of_pos (sub_pos.mpr hβ1)]
  filter_upwards [h2.eventually_lt_const hl2, h1.eventually_lt_const hl1]
    with ε e2 e1
  exact ⟨e2, by linarith⟩

end Woodford.PolicyResponseDynamics.InvestmentLimits
