/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkov
import StabilizationWelfare.BridgeExtensions
import StabilizationWelfare.BridgeCore
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Markov equilibrium: dispersion state, uniqueness, the Taylor principle, Layer B

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392), §2.2 (pp. 396–405: the
Calvo dispersion law, Proposition 6.3), §5 (pp. 455–463) and Appendix E; Chapter 4, §2.2
(Proposition 4.3); Appendix A.3.

Continues `NonlinearNKMarkov` (the exact conditions, the a-priori bound and the inverse function
argument on a finite Markov chain).

## Main results

* **The dispersion state.** `dispLaw`: the exact law `Δ_t = αΔ_{t−1}e^{θ(1+ω)π_t} +
  (1−α)e^{−θ(1+ω)x̂_t}`; `dispLaw_zero` (the deterministic steady state `Δ̄ = 1`, with
  `Δ_t − 1 = αᵗ⁺¹(Δ_{−1} − 1)` at `ε = 0`, `disp_det`); `disp_second_order` (on the price-index
  manifold `Δ_t − 1 − αe^{θ(1+ω)π}(Δ_{t−1} − 1)` is second order in `(π, x̂)`).
* **Uniqueness uniform over Markov operators.** `remainder_small` (a uniform first-order
  remainder for `C¹` maps), `uniform_uniqueness`: there is `ρ > 0`, depending only on the
  parameters, such that on EVERY state space with EVERY Markov operator two Markov equilibria within
  `ρ` of the steady state with disturbances within `ρ` coincide.
* **Markov equilibrium in the state `(Δ_{t−1}, s_t)`.** `fullOp` is the transition operator of the
  joint state when the dispersion moves by the policy's own law; `full_state_markov`: for `|ε|`
  small, the policy `(Δ, s) ↦ z_ε(s)` with dispersion policy `Δ′ = dispLaw Δ z_ε(s)` is a Markov
  equilibrium, and it is the UNIQUE Markov equilibrium within `ρ` among ALL policy functions of
  `(Δ_{t−1}, s_t)` (dispersion does not enter the forward-looking block, and the uniform bound
  rules out equilibria that depend on it).
* **The Taylor principle is necessary.** `taylor_necessary`: if `κ(φ_π − 1) + (1 − β)φ_y ≤ 0`
  there is a two-state stochastic matrix for which the linearised operator has a nonzero kernel;
  `lop_injective_iff`: the linearised operator is injective on EVERY finite Markov chain iff the
  Taylor principle holds.
* **Layer B (the family hypothesis discharged).** `family_sup`: `z_ε − εz₁ = O(ε²)` in the sup
  norm; `uproc_first_order`, `uproc_order_one`: along ANY shock path `s_t(ω)` on any `Ω` the
  equilibrium processes satisfy the `BridgeExtensions.UProc` hypotheses
  `X − εX₁ = O(ε²)` and `X = O(ε)` uniformly in `(t, ω)`; `disp_uniform`: `Δ_t − 1 = O(ε²)`
  uniformly when `Δ_{−1} − 1 = O(ε²)`; `calvoAS_of_markov`: with an `ExpectationSystem` whose
  conditional expectations follow the chain (`MarkovProp`), the equilibrium processes satisfy the
  exact Calvo model `LargeDistortions.CalvoModel.CalvoAS` of §5 for every amplitude, with the
  Euler equation `euler_of_markov` (in levels with the interest-rate rule: `euler_levels`,
  `euler_levels_markov`); `prop64_family`: the hypothesis `hπ` of
  `BridgeCore.Econ.prop64_bridge` along any shock path; `layerB_discharged` bundles the family
  hypotheses.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovLinks

open Filter Topology Asymptotics
open NonlinearNKMarkov

variable {p : Par}

/-! ## The price-dispersion state -/

/-- Woodford (2003), (2.12)–(2.13) and §5 (the exact Calvo dispersion law, Benigno–Woodford):
`Δ_t = αΔ_{t−1}e^{θ(1+ω)π_t} + (1−α)e^{−θ(1+ω)x̂_t}` with the reset gap
`x̂_t = (K̂_t − F̂_t)/(1+ωθ)`, `w = (ŷ, π, F̂, K̂)`. -/
noncomputable def dispLaw (p : Par) (Δ : ℝ) (w : Fin 4 → ℝ) : ℝ :=
  p.α * Δ * Real.exp (p.θ * (1 + p.ω) * w 1) +
    (1 - p.α) * Real.exp (-(p.θ * (1 + p.ω) * ((w 3 - w 2) / p.c0)))

/-- Woodford (2003), p. 400: at the steady state the dispersion law is `Δ′ = αΔ + (1 − α)`, whose
unique fixed point is `Δ̄ = 1`. -/
theorem dispLaw_zero (Δ : ℝ) : dispLaw p Δ 0 = p.α * Δ + (1 - p.α) := by
  simp [dispLaw]

/-- Woodford (2003), p. 400 (**the deterministic steady state is the base point of the
dispersion state**): with no disturbances (`z = 0`) dispersion converges to `1`,
`Δ_t − 1 = αᵗ⁺¹(Δ_{−1} − 1)`. -/
theorem disp_det (D : ℕ → ℝ) (hD : ∀ t, D (t + 1) = dispLaw p (D t) 0) (t : ℕ) :
    D t - 1 = p.α ^ t * (D 0 - 1) := by
  induction t with
  | zero => simp
  | succ t ih => rw [hD, dispLaw_zero, pow_succ]; linear_combination p.α * ih

/-- `|eᵘ − 1 − u| ≤ u²` for `|u| ≤ 1`. -/
theorem abs_expR_le {u : ℝ} (hu : |u| ≤ 1) : |Real.exp u - 1 - u| ≤ u ^ 2 :=
  Real.abs_exp_sub_one_sub_id_le hu

/-- Woodford (2003), App. E.2, p. 695 (**the dispersion law is second order on the price-index
manifold**): if the price index holds, `α(e^{(θ−1)π} − 1) + (1−α)(e^{−(θ−1)x̂} − 1) = 0`, and
`|π|, |x̂| ≤ 1/(θ(1+ω))`, then
`|Δ′ − 1 − αe^{θ(1+ω)π}(Δ − 1)| ≤ a(a + b)(π² + x̂²)` with `a = θ(1+ω)`, `b = θ − 1`: the
first-order terms cancel exactly as in Proposition 6.3. -/
theorem disp_second_order (hp : p.Std) (Δ : ℝ) (w : Fin 4 → ℝ)
    (hPI : p.α * (Real.exp ((p.θ - 1) * w 1) - 1) +
      (1 - p.α) * (Real.exp (-((p.θ - 1) * ((w 3 - w 2) / p.c0))) - 1) = 0)
    (hπ : |w 1| ≤ 1 / (p.θ * (1 + p.ω))) (hx : |(w 3 - w 2) / p.c0| ≤ 1 / (p.θ * (1 + p.ω))) :
    |dispLaw p Δ w - 1 - p.α * Real.exp (p.θ * (1 + p.ω) * w 1) * (Δ - 1)| ≤
      p.θ * (1 + p.ω) * (p.θ * (1 + p.ω) + (p.θ - 1)) *
        (w 1 ^ 2 + ((w 3 - w 2) / p.c0) ^ 2) := by
  set a := p.θ * (1 + p.ω) with ha
  set b := p.θ - 1 with hb
  set π := w 1
  set x := (w 3 - w 2) / p.c0
  have hb0 : 0 < b := by rw [hb]; linarith [hp.one_lt_θ]
  have hab : b ≤ a := by
    rw [ha, hb]; nlinarith [hp.ω_nonneg, hp.one_lt_θ]
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hab
  have hα0 := hp.α_pos
  have h1α : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  -- the four exponential remainders
  have hπa : |a * π| ≤ 1 := by
    rw [abs_mul, abs_of_pos ha0]
    calc a * |π| ≤ a * (1 / a) := mul_le_mul_of_nonneg_left hπ ha0.le
      _ = 1 := by field_simp
  have hxa : |-(a * x)| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_pos ha0]
    calc a * |x| ≤ a * (1 / a) := mul_le_mul_of_nonneg_left hx ha0.le
      _ = 1 := by field_simp
  have hπb : |b * π| ≤ 1 := by
    rw [abs_mul, abs_of_pos hb0]
    calc b * |π| ≤ a * |π| := mul_le_mul_of_nonneg_right hab (abs_nonneg _)
      _ ≤ 1 := by rw [← abs_of_pos ha0, ← abs_mul]; exact hπa
  have hxb : |-(b * x)| ≤ 1 := by
    rw [abs_neg, abs_mul, abs_of_pos hb0]
    calc b * |x| ≤ a * |x| := mul_le_mul_of_nonneg_right hab (abs_nonneg _)
      _ ≤ 1 := by rw [← abs_of_pos ha0, ← abs_mul, ← abs_neg]; exact hxa
  have r1 := abs_expR_le hπa
  have r2 := abs_expR_le hxa
  have r3 := abs_expR_le hπb
  have r4 := abs_expR_le hxb
  set R1 := Real.exp (a * π) - 1 - a * π
  set R2 := Real.exp (-(a * x)) - 1 - -(a * x)
  set R3 := Real.exp (b * π) - 1 - b * π
  set R4 := Real.exp (-(b * x)) - 1 - -(b * x)
  -- the linear term from the price index
  have hlin : b * (p.α * π - (1 - p.α) * x) = -(p.α * R3 + (1 - p.α) * R4) := by
    have : -(b * x) = -((p.θ - 1) * ((w 3 - w 2) / p.c0)) := by rw [hb]
    rw [← this] at hPI
    linear_combination hPI
  have hD : dispLaw p Δ w - 1 - p.α * Real.exp (a * π) * (Δ - 1) =
      -(a / b) * (p.α * R3 + (1 - p.α) * R4) + p.α * R1 + (1 - p.α) * R2 := by
    have e1 : a * (p.α * π - (1 - p.α) * x) = -(a / b) * (p.α * R3 + (1 - p.α) * R4) := by
      rw [show a * (p.α * π - (1 - p.α) * x) = (a / b) * (b * (p.α * π - (1 - p.α) * x)) by
        field_simp, hlin]
      ring
    unfold dispLaw
    rw [← e1]
    simp only [R1, R2]
    have : p.θ * (1 + p.ω) * ((w 3 - w 2) / p.c0) = a * x := rfl
    rw [this]
    ring
  rw [hD]
  have hR3 : |p.α * R3 + (1 - p.α) * R4| ≤ p.α * (b * π) ^ 2 + (1 - p.α) * (b * x) ^ 2 := by
    calc |p.α * R3 + (1 - p.α) * R4| ≤ |p.α * R3| + |(1 - p.α) * R4| := abs_add_le _ _
      _ = p.α * |R3| + (1 - p.α) * |R4| := by
          rw [abs_mul, abs_mul, abs_of_pos hα0, abs_of_pos h1α]
      _ ≤ p.α * (b * π) ^ 2 + (1 - p.α) * (-(b * x)) ^ 2 := by gcongr
      _ = _ := by ring
  calc |-(a / b) * (p.α * R3 + (1 - p.α) * R4) + p.α * R1 + (1 - p.α) * R2|
      ≤ (a / b) * |p.α * R3 + (1 - p.α) * R4| + p.α * |R1| + (1 - p.α) * |R2| := by
        have e := abs_add_le (-(a / b) * (p.α * R3 + (1 - p.α) * R4) + p.α * R1)
          ((1 - p.α) * R2)
        have e' := abs_add_le (-(a / b) * (p.α * R3 + (1 - p.α) * R4)) (p.α * R1)
        rw [abs_mul (1 - p.α), abs_of_pos h1α, abs_mul p.α, abs_of_pos hα0, abs_mul,
          abs_neg, abs_of_pos (div_pos ha0 hb0)] at *
        linarith
    _ ≤ (a / b) * (p.α * (b * π) ^ 2 + (1 - p.α) * (b * x) ^ 2) + p.α * (a * π) ^ 2 +
        (1 - p.α) * (-(a * x)) ^ 2 := by
        gcongr
    _ = a * b * (p.α * π ^ 2 + (1 - p.α) * x ^ 2) + a ^ 2 * (p.α * π ^ 2 + (1 - p.α) * x ^ 2) := by
        field_simp
        ring
    _ ≤ a * (a + b) * (π ^ 2 + x ^ 2) := by
        have : p.α * π ^ 2 + (1 - p.α) * x ^ 2 ≤ π ^ 2 + x ^ 2 := by
          nlinarith [sq_nonneg π, sq_nonneg x]
        have hab' : 0 ≤ a * b + a ^ 2 := by positivity
        nlinarith

/-! ## Uniqueness uniform over state spaces and Markov operators -/

/-- Woodford (2003), App. A.3: the partial derivative of `Q` in `w` at the steady state is `DQ`. -/
theorem fderiv_Qmap_inr (v : Fin 4 → ℝ) : fderiv ℝ (Qmap p) (0, 0) (0, v) = DQ0 p v := by
  have hd : HasFDerivAt (Qmap p) (fderiv ℝ (Qmap p) (0, 0)) (0, 0) :=
    ((contDiff_Qmap (p := p) (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 5 → ℝ), t • v)) ((0 : Fin 5 → ℝ), v) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : Fin 5 → ℝ)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Qmap_line v i)

/-- Woodford (2003), App. A.3: the partial derivative of `N` in `w` at the steady state is `DN`. -/
theorem fderiv_Nmap_inr (v : Fin 4 → ℝ) : fderiv ℝ (Nmap p) (0, 0) (0, v) = DN0 p v := by
  have hd : HasFDerivAt (Nmap p) (fderiv ℝ (Nmap p) (0, 0)) (0, 0) :=
    ((contDiff_Nmap (p := p) (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 5 → ℝ), t • v)) ((0 : Fin 5 → ℝ), v) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : Fin 5 → ℝ)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Nmap_line v i)

/-- Woodford (2003), App. A.3 (**a uniform first-order remainder**): for a `C¹` map `g(e, w)`,
for every `η > 0` there is `ρ > 0` with
`‖g(e, w) − g(e, w′) − Dg(0,0)(0, w − w′)‖ ≤ η‖w − w′‖` whenever `‖e‖, ‖w‖, ‖w′‖ ≤ ρ`. -/
theorem remainder_small {g : (Fin 5 → ℝ) × (Fin 4 → ℝ) → (Fin 4 → ℝ)} (hg : ContDiff ℝ 1 g)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ e w w', ‖e‖ ≤ ρ → ‖w‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖g (e, w) - g (e, w') - fderiv ℝ g (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖ := by
  have hc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  obtain ⟨ρ', hρ', hball⟩ := Metric.continuousAt_iff.1 hc.continuousAt η hη
  refine ⟨ρ' / 2, by positivity, fun e w w' he hw hw' => ?_⟩
  set A := fderiv ℝ g (0, 0) with hA
  set I := ContinuousLinearMap.inr ℝ (Fin 5 → ℝ) (Fin 4 → ℝ)
  set B := Metric.closedBall (0 : Fin 4 → ℝ) (ρ' / 2)
  have hdiff : ∀ u ∈ B, HasFDerivWithinAt (fun u => g (e, u) - A (0, u))
      ((fderiv ℝ g (e, u) - A).comp I) B u := fun u _ => by
    have h1 : HasFDerivAt (fun u => g (e, u)) ((fderiv ℝ g (e, u)).comp I) u :=
      ((hg.differentiable one_ne_zero) (e, u)).hasFDerivAt.comp u (hasFDerivAt_prodMk_right e u)
    have h2 : HasFDerivAt (fun u => A (0, u)) (A.comp I) u := (A.comp I).hasFDerivAt
    have := h1.sub h2
    rw [← ContinuousLinearMap.sub_comp] at this
    exact this.hasFDerivWithinAt
  have hbound : ∀ u ∈ B, ‖(fderiv ℝ g (e, u) - A).comp I‖ ≤ η := fun u hu => by
    have hd : dist (e, u) (0, 0) < ρ' := by
      have hu' : ‖u‖ ≤ ρ' / 2 := by simpa [B] using hu
      change dist (e, u) 0 < ρ'
      rw [dist_zero_right, Prod.norm_def]
      exact lt_of_le_of_lt (max_le he hu') (by linarith)
    have h := hball hd
    rw [dist_eq_norm] at h
    calc ‖(fderiv ℝ g (e, u) - A).comp I‖ ≤ ‖fderiv ℝ g (e, u) - A‖ * ‖I‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ η * 1 := mul_le_mul h.le (ContinuousLinearMap.norm_inr_le_one ℝ _ _) (norm_nonneg _) hη.le
      _ = η := mul_one η
  have hwB : w ∈ B := by simpa [B] using hw
  have hw'B : w' ∈ B := by simpa [B] using hw'
  have := (convex_closedBall (0 : Fin 4 → ℝ) (ρ' / 2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    hdiff hbound hw'B hwB
  have e1 : g (e, w) - A (0, w) - (g (e, w') - A (0, w')) =
      g (e, w) - g (e, w') - A (0, w - w') := by
    have : ((0 : Fin 5 → ℝ), w - w') = ((0 : Fin 5 → ℝ), w) - (0, w') := by simp
    rw [this, map_sub]; abel
  rw [e1] at this
  exact this

/-- `Mv` is subtractive. -/
theorem Mv_sub {X : Type*} {n : ℕ} (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (h k : X → Fin n → ℝ) :
    Mv M (fun x => h x - k x) = fun x => Mv M h x - Mv M k x := by
  funext x i
  simp only [Mv, Pi.sub_apply]
  have : (fun x' => h x' i - k x' i) = (fun x' => h x' i) - fun x' => k x' i := rfl
  rw [this, map_sub]
  rfl

/-- Woodford (2003), App. A.3: the a-priori constant is positive. -/
theorem Kap_pos (hp : p.Std) : 0 < Kap p := by
  unfold Kap Kc
  have := Uc_nonneg hp; have := Fc_nonneg hp; have := hp.k3_pos; have := hp.cR_pos
  positivity

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**local uniqueness of Markov equilibria,
uniform over state spaces and Markov operators**): under the Taylor principle there is `ρ > 0`,
depending only on the parameters, such that for every state space `X`, every Markov operator `M`,
every disturbance pattern and amplitude with `‖εξ(x)‖ ≤ ρ`, any two Markov equilibria `z, z′` with
`‖z(x)‖, ‖z′(x)‖ ≤ ρ` everywhere coincide. -/
theorem uniform_uniqueness (hp : p.Std) :
    ∃ ρ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ (ξ : X → Fin 5 → ℝ) (ε : ℝ) (z z' : X → Fin 4 → ℝ), (∀ x, ‖ε • ξ x‖ ≤ ρ) →
        (∀ x, ‖z x‖ ≤ ρ) → (∀ x, ‖z' x‖ ≤ ρ) → IsMarkovEqm p M ξ ε z →
          IsMarkovEqm p M ξ ε z' → z = z' := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_small (contDiff_Qmap (p := p) (n := 1)) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_small (contDiff_Nmap (p := p) (n := 1)) hη0
  refine ⟨min ρQ ρN, lt_min hρQ hρN, fun X M hM ξ ε z z' he hz hz' hE hE' => ?_⟩
  set d : X → Fin 4 → ℝ := fun x => z x - z' x with hd
  have hd0 : ∀ x, ‖d x‖ ≤ 2 * min ρQ ρN := fun x => by
    calc ‖d x‖ ≤ ‖z x‖ + ‖z' x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hz x, hz' x]
  have himp : ∀ U, (∀ x, ‖d x‖ ≤ U) → ∀ x, ‖d x‖ ≤ 0 + 1 / 2 * U := by
    intro U hU x
    have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU x)
    -- the residual identity
    have hres : ∀ x, Lop p M d x = -(Qmap p (ε • ξ x, z x) - Qmap p (ε • ξ x, z' x) -
        fderiv ℝ (Qmap p) (0, 0) (0, d x)) - Mv M (fun x' => Nmap p (ε • ξ x', z x') -
          Nmap p (ε • ξ x', z' x') - fderiv ℝ (Nmap p) (0, 0) (0, d x')) x := fun x => by
      have h1 := congrFun hE x
      have h2 := congrFun hE' x
      simp only [Phi, Pi.zero_apply] at h1 h2
      simp only [fderiv_Qmap_inr, fderiv_Nmap_inr]
      have e1 := congrFun (Mv_sub M (fun x' => Nmap p (ε • ξ x', z x') -
        Nmap p (ε • ξ x', z' x')) (fun x' => DN0 p (d x'))) x
      have e2 := congrFun (Mv_sub M (fun x' => Nmap p (ε • ξ x', z x'))
        (fun x' => Nmap p (ε • ξ x', z' x'))) x
      rw [e1, e2]
      simp only [Lop]
      linear_combination h1 - h2
    have hnorm : ∀ x, ‖Lop p M d x‖ ≤ 2 * η * U := fun x => by
      rw [hres x]
      have hzx := (hz x).trans (min_le_left _ _)
      have hz'x := (hz' x).trans (min_le_left _ _)
      have hex := (he x).trans (min_le_left _ _)
      have e1 := hQ (ε • ξ x) (z x) (z' x) hex hzx hz'x
      have e2 : ∀ x', ‖Nmap p (ε • ξ x', z x') - Nmap p (ε • ξ x', z' x') -
          fderiv ℝ (Nmap p) (0, 0) (0, d x')‖ ≤ η * U := fun x' => by
        have := hN (ε • ξ x') (z x') (z' x') ((he x').trans (min_le_right _ _))
          ((hz x').trans (min_le_right _ _)) ((hz' x').trans (min_le_right _ _))
        exact this.trans (mul_le_mul_of_nonneg_left (hU x') hη0.le)
      have e3 := Mv_norm_le hM (mul_nonneg hη0.le hU0) e2 x
      calc _ ≤ ‖-(Qmap p (ε • ξ x, z x) - Qmap p (ε • ξ x, z' x) -
              fderiv ℝ (Qmap p) (0, 0) (0, d x))‖ + ‖Mv M (fun x' => Nmap p (ε • ξ x', z x') -
              Nmap p (ε • ξ x', z' x') - fderiv ℝ (Nmap p) (0, 0) (0, d x')) x‖ :=
            norm_sub_le _ _
        _ ≤ η * U + η * U := by
            rw [norm_neg]
            exact add_le_add (e1.trans (mul_le_mul_of_nonneg_left (hU x) hη0.le)) e3
        _ = 2 * η * U := by ring
    have := apriori hp hM hd0 hnorm x
    calc ‖d x‖ ≤ Kap p * (2 * η * U) := this
      _ = 0 + 1 / 2 * U := by rw [hη]; field_simp; ring
  funext x
  have h := bound_of_improve (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hd0 himp x
  have : d x = 0 := norm_le_zero_iff.1 (by simpa using h)
  exact sub_eq_zero.1 this

/-! ## The Markov equilibrium in the state `(Δ_{t−1}, s_t)` -/

variable {S : Type*} [Fintype S]

/-- Woodford (2003), §2.2 and App. A.3 (**the transition of the joint state**): when the policy
`g(Δ, s)` is followed, next period's state is `(dispLaw Δ g(Δ, s), s′)` with `s′ ~ P(s, ·)`, so
`(Mh)(Δ, s) = ∑_{s′} P(s, s′) h(dispLaw Δ g(Δ, s), s′)`. -/
noncomputable def fullOp (p : Par) (P : S → S → ℝ) (g : ℝ × S → Fin 4 → ℝ) :
    (ℝ × S → ℝ) →ₗ[ℝ] (ℝ × S → ℝ) where
  toFun h x := ∑ s', P x.2 s' * h (dispLaw p x.1 (g x), s')
  map_add' h k := by funext x; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c h := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Woodford (2003), App. A.3: the joint transition operator is a Markov operator. -/
theorem fullOp_isMarkov {P : S → S → ℝ} (hP : Stochastic P) (g : ℝ × S → Fin 4 → ℝ) :
    IsMarkov (fullOp p P g) := by
  refine ⟨?_, fun h C hC x => ?_⟩
  · funext x; simp [fullOp, hP.2 x.2]
  · change |∑ s', P x.2 s' * h (dispLaw p x.1 (g x), s')| ≤ C
    calc |∑ s', P x.2 s' * h (dispLaw p x.1 (g x), s')|
        ≤ ∑ s', |P x.2 s' * h (dispLaw p x.1 (g x), s')| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', P x.2 s' * C := Finset.sum_le_sum fun s' _ => by
          rw [abs_mul, abs_of_nonneg (hP.1 x.2 s')]
          exact mul_le_mul_of_nonneg_left (hC _) (hP.1 x.2 s')
      _ = C := by rw [← Finset.sum_mul, hP.2 x.2, one_mul]

/-- Woodford (2003), App. A.3: a policy that does not depend on the lagged dispersion is an
equilibrium in the joint state iff it is an equilibrium in the exogenous state, whatever the law
of motion of dispersion (dispersion does not enter the forward-looking block). -/
theorem eqm_lift_iff (P : S → S → ℝ) (g : ℝ × S → Fin 4 → ℝ) (ξ : S → Fin 5 → ℝ) (ε : ℝ)
    (z : S → Fin 4 → ℝ) :
    IsMarkovEqm p (fullOp p P g) (fun x => ξ x.2) ε (fun x => z x.2) ↔
      IsMarkovEqm p (chainOp P) ξ ε z := by
  have key : ∀ x : ℝ × S, Phi p (fullOp p P g) (fun x => ξ x.2) ε (fun x => z x.2) x =
      Phi p (chainOp P) ξ ε z x.2 := fun x => rfl
  constructor
  · intro h
    funext s
    have := congrFun h (0, s)
    rw [key] at this
    exact this
  · intro h
    funext x
    rw [key, h]
    rfl

/-- Woodford (2003), Ch. 6, §1 and App. A.3 with the Taylor principle (Proposition 4.3)
(**THE MARKOV EQUILIBRIUM IN THE STATE (LAGGED DISPERSION, SHOCK)**). For a finite Markov chain
`(S, P)` and a disturbance pattern `ξ` there are `ρ, δ > 0` and a `C²` family `ε ↦ z_ε` with
`z₀ = 0` such that for `|ε| < δ`:
* the time-invariant policy functions `(Δ_{t−1}, s_t) ↦ z_ε(s_t)` for `(ŷ, π, F̂, K̂)`, together
  with the dispersion policy `Δ_t = dispLaw(Δ_{t−1}, z_ε(s_t))`, form a Markov equilibrium in
  the joint state (with the joint transition `fullOp`);
* `‖z_ε(s)‖ < ρ`;
* every policy function `g` of the joint state `(Δ_{t−1}, s_t)` with `‖g‖ ≤ ρ` that is a Markov
  equilibrium (with its own dispersion law) equals it. -/
theorem full_state_markov (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 5 → ℝ) :
    ∃ ρ > 0, ∃ δ > 0, ∃ z : ℝ → S → Fin 4 → ℝ, z 0 = 0 ∧ ContDiffAt ℝ 2 z 0 ∧
      ∀ ε, |ε| < δ →
        IsMarkovEqm p (fullOp p P (fun x => z ε x.2)) (fun x => ξ x.2) ε (fun x => z ε x.2) ∧
        (∀ s, ‖z ε s‖ < ρ) ∧
        ∀ g : ℝ × S → Fin 4 → ℝ, (∀ x, ‖g x‖ ≤ ρ) →
          IsMarkovEqm p (fullOp p P g) (fun x => ξ x.2) ε g → g = fun x => z ε x.2 := by
  obtain ⟨ρ, hρ, huniq⟩ := uniform_uniqueness hp
  obtain ⟨r, hr, δ0, hδ0, z, hz0, hzC, hz, -⟩ := markov_equilibrium hp hP ξ
  have hzc : ContinuousAt z 0 := hzC.continuousAt
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), z ε ∈ Metric.ball (0 : S → Fin 4 → ℝ) ρ := by
    have := hzc.tendsto
    rw [hz0] at this
    exact this (Metric.ball_mem_nhds _ hρ)
  obtain ⟨δ1, hδ1, hδ1ev⟩ := Metric.eventually_nhds_iff.1 hev
  set Ξ := ∑ s, ‖ξ s‖ with hΞ
  have hΞ0 : 0 ≤ Ξ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hξs : ∀ s, ‖ξ s‖ ≤ Ξ := fun s =>
    Finset.single_le_sum (f := fun s => ‖ξ s‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  set δ2 := ρ / (Ξ + 1) with hδ2
  have hδ2p : 0 < δ2 := by positivity
  refine ⟨ρ, hρ, min δ0 (min δ1 δ2), lt_min hδ0 (lt_min hδ1 hδ2p), z, hz0, hzC, ?_⟩
  intro ε hε
  have hε0 : |ε| < δ0 := lt_of_lt_of_le hε (min_le_left _ _)
  have hε1 : |ε| < δ1 := lt_of_lt_of_le hε ((min_le_right _ _).trans (min_le_left _ _))
  have hε2 : |ε| < δ2 := lt_of_lt_of_le hε ((min_le_right _ _).trans (min_le_right _ _))
  have hzε : ‖z ε‖ < ρ := by
    have := hδ1ev (show dist ε 0 < δ1 by rw [Real.dist_eq, sub_zero]; exact hε1)
    rwa [Metric.mem_ball, dist_zero_right] at this
  have hzs : ∀ s, ‖z ε s‖ < ρ := fun s => lt_of_le_of_lt (norm_le_pi_norm (z ε) s) hzε
  have heqm := (hz ε hε0).1
  refine ⟨(eqm_lift_iff P _ ξ ε (z ε)).2 heqm, hzs, fun g hg hgE => ?_⟩
  refine huniq (ℝ × S) (fullOp p P g) (fullOp_isMarkov hP g) (fun x => ξ x.2) ε g
    (fun x => z ε x.2) (fun x => ?_) hg (fun x => (hzs x.2).le) hgE
    ((eqm_lift_iff P g ξ ε (z ε)).2 heqm)
  rw [norm_smul, Real.norm_eq_abs]
  calc |ε| * ‖ξ x.2‖ ≤ δ2 * (Ξ + 1) := by
        apply mul_le_mul hε2.le (by linarith [hξs x.2]) (norm_nonneg _) hδ2p.le
    _ = ρ := by rw [hδ2]; field_simp

/-! ## The Taylor principle is necessary -/

/-- Woodford (2003), Proposition 4.3, p. 254: `det(B₀ − λB₁)` for the IS–AS block,
`(σ + φ_y − λσ)(1 − λβ) + κ(φ_π − λ)`. -/
noncomputable def charPoly (p : Par) (l : ℝ) : ℝ :=
  (p.σ + p.φy - l * p.σ) * (1 - l * p.β) + p.κ * (p.φ - l)

/-- Woodford (2003), Proposition 4.3 (**necessity of the Taylor principle, Markov form**): if
`κ(φ_π − 1) + (1 − β)φ_y ≤ 0` (all other assumptions maintained) there is a two-state stochastic
matrix `P` (with eigenvalue `λ₀ ∈ [0, 1]` a root of `det(B₀ − λB₁)`) and a nonzero `v` with
`Lv = 0`: the linearised operator is not invertible, so the implicit function theorem does not
apply on that chain. -/
theorem taylor_necessary (hα0 : 0 < p.α) (hα1 : p.α < 1) (hβ0 : 0 < p.β) (hβ1 : p.β < 1)
    (hθ : 1 < p.θ) (hω : 0 ≤ p.ω) (hσ : 0 < p.σ) (hφ : 0 ≤ p.φ) (hφy : 0 ≤ p.φy)
    (hT : p.κ * (p.φ - 1) + (1 - p.β) * p.φy ≤ 0) :
    ∃ P : Fin 2 → Fin 2 → ℝ, Stochastic P ∧
      ∃ v : Fin 2 → Fin 4 → ℝ, v ≠ 0 ∧ Lop p (chainOp P) v = 0 := by
  have hc0 : 0 < p.c0 := by
    have := mul_nonneg hω (by linarith : (0 : ℝ) ≤ p.θ); unfold Par.c0; linarith
  have h1α : 0 < 1 - p.α := by linarith
  have hab : p.α * p.β < 1 := by nlinarith
  have hκ : 0 < p.κ := by
    unfold Par.κ Moments.calvoKappa
    have h2 : 0 < 1 - p.α * p.β := by linarith
    have h3 : 0 < p.ω + p.σ := by linarith
    have h4 : 0 < 1 + p.ω * p.θ := hc0
    positivity
  -- a root of the characteristic polynomial in `[0, 1]`
  have hcont : ContinuousOn (charPoly p) (Set.Icc 0 1) := by
    unfold charPoly; fun_prop
  have h0 : 0 ≤ charPoly p 0 := by
    unfold charPoly; have := mul_nonneg hφ hκ.le; nlinarith
  have h1 : charPoly p 1 ≤ 0 := by unfold charPoly; nlinarith
  obtain ⟨l, hl, hroot⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont ⟨h1, h0⟩
  obtain ⟨hl0, hl1⟩ := hl
  set P : Fin 2 → Fin 2 → ℝ := ![![(1 + l) / 2, (1 - l) / 2], ![(1 - l) / 2, (1 + l) / 2]] with hP
  have hPs : Stochastic P := by
    refine ⟨fun s s' => ?_, fun s => ?_⟩
    · fin_cases s <;> fin_cases s' <;> simp [hP] <;> linarith
    · fin_cases s <;> simp [hP, Fin.sum_univ_two] <;> ring
  set y0 := 1 - l * p.β
  set π0 := p.κ
  have hd : 0 < 1 - p.α * p.β * l := by
    have : p.α * p.β * l ≤ p.α * p.β := mul_le_of_le_one_right (by positivity) hl1
    linarith
  set F0 := ((1 - p.α * p.β) * (1 - p.σ) * y0 + p.α * p.β * l * (p.θ - 1) * π0) /
    (1 - p.α * p.β * l)
  set K0 := F0 + p.cR * π0
  set c : Fin 4 → ℝ := ![y0, π0, F0, K0] with hc
  set w : Fin 2 → ℝ := ![1, -1] with hw
  set v : Fin 2 → Fin 4 → ℝ := fun s i => w s * c i with hv
  have hPv : ∀ i s, chainOp P (fun s' => v s' i) s = l * v s i := fun i s => by
    fin_cases s <;> simp [chainOp, Fin.sum_univ_two, hP, hv, hw] <;> ring
  refine ⟨P, hPs, v, fun h => ?_, ?_⟩
  · have := congrFun (congrFun h 0) 1
    have h2 : w 0 * c 1 = 0 := this
    simp only [hw, hc, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at h2
    exact hκ.ne' h2
  · have hk' : p.κ * p.cR = (1 - p.α * p.β) * (p.ω + p.σ) := by
      unfold Par.κ Moments.calvoKappa Par.cR Par.c0
      field_simp
    have habc : p.α * p.β * (p.c0 + p.cR) = p.β * p.cR := by
      unfold Par.cR; field_simp; ring
    have hcR : (1 - p.α) * p.cR = p.α * p.c0 := by unfold Par.cR; field_simp
    have hcharl : (p.σ + p.φy - l * p.σ) * (1 - l * p.β) + p.κ * (p.φ - l) = 0 := hroot
    funext s i
    obtain ⟨e0, e1, e2, e3⟩ := Lop_apply (p := p) (chainOp P) v s
    simp only [Pi.zero_apply]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      rw [e0, hPv, hPv]
      simp only [hv, hc, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination w s * hcharl
    · simp only [Fin.mk_one, Fin.isValue]
      rw [e1, hPv, hPv]
      simp only [hv, hc, Matrix.cons_val]
      have : F0 * (1 - p.α * p.β * l) =
          (1 - p.α * p.β) * (1 - p.σ) * y0 + p.α * p.β * l * (p.θ - 1) * π0 := by
        simp only [F0]; field_simp
      linear_combination w s * this
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [e2, hPv, hPv]
      simp only [hv, hc, Matrix.cons_val]
      have hF : F0 * (1 - p.α * p.β * l) =
          (1 - p.α * p.β) * (1 - p.σ) * y0 + p.α * p.β * l * (p.θ - 1) * π0 := by
        simp only [F0]; field_simp
      simp only [K0, y0, π0] at hF ⊢
      unfold Par.c0 at habc
      linear_combination w s * hF - w s * l * p.κ * habc + w s * (1 - l * p.β) * hk'
    · simp only [Fin.reduceFinMk, Fin.isValue]
      rw [e3]
      simp only [hv, hc, Matrix.cons_val]
      have hKF : w s * K0 - w s * F0 = w s * (p.cR * π0) := by simp only [K0]; ring
      rw [hKF]
      have : (1 - p.α) * (p.θ - 1) * (w s * (p.cR * π0)) / p.c0 =
          p.α * (p.θ - 1) * (w s * π0) := by
        rw [div_eq_iff hc0.ne']
        linear_combination (p.θ - 1) * w s * π0 * hcR
      rw [this]; ring

/-- Woodford (2003), Proposition 4.3 in Markov form (**the Taylor principle is exactly the
condition for the linearised operator to be injective on every finite Markov chain**): given the
other maintained assumptions, `L` is injective for every finite stochastic matrix iff
`κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem lop_injective_iff (hα0 : 0 < p.α) (hα1 : p.α < 1) (hβ0 : 0 < p.β) (hβ1 : p.β < 1)
    (hθ : 1 < p.θ) (hω : 0 ≤ p.ω) (hσ : 0 < p.σ) (hφ : 0 ≤ p.φ) (hφy : 0 ≤ p.φy) :
    (∀ (n : ℕ) (P : Fin n → Fin n → ℝ), Stochastic P → ∀ v : Fin n → Fin 4 → ℝ,
      Lop p (chainOp P) v = 0 → v = 0) ↔ 0 < p.κ * (p.φ - 1) + (1 - p.β) * p.φy := by
  constructor
  · intro h
    by_contra hT
    obtain ⟨P, hP, v, hv, hL⟩ :=
      taylor_necessary hα0 hα1 hβ0 hβ1 hθ hω hσ hφ hφy (not_lt.1 hT)
    exact hv (h 2 P hP v hL)
  · intro hT n P hP v hL
    have hp : p.Std := ⟨hα0, hα1, hβ0, hβ1, hθ, hω, hσ, hφ, hφy, hT⟩
    exact Lop_injective hp (chainOp_isMarkov hP) (V0 := ‖v‖) (fun s => norm_le_pi_norm v s) hL

/-! ## Layer B: the family of equilibria discharges the family hypothesis

Along the Markov equilibrium of amplitude `ε` and ANY realisation `s_t(ω)` of the exogenous state
(on any `Ω`), every endogenous variable is `X_t(ω) = z_ε(s_t(ω))`; since `ε ↦ z_ε` is `C²` in the
SUP norm over the finite state space, the orders hold uniformly in the date and the state. -/

/-- Woodford (2003), §1, pp. 385–389 (**the family is `C²` in the sup norm**): a family with
`z₀ = 0`, `C²` at `0`, satisfies `z_ε − ε z′(0) = O(ε²)` in the sup norm over states. -/
theorem family_sup {z : ℝ → S → Fin 4 → ℝ} (hz0 : z 0 = 0) (hzC : ContDiffAt ℝ 2 z 0) :
    (fun ε => z ε - ε • deriv z 0) =O[𝓝 0] fun ε => ε ^ 2 := by
  have hd : HasDerivAt z (deriv z 0) 0 :=
    (hzC.differentiableAt (by norm_num)).hasDerivAt
  rw [isBigO_pi]
  intro s
  rw [isBigO_pi]
  intro i
  set L : (S → Fin 4 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => Fin 4 → ℝ) s)
  have hc : ContDiffAt ℝ 2 (fun ε => z ε s i) 0 := L.contDiff.contDiffAt.comp 0 hzC
  have hder : deriv (fun ε => z ε s i) 0 = deriv z 0 s i :=
    (L.hasFDerivAt.comp_hasDerivAt 0 hd).deriv
  have h := OneParamTaylor.taylor_one_bigO hc
  refine h.congr (fun ε => ?_) (fun ε => by ring)
  simp [hz0, hder]
  ring

/-- Woodford (2003), §1 (**the family is `O(ε)` in the sup norm**). -/
theorem family_order_one {z : ℝ → S → Fin 4 → ℝ} (hz0 : z 0 = 0) (hzC : ContDiffAt ℝ 2 z 0) :
    z =O[𝓝 0] fun ε => ε := by
  have h1 := family_sup hz0 hzC
  have h2 : (fun ε : ℝ => ε ^ 2) =O[𝓝 0] fun ε => ε :=
    (BridgeCore.pow_isBigO_pow (s := fun ε : ℝ => ε) tendsto_id (by norm_num : 1 ≤ 2)).congr_right
      fun ε => pow_one ε
  have h3 : (fun ε : ℝ => ε • deriv z 0) =O[𝓝 0] fun ε => ε :=
    (isBigO_refl (fun ε : ℝ => ε) _).smul (isBigO_const_const _ one_ne_zero _) |>.congr_right
      fun ε => mul_one ε
  exact ((h1.trans h2).add h3).congr_left fun ε => by abel

/-- The endogenous process `X_t(ω) = z_ε(s_t(ω))_i` along a shock path. -/
def proc {Ω : Type*} (z : ℝ → S → Fin 4 → ℝ) (sh : ℕ → Ω → S) (i : Fin 4) :
    ℝ → ℕ → Ω → ℝ :=
  fun ε t ω => z ε (sh t ω) i

/-- Woodford (2003), App. E (`BridgeExtensions.UProc`, **the first-order hypothesis
discharged**): `X − εX₁ = O(ε²)` uniformly in `(t, ω)`, with `X₁ = z′(0)(s_t)`. -/
theorem uproc_first_order {Ω : Type*} {z : ℝ → S → Fin 4 → ℝ} (hz0 : z 0 = 0)
    (hzC : ContDiffAt ℝ 2 z 0) (sh : ℕ → Ω → S) (i : Fin 4) :
    BridgeExtensions.UProc (𝓝 0)
      (fun ε t ω => proc z sh i ε t ω - ε * deriv z 0 (sh t ω) i) fun ε => ε ^ 2 := by
  obtain ⟨C, hC⟩ := (family_sup hz0 hzC).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC.prod_inl ⊤] with q hq
  have h1 := norm_le_pi_norm ((z q.1 - q.1 • deriv z 0) (sh q.2.1 q.2.2)) i
  have h2 := norm_le_pi_norm (z q.1 - q.1 • deriv z 0) (sh q.2.1 q.2.2)
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  exact h1.trans (h2.trans hq)

/-- Woodford (2003), App. E: the first-order processes `z′(0)(s_t)` are bounded by `‖z₁‖`. -/
theorem bounded_first {Ω : Type*} (z1 : S → Fin 4 → ℝ) (sh : ℕ → Ω → S) (i : Fin 4) :
    ∀ t ω, |z1 (sh t ω) i| ≤ ‖z1‖ := by
  intro t ω
  have h1 := norm_le_pi_norm (z1 (sh t ω)) i
  have h2 := norm_le_pi_norm z1 (sh t ω)
  rw [Real.norm_eq_abs] at h1
  exact h1.trans h2

/-- Woodford (2003), §2, p. 394 (`BridgeExtensions.UProc`, **"bounded fluctuations"
discharged**): every endogenous process is `O(ε)` uniformly in `(t, ω)`. -/
theorem uproc_order_one {Ω : Type*} {z : ℝ → S → Fin 4 → ℝ} (hz0 : z 0 = 0)
    (hzC : ContDiffAt ℝ 2 z 0) (sh : ℕ → Ω → S) (i : Fin 4) :
    BridgeExtensions.UProc (𝓝 0) (proc z sh i) fun ε => ε ^ 1 :=
  BridgeExtensions.first_order_o (e := fun ε : ℝ => ε) tendsto_id
    ⟨_, bounded_first (deriv z 0) sh i⟩ (uproc_first_order hz0 hzC sh i)

/-- Woodford (2003), Proposition 6.4 (**the hypothesis `hπ` of `BridgeCore.Econ.prop64_bridge`
discharged**): along ANY deterministic path `s_t` of the exogenous state, inflation
`π_t(ε) = z_ε(s_t)₁` satisfies `π_t(ε) − επ₁_t = O(ε²)` uniformly in `t` (filter
`BridgeCore.unif`), with `π₁_t = z′(0)(s_t)₁` bounded. -/
theorem prop64_family {z : ℝ → S → Fin 4 → ℝ} (hz0 : z 0 = 0) (hzC : ContDiffAt ℝ 2 z 0)
    (sh : ℕ → S) :
    (fun q : ℕ × ℝ => z q.2 (sh q.1) 1 - q.2 * deriv z 0 (sh q.1) 1) =O[BridgeCore.unif]
      (fun q => q.2 ^ 2) ∧ ∃ C, ∀ t, |deriv z 0 (sh t) 1| ≤ C := by
  refine ⟨?_, ‖deriv z 0‖, fun t => ?_⟩
  · obtain ⟨C, hC⟩ := (family_sup hz0 hzC).bound
    refine BridgeCore.isBigO_unif_iff (f := fun t ε => z ε (sh t) 1 - ε * deriv z 0 (sh t) 1)
      (g := fun ε => ε ^ 2) |>.2 ⟨C, ?_⟩
    filter_upwards [hC] with ε hε t
    have h1 := norm_le_pi_norm ((z ε - ε • deriv z 0) (sh t)) 1
    have h2 := norm_le_pi_norm (z ε - ε • deriv z 0) (sh t)
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    exact h1.trans (h2.trans hε)
  · have h1 := norm_le_pi_norm (deriv z 0 (sh t)) 1
    have h2 := norm_le_pi_norm (deriv z 0) (sh t)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2

/-! ### The exact Calvo model along the chain (`LargeDistortions.CalvoModel.CalvoAS`) -/

/-- Woodford (2003), App. A.3 (**rational expectations follow the chain**): conditional
expectations of functions of next period's exogenous state are given by the transition matrix,
`E_t[h(s_{t+1})] = ∑_{s′} P(s_t, s′) h(s′)`. -/
def MarkovProp {Ω : Type*} (𝔼 : ExpectationSystem Ω) (P : S → S → ℝ) (sh : ℕ → Ω → S) :
    Prop :=
  ∀ t (h : S → ℝ), 𝔼.E t (fun ω => h (sh (t + 1) ω)) = fun ω => chainOp P h (sh t ω)

/-- The equilibrium conditions of a Markov equilibrium, component by component. -/
theorem eqm_comp {P : S → S → ℝ} {ξ : S → Fin 5 → ℝ} {ε : ℝ} {w : S → Fin 4 → ℝ}
    (hw : IsMarkovEqm p (chainOp P) ξ ε w) (s : S) (i : Fin 4) :
    Qmap p (ε • ξ s, w s) i + ∑ s', P s s' * Nmap p (ε • ξ s', w s') i = 0 :=
  congrFun (congrFun hw s) i

/-- `∑ P(s, s′)(a E(s′) + b) = a ∑ P(s, s′)E(s′) + b` for a stochastic matrix. -/
theorem sum_P_affine {P : S → S → ℝ} (hP : Stochastic P) (s : S) (a b : ℝ) (E : S → ℝ) :
    ∑ s', P s s' * (a * E s' + b) = a * ∑ s', P s s' * E s' + b := by
  have : ∑ s', P s s' * (a * E s' + b) = a * ∑ s', P s s' * E s' + b * ∑ s', P s s' := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this, hP.2 s, mul_one]

/-- Woodford (2003), §5, pp. 457–458 and Ch. 3 (**the Calvo block of the Layer-B family
discharged**): if `w` is a Markov equilibrium of amplitude `ε` and the expectation system follows
the chain (`MarkovProp`), then along the shock path the processes
`π_t = w(s_t)₁`, `x̂_t = (K̂_t − F̂_t)/(1+ωθ)`, `F̂_t`, `K̂_t`, `Ŷ_t = w(s_t)₀`,
`f̂_t = (1−σ)Ŷ_t + σĉ_t + τ̂_t`, `k̂_t = (1+ω)Ŷ_t − ωq_t + μ̂ʷ_t`, with `Ĝ = 0` and the disturbances
`(ĉ, τ̂, q, μ̂ʷ) = εξ(s_t)`, satisfy EXACTLY the Calvo model `CalvoAS` of §5 (with `s_C = 1`): the
price index, the reset price, the recursions for `F` and `K`, and the isoelastic forms. -/
theorem calvoAS_of_markov (hp : p.Std) {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    {P : S → S → ℝ} (hP : Stochastic P) (ξ : S → Fin 5 → ℝ) (ε : ℝ) (w : S → Fin 4 → ℝ)
    (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S) (hM : MarkovProp 𝔼 P sh) :
    LargeDistortions.CalvoModel.CalvoAS 𝔼 p.α p.β p.θ p.ω p.σ 1
      (fun t ω => w (sh t ω) 1) (fun t ω => (w (sh t ω) 3 - w (sh t ω) 2) / p.c0)
      (fun t ω => w (sh t ω) 2) (fun t ω => w (sh t ω) 3)
      (fun t ω => (1 - p.σ) * w (sh t ω) 0 + p.σ * (ε * ξ (sh t ω) 1) + ε * ξ (sh t ω) 2)
      (fun t ω => (1 + p.ω) * w (sh t ω) 0 - p.ω * (ε * ξ (sh t ω) 3) + ε * ξ (sh t ω) 4)
      (fun t ω => w (sh t ω) 0) (fun _ _ => 0) (fun t ω => ε * ξ (sh t ω) 1)
      (fun t ω => ε * ξ (sh t ω) 3) (fun t ω => ε * ξ (sh t ω) 4)
      (fun t ω => ε * ξ (sh t ω) 2) where
  priceIndex := by
    intro t ω
    have h := eqm_comp hw (sh t ω) 3
    simp only [Qmap, Nmap, Matrix.cons_val, mul_zero, Finset.sum_const_zero, add_zero] at h
    rw [mul_div_assoc] at h
    exact h
  resetPrice := by
    intro t ω
    have hc0 := hp.c0_pos.ne'
    change p.c0 * ((w (sh t ω) 3 - w (sh t ω) 2) / p.c0) = _
    field_simp
  recF := by
    intro t
    have hE := hM t (fun s' => Real.exp ((p.θ - 1) * w s' 1 + w s' 2) - 1)
    rw [hE]
    funext ω
    have hS1 : ∑ s', P (sh t ω) s' * Nmap p (ε • ξ s', w s') 1 =
        -(p.α * p.β) * ∑ s', P (sh t ω) s' * Real.exp ((p.θ - 1) * w s' 1 + w s' 2) := by
      simp only [Nmap, Matrix.cons_val]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hS2 : chainOp P (fun s' => Real.exp ((p.θ - 1) * w s' 1 + w s' 2) - 1) (sh t ω) =
        ∑ s', P (sh t ω) s' * Real.exp ((p.θ - 1) * w s' 1 + w s' 2) - 1 := by
      change ∑ s', P (sh t ω) s' * (Real.exp ((p.θ - 1) * w s' 1 + w s' 2) - 1) = _
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hP.2 (sh t ω)]
    have h := eqm_comp hw (sh t ω) 1
    rw [hS1] at h
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hS2]
    linear_combination h
  recK := by
    intro t
    have hE := hM t (fun s' => Real.exp (p.θ * (1 + p.ω) * w s' 1 + w s' 3) - 1)
    rw [hE]
    funext ω
    have hS1 : ∑ s', P (sh t ω) s' * Nmap p (ε • ξ s', w s') 2 =
        -(p.α * p.β) * ∑ s', P (sh t ω) s' * Real.exp (p.θ * (1 + p.ω) * w s' 1 + w s' 3) := by
      simp only [Nmap, Matrix.cons_val]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hS2 : chainOp P (fun s' => Real.exp (p.θ * (1 + p.ω) * w s' 1 + w s' 3) - 1) (sh t ω) =
        ∑ s', P (sh t ω) s' * Real.exp (p.θ * (1 + p.ω) * w s' 1 + w s' 3) - 1 := by
      change ∑ s', P (sh t ω) s' * (Real.exp (p.θ * (1 + p.ω) * w s' 1 + w s' 3) - 1) = _
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hP.2 (sh t ω)]
    have h := eqm_comp hw (sh t ω) 2
    rw [hS1] at h
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hS2]
    linear_combination h
  costK := fun t ω => by ring
  revF := fun t ω => by
    simp only [LargeDistortions.fhatIso, sub_self, sub_zero, div_one, Real.log_exp]
    ring

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) (**the Euler equation with the rule, exactly**): along the
chain, `E_t[e^{−σ(Ŷ_{t+1} − ĉ_{t+1}) − π_{t+1}}] = e^{−(φ_π π_t + φ_y Ŷ_t + ν_t + σ(Ŷ_t − ĉ_t))}`,
i.e. `u_c(t) = β(1 + i_t)E_t[u_c(t+1)/Π_{t+1}]` with `1 + i_t = β⁻¹Π_t^{φ_π}(Y_t/Ȳ)^{φ_y}e^{ν_t}`
and `u_c ∝ e^{−σ(Ŷ − ĉ)}`. -/
theorem euler_of_markov {Ω : Type*} (𝔼 : ExpectationSystem Ω) {P : S → S → ℝ}
    (ξ : S → Fin 5 → ℝ) (ε : ℝ) (w : S → Fin 4 → ℝ) (hw : IsMarkovEqm p (chainOp P) ξ ε w)
    (sh : ℕ → Ω → S) (hM : MarkovProp 𝔼 P sh) (t : ℕ) :
    𝔼.E t (fun ω => Real.exp (-(p.σ * (w (sh (t + 1) ω) 0 - ε * ξ (sh (t + 1) ω) 1)) -
        w (sh (t + 1) ω) 1)) =
      fun ω => Real.exp (-(p.φ * w (sh t ω) 1 + p.φy * w (sh t ω) 0 + ε * ξ (sh t ω) 0 +
        p.σ * (w (sh t ω) 0 - ε * ξ (sh t ω) 1))) := by
  have hE := hM t (fun s' => Real.exp (-(p.σ * (w s' 0 - ε * ξ s' 1)) - w s' 1))
  rw [hE]
  funext ω
  have h := eqm_comp hw (sh t ω) 0
  simp only [Qmap, Nmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul] at h
  simp only [chainOp, LinearMap.coe_mk, AddHom.coe_mk]
  linear_combination h

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) in levels (**the Euler equation with the interest-rate
rule**): with `Π = e^π`, `Y/Ȳ = e^ŷ`, the rule `1 + i = β⁻¹Π^{φ_π}(Y/Ȳ)^{φ_y}e^ν` and marginal
utility `u_c ∝ e^{−σ(ŷ − ĉ)}`, the household condition `u_c(t) = β(1+i_t)·X` (with
`X = E_t[u_c(t+1)/Π_{t+1}]` in the same normalisation) is EXACTLY the residual form used here,
`X = e^{−(φ_π π + φ_y ŷ + ν + σ(ŷ − ĉ))}`. -/
theorem euler_levels {β σ φ φy : ℝ} (hβ : β ≠ 0) (π y c ν X : ℝ) :
    Real.exp (-(σ * (y - c))) =
        β * (β⁻¹ * Real.exp π ^ φ * Real.exp y ^ φy * Real.exp ν) * X ↔
      X = Real.exp (-(φ * π + φy * y + ν + σ * (y - c))) := by
  rw [← Real.exp_mul, ← Real.exp_mul]
  have e : β * (β⁻¹ * Real.exp (π * φ) * Real.exp (y * φy) * Real.exp ν) =
      Real.exp (φ * π + φy * y + ν) := by
    rw [Real.exp_add, Real.exp_add]; field_simp
  rw [e]
  have hpos := Real.exp_pos (φ * π + φy * y + ν)
  constructor
  · intro h
    have h2 : X = Real.exp (-(σ * (y - c))) / Real.exp (φ * π + φy * y + ν) := by
      rw [h]; field_simp
    rw [h2, ← Real.exp_sub]
    ring_nf
  · intro h
    rw [h, ← Real.exp_add]
    ring_nf

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) (**the level Euler equation along the chain**): with the
rule `1 + i_t = β⁻¹(e^{π_t})^{φ_π}(e^{Ŷ_t})^{φ_y}e^{ν_t}`, a Markov equilibrium satisfies
`u_c(t) = β(1 + i_t)E_t[u_c(t+1)/Π_{t+1}]` at every date and state. -/
theorem euler_levels_markov (hp : p.Std) {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    {P : S → S → ℝ} (ξ : S → Fin 5 → ℝ) (ε : ℝ) (w : S → Fin 4 → ℝ)
    (hw : IsMarkovEqm p (chainOp P) ξ ε w) (sh : ℕ → Ω → S) (hM : MarkovProp 𝔼 P sh)
    (t : ℕ) (ω : Ω) :
    Real.exp (-(p.σ * (w (sh t ω) 0 - ε * ξ (sh t ω) 1))) =
      p.β * (p.β⁻¹ * Real.exp (w (sh t ω) 1) ^ p.φ * Real.exp (w (sh t ω) 0) ^ p.φy *
        Real.exp (ε * ξ (sh t ω) 0)) *
      𝔼.E t (fun ω => Real.exp (-(p.σ * (w (sh (t + 1) ω) 0 - ε * ξ (sh (t + 1) ω) 1))) *
        Real.exp (-w (sh (t + 1) ω) 1)) ω := by
  rw [euler_levels hp.β_pos.ne']
  have h := congrFun (euler_of_markov 𝔼 ξ ε w hw sh hM t) ω
  rw [← h]
  have e : (fun ω => Real.exp (-(p.σ * (w (sh (t + 1) ω) 0 - ε * ξ (sh (t + 1) ω) 1))) *
      Real.exp (-w (sh (t + 1) ω) 1)) = fun ω => Real.exp (-(p.σ * (w (sh (t + 1) ω) 0 -
        ε * ξ (sh (t + 1) ω) 1)) - w (sh (t + 1) ω) 1) := by
    funext ω'
    rw [← Real.exp_add]
    ring_nf
  rw [e]

/-! ### The dispersion state along the family -/

/-- Woodford (2003), Proposition 6.3 and p. 400 (**dispersion is second order, uniformly**): along
the family of Markov equilibria and ANY shock path, the exact dispersion
`Δ_t = dispLaw(Δ_{t−1}, z_ε(s_t))` satisfies `Δ_t − 1 = O(ε²)` uniformly in `(t, ω)` when the
initial dispersion does (`Δ_{−1} − 1 = O(ε²)`): the analogue, for the exact dispersion index, of
the hypothesis `D = O(ε²)` of `BridgeExtensions.prop615_layerB`. -/
theorem disp_uniform (hp : p.Std) {P : S → S → ℝ} {ξ : S → Fin 5 → ℝ}
    {z : ℝ → S → Fin 4 → ℝ} (hz0 : z 0 = 0) (hzC : ContDiffAt ℝ 2 z 0)
    (heq : ∀ᶠ ε in 𝓝 0, IsMarkovEqm p (chainOp P) ξ ε (z ε)) {Ω : Type*} (sh : ℕ → Ω → S)
    (D : ℝ → ℕ → Ω → ℝ) (hD : ∀ ε t ω, D ε (t + 1) ω = dispLaw p (D ε t ω) (z ε (sh t ω)))
    (hD0 : ∃ C0, ∀ᶠ ε in 𝓝 0, ∀ ω, |D ε 0 ω - 1| ≤ C0 * ε ^ 2) :
    BridgeExtensions.UProc (𝓝 0) (fun ε t ω => D ε t ω - 1) fun ε => ε ^ 2 := by
  obtain ⟨C0, hC0⟩ := hD0
  obtain ⟨C1, hC1⟩ := (family_order_one hz0 hzC).bound
  set a := p.θ * (1 + p.ω) with ha
  set b := p.θ - 1 with hb
  have hb0 : 0 < b := by rw [hb]; linarith [hp.one_lt_θ]
  have ha0 : 0 < a := by rw [ha]; nlinarith [hp.ω_nonneg, hp.one_lt_θ]
  have hc0 := hp.c0_pos
  set C2 := max C1 0 + 2 * max C1 0 / p.c0 with hC2
  have hC20 : 0 ≤ C2 := by positivity
  set q := (1 + p.α) / 2 with hq
  have hq1 : q < 1 := by rw [hq]; linarith [hp.α_lt_one]
  have hαq : p.α < q := by rw [hq]; linarith [hp.α_lt_one]
  set CD := a * (a + b) with hCD
  set K := 2 * CD * C2 ^ 2 / (1 - q) with hK
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - q := by linarith
    positivity
  -- smallness conditions on the amplitude
  have habs : Tendsto (fun ε : ℝ => |ε|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ))
  have ht1 : Tendsto (fun ε : ℝ => p.α * Real.exp (a * C2 * |ε|)) (𝓝 0) (𝓝 (p.α * 1)) := by
    have : Tendsto (fun ε : ℝ => a * C2 * |ε|) (𝓝 0) (𝓝 (a * C2 * 0)) := habs.const_mul (a * C2)
    simpa using (Real.continuous_exp.tendsto _ |>.comp this).const_mul p.α
  have hsm1 : ∀ᶠ ε : ℝ in 𝓝 0, p.α * Real.exp (a * C2 * |ε|) < q :=
    ht1.eventually (gt_mem_nhds (by simpa using hαq))
  have ht2 : Tendsto (fun ε : ℝ => C2 * |ε|) (𝓝 0) (𝓝 (C2 * 0)) := habs.const_mul C2
  have hsm2 : ∀ᶠ ε : ℝ in 𝓝 0, C2 * |ε| < 1 / a :=
    ht2.eventually (gt_mem_nhds (by simpa using (one_div_pos.2 ha0)))
  refine IsBigO.of_bound (max C0 0 + K) ?_
  have hev : ∀ᶠ ε in 𝓝 0, ∀ t ω, |D ε t ω - 1| ≤ (max C0 0 + K) * ε ^ 2 := by
    filter_upwards [heq, hC1, hC0, hsm1, hsm2] with ε hE hz hD0ε hs1 hs2
    have hzε : ‖z ε‖ ≤ max C1 0 * |ε| := by
      rw [Real.norm_eq_abs] at hz
      exact hz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    -- bounds at each state
    have hC1C2 : max C1 0 ≤ C2 := by
      rw [hC2]; have : 0 ≤ 2 * max C1 0 / p.c0 := by positivity
      linarith
    have hπs : ∀ s, |z ε s 1| ≤ C2 * |ε| := fun s => by
      have h1 := norm_le_pi_norm (z ε s) 1
      have h2 := norm_le_pi_norm (z ε) s
      rw [Real.norm_eq_abs] at h1
      calc |z ε s 1| ≤ ‖z ε‖ := h1.trans h2
        _ ≤ max C1 0 * |ε| := hzε
        _ ≤ C2 * |ε| := mul_le_mul_of_nonneg_right hC1C2 (abs_nonneg _)
    have hxs : ∀ s, |(z ε s 3 - z ε s 2) / p.c0| ≤ C2 * |ε| := fun s => by
      have h1 := norm_le_pi_norm (z ε s) 3
      have h2 := norm_le_pi_norm (z ε s) 2
      have h3 := norm_le_pi_norm (z ε) s
      rw [Real.norm_eq_abs] at h1 h2
      rw [abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
      have e : |z ε s 3 - z ε s 2| ≤ 2 * (max C1 0 * |ε|) := by
        have := abs_sub (z ε s 3) (z ε s 2); linarith
      have e2 : 2 * (max C1 0 * |ε|) ≤ C2 * |ε| * p.c0 := by
        rw [hC2, add_mul, add_mul]
        have : 2 * max C1 0 / p.c0 * |ε| * p.c0 = 2 * (max C1 0 * |ε|) := by
          field_simp
        rw [this]
        have : 0 ≤ max C1 0 * |ε| * p.c0 := by positivity
        linarith
      linarith
    have hstep : ∀ t ω, |D ε (t + 1) ω - 1| ≤ q * |D ε t ω - 1| + 2 * CD * C2 ^ 2 * ε ^ 2 := by
      intro t ω
      set w := z ε (sh t ω)
      have hPI := eqm_comp hE (sh t ω) 3
      simp only [Qmap, Nmap, Matrix.cons_val, mul_zero, Finset.sum_const_zero, add_zero] at hPI
      rw [mul_div_assoc] at hPI
      have hπa : |w 1| ≤ 1 / a := (hπs _).trans hs2.le
      have hxa : |(w 3 - w 2) / p.c0| ≤ 1 / a := (hxs _).trans hs2.le
      have h2 := disp_second_order hp (D ε t ω) w hPI hπa hxa
      rw [hD]
      have hexp : p.α * Real.exp (a * w 1) ≤ q := by
        have : Real.exp (a * w 1) ≤ Real.exp (a * C2 * |ε|) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_left ((le_abs_self (w 1)).trans (hπs (sh t ω))) ha0.le
          linarith [show a * (C2 * |ε|) = a * C2 * |ε| by ring]
        calc p.α * Real.exp (a * w 1) ≤ p.α * Real.exp (a * C2 * |ε|) :=
              mul_le_mul_of_nonneg_left this hp.α_pos.le
          _ ≤ q := hs1.le
      have hsq : w 1 ^ 2 + ((w 3 - w 2) / p.c0) ^ 2 ≤ 2 * C2 ^ 2 * ε ^ 2 := by
        have e1 : w 1 ^ 2 ≤ (C2 * |ε|) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hπs _) 2
        have e2 : ((w 3 - w 2) / p.c0) ^ 2 ≤ (C2 * |ε|) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hxs _) 2
        rw [mul_pow, sq_abs] at e1 e2
        linarith
      have hCD0 : 0 ≤ CD := by positivity
      have e3 := abs_sub_abs_le_abs_sub (dispLaw p (D ε t ω) w - 1)
        (p.α * Real.exp (a * w 1) * (D ε t ω - 1))
      have e4 : |p.α * Real.exp (a * w 1) * (D ε t ω - 1)| ≤ q * |D ε t ω - 1| := by
        rw [abs_mul, abs_of_pos (by have := hp.α_pos; positivity)]
        exact mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
      have e5 : |dispLaw p (D ε t ω) w - 1 - p.α * Real.exp (a * w 1) * (D ε t ω - 1)| ≤
          CD * (2 * C2 ^ 2 * ε ^ 2) := h2.trans (mul_le_mul_of_nonneg_left hsq hCD0)
      have : |dispLaw p (D ε t ω) w - 1| ≤ |p.α * Real.exp (a * w 1) * (D ε t ω - 1)| +
          |dispLaw p (D ε t ω) w - 1 - p.α * Real.exp (a * w 1) * (D ε t ω - 1)| := by
        have := abs_add_le (p.α * Real.exp (a * w 1) * (D ε t ω - 1))
          (dispLaw p (D ε t ω) w - 1 - p.α * Real.exp (a * w 1) * (D ε t ω - 1))
        simpa using this
      linarith
    intro t
    induction t with
    | zero =>
      intro ω
      have h := hD0ε ω
      have : C0 * ε ^ 2 ≤ (max C0 0 + K) * ε ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [le_max_left C0 0]) (sq_nonneg ε)
      linarith
    | succ t ih =>
      intro ω
      have h := hstep t ω
      have h1 := ih ω
      have hq0 : 0 ≤ q := by rw [hq]; linarith [hp.α_pos]
      have hKe : 2 * CD * C2 ^ 2 * ε ^ 2 = (1 - q) * (K * ε ^ 2) := by
        rw [hK]; have : 1 - q ≠ 0 := by linarith
        field_simp
      have hB : K * ε ^ 2 ≤ (max C0 0 + K) * ε ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [le_max_right C0 0]) (sq_nonneg ε)
      have e1 := mul_le_mul_of_nonneg_left h1 hq0
      have e2 := mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ 1 - q)
      linarith
  filter_upwards [hev.prod_inl ⊤] with x hx
  simpa [Real.norm_eq_abs] using hx x.2.1 x.2.2

/-! ### The family hypothesis of Layer B, discharged in one statement -/

/-- Woodford (2003), Ch. 6, §1 and §5 (**the Layer-B family hypothesis discharged for the exact NK
model with Calvo pricing and a Taylor rule**). Under the Taylor principle, for a finite Markov
chain and any disturbance pattern `ξ`, there are `δ > 0` and a `C²` family `ε ↦ z_ε` of Markov
equilibria (`z₀ = 0`, the steady state) such that, writing `z₁ = z′(0)`:
* for every `Ω`, every shock path `s_t(ω)` and every variable `i` (`ŷ, π, F̂, K̂`), the processes
  `z_ε(s_t)_i` are `O(ε)` and `z_ε(s_t)_i − εz₁(s_t)_i = O(ε²)` uniformly in `(t, ω)`
  (`BridgeExtensions.UProc`), with `z₁(s_t)_i` bounded;
* for every expectation system following the chain (`MarkovProp`) and every `|ε| < δ` the
  processes satisfy the exact Calvo model `CalvoAS` of §5;
* the exact dispersion `Δ_t = dispLaw(Δ_{t−1}, z_ε(s_t))` is `1 + O(ε²)` uniformly whenever the
  initial dispersion is. -/
theorem layerB_discharged (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 5 → ℝ) :
    ∃ δ > 0, ∃ z : ℝ → S → Fin 4 → ℝ, z 0 = 0 ∧ ContDiffAt ℝ 2 z 0 ∧
      (∀ ε, |ε| < δ → IsMarkovEqm p (chainOp P) ξ ε (z ε)) ∧
      (∀ (Ω : Type*) (sh : ℕ → Ω → S) (i : Fin 4),
        BridgeExtensions.UProc (𝓝 0) (proc z sh i) (fun ε => ε ^ 1) ∧
        BridgeExtensions.UProc (𝓝 0)
          (fun ε t ω => proc z sh i ε t ω - ε * deriv z 0 (sh t ω) i) (fun ε => ε ^ 2) ∧
        BoundedProc (fun t ω => deriv z 0 (sh t ω) i)) ∧
      (∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (sh : ℕ → Ω → S), MarkovProp 𝔼 P sh →
        ∀ ε, |ε| < δ → LargeDistortions.CalvoModel.CalvoAS 𝔼 p.α p.β p.θ p.ω p.σ 1
          (fun t ω => z ε (sh t ω) 1) (fun t ω => (z ε (sh t ω) 3 - z ε (sh t ω) 2) / p.c0)
          (fun t ω => z ε (sh t ω) 2) (fun t ω => z ε (sh t ω) 3)
          (fun t ω => (1 - p.σ) * z ε (sh t ω) 0 + p.σ * (ε * ξ (sh t ω) 1) + ε * ξ (sh t ω) 2)
          (fun t ω => (1 + p.ω) * z ε (sh t ω) 0 - p.ω * (ε * ξ (sh t ω) 3) +
            ε * ξ (sh t ω) 4)
          (fun t ω => z ε (sh t ω) 0) (fun _ _ => 0) (fun t ω => ε * ξ (sh t ω) 1)
          (fun t ω => ε * ξ (sh t ω) 3) (fun t ω => ε * ξ (sh t ω) 4)
          (fun t ω => ε * ξ (sh t ω) 2)) ∧
      (∀ (Ω : Type*) (sh : ℕ → Ω → S) (D : ℝ → ℕ → Ω → ℝ),
        (∀ ε t ω, D ε (t + 1) ω = dispLaw p (D ε t ω) (z ε (sh t ω))) →
        (∃ C0, ∀ᶠ ε in 𝓝 0, ∀ ω, |D ε 0 ω - 1| ≤ C0 * ε ^ 2) →
        BridgeExtensions.UProc (𝓝 0) (fun ε t ω => D ε t ω - 1) fun ε => ε ^ 2) := by
  obtain ⟨_, _, δ, hδ, z, hz0, hzC, hz, -⟩ := markov_equilibrium hp hP ξ
  have heq : ∀ᶠ ε in 𝓝 (0 : ℝ), IsMarkovEqm p (chainOp P) ξ ε (z ε) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with ε hε
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hε
    exact (hz ε hε).1
  refine ⟨δ, hδ, z, hz0, hzC, fun ε hε => (hz ε hε).1, fun Ω sh i =>
    ⟨uproc_order_one hz0 hzC sh i, uproc_first_order hz0 hzC sh i,
      ⟨_, bounded_first (deriv z 0) sh i⟩⟩,
    fun Ω 𝔼 sh hM ε hε => calvoAS_of_markov hp 𝔼 hP ξ ε (z ε) (hz ε hε).1 sh hM,
    fun Ω sh D hD hD0 => disp_uniform hp hz0 hzC heq sh D hD hD0⟩

end Woodford.StabilizationWelfare.NonlinearNKMarkovLinks
