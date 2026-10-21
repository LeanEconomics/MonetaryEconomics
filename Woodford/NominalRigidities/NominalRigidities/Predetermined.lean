/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Expectations
import NominalRigidities.ExpectationsFiniteTree
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Convex.Deriv

/-!
# Prices fixed one period in advance and the New Classical Phillips curve

Woodford (2003), *Interest and Prices*, Chapter 3, §1.1 (pp. 153–155), §1.2 "Consequences of
prices fixed in advance" (pp. 155–158) and §1.3 "A New Classical Phillips curve"
(pp. 158–163), including Figure 3.1 (p. 161).

Every expectational statement is made for an arbitrary `ExpectationSystem`, with `E_t` playing
the role of the book's `E_{t−1}` for prices of date `t + 1` (so `E_{t−1}` is a genuine conditional
expectation, idempotent by the tower property). Log-linear relations are linked to the nonlinear
objects by exact derivatives at the steady state.

## Main results

* `implicit_function_scalar`, `implicit_function_real`: the implicit function theorem for a
  scalar equation `f(v, x) = 0` with strict derivative (proved from Mathlib's
  `implicitFunctionOfProdDomain`); used for the natural rate (1.21) and the notional SRAS.
* `deriv_homogeneous_degree_zero`: if `Π` is homogeneous of degree one (Assumption 3.1) then
  `Π₁` is homogeneous of degree zero (p. 154); `expected_foc_symmetric_eq` gives (1.24).
* `hasDerivAt_baselineProfit`: the formula for `Π₁` in the baseline model (p. 164);
  `expected_foc_baseline_iff`: (1.24) takes the form (1.25).
* `asResidual_scale`, `priceLevel_homogeneous`: (1.26) makes `P_t` homogeneous of degree one in
  the distribution of nominal spending (p. 157).
* `foc_1_23_necessary` (finite state spaces: `foc_1_23_tree`, `foc_1_23_perfectForesight`) and
  `foc_1_23_sufficient` (any `ExpectationSystem`, concave profits): (1.22) ⇒ (1.23) and back.
* `asRoot_existsUnique`, `priceLevel_existsUnique_tree`, `priceLevel_homogeneous_tree`: (1.26)
  has a unique predetermined solution on every finite event tree, and homogeneity follows with
  uniqueness derived; `priceLevel_not_unique_counterexample`,
  `priceLevel_not_exists_counterexample`: the hypotheses cannot be dropped.
* `natural_rate_exists`, `linearisation_gap_form`: the natural rate exists and (1.27)
  `Π₁ ≈ ψ_y (Ŷ − Ŷⁿ)` is the exact first derivative; `linearised_foc_form` gives (1.30).
* `psi_p_not_negative_counterexample`: Assumption 3.1 does NOT imply `ψ_p < 0` (p. 158).
* `hasDerivAt_E_foc_product`: the first-order expansion of `E_t[Q Π₁]` around a point where
  `Π₁ = 0` is `Q̄ E_t[dΠ₁]` (the discount factor drops out).
* `predetermined_price_level`, `predetermined_output`, `forecastable_output`,
  `output_surprise` (pp. 157–158).
* `hasFDerivAt_log_ces_two`: log-linear CES price index `log P = ι log p₁ + (1 − ι) log p₂`.
* `prop_3_2` (Proposition 3.2, (1.32)), `expected_gap_zero`, `output_corrected` and
  `price_level_corrected` (corrected (1.33) and price-level formula), `printed_1_33_iff`,
  `printed_price_level_iff`, `printed_1_33_counterexample` (survey error E1, confirmed).
* Figure 3.1: `fig31_closed_form`, `fig31_strictAntiOn`, `fig31_strictConvexOn`,
  `fig31_strictConcaveOn`, `fig31_linear`, `fig31_antitone_zeta`, `kappaNC_tendsto_atTop`,
  `outputElasticity_tendsto_zero`.
-/

namespace Woodford.NominalRigidities.Predetermined

open Filter Topology

/-! ### The implicit function theorem for one scalar equation -/

/-- Implicit function theorem (used for Woodford (2003), (1.21) p. 154 and (1.34) p. 162): if
`f : E × ℝ → ℝ` has strict derivative `L` at `u` and `L (0, 1) ≠ 0`, then near `u` the
equation `f(v, x) = f(u)` is solved by a unique `x = n(v)`, with `n(u.1) = u.2` and strict
derivative `−L(0,1)⁻¹ • L(·, 0)`. Proved from Mathlib's `implicitFunctionOfProdDomain`. -/
theorem implicit_function_scalar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : E × ℝ → ℝ} {L : E × ℝ →L[ℝ] ℝ} {u : E × ℝ}
    (hf : HasStrictFDerivAt f L u) (hc : L (0, 1) ≠ 0) :
    ∃ n : E → ℝ, n u.1 = u.2 ∧ (∀ᶠ x in 𝓝 u.1, f (x, n x) = f u) ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ n v.1 = v.2) ∧
      HasStrictFDerivAt n (-(L (0, 1))⁻¹ • (L ∘L ContinuousLinearMap.inl ℝ E ℝ)) u.1 := by
  set e : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ _ hc).toContinuousLinearEquiv
  have he : (e : ℝ →L[ℝ] ℝ) = L ∘L ContinuousLinearMap.inr ℝ E ℝ := by
    ext; simp [e]
  have hinv : (L ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := ⟨e, he⟩
  refine ⟨hf.implicitFunctionOfProdDomain hinv,
    eq_of_tendsto_nhds (hf.tendsto_implicitFunctionOfProdDomain hinv),
    hf.eventually_apply_implicitFunctionOfProdDomain hinv,
    hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv, ?_⟩
  convert hf.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv using 1
  rw [← he, ContinuousLinearMap.inverse_equiv]
  ext x
  simp [e, Units.smul_def]

/-- Implicit function theorem, one parameter (Woodford (2003), (1.21) p. 154): if
`f : ℝ × ℝ → ℝ` has strict derivative `L` at `u` with `L (0, 1) ≠ 0`, the local solution
`x = n(v)` of `f(v, x) = f(u)` exists, is locally unique, and `n'(u.1) = −L(1,0)/L(0,1)`. -/
theorem implicit_function_real {f : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {u : ℝ × ℝ}
    (hf : HasStrictFDerivAt f L u) (hc : L (0, 1) ≠ 0) :
    ∃ n : ℝ → ℝ, n u.1 = u.2 ∧ (∀ᶠ x in 𝓝 u.1, f (x, n x) = f u) ∧
      (∀ᶠ v in 𝓝 u, f v = f u ↔ n v.1 = v.2) ∧
      HasStrictDerivAt n (-(L (1, 0)) / L (0, 1)) u.1 := by
  obtain ⟨n, h1, h2, h3, h4⟩ := implicit_function_scalar hf hc
  refine ⟨n, h1, h2, h3, ?_⟩
  rw [hasStrictDerivAt_iff_hasStrictFDerivAt]
  convert h4 using 1
  ext
  simp [div_eq_inv_mul]

/-! ### Assumption 3.1: homogeneity of the profit function -/

/-- Woodford (2003), p. 154 (consequence of Assumption 3.1, p. 153): if the profit function
`Π(p, p^I, P; ·)` is homogeneous of degree one in its three price arguments, its partial
derivative `Π₁` in the own price is homogeneous of degree zero. `X` collects `(Y, ξ̃)`. -/
theorem deriv_homogeneous_degree_zero {X : Type*} {Pi Pi1 : ℝ → ℝ → ℝ → X → ℝ}
    (hhom : ∀ c : ℝ, 0 < c → ∀ p q P x, Pi (c * p) (c * q) (c * P) x = c * Pi p q P x)
    (hd : ∀ p q P x, HasDerivAt (fun r => Pi r q P x) (Pi1 p q P x) p)
    {c : ℝ} (hc : 0 < c) (p q P : ℝ) (x : X) :
    Pi1 (c * p) (c * q) (c * P) x = Pi1 p q P x := by
  have h1 : HasDerivAt (fun r => Pi (c * r) (c * q) (c * P) x)
      (Pi1 (c * p) (c * q) (c * P) x * c) p := by
    have := (hd (c * p) (c * q) (c * P) x).comp p ((hasDerivAt_id p).const_mul c)
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun r => Pi (c * r) (c * q) (c * P) x) (c * Pi1 p q P x) p := by
    have := (hd p q P x).const_mul c
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun r => hhom c hc r q P x)
  have := h1.unique h2
  have hc0 : c ≠ 0 := hc.ne'
  field_simp at this
  linarith

/-- Woodford (2003), p. 158: by homogeneity, `Π₁(p, p^I, P)` depends only on relative prices:
`Π₁(p, q, P) = Π₁(p/P, q/P, 1)` for `P > 0`. -/
theorem foc_relative_price_form {X : Type*} {Pi1 : ℝ → ℝ → ℝ → X → ℝ}
    (h0 : ∀ c : ℝ, 0 < c → ∀ p q P x, Pi1 (c * p) (c * q) (c * P) x = Pi1 p q P x)
    {P : ℝ} (hP : 0 < P) (p q : ℝ) (x : X) :
    Pi1 p q P x = Pi1 (p / P) (q / P) 1 x := by
  have := h0 P hP (p / P) (q / P) 1 x
  rw [← this]
  congr 1 <;> field_simp

/-- Woodford (2003), eq. (1.24), p. 156: in a symmetric equilibrium with prices set at `t` for
date `t + 1`, `E_t[Q Π₁(P, P, P; Y, ξ̃)] = E_t[Q Π₁(1, 1, 1; Y, ξ̃)]`, so the first-order
condition involves no nominal variable. -/
theorem expected_foc_symmetric_eq {Ω X : Type*} (𝔼 : ExpectationSystem Ω)
    {Pi1 : ℝ → ℝ → ℝ → X → ℝ}
    (h0 : ∀ c : ℝ, 0 < c → ∀ p q P x, Pi1 (c * p) (c * q) (c * P) x = Pi1 p q P x)
    (t : ℕ) (Q P : Ω → ℝ) (hP : ∀ ω, 0 < P ω) (x : Ω → X) :
    𝔼.E t (fun ω => Q ω * Pi1 (P ω) (P ω) (P ω) (x ω)) =
      𝔼.E t (fun ω => Q ω * Pi1 1 1 1 (x ω)) := by
  congr 1
  funext ω
  have := h0 (P ω) (hP ω) 1 1 1 (x ω)
  simp only [mul_one] at this
  rw [this]

/-! ### The baseline profit function (1.18) -/

/-- Woodford (2003), eq. (1.18), p. 153 (with the wage bill written through the real total cost
`Γ` of producing `y` units, whose derivative is real marginal cost `s`): nominal profit
`p Y (p/P)^{−θ} − P Γ(Y (p/P)^{−θ})` of the supplier charging `p`. -/
noncomputable def baselineProfit (θ Y P : ℝ) (Γ : ℝ → ℝ) (p : ℝ) : ℝ :=
  p * (Y * (p / P) ^ (-θ)) - P * Γ (Y * (p / P) ^ (-θ))

/-- Woodford (2003), p. 164: in the baseline model
`Π₁(p) = −(θ − 1) Y (p/P)^{−θ−1} [p/P − µ s(Y (p/P)^{−θ})]`, `µ = θ/(θ − 1)`, where `s` is real
marginal cost (`Γ' = s`). -/
theorem hasDerivAt_baselineProfit {θ Y P p : ℝ} (hθ : 1 < θ) (hP : 0 < P) (hp : 0 < p)
    {Γ s : ℝ → ℝ} (hΓ : ∀ y, HasDerivAt Γ (s y) y) :
    HasDerivAt (baselineProfit θ Y P Γ)
      (-(θ - 1) * Y * (p / P) ^ (-θ - 1) *
        (p / P - θ / (θ - 1) * s (Y * (p / P) ^ (-θ)))) p := by
  have hr : 0 < p / P := div_pos hp hP
  have hD : HasDerivAt (fun r => Y * (r / P) ^ (-θ))
      (Y * ((1 / P) * (-θ) * (p / P) ^ (-θ - 1))) p := by
    have h1 : HasDerivAt (fun r => r / P) (1 / P) p := by
      simpa using (hasDerivAt_id p).div_const P
    exact (h1.rpow_const (Or.inl hr.ne')).const_mul Y
  have hprod := ((hasDerivAt_id p).mul hD)
  have hcost := ((hΓ (Y * (p / P) ^ (-θ))).comp p hD).const_mul P
  have := hprod.sub hcost
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hsplit : (p / P) ^ (-θ) = (p / P) * (p / P) ^ (-θ - 1) := by
    rw [show -θ = 1 + (-θ - 1) by ring, Real.rpow_add hr, Real.rpow_one]
    ring_nf
  unfold baselineProfit
  convert this using 1
  · funext r
    simp
  · rw [hsplit]
    simp only [id]
    field_simp
    ring

/-- Woodford (2003), p. 164 at a symmetric point: `Π₁(P, P, P) = Y (θ s(Y) − (θ − 1))`, i.e.
`−θ Y (µ⁻¹ − s(Y))` with `µ⁻¹ = (θ − 1)/θ`. -/
theorem baselineProfit_foc_symmetric {θ Y P : ℝ} (hθ : 1 < θ) (hP : 0 < P)
    {Γ s : ℝ → ℝ} (hΓ : ∀ y, HasDerivAt Γ (s y) y) :
    HasDerivAt (baselineProfit θ Y P Γ) (-θ * (Y * ((θ - 1) / θ - s Y))) P := by
  convert hasDerivAt_baselineProfit hθ hP hP hΓ using 1
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hθ0 : θ ≠ 0 := by linarith
  simp only [div_self hP.ne', Real.one_rpow, mul_one]
  field_simp

/-- Woodford (2003), eq. (1.25), p. 156: with the stochastic discount factor
`Q_{t,t+1} = c · u_c(Y_{t+1})`, where `c = β P_t/(u_c(Y_t) P_{t+1})` is known at `t` and nonzero
(`P_{t+1}` is predetermined), the condition `E_t[Q Π₁(1,1,1; Y, ξ̃)] = 0` with the baseline
`Π₁ = −θ Y (µ⁻¹ − s)` is equivalent to `E_t[u_c Y (µ⁻¹ − s(Y, Y; ξ̃))] = 0`. -/
theorem expected_foc_baseline_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    {θ μinv : ℝ} (hθ : θ ≠ 0) (t : ℕ) {c uc Y s : Ω → ℝ} (hc : 𝔼.E t c = c) (hc0 : ∀ ω, c ω ≠ 0) :
    𝔼.E t (fun ω => c ω * uc ω * (-θ * (Y ω * (μinv - s ω)))) = 0 ↔
      𝔼.E t (fun ω => uc ω * Y ω * (μinv - s ω)) = 0 := by
  have key : (fun ω => c ω * uc ω * (-θ * (Y ω * (μinv - s ω)))) =
      c * ((-θ) • fun ω => uc ω * Y ω * (μinv - s ω)) := by
    funext ω; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [key, hpo t _ _ hc, map_smul]
  constructor
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have h1 := (mul_eq_zero.mp this).resolve_left (hc0 ω)
    exact (mul_eq_zero.mp h1).resolve_left (neg_ne_zero.mpr hθ)
  · intro h
    rw [h]
    simp

/-! ### (1.26): homogeneity of the price level in nominal spending -/

/-- Woodford (2003), eq. (1.26), p. 156: the residual
`E_t[g(𝒴_{t+1}/P_{t+1})]` of the aggregate-supply condition, where
`g ω y = u_c(y; ξ) y (µ⁻¹ − s(y, y; ξ̃))` in the baseline model (any `g` is allowed). -/
noncomputable def asResidual {Ω : Type*} (𝔼 : ExpectationSystem Ω) (g : Ω → ℝ → ℝ) (t : ℕ)
    (N P : Ω → ℝ) : Ω → ℝ :=
  𝔼.E t (fun ω => g ω (N ω / P ω))

/-- Woodford (2003), p. 157: scaling nominal spending and the price level by the same nonzero
factor leaves the residual of (1.26) unchanged. -/
theorem asResidual_scale {Ω : Type*} (𝔼 : ExpectationSystem Ω) (g : Ω → ℝ → ℝ) (t : ℕ)
    (N P c : Ω → ℝ) (hc : ∀ ω, c ω ≠ 0) :
    asResidual 𝔼 g t (c * N) (c * P) = asResidual 𝔼 g t N P := by
  unfold asResidual
  congr 1
  funext ω
  simp only [Pi.mul_apply, mul_div_mul_left _ _ (hc ω)]

/-- Woodford (2003), (1.26), p. 156: `P` is an equilibrium price level for nominal spending
`N`: positive, predetermined (known at `t`) and solving (1.26). -/
def SolvesAS {Ω : Type*} (𝔼 : ExpectationSystem Ω) (g : Ω → ℝ → ℝ) (t : ℕ)
    (N P : Ω → ℝ) : Prop :=
  (∀ ω, 0 < P ω) ∧ 𝔼.E t P = P ∧ asResidual 𝔼 g t N P = 0

/-- Woodford (2003), p. 157: the price level determined by (1.26) is homogeneous of degree one
in the distribution of nominal spending: if `P₀` solves (1.26) for `N` and the solution for
`c N` (with `c > 0` known at `t`) is unique, that solution is `c P₀`. -/
theorem priceLevel_homogeneous {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut)
    (g : Ω → ℝ → ℝ) (t : ℕ) {N P₀ P₁ c : Ω → ℝ} (h0 : SolvesAS 𝔼 g t N P₀)
    (hc : ∀ ω, 0 < c ω) (hck : 𝔼.E t c = c)
    (huniq : ∀ P', SolvesAS 𝔼 g t (c * N) P' → P' = P₁) :
    P₁ = c * P₀ := by
  symm
  apply huniq
  refine ⟨fun ω => mul_pos (hc ω) (h0.1 ω), ?_, ?_⟩
  · rw [hpo t c P₀ hck, h0.2.1]
  · rw [asResidual_scale 𝔼 g t N P₀ c fun ω => (hc ω).ne']
    exact h0.2.2

/-- Woodford (2003), p. 157: output `Y = 𝒴/P` depends only on nominal spending relative to the
price level, so it is unchanged when both are scaled by the same nonzero factor. -/
theorem output_scale_invariant {Ω : Type*} (N P c : Ω → ℝ) (hc : ∀ ω, c ω ≠ 0) :
    (fun ω => (c * N) ω / (c * P) ω) = fun ω => N ω / P ω := by
  funext ω
  simp only [Pi.mul_apply, mul_div_mul_left _ _ (hc ω)]

/-! ### (1.26): existence and uniqueness of the price level -/

/-- Strict monotonicity of `E_t` on a finite state space (used for (1.26), p. 156): if `x < y`
in every state then `E_t x < E_t y`. -/
theorem E_lt_of_lt_finite {Ω : Type*} [Finite Ω] (𝔼 : ExpectationSystem Ω) (t : ℕ)
    {x y : Ω → ℝ} (h : ∀ ω, x ω < y ω) (ω₀ : Ω) : 𝔼.E t x ω₀ < 𝔼.E t y ω₀ := by
  have := Fintype.ofFinite Ω
  obtain ⟨ω₁, -, hmin⟩ := Finset.univ.exists_min_image (fun ω => y ω - x ω)
    ⟨ω₀, Finset.mem_univ _⟩
  have hε : 0 < y ω₁ - x ω₁ := by linarith [h ω₁]
  have hle : (fun _ => y ω₁ - x ω₁) ≤ y - x := fun ω => hmin ω (Finset.mem_univ ω)
  have := 𝔼.mono t hle ω₀
  rw [𝔼.const, map_sub] at this
  simp only [Pi.sub_apply] at this
  linarith

/-- Woodford (2003), (1.26), p. 156: the residual as a function of a candidate price level `r`
in the date-`t` state `ω₀`, `F(r) = E_t[g(𝒴/r)](ω₀)`. -/
noncomputable def asResidualAt {Ω : Type*} (𝔼 : ExpectationSystem Ω) (g : Ω → ℝ → ℝ) (t : ℕ)
    (N : Ω → ℝ) (ω₀ : Ω) (r : ℝ) : ℝ :=
  𝔼.E t (fun ω => g ω (N ω / r)) ω₀

/-- Woodford (2003), eq. (1.26), p. 156 ("P_t is implicitly defined"), on any finite state space:
if nominal spending is positive and, in every state, `g(·)` (in the baseline
`g(y) = u_c(y) y (µ⁻¹ − s(y, y))`) is continuous and strictly decreasing on `(0, ∞)`, positive at
some output `y_lo` and negative at some `y_hi`, then (1.26) has exactly one positive root `r`. -/
theorem asRoot_existsUnique {Ω : Type*} [Finite Ω] (𝔼 : ExpectationSystem Ω)
    {g : Ω → ℝ → ℝ} (t : ℕ) {N : Ω → ℝ} (ω₀ : Ω) (hN : ∀ ω, 0 < N ω)
    (hanti : ∀ ω, StrictAntiOn (g ω) (Set.Ioi 0)) (hcont : ∀ ω, ContinuousOn (g ω) (Set.Ioi 0))
    {ylo yhi : ℝ} (hylo : 0 < ylo) (hyhi : 0 < yhi) (hglo : ∀ ω, 0 < g ω ylo)
    (hghi : ∀ ω, g ω yhi < 0) :
    ∃! r, 0 < r ∧ asResidualAt 𝔼 g t N ω₀ r = 0 := by
  have := Fintype.ofFinite Ω
  set F := asResidualAt 𝔼 g t N ω₀ with hF
  have hmono : StrictMonoOn F (Set.Ioi 0) := by
    intro r₁ h₁ r₂ h₂ h12
    simp only [Set.mem_Ioi] at h₁ h₂
    apply E_lt_of_lt_finite
    intro ω
    apply hanti ω (Set.mem_Ioi.mpr (div_pos (hN ω) h₂)) (Set.mem_Ioi.mpr (div_pos (hN ω) h₁))
    exact div_lt_div_of_pos_left (hN ω) h₁ h12
  have hcontF : ContinuousOn F (Set.Ioi 0) := by
    have hin : ContinuousOn (fun r : ℝ => fun ω => g ω (N ω / r)) (Set.Ioi 0) := by
      refine continuousOn_pi.mpr fun ω => ?_
      refine (hcont ω).comp (continuousOn_const.div continuousOn_id fun r hr => ?_) ?_
      · exact (Set.mem_Ioi.mp hr).ne'
      · intro r hr
        exact Set.mem_Ioi.mpr (div_pos (hN ω) hr)
    have hL := (LinearMap.toContinuousLinearMap (𝔼.E t)).continuous.comp_continuousOn hin
    exact (continuous_apply ω₀).comp_continuousOn hL
  set Ssum := ∑ ω, N ω
  have hS : ∀ ω, N ω ≤ Ssum := fun ω =>
    Finset.single_le_sum (fun ω _ => (hN ω).le) (Finset.mem_univ ω)
  have hSpos : 0 < Ssum := lt_of_lt_of_le (hN ω₀) (hS ω₀)
  obtain ⟨ω₁, -, hmin⟩ := Finset.univ.exists_min_image N ⟨ω₀, Finset.mem_univ _⟩
  set rb := Ssum / ylo
  set rs := N ω₁ / yhi
  have hrb : 0 < rb := div_pos hSpos hylo
  have hrs : 0 < rs := div_pos (hN ω₁) hyhi
  have hFb : 0 < F rb := by
    have h0 : 𝔼.E t (fun _ => (0 : ℝ)) ω₀ = 0 := by rw [𝔼.const]
    rw [← h0]
    apply E_lt_of_lt_finite
    intro ω
    have hle : N ω / rb ≤ ylo := by
      simp only [rb]
      rw [div_div_eq_mul_div, div_le_iff₀ hSpos]
      nlinarith [hS ω]
    have := (hanti ω).antitoneOn (Set.mem_Ioi.mpr (div_pos (hN ω) hrb))
      (Set.mem_Ioi.mpr hylo) hle
    linarith [hglo ω]
  have hFs : F rs < 0 := by
    have h0 : 𝔼.E t (fun _ => (0 : ℝ)) ω₀ = 0 := by rw [𝔼.const]
    rw [← h0]
    apply E_lt_of_lt_finite
    intro ω
    have hle : yhi ≤ N ω / rs := by
      simp only [rs]
      rw [div_div_eq_mul_div, le_div_iff₀ (hN ω₁)]
      nlinarith [hmin ω (Finset.mem_univ ω)]
    have := (hanti ω).antitoneOn (Set.mem_Ioi.mpr hyhi)
      (Set.mem_Ioi.mpr (div_pos (hN ω) hrs)) hle
    linarith [hghi ω]
  have hlt : rs < rb := by
    by_contra h
    push Not at h
    have := hmono.monotoneOn (Set.mem_Ioi.mpr hrb) (Set.mem_Ioi.mpr hrs) h
    linarith
  have hsub : Set.Icc rs rb ⊆ Set.Ioi 0 := fun r hr => lt_of_lt_of_le hrs hr.1
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hlt.le (hcontF.mono hsub) ⟨hFs.le, hFb.le⟩
  refine ⟨r, ⟨hsub hr, hr0⟩, fun r' hr' => ?_⟩
  exact hmono.injOn hr'.1 (hsub hr) (hr'.2.trans hr0.symm)

/-- On a finite event tree, `E_t x` at `ω` depends only on the values of `x` on the date-`t`
information cell of `ω` (used for (1.26), p. 156). -/
theorem tree_condE_congr_on_cell {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) {t : ℕ} {x y : Ω → ℝ} {ω : Ω}
    (h : ∀ ω', T.info t ω' ω → x ω' = y ω') : T.condE t x ω = T.condE t y ω := by
  classical
  unfold ExpectationsFiniteTree.FiniteTree.condE ExpectationsFiniteTree.FiniteTree.num
  congr 1
  refine Finset.sum_congr rfl fun ω' _ => ?_
  by_cases hω : T.info t ω' ω
  · simp only [hω, ↓reduceIte, h ω' hω]
  · simp only [hω, ↓reduceIte]

/-- On a finite event tree, a variable known at `t` (`E_t P = P`) is constant on date-`t`
information cells (used for (1.26), p. 156). -/
theorem tree_known_const_on_cell {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) {t : ℕ} {P : Ω → ℝ}
    (hP : T.toExpectationSystem.E t P = P) {ω ω' : Ω} (h : T.info t ω' ω) : P ω' = P ω := by
  have h1 := congrFun hP ω'
  have h2 := congrFun hP ω
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at h1 h2
  rw [← h1, ← h2, T.condE_congr P h]

/-- Woodford (2003), eq. (1.26), p. 156, on every finite event tree: under the hypotheses of
`asRoot_existsUnique`, there is exactly one equilibrium price level — a positive process,
predetermined (known at `t`), solving (1.26). -/
theorem priceLevel_existsUnique_tree {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) {g : Ω → ℝ → ℝ} (t : ℕ) {N : Ω → ℝ}
    (hN : ∀ ω, 0 < N ω) (hanti : ∀ ω, StrictAntiOn (g ω) (Set.Ioi 0))
    (hcont : ∀ ω, ContinuousOn (g ω) (Set.Ioi 0)) {ylo yhi : ℝ} (hylo : 0 < ylo)
    (hyhi : 0 < yhi) (hglo : ∀ ω, 0 < g ω ylo) (hghi : ∀ ω, g ω yhi < 0) :
    ∃! P, SolvesAS T.toExpectationSystem g t N P := by
  set 𝔼 := T.toExpectationSystem
  have hroot := fun ω₀ => asRoot_existsUnique 𝔼 t ω₀ hN hanti hcont hylo hyhi hglo hghi
  -- the residual is the same function of `r` throughout an information cell
  have hcell : ∀ ω₀ ω', T.info t ω' ω₀ → asResidualAt 𝔼 g t N ω' = asResidualAt 𝔼 g t N ω₀ :=
    fun ω₀ ω' h => funext fun r => T.condE_congr _ h
  -- a predetermined `P` solves (1.26) iff `P ω₀` is the scalar root in every state
  have hred : ∀ P : Ω → ℝ, 𝔼.E t P = P → ∀ ω₀,
      asResidual 𝔼 g t N P ω₀ = asResidualAt 𝔼 g t N ω₀ (P ω₀) := by
    intro P hP ω₀
    unfold asResidual asResidualAt
    exact tree_condE_congr_on_cell T fun ω' h => by rw [tree_known_const_on_cell T hP h]
  set P : Ω → ℝ := fun ω₀ => (hroot ω₀).exists.choose
  have hPspec : ∀ ω₀, 0 < P ω₀ ∧ asResidualAt 𝔼 g t N ω₀ (P ω₀) = 0 :=
    fun ω₀ => (hroot ω₀).exists.choose_spec
  have hPcell : ∀ ω₀ ω', T.info t ω' ω₀ → P ω' = P ω₀ := by
    intro ω₀ ω' h
    apply (hroot ω₀).unique _ (hPspec ω₀)
    exact ⟨(hPspec ω').1, by rw [← hcell ω₀ ω' h]; exact (hPspec ω').2⟩
  have hPknown : 𝔼.E t P = P := by
    funext ω
    exact T.condE_of_const_on_cell fun ω' h => hPcell ω ω' h
  refine ⟨P, ⟨fun ω => (hPspec ω).1, hPknown, funext fun ω₀ => ?_⟩, fun P' hP' => ?_⟩
  · rw [hred P hPknown]; exact (hPspec ω₀).2
  · funext ω₀
    apply (hroot ω₀).unique ⟨hP'.1 ω₀, _⟩ (hPspec ω₀)
    rw [← hred P' hP'.2.1]
    exact congrFun hP'.2.2 ω₀

/-- Woodford (2003), p. 157, homogeneity of degree one of the price level, on every finite event
tree, with uniqueness DERIVED (not assumed): if `P₀` solves (1.26) for `N` and `c > 0` is known at
`t`, the unique solution for nominal spending `c N` is `c P₀`. -/
theorem priceLevel_homogeneous_tree {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) {g : Ω → ℝ → ℝ} (t : ℕ) {N P₀ c : Ω → ℝ}
    (hN : ∀ ω, 0 < N ω) (hanti : ∀ ω, StrictAntiOn (g ω) (Set.Ioi 0))
    (hcont : ∀ ω, ContinuousOn (g ω) (Set.Ioi 0)) {ylo yhi : ℝ} (hylo : 0 < ylo)
    (hyhi : 0 < yhi) (hglo : ∀ ω, 0 < g ω ylo) (hghi : ∀ ω, g ω yhi < 0)
    (h0 : SolvesAS T.toExpectationSystem g t N P₀) (hc : ∀ ω, 0 < c ω)
    (hck : T.toExpectationSystem.E t c = c) :
    SolvesAS T.toExpectationSystem g t (c * N) (c * P₀) ∧
      ∀ P₁, SolvesAS T.toExpectationSystem g t (c * N) P₁ → P₁ = c * P₀ := by
  obtain ⟨P₁, hP₁, huniq⟩ := priceLevel_existsUnique_tree T t
    (fun ω => mul_pos (hc ω) (hN ω)) hanti hcont hylo hyhi hglo hghi
  have hpo := ExpectationsFiniteTree.finiteTree_pullOut T
  have h := priceLevel_homogeneous T.toExpectationSystem hpo g t h0 hc hck huniq
  subst h
  exact ⟨hP₁, huniq⟩

/-- Woodford (2003), (1.26), p. 156 ("implicitly defined"), CORRECTION: without monotonicity of
`g` the price level need not be unique. Under perfect foresight, `g(y) = (y − 1)(y − 2)` and
nominal spending `2`, both `P = 1` and `P = 2` solve (1.26). -/
theorem priceLevel_not_unique_counterexample :
    SolvesAS perfectForesight (fun _ y => (y - 1) * (y - 2)) 0 (fun _ => 2) (fun _ => 1) ∧
      SolvesAS perfectForesight (fun _ y => (y - 1) * (y - 2)) 0 (fun _ => 2) (fun _ => 2) := by
  refine ⟨⟨fun _ => one_pos, rfl, ?_⟩, ⟨fun _ => two_pos, rfl, ?_⟩⟩ <;>
  · funext ω
    simp [asResidual, perfectForesight]

/-- Woodford (2003), (1.26), p. 156, CORRECTION: without a sign change of `g` there need be no
price level: under perfect foresight with `g ≡ 1`, no `P` solves (1.26). -/
theorem priceLevel_not_exists_counterexample (N : Unit → ℝ) :
    ∀ P, ¬ SolvesAS perfectForesight (fun _ _ => (1 : ℝ)) 0 N P := by
  intro P h
  have := congrFun h.2.2 ()
  simp [asResidual, perfectForesight] at this

/-! ### (1.21), (1.27), (1.30): the natural rate and the linearised first-order condition -/

/-- Woodford (2003), eq. (1.21), p. 154 (existence of the natural rate): if
`G(v, Ŷ) = Π₁(1, 1, 1; Ȳ e^Ŷ, ξ̃(v))` has strict derivative `L` at the steady state `0`, with
`G 0 = 0` and `ψ_y = L(0,1) ≠ 0`, then near `v = 0` there is a unique natural rate `Ŷⁿ(v)` with
`G(v, Ŷⁿ(v)) = 0`, `Ŷⁿ(0) = 0` and `dŶⁿ/dv = −L(1,0)/ψ_y`. -/
theorem natural_rate_exists {G : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} (hG : HasStrictFDerivAt G L 0)
    (hG0 : G 0 = 0) (hψ : L (0, 1) ≠ 0) :
    ∃ n : ℝ → ℝ, n 0 = 0 ∧ (∀ᶠ v in 𝓝 0, G (v, n v) = 0) ∧
      (∀ᶠ q in 𝓝 (0 : ℝ × ℝ), G q = 0 ↔ n q.1 = q.2) ∧
      HasStrictDerivAt n (-(L (1, 0)) / L (0, 1)) 0 := by
  obtain ⟨n, h1, h2, h3, h4⟩ := implicit_function_real hG hψ
  simp only [Prod.fst_zero, Prod.snd_zero, hG0] at h1 h2 h3 h4
  exact ⟨n, h1, h2, h3, h4⟩

/-- Woodford (2003), eq. (1.27), p. 157: if `G(v, Ŷ) = Π₁(1,1,1; Ȳe^Ŷ, ξ̃(v))` has derivative
`L(v, y) = g v + ψ_y y` at the steady state and `Ŷⁿ` (differentiable, `Ŷⁿ(0) = 0`) solves
`G(v, Ŷⁿ(v)) = 0`, then `dŶⁿ/dv = −g/ψ_y` and the linearisation is
`L(v, Ŷ) = ψ_y (Ŷ − Ŷⁿ'(0) v)`: to first order `Π₁ = ψ_y (Ŷ − Ŷⁿ)`. -/
theorem linearisation_gap_form {G : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {g ψy n' : ℝ}
    {n : ℝ → ℝ} (hG : HasFDerivAt G L 0) (hL : ∀ q, L q = g * q.1 + ψy * q.2)
    (hψ : ψy ≠ 0) (hn : HasDerivAt n n' 0) (hn0 : n 0 = 0)
    (hzero : ∀ᶠ v in 𝓝 0, G (v, n v) = 0) :
    n' = -g / ψy ∧ ∀ v y, L (v, y) = ψy * (y - n' * v) := by
  have hG' : HasFDerivAt G L ((0 : ℝ), n 0) := by
    rw [hn0]; exact hG
  have hpath : HasDerivAt (fun v => ((v, n v) : ℝ × ℝ)) ((1 : ℝ), n') 0 :=
    (hasDerivAt_id 0).prodMk hn
  have h1 := hG'.comp_hasDerivAt (x := (0 : ℝ)) hpath
  have h2 : HasDerivAt (fun v => G (v, n v)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero
  have h3 := h1.unique h2
  rw [hL] at h3
  simp only at h3
  have hn'' : n' = -g / ψy := by field_simp; linarith
  refine ⟨hn'', fun v y => ?_⟩
  rw [hL, hn'']
  field_simp
  ring

/-- Woodford (2003), eq. (1.30), pp. 158–159: if `J(x, v, Ŷ) = Π₁(e^x, e^x, 1; Ȳe^Ŷ, ξ̃(v))`
(by homogeneity `Π₁(p, p, P)` depends on `log(p/P) = x`) has derivative
`L = ψ_p x + g v + ψ_y Ŷ` at the steady state, and the natural rate solves `J(0, v, Ŷⁿ(v)) = 0`,
then `L(x, v, Ŷ) = ψ_p (x − ζ (Ŷ − Ŷⁿ'(0) v))` with `ζ = −ψ_y/ψ_p`. -/
theorem linearised_foc_form {J : ℝ × ℝ × ℝ → ℝ} {L : ℝ × ℝ × ℝ →L[ℝ] ℝ} {ψp g ψy n' : ℝ}
    {n : ℝ → ℝ} (hJ : HasFDerivAt J L 0) (hL : ∀ q, L q = ψp * q.1 + g * q.2.1 + ψy * q.2.2)
    (hψp : ψp ≠ 0) (hn : HasDerivAt n n' 0) (hn0 : n 0 = 0)
    (hzero : ∀ᶠ v in 𝓝 0, J (0, v, n v) = 0) :
    ∀ x v y, L (x, v, y) = ψp * (x - (-ψy / ψp) * (y - n' * v)) := by
  have hJ' : HasFDerivAt J L ((0 : ℝ), (0 : ℝ), n 0) := by
    rw [hn0]; exact hJ
  have hpath : HasDerivAt (fun v => ((0, v, n v) : ℝ × ℝ × ℝ)) ((0 : ℝ), (1 : ℝ), n') 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk ((hasDerivAt_id 0).prodMk hn)
  have h1 := hJ'.comp_hasDerivAt (x := (0 : ℝ)) hpath
  have h2 : HasDerivAt (fun v => J (0, v, n v)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero
  have h3 := h1.unique h2
  rw [hL] at h3
  simp only at h3
  intro x v y
  rw [hL, show ψp * (x - -ψy / ψp * (y - n' * v)) = ψp * x + ψy * (y - n' * v) by
    field_simp; ring]
  simp only
  linear_combination v * h3

/-- Woodford (2003), p. 158: the profit function `Π(p, q, P) = −P (p/P − (q/P)²)²/2` used to
show that Assumption 3.1 does not imply `ψ_p < 0`. -/
noncomputable def cePi (p q P : ℝ) : ℝ := -(P * (p / P - (q / P) ^ 2) ^ 2) / 2

/-- Woodford (2003), p. 158: the own-price derivative `Π₁(p, q, P) = −(p/P − (q/P)²)` of
`cePi`. -/
noncomputable def cePi1 (p q P : ℝ) : ℝ := -(p / P - (q / P) ^ 2)

/-- Woodford (2003), p. 158 (correction to "`ψ_p < 0` as a consequence of Assumption 3.1"):
`cePi` satisfies Assumption 3.1 — it is homogeneous of degree one in `(p, q, P)` and, for all
`q, P > 0`, single-peaked in `p` with its maximum at the positive price `q²/P` — and
`Π₁(1,1,1) = 0`, yet `ψ_p = d/dx Π₁(e^x, e^x, 1)|₀ = 1 > 0`. The extra hypothesis `ψ_p < 0`
(equivalently `Π₁₁ + Π₁₂ < 0` at the symmetric point) is needed and is assumed below. -/
theorem psi_p_not_negative_counterexample :
    (∀ c : ℝ, 0 < c → ∀ p q P, cePi (c * p) (c * q) (c * P) = c * cePi p q P) ∧
    (∀ p q P, 0 < P → HasDerivAt (fun r => cePi r q P) (cePi1 p q P) p) ∧
    (∀ q P, 0 < q → 0 < P → 0 < q ^ 2 / P ∧
      StrictMonoOn (fun r => cePi r q P) (Set.Iic (q ^ 2 / P)) ∧
      StrictAntiOn (fun r => cePi r q P) (Set.Ici (q ^ 2 / P))) ∧
    cePi1 1 1 1 = 0 ∧
    HasDerivAt (fun x => cePi1 (Real.exp x) (Real.exp x) 1) 1 0 := by
  refine ⟨?_, ?_, ?_, by simp [cePi1], ?_⟩
  · intro c hc p q P
    unfold cePi
    rw [mul_div_mul_left _ _ hc.ne', mul_div_mul_left _ _ hc.ne']
    ring
  · intro p q P hP
    have h1 : HasDerivAt (fun r : ℝ => r / P - (q / P) ^ 2) (1 / P) p := by
      simpa using ((hasDerivAt_id p).div_const P).sub_const ((q / P) ^ 2)
    have h2 := ((h1.pow 2).const_mul P).neg.div_const 2
    unfold cePi cePi1
    convert h2 using 1
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
  · intro q P hq hP
    refine ⟨div_pos (pow_pos hq 2) hP, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [Set.mem_Iic] at ha hb
      unfold cePi
      have h1 : a / P - (q / P) ^ 2 < b / P - (q / P) ^ 2 := by
        have := div_lt_div_of_pos_right hab hP
        linarith
      have h2 : b / P - (q / P) ^ 2 ≤ 0 := by
        have : b / P ≤ q ^ 2 / P / P := div_le_div_of_nonneg_right hb hP.le
        rw [div_pow]
        have e : q ^ 2 / P / P = q ^ 2 / P ^ 2 := by ring
        linarith
      have h3 : (b / P - (q / P) ^ 2) ^ 2 < (a / P - (q / P) ^ 2) ^ 2 := by nlinarith
      have := mul_lt_mul_of_pos_left h3 hP
      linarith
    · intro a ha b hb hab
      simp only [Set.mem_Ici] at ha hb
      unfold cePi
      have h1 : a / P - (q / P) ^ 2 < b / P - (q / P) ^ 2 := by
        have := div_lt_div_of_pos_right hab hP
        linarith
      have h2 : 0 ≤ a / P - (q / P) ^ 2 := by
        have : q ^ 2 / P / P ≤ a / P := div_le_div_of_nonneg_right ha hP.le
        rw [div_pow]
        have e : q ^ 2 / P / P = q ^ 2 / P ^ 2 := by ring
        linarith
      have h3 : (a / P - (q / P) ^ 2) ^ 2 < (b / P - (q / P) ^ 2) ^ 2 := by nlinarith
      have := mul_lt_mul_of_pos_left h3 hP
      linarith
  · have h := ((Real.hasDerivAt_exp 0).sub ((Real.hasDerivAt_exp 0).pow 2)).neg
    unfold cePi1
    convert h using 1
    · funext x
      simp
    · simp
      norm_num

/-! ### First-order expansion of `E_t[Q Π₁]` -/

/-- Woodford (2003), p. 157 ("log-linearization of (1.24)", restated pattern from the Chapter 2
project's `hasDerivAt_E`): on a finite state space, along a one-parameter perturbation `ε` of
the economy in which `Π₁` vanishes at `ε = 0` and the discount factor equals the constant `Q̄`
there, `d/dε E_t[Q_ε Π₁,ε] = Q̄ E_t[dΠ₁/dε]`: the fluctuations of `Q` drop out to first order. -/
theorem hasDerivAt_E_foc_product {Ω : Type*} [Finite Ω] (𝔼 : ExpectationSystem Ω)
    {Q J : ℝ → Ω → ℝ} {q' j' : Ω → ℝ} {Qbar : ℝ}
    (hQ : ∀ ω, HasDerivAt (fun ε => Q ε ω) (q' ω) 0)
    (hJ : ∀ ω, HasDerivAt (fun ε => J ε ω) (j' ω) 0)
    (hQ0 : ∀ ω, Q 0 ω = Qbar) (hJ0 : ∀ ω, J 0 ω = 0) (t : ℕ) (ω₀ : Ω) :
    HasDerivAt (fun ε => 𝔼.E t (fun ω => Q ε ω * J ε ω) ω₀) (Qbar * 𝔼.E t j' ω₀) 0 := by
  have := Fintype.ofFinite Ω
  have hprod : ∀ ω, HasDerivAt (fun ε => Q ε ω * J ε ω) (Qbar * j' ω) 0 := fun ω =>
    ((hQ ω).mul (hJ ω)).congr_deriv (by simp [hQ0 ω, hJ0 ω])
  have hF : HasDerivAt (fun ε => fun ω => Q ε ω * J ε ω) (Qbar • j') 0 :=
    hasDerivAt_pi.mpr fun ω => by simpa using hprod ω
  have hL := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt 0 hF
  have := hasDerivAt_pi.mp hL ω₀
  simpa [map_smul] using this

/-! ### (1.22)–(1.23): the ex ante pricing problem and its first-order condition

A general `ExpectationSystem` is only a linear, monotone family of maps on `Ω → ℝ`, with no
continuity, so differentiation under `E_t` is not available in general; it is available whenever
`Ω` is finite (every finite event tree, `ExpectationsFiniteTree.toExpectationSystem`, and perfect
foresight), where `E_t` is a linear map on a finite-dimensional space. -/

/-- Supporting-line inequality for a differentiable concave function (Woodford (2003), used for
(1.23), p. 155, and (B.2), p. 656): `f(y) ≤ f(x) + f'(x)(y − x)` on a convex set where `f` is
concave. -/
theorem concave_tangent_le {S : Set ℝ} {ψ : ℝ → ℝ} {x y d : ℝ} (hψ : ConcaveOn ℝ S ψ)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt ψ d x) : ψ y ≤ ψ x + d * (y - x) := by
  have hc : ConvexOn ℝ S (-ψ) := hψ.neg
  have hd' : HasDerivAt (-ψ) (-d) x := hd.neg
  rcases lt_trichotomy x y with h | h | h
  · have := hc.le_slope_of_hasDerivAt hx hy h hd'
    rw [slope_def_field] at this
    simp only [Pi.neg_apply] at this
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := hc.slope_le_of_hasDerivAt hy hx h hd'
    rw [slope_def_field] at this
    simp only [Pi.neg_apply] at this
    rw [div_le_iff₀ (by linarith)] at this
    linarith

/-- Woodford (2003), eq. (1.22), p. 155, on a finite state space: the ex ante objective
`r ↦ E_t[Q Π(r)]` (evaluated in the date-`t` state `ω₀`) has derivative `E_t[Q Π₁(p)]` at `p`
when each state's profit is differentiable in the price. -/
theorem hasDerivAt_expected_profit {Ω : Type*} [Finite Ω] (𝔼 : ExpectationSystem Ω)
    {Q : Ω → ℝ} {Pr Pr1 : ℝ → Ω → ℝ} {p : ℝ}
    (hd : ∀ ω, HasDerivAt (fun r => Pr r ω) (Pr1 p ω) p) (t : ℕ) (ω₀ : Ω) :
    HasDerivAt (fun r => 𝔼.E t (fun ω => Q ω * Pr r ω) ω₀)
      (𝔼.E t (fun ω => Q ω * Pr1 p ω) ω₀) p := by
  have := Fintype.ofFinite Ω
  have hF : HasDerivAt (fun r => fun ω => Q ω * Pr r ω) (fun ω => Q ω * Pr1 p ω) p :=
    hasDerivAt_pi.mpr fun ω => (hd ω).const_mul (Q ω)
  have hL := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt p hF
  have := hasDerivAt_pi.mp hL ω₀
  simpa using this

/-- Woodford (2003), eq. (1.23), p. 155 (necessity), on any finite state space: a price `p` that
maximises the ex ante objective (1.22) (even locally) satisfies `E_t[Q Π₁(p, …)] = 0`. -/
theorem foc_1_23_necessary {Ω : Type*} [Finite Ω] (𝔼 : ExpectationSystem Ω)
    {Q : Ω → ℝ} {Pr Pr1 : ℝ → Ω → ℝ} {p : ℝ}
    (hd : ∀ ω, HasDerivAt (fun r => Pr r ω) (Pr1 p ω) p) (t : ℕ) (ω₀ : Ω)
    (hmax : IsLocalMax (fun r => 𝔼.E t (fun ω => Q ω * Pr r ω) ω₀) p) :
    𝔼.E t (fun ω => Q ω * Pr1 p ω) ω₀ = 0 :=
  hmax.hasDerivAt_eq_zero (hasDerivAt_expected_profit 𝔼 hd t ω₀)

/-- Woodford (2003), (1.23), p. 155, for every finite event tree (genuine uncertainty). -/
theorem foc_1_23_tree {Ω : Type*} [Fintype Ω] (T : ExpectationsFiniteTree.FiniteTree Ω)
    {Q : Ω → ℝ} {Pr Pr1 : ℝ → Ω → ℝ} {p : ℝ}
    (hd : ∀ ω, HasDerivAt (fun r => Pr r ω) (Pr1 p ω) p) (t : ℕ) (ω₀ : Ω)
    (hmax : IsLocalMax (fun r => T.toExpectationSystem.E t (fun ω => Q ω * Pr r ω) ω₀) p) :
    T.toExpectationSystem.E t (fun ω => Q ω * Pr1 p ω) ω₀ = 0 :=
  foc_1_23_necessary _ hd t ω₀ hmax

/-- Woodford (2003), (1.23), p. 155, under perfect foresight: `Q Π₁(p) = 0`. -/
theorem foc_1_23_perfectForesight {Q : Unit → ℝ} {Pr Pr1 : ℝ → Unit → ℝ} {p : ℝ}
    (hd : ∀ ω, HasDerivAt (fun r => Pr r ω) (Pr1 p ω) p) (t : ℕ)
    (hmax : IsLocalMax (fun r => perfectForesight.E t (fun ω => Q ω * Pr r ω) ()) p) :
    Q () * Pr1 p () = 0 :=
  foc_1_23_necessary perfectForesight hd t () hmax

/-- Woodford (2003), (1.22)–(1.23), p. 155 (sufficiency, any `ExpectationSystem`): if the
discount factor is nonnegative and each state's profit is concave in the price on a convex set
`S` (the concavity behind single-peakedness, p. 154), then a price `p ∈ S` satisfying the
first-order condition (1.23) maximises the ex ante objective (1.22) over `S`. -/
theorem foc_1_23_sufficient {Ω : Type*} (𝔼 : ExpectationSystem Ω) {S : Set ℝ}
    {Q : Ω → ℝ} {Pr Pr1 : ℝ → Ω → ℝ} {p : ℝ} (hQ : ∀ ω, 0 ≤ Q ω)
    (hconc : ∀ ω, ConcaveOn ℝ S (fun r => Pr r ω)) (hp : p ∈ S)
    (hd : ∀ ω, HasDerivAt (fun r => Pr r ω) (Pr1 p ω) p) (t : ℕ) (ω₀ : Ω)
    (hfoc : 𝔼.E t (fun ω => Q ω * Pr1 p ω) ω₀ = 0) :
    ∀ r ∈ S, 𝔼.E t (fun ω => Q ω * Pr r ω) ω₀ ≤ 𝔼.E t (fun ω => Q ω * Pr p ω) ω₀ := by
  intro r hr
  have hle : (fun ω => Q ω * Pr r ω) ≤
      (fun ω => Q ω * Pr p ω) + (r - p) • (fun ω => Q ω * Pr1 p ω) := by
    intro ω
    have ht := concave_tangent_le (hconc ω) hp hr (hd ω)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hQ ω]
  have := 𝔼.mono t hle ω₀
  rw [map_add, map_smul] at this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hfoc, mul_zero, add_zero] at this
  exact this

/-! ### §1.2: the aggregate-supply relation with all prices fixed in advance -/

namespace AS

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 157: the linearised (1.24), `E_t[ψ_y (Ŷ − Ŷⁿ)] = 0` with `ψ_y ≠ 0`,
gives `E_t(Ŷ_{t+1} − Ŷⁿ_{t+1}) = 0`. -/
theorem expected_gap_zero_of_foc {ψy : ℝ} (hψ : ψy ≠ 0) (t : ℕ) (gap : Ω → ℝ)
    (h : 𝔼.E t (ψy • gap) = 0) : 𝔼.E t gap = 0 := by
  rw [map_smul] at h
  exact (smul_eq_zero.mp h).resolve_left hψ

variable {lN lP lY lYn : ℕ → Ω → ℝ} {t : ℕ}

/-- Woodford (2003), p. 157: with all prices fixed one period in advance (`P_{t+1}` known at
`t`), output `log Y = log 𝒴 − log P`, and `E_t(log Y − log Yⁿ) = 0`, the equilibrium price level
is `log P_{t+1} = E_t log 𝒴_{t+1} − E_t log Yⁿ_{t+1}`. -/
theorem predetermined_price_level (hgap : 𝔼.E t (lY (t + 1) - lYn (t + 1)) = 0)
    (hpre : 𝔼.E t (lP (t + 1)) = lP (t + 1)) (hY : lY (t + 1) = lN (t + 1) - lP (t + 1)) :
    lP (t + 1) = 𝔼.E t (lN (t + 1)) - 𝔼.E t (lYn (t + 1)) := by
  rw [map_sub, hY, map_sub, hpre] at hgap
  funext ω
  have := congrFun hgap ω
  simp only [Pi.sub_apply, Pi.zero_apply] at this ⊢
  linarith

/-- Woodford (2003), p. 157: `log Y_{t+1} = E_t log Yⁿ_{t+1} + [log 𝒴_{t+1} − E_t log 𝒴_{t+1}]`. -/
theorem predetermined_output (hgap : 𝔼.E t (lY (t + 1) - lYn (t + 1)) = 0)
    (hpre : 𝔼.E t (lP (t + 1)) = lP (t + 1)) (hY : lY (t + 1) = lN (t + 1) - lP (t + 1)) :
    lY (t + 1) = 𝔼.E t (lYn (t + 1)) + (lN (t + 1) - 𝔼.E t (lN (t + 1))) := by
  rw [hY, predetermined_price_level 𝔼 hgap hpre hY]
  abel

/-- Woodford (2003), p. 157: the forecastable component of output equals the forecast of the
natural rate, `E_t log Y_{t+1} = E_t log Yⁿ_{t+1}`, independently of monetary policy. -/
theorem forecastable_output (hgap : 𝔼.E t (lY (t + 1) - lYn (t + 1)) = 0) :
    𝔼.E t (lY (t + 1)) = 𝔼.E t (lYn (t + 1)) := by
  rw [map_sub] at hgap
  exact sub_eq_zero.mp hgap

/-- Woodford (2003), p. 158: unexpected output equals unexpected nominal spending,
`log Y − E_t log Y = log 𝒴 − E_t log 𝒴`. -/
theorem output_surprise (hgap : 𝔼.E t (lY (t + 1) - lYn (t + 1)) = 0)
    (hpre : 𝔼.E t (lP (t + 1)) = lP (t + 1)) (hY : lY (t + 1) = lN (t + 1) - lP (t + 1)) :
    lY (t + 1) - 𝔼.E t (lY (t + 1)) = lN (t + 1) - 𝔼.E t (lN (t + 1)) := by
  rw [forecastable_output 𝔼 hgap, predetermined_output 𝔼 hgap hpre hY]
  abel

end AS

/-! ### §1.3: the log-linear price index and Proposition 3.2 -/

/-- Woodford (2003), eq. (1.3), p. 146, with a fraction `ι` of goods at price `p₁` and `1 − ι`
at `p₂`: the log of the Dixit–Stiglitz index as a function of `(log p₁, log p₂)`,
`log P = log(ι e^{(1−θ)x₁} + (1−ι) e^{(1−θ)x₂})/(1 − θ)`. -/
noncomputable def logCES2 (θ ι : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.log (ι * Real.exp ((1 - θ) * x.1) + (1 - ι) * Real.exp ((1 - θ) * x.2)) / (1 - θ)

/-- Woodford (2003), (1.3), p. 146: `logCES2` is the log of
`P = (ι p₁^{1−θ} + (1−ι) p₂^{1−θ})^{1/(1−θ)}`. -/
theorem logCES2_eq {θ ι p₁ p₂ : ℝ} (hι0 : 0 ≤ ι) (hι1 : ι ≤ 1) (hθ : θ ≠ 1) (h₁ : 0 < p₁)
    (h₂ : 0 < p₂) :
    logCES2 θ ι (Real.log p₁, Real.log p₂) =
      Real.log ((ι * p₁ ^ (1 - θ) + (1 - ι) * p₂ ^ (1 - θ)) ^ (1 / (1 - θ))) := by
  have hpos : 0 < ι * p₁ ^ (1 - θ) + (1 - ι) * p₂ ^ (1 - θ) := by
    rcases hι0.eq_or_lt with h | h
    · subst h; simp [Real.rpow_pos_of_pos h₂]
    · have := Real.rpow_pos_of_pos h₂ (1 - θ)
      have := Real.rpow_pos_of_pos h₁ (1 - θ)
      nlinarith
  rw [Real.log_rpow hpos, logCES2, Real.rpow_def_of_pos h₁, Real.rpow_def_of_pos h₂]
  have : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  field_simp

/-- Woodford (2003), p. 159: the log-linear approximation to the price index,
`log P = ι log p₁ + (1 − ι) log p₂`, is the exact derivative of `logCES2` at the symmetric
point `p₁ = p₂ = 1` (where `log P = 0`). -/
theorem hasFDerivAt_log_ces_two {θ ι : ℝ} (hθ : θ ≠ 1) :
    logCES2 θ ι 0 = 0 ∧
    HasFDerivAt (logCES2 θ ι)
      (ι • ContinuousLinearMap.fst ℝ ℝ ℝ + (1 - ι) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := by
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  refine ⟨by simp [logCES2], ?_⟩
  have hA : HasFDerivAt (fun x : ℝ × ℝ => Real.exp ((1 - θ) * x.1))
      (Real.exp ((1 - θ) * (0 : ℝ × ℝ).1) • ((1 - θ) • ContinuousLinearMap.fst ℝ ℝ ℝ)) 0 :=
    HasFDerivAt.exp (HasFDerivAt.const_mul hasFDerivAt_fst (1 - θ))
  have hB : HasFDerivAt (fun x : ℝ × ℝ => Real.exp ((1 - θ) * x.2))
      (Real.exp ((1 - θ) * (0 : ℝ × ℝ).2) • ((1 - θ) • ContinuousLinearMap.snd ℝ ℝ ℝ)) 0 :=
    HasFDerivAt.exp (HasFDerivAt.const_mul hasFDerivAt_snd (1 - θ))
  have hS := HasFDerivAt.add (HasFDerivAt.const_mul hA ι) (HasFDerivAt.const_mul hB (1 - ι))
  have hS0 : ι * Real.exp ((1 - θ) * (0 : ℝ × ℝ).1) +
      (1 - ι) * Real.exp ((1 - θ) * (0 : ℝ × ℝ).2) ≠ 0 := by simp
  have hlog := HasFDerivAt.mul_const (HasFDerivAt.log hS hS0) (1 - θ)⁻¹
  unfold logCES2
  convert hlog using 1
  · funext q
    simp [div_eq_mul_inv]
  · ext <;> simp <;> field_simp

namespace NC

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)
variable {ι ζ : ℝ} {lP lp1 lp2 gap : ℕ → Ω → ℝ} {t : ℕ}

/-- Woodford (2003), (1.31) second line, p. 159: the linearised ex ante condition (1.29),
`E_t[log p₂ − log P − ζ(Ŷ − Ŷⁿ)] = 0`, with `p₂` predetermined, gives
`log p₂ = E_t[log P + ζ(Ŷ − Ŷⁿ)]`. -/
theorem sticky_price_eq
    (hsticky : 𝔼.E t (lp2 (t + 1) - lP (t + 1) - ζ • gap (t + 1)) = 0)
    (hpre : 𝔼.E t (lp2 (t + 1)) = lp2 (t + 1)) :
    lp2 (t + 1) = 𝔼.E t (lP (t + 1) + ζ • gap (t + 1)) := by
  rw [sub_sub, map_sub, hpre] at hsticky
  exact sub_eq_zero.mp hsticky

/-- Woodford (2003), p. 159: `log p₂ = E_t log p₁` — the predetermined price is the forecast
of the flexible price. -/
theorem sticky_eq_expected_flex (hflex : lp1 (t + 1) = lP (t + 1) + ζ • gap (t + 1))
    (hsticky : 𝔼.E t (lp2 (t + 1) - lP (t + 1) - ζ • gap (t + 1)) = 0)
    (hpre : 𝔼.E t (lp2 (t + 1)) = lp2 (t + 1)) :
    lp2 (t + 1) = 𝔼.E t (lp1 (t + 1)) := by
  rw [hflex]
  exact sticky_price_eq 𝔼 hsticky hpre

/-- Woodford (2003), p. 159: `π − E_t π = log P − E_t log P = ι/(1−ι) (log p₁ − log P)`. -/
theorem surprise_price (hι1 : ι < 1) (hflex : lp1 (t + 1) = lP (t + 1) + ζ • gap (t + 1))
    (hsticky : 𝔼.E t (lp2 (t + 1) - lP (t + 1) - ζ • gap (t + 1)) = 0)
    (hpre : 𝔼.E t (lp2 (t + 1)) = lp2 (t + 1))
    (hindex : lP (t + 1) = ι • lp1 (t + 1) + (1 - ι) • lp2 (t + 1)) :
    lP (t + 1) - 𝔼.E t (lP (t + 1)) = (ι / (1 - ι)) • (lp1 (t + 1) - lP (t + 1)) := by
  have h2 := sticky_eq_expected_flex 𝔼 hflex hsticky hpre
  have hE : 𝔼.E t (lP (t + 1)) = lp2 (t + 1) := by
    rw [hindex, map_add, map_smul, map_smul, hpre, ← h2]
    rw [← add_smul]; simp
  rw [hE]
  have h1ι : (1 : ℝ) - ι ≠ 0 := by linarith
  funext ω
  have hi := congrFun hindex ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hi ⊢
  rw [hi]
  field_simp
  ring

/-- **Proposition 3.2** (Woodford (2003), eq. (1.32), p. 159), the New Classical Phillips curve:
with a fraction `0 < ι < 1` of flexible prices (linearised (1.28): `log p₁ = log P + ζ(Ŷ − Ŷⁿ)`)
and `1 − ι` fixed one period in advance (linearised (1.29), `p₂` known at `t`), and the
log-linear index `log P = ι log p₁ + (1−ι) log p₂`, inflation satisfies
`π_{t+1} = κ (Ŷ − Ŷⁿ)_{t+1} + E_t π_{t+1}` with `κ = ι ζ/(1 − ι)`. -/
theorem prop_3_2 (hι1 : ι < 1) (hflex : lp1 (t + 1) = lP (t + 1) + ζ • gap (t + 1))
    (hsticky : 𝔼.E t (lp2 (t + 1) - lP (t + 1) - ζ • gap (t + 1)) = 0)
    (hpre : 𝔼.E t (lp2 (t + 1)) = lp2 (t + 1))
    (hindex : lP (t + 1) = ι • lp1 (t + 1) + (1 - ι) • lp2 (t + 1))
    (hadP : 𝔼.E t (lP t) = lP t) :
    lP (t + 1) - lP t = (ι * ζ / (1 - ι)) • gap (t + 1) + 𝔼.E t (lP (t + 1) - lP t) := by
  have hs := surprise_price 𝔼 hι1 hflex hsticky hpre hindex
  rw [map_sub, hadP]
  have h1ι : (1 : ℝ) - ι ≠ 0 := by linarith
  funext ω
  have h := congrFun hs ω
  have hf := congrFun hflex ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h hf ⊢
  rw [hf] at h
  field_simp at h ⊢
  linear_combination h

/-- Woodford (2003), Proposition 3.2, p. 159: `κ = ι ζ/(1 − ι) > 0` for `0 < ι < 1`, `ζ > 0`. -/
theorem kappa_pos (hι0 : 0 < ι) (hι1 : ι < 1) (hζ : 0 < ζ) : 0 < ι * ζ / (1 - ι) :=
  div_pos (mul_pos hι0 hζ) (by linarith)

end NC

/-! ### Consequences of (1.32): the corrected (1.33) (survey error E1) -/

namespace PC

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)
variable {κ : ℝ} {lN lP lY lYn : ℕ → Ω → ℝ} {t : ℕ}

/-- Woodford (2003), p. 160: (1.32) implies `E_t(Ŷ − Ŷⁿ)_{t+1} = 0` (for `κ ≠ 0`), using that
`E_t` is idempotent (`E_t E_t = E_t`, the tower property). -/
theorem expected_gap_zero (hκ : κ ≠ 0) (gap infl : Ω → ℝ)
    (hPC : infl = κ • gap + 𝔼.E t infl) : 𝔼.E t gap = 0 := by
  have h := congrArg (𝔼.E t) hPC
  rw [map_add, map_smul, 𝔼.E_E_self] at h
  have : κ • 𝔼.E t gap = 0 := by
    have h' := congrArg (· - 𝔼.E t infl) h
    simpa using h'.symm
  exact (smul_eq_zero.mp this).resolve_left hκ

/-- Woodford (2003), p. 160: under (1.32), `E_t log Y_{t+1} = E_t log Yⁿ_{t+1}`. -/
theorem expected_output (hκ : κ ≠ 0)
    (hPC : lP (t + 1) - lP t = κ • (lY (t + 1) - lYn (t + 1)) + 𝔼.E t (lP (t + 1) - lP t)) :
    𝔼.E t (lY (t + 1)) = 𝔼.E t (lYn (t + 1)) := by
  have := expected_gap_zero 𝔼 hκ _ _ hPC
  rw [map_sub] at this
  exact sub_eq_zero.mp this

/-- Woodford (2003), eq. (1.33), p. 160, CORRECTED (survey error E1): under (1.32) with
`log Y = log 𝒴 − log P` and `P_t` known at `t`,
`log Y = log Yⁿ + (1+κ)⁻¹ [(log 𝒴 − E_t log 𝒴) − (log Yⁿ − E_t log Yⁿ)]`. -/
theorem output_corrected (hκ : κ ≠ 0) (hκ1 : 1 + κ ≠ 0)
    (hPC : lP (t + 1) - lP t = κ • (lY (t + 1) - lYn (t + 1)) + 𝔼.E t (lP (t + 1) - lP t))
    (hY : lY (t + 1) = lN (t + 1) - lP (t + 1)) (hadP : 𝔼.E t (lP t) = lP t) :
    lY (t + 1) = lYn (t + 1) + (1 + κ)⁻¹ •
      ((lN (t + 1) - 𝔼.E t (lN (t + 1))) - (lYn (t + 1) - 𝔼.E t (lYn (t + 1)))) := by
  have hEY := expected_output 𝔼 hκ hPC
  have hEP : 𝔼.E t (lP (t + 1)) = 𝔼.E t (lN (t + 1)) - 𝔼.E t (lY (t + 1)) := by
    have : lP (t + 1) = lN (t + 1) - lY (t + 1) := by rw [hY]; abel
    rw [this, map_sub]
  rw [map_sub, hadP, hEP, hEY] at hPC
  funext ω
  have h := congrFun hPC ω
  have hy := congrFun hY ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h hy ⊢
  apply mul_left_cancel₀ hκ1
  rw [mul_add, mul_inv_cancel_left₀ hκ1]
  linear_combination hy - h

/-- Woodford (2003), p. 160, the price-level formula CORRECTED (survey error E1):
`log P = E_t log 𝒴 − E_t log Yⁿ + κ/(1+κ) [(log 𝒴 − E_t log 𝒴) − (log Yⁿ − E_t log Yⁿ)]`. -/
theorem price_level_corrected (hκ : κ ≠ 0) (hκ1 : 1 + κ ≠ 0)
    (hPC : lP (t + 1) - lP t = κ • (lY (t + 1) - lYn (t + 1)) + 𝔼.E t (lP (t + 1) - lP t))
    (hY : lY (t + 1) = lN (t + 1) - lP (t + 1)) (hadP : 𝔼.E t (lP t) = lP t) :
    lP (t + 1) = 𝔼.E t (lN (t + 1)) - 𝔼.E t (lYn (t + 1)) + (κ / (1 + κ)) •
      ((lN (t + 1) - 𝔼.E t (lN (t + 1))) - (lYn (t + 1) - 𝔼.E t (lYn (t + 1)))) := by
  have h := output_corrected 𝔼 hκ hκ1 hPC hY hadP
  funext ω
  have h1 := congrFun h ω
  have hy := congrFun hY ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1 hy ⊢
  rw [show κ / (1 + κ) = 1 - (1 + κ)⁻¹ by field_simp; ring]
  linear_combination hy - h1

/-- Woodford (2003), (1.33), p. 160 as printed: given the model, the printed formula
`log Y = log Yⁿ + (1+κ)⁻¹ (log 𝒴 − E_t log 𝒴)` holds if and only if the natural rate is
forecastable, `log Yⁿ_{t+1} = E_t log Yⁿ_{t+1}` (survey error E1 confirmed). -/
theorem printed_1_33_iff (hκ : κ ≠ 0) (hκ1 : 1 + κ ≠ 0)
    (hPC : lP (t + 1) - lP t = κ • (lY (t + 1) - lYn (t + 1)) + 𝔼.E t (lP (t + 1) - lP t))
    (hY : lY (t + 1) = lN (t + 1) - lP (t + 1)) (hadP : 𝔼.E t (lP t) = lP t) :
    lY (t + 1) = lYn (t + 1) + (1 + κ)⁻¹ • (lN (t + 1) - 𝔼.E t (lN (t + 1))) ↔
      lYn (t + 1) = 𝔼.E t (lYn (t + 1)) := by
  rw [output_corrected 𝔼 hκ hκ1 hPC hY hadP]
  constructor
  · intro h
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
    have : (1 + κ)⁻¹ * (lYn (t + 1) ω - 𝔼.E t (lYn (t + 1)) ω) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left (inv_ne_zero hκ1)
    linarith
  · intro h
    rw [← h, sub_self, sub_zero]

/-- Woodford (2003), p. 160, the printed price-level formula
`log P = (E_t log 𝒴 − log Yⁿ) + κ/(1+κ)(log 𝒴 − E_t log 𝒴)` holds if and only if
`log Yⁿ_{t+1} = E_t log Yⁿ_{t+1}` (survey error E1 confirmed). -/
theorem printed_price_level_iff (hκ : κ ≠ 0) (hκ1 : 1 + κ ≠ 0)
    (hPC : lP (t + 1) - lP t = κ • (lY (t + 1) - lYn (t + 1)) + 𝔼.E t (lP (t + 1) - lP t))
    (hY : lY (t + 1) = lN (t + 1) - lP (t + 1)) (hadP : 𝔼.E t (lP t) = lP t) :
    lP (t + 1) = 𝔼.E t (lN (t + 1)) - lYn (t + 1) +
        (κ / (1 + κ)) • (lN (t + 1) - 𝔼.E t (lN (t + 1))) ↔
      lYn (t + 1) = 𝔼.E t (lYn (t + 1)) := by
  rw [price_level_corrected 𝔼 hκ hκ1 hPC hY hadP]
  constructor
  · intro h
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h1
    have e : (1 + κ)⁻¹ * (lYn (t + 1) ω - 𝔼.E t (lYn (t + 1)) ω) = 0 := by
      field_simp at h1 ⊢
      linarith
    have := (mul_eq_zero.mp e).resolve_left (inv_ne_zero hκ1)
    linarith
  · intro h
    funext ω
    have h1 := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← h1]
    ring

end PC

/-- Woodford (2003), (1.33), p. 160 — a counterexample to the printed formula under genuine
uncertainty (two coin flips, `coinSystem`): for any `κ > 0`, with nominal spending constant,
`log Yⁿ_t = u_t` mean-zero shocks (`u = coinAR1 0`), `log Y = κ/(1+κ) u` and
`log P = −log Y`, all processes are adapted and the New Classical Phillips curve (1.32) holds at
every date, yet the printed (1.33) fails at date 1 (it would give `log Y_1 = u_1 ≠ κ u_1/(1+κ)`). -/
theorem printed_1_33_counterexample {κ : ℝ} (hκ : 0 < κ) :
    ∃ lN lP lY lYn : ℕ → Bool × Bool → ℝ,
      ExpectationsFiniteTree.coinSystem.Adapted lN ∧
      ExpectationsFiniteTree.coinSystem.Adapted lP ∧
      ExpectationsFiniteTree.coinSystem.Adapted lY ∧
      ExpectationsFiniteTree.coinSystem.Adapted lYn ∧ (∀ t, lY t = lN t - lP t) ∧
      (∀ t, lP (t + 1) - lP t =
        κ • (lY (t + 1) - lYn (t + 1)) +
          ExpectationsFiniteTree.coinSystem.E t (lP (t + 1) - lP t)) ∧
      lY 1 ≠ lYn 1 + (1 + κ)⁻¹ • (lN 1 - ExpectationsFiniteTree.coinSystem.E 0 (lN 1)) := by
  set u := ExpectationsFiniteTree.coinAR1 0 with hu_def
  have hu := ExpectationsFiniteTree.coinAR1_isAR1 (0 : ℝ)
  set a : ℝ := κ / (1 + κ)
  have hκ1 : (1 : ℝ) + κ ≠ 0 := by linarith
  refine ⟨fun _ => 0, fun t => (-a) • u t, fun t => a • u t, u, ?_, ?_, ?_, hu.1, ?_, ?_, ?_⟩
  · intro t; exact map_zero _
  · intro t; rw [map_smul, hu.1 t]
  · intro t; rw [map_smul, hu.1 t]
  · intro t; funext ω; simp
  · intro t
    rw [map_sub, map_smul, map_smul, hu.2 t, hu.1 t]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, zero_mul]
    simp only [a]
    field_simp
    ring
  · intro h
    have h1 := congrFun h (true, true)
    have hu1 : u 1 (true, true) = 1 := by
      simp [hu_def, ExpectationsFiniteTree.coinAR1, ExpectationsFiniteTree.coinShock]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_zero,
      Pi.zero_apply, sub_zero, mul_zero, add_zero, hu1, a] at h1
    field_simp at h1
    linarith

/-! ### Figure 3.1: the output elasticity `1/(1 + κ)` as a function of `ι` -/

/-- Woodford (2003), Proposition 3.2, p. 159: the slope `κ(ι) = ι ζ/(1 − ι)`. -/
noncomputable def kappaNC (ι ζ : ℝ) : ℝ := ι * ζ / (1 - ι)

/-- Woodford (2003), (1.33), p. 160: the elasticity `1/(1 + κ)` of output with respect to
unexpected nominal spending. -/
noncomputable def outputElasticity (ι ζ : ℝ) : ℝ := 1 / (1 + kappaNC ι ζ)

/-- Woodford (2003), Figure 3.1, p. 161: the plotted curve in closed form,
`f(ι) = (1 − ι)/(1 + (ζ − 1) ι)`, defined on all of `[0, 1]`. -/
noncomputable def fig31 (ζ ι : ℝ) : ℝ := (1 - ι) / (1 + (ζ - 1) * ι)

/-- Woodford (2003), Fig. 3.1, p. 161: the denominator `1 + (ζ − 1)ι = (1 − ι) + ζι` is positive
on `[0, 1]` when `ζ > 0`. -/
theorem fig31_den_pos {ζ ι : ℝ} (hζ : 0 < ζ) (h0 : 0 ≤ ι) (h1 : ι ≤ 1) :
    0 < 1 + (ζ - 1) * ι := by
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  · nlinarith

/-- Woodford (2003), Fig. 3.1, p. 161: for `0 ≤ ι < 1`, `1/(1 + κ) = (1 − ι)/(1 + (ζ − 1)ι)`. -/
theorem fig31_closed_form {ζ ι : ℝ} (hζ : 0 < ζ) (h0 : 0 ≤ ι) (h1 : ι < 1) :
    outputElasticity ι ζ = fig31 ζ ι := by
  have hd := fig31_den_pos hζ h0 h1.le
  have h1' : (1 : ℝ) - ι ≠ 0 := by linarith
  unfold outputElasticity kappaNC fig31
  field_simp
  ring_nf

/-- Woodford (2003), p. 160: "takes the same values in the two limiting cases `ι = 0` and
`ι = 1`": `f(0) = 1` and `f(1) = 0` for every `ζ`. -/
theorem fig31_endpoints (ζ : ℝ) : fig31 ζ 0 = 1 ∧ fig31 ζ 1 = 0 := by
  simp [fig31]

/-- Woodford (2003), Fig. 3.1: `f'(ι) = −ζ/(1 + (ζ − 1)ι)²`. -/
theorem fig31_hasDerivAt {ζ ι : ℝ} (hd : 1 + (ζ - 1) * ι ≠ 0) :
    HasDerivAt (fig31 ζ) (-ζ / (1 + (ζ - 1) * ι) ^ 2) ι := by
  have hn : HasDerivAt (fun x : ℝ => 1 - x) (-1) ι := by
    simpa using (hasDerivAt_id ι).const_sub 1
  have hden : HasDerivAt (fun x : ℝ => 1 + (ζ - 1) * x) (ζ - 1) ι := by
    simpa using ((hasDerivAt_id ι).const_mul (ζ - 1)).const_add 1
  have := hn.div hden hd
  unfold fig31
  convert this using 1
  field_simp
  ring

/-- Woodford (2003), Fig. 3.1: `f''(ι) = 2ζ(ζ − 1)/(1 + (ζ − 1)ι)³`. -/
theorem fig31_deriv2 {ζ ι : ℝ} (hd : 1 + (ζ - 1) * ι ≠ 0) :
    HasDerivAt (fun x => -ζ / (1 + (ζ - 1) * x) ^ 2)
      (2 * ζ * (ζ - 1) / (1 + (ζ - 1) * ι) ^ 3) ι := by
  have hl : HasDerivAt (fun x : ℝ => 1 + (ζ - 1) * x) (ζ - 1) ι := by
    simpa using ((hasDerivAt_id ι).const_mul (ζ - 1)).const_add 1
  have := (hasDerivAt_const ι (-ζ)).div (hl.pow 2) (pow_ne_zero 2 hd)
  convert this using 1
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.pow_apply]
  field_simp
  ring

/-- Woodford (2003), Fig. 3.1: on the interior `(0, 1)` the derivative of `f` equals
`−ζ/(1 + (ζ−1)ι)²` in a neighbourhood, so `f'' = 2ζ(ζ − 1)/(1 + (ζ − 1)ι)³` there. -/
theorem fig31_iterated_deriv {ζ ι : ℝ} (hζ : 0 < ζ) (h0 : 0 < ι) (h1 : ι < 1) :
    deriv^[2] (fig31 ζ) ι = 2 * ζ * (ζ - 1) / (1 + (ζ - 1) * ι) ^ 3 := by
  have hopen : IsOpen {x : ℝ | 1 + (ζ - 1) * x ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hmem : ι ∈ {x : ℝ | 1 + (ζ - 1) * x ≠ 0} := (fig31_den_pos hζ h0.le h1.le).ne'
  have hev : deriv (fig31 ζ) =ᶠ[𝓝 ι] fun x => -ζ / (1 + (ζ - 1) * x) ^ 2 :=
    Filter.eventually_of_mem (hopen.mem_nhds hmem) fun x hx => (fig31_hasDerivAt hx).deriv
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  rw [hev.deriv_eq]
  exact (fig31_deriv2 hmem).deriv

/-- Woodford (2003), Fig. 3.1, continuity of `f` on `[0, 1]` (for `ζ > 0`). -/
theorem fig31_continuousOn {ζ : ℝ} (hζ : 0 < ζ) : ContinuousOn (fig31 ζ) (Set.Icc 0 1) := by
  unfold fig31
  exact ContinuousOn.div (by fun_prop) (by fun_prop)
    fun x hx => (fig31_den_pos hζ hx.1 hx.2).ne'

/-- Woodford (2003), p. 160: "the function is monotonically decreasing": `f` is strictly
decreasing on `[0, 1]` for every `ζ > 0`. -/
theorem fig31_strictAntiOn {ζ : ℝ} (hζ : 0 < ζ) : StrictAntiOn (fig31 ζ) (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) (fig31_continuousOn hζ)
  intro x hx
  rw [interior_Icc] at hx
  have hd := fig31_den_pos hζ hx.1.le hx.2.le
  rw [(fig31_hasDerivAt hd.ne').deriv]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- Woodford (2003), p. 160: "when `ζ > 1`, the function is convex": strictly convex on
`[0, 1]`. -/
theorem fig31_strictConvexOn {ζ : ℝ} (hζ : 1 < ζ) : StrictConvexOn ℝ (Set.Icc 0 1) (fig31 ζ) := by
  have hζ0 : 0 < ζ := by linarith
  apply strictConvexOn_of_deriv2_pos (convex_Icc 0 1) (fig31_continuousOn hζ0)
  intro x hx
  rw [interior_Icc] at hx
  rw [fig31_iterated_deriv hζ0 hx.1 hx.2]
  have hd := fig31_den_pos hζ0 hx.1.le hx.2.le
  have : 0 < ζ - 1 := by linarith
  positivity

/-- Woodford (2003), p. 160: "when `ζ < 1`, the function is concave": strictly concave on
`[0, 1]` (for `0 < ζ < 1`). -/
theorem fig31_strictConcaveOn {ζ : ℝ} (hζ0 : 0 < ζ) (hζ : ζ < 1) :
    StrictConcaveOn ℝ (Set.Icc 0 1) (fig31 ζ) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) (fig31_continuousOn hζ0)
  intro x hx
  rw [interior_Icc] at hx
  rw [fig31_iterated_deriv hζ0 hx.1 hx.2]
  have hd := fig31_den_pos hζ0 hx.1.le hx.2.le
  have : 0 < 1 - ζ := by linarith
  have h3 : 0 < (1 + (ζ - 1) * x) ^ 3 := by positivity
  apply div_neg_of_neg_of_pos _ h3
  nlinarith

/-- Woodford (2003), Fig. 3.1: for `ζ = 1` the curve is the straight line `1 − ι`. -/
theorem fig31_linear (ι : ℝ) : fig31 1 ι = 1 - ι := by
  simp [fig31]

/-- Woodford (2003), p. 160, "more so the larger is ζ" / "more so the smaller is ζ": for each
`ι ∈ (0, 1)` the curve is strictly decreasing in `ζ`, so its distance below the chord `1 − ι`
(for `ζ > 1`) grows with `ζ` and its distance above the chord (for `ζ < 1`) grows as `ζ` falls. -/
theorem fig31_antitone_zeta {ι : ℝ} (h0 : 0 < ι) (h1 : ι < 1) :
    StrictAntiOn (fun ζ => fig31 ζ ι) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hda := fig31_den_pos ha h0.le h1.le
  have hdb := fig31_den_pos hb h0.le h1.le
  unfold fig31
  apply div_lt_div_of_pos_left (by linarith) hda
  nlinarith

/-- Woodford (2003), p. 160: below the chord for `ζ > 1`, above it for `ζ < 1`, on `(0, 1)`. -/
theorem fig31_vs_chord {ζ ι : ℝ} (hζ : 0 < ζ) (h0 : 0 < ι) (h1 : ι < 1) :
    (1 < ζ → fig31 ζ ι < 1 - ι) ∧ (ζ < 1 → 1 - ι < fig31 ζ ι) := by
  constructor
  · intro h
    have := fig31_antitone_zeta h0 h1 (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr hζ) h
    simpa [fig31_linear] using this
  · intro h
    have := fig31_antitone_zeta h0 h1 (Set.mem_Ioi.mpr hζ) (Set.mem_Ioi.mpr one_pos) h
    simpa [fig31_linear] using this

/-- Woodford (2003), p. 160: "a larger number of flexible prices (larger ι) implies a higher
value of κ": `κ(ι)` is strictly increasing on `[0, 1)` for `ζ > 0`. -/
theorem kappaNC_strictMonoOn {ζ : ℝ} (hζ : 0 < ζ) : StrictMonoOn (fun ι => kappaNC ι ζ)
    (Set.Ico 0 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ico] at ha hb
  unfold kappaNC
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Woodford (2003), p. 160: "in the limit as ι approaches one, κ becomes unboundedly large". -/
theorem kappaNC_tendsto_atTop {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun ι => kappaNC ι ζ) (𝓝[<] 1) atTop := by
  have h1 : Tendsto (fun ι : ℝ => 1 - ι) (𝓝[<] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun ι : ℝ => 1 - ι) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_const.sub continuous_id).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio] at hx
      simp only [Set.mem_Ioi]
      linarith
  have h2 := tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun ι : ℝ => ι * ζ) (𝓝[<] 1) (𝓝 (1 * ζ)) :=
    ((continuous_id.mul continuous_const).tendsto 1).mono_left nhdsWithin_le_nhds
  have := h3.pos_mul_atTop (by simpa using hζ) h2
  refine this.congr fun ι => ?_
  simp [kappaNC, div_eq_mul_inv]

/-- Woodford (2003), p. 160: "the output effects of variations in nominal spending approach
zero" as `ι → 1`. -/
theorem outputElasticity_tendsto_zero {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun ι => outputElasticity ι ζ) (𝓝[<] 1) (𝓝 0) := by
  have := (tendsto_atTop_add_const_left _ 1 (kappaNC_tendsto_atTop hζ)).inv_tendsto_atTop
  refine this.congr fun ι => ?_
  simp [outputElasticity]


end Woodford.NominalRigidities.Predetermined
