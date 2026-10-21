/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.Ex5_1
import DiscretionCommitment.Ex5_4
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Topology.Order.IntermediateValue

/-!
# Exercise 5.5: optimal steady-state inflation and the zero lower bound

Galí (2015), Chapter 5, Exercise 5.5, p. 162. The model is
`x_t = E_t x_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ρ) + z_t` (`Ex5_1.DIS`) and
`π_t − π̄ = β E_t(π_{t+1} − π̄) + κ x_t + u_t` (`NKPCbar`), with independent, serially
uncorrelated normal shocks `z_t ~ N(0, σ_z²)`, `u_t ~ N(0, σ_u²)`, and the loss
`π̄ + E_0 ∑ βᵗ (ϑ x_t² + (π_t − π̄)²)`.

## (a) Discretion and the choice of `π̄`
* `ex5_5a_period_optimal`: the targeting rule `x_t = −(κ/ϑ)(π_t − π̄)` solves each period's
  problem (taking `β E_t(π_{t+1} − π̄) + u_t` as given).
* `ex5_5a_exists`, `ex5_5a_unique`: for every `π̄` the discretionary equilibrium is
  `x_t = −κu_t/(ϑ+κ²)`, `π_t = π̄ + ϑu_t/(ϑ+κ²)`, `i_t = ρ + π̄ + σz_t + σκu_t/(ϑ+κ²)`, unique among
  equilibria at a bounded distance (normal shocks are unbounded, so Galí's "bounded" convention
  is applied to deviations). Only `E_t u_{t+1} = 0` is used.
* `ex5_5a_loss_diff`: the stabilisation part of the loss does not depend on `π̄`, so the total
  loss is `π̄` plus a constant.
* With a genuine Gaussian law (`GaussianShocks`; `hasLaw_affine`, `hasLaw_rate`):
  `i_t ~ N(ρ + π̄, s²)`, `s² = σ²σ_z² + (σκ/(ϑ+κ²))² σ_u²` (`rateVar`), and
  `ex5_5a_prob`: `P(i_t < 0) = Φ(−(ρ + π̄)/s)` (`prob_neg`), `Φ = cdf N(0,1)` (`Phi`).
* The quantile `z_{0.05}` (`z05`) is constructed: `Φ` is continuous (`phi_continuous`, no atoms),
  strictly increasing (`phi_strictMono`, positive density) with limits 0 and 1, so by the
  intermediate value theorem `Φ(q) = 0.05` has a solution (`exists_quantile`), unique
  (`eq_z05_iff`).
* `ex5_5a`: with `π̄* = −ρ − s z_{0.05}` (`piStar`), the zero bound binds with probability exactly
  5%; the constraint `P(i_t < 0) ≤ 5%` holds iff `π̄ ≥ π̄*` (`constraint_iff`); and `π̄*` is the
  unique loss-minimising feasible steady-state inflation rate (the book's linear cost `π̄` puts no
  sign restriction on `π̄`; `π̄* < 0` when `ρ > s |z_{0.05}|`).

## (b) An implementing rule
`i_t = ρ + π̄ + σ z_t + ψ_u u_t + φ_π(π_t − π̄)`, `ψ_u = (σκ − φ_πϑ)/(ϑ + κ²)` (`RuleB`, `psiU`):
`ex5_5b_exists` (the allocation of (a) is an equilibrium), `ex5_5b_unique` (for `φ_π > 1` it is
the unique equilibrium with adapted `x, π` at a bounded distance, via the determinacy result of
Exercise 5.1), `ex5_5b_not_unique` (for `0 ≤ φ_π ≤ 1` it is not).

## Non-vacuity
`shockMeasure`, `concreteShocks`: the i.i.d. product law on `ℕ → ℝ × ℝ`; `truncE`: an
expectation system on it under which the shocks are i.i.d. (`concrete_iid`);
`ex5_5_nonvacuous`: there the equilibrium under `π̄*` exists and `P(i_t < 0) = 5%` exactly.
-/

namespace Gali.DiscretionCommitment.Ex5_5

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-! ### The standard normal distribution function and its 5% quantile -/

/-- Galí (2015), Exercise 5.5(a), p. 162: the standard normal distribution function
`Φ = cdf N(0, 1)`. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Galí (2015), Exercise 5.5(a): `Φ` is continuous (the normal law has no atoms). -/
theorem phi_continuous : Continuous Phi := by
  have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) one_ne_zero
  rw [continuous_iff_continuousAt]
  intro a
  have hsing : (cdf (gaussianReal 0 1)).measure {a} = 0 := by
    rw [measure_cdf]; exact measure_singleton a
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hsing
  have hle := (cdf (gaussianReal 0 1)).mono.leftLim_le (le_refl a)
  have heq : Function.leftLim (cdf (gaussianReal 0 1)) a = cdf (gaussianReal 0 1) a :=
    le_antisymm hle (by linarith)
  unfold Phi
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · rw [← continuousWithinAt_Iio_iff_Iic]
    exact ((cdf (gaussianReal 0 1)).mono.continuousWithinAt_Iio_iff_leftLim_eq).2 heq
  · exact (cdf (gaussianReal 0 1)).right_continuous a

/-- Galí (2015), Exercise 5.5(a): `Φ` is strictly increasing (the normal density is
positive). -/
theorem phi_strictMono : StrictMono Phi := by
  intro a b hab
  have h1 : (cdf (gaussianReal 0 1)).measure (Set.Ioc a b) = ENNReal.ofReal (Phi b - Phi a) :=
    StieltjesFunction.measure_Ioc _ a b
  rw [measure_cdf] at h1
  have h2 : gaussianReal 0 1 (Set.Ioc a b) ≠ 0 := by
    intro h
    have := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at this
    linarith
  rw [h1, ne_eq, ENNReal.ofReal_eq_zero, not_le] at h2
  linarith

/-- Galí (2015), Exercise 5.5(a): every level `α ∈ (0, 1)` is attained by `Φ` (intermediate
value theorem). -/
theorem exists_quantile {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : ∃ q, Phi q = α := by
  obtain ⟨a, ha⟩ :=
    ((tendsto_cdf_atBot (μ := gaussianReal 0 1)).eventually (gt_mem_nhds h0)).exists
  obtain ⟨b, hb⟩ :=
    ((tendsto_cdf_atTop (μ := gaussianReal 0 1)).eventually (lt_mem_nhds h1)).exists
  have ha' : Phi a < α := ha
  have hb' : α < Phi b := hb
  have hab : a ≤ b := by
    by_contra h
    have := phi_strictMono.monotone (le_of_lt (not_le.mp h))
    linarith
  obtain ⟨q, -, hq⟩ := intermediate_value_Icc hab phi_continuous.continuousOn ⟨ha'.le, hb'.le⟩
  exact ⟨q, hq⟩

/-- Galí (2015), Exercise 5.5(a): the 5% quantile `z_{0.05}` of the standard normal
distribution, `Φ(z_{0.05}) = 0.05`. -/
noncomputable def z05 : ℝ :=
  Classical.choose (exists_quantile (α := 1 / 20) (by norm_num) (by norm_num))

/-- Galí (2015), Exercise 5.5(a): `Φ(z_{0.05}) = 1/20`. -/
theorem phi_z05 : Phi z05 = 1 / 20 :=
  Classical.choose_spec (exists_quantile (α := 1 / 20) (by norm_num) (by norm_num))

/-- Galí (2015), Exercise 5.5(a): `z_{0.05}` is the unique solution of `Φ(q) = 1/20`. -/
theorem eq_z05_iff (q : ℝ) : Phi q = 1 / 20 ↔ q = z05 := by
  constructor
  · intro h
    exact phi_strictMono.injective (h.trans phi_z05.symm)
  · rintro rfl
    exact phi_z05

/-! ### Laws -/

variable {Ω : Type*}

/-- Galí (2015), Exercise 5.5(a): if `Z ~ N(0, σ_z²)` and `U ~ N(0, σ_u²)` are independent, then
`c + a Z + b U ~ N(c, a² σ_z² + b² σ_u²)`. -/
theorem hasLaw_affine [MeasurableSpace Ω] {μ : Measure Ω} {Z U : Ω → ℝ} {vz vu : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal 0 vz) μ) (hU : HasLaw U (gaussianReal 0 vu) μ)
    (hI : IndepFun Z U μ) (a b c : ℝ) :
    HasLaw (fun ω => c + (a * Z ω + b * U ω))
      (gaussianReal c (⟨a ^ 2, sq_nonneg a⟩ * vz + ⟨b ^ 2, sq_nonneg b⟩ * vu)) μ := by
  have hX := gaussianReal_const_mul hZ a
  have hY := gaussianReal_const_mul hU b
  have hI' : IndepFun (fun ω => a * Z ω) (fun ω => b * U ω) μ :=
    hI.comp (measurable_const_mul a) (measurable_const_mul b)
  have hmap := gaussianReal_add_gaussianReal_of_indepFun hI' hX hY
  have hS : HasLaw ((fun ω => a * Z ω) + fun ω => b * U ω)
      (gaussianReal (a * 0 + b * 0) (⟨a ^ 2, sq_nonneg a⟩ * vz + ⟨b ^ 2, sq_nonneg b⟩ * vu)) μ :=
    ⟨hX.aemeasurable.add hY.aemeasurable, hmap⟩
  have := gaussianReal_const_add hS c
  simpa using this

/-- Galí (2015), Exercise 5.5(a): for `X ~ N(c, v)` with `v ≠ 0`,
`P(X < 0) = Φ(−c/√v)`. -/
theorem prob_neg [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal c v) μ) :
    μ.real {ω | X ω < 0} = Phi (-c / Real.sqrt v) := by
  rw [hX.measureReal_eq (p := fun x => x < 0) measurableSet_Iio]
  have := nullSingletonClass_gaussianReal (μ := c) hv
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))
  have h1 : (gaussianReal c v).real {x : ℝ | x < 0} = (gaussianReal c v).real (Set.Iic 0) := by
    simp only [measureReal_def]
    rw [show {x : ℝ | x < 0} = Set.Iio 0 from rfl, measure_congr Iio_ae_eq_Iic]
  have hmap : (gaussianReal 0 1).map (fun x => c + Real.sqrt v * x) = gaussianReal c v := by
    have e1 := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
    rw [show (fun x => c + Real.sqrt v * x) = (fun x => c + x) ∘ (fun x => Real.sqrt v * x)
      from rfl, ← Measure.map_map (measurable_const_add c) (measurable_const_mul _), e1,
      gaussianReal_map_const_add]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt (NNReal.coe_nonneg v)]
  rw [h1, ← hmap,
    map_measureReal_apply (by fun_prop) measurableSet_Iic, Phi, cdf_eq_real]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  rw [le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

/-! ### The model and the discretionary equilibrium -/

variable (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 5.5, p. 162: the Phillips curve around steady-state inflation `π̄`,
`π_t − π̄ = β E_t(π_{t+1} − π̄) + κ x_t + u_t`. -/
def NKPCbar (β κ πbar : ℝ) (x p u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t - (fun _ => πbar) = β • 𝔼.E t (p (t + 1) - fun _ => πbar) + κ • x t + u t

/-- Galí (2015), Exercise 5.5(a): the discretionary targeting rule `x_t = −(κ/ϑ)(π_t − π̄)`. -/
def Targeting (κ ϑ πbar : ℝ) (x p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = -(κ / ϑ) • (p t - fun _ => πbar)

/-- Galí (2015), Exercise 5.5(a): the discretionary equilibrium given `π̄`: the IS curve
(`Ex5_1.DIS`), the Phillips curve and the targeting rule. -/
def DiscEq (β σ κ ϑ ρ πbar : ℝ) (z u x p i : ℕ → Ω → ℝ) : Prop :=
  Ex5_1.DIS 𝔼 σ ρ x p i z ∧ NKPCbar 𝔼 β κ πbar x p u ∧ Targeting κ ϑ πbar x p

/-- Galí (2015), Exercise 5.5(a): the discretionary output gap `x_t = −κ u_t/(ϑ + κ²)`. -/
noncomputable def xT (κ ϑ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (-κ / (ϑ + κ ^ 2)) • u t

/-- Galí (2015), Exercise 5.5(a): discretionary inflation `π_t = π̄ + ϑ u_t/(ϑ + κ²)`. -/
noncomputable def pT (κ ϑ πbar : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => πbar) + (ϑ / (ϑ + κ ^ 2)) • u t

/-- Galí (2015), Exercise 5.5(a): the discretionary nominal rate
`i_t = (ρ + π̄) + σ z_t + σκ u_t/(ϑ + κ²)`. -/
noncomputable def iT (σ κ ϑ ρ πbar : ℝ) (z u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (ρ + πbar) + (σ * z t ω + σ * κ / (ϑ + κ ^ 2) * u t ω)

/-- Galí (2015), Exercise 5.5(a): with i.i.d. shocks the expectations of the discretionary
variables are `E_t x_{t+1} = 0`, `E_t π_{t+1} = π̄`. -/
theorem E_targets {κ ϑ πbar : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 0 u) (t : ℕ) :
    𝔼.E t (xT κ ϑ u (t + 1)) = 0 ∧ 𝔼.E t (pT κ ϑ πbar u (t + 1)) = fun _ => πbar := by
  have hEu : 𝔼.E t (u (t + 1)) = 0 := by rw [hu.2 t, zero_smul]
  constructor
  · simp only [xT, map_smul, hEu, smul_zero]
  · simp only [pT, map_add, map_smul, hEu, smul_zero, add_zero, 𝔼.const]

/-- **Exercise 5.5(a), existence** (Galí 2015, p. 162): with i.i.d. shocks, `x_t = −κu_t/(ϑ+κ²)`,
`π_t = π̄ + ϑu_t/(ϑ+κ²)`, `i_t = ρ + π̄ + σ z_t + σκ u_t/(ϑ+κ²)` is a discretionary equilibrium,
for every `π̄`. -/
theorem ex5_5a_exists {β σ κ ϑ ρ πbar : ℝ} (hσ : σ ≠ 0) (hϑ : 0 < ϑ) {z u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) :
    DiscEq 𝔼 β σ κ ϑ ρ πbar z u (xT κ ϑ u) (pT κ ϑ πbar u) (iT σ κ ϑ ρ πbar z u) := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · obtain ⟨h1, h2⟩ := E_targets 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu t
    rw [h1, h2]
    funext ω
    simp only [xT, iT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  · obtain ⟨-, h2⟩ := E_targets 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu t
    rw [map_sub, h2, 𝔼.const, sub_self]
    funext ω
    simp only [xT, pT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    field_simp
    ring
  · funext ω
    simp only [xT, pT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- **Exercise 5.5(a), period optimality** (Galí 2015, p. 162): in a discretionary equilibrium,
at every date and state, `(x_t, π_t − π̄)` minimises `ϑ x² + (π − π̄)²` over the choices
`π − π̄ = κ x + v_t`, `v_t = β E_t(π_{t+1} − π̄) + u_t` taken as given. -/
theorem ex5_5a_period_optimal {β σ κ ϑ ρ πbar : ℝ} (hϑ : 0 < ϑ) {z u x p i : ℕ → Ω → ℝ}
    (he : DiscEq 𝔼 β σ κ ϑ ρ πbar z u x p i) (t : ℕ) (ω : Ω) (x' : ℝ) :
    ϑ * x t ω ^ 2 + (p t ω - πbar) ^ 2 ≤
      ϑ * x' ^ 2 + (κ * x' + (β * 𝔼.E t (p (t + 1) - fun _ => πbar) ω + u t ω)) ^ 2 := by
  have h1 := congrFun (he.2.1 t) ω
  have h2 := congrFun (he.2.2 t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  set v := β * 𝔼.E t (p (t + 1) - fun _ => πbar) ω + u t ω
  have hp : p t ω - πbar = κ * x t ω + v := by rw [h1]; ring
  have hx : x t ω = Ex5_4.periodOpt ϑ κ v :=
    (Ex5_4.period_targeting_iff hϑ).mpr (by rw [← hp]; exact h2)
  rw [hp]
  exact (Ex5_4.period_opt_iff hϑ).mpr hx x'

/-- **Exercise 5.5(a), uniqueness** (Galí 2015, p. 162): every discretionary equilibrium whose
inflation differs from `π̄ + ϑu/(ϑ+κ²)` by a bounded process is the one above (normal shocks
are unbounded, so uniqueness is stated for bounded deviations). -/
theorem ex5_5a_unique {β σ κ ϑ ρ πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : σ ≠ 0)
    (hκ : κ ≠ 0) (hϑ : 0 < ϑ) {z u x p i : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) (he : DiscEq 𝔼 β σ κ ϑ ρ πbar z u x p i)
    (hb : BoundedProc (p - pT κ ϑ πbar u)) :
    x = xT κ ϑ u ∧ p = pT κ ϑ πbar u ∧ i = iT σ κ ϑ ρ πbar z u := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  set a := ϑ * β / (ϑ + κ ^ 2)
  have ha : |a| < 1 := by
    rw [abs_of_nonneg (by positivity), div_lt_one hK]
    nlinarith [pow_pos (abs_pos.mpr hκ) 2, sq_abs κ]
  have hEp : ∀ t, 𝔼.E t (pT κ ϑ πbar u (t + 1)) = fun _ => πbar := fun t =>
    (E_targets 𝔼 hu t).2
  have hd : ∀ t, (p - pT κ ϑ πbar u) t =
      a • 𝔼.E t ((p - pT κ ϑ πbar u) (t + 1)) + (0 : ℕ → Ω → ℝ) t := by
    intro t
    funext ω
    have e1 := congrFun (he.2.1 t) ω
    have e2 := congrFun (he.2.2 t) ω
    have e3 := congrFun (hEp t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, 𝔼.const]
      at e1 e2 e3 ⊢
    rw [e3]
    simp only [pT, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
    rw [e2] at e1
    simp only [a]
    field_simp
    have hinv : ϑ * ϑ⁻¹ = 1 := mul_inv_cancel₀ hϑ.ne'
    linear_combination ϑ * e1 - (p t ω - πbar) * κ ^ 2 * hinv
  have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = a • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + (0 : ℕ → Ω → ℝ) t :=
    fun t => by simp
  have hzero := 𝔼.forward_unique ha hd h0 hb ⟨0, fun _ _ => by simp⟩
  have hp : p = pT κ ϑ πbar u := sub_eq_zero.mp hzero
  have hx : x = xT κ ϑ u := by
    funext t
    rw [he.2.2 t, hp]
    funext ω
    simp only [xT, pT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  refine ⟨hx, hp, ?_⟩
  funext t ω
  have e1 := congrFun (he.1 t) ω
  obtain ⟨h1, h2⟩ := E_targets 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu t
  rw [hx, hp, h1, h2] at e1
  simp only [xT, iT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at e1 ⊢
  have hinv : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  linear_combination σ * e1 - (i t ω - πbar - ρ) * hinv

/-- **Exercise 5.5(a), the loss** (Galí 2015, p. 162): for any stabilisation loss functional
`L(x, π − π̄)` (e.g. `E_0 ∑ βᵗ(ϑ x_t² + (π_t − π̄)²)`), the total loss `π̄ + L` of the
discretionary equilibria under two steady-state inflation rates differs exactly by the
difference of the rates: the stabilisation component does not depend on `π̄`. -/
theorem ex5_5a_loss_diff {β σ κ ϑ ρ πbar πbar' : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : σ ≠ 0)
    (hκ : κ ≠ 0) (hϑ : 0 < ϑ) {z u x p i x' p' i' : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) (he : DiscEq 𝔼 β σ κ ϑ ρ πbar z u x p i)
    (hb : BoundedProc (p - pT κ ϑ πbar u)) (he' : DiscEq 𝔼 β σ κ ϑ ρ πbar' z u x' p' i')
    (hb' : BoundedProc (p' - pT κ ϑ πbar' u))
    (L : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → ℝ) :
    (πbar + L x (fun t => p t - fun _ => πbar)) - (πbar' + L x' (fun t => p' t - fun _ => πbar'))
      = πbar - πbar' := by
  obtain ⟨hx, hp, -⟩ := ex5_5a_unique 𝔼 hβ0 hβ1 hσ hκ hϑ hu he hb
  obtain ⟨hx', hp', -⟩ := ex5_5a_unique 𝔼 hβ0 hβ1 hσ hκ hϑ hu he' hb'
  have e : (fun t => p t - fun _ => πbar) = fun t => p' t - fun _ => πbar' := by
    rw [hp, hp']
    funext t
    simp only [pT, add_sub_cancel_left]
  rw [e, hx, hx']
  ring

/-! ### (b) An implementing rule -/

/-- Galí (2015), Exercise 5.5(b), p. 162: the interest-rate rule
`i_t = ρ + π̄ + σ z_t + ψ_u u_t + φ_π (π_t − π̄)`. -/
def RuleB (ρ πbar σ φ ψu : ℝ) (z u p i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = fun ω => ρ + πbar + σ * z t ω + ψu * u t ω + φ * (p t ω - πbar)

/-- Galí (2015), Exercise 5.5(b): the coefficient `ψ_u = (σκ − φ_π ϑ)/(ϑ + κ²)` that makes the
rule consistent with the discretionary allocation. -/
noncomputable def psiU (σ κ ϑ φ : ℝ) : ℝ := (σ * κ - φ * ϑ) / (ϑ + κ ^ 2)

/-- Galí (2015), Exercise 5.5(b): an equilibrium under the rule: the IS curve, the Phillips
curve and the rule. -/
def EqB (β σ κ ρ πbar φ ψu : ℝ) (z u x p i : ℕ → Ω → ℝ) : Prop :=
  Ex5_1.DIS 𝔼 σ ρ x p i z ∧ NKPCbar 𝔼 β κ πbar x p u ∧ RuleB ρ πbar σ φ ψu z u p i

/-- **Exercise 5.5(b), existence** (Galí 2015, p. 162): the discretionary allocation of (a),
with its nominal rate, is an equilibrium under the rule with `ψ_u = (σκ − φ_π ϑ)/(ϑ + κ²)`, for
every `φ_π`. -/
theorem ex5_5b_exists {β σ κ ϑ ρ πbar φ : ℝ} (hσ : σ ≠ 0) (hϑ : 0 < ϑ) {z u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) :
    EqB 𝔼 β σ κ ρ πbar φ (psiU σ κ ϑ φ) z u (xT κ ϑ u) (pT κ ϑ πbar u)
      (iT σ κ ϑ ρ πbar z u) := by
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  obtain ⟨h1, h2, -⟩ := ex5_5a_exists 𝔼 (β := β) (ρ := ρ) (πbar := πbar) (z := z) hσ hϑ hu
  refine ⟨h1, h2, fun t => ?_⟩
  funext ω
  simp only [iT, pT, psiU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Galí (2015), Exercise 5.5(b): the difference of two equilibria under the rule solves the
homogeneous system of Exercise 5.1 (`Ex5_1.HomEq`). -/
theorem eqB_sub {β σ κ ρ πbar φ ψu : ℝ} {z u x p i x' p' i' : ℕ → Ω → ℝ}
    (h : EqB 𝔼 β σ κ ρ πbar φ ψu z u x p i) (h' : EqB 𝔼 β σ κ ρ πbar φ ψu z u x' p' i') :
    Ex5_1.HomEq 𝔼 β σ κ φ (x - x') (p - p') := by
  obtain ⟨hd, hn, hr⟩ := h
  obtain ⟨hd', hn', hr'⟩ := h'
  intro t
  constructor
  · funext ω
    have e1 := congrFun (hd t) ω
    have e2 := congrFun (hd' t) ω
    have r1 := congrFun (hr t) ω
    have r2 := congrFun (hr' t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub] at e1 e2 r1 r2 ⊢
    rw [e1, e2, r1, r2]
    ring
  · funext ω
    have e1 := congrFun (hn t) ω
    have e2 := congrFun (hn' t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub, 𝔼.const]
      at e1 e2 ⊢
    linear_combination e1 - e2

/-- Galí (2015), Exercise 5.5(b): adding a solution of the homogeneous system to an equilibrium
under the rule (and moving the rate by `φ_π dπ`) gives another equilibrium. -/
theorem eqB_add_hom {β σ κ ρ πbar φ ψu : ℝ} {z u x p i dx dp : ℕ → Ω → ℝ}
    (h : EqB 𝔼 β σ κ ρ πbar φ ψu z u x p i) (hd : Ex5_1.HomEq 𝔼 β σ κ φ dx dp) :
    EqB 𝔼 β σ κ ρ πbar φ ψu z u (x + dx) (p + dp) (i + fun t => φ • dp t) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω
    have e1 := congrFun (h1 t) ω
    have e2 := congrFun (hd t).1 ω
    have r := congrFun (h3 t) ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add] at e1 e2 r ⊢
    rw [e1, e2]
    ring
  · funext ω
    have e1 := congrFun (h2 t) ω
    have e2 := congrFun (hd t).2 ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub,
      𝔼.const] at e1 e2 ⊢
    linear_combination e1 + e2
  · funext ω
    have r := congrFun (h3 t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at r ⊢
    rw [r]
    ring

/-- Galí (2015), Exercise 5.5(b): the discretionary output gap and inflation are adapted. -/
theorem targets_adapted {κ ϑ πbar : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) :
    𝔼.Adapted (xT κ ϑ u) ∧ 𝔼.Adapted (pT κ ϑ πbar u) :=
  ⟨fun t => by simp only [xT, map_smul, hu t],
    fun t => by simp only [pT, map_add, map_smul, hu t, 𝔼.const]⟩

/-- **Exercise 5.5(b), determinacy** (Galí 2015, p. 162): for `φ_π > 1`, the discretionary
allocation is the unique equilibrium under the rule among those with adapted `x, π` at a
bounded distance from it. -/
theorem ex5_5b_unique {β σ κ ϑ ρ πbar φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hϑ : 0 < ϑ) (hφ : 1 < φ) {z u x p i : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 0 u)
    (he : EqB 𝔼 β σ κ ρ πbar φ (psiU σ κ ϑ φ) z u x p i) (hax : 𝔼.Adapted x)
    (hap : 𝔼.Adapted p) (hbx : BoundedProc (x - xT κ ϑ u))
    (hbp : BoundedProc (p - pT κ ϑ πbar u)) :
    x = xT κ ϑ u ∧ p = pT κ ϑ πbar u ∧ i = iT σ κ ϑ ρ πbar z u := by
  have hD : 0 < σ + κ * φ := by nlinarith
  have hK : 0 < ϑ + κ ^ 2 := by positivity
  have hS := (Ex5_1.schurStable_A_iff hσ hκ hβ0 hβ1 (by linarith)).mpr hφ
  have hhom := eqB_sub 𝔼 he (ex5_5b_exists 𝔼 (β := β) (ρ := ρ) (πbar := πbar) (φ := φ) (z := z)
    hσ.ne' hϑ hu)
  have hsol := (Ex5_1.homEq_iff_solves 𝔼 hσ.ne' hD.ne' _ _).mp hhom
  obtain ⟨hxa, hpa⟩ := targets_adapted 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu.1
  have had := Ex5_1.adaptedVec_stack 𝔼 (x := x - xT κ ϑ u) (p := p - pT κ ϑ πbar u)
    (fun t => by simp only [Pi.sub_apply, map_sub, hax t, hxa t])
    (fun t => by simp only [Pi.sub_apply, map_sub, hap t, hpa t])
  have h0 : 𝔼.Solves (Ex5_1.A β σ κ φ) 0 0 := fun t i => by simp
  have heq := 𝔼.system_unique hS hsol h0 had (fun t i => by simp)
    (Ex5_1.boundedVec_stack hbx hbp) ⟨0, fun t i ω => by simp⟩
  have hx : x = xT κ ϑ u := by
    funext t
    have := congrFun (congrFun heq t) 0
    simpa [Ex5_1.stack, sub_eq_zero] using this
  have hp : p = pT κ ϑ πbar u := by
    funext t
    have := congrFun (congrFun heq t) 1
    simpa [Ex5_1.stack, sub_eq_zero] using this
  refine ⟨hx, hp, ?_⟩
  funext t ω
  rw [he.2.2 t, hp]
  simp only [iT, pT, psiU, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- **Exercise 5.5(b), indeterminacy for `φ_π ≤ 1`** (Galí 2015, p. 162): for `0 ≤ φ_π ≤ 1`
there is another equilibrium under the rule, with adapted `x, π` at a bounded distance from
the discretionary allocation. -/
theorem ex5_5b_not_unique [Nonempty Ω] {β σ κ ϑ ρ πbar φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) {z u : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 0 u) :
    ∃ x p i, EqB 𝔼 β σ κ ρ πbar φ (psiU σ κ ϑ φ) z u x p i ∧ 𝔼.Adapted x ∧ 𝔼.Adapted p ∧
      BoundedProc (x - xT κ ϑ u) ∧ BoundedProc (p - pT κ ϑ πbar u) ∧
      ¬ (x = xT κ ϑ u ∧ p = pT κ ϑ πbar u) := by
  have hD : 0 < σ + κ * φ := by positivity
  have hS : ¬ SchurStable (tr2 (Ex5_1.A β σ κ φ)) (det2 (Ex5_1.A β σ κ φ)) := by
    rw [Ex5_1.schurStable_A_iff hσ hκ hβ0 hβ1 hφ0]; linarith
  have h0 : 𝔼.Solves (Ex5_1.A β σ κ φ) 0 0 := fun t i => by simp
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ :=
    𝔼.system_not_unique hS h0 (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
  have hst : Ex5_1.stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t i
    fin_cases i <;> rfl
  have hhom : Ex5_1.HomEq 𝔼 β σ κ φ (fun t => y t 0) (fun t => y t 1) :=
    (Ex5_1.homEq_iff_solves 𝔼 hσ.ne' hD.ne' _ _).mpr (by rw [hst]; exact hy)
  obtain ⟨hxa, hpa⟩ := targets_adapted 𝔼 (κ := κ) (ϑ := ϑ) (πbar := πbar) hu.1
  refine ⟨xT κ ϑ u + fun t => y t 0, pT κ ϑ πbar u + fun t => y t 1, _,
    eqB_add_hom 𝔼 (ex5_5b_exists 𝔼 hσ.ne' hϑ hu) hhom,
    fun t => by simp only [Pi.add_apply, map_add, hxa t, hay t 0],
    fun t => by simp only [Pi.add_apply, map_add, hpa t, hay t 1],
    ⟨M, fun t ω => by simpa using hM t 0 ω⟩, ⟨M, fun t ω => by simpa using hM t 1 ω⟩, ?_⟩
  rintro ⟨h1, h2⟩
  apply hne
  funext t i
  fin_cases i
  · funext ω
    have := congrFun (congrFun h1 t) ω
    simpa using this
  · funext ω
    have := congrFun (congrFun h2 t) ω
    simpa using this

/-! ### Normal shocks and the zero lower bound -/

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- Galí (2015), Exercise 5.5, p. 162: normal shocks on a probability space: at every date
`z_t ~ N(0, σ_z²)` and `u_t ~ N(0, σ_u²)` are independent. -/
structure GaussianShocks where
  /-- The demand shock `z_t`. -/
  z : ℕ → Ω → ℝ
  /-- The cost-push shock `u_t`. -/
  u : ℕ → Ω → ℝ
  /-- The variance `σ_z²`. -/
  vz : ℝ≥0
  /-- The variance `σ_u²`. -/
  vu : ℝ≥0
  /-- `z_t ~ N(0, σ_z²)`. -/
  lawZ : ∀ t, HasLaw (z t) (gaussianReal 0 vz) μ
  /-- `u_t ~ N(0, σ_u²)`. -/
  lawU : ∀ t, HasLaw (u t) (gaussianReal 0 vu) μ
  /-- `z_t` and `u_t` are independent. -/
  indep : ∀ t, IndepFun (z t) (u t) μ

/-- Galí (2015), Exercise 5.5(a): the variance of the nominal rate,
`s² = σ² σ_z² + (σκ/(ϑ + κ²))² σ_u²`. -/
noncomputable def rateVar (σ κ ϑ : ℝ) (vz vu : ℝ≥0) : ℝ≥0 :=
  ⟨σ ^ 2, sq_nonneg σ⟩ * vz + ⟨(σ * κ / (ϑ + κ ^ 2)) ^ 2, sq_nonneg _⟩ * vu

/-- Galí (2015), Exercise 5.5(a): the standard deviation `s` of the nominal rate. -/
noncomputable def rateSd (σ κ ϑ : ℝ) (vz vu : ℝ≥0) : ℝ := Real.sqrt (rateVar σ κ ϑ vz vu)

/-- **Exercise 5.5(a), the optimal steady-state inflation** (Galí 2015, p. 162):
`π̄* = −ρ − s z_{0.05}` (`z_{0.05} < 0`, so `π̄* = s |z_{0.05}| − ρ`). -/
noncomputable def piStar (σ κ ϑ ρ : ℝ) (vz vu : ℝ≥0) : ℝ := -ρ - rateSd σ κ ϑ vz vu * z05

variable {μ}

/-- **Exercise 5.5(a), the law of the nominal rate** (Galí 2015, p. 162): in the discretionary
equilibrium `i_t ~ N(ρ + π̄, s²)`. -/
theorem hasLaw_rate (S : GaussianShocks μ) (σ κ ϑ ρ πbar : ℝ) (t : ℕ) :
    HasLaw (iT σ κ ϑ ρ πbar S.z S.u t) (gaussianReal (ρ + πbar) (rateVar σ κ ϑ S.vz S.vu)) μ :=
  hasLaw_affine (S.lawZ t) (S.lawU t) (S.indep t) σ (σ * κ / (ϑ + κ ^ 2)) (ρ + πbar)

/-- **Exercise 5.5(a), the probability of the zero bound** (Galí 2015, p. 162): in every
discretionary equilibrium (with bounded deviation), `P(i_t < 0) = Φ(−(ρ + π̄)/s)` at every
date. -/
theorem ex5_5a_prob (S : GaussianShocks μ) {β σ κ ϑ ρ πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hv : rateVar σ κ ϑ S.vz S.vu ≠ 0)
    (hu : 𝔼.IsAR1 0 S.u) {x p i : ℕ → Ω → ℝ}
    (he : DiscEq 𝔼 β σ κ ϑ ρ πbar S.z S.u x p i) (hb : BoundedProc (p - pT κ ϑ πbar S.u))
    (t : ℕ) :
    μ.real {ω | i t ω < 0} = Phi (-(ρ + πbar) / rateSd σ κ ϑ S.vz S.vu) := by
  obtain ⟨-, -, hi⟩ := ex5_5a_unique 𝔼 hβ0 hβ1 hσ hκ hϑ hu he hb
  rw [hi]
  exact prob_neg hv (hasLaw_rate S σ κ ϑ ρ πbar t)

/-- Galí (2015), Exercise 5.5(a): `s > 0` when `s² ≠ 0`. -/
theorem rateSd_pos {σ κ ϑ : ℝ} {vz vu : ℝ≥0} (hv : rateVar σ κ ϑ vz vu ≠ 0) :
    0 < rateSd σ κ ϑ vz vu :=
  Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv))

/-- **Exercise 5.5(a), the constraint** (Galí 2015, p. 162): `Φ(−(ρ + π̄)/s) ≤ 0.05` iff
`π̄ ≥ π̄*`, with equality iff `π̄ = π̄*`. -/
theorem constraint_iff {σ κ ϑ ρ πbar : ℝ} {vz vu : ℝ≥0} (hv : rateVar σ κ ϑ vz vu ≠ 0) :
    (Phi (-(ρ + πbar) / rateSd σ κ ϑ vz vu) ≤ 1 / 20 ↔ piStar σ κ ϑ ρ vz vu ≤ πbar) ∧
      (Phi (-(ρ + πbar) / rateSd σ κ ϑ vz vu) = 1 / 20 ↔ πbar = piStar σ κ ϑ ρ vz vu) := by
  have hs := rateSd_pos hv
  constructor
  · rw [← phi_z05, phi_strictMono.le_iff_le, div_le_iff₀ hs, piStar]
    constructor <;> intro h <;> nlinarith
  · rw [eq_z05_iff, div_eq_iff hs.ne', piStar]
    constructor <;> intro h <;> linarith

/-- **Exercise 5.5(a), optimal steady-state inflation** (Galí 2015, p. 162): with normal shocks
and `s > 0`, choose `π̄* = −ρ − s z_{0.05}`. Then (i) under `π̄*` the zero bound binds with
probability exactly 5% at every date; (ii) a discretionary equilibrium under `π̄` satisfies
the 5% constraint iff `π̄ ≥ π̄*`; (iii) among those, `π̄*` has the lowest total loss
`π̄ + L(x, π − π̄)`, strictly lower unless `π̄ = π̄*`. -/
theorem ex5_5a (S : GaussianShocks μ) {β σ κ ϑ ρ πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hϑ : 0 < ϑ) (hv : rateVar σ κ ϑ S.vz S.vu ≠ 0)
    (hu : 𝔼.IsAR1 0 S.u) {x p i x' p' i' : ℕ → Ω → ℝ}
    (he : DiscEq 𝔼 β σ κ ϑ ρ (piStar σ κ ϑ ρ S.vz S.vu) S.z S.u x p i)
    (hb : BoundedProc (p - pT κ ϑ (piStar σ κ ϑ ρ S.vz S.vu) S.u))
    (he' : DiscEq 𝔼 β σ κ ϑ ρ πbar S.z S.u x' p' i') (hb' : BoundedProc (p' - pT κ ϑ πbar S.u))
    (L : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → ℝ) (t : ℕ) :
    μ.real {ω | i t ω < 0} = 1 / 20 ∧
      (μ.real {ω | i' t ω < 0} ≤ 1 / 20 ↔ piStar σ κ ϑ ρ S.vz S.vu ≤ πbar) ∧
      (μ.real {ω | i' t ω < 0} ≤ 1 / 20 →
        piStar σ κ ϑ ρ S.vz S.vu + L x (fun t => p t - fun _ => piStar σ κ ϑ ρ S.vz S.vu) ≤
          πbar + L x' (fun t => p' t - fun _ => πbar) ∧
        (piStar σ κ ϑ ρ S.vz S.vu + L x (fun t => p t - fun _ => piStar σ κ ϑ ρ S.vz S.vu) =
          πbar + L x' (fun t => p' t - fun _ => πbar) → πbar = piStar σ κ ϑ ρ S.vz S.vu)) := by
  rw [ex5_5a_prob 𝔼 S hβ0 hβ1 hσ hκ hϑ hv hu he hb t,
    ex5_5a_prob 𝔼 S hβ0 hβ1 hσ hκ hϑ hv hu he' hb' t]
  have hd := ex5_5a_loss_diff 𝔼 hβ0 hβ1 hσ hκ hϑ hu he hb he' hb' L
  refine ⟨((constraint_iff hv).2).mpr rfl, (constraint_iff hv).1, fun hc => ?_⟩
  have hle := ((constraint_iff hv).1).mp hc
  constructor
  · linarith
  · intro h; linarith

/-! ### A concrete model (non-vacuity) -/

/-- Galí (2015), Exercise 5.5: truncation of a shock history at date `t` (later shocks are set
to their mean `0`). -/
def trunc (t : ℕ) (ω : ℕ → ℝ × ℝ) : ℕ → ℝ × ℝ := fun s => if s ≤ t then ω s else 0

/-- Galí (2015), Exercise 5.5: truncations compose, `trunc t ∘ trunc s = trunc s ∘ trunc t =
trunc s` for `s ≤ t`. -/
theorem trunc_trunc {s t : ℕ} (h : s ≤ t) (ω : ℕ → ℝ × ℝ) :
    trunc t (trunc s ω) = trunc s ω ∧ trunc s (trunc t ω) = trunc s ω := by
  constructor <;> funext k <;> simp only [trunc] <;> split_ifs <;> first | rfl | omega

/-- Galí (2015), Exercise 5.5: the certainty-equivalent expectation system on shock histories,
`E_t f(ω) = f(ω_0, …, ω_t, 0, 0, …)`. It satisfies all the axioms of `ExpectationSystem` (for
affine functions of the shocks it agrees with the conditional expectation under any law with
mean-zero independent shocks; that agreement is not needed and not proved here). -/
def truncE : ExpectationSystem (ℕ → ℝ × ℝ) where
  E t := LinearMap.funLeft ℝ ℝ (trunc t)
  const _ _ := rfl
  mono _ _ _ h ω := h _
  tower {s t} h x := by
    funext ω
    simp only [LinearMap.funLeft_apply]
    rw [(trunc_trunc h ω).1]
  known {s t} h x := by
    funext ω
    simp only [LinearMap.funLeft_apply]
    rw [(trunc_trunc h ω).2]

/-- Galí (2015), Exercise 5.5: the i.i.d. product law `⊗ₜ N(0, σ_z²) ⊗ N(0, σ_u²)` on shock
histories. -/
noncomputable abbrev shockMeasure (vz vu : ℝ≥0) : Measure (ℕ → ℝ × ℝ) :=
  Measure.infinitePi fun _ : ℕ => (gaussianReal 0 vz).prod (gaussianReal 0 vu)

/-- Galí (2015), Exercise 5.5: the date-`t` shock pair has the product normal law. -/
theorem hasLaw_pair (vz vu : ℝ≥0) (t : ℕ) :
    HasLaw (fun ω : ℕ → ℝ × ℝ => ω t) ((gaussianReal 0 vz).prod (gaussianReal 0 vu))
      (shockMeasure vz vu) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => (gaussianReal 0 vz).prod (gaussianReal 0 vu))
    t).hasLaw

/-- Galí (2015), Exercise 5.5: `z_t ~ N(0, σ_z²)` on the concrete space. -/
theorem hasLaw_z (vz vu : ℝ≥0) (t : ℕ) :
    HasLaw (fun ω : ℕ → ℝ × ℝ => (ω t).1) (gaussianReal 0 vz) (shockMeasure vz vu) :=
  HasLaw.comp (Y := Prod.fst)
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
    (hasLaw_pair vz vu t)

/-- Galí (2015), Exercise 5.5: `u_t ~ N(0, σ_u²)` on the concrete space. -/
theorem hasLaw_u (vz vu : ℝ≥0) (t : ℕ) :
    HasLaw (fun ω : ℕ → ℝ × ℝ => (ω t).2) (gaussianReal 0 vu) (shockMeasure vz vu) :=
  HasLaw.comp (Y := Prod.snd)
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
    (hasLaw_pair vz vu t)

/-- Galí (2015), Exercise 5.5: the concrete normal shocks. -/
noncomputable def concreteShocks (vz vu : ℝ≥0) : GaussianShocks (shockMeasure vz vu) where
  z t ω := (ω t).1
  u t ω := (ω t).2
  vz := vz
  vu := vu
  lawZ t := hasLaw_z vz vu t
  lawU t := hasLaw_u vz vu t
  indep t := (indepFun_iff_hasLaw_prodMk_prod (hasLaw_z vz vu t) (hasLaw_u vz vu t)).mpr
    (hasLaw_pair vz vu t)

/-- Galí (2015), Exercise 5.5: under `truncE` the concrete shocks are i.i.d. in the sense of the
expectation system: adapted, with `E_t z_{t+1} = E_t u_{t+1} = 0`. -/
theorem concrete_iid (vz vu : ℝ≥0) :
    truncE.IsAR1 0 (concreteShocks vz vu).z ∧ truncE.IsAR1 0 (concreteShocks vz vu).u := by
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, ⟨fun t => ?_, fun t => ?_⟩⟩ <;> funext ω <;>
    simp [truncE, concreteShocks, trunc, LinearMap.funLeft_apply]

/-- Galí (2015), Exercise 5.5(a): `s² ≠ 0` when `σ ≠ 0` and `σ_z² ≠ 0`. -/
theorem rateVar_ne_zero {σ κ ϑ : ℝ} {vz : ℝ≥0} (vu : ℝ≥0) (hσ : σ ≠ 0) (hvz : vz ≠ 0) :
    rateVar σ κ ϑ vz vu ≠ 0 := by
  unfold rateVar
  intro h
  have h1 := (add_eq_zero.mp h).1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · apply hσ
    have : σ ^ 2 = 0 := congrArg NNReal.toReal h2
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  · exact hvz h2

/-- **Exercise 5.5(a), non-vacuity** (Galí 2015, p. 162): on the concrete space (normal shocks,
the expectation system `truncE`), the discretionary equilibrium under `π̄*` exists and the
nominal rate is negative with probability exactly 5% at every date. -/
theorem ex5_5_nonvacuous {β σ κ ϑ ρ : ℝ} (hσ : σ ≠ 0) (hϑ : 0 < ϑ) (vz vu : ℝ≥0)
    (hv : rateVar σ κ ϑ vz vu ≠ 0) :
    DiscEq truncE β σ κ ϑ ρ (piStar σ κ ϑ ρ vz vu) (concreteShocks vz vu).z
        (concreteShocks vz vu).u (xT κ ϑ (concreteShocks vz vu).u)
        (pT κ ϑ (piStar σ κ ϑ ρ vz vu) (concreteShocks vz vu).u)
        (iT σ κ ϑ ρ (piStar σ κ ϑ ρ vz vu) (concreteShocks vz vu).z (concreteShocks vz vu).u) ∧
      ∀ t, (shockMeasure vz vu).real
        {ω | iT σ κ ϑ ρ (piStar σ κ ϑ ρ vz vu) (concreteShocks vz vu).z
          (concreteShocks vz vu).u t ω < 0} = 1 / 20 := by
  refine ⟨ex5_5a_exists truncE hσ hϑ (concrete_iid vz vu).2, fun t => ?_⟩
  rw [prob_neg hv (hasLaw_rate (concreteShocks vz vu) σ κ ϑ ρ (piStar σ κ ϑ ρ vz vu) t)]
  exact ((constraint_iff hv).2).mpr rfl

end Gali.DiscretionCommitment.Ex5_5
