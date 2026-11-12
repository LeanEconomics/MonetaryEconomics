/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.DebtLimitStochasticMeasure

/-!
# A Gaussian AR(1) surplus process and the debt limit

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197 ("Suppose we
generate the surplus by an AR(1) ... An AR(1) ranges over the entire real line, as does the
integral of an AR(1) ... the future debt-to-GDP ratio ... will eventually exceed any bound").

The book's continuous-time AR(1) needs Itô calculus; this module builds its discrete analogue on a
genuine probability space. On the i.i.d. product space `(ℕ → ℝ, ν^ℕ)` of `ExpectationsMeasureIID`
the innovations are the coordinates `ε_t(ω) = ω_t`, `u = ExpectationsMeasureIID.ar1 ρ` is the
AR(1) `u₀ = ε₀`, `u_{t+1} = ρ u_t + ε_{t+1}`, and the surplus-to-GDP ratio is `σ_t = s̄ + u_t`
(`arSurplus`). With `ν = N(0, v)` the process is a Gaussian AR(1): `u_t ~ N(0, v ∑_{j≤t} ρ^{2j})`
(`ar1_hasLaw_gaussian`), `E_t u_{t+1} = ρ u_t` (`E_ar1_succ`). The debt-to-GDP ratio is
`x_{t+1} = γ x_t − σ_t` with `0 ≤ γ < 1` (permanent `r < g`).

## Main results

* `arDebt_adapted`: debt `x_{t+1}` is known at `t`.
* `integral_abs_ar1_le`, `integral_abs_arDebt_le`: uniform `L¹` bounds for `|ρ| < 1`.
* `prob_exceeds_ar`: `P(x_{t+2} > M) ≥ q > 0` uniformly in `t` (Markov's inequality and the
  independence of `ε_{t+1}` from `𝓕_t`).
* `arDebt_shift`, `dseq_tendsto`: restarted at `N`, debt is a function of the innovations after
  `N` plus a term that vanishes, so the events below are tail events.
* `ar1_unbounded_of_integrable` (Kolmogorov's 0-1 law): for integrable innovations with deficits of
  every size, debt is a.s. unbounded above.
* **`gaussian_ar1_unbounded`, `gaussian_ar1_not_sustainable`**: with a Gaussian AR(1) surplus
  (`|ρ| < 1`, `v ≠ 0`, any mean `s̄`), almost surely the debt-to-GDP ratio exceeds every level
  infinitely often, so no debt limit is sustainable; `gaussian_ar1_exp_unbounded` for
  `ρ = e^{−η}`, the decay of the book's `ds = −η(s − s̄)dt + σ dz` over one period.
* `arSurplus_not_ae_bdd_above`: the surplus is not bounded above, so Theorem S
  (`DebtLimitStochastic.frequently_exceeds`) does not apply and the 0-1 argument is needed.
-/

namespace Cochrane.FiscalConstraints.TidyR5GaussianAR1

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID DebtLimitStochastic DebtLimitStochasticMeasure
  LognormalGrowthMeasure
open AggregateUncertaintyMeasure (integrable_coord_fun measurable_coord_future)

/-- Cochrane (2023), p. 197: the AR(1) surplus-to-GDP ratio `σ_t = s̄ + u_t`, with
`u = ExpectationsMeasureIID.ar1 ρ`. -/
noncomputable def arSurplus (ρ sbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := sbar + ar1 ρ t ω

/-- Cochrane (2023), p. 197: the AR(1) law of motion pointwise,
`u_{t+1} = ρ u_t + ε_{t+1}`. -/
theorem ar1_succ_apply (ρ : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    ar1 ρ (t + 1) ω = ρ * ar1 ρ t ω + ω (t + 1) := rfl

/-- Cochrane (2023), p. 197: the surplus is an AR(1) around `s̄`:
`σ_{t+1} − s̄ = ρ(σ_t − s̄) + ε_{t+1}`. -/
theorem arSurplus_succ (ρ sbar : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    arSurplus ρ sbar (t + 1) ω - sbar = ρ * (arSurplus ρ sbar t ω - sbar) + ω (t + 1) := by
  unfold arSurplus
  rw [ar1_succ_apply]
  ring

/-- Cochrane (2023), p. 197: the AR(1) is measurable. -/
theorem measurable_ar1 (ρ : ℝ) (t : ℕ) : Measurable (ar1 ρ t) := by
  induction t with
  | zero => exact measurable_pi_apply 0
  | succ t ih => exact (ih.const_mul ρ).add (measurable_pi_apply (t + 1))

variable {ν : ProbabilityMeasure ℝ}

variable (ν) in
/-- Cochrane (2023), p. 197: the AR(1) `u_t` is known at date `t`. -/
theorem measurable_ar1_F (ρ : ℝ) (t : ℕ) : Measurable[(iidSystem ν).𝓕 t] (ar1 ρ t) :=
  (ar1_adapted ν ρ t).measurable

variable (ν) in
/-- Cochrane (2023), (6.4) p. 196 and p. 197: with AR(1) surpluses the debt ratio `x_{t+1}` is
known at date `t`. -/
theorem arDebt_adapted (γ x₀ ρ sbar : ℝ) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (debtPath γ x₀ (arSurplus ρ sbar) (t + 1)) :=
  measurable_debtPath γ x₀ (t + 1) fun s hs =>
    ((measurable_ar1_F ν ρ s).mono ((iidSystem ν).𝓕.mono (by omega)) le_rfl).const_add sbar

/-- Cochrane (2023), (6.4) p. 196: with AR(1) surpluses the debt ratio is measurable. -/
theorem measurable_arDebt (γ x₀ ρ sbar : ℝ) (t : ℕ) :
    Measurable (debtPath γ x₀ (arSurplus ρ sbar) t) :=
  measurable_debtPath γ x₀ t fun s _ => (measurable_ar1 ρ s).const_add sbar

/-! ### The Gaussian AR(1) -/

/-- Cochrane (2023), p. 197: the squared AR(1) coefficient `ρ²` as a nonnegative real. -/
def rho2 (ρ : ℝ) : NNReal := ⟨ρ ^ 2, sq_nonneg ρ⟩

/-- Cochrane (2023), p. 197: the variance of the Gaussian AR(1) at date `t`,
`v ∑_{j ≤ t} ρ^{2j}`. -/
noncomputable def arVar (ρ : ℝ) (v : NNReal) (t : ℕ) : NNReal :=
  v * ∑ j ∈ Finset.range (t + 1), rho2 ρ ^ j

/-- Cochrane (2023), p. 197 (**the process is a Gaussian AR(1)**): with innovations `N(0, v)`,
`u_t ~ N(0, v ∑_{j ≤ t} ρ^{2j})`. -/
theorem ar1_hasLaw_gaussian (ρ : ℝ) (v : NNReal) (t : ℕ) :
    HasLaw (ar1 ρ t) (gaussianReal 0 (arVar ρ v t)) (iidSystem (gaussianProb 0 v)).μ := by
  have hshock : ∀ k, HasLaw (fun ω : ℕ → ℝ => ω k) (gaussianReal 0 v)
      (iidSystem (gaussianProb 0 v)).μ := fun k =>
    ⟨(measurable_pi_apply k).aemeasurable, Measure.infinitePi_map_eval _ k⟩
  induction t with
  | zero =>
    have h : arVar ρ v 0 = v := by simp [arVar]
    rw [h]
    exact hshock 0
  | succ t ih =>
    have h1 : HasLaw (fun ω => ρ * ar1 ρ t ω)
        (gaussianReal (ρ * 0) (rho2 ρ * arVar ρ v t))
        (iidSystem (gaussianProb 0 v)).μ :=
      HasLaw.comp ⟨by fun_prop, gaussianReal_map_const_mul ρ⟩ ih
    have hind : IndepFun (fun ω => ρ * ar1 ρ t ω) (fun ω : ℕ → ℝ => ω (t + 1))
        (iidSystem (gaussianProb 0 v)).μ := by
      rw [IndepFun_iff_Indep]
      refine indep_of_indep_of_le_right (indep_of_indep_of_le_left
        (indep_future (gaussianProb 0 v) t).symm ?_) ?_
      · exact (((measurable_ar1_F (gaussianProb 0 v) ρ t).const_mul ρ)).comap_le
      · exact (measurable_coord_future (Nat.lt_succ_self t)).comap_le
    have h := gaussianReal_add_gaussianReal_of_indepFun hind h1 (hshock (t + 1))
    have hv : arVar ρ v (t + 1) = rho2 ρ * arVar ρ v t + v := by
      unfold arVar
      rw [Finset.sum_range_succ', pow_zero, mul_add, mul_one, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ]
      ring
    rw [mul_zero, zero_add] at h
    rw [hv]
    refine ⟨(measurable_ar1 ρ (t + 1)).aemeasurable, ?_⟩
    rw [← h]
    rfl

/-- Cochrane (2023), p. 197: the AR(1) variance is nonzero when the innovation variance is. -/
theorem arVar_ne_zero (ρ : ℝ) {v : NNReal} (hv : v ≠ 0) (t : ℕ) : arVar ρ v t ≠ 0 := by
  unfold arVar
  refine mul_ne_zero hv ?_
  rw [Finset.sum_range_succ']
  simp

/-- Cochrane (2023), p. 197 ("an AR(1) ranges over the entire real line"): a Gaussian AR(1)
surplus is not almost surely bounded above at any date, so the bounded-above hypothesis of
Theorem S (`DebtLimitStochastic.frequently_exceeds`) fails. -/
theorem arSurplus_not_ae_bdd_above (ρ sbar : ℝ) {v : NNReal} (hv : v ≠ 0) (t : ℕ) (K : ℝ) :
    ¬ ∀ᵐ ω ∂(iidSystem (gaussianProb 0 v)).μ, arSurplus ρ sbar t ω ≤ K := by
  intro h
  have h0 : (iidSystem (gaussianProb 0 v)).μ (ar1 ρ t ⁻¹' Set.Ioi (K - sbar)) = 0 := by
    rw [ae_iff] at h
    have hs : {ω | ¬ arSurplus ρ sbar t ω ≤ K} = ar1 ρ t ⁻¹' Set.Ioi (K - sbar) := by
      ext ω
      simp only [arSurplus, Set.mem_ofPred_eq, not_le, Set.mem_preimage, Set.mem_Ioi]
      constructor <;> intro h <;> linarith
    rwa [hs] at h
  rw [← Measure.map_apply (measurable_ar1 ρ t) measurableSet_Ioi,
    (ar1_hasLaw_gaussian ρ v t).map_eq] at h0
  have h2 := gaussianReal_absolutelyContinuous' 0 (arVar_ne_zero ρ hv t) h0
  rw [Real.volume_Ioi] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197 (the AR(1) forecast): with mean-zero integrable innovations,
`E_t u_{t+1} = ρ u_t` almost everywhere. -/
theorem E_ar1_succ (hint : Integrable id (ν : Measure ℝ)) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (ρ : ℝ) (t : ℕ) :
    (iidSystem ν).E t (ar1 ρ (t + 1)) =ᵐ[(iidSystem ν).μ] ρ • ar1 ρ t := by
  have hui : ∀ s, Integrable (ar1 ρ s) (iidSystem ν).μ := by
    intro s
    induction s with
    | zero => exact integrable_coord_fun (f := id) hint 0
    | succ s ih => exact (ih.const_mul ρ).add (integrable_coord_fun (f := id) hint (s + 1))
  have hsi : Integrable (shock (t + 1)) (iidSystem ν).μ :=
    integrable_coord_fun (f := id) hint (t + 1)
  rw [ar1_succ]
  filter_upwards [(iidSystem ν).E_add ((hui t).smul ρ) hsi t, (iidSystem ν).E_smul ρ (ar1 ρ t) t,
    E_shock ν t] with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, hmean, add_zero,
    (iidSystem ν).E_of_stronglyMeasurable (ar1_adapted ν ρ t) (hui t)]

/-! ### `L¹` bounds and the uniform probability bound -/

/-- Cochrane (2023), p. 197: for `|ρ| < 1` and integrable innovations, every `u_t` is integrable
with `E|u_t| ≤ E|ε|/(1 − |ρ|)`. -/
theorem integral_abs_ar1_le (hint : Integrable id (ν : Measure ℝ)) {ρ : ℝ} (hρ : |ρ| < 1) :
    ∀ t, Integrable (ar1 ρ t) (iidSystem ν).μ ∧
      ∫ ω, |ar1 ρ t ω| ∂(iidSystem ν).μ ≤ (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) := by
  have h1 : 0 < 1 - |ρ| := by linarith
  have hm0 : 0 ≤ ∫ x, |x| ∂(ν : Measure ℝ) := integral_nonneg fun x => abs_nonneg x
  have hsa : ∀ s, ∫ ω, |ω s| ∂(iidSystem ν).μ = ∫ x, |x| ∂(ν : Measure ℝ) := fun s =>
    integral_shock_fun ν s (f := fun x => |x|) continuous_abs.measurable
  have hsh : ∀ s, Integrable (fun ω : ℕ → ℝ => ω s) (iidSystem ν).μ := fun s =>
    integrable_coord_fun (f := id) hint s
  have hkey : (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) * (1 - |ρ|) = ∫ x, |x| ∂(ν : Measure ℝ) :=
    div_mul_cancel₀ _ h1.ne'
  intro t
  induction t with
  | zero =>
    refine ⟨hsh 0, ?_⟩
    change ∫ ω, |ω 0| ∂(iidSystem ν).μ ≤ _
    rw [hsa 0, le_div_iff₀ h1]
    nlinarith [abs_nonneg ρ]
  | succ t ih =>
    have hI : Integrable (ar1 ρ (t + 1)) (iidSystem ν).μ := (ih.1.const_mul ρ).add (hsh (t + 1))
    refine ⟨hI, ?_⟩
    have hle : ∫ ω, |ar1 ρ (t + 1) ω| ∂(iidSystem ν).μ ≤
        ∫ ω, (|ρ| * |ar1 ρ t ω| + |ω (t + 1)|) ∂(iidSystem ν).μ := by
      refine integral_mono hI.abs ((ih.1.abs.const_mul |ρ|).add (hsh (t + 1)).abs) fun ω => ?_
      rw [ar1_succ_apply]
      calc |ρ * ar1 ρ t ω + ω (t + 1)| ≤ |ρ * ar1 ρ t ω| + |ω (t + 1)| := abs_add_le _ _
        _ = |ρ| * |ar1 ρ t ω| + |ω (t + 1)| := by rw [abs_mul]
    rw [integral_add (ih.1.abs.const_mul |ρ|) (hsh (t + 1)).abs, integral_const_mul,
      hsa] at hle
    nlinarith [mul_le_mul_of_nonneg_left ih.2 (abs_nonneg ρ)]

/-- Cochrane (2023), p. 197: with AR(1) surpluses, `|ρ| < 1` and `0 ≤ γ < 1`, every debt ratio is
integrable with `E|x_t| ≤ |x₀| + (|s̄| + E|ε|/(1 − |ρ|))/(1 − γ)`. -/
theorem integral_abs_arDebt_le (hint : Integrable id (ν : Measure ℝ)) {γ ρ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hρ : |ρ| < 1) (x₀ sbar : ℝ) :
    ∀ t, Integrable (debtPath γ x₀ (arSurplus ρ sbar) t) (iidSystem ν).μ ∧
      ∫ ω, |debtPath γ x₀ (arSurplus ρ sbar) t ω| ∂(iidSystem ν).μ ≤
        |x₀| + (|sbar| + (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|)) / (1 - γ) := by
  set Cu := (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) with hCu
  have h1 : 0 < 1 - γ := by linarith
  have hCu0 : 0 ≤ Cu := div_nonneg (integral_nonneg fun x => abs_nonneg x) (by linarith)
  have hB0 : 0 ≤ (|sbar| + Cu) / (1 - γ) := div_nonneg (by positivity) h1.le
  have hkey : (|sbar| + Cu) / (1 - γ) * (1 - γ) = |sbar| + Cu := div_mul_cancel₀ _ h1.ne'
  intro t
  induction t with
  | zero =>
    refine ⟨integrable_const x₀, ?_⟩
    change ∫ _, |x₀| ∂(iidSystem ν).μ ≤ _
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  | succ t ih =>
    obtain ⟨hu, hub⟩ := integral_abs_ar1_le hint hρ t
    have hf : debtPath γ x₀ (arSurplus ρ sbar) (t + 1) =
        fun ω => γ * debtPath γ x₀ (arSurplus ρ sbar) t ω - (sbar + ar1 ρ t ω) := by
      funext ω; exact debtPath_succ γ x₀ _ t ω
    have hsI : Integrable (fun ω => sbar + ar1 ρ t ω) (iidSystem ν).μ :=
      (integrable_const sbar).add hu
    have hI : Integrable (debtPath γ x₀ (arSurplus ρ sbar) (t + 1)) (iidSystem ν).μ := by
      rw [hf]; exact (ih.1.const_mul γ).sub hsI
    refine ⟨hI, ?_⟩
    have hle : ∫ ω, |debtPath γ x₀ (arSurplus ρ sbar) (t + 1) ω| ∂(iidSystem ν).μ ≤
        ∫ ω, (γ * |debtPath γ x₀ (arSurplus ρ sbar) t ω| + (|sbar| + |ar1 ρ t ω|))
          ∂(iidSystem ν).μ := by
      refine integral_mono hI.abs ((ih.1.abs.const_mul γ).add
        ((integrable_const |sbar|).add hu.abs)) fun ω => ?_
      rw [hf]
      calc |γ * debtPath γ x₀ (arSurplus ρ sbar) t ω - (sbar + ar1 ρ t ω)|
          ≤ |γ * debtPath γ x₀ (arSurplus ρ sbar) t ω| + |sbar + ar1 ρ t ω| := abs_sub _ _
        _ ≤ γ * |debtPath γ x₀ (arSurplus ρ sbar) t ω| + (|sbar| + |ar1 ρ t ω|) := by
          rw [abs_mul, abs_of_nonneg hγ0]
          linarith [abs_add_le sbar (ar1 ρ t ω)]
    have e : ∫ ω, (γ * |debtPath γ x₀ (arSurplus ρ sbar) t ω| + (|sbar| + |ar1 ρ t ω|))
        ∂(iidSystem ν).μ = γ * ∫ ω, |debtPath γ x₀ (arSurplus ρ sbar) t ω| ∂(iidSystem ν).μ +
          (|sbar| + ∫ ω, |ar1 ρ t ω| ∂(iidSystem ν).μ) := by
      rw [integral_add (f := fun ω => γ * |debtPath γ x₀ (arSurplus ρ sbar) t ω|)
        (g := fun ω => |sbar| + |ar1 ρ t ω|) (ih.1.abs.const_mul γ)
        ((integrable_const |sbar|).add hu.abs), integral_const_mul,
        integral_add (f := fun _ => |sbar|) (g := fun ω => |ar1 ρ t ω|)
        (integrable_const |sbar|) hu.abs]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [e] at hle
    nlinarith [mul_le_mul_of_nonneg_left ih.2 hγ0, abs_nonneg x₀]

/-- Cochrane (2023), p. 197: with AR(1) surpluses (`|ρ| < 1`), integrable innovations with
deficits of every size and `0 ≤ γ < 1`, the probability that debt exceeds `M` at date `t + 2` is
bounded below by a positive constant uniformly in `t`. Proof: `x_{t+2} = Z_t − s̄ − ε_{t+1}` with
`Z_t = γ x_{t+1} − ρ u_t` known at `t`; Markov's inequality gives `P(Z_t > −D) ≥ 1/2`, and
`ε_{t+1} ≤ −L` is independent of `𝓕_t`. -/
theorem prob_exceeds_ar (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {γ ρ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hρ : |ρ| < 1) (x₀ sbar M : ℝ) :
    ∃ q : ENNReal, q ≠ 0 ∧ ∀ t, q ≤
      (iidSystem ν).μ {ω | M < debtPath γ x₀ (arSurplus ρ sbar) (t + 2) ω} := by
  set Cu := (∫ x, |x| ∂(ν : Measure ℝ)) / (1 - |ρ|) with hCu
  set Cx := |x₀| + (|sbar| + Cu) / (1 - γ) with hCx
  set C := γ * Cx + |ρ| * Cu with hC
  set D := 2 * C + 1 with hD
  set L := M + sbar + D + 1 with hL
  have hCu0 : 0 ≤ Cu := div_nonneg (integral_nonneg fun x => abs_nonneg x) (by linarith)
  have hCx0 : 0 ≤ Cx := add_nonneg (abs_nonneg _) (div_nonneg (by positivity) (by linarith))
  have hC0 : 0 ≤ C := add_nonneg (mul_nonneg hγ0 hCx0) (mul_nonneg (abs_nonneg ρ) hCu0)
  have hD0 : 0 < D := by linarith
  refine ⟨(ν : Measure ℝ) (Set.Iic (-L)) * ENNReal.ofReal (1 / 2),
    mul_ne_zero (hdef L) (by norm_num), fun t => ?_⟩
  obtain ⟨hIx, hbx⟩ := integral_abs_arDebt_le hint hγ0 hγ1 hρ x₀ sbar (t + 1)
  obtain ⟨hIu, hbu⟩ := integral_abs_ar1_le hint hρ t
  set Z : (ℕ → ℝ) → ℝ := fun ω =>
    γ * debtPath γ x₀ (arSurplus ρ sbar) (t + 1) ω - ρ * ar1 ρ t ω with hZ
  have hZi : Integrable Z (iidSystem ν).μ := (hIx.const_mul γ).sub (hIu.const_mul ρ)
  have hZb : ∫ ω, |Z ω| ∂(iidSystem ν).μ ≤ C := by
    have hle : ∫ ω, |Z ω| ∂(iidSystem ν).μ ≤ ∫ ω, (γ * |debtPath γ x₀ (arSurplus ρ sbar) (t + 1)
        ω| + |ρ| * |ar1 ρ t ω|) ∂(iidSystem ν).μ := by
      refine integral_mono hZi.abs ((hIx.abs.const_mul γ).add (hIu.abs.const_mul |ρ|))
        fun ω => ?_
      calc |Z ω| ≤ |γ * debtPath γ x₀ (arSurplus ρ sbar) (t + 1) ω| + |ρ * ar1 ρ t ω| :=
            abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hγ0]
    rw [integral_add (hIx.abs.const_mul γ) (hIu.abs.const_mul |ρ|), integral_const_mul,
      integral_const_mul] at hle
    nlinarith [mul_le_mul_of_nonneg_left hbx hγ0, mul_le_mul_of_nonneg_left hbu (abs_nonneg ρ)]
  have hZm : Measurable[(iidSystem ν).𝓕 t] Z :=
    ((arDebt_adapted ν γ x₀ ρ sbar t).const_mul γ).sub ((measurable_ar1_F ν ρ t).const_mul ρ)
  set A := {ω : ℕ → ℝ | -D < Z ω} with hA
  set B := {ω : ℕ → ℝ | ω (t + 1) ≤ -L} with hB
  have hAm : MeasurableSet[(iidSystem ν).𝓕 t] A := measurableSet_lt measurable_const hZm
  have hBm : MeasurableSet[futureSigma t] B :=
    measurableSet_le (measurable_coord_future (by omega)) measurable_const
  have hind := (Indep_iff _ _ _).1 (indep_future ν t) B A hBm hAm
  have hsub : B ∩ A ⊆ {ω | M < debtPath γ x₀ (arSurplus ρ sbar) (t + 2) ω} := by
    rintro ω ⟨hb, ha⟩
    simp only [Set.mem_ofPred_eq, hB, hA, hZ] at hb ha ⊢
    rw [show t + 2 = (t + 1) + 1 by rfl, debtPath_succ]
    have e : arSurplus ρ sbar (t + 1) ω = sbar + (ρ * ar1 ρ t ω + ω (t + 1)) := rfl
    rw [e]
    linarith
  have hBval : (iidSystem ν).μ B = (ν : Measure ℝ) (Set.Iic (-L)) :=
    measure_shock_preimage (t + 1) measurableSet_Iic
  have hAval : ENNReal.ofReal (1 / 2) ≤ (iidSystem ν).μ A := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := (iidSystem ν).μ)
      (Eventually.of_forall fun ω => abs_nonneg (Z ω)) hZi.abs D
    have hreal : (iidSystem ν).μ.real {ω | D ≤ |Z ω|} ≤ 1 / 2 := by
      have : D * (iidSystem ν).μ.real {ω | D ≤ |Z ω|} ≤ C := hmk.trans hZb
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hpr := measureReal_nonneg (μ := (iidSystem ν).μ) (s := {ω | D ≤ |Z ω|})
      nlinarith
    have hcompl : Aᶜ ⊆ {ω | D ≤ |Z ω|} := by
      intro ω hω
      simp only [hA, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hω ⊢
      rw [le_abs]; right; linarith
    have hAc : (iidSystem ν).μ.real Aᶜ ≤ 1 / 2 := (measureReal_mono hcompl).trans hreal
    have hAm' : MeasurableSet A := (iidSystem ν).𝓕.le t _ hAm
    rw [measureReal_compl hAm', probReal_univ] at hAc
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc (ν : Measure ℝ) (Set.Iic (-L)) * ENNReal.ofReal (1 / 2)
      ≤ (iidSystem ν).μ B * (iidSystem ν).μ A := by rw [hBval]; gcongr
    _ = (iidSystem ν).μ (B ∩ A) := hind.symm
    _ ≤ _ := measure_mono hsub

/-! ### Tail events -/

/-- Cochrane (2023), p. 197: the AR(1) restarted at `N` from `0`, driven by `ε_{N+1}, ε_{N+2}, …`:
`w_0 = 0`, `w_{s+1} = ρ w_s + ε_{N+s+1}`. -/
noncomputable def ar1From (ρ : ℝ) (N : ℕ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | s + 1 => fun ω => ρ * ar1From ρ N s ω + ω (N + s + 1)

/-- Cochrane (2023), p. 197: the deterministic response of debt to the date-`N` AR(1) state,
`d_0 = 0`, `d_{k+1} = γ d_k − ρ^k`. -/
noncomputable def dseq (γ ρ : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => γ * dseq γ ρ k - ρ ^ k

/-- Cochrane (2023), p. 197: restarting the AR(1) at `N`, `u_{N+s} = ρ^s u_N + w_s`. -/
theorem ar1_shift (ρ : ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    ∀ s, ar1 ρ (N + s) ω = ρ ^ s * ar1 ρ N ω + ar1From ρ N s ω := by
  intro s
  induction s with
  | zero => simp [ar1From]
  | succ s ih =>
    rw [← add_assoc, ar1_succ_apply, ih]
    change _ = _ + (ρ * ar1From ρ N s ω + ω (N + s + 1))
    ring

/-- Cochrane (2023), (6.4) p. 196 and p. 197: restarting the debt recursion at `N`,
`x_{N+k} = γ^k x_N + y_k + u_N d_k`, where `y` is the debt from `0` driven by the surpluses
`s̄ + w_s` (functions of the innovations after `N` only). -/
theorem arDebt_shift (γ x₀ ρ sbar : ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    ∀ k, debtPath γ x₀ (arSurplus ρ sbar) (N + k) ω =
      γ ^ k * debtPath γ x₀ (arSurplus ρ sbar) N ω +
        debtPath γ 0 (fun s ω => sbar + ar1From ρ N s ω) k ω + ar1 ρ N ω * dseq γ ρ k := by
  intro k
  induction k with
  | zero => change _ = _ * _ + 0 + _ * 0; simp
  | succ k ih =>
    rw [← add_assoc, debtPath_succ, debtPath_succ, ih]
    unfold arSurplus
    rw [ar1_shift ρ N ω k]
    change _ = _ + _ + ar1 ρ N ω * (γ * dseq γ ρ k - ρ ^ k)
    ring

/-- Cochrane (2023), p. 197: `|d_{j+1}| ≤ (j + 1) m^j` with `m = max γ |ρ|`. -/
theorem abs_dseq_le {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (j : ℕ) :
    |dseq γ ρ (j + 1)| ≤ ((j : ℝ) + 1) * max γ |ρ| ^ j := by
  have hm0 : 0 ≤ max γ |ρ| := le_trans hγ0 (le_max_left _ _)
  induction j with
  | zero => simp [dseq]
  | succ j ih =>
    change |γ * dseq γ ρ (j + 1) - ρ ^ (j + 1)| ≤ _
    have h1 : |γ * dseq γ ρ (j + 1)| ≤ max γ |ρ| * (((j : ℝ) + 1) * max γ |ρ| ^ j) := by
      rw [abs_mul, abs_of_nonneg hγ0]
      exact mul_le_mul (le_max_left _ _) ih (abs_nonneg _) hm0
    have h2 : |ρ ^ (j + 1)| ≤ max γ |ρ| ^ (j + 1) := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg ρ) (le_max_right _ _) _
    calc |γ * dseq γ ρ (j + 1) - ρ ^ (j + 1)| ≤ |γ * dseq γ ρ (j + 1)| + |ρ ^ (j + 1)| :=
          abs_sub _ _
      _ ≤ max γ |ρ| * (((j : ℝ) + 1) * max γ |ρ| ^ j) + max γ |ρ| ^ (j + 1) := add_le_add h1 h2
      _ = (((j + 1 : ℕ) : ℝ) + 1) * max γ |ρ| ^ (j + 1) := by push_cast; ring

/-- Cochrane (2023), p. 197: for `0 ≤ γ < 1` and `|ρ| < 1` the response `d_k` vanishes. -/
theorem dseq_tendsto {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hρ : |ρ| < 1) :
    Tendsto (dseq γ ρ) atTop (𝓝 0) := by
  have hm0 : 0 ≤ max γ |ρ| := le_trans hγ0 (le_max_left _ _)
  have hm1 : max γ |ρ| < 1 := max_lt hγ1 hρ
  have hb : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * max γ |ρ| ^ j) atTop (𝓝 0) := by
    have := (tendsto_self_mul_const_pow_of_lt_one hm0 hm1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hm0 hm1)
    rw [add_zero] at this
    refine this.congr fun j => ?_
    ring
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  exact squeeze_zero_norm (fun j => (Real.norm_eq_abs _).le.trans (abs_dseq_le hγ0 j)) hb

/-- Cochrane (2023), p. 197: the restarted AR(1) `w_s` depends only on the innovations from date
`N` on. -/
theorem measurable_ar1From (ρ : ℝ) (N : ℕ) :
    ∀ s, Measurable[⨆ i ≥ N, coordSigma i] (ar1From ρ N s) := by
  intro s
  induction s with
  | zero => exact measurable_const
  | succ s ih =>
    exact (ih.const_mul ρ).add (Measurable.of_comap_le
      (le_iSup₂ (f := fun i (_ : i ≥ N) => coordSigma i) (N + s + 1) (by omega)))

/-- Cochrane (2023), p. 197 (**debt is a.s. unbounded above with AR(1) surpluses**): with
`u_{t+1} = ρ u_t + ε_{t+1}`, `|ρ| < 1`, i.i.d. integrable innovations with deficits of every size,
any mean `s̄` and `0 ≤ γ < 1`, almost surely the debt ratio exceeds every level infinitely often,
from every initial debt. The events are tail events (`arDebt_shift`, `dseq_tendsto`) of positive
probability (`prob_exceeds_ar`), hence of probability one by Kolmogorov's 0-1 law. -/
theorem ar1_unbounded_of_integrable (hint : Integrable id (ν : Measure ℝ))
    (hdef : ∀ c : ℝ, (ν : Measure ℝ) (Set.Iic (-c)) ≠ 0) {γ ρ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hρ : |ρ| < 1) (x₀ sbar : ℝ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, ∀ M : ℝ, ∃ᶠ t in atTop,
      M < debtPath γ x₀ (arSurplus ρ sbar) t ω := by
  set x := debtPath γ x₀ (arSurplus ρ sbar) with hx
  set E : ℝ → Set (ℕ → ℝ) := fun a =>
    {ω | ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < x t ω} with hE
  have htail : ∀ a, MeasurableSet[limsup coordSigma atTop] (E a) := by
    intro a
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    set y : ℕ → (ℕ → ℝ) → ℝ := fun k => debtPath γ 0 (fun s ω => sbar + ar1From ρ N s ω) k
      with hy
    have hym : ∀ k, Measurable[⨆ i ≥ N, coordSigma i] (y k) := fun k =>
      measurable_debtPath γ 0 k fun s _ => (measurable_ar1From ρ N s).const_add sbar
    have heq : E a = {ω | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ω} := by
      ext ω
      simp only [hE, Set.mem_ofPred_eq]
      have hshift : ∀ m : ℕ, (∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < x t ω) ↔
          ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < x (N + k) ω :=
        fun m => frequently_shift_iff N
      simp only [hshift]
      have hdiff : Tendsto (fun k => x (N + k) ω - y k ω) atTop (𝓝 0) := by
        have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (x N ω)
        have h2 := (dseq_tendsto hγ0 hγ1 hρ).const_mul (ar1 ρ N ω)
        rw [zero_mul] at h1
        rw [mul_zero] at h2
        have h3 := h1.add h2
        rw [add_zero] at h3
        refine h3.congr fun k => ?_
        rw [hx, arDebt_shift]
        simp only [hy]
        ring
      have hdiff' : Tendsto (fun k => y k ω - x (N + k) ω) atTop (𝓝 0) := by
        have := hdiff.neg
        rw [neg_zero] at this
        refine this.congr fun k => ?_
        ring
      exact ⟨fun h m => frequently_near_of_tendsto hdiff h m,
        fun h m => frequently_near_of_tendsto hdiff' h m⟩
    rw [heq]
    exact measurableSet_frequently_near hym a
  have hpos : ∀ a, (iidSystem ν).μ (E a) ≠ 0 := by
    intro a
    obtain ⟨q, hq0, hq⟩ := prob_exceeds_ar hint hdef hγ0 hγ1 hρ x₀ sbar a
    have hfreq := le_measure_frequently (μ := (iidSystem ν).μ)
      (A := fun t => {ω | a < x t ω})
      (fun t => measurableSet_lt measurable_const (measurable_arDebt γ x₀ ρ sbar t)) hq
    have hsub : {ω | ∃ᶠ t in atTop, ω ∈ {ω' | a < x t ω'}} ⊆ E a := by
      intro ω hω m
      refine hω.mono fun t ht => ?_
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      simp only [Set.mem_ofPred_eq] at ht
      linarith
    intro h0
    exact hq0 (nonpos_iff_eq_zero.1 ((hfreq.trans (measure_mono hsub)).trans_eq h0))
  have hone : ∀ n : ℕ, ∀ᵐ ω ∂(iidSystem ν).μ, ω ∈ E n := by
    intro n
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop coordSigma_le (iIndep_coord ν)
      (htail n) with h | h
    · exact absurd h (hpos n)
    · have hm : MeasurableSet (E n) :=
        (limsup_le_iSup.trans (iSup_le coordSigma_le)) _ (htail n)
      rw [ae_iff]
      have := (prob_compl_eq_zero_iff hm).2 h
      simpa [Set.compl_def] using this
  filter_upwards [ae_all_iff.2 hone] with ω hω M
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  refine (hω n 0).mono fun t ht => ?_
  simp only [CharP.cast_eq_zero, zero_add, div_one] at ht
  linarith

/-! ### The Gaussian AR(1) surplus -/

/-- Cochrane (2023), p. 197 (**Gaussian AR(1) surpluses: debt is a.s. unbounded above**): with
`σ_t = s̄ + u_t`, `u_{t+1} = ρ u_t + ε_{t+1}`, `|ρ| < 1`, `ε_t` i.i.d. `N(0, v)`, `v ≠ 0`, and
`0 ≤ γ < 1` (`r < g`), almost surely the debt-to-GDP ratio exceeds every level infinitely
often, from every initial debt. -/
theorem gaussian_ar1_unbounded {v : NNReal} (hv : v ≠ 0) {γ ρ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hρ : |ρ| < 1) (x₀ sbar : ℝ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb 0 v)).μ, ∀ M : ℝ, ∃ᶠ t in atTop,
      M < debtPath γ x₀ (arSurplus ρ sbar) t ω := by
  have hint : Integrable id (gaussianReal 0 v) := by
    have h := memLp_id_gaussianReal (μ := 0) (v := v) 1
    rw [ENNReal.coe_one, memLp_one_iff_integrable] at h
    exact h
  exact ar1_unbounded_of_integrable (ν := gaussianProb 0 v) hint (gaussian_Iic_ne_zero 0 hv)
    hγ0 hγ1 hρ x₀ sbar

/-- Cochrane (2023), p. 197 ("the initial value of debt ... is not sustainable", **Gaussian
AR(1)**): for every debt limit `M`, the event that debt stays at or below `M` forever has
probability zero. -/
theorem gaussian_ar1_not_sustainable {v : NNReal} (hv : v ≠ 0) {γ ρ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (hρ : |ρ| < 1) (x₀ sbar M : ℝ) :
    (iidSystem (gaussianProb 0 v)).μ {ω | ∀ t, debtPath γ x₀ (arSurplus ρ sbar) t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [gaussian_ar1_unbounded hv hγ0 hγ1 hρ x₀ sbar] with ω hω hall
  obtain ⟨t, ht⟩ := (hω M).exists
  exact absurd (hall t) (not_le.mpr ht)

/-- Cochrane (2023), p. 197: the book's mean reversion `ds = −η(s − s̄)dt + σ dz` with `η > 0`
decays by `ρ = e^{−η}` per period; with this `ρ` and Gaussian innovations, debt is a.s.
unbounded above. -/
theorem gaussian_ar1_exp_unbounded {v : NNReal} (hv : v ≠ 0) {γ η : ℝ} (hη : 0 < η)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (x₀ sbar : ℝ) :
    ∀ᵐ ω ∂(iidSystem (gaussianProb 0 v)).μ, ∀ M : ℝ, ∃ᶠ t in atTop,
      M < debtPath γ x₀ (arSurplus (Real.exp (-η)) sbar) t ω := by
  have hρ : |Real.exp (-η)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (by linarith)
  exact gaussian_ar1_unbounded hv hγ0 hγ1 hρ x₀ sbar

end Cochrane.FiscalConstraints.TidyR5GaussianAR1
