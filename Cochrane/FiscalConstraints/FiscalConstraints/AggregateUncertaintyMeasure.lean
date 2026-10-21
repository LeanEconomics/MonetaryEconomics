/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.AggregateUncertainty
import FiscalConstraints.ExpectationsMeasureIID
import Mathlib.Probability.Independence.Integration

/-!
# Aggregate uncertainty on a genuine i.i.d. growth process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.7, pp. 205–207,
equations (6.15)–(6.18), re-proved on a genuine infinite-horizon probability space.

The state space is `Ω = ℕ → ℝ` with the product law `ν^ℕ` (`ExpectationsMeasureIID.iidSystem`),
the shocks are the coordinates `ε_t(ω) = ω_t`, and `𝓕_t = σ(ε_0, …, ε_t)`. Consumption is
`c_t = ∏_{i < t} g(ε_{i+1})` (`cons`), so growth `G_{t+1} = c_{t+1}/c_t = g(ε_{t+1})` is i.i.d.
with law `g_* ν`, positive, and has every moment `mom a = ∫ g^a dν` (`GrowthLaw`). Expectations
are Mathlib's conditional expectations, statements hold almost everywhere, and present values
are genuine infinite sums, both as sums of expectations and as the expectation of the infinite
sum (`condExp_tsum`).

## Main results

* `E_past_mul_future`: a date-`t` variable times a function of the future: integrable, and
  `E_t[X F] = X E[F]` (independence). `integral_ratioPow`: `E[(c_{t+j}/c_t)^a] = (mom a)^j`.
* `meas_iidGrowth` (the a.e. form of `AggregateUncertainty.IIDGrowth` at every date),
  `E_ratio_rpow_mul`.
* (6.15)/(6.16): `correct_term`, `incorrect_term`, `correct_pv_summable_iff`,
  `incorrect_pv_summable_iff`, `correct_finite_incorrect_explodes`, and the expectation of the
  infinite sum `E_tsum_correct_pv`.
* (6.17): `rollover_step`, `eq_6_17`, `terminal_c`, `pv_term_c`, `bohn_pv_hasSum_iff`, and
  `E_tsum_bohn_pv` (`c_t = E_t Σ_{j ≥ 1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}`, a genuine expected
  infinite present value).
* (6.18): `eq_6_18`, `eq_6_18_diverges_ae`, `riskFree_prices`.
* The two-state Bohn example as an infinite i.i.d. coin process: `bohnG`, `bohnGrowthLaw`,
  `bohn_mom` (its moments are `AggregateUncertainty.bohnMom`), `bohn_infinite_witness`,
  `bohn_infinite_6_18`.
* Links: `MeasIIDGrowth.toCore` (the a.e. hypothesis gives the core `IIDGrowth` on a finite
  full-support system), `bohnTree_measIIDGrowth` (the coin tree satisfies it through
  `TreeBridge`), `link_correct_term`, `link_terminal_c`, `link_pv_term_c` (the infinite-process
  values equal the coin-tree values of `AggregateUncertainty`).
-/

namespace Cochrane.FiscalConstraints.AggregateUncertaintyMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID AggregateUncertainty

variable (ν : ProbabilityMeasure ℝ) (g : ℝ → ℝ)

/-- Cochrane (2023), p. 205: the law of i.i.d. growth `G = g(ε)`: `g` is measurable and positive,
and every power `G^a` has a finite mean. -/
structure GrowthLaw where
  /-- `g` is measurable. -/
  meas : Measurable g
  /-- growth is positive. -/
  pos : ∀ x, 0 < g x
  /-- every moment `E[G^a]` is finite. -/
  integrable : ∀ a : ℝ, Integrable (fun x => g x ^ a) (ν : Measure ℝ)

/-- Cochrane (2023), p. 205: consumption `c_t = ∏_{i < t} g(ε_{i+1})`, `c_0 = 1`. -/
noncomputable def cons (t : ℕ) (ω : ℕ → ℝ) : ℝ := ∏ i ∈ Finset.range t, g (ω (i + 1))

/-- Cochrane (2023), p. 205: the moments of growth, `mom a = E[G^a] = ∫ g^a dν`. -/
noncomputable def mom (a : ℝ) : ℝ := ∫ x, g x ^ a ∂(ν : Measure ℝ)

/-- Cochrane (2023), p. 205: the product `∏_{i < j} g(ε_{t+i+1})^a`, which is
`(c_{t+j}/c_t)^a` (`ratio_rpow`). -/
noncomputable def ratioPow (a : ℝ) (t j : ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∏ i ∈ Finset.range j, g (ω (t + i + 1)) ^ a

variable {ν g}

/-- Cochrane (2023), p. 205: consumption is positive. -/
theorem cons_pos (hG : GrowthLaw ν g) (t : ℕ) (ω : ℕ → ℝ) : 0 < cons g t ω :=
  Finset.prod_pos fun _ _ => hG.pos _

/-- Cochrane (2023), p. 205: `c_{t+j} = c_t ∏_{i<j} g(ε_{t+i+1})`. -/
theorem cons_add (t j : ℕ) (ω : ℕ → ℝ) :
    cons g (t + j) ω = cons g t ω * ∏ i ∈ Finset.range j, g (ω (t + i + 1)) := by
  unfold cons
  rw [Finset.prod_range_add]

/-- Cochrane (2023), p. 205: `c_0 = 1`. -/
theorem cons_zero (ω : ℕ → ℝ) : cons g 0 ω = 1 := by simp [cons]

/-- Cochrane (2023), p. 205: consumption growth is the i.i.d. factor, `G_{t+1} = g(ε_{t+1})`. -/
theorem growth_cons (hG : GrowthLaw ν g) (t : ℕ) (ω : ℕ → ℝ) :
    growth (cons g) t ω = g (ω (t + 1)) := by
  unfold growth
  rw [cons_add t 1 ω, Finset.prod_range_one, add_zero]
  field_simp [(cons_pos hG t ω).ne']

/-- Cochrane (2023), p. 205: `c_{t+j}/c_t = ∏_{i<j} g(ε_{t+i+1})`. -/
theorem ratio_cons (hG : GrowthLaw ν g) (t j : ℕ) (ω : ℕ → ℝ) :
    ratio (cons g) t j ω = ∏ i ∈ Finset.range j, g (ω (t + i + 1)) := by
  unfold ratio
  rw [cons_add]
  field_simp [(cons_pos hG t ω).ne']

/-- Cochrane (2023), p. 205: `(c_{t+j}/c_t)^a = ∏_{i<j} g(ε_{t+i+1})^a`. -/
theorem ratio_rpow (hG : GrowthLaw ν g) (a : ℝ) (t j : ℕ) (ω : ℕ → ℝ) :
    ratio (cons g) t j ω ^ a = ratioPow g a t j ω := by
  rw [ratio_cons hG, ratioPow, Real.finsetProd_rpow _ _ (fun i _ => (hG.pos _).le)]

/-- Cochrane (2023), p. 205: `c_t^a = ∏_{i<t} g(ε_{i+1})^a`. -/
theorem cons_rpow (hG : GrowthLaw ν g) (a : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    cons g t ω ^ a = ratioPow g a 0 t ω := by
  have h := ratio_rpow hG a 0 t ω
  rwa [ratio, cons_zero, div_one, zero_add] at h

/-- Cochrane (2023), p. 205: one more period of growth, `ratioPow` recursion. -/
theorem ratioPow_succ (a : ℝ) (t j : ℕ) (ω : ℕ → ℝ) :
    ratioPow g a t (j + 1) ω = ratioPow g a t j ω * g (ω (t + j + 1)) ^ a := by
  rw [ratioPow, Finset.prod_range_succ]
  rfl

/-- Cochrane (2023), p. 205: `(c_{t+j}/c_t)^a` is known at `t + j`. -/
theorem measurable_ratioPow (hG : GrowthLaw ν g) (a : ℝ) (t j : ℕ) :
    Measurable[(iidSystem ν).𝓕 (t + j)] (ratioPow g a t j) :=
  Finset.measurable_prod _ fun i hi => (hG.meas.pow_const a).comp
    (measurable_shock ν (by rw [Finset.mem_range] at hi; omega))

/-- Cochrane (2023), p. 205: consumption is known at `t`. -/
theorem measurable_cons (hG : GrowthLaw ν g) (t : ℕ) :
    Measurable[(iidSystem ν).𝓕 t] (cons g t) :=
  Finset.measurable_prod _ fun i hi => hG.meas.comp
    (measurable_shock ν (by rw [Finset.mem_range] at hi; omega))

/-- Cochrane (2023), p. 205: the shock `ε_k` with `k > t` is measurable for the future. -/
theorem measurable_coord_future {t k : ℕ} (hk : t < k) :
    Measurable[futureSigma t] (fun ω : ℕ → ℝ => ω k) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Set.Ioi t) => coordSigma i) k hk)

/-- Cochrane (2023), p. 205: `(c_{t+j}/c_t)^a` depends only on shocks after `t`. -/
theorem measurable_ratioPow_future (hG : GrowthLaw ν g) (a : ℝ) (t j : ℕ) :
    Measurable[futureSigma t] (ratioPow g a t j) :=
  Finset.measurable_prod _ fun _ _ => (hG.meas.pow_const a).comp
    (measurable_coord_future (by omega))

/-- Cochrane (2023), p. 205: a function of one shock with an integrable law is integrable. -/
theorem integrable_coord_fun {f : ℝ → ℝ} (hf : Integrable f (ν : Measure ℝ)) (k : ℕ) :
    Integrable (fun ω : ℕ → ℝ => f (ω k)) (iidSystem ν).μ :=
  (measurePreserving_eval_infinitePi (fun _ => (ν : Measure ℝ)) k).integrable_comp_of_integrable
    hf

variable (ν) in
/-- Cochrane (2023), p. 205: **independence of the past and the future**: a date-`t` variable
times a function of the shocks after `t` is integrable, its mean is the product of the means, and
`E_t[X F] = X E[F]` a.e. -/
theorem E_past_mul_future {t : ℕ} {X F : (ℕ → ℝ) → ℝ}
    (hX : StronglyMeasurable[(iidSystem ν).𝓕 t] X) (hF : StronglyMeasurable[futureSigma t] F)
    (hXi : Integrable X (iidSystem ν).μ) (hFi : Integrable F (iidSystem ν).μ) :
    Integrable (X * F) (iidSystem ν).μ ∧
      ∫ ω, (X * F) ω ∂(iidSystem ν).μ =
        (∫ ω, X ω ∂(iidSystem ν).μ) * ∫ ω, F ω ∂(iidSystem ν).μ ∧
      (iidSystem ν).E t (X * F) =ᵐ[(iidSystem ν).μ]
        X * fun _ => ∫ ω, F ω ∂(iidSystem ν).μ := by
  have hind : IndepFun X F (iidSystem ν).μ := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left (indep_future ν t).symm
      hX.measurable.comap_le) hF.measurable.comap_le
  have hint : Integrable (X * F) (iidSystem ν).μ := hind.integrable_mul hXi hFi
  refine ⟨hint, hind.integral_mul_eq_mul_integral hXi.1 hFi.1, ?_⟩
  refine (condExp_mul_of_stronglyMeasurable_left hX hint hFi).trans ?_
  filter_upwards [E_future ν t hF] with ω h
  simp only [Pi.mul_apply, h]

/-- Cochrane (2023), p. 205: **i.i.d. growth over `j` periods**: `(c_{t+j}/c_t)^a` is integrable
with mean `(mom a)^j`. -/
theorem integral_ratioPow (hG : GrowthLaw ν g) (a : ℝ) (t : ℕ) :
    ∀ j, Integrable (ratioPow g a t j) (iidSystem ν).μ ∧
      ∫ ω, ratioPow g a t j ω ∂(iidSystem ν).μ = mom ν g a ^ j := by
  intro j
  induction j with
  | zero =>
    have h : ratioPow g a t 0 = fun _ => 1 := by funext ω; simp [ratioPow]
    rw [h]
    simp
  | succ j ih =>
    have hfun : ratioPow g a t (j + 1) =
        ratioPow g a t j * fun ω => g (ω (t + j + 1)) ^ a := by
      funext ω; rw [ratioPow_succ]; rfl
    have hF : StronglyMeasurable[futureSigma (t + j)] (fun ω : ℕ → ℝ => g (ω (t + j + 1)) ^ a) :=
      ((hG.meas.pow_const a).comp (measurable_coord_future (by omega))).stronglyMeasurable
    obtain ⟨h1, h2, -⟩ := E_past_mul_future ν (measurable_ratioPow hG a t j).stronglyMeasurable
      hF ih.1 (integrable_coord_fun (hG.integrable a) _)
    rw [hfun]
    refine ⟨h1, ?_⟩
    rw [h2, ih.2, integral_shock_fun ν _ (hG.meas.pow_const a), pow_succ]
    rfl

/-- Cochrane (2023), p. 205: powers of consumption are integrable. -/
theorem integrable_cons_rpow (hG : GrowthLaw ν g) (a : ℝ) (t : ℕ) :
    Integrable (fun ω => cons g t ω ^ a) (iidSystem ν).μ := by
  have h : (fun ω => cons g t ω ^ a) = ratioPow g a 0 t := funext (cons_rpow hG a t)
  rw [h]
  exact (integral_ratioPow hG a 0 t).1

/-- Cochrane (2023), (6.15) p. 205 (i.i.d. growth over `j` periods, a.e.):
`E_t[(c_{t+j}/c_t)^a X] = (mom a)^j X` for `X` integrable and known at `t`; the product is
integrable. -/
theorem E_ratio_rpow_mul (hG : GrowthLaw ν g) (a : ℝ) {t : ℕ} {X : (ℕ → ℝ) → ℝ}
    (hX : StronglyMeasurable[(iidSystem ν).𝓕 t] X) (hXi : Integrable X (iidSystem ν).μ)
    (j : ℕ) :
    Integrable (fun ω => ratio (cons g) t j ω ^ a * X ω) (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => ratio (cons g) t j ω ^ a * X ω) =ᵐ[(iidSystem ν).μ]
        fun ω => mom ν g a ^ j * X ω := by
  have hfun : (fun ω => ratio (cons g) t j ω ^ a * X ω) = X * ratioPow g a t j := by
    funext ω; rw [ratio_rpow hG, Pi.mul_apply, mul_comm]
  obtain ⟨h1, -, h3⟩ := E_past_mul_future ν hX
    (measurable_ratioPow_future hG a t j).stronglyMeasurable hXi (integral_ratioPow hG a t j).1
  rw [hfun]
  refine ⟨h1, h3.trans (Eventually.of_forall fun ω => ?_)⟩
  simp only [Pi.mul_apply, (integral_ratioPow hG a t j).2]
  ring

/-- Cochrane (2023), p. 205: **the i.i.d. process has i.i.d. growth at every date** (the a.e.
form of `AggregateUncertainty.IIDGrowth`): `E_t[G_{t+1}^a] = mom a`. -/
theorem meas_iidGrowth (hG : GrowthLaw ν g) (t : ℕ) (a : ℝ) :
    (iidSystem ν).E t (fun ω => growth (cons g) t ω ^ a) =ᵐ[(iidSystem ν).μ]
      fun _ => mom ν g a := by
  have hfun : (fun ω => growth (cons g) t ω ^ a) =
      fun ω => ratio (cons g) t 1 ω ^ a * (fun _ => (1 : ℝ)) ω := by
    funext ω
    rw [growth_cons hG, ratio_cons hG, Finset.prod_range_one, add_zero, mul_one]
  rw [hfun]
  refine (E_ratio_rpow_mul hG a stronglyMeasurable_const (integrable_const 1) 1).2.trans ?_
  exact Eventually.of_forall fun ω => by simp


/-- Cochrane (2023), (6.15) p. 205: `E_t[(c_{t+j}/c_t)^a] = (mom a)^j` a.e., and the power is
integrable. -/
theorem E_ratio_rpow (hG : GrowthLaw ν g) (a : ℝ) (t j : ℕ) :
    Integrable (fun ω => ratio (cons g) t j ω ^ a) (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => ratio (cons g) t j ω ^ a) =ᵐ[(iidSystem ν).μ]
        fun _ => mom ν g a ^ j := by
  have h := E_ratio_rpow_mul hG a (t := t) stronglyMeasurable_const (integrable_const 1) j
  simp only [mul_one] at h
  exact h

/-! ### A general lemma: expectation of an absolutely summable series -/

/-- Cochrane (2023), (6.15) p. 205 (genuine infinite horizon): if the terms `f_i` are integrable
and `Σ E|f_i| < ∞`, then the series converges absolutely almost surely and `E_t` passes through
the infinite sum, `E_t Σ f_i = Σ E_t f_i` a.e. (from Mathlib's `condExp_tsum`). -/
theorem E_tsum_of_summable_integral {Ω : Type*} [MeasurableSpace Ω]
    (S : MeasExpectationSystem Ω) {f : ℕ → Ω → ℝ} (hf : ∀ i, Integrable (f i) S.μ)
    (hs : Summable fun i => ∫ ω, |f i ω| ∂S.μ) (t : ℕ) :
    (∀ᵐ ω ∂S.μ, Summable fun i => f i ω) ∧
      S.E t (fun ω => ∑' i, f i ω) =ᵐ[S.μ] fun ω => ∑' i, S.E t (f i) ω := by
  have hl : ∀ i, ∫⁻ ω, ‖f i ω‖ₑ ∂S.μ = ENNReal.ofReal (∫ ω, |f i ω| ∂S.μ) := fun i => by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf i)]
    simp only [Real.norm_eq_abs]
  have hne : ∑' i, ∫⁻ ω, ‖f i ω‖ₑ ∂S.μ ≠ ⊤ := by
    simp only [hl]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun ω => abs_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨?_, condExp_tsum (fun i => (hf i).1) hne⟩
  have hm : AEMeasurable (fun ω => ∑' i, ‖f i ω‖ₑ) S.μ :=
    AEMeasurable.tsum fun i => (hf i).1.enorm
  have hlt : ∫⁻ ω, ∑' i, ‖f i ω‖ₑ ∂S.μ ≠ ⊤ := by
    rw [lintegral_tsum fun i => (hf i).1.enorm]
    exact hne
  filter_upwards [ae_lt_top' hm hlt] with ω hω
  refine Summable.of_nnnorm ?_
  rw [← ENNReal.tsum_coe_ne_top_iff_summable]
  exact hω.ne

/-! ### (6.15) and (6.16) on the i.i.d. process -/

/-- Cochrane (2023), (6.15) p. 205: a constant surplus ratio's discounted term is integrable. -/
theorem integrable_pvTerm (hG : GrowthLaw ν g) (β γ κ : ℝ) (t j : ℕ) :
    Integrable (pvTerm β γ κ (cons g) t j) (iidSystem ν).μ := by
  have h : pvTerm β γ κ (cons g) t j =
      (β ^ j * κ) • fun ω => ratio (cons g) t j ω ^ (1 - γ) * (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp only [pvTerm, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos (cons_pos hG) t j ω),
      Real.rpow_one]
    ring
  rw [h]
  simp only [mul_one]
  exact (E_ratio_rpow hG (1 - γ) t j).1.smul _

/-- Cochrane (2023), (6.15) p. 205, a.e. on the i.i.d. process: the correct summands are
`E_t[β^j (c_{t+j}/c_t)^{1−γ}] κ = (β mom(1−γ))^j κ`. -/
theorem correct_term (hG : GrowthLaw ν g) (β γ κ : ℝ) (t j : ℕ) :
    (iidSystem ν).E t (pvTerm β γ κ (cons g) t j) =ᵐ[(iidSystem ν).μ]
      fun _ => (β * mom ν g (1 - γ)) ^ j * κ := by
  have h : pvTerm β γ κ (cons g) t j =
      (β ^ j * κ) • fun ω => ratio (cons g) t j ω ^ (1 - γ) * (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp only [pvTerm, Pi.smul_apply, smul_eq_mul, mul_one]
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos (cons_pos hG) t j ω),
      Real.rpow_one]
    ring
  rw [h]
  simp only [mul_one]
  refine ((iidSystem ν).E_smul _ _ t).trans ?_
  filter_upwards [(E_ratio_rpow hG (1 - γ) t j).2] with ω hω
  simp only [Pi.smul_apply, smul_eq_mul, hω, mul_pow]
  ring

/-- Cochrane (2023), (6.16) p. 205, a.e. on the i.i.d. process: the summands with the
expectation moved inside are `E_t[β^j (c_{t+j}/c_t)^{−γ}] E_t[c_{t+j}/c_t] κ =
(β mom(−γ) mom 1)^j κ`. -/
theorem incorrect_term (hG : GrowthLaw ν g) (β γ κ : ℝ) (t j : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (iidSystem ν).E t (fun ω' => β ^ j * ratio (cons g) t j ω' ^ (-γ)) ω *
        (iidSystem ν).E t (ratio (cons g) t j) ω * κ =
        (β * mom ν g (-γ) * mom ν g 1) ^ j * κ := by
  have h1 : (fun ω' => β ^ j * ratio (cons g) t j ω' ^ (-γ)) =
      β ^ j • fun ω' => ratio (cons g) t j ω' ^ (-γ) := by
    funext ω'; simp
  have hb := (E_ratio_rpow hG 1 t j).2
  simp only [Real.rpow_one] at hb
  rw [h1]
  filter_upwards [(iidSystem ν).E_smul (β ^ j) _ t, (E_ratio_rpow hG (-γ) t j).2, hb]
    with ω hs ha hb'
  rw [hs, Pi.smul_apply, ha, hb', smul_eq_mul, mul_pow, mul_pow]

/-- Cochrane (2023), (6.15) p. 205, on the i.i.d. process: almost surely the correct present
value `Σ_{j≥1} E_t[...]` converges iff `|β mom(1−γ)| < 1` (for `κ ≠ 0`). -/
theorem correct_pv_summable_iff (hG : GrowthLaw ν g) (β γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (Summable (fun j => (iidSystem ν).E t (pvTerm β γ κ (cons g) t (j + 1)) ω) ↔
        |β * mom ν g (1 - γ)| < 1) := by
  filter_upwards [ae_all_iff.2 fun j => correct_term hG β γ κ t (j + 1)] with ω hω
  simp only [hω]
  exact summable_geom_succ_iff hκ

/-- Cochrane (2023), (6.16) p. 205, on the i.i.d. process: almost surely the incorrect present
value converges iff `|β mom(−γ) mom 1| < 1` (for `κ ≠ 0`). -/
theorem incorrect_pv_summable_iff (hG : GrowthLaw ν g) (β γ : ℝ) {κ : ℝ} (hκ : κ ≠ 0)
    (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (Summable (fun j => (iidSystem ν).E t
          (fun ω' => β ^ (j + 1) * ratio (cons g) t (j + 1) ω' ^ (-γ)) ω *
        (iidSystem ν).E t (ratio (cons g) t (j + 1)) ω * κ) ↔
        |β * mom ν g (-γ) * mom ν g 1| < 1) := by
  filter_upwards [ae_all_iff.2 fun j => incorrect_term hG β γ κ t (j + 1)] with ω hω
  simp only [hω]
  exact summable_geom_succ_iff hκ

/-- Cochrane (2023), p. 205 ("the true present value can converge while this mistaken one
explodes"), on the i.i.d. process: if `0 ≤ β mom(1−γ) < 1 ≤ β mom(−γ) mom 1` then almost surely
the correct present value (6.15) converges and the incorrect one (6.16) does not. -/
theorem correct_finite_incorrect_explodes (hG : GrowthLaw ν g) {β γ κ : ℝ} (hκ : κ ≠ 0)
    (hq0 : 0 ≤ β * mom ν g (1 - γ)) (hq1 : β * mom ν g (1 - γ) < 1)
    (hρ : 1 ≤ β * mom ν g (-γ) * mom ν g 1) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      Summable (fun j => (iidSystem ν).E t (pvTerm β γ κ (cons g) t (j + 1)) ω) ∧
      ¬ Summable (fun j => (iidSystem ν).E t
          (fun ω' => β ^ (j + 1) * ratio (cons g) t (j + 1) ω' ^ (-γ)) ω *
        (iidSystem ν).E t (ratio (cons g) t (j + 1)) ω * κ) := by
  filter_upwards [correct_pv_summable_iff hG β γ hκ t, incorrect_pv_summable_iff hG β γ hκ t]
    with ω h1 h2
  rw [h1, h2, abs_of_nonneg hq0]
  refine ⟨hq1, fun h => ?_⟩
  have := le_abs_self (β * mom ν g (-γ) * mom ν g 1)
  linarith

/-- Cochrane (2023), p. 205: the moments of positive growth are positive. -/
theorem mom_pos (hG : GrowthLaw ν g) (a : ℝ) : 0 < mom ν g a := by
  unfold mom
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.rpow_pos_of_pos (hG.pos x) a).le)
    (hG.integrable a)]
  have hs : Function.support (fun x => g x ^ a) = Set.univ :=
    Set.eq_univ_of_forall fun x => (Real.rpow_pos_of_pos (hG.pos x) a).ne'
  rw [hs, measure_univ]
  exact one_pos

/-- **(6.15), genuine infinite horizon**, Cochrane (2023), p. 205: on the i.i.d. process with
`β ≥ 0` and `β mom(1−γ) < 1`, the discounted surplus stream `Σ_{j≥1} β^j (c_{t+j}/c_t)^{1−γ} κ`
converges almost surely and its conditional expectation is
`E_t Σ_{j≥1} (...) = Σ_{j≥1} E_t(...) = q κ/(1 − q)`, `q = β mom(1−γ)`. -/
theorem E_tsum_correct_pv (hG : GrowthLaw ν g) {β γ : ℝ} (κ : ℝ) (hβ : 0 ≤ β)
    (hq1 : β * mom ν g (1 - γ) < 1) (t : ℕ) :
    (∀ᵐ ω ∂(iidSystem ν).μ, Summable fun j => pvTerm β γ κ (cons g) t (j + 1) ω) ∧
      (iidSystem ν).E t (fun ω => ∑' j, pvTerm β γ κ (cons g) t (j + 1) ω)
        =ᵐ[(iidSystem ν).μ]
        fun _ => β * mom ν g (1 - γ) * κ / (1 - β * mom ν g (1 - γ)) := by
  set q := β * mom ν g (1 - γ) with hq
  have hq0 : 0 ≤ q := mul_nonneg hβ (mom_pos hG _).le
  have habs : ∀ j, ∫ ω, |pvTerm β γ κ (cons g) t (j + 1) ω| ∂(iidSystem ν).μ =
      q ^ (j + 1) * |κ| := fun j => by
    have hfun : (fun ω => |pvTerm β γ κ (cons g) t (j + 1) ω|) =
        fun ω => (β ^ (j + 1) * |κ|) * ratioPow g (1 - γ) t (j + 1) ω := by
      funext ω
      rw [← ratio_rpow hG, show (1 : ℝ) - γ = -γ + 1 by ring,
        Real.rpow_add (ratio_pos (cons_pos hG) t (j + 1) ω), Real.rpow_one, pvTerm, abs_mul,
        abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ _),
        abs_of_pos (Real.rpow_pos_of_pos (ratio_pos (cons_pos hG) t (j + 1) ω) _),
        abs_of_pos (ratio_pos (cons_pos hG) t (j + 1) ω)]
      ring
    rw [hfun, integral_const_mul, (integral_ratioPow hG (1 - γ) t (j + 1)).2, hq, mul_pow]
    ring
  have hsum : Summable fun j => ∫ ω, |pvTerm β γ κ (cons g) t (j + 1) ω| ∂(iidSystem ν).μ := by
    simp only [habs]
    exact ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq0 hq1)).mul_right _
  obtain ⟨hs, he⟩ := E_tsum_of_summable_integral (iidSystem ν)
    (fun j => integrable_pvTerm hG β γ κ t (j + 1)) hsum t
  refine ⟨hs, he.trans ?_⟩
  filter_upwards [ae_all_iff.2 fun j => correct_term hG β γ κ t (j + 1)] with ω hω
  simp only [hω]
  rw [tsum_mul_right]
  have h1 : ∑' j : ℕ, q ^ (j + 1) = q * (1 - q)⁻¹ := by
    simp only [pow_succ, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
    ring
  rw [h1]
  field_simp [(by linarith : (1 - q) ≠ 0)]

/-! ### (6.17) on the i.i.d. process -/

/-- Cochrane (2023), (6.17) p. 207, on the i.i.d. process: rolling debt over at the risk-free
rate, `β mom(−γ) R = 1`. For adapted debt `b` whose discounted value
`(c_{t+j}/c_t)^{−γ} b_{t+j}` is integrable, `β^{j+1}(c_{t+j+1}/c_t)^{−γ} R b_{t+j}` is integrable
and `E_t[D_{j+1} R b_{t+j}] = E_t[D_j b_{t+j}]` a.e. -/
theorem rollover_step (hG : GrowthLaw ν g) {β γ R : ℝ} (hR : β * mom ν g (-γ) * R = 1)
    {b : ℕ → (ℕ → ℝ) → ℝ} (hb : StronglyAdapted (iidSystem ν).𝓕 b) {t j : ℕ}
    (hbi : Integrable (fun ω => ratio (cons g) t j ω ^ (-γ) * b (t + j) ω) (iidSystem ν).μ) :
    Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * b (t + j) ω))
        (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * b (t + j) ω))
        =ᵐ[(iidSystem ν).μ] (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t j ω * b (t + j) ω)
        := by
  set Y : (ℕ → ℝ) → ℝ := fun ω => ratio (cons g) t j ω ^ (-γ) * b (t + j) ω with hY
  set F : (ℕ → ℝ) → ℝ := fun ω => g (ω (t + j + 1)) ^ (-γ) with hF
  have hYm : StronglyMeasurable[(iidSystem ν).𝓕 (t + j)] Y := by
    have h : Y = ratioPow g (-γ) t j * b (t + j) := by
      funext ω; simp only [hY, Pi.mul_apply]; rw [ratio_rpow hG]
    rw [h]
    exact (measurable_ratioPow hG (-γ) t j).stronglyMeasurable.mul (hb (t + j))
  have hFm : StronglyMeasurable[futureSigma (t + j)] F :=
    ((hG.meas.pow_const _).comp (measurable_coord_future (by omega))).stronglyMeasurable
  have hFi : Integrable F (iidSystem ν).μ := integrable_coord_fun (hG.integrable _) _
  have hFint : ∫ ω, F ω ∂(iidSystem ν).μ = mom ν g (-γ) :=
    integral_shock_fun ν _ (hG.meas.pow_const _)
  obtain ⟨hI, -, hE⟩ := E_past_mul_future ν hYm hFm hbi hFi
  have hL : (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * b (t + j) ω)) =
      (β ^ (j + 1) * R) • (Y * F) := by
    funext ω
    simp only [pvDisc, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hY, hF]
    rw [ratio_succ (cons_pos hG t ω).ne' (cons_pos hG (t + j) ω).ne',
      Real.mul_rpow (ratio_pos (cons_pos hG) t j ω).le
        (growth_pos (cons_pos hG) (t + j) ω).le, growth_cons hG]
    ring
  have hRt : (fun ω => pvDisc β γ (cons g) t j ω * b (t + j) ω) = β ^ j • Y := by
    funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul, hY]; ring
  rw [hL, hRt]
  refine ⟨hI.smul _, ?_⟩
  have h1 : (iidSystem ν).E t (Y * F) =ᵐ[(iidSystem ν).μ] mom ν g (-γ) • (iidSystem ν).E t Y := by
    refine ((iidSystem ν).E_tower (Nat.le_add_right t j) (Y * F)).symm.trans ?_
    refine ((iidSystem ν).E_congr hE t).trans ?_
    have hfun : (Y * fun _ => ∫ ω, F ω ∂(iidSystem ν).μ) = mom ν g (-γ) • Y := by
      funext ω; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hFint]; ring
    rw [hfun]
    exact (iidSystem ν).E_smul _ _ t
  filter_upwards [(iidSystem ν).E_smul (β ^ (j + 1) * R) (Y * F) t, h1,
    (iidSystem ν).E_smul (β ^ j) Y t] with ω e1 e2 e3
  rw [e1, e3, Pi.smul_apply, e2]
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination β ^ j * (iidSystem ν).E t Y ω * hR

/-- **(6.17)**, Cochrane (2023), p. 207, on the i.i.d. process: if adapted debt `b` (with
integrable discounted values) is rolled over at the risk-free rate, `s_{u+1} = R b_u − b_{u+1}`,
`β mom(−γ) R = 1`, then for every horizon `T`, a.e.
`b_t = E_t Σ_{j=1}^T β^j (c_{t+j}/c_t)^{−γ} s_{t+j} + E_t[β^T (c_{t+T}/c_t)^{−γ} b_{t+T}]`. -/
theorem eq_6_17 (hG : GrowthLaw ν g) {β γ R : ℝ} (hR : β * mom ν g (-γ) * R = 1)
    {b s : ℕ → (ℕ → ℝ) → ℝ} (hb : StronglyAdapted (iidSystem ν).𝓕 b)
    (hs : ∀ u ω, s (u + 1) ω = R * b u ω - b (u + 1) ω) (t : ℕ)
    (hbi : ∀ j, Integrable (fun ω => ratio (cons g) t j ω ^ (-γ) * b (t + j) ω) (iidSystem ν).μ)
    (T : ℕ) :
    b t =ᵐ[(iidSystem ν).μ]
      (iidSystem ν).E t (fun ω => ∑ j ∈ Finset.range T,
          pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) +
        (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t T ω * b (t + T) ω) := by
  have hDi : ∀ j, Integrable (fun ω => pvDisc β γ (cons g) t j ω * b (t + j) ω)
      (iidSystem ν).μ := fun j => by
    have h : (fun ω => pvDisc β γ (cons g) t j ω * b (t + j) ω) =
        β ^ j • fun ω => ratio (cons g) t j ω ^ (-γ) * b (t + j) ω := by
      funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul]; ring
    rw [h]
    exact (hbi j).smul _
  have hterm : ∀ j, (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) =
      (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * b (t + j) ω)) -
        fun ω => pvDisc β γ (cons g) t (j + 1) ω * b (t + (j + 1)) ω := fun j => by
    funext ω
    simp only [Pi.sub_apply]
    rw [hs (t + j) ω, ← add_assoc]
    ring
  have hti : ∀ j, Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω)
      (iidSystem ν).μ := fun j => by
    rw [hterm j]
    exact (rollover_step hG hR hb (hbi j)).1.sub (hDi (j + 1))
  induction T with
  | zero =>
    have h0 : (fun ω => ∑ j ∈ Finset.range 0,
        pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) = 0 := by funext ω; simp
    have h1 : (fun ω => pvDisc β γ (cons g) t 0 ω * b (t + 0) ω) = b t := by
      funext ω; simp [pvDisc, ratio_zero (cons_pos hG t ω).ne']
    have hbt : Integrable (b t) (iidSystem ν).μ := by rw [← h1]; exact hDi 0
    rw [h0, h1, (iidSystem ν).E_zero, (iidSystem ν).E_of_stronglyMeasurable (hb t) hbt, zero_add]
  | succ T ih =>
    have hsplit : (fun ω => ∑ j ∈ Finset.range (T + 1),
        pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) =
        (fun ω => ∑ j ∈ Finset.range T, pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) +
          fun ω => pvDisc β γ (cons g) t (T + 1) ω * s (t + T + 1) ω := by
      funext ω; simp [Finset.sum_range_succ]
    have hSi : Integrable (fun ω => ∑ j ∈ Finset.range T,
        pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) (iidSystem ν).μ :=
      integrable_finsetSum _ fun j _ => hti j
    rw [hsplit]
    have hstep := (rollover_step hG hR hb (hbi T)).2
    have hsub := (iidSystem ν).E_sub (rollover_step hG hR hb (hbi T)).1 (hDi (T + 1)) t
    rw [← hterm T] at hsub
    filter_upwards [ih, (iidSystem ν).E_add hSi (hti T) t, hsub, hstep] with ω e0 e1 e2 e3
    rw [e0, Pi.add_apply, Pi.add_apply, e1, Pi.add_apply, e2, Pi.sub_apply, e3]
    ring

/-- Cochrane (2023), (6.17) p. 207, on the i.i.d. process: for debt `b = c`, the discounted
debt `(c_{t+j}/c_t)^{−γ} c_{t+j} = c_t (c_{t+j}/c_t)^{1−γ}` is integrable and
`E_t[β^T (c_{t+T}/c_t)^{−γ} c_{t+T}] = (β mom(1−γ))^T c_t` a.e. -/
theorem terminal_c (hG : GrowthLaw ν g) (β γ : ℝ) (t T : ℕ) :
    Integrable (fun ω => ratio (cons g) t T ω ^ (-γ) * cons g (t + T) ω) (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t T ω * cons g (t + T) ω)
        =ᵐ[(iidSystem ν).μ] fun ω => (β * mom ν g (1 - γ)) ^ T * cons g t ω := by
  have hct : Integrable (cons g t) (iidSystem ν).μ := by
    have h := integrable_cons_rpow hG 1 t
    simp only [Real.rpow_one] at h
    exact h
  have hkey : ∀ ω, ratio (cons g) t T ω ^ (-γ) * cons g (t + T) ω =
      ratio (cons g) t T ω ^ (1 - γ) * cons g t ω := fun ω => by
    rw [show (1 : ℝ) - γ = -γ + 1 by ring, Real.rpow_add (ratio_pos (cons_pos hG) t T ω),
      Real.rpow_one, ratio]
    field_simp [(cons_pos hG t ω).ne']
  obtain ⟨hI, hE⟩ := E_ratio_rpow_mul hG (1 - γ) (measurable_cons hG t).stronglyMeasurable hct T
  have h1 : (fun ω => ratio (cons g) t T ω ^ (-γ) * cons g (t + T) ω) =
      fun ω => ratio (cons g) t T ω ^ (1 - γ) * cons g t ω := funext hkey
  refine ⟨h1 ▸ hI, ?_⟩
  have h : (fun ω => pvDisc β γ (cons g) t T ω * cons g (t + T) ω) =
      β ^ T • fun ω => ratio (cons g) t T ω ^ (1 - γ) * cons g t ω := by
    funext ω
    simp only [pvDisc, Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, hkey]
  rw [h]
  filter_upwards [(iidSystem ν).E_smul (β ^ T) _ t, hE] with ω e1 e2
  rw [e1, Pi.smul_apply, e2, smul_eq_mul, mul_pow]
  ring

/-- Cochrane (2023), (6.17) p. 207, on the i.i.d. process: each term of the present value of the
rollover surpluses `s_{u+1} = R c_u − c_{u+1}` is integrable, with
`E_t[β^{j+1}(c_{t+j+1}/c_t)^{−γ} s_{t+j+1}] = q^j (1 − q) c_t` a.e., `q = β mom(1−γ)`. -/
theorem pv_term_c (hG : GrowthLaw ν g) {β γ R : ℝ} (hR : β * mom ν g (-γ) * R = 1)
    {s : ℕ → (ℕ → ℝ) → ℝ} (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω)
    (t j : ℕ) :
    Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) (iidSystem ν).μ ∧
      (iidSystem ν).E t (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω)
        =ᵐ[(iidSystem ν).μ]
        fun ω => (β * mom ν g (1 - γ)) ^ j * (1 - β * mom ν g (1 - γ)) * cons g t ω := by
  have hca : StronglyAdapted (iidSystem ν).𝓕 (cons g) :=
    fun u => (measurable_cons hG u).stronglyMeasurable
  have hfun : (fun ω => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) =
      (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * cons g (t + j) ω)) -
        fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω := by
    funext ω
    simp only [Pi.sub_apply]
    rw [hs (t + j) ω, ← add_assoc]
    ring
  obtain ⟨hI1, hE1⟩ := rollover_step hG hR hca (terminal_c hG β γ t j).1
  have hI2 : Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω)
      (iidSystem ν).μ := by
    have h : (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω) =
        β ^ (j + 1) • fun ω => ratio (cons g) t (j + 1) ω ^ (-γ) * cons g (t + (j + 1)) ω := by
      funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul]; ring
    rw [h]
    exact (terminal_c hG β γ t (j + 1)).1.smul _
  rw [hfun]
  refine ⟨hI1.sub hI2, ?_⟩
  filter_upwards [(iidSystem ν).E_sub hI1 hI2 t, hE1, (terminal_c hG β γ t j).2,
    (terminal_c hG β γ t (j + 1)).2] with ω e1 e2 e3 e4
  rw [e1, Pi.sub_apply, e2, e3, e4, pow_succ]
  ring

/-- Cochrane (2023), (6.17) p. 207: for `q ≥ 0` and `x > 0`, `Σ_j q^j (1 − q) x` has sum `x` iff
`q < 1`. -/
theorem hasSum_geom_iff {q x : ℝ} (hq0 : 0 ≤ q) (hx : 0 < x) :
    HasSum (fun j : ℕ => q ^ j * (1 - q) * x) x ↔ q < 1 := by
  constructor
  · intro h
    by_contra hq1
    push Not at hq1
    rcases hq1.eq_or_lt with h1 | h1
    · have h0 : HasSum (fun j : ℕ => q ^ j * (1 - q) * x) 0 := by
        rw [← h1]; simp
      have := h.unique h0
      linarith
    · have hlim := h.summable.tendsto_atTop_zero
      have hle : ∀ j : ℕ, q ^ j * (1 - q) * x ≤ (1 - q) * x := fun j => by
        have hp : 1 ≤ q ^ j := one_le_pow₀ h1.le
        have hneg : (1 - q) * x < 0 := mul_neg_of_neg_of_pos (by linarith) hx
        nlinarith
      have := le_of_tendsto' hlim hle
      nlinarith
  · intro hq1
    have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_right ((1 - q) * x)
    have hval : (1 - q)⁻¹ * ((1 - q) * x) = x := by
      field_simp [(by linarith : (1 - q) ≠ 0)]
    rw [hval] at hg
    refine hg.congr_fun ?_
    intro j
    ring

/-- **(6.15) for Bohn's example**, Cochrane (2023), (6.17) p. 207, on the i.i.d. process: almost
surely, debt equal to consumption rolled over at the risk-free rate equals the sum of the
expected discounted surpluses, `Σ_{j≥1} E_t[β^j (c_{t+j}/c_t)^{−γ} s_{t+j}] = c_t`, iff
`β E[G^{1−γ}] < 1` (for `β ≥ 0`). -/
theorem bohn_pv_hasSum_iff (hG : GrowthLaw ν g) {β γ R : ℝ} (hβ : 0 ≤ β)
    (hR : β * mom ν g (-γ) * R = 1) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      (HasSum (fun j => (iidSystem ν).E t
          (fun ω' => pvDisc β γ (cons g) t (j + 1) ω' * s (t + j + 1) ω') ω) (cons g t ω) ↔
        β * mom ν g (1 - γ) < 1) := by
  filter_upwards [ae_all_iff.2 fun j => (pv_term_c hG hR hs t j).2] with ω hω
  simp only [hω]
  exact hasSum_geom_iff (mul_nonneg hβ (mom_pos hG _).le) (cons_pos hG t ω)

/-- **(6.17), genuine infinite horizon**, Cochrane (2023), p. 207, on the i.i.d. process: with
`β > 0` and `β E[G^{1−γ}] < 1`, the discounted rollover surpluses
`Σ_{j≥1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}` converge absolutely almost surely and debt is the
conditional expectation of this infinite sum: `c_t = E_t Σ_{j≥1} (...)` a.e. -/
theorem E_tsum_bohn_pv (hG : GrowthLaw ν g) {β γ R : ℝ} (hβ : 0 < β)
    (hR : β * mom ν g (-γ) * R = 1) (hq1 : β * mom ν g (1 - γ) < 1) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω) (t : ℕ) :
    (∀ᵐ ω ∂(iidSystem ν).μ,
        Summable fun j => pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω) ∧
      (iidSystem ν).E t (fun ω => ∑' j, pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω)
        =ᵐ[(iidSystem ν).μ] cons g t := by
  set q := β * mom ν g (1 - γ) with hq
  have hq0 : 0 ≤ q := mul_nonneg hβ.le (mom_pos hG _).le
  have hRpos : 0 < R := by
    have hm := mom_pos hG (-γ)
    by_contra h
    push Not at h
    have : β * mom ν g (-γ) * R ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hβ hm).le h
    linarith
  have hca : StronglyAdapted (iidSystem ν).𝓕 (cons g) :=
    fun u => (measurable_cons hG u).stronglyMeasurable
  have hct : Integrable (cons g t) (iidSystem ν).μ := by
    have h := integrable_cons_rpow hG 1 t
    simp only [Real.rpow_one] at h
    exact h
  have hDpos : ∀ j ω, 0 < pvDisc β γ (cons g) t j ω := fun j ω =>
    mul_pos (pow_pos hβ _) (Real.rpow_pos_of_pos (ratio_pos (cons_pos hG) t j ω) _)
  have hA : ∀ j, Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * (R * cons g (t + j) ω))
      (iidSystem ν).μ ∧ ∫ ω, pvDisc β γ (cons g) t (j + 1) ω * (R * cons g (t + j) ω)
        ∂(iidSystem ν).μ = q ^ j * ∫ ω, cons g t ω ∂(iidSystem ν).μ := fun j => by
    obtain ⟨hI, hE⟩ := rollover_step hG hR hca (terminal_c hG β γ t j).1
    refine ⟨hI, ?_⟩
    rw [← (iidSystem ν).integral_E t, integral_congr_ae (hE.trans (terminal_c hG β γ t j).2),
      integral_const_mul]
  have hB : ∀ j, Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω)
      (iidSystem ν).μ ∧ ∫ ω, pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω
        ∂(iidSystem ν).μ = q ^ (j + 1) * ∫ ω, cons g t ω ∂(iidSystem ν).μ := fun j => by
    have hI : Integrable (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω)
        (iidSystem ν).μ := by
      have h : (fun ω => pvDisc β γ (cons g) t (j + 1) ω * cons g (t + (j + 1)) ω) =
          β ^ (j + 1) • fun ω => ratio (cons g) t (j + 1) ω ^ (-γ) * cons g (t + (j + 1)) ω := by
        funext ω; simp only [pvDisc, Pi.smul_apply, smul_eq_mul]; ring
      rw [h]
      exact (terminal_c hG β γ t (j + 1)).1.smul _
    refine ⟨hI, ?_⟩
    rw [← (iidSystem ν).integral_E t, integral_congr_ae (terminal_c hG β γ t (j + 1)).2,
      integral_const_mul]
  have hbound : ∀ j, ∫ ω, |pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω| ∂(iidSystem ν).μ
      ≤ (q ^ j + q ^ (j + 1)) * ∫ ω, cons g t ω ∂(iidSystem ν).μ := fun j => by
    rw [add_mul, ← (hA j).2, ← (hB j).2, ← integral_add (hA j).1 (hB j).1]
    refine integral_mono ((pv_term_c hG hR hs t j).1.abs) ((hA j).1.add (hB j).1) fun ω => ?_
    rw [hs (t + j) ω, ← add_assoc, abs_mul, abs_of_pos (hDpos _ ω)]
    have h1 := hDpos (j + 1) ω
    have h2 := cons_pos hG (t + j) ω
    have h3 := cons_pos hG (t + j + 1) ω
    have h4 : |R * cons g (t + j) ω - cons g (t + j + 1) ω| ≤
        R * cons g (t + j) ω + cons g (t + j + 1) ω := by
      rw [abs_le]; constructor <;> nlinarith
    calc pvDisc β γ (cons g) t (j + 1) ω * |R * cons g (t + j) ω - cons g (t + j + 1) ω|
        ≤ pvDisc β γ (cons g) t (j + 1) ω * (R * cons g (t + j) ω + cons g (t + j + 1) ω) :=
          mul_le_mul_of_nonneg_left h4 h1.le
      _ = _ := by ring
  have hsum : Summable fun j =>
      ∫ ω, |pvDisc β γ (cons g) t (j + 1) ω * s (t + j + 1) ω| ∂(iidSystem ν).μ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun ω => abs_nonneg _) hbound ?_
    refine ((summable_geometric_of_lt_one hq0 hq1).add ?_).mul_right _
    exact (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one hq0 hq1)
  obtain ⟨hS, hE⟩ := E_tsum_of_summable_integral (iidSystem ν)
    (fun j => (pv_term_c hG hR hs t j).1) hsum t
  refine ⟨hS, hE.trans ?_⟩
  filter_upwards [ae_all_iff.2 fun j => (pv_term_c hG hR hs t j).2] with ω hω
  simp only [hω]
  exact ((hasSum_geom_iff hq0 (cons_pos hG t ω)).2 hq1).tsum_eq

/-! ### (6.18) and the risk-free rate on the i.i.d. process -/

/-- Cochrane (2023), p. 206, on the i.i.d. process: the risk-free rate prices the one-period
riskless bond, `E_t[β G_{t+1}^{−γ}] (1 + r) = 1` a.e. -/
theorem riskFree_prices (hG : GrowthLaw ν g) {β γ : ℝ} (hβ : β ≠ 0) (t : ℕ) :
    (iidSystem ν).E t (fun ω => β * growth (cons g) t ω ^ (-γ) * riskFreeGross β γ (mom ν g))
      =ᵐ[(iidSystem ν).μ] fun _ => 1 := by
  have hβm : β * mom ν g (-γ) ≠ 0 := mul_ne_zero hβ (mom_pos hG _).ne'
  have h : (fun ω => β * growth (cons g) t ω ^ (-γ) * riskFreeGross β γ (mom ν g)) =
      (β * riskFreeGross β γ (mom ν g)) • fun ω => growth (cons g) t ω ^ (-γ) := by
    funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [h]
  filter_upwards [(iidSystem ν).E_smul (β * riskFreeGross β γ (mom ν g)) _ t,
    meas_iidGrowth hG t (-γ)] with ω e1 e2
  rw [e1, Pi.smul_apply, e2, smul_eq_mul, riskFreeGross]
  field_simp
  exact div_self (mom_pos hG _).ne'

/-- **(6.18)**, Cochrane (2023), p. 207, on the i.i.d. process: discounting the rollover
surpluses at the risk-free rate `R ≠ 0`, a.e. the expected terminal term is
`E_t[R^{−T} c_{t+T}] = c_t (E[G]/R)^T` and the expected present value is
`E_t[Σ_{j=1}^T R^{−j} s_{t+j}] = c_t (1 − (E[G]/R)^T)`. -/
theorem eq_6_18 (hG : GrowthLaw ν g) {R : ℝ} (hR : R ≠ 0) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω) (t T : ℕ) :
    (iidSystem ν).E t (fun ω => (R⁻¹) ^ T * cons g (t + T) ω) =ᵐ[(iidSystem ν).μ]
        (fun ω => cons g t ω * (mom ν g 1 / R) ^ T) ∧
      (iidSystem ν).E t (fun ω => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω)
        =ᵐ[(iidSystem ν).μ] fun ω => cons g t ω * (1 - (mom ν g 1 / R) ^ T) := by
  have hct : Integrable (cons g t) (iidSystem ν).μ := by
    have h := integrable_cons_rpow hG 1 t
    simp only [Real.rpow_one] at h
    exact h
  have hkey : (fun ω => (R⁻¹) ^ T * cons g (t + T) ω) =
      (R⁻¹) ^ T • fun ω => ratio (cons g) t T ω ^ (1 : ℝ) * cons g t ω := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, Real.rpow_one, ratio]
    field_simp [(cons_pos hG t ω).ne']
  obtain ⟨hI, hE⟩ := E_ratio_rpow_mul hG 1 (measurable_cons hG t).stronglyMeasurable hct T
  have hterm : (iidSystem ν).E t (fun ω => (R⁻¹) ^ T * cons g (t + T) ω) =ᵐ[(iidSystem ν).μ]
      fun ω => cons g t ω * (mom ν g 1 / R) ^ T := by
    rw [hkey]
    filter_upwards [(iidSystem ν).E_smul ((R⁻¹) ^ T) _ t, hE] with ω e1 e2
    rw [e1, Pi.smul_apply, e2, smul_eq_mul, div_pow, inv_pow]
    field_simp
  refine ⟨hterm, ?_⟩
  have hfun : (fun ω => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω) =
      cons g t - fun ω => (R⁻¹) ^ T * cons g (t + T) ω := by
    funext ω
    rw [Pi.sub_apply, (eq_6_18_pathwise hR (cons_pos hG) hs t T ω).2]
  have hTi : Integrable (fun ω => (R⁻¹) ^ T * cons g (t + T) ω) (iidSystem ν).μ := by
    rw [hkey]; exact hI.smul _
  rw [hfun]
  filter_upwards [(iidSystem ν).E_sub hct hTi t, hterm] with ω e1 e2
  rw [e1, Pi.sub_apply, (iidSystem ν).E_of_stronglyMeasurable
    (measurable_cons hG t).stronglyMeasurable hct, e2]
  ring

/-- **(6.18) on the i.i.d. process**, Cochrane (2023), p. 207 ("the present value of cashflows
term builds to negative infinity, and the terminal value builds to positive infinity"): if
`0 < R < E[G]` (`r < g`), then almost surely `E_t[Σ_{j=1}^T R^{−j} s_{t+j}] → −∞` and
`E_t[R^{−T} c_{t+T}] → +∞` as `T → ∞`. -/
theorem eq_6_18_diverges_ae (hG : GrowthLaw ν g) {R : ℝ} (hR0 : 0 < R) (hRg : R < mom ν g 1)
    {s : ℕ → (ℕ → ℝ) → ℝ} (hs : ∀ u ω, s (u + 1) ω = R * cons g u ω - cons g (u + 1) ω)
    (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      Tendsto (fun T => (iidSystem ν).E t
          (fun ω' => ∑ j ∈ Finset.range T, (R⁻¹) ^ (j + 1) * s (t + j + 1) ω') ω) atTop atBot ∧
      Tendsto (fun T => (iidSystem ν).E t
          (fun ω' => (R⁻¹) ^ T * cons g (t + T) ω') ω) atTop atTop := by
  have h := fun T => eq_6_18 hG hR0.ne' hs t T
  filter_upwards [ae_all_iff.2 fun T => (h T).1, ae_all_iff.2 fun T => (h T).2] with ω h1 h2
  simp only [h1, h2]
  obtain ⟨d1, d2⟩ := eq_6_18_diverges hR0 hRg (cons_pos hG t ω)
  exact ⟨d1, by simpa only [mul_comm] using d2⟩

/-! ### Bohn's two-state example as an infinite i.i.d. coin process -/

/-- Cochrane (2023), p. 206 (Bohn's example): growth driven by a fair `±1` coin,
`G = 5/4` on heads (`ε ≥ 0`) and `G = 17/20` on tails. -/
noncomputable def bohnG (x : ℝ) : ℝ := if 0 ≤ x then 5 / 4 else 17 / 20

/-- Cochrane (2023), p. 206: two-state coin growth is a growth law (measurable, positive,
bounded moments). -/
theorem bohnGrowthLaw : GrowthLaw coin bohnG where
  meas := by
    unfold bohnG
    exact Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const
      measurable_const
  pos := fun x => by unfold bohnG; split_ifs <;> norm_num
  integrable := fun _ => by
    change Integrable _ coinMeasure
    unfold coinMeasure
    exact ((integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)).smul_measure
      (by simp)

/-- Cochrane (2023), p. 206: the moments of the infinite coin process are the two-state moments
of `AggregateUncertainty`, `E[G^a] = ((5/4)^a + (17/20)^a)/2`. -/
theorem bohn_mom : mom coin bohnG = bohnMom := by
  funext a
  rw [mom, integral_coin]
  simp [bohnG, bohnMom, bohnGrowth]

/-- Cochrane (2023), p. 206: the risk-free rate `R = 361250/358288` satisfies
`β E[G^{−γ}] R = 1` for the coin process (`β = 49/50`, `γ = 2`). -/
theorem bohn_hR :
    (49 / 50 : ℝ) * mom coin bohnG (-2) * riskFreeGross (49 / 50) 2 bohnMom = 1 := by
  rw [bohn_mom, riskFreeGross, bohnMom_values.2.2]
  norm_num

/-- Cochrane (2023), pp. 205–207 (**Theorem B on a genuine infinite i.i.d. process**): with
`β = 49/50`, `γ = 2`, growth `G ∈ {17/20, 5/4}` driven by i.i.d. fair coins on `ℕ → ℝ`, every
history has probability zero; the risk-free rate is below mean growth; for every `κ ≠ 0` the
correct present value converges and the incorrect one explodes a.s.; and debt equal to
consumption rolled over at the risk-free rate is the expectation of its infinite discounted
surplus stream, `c_t = E_t Σ_{j≥1} β^j (c_{t+j}/c_t)^{−γ} s_{t+j}`, with the stream converging
a.s. -/
theorem bohn_infinite_witness {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * cons bohnG u ω - cons bohnG (u + 1) ω) (t : ℕ) :
    (∀ ω, (iidSystem coin).μ {ω} = 0) ∧
    riskFreeGross (49 / 50) 2 (mom coin bohnG) < mom coin bohnG 1 ∧
    (∀ κ : ℝ, κ ≠ 0 → ∀ᵐ ω ∂(iidSystem coin).μ,
      Summable (fun j => (iidSystem coin).E t (pvTerm (49 / 50) 2 κ (cons bohnG) t (j + 1)) ω) ∧
      ¬ Summable (fun j => (iidSystem coin).E t
          (fun ω' => (49 / 50) ^ (j + 1) * ratio (cons bohnG) t (j + 1) ω' ^ (-2 : ℝ)) ω *
        (iidSystem coin).E t (ratio (cons bohnG) t (j + 1)) ω * κ)) ∧
    (∀ᵐ ω ∂(iidSystem coin).μ,
        Summable fun j => pvDisc (49 / 50) 2 (cons bohnG) t (j + 1) ω * s (t + j + 1) ω) ∧
      (iidSystem coin).E t
          (fun ω => ∑' j, pvDisc (49 / 50) 2 (cons bohnG) t (j + 1) ω * s (t + j + 1) ω)
        =ᵐ[(iidSystem coin).μ] cons bohnG t := by
  obtain ⟨-, hRm, hq, hq1, hρ⟩ := bohn_numbers
  rw [← bohn_mom] at hRm hq hq1 hρ
  have hρ' : 1 ≤ (49 / 50 : ℝ) * mom coin bohnG (-2) * mom coin bohnG 1 := hρ.le
  have hq0 : 0 ≤ (49 / 50 : ℝ) * mom coin bohnG (1 - 2) := by rw [hq]; norm_num
  refine ⟨iid_singleton coin_mean coin_var one_pos, by rw [bohn_mom] at hRm ⊢; exact hRm,
    fun κ hκ => correct_finite_incorrect_explodes bohnGrowthLaw hκ hq0 hq1 hρ' t, ?_⟩
  exact E_tsum_bohn_pv bohnGrowthLaw (by norm_num) bohn_hR hq1 hs t

/-- Cochrane (2023), (6.18) p. 207, **Bohn's example on the infinite coin process**: discounting
the rollover surpluses at the risk-free rate `R = 361250/358288 < E[G] = 21/20`, almost surely
the expected present value tends to `−∞` and the expected terminal value to `+∞`. -/
theorem bohn_infinite_6_18 {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * cons bohnG u ω - cons bohnG (u + 1) ω) (t : ℕ) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      Tendsto (fun T => (iidSystem coin).E t (fun ω' => ∑ j ∈ Finset.range T,
          (riskFreeGross (49 / 50) 2 bohnMom)⁻¹ ^ (j + 1) * s (t + j + 1) ω') ω) atTop atBot ∧
      Tendsto (fun T => (iidSystem coin).E t (fun ω' =>
          (riskFreeGross (49 / 50) 2 bohnMom)⁻¹ ^ T * cons bohnG (t + T) ω') ω) atTop atTop := by
  obtain ⟨hR, hRm, -, -, -⟩ := bohn_numbers
  have hR0 : 0 < riskFreeGross (49 / 50) 2 bohnMom := by rw [hR]; norm_num
  have hRm' : riskFreeGross (49 / 50) 2 bohnMom < mom coin bohnG 1 := by
    rw [bohn_mom]; exact hRm
  exact eq_6_18_diverges_ae bohnGrowthLaw hR0 hRm' hs t

/-! ### Links to the core and coin-tree versions -/

/-- Cochrane (2023), p. 205: **i.i.d. growth in the measure-theoretic setting** — for dates
`t < H`, `E_t[G_{t+1}^a] = m a` almost everywhere (the a.e. form of
`AggregateUncertainty.IIDGrowth`). -/
def MeasIIDGrowth {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
    (c : ℕ → Ω → ℝ) (m : ℝ → ℝ) (H : ℕ) : Prop :=
  ∀ t, t < H → ∀ a : ℝ, S.E t (fun ω => growth c t ω ^ a) =ᵐ[S.μ] fun _ => m a

/-- Cochrane (2023), p. 205 (**link to the core**): on a finite discrete state space with full
support, the a.e. hypothesis is exactly the core `IIDGrowth` of the bridged system, so every
core theorem of `AggregateUncertainty` applies to it. -/
theorem MeasIIDGrowth.toCore {Ω : Type*} [MeasurableSpace Ω] [Finite Ω]
    [DiscreteMeasurableSpace Ω] {S : MeasExpectationSystem Ω} (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {c : ℕ → Ω → ℝ} {m : ℝ → ℝ} {H : ℕ} (h : MeasIIDGrowth S c m H) :
    IIDGrowth (S.toExpectationSystem hfull) c m H :=
  fun t ht a => S.eq_of_ae_eq hfull (h t ht a)

/-- Cochrane (2023), p. 205: the genuine i.i.d. process satisfies `MeasIIDGrowth` at every
horizon, with moments `mom a = ∫ g^a dν`. -/
theorem iid_measIIDGrowth (hG : GrowthLaw ν g) (H : ℕ) :
    MeasIIDGrowth (iidSystem ν) (cons g) (mom ν g) H :=
  fun t _ a => meas_iidGrowth hG t a

/-- Cochrane (2023), p. 206 (**link to the coin tree**): the coin tree `bohnTree H`, viewed as
a measure-theoretic system through `TreeBridge.treeSystem`, satisfies `MeasIIDGrowth` with the
same moments `bohnMom` as the infinite coin process (`bohn_mom`). -/
theorem bohnTree_measIIDGrowth (H : ℕ) :
    MeasIIDGrowth (ExpectationsMeasure.TreeBridge.treeSystem (bohnTree H)) (bohnC H) bohnMom H :=
  fun t ht a => by
    rw [ExpectationsMeasure.TreeBridge.treeSystem_E]
    have h := bohnSystem_iid H t ht a
    rw [bohnSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at h
    rw [h]

/-- Cochrane (2023), (6.15) p. 205 (**link**): for `j ≤ H`, the `j`-th correct summand of the
infinite coin process equals, almost surely, the `j`-th correct summand of the coin tree of
horizon `H` (both are `(4116/4250)^j κ`). -/
theorem link_correct_term {H j : ℕ} (hj : j ≤ H) (κ : ℝ) (ω' : Fin H → Bool) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      (iidSystem coin).E 0 (pvTerm (49 / 50) 2 κ (cons bohnG) 0 j) ω =
        (bohnSystem H).E 0 (pvTerm (49 / 50) 2 κ (bohnC H) 0 j) ω' := by
  filter_upwards [correct_term bohnGrowthLaw (49 / 50) 2 κ 0 j] with ω h
  rw [h, (bohn_witness_terms hj κ ω').1, bohn_mom, bohn_numbers.2.2.1]

/-- Cochrane (2023), (6.17) p. 207 (**link**): for `T ≤ H`, the expected terminal term of the
infinite coin process equals, almost surely, the coin-tree value (both are `(4116/4250)^T`). -/
theorem link_terminal_c {H T : ℕ} (hT : T ≤ H) (ω' : Fin H → Bool) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      (iidSystem coin).E 0 (fun ω => pvDisc (49 / 50) 2 (cons bohnG) 0 T ω * cons bohnG (0 + T) ω)
          ω =
        (bohnSystem H).E 0 (fun ω => pvDisc (49 / 50) 2 (bohnC H) 0 T ω * bohnC H (0 + T) ω) ω'
        := by
  have hcore := AggregateUncertainty.terminal_c (bohnSystem H) (bohnSystem_pullOut H)
    (bohnC_pos H) (bohnSystem_knownPowers H) (bohnSystem_iid H) (49 / 50) 2 (t := 0) (T := T)
    (by omega)
  filter_upwards [(AggregateUncertaintyMeasure.terminal_c bohnGrowthLaw (49 / 50) 2 0 T).2]
    with ω h
  rw [h, hcore, bohn_mom, cons_zero]
  simp [bohnC]

/-- Cochrane (2023), (6.17) p. 207 (**link**): for `j + 1 ≤ H`, each expected discounted
rollover surplus of the infinite coin process equals, almost surely, the coin-tree value (both
are `q^j (1 − q)` with `q = 4116/4250`, `c_0 = 1`). -/
theorem link_pv_term_c {H j : ℕ} (hj : j + 1 ≤ H) {s : ℕ → (ℕ → ℝ) → ℝ}
    (hs : ∀ u ω, s (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * cons bohnG u ω - cons bohnG (u + 1) ω)
    {s' : ℕ → (Fin H → Bool) → ℝ}
    (hs' : ∀ u ω, s' (u + 1) ω =
      riskFreeGross (49 / 50) 2 bohnMom * bohnC H u ω - bohnC H (u + 1) ω) (ω' : Fin H → Bool) :
    ∀ᵐ ω ∂(iidSystem coin).μ,
      (iidSystem coin).E 0 (fun ω => pvDisc (49 / 50) 2 (cons bohnG) 0 (j + 1) ω * s (0 + j + 1) ω)
          ω =
        (bohnSystem H).E 0
          (fun ω => pvDisc (49 / 50) 2 (bohnC H) 0 (j + 1) ω * s' (0 + j + 1) ω) ω' := by
  have hRc : (49 / 50 : ℝ) * bohnMom (-2) * riskFreeGross (49 / 50) 2 bohnMom = 1 := by
    rw [riskFreeGross, bohnMom_values.2.2]; norm_num
  have hcore := AggregateUncertainty.pv_term_c (bohnSystem H) (bohnSystem_pullOut H)
    (bohnC_pos H) (bohnSystem_knownPowers H) (bohnSystem_iid H) hRc hs' (t := 0) (j := j)
    (by omega)
  filter_upwards [(AggregateUncertaintyMeasure.pv_term_c bohnGrowthLaw bohn_hR hs 0 j).2]
    with ω h
  rw [h, hcore, bohn_mom, cons_zero]
  simp [bohnC]

end Cochrane.FiscalConstraints.AggregateUncertaintyMeasure
