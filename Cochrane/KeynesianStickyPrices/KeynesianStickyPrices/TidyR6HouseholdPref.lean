/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6HouseholdMeasureTVC

/-!
# The household problem with preference shocks

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 119 ("IS shocks to
(5.1) can be formalized as discount rate shocks"), and Chapter 17, eq. (17.15), p. 407 ("We can
write `u_{x,t} = −σu_{r,t}` to interpret the IS disturbance in units of an interest rate
distortion").

The household of TidyR6HouseholdMeasure, with a **preference shock**: it maximises
`E ∑ βᵗ ξ_t u(C_t)` where the weight `ξ_t > 0` is adapted and essentially bounded (a discount-rate
shock when `ξ_{t+1}/ξ_t` is known at `t`). The proofs adapt those of TidyR6HouseholdMeasure and
TidyR6HouseholdMeasureTVC (the felicity `ξ_tu(C_t)` replaces `u(C_t)`); the expected utility is
expressed through those modules' `Admissible` and `expUtil` applied to the felicity stream
`felic` with the identity function.

## Main results

* `foc_le_w`, `euler_interior_w`, `euler_of_pos_w` (**necessity**): in an optimal plan, almost
  surely where bonds are held, `Q_tξ_tu′(c_t)/P_t = βE_t[ξ_{t+1}u′(c_{t+1})/P_{t+1}]`.
* `partial_bound_w`: for a candidate satisfying that Euler equation and any competitor that is
  feasible with possibly **different taxes** `s′`, the discounted felicity gain up to `N` is at
  most `β^N E[ξ_Nu′(c_N)B_{N−1}/P_N] + ∑_{n<N} βⁿE[ξ_nu′(c_n)(s_n − s′_n)]`. With `s′ = s` this
  gives `optimal_of_euler_tvc_w` (**sufficiency**, concave increasing `u`, transversality
  condition); with other `s′` it is the household half of the joint yeoman-farmer problem
  (TidyR6JointYeoman).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6HouseholdPref

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6HouseholdMeasureTVC

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), p. 119: the felicity stream `ξ_n u(c_n)` of a consumption plan. -/
def felic (w : ℕ → Ω → ℝ) (u : ℝ → ℝ) (c : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => w n ω * u (c n ω)

variable (S) in
/-- Cochrane (2023), p. 119, the household with preference shocks: a feasible plan whose
felicity stream is admissible and which no feasible admissible plan beats in
`E ∑ βⁿ ξ_n u(c_n)`. -/
def OptimalP (β y : ℝ) (u : ℝ → ℝ) (w P s Q : ℕ → Ω → ℝ) (b₀ : Ω → ℝ) (c b : ℕ → Ω → ℝ) :
    Prop :=
  Feasible S y P s Q b₀ c b ∧ Admissible S β (fun x => x) (felic w u c) ∧
    ∀ c' b', Feasible S y P s Q b₀ c' b' → Admissible S β (fun x => x) (felic w u c') →
      expUtil S β (fun x => x) (felic w u c') ≤ expUtil S β (fun x => x) (felic w u c)

variable (S) in
/-- Cochrane (2023), p. 119: the Euler gap with preference shocks,
`Q_tξ_tu′(c_t)/P_t − βE_t[ξ_{t+1}u′(c_{t+1})/P_{t+1}]`. -/
noncomputable def eulerGapW (β : ℝ) (u' : ℝ → ℝ) (w P Q c : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => Q t ω * (w t ω * u' (c t ω) / P t ω) -
    β * S.E t (fun ω => w (t + 1) ω * u' (c (t + 1) ω) / P (t + 1) ω) ω

/-- Cochrane (2023), p. 21 (differentiation under the integral sign, with a bounded weight): if
`v` has continuous derivative `v'`, and `w`, `f`, `g` are essentially bounded, then
`ε ↦ E[w v(f + εg)]` has derivative `E[w v′(f) g]` at `0`. -/
theorem hasDerivAt_integral_comp_w {μ : Measure Ω} [IsFiniteMeasure μ] {v v' : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : Continuous v') {w f g : Ω → ℝ}
    (hw : AEStronglyMeasurable w μ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) {Mw Mf Mg : ℝ} (hwM : ∀ᵐ ω ∂μ, |w ω| ≤ Mw)
    (hfM : ∀ᵐ ω ∂μ, |f ω| ≤ Mf) (hgM : ∀ᵐ ω ∂μ, |g ω| ≤ Mg) :
    HasDerivAt (fun ε => ∫ ω, w ω * v (f ω + ε * g ω) ∂μ)
      (∫ ω, w ω * v' (f ω) * g ω ∂μ) 0 := by
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun x => (hv x).continuousAt
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuous hv' (Mf + Mg)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun ε ω => w ω * v (f ω + ε * g ω))
    (F' := fun ε ω => w ω * v' (f ω + ε * g ω) * g ω)
    (bound := fun _ => Mw * C * Mg) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun ε => hw.mul (hvc.comp_aestronglyMeasurable
      (hf.add (hg.const_mul ε))))
    (by
      refine (integrable_comp_of_bdd hvc hf hfM).bdd_mul hw (c := Mw) ?_ |>.congr
        (Eventually.of_forall fun ω => by simp)
      exact hwM.mono fun ω h => by rwa [Real.norm_eq_abs])
    ((hw.mul (hv'.comp_aestronglyMeasurable (hf.add (hg.const_mul 0)))).mul hg) ?_
    (integrable_const _) ?_
  · simpa using key.2
  · filter_upwards [hwM, hfM, hgM] with ω h0 h1 h2
    intro ε hε
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hε
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hMg : 0 ≤ Mg := (abs_nonneg _).trans h2
    have hx : |f ω + ε * g ω| ≤ Mf + Mg := by
      calc |f ω + ε * g ω| ≤ |f ω| + |ε| * |g ω| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ Mf + 1 * Mg :=
            add_le_add h1 (mul_le_mul hε.le h2 (abs_nonneg _) zero_le_one)
        _ = Mf + Mg := by ring
    have hMw : 0 ≤ Mw := (abs_nonneg _).trans h0
    exact mul_le_mul (mul_le_mul h0 (hC _ hx) (abs_nonneg _) hMw) h2 (abs_nonneg _)
      (mul_nonneg hMw hC0)
  · refine Eventually.of_forall fun ω ε _ => ?_
    have h1 : HasDerivAt (fun ε => f ω + ε * g ω) (g ω) ε := by
      simpa using (hasDerivAt_mul_const (g ω)).const_add (f ω)
    have := ((hv _).comp ε h1).const_mul (w ω)
    exact this.congr_deriv (by ring)

/-- Cochrane (2023), p. 21 with p. 119, the household's first-order condition in variational
form, with preference shocks: in an optimal plan (regularity `EulerRegular` at `t`, weights
adapted and essentially bounded at `t` and `t + 1`), for a bounded `𝓕_t`-measurable `z` keeping
debt nonnegative for small steps, `E[z · eulerGapW] ≤ 0`. -/
theorem foc_le_w {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {w P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : OptimalP S β y u w P s Q b₀ c b) (hwad : StronglyAdapted S.𝓕 w)
    (hPad : StronglyAdapted S.𝓕 P) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ}
    (hQt : StronglyMeasurable[S.𝓕 t] (Q t)) (hreg : EulerRegular S P Q c t)
    (hw0 : BddAt S (w t)) (hw1 : BddAt S (w (t + 1))) {z : Ω → ℝ}
    (hz : StronglyMeasurable[S.𝓕 t] z) (hzb : BddAt S z) {η : ℝ} (hη : 0 < η)
    (hfz : ∀ ε, 0 < ε → ε < η → ∀ᵐ ω ∂S.μ, 0 ≤ b (t + 1) ω - ε * z ω) :
    ∫ ω, z ω * eulerGapW S β u' w P Q c t ω ∂S.μ ≤ 0 := by
  obtain ⟨hc0, hc1, hQb, hPi0, hPi1⟩ := hreg
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hfeas := hopt.1
  have hcad := hfeas.2.1
  have hz1 : StronglyMeasurable[S.𝓕 (t + 1)] z := hz.mono (S.𝓕.mono (Nat.le_succ t))
  set a : Ω → ℝ := fun ω => Q t ω * z ω * (P t ω)⁻¹ with ha
  set a' : Ω → ℝ := fun ω => -(z ω * (P (t + 1) ω)⁻¹) with ha'
  have ham : AEStronglyMeasurable a S.μ :=
    ((hQt.measurable.mul hz.measurable).mul (hPad t).measurable.inv).stronglyMeasurable.mono
      (S.𝓕.le t) |>.aestronglyMeasurable
  have ham' : AEStronglyMeasurable a' S.μ :=
    (hz1.measurable.mul (hPad (t + 1)).measurable.inv).neg.stronglyMeasurable.mono
      (S.𝓕.le (t + 1)) |>.aestronglyMeasurable
  have hab : BddAt S a := (hQb.mul hzb).mul hPi0
  have hab' : BddAt S a' := (hzb.mul hPi1).neg
  have hc0m : AEStronglyMeasurable (c t) S.μ := ((hcad t).mono (S.𝓕.le t)).aestronglyMeasurable
  have hc1m : AEStronglyMeasurable (c (t + 1)) S.μ :=
    ((hcad (t + 1)).mono (S.𝓕.le (t + 1))).aestronglyMeasurable
  have hw0m : AEStronglyMeasurable (w t) S.μ := ((hwad t).mono (S.𝓕.le t)).aestronglyMeasurable
  have hw1m : AEStronglyMeasurable (w (t + 1)) S.μ :=
    ((hwad (t + 1)).mono (S.𝓕.le (t + 1))).aestronglyMeasurable
  obtain ⟨Mc0, hMc0⟩ := hc0
  obtain ⟨Mc1, hMc1⟩ := hc1
  obtain ⟨Ma, hMa⟩ := hab
  obtain ⟨Ma', hMa'⟩ := hab'
  obtain ⟨Mw0, hMw0⟩ := hw0
  obtain ⟨Mw1, hMw1⟩ := hw1
  -- integrability of the perturbed felicities
  have hint : ∀ (v f g : Ω → ℝ) (Mv Mf Mg ε : ℝ), AEStronglyMeasurable v S.μ →
      AEStronglyMeasurable f S.μ → AEStronglyMeasurable g S.μ → (∀ᵐ ω ∂S.μ, |v ω| ≤ Mv) →
      (∀ᵐ ω ∂S.μ, |f ω| ≤ Mf) → (∀ᵐ ω ∂S.μ, |g ω| ≤ Mg) →
      Integrable (fun ω => v ω * u (f ω + ε * g ω)) S.μ := by
    intro v f g Mv Mf Mg ε hv hf hg hvM hfM hgM
    refine (integrable_comp_of_bdd huc (hf.add (hg.const_mul ε)) (R := Mf + |ε| * Mg) ?_).bdd_mul
      hv (c := Mv) (hvM.mono fun ω h => by rwa [Real.norm_eq_abs]) |>.congr
      (Eventually.of_forall fun ω => by simp)
    filter_upwards [hfM, hgM] with ω h1 h2
    calc |f ω + ε * g ω| ≤ |f ω| + |ε| * |g ω| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ Mf + |ε| * Mg := add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg ε))
  -- the felicity of the deviation
  set φ : ℝ → ℝ := fun ε =>
    β ^ t * (∫ ω, w t ω * u (c t ω + ε * a ω) ∂S.μ - ∫ ω, w t ω * u (c t ω) ∂S.μ) +
      β ^ (t + 1) * (∫ ω, w (t + 1) ω * u (c (t + 1) ω + ε * a' ω) ∂S.μ -
        ∫ ω, w (t + 1) ω * u (c (t + 1) ω) ∂S.μ) with hφ
  have hval : ∀ ε, Admissible S β (fun x => x) (felic w u (devC P Q c z t ε)) ∧
      expUtil S β (fun x => x) (felic w u (devC P Q c z t ε)) =
        expUtil S β (fun x => x) (felic w u c) + φ ε := by
    intro ε
    have h := admissible_modify hβ hopt.2.1 {t, t + 1} (c' := felic w u (devC P Q c z t ε))
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
        funext ω
        simp only [felic, devC, hn.1, hn.2, ↓reduceIte])
      (fun n hn => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rcases hn with rfl | rfl
        · simp only [felic, devC, ↓reduceIte]
          exact hint _ _ _ _ _ _ ε hw0m hc0m ham hMw0 hMc0 hMa
        · simp only [felic, devC, (show t + 1 ≠ t by omega), ↓reduceIte]
          exact hint _ _ _ _ _ _ ε hw1m hc1m ham' hMw1 hMc1 hMa')
    refine ⟨h.1, h.2.trans ?_⟩
    rw [Finset.sum_pair (show t ≠ t + 1 by omega)]
    simp only [felic, devC, ↓reduceIte, (show t + 1 ≠ t by omega), hφ]
    rfl
  -- the derivative
  have hd0 := hasDerivAt_integral_comp_w hu hu' hw0m hc0m ham hMw0 hMc0 hMa
  have hd1 := hasDerivAt_integral_comp_w hu hu' hw1m hc1m ham' hMw1 hMc1 hMa'
  have hD : HasDerivAt φ (β ^ t * ∫ ω, w t ω * u' (c t ω) * a ω ∂S.μ +
      β ^ (t + 1) * ∫ ω, w (t + 1) ω * u' (c (t + 1) ω) * a' ω ∂S.μ) 0 :=
    ((hd0.sub_const _).const_mul (β ^ t)).add ((hd1.sub_const _).const_mul (β ^ (t + 1)))
  have hle := deriv_nonpos_of_le hD (by simp [hφ]) hη fun ε hε hεη => by
    have h1 := hopt.2.2 _ _ (dev_feasible hfeas hPad hQt hP hz (hfz ε hε hεη)) (hval ε).1
    rw [(hval ε).2] at h1
    linarith
  -- rewrite the derivative as `β^t E[z · gap]`
  set X : Ω → ℝ := fun ω => w (t + 1) ω * u' (c (t + 1) ω) / P (t + 1) ω with hX
  have hXb : BddAt S X := by
    have := BddAt.mul (S := S) ⟨Mw1, hMw1⟩
      ((BddAt.comp hu' ⟨Mc1, hMc1⟩).mul hPi1)
    simpa [hX, div_eq_mul_inv, mul_assoc] using this
  have hXm : AEStronglyMeasurable X S.μ :=
    (((hwad (t + 1)).measurable.mul (hu'.measurable.comp (hcad (t + 1)).measurable)).div
      (hPad (t + 1)).measurable).stronglyMeasurable.mono (S.𝓕.le (t + 1)) |>.aestronglyMeasurable
  have hXi : Integrable X S.μ := hXb.integrable hXm
  obtain ⟨K, hK⟩ := hzb
  have hzm : AEStronglyMeasurable z S.μ := (hz.mono (S.𝓕.le t)).aestronglyMeasurable
  set A : Ω → ℝ := fun ω => Q t ω * (w t ω * u' (c t ω) / P t ω) with hA
  have hAb : BddAt S A := by
    have := hQb.mul (BddAt.mul (S := S) ⟨Mw0, hMw0⟩
      ((BddAt.comp hu' ⟨Mc0, hMc0⟩).mul hPi0))
    simpa [hA, div_eq_mul_inv, mul_assoc] using this
  have hAm : AEStronglyMeasurable A S.μ :=
    (hQt.measurable.mul (((hwad t).measurable.mul (hu'.measurable.comp (hcad t).measurable)).div
      (hPad t).measurable)).stronglyMeasurable.mono (S.𝓕.le t) |>.aestronglyMeasurable
  have hzA : Integrable (fun ω => z ω * A ω) S.μ :=
    (BddAt.mul ⟨K, hK⟩ hAb).integrable (hzm.mul hAm)
  have hzE : Integrable (fun ω => z ω * S.E t X ω) S.μ :=
    (BddAt.mul ⟨K, hK⟩ (hXb.E t)).integrable (hzm.mul (S.integrable_E t X).aestronglyMeasurable)
  have e1 : ∫ ω, w t ω * u' (c t ω) * a ω ∂S.μ = ∫ ω, z ω * A ω ∂S.μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [ha, hA, div_eq_mul_inv]
    ring
  have e2 : ∫ ω, w (t + 1) ω * u' (c (t + 1) ω) * a' ω ∂S.μ = -∫ ω, z ω * S.E t X ω ∂S.μ := by
    rw [← integral_mul_E hz hK hXi, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [ha', hX, div_eq_mul_inv]
    ring
  have e3 : ∫ ω, z ω * eulerGapW S β u' w P Q c t ω ∂S.μ =
      ∫ ω, z ω * A ω ∂S.μ - β * ∫ ω, z ω * S.E t X ω ∂S.μ := by
    rw [← integral_const_mul, ← integral_sub hzA (hzE.const_mul β)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [eulerGapW, hA, hX]
    ring
  rw [e1, e2] at hle
  rw [e3]
  have hbt : 0 < β ^ t := pow_pos hβ t
  have : β ^ t * (∫ ω, z ω * A ω ∂S.μ - β * ∫ ω, z ω * S.E t X ω ∂S.μ) ≤ 0 := by
    rw [pow_succ] at hle
    linarith
  by_contra hcon
  push Not at hcon
  linarith [mul_pos hbt hcon]

/-- Cochrane (2023), p. 119: the weighted Euler gap is known at `t`. -/
theorem eulerGapW_sm {β : ℝ} {u' : ℝ → ℝ} (hu' : Continuous u') {w P Q c : ℕ → Ω → ℝ}
    (hwad : StronglyAdapted S.𝓕 w) (hcad : StronglyAdapted S.𝓕 c) (hPad : StronglyAdapted S.𝓕 P)
    {t : ℕ} (hQt : StronglyMeasurable[S.𝓕 t] (Q t)) :
    StronglyMeasurable[S.𝓕 t] (eulerGapW S β u' w P Q c t) :=
  ((hQt.measurable.mul (((hwad t).measurable.mul (hu'.measurable.comp (hcad t).measurable)).div
    (hPad t).measurable)).sub
    ((S.stronglyMeasurable_E t _).measurable.const_mul β)).stronglyMeasurable

/-- Cochrane (2023), p. 119: the weighted Euler gap is essentially bounded. -/
theorem eulerGapW_bdd {β : ℝ} {u' : ℝ → ℝ} (hu' : Continuous u') {w P Q c : ℕ → Ω → ℝ} {t : ℕ}
    (hreg : EulerRegular S P Q c t) (hw0 : BddAt S (w t)) (hw1 : BddAt S (w (t + 1))) :
    BddAt S (eulerGapW S β u' w P Q c t) := by
  have hX : BddAt S (fun ω => w (t + 1) ω * u' (c (t + 1) ω) / P (t + 1) ω) := by
    have := hw1.mul ((BddAt.comp hu' hreg.2.1).mul hreg.2.2.2.2)
    simpa [div_eq_mul_inv, mul_assoc] using this
  have h1 := hreg.2.2.1.mul (hw0.mul ((BddAt.comp hu' hreg.1).mul hreg.2.2.2.1))
  have h2 := ((BddAt.const (S := S) β).mul (hX.E t)).neg
  have := h1.add h2
  unfold eulerGapW
  simpa [div_eq_mul_inv, sub_eq_add_neg, mul_assoc] using this

/-- Cochrane (2023), p. 21 with p. 119, **the Euler equation with preference shocks where bonds
are held**: in an optimal plan, almost surely on `{B_t > 0}`,
`Q_tξ_tu′(c_t)/P_t = βE_t[ξ_{t+1}u′(c_{t+1})/P_{t+1}]`. -/
theorem euler_interior_w {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') {w P s Q c b : ℕ → Ω → ℝ}
    {b₀ : Ω → ℝ} (hopt : OptimalP S β y u w P s Q b₀ c b) (hwad : StronglyAdapted S.𝓕 w)
    (hPad : StronglyAdapted S.𝓕 P) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ}
    (hQt : StronglyMeasurable[S.𝓕 t] (Q t)) (hreg : EulerRegular S P Q c t)
    (hw0 : BddAt S (w t)) (hw1 : BddAt S (w (t + 1))) :
    ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω →
      Q t ω * (w t ω * u' (c t ω) / P t ω) =
        β * S.E t (fun ω => w (t + 1) ω * u' (c (t + 1) ω) / P (t + 1) ω) ω := by
  set g := eulerGapW S β u' w P Q c t with hg
  have hgm : StronglyMeasurable[S.𝓕 t] g := eulerGapW_sm hu' hwad hopt.1.2.1 hPad hQt
  obtain ⟨K, hK0, hK⟩ := (eulerGapW_bdd (β := β) hu' hreg hw0 hw1).exists_pos
  have key : ∀ k : ℕ, ∀ᵐ ω ∂S.μ, 1 / ((k : ℝ) + 1) ≤ b (t + 1) ω → g ω = 0 := by
    intro k
    set δ : ℝ := 1 / ((k : ℝ) + 1) with hδ
    have hδ0 : 0 < δ := by positivity
    set A : Set Ω := {ω | δ ≤ b (t + 1) ω} with hAdef
    have hA : MeasurableSet[S.𝓕 t] A :=
      measurableSet_le measurable_const (hopt.1.2.2.1 t).measurable
    set z : Ω → ℝ := A.indicator g with hzdef
    have hz : StronglyMeasurable[S.𝓕 t] z := hgm.indicator hA
    have hzK : ∀ᵐ ω ∂S.μ, |z ω| ≤ K := hK.mono fun ω h => by
      by_cases hω : ω ∈ A
      · rwa [hzdef, Set.indicator_of_mem hω]
      · rw [hzdef, Set.indicator_of_notMem hω, abs_zero]
        exact (abs_nonneg _).trans h
    have hfz : ∀ ε, 0 < ε → ε < δ / K → ∀ᵐ ω ∂S.μ, 0 ≤ b (t + 1) ω - ε * z ω := by
      intro ε hε hεδ
      filter_upwards [hK, hopt.1.2.2.2.2 (t + 1)] with ω hk hb
      by_cases hω : ω ∈ A
      · rw [hzdef, Set.indicator_of_mem hω]
        have h1 : ε * g ω ≤ ε * K :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hk) hε.le
        have h2 : ε * K < δ := by rwa [lt_div_iff₀ hK0] at hεδ
        have h3 : δ ≤ b (t + 1) ω := hω
        linarith
      · rw [hzdef, Set.indicator_of_notMem hω, mul_zero, sub_zero]
        exact hb
    have h := foc_le_w hβ hu hu' hopt hwad hPad hP hQt hreg hw0 hw1 hz ⟨K, hzK⟩
      (div_pos hδ0 hK0) hfz
    have hnn : 0 ≤ᵐ[S.μ] fun ω => z ω * g ω := Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ A
      · simp only [Pi.zero_apply, hzdef, Set.indicator_of_mem hω]
        exact mul_self_nonneg _
      · simp [hzdef, Set.indicator_of_notMem hω]
    have hint : Integrable (fun ω => z ω * g ω) S.μ :=
      (BddAt.mul ⟨K, hzK⟩ ⟨K, hK⟩).integrable
        ((hz.mul hgm).mono (S.𝓕.le t)).aestronglyMeasurable
    have h0 : ∫ ω, z ω * g ω ∂S.μ = 0 := le_antisymm h (integral_nonneg_of_ae hnn)
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0] with ω hω hδb
    have hzg : z ω = g ω := by rw [hzdef, Set.indicator_of_mem (show ω ∈ A from hδb)]
    have : z ω * g ω = 0 := hω
    rw [hzg] at this
    exact mul_self_eq_zero.1 this
  filter_upwards [ae_all_iff.2 key] with ω h hb
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hb
  have := h k hk.le
  simp only [hg, eulerGapW] at this
  linarith

/-- Cochrane (2023), p. 119, **necessity**: if the household holds bonds almost surely, the
Euler equation with preference shocks holds almost surely. -/
theorem euler_of_pos_w {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : Continuous u') {w P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : OptimalP S β y u w P s Q b₀ c b) (hwad : StronglyAdapted S.𝓕 w)
    (hPad : StronglyAdapted S.𝓕 P) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ}
    (hQt : StronglyMeasurable[S.𝓕 t] (Q t)) (hreg : EulerRegular S P Q c t)
    (hw0 : BddAt S (w t)) (hw1 : BddAt S (w (t + 1))) (hb : ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω) :
    (fun ω => Q t ω * (w t ω * u' (c t ω) / P t ω)) =ᵐ[S.μ]
      β • S.E t (fun ω => w (t + 1) ω * u' (c (t + 1) ω) / P (t + 1) ω) := by
  filter_upwards [euler_interior_w hβ hu hu' hopt hwad hPad hP hQt hreg hw0 hw1, hb] with ω h1 h2
  exact h1 h2

/-! ### Sufficiency -/

/-- Cochrane (2023), p. 22 and Online Appendix A1.1, p. 556, the household's **budget comparison**
with preference shocks: let the candidate `(c, b)` be feasible with taxes `s` and satisfy the
weighted Euler equation at every date, and let the competitor `(c′, b′)` be feasible with taxes
`s′` (same initial debt, same prices). For concave increasing differentiable `u` and weights
`ξ ≥ 0`, with the integrability of the quantities involved,
`∑_{n<N} βⁿ(E ξ_nu(c′_n) − E ξ_nu(c_n)) ≤ β^N E[ξ_Nu′(c_N)B_{N−1}/P_N] +
∑_{n<N} βⁿ E[ξ_nu′(c_n)(s_n − s′_n)]`. -/
theorem partial_bound_w {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    {w P s s' Q c b c' b' : ℕ → Ω → ℝ} {b₀ : Ω → ℝ} (hw0 : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ w n ω)
    (hfeas : Feasible S y P s Q b₀ c b) (hf' : Feasible S y P s' Q b₀ c' b')
    (hci : ∀ n, Integrable (felic w u c n) S.μ) (hc'i : ∀ n, Integrable (felic w u c' n) S.μ)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hm : ∀ n, Integrable (fun ω => w n ω * u' (c n ω) / P n ω) S.μ)
    (hW : ∀ n, Integrable (fun ω => w n ω * u' (c n ω) * b n ω / P n ω) S.μ)
    (hδ : ∀ n, Integrable (fun ω => w n ω * u' (c n ω) * (s n ω - s' n ω)) S.μ)
    (heul : ∀ n, ∀ᵐ ω ∂S.μ, Q n ω * (w n ω * u' (c n ω) / P n ω) =
      β * S.E n (fun ω => w (n + 1) ω * u' (c (n + 1) ω) / P (n + 1) ω) ω) (N : ℕ) :
    ∑ n ∈ Finset.range N, β ^ n * (∫ ω, felic w u c' n ω ∂S.μ - ∫ ω, felic w u c n ω ∂S.μ) ≤
      β ^ N * ∫ ω, w N ω * u' (c N ω) * b N ω / P N ω ∂S.μ +
        ∑ n ∈ Finset.range N, β ^ n * ∫ ω, w n ω * u' (c n ω) * (s n ω - s' n ω) ∂S.μ := by
  obtain ⟨hb0, -, hbad, hflow, -⟩ := hfeas
  obtain ⟨hb0', -, hbad', hflow', hbnn'⟩ := hf'
  have hu'0 : ∀ x, 0 ≤ u' x := fun x => deriv_nonneg_of_monotone hmono (hu x)
  set m : ℕ → Ω → ℝ := fun n ω => w n ω * u' (c n ω) / P n ω with hmdef
  set W : ℕ → Ω → ℝ := fun n ω => w n ω * u' (c n ω) * b n ω / P n ω with hWdef
  set W' : ℕ → Ω → ℝ := fun n ω => w n ω * u' (c n ω) * b' n ω / P n ω with hW'def
  set δ : ℕ → Ω → ℝ := fun n ω => w n ω * u' (c n ω) * (s n ω - s' n ω) with hδdef
  set D : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N,
    β ^ n * (∫ ω, felic w u c' n ω ∂S.μ - ∫ ω, felic w u c n ω ∂S.μ) with hDdef
  set G : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, β ^ n * ∫ ω, δ n ω ∂S.μ with hGdef
  have hm0 : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ m n ω := fun n => by
    filter_upwards [hP n, hw0 n] with ω h hw
    exact div_nonneg (mul_nonneg hw (hu'0 _)) h.le
  -- the pointwise first-order bound at date `N`
  have hpt : ∀ N, ∀ᵐ ω ∂S.μ, felic w u c' N ω - felic w u c N ω ≤ W' N ω - W N ω -
      β * (b' (N + 1) ω * S.E N (m (N + 1)) ω) + β * (b (N + 1) ω * S.E N (m (N + 1)) ω) +
        δ N ω := by
    intro N
    filter_upwards [hflow N, hflow' N, hP N, heul N, hw0 N] with ω h1 h2 hp he hw
    have ht := concave_le_tangent hconc (hu (c N ω)) (c' N ω)
    have ht' : w N ω * u (c' N ω) - w N ω * u (c N ω) ≤
        w N ω * u' (c N ω) * (c' N ω - c N ω) := by
      have := mul_le_mul_of_nonneg_left ht hw
      nlinarith
    have hp0 := hp.ne'
    have hfd : b' N ω - b N ω - Q N ω * b' (N + 1) ω + Q N ω * b (N + 1) ω +
        P N ω * (s N ω - s' N ω) = P N ω * (c' N ω - c N ω) := by linarith
    have e : w N ω * u' (c N ω) * (c' N ω - c N ω) = W' N ω - W N ω -
        Q N ω * (w N ω * u' (c N ω) / P N ω) * b' (N + 1) ω +
          Q N ω * (w N ω * u' (c N ω) / P N ω) * b (N + 1) ω + δ N ω := by
      calc w N ω * u' (c N ω) * (c' N ω - c N ω) =
            w N ω * u' (c N ω) / P N ω * (P N ω * (c' N ω - c N ω)) := by field_simp
        _ = w N ω * u' (c N ω) / P N ω * (b' N ω - b N ω - Q N ω * b' (N + 1) ω +
            Q N ω * b (N + 1) ω + P N ω * (s N ω - s' N ω)) := by rw [hfd]
        _ = _ := by
          simp only [hW'def, hWdef, hδdef]
          field_simp
    rw [he] at e
    have : m (N + 1) = fun ω => w (N + 1) ω * u' (c (N + 1) ω) / P (N + 1) ω := rfl
    rw [this]
    simp only [felic]
    linarith
  -- the induction
  have claim : ∀ N, Integrable (W' N) S.μ ∧
      D N ≤ β ^ N * (∫ ω, W N ω ∂S.μ - ∫ ω, W' N ω ∂S.μ) + G N := by
    intro N
    induction N with
    | zero =>
      have e : W' 0 = W 0 := by
        funext ω
        simp only [hW'def, hWdef, hb0, hb0']
      refine ⟨e ▸ hW 0, ?_⟩
      simp [hDdef, hGdef, e]
    | succ N ih =>
      obtain ⟨hiW', hD⟩ := ih
      have hbm : ∀ (bb : ℕ → Ω → ℝ), (fun ω => w (N + 1) ω * u' (c (N + 1) ω) *
          bb (N + 1) ω / P (N + 1) ω) = bb (N + 1) * m (N + 1) := fun bb => by
        funext ω
        simp only [hmdef, Pi.mul_apply]
        ring
      have hpoC := condExp_mul_of_stronglyMeasurable_left (hbad N)
        ((hbm b) ▸ hW (N + 1)) (hm (N + 1))
      have hVC_i : Integrable (fun ω => b (N + 1) ω * S.E N (m (N + 1)) ω) S.μ :=
        (S.integrable_E N _).congr hpoC
      have hVC_eq : ∫ ω, b (N + 1) ω * S.E N (m (N + 1)) ω ∂S.μ = ∫ ω, W (N + 1) ω ∂S.μ := by
        have : W (N + 1) = b (N + 1) * m (N + 1) := hbm b
        rw [this, ← S.integral_E N (b (N + 1) * m (N + 1))]
        exact (integral_congr_ae hpoC).symm
      have hEm0 : ∀ᵐ ω ∂S.μ, 0 ≤ S.E N (m (N + 1)) ω :=
        condExp_nonneg (m := S.𝓕 N) (hm0 (N + 1))
      have hV0 : ∀ᵐ ω ∂S.μ, 0 ≤ b' (N + 1) ω * S.E N (m (N + 1)) ω := by
        filter_upwards [hbnn' (N + 1), hEm0] with ω h1 h2
        exact mul_nonneg h1 h2
      have hVm : AEStronglyMeasurable (fun ω => b' (N + 1) ω * S.E N (m (N + 1)) ω) S.μ :=
        ((hbad' N).mono (S.𝓕.le N)).aestronglyMeasurable.mul
          (S.integrable_E N _).aestronglyMeasurable
      have hbound_i : Integrable (fun ω => β⁻¹ * (W' N ω - W N ω +
          β * (b (N + 1) ω * S.E N (m (N + 1)) ω) + δ N ω -
            (felic w u c' N ω - felic w u c N ω))) S.μ :=
        (((((hiW'.sub (hW N)).add (hVC_i.const_mul β)).add (hδ N)).sub
          ((hc'i N).sub (hci N)))).const_mul _
      have hV_i : Integrable (fun ω => b' (N + 1) ω * S.E N (m (N + 1)) ω) S.μ := by
        refine Integrable.mono' hbound_i hVm ?_
        filter_upwards [hpt N, hV0] with ω h1 h2
        rw [Real.norm_eq_abs, abs_of_nonneg h2, le_inv_mul_iff₀ hβ]
        linarith
      obtain ⟨hiW'1, hW'eq⟩ := integrable_mul_of_E (hbad' N) (hbnn' (N + 1)) (hm (N + 1))
        (hm0 (N + 1)) hV_i
      have hW'1 : W' (N + 1) = fun ω => b' (N + 1) ω * m (N + 1) ω := hbm b'
      have hI : ∫ ω, felic w u c' N ω ∂S.μ - ∫ ω, felic w u c N ω ∂S.μ ≤
          ∫ ω, W' N ω ∂S.μ - ∫ ω, W N ω ∂S.μ -
            β * ∫ ω, b' (N + 1) ω * S.E N (m (N + 1)) ω ∂S.μ +
              β * ∫ ω, b (N + 1) ω * S.E N (m (N + 1)) ω ∂S.μ + ∫ ω, δ N ω ∂S.μ := by
        have iA : Integrable (fun ω => felic w u c' N ω - felic w u c N ω) S.μ :=
          (hc'i N).sub (hci N)
        have iB : Integrable (fun ω => W' N ω - W N ω) S.μ := hiW'.sub (hW N)
        have iC : Integrable (fun ω => β * (b' (N + 1) ω * S.E N (m (N + 1)) ω)) S.μ :=
          hV_i.const_mul β
        have iD : Integrable (fun ω => β * (b (N + 1) ω * S.E N (m (N + 1)) ω)) S.μ :=
          hVC_i.const_mul β
        have iBC : Integrable (fun ω => W' N ω - W N ω -
            β * (b' (N + 1) ω * S.E N (m (N + 1)) ω)) S.μ := iB.sub iC
        have iBCD : Integrable (fun ω => W' N ω - W N ω -
            β * (b' (N + 1) ω * S.E N (m (N + 1)) ω) +
              β * (b (N + 1) ω * S.E N (m (N + 1)) ω)) S.μ := iBC.add iD
        have hmono : ∫ ω, (felic w u c' N ω - felic w u c N ω) ∂S.μ ≤
            ∫ ω, (W' N ω - W N ω - β * (b' (N + 1) ω * S.E N (m (N + 1)) ω) +
              β * (b (N + 1) ω * S.E N (m (N + 1)) ω) + δ N ω) ∂S.μ :=
          integral_mono_ae iA (iBCD.add (hδ N)) (hpt N)
        rw [integral_sub (hc'i N) (hci N), integral_add iBCD (hδ N), integral_add iBC iD,
          integral_sub iB iC, integral_sub hiW' (hW N), integral_const_mul,
          integral_const_mul] at hmono
        exact hmono
      refine ⟨hW'1 ▸ hiW'1, ?_⟩
      have hDs : D (N + 1) = D N +
          β ^ N * (∫ ω, felic w u c' N ω ∂S.μ - ∫ ω, felic w u c N ω ∂S.μ) := by
        simp only [hDdef, Finset.sum_range_succ]
      have hGs : G (N + 1) = G N + β ^ N * ∫ ω, δ N ω ∂S.μ := by
        simp only [hGdef, Finset.sum_range_succ]
      rw [hDs, hGs, hW'1, hW'eq, ← hVC_eq, pow_succ]
      have hbN := pow_nonneg hβ.le N
      nlinarith [mul_le_mul_of_nonneg_left hI hbN]
  obtain ⟨-, hD⟩ := claim N
  have hW'0 : 0 ≤ ∫ ω, W' N ω ∂S.μ := integral_nonneg_of_ae (by
    filter_upwards [hbnn' N, hP N, hw0 N] with ω h1 h2 h3
    exact div_nonneg (mul_nonneg (mul_nonneg h3 (hu'0 _)) h1) h2.le)
  have := mul_nonneg (pow_nonneg hβ.le N) hW'0
  have e : ∫ ω, W N ω ∂S.μ = ∫ ω, w N ω * u' (c N ω) * b N ω / P N ω ∂S.μ := rfl
  change D N ≤ _
  rw [← e]
  change D N ≤ β ^ N * ∫ ω, W N ω ∂S.μ + G N
  nlinarith

/-- Cochrane (2023), p. 21 with p. 119, **sufficiency with preference shocks**: a feasible plan
with admissible felicity, concave increasing differentiable `u`, weights `ξ ≥ 0`, positive prices,
the weighted Euler equation at every date, the integrability of `ξ_nu′(c_n)/P_n` and
`ξ_nu′(c_n)B_{n−1}/P_n`, and the transversality condition `β^N E[ξ_Nu′(c_N)B_{N−1}/P_N] → 0`
is optimal. -/
theorem optimal_of_euler_tvc_w {β y : ℝ} (hβ : 0 < β) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    {w P s Q c b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ} (hw0 : ∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ w n ω)
    (hfeas : Feasible S y P s Q b₀ c b) (hadm : Admissible S β (fun x => x) (felic w u c))
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hm : ∀ n, Integrable (fun ω => w n ω * u' (c n ω) / P n ω) S.μ)
    (hW : ∀ n, Integrable (fun ω => w n ω * u' (c n ω) * b n ω / P n ω) S.μ)
    (heul : ∀ n, ∀ᵐ ω ∂S.μ, Q n ω * (w n ω * u' (c n ω) / P n ω) =
      β * S.E n (fun ω => w (n + 1) ω * u' (c (n + 1) ω) / P (n + 1) ω) ω)
    (htvc : Tendsto (fun N => β ^ N * ∫ ω, w N ω * u' (c N ω) * b N ω / P N ω ∂S.μ) atTop
      (𝓝 0)) :
    OptimalP S β y u w P s Q b₀ c b := by
  refine ⟨hfeas, hadm, fun c' b' hf' hadm' => ?_⟩
  have hD := partial_bound_w hβ hu hconc hmono hw0 hfeas hf' (hadm.integrable hβ)
    (hadm'.integrable hβ) hP hm hW (fun n => (integrable_const 0).congr
      (Eventually.of_forall fun ω => by simp)) heul
  have hlim := le_of_tendsto_of_tendsto' (tendsto_partial_utilDiff hβ hadm hadm') htvc
    fun N => by simpa using hD N
  linarith

end Cochrane.KeynesianStickyPrices.TidyR6HouseholdPref
