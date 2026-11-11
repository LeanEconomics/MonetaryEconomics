/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR9PositiveDiscount
import Generality.TidyR8ShortDebtRealForm

/-!
# A1.4 in real terms with a positive, fully diffusive discount factor

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1.4, pp. 564–565
(`B_t/P_t = E_t∫_t^∞ (Λ_τ/Λ_t)s_τ dτ`, (1.26) `i_t dt = −E_t[d(Λ_t/P_t)]/(Λ_t/P_t)`), and
Chapter 3, §3.6, (3.29)–(3.32), pp. 70–74. The non-vacuity instance of
`TidyR8ShortDebtRealForm.shortDebt_realForm_integral` given there
(`TidyR8ShortDebtRealForm.cosEconomy_realForm`) has a random but `𝓕_s`-measurable level
`Λ_s = 2 + cos W_s` and **no diffusion after `s`** (`Λ_u = Λ_se^{−r(u−s)}`, constant rate). This
module gives an instance with a **positive diffusive** discount factor on the whole horizon.

## The economy (on `bmPath`, `B` the Brownian motion read on `ℝ`; `r > 0`, any `b`)

* `P = 1`, nominal discount factor `n = Λ = e^{−ru}(2 + sin B) ∈ (0, 3e^{−ru}]`
  (`TidyR9PositiveDiscount.rrV`, drift `e^{−ru}(−r(2 + sin B) − ½ sin B)`, diffusion
  `e^{−ru}cos B`);
* the nominal rate forced by (1.26), `i = r + sin B/(2(2 + sin B))` (random, adapted,
  `|i − r| ≤ ½`), so that the drift of `n` is `−i n`;
* debt `B = b` constant and surplus `s = i b` (the flow `B i dt = P s dt + dB`).

Then `realForm_positive`: the transversality condition `E_s[n_TB_T] → 0` in `L¹` and the real
form `B_s/P_s = b = E_s[∫_s^∞ (Λ_u/Λ_s) s_u du]` hold, for every `s ≥ 0`.
-/

namespace Cochrane.Generality.TidyR9PositiveRealForm

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Generality.TidyR7StieltjesSums Cochrane.Generality.TidyR7BrownianTools
  Cochrane.Generality.TidyR7BrownianQV Cochrane.Generality.TidyR7ItoL2
  Cochrane.Generality.TidyR7ItoSums Cochrane.Generality.TidyR7ItoIntegral
  Cochrane.Generality.TidyR7ItoUnbounded Cochrane.Generality.TidyR7ItoProducts
  Cochrane.Generality.TidyR7ItoProcess Cochrane.Generality.TidyR7ItoProductRule
  Cochrane.Generality.TidyR7ItoBondStep Cochrane.Generality.TidyR7BrownianExist
  Cochrane.Generality.TidyR7BrownianSchauder Cochrane.Generality.TidyR7ItoDiscountFactor
  Cochrane.Generality.TidyR7ItoDiscountFactorCex Cochrane.Generality.TidyR9ItoFormula
  Cochrane.Generality.TidyR9ItoFormulaVariants Cochrane.Generality.TidyR9PositiveDiscount
  Cochrane.Generality.TidyR8ShortDebtRealForm
open scoped ENNReal NNReal

/-- Cochrane (2023), A1.4, (1.26), p. 564 (positive diffusive example): the nominal rate
`i = r + sin B/(2(2 + sin B))` forced by `E_t[dn] = −i n dt` for `n = e^{−ru}(2 + sin B)`. -/
noncomputable abbrev prI (r : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun u ω =>
  r + Real.sin (bmReal bmPath u ω) / (2 * (2 + Real.sin (bmReal bmPath u ω)))

/-- Cochrane (2023), A1.4, p. 564 (positive diffusive example): the real surplus `s = i b`
(constant debt `b`, `P = 1`). -/
noncomputable abbrev prSp (r b : ℝ) : ℝ → (ℕ → ℝ) → ℝ := fun u ω => prI r u ω * b

/-- Cochrane (2023), A1.4, (1.26), p. 564: `|i − r| ≤ ½` in the example. -/
theorem prI_bound (r u : ℝ) (ω : ℕ → ℝ) : |prI r u ω - r| ≤ 1 / 2 := by
  obtain ⟨h1, -⟩ := two_add_sin_bounds (bmReal bmPath u ω)
  have h3 := Real.abs_sin_le_one (bmReal bmPath u ω)
  have hpos : 0 < 2 * (2 + Real.sin (bmReal bmPath u ω)) := by linarith
  simp only [prI, add_sub_cancel_left]
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  linarith

/-- Cochrane (2023), A1.4, (1.26), p. 564: in the example the discounted surplus is
`n s = b e^{−ru}(r(2 + sin B) + ½ sin B)` (minus `b` times the drift of `n`). -/
theorem pr_lamSp_eq (r b u : ℝ) (ω : ℕ → ℝ) :
    rrV r u ω * prSp r b u ω = b * (Real.exp (-(r * u)) * (r * (2 + Real.sin (bmReal bmPath u ω))
      + Real.sin (bmReal bmPath u ω) / 2)) := by
  have h0 : 2 + Real.sin (bmReal bmPath u ω) ≠ 0 := by
    have := (two_add_sin_bounds (bmReal bmPath u ω)).1
    linarith
  simp only [rrV, prSp, prI]
  field_simp

/-- Cochrane (2023), A1.4, p. 564: `|n s| ≤ |b|(3r + 1)e^{−ru}` in the example (`r ≥ 0`). -/
theorem pr_abs_lamSp_le {r : ℝ} (hr : 0 ≤ r) (b u : ℝ) (ω : ℕ → ℝ) :
    |rrV r u ω * prSp r b u ω| ≤ |b| * (3 * r + 1) * Real.exp (-(r * u)) := by
  rw [pr_lamSp_eq, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := Real.neg_one_le_sin (bmReal bmPath u ω)
  have h2 := Real.sin_le_one (bmReal bmPath u ω)
  have hk : |r * (2 + Real.sin (bmReal bmPath u ω)) + Real.sin (bmReal bmPath u ω) / 2|
      ≤ 3 * r + 1 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have he := (Real.exp_pos (-(r * u))).le
  calc |b| * (Real.exp (-(r * u)) * |r * (2 + Real.sin (bmReal bmPath u ω))
        + Real.sin (bmReal bmPath u ω) / 2|)
      ≤ |b| * (Real.exp (-(r * u)) * (3 * r + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk he) (abs_nonneg _)
    _ = |b| * (3 * r + 1) * Real.exp (-(r * u)) := by ring

/-- Cochrane (2023), A1.4, p. 564: `x ↦ e^{−ru}(2 + sin x)((r + sin x/(2(2 + sin x)))b)`, the
discounted surplus as a function of the Brownian state, is continuous. -/
theorem pr_cont_state (r b u : ℝ) : Continuous fun x : ℝ =>
    Real.exp (-(r * u)) * (2 + Real.sin x) * ((r + Real.sin x / (2 * (2 + Real.sin x))) * b) :=
  (continuous_const.mul (continuous_const.add Real.continuous_sin)).mul
    ((continuous_const.add (Real.continuous_sin.div (continuous_const.mul
      (continuous_const.add Real.continuous_sin)) fun x => by
        have := (two_add_sin_bounds x).1
        exact (by linarith : (0 : ℝ) < 2 * (2 + Real.sin x)).ne')).mul continuous_const)

/-- Cochrane (2023), A1.4, p. 564: on every path, `u ↦ n_u s_u` is continuous. -/
theorem pr_cont_path (r b : ℝ) (ω : ℕ → ℝ) : Continuous fun u => rrV r u ω * prSp r b u ω := by
  have hB := continuous_bmReal_bmPath ω
  have hd : ∀ u, 2 * (2 + Real.sin (bmReal bmPath u ω)) ≠ 0 := fun u => by
    have := (two_add_sin_bounds (bmReal bmPath u ω)).1
    exact (by linarith : (0 : ℝ) < 2 * (2 + Real.sin (bmReal bmPath u ω))).ne'
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
    (continuous_const.add (Real.continuous_sin.comp hB))).mul ((continuous_const.add
      ((Real.continuous_sin.comp hB).div (continuous_const.mul
        (continuous_const.add (Real.continuous_sin.comp hB))) hd)).mul continuous_const)

/-- Cochrane (2023), A1.4, p. 564: `(u, ω) ↦ n_u(ω)s_u(ω)` is jointly measurable (continuous in
`u`, measurable in `ω`; Mathlib `measurable_uncurry_of_continuous_of_measurable`). -/
theorem pr_measurable_uncurry (r b : ℝ) :
    Measurable (Function.uncurry fun u ω => rrV r u ω * prSp r b u ω) :=
  measurable_uncurry_of_continuous_of_measurable (pr_cont_path r b)
    fun u => (pr_cont_state r b u).measurable.comp (measurable_bmPath _)

/-- Cochrane (2023), A1.4, p. 564: on every path, `u ↦ n_u s_u` is integrable on `(T, ∞)`
(`r > 0`). -/
theorem pr_integrableOn {r : ℝ} (hr : 0 < r) (b T : ℝ) (ω : ℕ → ℝ) :
    IntegrableOn (fun u => rrV r u ω * prSp r b u ω) (Set.Ioi T) := by
  refine Integrable.mono' (((exp_neg_integrableOn_Ioi T hr).const_mul (|b| * (3 * r + 1))))
    (pr_cont_path r b ω).aestronglyMeasurable (ae_of_all _ fun u => ?_)
  rw [Real.norm_eq_abs, neg_mul]
  exact pr_abs_lamSp_le hr.le b u ω

/-- Cochrane (2023), A1.4, p. 564: `|∫_T^∞ n s| ≤ |b|(3r + 1)e^{−rT}/r` on every path
(`r > 0`). -/
theorem pr_abs_integral_Ioi_le {r : ℝ} (hr : 0 < r) (b T : ℝ) (ω : ℕ → ℝ) :
    |∫ u in Set.Ioi T, rrV r u ω * prSp r b u ω| ≤
      |b| * (3 * r + 1) * (Real.exp (-(r * T)) / r) := by
  have hi : IntegrableOn (fun u => |b| * (3 * r + 1) * Real.exp (-r * u)) (Set.Ioi T) :=
    (exp_neg_integrableOn_Ioi T hr).const_mul _
  have h := norm_integral_le_of_norm_le hi (ae_of_all _ fun u => by
    rw [Real.norm_eq_abs, neg_mul]
    exact pr_abs_lamSp_le hr.le b u ω)
  rw [Real.norm_eq_abs, integral_const_mul, integral_exp_mul_Ioi (by linarith) T] at h
  calc _ ≤ _ := h
    _ = |b| * (3 * r + 1) * (Real.exp (-(r * T)) / r) := by
      rw [neg_mul, neg_div_neg_eq]

/-- Cochrane (2023), A1.4, p. 564: `ω ↦ ∫_T^∞ n_u(ω)s_u(ω) du` is measurable. -/
theorem pr_measurable_integral (r b T : ℝ) :
    Measurable fun ω => ∫ u in Set.Ioi T, rrV r u ω * prSp r b u ω :=
  ((pr_measurable_uncurry r b).stronglyMeasurable.integral_prod_left
    (μ := volume.restrict (Set.Ioi T))).measurable

/-- **Cochrane (2023), A1.4, pp. 564–565: the real form `B_t/P_t = E_t∫_t^∞ (Λ_τ/Λ_t)s_τ dτ` with
a POSITIVE, fully diffusive discount factor.** On the constructed Brownian motion, for `r > 0`,
any debt level `b` and `0 ≤ s`: `P = 1`, `n = Λ = e^{−ru}(2 + sin B)` (diffusion
`e^{−ru}cos B ≠ 0`), the rate `i = r + sin B/(2(2 + sin B))` of (1.26), `B = b`, `s = ib`
satisfy every hypothesis of `TidyR8ShortDebtRealForm.shortDebt_realForm_integral`; the
transversality condition `E_s[n_TB_T] → 0` holds in `L¹`, and so
`B_s/P_s = b = E_s[∫_s^∞ (Λ_u/Λ_s)s_u du]` a.s. -/
theorem realForm_positive {r : ℝ} (hr : 0 < r) (b : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun T => ∫ ω, |gaussSeq[fun ω => rrV r T ω * (fun _ _ => b) T ω | bmF s] ω|
      ∂gaussSeq) atTop (𝓝 0) ∧
    (fun ω => (fun (_ : ℝ) (_ : ℕ → ℝ) => b) s ω / (fun (_ : ℝ) (_ : ℕ → ℝ) => (1 : ℝ)) s ω)
      =ᵐ[gaussSeq] gaussSeq[fun ω => ∫ u in Set.Ioi s, rrV r u ω * (fun _ _ => (1 : ℝ)) u ω /
        (rrV r s ω * (fun _ _ => (1 : ℝ)) s ω) * prSp r b u ω | bmF s] := by
  have := isProb
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  set K : ℝ := |b| * (3 * r + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hn : ∀ T, s < T → ItoProcess gaussSeq bmF bmPath (rrV r)
      (fun u ω => -(prI r u ω * rrV r u ω)) (rrσV r) s T
      ((fun _ => r * (|2| + |1|) + |1| * 0 + |1| / 2 * (1 * 1)) T) ((fun _ => |1| * 1) T) :=
    fun T hT => itoProcess_of_coeff_eq (rr_val_ito hr.le hs hT.le) (fun u ω => by
      have h0 : 2 + Real.sin (bmReal bmPath u ω) ≠ 0 := by
        have := (two_add_sin_bounds (bmReal bmPath u ω)).1
        linarith
      simp only [rraV, prI, rrV]
      field_simp
      ring) fun _ _ => rfl
  have hB : ∀ T, s < T → ItoProcess gaussSeq bmF bmPath (fun _ _ => b)
      (fun u ω => prI r u ω * (fun _ _ => b) u ω - (fun _ _ => (1 : ℝ)) u ω * prSp r b u ω)
      (fun _ _ => 0) s T ((fun _ => (0 : ℝ)) T) 0 := fun T _ =>
    itoProcess_of_coeff_eq (itoProcess_det hBM measurable_bmPath h𝓕 hs (f := fun _ => b)
      (g := fun _ => 0) (Cg := 0) continuousOn_const (fun _ _ => by simp) (fun _ _ => by simp))
      (fun u ω => by simp only [prSp]; ring) fun _ _ => rfl
  -- the transversality condition
  have htvc : Tendsto (fun T => ∫ ω, |gaussSeq[fun ω => rrV r T ω * (fun _ _ => b) T ω
      | bmF s] ω| ∂gaussSeq) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T => 3 * |b| * Real.exp (-(r * T))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hr)).const_mul (3 * |b|)
      rwa [mul_zero] at this
    refine squeeze_zero (fun T => integral_nonneg fun ω => abs_nonneg _) (fun T => ?_) hlim
    refine (integral_abs_condExp_le _).trans ?_
    calc ∫ ω, |rrV r T ω * (fun _ _ => b) T ω| ∂gaussSeq
        ≤ ∫ _, 3 * |b| * Real.exp (-(r * T)) ∂gaussSeq :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _) (integrable_const _)
            (ae_of_all _ fun ω => by
              obtain ⟨-, h2⟩ := two_add_sin_bounds (bmReal bmPath T ω)
              have h1 := (two_add_sin_bounds (bmReal bmPath T ω)).1
              simp only [rrV]
              rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (by linarith)]
              have he := (Real.exp_pos (-(r * T))).le
              have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 he) (abs_nonneg b)
              linarith)
      _ = 3 * |b| * Real.exp (-(r * T)) := by simp
  refine ⟨htvc, ?_⟩
  -- the hypotheses of `shortDebt_realForm_integral`
  have hΛ : ∀ᵐ ω ∂gaussSeq, rrV r s ω * (fun _ _ => (1 : ℝ)) s ω ≠ 0 :=
    ae_of_all _ fun ω => by
      have := (two_add_sin_bounds (bmReal bmPath s ω)).1
      simp only [rrV, mul_one]
      exact (mul_pos (Real.exp_pos _) (by linarith)).ne'
  have eG : ∀ ω, (∫ u in Set.Ioi s, rrV r u ω * (fun _ _ => (1 : ℝ)) u ω * prSp r b u ω) =
      ∫ u in Set.Ioi s, rrV r u ω * prSp r b u ω := fun ω => by simp only [mul_one]
  have hGb : ∀ ω, |∫ u in Set.Ioi s, rrV r u ω * prSp r b u ω| ≤ K * (Real.exp (-(r * s)) / r) :=
    fun ω => pr_abs_integral_Ioi_le hr b s ω
  have hG : Integrable (fun ω => ∫ u in Set.Ioi s, rrV r u ω * (fun _ _ => (1 : ℝ)) u ω *
      prSp r b u ω) gaussSeq := by
    simp_rw [eG]
    exact Integrable.mono' (integrable_const (K * (Real.exp (-(r * s)) / r)))
      (pr_measurable_integral r b s).aestronglyMeasurable (ae_of_all _ fun ω => hGb ω)
  have hGΛ : Integrable (fun ω => ∫ u in Set.Ioi s, rrV r u ω * (fun _ _ => (1 : ℝ)) u ω /
      (rrV r s ω * (fun _ _ => (1 : ℝ)) s ω) * prSp r b u ω) gaussSeq := by
    have e : ∀ ω, (∫ u in Set.Ioi s, rrV r u ω * (fun _ _ => (1 : ℝ)) u ω /
        (rrV r s ω * (fun _ _ => (1 : ℝ)) s ω) * prSp r b u ω) =
        (∫ u in Set.Ioi s, rrV r u ω * prSp r b u ω) / rrV r s ω := fun ω => by
      rw [← integral_div]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp only [mul_one]
      ring
    simp_rw [e]
    have hns : Measurable (rrV r s) :=
      (continuous_const.mul (continuous_const.add Real.continuous_sin)).measurable.comp
        (measurable_bmPath _)
    refine Integrable.mono' (integrable_const (K / r))
      ((pr_measurable_integral r b s).div hns).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have h1 := (two_add_sin_bounds (bmReal bmPath s ω)).1
    have hlow : Real.exp (-(r * s)) ≤ rrV r s ω := by
      simp only [rrV]
      nlinarith [Real.exp_pos (-(r * s))]
    have hpos : 0 < Real.exp (-(r * s)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos.trans_le hlow), div_le_iff₀
      (hpos.trans_le hlow)]
    calc |∫ u in Set.Ioi s, rrV r u ω * prSp r b u ω| ≤ K * (Real.exp (-(r * s)) / r) := hGb ω
      _ = K / r * Real.exp (-(r * s)) := by ring
      _ ≤ K / r * rrV r s ω := mul_le_mul_of_nonneg_left hlow (by positivity)
  have hm : ∀ T, s < T → ItoDiscountModel gaussSeq bmF bmPath (rrV r) (fun _ _ => b)
      (fun u ω => -(prI r u ω * rrV r u ω)) (rrσV r)
      (fun u ω => prI r u ω * (fun _ _ => b) u ω - (fun _ _ => (1 : ℝ)) u ω * prSp r b u ω)
      (fun _ _ => 0) (fun u ω => (fun _ _ => (1 : ℝ)) u ω * prSp r b u ω) s T
      ((fun _ => r * (|2| + |1|) + |1| * 0 + |1| / 2 * (1 * 1)) T) ((fun _ => |1| * 1) T)
      ((fun _ => (0 : ℝ)) T) 0 := fun T hT => shortDebt_model (hn T hT) (hB T hT)
  have hconv : Tendsto (fun T => ∫ ω, |dtInt gaussSeq bmF (fun u ω => rrV r u ω *
      ((fun _ _ => (1 : ℝ)) u ω * prSp r b u ω)) s T ω
      - ∫ u in Set.Ioi s, rrV r u ω * (fun _ _ => (1 : ℝ)) u ω * prSp r b u ω| ∂gaussSeq)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun T => K * (Real.exp (-(r * T)) / r)) atTop (𝓝 0) := by
      have := ((Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hr)).div_const r).const_mul K
      rwa [zero_div, mul_zero] at this
    refine squeeze_zero' (Eventually.of_forall fun T => integral_nonneg fun ω => abs_nonneg _)
      ?_ hlim
    filter_upwards [eventually_gt_atTop s] with T hT
    have hd := dtInt_ae_eq_integral hT.le ((hm T hT).msIntegrand_lamSp hBM measurable_bmPath
      h𝓕 hs) (ae_of_all _ fun ω => by
        simp only [one_mul]
        exact (pr_cont_path r b ω).continuousOn)
    have hb : ∀ᵐ ω ∂gaussSeq, |dtInt gaussSeq bmF (fun u ω => rrV r u ω *
        ((fun _ _ => (1 : ℝ)) u ω * prSp r b u ω)) s T ω
        - ∫ u in Set.Ioi s, rrV r u ω * (fun _ _ => (1 : ℝ)) u ω * prSp r b u ω|
        ≤ K * (Real.exp (-(r * T)) / r) := by
      filter_upwards [hd] with ω hω
      rw [hω, eG]
      simp only [one_mul]
      rw [← Set.Ioc_union_Ioi_eq_Ioi hT.le, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl)
        measurableSet_Ioi ((pr_integrableOn hr b s ω).mono_set Set.Ioc_subset_Ioi_self)
        (pr_integrableOn hr b T ω), intervalIntegral.integral_of_le hT.le, sub_add_cancel_left,
        abs_neg]
      exact pr_abs_integral_Ioi_le hr b T ω
    calc ∫ ω, |dtInt gaussSeq bmF (fun u ω => rrV r u ω *
          ((fun _ _ => (1 : ℝ)) u ω * prSp r b u ω)) s T ω
          - ∫ u in Set.Ioi s, rrV r u ω * (fun _ _ => (1 : ℝ)) u ω * prSp r b u ω| ∂gaussSeq
        ≤ ∫ _, K * (Real.exp (-(r * T)) / r) ∂gaussSeq :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _) (integrable_const _) hb
      _ = K * (Real.exp (-(r * T)) / r) := by simp
  exact (shortDebt_realForm_integral hn hB hBM measurable_bmPath h𝓕 hs stronglyMeasurable_const
    hΛ hG hGΛ hconv).2 htvc

end Cochrane.Generality.TidyR9PositiveRealForm
