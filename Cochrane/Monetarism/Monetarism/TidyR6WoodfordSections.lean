/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.MoneyTargetingDynamics
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.IntermediateValue

/-!
# Woodford's Taylor-rule transversality, Obstfeld–Rogoff and convexity sections

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3.2, pp. 441–445 and
Online Appendix §3.2.2, pp. 621–625, where Cochrane discusses Woodford's (2003) treatment of
monetary targeting and of Obstfeld and Rogoff's argument. `MoneyTargetingDynamics` restated
Woodford's (2003) §4.1–4.2 but left out three sections; they are restated here from the
Woodford Chapter 2 project (MoneyTargetingDynamics and GlobalDynamics modules, Woodford (2003),
Chapter 2, §4, pp. 123–138), adapted to this namespace, and linked to `MoneyTargetingDynamics`.
Perfect foresight throughout.

## Restated from the Woodford Chapter 2 project

* **Convexity, error E7 (Woodford (2003), p. 130).** `vpE7`, `e7_convexity_fails`: with
  `v'(m) = e^{−m}`, `c = 1`, the function `MoneyTargetingDynamics.sepF` is positive, strictly
  increasing, tends to `0` at `0⁺`, but is not convex. It is stated with the `sepF` of
  `MoneyTargetingDynamics`, so it is literally about the map of Figure 2.5 used there.
* **Taylor-rule transversality (Woodford (2003), pp. 132–133, error E4).** The map (4.6)
  `map46`, `map46_step_down`; the path notion (4.5) `IsPath45`, `ratio_strictMonoOn`,
  `steady_state45_iff`, `step45_down`, `self_fulfilling_deflation45`; the transversality term
  `tvcValue`, `tvcValue_succ`, `taylor_tvc_violated_of_eventually_le`,
  `e4_printed_inequality_false`, `e4_corrected_inequality`, `deflation_tvc_violated`,
  `zero_bound_inflation_eq_beta`, `zero_bound_tvc_violated`, `fig24_deflations_violate_tvc`,
  `target_tvc_iff`.
* **Obstfeld–Rogoff, (4.10) (Woodford (2003), p. 136).** `sep_F_neg_of_or_condition`,
  `IsORMapPath`, `or_path_above_mlow`, `or_no_path_below`, `or_bounds_exist`,
  `or_iteration_bound`, `or_paths_above_mstar`.

## Links to `MoneyTargetingDynamics`

* `e7_miuPath_iff`: for the E7 utility, Cochrane's (19.18) path with constant money growth is
  the separable path of `MoneyTargetingDynamics` (via `MoneyTargetingDynamics.miuPath_iff_sepPath`),
  so the failure of convexity concerns exactly Cochrane's model.
* `tvcValue_const_lam`: with a constant marginal utility `λ ≡ c` and `D = M` (money), the
  Taylor-rule transversality term is the money transversality term `β^T U_c m_T` of
  `MoneyTargetingDynamics.money_tvc_violated`.
* `target_tvc_money_growth`: at the money-targeting steady state `Π* = μ̄` (constant real
  balances) the target path satisfies the transversality condition iff `β < 1`.
* `isORMapPath_sep_iff`, `or_sep_no_path_below`, `or_miu_no_path_below`: the Obstfeld–Rogoff
  path for `F = sepF c v'` is `MoneyTargetingDynamics.IsSepPath`, and under (4.10) no path of
  Cochrane's (19.18) with constant money growth ever has real balances below the steady state.
-/

namespace Cochrane.Monetarism.TidyR6WoodfordSections

open Filter Topology
open Cochrane.Monetarism.MoneyTargetingDynamics

/-! ## Error E7: `F` need not be convex -/

/-- Cochrane (2023), §19.3.2, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, error E7: the counterexample `v'(m) = e^{−m}` (`u = log c + v(m)`,
`ȳ = 1`). -/
noncomputable def vpE7 (m : ℝ) : ℝ := Real.exp (-m)

/-- Cochrane (2023), §19.3.2, pp. 442–445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 130, error E7: "`F(m)` is positive, increasing, and convex" — convexity is
false. For `c = 1`, `v'(m) = e^{−m}` all the hypotheses of Figure 2.5 hold (`v'` continuous,
strictly decreasing, `0 < v' < c`), so `F` is positive, strictly increasing and tends to `0` at
`0⁺`, yet `F` is not convex on `(0, ∞)`: `F(3) > (F(2) + F(4))/2`.
Renamed copy of MoneyTargetingDynamics.e7_counterexample in the Woodford Chapter 2 project. -/
theorem e7_convexity_fails :
    ContinuousOn vpE7 (Set.Ioi 0) ∧ StrictAntiOn vpE7 (Set.Ioi 0) ∧
      (∀ m, 0 < m → 0 < vpE7 m ∧ vpE7 m < 1) ∧
      (∀ m, 0 < m → 0 < sepF 1 vpE7 m) ∧ StrictMonoOn (sepF 1 vpE7) (Set.Ioi 0) ∧
      Tendsto (sepF 1 vpE7) (𝓝[>] 0) (𝓝 0) ∧
      (sepF 1 vpE7 2 + sepF 1 vpE7 4) / 2 < sepF 1 vpE7 3 ∧
      ¬ ConvexOn ℝ (Set.Ioi 0) (sepF 1 vpE7) := by
  have hsa : StrictAntiOn vpE7 (Set.Ioi 0) := fun a _ b _ hab => by
    unfold vpE7; exact Real.exp_lt_exp.mpr (by linarith)
  have hbd : ∀ m, 0 < m → 0 < vpE7 m ∧ vpE7 m < 1 := fun m hm => by
    unfold vpE7
    exact ⟨Real.exp_pos _, by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)⟩
  have hgap : ∀ m, 0 < m → vpE7 m < 1 := fun m hm => (hbd m hm).2
  have hmid : (sepF 1 vpE7 2 + sepF 1 vpE7 4) / 2 < sepF 1 vpE7 3 := by
    unfold sepF vpE7
    have he : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0); linarith
    have e2 : Real.exp (-2) = Real.exp (-4) * Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have e3 : Real.exp (-3) = Real.exp (-4) * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [e2, e3]
    have h4 := Real.exp_pos (-4)
    nlinarith [mul_pos h4 (mul_pos (by linarith : (0 : ℝ) < Real.exp 1 - 1)
      (by linarith : (0 : ℝ) < Real.exp 1 - 2))]
  refine ⟨fun m _ => (Real.continuous_exp.comp continuous_neg).continuousAt.continuousWithinAt,
    hsa, hbd, fun m hm => sepF_pos (by linarith [hgap m hm]) hm,
    sepF_strictMonoOn hsa.antitoneOn hgap, sepF_tendsto_zero hsa.antitoneOn hgap, hmid, ?_⟩
  intro hconv
  have := hconv.2 (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 4)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  norm_num at this
  linarith

/-- Cochrane (2023), eq. (19.18), p. 442, linked to Woodford (2003), p. 130, error E7: with the
E7 utility (`u_c(y) = 1`, `u_m = e^{−m}`) and money growth `M_{t+1} = (1 + µ)M_t`, a path of
Cochrane's (19.18) is exactly a path of the separable map whose `F` is not convex
(`e7_convexity_fails`); so convexity also fails in Cochrane's model and is not used by
`MoneyTargetingDynamics`. -/
theorem e7_miuPath_iff {β μg : ℝ} {M m : ℕ → ℝ} (hβ : 0 < β) (hM : ∀ t, 0 < M t)
    (hg : ∀ t, M (t + 1) = μg * M t) :
    MoneyInUtility.IsMIUPath β 1 vpE7 M m ↔ IsSepPath β μg 1 vpE7 m :=
  miuPath_iff_sepPath hβ one_pos hM hg

/-! ## The Taylor-rule version: nominal liabilities growing at `μ̄` -/

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), eq. (4.6), p. 125: the map `Π ↦ β(1 + φ(Π))` (the solid curve of
Figure 2.4). -/
def map46 (β : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ := fun x => β * (1 + φ x)

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 126: under `φ(β) = 0` and `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, the map (4.6)
sends `[β, Π*)` into itself, weakly downward. -/
theorem map46_step_down {β Pis x : ℝ} {φ : ℝ → ℝ} (hβ : 0 < β)
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hx : β ≤ x) (hxP : x < Pis) :
    β ≤ map46 β φ x ∧ map46 β φ x ≤ x := by
  simp only [map46]
  refine ⟨by nlinarith [hφ0 x (by linarith)], ?_⟩
  rcases hx.lt_or_eq with hlt | heq
  · have h := hbelow x hlt hxP
    have : β * φ x < β * (x / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ x hβ.ne'] at this
    linarith
  · rw [← heq, hφβ]; simp

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), eq. (4.5), p. 125: a perfect-foresight inflation path under the rule
`i_t = φ(Π_t)`: positive inflation with
`Π_{t+1}/λ(φ(Π_{t+1})) = β(1 + φ(Π_t))/λ(φ(Π_t))` at all dates. -/
def IsPath45 (β : ℝ) (lam φ : ℝ → ℝ) (Pi_ : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Pi_ t) ∧
    ∀ t, Pi_ (t + 1) / lam (φ (Pi_ (t + 1))) = β * (1 + φ (Pi_ t)) / lam (φ (Pi_ t))

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 127: if `λ > 0` is nonincreasing on `[0, ∞)` and `φ ≥ 0` is
nondecreasing, then `Π ↦ Π/λ(φ(Π))` is strictly increasing on `(0, ∞)`. -/
theorem ratio_strictMonoOn {lam φ : ℝ → ℝ} (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hmono : MonotoneOn φ (Set.Ioi 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) :
    StrictMonoOn (fun x => x / lam (φ x)) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hφab : φ a ≤ φ b := hmono ha hb hab.le
  have hl : lam (φ b) ≤ lam (φ a) :=
    hanti (Set.mem_Ici.mpr (hφ0 a ha')) (Set.mem_Ici.mpr (hφ0 b hb')) hφab
  have hla := hlam _ (hφ0 a ha')
  have hlb := hlam _ (hφ0 b hb')
  calc a / lam (φ a) < b / lam (φ a) := div_lt_div_of_pos_right hab hla
    _ ≤ b / lam (φ b) := div_le_div_of_nonneg_left hb'.le hlb hl

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (4.5), p. 127: the steady states of (4.5) are those of (4.6), since `λ`
cancels at a constant inflation rate. -/
theorem steady_state45_iff {β x : ℝ} {lam φ : ℝ → ℝ} (hl : 0 < lam (φ x)) :
    x / lam (φ x) = β * (1 + φ x) / lam (φ x) ↔ map46 β φ x = x := by
  rw [div_left_inj' hl.ne', map46, eq_comm]

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 127: under `λ > 0` nonincreasing, `φ(β) = 0` and `φ(Π) < β⁻¹Π − 1` on
`(β, Π*)`, the successor `Π'` of any `Π ∈ [β, Π*)` under (4.5) lies in `[β, Π]`. -/
theorem step45_down {β Pis x y : ℝ} {lam φ : ℝ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hanti : AntitoneOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hx : β ≤ x) (hxP : x < Pis)
    (hy : 0 < y) (heq : y / lam (φ y) = β * (1 + φ x) / lam (φ x)) : β ≤ y ∧ y ≤ x := by
  have hsm := ratio_strictMonoOn hlam hanti hmono hφ0
  have hx0 : 0 < x := by linarith
  have hφx := hφ0 x hx0
  have hlx := hlam _ hφx
  have hdown := map46_step_down hβ hφ0 hφβ hbelow hx hxP
  have hl0 : lam (φ x) ≤ lam 0 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hφx) hφx
  have hlam0 := hlam 0 le_rfl
  constructor
  · by_contra hcon
    push Not at hcon
    have h1 : y / lam (φ y) < β / lam (φ β) := hsm hy hβ hcon
    rw [hφβ, heq] at h1
    have h2 : β / lam 0 ≤ β / lam (φ x) := div_le_div_of_nonneg_left hβ.le hlx hl0
    have h3 : β / lam (φ x) ≤ β * (1 + φ x) / lam (φ x) :=
      div_le_div_of_nonneg_right (by nlinarith) hlx.le
    linarith
  · by_contra hcon
    push Not at hcon
    have h1 : x / lam (φ x) < y / lam (φ y) := hsm hx0 hy hcon
    rw [heq] at h1
    have h2 : β * (1 + φ x) / lam (φ x) ≤ x / lam (φ x) :=
      div_le_div_of_nonneg_right hdown.2 hlx.le
    linarith

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 127, the self-fulfilling deflations of Figure 2.4 under (4.5): if `λ > 0` is
continuous and nonincreasing on `[0, ∞)`, `φ ≥ 0` is continuous and nondecreasing, `φ(β) = 0`
and `φ(Π) < β⁻¹Π − 1` on `(β, Π*)`, every solution of (4.5) starting in `(β, Π*)` is
nonincreasing, stays in `[β, Π₀]` and converges to `β`. -/
theorem self_fulfilling_deflation45 {β Pis : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ} (hβ : 0 < β)
    (hlam : ∀ j, 0 ≤ j → 0 < lam j) (hanti : AntitoneOn lam (Set.Ici 0))
    (hlamc : ContinuousOn lam (Set.Ici 0)) (hmono : MonotoneOn φ (Set.Ioi 0))
    (hφ0 : ∀ x, 0 < x → 0 ≤ φ x) (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) :
    Antitone Pi_ ∧ (∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0) ∧ Tendsto Pi_ atTop (𝓝 β) := by
  have hstep : ∀ t, β ≤ Pi_ t ∧ Pi_ t ≤ Pi_ 0 ∧ Pi_ (t + 1) ≤ Pi_ t := by
    intro t
    induction t with
    | zero =>
      have := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow h0.1.le h0.2 (hpath.1 1)
        (hpath.2 0)
      exact ⟨h0.1.le, le_rfl, this.2⟩
    | succ n ih =>
      have h1 := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow ih.1
        (by linarith [h0.2, ih.2.1]) (hpath.1 (n + 1)) (hpath.2 n)
      have hle : Pi_ (n + 1) ≤ Pi_ 0 := le_trans ih.2.2 ih.2.1
      have h2 := step45_down hβ hlam hanti hmono hφ0 hφβ hbelow h1.1
        (by linarith [h0.2]) (hpath.1 (n + 1 + 1)) (hpath.2 (n + 1))
      exact ⟨h1.1, hle, h2.2⟩
  have hanti' : Antitone Pi_ := antitone_nat_of_succ_le fun t => (hstep t).2.2
  refine ⟨hanti', fun t => ⟨(hstep t).1, (hstep t).2.1⟩, ?_⟩
  have hbdd : BddBelow (Set.range Pi_) := ⟨β, by rintro _ ⟨t, rfl⟩; exact (hstep t).1⟩
  have hlim := tendsto_atTop_ciInf hanti' hbdd
  set L := ⨅ t, Pi_ t with hL
  have hLβ : β ≤ L := le_ciInf fun t => (hstep t).1
  have hLpos : 0 < L := by linarith
  have hlc : ContinuousOn (fun x => lam (φ x)) (Set.Ioi 0) :=
    hlamc.comp hcont fun x hx => Set.mem_Ici.mpr (hφ0 x hx)
  have hlcL : ContinuousAt (fun x => lam (φ x)) L := hlc.continuousAt (Ioi_mem_nhds hLpos)
  have hφcL : ContinuousAt φ L := hcont.continuousAt (Ioi_mem_nhds hLpos)
  have hlL := hlam _ (hφ0 L hLpos)
  have hhc : ContinuousAt (fun x => x / lam (φ x)) L := continuousAt_id.div hlcL hlL.ne'
  have hRc : ContinuousAt (fun x => β * (1 + φ x) / lam (φ x)) L :=
    (continuousAt_const.mul (continuousAt_const.add hφcL)).div hlcL hlL.ne'
  have hA : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (L / lam (φ L))) :=
    hhc.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have hB : Tendsto (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) atTop
      (𝓝 (β * (1 + φ L) / lam (φ L))) := by
    have : (fun t => Pi_ (t + 1) / lam (φ (Pi_ (t + 1)))) =
        (fun x => β * (1 + φ x) / lam (φ x)) ∘ Pi_ := funext fun t => hpath.2 t
    rw [this]
    exact hRc.tendsto.comp hlim
  have hfix : map46 β φ L = L := (steady_state45_iff hlL).mp (tendsto_nhds_unique hA hB)
  rcases hLβ.lt_or_eq with hlt | heq
  · exfalso
    have h := hbelow L hlt (by linarith [h0.2, ciInf_le hbdd 0])
    have : β * φ L < β * (L / β - 1) := mul_lt_mul_of_pos_left h hβ
    rw [mul_sub, mul_div_cancel₀ L hβ.ne'] at this
    simp only [map46] at hfix
    linarith
  · rw [← heq] at hlim; exact hlim

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), (1.24), p. 72, along a perfect-foresight path: the transversality term
`β^T λ(i_T) D_T/P_T` with `i_T = φ(Π_T)`. -/
noncomputable def tvcValue (β : ℝ) (lam φ : ℝ → ℝ) (Pi_ P D : ℕ → ℝ) (T : ℕ) : ℝ :=
  β ^ T * lam (φ (Pi_ T)) * D T / P T

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 133, displayed identity: when `P_{t+1} = Π_{t+1}P_t`, `D_{t+1} = μ̄D_t`
and (4.5) holds, `β^{T+1}λ_{T+1}D_{T+1}/P_{T+1} = β^Tλ_TD_T/P_T · μ̄/(1 + i_T)`. -/
theorem tvcValue_succ {β μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ} (hβ : 0 < β)
    (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ : ∀ t, 0 < 1 + φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t) (T : ℕ) :
    tvcValue β lam φ Pi_ P D (T + 1) = tvcValue β lam φ Pi_ P D T * (μ / (1 + φ (Pi_ T))) := by
  have h45 := hpath.2 T
  have hl1 := hlam (T + 1)
  have hl := hlam T
  have hPi := hpath.1 (T + 1)
  have hφT := hφ T
  have hPT := hP T
  have hlam1 : lam (φ (Pi_ (T + 1))) = Pi_ (T + 1) * lam (φ (Pi_ T)) / (β * (1 + φ (Pi_ T))) := by
    rw [div_eq_div_iff hl1.ne' hl.ne'] at h45
    rw [eq_div_iff (by positivity)]
    linarith
  unfold tvcValue
  rw [hlam1, hPrec, hD, pow_succ]
  field_simp

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), pp. 132–133 (error E4 corrected): if from some date on `1 + i_T ≤ μ̄`, the
transversality term is nondecreasing and positive from that date, so the transversality
condition (1.24) is violated. -/
theorem taylor_tvc_violated_of_eventually_le {β μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ : ∀ t, 0 < 1 + φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hev : ∃ t0, ∀ T, t0 ≤ T → 1 + φ (Pi_ T) ≤ μ) :
    ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  obtain ⟨t0, ht0⟩ := hev
  have hpos : ∀ T, 0 < tvcValue β lam φ Pi_ P D T := fun T => by
    unfold tvcValue; have := hlam T; have := hDpos T; have := hP T; positivity
  have hmono : ∀ n, tvcValue β lam φ Pi_ P D t0 ≤ tvcValue β lam φ Pi_ P D (t0 + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, tvcValue_succ hβ hpath hlam hφ hP hPrec hD]
      have h1 : 1 ≤ μ / (1 + φ (Pi_ (t0 + n))) :=
        (one_le_div (hφ _)).mpr (ht0 _ (Nat.le_add_right _ _))
      nlinarith [hpos (t0 + n)]
  intro h
  have hev : ∀ᶠ T in atTop, tvcValue β lam φ Pi_ P D t0 ≤ tvcValue β lam φ Pi_ P D T := by
    filter_upwards [eventually_ge_atTop t0] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hmono n
  have := ge_of_tendsto h hev
  linarith [hpos t0]

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 133, error E4: the printed claim "there must exist a date `t` such that
`1 + φ(Π_T) ≥ μ̄` for all `T ≥ t`" is false along any deflationary path converging to a point
`Π**` where `φ` is continuous with `1 + φ(Π**) < μ̄`. -/
theorem e4_printed_inequality_false {μ Pss : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss) (hμ : 1 + φ Pss < μ) :
    ¬ ∃ t, ∀ T, t ≤ T → μ ≤ 1 + φ (Pi_ T) := by
  rintro ⟨t, ht⟩
  have h1 : Tendsto (fun T => 1 + φ (Pi_ T)) atTop (𝓝 (1 + φ Pss)) :=
    tendsto_const_nhds.add (hcont.tendsto.comp hlim)
  have h2 : ∀ᶠ T in atTop, μ ≤ 1 + φ (Pi_ T) := by
    filter_upwards [eventually_ge_atTop t] with T hT using ht T hT
  have := ge_of_tendsto h1 h2
  linarith

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 133, error E4 corrected: under the same hypotheses there is a date after
which `1 + φ(Π_T) ≤ μ̄`. -/
theorem e4_corrected_inequality {μ Pss : ℝ} {φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss) (hμ : 1 + φ Pss < μ) :
    ∃ t, ∀ T, t ≤ T → 1 + φ (Pi_ T) ≤ μ := by
  have h1 : Tendsto (fun T => 1 + φ (Pi_ T)) atTop (𝓝 (1 + φ Pss)) :=
    tendsto_const_nhds.add (hcont.tendsto.comp hlim)
  obtain ⟨t, ht⟩ := eventually_atTop.mp (h1.eventually (gt_mem_nhds hμ))
  exact ⟨t, fun T hT => (ht T hT).le⟩

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 133, "the same argument works as long as `μ̄ > β⁻¹Π**`": a path of (4.5)
converging to a steady state `Π**` (`1 + φ(Π**) = β⁻¹Π**`) with `φ` continuous there and
`μ̄ > β⁻¹Π**` violates the transversality condition. -/
theorem deflation_tvc_violated {β μ Pss : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ} (hβ : 0 < β)
    (hpath : IsPath45 β lam φ Pi_) (hlam : ∀ t, 0 < lam (φ (Pi_ t)))
    (hφ0 : ∀ t, 0 ≤ φ (Pi_ t)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hlim : Tendsto Pi_ atTop (𝓝 Pss)) (hcont : ContinuousAt φ Pss)
    (hss : 1 + φ Pss = Pss / β) (hμ : Pss / β < μ) :
    ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) :=
  taylor_tvc_violated_of_eventually_le hβ hpath hlam (fun t => by linarith [hφ0 t]) hP hPrec hD
    hDpos (e4_corrected_inequality hlim hcont (by rw [hss]; exact hμ))

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 132: if `φ(Π) = 0` for all `Π ≤ Π̲`, a path of (4.5) that is eventually
below `Π̲` has `i_T = 0` and then `Π_{T+1} = β` from that date on. -/
theorem zero_bound_inflation_eq_beta {β Plow : ℝ} {lam φ : ℝ → ℝ} {Pi_ : ℕ → ℝ}
    (hpath : IsPath45 β lam φ Pi_) (hlam0 : 0 < lam 0) (hzero : ∀ x, x ≤ Plow → φ x = 0)
    {t : ℕ} (ht : ∀ T, t ≤ T → Pi_ T ≤ Plow) : ∀ T, t ≤ T → φ (Pi_ T) = 0 ∧ Pi_ (T + 1) = β := by
  intro T hT
  have h1 := hzero _ (ht T hT)
  have h2 := hzero _ (ht (T + 1) (by omega))
  have h45 := hpath.2 T
  rw [h1, h2, add_zero, mul_one] at h45
  exact ⟨h1, by rwa [div_left_inj' hlam0.ne'] at h45⟩

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 132: with `φ = 0` on `(−∞, Π̲]`, `Π̲ > β`, `D` growing at `μ̄ ≥ 1`, a path of
(4.5) converging to `β` eventually has `i = 0` and `Π = β`, and violates (1.24). -/
theorem zero_bound_tvc_violated {β μ Plow : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hPlow : β < Plow) (hμ : 1 ≤ μ) (hpath : IsPath45 β lam φ Pi_)
    (hlam : ∀ t, 0 < lam (φ (Pi_ t))) (hlam0 : 0 < lam 0) (hφ0 : ∀ t, 0 ≤ φ (Pi_ t))
    (hzero : ∀ x, x ≤ Plow → φ x = 0) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) (hlim : Tendsto Pi_ atTop (𝓝 β)) :
    (∃ t, ∀ T, t ≤ T → φ (Pi_ T) = 0 ∧ Pi_ (T + 1) = β) ∧
      ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  obtain ⟨t, ht⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hPlow))
  have hz := zero_bound_inflation_eq_beta hpath hlam0 hzero (fun T hT => (ht T hT).le)
  refine ⟨⟨t, hz⟩, taylor_tvc_violated_of_eventually_le hβ hpath hlam
    (fun s => by linarith [hφ0 s]) hP hPrec hD hDpos ⟨t, fun T hT => ?_⟩⟩
  rw [(hz T hT).1]; linarith

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), p. 133: as long as `φ(Π) < (Π − β)/β` on `(β, Π*)`, self-fulfilling
deflations are excluded under any fiscal policy giving liabilities growth `μ̄ > 1`: every
solution of (4.5) starting in `(β, Π*)` violates the transversality condition (1.24). -/
theorem fig24_deflations_violate_tvc {β Pis μ : ℝ} {lam φ : ℝ → ℝ} {Pi_ P D : ℕ → ℝ}
    (hβ : 0 < β) (hμ : 1 < μ) (hlam : ∀ j, 0 ≤ j → 0 < lam j)
    (hanti : AntitoneOn lam (Set.Ici 0)) (hlamc : ContinuousOn lam (Set.Ici 0))
    (hmono : MonotoneOn φ (Set.Ioi 0)) (hφ0 : ∀ x, 0 < x → 0 ≤ φ x)
    (hcont : ContinuousOn φ (Set.Ioi 0)) (hφβ : φ β = 0)
    (hbelow : ∀ x, β < x → x < Pis → φ x < x / β - 1) (hpath : IsPath45 β lam φ Pi_)
    (h0 : Pi_ 0 ∈ Set.Ioo β Pis) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) : ¬ Tendsto (tvcValue β lam φ Pi_ P D) atTop (𝓝 0) := by
  have hlim := (self_fulfilling_deflation45 hβ hlam hanti hlamc hmono hφ0 hcont hφβ hbelow
    hpath h0).2.2
  exact deflation_tvc_violated hβ hpath (fun t => hlam _ (hφ0 _ (hpath.1 t)))
    (fun t => hφ0 _ (hpath.1 t)) hP hPrec hD hDpos hlim
    (hcont.continuousAt (Ioi_mem_nhds hβ)) (by rw [hφβ, div_self hβ.ne']; ring)
    (by rw [div_self hβ.ne']; exact hμ)

/-- Cochrane (2023), §19.3.2, p. 445 (restated from the Woodford Chapter 2 project).
Woodford (2003), pp. 132–133: along the target path `Π_t ≡ Π*` (with `1 + φ(Π*) = Π*/β`) the
transversality term is `(βμ̄/Π*)^T` times its initial value, so the target equilibrium satisfies
(1.24) iff `βμ̄ < Π*` (given `μ̄ > 0`). -/
theorem target_tvc_iff {β μ Pis : ℝ} {lam φ : ℝ → ℝ} {P D : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hPis : 0 < Pis) (htarget : 1 + φ Pis = Pis / β) (hlam : 0 < lam (φ Pis))
    (hP : ∀ t, 0 < P t) (hPrec : ∀ t, P (t + 1) = Pis * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    Tendsto (tvcValue β lam φ (fun _ => Pis) P D) atTop (𝓝 0) ↔ β * μ < Pis := by
  have hpath : IsPath45 β lam φ (fun _ => Pis) := ⟨fun _ => hPis, fun _ => by
    simp only [htarget]; field_simp⟩
  have hval : ∀ T, tvcValue β lam φ (fun _ => Pis) P D T =
      tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T := by
    intro T
    induction T with
    | zero => simp
    | succ n ih =>
      rw [tvcValue_succ hβ hpath (fun _ => hlam) (fun _ => by rw [htarget]; positivity) hP hPrec
        hD, ih, htarget, pow_succ]
      field_simp
  have h0 : 0 < tvcValue β lam φ (fun _ => Pis) P D 0 := by
    unfold tvcValue; have := hDpos 0; have := hP 0; positivity
  have hr0 : 0 ≤ β * μ / Pis := by positivity
  rw [show tvcValue β lam φ (fun _ => Pis) P D =
    fun T => tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T from funext hval]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    have hr1 : 1 ≤ β * μ / Pis := (one_le_div hPis).mpr hcon
    have hev : ∀ᶠ T in atTop, tvcValue β lam φ (fun _ => Pis) P D 0 ≤
        tvcValue β lam φ (fun _ => Pis) P D 0 * (β * μ / Pis) ^ T :=
      Eventually.of_forall fun T => le_mul_of_one_le_right h0.le (one_le_pow₀ hr1)
    have := ge_of_tendsto h hev
    linarith
  · intro h
    have hr1 : β * μ / Pis < 1 := (div_lt_one hPis).mpr h
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul
      (tvcValue β lam φ (fun _ => Pis) P D 0)

/-- Cochrane (2023), §19.3.2, p. 445, linking Woodford (2003), (1.24), p. 72 to (4.9),
p. 132: with a constant marginal utility `λ ≡ c` (separable utility at constant output) and
`D = M` (nominal money), the Taylor-rule transversality term `β^Tλ D_T/P_T` is the money
transversality term `β^T U_c m_T` of `MoneyTargetingDynamics.money_tvc_violated`, with real
balances `m_T = M_T/P_T` and `U_c ≡ c`. -/
theorem tvcValue_const_lam (β c : ℝ) (φ : ℝ → ℝ) (Pi_ P M : ℕ → ℝ) (T : ℕ) :
    tvcValue β (fun _ => c) φ Pi_ P M T =
      β ^ T * (fun _ : ℝ => c) (M T / P T) * (M T / P T) := by
  unfold tvcValue
  ring

/-- Cochrane (2023), §19.3.2, pp. 442–445, linking Woodford (2003), pp. 132–133 to the
monetary-targeting steady state (`MoneyTargetingDynamics.sepMap_fixed_iff`): when nominal
liabilities grow at the money growth rate `μ̄ > 0` and the target inflation rate is the
money-targeting steady state `Π* = μ̄` (constant real balances), the target path satisfies the
transversality condition iff `β < 1`. -/
theorem target_tvc_money_growth {β μ : ℝ} {lam φ : ℝ → ℝ} {P D : ℕ → ℝ} (hβ : 0 < β)
    (hμ : 0 < μ) (htarget : 1 + φ μ = μ / β) (hlam : 0 < lam (φ μ)) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = μ * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    Tendsto (tvcValue β lam φ (fun _ => μ) P D) atTop (𝓝 0) ↔ β < 1 := by
  rw [target_tvc_iff hβ hμ hμ htarget hlam hP hPrec hD hDpos]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## (4.10): Obstfeld and Rogoff -/

/-- Cochrane (2023), Online Appendix §3.2.2, pp. 621–625 (restated from the Woodford Chapter 2
project). Woodford (2003), (4.10), p. 136: in the separable case,
`lim_{m→0⁺} m u_m(m) = ℓ > 0` implies that `F(m) = (c − v'(m))m` is negative on some interval
`(0, m̲]`. -/
theorem sep_F_neg_of_or_condition {c ℓ : ℝ} {vp : ℝ → ℝ} (hℓ : 0 < ℓ)
    (hlim : Tendsto (fun m => m * vp m) (𝓝[>] 0) (𝓝 ℓ)) :
    ∃ mlow, 0 < mlow ∧ ∀ m, 0 < m → m ≤ mlow → sepF c vp m < 0 := by
  have hF : Tendsto (sepF c vp) (𝓝[>] 0) (𝓝 (c * 0 - ℓ)) := by
    have h1 : Tendsto (fun m : ℝ => c * m) (𝓝[>] 0) (𝓝 (c * 0)) :=
      ((continuous_const.mul continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
    have : sepF c vp = fun m => c * m - m * vp m := by funext m; unfold sepF; ring
    rw [this]
    exact h1.sub hlim
  have hev : ∀ᶠ m in 𝓝[>] 0, sepF c vp m < 0 := hF.eventually (gt_mem_nhds (by linarith))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨u / 2, by linarith [Set.mem_Ioi.mp hu], fun m hm hmu => hsub ⟨hm, by
    linarith [Set.mem_Ioi.mp hu]⟩⟩

/-- Cochrane (2023), Online Appendix §3.2.2, pp. 621–625 (restated from the Woodford Chapter 2
project). Woodford (2003), (4.8) with `G(m) = cm`: a perfect-foresight path for a general
`F`.
Renamed copy of MoneyTargetingDynamics.IsORPath in the Woodford Chapter 2 project. -/
def IsORMapPath (β μ c : ℝ) (F : ℝ → ℝ) (m : ℕ → ℝ) : Prop :=
  (∀ t, 0 < m t) ∧ ∀ t, c * m (t + 1) = μ / β * F (m t)

/-- Cochrane (2023), Online Appendix §3.2.2, pp. 621–625 (restated from the Woodford Chapter 2
project). Woodford (2003), p. 136, "no equilibrium can ever have `m_t ≤ m̲`": if `F ≤ 0` on
`(0, m̲]`, every path has `m_t > m̲`. -/
theorem or_path_above_mlow {β μ c mlow : ℝ} {F : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hFneg : ∀ x, 0 < x → x ≤ mlow → F x ≤ 0) (hpath : IsORMapPath β μ c F m)
    (t : ℕ) : mlow < m t := by
  by_contra hcon
  push Not at hcon
  have h1 := hFneg _ (hpath.1 t) hcon
  have h2 := hpath.2 t
  have h3 : 0 < c * m (t + 1) := mul_pos hc (hpath.1 _)
  have h4 : μ / β * F (m t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h1
  linarith

/-- Cochrane (2023), Online Appendix §3.2.2, pp. 621–625 (restated from the Woodford Chapter 2
project). Woodford (2003), (4.10), p. 136, "no equilibrium is possible with `m_t < m*` at any
time" (monotone-orbit argument): if `F ≤ 0` on `(0, m̲]`, `F` is continuous on `(0, ∞)`, `m*`
is a steady state and the curve is below the diagonal on `[m̲, m*)`, every perfect-foresight
path has `m_t ≥ m*` at all dates. -/
theorem or_no_path_below {β μ c mlow ms : ℝ} {F : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hmlow : 0 < mlow) (hFneg : ∀ x, 0 < x → x ≤ mlow → F x ≤ 0)
    (hFc : ContinuousOn F (Set.Ioi 0))
    (hbelow : ∀ x, mlow ≤ x → x < ms → F x < β / μ * (c * x)) (hpath : IsORMapPath β μ c F m) :
    ∀ t, ms ≤ m t := by
  intro t0
  by_contra hcon
  push Not at hcon
  set g : ℝ → ℝ := fun x => μ / β * F x / c with hg
  have hrec : ∀ t, m (t + 1) = g (m t) := fun t => by
    rw [hg, eq_div_iff hc.ne', mul_comm]; exact hpath.2 t
  have hdown : ∀ x, mlow ≤ x → x < ms → g x < x := by
    intro x h1 h2
    have := hbelow x h1 h2
    rw [hg, div_lt_iff₀ hc]
    have h3 : μ / β * F x < μ / β * (β / μ * (c * x)) := mul_lt_mul_of_pos_left this (by positivity)
    have h4 : μ / β * (β / μ * (c * x)) = x * c := by field_simp
    linarith
  set y : ℕ → ℝ := fun n => m (t0 + n) with hy
  have hyrec : ∀ n, y (n + 1) = g (y n) := fun n => by simp only [hy, ← add_assoc]; exact hrec _
  have hylow : ∀ n, mlow < y n := fun n => or_path_above_mlow hβ hμ hc hFneg hpath _
  have hstep : ∀ n, y n < ms ∧ y (n + 1) < y n := by
    intro n
    induction n with
    | zero => exact ⟨hcon, by rw [hyrec]; exact hdown _ (hylow 0).le hcon⟩
    | succ n ih =>
      have h1 : y (n + 1) < ms := by linarith [ih.1, ih.2]
      exact ⟨h1, by rw [hyrec (n + 1)]; exact hdown _ (hylow _).le h1⟩
  have hanti : Antitone y := antitone_nat_of_succ_le fun n => (hstep n).2.le
  rcases antitone_orbit_atBot_or_fixed hyrec hanti with h | ⟨L, hL, hbd, hfixL⟩
  · obtain ⟨n, hn⟩ := (h.eventually (eventually_le_atBot mlow)).exists
    linarith [hylow n]
  · have hLlow : mlow ≤ L := ge_of_tendsto hL (Eventually.of_forall fun n => (hylow n).le)
    have hcL : ContinuousAt g L :=
      ((continuousAt_const.mul (hFc.continuousAt (Ioi_mem_nhds (by linarith))))).div
        continuousAt_const hc.ne'
    have hf := hfixL hcL
    have hLms : L < ms := lt_of_le_of_lt (hbd 0) (hstep 0).1
    have := hdown L hLlow hLms
    linarith

/-- Cochrane (2023), Online Appendix §3.2.2, pp. 621–625 (restated from the Woodford Chapter 2
project). Woodford (2003), (4.10), p. 136, the bounds of the Obstfeld–Rogoff iteration:
`m̲₀ = m̲`, `m̲_{k+1} = F⁻¹((β/μ̄)G(m̲_k))`. Under continuity, the single crossing below `m*` and
`m̲ < m*`, such a sequence exists, is nondecreasing, stays in `[m̲, m*]`, and converges to `m*`. -/
theorem or_bounds_exist {β μ c mlow ms : ℝ} {F : ℝ → ℝ} (hβ : 0 < β) (hμ : 0 < μ) (hc : 0 < c)
    (hmlow : 0 < mlow) (hlt : mlow < ms) (hFc : ContinuousOn F (Set.Ioi 0))
    (hfix : F ms = β / μ * (c * ms))
    (hbelow : ∀ x, mlow ≤ x → x < ms → F x < β / μ * (c * x)) :
    ∃ b : ℕ → ℝ, b 0 = mlow ∧ (∀ k, F (b (k + 1)) = β / μ * (c * b k)) ∧ Monotone b ∧
      (∀ k, mlow ≤ b k ∧ b k ≤ ms) ∧ Tendsto b atTop (𝓝 ms) := by
  have hsucc : ∀ x : ℝ, ∃ y : ℝ, x ∈ Set.Icc mlow ms →
      y ∈ Set.Icc x ms ∧ F y = β / μ * (c * x) := by
    intro x
    by_cases hx : x ∈ Set.Icc mlow ms
    · rcases hx.2.lt_or_eq with hlt' | heq
      · have hlo : F x ≤ β / μ * (c * x) := (hbelow x hx.1 hlt').le
        have hhi : β / μ * (c * x) ≤ F ms := by
          rw [hfix]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2 hc.le) (by positivity)
        obtain ⟨y, hy, hFy⟩ := intermediate_value_Icc hx.2
          (hFc.mono fun z hz => (by linarith [hz.1, hx.1] : (0 : ℝ) < z)) ⟨hlo, hhi⟩
        exact ⟨y, fun _ => ⟨hy, hFy⟩⟩
      · exact ⟨ms, fun _ => ⟨⟨heq.le, le_rfl⟩, by rw [hfix, heq]⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose g hg using hsucc
  set b : ℕ → ℝ := fun k => g^[k] mlow with hb
  have hbs : ∀ k, b (k + 1) = g (b k) := fun k => Function.iterate_succ_apply' _ _ _
  have hmem : ∀ k, b k ∈ Set.Icc mlow ms := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, hlt.le⟩
    | succ n ih =>
      rw [hbs]
      have := (hg _ ih).1
      exact ⟨le_trans ih.1 this.1, this.2⟩
  have hmono : Monotone b := monotone_nat_of_le_succ fun k => by
    rw [hbs]; exact (hg _ (hmem k)).1.1
  have hF : ∀ k, F (b (k + 1)) = β / μ * (c * b k) := fun k => by
    rw [hbs]; exact (hg _ (hmem k)).2
  refine ⟨b, rfl, hF, hmono, fun k => hmem k, ?_⟩
  have hbdd : BddAbove (Set.range b) := ⟨ms, by rintro _ ⟨k, rfl⟩; exact (hmem k).2⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ k, b k with hL
  have hLms : L ≤ ms := ciSup_le fun k => (hmem k).2
  have hLlow : mlow ≤ L := le_trans (hmem 0).1 (le_ciSup hbdd 0)
  have hcL : ContinuousAt F L := hFc.continuousAt (Ioi_mem_nhds (by linarith))
  have h1 : Tendsto (fun k => F (b (k + 1))) atTop (𝓝 (F L)) :=
    hcL.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun k => F (b (k + 1))) atTop (𝓝 (β / μ * (c * L))) := by
    simp only [hF]
    exact (hlim.const_mul c).const_mul (β / μ)
  have hFL := tendsto_nhds_unique h1 h2
  rcases hLms.lt_or_eq with hlt' | heq
  · have := hbelow L hLlow hlt'
    linarith
  · rw [← heq]; exact hlim

/-- Cochrane (2023), Online Appendix §3.2.2, pp. 621–625 (restated from the Woodford Chapter 2
project). Woodford (2003), (4.10), p. 136, the iteration step "no perfect-foresight equilibrium
can ever have `m_t ≤ m̲₁ ≡ F⁻¹(β/μ̄ G(m̲))` … and so on": if `F ≤ 0` on `(0, m̲]`, `F` is
strictly increasing on `[m̲, ∞)` and `b` is any sequence of bounds as in `or_bounds_exist`,
every path satisfies `m_t > b_k` for all `t` and `k`. -/
theorem or_iteration_bound {β μ c mlow : ℝ} {F : ℝ → ℝ} {m b : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < μ)
    (hc : 0 < c) (hFneg : ∀ x, 0 < x → x ≤ mlow → F x ≤ 0) (hFmono : StrictMonoOn F (Set.Ici mlow))
    (hb0 : b 0 = mlow) (hbF : ∀ k, F (b (k + 1)) = β / μ * (c * b k)) (hblow : ∀ k, mlow ≤ b k)
    (hpath : IsORMapPath β μ c F m) : ∀ k t, b k < m t := by
  intro k
  induction k with
  | zero => intro t; rw [hb0]; exact or_path_above_mlow hβ hμ hc hFneg hpath t
  | succ k ih =>
    intro t
    by_contra hcon
    push Not at hcon
    have hmt := or_path_above_mlow hβ hμ hc hFneg hpath t
    have h1 : F (m t) ≤ F (b (k + 1)) :=
      hFmono.monotoneOn (Set.mem_Ici.mpr hmt.le) (Set.mem_Ici.mpr (hblow _)) hcon
    rw [hbF] at h1
    have h2 : F (m t) = β / μ * (c * m (t + 1)) := by
      rw [hpath.2 t]; field_simp
    rw [h2] at h1
    have h3 : c * m (t + 1) ≤ c * b k := le_of_mul_le_mul_left h1 (by positivity)
    have h4 := ih (t + 1)
    nlinarith

/-- Cochrane (2023), Online Appendix §3.2.2, pp. 621–625 (restated from the Woodford Chapter 2
project). Woodford (2003), (4.10), p. 136, conclusion of the Obstfeld–Rogoff iteration: under
the hypotheses of `or_bounds_exist` and `or_iteration_bound` every perfect-foresight path
satisfies `m_t ≥ m*` at all dates — no self-fulfilling inflation. -/
theorem or_paths_above_mstar {β μ c mlow ms : ℝ} {F : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hμ : 0 < μ) (hc : 0 < c) (hmlow : 0 < mlow) (hlt : mlow < ms)
    (hFc : ContinuousOn F (Set.Ioi 0)) (hfix : F ms = β / μ * (c * ms))
    (hbelow : ∀ x, mlow ≤ x → x < ms → F x < β / μ * (c * x))
    (hFneg : ∀ x, 0 < x → x ≤ mlow → F x ≤ 0) (hFmono : StrictMonoOn F (Set.Ici mlow))
    (hpath : IsORMapPath β μ c F m) : ∀ t, ms ≤ m t := by
  obtain ⟨b, hb0, hbF, -, hbI, hlim⟩ := or_bounds_exist hβ hμ hc hmlow hlt hFc hfix hbelow
  have hbd := or_iteration_bound hβ hμ hc hFneg hFmono hb0 hbF (fun k => (hbI k).1) hpath
  intro t
  exact le_of_tendsto' hlim fun k => (hbd k t).le

/-! ## Links to `MoneyTargetingDynamics` -/

/-- Cochrane (2023), §19.3.2, p. 442, linking Woodford (2003), (4.8), p. 136: the
Obstfeld–Rogoff path for `F = sepF c v'` is exactly `MoneyTargetingDynamics.IsSepPath`. -/
theorem isORMapPath_sep_iff (β μ c : ℝ) (vp : ℝ → ℝ) (m : ℕ → ℝ) :
    IsORMapPath β μ c (sepF c vp) m ↔ IsSepPath β μ c vp m := Iff.rfl

/-- Cochrane (2023), §19.3.2, pp. 442–445, with Woodford (2003), (4.10), p. 136, in the
separable model of `MoneyTargetingDynamics`: if `v'` is continuous on `(0, ∞)`,
`m v'(m) → ℓ > 0` as `m → 0⁺` (Obstfeld–Rogoff), `m*` is a steady state and the map lies below
the diagonal on `(0, m*)`, then no separable path ever has `m_t < m*` (no self-fulfilling
inflation; contrast `MoneyTargetingDynamics.sep_inflation_path`, which needs `v' < c`). -/
theorem or_sep_no_path_below {β μ c ℓ ms : ℝ} {vp : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hμ : 0 < μ) (hc : 0 < c) (hℓ : 0 < ℓ) (hcont : ContinuousOn vp (Set.Ioi 0))
    (hlim : Tendsto (fun x => x * vp x) (𝓝[>] 0) (𝓝 ℓ))
    (hbelow : ∀ x, 0 < x → x < ms → sepF c vp x < β / μ * (c * x))
    (hpath : IsSepPath β μ c vp m) : ∀ t, ms ≤ m t := by
  obtain ⟨mlow, hml, hneg⟩ := sep_F_neg_of_or_condition (c := c) hℓ hlim
  have hFc : ContinuousOn (sepF c vp) (Set.Ioi 0) := by
    have : sepF c vp = fun x => (c - vp x) * x := rfl
    rw [this]
    exact (continuousOn_const.sub hcont).mul continuousOn_id
  exact or_no_path_below hβ hμ hc hml (fun x hx hxl => (hneg x hx hxl).le) hFc
    (fun x hx hxs => hbelow x (by linarith) hxs) hpath

/-- Cochrane (2023), eq. (19.18), p. 442, with Woodford (2003), (4.10), p. 136: under constant
money growth `M_{t+1} = (1 + µ)M_t` and the hypotheses of `or_sep_no_path_below` (with
`c = u_c(y)` and `v' = u_m`), no path of Cochrane's (19.18) ever has real balances below the
steady state. -/
theorem or_miu_no_path_below {β μg ucy ℓ ms : ℝ} {um : ℝ → ℝ} {M m : ℕ → ℝ} (hβ : 0 < β)
    (hμ : 0 < μg) (hucy : 0 < ucy) (hℓ : 0 < ℓ) (hcont : ContinuousOn um (Set.Ioi 0))
    (hlim : Tendsto (fun x => x * um x) (𝓝[>] 0) (𝓝 ℓ))
    (hbelow : ∀ x, 0 < x → x < ms → sepF ucy um x < β / μg * (ucy * x))
    (hM : ∀ t, 0 < M t) (hg : ∀ t, M (t + 1) = μg * M t)
    (hpath : MoneyInUtility.IsMIUPath β ucy um M m) : ∀ t, ms ≤ m t :=
  or_sep_no_path_below hβ hμ hucy hℓ hcont hlim hbelow
    ((miuPath_iff_sepPath hβ hucy hM hg).mp hpath)

end Cochrane.Monetarism.TidyR6WoodfordSections
