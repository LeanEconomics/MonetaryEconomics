/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR7ItoL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Doob's `L²` maximal inequality in discrete time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). Infrastructure for (1.32) with diffusive
bonds (Track 3, chunk B3): the discrete step of Doob's `L²` inequality
`E[max_{l ≤ N} Y_l²] ≤ 4E[Y_N²]`, used on dyadic grids in `TidyR10DoobContinuous`.

Mathlib v4.34 has Doob's maximal inequality maximal_ineq (OptionalStopping; weak type, for
non-negative submartingales) but no `L^p` version. The proof here is elementary and needs only
that the future increments `Y_N − Y_l` are orthogonal to square-integrable `m_l`-measurable
random variables (as `TidyR7ItoContinuity.kolmogorov_maximal`):

* with `S_l = max_{k ≤ l}|Y_k|` (`runMax`) and `D_l = S_l − S_{l−1}` (`runMaxStep`), pathwise
  `S_N² ≤ 2Σ_{l ≤ N} S_l D_l` and `S_l D_l = |Y_l| D_l` (the running maximum only moves when it
  equals `|Y_l|`);
* orthogonality with `G = ±D_l` gives `E[|Y_l| D_l] ≤ E[|Y_N| D_l]`, and `Σ D_l = S_N`, so
  `E[S_N²] ≤ 2E[|Y_N| S_N] ≤ 2√E[Y_N²]·√E[S_N²]` (Cauchy–Schwarz).

## Main results

* `doob_sq_discrete`: **Doob's `L²` inequality**, `E[(max_{l ≤ N}|Y_l|)²] ≤ 4E[Y_N²]`.
* `integral_mul_sub_eq_zero_of_condExp`: the orthogonality hypothesis follows from the
  martingale identity `E[Y_N | m_l] = Y_l`.
-/

namespace Cochrane.ZeroBound.TidyR10DoobDiscrete

open MeasureTheory Filter Topology
open Cochrane.ZeroBound.TidyR7ItoL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool): the running maximum
`S_l = max_{k ≤ l}|Y_k|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMax). -/
noncomputable def runMax (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (l + 1)).sup' Finset.nonempty_range_add_one fun k => |Y k ω|

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool): the increment of the running maximum,
`D_0 = S_0`, `D_l = S_l − S_{l−1}`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMaxStep). -/
noncomputable def runMaxStep (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) : ℝ :=
  runMax Y l ω - if l = 0 then 0 else runMax Y (l - 1) ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `S_0 = |Y_0|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMax_zero). -/
theorem runMax_zero (Y : ℕ → Ω → ℝ) (ω : Ω) : runMax Y 0 ω = |Y 0 ω| := by
  simp [runMax]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `S_{l+1} = max(|Y_{l+1}|, S_l)`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMax_succ). -/
theorem runMax_succ (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) :
    runMax Y (l + 1) ω = max |Y (l + 1) ω| (runMax Y l ω) := by
  refine le_antisymm (Finset.sup'_le _ _ fun k hk => ?_) (max_le ?_ ?_)
  · rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hk) with h | h
    · exact (Finset.le_sup' (fun k => |Y k ω|) (Finset.mem_range.2 h)).trans (le_max_right _ _)
    · rw [h]
      exact le_max_left _ _
  · exact Finset.le_sup' (fun k => |Y k ω|) (Finset.self_mem_range_succ (l + 1))
  · exact Finset.sup'_le _ _ fun k hk => Finset.le_sup' (fun k => |Y k ω|)
      (Finset.mem_range.2 ((Finset.mem_range.1 hk).trans (Nat.lt_succ_self _)))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `|Y_k| ≤ S_l` for `k ≤ l`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.le_runMax). -/
theorem le_runMax (Y : ℕ → Ω → ℝ) {k l : ℕ} (hkl : k ≤ l) (ω : Ω) : |Y k ω| ≤ runMax Y l ω :=
  Finset.le_sup' (fun k => |Y k ω|) (Finset.mem_range.2 (Nat.lt_succ_of_le hkl))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the running maximum is non-negative.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMax_nonneg). -/
theorem runMax_nonneg (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) : 0 ≤ runMax Y l ω :=
  (abs_nonneg _).trans (le_runMax Y (Nat.zero_le l) ω)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the running maximum is non-decreasing.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMax_le_succ). -/
theorem runMax_le_succ (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) : runMax Y l ω ≤ runMax Y (l + 1) ω := by
  rw [runMax_succ]
  exact le_max_right _ _

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the running maximum is at most `Σ_{k ≤ l}|Y_k|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMax_le_sum). -/
theorem runMax_le_sum (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) :
    runMax Y l ω ≤ ∑ k ∈ Finset.range (l + 1), |Y k ω| :=
  Finset.sup'_le _ _ fun _ hk =>
    Finset.single_le_sum (f := fun k => |Y k ω|) (fun _ _ => abs_nonneg _) hk

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `D_0 = |Y_0|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMaxStep_zero). -/
theorem runMaxStep_zero (Y : ℕ → Ω → ℝ) (ω : Ω) : runMaxStep Y 0 ω = |Y 0 ω| := by
  simp [runMaxStep, runMax_zero]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `D_{l+1} = S_{l+1} − S_l`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMaxStep_succ). -/
theorem runMaxStep_succ (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) :
    runMaxStep Y (l + 1) ω = runMax Y (l + 1) ω - runMax Y l ω := by
  simp [runMaxStep]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `D_l ≥ 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMaxStep_nonneg). -/
theorem runMaxStep_nonneg (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) : 0 ≤ runMaxStep Y l ω := by
  rcases l with _ | l
  · rw [runMaxStep_zero]
    exact abs_nonneg _
  · rw [runMaxStep_succ]
    exact sub_nonneg.2 (runMax_le_succ Y l ω)

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `Σ_{l ≤ N} D_l = S_N` (telescoping).
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.sum_runMaxStep). -/
theorem sum_runMaxStep (Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    ∑ l ∈ Finset.range (N + 1), runMaxStep Y l ω = runMax Y N ω := by
  induction N with
  | zero => simp [runMaxStep_zero, runMax_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, runMaxStep_succ]
    ring

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `S_l D_l = |Y_l| D_l`: the running maximum moves only
when it equals `|Y_l|`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMax_mul_step). -/
theorem runMax_mul_step (Y : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) :
    runMax Y l ω * runMaxStep Y l ω = |Y l ω| * runMaxStep Y l ω := by
  rcases l with _ | l
  · rw [runMax_zero]
  · rw [runMaxStep_succ, runMax_succ]
    rcases le_total |Y (l + 1) ω| (runMax Y l ω) with h | h
    · rw [max_eq_right h]
      ring
    · rw [max_eq_left h]

/-- Cochrane (2023), A1 §1.6, pp. 567–568: pathwise, `S_N² ≤ 2Σ_{l ≤ N}|Y_l| D_l`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.runMax_sq_le). -/
theorem runMax_sq_le (Y : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    runMax Y N ω ^ 2 ≤ 2 * ∑ l ∈ Finset.range (N + 1), |Y l ω| * runMaxStep Y l ω := by
  induction N with
  | zero =>
    rw [Finset.sum_range_one, runMaxStep_zero, runMax_zero]
    nlinarith [abs_nonneg (Y 0 ω)]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← runMax_mul_step, runMaxStep_succ]
    have h1 := runMax_le_succ Y N ω
    have h2 := runMax_nonneg Y N ω
    nlinarith

variable {Y : ℕ → Ω → ℝ} {m : ℕ → MeasurableSpace Ω}

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the running maximum of `m`-adapted variables is
`m_l`-strongly measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.stronglyMeasurable_runMax). -/
theorem stronglyMeasurable_runMax (hm : Monotone m) (hY : ∀ l, StronglyMeasurable[m l] (Y l))
    (l : ℕ) : StronglyMeasurable[m l] (runMax Y l) := by
  induction l with
  | zero =>
    have e : runMax Y 0 = fun ω => |Y 0 ω| := funext fun ω => runMax_zero Y ω
    rw [e]
    exact continuous_abs.comp_stronglyMeasurable (hY 0)
  | succ l ih =>
    have e : runMax Y (l + 1) = fun ω => max |Y (l + 1) ω| (runMax Y l ω) :=
      funext fun ω => runMax_succ Y l ω
    rw [e]
    exact continuous_max.comp_stronglyMeasurable
      ((continuous_abs.comp_stronglyMeasurable (hY (l + 1))).prodMk (ih.mono (hm (Nat.le_succ l))))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `D_l` is `m_l`-strongly measurable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.stronglyMeasurable_runMaxStep). -/
theorem stronglyMeasurable_runMaxStep (hm : Monotone m) (hY : ∀ l, StronglyMeasurable[m l] (Y l))
    (l : ℕ) : StronglyMeasurable[m l] (runMaxStep Y l) := by
  rcases l with _ | l
  · have e : runMaxStep Y 0 = fun ω => |Y 0 ω| := funext fun ω => runMaxStep_zero Y ω
    rw [e]
    exact continuous_abs.comp_stronglyMeasurable (hY 0)
  · have e : runMaxStep Y (l + 1) = fun ω => runMax Y (l + 1) ω - runMax Y l ω :=
      funext fun ω => runMaxStep_succ Y l ω
    rw [e]
    exact (stronglyMeasurable_runMax hm hY _).sub
      ((stronglyMeasurable_runMax hm hY l).mono (hm (Nat.le_succ l)))

/-- Cochrane (2023), A1 §1.6, pp. 567–568: the running maximum of square-integrable variables
is square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.memLp_runMax). -/
theorem memLp_runMax (hmle : ∀ l, m l ≤ mΩ) (hm : Monotone m)
    (hY : ∀ l, StronglyMeasurable[m l] (Y l)) (hY2 : ∀ l, MemLp (Y l) 2 P) (l : ℕ) :
    MemLp (runMax Y l) 2 P := by
  have hsum : MemLp (fun ω => ∑ k ∈ Finset.range (l + 1), |Y k ω|) 2 P :=
    memLp_finsetSum _ fun k _ => (hY2 k).abs
  refine hsum.of_le ((stronglyMeasurable_runMax hm hY l).mono (hmle l)).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (runMax_nonneg Y l ω),
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  exact runMax_le_sum Y l ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `D_l` is square integrable.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.memLp_runMaxStep). -/
theorem memLp_runMaxStep (hmle : ∀ l, m l ≤ mΩ) (hm : Monotone m)
    (hY : ∀ l, StronglyMeasurable[m l] (Y l)) (hY2 : ∀ l, MemLp (Y l) 2 P) (l : ℕ) :
    MemLp (runMaxStep Y l) 2 P := by
  rcases l with _ | l
  · have e : runMaxStep Y 0 = fun ω => |Y 0 ω| := funext fun ω => runMaxStep_zero Y ω
    rw [e]
    exact (hY2 0).abs
  · have e : runMaxStep Y (l + 1) = fun ω => runMax Y (l + 1) ω - runMax Y l ω :=
      funext fun ω => runMaxStep_succ Y l ω
    rw [e]
    exact (memLp_runMax hmle hm hY hY2 _).sub (memLp_runMax hmle hm hY hY2 l)

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (Track 3, item 1): Doob's `L²` maximal inequality
in discrete time.** Let `m_l` be increasing σ-algebras below the ambient one, `Y_l` square
integrable and `m_l`-strongly measurable, and suppose `E[G(Y_N − Y_l)] = 0` for every `l ≤ N`
and every square-integrable `m_l`-strongly measurable `G` (a square-integrable martingale:
`integral_mul_sub_eq_zero_of_condExp`). Then `E[(max_{l ≤ N}|Y_l|)²] ≤ 4E[Y_N²]`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.doob_sq_discrete). -/
theorem doob_sq_discrete (hm : Monotone m) (hmle : ∀ l, m l ≤ mΩ)
    (hY : ∀ l, StronglyMeasurable[m l] (Y l)) (hY2 : ∀ l, MemLp (Y l) 2 P) (N : ℕ)
    (horth : ∀ l ≤ N, ∀ G : Ω → ℝ, StronglyMeasurable[m l] G → MemLp G 2 P →
      ∫ ω, G ω * (Y N ω - Y l ω) ∂P = 0) :
    ∫ ω, runMax Y N ω ^ 2 ∂P ≤ 4 * ∫ ω, Y N ω ^ 2 ∂P := by
  have hS := memLp_runMax hmle hm hY hY2 N
  have hD := memLp_runMaxStep hmle hm hY hY2
  have hYN := (hY2 N).abs
  -- step: `E[|Y_l| D_l] ≤ E[|Y_N| D_l]`
  have hstep : ∀ l ≤ N, ∫ ω, |Y l ω| * runMaxStep Y l ω ∂P
      ≤ ∫ ω, |Y N ω| * runMaxStep Y l ω ∂P := by
    intro l hl
    set A : Set Ω := {ω | Y l ω < 0} with hA
    have hAm : MeasurableSet[m l] A := (hY l).measurableSet_lt stronglyMeasurable_const
    set G : Ω → ℝ := fun ω => runMaxStep Y l ω - 2 * A.indicator (runMaxStep Y l) ω with hG
    have hGm : StronglyMeasurable[m l] G :=
      (stronglyMeasurable_runMaxStep hm hY l).sub
        (((stronglyMeasurable_runMaxStep hm hY l).indicator hAm).const_mul 2)
    have hGcase : ∀ ω, (Y l ω < 0 ∧ G ω = -runMaxStep Y l ω)
        ∨ (0 ≤ Y l ω ∧ G ω = runMaxStep Y l ω) := fun ω => by
      by_cases h : Y l ω < 0
      · left
        refine ⟨h, ?_⟩
        simp only [hG, Set.indicator_of_mem (show ω ∈ A from h)]
        ring
      · right
        refine ⟨not_lt.1 h, ?_⟩
        simp only [hG, Set.indicator_of_notMem (show ω ∉ A from h)]
        ring
    have hG2 : MemLp G 2 P := by
      refine (hD l).of_le (hGm.mono (hmle l)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rcases hGcase ω with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
    have h0 := horth l hl G hGm hG2
    have e1 : ∀ ω, |Y l ω| * runMaxStep Y l ω = G ω * Y l ω := fun ω => by
      rcases hGcase ω with ⟨h1, h⟩ | ⟨h1, h⟩ <;> rw [h]
      · rw [abs_of_neg h1]
        ring
      · rw [abs_of_nonneg h1]
        ring
    have e2 : ∀ ω, G ω * Y N ω ≤ |Y N ω| * runMaxStep Y l ω := fun ω => by
      have hd := runMaxStep_nonneg Y l ω
      rcases hGcase ω with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h]
      · nlinarith [neg_abs_le (Y N ω)]
      · nlinarith [le_abs_self (Y N ω)]
    have i1 : Integrable (fun ω => G ω * Y N ω) P := hG2.integrable_mul (hY2 N)
    have i2 : Integrable (fun ω => G ω * Y l ω) P := hG2.integrable_mul (hY2 l)
    have e3 : ∫ ω, G ω * Y N ω ∂P = ∫ ω, G ω * Y l ω ∂P := by
      have e4 : ∫ ω, G ω * (Y N ω - Y l ω) ∂P = ∫ ω, G ω * Y N ω ∂P - ∫ ω, G ω * Y l ω ∂P := by
        rw [← integral_sub i1 i2]
        exact integral_congr_ae (ae_of_all _ fun ω => by ring)
      linarith
    calc ∫ ω, |Y l ω| * runMaxStep Y l ω ∂P = ∫ ω, G ω * Y l ω ∂P :=
          integral_congr_ae (ae_of_all _ e1)
      _ = ∫ ω, G ω * Y N ω ∂P := e3.symm
      _ ≤ ∫ ω, |Y N ω| * runMaxStep Y l ω ∂P :=
          integral_mono i1 (hYN.integrable_mul (hD l)) e2
  -- `E[S_N²] ≤ 2E[|Y_N| S_N]`
  have hmain : ∫ ω, runMax Y N ω ^ 2 ∂P ≤ 2 * ∫ ω, |Y N ω| * runMax Y N ω ∂P := by
    have iS : ∀ l, Integrable (fun ω => |Y l ω| * runMaxStep Y l ω) P := fun l =>
      (hY2 l).abs.integrable_mul (hD l)
    calc ∫ ω, runMax Y N ω ^ 2 ∂P
        ≤ ∫ ω, 2 * ∑ l ∈ Finset.range (N + 1), |Y l ω| * runMaxStep Y l ω ∂P :=
          integral_mono hS.integrable_sq
            ((integrable_finsetSum _ fun l _ => iS l).const_mul 2) (runMax_sq_le Y N)
      _ = 2 * ∑ l ∈ Finset.range (N + 1), ∫ ω, |Y l ω| * runMaxStep Y l ω ∂P := by
          rw [integral_const_mul, integral_finsetSum _ fun l _ => iS l]
      _ ≤ 2 * ∑ l ∈ Finset.range (N + 1), ∫ ω, |Y N ω| * runMaxStep Y l ω ∂P := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l hl => hstep l ?_) two_pos.le
          exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      _ = 2 * ∫ ω, |Y N ω| * runMax Y N ω ∂P := by
          have iN : ∀ l ∈ Finset.range (N + 1),
              Integrable (fun ω => |Y N ω| * runMaxStep Y l ω) P := fun l _ =>
            (hY2 N).abs.integrable_mul (hD l)
          rw [← integral_finsetSum _ iN]
          congr 1
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only
          rw [← Finset.mul_sum, sum_runMaxStep]
  -- Cauchy–Schwarz and the quadratic bound
  have hcs := sq_integral_mul_le hYN hS
  simp only [Pi.abs_apply, sq_abs] at hcs
  set x := ∫ ω, runMax Y N ω ^ 2 ∂P
  set a := ∫ ω, Y N ω ^ 2 ∂P
  set b := ∫ ω, |Y N ω| * runMax Y N ω ∂P
  have hx : 0 ≤ x := integral_nonneg fun _ => sq_nonneg _
  have ha : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
  have hb : 0 ≤ b := integral_nonneg fun ω => mul_nonneg (abs_nonneg _) (runMax_nonneg Y N ω)
  have h1 : x ^ 2 ≤ 4 * a * x := by nlinarith
  rcases hx.lt_or_eq with hx | hx
  · nlinarith
  · rw [← hx]
    linarith

/-- Cochrane (2023), A1 §1.6, pp. 567–568 (tool): **a martingale identity gives orthogonal
increments.** If `E[Z | m] = Y` a.e. and `Y, Z, G` are square
integrable with `G` `m`-strongly measurable, then `E[G(Z − Y)] = 0`.
Restated from the Cochrane Monetarism project
(Cochrane.Monetarism.TidyR10DoobDiscrete.integral_mul_sub_eq_zero_of_condExp). -/
theorem integral_mul_sub_eq_zero_of_condExp [IsFiniteMeasure P] {m0 : MeasurableSpace Ω}
    (hm0 : m0 ≤ mΩ) {Y Z G : Ω → ℝ} (hYZ : P[Z | m0] =ᵐ[P] Y) (hZ : MemLp Z 2 P) (hY : MemLp Y 2 P)
    (hG : StronglyMeasurable[m0] G) (hG2 : MemLp G 2 P) :
    ∫ ω, G ω * (Z ω - Y ω) ∂P = 0 := by
  have iGZ : Integrable (G * Z) P := hG2.integrable_mul hZ
  have iGY : Integrable (fun ω => G ω * Y ω) P := hG2.integrable_mul hY
  have h1 : P[G * Z | m0] =ᵐ[P] G * P[Z | m0] :=
    condExp_mul_of_stronglyMeasurable_left hG iGZ (hZ.integrable one_le_two)
  have h2 : ∫ ω, G ω * Z ω ∂P = ∫ ω, G ω * Y ω ∂P := by
    have e := integral_condExp hm0 (μ := P) (f := G * Z)
    simp only [Pi.mul_apply] at e
    rw [← e]
    refine integral_congr_ae ?_
    filter_upwards [h1, hYZ] with ω h1ω h2ω
    rw [h1ω, Pi.mul_apply, h2ω]
  have iGZ' : Integrable (fun ω => G ω * Z ω) P := iGZ
  rw [← sub_eq_zero.2 h2, ← integral_sub iGZ' iGY]
  exact integral_congr_ae (ae_of_all _ fun ω => by ring)

end Cochrane.ZeroBound.TidyR10DoobDiscrete
