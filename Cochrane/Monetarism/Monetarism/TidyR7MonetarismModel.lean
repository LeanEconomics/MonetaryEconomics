/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7MonetarismAC
import Monetarism.TidyR7ProductStep
import Monetarism.TidyR6StochasticDrift

/-!
# The money–bond model of §1.6 under uncertainty and the expected-increment equations (1.32)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34).

## The model (`MonetaryModel`)

A measure `μ` (finite in the theorems), a filtration `𝓕` indexed by `ℝ`, and processes
`ℝ → Ω → ℝ`: the SDF `Λ > 0`, the price level `P > 0` (both adapted), nominal bonds `B` and money
`M` (adapted), the nominal rate `i`, the interest on money `i^m`, the real surplus `s` (`sp`).
* **The nominal discount factor** `n = Λ/P` (`disc`) splits as `n = A + N`: `N` a càdlàg
  martingale (the news in `Λ/P`, jumps allowed) and `A` with
  `A_v − A_u = −∫_u^v i_r n_r dr` (`IncrOf`; `i·n` locally integrable path by path, `LocInt`).
  This is the bond-pricing condition `E_t d(Λ/P)/(Λ/P) = −i_t dt` in the expected-increment sense of
  `TidyR7ProductStep.ExpIncrLimit` (`MonetaryModel.expIncr_disc`).
* **Money** has continuous paths of bounded variation on every `[a, b]`.
* **The nominal flow (1.31)** `dM = iB dt + i^mM dt − Ps dt − dB`, path by path, as an identity of
  integrals: `(B + M)_v − (B + M)_u = ∫_u^v (iB + i^mM − Ps) dr` (`flowRate` locally integrable).
  Then `B = (B + M) − M` has continuous bounded-variation paths (`MonetaryModel.B_cont`,
  `MonetaryModel.B_bv`) and `dB` is the Lebesgue–Stieltjes measure of that path.

No measurability of `i`, `i^m`, `s` in `ω` is assumed: the integrals that enter the conditional
expectations are measurable as limits of partition sums (I2).

## Main results

* `MonetaryModel.pathwise_1_32`, `MonetaryModel.pathwise_1_34`: path by path,
  `∫_s^t n dB + ∫_s^t B dA = −(∫_s^t (Λs − i^m nM) dr + ∫_s^t n dM)` and
  `∫_s^t n d(B + M) + ∫_s^t (B + M) dA = −∫_s^t (Λs + (i − i^m)nM) dr`.
* `MonetaryModel.incr_1_32_general` (`i^m` arbitrary) and `MonetaryModel.incr_1_32` (`i^m = 0`,
  the book's (1.32)): `E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t Λ_rs_r dr + ∫_s^t n dM]`, i.e. integrated
  `E_t d(ΛB/P) = −Λ(s dt + dM/P)`.
* `MonetaryModel.expIncr_disc`, `MonetaryModel.middle_1_32`: the middle line of (1.32),
  `Λ/P·dB + E_t[d(Λ/P)]B = −Λ(s dt + dM/P)`, with `B·E_s d(Λ/P) = −E_s∫_s^t i n B`.
* `MonetaryModel.incr_1_34`: `E_s[n_t(B + M)_t − n_s(B + M)_s] = −E_s∫_s^t (Λs + (i − i^m)nM) dr`,
  integrated `E_t d(Λ(M + B)/P) = −Λ(s + (i − i^m)M/P) dt`, the line before (1.34).
* `MonetaryModel.hasDrift_1_34`, `MonetaryModel.hasDrift_1_32_ac`: the corresponding
  `TidyR6StochasticDrift.HasDrift` instances (for (1.32) when money has a density, `dM = m dt`).
* `Dominated`, `Dominated.of_bound`: the integrability conditions of the product step, and their
  verification for bounded paths of bounded variation.
-/

namespace Cochrane.Monetarism.TidyR7MonetarismModel

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7CondDominated Cochrane.Monetarism.TidyR7ProductStep
  Cochrane.Monetarism.TidyR7MonetarismAC

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the nominal discount factor `n_u = Λ_u/P_u`. -/
noncomputable def disc (Λ P : ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) : ℝ := Λ u ω / P u ω

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: the flow density `i B + i^m M − P s` of `B + M`. -/
def flowRate (B M P i im sp : ℝ → Ω → ℝ) (r : ℝ) (ω : Ω) : ℝ :=
  i r ω * B r ω + im r ω * M r ω - P r ω * sp r ω

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: **the path `g` has increments `∫ h`**:
`g_v − g_u = ∫_u^v h_r dr` for all `u ≤ v`, path by path. -/
def IncrOf (g h : ℝ → Ω → ℝ) : Prop :=
  ∀ ω u v, u ≤ v → g v ω - g u ω = ∫ r in u..v, h r ω

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: `h` is locally integrable path by path. -/
def LocInt (h : ℝ → Ω → ℝ) : Prop :=
  ∀ ω u v, IntervalIntegrable (fun r => h r ω) MeasureSpace.volume u v

variable (μ : Measure Ω) (𝓕 : Filtration ℝ mΩ) (Λ P B M A N i im sp : ℝ → Ω → ℝ)

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: the model under uncertainty.**
`Λ, P > 0` adapted; `Λ/P = A + N` with `N` a càdlàg martingale and `dA = −i(Λ/P) dt` (the
bond-pricing condition); `B`, `M` adapted, money continuous of bounded variation; the flow (1.31)
`d(B + M) = (iB + i^mM − Ps) dt` path by path. -/
structure MonetaryModel where
  P_pos : ∀ u ω, 0 < P u ω
  Λ_pos : ∀ u ω, 0 < Λ u ω
  Λ_adapted : ∀ u, StronglyMeasurable[𝓕 u] (Λ u)
  P_adapted : ∀ u, StronglyMeasurable[𝓕 u] (P u)
  dec : ∀ u ω, disc Λ P u ω = A u ω + N u ω
  A_incr : IncrOf A fun r ω => -(i r ω * disc Λ P r ω)
  A_int : LocInt fun r ω => -(i r ω * disc Λ P r ω)
  N_mart : Martingale N 𝓕 μ
  N_cadlag : ∀ ω, IsCadlag fun u => N u ω
  B_adapted : ∀ u, StronglyMeasurable[𝓕 u] (B u)
  M_adapted : ∀ u, StronglyMeasurable[𝓕 u] (M u)
  M_cont : ∀ ω, Continuous fun u => M u ω
  M_bv : ∀ ω a b, BoundedVariationOn (fun u => M u ω) (Set.Icc a b)
  flow : IncrOf (addProc B M) (flowRate B M P i im sp)
  flow_int : LocInt (flowRate B M P i im sp)

variable (s t : ℝ) (Y X : ℝ → Ω → ℝ)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the domination conditions of the product step**
for bonds `Y` against `X = Λ/P = A + N` on `[s, t]` (those of
`TidyR7ProductStep.ProductStepData`): `sup|X|·Var(Y)`, `sup|Y|·Var(A)` and `Y_u(N_v − N_u)`
integrable. Argument order: `Dominated μ A N s t Y X`. -/
structure Dominated where
  sup_var : Integrable (fun ω => pathSup s t X ω * pathVar s t Y ω) μ
  sup_varA : Integrable (fun ω => pathSup s t Y ω * pathVar s t A ω) μ
  mart_incr : ∀ u v, s ≤ u → u ≤ v → v ≤ t → Integrable (fun ω => Y u ω * (N v ω - N u ω)) μ

variable {μ 𝓕 Λ P B M A N i im sp s t Y X}

/-- Cochrane (2023), A1 §1.6, p. 567: **the domination conditions hold for bounded paths of
bounded variation**: if on `[s, t]` the paths of `X` are càdlàg with `|X| ≤ K`, the paths of `Y`
are continuous with `|Y| ≤ K`, `Var(Y), Var(A) ≤ K`, all processes measurable at each time and
`N` integrable, then `Dominated` holds for a finite measure.
Extends `TidyR7ProductStep.integrable_mul_incr_of_bound`. -/
theorem Dominated.of_bound [IsFiniteMeasure μ] {K : ℝ} (hK : 0 ≤ K) (hXm : ∀ u, Measurable (X u))
    (hYm : ∀ u, Measurable (Y u)) (hAm : ∀ u, Measurable (A u))
    (hYc : ∀ ω, Continuous fun u => Y u ω) (hAc : ∀ ω, IsCadlag fun u => A u ω)
    (hN : ∀ u, Integrable (N u) μ)
    (hX : ∀ ω, ∀ u ∈ Set.Icc s t, |X u ω| ≤ K) (hY : ∀ ω, ∀ u ∈ Set.Icc s t, |Y u ω| ≤ K)
    (hVY : ∀ ω, pathVar s t Y ω ≤ K) (hVA : ∀ ω, pathVar s t A ω ≤ K) :
    Dominated μ A N s t Y X := by
  have hsup : ∀ Z : ℝ → Ω → ℝ, (∀ ω, ∀ u ∈ Set.Icc s t, |Z u ω| ≤ K) →
      ∀ ω, pathSup s t Z ω ≤ K := fun Z hZ ω => Real.iSup_le (fun q => hZ ω q q.2.1) hK
  have hvar0 : ∀ (Z : ℝ → Ω → ℝ) ω, 0 ≤ pathVar s t Z ω := fun _ _ => ENNReal.toReal_nonneg
  have mY : Measurable (pathVar s t Y) :=
    TidyR7StieltjesVariation.measurable_variation_toReal_of_continuousOn (a := s) (b := t)
      (g := fun ω u => Y u ω) hYm fun ω => (hYc ω).continuousOn
  have mA : Measurable (pathVar s t A) :=
    TidyR7StieltjesVariation.measurable_variation_toReal_of_isCadlag (a := s) (b := t)
      (g := fun ω u => A u ω) hAm hAc
  have bound : ∀ (Z W : ℝ → Ω → ℝ), (∀ ω, ∀ u ∈ Set.Icc s t, |Z u ω| ≤ K) →
      (∀ ω, pathVar s t W ω ≤ K) → Measurable (pathSup s t Z) → Measurable (pathVar s t W) →
      Integrable (fun ω => pathSup s t Z ω * pathVar s t W ω) μ := by
    intro Z W hZ hW m1 m2
    refine Integrable.of_bound (m1.mul m2).aestronglyMeasurable (K * K)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pathSup_nonneg s t Z ω) (hvar0 W ω))]
    exact mul_le_mul (hsup Z hZ ω) (hW ω) (hvar0 W ω) hK
  exact ⟨bound X Y hX hVY (measurable_pathSup fun u _ => hXm u) mY,
    bound Y A hY hVA (measurable_pathSup fun u _ => hYm u) mA,
    integrable_mul_incr_of_bound (B := Y) (M := N) (K := K) (fun u hu ω => hY ω u hu)
      (fun u _ => hYm u) hN⟩

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): the variation of `−f` is that of `f`. -/
theorem eVariationOn_neg (f : ℝ → ℝ) (S : Set ℝ) :
    eVariationOn (fun x => -f x) S = eVariationOn f S := by
  simp only [eVariationOn, edist_neg_neg]

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): `f + (−1)·g` has bounded variation when `f` and `g`
have. -/
theorem bv_add_neg {f g : ℝ → ℝ} {S : Set ℝ} (hf : BoundedVariationOn f S)
    (hg : BoundedVariationOn g S) : BoundedVariationOn (fun x => f x + -1 * g x) S := by
  have h1 : BoundedVariationOn (fun x => -1 * g x) S := by
    have e : (fun x => -1 * g x) = fun x => -g x := funext fun x => by ring
    rw [BoundedVariationOn, e, eVariationOn_neg]
    exact hg
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, h1⟩) (eVariationOn_add_le _ _ S)

/-- Cochrane (2023), A1 §1.6, p. 567 (tool): a càdlàg function times an interval integrable one is
interval integrable on `[a, b]` (the càdlàg factor is bounded and measurable).
An instance of Mathlib `Integrable.bdd_mul`. -/
theorem intervalIntegrable_mul_of_isCadlag {f h : ℝ → ℝ} (hf : IsCadlag f) {a b : ℝ}
    (hab : a ≤ b) (hh : IntervalIntegrable h MeasureSpace.volume a b) :
    IntervalIntegrable (fun x => f x * h x) MeasureSpace.volume a b := by
  obtain ⟨C, -, hC⟩ := exists_bound_of_isCadlag hf a b
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hh ⊢
  exact hh.bdd_mul (c := C) (measurable_of_isCadlag hf).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]
      exact hC x ⟨hx.1.le, hx.2⟩))

namespace MonetaryModel

variable (hm : MonetaryModel μ 𝓕 Λ P B M A N i im sp)
include hm

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ/P = A + N` as processes. -/
theorem disc_eq : disc Λ P = addProc A N :=
  funext fun u => funext fun ω => hm.dec u ω

/-- Cochrane (2023), A1 §1.6, p. 567: `(Λ/P)·P = Λ`. -/
theorem disc_mul_P (u : ℝ) (ω : Ω) : disc Λ P u ω * P u ω = Λ u ω :=
  div_mul_cancel₀ (Λ u ω) (hm.P_pos u ω).ne'

/-- Cochrane (2023), A1 §1.6, p. 567: `A` has continuous paths (it has a locally integrable
density). -/
theorem A_cont (ω : Ω) : Continuous fun u => A u ω :=
  continuous_of_incr (hm.A_int ω) (hm.A_incr ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `A` has bounded variation on every `[a, b]`. -/
theorem A_bv (ω : Ω) (a b : ℝ) : BoundedVariationOn (fun u => A u ω) (Set.Icc a b) :=
  bv_of_incr (hm.A_int ω) (hm.A_incr ω) a b

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: `B + M` has continuous paths. -/
theorem W_cont (ω : Ω) : Continuous fun u => addProc B M u ω :=
  continuous_of_incr (hm.flow_int ω) (hm.flow ω)

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: `B + M` has bounded variation on every `[a, b]`. -/
theorem W_bv (ω : Ω) (a b : ℝ) : BoundedVariationOn (fun u => addProc B M u ω) (Set.Icc a b) :=
  bv_of_incr (hm.flow_int ω) (hm.flow ω) a b

omit hm in
/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: bonds `B = (B + M) − M` as paths. -/
theorem B_eq (ω : Ω) : (fun u => B u ω) = fun u => addProc B M u ω + -1 * M u ω :=
  funext fun u => by simp only [addProc]; ring

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: bonds have continuous paths. -/
theorem B_cont (ω : Ω) : Continuous fun u => B u ω := by
  rw [B_eq (B := B) (M := M) ω]
  exact (hm.W_cont ω).add (continuous_const.mul (hm.M_cont ω))

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567: bonds have bounded variation on every `[a, b]`. -/
theorem B_bv (ω : Ω) (a b : ℝ) : BoundedVariationOn (fun u => B u ω) (Set.Icc a b) := by
  rw [B_eq (B := B) (M := M) ω]
  exact bv_add_neg (hm.W_bv ω a b) (hm.M_bv ω a b)

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ/P` has càdlàg paths. -/
theorem disc_cadlag (ω : Ω) : IsCadlag fun u => disc Λ P u ω := by
  rw [hm.disc_eq]
  exact (hm.A_cont ω).isCadlag.fun_add (hm.N_cadlag ω)

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ_u/P_u` is `𝓕_u`-measurable. -/
theorem disc_adapted (u : ℝ) : StronglyMeasurable[𝓕 u] (disc Λ P u) :=
  ((hm.Λ_adapted u).measurable.div (hm.P_adapted u).measurable).stronglyMeasurable

/-- Cochrane (2023), A1 §1.6, p. 567: `Λ_u/P_u` is measurable. -/
theorem measurable_disc (u : ℝ) : Measurable (disc Λ P u) :=
  ((hm.disc_adapted u).mono (𝓕.le u)).measurable

/-- Cochrane (2023), A1 §1.6, p. 567: `A_u = Λ_u/P_u − N_u` is measurable. -/
theorem measurable_A (u : ℝ) : Measurable (A u) := by
  have e : A u = fun ω => disc Λ P u ω - N u ω := funext fun ω => by rw [hm.dec u ω]; ring
  rw [e]
  exact (hm.measurable_disc u).sub (((hm.N_mart.1 u).mono (𝓕.le u)).measurable)

/-- Cochrane (2023), A1 §1.6, p. 567: `B + M` is adapted. -/
theorem W_adapted (u : ℝ) : StronglyMeasurable[𝓕 u] (addProc B M u) :=
  (hm.B_adapted u).add (hm.M_adapted u)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the data of the product step for bonds**
`B` against `Λ/P = A + N` on `[s, t]`, under the domination conditions. -/
theorem productStepData_B (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    ProductStepData μ 𝓕 s t B A N where
  le := hst
  B_adapted u _ := hm.B_adapted u
  B_cont ω := (hm.B_cont ω).continuousOn
  B_bv ω := hm.B_bv ω s t
  A_meas u _ := hm.measurable_A u
  A_cadlag ω := (hm.A_cont ω).isCadlag
  A_bv ω := hm.A_bv ω s t
  M_mart := hm.N_mart
  M_cadlag := hm.N_cadlag
  int_XB := by rw [← hm.disc_eq]; exact hd.sup_var
  int_BA := hd.sup_varA
  int_BM := hd.mart_incr

/-- Cochrane (2023), A1 §1.6, (1.34), p. 567: **the data of the product step for bonds plus
money** `B + M` against `Λ/P = A + N` on `[s, t]`. -/
theorem productStepData_W (hst : s ≤ t) (hd : Dominated μ A N s t (addProc B M) (disc Λ P)) :
    ProductStepData μ 𝓕 s t (addProc B M) A N where
  le := hst
  B_adapted u _ := hm.W_adapted u
  B_cont ω := (hm.W_cont ω).continuousOn
  B_bv ω := hm.W_bv ω s t
  A_meas u _ := hm.measurable_A u
  A_cadlag ω := (hm.A_cont ω).isCadlag
  A_bv ω := hm.A_bv ω s t
  M_mart := hm.N_mart
  M_cadlag := hm.N_cadlag
  int_XB := by rw [← hm.disc_eq]; exact hd.sup_var
  int_BA := hd.sup_varA
  int_BM := hd.mart_incr

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `∫_s^t B dA = −∫_s^t i n B` path by path (the
expected increment of `Λ/P` is `−i(Λ/P) dt`). -/
theorem rsInt_B_A (ω : Ω) (hst : s ≤ t) :
    rsInt s t (fun u => B u ω) (fun u => A u ω) =
      -∫ r in s..t, i r ω * disc Λ P r ω * B r ω := by
  rw [rsInt_eq_integral_of_incr (hm.B_cont ω).isCadlag (hm.A_int ω) (hm.A_incr ω) hst,
    ← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun r _ => by ring

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, path by path.** For `s ≤ t`,
`∫_s^t n dB + ∫_s^t B dA = −(∫_s^t (Λ_rs_r − i^m_rn_rM_r) dr + ∫_s^t n dM)`, `n = Λ/P`. -/
theorem pathwise_1_32 (ω : Ω) (hst : s ≤ t) :
    rsInt s t (fun u => disc Λ P u ω) (fun u => B u ω) +
        rsInt s t (fun u => B u ω) (fun u => A u ω) =
      -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω)) := by
  have hn := hm.disc_cadlag ω
  have hMbv : BoundedVariationOn (fun u => -1 * M u ω) (Set.Icc s t) := by
    have e : (fun u => -1 * M u ω) = fun u => -M u ω := funext fun u => by ring
    rw [BoundedVariationOn, e, eVariationOn_neg]
    exact hm.M_bv ω s t
  have e1 : rsInt s t (fun u => disc Λ P u ω) (fun u => B u ω) =
      rsInt s t (fun u => disc Λ P u ω) (fun u => addProc B M u ω) -
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω) := by
    rw [B_eq (B := B) (M := M) ω,
      rsInt_add_right hst (hm.W_bv ω s t) hMbv (rsIntegrable_of_isCadlag hn),
      rsInt_smul_right (-1) hst (hm.M_bv ω s t)]
    ring
  have e2 : rsInt s t (fun u => disc Λ P u ω) (fun u => addProc B M u ω) =
      ∫ r in s..t, disc Λ P r ω * flowRate B M P i im sp r ω :=
    rsInt_eq_integral_of_incr hn (hm.flow_int ω) (hm.flow ω) hst
  have e3 : rsInt s t (fun u => B u ω) (fun u => A u ω) =
      ∫ r in s..t, B r ω * -(i r ω * disc Λ P r ω) :=
    rsInt_eq_integral_of_incr (hm.B_cont ω).isCadlag (hm.A_int ω) (hm.A_incr ω) hst
  have i1 : IntervalIntegrable (fun r => disc Λ P r ω * flowRate B M P i im sp r ω)
      MeasureSpace.volume s t := intervalIntegrable_mul_of_isCadlag hn hst (hm.flow_int ω s t)
  have i2 : IntervalIntegrable (fun r => B r ω * -(i r ω * disc Λ P r ω))
      MeasureSpace.volume s t :=
    intervalIntegrable_mul_of_isCadlag (hm.B_cont ω).isCadlag hst (hm.A_int ω s t)
  have e4 : (∫ r in s..t, disc Λ P r ω * flowRate B M P i im sp r ω) +
      (∫ r in s..t, B r ω * -(i r ω * disc Λ P r ω)) =
        -∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω) := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [flowRate]
    rw [← hm.disc_mul_P r ω]
    ring
  rw [e1, e2, e3]
  linarith

/-- **Cochrane (2023), A1 §1.6, (1.34), p. 567, path by path.** For `s ≤ t`,
`∫_s^t n d(B + M) + ∫_s^t (B + M) dA = −∫_s^t (Λ_rs_r + (i_r − i^m_r)n_rM_r) dr`. -/
theorem pathwise_1_34 (ω : Ω) (hst : s ≤ t) :
    rsInt s t (fun u => disc Λ P u ω) (fun u => addProc B M u ω) +
        rsInt s t (fun u => addProc B M u ω) (fun u => A u ω) =
      -∫ r in s..t, (Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω) := by
  have hn := hm.disc_cadlag ω
  have hW := (hm.W_cont ω).isCadlag
  rw [rsInt_eq_integral_of_incr hn (hm.flow_int ω) (hm.flow ω) hst,
    rsInt_eq_integral_of_incr hW (hm.A_int ω) (hm.A_incr ω) hst,
    ← intervalIntegral.integral_add (intervalIntegrable_mul_of_isCadlag hn hst (hm.flow_int ω s t))
      (intervalIntegrable_mul_of_isCadlag hW hst (hm.A_int ω s t)),
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun r _ => ?_
  simp only [flowRate, addProc]
  rw [← hm.disc_mul_P r ω]
  ring

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the integrand `Λs − i^m nM` of (1.32) is interval
integrable path by path (it is `−(n·(iB + i^mM − Ps) − iBn)`). -/
theorem intervalIntegrable_1_32 (ω : Ω) (hst : s ≤ t) :
    IntervalIntegrable (fun r => Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)
      MeasureSpace.volume s t := by
  have i1 := intervalIntegrable_mul_of_isCadlag (hm.disc_cadlag ω) hst (hm.flow_int ω s t)
  have i2 := intervalIntegrable_mul_of_isCadlag (hm.B_cont ω).isCadlag hst (hm.A_int ω s t)
  have e : (fun r => Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω) = fun r =>
      -(disc Λ P r ω * flowRate B M P i im sp r ω + B r ω * -(i r ω * disc Λ P r ω)) :=
    funext fun r => by
      simp only [flowRate]
      rw [← hm.disc_mul_P r ω]
      ring
  rw [e]
  exact (i1.add i2).neg

variable [IsFiniteMeasure μ]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, with interest on money.** Under the domination
conditions on `[s, t]`, almost surely
`E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t (Λ_rs_r − i^m_rn_rM_r) dr + ∫_s^t n dM]`, `n = Λ/P`. -/
theorem incr_1_32_general (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω)) | 𝓕 s] := by
  have hpd := hm.productStepData_B hst hd
  have h := hpd.product_step
  have i1 := hpd.integrable_intXB
  have i2 := hpd.integrable_intBA
  rw [← hm.disc_eq] at h i1
  have eL : (fun ω => B t ω * disc Λ P t ω - B s ω * disc Λ P s ω) =
      fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω := funext fun ω => by ring
  have eR : (fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω))) =
      intRS s t (disc Λ P) B + intRS s t B A :=
    funext fun ω => (hm.pathwise_1_32 ω hst).symm
  rw [eL] at h
  rw [eR]
  filter_upwards [h, condExp_add i1 i2 (𝓕 s)] with ω h1 h2
  rw [h1, h2]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_t d(ΛB/P) = −Λ(s dt + dM/P)`, integrated.**
With `i^m = 0` and the domination conditions on `[s, t]`, almost surely
`E_s[n_tB_t − n_sB_s] = −E_s[∫_s^t Λ_rs_r dr + ∫_s^t n dM]`, `n = Λ/P`.
Generalises `TidyR6StochasticDrift.drift_1_32_fv` and `TidyR7ProductStepCases.product_step_1_32_C1`;
continuous-time form of `TidyR6StochasticDrift.incr_1_32`. -/
theorem incr_1_32 (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P))
    (him : ∀ r ω, im r ω = 0) :
    μ[fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -((∫ r in s..t, Λ r ω * sp r ω) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω)) | 𝓕 s] := by
  have h := hm.incr_1_32_general hst hd
  have e : (fun ω => -((∫ r in s..t, (Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω)) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω))) = fun ω =>
      -((∫ r in s..t, Λ r ω * sp r ω) + rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω)) :=
    funext fun ω => by simp only [him, zero_mul, sub_zero]
  rwa [e] at h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `E_t d(Λ/P) = −i(Λ/P) dt` in the
expected-increment sense.** The expected-increment integral `B·E_s d(Λ/P)`
(`TidyR7ProductStep.ExpIncrLimit`) exists and equals `−E_s∫_s^t i n B`.
Generalises part of `TidyR7ProductStepCases.product_step_1_32_C1`. -/
theorem expIncr_disc (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P)) :
    ExpIncrLimit μ 𝓕 s t B (disc Λ P)
      (μ[fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω | 𝓕 s]) := by
  have h := expIncrLimit_condExp_rsInt (hm.productStepData_B hst hd)
  have e : intRS s t B A = fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω :=
    funext fun ω => hm.rsInt_B_A ω hst
  rw [e, ← hm.disc_eq] at h
  exact h

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, the middle line**
`(Λ/P) dB + E_t[d(Λ/P)]B = −Λ(s dt + dM/P)`, integrated: with `i^m = 0`, almost surely
`E_s[∫_s^t n dB] + B·E_s d(Λ/P) = −E_s[∫_s^t Λs dr + ∫_s^t n dM]`, where
`B·E_s d(Λ/P) = −E_s∫_s^t i n B` (`MonetaryModel.expIncr_disc`). -/
theorem middle_1_32 (hst : s ≤ t) (hd : Dominated μ A N s t B (disc Λ P))
    (him : ∀ r ω, im r ω = 0) :
    μ[intRS s t (disc Λ P) B | 𝓕 s] +
        μ[fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -((∫ r in s..t, Λ r ω * sp r ω) +
        rsInt s t (fun u => disc Λ P u ω) (fun u => M u ω)) | 𝓕 s] := by
  have hpd := hm.productStepData_B hst hd
  have h := hpd.product_step
  rw [← hm.disc_eq] at h
  have e : intRS s t B A = fun ω => -∫ r in s..t, i r ω * disc Λ P r ω * B r ω :=
    funext fun ω => hm.rsInt_B_A ω hst
  have eL : (fun ω => B t ω * disc Λ P t ω - B s ω * disc Λ P s ω) =
      fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω := funext fun ω => by ring
  rw [e, eL] at h
  filter_upwards [h, hm.incr_1_32 hst hd him] with ω h1 h2
  rw [← h1, h2]

/-- **Cochrane (2023), A1 §1.6, p. 567, the line before (1.34):
`E_t d(Λ(M + B)/P) = −Λ(s + (i − i^m)M/P) dt`, integrated.** Under the domination conditions for
`B + M` on `[s, t]`, almost surely
`E_s[n_t(B + M)_t − n_s(B + M)_s] = −E_s∫_s^t (Λ_rs_r + (i_r − i^m_r)n_rM_r) dr`.
Continuous-time form of `TidyR6StochasticDrift.incr_1_34`. -/
theorem incr_1_34 (hst : s ≤ t) (hd : Dominated μ A N s t (addProc B M) (disc Λ P)) :
    μ[fun ω => disc Λ P t ω * addProc B M t ω - disc Λ P s ω * addProc B M s ω | 𝓕 s] =ᵐ[μ]
      μ[fun ω => -∫ r in s..t, (Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω)
        | 𝓕 s] := by
  have hpd := hm.productStepData_W hst hd
  have h := hpd.product_step
  have i1 := hpd.integrable_intXB
  have i2 := hpd.integrable_intBA
  rw [← hm.disc_eq] at h i1
  have eL : (fun ω => addProc B M t ω * disc Λ P t ω - addProc B M s ω * disc Λ P s ω) =
      fun ω => disc Λ P t ω * addProc B M t ω - disc Λ P s ω * addProc B M s ω :=
    funext fun ω => by ring
  have eR : (fun ω => -∫ r in s..t,
        (Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω)) =
      intRS s t (disc Λ P) (addProc B M) + intRS s t (addProc B M) A :=
    funext fun ω => (hm.pathwise_1_34 ω hst).symm
  rw [eL] at h
  rw [eR]
  filter_upwards [h, condExp_add i1 i2 (𝓕 s)] with ω h1 h2
  rw [h1, h2]

/-- **Cochrane (2023), A1 §1.6, p. 567: `E_t d(Λ(M + B)/P) = −Λ(s + (i − i^m)M/P) dt` as a
`TidyR6StochasticDrift.HasDrift` instance.** If the domination conditions for `B + M` hold on
every `[s, t]`, then `n(B + M)` has drift `−(Λs + (i − i^m)nM)`. -/
theorem hasDrift_1_34 (hd : ∀ s t, s ≤ t → Dominated μ A N s t (addProc B M) (disc Λ P)) :
    TidyR6StochasticDrift.HasDrift μ 𝓕 (fun t ω => disc Λ P t ω * addProc B M t ω)
      fun r ω => -(Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω) := by
  have key : ∀ s t, s ≤ t → (fun ω => disc Λ P t ω * addProc B M t ω -
      disc Λ P s ω * addProc B M s ω - ∫ r in s..t,
        -(Λ r ω * sp r ω + (i r ω - im r ω) * disc Λ P r ω * M r ω)) =
      (fun ω => addProc B M t ω * disc Λ P t ω - addProc B M s ω * disc Λ P s ω) -
        (intRS s t (disc Λ P) (addProc B M) + intRS s t (addProc B M) A) :=
    fun s t hst => funext fun ω => by
      simp only [Pi.sub_apply, Pi.add_apply, intRS]
      rw [intervalIntegral.integral_neg, ← hm.pathwise_1_34 ω hst]
      ring
  have facts : ∀ s t, s ≤ t →
      Integrable (fun ω => addProc B M t ω * disc Λ P t ω - addProc B M s ω * disc Λ P s ω) μ ∧
      Integrable (intRS s t (disc Λ P) (addProc B M)) μ ∧
      Integrable (intRS s t (addProc B M) A) μ ∧
      μ[fun ω => addProc B M t ω * disc Λ P t ω - addProc B M s ω * disc Λ P s ω | 𝓕 s] =ᵐ[μ]
        μ[intRS s t (disc Λ P) (addProc B M) | 𝓕 s] + μ[intRS s t (addProc B M) A | 𝓕 s] := by
    intro s t hst
    have hpd := hm.productStepData_W hst (hd s t hst)
    have i0 := hpd.integrable_lhs
    have i1 := hpd.integrable_intXB
    have h := hpd.product_step
    rw [← hm.disc_eq] at i0 i1 h
    exact ⟨i0, i1, hpd.integrable_intBA, h⟩
  refine ⟨fun s t hst => ?_, fun s t hst => ?_⟩
  · obtain ⟨i0, i1, i2, -⟩ := facts s t hst
    rw [key s t hst]
    exact i0.sub (i1.add i2)
  · obtain ⟨i0, i1, i2, h⟩ := facts s t hst
    rw [key s t hst]
    filter_upwards [condExp_sub i0 (i1.add i2) (𝓕 s), h, condExp_add i1 i2 (𝓕 s)] with
      ω h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [h2, h3, sub_self]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567, as a `TidyR6StochasticDrift.HasDrift` instance
when money has a density.** If `M_v − M_u = ∫_u^v m` (`m` locally integrable) and the domination
conditions for `B` hold on every `[s, t]`, then `nB` has drift `−(Λs − i^m nM + n m)`:
`E_t d(ΛB/P) = −Λ(s + Ṁ/P) dt` when `i^m = 0`.
Generalises `TidyR6StochasticDrift.drift_1_32_fv`. -/
theorem hasDrift_1_32_ac {m : ℝ → Ω → ℝ} (hM : IncrOf M m) (hMi : LocInt m)
    (hd : ∀ s t, s ≤ t → Dominated μ A N s t B (disc Λ P)) :
    TidyR6StochasticDrift.HasDrift μ 𝓕 (fun t ω => disc Λ P t ω * B t ω)
      fun r ω => -(Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω + disc Λ P r ω * m r ω) := by
  have key : ∀ s t, s ≤ t → (fun ω => disc Λ P t ω * B t ω - disc Λ P s ω * B s ω -
      ∫ r in s..t, -(Λ r ω * sp r ω - im r ω * disc Λ P r ω * M r ω + disc Λ P r ω * m r ω)) =
      (fun ω => B t ω * disc Λ P t ω - B s ω * disc Λ P s ω) -
        (intRS s t (disc Λ P) B + intRS s t B A) :=
    fun s t hst => funext fun ω => by
      have hpw := hm.pathwise_1_32 ω hst
      rw [rsInt_eq_integral_of_incr (hm.disc_cadlag ω) (hMi ω) (hM ω) hst] at hpw
      simp only [Pi.sub_apply, Pi.add_apply, intRS]
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_add
        (hm.intervalIntegrable_1_32 ω hst)
        (intervalIntegrable_mul_of_isCadlag (hm.disc_cadlag ω) hst (hMi ω s t)), hpw]
      ring
  have facts : ∀ s t, s ≤ t →
      Integrable (fun ω => B t ω * disc Λ P t ω - B s ω * disc Λ P s ω) μ ∧
      Integrable (intRS s t (disc Λ P) B) μ ∧ Integrable (intRS s t B A) μ ∧
      μ[fun ω => B t ω * disc Λ P t ω - B s ω * disc Λ P s ω | 𝓕 s] =ᵐ[μ]
        μ[intRS s t (disc Λ P) B | 𝓕 s] + μ[intRS s t B A | 𝓕 s] := by
    intro s t hst
    have hpd := hm.productStepData_B hst (hd s t hst)
    have i0 := hpd.integrable_lhs
    have i1 := hpd.integrable_intXB
    have h := hpd.product_step
    rw [← hm.disc_eq] at i0 i1 h
    exact ⟨i0, i1, hpd.integrable_intBA, h⟩
  refine ⟨fun s t hst => ?_, fun s t hst => ?_⟩
  · obtain ⟨i0, i1, i2, -⟩ := facts s t hst
    rw [key s t hst]
    exact i0.sub (i1.add i2)
  · obtain ⟨i0, i1, i2, h⟩ := facts s t hst
    rw [key s t hst]
    filter_upwards [condExp_sub i0 (i1.add i2) (𝓕 s), h, condExp_add i1 i2 (𝓕 s)] with
      ω h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [h2, h3, sub_self]

end MonetaryModel

end Cochrane.Monetarism.TidyR7MonetarismModel
