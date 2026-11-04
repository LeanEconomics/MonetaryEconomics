/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6ActiveFiscalMeasure

/-!
# Active fiscal policy on a probability space: bonds and existence

Cochrane (2023), *The Fiscal Theory of the Price Level*, Ch. 19, §19.5, pp. 448–454 (the
valuation equation (19.35), p. 450; "active fiscal policy can rule out these multiple
equilibria", p. 454), on a genuine probability space (`ExpectationsMeasure`).

## Main results

* `stdBondPriceM_pos`: `q_t = E_t[βM_t/M_{t+1}] > 0` almost surely (a conditional expectation of
  a strictly positive variable).
* `meas_bonds_unique`: under the hypotheses of
  `TidyR6ActiveFiscalMeasure.meas_unique_of_standard`, bonds are unique too: `B_t = B^s_t`
  almost surely at every date (the flow budget pins them forward from `B_{−1}` once prices and
  `Q = q > 0` are pinned).
* `CoordinatedM`, `meas_std_exists_iff`: with `x = E_t Σ_jβ^j(s_{t+j} + (1 − q_{t+j})y/V)`
  (`ExpectationsMeasure.MeasExpectationSystem.forwardSol`), a standard equilibrium with bounded
  real liabilities and initial bonds `B_{−1}` exists iff `q_t ≤ 1` a.s., `M_{t+1}x_{t+1}` is
  a.e. `𝓕_t`-measurable, and `B_{−1} + M_{−1} = (M_0V/y)x_0` a.s.

The restriction to bounded real liabilities in the existence statement is needed because
`MeasMonetaryEq` imposes the transversality condition only in unconditional expectation,
`E[β^Tx_T] → 0`: that admits mean-zero exploding bubbles in real liabilities. Bounded debt is
the probability-space analogue of the conditional transversality conditions of
`TidyR6ActiveFiscalTree.StochMonetaryEq`, under which `TidyR6ActiveFiscalExist.std_exists_iff`
needs no boundedness.
-/

namespace Cochrane.Monetarism.TidyR6ActiveFiscalMeasureExist

open MeasureTheory Filter Topology
open Cochrane.Monetarism.ExpectationsMeasure
open Cochrane.Monetarism.TidyR6ActiveFiscalTree (stdPrice wealth)
open Cochrane.Monetarism.TidyR6ActiveFiscalMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}
variable {β y V : ℝ} {P Bin Min s : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 454: with positive money, `β > 0` and `βM_t/M_{t+1}` integrable, the
standard bond price `q_t` is strictly positive almost surely. -/
theorem stdBondPriceM_pos (hβ : 0 < β) (hM : ∀ t ω, 0 < Min (t + 1) ω) (t : ℕ)
    (hq : Integrable (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) S.μ) :
    ∀ᵐ ω ∂S.μ, 0 < stdBondPriceM S β Min t ω := by
  set f : Ω → ℝ := fun ω => β * Min (t + 1) ω / Min (t + 2) ω with hf
  have hfpos : ∀ ω, 0 < f ω := fun ω => by
    have := hM t ω; have := hM (t + 1) ω; simp only [hf]; positivity
  have hqm : StronglyMeasurable[S.𝓕 t] (stdBondPriceM S β Min t) := S.stronglyMeasurable_E t _
  set A := {ω | stdBondPriceM S β Min t ω ≤ 0} with hA
  have hAm : MeasurableSet[S.𝓕 t] A := measurableSet_le hqm.measurable measurable_const
  have hAm0 : MeasurableSet A := S.𝓕.le t _ hAm
  have h1 : ∫ ω in A, stdBondPriceM S β Min t ω ∂S.μ = ∫ ω in A, f ω ∂S.μ :=
    setIntegral_condExp (S.𝓕.le t) hq hAm
  have h2 : ∫ ω in A, stdBondPriceM S β Min t ω ∂S.μ ≤ 0 :=
    setIntegral_nonpos hAm0 fun ω hω => hω
  have hμA : S.μ A = 0 := by
    by_contra hne
    have hpos : 0 < ∫ ω in A, f ω ∂S.μ := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        (ae_of_all _ fun ω => (hfpos ω).le) hq.integrableOn]
      have : Function.support f ∩ A = A := by
        ext ω; simp [Function.mem_support, (hfpos ω).ne']
      rw [this]; exact pos_iff_ne_zero.mpr hne
    linarith
  rw [ae_iff]
  simpa [hA, not_lt] using hμA

/-- **Cochrane (2023), pp. 453–454 on a probability space: bonds are unique too.** Under the
hypotheses of `TidyR6ActiveFiscalMeasure.meas_unique_of_standard`, every equilibrium has the
standard bonds almost surely at every date. -/
theorem meas_bonds_unique (hβ : 0 < β) (hy : 0 < y) (hV : 0 < V) {Bs : ℕ → Ω → ℝ}
    (h : MeasMonetaryEq S β y V P Bin Min s)
    (hstd : MeasMonetaryEq S β y V (stdPrice y V Min) Bs Min s)
    (hs : ∀ t, Integrable (s t) S.μ) (hB0 : Bin 0 = Bs 0)
    (hW : ∀ᵐ ω ∂S.μ, 0 ≤ Bin 0 ω + Min 0 ω)
    (hpin : ∀ᵐ ω ∂S.μ, 0 < Bin 0 ω + Min 0 ω ∨ stdBondPriceM S β Min 0 ω < 1) :
    ∀ t, Bin t =ᵐ[S.μ] Bs t := by
  obtain ⟨hP, hQ⟩ := meas_unique_of_standard hβ hy hV h hstd hs hB0 hW hpin
  have hMp := money_pos_of_std hy hV hstd
  have hQs := bondPriceM_std (S := S) (β := β) hy hV hMp
  have hqint : ∀ t, Integrable (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) S.μ := by
    intro t
    refine (hstd.intQ t).congr (ae_of_all _ fun ω => ?_)
    have := (hMp (t + 1) ω).ne'
    have := hy.ne'
    have := hV.ne'
    change β * (Min (t + 1) ω * V / y) / (Min (t + 1 + 1) ω * V / y) =
      β * Min (t + 1) ω / Min (t + 2) ω
    field_simp
  intro t
  induction t with
  | zero => rw [hB0]
  | succ t ih =>
    filter_upwards [ih, h.flow t, hstd.flow t, hP t, hQ t,
      stdBondPriceM_pos hβ hMp t (hqint t)] with ω e0 f1 f2 eP eQ hq
    rw [hQs t] at f2
    rw [eQ, eP, e0] at f1
    have : stdBondPriceM S β Min t ω * (Bin (t + 1) ω - Bs (t + 1) ω) = 0 := by
      linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hq.ne')

/-! ## Existence of the standard equilibrium -/

/-- Cochrane (2023), (19.35), p. 450, on a probability space: the forward valuation along the
standard path, `x_t = E_t Σ_jβ^j(s_{t+j} + (1 − q_{t+j})y/V)`.
Probability-space version of `TidyR6ActiveFiscalExist.stdValue`. -/
noncomputable def stdValueM (S : MeasExpectationSystem Ω) (β y V : ℝ) (Min s : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  S.forwardSol β (stdFlowM S β y V Min s)

/-- Cochrane (2023), pp. 453–454, on a probability space: **the surplus is coordinated with
money**: `q_t ≤ 1` a.s., `M_{t+1}x_{t+1}` a.e. `𝓕_t`-measurable, and
`B_{−1} + M_{−1} = (M_0V/y)x_0` a.s.
Probability-space version of `TidyR6ActiveFiscalExist.Coordinated`. -/
def CoordinatedM (S : MeasExpectationSystem Ω) (β y V : ℝ) (B0 : Ω → ℝ)
    (Min s : ℕ → Ω → ℝ) : Prop :=
  (∀ t, ∀ᵐ ω ∂S.μ, stdBondPriceM S β Min t ω ≤ 1) ∧
    (∀ t, AEStronglyMeasurable[S.𝓕 t]
      (fun ω => Min (t + 2) ω * stdValueM S β y V Min s (t + 1) ω) S.μ) ∧
    ∀ᵐ ω ∂S.μ, B0 ω + Min 0 ω = Min 1 ω * V / y * stdValueM S β y V Min s 0 ω

/-- Cochrane (2023), (19.35), p. 450: the standard flow is adapted when the surplus is.
Probability-space version of `TidyR6ActiveFiscalExist.stdU_adapted`. -/
theorem stdFlowM_adapted (hs : StronglyAdapted S.𝓕 s) :
    StronglyAdapted S.𝓕 (stdFlowM S β y V Min s) := fun t =>
  (hs t).add ((((stronglyMeasurable_const.sub (S.stronglyMeasurable_E t _)).mul_const
    y).measurable.div_const V).stronglyMeasurable)

/-- Cochrane (2023), (19.35), p. 450: with `|s| ≤ S₀` a.s. and `0 < q ≤ 1` a.s., the standard
flow is bounded by `S₀ + y/V` a.s.
Probability-space version of `TidyR6ActiveFiscalExist.stdU_bound`. -/
theorem stdFlowM_bdd (hβ : 0 < β) (hy : 0 < y) (hV : 0 < V) (hM : ∀ t ω, 0 < Min (t + 1) ω)
    (hq : ∀ t, Integrable (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) S.μ)
    (hq1 : ∀ t, ∀ᵐ ω ∂S.μ, stdBondPriceM S β Min t ω ≤ 1) {S0 : ℝ}
    (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ S0) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |stdFlowM S β y V Min s t ω| ≤ S0 + y / V := by
  filter_upwards [hq1 t, hsb t, stdBondPriceM_pos hβ hM t (hq t)] with ω h1 h2 h0
  have hyV : 0 < y / V := div_pos hy hV
  have e : (1 - stdBondPriceM S β Min t ω) * y / V = (1 - stdBondPriceM S β Min t ω) * (y / V) :=
    by ring
  simp only [stdFlowM]
  rw [e]
  have h3 : |(1 - stdBondPriceM S β Min t ω) * (y / V)| ≤ y / V := by
    rw [abs_mul, abs_of_pos hyV, abs_of_nonneg (by linarith)]
    nlinarith
  calc |s t ω + (1 - stdBondPriceM S β Min t ω) * (y / V)|
      ≤ |s t ω| + |(1 - stdBondPriceM S β Min t ω) * (y / V)| := abs_add_le _ _
    _ ≤ S0 + y / V := add_le_add h2 h3

/-- Cochrane (2023), (19.27)–(19.35), pp. 449–450, conditionally and almost surely: in an
equilibrium, `x_t = βE_t x_{t+1} + s_t + (1 − Q_t)y/V`.
Probability-space version of `TidyR6ActiveFiscalTree.wealth_recursion`. -/
theorem wealth_rec_ae (hV : 0 < V) (h : MeasMonetaryEq S β y V P Bin Min s) (t : ℕ) :
    wealth P Bin Min t =ᵐ[S.μ]
      β • S.E t (wealth P Bin Min (t + 1)) + flowM S β y V P s t := by
  set K : Ω → ℝ := fun ω => Bin (t + 1) ω + Min (t + 1) ω with hK
  set R : Ω → ℝ := fun ω => β / P (t + 1) ω with hR
  have hKm : StronglyMeasurable[S.𝓕 t] K := (h.measB t).add (h.measM t)
  have hKR : K * R = β • wealth P Bin Min (t + 1) := by
    funext ω
    have := (h.pos (t + 1) ω).ne'
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hK, hR, wealth]
    field_simp
  have hKRi : Integrable (K * R) S.μ := by rw [hKR]; exact (h.intW (t + 1)).smul β
  have h1 : S.E t (K * R) =ᵐ[S.μ] K * S.E t R :=
    condExp_mul_of_stronglyMeasurable_left hKm hKRi (h.intR t)
  have h2 := bondPriceM_ae h t
  have h3 := S.E_smul β (wealth P Bin Min (t + 1)) t
  rw [← hKR] at h3
  filter_upwards [h1, h2, h.flow t, h.money t, h3] with ω e1 e2 hf hm e3
  simp only [Pi.mul_apply] at e1 e2
  simp only [Pi.add_apply]
  rw [← e3, e1]
  have hP := (h.pos t ω).ne'
  have hsg : (1 - bondPriceM S β P t ω) * Min (t + 1) ω =
      (1 - bondPriceM S β P t ω) * (P t ω * y / V) := by
    rcases lt_or_eq_of_le hm.1 with hQ | hQ
    · rw [hm.2 hQ]
    · rw [hQ, sub_self, zero_mul, zero_mul]
  have hER : S.E t R ω = bondPriceM S β P t ω / P t ω := by rw [e2, hR]; field_simp
  simp only [wealth, flowM]
  rw [hER, hf]
  have e4 : bondPriceM S β P t ω * Bin (t + 1) ω + Min (t + 1) ω + P t ω * s t ω =
      (Bin (t + 1) ω + Min (t + 1) ω) * bondPriceM S β P t ω +
        (1 - bondPriceM S β P t ω) * Min (t + 1) ω + P t ω * s t ω := by ring
  rw [e4, hsg]
  have := hV.ne'
  simp only [hK]
  field_simp
  ring

/-- **Cochrane (2023), pp. 448–454 on a probability space: existence of the standard
equilibrium.** Let `0 < β < 1`, `y, V > 0`, money positive and adapted with `β/M_{t+1}` and
`βM_t/M_{t+1}` integrable, surpluses adapted and essentially bounded. A standard equilibrium
(`P_t = M_tV/y`) with initial bonds `B_{−1}` and bounded real liabilities exists iff the surplus
is coordinated with money (`CoordinatedM`).
Probability-space version of `TidyR6ActiveFiscalExist.std_exists_iff`. -/
theorem meas_std_exists_iff (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    (hM : ∀ t ω, 0 < Min (t + 1) ω) (hMm : ∀ t, StronglyMeasurable[S.𝓕 t] (Min (t + 1)))
    (hS : ∀ t, Integrable (fun ω => β / Min (t + 2) ω) S.μ)
    (hq : ∀ t, Integrable (fun ω => β * Min (t + 1) ω / Min (t + 2) ω) S.μ)
    (hs : StronglyAdapted S.𝓕 s) {S0 : ℝ} (hsb : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ S0)
    (B0 : Ω → ℝ) :
    (∃ Bs : ℕ → Ω → ℝ, Bs 0 = B0 ∧ MeasMonetaryEq S β y V (stdPrice y V Min) Bs Min s ∧
      S.BddProc fun t => wealth (stdPrice y V Min) Bs Min t) ↔
      CoordinatedM S β y V B0 Min s := by
  have hQs := bondPriceM_std (S := S) (β := β) hy hV hM
  have habs : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hflow : ∀ t, flowM S β y V (stdPrice y V Min) s t = stdFlowM S β y V Min s t :=
    fun t => by funext ω; simp only [flowM, stdFlowM, hQs t]
  constructor
  · rintro ⟨Bs, hB0, h, hbdd⟩
    have hq1 : ∀ t, ∀ᵐ ω ∂S.μ, stdBondPriceM S β Min t ω ≤ 1 := fun t => by
      filter_upwards [h.money t] with ω hω
      rw [← hQs t]; exact hω.1
    have hub := stdFlowM_bdd hβ0 hy hV hM hq hq1 hsb
    have hw : S.Solves β (stdFlowM S β y V Min s) fun t => wealth (stdPrice y V Min) Bs Min t :=
      fun t => by
        have := wealth_rec_ae hV h t
        rwa [hflow t] at this
    have hx := S.forwardSol_solves habs (stdFlowM_adapted hs) hub
    have huniq := S.forward_unique habs hw hx (fun t => (h.intW t).1)
      (fun t => (S.integrable_E t _).1) hbdd (S.forwardSol_bdd habs hub)
    refine ⟨hq1, fun t => ?_, ?_⟩
    · have hgm : StronglyMeasurable[S.𝓕 t] fun ω => (Bs (t + 1) ω + Min (t + 1) ω) * y / V :=
        ((((h.measB t).add (hMm t)).mul_const y).measurable.div_const V).stronglyMeasurable
      refine ⟨_, hgm, ?_⟩
      filter_upwards [huniq (t + 1)] with ω hω
      have := (hM (t + 1) ω).ne'
      have := hy.ne'
      have := hV.ne'
      simp only [stdValueM]
      rw [← hω]
      simp only [wealth, stdPrice]
      field_simp
    · filter_upwards [huniq 0] with ω hω
      have := (hM 0 ω).ne'
      have := hy.ne'
      have := hV.ne'
      simp only [stdValueM]
      rw [← hω]
      simp only [wealth, stdPrice, zero_add, hB0]
      field_simp
  · rintro ⟨hq1, hii, hiii⟩
    have hub := stdFlowM_bdd hβ0 hy hV hM hq hq1 hsb
    set x := stdValueM S β y V Min s with hx
    have hxs : S.Solves β (stdFlowM S β y V Min s) x :=
      S.forwardSol_solves habs (stdFlowM_adapted hs) hub
    obtain ⟨C, hC⟩ := S.forwardSol_bdd habs hub
    have hxi : ∀ t, Integrable (x t) S.μ := fun t => S.integrable_E t _
    set G : ℕ → Ω → ℝ := fun k => (hii k).mk _ with hG
    have hGm : ∀ k, StronglyMeasurable[S.𝓕 k] (G k) := fun k => (hii k).stronglyMeasurable_mk
    have hGeq : ∀ k, (fun ω => Min (k + 2) ω * x (k + 1) ω) =ᵐ[S.μ] G k :=
      fun k => (hii k).ae_eq_mk
    set Bs : ℕ → Ω → ℝ := fun t ω =>
      if t = 0 then B0 ω else V / y * G (t - 1) ω - Min t ω with hBs
    have hB1 : ∀ k, Bs (k + 1) = fun ω => V / y * G k ω - Min (k + 1) ω :=
      fun k => by funext ω; simp [hBs]
    have hkey : ∀ t, ∀ᵐ ω ∂S.μ, Bs t ω + Min t ω = Min (t + 1) ω * V / y * x t ω := by
      intro t
      rcases t with _ | k
      · filter_upwards [hiii] with ω hω
        simp only [hBs, ↓reduceIte]; exact hω
      · filter_upwards [hGeq k] with ω hω
        rw [hB1 k]
        simp only at hω ⊢
        rw [← hω]; ring
    have hwealth : ∀ t, (fun ω => wealth (stdPrice y V Min) Bs Min t ω) =ᵐ[S.μ] x t := by
      intro t
      filter_upwards [hkey t] with ω hω
      have := (hM t ω).ne'
      have := hy.ne'
      have := hV.ne'
      simp only [wealth, stdPrice, hω]
      field_simp
    refine ⟨Bs, by simp [hBs], ⟨fun t ω => ?_, fun t => ?_, fun t => ?_, hMm, fun t => ?_,
      fun t => ?_, fun t => ((hxi t).congr (hwealth t).symm), fun t => ae_of_all _ fun ω => ?_,
      fun t => ?_, fun t => ?_, ?_⟩, ⟨C, fun t => ?_⟩⟩
    · have := hM t ω; simp only [stdPrice]; positivity
    · exact (((hMm t).mul_const V).measurable.div_const y).stronglyMeasurable
    · rw [hB1 t]; exact ((hGm t).const_mul (V / y)).sub (hMm t)
    · refine ((hS t).const_mul (y / V)).congr (ae_of_all _ fun ω => ?_)
      have := (hM (t + 1) ω).ne'
      have := hy.ne'
      have := hV.ne'
      change y / V * (β / Min (t + 2) ω) = β / (Min (t + 1 + 1) ω * V / y)
      field_simp
    · refine (hq t).congr (ae_of_all _ fun ω => ?_)
      have := (hM (t + 1) ω).ne'
      have := hy.ne'
      have := hV.ne'
      change β * Min (t + 1) ω / Min (t + 2) ω =
        β * (Min (t + 1) ω * V / y) / (Min (t + 1 + 1) ω * V / y)
      field_simp
    · simp only [stdPrice]; have := hy.ne'; have := hV.ne'; field_simp; rfl
    · filter_upwards [hq1 t] with ω hω
      refine ⟨by rw [hQs t]; exact hω, fun _ => ?_⟩
      simp only [stdPrice]; have := hy.ne'; have := hV.ne'; field_simp
    · -- the flow budget
      set K : Ω → ℝ := fun ω => V / y * G t ω with hK
      set R : Ω → ℝ := fun ω => 1 / Min (t + 2) ω with hR
      have hKm : StronglyMeasurable[S.𝓕 t] K := (hGm t).const_mul (V / y)
      have hRi : Integrable R S.μ := by
        refine ((hS t).const_mul β⁻¹).congr (ae_of_all _ fun ω => ?_)
        simp only [hR]; field_simp
      have hxKR : x (t + 1) =ᵐ[S.μ] (y / V) • (K * R) := by
        filter_upwards [hGeq t] with ω hω
        have := (hM (t + 1) ω).ne'
        have := hy.ne'
        have := hV.ne'
        simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hK, hR]
        rw [← hω]
        field_simp
      have hKRi : Integrable (K * R) S.μ := by
        refine ((hxi (t + 1)).const_mul (V / y)).congr ?_
        filter_upwards [hxKR] with ω hω
        rw [hω]
        simp only [Pi.smul_apply, smul_eq_mul]
        have := hy.ne'
        have := hV.ne'
        field_simp
      have hpull : S.E t (K * R) =ᵐ[S.μ] K * S.E t R :=
        condExp_mul_of_stronglyMeasurable_left hKm hKRi hRi
      have hEx1 := S.E_congr hxKR t
      have hEx2 := S.E_smul (y / V) (K * R) t
      have hq' := stdBondPriceM_ae (hMm) (hS t) (hq t)
      have hsm := S.E_smul β R t
      have heR : (fun ω => β / Min (t + 2) ω) = β • R := by
        funext ω; simp only [hR, Pi.smul_apply, smul_eq_mul]; ring
      rw [← heR] at hsm
      filter_upwards [hkey t, hxs t, hEx1, hEx2, hpull, hq', hsm] with ω e0 e1 e2 e3 e4 e5 e6
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at e1 e2 e3 e4 e5 e6
      rw [hQs t, e0, e1, e2, e3, e4, hB1 t]
      simp only [stdFlowM, stdPrice]
      rw [e5, e6]
      simp only [hK]
      have := hy.ne'
      have := hV.ne'
      field_simp
      ring
    · -- the transversality condition
      have hbd : ∀ T, |∫ ω, β ^ T * wealth (stdPrice y V Min) Bs Min T ω ∂S.μ| ≤ β ^ T * C := by
        intro T
        rw [integral_const_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le _)]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le _)
        refine (abs_integral_le_integral_abs).trans ?_
        have : ∫ ω, |wealth (stdPrice y V Min) Bs Min T ω| ∂S.μ ≤ ∫ _ω, C ∂S.μ :=
          integral_mono_ae ((hxi T).congr (hwealth T).symm).abs (integrable_const C)
            (by filter_upwards [hwealth T, hC T] with ω h1 h2; rw [h1]; exact h2)
        simpa using this
      have hlim : Tendsto (fun T => β ^ T * C) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const C
      exact squeeze_zero_norm (fun T => by rw [Real.norm_eq_abs]; exact hbd T) hlim
    · filter_upwards [hwealth t, hC t] with ω h1 h2
      rw [h1]; exact h2

end Cochrane.Monetarism.TidyR6ActiveFiscalMeasureExist
