/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.Links
import IntertemporalModel.FlatSupply
import IntertemporalModel.EquilibriumFormation

/-!
# Links among the Chapter 2 formalisations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.1–§2.6 and §2.9
(pp. 21–42, 47–49). The chapter is formalised three ways: `Valuation` derives the valuation
equation from the flow condition and the transversality condition (`Valuation.IsEqm`, debt
indexed by maturity date `Bm t = B_{t−1}`, bond price `Q`); `FiscalMonetary` takes the valuation
equation as the definition of equilibrium (`FiscalMonetary.Equilibrium`, debt indexed by issue
date `B t = B_t`, nominal rate `i`); `LinearFTMP` and `Links` study the exact Fisher equation and
the linear model. This module proves that they describe the same economics.

## Main results

* Present values: `fm_pv_eq_pv` (the ex-post form `E_t ∑ βʲ s_{t+j}` of `FiscalMonetary.pv`
  equals `Valuation.pv = ∑ βʲ E_t s_{t+j}` under conditional monotone convergence and ex-post
  absolute summability), `fm_pv_eq_pv_of_bounded` (bounded surpluses, any expectation system).
* Equilibrium: `equilibrium_iff_isEqm`: an equilibrium in the sense of `FiscalMonetary`
  (valuation equation plus bond pricing) is exactly an equilibrium in the sense of `Valuation`
  (flow condition (2.4), bond price (2.3), transversality condition (2.6)) with maturing debt
  `debtPath B_{−1} B` and bond price `Q = 1/(1 + i)`; so every result of `FiscalMonetary` and
  `FlatSupply` is about the equilibria derived in `Valuation`. Consequences:
  `equilibrium_price_eq_eqmPrice`, `peg_existsUnique_isEqm` (an interest-rate target selects
  exactly one derived equilibrium), `equilibrium_realRevenue` ((2.14)–(2.15) is (2.11)),
  `twoStep_eq_debtPath`.
* `bondPricing_iff_fisherExact`, `equilibrium_iff_pegEqm`: the bond-pricing condition is the
  exact Fisher equation of `LinearFTMP`, and `Links.PegEqm` with `PV = FiscalMonetary.pv` is
  `FiscalMonetary.Equilibrium`; `ftplPrice_eq_pegP`, `ftplDebt_eq_pegB`: the two peg
  equilibria constructed in `Links` and `FiscalMonetary` coincide.
* The linear model as the derivative of the nonlinear one: `isEqm_fisherExact` and
  `isEqm_fisher_log` (every derived equilibrium satisfies the exact Fisher equation in logs,
  whose derivative at the steady state is `LinearFTMP.fisher_deriv`, the linear (2.16));
  `innov_epv_eq_pvNews` and `equilibrium_pvNews` (the exact (2.13) of every equilibrium is the
  exact (2.17), with the fiscal shock `ε_{Σs}` of `LinearFTMP`, whose derivative is
  `LinearFTMP.linear_217`); `equilibrium_debt_218` ((2.18) in every equilibrium).
-/

namespace Cochrane.IntertemporalModel.GeneralLinks

open Filter Topology ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Present values -/

/-- Cochrane (2023), eq. (2.7), p. 22: the two forms of the present value agree,
`E_t ∑_j βʲ s_{t+j} = ∑_j βʲ E_t s_{t+j}`, under conditional monotone convergence when the
ex-post discounted sum converges absolutely in every state (signed surpluses: split into
positive and negative parts). -/
theorem fm_pv_eq_pv (hMC : MonotoneConvergence 𝔼) {β : ℝ} (hβ : 0 ≤ β) {s : ℕ → Ω → ℝ}
    {t : ℕ} (hex : ∀ ω, Summable fun j => β ^ j * |s (t + j) ω|) :
    FiscalMonetary.pv 𝔼 β s t = Valuation.pv 𝔼 β s t := by
  funext ω
  set sp : ℕ → Ω → ℝ := fun n ω => max (s n ω) 0 with hsp
  set sn : ℕ → Ω → ℝ := fun n ω => max (-s n ω) 0 with hsn
  have hsplit : ∀ n, s n = sp n - sn n := fun n => by
    funext ω
    simp [hsp, hsn, max_zero_sub_max_neg_zero_eq_self]
  have hpart : ∀ r : ℕ → Ω → ℝ, (∀ n ω, 0 ≤ r n ω) → (∀ n ω, r n ω ≤ |s n ω|) →
      (∀ ω', Summable fun j => β ^ j * r (t + j) ω') ∧
      HasSum (fun j => β ^ j * 𝔼.E t (r (t + j)) ω)
        (𝔼.E t (fun ω' => ∑' j, β ^ j * r (t + j) ω') ω) := by
    intro r hr0 hrs
    have hf0 : ∀ k ω', 0 ≤ β ^ k * r (t + k) ω' := fun k ω' =>
      mul_nonneg (pow_nonneg hβ k) (hr0 _ _)
    have hfs : ∀ ω', Summable fun k => β ^ k * r (t + k) ω' := fun ω' =>
      Summable.of_nonneg_of_le (fun k => hf0 k ω')
        (fun k => mul_le_mul_of_nonneg_left (hrs _ _) (pow_nonneg hβ k)) (hex ω')
    refine ⟨hfs, (hMC t (fun k ω' => β ^ k * r (t + k) ω') hf0 hfs ω).congr_fun fun j => ?_⟩
    change β ^ j * 𝔼.E t (r (t + j)) ω = 𝔼.E t (β ^ j • r (t + j)) ω
    rw [map_smul]
    rfl
  have hp := hpart sp (fun n ω => le_max_right _ _)
    (fun n ω => max_le (le_abs_self _) (abs_nonneg _))
  have hn := hpart sn (fun n ω => le_max_right _ _)
    (fun n ω => max_le (neg_le_abs _) (abs_nonneg _))
  have hepv : FiscalMonetary.epv β s t = (fun ω' => ∑' j, β ^ j * sp (t + j) ω') -
      (fun ω' => ∑' j, β ^ j * sn (t + j) ω') := by
    funext ω'
    simp only [FiscalMonetary.epv, Pi.sub_apply]
    rw [← (hp.1 ω').tsum_sub (hn.1 ω')]
    refine tsum_congr fun j => ?_
    rw [hsplit (t + j), Pi.sub_apply]
    ring
  change 𝔼.E t (FiscalMonetary.epv β s t) ω = ∑' j, β ^ j * 𝔼.E t (s (t + j)) ω
  rw [hepv, map_sub, Pi.sub_apply, ← hp.2.tsum_eq, ← hn.2.tsum_eq,
    ← hp.2.summable.tsum_sub hn.2.summable]
  refine tsum_congr fun j => ?_
  rw [hsplit (t + j), map_sub, Pi.sub_apply]
  ring

/-- Cochrane (2023), eq. (2.7), p. 22: for bounded surpluses and `0 ≤ β < 1` the two forms of
the present value agree for every expectation system (no monotone convergence needed). -/
theorem fm_pv_eq_pv_of_bounded {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) : FiscalMonetary.pv 𝔼 β s t = Valuation.pv 𝔼 β s t :=
  funext fun ω => FiscalMonetary.E_epv_tsum (𝔼 := 𝔼) hβ0 hβ1 hs t t ω

/-! ### The two equilibrium notions -/

/-- Cochrane (2023), §2.1, p. 21 (timing): the nominal debt maturing at each date, `B_{−1}` at
date `0` and `B_t` at date `t + 1`, built from the initial debt and the debt sold. This is the
`Bm` of `Environment`/`Valuation` (`Bm t = B_{t−1}`) for the `B` of `FiscalMonetary`. -/
def debtPath (Bm1 : Ω → ℝ) (B : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => Bm1
  | t + 1 => B t

/-- Cochrane (2023), §2.1–§2.4, pp. 21–33: the equilibrium of `FiscalMonetary` (valuation
equation (2.7)/(2.12) at every date plus the bond-pricing condition (2.3)) is exactly the
equilibrium of `Valuation` (positive adapted price level, bond price (2.3), flow condition
(2.4) and transversality condition (2.6) at every date), with maturing debt
`debtPath B_{−1} B` and bond price `Q_t = 1/(1 + i_t)`. Hypotheses: pull-out, conditional
monotone convergence, `β ≥ 0`, adapted surpluses that are absolutely summable both in
expectation and ex post, adapted debt sold and an adapted rate `i > −1`. So the results of
`FiscalMonetary` and `FlatSupply` are about the equilibria derived from flow plus TVC. -/
theorem equilibrium_iff_isEqm (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : Valuation.AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|)
    (hBa : 𝔼.Adapted B) (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω) :
    FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i ↔
      Valuation.IsEqm 𝔼 β (debtPath Bm1 B) s P (fun t => (1 + i t)⁻¹) := by
  have hpv : ∀ t, FiscalMonetary.pv 𝔼 β s t = Valuation.pv 𝔼 β s t := fun t =>
    fm_pv_eq_pv 𝔼 hMC hβ (hex t)
  have hB1 : ∀ t, 𝔼.E t (debtPath Bm1 B (t + 1)) = debtPath Bm1 B (t + 1) := hBa
  constructor
  · rintro ⟨hPa, hPpos, -, -, -, ⟨hv0, hv⟩, hbp⟩
    have hx : ∀ t, (fun ω => debtPath Bm1 B t ω / P t ω) = Valuation.pv 𝔼 β s t := by
      intro t
      cases t with
      | zero => exact hv0.trans (hpv 0)
      | succ t => exact (hv t).trans (hpv (t + 1))
    obtain ⟨hflow, htvc⟩ := (Valuation.valuation_iff 𝔼 hMC hβ hs hsad).mpr hx
    refine ⟨hPpos, hPa, hbp, fun t ω => ?_, htvc⟩
    exact (Environment.flow_iff_real_x 𝔼 hPO (Q := fun t => (1 + i t)⁻¹) (hPpos t) (hPa t)
      (hB1 t) (hbp t)).mpr (hflow t) ω
  · intro h
    have hx := Valuation.eqm_realDebt_eq_pv 𝔼 hPO hMC hβ hs hsad hB1 h
    exact ⟨h.2.1, h.1, hBa, hia, hi, ⟨(hx 0).trans (hpv 0).symm,
      fun t => (hx (t + 1)).trans (hpv (t + 1)).symm⟩, h.2.2.1⟩

/-- Cochrane (2023), p. 22, "the price level must adjust so that (2.7) holds", for the
equilibria of `FiscalMonetary`: under the hypotheses of `equilibrium_iff_isEqm` and positive
debt, the price level is `Valuation.eqmPrice`, `P_t = B_{t−1}/pv_t`. -/
theorem equilibrium_price_eq_eqmPrice (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼)
    {β : ℝ} (hβ : 0 ≤ β) {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ}
    (hs : Valuation.AbsSummable 𝔼 β s) (hsad : 𝔼.Adapted s)
    (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|) (hBa : 𝔼.Adapted B)
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω) (hBpos : ∀ t ω, 0 < debtPath Bm1 B t ω)
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) :
    P = Valuation.eqmPrice 𝔼 β (debtPath Bm1 B) s := by
  have hA := (equilibrium_iff_isEqm 𝔼 hPO hMC hβ hs hsad hex hBa hia hi).mp h
  funext t ω
  exact Valuation.eqm_price_eq 𝔼 hPO hMC hβ hs hsad (Bm := debtPath Bm1 B) hBa hA
    (hBpos t ω).ne'

/-- Cochrane (2023), pp. 31–33, in the language of `Valuation`: for every adapted
interest-rate target `i > −1` (with positive initial debt and positive present values) there is
exactly one pair (price level, debt sold) such that the debt is adapted and the economy with
maturing debt `debtPath B_{−1} B` and bond price `1/(1 + i)` is an equilibrium derived from
flow plus transversality. -/
theorem peg_existsUnique_isEqm (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm1 : Ω → ℝ} {s i : ℕ → Ω → ℝ} (hs : Valuation.AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|)
    (hBm1 : 𝔼.E 0 Bm1 = Bm1) (hB : ∀ ω, 0 < Bm1 ω) (hia : 𝔼.Adapted i)
    (hi : ∀ t ω, -1 < i t ω) (hpv : ∀ t ω, 0 < FiscalMonetary.pv 𝔼 β s t ω)
    (hpvEx : ∀ t ω, 0 < FiscalMonetary.pvEx 𝔼 β s t ω) :
    ∃! x : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted x.2 ∧
      Valuation.IsEqm 𝔼 β (debtPath Bm1 x.2) s x.1 (fun t => (1 + i t)⁻¹) := by
  obtain ⟨x, hx, hu⟩ := FiscalMonetary.peg_existsUnique hPO hBm1 hB hia hi hpv hpvEx
  refine ⟨x, ⟨hx.2.2.1, (equilibrium_iff_isEqm 𝔼 hPO hMC hβ hs hsad hex hx.2.2.1 hia hi).mp hx⟩,
    fun y hy => hu y ?_⟩
  exact (equilibrium_iff_isEqm 𝔼 hPO hMC hβ hs hsad hex hy.1 hia hi).mpr hy.2

/-- Cochrane (2023), eqs. (2.11) and (2.14)–(2.15), pp. 27, 31: in every equilibrium of
`FiscalMonetary` the real revenue from bond sales `(B_t/P_t)/(1 + i_t)` is the convergent series
`∑_{j≥0} β^{j+1} E_t s_{t+1+j}` of `EquilibriumFormation.eqm_realRevenue`. -/
theorem equilibrium_realRevenue (hPO : 𝔼.PullOut) (hMC : MonotoneConvergence 𝔼) {β : ℝ}
    (hβ : 0 ≤ β) {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : Valuation.AbsSummable 𝔼 β s)
    (hsad : 𝔼.Adapted s) (hex : ∀ t ω, Summable fun j => β ^ j * |s (t + j) ω|)
    (hBa : 𝔼.Adapted B) (hia : 𝔼.Adapted i) (hi : ∀ t ω, -1 < i t ω)
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (s (t + 1 + j)) ω)
      ((B t / P t * (1 + i t)⁻¹) ω) := by
  have hA := (equilibrium_iff_isEqm 𝔼 hPO hMC hβ hs hsad hex hBa hia hi).mp h
  have hr := EquilibriumFormation.eqm_realRevenue 𝔼 hPO hMC hβ hs hsad
    (Bm := debtPath Bm1 B) hBa hA t ω
  convert hr using 1
  simp only [Pi.mul_apply, Pi.div_apply, Pi.inv_apply, Pi.add_apply, Pi.one_apply, debtPath]
  ring

/-- Cochrane (2023), §2.9, p. 48: the nominal debt maturing at each date in the two-step process
(central bank sets `i`, Treasury follows its rule) is the maturing-debt path `Bm` of
`Valuation` built from the debt sold on the flat supply curve. -/
theorem twoStep_eq_debtPath {β : ℝ} {Bm1 : Ω → ℝ} {s i : ℕ → Ω → ℝ}
    (hs : FiscalMonetary.SurplusSummable β s) (hsa : 𝔼.Adapted s)
    (hpv : ∀ t ω, FiscalMonetary.pv 𝔼 β s t ω ≠ 0) :
    FlatSupply.twoStep 𝔼 β Bm1 s i = debtPath Bm1 (FiscalMonetary.pegB 𝔼 β Bm1 s i) := by
  funext t
  cases t with
  | zero => rfl
  | succ t => exact FlatSupply.twoStep_debt_eq_pegB hs hsa hpv t

/-! ### Bond pricing, the exact Fisher equation and the peg equilibria -/

/-- Cochrane (2023), eqs. (2.3) and (2.16), pp. 22, 35: the bond-pricing condition of
`FiscalMonetary` is the exact Fisher equation of `LinearFTMP` at every date. -/
theorem bondPricing_iff_fisherExact {β : ℝ} {P i : ℕ → Ω → ℝ} :
    FiscalMonetary.BondPricing 𝔼 β P i ↔ ∀ t, LinearFTMP.FisherExact 𝔼 β i P t := by
  refine forall_congr' fun t => ?_
  rw [funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.inv_apply, Pi.add_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, one_div]
  exact Iff.rfl

/-- Cochrane (2023), pp. 22, 33: the peg equilibrium `Links.PegEqm` of chain C, with the present
value `FiscalMonetary.pv` and a constant initial debt, is exactly `FiscalMonetary.Equilibrium`
(for an adapted target `i > −1`). -/
theorem equilibrium_iff_pegEqm {β Bm1 : ℝ} {s B P i : ℕ → Ω → ℝ} (hia : 𝔼.Adapted i)
    (hi : ∀ t ω, -1 < i t ω) :
    FiscalMonetary.Equilibrium 𝔼 β (fun _ => Bm1) s B P i ↔
      Links.PegEqm 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 P B := by
  constructor
  · rintro ⟨hPa, hPpos, hBa, -, -, ⟨hv0, hv⟩, hbp⟩
    exact ⟨hPa, hBa, hPpos, (bondPricing_iff_fisherExact 𝔼).mp hbp,
      fun ω => congrFun hv0 ω, fun t ω => congrFun (hv t) ω⟩
  · rintro ⟨hPa, hBa, hPpos, hfis, hv0, hv⟩
    exact ⟨hPa, hPpos, hBa, hia, hi, ⟨funext hv0, fun t => funext (hv t)⟩,
      (bondPricing_iff_fisherExact 𝔼).mpr hfis⟩

/-- Cochrane (2023), p. 33: the peg price path constructed in `Links` (`ftplPrice`, from the
exact Fisher equation and the valuation equation) is the peg price path of `FiscalMonetary`
(`pegP`) when the present value is `FiscalMonetary.pv`. No hypotheses are needed. -/
theorem ftplPrice_eq_pegP (β Bm1 : ℝ) (s i : ℕ → Ω → ℝ) (t : ℕ) :
    Links.ftplPrice 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 t =
      FiscalMonetary.pegP 𝔼 β (fun _ => Bm1) s i t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext ω
    have e := congrFun (FiscalMonetary.pvEx_eq 𝔼 β s t) ω
    simp only [Pi.smul_apply, smul_eq_mul] at e
    change β * (1 + i t ω) * (Links.ftplPrice 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 t ω *
        𝔼.E t (FiscalMonetary.pv 𝔼 β s (t + 1)) ω) / FiscalMonetary.pv 𝔼 β s (t + 1) ω =
      (1 + i t ω) * FiscalMonetary.pegP 𝔼 β (fun _ => Bm1) s i t ω *
        FiscalMonetary.pvEx 𝔼 β s t ω / FiscalMonetary.pv 𝔼 β s (t + 1) ω
    rw [ih, e]
    ring

/-- Cochrane (2023), p. 33: the peg debt of `Links` (`ftplDebt`) is the peg debt of
`FiscalMonetary` (`pegB`) when the present value is `FiscalMonetary.pv`. -/
theorem ftplDebt_eq_pegB (β Bm1 : ℝ) (s i : ℕ → Ω → ℝ) (t : ℕ) :
    Links.ftplDebt 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 t =
      FiscalMonetary.pegB 𝔼 β (fun _ => Bm1) s i t := by
  funext ω
  have e := congrFun (FiscalMonetary.pvEx_eq 𝔼 β s t) ω
  simp only [Pi.smul_apply, smul_eq_mul] at e
  change β * (1 + i t ω) * (Links.ftplPrice 𝔼 β i (FiscalMonetary.pv 𝔼 β s) Bm1 t ω *
      𝔼.E t (FiscalMonetary.pv 𝔼 β s (t + 1)) ω) =
    (1 + i t ω) * FiscalMonetary.pegP 𝔼 β (fun _ => Bm1) s i t ω *
      FiscalMonetary.pvEx 𝔼 β s t ω
  rw [ftplPrice_eq_pegP, e]
  ring

/-! ### The linear model as the derivative of the nonlinear model -/

/-- Cochrane (2023), eqs. (2.3) and (2.16), pp. 22, 35: every equilibrium derived in
`Valuation` satisfies the exact Fisher equation of `LinearFTMP` with the nominal rate
`i_t = 1/Q_t − 1` (`Environment.rate`). -/
theorem isEqm_fisherExact {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ} (h : Valuation.IsEqm 𝔼 β Bm s P Q)
    (t : ℕ) : LinearFTMP.FisherExact 𝔼 β (Environment.rate Q) P t := by
  intro ω
  rw [one_div, ← Environment.bondPrice_eq_inv_one_add_rate, h.2.2.1 t]
  rfl

/-- Cochrane (2023), eq. (2.16), p. 35: in every equilibrium derived in `Valuation` with
positive bond prices, the exact Fisher equation holds in logs,
`log(1 + i_t) = −log β − log E_t[exp(−π_{t+1})]`; `LinearFTMP.fisher_deriv` shows that its
derivative at the steady state is the linear (2.16), `i_t = r + E_t π_{t+1}`. -/
theorem isEqm_fisher_log {β : ℝ} (hβ : 0 < β) {Bm s P Q : ℕ → Ω → ℝ}
    (h : Valuation.IsEqm 𝔼 β Bm s P Q) (hQ : ∀ t ω, 0 < Q t ω) (t : ℕ) (ω : Ω) :
    Real.log (1 + Environment.rate Q t ω) = -Real.log β -
      Real.log (𝔼.E t (fun ω' => Real.exp (-Real.log (P (t + 1) ω' / P t ω'))) ω) := by
  have hi : ∀ ω, 0 < 1 + Environment.rate Q t ω := fun ω => by
    simp only [Environment.rate]
    linarith [inv_pos.mpr (hQ t ω)]
  have hE : ∀ ω, 0 < 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω := fun ω => by
    have e := congrFun (h.2.2.1 t) ω
    simp only [Pi.smul_apply, smul_eq_mul] at e
    by_contra hc
    push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos hβ.le hc
    linarith [hQ t ω]
  exact (LinearFTMP.fisher_log_form 𝔼 hβ h.1 hi hE).mp (isEqm_fisherExact 𝔼 h t) ω

/-- Cochrane (2023), pp. 35, 43: for bounded surpluses the ex-post fiscal news of
`FiscalMonetary`, `ΔE_{t+1} ∑ βʲ s_{t+1+j}`, is the fiscal shock `ε_{Σs,t+1}` of `LinearFTMP`. -/
theorem innov_epv_eq_pvNews {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    innov 𝔼 t (FiscalMonetary.epv β s (t + 1)) = LinearFTMP.pvNews 𝔼 β s t :=
  funext fun ω => FiscalMonetary.news_epv_tsum hβ0 hβ1 hs t ω

/-- Cochrane (2023), eqs. (2.13) and (2.17), pp. 30, 35: in every equilibrium of
`FiscalMonetary` with bounded surpluses, the exact unexpected-inflation identity is the exact
(2.17) of `LinearFTMP` (`unexpected_inflation_exact` with `PV = Valuation.pv`), with the fiscal
shock `ε_{Σs,t+1}`: `(B_t/P_t) ΔE_{t+1}(P_t/P_{t+1}) = ε_{Σs,t+1}`. Its derivative along a
family of equilibria is the linear (2.17), `LinearFTMP.linear_217`. -/
theorem equilibrium_pvNews (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) :
    (fun ω => B t ω / P t ω) * innov 𝔼 t (fun ω => P t ω / P (t + 1) ω) =
      LinearFTMP.pvNews 𝔼 β s t := by
  rw [LinearFTMP.unexpected_inflation_exact 𝔼 hPO (PV := Valuation.pv 𝔼 β s)
    (fun ω => (h.2.1 t ω).ne') (FiscalMonetary.realDebt_known hPO h t)
    ((h.2.2.2.2.2.1.2 t).trans (fm_pv_eq_pv_of_bounded 𝔼 hβ0 hβ1 hs (t + 1)))]
  exact LinearFTMP.innov_forwardSeries 𝔼 hβ0 hβ1 hs t

/-- Cochrane (2023), eq. (2.18), p. 35: in every equilibrium of `FiscalMonetary` with bounded
surpluses, `(B_t/P_t)/(1 + i_t) = ∑_{k≥0} β^{k+1} E_t s_{t+1+k}` (`LinearFTMP.debt_218`). -/
theorem equilibrium_debt_218 (hPO : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Bm1 : Ω → ℝ} {s B P i : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M)
    (h : FiscalMonetary.Equilibrium 𝔼 β Bm1 s B P i) (t : ℕ) (ω : Ω) :
    B t ω / P t ω * (1 / (1 + i t ω)) = ∑' k, β ^ (k + 1) * 𝔼.E t (s (t + 1 + k)) ω :=
  LinearFTMP.debt_218 𝔼 hPO hβ0 hβ1 hs (fun ω => (h.2.1 t ω).ne')
    ((bondPricing_iff_fisherExact 𝔼).mp h.2.2.2.2.2.2 t) (FiscalMonetary.realDebt_known hPO h t)
    ((h.2.2.2.2.2.1.2 t).trans (fm_pv_eq_pv_of_bounded 𝔼 hβ0 hβ1 hs (t + 1))) ω

end Cochrane.IntertemporalModel.GeneralLinks
