/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasFiscalNK

/-!
# The long-term-debt response (Fig. 5.4) in a probability model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.2, pp. 127–129, Fig. 5.4,
and §5.3, p. 131 ("a rate rise can lower inflation if debt is long-term").

As for one-period debt (`TidyR6MeasResponses`), the forecast paths of a bounded equilibrium of the
measure-theoretic long-term-debt model `TidyR6MeasFiscalNK.MLTD` are, state by state, a
perfect-foresight equilibrium of the core `LongTermDebt.LTD` (`ltd_forecast`), started from the
date-`s` pre-sample debt and bond price (`vqHat_zero`, `vqHat_succ`).

## Main results

* **`ltd_forecast`**: the bridge.
* `ltd_pf_peg`: under perfect foresight, every bounded equilibrium with a constant rate peg `c`,
  no surpluses and zero pre-sample values is `c` times the unit response of
  `LongTermDebt.ltd_perm_rise` (proved by combining with the unit solution, no division by `c`).
* **`fig54_response`** (Fig. 5.4 as forecast revisions): with a date-1 rate shock `ε`
  (`E_0 ε = 0`), a.e. `E_0 π_{1+j} = 0` and
  `E_1 π_{1+j} = ε (1 − [(1 − ρ/λ₁)/(1 − ω̃)] λ₁^{−j})`; **`fig54_disinflation`**: the impact
  revision has the opposite sign to the rate rise iff `ω̃ > ρ/λ₁`.
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasLTDResponse

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRulesMeasure NKModel LongTermDebt
  TidyR6MeasFiscalNK

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), pp. 127–128 (the pre-sample debt of a forecast path):
`v̂_{−1} = ρ E_s v_s − E_s r^n_s + E_s π_s + E_s s̃_s`. -/
noncomputable def vHat (ρ : ℝ) (s v p rn : ℕ → Ω → ℝ) (s0 : ℕ) (ω : Ω) : ℝ :=
  ρ * S.E s0 (v s0) ω - S.E s0 (rn s0) ω + S.E s0 (p s0) ω + S.E s0 (s s0) ω

/-- Cochrane (2023), (5.21) (the pre-sample bond price of a forecast path):
`q̂_{−1} = ω̃ E_s q_s − E_s r^n_s`. -/
noncomputable def qHat (om : ℝ) (q rn : ℕ → Ω → ℝ) (s0 : ℕ) (ω : Ω) : ℝ :=
  om * S.E s0 (q s0) ω - S.E s0 (rn s0) ω

/-- Cochrane (2023), pp. 127–129, **the forecast paths of the long-term-debt model are
perfect-foresight equilibria**: in a bounded equilibrium of (5.17)–(5.21) with bounded adapted
`i`, `s̃`, for every date `s` and a.e. state, the forecast paths form a bounded equilibrium of the
perfect-foresight model `LongTermDebt.LTD` driven by the forecast rate and surplus paths from
`(v̂_{−1}, q̂_{−1})`. -/
theorem ltd_forecast {σ β κ ρ om : ℝ} {i s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ}
    {x p v q rn : ℕ → Ω → ℝ} (h : MLTD S σ β κ ρ om i s vm1 qm1 x p v q rn)
    (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i) (hsa : StronglyAdapted S.𝓕 s)
    (hsb : S.BddProc s) (hvb : S.BddProc v) (hrna : StronglyAdapted S.𝓕 rn)
    (hrnb : S.BddProc rn) (s0 : ℕ) :
    ∀ᵐ ω ∂S.μ, LTD perfectForesight σ β κ ρ om (fun k _ => S.E s0 (i (s0 + k)) ω)
        (fun k _ => S.E s0 (s (s0 + k)) ω) (fun _ => vHat S ρ s v p rn s0 ω)
        (fun _ => qHat S om q rn s0 ω) (fun k _ => S.E s0 (x (s0 + k)) ω)
        (fun k _ => S.E s0 (p (s0 + k)) ω) (fun k _ => S.E s0 (v (s0 + k)) ω)
        (fun k _ => S.E s0 (q (s0 + k)) ω) (fun k _ => S.E s0 (rn (s0 + k)) ω) ∧
      BoundedProc (fun k (_ : Unit) => S.E s0 (p (s0 + k)) ω) ∧
      BoundedProc (fun k (_ : Unit) => S.E s0 (v (s0 + k)) ω) ∧
      BoundedProc (fun k (_ : Unit) => S.E s0 (q (s0 + k)) ω) := by
  obtain ⟨⟨his, hpc⟩, hfl, -, h20, h21, -, hxa, hpa, hva, hqa, hxb, hpb, hqb⟩ := h
  have hxi := int_of S hxa hxb
  have hpi := int_of S hpa hpb
  have hii := int_of S hia hib
  have hsi := int_of S hsa hsb
  have hvi := int_of S hva hvb
  have hqi := int_of S hqa hqb
  have hrni := int_of S hrna hrnb
  have hIS : ∀ k, ∀ᵐ ω ∂S.μ, S.E s0 (x (s0 + k)) ω = S.E s0 (x (s0 + k + 1)) ω -
      σ * (S.E s0 (i (s0 + k)) ω - S.E s0 (p (s0 + k + 1)) ω) := by
    intro k
    have hA := S.integrable_E (s0 + k) (x (s0 + k + 1))
    have hC := S.integrable_E (s0 + k) (p (s0 + k + 1))
    filter_upwards [S.E_congr (his (s0 + k)) s0,
      E_sub_smul S hA ((hii (s0 + k)).sub hC) σ s0, S.E_sub (hii (s0 + k)) hC s0,
      S.E_tower (Nat.le_add_right s0 k) (x (s0 + k + 1)),
      S.E_tower (Nat.le_add_right s0 k) (p (s0 + k + 1))] with ω e2 e3 e4 e5 e6
    rw [e2, e3, e4, Pi.sub_apply, e5, e6]
  have hPC : ∀ k, ∀ᵐ ω ∂S.μ, S.E s0 (p (s0 + k)) ω = β * S.E s0 (p (s0 + k + 1)) ω +
      κ * S.E s0 (x (s0 + k)) ω := by
    intro k
    have hC := S.integrable_E (s0 + k) (p (s0 + k + 1))
    filter_upwards [S.E_congr (hpc (s0 + k)) s0, E_comb S hC (hxi (s0 + k)) β κ s0,
      S.E_tower (Nat.le_add_right s0 k) (p (s0 + k + 1))] with ω e1 e2 e3
    rw [e1, e2, e3]
  have hFL : ∀ k, ∀ᵐ ω ∂S.μ, ρ * S.E s0 (v (s0 + k + 1)) ω = S.E s0 (v (s0 + k)) ω +
      S.E s0 (rn (s0 + k + 1)) ω - S.E s0 (p (s0 + k + 1)) ω - S.E s0 (s (s0 + k + 1)) ω := by
    intro k
    filter_upwards [S.E_congr (hfl (s0 + k)) s0, S.E_smul ρ (v (s0 + k + 1)) s0,
      S.E_sub (((hvi (s0 + k)).add (hrni (s0 + k + 1))).sub (hpi (s0 + k + 1)))
        (hsi (s0 + k + 1)) s0,
      S.E_sub ((hvi (s0 + k)).add (hrni (s0 + k + 1))) (hpi (s0 + k + 1)) s0,
      S.E_add (hvi (s0 + k)) (hrni (s0 + k + 1)) s0] with ω e1 e2 e3 e4 e5
    rw [e2] at e1
    simp only [Pi.smul_apply, smul_eq_mul] at e1
    rw [e1, e3, Pi.sub_apply, e4, Pi.sub_apply, e5, Pi.add_apply]
  have hEH : ∀ k, ∀ᵐ ω ∂S.μ, S.E s0 (rn (s0 + k + 1)) ω = S.E s0 (i (s0 + k)) ω := by
    intro k
    filter_upwards [(S.E_tower (Nat.le_add_right s0 k) (rn (s0 + k + 1))).symm,
      S.E_congr (h20 (s0 + k)) s0] with ω e1 e2
    rw [e1, e2]
  have hR : ∀ k, ∀ᵐ ω ∂S.μ, S.E s0 (rn (s0 + k + 1)) ω =
      om * S.E s0 (q (s0 + k + 1)) ω - S.E s0 (q (s0 + k)) ω := by
    intro k
    rw [h21 (s0 + k)]
    filter_upwards [E_sub_smul S (hqi (s0 + k + 1)) (hqi (s0 + k)) om s0,
      S.E_sub ((hqi (s0 + k + 1)).smul om) (hqi (s0 + k)) s0,
      S.E_smul om (q (s0 + k + 1)) s0] with ω e1 e2 e3
    rw [e2, Pi.sub_apply, e3]
    rfl
  obtain ⟨Mp, hMp⟩ := hpb
  obtain ⟨Mv, hMv⟩ := hvb
  obtain ⟨Mq, hMq⟩ := hqb
  filter_upwards [ae_all_iff.2 hIS, ae_all_iff.2 hPC, ae_all_iff.2 hFL, ae_all_iff.2 hEH,
    ae_all_iff.2 hR, ae_all_iff.2 fun k => S.abs_E_le (hMp (s0 + k)) s0,
    ae_all_iff.2 fun k => S.abs_E_le (hMv (s0 + k)) s0,
    ae_all_iff.2 fun k => S.abs_E_le (hMq (s0 + k)) s0] with ω e1 e2 e3 e4 e5 b1 b2 b3
  refine ⟨⟨⟨fun k => ?_, fun k => ?_⟩, fun k => ?_, ?_, fun k => ?_, fun k => ?_, ?_⟩,
    ⟨Mp, fun k _ => b1 k⟩, ⟨Mv, fun k _ => b2 k⟩, ⟨Mq, fun k _ => b3 k⟩⟩
  · funext u
    change S.E s0 (x (s0 + k)) ω = S.E s0 (x (s0 + (k + 1))) ω -
      σ * (S.E s0 (i (s0 + k)) ω - S.E s0 (p (s0 + (k + 1))) ω)
    exact e1 k
  · funext u
    change S.E s0 (p (s0 + k)) ω = β * S.E s0 (p (s0 + (k + 1))) ω +
      κ * S.E s0 (x (s0 + k)) ω
    exact e2 k
  · funext u
    change ρ * S.E s0 (v (s0 + (k + 1))) ω = S.E s0 (v (s0 + k)) ω +
      S.E s0 (rn (s0 + (k + 1))) ω - S.E s0 (p (s0 + (k + 1))) ω - S.E s0 (s (s0 + (k + 1))) ω
    exact e3 k
  · funext u
    change ρ * S.E s0 (v (s0 + 0)) ω = vHat S ρ s v p rn s0 ω + S.E s0 (rn (s0 + 0)) ω -
      S.E s0 (p (s0 + 0)) ω - S.E s0 (s (s0 + 0)) ω
    simp only [vHat, add_zero]
    ring
  · funext u
    change S.E s0 (rn (s0 + (k + 1))) ω = S.E s0 (i (s0 + k)) ω
    exact e4 k
  · funext u
    change S.E s0 (rn (s0 + (k + 1))) ω =
      om * S.E s0 (q (s0 + (k + 1))) ω - S.E s0 (q (s0 + k)) ω
    exact e5 k
  · funext u
    change S.E s0 (rn (s0 + 0)) ω = om * S.E s0 (q (s0 + 0)) ω - qHat S om q rn s0 ω
    simp only [qHat, add_zero]
    ring

/-- Cochrane (2023), p. 128 (tool): at `s = 0` the forecast path starts from `(v_{−1}, q_{−1})`. -/
theorem vqHat_zero {σ β κ ρ om : ℝ} {i s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ}
    {x p v q rn : ℕ → Ω → ℝ} (h : MLTD S σ β κ ρ om i s vm1 qm1 x p v q rn)
    (hsa : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s) (hvb : S.BddProc v)
    (hrna : StronglyAdapted S.𝓕 rn) (hrnb : S.BddProc rn) :
    ∀ᵐ ω ∂S.μ, vHat S ρ s v p rn 0 ω = vm1 ω ∧ qHat S om q rn 0 ω = qm1 ω := by
  obtain ⟨-, -, h0, -, -, hr0, -, hpa, hva, hqa, -, hpb, hqb⟩ := h
  filter_upwards [h0] with ω e
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply] at e
  simp only [vHat, qHat, E_self S hva hvb 0, E_self S hpa hpb 0, E_self S hsa hsb 0,
    E_self S hrna hrnb 0, E_self S hqa hqb 0]
  have hr := congrFun hr0 ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hr
  constructor <;> linarith

/-- Cochrane (2023), p. 128 (tool): at `s = t + 1` the forecast path starts from `(v_t, q_t)`. -/
theorem vqHat_succ {σ β κ ρ om : ℝ} {i s : ℕ → Ω → ℝ} {vm1 qm1 : Ω → ℝ}
    {x p v q rn : ℕ → Ω → ℝ} (h : MLTD S σ β κ ρ om i s vm1 qm1 x p v q rn)
    (hsa : StronglyAdapted S.𝓕 s) (hsb : S.BddProc s) (hvb : S.BddProc v)
    (hrna : StronglyAdapted S.𝓕 rn) (hrnb : S.BddProc rn) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, vHat S ρ s v p rn (t + 1) ω = v t ω ∧ qHat S om q rn (t + 1) ω = q t ω := by
  obtain ⟨-, hfl, -, -, h21, -, -, hpa, hva, hqa, -, hpb, hqb⟩ := h
  filter_upwards [hfl t] with ω e
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.add_apply] at e
  simp only [vHat, qHat, E_self S hva hvb (t + 1), E_self S hpa hpb (t + 1),
    E_self S hsa hsb (t + 1), E_self S hrna hrnb (t + 1), E_self S hqa hqb (t + 1)]
  have hr := congrFun (h21 t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hr
  constructor <;> linarith

/-- Cochrane (2023), Fig. 5.4, p. 128 (perfect foresight, any size of rise): every bounded
equilibrium of the long-term-debt model with the peg `i ≡ c`, no surpluses and zero pre-sample
values has `q_t = −c/(1 − ω̃)` and `π_t = c (1 − [(1 − ρ/λ₁)/(1 − ω̃)] λ₁^{−t})` — `c` times the
unit response of `LongTermDebt.ltd_perm_rise`. -/
theorem ltd_pf_peg {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) (c : ℝ) {x π v q rn : ℕ → Unit → ℝ}
    (h : LTD perfectForesight σ β κ ρ om (fun _ _ => c) (fun _ _ => 0) 0 0 x π v q rn)
    (hπb : BoundedProc π) (hvb : BoundedProc v) (hqb : BoundedProc q) (t : ℕ) :
    q t () = -c / (1 - om) ∧
      π t () = c * (1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om) * (lam1 σ β κ)⁻¹ ^ t) ∧
      v t () = c * (-(lam1 σ β κ)⁻¹ ^ (t + 1) / (1 - om)) := by
  obtain ⟨xU, πU, vU, qU, rnU, ⟨hU, -, -, hπU, hvU, hqU⟩, -⟩ :=
    ltd_determinate perfectForesight hσ hκ hβ hρ0 hρ1 hom0 hom1 (i := fun _ _ => (1 : ℝ))
      (s := fun _ _ => (0 : ℝ)) (vm1 := 0) (qm1 := 0) (fun _ => rfl) (Mi := 1) (by simp)
      (fun _ => rfl) (Ms := 0) (by simp) rfl (Mv := 0) (by simp) rfl (Mq := 0) (by simp)
  set d := 1 - c
  have hY : LTD perfectForesight σ β κ ρ om (fun _ _ => 1) (fun _ _ => 0) 0 0
      (fun t u => x t u + d * xU t u) (fun t u => π t u + d * πU t u)
      (fun t u => v t u + d * vU t u) (fun t u => q t u + d * qU t u)
      (fun t u => rn t u + d * rnU t u) := by
    obtain ⟨⟨a1, a2⟩, a3, a4, a5, a6, a7⟩ := h
    obtain ⟨⟨b1, b2⟩, b3, b4, b5, b6, b7⟩ := hU
    refine ⟨⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, ?_, fun t => ?_, fun t => ?_, ?_⟩ <;>
      funext u
    · have e1 := congrFun (a1 t) u
      have e2 := congrFun (b1 t) u
      simp only [perfectForesight, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] at e1 e2 ⊢
      simp only [d]
      linear_combination e1 + (1 - c) * e2
    · have e1 := congrFun (a2 t) u
      have e2 := congrFun (b2 t) u
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at e1 e2 ⊢
      linear_combination e1 + d * e2
    · have e1 := congrFun (a3 t) u
      have e2 := congrFun (b3 t) u
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      linear_combination e1 + d * e2
    · have e1 := congrFun a4 u
      have e2 := congrFun b4 u
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        at e1 e2 ⊢
      linear_combination e1 + d * e2
    · have e1 := congrFun (a5 t) u
      have e2 := congrFun (b5 t) u
      simp only [perfectForesight, LinearMap.id_apply] at e1 e2 ⊢
      simp only [d]
      linear_combination e1 + (1 - c) * e2
    · have e1 := congrFun (a6 t) u
      have e2 := congrFun (b6 t) u
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      linear_combination e1 + d * e2
    · have e1 := congrFun a7 u
      have e2 := congrFun b7 u
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
      linear_combination e1 + d * e2
  have hbd : ∀ {y z : ℕ → Unit → ℝ}, BoundedProc y → BoundedProc z →
      BoundedProc (fun t u => y t u + d * z t u) := by
    intro y z ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + |d| * B, fun t u => (abs_add_le _ _).trans (add_le_add (hA t u) ?_)⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t u) (abs_nonneg _)
  have hY' := ltd_perm_rise perfectForesight hσ hκ hβ hρ0 hρ1 hom0 hom1 hY (fun _ => rfl)
    (hbd hπb hπU) (hbd hvb hvU) (hbd hqb hqU) t ()
  have hU' := ltd_perm_rise perfectForesight hσ hκ hβ hρ0 hρ1 hom0 hom1 hU (fun _ => rfl)
    hπU hvU hqU t ()
  have hom : 1 - om ≠ 0 := by linarith
  constructor
  · have e1 := hY'.1
    have e2 := hU'.1
    rw [e2] at e1
    simp only [d] at e1
    field_simp at e1 ⊢
    linarith
  constructor
  · have e1 := hY'.2.1
    have e2 := hU'.2.1
    rw [e2] at e1
    simp only [d] at e1
    linarith
  · have e1 := hY'.2.2.2
    have e2 := hU'.2.2.2
    rw [e2] at e1
    simp only [d] at e1
    linarith

/-- Cochrane (2023), Fig. 5.4, p. 128, **as forecast revisions in a probability model**: a date-1
rate shock `ε` (bounded, `𝓕₁`-measurable, `E_0 ε = 0`), `i_0 = 0`, `i_t = ε` for `t ≥ 1`, no
surpluses, zero pre-sample debt and bond price, `0 ≤ ω̃ < 1`. In every bounded equilibrium with
long-term debt, a.e., `E_0 π_{1+j} = 0` and
`E_1 π_{1+j} = ε (1 − [(1 − ρ/λ₁)/(1 − ω̃)] λ₁^{−j})`. -/
theorem fig54_response {σ β κ ρ om B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) {ε : Ω → ℝ}
    (hεm : StronglyMeasurable[S.𝓕 1] ε) (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B)
    (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v q rn : ℕ → Ω → ℝ}
    (h : MLTD S σ β κ ρ om (fun t => if t = 0 then 0 else ε) 0 0 0 x p v q rn)
    (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, ∀ j, S.E 0 (p (1 + j)) ω = 0 ∧
      S.E 1 (p (1 + j)) ω =
        ε ω * (1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om) * (lam1 σ β κ)⁻¹ ^ j) := by
  set i : ℕ → Ω → ℝ := fun t => if t = 0 then 0 else ε
  have hεi : Integrable ε S.μ :=
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable hεm hεb).integrable
  have hia : StronglyAdapted S.𝓕 i := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · simp only [i, ht, ↓reduceIte]
      exact stronglyMeasurable_const
    · simp only [i, ht.ne', ↓reduceIte]
      exact hεm.mono (S.𝓕.mono ht)
  have hib : S.BddProc i := ⟨|B|, fun t => by
    filter_upwards [hεb] with ω h1
    by_cases ht : t = 0
    · simp [i, ht]
    · simp only [i, ht, ↓reduceIte]
      exact h1.trans (le_abs_self B)⟩
  have hsa : StronglyAdapted S.𝓕 (0 : ℕ → Ω → ℝ) := fun t => stronglyMeasurable_const
  have hsb : S.BddProc (0 : ℕ → Ω → ℝ) := mbdd_zero S
  -- the returns are adapted and bounded
  obtain ⟨-, -, -, -, h21, hr0, -, -, hva, hqa, -, -, hqb⟩ := id h
  obtain ⟨Mq, hMq⟩ := hqb
  have hrna : StronglyAdapted S.𝓕 rn := by
    intro t
    cases t with
    | zero =>
      rw [hr0]
      exact ((hqa 0).const_smul om).sub stronglyMeasurable_const
    | succ t =>
      rw [h21 t]
      exact ((hqa (t + 1)).const_smul om).sub ((hqa t).mono (S.𝓕.mono (Nat.le_succ t)))
  have hrnb : S.BddProc rn := by
    refine ⟨|om| * Mq + |Mq|, fun t => ?_⟩
    cases t with
    | zero =>
      filter_upwards [hMq 0] with ω e
      rw [hr0]
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, sub_zero, abs_mul]
      exact (mul_le_mul_of_nonneg_left e (abs_nonneg _)).trans (le_add_of_nonneg_right
        (abs_nonneg _))
    | succ t =>
      filter_upwards [hMq (t + 1), hMq t] with ω e1 e2
      rw [h21 t]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans (add_le_add ?_ (e2.trans (le_abs_self _)))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
  have hEi0 : ∀ k, ∀ᵐ ω ∂S.μ, S.E 0 (i (0 + k)) ω = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · refine Eventually.of_forall fun ω => ?_
      simp only [zero_add, hk, i, ↓reduceIte]
      rw [S.E_zero]
      rfl
    · filter_upwards [hε0] with ω e
      simp only [zero_add, i, hk.ne', ↓reduceIte]
      exact e
  have hzero : ∀ s0 k (ω : Ω), S.E s0 ((0 : ℕ → Ω → ℝ) (s0 + k)) ω = 0 := fun s0 k ω => by
    simp [S.E_zero]
  filter_upwards [ltd_forecast S h hia hib hsa hsb hvb hrna hrnb 0,
    ltd_forecast S h hia hib hsa hsb hvb hrna hrnb 1, vqHat_zero S h hsa hsb hvb hrna hrnb,
    vqHat_succ S h hsa hsb hvb hrna hrnb 0, ae_all_iff.2 hEi0] with ω ⟨f0, b0p, b0v, b0q⟩
    ⟨f1, b1p, b1v, b1q⟩ ⟨ev0, eq0⟩ ⟨ev1, eq1⟩ ei0
  -- the date-0 forecast path: all data zero
  have hi0 : (fun k (_ : Unit) => S.E 0 (i (0 + k)) ω) = fun _ _ => (0 : ℝ) := by
    funext k u
    exact ei0 k
  have hs0 : (fun k (_ : Unit) => S.E 0 ((0 : ℕ → Ω → ℝ) (0 + k)) ω) = fun _ _ => (0 : ℝ) := by
    funext k u
    exact hzero 0 k ω
  rw [hi0, hs0, ev0, eq0] at f0
  have f0' := f0
  change LTD perfectForesight σ β κ ρ om (fun _ _ => (0 : ℝ)) (fun _ _ => 0) 0 0 _ _ _ _ _ at f0'
  have P0 := fun j => ltd_pf_peg hσ hκ hβ hρ0 hρ1 hom0 hom1 0 f0' b0p b0v b0q j
  -- `v_0 = 0` and `q_0 = 0`
  have hv0 : v 0 ω = 0 := by
    have := (P0 0).2.2
    simp only [zero_add] at this
    rw [show S.E 0 (v 0) ω = v 0 ω from by
      rw [E_self S hva hvb 0]] at this
    rw [this]
    ring
  have hq0' : q 0 ω = 0 := by
    have := (P0 0).1
    simp only [zero_add] at this
    rw [show S.E 0 (q 0) ω = q 0 ω from by rw [E_self S hqa ⟨Mq, hMq⟩ 0]] at this
    rw [this]
    ring
  -- the date-1 forecast path: the peg `ε`
  have hi1 : (fun k (_ : Unit) => S.E 1 (i (1 + k)) ω) = fun _ _ => ε ω := by
    funext k u
    simp only [i, show 1 + k ≠ 0 by omega, ↓reduceIte]
    rw [S.E_of_stronglyMeasurable hεm hεi]
  have hs1 : (fun k (_ : Unit) => S.E 1 ((0 : ℕ → Ω → ℝ) (1 + k)) ω) = fun _ _ => (0 : ℝ) := by
    funext k u
    exact hzero 1 k ω
  rw [hi1, hs1, ev1, eq1, hv0, hq0'] at f1
  have f1' := f1
  change LTD perfectForesight σ β κ ρ om (fun _ _ => ε ω) (fun _ _ => 0) 0 0 _ _ _ _ _ at f1'
  intro j
  refine ⟨?_, (ltd_pf_peg hσ hκ hβ hρ0 hρ1 hom0 hom1 (ε ω) f1' b1p b1v b1q j).2.1⟩
  have := (P0 (1 + j)).2.1
  rw [zero_add] at this
  rw [this]
  ring

/-- Cochrane (2023), §5.3, p. 131 and Fig. 5.4 ("a rate rise lowers inflation on impact iff debt is
long enough"), **as a forecast revision in a probability model**: in the setting of
`fig54_response`, a.e. the impact revision is
`E_1 π_1 − E_0 π_1 = ε (1 − (1 − ρ/λ₁)/(1 − ω̃))`, and for a rise (`ε > 0`) it is negative iff
`ω̃ > ρ/λ₁`. -/
theorem fig54_disinflation {σ β κ ρ om B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) {ε : Ω → ℝ}
    (hεm : StronglyMeasurable[S.𝓕 1] ε) (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B)
    (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v q rn : ℕ → Ω → ℝ}
    (h : MLTD S σ β κ ρ om (fun t => if t = 0 then 0 else ε) 0 0 0 x p v q rn)
    (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, S.E 1 (p 1) ω - S.E 0 (p 1) ω =
        ε ω * (1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om)) ∧
      (0 < ε ω → (S.E 1 (p 1) ω - S.E 0 (p 1) ω < 0 ↔ ρ * (lam1 σ β κ)⁻¹ < om)) := by
  filter_upwards [fig54_response S hσ hκ hβ hρ0 hρ1 hom0 hom1 hεm hεb hε0 h hvb] with ω e
  have e0 := e 0
  simp only [add_zero, pow_zero, mul_one] at e0
  have hval : S.E 1 (p 1) ω - S.E 0 (p 1) ω =
      ε ω * (1 - (1 - ρ * (lam1 σ β κ)⁻¹) / (1 - om)) := by
    rw [e0.1, e0.2, sub_zero]
  refine ⟨hval, fun hε => ?_⟩
  rw [hval, ← ltd_disinflation_iff hom1]
  constructor
  · intro hneg
    by_contra hc
    push Not at hc
    nlinarith
  · intro hneg
    nlinarith

end Cochrane.StickyPriceFiscal.TidyR6MeasLTDResponse
