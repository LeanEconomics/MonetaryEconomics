/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasResponses
import StickyPriceFiscal.TidyR6MeasLTDResponse
import StickyPriceFiscal.HigherOrLower

/-!
# Non-constant rate news in a probability model: Fig. 5.2, the joint contraction, AR(1) rises

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1.2, Fig. 5.2, p. 124
(an anticipated rise), §5.3, pp. 131–132 (a joint monetary–fiscal contraction; a persistent
AR(1) rise with long-term debt).

The perfect-foresight models are linear in the forcing: `ftplnk_pf_add`, `ltd_pf_add`. With the
uniqueness theorems this gives **scaling** (`ftplnk_pf_scale`, `ltd_pf_scale`): the unique bounded
equilibrium driven by the rate path `c·r` is `c` times the one driven by `r` — proved without
dividing by `c`. Combined with the forecast bridges (`TidyR6MeasResponses.pf_forecast`,
`TidyR6MeasLTDResponse.ltd_forecast`), the core closed forms become statements about forecast
revisions in every probability model:

* **`fig52_response`**: a date-1 announcement `ε` of a rise from date `1 + S` on gives
  `E_0 π_{1+j} = 0`, `E_1 π_{1+j} = ε · FiscalNK.antPi S j` a.e.;
* **`joint_contraction_response`**: a date-1 rate rise `ε` with surplus news `ε s̃` (present value
  `S`) gives `E_1 π_{1+j} − E_0 π_{1+j} = ε(1 − (1 − ρ/λ₁)(1 + S)λ₁^{−j})` a.e.;
* **`ltd_ar1_response`**: with long-term debt, a date-1 AR(1) rate shock `i_{1+k} = ε ηᵏ` gives
  `E_0 π_{1+j} = 0`, `E_1 π_{1+j} = ε (A ηʲ + C λ₁^{−j})` (`LongTermDebt.ar1A`,
  `LongTermDebt.ar1C`) a.e.
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasPathForecasts

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRulesMeasure NKModel FiscalNK
  LongTermDebt TidyR6MeasFiscalNK TidyR6MeasResponses TidyR6MeasLTDResponse

/-! ### Linearity of the perfect-foresight models -/

/-- Cochrane (2023), (5.15)–(5.16) (tool): perfect-foresight equilibria of the one-period-debt
model add: `X + d·U` solves the model with forcing `i₁ + d i₂`, `s₁ + d s₂`, `b₁ + d b₂`. -/
theorem ftplnk_pf_add {σ β κ ρ d b1 b2 : ℝ} {i1 i2 s1 s2 x1 x2 p1 p2 v1 v2 : ℕ → Unit → ℝ}
    (h1 : FTPLNK perfectForesight σ β κ ρ i1 s1 (fun _ => b1) x1 p1 v1)
    (h2 : FTPLNK perfectForesight σ β κ ρ i2 s2 (fun _ => b2) x2 p2 v2) :
    FTPLNK perfectForesight σ β κ ρ (fun t u => i1 t u + d * i2 t u)
      (fun t u => s1 t u + d * s2 t u) (fun _ => b1 + d * b2) (fun t u => x1 t u + d * x2 t u)
      (fun t u => p1 t u + d * p2 t u) (fun t u => v1 t u + d * v2 t u) := by
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := h1
  obtain ⟨⟨b1', b2'⟩, b3, b4⟩ := h2
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, ?_⟩ <;> funext u
  · have e1 := congrFun (a1 t) u
    have e2 := congrFun (b1' t) u
    simp only [perfectForesight, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 + d * e2
  · have e1 := congrFun (a2 t) u
    have e2 := congrFun (b2' t) u
    simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 + d * e2
  · have e1 := congrFun (a3 t) u
    have e2 := congrFun (b3 t) u
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 + d * e2
  · have e1 := congrFun a4 u
    have e2 := congrFun b4 u
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 + d * e2

/-- Cochrane (2023), pp. 122–125 (tool), **scaling**: for `0 < ρ < 1` and a bounded rate path
`r`, if `U` is a bounded perfect-foresight equilibrium driven by `r` (no surpluses, `b₀ = 0`) and
`X` one driven by `c·r`, then `π_X = c π_U`, `x_X = c x_U` and `v_X = c v_U`. -/
theorem ftplnk_pf_scale {σ β κ ρ c M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {r : ℕ → ℝ} (hrb : ∀ t, |r t| ≤ M)
    {x p v xU pU vU : ℕ → Unit → ℝ}
    (hX : FTPLNK perfectForesight σ β κ ρ (fun t _ => c * r t) (fun _ _ => 0) (fun _ => 0) x p v)
    (hpb : BoundedProc p) (hvb : BoundedProc v)
    (hU : FTPLNK perfectForesight σ β κ ρ (fun t _ => r t) (fun _ _ => 0) (fun _ => 0) xU pU vU)
    (hpUb : BoundedProc pU) (hvUb : BoundedProc vU) (t : ℕ) :
    p t () = c * pU t () ∧ x t () = c * xU t () ∧ v t () = c * vU t () := by
  have hY := ftplnk_pf_add (d := 1 - c) hX hU
  have e1 : (fun t (u : Unit) => (fun t (_ : Unit) => c * r t) t u + (1 - c) * r t) =
      fun t _ => r t := by funext t u; ring
  have e2 : (fun t (u : Unit) => (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) t u +
      (1 - c) * (fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) t u) = fun _ _ => 0 := by funext t u; ring
  have e3 : (0 : ℝ) + (1 - c) * 0 = 0 := by ring
  rw [e1, e2, e3] at hY
  have hbd : ∀ {y z : ℕ → Unit → ℝ}, BoundedProc y → BoundedProc z →
      BoundedProc (fun t u => y t u + (1 - c) * z t u) := by
    intro y z ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + |1 - c| * B, fun t u => (abs_add_le _ _).trans (add_le_add (hA t u) ?_)⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t u) (abs_nonneg _)
  have hia : perfectForesight.Adapted (fun t (_ : Unit) => r t) := fun _ => rfl
  obtain ⟨hx, hp, hv⟩ := eqm_unique perfectForesight hσ hκ hβ hρ0 hρ1 hia (Mi := M)
    (fun t _ => hrb t) (fun _ => rfl) rfl ((ftplnk_iff perfectForesight).1 hY)
    ((ftplnk_iff perfectForesight).1 hU) (hbd hpb hpUb) hpUb (hbd hvb hvUb) hvUb
  have ep := congrFun (congrFun hp t) ()
  have ex := congrFun (congrFun hx t) ()
  have ev := congrFun (congrFun hv t) ()
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Cochrane (2023), (5.17)–(5.21) (tool): perfect-foresight equilibria of the long-term-debt
model add (zero pre-sample values, no surpluses). -/
theorem ltd_pf_add {σ β κ ρ om d : ℝ} {i1 i2 x1 x2 p1 p2 v1 v2 q1 q2 r1 r2 : ℕ → Unit → ℝ}
    (h1 : LTD perfectForesight σ β κ ρ om i1 (fun _ _ => 0) 0 0 x1 p1 v1 q1 r1)
    (h2 : LTD perfectForesight σ β κ ρ om i2 (fun _ _ => 0) 0 0 x2 p2 v2 q2 r2) :
    LTD perfectForesight σ β κ ρ om (fun t u => i1 t u + d * i2 t u) (fun _ _ => 0) 0 0
      (fun t u => x1 t u + d * x2 t u) (fun t u => p1 t u + d * p2 t u)
      (fun t u => v1 t u + d * v2 t u) (fun t u => q1 t u + d * q2 t u)
      (fun t u => r1 t u + d * r2 t u) := by
  obtain ⟨⟨a1, a2⟩, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨⟨b1, b2⟩, b3, b4, b5, b6, b7⟩ := h2
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, ?_, fun t => ?_, fun t => ?_, ?_⟩ <;>
    funext u
  · have e1 := congrFun (a1 t) u
    have e2 := congrFun (b1 t) u
    simp only [perfectForesight, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 + d * e2
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
    linear_combination e1 + d * e2
  · have e1 := congrFun (a6 t) u
    have e2 := congrFun (b6 t) u
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    linear_combination e1 + d * e2
  · have e1 := congrFun a7 u
    have e2 := congrFun b7 u
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
    linear_combination e1 + d * e2

/-- Cochrane (2023), §5.2 (tool), **scaling with long-term debt**: for `0 < ρ < 1`, `0 ≤ ω̃ < 1`
and a bounded rate path `r`, a bounded perfect-foresight equilibrium driven by `c·r` (no
surpluses, zero pre-sample values) has `π = c π_U` and `q = c q_U`, where `U` is one driven by
`r`. -/
theorem ltd_pf_scale {σ β κ ρ om c M : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) {r : ℕ → ℝ}
    (hrb : ∀ t, |r t| ≤ M) {x p v q rn xU pU vU qU rnU : ℕ → Unit → ℝ}
    (hX : LTD perfectForesight σ β κ ρ om (fun t _ => c * r t) (fun _ _ => 0) 0 0 x p v q rn)
    (hpb : BoundedProc p) (hvb : BoundedProc v) (hqb : BoundedProc q)
    (hU : LTD perfectForesight σ β κ ρ om (fun t _ => r t) (fun _ _ => 0) 0 0 xU pU vU qU rnU)
    (hpUb : BoundedProc pU) (hvUb : BoundedProc vU) (hqUb : BoundedProc qU) (t : ℕ) :
    p t () = c * pU t () ∧ q t () = c * qU t () := by
  have hY := ltd_pf_add (d := 1 - c) hX hU
  have e1 : (fun t (u : Unit) => (fun t (_ : Unit) => c * r t) t u + (1 - c) * r t) =
      fun t _ => r t := by funext t u; ring
  rw [e1] at hY
  have hbd : ∀ {y z : ℕ → Unit → ℝ}, BoundedProc y → BoundedProc z →
      BoundedProc (fun t u => y t u + (1 - c) * z t u) := by
    intro y z ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + |1 - c| * B, fun t u => (abs_add_le _ _).trans (add_le_add (hA t u) ?_)⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t u) (abs_nonneg _)
  obtain ⟨-, huniq⟩ := ltd_determinate perfectForesight hσ hκ hβ hρ0 hρ1 hom0 hom1
    (i := fun t _ => r t) (s := fun _ _ => (0 : ℝ)) (vm1 := 0) (qm1 := 0) (fun _ => rfl)
    (Mi := M) (fun t _ => hrb t) (fun _ => rfl) (Ms := 0) (by simp) rfl (Mv := 0) (by simp) rfl
    (Mq := 0) (by simp)
  obtain ⟨xV, pV, vV, qV, rnV, ⟨hV, -, -, hpV, hvV, hqV⟩, huV⟩ :=
    ltd_determinate perfectForesight hσ hκ hβ hρ0 hρ1 hom0 hom1
      (i := fun t _ => r t) (s := fun _ _ => (0 : ℝ)) (vm1 := 0) (qm1 := 0) (fun _ => rfl)
      (Mi := M) (fun t _ => hrb t) (fun _ => rfl) (Ms := 0) (by simp) rfl (Mv := 0) (by simp) rfl
      (Mq := 0) (by simp)
  obtain ⟨-, hp1, -, hq1, -⟩ := huV _ _ _ _ _ hY (fun _ => rfl) (hbd hpb hpUb) (hbd hvb hvUb)
    (hbd hqb hqUb)
  obtain ⟨-, hp2, -, hq2, -⟩ := huV _ _ _ _ _ hU (fun _ => rfl) hpUb hvUb hqUb
  have ep1 := congrFun (congrFun hp1 t) ()
  have ep2 := congrFun (congrFun hp2 t) ()
  have eq1 := congrFun (congrFun hq1 t) ()
  have eq2 := congrFun (congrFun hq2 t) ()
  constructor <;> linarith

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Fig. 5.2: an anticipated rise -/

/-- Cochrane (2023), Fig. 5.2, p. 124, **as forecast revisions in a probability model**: at date
1 the news `ε` (bounded, `𝓕₁`-measurable, `E_0 ε = 0`) announces a rise of the rate to `ε` from
date `1 + S` on (`i_t = ε` for `t ≥ 1 + S`, else `0`); no surpluses, `b₀ = 0`. In every bounded
equilibrium, a.e., `E_0 π_{1+j} = 0` and `E_1 π_{1+j} = ε · antPi S j`. -/
theorem fig52_response {σ β κ ρ B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (Sd : ℕ) {ε : Ω → ℝ} (hεm : StronglyMeasurable[S.𝓕 1] ε)
    (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B) (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ (fun t => if 1 + Sd ≤ t then ε else 0) 0 0 x p v)
    (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, ∀ j, S.E 0 (p (1 + j)) ω = 0 ∧ S.E 1 (p (1 + j)) ω = ε ω * antPi σ β κ ρ Sd j := by
  set i : ℕ → Ω → ℝ := fun t => if 1 + Sd ≤ t then ε else 0
  have hεi : Integrable ε S.μ :=
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable hεm hεb).integrable
  have hia : StronglyAdapted S.𝓕 i := by
    intro t
    by_cases ht : 1 + Sd ≤ t
    · simp only [i, ht, ↓reduceIte]
      exact hεm.mono (S.𝓕.mono (by omega))
    · simp only [i, ht, ↓reduceIte]
      exact stronglyMeasurable_zero
  have hib : S.BddProc i := ⟨|B|, fun t => by
    filter_upwards [hεb] with ω h1
    by_cases ht : 1 + Sd ≤ t
    · simp only [i, ht, ↓reduceIte]
      exact h1.trans (le_abs_self B)
    · simp [i, ht]⟩
  have hsa : StronglyAdapted S.𝓕 (0 : ℕ → Ω → ℝ) := fun t => stronglyMeasurable_const
  have hsb : S.BddProc (0 : ℕ → Ω → ℝ) := mbdd_zero S
  -- date-0 forecasts are zero
  have h0 := forecast_closed_form S hσ hκ hβ hρ0 hρ1 h hia hib hsa hsb hvb 0
    (fun _ => 0) (fun _ _ => 0) (fun _ => ⟨0, fun _ => by simp⟩) (by
      filter_upwards [hε0] with ω e k
      by_cases hk : 1 + Sd ≤ 0 + k
      · simp only [i, hk, ↓reduceIte]
        exact e
      · simp only [i, hk, ↓reduceIte]
        rw [S.E_zero]
        rfl) (Eventually.of_forall fun ω k => by simp [S.E_zero])
  have hb0 := bHat_zero S h hsa hsb hvb
  have hb1 := bHat_succ S h hsa hsb hvb 0
  have hpv0 : ∀ᵐ ω ∂S.μ, v 0 ω = 0 := by
    filter_upwards [h0, hb0] with ω e1 e2
    have := (e1 0).2.2
    rw [E_self S h.2.2.2.2.2.1 hvb 0] at this
    rw [this, vDet, e2]
    simp [pvS]
  -- the unit announced rise
  obtain ⟨⟨xU, pU, vU, hU, hpU, hvU⟩, hUform⟩ := anticipated_rise perfectForesight hσ hκ hβ
    hρ0 hρ1 Sd
  filter_upwards [h0, pf_forecast S h hia hib hsa hsb hvb 1, hb0, hb1, hpv0]
    with ω e0 ⟨hpf, hpb, hvb'⟩ eb0 eb1 ev0 j
  refine ⟨?_, ?_⟩
  · have := (e0 (1 + j)).1
    rw [zero_add] at this
    rw [this, piDet, eb0]
    simp [pvS]
  · have hi : (fun k (_ : Unit) => S.E 1 (i (1 + k)) ω) =
        fun k _ => ε ω * (if Sd ≤ k then 1 else 0) := by
      funext k u
      by_cases hk : Sd ≤ k
      · simp only [i, show 1 + Sd ≤ 1 + k by omega, ↓reduceIte, hk, mul_one]
        rw [S.E_of_stronglyMeasurable hεm hεi]
      · simp only [i, show ¬ (1 + Sd ≤ 1 + k) by omega, ↓reduceIte, hk, mul_zero]
        rw [S.E_zero]
        rfl
    have hs : (fun k (_ : Unit) => S.E 1 ((0 : ℕ → Ω → ℝ) (1 + k)) ω) = fun _ _ => (0 : ℝ) := by
      funext k u
      simp [S.E_zero]
    have hb : bHat S ρ 0 v p 1 ω = 0 := by
      rw [eb1, ev0]
      simp [i]
    rw [hi, hs, hb] at hpf
    have hsc := ftplnk_pf_scale hσ hκ hβ hρ0 hρ1 (c := ε ω) (r := fun k => if Sd ≤ k then 1 else 0)
      (M := 1) (fun k => by split_ifs <;> simp) hpf hpb hvb' hU hpU hvU j
    rw [hsc.1, hUform xU pU vU hU hpU hvU j ()]

/-! ### §5.3: the joint monetary–fiscal contraction -/

/-- Cochrane (2023), §5.3, p. 132 ("a joint monetary-fiscal contraction"), **as forecast
revisions in a probability model**: a date-1 news `ε` (bounded, `𝓕₁`-measurable, `E_0 ε = 0`)
raises the rate to `ε` from date 1 on and moves surpluses by `ε s̃_{t−1}` (`s̃` bounded with
present value `S`); `b₀ = 0`. In every bounded equilibrium, a.e., `E_0 π_{1+j} = 0` and
`E_1 π_{1+j} = ε (1 − (1 − ρ/λ₁)(1 + S) λ₁^{−j})` (`HigherOrLower.joint_contraction`). -/
theorem joint_contraction_response {σ β κ ρ B Ms : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ε : Ω → ℝ} (hεm : StronglyMeasurable[S.𝓕 1] ε)
    (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B) (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {sv : ℕ → ℝ}
    (hsv : ∀ j, |sv j| ≤ Ms) {x p v : ℕ → Ω → ℝ}
    (h : MFTPLNK S σ β κ ρ (fun t => if t = 0 then 0 else ε)
      (fun t ω => if t = 0 then 0 else ε ω * sv (t - 1)) 0 x p v) (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, ∀ j, S.E 0 (p (1 + j)) ω = 0 ∧ S.E 1 (p (1 + j)) ω =
      ε ω * (1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (1 + pvS ρ sv) * (lam1 σ β κ)⁻¹ ^ j) := by
  set i : ℕ → Ω → ℝ := fun t => if t = 0 then 0 else ε
  set s : ℕ → Ω → ℝ := fun t ω => if t = 0 then 0 else ε ω * sv (t - 1)
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
  have hsa : StronglyAdapted S.𝓕 s := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · simp only [s, ht, ↓reduceIte]
      exact stronglyMeasurable_const
    · simp only [s, ht.ne', ↓reduceIte]
      exact (hεm.mono (S.𝓕.mono ht)).mul stronglyMeasurable_const
  have hMs : 0 ≤ Ms := (abs_nonneg _).trans (hsv 0)
  have hsb : S.BddProc s := ⟨|B| * Ms, fun t => by
    filter_upwards [hεb] with ω h1
    by_cases ht : t = 0
    · simp only [s, ht, ↓reduceIte, abs_zero]
      positivity
    · simp only [s, ht, ↓reduceIte, abs_mul]
      exact mul_le_mul (h1.trans (le_abs_self B)) (hsv _) (abs_nonneg _) (abs_nonneg _)⟩
  have hEs0 : ∀ k, ∀ᵐ ω ∂S.μ, S.E 0 (s (0 + k)) ω = 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · refine Eventually.of_forall fun ω => ?_
      simp only [zero_add, hk, s, ↓reduceIte]
      rw [S.E_const]
    · have hfun : s (0 + k) = (sv (k - 1)) • ε := by
        funext ω
        simp only [zero_add, s, hk.ne', ↓reduceIte, Pi.smul_apply, smul_eq_mul]
        ring
      filter_upwards [S.E_smul (sv (k - 1)) ε 0, hε0] with ω e1 e2
      rw [hfun, e1, Pi.smul_apply, e2, Pi.zero_apply, smul_zero]
  have h0 := forecast_closed_form S hσ hκ hβ hρ0 hρ1 h hia hib hsa hsb hvb 0
    (fun _ => 0) (fun _ _ => 0) (fun _ => ⟨0, fun _ => by simp⟩) (by
      filter_upwards [hε0] with ω e k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · simp only [zero_add, hk, i, ↓reduceIte]
        rw [S.E_zero]
        rfl
      · simp only [zero_add, i, hk.ne', ↓reduceIte]
        exact e) (ae_all_iff.2 hEs0)
  have hb0 := bHat_zero S h hsa hsb hvb
  have h1 := forecast_closed_form S hσ hκ hβ hρ0 hρ1 h hia hib hsa hsb hvb 1
    ε (fun ω j => ε ω * sv j) (fun ω => ⟨|ε ω| * Ms, fun j => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hsv j) (abs_nonneg _)⟩)
    (Eventually.of_forall fun ω k => by
      simp only [i, show 1 + k ≠ 0 by omega, ↓reduceIte]
      rw [S.E_of_stronglyMeasurable hεm hεi])
    (Eventually.of_forall fun ω k => by
      have hfun : s (1 + k) = fun ω => ε ω * sv k := by
        funext ω
        simp only [s, show 1 + k ≠ 0 by omega, ↓reduceIte, show 1 + k - 1 = k by omega]
      rw [hfun]
      exact congrFun (S.E_of_stronglyMeasurable (x := fun ω => ε ω * sv k)
        (hεm.mul stronglyMeasurable_const) (hεi.mul_const (sv k))) ω)
  have hb1 := bHat_succ S h hsa hsb hvb 0
  have hpv0 : ∀ᵐ ω ∂S.μ, v 0 ω = 0 := by
    filter_upwards [h0, hb0] with ω e1 e2
    have := (e1 0).2.2
    rw [E_self S h.2.2.2.2.2.1 hvb 0] at this
    rw [this, vDet, e2]
    simp [pvS]
  have hpvε : ∀ ω, pvS ρ (fun j => ε ω * sv j) = ε ω * pvS ρ sv := by
    intro ω
    rw [pvS, show (fun j => ρ ^ j * (ε ω * sv j)) = fun j => ε ω * (ρ ^ j * sv j) by
      funext j; ring, tsum_mul_left, ← pvS]
  filter_upwards [h0, h1, hb0, hb1, hpv0] with ω e0 e1 eb0 eb1 ev0 j
  refine ⟨?_, ?_⟩
  · have := (e0 (1 + j)).1
    rw [zero_add] at this
    rw [this, piDet, eb0]
    simp [pvS]
  · rw [(e1 j).1, piDet, eb1, ev0, hpvε]
    simp only [i, ↓reduceIte, zero_add, Pi.zero_apply]
    ring

/-! ### §5.3: a persistent (AR(1)) rise with long-term debt -/

/-- Cochrane (2023), §5.3, p. 131 (`LongTermDebt.ltd_ar1`), **as forecast revisions in a
probability model**: with long-term debt (`0 ≤ ω̃ < 1`), a date-1 news `ε` (bounded,
`𝓕₁`-measurable, `E_0 ε = 0`) starts an AR(1) rate path `i_{1+k} = ε ηᵏ` (`0 ≤ η < 1`,
`λ₁η ≠ 1`), no surpluses, zero pre-sample values. In every bounded equilibrium, a.e.,
`E_0 π_{1+j} = 0` and `E_1 π_{1+j} = ε (A ηʲ + C λ₁^{−j})`. -/
theorem ltd_ar1_response {σ β κ ρ om η B : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hres : lam1 σ β κ * η ≠ 1) {ε : Ω → ℝ} (hεm : StronglyMeasurable[S.𝓕 1] ε)
    (hεb : ∀ᵐ ω ∂S.μ, |ε ω| ≤ B) (hε0 : S.E 0 ε =ᵐ[S.μ] 0) {x p v q rn : ℕ → Ω → ℝ}
    (h : MLTD S σ β κ ρ om (fun t => if t = 0 then 0 else η ^ (t - 1) • ε) 0 0 0 x p v q rn)
    (hvb : S.BddProc v) :
    ∀ᵐ ω ∂S.μ, ∀ j, S.E 0 (p (1 + j)) ω = 0 ∧
      S.E 1 (p (1 + j)) ω =
        ε ω * (ar1A σ β κ η * η ^ j + ar1C σ β κ ρ om η * (lam1 σ β κ)⁻¹ ^ j) := by
  set i : ℕ → Ω → ℝ := fun t => if t = 0 then 0 else η ^ (t - 1) • ε
  have hεi : Integrable ε S.μ :=
    (MeasExpectationSystem.BddRV.of_stronglyMeasurable hεm hεb).integrable
  have hηp : ∀ k, |η ^ k| ≤ 1 := fun k => by
    rw [abs_pow, abs_of_nonneg hη0]
    exact pow_le_one₀ hη0 hη1.le
  have hia : StronglyAdapted S.𝓕 i := by
    intro t
    rcases Nat.eq_zero_or_pos t with ht | ht
    · simp only [i, ht, ↓reduceIte]
      exact stronglyMeasurable_const
    · simp only [i, ht.ne', ↓reduceIte]
      exact (hεm.mono (S.𝓕.mono ht)).const_smul _
  have hib : S.BddProc i := ⟨|B|, fun t => by
    filter_upwards [hεb] with ω h1
    by_cases ht : t = 0
    · simp [i, ht]
    · simp only [i, ht, ↓reduceIte, Pi.smul_apply, smul_eq_mul, abs_mul]
      calc |η ^ (t - 1)| * |ε ω| ≤ 1 * |B| :=
            mul_le_mul (hηp _) (h1.trans (le_abs_self B)) (abs_nonneg _) zero_le_one
        _ = |B| := one_mul _⟩
  have hsa : StronglyAdapted S.𝓕 (0 : ℕ → Ω → ℝ) := fun t => stronglyMeasurable_const
  have hsb : S.BddProc (0 : ℕ → Ω → ℝ) := mbdd_zero S
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
    · filter_upwards [S.E_smul (η ^ (k - 1)) ε 0, hε0] with ω e1 e2
      simp only [zero_add, i, hk.ne', ↓reduceIte]
      rw [e1, Pi.smul_apply, e2, Pi.zero_apply, smul_zero]
  have hzero : ∀ s0 k (ω : Ω), S.E s0 ((0 : ℕ → Ω → ℝ) (s0 + k)) ω = 0 := fun s0 k ω => by
    simp [S.E_zero]
  -- the unit AR(1) path
  obtain ⟨xU, pU, vU, qU, rnU, ⟨hU, -, -, hpU, hvU, hqU⟩, -⟩ :=
    ltd_determinate perfectForesight hσ hκ hβ hρ0 hρ1 hom0 hom1
      (i := fun t _ => η ^ t) (s := fun _ _ => (0 : ℝ)) (vm1 := 0) (qm1 := 0) (fun _ => rfl)
      (Mi := 1) (fun t _ => hηp t) (fun _ => rfl) (Ms := 0) (by simp) rfl (Mv := 0) (by simp) rfl
      (Mq := 0) (by simp)
  filter_upwards [ltd_forecast S h hia hib hsa hsb hvb hrna hrnb 0,
    ltd_forecast S h hia hib hsa hsb hvb hrna hrnb 1, vqHat_zero S h hsa hsb hvb hrna hrnb,
    vqHat_succ S h hsa hsb hvb hrna hrnb 0, ae_all_iff.2 hEi0] with ω ⟨f0, b0p, b0v, b0q⟩
    ⟨f1, b1p, b1v, b1q⟩ ⟨ev0, eq0⟩ ⟨ev1, eq1⟩ ei0
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
  have hv0 : v 0 ω = 0 := by
    have := (P0 0).2.2
    simp only [zero_add] at this
    rw [show S.E 0 (v 0) ω = v 0 ω from by rw [E_self S hva hvb 0]] at this
    rw [this]
    ring
  have hq0' : q 0 ω = 0 := by
    have := (P0 0).1
    simp only [zero_add] at this
    rw [show S.E 0 (q 0) ω = q 0 ω from by rw [E_self S hqa ⟨Mq, hMq⟩ 0]] at this
    rw [this]
    ring
  have hi1 : (fun k (_ : Unit) => S.E 1 (i (1 + k)) ω) = fun k _ => ε ω * η ^ k := by
    funext k u
    simp only [i, show 1 + k ≠ 0 by omega, ↓reduceIte, show 1 + k - 1 = k by omega]
    rw [S.E_of_stronglyMeasurable (hεm.const_smul _) (hεi.smul _), Pi.smul_apply, smul_eq_mul,
      mul_comm]
  have hs1 : (fun k (_ : Unit) => S.E 1 ((0 : ℕ → Ω → ℝ) (1 + k)) ω) = fun _ _ => (0 : ℝ) := by
    funext k u
    exact hzero 1 k ω
  rw [hi1, hs1, ev1, eq1, hv0, hq0'] at f1
  have f1' := f1
  change LTD perfectForesight σ β κ ρ om (fun k _ => ε ω * η ^ k) (fun _ _ => 0) 0 0
    _ _ _ _ _ at f1'
  intro j
  refine ⟨?_, ?_⟩
  · have := (P0 (1 + j)).2.1
    rw [zero_add] at this
    rw [this]
    ring
  · have hsc := ltd_pf_scale hσ hκ hβ hρ0 hρ1 hom0 hom1 (c := ε ω) (r := fun k => η ^ k) (M := 1)
      hηp f1' b1p b1v b1q hU hpU hvU hqU j
    rw [hsc.1, (ltd_ar1 perfectForesight hσ hκ hβ hρ0 hρ1 hom0 hom1 hη0 hη1 hres hU
      (fun _ => rfl) hpU hvU hqU j ()).2]

end Cochrane.StickyPriceFiscal.TidyR6MeasPathForecasts
