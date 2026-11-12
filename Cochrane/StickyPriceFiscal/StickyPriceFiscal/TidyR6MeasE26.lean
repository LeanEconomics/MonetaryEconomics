/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasFiscalNK
import StickyPriceFiscal.ExpectationsMeasureIID

/-!
# Survey error E26 in a genuine probability model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1.1, eqs. (5.5) and (5.7),
pp. 119–120. In the two-sided moving average (5.5) the shock `δ_{t+1}` and unexpected inflation
`ΔE_{t+1}π_{t+1}` differ by the news about future rates (survey E26;
`TwoSidedMA.delta_eq_innov_iff`, and `TwoSidedMA.e26_coin` on a coin-flip tree). Here the same is
proved with Mathlib's conditional expectation.

In a bounded equilibrium of (5.1)–(5.2), with `F²_t = E_t ∑ λ₂ᵏ i_{t+k}` and
`c = σκ/(λ₁ − λ₂)` (`TwoSidedMA.coef`), (5.5) at `t + 1` defines the book's shock
`δ_{t+1} = π_{t+1} − λ₁⁻¹π_t − c(i_t + λ₂F²_{t+1} − λ₁⁻¹λ₂F²_t)` (`bookDelta`).

## Main results

* `forwardSol_lU`: the forward-solved rate term of `TidyR6MeasFiscalNK` is `−σλ₂ F²`.
* **`mbookDelta_mds`**: `E_t δ_{t+1} = 0` a.e. (`δ` is a martingale difference, as (5.5) needs);
* **`minnov_decomp`** ((5.7)): `ΔE_{t+1}π_{t+1} = δ_{t+1} + cλ₂ ΔE_{t+1}F²_{t+1}` a.e.;
  `mdelta_eq_innov_iff`: `δ_{t+1} = ΔE_{t+1}π_{t+1}` a.e. iff the rate news term vanishes a.e.;
* **`iid_e26`**: in the i.i.d. economy with rate shocks `i_t = ε_t` (bounded, mean zero, positive
  variance), every bounded equilibrium has `δ_1 ≠ ΔE_1π_1` on a set of positive probability, and
  such equilibria exist.
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasE26

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRulesMeasure NKModel
  TidyR6MeasFiscalNK

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eq. (5.5), p. 119: the book's shock in (5.5) at `t + 1`,
`δ_{t+1} = π_{t+1} − λ₁⁻¹π_t − c(i_t + λ₂F²_{t+1} − λ₁⁻¹λ₂F²_t)`. -/
noncomputable def bookDelta (σ β κ : ℝ) (i p : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := fun ω =>
  p (t + 1) ω - (lam1 σ β κ)⁻¹ * p t ω - TwoSidedMA.coef σ β κ * (i t ω +
    lam2 σ β κ * S.forwardSol (lam2 σ β κ) i (t + 1) ω -
    (lam1 σ β κ)⁻¹ * lam2 σ β κ * S.forwardSol (lam2 σ β κ) i t ω)

/-- Cochrane (2023), eq. (5.5) (tool): the forward-solved rate term used by
`TidyR6MeasFiscalNK.mnk_characterization` is `−σλ₂ F²` a.e. -/
theorem forwardSol_lU {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i) (t : ℕ) :
    S.forwardSol (lU σ β κ)⁻¹ (fun t => (-(σ / lU σ β κ)) • i t) t =ᵐ[S.μ]
      (-(σ * lam2 σ β κ)) • S.forwardSol (lam2 σ β κ) i t := by
  have ha := mul_pos hσ hκ
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl : |lam2 σ β κ| < 1 := by rw [abs_of_pos h2]; exact h21
  have e1 : (lU σ β κ)⁻¹ = lam2 σ β κ := by simp [lU]
  have e2 : σ / lU σ β κ = σ * lam2 σ β κ := by simp [lU, div_inv_eq_mul]
  rw [e1, e2]
  obtain ⟨Mi, hMi⟩ := hib
  set c := -(σ * lam2 σ β κ)
  have hb1 : ∀ t, ∀ᵐ ω ∂S.μ, |((fun t => c • i t) t) ω| ≤ |c| * Mi := fun t => by
    filter_upwards [hMi t] with ω h
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
  have hF := S.forwardSol_solves hl hia hMi
  have hG : S.Solves (lam2 σ β κ) (fun t => c • i t) (fun t => c • S.forwardSol (lam2 σ β κ) i t) :=
    fun t => by
      filter_upwards [hF t, S.E_smul c (S.forwardSol (lam2 σ β κ) i (t + 1)) t] with ω e1 e2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      rw [e2, e1]
      ring
  have hFb : S.BddProc (S.forwardSol (lam2 σ β κ) i) := S.forwardSol_bdd hl hMi
  exact S.forward_unique hl (S.forwardSol_solves hl (fun t => (hia t).const_smul c) hb1) hG
    (fun t => ((S.forwardSol_adapted _ _ t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => (((S.forwardSol_adapted _ _ t).mono (S.𝓕.le t)).const_smul c).aestronglyMeasurable)
    (S.forwardSol_bdd hl hb1) (mbdd_smul S c hFb) t

/-- Cochrane (2023), eq. (5.5) (tool, the algebra of `mbookDelta_mds`): with `c(λ₁ − λ₂) = σκ`
and `λ₁λ₂ = β`, the forecast of the book's shock vanishes. -/
theorem alg_e26 {l1 l2 c σ κ β P F EF : ℝ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0)
    (hc : c * (l1 - l2) = σ * κ) (hp : l1 * l2 = β) :
    l1⁻¹ * P - κ / β * (-(σ * l2) * F) -
      (l1⁻¹ * P + c * (F - l2 * EF - l1⁻¹ * l2 * F)) - c * l2 * EF = 0 := by
  have key : l1⁻¹ * P - κ / β * (-(σ * l2) * F) -
      (l1⁻¹ * P + c * (F - l2 * EF - l1⁻¹ * l2 * F)) - c * l2 * EF =
      F / l1 * (σ * κ - c * (l1 - l2)) := by
    rw [← hp]
    field_simp
    ring
  rw [key, hc, sub_self, mul_zero]

/-- Cochrane (2023), eq. (5.5), p. 119, **in a probability model**: in every bounded adapted
equilibrium of (5.1)–(5.2) the book's shock is a martingale difference, `E_t δ_{t+1} = 0` a.e. -/
theorem mbookDelta_mds {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i x p : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i) (hxa : StronglyAdapted S.𝓕 x)
    (hpa : StronglyAdapted S.𝓕 p) (hxb : S.BddProc x) (hpb : S.BddProc p)
    (h : MNK S σ β κ i x p) (t : ℕ) :
    S.E t (bookDelta S σ β κ i p t) =ᵐ[S.μ] 0 := by
  have ha := mul_pos hσ hκ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have h2 := lam2_pos ha hβ
  have hl : |lam2 σ β κ| < 1 := by rw [abs_of_pos h2]; exact lam2_lt_one ha hβ
  obtain ⟨-, hEp⟩ := (mnk_characterization S hσ hκ hβ hia hib hxa hpa hxb hpb).1 h
  set F2 := S.forwardSol (lam2 σ β κ) i
  obtain ⟨Mi, hMi⟩ := hib
  have hF2s := S.forwardSol_solves hl hia hMi
  have hF2a : StronglyAdapted S.𝓕 F2 := S.forwardSol_adapted _ _
  have hF2i := int_of S hF2a (S.forwardSol_bdd hl hMi)
  have hpi := int_of S hpa hpb
  have hii := int_of S hia ⟨Mi, hMi⟩
  set c := TwoSidedMA.coef σ β κ
  have hc := TwoSidedMA.coef_mul ha hβ
  have hprod := lam_prod ha hβ
  -- `bookDelta = π_{t+1} − (known) − cλ₂ F²_{t+1}`
  set k : Ω → ℝ := fun ω => (lam1 σ β κ)⁻¹ * p t ω + c * (i t ω - (lam1 σ β κ)⁻¹ *
    lam2 σ β κ * F2 t ω)
  have hkm : StronglyMeasurable[S.𝓕 t] k :=
    ((hpa t).const_mul _).add (((hia t).sub (((hF2a t).const_mul _))).const_mul _)
  have hki : Integrable k S.μ := ((hpi t).const_mul _).add (((hii t).sub
    ((hF2i t).const_mul _)).const_mul _)
  have hd : bookDelta S σ β κ i p t = p (t + 1) - k - (c * lam2 σ β κ) • F2 (t + 1) := by
    funext ω
    simp only [bookDelta, k, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, F2]
    ring
  rw [hd]
  filter_upwards [S.E_sub ((hpi (t + 1)).sub hki) ((hF2i (t + 1)).smul (c * lam2 σ β κ)) t,
    S.E_sub (hpi (t + 1)) hki t, S.E_smul (c * lam2 σ β κ) (F2 (t + 1)) t, hEp t, hF2s t,
    forwardSol_lU S hσ hκ hβ hia ⟨Mi, hMi⟩ t] with ω e1 e2 e3 e4 e5 e6
  rw [e1, Pi.sub_apply, e2, Pi.sub_apply, e3, S.E_of_stronglyMeasurable hkm hki, e4]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.zero_apply] at e5 e6 ⊢
  rw [e6]
  simp only [k]
  have hFt : F2 t ω = lam2 σ β κ * S.E t (F2 (t + 1)) ω + i t ω := e5
  have hI : i t ω = F2 t ω - lam2 σ β κ * S.E t (F2 (t + 1)) ω := by linarith
  rw [lS, hI]
  exact alg_e26 hl0 h2.ne' hc hprod

/-- Cochrane (2023), eq. (5.7), p. 120, **in a probability model**: unexpected inflation is the
book's shock plus the rate news, `ΔE_{t+1}π_{t+1} = δ_{t+1} + cλ₂ ΔE_{t+1}F²_{t+1}` a.e. -/
theorem minnov_decomp {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i x p : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i) (hxa : StronglyAdapted S.𝓕 x)
    (hpa : StronglyAdapted S.𝓕 p) (hxb : S.BddProc x) (hpb : S.BddProc p)
    (h : MNK S σ β κ i x p) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, p (t + 1) ω - S.E t (p (t + 1)) ω = bookDelta S σ β κ i p t ω +
      TwoSidedMA.coef σ β κ * lam2 σ β κ * (S.forwardSol (lam2 σ β κ) i (t + 1) ω -
        S.E t (S.forwardSol (lam2 σ β κ) i (t + 1)) ω) := by
  have ha := mul_pos hσ hκ
  have h2 := lam2_pos ha hβ
  have hl : |lam2 σ β κ| < 1 := by rw [abs_of_pos h2]; exact lam2_lt_one ha hβ
  set F2 := S.forwardSol (lam2 σ β κ) i
  obtain ⟨Mi, hMi⟩ := hib
  have hF2a : StronglyAdapted S.𝓕 F2 := S.forwardSol_adapted _ _
  have hF2i := int_of S hF2a (S.forwardSol_bdd hl hMi)
  have hpi := int_of S hpa hpb
  have hii := int_of S hia ⟨Mi, hMi⟩
  set c := TwoSidedMA.coef σ β κ
  set k : Ω → ℝ := fun ω => (lam1 σ β κ)⁻¹ * p t ω + c * (i t ω - (lam1 σ β κ)⁻¹ *
    lam2 σ β κ * F2 t ω)
  have hkm : StronglyMeasurable[S.𝓕 t] k :=
    ((hpa t).const_mul _).add (((hia t).sub (((hF2a t).const_mul _))).const_mul _)
  have hki : Integrable k S.μ := ((hpi t).const_mul _).add (((hii t).sub
    ((hF2i t).const_mul _)).const_mul _)
  have hd : bookDelta S σ β κ i p t = p (t + 1) - k - (c * lam2 σ β κ) • F2 (t + 1) := by
    funext ω
    simp only [bookDelta, k, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, F2]
    ring
  have hmds := mbookDelta_mds S hσ hκ hβ hia ⟨Mi, hMi⟩ hxa hpa hxb hpb h t
  rw [hd] at hmds ⊢
  filter_upwards [hmds, S.E_sub ((hpi (t + 1)).sub hki) ((hF2i (t + 1)).smul (c * lam2 σ β κ)) t,
    S.E_sub (hpi (t + 1)) hki t, S.E_smul (c * lam2 σ β κ) (F2 (t + 1)) t] with ω e0 e1 e2 e3
  rw [e1, Pi.sub_apply, e2, Pi.sub_apply, e3, S.E_of_stronglyMeasurable hkm hki] at e0
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e0 ⊢
  linarith

/-- Cochrane (2023), p. 120, survey E26, **in a probability model**: `δ_{t+1} = ΔE_{t+1}π_{t+1}`
a.e. iff the rate news term `cλ₂ ΔE_{t+1}F²_{t+1}` vanishes a.e. -/
theorem mdelta_eq_innov_iff {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {i x p : ℕ → Ω → ℝ} (hia : StronglyAdapted S.𝓕 i) (hib : S.BddProc i)
    (hxa : StronglyAdapted S.𝓕 x) (hpa : StronglyAdapted S.𝓕 p) (hxb : S.BddProc x)
    (hpb : S.BddProc p) (h : MNK S σ β κ i x p) (t : ℕ) :
    (bookDelta S σ β κ i p t =ᵐ[S.μ] fun ω => p (t + 1) ω - S.E t (p (t + 1)) ω) ↔
      (fun ω => TwoSidedMA.coef σ β κ * lam2 σ β κ * (S.forwardSol (lam2 σ β κ) i (t + 1) ω -
        S.E t (S.forwardSol (lam2 σ β κ) i (t + 1)) ω)) =ᵐ[S.μ] 0 := by
  have hd := minnov_decomp S hσ hκ hβ hia hib hxa hpa hxb hpb h t
  constructor
  · intro h1
    filter_upwards [h1, hd] with ω e1 e2
    simp only [Pi.zero_apply]
    linarith
  · intro h1
    filter_upwards [h1, hd] with ω e1 e2
    simp only [Pi.zero_apply] at e1
    linarith

open ExpectationsMeasureIID in
/-- Cochrane (2023), p. 120, survey E26, **in the i.i.d. economy**: with rate shocks
`i_t = ε_t` (bounded, mean zero, positive variance), every bounded adapted equilibrium of
(5.1)–(5.2) has `δ_1 ≠ ΔE_1π_1` on a set of positive probability (`δ_1` is not a.e. the
unexpected inflation); and bounded equilibria exist (with the fiscal block of §5.1.2). -/
theorem iid_e26 (ν : ProbabilityMeasure ℝ) {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ2 : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) :
    (∀ x p : ℕ → (ℕ → ℝ) → ℝ, StronglyAdapted (iidSystem ν).𝓕 x →
      StronglyAdapted (iidSystem ν).𝓕 p → (iidSystem ν).BddProc x →
      (iidSystem ν).BddProc p → MNK (iidSystem ν) σ β κ shock x p →
      ¬ bookDelta (iidSystem ν) σ β κ shock p 0 =ᵐ[(iidSystem ν).μ]
        fun ω => p 1 ω - (iidSystem ν).E 0 (p 1) ω) ∧
    ∃ x p v, MEqm (iidSystem ν) σ β κ (1 / 2) shock 0 0 x p v ∧ (iidSystem ν).BddProc v := by
  set S := iidSystem ν
  have ha := mul_pos hσ hκ
  have h2 := lam2_pos ha hβ
  have hl : |lam2 σ β κ| < 1 := by rw [abs_of_pos h2]; exact lam2_lt_one ha hβ
  have hia : StronglyAdapted S.𝓕 shock := fun t => (measurable_shock ν le_rfl).stronglyMeasurable
  have hib : S.BddProc shock := ⟨B, fun t => shock_ae_bdd ν hbdd t⟩
  have hshi : ∀ t, Integrable (shock t) S.μ := int_of S hia hib
  -- `E_s ε_{s+1+j} = 0`
  have hEfut : ∀ s j, S.E s (shock (s + 1 + j)) =ᵐ[S.μ] 0 := by
    intro s j
    have hz := E_shock_zero hmean (ν := ν) (s + j)
    rw [show s + j + 1 = s + 1 + j by ring] at hz
    filter_upwards [(S.E_tower (Nat.le_add_right s j) (shock (s + 1 + j))).symm,
      S.E_congr hz s] with ω e1 e2
    rw [e1, e2, S.E_zero]
  -- `F²_1 = ε_1` and `E_0 F²_1 = 0`
  have hF1 : S.forwardSol (lam2 σ β κ) shock 1 =ᵐ[S.μ] shock 1 := by
    filter_upwards [S.forwardSol_hasSum hl (fun t => ((hia t).mono (S.𝓕.le t)).aestronglyMeasurable)
      (fun t => shock_ae_bdd ν hbdd t) 1, ae_all_iff.2 fun j => hEfut 1 j] with ω e1 e2
    have hterm : (fun k => lam2 σ β κ ^ k * S.E 1 (shock (1 + k)) ω) =
        fun k => if k = 0 then shock 1 ω else 0 := by
      funext k
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp [S.E_of_stronglyMeasurable (hia 1) (hshi 1)]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [show 1 + (j + 1) = 1 + 1 + j by ring, e2 j]
        simp
    rw [hterm] at e1
    exact e1.unique (hasSum_ite_eq 0 (shock 1 ω))
  have hE0F : S.E 0 (S.forwardSol (lam2 σ β κ) shock 1) =ᵐ[S.μ] 0 := by
    filter_upwards [S.E_congr hF1 0, E_shock_zero hmean 0] with ω e1 e2
    rw [e1, e2]
  have hcne : TwoSidedMA.coef σ β κ * lam2 σ β κ ≠ 0 :=
    mul_ne_zero (div_pos ha (sub_pos.mpr (lam2_lt_lam1 ha hβ))).ne' h2.ne'
  refine ⟨fun x p hxa hpa hxb hpb h hcon => ?_, ?_⟩
  · have hz := (mdelta_eq_innov_iff S hσ hκ hβ hia hib hxa hpa hxb hpb h 0).1 hcon
    refine shock_not_ae_E hmean hvar hσ2 0 ?_
    filter_upwards [hz, hF1, hE0F, E_shock_zero hmean 0] with ω e1 e2 e3 e4
    simp only [Pi.zero_apply] at e1 e3 e4 ⊢
    rw [e2, e3, sub_zero] at e1
    rw [e4]
    exact (mul_eq_zero.mp e1).resolve_left hcne
  · exact meqm_exists S hσ hκ hβ (by norm_num) (by norm_num) hia hib
      (fun t => stronglyMeasurable_const) (mbdd_zero S) stronglyMeasurable_const
      (B := 0) (Eventually.of_forall fun ω => by simp)

end Cochrane.StickyPriceFiscal.TidyR6MeasE26
