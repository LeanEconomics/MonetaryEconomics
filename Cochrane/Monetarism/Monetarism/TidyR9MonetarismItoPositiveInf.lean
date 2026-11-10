/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR9MonetarismItoPositive
import Monetarism.TidyR7MonetarismItoCexInf
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Positive diffusive `Λ/P` with time-varying loadings: disjoint diffusions and the infinite horizon

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.32)–(1.33). The positive analogues of economy 2
(`TidyR7MonetarismItoCex.disjModel`: both diffusive, `σ_Xσ_B = 0`) and economy 3
(`TidyR7MonetarismItoCexInf.infModel`: transversality holds, the book's (1.33) fails), built
with the time-dependent Itô formula (`TidyR9ItoFormulaVariants.itoProcess_comp_time`).

## The loadings

`ρ(x) = x²/(1 + x²)` for `x > 0`, `0` for `x ≤ 0` (`loadRho`): `C¹`, `0 ≤ ρ < 1`, `|ρ'| ≤ 1`.
`φ(u) = ρ(1 − u)` (`phiL`, vanishes on `[1, ∞)`, `φ(0) = ½`), `ψ(u) = ρ(u − 1)` (`psiL`, vanishes
on `(−∞, 1]`), so `φψ = 0`. `a₀ + g(u) sin W` is an Itô process with drift `(g' − ½g) sin W`
and diffusion `g cos W` (`itoProcess_affine_tsin`).

## Main results

* Economy 2⁺ (`disjPModel`): `P = 1`, `Λ/P = Λ = 2 + φ sin W ∈ [1, 3]`, the forced rate
  `i = −(φ' − φ/2) sin W/Λ` (`|i| ≤ 3/2`), `B = b + ψ sin W`, `M = M₀ − ψ sin W`, `s = iB`. Both
  `Λ/P` and bonds diffuse (`σ_X = φ cos W`, `σ_B = ψ cos W`), on disjoint time sets: the book's
  last line of (1.32) holds on every `[s, t]` (`disjP_1_32`), and the book's (1.33) holds iff
  transversality (`disjP_1_33`).
* Economy 3⁺ (`infPModel`): `Λ = 2 + φ sin W`, `B = −φ sin W`, `M = M₀ + φ sin W`. **The
  transversality condition holds exactly** (`n_TB_T = 0` for `T ≥ 1`, `infP_tvc`), the bracket
  `E∫_0^T σ_Xσ_B = −E∫_0^T φ²cos²W ≤ −E∫_0^1 φ²cos²W < 0` (`infP_bracket_le`), and **the book's
  (1.33) fails with `Λ/P ∈ [1, 3]` throughout** (`infP_book_fails`, `infP_headline`).
-/

namespace Cochrane.Monetarism.TidyR9MonetarismItoPositiveInf

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesSums Cochrane.Monetarism.TidyR7BrownianTools
  Cochrane.Monetarism.TidyR7BrownianQV Cochrane.Monetarism.TidyR7ItoL2
  Cochrane.Monetarism.TidyR7ItoSums Cochrane.Monetarism.TidyR7ItoIntegral
  Cochrane.Monetarism.TidyR7ItoUnbounded Cochrane.Monetarism.TidyR7ItoProducts
  Cochrane.Monetarism.TidyR7ItoProcess Cochrane.Monetarism.TidyR7ItoProductRule
  Cochrane.Monetarism.TidyR7MonetarismModel Cochrane.Monetarism.TidyR7MonetarismIto
  Cochrane.Monetarism.TidyR7MonetarismItoValuation
  Cochrane.Monetarism.TidyR7MonetarismItoCex Cochrane.Monetarism.TidyR7MonetarismItoCexInf
  Cochrane.Monetarism.TidyR7BrownianExist
  Cochrane.Monetarism.TidyR7BrownianSchauder Cochrane.Monetarism.TidyR9ItoFormula
  Cochrane.Monetarism.TidyR9ItoFormulaVariants Cochrane.Monetarism.TidyR9MonetarismItoPositive
open scoped ENNReal NNReal

/-! ## The loading `ρ` -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the loading** `ρ(x) = x²/(1 + x²)` for `x > 0`,
`0` for `x ≤ 0`. -/
noncomputable def loadRho (x : ℝ) : ℝ := if x ≤ 0 then 0 else x ^ 2 / (1 + x ^ 2)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the derivative of `loadRho`. -/
noncomputable def loadRho' (x : ℝ) : ℝ := if x ≤ 0 then 0 else 2 * x / (1 + x ^ 2) ^ 2

/-- Cochrane (2023), A1 §1.6, p. 567: `loadRho' = d loadRho`. -/
theorem hasDerivAt_loadRho (x : ℝ) : HasDerivAt loadRho (loadRho' x) x := by
  have h := hasDerivAt_ite_le (c := 0) (q := fun _ => 0) (r := fun x => x ^ 2 / (1 + x ^ 2))
    (q' := fun _ => 0) (r' := fun x => 2 * x / (1 + x ^ 2) ^ 2)
    (fun x _ => hasDerivAt_const x 0)
    (fun x _ => by
      have hx : (1 + x ^ 2) ≠ 0 := by positivity
      have h1 := HasDerivAt.div (hasDerivAt_pow 2 x) (HasDerivAt.const_add 1 (hasDerivAt_pow 2 x))
        hx
      convert h1 using 1
      field_simp
      push_cast
      ring)
    (by simp) (by simp) x
  exact h

/-- Cochrane (2023), A1 §1.6, p. 567: `loadRho` and `loadRho'` are continuous. -/
theorem continuous_loadRho : Continuous loadRho ∧ Continuous loadRho' := by
  refine ⟨continuous_iff_continuousAt.2 fun x => (hasDerivAt_loadRho x).continuousAt, ?_⟩
  refine Continuous.if_le continuous_const ?_ continuous_id continuous_const ?_
  · exact (continuous_const.mul continuous_id).div ((continuous_const.add
      (continuous_id.pow 2)).pow 2) fun x => by positivity
  · intro x hx
    simp [hx]

/-- Cochrane (2023), A1 §1.6, p. 567: `0 ≤ ρ ≤ 1` and `|ρ'| ≤ 1`. -/
theorem loadRho_bounds (x : ℝ) : 0 ≤ loadRho x ∧ loadRho x ≤ 1 ∧ |loadRho' x| ≤ 1 := by
  unfold loadRho loadRho'
  split_ifs with hx
  · simp
  · have h1 : 0 < 1 + x ^ 2 := by positivity
    refine ⟨by positivity, (div_le_one h1).2 (by linarith), ?_⟩
    have hx0 : 0 < x := not_le.1 hx
    rw [abs_of_pos (by positivity), div_le_one (by positivity)]
    nlinarith [sq_nonneg (x - 1), sq_nonneg x, mul_pos hx0 hx0]

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the loading of `Λ/P`, `φ(u) = ρ(1 − u)`. -/
noncomputable def phiL (u : ℝ) : ℝ := loadRho (1 - u)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the loading of bonds, `ψ(u) = ρ(u − 1)`. -/
noncomputable def psiL (u : ℝ) : ℝ := loadRho (u - 1)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: `φψ = 0` everywhere, `φ = 0` on `[1, ∞)`, and
`φ(0) = ψ(2) = ½`. -/
theorem loadings_props :
    (∀ u, phiL u * psiL u = 0) ∧ (∀ u, 1 ≤ u → phiL u = 0) ∧ phiL 0 = 1 / 2 ∧
      psiL 2 = 1 / 2 := by
  refine ⟨fun u => ?_, fun u hu => ?_, ?_, ?_⟩
  · unfold phiL psiL loadRho
    rcases le_total u 1 with h | h
    · simp only [show u - 1 ≤ 0 by linarith, ↓reduceIte, mul_zero]
    · simp only [show 1 - u ≤ 0 by linarith, ↓reduceIte, zero_mul]
  · unfold phiL loadRho
    simp only [show 1 - u ≤ 0 by linarith, ↓reduceIte]
  · unfold phiL loadRho
    norm_num
  · unfold psiL loadRho
    norm_num

/-! ## `a₀ + g(u) sin W` -/

/-- **Cochrane (2023), A1 §1.6, pp. 567–568 (time-varying loadings via Itô's formula with time
dependence): `a₀ + g(u) sin W` is an Itô process** on every `[s, t]`, `0 ≤ s ≤ t`, for `g ∈ C¹`
with `|g| ≤ L₀`, `|g'| ≤ L₁`: drift `(g' − ½g) sin W`, diffusion `g cos W`.
Generalises `TidyR9MonetarismItoPositive.itoProcess_affine_sin`. -/
theorem itoProcess_affine_tsin {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (a0 : ℝ) {g g' : ℝ → ℝ}
    (hg : ∀ u, HasDerivAt g (g' u) u) (cg' : Continuous g') {L0 L1 : ℝ}
    (hgb : ∀ u, |g u| ≤ L0) (hg'b : ∀ u, |g' u| ≤ L1) :
    ItoProcess gaussSeq bmF bmPath (fun u ω => a0 + g u * Real.sin (bmReal bmPath u ω))
      (fun u ω => (g' u - g u / 2) * Real.sin (bmReal bmPath u ω))
      (fun u ω => g u * Real.cos (bmReal bmPath u ω)) s t (L1 + L0 / 2) L0 := by
  have hBM := isPreBrownianReal_bmPath
  have h𝓕 := bmFiltrationReal_isBM hBM measurable_bmPath
  have cg : Continuous g := continuous_iff_continuousAt.2 fun u => (hg u).continuousAt
  have hsin : ∀ x, |Real.sin x| ≤ 1 := Real.abs_sin_le_one
  have hcos : ∀ x, |Real.cos x| ≤ 1 := Real.abs_cos_le_one
  have h := itoProcess_comp_time hBM measurable_bmPath h𝓕 hs hst
    (itoProcess_bm (t := t) hBM measurable_bmPath h𝓕 hs)
    (ae_of_all _ fun ω => (continuous_bmReal (continuous_bmPath ω)).continuousOn)
    (f := fun u x => a0 + g u * Real.sin x) (ft := fun u x => g' u * Real.sin x)
    (fx := fun u x => g u * Real.cos x) (fxx := fun u x => g u * -Real.sin x)
    (Lt := L1) (L1 := L0) (L2 := L0)
    (fun u x => HasDerivAt.const_add a0 (HasDerivAt.mul_const (hg u) (Real.sin x)))
    (fun u x => HasDerivAt.const_add a0 (HasDerivAt.const_mul (g u) (Real.hasDerivAt_sin x)))
    (fun u x => HasDerivAt.const_mul (g u) (Real.hasDerivAt_cos x))
    (continuous_const.add ((cg.comp continuous_fst).mul (Real.continuous_sin.comp
      continuous_snd)))
    ((cg'.comp continuous_fst).mul (Real.continuous_sin.comp continuous_snd))
    ((cg.comp continuous_fst).mul (Real.continuous_cos.comp continuous_snd))
    ((cg.comp continuous_fst).mul (Real.continuous_sin.comp continuous_snd).neg)
    (fun u _ x => by
      rw [abs_mul]
      exact (mul_le_mul (hg'b u) (hsin x) (abs_nonneg _) ((abs_nonneg _).trans
        (hg'b u))).trans_eq (mul_one _))
    (fun u _ x => by
      rw [abs_mul]
      exact (mul_le_mul (hgb u) (hcos x) (abs_nonneg _) ((abs_nonneg _).trans
        (hgb u))).trans_eq (mul_one _))
    (fun u _ x => by
      rw [abs_mul, abs_neg]
      exact (mul_le_mul (hgb u) (hsin x) (abs_nonneg _) ((abs_nonneg _).trans
        (hgb u))).trans_eq (mul_one _))
  have e1 : L1 + L0 * 0 + L0 / 2 * (1 * 1) = L1 + L0 / 2 := by ring
  have e2 : L0 * 1 = L0 := mul_one _
  rw [e1, e2] at h
  exact itoProcess_of_coeff_eq h (fun u ω => by ring) (fun u ω => by ring)

/-- Cochrane (2023), A1 §1.6, p. 567: `φ' = −ρ'(1 − u)`, `ψ' = ρ'(u − 1)`, with the bounds
`|φ|, |ψ| ≤ 1`, `|φ'|, |ψ'| ≤ 1`. -/
theorem loadings_deriv :
    (∀ u, HasDerivAt phiL (-loadRho' (1 - u)) u) ∧ (∀ u, HasDerivAt psiL (loadRho' (u - 1)) u) ∧
    Continuous (fun u => -loadRho' (1 - u)) ∧ Continuous (fun u => loadRho' (u - 1)) ∧
    (∀ u, |phiL u| ≤ 1 ∧ |psiL u| ≤ 1 ∧ |-loadRho' (1 - u)| ≤ 1 ∧ |loadRho' (u - 1)| ≤ 1) := by
  refine ⟨fun u => ?_, fun u => ?_, (continuous_loadRho.2.comp (continuous_const.sub
    continuous_id)).neg, continuous_loadRho.2.comp (continuous_id.sub continuous_const),
    fun u => ?_⟩
  · have h : HasDerivAt (fun u => loadRho (1 - u)) (loadRho' (1 - u) * -1) u :=
      (hasDerivAt_loadRho (1 - u)).comp u (HasDerivAt.const_sub 1 (hasDerivAt_id' u))
    rw [show -loadRho' (1 - u) = loadRho' (1 - u) * -1 by ring]
    exact h
  · exact HasDerivAt.comp_sub_const u 1 (hasDerivAt_loadRho (u - 1))
  · obtain ⟨a1, a2, a3⟩ := loadRho_bounds (1 - u)
    obtain ⟨b1, b2, b3⟩ := loadRho_bounds (u - 1)
    refine ⟨?_, ?_, by rw [abs_neg]; exact a3, b3⟩
    · rw [phiL, abs_of_nonneg a1]; exact a2
    · rw [psiL, abs_of_nonneg b1]; exact b2

/-! ## The SDF `Λ = 2 + φ sin W` and its rate -/

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: the SDF `Λ = Λ/P = 2 + φ(u) sin W ∈ [1, 3]`. -/
noncomputable abbrev tΛ : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => 2 + phiL u * Real.sin (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **the forced nominal rate**
`i = −(φ' − φ/2) sin W / Λ` (bond pricing `E_t d(Λ/P) = −i(Λ/P) dt`). -/
noncomputable abbrev tI : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => -((-loadRho' (1 - u) - phiL u / 2) * Real.sin (bmReal bmPath u ω)) / tΛ u ω

/-- Cochrane (2023), A1 §1.6, pp. 567–568: `1 ≤ Λ = Λ/P ≤ 3` for every time and state, and
`|i| ≤ 3/2`. -/
theorem tΛ_bounds (u : ℝ) (ω : ℕ → ℝ) :
    1 ≤ tΛ u ω ∧ tΛ u ω ≤ 3 ∧ disc tΛ (constP 1) u ω = tΛ u ω ∧ |tI u ω| ≤ 3 / 2 := by
  obtain ⟨-, -, -, -, h⟩ := loadings_deriv
  obtain ⟨h1, -, h3, -⟩ := h u
  have hs := Real.abs_sin_le_one (bmReal bmPath u ω)
  have hps : |phiL u * Real.sin (bmReal bmPath u ω)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul h1 hs (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hl := abs_le.1 hps
  have hL1 : 1 ≤ tΛ u ω := by simp only [tΛ]; linarith
  refine ⟨hL1, by simp only [tΛ]; linarith, by simp [disc], ?_⟩
  simp only [tI]
  have hpos : 0 < tΛ u ω := by linarith
  rw [abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos, abs_mul]
  have hc : |-loadRho' (1 - u) - phiL u / 2| ≤ 3 / 2 := by
    have := abs_sub (-loadRho' (1 - u)) (phiL u / 2)
    rw [abs_div, abs_two] at this
    linarith
  have := mul_le_mul hc hs (abs_nonneg _) (by norm_num)
  nlinarith

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: **`Λ/P = 2 + φ sin W` is an Itô process with
drift `−i(Λ/P)`** (the bond-pricing condition) and diffusion `φ cos W`, on every `[s, t]`,
`0 ≤ s ≤ t`. -/
theorem tΛ_ito {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoProcess gaussSeq bmF bmPath (disc tΛ (constP 1))
      (fun u ω => -(tI u ω * disc tΛ (constP 1) u ω))
      (fun u ω => phiL u * Real.cos (bmReal bmPath u ω)) s t (1 + 1 / 2) 1 := by
  obtain ⟨h1, -, h3, -, h5⟩ := loadings_deriv
  have h := itoProcess_affine_tsin hs hst 2 h1 h3 (fun u => (h5 u).1) (fun u => (h5 u).2.2.1)
  refine itoProcess_congr_Icc h hst (fun u _ ω => by simp [disc]) (fun u _ ω => ?_)
    (fun u _ ω => rfl)
  have hne : tΛ u ω ≠ 0 := by linarith [(tΛ_bounds u ω).1]
  have e : disc tΛ (constP 1) u ω = tΛ u ω := (tΛ_bounds u ω).2.2.1
  rw [e]
  simp only [tI]
  field_simp

/-! ## Economy 2⁺: both diffusive, on disjoint time sets -/

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: economy 2⁺ is a model with positive
diffusive `Λ/P` and diffusive bonds** on every `[s, t]`, `0 ≤ s ≤ t`: `P = 1`,
`Λ/P = 2 + φ sin W`, `i = tI`, `i^m = 0`, `s = iB`, `B = b + ψ sin W`, `M = M₀ − ψ sin W`. -/
theorem disjPModel (b M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ItoMonetaryModel gaussSeq bmF bmPath tΛ (constP 1)
      (fun u ω => b + psiL u * Real.sin (bmReal bmPath u ω))
      (fun u ω => M0 + (fun u => -psiL u) u * Real.sin (bmReal bmPath u ω)) tI (constP 0)
      (fun u ω => tI u ω * (b + psiL u * Real.sin (bmReal bmPath u ω)))
      (fun u ω => (loadRho' (u - 1) - psiL u / 2) * Real.sin (bmReal bmPath u ω))
      (fun u ω => psiL u * Real.cos (bmReal bmPath u ω))
      (fun u ω => ((fun u => -loadRho' (u - 1)) u - (fun u => -psiL u) u / 2)
        * Real.sin (bmReal bmPath u ω))
      (fun u ω => (fun u => -psiL u) u * Real.cos (bmReal bmPath u ω))
      (fun u ω => phiL u * Real.cos (bmReal bmPath u ω)) s t (1 + 1 / 2) 1 (1 + 1 / 2) 1
      (1 + 1 / 2) 1 := by
  obtain ⟨-, h2, -, h4, h5⟩ := loadings_deriv
  exact
    { P_pos := fun _ _ => one_pos
      disc_ito := tΛ_ito hs hst
      bonds_ito := itoProcess_affine_tsin hs hst b h2 h4 (fun u => (h5 u).2.1)
        (fun u => (h5 u).2.2.2)
      money_ito := itoProcess_affine_tsin hs hst M0 (g := fun u => -psiL u)
        (g' := fun u => -loadRho' (u - 1)) (fun u => HasDerivAt.neg (h2 u)) h4.neg
        (fun u => by rw [abs_neg]; exact (h5 u).2.1)
        (fun u => by rw [abs_neg]; exact (h5 u).2.2.2)
      flow_drift := fun u ω => by
        simp only [flowRate, constP]
        ring
      flow_diff := fun u ω => by ring }

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the book's last line of (1.32) holds in
economy 2⁺** on every `[s, t]`, `0 ≤ s < t`, although `Λ/P > 0` and bonds both diffuse:
`σ_Xσ_B = φψ cos²W = 0`.
An instance of `TidyR7MonetarismIto.ItoMonetaryModel.incr_1_32_ito_uncorrelated`. -/
theorem disjP_1_32 (b M0 : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    gaussSeq[fun ω => disc tΛ (constP 1) t ω * (b + psiL t * Real.sin (bmReal bmPath t ω))
        - disc tΛ (constP 1) s ω * (b + psiL s * Real.sin (bmReal bmPath s ω)) | bmF s]
      =ᵐ[gaussSeq]
      gaussSeq[fun ω => -(dtInt gaussSeq bmF (fun u ω =>
          tΛ u ω * (tI u ω * (b + psiL u * Real.sin (bmReal bmPath u ω)))
          - constP 0 u ω * disc tΛ (constP 1) u ω
            * (M0 + (fun u => -psiL u) u * Real.sin (bmReal bmPath u ω))) s t ω
        + moneyInt gaussSeq bmF bmPath tΛ (constP 1)
          (fun u ω => ((fun u => -loadRho' (u - 1)) u - (fun u => -psiL u) u / 2)
            * Real.sin (bmReal bmPath u ω))
          (fun u ω => (fun u => -psiL u) u * Real.cos (bmReal bmPath u ω)) s t ω) | bmF s] :=
  (disjPModel b M0 hs hst.le).incr_1_32_ito_uncorrelated isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hst
    (ae_of_all _ fun ω u _ => by
      have h := loadings_props.1 u
      calc phiL u * Real.cos (bmReal bmPath u ω) * (psiL u * Real.cos (bmReal bmPath u ω))
          = (phiL u * psiL u) * Real.cos (bmReal bmPath u ω) ^ 2 := by ring
        _ = 0 := by rw [h, zero_mul])

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: the book's (1.33) in economy 2⁺**: for `0 ≤ s`
and times `T_k ≥ s`, the book's limit form holds iff the transversality condition holds.
An instance of `TidyR7MonetarismItoValuation.valuation_1_33_ito_uncorrelated`. -/
theorem disjP_1_33 (b M0 : ℝ) {s : ℝ} (hs : 0 ≤ s) {T : ℕ → ℝ} (hT : ∀ k, s ≤ T k) :
    (∀ᵐ ω ∂gaussSeq, Tendsto (fun k => gaussSeq[flowItoBook gaussSeq bmF bmPath tΛ
      (constP 1) (fun u ω => M0 + (fun u => -psiL u) u * Real.sin (bmReal bmPath u ω))
      (constP 0) (fun u ω => tI u ω * (b + psiL u * Real.sin (bmReal bmPath u ω)))
      (fun u ω => ((fun u => -loadRho' (u - 1)) u - (fun u => -psiL u) u / 2)
        * Real.sin (bmReal bmPath u ω))
      (fun u ω => (fun u => -psiL u) u * Real.cos (bmReal bmPath u ω)) s (T k) | bmF s] ω)
      atTop (𝓝 (disc tΛ (constP 1) s ω * (b + psiL s * Real.sin (bmReal bmPath s ω))))) ↔
      ∀ᵐ ω ∂gaussSeq, Tendsto (fun k => gaussSeq[fun ω => disc tΛ (constP 1) (T k) ω
        * (b + psiL (T k) * Real.sin (bmReal bmPath (T k) ω)) | bmF s] ω) atTop (𝓝 0) :=
  valuation_1_33_ito_uncorrelated
    (σX := fun u ω => phiL u * Real.cos (bmReal bmPath u ω))
    (σB := fun u ω => psiL u * Real.cos (bmReal bmPath u ω))
    (fun _ hT' => disjPModel b M0 hs hT'.le) isPreBrownianReal_bmPath measurable_bmPath
    (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) hs hT
    (ae_of_all _ fun ω u _ => by
      have h := loadings_props.1 u
      calc phiL u * Real.cos (bmReal bmPath u ω) * (psiL u * Real.cos (bmReal bmPath u ω))
          = (phiL u * psiL u) * Real.cos (bmReal bmPath u ω) ^ 2 := by ring
        _ = 0 := by rw [h, zero_mul])

/-! ## Economy 3⁺: transversality holds, the book's (1.33) fails, `Λ/P ∈ [1, 3]` -/

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3⁺): bonds `B = −φ sin W` (`0` from time
`1` on). -/
noncomputable abbrev infPB : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => 0 + (fun u => -phiL u) u * Real.sin (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.31), p. 567 (economy 3⁺): money `M = M₀ + φ sin W`. -/
noncomputable abbrev infPM (M0 : ℝ) : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => M0 + phiL u * Real.sin (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3⁺): the diffusion of `Λ/P`,
`σ_X = φ cos W`. -/
noncomputable abbrev infPσX : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => phiL u * Real.cos (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3⁺): the diffusion of bonds,
`σ_B = −φ cos W`. -/
noncomputable abbrev infPσB : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => (fun u => -phiL u) u * Real.cos (bmReal bmPath u ω)

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3⁺): the drift of money,
`m = (φ' − φ/2) sin W`. -/
noncomputable abbrev infPm : ℝ → (ℕ → ℝ) → ℝ :=
  fun u ω => (-loadRho' (1 - u) - phiL u / 2) * Real.sin (bmReal bmPath u ω)

/-- **Cochrane (2023), A1 §1.6, (1.31)–(1.34), pp. 567–568: economy 3⁺ is a model with positive
diffusive `Λ/P`** on every `[0, T]`: `P = 1`, `Λ/P = 2 + φ sin W ∈ [1, 3]`, `i = tI`,
`i^m = 0`, `s = iB`, `B = −φ sin W` (`σ_B = −φ cos W`), `M = M₀ + φ sin W` (`σ_M = φ cos W`). -/
theorem infPModel (M0 : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ItoMonetaryModel gaussSeq bmF bmPath tΛ (constP 1) infPB (infPM M0) tI (constP 0)
      (fun u ω => tI u ω * infPB u ω)
      (fun u ω => ((fun u => -(-loadRho' (1 - u))) u - (fun u => -phiL u) u / 2)
        * Real.sin (bmReal bmPath u ω)) infPσB infPm infPσX infPσX 0 T
      (1 + 1 / 2) 1 (1 + 1 / 2) 1 (1 + 1 / 2) 1 := by
  obtain ⟨h1, -, h3, -, h5⟩ := loadings_deriv
  exact
    { P_pos := fun _ _ => one_pos
      disc_ito := tΛ_ito le_rfl hT
      bonds_ito := itoProcess_affine_tsin le_rfl hT 0 (g := fun u => -phiL u)
        (g' := fun u => -(-loadRho' (1 - u))) (fun u => HasDerivAt.neg (h1 u)) h3.neg
        (fun u => by rw [abs_neg]; exact (h5 u).1)
        (fun u => by rw [abs_neg]; exact (h5 u).2.2.1)
      money_ito := itoProcess_affine_tsin le_rfl hT M0 h1 h3 (fun u => (h5 u).1)
        (fun u => (h5 u).2.2.1)
      flow_drift := fun u ω => by
        simp only [flowRate, constP]
        ring
      flow_diff := fun u ω => by ring }

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3⁺): the models on `[0, T]`, `T > 0`, as
`TidyR7MonetarismItoValuation` requires. -/
theorem infPModels (M0 : ℝ) : ∀ T, (0 : ℝ) < T →
    ItoMonetaryModel gaussSeq bmF bmPath tΛ (constP 1) infPB (infPM M0) tI (constP 0)
      (fun u ω => tI u ω * infPB u ω)
      (fun u ω => ((fun u => -(-loadRho' (1 - u))) u - (fun u => -phiL u) u / 2)
        * Real.sin (bmReal bmPath u ω)) infPσB infPm infPσX infPσX 0 T
      (1 + 1 / 2) 1 (1 + 1 / 2) 1 (1 + 1 / 2) 1 :=
  fun _ hT => infPModel M0 hT.le

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3⁺): transversality holds exactly**:
`n_TB_T = 0` for `T ≥ 1`, so `E_0[n_{T_k}B_{T_k}] = 0`, `T_k = k + 1`. -/
theorem infP_tvc :
    ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[fun ω => disc tΛ (constP 1) ((k : ℝ) + 1) ω
      * infPB ((k : ℝ) + 1) ω | bmF 0] ω) atTop (𝓝 0) := by
  refine ae_of_all _ fun ω => ?_
  have e : ∀ k : ℕ, (fun ω => disc tΛ (constP 1) ((k : ℝ) + 1) ω * infPB ((k : ℝ) + 1) ω)
      = 0 := fun k => funext fun ω => by
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := k.cast_nonneg (α := ℝ); linarith
    simp only [infPB, loadings_props.2.1 _ hk, neg_zero, zero_mul, add_zero, mul_zero,
      Pi.zero_apply]
  simp_rw [e, condExp_zero]
  exact tendsto_const_nhds

/-- Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3⁺): for every path,
`∫_0^1 (φ cos W)² du > 0` (`φ(0)cos W_0 = ½`). -/
theorem infP_kappa_path_pos (ω : ℕ → ℝ) :
    0 < ∫ u in (0 : ℝ)..1, infPσX u ω * infPσX u ω := by
  have hc : Continuous fun u => infPσX u ω :=
    (continuous_iff_continuousAt.2 fun u => (loadings_deriv.1 u).continuousAt).mul
      (Real.continuous_cos.comp (continuous_bmReal (continuous_bmPath ω)))
  refine intervalIntegral.integral_pos zero_lt_one (hc.mul hc).continuousOn
    (fun x _ => mul_self_nonneg _) ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
  simp only [infPσX, loadings_props.2.2.1, bmReal, Real.toNNReal_zero, bmPath_zero,
    Real.cos_zero, mul_one]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.32)–(1.33), p. 567 (economy 3⁺): the bracket is bounded away
from `0`**: `E∫_0^T σ_Xσ_B du = −E∫_0^T (φ cos W)² ≤ −κ < 0` for `T ≥ 1`, with
`κ = E∫_0^1 (φ cos W)² > 0`. -/
theorem infP_bracket_le {T : ℝ} (hT : 1 ≤ T) :
    ∫ ω, bracket infPσX infPσB 0 T ω ∂gaussSeq
        ≤ -∫ ω, (∫ u in (0 : ℝ)..1, infPσX u ω * infPσX u ω) ∂gaussSeq ∧
      0 < ∫ ω, (∫ u in (0 : ℝ)..1, infPσX u ω * infPσX u ω) ∂gaussSeq := by
  have := isProb
  have hX0 : ∀ {r : ℝ}, 0 ≤ r → ItoIntegrand gaussSeq bmF infPσX 0 r 1 := fun hr =>
    (tΛ_ito le_rfl hr).diff
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have i1 : Integrable (fun ω => ∫ u in (0 : ℝ)..1, infPσX u ω * infPσX u ω) gaussSeq :=
    (memLp_integral_drift (itoIntegrand_mul (hX0 zero_le_one) (hX0 zero_le_one)) le_rfl
      zero_le_one le_rfl).integrable one_le_two
  have iT : Integrable (fun ω => ∫ u in (0 : ℝ)..T, infPσX u ω * infPσX u ω) gaussSeq :=
    (memLp_integral_drift (itoIntegrand_mul (hX0 hT0) (hX0 hT0)) le_rfl hT0
      le_rfl).integrable one_le_two
  have eb : bracket infPσX infPσB 0 T = fun ω => -∫ u in (0 : ℝ)..T, infPσX u ω * infPσX u ω :=
    funext fun ω => by
      simp only [bracket, ← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun u _ => by simp only [infPσX, infPσB]; ring
  refine ⟨?_, ?_⟩
  · rw [eb, integral_neg, neg_le_neg_iff]
    refine integral_mono i1 iT fun ω => ?_
    have hc : Continuous fun u => infPσX u ω :=
      (continuous_iff_continuousAt.2 fun u => (loadings_deriv.1 u).continuousAt).mul
        (Real.continuous_cos.comp (continuous_bmReal (continuous_bmPath ω)))
    exact intervalIntegral.integral_mono_interval le_rfl zero_le_one hT
      (ae_of_all _ fun u => mul_self_nonneg _) ((hc.mul hc).intervalIntegrable _ _)
  · rw [integral_pos_iff_support_of_nonneg (fun ω => (infP_kappa_path_pos ω).le) i1]
    have e : Function.support (fun ω => ∫ u in (0 : ℝ)..1, infPσX u ω * infPσX u ω)
        = Set.univ := Set.eq_univ_of_forall fun ω => (infP_kappa_path_pos ω).ne'
    rw [e, measure_univ]
    exact one_pos

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567 (economy 3⁺, `Λ/P ∈ [1, 3]` throughout): the
book's (1.33) fails although transversality holds**: `E_0[F_{T_k}]` does not converge to
`n_0B_0` a.s., `T_k = k + 1` (by `TidyR7MonetarismItoValuation.valuation_1_33_ito_book_iff`
the printed form would force `E_0∫_0^{T_k}σ_Xσ_B → 0`, but it stays `≤ −κ < 0`). -/
theorem infP_book_fails (M0 : ℝ) :
    ¬ ∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[flowItoBook gaussSeq bmF bmPath tΛ
      (constP 1) (infPM M0) (constP 0) (fun u ω => tI u ω * infPB u ω) infPm infPσX 0
        ((k : ℝ) + 1) | bmF 0] ω) atTop (𝓝 (disc tΛ (constP 1) 0 ω * infPB 0 ω)) := by
  have := isProb
  intro h
  have hiff := (valuation_1_33_ito_book_iff (infPModels M0) isPreBrownianReal_bmPath
    measurable_bmPath (bmFiltrationReal_isBM isPreBrownianReal_bmPath measurable_bmPath) le_rfl
    (T := fun k : ℕ => (k : ℝ) + 1) (fun k => by positivity) infP_tvc).1 h
  obtain ⟨ω, hω⟩ := hiff.exists
  have hle : ∀ k : ℕ, gaussSeq[bracket infPσX infPσB 0 ((k : ℝ) + 1) | bmF 0] ω
      ≤ -∫ ω, (∫ u in (0 : ℝ)..1, infPσX u ω * infPσX u ω) ∂gaussSeq := fun k => by
    rw [bmF_zero, condExp_bot]
    exact (infP_bracket_le (by have := k.cast_nonneg (α := ℝ); linarith)).1
  have h0 := le_of_tendsto' hω hle
  linarith [(infP_bracket_le le_rfl).2]

/-- **Cochrane (2023), A1 §1.6, (1.33), p. 567: headline (economy 3⁺).** With
`1 ≤ Λ/P = Λ ≤ 3`, `P = 1` and `|i| ≤ 3/2` at every time and state: transversality holds
exactly, the bracket stays `≤ −κ < 0`, and the book's (1.33) fails. -/
theorem infP_headline (M0 : ℝ) :
    (∀ u ω, 1 ≤ disc tΛ (constP 1) u ω ∧ disc tΛ (constP 1) u ω ≤ 3 ∧ |tI u ω| ≤ 3 / 2) ∧
    (∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[fun ω => disc tΛ (constP 1)
      ((k : ℝ) + 1) ω * infPB ((k : ℝ) + 1) ω | bmF 0] ω) atTop (𝓝 0)) ∧
    (∀ k : ℕ, ∫ ω, bracket infPσX infPσB 0 ((k : ℝ) + 1) ω ∂gaussSeq
        ≤ -∫ ω, (∫ u in (0 : ℝ)..1, infPσX u ω * infPσX u ω) ∂gaussSeq) ∧
    (0 < ∫ ω, (∫ u in (0 : ℝ)..1, infPσX u ω * infPσX u ω) ∂gaussSeq) ∧
    ¬ (∀ᵐ ω ∂gaussSeq, Tendsto (fun k : ℕ => gaussSeq[flowItoBook gaussSeq bmF bmPath tΛ
      (constP 1) (infPM M0) (constP 0) (fun u ω => tI u ω * infPB u ω) infPm infPσX 0
        ((k : ℝ) + 1) | bmF 0] ω) atTop (𝓝 (disc tΛ (constP 1) 0 ω * infPB 0 ω))) := by
  refine ⟨fun u ω => ?_, infP_tvc, fun k => (infP_bracket_le (by
    have := k.cast_nonneg (α := ℝ); linarith)).1, (infP_bracket_le le_rfl).2,
    infP_book_fails M0⟩
  obtain ⟨h1, h2, h3, h4⟩ := tΛ_bounds u ω
  exact ⟨h3 ▸ h1, h3 ▸ h2, h4⟩

end Cochrane.Monetarism.TidyR9MonetarismItoPositiveInf
