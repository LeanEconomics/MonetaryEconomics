/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.History
import KeynesianStickyPrices.PersistenceFreedom

/-!
# Links between the simple-model and full-model formalisations of Chapter 17

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, pp. 397–421, Chapter 18,
p. 427, and Online Appendix A1, §1.8 and §1.13.1, pp. 571–572 and 586–588. The chapter was
formalised in two chains: the simple sticky-price model (17.1)–(17.14) with A1 §1.8/§1.13.1
(`StaticIS`, `RulesAdaptiveRE`, `AR1Responses`, `PersistenceFreedom`, `AdaptiveTaylor`) and
the full model (17.15)–(17.33) with Chapter 18 (`FullModel`, `FiscalUnderpinnings`,
`OptimalPolicy`, `TaylorDeterminacy`, `History`). This module proves that they talk about the
same objects.

* Innovations (pp. 400, 405, 411): the simple model's expectational error `reErr` is the
  innovation `FiscalUnderpinnings.innov` of an adapted process (`reErr_eq_innov`); the
  announcement-date surprise of `PersistenceFreedom.any_sign` is an innovation
  (`any_sign_innov`).
* The simple model is the `β = 0` case of the full model, exactly:
  - (17.18) under perfect foresight at `β = 0` is (17.7) with no expectational errors
    (`second_beta_zero_iff`), and on `ℤ` its bounded solutions are the backward moving average
    (17.8) (`secondZ_beta_zero`) — the `β = 0` end of `FullModel.secondZ_unique`;
  - the deviation system (17.29)–(17.32) at `β = 0` is the rational-expectations model with
    the rule, (17.11) (`deviation_beta_zero`), and determinacy of the full model at `β = 0`
    (`TaylorDeterminacy.Determinate`) is exactly the corrected E7 condition
    `φ > 1 ∨ φ < −1 − 2/(σκ)` (`determinate_beta_zero_iff`), i.e. `REDeterminate`
    (`determinate_beta_zero_iff_reDeterminate`);
  - the (1.58) bound `−(1 + 2(1+β)/(σκ))` equals the E7 bound `−1 − 2/(σκ)` at `β = 0`
    (`bound_1_58_beta_zero`), lies strictly below it for `β > 0` (`bound_1_58_lt`) and tends to
    it as `β → 0` (`tendsto_bound_1_58`).
* The (1.55) matrix: `AR1Responses.transA` is by definition `solvedA (Pmat σ κ φ 0) (Qmat σ β)`
  (`transA_eq_solvedA`), the inverse of the matrix `M` of (17.33) (`Mmat_mul_transA`).
  Determinacy is Schur stability of `transA` (`determinate_iff_transA`), so the MSV
  uniqueness of A1 p. 588 holds on the whole determinacy region (1.58), not only for `φ > 1`
  (`msv_unique_of_determinate`).
* E11: the lag-operator roots of A1 §1.8 (chain A) and the eigenvalues (1.57) (chain B) are
  reciprocal (`inv_mem_roots`, `discQ_div`), so `lag_roots_norm_lt_one` gives both eigenvalues
  of modulus above one for `φ > 1` (`eigen_norm_gt_one`); the complex example of
  `lag_roots_complex_example` is in the complex branch of `roots_phi_gt_one`
  (`complex_example_discE`).
* The three-equation model of A1 §1.13.1 is the full model with the rule substituted
  (`threeEq_iff_model`). Open mouth (p. 416): `λ₂ = β η*` (`lam2_eq_beta_mul_etaStar`), and
  with `i ≡ 0` every perfect-foresight equilibrium decays at rate `η*` (`openMouth_path`);
  super-Fisherian (p. 415): a constant rate gives the constant inflation path
  (`superFisher_path`).
* Fig. 17.5 vs p. 405/410: the path anticipated from the infinite past is the member of the
  `full_any_sign` family with initial value `zPath T 0` (`zPath_eq_path`), and every other
  initial jump differs from it by `(c − zPath T 0) λ₁^{−n}` (`path_sub_zPath`).
* History (18.1)–(18.2) (p. 427): the deviation system is the model with the rule (18.1)
  (`deviation_iff_rule181`); (18.2) without forward responses has `Q = Qmat`
  (`Q182_no_forward`) and the same determinacy condition (`rule182_determinate_iff_determinate`).
-/

namespace Cochrane.KeynesianStickyPrices.Links

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Innovations -/

/-- Cochrane (2023), p. 400 and eq. (17.19), p. 411: for an adapted process the expectational
error of the simple model, `δ_{t+1} = π_{t+1} − E_t π_{t+1}` (`StaticIS.reErr`), is the
innovation `ΔE_{t+1} π_{t+1} = E_{t+1} π_{t+1} − E_t π_{t+1}` (`FiscalUnderpinnings.innov`). -/
theorem reErr_eq_innov {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (t : ℕ) :
    StaticIS.reErr 𝔼 π (t + 1) = FiscalUnderpinnings.innov 𝔼 t (π (t + 1)) := by
  change π (t + 1) - 𝔼.E t (π (t + 1)) = 𝔼.E (t + 1) (π (t + 1)) - 𝔼.E t (π (t + 1))
  rw [hπ (t + 1)]

/-- Cochrane (2023), p. 405 and p. 411: in `PersistenceFreedom.any_sign` the announcement-date
surprise is the innovation, `ΔE_1 π*_1 = c ε`. -/
theorem any_sign_innov {σ κ Mg Mε : ℝ} (hσκ : 0 < σ * κ) {ε : Ω → ℝ}
    (hε0 : 𝔼.E 0 ε = 0) (hε1 : 𝔼.E 1 ε = ε) (hεb : ∀ ω, |ε ω| ≤ Mε) {g : ℕ → ℝ}
    (hg : ∀ t, |g t| ≤ Mg) (c : ℝ) :
    FiscalUnderpinnings.innov 𝔼 0
      (PersistenceFreedom.shockInfl (PersistenceFreedom.targetPath σ κ g c) ε 1) = c • ε := by
  obtain ⟨hm, -, -, hd⟩ := PersistenceFreedom.any_sign 𝔼 hσκ hε0 hε1 hεb hg c
  rw [← reErr_eq_innov 𝔼 hm.1 0]
  exact hd

/-! ### The simple model is the `β = 0` case of the full model -/

/-- Cochrane (2023), eqs. (17.18), p. 408, and (17.7), p. 398: under perfect foresight, (17.18)
with `β = 0` is (17.7) with no expectational errors,
`π_{t+1} = π_t/(1+σκ) + σκ/(1+σκ) i_t`. -/
theorem second_beta_zero_iff {σ κ : ℝ} (hσκ : 1 + σ * κ ≠ 0) (i π : ℕ → ℝ) :
    FullModel.Second σ 0 κ i π ↔
      ∀ t, π (t + 1) = 1 / (1 + σ * κ) * π t + σ * κ / (1 + σ * κ) * i t := by
  refine forall_congr' fun t => ?_
  constructor
  · intro h
    field_simp
    linear_combination -h
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), eq. (17.8), p. 400, and Fig. 17.5, p. 409: on `ℤ`, every bounded solution
of (17.18) with `β = 0` (bounded rate path) is the backward moving average (17.8) with no
expectational errors, `π_{t+1} = σκ/(1+σκ) ∑_j (1+σκ)^{−j} i_{t−j}` — the `β = 0` counterpart of
the infinite-past uniqueness `FullModel.secondZ_unique` (proved there for `β > 0`). -/
theorem secondZ_beta_zero {σ κ Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → ℝ}
    (hπ : ∀ s, |π s| ≤ Mπ) (hi : ∀ s, |i s| ≤ Mi) (h : FullModel.SecondZ σ 0 κ i π) (t : ℤ) :
    π (t + 1) = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  have e := StaticIS.eq_17_8 hσκ hπ hi (δ := fun _ => 0) (Mδ := 0) (fun _ => by simp)
    (fun s => by
      have hs := h s
      field_simp
      linear_combination -hs) t
  simpa using e

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420, and (17.11), p. 402: at `β = 0` the
deviation system of the full model with `i = φπ` is the rational-expectations simple model with
the rule, (17.11) with no disturbance (for adapted `π`, `κ ≠ 0`). -/
theorem deviation_beta_zero {σ κ φ : ℝ} (hκ : κ ≠ 0) {i r x π : ℕ → Ω → ℝ}
    (hπ : 𝔼.Adapted π) (h : TaylorDeterminacy.Deviation 𝔼 σ 0 κ φ 0 i r x π) :
    RulesAdaptiveRE.RERule 𝔼 σ κ φ 0 π := by
  have hx : ∀ t, x t = κ⁻¹ • π t := fun t => by
    rw [(h t).2.2.1, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  refine ⟨hπ, fun t ω => ?_⟩
  obtain ⟨h1, h2, -, h4⟩ := h t
  have e1 := congrFun h1 ω
  have e2 := congrFun h2 ω
  have e4 := congrFun h4 ω
  have ex := congrFun (hx t) ω
  have ex' : 𝔼.E t (x (t + 1)) ω = κ⁻¹ * 𝔼.E t (π (t + 1)) ω := by
    rw [hx (t + 1), map_smul]; rfl
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_mul,
    add_zero] at e1 e2 e4 ex
  simp only [Pi.zero_apply, add_zero]
  rw [ex, ex'] at e2
  have hk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  linear_combination κ * e2 + σ * κ * e1 - σ * κ * e4 - (π t ω - 𝔼.E t (π (t + 1)) ω) * hk

/-- Cochrane (2023), p. 402 (E7) and A1 p. 587: at `β = 0` the full model's determinacy
condition (`TaylorDeterminacy.determinate_iff`) is exactly the corrected E7 condition of the
simple model, `φ > 1 ∨ φ < −1 − 2/(σκ)`. -/
theorem determinate_beta_zero_iff [Nonempty Ω] {σ κ φ : ℝ} (hσκ : 0 < σ * κ) :
    TaylorDeterminacy.Determinate 𝔼 σ 0 κ φ 0 ↔ 1 < φ ∨ φ < -1 - 2 / (σ * κ) := by
  rw [TaylorDeterminacy.determinate_iff, ← RulesAdaptiveRE.abs_lt_abs_iff hσκ]
  simp only [mul_zero, add_zero, zero_div, SchurStable, abs_zero, zero_lt_one, true_and,
    zero_mul]
  constructor
  · rintro ⟨hD, h⟩
    rwa [abs_div, div_lt_one (abs_pos.mpr hD)] at h
  · intro h
    have hD : 1 + σ * κ * φ ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      exact absurd h (not_lt.mpr (abs_nonneg _))
    exact ⟨hD, by rwa [abs_div, div_lt_one (abs_pos.mpr hD)]⟩

/-- Cochrane (2023), p. 402 and p. 420: at `β = 0` the full model is determinate exactly when the
simple model (17.11) is (`RulesAdaptiveRE.reDeterminate_iff`). -/
theorem determinate_beta_zero_iff_reDeterminate [Nonempty Ω] {σ κ φ : ℝ} (hσκ : 0 < σ * κ) :
    TaylorDeterminacy.Determinate 𝔼 σ 0 κ φ 0 ↔ RulesAdaptiveRE.REDeterminate 𝔼 σ κ φ := by
  rw [determinate_beta_zero_iff 𝔼 hσκ, RulesAdaptiveRE.reDeterminate_iff 𝔼 hσκ]

/-- Cochrane (2023), eq. (1.58), A1 p. 587, and p. 402: at `β = 0` the lower determinacy bound
`−(1 + 2(1+β)/(σκ))` is the E7 bound `−1 − 2/(σκ)`. -/
theorem bound_1_58_beta_zero (σ κ : ℝ) :
    -(1 + 2 * (1 + 0) / (σ * κ)) = -1 - 2 / (σ * κ) := by ring

/-- Cochrane (2023), eq. (1.58), A1 p. 587: for `β > 0` the full-model bound lies strictly below
the simple-model bound, `−(1 + 2(1+β)/(σκ)) < −1 − 2/(σκ)`. -/
theorem bound_1_58_lt {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ : 0 < β) :
    -(1 + 2 * (1 + β) / (σ * κ)) < -1 - 2 / (σ * κ) := by
  have : 2 / (σ * κ) < 2 * (1 + β) / (σ * κ) :=
    div_lt_div_of_pos_right (by linarith) hσκ
  linarith

/-- Cochrane (2023), eq. (1.58), A1 p. 587: as `β → 0` the full-model bound tends to the
simple-model bound `−1 − 2/(σκ)`. -/
theorem tendsto_bound_1_58 (σ κ : ℝ) :
    Tendsto (fun β : ℝ => -(1 + 2 * (1 + β) / (σ * κ))) (𝓝 0) (𝓝 (-1 - 2 / (σ * κ))) := by
  have hc : Continuous (fun β : ℝ => -(1 + 2 * (1 + β) / (σ * κ))) := by fun_prop
  have h := hc.tendsto 0
  rwa [bound_1_58_beta_zero] at h

/-! ### The (1.55) matrix and MSV uniqueness -/

/-- Cochrane (2023), A1 eq. (1.55), p. 586, and p. 420: the transition matrix of chain A is the
solved structural matrix `P⁻¹Q` of the determinacy analysis at `φ_x = 0`. -/
theorem transA_eq_solvedA (σ κ β φ : ℝ) :
    AR1Responses.transA σ κ β φ =
      SharedTools.solvedA (SharedTools.Pmat σ κ φ 0) (SharedTools.Qmat σ β) := rfl

/-- Cochrane (2023), eq. (17.33), p. 420, and A1 eq. (1.55), p. 586: the matrix `M` of (17.33)
(`E_t x_{t+1} = M x_t`) is the inverse of the forward-looking transition matrix `A`. -/
theorem Mmat_mul_transA {σ κ β φ : ℝ} (hβ : β ≠ 0) (hD : 1 + σ * κ * φ ≠ 0) :
    TaylorDeterminacy.Mmat σ β κ φ * AR1Responses.transA σ κ β φ = 1 := by
  have hD' : 1 + κ * σ * φ ≠ 0 := by rwa [show κ * σ * φ = σ * κ * φ by ring]
  rw [AR1Responses.transA_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [TaylorDeterminacy.Mmat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- Cochrane (2023), p. 420 and A1 p. 587: the deviation system (17.29)–(17.32) is determinate
iff `1 + σκφ ≠ 0` and the transition matrix `A` of (1.55) (`AR1Responses.transA`) is Schur
stable. -/
theorem determinate_iff_transA [Nonempty Ω] (σ κ β φ : ℝ) :
    TaylorDeterminacy.Determinate 𝔼 σ β κ φ 0 ↔
      1 + σ * κ * φ ≠ 0 ∧
        SchurStable (tr2 (AR1Responses.transA σ κ β φ)) (det2 (AR1Responses.transA σ κ β φ)) := by
  rw [TaylorDeterminacy.determinate_iff_struct, TaylorDeterminacy.structDeterminate_iff,
    SharedTools.det2_Pmat, transA_eq_solvedA]
  simp only [mul_zero, add_zero]

/-- Cochrane (2023), A1 pp. 587–588 (MSV uniqueness) on the whole determinacy region (1.58):
whenever the deviation system is determinate (`TaylorDeterminacy.determinate_iff_phi`: `φ > 1`
or `φ < −(1 + 2(1+β)/(σκ))`) and the MSV denominator is nonzero, the minimal-state-variable
solution is the unique bounded equilibrium of the three-equation model with a bounded AR(1)
disturbance. `AR1Responses.msv_unique` is the case `φ > 1`. -/
theorem msv_unique_of_determinate [Nonempty Ω] {σ κ β φ η M : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    (hdet : TaylorDeterminacy.Determinate 𝔼 σ β κ φ 0)
    (hD : AR1Responses.denF σ κ β φ η ≠ 0) {u x π : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 η u) (hM : ∀ t ω, |u t ω| ≤ M) (h : AR1Responses.ThreeEq 𝔼 σ κ β φ u x π)
    (hxb : BoundedProc x) (hπb : BoundedProc π) :
    π = (fun t => (-1 / AR1Responses.denF σ κ β φ η) • u t) ∧
      x = (fun t => ((1 - β * η) / κ * (-1 / AR1Responses.denF σ κ β φ η)) • u t) := by
  obtain ⟨hMM, hS⟩ := (determinate_iff_transA 𝔼 σ κ β φ).mp hdet
  obtain ⟨h1, h2⟩ := (AR1Responses.eq_1_59_iff hσ hκ hD).mpr ⟨rfl, rfl⟩
  have hs := AR1Responses.msv_solves 𝔼 hu h1 h2
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mπ, hMπ⟩ := hπb
  set aπ := -1 / AR1Responses.denF σ κ β φ η
  set ax := (1 - β * η) / κ * aπ
  have e := 𝔼.system_unique hS (AR1Responses.threeEq_solves 𝔼 hMM h)
    (AR1Responses.threeEq_solves 𝔼 hMM hs)
    (fun t j => by fin_cases j <;> simp [h.1 t, h.2.1 t])
    (fun t j => by fin_cases j <;> simp [hs.1 t, hs.2.1 t])
    ⟨max Mx Mπ, fun t j ω => by
      fin_cases j
      · exact (hMx t ω).trans (le_max_left _ _)
      · exact (hMπ t ω).trans (le_max_right _ _)⟩
    ⟨max (|ax| * M) (|aπ| * M), fun t j ω => by
      fin_cases j
      · simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)).trans (le_max_left _ _)
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
          smul_eq_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)).trans (le_max_right _ _)⟩
  refine ⟨funext fun t => ?_, funext fun t => ?_⟩
  · simpa using congrFun (congrFun e t) 1
  · simpa using congrFun (congrFun e t) 0

/-! ### E11: lag roots and eigenvalues are reciprocal -/

/-- Cochrane (2023), A1 §1.8, p. 572, and eq. (1.57), p. 587: if `z` is a root of
`z² − Tz + D` with `D ≠ 0`, then `1/z` is a root of `λ² − (T/D)λ + 1/D`. -/
theorem inv_mem_roots {T D : ℝ} (hD : D ≠ 0) {z : ℂ}
    (hz : z = root₁ T D ∨ z = root₂ T D) :
    z⁻¹ = root₁ (T / D) (1 / D) ∨ z⁻¹ = root₂ (T / D) (1 / D) := by
  have hq := root_eq T D z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    have : (D : ℂ) = 0 := by simpa using hq
    exact hD (by exact_mod_cast this)
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  refine eq_root_of_eq ?_
  push_cast
  field_simp
  linear_combination hq

/-- Cochrane (2023), A1 p. 572 and p. 587: the discriminants of the two quadratics have the same
sign, `discQ (T/D) (1/D) = discQ T D / D²`. -/
theorem discQ_div {T D : ℝ} (hD : D ≠ 0) : discQ (T / D) (1 / D) = discQ T D / D ^ 2 := by
  unfold discQ
  field_simp

/-- Cochrane (2023), eq. (1.57), p. 587: `tr M = tr A/det A` and `det M = 1/det A` for the
lag-polynomial coefficients `T = (1+β+σκ)/(1+σκφ)`, `D = β/(1+σκφ)` of A1 §1.8. -/
theorem trM_detM_eq {σ β κ φ : ℝ} (hβ : β ≠ 0) (hM : 1 + σ * κ * φ ≠ 0) :
    TaylorDeterminacy.trM σ β κ =
        (1 + β + σ * κ) / (1 + σ * κ * φ) / (β / (1 + σ * κ * φ)) ∧
      TaylorDeterminacy.detM σ β κ φ = 1 / (β / (1 + σ * κ * φ)) := by
  unfold TaylorDeterminacy.trM TaylorDeterminacy.detM
  constructor <;> field_simp

/-- Cochrane (2023), Ch17 p. 420 and A1 p. 587 (survey error E11, unified): for `φ > 1` both
eigenvalues of (1.57) have modulus strictly above one, real or complex — derived from the
chain-A statement `AR1Responses.lag_roots_norm_lt_one` by reciprocity. -/
theorem eigen_norm_gt_one {σ β κ φ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hφ : 1 < φ) :
    1 < ‖root₁ (TaylorDeterminacy.trM σ β κ) (TaylorDeterminacy.detM σ β κ φ)‖ ∧
      1 < ‖root₂ (TaylorDeterminacy.trM σ β κ) (TaylorDeterminacy.detM σ β κ φ)‖ := by
  have hM : 0 < 1 + σ * κ * φ := by nlinarith
  set T := (1 + β + σ * κ) / (1 + σ * κ * φ)
  set D := β / (1 + σ * κ * φ)
  have hD : D ≠ 0 := (div_pos hβ0 hM).ne'
  have hD' : 1 / D ≠ 0 := one_div_ne_zero hD
  obtain ⟨htr, hdet⟩ := trM_detM_eq (φ := φ) (κ := κ) (σ := σ) hβ0.ne' hM.ne'
  obtain ⟨hA1, hA2⟩ := AR1Responses.lag_roots_norm_lt_one hσκ hβ0 hβ1 hφ
  have back : ∀ w : ℂ, (w = root₁ (T / D) (1 / D) ∨ w = root₂ (T / D) (1 / D)) → 1 < ‖w‖ := by
    intro w hw
    have hinv := inv_mem_roots hD' hw
    rw [show T / D / (1 / D) = T by field_simp, one_div_one_div] at hinv
    have hlt : ‖w⁻¹‖ < 1 := by rcases hinv with h | h <;> rw [h] <;> assumption
    have hw0 : w ≠ 0 := by
      rintro rfl
      have := root_eq (T / D) (1 / D) 0 hw
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero,
        zero_add] at this
      exact hD' (by exact_mod_cast this)
    rw [norm_inv] at hlt
    have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    rwa [inv_lt_one₀ hpos] at hlt
  rw [htr, hdet]
  exact ⟨back _ (Or.inl rfl), back _ (Or.inr rfl)⟩

/-- Cochrane (2023), A1 p. 572 (E11) and p. 587: the parameters of
`AR1Responses.lag_roots_complex_example` (`σ = 1`, `β = 0.99`, `κ = 0.5`, `φ = 1.5`) have
negative discriminant (1.57), so they fall in the complex branch of
`TaylorDeterminacy.roots_phi_gt_one`. -/
theorem complex_example_discE : TaylorDeterminacy.discE 1 0.99 0.5 1.5 < 0 := by
  unfold TaylorDeterminacy.discE
  norm_num

/-! ### The three-equation model, open mouth and super-Fisherian -/

/-- Cochrane (2023), A1 §1.13.1, p. 588, and eqs. (17.15)–(17.17), (17.20), pp. 407 and 415:
the three-equation model of chain A is the full model (17.15)–(17.17) with no IS or Phillips
disturbances, the rule `i_t = φπ_t + u_t` and the real rate `r_t = i_t − E_t π_{t+1}`. -/
theorem threeEq_iff_model (σ κ β φ : ℝ) (u x π : ℕ → Ω → ℝ) :
    AR1Responses.ThreeEq 𝔼 σ κ β φ u x π ↔ 𝔼.Adapted x ∧ 𝔼.Adapted π ∧
      FullModel.Model 𝔼 σ β κ 0 0 (fun t => φ • π t + u t)
        (fun t => φ • π t + u t - 𝔼.E t (π (t + 1))) x π := by
  unfold AR1Responses.ThreeEq FullModel.Model FullModel.IS FullModel.Fisher FullModel.PC
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_,
      fun t => funext fun ω => ?_⟩
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        add_zero]
      linarith [(h t ω).1]
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero]
      linarith [(h t ω).2]
  · rintro ⟨h1, -, h3⟩ t ω
    have e1 := congrFun (h1 t) ω
    have e3 := congrFun (h3 t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      add_zero] at e1 e3
    exact ⟨by linarith, by linarith⟩

/-- Cochrane (2023), p. 416 and eq. (5.6), p. 119: the smaller root of
`λ² − (1+β+σκ)λ + β` is `β` times the open-mouth persistence, `λ₂ = β η*`. -/
theorem lam2_eq_beta_mul_etaStar {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) :
    FullModel.lam2 σ β κ = β * AR1Responses.etaStar σ κ β := by
  have hp := FullModel.lam_prod hσκ hβ0
  have h1 := (one_pos.trans (FullModel.one_lt_lam1 hσκ hβ0)).ne'
  rw [PersistenceFreedom.etaStar_eq_inv_lam1 hσκ hβ0, eq_mul_inv_iff_mul_eq₀ h1]
  linear_combination hp

/-- Cochrane (2023), p. 416 (open mouth) with §17.4.1, p. 408: under perfect foresight, with the
interest rate held at zero every bounded equilibrium of (17.18) decays at the open-mouth rate,
`π_t = π_0 η*ᵗ`; with an AR(1) disturbance of persistence `η*` the MSV solution
(`AR1Responses.openMouth_full`: `i = 0`, `π = −u/φ`) is the member with `π_0 = −u_0/φ`. -/
theorem openMouth_path {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (c : ℝ) :
    FullModel.path σ β κ (fun _ => 0) c = fun t => c * AR1Responses.etaStar σ κ β ^ t := by
  funext t
  induction t with
  | zero => simp [FullModel.path]
  | succ t ih =>
    have hF : FullModel.F (FullModel.lam2 σ β κ) (fun _ => (0 : ℝ)) t = 0 := by
      simp [FullModel.F]
    rw [FullModel.path, ih, hF, PersistenceFreedom.etaStar_eq_inv_lam1 hσκ hβ0, pow_succ]
    ring

/-- Cochrane (2023), p. 415 (super-Fisherian, `η = 1`) with §17.4.1, p. 408: under perfect
foresight a constant interest rate `c` and constant inflation `c` solve (17.18), and this is the
bounded equilibrium with `π_0 = c` (`FullModel.path`) — the `η = 1` MSV response
`π = i = −u/(φ−1)` of `AR1Responses.superFisher_full`. -/
theorem superFisher_path {σ κ β : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (c : ℝ) :
    FullModel.Second σ β κ (fun _ => c) (fun _ => c) ∧
      FullModel.path σ β κ (fun _ => c) c = fun _ => c := by
  have hs : FullModel.Second σ β κ (fun _ => c) (fun _ => c) := fun _ => by ring
  have hi : ∀ t : ℕ, |(fun _ => c) t| ≤ |c| := fun _ => le_rfl
  refine ⟨hs, ?_⟩
  have hb := FullModel.path_bounded hσκ hβ0 hi c
  exact (FullModel.pf_existsUnique hσκ hβ0 hi c).unique
    ⟨hb, (FullModel.second_iff_factor hσκ hβ0 hi hb).mpr (FullModel.path_factor hσκ hβ0 _ c),
      rfl⟩
    ⟨⟨|c|, fun _ => le_rfl⟩, hs, rfl⟩

/-! ### Fig. 17.5 and the "any sign" family -/

/-- Cochrane (2023), Fig. 17.5, p. 409, and pp. 405, 410: from the announcement on, the response
anticipated from the infinite past (`FullModel.zPath`) is the member of the
`PersistenceFreedom.full_any_sign` family (`FullModel.path`) with initial inflation
`zPath T 0`. -/
theorem zPath_eq_path {σ β κ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (T : ℕ) :
    (fun s : ℕ => FullModel.zPath σ β κ T s) =
      FullModel.path σ β κ (FullModel.stepI T) (FullModel.zPath σ β κ T 0) := by
  have h0 := FullModel.zPath_eq_antPath hσκ hβ0 T 0
  rw [Nat.cast_zero] at h0
  rw [h0]
  funext s
  rw [FullModel.zPath_eq_antPath hσκ hβ0 T s]
  rfl

/-- Cochrane (2023), pp. 405, 409–410 ("any sign"): every other member of the `full_any_sign`
family — any announcement-date inflation `c`, of either sign — differs from the anticipated
path by a decaying term, `π_n − zPath_n = (c − zPath_0) λ₁^{−n}`. -/
theorem path_sub_zPath {σ β κ : ℝ} (hσκ : 0 < σ * κ) (hβ0 : 0 < β) (T : ℕ) (c : ℝ) (n : ℕ) :
    FullModel.path σ β κ (FullModel.stepI T) c n - FullModel.zPath σ β κ T n =
      (c - FullModel.zPath σ β κ T 0) * (FullModel.lam1 σ β κ)⁻¹ ^ n := by
  have h := congrFun (zPath_eq_path hσκ hβ0 T) n
  rw [h]
  exact FullModel.path_sub_path σ β κ _ c _ n

/-! ### History (18.1)–(18.2) -/

/-- Cochrane (2023), eq. (18.1), p. 427, and (17.29)–(17.32), p. 420: the deviation system with
an output response is the full model in deviations with the rule (18.1) without disturbance. -/
theorem deviation_iff_rule181 (σ β κ φπ φx : ℝ) (i r x π : ℕ → Ω → ℝ) :
    TaylorDeterminacy.Deviation 𝔼 σ β κ φπ φx i r x π ↔
      (∀ t, i t = r t + 𝔼.E t (π (t + 1)) ∧ x t = 𝔼.E t (x (t + 1)) - σ • r t ∧
        π t = β • 𝔼.E t (π (t + 1)) + κ • x t) ∧ History.Rule181 φπ φx 0 i x π := by
  unfold TaylorDeterminacy.Deviation History.Rule181
  simp only [Pi.zero_apply, add_zero]
  constructor
  · intro h
    exact ⟨fun t => ⟨(h t).1, (h t).2.1, (h t).2.2.1⟩, fun t => (h t).2.2.2⟩
  · rintro ⟨h, hr⟩ t
    exact ⟨(h t).1, (h t).2.1, (h t).2.2, hr t⟩

/-- Cochrane (2023), eq. (18.2), p. 427: without forward-looking responses the matrix `Q` of
(18.2) is the matrix `Q` of (17.29)–(17.32). -/
theorem Q182_no_forward (σ β : ℝ) : History.Q182 σ β 0 0 = SharedTools.Qmat σ β := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [History.Q182, SharedTools.Qmat]

/-- Cochrane (2023), eqs. (18.1)–(18.2), p. 427: without inertia and forward responses, (18.2)
has the same determinacy condition as the deviation system with (18.1). -/
theorem rule182_determinate_iff_determinate (σ β κ φπ φx : ℝ) :
    TaylorDeterminacy.StructDeterminate 𝔼 (SharedTools.Pmat σ κ φπ φx) (History.Q182 σ β 0 0) ↔
      TaylorDeterminacy.Determinate 𝔼 σ β κ φπ φx := by
  rw [Q182_no_forward, TaylorDeterminacy.determinate_iff_struct]

end Cochrane.KeynesianStickyPrices.Links
