/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ForwardSolution

/-!
# Gabaix's behavioural new-Keynesian model at a peg

Cochrane (2023), Chapter 20, §20.2.6, pp. 482–483, eqs. (20.11)–(20.12):
`x_t = M E_tx_{t+1} − σ(i_t − E_tπ_{t+1})`, `π_t = M^f βE_tπ_{t+1} + κx_t`, with the interest rate
pegged, `i_t = ī`, for an arbitrary `ExpectationSystem`.

## Main results

* `gabaixEq_iff_solves`: the model is the backward system `z_t = A E_tz_{t+1} + w` with
  `A = [[M, σ], [κM, M^fβ + σκ]]`, `tr A = M + M^fβ + σκ`, `det A = MM^fβ` (`gabaix_tr_det`),
  and `1 − tr A + det A = (1 − M)(1 − βM^f) − σκ` (`gabaix_charpoly_one`).
* `gabaix_determinate_iff`: for `0 ≤ M, M^f ≤ 1`, `0 < β < 1`, `σκ ≥ 0`, the peg is determinate
  (a unique bounded equilibrium: "traditional forward-explosive, backward-stable dynamics") iff
  `(1 − M)(1 − βM^f) > σκ`; equivalently both roots of `A` lie inside the unit circle
  (`gabaix_roots_iff`). Then the unique bounded equilibrium is the steady state
  (`gabaix_unique`, `gabaix_steady`); otherwise there are other bounded equilibria
  (`gabaix_not_unique`).
* p. 483 corollaries: at the rational IS curve `M = 1` the peg is never determinate
  (`rational_IS_indeterminate`); as prices become less sticky determinacy always fails
  (`frictionless_limit_indeterminate`); determinacy requires `M < 1 − σκ`, `σκ < 1 − βM^f`
  (`determinate_bounded_away`); on the boundary a root equals one (`boundary_root_one`: the
  eigenvalues must cross one).
* Survey error E8, confirmed: "one needs `M` less than a half, together with … `σκ` less than
  about a half" is neither necessary (`e8_half_not_necessary`, `e8_half_not_necessary'`) nor
  sufficient (`e8_not_sufficient`).
-/

namespace Cochrane.ZeroBound.Gabaix

open Cochrane.ZeroBound

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: the backward-form matrix
`A = [[M, σ], [κM, M^fβ + σκ]]` of the model at a peg. -/
def gabaixMatrix (M Mf β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![M, σ; κ * M, Mf * β + σ * κ]

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: the constant forcing `(−σī, −κσī)` at the
peg `i_t = ī`. -/
def gabaixForcing {Ω : Type*} (σ κ ibar : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun _ => ![fun _ => -(σ * ibar), fun _ => -(κ * σ * ibar)]

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: trace and determinant of the peg matrix. -/
theorem gabaix_tr_det (M Mf β σ κ : ℝ) :
    tr2 (gabaixMatrix M Mf β σ κ) = M + Mf * β + σ * κ ∧
      det2 (gabaixMatrix M Mf β σ κ) = M * Mf * β := by
  simp only [tr2, det2, gabaixMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor <;> ring

/-- Cochrane (2023), §20.2.6, p. 483: the characteristic polynomial at one,
`1 − tr A + det A = (1 − M)(1 − βM^f) − σκ`. -/
theorem gabaix_charpoly_one (M Mf β σ κ : ℝ) :
    1 - tr2 (gabaixMatrix M Mf β σ κ) + det2 (gabaixMatrix M Mf β σ κ) =
      (1 - M) * (1 - β * Mf) - σ * κ := by
  rw [(gabaix_tr_det M Mf β σ κ).1, (gabaix_tr_det M Mf β σ κ).2]
  ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482, with `i_t = ī`:
`x_t = M E_tx_{t+1} − σ(ī − E_tπ_{t+1})` and `π_t = M^fβE_tπ_{t+1} + κx_t`. -/
def GabaixEq (M Mf β σ κ ibar : ℝ) (x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = M * 𝔼.E t (x (t + 1)) ω - σ * (ibar - 𝔼.E t (π (t + 1)) ω) ∧
    π t ω = Mf * β * 𝔼.E t (π (t + 1)) ω + κ * x t ω

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: the model is the system
`z_t = A E_tz_{t+1} + w` of the core module. -/
theorem gabaixEq_iff_solves (M Mf β σ κ ibar : ℝ) (x π : ℕ → Ω → ℝ) :
    GabaixEq 𝔼 M Mf β σ κ ibar x π ↔
      𝔼.Solves (gabaixMatrix M Mf β σ κ) (gabaixForcing σ κ ibar) (fun t => ![x t, π t]) := by
  constructor
  · intro h t i
    fin_cases i
    · funext ω
      obtain ⟨h1, -⟩ := h t ω
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, gabaixMatrix, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, gabaixForcing,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    · funext ω
      obtain ⟨h1, h2⟩ := h t ω
      simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one,
        Matrix.cons_val_one, gabaixMatrix, Matrix.of_apply, Matrix.cons_val_zero, gabaixForcing,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h2, h1]
      ring
  · intro h t ω
    have h0 := congrFun (h t 0) ω
    have h1 := congrFun (h t 1) ω
    simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero,
      gabaixMatrix, Matrix.of_apply, Matrix.cons_val_one, gabaixForcing, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at h0 h1
    refine ⟨by linarith, ?_⟩
    rw [h1, h0]
    ring

/-- Cochrane (2023), §20.2.6, pp. 482–483 (survey E8, exact boundary): for `0 ≤ M ≤ 1`,
`0 ≤ M^f ≤ 1`, `0 < β < 1`, `σκ ≥ 0`, the Schur–Cohn condition holds iff
`(1 − M)(1 − βM^f) > σκ`. -/
theorem gabaix_schur_iff {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hMf0 : 0 ≤ Mf)
    (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) :
    SchurStable (tr2 (gabaixMatrix M Mf β σ κ)) (det2 (gabaixMatrix M Mf β σ κ)) ↔
      σ * κ < (1 - M) * (1 - β * Mf) := by
  obtain ⟨ht, hd⟩ := gabaix_tr_det M Mf β σ κ
  rw [ht, hd]
  have hdet0 : 0 ≤ M * Mf * β := by positivity
  have hdet1 : M * Mf * β < 1 := by
    have : M * Mf ≤ 1 := by nlinarith
    nlinarith
  have htr : 0 ≤ M + Mf * β + σ * κ := by positivity
  unfold SchurStable
  rw [abs_of_nonneg hdet0, abs_of_nonneg htr]
  constructor
  · rintro ⟨-, h⟩
    nlinarith
  · intro h
    exact ⟨hdet1, by nlinarith⟩

/-- Cochrane (2023), §20.2.6, pp. 482–483: in terms of roots, both roots of
`λ² − tr A λ + det A` lie inside the unit circle (the forward dynamics are explosive in both
directions, "forward-explosive, backward-stable") iff `(1 − M)(1 − βM^f) > σκ`. -/
theorem gabaix_roots_iff {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hMf0 : 0 ≤ Mf)
    (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) :
    (‖root₁ (tr2 (gabaixMatrix M Mf β σ κ)) (det2 (gabaixMatrix M Mf β σ κ))‖ < 1 ∧
      ‖root₂ (tr2 (gabaixMatrix M Mf β σ κ)) (det2 (gabaixMatrix M Mf β σ κ))‖ < 1) ↔
      σ * κ < (1 - M) * (1 - β * Mf) := by
  rw [← schurStable_iff_roots]
  exact gabaix_schur_iff hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ

/-- Cochrane (2023), §20.2.6, pp. 482–483 (survey E8): the peg in Gabaix's model is determinate
(at most one bounded adapted equilibrium for every forcing) iff `(1 − M)(1 − βM^f) > σκ`. -/
theorem gabaix_determinate_iff [Nonempty Ω] {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) :
    𝔼.Determinate (gabaixMatrix M Mf β σ κ) ↔ σ * κ < (1 - M) * (1 - β * Mf) := by
  rw [𝔼.determinate_iff]
  exact gabaix_schur_iff hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ

/-- Cochrane (2023), eqs. (20.11)–(20.12), p. 482: the steady state at the peg,
`π̄ = −σκī/((1 − M)(1 − βM^f) − σκ)`, `x̄ = (1 − βM^f)π̄/κ`. -/
theorem gabaix_steady {M Mf β σ κ ibar : ℝ} (hκ : κ ≠ 0)
    (hp : (1 - M) * (1 - β * Mf) - σ * κ ≠ 0) :
    GabaixEq 𝔼 M Mf β σ κ ibar
      (fun _ _ => (1 - β * Mf) * (-(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) / κ)
      (fun _ _ => -(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) := by
  have hPD : -(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ) *
      ((1 - M) * (1 - β * Mf) - σ * κ) = -(σ * κ * ibar) := div_mul_cancel₀ _ hp
  intro t ω
  simp only [𝔼.const]
  generalize -(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ) = P at hPD ⊢
  constructor
  · apply mul_left_cancel₀ hκ
    field_simp
    linear_combination hPD
  · field_simp
    ring

/-- Cochrane (2023), §20.2.6, p. 482: under `(1 − M)(1 − βM^f) > σκ` the unique bounded adapted
equilibrium at the peg is the steady state. -/
theorem gabaix_unique {M Mf β σ κ ibar : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) (hMf0 : 0 ≤ Mf)
    (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) (hκ : κ ≠ 0)
    (hc : σ * κ < (1 - M) * (1 - β * Mf)) {x π : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x)
    (hπa : 𝔼.Adapted π) (hxb : BoundedProc x) (hπb : BoundedProc π)
    (h : GabaixEq 𝔼 M Mf β σ κ ibar x π) :
    x = (fun _ _ => (1 - β * Mf) * (-(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) / κ) ∧
      π = (fun _ _ => -(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) := by
  have hp : (1 - M) * (1 - β * Mf) - σ * κ ≠ 0 := by linarith
  have hs := gabaix_steady 𝔼 (ibar := ibar) hκ hp
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mp, hMp⟩ := hπb
  have heq := 𝔼.system_unique ((gabaix_schur_iff hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ).mpr hc)
    ((gabaixEq_iff_solves 𝔼 _ _ _ _ _ _ _ _).mp h)
    ((gabaixEq_iff_solves 𝔼 _ _ _ _ _ _ _ _).mp hs)
    (fun t i => by fin_cases i <;> simp [hxa t, hπa t])
    (fun t i => by fin_cases i <;> simp [𝔼.const])
    ⟨max Mx Mp, fun t i ω => by
      fin_cases i
      · exact (hMx t ω).trans (le_max_left _ _)
      · exact (hMp t ω).trans (le_max_right _ _)⟩
    ⟨|(1 - β * Mf) * (-(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)) / κ| +
      |-(σ * κ * ibar) / ((1 - M) * (1 - β * Mf) - σ * κ)|, fun t i ω => by
      fin_cases i
      · simp
      · simp⟩
  exact ⟨funext fun t => by simpa using congrFun heq t |> fun e => congrFun e 0,
    funext fun t => by simpa using congrFun heq t |> fun e => congrFun e 1⟩

/-- Cochrane (2023), §20.2.6, p. 483: when `(1 − M)(1 − βM^f) ≤ σκ`, next to every bounded
adapted equilibrium there is another one (the new-Keynesian indeterminacy reappears). -/
theorem gabaix_not_unique [Nonempty Ω] {M Mf β σ κ ibar : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ)
    (hc : (1 - M) * (1 - β * Mf) ≤ σ * κ) {x π : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x)
    (hπa : 𝔼.Adapted π) (hxb : BoundedProc x) (hπb : BoundedProc π)
    (h : GabaixEq 𝔼 M Mf β σ κ ibar x π) :
    ∃ y, 𝔼.Solves (gabaixMatrix M Mf β σ κ) (gabaixForcing σ κ ibar) y ∧ 𝔼.AdaptedVec y ∧
      BoundedVec y ∧ y ≠ fun t => ![x t, π t] := by
  have hn : ¬ SchurStable (tr2 (gabaixMatrix M Mf β σ κ)) (det2 (gabaixMatrix M Mf β σ κ)) :=
    fun hs => absurd ((gabaix_schur_iff hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ).mp hs) (not_lt.mpr hc)
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mp, hMp⟩ := hπb
  exact 𝔼.system_not_unique hn ((gabaixEq_iff_solves 𝔼 _ _ _ _ _ _ _ _).mp h)
    (fun t i => by fin_cases i <;> simp [hxa t, hπa t])
    ⟨max Mx Mp, fun t i ω => by
      fin_cases i
      · exact (hMx t ω).trans (le_max_left _ _)
      · exact (hMp t ω).trans (le_max_right _ _)⟩

/-- Cochrane (2023), §20.2.6, p. 483 ("Gabaix's result is bounded away from rationality"): with
the rational IS curve `M = 1` the peg is never determinate. -/
theorem rational_IS_indeterminate [Nonempty Ω] {Mf β σ κ : ℝ} (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ) :
    ¬ 𝔼.Determinate (gabaixMatrix 1 Mf β σ κ) := by
  rw [gabaix_determinate_iff 𝔼 zero_le_one le_rfl hMf0 hMf1 hβ0 hβ1 hσκ]
  simp only [sub_self, zero_mul, not_lt]
  exact hσκ

/-- Cochrane (2023), §20.2.6, p. 483 ("As prices become less sticky, new-Keynesian dynamics
always reappear"): for `σ > 0` and any `M, M^f`, the peg is indeterminate for all `κ ≥ 1/σ`. -/
theorem frictionless_limit_indeterminate [Nonempty Ω] {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M)
    (hM1 : M ≤ 1) (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 1 / σ ≤ κ) : ¬ 𝔼.Determinate (gabaixMatrix M Mf β σ κ) := by
  have h1 : 1 ≤ σ * κ := by
    rw [div_le_iff₀ hσ] at hκ
    linarith
  rw [gabaix_determinate_iff 𝔼 hM0 hM1 hMf0 hMf1 hβ0 hβ1 (by linarith), not_lt]
  have : (1 - M) * (1 - β * Mf) ≤ 1 := by
    have a : 0 ≤ 1 - M := by linarith
    have b : 0 ≤ β * Mf := by positivity
    nlinarith
  linarith

/-- Cochrane (2023), §20.2.6, p. 483 ("bounded away from rationality … bounded away from the
frictionless price limit"): determinacy requires `M < 1 − σκ`, `σκ < 1 − βM^f` and `σκ < 1`. -/
theorem determinate_bounded_away [Nonempty Ω] {M Mf β σ κ : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hMf0 : 0 ≤ Mf) (hMf1 : Mf ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hσκ : 0 ≤ σ * κ)
    (h : 𝔼.Determinate (gabaixMatrix M Mf β σ κ)) :
    M < 1 - σ * κ ∧ σ * κ < 1 - β * Mf ∧ σ * κ < 1 := by
  have hc := (gabaix_determinate_iff 𝔼 hM0 hM1 hMf0 hMf1 hβ0 hβ1 hσκ).mp h
  have a : 0 ≤ 1 - M := by linarith
  have b : 0 ≤ β * Mf := by positivity
  have c : β * Mf ≤ 1 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- Cochrane (2023), §20.2.6, p. 482 ("Eigenvalues must switch from greater to less than one"):
on the boundary `(1 − M)(1 − βM^f) = σκ`, one is a root of the characteristic polynomial. -/
theorem boundary_root_one {M Mf β σ κ : ℝ} (h : (1 - M) * (1 - β * Mf) = σ * κ) :
    (1 : ℝ) ^ 2 - tr2 (gabaixMatrix M Mf β σ κ) * 1 + det2 (gabaixMatrix M Mf β σ κ) = 0 := by
  have := gabaix_charpoly_one M Mf β σ κ
  rw [h, sub_self] at this
  linarith

/-- Cochrane (2023), p. 483, survey error E8: "`M` less than a half" is not necessary. With
`M = M^f = 3/5`, `β = 0.99`, `σ = 1`, `κ = 1/10` the peg is determinate. -/
theorem e8_half_not_necessary [Nonempty Ω] :
    (1 / 2 : ℝ) < 3 / 5 ∧ 𝔼.Determinate (gabaixMatrix (3 / 5) (3 / 5) (99 / 100) 1 (1 / 10)) := by
  refine ⟨by norm_num, ?_⟩
  rw [gabaix_determinate_iff 𝔼] <;> norm_num

/-- Cochrane (2023), p. 483, survey error E8 (the survey's example): `M = 0.9`, `M^f = 1/2`,
`β = 0.99`, `σκ = 0.05` is determinate, so `M` can be close to one. -/
theorem e8_half_not_necessary' [Nonempty Ω] :
    𝔼.Determinate (gabaixMatrix (9 / 10) (1 / 2) (99 / 100) 1 (1 / 20)) := by
  rw [gabaix_determinate_iff 𝔼] <;> norm_num

/-- Cochrane (2023), p. 483, survey error E8: "`M` less than a half, together with … `σκ` less
than about a half" is not sufficient: `M = M^f = 2/5`, `β = 0.99`, `σκ = 2/5` is
indeterminate. -/
theorem e8_not_sufficient [Nonempty Ω] :
    (2 / 5 : ℝ) < 1 / 2 ∧ (1 : ℝ) * (2 / 5) < 1 / 2 ∧
      ¬ 𝔼.Determinate (gabaixMatrix (2 / 5) (2 / 5) (99 / 100) 1 (2 / 5)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [gabaix_determinate_iff 𝔼] <;> norm_num

end Cochrane.ZeroBound.Gabaix
