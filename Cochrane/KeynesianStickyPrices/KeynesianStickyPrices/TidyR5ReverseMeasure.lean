/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5InnovEqmMeasure

/-!
# Reverse-engineered disturbances on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, p. 414 ("if fed these
`{u_t}` paths, the model produces the given interest rate and inflation paths") and p. 411
("multiple disturbance paths `u_t` produce the same interest-rate path"), with the determinacy
of the deviation system (17.29)–(17.32), p. 420.

The measure-theoretic version of `TidyR5StochasticPaths.reverse_engineer_innov`:

* `devA`, `tr2_devA`, `det2_devA`: the deviation system `d_t = A E_t d_{t+1}` for the rule
  `i = φπ + u` (trace `(1 + β + σκ)/D`, determinant `β/D`, `D = 1 + σκφ`).
* `dev_zero_ae`: if `A` is Schur stable, every essentially bounded adapted a.e. solution of
  `d_t = A E_t d_{t+1}` vanishes almost surely (the measure-theoretic `system_unique`).
* **`rule_unique_ae`**: for `φ` in the determinacy region (`TaylorDeterminacy.Determinate`,
  which does not depend on the expectation system), two essentially bounded adapted equilibria of
  (17.15)–(17.17) whose rates satisfy the same rule `i = φπ + u` coincide almost surely.
* `reverse_engineer_piM`: for every innovation process `δ`, the equilibrium
  `TidyR5InnovEqmMeasure.piM` with `u = i − φπ` is, almost surely, the only essentially bounded
  adapted equilibrium of the model with that rule; `reverse_engineer_piM_distinct`: with `φ ≠ 0`,
  equal disturbances force equal innovations almost surely, so different innovation processes
  need different disturbances for the same rate process.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5ReverseMeasure

open MeasureTheory Filter Topology FullModel TidyR5ExpectationsMeasure
open TidyR5StochasticPathsMeasure TidyR5InnovEqmMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eqs. (17.29)–(17.33), p. 420: the forward matrix `A` of the deviation system
`(x̃, π̃)_t = A E_t (x̃, π̃)_{t+1}` for the rule `ĩ = φπ̃`, `D = 1 + σκφ`. -/
noncomputable def devA (σ β κ φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / (1 + σ * κ * φ), σ * (1 - φ * β) / (1 + σ * κ * φ);
    κ / (1 + σ * κ * φ), (κ * σ * (1 - φ * β) + β * (1 + σ * κ * φ)) / (1 + σ * κ * φ)]

/-- Cochrane (2023), A1 (1.57): the trace of `A` is `(1 + β + σκ)/D`. -/
theorem tr2_devA (σ β κ φ : ℝ) :
    tr2 (devA σ β κ φ) = (1 + β + σ * κ) / (1 + σ * κ * φ) := by
  simp only [tr2, devA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  ring

/-- Cochrane (2023), A1 (1.57): the determinant of `A` is `β/D`. -/
theorem det2_devA {σ β κ φ : ℝ} (hD : 1 + σ * κ * φ ≠ 0) :
    det2 (devA σ β κ φ) = β / (1 + σ * κ * φ) := by
  simp only [det2, devA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_fin_one, Matrix.cons_val_one]
  field_simp
  ring

/-- Cochrane (2023), p. 420, on a probability space (the measure-theoretic `system_unique`): if
`A` is Schur stable, every essentially bounded adapted integrable a.e. solution of
`d_t = A E_t d_{t+1}` vanishes almost surely at every date. -/
theorem dev_zero_ae {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : SchurStable (tr2 A) (det2 A))
    {d : ℕ → Fin 2 → Ω → ℝ} (hda : ∀ i, StronglyAdapted S.𝓕 (fun t => d t i))
    (hdi : ∀ t i, Integrable (d t i) S.μ) {M : ℝ} (hdb : ∀ t i, ∀ᵐ ω ∂S.μ, |d t i ω| ≤ M)
    (hd : ∀ t i, d t i =ᵐ[S.μ] A i 0 • S.E t (d (t + 1) 0) + A i 1 • S.E t (d (t + 1) 1)) :
    ∀ t i, d t i =ᵐ[S.μ] 0 := by
  -- iterate: `d_t = Aᵏ E_t d_{t+k}`
  have hit : ∀ k t i, d t i =ᵐ[S.μ]
      (A ^ k) i 0 • S.E t (d (t + k) 0) + (A ^ k) i 1 • S.E t (d (t + k) 1) := by
    intro k
    induction k with
    | zero =>
      intro t i
      have h0 := S.E_of_stronglyMeasurable (hda 0 t) (hdi t 0)
      have h1 := S.E_of_stronglyMeasurable (hda 1 t) (hdi t 1)
      refine Eventually.of_forall fun ω => ?_
      simp only [add_zero, pow_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [h0, h1]
      fin_cases i <;> simp [Matrix.one_apply]
    | succ k ih =>
      intro t i
      have hle : t ≤ t + k := Nat.le_add_right t k
      have e : ∀ j : Fin 2, S.E t (d (t + k) j) =ᵐ[S.μ]
          A j 0 • S.E t (d (t + k + 1) 0) + A j 1 • S.E t (d (t + k + 1) 1) := by
        intro j
        have iE0 := S.integrable_E (t + k) (d (t + k + 1) 0)
        have iE1 := S.integrable_E (t + k) (d (t + k + 1) 1)
        filter_upwards [S.E_congr (hd (t + k) j) t, S.E_add (iE0.smul (A j 0)) (iE1.smul (A j 1)) t,
          S.E_smul (A j 0) (S.E (t + k) (d (t + k + 1) 0)) t,
          S.E_smul (A j 1) (S.E (t + k) (d (t + k + 1) 1)) t,
          S.E_tower hle (d (t + k + 1) 0), S.E_tower hle (d (t + k + 1) 1)] with ω a b c f g k'
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a b c f ⊢
        rw [a, b, c, f, g, k']
      filter_upwards [ih t i, e 0, e 1] with ω a b c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a b c ⊢
      rw [a, b, c, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
        Fin.sum_univ_two, show t + (k + 1) = t + k + 1 from rfl]
      ring
  intro t i
  have hk : ∀ k, ∀ᵐ ω ∂S.μ, |d t i ω| ≤ (|(A ^ k) i 0| + |(A ^ k) i 1|) * M := by
    intro k
    filter_upwards [hit k t i, S.abs_E_le (hdb (t + k) 0) t, S.abs_E_le (hdb (t + k) 1) t]
      with ω a b c
    rw [a]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left b (abs_nonneg _))
      (mul_le_mul_of_nonneg_left c (abs_nonneg _))
  filter_upwards [ae_all_iff.mpr hk] with ω h
  have hlim : Tendsto (fun k => (|(A ^ k) i 0| + |(A ^ k) i 1|) * M) atTop (𝓝 0) := by
    simpa using
      (((tendsto_pow_entry hA i 0).abs.add (tendsto_pow_entry hA i 1).abs).mul_const M)
  exact abs_nonpos_iff.mp (ge_of_tendsto' hlim h)

/-- Cochrane (2023), pp. 414 and 420, on a probability space (**uniqueness under a rule**): for
`σ, κ, β > 0` and `φ` in the determinacy region, two essentially bounded adapted equilibria of
(17.15)–(17.17) whose rates obey the same rule `i = φπ + u` (`i' − φπ' = i − φπ` a.s.)
coincide almost surely. -/
theorem rule_unique_ae {σ β κ φ M : ℝ}
    (hdet : TaylorDeterminacy.Determinate perfectForesight σ β κ φ 0)
    {i r x π i' r' x' π' : ℕ → Ω → ℝ} (h : ModelM S σ β κ i r x π)
    (h' : ModelM S σ β κ i' r' x' π')
    (hxa : StronglyAdapted S.𝓕 x) (hπa : StronglyAdapted S.𝓕 π)
    (hxa' : StronglyAdapted S.𝓕 x') (hπa' : StronglyAdapted S.𝓕 π')
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ M ∧ |π t ω| ≤ M ∧ |x' t ω| ≤ M ∧ |π' t ω| ≤ M)
    (hrule : ∀ t, i' t =ᵐ[S.μ] φ • π' t + (i t - φ • π t)) :
    ∀ t, x' t =ᵐ[S.μ] x t ∧ π' t =ᵐ[S.μ] π t := by
  obtain ⟨hD, hS⟩ := (TaylorDeterminacy.determinate_iff perfectForesight σ β κ φ 0).mp hdet
  simp only [mul_zero, add_zero] at hD hS
  have hA : SchurStable (tr2 (devA σ β κ φ)) (det2 (devA σ β κ φ)) := by
    rw [tr2_devA, det2_devA hD]; exact hS
  set d : ℕ → Fin 2 → Ω → ℝ := fun t => ![x' t - x t, π' t - π t] with hd
  obtain ⟨hint, heq⟩ := h
  obtain ⟨hint', heq'⟩ := h'
  have hdi : ∀ t j, Integrable (d t j) S.μ := fun t j => by
    fin_cases j
    · exact (hint' t).2.2.1.sub (hint t).2.2.1
    · exact (hint' t).2.2.2.sub (hint t).2.2.2
  have hda : ∀ j, StronglyAdapted S.𝓕 (fun t => d t j) := fun j t => by
    fin_cases j
    · exact (hxa' t).sub (hxa t)
    · exact (hπa' t).sub (hπa t)
  have hdb : ∀ t j, ∀ᵐ ω ∂S.μ, |d t j ω| ≤ 2 * M := fun t j => by
    filter_upwards [hb t] with ω ⟨a, b, c, e⟩
    fin_cases j
    · change |x' t ω - x t ω| ≤ 2 * M
      exact (abs_sub _ _).trans (by linarith)
    · change |π' t ω - π t ω| ≤ 2 * M
      exact (abs_sub _ _).trans (by linarith)
  have hrel2 : ∀ t, (x' t - x t =ᵐ[S.μ] (1 / (1 + σ * κ * φ)) •
        S.E t (x' (t + 1) - x (t + 1)) + (σ * (1 - φ * β) / (1 + σ * κ * φ)) •
        S.E t (π' (t + 1) - π (t + 1))) ∧
      (π' t - π t =ᵐ[S.μ] (κ / (1 + σ * κ * φ)) • S.E t (x' (t + 1) - x (t + 1)) +
        ((κ * σ * (1 - φ * β) + β * (1 + σ * κ * φ)) / (1 + σ * κ * φ)) •
        S.E t (π' (t + 1) - π (t + 1))) := by
    intro t
    obtain ⟨a1, a2, a3⟩ := heq t
    obtain ⟨b1, b2, b3⟩ := heq' t
    have hall : ∀ᵐ ω ∂S.μ, (1 + σ * κ * φ) * (x' t ω - x t ω) =
          (S.E t (x' (t + 1)) ω - S.E t (x (t + 1)) ω) +
            σ * (1 - φ * β) * (S.E t (π' (t + 1)) ω - S.E t (π (t + 1)) ω) ∧
        (1 + σ * κ * φ) * (π' t ω - π t ω) =
          κ * (S.E t (x' (t + 1)) ω - S.E t (x (t + 1)) ω) +
            (κ * σ * (1 - φ * β) + β * (1 + σ * κ * φ)) *
              (S.E t (π' (t + 1)) ω - S.E t (π (t + 1)) ω) := by
      filter_upwards [a1, a2, a3, b1, b2, b3, hrule t] with ω e1 e2 e3 f1 f2 f3 g
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul] at e1 e2 e3 f1 f2 f3 g
      have hm : (1 + σ * κ * φ) * (x' t ω - x t ω) =
          (S.E t (x' (t + 1)) ω - S.E t (x (t + 1)) ω) +
            σ * (1 - φ * β) * (S.E t (π' (t + 1)) ω - S.E t (π (t + 1)) ω) := by
        linear_combination (f1 - e1) + σ * (f2 - e2) - σ * g - σ * φ * (f3 - e3)
      exact ⟨hm, by linear_combination (1 + σ * κ * φ) * (f3 - e3) + κ * hm⟩
    have k0 := S.E_sub (hint' (t + 1)).2.2.1 (hint (t + 1)).2.2.1 t
    have k1 := S.E_sub (hint' (t + 1)).2.2.2 (hint (t + 1)).2.2.2 t
    refine ⟨?_, ?_⟩
    · filter_upwards [hall, k0, k1] with ω hm c0 c1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at c0 c1 ⊢
      rw [c0, c1]
      have : x' t ω - x t ω = ((S.E t (x' (t + 1)) ω - S.E t (x (t + 1)) ω) +
          σ * (1 - φ * β) * (S.E t (π' (t + 1)) ω - S.E t (π (t + 1)) ω)) /
            (1 + σ * κ * φ) := by
        rw [eq_div_iff hD]; linarith [hm.1]
      rw [this]
      ring
    · filter_upwards [hall, k0, k1] with ω hm c0 c1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at c0 c1 ⊢
      rw [c0, c1]
      have : π' t ω - π t ω = (κ * (S.E t (x' (t + 1)) ω - S.E t (x (t + 1)) ω) +
          (κ * σ * (1 - φ * β) + β * (1 + σ * κ * φ)) *
            (S.E t (π' (t + 1)) ω - S.E t (π (t + 1)) ω)) / (1 + σ * κ * φ) := by
        rw [eq_div_iff hD]; linarith [hm.2]
      rw [this]
      ring
  have hrel : ∀ t j, d t j =ᵐ[S.μ]
      devA σ β κ φ j 0 • S.E t (d (t + 1) 0) + devA σ β κ φ j 1 • S.E t (d (t + 1) 1) := by
    intro t j
    fin_cases j
    · exact (hrel2 t).1
    · exact (hrel2 t).2
  have hz := dev_zero_ae S hA hda hdi hdb hrel
  intro t
  refine ⟨?_, ?_⟩
  · filter_upwards [hz t 0] with ω a
    change x' t ω - x t ω = 0 at a
    linarith
  · filter_upwards [hz t 1] with ω a
    change π' t ω - π t ω = 0 at a
    linarith

/-- Cochrane (2023), p. 414, on a probability space: output along `piM`,
`x_t = (π_t − β E_t π_{t+1})/κ`. -/
noncomputable def xM (σ β κ : ℝ) (i : ℕ → Ω → ℝ) (p : Ω → ℝ) (δ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => κ⁻¹ • (piM S σ β κ i p δ t - β • S.E t (piM S σ β κ i p δ (t + 1)))

/-- Cochrane (2023), p. 414 ("if fed these `{u_t}` paths, the model produces the given interest
rate and inflation paths"), on a probability space: for `σ, κ, β > 0`, `φ` in the determinacy
region and every innovation process `δ`, every essentially bounded adapted equilibrium whose
rates obey `i' = φπ' + u` with the reverse-engineered `u = i − φ piM` equals `(xM, piM)`
almost surely. -/
theorem reverse_engineer_piM {σ β κ φ M Mp Mδ M' : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hdet : TaylorDeterminacy.Determinate perfectForesight σ β κ φ 0) {i : ℕ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) {p : Ω → ℝ}
    (hp0 : StronglyMeasurable[S.𝓕 0] p) (hp : ∀ᵐ ω ∂S.μ, |p ω| ≤ Mp) {δ : ℕ → Ω → ℝ}
    (hδa : StronglyAdapted S.𝓕 δ) (hδ : ∀ t, ∀ᵐ ω ∂S.μ, |δ t ω| ≤ Mδ)
    (hδ0 : ∀ t, S.E t (δ (t + 1)) =ᵐ[S.μ] 0) {i' r' x' π' : ℕ → Ω → ℝ}
    (h' : ModelM S σ β κ i' r' x' π') (hxa' : StronglyAdapted S.𝓕 x')
    (hπa' : StronglyAdapted S.𝓕 π') (hb' : ∀ t, ∀ᵐ ω ∂S.μ, |x' t ω| ≤ M' ∧ |π' t ω| ≤ M')
    (hrule : ∀ t, i' t =ᵐ[S.μ] φ • π' t + (i t - φ • piM S σ β κ i p δ t)) :
    ∀ t, x' t =ᵐ[S.μ] xM S σ β κ i p δ t ∧ π' t =ᵐ[S.μ] piM S σ β κ i p δ t := by
  have ha := mul_pos hσ hκ
  obtain ⟨had, ⟨K, hK⟩, -, -, hm⟩ := piM_equilibrium S ha hβ hia hi hp0 hp hδa hδ hδ0
  have hxa : StronglyAdapted S.𝓕 (xM S σ β κ i p δ) := fun t =>
    ((had t).sub ((S.stronglyMeasurable_E t _).const_smul β)).const_smul _
  set Mb := max (|κ⁻¹| * (K + |β| * K)) (max K M')
  refine rule_unique_ae S (M := Mb) hdet hm h' hxa had hxa' hπa' (fun t => ?_) hrule
  filter_upwards [hK t, S.abs_E_le (hK (t + 1)) t, hb' t] with ω a b ⟨c, e⟩
  refine ⟨?_, a.trans ((le_max_left _ _).trans (le_max_right _ _)),
    c.trans ((le_max_right _ _).trans (le_max_right _ _)),
    e.trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  refine le_trans ?_ (le_max_left _ _)
  simp only [xM, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add a ?_)) (abs_nonneg _)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left b (abs_nonneg _)

/-- Cochrane (2023), p. 411 ("multiple disturbance paths `u_t` produce the same interest-rate
path"), on a probability space: with `φ ≠ 0`, if two equilibria `piM` with innovation processes
`δ`, `δ'` have the same reverse-engineered disturbance `u = i − φπ` almost surely, their
innovations agree almost surely; different innovation processes need different disturbances. -/
theorem reverse_engineer_piM_distinct {σ β κ φ M Mp Mδ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    (hφ : φ ≠ 0) {i : ℕ → Ω → ℝ} (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) {p : Ω → ℝ} (hp0 : StronglyMeasurable[S.𝓕 0] p)
    (hp : ∀ᵐ ω ∂S.μ, |p ω| ≤ Mp) {δ δ' : ℕ → Ω → ℝ} (hδa : StronglyAdapted S.𝓕 δ)
    (hδ : ∀ t, ∀ᵐ ω ∂S.μ, |δ t ω| ≤ Mδ) (hδ0 : ∀ t, S.E t (δ (t + 1)) =ᵐ[S.μ] 0)
    (hδa' : StronglyAdapted S.𝓕 δ') (hδ' : ∀ t, ∀ᵐ ω ∂S.μ, |δ' t ω| ≤ Mδ)
    (hδ0' : ∀ t, S.E t (δ' (t + 1)) =ᵐ[S.μ] 0)
    (hu : ∀ t, i t - φ • piM S σ β κ i p δ t =ᵐ[S.μ] i t - φ • piM S σ β κ i p δ' t) :
    ∀ t, δ (t + 1) =ᵐ[S.μ] δ' (t + 1) := by
  obtain ⟨-, -, hin, -, -⟩ := piM_equilibrium S ha hβ hia hi hp0 hp hδa hδ hδ0
  obtain ⟨-, -, hin', -, -⟩ := piM_equilibrium S ha hβ hia hi hp0 hp hδa' hδ' hδ0'
  have heq : ∀ t, piM S σ β κ i p δ t =ᵐ[S.μ] piM S σ β κ i p δ' t := fun t => by
    filter_upwards [hu t] with ω a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a
    exact mul_left_cancel₀ hφ (by linarith)
  intro t
  filter_upwards [hin t, hin' t, heq (t + 1), S.E_congr (heq (t + 1)) t] with ω a b c e
  simp only [Pi.sub_apply] at a b
  rw [← a, ← b, c, e]

end Cochrane.KeynesianStickyPrices.TidyR5ReverseMeasure
