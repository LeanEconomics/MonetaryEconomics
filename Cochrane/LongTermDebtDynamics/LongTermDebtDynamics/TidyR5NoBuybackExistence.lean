/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5Pathwise
import LongTermDebtDynamics.PolicyConstraints

/-!
# Existence of a positive equilibrium without buy-backs

Cochrane (2023), §7.4, pp. 224–226, equations (7.14)–(7.17), with the flow and present-value
relations (7.1), (7.2), (7.5) of pp. 213 and 216.

`GeneralFormula.price_unique_noBuyback` shows that without buy-backs at most one positive price
path satisfies every flow and present-value relation. This module settles existence.

* `weight_mem_unit`: without buy-backs every weight `W_t^{(m)}` of (7.17) lies in `[0, 1]`, because
  each column of sale fractions sums to at most one. So (7.17) converges absolutely for bounded
  surpluses whatever the rows of the sale fractions look like.
* `formulaW_solves_noBuyback`: without buy-backs, (7.17) solves the flow system (7.14) for every
  expectation system with the pull-out property (no row condition).
* `equilibrium_of_formulaW_pos`, `maturing_eq_formulaW`, `exists_equilibrium_iff`: **the
  exact condition.** Without buy-backs, a positive equilibrium price path exists if and only if
  the weighted present value (7.17) is strictly positive at every date and state; it is then
  `1/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m} / B_{t−1}^{(t)}`, and it is unique.
* `existsUnique_of_pos_surplus`: positive bounded surpluses suffice.
* `cb_*`: **no buy-backs alone do not give existence.** With debt of every maturity, no trading,
  and surpluses `s_0 = −1`, `s_t = 1` for `t ≥ 1`, there is no positive price level at date 0,
  although the present value of surpluses at date 0 is positive for `β > 1/2`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence

open Filter Topology MaturityStructure GeneralFormula TidyR5Pathwise

/-- Cochrane (2023), §7.4, p. 226: with nonnegative sale fractions whose columns sum to at most
one, every weight `W_t^{(m)}` lies in `[0, 1]`. -/
theorem weight_mem_unit {A : ℕ → ℕ → ℝ} (hA0 : ∀ t m, t < m → 0 ≤ A t m)
    (hcolA : ∀ m, ∑ t ∈ Finset.range m, A t m ≤ 1) (m : ℕ) :
    ∀ t, 0 ≤ weight A t m ∧ weight A t m ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t
    rcases m with _ | k
    · simp [weight_zero]
    · rw [weight_succ]
      constructor
      · exact Finset.sum_nonneg fun n hn =>
          mul_nonneg (hA0 _ _ (by have := Finset.mem_range.mp hn; omega))
            (ih n (Finset.mem_range.mp hn) t).1
      · have h1 : ∑ n ∈ Finset.range (k + 1), A (t + n) (t + (k + 1)) * weight A t n ≤
            ∑ n ∈ Finset.range (k + 1), A (t + n) (t + (k + 1)) :=
          Finset.sum_le_sum fun n hn => mul_le_of_le_one_right
            (hA0 _ _ (by have := Finset.mem_range.mp hn; omega))
            (ih n (Finset.mem_range.mp hn) t).2
        have h2 : ∑ n ∈ Finset.range (k + 1), A (t + n) (t + (k + 1)) =
            ∑ u ∈ Finset.Ico t (t + (k + 1)), A u (t + (k + 1)) := by
          rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
        have h3 : ∑ u ∈ Finset.Ico t (t + (k + 1)), A u (t + (k + 1)) ≤
            ∑ u ∈ Finset.range (t + (k + 1)), A u (t + (k + 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun u hu => Finset.mem_range.mpr (Finset.mem_Ico.mp hu).2)
            fun u hu _ => hA0 _ _ (Finset.mem_range.mp hu)
        linarith [hcolA (t + (k + 1))]

/-- Cochrane (2023), §7.4: with nonnegative sale fractions whose columns sum to at most one, each
fraction `A_t^{(m)}` (`t < m`) lies in `[0, 1]`. -/
theorem frac_le_one {A : ℕ → ℕ → ℝ} (hA0 : ∀ t m, t < m → 0 ≤ A t m)
    (hcolA : ∀ m, ∑ t ∈ Finset.range m, A t m ≤ 1) {t m : ℕ} (htm : t < m) : A t m ≤ 1 :=
  (Finset.single_le_sum (fun i hi => hA0 i m (Finset.mem_range.mp hi))
    (Finset.mem_range.mpr htm)).trans (hcolA m)

/-- Cochrane (2023), eq. (7.17), p. 226: with weights in `[0, 1]` and `0 ≤ β < 1`,
`∑_m β^m |W_t^{(m)}|` converges with sum at most `1/(1−β)`. -/
theorem weight_series_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {A : ℕ → ℕ → ℝ}
    (hA0 : ∀ t m, t < m → 0 ≤ A t m) (hcolA : ∀ m, ∑ t ∈ Finset.range m, A t m ≤ 1) (u : ℕ) :
    Summable (fun m => β ^ m * |weight A u m|) ∧
      ∑' m, β ^ m * |weight A u m| ≤ 1 / (1 - β) := by
  have hb : ∀ m, β ^ m * |weight A u m| ≤ β ^ m := fun m => by
    have h := weight_mem_unit hA0 hcolA m u
    rw [abs_of_nonneg h.1]
    exact mul_le_of_le_one_right (pow_nonneg hβ0 m) h.2
  have hg := summable_geometric_of_lt_one hβ0 hβ1
  have hs : Summable (fun m => β ^ m * |weight A u m|) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg hβ0 m) (abs_nonneg _)) hb hg
  refine ⟨hs, (Summable.tsum_le_tsum hb hs hg).trans ?_⟩
  rw [tsum_geometric_of_lt_one hβ0 hβ1, one_div]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: without buy-backs the pathwise weighted
present value `Z` solves the flow system state by state, and `|Z_t| ≤ M/(1−β)`. -/
theorem pathZΩ_noBuyback {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {A : ℕ → ℕ → Ω → ℝ}
    (hA0 : ∀ t m ω, t < m → 0 ≤ A t m ω) (hcolA : ∀ m ω, ∑ t ∈ Finset.range m, A t m ω ≤ 1)
    {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * (A t (t + (j + 1)) ω *
      pathZΩ β A s (t + (j + 1)) ω)) (pathZΩ β A s t ω - s t ω)) ∧
      ∀ t ω, |pathZΩ β A s t ω| ≤ M / (1 - β) := by
  have hW := fun ω => weight_series_le hβ0 hβ1 (A := fun u v => A u v ω)
    (fun t m h => hA0 t m ω h) (fun m => hcolA m ω)
  refine ⟨fun t ω => ?_, fun t ω => ?_⟩
  · have hrow : Summable (fun j : ℕ => β ^ (j + 1) * |A t (t + (j + 1)) ω|) := by
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _))
        (fun j => ?_) ((summable_geometric_of_lt_one hβ0 hβ1).comp_injective
          (add_left_injective 1))
      rw [abs_of_nonneg (hA0 _ _ ω (by omega))]
      exact mul_le_of_le_one_right (pow_nonneg hβ0 _) (frac_le_one (A := fun u v => A u v ω)
        (fun t m h => hA0 t m ω h) (fun m => hcolA m ω) (by omega))
    exact pathZ_solves hβ0 (fun u => hsb u ω) (fun u => (hW ω u).1) (fun u => (hW ω u).2) t hrow
  · have := (pathZ_summable_bound hβ0 (fun u => hsb u ω) (hW ω t).1 (hW ω t).2).2
    rw [one_div_mul_eq_div] at this
    exact this

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: **without buy-backs, (7.17) solves the
flow system**, with no row condition. Nonnegative sale fractions with column sums at most one,
each `A_t^{(t+j+1)}` known at `t + j`, bounded adapted surpluses, `0 ≤ β < 1`: then
`y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}` (an absolutely convergent series with `|y_t| ≤ M/(1−β)`)
satisfies every flow condition (7.14), under uncertainty, and is known at `t`. -/
theorem formulaW_solves_noBuyback (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {A : ℕ → ℕ → Ω → ℝ} (hA0 : ∀ t m ω, t < m → 0 ≤ A t m ω)
    (hcolA : ∀ m ω, ∑ t ∈ Finset.range m, A t m ω ≤ 1)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t, MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t) ∧
      (∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (formulaW 𝔼 β A s t ω)) ∧
      (∀ t ω, |formulaW 𝔼 β A s t ω| ≤ M / (1 - β)) ∧
      ∀ t, 𝔼.E t (formulaW 𝔼 β A s t) = formulaW 𝔼 β A s t := by
  obtain ⟨hpw, hZb⟩ := pathZΩ_noBuyback hβ0 hβ1 hA0 hcolA hsb
  have hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω)
      (𝔼.E t (pathZΩ β A s t) ω) := by
    intro t ω
    have hf : ∀ m ω', |β ^ m * (weight A t m ω' * s (t + m) ω')| ≤ β ^ m * M := by
      intro m ω'
      have h := weight_mem_unit (A := fun u v => A u v ω') (fun t m h => hA0 t m ω' h)
        (fun m => hcolA m ω') m t
      rw [← weight_apply] at h
      rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hβ0, abs_of_nonneg h.1]
      exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (abs_nonneg _) h.2).trans
        (hsb _ ω')) (pow_nonneg hβ0 m)
    have h := hasSum_E_of_dom 𝔼 ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M) hf t ω
    have hZ : (fun ω' => ∑' m, β ^ m * (weight A t m ω' * s (t + m) ω')) = pathZΩ β A s t := by
      funext ω'
      simp only [pathZΩ, pathZ, weight_apply]
    rw [hZ] at h
    refine h.congr_fun fun m => ?_
    rw [formulaTerm, show (fun ω' => β ^ m * (weight A t m ω' * s (t + m) ω')) =
      β ^ m • (weight A t m * s (t + m)) from rfl, map_smul]
    rfl
  have hex2 : ∀ t ω, HasSum (fun j : ℕ => 𝔼.E t (fun ω' => β ^ (j + 1) *
      (A t (t + (j + 1)) ω' * pathZΩ β A s (t + (j + 1)) ω')) ω)
      (𝔼.E t (fun ω' => ∑' j : ℕ, β ^ (j + 1) *
        (A t (t + (j + 1)) ω' * pathZΩ β A s (t + (j + 1)) ω')) ω) := by
    intro t ω
    refine hasSum_E_of_dom 𝔼 (((summable_geometric_of_lt_one hβ0 hβ1).comp_injective
      (add_left_injective 1)).mul_right (M / (1 - β))) (fun j ω' => ?_) t ω
    have hA1 : |A t (t + (j + 1)) ω'| ≤ 1 := by
      rw [abs_of_nonneg (hA0 _ _ ω' (by omega))]
      exact frac_le_one (A := fun u v => A u v ω') (fun t m h => hA0 t m ω' h)
        (fun m => hcolA m ω') (by omega)
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hβ0]
    simp only [Function.comp_apply]
    exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_left (abs_nonneg _) hA1).trans
      (hZb _ ω')) (pow_nonneg hβ0 _)
  have hfw := formulaW_eq_E 𝔼 hex1
  refine ⟨formulaW_solves_of_exchange 𝔼 hpo hA hs hpw hex1 hex2, fun t ω => ?_,
    fun t ω => ?_, formulaW_adapted_of_exchange 𝔼 hex1⟩
  · rw [hfw t]; exact hex1 t ω
  · rw [hfw t]; exact 𝔼.abs_E_le (hZb t) t ω

/-! ### Positive equilibria without buy-backs -/

/-- Cochrane (2023), §7.4: without buy-backs, debt due at `m` outstanding at `t ≤ m` is at most the
debt coming due at `m`, `B_{t−1}^{(m)} ≤ B_{m−1}^{(m)}`. -/
theorem noBuyback_le_maturing {D : ℕ → ℕ → Ω → ℝ} (h : NoBuyback D) (ω : Ω) (m : ℕ) :
    ∀ k t, t + k = m → D t m ω ≤ D m m ω := by
  intro k
  induction k with
  | zero => intro t htm; rw [← htm, add_zero]
  | succ k ih =>
    intro t htm
    exact (h.2.1 t m ω (by omega)).trans (ih (t + 1) (by omega))

/-- Cochrane (2023), §7.4, p. 225: with predetermined debt and quotients of known variables known,
the sale fraction `A_t^{(t+j+1)}` is known at `t + j`, the date of the last sale before maturity. -/
theorem fracSold_known (hdc : PolicyConstraints.DivClosed 𝔼) {D : ℕ → ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (t j : ℕ) :
    𝔼.E (t + j) (fracSold D t (t + (j + 1))) = fracSold D t (t + (j + 1)) := by
  unfold fracSold
  apply hdc
  · rw [map_sub, Predetermined.known_succ 𝔼 hD (by omega), Predetermined.known 𝔼 hD (by omega)]
  · have := hD.2 (t + j) (t + (j + 1))
    rwa [show t + j + 1 = t + (j + 1) by omega] at this

/-- Cochrane (2023), eq. (7.17), p. 225: the candidate equilibrium,
`1/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m} / B_{t−1}^{(t)}`. -/
noncomputable def eqX (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  formulaW 𝔼 β (fracSold D) s t / D t t

/-- Cochrane (2023), §7.4 and eq. (7.17), pp. 225–226: **sufficiency.** Without buy-backs
(`GeneralFormula.NoBuyback`), with predetermined debt, quotients of known variables known,
`0 < β < 1` and bounded adapted surpluses, if the weighted present value (7.17) is strictly
positive at every date and state, then `1/P_t = eqX` is a positive equilibrium: adapted, positive,
satisfying every flow condition (7.1) and every present-value relation (7.2)/(7.5). -/
theorem equilibrium_of_formulaW_pos (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hpos : ∀ t ω, 0 < formulaW 𝔼 β (fracSold D) s t ω) :
    𝔼.Adapted (eqX 𝔼 β D s) ∧ (∀ t ω, 0 < eqX 𝔼 β D s t ω) ∧
      (∀ t, RealFlow 𝔼 β D (eqX 𝔼 β D s) s t) ∧ ∀ t, PresentValue 𝔼 β D (eqX 𝔼 β D s) s t := by
  obtain ⟨hsys, -, hzb, hzad⟩ := formulaW_solves_noBuyback 𝔼 hpo hβ0.le hβ1
    (A := fracSold D) (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (fracSold_known 𝔼 hdc hD) hs hsb
  have hDmm : ∀ m ω, D m m ω ≠ 0 := fun m ω => (hnb.2.2 m ω).ne'
  set x := eqX 𝔼 β D s with hxdef
  have hx : 𝔼.Adapted x := fun t => hdc t _ _ (hzad t) (Predetermined.known 𝔼 hD le_rfl t)
  have hy : (fun u => D u u * x u) = formulaW 𝔼 β (fracSold D) s := by
    funext u ω
    simp only [hxdef, eqX, Pi.mul_apply, Pi.div_apply]
    field_simp [hDmm u ω]
  have hflow : ∀ t, RealFlow 𝔼 β D x s t := fun t =>
    (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mpr (by rw [hy]; exact hsys t)
  have hcore : ∀ t j ω, |D t (t + j) ω * 𝔼.E t (x (t + j)) ω| ≤ M / (1 - β) := by
    intro t j ω
    have hpull := congrFun (hpo t _ (x (t + j)) (Predetermined.known 𝔼 hD le_rfl (t + j))) ω
    simp only [Pi.mul_apply] at hpull
    rw [← hpull]
    refine 𝔼.abs_E_le (fun ω' => ?_) t ω
    have hr0 : 0 ≤ D t (t + j) ω' := hnb.nonneg t (t + j) (by omega) ω'
    have hr1 : D t (t + j) ω' ≤ D (t + j) (t + j) ω' :=
      noBuyback_le_maturing hnb ω' (t + j) j t rfl
    have hpos' := hnb.2.2 (t + j) ω'
    simp only [Pi.mul_apply, hxdef, eqX, Pi.div_apply]
    rw [show D t (t + j) ω' * (formulaW 𝔼 β (fracSold D) s (t + j) ω' / D (t + j) (t + j) ω') =
      D t (t + j) ω' / D (t + j) (t + j) ω' * formulaW 𝔼 β (fracSold D) s (t + j) ω' by ring,
      abs_mul, abs_of_nonneg (div_nonneg hr0 hpos'.le)]
    exact mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hpos').mpr hr1) |>.trans (hzb _ ω')
  have hdt : ∀ t j ω, |debtTerm 𝔼 β D x t j ω| ≤ β ^ j * (M / (1 - β)) := by
    intro t j ω
    rw [debtTerm, abs_mul, abs_pow, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left (hcore t j ω) (pow_nonneg hβ0.le j)
  have hgeo : Summable (fun j : ℕ => β ^ j * (M / (1 - β))) :=
    (summable_geometric_of_lt_one hβ0.le hβ1).mul_right _
  have hdom : ∀ t, DebtDominated 𝔼 β D x t := fun t => ⟨_, hgeo, hdt t⟩
  have hsumm : ∀ t ω, Summable (fun j => debtTerm 𝔼 β D x t j ω) := fun t ω =>
    Summable.of_norm_bounded hgeo (fun j => by rw [Real.norm_eq_abs]; exact hdt t j ω)
  have hV : ∀ t ω, |debtValue 𝔼 β D x t ω| ≤ ∑' j : ℕ, β ^ j * (M / (1 - β)) := by
    intro t ω
    have h0 := norm_tsum_le_tsum_norm (f := fun j => debtTerm 𝔼 β D x t j ω)
      (by simpa only [Real.norm_eq_abs] using (hsumm t ω).abs)
    simp only [Real.norm_eq_abs] at h0
    exact h0.trans (Summable.tsum_le_tsum (fun j => hdt t j ω) (hsumm t ω).abs hgeo)
  refine ⟨hx, fun t ω => div_pos (hpos t ω) (hnb.2.2 t ω), hflow, fun t => ?_⟩
  exact presentValue_of_bounded 𝔼 hpo hβ0.le hβ1 hD hx hs hsb hsumm hdom hflow hV t

/-- Cochrane (2023), §7.4 and eq. (7.17), pp. 225–226: **necessity.** Without buy-backs, in every
equilibrium with nonnegative `1/P` (adapted, every flow and present-value relation), the real
value of maturing debt is the weighted present value: `B_{t−1}^{(t)}/P_t =
E_t ∑_m β^m W_t^{(m)} s_{t+m}`. -/
theorem maturing_eq_formulaW (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hx : 𝔼.Adapted x) (hx0 : ∀ t ω, 0 ≤ x t ω) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hpv : ∀ t, PresentValue 𝔼 β D x s t) (t : ℕ) (ω : Ω) :
    D t t ω * x t ω = formulaW 𝔼 β (fracSold D) s t ω := by
  obtain ⟨hsys, -, hzb, -⟩ := formulaW_solves_noBuyback 𝔼 hpo hβ0.le hβ1
    (A := fracSold D) (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (fracSold_known 𝔼 hdc hD) hs hsb
  have hDmm : ∀ m ω, D m m ω ≠ 0 := fun m ω => (hnb.2.2 m ω).ne'
  have hD0 : ∀ t j ω, 0 ≤ D t (t + j) ω := fun t j ω => hnb.nonneg t (t + j) (by omega) ω
  have hy := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow t)
  have hb : ∀ t ω, |D t t ω * x t ω| ≤ M / (1 - β) := fun t ω => by
    obtain ⟨h1, h2⟩ := bounded_of_presentValue 𝔼 hβ0.le hβ1 hx hx0 hD0 hsb (hpv t) ω
    rw [abs_of_nonneg h1]; exact h2
  have hzero := unique_of_noBuyback 𝔼 hβ0 hβ1 (A := fracSold D)
    (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (homogeneous_of_two 𝔼 hy hsys) (K := M / (1 - β) + M / (1 - β))
    (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hb t ω) (hzb t ω)))
  have := congrFun (congrFun hzero t) ω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- Cochrane (2023), §7.4, pp. 225–226: **the exact condition for existence without buy-backs.**
Without buy-backs, with predetermined debt, quotients of known variables known, `0 < β < 1` and
bounded adapted surpluses, a positive equilibrium price path exists if and only if the weighted
present value (7.17) is strictly positive at every date and state. -/
theorem exists_equilibrium_iff (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∃ x : ℕ → Ω → ℝ, 𝔼.Adapted x ∧ (∀ t ω, 0 < x t ω) ∧ (∀ t, RealFlow 𝔼 β D x s t) ∧
      ∀ t, PresentValue 𝔼 β D x s t) ↔ ∀ t ω, 0 < formulaW 𝔼 β (fracSold D) s t ω := by
  constructor
  · rintro ⟨x, hx, hxpos, hflow, hpv⟩ t ω
    rw [← maturing_eq_formulaW 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb hx (fun t ω => (hxpos t ω).le)
      hflow hpv t ω]
    exact mul_pos (hnb.2.2 t ω) (hxpos t ω)
  · intro hpos
    exact ⟨eqX 𝔼 β D s, equilibrium_of_formulaW_pos 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb hpos⟩

/-- Cochrane (2023), eq. (7.17), p. 225: with weights in `[0, 1]` and nonnegative surpluses,
(7.17) is at least the current surplus, `E_t ∑_m β^m W_t^{(m)} s_{t+m} ≥ s_t`. -/
theorem formulaW_ge_surplus (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hs0 : ∀ t ω, 0 ≤ s t ω) (t : ℕ) (ω : Ω) : s t ω ≤ formulaW 𝔼 β (fracSold D) s t ω := by
  obtain ⟨-, hsum, -, -⟩ := formulaW_solves_noBuyback 𝔼 hpo hβ0.le hβ1
    (A := fracSold D) (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (fracSold_known 𝔼 hdc hD) hs hsb
  have h0 : formulaTerm 𝔼 β (fracSold D) s t 0 ω = s t ω := by
    simp [formulaTerm, weight_zero, hs t]
  rw [← h0]
  refine le_hasSum (hsum t ω) 0 fun m _ => ?_
  rw [formulaTerm]
  refine mul_nonneg (pow_nonneg hβ0.le m) ?_
  have hnn : (fun _ => (0 : ℝ)) ≤ weight (fracSold D) t m * s (t + m) := fun ω' => by
    have h := weight_mem_unit (A := fun u v => fracSold D u v ω')
      (fun t m h => hnb.frac_nonneg t m ω' h) (fun m => hnb.col_le_one m ω') m t
    rw [← weight_apply] at h
    exact mul_nonneg h.1 (hs0 _ ω')
  have := 𝔼.mono t hnn ω
  rwa [𝔼.const] at this

/-- Cochrane (2023), §7.4, pp. 225–226: **positive surpluses suffice.** Without buy-backs, with
predetermined debt, quotients of known variables known, `0 < β < 1` and bounded adapted strictly
positive surpluses, there is exactly one positive equilibrium price path (every flow and
present-value relation), and it is `1/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m} / B_{t−1}^{(t)}`. -/
theorem existsUnique_of_pos_surplus (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼)
    {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ} {s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hnb : NoBuyback D) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hspos : ∀ t ω, 0 < s t ω) :
    ∃! x : ℕ → Ω → ℝ, 𝔼.Adapted x ∧ (∀ t ω, 0 < x t ω) ∧ (∀ t, RealFlow 𝔼 β D x s t) ∧
      ∀ t, PresentValue 𝔼 β D x s t := by
  have hpos : ∀ t ω, 0 < formulaW 𝔼 β (fracSold D) s t ω := fun t ω =>
    (hspos t ω).trans_le (formulaW_ge_surplus 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb
      (fun t ω => (hspos t ω).le) t ω)
  refine ⟨eqX 𝔼 β D s, equilibrium_of_formulaW_pos 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb hpos, ?_⟩
  rintro x' ⟨hx', hxpos', hflow', hpv'⟩
  obtain ⟨hx, hxpos, hflow, hpv⟩ := equilibrium_of_formulaW_pos 𝔼 hpo hdc hβ0 hβ1 hD hnb hs hsb
    hpos
  exact price_unique_noBuyback 𝔼 hpo hβ0 hβ1 hD hnb hx' hx (fun t ω => (hxpos' t ω).le)
    (fun t ω => (hxpos t ω).le) hsb hflow' hflow hpv' hpv

/-! ### No buy-backs alone do not give existence -/

/-- Cochrane (2023), §7.4 (counterexample to existence): one unit of debt due at every date, never
traded, `B_{t−1}^{(m)} = 1`. -/
def cbD : ℕ → ℕ → Unit → ℝ := fun _ _ _ => 1

/-- Cochrane (2023), §7.4 (counterexample to existence): a deficit at date 0 and surpluses after,
`s_0 = −1`, `s_t = 1` for `t ≥ 1`. -/
noncomputable def cbS : ℕ → Unit → ℝ := fun t _ => if t = 0 then -1 else 1

/-- Cochrane (2023), §7.4: the counterexample never buys back debt. -/
theorem cb_noBuyback : NoBuyback cbD :=
  ⟨fun _ _ => zero_le_one, fun _ _ _ _ => le_rfl, fun _ _ => one_pos⟩

/-- Cochrane (2023), §7.4: the counterexample's debt is predetermined (perfect foresight). -/
theorem cb_predetermined : Predetermined perfectForesight cbD := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Cochrane (2023), §7.4: the counterexample's surpluses are bounded, `|s_t| ≤ 1`. -/
theorem cb_bounded (t : ℕ) (u : Unit) : |cbS t u| ≤ 1 := by
  unfold cbS; split_ifs <;> simp

/-- Cochrane (2023), §7.4 (E7.4, existence): **no buy-backs alone do not give a positive
equilibrium.** In the counterexample no positive price level satisfies even the date-0 flow
condition (7.1), whatever `β`: with no sales it reads `B_{−1}^{(0)}/P_0 = s_0 = −1`. -/
theorem cb_no_positive_price (β : ℝ) :
    ¬ ∃ x : ℕ → Unit → ℝ, (∀ t u, 0 < x t u) ∧ RealFlow perfectForesight β cbD x cbS 0 := by
  rintro ⟨x, hx, hflow⟩
  have h := hflow ()
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales cbD 0 (0 + (j + 1)) () *
      perfectForesight.E 0 (x (0 + (j + 1))) ())) = fun _ => 0 := by
    funext j; simp [sales, cbD]
  rw [hz] at h
  have := h.unique hasSum_zero
  simp only [cbD, cbS, one_mul, ↓reduceIte] at this
  linarith [hx 0 ()]

/-- Cochrane (2023), §7.4 (E7.4, existence): in the counterexample the present value of surpluses
at date 0 is `(2β − 1)/(1 − β)`, positive for `1/2 < β < 1`: a positive present value of surpluses
does not rescue existence. -/
theorem cb_pv_pos {β : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) :
    HasSum (fun k => surplusTerm perfectForesight β cbS 0 k ()) ((2 * β - 1) / (1 - β)) ∧
      0 < (2 * β - 1) / (1 - β) := by
  have hβ0 : 0 ≤ β := by linarith
  have hg := hasSum_geometric_of_lt_one hβ0 hβ1
  have h2 : HasSum (fun k : ℕ => (Pi.single 0 (2 : ℝ) : ℕ → ℝ) k) 2 := hasSum_pi_single 0 2
  refine ⟨?_, div_pos (by linarith) (by linarith)⟩
  have h := hg.sub h2
  have hval : (1 - β)⁻¹ - 2 = (2 * β - 1) / (1 - β) := by
    have : (1 : ℝ) - β ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at h
  refine h.congr_fun fun k => ?_
  rcases k with _ | k
  · simp [surplusTerm, perfectForesight, cbS]; norm_num
  · simp [surplusTerm, perfectForesight, cbS]

end Cochrane.LongTermDebtDynamics.TidyR5NoBuybackExistence
