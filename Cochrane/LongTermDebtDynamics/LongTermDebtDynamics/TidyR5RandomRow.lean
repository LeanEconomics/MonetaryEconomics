/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5Pathwise
import LongTermDebtDynamics.ExpectationsFiniteTree

/-!
# Theorem W with random bounds on the sale fractions

Cochrane (2023), §7.4, pp. 224–226, equations (7.14)–(7.17).

`GeneralFormula.RowBound` bounds the sale fractions by a deterministic, date-independent sequence,
`|A_t^{(t+j+1)}| ≤ a_j` with `∑_j β^{j+1} a_j ≤ ρ < 1`. This module replaces it by the row
condition state by state and date by date,
`∑_j β^{j+1} |A_t^{(t+j+1)}(ω)| ≤ ρ < 1` for every `t` and `ω` (`RowBoundR`), which is implied by
any random bounds `a_{t,j}(ω)` (adapted or not) with `∑_j β^{j+1} a_{t,j}(ω) ≤ ρ`
(`rowBoundR_of_randomBound`), and so by the deterministic row condition
(`randomBound_of_rowBound`). It is strictly weaker than the deterministic condition even under
perfect foresight (`sx_rowBoundR`, `sx_not_rowBound`).

* `unique_of_rowR`: bounded solutions of the homogeneous system vanish, for every expectation
  system.
* `exists_bounded_solution`: the flow system (7.14) has a bounded solution, for every
  expectation system, by a contraction argument (`iterY`, `opK`); with `unique_of_rowR` it is
  the unique bounded solution (`existsUnique_bounded_solution`).
* `theoremW_rowR`: **Theorem W with random bounds.** If in addition `E_t` passes through
  absolutely convergent series (`SeriesExchange`, true for perfect foresight and every finite
  event tree: `perfectForesight_seriesExchange`, `finiteTree_seriesExchange`), the bounded
  solution is the weighted present value (7.17), an absolutely convergent series.

Why `SeriesExchange` appears here: with deterministic bounds the series in (7.17) are dominated
uniformly in the state, and `ForwardSolution.E_tsum_dom` interchanges `E_t` and the sum; with
random bounds the domination is state by state only. Uniqueness and existence do not need the
interchange; only the formula does. The hypothesis is in fact a theorem of the axioms (module
TidyR5SeriesExchange, `TidyR5SeriesExchange.seriesExchange`), because `E_t` is monotone and
linear on all random variables, unbounded ones included.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5RandomRow

open Filter Topology MaturityStructure GeneralFormula TidyR5Pathwise

/-! ### The weights under a row-by-row bound -/

/-- Cochrane (2023), eq. (7.17), p. 226: if every row of (deterministic) sale fractions satisfies
`∑_{j<N} β^{j+1}|A_t^{(t+j+1)}| ≤ ρ`, the partial sums of `β^m |W_u^{(m)}|` are at most
`∑_{n<N} ρ^n`, for every start date `u`. -/
theorem sum_abs_weight_le {β ρ : ℝ} (hβ0 : 0 ≤ β) (hρ0 : 0 ≤ ρ) {A : ℕ → ℕ → ℝ}
    (hrow : ∀ t N, ∑ j ∈ Finset.range N, β ^ (j + 1) * |A t (t + (j + 1))| ≤ ρ) (N : ℕ) :
    ∀ u, ∑ m ∈ Finset.range N, β ^ m * |weight A u m| ≤ ∑ n ∈ Finset.range N, ρ ^ n := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro u
    rcases N with _ | N
    · simp
    · rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [pow_zero, weight_zero, abs_one, mul_one]
      have hk : ∀ k, β ^ (k + 1) * |weight A u (k + 1)| ≤
          ∑ j ∈ Finset.range (k + 1), β ^ (j + 1) * |A u (u + (j + 1))| *
            (β ^ (k - j) * |weight A (u + (j + 1)) (k - j)|) := by
        intro k
        rw [weight_first_step]
        refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (pow_nonneg hβ0 _)).trans (le_of_eq ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [abs_mul, show β ^ (k + 1) = β ^ (j + 1) * β ^ (k - j) by
          rw [← pow_add]; congr 1; omega]
        ring
      have hsumk := Finset.sum_le_sum fun k (_ : k ∈ Finset.range N) => hk k
      rw [← sum_triangle N (fun j m => β ^ (j + 1) * |A u (u + (j + 1))| *
        (β ^ m * |weight A (u + (j + 1)) m|))] at hsumk
      have hstep : ∑ j ∈ Finset.range N, ∑ m ∈ Finset.range (N - j),
          β ^ (j + 1) * |A u (u + (j + 1))| * (β ^ m * |weight A (u + (j + 1)) m|) ≤
          ∑ j ∈ Finset.range N, β ^ (j + 1) * |A u (u + (j + 1))| *
            ∑ n ∈ Finset.range N, ρ ^ n := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ((ih (N - j) (by omega) _).trans ?_)
          (mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _))
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N j))
          fun n _ _ => pow_nonneg hρ0 n
      rw [← Finset.sum_mul] at hstep
      have hgeo : 0 ≤ ∑ n ∈ Finset.range N, ρ ^ n := Finset.sum_nonneg fun n _ => pow_nonneg hρ0 n
      have h2 := mul_le_mul_of_nonneg_right (hrow u N) hgeo
      have h3 : ∑ i ∈ Finset.range N, ρ ^ (i + 1) = ρ * ∑ n ∈ Finset.range N, ρ ^ n := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_succ' ρ i
      rw [h3]
      linarith

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (7.17), p. 225: **the row condition with random bounds**: at every date
and state, `∑_j β^{j+1} |A_t^{(t+j+1)}(ω)| ≤ ρ` (a convergent series). -/
def RowBoundR (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (ρ : ℝ) : Prop :=
  ∀ t ω, Summable (fun j : ℕ => β ^ (j + 1) * |A t (t + (j + 1)) ω|) ∧
    ∑' j : ℕ, β ^ (j + 1) * |A t (t + (j + 1)) ω| ≤ ρ

/-- Cochrane (2023), eq. (7.17), p. 225: random bounds `|A_t^{(t+j+1)}(ω)| ≤ a_{t,j}(ω)` with
`∑_j β^{j+1} a_{t,j}(ω) ≤ ρ` at every date and state. -/
def RandomBound (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℕ → Ω → ℝ) (ρ : ℝ) : Prop :=
  (∀ t j ω, |A t (t + (j + 1)) ω| ≤ a t j ω) ∧
    ∀ t ω, Summable (fun j : ℕ => β ^ (j + 1) * a t j ω) ∧ ∑' j : ℕ, β ^ (j + 1) * a t j ω ≤ ρ

/-- Cochrane (2023), eq. (7.17), p. 225: random bounds imply the row condition `RowBoundR`. -/
theorem rowBoundR_of_randomBound {β ρ : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ}
    {a : ℕ → ℕ → Ω → ℝ} (h : RandomBound β A a ρ) : RowBoundR β A ρ := by
  intro t ω
  have hle : ∀ j : ℕ, β ^ (j + 1) * |A t (t + (j + 1)) ω| ≤ β ^ (j + 1) * a t j ω := fun j =>
    mul_le_mul_of_nonneg_left (h.1 t j ω) (pow_nonneg hβ0 _)
  have hs : Summable (fun j : ℕ => β ^ (j + 1) * |A t (t + (j + 1)) ω|) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _)) hle
      (h.2 t ω).1
  exact ⟨hs, (Summable.tsum_le_tsum hle hs (h.2 t ω).1).trans (h.2 t ω).2⟩

/-- Cochrane (2023), eq. (7.17), p. 225: the deterministic row condition
`GeneralFormula.RowBound` is the special case of constant bounds `a_{t,j}(ω) = a_j`. -/
theorem randomBound_of_rowBound {β ρ : ℝ} {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (h : RowBound β A a ρ) : RandomBound β A (fun _ j _ => a j) ρ :=
  ⟨h.2.1, fun _ _ => ⟨h.2.2.1, h.2.2.2⟩⟩

/-- Cochrane (2023), eq. (7.17), p. 225: the partial sums of each row are at most `ρ`. -/
theorem RowBoundR.partial {β ρ : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (t : ℕ) (ω : Ω) (N : ℕ) :
    ∑ j ∈ Finset.range N, β ^ (j + 1) * |A t (t + (j + 1)) ω| ≤ ρ :=
  ((h t ω).1.sum_le_tsum _ fun _ _ => mul_nonneg (pow_nonneg hβ0 _) (abs_nonneg _)).trans
    (h t ω).2

/-- Cochrane (2023), eq. (7.17), p. 225: under the row condition `ρ ≥ 0` (given any state). -/
theorem RowBoundR.nonneg {β ρ : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (ω : Ω) : 0 ≤ ρ := by
  simpa using h.partial hβ0 0 ω 0

/-- Cochrane (2023), eq. (7.17), p. 226: under the row condition with `ρ < 1`, at every state
`∑_m β^m |W_u^{(m)}(ω)|` converges, with sum at most `1/(1−ρ)`. -/
theorem weight_series_le {β ρ : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) (ω : Ω) (u : ℕ) :
    Summable (fun m => β ^ m * |weight (fun t v => A t v ω) u m|) ∧
      ∑' m, β ^ m * |weight (fun t v => A t v ω) u m| ≤ 1 / (1 - ρ) := by
  have hρ0 := h.nonneg hβ0 ω
  have hb : ∀ N, ∑ m ∈ Finset.range N, β ^ m * |weight (fun t v => A t v ω) u m| ≤
      1 / (1 - ρ) := by
    intro N
    refine (sum_abs_weight_le hβ0 hρ0 (fun t N => h.partial hβ0 t ω N) N u).trans ?_
    have hg := summable_geometric_of_lt_one hρ0 hρ1
    refine (hg.sum_le_tsum _ fun n _ => pow_nonneg hρ0 n).trans ?_
    rw [tsum_geometric_of_lt_one hρ0 hρ1, one_div]
  have hnn : ∀ m, 0 ≤ β ^ m * |weight (fun t v => A t v ω) u m| := fun m =>
    mul_nonneg (pow_nonneg hβ0 m) (abs_nonneg _)
  exact ⟨summable_of_sum_range_le hnn hb, Real.tsum_le_of_sum_range_le hnn hb⟩

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: under the row condition with random bounds
the pathwise weighted present value `Z` solves the flow system state by state, and
`|Z_t| ≤ M/(1−ρ)`. -/
theorem pathZΩ_rowR {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * (A t (t + (j + 1)) ω *
      pathZΩ β A s (t + (j + 1)) ω)) (pathZΩ β A s t ω - s t ω)) ∧
      ∀ t ω, |pathZΩ β A s t ω| ≤ M / (1 - ρ) := by
  refine ⟨fun t ω => ?_, fun t ω => ?_⟩
  · exact pathZ_solves hβ0 (fun u => hsb u ω) (fun u => (weight_series_le hβ0 hρ1 h ω u).1)
      (fun u => (weight_series_le hβ0 hρ1 h ω u).2) t (h t ω).1
  · have := (pathZ_summable_bound hβ0 (fun u => hsb u ω) (weight_series_le hβ0 hρ1 h ω t).1
      (weight_series_le hβ0 hρ1 h ω t).2).2
    rw [one_div_mul_eq_div] at this
    exact this

/-! ### Uniqueness, for every expectation system -/

/-- Cochrane (2023), eq. (7.17), p. 225: under the row condition the expected rows satisfy
`∑_{j<N} β^{j+1} E_t|A_t^{(t+j+1)}| ≤ ρ` (finite additivity of `E_t` suffices). -/
theorem E_row_partial {β ρ : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (t : ℕ) (ω : Ω) (N : ℕ) :
    ∑ j ∈ Finset.range N, β ^ (j + 1) * 𝔼.E t (fun ω' => |A t (t + (j + 1)) ω'|) ω ≤ ρ := by
  have hle : (∑ j ∈ Finset.range N, β ^ (j + 1) • fun ω' => |A t (t + (j + 1)) ω'|) ≤
      fun _ => ρ := fun ω' => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact h.partial hβ0 t ω' N
  have := 𝔼.mono t hle ω
  rw [𝔼.const, map_sum, Finset.sum_apply] at this
  simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using this

/-- Cochrane (2023), §7.4: a term of the system is bounded through the expected absolute row,
`|β^{j+1} E_t(A d)| ≤ β^{j+1} E_t|A| K` when `|d| ≤ K`. -/
theorem abs_term_le {β K : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} {d : ℕ → Ω → ℝ}
    (hK : ∀ t ω, |d t ω| ≤ K) (t j : ℕ) (ω : Ω) :
    |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω| ≤
      β ^ (j + 1) * 𝔼.E t (fun ω' => |A t (t + (j + 1)) ω'|) ω * K := by
  rw [abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((abs_E_le_E_abs 𝔼 _ _ ω).trans ?_) (pow_nonneg hβ0 _)
  have hle : (fun ω' => |(A t (t + (j + 1)) * d (t + (j + 1))) ω'|) ≤
      K • fun ω' => |A t (t + (j + 1)) ω'| := fun ω' => by
    simp only [Pi.mul_apply, abs_mul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm K]
    exact mul_le_mul_of_nonneg_left (hK _ ω') (abs_nonneg _)
  have := 𝔼.mono t hle ω
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm K] at this
  exact this

/-- Cochrane (2023), eq. (7.14), p. 225: under the row condition, for `|d| ≤ K` the series
`∑_j β^{j+1} E_t(A_t^{(t+j+1)} d_{t+j+1})` converges absolutely and its sum is at most `ρ K` in
absolute value. -/
theorem row_series {β ρ K : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    {d : ℕ → Ω → ℝ} (hK : ∀ t ω, |d t ω| ≤ K) (t : ℕ) (ω : Ω) :
    Summable (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω) ∧
      |∑' j : ℕ, β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω| ≤ ρ * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK t ω)
  set g : ℕ → ℝ := fun j => β ^ (j + 1) * 𝔼.E t (fun ω' => |A t (t + (j + 1)) ω'|) ω * K
    with hg
  have hEA : ∀ j, 0 ≤ 𝔼.E t (fun ω' => |A t (t + (j + 1)) ω'|) ω := fun j => by
    have := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ fun ω' => |A t (t + (j + 1)) ω'| from
      fun ω' => abs_nonneg _) ω
    rwa [𝔼.const] at this
  have hg0 : ∀ j, 0 ≤ g j := fun j => mul_nonneg (mul_nonneg (pow_nonneg hβ0 _) (hEA j)) hK0
  have hgN : ∀ N, ∑ j ∈ Finset.range N, g j ≤ ρ * K := fun N => by
    simp only [hg]
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (E_row_partial 𝔼 hβ0 h t ω N) hK0
  have hgs : Summable g := summable_of_sum_range_le hg0 hgN
  have hb : ∀ j, ‖β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω‖ ≤ g j :=
    fun j => by rw [Real.norm_eq_abs]; exact abs_term_le 𝔼 hβ0 hK t j ω
  have hs := Summable.of_norm_bounded hgs hb
  refine ⟨hs, ?_⟩
  have hsn : Summable (fun j : ℕ => ‖β ^ (j + 1) *
      𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  have h0 := norm_tsum_le_tsum_norm hsn
  rw [Real.norm_eq_abs] at h0
  exact h0.trans ((Summable.tsum_le_tsum hb hsn hgs).trans
    (Real.tsum_le_of_sum_range_le hg0 hgN))

/-- Cochrane (2023), §7.4, p. 225: **uniqueness under the row condition with random bounds.** If
`ρ < 1`, the only bounded solution of the homogeneous system
`d_t = ∑_j β^{j+1} E_t(A_t^{(t+j+1)} d_{t+j+1})` is zero, for every expectation system. -/
theorem unique_of_rowR {β ρ K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) {d : ℕ → Ω → ℝ}
    (hd : ∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω)
      (d t ω)) (hK : ∀ t ω, |d t ω| ≤ K) : d = 0 := by
  have hstep : ∀ n t ω, |d t ω| ≤ ρ ^ n * K := by
    intro n
    induction n with
    | zero => intro t ω; simpa using hK t ω
    | succ n ih =>
      intro t ω
      have := (row_series 𝔼 hβ0 h ih t ω).2
      rw [(hd t ω).tsum_eq] at this
      rw [pow_succ, mul_comm (ρ ^ n) ρ, mul_assoc]
      exact this
  funext t ω
  have hρ0 := h.nonneg hβ0 ω
  have hlim : Tendsto (fun n : ℕ => ρ ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const K
  have := ge_of_tendsto' hlim (fun n => hstep n t ω)
  simpa using abs_nonpos_iff.mp this

/-! ### Existence, for every expectation system -/

/-- Cochrane (2023), eq. (7.14), p. 225: the right-hand operator of the flow system,
`(K y)_t = ∑_j β^{j+1} E_t(A_t^{(t+j+1)} y_{t+j+1})`. -/
noncomputable def opK (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (y : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑' j : ℕ, β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) ω

/-- Cochrane (2023), eq. (7.14), p. 225: the iterates `y⁰ = 0`, `y^{n+1} = s + K yⁿ`. -/
noncomputable def iterY (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun t ω => s t ω + opK 𝔼 β A (iterY β A s n) t ω

/-- Cochrane (2023), eq. (7.14), p. 225: on bounded processes the operator is a difference
operator, `K y − K y' = K(y − y')`. -/
theorem opK_sub {β ρ K K' : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    {y y' : ℕ → Ω → ℝ} (hK : ∀ t ω, |y t ω| ≤ K) (hK' : ∀ t ω, |y' t ω| ≤ K') (t : ℕ)
    (ω : Ω) : opK 𝔼 β A y t ω - opK 𝔼 β A y' t ω = opK 𝔼 β A (y - y') t ω := by
  unfold opK
  rw [← ((row_series 𝔼 hβ0 h hK t ω).1.hasSum.sub (row_series 𝔼 hβ0 h hK' t ω).1.hasSum).tsum_eq]
  refine tsum_congr fun j => ?_
  simp only [Pi.sub_apply, mul_sub, map_sub]

/-- Cochrane (2023), eq. (7.14), p. 225: the iterates are bounded by `M/(1−ρ)` and successive
iterates differ by at most `M ρ^n`. -/
theorem iterY_bounds {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) (n : ℕ) :
    (∀ t ω, |iterY 𝔼 β A s n t ω| ≤ M / (1 - ρ)) ∧
      ∀ t ω, |iterY 𝔼 β A s (n + 1) t ω - iterY 𝔼 β A s n t ω| ≤ M * ρ ^ n := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hb : ∀ n t ω, |iterY 𝔼 β A s n t ω| ≤ M / (1 - ρ) := by
    intro n
    induction n with
    | zero =>
      intro t ω
      simp only [iterY, abs_zero]
      exact div_nonneg ((abs_nonneg _).trans (hsb t ω)) h1ρ.le
    | succ n ih =>
      intro t ω
      simp only [iterY]
      have h2 := (row_series 𝔼 hβ0 h ih t ω).2
      have : M + ρ * (M / (1 - ρ)) = M / (1 - ρ) := by field_simp; ring
      refine (abs_add_le _ _).trans ?_
      rw [← this]
      exact add_le_add (hsb t ω) h2
  refine ⟨hb n, ?_⟩
  induction n with
  | zero =>
    intro t ω
    have h0 : opK 𝔼 β A (fun _ _ => 0) t ω = 0 := by
      unfold opK
      have : (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) *
          (fun _ _ => (0 : ℝ)) (t + (j + 1))) ω) = fun _ => 0 := by
        funext j
        rw [show (A t (t + (j + 1)) * (fun _ _ => (0 : ℝ)) (t + (j + 1))) = 0 from
          funext fun _ => mul_zero _, map_zero]
        simp
      rw [this, tsum_zero]
    simp only [iterY, h0, add_zero, sub_zero, pow_zero, mul_one]
    exact hsb t ω
  | succ n ih =>
    intro t ω
    have hd : iterY 𝔼 β A s (n + 1 + 1) t ω - iterY 𝔼 β A s (n + 1) t ω =
        opK 𝔼 β A (iterY 𝔼 β A s (n + 1) - iterY 𝔼 β A s n) t ω := by
      rw [← opK_sub 𝔼 hβ0 h (hb (n + 1)) (hb n)]
      simp only [iterY]
      ring
    rw [hd]
    have h2 := (row_series 𝔼 hβ0 h (d := iterY 𝔼 β A s (n + 1) - iterY 𝔼 β A s n)
      (fun t ω => by simpa only [Pi.sub_apply] using ih t ω) t ω).2
    refine h2.trans (le_of_eq ?_)
    ring

/-- Cochrane (2023), eq. (7.14), p. 225: **existence under the row condition with random
bounds**, for every expectation system: the flow system (7.14) has a solution with
`|y_t| ≤ M/(1−ρ)` (the limit of the iterates `iterY`). -/
theorem exists_bounded_solution {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    (h : RowBoundR β A ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) :
    ∃ y : ℕ → Ω → ℝ, (∀ t, GeneralFormula.MaturingSystem 𝔼 β A y s t) ∧
      ∀ t ω, |y t ω| ≤ M / (1 - ρ) := by
  have hbd := fun n => iterY_bounds 𝔼 hβ0 hρ1 h hsb n
  have hcau : ∀ t ω, CauchySeq (fun n => iterY 𝔼 β A s n t ω) := fun t ω =>
    cauchySeq_of_le_geometric ρ M hρ1 fun n => by
      rw [Real.dist_eq, abs_sub_comm]; exact (hbd n).2 t ω
  set y : ℕ → Ω → ℝ := fun t ω => limUnder atTop (fun n => iterY 𝔼 β A s n t ω) with hy
  have hlim : ∀ t ω, Tendsto (fun n => iterY 𝔼 β A s n t ω) atTop (𝓝 (y t ω)) :=
    fun t ω => (hcau t ω).tendsto_limUnder
  have hyb : ∀ t ω, |y t ω| ≤ M / (1 - ρ) := fun t ω =>
    le_of_tendsto' (hlim t ω).abs fun n => (hbd n).1 t ω
  have hdist : ∀ n t ω, |iterY 𝔼 β A s n t ω - y t ω| ≤ M * ρ ^ n / (1 - ρ) := fun n t ω => by
    rw [← Real.dist_eq]
    exact dist_le_of_le_geometric_of_tendsto ρ M hρ1 (fun n => by
      rw [Real.dist_eq, abs_sub_comm]; exact (hbd n).2 t ω) (hlim t ω) n
  have hfix : ∀ t ω, y t ω = s t ω + opK 𝔼 β A y t ω := by
    intro t ω
    have hρ0 := h.nonneg hβ0 ω
    have h1 : Tendsto (fun n => iterY 𝔼 β A s (n + 1) t ω) atTop (𝓝 (y t ω)) :=
      (hlim t ω).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => iterY 𝔼 β A s (n + 1) t ω) atTop
        (𝓝 (s t ω + opK 𝔼 β A y t ω)) := by
      have hc : Tendsto (fun n : ℕ => ρ * (M * ρ ^ n / (1 - ρ))) atTop (𝓝 0) := by
        have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul M).div_const (1 - ρ)
        simpa using this.const_mul ρ
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hc
      simp only [iterY, Real.norm_eq_abs]
      rw [show s t ω + opK 𝔼 β A (iterY 𝔼 β A s n) t ω - (s t ω + opK 𝔼 β A y t ω) =
        opK 𝔼 β A (iterY 𝔼 β A s n) t ω - opK 𝔼 β A y t ω by ring,
        opK_sub 𝔼 hβ0 h ((hbd n).1) hyb]
      exact (row_series 𝔼 hβ0 h (d := iterY 𝔼 β A s n - y)
        (fun t ω => by simpa only [Pi.sub_apply] using hdist n t ω) t ω).2
    exact tendsto_nhds_unique h1 h2
  refine ⟨y, fun t ω => ?_, hyb⟩
  have := (row_series 𝔼 hβ0 h hyb t ω).1.hasSum
  convert this using 1
  rw [hfix t ω, opK]
  ring

/-- Cochrane (2023), §7.4, p. 225: **existence and uniqueness under the row condition with random
bounds**, for every expectation system: the flow system (7.14) has exactly one bounded
solution. -/
theorem existsUnique_bounded_solution {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) :
    ∃! y : ℕ → Ω → ℝ, (∀ t, GeneralFormula.MaturingSystem 𝔼 β A y s t) ∧
      ∃ K, ∀ t ω, |y t ω| ≤ K := by
  obtain ⟨y, hy, hyb⟩ := exists_bounded_solution 𝔼 hβ0 hρ1 h hsb
  refine ⟨y, ⟨hy, _, hyb⟩, ?_⟩
  rintro y' ⟨hy', K, hK⟩
  have := unique_of_rowR 𝔼 hβ0 hρ1 h (homogeneous_of_two 𝔼 hy' hy)
    (K := K + M / (1 - ρ)) (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hK t ω) (hyb t ω)))
  exact sub_eq_zero.mp this

/-! ### Theorem W with random bounds -/

/-- Cochrane (2023), eq. (7.17), p. 225: `E_t` passes through absolutely convergent series of
random variables (a theorem of the axioms: `TidyR5SeriesExchange.seriesExchange`). -/
def SeriesExchange : Prop :=
  ∀ f : ℕ → Ω → ℝ, (∀ ω, Summable (fun n => |f n ω|)) → ∀ t ω,
    HasSum (fun n => 𝔼.E t (f n) ω) (𝔼.E t (fun ω' => ∑' n, f n ω') ω)

/-- Cochrane (2023), eq. (7.17): perfect foresight passes through absolutely convergent series. -/
theorem perfectForesight_seriesExchange : SeriesExchange perfectForesight := by
  intro f hf t ω
  exact ((hf ω).of_abs).hasSum

/-- Cochrane (2023), eq. (7.17): every finite event tree passes through absolutely convergent
series (a conditional expectation is a finite weighted sum). -/
theorem finiteTree_seriesExchange {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : SeriesExchange T.toExpectationSystem := by
  classical
  intro f hf t ω
  simp only [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num]
  refine HasSum.div_const ?_ _
  refine hasSum_sum fun ω' _ => ?_
  by_cases hω : T.info t ω' ω
  · simp only [hω, ↓reduceIte]
    exact ((hf ω').of_abs).hasSum.mul_left _
  · simp only [hω, ↓reduceIte]
    exact hasSum_zero

/-- Cochrane (2023), eqs. (7.14), (7.17), pp. 225–226: under the row condition with random
bounds, if `E_t` passes through absolutely convergent series, (7.17) converges absolutely,
`|y_t| ≤ M/(1−ρ)`, it is known at `t`, and it solves the flow system (7.14). -/
theorem formulaW_solves_rowR (hpo : 𝔼.PullOut) (hex : SeriesExchange 𝔼) {β ρ M : ℝ}
    (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) :
    (∀ t, MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t) ∧
      (∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (formulaW 𝔼 β A s t ω)) ∧
      (∀ t ω, |formulaW 𝔼 β A s t ω| ≤ M / (1 - ρ)) ∧
      ∀ t, 𝔼.E t (formulaW 𝔼 β A s t) = formulaW 𝔼 β A s t := by
  obtain ⟨hpw, hZb⟩ := pathZΩ_rowR hβ0 hρ1 h hsb
  have hex1 : ∀ t ω, HasSum (fun m => formulaTerm 𝔼 β A s t m ω)
      (𝔼.E t (pathZΩ β A s t) ω) := by
    intro t ω
    have habs : ∀ ω', Summable (fun m => |β ^ m * (weight A t m ω' * s (t + m) ω')|) := by
      intro ω'
      have := (pathZ_summable_bound hβ0 (fun u => hsb u ω') (weight_series_le hβ0 hρ1 h ω' t).1
        (weight_series_le hβ0 hρ1 h ω' t).2).1
      simpa only [weight_apply] using this
    have hh := hex (fun m ω' => β ^ m * (weight A t m ω' * s (t + m) ω')) habs t ω
    have hZ : (fun ω' => ∑' m, β ^ m * (weight A t m ω' * s (t + m) ω')) = pathZΩ β A s t := by
      funext ω'
      simp only [pathZΩ, pathZ, weight_apply]
    rw [hZ] at hh
    refine hh.congr_fun fun m => ?_
    rw [formulaTerm, show (fun ω' => β ^ m * (weight A t m ω' * s (t + m) ω')) =
      β ^ m • (weight A t m * s (t + m)) from rfl, map_smul]
    rfl
  have hex2 : ∀ t ω, HasSum (fun j : ℕ => 𝔼.E t (fun ω' => β ^ (j + 1) *
      (A t (t + (j + 1)) ω' * pathZΩ β A s (t + (j + 1)) ω')) ω)
      (𝔼.E t (fun ω' => ∑' j : ℕ, β ^ (j + 1) *
        (A t (t + (j + 1)) ω' * pathZΩ β A s (t + (j + 1)) ω')) ω) := by
    intro t ω
    refine hex _ (fun ω' => ?_) t ω
    refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_)
      ((h t ω').1.mul_right (M / (1 - ρ)))
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hZb _ ω') (abs_nonneg _))
      (pow_nonneg hβ0 _)
  have hfw := formulaW_eq_E 𝔼 hex1
  refine ⟨formulaW_solves_of_exchange 𝔼 hpo hA hs hpw hex1 hex2, fun t ω => ?_,
    fun t ω => ?_, formulaW_adapted_of_exchange 𝔼 hex1⟩
  · rw [hfw t]; exact hex1 t ω
  · rw [hfw t]; exact 𝔼.abs_E_le (hZb t) t ω

/-- Cochrane (2023), eq. (7.17), p. 225: **Theorem W with random bounds.** Under the row condition
with random bounds (`ρ < 1`), with each `A_t^{(t+j+1)}` known at `t + j`, bounded adapted
surpluses and an expectation system that passes through absolutely convergent series, every
bounded solution of the flow conditions (7.14) is the weighted present value (7.17),
`y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}`, an absolutely convergent series. -/
theorem theoremW_rowR (hpo : 𝔼.PullOut) (hex : SeriesExchange 𝔼) {β ρ M K : ℝ}
    (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s y : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hyb : ∀ t ω, |y t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (y t ω) := by
  obtain ⟨hz, hsum, hzb, -⟩ := formulaW_solves_rowR 𝔼 hpo hex hβ0 hρ1 h hA hs hsb
  have hd := unique_of_rowR 𝔼 hβ0 hρ1 h (homogeneous_of_two 𝔼 hy hz)
    (K := K + M / (1 - ρ)) (fun u ω' => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hyb u ω') (hzb u ω')))
  have hyz : y t ω = formulaW 𝔼 β A s t ω := by
    have := congrFun (congrFun hd t) ω
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    linarith
  rw [hyz]
  exact hsum t ω

/-- Cochrane (2023), §7.4, p. 225: **the price level is determined under the row condition with
random bounds**: two adapted price paths satisfying every flow condition (7.1) with bounded real
values of maturing debt coincide, for every expectation system with the pull-out property. -/
theorem price_unique_rowR (hpo : 𝔼.PullOut) {β ρ K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x x' s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) (h : RowBoundR β (fracSold D) ρ)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D x' s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (hb' : ∀ t ω, |D t t ω * x' t ω| ≤ K) : x = x' := by
  have hy := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow t)
  have hy' := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow' t)
  have hzero := unique_of_rowR 𝔼 hβ0 hρ1 h (homogeneous_of_two 𝔼 hy hy') (K := K + K)
    (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hb t ω) (hb' t ω)))
  funext t ω
  have := congrFun (congrFun hzero t) ω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact mul_left_cancel₀ (hDmm t ω) this

/-- Cochrane (2023), eq. (7.17), p. 225: **(7.17) for the price level with random bounds.** In an
equilibrium with bounded real maturing debt, under the row condition with random bounds, with
each sale fraction known at the last sale date and an expectation system passing through
absolutely convergent series, `B_{t−1}^{(t)}/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}`. -/
theorem price_formula_rowR (hpo : 𝔼.PullOut) (hex : SeriesExchange 𝔼) {β ρ M K : ℝ}
    (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (hDmm : ∀ m ω, D m m ω ≠ 0) (h : RowBoundR β (fracSold D) ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (fracSold D t (t + (j + 1))) = fracSold D t (t + (j + 1)))
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β (fracSold D) s t m ω) (D t t ω * x t ω) :=
  theoremW_rowR 𝔼 hpo hex hβ0 hρ1 h hA hs hsb
    (fun u => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm u).mp (hflow u)) hb t ω

/-! ### The random row condition is strictly weaker than the deterministic one -/

/-- Cochrane (2023), §7.4 (illustration): sale fractions whose row `t` has a single entry
`ρ/β^{t+1}` at lag `t` (maturity `2t + 1`), perfect foresight. -/
noncomputable def sxA (β ρ : ℝ) : ℕ → ℕ → Unit → ℝ :=
  fun t m _ => if m = 2 * t + 1 then ρ / β ^ (t + 1) else 0

/-- Cochrane (2023), §7.4: each row of `sxA` sums to exactly `ρ`, so `sxA` satisfies the row
condition with (time-varying) bounds. -/
theorem sx_rowBoundR {β ρ : ℝ} (hβ0 : 0 < β) (hρ0 : 0 ≤ ρ) : RowBoundR β (sxA β ρ) ρ := by
  intro t u
  have hfun : (fun j : ℕ => β ^ (j + 1) * |sxA β ρ t (t + (j + 1)) u|) =
      Pi.single t ρ := by
    funext j
    by_cases hj : j = t
    · subst hj
      simp only [sxA, show j + (j + 1) = 2 * j + 1 by omega, ↓reduceIte, Pi.single_eq_same]
      rw [abs_of_nonneg (div_nonneg hρ0 (pow_nonneg hβ0.le _))]
      field_simp
    · simp only [sxA, show ¬ (t + (j + 1) = 2 * t + 1) by omega, ↓reduceIte, abs_zero, mul_zero]
      rw [Pi.single_eq_of_ne hj]
  rw [hfun]
  exact ⟨(hasSum_pi_single t ρ).summable, le_of_eq (hasSum_pi_single t ρ).tsum_eq⟩

/-- Cochrane (2023), §7.4: **the deterministic row condition fails for `sxA`** (`ρ > 0`): any
date-independent bound has `β^{j+1} a_j ≥ ρ` for every `j`, so `∑_j β^{j+1} a_j` diverges. -/
theorem sx_not_rowBound {β ρ : ℝ} (hβ0 : 0 < β) (hρ : 0 < ρ) :
    ¬ ∃ a ρ', RowBound β (sxA β ρ) a ρ' := by
  rintro ⟨a, ρ', hrow⟩
  have hge : ∀ j, ρ ≤ β ^ (j + 1) * a j := by
    intro j
    have := hrow.2.1 j j ()
    simp only [sxA, show j + (j + 1) = 2 * j + 1 by omega, ↓reduceIte] at this
    rw [abs_of_nonneg (div_nonneg hρ.le (pow_nonneg hβ0.le _)),
      div_le_iff₀ (pow_pos hβ0 _)] at this
    linarith
  have hlim := hrow.2.2.1.tendsto_atTop_zero
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hρ)).exists
  exact absurd (hge j) (not_le.mpr hj)

end Cochrane.LongTermDebtDynamics.TidyR5RandomRow
