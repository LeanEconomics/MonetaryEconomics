/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5SeriesExchange
import LongTermDebtDynamics.PolicyConstraints

/-!
# The innovation form of (7.12) at every date

Cochrane (2023), §7.3.2, p. 224 (the unnumbered innovation version of (7.12)), and §7.4,
eq. (7.17), p. 225.

`BondSales.dilution_formula` is (7.12) at date 0 and `BondSales.offset_shock` states its content at
date 0. Here (7.12) and its innovation form hold at every date `t`.

* `dilution_at`: **(7.12) at date `t₀`.** If the government trades at `t₀` (state-contingently)
  and never after,
  `B_{t₀−1}^{(t₀)}/P_{t₀} = s_{t₀} + ∑_{j≥1} β^j A_{t₀}^{(t₀+j)} E_{t₀} s_{t₀+j}` with
  `A_{t₀}^{(m)} = (B_{t₀}^{(m)} − B_{t₀−1}^{(m)})/B_{t₀}^{(m)}` (`fracNew`).
* `innovation_at`: **the innovation form at date `t + 1`**:
  `B_t^{(t+1)} (1/P_{t+1} − E_t(1/P_{t+1})) = ΔE_{t+1} s_{t+1} +
  ∑_j β^{j+1} [A E_{t+1} s_{t+1+j+1} − E_t(A s_{t+1+j+1})]`, a convergent series. The printed
  display
  mixes the dates `0` and `t` (E7.9); this is its corrected form at a general date.
* `no_surprise_iff`: there is no unexpected inflation at `t + 1` exactly when the surplus news is
  offset by the news in the dilution terms (the state-contingent sales).
* `innovation_rowR`: the innovation form of the general formula (7.17) at every date, for any
  sale policy under the row condition with random bounds:
  `y_{t+1} − E_t y_{t+1} = ∑_m β^m (E_{t+1} − E_t)(W_{t+1}^{(m)} s_{t+1+m})`.

The interchanges of `E_t` and the series use `TidyR5SeriesExchange.seriesExchange`.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5InnovationForm

open Filter Topology MaturityStructure GeneralFormula TidyR5Pathwise TidyR5RandomRow
  TidyR5SeriesExchange

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.3.2, p. 224: the government trades at date `t₀` and never after:
`B_u^{(m)} = B_{u−1}^{(m)}` for `t₀ < u < m`. -/
def NoSalesAfter (D : ℕ → ℕ → Ω → ℝ) (t₀ : ℕ) : Prop :=
  ∀ u m, t₀ < u → u < m → D (u + 1) m = D u m

/-- Cochrane (2023), eq. (7.12), p. 222 (at date `t₀`): the fraction of the date-`m` debt sold at
`t₀`, `A_{t₀}^{(m)} = (B_{t₀}^{(m)} − B_{t₀−1}^{(m)})/B_{t₀}^{(m)}`. -/
noncomputable def fracNew (D : ℕ → ℕ → Ω → ℝ) (t₀ m : ℕ) : Ω → ℝ :=
  (D (t₀ + 1) m - D t₀ m) / D (t₀ + 1) m

/-- Cochrane (2023), §7.3, p. 221 (at date `t₀`): after `t₀` the debt due at `m` is
`B_{t₀}^{(m)}`. -/
theorem debt_after {D : ℕ → ℕ → Ω → ℝ} {t₀ : ℕ} (h : NoSalesAfter D t₀) (m : ℕ) :
    ∀ k, t₀ + 1 + k ≤ m → D (t₀ + 1 + k) m = D (t₀ + 1) m := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [show t₀ + 1 + (k + 1) = t₀ + 1 + k + 1 by omega, h _ m (by omega) (by omega),
      ih (by omega)]

/-- Cochrane (2023), eq. (7.9), p. 221 (after date `t₀`): with no trading after `t₀`, each later
surplus pays off the debt maturing at its date, `B_{t₀}^{(u)}/P_u = s_u` for `u > t₀`. -/
theorem maturing_after {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} {t₀ : ℕ}
    (h : NoSalesAfter D t₀) {u : ℕ} (hu : t₀ < u) (hflow : RealFlow 𝔼 β D x s u) :
    D (t₀ + 1) u * x u = s u := by
  funext ω
  have hz : (fun j : ℕ => β ^ (j + 1) * (sales D u (u + (j + 1)) ω *
      𝔼.E u (x (u + (j + 1))) ω)) = fun _ => 0 := by
    funext j
    simp [sales, h u (u + (j + 1)) hu (by omega)]
  have h1 := hflow ω
  rw [hz] at h1
  have h2 := h1.unique hasSum_zero
  have hD : D u u = D (t₀ + 1) u := by
    have := debt_after h u (u - (t₀ + 1)) (by omega)
    rwa [show t₀ + 1 + (u - (t₀ + 1)) = u by omega] at this
  simp only [Pi.mul_apply]
  rw [← hD]
  linarith

/-- Cochrane (2023), eq. (7.12), p. 222, **at date `t₀`**: with trading at `t₀` only,
`B_{t₀−1}^{(t₀)}/P_{t₀} = s_{t₀} + ∑_{j≥0} β^{j+1} A_{t₀}^{(t₀+j+1)} E_{t₀} s_{t₀+j+1}`. -/
theorem dilution_at (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} {t₀ : ℕ} (hD : Predetermined 𝔼 D)
    (h : NoSalesAfter D t₀) (hflow : ∀ u, t₀ ≤ u → RealFlow 𝔼 β D x s u)
    (hD1 : ∀ m ω, t₀ < m → D (t₀ + 1) m ω ≠ 0) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * (fracNew D t₀ (t₀ + (j + 1)) ω *
      𝔼.E t₀ (s (t₀ + (j + 1))) ω)) (D t₀ t₀ ω * x t₀ ω - s t₀ ω) := by
  refine (hflow t₀ le_rfl ω).congr_fun fun j => ?_
  set m := t₀ + (j + 1) with hm
  have hx : x m = s m / D (t₀ + 1) m := by
    funext ω'
    have := congrFun (maturing_after 𝔼 h (show t₀ < m by omega) (hflow m (by omega))) ω'
    simp only [Pi.mul_apply] at this
    simp only [Pi.div_apply]
    rw [eq_div_iff (hD1 m ω' (by omega)), ← this, mul_comm]
  rw [hx, PolicyConstraints.E_div_known 𝔼 hpo hdc (hD.2 t₀ m)]
  simp only [sales, fracNew, Pi.sub_apply, Pi.div_apply]
  ring

/-- Cochrane (2023), §7.3.2, p. 224: the sale fractions `A_{t+1}^{(m)}` are known at `t + 1`. -/
theorem fracNew_known (hdc : PolicyConstraints.DivClosed 𝔼) {D : ℕ → ℕ → Ω → ℝ}
    (hD : Predetermined 𝔼 D) (t₀ m : ℕ) : 𝔼.E t₀ (fracNew D t₀ m) = fracNew D t₀ m :=
  hdc t₀ _ _ (by rw [map_sub, hD.2 t₀ m, Predetermined.known 𝔼 hD le_rfl]) (hD.2 t₀ m)

/-- Cochrane (2023), §7.3.2, p. 224, **the innovation form of (7.12) at date `t + 1`** (corrected,
E7.9): with trading at `t + 1` only and an absolutely convergent dilution series,
`B_t^{(t+1)} (1/P_{t+1} − E_t(1/P_{t+1})) − (s_{t+1} − E_t s_{t+1}) =
∑_j β^{j+1} [A_{t+1}^{(m)} E_{t+1} s_m − E_t(A_{t+1}^{(m)} s_m)]` with `m = t + 1 + j + 1`. -/
theorem innovation_at (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} {t : ℕ} (hD : Predetermined 𝔼 D)
    (h : NoSalesAfter D (t + 1)) (hflow : ∀ u, t + 1 ≤ u → RealFlow 𝔼 β D x s u)
    (hD1 : ∀ m ω, t + 1 < m → D (t + 2) m ω ≠ 0)
    (habs : ∀ ω, Summable (fun j : ℕ => |β ^ (j + 1) * (fracNew D (t + 1) (t + 1 + (j + 1)) ω *
      𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω)|)) (ω : Ω) :
    HasSum (fun j : ℕ => β ^ (j + 1) * (fracNew D (t + 1) (t + 1 + (j + 1)) ω *
        𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω -
        𝔼.E t (fracNew D (t + 1) (t + 1 + (j + 1)) * s (t + 1 + (j + 1))) ω))
      (D (t + 1) (t + 1) ω * (x (t + 1) ω - 𝔼.E t (x (t + 1)) ω) -
        (s (t + 1) ω - 𝔼.E t (s (t + 1)) ω)) := by
  set g : ℕ → Ω → ℝ := fun j ω' => β ^ (j + 1) * (fracNew D (t + 1) (t + 1 + (j + 1)) ω' *
    𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω') with hg
  have hlev : ∀ ω', HasSum (fun j => g j ω')
      (D (t + 1) (t + 1) ω' * x (t + 1) ω' - s (t + 1) ω') := fun ω' =>
    dilution_at 𝔼 hpo hdc hD h hflow hD1 ω'
  have hex := seriesExchange 𝔼 g habs t ω
  have hsum : (fun ω' => ∑' j, g j ω') = D (t + 1) (t + 1) * x (t + 1) - s (t + 1) := by
    funext ω'; exact (hlev ω').tsum_eq
  rw [hsum, map_sub, hpo t _ _ (hD.2 t (t + 1))] at hex
  have hEg : ∀ j, 𝔼.E t (g j) ω = β ^ (j + 1) *
      𝔼.E t (fracNew D (t + 1) (t + 1 + (j + 1)) * s (t + 1 + (j + 1))) ω := by
    intro j
    have hk := fracNew_known 𝔼 hdc hD (t + 1) (t + 1 + (j + 1))
    rw [show g j = β ^ (j + 1) • (fracNew D (t + 1) (t + 1 + (j + 1)) *
      𝔼.E (t + 1) (s (t + 1 + (j + 1)))) from rfl, map_smul, ← hpo _ _ _ hk,
      𝔼.tower (Nat.le_succ t)]
    rfl
  have hd := (hlev ω).sub hex
  simp only [hEg] at hd
  convert hd using 1
  · funext j; simp only [hg]; ring
  · simp only [Pi.mul_apply, Pi.sub_apply]; ring

/-- Cochrane (2023), §7.3.2, p. 224 (bullet), at every date: **no unexpected inflation at
`t + 1` exactly when the surplus news is offset by the news in the dilution terms**: with
`B_t^{(t+1)} ≠ 0`, `1/P_{t+1} = E_t(1/P_{t+1})` iff
`s_{t+1} − E_t s_{t+1} + ∑_j β^{j+1}[A E_{t+1} s_m − E_t(A s_m)] = 0`. -/
theorem no_surprise_iff (hpo : 𝔼.PullOut) (hdc : PolicyConstraints.DivClosed 𝔼) {β : ℝ}
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} {t : ℕ} (hD : Predetermined 𝔼 D)
    (h : NoSalesAfter D (t + 1)) (hflow : ∀ u, t + 1 ≤ u → RealFlow 𝔼 β D x s u)
    (hD1 : ∀ m ω, t + 1 < m → D (t + 2) m ω ≠ 0)
    (habs : ∀ ω, Summable (fun j : ℕ => |β ^ (j + 1) * (fracNew D (t + 1) (t + 1 + (j + 1)) ω *
      𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω)|)) (ω : Ω) (hDt : D (t + 1) (t + 1) ω ≠ 0) :
    x (t + 1) ω = 𝔼.E t (x (t + 1)) ω ↔
      s (t + 1) ω - 𝔼.E t (s (t + 1)) ω + ∑' j : ℕ, β ^ (j + 1) *
        (fracNew D (t + 1) (t + 1 + (j + 1)) ω * 𝔼.E (t + 1) (s (t + 1 + (j + 1))) ω -
          𝔼.E t (fracNew D (t + 1) (t + 1 + (j + 1)) * s (t + 1 + (j + 1))) ω) = 0 := by
  rw [(innovation_at 𝔼 hpo hdc hD h hflow hD1 habs ω).tsum_eq]
  constructor
  · intro hx; rw [hx]; ring
  · intro h0
    have : D (t + 1) (t + 1) ω * (x (t + 1) ω - 𝔼.E t (x (t + 1)) ω) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hDt
    · linarith

/-- Cochrane (2023), eq. (7.17), p. 225, **innovation form at every date for any sale policy**:
under the row condition with random bounds, for every bounded solution `y` of the flow system
(7.14), `y_{t+1} − E_t y_{t+1} = ∑_m β^m (E_{t+1}(W_{t+1}^{(m)} s_{t+1+m}) −
E_t(W_{t+1}^{(m)} s_{t+1+m}))`, a convergent series. -/
theorem innovation_rowR (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} (h : RowBoundR β A ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s y : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hyb : ∀ t ω, |y t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => β ^ m * (𝔼.E (t + 1) (weight A (t + 1) m * s (t + 1 + m)) ω -
        𝔼.E t (weight A (t + 1) m * s (t + 1 + m)) ω))
      (y (t + 1) ω - 𝔼.E t (y (t + 1)) ω) := by
  have hlev := fun ω' => theoremW_rowR' 𝔼 hpo hβ0 hρ1 h hA hs hsb hy hyb (t + 1) ω'
  -- absolute summability of the terms of (7.17) at each state
  have habs : ∀ ω', Summable (fun m => |formulaTerm 𝔼 β A s (t + 1) m ω'|) := by
    intro ω'
    have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0 ω')
    set g : ℕ → ℝ := fun m => β ^ m * 𝔼.E (t + 1) (fun ω'' => |weight A (t + 1) m ω''|) ω' * M
      with hgdef
    have hEnn : ∀ m, 0 ≤ 𝔼.E (t + 1) (fun ω'' => |weight A (t + 1) m ω''|) ω' := fun m => by
      have := 𝔼.mono (t + 1) (show (fun _ => (0 : ℝ)) ≤ fun ω'' => |weight A (t + 1) m ω''| from
        fun _ => abs_nonneg _) ω'
      rwa [𝔼.const] at this
    have hg0 : ∀ m, 0 ≤ g m := fun m => mul_nonneg (mul_nonneg (pow_nonneg hβ0 m) (hEnn m)) hM
    have hgN : ∀ N, ∑ m ∈ Finset.range N, g m ≤ 1 / (1 - ρ) * M := by
      intro N
      simp only [hgdef]
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hM
      have hle : (∑ m ∈ Finset.range N, β ^ m • fun ω'' => |weight A (t + 1) m ω''|) ≤
          fun _ => 1 / (1 - ρ) := fun ω'' => by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        have hw := weight_series_le hβ0 hρ1 h ω'' (t + 1)
        simp only [← weight_apply] at hw
        exact (hw.1.sum_le_tsum _ fun m _ => mul_nonneg (pow_nonneg hβ0 m)
          (abs_nonneg _)).trans hw.2
      have := 𝔼.mono (t + 1) hle ω'
      rw [𝔼.const, map_sum, Finset.sum_apply] at this
      simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using this
    refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => ?_)
      (summable_of_sum_range_le hg0 hgN)
    rw [formulaTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
    change _ ≤ β ^ m * 𝔼.E (t + 1) (fun ω'' => |weight A (t + 1) m ω''|) ω' * M
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ((abs_E_le_E_abs 𝔼 _ _ ω').trans ?_) (pow_nonneg hβ0 m)
    have hle : (fun ω'' => |(weight A (t + 1) m * s (t + 1 + m)) ω''|) ≤
        M • fun ω'' => |weight A (t + 1) m ω''| := fun ω'' => by
      simp only [Pi.mul_apply, abs_mul, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (hsb _ ω'') (abs_nonneg _)
    have := 𝔼.mono (t + 1) hle ω'
    rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm M] at this
    exact this
  have hex := seriesExchange 𝔼 (fun m ω' => formulaTerm 𝔼 β A s (t + 1) m ω') habs t ω
  have hsum : (fun ω' => ∑' m, formulaTerm 𝔼 β A s (t + 1) m ω') = y (t + 1) := by
    funext ω'; exact (hlev ω').tsum_eq
  rw [hsum] at hex
  have hEt : ∀ m, 𝔼.E t (fun ω' => formulaTerm 𝔼 β A s (t + 1) m ω') ω =
      β ^ m * 𝔼.E t (weight A (t + 1) m * s (t + 1 + m)) ω := by
    intro m
    rw [show (fun ω' => formulaTerm 𝔼 β A s (t + 1) m ω') =
      β ^ m • 𝔼.E (t + 1) (weight A (t + 1) m * s (t + 1 + m)) from rfl, map_smul,
      𝔼.tower (Nat.le_succ t)]
    rfl
  simp only [hEt] at hex
  refine ((hlev ω).sub hex).congr_fun fun m => ?_
  simp only [formulaTerm]
  ring

end Cochrane.LongTermDebtDynamics.TidyR5InnovationForm
