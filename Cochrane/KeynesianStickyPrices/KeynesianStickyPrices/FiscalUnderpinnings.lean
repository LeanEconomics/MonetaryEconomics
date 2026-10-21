/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.FullModel

/-!
# The fiscal underpinnings of new-Keynesian models

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4.2 "The fiscal
underpinnings of new-Keynesian models", eq. (17.19), pp. 411–415, with Figure 17.7.

## The unexpected-inflation identity (17.19)

With one-period debt the linearised flow condition is
`ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (`Flow`). For an arbitrary expectation system,
`innov t y = E_{t+1} y − E_t y` is the innovation `ΔE_{t+1}`. The finite-horizon identity
`innov_finite` is exact; under the transversality condition and summability it gives
(`eq_17_19`)

  `ΔE_{t+1} π_{t+1} = −∑_{j≥0} ρʲ ΔE_{t+1} s̃_{t+1+j} + ∑_{j≥0} ρʲ ΔE_{t+1} r_{t+1+j}`,

where `r_{t+1+j} = i_{t+j} − E_{t+j} π_{t+1+j}` is the (ex-ante) real rate **earned between
`t + j` and `t + 1 + j`**. With the dating of (17.16), `r_t = i_t − E_t π_{t+1}`, the real-rate
term carries an extra factor `ρ` (`eq_17_19_own_dating`); the printed sum is then right iff
`ρ = 1` or there is no real-rate news (`printed_own_dating_iff`). With the text's ex-post
`r_{t+1} = i_t − π_{t+1}` the `j = 0` term would be `−ΔE_{t+1} π_{t+1}` itself
(`expost_first_term`), so that reading is wrong. For bounded processes and `0 ≤ ρ < 1` the
innovation passes through the sums (`eq_17_19_bounded`), which is the printed form `ΔE Σ`.

Consequences (p. 411): "for higher interest rates to lower inflation, there must be a fiscal
contraction" (`fiscal_contraction`); at a 100% debt-to-GDP ratio surpluses must rise one
percentage point of GDP per point of unexpected disinflation (`surplus_gdp`).

## Figure 17.7 and the reverse-engineered disturbances (pp. 412–414)

Under perfect foresight after the shock, an interest-rate path `i` can be produced by a whole
family of disturbances `u = i − φ π` (`reverse_engineer`): one for every initial inflation. For
the AR(1) path `i_n = ηⁿ` the equilibrium is `π_n = c ηⁿ + (π₁ − c) μⁿ` with
`c = σκ/(−βη² + (1 + β + σκ)η − 1)`, `μ = 1/λ₁` (`piAR_eq_path`), and the surpluses required by
(17.19) with `ρ = 1` are `Σs = −π₁ + ∑_n (i_n − π_{n+1})` (`sigmaS_closed`). At the book's
parameters (`η = 0.6`, `σ = 1`, `κ = 0.25`, `β = 0.95`, `φ = 1.2`) this gives exactly the printed
3.55, 2.23, 0.91, −0.41, and 2.55 from real rates (`fig17_7_values`, `fig17_7_real_rates`); the
reverse-engineered disturbances are not AR(1) (`fig17_7_u_not_ar1`). Survey error E10 (p. 414):
`5 × 2.23 = 11.15`, not 11.5 (`e10`).

## Figure 17.6: `Δs` for equilibria A–E (p. 410)

With (17.19) and `ρ < 1`, after an unexpected permanent rise the equilibrium with initial
inflation `p` needs `Δs(p) = −p + ∑ ρʲ(1 − π_{j+1}) = (1 − p)/(λ₁ − ρ) − p` (`deltaS`,
`deltaS_closed`), the percentage change in steady-state surpluses (`permanent_surplus_pct`):
B has `Δs = −1` for all parameters (`deltaS_B`), D has `Δs = 1/(λ₁ − ρ)` (`deltaS_D`), C is
`p = 1/(1 + λ₁ − ρ)` (`deltaS_zero_iff`). The book does not state the parameters of Fig. 17.6,
so the printed numbers cannot be recomputed; but the affine form alone shows that, given the
printed D and `δ = 0` values, A and E cannot be the jumps `δ₁ = ±1%` (`fig17_6_inconsistent`);
they correspond to jumps of about `+0.83` and `−0.87` (`fig17_6_implied_jumps`).
-/

namespace Cochrane.KeynesianStickyPrices.FiscalUnderpinnings

open Filter Topology FullModel

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The unexpected-inflation identity -/

/-- Cochrane (2023), eq. (17.19), p. 411: the innovation `ΔE_{t+1} y = E_{t+1} y − E_t y`. -/
def innov (t : ℕ) (y : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) y - 𝔼.E t y

/-- Cochrane (2023), p. 411 (one-period debt; eq. (5.16), p. 121): the linearised flow
condition `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`. -/
def Flow (ρ : ℝ) (i s v π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ρ • v (t + 1) = v t + i t - π (t + 1) - s (t + 1)

/-- Cochrane (2023), eq. (17.16), p. 407: the ex-ante real rate `r_n = i_n − E_n π_{n+1}`
(earned between `n` and `n + 1`). -/
def rea (i π : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ := i n - 𝔼.E n (π (n + 1))

/-- The innovation is linear. -/
theorem innov_sub (t : ℕ) (a b : Ω → ℝ) : innov 𝔼 t (a - b) = innov 𝔼 t a - innov 𝔼 t b := by
  unfold innov
  rw [map_sub, map_sub]
  abel

/-- The innovation of a variable known at `t` is zero. -/
theorem innov_known {t s : ℕ} (hs : s ≤ t) {y : Ω → ℝ} (hy : 𝔼.E s y = y) : innov 𝔼 t y = 0 := by
  unfold innov
  rw [ForwardSolution.E_of_known 𝔼 (by omega) hy, ForwardSolution.E_of_known 𝔼 hs hy, sub_self]

/-- Cochrane (2023), p. 411: for `n ≥ t + 1`, the date-`(t+1)` news about the ex-post real
return `i_n − π_{n+1}` equals the news about the ex-ante rate `r_n`. -/
theorem innov_expost_eq {t n : ℕ} (hn : t + 1 ≤ n) (i π : ℕ → Ω → ℝ) :
    innov 𝔼 t (i n - π (n + 1)) = innov 𝔼 t (rea 𝔼 i π n) := by
  unfold innov rea
  simp only [map_sub, 𝔼.tower hn, 𝔼.tower (show t ≤ n by omega)]

/-- Cochrane (2023), p. 411: the `j = 0` term with the ex-post rate `r_{t+1} = i_t − π_{t+1}`
is `−ΔE_{t+1} π_{t+1}` (for adapted `i`), so (17.19) cannot be read with ex-post rates. -/
theorem expost_first_term (t : ℕ) {i : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (π : ℕ → Ω → ℝ) :
    innov 𝔼 t (i t - π (t + 1)) = -innov 𝔼 t (π (t + 1)) := by
  rw [innov_sub, innov_known 𝔼 le_rfl (hi t), zero_sub]

/-- The date-`t` ex-ante rate is known at `t`, so its innovation vanishes. -/
theorem innov_rea_self (t : ℕ) {i : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (π : ℕ → Ω → ℝ) :
    innov 𝔼 t (rea 𝔼 i π t) = 0 :=
  innov_known 𝔼 le_rfl (by unfold rea; rw [map_sub, hi t, 𝔼.E_E_self])

/-- Cochrane (2023), eq. (17.19), p. 411, finite horizon (exact): for adapted `v`, `i` and the
flow condition,
`ΔE_{t+1} π_{t+1} = −∑_{j≤N} ρʲ ΔE_{t+1} s̃_{t+1+j} + ∑_{j<N} ρ^{j+1} ΔE_{t+1} r_{t+1+j}
  − ρ^{N+1} ΔE_{t+1} v_{t+N+1}`. -/
theorem innov_finite {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v) (hi : 𝔼.Adapted i)
    (hf : Flow ρ i s v π) (t N : ℕ) (ω : Ω) :
    innov 𝔼 t (π (t + 1)) ω =
      -∑ j ∈ Finset.range (N + 1), ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω +
        ∑ j ∈ Finset.range N, ρ ^ (j + 1) * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω -
        ρ ^ (N + 1) * innov 𝔼 t (v (t + N + 1)) ω := by
  -- the innovation of the flow condition at date `n`
  have hflow : ∀ n, ρ * innov 𝔼 t (v (n + 1)) ω =
      innov 𝔼 t (v n) ω + innov 𝔼 t (i n - π (n + 1)) ω - innov 𝔼 t (s (n + 1)) ω := by
    intro n
    have h := congrArg (innov 𝔼 t) (hf n)
    unfold innov at h ⊢
    simp only [map_smul, map_sub, map_add] at h ⊢
    have h' := congrFun h ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at h' ⊢
    linear_combination h'
  induction N with
  | zero =>
    have h := hflow t
    rw [innov_known 𝔼 le_rfl (hv t), expost_first_term 𝔼 t hi] at h
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, Finset.range_zero,
      Finset.sum_empty, pow_one, add_zero, Pi.zero_apply, Pi.neg_apply] at h ⊢
    linear_combination h
  | succ N ih =>
    have h := hflow (t + N + 1)
    rw [innov_expost_eq 𝔼 (by omega)] at h
    rw [ih, Finset.sum_range_succ _ (N + 1),
      Finset.sum_range_succ (fun j => ρ ^ (j + 1) * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω) N,
      show t + 1 + (N + 1) = t + N + 1 + 1 by omega, show t + 1 + N = t + N + 1 by omega,
      show t + (N + 1) + 1 = t + N + 1 + 1 by omega]
    linear_combination ρ ^ (N + 1) * h


/-- Cochrane (2023), eq. (17.19), p. 411, corrected dating (with `ρ` placed explicitly): for
adapted `v`, `i`, the flow condition, the transversality condition
`ρᴺ ΔE_{t+1} v_{t+N} → 0` and summable news series,
`ΔE_{t+1} π_{t+1} = −∑ ρʲ ΔE_{t+1} s̃_{t+1+j} + ρ ∑ ρʲ ΔE_{t+1} r_{t+1+j}` with
`r_n = i_n − E_n π_{n+1}` dated as in (17.16). -/
theorem eq_17_19_own_dating {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hi : 𝔼.Adapted i) (hf : Flow ρ i s v π) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun N => ρ ^ N * innov 𝔼 t (v (t + N)) ω) atTop (𝓝 0))
    (hs : Summable fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
    (hr : Summable fun j => ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω) :
    innov 𝔼 t (π (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω +
        ρ * ∑' j, ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω := by
  have h1 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
      atTop (𝓝 (∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)) :=
    hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N => ∑ j ∈ Finset.range N,
      ρ ^ (j + 1) * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω) atTop
      (𝓝 (ρ * ∑' j, ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω)) := by
    refine (hr.hasSum.tendsto_sum_nat.const_mul ρ).congr fun N => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : Tendsto (fun N => ρ ^ (N + 1) * innov 𝔼 t (v (t + N + 1)) ω) atTop (𝓝 0) :=
    htvc.comp (tendsto_add_atTop_nat 1)
  have hlim := (h1.neg.add h2).sub h3
  rw [sub_zero] at hlim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr fun N => ?_) hlim
  exact innov_finite 𝔼 hv hi hf t N ω

/-- Cochrane (2023), eq. (17.19), p. 411, **as printed**, with `r_{t+1+j}` read as the ex-ante
real rate earned between `t + j` and `t + 1 + j`, `i_{t+j} − E_{t+j} π_{t+1+j}`:
`ΔE_{t+1} π_{t+1} = −∑_{j≥0} ρʲ ΔE_{t+1} s̃_{t+1+j} + ∑_{j≥0} ρʲ ΔE_{t+1} r_{t+1+j}`. The
`j = 0` real-rate term is known at `t` and has no news. -/
theorem eq_17_19 {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v)
    (hi : 𝔼.Adapted i) (hf : Flow ρ i s v π) (t : ℕ) (ω : Ω)
    (htvc : Tendsto (fun N => ρ ^ N * innov 𝔼 t (v (t + N)) ω) atTop (𝓝 0))
    (hs : Summable fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
    (hr : Summable fun j => ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + j)) ω) :
    innov 𝔼 t (π (t + 1)) ω =
      -∑' j, ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω +
        ∑' j, ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + j)) ω := by
  have hr' : Summable fun j => ρ ^ j * innov 𝔼 t (rea 𝔼 i π (t + 1 + j)) ω := by
    by_cases hρ : ρ = 0
    · simp [hρ, zero_pow_eq]
      exact (summable_nat_add_iff 1).mp (summable_of_ne_finset_zero (s := {0})
        (fun j hj => by simp at hj; simp [hj]))
    · have := ((summable_nat_add_iff 1).mpr hr).mul_left ρ⁻¹
      refine this.congr fun j => ?_
      rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
      field_simp
  rw [eq_17_19_own_dating 𝔼 hv hi hf t ω htvc hs hr', hr.tsum_eq_zero_add]
  rw [add_zero, innov_rea_self 𝔼 t hi, Pi.zero_apply, mul_zero, zero_add, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), eq. (17.19), p. 411: with the dating of (17.16), `r_n = i_n − E_n π_{n+1}`,
the printed formula (no factor `ρ` in front of the real-rate sum) holds iff `ρ = 1` or the
real-rate news is zero (here `S`, `R` stand for the two news sums of `eq_17_19_own_dating`). -/
theorem printed_own_dating_iff {ρ S R infl1 : ℝ} (h : infl1 = -S + ρ * R) :
    infl1 = -S + R ↔ ρ = 1 ∨ R = 0 := by
  rw [h]
  constructor
  · intro h'
    have : (ρ - 1) * R = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr h1
  · rintro (h1 | h1) <;> simp [h1]

/-- `ΔE_{t+1}` passes through a series dominated by a geometric series. -/
theorem innov_tsum {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ω, |f k ω| ≤ a ^ k * M) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (fun ω' => ∑' k, f k ω') ω = ∑' k, innov 𝔼 t (f k) ω := by
  have hg : Summable fun k : ℕ => a ^ k * M :=
    (summable_geometric_of_lt_one ha0 ha1).mul_right M
  have s1 : Summable fun k => 𝔼.E (t + 1) (f k) ω := Summable.of_norm_bounded hg
    (fun k => by rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) (t + 1) ω)
  have s2 : Summable fun k => 𝔼.E t (f k) ω := Summable.of_norm_bounded hg
    (fun k => by rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)
  unfold innov
  rw [Pi.sub_apply, 𝔼.E_tsum ha0 ha1 hf, 𝔼.E_tsum ha0 ha1 hf, ← s1.tsum_sub s2]
  rfl

/-- Cochrane (2023), eq. (17.19), p. 411, for bounded processes and `0 ≤ ρ < 1`, in the printed
form `ΔE_{t+1} π_{t+1} = −ΔE_{t+1} ∑ ρʲ s̃_{t+1+j} + ΔE_{t+1} ∑ ρʲ r_{t+1+j}` (real rates earned
between `t + j` and `t + 1 + j`): transversality and summability are automatic. -/
theorem eq_17_19_bounded {ρ M : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {i s v π : ℕ → Ω → ℝ}
    (hv : 𝔼.Adapted v) (hi : 𝔼.Adapted i) (hf : Flow ρ i s v π)
    (hsb : ∀ t ω, |s t ω| ≤ M) (hvb : ∀ t ω, |v t ω| ≤ M) (hib : ∀ t ω, |i t ω| ≤ M)
    (hπb : ∀ t ω, |π t ω| ≤ M) (t : ℕ) (ω : Ω) :
    innov 𝔼 t (π (t + 1)) ω =
      -innov 𝔼 t (fun ω' => ∑' j, ρ ^ j * s (t + 1 + j) ω') ω +
        innov 𝔼 t (fun ω' => ∑' j, ρ ^ j * rea 𝔼 i π (t + j) ω') ω := by
  have hinb : ∀ (y : Ω → ℝ) (K : ℝ), (∀ ω, |y ω| ≤ K) → ∀ ω, |innov 𝔼 t y ω| ≤ 2 * K := by
    intro y K hy ω
    unfold innov
    rw [Pi.sub_apply, two_mul]
    exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le hy _ ω) (𝔼.abs_E_le hy _ ω))
  have hreab : ∀ n ω, |rea 𝔼 i π n ω| ≤ 2 * M := by
    intro n ω
    unfold rea
    rw [Pi.sub_apply, two_mul]
    exact (abs_sub _ _).trans (add_le_add (hib n ω) (𝔼.abs_E_le (hπb (n + 1)) n ω))
  have hgeo : Summable fun k : ℕ => ρ ^ k * (2 * (2 * M)) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_right _
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb 0 ω)
  have hsm : ∀ (y : ℕ → Ω → ℝ), (∀ n ω, |y n ω| ≤ 2 * M) →
      Summable fun j => ρ ^ j * innov 𝔼 t (y j) ω := by
    intro y hy
    refine Summable.of_norm_bounded hgeo (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (hinb _ _ (hy j) ω) (pow_nonneg hρ0 j)
  have hs2 : ∀ n ω, |s n ω| ≤ 2 * M := fun n ω => (hsb n ω).trans (by linarith)
  have htvc : Tendsto (fun N => ρ ^ N * innov 𝔼 t (v (t + N)) ω) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N => ρ ^ N * (2 * M)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (2 * M)
    refine squeeze_zero_norm (fun N => ?_) hlim
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hρ0]
    exact mul_le_mul_of_nonneg_left (hinb _ _ (hvb (t + N)) ω) (pow_nonneg hρ0 N)
  rw [eq_17_19 𝔼 hv hi hf t ω htvc (hsm (fun j => s (t + 1 + j)) (fun n ω => hs2 _ ω))
    (hsm (fun j => rea 𝔼 i π (t + j)) (fun n ω => hreab _ ω))]
  rw [innov_tsum 𝔼 hρ0 hρ1 (f := fun j ω' => ρ ^ j * s (t + 1 + j) ω') (M := M)
      (fun k ω' => by rw [abs_mul, abs_pow, abs_of_nonneg hρ0]
                      exact mul_le_mul_of_nonneg_left (hsb _ ω') (pow_nonneg hρ0 k)) t ω,
    innov_tsum 𝔼 hρ0 hρ1 (f := fun j ω' => ρ ^ j * rea 𝔼 i π (t + j) ω') (M := 2 * M)
      (fun k ω' => by rw [abs_mul, abs_pow, abs_of_nonneg hρ0]
                      exact mul_le_mul_of_nonneg_left (hreab _ ω') (pow_nonneg hρ0 k)) t ω]
  have hc : ∀ (c : ℝ) (y : Ω → ℝ), innov 𝔼 t (fun ω' => c * y ω') ω = c * innov 𝔼 t y ω := by
    intro c y
    change innov 𝔼 t (c • y) ω = _
    unfold innov
    rw [map_smul, map_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hc]

/-- Cochrane (2023), p. 411 ("for higher interest rates to lower inflation, there must be a
fiscal contraction"): in (17.19), if unexpected inflation is negative and real-rate news is
nonnegative, news about the present value of surpluses is positive. -/
theorem fiscal_contraction {infl1 S R : ℝ} (h : infl1 = -S + R) (hinfl : infl1 < 0) (hR : 0 ≤ R) :
    0 < S := by linarith

/-- Cochrane (2023), pp. 411–412: since `s̃` is the surplus divided by the value of debt, the
surplus as a share of GDP is `(debt/GDP) · s̃`. With no real-rate news an unexpected
disinflation of `d` points needs surplus news of `(debt/GDP) · d` points of GDP: one for one at
100% debt-to-GDP, a quarter of that at 25% (1980). -/
theorem surplus_gdp {infl1 S debtGDP : ℝ} (h : infl1 = -S + 0) :
    debtGDP * S = debtGDP * (-infl1) ∧ (1 : ℝ) * S = -infl1 ∧ (1 / 4 : ℝ) * S = -infl1 / 4 := by
  refine ⟨by rw [h]; ring, by rw [h]; ring, by rw [h]; ring⟩

/-! ### Reverse-engineered disturbances (p. 414) -/

/-- Cochrane (2023), p. 414 ("I reverse-engineer a `{u_t}` disturbance to produce the same
interest-rate path and a chosen value of initial inflation"; perfect foresight): for every
bounded rate path `i`, every initial inflation `p` and every `φ`, the disturbance
`u = i − φ π` with `π = path p` makes `(x, π)` with `x_t = (π_t − β π_{t+1})/κ` an equilibrium
of the model with the rule `i_t = φ π_t + u_t`, with initial inflation `p`. Different `p` give
different inflation and (for `φ ≠ 0`) different disturbances, but the same interest rate. -/
theorem reverse_engineer {σ β κ M φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (p : ℝ) :
    let π := path σ β κ i p
    let u := fun t => i t - φ * π t
    (∀ t, i t = φ * π t + u t) ∧ π 0 = p ∧ BoundedS π ∧
      PFEqm σ β κ i (fun t => (π t - β * π (t + 1)) / κ) π := by
  have ha := mul_pos hσ hκ
  have hb := path_bounded ha hβ hi p
  refine ⟨fun t => by ring, rfl, hb, (pfEqm_iff_second hκ.ne' _ _ _).mpr ⟨fun t => rfl, ?_⟩⟩
  exact (second_iff_factor ha hβ hi hb).mpr (path_factor ha hβ i p)

/-- Cochrane (2023), p. 414: different initial inflations give different reverse-engineered
disturbances (for `φ ≠ 0`) producing the same interest-rate path. -/
theorem reverse_engineer_distinct {σ β κ φ p p' : ℝ} (hφ : φ ≠ 0) (hp : p ≠ p') (i : ℕ → ℝ) :
    (fun t => i t - φ * path σ β κ i p t) ≠ (fun t => i t - φ * path σ β κ i p' t) := by
  intro h
  have := congrFun h 0
  simp only [path] at this
  exact hp (mul_left_cancel₀ hφ (by linarith))


/-! ### Figure 17.7: an AR(1) interest-rate rise -/

/-- Cochrane (2023), Fig. 17.7, p. 413: the particular-solution coefficient
`c = σκ/(−βη² + (1 + β + σκ)η − 1)` of the response to `i_n = ηⁿ`. -/
noncomputable def cAR (σ β κ η : ℝ) : ℝ := σ * κ / (-β * η ^ 2 + (1 + β + σ * κ) * η - 1)

/-- Cochrane (2023), Fig. 17.7, p. 413 (dates `n = 0, 1, …` stand for the book's `1, 2, …`):
inflation `π_n = c ηⁿ + (π₁ − c) μⁿ`, `μ = 1/λ₁`, for the AR(1) path `i_n = ηⁿ` with initial
inflation `π₁ = p`. -/
noncomputable def piAR (σ β κ η p : ℝ) (n : ℕ) : ℝ :=
  cAR σ β κ η * η ^ n + (p - cAR σ β κ η) * (lam1 σ β κ)⁻¹ ^ n

/-- Cochrane (2023), Fig. 17.7: `π_n = c ηⁿ + (π₁ − c) μⁿ` solves (17.18) for `i_n = ηⁿ`. -/
theorem piAR_second {σ β κ η : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0) (p : ℝ) :
    Second σ β κ (fun n => η ^ n) (piAR σ β κ η p) := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have hroot : 1 - (1 + β + σ * κ) * (lam1 σ β κ)⁻¹ + β * (lam1 σ β κ)⁻¹ ^ 2 = 0 := by
    have h1 := lam_sum σ β κ
    have h2 := lam_prod ha hβ
    have hr : lam1 σ β κ ^ 2 - (1 + β + σ * κ) * lam1 σ β κ + β = 0 := by
      linear_combination lam1 σ β κ * h1 - h2
    field_simp
    linear_combination hr
  have hc : cAR σ β κ η * (-β * η ^ 2 + (1 + β + σ * κ) * η - 1) = σ * κ := by
    unfold cAR; exact div_mul_cancel₀ _ hD
  intro n
  simp only [piAR, pow_succ]
  linear_combination (-(η ^ n)) * hc +
    (p - cAR σ β κ η) * (lam1 σ β κ)⁻¹ ^ n * hroot

/-- Cochrane (2023), p. 414 ("the inflation path is then determined by the solution (5.5) up to
an initial value"): for `0 ≤ η < 1`, `piAR p` is the unique bounded equilibrium path with
initial inflation `p`. -/
theorem piAR_eq_path {σ β κ η : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hD : -β * η ^ 2 + (1 + β + σ * κ) * η - 1 ≠ 0) (p : ℝ) :
    piAR σ β κ η p = path σ β κ (fun n => η ^ n) p := by
  have hi : ∀ n, |η ^ n| ≤ 1 := fun n => by
    rw [abs_of_nonneg (pow_nonneg hη0 n)]; exact pow_le_one₀ hη0 hη1.le
  have hl1 := one_lt_lam1 ha hβ
  have hμ0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (one_pos.trans hl1).le
  have hμ1 : (lam1 σ β κ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hl1).le
  obtain ⟨_, _, huniq⟩ := pf_existsUnique ha hβ hi p
  have hb : BoundedS (piAR σ β κ η p) := ⟨|cAR σ β κ η| + |p - cAR σ β κ η|, fun n => by
    unfold piAR
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_of_le_one_right (abs_nonneg _) (hi n)
    · rw [abs_of_nonneg (pow_nonneg hμ0 n)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hμ0 hμ1)⟩
  have hp : BoundedS (path σ β κ (fun n => η ^ n) p) := path_bounded ha hβ hi p
  rw [huniq _ ⟨hb, piAR_second ha hβ hD p, by simp [piAR]⟩,
    huniq _ ⟨hp, (second_iff_factor ha hβ hi hp).mpr (path_factor ha hβ _ p), rfl⟩]

/-- Cochrane (2023), p. 412 and Fig. 17.7: the cumulative surplus required by (17.19) with
`ρ = 1` (after a shock at date 1, pre-shock expectations at the steady state, perfect foresight
afterwards): `Σs = −π₁ + ∑_n (i_n − π_{n+1})` — the windfall plus the real interest costs. -/
noncomputable def sigmaS (σ β κ η p : ℝ) : ℝ :=
  -p + ∑' n, (η ^ n - piAR σ β κ η p (n + 1))

/-- Cochrane (2023), Fig. 17.7: closed form
`Σs = −π₁ + 1/(1 − η) − c η/(1 − η) − (π₁ − c)/(λ₁ − 1)`. -/
theorem sigmaS_closed {σ β κ η : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (p : ℝ) :
    sigmaS σ β κ η p = -p + 1 / (1 - η) - cAR σ β κ η * η / (1 - η) -
      (p - cAR σ β κ η) / (lam1 σ β κ - 1) := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hμ0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr hl0.le
  have hμ1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have g1 := hasSum_geometric_of_lt_one hη0 hη1
  have g2 := hasSum_geometric_of_lt_one hμ0 hμ1
  have hs : HasSum (fun n => η ^ n - piAR σ β κ η p (n + 1))
      ((1 - η)⁻¹ - (cAR σ β κ η * η * (1 - η)⁻¹ +
        (p - cAR σ β κ η) * (lam1 σ β κ)⁻¹ * (1 - (lam1 σ β κ)⁻¹)⁻¹)) := by
    refine g1.sub ((g1.mul_left (cAR σ β κ η * η)).add
      (g2.mul_left ((p - cAR σ β κ η) * (lam1 σ β κ)⁻¹))) |>.congr_fun ?_
    intro n
    simp only [piAR, pow_succ]
    ring
  unfold sigmaS
  rw [hs.tsum_eq]
  have h1 : 1 - η ≠ 0 := by linarith
  have h2 : lam1 σ β κ - 1 ≠ 0 := by linarith
  have h3 : 1 - (lam1 σ β κ)⁻¹ = (lam1 σ β κ - 1) / lam1 σ β κ := by field_simp
  rw [h3]
  field_simp
  ring

/-- Cochrane (2023), Fig. 17.7 (`σ = 1`, `κ = 0.25`, `β = 0.95`, `η = 0.6`): `c = −125/11`. -/
theorem fig17_7_c : cAR 1 (19 / 20) (1 / 4) (3 / 5) = -125 / 11 := by
  unfold cAR; norm_num

/-- Cochrane (2023), Fig. 17.7: `λ₁ = (2.2 + √1.04)/2`. -/
theorem fig17_7_lam1 : lam1 1 (19 / 20) (1 / 4) = (11 / 5 + Real.sqrt (26 / 25)) / 2 := by
  unfold lam1
  rw [show ((1 : ℝ) + 19 / 20 + 1 * (1 / 4)) ^ 2 - 4 * (19 / 20) = 26 / 25 by norm_num]
  norm_num

/-- Cochrane (2023), Fig. 17.7: `1.6099 < λ₁ < 1.609905`. -/
theorem fig17_7_lam1_bounds :
    (1.6099 : ℝ) < lam1 1 (19 / 20) (1 / 4) ∧ lam1 1 (19 / 20) (1 / 4) < 1.609905 := by
  rw [fig17_7_lam1]
  have h1 : (1.0198 : ℝ) < Real.sqrt (26 / 25) :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have h2 : Real.sqrt (26 / 25) < (1.01981 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  constructor <;> linarith

/-- The book's parameters satisfy `σκ > 0`, `β > 0`, `0 ≤ η < 1`. -/
theorem fig17_7_params :
    (0 : ℝ) < 1 * (1 / 4) ∧ (0 : ℝ) < 19 / 20 ∧ (0 : ℝ) ≤ 3 / 5 ∧ (3 / 5 : ℝ) < 1 := by
  norm_num

/-- Cochrane (2023), Fig. 17.7: `Σs` at the book's parameters, in terms of
`L = 1/(λ₁ − 1) ∈ (1.639599, 1.639614)`: `Σs = −π₁ + 5/2 + 375/22 − (π₁ + 125/11) L`. -/
theorem fig17_7_sigmaS (p : ℝ) :
    sigmaS 1 (19 / 20) (1 / 4) (3 / 5) p =
      -p + 5 / 2 + 375 / 22 - (p + 125 / 11) * (1 / (lam1 1 (19 / 20) (1 / 4) - 1)) := by
  obtain ⟨ha, hβ, hη0, hη1⟩ := fig17_7_params
  rw [sigmaS_closed ha hβ hη0 hη1, fig17_7_c]
  ring

/-- The bounds `1.639599 < 1/(λ₁ − 1) < 1.639614` at the book's parameters. -/
theorem fig17_7_L_bounds :
    (1.639599 : ℝ) < 1 / (lam1 1 (19 / 20) (1 / 4) - 1) ∧
      1 / (lam1 1 (19 / 20) (1 / 4) - 1) < 1.639614 := by
  obtain ⟨h1, h2⟩ := fig17_7_lam1_bounds
  have hp : 0 < lam1 1 (19 / 20) (1 / 4) - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- Cochrane (2023), Fig. 17.7, p. 413 (panel titles): with the same AR(1) interest-rate path,
initial inflation `π₁ = −1, −0.5, 0, 0.5` requires cumulative surpluses that round to
`Σs = 3.55, 2.23, 0.91, −0.41` percent of GDP (`ρ = 1`, 100% debt-to-GDP). -/
theorem fig17_7_values :
    (3.545 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1) ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1) < 3.555) ∧
    (2.225 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1 / 2) ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1 / 2) < 2.235) ∧
    (0.905 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) 0 ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) 0 < 0.915) ∧
    (-0.415 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (1 / 2) ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (1 / 2) < -0.405) := by
  obtain ⟨h1, h2⟩ := fig17_7_L_bounds
  simp only [fig17_7_sigmaS]
  generalize 1 / (lam1 1 (19 / 20) (1 / 4) - 1) = L at h1 h2 ⊢
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> norm_num <;> linarith

/-- Cochrane (2023), p. 413: in the top-left panel (`π₁ = −1`) the surpluses rise one point to
pay the deflationary windfall and "an additional 2.55 percentage points of GDP because of the
long period of high real interest rates": `∑ (i_n − π_{n+1}) = Σs + π₁ ∈ (2.545, 2.555)`. -/
theorem fig17_7_real_rates :
    2.545 < sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1) + (-1) ∧
      sigmaS 1 (19 / 20) (1 / 4) (3 / 5) (-1) + (-1) < 2.555 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := fig17_7_values
  obtain ⟨l1, l2⟩ := fig17_7_L_bounds
  rw [fig17_7_sigmaS] at h1 h2 ⊢
  generalize 1 / (lam1 1 (19 / 20) (1 / 4) - 1) = L at h1 h2 l1 l2 ⊢
  constructor <;> norm_num <;> linarith

/-- Cochrane (2023), Fig. 17.7, p. 414 (lower-left panel, "inflation starts at zero and then
slightly rises"): with `π₁ = 0`, `π₂ = c (η − μ) ∈ (0, 0.25)`. -/
theorem fig17_7_zero_panel :
    0 < piAR 1 (19 / 20) (1 / 4) (3 / 5) 0 1 ∧ piAR 1 (19 / 20) (1 / 4) (3 / 5) 0 1 < 1 / 4 := by
  obtain ⟨h1, h2⟩ := fig17_7_lam1_bounds
  have hp : 0 < lam1 1 (19 / 20) (1 / 4) := by linarith
  have e : piAR 1 (19 / 20) (1 / 4) (3 / 5) 0 1 =
      -125 / 11 * (3 / 5) + 125 / 11 * (1 / lam1 1 (19 / 20) (1 / 4)) := by
    simp only [piAR, fig17_7_c, pow_one]
    ring
  have m1 : (1 / 1.609905 : ℝ) < 1 / lam1 1 (19 / 20) (1 / 4) :=
    one_div_lt_one_div_of_lt hp h2
  have m2 : 1 / lam1 1 (19 / 20) (1 / 4) < (1 / 1.6099 : ℝ) :=
    one_div_lt_one_div_of_lt (by norm_num) h1
  rw [e]
  constructor <;> norm_num at m1 m2 ⊢ <;> linarith

/-- Cochrane (2023), p. 414 ("the reverse-engineered `u_t` processes are not AR(1)"): a sum
`a ηⁿ + b μⁿ` with `a, b ≠ 0`, `η ≠ μ` is not a geometric sequence. -/
theorem not_geometric {a b η μ : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hημ : η ≠ μ) :
    ¬ ∃ r : ℝ, ∀ n : ℕ, a * η ^ (n + 1) + b * μ ^ (n + 1) = r * (a * η ^ n + b * μ ^ n) := by
  rintro ⟨r, hr⟩
  have h0 := hr 0
  have h1 := hr 1
  simp only [pow_zero, pow_one, mul_one, zero_add] at h0 h1
  have key : a * b * (η - μ) ^ 2 = 0 := by
    have : (a * η + b * μ) ^ 2 = (a + b) * (a * η ^ 2 + b * μ ^ 2) := by
      rw [show (1 + 1 : ℕ) = 2 from rfl] at h1
      have : (a * η + b * μ) ^ 2 = (a * η + b * μ) * (r * (a + b)) := by rw [← h0]; ring
      rw [this, h1]; ring
    linear_combination -this
  have : (η - μ) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hημ)
  exact (mul_ne_zero (mul_ne_zero ha hb) this) key

/-- Cochrane (2023), Fig. 17.7 and p. 414: at the book's parameters (`φ = 1.2`) the
reverse-engineered disturbance `u_n = i_n − φ π_n` is not AR(1) for any initial inflation
`π₁ ≠ c = −125/11`, in particular for all four panels. -/
theorem fig17_7_u_not_ar1 {p : ℝ} (hp : p ≠ -125 / 11) :
    ¬ ∃ r : ℝ, ∀ n : ℕ,
      ((3 / 5 : ℝ) ^ (n + 1) - 6 / 5 * piAR 1 (19 / 20) (1 / 4) (3 / 5) p (n + 1)) =
        r * ((3 / 5 : ℝ) ^ n - 6 / 5 * piAR 1 (19 / 20) (1 / 4) (3 / 5) p n) := by
  obtain ⟨h1, h2⟩ := fig17_7_lam1_bounds
  have hp0 : 0 < lam1 1 (19 / 20) (1 / 4) := by linarith
  have hμ : (3 / 5 : ℝ) ≠ (lam1 1 (19 / 20) (1 / 4))⁻¹ := by
    intro h
    have : lam1 1 (19 / 20) (1 / 4) = 5 / 3 := by
      rw [← inv_inv (lam1 1 (19 / 20) (1 / 4)), ← h]; norm_num
    linarith
  have hb : -(6 / 5) * (p + 125 / 11) ≠ 0 := by
    have : p + 125 / 11 ≠ 0 := fun h => hp (by linarith)
    exact mul_ne_zero (by norm_num) this
  have hng := not_geometric (a := 161 / 11) (by norm_num) hb hμ
  rintro ⟨r, hr⟩
  refine hng ⟨r, fun n => ?_⟩
  have := hr n
  simp only [piAR, fig17_7_c] at this
  linear_combination this

/-- Cochrane (2023), p. 413: "multiplying by 5 … requires an 18% of GDP austerity program":
`5 × 3.55 = 17.75 ≈ 18`. -/
theorem fig17_7_times_five : (5 : ℝ) * 3.55 = 17.75 := by norm_num

/-- Survey error E10, Cochrane (2023), p. 414: "5 × 2.23 = 11.5" is an arithmetic slip:
`5 × 2.23 = 11.15 ≠ 11.5`; at $200 billion per point of GDP (p. 411) this is $2.23 trillion,
matching the printed "$2.2 trillion". -/
theorem e10 : (5 : ℝ) * 2.23 = 11.15 ∧ (5 : ℝ) * 2.23 ≠ 11.5 ∧ (11.15 : ℝ) * 200 = 2230 := by
  norm_num


/-! ### Figure 17.6: the surplus change `Δs` of equilibria A–E (ρ < 1) -/

/-- Cochrane (2023), Fig. 17.6, p. 410: after an unexpected permanent rise at date 0
(`i_t = 1`, `t ≥ 0`), the perfect-foresight path with initial inflation `p` is
`π_j = 1 + (p − 1) λ₁^{−j}`. -/
theorem path_step0 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (p : ℝ) (j : ℕ) :
    path σ β κ (stepI 0) p j = 1 + (p - 1) * (lam1 σ β κ)⁻¹ ^ j := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have h1 : 1 - lam2 σ β κ ≠ 0 := by linarith
  have hsk := sigma_kappa_eq ha hβ
  induction j with
  | zero => simp [path]
  | succ j ih =>
    simp only [path]
    rw [ih, F_step h2.le h21, Nat.zero_sub, pow_zero, pow_succ, hsk]
    field_simp
    ring

/-- Cochrane (2023), Fig. 17.6, p. 410, and eq. (17.19) with `0 ≤ ρ < 1` (real rates earned
between `j` and `j + 1`, `eq_17_19`): the news about the present value of surpluses needed by
the equilibrium with initial inflation `p`, with pre-shock expectations at the steady state,
`Δs = −π₀ + ∑_j ρʲ (i_j − π_{j+1})`. A permanent change `Δ` of `s̃` has present value
`Δ/(1 − ρ)` (`permanent_surplus_pct`), i.e. `Δ/s̃̄` with steady state `s̃̄ = 1 − ρ` (debt value
one), so `Δs` is the percentage change in steady-state surpluses that Fig. 17.6 reports. -/
noncomputable def deltaS (σ β κ ρ p : ℝ) : ℝ :=
  -p + ∑' j : ℕ, ρ ^ j * (1 - path σ β κ (stepI 0) p (j + 1))

/-- A permanent surplus change `Δ` has present value `∑ ρʲ Δ = Δ/(1 − ρ)`. -/
theorem permanent_surplus_pct {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (Δ : ℝ) :
    ∑' j : ℕ, ρ ^ j * Δ = Δ / (1 - ρ) := by
  rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0 hρ1, div_eq_inv_mul]

/-- Cochrane (2023), Fig. 17.6: closed form `Δs(p) = (1 − p)/(λ₁ − ρ) − p` for `0 ≤ ρ < λ₁`. -/
theorem deltaS_closed {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) (p : ℝ) :
    deltaS σ β κ ρ p = (1 - p) / (lam1 σ β κ - ρ) - p := by
  have hl0 : 0 < lam1 σ β κ := one_pos.trans (one_lt_lam1 ha hβ)
  have hq0 : 0 ≤ ρ * (lam1 σ β κ)⁻¹ := mul_nonneg hρ0 (inv_nonneg.mpr hl0.le)
  have hq1 : ρ * (lam1 σ β κ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hl0]; exact hρ
  have hterm : ∀ j : ℕ, ρ ^ j * (1 - path σ β κ (stepI 0) p (j + 1)) =
      (1 - p) * (lam1 σ β κ)⁻¹ * (ρ * (lam1 σ β κ)⁻¹) ^ j := fun j => by
    rw [path_step0 ha hβ, mul_pow, pow_succ]; ring
  unfold deltaS
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have h1 : lam1 σ β κ - ρ ≠ 0 := by linarith
  field_simp
  ring

/-- Cochrane (2023), Fig. 17.6, equilibrium B (`π = 1` at once, the super-neutral response):
`Δs = −1`, for every parameter value — the printed "B, Δs = −1.00". -/
theorem deltaS_B {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) : deltaS σ β κ ρ 1 = -1 := by
  rw [deltaS_closed ha hβ hρ0 hρ]; simp

/-- Cochrane (2023), Fig. 17.6, equilibrium D (no unexpected inflation, `π₀ = 0`):
`Δs = 1/(λ₁ − ρ) > 0` — real rates rise, so surpluses must rise. -/
theorem deltaS_D {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) : deltaS σ β κ ρ 0 = 1 / (lam1 σ β κ - ρ) ∧ 0 < deltaS σ β κ ρ 0 := by
  rw [deltaS_closed ha hβ hρ0 hρ]
  refine ⟨by ring, ?_⟩
  have : 0 < lam1 σ β κ - ρ := by linarith
  simp only [sub_zero]
  positivity

/-- Cochrane (2023), Fig. 17.6, equilibrium C and p. 410 ("the Δs = 0 equilibrium is not the
equilibrium … with ΔE₁π₁ = 0"): `Δs = 0` exactly at initial inflation `1/(1 + λ₁ − ρ) ∈ (0, 1)`. -/
theorem deltaS_zero_iff {σ β κ ρ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (hρ0 : 0 ≤ ρ)
    (hρ : ρ < lam1 σ β κ) (p : ℝ) :
    deltaS σ β κ ρ p = 0 ↔ p = 1 / (1 + lam1 σ β κ - ρ) := by
  rw [deltaS_closed ha hβ hρ0 hρ]
  have h1 : lam1 σ β κ - ρ ≠ 0 := by linarith
  have h2 : 1 + lam1 σ β κ - ρ ≠ 0 := by linarith
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Cochrane (2023), Fig. 17.6, p. 410: the printed `Δs` values cannot all hold with A and E
being the jumps `δ₁ = ±1%` relative to the `δ = 0` equilibrium. Whatever the parameters, `Δs` is
affine, `Δs(p) = K (1 − p) − p` (`deltaS_closed`, with `K = 1/(λ₁ − ρ)`; with (17.16)'s dating
`K = ρ/(λ₁ − ρ)`). If D (`p = 0`) has `Δs = 1.66` and the `δ = 0` equilibrium (`p = p₀`) has
`Δs = 0.67` (up to rounding), then `δ = +1` gives `Δs < −1.9` (printed A: −1.53) and `δ = −1`
gives `Δs > 3.2` (printed E: 2.99). -/
theorem fig17_6_inconsistent {K p0 : ℝ} (f : ℝ → ℝ) (hf : ∀ p, f p = K * (1 - p) - p)
    (hD : |f 0 - 1.66| ≤ 0.005) (h0 : |f p0 - 0.67| ≤ 0.005) :
    f (p0 + 1) < -1.9 ∧ 3.2 < f (p0 - 1) := by
  rw [hf] at hD h0 ⊢
  rw [hf]
  rw [abs_le] at hD h0
  constructor <;> nlinarith [hD.1, hD.2, h0.1, h0.2]

/-- Cochrane (2023), Fig. 17.6, p. 410: with the affine `Δs` of `deltaS_closed`, the printed A
(`Δs = −1.53`) and E (`Δs = 2.99`) correspond to jumps of about `+0.83` and `−0.87` relative to
the `δ = 0` equilibrium (all printed values up to rounding), not `±1`. -/
theorem fig17_6_implied_jumps {K p0 pA pE : ℝ} (f : ℝ → ℝ) (hf : ∀ p, f p = K * (1 - p) - p)
    (hD : |f 0 - 1.66| ≤ 0.005) (h0 : |f p0 - 0.67| ≤ 0.005) (hA : |f pA + 1.53| ≤ 0.005)
    (hE : |f pE - 2.99| ≤ 0.005) :
    0.82 < pA - p0 ∧ pA - p0 < 0.84 ∧ 0.86 < p0 - pE ∧ p0 - pE < 0.88 := by
  simp only [hf, abs_le] at hD h0 hA hE
  have hK1 : 1.655 ≤ K := by linarith [hD.1]
  have hK2 : K ≤ 1.665 := by linarith [hD.2]
  have eA : (1 + K) * (pA - p0) = (K * (1 - p0) - p0) - (K * (1 - pA) - pA) := by ring
  have eE : (1 + K) * (p0 - pE) = (K * (1 - pE) - pE) - (K * (1 - p0) - p0) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hA.1, hA.2, hE.1, hE.2, h0.1, h0.2]

end Cochrane.KeynesianStickyPrices.FiscalUnderpinnings
