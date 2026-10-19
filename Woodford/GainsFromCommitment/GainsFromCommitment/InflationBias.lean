/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Expectations

/-!
# The inflationary bias of discretionary policy

Woodford (2003), *Interest and Prices*, Chapter 7, §1.1, eqs. (1.1)–(1.6) and Proposition 7.1,
pp. 468–472.

With the aggregate-supply relation (1.1) `π_t = κ x_t + β E_t π_{t+1}` and the period loss
`π_t² + λ(x_t − x*)²` of (1.2), a discretionary central bank takes expected inflation `πᵉ` as
given and solves the static problem of minimising the period loss along the line (1.3)
`π = κx + βπᵉ`. This module proves:

* `static_foc_iff` ((1.3)–(1.4)): a point of the line is a minimiser iff
  `π + (λ/κ)(x − x*) = 0`; `staticOptimal_iff` (1.5): the minimiser is unique, with
  `π = (1 + κ²/λ)⁻¹(κx* + βπᵉ)`;
* `fixedPoint_iff` (1.6): the unique fixed point `πᵉ = κλx*/((1 − β)λ + κ²)`;
  `discretionInflation_pos_iff`: it is positive iff `x* > 0`;
* **Proposition 7.1** in exact linear-quadratic form. A *Markov equilibrium*
  (`MarkovEquilibrium`) is a time-invariant pair `(pbar, xbar)` (the continuation game from every
  date is identical and there is no payoff-relevant state) such that, with rational expectations
  `πᵉ = pbar`, `(pbar, xbar)` solves the bank's static problem. `prop_7_1` proves it exists and is
  unique, with `pbar` given by (1.6). Without imposing time invariance, `discretion_unique` shows
  that every bounded adapted sequence of period-by-period discretionary optima (under an
  arbitrary expectation system) is that same constant path, and `discretion_exists` that the
  constant path is one.

The book's qualifier "up to an error of order `O(‖Δ_{−1}^{1/2}, Δ_y, ξ̃‖²)`" concerns the
second-order welfare approximation of Chapter 6 and is not part of this linear-quadratic
statement.
-/

namespace Woodford.GainsFromCommitment.InflationBias

/-- Woodford (2003), eq. (1.2), p. 469: the period loss `π² + λ(x − x*)²`. -/
def staticLoss (lam xs π x : ℝ) : ℝ := π ^ 2 + lam * (x - xs) ^ 2

/-- Woodford (2003), (1.3), p. 471: `(π, x)` minimises the period loss among the pairs on the
perceived trade-off `π = κx + βπᵉ` (the discretionary bank's static problem). -/
def StaticOptimal (β κ lam xs πe π x : ℝ) : Prop :=
  π = κ * x + β * πe ∧ ∀ x', staticLoss lam xs π x ≤ staticLoss lam xs (κ * x' + β * πe) x'

/-- Woodford (2003), (1.3)–(1.4), p. 471: along the line `π = κx + βπᵉ`,
`ℓ(x') − ℓ(x) = (κ² + λ)(x' − x)² + 2(x' − x)(κπ + λ(x − x*))`. -/
theorem staticLoss_line (β κ lam xs πe x x' : ℝ) :
    staticLoss lam xs (κ * x' + β * πe) x' - staticLoss lam xs (κ * x + β * πe) x =
      (κ ^ 2 + lam) * (x' - x) ^ 2 + 2 * (x' - x) * (κ * (κ * x + β * πe) + lam * (x - xs)) := by
  unfold staticLoss; ring

/-- Woodford (2003), eq. (1.4), p. 471: the first-order condition of the static problem is
necessary and sufficient, `(π, x)` is optimal iff `π + (λ/κ)(x − x*) = 0` (for `κ ≠ 0`,
`λ > 0`). -/
theorem static_foc_iff {β κ lam xs πe π x : ℝ} (hκ : κ ≠ 0) (hlam : 0 < lam)
    (hline : π = κ * x + β * πe) :
    StaticOptimal β κ lam xs πe π x ↔ π + lam / κ * (x - xs) = 0 := by
  have hkey : κ * π + lam * (x - xs) = κ * (π + lam / κ * (x - xs)) := by field_simp
  constructor
  · intro ⟨_, hopt⟩
    set g := κ * π + lam * (x - xs) with hg
    have hd : 0 < κ ^ 2 + lam := by positivity
    have h := hopt (x - g / (κ ^ 2 + lam))
    have hl := staticLoss_line β κ lam xs πe x (x - g / (κ ^ 2 + lam))
    rw [← hline] at hl
    have hval : (κ ^ 2 + lam) * (x - g / (κ ^ 2 + lam) - x) ^ 2 +
        2 * (x - g / (κ ^ 2 + lam) - x) * g = -(g ^ 2 / (κ ^ 2 + lam)) := by
      field_simp; ring
    rw [hval] at hl
    have hg0 : g ^ 2 / (κ ^ 2 + lam) ≤ 0 := by linarith
    have : g = 0 := by
      have := div_nonneg (sq_nonneg g) hd.le
      have h2 : g ^ 2 = 0 := by
        have := (div_eq_zero_iff.mp (le_antisymm hg0 this)).resolve_right hd.ne'
        exact this
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h2
    rw [hkey] at this
    exact (mul_eq_zero.mp this).resolve_left hκ
  · intro hfoc
    refine ⟨hline, fun x' => ?_⟩
    have hl := staticLoss_line β κ lam xs πe x x'
    rw [← hline, hkey, hfoc] at hl
    have : 0 ≤ (κ ^ 2 + lam) * (x' - x) ^ 2 := by positivity
    linarith

/-- Woodford (2003), eq. (1.5), p. 471: the discretionary bank's unique best response,
`π = (1 + κ²/λ)⁻¹(κx* + βπᵉ)` (with `x` then given by (1.3)). -/
theorem staticOptimal_iff {β κ lam xs πe π x : ℝ} (hκ : κ ≠ 0) (hlam : 0 < lam) :
    StaticOptimal β κ lam xs πe π x ↔
      π = (1 + κ ^ 2 / lam)⁻¹ * (κ * xs + β * πe) ∧ π = κ * x + β * πe := by
  have hd : 0 < 1 + κ ^ 2 / lam := by positivity
  constructor
  · intro h
    have hfoc := (static_foc_iff hκ hlam h.1).mp h
    refine ⟨?_, h.1⟩
    rw [eq_inv_mul_iff_mul_eq₀ hd.ne']
    have hx : x = (π - β * πe) / κ := by rw [h.1]; field_simp; ring
    rw [hx] at hfoc
    field_simp at hfoc
    have e : (1 + κ ^ 2 / lam) * π = ((lam + κ ^ 2) * π) / lam := by field_simp
    rw [e, div_eq_iff hlam.ne']
    linear_combination hfoc
  · intro ⟨hπ, hline⟩
    refine (static_foc_iff hκ hlam hline).mpr ?_
    have hx : x = (π - β * πe) / κ := by rw [hline]; field_simp; ring
    have e : (1 + κ ^ 2 / lam) * π = ((lam + κ ^ 2) * π) / lam := by field_simp
    rw [eq_inv_mul_iff_mul_eq₀ hd.ne', e, div_eq_iff hlam.ne'] at hπ
    rw [hx]
    field_simp
    linear_combination hπ

/-- Woodford (2003), eq. (1.6), p. 471: discretionary inflation
`πᵉ = κλx*/((1 − β)λ + κ²)`. -/
noncomputable def discretionInflation (β κ lam xs : ℝ) : ℝ := κ * lam * xs / ((1 - β) * lam + κ ^ 2)

/-- Woodford (2003), eq. (1.6), p. 471: rational expectations require `πᵉ` to be a fixed point of
the best response (1.5); the unique fixed point is `κλx*/((1 − β)λ + κ²)`. -/
theorem fixedPoint_iff {β κ lam xs : ℝ} (hβ1 : β < 1) (hlam : 0 < lam) (p : ℝ) :
    p = (1 + κ ^ 2 / lam)⁻¹ * (κ * xs + β * p) ↔ p = discretionInflation β κ lam xs := by
  have hd : 0 < 1 + κ ^ 2 / lam := by positivity
  have hd2 : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith [sq_nonneg κ]
  unfold discretionInflation
  rw [eq_inv_mul_iff_mul_eq₀ hd.ne', eq_div_iff hd2.ne']
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    field_simp
    linear_combination h

/-- Woodford (2003), eq. (1.6), p. 471, and p. 475 (survey E2): discretionary inflation is
positive iff `x* > 0`. -/
theorem discretionInflation_pos_iff {β κ lam xs : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) :
    0 < discretionInflation β κ lam xs ↔ 0 < xs := by
  have hd2 : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith [sq_nonneg κ]
  unfold discretionInflation
  rw [div_pos_iff_of_pos_right hd2]
  constructor
  · intro h; exact pos_of_mul_pos_right h (by positivity)
  · intro h; positivity

/-- Woodford (2003), p. 475 (survey E2): discretionary inflation is zero iff `x* = 0`. -/
theorem discretionInflation_eq_zero_iff {β κ lam xs : ℝ} (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) : discretionInflation β κ lam xs = 0 ↔ xs = 0 := by
  have hd2 : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith [sq_nonneg κ]
  unfold discretionInflation
  rw [div_eq_zero_iff, or_iff_left hd2.ne']
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by positivity)
    · exact h
  · intro h; rw [h, mul_zero]

/-- Woodford (2003), p. 470 and fn. 5 (**Markov equilibrium**, made precise): the continuation
game is the same from every date and has no payoff-relevant state, so a Markov equilibrium is a
time-invariant pair `(pbar, xbar)` such that, with rational expectations `πᵉ = pbar`, the pair
solves the discretionary bank's static problem on the line `π = κx + βπᵉ` in every period. -/
def MarkovEquilibrium (β κ lam xs pbar xbar : ℝ) : Prop :=
  ∃ πe, πe = pbar ∧ StaticOptimal β κ lam xs πe pbar xbar

/-- **Woodford (2003), Proposition 7.1, pp. 471–472** (exact linear-quadratic form): there is a
unique Markov equilibrium; in it inflation is constant at (1.6),
`pbar = κλx*/((1 − β)λ + κ²)`, and the output gap is `xbar = (1 − β)pbar/κ`. -/
theorem prop_7_1 {β κ lam xs : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (pbar xbar : ℝ) :
    MarkovEquilibrium β κ lam xs pbar xbar ↔
      pbar = discretionInflation β κ lam xs ∧ xbar = (1 - β) * pbar / κ := by
  constructor
  · rintro ⟨πe, rfl, h⟩
    obtain ⟨h1, h2⟩ := (staticOptimal_iff hκ.ne' hlam).mp h
    refine ⟨(fixedPoint_iff hβ1 hlam πe).mp h1, ?_⟩
    field_simp
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨pbar, rfl, (staticOptimal_iff hκ.ne' hlam).mpr
      ⟨(fixedPoint_iff hβ1 hlam pbar).mpr h1, ?_⟩⟩
    rw [h2]
    field_simp
    ring

/-- Woodford (2003), Proposition 7.1, pp. 471–472: existence and uniqueness of the Markov
equilibrium. -/
theorem existsUnique_markov {β κ lam xs : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) :
    ∃! p : ℝ × ℝ, MarkovEquilibrium β κ lam xs p.1 p.2 := by
  refine ⟨(discretionInflation β κ lam xs, (1 - β) * discretionInflation β κ lam xs / κ),
    (prop_7_1 hβ1 hκ hlam _ _).mpr ⟨rfl, rfl⟩, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := (prop_7_1 hβ1 hκ hlam _ _).mp hp
  ext
  · exact h1
  · rw [h2, h1]

/-! ### Discretion without imposing time invariance -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), pp. 470–471 (discretionary optimisation, stochastic form): in every period
and state the bank takes expected inflation `E_t π_{t+1}` as given (its action cannot affect
it) and `(π_t, x_t)` solves the static problem on `π_t = κx_t + βE_tπ_{t+1}`; so (1.1) holds. -/
def DiscretionaryEq (β κ lam xs : ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, StaticOptimal β κ lam xs (𝔼.E t (π (t + 1)) ω) (π t ω) (x t ω)

/-- Woodford (2003), Proposition 7.1, pp. 471–472 (**uniqueness without the Markov
restriction**): for `0 ≤ β < 1`, every bounded adapted sequence of period-by-period discretionary
optima has constant inflation (1.6) and constant output gap `(1 − β)πᵉ/κ`, in every state. -/
theorem discretion_unique {β κ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {π x : ℕ → Ω → ℝ} (hπb : BoundedProc π)
    (hd : DiscretionaryEq 𝔼 β κ lam xs π x) :
    (∀ t ω, π t ω = discretionInflation β κ lam xs) ∧
      ∀ t ω, x t ω = (1 - β) * discretionInflation β κ lam xs / κ := by
  have hd1 : 0 < 1 + κ ^ 2 / lam := by positivity
  set a := (1 + κ ^ 2 / lam)⁻¹ * β with ha
  set b := (1 + κ ^ 2 / lam)⁻¹ * (κ * xs) with hb
  have hinv : 0 < (1 + κ ^ 2 / lam)⁻¹ := inv_pos.mpr hd1
  have hinv1 : (1 + κ ^ 2 / lam)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    have : 0 ≤ κ ^ 2 / lam := by positivity
    linarith)
  have hab : |a| < 1 := by
    rw [abs_of_nonneg (mul_nonneg hinv.le hβ0)]
    calc a ≤ 1 * β := mul_le_mul_of_nonneg_right hinv1 hβ0
      _ < 1 := by linarith
  have hrec : ∀ t, π t = a • 𝔼.E t (π (t + 1)) + fun _ => b := by
    intro t
    funext ω
    have h := ((staticOptimal_iff hκ.ne' hlam).mp (hd t ω)).1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, hb]
    rw [h]; ring
  set p := discretionInflation β κ lam xs with hp
  have hfix := (fixedPoint_iff (xs := xs) (κ := κ) hβ1 hlam p).mpr rfl
  have hconst : ∀ t, (fun _ _ => p : ℕ → Ω → ℝ) t =
      a • 𝔼.E t ((fun _ _ => p : ℕ → Ω → ℝ) (t + 1)) + fun _ => b := by
    intro t
    rw [𝔼.const]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, hb]
    conv_lhs => rw [hfix]
    ring
  have heq := 𝔼.forward_unique hab hrec hconst hπb ⟨|p|, fun _ _ => le_rfl⟩
  have hπ : ∀ t ω, π t ω = p := fun t ω => congrFun (congrFun heq t) ω
  refine ⟨hπ, fun t ω => ?_⟩
  have h := ((staticOptimal_iff hκ.ne' hlam).mp (hd t ω)).2
  have hE : 𝔼.E t (π (t + 1)) ω = p := by rw [heq, 𝔼.const]
  rw [hπ, hE] at h
  field_simp
  linarith

/-- Woodford (2003), Proposition 7.1, pp. 471–472 (existence): the constant path with inflation
(1.6) and output gap `(1 − β)πᵉ/κ` is a bounded adapted discretionary equilibrium. -/
theorem discretion_exists {β κ lam xs : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) :
    DiscretionaryEq 𝔼 β κ lam xs (fun _ _ => discretionInflation β κ lam xs)
      (fun _ _ => (1 - β) * discretionInflation β κ lam xs / κ) := by
  intro t ω
  rw [𝔼.const]
  obtain ⟨_, rfl, h⟩ := (prop_7_1 hβ1 hκ hlam (discretionInflation β κ lam xs)
    ((1 - β) * discretionInflation β κ lam xs / κ)).mpr ⟨rfl, rfl⟩
  exact h

end Woodford.GainsFromCommitment.InflationBias
