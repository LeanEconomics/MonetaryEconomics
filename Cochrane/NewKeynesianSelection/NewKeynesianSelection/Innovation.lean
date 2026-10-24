/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.ForwardSolution
import NewKeynesianSelection.ExpectationsFiniteTree

/-!
# Innovations `ΔE_{t+1} = E_{t+1} − E_t`

Cochrane (2023), *The Fiscal Theory of the Price Level*, notation `ΔE_{t+1} ≡ E_{t+1} − E_t`
(§2.4, p. 30), used throughout Chapter 16 (eqs. (16.3), (16.5), (16.7), (16.10), pp. 364–365).
Cochrane writes the new-Keynesian and fiscal-theory models in innovations: unexpected
inflation `ΔE_{t+1} π_{t+1}`, the fiscal shock `ε_{Σs,t+1}`, and the sunspots `δ_{t+1}` with
`E_t δ_{t+1} = 0`. This module provides the innovation operator for an arbitrary
`ExpectationSystem`, so every later result holds under perfect foresight and under genuine
uncertainty. The algebra of `innov` is restated from the Chapter 2 project
(`ExpectationTools`); the decomposition, shock and AR(1) results are new.

## Main results

* `innov` and its algebra: `innov_add`, `innov_sub`, `innov_smul`, `innov_neg`, `innov_const`,
  `innov_of_known`, `innov_eq_sub_E`, `innov_known_next`, `innov_E_succ`, `innov_mul_known`.
* `E_innov_zero`, `E_innov_zero_of_le`: `E_t ΔE_{t+1} x = 0` (innovations are unforecastable).
* The decomposition `x_{t+1} = E_t x_{t+1} + ΔE_{t+1} x_{t+1}` (`eq_E_add_innov`), and its
  uniqueness (`decomposition_unique`): a split into a date-`t` known part and an unforecastable
  part is necessarily this one. `telescope_innov`: `x = E_t x + ∑_{j<n} ΔE_{t+j+1} x` for `x`
  known at `t + n`.
* Shocks (`IsShock`: known at `t + 1`, `E_t ε_{t+1} = 0`): `innov_shock`, `innov_shock_later`,
  `isShock_iff_innov`, `isShock_smul`, `isShock_neg`; the innovation process of any adapted
  process is a shock (`innovProc_isShock`); `adapted_isShock_iff` (an adapted process with
  unforecastable increments is a shock; the notions differ only at date 0).
* AR(1) innovations: `ar1_of_shock` (a process `u_{t+1} = η u_t + ε_{t+1}` driven by a shock is
  `IsAR1 η`), `shock_of_ar1` (conversely the AR(1) residual is a shock and is the innovation),
  `innov_ar1` (`ΔE_{t+1} u_{t+1+j} = ηʲ ε_{t+1}`), `E_ar1_shift` (`E_s u_{t} = η^{t−s} u_s`).
* `innov_tsum`: the innovation of a dominated infinite sum is the sum of the innovations.
* `coinShock_adapted`, `coin_shock_ne_zero`: on the coin-flip event tree a genuinely random
  shock exists.
-/

namespace Cochrane.NewKeynesianSelection.Innovation

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The operator -/

/-- Cochrane (2023), §2.4, p. 30 (notation `ΔE_{t+1} ≡ E_{t+1} − E_t`, used in (16.3), p. 364):
the innovation of `x` between dates `t` and `t + 1`. -/
def innov (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) x - 𝔼.E t x

/-- Cochrane (2023), p. 30: innovations are additive. -/
theorem innov_add (t : ℕ) (x y : Ω → ℝ) : innov 𝔼 t (x + y) = innov 𝔼 t x + innov 𝔼 t y := by
  unfold innov
  rw [map_add, map_add]
  abel

/-- Cochrane (2023), p. 30: innovations commute with subtraction. -/
theorem innov_sub (t : ℕ) (x y : Ω → ℝ) : innov 𝔼 t (x - y) = innov 𝔼 t x - innov 𝔼 t y := by
  unfold innov
  rw [map_sub, map_sub]
  abel

/-- Cochrane (2023), p. 30: innovations are homogeneous. -/
theorem innov_smul (t : ℕ) (c : ℝ) (x : Ω → ℝ) : innov 𝔼 t (c • x) = c • innov 𝔼 t x := by
  unfold innov
  rw [map_smul, map_smul, smul_sub]

/-- Cochrane (2023), p. 30: the innovation of a negative. -/
theorem innov_neg (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t (-x) = -innov 𝔼 t x := by
  unfold innov
  rw [map_neg, map_neg]
  abel

/-- Cochrane (2023), p. 30: constants have no innovation. -/
theorem innov_const (t : ℕ) (c : ℝ) : innov 𝔼 t (fun _ => c) = 0 := by
  unfold innov
  rw [𝔼.const, 𝔼.const, sub_self]

/-- Cochrane (2023), p. 30: a variable known at date `t` has no date-`t + 1` innovation. -/
theorem innov_of_known {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E t x = x) : innov 𝔼 t x = 0 := by
  unfold innov
  rw [ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) hx, hx, sub_self]

/-- Cochrane (2023), p. 30 and (16.5), p. 364 ("you can't expect future unexpected shocks"):
`E_t(ΔE_{t+1} x) = 0`. -/
theorem E_innov_zero (t : ℕ) (x : Ω → ℝ) : 𝔼.E t (innov 𝔼 t x) = 0 := by
  unfold innov
  rw [map_sub, 𝔼.tower (Nat.le_succ t), 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), p. 30: an earlier expectation of a later innovation is zero,
`E_s(ΔE_{t+1} x) = 0` for `s ≤ t`. -/
theorem E_innov_zero_of_le {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : 𝔼.E s (innov 𝔼 t x) = 0 := by
  rw [← 𝔼.tower hst, E_innov_zero, map_zero]

/-- Cochrane (2023), (16.3), p. 364: for `x` known at `t + 1`,
`ΔE_{t+1} x = x − E_t x` (the unexpected part of `x`). -/
theorem innov_eq_sub_E {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    innov 𝔼 t x = x - 𝔼.E t x := by
  rw [innov, hx]

/-- Cochrane (2023), p. 30: the date-`t + 1` innovation is known at date `t + 1`. -/
theorem innov_known_next (t : ℕ) (x : Ω → ℝ) : 𝔼.E (t + 1) (innov 𝔼 t x) = innov 𝔼 t x := by
  unfold innov
  rw [map_sub, 𝔼.E_E_self, 𝔼.known (Nat.le_succ t)]

/-- Cochrane (2023), p. 30: the innovation of `E_{t+1} x` is the innovation of `x`. -/
theorem innov_E_succ (t : ℕ) (x : Ω → ℝ) : innov 𝔼 t (𝔼.E (t + 1) x) = innov 𝔼 t x := by
  unfold innov
  rw [𝔼.E_E_self, 𝔼.tower (Nat.le_succ t)]

/-- Cochrane (2023), p. 30 (pull-out): a factor known at date `t` comes out of the innovation,
`ΔE_{t+1}(a y) = a ΔE_{t+1} y`. -/
theorem innov_mul_known (hPO : 𝔼.PullOut) {t : ℕ} {a : Ω → ℝ} (ha : 𝔼.E t a = a)
    (y : Ω → ℝ) : innov 𝔼 t (a * y) = a * innov 𝔼 t y := by
  unfold innov
  rw [hPO (t + 1) a y (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ha), hPO t a y ha, mul_sub]

/-! ### The decomposition into expected and unexpected parts -/

/-- Cochrane (2023), p. 35 and (16.5), p. 364 (`π_{t+1} = E_t π_{t+1} + ΔE_{t+1} π_{t+1}`): any
random variable known at `t + 1` is its forecast plus its innovation. -/
theorem eq_E_add_innov {t : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    x = 𝔼.E t x + innov 𝔼 t x := by
  unfold innov
  rw [hx]
  abel

/-- Cochrane (2023), (16.5), p. 364: the decomposition is unique. If `x = a + d` with `a` known
at `t` and `E_t d = 0`, then `a = E_t x` and, when `x` is known at `t + 1`, `d = ΔE_{t+1} x`. -/
theorem decomposition_unique {t : ℕ} {x a d : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x)
    (ha : 𝔼.E t a = a) (hd : 𝔼.E t d = 0) (hsplit : x = a + d) :
    a = 𝔼.E t x ∧ d = innov 𝔼 t x := by
  have hEa : 𝔼.E t x = a := by rw [hsplit, map_add, ha, hd, add_zero]
  refine ⟨hEa.symm, ?_⟩
  unfold innov
  rw [hx, hEa, hsplit]
  abel

/-- Cochrane (2023), p. 30 (iterating `ΔE`): a variable known at `t + n` is its date-`t`
forecast plus the sum of the `n` innovations from `t + 1` to `t + n`,
`x = E_t x + ∑_{j<n} ΔE_{t+j+1} x`. -/
theorem telescope_innov {t n : ℕ} {x : Ω → ℝ} (hx : 𝔼.E (t + n) x = x) :
    x = 𝔼.E t x + ∑ j ∈ Finset.range n, innov 𝔼 (t + j) x := by
  have key : ∀ m, 𝔼.E (t + m) x = 𝔼.E t x + ∑ j ∈ Finset.range m, innov 𝔼 (t + j) x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← add_assoc (𝔼.E t x), ← ih, ← add_assoc t m 1]
      unfold innov
      abel
  rw [← key n, hx]

/-! ### Shocks -/

/-- Cochrane (2023), p. 40 (terminology: a "shock" only moves unexpectedly) and (16.5), p. 364
(`E_t δ_{t+1} = 0`): `ε_{t+1}` is known at `t + 1` and `E_t ε_{t+1} = 0`. The date-0 value is
irrelevant. -/
def IsShock (ε : ℕ → Ω → ℝ) : Prop :=
  (∀ t, 𝔼.E (t + 1) (ε (t + 1)) = ε (t + 1)) ∧ ∀ t, 𝔼.E t (ε (t + 1)) = 0

/-- Cochrane (2023), p. 40: a shock's innovation on arrival is the shock itself,
`ΔE_{t+1} ε_{t+1} = ε_{t+1}`. -/
theorem innov_shock {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (t : ℕ) :
    innov 𝔼 t (ε (t + 1)) = ε (t + 1) := by
  unfold innov
  rw [hε.1 t, hε.2 t, sub_zero]

/-- Cochrane (2023), p. 40: a later shock has no innovation at an earlier date,
`ΔE_{t+1} ε_{t+2+j} = 0`. -/
theorem innov_shock_later {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (t j : ℕ) :
    innov 𝔼 t (ε (t + 2 + j)) = 0 := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e]
  unfold innov
  rw [← 𝔼.tower (show t + 1 ≤ t + 1 + j by omega), hε.2, map_zero,
    ← 𝔼.tower (show t ≤ t + 1 + j by omega), hε.2, map_zero, sub_zero]

/-- Cochrane (2023), (16.5), p. 364: a shock has zero forecast at every earlier date,
`E_s ε_{t+1} = 0` for `s ≤ t`. -/
theorem E_shock_of_le {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (ε (t + 1)) = 0 := by
  rw [← 𝔼.tower hst, hε.2 t, map_zero]

/-- Cochrane (2023), (16.5), p. 364: a process known at `t + 1` is a shock iff it equals its own
innovation at every date. -/
theorem isShock_iff_innov {ε : ℕ → Ω → ℝ} (hk : ∀ t, 𝔼.E (t + 1) (ε (t + 1)) = ε (t + 1)) :
    IsShock 𝔼 ε ↔ ∀ t, innov 𝔼 t (ε (t + 1)) = ε (t + 1) := by
  constructor
  · exact fun h t => innov_shock 𝔼 h t
  · intro h
    refine ⟨hk, fun t => ?_⟩
    rw [← h t, E_innov_zero]

/-- Cochrane (2023), (16.5), p. 364: the innovation process `ν_0 = 0`,
`ν_{t+1} = ΔE_{t+1} x_{t+1}` of a process `x`. -/
def innovProc (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => innov 𝔼 t (x (t + 1))

/-- Cochrane (2023), (16.5), p. 364: the innovation process of any process is a shock. -/
theorem innovProc_isShock (x : ℕ → Ω → ℝ) : IsShock 𝔼 (innovProc 𝔼 x) :=
  ⟨fun t => innov_known_next 𝔼 t (x (t + 1)), fun t => E_innov_zero 𝔼 t (x (t + 1))⟩

/-- Cochrane (2023), (16.5), p. 364: an adapted process is its own forecast plus its innovation
process, `x_{t+1} = E_t x_{t+1} + ν_{t+1}`. -/
theorem eq_E_add_innovProc {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (t : ℕ) :
    x (t + 1) = 𝔼.E t (x (t + 1)) + innovProc 𝔼 x (t + 1) :=
  eq_E_add_innov 𝔼 (hx (t + 1))

/-- Cochrane (2023), (16.5), p. 364: shocks are closed under linear combinations. -/
theorem isShock_lin {ε ν : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (hν : IsShock 𝔼 ν) (a b : ℝ) :
    IsShock 𝔼 (fun t => a • ε t + b • ν t) :=
  ⟨fun t => by simp only [map_add, map_smul, hε.1 t, hν.1 t],
    fun t => by simp only [map_add, map_smul, hε.2 t, hν.2 t, smul_zero, add_zero]⟩

/-- Cochrane (2023), (16.5), p. 364: a rescaled shock is a shock. -/
theorem isShock_smul {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) (c : ℝ) :
    IsShock 𝔼 (fun t => c • ε t) :=
  ⟨fun t => by simp only [map_smul, hε.1 t], fun t => by simp only [map_smul, hε.2 t, smul_zero]⟩

/-- Cochrane (2023), (16.5), p. 364: the negative of a shock is a shock. -/
theorem isShock_neg {ε : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε) : IsShock 𝔼 (fun t => -ε t) :=
  ⟨fun t => by rw [map_neg, hε.1 t], fun t => by rw [map_neg, hε.2 t, neg_zero]⟩

/-- Cochrane (2023), p. 365 (a shock as an adapted process with `E_t ε_{t+1} = 0`): an adapted
process with unforecastable increments is a shock in the sense of `IsShock`, and the two notions
differ only by the irrelevant date-0 measurability of `ε_0`. -/
theorem adapted_isShock_iff {ε : ℕ → Ω → ℝ} :
    (𝔼.Adapted ε ∧ ∀ t, 𝔼.E t (ε (t + 1)) = 0) ↔ IsShock 𝔼 ε ∧ 𝔼.E 0 (ε 0) = ε 0 := by
  constructor
  · rintro ⟨ha, h0⟩
    exact ⟨⟨fun t => ha (t + 1), h0⟩, ha 0⟩
  · rintro ⟨hs, h0⟩
    refine ⟨fun t => ?_, hs.2⟩
    cases t with
    | zero => exact h0
    | succ t => exact hs.1 t

/-- Cochrane (2023), (16.5), p. 364: the zero process is a shock. -/
theorem isShock_zero : IsShock 𝔼 (0 : ℕ → Ω → ℝ) :=
  ⟨fun _ => map_zero _, fun _ => map_zero _⟩

/-! ### AR(1) innovations -/

/-- Cochrane (2023), p. 364 (`u_t = η u_{t−1} + ε_t`) and p. 365 (`u_{t+1} = η u_t + ε_{i,t+1}`):
the AR(1) law of motion driven by `ε`. -/
def AR1Law (η : ℝ) (u ε : ℕ → Ω → ℝ) : Prop := ∀ t, u (t + 1) = η • u t + ε (t + 1)

/-- Cochrane (2023), p. 364: an adapted process following the AR(1) law with shock innovations
satisfies `E_t u_{t+1} = η u_t`, i.e. is `IsAR1 η`. -/
theorem ar1_of_shock {η : ℝ} {u ε : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε)
    (hlaw : AR1Law η u ε) : 𝔼.IsAR1 η u :=
  ⟨hu, fun t => by rw [hlaw t, map_add, map_smul, hu t, hε.2 t, add_zero]⟩

/-- Cochrane (2023), p. 364: conversely, for `IsAR1 η u` the residual
`ε_{t+1} = u_{t+1} − η u_t` is a shock, it satisfies the AR(1) law, and it is the innovation
`ΔE_{t+1} u_{t+1}`. -/
theorem shock_of_ar1 {η : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) :
    IsShock 𝔼 (fun t => u t - η • u (t - 1)) ∧ AR1Law η u (fun t => u t - η • u (t - 1)) ∧
      ∀ t, innov 𝔼 t (u (t + 1)) = u (t + 1) - η • u t := by
  have hk : ∀ t, 𝔼.E (t + 1) (u t) = u t := fun t =>
    ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hu.1 t)
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, fun t => ?_⟩
  · simp only [Nat.add_sub_cancel, map_sub, map_smul, hu.1 (t + 1), hk t]
  · simp only [Nat.add_sub_cancel, map_sub, map_smul, hu.2 t, hu.1 t, sub_self]
  · simp only [Nat.add_sub_cancel]
    abel
  · unfold innov
    rw [hu.1 (t + 1), hu.2 t]

/-- Cochrane (2023), p. 365 and Figure 16.1 (the response of the disturbance to `ε_{i,t+1}`):
`ΔE_{t+1} u_{t+1+j} = ηʲ ε_{t+1}`. -/
theorem innov_ar1 {η : ℝ} {u ε : ℕ → Ω → ℝ} (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε)
    (hlaw : AR1Law η u ε) (t j : ℕ) : innov 𝔼 t (u (t + 1 + j)) = η ^ j • ε (t + 1) := by
  induction j with
  | zero =>
    rw [add_zero, hlaw t, innov_add, innov_smul, innov_of_known 𝔼 (hu t), innov_shock 𝔼 hε,
      smul_zero, zero_add, pow_zero, one_smul]
  | succ j ih =>
    rw [show t + 1 + (j + 1) = t + 1 + j + 1 by omega, hlaw, innov_add, innov_smul, ih,
      show t + 1 + j + 1 = t + 2 + j by omega, innov_shock_later 𝔼 hε, add_zero, smul_smul,
      pow_succ, mul_comm η]

/-- Cochrane (2023), p. 364: forecasts of an AR(1) at every horizon, `E_s u_{s+k} = ηᵏ u_s`
(restating `ExpectationSystem.ar1_iterate`), so the date-`s` forecast of `u_t` is
`η^{t−s} u_s` for `s ≤ t`. -/
theorem E_ar1_shift {η : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (u t) = η ^ (t - s) • u s := by
  have := 𝔼.ar1_iterate hu s (t - s)
  rwa [Nat.add_sub_cancel' hst] at this

/-! ### Innovations of infinite sums -/

/-- Cochrane (2023), eq. (2.17), p. 35, and (16.3), p. 364 (the fiscal shock is the innovation in
a present value): the innovation of a dominated infinite sum of random variables is the sum of
the innovations, `ΔE_{t+1} ∑ₖ fₖ = ∑ₖ ΔE_{t+1} fₖ`, for `|fₖ| ≤ cₖ` with `∑ cₖ < ∞`. -/
theorem innov_tsum {c : ℕ → ℝ} (hc : Summable c) {f : ℕ → Ω → ℝ} (hf : ∀ k ω, |f k ω| ≤ c k)
    (t : ℕ) (ω : Ω) :
    innov 𝔼 t (fun ω' => ∑' k, f k ω') ω = ∑' k, innov 𝔼 t (f k) ω := by
  unfold innov
  rw [Pi.sub_apply, ForwardSolution.E_tsum_dom 𝔼 hc hf (t + 1) ω,
    ForwardSolution.E_tsum_dom 𝔼 hc hf t ω]
  have h1 : Summable (fun k => 𝔼.E (t + 1) (f k) ω) :=
    Summable.of_norm_bounded hc (fun k => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) (t + 1) ω)
  have h2 : Summable (fun k => 𝔼.E t (f k) ω) :=
    Summable.of_norm_bounded hc (fun k => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hf k) t ω)
  rw [← h1.tsum_sub h2]
  rfl

/-! ### Genuine uncertainty -/

/-- Cochrane (2023), p. 364 and p. 373 (uncertainty examples): the coin-flip shock is adapted on
the coin-flip event tree. -/
theorem coinShock_adapted :
    ExpectationsFiniteTree.coinSystem.Adapted ExpectationsFiniteTree.coinShock := by
  intro t
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
    ExpectationsFiniteTree.coinShock_measurable t h

/-- Cochrane (2023), (16.5), p. 364 ("sunspot shocks `δ_{t+1}` can erupt at any time"): on the
coin-flip event tree the coin shock is a shock in the sense of `IsShock` and it is not
identically zero, so shocks are not restricted to perfect foresight. -/
theorem coin_shock_ne_zero :
    IsShock ExpectationsFiniteTree.coinSystem ExpectationsFiniteTree.coinShock ∧
      ExpectationsFiniteTree.coinShock 1 ≠ 0 := by
  refine ⟨⟨fun t => coinShock_adapted (t + 1), ExpectationsFiniteTree.coinShock_mean_zero⟩,
    fun h => ?_⟩
  have := congrFun h (true, true)
  simp [ExpectationsFiniteTree.coinShock] at this

end Cochrane.NewKeynesianSelection.Innovation
