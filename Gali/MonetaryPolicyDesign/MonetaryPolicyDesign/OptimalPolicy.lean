/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Expectations
import MonetaryPolicyDesign.Distortions
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Optimal monetary policy with an efficient natural allocation

Galí (2015), Chapter 4, §4.3, pp. 102–104, eqs. (4)–(5) and `i_t = r^n_t`.

The non-policy block is the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t` (eq. (7), p. 104, `κ > 0`) and
the DIS `ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (eq. (6), p. 104), stated for an
arbitrary `ExpectationSystem`, so all results hold under perfect foresight and under
uncertainty. The natural rate `r^n` is an arbitrary process.

## Main results

* `zero_equilibrium_iff`: `(ỹ, π) ≡ (0, 0)` is an equilibrium **iff** `i_t = r^n_t` for all
  `t` (eqs. (4), (5) and `i = r^n`, p. 103).
* `infl_zero_of_gap_zero`: (4) ⇒ (5): along an equilibrium with bounded inflation, a closed gap
  implies zero inflation (forward uniqueness, `0 < β < 1`); `gap_zero_of_infl_zero`: (5) ⇒ (4)
  for `κ ≠ 0` (no boundedness needed).
* `divine_coincidence`: along any equilibrium with bounded inflation, `ỹ ≡ 0 ⟺ π ≡ 0`, and
  then `i = r^n`.
* `unbounded_counterexample`: the boundedness requirement cannot be dropped: under perfect
  foresight `ỹ ≡ 0`, `π_t = β^{−t}`, `i_t = r^n_t + β^{−(t+1)}` is an (unbounded) equilibrium.
* `pathLoss_nonneg`, `pathLoss_eq_zero_iff`, `optimal_policy`: for any discounted quadratic
  loss `∑ βᵗ (a ỹ_t² + b π_t²)` with `a, b > 0` (the form of §4.4), the policy `i = r^n`
  attains the minimum (zero) loss, state by state and in expectation, and any equilibrium
  attaining zero loss has `ỹ ≡ π ≡ 0` and `i = r^n`.
* `gap_zero_iff_efficient`: with the optimal subsidy `τ = 1/ε`, natural output is efficient
  output, so `ỹ = log Y − log Yⁿ = 0` iff `Y = A N*^{1−α}` (the link to §§4.1–4.2).
* `no_dispersion_of_price_stability`: in levels, with Calvo pricing and no inherited
  dispersion (`P_{−1}(i) = P_{−1}`, p. 102), a constant price level implies every reset price
  equals the old price level and **all prices stay equal forever** (no relative-price
  distortions).
-/

namespace Gali.MonetaryPolicyDesign.OptimalPolicy

open Filter Topology
open Gali.MonetaryPolicyDesign.Efficient Gali.MonetaryPolicyDesign.Distortions

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (7), p. 104: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (6), p. 104: the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`. -/
def DIS (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), p. 103: an equilibrium of the non-policy block given the interest-rate path
`i`: the NKPC (7) and the DIS (6). -/
def Equilibrium (β σ κ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn

/-- Galí (2015), eqs. (4)–(5) and `i_t = r^n_t`, p. 103: the optimal outcome `ỹ ≡ 0`,
`π ≡ 0` is an equilibrium **iff** the nominal rate tracks the natural rate, `i_t = r^n_t` for
all `t` (`σ ≠ 0`). -/
theorem zero_equilibrium_iff {β σ κ : ℝ} (hσ : σ ≠ 0) (rn i : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ rn 0 0 i ↔ ∀ t, i t = rn t := by
  constructor
  · rintro ⟨-, hd⟩ t
    have h := hd t
    simp only [Pi.zero_apply, map_zero, zero_sub, sub_zero] at h
    have h2 : σ⁻¹ • (i t - rn t) = 0 := by
      have := congrArg Neg.neg h
      simp only [neg_zero, neg_neg] at this
      exact this.symm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (inv_eq_zero.1 h3) hσ
    · exact sub_eq_zero.1 h3
  · intro h
    refine ⟨fun t => by simp, fun t => ?_⟩
    simp [h t]

/-- Galí (2015), eqs. (4) ⇒ (5), p. 103: if the output gap is closed at all times and
inflation is bounded, the NKPC (with `|β| < 1`) forces zero inflation at all times. -/
theorem infl_zero_of_gap_zero {β κ : ℝ} (hβ : |β| < 1) {infl : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ 0 infl) (hb : BoundedProc infl) : infl = 0 := by
  have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
    simp
  refine 𝔼.forward_unique hβ (u := 0) (fun t => ?_) h0 hb ⟨0, fun _ _ => by simp⟩
  rw [hp t]
  simp

/-- Galí (2015), eqs. (5) ⇒ (4), p. 103: if inflation is zero at all times, the NKPC (with
`κ ≠ 0`) forces a closed output gap (no boundedness needed). -/
theorem gap_zero_of_infl_zero {β κ : ℝ} (hκ : κ ≠ 0) {ygap : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ ygap 0) : ygap = 0 := by
  funext t
  have h := hp t
  simp only [Pi.zero_apply, map_zero, smul_zero, zero_add] at h
  rcases smul_eq_zero.1 h.symm with h1 | h1
  · exact absurd h1 hκ
  · exact h1

/-- Galí (2015), p. 103, **the divine coincidence**: along any equilibrium with bounded
inflation (`|β| < 1`, `κ ≠ 0`, `σ ≠ 0`), the output gap is closed at all times **iff**
inflation is zero at all times; and in that case `i_t = r^n_t` for all `t`. -/
theorem divine_coincidence {β σ κ : ℝ} (hβ : |β| < 1) (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (heq : Equilibrium 𝔼 β σ κ rn ygap infl i)
    (hb : BoundedProc infl) :
    (ygap = 0 ↔ infl = 0) ∧ (ygap = 0 → ∀ t, i t = rn t) := by
  have hiff : ygap = 0 ↔ infl = 0 := by
    constructor
    · intro hy
      subst hy
      exact infl_zero_of_gap_zero 𝔼 hβ heq.1 hb
    · intro hπ
      subst hπ
      exact gap_zero_of_infl_zero 𝔼 hκ heq.1
  refine ⟨hiff, fun hy => ?_⟩
  have hπ := hiff.1 hy
  subst hy
  subst hπ
  exact (zero_equilibrium_iff 𝔼 hσ rn i).1 heq

/-- Galí (2015), p. 103: the optimal policy (4)–(5) in the form "price stability implies an
efficient level of output and vice versa": for a bounded equilibrium, `ỹ ≡ 0`, `π ≡ 0` and
`(ỹ, π) ≡ 0` are equivalent, and each forces `i = r^n`; conversely `i = r^n` makes
`(ỹ, π) ≡ 0` an equilibrium. -/
theorem optimal_policy_characterisation {β σ κ : ℝ} (hβ : |β| < 1) (hσ : σ ≠ 0) (hκ : κ ≠ 0)
    {rn ygap infl i : ℕ → Ω → ℝ} (heq : Equilibrium 𝔼 β σ κ rn ygap infl i)
    (hb : BoundedProc infl) :
    (ygap = 0 ↔ ygap = 0 ∧ infl = 0) ∧ (infl = 0 ↔ ygap = 0 ∧ infl = 0) ∧
      (ygap = 0 ∧ infl = 0 → ∀ t, i t = rn t) ∧
      ((∀ t, i t = rn t) → Equilibrium 𝔼 β σ κ rn 0 0 i) := by
  obtain ⟨hiff, hi⟩ := divine_coincidence 𝔼 hβ hσ hκ heq hb
  exact ⟨⟨fun h => ⟨h, hiff.1 h⟩, fun h => h.1⟩, ⟨fun h => ⟨hiff.2 h, h⟩, fun h => h.2⟩,
    fun h => hi h.1, (zero_equilibrium_iff 𝔼 hσ rn i).2⟩

/-- Galí (2015), p. 103 (precision): boundedness cannot be dropped from (4) ⇒ (5). Under
perfect foresight with `0 < β < 1`, `ỹ ≡ 0`, `π_t = β^{−t}` and `i_t = r^n_t + β^{−(t+1)}`
solve the NKPC and the DIS, yet inflation is never zero (and is unbounded). -/
theorem unbounded_counterexample {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (rn : ℕ → Unit → ℝ) :
    Equilibrium perfectForesight β σ κ rn 0 (fun t _ => (β ^ t)⁻¹)
        (fun t u => rn t u + (β ^ (t + 1))⁻¹) ∧
      (∀ t u, (fun t (_ : Unit) => (β ^ t)⁻¹) t u ≠ 0) ∧
      ¬ BoundedProc (fun t (_ : Unit) => (β ^ t)⁻¹) := by
  refine ⟨⟨fun t => funext fun u => ?_, fun t => funext fun u => ?_⟩, fun t u => ?_, ?_⟩
  · simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
      Pi.zero_apply, smul_eq_mul, mul_zero, add_zero, pow_succ, mul_inv]
    field_simp
  · simp only [perfectForesight, LinearMap.id_apply, Pi.zero_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  · exact inv_ne_zero (pow_ne_zero _ hβ0.ne')
  · rintro ⟨M, hM⟩
    have hlim : Tendsto (fun t : ℕ => (β ^ t)⁻¹) atTop atTop := by
      have h := tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hβ0 |>.2 hβ1)
      simpa [inv_pow] using h
    obtain ⟨t, ht⟩ := (hlim.eventually_gt_atTop M).exists
    have := hM t ()
    rw [abs_of_pos (inv_pos.2 (pow_pos hβ0 t))] at this
    linarith

/-! ### The loss function is minimised by the optimal policy -/

/-- Galí (2015), §4.3 and §4.4 (p. 111): the discounted quadratic loss along a state `ω`,
`∑ₜ βᵗ (a ỹ_t² + b π_t²)`. -/
noncomputable def pathLoss (a b β : ℝ) (ygap infl : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' t, β ^ t * (a * ygap t ω ^ 2 + b * infl t ω ^ 2)

omit 𝔼 in
/-- Galí (2015), p. 111: for bounded processes and `0 ≤ β < 1`, the loss series converges. -/
theorem pathLoss_summable {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ygap infl : ℕ → Ω → ℝ} (hy : BoundedProc ygap) (hπ : BoundedProc infl) (ω : Ω) :
    Summable fun t => β ^ t * (a * ygap t ω ^ 2 + b * infl t ω ^ 2) := by
  obtain ⟨M₁, hM₁⟩ := hy
  obtain ⟨M₂, hM₂⟩ := hπ
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0 t)
    (add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _))))
    (fun t => mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hM₁ t ω)).1 (abs_le.1 (hM₁ t ω)).2) ha)
      (mul_le_mul_of_nonneg_left (sq_le_sq' (abs_le.1 (hM₂ t ω)).1 (abs_le.1 (hM₂ t ω)).2) hb))
      (pow_nonneg hβ0 t))
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (a * M₁ ^ 2 + b * M₂ ^ 2))

omit 𝔼 in
/-- Galí (2015), p. 111: the loss is nonnegative (`a, b, β ≥ 0`). -/
theorem pathLoss_nonneg {a b β : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β)
    (ygap infl : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ pathLoss a b β ygap infl ω :=
  tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0 t)
    (add_nonneg (mul_nonneg ha (sq_nonneg _)) (mul_nonneg hb (sq_nonneg _)))

omit 𝔼 in
/-- Galí (2015), p. 103: the outcome `ỹ ≡ π ≡ 0` has zero loss. -/
theorem pathLoss_zero (a b β : ℝ) (ω : Ω) : pathLoss a b β (0 : ℕ → Ω → ℝ) 0 ω = 0 := by
  simp [pathLoss]

omit 𝔼 in
/-- Galí (2015), p. 103: with `a, b, β > 0` and a summable loss, the loss is zero **iff**
`ỹ_t(ω) = π_t(ω) = 0` for all `t`. -/
theorem pathLoss_eq_zero_iff {a b β : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β)
    {ygap infl : ℕ → Ω → ℝ} {ω : Ω}
    (hs : Summable fun t => β ^ t * (a * ygap t ω ^ 2 + b * infl t ω ^ 2)) :
    pathLoss a b β ygap infl ω = 0 ↔ ∀ t, ygap t ω = 0 ∧ infl t ω = 0 := by
  have hnn : ∀ t, 0 ≤ β ^ t * (a * ygap t ω ^ 2 + b * infl t ω ^ 2) := fun t =>
    mul_nonneg (pow_nonneg hβ0.le t)
      (add_nonneg (mul_nonneg ha.le (sq_nonneg _)) (mul_nonneg hb.le (sq_nonneg _)))
  rw [pathLoss, ← hs.hasSum_iff, hasSum_zero_iff_of_nonneg hnn]
  constructor
  · intro h t
    have h1 := congrFun h t
    simp only [Pi.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero _ hβ0.ne')
    · have hy := mul_nonneg ha.le (sq_nonneg (ygap t ω))
      have hπ := mul_nonneg hb.le (sq_nonneg (infl t ω))
      have e1 : a * ygap t ω ^ 2 = 0 := by linarith
      have e2 : b * infl t ω ^ 2 = 0 := by linarith
      exact ⟨pow_eq_zero_iff (n := 2) two_ne_zero |>.1
          ((mul_eq_zero.1 e1).resolve_left ha.ne'),
        pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((mul_eq_zero.1 e2).resolve_left hb.ne')⟩
  · intro h
    funext t
    simp [(h t).1, (h t).2]

/-- Galí (2015), §4.3, pp. 102–103, **the optimal policy**: for any loss `∑ βᵗ (a ỹ² + b π²)`
with `a, b > 0`, `0 < β < 1`: (i) every outcome has nonnegative loss in every state and in
expectation `E_0`; (ii) the rule `i = r^n` supports `ỹ ≡ π ≡ 0`, with zero loss; (iii) any
bounded equilibrium with zero loss in every state has `ỹ ≡ π ≡ 0` and `i = r^n`. -/
theorem optimal_policy {a b β σ κ : ℝ} (ha : 0 < a) (hb : 0 < b) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : σ ≠ 0) (rn : ℕ → Ω → ℝ) :
    (∀ ygap infl : ℕ → Ω → ℝ, (∀ ω, 0 ≤ pathLoss a b β ygap infl ω) ∧
        ∀ ω, 𝔼.E 0 (pathLoss a b β (0 : ℕ → Ω → ℝ) 0) ω
          ≤ 𝔼.E 0 (pathLoss a b β ygap infl) ω) ∧
      Equilibrium 𝔼 β σ κ rn 0 0 rn ∧
      ∀ ygap infl i : ℕ → Ω → ℝ, Equilibrium 𝔼 β σ κ rn ygap infl i →
        BoundedProc ygap → BoundedProc infl → (∀ ω, pathLoss a b β ygap infl ω = 0) →
        ygap = 0 ∧ infl = 0 ∧ ∀ t, i t = rn t := by
  refine ⟨fun ygap infl => ⟨pathLoss_nonneg ha.le hb.le hβ0.le ygap infl, fun ω => ?_⟩,
    (zero_equilibrium_iff 𝔼 hσ rn rn).2 fun _ => rfl, ?_⟩
  · have h0 : pathLoss a b β (0 : ℕ → Ω → ℝ) 0 = fun _ => (0 : ℝ) :=
      funext fun ω => pathLoss_zero a b β ω
    have := 𝔼.mono 0 (pathLoss_nonneg ha.le hb.le hβ0.le ygap infl) ω
    rw [h0]
    simpa [𝔼.const] using this
  · intro ygap infl i heq hy hπ hzero
    have hall : ∀ t ω, ygap t ω = 0 ∧ infl t ω = 0 := fun t ω =>
      ((pathLoss_eq_zero_iff ha hb hβ0
        (pathLoss_summable ha.le hb.le hβ0.le hβ1 hy hπ ω)).1 (hzero ω)) t
    have hy0 : ygap = 0 := funext fun t => funext fun ω => (hall t ω).1
    have hπ0 : infl = 0 := funext fun t => funext fun ω => (hall t ω).2
    refine ⟨hy0, hπ0, ?_⟩
    subst hy0
    subst hπ0
    exact (zero_equilibrium_iff 𝔼 hσ rn i).1 heq

/-! ### Links to the efficient allocation and to price stability in levels -/

/-- Galí (2015), §4.3, p. 102: with the optimal subsidy `τ = 1/ε` the natural (flexible-price)
level of output `Yⁿ = A N(M(1 − τ))^{1−α}` is the efficient level, so the output gap
`ỹ = log Y − log Yⁿ` is zero **iff** `Y = A N*^{1−α}` (efficient output). -/
theorem gap_zero_iff_efficient {σ φ ε α A Y : ℝ} (hε : 1 < ε) (hA : 0 < A) (hα1 : α < 1)
    (hY : 0 < Y) :
    Real.log Y - Real.log (A * flexEmployment σ φ α A (markup ε * (1 - 1 / ε)) ^ (1 - α)) = 0 ↔
      Y = A * effEmployment σ φ α A ^ (1 - α) := by
  rw [optimal_subsidy hε, flexEmployment_one, sub_eq_zero]
  have hYe : 0 < A * effEmployment σ φ α A ^ (1 - α) :=
    mul_pos hA (Real.rpow_pos_of_pos (effEmployment_pos hα1 hA) _)
  exact ⟨fun h => Real.log_injOn_pos hY hYe h, fun h => by rw [h]⟩

omit 𝔼 in
/-- Galí (2015), p. 102, **price stability in levels**: Calvo pricing, where each firm either
keeps its price or resets it to the common `P*_t`, with the price index law
`P_t^{1−ε} = θ P_{t−1}^{1−ε} + (1 − θ) P*_t^{1−ε}` (`0 ≤ θ < 1`, `ε ≠ 1`) and no inherited
dispersion (`P_{−1}(i) = P_{−1}`; date `0` here is the book's `−1`). If the price level is
constant, then every reset price equals the old price level, `P*_t = P_{t−1}`, and all
prices stay equal to `P_{−1}` forever: no relative-price distortions emerge. -/
theorem no_dispersion_of_price_stability {G : Type*} {ε θ : ℝ} (hε : ε ≠ 1) (hθ : θ < 1)
    {Pl Pstar : ℕ → ℝ} {Pi : ℕ → G → ℝ} (hPl : ∀ t, 0 < Pl t) (hPs : ∀ t, 0 < Pstar t)
    (hlaw : ∀ t, Pl (t + 1) ^ (1 - ε) = θ * Pl t ^ (1 - ε) + (1 - θ) * Pstar (t + 1) ^ (1 - ε))
    (hfirm : ∀ t i, Pi (t + 1) i = Pi t i ∨ Pi (t + 1) i = Pstar (t + 1))
    (hinit : ∀ i, Pi 0 i = Pl 0) (hstab : ∀ t, Pl (t + 1) = Pl t) :
    (∀ t, Pl t = Pl 0) ∧ (∀ t, Pstar (t + 1) = Pl t) ∧ ∀ t i, Pi t i = Pl 0 := by
  have hconst : ∀ t, Pl t = Pl 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [hstab t, ih]
  have hne : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.2 (Ne.symm hε)
  have hreset : ∀ t, Pstar (t + 1) = Pl t := by
    intro t
    have h := hlaw t
    rw [hstab t] at h
    have h1 : Pstar (t + 1) ^ (1 - ε) = Pl t ^ (1 - ε) := by
      have h2 : (1 - θ) * Pstar (t + 1) ^ (1 - ε) = (1 - θ) * Pl t ^ (1 - ε) := by linarith
      exact mul_left_cancel₀ (by linarith) h2
    rw [← Real.rpow_rpow_inv (hPs (t + 1)).le hne, h1, Real.rpow_rpow_inv (hPl t).le hne]
  refine ⟨hconst, hreset, fun t => ?_⟩
  induction t with
  | zero => exact hinit
  | succ t ih =>
    intro i
    rcases hfirm t i with h | h
    · rw [h, ih i]
    · rw [h, hreset t, hconst t]

end Gali.MonetaryPolicyDesign.OptimalPolicy
