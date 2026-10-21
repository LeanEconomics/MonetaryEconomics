/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.ObservationalEquivalence

/-!
# Responses in the simplest new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 16, §16.7 "Responses"
(pp. 374–377).

All results hold for an arbitrary `ExpectationSystem`; the response examples are pathwise
(along any history `ω` with the stated shocks), and each is shown to be non-vacuous on the
coin-flip event tree, where the shock at date 1 is genuinely unexpected.

## Main results

* (16.13) with `η = 0` (p. 374): `u_shock_eq_target` — a shock `u_1 = 1` is a target
  `π*_1 = −1/φ`; `king_iff_nk` (the two forms of the rule).
* Alternative paths (p. 374): `alt_paths`
  `E_s π_{s+k} = −ηᵏ u_s/(φ − η) + φᵏ (π_s + u_s/(φ − η))` for every solution;
  `alt_paths_explode` (`|E_s π_{s+k}| → ∞` unless `π_s = −u_s/(φ − η)`),
  `nonExplosive_iff` (the non-explosive solution is exactly (16.9), with no uniform bound on
  `u`, so it covers `η = 1`).
* Fisherian responses (pp. 374–375): `real_rate_zero`, `expected_follows_rate`
  (`E_t π_{t+j+1} = E_t i_{t+j}`, p. 376), `fisherian_sign`, `impulse_path`,
  `impact_signs` (inflation and the interest rate fall on impact although `u_1 > 0`; the fall
  is entirely unexpected).
* Super-Fisherian (p. 375): `super_fisherian`, `super_fisherian_coin`; open-mouth (p. 375,
  survey error E5 is a typo only): `open_mouth`, `open_mouth_price_jump`, `open_mouth_coin`.
* The rule `i_t = φ E_t π_{t+1}` (p. 376): `ruleExp_trivial` (for `φ ≠ 1` every equilibrium
  has `E_t π_{t+1} = i_t = 0`), `ruleExp_solutions`, `ruleExp_has_solution` (so the printed
  "has no solution" is imprecise), `ruleExp_disturbance`.
* The fiscal requirement (pp. 376–377): `no_fiscal_no_surprise`, `nk3_ar1_fiscal_iff`,
  `no_eq_without_fiscal`, `disinflation_iff_contraction`.
-/

namespace Cochrane.NewKeynesianSelection.Responses

open Filter Topology Cochrane.NewKeynesianSelection.Identification
open Innovation (innov IsShock innov_eq_sub_E adapted_isShock_iff coinShock_adapted)
open SimplestModel (Eq164 ar1Pi ar1Pi_eq164)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The two forms of the rule and `u_1 = 1` as a target -/

/-- Cochrane (2023), (16.12)–(16.13), pp. 366–367: the rule `i_t = i*_t + φ(π_t − π*_t)` is the
rule `i_t = φ π_t + u_t` with `u_t = i*_t − φ π*_t`. -/
theorem king_iff_nk (φ : ℝ) (istar pistar π i : ℕ → Ω → ℝ) :
    KingEq 𝔼 φ istar pistar π i ↔ NKEq 𝔼 φ (fun t => istar t - φ • pistar t) π i := by
  unfold KingEq NKEq
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun t => ?_
  constructor <;> intro h <;> rw [h] <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Cochrane (2023), p. 374 ("From (16.13), the `u_1 = 1` shock is the same thing as a
`π*_1 = −1/φ` shock"): with a serially uncorrelated disturbance (`η = 0`) the target is
`π* = −u/φ`; it satisfies (16.13) `u_t = E_t π*_{t+1} − φ π*_t`, and `π*_t = −1/φ` exactly
where `u_t = 1`. -/
theorem u_shock_eq_target {φ : ℝ} (hφ : φ ≠ 0) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 0 u ε) (t : ℕ)
    (ω : Ω) :
    u t = 𝔼.E t (ar1Pi φ 0 u (t + 1)) - φ • ar1Pi φ 0 u t ∧
      (ar1Pi φ 0 u t ω = -1 / φ ↔ u t ω = 1) := by
  refine ⟨?_, ?_⟩
  · rw [ar1Pi_eq164 𝔼 hφ (h.isAR1 𝔼) t]
    abel
  · simp only [ar1Pi, sub_zero, Pi.smul_apply, smul_eq_mul]
    constructor
    · intro e
      field_simp at e
      linarith
    · intro e
      rw [e]
      field_simp

/-! ### Alternative paths and explosions (p. 374) -/

/-- Cochrane (2023), p. 374: every adapted solution of (16.4) with an AR(1) disturbance
satisfies `E_s π_{s+k} = −ηᵏ u_s/(φ − η) + φᵏ (π_s + u_s/(φ − η))` (the book's display with
`s = 1`, `k = t`). -/
theorem alt_paths {φ η : ℝ} (hφη : φ ≠ η) {u ε π : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε)
    (ha : 𝔼.Adapted π) (hπ : Eq164 𝔼 φ u π) (s k : ℕ) :
    𝔼.E s (π (s + k)) =
      (-(η ^ k * (φ - η)⁻¹)) • u s + φ ^ k • (π s + (φ - η)⁻¹ • u s) := by
  have hne : φ - η ≠ 0 := sub_ne_zero.mpr hφη
  set c := (φ - η)⁻¹ with hc
  set d : ℕ → Ω → ℝ := fun t => π t + c • u t with hd
  have hdd : ∀ t, 𝔼.E t (d (t + 1)) = φ • d t := by
    intro t
    simp only [hd, map_add, map_smul, hπ t, h.E_succ 𝔼 t, smul_add, smul_smul]
    have : c * η = φ * c - 1 := by rw [hc]; field_simp; ring
    rw [this, sub_smul, one_smul]
    abel
  have hiter : ∀ k, 𝔼.E s (d (s + k)) = φ ^ k • d s := by
    intro k
    induction k with
    | zero => simp only [hd, add_zero, pow_zero, one_smul, map_add, map_smul, ha s, h.1 s]
    | succ k ih =>
      rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right s k), hdd, map_smul, ih, smul_smul,
        pow_succ, mul_comm]
  have hu : ∀ k, 𝔼.E s (u (s + k)) = η ^ k • u s :=
    𝔼.ar1_iterate ⟨h.1, h.E_succ 𝔼⟩ s
  have e := hiter k
  simp only [hd, map_add, map_smul, hu k, smul_smul] at e
  rw [show 𝔼.E s (π (s + k)) = φ ^ k • (π s + c • u s) - (c * η ^ k) • u s by rw [← e]; abel]
  rw [neg_smul, sub_eq_add_neg, add_comm, mul_comm]

/-- Cochrane (2023), p. 364: a solution is non-explosive if, at every date and state, its
expected future path `k ↦ |E_s π_{s+k}|` is bounded. -/
def NonExplosive (π : ℕ → Ω → ℝ) : Prop :=
  ∀ s ω, BddAbove (Set.range fun k => |𝔼.E s (π (s + k)) ω|)

/-- Cochrane (2023), p. 374 ("Inflation explodes for any value of `π_1` but one"): for
`|φ| > 1 ≥ |η|`, if `π_s ≠ −u_s/(φ − η)` at a state, then `|E_s π_{s+k}| → ∞` there. -/
theorem alt_paths_explode {φ η : ℝ} (hφ : 1 < |φ|) (hη : |η| ≤ 1) (hφη : φ ≠ η)
    {u ε π : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ha : 𝔼.Adapted π) (hπ : Eq164 𝔼 φ u π) {s : ℕ}
    {ω : Ω} (hd : π s ω ≠ ar1Pi φ η u s ω) :
    Tendsto (fun k => |𝔼.E s (π (s + k)) ω|) atTop atTop := by
  have hD0 : π s ω + (φ - η)⁻¹ * u s ω ≠ 0 := by
    intro h0
    apply hd
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul]
    linarith
  have hlow : ∀ k, |φ| ^ k * |π s ω + (φ - η)⁻¹ * u s ω| - |(φ - η)⁻¹ * u s ω| ≤
      |𝔼.E s (π (s + k)) ω| := by
    intro k
    rw [alt_paths 𝔼 hφη h ha hπ s k]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    set A := φ ^ k * (π s ω + (φ - η)⁻¹ * u s ω) with hA
    set B := -(η ^ k * (φ - η)⁻¹) * u s ω with hB
    have h1 : |B| ≤ |(φ - η)⁻¹ * u s ω| := by
      rw [hB, abs_mul, abs_neg, abs_mul, abs_pow, abs_mul]
      have : |η| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg η) hη
      nlinarith [abs_nonneg (φ - η)⁻¹, abs_nonneg (u s ω),
        mul_nonneg (abs_nonneg (φ - η)⁻¹) (abs_nonneg (u s ω))]
    have h2 : |A| = |φ| ^ k * |π s ω + (φ - η)⁻¹ * u s ω| := by rw [hA, abs_mul, abs_pow]
    have h3 := abs_sub_abs_le_abs_sub A (-B)
    rw [abs_neg, sub_neg_eq_add, add_comm] at h3
    linarith
  have hT : Tendsto (fun k : ℕ => |φ| ^ k * |π s ω + (φ - η)⁻¹ * u s ω|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const (abs_pos.mpr hD0)
  exact tendsto_atTop_mono hlow (by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-|(φ - η)⁻¹ * u s ω|) hT)

/-- Cochrane (2023), pp. 364, 374: for `|φ| > 1 ≥ |η|` and `φ ≠ η`, an adapted solution of
(16.4) is non-explosive iff it is (16.9) `π = −u/(φ − η)`. No uniform bound on `u` is needed,
so this covers the random-walk case `η = 1` of the super-Fisherian response. -/
theorem nonExplosive_iff {φ η : ℝ} (hφ : 1 < |φ|) (hη : |η| ≤ 1) (hφη : φ ≠ η)
    {u ε π : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) (ha : 𝔼.Adapted π) (hπ : Eq164 𝔼 φ u π) :
    NonExplosive 𝔼 π ↔ π = ar1Pi φ η u := by
  constructor
  · intro hne
    funext s ω
    by_contra hd
    exact not_bddAbove_of_tendsto_atTop (alt_paths_explode 𝔼 hφ hη hφη h ha hπ hd) (hne s ω)
  · rintro rfl s ω
    refine ⟨|(φ - η)⁻¹ * u s ω|, ?_⟩
    rintro _ ⟨k, rfl⟩
    change |𝔼.E s (ar1Pi φ η u (s + k)) ω| ≤ _
    rw [alt_paths 𝔼 hφη h ha hπ s k]
    simp only [ar1Pi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul, neg_add_cancel,
      mul_zero, add_zero]
    rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_pow, mul_assoc]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (abs_nonneg η) hη)

/-! ### Fisherian responses (pp. 374–376) -/

/-- Cochrane (2023), p. 374 ("The model is Fisherian `i_t = E_t π_{t+1}` throughout"): the
ex-ante real rate is identically zero in every equilibrium. -/
theorem real_rate_zero {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) (t : ℕ) :
    i t - 𝔼.E t (π (t + 1)) = 0 := by
  rw [h.2.1 t, sub_self]

/-- Cochrane (2023), p. 376 ("`E_t π_{t+1} = i_t` so `E_t π_{t+j+1} = E_t i_{t+j}`"):
anticipated interest rates move expected inflation one for one with a one-period lag. -/
theorem expected_follows_rate {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NKEq 𝔼 φ u π i) (t j : ℕ) :
    𝔼.E t (π (t + j + 1)) = 𝔼.E t (i (t + j)) := by
  rw [h.2.1 (t + j), 𝔼.tower (Nat.le_add_right t j)]

/-- Cochrane (2023), p. 375 ("Someone observing data from this economy would see interest
rates and inflation always moving in the same direction"): in the selected AR(1) equilibrium
with `η ≥ 0`, `i_t π_t ≥ 0` at every date and state. -/
theorem fisherian_sign (φ : ℝ) {η : ℝ} (hη : 0 ≤ η) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε)
    (t : ℕ) (ω : Ω) : 0 ≤ fisherRate 𝔼 (ar1Pi φ η u) t ω * ar1Pi φ η u t ω := by
  rw [(eq_16_15 𝔼 φ h t).1, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact mul_nonneg hη (mul_self_nonneg _)

/-- Cochrane (2023), Figure 16.1 and p. 374: the response to a monetary shock `ε_1` from the
steady state `u_0 = 0` with no later shocks: `π_{k+1} = −ηᵏ ε_1/(φ − η)` and
`i_{k+1} = −η^{k+1} ε_1/(φ − η)`. -/
theorem impulse_path (φ : ℝ) {η : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) {ω : Ω}
    (hu0 : u 0 ω = 0) (hε : ∀ k, ε (k + 2) ω = 0) (k : ℕ) :
    ar1Pi φ η u (k + 1) ω = -(η ^ k * ε 1 ω / (φ - η)) ∧
      fisherRate 𝔼 (ar1Pi φ η u) (k + 1) ω = -(η ^ (k + 1) * ε 1 ω / (φ - η)) := by
  have hu : ∀ k, u (k + 1) ω = η ^ k * ε 1 ω := by
    intro k
    induction k with
    | zero =>
      have := congrFun (h.2.2 0) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu0, mul_zero, zero_add] at this
      rw [this, pow_zero, one_mul]
    | succ k ih =>
      have := congrFun (h.2.2 (k + 1)) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ih, hε k, add_zero] at this
      rw [this, pow_succ]
      ring
  have hπ : ar1Pi φ η u (k + 1) ω = -(η ^ k * ε 1 ω / (φ - η)) := by
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul, hu k]
    ring
  refine ⟨hπ, ?_⟩
  rw [(eq_16_15 𝔼 φ h (k + 1)).1, Pi.smul_apply, smul_eq_mul, hπ]
  ring

/-- Cochrane (2023), pp. 374–375: on a positive monetary-policy shock `ε_1 > 0` from the
steady state, with `φ > η > 0`: the disturbance rises (`u_1 > 0`), yet inflation and the
observed interest rate fall on impact (`π_1 < 0`, `i_1 = φπ_1 + u_1 < 0`, the endogenous part
`φπ_1` overwhelming `u_1`), and the inflation decline is entirely unexpected (`E_0 π_1 = 0`,
so `π_1 = ΔE_1 π_1`). -/
theorem impact_signs {φ η : ℝ} (hη : 0 < η) (hφη : η < φ) {u ε : ℕ → Ω → ℝ}
    (h : AR1 𝔼 η u ε) {ω : Ω} (hu0 : u 0 ω = 0) (hε : 0 < ε 1 ω) :
    0 < u 1 ω ∧ ar1Pi φ η u 1 ω < 0 ∧ fisherRate 𝔼 (ar1Pi φ η u) 1 ω < 0 ∧
      φ * ar1Pi φ η u 1 ω + u 1 ω < 0 ∧ 𝔼.E 0 (ar1Pi φ η u 1) ω = 0 ∧
      innov 𝔼 0 (ar1Pi φ η u 1) ω = ar1Pi φ η u 1 ω := by
  have hpos : 0 < φ - η := by linarith
  have hu1 : u 1 ω = ε 1 ω := by
    have := congrFun (h.2.2 0) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu0, mul_zero, zero_add] at this
    exact this
  have hπ1 : ar1Pi φ η u 1 ω = -(ε 1 ω / (φ - η)) := by
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul, hu1]
    ring
  have hE0 : 𝔼.E 0 (ar1Pi φ η u 1) ω = 0 := by
    change fisherRate 𝔼 (ar1Pi φ η u) 0 ω = 0
    rw [(eq_16_15 𝔼 φ h 0).1]
    simp [ar1Pi, hu0]
  have hi1 : fisherRate 𝔼 (ar1Pi φ η u) 1 ω = η * ar1Pi φ η u 1 ω := by
    rw [(eq_16_15 𝔼 φ h 1).1, Pi.smul_apply, smul_eq_mul]
  have hq : 0 < ε 1 ω / (φ - η) := div_pos hε hpos
  refine ⟨by rw [hu1]; exact hε, by rw [hπ1]; linarith, ?_, ?_, hE0, ?_⟩
  · rw [hi1, hπ1]; nlinarith
  · rw [hπ1, hu1]
    have : φ * -(ε 1 ω / (φ - η)) + ε 1 ω = -(η * (ε 1 ω / (φ - η))) := by
      field_simp
      ring
    rw [this]
    nlinarith
  · have had : 𝔼.Adapted (ar1Pi φ η u) := fun s => by simp only [ar1Pi, map_smul, h.1 s]
    rw [innov_eq_sub_E 𝔼 (had 1), Pi.sub_apply, hE0, sub_zero]

/-! ### Super-Fisherian and open-mouth responses (p. 375) -/

/-- Cochrane (2023), p. 375 (super-Fisherian response): with `η = 1` and the shock
`ε_1 = u_1 = 1 − φ` (so `u_t = 1 − φ` for `t ≥ 1` along `ω`), the non-explosive equilibrium has
`π_t = i_t = 1` for all `t ≥ 1`: interest rates and inflation rise together, immediately and
permanently. -/
theorem super_fisherian {φ : ℝ} (hφ : 1 < |φ|) {u ε π : ℕ → Ω → ℝ} (h : AR1 𝔼 1 u ε)
    (ha : 𝔼.Adapted π) (hπ : Eq164 𝔼 φ u π) (hne : NonExplosive 𝔼 π) {ω : Ω}
    (hu : ∀ t, u (t + 1) ω = 1 - φ) (t : ℕ) :
    π (t + 1) ω = 1 ∧ fisherRate 𝔼 π (t + 1) ω = 1 := by
  have hφ1 : φ ≠ 1 := fun e => by rw [e, abs_one] at hφ; exact lt_irrefl _ hφ
  have hsub : φ - 1 ≠ 0 := sub_ne_zero.mpr hφ1
  have heq := (nonExplosive_iff 𝔼 hφ (by rw [abs_one]) hφ1 h ha hπ).mp hne
  have hπt : ∀ t, π (t + 1) ω = 1 := fun t => by
    rw [heq]
    simp only [ar1Pi, Pi.smul_apply, smul_eq_mul, hu t]
    field_simp
    ring
  refine ⟨hπt t, ?_⟩
  rw [heq, (eq_16_15 𝔼 φ h (t + 1)).1, ← heq, Pi.smul_apply, smul_eq_mul, one_mul, hπt t]

/-- Cochrane (2023), p. 375 (open-mouth operation; survey error E5 — the printed
"`π_2 = π_2 = ..`" means `π_2 = π_3 = … = 0`): with `η = 0` and the one-period shock
`u_1 = ε_1 = −φ` (`u_t = 0` otherwise along `ω`), the selected equilibrium has `π_1 = 1`,
`π_t = 0` for `t ≠ 1`, and `i_t = 0` at every date and in every state: inflation moves with no
movement in interest rates at all. -/
theorem open_mouth {φ : ℝ} (hφ : φ ≠ 0) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 0 u ε) {ω : Ω}
    (hu1 : u 1 ω = -φ) (hu : ∀ t, t ≠ 1 → u t ω = 0) :
    ar1Pi φ 0 u 1 ω = 1 ∧ (∀ t, t ≠ 1 → ar1Pi φ 0 u t ω = 0) ∧
      ∀ t, fisherRate 𝔼 (ar1Pi φ 0 u) t = 0 := by
  refine ⟨?_, fun t ht => ?_, fun t => ?_⟩
  · simp only [ar1Pi, sub_zero, Pi.smul_apply, smul_eq_mul, hu1]
    field_simp
  · simp only [ar1Pi, sub_zero, Pi.smul_apply, smul_eq_mul, hu t ht, mul_zero]
  · rw [(eq_16_15 𝔼 φ h t).1, zero_smul]

/-- Cochrane (2023), p. 375 ("The price level takes a permanent jump"): in the open-mouth
response the log price level `p_t = p_0 + ∑_{s=1}^{t} π_s` rises by exactly one at date 1 and
stays there. -/
theorem open_mouth_price_jump {φ : ℝ} (hφ : φ ≠ 0) {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 0 u ε)
    {ω : Ω} (hu1 : u 1 ω = -φ) (hu : ∀ t, t ≠ 1 → u t ω = 0) (t : ℕ) :
    ∑ s ∈ Finset.range (t + 2), ar1Pi φ 0 u s ω = 1 := by
  obtain ⟨h1, h0, -⟩ := open_mouth 𝔼 hφ h hu1 hu
  induction t with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_one, h0 0 (by norm_num), h1, zero_add]
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, h0 (t + 2) (by omega), add_zero]

/-! ### Non-vacuity: the responses on the coin-flip tree -/

/-- Cochrane (2023), p. 375 (examples): a shock arriving only at date 1, `ε_1 = c·(±1)` on the
first coin flip, `ε_t = 0` otherwise. -/
noncomputable def dateOneShock (c : ℝ) (t : ℕ) : Bool × Bool → ℝ :=
  if t = 1 then c • ExpectationsFiniteTree.coinShock 1 else 0

/-- Cochrane (2023), p. 375 (examples): the date-1 shock is a shock on the coin-flip tree,
and it is adapted at every date. -/
theorem dateOneShock_isShock (c : ℝ) :
    IsShock ExpectationsFiniteTree.coinSystem (dateOneShock c) ∧
      ExpectationsFiniteTree.coinSystem.Adapted (dateOneShock c) := by
  have ha : ExpectationsFiniteTree.coinSystem.Adapted (dateOneShock c) := fun t => by
    by_cases ht : t = 1
    · subst ht
      simp only [dateOneShock, ↓reduceIte, map_smul, coinShock_adapted 1]
    · simp only [dateOneShock, ht, ↓reduceIte, map_zero]
  refine ⟨⟨fun t => ha (t + 1), fun t => ?_⟩, ha⟩
  by_cases ht : t = 0
  · subst ht
    simp only [dateOneShock, zero_add, ↓reduceIte, map_smul,
      ExpectationsFiniteTree.coinShock_mean_zero 0, smul_zero]
  · have : t + 1 ≠ 1 := by omega
    simp only [dateOneShock, this, ↓reduceIte, map_zero]

/-- Cochrane (2023), p. 375 (super-Fisherian example): the random walk `u_0 = 0`,
`u_t = (1 − φ)·(±1)` for `t ≥ 1`, on the coin-flip tree. -/
noncomputable def superU (φ : ℝ) (t : ℕ) : Bool × Bool → ℝ :=
  if t = 0 then 0 else (1 - φ) • ExpectationsFiniteTree.coinShock 1

/-- Cochrane (2023), p. 375: `superU` is an AR(1) with `η = 1` driven by the date-1 shock. -/
theorem superU_ar1 (φ : ℝ) :
    AR1 ExpectationsFiniteTree.coinSystem 1 (superU φ) (dateOneShock (1 - φ)) := by
  refine ⟨fun t => ?_, (dateOneShock_isShock (1 - φ)).1, fun t => ?_⟩
  · by_cases ht : t = 0
    · subst ht
      simp only [superU, ↓reduceIte, map_zero]
    · simp only [superU, ht, ↓reduceIte, map_smul]
      rw [ForwardSolution.E_of_known _ (Nat.one_le_iff_ne_zero.mpr ht)
        (coinShock_adapted 1)]
  · by_cases ht : t = 0
    · subst ht
      simp [superU, dateOneShock]
    · simp [superU, dateOneShock, ht]

/-- Cochrane (2023), p. 375 (super-Fisherian response, non-vacuous): on the coin-flip tree,
for every `|φ| > 1`, the selected equilibrium `π = −u/(φ − 1)` of `superU` has, on the history
where the first flip is heads, `π_t = i_t = 1` for all `t ≥ 1`, while `E_0 π_1 = 0`. -/
theorem super_fisherian_coin {φ : ℝ} (hφ : 1 < |φ|) (b : Bool) (t : ℕ) :
    ar1Pi φ 1 (superU φ) (t + 1) (true, b) = 1 ∧
      fisherRate ExpectationsFiniteTree.coinSystem (ar1Pi φ 1 (superU φ)) (t + 1) (true, b) = 1 ∧
      ExpectationsFiniteTree.coinSystem.E 0 (ar1Pi φ 1 (superU φ) 1) = 0 := by
  have hφ1 : φ ≠ 1 := fun e => by rw [e, abs_one] at hφ; exact lt_irrefl _ hφ
  have h := superU_ar1 φ
  have ha : ExpectationsFiniteTree.coinSystem.Adapted (ar1Pi φ 1 (superU φ)) := fun s => by
    simp only [ar1Pi, map_smul, h.1 s]
  have hπ := ar1Pi_eq164 ExpectationsFiniteTree.coinSystem hφ1 (h.isAR1 _)
  have hne : NonExplosive ExpectationsFiniteTree.coinSystem (ar1Pi φ 1 (superU φ)) :=
    (nonExplosive_iff _ hφ (by rw [abs_one]) hφ1 h ha hπ).mpr rfl
  have hu : ∀ t, superU φ (t + 1) (true, b) = 1 - φ := fun t => by
    simp [superU, ExpectationsFiniteTree.coinShock]
  obtain ⟨h1, h2⟩ := super_fisherian _ hφ h ha hπ hne hu t
  refine ⟨h1, h2, ?_⟩
  change fisherRate ExpectationsFiniteTree.coinSystem (ar1Pi φ 1 (superU φ)) 0 = 0
  rw [(eq_16_15 _ φ h 0).1]
  funext ω
  simp [ar1Pi, superU]

/-- Cochrane (2023), p. 375 (open-mouth operation, non-vacuous): on the coin-flip tree, with
`u = ε` the date-1 shock `−φ·(±1)`, on the heads history `π_1 = 1`, `π_t = 0` for `t ≠ 1`, and
the interest rate is zero at every date in every state. -/
theorem open_mouth_coin {φ : ℝ} (hφ : φ ≠ 0) (b : Bool) :
    ar1Pi φ 0 (dateOneShock (-φ)) 1 (true, b) = 1 ∧
      (∀ t, t ≠ 1 → ar1Pi φ 0 (dateOneShock (-φ)) t (true, b) = 0) ∧
      ∀ t, fisherRate ExpectationsFiniteTree.coinSystem (ar1Pi φ 0 (dateOneShock (-φ))) t = 0 := by
  have h : AR1 ExpectationsFiniteTree.coinSystem 0 (dateOneShock (-φ)) (dateOneShock (-φ)) :=
    ⟨(dateOneShock_isShock (-φ)).2, (dateOneShock_isShock (-φ)).1, fun t => by simp⟩
  refine open_mouth _ hφ h ?_ fun t ht => ?_
  · simp [dateOneShock, ExpectationsFiniteTree.coinShock]
  · simp [dateOneShock, ht]

/-! ### The rule `i_t = φ E_t π_{t+1}` (p. 376) -/

/-- Cochrane (2023), p. 376: an equilibrium of the Fisher equation with the rule
`i_t = φ E_t π_{t+1}` (a rule that "raises real interest rates when inflation rises"). -/
def RuleExpEq (φ : ℝ) (π i : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ (∀ t, i t = 𝔼.E t (π (t + 1))) ∧ ∀ t, i t = φ • 𝔼.E t (π (t + 1))

/-- Cochrane (2023), p. 376 (corrected): for `φ ≠ 1`, every equilibrium of the rule
`i_t = φ E_t π_{t+1}` has `E_t π_{t+1} = 0` and `i_t = 0`: the rule cannot move the interest
rate or expected inflation at all. -/
theorem ruleExp_trivial {φ : ℝ} (hφ : φ ≠ 1) {π i : ℕ → Ω → ℝ} (h : RuleExpEq 𝔼 φ π i)
    (t : ℕ) : 𝔼.E t (π (t + 1)) = 0 ∧ i t = 0 := by
  have e := (h.2.1 t).symm.trans (h.2.2 t)
  have hz : (φ - 1) • 𝔼.E t (π (t + 1)) = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
  have hE := (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hφ)
  exact ⟨hE, by rw [h.2.1 t, hE]⟩

/-- Cochrane (2023), p. 376 (corrected): the rule has solutions — any shock process (a shock
with `δ_0` known at date 0, i.e. adapted with `E_t δ_{t+1} = 0`) is equilibrium inflation, with
`i = 0`; so inflation is entirely indeterminate. -/
theorem ruleExp_solutions (φ : ℝ) {δ : ℕ → Ω → ℝ} (hδ : IsShock 𝔼 δ)
    (h0 : 𝔼.E 0 (δ 0) = δ 0) : RuleExpEq 𝔼 φ δ (fun _ => 0) :=
  ⟨((adapted_isShock_iff 𝔼).mpr ⟨hδ, h0⟩).1, fun t => (hδ.2 t).symm,
    fun t => by rw [hδ.2 t, smul_zero]⟩

/-- Cochrane (2023), p. 376 ("would lead to an equilibrium condition `φ E_t π_{t+1} =
E_t π_{t+1}` which has no solution"): the printed claim is imprecise — `π = 0`, `i = 0` is a
solution for every `φ` and every expectation system. -/
theorem ruleExp_has_solution (φ : ℝ) : RuleExpEq 𝔼 φ (fun _ => 0) (fun _ => 0) :=
  ruleExp_solutions 𝔼 φ ⟨fun _ => map_zero _, fun _ => map_zero _⟩ (map_zero _)

/-- Cochrane (2023), p. 376: with a disturbance, `i_t = φ E_t π_{t+1} + u_t` and `φ ≠ 1`, the
rule pins expected inflation `E_t π_{t+1} = u_t/(1 − φ)`; the real rate `i_t − E_t π_{t+1}`
is still zero, so no rule raises real rates in this model. -/
theorem ruleExp_disturbance {φ : ℝ} (hφ : φ ≠ 1) {u π i : ℕ → Ω → ℝ}
    (hF : ∀ t, i t = 𝔼.E t (π (t + 1))) (hR : ∀ t, i t = φ • 𝔼.E t (π (t + 1)) + u t)
    (t : ℕ) : 𝔼.E t (π (t + 1)) = (1 - φ)⁻¹ • u t ∧ i t - 𝔼.E t (π (t + 1)) = 0 := by
  have hne : 1 - φ ≠ 0 := sub_ne_zero.mpr (Ne.symm hφ)
  have e := (hF t).symm.trans (hR t)
  refine ⟨?_, by rw [hF t, sub_self]⟩
  have : (1 - φ) • 𝔼.E t (π (t + 1)) = u t := by
    rw [sub_smul, one_smul, sub_eq_iff_eq_add, add_comm (u t)]
    exact e
  rw [← this, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-! ### The fiscal requirement (pp. 376–377) -/

/-- Cochrane (2023), (16.1)–(16.3), p. 364: an equilibrium of the full simplest model, including
the debt-valuation equation `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`. -/
def NK3Eq (φ : ℝ) (u εs π i : ℕ → Ω → ℝ) : Prop :=
  NKEq 𝔼 φ u π i ∧ ∀ t, innov 𝔼 t (π (t + 1)) = -εs (t + 1)

/-- Cochrane (2023), p. 376 ("if this passive fiscal contraction does not or cannot happen, the
unexpected inflation cannot happen"): with no fiscal shock, every equilibrium has no
unexpected inflation. -/
theorem no_fiscal_no_surprise {φ : ℝ} {u π i : ℕ → Ω → ℝ} (h : NK3Eq 𝔼 φ u 0 π i) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = 0 := by
  rw [h.2 t, Pi.zero_apply, neg_zero]

/-- Cochrane (2023), pp. 372, 376: the selected AR(1) equilibrium is an equilibrium of the full
model (16.1)–(16.3) iff the fiscal shock is exactly `ε_Σs,t+1 = ε_{i,t+1}/(φ − η)`. -/
theorem nk3_ar1_fiscal_iff {φ η : ℝ} (hφη : φ ≠ η) {u ε εs : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) :
    NK3Eq 𝔼 φ u εs (ar1Pi φ η u) (fisherRate 𝔼 (ar1Pi φ η u)) ↔
      ∀ t, εs (t + 1) = (φ - η)⁻¹ • ε (t + 1) := by
  have hN : NKEq 𝔼 φ u (ar1Pi φ η u) (fisherRate 𝔼 (ar1Pi φ η u)) :=
    (nkEq_iff 𝔼 _ _ _ _).mpr ⟨fun s => by simp only [ar1Pi, map_smul, h.1 s],
      ar1Pi_eq164 𝔼 hφη (h.isAR1 𝔼), rfl⟩
  constructor
  · intro h3 t
    have e := h3.2 t
    rw [eq_16_16_innov 𝔼 φ h t, neg_smul, neg_inj] at e
    exact e.symm
  · intro hs
    exact ⟨hN, fun t => by rw [eq_16_16_innov 𝔼 φ h t, hs t, neg_smul]⟩

/-- Cochrane (2023), pp. 376–377: if a monetary-policy shock occurs (`ε_{t+1} ≠ 0` somewhere)
and there is no fiscal response (`ε_Σs = 0`), then (16.1)–(16.3) has NO non-explosive
equilibrium (`|φ| > 1 ≥ |η|`): the new-Keynesian response exists only because of the
"passive" fiscal contraction. -/
theorem no_eq_without_fiscal {φ η : ℝ} (hφ : 1 < |φ|) (hη : |η| ≤ 1) (hφη : φ ≠ η)
    {u ε : ℕ → Ω → ℝ} (h : AR1 𝔼 η u ε) {t : ℕ} {ω : Ω} (hε : ε (t + 1) ω ≠ 0) :
    ¬ ∃ π i, NK3Eq 𝔼 φ u 0 π i ∧ NonExplosive 𝔼 π := by
  rintro ⟨π, i, h3, hne⟩
  have hN := (nkEq_iff 𝔼 _ _ _ _).mp h3.1
  have heq := (nonExplosive_iff 𝔼 hφ hη hφη h hN.1 hN.2.1).mp hne
  have e := congrFun (no_fiscal_no_surprise 𝔼 h3 t) ω
  rw [heq, eq_16_16_innov 𝔼 φ h t] at e
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, neg_mul, neg_eq_zero,
    mul_eq_zero, inv_eq_zero, sub_eq_zero] at e
  rcases e with e | e
  · exact hφη e
  · exact hε e

/-- Cochrane (2023), p. 376 ("the monetary policy shock lowers inflation because it induces a
fiscal contraction, and only because it induces a fiscal contraction"): in every equilibrium
of (16.1)–(16.3), unexpected inflation is negative exactly when the fiscal shock (the rise in
the present value of surpluses) is positive. -/
theorem disinflation_iff_contraction {φ : ℝ} {u εs π i : ℕ → Ω → ℝ} (h : NK3Eq 𝔼 φ u εs π i)
    (t : ℕ) (ω : Ω) : innov 𝔼 t (π (t + 1)) ω < 0 ↔ 0 < εs (t + 1) ω := by
  rw [h.2 t, Pi.neg_apply, neg_lt_zero]

end Cochrane.NewKeynesianSelection.Responses
