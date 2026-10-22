/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5RealExplosions
import KeynesianStickyPrices.TidyR5ExpectationsMeasure

/-!
# Real explosions on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.5.2, eqs.
(17.29)–(17.32), pp. 420–421 ("real explosions … so `E_t βʲ x_{t+j} → ∞`"), with the output
response of (18.1), p. 427.

The core `ExpectationSystem` has exact conditional expectations on all functions, so on a
countable state space its forecasts are finitely supported. Here the deviation system is posed
on a probability space with a filtration and Mathlib's conditional expectation
(`TidyR5ExpectationsMeasure.MeasExpectationSystem`), every equation holding almost everywhere
and every variable integrable (`DevM`). This covers genuine infinite-horizon uncertainty such as
i.i.d. shocks (TidyR5ExpectationsMeasureIID).

* `expected_pfDevX_ae`: for every date `s`, almost every state `ω` has a perfect-foresight
  expected path `j ↦ (E_s x̃_{s+j}(ω), E_s π̃_{s+j}(ω))` (`TidyR5RealExplosions.PFDevX`);
  `mean_pfDevX`: the unconditional mean path `t ↦ (𝔼 x̃_t, 𝔼 π̃_t)` is one too.
* `constDevM`: every perfect-foresight deviation is a (deterministic) deviation on the
  probability space.
* Hence the characterisations of TidyR5RealExplosions hold verbatim on every probability space,
  for all `φ`, `φ_x` (`σ, κ, β > 0`): some deviation has, at some date `s`, on a set of positive
  probability, `βʲ E_s x̃_{s+j} → +∞` iff `φ < 1/β` or (`T > 2` and `4B ≤ T²`)
  (`explodes_measure_iff`); unbounded iff `φ < 1/β`, `|B| > 1`, `1 + B + T < 0` or
  `B = 1 ∧ T = −2` (`unbounded_measure_iff`); the expected real transversality condition fails
  iff `φ < 1/β`, `|B| ≥ 1` or `1 + B + T ≤ 0` (`tvc_measure_iff`); and the same for the
  unconditional mean `βᵗ 𝔼 x̃_t` (`explodes_mean_iff`, `unbounded_mean_iff`, `tvc_mean_iff`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5ExplosionsMeasure

open MeasureTheory Filter Topology TidyR5ExpectationsMeasure TidyR5RealExplosions

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420, with the output response of (18.1), on a
probability space: `ĩ_t = r̃_t + E_t π̃_{t+1}`, `x̃_t = E_t x̃_{t+1} − σ r̃_t`,
`π̃_t = β E_t π̃_{t+1} + κ x̃_t`, `ĩ_t = φ π̃_t + φ_x x̃_t`, almost everywhere, all variables
integrable. -/
def DevM (σ β κ φ φx : ℝ) (i r x π : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Integrable (i t) S.μ ∧ Integrable (r t) S.μ ∧ Integrable (x t) S.μ ∧
    Integrable (π t) S.μ) ∧
  ∀ t, i t =ᵐ[S.μ] r t + S.E t (π (t + 1)) ∧ x t =ᵐ[S.μ] S.E t (x (t + 1)) - σ • r t ∧
    π t =ᵐ[S.μ] β • S.E t (π (t + 1)) + κ • x t ∧ i t =ᵐ[S.μ] φ • π t + φx • x t

/-- Cochrane (2023), p. 421 ("`E_t βʲ x_{t+j}`"), on a probability space: for every date `s`,
almost surely the expected path `j ↦ (E_s x̃_{s+j}, E_s π̃_{s+j})` is a perfect-foresight
deviation. -/
theorem expected_pfDevX_ae {σ β κ φ φx : ℝ} {i r x π : ℕ → Ω → ℝ}
    (h : DevM S σ β κ φ φx i r x π) (s : ℕ) :
    ∀ᵐ ω ∂S.μ, PFDevX σ β κ φ φx (fun j => S.E s (x (s + j)) ω)
      (fun j => S.E s (π (s + j)) ω) := by
  obtain ⟨hint, heq⟩ := h
  refine ae_all_iff.mpr fun j => ?_
  have hle : s ≤ s + j := Nat.le_add_right s j
  obtain ⟨h1, h2, h3, h4⟩ := heq (s + j)
  obtain ⟨-, ir, ix, iπ⟩ := hint (s + j)
  have iEπ := S.integrable_E (s + j) (π (s + j + 1))
  have iEx := S.integrable_E (s + j) (x (s + j + 1))
  filter_upwards [S.E_congr h1 s, S.E_add ir iEπ s, S.E_tower hle (π (s + j + 1)),
    S.E_congr h2 s, S.E_sub iEx (ir.smul σ) s, S.E_tower hle (x (s + j + 1)),
    S.E_smul σ (r (s + j)) s,
    S.E_congr h3 s, S.E_add (iEπ.smul β) (ix.smul κ) s,
    S.E_smul β (S.E (s + j) (π (s + j + 1))) s, S.E_smul κ (x (s + j)) s,
    S.E_congr h4 s, S.E_add (iπ.smul φ) (ix.smul φx) s, S.E_smul φ (π (s + j)) s,
    S.E_smul φx (x (s + j)) s] with ω a1 b1 c1 a2 b2 c2 d2 a3 b3 c3 d3 a4 b4 c4 d4
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at a1 b1 a2 b2 d2 a3 b3 c3 d3 a4 b4 c4 d4
  have hs : s + (j + 1) = s + j + 1 := rfl
  simp only [hs]
  refine ⟨by linear_combination a3 + b3 + c3 + d3 + β * c1, ?_⟩
  linear_combination a2 + b2 + c2 - d2 + σ * (a1 + b1 + c1) - σ * (a4 + b4 + c4 + d4)

/-- Cochrane (2023), p. 421, on a probability space: the unconditional mean path
`t ↦ (𝔼 x̃_t, 𝔼 π̃_t)` is a perfect-foresight deviation. -/
theorem mean_pfDevX {σ β κ φ φx : ℝ} {i r x π : ℕ → Ω → ℝ} (h : DevM S σ β κ φ φx i r x π) :
    PFDevX σ β κ φ φx (fun t => ∫ ω, x t ω ∂S.μ) (fun t => ∫ ω, π t ω ∂S.μ) := by
  obtain ⟨hint, heq⟩ := h
  intro t
  obtain ⟨h1, h2, h3, h4⟩ := heq t
  obtain ⟨ii, ir, ix, iπ⟩ := hint t
  have iEπ := S.integrable_E t (π (t + 1))
  have iEx := S.integrable_E t (x (t + 1))
  have a1 := integral_congr_ae h1
  have a2 := integral_congr_ae h2
  have a3 := integral_congr_ae h3
  have a4 := integral_congr_ae h4
  rw [integral_add' ir iEπ, S.integral_E] at a1
  rw [integral_sub' iEx (ir.smul σ), S.integral_E] at a2
  rw [integral_add' (iEπ.smul β) (ix.smul κ)] at a3
  rw [integral_add' (iπ.smul φ) (ix.smul φx)] at a4
  simp only [Pi.smul_apply] at a2 a3 a4
  rw [integral_smul] at a2
  rw [integral_smul, integral_smul, S.integral_E] at a3
  rw [integral_smul, integral_smul] at a4
  simp only [smul_eq_mul] at a1 a2 a3 a4
  refine ⟨a3, ?_⟩
  linear_combination a2 + σ * a1 - σ * a4

/-- Cochrane (2023), p. 420: a perfect-foresight deviation is a deterministic deviation on any
probability space. -/
theorem constDevM {σ β κ φ φx : ℝ} {x π : ℕ → ℝ} (hd : PFDevX σ β κ φ φx x π) :
    DevM S σ β κ φ φx (fun t _ => φ * π t + φx * x t)
      (fun t _ => φ * π t + φx * x t - π (t + 1)) (fun t _ => x t) (fun t _ => π t) := by
  refine ⟨fun t => ⟨integrable_const _, integrable_const _, integrable_const _,
    integrable_const _⟩, fun t => ?_⟩
  rw [S.E_const, S.E_const]
  refine ⟨Eventually.of_forall fun ω => ?_, Eventually.of_forall fun ω => ?_,
    Eventually.of_forall fun ω => ?_, Eventually.of_forall fun ω => ?_⟩ <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · ring
  · linarith [(hd t).2]
  · exact (hd t).1

/-- A property of the expected path that holds on a set of positive probability holds, together
with `PFDevX`, at some state (the a.e. statement of `expected_pfDevX_ae`). -/
theorem exists_state_of_pos {σ β κ φ φx : ℝ} {i r x π : ℕ → Ω → ℝ}
    (h : DevM S σ β κ φ φx i r x π) (s : ℕ) (P : (ℕ → ℝ) → Prop)
    (hpos : S.μ {ω | P (fun j => β ^ j * S.E s (x (s + j)) ω)} ≠ 0) :
    ∃ ω, PFDevX σ β κ φ φx (fun j => S.E s (x (s + j)) ω) (fun j => S.E s (π (s + j)) ω) ∧
      P (fun j => β ^ j * S.E s (x (s + j)) ω) := by
  by_contra hc
  push Not at hc
  apply hpos
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp (expected_pfDevX_ae S h s))
  exact fun hp => hc ω hp hω

/-- The set where the expected path of a deterministic deviation has a property is everything
or nothing; for a property that holds it is the whole space, of probability one. -/
theorem const_set {x : ℕ → ℝ} {β : ℝ} (P : (ℕ → ℝ) → Prop) (hP : P (fun j => β ^ j * x j)) :
    S.μ {ω | P (fun j => β ^ j * S.E 0 (fun _ => x (0 + j)) ω)} ≠ 0 := by
  have : {ω | P (fun j => β ^ j * S.E 0 (fun _ => x (0 + j)) ω)} = Set.univ := by
    ext ω
    simp only [Set.mem_univ, iff_true]
    change P (fun j => β ^ j * S.E 0 (fun _ => x (0 + j)) ω)
    simp only [S.E_const, zero_add]
    exact hP
  rw [this, measure_univ]
  exact one_ne_zero

/-! ### The characterisations on a probability space -/

/-- Cochrane (2023), p. 421 ("`E_t βʲ x_{t+j} → ∞`"), on any probability space with a
filtration, for `σ, κ, β > 0` and every `φ`, `φ_x`: some deviation has, at some date `s`, with
positive probability, `βʲ E_s x̃_{s+j} → +∞` iff `φ < 1/β` or (`T > 2` and `4B ≤ T²`). -/
theorem explodes_measure_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, DevM S σ β κ φ φx i r x π ∧ ∃ s,
        S.μ {ω | Tendsto (fun j => β ^ j * S.E s (x (s + j)) ω) atTop atTop} ≠ 0) ↔
      φ < 1 / β ∨ (2 < 1 + β + σ * κ + β * σ * φx ∧
        4 * (β * (1 + σ * φx + σ * κ * φ)) ≤ (1 + β + σ * κ + β * σ * φx) ^ 2) := by
  rw [← explodesX_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, s, hpos⟩
    obtain ⟨ω, hp, ht⟩ := exists_state_of_pos S hd s (fun y => Tendsto y atTop atTop) hpos
    exact ⟨_, _, hp, ht⟩
  · rintro ⟨x, π, hd, ht⟩
    exact ⟨_, _, _, _, constDevM S hd, 0, const_set S (fun y => Tendsto y atTop atTop) ht⟩

/-- Cochrane (2023), p. 421, on any probability space: some deviation has, at some date, with
positive probability, unbounded expected discounted output iff `φ < 1/β`, `|B| > 1`,
`1 + B + T < 0` or `B = 1 ∧ T = −2`. -/
theorem unbounded_measure_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, DevM S σ β κ φ φx i r x π ∧ ∃ s,
        S.μ {ω | ¬ ∃ M, ∀ j, |β ^ j * S.E s (x (s + j)) ω| ≤ M} ≠ 0) ↔
      φ < 1 / β ∨ 1 < |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) < 0 ∨
        (β * (1 + σ * φx + σ * κ * φ) = 1 ∧ 1 + β + σ * κ + β * σ * φx = -2) := by
  rw [← unboundedX_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, s, hpos⟩
    obtain ⟨ω, hp, ht⟩ := exists_state_of_pos S hd s (fun y => ¬ ∃ M, ∀ j, |y j| ≤ M) hpos
    exact ⟨_, _, hp, ht⟩
  · rintro ⟨x, π, hd, ht⟩
    exact ⟨_, _, _, _, constDevM S hd, 0,
      const_set S (fun y => ¬ ∃ M, ∀ j, |y j| ≤ M) ht⟩

/-- Cochrane (2023), p. 421 (the real transversality condition in expectation), on any
probability space: some deviation violates `βʲ E_s x̃_{s+j} → 0` at some date with positive
probability iff `φ < 1/β`, `|B| ≥ 1` or `1 + B + T ≤ 0`. -/
theorem tvc_measure_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, DevM S σ β κ φ φx i r x π ∧ ∃ s,
        S.μ {ω | ¬ Tendsto (fun j => β ^ j * S.E s (x (s + j)) ω) atTop (𝓝 0)} ≠ 0) ↔
      φ < 1 / β ∨ 1 ≤ |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) ≤ 0 := by
  rw [← tvcX_fails_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, s, hpos⟩
    obtain ⟨ω, hp, ht⟩ :=
      exists_state_of_pos S hd s (fun y => ¬ Tendsto y atTop (𝓝 0)) hpos
    exact ⟨_, _, hp, ht⟩
  · rintro ⟨x, π, hd, ht⟩
    exact ⟨_, _, _, _, constDevM S hd, 0, const_set S (fun y => ¬ Tendsto y atTop (𝓝 0)) ht⟩

/-- The mean of a deterministic process is the process. -/
theorem integral_const_path (x : ℕ → ℝ) (t : ℕ) : ∫ _ : Ω, x t ∂S.μ = x t := by
  simp

/-- Cochrane (2023), p. 421, on any probability space, for the unconditional mean: some
deviation has `βᵗ 𝔼 x̃_t → +∞` iff `φ < 1/β` or (`T > 2` and `4B ≤ T²`). -/
theorem explodes_mean_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, DevM S σ β κ φ φx i r x π ∧
        Tendsto (fun t => β ^ t * ∫ ω, x t ω ∂S.μ) atTop atTop) ↔
      φ < 1 / β ∨ (2 < 1 + β + σ * κ + β * σ * φx ∧
        4 * (β * (1 + σ * φx + σ * κ * φ)) ≤ (1 + β + σ * κ + β * σ * φx) ^ 2) := by
  rw [← explodesX_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, ht⟩
    exact ⟨_, _, mean_pfDevX S hd, ht⟩
  · rintro ⟨x, π, hd, ht⟩
    refine ⟨_, _, _, _, constDevM S hd, ?_⟩
    simpa only [integral_const_path S] using ht

/-- Cochrane (2023), p. 421, on any probability space, for the unconditional mean: some
deviation has `βᵗ 𝔼 x̃_t` unbounded iff `φ < 1/β`, `|B| > 1`, `1 + B + T < 0` or
`B = 1 ∧ T = −2`. -/
theorem unbounded_mean_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, DevM S σ β κ φ φx i r x π ∧
        ¬ ∃ M, ∀ t, |β ^ t * ∫ ω, x t ω ∂S.μ| ≤ M) ↔
      φ < 1 / β ∨ 1 < |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) < 0 ∨
        (β * (1 + σ * φx + σ * κ * φ) = 1 ∧ 1 + β + σ * κ + β * σ * φx = -2) := by
  rw [← unboundedX_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, ht⟩
    exact ⟨_, _, mean_pfDevX S hd, ht⟩
  · rintro ⟨x, π, hd, ht⟩
    refine ⟨_, _, _, _, constDevM S hd, ?_⟩
    simpa only [integral_const_path S] using ht

/-- Cochrane (2023), p. 421, on any probability space, for the unconditional mean: some
deviation violates `βᵗ 𝔼 x̃_t → 0` iff `φ < 1/β`, `|B| ≥ 1` or `1 + B + T ≤ 0`. -/
theorem tvc_mean_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, DevM S σ β κ φ φx i r x π ∧
        ¬ Tendsto (fun t => β ^ t * ∫ ω, x t ω ∂S.μ) atTop (𝓝 0)) ↔
      φ < 1 / β ∨ 1 ≤ |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) ≤ 0 := by
  rw [← tvcX_fails_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, ht⟩
    exact ⟨_, _, mean_pfDevX S hd, ht⟩
  · rintro ⟨x, π, hd, ht⟩
    refine ⟨_, _, _, _, constDevM S hd, ?_⟩
    simpa only [integral_const_path S] using ht

end Cochrane.KeynesianStickyPrices.TidyR5ExplosionsMeasure
