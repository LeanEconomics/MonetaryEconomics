/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5Recurrence

/-!
# Real explosions with an output response and under uncertainty

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.5.2, eqs.
(17.29)–(17.33), pp. 420–421 ("real explosions faster than the interest rate so
`E_t βʲ x_{t+j} → ∞`"), with the output response of (18.1), p. 427, and Online Appendix A1,
(1.57), p. 587.

FullModelTidy characterised real explosions for the perfect-foresight deviation system with
`φ_x = 0`, as in (17.32). Here they are characterised for **every** `φ` and `φ_x`, and for
**every** `ExpectationSystem`.

## Perfect foresight with an output response

`PFDevX` is the deviation system with `ĩ = φπ̃ + φ_x x̃` (`deviation_iff_pfDevX`). In the
discounted variables `y_t = βᵗ x̃_t`, `q_t = βᵗ π̃_t`: `q_{t+1} = q_t − κ y_t`,
`y_{t+1} = (β + βσφ_x + σκ) y_t + σ(βφ − 1) q_t` (`scaledX`), so
`y_{t+2} = T y_{t+1} − B y_t` with `T = 1 + β + σκ + βσφ_x` and `B = β(1 + σφ_x + σκφ) = βD`
(`y_recX`); `1 − T + B = σκ(βφ − 1)` does not depend on `φ_x` (`p_one`). For `βφ ≠ 1` the
discounted outputs are **exactly** the solutions of this recursion (`discY_iff`); at
`βφ = 1` they are exactly the geometric paths `c Bᵗ` (`discY_inv_beta`). With
TidyR5Recurrence, for `σ, κ, β > 0` and all `φ`, `φ_x`:

* `explodesX_pf_iff`: some deviation has `βᵗ x̃_t → +∞` iff `φ < 1/β` or (`T > 2` and
  `4B ≤ T²`); `explodesX_atBot_pf_iff`: the same for `−∞`.
* `unboundedX_pf_iff`: some deviation has `βᵗ x̃_t` unbounded iff `φ < 1/β`, `|B| > 1`,
  `1 + B + T < 0`, or `B = 1 ∧ T = −2`.
* `tvcX_fails_pf_iff`: some deviation violates `βᵗ x̃_t → 0` iff `φ < 1/β`, `|B| ≥ 1` or
  `1 + B + T ≤ 0`.

At `φ_x = 0` these are the conditions of FullModelTidy (`explodes_cond_phix_zero`,
`unbounded_cond_phix_zero`, `tvc_cond_phix_zero`). What changes with `φ_x ≠ 0`:

* `φ < 1/β` still produces a monotone real explosion for every `φ_x` (`explodes_of_lt_inv_beta`).
* At the book's calibration of Fig. 17.8 (`β = 0.95`, `σ = 1`, `κ = 1/2`, `φ = 1.5`), where
  with `φ_x = 0` every real explosion oscillates (`FullModelTidy.book_calibration_oscillates`),
  the Taylor-type response `φ_x = 1/2` keeps the system determinate and makes the roots real:
  some deviation has `βᵗ x̃_t → +∞` (`book_calibration_output_response`).
* The determinant condition `β(1 + σκφ) > 1` of the `φ_x = 0` case is no longer the whole story:
  with `β = 1/2`, `σ = κ = 1`, `φ = 10 ≥ 1/β`, `φ_x = −10`, `B = 1/2 < 1` but `1 + B + T < 0`
  and real explosions exist (`explosion_with_small_det`).

## Every expectation system

For any `ExpectationSystem`, expected paths of a deviation are perfect-foresight deviations:
`j ↦ (E_s x̃_{s+j}(ω), E_s π̃_{s+j}(ω))` solves `PFDevX` for every date `s` and state `ω`
(`expected_pfDevX`), and every perfect-foresight deviation is a (deterministic) deviation under
`𝔼` (`const_deviation`). So the book's form `E_t βʲ x̃_{t+j} → ∞` is characterised **exactly**
by the same conditions under uncertainty (`explodes_uncertainty_iff`,
`unbounded_uncertainty_iff`, `tvc_uncertainty_iff`), for every `ExpectationSystem` on a
nonempty state space.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5RealExplosions

open Filter Topology FullModel TaylorDeterminacy FullModelTidy TidyR5Recurrence

/-! ### Perfect foresight with an output response -/

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420, with the output response of (18.1), p. 427,
under perfect foresight with `ĩ = φπ̃ + φ_x x̃` and `r̃ = ĩ − π̃_{t+1}` eliminated:
`π̃_t = β π̃_{t+1} + κ x̃_t`, `x̃_t = x̃_{t+1} − σ(φ π̃_t + φ_x x̃_t − π̃_{t+1})`. -/
def PFDevX (σ β κ φ φx : ℝ) (x π : ℕ → ℝ) : Prop :=
  ∀ t, π t = β * π (t + 1) + κ * x t ∧
    x t = x (t + 1) - σ * (φ * π t + φx * x t - π (t + 1))

/-- Cochrane (2023), eqs. (17.29)–(17.32), p. 420: under perfect foresight the deviation system
with output response holds iff `ĩ = φπ̃ + φ_x x̃`, `r̃_t = ĩ_t − π̃_{t+1}` and `(x̃, π̃)` solves
`PFDevX`. -/
theorem deviation_iff_pfDevX (σ β κ φ φx : ℝ) (i r x π : ℕ → Unit → ℝ) :
    Deviation perfectForesight σ β κ φ φx i r x π ↔
      (∀ t, i t () = φ * π t () + φx * x t ()) ∧ (∀ t, r t () = i t () - π (t + 1) ()) ∧
        PFDevX σ β κ φ φx (fun t => x t ()) (fun t => π t ()) := by
  constructor
  · intro h
    have e : ∀ t, i t () = r t () + π (t + 1) () ∧ x t () = x (t + 1) () - σ * r t () ∧
        π t () = β * π (t + 1) () + κ * x t () ∧ i t () = φ * π t () + φx * x t () :=
      fun t => by
      obtain ⟨h1, h2, h3, h4⟩ := h t
      have a1 := congrFun h1 ()
      have a2 := congrFun h2 ()
      have a3 := congrFun h3 ()
      have a4 := congrFun h4 ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul] at a1 a2 a3 a4
      exact ⟨a1, a2, a3, a4⟩
    refine ⟨fun t => (e t).2.2.2, fun t => by linarith [(e t).1], fun t => ⟨(e t).2.2.1, ?_⟩⟩
    obtain ⟨a1, a2, _, a4⟩ := e t
    linear_combination a2 + σ * (a1 - a4)
  · rintro ⟨hi, hr, hd⟩ t
    refine ⟨?_, ?_, ?_, ?_⟩ <;> funext u <;> cases u <;>
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
    · linarith [hr t]
    · rw [hr t, hi t]
      linarith [(hd t).2]
    · exact (hd t).1
    · exact hi t

/-- Cochrane (2023), p. 420: a property of output deviations holds for some solution of the
perfect-foresight deviation system with output response iff it holds for some solution of
`PFDevX`. -/
theorem exists_deviation_iff_X (σ β κ φ φx : ℝ) (P : (ℕ → ℝ) → Prop) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ φx i r x π ∧
        P (fun t => x t ())) ↔ ∃ x π : ℕ → ℝ, PFDevX σ β κ φ φx x π ∧ P x := by
  constructor
  · rintro ⟨i, r, x, π, h, hP⟩
    exact ⟨fun t => x t (), fun t => π t (),
      ((deviation_iff_pfDevX σ β κ φ φx i r x π).mp h).2.2, hP⟩
  · rintro ⟨x, π, hd, hP⟩
    exact ⟨fun t _ => φ * π t + φx * x t, fun t _ => φ * π t + φx * x t - π (t + 1),
      fun t _ => x t, fun t _ => π t,
      (deviation_iff_pfDevX σ β κ φ φx _ _ _ _).mpr ⟨fun _ => rfl, fun _ => rfl, hd⟩, hP⟩

/-- Cochrane (2023), p. 420: with `φ_x = 0`, `PFDevX` is the system `PFDev` of
FullModelTidy. -/
theorem pfDevX_zero (σ β κ φ : ℝ) (x π : ℕ → ℝ) :
    PFDevX σ β κ φ 0 x π ↔ PFDev σ β κ φ x π := by
  simp only [PFDevX, PFDev, zero_mul, add_zero]

/-! ### Discounted variables -/

/-- Cochrane (2023), p. 421 ("faster than the interest rate"): in the discounted variables
`y_t = βᵗ x̃_t`, `q_t = βᵗ π̃_t` the deviation system reads `q_{t+1} = q_t − κ y_t`,
`y_{t+1} = (β + βσφ_x + σκ) y_t + σ(βφ − 1) q_t`. -/
theorem scaledX {σ β κ φ φx : ℝ} {x π : ℕ → ℝ} (h : PFDevX σ β κ φ φx x π) (t : ℕ) :
    β ^ (t + 1) * π (t + 1) = β ^ t * π t - κ * (β ^ t * x t) ∧
      β ^ (t + 1) * x (t + 1) =
        (β + β * σ * φx + σ * κ) * (β ^ t * x t) + σ * (β * φ - 1) * (β ^ t * π t) := by
  obtain ⟨h1, h2⟩ := h t
  rw [pow_succ]
  exact ⟨by linear_combination (-β ^ t) * h1,
    by linear_combination (-(β ^ t * β)) * h2 + (σ * β ^ t) * h1⟩

/-- Cochrane (2023), A1 (1.57), p. 587, with an output response: discounted output
`y_t = βᵗ x̃_t` solves `y_{t+2} = T y_{t+1} − B y_t`, `T = 1 + β + σκ + βσφ_x`,
`B = β(1 + σφ_x + σκφ)`. -/
theorem y_recX {σ β κ φ φx : ℝ} {x π : ℕ → ℝ} (h : PFDevX σ β κ φ φx x π) :
    Rec (1 + β + σ * κ + β * σ * φx) (β * (1 + σ * φx + σ * κ * φ))
      (fun t => β ^ t * x t) := fun t => by
  have s0 := scaledX h t
  have s1 := scaledX h (t + 1)
  rw [show t + 1 + 1 = t + 2 by ring] at s1
  simp only
  linear_combination s1.2 + σ * (β * φ - 1) * s0.1 - s0.2

/-- Cochrane (2023), p. 421: `1 − T + B = σκ(βφ − 1)`, independent of `φ_x`. -/
theorem p_one (σ β κ φ φx : ℝ) :
    1 - (1 + β + σ * κ + β * σ * φx) + β * (1 + σ * φx + σ * κ * φ) = σ * κ * (β * φ - 1) := by
  ring

/-- Cochrane (2023), p. 421: at `φ = 1/β` the discounted output decouples,
`βᵗ x̃_t = (β + βσφ_x + σκ)ᵗ x̃_0`. -/
theorem y_at_inv_betaX {σ β κ φ φx : ℝ} {x π : ℕ → ℝ} (h : PFDevX σ β κ φ φx x π)
    (hφ : β * φ = 1) (t : ℕ) : β ^ t * x t = (β + β * σ * φx + σ * κ) ^ t * x 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [(scaledX h t).2, hφ, ih, pow_succ]
    ring

/-- Cochrane (2023), p. 420: the deviation path with output response from arbitrary initial
discounted values `(y_0, q_0)`. -/
noncomputable def sPathX (σ β κ φ φx y0 q0 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (y0, q0)
  | t + 1 => ((β + β * σ * φx + σ * κ) * (sPathX σ β κ φ φx y0 q0 t).1 +
      σ * (β * φ - 1) * (sPathX σ β κ φ φx y0 q0 t).2,
      (sPathX σ β κ φ φx y0 q0 t).2 - κ * (sPathX σ β κ φ φx y0 q0 t).1)

/-- Cochrane (2023), p. 420: `x̃_t = y_t/βᵗ`, `π̃_t = q_t/βᵗ` from `sPathX` solves the deviation
system with output response. -/
theorem sPathX_pfDevX {σ β κ φ φx : ℝ} (hβ : β ≠ 0) (y0 q0 : ℝ) :
    PFDevX σ β κ φ φx (fun t => (sPathX σ β κ φ φx y0 q0 t).1 / β ^ t)
      (fun t => (sPathX σ β κ φ φx y0 q0 t).2 / β ^ t) := by
  intro t
  have hb : β ^ t ≠ 0 := pow_ne_zero t hβ
  simp only [sPathX]
  rw [pow_succ]
  constructor <;> field_simp <;> ring

/-- The discounted output of the `sPathX` deviation is `y_t`. -/
theorem sPathX_scaled {σ β κ φ φx : ℝ} (hβ : β ≠ 0) (y0 q0 : ℝ) :
    (fun t => β ^ t * ((sPathX σ β κ φ φx y0 q0 t).1 / β ^ t)) =
      fun t => (sPathX σ β κ φ φx y0 q0 t).1 :=
  funext fun t => mul_div_cancel₀ _ (pow_ne_zero t hβ)

/-- Cochrane (2023), p. 421 and A1 (1.57): for `βφ ≠ 1` the discounted outputs `βᵗ x̃_t` of
perfect-foresight deviations are **exactly** the solutions of `y_{t+2} = T y_{t+1} − B y_t`. -/
theorem discY_iff {σ β κ φ φx : ℝ} (hσ : σ ≠ 0) (hβ : β ≠ 0) (hb : β * φ ≠ 1)
    (P : (ℕ → ℝ) → Prop) :
    (∃ x π : ℕ → ℝ, PFDevX σ β κ φ φx x π ∧ P (fun t => β ^ t * x t)) ↔
      ∃ y, Rec (1 + β + σ * κ + β * σ * φx) (β * (1 + σ * φx + σ * κ * φ)) y ∧ P y := by
  constructor
  · rintro ⟨x, π, hd, hP⟩
    exact ⟨_, y_recX hd, hP⟩
  · rintro ⟨y, hy, hP⟩
    have hb' : σ * (β * φ - 1) ≠ 0 := mul_ne_zero hσ (sub_ne_zero.mpr hb)
    set q0 := (y 1 - (β + β * σ * φx + σ * κ) * y 0) / (σ * (β * φ - 1))
    have hd := sPathX_pfDevX (σ := σ) (κ := κ) (φ := φ) (φx := φx) hβ (y 0) q0
    have hrec := y_recX hd
    rw [sPathX_scaled hβ] at hrec
    have heq : (fun t => (sPathX σ β κ φ φx (y 0) q0 t).1) = y := by
      refine rec_ext hrec hy rfl ?_
      simp only [sPathX, q0]
      field_simp
      ring
    refine ⟨_, _, hd, ?_⟩
    rw [sPathX_scaled hβ, heq]
    exact hP

/-- Cochrane (2023), p. 421: at `βφ = 1` the discounted outputs of perfect-foresight deviations
are exactly the geometric paths `c (β + βσφ_x + σκ)ᵗ`. -/
theorem discY_inv_beta {σ β κ φ φx : ℝ} (hβ : β ≠ 0) (hb : β * φ = 1) (P : (ℕ → ℝ) → Prop) :
    (∃ x π : ℕ → ℝ, PFDevX σ β κ φ φx x π ∧ P (fun t => β ^ t * x t)) ↔
      ∃ c, P (fun t => c * (β + β * σ * φx + σ * κ) ^ t) := by
  constructor
  · rintro ⟨x, π, hd, hP⟩
    refine ⟨x 0, ?_⟩
    have : (fun t => β ^ t * x t) = fun t => x 0 * (β + β * σ * φx + σ * κ) ^ t :=
      funext fun t => by rw [y_at_inv_betaX hd hb t, mul_comm]
    rwa [this] at hP
  · rintro ⟨c, hP⟩
    have hd := sPathX_pfDevX (σ := σ) (κ := κ) (φ := φ) (φx := φx) hβ c 0
    refine ⟨_, _, hd, ?_⟩
    have : (fun t => β ^ t * ((sPathX σ β κ φ φx c 0 t).1 / β ^ t)) =
        fun t => c * (β + β * σ * φx + σ * κ) ^ t := by
      funext t
      rw [y_at_inv_betaX hd hb t]
      simp [sPathX, mul_comm]
    rw [this]
    exact hP

/-! ### Geometric paths -/

/-- Some `c aᵗ` tends to `+∞` iff `a > 1`. -/
theorem geom_atTop_iff (a : ℝ) : (∃ c : ℝ, Tendsto (fun t : ℕ => c * a ^ t) atTop atTop) ↔
    1 < a := by
  constructor
  · rintro ⟨c, h⟩
    by_contra ha
    push Not at ha
    obtain ⟨T, hT⟩ := eventually_atTop.mp (h.eventually_gt_atTop 0)
    by_cases ha0 : a ≤ 0
    · have h1 := hT T le_rfl
      have h2 := hT (T + 1) (by omega)
      rw [pow_succ, ← mul_assoc] at h2
      nlinarith
    · push Not at ha0
      refine not_atTop_of_bounded ⟨|c|, fun t => ?_⟩ h
      rw [abs_mul, abs_pow, abs_of_pos ha0]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ha0.le ha)
  · intro ha
    exact ⟨1, by simpa using tendsto_pow_atTop_atTop_of_one_lt ha⟩

/-- Some `c aᵗ` tends to `−∞` iff `a > 1`. -/
theorem geom_atBot_iff (a : ℝ) : (∃ c : ℝ, Tendsto (fun t : ℕ => c * a ^ t) atTop atBot) ↔
    1 < a := by
  rw [← geom_atTop_iff]
  constructor
  · rintro ⟨c, h⟩
    exact ⟨-c, (tendsto_neg_atBot_atTop.comp h).congr fun t => by simp⟩
  · rintro ⟨c, h⟩
    exact ⟨-c, (tendsto_neg_atTop_atBot.comp h).congr fun t => by simp⟩

/-- Some `c aᵗ` is unbounded iff `|a| > 1`. -/
theorem geom_unbounded_iff (a : ℝ) :
    (∃ c : ℝ, ¬ ∃ M, ∀ t : ℕ, |c * a ^ t| ≤ M) ↔ 1 < |a| := by
  constructor
  · rintro ⟨c, h⟩
    by_contra ha
    push Not at ha
    refine h ⟨|c|, fun t => ?_⟩
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) ha)
  · intro ha
    exact ⟨1, pow_unbounded ha⟩

/-- Some `c aᵗ` fails to tend to zero iff `|a| ≥ 1`. -/
theorem geom_not_tendsto_iff (a : ℝ) :
    (∃ c : ℝ, ¬ Tendsto (fun t : ℕ => c * a ^ t) atTop (𝓝 0)) ↔ 1 ≤ |a| := by
  constructor
  · rintro ⟨c, h⟩
    by_contra ha
    push Not at ha
    refine h ?_
    have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha).const_mul c
    rwa [mul_zero] at this
  · intro ha
    exact ⟨1, pow_not_tendsto_zero ha⟩

/-! ### The characterisations for every `φ`, `φ_x` -/

/-- Cochrane (2023), p. 421 ("`βʲ x_{t+j} → ∞`"), with an output response: for `σ, κ, β > 0`
and **every** `φ`, `φ_x`, some perfect-foresight deviation has `βᵗ x̃_t → +∞` iff `φ < 1/β`
or (`T > 2` and `4B ≤ T²`), `T = 1 + β + σκ + βσφ_x`, `B = β(1 + σφ_x + σκφ)`. -/
theorem explodesX_pf_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ x π : ℕ → ℝ, PFDevX σ β κ φ φx x π ∧ Tendsto (fun t => β ^ t * x t) atTop atTop) ↔
      φ < 1 / β ∨ (2 < 1 + β + σ * κ + β * σ * φx ∧
        4 * (β * (1 + σ * φx + σ * κ * φ)) ≤ (1 + β + σ * κ + β * σ * φx) ^ 2) := by
  have ha := mul_pos hσ hκ
  have hp := p_one σ β κ φ φx
  have hlt : φ < 1 / β ↔ β * φ < 1 := by rw [lt_div_iff₀ hβ, mul_comm]
  by_cases hb : β * φ = 1
  · rw [discY_inv_beta hβ.ne' hb (fun y => Tendsto y atTop atTop), geom_atTop_iff]
    have hB : β * (1 + σ * φx + σ * κ * φ) = β + β * σ * φx + σ * κ := by
      linear_combination (σ * κ) * hb
    rw [hB, hlt]
    constructor
    · intro h; right; exact ⟨by linarith, by nlinarith [sq_nonneg (β + β * σ * φx + σ * κ - 1)]⟩
    · rintro (h | ⟨h, _⟩)
      · linarith
      · linarith
  · rw [discY_iff hσ.ne' hβ.ne' hb (fun y => Tendsto y atTop atTop), exists_atTop_iff, hlt, hp]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · left; nlinarith
      · rcases lt_or_gt_of_ne hb with h3 | h3
        · left; exact h3
        · right
          refine ⟨?_, h2⟩
          rcases h1.eq_or_lt with h4 | h4
          · exfalso
            have : 0 < σ * κ * (β * φ - 1) := mul_pos ha (by linarith)
            nlinarith
          · exact h4
    · rintro (h | ⟨h1, h2⟩)
      · left; exact mul_neg_of_pos_of_neg ha (by linarith)
      · right; exact ⟨h1.le, h2⟩

/-- Cochrane (2023), p. 421: the same condition characterises `βᵗ x̃_t → −∞`. -/
theorem explodesX_atBot_pf_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ x π : ℕ → ℝ, PFDevX σ β κ φ φx x π ∧ Tendsto (fun t => β ^ t * x t) atTop atBot) ↔
      φ < 1 / β ∨ (2 < 1 + β + σ * κ + β * σ * φx ∧
        4 * (β * (1 + σ * φx + σ * κ * φ)) ≤ (1 + β + σ * κ + β * σ * φx) ^ 2) := by
  rw [← explodesX_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨x, π, hd, h⟩
    refine ⟨fun t => -x t, fun t => -π t, fun t => ⟨?_, ?_⟩,
      (tendsto_neg_atBot_atTop.comp h).congr fun t => by simp⟩
    · linear_combination -(hd t).1
    · linear_combination -(hd t).2
  · rintro ⟨x, π, hd, h⟩
    refine ⟨fun t => -x t, fun t => -π t, fun t => ⟨?_, ?_⟩,
      (tendsto_neg_atTop_atBot.comp h).congr fun t => by simp⟩
    · linear_combination -(hd t).1
    · linear_combination -(hd t).2

/-- Cochrane (2023), p. 421 (real explosion as unboundedness of `βᵗ x̃_t`), with an output
response: for `σ, κ, β > 0` and every `φ`, `φ_x`, some perfect-foresight deviation has
`βᵗ x̃_t` unbounded iff `φ < 1/β`, `|B| > 1`, `1 + B + T < 0`, or `B = 1 ∧ T = −2`. -/
theorem unboundedX_pf_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ x π : ℕ → ℝ, PFDevX σ β κ φ φx x π ∧ ¬ ∃ M, ∀ t, |β ^ t * x t| ≤ M) ↔
      φ < 1 / β ∨ 1 < |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) < 0 ∨
        (β * (1 + σ * φx + σ * κ * φ) = 1 ∧ 1 + β + σ * κ + β * σ * φx = -2) := by
  have ha := mul_pos hσ hκ
  have hp := p_one σ β κ φ φx
  have hlt : φ < 1 / β ↔ β * φ < 1 := by rw [lt_div_iff₀ hβ, mul_comm]
  set T := 1 + β + σ * κ + β * σ * φx with hT
  set B := β * (1 + σ * φx + σ * κ * φ) with hBdef
  by_cases hb : β * φ = 1
  · rw [discY_inv_beta hβ.ne' hb (fun y => ¬ ∃ M, ∀ t, |y t| ≤ M), geom_unbounded_iff]
    have hB : B = β + β * σ * φx + σ * κ := by
      rw [hBdef]; linear_combination (σ * κ) * hb
    have hT' : T = 1 + B := by rw [hB, hT]; ring
    rw [← hB, hlt, hT']
    constructor
    · intro h; right; left; exact h
    · rintro (h | h | h | ⟨h1, h2⟩)
      · linarith
      · exact h
      · rw [abs_of_neg (by linarith)]; linarith
      · linarith
  · rw [discY_iff hσ.ne' hβ.ne' hb (fun y => ¬ ∃ M, ∀ t, |y t| ≤ M), exists_unbounded_iff, hlt]
    have hp' : 1 - T + B = σ * κ * (β * φ - 1) := hp
    constructor
    · rintro (h | h | ⟨h1, h2⟩)
      · right; left; rw [abs_of_pos (by linarith)]; exact h
      · rcases le_or_gt 0 T with hT0 | hT0
        · left
          rw [abs_of_nonneg hT0] at h
          have : σ * κ * (β * φ - 1) < 0 := by linarith
          by_contra hc
          push Not at hc
          nlinarith
        · right; right; left
          rw [abs_of_neg hT0] at h
          linarith
      · rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 2)).mp h2 with h3 | h3
        · exfalso
          have : σ * κ * (β * φ - 1) = 0 := by rw [← hp']; linarith
          rcases mul_eq_zero.mp this with h4 | h4
          · exact ha.ne' h4
          · exact hb (by linarith)
        · right; right; right; exact ⟨h1, h3⟩
    · rintro (h | h | h | ⟨h1, h2⟩)
      · right; left
        have : σ * κ * (β * φ - 1) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
        exact lt_of_lt_of_le (by linarith) (le_abs_self T)
      · rcases lt_abs.mp h with h' | h'
        · left; exact h'
        · right; left; exact lt_of_lt_of_le (by linarith) (abs_nonneg T)
      · right; left; exact lt_of_lt_of_le (by linarith) (neg_le_abs T)
      · right; right; exact ⟨h1, by rw [← hT, h2]; norm_num⟩

/-- Cochrane (2023), p. 421 (the real transversality condition `βᵗ x̃_t → 0`), with an output
response: for `σ, κ, β > 0` and every `φ`, `φ_x`, some perfect-foresight deviation violates it
iff `φ < 1/β`, `|B| ≥ 1`, or `1 + B + T ≤ 0`. -/
theorem tvcX_fails_pf_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ x π : ℕ → ℝ, PFDevX σ β κ φ φx x π ∧ ¬ Tendsto (fun t => β ^ t * x t) atTop (𝓝 0)) ↔
      φ < 1 / β ∨ 1 ≤ |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) ≤ 0 := by
  have ha := mul_pos hσ hκ
  have hp := p_one σ β κ φ φx
  have hlt : φ < 1 / β ↔ β * φ < 1 := by rw [lt_div_iff₀ hβ, mul_comm]
  set T := 1 + β + σ * κ + β * σ * φx with hT
  set B := β * (1 + σ * φx + σ * κ * φ) with hBdef
  by_cases hb : β * φ = 1
  · rw [discY_inv_beta hβ.ne' hb (fun y => ¬ Tendsto y atTop (𝓝 0)), geom_not_tendsto_iff]
    have hB : B = β + β * σ * φx + σ * κ := by
      rw [hBdef]; linear_combination (σ * κ) * hb
    have hT' : T = 1 + B := by rw [hB, hT]; ring
    rw [← hB, hlt, hT']
    constructor
    · intro h; right; left; exact h
    · rintro (h | h | h)
      · linarith
      · exact h
      · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [discY_iff hσ.ne' hβ.ne' hb (fun y => ¬ Tendsto y atTop (𝓝 0)),
      exists_not_tendsto_zero_iff, hlt]
    have hp' : 1 - T + B = σ * κ * (β * φ - 1) := hp
    unfold SchurStable
    constructor
    · intro h
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2, h3⟩ := hc
      refine h ⟨h2, abs_lt.mpr ⟨by linarith, ?_⟩⟩
      have h4 : β * φ - 1 > 0 := by
        rcases lt_or_gt_of_ne hb with h5 | h5
        · linarith
        · linarith
      have : 0 < σ * κ * (β * φ - 1) := mul_pos ha h4
      linarith
    · rintro (h | h | h) ⟨h1, h2⟩
      · have : σ * κ * (β * φ - 1) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
        have := (abs_lt.mp h2).2
        linarith
      · linarith
      · have := (abs_lt.mp h2).1
        linarith

/-! ### The deviation system (17.29)–(17.32) with output response -/

/-- Cochrane (2023), p. 421, with an output response, for the deviation system (17.29)–(17.32):
some solution has `βᵗ x̃_t → +∞` iff `φ < 1/β` or (`T > 2` and `4B ≤ T²`). -/
theorem explodesX_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ φx i r x π ∧
        Tendsto (fun t => β ^ t * x t ()) atTop atTop) ↔
      φ < 1 / β ∨ (2 < 1 + β + σ * κ + β * σ * φx ∧
        4 * (β * (1 + σ * φx + σ * κ * φ)) ≤ (1 + β + σ * κ + β * σ * φx) ^ 2) :=
  (exists_deviation_iff_X σ β κ φ φx fun y => Tendsto (fun t => β ^ t * y t) atTop atTop).trans
    (explodesX_pf_iff hσ hκ hβ)

/-- Cochrane (2023), p. 421, with an output response, for the deviation system: some solution
has `βᵗ x̃_t` unbounded iff `φ < 1/β`, `|B| > 1`, `1 + B + T < 0`, or `B = 1 ∧ T = −2`. -/
theorem unboundedX_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ φx i r x π ∧
        ¬ ∃ M, ∀ t, |β ^ t * x t ()| ≤ M) ↔
      φ < 1 / β ∨ 1 < |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) < 0 ∨
        (β * (1 + σ * φx + σ * κ * φ) = 1 ∧ 1 + β + σ * κ + β * σ * φx = -2) :=
  (exists_deviation_iff_X σ β κ φ φx fun y => ¬ ∃ M, ∀ t, |β ^ t * y t| ≤ M).trans
    (unboundedX_pf_iff hσ hκ hβ)

/-- Cochrane (2023), p. 421, with an output response, for the deviation system: some solution
violates the real transversality condition iff `φ < 1/β`, `|B| ≥ 1`, or `1 + B + T ≤ 0`. -/
theorem tvcX_fails_iff {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ φx i r x π ∧
        ¬ Tendsto (fun t => β ^ t * x t ()) atTop (𝓝 0)) ↔
      φ < 1 / β ∨ 1 ≤ |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) ≤ 0 :=
  (exists_deviation_iff_X σ β κ φ φx fun y => ¬ Tendsto (fun t => β ^ t * y t) atTop (𝓝 0)).trans
    (tvcX_fails_pf_iff hσ hκ hβ)

/-! ### Consistency with `φ_x = 0` -/

/-- Cochrane (2023), p. 421: at `φ_x = 0` the explosion condition is that of
`FullModelTidy.explodes_atTop_iff`. -/
theorem explodes_cond_phix_zero (σ β κ φ : ℝ) :
    (φ < 1 / β ∨ (2 < 1 + β + σ * κ + β * σ * 0 ∧
        4 * (β * (1 + σ * 0 + σ * κ * φ)) ≤ (1 + β + σ * κ + β * σ * 0) ^ 2)) ↔
      φ < 1 / β ∨ (1 < β + σ * κ ∧ 4 * (β * (1 + σ * κ * φ)) ≤ (1 + β + σ * κ) ^ 2) := by
  simp only [mul_zero, add_zero]
  constructor <;> rintro (h | ⟨h1, h2⟩)
  · exact Or.inl h
  · exact Or.inr ⟨by linarith, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨by linarith, h2⟩

/-- Cochrane (2023), p. 421: at `φ_x = 0` (with `σ, κ, β > 0`) the unboundedness condition is
that of `FullModelTidy.unbounded_iff`, `φ < 1/β ∨ β(1 + σκφ) > 1`. -/
theorem unbounded_cond_phix_zero {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (φ < 1 / β ∨ 1 < |β * (1 + σ * 0 + σ * κ * φ)| ∨
        1 + β * (1 + σ * 0 + σ * κ * φ) + (1 + β + σ * κ + β * σ * 0) < 0 ∨
        (β * (1 + σ * 0 + σ * κ * φ) = 1 ∧ 1 + β + σ * κ + β * σ * 0 = -2)) ↔
      φ < 1 / β ∨ 1 < β * (1 + σ * κ * φ) := by
  have ha := mul_pos hσ hκ
  have hlt : φ < 1 / β ↔ β * φ < 1 := by rw [lt_div_iff₀ hβ, mul_comm]
  simp only [mul_zero, add_zero]
  rw [hlt]
  constructor
  · rintro (h | h | h | ⟨_, h2⟩)
    · exact Or.inl h
    · rcases lt_abs.mp h with h' | h'
      · exact Or.inr h'
      · left; nlinarith
    · left; nlinarith
    · linarith
  · rintro (h | h)
    · exact Or.inl h
    · right; left; exact lt_of_lt_of_le h (le_abs_self _)

/-- Cochrane (2023), p. 421: at `φ_x = 0` (with `σ, κ, β > 0`) the condition for a violation of
the real transversality condition is that of `FullModelTidy.tvc_fails_iff`,
`φ < 1/β ∨ β(1 + σκφ) ≥ 1`. -/
theorem tvc_cond_phix_zero {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (φ < 1 / β ∨ 1 ≤ |β * (1 + σ * 0 + σ * κ * φ)| ∨
        1 + β * (1 + σ * 0 + σ * κ * φ) + (1 + β + σ * κ + β * σ * 0) ≤ 0) ↔
      φ < 1 / β ∨ 1 ≤ β * (1 + σ * κ * φ) := by
  have ha := mul_pos hσ hκ
  have hlt : φ < 1 / β ↔ β * φ < 1 := by rw [lt_div_iff₀ hβ, mul_comm]
  simp only [mul_zero, add_zero]
  rw [hlt]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · rcases le_abs'.mp h with h' | h'
      · left; nlinarith
      · exact Or.inr h'
    · left; nlinarith
  · rintro (h | h)
    · exact Or.inl h
    · right; left; exact h.trans (le_abs_self _)

/-! ### What changes with an output response -/

/-- Cochrane (2023), p. 421: for every output response `φ_x`, `φ < 1/β` still gives a
deviation with `βᵗ x̃_t → +∞` (the condition `1 − T + B = σκ(βφ − 1) < 0` does not involve
`φ_x`). -/
theorem explodes_of_lt_inv_beta {σ β κ φ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hφ : φ < 1 / β) (φx : ℝ) :
    ∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight σ β κ φ φx i r x π ∧
      Tendsto (fun t => β ^ t * x t ()) atTop atTop :=
  (explodesX_iff hσ hκ hβ).mpr (Or.inl hφ)

/-- Cochrane (2023), p. 421, at the calibration of Fig. 17.8, p. 416 (`β = 0.95`, `σ = 1`,
`κ = 1/2`, `φ = 1.5`), with the output response `φ_x = 1/2`: the deviation system is
determinate, and some deviation has `βᵗ x̃_t → +∞` — a monotone real explosion, which with
`φ_x = 0` does not exist (`FullModelTidy.book_calibration_oscillates`). -/
theorem book_calibration_output_response :
    Determinate perfectForesight 1 (19 / 20) (1 / 2) (3 / 2) (1 / 2) ∧
      ∃ i r x π : ℕ → Unit → ℝ,
        Deviation perfectForesight 1 (19 / 20) (1 / 2) (3 / 2) (1 / 2) i r x π ∧
          Tendsto (fun t => (19 / 20 : ℝ) ^ t * x t ()) atTop atTop := by
  refine ⟨(determinate_iff_explicit perfectForesight (by norm_num)).mpr (Or.inl ?_),
    (explodesX_iff one_pos (by norm_num) (by norm_num)).mpr (Or.inr ⟨by norm_num, by norm_num⟩)⟩
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [abs_of_pos (by norm_num)]
  norm_num

/-- Cochrane (2023), p. 421: with an output response the determinant condition alone no
longer decides. At `β = 1/2`, `σ = κ = 1`, `φ = 10 ≥ 1/β`, `φ_x = −10`, `B = β(1 + σφ_x + σκφ)
= 1/2 < 1`, yet `1 + B + T < 0` and some deviation has unbounded `βᵗ x̃_t`. -/
theorem explosion_with_small_det :
    (1 / 2 : ℝ) * (1 + 1 * (-10) + 1 * 1 * 10) = 1 / 2 ∧ (10 : ℝ) ≥ 1 / (1 / 2) ∧
      ∃ i r x π : ℕ → Unit → ℝ, Deviation perfectForesight 1 (1 / 2) 1 10 (-10) i r x π ∧
        ¬ ∃ M, ∀ t, |(1 / 2 : ℝ) ^ t * x t ()| ≤ M := by
  refine ⟨by norm_num, by norm_num, (unboundedX_iff one_pos one_pos (by norm_num)).mpr ?_⟩
  right; right; left
  norm_num

/-! ### Every expectation system -/

/-- Cochrane (2023), p. 421 ("`E_t βʲ x_{t+j}`"): for any expectation system, the expected
path of a deviation, `j ↦ (E_s x̃_{s+j}(ω), E_s π̃_{s+j}(ω))`, is a perfect-foresight
deviation, for every date `s` and state `ω`. -/
theorem expected_pfDevX {Ω : Type*} (𝔼 : ExpectationSystem Ω) {σ β κ φ φx : ℝ}
    {i r x π : ℕ → Ω → ℝ} (h : Deviation 𝔼 σ β κ φ φx i r x π) (s : ℕ) (ω : Ω) :
    PFDevX σ β κ φ φx (fun j => 𝔼.E s (x (s + j)) ω) (fun j => 𝔼.E s (π (s + j)) ω) := by
  intro j
  obtain ⟨h1, h2, h3, h4⟩ := h (s + j)
  have hle : s ≤ s + j := Nat.le_add_right s j
  have e1 := congrFun (congrArg (𝔼.E s) h1) ω
  have e2 := congrFun (congrArg (𝔼.E s) h2) ω
  have e3 := congrFun (congrArg (𝔼.E s) h3) ω
  have e4 := congrFun (congrArg (𝔼.E s) h4) ω
  simp only [map_add, map_sub, map_smul, 𝔼.tower hle, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4
  have hs : s + (j + 1) = s + j + 1 := rfl
  simp only [hs]
  exact ⟨e3, by linear_combination e2 + σ * (e1 - e4)⟩

/-- Cochrane (2023), p. 420: a perfect-foresight deviation is a deterministic deviation under any
expectation system. -/
theorem const_deviation {Ω : Type*} (𝔼 : ExpectationSystem Ω) {σ β κ φ φx : ℝ} {x π : ℕ → ℝ}
    (hd : PFDevX σ β κ φ φx x π) :
    Deviation 𝔼 σ β κ φ φx (fun t _ => φ * π t + φx * x t)
      (fun t _ => φ * π t + φx * x t - π (t + 1)) (fun t _ => x t) (fun t _ => π t) := by
  intro t
  rw [𝔼.const, 𝔼.const]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · ring
  · linarith [(hd t).2]
  · exact (hd t).1

/-- Cochrane (2023), p. 421 ("real explosions … so `E_t βʲ x_{t+j} → ∞`"), under **any**
expectation system on a nonempty state space, with an output response: some deviation has, at
some date `s` and state `ω`, `βʲ E_s x̃_{s+j} → +∞` iff `φ < 1/β` or (`T > 2` and `4B ≤ T²`). -/
theorem explodes_uncertainty_iff {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, Deviation 𝔼 σ β κ φ φx i r x π ∧
        ∃ s ω, Tendsto (fun j => β ^ j * 𝔼.E s (x (s + j)) ω) atTop atTop) ↔
      φ < 1 / β ∨ (2 < 1 + β + σ * κ + β * σ * φx ∧
        4 * (β * (1 + σ * φx + σ * κ * φ)) ≤ (1 + β + σ * κ + β * σ * φx) ^ 2) := by
  rw [← explodesX_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, s, ω, h⟩
    exact ⟨_, _, expected_pfDevX 𝔼 hd s ω, h⟩
  · rintro ⟨x, π, hd, h⟩
    refine ⟨_, _, _, _, const_deviation 𝔼 hd, 0, Classical.arbitrary Ω, ?_⟩
    simpa [𝔼.const] using h

/-- Cochrane (2023), p. 421, under any expectation system on a nonempty state space: some
deviation has, at some date and state, unbounded expected discounted output `βʲ E_s x̃_{s+j}`
iff `φ < 1/β`, `|B| > 1`, `1 + B + T < 0`, or `B = 1 ∧ T = −2`. -/
theorem unbounded_uncertainty_iff {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, Deviation 𝔼 σ β κ φ φx i r x π ∧
        ∃ s ω, ¬ ∃ M, ∀ j, |β ^ j * 𝔼.E s (x (s + j)) ω| ≤ M) ↔
      φ < 1 / β ∨ 1 < |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) < 0 ∨
        (β * (1 + σ * φx + σ * κ * φ) = 1 ∧ 1 + β + σ * κ + β * σ * φx = -2) := by
  rw [← unboundedX_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, s, ω, h⟩
    exact ⟨_, _, expected_pfDevX 𝔼 hd s ω, h⟩
  · rintro ⟨x, π, hd, h⟩
    refine ⟨_, _, _, _, const_deviation 𝔼 hd, 0, Classical.arbitrary Ω, ?_⟩
    simpa [𝔼.const] using h

/-- Cochrane (2023), p. 421 (the real transversality condition in expectation,
`E_s βʲ x̃_{s+j} → 0`), under any expectation system on a nonempty state space: some deviation
violates it at some date and state iff `φ < 1/β`, `|B| ≥ 1`, or `1 + B + T ≤ 0`. -/
theorem tvc_uncertainty_iff {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {σ β κ φ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    (∃ i r x π : ℕ → Ω → ℝ, Deviation 𝔼 σ β κ φ φx i r x π ∧
        ∃ s ω, ¬ Tendsto (fun j => β ^ j * 𝔼.E s (x (s + j)) ω) atTop (𝓝 0)) ↔
      φ < 1 / β ∨ 1 ≤ |β * (1 + σ * φx + σ * κ * φ)| ∨
        1 + β * (1 + σ * φx + σ * κ * φ) + (1 + β + σ * κ + β * σ * φx) ≤ 0 := by
  rw [← tvcX_fails_pf_iff hσ hκ hβ]
  constructor
  · rintro ⟨i, r, x, π, hd, s, ω, h⟩
    exact ⟨_, _, expected_pfDevX 𝔼 hd s ω, h⟩
  · rintro ⟨x, π, hd, h⟩
    refine ⟨_, _, _, _, const_deviation 𝔼 hd, 0, Classical.arbitrary Ω, ?_⟩
    simpa [𝔼.const] using h

end Cochrane.KeynesianStickyPrices.TidyR5RealExplosions
