/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.StaticIS

/-!
# Policy rules under adaptive and rational expectations

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.2 (p. 401) and §17.3
"Rational expectations responses with policy rules", pp. 401–403.

Adding the rule `i_t = φ π_t + u_{i,t}` to the static model gives (17.9)
`π_t = (1+σκ)/(1+σκφ) πᵉ_t − σκ/(1+σκφ) u_{i,t}`.

* Adaptive expectations (17.10): the solution is always unique given `π_{−1}`
  (`adaptiveRule_existsUnique`); it is stable iff `|1 + σκ| < |1 + σκφ|`, i.e. iff
  `φ > 1` or `φ < −1 − 2/(σκ)` (`adaptiveStable_iff`). Survey error **E7** (confirmed): the book's
  "the Taylor rule `|φ| > 1` stabilizes" is false for `−1 − 2/(σκ) ≤ φ < −1`
  (`printed_abs_phi_gt_one_stabilizes_false`: `σκ = 1/2`, `φ = −3/2` gives coefficient 6); the
  book's "`|φ| < 1` produces unstable inflation" is true (`passive_unstable`).
* Rational expectations (17.11): the model has exactly one bounded equilibrium for every bounded
  disturbance iff `φ > 1` or `φ < −1 − 2/(σκ)` (`reDeterminate_iff`). **E7** again: "passive
  policy `φ < 1` produces … indeterminate inflation" fails for `φ < −1 − 2/(σκ)`
  (`printed_passive_indeterminate_false`, `φ = −6`, `σκ = 1/2`); the coefficient of (17.11) has
  modulus below one iff `−1 − 2/(σκ) < φ < 1` (`re_coeff_abs_lt_one_iff`).
* The forward solution of p. 403 (`forward_solution`), the frictionless limit `κ → ∞` of
  (17.11), which is (16.4) (`tendsto_coeff_17_11`).
* p. 401: with `i_t = i*_t + φ(π_t − π*_t)` and `φ > 1` the central bank selects any
  equilibrium `π*` of the peg model, i.e. any value of unexpected inflation
  (`rule_selects`, `rule_selects_any_delta`).
-/

namespace Cochrane.KeynesianStickyPrices.RulesAdaptiveRE

open Filter Topology StaticIS ForwardSolution

variable {Ω : Type*}

/-! ### The key inequality -/

/-- Cochrane (2023), p. 402 (survey error E7): for `s = σκ > 0`,
`|1 + s| < |1 + sφ|` iff `φ > 1` or `φ < −1 − 2/s`. -/
theorem abs_lt_abs_iff {s φ : ℝ} (hs : 0 < s) :
    |1 + s| < |1 + s * φ| ↔ 1 < φ ∨ φ < -1 - 2 / s := by
  rw [← sq_lt_sq, ← sub_pos]
  have e : (1 + s * φ) ^ 2 - (1 + s) ^ 2 = s * ((φ - 1) * (s * φ + s + 2)) := by ring
  rw [e, mul_pos_iff_of_pos_left hs, mul_pos_iff]
  have e2 : φ < -1 - 2 / s ↔ s * φ + s + 2 < 0 := by
    have : -1 - 2 / s = (-s - 2) / s := by field_simp
    rw [this, lt_div_iff₀ hs]
    constructor <;> intro h <;> linarith
  rw [e2]
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr h2
  · rintro (h1 | h2)
    · exact Or.inl ⟨by linarith, by nlinarith⟩
    · refine Or.inr ⟨?_, h2⟩
      nlinarith

/-- Cochrane (2023), p. 402 (survey error E7): for `σκ > 0` and `1 + σκφ ≠ 0`, the coefficient
`(1+σκ)/(1+σκφ)` of (17.10) has modulus below one iff `φ > 1` or `φ < −1 − 2/(σκ)`. -/
theorem abs_coeff_lt_one_iff {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (h : 1 + σ * κ * φ ≠ 0) :
    |(1 + σ * κ) / (1 + σ * κ * φ)| < 1 ↔ 1 < φ ∨ φ < -1 - 2 / (σ * κ) := by
  rw [abs_div, div_lt_one (abs_pos.mpr h)]
  exact abs_lt_abs_iff hσκ

/-! ### (17.9) and adaptive expectations (17.10) -/

/-- Cochrane (2023), eq. (17.9), p. 402: with the rule `i_t = φ π_t + u_t`, (17.5) is
`π_t = (1+σκ)/(1+σκφ) πᵉ_t − σκ/(1+σκφ) u_t`. -/
theorem eq_17_9 {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) (πe π u : ℕ → Ω → ℝ) :
    (∀ t ω, π t ω = -(σ * κ) * (φ * π t ω + u t ω) + (1 + σ * κ) * πe t ω) ↔
      ∀ t ω, π t ω = (1 + σ * κ) / (1 + σ * κ * φ) * πe t ω -
        σ * κ / (1 + σ * κ * φ) * u t ω := by
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor
  · intro e; field_simp; linear_combination e
  · intro e; field_simp at e; linear_combination e

/-- Cochrane (2023), eq. (17.10), p. 402: the adaptive model (17.6) with the rule
`i_t = φ π_t + u_t`. -/
def AdaptiveRule (σ κ φ : ℝ) (π0 : Ω → ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  AdaptiveEq σ κ π0 (fun t ω => φ * π t ω + u t ω) π

/-- Cochrane (2023), eq. (17.10), p. 402:
`π_t = (1+σκ)/(1+σκφ) π_{t−1} − σκ/(1+σκφ) u_t`. -/
theorem adaptiveRule_iff_17_10 {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) (π0 : Ω → ℝ)
    (u π : ℕ → Ω → ℝ) :
    AdaptiveRule σ κ φ π0 u π ↔ ∀ t ω, π t ω = (1 + σ * κ) / (1 + σ * κ * φ) *
      lagged π0 π t ω - σ * κ / (1 + σ * κ * φ) * u t ω := by
  rw [← eq_17_9 h]
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro e <;> linear_combination e

/-- Cochrane (2023), eq. (17.10), p. 402: the solution of (17.10) built from `π_{−1}`. -/
noncomputable def adaptiveRulePath (σ κ φ : ℝ) (π0 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => (1 + σ * κ) / (1 + σ * κ * φ) * π0 ω - σ * κ / (1 + σ * κ * φ) * u 0 ω
  | t + 1 => fun ω => (1 + σ * κ) / (1 + σ * κ * φ) * adaptiveRulePath σ κ φ π0 u t ω -
      σ * κ / (1 + σ * κ * φ) * u (t + 1) ω

/-- Cochrane (2023), p. 402, "there is only one equilibrium": given `π_{−1}`, (17.10) has
exactly one solution for every rule with `1 + σκφ ≠ 0`. -/
theorem adaptiveRule_existsUnique {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) (π0 : Ω → ℝ)
    (u : ℕ → Ω → ℝ) : ∃! π, AdaptiveRule σ κ φ π0 u π := by
  refine ⟨adaptiveRulePath σ κ φ π0 u, (adaptiveRule_iff_17_10 h π0 u _).mpr fun t ω => ?_,
    fun π hπ => ?_⟩
  · cases t <;> rfl
  · have e := (adaptiveRule_iff_17_10 h π0 u π).mp hπ
    funext t ω
    induction t with
    | zero => rw [e 0 ω]; rfl
    | succ t ih => rw [e (t + 1) ω]; simp only [lagged]; rw [ih]; rfl

/-- Cochrane (2023), eq. (17.10), p. 402: with no disturbance, `π_t = cᵗ⁺¹ π_{−1}` with
`c = (1+σκ)/(1+σκφ)`. -/
theorem adaptiveRule_homog {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ π0 0 π) (t : ℕ) (ω : Ω) :
    π t ω = ((1 + σ * κ) / (1 + σ * κ * φ)) ^ (t + 1) * π0 ω := by
  have e := (adaptiveRule_iff_17_10 h π0 0 π).mp hπ
  induction t with
  | zero => rw [e 0 ω]; simp [lagged]
  | succ t ih => rw [e (t + 1) ω]; simp only [lagged]; rw [ih]; simp; ring

/-- Cochrane (2023), p. 402: stability of the adaptive model with a rule — after any initial
condition, inflation returns to zero when there are no further disturbances ("Any shocks …
eventually die out"). -/
def AdaptiveStable (Ω : Type*) (σ κ φ : ℝ) : Prop :=
  ∀ (π0 : Ω → ℝ) (π : ℕ → Ω → ℝ), AdaptiveRule σ κ φ π0 0 π →
    ∀ ω, Tendsto (fun t => π t ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 402 (survey error E7, corrected): the adaptive model with the rule
`i = φπ + u` is stable iff `φ > 1` or `φ < −1 − 2/(σκ)`. -/
theorem adaptiveStable_iff [Nonempty Ω] {σ κ φ : ℝ} (hσκ : 0 < σ * κ)
    (h : 1 + σ * κ * φ ≠ 0) :
    AdaptiveStable Ω σ κ φ ↔ 1 < φ ∨ φ < -1 - 2 / (σ * κ) := by
  rw [← abs_coeff_lt_one_iff hσκ h]
  set c := (1 + σ * κ) / (1 + σ * κ * φ)
  constructor
  · intro hs
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    obtain ⟨π, hπ, -⟩ := adaptiveRule_existsUnique h (fun _ => (1 : ℝ)) 0
    have hl := hs _ π hπ ω
    have he : (fun t => π t ω) = fun t => c ^ (t + 1) := funext fun t => by
      rw [adaptiveRule_homog h hπ t ω, mul_one]
    rw [he] at hl
    have hl' : Tendsto (fun t => c ^ t) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mp hl
    exact tendsto_pow_atTop_nhds_zero_iff.mp hl'
  · intro hc π0 π hπ ω
    have he : (fun t => π t ω) = fun t => c ^ (t + 1) * π0 ω := funext fun t =>
      adaptiveRule_homog h hπ t ω
    rw [he]
    have h0 := (tendsto_add_atTop_iff_nat 1).mpr (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hc)
    simpa using h0.mul_const (π0 ω)

/-- Cochrane (2023), p. 402, "Any 'passive' monetary policy `|φ| < 1` produces unstable …
inflation. The coefficient on lagged inflation is above one" (true, in modulus). -/
theorem passive_unstable {σ κ φ : ℝ} (hσκ : 0 < σ * κ) (h : 1 + σ * κ * φ ≠ 0)
    (hφ : |φ| < 1) : 1 < |(1 + σ * κ) / (1 + σ * κ * φ)| := by
  rw [abs_div, one_lt_div (abs_pos.mpr h)]
  rw [abs_lt] at hφ
  rw [abs_of_pos (by linarith : 0 < 1 + σ * κ), abs_lt]
  constructor <;> nlinarith

/-- Cochrane (2023), p. 402: when the coefficient exceeds one in modulus, every undisturbed path
starting away from zero diverges, `|π_t| → ∞`. -/
theorem unstable_diverges {σ κ φ : ℝ} (h : 1 + σ * κ * φ ≠ 0)
    (hc : 1 < |(1 + σ * κ) / (1 + σ * κ * φ)|) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (hπ : AdaptiveRule σ κ φ π0 0 π) {ω : Ω} (hω : π0 ω ≠ 0) :
    Tendsto (fun t => |π t ω|) atTop atTop := by
  have he : (fun t => |π t ω|) =
      fun t => |(1 + σ * κ) / (1 + σ * κ * φ)| ^ (t + 1) * |π0 ω| := funext fun t => by
    rw [adaptiveRule_homog h hπ t ω, abs_mul, abs_pow]
  rw [he]
  exact Tendsto.atTop_mul_const (abs_pos.mpr hω)
    ((tendsto_pow_atTop_atTop_of_one_lt hc).comp (tendsto_add_atTop_nat 1))

/-- Cochrane (2023), p. 402, survey error E7: the printed claim "The Taylor rule `|φ| > 1`
stabilizes" is false. With `σ = 1`, `κ = 1/2` and `φ = −3/2` (so `|φ| > 1`) the coefficient of
(17.10) is `6`, and inflation spirals away. -/
theorem printed_abs_phi_gt_one_stabilizes_false :
    1 < |(-3 / 2 : ℝ)| ∧ (1 + 1 * (1 / 2)) / (1 + 1 * (1 / 2) * (-3 / 2)) = (6 : ℝ) ∧
      ¬ (1 < (-3 / 2 : ℝ) ∨ (-3 / 2 : ℝ) < -1 - 2 / (1 * (1 / 2))) := by
  refine ⟨by norm_num [abs_of_neg], by norm_num, by norm_num⟩

/-- Cochrane (2023), p. 402 (boundary case of E7): at `φ = −1 − 2/(σκ)` the coefficient of
(17.10) is exactly `−1`: undisturbed inflation oscillates forever, neither stable nor
explosive. -/
theorem boundary_coeff {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    (1 + σ * κ) / (1 + σ * κ * (-1 - 2 / (σ * κ))) = -1 := by
  have : σ * κ ≠ 0 := hσκ.ne'
  have hσ : σ ≠ 0 := left_ne_zero_of_mul this
  have hκ : κ ≠ 0 := right_ne_zero_of_mul this
  have h2 : 1 + σ * κ * (-1 - 2 / (σ * κ)) = -(1 + σ * κ) := by field_simp; ring
  rw [h2, div_neg, div_self (by linarith)]

/-- Cochrane (2023), p. 402: in the stable case bounded disturbances produce bounded inflation,
whatever the initial condition. -/
theorem adaptiveRule_bounded {σ κ φ B M : ℝ} (h : 1 + σ * κ * φ ≠ 0)
    (hc : |(1 + σ * κ) / (1 + σ * κ * φ)| < 1) {π0 : Ω → ℝ} {u π : ℕ → Ω → ℝ}
    (hπ0 : ∀ ω, |π0 ω| ≤ B) (hu : ∀ t ω, |u t ω| ≤ M) (hπ : AdaptiveRule σ κ φ π0 u π) :
    BoundedProc π := by
  have e := (adaptiveRule_iff_17_10 h π0 u π).mp hπ
  set c := (1 + σ * κ) / (1 + σ * κ * φ)
  set k := σ * κ / (1 + σ * κ * φ)
  set K := |B| + |k| * |M| / (1 - |c|) with hK
  have h1c : 0 < 1 - |c| := by linarith
  have hKc : (1 - |c|) * K = (1 - |c|) * |B| + |k| * |M| := by rw [hK]; field_simp
  have hB : 0 ≤ (1 - |c|) * |B| := mul_nonneg h1c.le (abs_nonneg _)
  have hstep : ∀ x : ℝ, |x| ≤ K → ∀ t ω, |c * x - k * u t ω| ≤ K := fun x hx t ω => by
    calc |c * x - k * u t ω| ≤ |c| * |x| + |k| * |u t ω| := by
          rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ |c| * K + |k| * |M| :=
          add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg c))
            (mul_le_mul_of_nonneg_left ((hu t ω).trans (le_abs_self M)) (abs_nonneg k))
      _ ≤ K := by nlinarith [abs_nonneg c]
  have hK0 : |B| ≤ K := by
    have : 0 ≤ |k| * |M| / (1 - |c|) := by positivity
    linarith
  refine ⟨K, fun t ω => ?_⟩
  induction t generalizing ω with
  | zero => rw [e 0 ω]; exact hstep _ (((hπ0 ω).trans (le_abs_self B)).trans hK0) 0 ω
  | succ t ih => rw [e (t + 1) ω]; exact hstep _ (ih ω) (t + 1) ω

/-! ### Rational expectations (17.11) -/

/-- Cochrane (2023), eqs. (17.9) and (17.11), p. 402: the rational-expectations model (17.5)
with `πᵉ_t = E_t π_{t+1}` and the rule `i_t = φ π_t + u_t`. -/
def RERule (𝔼 : ExpectationSystem Ω) (σ κ φ : ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  REModel 𝔼 σ κ (fun t ω => φ * π t ω + u t ω) π

/-- Cochrane (2023), eq. (17.11), p. 402:
`E_t π_{t+1} = (1+σκφ)/(1+σκ) π_t + σκ/(1+σκ) u_t`. -/
theorem reRule_iff_17_11 (𝔼 : ExpectationSystem Ω) {σ κ φ : ℝ} (h : 1 + σ * κ ≠ 0)
    (u π : ℕ → Ω → ℝ) :
    RERule 𝔼 σ κ φ u π ↔ 𝔼.Adapted π ∧ ∀ t ω, 𝔼.E t (π (t + 1)) ω =
      (1 + σ * κ * φ) / (1 + σ * κ) * π t ω + σ * κ / (1 + σ * κ) * u t ω := by
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun ω => ?_)
  constructor
  · intro e; simp only at e; field_simp; linear_combination -e
  · intro e; field_simp at e; simp only; linear_combination -e

/-- Cochrane (2023), eq. (17.11), p. 402, in the undivided form of the core:
`(1 + σκφ) π_t = (1 + σκ) E_t π_{t+1} − σκ u_t`. -/
theorem reRule_iff_scalar (𝔼 : ExpectationSystem Ω) (σ κ φ : ℝ) (u π : ℕ → Ω → ℝ) :
    RERule 𝔼 σ κ φ u π ↔ 𝔼.Adapted π ∧
      ScalarEq 𝔼 (1 + σ * κ * φ) (1 + σ * κ) (fun t => (-(σ * κ)) • u t) π := by
  refine and_congr Iff.rfl ⟨fun e t => funext fun ω => ?_, fun e t ω => ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination e t ω
  · have := congrFun (e t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this

/-- Cochrane (2023), p. 402: determinacy of the rational-expectations model with a rule — for
every bounded adapted disturbance there is exactly one bounded equilibrium. -/
def REDeterminate (𝔼 : ExpectationSystem Ω) (σ κ φ : ℝ) : Prop :=
  ∀ u : ℕ → Ω → ℝ, BoundedProc u → 𝔼.Adapted u → ∃! π, BoundedProc π ∧ RERule 𝔼 σ κ φ u π

/-- Cochrane (2023), p. 402 (survey error E7, corrected): (17.11) is determinate iff `φ > 1` or
`φ < −1 − 2/(σκ)`. -/
theorem reDeterminate_iff (𝔼 : ExpectationSystem Ω) [Nonempty Ω] {σ κ φ : ℝ}
    (hσκ : 0 < σ * κ) : REDeterminate 𝔼 σ κ φ ↔ 1 < φ ∨ φ < -1 - 2 / (σ * κ) := by
  rw [← abs_lt_abs_iff hσκ]
  constructor
  · intro hd
    by_contra hc
    push Not at hc
    have hB : 1 + σ * κ ≠ 0 := by linarith
    obtain ⟨hh, hhb⟩ := scalar_homog 𝔼 hc hB
    have hz : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
    obtain ⟨π, -, hu⟩ := hd 0 ⟨0, fun _ _ => by simp⟩ hz
    have hf : (fun t => (-(σ * κ)) • (0 : ℕ → Ω → ℝ) t) = 0 := by funext t; simp
    have s0 : RERule 𝔼 σ κ φ 0 0 :=
      (reRule_iff_scalar 𝔼 σ κ φ 0 0).mpr ⟨hz, by rw [hf]; intro t; simp⟩
    have s1 : RERule 𝔼 σ κ φ 0 (fun t _ => ((1 + σ * κ * φ) / (1 + σ * κ)) ^ t) :=
      (reRule_iff_scalar 𝔼 σ κ φ 0 _).mpr ⟨fun t => 𝔼.const t _, by rw [hf]; exact hh⟩
    have e := (hu _ ⟨hhb, s1⟩).trans (hu 0 ⟨⟨0, fun _ _ => by simp⟩, s0⟩).symm
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun e 0) ω
    simp at this
  · intro hc u ⟨M, hM⟩ hua
    have hf : ∀ t ω, |(fun t => (-(σ * κ)) • u t) t ω| ≤ σ * κ * M := fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hσκ]
      exact mul_le_mul_of_nonneg_left (hM t ω) hσκ.le
    have hfa : 𝔼.Adapted (fun t => (-(σ * κ)) • u t) := fun t => by rw [map_smul, hua t]
    obtain ⟨hs, hb, ha, hu⟩ := scalar_existsUnique 𝔼 hc hf hfa
    exact ⟨_, ⟨hb, (reRule_iff_scalar 𝔼 σ κ φ u _).mpr ⟨ha, hs⟩⟩,
      fun π hπ => hu π ((reRule_iff_scalar 𝔼 σ κ φ u π).mp hπ.2).2 hπ.1⟩

/-- Cochrane (2023), p. 402, "The coefficient on lagged inflation in (17.11) is below one": the
coefficient `(1+σκφ)/(1+σκ)` of (17.11) has modulus below one iff `−1 − 2/(σκ) < φ < 1`. -/
theorem re_coeff_abs_lt_one_iff {σ κ φ : ℝ} (hσκ : 0 < σ * κ) :
    |(1 + σ * κ * φ) / (1 + σ * κ)| < 1 ↔ -1 - 2 / (σ * κ) < φ ∧ φ < 1 := by
  have h1 : 0 < 1 + σ * κ := by linarith
  rw [abs_div, abs_of_pos h1, div_lt_one h1, abs_lt]
  have e2 : -1 - 2 / (σ * κ) < φ ↔ 0 < σ * κ * φ + σ * κ + 2 := by
    have : -1 - 2 / (σ * κ) = (-(σ * κ) - 2) / (σ * κ) := by
      rw [sub_div, neg_div, div_self hσκ.ne']
    rw [this, div_lt_iff₀ hσκ]
    constructor <;> intro h <;> linarith
  rw [e2]
  constructor
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨ha, hb⟩; exact ⟨by linarith, by nlinarith⟩

/-- Cochrane (2023), p. 402, survey error E7: the printed "passive policy `φ < 1` produces
stable, indeterminate inflation" is false for very negative `φ`. With `σ = 1`, `κ = 1/2` and
`φ = −6 < 1` the model is determinate. -/
theorem printed_passive_indeterminate_false (𝔼 : ExpectationSystem Ω) [Nonempty Ω] :
    (-6 : ℝ) < 1 ∧ REDeterminate 𝔼 1 (1 / 2) (-6) := by
  refine ⟨by norm_num, (reDeterminate_iff 𝔼 (by norm_num)).mpr (Or.inr (by norm_num))⟩

/-- Cochrane (2023), p. 402: for `−1 − 2/(σκ) ≤ φ ≤ 1` (in particular passive `0 ≤ φ ≤ 1`)
the model is indeterminate. -/
theorem passive_indeterminate (𝔼 : ExpectationSystem Ω) [Nonempty Ω] {σ κ φ : ℝ}
    (hσκ : 0 < σ * κ) (h1 : φ ≤ 1) (h2 : -1 - 2 / (σ * κ) ≤ φ) : ¬ REDeterminate 𝔼 σ κ φ := by
  rw [reDeterminate_iff 𝔼 hσκ]
  push Not
  exact ⟨h1, h2⟩

/-- Cochrane (2023), p. 403: the forward solution. When (17.11) is determinate, the unique
bounded equilibrium is
`π_t = −σκ/(1+σκφ) ∑_j ((1+σκ)/(1+σκφ))ʲ E_t u_{t+j}`. -/
theorem forward_solution (𝔼 : ExpectationSystem Ω) {σ κ φ M : ℝ} (hσκ : 0 < σ * κ)
    (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ)) {u π : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) (hπb : BoundedProc π) (hπ : RERule 𝔼 σ κ φ u π) (t : ℕ) (ω : Ω) :
    π t ω = -(σ * κ) / (1 + σ * κ * φ) *
      ∑' j, ((1 + σ * κ) / (1 + σ * κ * φ)) ^ j * 𝔼.E t (u (t + j)) ω := by
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  have hf : ∀ t ω, |(fun t => (-(σ * κ)) • u t) t ω| ≤ σ * κ * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg, abs_of_pos hσκ]
    exact mul_le_mul_of_nonneg_left (hu t ω) hσκ.le
  have hfa : 𝔼.Adapted (fun t => (-(σ * κ)) • u t) := fun t => by rw [map_smul, hua t]
  obtain ⟨-, -, -, huniq⟩ := scalar_existsUnique 𝔼 hc hf hfa
  rw [huniq π ((reRule_iff_scalar 𝔼 σ κ φ u π).mp hπ).2 hπb, scalarSol_apply, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul, div_pow, pow_succ]
  have hA : 1 + σ * κ * φ ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith [abs_nonneg (1 + σ * κ)]
  field_simp

/-- Cochrane (2023), p. 402, "The frictionless case (16.4), `E_t π_{t+1} = φ π_t + u_{i,t}`, is
the `κ → ∞` limit": the coefficients of (17.11) tend to `φ` and `1`. -/
theorem tendsto_coeff_17_11 {σ : ℝ} (hσ : 0 < σ) (φ : ℝ) :
    Tendsto (fun κ : ℝ => (1 + σ * κ * φ) / (1 + σ * κ)) atTop (𝓝 φ) ∧
      Tendsto (fun κ : ℝ => σ * κ / (1 + σ * κ)) atTop (𝓝 1) := by
  obtain ⟨h0, h1⟩ := tendsto_coeff_17_7 hσ
  refine ⟨?_, h1⟩
  have h2 := (h0.const_mul (1 - φ)).const_add φ
  rw [mul_zero, add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have : 1 + σ * κ ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### Equilibrium selection by the rule (p. 401) -/

/-- Cochrane (2023), p. 401: with `i_t = i*_t + φ (π_t − π*_t)`, the deviation `d = π − π*` of
an equilibrium from an equilibrium `π*` of the model with `i*` obeys
`(1 + σκφ) d_t = (1 + σκ) E_t d_{t+1}`, i.e. `E_t d_{t+1} = (1+σκφ)/(1+σκ) d_t`. -/
theorem deviation_eq {𝔼 : ExpectationSystem Ω} {σ κ φ : ℝ} {istar πstar π : ℕ → Ω → ℝ}
    (hstar : REModel 𝔼 σ κ istar πstar)
    (hπ : REModel 𝔼 σ κ (fun t ω => istar t ω + φ * (π t ω - πstar t ω)) π) :
    ScalarEq 𝔼 (1 + σ * κ * φ) (1 + σ * κ) 0 (π - πstar) := by
  intro t
  funext ω
  have e1 := hstar.2 t ω
  have e2 := hπ.2 t ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply, map_sub,
    add_zero]
  linear_combination e2 - e1

/-- Cochrane (2023), p. 401: "If we rule out nominal explosions and add a policy rule
`i_t = i*_t + φ(π_t − π*_t)` with `φ > 1` … the central bank can achieve any value of
unexpected inflation": for any bounded equilibrium `π*` of the model with `i*`, it is the unique
bounded equilibrium under the rule (also for `φ < −1 − 2/(σκ)`). -/
theorem rule_selects {𝔼 : ExpectationSystem Ω} {σ κ φ : ℝ} (hσκ : 0 < σ * κ)
    (hφ : 1 < φ ∨ φ < -1 - 2 / (σ * κ)) {istar πstar : ℕ → Ω → ℝ}
    (hstar : REModel 𝔼 σ κ istar πstar) (hb : BoundedProc πstar) :
    ∃! π, BoundedProc π ∧
      REModel 𝔼 σ κ (fun t ω => istar t ω + φ * (π t ω - πstar t ω)) π := by
  have hc := (abs_lt_abs_iff hσκ).mpr hφ
  refine ⟨πstar, ⟨hb, ⟨hstar.1, fun t ω => ?_⟩⟩, fun π ⟨hπb, hπ⟩ => ?_⟩
  · rw [hstar.2 t ω]; ring
  · obtain ⟨-, -, -, huniq⟩ := scalar_existsUnique 𝔼 (K := 0) hc (f := 0) (fun _ _ => by simp)
      (fun t => by simp)
    obtain ⟨M₁, hM₁⟩ := hπb
    obtain ⟨M₂, hM₂⟩ := hb
    have hd : BoundedProc (π - πstar) := ⟨M₁ + M₂, fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω))⟩
    have h0 : ScalarEq 𝔼 (1 + σ * κ * φ) (1 + σ * κ) 0 0 := fun t => by simp
    have e := (huniq _ (deviation_eq hstar hπ) hd).trans
      (huniq 0 h0 ⟨0, fun _ _ => by simp⟩).symm
    exact sub_eq_zero.mp e

/-- Cochrane (2023), p. 401: any member of the family of equilibria of the peg model
(any adapted bounded martingale-difference process `δ` of unexpected inflation, any `π_0`)
can be selected by the rule `i_t = i*_t + φ(π_t − π*_t)` with `φ > 1`. -/
theorem rule_selects_any_delta (𝔼 : ExpectationSystem Ω) {σ κ φ B Mi Mδ : ℝ}
    (hσκ : 0 < σ * κ) (hφ : 1 < φ) {π0 : Ω → ℝ} {istar δ : ℕ → Ω → ℝ}
    (hπ0 : 𝔼.E 0 π0 = π0) (hπ0b : ∀ ω, |π0 ω| ≤ B) (hi : 𝔼.Adapted istar)
    (hib : ∀ t ω, |istar t ω| ≤ Mi) (hδ : 𝔼.Adapted δ) (hδb : ∀ t ω, |δ t ω| ≤ Mδ)
    (hmd : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    ∃! π, BoundedProc π ∧ REModel 𝔼 σ κ (fun t ω => istar t ω +
      φ * (π t ω - reFamily σ κ π0 istar δ t ω)) π := by
  exact rule_selects hσκ (Or.inl hφ) (reFamily_solves 𝔼 (by linarith) hπ0 hi hδ hmd).1
    (reFamily_bounded hσκ hπ0b hib hδb)

end Cochrane.KeynesianStickyPrices.RulesAdaptiveRE
