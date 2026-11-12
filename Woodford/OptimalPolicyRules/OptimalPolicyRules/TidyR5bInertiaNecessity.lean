/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflTargetInertia
import OptimalPolicyRules.ExpectationTools

/-!
# Necessity of the target criterion (2.5) under uncertainty

Woodford (2003), *Interest and Prices*, Chapter 8, §2.1, pp. 560–561, (2.1)–(2.5) (and Chapter 7,
§5, Proposition 7.15).

`InflTargetInertia.timeless_criterion_pf` proves that a plan optimal from a timeless perspective
satisfies the criterion `π_t + (λ/κ)(x_t − x_{t−1}) = 0`, under perfect foresight only. Here the
same is proved under an arbitrary expectation system with the pull-out property:

* `exists_criterion_plan`: for any bounded admissible plan there is a bounded initial value
  `x_{t₀−1}`, known at `t₀`, whose criterion equilibrium has the same initial inflation `π_{t₀}`
  (the self-consistent `x_{t₀−1} = (π_{t₀} + φ w_{t₀}) / (φ (1 − μ₁))`, a linear function of
  date-`t₀` information);
* `timeless_criterion_sq`: every timelessly optimal plan coincides with that criterion
  equilibrium in conditional mean square, so the criterion holds in conditional mean square,
  `E_{t₀}[(π_{t+1} + φ(x_{t+1} − x_t))²] = 0` — with no further hypothesis (genuine probability
  spaces: "almost surely");
* `timeless_criterion`: with faithful expectations the criterion holds state by state, at every
  date `t > t₀`, and at `t₀` with the self-consistent `x_{t₀−1}`;
* `timeless_iff_criterion`: optimality from a timeless perspective is EQUIVALENT to commitment to
  (2.5) with some bounded `x_{t₀−1}` known at `t₀` (sufficiency is
  `InflTargetInertia.criterion_timeless`).
-/

namespace Woodford.OptimalPolicyRules.TidyR5bInertiaNecessity

open InflTargetInertia
open QuadraticRoots (lam1 lam1_root lam1_pos lam1_lt_one beta_lam1_mem)
open ExpectationTools (Faithful)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (2.5) and survey §4.3: the forward part `w_t` of the criterion equilibrium is
bounded and adapted. -/
theorem wsol_bdd_adapted {β c M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c)
    {f : ℕ → Ω → ℝ} (hf : ∀ t ω, |f t ω| ≤ M) :
    BoundedProc (wsol 𝔼 β c f) ∧ (𝔼.Adapted f → 𝔼.Adapted (wsol 𝔼 β c f)) := by
  have hμ0 := lam1_pos hβ0 hc
  obtain ⟨ha0, ha1⟩ := beta_lam1_mem hβ0 hβ1 hc
  have hgb := neg_mu_f_bounded hμ0 hf
  refine ⟨𝔼.forwardSeries_bounded ha0 ha1 hgb, fun hfa => ?_⟩
  have := 𝔼.forwardSeries_adapted ha0 ha1 hgb (u := fun s => (-lam1 β c) • f s)
  exact this

/-- Woodford (2003), (2.5), p. 561 (**the self-consistent initial value**): for `κ, λ > 0`, every
bounded admissible plan `(π, x)` and every bounded adapted cost-push process there is a bounded
`x_{t₀−1}`, known at `t₀`, such that the unique bounded equilibrium under the criterion
`π_t + (λ/κ)(x_t − x_{t−1}) = 0` has the same initial inflation `π_{t₀}`. -/
theorem exists_criterion_plan {β κ lam M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u)
    {π x : ℕ → Ω → ℝ} (hp : Plan 𝔼 β κ u π x) :
    ∃ x₀ : Ω → ℝ, (∃ B, ∀ ω, |x₀ ω| ≤ B) ∧ 𝔼.E 0 x₀ = x₀ ∧
      (Plan 𝔼 β κ u (inflR 𝔼 β κ (lam / κ) x₀ u) (gapR 𝔼 β κ (lam / κ) x₀ u) ∧
        Criterion (lam / κ) x₀ (inflR 𝔼 β κ (lam / κ) x₀ u) (gapR 𝔼 β κ (lam / κ) x₀ u)) ∧
      inflR 𝔼 β κ (lam / κ) x₀ u 0 = π 0 := by
  set φ := lam / κ with hφdef
  have hφ : 0 < φ := div_pos hlam hκ
  have hc : 0 < κ / φ := div_pos hκ hφ
  set μ := lam1 β (κ / φ) with hμ
  have hμ1 := lam1_lt_one hβ0 hc
  have h1μ : 0 < φ * (1 - μ) := mul_pos hφ (by linarith)
  have h1m : 1 - μ ≠ 0 := (sub_pos.2 hμ1).ne'
  set f : ℕ → Ω → ℝ := fun t => φ⁻¹ • u t with hf
  have hfb : ∀ t ω, |f t ω| ≤ φ⁻¹ * M := fun t ω => by
    simp only [hf, Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hφ]
    exact mul_le_mul_of_nonneg_left (hu t ω) (inv_nonneg.2 hφ.le)
  have hfa : 𝔼.Adapted f := fun t => by simp only [hf, map_smul, hua t]
  obtain ⟨⟨W, hW⟩, hwa⟩ := wsol_bdd_adapted 𝔼 hβ0 hβ1 hc hfb
  have hwa' := hwa hfa
  set w0 : Ω → ℝ := wsol 𝔼 β (κ / φ) f 0 with hw0
  set x₀ : Ω → ℝ := fun ω => (π 0 ω + φ * w0 ω) / (φ * (1 - μ)) with hx₀
  obtain ⟨-, hπa, -, ⟨A, hA⟩, -⟩ := hp
  have hx₀b : ∃ B, ∀ ω, |x₀ ω| ≤ B := by
    refine ⟨(A + φ * W) / (φ * (1 - μ)), fun ω => ?_⟩
    simp only [hx₀, abs_div, abs_of_pos h1μ]
    refine div_le_div_of_nonneg_right ?_ h1μ.le
    refine (abs_add_le _ _).trans (add_le_add (hA 0 ω) ?_)
    rw [abs_mul, abs_of_pos hφ]
    exact mul_le_mul_of_nonneg_left (hW 0 ω) hφ.le
  have hx₀a : 𝔼.E 0 x₀ = x₀ := by
    have e : x₀ = (φ * (1 - μ))⁻¹ • (π 0 + φ • w0) := by
      funext ω
      simp only [hx₀, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      field_simp
    rw [e, map_smul, map_add, map_smul, hπa 0]
    have : 𝔼.E 0 w0 = w0 := hwa' 0
    rw [this]
  obtain ⟨B, hB⟩ := hx₀b
  obtain ⟨hex, -⟩ := ruleEq_existsUnique 𝔼 hβ0 hβ1 hκ hφ hu hua hB hx₀a
  refine ⟨x₀, ⟨B, hB⟩, hx₀a, hex, ?_⟩
  funext ω
  obtain ⟨-, hr⟩ := ruleEq_representation 𝔼 β κ φ x₀ u 0 ω
  rw [hr]
  simp only [lagW_zero]
  have e : φ * (1 - μ) * x₀ ω = π 0 ω + φ * w0 ω := by
    simp only [hx₀]
    field_simp
  change φ * (1 - μ) * x₀ ω - φ * w0 ω = π 0 ω
  linarith

/-- Woodford (2003), (2.5) (**necessity in conditional mean square, any expectation system with
pull-out**): a plan optimal from a timeless perspective coincides in conditional mean square with
the criterion equilibrium for a bounded `x_{t₀−1}` known at `t₀`:
`E_{t₀}(π_t − π^R_t)² = E_{t₀}(x_t − x^R_t)² = 0` at every date. -/
theorem timeless_criterion_sq (hpo : 𝔼.PullOut) {β κ lam xstar M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) {π x : ℕ → Ω → ℝ} (h : TimelessOptimal 𝔼 β κ lam xstar u π x) :
    ∃ x₀ : Ω → ℝ, (∃ B, ∀ ω, |x₀ ω| ≤ B) ∧ 𝔼.E 0 x₀ = x₀ ∧
      Criterion (lam / κ) x₀ (inflR 𝔼 β κ (lam / κ) x₀ u) (gapR 𝔼 β κ (lam / κ) x₀ u) ∧
      ∀ t ω, 𝔼.E 0 (fun ω => (π t ω - inflR 𝔼 β κ (lam / κ) x₀ u t ω) ^ 2) ω = 0 ∧
        𝔼.E 0 (fun ω => (x t ω - gapR 𝔼 β κ (lam / κ) x₀ u t ω) ^ 2) ω = 0 := by
  obtain ⟨x₀, hx₀b, hx₀a, ⟨hpR, hcR⟩, h0⟩ :=
    exists_criterion_plan 𝔼 hβ0 hβ1 hκ hlam hu hua h.1
  refine ⟨x₀, hx₀b, hx₀a, hcR, fun t ω => ?_⟩
  have hle1 := h.2 _ _ hpR h0 ω
  have hle2 := (criterion_timeless 𝔼 hpo (xstar := xstar) hβ0.le hβ1 hlam.le hκ.ne' hx₀b hpR
    hcR).2 π x h.1 h0.symm ω
  exact criterion_timeless_unique 𝔼 hpo hβ0 hβ1 hlam hκ.ne' hx₀b hpR hcR h.1 h0.symm ω
    (le_antisymm hle1 hle2) t

/-- Woodford (2003), (2.5): `(a + b + c)² ≤ 3(a² + b² + c²)`. -/
theorem sq_add3_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- Woodford (2003), (2.5) (**the criterion holds in conditional mean square**): for a plan that
is optimal from a timeless perspective, under any expectation system with pull-out,
`E_{t₀}[(π_{t+1} + (λ/κ)(x_{t+1} − x_t))²] = 0` at every date `t > t₀` (on a probability space:
the criterion holds almost surely). -/
theorem timeless_criterion_meanSq (hpo : 𝔼.PullOut) {β κ lam xstar M : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) {π x : ℕ → Ω → ℝ} (h : TimelessOptimal 𝔼 β κ lam xstar u π x)
    (t : ℕ) (ω : Ω) :
    𝔼.E 0 (fun ω => (π (t + 1) ω + lam / κ * (x (t + 1) ω - x t ω)) ^ 2) ω = 0 := by
  obtain ⟨x₀, -, -, hcR, hsq⟩ := timeless_criterion_sq 𝔼 hpo hβ0 hβ1 hκ hlam hu hua h
  set φ := lam / κ
  set πR := inflR 𝔼 β κ φ x₀ u
  set xR := gapR 𝔼 β κ φ x₀ u
  have hpt : ∀ ω', (π (t + 1) ω' + φ * (x (t + 1) ω' - x t ω')) ^ 2 ≤
      3 * ((π (t + 1) ω' - πR (t + 1) ω') ^ 2 + φ ^ 2 * (x (t + 1) ω' - xR (t + 1) ω') ^ 2 +
        φ ^ 2 * (x t ω' - xR t ω') ^ 2) := by
    intro ω'
    have hc := hcR (t + 1) ω'
    simp only [lagW_succ] at hc
    have e : π (t + 1) ω' + φ * (x (t + 1) ω' - x t ω') =
        (π (t + 1) ω' - πR (t + 1) ω') + φ * (x (t + 1) ω' - xR (t + 1) ω') +
          (-(φ * (x t ω' - xR t ω'))) := by linarith
    rw [e]
    have := sq_add3_le (π (t + 1) ω' - πR (t + 1) ω') (φ * (x (t + 1) ω' - xR (t + 1) ω'))
      (-(φ * (x t ω' - xR t ω')))
    simpa [mul_pow] using this
  have hmono := 𝔼.mono 0 (x := fun ω' => (π (t + 1) ω' + φ * (x (t + 1) ω' - x t ω')) ^ 2)
    (y := (3 : ℝ) • ((fun ω' => (π (t + 1) ω' - πR (t + 1) ω') ^ 2) +
      φ ^ 2 • (fun ω' => (x (t + 1) ω' - xR (t + 1) ω') ^ 2) +
      φ ^ 2 • (fun ω' => (x t ω' - xR t ω') ^ 2))) (fun ω' => by
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        exact hpt ω') ω
  simp only [map_smul, map_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul] at hmono
  rw [(hsq (t + 1) ω).1, (hsq (t + 1) ω).2, (hsq t ω).2] at hmono
  have hnn := E_nonneg 𝔼 (f := fun ω' => (π (t + 1) ω' + φ * (x (t + 1) ω' - x t ω')) ^ 2)
    (fun ω' => sq_nonneg _) 0 ω
  linarith

/-- Woodford (2003), Ch. 7 §5 / Ch. 8 (2.5) (**necessity of the target criterion under
uncertainty**): under any faithful expectation system with the pull-out property (for
`0 < β < 1`, `κ, λ > 0` and a bounded adapted cost-push process), every plan that is optimal
from a timeless perspective satisfies the target criterion `π_t + (λ/κ)(x_t − x_{t−1}) = 0` at
every date, with a bounded self-consistent `x_{t₀−1}` known at `t₀`. This extends
`InflTargetInertia.timeless_criterion_pf` beyond perfect foresight. -/
theorem timeless_criterion (hpo : 𝔼.PullOut) (hfaith : Faithful 𝔼) {β κ lam xstar M : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) {π x : ℕ → Ω → ℝ}
    (h : TimelessOptimal 𝔼 β κ lam xstar u π x) :
    ∃ x₀ : Ω → ℝ, (∃ B, ∀ ω, |x₀ ω| ≤ B) ∧ 𝔼.E 0 x₀ = x₀ ∧ Criterion (lam / κ) x₀ π x := by
  obtain ⟨x₀, hx₀b, hx₀a, hcR, hsq⟩ := timeless_criterion_sq 𝔼 hpo hβ0 hβ1 hκ hlam hu hua h
  have hπ : ∀ t ω, π t ω = inflR 𝔼 β κ (lam / κ) x₀ u t ω := by
    intro t ω
    have := hfaith.eq_zero (fun ω' => sq_nonneg (π t ω' - inflR 𝔼 β κ (lam / κ) x₀ u t ω'))
      (funext fun ω' => (hsq t ω').1) ω
    nlinarith [sq_nonneg (π t ω - inflR 𝔼 β κ (lam / κ) x₀ u t ω)]
  have hx : ∀ t ω, x t ω = gapR 𝔼 β κ (lam / κ) x₀ u t ω := by
    intro t ω
    have := hfaith.eq_zero (fun ω' => sq_nonneg (x t ω' - gapR 𝔼 β κ (lam / κ) x₀ u t ω'))
      (funext fun ω' => (hsq t ω').2) ω
    nlinarith [sq_nonneg (x t ω - gapR 𝔼 β κ (lam / κ) x₀ u t ω)]
  refine ⟨x₀, hx₀b, hx₀a, fun t ω => ?_⟩
  have hlag : lagW x₀ x t ω = lagW x₀ (gapR 𝔼 β κ (lam / κ) x₀ u) t ω := by
    cases t with
    | zero => rfl
    | succ t => exact hx t ω
  rw [hπ, hx, hlag]
  exact hcR t ω

/-- Woodford (2003), Ch. 8 (2.5), pp. 560–561 (**at every date `t > t₀`**): under faithful
expectations with pull-out, a timelessly optimal plan satisfies
`π_{t+1} + (λ/κ)(x_{t+1} − x_t) = 0` in every state. -/
theorem timeless_criterion_succ (hpo : 𝔼.PullOut) (hfaith : Faithful 𝔼) {β κ lam xstar M : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) {π x : ℕ → Ω → ℝ}
    (h : TimelessOptimal 𝔼 β κ lam xstar u π x) (t : ℕ) (ω : Ω) :
    π (t + 1) ω + lam / κ * (x (t + 1) ω - x t ω) = 0 := by
  obtain ⟨x₀, -, -, hc⟩ := timeless_criterion 𝔼 hpo hfaith hβ0 hβ1 hκ hlam hu hua h
  simpa using hc (t + 1) ω

/-- Woodford (2003), Ch. 7 Prop. 7.15 / Ch. 8 (2.5) (**optimality from a timeless perspective
is equivalent to commitment to the criterion**): under faithful expectations with pull-out, an
admissible plan is optimal from a timeless perspective iff it satisfies
`π_t + (λ/κ)(x_t − x_{t−1}) = 0` for some bounded `x_{t₀−1}` known at `t₀`. -/
theorem timeless_iff_criterion (hpo : 𝔼.PullOut) (hfaith : Faithful 𝔼) {β κ lam xstar M : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hua : 𝔼.Adapted u) {π x : ℕ → Ω → ℝ} :
    TimelessOptimal 𝔼 β κ lam xstar u π x ↔ Plan 𝔼 β κ u π x ∧
      ∃ x₀ : Ω → ℝ, (∃ B, ∀ ω, |x₀ ω| ≤ B) ∧ 𝔼.E 0 x₀ = x₀ ∧ Criterion (lam / κ) x₀ π x := by
  constructor
  · intro h
    exact ⟨h.1, timeless_criterion 𝔼 hpo hfaith hβ0 hβ1 hκ hlam hu hua h⟩
  · rintro ⟨hp, x₀, hx₀b, -, hc⟩
    exact criterion_timeless 𝔼 hpo hβ0.le hβ1 hlam.le hκ.ne' hx₀b hp hc

/-- Woodford (2003), (2.5): the perfect-foresight statement
`InflTargetInertia.timeless_criterion_pf` is the special case (perfect foresight is faithful and
has the pull-out property). -/
theorem timeless_criterion_pf' {β κ lam xstar M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) {u : ℕ → Unit → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    {π x : ℕ → Unit → ℝ} (h : TimelessOptimal perfectForesight β κ lam xstar u π x) (t : ℕ)
    (ω : Unit) : π (t + 1) ω + lam / κ * (x (t + 1) ω - x t ω) = 0 :=
  timeless_criterion_succ perfectForesight perfectForesight_pullOut
    ExpectationTools.perfectForesight_faithful hβ0 hβ1 hκ hlam hu (fun _ => rfl) h t ω

end Woodford.OptimalPolicyRules.TidyR5bInertiaNecessity
