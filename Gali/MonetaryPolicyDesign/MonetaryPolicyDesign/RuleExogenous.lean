/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Expectations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Complex.Basic

/-!
# An exogenous interest-rate rule

Galí (2015), Chapter 4, §4.3.1.1, pp. 104–105. The non-policy block of the basic
New Keynesian model is the NKPC `π_t = β E_t π_{t+1} + κ ỹ_t` (eq. (7)) and the
DIS `ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)` (eq. (6)). Under the
candidate rule (8), `i_t = r^n_t`, the equilibrium conditions are the system (9),
`x_t = A_O E_t x_{t+1}` with `x_t = (ỹ_t, π_t)` and (10)
`A_O = [[1, 1/σ], [κ, β + κ/σ]]`.

## Main results

* `equilibrium_iff_solves`: the NKPC, the DIS and the rule (8) hold iff `(ỹ, π)`
  solves (9) and `i = r^n`.
* `zero_equilibrium`: `ỹ = π = 0`, `i = r^n` is an equilibrium (p. 105).
* `det_sub_AO`, `charPolyO`: the characteristic polynomial
  `p(λ) = λ² − (1 + β + κ/σ) λ + β` of `A_O`.
* `eigenvalues_AO`: `A_O` has two real eigenvalues `0 < λ₁ < 1 < λ₂` and no
  other (complex) ones; found by the intermediate value theorem from
  `p(0) = β > 0`, `p(1) = −κ/σ < 0`, `p(1 + β + κ/σ) = β > 0`.
* `not_determinate_AO`: hence the system is indeterminate (Blanchard–Kahn,
  via `determinate_iff`).
* `sunspot_equilibrium`, `exists_second_equilibrium`: an explicit second bounded
  equilibrium, `ỹ_t = λ₂^{−t}`, `π_t = σ (λ₂ − 1) λ₂^{−t}`, `i_t = r^n_t`.
* `equilibrium_not_unique`: next to every bounded equilibrium there is another.
-/

namespace Gali.MonetaryPolicyDesign.RuleExogenous

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (7), p. 104: the New Keynesian Phillips curve
`π_t = β E_t π_{t+1} + κ ỹ_t`. -/
def NKPC (β κ : ℝ) (ygap infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ygap t

/-- Galí (2015), eq. (6), p. 104: the dynamic IS equation
`ỹ_t = E_t ỹ_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − r^n_t)`. -/
def DIS (σ : ℝ) (ygap i infl rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ygap t = 𝔼.E t (ygap (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - rn t)

/-- Galí (2015), eq. (8), p. 104: the exogenous rule `i_t = r^n_t`. -/
def ExogRule (i rn : ℕ → Ω → ℝ) : Prop := ∀ t, i t = rn t

/-- Galí (2015), §4.3.1.1, p. 104: an equilibrium under rule (8): the DIS (6),
the NKPC (7) and the rule (8). -/
def Equilibrium (β σ κ : ℝ) (rn ygap infl i : ℕ → Ω → ℝ) : Prop :=
  NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn ∧ ExogRule i rn

/-- Galí (2015), eq. (10), p. 105: `A_O = [[1, 1/σ], [κ, β + κ/σ]]`. -/
noncomputable def AO (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1 / σ; κ, β + κ / σ]

/-- Galí (2015), eq. (9), p. 104: the stacked vector `x_t = (ỹ_t, π_t)`. -/
def stack (ygap infl : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ := fun t => ![ygap t, infl t]

/-- Two bounded processes stack to a bounded vector process (restated from the
Chapter 3 project). -/
theorem boundedVec_stack {a b : ℕ → Ω → ℝ} (ha : BoundedProc a) (hb : BoundedProc b) :
    BoundedVec (stack a b) := by
  obtain ⟨M₁, h₁⟩ := ha
  obtain ⟨M₂, h₂⟩ := hb
  refine ⟨max M₁ M₂, fun t j ω => ?_⟩
  fin_cases j
  · exact (h₁ t ω).trans (le_max_left _ _)
  · exact (h₂ t ω).trans (le_max_right _ _)

/-- Two adapted processes stack to an adapted vector process (restated from the
Chapter 3 project). -/
theorem adaptedVec_stack {a b : ℕ → Ω → ℝ} (ha : 𝔼.Adapted a) (hb : 𝔼.Adapted b) :
    𝔼.AdaptedVec (stack a b) := by
  intro t j
  fin_cases j
  · exact ha t
  · exact hb t

/-- Galí (2015), eq. (9), p. 104: given the rule (8), the NKPC and the DIS hold
iff `(ỹ, π)` solves `x_t = A_O E_t x_{t+1}`. -/
theorem nk_iff_solves {β σ κ : ℝ} {rn ygap infl i : ℕ → Ω → ℝ}
    (hrule : ExogRule i rn) :
    (NKPC 𝔼 β κ ygap infl ∧ DIS 𝔼 σ ygap i infl rn) ↔
      𝔼.Solves (AO β σ κ) 0 (stack ygap infl) := by
  constructor
  · rintro ⟨hp, hd⟩ t j
    funext ω
    have e := congrFun (hd t) ω
    have p := congrFun (hp t) ω
    simp only [hrule t, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e p
    fin_cases j
    · simp [stack, AO]
      linear_combination e
    · simp [stack, AO]
      linear_combination p + κ * e
  · intro h
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have e0 := congrFun (h t 0) ω
      have e1 := congrFun (h t 1) ω
      simp [stack, AO] at e0 e1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e1 - κ * e0
    · have e0 := congrFun (h t 0) ω
      simp [stack, AO] at e0
      simp only [hrule t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination e0

/-- Galí (2015), eqs. (8)–(10), pp. 104–105: `(ỹ, π, i)` is an equilibrium under
rule (8) iff `x_t = (ỹ_t, π_t)` solves `x_t = A_O E_t x_{t+1}` and `i = r^n`. -/
theorem equilibrium_iff_solves {β σ κ : ℝ} {rn ygap infl i : ℕ → Ω → ℝ} :
    Equilibrium 𝔼 β σ κ rn ygap infl i ↔
      𝔼.Solves (AO β σ κ) 0 (stack ygap infl) ∧ i = rn := by
  constructor
  · rintro ⟨hp, hd, hr⟩
    exact ⟨(nk_iff_solves 𝔼 hr).mp ⟨hp, hd⟩, funext hr⟩
  · rintro ⟨hs, rfl⟩
    have hr : ExogRule i i := fun _ => rfl
    obtain ⟨hp, hd⟩ := (nk_iff_solves 𝔼 hr).mpr hs
    exact ⟨hp, hd, hr⟩

/-- Galí (2015), p. 105: `ỹ_t = π_t = 0` for all `t`, with `i_t = r^n_t`, is an
equilibrium under rule (8). -/
theorem zero_equilibrium (β σ κ : ℝ) (rn : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ rn 0 0 rn := by
  refine ⟨fun t => ?_, fun t => ?_, fun _ => rfl⟩ <;> simp

/-- The trace of `A_O`: `tr A_O = 1 + β + κ/σ` (Galí 2015, eq. (10), p. 105). -/
theorem tr2_AO (β σ κ : ℝ) : tr2 (AO β σ κ) = 1 + β + κ / σ := by
  simp [tr2, AO]
  ring

/-- The determinant of `A_O`: `det A_O = β` (Galí 2015, eq. (10), p. 105). -/
theorem det2_AO {β σ κ : ℝ} (hσ : σ ≠ 0) : det2 (AO β σ κ) = β := by
  simp [det2, AO]
  field_simp
  ring

/-- Galí (2015), p. 105: the characteristic polynomial of `A_O`,
`p(λ) = λ² − (1 + β + κ/σ) λ + β`. -/
noncomputable def charPolyO (β σ κ x : ℝ) : ℝ := x ^ 2 - (1 + β + κ / σ) * x + β

/-- Galí (2015), p. 105: `det (λ I − A_O) = p(λ)`, so the eigenvalues of `A_O`
are the roots of `charPolyO`. -/
theorem det_sub_AO {β σ κ : ℝ} (hσ : σ ≠ 0) (x : ℝ) :
    Matrix.det (x • (1 : Matrix (Fin 2) (Fin 2) ℝ) - AO β σ κ) = charPolyO β σ κ x := by
  rw [Matrix.det_fin_two]
  simp [AO, charPolyO]
  field_simp
  ring

/-- Galí (2015), p. 105: `p(0) = β`. -/
theorem charPolyO_zero (β σ κ : ℝ) : charPolyO β σ κ 0 = β := by
  simp [charPolyO]

/-- Galí (2015), p. 105: `p(1) = −κ/σ`. -/
theorem charPolyO_one (β σ κ : ℝ) : charPolyO β σ κ 1 = -(κ / σ) := by
  simp [charPolyO]
  ring

/-- Galí (2015), p. 105: `p(1 + β + κ/σ) = β`. -/
theorem charPolyO_trace (β σ κ : ℝ) : charPolyO β σ κ (1 + β + κ / σ) = β := by
  simp [charPolyO]
  ring

/-- The characteristic polynomial is continuous. -/
theorem continuous_charPolyO (β σ κ : ℝ) : Continuous (charPolyO β σ κ) := by
  unfold charPolyO
  fun_prop

/-- Galí (2015), p. 105 (Exercise 4.1(a)): for `σ, κ, β > 0`, `p` has a root in
`(0, 1)` (intermediate value theorem: `p(0) > 0 > p(1)`). -/
theorem exists_root_Ioo_zero_one {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    ∃ x, 0 < x ∧ x < 1 ∧ charPolyO β σ κ x = 0 := by
  have h : (0 : ℝ) ∈ Set.Ioo (charPolyO β σ κ 1) (charPolyO β σ κ 0) := by
    rw [charPolyO_zero, charPolyO_one]
    exact ⟨by have := div_pos hκ hσ; linarith, hβ⟩
  obtain ⟨x, ⟨hx0, hx1⟩, hx⟩ :=
    intermediate_value_Ioo' zero_le_one (continuous_charPolyO β σ κ).continuousOn h
  exact ⟨x, hx0, hx1, hx⟩

/-- Galí (2015), p. 105 (Exercise 4.1(a)): for `σ, κ, β > 0`, `p` has a root
strictly greater than one (intermediate value theorem on `[1, 1 + β + κ/σ]`). -/
theorem exists_root_gt_one {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    ∃ x, 1 < x ∧ charPolyO β σ κ x = 0 := by
  have hT : 1 ≤ 1 + β + κ / σ := by have := div_pos hκ hσ; linarith
  have h : (0 : ℝ) ∈ Set.Ioo (charPolyO β σ κ 1) (charPolyO β σ κ (1 + β + κ / σ)) := by
    rw [charPolyO_trace, charPolyO_one]
    exact ⟨by have := div_pos hκ hσ; linarith, hβ⟩
  obtain ⟨x, ⟨hx1, -⟩, hx⟩ :=
    intermediate_value_Ioo hT (continuous_charPolyO β σ κ).continuousOn h
  exact ⟨x, hx1, hx⟩

/-- **The eigenvalues of `A_O`** (Galí 2015, p. 105; Exercise 4.1(a)): for
`σ, κ, β > 0`, `A_O` has two real eigenvalues `λ₁ ∈ (0, 1)` and `λ₂ > 1`, and
every complex root of its characteristic polynomial `z² − tr A_O z + det A_O`
is one of them. -/
theorem eigenvalues_AO {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    ∃ l₁ l₂ : ℝ, 0 < l₁ ∧ l₁ < 1 ∧ 1 < l₂ ∧
      Matrix.det (l₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - AO β σ κ) = 0 ∧
      Matrix.det (l₂ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - AO β σ κ) = 0 ∧
      ∀ z : ℂ, z ^ 2 - (tr2 (AO β σ κ) : ℂ) * z + (det2 (AO β σ κ) : ℂ) = 0 →
        z = l₁ ∨ z = l₂ := by
  obtain ⟨l₁, h0, h1, hp1⟩ := exists_root_Ioo_zero_one hσ hκ hβ
  obtain ⟨l₂, h2, hp2⟩ := exists_root_gt_one hσ hκ hβ
  refine ⟨l₁, l₂, h0, h1, h2, by rw [det_sub_AO hσ.ne', hp1],
    by rw [det_sub_AO hσ.ne', hp2], fun z hz => ?_⟩
  rw [tr2_AO, det2_AO hσ.ne'] at hz
  unfold charPolyO at hp1 hp2
  set T := 1 + β + κ / σ
  -- Vieta: `l₁ + l₂ = T` and `l₁ l₂ = β`, since `l₁ ≠ l₂`
  have hne : l₁ - l₂ ≠ 0 := by intro h; linarith
  have hsum : l₁ + l₂ = T := by
    have : (l₁ - l₂) * (l₁ + l₂ - T) = 0 := by linear_combination hp1 - hp2
    linarith [(mul_eq_zero.mp this).resolve_left hne]
  have hprod : l₁ * l₂ = β := by linear_combination -hp1 + l₁ * hsum
  have hsumC : ((l₁ : ℂ) + l₂) = (T : ℂ) := by exact_mod_cast hsum
  have hprodC : ((l₁ : ℂ) * l₂) = (β : ℂ) := by exact_mod_cast hprod
  have hf : (z - l₁) * (z - l₂) = 0 := by
    linear_combination hz - z * hsumC + hprodC
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Galí (2015), p. 105: `A_O` fails the Schur–Cohn condition, because
`tr A_O = 1 + det A_O + κ/σ > 1 + det A_O`. -/
theorem not_schurStable_AO {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ SchurStable (tr2 (AO β σ κ)) (det2 (AO β σ κ)) := by
  rintro ⟨-, hT⟩
  rw [tr2_AO, det2_AO hσ.ne'] at hT
  have := div_pos hκ hσ
  have := le_abs_self (1 + β + κ / σ)
  linarith

/-- **Indeterminacy under rule (8)** (Galí 2015, p. 105): for `σ, κ > 0` the
system (9) is not determinate: it has two distinct bounded adapted solutions
for some forcing process (Blanchard–Kahn, via `determinate_iff`). -/
theorem not_determinate_AO [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ¬ 𝔼.Determinate (AO β σ κ) := by
  rw [𝔼.determinate_iff]
  exact not_schurStable_AO hσ hκ

/-- Galí (2015), p. 105: the self-fulfilling output-gap path `ỹ_t = λ^{−t}`
attached to an eigenvalue `λ` of `A_O` (a deterministic process). -/
noncomputable def sunspotY (l : ℝ) : ℕ → Ω → ℝ := fun t _ => l⁻¹ ^ t

/-- Galí (2015), p. 105: the matching inflation path `π_t = σ (λ − 1) λ^{−t}`
(the eigenvector of `A_O` for `λ` is `(1, σ (λ − 1))`). -/
noncomputable def sunspotPi (σ l : ℝ) : ℕ → Ω → ℝ := fun t _ => σ * (l - 1) * l⁻¹ ^ t

/-- Galí (2015), p. 105: for every nonzero root `λ` of the characteristic
polynomial, `ỹ_t = λ^{−t}`, `π_t = σ (λ − 1) λ^{−t}`, `i_t = r^n_t` is an
equilibrium under rule (8). -/
theorem sunspot_equilibrium {β σ κ l : ℝ} (hσ : σ ≠ 0) (hl : l ≠ 0)
    (hp : charPolyO β σ κ l = 0) (rn : ℕ → Ω → ℝ) :
    Equilibrium 𝔼 β σ κ rn (sunspotY l) (sunspotPi σ l) rn := by
  have hp' : σ * l ^ 2 - (σ + β * σ + κ) * l + β * σ = 0 := by
    unfold charPolyO at hp
    field_simp at hp
    linear_combination hp
  have h1 : l * l⁻¹ = 1 := mul_inv_cancel₀ hl
  have hs : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
  refine ⟨fun t => ?_, fun t => ?_, fun _ => rfl⟩
  · change (fun _ => σ * (l - 1) * l⁻¹ ^ t : Ω → ℝ) =
      β • 𝔼.E t (fun _ => σ * (l - 1) * l⁻¹ ^ (t + 1)) + κ • (fun _ => l⁻¹ ^ t)
    rw [𝔼.const]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    linear_combination l⁻¹ ^ t * l⁻¹ * hp' - l⁻¹ ^ t * (σ * l - σ - κ) * h1
  · change (fun _ => l⁻¹ ^ t : Ω → ℝ) = 𝔼.E t (fun _ => l⁻¹ ^ (t + 1))
      - σ⁻¹ • (rn t - 𝔼.E t (fun _ => σ * (l - 1) * l⁻¹ ^ (t + 1)) - rn t)
    rw [𝔼.const, 𝔼.const]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    linear_combination (-(l⁻¹ ^ t)) * h1 - l⁻¹ ^ t * l⁻¹ * (l - 1) * hs

/-- **A second bounded equilibrium** (Galí 2015, p. 105): for `σ, κ, β > 0`
there is an equilibrium under rule (8) with bounded adapted output gap and
inflation that is not `ỹ = π = 0`, namely the sunspot path of the eigenvalue
`λ₂ > 1`: `ỹ_t = λ₂^{−t}`, `π_t = σ (λ₂ − 1) λ₂^{−t}`, `i_t = r^n_t`. -/
theorem exists_second_equilibrium [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (rn : ℕ → Ω → ℝ) :
    ∃ ygap infl : ℕ → Ω → ℝ, Equilibrium 𝔼 β σ κ rn ygap infl rn ∧
      𝔼.Adapted ygap ∧ 𝔼.Adapted infl ∧ BoundedProc ygap ∧ BoundedProc infl ∧
      ygap ≠ 0 ∧ infl ≠ 0 := by
  obtain ⟨l, hl1, hp⟩ := exists_root_gt_one hσ hκ hβ
  have hl0 : 0 < l := by linarith
  have hpow : ∀ t : ℕ, 0 < l⁻¹ ^ t ∧ l⁻¹ ^ t ≤ 1 := fun t =>
    ⟨by positivity, pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl1.le)⟩
  have hc : 0 < σ * (l - 1) := mul_pos hσ (by linarith)
  refine ⟨sunspotY l, sunspotPi σ l, sunspot_equilibrium 𝔼 hσ.ne' hl0.ne' hp rn,
    fun t => 𝔼.const t _, fun t => 𝔼.const t _, ⟨1, fun t _ => ?_⟩,
    ⟨σ * (l - 1), fun t _ => ?_⟩, fun h => ?_, fun h => ?_⟩
  · simp only [sunspotY]
    rw [abs_of_pos (hpow t).1]
    exact (hpow t).2
  · simp only [sunspotPi]
    rw [abs_of_pos (mul_pos hc (hpow t).1)]
    exact mul_le_of_le_one_right hc.le (hpow t).2
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp [sunspotY] at this
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp only [sunspotPi, pow_zero, mul_one, Pi.zero_apply] at this
    linarith

/-- **Multiplicity around every equilibrium** (Galí 2015, p. 105): for `σ, κ > 0`,
next to any equilibrium under rule (8) with bounded adapted output gap and
inflation there is another one with a different output gap or inflation path. -/
theorem equilibrium_not_unique [Nonempty Ω] {β σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    {rn ygap infl i : ℕ → Ω → ℝ} (he : Equilibrium 𝔼 β σ κ rn ygap infl i)
    (ha : 𝔼.Adapted ygap) (hb : 𝔼.Adapted infl) (hba : BoundedProc ygap)
    (hbb : BoundedProc infl) :
    ∃ ygap' infl', Equilibrium 𝔼 β σ κ rn ygap' infl' i ∧
      𝔼.Adapted ygap' ∧ 𝔼.Adapted infl' ∧ BoundedProc ygap' ∧ BoundedProc infl' ∧
      (ygap' ≠ ygap ∨ infl' ≠ infl) := by
  obtain ⟨hx, hi⟩ := (equilibrium_iff_solves 𝔼).mp he
  obtain ⟨y, hy, hay, ⟨M, hM⟩, hne⟩ := 𝔼.system_not_unique (not_schurStable_AO hσ hκ) hx
    (adaptedVec_stack 𝔼 ha hb) (boundedVec_stack hba hbb)
  have hst : stack (fun t => y t 0) (fun t => y t 1) = y := by
    funext t j
    fin_cases j <;> rfl
  refine ⟨fun t => y t 0, fun t => y t 1,
    (equilibrium_iff_solves 𝔼).mpr ⟨hst ▸ hy, hi⟩,
    fun t => hay t 0, fun t => hay t 1, ⟨M, fun t ω => hM t 0 ω⟩,
    ⟨M, fun t ω => hM t 1 ω⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hne
  rw [← hst, hcon.1, hcon.2]

end Gali.MonetaryPolicyDesign.RuleExogenous
