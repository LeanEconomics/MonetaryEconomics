/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.Expectations

/-!
# Exercise 2.6: equilibrium uniqueness in the money-in-the-utility-function model

Galí (2015), Chapter 2, Exercise 2.6, p. 49, using eqs. (43) (p. 37) and (47) (p. 39) and the
rule `i_t = ρ + φ_π π_t` (fn. 13, p. 41).

The log-linear MIU equilibrium conditions, stated here for an arbitrary `ExpectationSystem`:

* (43) `y_t = ψ_y + ψ_ya a_t + ψ_yi i_t` (`ψ_y` the additive constant),
  `ψ_ya = (1+φ)/D`, `ψ_yi = −ϖ(1−α)/D`, `D = σ(1−α)+φ+α`;
* (47) `y_t = E_t y_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ϖ(E_t i_{t+1} − i_t) − ρ)`;
* the rule `i_t = ρ + φ_π π_t`.

## Main results

* `inflEq_of_isEquilibrium`, `isEquilibrium_iff`: an equilibrium is exactly (43), the rule, and
  `(1 + φ_π k) E_t π_{t+1} = φ_π(1+k) π_t − σψ_ya(E_t a_{t+1} − a_t)`, `k = ϖ + σψ_yi`; with
  no technology shocks `E_t π_{t+1} = c π_t`, `c = φ_π(1+ϖ+σψ_yi)/(1+φ_π(ϖ+σψ_yi))`
  (`expected_infl_eq_c`).
* `kappa_eq`, `kappa_nonneg`: `ϖ + σψ_yi = ϖ(φ+α)/D ≥ 0`.
* `one_lt_abs_c_iff`: for `φ_π ≥ 0`, `|c| > 1 ⟺ φ_π > 1`.
* `unique_of_one_lt_abs_c`, `exists_equilibrium`: for `φ_π > 1` there is exactly one bounded
  equilibrium (for any bounded adapted technology).
* `not_unique_of_le_one`: for `0 ≤ φ_π ≤ 1` every bounded equilibrium has a second one.
* `determinate_iff`: with `a ≡ 0` the unique bounded equilibrium is `π ≡ 0` iff `φ_π > 1`.
* `counterexample_negative_phi`: the sign restriction `φ_π ≥ 0` (implicit in the book) is
  needed: `φ_π = −2`, `ϖ = 0` gives a determinate equilibrium although `φ_π < 1`.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_6

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (18), p. 23: `D = σ(1−α) + φ + α`. -/
def bigD (σ φ α : ℝ) : ℝ := σ * (1 - α) + φ + α

/-- Galí (2015), eq. (43), p. 37: `ψ_ya = (1+φ)/D`. -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / bigD σ φ α

/-- Galí (2015), eq. (43), p. 37: `ψ_yi = −ϖ(1−α)/D`. -/
noncomputable def psiYI (σ φ α ϖ : ℝ) : ℝ := -(ϖ * (1 - α)) / bigD σ φ α

/-- Galí (2015), Ex. 2.6, p. 49: the coefficient `c = φ_π(1+k)/(1+φ_π k)`, `k = ϖ + σψ_yi`. -/
noncomputable def cCoef (φπ k : ℝ) : ℝ := φπ * (1 + k) / (1 + φπ * k)

/-- Galí (2015), eq. (47), p. 39: the right side
`E_t y_{t+1} − σ⁻¹(i_t − E_t π_{t+1} − ϖ(E_t i_{t+1} − i_t) − ρ)`. -/
noncomputable def rhs47 (σ ρ ϖ : ℝ) (y infl i : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (y (t + 1)) -
    σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - ϖ • (𝔼.E t (i (t + 1)) - i t) - fun _ => ρ)

/-- Galí (2015), Ex. 2.6, p. 49 (**existence**): the bounded adapted forcing
`u_t = s (E_t a_{t+1} − a_t)` of the inflation equation, `s = σψ_ya/(φ_π(1+k))`. -/
noncomputable def forcing (s : ℝ) (a : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  s • (𝔼.E t (a (t + 1)) - a t)

variable (σ ρ ϖ ψy ψya ψyi φπ : ℝ) (a y infl i : ℕ → Ω → ℝ)

/-- Galí (2015), Ex. 2.6, p. 49: an equilibrium of the MIU model under `i_t = ρ + φ_π π_t`:
conditions (43), (47) and the rule. -/
structure IsEquilibrium where
  /-- Eq. (43), p. 37. -/
  eq43 : ∀ t, y t = (fun _ => ψy) + ψya • a t + ψyi • i t
  /-- Eq. (47), p. 39. -/
  eq47 : ∀ t, y t = rhs47 𝔼 σ ρ ϖ y infl i t
  /-- The rule `i_t = ρ + φ_π π_t` (Ex. 2.6). -/
  rule : ∀ t, i t = (fun _ => ρ) + φπ • infl t

/-- Galí (2015), Ex. 2.6, p. 49: the reduced inflation equation
`(1 + φ_π k) E_t π_{t+1} = φ_π(1+k) π_t − σψ_ya(E_t a_{t+1} − a_t)`, `k = ϖ + σψ_yi`. -/
def InflEq : Prop :=
  ∀ t, (1 + φπ * (ϖ + σ * ψyi)) • 𝔼.E t (infl (t + 1)) =
    (φπ * (1 + (ϖ + σ * ψyi))) • infl t - (σ * ψya) • (𝔼.E t (a (t + 1)) - a t)

variable {𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i}

/-- Pointwise form of eq. (43) and its date-`t` expectation (Galí (2015), p. 37). -/
theorem eq43_apply (h43 : ∀ t, y t = (fun _ => ψy) + ψya • a t + ψyi • i t) (t : ℕ) (ω : Ω) :
    y t ω = ψy + ψya * a t ω + ψyi * i t ω ∧
      𝔼.E t (y (t + 1)) ω = ψy + ψya * 𝔼.E t (a (t + 1)) ω + ψyi * 𝔼.E t (i (t + 1)) ω := by
  refine ⟨by simp [h43 t], ?_⟩
  rw [h43 (t + 1)]
  simp [map_add, map_smul, 𝔼.const]

/-- Pointwise form of the rule `i_t = ρ + φ_π π_t` and its expectation (Galí (2015), Ex. 2.6). -/
theorem rule_apply (hr : ∀ t, i t = (fun _ => ρ) + φπ • infl t) (t : ℕ) (ω : Ω) :
    i t ω = ρ + φπ * infl t ω ∧ 𝔼.E t (i (t + 1)) ω = ρ + φπ * 𝔼.E t (infl (t + 1)) ω := by
  refine ⟨by simp [hr t], ?_⟩
  rw [hr (t + 1)]
  simp [map_add, map_smul, 𝔼.const]

/-- Galí (2015), eq. (47), p. 39, pointwise and multiplied through by `σ ≠ 0`. -/
theorem eq47_apply_iff (hσ : σ ≠ 0) (t : ℕ) (ω : Ω) :
    y t ω = rhs47 𝔼 σ ρ ϖ y infl i t ω ↔
      σ * (y t ω - 𝔼.E t (y (t + 1)) ω) =
        -(i t ω - 𝔼.E t (infl (t + 1)) ω - ϖ * (𝔼.E t (i (t + 1)) ω - i t ω) - ρ) := by
  simp only [rhs47, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    have : y t ω - 𝔼.E t (y (t + 1)) ω =
        -(i t ω - 𝔼.E t (infl (t + 1)) ω - ϖ * (𝔼.E t (i (t + 1)) ω - i t ω) - ρ) / σ := by
      rw [← h]; field_simp
    rw [div_eq_inv_mul] at this
    linarith

/-- Galí (2015), Ex. 2.6, p. 49: every equilibrium satisfies the reduced inflation equation. -/
theorem inflEq_of_isEquilibrium (hσ : σ ≠ 0)
    (h : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i) :
    InflEq 𝔼 σ ϖ ψya ψyi φπ a infl := by
  intro t
  funext ω
  obtain ⟨hy, hEy⟩ := eq43_apply h.eq43 t ω
  obtain ⟨hi, hEi⟩ := rule_apply (𝔼 := 𝔼) h.rule t ω
  have h47 := (eq47_apply_iff hσ t ω).1 (congrFun (h.eq47 t) ω)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [hy, hEy, hEi, hi] at h47
  linear_combination -h47

/-- Galí (2015), Ex. 2.6, p. 49: conversely, (43), the rule and the reduced inflation equation
give (47); so an equilibrium is exactly (43) + rule + `InflEq`. -/
theorem isEquilibrium_iff (hσ : σ ≠ 0) :
    Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i) ↔
      (∀ t, y t = (fun _ => ψy) + ψya • a t + ψyi • i t) ∧
      (∀ t, i t = (fun _ => ρ) + φπ • infl t) ∧ InflEq 𝔼 σ ϖ ψya ψyi φπ a infl := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.eq43, h.rule, inflEq_of_isEquilibrium hσ h⟩
  · rintro ⟨h43, hr, hI⟩
    refine ⟨⟨h43, fun t => ?_, hr⟩⟩
    funext ω
    obtain ⟨hy, hEy⟩ := eq43_apply h43 t ω
    obtain ⟨hi, hEi⟩ := rule_apply (𝔼 := 𝔼) hr t ω
    have hIt := congrFun (hI t) ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hIt
    refine (eq47_apply_iff hσ t ω).2 ?_
    rw [hy, hEy, hEi, hi]
    linear_combination -hIt

/-- Galí (2015), Ex. 2.6, p. 49: with no technology shocks (`a ≡ 0`) and `1 + φ_π k ≠ 0`,
every equilibrium satisfies `E_t π_{t+1} = c π_t`. -/
theorem expected_infl_eq_c (hσ : σ ≠ 0) (ha : ∀ t, a t = 0)
    (hk : 1 + φπ * (ϖ + σ * ψyi) ≠ 0) (h : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i)
    (t : ℕ) : 𝔼.E t (infl (t + 1)) = cCoef φπ (ϖ + σ * ψyi) • infl t := by
  have hI := inflEq_of_isEquilibrium hσ h t
  rw [ha, ha, map_zero, sub_zero, smul_zero, sub_zero] at hI
  funext ω
  have := congrFun hI ω
  simp only [Pi.smul_apply, smul_eq_mul] at this
  simp only [Pi.smul_apply, smul_eq_mul, cCoef]
  field_simp
  linarith

/-- Galí (2015), Ex. 2.6 and eq. (43), p. 37: `ϖ + σψ_yi = ϖ(φ+α)/D` (for `D ≠ 0`). -/
theorem kappa_eq {σ φ α ϖ : ℝ} (hD : bigD σ φ α ≠ 0) :
    ϖ + σ * psiYI σ φ α ϖ = ϖ * (φ + α) / bigD σ φ α := by
  rw [psiYI]
  field_simp
  rw [bigD]
  ring

/-- Galí (2015), Ex. 2.6, p. 49: `ϖ + σψ_yi ≥ 0` under `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1` and the
book's maintained `ϖ ≥ 0` (p. 38). -/
theorem kappa_nonneg {σ φ α ϖ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hϖ : 0 ≤ ϖ) : 0 ≤ ϖ + σ * psiYI σ φ α ϖ := by
  have hD : 0 < bigD σ φ α := by
    rw [bigD]; nlinarith
  rw [kappa_eq hD.ne']
  exact div_nonneg (mul_nonneg hϖ (by linarith)) hD.le

/-- Galí (2015), Ex. 2.6, p. 49: for `φ_π ≥ 0` and `k ≥ 0`, `|c| > 1 ⟺ φ_π > 1`. -/
theorem one_lt_abs_c_iff {φπ k : ℝ} (hφ : 0 ≤ φπ) (hk : 0 ≤ k) :
    1 < |cCoef φπ k| ↔ 1 < φπ := by
  have hd : 0 < 1 + φπ * k := by nlinarith
  have hc : 0 ≤ cCoef φπ k := div_nonneg (mul_nonneg hφ (by linarith)) hd.le
  rw [abs_of_nonneg hc, cCoef, one_lt_div hd]
  constructor <;> intro h <;> nlinarith

/-- Galí (2015), Ex. 2.6, p. 49 (**uniqueness**): if `1 + φ_π k ≠ 0` and `|c| > 1`, two
bounded equilibria with the same technology coincide. -/
theorem unique_of_one_lt_abs_c (hσ : σ ≠ 0) (hk : 1 + φπ * (ϖ + σ * ψyi) ≠ 0)
    (hc : 1 < |cCoef φπ (ϖ + σ * ψyi)|) {y' infl' i' : ℕ → Ω → ℝ}
    (h : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i)
    (h' : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y' infl' i')
    (hb : BoundedProc infl) (hb' : BoundedProc infl') :
    y = y' ∧ infl = infl' ∧ i = i' := by
  set k := ϖ + σ * ψyi with hkdef
  set c := cCoef φπ k with hcdef
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hc; linarith
  have hI := inflEq_of_isEquilibrium hσ h
  have hI' := inflEq_of_isEquilibrium hσ h'
  -- the difference d solves d_t = c⁻¹ E_t d_{t+1}
  have hd : ∀ t, (infl - infl') t = c⁻¹ • 𝔼.E t ((infl - infl') (t + 1)) + 0 := by
    intro t
    funext ω
    have e1 := congrFun (hI t) ω
    have e2 := congrFun (hI' t) ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1 e2
    rw [← hkdef] at e1 e2
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_sub,
      Pi.zero_apply, add_zero]
    have key : c * (infl t ω - infl' t ω) =
        𝔼.E t (infl (t + 1)) ω - 𝔼.E t (infl' (t + 1)) ω := by
      rw [hcdef, cCoef]
      field_simp
      linear_combination e2 - e1
    rw [← key, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = c⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t; simp
  have hbd : BoundedProc (infl - infl') := by
    obtain ⟨M, hM⟩ := hb
    obtain ⟨M', hM'⟩ := hb'
    exact ⟨M + M', fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) (hM' t ω))⟩
  have hca : |c⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hc
  have hdz := 𝔼.forward_unique hca hd hz hbd ⟨0, fun _ _ => by simp⟩
  have hπ : infl = infl' := sub_eq_zero.1 hdz
  have hi : i = i' := by
    funext t; rw [h.rule t, h'.rule t, hπ]
  refine ⟨?_, hπ, hi⟩
  funext t; rw [h.eq43 t, h'.eq43 t, hi]

/-- Galí (2015), Ex. 2.6, p. 49 (**existence**): for `φ_π > 1`, `k ≥ 0`, and bounded adapted
technology, there is a bounded adapted equilibrium: `π` is the forward series
`∑ c⁻ʲ E_t u_{t+j}`, `i_t = ρ + φ_π π_t`, and `y` from (43). -/
theorem exists_equilibrium (hσ : σ ≠ 0) (hφ : 1 < φπ) (hk : 0 ≤ ϖ + σ * ψyi)
    (ha : 𝔼.Adapted a) {Ma : ℝ} (hab : ∀ t ω, |a t ω| ≤ Ma) :
    ∃ y' infl' i' : ℕ → Ω → ℝ, Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y' infl' i') ∧
      BoundedProc infl' ∧ 𝔼.Adapted infl' ∧ 𝔼.Adapted i' ∧ 𝔼.Adapted y' := by
  set k := ϖ + σ * ψyi with hkdef
  set c := cCoef φπ k with hcdef
  have hd : 0 < 1 + φπ * k := by nlinarith
  have hc1 : 1 < c := by
    have := (one_lt_abs_c_iff (by linarith) hk).2 hφ
    have hc0' : 0 ≤ cCoef φπ k := div_nonneg (mul_nonneg (by linarith) (by linarith)) hd.le
    rw [abs_of_nonneg hc0'] at this
    exact this
  have hcinv0 : 0 ≤ c⁻¹ := inv_nonneg.2 (by linarith)
  have hcinv1 : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc1
  set s := σ * ψya / (φπ * (1 + k)) with hsdef
  set u := forcing 𝔼 s a with hudef
  have hub : ∀ t ω, |u t ω| ≤ |s| * (Ma + Ma) := by
    intro t ω
    simp only [hudef, forcing, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
      (add_le_add (𝔼.abs_E_le (hab (t + 1)) t ω) (hab t ω))) (abs_nonneg s)
  have hua : 𝔼.Adapted u := by
    intro t
    simp only [hudef, forcing, map_smul, map_sub, 𝔼.E_E_self, ha t]
  set p := 𝔼.forwardSeries c⁻¹ u with hpdef
  have hp := 𝔼.forwardSeries_solves hcinv0 hcinv1 hub hua
  rw [← hpdef] at hp
  have hpa : 𝔼.Adapted p := by
    intro t
    rw [hp t, map_add, map_smul, 𝔼.E_E_self, hua t]
  refine ⟨fun t => (fun _ => ψy) + ψya • a t + ψyi • ((fun _ => ρ) + φπ • p t), p,
    fun t => (fun _ => ρ) + φπ • p t, ?_, 𝔼.forwardSeries_bounded hcinv0 hcinv1 hub, hpa, ?_, ?_⟩
  · refine (isEquilibrium_iff hσ).2 ⟨fun _ => rfl, fun _ => rfl, fun t => ?_⟩
    funext ω
    have e := congrFun (hp t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hudef, forcing, Pi.sub_apply] at e
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have hφ0 : φπ * (1 + k) ≠ 0 := by positivity
    rw [e]
    simp only [hcdef, cCoef, hsdef]
    field_simp
    ring
  · intro t
    simp only [map_add, map_smul, 𝔼.const, hpa t]
  · intro t
    simp only [map_add, map_smul, 𝔼.const, hpa t, ha t]

/-- Galí (2015), Ex. 2.6, p. 49 (**multiplicity**): if `0 ≤ φ_π ≤ 1` and `k ≥ 0`, every
equilibrium `(y, π, i)` has a second, distinct one, `π_t + cᵗ` (with `i`, `y` adjusted),
which is bounded (and adapted) whenever the first is: `0 ≤ c ≤ 1`. -/
theorem not_unique_of_le_one [Nonempty Ω] (hσ : σ ≠ 0) (hφ0 : 0 ≤ φπ) (hφ1 : φπ ≤ 1)
    (hk : 0 ≤ ϖ + σ * ψyi) (h : IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y infl i)
    (hb : BoundedProc infl) :
    ∃ y' infl' i' : ℕ → Ω → ℝ, Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ a y' infl' i') ∧
      BoundedProc infl' ∧ infl' ≠ infl ∧
      (𝔼.Adapted infl → 𝔼.Adapted infl') := by
  set k := ϖ + σ * ψyi with hkdef
  set c := cCoef φπ k with hcdef
  have hd : 0 < 1 + φπ * k := by nlinarith
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg hφ0 (by linarith)) hd.le
  have hc1 : c ≤ 1 := by
    rw [hcdef, cCoef, div_le_one hd]; nlinarith
  set d : ℕ → Ω → ℝ := fun t _ => c ^ t with hddef
  have hI := inflEq_of_isEquilibrium hσ h
  refine ⟨fun t => y t + (ψyi * φπ) • d t, fun t => infl t + d t, fun t => i t + φπ • d t, ?_,
    ?_, ?_, ?_⟩
  · refine (isEquilibrium_iff hσ).2 ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
    · rw [h.eq43 t, smul_add, mul_smul]; abel
    · rw [h.rule t, smul_add]; abel
    · funext ω
      have e := congrFun (hI t) ω
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, map_add, hddef,
        𝔼.const]
      have hcd : (1 + φπ * k) * c = φπ * (1 + k) := by
        rw [hcdef, cCoef]; field_simp
      rw [pow_succ]
      linear_combination e + c ^ t * hcd
  · obtain ⟨M, hM⟩ := hb
    refine ⟨M + 1, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)⟩
    simp only [hddef, abs_pow, abs_of_nonneg hc0]
    exact pow_le_one₀ hc0 hc1
  · intro heq
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun heq 0) ω
    simp [hddef] at this
  · intro hpa t
    simp only [map_add, hpa t, hddef, 𝔼.const]

/-- Galí (2015), Ex. 2.6, p. 49: with no technology shocks the zero-inflation path
`π ≡ 0`, `i ≡ ρ`, `y ≡ ψ_y + ψ_yi ρ` is an equilibrium. -/
theorem zero_isEquilibrium (hσ : σ ≠ 0) :
    Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ (fun _ => 0)
      (fun _ _ => ψy + ψyi * ρ) (fun _ => 0) (fun _ _ => ρ)) := by
  refine (isEquilibrium_iff hσ).2 ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω; simp
  · funext ω; simp
  · funext ω; simp

/-- Galí (2015), Ex. 2.6, p. 49 (**the exercise**): with no technology shocks, `σ > 0` and
`k = ϖ + σψ_yi ≥ 0` (`kappa_nonneg`), the unique bounded equilibrium is `π ≡ 0` if and only if
`φ_π > 1` (for `φ_π ≥ 0`). -/
theorem determinate_iff [Nonempty Ω] (hσ : σ ≠ 0) (hφ0 : 0 ≤ φπ) (hk : 0 ≤ ϖ + σ * ψyi) :
    (∀ y' infl' i' : ℕ → Ω → ℝ,
      Nonempty (IsEquilibrium 𝔼 σ ρ ϖ ψy ψya ψyi φπ (fun _ => 0) y' infl' i') →
        BoundedProc infl' → infl' = fun _ => 0) ↔ 1 < φπ := by
  constructor
  · intro hU
    by_contra hle
    push Not at hle
    obtain ⟨y', infl', i', ⟨h'⟩, hb', hne, -⟩ := not_unique_of_le_one hσ hφ0 hle hk
      (zero_isEquilibrium (𝔼 := 𝔼) (ψya := ψya) (φπ := φπ) hσ).some ⟨0, fun _ _ => by simp⟩
    exact hne (hU _ _ _ ⟨h'⟩ hb')
  · intro hφ y' infl' i' ⟨h'⟩ hb'
    have hd : 0 < 1 + φπ * (ϖ + σ * ψyi) := by nlinarith
    have hc := (one_lt_abs_c_iff hφ0 hk).2 hφ
    exact (unique_of_one_lt_abs_c hσ hd.ne' hc h'
      (zero_isEquilibrium (𝔼 := 𝔼) (ψya := ψya) (φπ := φπ) hσ).some hb'
      ⟨0, fun _ _ => by simp⟩).2.1

/-- Galí (2015), Ex. 2.6, p. 49 (**correction**: the restriction `φ_π ≥ 0` is needed): with
`ϖ = 0` (so `k = 0`) and `φ_π = −2 < 1` we get `|c| = 2 > 1`, so the bounded equilibrium is
still unique. -/
theorem counterexample_negative_phi :
    1 < |cCoef (-2) 0| ∧ (1 : ℝ) + (-2) * 0 ≠ 0 ∧ ¬ (1 < (-2 : ℝ)) := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [cCoef]
  norm_num

/-- Galí (2015), Ex. 2.6, p. 49 (**correction**, applied): with `ϖ = 0`, `ψ_yi = 0` and
`φ_π = −2`, two bounded equilibria coincide, although `φ_π < 1`. -/
theorem unique_negative_phi (hσ : σ ≠ 0) {y' infl' i' : ℕ → Ω → ℝ}
    (h : IsEquilibrium 𝔼 σ ρ 0 ψy ψya 0 (-2) a y infl i)
    (h' : IsEquilibrium 𝔼 σ ρ 0 ψy ψya 0 (-2) a y' infl' i')
    (hb : BoundedProc infl) (hb' : BoundedProc infl') :
    y = y' ∧ infl = infl' ∧ i = i' :=
  unique_of_one_lt_abs_c hσ (by norm_num) (by simpa using counterexample_negative_phi.1) h h'
    hb hb'

end Gali.ClassicalMonetaryModel.Ex2_6
