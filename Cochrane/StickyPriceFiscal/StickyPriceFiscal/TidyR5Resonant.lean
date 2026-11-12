/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.LongTermDebt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The resonant AR(1) rate rise with long-term debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.3, p. 131, with the
long-term-debt model of §5.2, eqs. (5.17)–(5.21), pp. 127–129.

`LongTermDebt.ltd_ar1` solves the AR(1) rate rise `i_t = ηᵗ` in closed form,
`π_t = A ηᵗ + C λ₁^{−t}`, but only when `λ₁η ≠ 1`: at `η = 1/λ₁` the coefficient
`A = σκ/((λ₁η − 1)(1 − λ₂η))` blows up. This module closes that case.

## Main results

* `resA`, `resC`: the coefficients of the resonant solution.
* `ltd_ar1_resonant`: when `λ₁η = 1`, every equilibrium with bounded inflation and debt and
  adapted bounded bond prices has `q_t = −ηᵗ/(1 − ω̃η)` and
  `π_t = resA · t · ηᵗ + resC · ηᵗ` (the `t λ₁^{−t}` term of a double root).
* `ltd_ar1_resonant_exists`, `ltd_ar1_resonant_existsUnique`: such an equilibrium exists, and
  it is unique.
* `resC_eq_impactRHS`: the resonant impact `resC` is the value at `η = 1/λ₁` of the
  closed-form impact of `LongTermDebt.ar1_impact` (whose right side has no resonance).
* `tendsto_ar1_resonant`: **the resonant path is the limit of the non-resonant ones**: for every
  date `t`, `A(η) ηᵗ + C(η) λ₁^{−t} → resA · t · λ₁^{−t} + resC · λ₁^{−t}` as `η → 1/λ₁`,
  `η ≠ 1/λ₁`; `tendsto_ar1_impact_resonant` is the impact (`t = 0`).
-/

namespace Cochrane.StickyPriceFiscal.TidyR5Resonant

open Filter Topology NKModel TwoSidedMA FiscalNK LongTermDebt

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 131 (resonant case `λ₁η = 1`): the coefficient on `t ηᵗ` in inflation,
`σκ/(1 − λ₂η)`. -/
noncomputable def resA (σ β κ η : ℝ) : ℝ :=
  σ * κ / (1 - lam2 σ β κ * η)

/-- Cochrane (2023), p. 131 (resonant case `λ₁η = 1`): the coefficient on `ηᵗ`, pinned by the
valuation equation, `ρ − resA·ρη/(1 − ρη) − (1 − ρη) ω̃/(1 − ω̃η)`; it is the impact response. -/
noncomputable def resC (σ β κ ρ om η : ℝ) : ℝ :=
  ρ - resA σ β κ η * (ρ * η) / (1 - ρ * η) - (1 - ρ * η) * (om / (1 - om * η))

/-- Cochrane (2023), p. 131: the right side of `LongTermDebt.ar1_impact`,
`ρ/(1 − ρη)·[(1 − ρ/λ₁) − (1 − λ₁⁻¹)(1 − λ₂)/(1 − λ₂η)] − (1 − ρ/λ₁) ω̃/(1 − ω̃η)`, as a function
of the persistence `η` defined at every `η` (it has no resonance). -/
noncomputable def impactRHS (σ β κ ρ om η : ℝ) : ℝ :=
  ρ / (1 - ρ * η) * ((1 - ρ * (lam1 σ β κ)⁻¹) -
    (1 - (lam1 σ β κ)⁻¹) * (1 - lam2 σ β κ) / (1 - lam2 σ β κ * η)) -
  (1 - ρ * (lam1 σ β κ)⁻¹) * (om / (1 - om * η))

/-- Cochrane (2023), p. 131: in the resonant case the persistence is `η = 1/λ₁ ∈ (0, 1)`. -/
theorem resonant_eta {σ β κ η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hres : lam1 σ β κ * η = 1) : η = (lam1 σ β κ)⁻¹ ∧ 0 < η ∧ η < 1 := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have he : η = (lam1 σ β κ)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right hres
  refine ⟨he, ?_, ?_⟩
  · rw [he]; exact inv_pos.mpr (by linarith)
  · rw [he]; exact inv_lt_one_of_one_lt₀ h1

/-- Cochrane (2023), §5.3, p. 131, **the resonant case `λ₁η = 1`**: an unexpected AR(1) rate path
`i_t = ηᵗ` with `η = 1/λ₁`, long-term debt (`0 ≤ ω̃ < 1`), unchanged surpluses and
`v_{−1} = q_{−1} = 0`. In every equilibrium with bounded inflation and debt and adapted bounded
bond prices, `q_t = −ηᵗ/(1 − ω̃η)` and `π_t = resA · t · ηᵗ + resC · ηᵗ`. -/
theorem ltd_ar1_resonant {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1)
    (hres : lam1 σ β κ * η = 1) {x π v q rn : ℕ → Ω → ℝ}
    (h : LTD 𝔼 σ β κ ρ om (fun t _ => η ^ t) (fun _ _ => 0) 0 0 x π v q rn) (hqa : 𝔼.Adapted q)
    (hπb : BoundedProc π) (hvb : BoundedProc v) (hqb : BoundedProc q) (t : ℕ) (ω : Ω) :
    q t ω = -η ^ t / (1 - om * η) ∧
      π t ω = resA σ β κ η * t * η ^ t + resC σ β κ ρ om η * η ^ t := by
  have ha := mul_pos hσ hκ
  obtain ⟨-, hη0', hη1⟩ := resonant_eta hσ hκ hβ hres
  have hη0 := hη0'.le
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hoη : 0 < 1 - om * η := by nlinarith
  have hl2η : 0 < 1 - lam2 σ β κ * η := by nlinarith
  have hρη : 0 < 1 - ρ * η := by nlinarith
  have hρη1 : ρ * η < 1 := by linarith
  have hηb : ∀ t, |η ^ t| ≤ 1 := fun t => by
    rw [abs_of_nonneg (pow_nonneg hη0 t)]; exact pow_le_one₀ hη0 hη1.le
  -- the bond price
  have hi : 𝔼.Adapted (fun t (_ : Ω) => η ^ t) := fun t => 𝔼.const t _
  have hqc : q = fun t _ => -η ^ t / (1 - om * η) := by
    rw [bond_price 𝔼 hom0 hom1 hi (Mi := 1) (fun t _ => hηb t) hqa hqb h.2.2.2.1 h.2.2.2.2.1]
    refine (𝔼.eq_forwardSeries hom0 hom1 (M := 1) (fun t _ => by simpa using hηb t)
      (fun t => by rw [Pi.neg_apply, map_neg, hi t]) (fun t => ?_)
      ⟨1 / (1 - om * η), fun t _ => ?_⟩).symm
    · rw [𝔼.const]
      funext ω'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      field_simp
      ring
    · rw [abs_div, abs_neg, abs_of_pos hoη]
      exact div_le_div_of_nonneg_right (hηb t) hoη.le
  set c0 := om / (1 - om * η) with hc0
  set s'' : ℕ → ℝ := fun t => if t = 0 then c0 else 0 with hs''
  have hsadj : sAdj (fun t _ => η ^ t) (fun _ _ => (0 : ℝ)) rn = fun t _ => s'' t := by
    funext t ω'
    cases t with
    | zero =>
      simp only [sAdj, Pi.sub_apply, hs'', ↓reduceIte]
      rw [h.2.2.2.2.2, hqc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hc0, pow_zero]
      field_simp
      ring
    | succ t =>
      simp only [sAdj, Pi.add_apply, Pi.sub_apply, hs'', Nat.succ_ne_zero, ↓reduceIte]
      rw [h.2.2.2.2.1 t, hqc]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have hft := ltd_to_ftplnk 𝔼 h
  rw [hsadj] at hft
  set A := resA σ β κ η with hAdef
  set C := resC σ β κ ρ om η with hCdef
  set l1 := lam1 σ β κ with hl1
  set l2 := lam2 σ β κ with hl2
  have hA : A * (1 - l2 * η) = σ * κ := by
    rw [hAdef, resA, ← hl2]
    field_simp
  have hFd : ∀ t, ∑' k, l2 ^ k * η ^ (t + k) = η ^ t / (1 - l2 * η) := by
    intro t
    have := ((hasSum_geometric_of_lt_one (mul_nonneg h2.le hη0) (by nlinarith)).mul_left
      (η ^ t)).tsum_eq
    rw [← div_eq_mul_inv] at this
    rw [← this]
    exact tsum_congr fun k => by rw [pow_add, mul_pow]; ring
  set p : ℕ → ℝ := fun t => A * t * η ^ t + C * η ^ t with hp
  have hfac : ∀ t, p t - l1 * p (t + 1) = -(σ * κ) * ∑' k, l2 ^ k * η ^ (t + k) := by
    intro t
    have hkey : p t - l1 * p (t + 1) = -(A * η ^ t) := by
      simp only [hp]
      push_cast
      rw [pow_succ]
      linear_combination (-((A * (t + 1) + C) * η ^ t)) * hres
    have e1 : 1 - l2 * η ≠ 0 := hl2η.ne'
    rw [hkey, hFd t, ← hA]
    field_simp
  -- present values
  have hgeo : HasSum (fun j : ℕ => (j : ℝ) * (ρ * η) ^ j) (ρ * η / (1 - ρ * η) ^ 2) := by
    have := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := ρ * η)
      (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hρη1)
    exact this
  have hps : HasSum (fun j : ℕ => ρ ^ j * (p j + s'' j))
      (A * (ρ * η / (1 - ρ * η) ^ 2) + C * (1 - ρ * η)⁻¹ + c0) := by
    have hs0 : HasSum (fun j : ℕ => if j = 0 then c0 else 0) c0 := hasSum_ite_eq 0 c0
    have := ((hgeo.mul_left A).add ((hasSum_geometric_of_lt_one (by positivity) hρη1).mul_left
      C)).add hs0
    convert this using 1
    funext j
    simp only [hs'', hp]
    split_ifs with hj
    · subst hj; simp
    · rw [mul_pow]; ring
  have hηs : ∑' j, ρ ^ j * η ^ j = (1 - ρ * η)⁻¹ := by
    rw [← tsum_geometric_of_lt_one (by positivity) hρη1]
    exact tsum_congr fun j => by rw [mul_pow]
  have hfis : ∑' j, ρ ^ j * (p j + s'' j) - ρ * ∑' j, ρ ^ j * η ^ j = 0 := by
    rw [hps.tsum_eq, hηs, hCdef, resC, ← hAdef, ← hc0]
    field_simp
    ring
  -- bounds
  have hjb : ∀ j : ℕ, (j : ℝ) * η ^ j ≤ η / (1 - η) ^ 2 := fun j => by
    have hg := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := η)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hη0]; exact hη1)
    exact le_hasSum hg j (fun k _ => by positivity)
  have hpb : ∀ t, |p t| ≤ |A| * (η / (1 - η) ^ 2) + |C| := fun t => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [mul_assoc, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t * η ^ t)]
      exact mul_le_mul_of_nonneg_left (hjb t) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hηb t)
  have hsb : ∀ t, |s'' t| ≤ |c0| := fun t => by
    simp only [hs'']; split_ifs <;> simp
  have hdp := det_path 𝔼 hσ hκ hβ hρ0 hρ1 0 (c := fun t => η ^ t) hηb hsb hpb hfac hfis
  have hπ := (hdp.2 x π v (by exact hft) hπb hvb).1
  refine ⟨by rw [hqc], ?_⟩
  rw [hπ]

/-- Cochrane (2023), §5.3, p. 131 and p. 128 (resonant case): **an equilibrium exists** with
bounded output, inflation, debt and adapted bounded bond prices (`ltd_determinate`). -/
theorem ltd_ar1_resonant_exists {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1)
    (hres : lam1 σ β κ * η = 1) :
    ∃ x π v q rn, LTD 𝔼 σ β κ ρ om (fun t _ => η ^ t) (fun _ _ => 0) 0 0 x π v q rn ∧
      𝔼.Adapted q ∧ BoundedProc x ∧ BoundedProc π ∧ BoundedProc v ∧ BoundedProc q := by
  obtain ⟨-, hη0, hη1⟩ := resonant_eta hσ hκ hβ hres
  obtain ⟨x, π, v, q, rn, ⟨hL, hqa, hxb, hπb, hvb, hqb⟩, -⟩ :=
    ltd_determinate 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hom1 (i := fun t _ => η ^ t)
      (s := fun _ _ => 0) (vm1 := 0) (qm1 := 0) (Mi := 1) (Ms := 0) (Mv := 0) (Mq := 0)
      (fun t => 𝔼.const t _)
      (fun t _ => by
        rw [abs_of_nonneg (pow_nonneg hη0.le t)]; exact pow_le_one₀ hη0.le hη1.le)
      (fun t => 𝔼.const t _) (fun _ _ => by simp) (map_zero _) (fun _ => by simp)
      (map_zero _) (fun _ => by simp)
  exact ⟨x, π, v, q, rn, hL, hqa, hxb, hπb, hvb, hqb⟩

/-- Cochrane (2023), §5.3, p. 131, **existence and uniqueness in the resonant case**: there is
an equilibrium, every equilibrium (bounded inflation and debt, adapted bounded bond prices) has
the closed form of `ltd_ar1_resonant`, and any two coincide. -/
theorem ltd_ar1_resonant_existsUnique {σ β κ ρ om η : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1)
    (hres : lam1 σ β κ * η = 1) :
    (∃ x π v q rn, LTD 𝔼 σ β κ ρ om (fun t _ => η ^ t) (fun _ _ => 0) 0 0 x π v q rn ∧
      𝔼.Adapted q ∧ BoundedProc x ∧ BoundedProc π ∧ BoundedProc v ∧ BoundedProc q) ∧
    ∀ x π v q rn x' π' v' q' rn',
      LTD 𝔼 σ β κ ρ om (fun t _ => η ^ t) (fun _ _ => 0) 0 0 x π v q rn → 𝔼.Adapted q →
      BoundedProc π → BoundedProc v → BoundedProc q →
      LTD 𝔼 σ β κ ρ om (fun t _ => η ^ t) (fun _ _ => 0) 0 0 x' π' v' q' rn' →
      𝔼.Adapted q' → BoundedProc π' → BoundedProc v' → BoundedProc q' → π = π' ∧ q = q' := by
  refine ⟨ltd_ar1_resonant_exists 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hom1 hres,
    fun x π v q rn x' π' v' q' rn' h hqa hπb hvb hqb h' hqa' hπb' hvb' hqb' => ⟨?_, ?_⟩⟩
  · funext t ω
    rw [(ltd_ar1_resonant 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hom1 hres h hqa hπb hvb hqb t ω).2,
      (ltd_ar1_resonant 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hom1 hres h' hqa' hπb' hvb' hqb' t ω).2]
  · funext t ω
    rw [(ltd_ar1_resonant 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hom1 hres h hqa hπb hvb hqb t ω).1,
      (ltd_ar1_resonant 𝔼 hσ hκ hβ hρ0 hρ1 hom0 hom1 hres h' hqa' hπb' hvb' hqb' t ω).1]

/-- Cochrane (2023), p. 131: the resonant impact `resC` is the value of the closed-form impact
of `LongTermDebt.ar1_impact` at `η = 1/λ₁` (the right side of `ar1_impact` is continuous
through the resonance). -/
theorem resC_eq_impactRHS {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) :
    resC σ β κ ρ om (lam1 σ β κ)⁻¹ = impactRHS σ β κ ρ om (lam1 σ β κ)⁻¹ := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  obtain ⟨-, hη0, hη1⟩ := resonant_eta hσ hκ hβ (mul_inv_cancel₀ hl0)
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hoη : 1 - om * (lam1 σ β κ)⁻¹ ≠ 0 := by nlinarith
  have hl2η : 1 - lam2 σ β κ * (lam1 σ β κ)⁻¹ ≠ 0 := by nlinarith
  have hρη : 1 - ρ * (lam1 σ β κ)⁻¹ ≠ 0 := by nlinarith
  have hsk := sigma_kappa_eq ha hβ
  unfold resC resA impactRHS
  rw [hsk]
  obtain ⟨η, hη⟩ : ∃ η, lam1 σ β κ = η⁻¹ := ⟨(lam1 σ β κ)⁻¹, (inv_inv _).symm⟩
  rw [hη] at hoη hl2η hρη hl0 ⊢
  simp only [inv_inv] at hoη hl2η hρη ⊢
  have hηne : η ≠ 0 := by rintro rfl; simp at hl0
  generalize lam2 σ β κ = M at *
  field_simp

/-- Cochrane (2023), p. 131: `impactRHS` is continuous at the resonance `η = 1/λ₁`. -/
theorem continuousAt_impactRHS {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) :
    ContinuousAt (impactRHS σ β κ ρ om) (lam1 σ β κ)⁻¹ := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  obtain ⟨-, hη0, hη1⟩ := resonant_eta hσ hκ hβ (mul_inv_cancel₀ hl0)
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hoη : 1 - om * (lam1 σ β κ)⁻¹ ≠ 0 := by nlinarith
  have hl2η : 1 - lam2 σ β κ * (lam1 σ β κ)⁻¹ ≠ 0 := by nlinarith
  have hρη : 1 - ρ * (lam1 σ β κ)⁻¹ ≠ 0 := by nlinarith
  unfold impactRHS
  fun_prop (disch := assumption)

/-- Cochrane (2023), §5.3, p. 131, **the resonant path is the limit of the non-resonant paths**:
for every date `t`, the closed form `A(η) ηᵗ + C(η) λ₁^{−t}` of `LongTermDebt.ltd_ar1` converges,
as `η → 1/λ₁` with `η ≠ 1/λ₁`, to the resonant closed form `resA · t · λ₁^{−t} + resC · λ₁^{−t}`
of `ltd_ar1_resonant`. -/
theorem tendsto_ar1_resonant {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) (t : ℕ) :
    Tendsto (fun η => ar1A σ β κ η * η ^ t + ar1C σ β κ ρ om η * (lam1 σ β κ)⁻¹ ^ t)
      (𝓝[≠] (lam1 σ β κ)⁻¹)
      (𝓝 (resA σ β κ (lam1 σ β κ)⁻¹ * t * (lam1 σ β κ)⁻¹ ^ t +
        resC σ β κ ρ om (lam1 σ β κ)⁻¹ * (lam1 σ β κ)⁻¹ ^ t)) := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  obtain ⟨-, hη0, hη1⟩ := resonant_eta hσ hκ hβ (mul_inv_cancel₀ hl0)
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  set l1 := lam1 σ β κ with hl1
  set l2 := lam2 σ β κ with hl2
  set η0 := l1⁻¹ with hη0d
  have hq : l1 * η0 = 1 := mul_inv_cancel₀ hl0
  have hoη : 0 < 1 - om * η0 := by nlinarith
  have hl2η : 0 < 1 - l2 * η0 := by nlinarith
  have hρη : 0 < 1 - ρ * η0 := by nlinarith
  -- the three factors
  have hslope : Tendsto (fun η => (η - η0)⁻¹ * (η ^ t - η0 ^ t)) (𝓝[≠] η0)
      (𝓝 ((t : ℝ) * η0 ^ (t - 1))) := by
    have := (hasDerivAt_pow t η0).tendsto_slope
    refine this.congr fun η => ?_
    simp [slope_def_field, div_eq_inv_mul]
  have hfac : Tendsto (fun η => σ * κ / (l1 * (1 - l2 * η))) (𝓝[≠] η0)
      (𝓝 (σ * κ / (l1 * (1 - l2 * η0)))) := by
    have hc : ContinuousAt (fun η => σ * κ / (l1 * (1 - l2 * η))) η0 := by
      have : l1 * (1 - l2 * η0) ≠ 0 := mul_ne_zero hl0 hl2η.ne'
      fun_prop (disch := assumption)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have himp : Tendsto (impactRHS σ β κ ρ om) (𝓝[≠] η0) (𝓝 (impactRHS σ β κ ρ om η0)) :=
    (continuousAt_impactRHS hσ hκ hβ hρ0 hρ1 hom0 hom1).tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hfac.mul hslope).add (himp.mul_const (η0 ^ t))
  have hval : σ * κ / (l1 * (1 - l2 * η0)) * ((t : ℝ) * η0 ^ (t - 1)) +
      impactRHS σ β κ ρ om η0 * η0 ^ t =
      resA σ β κ η0 * t * η0 ^ t + resC σ β κ ρ om η0 * η0 ^ t := by
    rw [← resC_eq_impactRHS hσ hκ hβ hρ0 hρ1 hom0 hom1]
    congr 1
    rw [resA, ← hl2]
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp
    · have e : η0 ^ t = η0 ^ (t - 1) * η0 := by
        rw [← pow_succ, Nat.sub_add_cancel ht]
      rw [e]
      field_simp
      linear_combination (-1 : ℝ) * hq
  rw [← hval]
  refine hlim.congr' ?_
  -- eventually the denominators of `ar1_impact` are nonzero
  have hev1 : ∀ᶠ η in 𝓝 η0, 1 - ρ * η ≠ 0 :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne
      hρη.ne')
  have hev2 : ∀ᶠ η in 𝓝 η0, 1 - om * η ≠ 0 :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne
      hoη.ne')
  have hev3 : ∀ᶠ η in 𝓝 η0, 1 - l2 * η ≠ 0 :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne
      hl2η.ne')
  filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, nhdsWithin_le_nhds hev3,
    self_mem_nhdsWithin] with η e1 e2 e3 hne
  have hne' : η - η0 ≠ 0 := sub_ne_zero.mpr hne
  have hres : l1 * η ≠ 1 := by
    intro h0
    apply hne'
    have : l1 * (η - η0) = 0 := by rw [mul_sub, h0, hq, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hl0
    · exact h
  have himpη := ar1_impact hσ hκ hβ e1 e2 e3 hres
  have hC : ar1C σ β κ ρ om η = impactRHS σ β κ ρ om η - ar1A σ β κ η := by
    rw [impactRHS, ← himpη]; ring
  have hA : ar1A σ β κ η = σ * κ / (l1 * (1 - l2 * η)) * (η - η0)⁻¹ := by
    rw [ar1A, ← hl1, ← hl2]
    have : l1 * η - 1 = l1 * (η - η0) := by rw [mul_sub, hq]
    rw [this]
    field_simp
  rw [hC, hA]
  ring

/-- Cochrane (2023), p. 131: the impact response `A(η) + C(η)` converges to the resonant impact
`resC` as `η → 1/λ₁` (`t = 0` in `tendsto_ar1_resonant`). -/
theorem tendsto_ar1_impact_resonant {σ β κ ρ om : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hom0 : 0 ≤ om) (hom1 : om < 1) :
    Tendsto (fun η => ar1A σ β κ η + ar1C σ β κ ρ om η) (𝓝[≠] (lam1 σ β κ)⁻¹)
      (𝓝 (resC σ β κ ρ om (lam1 σ β κ)⁻¹)) := by
  have := tendsto_ar1_resonant hσ hκ hβ hρ0 hρ1 hom0 hom1 0
  simp only [pow_zero, mul_one, Nat.cast_zero, mul_zero, zero_add] at this
  exact this

end Cochrane.StickyPriceFiscal.TidyR5Resonant
