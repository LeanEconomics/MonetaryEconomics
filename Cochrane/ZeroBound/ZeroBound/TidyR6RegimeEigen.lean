/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.FutureSelection
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Leaving the active-money regime moves an eigenvalue across the unit circle

Cochrane (2023), Chapter 24, p. 523: "Shifting from active-fiscal passive-money to active-money
passive-fiscal requires a discrete shift in variables, to move eigenvalues from stable to
unstable. But if we are simply viewing shifting correlations … a shift of `θ` in `i*_t = θπ*_t`
… has no such momentous or discontinuous consequences."

The model is the Leeper model (23.1)–(23.4) of `FutureSelection.LeeperEq` with constant
coefficients `φ`, `γ`, `0 < ρ < 1`, under perfect foresight and without disturbances; the regime
parameters are `(φ, γ)`. Its transition matrix is `diag(φ, λ)`, `λ = (1 − γ)/ρ`.

## Main results

* Eigenvalues: `leeper_charpoly` (`det(A − zI) = (φ − z)(λ − z)`), `eig_continuous` (the
  eigenvalues are continuous in the regime parameters).
* The complete determinacy map (`leeper_pf_char`, `bounded_geom_iff`, `mem_eqSet_iff`): for
  `c₀ ≠ 0` there is exactly one bounded equilibrium iff `(φ, γ)` is active-money/passive-fiscal
  (`1 < |φ|`, `|λ| ≤ 1`) or active-fiscal/passive-money (`|φ| ≤ 1`, `1 < |λ|`)
  (`existsUnique_iff`); none iff both eigenvalues lie outside the unit circle
  (`eqSet_empty_iff`); uncountably many iff both lie inside or on it (`eqSet_uncountable`).
  Initial inflation is `π₀ = 0` in the first regime and `π₀ = c₀` in the second
  (`am_pi0`, `af_pi0`).
* **The p. 523 claim** (`path_crosses`): along every continuous path of regime parameters from
  the active-money to the active-fiscal regime, `|φ|` crosses `1`, `|λ|` crosses `1`, and at some
  intermediate parameter the two eigenvalues have equal modulus, where the model has no unique
  bounded equilibrium. Hence the two determinate regions cannot be joined inside the determinate
  region (`no_determinate_path`), and the equilibrium response `∂π₀/∂c₀` jumps from `0` to `1`
  (`pi0_response_jump`): a regime change is a discrete shift.
* The contrast (`ftpl_existsUnique`, `ftpl_continuous_theta`): in the frictionless fiscal-theory
  equilibrium with an on-equilibrium rate `i_t = θπ_t + w_t`, for an arbitrary
  `ExpectationSystem`, every `θ ∈ ℝ` gives exactly one equilibrium and it is continuous
  (polynomial) in `θ`; nothing happens at `|θ| = 1`.
-/

namespace Cochrane.ZeroBound.TidyR6RegimeEigen

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.FutureSelection

/-! ## The eigenvalues -/

/-- Cochrane (2023), (23.1)–(23.4), p. 512 and p. 523: the fiscal eigenvalue `λ = (1 − γ)/ρ` of
the Leeper model (from `ρE_tv_{t+1} = (1 − γ)v_t`, `FutureSelection.leeper_debt_eq`). -/
noncomputable def lamF (ρ γ : ℝ) : ℝ := (1 - γ) / ρ

/-- Cochrane (2023), p. 523: the transition matrix of `(π, v)` in the Leeper model without
disturbances, `diag(φ, λ)`. -/
noncomputable def leeperMatrix (ρ φ γ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![φ, 0; 0, lamF ρ γ]

/-- Cochrane (2023), p. 523: the eigenvalues are `φ` and `λ`:
`det(A − zI) = (φ − z)(λ − z)`. -/
theorem leeper_charpoly (ρ φ γ z : ℝ) :
    (leeperMatrix ρ φ γ - z • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det =
      (φ - z) * (lamF ρ γ - z) := by
  rw [Matrix.det_fin_two]
  simp [leeperMatrix]

/-- Cochrane (2023), p. 523 ("to move eigenvalues"): the eigenvalues `(φ, λ)` are continuous
functions of the regime parameters `(φ, γ)`. -/
theorem eig_continuous (ρ : ℝ) : Continuous fun q : ℝ × ℝ => (q.1, lamF ρ q.2) := by
  unfold lamF
  fun_prop

/-! ## The determinacy map -/

/-- Cochrane (2023), p. 523: the active-money / passive-fiscal regime, `1 < |φ|`, `|λ| ≤ 1`. -/
def AM (ρ φ γ : ℝ) : Prop := 1 < |φ| ∧ |lamF ρ γ| ≤ 1

/-- Cochrane (2023), p. 523: the active-fiscal / passive-money regime, `|φ| ≤ 1`, `1 < |λ|`. -/
def AF (ρ φ γ : ℝ) : Prop := |φ| ≤ 1 ∧ 1 < |lamF ρ γ|

/-- Cochrane (2023), (23.1)–(23.4): the Leeper model with constant coefficients, perfect
foresight and no disturbances. -/
def LEq (ρ φ γ c0 : ℝ) (π v : ℕ → Unit → ℝ) : Prop :=
  LeeperEq perfectForesight ρ (fun _ => φ) (fun _ => γ) (fun _ => c0) 0 0 π v

/-- Cochrane (2023), p. 523: the inflation path `π_t = φᵗp`. -/
def eqPi (φ p : ℝ) : ℕ → Unit → ℝ := fun t _ => φ ^ t * p

/-- Cochrane (2023), p. 523: the debt path `v_t = λᵗ(c₀ − p)/ρ`. -/
noncomputable def eqV (ρ γ c0 p : ℝ) : ℕ → Unit → ℝ := fun t _ => lamF ρ γ ^ t * ((c0 - p) / ρ)

/-- Cochrane (2023), (23.1)–(23.4): the solutions of the model are exactly the paths
`π_t = φᵗπ₀`, `v_t = λᵗ(c₀ − π₀)/ρ` (`ρ ≠ 0`). -/
theorem leeper_pf_char {ρ φ γ c0 : ℝ} (hρ : ρ ≠ 0) (π v : ℕ → Unit → ℝ) :
    LEq ρ φ γ c0 π v ↔ π = eqPi φ (π 0 ()) ∧ v = eqV ρ γ c0 (π 0 ()) := by
  constructor
  · rintro ⟨h0, h⟩
    have hπ : ∀ t, π t () = φ ^ t * π 0 () := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have := congrFun (h t).1 ()
        simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Pi.zero_apply, add_zero] at this
        rw [this, ih, pow_succ]
        ring
    have hv0 : v 0 () = (c0 - π 0 ()) / ρ := by
      have := congrFun h0 ()
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at this
      field_simp
      linarith
    have hv : ∀ t, v t () = lamF ρ γ ^ t * v 0 () := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        have a := congrFun (h t).1 ()
        have b := congrFun (h t).2 ()
        simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Pi.zero_apply, add_zero, Pi.sub_apply] at a b
        rw [a] at b
        have : v (t + 1) () = lamF ρ γ * v t () := by
          unfold lamF
          field_simp
          linarith
        rw [this, ih, pow_succ]
        ring
    refine ⟨funext fun t => funext fun u => ?_, funext fun t => funext fun u => ?_⟩
    · cases u; exact hπ t
    · cases u; rw [hv t, hv0]; rfl
  · rintro ⟨hπ, hv⟩
    rw [hπ, hv]
    refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
    · funext u
      simp only [eqV, eqPi, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, pow_zero, one_mul]
      field_simp
    · funext u
      simp only [perfectForesight, LinearMap.id_apply, eqPi, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply, add_zero, pow_succ]
      ring
    · funext u
      simp only [eqV, eqPi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero,
        Pi.sub_apply, lamF, pow_succ]
      field_simp
      ring

/-- Cochrane (2023), p. 523: a geometric path `aᵗc` is bounded iff `|a| ≤ 1` or `c = 0`. -/
theorem bounded_geom_iff (a c : ℝ) :
    BoundedProc (fun t (_ : Unit) => a ^ t * c) ↔ |a| ≤ 1 ∨ c = 0 := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hc⟩ := hcon
    have hcpos : 0 < |c| := abs_pos.mpr hc
    have ht := (tendsto_pow_atTop_atTop_of_one_lt ha).atTop_mul_const hcpos
    obtain ⟨t, htt⟩ := (ht.eventually (eventually_gt_atTop M)).exists
    have := hM t ()
    rw [abs_mul, abs_pow] at this
    linarith
  · rintro (h | h)
    · refine ⟨|c|, fun t _ => ?_⟩
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_left (abs_nonneg c) (pow_le_one₀ (abs_nonneg a) h)
    · exact ⟨0, fun t _ => by simp [h]⟩

/-- Cochrane (2023), p. 523: the bounded equilibria of the Leeper model. -/
def EqSet (ρ φ γ c0 : ℝ) : Set ((ℕ → Unit → ℝ) × (ℕ → Unit → ℝ)) :=
  {z | BoundedProc z.1 ∧ BoundedProc z.2 ∧ LEq ρ φ γ c0 z.1 z.2}

/-- Cochrane (2023), p. 523: the admissible initial inflation rates: a bounded inflation path
needs `|φ| ≤ 1` or `π₀ = 0`, a bounded debt path needs `|λ| ≤ 1` or `π₀ = c₀`. -/
def Adm (ρ φ γ c0 p : ℝ) : Prop := (|φ| ≤ 1 ∨ p = 0) ∧ (|lamF ρ γ| ≤ 1 ∨ p = c0)

/-- Cochrane (2023), p. 523: the bounded equilibria are exactly `(φᵗp, λᵗ(c₀ − p)/ρ)` for
admissible `p` (`ρ > 0`). -/
theorem mem_eqSet_iff {ρ φ γ c0 : ℝ} (hρ : 0 < ρ) (z : (ℕ → Unit → ℝ) × (ℕ → Unit → ℝ)) :
    z ∈ EqSet ρ φ γ c0 ↔ ∃ p, Adm ρ φ γ c0 p ∧ z = (eqPi φ p, eqV ρ γ c0 p) := by
  have hb2 : ∀ p, BoundedProc (eqV ρ γ c0 p) ↔ |lamF ρ γ| ≤ 1 ∨ p = c0 := fun p => by
    rw [show eqV ρ γ c0 p = fun t (_ : Unit) => lamF ρ γ ^ t * ((c0 - p) / ρ) from rfl,
      bounded_geom_iff]
    refine or_congr_right ⟨fun h => ?_, fun h => by rw [h]; simp⟩
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · linarith
    · exact absurd h hρ.ne'
  constructor
  · rintro ⟨hb1, hb2', heq⟩
    obtain ⟨hπ, hv⟩ := (leeper_pf_char hρ.ne' z.1 z.2).mp heq
    refine ⟨z.1 0 (), ⟨?_, ?_⟩, Prod.ext hπ hv⟩
    · rw [hπ] at hb1
      exact (bounded_geom_iff φ _).mp hb1
    · rw [hv] at hb2'
      exact (hb2 _).mp hb2'
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    refine ⟨(bounded_geom_iff φ p).mpr h1, (hb2 p).mpr h2, ?_⟩
    rw [leeper_pf_char hρ.ne']
    refine ⟨?_, ?_⟩ <;> simp [eqPi]

/-- Cochrane (2023), p. 523: the equilibrium map `p ↦ (φᵗp, λᵗ(c₀ − p)/ρ)` is injective. -/
theorem eqMap_injective (ρ φ γ c0 : ℝ) :
    Function.Injective fun p : ℝ => (eqPi φ p, eqV ρ γ c0 p) := by
  intro p p' h
  have := congrFun (congrFun (congrArg Prod.fst h) 0) ()
  simpa [eqPi] using this

/-- Cochrane (2023), p. 523: **the determinacy map.** For `ρ > 0` and `c₀ ≠ 0` there is exactly
one bounded equilibrium iff the regime parameters are active-money/passive-fiscal or
active-fiscal/passive-money. -/
theorem existsUnique_iff {ρ φ γ c0 : ℝ} (hρ : 0 < ρ) (hc0 : c0 ≠ 0) :
    (∃! z, z ∈ EqSet ρ φ γ c0) ↔ AM ρ φ γ ∨ AF ρ φ γ := by
  have hp : (∃! z, z ∈ EqSet ρ φ γ c0) ↔ ∃! p, Adm ρ φ γ c0 p := by
    constructor
    · rintro ⟨z, hz, hu⟩
      obtain ⟨p, hp, rfl⟩ := (mem_eqSet_iff hρ z).mp hz
      refine ⟨p, hp, fun p' hp' => eqMap_injective ρ φ γ c0 ?_⟩
      exact hu _ ((mem_eqSet_iff hρ _).mpr ⟨p', hp', rfl⟩)
    · rintro ⟨p, hp, hu⟩
      refine ⟨(eqPi φ p, eqV ρ γ c0 p), (mem_eqSet_iff hρ _).mpr ⟨p, hp, rfl⟩, fun z hz => ?_⟩
      obtain ⟨p', hp', rfl⟩ := (mem_eqSet_iff hρ z).mp hz
      rw [hu p' hp']
  rw [hp]
  unfold AM AF Adm
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, hu⟩
    by_cases hφ : |φ| ≤ 1 <;> by_cases hlam : |lamF ρ γ| ≤ 1
    · exfalso
      have a := hu (p + 1) ⟨Or.inl hφ, Or.inl hlam⟩
      linarith
    · exact Or.inr ⟨hφ, lt_of_not_ge hlam⟩
    · exact Or.inl ⟨lt_of_not_ge hφ, hlam⟩
    · exfalso
      have a := h1.resolve_left hφ
      have b := h2.resolve_left hlam
      exact hc0 (b ▸ a)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨0, ⟨Or.inr rfl, Or.inl h2⟩, fun p hp => ?_⟩
      exact hp.1.resolve_left (not_le.mpr h1)
    · refine ⟨c0, ⟨Or.inl h1, Or.inr rfl⟩, fun p hp => ?_⟩
      exact hp.2.resolve_left (not_le.mpr h2)

/-- Cochrane (2023), p. 523: with both eigenvalues outside the unit circle (both policies
active) there is no bounded equilibrium (`c₀ ≠ 0`), and conversely. -/
theorem eqSet_empty_iff {ρ φ γ c0 : ℝ} (hρ : 0 < ρ) (hc0 : c0 ≠ 0) :
    EqSet ρ φ γ c0 = ∅ ↔ 1 < |φ| ∧ 1 < |lamF ρ γ| := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h
    by_contra hcon
    rw [not_and_or, not_lt, not_lt] at hcon
    rcases hcon with hφ | hlam
    · exact h _ ((mem_eqSet_iff hρ _).mpr ⟨c0, ⟨Or.inl hφ, Or.inr rfl⟩, rfl⟩)
    · exact h _ ((mem_eqSet_iff hρ _).mpr ⟨0, ⟨Or.inr rfl, Or.inl hlam⟩, rfl⟩)
  · rintro ⟨hφ, hlam⟩ z hz
    obtain ⟨p, ⟨h1, h2⟩, -⟩ := (mem_eqSet_iff hρ z).mp hz
    have a := h1.resolve_left (not_le.mpr hφ)
    have b := h2.resolve_left (not_le.mpr hlam)
    exact hc0 (b ▸ a)

/-- Cochrane (2023), p. 523: with both eigenvalues inside or on the unit circle (both policies
passive) the bounded equilibria form an uncountable family. -/
theorem eqSet_uncountable {ρ φ γ c0 : ℝ} (hρ : 0 < ρ) (hφ : |φ| ≤ 1) (hlam : |lamF ρ γ| ≤ 1) :
    ¬ (EqSet ρ φ γ c0).Countable := by
  intro hc
  have hsub : Set.range (fun p : ℝ => (eqPi φ p, eqV ρ γ c0 p)) ⊆ EqSet ρ φ γ c0 := by
    rintro _ ⟨p, rfl⟩
    exact (mem_eqSet_iff hρ _).mpr ⟨p, ⟨Or.inl hφ, Or.inl hlam⟩, rfl⟩
  have h2 := (hc.mono hsub).preimage (eqMap_injective ρ φ γ c0)
  rw [Set.preimage_range] at h2
  exact Cardinal.not_countable_real h2

/-- Cochrane (2023), p. 523: in the active-money regime the unique equilibrium has `π₀ = 0`:
inflation does not respond to the fiscal state `c₀`. -/
theorem am_pi0 {ρ φ γ c0 : ℝ} (hρ : 0 < ρ) (h : AM ρ φ γ) {z} (hz : z ∈ EqSet ρ φ γ c0) :
    z.1 0 () = 0 := by
  obtain ⟨p, ⟨h1, -⟩, rfl⟩ := (mem_eqSet_iff hρ z).mp hz
  simp [eqPi, h1.resolve_left (not_le.mpr h.1)]

/-- Cochrane (2023), p. 523: in the active-fiscal regime the unique equilibrium has `π₀ = c₀`:
inflation absorbs the fiscal state one for one. -/
theorem af_pi0 {ρ φ γ c0 : ℝ} (hρ : 0 < ρ) (h : AF ρ φ γ) {z} (hz : z ∈ EqSet ρ φ γ c0) :
    z.1 0 () = c0 := by
  obtain ⟨p, ⟨-, h2⟩, rfl⟩ := (mem_eqSet_iff hρ z).mp hz
  simp [eqPi, h2.resolve_left (not_le.mpr h.2)]

/-! ## Paths of regime parameters (p. 523) -/

/-- Cochrane (2023), p. 523: at parameters where the two eigenvalues have equal modulus there is
no unique bounded equilibrium (`ρ > 0`, `c₀ ≠ 0`). -/
theorem not_unique_of_eq_modulus {ρ φ γ c0 : ℝ} (hρ : 0 < ρ) (hc0 : c0 ≠ 0)
    (h : |φ| = |lamF ρ γ|) : ¬ ∃! z, z ∈ EqSet ρ φ γ c0 := by
  rw [existsUnique_iff hρ hc0]
  rintro (⟨a, b⟩ | ⟨a, b⟩) <;> linarith

/-- Cochrane (2023), p. 523, **"requires a discrete shift … to move eigenvalues from stable to
unstable"**: along every continuous path `s ↦ (φ(s), γ(s))`, `s ∈ [0, 1]`, from the
active-money regime to the active-fiscal regime, the monetary eigenvalue reaches the unit circle
(at some `s > 0`), the fiscal eigenvalue reaches it (at some `s < 1`), and at some intermediate
parameter the two eigenvalues have equal modulus, so that (for `ρ > 0`, `c₀ ≠ 0`) the model has
no unique bounded equilibrium there. -/
theorem path_crosses {ρ c0 : ℝ} (hρ : 0 < ρ) (hc0 : c0 ≠ 0) {φ γ : ℝ → ℝ}
    (hφc : ContinuousOn φ (Set.Icc 0 1)) (hγc : ContinuousOn γ (Set.Icc 0 1))
    (h0 : AM ρ (φ 0) (γ 0)) (h1 : AF ρ (φ 1) (γ 1)) :
    (∃ s ∈ Set.Ioc (0 : ℝ) 1, |φ s| = 1) ∧ (∃ s ∈ Set.Ico (0 : ℝ) 1, |lamF ρ (γ s)| = 1) ∧
      ∃ s ∈ Set.Ioo (0 : ℝ) 1, |φ s| = |lamF ρ (γ s)| ∧
        ¬ ∃! z, z ∈ EqSet ρ (φ s) (γ s) c0 := by
  have hlamc : ContinuousOn (fun s => |lamF ρ (γ s)|) (Set.Icc 0 1) := by
    unfold lamF
    exact ((continuousOn_const.sub hγc).div_const ρ).abs
  have hφa : ContinuousOn (fun s => |φ s|) (Set.Icc 0 1) := hφc.abs
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, hs, hs1⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hφa ⟨h1.1, h0.1.le⟩
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, hs.2⟩, hs1⟩
    rintro rfl
    exact absurd hs1 (ne_of_gt h0.1)
  · obtain ⟨s, hs, hs1⟩ := intermediate_value_Icc (zero_le_one' ℝ) hlamc ⟨h0.2, h1.2.le⟩
    refine ⟨s, ⟨hs.1, lt_of_le_of_ne hs.2 ?_⟩, hs1⟩
    rintro rfl
    exact absurd hs1 (ne_of_gt h1.2)
  · have hF : ContinuousOn (fun s => |φ s| - |lamF ρ (γ s)|) (Set.Icc 0 1) := hφa.sub hlamc
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo' (zero_le_one' ℝ) hF
      (show (0 : ℝ) ∈ Set.Ioo (|φ 1| - |lamF ρ (γ 1)|) (|φ 0| - |lamF ρ (γ 0)|) from
        ⟨by linarith [h1.1, h1.2], by linarith [h0.1, h0.2]⟩)
    have he : |φ s| = |lamF ρ (γ s)| := by linarith
    exact ⟨s, hs, he, not_unique_of_eq_modulus hρ hc0 he⟩

/-- Cochrane (2023), p. 523: the active-money and active-fiscal regions cannot be joined by a
continuous path of regime parameters along which the equilibrium stays unique. -/
theorem no_determinate_path {ρ c0 : ℝ} (hρ : 0 < ρ) (hc0 : c0 ≠ 0) {φ γ : ℝ → ℝ}
    (hφc : ContinuousOn φ (Set.Icc 0 1)) (hγc : ContinuousOn γ (Set.Icc 0 1))
    (h0 : AM ρ (φ 0) (γ 0)) (h1 : AF ρ (φ 1) (γ 1)) :
    ¬ ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃! z, z ∈ EqSet ρ (φ s) (γ s) c0 := by
  intro h
  obtain ⟨-, -, s, hs, -, hn⟩ := path_crosses hρ hc0 hφc hγc h0 h1
  exact hn (h s ⟨hs.1.le, hs.2.le⟩)

/-- Cochrane (2023), p. 523 ("momentous or discontinuous consequences"): the equilibrium
response of initial inflation to the fiscal state is `π₀ = r·c₀` with `r = 0` throughout the
active-money regime and `r = 1` throughout the active-fiscal regime; along any continuous path
between them it jumps, passing through a parameter with no unique equilibrium
(`path_crosses`). -/
theorem pi0_response_jump {ρ c0 : ℝ} (hρ : 0 < ρ) (hc0 : c0 ≠ 0) {φ γ : ℝ → ℝ}
    (h0 : AM ρ (φ 0) (γ 0)) (h1 : AF ρ (φ 1) (γ 1)) :
    (∃! z, z ∈ EqSet ρ (φ 0) (γ 0) c0) ∧ (∃! z, z ∈ EqSet ρ (φ 1) (γ 1) c0) ∧
      (∀ z ∈ EqSet ρ (φ 0) (γ 0) c0, z.1 0 () = 0 * c0) ∧
      ∀ z ∈ EqSet ρ (φ 1) (γ 1) c0, z.1 0 () = 1 * c0 :=
  ⟨(existsUnique_iff hρ hc0).mpr (Or.inl h0), (existsUnique_iff hρ hc0).mpr (Or.inr h1),
    fun z hz => by rw [zero_mul]; exact am_pi0 hρ h0 hz,
    fun z hz => by rw [one_mul]; exact af_pi0 hρ h1 hz⟩

/-! ## The contrast: on-equilibrium correlations (p. 523) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 523 (with (5.10)–(5.12), p. 116, frictionless): the fiscal-theory
equilibrium with an on-equilibrium interest-rate correlation `i_t = θπ_t + w_t`: the Fisher
equation `E_tπ_{t+1} = i_t`, unexpected inflation equal to minus the fiscal news,
`π_{t+1} − E_tπ_{t+1} = −ε_{t+1}`, and `π₀ = −ε₀` from the steady state. -/
def FTPLEq (θ : ℝ) (w ε π : ℕ → Ω → ℝ) : Prop :=
  π 0 = -ε 0 ∧ ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + w t ∧
    π (t + 1) - 𝔼.E t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), p. 523: the equilibrium path `π_{t+1} = θπ_t + w_t − ε_{t+1}`,
`π₀ = −ε₀`. -/
def ftplPi (θ : ℝ) (w ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => -ε 0
  | t + 1 => θ • ftplPi θ w ε t + w t - ε (t + 1)

/-- Cochrane (2023), p. 523 ("a shift of `θ` … has no such momentous or discontinuous
consequences"): for EVERY `θ ∈ ℝ` (including `|θ| = 1` and `|θ| > 1`), adapted `w`, `ε` and news
`E_tε_{t+1} = 0`, there is exactly one adapted equilibrium, `ftplPi`. -/
theorem ftpl_existsUnique (θ : ℝ) {w ε : ℕ → Ω → ℝ} (hw : 𝔼.Adapted w) (hε : 𝔼.Adapted ε)
    (hn : ∀ t, 𝔼.E t (ε (t + 1)) = 0) :
    ∃! π : ℕ → Ω → ℝ, 𝔼.Adapted π ∧ FTPLEq 𝔼 θ w ε π := by
  have hkn : ∀ {x : ℕ → Ω → ℝ}, 𝔼.Adapted x → ∀ t, 𝔼.E (t + 1) (x t) = x t := by
    intro x hx t
    rw [← hx t, 𝔼.known (Nat.le_succ t), hx t]
  have hEt : ∀ t, 𝔼.E t (ftplPi θ w ε (t + 1)) =
      θ • 𝔼.E t (ftplPi θ w ε t) + w t := by
    intro t
    simp only [ftplPi, map_sub, map_add, map_smul, hw t, hn t, sub_zero]
  have had : 𝔼.Adapted (ftplPi θ w ε) := by
    intro t
    induction t with
    | zero => simp only [ftplPi, map_neg, hε 0]
    | succ t ih =>
      have h1 : 𝔼.E (t + 1) (ftplPi θ w ε t) = ftplPi θ w ε t := by
        rw [← ih, 𝔼.known (Nat.le_succ t)]
      simp only [ftplPi, map_sub, map_add, map_smul, h1, hkn hw t, hε (t + 1)]
  refine ⟨ftplPi θ w ε, ⟨had, rfl, fun t => ⟨by rw [hEt, had t], ?_⟩⟩, ?_⟩
  · rw [hEt, had t]
    simp only [ftplPi]
    abel
  · rintro π ⟨-, h0, h⟩
    funext t
    induction t with
    | zero => exact h0
    | succ t ih =>
      have a := (h t).1
      have b := (h t).2
      rw [a, ih] at b
      simp only [ftplPi]
      linear_combination b

/-- Cochrane (2023), p. 523: the equilibrium is a continuous (polynomial) function of `θ` at
every date and state; nothing happens at `|θ| = 1`. -/
theorem ftpl_continuous_theta (w ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Continuous fun θ => ftplPi θ w ε t ω := by
  induction t with
  | zero => exact continuous_const
  | succ t ih =>
    simp only [ftplPi, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact ((continuous_id.mul ih).add continuous_const).sub continuous_const

end Cochrane.ZeroBound.TidyR6RegimeEigen
