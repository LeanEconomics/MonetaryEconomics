/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR5UnitRoot
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact

/-!
# Region (d) at `|φ| = 1` on every countable state space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.7, pp. 508–509, and
Chapter 23, eqs. (23.1)–(23.2), p. 512.

`TidyR5UnitRoot` proves, in any `ExpectationSystem`, that a bounded solution of
`E_t π_{t+1} = φπ_t + u_{i,t}` (`φ² = 1`) forces the conditional sums
`∑_{j<T} φʲ E_t u_{t+j}` to be bounded, and the converse when information stops arriving. Here the
converse is proved whenever each forecast `E_t(·)(ω)` depends on finitely many states
(`FinSupp`), by Tychonoff's theorem: the pinned solutions give a decreasing sequence of nonempty
closed subsets of the compact cube `[−C, C]^{ℕ × Ω}`.

Every expectation system on a countable state space is finitely supported
(`finSupp_of_countable`, from `pos_functional_finite_support`, restated from the Woodford
Chapter 2 project PriceLevelDetermination, module SGUStochasticMeasure). Hence:

* `exists_iff_of_finSupp`, `exists_iff_countable`: on every countable state space, with any
  expectation system, a bounded adapted solution exists **iff** the conditional sums are bounded;
  `exists_iff_countable_phi_one` (`|E_t ∑_{j<T} u_{t+j}| ≤ C`) and
  `exists_iff_countable_phi_neg_one` (`|E_t ∑_{j<T} (−1)ʲ u_{t+j}| ≤ C`).
* `leeper_unit_iff_countable`: on a countable state space, at `φ² = 1` and `0 < γ < 2`, the Leeper
  model has admissible equilibria (then uncountably many, the region (d) sunspot families) iff the
  conditional sums of `u_i` are bounded.

On an uncountable state space a core expectation need not be finitely supported (the Woodford
Chapter 2 project shows this is independent of Lean's foundations); the measure-theoretic
characterisation `TidyR5UnitRootMeasure.exists_iff_condBddM` covers every probability space.
-/

namespace Cochrane.ObservationalEquivalence.TidyR5UnitRootCompact

open Filter Topology
open Cochrane.ObservationalEquivalence.TidyR5UnitRoot
open Cochrane.ObservationalEquivalence.StarredModel Cochrane.ObservationalEquivalence.LeeperRegions

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §22.7, p. 508: every forecast `E_t(·)(ω)` depends only on the values of its
argument on a finite set of states. -/
def FinSupp : Prop :=
  ∀ t (ω : Ω), ∃ F : Finset Ω, ∀ f : Ω → ℝ, (∀ ω' ∈ F, f ω' = 0) → 𝔼.E t f ω = 0

/-- Cochrane (2023), §22.7, p. 508 (tool): a finitely supported forecast is a continuous function
of the random variable in the product topology. -/
theorem continuous_E_apply (h : FinSupp 𝔼) (t : ℕ) (ω : Ω) :
    Continuous fun f : Ω → ℝ => 𝔼.E t f ω := by
  classical
  obtain ⟨F, hF⟩ := h t ω
  set δ : Ω → Ω → ℝ := fun ω' x => if x = ω' then 1 else 0 with hδ
  have key : ∀ f : Ω → ℝ, 𝔼.E t f ω = ∑ ω' ∈ F, f ω' * 𝔼.E t (δ ω') ω := by
    intro f
    have hz := hF (f - ∑ ω' ∈ F, f ω' • δ ω') fun x hx => by
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hδ, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, hx, ↓reduceIte, sub_self]
    rw [map_sub, map_sum, Pi.sub_apply, sub_eq_zero, Finset.sum_apply] at hz
    rw [hz]
    exact Finset.sum_congr rfl fun ω' _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [show (fun f : Ω → ℝ => 𝔼.E t f ω) = fun f => ∑ ω' ∈ F, f ω' * 𝔼.E t (δ ω') ω from
    funext key]
  exact continuous_finsetSum _ fun ω' _ => (continuous_apply ω').mul continuous_const

/-- Cochrane (2023), §22.7, p. 508 (tool): the bounded adapted paths with `|π_t| ≤ C` that solve
the monetary equation at the dates `t < n`. -/
def Kc (φ C : ℝ) (u : ℕ → Ω → ℝ) (n : ℕ) : Set (ℕ → Ω → ℝ) :=
  {π | (∀ t ω, |π t ω| ≤ C) ∧ (∀ t, 𝔼.E t (π t) = π t) ∧
    ∀ t, t < n → 𝔼.E t (π (t + 1)) = φ • π t + u t}

/-- Cochrane (2023), §22.7, p. 508 (tool): with finitely supported forecasts the sets `Kc` are
closed in the product topology. -/
theorem isClosed_kc (h : FinSupp 𝔼) (φ C : ℝ) (u : ℕ → Ω → ℝ) (n : ℕ) :
    IsClosed (Kc 𝔼 φ C u n) := by
  have hc : ∀ s t (ω : Ω), Continuous fun π : ℕ → Ω → ℝ => 𝔼.E t (π s) ω := fun s t ω =>
    (continuous_E_apply 𝔼 h t ω).comp (continuous_apply s)
  have hp : ∀ t (ω : Ω), Continuous fun π : ℕ → Ω → ℝ => π t ω := fun t ω =>
    (continuous_apply ω).comp (continuous_apply t)
  have e : Kc 𝔼 φ C u n = (⋂ t, ⋂ ω, {π : ℕ → Ω → ℝ | |π t ω| ≤ C}) ∩
      ((⋂ t, ⋂ ω, {π : ℕ → Ω → ℝ | 𝔼.E t (π t) ω = π t ω}) ∩
      ⋂ t, ⋂ (_ : t < n), ⋂ ω, {π : ℕ → Ω → ℝ | 𝔼.E t (π (t + 1)) ω = φ * π t ω + u t ω}) := by
    ext π
    simp only [Kc, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, funext_iff,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact (isClosed_iInter fun t => isClosed_iInter fun ω =>
    isClosed_le (continuous_abs.comp (hp t ω)) continuous_const).inter
    ((isClosed_iInter fun t => isClosed_iInter fun ω => isClosed_eq (hc t t ω) (hp t ω)).inter
      (isClosed_iInter fun t => isClosed_iInter fun _ => isClosed_iInter fun ω =>
        isClosed_eq (hc (t + 1) t ω) ((continuous_const.mul (hp t ω)).add continuous_const)))

/-- Cochrane (2023), §22.7, p. 508 (**sufficiency** with finitely supported forecasts): at
`φ² = 1`, bounded conditional sums give a bounded adapted solution. The pinned solutions
`π^{(n)}` (frozen at 0 after `n`) lie in the decreasing closed sets `Kc n` of the compact cube
`[−C, C]^{ℕ × Ω}`, which therefore have a common point. -/
theorem sol_of_condBdd_finSupp {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    (h : FinSupp 𝔼) (hC : CondBdd 𝔼 φ u) : HasBddSol 𝔼 φ u := by
  obtain ⟨C, hC⟩ := hC
  have hne : ∀ n, (Kc 𝔼 φ C u n).Nonempty := by
    intro n
    refine ⟨fun t => if t ≤ n then finSol 𝔼 φ u n t else 0, fun t ω => ?_, fun t => ?_,
      fun t ht => ?_⟩
    · by_cases htn : t ≤ n
      · simp only [htn, ↓reduceIte]
        obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_le htn
        rw [finSol_eq_condSum 𝔼 hφ hua, Pi.neg_apply, abs_neg, Pi.smul_apply, smul_eq_mul,
          abs_mul, abs_eq_one hφ, one_mul]
        exact hC t T ω
      · simp only [htn, ↓reduceIte, Pi.zero_apply, abs_zero]
        exact (abs_nonneg _).trans (hC 0 0 ω)
    · by_cases htn : t ≤ n
      · simp only [htn, ↓reduceIte]; exact finSol_adapted 𝔼 hua n t
      · simp only [htn, ↓reduceIte]; exact map_zero _
    · simp only [show t + 1 ≤ n by omega, show t ≤ n by omega, ↓reduceIte]
      exact finSol_solves 𝔼 hua n t
  have hcube : IsCompact (Set.univ.pi fun _ : ℕ => Set.univ.pi fun _ : Ω => Set.Icc (-C) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have h0 : IsCompact (Kc 𝔼 φ C u 0) :=
    hcube.of_isClosed_subset (isClosed_kc 𝔼 h φ C u 0) fun π hπ t _ ω _ =>
      abs_le.1 (hπ.1 t ω)
  obtain ⟨π, hπ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (Kc 𝔼 φ C u) (fun n π hπ => ⟨hπ.1, hπ.2.1, fun t ht => hπ.2.2 t (by omega)⟩) hne h0
    (isClosed_kc 𝔼 h φ C u)
  rw [Set.mem_iInter] at hπ
  exact ⟨π, (hπ 0).2.1, ⟨C, (hπ 0).1⟩, fun t => (hπ (t + 1)).2.2 t (Nat.lt_succ_self t)⟩

/-- Cochrane (2023), §22.7, p. 508 (**the characterisation** with finitely supported forecasts):
at `φ² = 1` a bounded adapted solution exists iff the conditional sums are bounded. -/
theorem exists_iff_of_finSupp {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u)
    (h : FinSupp 𝔼) : HasBddSol 𝔼 φ u ↔ CondBdd 𝔼 φ u :=
  ⟨condBdd_of_sol 𝔼 hφ, sol_of_condBdd_finSupp 𝔼 hφ hua h⟩

/-! ### Countable state spaces -/

/-- Cochrane (2023), §22.7, p. 508 (tool; restated from the Woodford Chapter 2 project,
module SGUStochasticMeasure): a positive linear functional on all of
`ℝ^ℕ` depends on finitely many coordinates. -/
theorem pos_functional_finite_support (φ : (ℕ → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀ y, 0 ≤ y → 0 ≤ φ y) :
    ∃ N, ∀ y : ℕ → ℝ, (∀ n ≤ N, y n = 0) → φ y = 0 := by
  by_contra h
  push Not at h
  have hz : ∀ N, ∃ z : ℕ → ℝ, 0 ≤ z ∧ (∀ n ≤ N, z n = 0) ∧ 0 < φ z := by
    intro N
    obtain ⟨y, hy, hφ⟩ := h N
    set yp : ℕ → ℝ := fun n => max (y n) 0 with hyp
    set ym : ℕ → ℝ := fun n => max (-y n) 0 with hym
    have hsplit : y = yp - ym := by
      funext n
      simp only [hyp, hym, Pi.sub_apply]
      rcases le_total 0 (y n) with h0 | h0
      · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    have hp0 : 0 ≤ yp := fun n => le_max_right _ _
    have hm0 : 0 ≤ ym := fun n => le_max_right _ _
    have hpN : ∀ n ≤ N, yp n = 0 := fun n hn => by simp [hyp, hy n hn]
    have hmN : ∀ n ≤ N, ym n = 0 := fun n hn => by simp [hym, hy n hn]
    rw [hsplit, map_sub] at hφ
    rcases (hpos yp hp0).lt_or_eq with h1 | h1
    · exact ⟨yp, hp0, hpN, h1⟩
    · rcases (hpos ym hm0).lt_or_eq with h2 | h2
      · exact ⟨ym, hm0, hmN, h2⟩
      · exact absurd (by rw [← h1, ← h2, sub_self]) hφ
  choose z hz0 hzN hzpos using hz
  set c : ℕ → ℝ := fun N => ((N : ℝ) + 1) / φ (z N) with hc
  have hc0 : ∀ N, 0 ≤ c N := fun N => div_nonneg (by positivity) (hzpos N).le
  set Z : ℕ → ℝ := fun n => ∑ N ∈ Finset.range n, c N * z N n with hZ
  have hle : ∀ M, (∑ N ∈ Finset.range M, c N • z N) ≤ Z := by
    intro M n
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, hZ]
    calc ∑ N ∈ Finset.range M, c N * z N n ≤ ∑ N ∈ Finset.range (n + M), c N * z N n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
            (fun N _ _ => mul_nonneg (hc0 N) (hz0 N n))
      _ = ∑ N ∈ Finset.range n, c N * z N n := by
          rw [Finset.sum_range_add]
          have : ∑ k ∈ Finset.range M, c (n + k) * z (n + k) n = 0 :=
            Finset.sum_eq_zero fun k _ => by rw [hzN (n + k) n (by omega), mul_zero]
          rw [this, add_zero]
  have hbound : ∀ M : ℕ, (M : ℝ) ≤ φ Z := by
    intro M
    have h1 := hpos _ (sub_nonneg.mpr (hle M))
    rw [map_sub, map_sum, sub_nonneg] at h1
    have h2 : ∑ N ∈ Finset.range M, φ (c N • z N) = ∑ N ∈ Finset.range M, ((N : ℝ) + 1) := by
      refine Finset.sum_congr rfl fun N _ => ?_
      rw [map_smul, smul_eq_mul, hc, div_mul_cancel₀ _ (hzpos N).ne']
    rw [h2] at h1
    have h3 : (M : ℝ) ≤ ∑ N ∈ Finset.range M, ((N : ℝ) + 1) := by
      calc (M : ℝ) = ∑ _N ∈ Finset.range M, (1 : ℝ) := by simp
        _ ≤ ∑ N ∈ Finset.range M, ((N : ℝ) + 1) :=
            Finset.sum_le_sum fun N _ => by
              have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
              linarith
    linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (φ Z)
  linarith [hbound M]

/-- Cochrane (2023), §22.7, p. 508: on a countable state space every expectation system is
finitely supported (each `E_t(·)(ω)` is a positive linear functional on all of `ℝ^Ω`). -/
theorem finSupp_of_countable [Countable Ω] : FinSupp 𝔼 := by
  intro t ω
  obtain ⟨e, he⟩ := Countable.exists_injective_nat Ω
  set L : (ℕ → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj ω).comp ((𝔼.E t).comp (LinearMap.funLeft ℝ ℝ e))
    with hL
  have hpos : ∀ y, 0 ≤ y → 0 ≤ L y := fun y hy => by
    have h := 𝔼.mono t (show (0 : Ω → ℝ) ≤ y ∘ e from fun x => hy (e x)) ω
    rw [map_zero] at h
    exact h
  obtain ⟨N, hN⟩ := pos_functional_finite_support L hpos
  have hfin : (e ⁻¹' Set.Iic N).Finite := (Set.finite_Iic N).preimage he.injOn
  refine ⟨hfin.toFinset, fun f hf => ?_⟩
  have hy : (Function.extend e f 0) ∘ e = f := funext fun x => he.extend_apply f 0 x
  have h0 : ∀ n ≤ N, Function.extend e f 0 n = 0 := by
    intro n hn
    by_cases hr : ∃ a, e a = n
    · obtain ⟨a, rfl⟩ := hr
      rw [he.extend_apply]
      exact hf a (hfin.mem_toFinset.2 hn)
    · rw [Function.extend_apply' _ _ _ hr, Pi.zero_apply]
  have := hN _ h0
  simp only [hL, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval] at this
  have e2 : LinearMap.funLeft ℝ ℝ e (Function.extend e f 0) = f := hy
  rw [e2] at this
  exact this

/-- Cochrane (2023), §22.7, p. 508 (**the characterisation on every countable state space**): for
every expectation system on a countable state space, at `φ² = 1` the monetary equation has a
bounded adapted solution iff the conditional sums `∑_{j<T} φʲ E_t u_{t+j}` are bounded. -/
theorem exists_iff_countable [Countable Ω] {φ : ℝ} (hφ : φ ^ 2 = 1) {u : ℕ → Ω → ℝ}
    (hua : 𝔼.Adapted u) : HasBddSol 𝔼 φ u ↔ CondBdd 𝔼 φ u :=
  exists_iff_of_finSupp 𝔼 hφ hua (finSupp_of_countable 𝔼)

/-- Cochrane (2023), §22.7, p. 508, at `φ = 1` on a countable state space: a bounded solution of
`E_t π_{t+1} = π_t + u_{i,t}` exists iff `|E_t ∑_{j<T} u_{t+j}| ≤ C`. -/
theorem exists_iff_countable_phi_one [Countable Ω] {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) :
    HasBddSol 𝔼 1 u ↔ ∃ C, ∀ t T ω, |𝔼.E t (∑ j ∈ Finset.range T, u (t + j)) ω| ≤ C := by
  rw [exists_iff_countable 𝔼 (by norm_num) hua, CondBdd]
  simp only [condSum, one_pow, one_smul, map_sum]

/-- Cochrane (2023), §22.7, p. 508, at `φ = −1` on a countable state space: a bounded solution
of `E_t π_{t+1} = −π_t + u_{i,t}` exists iff `|E_t ∑_{j<T} (−1)ʲ u_{t+j}| ≤ C`. -/
theorem exists_iff_countable_phi_neg_one [Countable Ω] {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) :
    HasBddSol 𝔼 (-1) u ↔
      ∃ C, ∀ t T ω, |𝔼.E t (∑ j ∈ Finset.range T, (-1 : ℝ) ^ j • u (t + j)) ω| ≤ C := by
  rw [exists_iff_countable 𝔼 (by norm_num) hua, CondBdd]
  simp only [condSum, map_sum, map_smul]

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) at `φ² = 1` on a countable state space
(`0 < γ < 2`): the Leeper model has an admissible equilibrium — and then uncountably many,
`LeeperRegions.region_d_of_solution` — iff the conditional sums `∑_{j<T} φʲ E_t u_{i,t+j}` are
bounded. -/
theorem leeper_unit_iff_countable [Countable Ω] [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hφ : φ ^ 2 = 1) (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) :
    ((∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) ↔ CondBdd 𝔼 φ ui) ∧
      (CondBdd 𝔼 φ ui →
        ¬ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x}.Countable) := by
  have h := leeper_unit_dichotomy 𝔼 hρ0 hρ1 hφ hγ hus husa hK (ui := ui)
  have e := exists_iff_countable 𝔼 hφ huia
  exact ⟨h.1.trans e, fun hc => h.2 (h.1.2 (e.2 hc))⟩

end Cochrane.ObservationalEquivalence.TidyR5UnitRootCompact
