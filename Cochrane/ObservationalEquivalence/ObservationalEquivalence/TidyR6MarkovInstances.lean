/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.TidyR6MarkovPullOut
import ObservationalEquivalence.ExpectationTools

/-!
# Models of the abstract `N`-regime theorems, and what the non-degenerate case forces

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Davig and
Leeper (2006, 2007); "the Markov assumption, with exactly two (or even N) states", p. 523).

## Which models exist

* **Degenerate chains, known regime** (`detT`, `detRegime`): with full information
  (`ExpectationTools.fullInfo`, `E_t = id`) and a deterministic transition `S_{t+1} = σ(S_t)`, the
  regime satisfies the tree hypothesis `TidyR6MarkovAbstractN.HistMarkovN`, is known at each date
  and the system has the pull-out property. For `σ = id`, `genCondition_id_iff` computes the
  condition (`|φ_i| > 1` for every `i`), and the abstract theorems become concrete
  (`id_hist_determinate_iff`, `id_pullOut_determinate_iff`, `id_hist_dichotomy`,
  `id_markov_dichotomy`, `eg_id_determinate`, `eg_id_indeterminate`).
* **Non-degenerate chains, unknown regime**: `TidyR6MarkovAbstractN.avgRegime` (`p_ij = ½`) is a
  Markov regime of a two-state system; `avg_naive_nonzero` instantiates
  `TidyR6MarkovAbstractN.absN_homog_nonzero_of_not_naive` there.
* **Non-degenerate chains, known regime: no constructible model.** Under the tree hypothesis
  (`histMarkov_no_atoms`), or with pull-out and a known regime (`pullOut_no_atoms`), every
  date-`0` forecast gives weight zero to every single state, `E_0 1{z}(ω) = 0`; with
  `TidyR6MarkovNoGo.not_pointwiseLinear` and `TidyR6MarkovNoGo.countable_no_regime` there is no
  pointwise-linear and no countable model. The substantive non-degenerate versions are therefore
  `MarkovRegimesGeneral.determinate_iff` (regime tree) and
  `MarkovRegimesGeneralMeasure.meas_determinate_iff` (probability space).
-/

namespace Cochrane.ObservationalEquivalence.TidyR6MarkovInstances

open Filter Topology
open Cochrane.ObservationalEquivalence.MarkovRegimesGeneral
open Cochrane.ObservationalEquivalence.TidyR6MarkovAbstractN
open Cochrane.ObservationalEquivalence.TidyR6MarkovNoGo
open Cochrane.ObservationalEquivalence.TidyR6MarkovPullOut
open Cochrane.ObservationalEquivalence.ExpectationTools
open scoped Matrix ENNReal NNReal

variable {Ω : Type*} {N : ℕ}

/-! ### Deterministic chains -/

/-- Cochrane (2023), p. 523: the degenerate transition matrix of a deterministic regime map `σ`,
`P_{ij} = 1{j = σ(i)}`. -/
def detT (σ : Fin N → Fin N) : TransitionN N where
  P i j := if j = σ i then 1 else 0
  nonneg i j := by
    split_ifs <;> norm_num
  rowSum i := by simp

/-- Cochrane (2023), pp. 522–523: under full information on `Fin N`, the regime
`S_t(ω) = σ^t(ω)` satisfies the tree hypothesis for `detT σ`. -/
def detRegime (σ : Fin N → Fin N) : HistMarkovN (fullInfo (Fin N)) (detT σ) where
  S t ω := σ^[t] ω
  hist t G := by
    funext ω
    change G (σ^[t + 1] ω, _) = ∑ j, (if j = σ (σ^[t] ω) then (1 : ℝ) else 0) * G (j, _)
    rw [Function.iterate_succ_apply']
    simp

/-- Cochrane (2023), p. 522: in `detRegime σ` every regime is possible at date `0`. -/
theorem detRegime_initial (σ : Fin N → Fin N) (i : Fin N) : ∃ ω, (detRegime σ).S 0 ω = i :=
  ⟨i, rfl⟩

/-- Cochrane (2023), p. 522: in `detRegime σ` the regime is known at each date. -/
theorem detRegime_adapted (σ : Fin N → Fin N) :
    RegimeAdapted (fullInfo (Fin N)) (detRegime σ).S :=
  fun _ _ => rfl

/-- Cochrane (2023), p. 522: full information has the pull-out property.
The full-information analogue of `perfectForesight_pullOut`. -/
theorem fullInfo_pullOut : (fullInfo Ω).PullOut := fun _ _ _ _ => rfl

/-- Cochrane (2023), p. 523: for `σ = id`, `|Φ|⁻¹P` is the diagonal matrix of `1/|φ_i|`. -/
theorem absM_detT_id (φ : Fin N → ℝ) :
    absM (detT (N := N) id) φ = Matrix.diagonal fun i => 1 / |φ i| := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [absM, detT]
  · simp [absM, detT, h, Ne.symm h]

/-- Cochrane (2023), pp. 522–523: for the absorbing chain `P = I` the condition is that every
regime is active, `|φ_i| > 1`. -/
theorem genCondition_id_iff (φ : Fin N → ℝ) :
    GenCondition (detT (N := N) id) φ ↔ ∀ i, 1 < |φ i| := by
  have hmap : (Matrix.diagonal fun i => 1 / |φ i|).map Complex.ofReal =
      Matrix.diagonal fun i => ((1 / |φ i| : ℝ) : ℂ) := Matrix.diagonal_map (by simp)
  constructor
  · rintro ⟨h0, hs⟩ i
    by_contra hle
    push Not at hle
    have hpos : 0 < |φ i| := abs_pos.2 (h0 i)
    have hv : (Pi.single i (1 : ℂ) : Fin N → ℂ) ≠ 0 := by
      intro h
      have := congrFun h i
      simp at this
    have hAv : ((absM (detT (N := N) id) φ).map Complex.ofReal) *ᵥ Pi.single i (1 : ℂ) =
        ((1 / |φ i| : ℝ) : ℂ) • Pi.single i (1 : ℂ) := by
      rw [absM_detT_id, hmap]
      funext k
      rw [Matrix.mulVec_diagonal]
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    have h1 := norm_le_spectralRadius hv hAv
    have hge : (1 : ℝ) ≤ ‖((1 / |φ i| : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [le_div_iff₀ hpos, one_mul]
      exact hle
    have hge' : (1 : ℝ≥0∞) ≤ ‖((1 / |φ i| : ℝ) : ℂ)‖₊ := by
      rw [ENNReal.one_le_coe_iff, ← NNReal.coe_le_coe, coe_nnnorm]
      exact hge
    exact absurd (lt_of_le_of_lt (hge'.trans h1) hs) (lt_irrefl _)
  · intro h
    have h0 : ∀ i, φ i ≠ 0 := fun i hi => by
      have := h i
      rw [hi, abs_zero] at this
      linarith
    refine ⟨h0, ?_⟩
    set c : ℝ≥0 := Finset.univ.sup fun i => (1 / |φ i|).toNNReal with hc
    have hc1 : c < 1 := by
      rw [hc, Finset.sup_lt_iff (by simp)]
      intro i _
      rw [Real.toNNReal_lt_one, div_lt_one (by linarith [h i])]
      exact h i
    refine lt_of_le_of_lt (specRad_le_of_eigen fun z v hv hAv => ?_) (by exact_mod_cast hc1)
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hv (funext hno)
    have hrow := congrFun hAv k
    rw [absM_detT_id, hmap, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hrow
    have hz : z = ((1 / |φ k| : ℝ) : ℂ) := (mul_right_cancel₀ hk hrow).symm
    rw [← NNReal.coe_le_coe, coe_nnnorm, hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by have := h k; positivity)]
    have hle : (1 / |φ k|).toNNReal ≤ c :=
      Finset.le_sup (f := fun i => (1 / |φ i|).toNNReal) (Finset.mem_univ k)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)] at hle
    exact hle

/-- Cochrane (2023), pp. 522–523 (**`hist_determinate_iff` instantiated**): for the absorbing
chain under full information, there is exactly one bounded equilibrium for every bounded
history-driven disturbance iff every regime is active, `|φ_i| > 1`. -/
theorem id_hist_determinate_iff (φ : Fin N → ℝ) :
    HDeterminate (detRegime (N := N) id) φ ↔ ∀ i, 1 < |φ i| :=
  (hist_determinate_iff _ φ (detRegime_initial id)).trans (genCondition_id_iff φ)

/-- Cochrane (2023), pp. 522–523 (**`pullOut_determinate_iff` instantiated**): for the absorbing
chain under full information, there is exactly one bounded equilibrium for every bounded
disturbance iff every regime is active, `|φ_i| > 1`. -/
theorem id_pullOut_determinate_iff (φ : Fin N → ℝ) :
    PDeterminate (fullInfo (Fin N)) (detRegime (N := N) id).S φ ↔ ∀ i, 1 < |φ i| :=
  (pullOut_determinate_iff (detRegime id).toMarkov (detRegime_adapted id) fullInfo_pullOut φ
    (detRegime_initial id)).trans (genCondition_id_iff φ)

/-- Cochrane (2023), pp. 522–523 (**`hist_dichotomy` instantiated**): for the absorbing chain
under full information, the homogeneous model has a nonzero bounded solution iff some regime is
passive, `|φ_i| ≤ 1`. -/
theorem id_hist_dichotomy (φ : Fin N → ℝ) :
    (∃ e, Homog (fullInfo (Fin N)) (detRegime (N := N) id).S φ e ∧ BoundedProc e ∧ e ≠ 0) ↔
      ∃ i, |φ i| ≤ 1 := by
  rw [hist_dichotomy _ (detRegime_initial id), genCondition_id_iff]
  push Not
  rfl

/-- Cochrane (2023), pp. 522–523 (**`absN_pos_dichotomy` instantiated with a known regime**): for
the absorbing chain under full information and `φ_i > 0`, a nonzero bounded homogeneous solution
exists iff some `φ_i ≤ 1`. -/
theorem id_markov_dichotomy {φ : Fin N → ℝ} (hφ : ∀ i, 0 < φ i) :
    (∃ e, Homog (fullInfo (Fin N)) (detRegime (N := N) id).S φ e ∧ BoundedProc e ∧ e ≠ 0) ↔
      ∃ i, φ i ≤ 1 := by
  refine (absN_pos_dichotomy (detRegime id).toMarkov hφ (detRegime_initial id)).trans ?_
  rw [genCondition_id_iff]
  push Not
  simp only [abs_of_pos (hφ _)]

/-- Cochrane (2023), pp. 522–523 (example): two absorbing regimes with `φ = (2, −3)`, both active,
are determinate, for history-driven and for arbitrary bounded disturbances. -/
theorem eg_id_determinate :
    HDeterminate (detRegime (N := 2) id) ![2, -3] ∧
      PDeterminate (fullInfo (Fin 2)) (detRegime (N := 2) id).S ![2, -3] := by
  have h : ∀ i : Fin 2, 1 < |(![2, -3] : Fin 2 → ℝ) i| := by
    intro i
    fin_cases i <;> norm_num
  exact ⟨(id_hist_determinate_iff _).2 h, (id_pullOut_determinate_iff _).2 h⟩

/-- Cochrane (2023), pp. 522–523 (example): two absorbing regimes with `φ = (2, −½)` have a
nonzero bounded sunspot. -/
theorem eg_id_indeterminate :
    ∃ e, Homog (fullInfo (Fin 2)) (detRegime (N := 2) id).S ![2, -1 / 2] e ∧ BoundedProc e ∧
      e ≠ 0 :=
  (id_hist_dichotomy _).2 ⟨1, by norm_num⟩

/-! ### A non-degenerate chain with an unknown regime -/

/-- Cochrane (2023), p. 523 (**`absN_homog_nonzero_of_not_naive` instantiated**): in
`avgSystem`, with `p_ij = ½` and `φ = (½, ½)`, the naive condition fails and the homogeneous model
has a nonzero bounded solution. -/
theorem avg_naive_nonzero :
    ¬ NaiveCondition (ofTwo egHalf) ![1 / 2, 1 / 2] ∧
      ∃ e, Homog avgSystem avgRegime.S ![1 / 2, 1 / 2] e ∧ BoundedProc e ∧ e ≠ 0 := by
  have hpos : ∀ i, 0 < (![1 / 2, 1 / 2] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num
  have hdl : ¬ MarkovRegimes.DLCondition egHalf ![1 / 2, 1 / 2] := by
    simp only [MarkovRegimes.DLCondition, egHalf]
    norm_num
  have hng : ¬ NaiveCondition (ofTwo egHalf) ![1 / 2, 1 / 2] := by
    rintro ⟨h0, hs⟩
    rw [sgnM_eq_absM _ hpos] at hs
    exact hdl ((dl_iff_genCondition egHalf hpos).2 ⟨h0, hs⟩)
  exact ⟨hng, absN_homog_nonzero_of_not_naive avgRegime hng avgRegime_initial⟩

/-! ### Non-degenerate chains with a known regime: forecasts have no atoms -/

/-- Cochrane (2023), p. 522: the indicator that the regime history up to date `t` (inclusive)
is `z`'s. -/
def histInd (S : ℕ → Ω → Fin N) (t : ℕ) (z : Ω) : Ω → ℝ :=
  fun w => if pastOf S (t + 1) w = pastOf S (t + 1) z then 1 else 0

/-- Cochrane (2023), p. 523: with non-degenerate transitions every transition probability is at
most some `q < 1`. -/
theorem exists_q {T : TransitionN N} (hT : Nondegenerate T) (i₀ : Fin N) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ i j, T.P i j ≤ q := by
  have hlt : ∀ i j, T.P i j < 1 := by
    intro i j
    obtain ⟨j₁, j₂, hne, h1, h2⟩ := hT i
    have hnn : ∀ l ∈ Finset.univ, 0 ≤ T.P i l := fun l _ => T.nonneg i l
    have hsum := T.rowSum i
    by_cases hj : j = j₁
    · subst hj
      have := Finset.add_le_sum hnn (Finset.mem_univ j) (Finset.mem_univ j₂) hne
      linarith
    · have := Finset.add_le_sum hnn (Finset.mem_univ j) (Finset.mem_univ j₁) hj
      linarith
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin N × Fin N))
    (fun p => T.P p.1 p.2) ⟨(i₀, i₀), Finset.mem_univ _⟩
  exact ⟨T.P p.1 p.2, T.nonneg _ _, hlt _ _, fun i j => hp (i, j) (Finset.mem_univ _)⟩

/-- Cochrane (2023), p. 523: if each step of the regime history has forecast weight at most
`q < 1`, `E_t 1{history to t+1 = z's} ≤ q · 1{history to t = z's}`, then the date-`0` forecast
gives no weight to any single state. -/
theorem no_atoms_of_step [DecidableEq Ω] {𝔼 : ExpectationSystem Ω} {S : ℕ → Ω → Fin N} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hstep : ∀ t z, 𝔼.E t (histInd S (t + 1) z) ≤ q • histInd S t z)
    (ω z : Ω) : 𝔼.E 0 (fun w => if w = z then 1 else 0) ω = 0 := by
  have hbd : ∀ t, 𝔼.E 0 (histInd S t z) ω ≤ q ^ t := by
    intro t
    induction t with
    | zero =>
      have hle : histInd S 0 z ≤ fun _ => 1 := fun w => by
        change (if _ then (1 : ℝ) else 0) ≤ 1
        split_ifs <;> norm_num
      have := 𝔼.mono 0 hle ω
      rw [𝔼.const] at this
      simpa using this
    | succ t ih =>
      have h1 := 𝔼.mono 0 (hstep t z) ω
      rw [𝔼.tower (Nat.zero_le t), map_smul, Pi.smul_apply, smul_eq_mul] at h1
      calc 𝔼.E 0 (histInd S (t + 1) z) ω ≤ q * 𝔼.E 0 (histInd S t z) ω := h1
        _ ≤ q * q ^ t := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (t + 1) := (pow_succ' q t).symm
  have hpt : ∀ t, (fun w => if w = z then (1 : ℝ) else 0) ≤ histInd S t z := fun t w => by
    simp only [histInd]
    by_cases hw : w = z
    · simp [hw]
    · simp only [hw, ↓reduceIte]
      split_ifs <;> norm_num
  have hnn : 0 ≤ 𝔼.E 0 (fun w => if w = z then (1 : ℝ) else 0) ω :=
    E_nonneg 𝔼 0 (fun w => by
      change (0 : ℝ) ≤ if w = z then 1 else 0
      split_ifs <;> norm_num) ω
  refine le_antisymm (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    fun t => ?_) hnn
  exact (𝔼.mono 0 (hpt t) ω).trans (hbd t)

/-- Cochrane (2023), pp. 522–523 (**the tree hypothesis forces atomless forecasts**): if a regime
satisfies the tree hypothesis with non-degenerate transitions, every date-`0` forecast gives
weight zero to every single state, `E_0 1{z}(ω) = 0`. -/
theorem histMarkov_no_atoms [DecidableEq Ω] {𝔼 : ExpectationSystem Ω} {T : TransitionN N}
    (R : HistMarkovN 𝔼 T) (hT : Nondegenerate T) (ω z : Ω) :
    𝔼.E 0 (fun w => if w = z then 1 else 0) ω = 0 := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_q hT (R.S 0 ω)
  refine no_atoms_of_step (S := R.S) hq0 hq1 (fun t z' w => ?_) ω z
  have hm : 𝔼.E t (histInd R.S (t + 1) z') = fun w => ∑ j, T.P (R.S t w) j *
      (if j :: pastOf R.S (t + 1) w = pastOf R.S (t + 1 + 1) z' then 1 else 0) :=
    R.hist t (fun n => if n.1 :: n.2 = pastOf R.S (t + 1 + 1) z' then 1 else 0)
  rw [hm]
  simp only [Pi.smul_apply, smul_eq_mul, histInd]
  rw [show pastOf R.S (t + 1 + 1) z' = R.S (t + 1) z' :: pastOf R.S (t + 1) z' from rfl]
  by_cases h : pastOf R.S (t + 1) w = pastOf R.S (t + 1) z'
  · simp only [List.cons.injEq, h, and_true, ↓reduceIte, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ]
    exact hq _ _
  · simp [h]

/-- Cochrane (2023), p. 522: with pull-out and a known regime, the regime history up to date `t`
is known at date `t`. -/
theorem histInd_adapted {𝔼 : ExpectationSystem Ω} (hP : 𝔼.PullOut) {S : ℕ → Ω → Fin N}
    (hA : RegimeAdapted 𝔼 S) (z : Ω) : ∀ t, 𝔼.E t (histInd S t z) = histInd S t z := by
  intro t
  induction t with
  | zero =>
    have h0 : histInd S 0 z = (fun l => if l = S 0 z then (1 : ℝ) else 0) ∘ S 0 := by
      funext w
      simp [histInd, pastOf]
    rw [h0, hA 0]
  | succ t ih =>
    have hsplit : histInd S (t + 1) z =
        (fun l => if l = S (t + 1) z then (1 : ℝ) else 0) ∘ S (t + 1) * histInd S t z := by
      funext w
      simp only [histInd, Pi.mul_apply, Function.comp_apply]
      rw [show pastOf S (t + 1 + 1) w = S (t + 1) w :: pastOf S (t + 1) w from rfl,
        show pastOf S (t + 1 + 1) z = S (t + 1) z :: pastOf S (t + 1) z from rfl]
      simp only [List.cons.injEq]
      by_cases h1 : S (t + 1) w = S (t + 1) z <;>
        by_cases h2 : pastOf S (t + 1) w = pastOf S (t + 1) z <;> simp [h1, h2]
    rw [hsplit, hP _ _ _ (hA (t + 1) _), ← ih, 𝔼.known (Nat.le_succ t)]

/-- Cochrane (2023), pp. 522–523 (**pull-out with a known regime forces atomless forecasts**):
with the pull-out property, a known Markov regime and non-degenerate transitions, every date-`0`
forecast gives weight zero to every single state. -/
theorem pullOut_no_atoms [DecidableEq Ω] {𝔼 : ExpectationSystem Ω} {T : TransitionN N}
    (R : MarkovRegimeN 𝔼 T) (hA : RegimeAdapted 𝔼 R.S) (hP : 𝔼.PullOut) (hT : Nondegenerate T)
    (ω z : Ω) :
    𝔼.E 0 (fun w => if w = z then 1 else 0) ω = 0 := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_q hT (R.S 0 ω)
  refine no_atoms_of_step (S := R.S) hq0 hq1 (fun t z' w => ?_) ω z
  set g : Fin N → ℝ := fun l => if l = R.S (t + 1) z' then 1 else 0 with hg
  have hsplit : histInd R.S (t + 1) z' = histInd R.S t z' * (g ∘ R.S (t + 1)) := by
    funext w
    simp only [histInd, Pi.mul_apply, Function.comp_apply, hg]
    rw [show pastOf R.S (t + 1 + 1) w = R.S (t + 1) w :: pastOf R.S (t + 1) w from rfl,
      show pastOf R.S (t + 1 + 1) z' = R.S (t + 1) z' :: pastOf R.S (t + 1) z' from rfl]
    simp only [List.cons.injEq]
    by_cases h1 : R.S (t + 1) w = R.S (t + 1) z' <;>
      by_cases h2 : pastOf R.S (t + 1) w = pastOf R.S (t + 1) z' <;> simp [h1, h2]
  rw [hsplit, hP _ _ _ (histInd_adapted hP hA z' t), R.markov t g]
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hg, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hI : 0 ≤ histInd R.S t z' w := by
    simp only [histInd]
    split_ifs <;> norm_num
  calc histInd R.S t z' w * T.P (R.S t w) (R.S (t + 1) z') ≤ histInd R.S t z' w * q :=
        mul_le_mul_of_nonneg_left (hq _ _) hI
    _ = q * histInd R.S t z' w := mul_comm _ _

end Cochrane.ObservationalEquivalence.TidyR6MarkovInstances
