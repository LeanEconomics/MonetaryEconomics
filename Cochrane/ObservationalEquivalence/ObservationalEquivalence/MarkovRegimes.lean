/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.Expectations
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Mul

/-!
# Markov-switching monetary policy: the Davig–Leeper determinacy condition

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Davig and
Leeper (2006, 2007): policy-rule coefficients switch between regimes according to a Markov
process; "if an economy is currently in what looks like a passive … regime, but people expect a
switch …, then that future … policy selects equilibria"; "a time with `φ < 1` should be something
like 'locally passive' or 'temporarily passive'"), and Chapter 22, §22.3, p. 500 (Markov-switching
estimates of `φ` and `γ`).

## The frictionless model

Two regimes `S_t ∈ {0, 1}` follow a Markov chain with transition matrix `P` (`Transition`). The
frictionless model is the Fisher equation `i_t = E_t π_{t+1}` and the regime-dependent rule
`i_t = φ_{S_t} π_t + u_t`, so `E_t π_{t+1} = φ_{S_t} π_t + u_t`. With all uncertainty coming from
the regimes, a process is a function of the regime history: a node `(i, h)` is the current
regime `i` and the list `h` of past regimes (most recent first), and
`E_t π_{t+1} = ∑_j P_{ij} π(j, i :: h)` (`Solves`). A solution is *bounded* if it is bounded over
all histories (`BoundedFn`). This contains every regime-dependent sunspot.

## Main results (`φ_0, φ_1 > 0`)

* `dl_iff_schur`: the Davig–Leeper "long-run Taylor principle"
  `(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1` together with `p_00/φ_0 + p_11/φ_1 < 2`
  (`DLCondition`) holds iff both eigenvalues of `M = Φ⁻¹P` lie in the open unit disc.
* `homog_eq_zero`: under the condition every bounded solution of the homogeneous model is zero;
  `exists_perron`, `homog_nonzero_of_not_dl`: otherwise there is a nonzero bounded solution
  `π(i, h) = w_i/r^{|h|}` (`r ≥ 1` the Perron root of `M`).
* `fwdSol_solves`, `fwdSol_bounded`: under the condition the forward solution exists and is
  bounded for every bounded disturbance `u`.
* `determinate_iff`: **the model has exactly one bounded equilibrium for every bounded
  disturbance iff the Davig–Leeper condition holds.**
* Examples: `both_active_determinate` (both regimes active), `both_passive_indeterminate`
  (both passive, `φ_i ≤ 1`), `temporarily_passive_determinate` (`φ = (2, ½)`: a passive regime
  that is expected to end is consistent with determinacy), `locally_active_indeterminate`
  (`φ = (2, ½)` with a persistent passive regime: the currently active regime does not determine
  inflation).
* `abstract_homog_eq_zero`, `abstract_homog_nonzero`: the same dichotomy for an arbitrary
  `ExpectationSystem` carrying a Markov regime process (so also excluding extraneous sunspots).
-/

namespace Cochrane.ObservationalEquivalence.MarkovRegimes

open Filter Topology Finset
open scoped Matrix

/-- Cochrane (2023), p. 522 ("switches … according to a Markov process"): the transition matrix
`P_{ij} = Pr(S_{t+1} = j | S_t = i)` of a two-state Markov chain. -/
structure Transition where
  /-- the transition probabilities -/
  P : Fin 2 → Fin 2 → ℝ
  /-- probabilities are nonnegative -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- rows sum to one -/
  rowSum : ∀ i, ∑ j, P i j = 1

/-- Cochrane (2023), p. 522: a node of the regime tree, the current regime and the list of past
regimes (most recent first). -/
abbrev Node := Fin 2 × List (Fin 2)

/-- Cochrane (2023), eqs. (22.3)–(22.4), p. 500, with Markov-switching `φ` (p. 522):
`E_t π_{t+1} = φ_{S_t} π_t + u_t`, where `E_t π_{t+1} = ∑_j P_{ij} π(j, i :: h)` at node
`(i, h)`. -/
def Solves (T : Transition) (φ : Fin 2 → ℝ) (u π : Node → ℝ) : Prop :=
  ∀ i h, ∑ j, T.P i j * π (j, i :: h) = φ i * π (i, h) + u (i, h)

/-- Cochrane (2023), p. 500: a process bounded over all regime histories. -/
def BoundedFn (x : Node → ℝ) : Prop := ∃ B, ∀ n, |x n| ≤ B

/-- Cochrane (2023), p. 523 ("move eigenvalues from stable to unstable"): the matrix
`M = Φ⁻¹P`, `M_{ij} = P_{ij}/φ_i`, whose eigenvalues govern determinacy. -/
noncomputable def regM (T : Transition) (φ : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => T.P i j / φ i

/-- Cochrane (2023), pp. 522–523 (Davig and Leeper's "long-run Taylor principle"):
`(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1` and `p_00/φ_0 + p_11/φ_1 < 2`. -/
def DLCondition (T : Transition) (φ : Fin 2 → ℝ) : Prop :=
  1 < (1 - φ 1) * T.P 0 0 + (1 - φ 0) * T.P 1 1 + φ 0 * φ 1 ∧
    T.P 0 0 / φ 0 + T.P 1 1 / φ 1 < 2

/-! ### The eigenvalue condition -/

/-- Cochrane (2023), p. 523: `M` has nonnegative entries when `φ > 0`. -/
theorem regM_nonneg (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) (i j : Fin 2) :
    0 ≤ regM T φ i j :=
  div_nonneg (T.nonneg i j) (hφ i).le

/-- Cochrane (2023), p. 522: the off-diagonal transition probabilities, `p_01 = 1 − p_00`. -/
theorem P01 (T : Transition) : T.P 0 1 = 1 - T.P 0 0 := by
  have := T.rowSum 0; rw [Fin.sum_univ_two] at this; linarith

/-- Cochrane (2023), p. 522: `p_10 = 1 − p_11`. -/
theorem P10 (T : Transition) : T.P 1 0 = 1 - T.P 1 1 := by
  have := T.rowSum 1; rw [Fin.sum_univ_two] at this; linarith

/-- Cochrane (2023), p. 523: the characteristic polynomial of `M` at `1`, times `φ_0φ_1`, is the
Davig–Leeper expression. -/
theorem charpoly_one_eq (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    (1 - tr2 (regM T φ) + det2 (regM T φ)) * (φ 0 * φ 1) =
      (1 - φ 1) * T.P 0 0 + (1 - φ 0) * T.P 1 1 + φ 0 * φ 1 - 1 := by
  have h0 := (hφ 0).ne'
  have h1 := (hφ 1).ne'
  simp only [tr2, det2, regM, Matrix.of_apply, P01, P10]
  field_simp
  ring

/-- Cochrane (2023), p. 523: for a `2 × 2` matrix with nonnegative entries, both eigenvalues lie
in the open unit disc iff `χ(1) = 1 − tr + det > 0` and `tr < 2`. -/
theorem schur_iff_of_nonneg {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    SchurStable (tr2 A) (det2 A) ↔ 0 < 1 - tr2 A + det2 A ∧ tr2 A < 2 := by
  have hT : 0 ≤ tr2 A := add_nonneg (hA 0 0) (hA 1 1)
  have hdisc : 4 * det2 A ≤ tr2 A ^ 2 := by
    simp only [tr2, det2]
    nlinarith [sq_nonneg (A 0 0 - A 1 1), mul_nonneg (hA 0 1) (hA 1 0)]
  unfold SchurStable
  constructor
  · rintro ⟨hD, hTr⟩
    rw [abs_lt] at hD hTr
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    refine ⟨abs_lt.mpr ⟨by linarith, by nlinarith⟩, ?_⟩
    rw [abs_of_nonneg hT]; linarith

/-- Cochrane (2023), pp. 522–523 (Davig–Leeper): for `φ_0, φ_1 > 0`, the Davig–Leeper condition
holds iff both eigenvalues of `M = Φ⁻¹P` lie in the open unit disc. -/
theorem dl_iff_schur (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    DLCondition T φ ↔ SchurStable (tr2 (regM T φ)) (det2 (regM T φ)) := by
  rw [schur_iff_of_nonneg (regM_nonneg T hφ)]
  have key := charpoly_one_eq T hφ
  have hpos : 0 < φ 0 * φ 1 := mul_pos (hφ 0) (hφ 1)
  have htr : tr2 (regM T φ) = T.P 0 0 / φ 0 + T.P 1 1 / φ 1 := by
    simp [tr2, regM]
  unfold DLCondition
  rw [htr]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    by_contra hcon
    push Not at hcon
    rw [← htr] at h2
    nlinarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [← htr] at h2
    nlinarith

/-! ### Uniqueness under the condition -/

/-- Cochrane (2023), p. 523: entries of `M^{k+1}` through `M^k`. -/
theorem pow_succ_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (k : ℕ) (i l : Fin 2) :
    (A ^ (k + 1)) i l = A i 0 * (A ^ k) 0 l + A i 1 * (A ^ k) 1 l := by
  rw [pow_succ', Matrix.mul_apply, Fin.sum_univ_two]

/-- Cochrane (2023), p. 523 (iterating the expectational recursion): a bounded solution of the
homogeneous model satisfies `|π(i, h)| ≤ B ∑_j (M^k)_{ij}` for every `k`. -/
theorem abs_le_pow_bound (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) {e : Node → ℝ}
    (he : Solves T φ 0 e) {B : ℝ} (hB : ∀ n, |e n| ≤ B) (k : ℕ) :
    ∀ i h, |e (i, h)| ≤ B * ∑ j, (regM T φ ^ k) i j := by
  induction k with
  | zero =>
    intro i h
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_one]
    exact hB _
  | succ k ih =>
    intro i h
    have hφi := hφ i
    have heq : φ i * e (i, h) = ∑ j, T.P i j * e (j, i :: h) := by
      have := he i h; simp only [Pi.zero_apply, add_zero] at this; linarith
    have habs : φ i * |e (i, h)| ≤ ∑ j, T.P i j * |e (j, i :: h)| := by
      rw [← abs_of_pos hφi, ← abs_mul, heq]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [abs_mul, abs_of_nonneg (T.nonneg i j)]
    have hstep : ∑ j, T.P i j * |e (j, i :: h)| ≤
        ∑ j, T.P i j * (B * ∑ l, (regM T φ ^ k) j l) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j (i :: h)) (T.nonneg i j)
    have hval : ∑ j, T.P i j * (B * ∑ l, (regM T φ ^ k) j l) =
        φ i * (B * ∑ l, (regM T φ ^ (k + 1)) i l) := by
      simp only [pow_succ_apply, Fin.sum_univ_two, regM, Matrix.of_apply]
      field_simp
      ring
    have := habs.trans (hstep.trans (le_of_eq hval))
    exact le_of_mul_le_mul_left this hφi

/-- Cochrane (2023), pp. 522–523: under the Davig–Leeper condition the homogeneous model has no
bounded solution other than zero. -/
theorem homog_eq_zero (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {e : Node → ℝ} (he : Solves T φ 0 e) (hb : BoundedFn e) :
    e = 0 := by
  obtain ⟨B, hB⟩ := hb
  have hS := (dl_iff_schur T hφ).mp hdl
  funext n
  obtain ⟨i, h⟩ := n
  have hlim : Tendsto (fun k => B * ∑ j, (regM T φ ^ k) i j) atTop (𝓝 0) := by
    have h0 := tendsto_pow_entry hS i 0
    have h1 := tendsto_pow_entry hS i 1
    simpa [Fin.sum_univ_two] using (h0.add h1).const_mul B
  have hle : |e (i, h)| ≤ 0 :=
    ge_of_tendsto' hlim fun k => abs_le_pow_bound T hφ he hB k i h
  simpa using abs_nonpos_iff.mp hle

/-! ### Non-uniqueness when the condition fails -/

/-- Cochrane (2023), p. 523 (tool): `(Aw)_i = A_{i0} w_0 + A_{i1} w_1`. -/
theorem mulVec_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) (w : Fin 2 → ℝ) (i : Fin 2) :
    (A *ᵥ w) i = A i 0 * w 0 + A i 1 * w 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Cochrane (2023), p. 523 (Perron–Frobenius for `2 × 2` nonnegative matrices): if the
eigenvalues of a nonnegative `A` are not both in the open unit disc, `A` has an eigenvalue
`r ≥ 1` with a nonzero nonnegative eigenvector. -/
theorem exists_perron {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : ∀ i j, 0 ≤ A i j)
    (hns : ¬ SchurStable (tr2 A) (det2 A)) :
    ∃ (r : ℝ) (w : Fin 2 → ℝ), 1 ≤ r ∧ (∀ i, 0 ≤ w i) ∧ w ≠ 0 ∧ A *ᵥ w = r • w := by
  rw [schur_iff_of_nonneg hA] at hns
  have hcase : 1 - tr2 A + det2 A ≤ 0 ∨ 2 ≤ tr2 A := by
    by_contra hcon
    push Not at hcon
    exact hns hcon
  simp only [tr2, det2] at hcase
  set a := A 0 0
  set b := A 0 1
  set c := A 1 0
  set d := A 1 1
  have ha := hA 0 0
  have hb := hA 0 1
  have hc := hA 1 0
  have hd := hA 1 1
  rcases hb.lt_or_eq with hbpos | hb0
  · -- `b > 0`: the Perron root `r = (a + d + √disc)/2` with eigenvector `(b, r − a)`
    set s := Real.sqrt ((a - d) ^ 2 + 4 * b * c) with hs
    have hdisc : 0 ≤ (a - d) ^ 2 + 4 * b * c := by positivity
    have hs2 : s ^ 2 = (a - d) ^ 2 + 4 * b * c := Real.sq_sqrt hdisc
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsad : |a - d| ≤ s := by
      rw [hs, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    set r := (a + d + s) / 2 with hr
    have hra : 0 ≤ r - a := by
      have := (abs_le.mp hsad).2; rw [hr]; linarith
    have hr1 : 1 ≤ r := by
      rcases hcase with h1 | h2
      · by_contra hlt
        push Not at hlt
        have hr1' : (a + d - s) / 2 ≤ r := by rw [hr]; linarith
        have hprod : 1 - (a + d) + (a * d - b * c) = (1 - (a + d - s) / 2) * (1 - r) := by
          rw [hr]; nlinarith
        have : 0 < (1 - (a + d - s) / 2) * (1 - r) :=
          mul_pos (by linarith) (by linarith)
        linarith
      · rw [hr]; linarith
    refine ⟨r, ![b, r - a], hr1, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using hb
      · simpa using hra
    · intro h
      have := congrFun h 0
      simp only [Fin.isValue, Matrix.cons_val_zero, Pi.zero_apply] at this
      exact hbpos.ne' this
    · funext i
      fin_cases i
      · rw [mulVec_fin_two]
        simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
        change a * b + b * (r - a) = r * b
        ring
      · rw [mulVec_fin_two]
        simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, smul_eq_mul]
        change c * b + d * (r - a) = r * (r - a)
        have : r ^ 2 - (a + d) * r + (a * d - b * c) = 0 := by rw [hr]; nlinarith
        nlinarith
  · -- `b = 0`: lower triangular
    have hb0' : b = 0 := hb0.symm
    rw [hb0'] at hcase
    by_cases hd1 : 1 ≤ d
    · refine ⟨d, ![0, 1], hd1, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp
      · intro h
        have := congrFun h 1
        simp at this
      · funext i
        fin_cases i
        · rw [mulVec_fin_two]
          simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul,
            mul_zero]
          change 0 + b * 1 = 0
          rw [hb0']; ring
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          rfl
    · push Not at hd1
      have ha1 : 1 ≤ a := by
        rcases hcase with h1 | h2
        · by_contra hlt
          push Not at hlt
          nlinarith
        · linarith
      refine ⟨a, ![a - d, c], ha1, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp <;> linarith
      · intro h
        have := congrFun h 0
        simp at this
        linarith
      · funext i
        fin_cases i
        · rw [mulVec_fin_two]
          simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
          change a * (a - d) + b * c = a * (a - d)
          rw [hb0']; ring
        · rw [mulVec_fin_two]
          simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, smul_eq_mul]
          change c * (a - d) + d * c = a * c
          ring

/-- Cochrane (2023), pp. 522–523: if the Davig–Leeper condition fails, the homogeneous model has
a nonzero bounded solution `π(i, h) = w_i/r^{|h|}` — inflation is not determined. -/
theorem homog_nonzero_of_not_dl (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hndl : ¬ DLCondition T φ) : ∃ e : Node → ℝ, Solves T φ 0 e ∧ BoundedFn e ∧ e ≠ 0 := by
  rw [dl_iff_schur T hφ] at hndl
  obtain ⟨r, w, hr1, hw0, hwne, hMw⟩ := exists_perron (regM_nonneg T hφ) hndl
  have hr0 : 0 < r := by linarith
  refine ⟨fun n => w n.1 / r ^ n.2.length, ?_, ?_, ?_⟩
  · intro i h
    have hrow := congrFun hMw i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, regM, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul] at hrow
    have hφi := (hφ i).ne'
    have hrow' : T.P i 0 * w 0 + T.P i 1 * w 1 = φ i * (r * w i) := by
      field_simp at hrow; linarith
    have hpow : r ^ (h.length + 1) = r ^ h.length * r := pow_succ r h.length
    have hrl := (pow_pos hr0 h.length).ne'
    have hr0' := hr0.ne'
    have key : T.P i 0 * (w 0 / r ^ (h.length + 1)) + T.P i 1 * (w 1 / r ^ (h.length + 1)) =
        φ i * (w i / r ^ h.length) := by
      rw [hpow, show T.P i 0 * (w 0 / (r ^ h.length * r)) + T.P i 1 * (w 1 / (r ^ h.length * r))
        = (T.P i 0 * w 0 + T.P i 1 * w 1) / (r ^ h.length * r) by ring, hrow']
      field_simp
    simpa [Fin.sum_univ_two] using key
  · refine ⟨|w 0| + |w 1|, fun n => ?_⟩
    have hge : 1 ≤ r ^ n.2.length := one_le_pow₀ hr1
    rw [abs_div, abs_of_pos (pow_pos hr0 _)]
    have hwn : ∀ i : Fin 2, |w i| ≤ |w 0| + |w 1| := by
      intro i; fin_cases i <;> simp [abs_nonneg]
    exact (div_le_self (abs_nonneg _) hge).trans (hwn _)
  · intro h
    apply hwne
    funext i
    have := congrFun h (i, [])
    simpa using this

/-! ### Existence: the forward solution -/

/-- Cochrane (2023), p. 523: the matrix powers of a Schur-stable `2 × 2` matrix are absolutely
summable entry by entry. -/
theorem summable_pow_entry_of_schur {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : SchurStable (tr2 A) (det2 A)) (i j : Fin 2) : Summable (fun k => |(A ^ k) i j|) := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots _ _).mp h
  set ρ := max ‖root₁ (tr2 A) (det2 A)‖ ‖root₂ (tr2 A) (det2 A)‖ with hρ
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρ1 : ρ < 1 := max_lt h1 h2
  have hgeo : Summable (fun k : ℕ => ((k : ℝ) + 1) * ρ ^ k) := by
    have ha := summable_pow_mul_geometric_of_norm_lt_one 1 (r := ρ)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1)
    have hb := summable_geometric_of_lt_one hρ0 hρ1
    simpa [add_mul] using ha.add hb
  have hg : Summable (fun k : ℕ => ((k + 1 : ℕ) + 1 : ℝ) * ρ ^ (k + 1) * |A i j| +
      |det2 A| * (((k : ℝ) + 1) * ρ ^ k)) := by
    refine Summable.add ?_ (hgeo.mul_left _)
    have := (summable_nat_add_iff 1).mpr hgeo
    exact this.mul_right _
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) hg
  refine (abs_pow_entry_le A k i j).trans ?_
  have hc1 := abs_chSeq_le (tr2 A) (det2 A) (k + 1)
  have hc0 := abs_chSeq_le (tr2 A) (det2 A) k
  push_cast at hc1 hc0 ⊢
  gcongr

/-- Cochrane (2023), p. 523 (the forward solution): the terms
`Δ_0 = −u/φ`, `Δ_{k+1}(i, h) = ∑_j P_{ij} Δ_k(j, i :: h)/φ_i`. -/
noncomputable def fwdTerm (T : Transition) (φ : Fin 2 → ℝ) (u : Node → ℝ) : ℕ → Node → ℝ
  | 0, n => -u n / φ n.1
  | k + 1, n => (∑ j, T.P n.1 j * fwdTerm T φ u k (j, n.1 :: n.2)) / φ n.1

/-- Cochrane (2023), p. 523: the forward solution `π = ∑_k Δ_k`. -/
noncomputable def fwdSol (T : Transition) (φ : Fin 2 → ℝ) (u : Node → ℝ) (n : Node) : ℝ :=
  ∑' k, fwdTerm T φ u k n

/-- Cochrane (2023), p. 523: `|Δ_k(i, h)| ≤ U ∑_l (M^k)_{il}/φ_l`. -/
theorem fwdTerm_bound (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) {u : Node → ℝ}
    {U : ℝ} (hU : ∀ n, |u n| ≤ U) (k : ℕ) :
    ∀ i h, |fwdTerm T φ u k (i, h)| ≤ U * ∑ l, (regM T φ ^ k) i l / φ l := by
  induction k with
  | zero =>
    intro i h
    simp only [fwdTerm, pow_zero, Matrix.one_apply, ite_div, zero_div, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
    rw [abs_div, abs_neg, abs_of_pos (hφ i), mul_one_div]
    exact div_le_div_of_nonneg_right (hU _) (hφ i).le
  | succ k ih =>
    intro i h
    have hφi := hφ i
    simp only [fwdTerm]
    rw [abs_div, abs_of_pos hφi, div_le_iff₀ hφi]
    calc |∑ j, T.P i j * fwdTerm T φ u k (j, i :: h)|
        ≤ ∑ j, T.P i j * |fwdTerm T φ u k (j, i :: h)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (T.nonneg i j)]
      _ ≤ ∑ j, T.P i j * (U * ∑ l, (regM T φ ^ k) j l / φ l) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (ih j (i :: h)) (T.nonneg i j)
      _ = (U * ∑ l, (regM T φ ^ (k + 1)) i l / φ l) * φ i := by
          simp only [pow_succ_apply, Fin.sum_univ_two, regM, Matrix.of_apply]
          have h0 := (hφ 0).ne'
          have h1 := (hφ 1).ne'
          field_simp
          ring

/-- Cochrane (2023), p. 523: the dominating sequence for the forward solution is summable under
the Davig–Leeper condition. -/
theorem summable_bound (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) (U : ℝ) (i : Fin 2) :
    Summable (fun k => U * ∑ l, (regM T φ ^ k) i l / φ l) := by
  have hS := (dl_iff_schur T hφ).mp hdl
  refine Summable.mul_left U ?_
  simp only [Fin.sum_univ_two]
  refine Summable.add ?_ ?_
  · exact ((summable_pow_entry_of_schur hS i 0).of_abs).div_const _
  · exact ((summable_pow_entry_of_schur hS i 1).of_abs).div_const _

/-- Cochrane (2023), p. 523: the forward-solution terms are summable at every node. -/
theorem fwdTerm_summable (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : Node → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) (n : Node) :
    Summable (fun k => fwdTerm T φ u k n) := by
  obtain ⟨i, h⟩ := n
  exact Summable.of_norm_bounded (summable_bound T hφ hdl U i) fun k => by
    rw [Real.norm_eq_abs]; exact fwdTerm_bound T hφ hU k i h

/-- Cochrane (2023), pp. 522–523: under the Davig–Leeper condition the forward solution solves
the model `E_t π_{t+1} = φ_{S_t} π_t + u_t`. -/
theorem fwdSol_solves (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : Node → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) :
    Solves T φ u (fwdSol T φ u) := by
  intro i h
  have hs := fun n => fwdTerm_summable T hφ hdl hU n
  have hφi := (hφ i).ne'
  have hsplit := (hs (i, h)).tsum_eq_zero_add
  have hsucc : ∀ k, fwdTerm T φ u (k + 1) (i, h) =
      (T.P i 0 * fwdTerm T φ u k (0, i :: h) + T.P i 1 * fwdTerm T φ u k (1, i :: h)) / φ i := by
    intro k; simp [fwdTerm, Fin.sum_univ_two]
  have hA : ∑ j, T.P i j * fwdSol T φ u (j, i :: h) =
      ∑' k, (T.P i 0 * fwdTerm T φ u k (0, i :: h) + T.P i 1 * fwdTerm T φ u k (1, i :: h)) := by
    simp only [fwdSol, Fin.sum_univ_two]
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add ((hs _).mul_left _)
      ((hs _).mul_left _)]
  have hB : fwdSol T φ u (i, h) = -u (i, h) / φ i +
      (∑' k, (T.P i 0 * fwdTerm T φ u k (0, i :: h) +
        T.P i 1 * fwdTerm T φ u k (1, i :: h))) / φ i := by
    unfold fwdSol
    rw [hsplit]
    simp only [hsucc]
    rw [tsum_div_const]
    rfl
  rw [hA, hB]
  field_simp
  ring

/-- Cochrane (2023), pp. 522–523: under the Davig–Leeper condition the forward solution is
bounded. -/
theorem fwdSol_bounded (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hdl : DLCondition T φ) {u : Node → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) :
    BoundedFn (fwdSol T φ u) := by
  set g : Fin 2 → ℝ := fun i => ∑' k, U * ∑ l, (regM T φ ^ k) i l / φ l with hg
  refine ⟨|g 0| + |g 1|, fun n => ?_⟩
  obtain ⟨i, h⟩ := n
  have h1 : |fwdSol T φ u (i, h)| ≤ g i := by
    unfold fwdSol
    have hsa : Summable (fun k => |fwdTerm T φ u k (i, h)|) :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => fwdTerm_bound T hφ hU k i h)
        (summable_bound T hφ hdl U i)
    have hn := norm_tsum_le_tsum_norm (f := fun k => fwdTerm T φ u k (i, h))
      (by simpa only [Real.norm_eq_abs] using hsa)
    simp only [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    exact Summable.tsum_le_tsum (fun k => fwdTerm_bound T hφ hU k i h) hsa
      (summable_bound T hφ hdl U i)
  have h2 : g i ≤ |g 0| + |g 1| := by
    fin_cases i
    · simp only [Fin.zero_eta]; linarith [le_abs_self (g 0), abs_nonneg (g 1)]
    · simp only [Fin.mk_one]; linarith [le_abs_self (g 1), abs_nonneg (g 0)]
  exact h1.trans h2

/-- Cochrane (2023), pp. 522–523: the difference of two solutions solves the homogeneous
model. -/
theorem solves_sub (T : Transition) (φ : Fin 2 → ℝ) {u π₁ π₂ : Node → ℝ}
    (h₁ : Solves T φ u π₁) (h₂ : Solves T φ u π₂) : Solves T φ 0 (π₁ - π₂) := by
  intro i h
  have e1 := h₁ i h
  have e2 := h₂ i h
  simp only [Pi.sub_apply, Pi.zero_apply, Fin.sum_univ_two] at e1 e2 ⊢
  linarith

/-- Cochrane (2023), pp. 522–523 (Davig and Leeper's determinacy condition): for `φ_0, φ_1 > 0`
the frictionless Markov-switching model has exactly one bounded equilibrium for every bounded
disturbance iff `(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1` and `p_00/φ_0 + p_11/φ_1 < 2`. -/
theorem determinate_iff (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    (∀ u, BoundedFn u → ∃! π, Solves T φ u π ∧ BoundedFn π) ↔ DLCondition T φ := by
  constructor
  · intro h
    by_contra hndl
    obtain ⟨e, he, heb, hne⟩ := homog_nonzero_of_not_dl T hφ hndl
    obtain ⟨π, _, huniq⟩ := h 0 ⟨0, fun n => by simp⟩
    have h0 : (0 : Node → ℝ) = π := huniq 0 ⟨fun i h => by simp, ⟨0, fun n => by simp⟩⟩
    have he' : e = π := huniq e ⟨he, heb⟩
    exact hne (he'.trans h0.symm)
  · intro hdl u ⟨U, hU⟩
    refine ⟨fwdSol T φ u, ⟨fwdSol_solves T hφ hdl hU, fwdSol_bounded T hφ hdl hU⟩, ?_⟩
    rintro π ⟨hπ, hπb⟩
    have hd := solves_sub T φ hπ (fwdSol_solves T hφ hdl hU)
    obtain ⟨B1, hB1⟩ := hπb
    obtain ⟨B2, hB2⟩ := fwdSol_bounded T hφ hdl hU
    have hzero := homog_eq_zero T hφ hdl hd ⟨B1 + B2, fun n => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hB1 n) (hB2 n))⟩
    exact sub_eq_zero.mp hzero

/-! ### Examples -/

/-- Cochrane (2023), p. 523: if both regimes are active (`φ_i > 1`) the Davig–Leeper condition
holds. -/
theorem both_active_determinate (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 1 < φ i) :
    DLCondition T φ := by
  have h00 : T.P 0 0 ≤ 1 := by have := P01 T; linarith [T.nonneg 0 1]
  have h11 : T.P 1 1 ≤ 1 := by have := P10 T; linarith [T.nonneg 1 0]
  have hn0 := T.nonneg 0 0
  have hn1 := T.nonneg 1 1
  have hφ0 := hφ 0
  have hφ1 := hφ 1
  refine ⟨by nlinarith, ?_⟩
  have e0 : T.P 0 0 / φ 0 < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  have e1 : T.P 1 1 / φ 1 < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  linarith

/-- Cochrane (2023), p. 523: if both regimes are passive (`0 < φ_i ≤ 1`) the Davig–Leeper
condition fails: inflation is indeterminate. -/
theorem both_passive_indeterminate (T : Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i)
    (hφ1 : ∀ i, φ i ≤ 1) : ¬ DLCondition T φ := by
  intro hdl
  have hS := (dl_iff_schur T hφ).mp hdl
  have hrow : ∀ k i, 1 ≤ ∑ j, (regM T φ ^ k) i j := by
    intro k
    induction k with
    | zero => intro i; simp [Matrix.one_apply]
    | succ k ih =>
      intro i
      have hM0 := regM_nonneg T hφ i 0
      have hM1 := regM_nonneg T hφ i 1
      have hsum : 1 ≤ regM T φ i 0 + regM T φ i 1 := by
        simp only [regM, Matrix.of_apply]
        rw [← add_div, ← Fin.sum_univ_two (fun j => T.P i j), T.rowSum i,
          le_div_iff₀ (hφ i), one_mul]
        exact hφ1 i
      simp only [Fin.sum_univ_two, pow_succ_apply] at ih ⊢
      nlinarith [ih 0, ih 1]
  have hlim : Tendsto (fun k => ∑ j, (regM T φ ^ k) 0 j) atTop (𝓝 0) := by
    simpa [Fin.sum_univ_two] using
      (tendsto_pow_entry hS 0 0).add (tendsto_pow_entry hS 0 1)
  have := ge_of_tendsto' hlim fun k => hrow k 0
  linarith

/-- Cochrane (2023), p. 523 (example): an absorbing-free chain with `p_00 = 0.9`, `p_11 = 0.4`. -/
noncomputable def egShortPassive : Transition where
  P := ![![9 / 10, 1 / 10], ![6 / 10, 4 / 10]]
  nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  rowSum := by intro i; fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num

/-- Cochrane (2023), p. 523 (example): a chain with a persistent passive regime,
`p_00 = p_11 = 0.9`. -/
noncomputable def egLongPassive : Transition where
  P := ![![9 / 10, 1 / 10], ![1 / 10, 9 / 10]]
  nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  rowSum := by intro i; fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num

/-- Cochrane (2023), p. 523 ("A time with `φ < 1` should be something like … 'temporarily
passive'"): with `φ = (2, ½)` and a short-lived passive regime the equilibrium is determinate,
although regime `1` is passive. -/
theorem temporarily_passive_determinate : DLCondition egShortPassive ![2, 1 / 2] := by
  simp only [DLCondition, egShortPassive]
  norm_num

/-- Cochrane (2023), pp. 522–523: with `φ = (2, ½)` and a persistent passive regime the
equilibrium is indeterminate, although regime `0` is active — the expected future passive
regime undoes the current active one. -/
theorem locally_active_indeterminate : ¬ DLCondition egLongPassive ![2, 1 / 2] := by
  simp only [DLCondition, egLongPassive]
  norm_num

/-! ### The same dichotomy for an arbitrary expectation system -/

variable {Ω : Type*}

variable (𝔼₀ : ExpectationSystem Ω) (T₀ : Transition)

/-- Cochrane (2023), p. 522: a Markov regime process `S_t` in an expectation system — adapted,
and `E_t f(S_{t+1}) = ∑_j P_{S_t, j} f(j)`. -/
structure MarkovRegime where
  /-- the regime process -/
  S : ℕ → Ω → Fin 2
  /-- the Markov property -/
  markov : ∀ t (f : Fin 2 → ℝ), 𝔼₀.E t (f ∘ S (t + 1)) = fun ω => ∑ j, T₀.P (S t ω) j * f j

/-- Cochrane (2023), pp. 522–523: in any expectation system with a Markov regime process, a
bounded solution of `E_t π_{t+1} = φ_{S_t} π_t` (possibly driven by extraneous sunspots)
satisfies `|π_t| ≤ B ∑_j (M^k)_{S_t, j}` for every `k`. -/
theorem abstract_bound {𝔼 : ExpectationSystem Ω} {T : Transition} (R : MarkovRegime 𝔼 T)
    {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) {e : ℕ → Ω → ℝ}
    (he : ∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (R.S t ω) * e t ω) {B : ℝ}
    (hB : ∀ t ω, |e t ω| ≤ B) (k : ℕ) :
    ∀ t ω, |e t ω| ≤ B * ∑ j, (regM T φ ^ k) (R.S t ω) j := by
  induction k with
  | zero =>
    intro t ω
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_one]
    exact hB t ω
  | succ k ih =>
    intro t ω
    set f : Fin 2 → ℝ := fun l => B * ∑ j, (regM T φ ^ k) l j with hf
    have hφi := hφ (R.S t ω)
    have hup : e (t + 1) ≤ f ∘ R.S (t + 1) :=
      fun ω' => (le_abs_self _).trans (ih (t + 1) ω')
    have hlo : -(f ∘ R.S (t + 1)) ≤ e (t + 1) :=
      fun ω' => by
        have := ih (t + 1) ω'; have := neg_abs_le (e (t + 1) ω')
        simp only [Pi.neg_apply, Function.comp_apply]; linarith
    have h1 := 𝔼.mono t hup ω
    have h2 := 𝔼.mono t hlo ω
    rw [map_neg, R.markov t f] at h2
    rw [R.markov t f] at h1
    beta_reduce at h1
    have hE : 𝔼.E t (e (t + 1)) ω = φ (R.S t ω) * e t ω := congrFun (he t) ω
    have hval : ∑ j, T.P (R.S t ω) j * f j =
        φ (R.S t ω) * (B * ∑ j, (regM T φ ^ (k + 1)) (R.S t ω) j) := by
      simp only [hf, pow_succ_apply, Fin.sum_univ_two, regM, Matrix.of_apply]
      field_simp
      ring
    simp only [Pi.neg_apply] at h2
    rw [hE, hval] at h1 h2
    have habs : φ (R.S t ω) * |e t ω| ≤
        φ (R.S t ω) * (B * ∑ j, (regM T φ ^ (k + 1)) (R.S t ω) j) := by
      rw [← abs_of_pos hφi, ← abs_mul, abs_le]
      rw [abs_of_pos hφi]
      exact ⟨by linarith, h1⟩
    exact le_of_mul_le_mul_left habs hφi

/-- Cochrane (2023), pp. 522–523: under the Davig–Leeper condition, in any expectation system with
a Markov regime process, the only bounded solution of the homogeneous model is zero (no
regime-dependent or extraneous sunspots survive). -/
theorem abstract_homog_eq_zero {𝔼 : ExpectationSystem Ω} {T : Transition}
    (R : MarkovRegime 𝔼 T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) (hdl : DLCondition T φ)
    {e : ℕ → Ω → ℝ} (he : ∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (R.S t ω) * e t ω)
    (hb : BoundedProc e) : e = 0 := by
  obtain ⟨B, hB⟩ := hb
  have hS := (dl_iff_schur T hφ).mp hdl
  funext t ω
  have hlim : Tendsto (fun k => B * ∑ j, (regM T φ ^ k) (R.S t ω) j) atTop (𝓝 0) := by
    have h0 := tendsto_pow_entry hS (R.S t ω) 0
    have h1 := tendsto_pow_entry hS (R.S t ω) 1
    simpa [Fin.sum_univ_two] using (h0.add h1).const_mul B
  have hle : |e t ω| ≤ 0 :=
    ge_of_tendsto' hlim fun k => abstract_bound R hφ he hB k t ω
  simpa using abs_nonpos_iff.mp hle

/-- Cochrane (2023), pp. 522–523: if the Davig–Leeper condition fails and both regimes are
possible at date `0`, then in any expectation system with a Markov regime process the
homogeneous model has a nonzero bounded solution `π_t = w_{S_t}/r^t`. -/
theorem abstract_homog_nonzero {𝔼 : ExpectationSystem Ω} {T : Transition}
    (R : MarkovRegime 𝔼 T) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) (hndl : ¬ DLCondition T φ)
    (hS0 : ∀ i, ∃ ω, R.S 0 ω = i) :
    ∃ e : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (e (t + 1)) = fun ω => φ (R.S t ω) * e t ω) ∧
      BoundedProc e ∧ e ≠ 0 := by
  rw [dl_iff_schur T hφ] at hndl
  obtain ⟨r, w, hr1, hw0, hwne, hMw⟩ := exists_perron (regM_nonneg T hφ) hndl
  have hr0 : 0 < r := by linarith
  refine ⟨fun t ω => w (R.S t ω) / r ^ t, ?_, ?_, ?_⟩
  · intro t
    have hm : 𝔼.E t (fun ω => w (R.S (t + 1) ω) / r ^ (t + 1)) =
        fun ω => ∑ j, T.P (R.S t ω) j * (w j / r ^ (t + 1)) :=
      R.markov t (fun l => w l / r ^ (t + 1))
    rw [hm]
    funext ω
    set i := R.S t ω
    have hrow := congrFun hMw i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, regM, Matrix.of_apply,
      Pi.smul_apply, smul_eq_mul] at hrow
    have hφi := (hφ i).ne'
    have hrow' : T.P i 0 * w 0 + T.P i 1 * w 1 = φ i * (r * w i) := by
      field_simp at hrow; linarith
    have hrl := (pow_pos hr0 t).ne'
    have hr0' := hr0.ne'
    have key : T.P i 0 * (w 0 / r ^ (t + 1)) + T.P i 1 * (w 1 / r ^ (t + 1)) =
        φ i * (w i / r ^ t) := by
      rw [pow_succ, show T.P i 0 * (w 0 / (r ^ t * r)) + T.P i 1 * (w 1 / (r ^ t * r))
        = (T.P i 0 * w 0 + T.P i 1 * w 1) / (r ^ t * r) by ring, hrow']
      field_simp
    simpa [Fin.sum_univ_two] using key
  · refine ⟨|w 0| + |w 1|, fun t ω => ?_⟩
    have hge : 1 ≤ r ^ t := one_le_pow₀ hr1
    rw [abs_div, abs_of_pos (pow_pos hr0 _)]
    have hwn : ∀ i : Fin 2, |w i| ≤ |w 0| + |w 1| := by
      intro i; fin_cases i <;> simp [abs_nonneg]
    exact (div_le_self (abs_nonneg _) hge).trans (hwn _)
  · intro h
    apply hwne
    funext i
    obtain ⟨ω, hω⟩ := hS0 i
    have := congrFun (congrFun h 0) ω
    simpa [hω] using this

end Cochrane.ObservationalEquivalence.MarkovRegimes
