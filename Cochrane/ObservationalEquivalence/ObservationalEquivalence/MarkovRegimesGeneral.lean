/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.MarkovRegimes
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Markov-switching monetary policy with `N` regimes and coefficients of any sign

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 24, §24.2, pp. 522–523 (Davig and
Leeper (2006, 2007): policy-rule coefficients switch according to a Markov process; "the Markov
assumption, with exactly two (or even N) states"; "a time with `φ < 1` should be something like
'locally passive' or 'temporarily passive'"), and Chapter 22, §22.3, p. 500.

## The model

`N` regimes follow a Markov chain with transition matrix `P` (`TransitionN`); the frictionless
model is `E_t π_{t+1} = φ_{S_t} π_t + u_t` with arbitrary real rule coefficients `φ_i` (positive,
negative or zero). As in `MarkovRegimes`, a process is a function of the regime history: at the
node `(i, h)` (current regime `i`, past regimes `h`, most recent first),
`E_t π_{t+1} = ∑_j P_{ij} π(j, i :: h)` (`Solves`). The model is *determinate*
(`Determinate`) if for every bounded disturbance `u` there is exactly one bounded solution.

## Main results

* `determinate_iff` (**Davig–Leeper for `N` regimes and any signs**): the model is determinate
  iff every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` (entries `P_{ij}/|φ_i|`, a nonnegative
  matrix; `absM`) is `< 1` (`GenCondition`). The spectral radius is Mathlib's `spectralRadius ℂ`
  of the matrix viewed over `ℂ`.
* **Zero coefficients** (`zero_coeff_indeterminate`): a regime with `φ_i = 0` makes the model
  indeterminate — the date-`0` value in that regime enters no equation. Nothing replaces `Φ⁻¹`: the
  inverse-free form of the condition is `∀ i, φ_i ≠ 0` together with `ρ(|Φ|⁻¹P) < 1`, and Lean's
  junk value `1/0 = 0` must not be used (`junk_inverse_wrong`).
* **Signs do not matter** (`determinate_iff_abs`, `determinate_congr_abs`): determinacy depends
  only on `|φ_i|`. Necessity uses the sign-twisted sunspot `π(i, h) = s(h) x_{|h|}(i)`,
  `s(h) = ∏_{l ∈ h} sgn φ_l`, where `x_t = |Φ|⁻¹P x_{t+1}` is built from a complex eigenvector of
  `|Φ|⁻¹P` with eigenvalue of modulus `≥ 1`; sufficiency uses Gelfand's formula
  (`summable_entry_of_lt`) and the forward solution `fwdSol`.
* **The naive generalisation fails** (`naive_necessary`, `naive_not_sufficient`): the spectral
  condition on `Φ⁻¹P` itself is necessary but not sufficient — with `P_{ij} = ½` and
  `φ = (½, −½)`, `Φ⁻¹P` is nilpotent but the model is indeterminate.
* **The two-regime Davig–Leeper formula fails with negative coefficients**
  (`dl_formula_fails_negative`): with `p_00 = 0.9`, `p_11 = 0.5`, `φ = (½, −½)` the formula
  `(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1`, `p_00/φ_0 + p_11/φ_1 < 2` holds, but the model is
  indeterminate. Corrected statement (`dl_corrected`): for two regimes with `φ_i ≠ 0`, determinacy
  iff the Davig–Leeper formula holds for `|φ_0|, |φ_1|`.
* **Special cases**: `determinate_iff_old`, `dl_iff_genCondition` (the two-regime, `φ_i > 0`
  results of `MarkovRegimes` are the case `N = 2`); `iid_determinate_iff` (i.i.d. regimes:
  determinate iff `∑_j q_j/|φ_j| < 1`).
* Examples: `negative_regime_determinate` (`φ = (2, −½)`, short-lived passive regime),
  `three_regime_determinate` (three i.i.d. regimes with `φ = (4, −4, ½)`).
-/

namespace Cochrane.ObservationalEquivalence.MarkovRegimesGeneral

open Filter Topology
open scoped Matrix ENNReal NNReal

variable (N : ℕ)

/-- Cochrane (2023), p. 523 ("exactly two (or even N) states"): the transition matrix
`P_{ij} = Pr(S_{t+1} = j | S_t = i)` of an `N`-state Markov chain. -/
structure TransitionN where
  /-- the transition probabilities -/
  P : Fin N → Fin N → ℝ
  /-- probabilities are nonnegative -/
  nonneg : ∀ i j, 0 ≤ P i j
  /-- rows sum to one -/
  rowSum : ∀ i, ∑ j, P i j = 1

/-- Cochrane (2023), p. 522: a node of the regime tree, the current regime and the list of past
regimes (most recent first). -/
abbrev NodeN := Fin N × List (Fin N)

variable {N}

/-- Cochrane (2023), eqs. (22.3)–(22.4), p. 500, with Markov-switching `φ` (pp. 522–523):
`E_t π_{t+1} = φ_{S_t} π_t + u_t`, with `E_t π_{t+1} = ∑_j P_{ij} π(j, i :: h)` at `(i, h)`. -/
def Solves (T : TransitionN N) (φ : Fin N → ℝ) (u π : NodeN N → ℝ) : Prop :=
  ∀ i h, ∑ j, T.P i j * π (j, i :: h) = φ i * π (i, h) + u (i, h)

/-- Cochrane (2023), p. 500: a process bounded over all regime histories. -/
def BoundedFn (x : NodeN N → ℝ) : Prop := ∃ B, ∀ n, |x n| ≤ B

/-- Cochrane (2023), pp. 522–523: the model is determinate — for every bounded disturbance there
is exactly one bounded equilibrium. -/
def Determinate (T : TransitionN N) (φ : Fin N → ℝ) : Prop :=
  ∀ u, BoundedFn u → ∃! π, Solves T φ u π ∧ BoundedFn π

/-- Cochrane (2023), p. 523 ("move eigenvalues from stable to unstable"): the nonnegative matrix
`|Φ|⁻¹P`, entries `P_{ij}/|φ_i|`. -/
noncomputable def absM (T : TransitionN N) (φ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => T.P i j / |φ i|

/-- Cochrane (2023), p. 523: the matrix `Φ⁻¹P`, entries `P_{ij}/φ_i`. -/
noncomputable def sgnM (T : TransitionN N) (φ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => T.P i j / φ i

/-- Cochrane (2023), p. 523: the spectral radius of a real matrix, the largest modulus of its
complex eigenvalues (Mathlib's `spectralRadius ℂ` of the matrix viewed over `ℂ`). -/
noncomputable def specRad (A : Matrix (Fin N) (Fin N) ℝ) : ℝ≥0∞ :=
  spectralRadius ℂ (A.map Complex.ofReal)

/-- Cochrane (2023), pp. 522–523 (the Davig–Leeper "long-run Taylor principle" for `N` regimes
and coefficients of any sign): every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P` is `< 1`. -/
def GenCondition (T : TransitionN N) (φ : Fin N → ℝ) : Prop :=
  (∀ i, φ i ≠ 0) ∧ specRad (absM T φ) < 1

/-- Cochrane (2023), p. 523: the naive generalisation, the spectral radius of `Φ⁻¹P` itself
`< 1` (necessary, `naive_necessary`, but not sufficient, `naive_not_sufficient`). -/
def NaiveCondition (T : TransitionN N) (φ : Fin N → ℝ) : Prop :=
  (∀ i, φ i ≠ 0) ∧ specRad (sgnM T φ) < 1

/-! ### Spectral tools -/

/-- Cochrane (2023), p. 523 (Gelfand's formula): if the spectral radius of a complex matrix is
`< 1`, the entries of its powers are absolutely summable. -/
theorem summable_entry_of_lt {A : Matrix (Fin N) (Fin N) ℂ} (h : spectralRadius ℂ A < 1)
    (i j : Fin N) : Summable (fun k => ‖(A ^ k) i j‖) := by
  let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  obtain ⟨θ, hρθ, hθ1⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
  have hθ1' : (θ : ℝ) < 1 := by exact_mod_cast hθ1
  have hg := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius A
  have hev : ∀ᶠ n : ℕ in atTop, (‖A ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) < θ :=
    hg.eventually (gt_mem_nhds hρθ)
  have hev2 : ∀ᶠ n : ℕ in atTop, ‖(A ^ n) i j‖ ≤ (θ : ℝ) ^ n := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 : (‖A ^ n‖₊ : ℝ≥0∞) < (θ : ℝ≥0∞) ^ n := by
      have := ENNReal.rpow_lt_rpow hn (show (0 : ℝ) < n from hnpos)
      rwa [← ENNReal.rpow_mul, one_div_mul_cancel hnpos.ne', ENNReal.rpow_one,
        ENNReal.rpow_natCast] at this
    have h2 : ‖A ^ n‖₊ < θ ^ n := by exact_mod_cast h1
    have h3 : ‖A ^ n‖ < (θ : ℝ) ^ n := by exact_mod_cast h2
    have hentry : ‖(A ^ n) i j‖ ≤ ‖A ^ n‖ := by
      rw [← coe_nnnorm, ← coe_nnnorm, NNReal.coe_le_coe, Matrix.linfty_opNNNorm_def]
      refine le_trans ?_ (Finset.le_sup (f := fun i : Fin N => ∑ j : Fin N, ‖(A ^ n) i j‖₊)
        (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => ‖(A ^ n) i j‖₊) (fun _ _ => by positivity)
        (Finset.mem_univ j)
    exact hentry.trans h3.le
  exact summable_of_isBigO_nat (summable_geometric_of_lt_one θ.2 hθ1')
    (Asymptotics.IsBigO.of_bound 1 (by
      filter_upwards [hev2] with n hn
      rw [one_mul, norm_norm, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg θ.2 n)]
      exact hn))

/-- Cochrane (2023), p. 523: powers commute with viewing a real matrix over `ℂ`. -/
theorem map_pow_ofReal (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) :
    (A ^ k).map Complex.ofReal = (A.map Complex.ofReal) ^ k := by
  exact map_pow (Complex.ofRealHom.mapMatrix (m := Fin N)) A k

/-- Cochrane (2023), p. 523: if the spectral radius of a real matrix is `< 1`, the entries of its
powers are absolutely summable. -/
theorem summable_abs_pow_entry {A : Matrix (Fin N) (Fin N) ℝ} (h : specRad A < 1) (i j : Fin N) :
    Summable (fun k => |(A ^ k) i j|) := by
  have hs := summable_entry_of_lt h i j
  refine hs.congr fun k => ?_
  rw [← map_pow_ofReal, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]

/-- Cochrane (2023), p. 523: an eigenvalue of a complex matrix is bounded by the spectral
radius. -/
theorem norm_le_spectralRadius {A : Matrix (Fin N) (Fin N) ℂ} {z : ℂ} {v : Fin N → ℂ}
    (hv : v ≠ 0) (hAv : A *ᵥ v = z • v) : (‖z‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ A := by
  have hz : z ∈ spectrum ℂ A := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, hAv, sub_self]
  rw [spectralRadius_eq_of_unital]
  exact le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ A) => (‖k‖₊ : ℝ≥0∞)) z hz

/-- Cochrane (2023), p. 523: if the spectral radius of a complex matrix is not `< 1`, it has an
eigenvector whose eigenvalue has modulus `≥ 1`. -/
theorem exists_eigen_of_not_lt {A : Matrix (Fin N) (Fin N) ℂ} (h : ¬ spectralRadius ℂ A < 1) :
    ∃ (z : ℂ) (v : Fin N → ℂ), 1 ≤ ‖z‖ ∧ v ≠ 0 ∧ A *ᵥ v = z • v := by
  let _ : NormedRing (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin N) (Fin N) ℂ) := Matrix.linftyOpNormedAlgebra
  rcases (spectrum ℂ A).eq_empty_or_nonempty with he | hne
  · exfalso
    apply h
    rw [spectralRadius_eq_of_unital, he]
    simp
  · obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hne
    have hz1 : (1 : ℝ≥0∞) ≤ ‖z‖₊ := by rw [hzr]; exact not_lt.1 h
    have hz1' : 1 ≤ ‖z‖ := by
      have : (1 : ℝ≥0) ≤ ‖z‖₊ := by exact_mod_cast hz1
      exact_mod_cast this
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      ← Matrix.exists_mulVec_eq_zero_iff] at hz
    obtain ⟨v, hv, hzv⟩ := hz
    refine ⟨z, v, hz1', hv, ?_⟩
    rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, sub_eq_zero] at hzv
    exact hzv.symm

/-- Cochrane (2023), p. 523 (the backward recursion `x_t = A x_{t+1}`): if the spectral radius of
a real matrix `A` is not `< 1`, there is a bounded real sequence `x_t` with `x_t = A x_{t+1}` and
`x_0 ≠ 0` — built as `x_t = Re(z^{−t} v)` from an eigenvector `Av = zv`, `|z| ≥ 1`. -/
theorem exists_bdd_backward {A : Matrix (Fin N) (Fin N) ℝ} (h : ¬ specRad A < 1) :
    ∃ x : ℕ → Fin N → ℝ, (∀ t, x t = A *ᵥ x (t + 1)) ∧ (∃ B, ∀ t i, |x t i| ≤ B) ∧
      ∃ i₀, x 0 i₀ ≠ 0 := by
  obtain ⟨z, v, hz1, hv, hAv⟩ := exists_eigen_of_not_lt h
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, v i₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  have hz0 : z ≠ 0 := by
    intro hz; rw [hz, norm_zero] at hz1; linarith
  set w : Fin N → ℂ := (starRingEnd ℂ) (v i₀) • v with hw
  have hAw : (A.map Complex.ofReal) *ᵥ w = z • w := by
    rw [hw, Matrix.mulVec_smul, hAv, smul_comm]
  have hw0 : (w i₀).re ≠ 0 := by
    simp only [hw, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact (Complex.normSq_pos.2 hi₀).ne'
  refine ⟨fun t i => ((z⁻¹) ^ t * w i).re, ?_, ⟨∑ i, ‖w i‖, ?_⟩, i₀, ?_⟩
  · intro t
    funext i
    have hrow := congrFun hAw i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at hrow
    simp only [Matrix.mulVec, dotProduct]
    have key : ∑ j, A i j * ((z⁻¹) ^ (t + 1) * w j).re =
        ((z⁻¹) ^ (t + 1) * ∑ j, (A i j : ℂ) * w j).re := by
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (z⁻¹) ^ (t + 1) * ((A i j : ℂ) * w j) = (A i j : ℂ) * ((z⁻¹) ^ (t + 1) * w j)
        by ring, Complex.re_ofReal_mul]
    rw [key, hrow, pow_succ]
    congr 1
    field_simp
  · intro t i
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, norm_inv]
    have hle : ‖z‖⁻¹ ^ t ≤ 1 :=
      pow_le_one₀ (inv_nonneg.2 (norm_nonneg _)) (inv_le_one_of_one_le₀ hz1)
    calc ‖z‖⁻¹ ^ t * ‖w i‖ ≤ 1 * ‖w i‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ = ‖w i‖ := one_mul _
      _ ≤ ∑ i, ‖w i‖ := Finset.single_le_sum (f := fun i => ‖w i‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ i)
  · simpa using hw0

/-- Cochrane (2023), p. 523: every eigenvalue of a complex matrix comes with an eigenvector. -/
theorem eigen_of_mem_spectrum {A : Matrix (Fin N) (Fin N) ℂ} {z : ℂ} (hz : z ∈ spectrum ℂ A) :
    ∃ v : Fin N → ℂ, v ≠ 0 ∧ A *ᵥ v = z • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff] at hz
  obtain ⟨v, hv, hzv⟩ := hz
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
    Matrix.one_mulVec, sub_eq_zero] at hzv
  exact hzv.symm

/-- Cochrane (2023), p. 523: if every complex eigenvalue of a real matrix has modulus at most `c`,
its spectral radius is at most `c`. -/
theorem specRad_le_of_eigen {A : Matrix (Fin N) (Fin N) ℝ} {c : ℝ≥0}
    (h : ∀ (z : ℂ) (v : Fin N → ℂ), v ≠ 0 → (A.map Complex.ofReal) *ᵥ v = z • v → ‖z‖₊ ≤ c) :
    specRad A ≤ c := by
  unfold specRad
  rw [spectralRadius_eq_of_unital]
  refine iSup₂_le fun z hz => ?_
  obtain ⟨v, hv, hAv⟩ := eigen_of_mem_spectrum hz
  exact_mod_cast h z v hv hAv

/-! ### The sign of a coefficient and of a history -/

/-- Cochrane (2023), p. 523: the sign `sgn a = 1` if `a ≥ 0`, `−1` otherwise. -/
noncomputable def sgn (a : ℝ) : ℝ := if 0 ≤ a then 1 else -1

/-- Cochrane (2023), p. 523: `sgn a · |a| = a`. -/
theorem sgn_mul_abs (a : ℝ) : sgn a * |a| = a := by
  unfold sgn
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.1 h)]; ring

/-- Cochrane (2023), p. 523: `|sgn a| = 1`. -/
theorem abs_sgn (a : ℝ) : |sgn a| = 1 := by
  unfold sgn; split_ifs <;> simp

/-- Cochrane (2023), p. 523: the sign of a regime history, `s(h) = ∏_{l ∈ h} sgn φ_l`. -/
noncomputable def histSign (φ : Fin N → ℝ) (h : List (Fin N)) : ℝ :=
  (h.map fun l => sgn (φ l)).prod

/-- Cochrane (2023), p. 523: `s(i :: h) = sgn φ_i · s(h)`. -/
theorem histSign_cons (φ : Fin N → ℝ) (i : Fin N) (h : List (Fin N)) :
    histSign φ (i :: h) = sgn (φ i) * histSign φ h := by
  simp [histSign]

/-- Cochrane (2023), p. 523: `|s(h)| = 1`. -/
theorem abs_histSign (φ : Fin N → ℝ) (h : List (Fin N)) : |histSign φ h| = 1 := by
  induction h with
  | nil => simp [histSign]
  | cons i h ih => rw [histSign_cons, abs_mul, abs_sgn, ih, one_mul]

/-! ### Row identities -/

/-- Cochrane (2023), p. 523: `∑_j P_{ij} g_j = |φ_i| ∑_j (|Φ|⁻¹P)_{ij} g_j` when `φ_i ≠ 0`. -/
theorem row_absM (T : TransitionN N) {φ : Fin N → ℝ} {i : Fin N} (hφ : φ i ≠ 0)
    (g : Fin N → ℝ) : ∑ j, T.P i j * g j = |φ i| * ∑ j, absM T φ i j * g j := by
  have h0 : |φ i| ≠ 0 := abs_ne_zero.2 hφ
  simp only [absM, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- Cochrane (2023), p. 523: `∑_j P_{ij} g_j = φ_i ∑_j (Φ⁻¹P)_{ij} g_j` when `φ_i ≠ 0`. -/
theorem row_sgnM (T : TransitionN N) {φ : Fin N → ℝ} {i : Fin N} (hφ : φ i ≠ 0)
    (g : Fin N → ℝ) : ∑ j, T.P i j * g j = φ i * ∑ j, sgnM T φ i j * g j := by
  simp only [sgnM, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- Cochrane (2023), p. 523: `∑_l (A^{k+1})_{il} c_l = ∑_j A_{ij} ∑_l (A^k)_{jl} c_l`. -/
theorem sum_pow_succ (A : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) (i : Fin N) (c : Fin N → ℝ) :
    ∑ l, (A ^ (k + 1)) i l * c l = ∑ j, A i j * ∑ l, (A ^ k) j l * c l := by
  simp only [pow_succ', Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ### Indeterminacy -/

/-- Cochrane (2023), pp. 522–523: a nonzero bounded solution of the homogeneous model rules out
determinacy. -/
theorem not_determinate_of_homog {T : TransitionN N} {φ : Fin N → ℝ}
    (h : ∃ e, Solves T φ 0 e ∧ BoundedFn e ∧ e ≠ 0) : ¬ Determinate T φ := by
  intro hd
  obtain ⟨e, he, heb, hne⟩ := h
  obtain ⟨π, _, huniq⟩ := hd 0 ⟨0, fun n => by simp⟩
  have h0 : (0 : NodeN N → ℝ) = π :=
    huniq 0 ⟨fun i h => by simp, ⟨0, fun n => by simp⟩⟩
  exact hne ((huniq e ⟨he, heb⟩).trans h0.symm)

/-- Cochrane (2023), p. 523 (**zero coefficients**): if `φ_i = 0` the date-`0` value of inflation
in regime `i` enters no equation, so `π = 1{node = (i, [])}` is a nonzero bounded solution of the
homogeneous model. -/
theorem zero_coeff_homog (T : TransitionN N) {φ : Fin N → ℝ} {i : Fin N} (hφ : φ i = 0) :
    ∃ e, Solves T φ 0 e ∧ BoundedFn e ∧ e ≠ 0 := by
  classical
  refine ⟨fun n => if n = (i, []) then 1 else 0, ?_, ⟨1, fun n => ?_⟩, ?_⟩
  · intro k h
    have hl : ∀ j, ((j, k :: h) : NodeN N) ≠ (i, []) := fun j hj => by
      simp at hj
    simp only [hl, ↓reduceIte, mul_zero, Finset.sum_const_zero, Pi.zero_apply, add_zero]
    by_cases hk : ((k, h) : NodeN N) = (i, [])
    · simp only [hk, ↓reduceIte, mul_one]
      rw [Prod.mk.injEq] at hk
      rw [hk.1, hφ]
    · simp [hk]
  · change |(if n = (i, []) then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> simp
  · intro h0
    have := congrFun h0 (i, [])
    simp at this

/-- Cochrane (2023), p. 523 (**zero coefficients**): a regime with `φ_i = 0` makes the model
indeterminate. -/
theorem zero_coeff_indeterminate (T : TransitionN N) {φ : Fin N → ℝ} {i : Fin N}
    (hφ : φ i = 0) : ¬ Determinate T φ :=
  not_determinate_of_homog (zero_coeff_homog T hφ)

/-- Cochrane (2023), pp. 522–523 (**necessity, any signs**): if every `φ_i ≠ 0` but the spectral
radius of `|Φ|⁻¹P` is not `< 1`, the sign-twisted process `π(i, h) = s(h) x_{|h|}(i)` with
`x_t = |Φ|⁻¹P x_{t+1}` is a nonzero bounded solution of the homogeneous model. -/
theorem homog_nonzero_of_not (T : TransitionN N) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    (h : ¬ specRad (absM T φ) < 1) : ∃ e, Solves T φ 0 e ∧ BoundedFn e ∧ e ≠ 0 := by
  obtain ⟨x, hx, ⟨B, hB⟩, i₀, hi₀⟩ := exists_bdd_backward h
  refine ⟨fun n => histSign φ n.2 * x n.2.length n.1, ?_, ⟨B, fun n => ?_⟩, ?_⟩
  · intro i h
    have hrow : ∑ j, T.P i j * x (h.length + 1) j = |φ i| * x h.length i := by
      rw [row_absM T (hφ i), hx h.length]
      rfl
    simp only [List.length_cons, Pi.zero_apply, add_zero]
    calc ∑ j, T.P i j * (histSign φ (i :: h) * x (h.length + 1) j)
        = histSign φ (i :: h) * ∑ j, T.P i j * x (h.length + 1) j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = φ i * (histSign φ h * x h.length i) := by
          rw [hrow, histSign_cons]
          linear_combination (histSign φ h * x h.length i) * sgn_mul_abs (φ i)
  · rw [abs_mul, abs_histSign, one_mul]
    exact hB _ _
  · intro h0
    have := congrFun h0 (i₀, [])
    simp only [histSign, List.map_nil, List.prod_nil, List.length_nil, one_mul,
      Pi.zero_apply] at this
    exact hi₀ this

/-- Cochrane (2023), p. 523 (**the naive condition is necessary**): if every `φ_i ≠ 0` but the
spectral radius of `Φ⁻¹P` is not `< 1`, `π(i, h) = x_{|h|}(i)` with `x_t = Φ⁻¹P x_{t+1}` is a
nonzero bounded solution of the homogeneous model. -/
theorem homog_nonzero_of_not_naive (T : TransitionN N) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    (h : ¬ specRad (sgnM T φ) < 1) : ∃ e, Solves T φ 0 e ∧ BoundedFn e ∧ e ≠ 0 := by
  obtain ⟨x, hx, ⟨B, hB⟩, i₀, hi₀⟩ := exists_bdd_backward h
  refine ⟨fun n => x n.2.length n.1, ?_, ⟨B, fun n => hB _ _⟩, ?_⟩
  · intro i h
    simp only [List.length_cons, Pi.zero_apply, add_zero]
    rw [row_sgnM T (hφ i), hx h.length]
    rfl
  · intro h0
    have := congrFun h0 (i₀, [])
    exact hi₀ this

/-! ### Uniqueness and existence under the condition -/

/-- Cochrane (2023), p. 523 (iterating the expectational recursion): a bounded solution of the
homogeneous model satisfies `|π(i, h)| ≤ B ∑_j ((|Φ|⁻¹P)^k)_{ij}` for every `k`. -/
theorem abs_le_pow_bound (T : TransitionN N) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    {e : NodeN N → ℝ} (he : Solves T φ 0 e) {B : ℝ} (hB : ∀ n, |e n| ≤ B) (k : ℕ) :
    ∀ i h, |e (i, h)| ≤ B * ∑ j, (absM T φ ^ k) i j := by
  induction k with
  | zero =>
    intro i h
    simp only [pow_zero, Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      mul_one]
    exact hB _
  | succ k ih =>
    intro i h
    have hpos : 0 < |φ i| := abs_pos.2 (hφ i)
    have heq : φ i * e (i, h) = ∑ j, T.P i j * e (j, i :: h) := by
      have := he i h; simp only [Pi.zero_apply, add_zero] at this; linarith
    have habs : |φ i| * |e (i, h)| ≤ ∑ j, T.P i j * |e (j, i :: h)| := by
      rw [← abs_mul, heq]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [abs_mul, abs_of_nonneg (T.nonneg i j)]
    have hstep : ∑ j, T.P i j * |e (j, i :: h)| ≤
        ∑ j, T.P i j * (B * ∑ l, (absM T φ ^ k) j l) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j (i :: h)) (T.nonneg i j)
    have hval : ∑ j, T.P i j * (B * ∑ l, (absM T φ ^ k) j l) =
        |φ i| * (B * ∑ l, (absM T φ ^ (k + 1)) i l) := by
      have hs := sum_pow_succ (absM T φ) k i (fun _ => 1)
      simp only [mul_one] at hs
      rw [row_absM T (hφ i), hs]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := habs.trans (hstep.trans (le_of_eq hval))
    exact le_of_mul_le_mul_left this hpos

/-- Cochrane (2023), pp. 522–523: under the condition the homogeneous model has no bounded
solution other than zero. -/
theorem homog_eq_zero (T : TransitionN N) {φ : Fin N → ℝ} (hc : GenCondition T φ)
    {e : NodeN N → ℝ} (he : Solves T φ 0 e) (hb : BoundedFn e) : e = 0 := by
  obtain ⟨B, hB⟩ := hb
  funext n
  obtain ⟨i, h⟩ := n
  have hlim : Tendsto (fun k => B * ∑ j, (absM T φ ^ k) i j) atTop (𝓝 0) := by
    have hj : ∀ j ∈ Finset.univ, Tendsto (fun k => (absM T φ ^ k) i j) atTop (𝓝 0) :=
      fun j _ => (summable_abs_pow_entry hc.2 i j).of_abs.tendsto_atTop_zero
    simpa using (tendsto_finsetSum Finset.univ hj).const_mul B
  have hle : |e (i, h)| ≤ 0 :=
    ge_of_tendsto' hlim fun k => abs_le_pow_bound T hc.1 he hB k i h
  simpa using abs_nonpos_iff.mp hle

/-- Cochrane (2023), p. 523 (the forward solution): `Δ_0 = −u/φ`,
`Δ_{k+1}(i, h) = ∑_j P_{ij} Δ_k(j, i :: h)/φ_i`. -/
noncomputable def fwdTerm (T : TransitionN N) (φ : Fin N → ℝ) (u : NodeN N → ℝ) :
    ℕ → NodeN N → ℝ
  | 0, n => -u n / φ n.1
  | k + 1, n => (∑ j, T.P n.1 j * fwdTerm T φ u k (j, n.1 :: n.2)) / φ n.1

/-- Cochrane (2023), p. 523: the forward solution `π = ∑_k Δ_k`. -/
noncomputable def fwdSol (T : TransitionN N) (φ : Fin N → ℝ) (u : NodeN N → ℝ) (n : NodeN N) :
    ℝ :=
  ∑' k, fwdTerm T φ u k n

/-- Cochrane (2023), p. 523: `|Δ_k(i, h)| ≤ U ∑_l ((|Φ|⁻¹P)^k)_{il}/|φ_l|`. -/
theorem fwdTerm_bound (T : TransitionN N) {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0)
    {u : NodeN N → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) (k : ℕ) :
    ∀ i h, |fwdTerm T φ u k (i, h)| ≤ U * ∑ l, (absM T φ ^ k) i l * (1 / |φ l|) := by
  induction k with
  | zero =>
    intro i h
    simp only [fwdTerm, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [abs_div, abs_neg, mul_one_div]
    exact div_le_div_of_nonneg_right (hU _) (abs_nonneg _)
  | succ k ih =>
    intro i h
    have hpos : 0 < |φ i| := abs_pos.2 (hφ i)
    simp only [fwdTerm]
    rw [abs_div, div_le_iff₀ hpos]
    calc |∑ j, T.P i j * fwdTerm T φ u k (j, i :: h)|
        ≤ ∑ j, T.P i j * |fwdTerm T φ u k (j, i :: h)| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (T.nonneg i j)]
      _ ≤ ∑ j, T.P i j * (U * ∑ l, (absM T φ ^ k) j l * (1 / |φ l|)) :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (ih j (i :: h)) (T.nonneg i j)
      _ = (U * ∑ l, (absM T φ ^ (k + 1)) i l * (1 / |φ l|)) * |φ i| := by
          have hs := sum_pow_succ (absM T φ) k i (fun l => 1 / |φ l|)
          rw [row_absM T (hφ i), hs, mul_comm _ (|φ i|)]
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring

/-- Cochrane (2023), p. 523: the dominating sequence for the forward solution is summable under
the condition. -/
theorem summable_bound (T : TransitionN N) {φ : Fin N → ℝ} (hc : GenCondition T φ) (U : ℝ)
    (i : Fin N) : Summable (fun k => U * ∑ l, (absM T φ ^ k) i l * (1 / |φ l|)) :=
  (summable_sum fun l _ =>
    ((summable_abs_pow_entry hc.2 i l).of_abs.mul_right _)).mul_left U

/-- Cochrane (2023), p. 523: the forward-solution terms are summable at every node. -/
theorem fwdTerm_summable (T : TransitionN N) {φ : Fin N → ℝ} (hc : GenCondition T φ)
    {u : NodeN N → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) (n : NodeN N) :
    Summable (fun k => fwdTerm T φ u k n) := by
  obtain ⟨i, h⟩ := n
  exact Summable.of_norm_bounded (summable_bound T hc U i) fun k => by
    rw [Real.norm_eq_abs]; exact fwdTerm_bound T hc.1 hU k i h

/-- Cochrane (2023), pp. 522–523: under the condition the forward solution solves
`E_t π_{t+1} = φ_{S_t} π_t + u_t`. -/
theorem fwdSol_solves (T : TransitionN N) {φ : Fin N → ℝ} (hc : GenCondition T φ)
    {u : NodeN N → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) : Solves T φ u (fwdSol T φ u) := by
  intro i h
  have hs := fun n => fwdTerm_summable T hc hU n
  have hφi := hc.1 i
  have hsplit := (hs (i, h)).tsum_eq_zero_add
  have hA : ∑ j, T.P i j * fwdSol T φ u (j, i :: h) =
      ∑' k, ∑ j, T.P i j * fwdTerm T φ u k (j, i :: h) := by
    simp only [fwdSol]
    rw [Summable.tsum_finsetSum fun j _ => (hs _).mul_left _]
    exact Finset.sum_congr rfl fun j _ => (tsum_mul_left).symm
  have hB : fwdSol T φ u (i, h) = -u (i, h) / φ i +
      (∑' k, ∑ j, T.P i j * fwdTerm T φ u k (j, i :: h)) / φ i := by
    unfold fwdSol
    rw [hsplit, ← tsum_div_const]
    rfl
  rw [hA, hB]
  field_simp
  ring

/-- Cochrane (2023), pp. 522–523: under the condition the forward solution is bounded. -/
theorem fwdSol_bounded (T : TransitionN N) {φ : Fin N → ℝ} (hc : GenCondition T φ)
    {u : NodeN N → ℝ} {U : ℝ} (hU : ∀ n, |u n| ≤ U) : BoundedFn (fwdSol T φ u) := by
  set g : Fin N → ℝ := fun i => ∑' k, U * ∑ l, (absM T φ ^ k) i l * (1 / |φ l|) with hg
  refine ⟨∑ i, |g i|, fun n => ?_⟩
  obtain ⟨i, h⟩ := n
  have h1 : |fwdSol T φ u (i, h)| ≤ g i := by
    unfold fwdSol
    have hsa : Summable (fun k => |fwdTerm T φ u k (i, h)|) :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => fwdTerm_bound T hc.1 hU k i h)
        (summable_bound T hc U i)
    have hn := norm_tsum_le_tsum_norm (f := fun k => fwdTerm T φ u k (i, h))
      (by simpa only [Real.norm_eq_abs] using hsa)
    simp only [Real.norm_eq_abs] at hn
    exact hn.trans (Summable.tsum_le_tsum (fun k => fwdTerm_bound T hc.1 hU k i h) hsa
      (summable_bound T hc U i))
  exact h1.trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun i => |g i|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))

/-- Cochrane (2023), pp. 522–523: the difference of two solutions solves the homogeneous
model. -/
theorem solves_sub (T : TransitionN N) (φ : Fin N → ℝ) {u π₁ π₂ : NodeN N → ℝ}
    (h₁ : Solves T φ u π₁) (h₂ : Solves T φ u π₂) : Solves T φ 0 (π₁ - π₂) := by
  intro i h
  have e1 := h₁ i h
  have e2 := h₂ i h
  simp only [Pi.sub_apply, Pi.zero_apply, mul_sub, Finset.sum_sub_distrib, add_zero]
  linarith

/-! ### The determinacy theorem -/

/-- Cochrane (2023), pp. 522–523 (**Davig–Leeper for `N` regimes and coefficients of any
sign**): the Markov-switching model `E_t π_{t+1} = φ_{S_t} π_t + u_t` has exactly one bounded
equilibrium for every bounded disturbance iff every `φ_i ≠ 0` and the spectral radius of `|Φ|⁻¹P`
is `< 1`. -/
theorem determinate_iff (T : TransitionN N) (φ : Fin N → ℝ) :
    Determinate T φ ↔ GenCondition T φ := by
  constructor
  · intro hd
    by_cases h0 : ∀ i, φ i ≠ 0
    · refine ⟨h0, ?_⟩
      by_contra hns
      exact not_determinate_of_homog (homog_nonzero_of_not T h0 hns) hd
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      exact absurd hd (zero_coeff_indeterminate T hi)
  · intro hc u ⟨U, hU⟩
    refine ⟨fwdSol T φ u, ⟨fwdSol_solves T hc hU, fwdSol_bounded T hc hU⟩, ?_⟩
    rintro π ⟨hπ, hπb⟩
    have hd := solves_sub T φ hπ (fwdSol_solves T hc hU)
    obtain ⟨B1, hB1⟩ := hπb
    obtain ⟨B2, hB2⟩ := fwdSol_bounded T hc hU
    have hzero := homog_eq_zero T hc hd ⟨B1 + B2, fun n => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hB1 n) (hB2 n))⟩
    exact sub_eq_zero.mp hzero

/-- Cochrane (2023), pp. 522–523 (**signs do not matter**): determinacy depends only on the
absolute values `|φ_i|`. -/
theorem determinate_iff_abs (T : TransitionN N) (φ : Fin N → ℝ) :
    Determinate T φ ↔ Determinate T (fun i => |φ i|) := by
  rw [determinate_iff, determinate_iff]
  have hM : absM T (fun i => |φ i|) = absM T φ := by
    ext i j; simp [absM]
  unfold GenCondition
  rw [hM]
  simp only [ne_eq, abs_eq_zero]

/-- Cochrane (2023), pp. 522–523: two coefficient vectors with the same absolute values are
determinate together. -/
theorem determinate_congr_abs (T : TransitionN N) {φ ψ : Fin N → ℝ}
    (h : ∀ i, |φ i| = |ψ i|) : Determinate T φ ↔ Determinate T ψ := by
  rw [determinate_iff_abs, determinate_iff_abs T ψ]
  simp only [h]

/-- Cochrane (2023), p. 523 (**the naive condition is necessary**): determinacy implies that every
`φ_i ≠ 0` and that the spectral radius of `Φ⁻¹P` is `< 1`. -/
theorem naive_necessary (T : TransitionN N) {φ : Fin N → ℝ} (hd : Determinate T φ) :
    NaiveCondition T φ := by
  have h0 := ((determinate_iff T φ).1 hd).1
  refine ⟨h0, ?_⟩
  by_contra hns
  exact not_determinate_of_homog (homog_nonzero_of_not_naive T h0 hns) hd

/-- Cochrane (2023), p. 523 (**zero coefficients, Lean's junk inverse is wrong**): with one
regime, `P = 1` and `φ = 0`, the junk matrix `|Φ|⁻¹P` (computed with `1/0 = 0`) has spectral
radius `0 < 1`, yet the model is indeterminate — `φ_i ≠ 0` must be part of the condition. -/
theorem junk_inverse_wrong :
    specRad (absM (⟨fun _ _ => 1, fun _ _ => zero_le_one, fun _ => by simp⟩ : TransitionN 1)
      (fun _ => 0)) < 1 ∧
    ¬ Determinate (⟨fun _ _ => 1, fun _ _ => zero_le_one, fun _ => by simp⟩ : TransitionN 1)
      (fun _ => 0) := by
  refine ⟨?_, zero_coeff_indeterminate _ (i := 0) rfl⟩
  have h0 : absM (⟨fun _ _ => 1, fun _ _ => zero_le_one, fun _ => by simp⟩ : TransitionN 1)
      (fun _ => 0) = 0 := by
    ext i j; simp [absM]
  rw [h0]
  simp [specRad]

/-! ### Two regimes: the special case `N = 2` and the Davig–Leeper formula -/

/-- Cochrane (2023), p. 522: a two-state transition matrix of `MarkovRegimes` as an `N = 2`
transition matrix. -/
def ofTwo (T : MarkovRegimes.Transition) : TransitionN 2 := ⟨T.P, T.nonneg, T.rowSum⟩

/-- Cochrane (2023), pp. 522–523 (**link**): for `N = 2` the model and its determinacy are
exactly those of `MarkovRegimes` (the regime trees coincide). -/
theorem determinate_iff_old (T : MarkovRegimes.Transition) (φ : Fin 2 → ℝ) :
    Determinate (ofTwo T) φ ↔ ∀ u, MarkovRegimes.BoundedFn u →
      ∃! π, MarkovRegimes.Solves T φ u π ∧ MarkovRegimes.BoundedFn π :=
  Iff.rfl

/-- Cochrane (2023), p. 523: for `φ > 0`, `|Φ|⁻¹P` is the matrix `M = Φ⁻¹P` of `MarkovRegimes`. -/
theorem absM_ofTwo (T : MarkovRegimes.Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    absM (ofTwo T) φ = MarkovRegimes.regM T φ := by
  ext i j
  simp [absM, MarkovRegimes.regM, ofTwo, abs_of_pos (hφ i)]

/-- Cochrane (2023), pp. 522–523 (**the two-regime result recovered**): for two regimes with
`φ_0, φ_1 > 0`, Davig and Leeper's condition `(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1`,
`p_00/φ_0 + p_11/φ_1 < 2` is the general condition. -/
theorem dl_iff_genCondition (T : MarkovRegimes.Transition) {φ : Fin 2 → ℝ}
    (hφ : ∀ i, 0 < φ i) : MarkovRegimes.DLCondition T φ ↔ GenCondition (ofTwo T) φ :=
  (MarkovRegimes.determinate_iff T hφ).symm.trans
    ((determinate_iff_old T φ).symm.trans (determinate_iff _ φ))

/-- Cochrane (2023), p. 523: for `φ > 0` the `2 × 2` Schur–Cohn condition of `MarkovRegimes`
is the spectral-radius condition. -/
theorem schur_iff_specRad (T : MarkovRegimes.Transition) {φ : Fin 2 → ℝ} (hφ : ∀ i, 0 < φ i) :
    SchurStable (tr2 (MarkovRegimes.regM T φ)) (det2 (MarkovRegimes.regM T φ)) ↔
      specRad (MarkovRegimes.regM T φ) < 1 := by
  rw [← MarkovRegimes.dl_iff_schur T hφ, dl_iff_genCondition T hφ, GenCondition,
    absM_ofTwo T hφ]
  exact ⟨fun h => h.2, fun h => ⟨fun i => (hφ i).ne', h⟩⟩

/-- Cochrane (2023), pp. 522–523 (**the corrected Davig–Leeper formula**): with two regimes and
coefficients of any sign, the model is determinate iff `φ_0, φ_1 ≠ 0` and the Davig–Leeper formula
holds for `|φ_0|, |φ_1|`. -/
theorem dl_corrected (T : MarkovRegimes.Transition) (φ : Fin 2 → ℝ) :
    Determinate (ofTwo T) φ ↔
      (∀ i, φ i ≠ 0) ∧ MarkovRegimes.DLCondition T (fun i => |φ i|) := by
  by_cases h0 : ∀ i, φ i ≠ 0
  · rw [determinate_iff_abs, determinate_iff_old,
      MarkovRegimes.determinate_iff T (fun i => abs_pos.2 (h0 i))]
    exact ⟨fun h => ⟨h0, h⟩, fun h => h.2⟩
  · push Not at h0
    obtain ⟨i, hi⟩ := h0
    exact ⟨fun h => absurd h (zero_coeff_indeterminate _ hi), fun h => absurd hi (h.1 i)⟩

/-- Cochrane (2023), p. 523 (example): a chain with `p_00 = 0.9`, `p_11 = 0.5`. -/
noncomputable def egDL : MarkovRegimes.Transition where
  P := ![![9 / 10, 1 / 10], ![1 / 2, 1 / 2]]
  nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num
  rowSum := by intro i; fin_cases i <;> simp [Fin.sum_univ_two] <;> norm_num

/-- Cochrane (2023), p. 523 (example): i.i.d. regimes with `p_ij = ½`. -/
noncomputable def egHalf : MarkovRegimes.Transition where
  P := fun _ _ => 1 / 2
  nonneg := by intro i j; norm_num
  rowSum := by intro i; simp

/-- Cochrane (2023), pp. 522–523 (**the Davig–Leeper formula fails with a negative
coefficient**): with `p_00 = 0.9`, `p_11 = 0.5` and `φ = (½, −½)` the formula
`(1 − φ_1)p_00 + (1 − φ_0)p_11 + φ_0φ_1 > 1`, `p_00/φ_0 + p_11/φ_1 < 2` holds, but the model is
indeterminate (both regimes have `|φ_i| = ½ < 1`). -/
theorem dl_formula_fails_negative :
    MarkovRegimes.DLCondition egDL ![1 / 2, -1 / 2] ∧
      ¬ Determinate (ofTwo egDL) ![1 / 2, -1 / 2] := by
  refine ⟨?_, ?_⟩
  · simp only [MarkovRegimes.DLCondition, egDL]
    norm_num
  · rw [dl_corrected]
    rintro ⟨-, h⟩
    simp only [MarkovRegimes.DLCondition, egDL] at h
    norm_num at h

/-- Cochrane (2023), p. 523 (**a negative regime that is still determinate**): with the
short-lived passive chain `p_00 = 0.9`, `p_11 = 0.4` and `φ = (2, −½)` the model is
determinate. -/
theorem negative_regime_determinate :
    Determinate (ofTwo MarkovRegimes.egShortPassive) ![2, -1 / 2] := by
  rw [dl_corrected]
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
  simp only [MarkovRegimes.DLCondition, MarkovRegimes.egShortPassive]
  norm_num

/-- Cochrane (2023), p. 523 (**sign changes destroy the naive condition**): with `p_ij = ½` and
`φ = (½, −½)`, `Φ⁻¹P` is nilpotent (spectral radius `0`), so the naive condition holds, but the
model is indeterminate (`|Φ|⁻¹P = 2P` has spectral radius `2`). -/
theorem naive_not_sufficient :
    NaiveCondition (ofTwo egHalf) ![1 / 2, -1 / 2] ∧
      ¬ Determinate (ofTwo egHalf) ![1 / 2, -1 / 2] := by
  refine ⟨⟨fun i => by fin_cases i <;> norm_num, ?_⟩, ?_⟩
  · have hMM : (sgnM (ofTwo egHalf) ![1 / 2, -1 / 2]).map Complex.ofReal *
        (sgnM (ofTwo egHalf) ![1 / 2, -1 / 2]).map Complex.ofReal = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sgnM, ofTwo, egHalf, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
    refine lt_of_le_of_lt (specRad_le_of_eigen (c := 0) fun z v hv hAv => ?_) (by simp)
    have h2 : (z * z) • v = 0 := by
      rw [mul_smul, ← hAv, ← Matrix.mulVec_smul, ← hAv, Matrix.mulVec_mulVec, hMM,
        Matrix.zero_mulVec]
    rcases smul_eq_zero.1 h2 with hz | hv'
    · simp [mul_self_eq_zero.1 hz]
    · exact absurd hv' hv
  · rw [dl_corrected]
    rintro ⟨-, h⟩
    simp only [MarkovRegimes.DLCondition, egHalf] at h
    norm_num at h

/-! ### I.i.d. regimes -/

/-- Cochrane (2023), p. 523: i.i.d. regimes, `P_{ij} = q_j`. -/
def iidT (q : Fin N → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1) : TransitionN N :=
  ⟨fun _ j => q j, fun _ j => hq0 j, fun _ => hq1⟩

/-- Cochrane (2023), p. 523: with i.i.d. regimes and `φ_i ≠ 0`, the spectral radius of
`|Φ|⁻¹P` is `< 1` iff `∑_j q_j/|φ_j| < 1` (`|Φ|⁻¹P` has rank one; its nonzero eigenvalue is
`∑_j q_j/|φ_j|`). -/
theorem iid_specRad_lt_iff (q : Fin N → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    {φ : Fin N → ℝ} (hφ : ∀ i, φ i ≠ 0) :
    specRad (absM (iidT q hq0 hq1) φ) < 1 ↔ ∑ j, q j / |φ j| < 1 := by
  set c : ℝ := ∑ j, q j / |φ j| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun j _ => div_nonneg (hq0 j) (abs_nonneg _)
  have hrow : ∀ (v : Fin N → ℂ) (i : Fin N),
      ((absM (iidT q hq0 hq1) φ).map Complex.ofReal *ᵥ v) i =
        (∑ j, (q j : ℂ) * v j) / ((|φ i| : ℝ) : ℂ) := by
    intro v i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, absM, iidT, Matrix.of_apply,
      Complex.ofReal_div, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hφc : ∀ i, ((|φ i| : ℝ) : ℂ) ≠ 0 := fun i => by exact_mod_cast abs_ne_zero.2 (hφ i)
  constructor
  · intro h
    by_contra hge
    push Not at hge
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := fun j => q j / |φ j|) (by rw [← hc]; linarith)
    set d : Fin N → ℂ := fun i => 1 / ((|φ i| : ℝ) : ℂ) with hd
    have hdv : (absM (iidT q hq0 hq1) φ).map Complex.ofReal *ᵥ d = (c : ℂ) • d := by
      funext i
      rw [hrow, Pi.smul_apply, smul_eq_mul, hc]
      push_cast
      simp only [hd]
      rw [div_eq_mul_one_div _ ((|φ i| : ℝ) : ℂ)]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by ring
    have hd0 : d ≠ 0 := by
      intro h0
      have := congrFun h0 j₀
      simp only [hd, Pi.zero_apply, one_div, inv_eq_zero] at this
      exact hφc j₀ this
    have hle := norm_le_spectralRadius hd0 hdv
    have hc1 : (1 : ℝ≥0∞) ≤ ‖(c : ℂ)‖₊ := by
      have h1 : (1 : ℝ≥0) ≤ ‖(c : ℂ)‖₊ := by
        rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hc0]
        exact hge
      exact_mod_cast h1
    exact absurd (hc1.trans hle) (not_le.2 h)
  · intro h
    refine lt_of_le_of_lt (specRad_le_of_eigen (c := c.toNNReal) fun z v hv hAv => ?_)
      (ENNReal.coe_lt_one_iff.2 (Real.toNNReal_lt_one.2 h))
    set s : ℂ := ∑ j, (q j : ℂ) * v j with hs
    have hzv : ∀ i, z * v i = s / ((|φ i| : ℝ) : ℂ) := fun i => by
      rw [← hrow, hAv, Pi.smul_apply, smul_eq_mul]
    have hzs : z * s = s * c := by
      rw [hs, Finset.mul_sum, hc]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, hzv j]
      ring
    obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv (funext hcon)
    by_cases hs0 : s = 0
    · have := hzv i₀
      rw [hs0, zero_div] at this
      rcases mul_eq_zero.1 this with hz | hz
      · simp [hz]
      · exact absurd hz hi₀
    · have hzc : z = c := by
        have := hzs
        rw [mul_comm s] at this
        exact mul_right_cancel₀ hs0 this
      rw [hzc, ← NNReal.coe_le_coe, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hc0, Real.coe_toNNReal _ hc0]

/-- Cochrane (2023), pp. 522–523 (**i.i.d. regimes**): with i.i.d. regimes the model is
determinate iff every `φ_i ≠ 0` and `∑_j q_j/|φ_j| < 1` — the probability-weighted harmonic mean
of `|φ_i|` exceeds one. -/
theorem iid_determinate_iff (q : Fin N → ℝ) (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    (φ : Fin N → ℝ) :
    Determinate (iidT q hq0 hq1) φ ↔ (∀ i, φ i ≠ 0) ∧ ∑ j, q j / |φ j| < 1 := by
  rw [determinate_iff]
  exact ⟨fun h => ⟨h.1, (iid_specRad_lt_iff q hq0 hq1 h.1).1 h.2⟩,
    fun h => ⟨h.1, (iid_specRad_lt_iff q hq0 hq1 h.1).2 h.2⟩⟩

/-- Cochrane (2023), p. 523 (**three regimes, one negative and one passive**): with three equally
likely i.i.d. regimes and `φ = (4, −4, ½)`, the model is determinate
(`∑_j q_j/|φ_j| = 1/12 + 1/12 + 2/3 = 5/6 < 1`). -/
theorem three_regime_determinate :
    Determinate (iidT (fun _ : Fin 3 => 1 / 3) (fun _ => by norm_num)
      (by simp)) ![4, -4, 1 / 2] := by
  rw [iid_determinate_iff]
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
  simp [Fin.sum_univ_three]
  norm_num

end Cochrane.ObservationalEquivalence.MarkovRegimesGeneral
