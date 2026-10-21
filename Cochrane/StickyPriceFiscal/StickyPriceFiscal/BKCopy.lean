/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.Expectations
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# The general Blanchard–Kahn theorem (copied infrastructure)

Cochrane (2023), Online Appendix A1 §1.9, pp. 573–576 ("solve unstable eigenvalues forward and
stable eigenvalues backward"; Blanchard and Kahn 1980), and Ch. 5 §5.5, p. 148 (the counting of
expectational errors against forward-looking roots). The book uses the Blanchard–Kahn counting
rule without proof; this module supplies the general theorem, restated from the Woodford
Chapter 4 project (`NeoWicksellianFramework.InvariantSplit`, `GeneralBKForward`, `GeneralBK`)
with the namespace renamed and the three modules nested as sub-namespaces. The docstrings keep
the Woodford (2003) citations of the original. The only adaptation to this project's core is
that `GeneralBKForward.fsolves_exists` uses the core `ExpectationSystem.E_tsum` (same statement
as in the Woodford core).

* `InvariantSplit`: complex eigenvalues of a real matrix (`eigs`, `stableCount`, `NoUnit`), the
  bounded-orbit subspace `boundedOrbits`, `finrank_eq_stableCount`, genericity `GenericX`, the
  graph of the stable subspace (`exists_graph`).
* `GeneralBKForward`: forward systems `s_t = K E_t s_{t+1} + w_t` (`fsolves_exists`,
  `fsolves_unique`).
* `GeneralBK`: `Equil`, `Determinate`, and the Blanchard–Kahn theorem `determinate_iff`,
  `determinate_iff_count` (no eigenvalue on the unit circle, exactly `|X|` eigenvalues in the open
  unit disc, genericity), with each failure mode (`nonexist_of_unit`, `mult_of_not_genericX`,
  `nonexist_of_lt`).
-/

namespace Cochrane.StickyPriceFiscal.BKCopy

/-!
# The stable invariant subspace of a real matrix

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 and footnotes 1–2; Blanchard and
Kahn (1980). Linear algebra behind the general Blanchard–Kahn theorem (`GeneralBK`).

For a real square matrix `A` (any finite index type):

* `eigs A`: the complex eigenvalues of `A` with algebraic multiplicity (the roots of the
  characteristic polynomial over `ℂ`), `stableCount A` the number of them in the open unit disc,
  `NoUnit A`: no eigenvalue on the unit circle.
* `boundedOrbits A`: the real subspace of vectors `v` whose orbit `Aᵗ v` is bounded — the real
  stable invariant subspace when `NoUnit A` holds.
* `pow_entry_bound`: eigenvalues in the open disc give geometric decay of the powers (Gelfand's
  formula); `norm_le_one_of_pow_bounded`: bounded powers force eigenvalues in the closed disc.
* `stableCount_le_finrank`: the number of stable eigenvalues (with multiplicity) is at most the
  dimension of `boundedOrbits A` (complex generalised eigenspaces of stable eigenvalues have
  bounded orbits; their real and imaginary parts lie in `boundedOrbits A`).
* `finrank_le_stableCount`, `finrank_eq_stableCount`: with no eigenvalue on the unit circle the
  dimension of `boundedOrbits A` *equals* the number of eigenvalues in the open disc (the
  restriction of `A` to it, `restrict_block`, has a characteristic polynomial dividing that of
  `A` and bounded powers, `exists_restrict_stable`); `boundedOrbits_eq_bot_of_unstable`.
* `tendsto_of_mem_boundedOrbits`: with no eigenvalue on the unit circle every bounded orbit tends
  to `0` — `boundedOrbits A` is the real stable invariant subspace `{v : Aᵗ v → 0}`.

For a split state `Z ⊕ X` (`X` the predetermined coordinates):

* `GenericX A`: `boundedOrbits A` meets `{x = 0}` only in `0` (the genericity condition).
* `exists_graph`: if moreover `dim boundedOrbits A = |X|`, the subspace is the graph of a matrix
  `G : Z × X` (`IsGraph`), so `A [G; I] = [G; I] Λ` with `Λ = A_xz G + A_xx` (`lam`), and with
  `C = A_zz − G A_xz` (`cmat`) the change of variables `ẑ = z − G x` makes `A` block triangular:
  `charpoly A = charpoly C · charpoly Λ` (`charpoly_split`, `eigs_split`).
* `lam_stable`: under `NoUnit`, every eigenvalue of `Λ` lies in the open disc;
  `cmat_unstable`: every eigenvalue of `C` lies outside the closed disc;
  `stableCount_eq_card`: hence exactly `|X|` eigenvalues of `A` lie in the open disc.

The proof of `pow_entry_bound` is restated from `BlanchardKahn.pow_entry_bound` (from the Galí
Chapter 6 project), generalised from `Fin n` to any finite index type.
-/

namespace InvariantSplit

open Polynomial Filter Topology
open scoped Matrix

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Complex eigenvalues of a real matrix -/

/-- Woodford (2003), App. C.1, p. 670: the complex eigenvalues of a real square matrix, with
algebraic multiplicity (the roots of its characteristic polynomial over `ℂ`). -/
noncomputable def eigs (K : Matrix κ κ ℝ) : Multiset ℂ := (K.map Complex.ofReal).charpoly.roots

/-- Woodford (2003), App. C.1, p. 670: the number of eigenvalues (with multiplicity) in the open
unit disc. -/
noncomputable def stableCount (K : Matrix κ κ ℝ) : ℕ :=
  Multiset.card ((eigs K).filter (fun μ => ‖μ‖ < 1))

/-- Woodford (2003), App. C.1, p. 670, fn. 1: no eigenvalue lies on the unit circle. -/
def NoUnit (K : Matrix κ κ ℝ) : Prop := ∀ μ ∈ eigs K, ‖μ‖ ≠ 1

/-- Woodford (2003), App. C.1, p. 670 (tool): `μ` is an eigenvalue iff `det (μ I − K) = 0`. -/
theorem mem_eigs_iff (K : Matrix κ κ ℝ) (μ : ℂ) :
    μ ∈ eigs K ↔ (Matrix.scalar κ μ - K.map Complex.ofReal).det = 0 := by
  rw [eigs, mem_roots (Matrix.charpoly_monic _).ne_zero, IsRoot, Matrix.eval_charpoly]

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvalue has a complex eigenvector. -/
theorem exists_eigvec {K : Matrix κ κ ℝ} {μ : ℂ} (h : μ ∈ eigs K) :
    ∃ c : κ → ℂ, c ≠ 0 ∧ K.map Complex.ofReal *ᵥ c = μ • c := by
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr ((mem_eigs_iff K μ).mp h)
  refine ⟨c, hc0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hc
  rw [← hc]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvalue has a complex left eigenvector. -/
theorem exists_left_eigvec {K : Matrix κ κ ℝ} {μ : ℂ} (h : μ ∈ eigs K) :
    ∃ q : κ → ℂ, q ≠ 0 ∧ q ᵥ* K.map Complex.ofReal = μ • q := by
  obtain ⟨q, hq0, hq⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr ((mem_eigs_iff K μ).mp h)
  refine ⟨q, hq0, ?_⟩
  rw [Matrix.vecMul_sub, sub_eq_zero] at hq
  rw [← hq]
  funext i
  simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]

/-- Woodford (2003), App. C.1, p. 670 (tool): a complex eigenvector gives an eigenvalue. -/
theorem mem_eigs_of_eigvec {K : Matrix κ κ ℝ} {μ : ℂ} {c : κ → ℂ} (hc0 : c ≠ 0)
    (hc : K.map Complex.ofReal *ᵥ c = μ • c) : μ ∈ eigs K := by
  rw [mem_eigs_iff, ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨c, hc0, ?_⟩
  rw [Matrix.sub_mulVec, hc]
  funext i
  simp [Matrix.scalar_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvector of `M` is one of every power,
`Mᵗ c = μᵗ c`. -/
theorem pow_mulVec_eigvec {R : Type*} [CommRing R] {M : Matrix κ κ R} {μ : R} {c : κ → R}
    (hc : M *ᵥ c = μ • c) (t : ℕ) : M ^ t *ᵥ c = μ ^ t • c := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- Woodford (2003), App. C.1, p. 670 (tool): powers of the complexified matrix are the
complexified powers. -/
theorem map_ofReal_pow (K : Matrix κ κ ℝ) (t : ℕ) :
    (K ^ t).map Complex.ofReal = K.map Complex.ofReal ^ t :=
  Matrix.map_pow K Complex.ofRealHom t

/-- Woodford (2003), App. C.1, p. 670 (tool): the number of eigenvalues equals the dimension. -/
theorem card_eigs (K : Matrix κ κ ℝ) : Multiset.card (eigs K) = Fintype.card κ := by
  rw [eigs, IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim]

/-! ### Geometric decay and bounded powers -/

/-- Woodford (2003), App. C.1, p. 670, fn. 1 (Blanchard–Kahn, the tool; restated from
`BlanchardKahn.pow_entry_bound` for any finite index type): if every complex eigenvalue of a
real square matrix `K` lies in the open unit disc, the entries of `Kᵏ` decay geometrically
(Gelfand's spectral radius formula). -/
theorem pow_entry_bound (K : Matrix κ κ ℝ) (h : ∀ μ ∈ eigs K, ‖μ‖ < 1) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix κ κ ℂ := K.map Complex.ofReal with hA
  have hspec : ∀ w ∈ spectrum ℂ A, w ∈ A.charpoly.roots.toFinset ∧ ‖w‖ < 1 := by
    intro w hw
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hw
    have hm : w ∈ A.charpoly.roots := by
      rw [mem_roots (Matrix.charpoly_monic A).ne_zero]; exact hw
    exact ⟨Multiset.mem_toFinset.mpr hm, h w hm⟩
  set ρ0 : NNReal := A.charpoly.roots.toFinset.sup (fun w => ‖w‖₊) with hρ0
  have hρ0lt : ρ0 < 1 := by
    rw [hρ0, Finset.sup_lt_iff (by norm_num)]
    intro w hw
    have := h w (Multiset.mem_toFinset.mp hw)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    simpa using this
  have hsr : spectralRadius ℂ A ≤ (ρ0 : ENNReal) := by
    refine iSup₂_le fun w hw => ?_
    rw [quasispectrum_eq_spectrum_union_zero] at hw
    rcases hw with hw | hw
    · exact ENNReal.coe_le_coe.mpr (Finset.le_sup (f := fun w => ‖w‖₊) (hspec w hw).1)
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      simp
  set r : ℝ := ((ρ0 : ℝ) + 1) / 2 with hr
  have hρ0' : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
  have hρ0r : (ρ0 : ℝ) < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt ρ0.coe_nonneg hρ0r
  have hlt : spectralRadius ℂ A < ENNReal.ofReal r := by
    refine lt_of_le_of_lt hsr ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hρ0r
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A).eventually_lt_const
    hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hbig : ∀ k ≥ N + 1, ‖A ^ k‖ ≤ r ^ k := by
    intro k hk
    have h1 := hN k (by omega)
    rw [ENNReal.ofReal_lt_ofReal_iff hr0] at h1
    have hk0 : k ≠ 0 := by omega
    have h2 : (‖A ^ k‖ ^ (1 / k : ℝ)) ^ k = ‖A ^ k‖ := by
      rw [one_div]; exact Real.rpow_inv_natCast_pow (norm_nonneg _) hk0
    rw [← h2]
    exact (pow_lt_pow_left₀ h1 (Real.rpow_nonneg (norm_nonneg _) _) hk0).le
  set Cb : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k with hCb
  have hsum0 : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
    Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
  have hCb0 : 0 ≤ Cb := by linarith
  have hall : ∀ k, ‖A ^ k‖ ≤ Cb * r ^ k := by
    intro k
    by_cases hk : k ≤ N
    · have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      have hle : ‖A ^ k‖ / r ^ k ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
        Finset.single_le_sum (f := fun k => ‖A ^ k‖ / r ^ k)
          (fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)) hmem
      have hrk : 0 < r ^ k := pow_pos hr0 k
      have : ‖A ^ k‖ = ‖A ^ k‖ / r ^ k * r ^ k := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hrk.le
    · have := hbig k (by omega)
      have hrk : 0 ≤ r ^ k := pow_nonneg hr0.le k
      nlinarith
  refine ⟨Cb, r, hCb0, hr0, hr1, fun k i j => ?_⟩
  have hentry : |(K ^ k) i j| = ‖(A ^ k) i j‖ := by
    have e : (A ^ k) i j = ((K ^ k) i j : ℂ) := by
      rw [hA, ← map_ofReal_pow]; rfl
    rw [e, Complex.norm_real, Real.norm_eq_abs]
  rw [hentry]
  refine le_trans ?_ (hall k)
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖(A ^ k) i j‖₊ ≤ ∑ j, ‖(A ^ k) i j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖(A ^ k) i j‖₊) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ j, ‖(A ^ k) i j‖₊ ≤ Finset.univ.sup fun i => ∑ j, ‖(A ^ k) i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖(A ^ k) i j‖₊) (Finset.mem_univ i)
  have := h1.trans h2
  rw [← coe_nnnorm]
  exact_mod_cast this

/-- Woodford (2003), App. C.1, p. 670 (tool): if the entries of all powers of a real matrix are
bounded, every complex eigenvalue lies in the closed unit disc. -/
theorem norm_le_one_of_pow_bounded {K : Matrix κ κ ℝ} {Cb : ℝ}
    (hb : ∀ t i j, |(K ^ t) i j| ≤ Cb) : ∀ μ ∈ eigs K, ‖μ‖ ≤ 1 := by
  intro μ hμ
  obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hc0 (funext hne)
  by_contra hgt
  push Not at hgt
  set D : ℝ := ∑ j, Cb * ‖c j‖ with hD
  have hle : ∀ t : ℕ, ‖μ‖ ^ t * ‖c i‖ ≤ D := by
    intro t
    have e := congrFun (pow_mulVec_eigvec hc t) i
    rw [← map_ofReal_pow] at e
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [← norm_pow, ← norm_mul, ← e, Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb t i j) (norm_nonneg _)
  have hci : 0 < ‖c i‖ := norm_pos_iff.mpr hi
  have htend : Tendsto (fun t : ℕ => ‖μ‖ ^ t * ‖c i‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const hci
  obtain ⟨t, ht⟩ := (htend.eventually_gt_atTop D).exists
  exact absurd (hle t) (not_le.mpr ht)

/-! ### The bounded-orbit (stable) subspace -/

/-- Woodford (2003), App. C.1, p. 670, fn. 2: the real vectors whose orbit `Aᵗ v` under
`y_{t+1} = A y_t` is bounded — the real stable invariant subspace of `A` when no eigenvalue lies on
the unit circle. -/
def boundedOrbits (A : Matrix κ κ ℝ) : Submodule ℝ (κ → ℝ) where
  carrier := {v | ∃ C, ∀ t i, |(A ^ t *ᵥ v) i| ≤ C}
  add_mem' := by
    rintro v w ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun t i => ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hC t i) (hD t i))
  zero_mem' := ⟨0, fun t i => by simp⟩
  smul_mem' := by
    rintro c v ⟨C, hC⟩
    refine ⟨|c| * C, fun t i => ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC t i) (abs_nonneg c)

/-- Woodford (2003), App. C.1, p. 670 (tool): membership in the bounded-orbit subspace. -/
theorem mem_boundedOrbits {A : Matrix κ κ ℝ} {v : κ → ℝ} :
    v ∈ boundedOrbits A ↔ ∃ C, ∀ t i, |(A ^ t *ᵥ v) i| ≤ C := Iff.rfl

/-- Woodford (2003), App. C.1, p. 670 (tool): the bounded-orbit subspace is `A`-invariant. -/
theorem mulVec_mem_boundedOrbits {A : Matrix κ κ ℝ} {v : κ → ℝ} (hv : v ∈ boundedOrbits A) :
    A *ᵥ v ∈ boundedOrbits A := by
  obtain ⟨C, hC⟩ := hv
  refine ⟨C, fun t i => ?_⟩
  rw [Matrix.mulVec_mulVec, ← pow_succ]
  exact hC (t + 1) i

/-- Woodford (2003), App. C.1, p. 670 (tool): a vector whose orbit is a bounded sequence `y`
lies in the bounded-orbit subspace. -/
theorem mem_boundedOrbits_of_orbit {A : Matrix κ κ ℝ} {y : ℕ → κ → ℝ}
    (hy : ∀ t, y (t + 1) = A *ᵥ y t) {C : ℝ} (hC : ∀ t i, |y t i| ≤ C) :
    y 0 ∈ boundedOrbits A := by
  have horb : ∀ t, A ^ t *ᵥ y 0 = y t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hy t]
  exact ⟨C, fun t i => by rw [horb t]; exact hC t i⟩

omit [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): the real part of a complexified matrix–vector
product. -/
theorem re_mulVec (K : Matrix κ κ ℝ) (v : κ → ℂ) (i : κ) :
    ((K.map Complex.ofReal *ᵥ v) i).re = (K *ᵥ fun j => (v j).re) i := by
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]

omit [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): the imaginary part of a complexified matrix–vector
product. -/
theorem im_mulVec (K : Matrix κ κ ℝ) (v : κ → ℂ) (i : κ) :
    ((K.map Complex.ofReal *ᵥ v) i).im = (K *ᵥ fun j => (v j).im) i := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]

/-- Woodford (2003), App. C.1, p. 670 (tool): the complex vectors with bounded orbits. -/
def boundedOrbitsC (A : Matrix κ κ ℝ) : Submodule ℂ (κ → ℂ) where
  carrier := {v | ∃ C, ∀ t i, ‖(A.map Complex.ofReal ^ t *ᵥ v) i‖ ≤ C}
  add_mem' := by
    rintro v w ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C + D, fun t i => ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (hC t i) (hD t i))
  zero_mem' := ⟨0, fun t i => by simp⟩
  smul_mem' := by
    rintro c v ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun t i => ?_⟩
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC t i) (norm_nonneg c)

/-- Woodford (2003), App. C.1, p. 670 (tool): generalised eigenvectors of an eigenvalue in the
open unit disc have bounded orbits. Induction on the nilpotency order: with
`u = (A − μ) v` of bounded orbit, `Aᵗ⁺¹ v = μ Aᵗ v + Aᵗ u` stays bounded. -/
theorem maxGenEigenspace_le_boundedOrbitsC (A : Matrix κ κ ℝ) {μ : ℂ} (hμ : ‖μ‖ < 1) :
    Module.End.maxGenEigenspace (Matrix.toLin' (A.map Complex.ofReal)) μ ≤ boundedOrbitsC A := by
  set M : Matrix κ κ ℂ := A.map Complex.ofReal with hM
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨k, hk⟩ := hv
  induction k generalizing v with
  | zero => simp only [pow_zero, Module.End.one_apply] at hk; rw [hk]; exact Submodule.zero_mem _
  | succ k ih =>
    set u : κ → ℂ := M *ᵥ v - μ • v with hu
    have hu' : (Matrix.toLin' M - μ • 1) v = u := by
      simp [hu, Matrix.toLin'_apply]
    have hub : u ∈ boundedOrbitsC A := by
      apply ih
      rw [← hu', ← Module.End.mul_apply, ← pow_succ]
      exact hk
    obtain ⟨Cu, hCu⟩ := hub
    set V : ℝ := ∑ i, ‖v i‖ with hV
    set Mb : ℝ := max V (max Cu 0 / (1 - ‖μ‖)) with hMb
    have h1 : 0 < 1 - ‖μ‖ := by linarith
    have hCM : max Cu 0 ≤ (1 - ‖μ‖) * Mb := by
      have : max Cu 0 / (1 - ‖μ‖) ≤ Mb := le_max_right _ _
      rw [div_le_iff₀ h1] at this
      linarith
    refine ⟨Mb, fun t => ?_⟩
    induction t with
    | zero =>
      intro i
      simp only [pow_zero, Matrix.one_mulVec]
      exact le_trans (Finset.single_le_sum (f := fun i => ‖v i‖) (fun i _ => norm_nonneg _)
        (Finset.mem_univ i)) (le_max_left _ _)
    | succ t ih2 =>
      intro i
      have e : M ^ (t + 1) *ᵥ v = μ • (M ^ t *ᵥ v) + M ^ t *ᵥ u := by
        rw [pow_succ, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_sub, Matrix.mulVec_smul]
        abel
      rw [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have hu2 := hCu t i
      have := mul_le_mul_of_nonneg_left (ih2 i) (norm_nonneg μ)
      have : Cu ≤ max Cu 0 := le_max_left _ _
      nlinarith

/-- Woodford (2003), App. C.1, p. 670 (tool): the complex bounded-orbit subspace is spanned by
(the images of) real vectors with bounded orbits, so its complex dimension is at most the real
dimension of `boundedOrbits A`. -/
theorem finrank_boundedOrbitsC_le (A : Matrix κ κ ℝ) :
    Module.finrank ℂ (boundedOrbitsC A) ≤ Module.finrank ℝ (boundedOrbits A) := by
  set b := Module.finBasis ℝ (boundedOrbits A) with hb
  set f : Fin (Module.finrank ℝ (boundedOrbits A)) → (κ → ℂ) :=
    fun k i => (((b k : boundedOrbits A) : κ → ℝ) i : ℂ) with hf
  have hreal : ∀ w ∈ boundedOrbits A,
      (fun i => (w i : ℂ)) ∈ Submodule.span ℂ (Set.range f) := by
    intro w hw
    have hsum := b.sum_repr ⟨w, hw⟩
    have e : (fun i => (w i : ℂ)) = ∑ k, ((b.repr ⟨w, hw⟩ k : ℝ) : ℂ) • f k := by
      funext i
      have := congrArg (fun z : boundedOrbits A => (z : κ → ℝ) i) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf, ← this, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [e]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  have hle : boundedOrbitsC A ≤ Submodule.span ℂ (Set.range f) := by
    rintro v ⟨C, hC⟩
    have hre : (fun i => (v i).re) ∈ boundedOrbits A := by
      refine ⟨C, fun t i => ?_⟩
      rw [← re_mulVec, map_ofReal_pow]
      exact (Complex.abs_re_le_norm _).trans (hC t i)
    have him : (fun i => (v i).im) ∈ boundedOrbits A := by
      refine ⟨C, fun t i => ?_⟩
      rw [← im_mulVec, map_ofReal_pow]
      exact (Complex.abs_im_le_norm _).trans (hC t i)
    have e : v = (fun i => ((v i).re : ℂ)) + Complex.I • fun i => ((v i).im : ℂ) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm]
      exact (Complex.re_add_im (v i)).symm
    rw [e]
    exact Submodule.add_mem _ (hreal _ hre) (Submodule.smul_mem _ _ (hreal _ him))
  calc Module.finrank ℂ (boundedOrbitsC A) ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range f)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank ℝ (boundedOrbits A))) := finrank_range_le_card f
    _ = Module.finrank ℝ (boundedOrbits A) := Fintype.card_fin _

/-- Woodford (2003), App. C.1, p. 670 (tool): the dimension of the span of finitely many
independent subspaces is the sum of their dimensions. -/
theorem finrank_finset_sup {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {W : ℂ → Submodule ℂ V} (hW : iSupIndep W) (s : Finset ℂ) :
    Module.finrank ℂ (s.sup W : Submodule ℂ V) = ∑ μ ∈ s, Module.finrank ℂ (W μ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha, ← ih]
    have hd : Disjoint (W a) (s.sup W) := by
      rw [Finset.sup_eq_iSup]
      have := hW.disjoint_biSup (x := a) (y := (s : Set ℂ)) (by simpa using ha)
      simpa using this
    have h := Submodule.finrank_sup_add_finrank_inf_eq (W a) (s.sup W)
    rw [disjoint_iff.mp hd, finrank_bot, add_zero] at h
    exact h

/-- Woodford (2003), App. C.1, p. 670 (tool): the number of eigenvalues in a set, counted with
multiplicity, is the sum of their root multiplicities. -/
theorem card_filter_eq_sum (p : ℂ[X]) (P : ℂ → Prop) [DecidablePred P] :
    Multiset.card (p.roots.filter P) =
      ∑ μ ∈ p.roots.toFinset.filter P, p.rootMultiplicity μ := by
  rw [← Multiset.toFinset_sum_count_eq, Multiset.toFinset_filter]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [Finset.mem_filter] at hμ
  rw [Multiset.count_filter, count_roots]
  simp only [hμ.2, ↓reduceIte]

/-- **Stable eigenvalues span bounded orbits** (Woodford (2003), App. C.1, p. 670; Blanchard and
Kahn (1980)): the number of eigenvalues of `A` in the open unit disc, counted with algebraic
multiplicity, is at most the dimension of the real bounded-orbit subspace. -/
theorem stableCount_le_finrank (A : Matrix κ κ ℝ) :
    stableCount A ≤ Module.finrank ℝ (boundedOrbits A) := by
  set φ := Matrix.toLin' (A.map Complex.ofReal) with hφ
  set p := (A.map Complex.ofReal).charpoly with hp
  set s := p.roots.toFinset.filter (fun μ => ‖μ‖ < 1) with hs
  have hcount : stableCount A = ∑ μ ∈ s, Module.finrank ℂ (Module.End.maxGenEigenspace φ μ) := by
    rw [stableCount, eigs, card_filter_eq_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [LinearMap.finrank_maxGenEigenspace_eq, hφ, Matrix.charpoly_toLin']
  have hsup : s.sup (Module.End.maxGenEigenspace φ) ≤ boundedOrbitsC A := by
    refine Finset.sup_le fun μ hμ => ?_
    rw [hs, Finset.mem_filter] at hμ
    exact maxGenEigenspace_le_boundedOrbitsC A hμ.2
  rw [hcount, ← finrank_finset_sup (Module.End.independent_maxGenEigenspace φ) s]
  exact (Submodule.finrank_mono hsup).trans (finrank_boundedOrbitsC_le A)

/-- Woodford (2003), App. C.1, p. 670 (tool): the number of eigenvalues outside the closed unit
disc. -/
noncomputable def unstableCount (K : Matrix κ κ ℝ) : ℕ :=
  Multiset.card ((eigs K).filter (fun μ => 1 < ‖μ‖))

/-- Woodford (2003), App. C.1, p. 670: with no eigenvalue on the unit circle, the stable and the
unstable eigenvalues together are all `n` of them. -/
theorem stableCount_add_unstableCount {K : Matrix κ κ ℝ} (h : NoUnit K) :
    stableCount K + unstableCount K = Fintype.card κ := by
  rw [stableCount, unstableCount, ← card_eigs K, ← Multiset.card_add]
  congr 1
  conv_rhs => rw [← Multiset.filter_add_not (fun μ : ℂ => ‖μ‖ < 1) (eigs K)]
  congr 1
  refine Multiset.filter_congr fun μ hμ => ?_
  have := h μ hμ
  constructor
  · intro h1; exact not_lt.mpr h1.le
  · intro h1; exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm this)

/-! ### The bounded-orbit subspace has exactly `stableCount` dimensions (no unit eigenvalue) -/

/-- Woodford (2003), App. C.1, p. 670 (tool): an `A`-invariant subspace `V` carries a matrix `T`
of the restriction of `A` (in the basis `Module.finBasis`), and `charpoly T` divides
`charpoly A` (block triangular form in a basis adapted to `V ⊕ W`, `W` a complement). -/
theorem restrict_block (A : Matrix κ κ ℝ) (V : Submodule ℝ (κ → ℝ))
    (hV : ∀ v ∈ V, A *ᵥ v ∈ V) :
    ∃ T : Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ,
      T.charpoly ∣ A.charpoly ∧ ∀ j, A *ᵥ (Module.finBasis ℝ V j : κ → ℝ) =
        ∑ i, T i j • (Module.finBasis ℝ V i : κ → ℝ) := by
  set bV := Module.finBasis ℝ V with hbV
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  set bW := Module.finBasis ℝ W with hbW
  set e := Submodule.prodEquivOfIsCompl V W hW with he
  set φ : Module.End ℝ (κ → ℝ) := Matrix.toLin' A with hφ
  set ψ := e.symm.conj φ with hψdef
  set bb := bV.prod bW with hbb
  set T' := LinearMap.toMatrix bb bb ψ with hT'
  have hψ : ∀ j, ψ (bb (Sum.inl j)) = (⟨A *ᵥ bV j, hV _ (bV j).2⟩, 0) := by
    intro j
    rw [hψdef, LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
    have h1 : e (bb (Sum.inl j)) = bV j := by
      rw [he, Submodule.coe_prodEquivOfIsCompl', hbb, Module.Basis.prod_apply_inl_fst,
        Module.Basis.prod_apply_inl_snd]
      simp
    rw [h1, hφ, Matrix.toLin'_apply]
    exact Submodule.prodEquivOfIsCompl_symm_apply_left V W hW ⟨_, _⟩
  have h21 : T'.toBlocks₂₁ = 0 := by
    ext k j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply, hT',
      LinearMap.toMatrix_apply]
    rw [hψ, hbb, Module.Basis.prod_repr_inr]
    simp
  have h11 : ∀ i j, T'.toBlocks₁₁ i j = bV.repr ⟨A *ᵥ bV j, hV _ (bV j).2⟩ i := by
    intro i j
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, hT', LinearMap.toMatrix_apply]
    rw [hψ, hbb, Module.Basis.prod_repr_inl]
  refine ⟨T'.toBlocks₁₁, ?_, fun j => ?_⟩
  · have hc : A.charpoly = T'.charpoly := by
      rw [hT', LinearMap.charpoly_toMatrix, hψdef, LinearEquiv.charpoly_conj, hφ,
        Matrix.charpoly_toLin']
    rw [hc, ← Matrix.fromBlocks_toBlocks T', h21, Matrix.charpoly_fromBlocks_zero₂₁]
    exact dvd_mul_right _ _
  · have hsum := bV.sum_repr ⟨A *ᵥ bV j, hV _ (bV j).2⟩
    have := congrArg Subtype.val hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [h11]

/-- Woodford (2003), App. C.1, p. 670 (tool): `|μ| ≤ 1` when `μᵗ z` stays bounded, `z ≠ 0`. -/
theorem norm_le_one_of_bounded_pow_mul {μ z : ℂ} (hz : z ≠ 0) {C : ℝ}
    (h : ∀ t : ℕ, ‖μ ^ t * z‖ ≤ C) : ‖μ‖ ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have htend : Tendsto (fun t : ℕ => ‖μ‖ ^ t * ‖z‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hgt).atTop_mul_const hz0
  obtain ⟨t, ht⟩ := (htend.eventually_gt_atTop C).exists
  have := h t
  rw [norm_mul, norm_pow] at this
  linarith

/-- Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn (1980)): if no eigenvalue lies on the
unit circle, the matrix `T` of `A` restricted to the bounded-orbit subspace has all its
eigenvalues in the open unit disc, and they are eigenvalues of `A` with multiplicity. The
restriction has bounded powers, so its eigenvalues lie in the closed disc (`restrict_block`
gives `charpoly T ∣ charpoly A`). -/
theorem exists_restrict_stable {A : Matrix κ κ ℝ} (hnu : NoUnit A) :
    ∃ T : Matrix (Fin (Module.finrank ℝ (boundedOrbits A)))
        (Fin (Module.finrank ℝ (boundedOrbits A))) ℝ,
      eigs T ≤ eigs A ∧ (∀ μ ∈ eigs T, ‖μ‖ < 1) ∧
      ∀ j, A *ᵥ (Module.finBasis ℝ (boundedOrbits A) j : κ → ℝ) =
        ∑ i, T i j • (Module.finBasis ℝ (boundedOrbits A) i : κ → ℝ) := by
  set B := boundedOrbits A with hB
  set bV := Module.finBasis ℝ B with hbV
  obtain ⟨T, hdvd, hexp⟩ := restrict_block A B (fun v hv => mulVec_mem_boundedOrbits hv)
  have hle : eigs T ≤ eigs A := by
    have e1 : (T.map Complex.ofReal).charpoly = T.charpoly.map Complex.ofRealHom :=
      Matrix.charpoly_map T Complex.ofRealHom
    have e2 : (A.map Complex.ofReal).charpoly = A.charpoly.map Complex.ofRealHom :=
      Matrix.charpoly_map A Complex.ofRealHom
    rw [eigs, eigs, e1, e2]
    exact Polynomial.roots.le_of_dvd ((Matrix.charpoly_monic A).map _).ne_zero
      (Polynomial.map_dvd _ hdvd)
  set bv : Fin (Module.finrank ℝ B) → κ → ℝ := fun j => (bV j : κ → ℝ) with hbv
  have hli : LinearIndependent ℝ bv := bV.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hst : ∀ μ ∈ eigs T, ‖μ‖ < 1 := by
    intro μ hμ
    obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
    have hcT : ∀ i, ∑ j, (T i j : ℂ) * c j = μ * c i := fun i => by
      have := congrFun hc i
      simpa [Matrix.mulVec, dotProduct] using this
    set u : κ → ℂ := fun k => ∑ j, c j * (bv j k : ℂ) with hu
    have hAu : A.map Complex.ofReal *ᵥ u = μ • u := by
      funext k
      have hb : ∀ j, ∑ l, (A k l : ℂ) * (bv j l : ℂ) = ∑ i, (T i j : ℂ) * (bv i k : ℂ) := by
        intro j
        have := congrFun (hexp j) k
        simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at this
        exact_mod_cast this
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hu, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      have e1 : ∀ j, ∑ l, (A k l : ℂ) * (c j * (bv j l : ℂ)) =
          c j * ∑ i, (T i j : ℂ) * (bv i k : ℂ) := by
        intro j
        rw [← hb j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      simp only [e1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show μ * (c i * (bv i k : ℂ)) = (∑ j, (T i j : ℂ) * c j) * (bv i k : ℂ) by
        rw [hcT i]; ring, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hre : (fun k => (u k).re) = ∑ j, (c j).re • bv j := by
      funext k
      simp [hu, Finset.sum_apply, Complex.re_sum]
    have him : (fun k => (u k).im) = ∑ j, (c j).im • bv j := by
      funext k
      simp [hu, Finset.sum_apply, Complex.im_sum]
    have hreB : (fun k => (u k).re) ∈ B := by
      rw [hre]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bV j).2
    have himB : (fun k => (u k).im) ∈ B := by
      rw [him]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bV j).2
    have hu0 : u ≠ 0 := by
      intro h0
      have h1 : ∑ j, (c j).re • bv j = 0 := by
        rw [← hre, h0]; funext k; simp
      have h2 : ∑ j, (c j).im • bv j = 0 := by
        rw [← him, h0]; funext k; simp
      apply hc0
      funext j
      exact Complex.ext (Fintype.linearIndependent_iff.mp hli _ h1 j)
        (Fintype.linearIndependent_iff.mp hli _ h2 j)
    obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hu0 (funext hne)
    obtain ⟨C1, hC1⟩ := hreB
    obtain ⟨C2, hC2⟩ := himB
    have hbd : ∀ t : ℕ, ‖μ ^ t * u k‖ ≤ C1 + C2 := by
      intro t
      have e := congrFun (pow_mulVec_eigvec hAu t) k
      rw [← map_ofReal_pow] at e
      simp only [Pi.smul_apply, smul_eq_mul] at e
      rw [← e]
      have hr := hC1 t k
      have hi := hC2 t k
      rw [← re_mulVec] at hr
      rw [← im_mulVec] at hi
      refine (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hr hi)
    have h1 := norm_le_one_of_bounded_pow_mul hk hbd
    exact lt_of_le_of_ne h1 (hnu μ (Multiset.mem_of_le hle hμ))
  exact ⟨T, hle, hst, hexp⟩

/-- **The stable dimension equals the stable count** (Woodford (2003), App. C.1, p. 670;
Blanchard and Kahn (1980)), upper bound: if no eigenvalue lies on the unit circle, the dimension
of the bounded-orbit subspace is at most the number of eigenvalues in the open unit disc. -/
theorem finrank_le_stableCount {A : Matrix κ κ ℝ} (hnu : NoUnit A) :
    Module.finrank ℝ (boundedOrbits A) ≤ stableCount A := by
  obtain ⟨T, hle, hst, -⟩ := exists_restrict_stable hnu
  calc Module.finrank ℝ (boundedOrbits A) = Multiset.card (eigs T) := by
        rw [card_eigs, Fintype.card_fin]
    _ = Multiset.card ((eigs T).filter (fun μ => ‖μ‖ < 1)) := by
        rw [Multiset.filter_eq_self.mpr hst]
    _ ≤ stableCount A := Multiset.card_le_card (Multiset.filter_le_filter _ hle)

/-- **Bounded orbits decay** (Woodford (2003), App. C.1, p. 670; Blanchard and Kahn (1980)): if
no eigenvalue lies on the unit circle, every bounded orbit tends to `0`, so the bounded-orbit
subspace is the stable subspace `{v : Aᵗ v → 0}`. On the subspace, `A` acts through the matrix
`T` of `exists_restrict_stable`, whose powers decay geometrically. -/
theorem tendsto_of_mem_boundedOrbits {A : Matrix κ κ ℝ} (hnu : NoUnit A) {v : κ → ℝ}
    (hv : v ∈ boundedOrbits A) : Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0) := by
  obtain ⟨T, -, hst, hexp⟩ := exists_restrict_stable hnu
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hT⟩ := pow_entry_bound T hst
  set bV := Module.finBasis ℝ (boundedOrbits A) with hbV
  set b : Fin (Module.finrank ℝ (boundedOrbits A)) → κ → ℝ := fun j => (bV j : κ → ℝ) with hb
  have hpow : ∀ t j, A ^ t *ᵥ b j = ∑ i, (T ^ t) i j • b i := by
    intro t
    induction t with
    | zero =>
      intro j
      simp only [pow_zero, Matrix.one_mulVec, Matrix.one_apply, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    | succ t ih =>
      intro j
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih j, Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul, hb, hexp, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_smul, pow_succ', Matrix.mul_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hv' : v = ∑ j, bV.repr ⟨v, hv⟩ j • b j := by
    have := congrArg Subtype.val (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hentry : ∀ i j, Tendsto (fun t => (T ^ t) i j) atTop (𝓝 0) := by
    intro i j
    refine squeeze_zero_norm (a := fun t : ℕ => Cb * ρ ^ t) (fun t => ?_) ?_
    · rw [Real.norm_eq_abs]; exact hT t i j
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul Cb
  have e : (fun t => A ^ t *ᵥ v) =
      fun t => ∑ j, ∑ i, (bV.repr ⟨v, hv⟩ j * (T ^ t) i j) • b i := by
    funext t
    conv_lhs => rw [hv']
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, hpow, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
  rw [e]
  have : (0 : κ → ℝ) = ∑ j : Fin (Module.finrank ℝ (boundedOrbits A)),
      ∑ i : Fin (Module.finrank ℝ (boundedOrbits A)), (bV.repr ⟨v, hv⟩ j * 0) • b i := by
    simp
  rw [this]
  refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun i _ => ?_
  exact ((hentry i j).const_mul _).smul_const _

/-- **The stable dimension equals the stable count** (Woodford (2003), App. C.1, p. 670, the
"equivalently" of the counting rule; Blanchard and Kahn (1980)): with no eigenvalue on the unit
circle, the real bounded-orbit (stable) subspace has dimension equal to the number of eigenvalues
in the open unit disc, counted with algebraic multiplicity. -/
theorem finrank_eq_stableCount {A : Matrix κ κ ℝ} (hnu : NoUnit A) :
    Module.finrank ℝ (boundedOrbits A) = stableCount A :=
  le_antisymm (finrank_le_stableCount hnu) (stableCount_le_finrank A)

/-- Woodford (2003), App. C.1, p. 670 (Prop. C.1's mechanism): if every eigenvalue lies outside
the closed unit disc, the only bounded orbit is `0`. -/
theorem boundedOrbits_eq_bot_of_unstable {A : Matrix κ κ ℝ} (h : ∀ μ ∈ eigs A, 1 < ‖μ‖) :
    boundedOrbits A = ⊥ := by
  have hnu : NoUnit A := fun μ hμ h1 => by have := h μ hμ; rw [h1] at this; exact lt_irrefl _ this
  have hc : stableCount A = 0 := by
    rw [stableCount, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    exact fun μ hμ => not_lt.mpr (h μ hμ).le
  rw [← Submodule.finrank_eq_zero, finrank_eq_stableCount hnu, hc]

/-! ### Bounded linear recursions -/

/-- Woodford (2003), App. C.1, p. 670 (tool): an entry of a matrix is bounded by the sum of the
absolute values of all entries. -/
theorem abs_entry_le_sum {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) (i : m)
    (j : n) : |M i j| ≤ ∑ i, ∑ j, |M i j| :=
  (Finset.single_le_sum (f := fun j => |M i j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))

/-- Woodford (2003), App. C.1, p. 670 (tool): `|(M v)_i| ≤ n a b` when the entries of `M` are
bounded by `a` and those of `v` by `b`. -/
theorem abs_mulVec_le {m n : Type*} [Fintype n] (M : Matrix m n ℝ) (v : n → ℝ) {a b : ℝ}
    (hM : ∀ i j, |M i j| ≤ a) (hv : ∀ j, |v j| ≤ b) (i : m) :
    |(M *ᵥ v) i| ≤ Fintype.card n * (a * b) := by
  rw [Matrix.mulVec, dotProduct]
  calc |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : n, a * b := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hM i j) (hv j) (abs_nonneg _) ((abs_nonneg _).trans (hM i j))
    _ = Fintype.card n * (a * b) := by simp

/-- Woodford (2003), App. C.1, p. 670 (tool): the solution of `x_{t+1} = L x_t + f_t`,
`x_t = Lᵗ x_0 + ∑_{k<t} Lᵏ f_{t−1−k}`. -/
theorem rec_closed {L : Matrix κ κ ℝ} {f x : ℕ → κ → ℝ} (hx : ∀ t, x (t + 1) = L *ᵥ x t + f t)
    (t : ℕ) : x t = L ^ t *ᵥ x 0 + ∑ k ∈ Finset.range t, L ^ k *ᵥ f (t - 1 - k) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hx t, ih, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_mulVec, ← pow_succ',
      Finset.sum_range_succ' _ t, add_assoc]
    congr 1
    simp only [pow_zero, Matrix.one_mulVec, Matrix.mulVec_mulVec, ← pow_succ']
    rw [show t + 1 - 1 - 0 = t by omega]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show t + 1 - 1 - (k + 1) = t - 1 - k by omega]

/-- Woodford (2003), App. C.1, p. 670 (tool): if the powers of `L` decay geometrically, the
backward recursion `x_{t+1} = L x_t + f_t` with bounded `f` has a bounded solution. -/
theorem rec_bounded {L : Matrix κ κ ℝ} {Cb ρ : ℝ} (hCb : 0 ≤ Cb) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hL : ∀ k i j, |(L ^ k) i j| ≤ Cb * ρ ^ k) {f x : ℕ → κ → ℝ}
    (hx : ∀ t, x (t + 1) = L *ᵥ x t + f t) {F X0 : ℝ} (hF0 : 0 ≤ F) (hX0 : 0 ≤ X0)
    (hf : ∀ t j, |f t j| ≤ F) (hx0 : ∀ j, |x 0 j| ≤ X0) :
    ∀ t j, |x t j| ≤ Fintype.card κ * Cb * (X0 + F / (1 - ρ)) := by
  intro t j
  set c : ℝ := (Fintype.card κ : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have h1 : 0 < 1 - ρ := by linarith
  rw [rec_closed hx t, Pi.add_apply, Finset.sum_apply]
  have hA : |(L ^ t *ᵥ x 0) j| ≤ c * (Cb * ρ ^ t * X0) :=
    abs_mulVec_le _ _ (hL t) hx0 j
  have hB : ∀ k ∈ Finset.range t, |(L ^ k *ᵥ f (t - 1 - k)) j| ≤ c * Cb * F * ρ ^ k := by
    intro k _
    have := abs_mulVec_le _ _ (hL k) (hf (t - 1 - k)) j
    calc _ ≤ c * (Cb * ρ ^ k * F) := this
      _ = c * Cb * F * ρ ^ k := by ring
  have hgeo : ∑ k ∈ Finset.range t, ρ ^ k ≤ 1 / (1 - ρ) := by
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := t) hρ0 hρ1
    rwa [pow_zero, ← Finset.range_eq_Ico] at this
  have hρt : ρ ^ t ≤ 1 := pow_le_one₀ hρ0 hρ1.le
  have hsum : |∑ k ∈ Finset.range t, (L ^ k *ᵥ f (t - 1 - k)) j| ≤ c * Cb * F * (1 / (1 - ρ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hB).trans ?_)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hgeo (by positivity)
  have hcCb : 0 ≤ c * Cb := mul_nonneg hc0 hCb
  calc _ ≤ |(L ^ t *ᵥ x 0) j| + |∑ k ∈ Finset.range t, (L ^ k *ᵥ f (t - 1 - k)) j| :=
        abs_add_le _ _
    _ ≤ c * (Cb * ρ ^ t * X0) + c * Cb * F * (1 / (1 - ρ)) := add_le_add hA hsum
    _ ≤ c * Cb * X0 + c * Cb * F * (1 / (1 - ρ)) := by
        have : c * (Cb * ρ ^ t * X0) = c * Cb * X0 * ρ ^ t := by ring
        rw [this]
        have := mul_le_mul_of_nonneg_left hρt (mul_nonneg hcCb hX0)
        linarith
    _ = c * Cb * (X0 + F / (1 - ρ)) := by ring

/-- Woodford (2003), App. C.1, p. 670 (tool): the backward recursion `x_{t+1} = L x_t + f_t`,
`x_0` given. -/
def xrecV {ι : Type*} [Fintype ι] (L : Matrix ι ι ℝ) (f : ℕ → ι → ℝ) (x0 : ι → ℝ) :
    ℕ → ι → ℝ
  | 0 => x0
  | t + 1 => L *ᵥ xrecV L f x0 t + f t

/-! ### Predetermined coordinates: the genericity condition and the graph -/

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, p. 672, fn. 2 (the genericity condition the book leaves
implicit; Blanchard and Kahn (1980)): with the state split into non-predetermined coordinates
`Z` and predetermined coordinates `X`, no nonzero bounded orbit starts with `x = 0`. -/
def GenericX (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ v ∈ boundedOrbits A, (∀ j, v (Sum.inr j) = 0) → v = 0

/-- Woodford (2003), App. C.1, p. 672: the projection onto the predetermined coordinates. -/
def projX : (Z ⊕ X → ℝ) →ₗ[ℝ] (X → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inr

/-- Woodford (2003), App. C.1, p. 672: the vector `(G x, x)` of the graph of `G : X → Z`. -/
def graphV (G : Matrix Z X ℝ) (x : X → ℝ) : Z ⊕ X → ℝ := Sum.elim (G *ᵥ x) x

/-- Woodford (2003), App. C.1, p. 672 (Blanchard–Kahn): the bounded-orbit subspace is the graph
of `G`: it contains every `(G x, x)`, and each of its vectors has `z = G x`. -/
def IsGraph (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) : Prop :=
  (∀ x, graphV G x ∈ boundedOrbits A) ∧
    ∀ v ∈ boundedOrbits A, ∀ i, v (Sum.inl i) = (G *ᵥ fun j => v (Sum.inr j)) i

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): two matrices acting identically on all vectors
are equal. -/
theorem matrix_eq_of_mulVec {m n : Type*} [Fintype n] {M N : Matrix m n ℝ}
    (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N := by
  classical
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): a block matrix acting on `(z, x)`. -/
theorem mulVec_sumElim (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (z : Z → ℝ) (x : X → ℝ) :
    A *ᵥ Sum.elim z x = Sum.elim (A.toBlocks₁₁ *ᵥ z + A.toBlocks₁₂ *ᵥ x)
      (A.toBlocks₂₁ *ᵥ z + A.toBlocks₂₂ *ᵥ x) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
  rw [Matrix.fromBlocks_mulVec]
  rfl

/-- **The graph** (Woodford (2003), App. C.1, p. 672; Blanchard and Kahn (1980)): if the
bounded-orbit subspace has dimension `|X|` and meets `{x = 0}` only in `0`, it projects
isomorphically onto the predetermined coordinates, so it is the graph of a matrix `G`. -/
theorem exists_graph {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X) (hg : GenericX A) :
    ∃ G : Matrix Z X ℝ, IsGraph A G := by
  set B := boundedOrbits A with hB
  set f : B →ₗ[ℝ] (X → ℝ) := (projX (Z := Z) (X := X)).domRestrict B with hf
  have hfv : ∀ v : B, ∀ j, f v j = (v : Z ⊕ X → ℝ) (Sum.inr j) := fun _ _ => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    apply Subtype.ext
    exact hg v v.2 (fun j => by rw [← hfv]; exact congrFun hv j)
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [hd, Module.finrank_fintype_fun_eq_card])).mp hinj
  choose b hb using fun j : X => hsurj (Pi.single j 1)
  set G : Matrix Z X ℝ := fun i j => (b j : Z ⊕ X → ℝ) (Sum.inl i) with hG
  have h1 : ∀ x : X → ℝ, graphV G x = ∑ j, x j • (b j : Z ⊕ X → ℝ) := by
    intro x
    funext k
    rcases k with i | k
    · simp [graphV, hG, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    · have e : ∀ j, (b j : Z ⊕ X → ℝ) (Sum.inr k) = (Pi.single j (1 : ℝ) : X → ℝ) k := fun j => by
        rw [← hfv, hb j]
      simp only [graphV, Sum.elim_inr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp only [e]
      simp [Pi.single_apply]
  have hmem : ∀ x : X → ℝ, graphV G x ∈ B := by
    intro x
    rw [h1 x]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2
  refine ⟨G, hmem, fun v hv i => ?_⟩
  set w := v - graphV G (fun j => v (Sum.inr j)) with hw
  have hwB : w ∈ B := Submodule.sub_mem _ hv (hmem _)
  have hw0 : w = 0 := hg w hwB (fun j => by simp [hw, graphV])
  have := congrFun hw0 (Sum.inl i)
  simp only [hw, Pi.sub_apply, graphV, Sum.elim_inl, Pi.zero_apply, sub_eq_zero] at this
  exact this

/-- Woodford (2003), App. C.1, p. 672: `Λ = A_xz G + A_xx`, the matrix of `A` restricted to the
graph, in the predetermined coordinates. -/
def lam (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) : Matrix X X ℝ :=
  A.toBlocks₂₁ * G + A.toBlocks₂₂

/-- Woodford (2003), App. C.1, p. 672: `C = A_zz − G A_xz`, the matrix governing
`ẑ_t = z_t − G x_t`. -/
def cmat (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) : Matrix Z Z ℝ :=
  A.toBlocks₁₁ - G * A.toBlocks₂₁

/-- Woodford (2003), App. C.1, p. 672: invariance of the graph,
`A_zz G + A_zx = G Λ`, i.e. `A [G; I] = [G; I] Λ`. -/
theorem graph_invariant {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G) :
    A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G := by
  refine matrix_eq_of_mulVec fun x => ?_
  have hv := mulVec_mem_boundedOrbits (hG.1 x)
  funext i
  have e := hG.2 _ hv i
  rw [graphV, mulVec_sumElim] at e
  simp only [Sum.elim_inl, Sum.elim_inr] at e
  have e2 : (A.toBlocks₁₁ * G + A.toBlocks₁₂) *ᵥ x =
      A.toBlocks₁₁ *ᵥ (G *ᵥ x) + A.toBlocks₁₂ *ᵥ x := by
    rw [Matrix.add_mulVec, Matrix.mulVec_mulVec]
  have e3 : (G * lam A G) *ᵥ x = G *ᵥ (A.toBlocks₂₁ *ᵥ (G *ᵥ x) + A.toBlocks₂₂ *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, lam, Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [e2, e3]
  exact e

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the invariance identity on vectors,
`A_zz G x + A_zx x = G Λ x`. -/
theorem graph_invariant_vec {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (x : X → ℝ) :
    A.toBlocks₁₁ *ᵥ (G *ᵥ x) + A.toBlocks₁₂ *ᵥ x = G *ᵥ (lam A G *ᵥ x) := by
  have := congrArg (fun M => M *ᵥ x) hinv
  simpa only [Matrix.add_mulVec, Matrix.mulVec_mulVec] using this

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): `Λ x = A_xz G x + A_xx x`. -/
theorem lam_mulVec (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) (x : X → ℝ) :
    lam A G *ᵥ x = A.toBlocks₂₁ *ᵥ (G *ᵥ x) + A.toBlocks₂₂ *ᵥ x := by
  rw [lam, Matrix.add_mulVec, Matrix.mulVec_mulVec]

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672: `A (G x, x) = (G Λ x, Λ x)`. -/
theorem mulVec_graphV {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (x : X → ℝ) :
    A *ᵥ graphV G x = graphV G (lam A G *ᵥ x) := by
  rw [graphV, mulVec_sumElim, graphV, graph_invariant_vec hinv, lam_mulVec]

/-- Woodford (2003), App. C.1, p. 672: `Aᵗ (G x, x) = (G Λᵗ x, Λᵗ x)`. -/
theorem pow_mulVec_graphV {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (x : X → ℝ) (t : ℕ) :
    A ^ t *ᵥ graphV G x = graphV G (lam A G ^ t *ᵥ x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, mulVec_graphV hinv, Matrix.mulVec_mulVec,
      ← pow_succ']

/-- Woodford (2003), App. C.1, p. 672: the powers of `Λ` are bounded (`Λᵗ` is `Aᵗ` on bounded
orbits). -/
theorem lam_pow_bounded {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G) :
    ∃ Cb, ∀ t j k, |(lam A G ^ t) j k| ≤ Cb := by
  have hinv := graph_invariant hG
  choose C hC using fun k : X => hG.1 (Pi.single k (1 : ℝ))
  refine ⟨∑ k, |C k|, fun t j k => ?_⟩
  have e : (lam A G ^ t) j k = (A ^ t *ᵥ graphV G (Pi.single k (1 : ℝ))) (Sum.inr j) := by
    rw [pow_mulVec_graphV hinv, graphV, Sum.elim_inr]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e]
  exact ((hC k t _).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))

/-- Woodford (2003), App. C.1, p. 672 (tool): the change of variables `ẑ = z − G x` and its
inverse. -/
theorem fromBlocks_shear_mul (G : Matrix Z X ℝ) :
    Matrix.fromBlocks (1 : Matrix Z Z ℝ) G 0 (1 : Matrix X X ℝ) *
      Matrix.fromBlocks (1 : Matrix Z Z ℝ) (-G) 0 (1 : Matrix X X ℝ) = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

/-- **Block triangularisation** (Woodford (2003), App. C.1, p. 672; Blanchard and Kahn (1980)):
in the coordinates `(ẑ, x)`, `ẑ = z − G x`, the matrix `A` is block lower triangular with
diagonal blocks `C` and `Λ`, so `charpoly A = charpoly C · charpoly Λ`. -/
theorem charpoly_split {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) :
    A.charpoly = (cmat A G).charpoly * (lam A G).charpoly := by
  set T := Matrix.fromBlocks (1 : Matrix Z Z ℝ) G 0 (1 : Matrix X X ℝ) with hT
  set T' := Matrix.fromBlocks (1 : Matrix Z Z ℝ) (-G) 0 (1 : Matrix X X ℝ) with hT'
  have hconj : T' * A * T = Matrix.fromBlocks (cmat A G) 0 A.toBlocks₂₁ (lam A G) := by
    rw [hT, hT']
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks A]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    have h12 : (A.toBlocks₁₁ - G * A.toBlocks₂₁) * G + (A.toBlocks₁₂ - G * A.toBlocks₂₂) = 0 := by
      have e : (A.toBlocks₁₁ - G * A.toBlocks₂₁) * G + (A.toBlocks₁₂ - G * A.toBlocks₂₂) =
          (A.toBlocks₁₁ * G + A.toBlocks₁₂) - G * lam A G := by
        rw [lam, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel
      rw [e, hinv, sub_self]
    congr 1
    · simp [cmat, sub_eq_add_neg, Matrix.neg_mul]
    · simpa [sub_eq_add_neg, Matrix.neg_mul, Matrix.add_mul, Matrix.mul_assoc] using h12
    · simp
    · simp [lam]
  calc A.charpoly = ((T * T') * A).charpoly := by rw [fromBlocks_shear_mul, Matrix.one_mul]
    _ = ((T' * A) * T).charpoly := by rw [Matrix.mul_assoc, Matrix.charpoly_mul_comm]
    _ = _ := by rw [hconj, Matrix.charpoly_fromBlocks_zero₁₂]

/-- Woodford (2003), App. C.1, p. 670 (tool): the characteristic polynomial of the
complexification. -/
theorem charpoly_map_ofReal (K : Matrix κ κ ℝ) :
    (K.map Complex.ofReal).charpoly = K.charpoly.map Complex.ofRealHom :=
  Matrix.charpoly_map K Complex.ofRealHom

/-- Woodford (2003), App. C.1, p. 672: the eigenvalues of `A` are those of `C` together with those
of `Λ`, with multiplicity. -/
theorem eigs_split {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) :
    eigs A = eigs (cmat A G) + eigs (lam A G) := by
  rw [eigs, eigs, eigs, charpoly_map_ofReal, charpoly_map_ofReal, charpoly_map_ofReal,
    charpoly_split hinv, Polynomial.map_mul]
  refine roots_mul ?_
  exact mul_ne_zero ((Matrix.charpoly_monic _).map _).ne_zero
    ((Matrix.charpoly_monic _).map _).ne_zero

/-- Woodford (2003), App. C.1, p. 672: with no eigenvalue on the unit circle, every eigenvalue of
`Λ` lies in the open unit disc. -/
theorem lam_stable {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G)
    (hnu : NoUnit A) : ∀ μ ∈ eigs (lam A G), ‖μ‖ < 1 := by
  intro μ hμ
  obtain ⟨Cb, hCb⟩ := lam_pow_bounded hG
  have h1 := norm_le_one_of_pow_bounded hCb μ hμ
  have h2 : μ ∈ eigs A := by
    rw [eigs_split (graph_invariant hG)]
    exact Multiset.mem_add.mpr (Or.inr hμ)
  exact lt_of_le_of_ne h1 (hnu μ h2)

/-- Woodford (2003), App. C.1, p. 672 (Blanchard–Kahn): a bounded solution `ẑ` of
`ẑ_{t+1} = C ẑ_t` starts at `0` — otherwise `(ẑ_0, 0)` would be a nonzero bounded orbit of `A`
with `x = 0` (the orbit is completed by `x_{t+1} = Λ x_t + A_xz ẑ_t`, `x_0 = 0`). -/
theorem zero_of_cmat_orbit {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hG : IsGraph A G) (hg : GenericX A) {Cb ρ : ℝ} (hCb : 0 ≤ Cb) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hL : ∀ k i j, |(lam A G ^ k) i j| ≤ Cb * ρ ^ k) {zh : ℕ → Z → ℝ}
    (hrec : ∀ t, zh (t + 1) = cmat A G *ᵥ zh t) {Kz : ℝ} (hKz : 0 ≤ Kz)
    (hzb : ∀ t i, |zh t i| ≤ Kz) : zh 0 = 0 := by
  have hinv := graph_invariant hG
  set R := A.toBlocks₂₁ with hR
  set x : ℕ → X → ℝ := xrecV (lam A G) (fun t => R *ᵥ zh t) 0 with hx
  have hxrec : ∀ t, x (t + 1) = lam A G *ᵥ x t + R *ᵥ zh t := fun t => rfl
  set aR : ℝ := ∑ i, ∑ j, |R i j| with haR
  set aG : ℝ := ∑ i, ∑ j, |G i j| with haG
  have haR0 : 0 ≤ aR := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have haG0 : 0 ≤ aG := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set F : ℝ := Fintype.card Z * (aR * Kz) with hF
  have hF0 : 0 ≤ F := by positivity
  have hfb : ∀ t j, |(R *ᵥ zh t) j| ≤ F := fun t j =>
    abs_mulVec_le R (zh t) (abs_entry_le_sum R) (hzb t) j
  set Xb : ℝ := Fintype.card X * Cb * (0 + F / (1 - ρ)) with hXb
  have hxb : ∀ t j, |x t j| ≤ Xb :=
    rec_bounded hCb hρ0 hρ1 hL hxrec hF0 le_rfl hfb (fun j => by simp [hx, xrecV])
  have hXb0 : 0 ≤ Xb := by
    have : 0 < 1 - ρ := by linarith
    positivity
  set y : ℕ → Z ⊕ X → ℝ := fun t => Sum.elim (zh t + G *ᵥ x t) (x t) with hy
  have hystep : ∀ t, y (t + 1) = A *ᵥ y t := by
    intro t
    rw [hy, mulVec_sumElim]
    simp only
    rw [hrec t, hxrec t]
    congr 1
    · rw [cmat]
      simp only [Matrix.mulVec_add, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
      rw [← graph_invariant_vec hinv]
      abel
    · simp only [Matrix.mulVec_add, lam_mulVec]
      abel
  have hyb : ∀ t k, |y t k| ≤ Kz + Fintype.card X * (aG * Xb) + Xb := by
    intro t k
    have hGx : ∀ i, |(G *ᵥ x t) i| ≤ Fintype.card X * (aG * Xb) := fun i =>
      abs_mulVec_le G (x t) (abs_entry_le_sum G) (hxb t) i
    rcases k with i | j
    · simp only [hy, Sum.elim_inl, Pi.add_apply]
      have := (abs_add_le _ _).trans (add_le_add (hzb t i) (hGx i))
      linarith
    · simp only [hy, Sum.elim_inr]
      have : 0 ≤ Kz + Fintype.card X * (aG * Xb) := by positivity
      linarith [hxb t j]
  have hmem := mem_boundedOrbits_of_orbit hystep hyb
  have h0 : y 0 = 0 := hg _ hmem (fun j => by simp [hy, hx, xrecV])
  funext i
  have := congrFun h0 (Sum.inl i)
  simpa [hy, hx, xrecV] using this

/-- Woodford (2003), App. C.1, p. 672 (Blanchard–Kahn): under genericity, every eigenvalue of
`C = A_zz − G A_xz` lies outside the closed unit disc (given that `Λ` is stable). For an
eigenvalue `|μ| ≤ 1` with eigenvector `c`, the real and imaginary parts of `μᵗ c` are bounded
solutions of `ẑ_{t+1} = C ẑ_t`, so `c = 0` by `zero_of_cmat_orbit`. -/
theorem cmat_unstable {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G)
    (hg : GenericX A) (hΛ : ∀ μ ∈ eigs (lam A G), ‖μ‖ < 1) :
    ∀ μ ∈ eigs (cmat A G), 1 < ‖μ‖ := by
  intro μ hμ
  by_contra hle
  push Not at hle
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hL⟩ := pow_entry_bound (lam A G) hΛ
  obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
  set K : ℝ := ∑ i, ‖c i‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hstep : ∀ t i, μ ^ (t + 1) * c i =
      ((cmat A G).map Complex.ofReal *ᵥ fun j => μ ^ t * c j) i := by
    intro t i
    have : (cmat A G).map Complex.ofReal *ᵥ (fun j => μ ^ t * c j) = μ ^ (t + 1) • c := by
      have e : (fun j => μ ^ t * c j) = μ ^ t • c := rfl
      rw [e, Matrix.mulVec_smul, hc, smul_smul, pow_succ]
    rw [this]
    rfl
  have hbd : ∀ t i, ‖μ ^ t * c i‖ ≤ K := by
    intro t i
    rw [norm_mul, norm_pow]
    calc ‖μ‖ ^ t * ‖c i‖ ≤ 1 * ‖c i‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hle) (norm_nonneg _)
      _ ≤ K := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun i => ‖c i‖) (fun _ _ => norm_nonneg _)
            (Finset.mem_univ i)
  have hre := zero_of_cmat_orbit hG hg hCb hρ0.le hρ1 hL
    (zh := fun t i => (μ ^ t * c i).re)
    (fun t => by
      funext i
      rw [hstep t i]
      exact re_mulVec _ _ i) hK0
    (fun t i => (Complex.abs_re_le_norm _).trans (hbd t i))
  have him := zero_of_cmat_orbit hG hg hCb hρ0.le hρ1 hL
    (zh := fun t i => (μ ^ t * c i).im)
    (fun t => by
      funext i
      rw [hstep t i]
      exact im_mulVec _ _ i) hK0
    (fun t i => (Complex.abs_im_le_norm _).trans (hbd t i))
  apply hc0
  funext i
  have h1 := congrFun hre i
  have h2 := congrFun him i
  simp only [pow_zero, one_mul, Pi.zero_apply] at h1 h2
  exact Complex.ext h1 h2

/-- **The eigenvalue count** (Woodford (2003), App. C.1, p. 672; Blanchard and Kahn (1980)): if
the graph's `Λ` is stable and `C` is unstable, exactly `|X|` eigenvalues of `A` (with
multiplicity) lie in the open unit disc. -/
theorem stableCount_eq_card {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G)
    (hΛ : ∀ μ ∈ eigs (lam A G), ‖μ‖ < 1) (hC : ∀ μ ∈ eigs (cmat A G), 1 < ‖μ‖) :
    stableCount A = Fintype.card X := by
  rw [stableCount, eigs_split hinv, Multiset.filter_add, Multiset.card_add,
    Multiset.filter_eq_nil.mpr (fun μ hμ => not_lt.mpr (hC μ hμ).le),
    Multiset.filter_eq_self.mpr hΛ, Multiset.card_zero, zero_add, card_eigs]

/-- Woodford (2003), App. C.1, p. 672: genericity bounds the dimension of the bounded-orbit
subspace by the number of predetermined variables. -/
theorem finrank_le_of_genericX {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hg : GenericX A) :
    Module.finrank ℝ (boundedOrbits A) ≤ Fintype.card X := by
  set f := (projX (Z := Z) (X := X)).domRestrict (boundedOrbits A) with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (hg v v.2 (fun j => congrFun hv j))
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card] at this

/-- Woodford (2003), App. C.1, p. 672, fn. 2: more bounded directions than predetermined
variables violate genericity. -/
theorem not_genericX_of_lt {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Fintype.card X < Module.finrank ℝ (boundedOrbits A)) : ¬ GenericX A :=
  fun hg => absurd (finrank_le_of_genericX hg) (not_le.mpr h)

/-- Woodford (2003), App. C.1, p. 672: fewer bounded directions than predetermined variables
leave some initial condition `x₀` not reached by any bounded orbit. -/
theorem exists_unreached_of_lt {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) :
    ∃ x0 : X → ℝ, ∀ v ∈ boundedOrbits A, (fun j => v (Sum.inr j)) ≠ x0 := by
  set f := (projX (Z := Z) (X := X)).domRestrict (boundedOrbits A) with hf
  have hr : LinearMap.range f ≠ ⊤ := by
    intro htop
    have h1 := LinearMap.finrank_range_le f
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
    exact absurd h1 (not_le.mpr h)
  obtain ⟨x0, hx0⟩ : ∃ x0, x0 ∉ LinearMap.range f := by
    by_contra hall
    push Not at hall
    exact hr (eq_top_iff.mpr fun x _ => hall x)
  refine ⟨x0, fun v hv he => hx0 ⟨⟨v, hv⟩, ?_⟩⟩
  rw [← he]
  rfl

/-- **The two forms of the counting condition** (Woodford (2003), App. C.1, p. 672; Blanchard and
Kahn (1980)): with no eigenvalue on the unit circle and genericity, the stable subspace has
dimension `|X|` iff exactly `|X|` eigenvalues (with multiplicity) lie in the open unit disc. -/
theorem finrank_eq_iff_stableCount_eq {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A)
    (hg : GenericX A) :
    Module.finrank ℝ (boundedOrbits A) = Fintype.card X ↔ stableCount A = Fintype.card X := by
  constructor
  · intro hd
    obtain ⟨G, hG⟩ := exists_graph hd hg
    have hΛ := lam_stable hG hnu
    exact stableCount_eq_card (graph_invariant hG) hΛ (cmat_unstable hG hg hΛ)
  · intro hc
    exact le_antisymm (finrank_le_of_genericX hg) (hc ▸ stableCount_le_finrank A)

end InvariantSplit

/-!
# Forward systems over an arbitrary finite index type

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670, fn. 1 (Blanchard and Kahn 1980).
Vector processes of random variables indexed by any finite type, and the forward system
`s_t = K E_t s_{t+1} + w_t`: if the powers of `K` decay geometrically it has exactly one bounded
adapted solution for every bounded adapted forcing, the forward series
`s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` (`fsolves_exists`, `fsolves_unique`).

Restated from `BlanchardKahn` (`rvMul`, `FSolves`, `fsolves_iterate`, `fsolves_unique`,
`fsolves_exists`, which restated them from the Galí Chapter 6 project), generalised from `Fin n`
to any finite index type.
-/

namespace GeneralBKForward

open Filter Topology
open scoped Matrix

/-- Woodford (2003), App. C.1, p. 670 (tool): a matrix acting on a vector of random variables,
`(M a)_i = ∑_j M_{ij} a_j`. -/
def mv {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) : m → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Woodford (2003), App. C.1, p. 670 (tool): the action, pointwise. -/
theorem mv_apply {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m)
    (ω : Ω) : mv M a i ω = (M *ᵥ fun j => a j ω) i := by
  simp [mv, Finset.sum_apply, Matrix.mulVec, dotProduct]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action, pointwise, as a sum. -/
theorem mv_apply_sum {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m)
    (ω : Ω) : mv M a i ω = ∑ j, M i j * a j ω := by
  simp [mv, Finset.sum_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): compatibility with matrix multiplication. -/
theorem mv_mv {Ω m n l : Type*} [Fintype n] [Fintype l] (M : Matrix m n ℝ) (N : Matrix n l ℝ)
    (a : l → Ω → ℝ) : mv M (mv N a) = mv (M * N) a := by
  funext i
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Woodford (2003), App. C.1, p. 670 (tool): additivity of the action. -/
theorem mv_add {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a b : n → Ω → ℝ) :
    mv M (a + b) = mv M a + mv M b := by
  funext i
  simp only [mv, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action respects subtraction. -/
theorem mv_sub {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a b : n → Ω → ℝ) :
    mv M (a - b) = mv M a - mv M b := by
  funext i
  simp only [mv, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action of a sum of matrices. -/
theorem add_mv {Ω m n : Type*} [Fintype n] (M N : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv (M + N) a = mv M a + mv N a := by
  funext i
  simp only [mv, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action of a difference of matrices. -/
theorem sub_mv {Ω m n : Type*} [Fintype n] (M N : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv (M - N) a = mv M a - mv N a := by
  funext i
  simp only [mv, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.sub_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the identity matrix acts trivially. -/
theorem mv_one {Ω n : Type*} [Fintype n] [DecidableEq n] (a : n → Ω → ℝ) :
    mv (1 : Matrix n n ℝ) a = a := by
  funext i
  simp [mv, Matrix.one_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action on the zero vector. -/
theorem mv_zero {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) :
    mv M (0 : n → Ω → ℝ) = 0 := by
  funext i
  simp [mv]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action respects negation. -/
theorem mv_neg {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv M (-a) = -mv M a := by
  funext i
  simp [mv, Finset.sum_neg_distrib]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), App. C.1, p. 670 (tool): `E_t` commutes with constant matrices. -/
theorem E_mv {m n : Type*} [Fintype n] (t : ℕ) (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m) :
    𝔼.E t (mv M a i) = mv M (fun j => 𝔼.E t (a j)) i := by
  simp only [mv, map_sum, map_smul]

/-- Woodford (2003), App. C.1, p. 670: a vector process is adapted. -/
def AdaptedV {ι : Type*} (s : ℕ → ι → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Woodford (2003), App. C.1, p. 670: a vector process is bounded. -/
def BoundedV {ι : Type*} (s : ℕ → ι → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M

/-- Woodford (2003), App. C.1, p. 670: `s` solves the forward system
`s_t = K E_t s_{t+1} + w_t`. -/
def FSolves {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (w s : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t, s t = mv K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Woodford (2003), App. C.1, p. 670 (tool): a constant matrix maps a bounded vector process to
a bounded one. -/
theorem boundedV_mv {m n : Type*} [Finite m] [Fintype n] (M : Matrix m n ℝ)
    {a : ℕ → n → Ω → ℝ} (ha : BoundedV a) : BoundedV (fun t => mv M (a t)) := by
  have := Fintype.ofFinite m
  obtain ⟨B, hB⟩ := ha
  refine ⟨Fintype.card n * ((∑ i, ∑ j, |M i j|) * max B 0), fun t i ω => ?_⟩
  change |mv M (a t) i ω| ≤ _
  rw [mv_apply]
  exact InvariantSplit.abs_mulVec_le M _ (InvariantSplit.abs_entry_le_sum M)
    (fun j => (hB t j ω).trans (le_max_left _ _)) i |>.trans (le_of_eq (by ring))

/-- Woodford (2003), App. C.1, p. 670 (tool): a constant matrix maps an adapted vector process
to an adapted one. -/
theorem adaptedV_mv {m n : Type*} [Fintype n] (M : Matrix m n ℝ) {a : ℕ → n → Ω → ℝ}
    (ha : AdaptedV 𝔼 a) : AdaptedV 𝔼 (fun t => mv M (a t)) := by
  intro t i
  change 𝔼.E t (mv M (a t) i) = mv M (a t) i
  rw [E_mv 𝔼]
  congr 1
  funext j
  exact ha t j

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), App. C.1, p. 670: iterating a homogeneous forward system,
`d_t = Kᵏ E_t d_{t+k}`. -/
theorem fsolves_iterate {K : Matrix ι ι ℝ} {d : ℕ → ι → Ω → ℝ} (hd : FSolves 𝔼 K 0 d)
    (had : AdaptedV 𝔼 d) (t k : ℕ) : d t = mv (K ^ k) (fun j => 𝔼.E t (d (t + k) j)) := by
  induction k with
  | zero =>
    funext i
    simp only [pow_zero, add_zero, mv_one, had t i]
  | succ k ih =>
    rw [ih]
    have h := hd (t + k)
    simp only [Pi.zero_apply, add_zero] at h
    have : (fun j => 𝔼.E t (d (t + k) j)) = mv K (fun j => 𝔼.E t (d (t + (k + 1)) j)) := by
      funext j
      rw [h, E_mv 𝔼]
      congr 1
      funext l
      rw [𝔼.tower (Nat.le_add_right t k), ← add_assoc]
    rw [this, mv_mv, ← pow_succ]

omit [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): bound for `Kᵏ` acting on a bounded vector. -/
theorem abs_mv_le {M : Matrix ι ι ℝ} {c : ℝ} (hM : ∀ i j, |M i j| ≤ c) {a : ι → Ω → ℝ}
    {B : ℝ} (ha : ∀ j ω, |a j ω| ≤ B) (i : ι) (ω : Ω) :
    |mv M a i ω| ≤ Fintype.card ι * (c * B) := by
  rw [mv_apply]
  exact InvariantSplit.abs_mulVec_le M _ hM (fun j => ha j ω) i

/-- Woodford (2003), App. C.1, p. 670, fn. 1 (Blanchard–Kahn): if the powers of `K` decay
geometrically, `s_t = K E_t s_{t+1} + w_t` has at most one bounded adapted solution. -/
theorem fsolves_unique {K : Matrix ι ι ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w x y : ℕ → ι → Ω → ℝ}
    (hx : FSolves 𝔼 K w x) (hy : FSolves 𝔼 K w y) (hax : AdaptedV 𝔼 x) (hay : AdaptedV 𝔼 y)
    (hbx : BoundedV x) (hby : BoundedV y) : x = y := by
  obtain ⟨M₁, hM₁⟩ := hbx
  obtain ⟨M₂, hM₂⟩ := hby
  set d : ℕ → ι → Ω → ℝ := fun t => x t - y t with hd_def
  have hd : FSolves 𝔼 K 0 d := by
    intro t
    simp only [hd_def, Pi.zero_apply, add_zero, Pi.sub_apply, map_sub]
    rw [hx t, hy t]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, mv, smul_sub, Finset.sum_sub_distrib]
    abel
  have had : AdaptedV 𝔼 d := by
    intro t i
    simp only [hd_def, Pi.sub_apply, map_sub, hax t i, hay t i]
  have hdb : ∀ t i ω, |d t i ω| ≤ M₁ + M₂ := fun t i ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t i ω) (hM₂ t i ω))
  have hzero : d = 0 := by
    funext t i ω
    have hle : ∀ k, |d t i ω| ≤ Fintype.card ι * (Cb * ρ ^ k * (M₁ + M₂)) := by
      intro k
      rw [fsolves_iterate 𝔼 hd had t k]
      exact abs_mv_le (hK k) (fun j ω => 𝔼.abs_E_le (hdb (t + k) j) t ω) i ω
    have hlim : Tendsto (fun k : ℕ => (Fintype.card ι : ℝ) * (Cb * ρ ^ k * (M₁ + M₂))) atTop
        (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul Cb).mul_const
        (M₁ + M₂)
      simpa using this.const_mul (Fintype.card ι : ℝ)
    have h0 : |d t i ω| ≤ 0 := ge_of_tendsto' hlim hle
    simpa using h0
  funext t i ω
  have := congrFun (congrFun (congrFun hzero t) i) ω
  simpa [hd_def, sub_eq_zero] using this

/-- Woodford (2003), App. C.1, p. 670, fn. 1 (Blanchard–Kahn): if the powers of `K` decay
geometrically, the forward series `s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` is a bounded adapted solution
of `s_t = K E_t s_{t+1} + w_t` for bounded adapted forcing `w`. -/
theorem fsolves_exists {K : Matrix ι ι ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w : ℕ → ι → Ω → ℝ} {Mw : ℝ}
    (hw : ∀ t i ω, |w t i ω| ≤ Mw) (haw : AdaptedV 𝔼 w) :
    ∃ s, FSolves 𝔼 K w s ∧ AdaptedV 𝔼 s ∧ BoundedV s := by
  set Mb : ℝ := Fintype.card ι * Cb * Mw with hMb
  set B : ℕ → ℕ → ι → Ω → ℝ := fun k t => mv (K ^ k) (fun j => 𝔼.E t (w (t + k) j)) with hB
  have hT : ∀ k t t' i ω, |mv (K ^ k) (fun j => 𝔼.E t (w t' j)) i ω| ≤ ρ ^ k * Mb := by
    intro k t t' i ω
    have := abs_mv_le (hK k) (fun j ω => 𝔼.abs_E_le (hw t' j) t ω) i ω
    calc _ ≤ Fintype.card ι * (Cb * ρ ^ k * Mw) := this
      _ = ρ ^ k * Mb := by rw [hMb]; ring
  have hTs : ∀ t t' : ℕ → ℕ, ∀ i ω,
      Summable fun k => mv (K ^ k) (fun j => 𝔼.E (t k) (w (t' k) j)) i ω := fun t t' i ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Mb)
      (fun k => by rw [Real.norm_eq_abs]; exact hT k (t k) (t' k) i ω)
  have hBb : ∀ k t i ω, |B k t i ω| ≤ ρ ^ k * Mb := fun k t i ω => hT k t (t + k) i ω
  have hsum : ∀ t i ω, Summable fun k => B k t i ω := fun t i ω =>
    hTs (fun _ => t) (fun k => t + k) i ω
  set s : ℕ → ι → Ω → ℝ := fun t i ω => ∑' k, B k t i ω with hs
  have hEB : ∀ k t i, 𝔼.E t (B k (t + 1) i) =
      mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i := by
    intro k t i
    simp only [hB, E_mv 𝔼, 𝔼.tower (Nat.le_succ t)]
  have hEs : ∀ t i ω, 𝔼.E t (s (t + 1) i) ω =
      ∑' k, mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i ω := by
    intro t i ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k (t + 1) i) (fun k ω => hBb k (t + 1) i ω) t ω
    rw [show s (t + 1) i = fun ω' => ∑' k, B k (t + 1) i ω' from rfl, this]
    exact tsum_congr fun k => by rw [hEB]
  refine ⟨s, ?_, ?_, ?_⟩
  · intro t
    funext i ω
    have hB0 : B 0 t i ω = w t i ω := by
      simp only [hB, pow_zero, add_zero, mv_one, haw t i]
    have hshift : ∀ k, B (k + 1) t i ω =
        ∑ l, K i l * mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) l ω := by
      intro k
      simp only [hB]
      rw [← mv_apply_sum, mv_mv, ← pow_succ', show t + (k + 1) = t + 1 + k by omega]
    have hR : (mv K (fun j => 𝔼.E t (s (t + 1) j)) + w t) i ω =
        (∑' k, B (k + 1) t i ω) + w t i ω := by
      rw [Pi.add_apply, Pi.add_apply, mv_apply_sum]
      congr 1
      simp only [hEs, ← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun l _ =>
        (hTs (fun _ => t) (fun k => t + 1 + k) l ω).mul_left (K i l))]
      exact tsum_congr fun k => (hshift k).symm
    rw [hR, show s t i ω = ∑' k, B k t i ω from rfl, (hsum t i ω).tsum_eq_zero_add, hB0]
    ring
  · intro t i
    funext ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k t i) (fun k ω => hBb k t i ω) t ω
    rw [show s t i = fun ω' => ∑' k, B k t i ω' from rfl, this]
    refine tsum_congr fun k => ?_
    simp only [hB, E_mv 𝔼, 𝔼.E_E_self]
  · refine ⟨Mb / (1 - ρ), fun t i ω => ?_⟩
    have hg : HasSum (fun k : ℕ => ρ ^ k * Mb) (Mb / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right Mb
      rwa [← div_eq_inv_mul] at this
    have := tsum_of_norm_bounded hg (f := fun k => B k t i ω)
      (fun k => by rw [Real.norm_eq_abs]; exact hBb k t i ω)
    rw [Real.norm_eq_abs] at this
    exact this

end GeneralBKForward

/-!
# The general Blanchard–Kahn theorem

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 (Props. C.1, C.2 and footnotes
1–2), which *assumes* the counting rule of Blanchard and Kahn (1980). This module proves the
general rule, for any number of predetermined and non-predetermined variables and any
`ExpectationSystem` (perfect foresight and genuine uncertainty alike), with existence and
uniqueness among bounded adapted processes.

## Setting

The state is `y_t = (z_t, x_t)` with index type `Z ⊕ X`: `z_t` non-predetermined, `x_t`
predetermined. `E_t y_{t+1} = A y_t + w_t` (`Solves`) for a real matrix `A`; an equilibrium
(`Equil`) is a bounded adapted solution whose predetermined block `x_{t+1}` is known at date `t`
and starts at the given `x_0`. `Determinate`: for every bounded adapted forcing `w` and every
`x_0` there is exactly one equilibrium.

## Main results

* `determinate_of` (**sufficiency**, any `ExpectationSystem`): no eigenvalue of `A` on the unit
  circle (`NoUnit`), the bounded-orbit (stable) subspace of dimension `|X|`, and genericity
  (`GenericX`: the stable subspace meets `{x = 0}` only in `0`) imply determinacy. Proof: the
  stable subspace is the graph of `G` (`InvariantSplit.exists_graph`); `ẑ_t = z_t − G x_t` solves
  `E_t ẑ_{t+1} = C ẑ_t + ŵ_t` with all eigenvalues of `C` outside the closed disc, so it is the
  forward solution through `C⁻¹`; then `x_{t+1} = Λ x_t + A_xz ẑ_t + w^x_t` with `Λ` stable is
  solved backward from `x_0`.
* Necessity, for every `ExpectationSystem` on a nonempty state space, failure by failure:
  - an eigenvalue on the unit circle gives **non-existence** by resonance: a bounded
    deterministic forcing `w_t = Re(μ^{t+1} b)` admits no bounded solution at all
    (`nonexist_of_unit`);
  - a failure of genericity gives **non-uniqueness**: next to every equilibrium there is another
    one, obtained by adding a bounded orbit with `x_0 = 0` (`mult_of_not_genericX`); this
    covers a stable subspace of dimension larger than `|X|` (`InvariantSplit.not_genericX_of_lt`);
  - a stable subspace of dimension smaller than `|X|` gives **non-existence** for some `x_0`
    already with `w = 0` (`nonexist_of_lt`).
* `determinate_iff` (**the Blanchard–Kahn theorem**): `Determinate ↔ NoUnit ∧ dim = |X| ∧ GenericX`;
  `determinate_iff_count`: the same with the dimension replaced by the number of eigenvalues in
  the open unit disc counted with algebraic multiplicity (`stableCount A = |X|`);
  `determinate_iff_unstableCount`: equivalently `|Z|` eigenvalues outside the closed disc.
* `determinate_iff_perfectForesight`: determinacy does not depend on the expectation system.
* `mem_boundedOrbits_iff_tendsto_of_noUnit`: with no eigenvalue on the unit circle the
  bounded-orbit subspace is the stable invariant subspace `{v : Aᵗ v → 0}`, and its dimension is
  the number of stable eigenvalues (`InvariantSplit.finrank_eq_stableCount`), so (ii) can be read
  either way.
-/

namespace GeneralBK

open Filter Topology InvariantSplit GeneralBKForward
open scoped Matrix

/-! ### Small tools -/

/-- Woodford (2003), App. C.1, p. 670 (tool): a complexified real vector under a complexified
real matrix. -/
theorem map_ofReal_mulVec {m n : Type*} [Fintype n] (K : Matrix m n ℝ) (v : n → ℝ) :
    K.map Complex.ofReal *ᵥ (fun i => (v i : ℂ)) = fun i => ((K *ᵥ v) i : ℂ) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Complex.ofReal_sum]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Woodford (2003), App. C.1, p. 670 (tool): a matrix with all eigenvalues outside the closed
unit disc is invertible. -/
theorem det_ne_zero_of_unstable {K : Matrix κ κ ℝ} (h : ∀ μ ∈ eigs K, 1 < ‖μ‖) : K.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have h0 : (0 : ℂ) ∈ eigs K := by
    refine mem_eigs_of_eigvec (c := fun i => (v i : ℂ)) ?_ ?_
    · intro hc
      apply hv0
      funext i
      have := congrFun hc i
      simpa using this
    · rw [map_ofReal_mulVec, hv]
      funext i
      simp
  have := h 0 h0
  norm_num at this

/-- Woodford (2003), App. C.1, p. 670 (tool): if every eigenvalue of `K` lies outside the closed
unit disc, every eigenvalue of `K⁻¹` lies in the open disc. -/
theorem inv_stable {K : Matrix κ κ ℝ} (h : ∀ μ ∈ eigs K, 1 < ‖μ‖) : ∀ μ ∈ eigs K⁻¹, ‖μ‖ < 1 := by
  have hdet := det_ne_zero_of_unstable h
  have hKK : K * K⁻¹ = 1 := Matrix.mul_nonsing_inv K (isUnit_iff_ne_zero.mpr hdet)
  intro μ hμ
  obtain ⟨c, hc0, hc⟩ := exists_eigvec hμ
  have hmap : K.map Complex.ofReal * K⁻¹.map Complex.ofReal = 1 := by
    have e : (K * K⁻¹).map Complex.ofReal = K.map Complex.ofReal * K⁻¹.map Complex.ofReal :=
      Matrix.map_mul (f := Complex.ofRealHom)
    rw [← e, hKK]
    exact Matrix.map_one _ (by simp) (by simp)
  have hc' : μ • (K.map Complex.ofReal *ᵥ c) = c := by
    calc μ • (K.map Complex.ofReal *ᵥ c) = K.map Complex.ofReal *ᵥ (μ • c) :=
          (Matrix.mulVec_smul _ _ _).symm
      _ = (K.map Complex.ofReal * K⁻¹.map Complex.ofReal) *ᵥ c := by
          rw [← hc, Matrix.mulVec_mulVec]
      _ = c := by rw [hmap, Matrix.one_mulVec]
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hc0
    rw [← hc', h0, zero_smul]
  have hev : K.map Complex.ofReal *ᵥ c = μ⁻¹ • c := (eq_inv_smul_iff₀ hμ0).mpr hc'
  have h1 := h μ⁻¹ (mem_eigs_of_eigvec hc0 hev)
  rw [norm_inv] at h1
  exact (one_lt_inv₀ (norm_pos_iff.mpr hμ0)).mp h1

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): sums of bounded vector processes are bounded. -/
theorem boundedV_add {a b : ℕ → κ → Ω → ℝ} (ha : BoundedV a) (hb : BoundedV b) :
    BoundedV (fun t => a t + b t) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t i ω => (abs_add_le _ _).trans (add_le_add (hA t i ω) (hB t i ω))⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): differences of bounded vector processes are
bounded. -/
theorem boundedV_sub {a b : ℕ → κ → Ω → ℝ} (ha : BoundedV a) (hb : BoundedV b) :
    BoundedV (fun t => a t - b t) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t i ω => (abs_sub _ _).trans (add_le_add (hA t i ω) (hB t i ω))⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): negatives of bounded vector processes are
bounded. -/
theorem boundedV_neg {a : ℕ → κ → Ω → ℝ} (ha : BoundedV a) : BoundedV (fun t => -a t) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun t i ω => by simpa using hA t i ω⟩

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): sums of adapted vector processes are adapted. -/
theorem adaptedV_add {a b : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) (hb : AdaptedV 𝔼 b) :
    AdaptedV 𝔼 (fun t => a t + b t) := fun t i => by
  simp only [Pi.add_apply, map_add, ha t i, hb t i]

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): differences of adapted vector processes are
adapted. -/
theorem adaptedV_sub {a b : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) (hb : AdaptedV 𝔼 b) :
    AdaptedV 𝔼 (fun t => a t - b t) := fun t i => by
  simp only [Pi.sub_apply, map_sub, ha t i, hb t i]

omit [Fintype κ] [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): negatives of adapted vector processes are
adapted. -/
theorem adaptedV_neg {a : ℕ → κ → Ω → ℝ} (ha : AdaptedV 𝔼 a) : AdaptedV 𝔼 (fun t => -a t) :=
  fun t i => by simp only [Pi.neg_apply, map_neg, ha t i]

/-! ### The system -/

/-- Woodford (2003), (C.19) and App. C.1, p. 670: `y` solves `E_t y_{t+1} = A y_t + w_t`. -/
def Solves {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (w y : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (y (t + 1) i) = mv A (y t) i + w t i

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, pp. 670–672 (Blanchard and Kahn 1980): a (bounded) rational
expectations equilibrium of `E_t y_{t+1} = A y_t + w_t` with state `y = (z, x)`: `y` solves the
system, is adapted and bounded, the predetermined block `x_{t+1}` is known at date `t`, and
`x_0` is the given vector. -/
def Equil (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (w : ℕ → Z ⊕ X → Ω → ℝ) (x0 : X → ℝ)
    (y : ℕ → Z ⊕ X → Ω → ℝ) : Prop :=
  Solves 𝔼 A w y ∧ AdaptedV 𝔼 y ∧
    (∀ t j, 𝔼.E t (y (t + 1) (Sum.inr j)) = y (t + 1) (Sum.inr j)) ∧
    (∀ j, y 0 (Sum.inr j) = fun _ => x0 j) ∧ BoundedV y

/-- Woodford (2003), App. C.1, p. 670 (determinacy, Blanchard and Kahn 1980): for every bounded
adapted forcing and every initial value of the predetermined variables there is exactly one
bounded equilibrium. -/
def Determinate (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ w : ℕ → Z ⊕ X → Ω → ℝ, BoundedV w → AdaptedV 𝔼 w → ∀ x0 : X → ℝ, ∃! y, Equil 𝔼 A w x0 y

omit [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670 (tool): a random state vector at a fixed outcome, split
into its blocks. -/
theorem eval_split (y : Z ⊕ X → Ω → ℝ) (ω : Ω) :
    (fun k => y k ω) = Sum.elim (fun i => y (Sum.inl i) ω) (fun j => y (Sum.inr j) ω) := by
  funext k
  rcases k with i | j <;> rfl

/-! ### Identities behind the change of variables `ẑ = z − G x` -/

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the rows of `A y` for the non-predetermined block,
`(A y)_z = A_zz z + A_zx x`. -/
theorem mv_inl (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (y : Z ⊕ X → Ω → ℝ) :
    (fun i => mv A y (Sum.inl i)) =
      mv A.toBlocks₁₁ (fun i => y (Sum.inl i)) + mv A.toBlocks₁₂ (fun j => y (Sum.inr j)) := by
  funext i
  simp only [mv, Fintype.sum_sum_type, Pi.add_apply]
  rfl

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the rows of `A y` for the predetermined block,
`(A y)_x = A_xz z + A_xx x`. -/
theorem mv_inr (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (y : Z ⊕ X → Ω → ℝ) :
    (fun j => mv A y (Sum.inr j)) =
      mv A.toBlocks₂₁ (fun i => y (Sum.inl i)) + mv A.toBlocks₂₂ (fun j => y (Sum.inr j)) := by
  funext j
  simp only [mv, Fintype.sum_sum_type, Pi.add_apply]
  rfl

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (tool): the invariance of the graph solved for `A_zx`:
`A_zx = G A_xz G + G A_xx − A_zz G`. -/
theorem zx_block_eq {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) :
    A.toBlocks₁₂ = G * A.toBlocks₂₁ * G + G * A.toBlocks₂₂ - A.toBlocks₁₁ * G := by
  rw [eq_sub_iff_add_eq, add_comm, hinv, lam, Matrix.mul_add, Matrix.mul_assoc]

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (uniqueness step): for random `(z, x)`,
`A_zz z + A_zx x + w^z − G (A_xz z + A_xx x + w^x) = C (z − G x) + (w^z − G w^x)`. -/
theorem identity_zhat {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (z wz : Z → Ω → ℝ)
    (x wx : X → Ω → ℝ) :
    mv A.toBlocks₁₁ z + mv A.toBlocks₁₂ x + wz -
        mv G (mv A.toBlocks₂₁ z + mv A.toBlocks₂₂ x + wx) =
      mv (cmat A G) (z - mv G x) + (wz - mv G wx) := by
  rw [zx_block_eq hinv, cmat]
  simp only [add_mv, sub_mv, mv_add, mv_sub, ← mv_mv]
  abel

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (the predetermined block):
`A_xz z + A_xx x = A_xz (z − G x) + Λ x`. -/
theorem identity_x (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) (z : Z → Ω → ℝ)
    (x : X → Ω → ℝ) :
    mv A.toBlocks₂₁ z + mv A.toBlocks₂₂ x = mv A.toBlocks₂₁ (z - mv G x) + mv (lam A G) x := by
  rw [lam]
  simp only [add_mv, mv_sub, ← mv_mv]
  abel

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (existence step): with `z = ẑ + G x`,
`C ẑ + (w^z − G w^x) + G (Λ x + (A_xz ẑ + w^x)) = A_zz z + A_zx x + w^z`. -/
theorem identity_exist {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ}
    (hinv : A.toBlocks₁₁ * G + A.toBlocks₁₂ = G * lam A G) (a wz : Z → Ω → ℝ)
    (b c : X → Ω → ℝ) :
    mv (cmat A G) a + (wz - mv G c) + mv G (mv (lam A G) b + (mv A.toBlocks₂₁ a + c)) =
      mv A.toBlocks₁₁ (a + mv G b) + mv A.toBlocks₁₂ b + wz := by
  rw [zx_block_eq hinv, cmat, lam]
  simp only [add_mv, sub_mv, mv_add, ← mv_mv]
  abel_nf

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672 (existence step, predetermined block):
`Λ x + (A_xz ẑ + w^x) = A_xz (ẑ + G x) + A_xx x + w^x`. -/
theorem identity_exist_x (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) (G : Matrix Z X ℝ) (a : Z → Ω → ℝ)
    (b c : X → Ω → ℝ) :
    mv (lam A G) b + (mv A.toBlocks₂₁ a + c) =
      mv A.toBlocks₂₁ (a + mv G b) + mv A.toBlocks₂₂ b + c := by
  rw [lam]
  simp only [add_mv, mv_add, ← mv_mv]
  abel

/-! ### The backward recursion for the predetermined block -/

/-- Woodford (2003), App. C.1, p. 672: the predetermined block `x_{t+1} = Λ x_t + g_t`,
`x_0` given, as a process of random variables. -/
def xrecR (L : Matrix X X ℝ) (g : ℕ → X → Ω → ℝ) (x0 : X → ℝ) : ℕ → X → Ω → ℝ
  | 0 => fun j _ => x0 j
  | t + 1 => mv L (xrecR L g x0 t) + g t

omit [DecidableEq Z] in
/-- Woodford (2003), App. C.1, p. 672: the backward recursion is bounded when `Λ` is stable and
`g` is bounded. -/
theorem xrecR_bounded {L : Matrix X X ℝ} (hL : ∀ μ ∈ eigs L, ‖μ‖ < 1) {g : ℕ → X → Ω → ℝ}
    (hg : BoundedV g) (x0 : X → ℝ) : BoundedV (xrecR L g x0) := by
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hLp⟩ := pow_entry_bound L hL
  obtain ⟨F, hF⟩ := hg
  refine ⟨Fintype.card X * Cb * (∑ j, |x0 j| + max F 0 / (1 - ρ)), fun t j ω => ?_⟩
  have hrec : ∀ t, (fun j => xrecR L g x0 (t + 1) j ω) =
      L *ᵥ (fun j => xrecR L g x0 t j ω) + fun j => g t j ω := by
    intro t
    funext j
    simp only [xrecR, Pi.add_apply, mv_apply]
  exact rec_bounded (x := fun t j => xrecR L g x0 t j ω) (f := fun t j => g t j ω) hCb hρ0.le
    hρ1 hLp hrec (le_max_right _ _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (fun t j => (hF t j ω).trans (le_max_left _ _))
    (fun j => Finset.single_le_sum (f := fun j => |x0 j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)) t j

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 672: the backward recursion is known one period ahead:
`x_t` is known at `t` and so is `x_{t+1}` (when `g` is adapted). -/
theorem xrecR_known {L : Matrix X X ℝ} {g : ℕ → X → Ω → ℝ} (hg : AdaptedV 𝔼 g) (x0 : X → ℝ) :
    ∀ t j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j ∧
      𝔼.E t (xrecR L g x0 (t + 1) j) = xrecR L g x0 (t + 1) j := by
  have hnext : ∀ t, (∀ j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j) →
      ∀ j, 𝔼.E t (xrecR L g x0 (t + 1) j) = xrecR L g x0 (t + 1) j := by
    intro t ht j
    simp only [xrecR, Pi.add_apply, map_add, E_mv 𝔼, hg t j]
    congr 2
    funext k
    exact ht k
  have hcur : ∀ t j, 𝔼.E t (xrecR L g x0 t j) = xrecR L g x0 t j := by
    intro t
    induction t with
    | zero => intro j; exact 𝔼.const 0 (x0 j)
    | succ t ih =>
      intro j
      rw [← hnext t ih j, 𝔼.known (Nat.le_succ t)]
  exact fun t j => ⟨hcur t j, hnext t (hcur t) j⟩

/-! ### Sufficiency -/

/-- Woodford (2003), App. C.1, p. 672 (tool): with `K C = C K = 1`, the forward form
`ẑ_t = K E_t ẑ_{t+1} − K ŵ_t` is the system `E_t ẑ_{t+1} = C ẑ_t + ŵ_t`. -/
theorem fsolves_iff_cform {C K : Matrix Z Z ℝ} (hKC : K * C = 1) (hCK : C * K = 1)
    (wh zh : ℕ → Z → Ω → ℝ) :
    FSolves 𝔼 K (fun t => -mv K (wh t)) zh ↔
      ∀ t, (fun i => 𝔼.E t (zh (t + 1) i)) = mv C (zh t) + wh t := by
  constructor
  · intro h t
    have e := congrArg (mv C) (h t)
    rw [mv_add, mv_neg, mv_mv, mv_mv, hCK, mv_one, mv_one] at e
    rw [e]
    abel
  · intro h t
    simp only [h t, mv_add, mv_mv, hKC, mv_one, add_neg_cancel_right]

/-- **Blanchard–Kahn, sufficiency** (Woodford (2003), App. C.1, p. 670; Blanchard and Kahn 1980):
for any expectation system, if no eigenvalue of `A` lies on the unit circle, the stable
(bounded-orbit) subspace has dimension equal to the number of predetermined variables, and it
meets `{x = 0}` only in `0`, then for every bounded adapted forcing and every `x_0` there is
exactly one bounded equilibrium. -/
theorem determinate_of {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A)
    (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X) (hg : GenericX A) :
    Determinate 𝔼 A := by
  obtain ⟨G, hG⟩ := exists_graph hd hg
  have hinv := graph_invariant hG
  have hΛ := lam_stable hG hnu
  have hC := cmat_unstable hG hg hΛ
  have hdet : IsUnit (cmat A G).det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_unstable hC)
  have hKC : (cmat A G)⁻¹ * cmat A G = 1 := Matrix.nonsing_inv_mul _ hdet
  have hCK : cmat A G * (cmat A G)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  obtain ⟨CbK, ρK, -, hρK0, hρK1, hKpow⟩ := pow_entry_bound _ (inv_stable hC)
  intro w hwb hwa x0
  set wz : ℕ → Z → Ω → ℝ := fun t i => w t (Sum.inl i) with hwz
  set wx : ℕ → X → Ω → ℝ := fun t j => w t (Sum.inr j) with hwx
  have hwzb : BoundedV wz := by
    obtain ⟨M, hM⟩ := hwb; exact ⟨M, fun t i ω => hM t _ ω⟩
  have hwxb : BoundedV wx := by
    obtain ⟨M, hM⟩ := hwb; exact ⟨M, fun t j ω => hM t _ ω⟩
  have hwzA : AdaptedV 𝔼 wz := fun t i => hwa t (Sum.inl i)
  have hwxA : AdaptedV 𝔼 wx := fun t j => hwa t (Sum.inr j)
  set wh : ℕ → Z → Ω → ℝ := fun t => wz t - mv G (wx t) with hwh
  have hwhb : BoundedV wh := boundedV_sub hwzb (boundedV_mv G hwxb)
  have hwhA : AdaptedV 𝔼 wh := adaptedV_sub 𝔼 hwzA (adaptedV_mv 𝔼 G hwxA)
  have hfb : BoundedV (fun t => -mv (cmat A G)⁻¹ (wh t)) :=
    boundedV_neg (boundedV_mv _ hwhb)
  have hfA : AdaptedV 𝔼 (fun t => -mv (cmat A G)⁻¹ (wh t)) :=
    adaptedV_neg 𝔼 (adaptedV_mv 𝔼 _ hwhA)
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨zh, hzh, hzhA, hzhb⟩ := fsolves_exists 𝔼 hρK0.le hρK1 hKpow hMf hfA
  have hzhE := (fsolves_iff_cform 𝔼 hKC hCK wh zh).mp hzh
  set g : ℕ → X → Ω → ℝ := fun t => mv A.toBlocks₂₁ (zh t) + wx t with hgdef
  have hgA : AdaptedV 𝔼 g := adaptedV_add 𝔼 (adaptedV_mv 𝔼 _ hzhA) hwxA
  have hgb : BoundedV g := boundedV_add (boundedV_mv _ hzhb) hwxb
  set xr := xrecR (lam A G) g x0 with hxr
  have hxrb : BoundedV xr := xrecR_bounded hΛ hgb x0
  have hxrK := xrecR_known 𝔼 (L := lam A G) hgA x0
  have hxr1 : ∀ t, xr (t + 1) = mv (lam A G) (xr t) + g t := fun t => rfl
  set y : ℕ → Z ⊕ X → Ω → ℝ := fun t => Sum.elim (zh t + mv G (xr t)) (xr t) with hy
  have hyz : ∀ t, (fun i => y t (Sum.inl i)) = zh t + mv G (xr t) := fun t => rfl
  have hyx : ∀ t, (fun j => y t (Sum.inr j)) = xr t := fun t => rfl
  -- every equilibrium is `y`
  have huniq : ∀ y', Equil 𝔼 A w x0 y' → y' = y := by
    rintro y' ⟨hs, ha, hk, h0, hb⟩
    set zh' : ℕ → Z → Ω → ℝ :=
      fun t => (fun i => y' t (Sum.inl i)) - mv G (fun j => y' t (Sum.inr j)) with hzh'
    have hzh'A : AdaptedV 𝔼 zh' :=
      adaptedV_sub 𝔼 (fun t i => ha t (Sum.inl i))
        (adaptedV_mv 𝔼 G (fun t j => ha t (Sum.inr j)))
    have hb1 : BoundedV (fun t i => y' t (Sum.inl i)) := by
      obtain ⟨M, hM⟩ := hb; exact ⟨M, fun t i ω => hM t _ ω⟩
    have hb2 : BoundedV (fun t j => y' t (Sum.inr j)) := by
      obtain ⟨M, hM⟩ := hb; exact ⟨M, fun t j ω => hM t _ ω⟩
    have hzh'b : BoundedV zh' := boundedV_sub hb1 (boundedV_mv G hb2)
    have hEz : ∀ t, (fun i => 𝔼.E t (y' (t + 1) (Sum.inl i))) =
        (fun i => mv A (y' t) (Sum.inl i)) + wz t := fun t => by
      funext i; rw [hs t]; rfl
    have hEx : ∀ t, (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) =
        (fun j => mv A (y' t) (Sum.inr j)) + wx t := fun t => by
      funext j; rw [hs t]; rfl
    have hcf : ∀ t, (fun i => 𝔼.E t (zh' (t + 1) i)) = mv (cmat A G) (zh' t) + wh t := by
      intro t
      have hE : (fun i => 𝔼.E t (zh' (t + 1) i)) =
          (fun i => 𝔼.E t (y' (t + 1) (Sum.inl i))) -
            mv G (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) := by
        funext i
        simp only [hzh', Pi.sub_apply, map_sub, E_mv 𝔼]
      rw [hE, hEz, hEx, mv_inl, mv_inr, identity_zhat hinv]
    have hzz : zh' = zh :=
      fsolves_unique 𝔼 hρK0.le hρK1 hKpow ((fsolves_iff_cform 𝔼 hKC hCK wh zh').mpr hcf) hzh
        hzh'A hzhA hzh'b ⟨_, hzhb.choose_spec⟩
    have hxx : ∀ t, (fun j => y' t (Sum.inr j)) = xr t := by
      intro t
      induction t with
      | zero => funext j; exact h0 j
      | succ t ih =>
        have e1 : (fun j => y' (t + 1) (Sum.inr j)) =
            (fun j => 𝔼.E t (y' (t + 1) (Sum.inr j))) := by
          funext j; exact (hk t j).symm
        have hz't : (fun i => y' t (Sum.inl i)) - mv G (fun j => y' t (Sum.inr j)) = zh' t := rfl
        rw [e1, hEx, mv_inr, identity_x A G, hz't, hzz, ih, hxr1]
        simp only [hgdef]
        abel
    funext t k
    rcases k with i | j
    · have e := congrFun (congrArg (fun f => f t) hzz) i
      simp only [hzh', Pi.sub_apply, hxx t] at e
      have e2 : y' t (Sum.inl i) = zh t i + mv G (xr t) i := by
        rw [← e]; abel
      rw [e2]
      rfl
    · exact congrFun (hxx t) j
  refine ⟨y, ⟨?_, ?_, ?_, ?_, ?_⟩, huniq⟩
  · -- the system
    intro t k
    rcases k with i | j
    · have hv : (fun i => 𝔼.E t (y (t + 1) (Sum.inl i))) =
          (fun i => mv A (y t) (Sum.inl i)) + wz t := by
        have e1 : (fun i => 𝔼.E t (y (t + 1) (Sum.inl i))) =
            (fun i => 𝔼.E t (zh (t + 1) i)) + mv G (fun j => 𝔼.E t (xr (t + 1) j)) := by
          funext i
          simp only [hy, Sum.elim_inl, Pi.add_apply, map_add, E_mv 𝔼]
        have e2 : (fun j => 𝔼.E t (xr (t + 1) j)) = xr (t + 1) := by
          funext j; exact (hxrK t j).2
        rw [e1, e2, hzhE t, hxr1, mv_inl, hyz, hyx, hwh, hgdef]
        exact identity_exist hinv _ _ _ _
      exact congrFun hv i
    · have hv : (fun j => 𝔼.E t (y (t + 1) (Sum.inr j))) =
          (fun j => mv A (y t) (Sum.inr j)) + wx t := by
        have e1 : (fun j => 𝔼.E t (y (t + 1) (Sum.inr j))) = xr (t + 1) := by
          funext j; exact (hxrK t j).2
        rw [e1, hxr1, mv_inr, hyz, hyx, hgdef]
        exact identity_exist_x A G _ _ _
      exact congrFun hv j
  · -- adapted
    intro t k
    rcases k with i | j
    · simp only [hy, Sum.elim_inl, Pi.add_apply, map_add, E_mv 𝔼, hzhA t i]
      congr 2
      funext j
      exact (hxrK t j).1
    · exact (hxrK t j).1
  · -- the predetermined block is known one period ahead
    intro t j
    exact (hxrK t j).2
  · -- the initial condition
    intro j
    rfl
  · -- boundedness
    obtain ⟨Mz, hMz⟩ := hzhb
    obtain ⟨Mx, hMx⟩ := hxrb
    obtain ⟨Mg, hMg⟩ := boundedV_mv G ⟨Mx, hMx⟩
    refine ⟨max (Mz + Mg) Mx, fun t k ω => ?_⟩
    rcases k with i | j
    · change |zh t i ω + mv G (xr t) i ω| ≤ _
      exact ((abs_add_le _ _).trans (add_le_add (hMz t i ω) (hMg t i ω))).trans
        (le_max_left _ _)
    · exact (hMx t j ω).trans (le_max_right _ _)

/-! ### Necessity (i): an eigenvalue on the unit circle gives non-existence by resonance -/

open ComplexConjugate

omit [DecidableEq κ] in
/-- Woodford (2003), App. C.1, p. 670 (tool): for a left eigenvector `q A = μ q`,
`q · (A e) = μ (q · e)`. -/
theorem sum_q_mulVec {A : Matrix κ κ ℝ} {μ : ℂ} {q : κ → ℂ}
    (hq : q ᵥ* A.map Complex.ofReal = μ • q) (e : κ → ℝ) :
    ∑ i, q i * ((A *ᵥ e) i : ℂ) = μ * ∑ j, q j * (e j : ℂ) := by
  have hcol : ∀ j, ∑ i, q i * (A i j : ℂ) = μ * q j := fun j => by
    have := congrFun hq j
    simpa [Matrix.vecMul, dotProduct] using this
  simp only [Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hcol j, mul_assoc]

/-- Woodford (2003), App. C.1, p. 670 (tool): a linear lower bound `a + T c − K` with `c > 0`
cannot stay below a constant. -/
theorem false_of_linear_growth {a c K Q : ℝ} (hc : 0 < c) (h : ∀ T : ℕ, a + T * c - K ≤ Q) :
    False := by
  obtain ⟨T, hT⟩ := exists_nat_gt ((Q + K - a) / c)
  have := h T
  rw [div_lt_iff₀ hc] at hT
  linarith

omit [DecidableEq κ] in
/-- **Resonance** (Woodford (2003), App. C.1, p. 670, fn. 1: the boundary case): let `‖μ‖ = 1`
and `q A = μ q`, `q ≠ 0` (with `q` real when `μ = ±1`). Then the deterministic system
`e_{t+1} = A e_t + w_t` with the bounded forcing `w_{t,i} = Re(μ^{t+1} q̄_i)` has no bounded
solution: `d_t = (q · e_t) μ̄ᵗ` grows like `t ∑|q_i|²/2`. -/
theorem no_bounded_resonance {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : ‖μ‖ = 1) {q : κ → ℂ}
    (hq0 : q ≠ 0) (hq : q ᵥ* A.map Complex.ofReal = μ • q)
    (hre : μ ^ 2 = 1 → ∀ i, (q i).im = 0) {e : ℕ → κ → ℝ}
    (he : ∀ t, e (t + 1) = A *ᵥ e t + fun i => (μ ^ (t + 1) * conj (q i)).re)
    {B : ℝ} (hB : ∀ t i, |e t i| ≤ B) : False := by
  set m : ℕ → ℂ := fun t => ∑ i, q i * (e t i : ℂ) with hm
  set N : ℝ := ∑ i, ‖q i‖ ^ 2 with hN
  set σ : ℂ := ∑ i, q i ^ 2 with hσ
  set ζ : ℂ := conj μ ^ 2 with hζ
  have hμc : μ * conj μ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ]
    norm_num
  have hN0 : 0 < N := by
    obtain ⟨i, hi⟩ : ∃ i, q i ≠ 0 := by
      by_contra hne
      push Not at hne
      exact hq0 (funext hne)
    exact Finset.sum_pos' (fun i _ => by positivity)
      ⟨i, Finset.mem_univ i, by have := norm_pos_iff.mpr hi; positivity⟩
  have hNc : (N : ℂ) = ∑ i, q i * conj (q i) := by
    rw [hN]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hqw : ∀ t, ∑ i, q i * (((μ ^ (t + 1) * conj (q i)).re : ℝ) : ℂ) =
      (μ ^ (t + 1) * (N : ℂ) + conj μ ^ (t + 1) * σ) / 2 := by
    intro t
    rw [hNc, hσ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_eq_add_conj, map_mul, map_pow, Complex.conj_conj]
    ring
  have hm_succ : ∀ t, m (t + 1) = μ * m t + (μ ^ (t + 1) * (N : ℂ) + conj μ ^ (t + 1) * σ) / 2 := by
    intro t
    simp only [hm, he t, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]
    rw [sum_q_mulVec hq, hqw]
  set d : ℕ → ℂ := fun t => m t * conj μ ^ t with hd
  have hd_succ : ∀ t, d (t + 1) = d t + ((N : ℂ) + σ * ζ ^ (t + 1)) / 2 := by
    intro t
    have h1 : μ ^ (t + 1) * conj μ ^ (t + 1) = 1 := by rw [← mul_pow, hμc, one_pow]
    have h2 : μ * conj μ ^ (t + 1) = conj μ ^ t := by
      rw [pow_succ]
      linear_combination (conj μ ^ t) * hμc
    have h3 : conj μ ^ (t + 1) * conj μ ^ (t + 1) = ζ ^ (t + 1) := by
      rw [hζ, ← pow_mul, ← pow_add]
      ring_nf
    simp only [hd]
    rw [hm_succ t]
    linear_combination (m t) * h2 + ((N : ℂ) / 2) * h1 + (σ / 2) * h3
  set S : ℕ → ℂ := fun T => ∑ s ∈ Finset.range T, ζ ^ (s + 1) with hS
  have hd_closed : ∀ T : ℕ, d T = d 0 + ((T * N / 2 : ℝ) : ℂ) + σ / 2 * S T := by
    intro T
    induction T with
    | zero => simp [hS]
    | succ T ih =>
      rw [hd_succ T, ih]
      simp only [hS, Finset.sum_range_succ]
      push_cast
      ring
  set Q : ℝ := ∑ i, ‖q i‖ * B with hQ
  have hdQ : ∀ T, ‖d T‖ ≤ Q := by
    intro T
    simp only [hd, hm, norm_mul, norm_pow, Complex.norm_conj, hμ, one_pow, mul_one]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB T i) (norm_nonneg _)
  -- the oscillating part is bounded below
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ T, -K ≤ (σ / 2 * S T).re := by
    by_cases hζ1 : ζ = 1
    · have hμ2 : μ ^ 2 = 1 := by
        have := congrArg conj hζ1
        rw [hζ, map_pow, Complex.conj_conj, map_one] at this
        exact this
      have hreal := hre hμ2
      have hσN : σ = (N : ℂ) := by
        rw [hσ, hNc]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hqi : q i = ((q i).re : ℂ) := Complex.ext rfl (by simp [hreal i])
        rw [hqi, Complex.conj_ofReal]
        ring
      refine ⟨0, fun T => ?_⟩
      have hST : S T = (T : ℂ) := by simp [hS, hζ1]
      rw [hσN, hST]
      have : ((N : ℂ) / 2 * (T : ℂ)).re = N / 2 * T := by
        rw [show ((N : ℂ) / 2 * (T : ℂ)) = ((N / 2 * T : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
      rw [this]
      have : 0 ≤ N / 2 * T := by positivity
      linarith
    · have hζn : ‖ζ‖ = 1 := by rw [hζ, norm_pow, Complex.norm_conj, hμ, one_pow]
      have hζ1' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
      refine ⟨‖σ‖ / ‖ζ - 1‖, fun T => ?_⟩
      have hSb : ‖S T‖ ≤ 2 / ‖ζ - 1‖ := by
        have e : S T = ζ * ((ζ ^ T - 1) / (ζ - 1)) := by
          rw [hS, ← geom_sum_eq hζ1 T, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
        rw [e, norm_mul, hζn, one_mul, norm_div]
        refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖ζ ^ T - 1‖ ≤ ‖ζ ^ T‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hζn, one_pow, norm_one]; norm_num
      have hb : ‖σ / 2 * S T‖ ≤ ‖σ‖ / ‖ζ - 1‖ := by
        rw [norm_mul, norm_div, Complex.norm_two]
        calc ‖σ‖ / 2 * ‖S T‖ ≤ ‖σ‖ / 2 * (2 / ‖ζ - 1‖) :=
              mul_le_mul_of_nonneg_left hSb (by positivity)
          _ = ‖σ‖ / ‖ζ - 1‖ := by ring
      have := Complex.abs_re_le_norm (σ / 2 * S T)
      have := neg_abs_le (σ / 2 * S T).re
      linarith
  refine false_of_linear_growth (a := (d 0).re) (c := N / 2) (K := K) (Q := Q)
    (by positivity) fun T => ?_
  have h1 : (d T).re = (d 0).re + T * N / 2 + (σ / 2 * S T).re := by
    rw [hd_closed T, Complex.add_re, Complex.add_re, Complex.ofReal_re]
  have h2 : (d T).re ≤ Q := (Complex.re_le_norm _).trans (hdQ T)
  have h3 := hK T
  have : (T : ℝ) * (N / 2) = T * N / 2 := by ring
  linarith

/-- Woodford (2003), App. C.1, p. 670 (tool): an eigenvalue on the unit circle has a left
eigenvector, which can be chosen real when the eigenvalue is `±1`. -/
theorem exists_left_eigvec_unit {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : μ ∈ eigs A) :
    ∃ q : κ → ℂ, q ≠ 0 ∧ q ᵥ* A.map Complex.ofReal = μ • q ∧
      (μ ^ 2 = 1 → ∀ i, (q i).im = 0) := by
  by_cases h2 : μ ^ 2 = 1
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, μ = (r : ℂ) := by
      have : (μ - 1) * (μ + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.mp this with e | e
      · exact ⟨1, by push_cast; linear_combination e⟩
      · exact ⟨-1, by push_cast; linear_combination e⟩
    have hdetC := (mem_eigs_iff A μ).mp hμ
    have hmap : Matrix.scalar κ μ - A.map Complex.ofReal =
        (Matrix.scalar κ r - A).map Complex.ofReal := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hr]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
    have hdetR : (Matrix.scalar κ r - A).det = 0 := by
      have e := RingHom.map_det Complex.ofRealHom (Matrix.scalar κ r - A)
      rw [hmap] at hdetC
      have e2 : (Complex.ofRealHom.mapMatrix (Matrix.scalar κ r - A)) =
          (Matrix.scalar κ r - A).map Complex.ofReal := rfl
      rw [e2, hdetC] at e
      exact Complex.ofReal_eq_zero.mp e
    obtain ⟨p, hp0, hp⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdetR
    refine ⟨fun i => (p i : ℂ), ?_, ?_, fun _ i => by simp⟩
    · intro h
      apply hp0
      funext i
      have := congrFun h i
      simpa using this
    · rw [Matrix.vecMul_sub, sub_eq_zero] at hp
      funext j
      have hj := congrFun hp j
      have h1 : (p ᵥ* Matrix.scalar κ r) j = r * p j := by
        simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]
      have e : ∑ i, p i * A i j = r * p j := by
        calc ∑ i, p i * A i j = (p ᵥ* A) j := rfl
          _ = r * p j := hj.symm.trans h1
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, hr]
      exact_mod_cast e
  · obtain ⟨q, hq0, hq⟩ := exists_left_eigvec hμ
    exact ⟨q, hq0, hq, fun h => absurd h h2⟩

/-- **Non-existence at a unit-circle eigenvalue** (Woodford (2003), App. C.1, p. 670, fn. 1;
Blanchard and Kahn 1980): if `A` has an eigenvalue `μ` with `|μ| = 1`, there is a bounded
adapted (indeed deterministic) forcing, `w_{t,i} = Re(μ^{t+1} q̄_i)` for a left eigenvector `q`,
for which `E_t y_{t+1} = A y_t + w_t` has no bounded solution at all, adapted or not, whatever the
predetermined restrictions. Taking `E_0` of a solution reduces to `no_bounded_resonance`. -/
theorem nonexist_of_unit [Nonempty Ω] {A : Matrix κ κ ℝ} {μ : ℂ} (hμ : μ ∈ eigs A)
    (h1 : ‖μ‖ = 1) :
    ∃ w : ℕ → κ → Ω → ℝ, BoundedV w ∧ AdaptedV 𝔼 w ∧
      ∀ y, Solves 𝔼 A w y → BoundedV y → False := by
  obtain ⟨q, hq0, hq, hre⟩ := exists_left_eigvec_unit hμ
  refine ⟨fun t i _ => (μ ^ (t + 1) * conj (q i)).re, ⟨∑ i, ‖q i‖, fun t i _ => ?_⟩,
    fun t i => 𝔼.const t _, ?_⟩
  · refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow, h1, one_pow, one_mul, Complex.norm_conj]
    exact Finset.single_le_sum (f := fun i => ‖q i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)
  · rintro y hy ⟨B, hB⟩
    obtain ⟨ω₀⟩ := ‹Nonempty Ω›
    refine no_bounded_resonance h1 hq0 hq hre (e := fun t i => 𝔼.E 0 (y t i) ω₀) (fun t => ?_)
      (B := B) (fun t i => 𝔼.abs_E_le (hB t i) 0 ω₀)
    funext i
    have e1 : 𝔼.E 0 (y (t + 1) i) = 𝔼.E 0 (𝔼.E t (y (t + 1) i)) :=
      (𝔼.tower (Nat.zero_le t) _).symm
    rw [e1, hy t i, map_add, E_mv 𝔼, 𝔼.const, Pi.add_apply, Pi.add_apply, mv_apply]

/-- Woodford (2003), App. C.1, p. 670, fn. 1: with an eigenvalue on the unit circle the system is
not determinate (equilibrium fails to exist for some bounded forcing). -/
theorem not_determinate_of_unit [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {μ : ℂ}
    (hμ : μ ∈ eigs A) (h1 : ‖μ‖ = 1) : ¬ Determinate 𝔼 A := by
  intro hdet
  obtain ⟨w, hwb, hwa, hno⟩ := nonexist_of_unit 𝔼 hμ h1
  obtain ⟨y, ⟨hs, -, -, -, hb⟩, -⟩ := hdet w hwb hwa 0
  exact hno y hs hb

/-! ### Necessity (ii): genericity and the dimension of the stable subspace -/

/-- **Non-uniqueness without genericity** (Woodford (2003), App. C.1, p. 672, fn. 2; Blanchard
and Kahn 1980): if a nonzero bounded orbit `Aᵗ v` starts with `x = 0`, then next to every
equilibrium there is another one (add the deterministic path `Aᵗ v`). -/
theorem mult_of_not_genericX [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (h : ¬ GenericX A)
    {w : ℕ → Z ⊕ X → Ω → ℝ} {x0 : X → ℝ} {y : ℕ → Z ⊕ X → Ω → ℝ} (hy : Equil 𝔼 A w x0 y) :
    ∃ y', Equil 𝔼 A w x0 y' ∧ y' ≠ y := by
  unfold GenericX at h
  push Not at h
  obtain ⟨v, ⟨C, hC⟩, hvx, hv0⟩ := h
  obtain ⟨hs, ha, hk, h0, ⟨M, hM⟩⟩ := hy
  set y' : ℕ → Z ⊕ X → Ω → ℝ := fun t k => y t k + fun _ => (A ^ t *ᵥ v) k with hy'
  refine ⟨y', ⟨fun t k => ?_, fun t k => ?_, fun t j => ?_, fun j => ?_, ⟨M + C, ?_⟩⟩, ?_⟩
  · simp only [hy', map_add, 𝔼.const, hs t k]
    funext ω
    simp only [Pi.add_apply, mv_apply]
    rw [show (fun j => y t j ω + (A ^ t *ᵥ v) j) = (fun j => y t j ω) + A ^ t *ᵥ v from rfl,
      Matrix.mulVec_add, Pi.add_apply, Matrix.mulVec_mulVec, ← pow_succ']
    ring
  · simp only [hy', map_add, 𝔼.const, ha t k]
  · simp only [hy', map_add, 𝔼.const, hk t j]
  · simp only [hy', pow_zero, Matrix.one_mulVec, hvx j, h0 j]
    funext ω
    simp
  · intro t k ω
    exact (abs_add_le _ _).trans (add_le_add (hM t k ω) (hC t k))
  · intro he
    apply hv0
    funext k
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrFun he 0) k) ω
    simpa [hy'] using this

/-- Woodford (2003), App. C.1, p. 672, fn. 2: without genericity the system is not
determinate (already for `w = 0`, `x_0 = 0` there are two equilibria). -/
theorem not_determinate_of_not_genericX [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : ¬ GenericX A) : ¬ Determinate 𝔼 A := by
  intro hdet
  have hb0 : BoundedV (0 : ℕ → Z ⊕ X → Ω → ℝ) := ⟨0, fun _ _ _ => by simp⟩
  have ha0 : AdaptedV 𝔼 (0 : ℕ → Z ⊕ X → Ω → ℝ) := fun t k => by simp
  obtain ⟨y, hy, huniq⟩ := hdet 0 hb0 ha0 0
  obtain ⟨y', hy', hne⟩ := mult_of_not_genericX 𝔼 h hy
  exact hne (huniq y' hy')

/-- **Non-existence with too few stable directions** (Woodford (2003), App. C.1, p. 670;
Blanchard and Kahn 1980): if the bounded-orbit subspace has dimension below the number of
predetermined variables, some initial `x_0` admits no equilibrium even with `w = 0`. Taking
`E_0` of an equilibrium gives, outcome by outcome, a bounded orbit starting at `(z_0, x_0)`. -/
theorem nonexist_of_lt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) :
    ∃ x0 : X → ℝ, ∀ y, ¬ Equil 𝔼 A 0 x0 y := by
  obtain ⟨x0, hx0⟩ := exists_unreached_of_lt h
  refine ⟨x0, fun y hy => ?_⟩
  obtain ⟨hs, -, -, h0, ⟨M, hM⟩⟩ := hy
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  set e : ℕ → Z ⊕ X → ℝ := fun t k => 𝔼.E 0 (y t k) ω₀ with he
  have hstep : ∀ t, e (t + 1) = A *ᵥ e t := by
    intro t
    funext k
    have e1 : 𝔼.E 0 (y (t + 1) k) = 𝔼.E 0 (𝔼.E t (y (t + 1) k)) :=
      (𝔼.tower (Nat.zero_le t) _).symm
    simp only [he]
    rw [e1, hs t k, Pi.zero_apply, Pi.zero_apply, add_zero, E_mv 𝔼, mv_apply]
  have hmem := mem_boundedOrbits_of_orbit hstep (fun t k => 𝔼.abs_E_le (hM t k) 0 ω₀)
  apply hx0 _ hmem
  funext j
  simp only [he, h0 j, 𝔼.const]

/-- Woodford (2003), App. C.1, p. 670: too few stable directions — not determinate. -/
theorem not_determinate_of_lt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) : ¬ Determinate 𝔼 A := by
  intro hdet
  obtain ⟨x0, hx0⟩ := nonexist_of_lt 𝔼 h
  obtain ⟨y, hy, -⟩ := hdet 0 ⟨0, fun _ _ _ => by simp⟩ (fun t k => by simp) x0
  exact hx0 y hy

/-- Woodford (2003), App. C.1, p. 672, fn. 2: too many stable directions — not determinate
(genericity must fail, so equilibria are not unique). -/
theorem not_determinate_of_gt [Nonempty Ω] {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Fintype.card X < Module.finrank ℝ (boundedOrbits A)) : ¬ Determinate 𝔼 A :=
  not_determinate_of_not_genericX 𝔼 (not_genericX_of_lt h)

/-! ### The Blanchard–Kahn theorem -/

/-- **The Blanchard–Kahn theorem** (Woodford (2003), App. C.1, p. 670 and fn. 1–2, which the book
takes from Blanchard and Kahn (1980)): for any expectation system on a nonempty state space, the
system `E_t y_{t+1} = A y_t + w_t` with `|X|` predetermined variables is determinate iff
(i) no eigenvalue of `A` lies on the unit circle, (ii) the stable (bounded-orbit) subspace has
dimension `|X|`, and (iii) the stable subspace meets `{x = 0}` only in `0`. -/
theorem determinate_iff [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ Module.finrank ℝ (boundedOrbits A) = Fintype.card X ∧
      GenericX A := by
  constructor
  · intro hdet
    have hnu : NoUnit A := fun μ hμ h1 => not_determinate_of_unit 𝔼 hμ h1 hdet
    have hg : GenericX A := by
      by_contra hg
      exact not_determinate_of_not_genericX 𝔼 hg hdet
    refine ⟨hnu, ?_, hg⟩
    rcases lt_trichotomy (Module.finrank ℝ (boundedOrbits A)) (Fintype.card X) with h | h | h
    · exact absurd hdet (not_determinate_of_lt 𝔼 h)
    · exact h
    · exact absurd hdet (not_determinate_of_gt 𝔼 h)
  · rintro ⟨hnu, hd, hg⟩
    exact determinate_of 𝔼 hnu hd hg

/-- **The Blanchard–Kahn counting rule** (Woodford (2003), App. C.1, p. 670 and fn. 1–2; Blanchard
and Kahn 1980): determinate iff no eigenvalue on the unit circle, exactly `|X|` eigenvalues in the
open unit disc counted with algebraic multiplicity, and genericity. -/
theorem determinate_iff_count [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ stableCount A = Fintype.card X ∧ GenericX A := by
  rw [determinate_iff]
  constructor
  · rintro ⟨hnu, hd, hg⟩
    exact ⟨hnu, (finrank_eq_iff_stableCount_eq hnu hg).mp hd, hg⟩
  · rintro ⟨hnu, hc, hg⟩
    exact ⟨hnu, (finrank_eq_iff_stableCount_eq hnu hg).mpr hc, hg⟩

/-- **The Blanchard–Kahn counting rule, unstable form** (Woodford (2003), App. C.1, p. 670;
Blanchard and Kahn 1980): determinate iff no eigenvalue on the unit circle, exactly as many
eigenvalues outside the unit circle (with multiplicity) as non-predetermined variables, and
genericity. -/
theorem determinate_iff_unstableCount [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ NoUnit A ∧ unstableCount A = Fintype.card Z ∧ GenericX A := by
  rw [determinate_iff_count]
  constructor
  · rintro ⟨hnu, hc, hg⟩
    refine ⟨hnu, ?_, hg⟩
    have := stableCount_add_unstableCount hnu
    rw [Fintype.card_sum, hc] at this
    omega
  · rintro ⟨hnu, hc, hg⟩
    refine ⟨hnu, ?_, hg⟩
    have := stableCount_add_unstableCount hnu
    rw [Fintype.card_sum, hc] at this
    omega

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670: determinacy does not depend on the expectation system —
it holds under any expectation system on a nonempty state space iff it holds under perfect
foresight. -/
theorem determinate_iff_perfectForesight [Nonempty Ω] (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    Determinate 𝔼 A ↔ Determinate perfectForesight A := by
  classical
  rw [determinate_iff, determinate_iff]

/-! ### The bounded-orbit subspace is the stable subspace -/

/-- Woodford (2003), App. C.1, p. 670 (tool): a vector whose orbit tends to `0` has a bounded
orbit. -/
theorem mem_boundedOrbits_of_tendsto {A : Matrix κ κ ℝ} {v : κ → ℝ}
    (h : Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0)) : v ∈ boundedOrbits A := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto (fun t => A ^ t *ᵥ v) h)
  exact ⟨C, fun t i => (norm_le_pi_norm (A ^ t *ᵥ v) i).trans (hC _ ⟨t, rfl⟩) |>.trans' le_rfl⟩

/-- Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn 1980): with no eigenvalue on the unit
circle, the bounded-orbit subspace is exactly the stable subspace `{v : Aᵗ v → 0}`. -/
theorem mem_boundedOrbits_iff_tendsto_of_noUnit {A : Matrix κ κ ℝ} (hnu : NoUnit A)
    (v : κ → ℝ) : v ∈ boundedOrbits A ↔ Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0) :=
  ⟨tendsto_of_mem_boundedOrbits hnu, mem_boundedOrbits_of_tendsto⟩

/-- Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn 1980): under the Blanchard–Kahn
conditions every bounded orbit tends to `0` — the bounded-orbit subspace is exactly the stable
subspace `{v : Aᵗ v → 0}`. -/
theorem mem_boundedOrbits_iff_tendsto {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hnu : NoUnit A)
    (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X) (hg : GenericX A)
    (v : Z ⊕ X → ℝ) :
    v ∈ boundedOrbits A ↔ Tendsto (fun t => A ^ t *ᵥ v) atTop (𝓝 0) := by
  refine ⟨fun hv => ?_, mem_boundedOrbits_of_tendsto⟩
  obtain ⟨G, hG⟩ := exists_graph hd hg
  have hinv := graph_invariant hG
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hL⟩ := pow_entry_bound _ (lam_stable hG hnu)
  set x : X → ℝ := fun j => v (Sum.inr j) with hx
  have hvg : v = graphV G x := by
    funext k
    rcases k with i | j
    · exact hG.2 v hv i
    · rfl
  set Xb : ℝ := ∑ j, |x j| with hXb
  have hXb0 : 0 ≤ Xb := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hxj : ∀ j, |x j| ≤ Xb := fun j =>
    Finset.single_le_sum (f := fun j => |x j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
  set aG : ℝ := ∑ i, ∑ j, |G i j| with haG
  have hLx : ∀ t j, |(lam A G ^ t *ᵥ x) j| ≤ Fintype.card X * (Cb * ρ ^ t * Xb) :=
    fun t j => InvariantSplit.abs_mulVec_le _ _ (hL t) hxj j
  have hlim : Tendsto (fun t : ℕ => (Fintype.card X : ℝ) * (Cb * ρ ^ t * Xb)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul Cb).mul_const Xb
    simpa using this.const_mul (Fintype.card X : ℝ)
  have hlim2 : Tendsto (fun t : ℕ => (Fintype.card X : ℝ) *
      (aG * ((Fintype.card X : ℝ) * (Cb * ρ ^ t * Xb)))) atTop (𝓝 0) := by
    simpa using (hlim.const_mul aG).const_mul (Fintype.card X : ℝ)
  rw [hvg, tendsto_pi_nhds]
  intro k
  simp only [pow_mulVec_graphV hinv]
  rcases k with i | j
  · refine squeeze_zero_norm (fun t => ?_) hlim2
    rw [Real.norm_eq_abs]
    exact InvariantSplit.abs_mulVec_le G _ (abs_entry_le_sum G) (hLx t) i
  · refine squeeze_zero_norm (fun t => ?_) hlim
    rw [Real.norm_eq_abs]
    exact hLx t j

end GeneralBK

end Cochrane.StickyPriceFiscal.BKCopy
