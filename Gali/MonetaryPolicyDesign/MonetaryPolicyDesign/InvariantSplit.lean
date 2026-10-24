/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The stable invariant subspace of a real matrix

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 and footnotes 1–2; Blanchard and
Kahn (1980). Linear algebra behind the general Blanchard–Kahn theorem (`GeneralBK`).

Restated from the Woodford Chapter 4 project (`NeoWicksellianFramework.InvariantSplit`, namespace
renamed; this project does not import across projects). Used here for Galí (2015), Ex. 4.4(c),
p. 123: uniqueness of the equilibrium under the money supply rule (`Ex4_4Determinacy`).

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

namespace Gali.MonetaryPolicyDesign.InvariantSplit

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

end Gali.MonetaryPolicyDesign.InvariantSplit
