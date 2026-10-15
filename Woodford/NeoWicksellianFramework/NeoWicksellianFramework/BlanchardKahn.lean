/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.SchurCohn
import NeoWicksellianFramework.Expectations
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Blanchard–Kahn determinacy for the systems of Woodford, Appendix C

Woodford (2003), *Interest and Prices*, Appendix C.1, pp. 670–676 (Props C.1 and C.2, first
sentences, and footnotes 1–2). The book *assumes* the Blanchard–Kahn (1980) counting rule;
this module proves it for the systems Chapter 4 needs, for an arbitrary `ExpectationSystem`
(perfect foresight and genuine uncertainty alike), with existence and uniqueness among bounded
adapted processes.

## Two non-predetermined variables (Prop. C.1)

`E_t z_{t+1} = A z_t + w_t` (`SolvesE2`). `determinate2_iff`: exactly one bounded adapted solution
for every bounded adapted forcing iff both eigenvalues of `A` lie outside the unit circle
(`BothOutside`); with Prop. C.1 this is `determinate2_iff_cases` (Case I or Case II). Existence is
the forward solution through `A⁻¹` (`existsUnique2`, using geometric decay of powers,
`pow_bound_of_schurStable`); with a root on or inside the circle a bounded self-fulfilling path
exists (`exists_bounded_forward_homog`). No boundary case has to be set aside (fn. 1).

## Three variables, one predetermined (Prop. C.2)

State `y_t = (z_t, x_t)` with `x_t` (index `2`) predetermined: `E_t y_{t+1} = A y_t + w_t`,
`x_{t+1}` known at `t`, `x_0` given (`Equil3`). `Determinate3`: exactly one bounded equilibrium for
every bounded adapted forcing and every `x_0`; `DeterminateFor A a`: the same for forcing `a e_t`
with a scalar disturbance (the form (C.19) of the Chapter 4 models).

* `determinate3_of` (**sufficiency**): one eigenvalue in the open disc, two outside the closed disc
  (`OneInTwoOut`) and `Generic` (the stable eigenvector has a nonzero predetermined component)
  imply determinacy. Proof: with stable eigenvector `(g, 1)`, `ẑ_t = z_t − g x_t` solves a closed
  two-variable system with matrix `C = A_zz − g A_xz` whose eigenvalues are the two unstable ones
  (`realSplit_redC`, `reduce_equil`), solved forward by Prop. C.1; then
  `x_{t+1} = A_xz ẑ_t + μ x_t + w^x_t` is solved backward (`xrec`).
* `determinate3_iff` (**the Blanchard–Kahn theorem**): `Determinate3 ↔ OneInTwoOut ∧ Generic`;
  `determinate3_iff_cases` combines it with Prop. C.2.
* The genericity condition is genuinely needed: `diagEx = diag(1/2, 2, 2)` satisfies the count
  (`diagEx_oneInTwoOut`) but is not determinate (`diagEx_not_determinate`).
* Converse (the count fails): two eigenvalues in the open disc give a self-fulfilling path
  (`mult_of_two_inside`, `not_determinateFor_of_two_inside`); none in the closed disc gives
  non-existence (`nonexist_of_none_inside`, `not_determinateFor_of_none_inside`); every root
  configuration is covered by `oneInTwoOut_or_fails` (including complex pairs on the unit circle);
  a real eigenvalue `±1` gives non-existence by resonance (`nonexist_of_unit_left`,
  `not_determinate3_of_unit_root`). For a model `a e_t`, `oneInTwoOut_of_determinateFor` needs
  `P(±1) ≠ 0` — at a unit root the outcome depends on `a` (fn. 2's non-generic boundary).

The n-dimensional forward-system tools (`pow_entry_bound`, `rvMul`, `FSolves`, `fsolves_unique`,
`fsolves_exists`) are restated from the Galí Chapter 6 project (`Determinacy4`).

## Shared `2 × 2` tools (the canonical versions for the whole project)

* The inverse `inv2` (`inv2_mul`, `mul_inv2`, `tr2_inv2`, `det2_inv2`, and Mathlib's inverse:
  `inv2_eq_inv`, `tr2_inv`, `det2_inv`); geometric decay and summability of powers under
  Schur–Cohn (`pow_bound_of_schurStable`, `summable_abs_pow_entry`); `det_scalar_sub_two`.
* The forward form `x_t = K E_t x_{t+1} + w_t` with the core's `Solves`
  (`solves_iff_fsolves`, `forward_exists`, `FwdDeterminate`, `fwd_existsUnique`,
  `fwdDeterminate_iff`: exactly one bounded adapted solution for every bounded adapted forcing
  iff Schur–Cohn) and Prop. C.1 for `A⁻¹` (`schurStable_inv_iff_cases`,
  `schurStable_inv_iff_caseI`, `not_caseII`, from `SchurCohn.bothOutside_iff_cases`).
* Systems `M z_t = N E_t z_{t+1} + f_t` (`solveMN`, `tr2_solveMN`, `det2_solveMN`, `wMN`,
  `rows_mn_iff`, `solvesMN_iff`, `wMN_bounded_adapted`), and scalar recursions (`abs_rec_le`,
  `pow_bounded_eq_zero`).
-/

namespace Woodford.NeoWicksellianFramework.BlanchardKahn

open Polynomial Filter Topology SchurCohn
open scoped Matrix

/-- Woodford, p. 670 (from Galí Ch. 6), fn. 1 (Blanchard–Kahn, the tool): if every complex
eigenvalue of a real square matrix `K` lies in the open unit disc, the entries of `Kᵏ` decay
geometrically (Gelfand's spectral radius formula). -/
theorem pow_entry_bound {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ w : ℂ, (Matrix.scalar (Fin n) w - K.map Complex.ofReal).det = 0 → ‖w‖ < 1) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  have hpow : ∀ k, ((K ^ k).map Complex.ofReal) = (K.map Complex.ofReal) ^ k := fun k =>
    (Complex.ofRealHom.mapMatrix.map_pow K k)
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix (Fin n) (Fin n) ℂ := K.map Complex.ofReal with hA
  have hspec : ∀ w ∈ spectrum ℂ A, w ∈ A.charpoly.roots.toFinset ∧ ‖w‖ < 1 := by
    intro w hw
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hw
    refine ⟨?_, h w ?_⟩
    · rw [Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic A).ne_zero]
      exact hw
    · rw [← Matrix.eval_charpoly]; exact hw
  set ρ0 : NNReal := A.charpoly.roots.toFinset.sup (fun w => ‖w‖₊) with hρ0
  have hρ0lt : ρ0 < 1 := by
    rw [hρ0, Finset.sup_lt_iff (by norm_num)]
    intro w hw
    have hw' : w ∈ spectrum ℂ A := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      rw [Multiset.mem_toFinset, mem_roots (Matrix.charpoly_monic A).ne_zero] at hw
      exact hw
    have := (hspec w hw').2
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
  have hρ0r : (ρ0 : ℝ) < r := by
    have : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
    rw [hr]; linarith
  have hr1 : r < 1 := by
    have : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
    rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt ρ0.coe_nonneg hρ0r
  have hlt : spectralRadius ℂ A < ENNReal.ofReal r := by
    refine lt_of_le_of_lt hsr ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hρ0r
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A).eventually_lt_const
    hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- norm bound for large powers
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
  have hCb0 : 0 ≤ Cb := by
    have : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
    linarith
  have hCb1 : 1 ≤ Cb := by
    have : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
      Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
    linarith
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
      have := congrFun (congrFun (hpow k) i) j
      exact this.symm
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

/-- Woodford, p. 670 (from Galí Ch. 6): A matrix acting on a vector of random variables: `(M
a)_i = ∑_j M_{ij} a_j`. -/
def rvMul {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    Fin n → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Woodford, p. 670 (from Galí Ch. 6) (tool): matrices act on vectors of random variables
compatibly with multiplication. -/
theorem rvMul_rvMul {Ω : Type*} {n m l : ℕ} (M : Matrix (Fin n) (Fin m) ℝ)
    (N : Matrix (Fin m) (Fin l) ℝ) (a : Fin l → Ω → ℝ) :
    rvMul M (rvMul N a) = rvMul (M * N) a := by
  funext i
  simp only [rvMul, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Woodford, p. 670 (from Galí Ch. 6) (tool): additivity of the action. -/
theorem rvMul_add {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a + b) = rvMul M a + rvMul M b := by
  funext i
  simp only [rvMul, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Woodford, p. 670 (from Galí Ch. 6) (tool): the action respects subtraction. -/
theorem rvMul_sub {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a - b) = rvMul M a - rvMul M b := by
  funext i
  simp only [rvMul, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Woodford, p. 670 (from Galí Ch. 6) (tool): the identity matrix acts trivially. -/
theorem rvMul_one {Ω : Type*} {n : ℕ} (a : Fin n → Ω → ℝ) : rvMul 1 a = a := by
  funext i
  simp [rvMul, Matrix.one_apply]

/-- Woodford, p. 670 (from Galí Ch. 6) (tool): the action on the zero vector. -/
theorem rvMul_zero {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) :
    rvMul M (0 : Fin m → Ω → ℝ) = 0 := by
  funext i
  simp [rvMul]

/-- Woodford, p. 670 (from Galí Ch. 6) (tool): the action, pointwise. -/
theorem rvMul_apply {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) (ω : Ω) : rvMul M a i ω = ∑ j, M i j * a j ω := by
  simp [rvMul, Finset.sum_apply]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford, p. 670 (from Galí Ch. 6) (tool): `E_t` commutes with constant matrices. -/
theorem E_rvMul {n m : ℕ} (t : ℕ) (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) : 𝔼.E t (rvMul M a i) = rvMul M (fun j => 𝔼.E t (a j)) i := by
  simp only [rvMul, map_sum, map_smul]

/-- Woodford, p. 670 (from Galí Ch. 6): A vector process solves the forward system `s_t = K E_t
s_{t+1} + w_t`. -/
def FSolves {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (w s : ℕ → Fin n → Ω → ℝ) : Prop :=
  ∀ t, s t = rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Woodford, p. 670 (from Galí Ch. 6): A vector process is adapted. -/
def VAdapted {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Woodford, p. 670 (from Galí Ch. 6): A vector process is bounded. -/
def VBounded {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M

/-- Woodford, p. 670 (from Galí Ch. 6): Iterating a homogeneous forward system: `d_t = Kᵏ E_t
d_{t+k}`. -/
theorem fsolves_iterate {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {d : ℕ → Fin n → Ω → ℝ}
    (hd : FSolves 𝔼 K 0 d) (had : VAdapted 𝔼 d) (t k : ℕ) :
    d t = rvMul (K ^ k) (fun j => 𝔼.E t (d (t + k) j)) := by
  induction k with
  | zero =>
    funext i
    simp only [pow_zero, add_zero, rvMul_one, had t i]
  | succ k ih =>
    rw [ih]
    have h := hd (t + k)
    simp only [Pi.zero_apply, add_zero] at h
    have : (fun j => 𝔼.E t (d (t + k) j)) =
        rvMul K (fun j => 𝔼.E t (d (t + (k + 1)) j)) := by
      funext j
      rw [h, E_rvMul 𝔼]
      congr 1
      funext l
      rw [𝔼.tower (Nat.le_add_right t k), ← add_assoc]
    rw [this, rvMul_rvMul, ← pow_succ]

/-- Woodford, p. 670 (from Galí Ch. 6): Bound for `Kᵏ` acting on a bounded vector. -/
theorem abs_rvMul_pow_le {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ}
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) (k : ℕ) {a : Fin n → Ω → ℝ} {M : ℝ}
    (ha : ∀ j ω, |a j ω| ≤ M) (i : Fin n) (ω : Ω) :
    |rvMul (K ^ k) a i ω| ≤ n * (Cb * ρ ^ k * M) := by
  rw [rvMul_apply]
  have hM : 0 ≤ M := (abs_nonneg _).trans (ha i ω)
  calc |∑ j, (K ^ k) i j * a j ω| ≤ ∑ j, |(K ^ k) i j * a j ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, Cb * ρ ^ k * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hK k i j) (ha j ω) (abs_nonneg _)
          ((abs_nonneg _).trans (hK k i j))
    _ = n * (Cb * ρ ^ k * M) := by simp

/-- Woodford, p. 670 (from Galí Ch. 6), fn. 1 (Blanchard–Kahn): if the powers of `K` decay
geometrically, the forward system `s_t = K E_t s_{t+1} + w_t` has at most one bounded
adapted solution. -/
theorem fsolves_unique {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w x y : ℕ → Fin n → Ω → ℝ}
    (hx : FSolves 𝔼 K w x) (hy : FSolves 𝔼 K w y) (hax : VAdapted 𝔼 x)
    (hay : VAdapted 𝔼 y) (hbx : VBounded x) (hby : VBounded y) : x = y := by
  obtain ⟨M₁, hM₁⟩ := hbx
  obtain ⟨M₂, hM₂⟩ := hby
  set d : ℕ → Fin n → Ω → ℝ := fun t => x t - y t with hd_def
  have hd : FSolves 𝔼 K 0 d := by
    intro t
    simp only [hd_def, Pi.zero_apply, add_zero, Pi.sub_apply, map_sub]
    rw [hx t, hy t]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, rvMul, smul_sub, Finset.sum_sub_distrib]
    abel
  have had : VAdapted 𝔼 d := by
    intro t i
    simp only [hd_def, Pi.sub_apply, map_sub, hax t i, hay t i]
  have hdb : ∀ t i ω, |d t i ω| ≤ M₁ + M₂ := fun t i ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t i ω) (hM₂ t i ω))
  have hzero : d = 0 := by
    funext t i ω
    have hle : ∀ k, |d t i ω| ≤ n * (Cb * ρ ^ k * (M₁ + M₂)) := by
      intro k
      rw [fsolves_iterate 𝔼 hd had t k]
      exact abs_rvMul_pow_le hK k (fun j ω => 𝔼.abs_E_le (hdb (t + k) j) t ω) i ω
    have hlim : Tendsto (fun k : ℕ => (n : ℝ) * (Cb * ρ ^ k * (M₁ + M₂))) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul Cb).mul_const
        (M₁ + M₂)
      simpa using this.const_mul (n : ℝ)
    have h0 : |d t i ω| ≤ 0 := ge_of_tendsto' hlim hle
    simpa using h0
  funext t i ω
  have := congrFun (congrFun (congrFun hzero t) i) ω
  simpa [hd_def, sub_eq_zero] using this

/-- Woodford, p. 670 (from Galí Ch. 6), fn. 1 (Blanchard–Kahn): if the powers of `K` decay
geometrically, the forward series `s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` is a bounded adapted
solution of `s_t = K E_t s_{t+1} + w_t` for bounded adapted forcing `w`. -/
theorem fsolves_exists {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k)
    {w : ℕ → Fin n → Ω → ℝ} {Mw : ℝ} (hw : ∀ t i ω, |w t i ω| ≤ Mw) (haw : VAdapted 𝔼 w) :
    ∃ s, FSolves 𝔼 K w s ∧ VAdapted 𝔼 s ∧ VBounded s := by
  set Mb : ℝ := n * Cb * Mw with hMb
  set B : ℕ → ℕ → Fin n → Ω → ℝ := fun k t => rvMul (K ^ k) (fun j => 𝔼.E t (w (t + k) j))
    with hB
  have hT : ∀ k t t' i ω, |rvMul (K ^ k) (fun j => 𝔼.E t (w t' j)) i ω| ≤ ρ ^ k * Mb := by
    intro k t t' i ω
    have := abs_rvMul_pow_le hK k (fun j ω => 𝔼.abs_E_le (hw t' j) t ω) i ω
    calc _ ≤ n * (Cb * ρ ^ k * Mw) := this
      _ = ρ ^ k * Mb := by rw [hMb]; ring
  have hTs : ∀ t t' : ℕ → ℕ, ∀ i ω,
      Summable fun k => rvMul (K ^ k) (fun j => 𝔼.E (t k) (w (t' k) j)) i ω := fun t t' i ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Mb)
      (fun k => by rw [Real.norm_eq_abs]; exact hT k (t k) (t' k) i ω)
  have hBb : ∀ k t i ω, |B k t i ω| ≤ ρ ^ k * Mb := fun k t i ω => hT k t (t + k) i ω
  have hsum : ∀ t i ω, Summable fun k => B k t i ω := fun t i ω =>
    hTs (fun _ => t) (fun k => t + k) i ω
  set s : ℕ → Fin n → Ω → ℝ := fun t i ω => ∑' k, B k t i ω with hs
  have hEB : ∀ k t i, 𝔼.E t (B k (t + 1) i) =
      rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i := by
    intro k t i
    simp only [hB, E_rvMul 𝔼, 𝔼.tower (Nat.le_succ t)]
  have hEs : ∀ t i ω, 𝔼.E t (s (t + 1) i) ω =
      ∑' k, rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i ω := by
    intro t i ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k (t + 1) i) (fun k ω => hBb k (t + 1) i ω) t ω
    rw [show s (t + 1) i = fun ω' => ∑' k, B k (t + 1) i ω' from rfl, this]
    exact tsum_congr fun k => by rw [hEB]
  refine ⟨s, ?_, ?_, ?_⟩
  · intro t
    funext i ω
    have hB0 : B 0 t i ω = w t i ω := by
      simp only [hB, pow_zero, add_zero, rvMul_one, haw t i]
    have hshift : ∀ k, B (k + 1) t i ω =
        ∑ l, K i l * rvMul (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) l ω := by
      intro k
      simp only [hB]
      rw [← rvMul_apply, rvMul_rvMul, ← pow_succ', show t + (k + 1) = t + 1 + k by omega]
    have hR : (rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t) i ω =
        (∑' k, B (k + 1) t i ω) + w t i ω := by
      rw [Pi.add_apply, Pi.add_apply, rvMul_apply]
      congr 1
      simp only [hEs, ← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun l _ => (hTs (fun _ => t) (fun k => t + 1 + k) l ω).mul_left
        (K i l))]
      exact tsum_congr fun k => (hshift k).symm
    rw [hR, show s t i ω = ∑' k, B k t i ω from rfl, (hsum t i ω).tsum_eq_zero_add, hB0]
    ring
  · intro t i
    funext ω
    have := 𝔼.E_tsum hρ0 hρ1 (f := fun k => B k t i) (fun k ω => hBb k t i ω) t ω
    rw [show s t i = fun ω' => ∑' k, B k t i ω' from rfl, this]
    refine tsum_congr fun k => ?_
    simp only [hB, E_rvMul 𝔼, 𝔼.E_E_self]
  · refine ⟨Mb / (1 - ρ), fun t i ω => ?_⟩
    have hg : HasSum (fun k : ℕ => ρ ^ k * Mb) (Mb / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right Mb
      rwa [← div_eq_inv_mul] at this
    have := tsum_of_norm_bounded hg (f := fun k => B k t i ω)
      (fun k => by rw [Real.norm_eq_abs]; exact hBb k t i ω)
    rw [Real.norm_eq_abs] at this
    exact this


/-! ### Two non-predetermined variables (Proposition C.1) -/

/-- Woodford (2003), (C.19) and Prop. C.1, p. 670: `z` solves `E_t z_{t+1} = A z_t + w_t`. -/
def SolvesE2 (A : Matrix (Fin 2) (Fin 2) ℝ) (w z : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (z (t + 1) i) = rvMul A (z t) i + w t i

/-- Woodford (2003), Prop. C.1, p. 670: determinacy with two non-predetermined variables — for
every bounded adapted forcing there is exactly one bounded adapted solution. -/
def Determinate2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ w : ℕ → Fin 2 → Ω → ℝ, VBounded w → VAdapted 𝔼 w →
    ∃! z, SolvesE2 𝔼 A w z ∧ VAdapted 𝔼 z ∧ VBounded z

/-- Woodford (2003), App. C.1, p. 670: the inverse `A⁻¹ = (det A)⁻¹ adj A` of a `2 × 2` matrix
(the forward-form matrix `B` of `E_t z_{t+1} = A z_t + …`). -/
noncomputable def inv2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 1 1 / det2 A, -A 0 1 / det2 A; -A 1 0 / det2 A, A 0 0 / det2 A]

/-- Woodford (2003), App. C.1, p. 670: `tr A⁻¹ = tr A / det A`. -/
theorem tr2_inv2 (A : Matrix (Fin 2) (Fin 2) ℝ) : tr2 (inv2 A) = tr2 A / det2 A := by
  simp only [inv2, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), App. C.1, p. 670: `det A⁻¹ = (det A)⁻¹` (also when `det A = 0`, both sides
then being `0`). -/
theorem det2_inv2 (A : Matrix (Fin 2) (Fin 2) ℝ) : det2 (inv2 A) = (det2 A)⁻¹ := by
  have e : det2 (inv2 A) = det2 A * (det2 A)⁻¹ ^ 2 := by
    change inv2 A 0 0 * inv2 A 1 1 - inv2 A 0 1 * inv2 A 1 0 = _
    simp only [inv2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [show det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 from rfl]
    ring
  rw [e]
  by_cases h : det2 A = 0
  · simp [h]
  · field_simp

/-- Woodford (2003), App. C.1, p. 670: `A⁻¹ A = I` when `det A ≠ 0`. -/
theorem inv2_mul {A : Matrix (Fin 2) (Fin 2) ℝ} (h : det2 A ≠ 0) : inv2 A * A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inv2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (try rw [show det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 from rfl]) <;> ring

/-- Woodford (2003), App. C.1, p. 670: `A A⁻¹ = I` when `det A ≠ 0`. -/
theorem mul_inv2 {A : Matrix (Fin 2) (Fin 2) ℝ} (h : det2 A ≠ 0) : A * inv2 A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inv2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (try rw [show det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 from rfl]) <;> ring

/-- Woodford (2003), p. 277: `inv2 A` is Mathlib's inverse `A⁻¹` (which is `0` when
`det A = 0`, matching division by zero). -/
theorem inv2_eq_inv (A : Matrix (Fin 2) (Fin 2) ℝ) : inv2 A = A⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv', ← det2_eq_det]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inv2, div_eq_inv_mul]

/-- Woodford (2003), p. 277: `tr A⁻¹ = tr A / det A` for Mathlib's inverse. -/
theorem tr2_inv (A : Matrix (Fin 2) (Fin 2) ℝ) : tr2 A⁻¹ = tr2 A / det2 A := by
  rw [← inv2_eq_inv, tr2_inv2]

/-- Woodford (2003), p. 277: `det A⁻¹ = 1 / det A` for Mathlib's inverse. -/
theorem det2_inv (A : Matrix (Fin 2) (Fin 2) ℝ) : det2 A⁻¹ = 1 / det2 A := by
  rw [← inv2_eq_inv, det2_inv2, one_div]

/-- Woodford (2003), App. C.1, p. 670: the complex eigenvalues of a real `2 × 2` matrix are the
roots of `w² − (tr A) w + det A`. -/
theorem det_scalar_sub_two (K : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) :
    (Matrix.scalar (Fin 2) w - K.map Complex.ofReal).det =
      w ^ 2 - (tr2 K : ℂ) * w + (det2 K : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [tr2, det2, Matrix.scalar_apply, Matrix.diagonal]
  ring

/-- Woodford (2003), Prop. C.1, p. 670: under the Schur–Cohn condition the powers of a `2 × 2`
matrix decay geometrically. -/
theorem pow_bound_of_schurStable {K : Matrix (Fin 2) (Fin 2) ℝ}
    (h : SchurStable (tr2 K) (det2 K)) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  refine pow_entry_bound K (fun w hw => ?_)
  rw [det_scalar_sub_two] at hw
  rcases eq_root_of_eq hw with rfl | rfl
  · exact ((schurStable_iff_roots _ _).mp h).1
  · exact ((schurStable_iff_roots _ _).mp h).2

/-- Woodford (2003), p. 277 (the spectral-radius lemma behind (2.34)): under the Schur–Cohn
condition every entry of `Bᵏ` is absolutely summable in `k`. -/
theorem summable_abs_pow_entry {B : Matrix (Fin 2) (Fin 2) ℝ}
    (h : SchurStable (tr2 B) (det2 B)) (i j : Fin 2) : Summable (fun k => |(B ^ k) i j|) := by
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hB⟩ := pow_bound_of_schurStable h
  exact Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => hB k i j)
    ((summable_geometric_of_lt_one hρ0.le hρ1).mul_left Cb)

/-- Woodford (2003), (C.19), p. 677 (tool): a constant matrix maps a bounded vector process to a
bounded one. -/
theorem vBounded_rvMul {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) {a : ℕ → Fin m → Ω → ℝ}
    (ha : VBounded a) : VBounded (fun t => rvMul M (a t)) := by
  obtain ⟨B, hB⟩ := ha
  refine ⟨(∑ i, ∑ j, |M i j|) * max B 0, fun t i ω => ?_⟩
  change |rvMul M (a t) i ω| ≤ _
  rw [rvMul_apply]
  calc |∑ j, M i j * a t j ω| ≤ ∑ j, |M i j| * max B 0 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((hB t j ω).trans (le_max_left _ _)) (abs_nonneg _)
    _ = (∑ j, |M i j|) * max B 0 := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, |M i j|) * max B 0 := by
        refine mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)
        exact Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- Woodford (2003), (C.19), p. 677 (tool): a constant matrix maps an adapted vector process to an
adapted one. -/
theorem vAdapted_rvMul {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) {a : ℕ → Fin m → Ω → ℝ}
    (ha : VAdapted 𝔼 a) : VAdapted 𝔼 (fun t => rvMul M (a t)) := by
  intro t i
  change 𝔼.E t (rvMul M (a t) i) = rvMul M (a t) i
  rw [E_rvMul 𝔼]
  congr 1
  funext j
  exact ha t j

/-- Woodford (2003), Prop. C.1, p. 670: for `det A ≠ 0`, `E_t z_{t+1} = A z_t + w_t` is the forward
system `z_t = A⁻¹ E_t z_{t+1} − A⁻¹ w_t`. -/
theorem solvesE2_iff {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : det2 A ≠ 0)
    (w z : ℕ → Fin 2 → Ω → ℝ) :
    SolvesE2 𝔼 A w z ↔ FSolves 𝔼 (inv2 A) (fun t => -rvMul (inv2 A) (w t)) z := by
  constructor
  · intro h t
    have e : (fun j => 𝔼.E t (z (t + 1) j)) = rvMul A (z t) + w t := by
      funext j; rw [Pi.add_apply]; exact h t j
    rw [e, rvMul_add, rvMul_rvMul, inv2_mul hA, rvMul_one]
    funext i ω
    simp
  · intro h t i
    have e := h t
    have e2 : rvMul A (z t) = rvMul A (rvMul (inv2 A) (fun j => 𝔼.E t (z (t + 1) j)))
        - rvMul A (rvMul (inv2 A) (w t)) := by
      conv_lhs => rw [e]
      rw [← sub_eq_add_neg, rvMul_sub]
    rw [rvMul_rvMul, rvMul_rvMul, mul_inv2 hA, rvMul_one, rvMul_one] at e2
    have := congrFun e2 i
    simp only [Pi.sub_apply] at this
    rw [this]
    abel

/-- **Proposition C.1, sufficiency** (Woodford (2003), p. 670): if both eigenvalues of `A` lie
outside the unit circle, then for every bounded adapted forcing `E_t z_{t+1} = A z_t + w_t` has
exactly one bounded adapted solution, the forward solution `z_t = −∑ A^{−k−1} E_t w_{t+k}`. -/
theorem existsUnique2 {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : BothOutside (tr2 A) (det2 A))
    {w : ℕ → Fin 2 → Ω → ℝ} (hwb : VBounded w) (hwa : VAdapted 𝔼 w) :
    ∃! z, SolvesE2 𝔼 A w z ∧ VAdapted 𝔼 z ∧ VBounded z := by
  obtain ⟨hD, hS⟩ := (bothOutside_iff_schurStable_inv _ _).mp hA
  have hK : SchurStable (tr2 (inv2 A)) (det2 (inv2 A)) := by
    rw [tr2_inv2, det2_inv2, ← one_div]; exact hS
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hpow⟩ := pow_bound_of_schurStable hK
  have hfb : VBounded (fun t => -rvMul (inv2 A) (w t)) := by
    obtain ⟨B, hB⟩ := vBounded_rvMul (inv2 A) hwb
    exact ⟨B, fun t i ω => by simpa using hB t i ω⟩
  have hfa : VAdapted 𝔼 (fun t => -rvMul (inv2 A) (w t)) := by
    intro t i
    have := vAdapted_rvMul 𝔼 (inv2 A) hwa t i
    simp only [Pi.neg_apply, map_neg]
    exact congrArg Neg.neg this
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨z, hz, hza, hzb⟩ := fsolves_exists 𝔼 hρ0.le hρ1 hpow hMf hfa
  refine ⟨z, ⟨(solvesE2_iff 𝔼 hD w z).mpr hz, hza, hzb⟩, fun y ⟨hy, hya, hyb⟩ => ?_⟩
  exact fsolves_unique 𝔼 hρ0.le hρ1 hpow ((solvesE2_iff 𝔼 hD w y).mp hy) hz hya hza hyb hzb

/-- Woodford (2003), Prop. C.1, p. 670 (necessity, the self-fulfilling path): if a root `r` of the
characteristic polynomial has `|r| ≤ 1`, the deterministic path `z_t = Re(rᵗ v)` (`v` an
eigenvector) is a nonzero bounded solution of `z_{t+1} = A z_t`. -/
theorem exists_bounded_forward_homog {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : ¬ BothOutside (tr2 A) (det2 A)) :
    ∃ x : ℕ → Fin 2 → ℝ, (∀ t i, x (t + 1) i = A i 0 * x t 0 + A i 1 * x t 1) ∧
      (∃ C, ∀ t i, |x t i| ≤ C) ∧ x 0 ≠ 0 := by
  unfold BothOutside at h
  rw [not_and_or, not_lt, not_lt] at h
  obtain ⟨r, hr1, hroot⟩ : ∃ r : ℂ, ‖r‖ ≤ 1 ∧ r ^ 2 - tr2 A * r + det2 A = 0 := by
    rcases h with h | h
    · exact ⟨_, h, root_eq _ _ _ (Or.inl rfl)⟩
    · exact ⟨_, h, root_eq _ _ _ (Or.inr rfl)⟩
  obtain ⟨v, ⟨j, hj⟩, hv⟩ := exists_eigenvector A hroot
  refine ⟨fun t i => (r ^ t * v i).re, fun t i => ?_, ⟨‖v 0‖ + ‖v 1‖, fun t i => ?_⟩,
    fun h0 => ?_⟩
  · have hc : ∀ (a : ℝ) (z : ℂ), a * z.re = ((a : ℂ) * z).re := by intro a z; simp
    rw [hc, hc, ← Complex.add_re]
    change (r ^ (t + 1) * v i).re = _
    congr 1
    rw [pow_succ, mul_assoc, ← hv i]
    ring
  · have hrt : ‖r ^ t‖ ≤ 1 := by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hr1
    calc |(r ^ t * v i).re| ≤ ‖r ^ t * v i‖ := Complex.abs_re_le_norm _
      _ ≤ 1 * ‖v i‖ := by rw [norm_mul]; gcongr
      _ ≤ ‖v 0‖ + ‖v 1‖ := by fin_cases i <;> simp
  · exact hj (by simpa using congrFun h0 j)

/-- **Proposition C.1** (Woodford (2003), p. 670), determinacy form: the system
`E_t z_{t+1} = A z_t + w_t` in two non-predetermined variables is determinate (exactly one bounded
adapted solution for every bounded adapted forcing) iff both eigenvalues of `A` lie outside the
unit circle. Exact — fn. 1's "only generically necessary" is not needed: with a root on or inside
the circle a bounded self-fulfilling path exists. -/
theorem determinate2_iff [Nonempty Ω] (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Determinate2 𝔼 A ↔ BothOutside (tr2 A) (det2 A) := by
  constructor
  · intro hdet
    by_contra hA
    obtain ⟨x, hx, ⟨C, hC⟩, hx0⟩ := exists_bounded_forward_homog hA
    have h0 : VBounded (0 : ℕ → Fin 2 → Ω → ℝ) := ⟨0, fun _ _ _ => by simp⟩
    have ha0 : VAdapted 𝔼 (0 : ℕ → Fin 2 → Ω → ℝ) := fun _ _ => by simp
    obtain ⟨z, -, hu⟩ := hdet 0 h0 ha0
    have s1 : SolvesE2 𝔼 A 0 0 := fun t i => by simp [rvMul]
    have s2 : SolvesE2 𝔼 A 0 (fun t i _ => x t i) := fun t i => by
      rw [𝔼.const]
      funext ω
      simp only [rvMul_apply, Fin.sum_univ_two, Pi.add_apply, Pi.zero_apply, add_zero]
      exact hx t i
    have e1 := hu 0 ⟨s1, ha0, h0⟩
    have e2 := hu _ ⟨s2, fun t i => 𝔼.const t (x t i), ⟨C, fun t i _ => hC t i⟩⟩
    apply hx0
    funext i
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrFun (e2.trans e1.symm) 0) i) ω
    simpa using this
  · intro hA w hwb hwa
    exact existsUnique2 𝔼 hA hwb hwa

/-- **Proposition C.1** (Woodford (2003), pp. 670–671), complete: determinacy of
`E_t z_{t+1} = A z_t + w_t` iff Case I or Case II holds for `tr A`, `det A`. -/
theorem determinate2_iff_cases [Nonempty Ω] (A : Matrix (Fin 2) (Fin 2) ℝ) :
    Determinate2 𝔼 A ↔ CaseI2 (tr2 A) (det2 A) ∨ CaseII2 (tr2 A) (det2 A) := by
  rw [determinate2_iff, bothOutside_iff_cases]

/-! ### Two non-predetermined variables in forward form `x_t = K E_t x_{t+1} + w_t` -/

/-- Woodford (2003), App. C.1, p. 670 (tool): the core's two-variable system `Solves` is the
`n = 2` case of `FSolves`. -/
theorem solves_iff_fsolves (K : Matrix (Fin 2) (Fin 2) ℝ) (w x : ℕ → Fin 2 → Ω → ℝ) :
    𝔼.Solves K w x ↔ FSolves 𝔼 K w x := by
  constructor
  · intro h t
    funext i
    simp only [Pi.add_apply, rvMul, Fin.sum_univ_two]
    exact h t i
  · intro h t i
    have := congrFun (h t) i
    simpa only [Pi.add_apply, rvMul, Fin.sum_univ_two] using this

/-- Woodford (2003), App. C.1, p. 670 (`fsolves_exists` for two variables): if the powers of `K`
decay geometrically, the forward series `x_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` is a bounded adapted
solution of `x_t = K E_t x_{t+1} + w_t` for bounded adapted forcing `w`. -/
theorem forward_exists {K : Matrix (Fin 2) (Fin 2) ℝ} {Cb ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k)
    {w : ℕ → Fin 2 → Ω → ℝ} {Mw : ℝ} (hw : ∀ t i ω, |w t i ω| ≤ Mw)
    (haw : 𝔼.AdaptedVec w) :
    ∃ s, 𝔼.Solves K w s ∧ 𝔼.AdaptedVec s ∧ BoundedVec s := by
  obtain ⟨s, hs, has, hbs⟩ := fsolves_exists 𝔼 hρ0 hρ1 hK hw haw
  exact ⟨s, (solves_iff_fsolves 𝔼 K w s).mpr hs, has, hbs⟩

/-- Woodford (2003), App. C.1, Prop. C.1, p. 670 (determinacy in the genuine sense): for every
bounded adapted forcing `w`, the system `x_t = K E_t x_{t+1} + w_t` has exactly one bounded
adapted solution. -/
def FwdDeterminate (K : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ w : ℕ → Fin 2 → Ω → ℝ, BoundedVec w → 𝔼.AdaptedVec w →
    ∃! x, 𝔼.Solves K w x ∧ 𝔼.AdaptedVec x ∧ BoundedVec x

/-- Woodford (2003), App. C.1, Prop. C.1, p. 670 (sufficiency, existence and uniqueness): under
the Schur–Cohn condition `x_t = K E_t x_{t+1} + w_t` has exactly one bounded adapted solution,
the forward series `∑ Kᵏ E_t w_{t+k}`. -/
theorem fwd_existsUnique {K : Matrix (Fin 2) (Fin 2) ℝ} (hK : SchurStable (tr2 K) (det2 K))
    {w : ℕ → Fin 2 → Ω → ℝ} (hw : BoundedVec w) (haw : 𝔼.AdaptedVec w) :
    ∃! x, 𝔼.Solves K w x ∧ 𝔼.AdaptedVec x ∧ BoundedVec x := by
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hb⟩ := pow_bound_of_schurStable hK
  obtain ⟨Mw, hMw⟩ := hw
  obtain ⟨s, hs, has, hbs⟩ := forward_exists 𝔼 hρ0.le hρ1 hb hMw haw
  exact ⟨s, ⟨hs, has, hbs⟩, fun y hy => 𝔼.system_unique hK hy.1 hs hy.2.1 has hy.2.2 hbs⟩

/-- Woodford (2003), App. C.1, Prop. C.1, p. 670 (the determinacy criterion, proved rather than
assumed): a two-variable system with no predetermined variable has a unique bounded adapted
solution for every bounded adapted forcing iff `K` satisfies the Schur–Cohn condition (both
eigenvalues of `K = A⁻¹` inside, i.e. both eigenvalues of `A` outside, the unit circle). No
boundary case is excluded. -/
theorem fwdDeterminate_iff [Nonempty Ω] (K : Matrix (Fin 2) (Fin 2) ℝ) :
    FwdDeterminate 𝔼 K ↔ SchurStable (tr2 K) (det2 K) := by
  constructor
  · intro h
    by_contra hK
    have hz : 𝔼.Solves K 0 0 := fun t i => by simp
    have ha0 : 𝔼.AdaptedVec (0 : ℕ → Fin 2 → Ω → ℝ) := fun t i => by simp
    have hb0 : BoundedVec (0 : ℕ → Fin 2 → Ω → ℝ) := ⟨0, fun t i ω => by simp⟩
    obtain ⟨y, hy, hay, hby, hne⟩ := 𝔼.system_not_unique hK hz ha0 hb0
    obtain ⟨x, -, hx⟩ := h 0 hb0 ha0
    exact hne ((hx y ⟨hy, hay, hby⟩).trans (hx 0 ⟨hz, ha0, hb0⟩).symm)
  · intro hK w hw haw
    exact fwd_existsUnique 𝔼 hK hw haw

/-- Woodford (2003), Prop. C.1, pp. 670–671 (both cases, `det A ≠ 0`): `A⁻¹` satisfies the
Schur–Cohn condition (both eigenvalues of `A` outside the unit circle) iff Case I
((C.1)–(C.3)) or Case II ((C.4) `det A − tr A < −1` and (C.5) `det A + tr A < −1`). -/
theorem schurStable_inv_iff_cases {A : Matrix (Fin 2) (Fin 2) ℝ} (hD : det2 A ≠ 0) :
    SchurStable (tr2 (inv2 A)) (det2 (inv2 A)) ↔
      ((1 < det2 A ∧ -1 < det2 A - tr2 A ∧ -1 < det2 A + tr2 A) ∨
        (det2 A - tr2 A < -1 ∧ det2 A + tr2 A < -1)) := by
  rw [tr2_inv2, det2_inv2, ← one_div,
    ← (bothOutside_iff_schurStable_inv _ _).trans (and_iff_right hD), bothOutside_iff_cases]
  rfl

/-- Woodford (2003), Prop. C.1, p. 670, Case I (for `det A > 0`): both eigenvalues of `A` lie
outside the unit circle — equivalently `A⁻¹` satisfies the Schur–Cohn condition — iff
(C.1) `det A > 1`, (C.2) `det A − tr A > −1` and (C.3) `det A + tr A > −1`. -/
theorem schurStable_inv_iff_caseI {A : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < det2 A) :
    SchurStable (tr2 (inv2 A)) (det2 (inv2 A)) ↔
      (1 < det2 A ∧ -1 < det2 A - tr2 A ∧ -1 < det2 A + tr2 A) := by
  rw [schurStable_inv_iff_cases hD.ne']
  exact or_iff_left fun h => by linarith [h.1, h.2]

/-- Woodford (2003), App. C.2, p. 677, and C.4, p. 681: with `det A > 0` Case II of
Proposition C.1 is impossible (adding (C.4) and (C.5) gives `det A < −1`). -/
theorem not_caseII {A : Matrix (Fin 2) (Fin 2) ℝ} (hD : 0 < det2 A) :
    ¬ (det2 A - tr2 A < -1 ∧ det2 A + tr2 A < -1) := by
  rintro ⟨h1, h2⟩
  linarith

/-- Woodford (2003), App. C.1, p. 670 and p. 277 (algebra): the forward matrix `G = M⁻¹N` of a
system `M z_t = N E_t z_{t+1} + f_t`, written through the adjugate of `M`. -/
noncomputable def solveMN (M N : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(M 1 1 * N 0 0 - M 0 1 * N 1 0) / det2 M, (M 1 1 * N 0 1 - M 0 1 * N 1 1) / det2 M;
    (M 0 0 * N 1 0 - M 1 0 * N 0 0) / det2 M, (M 0 0 * N 1 1 - M 1 0 * N 0 1) / det2 M]

/-- Woodford (2003), App. C.1, p. 670 and p. 277: `tr(M⁻¹N)` through the adjugate. -/
theorem tr2_solveMN (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    tr2 (solveMN M N) =
      (M 1 1 * N 0 0 - M 0 1 * N 1 0 + M 0 0 * N 1 1 - M 1 0 * N 0 1) / det2 M := by
  simp only [tr2, solveMN, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  ring

/-- Woodford (2003), App. C.1, p. 670 and p. 277: `det(M⁻¹N) = det N / det M` (also when
`det M = 0`, both sides then being `0`). -/
theorem det2_solveMN (M N : Matrix (Fin 2) (Fin 2) ℝ) :
    det2 (solveMN M N) = det2 N / det2 M := by
  have hdd : det2 M = M 0 0 * M 1 1 - M 0 1 * M 1 0 := rfl
  change solveMN M N 0 0 * solveMN M N 1 1 - solveMN M N 0 1 * solveMN M N 1 0 =
    (N 0 0 * N 1 1 - N 0 1 * N 1 0) / det2 M
  simp only [solveMN, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
  by_cases hd : det2 M = 0
  · rw [hd]
    simp
  · field_simp
    linear_combination (-(N 0 0 * N 1 1 - N 0 1 * N 1 0)) * hdd

/-- Woodford (2003), App. C.1, p. 670 (algebra): the forcing `M⁻¹ f_t`. -/
noncomputable def wMN (M : Matrix (Fin 2) (Fin 2) ℝ) (f : ℕ → Fin 2 → Ω → ℝ) :
    ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(M 1 1 / det2 M) • f t 0 - (M 0 1 / det2 M) • f t 1,
    (M 0 0 / det2 M) • f t 1 - (M 1 0 / det2 M) • f t 0]

/-- Woodford (2003), App. C.1, p. 670 (algebra): with `det M ≠ 0`, the pair of rows
`M z = N P + f` is equivalent to `z = M⁻¹N P + M⁻¹ f`. -/
theorem rows_mn_iff {M N : Matrix (Fin 2) (Fin 2) ℝ} (hM : det2 M ≠ 0) (z0 z1 P0 P1 f0 f1 : ℝ) :
    (M 0 0 * z0 + M 0 1 * z1 = N 0 0 * P0 + N 0 1 * P1 + f0 ∧
      M 1 0 * z0 + M 1 1 * z1 = N 1 0 * P0 + N 1 1 * P1 + f1) ↔
      (z0 = solveMN M N 0 0 * P0 + solveMN M N 0 1 * P1 +
          (M 1 1 / det2 M * f0 - M 0 1 / det2 M * f1) ∧
        z1 = solveMN M N 1 0 * P0 + solveMN M N 1 1 * P1 +
          (M 0 0 / det2 M * f1 - M 1 0 / det2 M * f0)) := by
  simp only [solveMN, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  have hd : det2 M = M 0 0 * M 1 1 - M 0 1 * M 1 0 := rfl
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · field_simp
      rw [hd]
      linear_combination M 1 1 * h1 - M 0 1 * h2
    · field_simp
      rw [hd]
      linear_combination M 0 0 * h2 - M 1 0 * h1
  · rintro ⟨g1, g2⟩
    have G1 : det2 M * z0 = (M 1 1 * N 0 0 - M 0 1 * N 1 0) * P0 +
        (M 1 1 * N 0 1 - M 0 1 * N 1 1) * P1 + (M 1 1 * f0 - M 0 1 * f1) := by
      rw [g1]; field_simp
    have G2 : det2 M * z1 = (M 0 0 * N 1 0 - M 1 0 * N 0 0) * P0 +
        (M 0 0 * N 1 1 - M 1 0 * N 0 1) * P1 + (M 0 0 * f1 - M 1 0 * f0) := by
      rw [g2]; field_simp
    have H1 : det2 M * (M 0 0 * z0 + M 0 1 * z1 - (N 0 0 * P0 + N 0 1 * P1 + f0)) = 0 := by
      rw [hd] at G1 G2 ⊢
      linear_combination M 0 0 * G1 + M 0 1 * G2
    have H2 : det2 M * (M 1 0 * z0 + M 1 1 * z1 - (N 1 0 * P0 + N 1 1 * P1 + f1)) = 0 := by
      rw [hd] at G1 G2 ⊢
      linear_combination M 1 0 * G1 + M 1 1 * G2
    rcases mul_eq_zero.mp H1 with h | h
    · exact absurd h hM
    rcases mul_eq_zero.mp H2 with h' | h'
    · exact absurd h' hM
    exact ⟨by linarith, by linarith⟩

/-- Woodford (2003), App. C.1, p. 670: with `det M ≠ 0`, the system
`M z_t = N E_t z_{t+1} + f_t` is the forward system `z_t = M⁻¹N E_t z_{t+1} + M⁻¹ f_t`. -/
theorem solvesMN_iff {M N : Matrix (Fin 2) (Fin 2) ℝ} (hM : det2 M ≠ 0)
    {f z : ℕ → Fin 2 → Ω → ℝ} :
    (∀ t ω, (M 0 0 * z t 0 ω + M 0 1 * z t 1 ω = N 0 0 * 𝔼.E t (z (t + 1) 0) ω +
        N 0 1 * 𝔼.E t (z (t + 1) 1) ω + f t 0 ω ∧
      M 1 0 * z t 0 ω + M 1 1 * z t 1 ω = N 1 0 * 𝔼.E t (z (t + 1) 0) ω +
        N 1 1 * 𝔼.E t (z (t + 1) 1) ω + f t 1 ω)) ↔
      𝔼.Solves (solveMN M N) (wMN M f) z := by
  constructor
  · intro h t i
    funext ω
    have k := (rows_mn_iff hM _ _ _ _ _ _).mp (h t ω)
    fin_cases i
    · simp only [Fin.zero_eta, Pi.add_apply, Pi.smul_apply, smul_eq_mul, wMN,
        Matrix.cons_val_zero, Pi.sub_apply]
      exact k.1
    · simp only [Fin.mk_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, wMN,
        Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply]
      exact k.2
  · intro h t ω
    refine (rows_mn_iff hM _ _ _ _ _ _).mpr ⟨?_, ?_⟩
    · have := congrFun (h t 0) ω
      simpa [wMN] using this
    · have := congrFun (h t 1) ω
      simpa [wMN] using this

/-- Woodford (2003), App. C.1, p. 670: the forcing `M⁻¹ f` of a bounded adapted `f` is bounded
and adapted. -/
theorem wMN_bounded_adapted (M : Matrix (Fin 2) (Fin 2) ℝ) {f : ℕ → Fin 2 → Ω → ℝ}
    (hf : BoundedVec f) (hfa : 𝔼.AdaptedVec f) :
    BoundedVec (wMN M f) ∧ 𝔼.AdaptedVec (wMN M f) := by
  obtain ⟨K, hK⟩ := hf
  set c := |M 1 1 / det2 M| + |M 0 1 / det2 M| + |M 0 0 / det2 M| + |M 1 0 / det2 M|
  refine ⟨⟨c * K, fun t i ω => ?_⟩, fun t i => ?_⟩
  · have h0 := hK t 0 ω
    have h1 := hK t 1 ω
    have hK0 : 0 ≤ K := (abs_nonneg _).trans h0
    have a1 := abs_nonneg (M 1 1 / det2 M)
    have a2 := abs_nonneg (M 0 1 / det2 M)
    have a3 := abs_nonneg (M 0 0 / det2 M)
    have a4 := abs_nonneg (M 1 0 / det2 M)
    fin_cases i
    · simp only [wMN, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left h0 a1, mul_le_mul_of_nonneg_left h1 a2]
    · simp only [wMN, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left h1 a3, mul_le_mul_of_nonneg_left h0 a4]
  · fin_cases i <;> simp [wMN, map_sub, hfa t 0, hfa t 1]

/-! ### Three variables, one predetermined: the characteristic polynomial -/

/-- Woodford (2003), Prop. C.2, p. 672: the coefficient `A₂ = −tr A` of `det(λI − A)`. -/
def ch2 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := -(A 0 0 + A 1 1 + A 2 2)

/-- Woodford (2003), Prop. C.2, p. 672: the coefficient `A₁` of `det(λI − A)` (the sum of the
principal `2 × 2` minors). -/
def ch1 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0 + A 0 0 * A 2 2 - A 0 2 * A 2 0 + A 1 1 * A 2 2 - A 1 2 * A 2 1

/-- Woodford (2003), Prop. C.2, p. 672: the coefficient `A₀ = −det A` of `det(λI − A)`. -/
def ch0 (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  -(A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2
    + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0)

/-- Woodford (2003), Prop. C.2, p. 674: `A₀ = −det A`. -/
theorem ch0_eq (A : Matrix (Fin 3) (Fin 3) ℝ) : ch0 A = -A.det := by
  rw [Matrix.det_fin_three]; unfold ch0; ring

/-- Woodford (2003), Prop. C.2, p. 672: `det(xI − A) = x³ + A₂x² + A₁x + A₀`. -/
theorem det_sub_eq (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) :
    (Matrix.scalar (Fin 3) x - A).det = cubicR (ch2 A) (ch1 A) (ch0 A) x := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.scalar_apply, Fin.isValue, Matrix.sub_apply, Matrix.diagonal_apply_eq, ne_eq,
    Fin.reduceEq, not_false_eq_true, Matrix.diagonal_apply_ne, zero_sub, mul_neg, neg_mul, neg_neg,
    zero_ne_one, one_ne_zero]
  unfold cubicR ch2 ch1 ch0
  ring

/-- Woodford (2003), Prop. C.2, p. 672 (Cayley–Hamilton for `3 × 3` matrices):
`A³ + A₂A² + A₁A + A₀I = 0`. -/
theorem cayley_hamilton3 (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ^ 3 + ch2 A • A ^ 2 + ch1 A • A + ch0 A • (1 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, ch2, ch1, ch0] <;>
    ring

/-- Woodford (2003), Prop. C.2, p. 672: a real root of the characteristic polynomial is an
eigenvalue with a real eigenvector. -/
theorem exists_eigvec {A : Matrix (Fin 3) (Fin 3) ℝ} {μ : ℝ}
    (h : cubicR (ch2 A) (ch1 A) (ch0 A) μ = 0) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (by rw [det_sub_eq]; exact h)
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv
  rw [← hv]
  funext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

/-- Woodford (2003), Prop. C.2, p. 672: a real root of the characteristic polynomial has a real
left eigenvector, `q A = μ q`. -/
theorem exists_left_eigvec {A : Matrix (Fin 3) (Fin 3) ℝ} {μ : ℝ}
    (h : cubicR (ch2 A) (ch1 A) (ch0 A) μ = 0) :
    ∃ q : Fin 3 → ℝ, q ≠ 0 ∧ q ᵥ* A = μ • q := by
  obtain ⟨q, hq0, hq⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr (by rw [det_sub_eq]; exact h)
  refine ⟨q, hq0, ?_⟩
  rw [Matrix.vecMul_sub, sub_eq_zero] at hq
  rw [← hq]
  funext i
  simp [Matrix.scalar_apply, Matrix.vecMul_diagonal, mul_comm]

/-! ### Equilibrium with one predetermined variable -/

/-- Woodford (2003), Prop. C.2, p. 672 and (C.19): `E_t y_{t+1} = A y_t + w_t` for the state
`y_t = (z_t, x_t)`, `z_t` the two non-predetermined variables (indices `0, 1`) and `x_t` the
predetermined one (index `2`). -/
def Solves3 (A : Matrix (Fin 3) (Fin 3) ℝ) (w y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (y (t + 1) i) = rvMul A (y t) i + w t i

/-- Woodford (2003), Prop. C.2, p. 672: a (bounded) rational-expectations equilibrium: `y` solves
the system, is adapted and bounded, the predetermined variable `x_{t+1}` is known at date `t`, and
its initial value is `x₀`. -/
def Equil3 (A : Matrix (Fin 3) (Fin 3) ℝ) (w : ℕ → Fin 3 → Ω → ℝ) (x0 : ℝ)
    (y : ℕ → Fin 3 → Ω → ℝ) : Prop :=
  Solves3 𝔼 A w y ∧ VAdapted 𝔼 y ∧ (∀ t, 𝔼.E t (y (t + 1) 2) = y (t + 1) 2) ∧
    y 0 2 = (fun _ => x0) ∧ VBounded y

/-- Woodford (2003), Prop. C.2, p. 672: determinacy — for every bounded adapted forcing and every
initial value of the predetermined variable there is exactly one bounded equilibrium. -/
def Determinate3 (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ w : ℕ → Fin 3 → Ω → ℝ, VBounded w → VAdapted 𝔼 w → ∀ x0 : ℝ, ∃! y, Equil3 𝔼 A w x0 y

/-- Woodford (2003), (C.19), p. 677: determinacy of the model `E_t y_{t+1} = A y_t + a e_t` with a
scalar exogenous disturbance `e_t` entering in the direction `a`. -/
def DeterminateFor (A : Matrix (Fin 3) (Fin 3) ℝ) (a : Fin 3 → ℝ) : Prop :=
  ∀ e : ℕ → Ω → ℝ, BoundedProc e → 𝔼.Adapted e → ∀ x0 : ℝ,
    ∃! y, Equil3 𝔼 A (fun t i => a i • e t) x0 y

/-- Woodford (2003), p. 672, fn. 2 (the genericity the book leaves implicit): no eigenvector of an
eigenvalue in the open unit disc has a zero predetermined component. -/
def Generic (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ (μ : ℝ) (v : Fin 3 → ℝ), |μ| < 1 → A *ᵥ v = μ • v → v 2 = 0 → v = 0

/-- Woodford (2003), (C.19), p. 677: general determinacy implies determinacy of every model with a
scalar disturbance. -/
theorem determinateFor_of_determinate3 {A : Matrix (Fin 3) (Fin 3) ℝ} (h : Determinate3 𝔼 A)
    (a : Fin 3 → ℝ) : DeterminateFor 𝔼 A a := by
  intro e ⟨M, hM⟩ he x0
  refine h _ ⟨(∑ i, |a i|) * max M 0, fun t i ω => ?_⟩ (fun t i => ?_) x0
  · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    calc |a i| * |e t ω| ≤ |a i| * max M 0 :=
          mul_le_mul_of_nonneg_left ((hM t ω).trans (le_max_left _ _)) (abs_nonneg _)
      _ ≤ (∑ i, |a i|) * max M 0 := by
          refine mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)
          exact Finset.single_le_sum (f := fun i => |a i|) (fun i _ => abs_nonneg _)
            (Finset.mem_univ i)
  · simp only [map_smul, he t]

/-! ### Sufficiency: the Blanchard–Kahn reduction -/

/-- Woodford (2003), Prop. C.2, p. 672 (the reduction): `C = A_zz − g A_xz`, the matrix governing
`ẑ_t = z_t − g x_t` when `(g, 1)` is the stable eigenvector. -/
def redC (A : Matrix (Fin 3) (Fin 3) ℝ) (g0 g1 : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 0 0 - g0 * A 2 0, A 0 1 - g0 * A 2 1; A 1 0 - g1 * A 2 0, A 1 1 - g1 * A 2 1]

/-- Woodford (2003), Prop. C.2, p. 672 (the reduction): `ẑ_t = z_t − g x_t`. -/
def zhat (g0 g1 : ℝ) (y : ℕ → Fin 3 → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![y t 0 - g0 • y t 2, y t 1 - g1 • y t 2]

/-- Woodford (2003), Prop. C.2, p. 674: with `(g₀, g₁, 1)` an eigenvector of `μ`, the
characteristic polynomial factors as `(λ − μ) det(λI − C)`. -/
theorem realSplit_redC {A : Matrix (Fin 3) (Fin 3) ℝ} {μ g0 g1 : ℝ}
    (e0 : A 0 0 * g0 + A 0 1 * g1 + A 0 2 = μ * g0)
    (e1 : A 1 0 * g0 + A 1 1 * g1 + A 1 2 = μ * g1)
    (e2 : A 2 0 * g0 + A 2 1 * g1 + A 2 2 = μ) :
    RealSplit (ch2 A) (ch1 A) (ch0 A) μ (tr2 (redC A g0 g1)) (det2 (redC A g0 g1)) := by
  have h02 : A 0 2 = μ * g0 - A 0 0 * g0 - A 0 1 * g1 := by linarith
  have h12 : A 1 2 = μ * g1 - A 1 0 * g0 - A 1 1 * g1 := by linarith
  have h22 : A 2 2 = μ - A 2 0 * g0 - A 2 1 * g1 := by linarith
  unfold RealSplit ch2 ch1 ch0 tr2 det2 redC
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  rw [h02, h12, h22]
  refine ⟨by ring, by ring, by ring⟩

/-- Woodford (2003), Prop. C.2, p. 672 (the reduction): in an equilibrium, `ẑ` solves the
two-variable system `E_t ẑ_{t+1} = C ẑ_t + ŵ_t`, and the predetermined variable follows
`x_{t+1} = A_xz ẑ_t + μ x_t + w^x_t`. -/
theorem reduce_equil {A : Matrix (Fin 3) (Fin 3) ℝ} {μ g0 g1 : ℝ}
    (e0 : A 0 0 * g0 + A 0 1 * g1 + A 0 2 = μ * g0)
    (e1 : A 1 0 * g0 + A 1 1 * g1 + A 1 2 = μ * g1)
    (e2 : A 2 0 * g0 + A 2 1 * g1 + A 2 2 = μ) {w : ℕ → Fin 3 → Ω → ℝ} {x0 : ℝ}
    {y : ℕ → Fin 3 → Ω → ℝ} (hy : Equil3 𝔼 A w x0 y) :
    SolvesE2 𝔼 (redC A g0 g1) (zhat g0 g1 w) (zhat g0 g1 y) ∧ VAdapted 𝔼 (zhat g0 g1 y) ∧
      VBounded (zhat g0 g1 y) ∧
      ∀ t, y (t + 1) 2 = A 2 0 • zhat g0 g1 y t 0 + A 2 1 • zhat g0 g1 y t 1 + μ • y t 2 + w t 2
    := by
  obtain ⟨hs, ha, hp, -, ⟨M, hM⟩⟩ := hy
  have hx : ∀ t, y (t + 1) 2 = A 2 0 • zhat g0 g1 y t 0 + A 2 1 • zhat g0 g1 y t 1 +
      μ • y t 2 + w t 2 := by
    intro t
    rw [← hp t, hs t 2]
    funext ω
    have h22 : A 2 2 = μ - A 2 0 * g0 - A 2 1 * g1 := by linarith
    simp only [zhat, rvMul_apply, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h22]
    ring
  refine ⟨fun t i => ?_, fun t i => ?_, ⟨M + (|g0| + |g1|) * M, fun t i ω => ?_⟩, hx⟩
  · have h02 : A 0 2 = μ * g0 - A 0 0 * g0 - A 0 1 * g1 := by linarith
    have h12 : A 1 2 = μ * g1 - A 1 0 * g0 - A 1 1 * g1 := by linarith
    have h22 : A 2 2 = μ - A 2 0 * g0 - A 2 1 * g1 := by linarith
    have s0 := hs t 0
    have s1 := hs t 1
    have s2 := hs t 2
    funext ω
    have t0 := congrFun s0 ω
    have t1 := congrFun s1 ω
    have t2 := congrFun s2 ω
    simp only [rvMul_apply, Fin.sum_univ_three, Pi.add_apply] at t0 t1 t2
    fin_cases i
    · simp only [zhat, rvMul_apply, Fin.sum_univ_two, redC, map_sub, map_smul, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
      rw [t0, t2, h02, h22]
      ring
    · simp only [zhat, rvMul_apply, Fin.sum_univ_two, redC, map_sub, map_smul, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.mk_one, Fin.isValue]
      rw [t1, t2, h12, h22]
      ring
  · fin_cases i
    · simp [zhat, map_sub, map_smul, ha t 0, ha t 2]
    · simp [zhat, map_sub, map_smul, ha t 1, ha t 2]
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 ω)
    fin_cases i
    · change |y t 0 ω - g0 * y t 2 ω| ≤ _
      calc |y t 0 ω - g0 * y t 2 ω| ≤ |y t 0 ω| + |g0| * |y t 2 ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ M + (|g0| + |g1|) * M := by
            have := hM t 0 ω; have := hM t 2 ω
            have := abs_nonneg g1
            nlinarith [abs_nonneg g0]
    · change |y t 1 ω - g1 * y t 2 ω| ≤ _
      calc |y t 1 ω - g1 * y t 2 ω| ≤ |y t 1 ω| + |g1| * |y t 2 ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ M + (|g0| + |g1|) * M := by
            have := hM t 1 ω; have := hM t 2 ω
            have := abs_nonneg g0
            nlinarith [abs_nonneg g1]

/-- Woodford (2003), Prop. C.2, p. 672 (the backward-looking block): the predetermined variable
generated by `x₀` and `x_{t+1} = c_t + μ x_t`. -/
noncomputable def xrec (c : ℕ → Ω → ℝ) (μ x0 : ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x0
  | t + 1 => c t + μ • xrec c μ x0 t

omit 𝔼 in
/-- Woodford (2003), p. 277 and Prop. C.2, p. 672: a stable scalar recursion
`x_{t+1} = λ x_t + u_t` with `|λ| < 1` and bounded `u` stays bounded. -/
theorem abs_rec_le {lam C B : ℝ} (hl : |lam| < 1) {u x : ℕ → ℝ} (hu : ∀ t, |u t| ≤ C)
    (hx0 : |x 0| ≤ B) (hx : ∀ t, x (t + 1) = lam * x t + u t) (t : ℕ) :
    |x t| ≤ max B (C / (1 - |lam|)) := by
  have h1 : 0 < 1 - |lam| := by linarith
  induction t with
  | zero => exact le_max_of_le_left hx0
  | succ t ih =>
    rw [hx t]
    set K := max B (C / (1 - |lam|))
    have hK : C ≤ (1 - |lam|) * K := by
      have := le_max_right B (C / (1 - |lam|))
      rw [div_le_iff₀ h1] at this
      linarith
    calc |lam * x t + u t| ≤ |lam| * |x t| + |u t| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |lam| * K + C := by gcongr; exact hu t
      _ ≤ K := by linarith

omit 𝔼 in
/-- Woodford (2003), p. 314 and App. C.8: if `|γ| > 1` and `γᵗ e₀` stays bounded, then
`e₀ = 0`. -/
theorem pow_bounded_eq_zero {γ e0 M : ℝ} (hγ : 1 < |γ|) (h : ∀ t : ℕ, |γ ^ t * e0| ≤ M) :
    e0 = 0 := by
  by_contra hne
  have hpos : 0 < |e0| := abs_pos.mpr hne
  have ht := tendsto_pow_atTop_atTop_of_one_lt hγ
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop (M / |e0|)).exists
  have := h n
  rw [abs_mul, abs_pow, div_lt_iff₀ hpos] at *
  linarith

omit 𝔼 in
/-- Woodford (2003), Prop. C.2, p. 672: with `|μ| < 1` and bounded `c` the backward recursion is
bounded. -/
theorem xrec_bounded {c : ℕ → Ω → ℝ} {μ K : ℝ} (x0 : ℝ) (hc : ∀ t ω, |c t ω| ≤ K)
    (hμ : |μ| < 1) : ∀ t ω, |xrec c μ x0 t ω| ≤ max |x0| (K / (1 - |μ|)) := fun t ω =>
  abs_rec_le hμ (u := fun t => c t ω) (x := fun t => xrec c μ x0 t ω) (fun t => hc t ω) le_rfl
    (fun t => by change c t ω + μ * xrec c μ x0 t ω = _; ring) t

/-- Woodford (2003), Prop. C.2, p. 672: with `c` adapted, `x_{t+1}` is known at date `t`. -/
theorem xrec_known {c : ℕ → Ω → ℝ} {μ : ℝ} (x0 : ℝ) (hc : 𝔼.Adapted c) :
    ∀ t, 𝔼.E t (xrec c μ x0 t) = xrec c μ x0 t ∧
      𝔼.E t (xrec c μ x0 (t + 1)) = xrec c μ x0 (t + 1) := by
  intro t
  induction t with
  | zero =>
    have h0 : 𝔼.E 0 (xrec c μ x0 0) = xrec c μ x0 0 := 𝔼.const 0 x0
    refine ⟨h0, ?_⟩
    change 𝔼.E 0 (c 0 + μ • xrec c μ x0 0) = c 0 + μ • xrec c μ x0 0
    rw [map_add, map_smul, hc 0, h0]
  | succ t ih =>
    have h1 : 𝔼.E (t + 1) (xrec c μ x0 (t + 1)) = xrec c μ x0 (t + 1) := by
      rw [← ih.2, 𝔼.known (Nat.le_succ t)]
    refine ⟨h1, ?_⟩
    change 𝔼.E (t + 1) (c (t + 1) + μ • xrec c μ x0 (t + 1)) = c (t + 1) + μ • xrec c μ x0 (t + 1)
    rw [map_add, map_smul, hc (t + 1), h1]

/-- **The Blanchard–Kahn theorem, sufficiency** (Woodford (2003), Prop. C.2, p. 672, which the
book assumes, fns. 1–2): if `A` has a real eigenvalue `|μ| < 1` with eigenvector `(g₀, g₁, 1)` and
the reduced matrix `C = A_zz − g A_xz` has both eigenvalues outside the unit circle, then for every
bounded adapted forcing and every initial value of the predetermined variable there is exactly one
bounded equilibrium. -/
theorem determinate3_of_reduction {A : Matrix (Fin 3) (Fin 3) ℝ} {μ g0 g1 : ℝ} (hμ : |μ| < 1)
    (e0 : A 0 0 * g0 + A 0 1 * g1 + A 0 2 = μ * g0)
    (e1 : A 1 0 * g0 + A 1 1 * g1 + A 1 2 = μ * g1)
    (e2 : A 2 0 * g0 + A 2 1 * g1 + A 2 2 = μ)
    (hC : BothOutside (tr2 (redC A g0 g1)) (det2 (redC A g0 g1))) : Determinate3 𝔼 A := by
  intro w hwb hwa x0
  -- the forcing of the reduced system
  have hfb : VBounded (zhat g0 g1 w) := by
    obtain ⟨M, hM⟩ := hwb
    refine ⟨M + (|g0| + |g1|) * M, fun t i ω => ?_⟩
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0 ω)
    fin_cases i
    · change |w t 0 ω - g0 * w t 2 ω| ≤ _
      calc |w t 0 ω - g0 * w t 2 ω| ≤ |w t 0 ω| + |g0| * |w t 2 ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ M + (|g0| + |g1|) * M := by
            have := hM t 0 ω; have := hM t 2 ω; have := abs_nonneg g1
            nlinarith [abs_nonneg g0]
    · change |w t 1 ω - g1 * w t 2 ω| ≤ _
      calc |w t 1 ω - g1 * w t 2 ω| ≤ |w t 1 ω| + |g1| * |w t 2 ω| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ M + (|g0| + |g1|) * M := by
            have := hM t 1 ω; have := hM t 2 ω; have := abs_nonneg g0
            nlinarith [abs_nonneg g1]
  have hfa : VAdapted 𝔼 (zhat g0 g1 w) := by
    intro t i
    fin_cases i
    · simp [zhat, map_sub, map_smul, hwa t 0, hwa t 2]
    · simp [zhat, map_sub, map_smul, hwa t 1, hwa t 2]
  obtain ⟨zh, ⟨hzs, hza, hzb⟩, hzu⟩ := existsUnique2 𝔼 hC hfb hfa
  -- the predetermined variable
  set c : ℕ → Ω → ℝ := fun t => A 2 0 • zh t 0 + A 2 1 • zh t 1 + w t 2 with hc_def
  have hca : 𝔼.Adapted c := fun t => by
    simp only [hc_def, map_add, map_smul, hza t 0, hza t 1, hwa t 2]
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨Mw, hMw⟩ := hwb
  have hcb : ∀ t ω, |c t ω| ≤ |A 2 0| * Mz + |A 2 1| * Mz + Mw := by
    intro t ω
    simp only [hc_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |A 2 0 * zh t 0 ω + A 2 1 * zh t 1 ω + w t 2 ω|
        ≤ |A 2 0 * zh t 0 ω| + |A 2 1 * zh t 1 ω| + |w t 2 ω| := abs_add_three _ _ _
      _ ≤ _ := by
          rw [abs_mul, abs_mul]
          gcongr
          · exact hMz t 0 ω
          · exact hMz t 1 ω
          · exact hMw t 2 ω
  set x := xrec c μ x0 with hx_def
  have hxk := xrec_known 𝔼 (μ := μ) x0 hca
  have hxb := xrec_bounded x0 hcb hμ
  set y : ℕ → Fin 3 → Ω → ℝ := fun t => ![zh t 0 + g0 • x t, zh t 1 + g1 • x t, x t] with hy_def
  have h02 : A 0 2 = μ * g0 - A 0 0 * g0 - A 0 1 * g1 := by linarith
  have h12 : A 1 2 = μ * g1 - A 1 0 * g0 - A 1 1 * g1 := by linarith
  have h22 : A 2 2 = μ - A 2 0 * g0 - A 2 1 * g1 := by linarith
  have hyeq : Equil3 𝔼 A w x0 y := by
    refine ⟨fun t i => ?_, fun t i => ?_, fun t => (hxk t).2, rfl, ?_⟩
    · have z0 := congrFun (hzs t 0)
      have z1 := congrFun (hzs t 1)
      fin_cases i
      · change 𝔼.E t (zh (t + 1) 0 + g0 • x (t + 1)) = _
        rw [map_add, map_smul, (hxk t).2, show xrec c μ x0 (t + 1) = c t + μ • x t from rfl]
        funext ω
        have := z0 ω
        simp only [rvMul_apply, Fin.sum_univ_two, redC, zhat, Pi.add_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [rvMul_apply, Fin.sum_univ_three, hy_def, hc_def, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.isValue]
        rw [this, h02]
        ring
      · change 𝔼.E t (zh (t + 1) 1 + g1 • x (t + 1)) = _
        rw [map_add, map_smul, (hxk t).2, show xrec c μ x0 (t + 1) = c t + μ • x t from rfl]
        funext ω
        have := z1 ω
        simp only [rvMul_apply, Fin.sum_univ_two, redC, zhat, Pi.add_apply, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
          Matrix.cons_val_fin_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [rvMul_apply, Fin.sum_univ_three, hy_def, hc_def, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.mk_one, Fin.isValue]
        rw [this, h12]
        ring
      · change 𝔼.E t (x (t + 1)) = _
        rw [(hxk t).2, show xrec c μ x0 (t + 1) = c t + μ • x t from rfl]
        funext ω
        simp only [rvMul_apply, Fin.sum_univ_three, hy_def, hc_def, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.reduceFinMk, Fin.isValue]
        rw [h22]
        ring
    · fin_cases i
      · change 𝔼.E t (zh t 0 + g0 • x t) = zh t 0 + g0 • x t
        rw [map_add, map_smul, hza t 0, (hxk t).1]
      · change 𝔼.E t (zh t 1 + g1 • x t) = zh t 1 + g1 • x t
        rw [map_add, map_smul, hza t 1, (hxk t).1]
      · exact (hxk t).1
    · refine ⟨Mz + (|g0| + |g1| + 1) * max |x0| ((|A 2 0| * Mz + |A 2 1| * Mz + Mw) / (1 - |μ|)),
        fun t i ω => ?_⟩
      set B := max |x0| ((|A 2 0| * Mz + |A 2 1| * Mz + Mw) / (1 - |μ|))
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (le_max_left _ _)
      have hMz0 : 0 ≤ Mz := (abs_nonneg _).trans (hMz 0 0 ω)
      have hxt := hxb t ω
      fin_cases i
      · change |zh t 0 ω + g0 * x t ω| ≤ _
        calc |zh t 0 ω + g0 * x t ω| ≤ |zh t 0 ω| + |g0| * |x t ω| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ _ := by
              have := hMz t 0 ω
              nlinarith [abs_nonneg g0, abs_nonneg g1, abs_nonneg (x t ω)]
      · change |zh t 1 ω + g1 * x t ω| ≤ _
        calc |zh t 1 ω + g1 * x t ω| ≤ |zh t 1 ω| + |g1| * |x t ω| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ _ := by
              have := hMz t 1 ω
              nlinarith [abs_nonneg g0, abs_nonneg g1, abs_nonneg (x t ω)]
      · change |x t ω| ≤ _
        nlinarith [abs_nonneg g0, abs_nonneg g1]
  refine ⟨y, hyeq, fun y' hy' => ?_⟩
  -- uniqueness
  obtain ⟨r1, r2, r3, r4⟩ := reduce_equil 𝔼 e0 e1 e2 hy'
  have hz' : zhat g0 g1 y' = zh := hzu _ ⟨r1, r2, r3⟩
  have hx' : ∀ t, y' t 2 = x t := by
    intro t
    induction t with
    | zero => rw [hy'.2.2.2.1]; rfl
    | succ t ih =>
      rw [r4 t, ih, hz']
      change _ = c t + μ • x t
      simp only [hc_def]
      abel
  funext t i
  fin_cases i
  · have := congrFun (congrFun hz' t) 0
    change y' t 0 - g0 • y' t 2 = zh t 0 at this
    change y' t 0 = zh t 0 + g0 • x t
    rw [← hx' t, ← this]; abel
  · have := congrFun (congrFun hz' t) 1
    change y' t 1 - g1 • y' t 2 = zh t 1 at this
    change y' t 1 = zh t 1 + g1 • x t
    rw [← hx' t, ← this]; abel
  · exact hx' t

/-- **The Blanchard–Kahn theorem, sufficiency** (Woodford (2003), Prop. C.2, p. 672): exactly one
eigenvalue in the open unit disc and two outside the closed disc, together with the genericity
condition (the stable eigenvector has a nonzero predetermined component), imply determinacy. -/
theorem determinate3_of {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : OneInTwoOut (ch2 A) (ch1 A) (ch0 A)) (hg : Generic A) : Determinate3 𝔼 A := by
  obtain ⟨μ, T, D, hμ, hTD, hs⟩ := (oneInTwoOut_iff_real _ _ _).mp hA
  have hroot : cubicR (ch2 A) (ch1 A) (ch0 A) μ = 0 := by
    rw [cubicR_of_realSplit hs]; ring
  obtain ⟨v, hv0, hv⟩ := exists_eigvec hroot
  have hv2 : v 2 ≠ 0 := fun h => hv0 (hg μ v hμ hv h)
  have hrow : ∀ i, A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 = μ * v i := by
    intro i
    have := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      smul_eq_mul] at this
    exact this
  have hi : v 2 * (v 2)⁻¹ = 1 := mul_inv_cancel₀ hv2
  set g0 := v 0 / v 2 with hg0
  set g1 := v 1 / v 2 with hg1
  have e0 : A 0 0 * g0 + A 0 1 * g1 + A 0 2 = μ * g0 := by
    have := hrow 0
    rw [hg0, hg1, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (v 2)⁻¹ * this - A 0 2 * hi
  have e1 : A 1 0 * g0 + A 1 1 * g1 + A 1 2 = μ * g1 := by
    have := hrow 1
    rw [hg0, hg1, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (v 2)⁻¹ * this - A 1 2 * hi
  have e2 : A 2 0 * g0 + A 2 1 * g1 + A 2 2 = μ := by
    have := hrow 2
    rw [hg0, hg1, div_eq_mul_inv, div_eq_mul_inv]
    linear_combination (v 2)⁻¹ * this - (A 2 2 - μ) * hi
  have hs' := realSplit_redC e0 e1 e2
  have hT : T = tr2 (redC A g0 g1) := by
    have := hs.1.symm.trans hs'.1; linarith
  have hD : D = det2 (redC A g0 g1) := by
    have h1 := hs.2.1.symm.trans hs'.2.1
    rw [hT] at h1; linarith
  rw [hT, hD] at hTD
  exact determinate3_of_reduction 𝔼 hμ e0 e1 e2 hTD

/-! ### Necessity: self-fulfilling paths and non-existence -/

/-- Woodford (2003), Prop. C.2, p. 672: a bounded deterministic orbit `y_t = Aᵗ u` is an
equilibrium with zero forcing and initial predetermined value `u₂`. -/
theorem equil_orbit {A : Matrix (Fin 3) (Fin 3) ℝ} {u : Fin 3 → ℝ} {C : ℝ}
    (hC : ∀ t i, |(A ^ t *ᵥ u) i| ≤ C) :
    Equil3 𝔼 A 0 (u 2) (fun t i _ => (A ^ t *ᵥ u) i) := by
  refine ⟨fun t i => ?_, fun t i => 𝔼.const t _, fun t => 𝔼.const t _, ?_,
    ⟨C, fun t i _ => hC t i⟩⟩
  · rw [𝔼.const]
    funext ω
    simp only [rvMul_apply, Pi.add_apply, Pi.zero_apply, add_zero]
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct]
  · funext ω
    simp

/-- Woodford (2003), Prop. C.2, p. 672: zero is an equilibrium for zero forcing and `x₀ = 0`. -/
theorem equil_zero (A : Matrix (Fin 3) (Fin 3) ℝ) : Equil3 𝔼 A 0 0 0 := by
  refine ⟨fun t i => ?_, fun t i => by simp, fun t => by simp, rfl, ⟨0, fun t i ω => by simp⟩⟩
  simp [rvMul]

/-- Woodford (2003), Prop. C.2, p. 672 (multiplicity): a nonzero equilibrium with zero forcing and
`x₀ = 0` (a self-fulfilling path) rules out determinacy, whatever the disturbance direction. -/
theorem not_determinateFor_of_mult {A : Matrix (Fin 3) (Fin 3) ℝ} (a : Fin 3 → ℝ)
    {y : ℕ → Fin 3 → Ω → ℝ} (hy : Equil3 𝔼 A 0 0 y) (hne : y ≠ 0) :
    ¬ DeterminateFor 𝔼 A a := by
  intro h
  obtain ⟨z, -, hu⟩ := h 0 ⟨0, fun _ _ => by simp⟩ (fun _ => by simp) 0
  have hw : (fun t i => a i • (0 : ℕ → Ω → ℝ) t) = 0 := by funext t i; simp
  rw [hw] at hu
  exact hne ((hu y hy).trans (hu 0 (equil_zero 𝔼 A)).symm)

/-- Woodford (2003), Prop. C.2, p. 672 (non-existence): if for some initial value there is no
bounded equilibrium with zero forcing, the model is not determinate. -/
theorem not_determinateFor_of_nonexist {A : Matrix (Fin 3) (Fin 3) ℝ} (a : Fin 3 → ℝ) {x0 : ℝ}
    (h : ∀ y, ¬ Equil3 𝔼 A 0 x0 y) : ¬ DeterminateFor 𝔼 A a := by
  intro hd
  obtain ⟨y, hy, -⟩ := hd 0 ⟨0, fun _ _ => by simp⟩ (fun _ => by simp) x0
  have hw : (fun t i => a i • (0 : ℕ → Ω → ℝ) t) = 0 := by funext t i; simp
  rw [hw] at hy
  exact h y hy

/-- Woodford (2003), Prop. C.2, p. 672: the orbit of an eigenvector, `Aᵗ v = μᵗ v`. -/
theorem pow_mulVec_eigen {A : Matrix (Fin 3) (Fin 3) ℝ} {μ : ℝ} {v : Fin 3 → ℝ}
    (hv : A *ᵥ v = μ • v) (t : ℕ) : A ^ t *ᵥ v = μ ^ t • v := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- Woodford (2003), Prop. C.2, p. 672, fn. 2 (the genericity is necessary): an eigenvector
`v ≠ 0` with `v₂ = 0` of an eigenvalue `|μ| ≤ 1` gives a self-fulfilling path `μᵗ v`. -/
theorem mult_of_eigen [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ} {μ : ℝ} {v : Fin 3 → ℝ}
    (hμ : |μ| ≤ 1) (hv : A *ᵥ v = μ • v) (h2 : v 2 = 0) (hne : v ≠ 0) :
    ∃ y, Equil3 𝔼 A 0 0 y ∧ y ≠ 0 := by
  have hb : ∀ t i, |(A ^ t *ᵥ v) i| ≤ |v 0| + |v 1| + |v 2| := by
    intro t i
    rw [pow_mulVec_eigen hv t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    have h1 : |μ| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg _) hμ
    have h2 : |v i| ≤ |v 0| + |v 1| + |v 2| := by
      fin_cases i <;> simp <;> linarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2)]
    calc |μ| ^ t * |v i| ≤ 1 * |v i| := by gcongr
      _ ≤ _ := by linarith
  have he := equil_orbit 𝔼 hb
  rw [h2] at he
  refine ⟨_, he, fun h0 => hne ?_⟩
  funext i
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun (congrFun h0 0) i) ω
  simpa using this

/-- Woodford (2003), Prop. C.2, p. 672: all solutions of `x_{k+2} = s x_{k+1} − p x_k` are bounded
(stated through the Cayley–Hamilton sequence of `λ² − sλ + p`). -/
def RecBounded (s p : ℝ) : Prop := ∃ C, ∀ k, |chSeq s p k| ≤ C

/-- Woodford (2003), Prop. C.1, p. 670: roots inside the unit circle give bounded solutions. -/
theorem recBounded_of_schurStable {s p : ℝ} (h : SchurStable s p) : RecBounded s p := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
    (Metric.isBounded_range_of_tendsto _ (tendsto_chSeq h))
  exact ⟨C, fun k => by simpa [Real.norm_eq_abs] using hC _ (Set.mem_range_self k)⟩

/-- Woodford (2003), Prop. C.1, p. 671: a complex pair on the unit circle (`D = 1`, negative
discriminant) also gives bounded solutions: `(λ₁ − λ₂) S_k = λ₁^{k+1} − λ₂^{k+1}`. -/
theorem recBounded_of_circle {s : ℝ} (h : disc s 1 < 0) : RecBounded s 1 := by
  obtain ⟨h1, h2⟩ := normSq_root_of_neg h
  have n1 : ‖root₁ s 1‖ = 1 := by
    have := norm_nonneg (root₁ s 1); nlinarith
  have n2 : ‖root₂ s 1‖ = 1 := by
    have := norm_nonneg (root₂ s 1); nlinarith
  have hne : root₁ s 1 - root₂ s 1 ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    have hn : ¬ 0 ≤ disc s 1 := not_le.mpr h
    have hsq : 0 < Real.sqrt (-disc s 1) := Real.sqrt_pos.mpr (by linarith)
    unfold root₁ root₂ at him
    simp only [hn, ↓reduceIte, Complex.sub_im, Complex.zero_im] at him
    linarith
  have key : ∀ k, (root₁ s 1 - root₂ s 1) * convSeq (root₁ s 1) (root₂ s 1) k =
      root₁ s 1 ^ (k + 1) - root₂ s 1 ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp [convSeq]
    | succ k ih =>
      simp only [convSeq]
      linear_combination root₂ s 1 * ih
  refine ⟨2 / ‖root₁ s 1 - root₂ s 1‖, fun k => ?_⟩
  have hpos : 0 < ‖root₁ s 1 - root₂ s 1‖ := norm_pos_iff.mpr hne
  have he : |chSeq s 1 k| = ‖convSeq (root₁ s 1) (root₂ s 1) k‖ := by
    rw [← chSeq_eq_convSeq]; simp
  rw [he, le_div_iff₀ hpos, mul_comm, ← norm_mul, key k]
  calc ‖root₁ s 1 ^ (k + 1) - root₂ s 1 ^ (k + 1)‖
      ≤ ‖root₁ s 1 ^ (k + 1)‖ + ‖root₂ s 1 ^ (k + 1)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, norm_pow, n1, n2]; norm_num

/-- Woodford (2003), Prop. C.2, p. 672: under `RecBounded`, every solution of
`x_{k+2} = s x_{k+1} − p x_k` is bounded, `x_{k+2} = S_{k+1} x₁ − p S_k x₀`. -/
theorem rec_seq_bounded {s p : ℝ} (hR : RecBounded s p) {x : ℕ → ℝ}
    (hx : ∀ k, x (k + 2) = s * x (k + 1) - p * x k) : ∃ C, ∀ k, |x k| ≤ C := by
  obtain ⟨C, hC⟩ := hR
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have key : ∀ k, x (k + 2) = chSeq s p (k + 1) * x 1 - p * chSeq s p k * x 0 ∧
      x (k + 3) = chSeq s p (k + 2) * x 1 - p * chSeq s p (k + 1) * x 0 := by
    intro k
    induction k with
    | zero =>
      refine ⟨by rw [hx 0]; simp [chSeq], ?_⟩
      rw [hx 1, hx 0]
      simp only [chSeq]
      ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 3 = (k + 2) + 2 by omega, hx (k + 2), show k + 2 + 1 = k + 3 by omega,
        ih.2, ih.1, show k + 1 + 2 = (k + 1) + 2 by omega]
      simp only [chSeq]
      ring
  refine ⟨|x 0| + |x 1| + C * |x 1| + |p| * C * |x 0|, fun k => ?_⟩
  have a0 := abs_nonneg (x 0)
  have a1 := abs_nonneg (x 1)
  have ap := abs_nonneg p
  match k with
  | 0 => nlinarith [mul_nonneg hC0 a1, mul_nonneg (mul_nonneg ap hC0) a0]
  | 1 => nlinarith [mul_nonneg hC0 a1, mul_nonneg (mul_nonneg ap hC0) a0]
  | k + 2 =>
    rw [(key k).1]
    calc |chSeq s p (k + 1) * x 1 - p * chSeq s p k * x 0|
        ≤ |chSeq s p (k + 1)| * |x 1| + |p| * |chSeq s p k| * |x 0| := by
          rw [← abs_mul, ← abs_mul, ← abs_mul]; exact abs_sub _ _
      _ ≤ C * |x 1| + |p| * C * |x 0| := by
          gcongr
          · exact hC _
          · exact hC _
      _ ≤ _ := by linarith

/-- Woodford (2003), Prop. C.2, p. 674 (Cayley–Hamilton through the real factorisation): if
`P(λ) = (λ − l₃)(λ² − sλ + p)` then `(A² − sA + p)(A − l₃) = 0`. -/
theorem quad_mul_lin {A : Matrix (Fin 3) (Fin 3) ℝ} {l3 s p : ℝ}
    (hs : RealSplit (ch2 A) (ch1 A) (ch0 A) l3 s p) :
    (A ^ 2 - s • A + p • (1 : Matrix (Fin 3) (Fin 3) ℝ)) * (A - l3 • 1) = 0 := by
  have CH := cayley_hamilton3 A
  obtain ⟨h2, h1, h0⟩ := hs
  rw [h2, h1, h0] at CH
  rw [← CH]
  simp only [sub_mul, add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    pow_succ, pow_zero]
  module

/-- Woodford (2003), Prop. C.2, p. 672: if `(A² − sA + p) u = 0` and `RecBounded s p`, the orbit
`Aᵗ u` is bounded. -/
theorem orbit_bounded_of_quad {A : Matrix (Fin 3) (Fin 3) ℝ} {s p : ℝ} {u : Fin 3 → ℝ}
    (hQ : (A ^ 2 - s • A + p • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ u = 0) (hR : RecBounded s p) :
    ∃ C, ∀ t i, |(A ^ t *ᵥ u) i| ≤ C := by
  have h2 : A ^ 2 *ᵥ u = s • (A *ᵥ u) - p • u := by
    rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at hQ
    rw [← sub_eq_zero, ← hQ]; abel
  have hrec : ∀ k, A ^ (k + 2) *ᵥ u = s • (A ^ (k + 1) *ᵥ u) - p • (A ^ k *ᵥ u) := by
    intro k
    rw [pow_add, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_succ]
  have hb : ∀ i, ∃ C, ∀ t, |(A ^ t *ᵥ u) i| ≤ C := fun i =>
    rec_seq_bounded hR (x := fun t => (A ^ t *ᵥ u) i) (fun k => by
      have := congrFun (hrec k) i
      simpa using this)
  obtain ⟨C0, h0⟩ := hb 0
  obtain ⟨C1, h1⟩ := hb 1
  obtain ⟨C2, h2'⟩ := hb 2
  refine ⟨|C0| + |C1| + |C2|, fun t i => ?_⟩
  fin_cases i
  · exact (h0 t).trans (by linarith [le_abs_self C0, abs_nonneg C1, abs_nonneg C2])
  · exact (h1 t).trans (by linarith [le_abs_self C1, abs_nonneg C0, abs_nonneg C2])
  · exact (h2' t).trans (by linarith [le_abs_self C2, abs_nonneg C0, abs_nonneg C1])

/-- Woodford (2003), Prop. C.2, p. 674 (multiplicity from a real factorisation): if
`P(λ) = (λ − l₃)(λ² − sλ + p)`, all solutions of `x_{k+2} = s x_{k+1} − p x_k` are bounded, and
`|l₃| ≤ 1` or `l₃` is not a root of `λ² − sλ + p`, then some `u ≠ 0` with `u₂ = 0` has a bounded
orbit. The vector is `(A − l₃) r` when the image of `A − l₃` meets `{u₂ = 0}`; otherwise
`A − l₃` has rank at most one, which makes `l₃` a double root. -/
theorem mult_of_realSplit {A : Matrix (Fin 3) (Fin 3) ℝ} {l3 s p : ℝ}
    (hs : RealSplit (ch2 A) (ch1 A) (ch0 A) l3 s p) (hR : RecBounded s p)
    (h3 : |l3| ≤ 1 ∨ l3 ^ 2 - s * l3 + p ≠ 0) :
    ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ u 2 = 0 ∧ ∃ C, ∀ t i, |(A ^ t *ᵥ u) i| ≤ C := by
  have hQM := quad_mul_lin hs
  set M := A - l3 • (1 : Matrix (Fin 3) (Fin 3) ℝ) with hM
  by_cases hex : ∃ r, (M *ᵥ r) 2 = 0 ∧ M *ᵥ r ≠ 0
  · obtain ⟨r, hr2, hr0⟩ := hex
    refine ⟨M *ᵥ r, hr0, hr2, orbit_bounded_of_quad ?_ hR⟩
    rw [Matrix.mulVec_mulVec, hQM, Matrix.zero_mulVec]
  push Not at hex
  have hMe : ∀ i j, M i j = A i j - l3 * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by
    rw [hM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  -- the relations `m_k M_ij = m_j M_ik`, `m = ` row 2 of `M`
  have hrel : ∀ i j k, M 2 k * M i j = M 2 j * M i k := by
    intro i j k
    set r : Fin 3 → ℝ := M 2 k • Pi.single j 1 - M 2 j • Pi.single k 1
    have hMr : M *ᵥ r = M 2 k • M.col j - M 2 j • M.col k := by
      simp only [r, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
    have h2 : (M *ᵥ r) 2 = 0 := by
      rw [hMr]; simp [Matrix.col_apply, mul_comm]
    have := congrFun (hex r h2) i
    rw [hMr] at this
    simpa [Matrix.col_apply, sub_eq_zero] using this
  -- all principal `2 × 2` minors of `M` vanish
  have hminor : ∀ i j, M i i * M j j - M i j * M j i = 0 := by
    intro i j
    by_cases hm : ∃ k, M 2 k ≠ 0
    · obtain ⟨k, hk⟩ := hm
      have e : M 2 k ^ 2 * (M i i * M j j - M i j * M j i) = 0 := by
        linear_combination (M 2 k * M j j) * hrel i i k + (M 2 i * M i k) * hrel j j k
          - (M 2 k * M j i) * hrel i j k - (M 2 j * M i k) * hrel j i k
      rcases mul_eq_zero.mp e with e | e
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp e) hk
      · exact e
    · push Not at hm
      have hz : ∀ a b, M a b = 0 := by
        intro a b
        have := hex (Pi.single b 1) (by simp [Matrix.col_apply, hm])
        have := congrFun this a
        simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
      rw [hz i i, hz j j, hz i j, hz j i]; ring
  -- the "no" case forces `l₃` to be a root of `λ² − sλ + p`
  have hq : l3 ^ 2 - s * l3 + p = 0 := by
    obtain ⟨h2, h1, -⟩ := hs
    have m01 := hminor 0 1
    have m02 := hminor 0 2
    have m12 := hminor 1 2
    simp only [hMe, Matrix.one_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at m01 m02 m12
    unfold ch2 at h2
    unfold ch1 at h1
    linear_combination m01 + m02 + m12 - h1 - 2 * l3 * h2
  -- an eigenvector of `l₃` with zero predetermined component
  have hl3 : |l3| ≤ 1 := by
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd hq h3
  set u : Fin 3 → ℝ := if M 2 0 = 0 ∧ M 2 1 = 0 then ![1, 0, 0] else ![M 2 1, -M 2 0, 0]
    with hu_def
  have hu2 : u 2 = 0 := by rw [hu_def]; split_ifs <;> simp
  have hu0 : u ≠ 0 := by
    rw [hu_def]
    split_ifs with h
    · intro h0; have := congrFun h0 0; simp at this
    · intro h0
      apply h
      have e0 : M 2 1 = 0 := by simpa using congrFun h0 0
      have e1 : M 2 0 = 0 := by simpa using congrFun h0 1
      exact ⟨e1, e0⟩
  have hMu2 : (M *ᵥ u) 2 = 0 := by
    rw [hu_def]
    split_ifs with h
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h.1]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring
  have hMu := hex u hMu2
  have hAu : A *ᵥ u = l3 • u := by
    rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMu
    exact hMu
  refine ⟨u, hu0, hu2, |u 0| + |u 1| + |u 2|, fun t i => ?_⟩
  rw [pow_mulVec_eigen hAu t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
  have h1 : |l3| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg _) hl3
  have h2 : |u i| ≤ |u 0| + |u 1| + |u 2| := by
    fin_cases i <;> simp <;> linarith [abs_nonneg (u 0), abs_nonneg (u 1), abs_nonneg (u 2)]
  calc |l3| ^ t * |u i| ≤ 1 * |u i| := by gcongr
    _ ≤ _ := by linarith

/-- Woodford (2003), Prop. C.1, p. 671 (backward uniqueness): if both roots of `λ² − sλ + p` lie
outside the unit circle, the only bounded solution of `x_{k+2} = s x_{k+1} − p x_k` is zero. -/
theorem rec_zero_of_bothOutside {s p : ℝ} (hb : BothOutside s p) {x : ℕ → ℝ}
    (hx : ∀ k, x (k + 2) = s * x (k + 1) - p * x k) (hxb : ∃ C, ∀ k, |x k| ≤ C) :
    ∀ k, x k = 0 := by
  obtain ⟨hp, hS⟩ := (bothOutside_iff_schurStable_inv s p).mp hb
  set B : Matrix (Fin 2) (Fin 2) ℝ := !![s / p, -(1 / p); 1, 0] with hB
  have htr : tr2 B = s / p := by simp [tr2, hB]
  have hdet : det2 B = 1 / p := by simp [det2, hB]
  set X : ℕ → Fin 2 → ℝ := fun t => ![x t, x (t + 1)] with hX
  have hXrec : ∀ t, X t = B.mulVec (X (t + 1)) := by
    intro t
    funext i
    fin_cases i
    · simp only [hX, hB, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.zero_eta, Fin.isValue]
      rw [hx t]
      field_simp
      ring
    · simp [hX, hB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  obtain ⟨C, hC⟩ := hxb
  have hXb : BoundedSeq X := ⟨C, fun t i => by fin_cases i <;> simp [hX, hC]⟩
  have hz := homogeneous_eq_zero (by rw [htr, hdet]; exact hS) hXrec hXb
  intro k
  have := congrFun (congrFun hz k) 0
  simpa [hX] using this

/-- Woodford (2003), Prop. C.2, p. 674 (no root inside): if
`P(λ) = (λ − l₃)(λ² − sλ + p)` with `|l₃| > 1` and both roots of `λ² − sλ + p` outside the unit
circle, the only bounded orbit of `y_{t+1} = A y_t` is zero. -/
theorem orbit_zero_of_realSplit {A : Matrix (Fin 3) (Fin 3) ℝ} {l3 s p : ℝ}
    (hs : RealSplit (ch2 A) (ch1 A) (ch0 A) l3 s p) (hl : 1 < |l3|) (hb : BothOutside s p)
    {Y : ℕ → Fin 3 → ℝ} (hY : ∀ t, Y (t + 1) = A *ᵥ Y t) (hYb : ∃ C, ∀ t i, |Y t i| ≤ C) :
    Y 0 = 0 := by
  have hQM := quad_mul_lin hs
  set M := A - l3 • (1 : Matrix (Fin 3) (Fin 3) ℝ) with hM
  obtain ⟨C, hC⟩ := hYb
  -- `W_t = M Y_t` solves the second-order recursion and is bounded, hence zero
  have hW : ∀ i, ∀ t, (M *ᵥ Y t) i = 0 := by
    intro i
    refine rec_zero_of_bothOutside hb (x := fun t => (M *ᵥ Y t) i) (fun k => ?_) ?_
    · have hY2 : Y (k + 2) = A ^ 2 *ᵥ Y k := by
        rw [hY, hY, Matrix.mulVec_mulVec, sq]
      have hcomm : (A ^ 2 - s • A + p • (1 : Matrix (Fin 3) (Fin 3) ℝ)) * M =
          M * (A ^ 2 - s • A + p • 1) := by
        rw [hM]
        simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
          mul_one, sq, mul_assoc]
        module
      have hQv : (A ^ 2 - s • A + p • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ Y k =
          Y (k + 2) - s • Y (k + 1) + p • Y k := by
        rw [hY2, hY k, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec]
      have h0 : M *ᵥ (Y (k + 2) - s • Y (k + 1) + p • Y k) = 0 := by
        rw [← hQv, Matrix.mulVec_mulVec, ← hcomm, hQM, Matrix.zero_mulVec]
      rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul] at h0
      have h0i := congrFun h0 i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0i
      change (M *ᵥ Y (k + 2)) i = s * (M *ᵥ Y (k + 1)) i - p * (M *ᵥ Y k) i
      linear_combination h0i
    · refine ⟨(∑ a, ∑ b, |M a b|) * max C 0, fun t => ?_⟩
      simp only [Matrix.mulVec, dotProduct]
      calc |∑ b, M i b * Y t b| ≤ ∑ b, |M i b| * max C 0 := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left ((hC t b).trans (le_max_left _ _)) (abs_nonneg _)
        _ = (∑ b, |M i b|) * max C 0 := by rw [Finset.sum_mul]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)
            exact Finset.single_le_sum (f := fun a => ∑ b, |M a b|)
              (fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _) (Finset.mem_univ i)
  -- hence `Y_0` is an eigenvector of `l₃`, and `|l₃| > 1` forces it to vanish
  have hA0 : A *ᵥ Y 0 = l3 • Y 0 := by
    have : M *ᵥ Y 0 = 0 := funext fun i => hW i 0
    rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
    exact this
  have hYt : ∀ t, Y t = l3 ^ t • Y 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [hY, ih, Matrix.mulVec_smul, hA0, smul_smul, pow_succ]
  funext i
  by_contra hne
  have hpos : 0 < |Y 0 i| := abs_pos.mpr hne
  have hgrow : Tendsto (fun t : ℕ => |l3| ^ t * |Y 0 i|) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hl).atTop_mul_const hpos
  obtain ⟨t, ht⟩ := (hgrow.eventually_gt_atTop C).exists
  have := hC t i
  rw [hYt t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow] at this
  linarith

/-- Woodford (2003), Prop. C.2, p. 674 (non-existence when no root is inside): with
`P(λ) = (λ − l₃)(λ² − sλ + p)`, `|l₃| > 1` and both roots of `λ² − sλ + p` outside the unit
circle, there is no bounded equilibrium with zero forcing and `x₀ ≠ 0` (the date-0 expectations
`E_0 y_t` form a bounded orbit of `A`). -/
theorem nonexist_of_realSplit [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ} {l3 s p : ℝ}
    (hs : RealSplit (ch2 A) (ch1 A) (ch0 A) l3 s p) (hl : 1 < |l3|) (hb : BothOutside s p)
    {x0 : ℝ} (hx0 : x0 ≠ 0) (y : ℕ → Fin 3 → Ω → ℝ) : ¬ Equil3 𝔼 A 0 x0 y := by
  rintro ⟨hsol, -, -, h0, ⟨C, hC⟩⟩
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  set Y : ℕ → Fin 3 → ℝ := fun t i => 𝔼.E 0 (y t i) ω with hYdef
  have hY : ∀ t, Y (t + 1) = A *ᵥ Y t := by
    intro t
    funext i
    have e := congrArg (𝔼.E 0) (hsol t i)
    rw [𝔼.tower (Nat.zero_le t)] at e
    have e' := congrFun e ω
    simp only [hYdef, e', Pi.zero_apply, add_zero, E_rvMul 𝔼]
    simp [rvMul_apply, Matrix.mulVec, dotProduct]
  have hYb : ∃ C, ∀ t i, |Y t i| ≤ C := ⟨C, fun t i => 𝔼.abs_E_le (hC t i) 0 ω⟩
  have hz := orbit_zero_of_realSplit hs hl hb hY hYb
  have := congrFun hz 2
  simp only [hYdef, Pi.zero_apply, h0, 𝔼.const] at this
  exact hx0 this

/-- Woodford (2003), Prop. C.2, p. 672, fn. 2 (a real root on the unit circle, resonance): if
`q A = λ q` with `λ² = 1` and `q · a ≠ 0`, then for the bounded disturbance `e_t = λᵗ` there is no
bounded equilibrium — `E_0 (q · y_t) = λᵗ (q · y_0 + t (q · a) λ)` grows without bound. -/
theorem nonexist_of_unit_left [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ} {a q : Fin 3 → ℝ}
    {lam : ℝ} (hq : q ᵥ* A = lam • q) (hl : lam ^ 2 = 1) (hc : ∑ i, q i * a i ≠ 0) (x0 : ℝ)
    (y : ℕ → Fin 3 → Ω → ℝ) : ¬ Equil3 𝔼 A (fun t i => a i • (fun _ => lam ^ t)) x0 y := by
  rintro ⟨hsol, -, -, -, ⟨C, hC⟩⟩
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  set Y : ℕ → Fin 3 → ℝ := fun t i => 𝔼.E 0 (y t i) ω with hYdef
  have hY : ∀ t i, Y (t + 1) i = ∑ j, A i j * Y t j + a i * lam ^ t := by
    intro t i
    have e := congrArg (𝔼.E 0) (hsol t i)
    rw [𝔼.tower (Nat.zero_le t)] at e
    have e' := congrFun e ω
    simp only [hYdef, e', map_add, E_rvMul 𝔼, Pi.add_apply, rvMul_apply, map_smul, 𝔼.const,
      Pi.smul_apply, smul_eq_mul]
  set c := ∑ i, q i * a i with hc_def
  set S : ℕ → ℝ := fun t => ∑ i, q i * Y t i with hS_def
  have hqj : ∀ j, ∑ i, q i * A i j = lam * q j := fun j => by
    have := congrFun hq j
    simpa [Matrix.vecMul, dotProduct] using this
  have hS : ∀ t, S (t + 1) = lam * S t + c * lam ^ t := by
    intro t
    simp only [hS_def, hY, hc_def, Fin.sum_univ_three] at hqj ⊢
    linear_combination (Y t 0) * hqj 0 + (Y t 1) * hqj 1 + (Y t 2) * hqj 2
  have hclosed : ∀ t : ℕ, S t = lam ^ t * (S 0 + t * c * lam) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hS t, ih]
      push_cast
      linear_combination (-(c * lam ^ t)) * hl
  have habs : |lam| = 1 := by
    have h1 : |lam| ^ 2 = 1 := by rw [sq_abs]; exact hl
    have := abs_nonneg lam
    nlinarith
  set B : ℝ := (∑ i, |q i|) * max C 0 with hB
  have hSb : ∀ t, |S t| ≤ B := by
    intro t
    simp only [hS_def]
    calc |∑ i, q i * Y t i| ≤ ∑ i, |q i| * max C 0 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            ((𝔼.abs_E_le (hC t i) 0 ω).trans (le_max_left _ _)) (abs_nonneg _)
      _ = B := by rw [hB, Finset.sum_mul]
  have hcpos : 0 < |c| := abs_pos.mpr hc
  obtain ⟨t, ht⟩ := exists_nat_gt ((B + |S 0|) / |c|)
  have h1 := hSb t
  rw [hclosed t, abs_mul, abs_pow, habs, one_pow, one_mul] at h1
  have h2 : (t : ℝ) * |c| ≤ |S 0 + t * c * lam| + |S 0| := by
    have e : |(t : ℝ) * c * lam| = t * |c| := by
      rw [abs_mul, abs_mul, habs, mul_one, abs_of_nonneg (Nat.cast_nonneg t)]
    have := abs_sub_abs_le_abs_sub (t * c * lam) (-(S 0))
    rw [sub_neg_eq_add, add_comm (↑t * c * lam), abs_neg, e] at this
    linarith
  rw [div_lt_iff₀ hcpos] at ht
  linarith

/-- Woodford (2003), Prop. C.2, p. 672, fn. 2: a real eigenvalue `±1` whose left eigenvector is
not orthogonal to the disturbance direction rules out determinacy (non-existence). -/
theorem not_determinateFor_of_unit_left [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ}
    {a q : Fin 3 → ℝ} {lam : ℝ} (hq : q ᵥ* A = lam • q) (hl : lam ^ 2 = 1)
    (hc : ∑ i, q i * a i ≠ 0) : ¬ DeterminateFor 𝔼 A a := by
  intro h
  have habs : |lam| = 1 := by
    have h1 : |lam| ^ 2 = 1 := by rw [sq_abs]; exact hl
    have := abs_nonneg lam
    nlinarith
  obtain ⟨y, hy, -⟩ := h (fun t _ => lam ^ t)
    ⟨1, fun t _ => by rw [abs_pow, habs, one_pow]⟩ (fun t => 𝔼.const t _) 0
  exact nonexist_of_unit_left 𝔼 hq hl hc 0 y hy

/-- Woodford (2003), Prop. C.2, p. 672, fn. 2: an eigenvalue `±1` rules out determinacy for
general forcing. -/
theorem not_determinate3_of_unit_root [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ} {lam : ℝ}
    (hroot : cubicR (ch2 A) (ch1 A) (ch0 A) lam = 0) (hl : lam ^ 2 = 1) :
    ¬ Determinate3 𝔼 A := by
  obtain ⟨q, hq0, hq⟩ := exists_left_eigvec hroot
  intro h
  refine not_determinateFor_of_unit_left 𝔼 hq hl ?_ (determinateFor_of_determinate3 𝔼 h q)
  intro hs
  apply hq0
  simp only [Fin.sum_univ_three] at hs
  have h0 : q 0 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1), sq_nonneg (q 2)]
  have h1 : q 1 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1), sq_nonneg (q 2)]
  have h2 : q 2 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1), sq_nonneg (q 2)]
  funext i
  fin_cases i <;> simp [h0, h1, h2]

/-! ### Root configurations of the characteristic polynomial -/

/-- Woodford (2003), p. 674: the order of the roots in a factorisation is immaterial
(first two). -/
theorem factors_swap12 {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    Factors a2 a1 a0 l2 l1 l3 := fun z => by rw [h z]; ring

/-- Woodford (2003), p. 674: the order of the roots in a factorisation is immaterial
(last two). -/
theorem factors_swap23 {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) :
    Factors a2 a1 a0 l1 l3 l2 := fun z => by rw [h z]; ring

/-- Woodford (2003), p. 674: the conjugate of a root is a root. -/
theorem conj_root {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3) {z : ℂ}
    (hz : z = l1 ∨ z = l2 ∨ z = l3) :
    starRingEnd ℂ z = l1 ∨ starRingEnd ℂ z = l2 ∨ starRingEnd ℂ z = l3 := by
  have hz0 : cubic a2 a1 a0 z = 0 := by
    rcases hz with rfl | rfl | rfl <;> rw [h] <;> ring
  have hc : cubic a2 a1 a0 (starRingEnd ℂ z) = 0 := by rw [cubic_conj, hz0, map_zero]
  rw [h] at hc
  rcases mul_eq_zero.mp hc with hc | hc
  · rcases mul_eq_zero.mp hc with hc | hc
    · exact Or.inl (sub_eq_zero.mp hc)
    · exact Or.inr (Or.inl (sub_eq_zero.mp hc))
  · exact Or.inr (Or.inr (sub_eq_zero.mp hc))

/-- Woodford (2003), p. 674 (one real root and a complex pair, or three real roots): two roots
with a conjugation-invariant property `P` can be taken to form a real pair (both real or complex
conjugates), the remaining root being real. -/
theorem exists_realPair {a2 a1 a0 : ℝ} {l1 l2 l3 : ℂ} (h : Factors a2 a1 a0 l1 l2 l3)
    (P : ℂ → Prop) (hP : ∀ z, P (starRingEnd ℂ z) ↔ P z) (h1 : P l1) (h2 : P l2) :
    ∃ k1 k2 k3 : ℂ, Factors a2 a1 a0 k1 k2 k3 ∧ P k1 ∧ P k2 ∧ (k3 = l1 ∨ k3 = l2 ∨ k3 = l3) ∧
      (k1 + k2).im = 0 ∧ (k1 * k2).im = 0 ∧ k3.im = 0 := by
  obtain ⟨v2, -, -⟩ := factors_vieta h
  have hsum : (l1 + l2 + l3).im = 0 := by
    have := congrArg Complex.im v2
    simp only [Complex.ofReal_im, Complex.neg_im, Complex.add_im] at this
    simp only [Complex.add_im]
    linarith
  by_cases r1 : l1.im = 0
  · by_cases r2 : l2.im = 0
    · refine ⟨l1, l2, l3, h, h1, h2, Or.inr (Or.inr rfl), by simp [r1, r2], by simp [r1, r2], ?_⟩
      simp only [Complex.add_im] at hsum; linarith
    · rcases conj_root h (Or.inr (Or.inl rfl)) with c | c | c
      · exfalso; apply r2
        have := congrArg Complex.im c
        simp only [Complex.conj_im] at this; linarith
      · exfalso; apply r2
        exact Complex.conj_eq_iff_im.mp c
      · refine ⟨l2, l3, l1, factors_swap23 (factors_swap12 h), h2, ?_, Or.inl rfl, ?_, ?_, r1⟩
        · rw [← c, hP]; exact h2
        · rw [← c]; simp
        · rw [← c]; simp; ring
  · rcases conj_root h (Or.inl rfl) with c | c | c
    · exact absurd (Complex.conj_eq_iff_im.mp c) r1
    · refine ⟨l1, l2, l3, h, h1, h2, Or.inr (Or.inr rfl), ?_, ?_, ?_⟩
      · rw [← c]; simp
      · rw [← c]; simp; ring
      · simp only [Complex.add_im] at hsum
        rw [← c] at hsum; simp only [Complex.conj_im] at hsum; linarith
    · refine ⟨l1, l3, l2, factors_swap23 h, h1, ?_, Or.inr (Or.inl rfl), ?_, ?_, ?_⟩
      · rw [← c, hP]; exact h1
      · rw [← c]; simp
      · rw [← c]; simp; ring
      · simp only [Complex.add_im] at hsum
        rw [← c] at hsum; simp only [Complex.conj_im] at hsum; linarith

/-- Woodford (2003), p. 674: a factorisation whose first two roots form a real pair and whose
third root is real gives a real split `P(λ) = (λ − l)(λ² − sλ + p)`. -/
theorem realSplit_of_realPair {a2 a1 a0 : ℝ} {k1 k2 k3 : ℂ} (h : Factors a2 a1 a0 k1 k2 k3)
    (hs : (k1 + k2).im = 0) (hp : (k1 * k2).im = 0) (hl : k3.im = 0) :
    RealSplit a2 a1 a0 k3.re (k1 + k2).re (k1 * k2).re ∧
      ∀ z : ℂ, z ^ 2 - ((k1 + k2).re : ℂ) * z + ((k1 * k2).re : ℂ) = (z - k1) * (z - k2) := by
  have es : ((k1 + k2).re : ℂ) = k1 + k2 := Complex.ext (by simp) (by simp [hs])
  have ep : ((k1 * k2).re : ℂ) = k1 * k2 := Complex.ext (by simp) (by simp [hp])
  have el : (k3.re : ℂ) = k3 := Complex.ext (by simp) (by simp [hl])
  obtain ⟨v2, v1, v0⟩ := factors_vieta h
  refine ⟨⟨?_, ?_, ?_⟩, fun z => ?_⟩
  · exact_mod_cast (show (a2 : ℂ) = -((k3.re : ℂ) + ((k1 + k2).re : ℂ)) by
      rw [es, el, v2]; ring)
  · exact_mod_cast (show (a1 : ℂ) = ((k1 * k2).re : ℂ) + (k3.re : ℂ) * ((k1 + k2).re : ℂ) by
      rw [es, el, ep, v1]; ring)
  · exact_mod_cast (show (a0 : ℂ) = -((k3.re : ℂ) * ((k1 * k2).re : ℂ)) by
      rw [ep, el, v0]; ring)
  · rw [es, ep]; ring

/-- **Two roots inside ⇒ multiplicity** (Woodford (2003), Prop. C.2, p. 672, the converse the
book assumes): if two eigenvalues (with multiplicity) lie in the open unit disc, there is a
nonzero bounded equilibrium with zero forcing and `x₀ = 0` — a self-fulfilling path. -/
theorem mult_of_two_inside [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ} {l1 l2 l3 : ℂ}
    (h : Factors (ch2 A) (ch1 A) (ch0 A) l1 l2 l3) (h1 : ‖l1‖ < 1) (h2 : ‖l2‖ < 1) :
    ∃ y, Equil3 𝔼 A 0 0 y ∧ y ≠ 0 := by
  obtain ⟨k1, k2, k3, hk, p1, p2, -, hs, hp, hl⟩ :=
    exists_realPair h (fun z => ‖z‖ < 1) (fun z => by simp) h1 h2
  obtain ⟨hsplit, hfac⟩ := realSplit_of_realPair hk hs hp hl
  have hR := recBounded_of_schurStable (schurStable_of_factor hfac p1 p2)
  have h3 : |k3.re| ≤ 1 ∨ k3.re ^ 2 - (k1 + k2).re * k3.re + (k1 * k2).re ≠ 0 := by
    by_cases hc : |k3.re| ≤ 1
    · exact Or.inl hc
    · right
      push Not at hc
      intro h0
      have hz := hfac (k3.re : ℂ)
      have h0' : ((k3.re ^ 2 - (k1 + k2).re * k3.re + (k1 * k2).re : ℝ) : ℂ) = 0 := by
        rw [h0]; simp
      push_cast at h0'
      rw [h0'] at hz
      rcases mul_eq_zero.mp hz.symm with e | e
      · have := congrArg norm (sub_eq_zero.mp e)
        rw [Complex.norm_real, Real.norm_eq_abs] at this
        linarith
      · have := congrArg norm (sub_eq_zero.mp e)
        rw [Complex.norm_real, Real.norm_eq_abs] at this
        linarith
  obtain ⟨u, hu0, hu2, C, hC⟩ := mult_of_realSplit hsplit hR h3
  have he := equil_orbit 𝔼 hC
  rw [hu2] at he
  refine ⟨_, he, fun h0 => hu0 ?_⟩
  funext i
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun (congrFun h0 0) i) ω
  simpa using this

/-- **No root inside ⇒ non-existence** (Woodford (2003), Prop. C.2, p. 672, the converse the book
assumes): if all three eigenvalues lie outside the closed unit disc, there is no bounded
equilibrium with zero forcing and `x₀ = 1`. -/
theorem nonexist_of_none_inside [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ} {l1 l2 l3 : ℂ}
    (h : Factors (ch2 A) (ch1 A) (ch0 A) l1 l2 l3) (h1 : 1 < ‖l1‖) (h2 : 1 < ‖l2‖)
    (h3 : 1 < ‖l3‖) (y : ℕ → Fin 3 → Ω → ℝ) : ¬ Equil3 𝔼 A 0 1 y := by
  obtain ⟨k1, k2, k3, hk, p1, p2, hk3, hs, hp, hl⟩ :=
    exists_realPair h (fun z => 1 < ‖z‖) (fun z => by simp) h1 h2
  obtain ⟨hsplit, hfac⟩ := realSplit_of_realPair hk hs hp hl
  have hn3 : 1 < ‖k3‖ := by rcases hk3 with rfl | rfl | rfl <;> assumption
  have el : (k3.re : ℂ) = k3 := Complex.ext (by simp) (by simp [hl])
  have habs : 1 < |k3.re| := by rwa [← el, Complex.norm_real, Real.norm_eq_abs] at hn3
  exact nonexist_of_realSplit 𝔼 hsplit habs (bothOutside_of_factor hfac p1 p2) one_ne_zero y

/-- Woodford (2003), Prop. C.2, p. 672 (converse, any disturbance direction): two eigenvalues in
the open unit disc rule out determinacy (multiplicity). -/
theorem not_determinateFor_of_two_inside [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ}
    (a : Fin 3 → ℝ) {l1 l2 l3 : ℂ} (h : Factors (ch2 A) (ch1 A) (ch0 A) l1 l2 l3)
    (h1 : ‖l1‖ < 1) (h2 : ‖l2‖ < 1) : ¬ DeterminateFor 𝔼 A a := by
  obtain ⟨y, hy, hne⟩ := mult_of_two_inside 𝔼 h h1 h2
  exact not_determinateFor_of_mult 𝔼 a hy hne

/-- Woodford (2003), Prop. C.2, p. 672 (converse, any disturbance direction): no eigenvalue in
the closed unit disc rules out determinacy (non-existence). -/
theorem not_determinateFor_of_none_inside [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ}
    (a : Fin 3 → ℝ) {l1 l2 l3 : ℂ} (h : Factors (ch2 A) (ch1 A) (ch0 A) l1 l2 l3)
    (h1 : 1 < ‖l1‖) (h2 : 1 < ‖l2‖) (h3 : 1 < ‖l3‖) : ¬ DeterminateFor 𝔼 A a :=
  not_determinateFor_of_nonexist 𝔼 a (nonexist_of_none_inside 𝔼 h h1 h2 h3)

/-- Woodford (2003), Prop. C.2, pp. 672–676 (every root configuration): either exactly one
eigenvalue is inside and two outside, or there is a real eigenvalue `±1`, or a self-fulfilling
path exists (zero forcing, `x₀ = 0`), or no bounded equilibrium exists (zero forcing, `x₀ = 1`). -/
theorem oneInTwoOut_or_fails [Nonempty Ω] (A : Matrix (Fin 3) (Fin 3) ℝ) :
    OneInTwoOut (ch2 A) (ch1 A) (ch0 A) ∨
      (∃ lam : ℝ, lam ^ 2 = 1 ∧ cubicR (ch2 A) (ch1 A) (ch0 A) lam = 0) ∨
      (∃ y, Equil3 𝔼 A 0 0 y ∧ y ≠ 0) ∨ (∀ y, ¬ Equil3 𝔼 A 0 1 y) := by
  obtain ⟨r, T, D, hs⟩ := exists_realSplit (ch2 A) (ch1 A) (ch0 A)
  have F := factors_of_realSplit hs
  have hr0 : cubicR (ch2 A) (ch1 A) (ch0 A) r = 0 := by rw [cubicR_of_realSplit hs]; ring
  have nr : ‖(r : ℂ)‖ = |r| := by rw [Complex.norm_real, Real.norm_eq_abs]
  -- a real root of modulus one
  have unit_of_real : ∀ x : ℝ, |x| = 1 → (x : ℂ) = root₁ T D ∨ (x : ℂ) = root₂ T D →
      ∃ lam : ℝ, lam ^ 2 = 1 ∧ cubicR (ch2 A) (ch1 A) (ch0 A) lam = 0 := by
    intro x hx hroot
    refine ⟨x, by rw [← sq_abs, hx]; norm_num, ?_⟩
    have hc : cubic (ch2 A) (ch1 A) (ch0 A) x = 0 := by
      rw [F]; rcases hroot with e | e <;> rw [e] <;> ring
    rw [cubic_ofReal] at hc
    exact_mod_cast hc
  -- a complex pair on the unit circle gives a self-fulfilling path
  have circle : disc T D < 0 → D = 1 → ∃ y, Equil3 𝔼 A 0 0 y ∧ y ≠ 0 := by
    intro hd hD1
    subst hD1
    have hR := recBounded_of_circle hd
    have hq : r ^ 2 - T * r + 1 ≠ 0 := by
      unfold disc at hd; nlinarith [sq_nonneg (2 * r - T)]
    obtain ⟨u, hu0, hu2, C, hC⟩ := mult_of_realSplit hs hR (Or.inr hq)
    have he := equil_orbit 𝔼 hC
    rw [hu2] at he
    refine ⟨_, he, fun h0 => hu0 ?_⟩
    funext i
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrFun h0 0) i) ω
    simpa using this
  -- unit-modulus roots
  by_cases u0 : |r| = 1
  · exact Or.inr (Or.inl ⟨r, by rw [← sq_abs, u0]; norm_num, hr0⟩)
  by_cases u1 : ‖root₁ T D‖ = 1
  · by_cases hd : 0 ≤ disc T D
    · refine Or.inr (Or.inl (unit_of_real ((T + Real.sqrt (disc T D)) / 2) ?_ (Or.inl ?_)))
      · rw [← (norm_root_of_nonneg hd).1]; exact u1
      · unfold root₁; simp [hd]
    · have hD := (normSq_root_of_neg (not_le.mp hd)).1
      rw [u1] at hD
      exact Or.inr (Or.inr (Or.inl (circle (not_le.mp hd) (by linarith))))
  by_cases u2 : ‖root₂ T D‖ = 1
  · by_cases hd : 0 ≤ disc T D
    · refine Or.inr (Or.inl (unit_of_real ((T - Real.sqrt (disc T D)) / 2) ?_ (Or.inr ?_)))
      · rw [← (norm_root_of_nonneg hd).2]; exact u2
      · unfold root₂; simp [hd]
    · have hD := (normSq_root_of_neg (not_le.mp hd)).2
      rw [u2] at hD
      exact Or.inr (Or.inr (Or.inl (circle (not_le.mp hd) (by linarith))))
  -- no root on the unit circle: count the roots inside
  rw [← nr] at u0
  rcases lt_or_gt_of_ne u0 with a | a <;> rcases lt_or_gt_of_ne u1 with b | b <;>
    rcases lt_or_gt_of_ne u2 with c | c
  · exact Or.inr (Or.inr (Or.inl (mult_of_two_inside 𝔼 F a b)))
  · exact Or.inr (Or.inr (Or.inl (mult_of_two_inside 𝔼 F a b)))
  · exact Or.inr (Or.inr (Or.inl (mult_of_two_inside 𝔼 (factors_swap23 F) a c)))
  · exact Or.inl ⟨_, _, _, F, a, b, c⟩
  · exact Or.inr (Or.inr (Or.inl
      (mult_of_two_inside 𝔼 (factors_swap23 (factors_swap12 F)) b c)))
  · exact Or.inl ⟨_, _, _, factors_swap12 F, b, a, c⟩
  · exact Or.inl ⟨_, _, _, factors_swap12 (factors_swap23 F), c, a, b⟩
  · exact Or.inr (Or.inr (Or.inr (nonexist_of_none_inside 𝔼 F a b c)))

/-- **Blanchard–Kahn converse** (Woodford (2003), Prop. C.2, p. 672): determinacy for general
forcing implies exactly one eigenvalue inside and two outside the unit circle. -/
theorem oneInTwoOut_of_determinate3 [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ}
    (h : Determinate3 𝔼 A) : OneInTwoOut (ch2 A) (ch1 A) (ch0 A) := by
  rcases oneInTwoOut_or_fails 𝔼 A with h1 | ⟨lam, hl, hr⟩ | ⟨y, hy, hne⟩ | hn
  · exact h1
  · exact absurd h (not_determinate3_of_unit_root 𝔼 hr hl)
  · exact absurd (determinateFor_of_determinate3 𝔼 h 0) (not_determinateFor_of_mult 𝔼 0 hy hne)
  · exact absurd (determinateFor_of_determinate3 𝔼 h 0) (not_determinateFor_of_nonexist 𝔼 0 hn)

/-- **Blanchard–Kahn converse for a model** (Woodford (2003), Prop. C.2, p. 672 and fn. 2): if
`±1` are not eigenvalues (`P(1) ≠ 0`, `P(−1) ≠ 0`), determinacy of
`E_t y_{t+1} = A y_t + a e_t` implies exactly one eigenvalue inside and two outside. -/
theorem oneInTwoOut_of_determinateFor [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ}
    {a : Fin 3 → ℝ} (h : DeterminateFor 𝔼 A a) (h1 : P1 (ch2 A) (ch1 A) (ch0 A) ≠ 0)
    (hm1 : Pm1 (ch2 A) (ch1 A) (ch0 A) ≠ 0) : OneInTwoOut (ch2 A) (ch1 A) (ch0 A) := by
  rcases oneInTwoOut_or_fails 𝔼 A with h' | ⟨lam, hl, hr⟩ | ⟨y, hy, hne⟩ | hn
  · exact h'
  · exfalso
    have : (lam - 1) * (lam + 1) = 0 := by linear_combination hl
    rcases mul_eq_zero.mp this with e | e
    · rw [show lam = 1 by linarith, ← P1_eq] at hr; exact h1 hr
    · rw [show lam = -1 by linarith, ← Pm1_eq] at hr; exact hm1 hr
  · exact absurd h (not_determinateFor_of_mult 𝔼 a hy hne)
  · exact absurd h (not_determinateFor_of_nonexist 𝔼 a hn)

/-- Woodford (2003), Prop. C.2, p. 672, fn. 2: determinacy implies the genericity condition. -/
theorem generic_of_determinateFor [Nonempty Ω] {A : Matrix (Fin 3) (Fin 3) ℝ} {a : Fin 3 → ℝ}
    (h : DeterminateFor 𝔼 A a) : Generic A := by
  intro μ v hμ hv h2
  by_contra hne
  obtain ⟨y, hy, hy0⟩ := mult_of_eigen 𝔼 hμ.le hv h2 hne
  exact not_determinateFor_of_mult 𝔼 a hy hy0 h

/-- **The Blanchard–Kahn theorem** (Woodford (2003), Prop. C.2, p. 672, first sentence, which the
book takes from Blanchard and Kahn (1980)): with one predetermined variable, the system is
determinate iff exactly one eigenvalue lies in the open unit disc and two outside the closed disc,
**and** the stable eigenvector has a nonzero predetermined component (`Generic`). -/
theorem determinate3_iff [Nonempty Ω] (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Determinate3 𝔼 A ↔ OneInTwoOut (ch2 A) (ch1 A) (ch0 A) ∧ Generic A :=
  ⟨fun h => ⟨oneInTwoOut_of_determinate3 𝔼 h,
    generic_of_determinateFor 𝔼 (determinateFor_of_determinate3 𝔼 h 0)⟩,
   fun h => determinate3_of 𝔼 h.1 h.2⟩

/-- Woodford (2003), Prop. C.2, p. 672 (the counting criterion with the cases of p. 673): the
system is determinate iff Case I, II or III′ holds and the genericity condition holds. -/
theorem determinate3_iff_cases [Nonempty Ω] (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Determinate3 𝔼 A ↔ (CaseI3 (ch2 A) (ch1 A) (ch0 A) ∨ CaseII3 (ch2 A) (ch1 A) (ch0 A) ∨
      CaseIII3' (ch2 A) (ch1 A) (ch0 A)) ∧ Generic A := by
  rw [determinate3_iff, oneInTwoOut_iff_cases]

/-- Woodford (2003), Prop. C.2, p. 672 (counterexample: the eigenvalue count alone is not
sufficient): `A = diag(1/2, 2, 2)`. -/
noncomputable def diagEx : Matrix (Fin 3) (Fin 3) ℝ := !![1 / 2, 0, 0; 0, 2, 0; 0, 0, 2]

/-- Woodford (2003), Prop. C.2, p. 672: `diag(1/2, 2, 2)` has exactly one eigenvalue inside and
two outside the unit circle. -/
theorem diagEx_oneInTwoOut : OneInTwoOut (ch2 diagEx) (ch1 diagEx) (ch0 diagEx) := by
  refine (oneInTwoOut_iff_real _ _ _).mpr ⟨1 / 2, 4, 4, by norm_num [abs_of_pos], ?_, ?_⟩
  · rw [bothOutside_iff_cases]; left; unfold CaseI2; norm_num
  · unfold RealSplit ch2 ch1 ch0 diagEx; norm_num

/-- Woodford (2003), Prop. C.2, p. 672 (the printed first sentence is false without genericity):
`diag(1/2, 2, 2)` satisfies the eigenvalue count but is not determinate — its stable eigenvector
`(1, 0, 0)` is a non-predetermined direction, so `z_t = 2⁻ᵗ` is a self-fulfilling path. -/
theorem diagEx_not_determinate [Nonempty Ω] : ¬ Determinate3 𝔼 diagEx := by
  intro h
  have hg := ((determinate3_iff 𝔼 diagEx).mp h).2
  have := hg (1 / 2) ![1, 0, 0] (by norm_num [abs_of_pos])
    (by funext i; fin_cases i <;> simp [diagEx, Matrix.mulVec, dotProduct, Fin.sum_univ_three])
    (by simp)
  have := congrFun this 0
  simp at this

end Woodford.NeoWicksellianFramework.BlanchardKahn
