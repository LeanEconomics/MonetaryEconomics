/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.ForwardSolution
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Vector forward systems

Woodford (2003), *Interest and Prices*, Appendix C.1, pp. 670–672 (and the uses in Chapter 5,
pp. 327–335 and 375–376): the shared theory of vector expectational systems used by several
modules of this project (the Chapter 4 Proposition 4.3 restatement, the habit model (1.30)–(1.33),
Proposition C.1 for (2.8), and the investment model (3.36)). Restated from the Woodford Chapter 4
project (`BlanchardKahn`, `InflationDeterminants`) and the Galí Chapter 6 project
(`Determinacy4`).

## Main results

* `rvMul`: a constant matrix acting on a vector of random variables, with its algebra
  (`rvMul_rvMul`, `rvMul_add`, `rvMul_sub`, `rvMul_neg`, `rvMul_one`, `rvMul_zero`,
  `rvMul_apply`, `rvMul_smul_const`, `E_rvMul`, `abs_rvMul_le`, `vBounded_rvMul`,
  `vAdapted_rvMul`).
* `FSolves` (`s_t = K E_t s_{t+1} + w_t`): `pow_entry_bound` (eigenvalues inside the unit disc
  give geometric decay of `Kᵏ`, Gelfand's formula), `fsolves_unique`, and the explicit forward
  series `fwdVec` with `fwdVec_spec` (bounded adapted solution).
* The `2 × 2` case: `pow_geom_bound` (Schur–Cohn gives geometric decay), `solves_iff_fsolves`,
  `fwd_existsUnique`.
* `abs_rec_le`: a stable scalar recursion stays bounded.
* `secondOrder_forward_iff`, `secondOrder_forward_existsUnique`: `a₀ E_t x_{t+2} − a₁ x_{t+1}
  + a₂ x_t = f_t` with `A(L) = a₀(1 − μ₁L)(1 − μ₂L)`, `|μ₁| < 1 < |μ₂|`, has the unique bounded
  predetermined solution `x_{t+1} = μ₁ x_t + w_t` (`wSol`, `path`) — (3.20)–(3.22), (D.3)–(D.4).
* `unitRoot_iterate`, `unitRoot_forward_iff`: iterating the bond-pricing relation
  `î_t = λ̂_t + E_t[π_{t+1} − λ̂_{t+1}]` (pp. 325, 365) and its forward solution.
* `ExpSys` (`E_t x_{t+1} = A x_t + w_t`): `existsUnique_of_eigenOut` and
  `expSysDeterminate_iff` — determinate iff every eigenvalue of `A` lies outside the unit circle.
-/

namespace Woodford.PolicyResponseDynamics.ForwardSystems

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Matrices acting on vectors of random variables -/

/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project): A matrix acting on a vector
of random variables: `(M a)_i = ∑_j M_{ij} a_j`. -/
def rvMul {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    Fin n → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project) (tool): matrices act on
vectors of random variables compatibly with multiplication. -/
theorem rvMul_rvMul {n m l : ℕ} (M : Matrix (Fin n) (Fin m) ℝ)
    (N : Matrix (Fin m) (Fin l) ℝ) (a : Fin l → Ω → ℝ) :
    rvMul M (rvMul N a) = rvMul (M * N) a := by
  funext i
  simp only [rvMul, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Woodford (2003), p. 670 (tool): additivity of the action. -/
theorem rvMul_add {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a + b) = rvMul M a + rvMul M b := by
  funext i
  simp only [rvMul, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Woodford (2003), p. 670 (tool): the action respects subtraction. -/
theorem rvMul_sub {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a - b) = rvMul M a - rvMul M b := by
  funext i
  simp only [rvMul, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]


/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project) (tool): the identity matrix
acts trivially. -/
theorem rvMul_one {n : ℕ} (a : Fin n → Ω → ℝ) : rvMul 1 a = a := by
  funext i
  simp [rvMul, Matrix.one_apply]


/-- Woodford (2003), p. 670 (tool): the action on the zero vector. -/
theorem rvMul_zero {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) :
    rvMul M (0 : Fin m → Ω → ℝ) = 0 := by
  funext i
  simp [rvMul]


omit 𝔼 in
/-- Woodford (2003), p. 376 (tool): `(−M)` acts as `−M`. -/
theorem rvMul_neg {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    rvMul (-M) a = -rvMul M a := by
  funext i
  simp only [rvMul, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib, Pi.neg_apply]


/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project) (tool): the action,
pointwise. -/
theorem rvMul_apply {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) (ω : Ω) : rvMul M a i ω = ∑ j, M i j * a j ω := by
  simp [rvMul, Finset.sum_apply]


omit 𝔼 in
/-- Woodford (2003), p. 335: a matrix acting on a scalar shock with loading `v`:
`M (v g) = (M v) g`. -/
theorem rvMul_smul_const {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (v : Fin m → ℝ)
    (y : Ω → ℝ) : rvMul M (fun j => v j • y) = fun i => (M.mulVec v) i • y := by
  funext i
  simp only [rvMul, smul_smul, ← Finset.sum_smul, Matrix.mulVec, dotProduct]


omit 𝔼 in
/-- Woodford (2003), p. 376 (tool): a matrix acting on a bounded vector is bounded. -/
theorem abs_rvMul_le {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) {a : Fin m → Ω → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (ha : ∀ j ω, |a j ω| ≤ B) (i : Fin n) (ω : Ω) :
    |rvMul M a i ω| ≤ (∑ i, ∑ j, |M i j|) * B := by
  rw [rvMul_apply]
  calc |∑ j, M i j * a j ω| ≤ ∑ j, |M i j * a j ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * B := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (ha j ω) (abs_nonneg _)
    _ = (∑ j, |M i j|) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ j, |M i j|) * B :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)) hB


/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project) (tool): `E_t` commutes with
constant matrices. -/
theorem E_rvMul {n m : ℕ} (t : ℕ) (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) : 𝔼.E t (rvMul M a i) = rvMul M (fun j => 𝔼.E t (a j)) i := by
  simp only [rvMul, map_sum, map_smul]

/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project): A vector process solves the
forward system `s_t = K E_t s_{t+1} + w_t`. -/
def FSolves {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (w s : ℕ → Fin n → Ω → ℝ) : Prop :=
  ∀ t, s t = rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project): A vector process is adapted.
-/
def VAdapted {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project): A vector process is bounded.
-/
def VBounded {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M


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


/-! ### Forward systems `s_t = K E_t s_{t+1} + w_t` -/

/-- Woodford (2003), p. 670, fn. 1 (Blanchard–Kahn, the tool): if every complex
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
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero]
      exact hw
    · rw [← Matrix.eval_charpoly]; exact hw
  set ρ0 : NNReal := A.charpoly.roots.toFinset.sup (fun w => ‖w‖₊) with hρ0
  have hρ0lt : ρ0 < 1 := by
    rw [hρ0, Finset.sup_lt_iff (by norm_num)]
    intro w hw
    have hw' : w ∈ spectrum ℂ A := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero] at hw
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


/-- Woodford (2003), p. 670 (restated from the Galí Chapter 6 project): Bound for `Kᵏ` acting on a
bounded vector. -/
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


/-- Woodford (2003), p. 670: Iterating a homogeneous forward system: `d_t = Kᵏ E_t
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


/-- Woodford (2003), p. 670, fn. 1 (Blanchard–Kahn): if the powers of `K` decay
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


/-- Woodford (2003), App. C.1, p. 670 (restated from the Chapter 4 project): the forward series
`s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` of `s_t = K E_t s_{t+1} + w_t`. -/
noncomputable def fwdVec {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (w : ℕ → Fin n → Ω → ℝ) :
    ℕ → Fin n → Ω → ℝ :=
  fun t i ω => ∑' k, rvMul (K ^ k) (fun j => 𝔼.E t (w (t + k) j)) i ω

/-- Woodford (2003), App. C.1, p. 670 (restated from the Chapter 4 project, `fsolves_exists`,
with the solution named): if the powers of `K` decay geometrically, the forward series
`fwdVec K w` is a bounded adapted solution of `s_t = K E_t s_{t+1} + w_t`. -/
theorem fwdVec_spec {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k)
    {w : ℕ → Fin n → Ω → ℝ} {Mw : ℝ} (hw : ∀ t i ω, |w t i ω| ≤ Mw) (haw : VAdapted 𝔼 w) :
    FSolves 𝔼 K w (fwdVec 𝔼 K w) ∧ VAdapted 𝔼 (fwdVec 𝔼 K w) ∧ VBounded (fwdVec 𝔼 K w) := by
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
  change FSolves 𝔼 K w s ∧ VAdapted 𝔼 s ∧ VBounded s
  refine ⟨?_, ?_, ?_⟩
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

/-- Woodford (2003), App. C.1, p. 670 (restated from the Chapter 4 project): the core's
two-variable system `Solves` is the `n = 2` case of `FSolves`. -/
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

omit 𝔼 in
/-- Woodford (2003), Prop. C.1, p. 670 (geometric decay of powers under the Schur–Cohn
condition, proved from the Cayley–Hamilton sequence of the core): there are `C` and
`0 ≤ ρ < 1` with `|(Aᵏ)_{ij}| ≤ C ρᵏ`. -/
theorem pow_geom_bound {A : Matrix (Fin 2) (Fin 2) ℝ} (h : SchurStable (tr2 A) (det2 A)) :
    ∃ C ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ k i j, |(A ^ k) i j| ≤ C * ρ ^ k := by
  obtain ⟨h1, h2⟩ := (schurStable_iff_roots _ _).mp h
  set r := max ‖root₁ (tr2 A) (det2 A)‖ ‖root₂ (tr2 A) (det2 A)‖ with hr
  have hr0 : 0 ≤ r := le_max_of_le_left (norm_nonneg _)
  have hr1 : r < 1 := max_lt h1 h2
  set ρ := (1 + r) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hq0 : 0 ≤ r / ρ := div_nonneg hr0 hρ0.le
  have hq1 : r / ρ < 1 := (div_lt_one hρ0).mpr (by rw [hρ]; linarith)
  have hlim : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * (r / ρ) ^ k) atTop (𝓝 0) := by
    have ha := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
    have hb := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa [add_mul] using ha.add hb
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  have hbound : ∀ k : ℕ, |chSeq (tr2 A) (det2 A) k| ≤ B * ρ ^ k := by
    intro k
    have hc := abs_chSeq_le (tr2 A) (det2 A) k
    have hk : ((k : ℝ) + 1) * (r / ρ) ^ k ≤ B := hB ⟨k, rfl⟩
    have heq : ((k : ℝ) + 1) * r ^ k = ((k : ℝ) + 1) * (r / ρ) ^ k * ρ ^ k := by
      rw [div_pow, mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hρ0.ne')]
    calc |chSeq (tr2 A) (det2 A) k| ≤ ((k : ℝ) + 1) * r ^ k := hc
      _ = ((k : ℝ) + 1) * (r / ρ) ^ k * ρ ^ k := heq
      _ ≤ B * ρ ^ k := mul_le_mul_of_nonneg_right hk (pow_nonneg hρ0.le k)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans ((hbound 0).trans (by simp))
  set M := |A 0 0| + |A 0 1| + |A 1 0| + |A 1 1| with hM
  have hAij : ∀ i j, |A i j| ≤ M := by
    intro i j
    have := abs_nonneg (A 0 0); have := abs_nonneg (A 0 1)
    have := abs_nonneg (A 1 0); have := abs_nonneg (A 1 1)
    fin_cases i <;> fin_cases j <;> simp only [hM] <;> norm_num <;> linarith
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hAij 0 0)
  set C := (1 + M + B * (ρ * M + |det2 A|)) / ρ ^ 2 with hC
  have hnum : 1 + M + B * (ρ * M + |det2 A|) ≥ 1 := by
    have : 0 ≤ B * (ρ * M + |det2 A|) := mul_nonneg hB0 (by positivity)
    linarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  refine ⟨C, ρ, hρ0.le, hρ1, fun k i j => ?_⟩
  rcases k with _ | _ | k
  · have h1 : |((A ^ 0) i j)| ≤ 1 := by
      rw [pow_zero, Matrix.one_apply]; split_ifs <;> simp
    have : 1 ≤ C := by
      rw [hC, le_div_iff₀ hρ2]
      nlinarith
    simpa using h1.trans this
  · have : M ≤ C * ρ := by
      rw [hC, div_mul_eq_mul_div, le_div_iff₀ hρ2]
      have hX : 0 ≤ B * (ρ * M + |det2 A|) := mul_nonneg hB0 (by positivity)
      have e1 : M * ρ ^ 2 ≤ M * ρ := by
        have := mul_le_mul_of_nonneg_left hρ1.le (mul_nonneg hM0 hρ0.le)
        nlinarith
      have e2 : 0 ≤ (1 + B * (ρ * M + |det2 A|)) * ρ := by positivity
      nlinarith
    simpa using (hAij i j).trans this
  · refine (abs_pow_entry_le A k i j).trans ?_
    have e1 := mul_le_mul (hbound (k + 1)) (hAij i j) (abs_nonneg _)
      (mul_nonneg hB0 (pow_nonneg hρ0.le _))
    have e2 := mul_le_mul_of_nonneg_left (hbound k) (abs_nonneg (det2 A))
    have hCk : C * ρ ^ (k + 2) = (1 + M + B * (ρ * M + |det2 A|)) * ρ ^ k := by
      rw [hC, pow_add]
      field_simp
    rw [hCk]
    have hρk := pow_nonneg hρ0.le k
    have : B * ρ ^ (k + 1) * M + |det2 A| * (B * ρ ^ k) =
        B * (ρ * M + |det2 A|) * ρ ^ k := by ring
    nlinarith

/-- Woodford (2003), App. C.1, Prop. C.1, p. 670 (restated from the Chapter 4 project,
`fwd_existsUnique`): under the Schur–Cohn condition `x_t = K E_t x_{t+1} + w_t` has exactly
one bounded adapted solution for bounded adapted forcing, the forward series `fwdVec K w`. -/
theorem fwd_existsUnique {K : Matrix (Fin 2) (Fin 2) ℝ} (hK : SchurStable (tr2 K) (det2 K))
    {w : ℕ → Fin 2 → Ω → ℝ} (hw : BoundedVec w) (haw : 𝔼.AdaptedVec w) :
    ∃! x, 𝔼.Solves K w x ∧ 𝔼.AdaptedVec x ∧ BoundedVec x := by
  obtain ⟨Cb, ρ, hρ0, hρ1, hb⟩ := pow_geom_bound hK
  obtain ⟨Mw, hMw⟩ := hw
  obtain ⟨hs, has, hbs⟩ := fwdVec_spec 𝔼 hρ0 hρ1 hb hMw haw
  refine ⟨fwdVec 𝔼 K w, ⟨(solves_iff_fsolves 𝔼 K w _).mpr hs, has, hbs⟩, fun y hy => ?_⟩
  exact 𝔼.system_unique hK hy.1 ((solves_iff_fsolves 𝔼 K w _).mpr hs) hy.2.1 has hy.2.2 hbs


omit 𝔼 in
/-- Woodford (2003), p. 335 (restated from the Woodford Ch. 4 project, `abs_rec_le`): a stable
scalar recursion `x_{t+1} = λ x_t + u_t` with `|λ| < 1` and bounded `u` stays bounded. -/
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


/-! ### The unit-root forward iteration of the bond-pricing relation -/

/-- Woodford (2003), p. 325 (the bond-pricing relation `î_t = λ̂_t + E_t[π_{t+1} − λ̂_{t+1}]`) and
eq. (3.21), p. 365 (the same relation (3.10) of the investment model): iterating it, conditioned
on any date `s ≤ t`, `E_s λ̂_t = E_s λ̂_{t+k} + ∑_{j<k} E_s(î_{t+j} − π_{t+j+1})`. -/
theorem unitRoot_iterate {i infl lam : ℕ → Ω → ℝ}
    (h : ∀ t, i t = lam t + 𝔼.E t (infl (t + 1) - lam (t + 1))) {s t : ℕ} (hst : s ≤ t)
    (k : ℕ) : 𝔼.E s (lam t) = 𝔼.E s (lam (t + k)) +
      ∑ j ∈ Finset.range k, 𝔼.E s (i (t + j) - infl (t + j + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk := congrArg (𝔼.E s) (h (t + k))
    rw [map_add, 𝔼.tower (le_trans hst (Nat.le_add_right t k))] at hk
    rw [ih, Finset.sum_range_succ, map_sub, hk, map_sub, ← add_assoc t k 1]
    abel

/-- Woodford (2003), p. 325 and eq. (3.21), p. 365 (**the forward solution for `λ̂`**, made
precise): along a solution of the bond-pricing relation, the partial sums of
`∑_j E_s(î_{t+j} − π_{t+j+1})` converge to `E_s λ̂_t − λ̂_∞` if and only if
`E_s λ̂_{t+k} → λ̂_∞`. -/
theorem unitRoot_forward_iff {i infl lam : ℕ → Ω → ℝ}
    (h : ∀ t, i t = lam t + 𝔼.E t (infl (t + 1) - lam (t + 1))) {s t : ℕ} (hst : s ≤ t) (L : ℝ)
    (ω : Ω) :
    Tendsto (fun k => ∑ j ∈ Finset.range k, 𝔼.E s (i (t + j) - infl (t + j + 1)) ω) atTop
        (𝓝 (𝔼.E s (lam t) ω - L)) ↔
      Tendsto (fun k => 𝔼.E s (lam (t + k)) ω) atTop (𝓝 L) := by
  have hS : ∀ k, ∑ j ∈ Finset.range k, 𝔼.E s (i (t + j) - infl (t + j + 1)) ω =
      𝔼.E s (lam t) ω - 𝔼.E s (lam (t + k)) ω := by
    intro k
    have := congrFun (unitRoot_iterate 𝔼 h hst k) ω
    simp only [Pi.add_apply, Finset.sum_apply] at this
    linarith
  simp_rw [hS]
  constructor
  · intro hc
    have := (tendsto_const_nhds (x := 𝔼.E s (lam t) ω)).sub hc
    simpa using this
  · intro hc
    exact tendsto_const_nhds.sub hc

/-! ### Second-order equations with one stable root (pp. 365, 689)

Used for (3.20)–(3.22) (`ISBlock`) and (D.3)–(D.4) (`Prop51`). -/

/-- Woodford (2003), p. 365: the forward part of the solution of (3.20),
`w_t = −(a₀μ̃₂)⁻¹ ∑_j μ̃₂^{−j} E_t f_{t+j}`. -/
noncomputable def wSol (a0 μ2 : ℝ) (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries μ2⁻¹ (fun t => -(a0 * μ2)⁻¹ • f t)

/-- Woodford (2003), p. 365: `w_t = ∑_j μ̃₂^{−j} (−(a₀μ̃₂)⁻¹) E_t f_{t+j}`, pointwise. -/
theorem wSol_apply (a0 μ2 : ℝ) (f : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    wSol 𝔼 a0 μ2 f t ω = ∑' j, μ2⁻¹ ^ j * (-(a0 * μ2)⁻¹ * 𝔼.E t (f (t + j)) ω) := by
  simp only [wSol, ExpectationSystem.forwardSeries, map_smul, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), p. 365, "there is a unique bounded solution for `K̂_{t+1}` as a linear
function of `K̂_t` and the expectations `E_t f_{t+j}`": for `A(L) = a₀(1 − μ₁L)(1 − μ₂L)` with
`|μ₂| > 1`, a bounded predetermined process `x` solves
`a₀ E_t x_{t+2} − a₁ x_{t+1} + a₂ x_t = f_t` (bounded adapted `f`) if and only if
`x_{t+1} = μ₁ x_t + w_t` at every date. -/
theorem secondOrder_forward_iff {a0 a1 a2 μ1 μ2 : ℝ} (ha0 : a0 ≠ 0) (h1 : a1 = a0 * (μ1 + μ2))
    (h2 : a2 = a0 * μ1 * μ2) (hμ2 : 1 < |μ2|) {x f : ℕ → Ω → ℝ} {M : ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) (hx : (∀ t, 𝔼.E t (x (t + 1)) = x (t + 1)))
    (hxb : BoundedProc x) :
    (∀ t, a0 • 𝔼.E t (x (t + 2)) - a1 • x (t + 1) + a2 • x t = f t) ↔
      ∀ t, x (t + 1) = μ1 • x t + wSol 𝔼 a0 μ2 f t := by
  have hμ0 : μ2 ≠ 0 := by
    intro h; rw [h, abs_zero] at hμ2; linarith
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hμ2
  set u : ℕ → Ω → ℝ := fun t => -(a0 * μ2)⁻¹ • f t with hu_def
  have hu : ∀ t ω, |u t ω| ≤ |(a0 * μ2)⁻¹| * M := fun t ω => by
    simp only [hu_def, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hf t ω) (abs_nonneg _)
  have hua : 𝔼.Adapted u := fun t => by simp only [hu_def, map_smul, hfa t]
  constructor
  · intro h
    set d : ℕ → Ω → ℝ := fun t => x (t + 1) - μ1 • x t with hd_def
    have hd : ForwardSolution.Solves 𝔼 μ2⁻¹ u d := by
      intro t
      have he := h t
      funext ω
      have h3 := congrFun he ω
      have hEd : 𝔼.E t (x (t + 1 + 1) - μ1 • x (t + 1)) ω =
          𝔼.E t (x (t + 2)) ω - μ1 * x (t + 1) ω := by
        simp only [map_sub, map_smul, hx t, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hd_def, hu_def] at h3 ⊢
      rw [hEd]
      rw [h1, h2] at h3
      linear_combination (norm := (field_simp; ring)) (-(a0 * μ2)⁻¹) * h3
    obtain ⟨Mx, hMx⟩ := hxb
    have hdb : BoundedProc d := ⟨Mx + |μ1| * Mx, fun t ω => by
      simp only [hd_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      calc |x (t + 1) ω - μ1 * x t ω| ≤ |x (t + 1) ω| + |μ1 * x t ω| := abs_sub _ _
        _ ≤ Mx + |μ1| * Mx := by
          rw [abs_mul]
          exact add_le_add (hMx _ _) (mul_le_mul_of_nonneg_left (hMx _ _) (abs_nonneg _))⟩
    have heq := ForwardSolution.eq_forwardSeries_abs 𝔼 hq hu hua hd hdb
    intro t
    have := congrFun heq t
    rw [show wSol 𝔼 a0 μ2 f t = 𝔼.forwardSeries μ2⁻¹ u t from rfl, ← this]
    simp only [hd_def]
    abel
  · intro h t
    have hw := ForwardSolution.forwardSeries_solves_abs 𝔼 hq hu hua t
    have hE : 𝔼.E t (x (t + 2)) = μ1 • x (t + 1) + 𝔼.E t (wSol 𝔼 a0 μ2 f (t + 1)) := by
      rw [h (t + 1), map_add, map_smul, hx t]
    rw [hE]
    funext ω
    have h4 := congrFun hw ω
    have h5 := congrFun (h t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hu_def] at h4 h5 ⊢
    rw [show 𝔼.forwardSeries μ2⁻¹ u = wSol 𝔼 a0 μ2 f from rfl] at h4
    rw [h1, h2]
    linear_combination (norm := (field_simp; ring)) (-a0 * μ2) * h4 + (-a0 * μ2) * h5

/-- Woodford (2003), p. 365: the capital path generated from an initial stock `x₀` by
`x_{t+1} = μ₁ x_t + w_t`. -/
def path (x0 : Ω → ℝ) (μ1 : ℝ) (w : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => x0
  | t + 1 => μ1 • path x0 μ1 w t + w t

omit 𝔼 in
/-- Woodford (2003), p. 365: the path solves its recursion. -/
theorem path_succ (x0 : Ω → ℝ) (μ1 : ℝ) (w : ℕ → Ω → ℝ) (t : ℕ) :
    path x0 μ1 w (t + 1) = μ1 • path x0 μ1 w t + w t := rfl

/-- Woodford (2003), p. 365: the path is known at each date if `x₀` is known at date 0 and `w`
is adapted, and hence `x_{t+1}` is predetermined. -/
theorem path_adapted {x0 : Ω → ℝ} {μ1 : ℝ} {w : ℕ → Ω → ℝ} (hx0 : 𝔼.E 0 x0 = x0)
    (hw : 𝔼.Adapted w) : 𝔼.Adapted (path x0 μ1 w) ∧
      ∀ t, 𝔼.E t (path x0 μ1 w (t + 1)) = path x0 μ1 w (t + 1) := by
  have hA : 𝔼.Adapted (path x0 μ1 w) := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih =>
      rw [path_succ, map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hw t)]
  refine ⟨hA, fun t => ?_⟩
  rw [path_succ, map_add, map_smul, hA t, hw t]

/-- Woodford (2003), p. 365: the path is bounded when `|μ₁| < 1` and `w`, `x₀` are bounded. -/
theorem path_bounded {x0 : Ω → ℝ} {μ1 B0 Mw : ℝ} {w : ℕ → Ω → ℝ} (hμ1 : |μ1| < 1)
    (hx0 : ∀ ω, |x0 ω| ≤ B0) (hw : ∀ t ω, |w t ω| ≤ Mw) : BoundedProc (path x0 μ1 w) := by
  have hpos : 0 < 1 - |μ1| := by linarith
  set B : ℝ := max B0 (Mw / (1 - |μ1|)) with hB
  have hMw : Mw ≤ (1 - |μ1|) * B := by
    have : Mw / (1 - |μ1|) ≤ B := le_max_right _ _
    rw [div_le_iff₀ hpos] at this
    linarith
  refine ⟨B, fun t ω => ?_⟩
  induction t with
  | zero => exact (hx0 ω).trans (le_max_left _ _)
  | succ t ih =>
    simp only [path_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |μ1 * path x0 μ1 w t ω + w t ω| ≤ |μ1| * |path x0 μ1 w t ω| + |w t ω| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |μ1| * B + Mw := add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg _)) (hw t ω)
      _ ≤ B := by linarith

/-- Woodford (2003), p. 365 ("there is a unique bounded solution for `K̂_{t+1}` as a linear
function of `K̂_t`, the expectations `E_t λ̂_{t+j}` and `E_t z_{t+j}`"): for
`A(L) = a₀(1 − μ₁L)(1 − μ₂L)` with `|μ₁| < 1 < |μ₂|`, bounded adapted forcing `f` and a bounded
initial stock `x₀` known at date 0, there is exactly one bounded predetermined solution of
`a₀ E_t x_{t+2} − a₁ x_{t+1} + a₂ x_t = f_t` starting from `x₀`: the path
`x_{t+1} = μ₁ x_t + w_t`. -/
theorem secondOrder_forward_existsUnique {a0 a1 a2 μ1 μ2 : ℝ} (ha0 : a0 ≠ 0)
    (h1 : a1 = a0 * (μ1 + μ2)) (h2 : a2 = a0 * μ1 * μ2) (hμ1 : |μ1| < 1) (hμ2 : 1 < |μ2|)
    {f : ℕ → Ω → ℝ} {M B0 : ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (hfa : 𝔼.Adapted f) {x0 : Ω → ℝ} (hx0 : 𝔼.E 0 x0 = x0)
    (hx0b : ∀ ω, |x0 ω| ≤ B0) :
    ∃! x : ℕ → Ω → ℝ, x 0 = x0 ∧ (∀ t, 𝔼.E t (x (t + 1)) = x (t + 1)) ∧ BoundedProc x ∧
      ∀ t, a0 • 𝔼.E t (x (t + 2)) - a1 • x (t + 1) + a2 • x t = f t := by
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hμ2
  have hu : ∀ t ω, |(fun t => -(a0 * μ2)⁻¹ • f t) t ω| ≤ |(a0 * μ2)⁻¹| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hf t ω) (abs_nonneg _)
  have hwb := ForwardSolution.forwardSeries_bounded_abs 𝔼 hq hu
  have hwa := ForwardSolution.forwardSeries_adapted_abs 𝔼 hq hu
  obtain ⟨Mw, hMw⟩ := hwb
  set w := wSol 𝔼 a0 μ2 f with hw
  have hpa := path_adapted 𝔼 (μ1 := μ1) hx0 hwa
  have hpb := path_bounded (μ1 := μ1) hμ1 hx0b hMw
  refine ⟨path x0 μ1 w, ⟨rfl, hpa.2, hpb, ?_⟩, ?_⟩
  · exact (secondOrder_forward_iff 𝔼 ha0 h1 h2 hμ2 hf hfa hpa.2 hpb).mpr
      (fun t => path_succ x0 μ1 w t)
  · rintro y ⟨hy0, hyp, hyb, hy⟩
    have hrec := (secondOrder_forward_iff 𝔼 ha0 h1 h2 hμ2 hf hfa hyp hyb).mp hy
    funext t
    induction t with
    | zero => exact hy0
    | succ t ih => rw [hrec t, ih]; rfl


/-! ### Purely forward-looking systems `E_t x_{t+1} = A x_t + w_t` -/

open scoped Matrix

variable {n : ℕ}

/-- Woodford (2003), eq. (3.36), p. 375: `x` solves the purely forward-looking system
`E_t x_{t+1} = A x_t + w_t`. -/
def ExpSys (A : Matrix (Fin n) (Fin n) ℝ) (w x : ℕ → Fin n → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (x (t + 1) i) = rvMul A (x t) i + w t i

/-- Woodford (2003), p. 376: "all four eigenvalues outside the unit circle" — every complex
root of `det(μ I − A) = 0` has `|μ| > 1`. -/
def EigenOut (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ μ : ℂ, (Matrix.scalar (Fin n) μ - A.map Complex.ofReal).det = 0 → 1 < ‖μ‖

/-- Woodford (2003), p. 376: determinacy of `E_t x_{t+1} = A x_t + w_t` — for every bounded
adapted forcing there is exactly one bounded adapted solution (no predetermined variables). -/
def ExpSysDeterminate (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ w : ℕ → Fin n → Ω → ℝ, VBounded w → VAdapted 𝔼 w →
    ∃! x, ExpSys 𝔼 A w x ∧ VAdapted 𝔼 x ∧ VBounded x

omit 𝔼 in
/-- Woodford (2003), p. 376 (tool): `μ` is an eigenvalue iff it has an eigenvector. -/
theorem eigen_iff (M : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    (Matrix.scalar (Fin n) μ - M).det = 0 ↔ ∃ v ≠ 0, M *ᵥ v = μ • v := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  have hs : Matrix.scalar (Fin n) μ *ᵥ v = μ • v := by
    funext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [Matrix.sub_mulVec, hs, sub_eq_zero, eq_comm]

omit 𝔼 in
/-- Woodford (2003), p. 376 (tool): complexifying commutes with `*ᵥ`. -/
theorem ofReal_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    A.map Complex.ofReal *ᵥ (fun i => (v i : ℂ)) = fun i => ((A *ᵥ v) i : ℂ) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

omit 𝔼 in
/-- Woodford (2003), p. 376: if no eigenvalue lies in the closed unit disc, `A` is invertible
(`0` is not an eigenvalue). -/
theorem det_ne_zero_of_eigenOut {A : Matrix (Fin n) (Fin n) ℝ} (hA : EigenOut A) : A.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have h := hA 0 ((eigen_iff _ 0).mpr ⟨fun i => (v i : ℂ), fun h => hv0 (funext fun i => by
    have := congrFun h i; simpa using this), by rw [ofReal_mulVec, hv]; funext i; simp⟩)
  rw [norm_zero] at h
  linarith

omit 𝔼 in
/-- Woodford (2003), p. 376: if every eigenvalue of `A` lies outside the closed unit disc, every
eigenvalue of `A⁻¹` lies inside the open unit disc. -/
theorem eigen_inv {A : Matrix (Fin n) (Fin n) ℝ} (hA : EigenOut A) :
    ∀ μ : ℂ, (Matrix.scalar (Fin n) μ - (A⁻¹).map Complex.ofReal).det = 0 → ‖μ‖ < 1 := by
  intro μ hμ
  obtain ⟨v, hv0, hv⟩ := (eigen_iff _ μ).mp hμ
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr (det_ne_zero_of_eigenOut hA)
  have hAK : A.map Complex.ofReal * (A⁻¹).map Complex.ofReal = 1 := by
    ext i j
    have h := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i) j
    rw [Matrix.mul_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.map_apply, ← Complex.ofReal_mul, ← Complex.ofReal_sum, h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hv' : v = μ • (A.map Complex.ofReal *ᵥ v) := by
    calc v = (A.map Complex.ofReal * (A⁻¹).map Complex.ofReal) *ᵥ v := by
          rw [hAK, Matrix.one_mulVec]
      _ = A.map Complex.ofReal *ᵥ ((A⁻¹).map Complex.ofReal *ᵥ v) :=
          (Matrix.mulVec_mulVec _ _ _).symm
      _ = μ • (A.map Complex.ofReal *ᵥ v) := by rw [hv, Matrix.mulVec_smul]
  have hμ0 : μ ≠ 0 := by
    intro h; apply hv0; rw [hv', h, zero_smul]
  have hev : A.map Complex.ofReal *ᵥ v = μ⁻¹ • v := by
    conv_rhs => rw [hv']
    rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  have h := hA μ⁻¹ ((eigen_iff _ _).mpr ⟨v, hv0, hev⟩)
  rw [norm_inv] at h
  exact (one_lt_inv₀ (norm_pos_iff.mpr hμ0)).mp h

/-- Woodford (2003), p. 376: for invertible `A`, `E_t x_{t+1} = A x_t + w_t` is the forward
system `x_t = A⁻¹ E_t x_{t+1} − A⁻¹ w_t`. -/
theorem expSys_iff {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.det ≠ 0)
    {w x : ℕ → Fin n → Ω → ℝ} :
    ExpSys 𝔼 A w x ↔ FSolves 𝔼 A⁻¹ (fun t => rvMul (-A⁻¹) (w t)) x := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hKA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hu
  have hAK : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  constructor
  · intro h t
    have hv : (fun j => 𝔼.E t (x (t + 1) j)) = rvMul A (x t) + w t := by
      funext j; rw [h t j]; rfl
    rw [hv, rvMul_add, rvMul_rvMul, hKA, rvMul_one]
    simp only [rvMul_neg]
    abel
  · intro h t i
    have hv : (fun j => 𝔼.E t (x (t + 1) j)) =
        rvMul A (rvMul A⁻¹ (fun j => 𝔼.E t (x (t + 1) j))) := by
      rw [rvMul_rvMul, hAK, rvMul_one]
    have hx : rvMul A⁻¹ (fun j => 𝔼.E t (x (t + 1) j)) = x t + rvMul A⁻¹ (w t) := by
      rw [h t]; simp only [rvMul_neg]; abel
    have := congrFun hv i
    rw [hx, rvMul_add, rvMul_rvMul, hAK, rvMul_one] at this
    exact this

/-- Woodford (2003), p. 376 ("When this is true, the system can be solved forward in the usual way
to obtain a unique bounded solution"): if every eigenvalue of `A` lies outside the unit circle,
then for bounded adapted `w` the forward series of `x_t = A⁻¹E_t x_{t+1} − A⁻¹w_t` is a bounded
adapted solution of `E_t x_{t+1} = A x_t + w_t`, and it is the only one. -/
theorem existsUnique_of_eigenOut {A : Matrix (Fin n) (Fin n) ℝ} (hA : EigenOut A)
    {w : ℕ → Fin n → Ω → ℝ} {Mw : ℝ} (hw : ∀ t i ω, |w t i ω| ≤ Mw) (hwa : VAdapted 𝔼 w) :
    ExpSys 𝔼 A w (fwdVec 𝔼 A⁻¹ (fun t => rvMul (-A⁻¹) (w t))) ∧
      VAdapted 𝔼 (fwdVec 𝔼 A⁻¹ (fun t => rvMul (-A⁻¹) (w t))) ∧
      VBounded (fwdVec 𝔼 A⁻¹ (fun t => rvMul (-A⁻¹) (w t))) ∧
      ∀ x, ExpSys 𝔼 A w x → VAdapted 𝔼 x → VBounded x →
        x = fwdVec 𝔼 A⁻¹ (fun t => rvMul (-A⁻¹) (w t)) := by
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hK⟩ := pow_entry_bound (A⁻¹) (eigen_inv hA)
  have hw' : ∀ t i ω, |w t i ω| ≤ max Mw 0 := fun t i ω => (hw t i ω).trans (le_max_left _ _)
  have hfb : ∀ t i ω, |rvMul (-A⁻¹) (w t) i ω| ≤ (∑ i, ∑ j, |(-A⁻¹) i j|) * max Mw 0 :=
    fun t i ω => abs_rvMul_le _ (le_max_right _ _) (fun j ω => hw' t j ω) i ω
  have hfa : VAdapted 𝔼 (fun t => rvMul (-A⁻¹) (w t)) := fun t i => by
    rw [E_rvMul 𝔼]; simp only [hwa t]
  obtain ⟨hs, ha, hb⟩ := fwdVec_spec 𝔼 hρ0.le hρ1 hK hfb hfa
  refine ⟨(expSys_iff 𝔼 (det_ne_zero_of_eigenOut hA)).mpr hs, ha, hb, fun x hx hxa hxb => ?_⟩
  exact fsolves_unique 𝔼 hρ0.le hρ1 hK ((expSys_iff 𝔼 (det_ne_zero_of_eigenOut hA)).mp hx) hs
    hxa ha hxb hb

omit 𝔼 in
/-- Woodford (2003), p. 376: an eigenvalue `μ` of `A` with `|μ| ≤ 1` gives a nonzero bounded
deterministic solution `m_{t+1} = A m_t` (`m_t = Re(c μᵗ v)` for an eigenvector `v`). -/
theorem exists_mode {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℂ} (hμ : ‖μ‖ ≤ 1)
    (hdet : (Matrix.scalar (Fin n) μ - A.map Complex.ofReal).det = 0) :
    ∃ m : ℕ → Fin n → ℝ, (∀ t, m (t + 1) = A *ᵥ m t) ∧ (∃ M, ∀ t i, |m t i| ≤ M) ∧ m 0 ≠ 0 := by
  obtain ⟨V, hV0, hV⟩ := (eigen_iff _ μ).mp hdet
  obtain ⟨j0, hj0⟩ : ∃ j, V j ≠ 0 := by
    by_contra h; push Not at h; exact hV0 (funext h)
  set c : ℂ := (starRingEnd ℂ) (V j0) with hc
  have key : ∀ (a : ℂ) (i : Fin n),
      (A *ᵥ fun j => (a * V j).re) i = (a * ((A.map Complex.ofReal) *ᵥ V) i).re := by
    intro a i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show a * (↑(A i j) * V j) = ↑(A i j) * (a * V j) by ring, Complex.re_ofReal_mul]
  refine ⟨fun t i => (c * μ ^ t * V i).re, fun t => ?_, ?_, ?_⟩
  · funext i
    rw [key, hV, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · refine ⟨‖c‖ * ∑ j, ‖V j‖, fun t j => ?_⟩
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖μ‖ ^ t ≤ 1 := pow_le_one₀ (norm_nonneg _) hμ
    have h2 : ‖V j‖ ≤ ∑ j, ‖V j‖ :=
      Finset.single_le_sum (f := fun j => ‖V j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    calc ‖c‖ * ‖μ‖ ^ t * ‖V j‖ ≤ ‖c‖ * 1 * ∑ j, ‖V j‖ := by gcongr
      _ = _ := by ring
  · intro h
    have h0 := congrFun h j0
    simp only [pow_zero, mul_one, Pi.zero_apply, hc] at h0
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] at h0
    exact hj0 (norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0))

/-- Woodford (2003), p. 376: with an eigenvalue in the closed unit disc, any bounded adapted
solution of `E_t x_{t+1} = A x_t + w_t` has a different bounded adapted companion (add a nonzero
bounded mode): bounded solutions are never unique. -/
theorem not_unique_of_mode [Nonempty Ω] {A : Matrix (Fin n) (Fin n) ℝ} {m : ℕ → Fin n → ℝ}
    (hm : ∀ t, m (t + 1) = A *ᵥ m t) (hmb : ∃ M, ∀ t i, |m t i| ≤ M) (hm0 : m 0 ≠ 0)
    {w x : ℕ → Fin n → Ω → ℝ} (hx : ExpSys 𝔼 A w x) (hxa : VAdapted 𝔼 x) (hxb : VBounded x) :
    ExpSys 𝔼 A w (fun t i => x t i + fun _ => m t i) ∧
      VAdapted 𝔼 (fun t i => x t i + fun _ => m t i) ∧
      VBounded (fun t i => x t i + fun _ => m t i) ∧ (fun t i => x t i + fun _ => m t i) ≠ x := by
  refine ⟨fun t i => ?_, fun t i => ?_, ?_, ?_⟩
  · rw [map_add, 𝔼.const, hx t i, hm t]
    funext ω
    simp only [Pi.add_apply, rvMul_apply, Matrix.mulVec, dotProduct, mul_add,
      Finset.sum_add_distrib]
    ring
  · rw [map_add, 𝔼.const, hxa t i]
  · obtain ⟨M1, hM1⟩ := hxb
    obtain ⟨M2, hM2⟩ := hmb
    exact ⟨M1 + M2, fun t i ω => (abs_add_le _ _).trans (add_le_add (hM1 t i ω) (hM2 t i))⟩
  · intro h
    apply hm0
    funext i
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrFun h 0) i) ω
    simp only [Pi.add_apply, add_eq_left] at this
    exact this

/-- **Woodford (2003), p. 376** (the determinacy criterion for (3.36), proved for any purely
forward-looking `n`-dimensional system): `E_t x_{t+1} = A x_t + w_t` has a unique bounded
solution for every bounded adapted forcing if and only if all eigenvalues of `A` lie outside
the unit circle. -/
theorem expSysDeterminate_iff [Nonempty Ω] (A : Matrix (Fin n) (Fin n) ℝ) :
    ExpSysDeterminate 𝔼 A ↔ EigenOut A := by
  constructor
  · intro hD μ hμ
    by_contra hle
    push Not at hle
    obtain ⟨m, hm, hmb, hm0⟩ := exists_mode hle hμ
    obtain ⟨x, ⟨hx, hxa, hxb⟩, huniq⟩ := hD 0 ⟨0, fun _ _ _ => by simp⟩ (fun _ _ => by simp)
    obtain ⟨h1, h2, h3, h4⟩ := not_unique_of_mode 𝔼 hm hmb hm0 hx hxa hxb
    exact h4 (huniq _ ⟨h1, h2, h3⟩)
  · intro hA w ⟨Mw, hw⟩ hwa
    obtain ⟨h1, h2, h3, h4⟩ := existsUnique_of_eigenOut 𝔼 hA hw hwa
    exact ⟨_, ⟨h1, h2, h3⟩, fun x ⟨hx, hxa, hxb⟩ => h4 x hx hxa hxb⟩

end Woodford.PolicyResponseDynamics.ForwardSystems
