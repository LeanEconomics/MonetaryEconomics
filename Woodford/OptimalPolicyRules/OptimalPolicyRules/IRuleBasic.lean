/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.ExpectationTools
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# An optimal interest-rate rule for the basic neo-Wicksellian model

Woodford (2003), *Interest and Prices*, Chapter 8, §3.1, pp. 582–588, and Appendix G.4,
pp. 721–722 (proof of Proposition 8.5).

The model is the aggregate-supply relation (2.1) `π_t = κ x_t + β E_t π_{t+1} + u_t` and the IS
relation (3.1) `x_t = E_t x_{t+1} − σ (i_t − E_t π_{t+1} − rⁿ_t)`; the loss (3.2) is
`π_t² + λ_x (x_t − x*)² + λ_i (i_t − i*)²`. Everything is stated for an arbitrary
`ExpectationSystem` (perfect foresight and genuine uncertainty alike).

## Main results

* **The first-order conditions and the rule.** `FOC3`, `FOC4`, `FOC5` are (3.3)–(3.5).
  `rule_iff_foc3`: with the multipliers read off (3.4)–(3.5) (`mult1`, `mult2`, and the
  pre-sample ones `mult1h`, `mult2h` inferred from the history `x_{−1}, i_{−1}, i_{−2}`), the
  instrument rule (3.7) holds at a date iff (3.3) does — the elimination of the multipliers, with
  the coefficients (3.8)–(3.9) (`rho1`, `rho2`, `phiPi`, `phiX`; signs in `coef_signs`).
* **Optimality (timeless perspective, robust).** `lagrangian_identity`: for a plan satisfying the
  first-order conditions with bounded adapted multipliers and any other bounded feasible plan
  with the same initial values (3.6), the loss difference is exactly
  `∑ βᵗ E₀[dπ² + λ_x dx² + λ_i di²]` (pull-out property assumed). Hence `plan_optimal`
  (Lagrangian sufficiency), `rule_eqm_optimal` (every bounded equilibrium under (3.7) minimises
  the expected discounted loss among all bounded feasible plans with the same `π_{t₀}, x_{t₀}` —
  the self-consistent commitments (3.6) — whatever the bounded disturbances; `OptimalGiven`), and
  `unique_optimum_pf` (uniqueness of the optimum under perfect foresight). Under any faithful
  expectation system with the pull-out property (`ExpectationTools.Faithful`; perfect
  foresight is faithful, `ExpectationTools.perfectForesight_faithful`) the optimum is unique
  (`unique_optimum`), and every plan optimal
  given the rule equilibrium's initial values is that equilibrium (`rule_eqm_unique_optimum`).
* **The characteristic polynomial (G.10)–(G.13).** `det_Abar`: `det(Ā − µĪ) = −p(µ)βµ` for the
  `6 × 6` matrices of (G.10); `palin_inv`, `palin_inv_eq_zero_iff`: the reciprocal symmetry
  `p((βµ)⁻¹) = p(µ)/(β²µ⁴)` behind the pairing `µ ↔ (βµ)⁻¹`; `palin_split`: (G.13).
* **Root counting, the precise form of the argument for Prop. 8.5 (survey E21).** For every
  `β`-palindromic quartic: at most two roots (with multiplicity) lie in the open unit disc
  (`palin_insideCard_le`, the book's argument), and exactly two do **iff** no root lies in the
  closed annulus `1 ≤ |µ| ≤ β⁻¹` (`palin_insideCard_eq_two_iff`). For the model's `p` no root ever
  lies in the annulus (`pG_ne_zero_of_annulus`, via `p(µ) = µ²Q(µ + (βµ)⁻¹ − (1+β)/β)` with
  `Q(s) = s² − T_Q s + K_Q`, `T_Q, K_Q > 0`), so exactly two roots lie inside
  (`pG_insideCard_eq_two`), and `det(Ā − µĪ)` has exactly `n_Z = 3` roots inside
  (`charPoly_insideCard_eq_three`) — for every admissible parameter vector.
* **Determinacy (Prop. 8.5).** `rule_determinate`: for every bounded adapted `(rⁿ, u)` and every
  history there is exactly one bounded adapted equilibrium under (3.7)–(3.9). Proof: equilibria
  correspond one-to-one (`sys_of_eqm`, `eqm_of_sys`, `eqm_roundtrip`) to bounded solutions of the
  second-order multiplier system `P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t` with `Φ_{−1}` fixed by
  the history, whose characteristic polynomial is `β²p(µ)` (`det_Mphi`). The stable real factor
  `µ² − Tµ + D` of `p` (`exists_real_split`) yields the real solvent
  `X = (A₁ − TP)⁻¹(A₂ − DP)` (`solvent_eq`), and the second-order Blanchard–Kahn theorem
  `sys2_existsUnique` (proved here: stable block backward, unstable block forward) gives existence
  and uniqueness. `prop_8_5` is the book's statement; its hypothesis is not needed and in fact
  always holds (`bounded_optimum_exists`).
* **Numbers, p. 586** (`p586_numbers`): with Table 6.1 (`β = .99`, `σ = 1/.16`, `κ = .024`) and
  `λ_i = .236`, `λ_x = κ/θ`, `θ = 7.88`: `ρ₁ ∈ (1.15, 1.152)`, `ρ₂ ∈ (1.010, 1.0102)`,
  `φ_π ∈ (.635, .636)`, `φ_x ∈ (.322, .323)` (printed `.33`, `p586_phiX_not_033`). The Table 6.1
  weight `λ_i = .077` would give `φ_π ≈ 1.95`, not `.64` (`p586_phiPi_table_value`).
* **Footnote 35.** `fn35_roots_lt_gt`, `fn35_one_root_gt_one`: if `ρ₁ > 1`, the polynomial
  `z² − (ρ₁+ρ₂)z + ρ₂` has two real roots `λ₁ < 1 < λ₂` and exactly one root above `1`, whatever
  the sign of `ρ₂`; `fn35_roots`: with `ρ₂ > 0` also `λ₁ > 0` (`lam1`, `lam2`, `lam_factor`,
  `lam_model`, used for (3.10)).

The `n`-dimensional forward-system tools (`pow_entry_bound`, `rvMul`, `FSolves`,
`fsolves_unique`, `fsolves_exists`), `inv2` and `schurStable_of_factor` are restated from the
Woodford Chapter 4 project (`BlanchardKahn`, `SchurCohn`), which restated them from the Galí
Chapter 6 project.
-/

namespace Woodford.OptimalPolicyRules.IRuleBasic

open Filter Topology
open scoped Matrix ComplexConjugate
open ExpectationTools (Faithful)

/-! ### Tools restated from the Woodford Chapter 4 project -/

/-- Woodford, p. 670 (restated from the Chapter 4 project), fn. 1 (Blanchard–Kahn, the tool): if
every complex eigenvalue of a real square matrix `K` lies in the open unit disc, the entries of
`Kᵏ` decay geometrically (Gelfand's spectral radius formula). -/
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
      have h1 : 1 ≤ Cb := by
        have : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
          Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
        linarith
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

/-- Woodford, p. 670 (restated from the Chapter 4 project): a matrix acting on a vector of random
variables, `(M a)_i = ∑_j M_{ij} a_j`. -/
def rvMul {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    Fin n → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Woodford, p. 670 (restated from the Chapter 4 project): the action is compatible with matrix
multiplication. -/
theorem rvMul_rvMul {Ω : Type*} {n m l : ℕ} (M : Matrix (Fin n) (Fin m) ℝ)
    (N : Matrix (Fin m) (Fin l) ℝ) (a : Fin l → Ω → ℝ) :
    rvMul M (rvMul N a) = rvMul (M * N) a := by
  funext i
  simp only [rvMul, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Woodford, p. 670 (restated from the Chapter 4 project): additivity of the action. -/
theorem rvMul_add {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a + b) = rvMul M a + rvMul M b := by
  funext i
  simp only [rvMul, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Woodford, p. 670 (restated from the Chapter 4 project): the action respects subtraction. -/
theorem rvMul_sub {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a - b) = rvMul M a - rvMul M b := by
  funext i
  simp only [rvMul, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Woodford, p. 670 (restated from the Chapter 4 project): the identity matrix acts trivially. -/
theorem rvMul_one {Ω : Type*} {n : ℕ} (a : Fin n → Ω → ℝ) : rvMul 1 a = a := by
  funext i
  simp [rvMul, Matrix.one_apply]

/-- Woodford, p. 670 (restated from the Chapter 4 project): the action of a sum of matrices. -/
theorem add_rvMul {Ω : Type*} {n m : ℕ} (M N : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    rvMul (M + N) a = rvMul M a + rvMul N a := by
  funext i
  simp only [rvMul, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

/-- Woodford, p. 670: the action of a difference of matrices. -/
theorem sub_rvMul {Ω : Type*} {n m : ℕ} (M N : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    rvMul (M - N) a = rvMul M a - rvMul N a := by
  funext i
  simp only [rvMul, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.sub_apply]

/-- Woodford, p. 670: the action of a negated matrix. -/
theorem neg_rvMul {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    rvMul (-M) a = -rvMul M a := by
  funext i
  simp only [rvMul, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib, Pi.neg_apply]

/-- Woodford, p. 670 (restated from the Chapter 4 project): the action, pointwise. -/
theorem rvMul_apply {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) (ω : Ω) : rvMul M a i ω = ∑ j, M i j * a j ω := by
  simp [rvMul, Finset.sum_apply]

/-- Woodford, p. 670: the action of a `2 × 2` matrix, pointwise. -/
theorem rvMul_two {Ω : Type*} (M : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → Ω → ℝ)
    (i : Fin 2) (ω : Ω) : rvMul M a i ω = M i 0 * a 0 ω + M i 1 * a 1 ω := by
  rw [rvMul_apply, Fin.sum_univ_two]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford, p. 670 (restated from the Chapter 4 project): `E_t` commutes with constant
matrices. -/
theorem E_rvMul {n m : ℕ} (t : ℕ) (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) : 𝔼.E t (rvMul M a i) = rvMul M (fun j => 𝔼.E t (a j)) i := by
  simp only [rvMul, map_sum, map_smul]

/-- Woodford, p. 670 (restated from the Chapter 4 project): a vector process solves the forward
system `s_t = K E_t s_{t+1} + w_t`. -/
def FSolves {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (w s : ℕ → Fin n → Ω → ℝ) : Prop :=
  ∀ t, s t = rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Woodford, p. 670 (restated from the Chapter 4 project): a vector process is adapted. -/
def VAdapted {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Woodford, p. 670 (restated from the Chapter 4 project): a vector process is bounded. -/
def VBounded {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M

/-- Woodford, p. 670 (restated from the Chapter 4 project): iterating a homogeneous forward
system, `d_t = Kᵏ E_t d_{t+k}`. -/
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

/-- Woodford, p. 670 (restated from the Chapter 4 project): bound for `Kᵏ` acting on a bounded
vector. -/
theorem abs_rvMul_pow_le {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ} {Cb ρ : ℝ}
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) (k : ℕ) {a : Fin n → Ω → ℝ} {M : ℝ}
    (ha : ∀ j ω, |a j ω| ≤ M) (i : Fin n) (ω : Ω) :
    |rvMul (K ^ k) a i ω| ≤ n * (Cb * ρ ^ k * M) := by
  rw [rvMul_apply]
  calc |∑ j, (K ^ k) i j * a j ω| ≤ ∑ j, |(K ^ k) i j * a j ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, Cb * ρ ^ k * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hK k i j) (ha j ω) (abs_nonneg _)
          ((abs_nonneg _).trans (hK k i j))
    _ = n * (Cb * ρ ^ k * M) := by simp

/-- Woodford, p. 670 (restated from the Chapter 4 project), fn. 1: if the powers of `K` decay
geometrically, the forward system `s_t = K E_t s_{t+1} + w_t` has at most one bounded adapted
solution. -/
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

/-- Woodford, p. 670 (restated from the Chapter 4 project), fn. 1: if the powers of `K` decay
geometrically, the forward series `s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` is a bounded adapted solution
of `s_t = K E_t s_{t+1} + w_t` for bounded adapted forcing `w`. -/
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
      rw [← Summable.tsum_finsetSum (fun l _ => (hTs (fun _ => t) (fun k => t + 1 + k) l
        ω).mul_left (K i l))]
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

/-- Woodford (2003), App. C.1, p. 670 (restated from the Chapter 4 project): the complex
eigenvalues of a real `2 × 2` matrix are the roots of `w² − (tr A) w + det A`. -/
theorem det_scalar_sub_two (K : Matrix (Fin 2) (Fin 2) ℝ) (w : ℂ) :
    (Matrix.scalar (Fin 2) w - K.map Complex.ofReal).det =
      w ^ 2 - (tr2 K : ℂ) * w + (det2 K : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [tr2, det2, Matrix.scalar_apply, Matrix.diagonal]
  ring

/-- Woodford (2003), Prop. C.1, p. 670 (restated from the Chapter 4 project): under the
Schur–Cohn condition the powers of a `2 × 2` matrix decay geometrically. -/
theorem pow_bound_of_schurStable {K : Matrix (Fin 2) (Fin 2) ℝ}
    (h : SchurStable (tr2 K) (det2 K)) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  refine pow_entry_bound K (fun w hw => ?_)
  rw [det_scalar_sub_two] at hw
  rcases eq_root_of_eq hw with rfl | rfl
  · exact ((schurStable_iff_roots _ _).mp h).1
  · exact ((schurStable_iff_roots _ _).mp h).2

/-- Woodford (2003), App. C.1, p. 670 (restated from the Chapter 4 project): the inverse
`A⁻¹ = (det A)⁻¹ adj A` of a `2 × 2` matrix. -/
noncomputable def inv2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![A 1 1 / det2 A, -A 0 1 / det2 A; -A 1 0 / det2 A, A 0 0 / det2 A]

/-- Woodford (2003), App. C.1, p. 670 (restated from the Chapter 4 project): `A⁻¹ A = I` when
`det A ≠ 0`. -/
theorem inv2_mul {A : Matrix (Fin 2) (Fin 2) ℝ} (h : det2 A ≠ 0) : inv2 A * A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inv2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (try rw [show det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 from rfl]) <;> ring

/-- Woodford (2003), App. C.1, p. 670 (restated from the Chapter 4 project): `A A⁻¹ = I` when
`det A ≠ 0`. -/
theorem mul_inv2 {A : Matrix (Fin 2) (Fin 2) ℝ} (h : det2 A ≠ 0) : A * inv2 A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inv2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (try rw [show det2 A = A 0 0 * A 1 1 - A 0 1 * A 1 0 from rfl]) <;> ring

/-- Woodford (2003), (C.19), p. 677 (restated from the Chapter 4 project): a constant matrix maps
a bounded vector process to a bounded one. -/
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

/-- Woodford (2003), (C.19), p. 677 (restated from the Chapter 4 project): a constant matrix maps
an adapted vector process to an adapted one. -/
theorem vAdapted_rvMul {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) {a : ℕ → Fin m → Ω → ℝ}
    (ha : VAdapted 𝔼 a) : VAdapted 𝔼 (fun t => rvMul M (a t)) := by
  intro t i
  change 𝔼.E t (rvMul M (a t) i) = rvMul M (a t) i
  rw [E_rvMul 𝔼]
  congr 1
  funext j
  exact ha t j

/-- Woodford (2003), Prop. C.1, p. 671 (restated from the Chapter 4 project): if
`λ² − Tλ + D = (λ − p)(λ − q)` with `|p|, |q| < 1`, the Schur–Cohn condition holds. -/
theorem schurStable_of_factor {T D : ℝ} {p q : ℂ}
    (h : ∀ z : ℂ, z ^ 2 - T * z + D = (z - p) * (z - q)) (hp : ‖p‖ < 1) (hq : ‖q‖ < 1) :
    SchurStable T D := by
  have e : ∀ r : ℂ, r ^ 2 - T * r + D = 0 → r = p ∨ r = q := by
    intro r hr
    rw [h r] at hr
    rcases mul_eq_zero.mp hr with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (sub_eq_zero.mp h')
  rw [schurStable_iff_roots]
  refine ⟨?_, ?_⟩
  · rcases e _ (root_eq T D _ (Or.inl rfl)) with e | e <;> rw [e] <;> assumption
  · rcases e _ (root_eq T D _ (Or.inr rfl)) with e | e <;> rw [e] <;> assumption

/-! ### The characteristic polynomial (G.10)–(G.13) -/

/-- Woodford (2003), (G.12), p. 722: the coefficient `a = 2(1 + β + σκ)/β + σ²λ_x/λ_i`. -/
noncomputable def aG (β σ κ lx li : ℝ) : ℝ := 2 * (1 + β + σ * κ) / β + σ ^ 2 * lx / li

/-- Woodford (2003), (G.12), p. 722: the coefficient
`b = (1 + 2κβσ + 2σκ + σ²κ² + 4β + β²)/β² + σ²((1 + β)λ_x + κ²)/(βλ_i)`. -/
noncomputable def bG (β σ κ lx li : ℝ) : ℝ :=
  (1 + 2 * κ * β * σ + 2 * σ * κ + σ ^ 2 * κ ^ 2 + 4 * β + β ^ 2) / β ^ 2
    + σ ^ 2 * ((1 + β) * lx + κ ^ 2) / (β * li)

/-- Woodford (2003), (G.12), p. 722: `p(µ) = µ⁴ − aµ³ + bµ² − aβ⁻¹µ + β⁻²` at a real argument. -/
noncomputable def pR (β σ κ lx li μ : ℝ) : ℝ :=
  μ ^ 4 - aG β σ κ lx li * μ ^ 3 + bG β σ κ lx li * μ ^ 2 - aG β σ κ lx li / β * μ + 1 / β ^ 2

/-- Woodford (2003), (G.10), p. 721: the matrix `Ī` multiplying `(Z_{t+1}, E_t z_{t+1},
E_t i_{t+1})`, with `Z_t = (x_{t−1}, i_{t−1}, i_{t−2})`, `z_t = (π_t, x_t)`. -/
def Ibar (β σ : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; 0, 0, 0, σ, 1, 0;
    0, 0, 0, β, 0, 0; 0, 0, 0, 0, 0, 0]

/-- Woodford (2003), (G.10), p. 721: the matrix `Ā` of the system (2.1), (3.1), (3.7)–(3.9); its
last row is the rule (3.7). -/
noncomputable def Abar (β σ κ lx li : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![0, 0, 0, 0, 1, 0; 0, 0, 0, 0, 0, 1; 0, 1, 0, 0, 0, 0; 0, 0, 0, 0, 1, σ;
    0, 0, 0, 1, -κ, 0;
    -(σ * lx / li), 1 + κ * σ / β + β⁻¹, -β⁻¹, κ * σ / li, σ * lx / li, -1]

/-- Woodford (2003), (G.11), p. 722: `det(Ā − µĪ) = −p(µ)βµ`. -/
theorem det_Abar {β σ κ lx li : ℝ} (hβ : β ≠ 0) (hli : li ≠ 0) (μ : ℝ) :
    (Abar β σ κ lx li - μ • Ibar β σ).det = -(pR β σ κ lx li μ) * β * μ := by
  unfold pR aG bG
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Abar, Ibar, Matrix.submatrix,
    Fin.succAbove]
  norm_num [Fin.succAbove, Fin.castSucc, Fin.succ]
  field_simp
  ring

/-- Woodford (2003), (G.12), p. 722: the general `β`-palindromic quartic
`µ⁴ − aµ³ + bµ² − aβ⁻¹µ + β⁻²` (complex coefficients). -/
noncomputable def palin (β : ℝ) (a b μ : ℂ) : ℂ :=
  μ ^ 4 - a * μ ^ 3 + b * μ ^ 2 - a / β * μ + 1 / (β : ℂ) ^ 2

/-- Woodford (2003), (G.12), p. 722: the quartic as a polynomial. -/
noncomputable def palinPoly (β : ℝ) (a b : ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 4 - Polynomial.C a * Polynomial.X ^ 3 + Polynomial.C b * Polynomial.X ^ 2
    - Polynomial.C (a / β) * Polynomial.X + Polynomial.C (1 / (β : ℂ) ^ 2)

/-- Woodford (2003), (G.12), p. 722: evaluating the polynomial. -/
theorem eval_palinPoly (β : ℝ) (a b μ : ℂ) : (palinPoly β a b).eval μ = palin β a b μ := by
  simp [palinPoly, palin]

/-- Woodford (2003), (G.12)–(G.13), p. 722 ("the symmetry in (G.12)"):
`p((βµ)⁻¹) = p(µ)/(β²µ⁴)`, so `µ` is a root iff `(βµ)⁻¹` is. -/
theorem palin_inv {β : ℝ} (hβ : β ≠ 0) (a b : ℂ) {μ : ℂ} (hμ : μ ≠ 0) :
    palin β a b ((β * μ)⁻¹) = palin β a b μ / ((β : ℂ) ^ 2 * μ ^ 4) := by
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  unfold palin
  field_simp
  ring

/-- Woodford (2003), (G.13), p. 722: the roots pair up, `µ` is a root iff `(βµ)⁻¹` is. -/
theorem palin_inv_eq_zero_iff {β : ℝ} (hβ : β ≠ 0) (a b : ℂ) {μ : ℂ} (hμ : μ ≠ 0) :
    palin β a b ((β * μ)⁻¹) = 0 ↔ palin β a b μ = 0 := by
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  rw [palin_inv hβ a b hμ, div_eq_zero_iff]
  simp [hβ', hμ]

/-- Woodford (2003), (G.12), p. 722: `0` is never a root (`p(0) = β⁻²`). -/
theorem palin_zero {β : ℝ} (hβ : β ≠ 0) (a b : ℂ) : palin β a b 0 ≠ 0 := by
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  simp [palin, hβ']

/-- Woodford (2003), (G.12), p. 722: the factorisation of a `β`-palindromic quartic through
`ν = µ + (βµ)⁻¹`: if `ν₁ + ν₂ = a` and `ν₁ν₂ = b − 2/β` then
`p(µ) = (µ² − ν₁µ + β⁻¹)(µ² − ν₂µ + β⁻¹)`. -/
theorem palin_factor {β : ℝ} (hβ : β ≠ 0) {a b ν1 ν2 : ℂ} (h1 : ν1 + ν2 = a)
    (h2 : ν1 * ν2 = b - 2 / β) (μ : ℂ) :
    palin β a b μ = (μ ^ 2 - ν1 * μ + 1 / β) * (μ ^ 2 - ν2 * μ + 1 / β) := by
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  have hb : b = ν1 * ν2 + 2 / β := by rw [h2]; ring
  subst h1
  rw [hb]
  unfold palin
  field_simp
  ring

/-- Woodford (2003), App. G.4, p. 722 (tool): every complex number pair `(s, c)` is the sum and
product of two complex numbers (the roots of `z² − sz + c`). -/
theorem exists_sum_prod (s c : ℂ) : ∃ x y : ℂ, x + y = s ∧ x * y = c := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self (s ^ 2 - 4 * c)
  exact ⟨(s + r) / 2, (s - r) / 2, by ring, by linear_combination (1 / 4 : ℂ) * hr⟩

/-- Woodford (2003), (G.13), p. 722: every `β`-palindromic quartic factors as
`(µ − µ₁)(µ − µ₂)(µ − µ₃)(µ − µ₄)` with `µ₁µ₂ = µ₃µ₄ = β⁻¹`, i.e. `µ₁ = (βµ₂)⁻¹` and
`µ₃ = (βµ₄)⁻¹`. -/
theorem palin_split {β : ℝ} (hβ : β ≠ 0) (a b : ℂ) :
    ∃ ν1 ν2 m1 m1' m2 m2' : ℂ, ν1 + ν2 = a ∧ ν1 * ν2 = b - 2 / β ∧
      m1 + m1' = ν1 ∧ m1 * m1' = 1 / β ∧ m2 + m2' = ν2 ∧ m2 * m2' = 1 / β ∧
      ∀ μ, palin β a b μ = (μ - m1) * (μ - m1') * ((μ - m2) * (μ - m2')) := by
  obtain ⟨ν1, ν2, h1, h2⟩ := exists_sum_prod a (b - 2 / β)
  obtain ⟨m1, m1', h3, h4⟩ := exists_sum_prod ν1 (1 / β)
  obtain ⟨m2, m2', h5, h6⟩ := exists_sum_prod ν2 (1 / β)
  refine ⟨ν1, ν2, m1, m1', m2, m2', h1, h2, h3, h4, h5, h6, fun μ => ?_⟩
  rw [palin_factor hβ h1 h2 μ, ← h3, ← h5]
  linear_combination (-(μ ^ 2 - (m2 + m2') * μ + m2 * m2')) * h4
    + (-(μ ^ 2 - (m1 + m1') * μ + 1 / β)) * h6

/-- Woodford (2003), (G.13), p. 722: the polynomial is the product of its four linear factors. -/
theorem palinPoly_eq_prod {β : ℝ} {a b m1 m1' m2 m2' : ℂ}
    (h : ∀ μ, palin β a b μ = (μ - m1) * (μ - m1') * ((μ - m2) * (μ - m2'))) :
    palinPoly β a b =
      ((m1 ::ₘ m1' ::ₘ m2 ::ₘ m2' ::ₘ 0).map (fun z => Polynomial.X - Polynomial.C z)).prod := by
  refine Polynomial.funext fun μ => ?_
  rw [eval_palinPoly, h μ]
  simp only [Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_one]
  ring

/-- Woodford (2003), (G.13), p. 722: the roots (with multiplicity) are `µ₁, …, µ₄`. -/
theorem palinPoly_roots {β : ℝ} {a b m1 m1' m2 m2' : ℂ}
    (h : ∀ μ, palin β a b μ = (μ - m1) * (μ - m1') * ((μ - m2) * (μ - m2'))) :
    (palinPoly β a b).roots = m1 ::ₘ m1' ::ₘ m2 ::ₘ m2' ::ₘ 0 := by
  rw [palinPoly_eq_prod h, Polynomial.roots_multiset_prod_X_sub_C]

/-- Woodford (2003), App. G.4, p. 722: the number of roots (with multiplicity) in the open unit
disc. -/
noncomputable def insideCard (P : Polynomial ℂ) : ℕ := (P.roots.filter (fun z => ‖z‖ < 1)).card

/-- Woodford (2003), App. G.4, p. 722 (tool): the indicator of the open unit disc. -/
noncomputable def ind (z : ℂ) : ℕ := if ‖z‖ < 1 then 1 else 0

/-- Woodford (2003), App. G.4, p. 722 (tool): counting the roots of a cons. -/
theorem card_filter_cons (z : ℂ) (s : Multiset ℂ) :
    ((z ::ₘ s).filter (fun z => ‖z‖ < 1)).card = ind z + (s.filter (fun z => ‖z‖ < 1)).card := by
  unfold ind
  by_cases h : ‖z‖ < 1
  · rw [Multiset.filter_cons_of_pos (p := fun z : ℂ => ‖z‖ < 1) (a := z) s h,
      Multiset.card_cons]
    simp [h, add_comm]
  · rw [Multiset.filter_cons_of_neg (p := fun z : ℂ => ‖z‖ < 1) (a := z) s h]
    simp [h]

/-- Woodford (2003), App. G.4, p. 722: the closed annulus `1 ≤ |µ| ≤ β⁻¹`. -/
def Annulus (β : ℝ) (z : ℂ) : Prop := 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / β

/-- Woodford (2003), (G.13), p. 722: `|µ| |µ'| = β⁻¹` for a pair. -/
theorem norm_pair {β : ℝ} (hβ : 0 < β) {m m' : ℂ} (h : m * m' = 1 / β) :
    ‖m‖ * ‖m'‖ = 1 / β := by
  rw [← norm_mul, h, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]

/-- Woodford (2003), App. G.4, p. 722 (the book's step): at most one root of a pair
`µµ' = β⁻¹` lies in the open unit disc. -/
theorem ind_pair_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m m' : ℂ} (h : m * m' = 1 / β) :
    ind m + ind m' ≤ 1 := by
  have hn := norm_pair hβ0 h
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  unfold ind
  by_cases hm : ‖m‖ < 1 <;> by_cases hm' : ‖m'‖ < 1 <;> simp only [hm, hm', ↓reduceIte] <;>
    try omega
  nlinarith [norm_nonneg m, norm_nonneg m']

/-- Woodford (2003), App. G.4, p. 722 (survey E21, the precise form): exactly one root of a pair
`µµ' = β⁻¹` lies in the open unit disc iff neither lies in the annulus `1 ≤ |µ| ≤ β⁻¹`. -/
theorem ind_pair_eq_one_iff {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m m' : ℂ}
    (h : m * m' = 1 / β) :
    ind m + ind m' = 1 ↔ ¬ Annulus β m ∧ ¬ Annulus β m' := by
  have hn := norm_pair hβ0 h
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have hpos : 0 < ‖m‖ := by
    rcases (norm_nonneg m).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', zero_mul] at hn; linarith
  have hpos' : 0 < ‖m'‖ := by
    rcases (norm_nonneg m').lt_or_eq with h' | h'
    · exact h'
    · rw [← h', mul_zero] at hn; linarith
  unfold ind Annulus
  constructor
  · intro hc
    by_cases hm : ‖m‖ < 1
    · have hm' : 1 / β < ‖m'‖ := by
        by_contra hc'
        push Not at hc'
        nlinarith
      exact ⟨fun h' => by linarith [h'.1], fun h' => by linarith [h'.2]⟩
    · simp only [hm, ↓reduceIte, zero_add] at hc
      by_cases hm' : ‖m'‖ < 1
      · have : 1 / β < ‖m‖ := by
          by_contra hc'
          push Not at hc'
          nlinarith
        exact ⟨fun h' => by linarith [h'.2], fun h' => by linarith [h'.1]⟩
      · simp [hm'] at hc
  · rintro ⟨ha, ha'⟩
    by_cases hm : ‖m‖ < 1
    · have hm' : ¬ ‖m'‖ < 1 := by
        intro hm'
        nlinarith [norm_nonneg m, norm_nonneg m']
      simp [hm, hm']
    · have hgt : 1 / β < ‖m‖ := by
        push Not at hm
        by_contra hc
        push Not at hc
        exact ha ⟨hm, hc⟩
      have hm' : ‖m'‖ < 1 := by
        by_contra hc
        push Not at hc
        nlinarith
      simp [hm, hm']

/-- Woodford (2003), App. G.4, p. 722: the partner of a root in the annulus is in the annulus. -/
theorem annulus_pair {β : ℝ} (hβ0 : 0 < β) {m m' : ℂ} (h : m * m' = 1 / β)
    (ha : Annulus β m) : Annulus β m' := by
  have hn := norm_pair hβ0 h
  obtain ⟨h1, h2⟩ := ha
  have hpos : 0 < ‖m‖ := by linarith
  have hb : 0 < 1 / β := by positivity
  refine ⟨?_, ?_⟩
  · by_contra hc
    push Not at hc
    nlinarith [norm_nonneg m']
  · by_contra hc
    push Not at hc
    nlinarith [norm_nonneg m']

/-- **Woodford (2003), App. G.4, p. 722 — the book's pairing argument.** A `β`-palindromic
quartic (`0 < β < 1`) has at most two roots, counted with multiplicity, in the open unit disc. -/
theorem palin_insideCard_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a b : ℂ) :
    insideCard (palinPoly β a b) ≤ 2 := by
  obtain ⟨ν1, ν2, m1, m1', m2, m2', -, -, -, h4, -, h6, hf⟩ := palin_split hβ0.ne' a b
  unfold insideCard
  rw [palinPoly_roots hf]
  simp only [card_filter_cons, Multiset.filter_zero, Multiset.card_zero]
  have := ind_pair_le hβ0 hβ1 h4
  have := ind_pair_le hβ0 hβ1 h6
  omega

/-- **Woodford (2003), App. G.4, p. 722 — the precise form of the argument (survey E21).** A
`β`-palindromic quartic has exactly two roots (with multiplicity) in the open unit disc **iff** it
has no root in the closed annulus `1 ≤ |µ| ≤ β⁻¹`. -/
theorem palin_insideCard_eq_two_iff {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (a b : ℂ) :
    insideCard (palinPoly β a b) = 2 ↔ ∀ μ, palin β a b μ = 0 → ¬ Annulus β μ := by
  obtain ⟨ν1, ν2, m1, m1', m2, m2', -, -, -, h4, -, h6, hf⟩ := palin_split hβ0.ne' a b
  unfold insideCard
  rw [palinPoly_roots hf]
  simp only [card_filter_cons, Multiset.filter_zero, Multiset.card_zero]
  have l1 := ind_pair_le hβ0 hβ1 h4
  have l2 := ind_pair_le hβ0 hβ1 h6
  have e1 := ind_pair_eq_one_iff hβ0 hβ1 h4
  have e2 := ind_pair_eq_one_iff hβ0 hβ1 h6
  constructor
  · intro hc μ hμ
    have hc1 : ind m1 + ind m1' = 1 := by omega
    have hc2 : ind m2 + ind m2' = 1 := by omega
    rw [hf μ] at hμ
    rcases mul_eq_zero.mp hμ with hμ | hμ <;> rcases mul_eq_zero.mp hμ with hμ | hμ <;>
      rw [sub_eq_zero.mp hμ]
    · exact (e1.mp hc1).1
    · exact (e1.mp hc1).2
    · exact (e2.mp hc2).1
    · exact (e2.mp hc2).2
  · intro hno
    have r : ∀ z, palin β a b z = 0 → ¬ Annulus β z := hno
    have hc1 : ind m1 + ind m1' = 1 := e1.mpr ⟨r m1 (by rw [hf]; ring), r m1' (by rw [hf]; ring)⟩
    have hc2 : ind m2 + ind m2' = 1 := e2.mpr ⟨r m2 (by rw [hf]; ring), r m2' (by rw [hf]; ring)⟩
    omega

/-! ### No root of the model's `p` lies in the annulus -/

/-- Woodford (2003), (G.12), p. 722: the model's characteristic polynomial `p(µ)` at a complex
argument. -/
noncomputable def pG (β σ κ lx li : ℝ) (μ : ℂ) : ℂ := palin β (aG β σ κ lx li) (bG β σ κ lx li) μ

/-- Woodford (2003), (G.12), p. 722: `p` as a polynomial. -/
noncomputable def pGPoly (β σ κ lx li : ℝ) : Polynomial ℂ :=
  palinPoly β (aG β σ κ lx li) (bG β σ κ lx li)

/-- Woodford (2003), (G.12), p. 722: at a real argument `p` is the real polynomial `pR`. -/
theorem pG_ofReal (β σ κ lx li μ : ℝ) : pG β σ κ lx li μ = pR β σ κ lx li μ := by
  simp [pG, palin, pR]

/-- Woodford (2003), App. G.4, p. 722 (tool): the quadratic `Q(s) = s² − T_Q s + K_Q` with
`T_Q = 2κσ/β + σ²λ_x/λ_i` and `K_Q = κ²σ²(β⁻² + (βλ_i)⁻¹)`. -/
noncomputable def Qs (β σ κ lx li : ℝ) (s : ℂ) : ℂ :=
  s ^ 2 - ((2 * κ * σ / β + σ ^ 2 * lx / li : ℝ) : ℂ) * s
    + ((κ ^ 2 * σ ^ 2 * (1 / β ^ 2 + 1 / (β * li)) : ℝ) : ℂ)

/-- Woodford (2003), (G.12), p. 722 (the structure behind it): with `s = µ + (βµ)⁻¹ − (1+β)/β`,
`p(µ) = µ² Q(s)`. -/
theorem pG_eq_Qs {β σ κ lx li : ℝ} (hβ : β ≠ 0) (hli : li ≠ 0) {μ : ℂ} (hμ : μ ≠ 0) :
    pG β σ κ lx li μ = μ ^ 2 * Qs β σ κ lx li (μ + ((β : ℂ) * μ)⁻¹ - (((1 + β) / β : ℝ) : ℂ)) := by
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  have hli' : (li : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hli
  unfold pG palin Qs aG bG
  push_cast
  field_simp
  ring

/-- Woodford (2003), (G.12), p. 722: in the variable `ν = µ + (βµ)⁻¹`, `ν² − aν + b − 2/β =
Q(ν − (1+β)/β)`. -/
theorem nu_quad_eq_Qs {β σ κ lx li : ℝ} (hβ : β ≠ 0) (hli : li ≠ 0) (ν : ℂ) :
    ν ^ 2 - (aG β σ κ lx li : ℂ) * ν + ((bG β σ κ lx li : ℂ) - 2 / β) =
      Qs β σ κ lx li (ν - (((1 + β) / β : ℝ) : ℂ)) := by
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
  have hli' : (li : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hli
  unfold Qs aG bG
  push_cast
  field_simp
  ring

/-- Woodford (2003), App. G.4, p. 722 (tool): a quadratic `s² − Ts + K` with `T, K > 0` has no
root with `Re s ≤ 0`. -/
theorem quad_ne_zero_of_re_nonpos {Tq Kq : ℝ} (hT : 0 < Tq) (hK : 0 < Kq) {s : ℂ}
    (hs : s.re ≤ 0) : s ^ 2 - (Tq : ℂ) * s + (Kq : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, Complex.add_im, Complex.sub_im, Complex.mul_im,
    Complex.zero_im] at hre him
  have hm : s.im * (2 * s.re - Tq) = 0 := by linarith
  rcases mul_eq_zero.mp hm with h0 | h0
  · rw [h0] at hre
    nlinarith
  · linarith

/-- Woodford (2003), App. G.4, p. 722: on the annulus `1 ≤ |µ| ≤ β⁻¹`, the variable
`s = µ + (βµ)⁻¹ − (1+β)/β` has `Re s ≤ 0`. -/
theorem re_s_nonpos {β : ℝ} (hβ0 : 0 < β) {μ : ℂ} (ha : Annulus β μ) :
    (μ + ((β : ℂ) * μ)⁻¹ - (((1 + β) / β : ℝ) : ℂ)).re ≤ 0 := by
  obtain ⟨h1, h2⟩ := ha
  set r := ‖μ‖ with hr
  have hr0 : 0 < r := by linarith
  have hns : Complex.normSq μ = r ^ 2 := by rw [hr, Complex.sq_norm]
  have hinv : (((β : ℂ) * μ)⁻¹).re = μ.re / (β * r ^ 2) := by
    rw [Complex.inv_re, Complex.normSq_mul, Complex.normSq_ofReal, hns, Complex.re_ofReal_mul]
    field_simp
  rw [Complex.sub_re, Complex.add_re, hinv, Complex.ofReal_re]
  have hre : μ.re ≤ r := Complex.re_le_norm μ
  have hc : 0 < 1 + 1 / (β * r ^ 2) := by positivity
  have key : μ.re + μ.re / (β * r ^ 2) ≤ r + r / (β * r ^ 2) := by
    have : μ.re + μ.re / (β * r ^ 2) = μ.re * (1 + 1 / (β * r ^ 2)) := by ring
    rw [this]
    have : r + r / (β * r ^ 2) = r * (1 + 1 / (β * r ^ 2)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hre hc.le
  have hbound : r + r / (β * r ^ 2) - (1 + β) / β = (r - 1) * (β * r - 1) / (β * r) := by
    field_simp
    ring
  have hβr : β * r ≤ 1 := by
    have := h2
    rw [le_div_iff₀ hβ0] at this
    linarith
  have : (r - 1) * (β * r - 1) / (β * r) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  linarith

/-- **Woodford (2003), App. G.4, p. 722 (survey E21, closing the gap).** For `0 < β < 1`,
`σ, κ, λ_i > 0`, `λ_x ≥ 0`, the polynomial `p` of (G.12) has no root in the closed annulus
`1 ≤ |µ| ≤ β⁻¹` — in particular none on the unit circle. -/
theorem pG_ne_zero_of_annulus {β σ κ lx li : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ)
    (hlx : 0 ≤ lx) (hli : 0 < li) {μ : ℂ} (ha : Annulus β μ) : pG β σ κ lx li μ ≠ 0 := by
  have hμ : μ ≠ 0 := by
    intro h
    have := ha.1
    rw [h, norm_zero] at this
    linarith
  rw [pG_eq_Qs hβ0.ne' hli.ne' hμ]
  refine mul_ne_zero (pow_ne_zero 2 hμ) ?_
  unfold Qs
  refine quad_ne_zero_of_re_nonpos (by positivity) (by positivity) (re_s_nonpos hβ0 ha)

/-- Woodford (2003), App. G.4, p. 722 (survey E21): any root `ν` of `ν² − aν + b − 2/β` has
`Re ν > (1+β)/β > 0`. -/
theorem nu_re_pos {β σ κ lx li : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) (hlx : 0 ≤ lx)
    (hli : 0 < li) {ν : ℂ}
    (hν : ν ^ 2 - (aG β σ κ lx li : ℂ) * ν + ((bG β σ κ lx li : ℂ) - 2 / β) = 0) :
    (1 + β) / β < ν.re := by
  rw [nu_quad_eq_Qs hβ0.ne' hli.ne'] at hν
  by_contra hc
  push Not at hc
  have hs : (ν - (((1 + β) / β : ℝ) : ℂ)).re ≤ 0 := by
    rw [Complex.sub_re, Complex.ofReal_re]; linarith
  exact quad_ne_zero_of_re_nonpos (by positivity) (by positivity) hs hν

/-- **Woodford (2003), App. G.4, p. 722: exactly two roots inside.** For all admissible
parameters, `p` has exactly two roots (counted with multiplicity) in the open unit disc. -/
theorem pG_insideCard_eq_two {β σ κ lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hlx : 0 ≤ lx) (hli : 0 < li) : insideCard (pGPoly β σ κ lx li) = 2 :=
  (palin_insideCard_eq_two_iff hβ0 hβ1 _ _).mpr fun _ hμ ha =>
    pG_ne_zero_of_annulus hβ0 hσ hκ hlx hli ha hμ

/-! ### The stable real factor of `p` -/

/-- Woodford (2003), (G.13), p. 722: a pair `µµ' = β⁻¹` whose first root is not in the annulus
(then neither is the second, `annulus_pair`) can be ordered with the first root inside the unit
disc and the second outside the disc of radius `β⁻¹`. -/
theorem pair_split {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {ν m m' : ℂ} (hs : m + m' = ν)
    (hp : m * m' = 1 / β) (ha : ¬ Annulus β m) :
    ∃ u v : ℂ, u + v = ν ∧ u * v = 1 / β ∧ ‖u‖ < 1 ∧ 1 / β < ‖v‖ := by
  have hn := norm_pair hβ0 hp
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have hb : 0 < 1 / β := by positivity
  by_cases hm : ‖m‖ < 1
  · refine ⟨m, m', hs, hp, hm, ?_⟩
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg (norm_nonneg m) (sub_nonneg.mpr hc), mul_pos (sub_pos.mpr hm) hb]
  · push Not at hm
    have hgt : 1 / β < ‖m‖ := by
      by_contra hc
      push Not at hc
      exact ha ⟨hm, hc⟩
    refine ⟨m', m, by rw [add_comm]; exact hs, by rw [mul_comm]; exact hp, ?_, hgt⟩
    by_contra hc
    push Not at hc
    nlinarith [mul_le_mul_of_nonneg_left hc (norm_nonneg m)]

/-- Woodford (2003), (G.13), p. 722: the root of `z² − νz + β⁻¹` in the open unit disc is unique
when its partner has modulus at least one. -/
theorem inside_root_unique {β : ℝ} {ν u v z : ℂ} (hs : u + v = ν) (hp : u * v = 1 / β)
    (hv : 1 ≤ ‖v‖) (hz : z ^ 2 - ν * z + 1 / β = 0) (hz1 : ‖z‖ < 1) : z = u := by
  have h : (z - u) * (z - v) = 0 := by linear_combination hz + (-z) * hs + hp
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · rw [sub_eq_zero.mp h] at hz1
    linarith

/-- Woodford (2003), (G.13), p. 722: a root of a pair is a root of its quadratic factor. -/
theorem pair_root {β : ℝ} {ν u v : ℂ} (hs : u + v = ν) (hp : u * v = 1 / β) :
    u ^ 2 - ν * u + 1 / β = 0 := by
  linear_combination u * hs - hp

/-- Woodford (2003), (G.13), p. 722: conjugating a root of `z² − νz + β⁻¹`. -/
theorem conj_pair_root {β : ℝ} {ν u : ℂ} (h : u ^ 2 - ν * u + 1 / β = 0) :
    (conj u) ^ 2 - conj ν * conj u + 1 / β = 0 := by
  have := congrArg conj h
  simpa [map_sub, map_add, map_mul, map_pow, Complex.conj_ofReal, map_div₀] using this

/-- Woodford (2003), App. G.4, p. 722: a real root `u` of `z² − νz + β⁻¹` with `Re ν > 0`, real
`ν`, is positive. -/
theorem pos_of_real_pair {β : ℝ} (hβ0 : 0 < β) {ν u v : ℂ} (hs : u + v = ν)
    (hp : u * v = 1 / β) (hνim : ν.im = 0) (huim : u.im = 0) (hνre : 0 < ν.re) : 0 < u.re := by
  have hvim : v.im = 0 := by
    have := congrArg Complex.im hs
    simp only [Complex.add_im] at this
    linarith
  have hre := congrArg Complex.re hp
  have hsre := congrArg Complex.re hs
  simp only [Complex.mul_re, huim, hvim, mul_zero, sub_zero, Complex.add_re] at hre hsre
  have h1 : (1 / (β : ℂ)).re = 1 / β := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [h1] at hre
  have hb : 0 < 1 / β := by positivity
  by_contra hc
  push Not at hc
  nlinarith

/-- **Woodford (2003), App. G.4, p. 722: the stable factor of `p` is real.** For admissible
parameters there are real `T, D` with `µ² − Tµ + D` Schur-stable (both roots in the open unit
disc), `D > 0`, and `p(µ) = (µ² − Tµ + D)(µ² − (T/(βD))µ + 1/(β²D))` — the second factor carries
the partner roots `(βµ_k)⁻¹`. -/
theorem exists_real_split {β σ κ lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hlx : 0 ≤ lx) (hli : 0 < li) :
    ∃ T D : ℝ, SchurStable T D ∧ 0 < D ∧ ∀ μ : ℂ, pG β σ κ lx li μ =
      (μ ^ 2 - T * μ + D) *
        (μ ^ 2 - ((T / (β * D) : ℝ) : ℂ) * μ + ((1 / (β ^ 2 * D) : ℝ) : ℂ)) := by
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ0.ne'
  set a := aG β σ κ lx li with ha
  set b := bG β σ κ lx li with hb
  obtain ⟨ν1, ν2, h1, h2⟩ := exists_sum_prod (a : ℂ) ((b : ℂ) - 2 / β)
  obtain ⟨p, p', hp1, hp2⟩ := exists_sum_prod ν1 (1 / β)
  obtain ⟨q, q', hq1, hq2⟩ := exists_sum_prod ν2 (1 / β)
  have hf : ∀ μ, pG β σ κ lx li μ = (μ - p) * (μ - p') * ((μ - q) * (μ - q')) := by
    intro μ
    unfold pG
    rw [palin_factor hβ0.ne' h1 h2 μ, ← hp1, ← hq1]
    linear_combination (-(μ ^ 2 - (q + q') * μ + q * q')) * hp2
      + (-(μ ^ 2 - (p + p') * μ + 1 / β)) * hq2
  have hroot : ∀ z, pG β σ κ lx li z = 0 → ¬ Annulus β z := fun z hz ha =>
    pG_ne_zero_of_annulus hβ0 hσ hκ hlx hli ha hz
  obtain ⟨u1, v1, hu1, hv1, hn1, hm1⟩ := pair_split hβ0 hβ1 hp1 hp2
    (hroot p (by rw [hf]; ring))
  obtain ⟨u2, v2, hu2, hv2, hn2, hm2⟩ := pair_split hβ0 hβ1 hq1 hq2
    (hroot q (by rw [hf]; ring))
  have hone : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
  have hv1ge : 1 ≤ ‖v1‖ := by linarith
  have hv2ge : 1 ≤ ‖v2‖ := by linarith
  have hνq : ∀ z : ℂ, z ^ 2 - (a : ℂ) * z + ((b : ℂ) - 2 / β) = (z - ν1) * (z - ν2) := by
    intro z
    rw [← h1, ← h2]
    ring
  have hν1root : ν1 ^ 2 - (a : ℂ) * ν1 + ((b : ℂ) - 2 / β) = 0 := by rw [hνq]; ring
  have hν2root : ν2 ^ 2 - (a : ℂ) * ν2 + ((b : ℂ) - 2 / β) = 0 := by rw [hνq]; ring
  have hcν : conj ν1 = ν1 ∨ conj ν1 = ν2 := by
    have hc : (conj ν1) ^ 2 - (a : ℂ) * conj ν1 + ((b : ℂ) - 2 / β) = 0 := by
      have := congrArg conj hν1root
      simpa [map_sub, map_add, map_mul, map_pow, Complex.conj_ofReal, map_div₀, map_ofNat]
        using this
    rw [hνq] at hc
    rcases mul_eq_zero.mp hc with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have hcu1 := conj_pair_root (pair_root hu1 hv1)
  have hcu2 := conj_pair_root (pair_root hu2 hv2)
  have hnc1 : ‖conj u1‖ < 1 := by rw [Complex.norm_conj]; exact hn1
  have hnc2 : ‖conj u2‖ < 1 := by rw [Complex.norm_conj]; exact hn2
  have hu1ne : u1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hv1
    exact (one_div_ne_zero hβ') hv1.symm
  have hu2ne : u2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hv2
    exact (one_div_ne_zero hβ') hv2.symm
  have key : (u1 + u2).im = 0 ∧ (u1 * u2).im = 0 ∧ 0 < (u1 * u2).re := by
    rcases hcν with hc | hc
    · have e1 : conj u1 = u1 := inside_root_unique hu1 hv1 hv1ge (by rw [← hc]; exact hcu1) hnc1
      have hc2 : conj ν2 = ν2 := by
        have : ν2 = (a : ℂ) - ν1 := by rw [← h1]; ring
        rw [this, map_sub, Complex.conj_ofReal, hc]
      have e2 : conj u2 = u2 :=
        inside_root_unique hu2 hv2 hv2ge (by rw [← hc2]; exact hcu2) hnc2
      have i1 : u1.im = 0 := Complex.conj_eq_iff_im.mp e1
      have i2 : u2.im = 0 := Complex.conj_eq_iff_im.mp e2
      have r1 : 0 < u1.re := pos_of_real_pair hβ0 hu1 hv1 (Complex.conj_eq_iff_im.mp hc) i1
        (lt_trans (by positivity) (nu_re_pos hβ0 hσ hκ hlx hli hν1root))
      have r2 : 0 < u2.re := pos_of_real_pair hβ0 hu2 hv2 (Complex.conj_eq_iff_im.mp hc2) i2
        (lt_trans (by positivity) (nu_re_pos hβ0 hσ hκ hlx hli hν2root))
      refine ⟨?_, ?_, ?_⟩
      · simp [Complex.add_im, i1, i2]
      · simp [Complex.mul_im, i1, i2]
      · simp only [Complex.mul_re, i1, i2, mul_zero, sub_zero]
        positivity
    · have e : conj u1 = u2 := inside_root_unique hu2 hv2 hv2ge (by rw [← hc]; exact hcu1) hnc1
      rw [← e, Complex.mul_conj]
      refine ⟨by simp [Complex.add_im], by simp, ?_⟩
      rw [Complex.ofReal_re]
      exact Complex.normSq_pos.mpr hu1ne
  set T := (u1 + u2).re with hTdef
  set D := (u1 * u2).re with hDdef
  have hT : (T : ℂ) = u1 + u2 := Complex.ext (by simp [hTdef]) (by simp [key.1])
  have hD : (D : ℂ) = u1 * u2 := Complex.ext (by simp [hDdef]) (by simp [key.2.1])
  refine ⟨T, D, schurStable_of_factor (fun z => by rw [hT, hD]; ring) hn1 hn2, key.2.2,
    fun μ => ?_⟩
  have e1 : (μ - p) * (μ - p') = (μ - u1) * (μ - v1) := by
    linear_combination (-μ) * hp1 + hp2 + μ * hu1 - hv1
  have e2 : (μ - q) * (μ - q') = (μ - u2) * (μ - v2) := by
    linear_combination (-μ) * hq1 + hq2 + μ * hu2 - hv2
  have hv1' : v1 = 1 / (β * u1) := by
    rw [eq_div_iff (mul_ne_zero hβ' hu1ne)]
    have h : u1 * v1 * β = 1 := by rw [hv1]; field_simp
    linear_combination h
  have hv2' : v2 = 1 / (β * u2) := by
    rw [eq_div_iff (mul_ne_zero hβ' hu2ne)]
    have h : u2 * v2 * β = 1 := by rw [hv2]; field_simp
    linear_combination h
  rw [hf μ, e1, e2]
  push_cast
  rw [hT, hD, hv1', hv2']
  field_simp
  ring

/-! ### Second-order vector systems with one predetermined lag (the Blanchard–Kahn argument) -/

/-- Woodford (2003), §1.2 and App. G.4, p. 721: a vector process lagged once, with the
pre-sample value `z_{−1} = z₀` (known numbers). -/
def lagV (z0 : Fin 2 → ℝ) (z : ℕ → Fin 2 → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ
  | 0 => fun i _ => z0 i
  | t + 1 => z t

/-- Woodford (2003), App. G.4, p. 721: `Φ` solves the second-order system
`P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t` for all `t ≥ 0`, with `Φ_{−1} = Φm`. -/
def Sys2 (P A1 A2 : Matrix (Fin 2) (Fin 2) ℝ) (F : ℕ → Fin 2 → Ω → ℝ) (Φm : Fin 2 → ℝ)
    (Φ : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t, rvMul P (fun j => 𝔼.E t (Φ (t + 1) j)) - rvMul A1 (Φ t) + rvMul A2 (lagV Φm Φ t) = F t

/-- Woodford (2003), App. G.4 (the unstable block): `ψ_t = Φ_t − XΦ_{t−1}`. -/
def psiOf (X : Matrix (Fin 2) (Fin 2) ℝ) (Φm : Fin 2 → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) :
    ℕ → Fin 2 → Ω → ℝ :=
  fun s => Φ s - rvMul X (lagV Φm Φ s)

/-- Woodford (2003), App. G.4, p. 721 (tool): `E_t` of a matrix image, as vectors. -/
theorem E_rvMul_vec (t : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → Ω → ℝ) :
    (fun j => 𝔼.E t (rvMul M a j)) = rvMul M (fun j => 𝔼.E t (a j)) := by
  funext j
  exact E_rvMul 𝔼 t M a j

/-- Woodford (2003), App. G.4, p. 721 (the key reduction): if `X` solves the matrix quadratic
`PX² − A₁X + A₂ = 0` and `B = PX − A₁` is invertible, then for an adapted `Φ` the system holds at
date `t` iff `ψ = Φ − XΦ_{−1}` solves the forward system `ψ_t = K E_tψ_{t+1} + B⁻¹F_t` with
`K = −B⁻¹P`. -/
theorem sys2_step_iff {P A1 A2 X : Matrix (Fin 2) (Fin 2) ℝ} (hX : P * X * X - A1 * X + A2 = 0)
    (hB : det2 (P * X - A1) ≠ 0) {F : ℕ → Fin 2 → Ω → ℝ} {Φm : Fin 2 → ℝ}
    {Φ : ℕ → Fin 2 → Ω → ℝ} (hΦa : VAdapted 𝔼 Φ) (t : ℕ) :
    (rvMul P (fun j => 𝔼.E t (Φ (t + 1) j)) - rvMul A1 (Φ t) + rvMul A2 (lagV Φm Φ t) = F t) ↔
      psiOf X Φm Φ t = rvMul (-(inv2 (P * X - A1) * P))
        (fun j => 𝔼.E t (psiOf X Φm Φ (t + 1) j)) + rvMul (inv2 (P * X - A1)) (F t) := by
  set B := P * X - A1 with hBdef
  have hEΦ : (fun j => 𝔼.E t (Φ t j)) = Φ t := funext fun j => hΦa t j
  have hEψ : (fun j => 𝔼.E t (psiOf X Φm Φ (t + 1) j)) =
      (fun j => 𝔼.E t (Φ (t + 1) j)) - rvMul X (Φ t) := by
    funext j
    simp only [psiOf, lagV, Pi.sub_apply, map_sub]
    rw [E_rvMul 𝔼, hEΦ]
  have hBX : B * X = -A2 := by
    rw [hBdef, sub_mul]
    exact eq_neg_of_add_eq_zero_left hX
  have hL : rvMul P (fun j => 𝔼.E t (Φ (t + 1) j)) - rvMul A1 (Φ t) + rvMul A2 (lagV Φm Φ t) =
      rvMul P (fun j => 𝔼.E t (psiOf X Φm Φ (t + 1) j)) + rvMul B (psiOf X Φm Φ t) := by
    rw [hEψ]
    simp only [psiOf]
    rw [rvMul_sub, rvMul_sub, rvMul_rvMul, rvMul_rvMul, hBX, neg_rvMul, hBdef, sub_rvMul]
    abel
  rw [hL]
  set v := (fun j => 𝔼.E t (psiOf X Φm Φ (t + 1) j))
  set ψ := psiOf X Φm Φ t
  constructor
  · intro h
    have h2 := congrArg (rvMul (inv2 B)) h
    rw [rvMul_add, rvMul_rvMul, rvMul_rvMul, inv2_mul hB, rvMul_one] at h2
    rw [neg_rvMul]
    linear_combination h2
  · intro h
    rw [h, rvMul_add, rvMul_rvMul, rvMul_rvMul, mul_neg, ← mul_assoc, mul_inv2 hB, one_mul,
      rvMul_one, neg_rvMul]
    abel

/-- Woodford (2003), App. G.4 (the stable block, backward): `Φ_t = XΦ_{t−1} + ψ_t` from
`Φ_{−1} = Φm`. -/
def backRec (X : Matrix (Fin 2) (Fin 2) ℝ) (Φm : Fin 2 → ℝ) (ψ : ℕ → Fin 2 → Ω → ℝ) :
    ℕ → Fin 2 → Ω → ℝ
  | 0 => rvMul X (fun i _ => Φm i) + ψ 0
  | t + 1 => rvMul X (backRec X Φm ψ t) + ψ (t + 1)

/-- Woodford (2003), App. G.4: the backward recursion in lag form. -/
theorem backRec_eq (X : Matrix (Fin 2) (Fin 2) ℝ) (Φm : Fin 2 → ℝ) (ψ : ℕ → Fin 2 → Ω → ℝ)
    (t : ℕ) : backRec X Φm ψ t = rvMul X (lagV Φm (backRec X Φm ψ) t) + ψ t := by
  cases t <;> rfl

/-- Woodford (2003), App. G.4 (tool): a matrix image of a finite sum. -/
theorem rvMul_sum (M : Matrix (Fin 2) (Fin 2) ℝ) (s : Finset ℕ) (f : ℕ → Fin 2 → Ω → ℝ) :
    rvMul M (∑ k ∈ s, f k) = ∑ k ∈ s, rvMul M (f k) := by
  induction s using Finset.induction_on with
  | empty => funext i; simp [rvMul]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, rvMul_add, ih]

/-- Woodford (2003), App. G.4: the closed form
`Φ_t = X^{t+1}Φ_{−1} + ∑_{k ≤ t} X^{t−k}ψ_k`. -/
theorem backRec_closed (X : Matrix (Fin 2) (Fin 2) ℝ) (Φm : Fin 2 → ℝ)
    (ψ : ℕ → Fin 2 → Ω → ℝ) (t : ℕ) :
    backRec X Φm ψ t = rvMul (X ^ (t + 1)) (fun i _ => Φm i)
      + ∑ k ∈ Finset.range (t + 1), rvMul (X ^ (t - k)) (ψ k) := by
  induction t with
  | zero => simp [backRec, rvMul_one]
  | succ t ih =>
    rw [show backRec X Φm ψ (t + 1) = rvMul X (backRec X Φm ψ t) + ψ (t + 1) from rfl, ih,
      rvMul_add, rvMul_rvMul, rvMul_sum, Finset.sum_range_succ _ (t + 1), Nat.sub_self,
      pow_zero, rvMul_one, ← pow_succ']
    have : ∑ k ∈ Finset.range (t + 1), rvMul X (rvMul (X ^ (t - k)) (ψ k)) =
        ∑ k ∈ Finset.range (t + 1), rvMul (X ^ (t + 1 - k)) (ψ k) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [rvMul_rvMul, ← pow_succ', show t + 1 - k = t - k + 1 by omega]
    rw [this]
    abel

/-- Woodford (2003), App. G.4: with `X` Schur-stable and `ψ` bounded, the backward recursion is
bounded. -/
theorem backRec_bounded {X : Matrix (Fin 2) (Fin 2) ℝ} (hXs : SchurStable (tr2 X) (det2 X))
    (Φm : Fin 2 → ℝ) {ψ : ℕ → Fin 2 → Ω → ℝ} (hψ : VBounded ψ) : VBounded (backRec X Φm ψ) := by
  obtain ⟨Cb, ρ, hCb, hρ0, hρ1, hX⟩ := pow_bound_of_schurStable hXs
  obtain ⟨Mψ, hMψ⟩ := hψ
  set M0 := |Φm 0| + |Φm 1| with hM0def
  have hM0n : 0 ≤ M0 := by positivity
  have hM0 : ∀ j (ω : Ω), |(fun i (_ : Ω) => Φm i) j ω| ≤ M0 := by
    intro j ω
    fin_cases j
    · simp only [hM0def]; simp
    · simp only [hM0def]; simp
  have hψ' : ∀ k j ω, |ψ k j ω| ≤ max Mψ 0 := fun k j ω => (hMψ k j ω).trans (le_max_left _ _)
  have hgeo : ∀ t : ℕ, ∑ k ∈ Finset.range (t + 1), ρ ^ (t - k) ≤ (1 - ρ)⁻¹ := by
    intro t
    have e : ∑ k ∈ Finset.range (t + 1), ρ ^ (t - k) = ∑ k ∈ Finset.range (t + 1), ρ ^ k := by
      have := Finset.sum_range_reflect (fun j => ρ ^ j) (t + 1)
      simpa using this
    rw [e, ← tsum_geometric_of_lt_one hρ0.le hρ1]
    exact (summable_geometric_of_lt_one hρ0.le hρ1).sum_le_tsum _
      (fun j _ => pow_nonneg hρ0.le j)
  refine ⟨2 * (Cb * M0) + 2 * (Cb * max Mψ 0) * (1 - ρ)⁻¹, fun t i ω => ?_⟩
  rw [backRec_closed, Pi.add_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
  have h1 : |rvMul (X ^ (t + 1)) (fun i _ => Φm i) i ω| ≤ 2 * (Cb * M0) := by
    have := abs_rvMul_pow_le hX (t + 1) hM0 i ω
    have hp : ρ ^ (t + 1) ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    have hc : Cb * ρ ^ (t + 1) * M0 ≤ Cb * M0 := by
      have := mul_le_mul_of_nonneg_left hp hCb
      nlinarith
    push_cast at this
    linarith
  have h2 : ∀ k ∈ Finset.range (t + 1),
      |rvMul (X ^ (t - k)) (ψ k) i ω| ≤ 2 * (Cb * max Mψ 0) * ρ ^ (t - k) := by
    intro k _
    have := abs_rvMul_pow_le hX (t - k) (hψ' k) i ω
    push_cast at this
    linarith
  have hC : 0 ≤ 2 * (Cb * max Mψ 0) := by positivity
  calc |rvMul (X ^ (t + 1)) (fun i _ => Φm i) i ω
        + ∑ k ∈ Finset.range (t + 1), rvMul (X ^ (t - k)) (ψ k) i ω|
      ≤ |rvMul (X ^ (t + 1)) (fun i _ => Φm i) i ω|
        + ∑ k ∈ Finset.range (t + 1), |rvMul (X ^ (t - k)) (ψ k) i ω| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ 2 * (Cb * M0) + ∑ k ∈ Finset.range (t + 1), 2 * (Cb * max Mψ 0) * ρ ^ (t - k) :=
        add_le_add h1 (Finset.sum_le_sum h2)
    _ ≤ 2 * (Cb * M0) + 2 * (Cb * max Mψ 0) * (1 - ρ)⁻¹ := by
        rw [← Finset.mul_sum]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hgeo t) hC)

/-- Woodford (2003), App. G.4 (tool): the backward recursion is adapted when `ψ` is. -/
theorem backRec_adapted (X : Matrix (Fin 2) (Fin 2) ℝ) (Φm : Fin 2 → ℝ)
    {ψ : ℕ → Fin 2 → Ω → ℝ} (hψ : VAdapted 𝔼 ψ) : VAdapted 𝔼 (backRec X Φm ψ) := by
  have h : ∀ t, (fun i => 𝔼.E t (backRec X Φm ψ t i)) = backRec X Φm ψ t := by
    intro t
    induction t with
    | zero =>
      funext i
      change 𝔼.E 0 ((rvMul X (fun i (_ : Ω) => Φm i) + ψ 0) i) =
        (rvMul X (fun i (_ : Ω) => Φm i) + ψ 0) i
      rw [Pi.add_apply, map_add, E_rvMul 𝔼, hψ 0 i]
      congr 2
      funext j
      exact 𝔼.const 0 (Φm j)
    | succ t ih =>
      funext i
      change 𝔼.E (t + 1) ((rvMul X (backRec X Φm ψ t) + ψ (t + 1)) i) =
        (rvMul X (backRec X Φm ψ t) + ψ (t + 1)) i
      rw [Pi.add_apply, map_add, E_rvMul 𝔼, hψ (t + 1) i]
      congr 2
      funext j
      exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (congrFun ih j)
  exact fun t i => congrFun (h t) i

/-- Woodford (2003), App. G.4 (tool): the lag of an adapted process is known one date ahead. -/
theorem lagV_known {Φm : Fin 2 → ℝ} {Φ : ℕ → Fin 2 → Ω → ℝ} (hΦ : VAdapted 𝔼 Φ) (t : ℕ)
    (j : Fin 2) : 𝔼.E t (lagV Φm Φ t j) = lagV Φm Φ t j := by
  cases t with
  | zero => exact 𝔼.const 0 (Φm j)
  | succ t => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hΦ t j)

/-- Woodford (2003), App. G.4 (tool): the lag of a bounded process is bounded. -/
theorem lagV_bounded (Φm : Fin 2 → ℝ) {Φ : ℕ → Fin 2 → Ω → ℝ} (hΦ : VBounded Φ) :
    VBounded (lagV Φm Φ) := by
  obtain ⟨M, hM⟩ := hΦ
  refine ⟨max M (|Φm 0| + |Φm 1|), fun t j ω => ?_⟩
  cases t with
  | zero =>
    refine le_trans ?_ (le_max_right _ _)
    fin_cases j
    · change |Φm 0| ≤ _
      linarith [abs_nonneg (Φm 1)]
    · change |Φm 1| ≤ _
      linarith [abs_nonneg (Φm 0)]
  | succ t => exact (hM t j ω).trans (le_max_left _ _)

/-- **Woodford (2003), §1.2 and App. G.4, pp. 721–722 — the Blanchard–Kahn theorem for a
second-order system, proved.** Suppose `X` is a real solvent of `PX² − A₁X + A₂ = 0` with both
eigenvalues in the open unit disc (the stable roots), `B = PX − A₁` is invertible and
`K = −B⁻¹P` has both eigenvalues in the open unit disc (the reciprocals of the unstable roots).
Then for every bounded adapted forcing `F` and every `Φ_{−1}` the system
`P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t` has exactly one bounded adapted solution:
`Φ_t = XΦ_{t−1} + ψ_t` with `ψ` the forward solution of `ψ_t = K E_tψ_{t+1} + B⁻¹F_t`. -/
theorem sys2_existsUnique {P A1 A2 X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : P * X * X - A1 * X + A2 = 0) (hXs : SchurStable (tr2 X) (det2 X))
    (hB : det2 (P * X - A1) ≠ 0)
    (hK : SchurStable (tr2 (-(inv2 (P * X - A1) * P))) (det2 (-(inv2 (P * X - A1) * P))))
    {F : ℕ → Fin 2 → Ω → ℝ} (hFb : VBounded F) (hFa : VAdapted 𝔼 F) (Φm : Fin 2 → ℝ) :
    ∃! Φ, Sys2 𝔼 P A1 A2 F Φm Φ ∧ VAdapted 𝔼 Φ ∧ VBounded Φ := by
  set B := P * X - A1 with hBdef
  set K := -(inv2 B * P) with hKdef
  set w : ℕ → Fin 2 → Ω → ℝ := fun t => rvMul (inv2 B) (F t) with hw
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hKb⟩ := pow_bound_of_schurStable hK
  have hwb : VBounded w := vBounded_rvMul (inv2 B) hFb
  have hwa : VAdapted 𝔼 w := vAdapted_rvMul 𝔼 (inv2 B) hFa
  obtain ⟨Mw, hMw⟩ := hwb
  have hpsiA : ∀ Φ : ℕ → Fin 2 → Ω → ℝ, VAdapted 𝔼 Φ → VAdapted 𝔼 (psiOf X Φm Φ) := by
    intro Φ hΦ t i
    simp only [psiOf, Pi.sub_apply, map_sub, E_rvMul 𝔼, hΦ t i]
    congr 2
    funext j
    exact lagV_known 𝔼 hΦ t j
  have hpsiB : ∀ Φ : ℕ → Fin 2 → Ω → ℝ, VBounded Φ → VBounded (psiOf X Φm Φ) := by
    intro Φ hΦ
    obtain ⟨M1, hM1⟩ := hΦ
    obtain ⟨M2, hM2⟩ := vBounded_rvMul X (lagV_bounded Φm ⟨M1, hM1⟩)
    refine ⟨M1 + M2, fun t i ω => ?_⟩
    simp only [psiOf, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM1 t i ω) (hM2 t i ω))
  have hsolves : ∀ Φ : ℕ → Fin 2 → Ω → ℝ, VAdapted 𝔼 Φ →
      (Sys2 𝔼 P A1 A2 F Φm Φ ↔ FSolves 𝔼 K w (psiOf X Φm Φ)) := fun Φ hΦ =>
    ⟨fun h t => (sys2_step_iff 𝔼 hX hB hΦ t).mp (h t),
      fun h t => (sys2_step_iff 𝔼 hX hB hΦ t).mpr (h t)⟩
  obtain ⟨ψ, hψs, hψa, hψb⟩ := fsolves_exists 𝔼 hρ0.le hρ1 hKb hMw hwa
  have hpsiΦ : psiOf X Φm (backRec X Φm ψ) = ψ := by
    funext t
    simp only [psiOf]
    rw [backRec_eq X Φm ψ t]
    abel
  have hΦa : VAdapted 𝔼 (backRec X Φm ψ) := backRec_adapted 𝔼 X Φm hψa
  refine ⟨backRec X Φm ψ, ⟨(hsolves _ hΦa).mpr (by rw [hpsiΦ]; exact hψs), hΦa,
    backRec_bounded hXs Φm hψb⟩, ?_⟩
  rintro Φ' ⟨hs', ha', hb'⟩
  have e : psiOf X Φm Φ' = ψ := fsolves_unique 𝔼 hρ0.le hρ1 hKb ((hsolves Φ' ha').mp hs') hψs
    (hpsiA Φ' ha') hψa (hpsiB Φ' hb') hψb
  funext t
  induction t with
  | zero =>
    have := congrFun e 0
    simp only [psiOf, lagV] at this
    rw [show backRec X Φm ψ 0 = rvMul X (fun i (_ : Ω) => Φm i) + ψ 0 from rfl, ← this]
    abel
  | succ t ih =>
    have := congrFun e (t + 1)
    simp only [psiOf, lagV] at this
    rw [show backRec X Φm ψ (t + 1) = rvMul X (backRec X Φm ψ t) + ψ (t + 1) from rfl, ← ih,
      ← this]
    abel

/-! ### The multiplier system of the model and its real solvent -/

/-- Woodford (2003), (3.3)–(3.5) and (G.10)–(G.11): the coupling coefficient `σ − κ/λ_x` of the
multiplier system. -/
noncomputable def cpG (σ κ lx : ℝ) : ℝ := σ - κ / lx

/-- Woodford (2003), (3.1) in multiplier form: the coefficient
`c₁ = 1 + β + βλ_xσ²/λ_i + λ_xσ²`. -/
noncomputable def c1G (β σ lx li : ℝ) : ℝ := 1 + β + β * lx * σ ^ 2 / li + lx * σ ^ 2

/-- Woodford (2003), (2.1) in multiplier form: the coefficient `c₂ = 1 + β + κ²/λ_x`. -/
noncomputable def c2G (β κ lx : ℝ) : ℝ := 1 + β + κ ^ 2 / lx

/-- Woodford (2003), (3.3)–(3.5) with (2.1), (3.1): the lead matrix `P = βA₀` of the
multiplier system `P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t`, `Φ = (φ₁, φ₂)`. -/
noncomputable def PmG (β σ κ lx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β, β * lx * cpG σ κ lx; 0, β]

/-- Woodford (2003), (3.3)–(3.5) with (2.1), (3.1): the matrix `A₁`. -/
noncomputable def A1G (β σ κ lx li : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c1G β σ lx li, β * lx * cpG σ κ lx; cpG σ κ lx, c2G β κ lx]

/-- Woodford (2003), (3.3)–(3.5) with (2.1), (3.1): the lag matrix `A₂`. -/
noncomputable def A2G (β σ κ lx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 0; cpG σ κ lx / β, 1]

/-- Woodford (2003), (G.11), p. 722: the characteristic matrix `M(µ) = µ²P − µA₁ + A₂` of the
multiplier system. -/
noncomputable def MphiG (β σ κ lx li μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  μ ^ 2 • PmG β σ κ lx - μ • A1G β σ κ lx li + A2G β σ κ lx

/-- **Woodford (2003), (G.11)–(G.12), p. 722**: the characteristic polynomial of the multiplier
system is `det M(µ) = β² p(µ)`. -/
theorem det_Mphi {β σ κ lx li : ℝ} (hβ : β ≠ 0) (hlx : lx ≠ 0) (hli : li ≠ 0) (μ : ℝ) :
    det2 (MphiG β σ κ lx li μ) = β ^ 2 * pR β σ κ lx li μ := by
  simp only [det2, MphiG, PmG, A1G, A2G, cpG, c1G, c2G, pR, aG, bG, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), App. G.4 (tool): `det(sP + N) = s² det P + s cross(P, N) + det N`. -/
noncomputable def cross2 (P N : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  P 0 0 * N 1 1 + P 1 1 * N 0 0 - P 0 1 * N 1 0 - P 1 0 * N 0 1

/-- Woodford (2003), App. G.4 (tool): expansion of a `2 × 2` determinant along a pencil. -/
theorem det2_smul_add (s : ℝ) (P N : Matrix (Fin 2) (Fin 2) ℝ) :
    det2 (s • P + N) = s ^ 2 * det2 P + s * cross2 P N + det2 N := by
  simp only [det2, cross2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), App. G.4 (tool): matching coefficients — if
`g₂µ² − g₁µ + g₀ = (µ² − Tµ + D)(l₁µ + l₀)` for all real `µ`, then `l₁ = 0`, `g₂ = l₀`,
`g₁ = T l₀` and `g₀ = D l₀`. -/
theorem coeff_match {g2 g1 g0 T D l1 l0 : ℝ}
    (h : ∀ μ : ℝ, g2 * μ ^ 2 - g1 * μ + g0 = (μ ^ 2 - T * μ + D) * (l1 * μ + l0)) :
    l1 = 0 ∧ g2 = l0 ∧ g1 = T * l0 ∧ g0 = D * l0 := by
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  have h2 := h 2
  have e1 : l1 = 0 := by linear_combination (-1 / 6 : ℝ) * (h2 - 3 * h1 + 3 * h0 - hm)
  subst e1
  refine ⟨rfl, ?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℝ) * (h1 + hm - 2 * h0)
  · linear_combination (-1 / 2 : ℝ) * (h1 - hm)
  · linear_combination h0

/-- Woodford (2003), App. G.4 (tool): the trace of `G⁻¹H` for `2 × 2` matrices. -/
theorem tr2_inv2_mul (G H : Matrix (Fin 2) (Fin 2) ℝ) :
    tr2 (inv2 G * H) = cross2 G H / det2 G := by
  simp only [tr2, inv2, cross2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), App. G.4 (tool): the determinant of `G⁻¹H`. -/
theorem det2_inv2_mul {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : det2 G ≠ 0)
    (H : Matrix (Fin 2) (Fin 2) ℝ) : det2 (inv2 G * H) = det2 H / det2 G := by
  have e : det2 (inv2 G * H) = det2 H * (det2 G * (det2 G)⁻¹ ^ 2) := by
    simp only [det2, inv2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    ring
  rw [e]
  field_simp

/-- Woodford (2003), App. G.4 (tool): `det(−M) = det M` for `2 × 2` matrices. -/
theorem det2_neg (M : Matrix (Fin 2) (Fin 2) ℝ) : det2 (-M) = det2 M := by
  simp only [det2, Matrix.neg_apply]
  ring

/-- Woodford (2003), App. G.4 (tool): `tr(−M) = −tr M`. -/
theorem tr2_neg (M : Matrix (Fin 2) (Fin 2) ℝ) : tr2 (-M) = -tr2 M := by
  simp only [tr2, Matrix.neg_apply]
  ring

/-- Woodford (2003), App. G.4 (tool): `det(µI − X) = µ² − (tr X)µ + det X`. -/
theorem det2_scalar_sub (μ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    det2 (μ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - X) = μ ^ 2 - tr2 X * μ + det2 X := by
  simp only [det2, tr2, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp
  ring

/-- Woodford (2003), App. G.4 (tool): `det(MN) = det M det N` for `2 × 2` matrices. -/
theorem det2_mul (M N : Matrix (Fin 2) (Fin 2) ℝ) : det2 (M * N) = det2 M * det2 N := by
  rw [det2_eq_det, det2_eq_det, det2_eq_det, Matrix.det_mul]

/-- Woodford (2003), App. G.4, p. 722: Schur stability is preserved when both roots are scaled
by `β ∈ (0, 1)`: `SchurStable T D → SchurStable (βT) (β²D)`. -/
theorem schurStable_scale {T D β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (h : SchurStable T D) :
    SchurStable (β * T) (β ^ 2 * D) := by
  obtain ⟨hD, hT⟩ := h
  rw [abs_lt] at hD
  have hb2 : β ^ 2 < 1 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [abs_lt]
    constructor <;> nlinarith
  · rw [abs_mul, abs_of_pos hβ0]
    have h1 : β * |T| < β * (1 + D) := mul_lt_mul_of_pos_left hT hβ0
    have h2 : 0 < 1 - β * D := by nlinarith [mul_pos hβ0 (sub_pos.mpr hD.2)]
    nlinarith [mul_pos (sub_pos.mpr hβ1) h2]

/-- **Woodford (2003), App. G.4: the real solvent.** If `µ² − Tµ + D` (Schur-stable, `D > 0`)
divides `p` as `p(µ) = (µ² − Tµ + D)(µ² − (T/(βD))µ + 1/(β²D))`, then
`X = (A₁ − TP)⁻¹(A₂ − DP)` solves `PX² − A₁X + A₂ = 0`, has trace `T` and determinant `D`, and
`B = PX − A₁` is invertible with `K = −B⁻¹P` having trace `βT` and determinant `β²D` (so its
eigenvalues `βµ_k = 1/µ_k'` are the reciprocals of the unstable roots). -/
theorem solvent_eq {β σ κ lx li T D : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hlx : 0 < lx)
    (hli : 0 < li) (hTD : SchurStable T D) (hD : 0 < D)
    (hfac : ∀ μ : ℝ, pR β σ κ lx li μ =
      (μ ^ 2 - T * μ + D) * (μ ^ 2 - T / (β * D) * μ + 1 / (β ^ 2 * D))) :
    let G := A1G β σ κ lx li - T • PmG β σ κ lx
    let H := A2G β σ κ lx - D • PmG β σ κ lx
    let X := inv2 G * H
    let B := PmG β σ κ lx * X - A1G β σ κ lx li
    det2 G ≠ 0 ∧ PmG β σ κ lx * X * X - A1G β σ κ lx li * X + A2G β σ κ lx = 0 ∧
      tr2 X = T ∧ det2 X = D ∧ det2 B ≠ 0 ∧
      tr2 (-(inv2 B * PmG β σ κ lx)) = β * T ∧ det2 (-(inv2 B * PmG β σ κ lx)) = β ^ 2 * D := by
  intro G H X B
  set P := PmG β σ κ lx with hP
  set A1 := A1G β σ κ lx li with hA1
  set A2 := A2G β σ κ lx with hA2
  have hβ : β ≠ 0 := hβ0.ne'
  -- the determinant of `H` is positive
  have hdetH : det2 H = (1 - β * D) ^ 2 + D * lx * cpG σ κ lx ^ 2 := by
    simp only [H, det2, PmG, A2G, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
    field_simp
    ring
  have hHpos : 0 < det2 H := by
    rw [hdetH]
    have : 0 < (1 - β * D) ^ 2 := by
      obtain ⟨hD1, -⟩ := hTD
      rw [abs_lt] at hD1
      have : β * D < 1 := by nlinarith
      positivity
    positivity
  -- the pencil identity `M(µ) = P_in(µ) P + (H − µG)`
  have hM : ∀ μ : ℝ, MphiG β σ κ lx li μ = (μ ^ 2 - T * μ + D) • P + (H - μ • G) := by
    intro μ
    simp only [MphiG, H, G, ← hP, ← hA1, ← hA2]
    module
  have hpoly : ∀ μ : ℝ, det2 G * μ ^ 2 - cross2 G H * μ + det2 H =
      (μ ^ 2 - T * μ + D) * ((β ^ 2 * (T - T / (β * D)) + cross2 P G) * μ
        + (β ^ 2 * (1 / (β ^ 2 * D) - D) - cross2 P H)) := by
    intro μ
    have e1 := det_Mphi (σ := σ) (κ := κ) hβ hlx.ne' hli.ne' μ
    rw [hM μ, det2_smul_add, hfac μ] at e1
    have e2 : det2 (H - μ • G) = det2 G * μ ^ 2 - cross2 G H * μ + det2 H := by
      simp only [det2, cross2, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have e3 : cross2 P (H - μ • G) = cross2 P H - μ * cross2 P G := by
      simp only [cross2, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have e4 : det2 P = β ^ 2 := by
      simp only [hP, det2, PmG, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      ring
    rw [e2, e3, e4] at e1
    linear_combination e1
  obtain ⟨-, hg2, hg1, hg0⟩ := coeff_match hpoly
  have hG : det2 G ≠ 0 := by
    intro h0
    rw [h0] at hg2
    rw [← hg2, mul_zero] at hg0
    linarith
  have htrX : tr2 X = T := by
    simp only [X]
    rw [tr2_inv2_mul, hg1, ← hg2]
    field_simp
  have hdetX : det2 X = D := by
    simp only [X]
    rw [det2_inv2_mul hG, hg0, ← hg2]
    field_simp
  have hsolv : P * X * X - A1 * X + A2 = 0 := by
    have hCH := sq_eq_cayleyHamilton X
    rw [htrX, hdetX, sq] at hCH
    have hGX : G * X = H := by
      simp only [X]
      rw [← mul_assoc, mul_inv2 hG, one_mul]
    have hGX' : A1 * X - T • (P * X) = A2 - D • P := by
      have hG' : G = A1 - T • P := rfl
      have hH' : H = A2 - D • P := rfl
      rw [hG', hH', sub_mul, smul_mul_assoc] at hGX
      exact hGX
    rw [mul_assoc, hCH, mul_sub, mul_smul_comm, mul_smul_comm, mul_one,
      show A1 * X = A2 - D • P + T • (P * X) by rw [← hGX']; abel]
    abel
  refine ⟨hG, hsolv, htrX, hdetX, ?_⟩
  -- the factorisation `M(µ) = (µP + B)(µI − X)`
  have hBX : B * X = -A2 := by
    simp only [B]
    rw [sub_mul]
    exact eq_neg_of_add_eq_zero_left hsolv
  have hfact : ∀ μ : ℝ, MphiG β σ κ lx li μ =
      (μ • P + B) * (μ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - X) := by
    intro μ
    have hB' : B = P * X - A1 := rfl
    rw [add_mul, mul_sub, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, smul_mul_assoc,
      mul_smul_comm, mul_one, hBX, hB', smul_smul, ← sq]
    simp only [MphiG, ← hP, ← hA1, ← hA2, smul_sub]
    abel
  have hdet : ∀ μ : ℝ, det2 (μ • P + B) * (μ ^ 2 - T * μ + D) =
      β ^ 2 * ((μ ^ 2 - T * μ + D) * (μ ^ 2 - T / (β * D) * μ + 1 / (β ^ 2 * D))) := by
    intro μ
    have := det_Mphi (σ := σ) (κ := κ) hβ hlx.ne' hli.ne' μ
    rw [hfact μ, det2_mul, det2_scalar_sub, htrX, hdetX, hfac μ] at this
    exact this
  have e4 : det2 P = β ^ 2 := by
    simp only [hP, det2, PmG, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  obtain ⟨hD1, hT1⟩ := hTD
  rw [abs_lt] at hD1 hT1
  have hp1 : 0 < 1 - T + D := by linarith
  have hpm1 : 0 < 1 + T + D := by linarith
  have q1 := hdet 1
  have qm1 := hdet (-1)
  rw [det2_smul_add, e4] at q1 qm1
  have q1' : β ^ 2 + cross2 P B + det2 B =
      β ^ 2 * (1 - T / (β * D) + 1 / (β ^ 2 * D)) := by
    have h : (1 : ℝ) ^ 2 - T * 1 + D ≠ 0 := by nlinarith
    apply mul_right_cancel₀ h
    linear_combination q1
  have qm1' : β ^ 2 - cross2 P B + det2 B =
      β ^ 2 * (1 + T / (β * D) + 1 / (β ^ 2 * D)) := by
    have h : (-1 : ℝ) ^ 2 - T * (-1) + D ≠ 0 := by nlinarith
    apply mul_right_cancel₀ h
    linear_combination qm1
  have hdetB : det2 B = 1 / D := by
    have : det2 B = β ^ 2 * (1 / (β ^ 2 * D)) := by linear_combination (q1' + qm1') / 2
    rw [this]
    field_simp
  have hcrossB : cross2 P B = -(T / D) / β * β ^ 2 := by
    have : cross2 P B = -(β ^ 2 * (T / (β * D))) := by linear_combination (q1' - qm1') / 2
    rw [this]
    field_simp
  have hB0 : det2 B ≠ 0 := by rw [hdetB]; positivity
  refine ⟨hB0, ?_, ?_⟩
  · rw [tr2_neg, tr2_inv2_mul]
    have hc : cross2 B P = cross2 P B := by simp only [cross2]; ring
    rw [hc, hcrossB, hdetB]
    field_simp
  · rw [det2_neg, det2_inv2_mul hB0, e4, hdetB]
    field_simp

/-! ### The model (2.1), (3.1), the rule (3.7)–(3.9) and the first-order conditions (3.3)–(3.5) -/

/-- Woodford (2003), §3.1, pp. 583–584, Table 6.1: the parameters `β, σ, κ` of (2.1), (3.1), the
loss weights `λ_x, λ_i` of (3.2) and the targets `x*, i*`. -/
structure Calib where
  /-- the discount factor -/
  β : ℝ
  /-- the intertemporal elasticity of substitution -/
  σ : ℝ
  /-- the slope of the aggregate-supply relation -/
  κ : ℝ
  /-- the weight on the output gap -/
  lx : ℝ
  /-- the weight on the interest rate -/
  li : ℝ
  /-- the output-gap target -/
  xstar : ℝ
  /-- the interest-rate target -/
  istar : ℝ

/-- Woodford (2003), §3.1, p. 584: the admissible parameters, `0 < β < 1`, `σ, κ, λ_x, λ_i > 0`. -/
def Calib.Adm (c : Calib) : Prop :=
  0 < c.β ∧ c.β < 1 ∧ 0 < c.σ ∧ 0 < c.κ ∧ 0 < c.lx ∧ 0 < c.li

/-- Woodford (2003), (3.8), p. 584: `ρ₁ = 1 + κσ/β`. -/
noncomputable def rho1 (β σ κ : ℝ) : ℝ := 1 + κ * σ / β

/-- Woodford (2003), (3.8), p. 584: `ρ₂ = β⁻¹`. -/
noncomputable def rho2 (β : ℝ) : ℝ := β⁻¹

/-- Woodford (2003), (3.9), p. 584: `φ_π = κσ/λ_i`. -/
noncomputable def phiPi (σ κ li : ℝ) : ℝ := κ * σ / li

/-- Woodford (2003), (3.9), p. 584: `φ_x = 4σλ_x/λ_i`. -/
noncomputable def phiX (σ lx li : ℝ) : ℝ := 4 * σ * lx / li

/-- Woodford (2003), (3.8)–(3.9), p. 584: `ρ₁ > 1`, `ρ₂ > 1`, `φ_π > 0`, `φ_x > 0`. -/
theorem coef_signs {β σ κ lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hlx : 0 < lx) (hli : 0 < li) :
    1 < rho1 β σ κ ∧ 1 < rho2 β ∧ 0 < phiPi σ κ li ∧ 0 < phiX σ lx li := by
  refine ⟨?_, ?_, by unfold phiPi; positivity, by unfold phiX; positivity⟩
  · unfold rho1
    have : 0 < κ * σ / β := by positivity
    linarith
  · unfold rho2
    exact one_lt_inv₀ hβ0 |>.mpr hβ1

/-- Woodford (2003), (3.6)–(3.7), p. 584: a scalar process lagged once, with the pre-sample value
`z_{−1} = z₀`. -/
def lag (z0 : ℝ) (z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => z0
  | t + 1 => z t

/-- Woodford (2003), (2.1), p. 560: `π_t = κx_t + βE_tπ_{t+1} + u_t`. -/
def AS (c : Calib) (u π x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  π t = c.κ • x t + c.β • 𝔼.E t (π (t + 1)) + u t

/-- Woodford (2003), (3.1), p. 583: `x_t = E_t x_{t+1} − σ(i_t − E_tπ_{t+1} − rⁿ_t)`. -/
def IS (c : Calib) (rn π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  x t = 𝔼.E t (x (t + 1)) - c.σ • (i t - 𝔼.E t (π (t + 1)) - rn t)

/-- Woodford (2003), (3.7), p. 584: the implicit instrument rule
`i_t = (1 − ρ₁)i* + ρ₁i_{t−1} + ρ₂Δi_{t−1} + φ_ππ_t + φ_xΔx_t/4`, with the history
`x_{−1}, i_{−1}, i_{−2}`. -/
def Rule (c : Calib) (xm1 im1 im2 : ℝ) (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t = (fun _ => (1 - rho1 c.β c.σ c.κ) * c.istar) + rho1 c.β c.σ c.κ • lag im1 i t
    + rho2 c.β • (lag im1 i t - lag im2 (lag im1 i) t) + phiPi c.σ c.κ c.li • π t
    + (phiX c.σ c.lx c.li / 4) • (x t - lag xm1 x t)

/-- Woodford (2003), (2.1), (3.1), (3.7), p. 584: a rational-expectations equilibrium under the
rule, from date `t₀ = 0` with history `x_{−1}, i_{−1}, i_{−2}`. -/
def RuleEqm (c : Calib) (rn u : ℕ → Ω → ℝ) (xm1 im1 im2 : ℝ) (π x i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, AS 𝔼 c u π x t ∧ IS 𝔼 c rn π x i t ∧ Rule c xm1 im1 im2 π x i t

/-- Woodford (2003), (3.3), p. 584: `π_t − β⁻¹σφ_{1,t−1} + φ_{2t} − φ_{2,t−1} = 0`. -/
def FOC3 (c : Calib) (π φ1 φ2 : ℕ → Ω → ℝ) (φ1h φ2h : ℝ) (t : ℕ) : Prop :=
  π t - (c.σ / c.β) • lag φ1h φ1 t + φ2 t - lag φ2h φ2 t = 0

/-- Woodford (2003), (3.4), p. 584: `λ_x(x_t − x*) + φ_{1t} − β⁻¹φ_{1,t−1} − κφ_{2t} = 0`. -/
def FOC4 (c : Calib) (x φ1 φ2 : ℕ → Ω → ℝ) (φ1h : ℝ) (t : ℕ) : Prop :=
  c.lx • (x t - fun _ => c.xstar) + φ1 t - c.β⁻¹ • lag φ1h φ1 t - c.κ • φ2 t = 0

/-- Woodford (2003), (3.5), p. 584: `λ_i(i_t − i*) + σφ_{1t} = 0`. -/
def FOC5 (c : Calib) (i φ1 : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  c.li • (i t - fun _ => c.istar) + c.σ • φ1 t = 0

/-- Woodford (2003), p. 584 ("employing (3.5) to solve for φ₁"): `φ_{1t} = −(λ_i/σ)(i_t − i*)`. -/
noncomputable def mult1 (c : Calib) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (-(c.li / c.σ)) • (i t - fun _ => c.istar)

/-- Woodford (2003), p. 584: the pre-sample multiplier `φ_{1,s} = −(λ_i/σ)(i_s − i*)`, `s < 0`. -/
noncomputable def mult1h (c : Calib) (ih : ℝ) : ℝ := -(c.li / c.σ) * (ih - c.istar)

/-- Woodford (2003), p. 584 ("resorting to (3.4) to solve for φ₂"):
`φ_{2t} = κ⁻¹(λ_x(x_t − x*) + φ_{1t} − β⁻¹φ_{1,t−1})`. -/
noncomputable def mult2 (c : Calib) (im1 : ℝ) (x i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => c.κ⁻¹ • (c.lx • (x t - fun _ => c.xstar) + mult1 c i t
    - c.β⁻¹ • lag (mult1h c im1) (mult1 c i) t)

/-- Woodford (2003), p. 585: the initial multiplier `φ_{2,−1}` inferred from the history
`x_{−1}, i_{−1}, i_{−2}`. -/
noncomputable def mult2h (c : Calib) (xm1 im1 im2 : ℝ) : ℝ :=
  c.κ⁻¹ * (c.lx * (xm1 - c.xstar) + mult1h c im1 - c.β⁻¹ * mult1h c im2)

/-- Woodford (2003), p. 584 (tool): the lagged first multiplier. -/
theorem lag_mult1 (c : Calib) (im1 : ℝ) (i : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    lag (mult1h c im1) (mult1 c i) t ω = -(c.li / c.σ) * (lag im1 i t ω - c.istar) := by
  cases t with
  | zero => rfl
  | succ t => simp [lag, mult1, smul_eq_mul]

/-- Woodford (2003), p. 584 (tool): the lagged second multiplier. -/
theorem lag_mult2 (c : Calib) (xm1 im1 im2 : ℝ) (x i : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    lag (mult2h c xm1 im1 im2) (mult2 c im1 x i) t ω =
      c.κ⁻¹ * (c.lx * (lag xm1 x t ω - c.xstar) + -(c.li / c.σ) * (lag im1 i t ω - c.istar)
        - c.β⁻¹ * (-(c.li / c.σ) * (lag im2 (lag im1 i) t ω - c.istar))) := by
  cases t with
  | zero => rfl
  | succ t =>
    change mult2 c im1 x i t ω = _
    simp only [mult2, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    rw [lag_mult1]
    simp [lag, mult1, smul_eq_mul]

/-- Woodford (2003), (3.7)–(3.9), p. 584 (the elimination, real form): the rule holds iff (3.3)
holds after substituting the multipliers from (3.4)–(3.5). -/
theorem rule_foc3_real (c : Calib) (hβ : c.β ≠ 0) (hσ : c.σ ≠ 0) (hκ : c.κ ≠ 0)
    (hli : c.li ≠ 0) (p x i L1 L2 Lx : ℝ) :
    i = (1 - rho1 c.β c.σ c.κ) * c.istar + rho1 c.β c.σ c.κ * L1 + rho2 c.β * (L1 - L2)
        + phiPi c.σ c.κ c.li * p + phiX c.σ c.lx c.li / 4 * (x - Lx) ↔
      p - c.σ / c.β * (-(c.li / c.σ) * (L1 - c.istar))
        + c.κ⁻¹ * (c.lx * (x - c.xstar) + -(c.li / c.σ) * (i - c.istar)
          - c.β⁻¹ * (-(c.li / c.σ) * (L1 - c.istar)))
        - c.κ⁻¹ * (c.lx * (Lx - c.xstar) + -(c.li / c.σ) * (L1 - c.istar)
          - c.β⁻¹ * (-(c.li / c.σ) * (L2 - c.istar))) = 0 := by
  have key : p - c.σ / c.β * (-(c.li / c.σ) * (L1 - c.istar))
        + c.κ⁻¹ * (c.lx * (x - c.xstar) + -(c.li / c.σ) * (i - c.istar)
          - c.β⁻¹ * (-(c.li / c.σ) * (L1 - c.istar)))
        - c.κ⁻¹ * (c.lx * (Lx - c.xstar) + -(c.li / c.σ) * (L1 - c.istar)
          - c.β⁻¹ * (-(c.li / c.σ) * (L2 - c.istar))) =
      c.li / (c.κ * c.σ) * ((1 - rho1 c.β c.σ c.κ) * c.istar + rho1 c.β c.σ c.κ * L1
        + rho2 c.β * (L1 - L2) + phiPi c.σ c.κ c.li * p + phiX c.σ c.lx c.li / 4 * (x - Lx)
        - i) := by
    unfold rho1 rho2 phiPi phiX
    field_simp
    ring
  rw [key]
  have hk : c.li / (c.κ * c.σ) ≠ 0 := div_ne_zero hli (mul_ne_zero hκ hσ)
  constructor
  · intro h
    rw [← h]
    ring
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hk
    · linarith

/-- **Woodford (2003), (3.7)–(3.9), p. 584: the elimination of the multipliers.** With the
multipliers read off (3.4)–(3.5) (and the pre-sample ones from the history), the instrument rule
(3.7) with coefficients (3.8)–(3.9) holds at date `t` iff the first-order condition (3.3) does. -/
theorem rule_iff_foc3 (c : Calib) (hβ : c.β ≠ 0) (hσ : c.σ ≠ 0) (hκ : c.κ ≠ 0)
    (hli : c.li ≠ 0) (xm1 im1 im2 : ℝ) (π x i : ℕ → Ω → ℝ) (t : ℕ) :
    Rule c xm1 im1 im2 π x i t ↔
      FOC3 c π (mult1 c i) (mult2 c im1 x i) (mult1h c im1) (mult2h c xm1 im1 im2) t := by
  unfold Rule FOC3
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [lag_mult1, lag_mult2]
  simp only [mult2, mult1, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  rw [lag_mult1]
  exact rule_foc3_real c hβ hσ hκ hli _ _ _ _ _ _

/-- Woodford (2003), (3.5), p. 584: the multiplier `φ₁` read off (3.5) satisfies (3.5). -/
theorem foc5_mult (c : Calib) (hσ : c.σ ≠ 0) (i : ℕ → Ω → ℝ) (t : ℕ) :
    FOC5 c i (mult1 c i) t := by
  unfold FOC5 mult1
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

/-- Woodford (2003), (3.4), p. 584: the multiplier `φ₂` read off (3.4) satisfies (3.4). -/
theorem foc4_mult (c : Calib) (hκ : c.κ ≠ 0) (im1 : ℝ) (x i : ℕ → Ω → ℝ) (t : ℕ) :
    FOC4 c x (mult1 c i) (mult2 c im1 x i) (mult1h c im1) t := by
  unfold FOC4 mult2
  funext ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
  field_simp
  ring

/-! ### The multiplier system and the one-to-one correspondence with rule equilibria -/

/-- Woodford (2003), (2.1), (3.1), (3.3)–(3.5) (real form of the substitution): with
`π_t = β⁻¹σφ_{1,t−1} − φ_{2t} + φ_{2,t−1}`, `x_t − x* = λ_x⁻¹(κφ_{2t} − φ_{1t} + β⁻¹φ_{1,t−1})`,
`i_t − i* = −(σ/λ_i)φ_{1t}` (and the same one date ahead in expectation), (2.1) is the second
row and (3.1) the first row of the multiplier system. -/
theorem rows_real (c : Calib) (hβ : c.β ≠ 0) (hlx : c.lx ≠ 0) (hli : c.li ≠ 0)
    {a1 a2 f1 f2 e1 e2 p x i ep ex u rn : ℝ}
    (hp : p = c.σ / c.β * a1 - f2 + a2) (hep : ep = c.σ / c.β * f1 - e2 + f2)
    (hx : x = c.xstar + c.lx⁻¹ * (c.κ * f2 - f1 + c.β⁻¹ * a1))
    (hex : ex = c.xstar + c.lx⁻¹ * (c.κ * e2 - e1 + c.β⁻¹ * f1))
    (hi : i = c.istar - c.σ / c.li * f1) :
    (p = c.κ * x + c.β * ep + u ↔
      c.β * e2 - cpG c.σ c.κ c.lx * f1 - c2G c.β c.κ c.lx * f2 + cpG c.σ c.κ c.lx / c.β * a1
        + a2 = u + c.κ * c.xstar) ∧
    (x = ex - c.σ * (i - ep - rn) ↔
      c.β * e1 + c.β * c.lx * cpG c.σ c.κ c.lx * e2 - c1G c.β c.σ c.lx c.li * f1
        - c.β * c.lx * cpG c.σ c.κ c.lx * f2 + a1 = c.β * c.lx * c.σ * (rn - c.istar)) := by
  subst hp hep hx hex hi
  unfold cpG c1G c2G
  have hbl : c.β * c.lx ≠ 0 := mul_ne_zero hβ hlx
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · linear_combination (norm := (field_simp; ring)) h
  · linear_combination (norm := (field_simp; ring)) h
  · linear_combination (norm := (field_simp; ring)) (c.β * c.lx) * h
  · linear_combination (norm := (field_simp; ring)) (1 / (c.β * c.lx)) * h

/-- Woodford (2003), p. 584: the multipliers of a plan, `Φ_t = (φ_{1t}, φ_{2t})`. -/
noncomputable def PhiOf (c : Calib) (im1 : ℝ) (x i : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![mult1 c i t, mult2 c im1 x i t]

/-- Woodford (2003), p. 585: the initial multipliers `Φ_{−1}` inferred from the history. -/
noncomputable def PhiH (c : Calib) (xm1 im1 im2 : ℝ) : Fin 2 → ℝ :=
  ![mult1h c im1, mult2h c xm1 im1 im2]

/-- Woodford (2003), (2.1), (3.1): the forcing of the multiplier system,
`F_t = (βλ_xσ(rⁿ_t − i*), u_t + κx*)`. -/
noncomputable def Fphi (c : Calib) (rn u : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![(c.β * c.lx * c.σ) • (rn t - fun _ => c.istar), u t + fun _ => c.κ * c.xstar]

/-- Woodford (2003), (3.3): inflation from the multipliers. -/
noncomputable def piOf (c : Calib) (Φh : Fin 2 → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (c.σ / c.β) • lagV Φh Φ t 0 - Φ t 1 + lagV Φh Φ t 1

/-- Woodford (2003), (3.4): the output gap from the multipliers. -/
noncomputable def xOf (c : Calib) (Φh : Fin 2 → ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => c.xstar) + c.lx⁻¹ • (c.κ • Φ t 1 - Φ t 0 + c.β⁻¹ • lagV Φh Φ t 0)

/-- Woodford (2003), (3.5): the interest rate from the multipliers. -/
noncomputable def iOf (c : Calib) (Φ : ℕ → Fin 2 → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => c.istar) - (c.σ / c.li) • Φ t 0

/-- Woodford (2003), p. 584 (tool): the lagged multipliers of a plan. -/
theorem lagV_PhiOf (c : Calib) (xm1 im1 im2 : ℝ) (x i : ℕ → Ω → ℝ) (t : ℕ) :
    lagV (PhiH c xm1 im1 im2) (PhiOf c im1 x i) t 0 = lag (mult1h c im1) (mult1 c i) t ∧
      lagV (PhiH c xm1 im1 im2) (PhiOf c im1 x i) t 1 =
        lag (mult2h c xm1 im1 im2) (mult2 c im1 x i) t := by
  cases t <;> exact ⟨rfl, rfl⟩

/-- Woodford (2003), p. 584 (tool): a lag of an adapted process is known at each date. -/
theorem lag_known (z0 : ℝ) {z : ℕ → Ω → ℝ} (hz : 𝔼.Adapted z) (t : ℕ) :
    𝔼.E t (lag z0 z t) = lag z0 z t := by
  cases t with
  | zero => exact 𝔼.const 0 z0
  | succ t => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hz t)

/-- Woodford (2003), p. 584: the multiplier `φ₁` of an adapted plan is adapted. -/
theorem mult1_adapted (c : Calib) {i : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) :
    𝔼.Adapted (mult1 c i) := by
  intro t
  simp only [mult1, map_smul, map_sub, hi t, 𝔼.const]

/-- Woodford (2003), p. 584: the multiplier `φ₂` of an adapted plan is adapted. -/
theorem mult2_adapted (c : Calib) (im1 : ℝ) {x i : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (hi : 𝔼.Adapted i) : 𝔼.Adapted (mult2 c im1 x i) := by
  intro t
  simp only [mult2, map_smul, map_sub, map_add, hx t, 𝔼.const, mult1_adapted 𝔼 c hi t,
    lag_known 𝔼 _ (mult1_adapted 𝔼 c hi) t]

/-- Woodford (2003), p. 584: the multipliers of an adapted plan form an adapted vector. -/
theorem PhiOf_adapted (c : Calib) (im1 : ℝ) {x i : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (hi : 𝔼.Adapted i) : VAdapted 𝔼 (PhiOf c im1 x i) := by
  intro t j
  fin_cases j
  · exact mult1_adapted 𝔼 c hi t
  · exact mult2_adapted 𝔼 c im1 hx hi t

/-- Woodford (2003), (2.1), (3.1): the forcing of the multiplier system is adapted. -/
theorem Fphi_adapted (c : Calib) {rn u : ℕ → Ω → ℝ} (hr : 𝔼.Adapted rn) (hu : 𝔼.Adapted u) :
    VAdapted 𝔼 (Fphi c rn u) := by
  intro t j
  fin_cases j
  · simp [Fphi, map_smul, map_sub, hr t, 𝔼.const]
  · simp [Fphi, map_add, hu t, 𝔼.const]

/-- Woodford (2003), (2.1), (3.1): the forcing of the multiplier system is bounded. -/
theorem Fphi_bounded (c : Calib) {rn u : ℕ → Ω → ℝ} (hr : BoundedProc rn)
    (hu : BoundedProc u) : VBounded (Fphi c rn u) := by
  obtain ⟨Mr, hMr⟩ := hr
  obtain ⟨Mu, hMu⟩ := hu
  refine ⟨|c.β * c.lx * c.σ| * (Mr + |c.istar|) + (Mu + |c.κ * c.xstar|), fun t j ω => ?_⟩
  have h1 : |(c.β * c.lx * c.σ) * (rn t ω - c.istar)| ≤ |c.β * c.lx * c.σ| * (Mr + |c.istar|) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMr t ω) le_rfl))
      (abs_nonneg _)
  have h2 : |u t ω + c.κ * c.xstar| ≤ Mu + |c.κ * c.xstar| :=
    (abs_add_le _ _).trans (add_le_add (hMu t ω) le_rfl)
  have h1' : 0 ≤ |c.β * c.lx * c.σ| * (Mr + |c.istar|) := (abs_nonneg _).trans h1
  have h2' : 0 ≤ Mu + |c.κ * c.xstar| := (abs_nonneg _).trans h2
  fin_cases j
  · simp only [Fphi]
    simp only [Fin.zero_eta, Matrix.cons_val_zero, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  · simp only [Fphi]
    simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.add_apply]
    linarith

/-- Woodford (2003), p. 584 (tool): unfolding the entries of the multiplier system. -/
theorem sys_row (P A1 A2 : Matrix (Fin 2) (Fin 2) ℝ) (v w z : Fin 2 → Ω → ℝ) (j : Fin 2)
    (ω : Ω) : (rvMul P v - rvMul A1 w + rvMul A2 z) j ω =
      P j 0 * v 0 ω + P j 1 * v 1 ω - (A1 j 0 * w 0 ω + A1 j 1 * w 1 ω)
        + (A2 j 0 * z 0 ω + A2 j 1 * z 1 ω) := by
  simp only [Pi.add_apply, Pi.sub_apply, rvMul_two]

/-- **Woodford (2003), (3.3)–(3.5), pp. 584–585: from the rule to the multiplier system.** The
multipliers `Φ_t = (φ_{1t}, φ_{2t})` of a rule equilibrium (read off (3.4)–(3.5), with `Φ_{−1}`
inferred from the history) solve `P E_tΦ_{t+1} − A₁Φ_t + A₂Φ_{t−1} = F_t`. -/
theorem sys_of_eqm (c : Calib) (hc : c.Adm) {rn u π x i : ℕ → Ω → ℝ} {xm1 im1 im2 : ℝ}
    (he : RuleEqm 𝔼 c rn u xm1 im1 im2 π x i) (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i) :
    Sys2 𝔼 (PmG c.β c.σ c.κ c.lx) (A1G c.β c.σ c.κ c.lx c.li) (A2G c.β c.σ c.κ c.lx)
      (Fphi c rn u) (PhiH c xm1 im1 im2) (PhiOf c im1 x i) := by
  obtain ⟨hβ0, -, hσ, hκ, hlx, hli⟩ := hc
  have hfoc : ∀ s, FOC3 c π (mult1 c i) (mult2 c im1 x i) (mult1h c im1)
      (mult2h c xm1 im1 im2) s :=
    fun s => (rule_iff_foc3 c hβ0.ne' hσ.ne' hκ.ne' hli.ne' xm1 im1 im2 π x i s).mp (he s).2.2
  have hm1a := mult1_adapted 𝔼 c hia
  have hm2a := mult2_adapted 𝔼 c im1 hxa hia
  intro t
  obtain ⟨hl0, hl1⟩ := lagV_PhiOf c xm1 im1 im2 x i t
  funext j ω
  have hp : π t ω = c.σ / c.β * lag (mult1h c im1) (mult1 c i) t ω - mult2 c im1 x i t ω
      + lag (mult2h c xm1 im1 im2) (mult2 c im1 x i) t ω := by
    have := congrFun (hfoc t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    linarith
  have hep : 𝔼.E t (π (t + 1)) ω =
      c.σ / c.β * mult1 c i t ω - 𝔼.E t (mult2 c im1 x i (t + 1)) ω + mult2 c im1 x i t ω := by
    have h := congrArg (𝔼.E t) (hfoc (t + 1))
    rw [map_zero] at h
    have := congrFun h ω
    simp only [lag, map_add, map_sub, map_smul, hm1a t, hm2a t, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linarith
  have hx : x t ω = c.xstar + c.lx⁻¹ * (c.κ * mult2 c im1 x i t ω - mult1 c i t ω
      + c.β⁻¹ * lag (mult1h c im1) (mult1 c i) t ω) := by
    have := congrFun (foc4_mult c hκ.ne' im1 x i t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    have e : c.lx * (x t ω - c.xstar) = c.κ * mult2 c im1 x i t ω - mult1 c i t ω
        + c.β⁻¹ * lag (mult1h c im1) (mult1 c i) t ω := by linarith
    rw [← e]
    field_simp
    ring
  have hex : 𝔼.E t (x (t + 1)) ω = c.xstar + c.lx⁻¹ * (c.κ * 𝔼.E t (mult2 c im1 x i (t + 1)) ω
      - 𝔼.E t (mult1 c i (t + 1)) ω + c.β⁻¹ * mult1 c i t ω) := by
    have h := congrArg (𝔼.E t) (foc4_mult c hκ.ne' im1 x i (t + 1))
    rw [map_zero] at h
    have := congrFun h ω
    simp only [lag, map_add, map_sub, map_smul, hm1a t, 𝔼.const, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    have e : c.lx * (𝔼.E t (x (t + 1)) ω - c.xstar) = c.κ * 𝔼.E t (mult2 c im1 x i (t + 1)) ω
        - 𝔼.E t (mult1 c i (t + 1)) ω + c.β⁻¹ * mult1 c i t ω := by linarith
    rw [← e]
    field_simp
    ring
  have hi : i t ω = c.istar - c.σ / c.li * mult1 c i t ω := by
    have := congrFun (foc5_mult c hσ.ne' i t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    have e : c.σ * mult1 c i t ω = -(c.li * (i t ω - c.istar)) := by linarith
    rw [div_mul_eq_mul_div, e]
    field_simp
    ring
  have r := rows_real c hβ0.ne' hlx.ne' hli.ne' (u := u t ω) (rn := rn t ω) hp hep hx hex hi
  have hAS : π t ω = c.κ * x t ω + c.β * 𝔼.E t (π (t + 1)) ω + u t ω := by
    have := congrFun (he t).1 ω
    simpa only [AS, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hIS : x t ω = 𝔼.E t (x (t + 1)) ω - c.σ * (i t ω - 𝔼.E t (π (t + 1)) ω - rn t ω) := by
    have := congrFun (he t).2.1 ω
    simpa only [IS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this
  rw [sys_row, hl0, hl1]
  fin_cases j
  · have := r.2.mp hIS
    simp only [PmG, A1G, A2G, Fphi, PhiOf, Matrix.of_apply, Matrix.cons_val', Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linarith
  · have := r.1.mp hAS
    simp only [PmG, A1G, A2G, Fphi, PhiOf, Matrix.of_apply, Matrix.cons_val', Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Pi.add_apply]
    linarith

/-- Woodford (2003), p. 584 (tool): the multiplier `φ₁` of the plan built from `Φ` is `Φ₀`. -/
theorem mult1_iOf (c : Calib) (hσ : c.σ ≠ 0) (hli : c.li ≠ 0) (Φ : ℕ → Fin 2 → Ω → ℝ)
    (t : ℕ) : mult1 c (iOf c Φ) t = Φ t 0 := by
  funext ω
  simp only [mult1, iOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), p. 584 (tool): the lagged `φ₁` of the plan built from `Φ`. -/
theorem lag_mult1_iOf (c : Calib) (hσ : c.σ ≠ 0) (hli : c.li ≠ 0) (xm1 im1 im2 : ℝ)
    (Φ : ℕ → Fin 2 → Ω → ℝ) (t : ℕ) :
    lag (mult1h c im1) (mult1 c (iOf c Φ)) t = lagV (PhiH c xm1 im1 im2) Φ t 0 := by
  cases t with
  | zero => rfl
  | succ t => exact mult1_iOf c hσ hli Φ t

/-- Woodford (2003), p. 584 (tool): the multiplier `φ₂` of the plan built from `Φ` is `Φ₁`. -/
theorem mult2_xOf (c : Calib) (hσ : c.σ ≠ 0) (hκ : c.κ ≠ 0) (hlx : c.lx ≠ 0) (hli : c.li ≠ 0)
    (xm1 im1 im2 : ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) (t : ℕ) :
    mult2 c im1 (xOf c (PhiH c xm1 im1 im2) Φ) (iOf c Φ) t = Φ t 1 := by
  have h1 := mult1_iOf c hσ hli Φ t
  have h2 := lag_mult1_iOf c hσ hli xm1 im1 im2 Φ t
  simp only [mult2]
  rw [h1, h2]
  funext ω
  simp only [xOf, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), p. 584 (tool): the lagged `φ₂` of the plan built from `Φ`. -/
theorem lag_mult2_xOf (c : Calib) (hσ : c.σ ≠ 0) (hκ : c.κ ≠ 0) (hlx : c.lx ≠ 0)
    (hli : c.li ≠ 0) (xm1 im1 im2 : ℝ) (Φ : ℕ → Fin 2 → Ω → ℝ) (t : ℕ) :
    lag (mult2h c xm1 im1 im2) (mult2 c im1 (xOf c (PhiH c xm1 im1 im2) Φ) (iOf c Φ)) t =
      lagV (PhiH c xm1 im1 im2) Φ t 1 := by
  cases t with
  | zero => rfl
  | succ t => exact mult2_xOf c hσ hκ hlx hli xm1 im1 im2 Φ t

/-- **Woodford (2003), (3.3)–(3.5), p. 585: from the multiplier system to the rule.** If `Φ` is an
adapted solution of the multiplier system with `Φ_{−1}` inferred from the history, the plan
`π_t = β⁻¹σφ_{1,t−1} − φ_{2t} + φ_{2,t−1}`, `x_t = x* + λ_x⁻¹(κφ_{2t} − φ_{1t} + β⁻¹φ_{1,t−1})`,
`i_t = i* − (σ/λ_i)φ_{1t}` is an equilibrium under the rule (3.7). -/
theorem eqm_of_sys (c : Calib) (hc : c.Adm) {rn u : ℕ → Ω → ℝ} {xm1 im1 im2 : ℝ}
    {Φ : ℕ → Fin 2 → Ω → ℝ}
    (hs : Sys2 𝔼 (PmG c.β c.σ c.κ c.lx) (A1G c.β c.σ c.κ c.lx c.li) (A2G c.β c.σ c.κ c.lx)
      (Fphi c rn u) (PhiH c xm1 im1 im2) Φ) (ha : VAdapted 𝔼 Φ) :
    RuleEqm 𝔼 c rn u xm1 im1 im2 (piOf c (PhiH c xm1 im1 im2) Φ)
      (xOf c (PhiH c xm1 im1 im2) Φ) (iOf c Φ) := by
  obtain ⟨hβ0, -, hσ, hκ, hlx, hli⟩ := hc
  set Φh := PhiH c xm1 im1 im2 with hΦh
  intro t
  -- the rule, through (3.3)
  have hrule : Rule c xm1 im1 im2 (piOf c Φh Φ) (xOf c Φh Φ) (iOf c Φ) t := by
    rw [rule_iff_foc3 c hβ0.ne' hσ.ne' hκ.ne' hli.ne']
    unfold FOC3
    rw [lag_mult1_iOf c hσ.ne' hli.ne' xm1 im1 im2 Φ t,
      lag_mult2_xOf c hσ.ne' hκ.ne' hlx.ne' hli.ne' xm1 im1 im2 Φ t,
      mult2_xOf c hσ.ne' hκ.ne' hlx.ne' hli.ne' xm1 im1 im2 Φ t]
    simp only [piOf]
    abel
  refine ⟨?_, ?_, hrule⟩
  all_goals
    have hrow := congrFun (hs t)
    have hl : lagV Φh Φ (t + 1) = Φ t := rfl
    funext ω
    have r := rows_real c hβ0.ne' hlx.ne' hli.ne' (u := u t ω) (rn := rn t ω)
      (a1 := lagV Φh Φ t 0 ω) (a2 := lagV Φh Φ t 1 ω) (f1 := Φ t 0 ω) (f2 := Φ t 1 ω)
      (e1 := 𝔼.E t (Φ (t + 1) 0) ω) (e2 := 𝔼.E t (Φ (t + 1) 1) ω)
      (p := piOf c Φh Φ t ω) (x := xOf c Φh Φ t ω) (i := iOf c Φ t ω)
      (ep := 𝔼.E t (piOf c Φh Φ (t + 1)) ω) (ex := 𝔼.E t (xOf c Φh Φ (t + 1)) ω)
      (by simp only [piOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
      (by simp only [piOf, hl, map_add, map_sub, map_smul, ha t 0, ha t 1, Pi.add_apply,
            Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
      (by simp only [xOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
      (by simp only [xOf, hl, map_add, map_sub, map_smul, ha t 0, 𝔼.const, Pi.add_apply,
            Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
      (by simp only [iOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
    have h0 := hrow 0
    have h1 := hrow 1
    rw [funext_iff] at h0 h1
    have h0 := h0 ω
    have h1 := h1 ω
    rw [sys_row] at h0 h1
    simp only [PmG, A1G, A2G, Fphi, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
      smul_eq_mul] at h0 h1
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact r.1.mpr (by linarith)
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact r.2.mpr (by linarith)

/-- Woodford (2003), p. 585: an equilibrium under the rule is recovered from its multipliers. -/
theorem eqm_roundtrip (c : Calib) (hc : c.Adm) {rn u π x i : ℕ → Ω → ℝ} {xm1 im1 im2 : ℝ}
    (he : RuleEqm 𝔼 c rn u xm1 im1 im2 π x i) :
    piOf c (PhiH c xm1 im1 im2) (PhiOf c im1 x i) = π ∧
      xOf c (PhiH c xm1 im1 im2) (PhiOf c im1 x i) = x ∧ iOf c (PhiOf c im1 x i) = i := by
  obtain ⟨hβ0, -, hσ, hκ, hlx, hli⟩ := hc
  refine ⟨?_, ?_, ?_⟩
  · funext t ω
    have hf := congrFun ((rule_iff_foc3 c hβ0.ne' hσ.ne' hκ.ne' hli.ne' xm1 im1 im2 π x i
      t).mp (he t).2.2) ω
    obtain ⟨hl0, hl1⟩ := lagV_PhiOf c xm1 im1 im2 x i t
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at hf
    simp only [piOf, hl0, hl1, PhiOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · funext t ω
    obtain ⟨hl0, -⟩ := lagV_PhiOf c xm1 im1 im2 x i t
    simp only [xOf, hl0, PhiOf, mult2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  · funext t ω
    simp only [iOf, PhiOf, mult1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero]
    field_simp
    ring

/-- Woodford (2003), p. 584 (tool): the multipliers of a bounded plan are bounded. -/
theorem PhiOf_bounded (c : Calib) (im1 : ℝ) {x i : ℕ → Ω → ℝ} (hx : BoundedProc x)
    (hi : BoundedProc i) : VBounded (PhiOf c im1 x i) := by
  obtain ⟨Mx, hMx⟩ := hx
  obtain ⟨Mi, hMi⟩ := hi
  set B1 := |c.li / c.σ| * (Mi + |c.istar|) with hB1
  have h1 : ∀ t ω, |mult1 c i t ω| ≤ B1 := by
    intro t ω
    simp only [mult1, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_neg, hB1]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMi t ω) le_rfl))
      (abs_nonneg _)
  set B1' := max B1 |mult1h c im1| with hB1'
  have hl1 : ∀ t ω, |lag (mult1h c im1) (mult1 c i) t ω| ≤ B1' := by
    intro t ω
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (h1 t ω).trans (le_max_left _ _)
  set B2 := |c.κ⁻¹| * (|c.lx| * (Mx + |c.xstar|) + B1 + |c.β⁻¹| * B1') with hB2
  have h2 : ∀ t ω, |mult2 c im1 x i t ω| ≤ B2 := by
    intro t ω
    simp only [mult2, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, hB2, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ (h1 t ω))) ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hMx t ω) le_rfl))
        (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hl1 t ω) (abs_nonneg _)
  refine ⟨max B1 B2, fun t j ω => ?_⟩
  fin_cases j
  · exact (h1 t ω).trans (le_max_left _ _)
  · exact (h2 t ω).trans (le_max_right _ _)

/-- Woodford (2003), p. 585 (tool): the plan built from a bounded `Φ` is bounded. -/
theorem planOf_bounded (c : Calib) (Φh : Fin 2 → ℝ) {Φ : ℕ → Fin 2 → Ω → ℝ}
    (hΦ : VBounded Φ) :
    BoundedProc (piOf c Φh Φ) ∧ BoundedProc (xOf c Φh Φ) ∧ BoundedProc (iOf c Φ) := by
  obtain ⟨M, hM⟩ := hΦ
  obtain ⟨ML, hML⟩ := lagV_bounded Φh ⟨M, hM⟩
  refine ⟨⟨|c.σ / c.β| * ML + M + ML, fun t ω => ?_⟩,
    ⟨|c.xstar| + |c.lx⁻¹| * (|c.κ| * M + M + |c.β⁻¹| * ML), fun t ω => ?_⟩,
    ⟨|c.istar| + |c.σ / c.li| * M, fun t ω => ?_⟩⟩
  · simp only [piOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_
      (hM t 1 ω))) (hML t 1 ω))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hML t 0 ω) (abs_nonneg _)
  · simp only [xOf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_
      (hM t 0 ω))) ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t 1 ω) (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hML t 0 ω) (abs_nonneg _)
  · simp only [iOf, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t 0 ω) (abs_nonneg _)

/-- Woodford (2003), p. 585 (tool): the plan built from an adapted `Φ` is adapted. -/
theorem planOf_adapted (c : Calib) (Φh : Fin 2 → ℝ) {Φ : ℕ → Fin 2 → Ω → ℝ}
    (hΦ : VAdapted 𝔼 Φ) :
    𝔼.Adapted (piOf c Φh Φ) ∧ 𝔼.Adapted (xOf c Φh Φ) ∧ 𝔼.Adapted (iOf c Φ) := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · simp only [piOf, map_add, map_sub, map_smul, hΦ t 1, lagV_known 𝔼 hΦ t 0,
      lagV_known 𝔼 hΦ t 1]
  · simp only [xOf, map_add, map_sub, map_smul, hΦ t 0, hΦ t 1, 𝔼.const,
      lagV_known 𝔼 hΦ t 0]
  · simp only [iOf, map_sub, map_smul, hΦ t 0, 𝔼.const]

/-- **Woodford (2003), Proposition 8.5, p. 584 (and App. G.4) — determinacy, proved for all
admissible parameters.** For `0 < β < 1` and `σ, κ, λ_x, λ_i > 0`, every bounded adapted
disturbance process `(rⁿ, u)` and every history `x_{−1}, i_{−1}, i_{−2}`, there is exactly one
bounded adapted rational-expectations equilibrium `(π, x, i)` of (2.1), (3.1) under the rule
(3.7)–(3.9). (The book's hypothesis that a bounded optimal plan exists is not needed: see
`bounded_optimum_exists`; survey E21.) -/
theorem rule_determinate (c : Calib) (hc : c.Adm) {rn u : ℕ → Ω → ℝ}
    (hrb : BoundedProc rn) (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hua : 𝔼.Adapted u)
    (xm1 im1 im2 : ℝ) :
    ∃! e : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      RuleEqm 𝔼 c rn u xm1 im1 im2 e.1 e.2.1 e.2.2 ∧
        (𝔼.Adapted e.1 ∧ 𝔼.Adapted e.2.1 ∧ 𝔼.Adapted e.2.2) ∧
        (BoundedProc e.1 ∧ BoundedProc e.2.1 ∧ BoundedProc e.2.2) := by
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, hli⟩ := hc
  obtain ⟨T, D, hTD, hD, hfacC⟩ := exists_real_split hβ0 hβ1 hσ hκ hlx.le hli
  have hfac : ∀ μ : ℝ, pR c.β c.σ c.κ c.lx c.li μ =
      (μ ^ 2 - T * μ + D) * (μ ^ 2 - T / (c.β * D) * μ + 1 / (c.β ^ 2 * D)) := by
    intro μ
    have := hfacC μ
    rw [pG_ofReal] at this
    exact_mod_cast this
  obtain ⟨-, hsolv, htr, hdet, hB, htrK, hdetK⟩ := solvent_eq hβ0 hβ1 hlx hli hTD hD hfac
  have hK := schurStable_scale hβ0 hβ1 hTD
  rw [← htrK, ← hdetK] at hK
  have hXs : SchurStable
      (tr2 (inv2 (A1G c.β c.σ c.κ c.lx c.li - T • PmG c.β c.σ c.κ c.lx) *
        (A2G c.β c.σ c.κ c.lx - D • PmG c.β c.σ c.κ c.lx)))
      (det2 (inv2 (A1G c.β c.σ c.κ c.lx c.li - T • PmG c.β c.σ c.κ c.lx) *
        (A2G c.β c.σ c.κ c.lx - D • PmG c.β c.σ c.κ c.lx))) := by
    rw [htr, hdet]; exact hTD
  obtain ⟨Φ, ⟨hs, ha, hb⟩, huniq⟩ := sys2_existsUnique 𝔼 hsolv hXs hB hK
    (Fphi_bounded c hrb hub) (Fphi_adapted 𝔼 c hra hua) (PhiH c xm1 im1 im2)
  have hcA : c.Adm := ⟨hβ0, hβ1, hσ, hκ, hlx, hli⟩
  refine ⟨(piOf c (PhiH c xm1 im1 im2) Φ, xOf c (PhiH c xm1 im1 im2) Φ, iOf c Φ),
    ⟨eqm_of_sys 𝔼 c hcA hs ha, planOf_adapted 𝔼 c _ ha, planOf_bounded c _ hb⟩, ?_⟩
  rintro ⟨π', x', i'⟩ ⟨he, ⟨-, hxa, hia⟩, ⟨-, hxb, hib⟩⟩
  have hΦ' : PhiOf c im1 x' i' = Φ := huniq _ ⟨sys_of_eqm 𝔼 c hcA he hxa hia,
    PhiOf_adapted 𝔼 c im1 hxa hia, PhiOf_bounded c im1 hxb hib⟩
  obtain ⟨r1, r2, r3⟩ := eqm_roundtrip 𝔼 c hcA he
  rw [← hΦ', r1, r2, r3]

/-! ### Optimality: Lagrangian sufficiency, timeless and robust -/

/-- Woodford (2003), (3.2), p. 583: the period loss `π_t² + λ_x(x_t − x*)² + λ_i(i_t − i*)²`. -/
noncomputable def periodLoss (c : Calib) (π x i : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => π t ω ^ 2 + c.lx * (x t ω - c.xstar) ^ 2 + c.li * (i t ω - c.istar) ^ 2

/-- Woodford (2003), (2.2), p. 560, with (3.2): the expected discounted loss
`E_{t₀} ∑_{t ≥ t₀} β^{t−t₀} L_t` (`t₀ = 0`), as a function of the date-0 state. -/
noncomputable def Jloss (c : Calib) (π x i : ℕ → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑' t, c.β ^ t * 𝔼.E 0 (periodLoss c π x i t) ω

/-- Woodford (2003), §3.1, p. 584: a plan is feasible if it satisfies (2.1) and (3.1) at all
dates. -/
def Feasible (c : Calib) (rn u π x i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, AS 𝔼 c u π x t ∧ IS 𝔼 c rn π x i t

/-- Woodford (2003), (3.3)–(3.5), p. 584: the first-order conditions with multipliers
`φ₁, φ₂` and pre-sample multipliers `φ_{1,−1}, φ_{2,−1}`. -/
def FOC (c : Calib) (π x i φ1 φ2 : ℕ → Ω → ℝ) (φ1h φ2h : ℝ) : Prop :=
  ∀ t, FOC3 c π φ1 φ2 φ1h φ2h t ∧ FOC4 c x φ1 φ2 φ1h t ∧ FOC5 c i φ1 t

/-- Woodford (2003), §1.1, p. 538 (optimality subject to the initial commitments (3.6)): the
plan is bounded, adapted and feasible, has `π₀ = π̄₀`, `x₀ = x̄₀`, and attains the lowest
expected discounted loss among all such plans. -/
def OptimalGiven (c : Calib) (rn u : ℕ → Ω → ℝ) (πbar xbar : Ω → ℝ) (π x i : ℕ → Ω → ℝ) :
    Prop :=
  Feasible 𝔼 c rn u π x i ∧ (𝔼.Adapted π ∧ 𝔼.Adapted x ∧ 𝔼.Adapted i) ∧
    (BoundedProc π ∧ BoundedProc x ∧ BoundedProc i) ∧ π 0 = πbar ∧ x 0 = xbar ∧
    ∀ π' x' i' : ℕ → Ω → ℝ, Feasible 𝔼 c rn u π' x' i' →
      (𝔼.Adapted π' ∧ 𝔼.Adapted x' ∧ 𝔼.Adapted i') →
      (BoundedProc π' ∧ BoundedProc x' ∧ BoundedProc i') → π' 0 = πbar → x' 0 = xbar →
      Jloss 𝔼 c π x i ≤ Jloss 𝔼 c π' x' i'

/-- Woodford (2003), App. G (tool): a telescoping series with geometrically vanishing terms. -/
theorem tsum_telescope {y : ℕ → ℝ} {C ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hy : ∀ t, |y t| ≤ C * ρ ^ t) : ∑' t, (y t - y (t + 1)) = y 0 := by
  have hs : Summable (fun t => y t - y (t + 1)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (2 * C))
      (fun t => ?_)
    rw [Real.norm_eq_abs]
    have h1 := hy t
    have h2 := hy (t + 1)
    have hp : ρ ^ (t + 1) ≤ ρ ^ t := pow_le_pow_of_le_one hρ0 hρ1.le (Nat.le_succ t)
    have hC : 0 ≤ C := by
      have := (abs_nonneg (y 0)).trans (hy 0)
      simpa using this
    calc |y t - y (t + 1)| ≤ |y t| + |y (t + 1)| := abs_sub _ _
      _ ≤ C * ρ ^ t + C * ρ ^ t := add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left hp hC))
      _ = 2 * C * ρ ^ t := by ring
  have hlim : Tendsto (fun n => ∑ t ∈ Finset.range n, (y t - y (t + 1))) atTop
      (𝓝 (y 0)) := by
    have hy0 : Tendsto y atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun t => C * ρ ^ t) (fun t => ?_) ?_
      · rw [Real.norm_eq_abs]; exact hy t
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul C
    have : (fun n => ∑ t ∈ Finset.range n, (y t - y (t + 1))) = fun n => y 0 - y n := by
      funext n
      exact Finset.sum_range_sub' y n
    rw [this]
    simpa using hy0.const_sub (y 0)
  exact tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim

/-- Woodford (2003), (2.2), p. 560 (tool): discounted expectations of a bounded process are
summable. -/
theorem summable_disc {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → Ω → ℝ} {M : ℝ}
    (hf : ∀ t ω, |f t ω| ≤ M) (ω : Ω) : Summable (fun t => β ^ t * 𝔼.E 0 (f t) ω) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M) (fun t => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hf t) 0 ω) (pow_nonneg hβ0 t))

/-- Woodford (2003), (3.2), p. 583 (tool): the period loss of a bounded plan is bounded. -/
theorem periodLoss_bounded (c : Calib) (hc : c.Adm) {π x i : ℕ → Ω → ℝ} (hπ : BoundedProc π)
    (hx : BoundedProc x) (hi : BoundedProc i) :
    ∃ M, ∀ t ω, |periodLoss c π x i t ω| ≤ M := by
  obtain ⟨-, -, -, -, hlx, hli⟩ := hc
  obtain ⟨Mπ, hMπ⟩ := hπ
  obtain ⟨Mx, hMx⟩ := hx
  obtain ⟨Mi, hMi⟩ := hi
  refine ⟨Mπ ^ 2 + c.lx * (Mx + |c.xstar|) ^ 2 + c.li * (Mi + |c.istar|) ^ 2, fun t ω => ?_⟩
  have h1 : π t ω ^ 2 ≤ Mπ ^ 2 := by
    have := hMπ t ω
    have h0 : 0 ≤ |π t ω| := abs_nonneg _
    nlinarith [sq_abs (π t ω)]
  have h2 : (x t ω - c.xstar) ^ 2 ≤ (Mx + |c.xstar|) ^ 2 := by
    have := (abs_sub (x t ω) c.xstar).trans (add_le_add (hMx t ω) le_rfl)
    have h0 : 0 ≤ |x t ω - c.xstar| := abs_nonneg _
    nlinarith [sq_abs (x t ω - c.xstar)]
  have h3 : (i t ω - c.istar) ^ 2 ≤ (Mi + |c.istar|) ^ 2 := by
    have := (abs_sub (i t ω) c.istar).trans (add_le_add (hMi t ω) le_rfl)
    have h0 : 0 ≤ |i t ω - c.istar| := abs_nonneg _
    nlinarith [sq_abs (i t ω - c.istar)]
  have hnn : 0 ≤ periodLoss c π x i t ω := by
    unfold periodLoss
    positivity
  rw [abs_of_nonneg hnn]
  unfold periodLoss
  nlinarith [mul_le_mul_of_nonneg_left h2 hlx.le, mul_le_mul_of_nonneg_left h3 hli.le]

/-- **Woodford (2003), §3.1, pp. 584–585, and Ch. 7 (the Lagrangian method made exact):
the Lagrangian identity.** Let `(π, x, i)` be feasible and satisfy the first-order conditions
(3.3)–(3.5) with bounded adapted multipliers, and let `(π', x', i')` be any bounded feasible plan
with the same initial values `π'₀ = π₀`, `x'₀ = x₀` (the commitments (3.6)). Then (under the
pull-out property) the loss difference is exactly
`J' − J = ∑ βᵗ E₀[(π'_t − π_t)² + λ_x(x'_t − x_t)² + λ_i(i'_t − i_t)²]`. -/
theorem lagrangian_identity (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut)
    {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : ℝ}
    (hf : Feasible 𝔼 c rn u π x i) (hfoc : FOC c π x i φ1 φ2 φ1h φ2h)
    (hφ1a : 𝔼.Adapted φ1) (hφ2a : 𝔼.Adapted φ2)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    (hφ1b : BoundedProc φ1) (hφ2b : BoundedProc φ2)
    {π' x' i' : ℕ → Ω → ℝ} (hf' : Feasible 𝔼 c rn u π' x' i')
    (hπb' : BoundedProc π') (hxb' : BoundedProc x') (hib' : BoundedProc i')
    (h0 : π' 0 = π 0) (hx0 : x' 0 = x 0) (ω : Ω) :
    Jloss 𝔼 c π' x' i' ω = Jloss 𝔼 c π x i ω +
      ∑' t, c.β ^ t * 𝔼.E 0 (fun ω' => (π' t ω' - π t ω') ^ 2
        + c.lx * (x' t ω' - x t ω') ^ 2 + c.li * (i' t ω' - i t ω') ^ 2) ω := by
  have hc' := hc
  obtain ⟨hβ0, hβ1, hσ, hκ, hlx, hli⟩ := hc'
  set dπ : ℕ → Ω → ℝ := fun t => π' t - π t with hdπ
  set dx : ℕ → Ω → ℝ := fun t => x' t - x t with hdx
  set di : ℕ → Ω → ℝ := fun t => i' t - i t with hdi
  set Sq : ℕ → Ω → ℝ := fun t ω' => (π' t ω' - π t ω') ^ 2
    + c.lx * (x' t ω' - x t ω') ^ 2 + c.li * (i' t ω' - i t ω') ^ 2 with hSq
  set G : ℕ → Ω → ℝ := fun t => π t * dπ t + c.lx • ((x t - fun _ => c.xstar) * dx t)
    + c.li • ((i t - fun _ => c.istar) * di t) with hG
  set b : ℕ → Ω → ℝ := fun t => c.β⁻¹ • (lag φ1h φ1 t * (c.σ • dπ t + dx t))
    + lag φ2h φ2 t * dπ t with hb
  -- (1) the loss difference
  have hL : ∀ t, periodLoss c π' x' i' t = periodLoss c π x i t + (2 : ℝ) • G t + Sq t := by
    intro t
    funext ω'
    simp only [periodLoss, hG, hSq, hdπ, hdx, hdi, Pi.add_apply, Pi.smul_apply, Pi.mul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
  -- (2) the first-order conditions and the constraints
  have hGb : ∀ t, G t = b t - (c.β • (φ2 t * 𝔼.E t (dπ (t + 1)))
      + φ1 t * (𝔼.E t (dx (t + 1)) + c.σ • 𝔼.E t (dπ (t + 1)))) := by
    intro t
    funext ω'
    obtain ⟨f3, f4, f5⟩ := hfoc t
    have f3 := congrFun f3 ω'
    have f4 := congrFun f4 ω'
    have f5 := congrFun f5 ω'
    have a1 := congrFun (hf t).1 ω'
    have a2 := congrFun (hf' t).1 ω'
    have s1 := congrFun (hf t).2 ω'
    have s2 := congrFun (hf' t).2 ω'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at f3 f4 f5 a1 a2 s1 s2
    simp only [hG, hb, hdπ, hdx, hdi, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul]
    have hβne : c.β ≠ 0 := hβ0.ne'
    linear_combination (norm := (field_simp; ring)) (π' t ω' - π t ω') * f3
      + (x' t ω' - x t ω') * f4 + (i' t ω' - i t ω') * f5
      - φ2 t ω' * (a2 - a1) - φ1 t ω' * (s2 - s1)
  -- (3) the pull-out step: `E₀ c'_t = β E₀ b_{t+1}`
  have hc' : ∀ t, 𝔼.E 0 (c.β • (φ2 t * 𝔼.E t (dπ (t + 1)))
      + φ1 t * (𝔼.E t (dx (t + 1)) + c.σ • 𝔼.E t (dπ (t + 1)))) = c.β • 𝔼.E 0 (b (t + 1)) := by
    intro t
    have e1 : c.β • (φ2 t * 𝔼.E t (dπ (t + 1)))
        + φ1 t * (𝔼.E t (dx (t + 1)) + c.σ • 𝔼.E t (dπ (t + 1))) =
        𝔼.E t (c.β • (φ2 t * dπ (t + 1)) + φ1 t * (dx (t + 1) + c.σ • dπ (t + 1))) := by
      rw [map_add, map_smul, hpo t _ _ (hφ2a t), hpo t _ _ (hφ1a t), map_add, map_smul]
    have e2 : c.β • (φ2 t * dπ (t + 1)) + φ1 t * (dx (t + 1) + c.σ • dπ (t + 1)) =
        c.β • b (t + 1) := by
      have hβne : c.β ≠ 0 := hβ0.ne'
      funext ω'
      simp only [hb, lag, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      field_simp
      ring
    rw [e1, 𝔼.tower (Nat.zero_le t), e2, map_smul]
  -- (4) the initial term vanishes by the commitments (3.6)
  have hb0 : b 0 = 0 := by
    funext ω'
    simp only [hb, hdπ, hdx, lag, h0, hx0, sub_self, Pi.add_apply, Pi.smul_apply,
      Pi.mul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  -- (5) bounds
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mπ', hMπ'⟩ := hπb'
  obtain ⟨Mx', hMx'⟩ := hxb'
  obtain ⟨M1, hM1⟩ := hφ1b
  obtain ⟨M2, hM2⟩ := hφ2b
  set L1M := max M1 |φ1h|
  set L2M := max M2 |φ2h|
  have hl1 : ∀ t ω', |lag φ1h φ1 t ω'| ≤ L1M := by
    intro t ω'
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (hM1 t ω').trans (le_max_left _ _)
  have hl2 : ∀ t ω', |lag φ2h φ2 t ω'| ≤ L2M := by
    intro t ω'
    cases t with
    | zero => exact le_max_right _ _
    | succ t => exact (hM2 t ω').trans (le_max_left _ _)
  have hdπb : ∀ t ω', |dπ t ω'| ≤ Mπ' + Mπ := fun t ω' =>
    (abs_sub _ _).trans (add_le_add (hMπ' t ω') (hMπ t ω'))
  have hdxb : ∀ t ω', |dx t ω'| ≤ Mx' + Mx := fun t ω' =>
    (abs_sub _ _).trans (add_le_add (hMx' t ω') (hMx t ω'))
  set MB := |c.β⁻¹| * (L1M * (|c.σ| * (Mπ' + Mπ) + (Mx' + Mx))) + L2M * (Mπ' + Mπ)
  have hbb : ∀ t ω', |b t ω'| ≤ MB := by
    intro t ω'
    simp only [hb, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left (mul_le_mul (hl1 t ω') ?_ (abs_nonneg _)
        ((abs_nonneg _).trans (hl1 t ω'))) (abs_nonneg _)
      refine (abs_add_le _ _).trans (add_le_add ?_ (hdxb t ω'))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hdπb t ω') (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul (hl2 t ω') (hdπb t ω') (abs_nonneg _) ((abs_nonneg _).trans (hl2 t ω'))
  -- (6) summing
  set y : ℕ → ℝ := fun t => c.β ^ t * 𝔼.E 0 (b t) ω with hy
  have hyb : ∀ t, |y t| ≤ MB * c.β ^ t := by
    intro t
    simp only [hy, abs_mul, abs_pow, abs_of_pos hβ0]
    rw [mul_comm MB]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hbb t) 0 ω) (pow_nonneg hβ0.le t)
  have key : ∀ t, c.β ^ t * 𝔼.E 0 (periodLoss c π' x' i' t) ω =
      c.β ^ t * 𝔼.E 0 (periodLoss c π x i t) ω + 2 * (y t - y (t + 1))
        + c.β ^ t * 𝔼.E 0 (Sq t) ω := by
    intro t
    have e := congrFun (congrArg (𝔼.E 0) (hL t)) ω
    rw [map_add, map_add, map_smul, hGb t, map_sub, hc' t] at e
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e
    rw [e]
    simp only [hy, pow_succ]
    ring
  obtain ⟨ML, hML⟩ := periodLoss_bounded c hc ⟨Mπ, hMπ⟩ ⟨Mx, hMx⟩ hib
  obtain ⟨ML', hML'⟩ := periodLoss_bounded c hc ⟨Mπ', hMπ'⟩ ⟨Mx', hMx'⟩ hib'
  have s1 := summable_disc 𝔼 hβ0.le hβ1 hML ω
  have s1' := summable_disc 𝔼 hβ0.le hβ1 hML' ω
  have s2 : Summable (fun t => y t - y (t + 1)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left
      (2 * MB)) (fun t => ?_)
    rw [Real.norm_eq_abs]
    have hp : c.β ^ (t + 1) ≤ c.β ^ t := pow_le_pow_of_le_one hβ0.le hβ1.le (Nat.le_succ t)
    have hMB : 0 ≤ MB := (abs_nonneg _).trans (hbb 0 ω)
    calc |y t - y (t + 1)| ≤ |y t| + |y (t + 1)| := abs_sub _ _
      _ ≤ MB * c.β ^ t + MB * c.β ^ t :=
          add_le_add (hyb t) ((hyb (t + 1)).trans (mul_le_mul_of_nonneg_left hp hMB))
      _ = 2 * MB * c.β ^ t := by ring
  have s3 : Summable (fun t => c.β ^ t * 𝔼.E 0 (Sq t) ω) := by
    have : (fun t => c.β ^ t * 𝔼.E 0 (Sq t) ω) = fun t =>
        c.β ^ t * 𝔼.E 0 (periodLoss c π' x' i' t) ω
          - c.β ^ t * 𝔼.E 0 (periodLoss c π x i t) ω - 2 * (y t - y (t + 1)) := by
      funext t
      rw [key t]
      ring
    rw [this]
    exact (s1'.sub s1).sub (s2.mul_left 2)
  have htel : ∑' t, (y t - y (t + 1)) = 0 := by
    rw [tsum_telescope hβ0.le hβ1 (C := MB) hyb]
    simp [hy, hb0]
  unfold Jloss
  rw [tsum_congr key, (s1.add (s2.mul_left 2)).tsum_add s3, s1.tsum_add (s2.mul_left 2),
    tsum_mul_left, htel]
  ring

/-- **Woodford (2003), §3.1, pp. 584–585: Lagrangian sufficiency.** A plan satisfying (2.1),
(3.1) and the first-order conditions (3.3)–(3.5) with bounded adapted multipliers minimises the
expected discounted loss among all bounded feasible plans with the same initial values (3.6)
(under the pull-out property, true for perfect foresight and every finite event tree). -/
theorem plan_optimal (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut)
    {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : ℝ}
    (hf : Feasible 𝔼 c rn u π x i) (hfoc : FOC c π x i φ1 φ2 φ1h φ2h)
    (hφ1a : 𝔼.Adapted φ1) (hφ2a : 𝔼.Adapted φ2)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    (hφ1b : BoundedProc φ1) (hφ2b : BoundedProc φ2)
    {π' x' i' : ℕ → Ω → ℝ} (hf' : Feasible 𝔼 c rn u π' x' i')
    (hπb' : BoundedProc π') (hxb' : BoundedProc x') (hib' : BoundedProc i')
    (h0 : π' 0 = π 0) (hx0 : x' 0 = x 0) : Jloss 𝔼 c π x i ≤ Jloss 𝔼 c π' x' i' := by
  intro ω
  rw [lagrangian_identity 𝔼 c hc hpo hf hfoc hφ1a hφ2a hπb hxb hib hφ1b hφ2b hf' hπb' hxb'
    hib' h0 hx0 ω]
  have hlx := hc.2.2.2.2.1
  have hli := hc.2.2.2.2.2
  refine le_add_of_nonneg_right (tsum_nonneg fun t => mul_nonneg (pow_nonneg hc.1.le t) ?_)
  have hm := 𝔼.mono 0 (x := fun _ => (0 : ℝ))
    (y := fun ω' => (π' t ω' - π t ω') ^ 2 + c.lx * (x' t ω' - x t ω') ^ 2
      + c.li * (i' t ω' - i t ω') ^ 2) (fun ω' => by positivity)
  rw [𝔼.const] at hm
  exact hm ω

/-- **Woodford (2003), §3.1, p. 585: the rule is optimal from a timeless perspective, and
robustly so.** Every bounded equilibrium under the rule (3.7)–(3.9) (with adapted `x`, `i`)
minimises the expected discounted loss (2.2)–(3.2) among all bounded adapted feasible plans that
share its date-`t₀` inflation and output gap — the self-consistent initial commitments (3.6) — for
any bounded disturbance processes `rⁿ, u` (pull-out property assumed). -/
theorem rule_eqm_optimal (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut) {rn u π x i : ℕ → Ω → ℝ}
    {xm1 im1 im2 : ℝ} (he : RuleEqm 𝔼 c rn u xm1 im1 im2 π x i) (hπa : 𝔼.Adapted π)
    (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (hib : BoundedProc i) : OptimalGiven 𝔼 c rn u (π 0) (x 0) π x i := by
  have hc' := hc
  obtain ⟨hβ0, -, hσ, hκ, -, hli⟩ := hc'
  have hfoc : FOC c π x i (mult1 c i) (mult2 c im1 x i) (mult1h c im1) (mult2h c xm1 im1 im2) :=
    fun t => ⟨(rule_iff_foc3 c hβ0.ne' hσ.ne' hκ.ne' hli.ne' xm1 im1 im2 π x i t).mp (he t).2.2,
      foc4_mult c hκ.ne' im1 x i t, foc5_mult c hσ.ne' i t⟩
  obtain ⟨M, hM⟩ := PhiOf_bounded c im1 hxb hib
  have hb1 : BoundedProc (mult1 c i) := ⟨M, fun t ω => hM t 0 ω⟩
  have hb2 : BoundedProc (mult2 c im1 x i) := ⟨M, fun t ω => hM t 1 ω⟩
  refine ⟨fun t => ⟨(he t).1, (he t).2.1⟩, ⟨hπa, hxa, hia⟩, ⟨hπb, hxb, hib⟩, rfl, rfl, ?_⟩
  intro π' x' i' hf' _ ⟨hπb', hxb', hib'⟩ h0 hx0
  exact plan_optimal 𝔼 c hc hpo (fun t => ⟨(he t).1, (he t).2.1⟩) hfoc (mult1_adapted 𝔼 c hia)
    (mult2_adapted 𝔼 c im1 hxa hia) hπb hxb hib hb1 hb2 hf' hπb' hxb' hib' h0 hx0

/-- **Woodford (2003), §3.1 (uniqueness of the optimum by strict convexity), perfect
foresight.** A bounded feasible plan with the same initial values and the same loss as a plan
satisfying the first-order conditions coincides with it. -/
theorem unique_optimum_pf (c : Calib) (hc : c.Adm)
    {rn u π x i φ1 φ2 : ℕ → Unit → ℝ} {φ1h φ2h : ℝ}
    (hf : Feasible perfectForesight c rn u π x i) (hfoc : FOC c π x i φ1 φ2 φ1h φ2h)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    (hφ1b : BoundedProc φ1) (hφ2b : BoundedProc φ2)
    {π' x' i' : ℕ → Unit → ℝ} (hf' : Feasible perfectForesight c rn u π' x' i')
    (hπb' : BoundedProc π') (hxb' : BoundedProc x') (hib' : BoundedProc i')
    (h0 : π' 0 = π 0) (hx0 : x' 0 = x 0)
    (hJ : Jloss perfectForesight c π' x' i' = Jloss perfectForesight c π x i) :
    π' = π ∧ x' = x ∧ i' = i := by
  have hc' := hc
  obtain ⟨hβ0, hβ1, -, -, hlx, hli⟩ := hc'
  have hid := lagrangian_identity perfectForesight c hc perfectForesight_pullOut hf hfoc
    (fun _ => rfl) (fun _ => rfl) hπb hxb hib hφ1b hφ2b hf' hπb' hxb' hib' h0 hx0 ()
  rw [hJ] at hid
  set S : ℕ → ℝ := fun t => (π' t () - π t ()) ^ 2 + c.lx * (x' t () - x t ()) ^ 2
    + c.li * (i' t () - i t ()) ^ 2 with hS
  have hS0 : ∀ t, 0 ≤ S t := fun t => by simp only [hS]; positivity
  have hsum0 : ∑' t, c.β ^ t * S t = 0 := by
    have : ∑' t, c.β ^ t * perfectForesight.E 0 (fun ω' => (π' t ω' - π t ω') ^ 2
        + c.lx * (x' t ω' - x t ω') ^ 2 + c.li * (i' t ω' - i t ω') ^ 2) () = 0 := by linarith
    simpa [perfectForesight] using this
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨Mπ', hMπ'⟩ := hπb'
  obtain ⟨Mx', hMx'⟩ := hxb'
  obtain ⟨Mi', hMi'⟩ := hib'
  have hSb : ∀ t, S t ≤ (Mπ' + Mπ) ^ 2 + c.lx * (Mx' + Mx) ^ 2 + c.li * (Mi' + Mi) ^ 2 := by
    intro t
    have a := (abs_sub (π' t ()) (π t ())).trans (add_le_add (hMπ' t ()) (hMπ t ()))
    have b := (abs_sub (x' t ()) (x t ())).trans (add_le_add (hMx' t ()) (hMx t ()))
    have d := (abs_sub (i' t ()) (i t ())).trans (add_le_add (hMi' t ()) (hMi t ()))
    have a2 := sq_le_sq' (abs_le.mp a).1 (abs_le.mp a).2
    have b2 := sq_le_sq' (abs_le.mp b).1 (abs_le.mp b).2
    have d2 := sq_le_sq' (abs_le.mp d).1 (abs_le.mp d).2
    simp only [hS]
    nlinarith [mul_le_mul_of_nonneg_left b2 hlx.le, mul_le_mul_of_nonneg_left d2 hli.le]
  have hsumm : Summable (fun t => c.β ^ t * S t) :=
    Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hβ0.le t) (hS0 t))
      (fun t => mul_le_mul_of_nonneg_left (hSb t) (pow_nonneg hβ0.le t))
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right _)
  have hzero := (hasSum_zero_iff_of_nonneg
    (fun t => mul_nonneg (pow_nonneg hβ0.le t) (hS0 t))).mp (hsum0 ▸ hsumm.hasSum)
  have hSt : ∀ t, S t = 0 := by
    intro t
    have := congrFun hzero t
    simp only [Pi.zero_apply] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero t hβ0.ne')
    · exact h
  have hcomp : ∀ t, π' t () = π t () ∧ x' t () = x t () ∧ i' t () = i t () := by
    intro t
    have h := hSt t
    simp only [hS] at h
    have q1 := sq_nonneg (π' t () - π t ())
    have q2 := mul_nonneg hlx.le (sq_nonneg (x' t () - x t ()))
    have q3 := mul_nonneg hli.le (sq_nonneg (i' t () - i t ()))
    have e1 : (π' t () - π t ()) ^ 2 = 0 := by linarith
    have e2' : c.lx * (x' t () - x t ()) ^ 2 = 0 := by linarith
    have e3' : c.li * (i' t () - i t ()) ^ 2 = 0 := by linarith
    have e2 : (x' t () - x t ()) ^ 2 = 0 :=
      (mul_eq_zero.mp e2').resolve_left hlx.ne'
    have e3 : (i' t () - i t ()) ^ 2 = 0 :=
      (mul_eq_zero.mp e3').resolve_left hli.ne'
    exact ⟨sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e1),
      sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e2),
      sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e3)⟩
  refine ⟨funext fun t => funext fun _ => (hcomp t).1, funext fun t => funext fun _ =>
    (hcomp t).2.1, funext fun t => funext fun _ => (hcomp t).2.2⟩

/-- Woodford (2003), Proposition 8.5, p. 584 (the hypothesis): for every bounded adapted
disturbance process the optimal-policy problem with initial commitments (3.6) has a bounded
solution (for some initial commitments). -/
def BoundedOptimumExists (c : Calib) : Prop :=
  ∀ rn u : ℕ → Ω → ℝ, BoundedProc rn → 𝔼.Adapted rn → BoundedProc u → 𝔼.Adapted u →
    ∃ πbar xbar : Ω → ℝ, ∃ π x i : ℕ → Ω → ℝ, OptimalGiven 𝔼 c rn u πbar xbar π x i

/-- **Woodford (2003), Proposition 8.5, p. 584, the book's hypothesis is always satisfied**
(under the pull-out property): the equilibrium under the rule from any history is a bounded
optimum given its own initial values. -/
theorem bounded_optimum_exists (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut) :
    BoundedOptimumExists 𝔼 c := by
  intro rn u hrb hra hub hua
  obtain ⟨⟨π, x, i⟩, ⟨he, ⟨hπa, hxa, hia⟩, ⟨hπb, hxb, hib⟩⟩, -⟩ :=
    rule_determinate 𝔼 c hc hrb hra hub hua 0 0 0
  exact ⟨π 0, x 0, π, x, i, rule_eqm_optimal 𝔼 c hc hpo he hπa hxa hia hπb hxb hib⟩

/-- **Woodford (2003), Proposition 8.5, p. 584, as stated.** If the optimal-policy problem has a
bounded solution for all bounded disturbances, commitment to the rule (3.7)–(3.9) implies a
determinate rational-expectations equilibrium: exactly one bounded adapted equilibrium for every
bounded adapted `(rⁿ, u)` and every history. (The hypothesis is not used: `rule_determinate`
proves the conclusion for all admissible parameters, and `bounded_optimum_exists` shows the
hypothesis holds anyway; survey E21.) -/
theorem prop_8_5 (c : Calib) (hc : c.Adm) :
    BoundedOptimumExists 𝔼 c → ∀ rn u : ℕ → Ω → ℝ, BoundedProc rn → 𝔼.Adapted rn →
      BoundedProc u → 𝔼.Adapted u → ∀ xm1 im1 im2 : ℝ,
      ∃! e : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
        RuleEqm 𝔼 c rn u xm1 im1 im2 e.1 e.2.1 e.2.2 ∧
          (𝔼.Adapted e.1 ∧ 𝔼.Adapted e.2.1 ∧ 𝔼.Adapted e.2.2) ∧
          (BoundedProc e.1 ∧ BoundedProc e.2.1 ∧ BoundedProc e.2.2) :=
  fun _ _ _ hrb hra hub hua xm1 im1 im2 => rule_determinate 𝔼 c hc hrb hra hub hua xm1 im1 im2

/-! ### Footnote 35 and the roots `λ₁, λ₂` of the rule -/

/-- Woodford (2003), (3.10) and fn. 35, pp. 586–588: the smaller root
`λ₁ = (ρ₁ + ρ₂ − √((ρ₁+ρ₂)² − 4ρ₂))/2` of `z² − (ρ₁+ρ₂)z + ρ₂`. -/
noncomputable def lam1 (r1 r2 : ℝ) : ℝ := ((r1 + r2) - Real.sqrt ((r1 + r2) ^ 2 - 4 * r2)) / 2

/-- Woodford (2003), (3.10) and fn. 35, pp. 586–588: the larger root
`λ₂ = (ρ₁ + ρ₂ + √((ρ₁+ρ₂)² − 4ρ₂))/2`. -/
noncomputable def lam2 (r1 r2 : ℝ) : ℝ := ((r1 + r2) + Real.sqrt ((r1 + r2) ^ 2 - 4 * r2)) / 2

/-- Woodford (2003), fn. 35, p. 586: if `ρ₁ > 1` the discriminant is positive,
`(ρ₁+ρ₂)² − 4ρ₂ = (ρ₁+ρ₂−2)² + 4(ρ₁−1)`. -/
theorem disc_pos {r1 r2 : ℝ} (h1 : 1 < r1) : 0 < (r1 + r2) ^ 2 - 4 * r2 := by
  nlinarith [sq_nonneg (r1 + r2 - 2)]

/-- Woodford (2003), (3.10), p. 588: `λ₁ + λ₂ = ρ₁ + ρ₂`, `λ₁λ₂ = ρ₂`, hence
`z² − (ρ₁+ρ₂)z + ρ₂ = (z − λ₁)(z − λ₂)`, i.e. `1 − (ρ₁+ρ₂)L + ρ₂L² = (1 − λ₁L)(1 − λ₂L)`. -/
theorem lam_factor {r1 r2 : ℝ} (h1 : 1 < r1) :
    lam1 r1 r2 + lam2 r1 r2 = r1 + r2 ∧ lam1 r1 r2 * lam2 r1 r2 = r2 ∧
      ∀ z : ℝ, z ^ 2 - (r1 + r2) * z + r2 = (z - lam1 r1 r2) * (z - lam2 r1 r2) := by
  have hd := disc_pos (r2 := r2) h1
  have hs := Real.sq_sqrt hd.le
  refine ⟨by unfold lam1 lam2; ring, ?_, fun z => ?_⟩
  · unfold lam1 lam2
    nlinarith
  · unfold lam1 lam2
    nlinarith

/-- **Woodford (2003), fn. 35, p. 586.** If `ρ₁ > 1` then `λ₁ < 1 < λ₂`: the rule (3.7) is
superinertial (a root `λ₂ > 1`), whatever the sign of `ρ₂`. -/
theorem fn35_roots_lt_gt {r1 r2 : ℝ} (h1 : 1 < r1) : lam1 r1 r2 < 1 ∧ 1 < lam2 r1 r2 := by
  have hd := disc_pos (r2 := r2) h1
  have hs := Real.sq_sqrt hd.le
  have h0 := Real.sqrt_nonneg ((r1 + r2) ^ 2 - 4 * r2)
  set q := Real.sqrt ((r1 + r2) ^ 2 - 4 * r2)
  have hq : (r1 + r2 - 2) ^ 2 < q ^ 2 := by rw [hs]; nlinarith
  have habs : |r1 + r2 - 2| < q := abs_lt_of_sq_lt_sq hq h0
  rw [abs_lt] at habs
  unfold lam1 lam2
  constructor <;> linarith [habs.1, habs.2]

/-- **Woodford (2003), fn. 35, p. 586: exactly one root above one.** If `ρ₁ > 1`,
`z² − (ρ₁+ρ₂)z + ρ₂` has exactly one root greater than `1` (namely `λ₂`). -/
theorem fn35_one_root_gt_one {r1 r2 : ℝ} (h1 : 1 < r1) :
    ∃! z : ℝ, 1 < z ∧ z ^ 2 - (r1 + r2) * z + r2 = 0 := by
  obtain ⟨-, -, hf⟩ := lam_factor (r2 := r2) h1
  obtain ⟨hl1, hl2⟩ := fn35_roots_lt_gt (r2 := r2) h1
  refine ⟨lam2 r1 r2, ⟨hl2, by rw [hf]; ring⟩, fun z ⟨hz1, hz⟩ => ?_⟩
  rw [hf] at hz
  rcases mul_eq_zero.mp hz with h | h
  · linarith [sub_eq_zero.mp h]
  · exact sub_eq_zero.mp h

/-- **Woodford (2003), p. 588 ("necessarily satisfy 0 < λ₁ < 1 < λ₂").** With `ρ₁ > 1` and
`ρ₂ > 0` (as in (3.8)), `0 < λ₁ < 1 < λ₂`. -/
theorem fn35_roots {r1 r2 : ℝ} (h1 : 1 < r1) (h2 : 0 < r2) :
    0 < lam1 r1 r2 ∧ lam1 r1 r2 < 1 ∧ 1 < lam2 r1 r2 := by
  obtain ⟨-, hp, -⟩ := lam_factor (r2 := r2) h1
  obtain ⟨hl1, hl2⟩ := fn35_roots_lt_gt (r2 := r2) h1
  refine ⟨?_, hl1, hl2⟩
  by_contra hc
  push Not at hc
  nlinarith

/-- Woodford (2003), (3.8), (3.10), p. 588: for the optimal coefficients the roots solve
`βz² − (1 + β + κσ)z + 1 = 0` (so `λ₁λ₂ = β⁻¹` and `(1 − λ₁)(1 − λ₂) = −κσ/β`). -/
theorem lam_model {β σ κ : ℝ} (hβ0 : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    lam1 (rho1 β σ κ) (rho2 β) + lam2 (rho1 β σ κ) (rho2 β) = (1 + β + κ * σ) / β ∧
      lam1 (rho1 β σ κ) (rho2 β) * lam2 (rho1 β σ κ) (rho2 β) = β⁻¹ ∧
      (1 - lam1 (rho1 β σ κ) (rho2 β)) * (1 - lam2 (rho1 β σ κ) (rho2 β)) = -(κ * σ / β) := by
  have h1 : 1 < rho1 β σ κ := by
    unfold rho1
    have : 0 < κ * σ / β := by positivity
    linarith
  obtain ⟨hs, hp, -⟩ := lam_factor (r2 := rho2 β) h1
  refine ⟨?_, hp, ?_⟩
  · rw [hs]
    unfold rho1 rho2
    field_simp
    ring
  · have : (1 - lam1 (rho1 β σ κ) (rho2 β)) * (1 - lam2 (rho1 β σ κ) (rho2 β)) =
        1 - (lam1 (rho1 β σ κ) (rho2 β) + lam2 (rho1 β σ κ) (rho2 β))
          + lam1 (rho1 β σ κ) (rho2 β) * lam2 (rho1 β σ κ) (rho2 β) := by ring
    rw [this, hs, hp]
    unfold rho1 rho2
    ring

/-! ### The numbers of p. 586 -/

/-- **Woodford (2003), p. 586: the optimal coefficients at the calibration of Table 6.1.** With
`β = .99`, `σ = 1/.16`, `κ = .024` and `λ_i = .236` (the ZLB-adjusted weight of Ch. 6, p. 434;
survey E10), `λ_x = κ/θ = .024/7.88` (quarterly): `ρ₁ ∈ (1.15, 1.152)`, `ρ₂ ∈ (1.010, 1.0102)`,
`φ_π ∈ (.635, .636)`, `φ_x ∈ (.322, .323)` — the book prints `1.15`, `1.01`, `.64`, `.33`. -/
theorem p586_numbers :
    (1.15 : ℝ) < rho1 0.99 (1 / 0.16) 0.024 ∧ rho1 0.99 (1 / 0.16) 0.024 < 1.152 ∧
      (1.01 : ℝ) < rho2 0.99 ∧ rho2 0.99 < 1.0102 ∧
      (0.635 : ℝ) < phiPi (1 / 0.16) 0.024 0.236 ∧ phiPi (1 / 0.16) 0.024 0.236 < 0.636 ∧
      (0.322 : ℝ) < phiX (1 / 0.16) (0.024 / 7.88) 0.236 ∧
        phiX (1 / 0.16) (0.024 / 7.88) 0.236 < 0.323 := by
  unfold rho1 rho2 phiPi phiX
  norm_num

/-- Woodford (2003), p. 586 (correction): the printed `φ_x = .33` does not round from the
recomputed value: with `λ_x = κ/θ` it is `.3226…`, and with `λ_x = .048/16` (Table 6.1's annual
weight, quarterly) it is `.3178…`; both are more than `.005` below `.33`. -/
theorem p586_phiX_not_033 :
    phiX (1 / 0.16) (0.024 / 7.88) 0.236 < 0.33 - 0.005 ∧
      phiX (1 / 0.16) (0.048 / 16) 0.236 < 0.33 - 0.005 := by
  unfold phiX
  norm_num

/-- Woodford (2003), p. 586 with Table 6.1's printed `λ_i = .077` (survey E10): `φ_π = κσ/λ_i`
would be `1.948…`, not `.64`; the printed value requires `λ_i = .236`. -/
theorem p586_phiPi_table_value :
    (1.94 : ℝ) < phiPi (1 / 0.16) 0.024 0.077 ∧ phiPi (1 / 0.16) 0.024 0.077 < 1.95 := by
  unfold phiPi
  norm_num

/-- **Woodford (2003), App. G.4, pp. 721–722: the Blanchard–Kahn count.** The characteristic
polynomial `det(Ā − µĪ) = −βµ p(µ)` of (G.10)–(G.11) has, up to the constant `−β`, the roots of
`µ p(µ)`; exactly `n_Z = 3` of them (with multiplicity) lie in the open unit disc — the root `0`
and the two stable roots of `p` — matching the three predetermined variables
`(x_{t−1}, i_{t−1}, i_{t−2})`. -/
theorem charPoly_insideCard_eq_three {β σ κ lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hlx : 0 ≤ lx) (hli : 0 < li) :
    insideCard (Polynomial.X * pGPoly β σ κ lx li) = 3 := by
  have hne : pGPoly β σ κ lx li ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    rw [pGPoly, eval_palinPoly, Polynomial.eval_zero] at this
    exact palin_zero hβ0.ne' _ _ this
  have h2 := pG_insideCard_eq_two hβ0 hβ1 hσ hκ hlx hli
  unfold insideCard at h2 ⊢
  rw [Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero hne), Polynomial.roots_X,
    Multiset.filter_add, Multiset.card_add, h2, Multiset.filter_singleton]
  simp

/-! ### Uniqueness of the optimum under a faithful expectation system -/

/-- **Woodford (2003), §3.1 (uniqueness of the optimum by strict convexity), any faithful
expectation system with the pull-out property.** A bounded feasible plan with the same initial
values (3.6) and the same expected discounted loss as a plan satisfying the first-order conditions
(3.3)–(3.5) with bounded adapted multipliers coincides with it. -/
theorem unique_optimum (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut) (hfa : Faithful 𝔼)
    {rn u π x i φ1 φ2 : ℕ → Ω → ℝ} {φ1h φ2h : ℝ}
    (hf : Feasible 𝔼 c rn u π x i) (hfoc : FOC c π x i φ1 φ2 φ1h φ2h)
    (hφ1a : 𝔼.Adapted φ1) (hφ2a : 𝔼.Adapted φ2)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (hib : BoundedProc i)
    (hφ1b : BoundedProc φ1) (hφ2b : BoundedProc φ2)
    {π' x' i' : ℕ → Ω → ℝ} (hf' : Feasible 𝔼 c rn u π' x' i')
    (hπb' : BoundedProc π') (hxb' : BoundedProc x') (hib' : BoundedProc i')
    (h0 : π' 0 = π 0) (hx0 : x' 0 = x 0) (hJ : Jloss 𝔼 c π' x' i' = Jloss 𝔼 c π x i) :
    π' = π ∧ x' = x ∧ i' = i := by
  have hc' := hc
  obtain ⟨hβ0, hβ1, -, -, hlx, hli⟩ := hc'
  set Sq : ℕ → Ω → ℝ := fun t ω' => (π' t ω' - π t ω') ^ 2 + c.lx * (x' t ω' - x t ω') ^ 2
    + c.li * (i' t ω' - i t ω') ^ 2 with hSq
  have hS0 : ∀ t, 0 ≤ Sq t := fun t ω' => by simp only [hSq]; positivity
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨Mπ', hMπ'⟩ := hπb'
  obtain ⟨Mx', hMx'⟩ := hxb'
  obtain ⟨Mi', hMi'⟩ := hib'
  have hSb : ∀ t ω', |Sq t ω'| ≤
      (Mπ' + Mπ) ^ 2 + c.lx * (Mx' + Mx) ^ 2 + c.li * (Mi' + Mi) ^ 2 := by
    intro t ω'
    have a := (abs_sub (π' t ω') (π t ω')).trans (add_le_add (hMπ' t ω') (hMπ t ω'))
    have b := (abs_sub (x' t ω') (x t ω')).trans (add_le_add (hMx' t ω') (hMx t ω'))
    have d := (abs_sub (i' t ω') (i t ω')).trans (add_le_add (hMi' t ω') (hMi t ω'))
    have a2 := sq_le_sq' (abs_le.mp a).1 (abs_le.mp a).2
    have b2 := sq_le_sq' (abs_le.mp b).1 (abs_le.mp b).2
    have d2 := sq_le_sq' (abs_le.mp d).1 (abs_le.mp d).2
    rw [abs_of_nonneg (hS0 t ω')]
    simp only [hSq]
    nlinarith [mul_le_mul_of_nonneg_left b2 hlx.le, mul_le_mul_of_nonneg_left d2 hli.le]
  have hE0 : ∀ t, 𝔼.E 0 (Sq t) = 0 := by
    intro t
    funext ω
    have hid := lagrangian_identity 𝔼 c hc hpo hf hfoc hφ1a hφ2a ⟨Mπ, hMπ⟩ ⟨Mx, hMx⟩
      ⟨Mi, hMi⟩ hφ1b hφ2b hf' ⟨Mπ', hMπ'⟩ ⟨Mx', hMx'⟩ ⟨Mi', hMi'⟩ h0 hx0 ω
    rw [hJ] at hid
    have hsum0 : ∑' s, c.β ^ s * 𝔼.E 0 (Sq s) ω = 0 := by linarith
    have hnn : ∀ s, 0 ≤ c.β ^ s * 𝔼.E 0 (Sq s) ω := by
      intro s
      refine mul_nonneg (pow_nonneg hβ0.le s) ?_
      have hm := 𝔼.mono 0 (hS0 s)
      rw [show (0 : Ω → ℝ) = fun _ => (0 : ℝ) from rfl, 𝔼.const] at hm
      exact hm ω
    have hzero := (hasSum_zero_iff_of_nonneg hnn).mp
      (hsum0 ▸ (summable_disc 𝔼 hβ0.le hβ1 hSb ω).hasSum)
    have := congrFun hzero t
    simp only [Pi.zero_apply] at this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero t hβ0.ne')
    · exact h
  have hSt : ∀ t ω', Sq t ω' = 0 := fun t ω' =>
    congrFun (hfa 0 (Sq t) (hS0 t) (hE0 t)) ω'
  have hcomp : ∀ t ω', π' t ω' = π t ω' ∧ x' t ω' = x t ω' ∧ i' t ω' = i t ω' := by
    intro t ω'
    have h := hSt t ω'
    simp only [hSq] at h
    have q1 := sq_nonneg (π' t ω' - π t ω')
    have q2 := mul_nonneg hlx.le (sq_nonneg (x' t ω' - x t ω'))
    have q3 := mul_nonneg hli.le (sq_nonneg (i' t ω' - i t ω'))
    have e1 : (π' t ω' - π t ω') ^ 2 = 0 := by linarith
    have e2' : c.lx * (x' t ω' - x t ω') ^ 2 = 0 := by linarith
    have e3' : c.li * (i' t ω' - i t ω') ^ 2 = 0 := by linarith
    have e2 : (x' t ω' - x t ω') ^ 2 = 0 := (mul_eq_zero.mp e2').resolve_left hlx.ne'
    have e3 : (i' t ω' - i t ω') ^ 2 = 0 := (mul_eq_zero.mp e3').resolve_left hli.ne'
    exact ⟨sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e1),
      sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e2),
      sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp e3)⟩
  exact ⟨funext fun t => funext fun ω' => (hcomp t ω').1,
    funext fun t => funext fun ω' => (hcomp t ω').2.1,
    funext fun t => funext fun ω' => (hcomp t ω').2.2⟩

/-- **Woodford (2003), §3.1, p. 585: the rule equilibrium is the unique optimum** (faithful
expectation system with the pull-out property). Every plan that is optimal given the rule
equilibrium's initial values `π₀, x₀` (the commitments (3.6)) coincides with the bounded
equilibrium under the rule (3.7)–(3.9). -/
theorem rule_eqm_unique_optimum (c : Calib) (hc : c.Adm) (hpo : 𝔼.PullOut) (hfa : Faithful 𝔼)
    {rn u π x i : ℕ → Ω → ℝ} {xm1 im1 im2 : ℝ} (he : RuleEqm 𝔼 c rn u xm1 im1 im2 π x i)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i) (hπb : BoundedProc π)
    (hxb : BoundedProc x) (hib : BoundedProc i) {π' x' i' : ℕ → Ω → ℝ}
    (hopt : OptimalGiven 𝔼 c rn u (π 0) (x 0) π' x' i') : π' = π ∧ x' = x ∧ i' = i := by
  have hc' := hc
  obtain ⟨hβ0, -, hσ, hκ, -, hli⟩ := hc'
  have hfoc : FOC c π x i (mult1 c i) (mult2 c im1 x i) (mult1h c im1) (mult2h c xm1 im1 im2) :=
    fun t => ⟨(rule_iff_foc3 c hβ0.ne' hσ.ne' hκ.ne' hli.ne' xm1 im1 im2 π x i t).mp (he t).2.2,
      foc4_mult c hκ.ne' im1 x i t, foc5_mult c hσ.ne' i t⟩
  obtain ⟨M, hM⟩ := PhiOf_bounded c im1 hxb hib
  have hb1 : BoundedProc (mult1 c i) := ⟨M, fun t ω => hM t 0 ω⟩
  have hb2 : BoundedProc (mult2 c im1 x i) := ⟨M, fun t ω => hM t 1 ω⟩
  obtain ⟨hf', ⟨hπa', hxa', hia'⟩, ⟨hπb', hxb', hib'⟩, h0, hx0, hmin'⟩ := hopt
  obtain ⟨hf, -, -, -, -, hmin⟩ := rule_eqm_optimal 𝔼 c hc hpo he hπa hxa hia hπb hxb hib
  have hJ : Jloss 𝔼 c π' x' i' = Jloss 𝔼 c π x i :=
    le_antisymm (hmin' π x i hf ⟨hπa, hxa, hia⟩ ⟨hπb, hxb, hib⟩ rfl rfl)
      (hmin π' x' i' hf' ⟨hπa', hxa', hia'⟩ ⟨hπb', hxb', hib'⟩ h0 hx0)
  exact unique_optimum 𝔼 c hc hpo hfa hf hfoc (mult1_adapted 𝔼 c hia)
    (mult2_adapted 𝔼 c im1 hxa hia) hπb hxb hib hb1 hb2 hf' hπb' hxb' hib' h0 hx0 hJ

end Woodford.OptimalPolicyRules.IRuleBasic
