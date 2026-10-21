/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Noninertial
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The optimal Taylor rule

Woodford (2003), *Interest and Prices*, Chapter 7, §3.2 (pp. 513–517), with the determinacy
theory of Chapter 4 (Prop. 4.3) and Appendix F.4.

## Main results

* The model (2.1), (2.23) under the Taylor rule (3.1) is a two-dimensional forward system in
  `(π − π̄, x − x̄)` with cost-push forcing (fn. 31) (`taylorEqm_iff_solves`), and
  **(3.9) / Prop. 4.3 restated**: equilibrium is determinate — exactly one bounded adapted
  equilibrium for every bounded adapted `(u, rⁿ)` — iff `φ_π + (1 − β) φ_x/(4κ) > 1`
  (`taylor_determinate_iff`), for `φ_π, φ_x ≥ 0`.
* **Proposition 7.12**: with `ρ_r = ρ_u = ρ` and (3.10), the coefficients (3.11)–(3.12) are
  positive and satisfy (3.9) (`prop_7_12_coeffs`); the Taylor rule reproduces the F.4 response
  coefficients (`rule_matches_f4_u`, `rule_matches_f4_r`), so the optimal noninertial plan is an
  equilibrium under it, and the unique one (`prop_7_12`); every other determinate Taylor rule has
  an equilibrium of the form (3.6) (`taylor_eqm_plan2`) with no smaller `L^stab`
  (`prop_7_12_optimal`). (3.10)'s upper bound is equivalent to (3.9) (`upper_iff_taylorPrinciple`).
* p. 515, `ρ_r ≠ ρ_u` (confirmed): the set `RuleSet` of `(ρ_r, ρ_u)` at which the Taylor
  coefficients consistent with the optimal noninertial plan exist, are positive and satisfy (3.9)
  is open (`ruleSet_open`), contains every diagonal point satisfying (3.10) (`diag_mem_ruleSet`)
  and off-diagonal points in `(0, 1)²` (`exists_offdiag_ruleSet`); there Prop. 7.12 holds
  (`prop_7_12_general`, `prop_7_12_optimal_general`).
* Survey E9 (confirmed): the p. 515 claim "`φ_π > 1` as long as `λᵢ` satisfies the upper bound"
  is false: `phiPi_gt_one_iff` and the counterexample `e9_counterexample` (`λᵢ = .236`, `ρ = .18`).
* (3.10) holds exactly on an interval `(ρ̲, ρ̄)` with `0 < ρ̄ < 1` (`prop_7_12_interval`); at the
  calibration of fn. 32 (`λᵢ = .236`, quarterly `λₓ = .003`) `ρ̲ ∈ [.170, .171)`,
  `ρ̄ ∈ (.683, .684]` (`fn32_interval`), but with Table 6.1's `λᵢ = .077`, or the annualised
  `λₓ = .048`, (3.10) already holds at `ρ = .1` (`e10_table61`, `e10_annual_lx`) (survey E10).
* (3.13)–(3.14): the forecast-based rule with `φ_y = ρ^{−k} φ̄_y` is consistent with the optimal
  noninertial plan (`forecast_rule_consistent`).
* **Proposition 7.13** (only cited in the book): a root `λ` of the characteristic polynomial with
  `0 < |λ| ≤ 1` gives a second bounded equilibrium (`indeterminate_of_root`); for `k = 1` the exact
  determinacy criterion (`forecast1_determinate_iff`); for every `k ≥ 1`, if the leading
  coefficient exceeds one in modulus a root lies inside the unit disc (Vieta,
  `exists_root_inside`), so the rule is indeterminate for all `k` beyond an explicit critical
  value (`prop_7_13`). Footnote 37 at the calibration: indeterminate for every `k ≥ 1` and every
  `ρ ∈ (0, 1)` with `D(ρ) > 0` (`fn37`).

The two-dimensional Blanchard–Kahn tools (`pow_entry_bound`, `fsolves_exists`,
`fwd_existsUnique`, …) are restated from the Woodford Chapter 4 project (`BlanchardKahn`,
`Determinacy2`).
-/

namespace Woodford.GainsFromCommitment.OptimalTaylor

open Filter Topology
open Noninertial (AS IS taylorRule plan2_iff Nondeg2)
open VarianceFrontier (plan2 plan2_apply)

/-- Woodford (2003), p. 670 (Ch. 4 copy), fn. 1 (Blanchard–Kahn, the tool): if every complex
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

/-- Woodford (2003), p. 670 (Ch. 4 copy): A matrix acting on a vector of random variables: `(M
a)_i = ∑_j M_{ij} a_j`. -/
def rvMul {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ) :
    Fin n → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Woodford (2003), p. 670 (Ch. 4 copy) (tool): matrices act on vectors of random variables
compatibly with multiplication. -/
theorem rvMul_rvMul {Ω : Type*} {n m l : ℕ} (M : Matrix (Fin n) (Fin m) ℝ)
    (N : Matrix (Fin m) (Fin l) ℝ) (a : Fin l → Ω → ℝ) :
    rvMul M (rvMul N a) = rvMul (M * N) a := by
  funext i
  simp only [rvMul, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Woodford (2003), p. 670 (Ch. 4 copy) (tool): additivity of the action. -/
theorem rvMul_add {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a + b) = rvMul M a + rvMul M b := by
  funext i
  simp only [rvMul, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Woodford (2003), p. 670 (Ch. 4 copy) (tool): the action respects subtraction. -/
theorem rvMul_sub {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m → Ω → ℝ) :
    rvMul M (a - b) = rvMul M a - rvMul M b := by
  funext i
  simp only [rvMul, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Woodford (2003), p. 670 (Ch. 4 copy) (tool): the identity matrix acts trivially. -/
theorem rvMul_one {Ω : Type*} {n : ℕ} (a : Fin n → Ω → ℝ) : rvMul 1 a = a := by
  funext i
  simp [rvMul, Matrix.one_apply]

/-- Woodford (2003), p. 670 (Ch. 4 copy) (tool): the action on the zero vector. -/
theorem rvMul_zero {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) :
    rvMul M (0 : Fin m → Ω → ℝ) = 0 := by
  funext i
  simp [rvMul]

/-- Woodford (2003), p. 670 (Ch. 4 copy) (tool): the action, pointwise. -/
theorem rvMul_apply {Ω : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) (ω : Ω) : rvMul M a i ω = ∑ j, M i j * a j ω := by
  simp [rvMul, Finset.sum_apply]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 670 (Ch. 4 copy) (tool): `E_t` commutes with constant matrices. -/
theorem E_rvMul {n m : ℕ} (t : ℕ) (M : Matrix (Fin n) (Fin m) ℝ) (a : Fin m → Ω → ℝ)
    (i : Fin n) : 𝔼.E t (rvMul M a i) = rvMul M (fun j => 𝔼.E t (a j)) i := by
  simp only [rvMul, map_sum, map_smul]

/-- Woodford (2003), p. 670 (Ch. 4 copy): A vector process solves the forward system `s_t = K E_t
s_{t+1} + w_t`. -/
def FSolves {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (w s : ℕ → Fin n → Ω → ℝ) : Prop :=
  ∀ t, s t = rvMul K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Woodford (2003), p. 670 (Ch. 4 copy): A vector process is adapted. -/
def VAdapted {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Woodford (2003), p. 670 (Ch. 4 copy): A vector process is bounded. -/
def VBounded {n : ℕ} (s : ℕ → Fin n → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M

/-- Woodford (2003), p. 670 (Ch. 4 copy): Iterating a homogeneous forward system: `d_t = Kᵏ E_t
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

/-- Woodford (2003), p. 670 (Ch. 4 copy): Bound for `Kᵏ` acting on a bounded vector. -/
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

/-- Woodford (2003), p. 670 (Ch. 4 copy), fn. 1 (Blanchard–Kahn): if the powers of `K` decay
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

/-- Woodford (2003), p. 670 (Ch. 4 copy), fn. 1 (Blanchard–Kahn): if the powers of `K` decay
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


/-! ### Determinacy at the level of the model (restated from the Chapter 4 project) -/

/-- Woodford (2003), Ch. 4, §2.2, p. 252 and Ch. 7, p. 513 (determinacy of equilibrium): for every
bounded adapted cost-push disturbance `u` and natural rate `rⁿ` the model has exactly one bounded
adapted equilibrium `(π, x)`. -/
def ModelDet (Eqm : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop) : Prop :=
  ∀ u rn : ℕ → Ω → ℝ, BoundedProc u → BoundedProc rn → 𝔼.Adapted u → 𝔼.Adapted rn →
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), BoundedProc p.1 ∧ BoundedProc p.2 ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2 ∧ Eqm u rn p.1 p.2

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: the deviation vector `z_t = (π_t − p₀, x_t − x₀)`
(restated from the Chapter 4 project). -/
def devStack (π x : ℕ → Ω → ℝ) (p0 x0 : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![π t - fun _ => p0, x t - fun _ => x0]

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: the deviation vector of bounded processes is bounded. -/
theorem devStack_bounded {π x : ℕ → Ω → ℝ} (h1 : BoundedProc π) (h2 : BoundedProc x)
    (p0 x0 : ℝ) : BoundedVec (devStack π x p0 x0) := by
  obtain ⟨M₁, hM₁⟩ := h1
  obtain ⟨M₂, hM₂⟩ := h2
  refine ⟨M₁ + M₂ + |p0| + |x0|, fun t i ω => ?_⟩
  have hp := abs_nonneg p0
  have hx := abs_nonneg x0
  have h1' := (abs_nonneg _).trans (hM₁ t ω)
  have h2' := (abs_nonneg _).trans (hM₂ t ω)
  fin_cases i
  · simp only [devStack, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
    exact (abs_sub _ _).trans (by linarith [hM₁ t ω])
  · simp only [devStack, Fin.mk_one, Matrix.cons_val_one]
    exact (abs_sub _ _).trans (by linarith [hM₂ t ω])

/-- Woodford (2003), (C.19), p. 677: the deviation vector of adapted processes is adapted. -/
theorem devStack_adapted {π x : ℕ → Ω → ℝ} (h1 : 𝔼.Adapted π) (h2 : 𝔼.Adapted x)
    (p0 x0 : ℝ) : 𝔼.AdaptedVec (devStack π x p0 x0) := by
  intro t i
  fin_cases i
  · simp [devStack, map_sub, h1 t, 𝔼.const]
  · simp [devStack, map_sub, h2 t, 𝔼.const]

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: recovering `(π, x)` from the deviation vector. -/
def ofDevStack (p0 x0 : ℝ) (z : ℕ → Fin 2 → Ω → ℝ) : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) :=
  (fun t => z t 0 + fun _ => p0, fun t => z t 1 + fun _ => x0)

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: `devStack` inverts `ofDevStack`. -/
theorem devStack_ofDevStack (p0 x0 : ℝ) (z : ℕ → Fin 2 → Ω → ℝ) :
    devStack (ofDevStack p0 x0 z).1 (ofDevStack p0 x0 z).2 p0 x0 = z := by
  funext t i
  fin_cases i <;> simp [devStack, ofDevStack]

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: `devStack` is injective. -/
theorem devStack_inj {p0 x0 : ℝ} {π x π' x' : ℕ → Ω → ℝ}
    (h : devStack π x p0 x0 = devStack π' x' p0 x0) : π = π' ∧ x = x' := by
  constructor
  · funext t ω
    have := congrFun (congrFun (congrFun h t) 0) ω
    simpa [devStack] using this
  · funext t ω
    have := congrFun (congrFun (congrFun h t) 1) ω
    simpa [devStack] using this

/-- Woodford (2003), (C.19), p. 677: `ofDevStack` of a bounded adapted vector is bounded and
adapted. -/
theorem ofDevStack_bounded_adapted {p0 x0 : ℝ} {z : ℕ → Fin 2 → Ω → ℝ} (hz : BoundedVec z)
    (haz : 𝔼.AdaptedVec z) :
    𝔼.Adapted (ofDevStack p0 x0 z).1 ∧ 𝔼.Adapted (ofDevStack p0 x0 z).2 ∧
      BoundedProc (ofDevStack p0 x0 z).1 ∧ BoundedProc (ofDevStack p0 x0 z).2 := by
  obtain ⟨M, hM⟩ := hz
  refine ⟨fun t => ?_, fun t => ?_, ⟨M + |p0|, fun t ω => ?_⟩, ⟨M + |x0|, fun t ω => ?_⟩⟩
  · simp [ofDevStack, map_add, haz t 0, 𝔼.const]
  · simp [ofDevStack, map_add, haz t 1, 𝔼.const]
  · simpa [ofDevStack] using (abs_add_le _ _).trans (add_le_add (hM t 0 ω) le_rfl)
  · simpa [ofDevStack] using (abs_add_le _ _).trans (add_le_add (hM t 1 ω) le_rfl)

/-- Woodford (2003), Ch. 4, §2.2, pp. 252–254 and App. C.1 (restated from the Chapter 4 project,
with the cost-push disturbance as a second forcing process): if the equilibrium conditions are
equivalent to a forward system `z_t = K E_t z_{t+1} + W_t(u, rⁿ)` in the deviations
`z = (π − p₀, x − x₀)`, the forcing of bounded adapted disturbances is bounded and adapted, and
some bounded adapted disturbances give zero forcing, then the model is determinate iff `K`
satisfies the Schur–Cohn condition. -/
theorem modelDet_iff_of_reduction [Nonempty Ω] {K : Matrix (Fin 2) (Fin 2) ℝ}
    {p0 x0 : ℝ} {Eqm : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop}
    {W : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → ℕ → Fin 2 → Ω → ℝ}
    (hred : ∀ u rn π x, Eqm u rn π x ↔ 𝔼.Solves K (W u rn) (devStack π x p0 x0))
    (hW : ∀ u rn, BoundedProc u → BoundedProc rn → 𝔼.Adapted u → 𝔼.Adapted rn →
      BoundedVec (W u rn) ∧ 𝔼.AdaptedVec (W u rn))
    (hW0 : ∃ u rn, BoundedProc u ∧ BoundedProc rn ∧ 𝔼.Adapted u ∧ 𝔼.Adapted rn ∧
      W u rn = 0) :
    ModelDet 𝔼 Eqm ↔ SchurStable (tr2 K) (det2 K) := by
  constructor
  · intro hdet
    by_contra hA
    obtain ⟨u, rn, h1, h2, h3, h4, hw0⟩ := hW0
    obtain ⟨y, hy, hay, hby, hne⟩ := 𝔼.system_not_unique hA (x := 0) (w := 0)
      (fun t i => by simp) (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
    obtain ⟨p, _, hpu⟩ := hdet u rn h1 h2 h3 h4
    have hsol : ∀ z, 𝔼.Solves K 0 z → BoundedVec z → 𝔼.AdaptedVec z →
        ofDevStack p0 x0 z = p := by
      intro z hz hbz haz
      obtain ⟨a1, a2, b1, b2⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := p0) (x0 := x0) hbz haz
      refine hpu _ ⟨b1, b2, a1, a2, ?_⟩
      rw [hred, devStack_ofDevStack, hw0]
      exact hz
    have e1 := hsol y hy hby hay
    have e2 := hsol 0 (fun t i => by simp) ⟨0, fun t i ω => by simp⟩ (fun t i => by simp)
    apply hne
    rw [← devStack_ofDevStack p0 x0 y, ← devStack_ofDevStack p0 x0 (0 : ℕ → Fin 2 → Ω → ℝ),
      e1, e2]
  · intro hK u rn hu hrn hau harn
    obtain ⟨hwb, hwa⟩ := hW u rn hu hrn hau harn
    obtain ⟨z, ⟨hz, haz, hbz⟩, hzu⟩ := fwd_existsUnique 𝔼 hK hwb hwa
    obtain ⟨a1, a2, b1, b2⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := p0) (x0 := x0) hbz haz
    refine ⟨ofDevStack p0 x0 z, ⟨b1, b2, a1, a2, ?_⟩, fun q ⟨d1, d2, c1, c2, hq⟩ => ?_⟩
    · rw [hred, devStack_ofDevStack]
      exact hz
    · have := hzu (devStack q.1 q.2 p0 x0)
        ⟨(hred _ _ _ _).mp hq, devStack_adapted 𝔼 c1 c2 p0 x0, devStack_bounded d1 d2 p0 x0⟩
      rw [← this]
      obtain ⟨e1, e2⟩ := devStack_inj (devStack_ofDevStack p0 x0 (devStack q.1 q.2 p0 x0))
      exact Prod.ext e1.symm e2.symm

/-! ### The model under the Taylor rule (3.1) and the Taylor principle (3.9) -/

/-- Woodford (2003), (2.1), (2.23) and (3.1), pp. 486, 502, 507: `(π, x)` is an equilibrium under
the Taylor rule `i_t = ī + φ_π (π_t − π̄) + φ_x (x_t − x̄)/4` (the interest rate is then given by
the rule). -/
def TaylorEqm (β σ κ ibar φπ φx πbar xbar : ℝ) (u rn π x : ℕ → Ω → ℝ) : Prop :=
  AS 𝔼 β κ π x u ∧ IS 𝔼 σ π x (taylorRule ibar φπ φx πbar xbar π x) rn

omit 𝔼 in
/-- Woodford (2003), App. C.2, p. 677: `Δ = 1 + σ φ_x/4 + σ κ φ_π`. -/
noncomputable def taylorDelta (σ κ φπ φx : ℝ) : ℝ := 1 + σ * φx / 4 + σ * κ * φπ

omit 𝔼 in
/-- Woodford (2003), eq. (2.18), p. 263 (restated from the Chapter 4 project): the matrix `B` of
the forward form `z_t = B E_t z_{t+1} + w_t` of (2.1), (2.23) under (3.1). -/
noncomputable def taylorB (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx, κ / taylorDelta σ κ φπ φx;
    σ * (1 - β * φπ) / taylorDelta σ κ φπ φx, 1 / taylorDelta σ κ φπ φx]

omit 𝔼 in
/-- Woodford (2003), Ch. 7, fn. 31, p. 513: the forcing of the forward form under (3.1), with the
cost-push disturbance `u` and `e_t = rⁿ_t − ī + π̄`:
`w_t = ((κσ e_t + (1 + σφ_x/4) u_t)/Δ, (σ e_t − σφ_π u_t)/Δ)`. -/
noncomputable def taylorW (σ κ φπ φx ibar πbar : ℝ) (u rn : ℕ → Ω → ℝ) :
    ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![fun ω => (κ * σ * (rn t ω - ibar + πbar) + (1 + σ * φx / 4) * u t ω) /
      taylorDelta σ κ φπ φx,
    fun ω => (σ * (rn t ω - ibar + πbar) - σ * φπ * u t ω) / taylorDelta σ κ φπ φx]

omit 𝔼 in
/-- Woodford (2003), eq. (2.18), p. 263 and fn. 31, p. 513, state by state: under (3.1) the IS
relation and the AS relation with cost-push term are equivalent to the forward form in deviations
from `(π̄, x̄)` (where `κ x̄ = (1 − β) π̄`). `P`, `X` are the expectations of `π`, `x`. -/
theorem taylor_pt {β σ κ φπ φx πbar xb ibar : ℝ} (hxb : κ * xb = (1 - β) * πbar)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {p x P X rn uu r : ℝ}
    (hr : r = ibar + φπ * (p - πbar) + φx * (x - xb) / 4) :
    (x = X - σ * (r - P - rn) ∧ p = κ * x + β * P + uu) ↔
      (p - πbar = taylorB β σ κ φπ φx 0 0 * (P - πbar) + taylorB β σ κ φπ φx 0 1 * (X - xb)
          + (κ * σ * (rn - ibar + πbar) + (1 + σ * φx / 4) * uu) / taylorDelta σ κ φπ φx ∧
        x - xb = taylorB β σ κ φπ φx 1 0 * (P - πbar) + taylorB β σ κ φπ φx 1 1 * (X - xb)
          + (σ * (rn - ibar + πbar) - σ * φπ * uu) / taylorDelta σ κ φπ φx) := by
  subst hr
  simp only [taylorB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  set Δ := taylorDelta σ κ φπ φx with hΔdef
  have hΔe : Δ = 1 + σ * φx / 4 + σ * κ * φπ := rfl
  constructor
  · rintro ⟨h1, h2⟩
    have k1 : Δ * (x - xb) = σ * (1 - β * φπ) * (P - πbar) + (X - xb)
        + (σ * (rn - ibar + πbar) - σ * φπ * uu) := by
      rw [hΔe]; linear_combination h1 - σ * φπ * h2 - σ * φπ * hxb
    have k2 : Δ * (p - πbar) = (β + σ * κ + β * σ * φx / 4) * (P - πbar) + κ * (X - xb)
        + (κ * σ * (rn - ibar + πbar) + (1 + σ * φx / 4) * uu) := by
      rw [hΔe]
      linear_combination κ * h1 + (1 + σ * φx / 4) * h2 + (1 + σ * φx / 4) * hxb
    constructor
    · apply mul_left_cancel₀ hΔ
      rw [k2]
      field_simp
    · apply mul_left_cancel₀ hΔ
      rw [k1]
      field_simp
  · rintro ⟨h1, h2⟩
    have k2 : Δ * (p - πbar) = (β + σ * κ + β * σ * φx / 4) * (P - πbar) + κ * (X - xb)
        + (κ * σ * (rn - ibar + πbar) + (1 + σ * φx / 4) * uu) := by
      rw [h1]; field_simp
    have k1 : Δ * (x - xb) = σ * (1 - β * φπ) * (P - πbar) + (X - xb)
        + (σ * (rn - ibar + πbar) - σ * φπ * uu) := by
      rw [h2]; field_simp
    have e : Δ * (p - κ * x - β * P - uu) = 0 := by
      rw [hΔe] at k1 k2 ⊢
      linear_combination k2 - κ * k1 - (1 + σ * φx / 4 + σ * κ * φπ) * hxb
    have hn : p = κ * x + β * P + uu := by
      have := (mul_eq_zero.mp e).resolve_left hΔ
      linarith
    refine ⟨?_, hn⟩
    rw [hΔe] at k1
    linear_combination k1 + σ * φπ * hn + σ * φπ * hxb

/-- Woodford (2003), eq. (C.19), p. 677 (restated from the Chapter 4 project): the forward system
in the deviations, written out date by date and state by state. -/
theorem solves_dev_iff (K : Matrix (Fin 2) (Fin 2) ℝ) (W : ℕ → Fin 2 → Ω → ℝ) (p0 x0 : ℝ)
    (π x : ℕ → Ω → ℝ) :
    𝔼.Solves K W (devStack π x p0 x0) ↔ ∀ t ω,
      (π t ω - p0 = K 0 0 * (𝔼.E t (π (t + 1)) ω - p0)
        + K 0 1 * (𝔼.E t (x (t + 1)) ω - x0) + W t 0 ω) ∧
      (x t ω - x0 = K 1 0 * (𝔼.E t (π (t + 1)) ω - p0)
        + K 1 1 * (𝔼.E t (x (t + 1)) ω - x0) + W t 1 ω) := by
  simp only [ExpectationSystem.Solves, Fin.forall_fin_two, devStack, funext_iff, ← forall_and]
  simp [map_sub, 𝔼.const]

/-- Woodford (2003), eq. (2.1), p. 486, state by state. -/
theorem AS_iff (β κ : ℝ) (π x u : ℕ → Ω → ℝ) :
    AS 𝔼 β κ π x u ↔ ∀ t ω, π t ω = κ * x t ω + β * 𝔼.E t (π (t + 1)) ω + u t ω := by
  simp only [AS, funext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), eq. (2.23), p. 502, state by state. -/
theorem IS_iff (σ : ℝ) (π x i rn : ℕ → Ω → ℝ) :
    IS 𝔼 σ π x i rn ↔ ∀ t ω,
      x t ω = 𝔼.E t (x (t + 1)) ω - σ * (i t ω - 𝔼.E t (π (t + 1)) ω - rn t ω) := by
  simp only [IS, funext_iff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), eq. (2.18), p. 263 and fn. 31, p. 513: under the Taylor rule (3.1) the model
(2.1), (2.23) is exactly the forward system `z_t = B E_t z_{t+1} + w_t` in the deviations
`z = (π − π̄, x − x̄)`, provided `κ x̄ = (1 − β) π̄`. -/
theorem taylorEqm_iff_solves {β σ κ φπ φx πbar xbar ibar : ℝ} (hxb : κ * xbar = (1 - β) * πbar)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) (u rn π x : ℕ → Ω → ℝ) :
    TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u rn π x ↔
      𝔼.Solves (taylorB β σ κ φπ φx) (taylorW σ κ φπ φx ibar πbar u rn)
        (devStack π x πbar xbar) := by
  rw [solves_dev_iff, TaylorEqm, AS_iff, IS_iff, ← forall_and]
  refine forall_congr' fun t => ?_
  rw [← forall_and]
  refine forall_congr' fun ω => ?_
  rw [and_comm]
  simp only [taylorW, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact taylor_pt hxb hΔ (by simp [taylorRule])

omit 𝔼 in
/-- Woodford (2003), App. C.2, p. 677: `Δ ≥ 1` for `φ_π, φ_x ≥ 0`. -/
theorem one_le_taylorDelta {σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) : 1 ≤ taylorDelta σ κ φπ φx := by
  unfold taylorDelta
  have h1 : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
  have h2 : 0 ≤ σ * κ * φπ := mul_nonneg (mul_nonneg hσ.le hκ.le) hφπ
  linarith

omit 𝔼 in
/-- Woodford (2003), eq. (3.9), p. 514: the left-hand side `φ_π + (1 − β) φ_x/(4κ)` of the
Taylor principle. -/
noncomputable def taylorLHS (β κ φπ φx : ℝ) : ℝ := φπ + (1 - β) * φx / (4 * κ)

omit 𝔼 in
/-- Woodford (2003), App. C.2, p. 677 (direct proof): for `φ_π, φ_x ≥ 0` the matrix `B` satisfies
the Schur–Cohn condition iff the Taylor principle (3.9) holds. Here `tr B = (1 + β + σκ +
βσφ_x/4)/Δ`, `det B = β/Δ`, and `|tr B| < 1 + det B` reduces to (3.9). -/
theorem taylorB_schurStable_iff {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    SchurStable (tr2 (taylorB β σ κ φπ φx)) (det2 (taylorB β σ κ φπ φx)) ↔
      1 < taylorLHS β κ φπ φx := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hΔ0 : 0 < taylorDelta σ κ φπ φx := by linarith
  have htr : tr2 (taylorB β σ κ φπ φx) =
      (1 + β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx := by
    simp only [taylorB, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have hdet : det2 (taylorB β σ κ φπ φx) = β / taylorDelta σ κ φπ φx := by
    simp only [taylorB, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    unfold taylorDelta
    ring
  unfold SchurStable
  rw [htr, hdet]
  have hT : 0 < (1 + β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx := by positivity
  have hD : 0 < β / taylorDelta σ κ φπ φx := by positivity
  rw [abs_of_pos hT, abs_of_pos hD]
  have hD1 : β / taylorDelta σ κ φπ φx < 1 := by
    rw [div_lt_one hΔ0]; linarith
  rw [show 1 + β / taylorDelta σ κ φπ φx = (taylorDelta σ κ φπ φx + β) / taylorDelta σ κ φπ φx
    by field_simp, div_lt_div_iff_of_pos_right hΔ0]
  simp only [hD1, true_and]
  have key : taylorDelta σ κ φπ φx + β - (1 + β + σ * κ + β * σ * φx / 4) =
      σ * κ * (taylorLHS β κ φπ φx - 1) := by
    unfold taylorDelta taylorLHS
    field_simp
    ring
  have hsk : 0 < σ * κ := mul_pos hσ hκ
  constructor
  · intro h
    have : 0 < σ * κ * (taylorLHS β κ φπ φx - 1) := by linarith
    have := (pos_iff_pos_of_mul_pos this).mp hsk
    linarith
  · intro h
    have : 0 < σ * κ * (taylorLHS β κ φπ φx - 1) := mul_pos hsk (by linarith)
    linarith

/-- **(3.9) — Proposition 4.3 restated** (Woodford (2003), Ch. 7, p. 513, fn. 31, and Ch. 4,
p. 254, App. C.2): under the Taylor rule (3.1) with `φ_π, φ_x ≥ 0`, `0 < β < 1`, `σ, κ > 0` (and
the rule's `x̄` consistent with its `π̄`, `κ x̄ = (1 − β) π̄`), equilibrium is determinate — for
every bounded adapted `(u, rⁿ)` there is exactly one bounded adapted `(π, x)` — iff
`φ_π + (1 − β) φ_x/(4κ) > 1`. -/
theorem taylor_determinate_iff [Nonempty Ω] {β σ κ φπ φx πbar xbar ibar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hxb : κ * xbar = (1 - β) * πbar) :
    ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar) ↔ 1 < taylorLHS β κ φπ φx := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have hΔ0 : taylorDelta σ κ φπ φx ≠ 0 := by linarith
  rw [← taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx]
  refine modelDet_iff_of_reduction 𝔼 (W := fun u rn => taylorW σ κ φπ φx ibar πbar u rn)
    (fun u rn π x => taylorEqm_iff_solves 𝔼 hxb hΔ0 u rn π x) ?_ ?_
  · intro u rn hu hrn hau harn
    obtain ⟨M₁, hM₁⟩ := hu
    obtain ⟨M₂, hM₂⟩ := hrn
    set Δ := taylorDelta σ κ φπ φx
    have hΔp : 0 < Δ := by linarith
    refine ⟨⟨(|κ * σ| * (M₂ + |ibar| + |πbar|) + |1 + σ * φx / 4| * M₁ +
        |σ| * (M₂ + |ibar| + |πbar|) + |σ * φπ| * M₁) / Δ, fun t i ω => ?_⟩, fun t i => ?_⟩
    · have he : |rn t ω - ibar + πbar| ≤ M₂ + |ibar| + |πbar| := by
        calc |rn t ω - ibar + πbar| ≤ |rn t ω - ibar| + |πbar| := abs_add_le _ _
          _ ≤ |rn t ω| + |ibar| + |πbar| := by gcongr; exact abs_sub _ _
          _ ≤ M₂ + |ibar| + |πbar| := by gcongr; exact hM₂ t ω
      have hu' := hM₁ t ω
      have a1 : |κ * σ * (rn t ω - ibar + πbar)| ≤ |κ * σ| * (M₂ + |ibar| + |πbar|) := by
        rw [abs_mul]; gcongr
      have a2 : |(1 + σ * φx / 4) * u t ω| ≤ |1 + σ * φx / 4| * M₁ := by rw [abs_mul]; gcongr
      have a3 : |σ * (rn t ω - ibar + πbar)| ≤ |σ| * (M₂ + |ibar| + |πbar|) := by
        rw [abs_mul]; gcongr
      have a4 : |σ * φπ * u t ω| ≤ |σ * φπ| * M₁ := by rw [abs_mul]; gcongr
      have p1 : 0 ≤ |κ * σ| * (M₂ + |ibar| + |πbar|) := (abs_nonneg _).trans a1
      have p2 : 0 ≤ |(1 + σ * φx / 4)| * M₁ := (abs_nonneg _).trans a2
      have p3 : 0 ≤ |σ| * (M₂ + |ibar| + |πbar|) := (abs_nonneg _).trans a3
      have p4 : 0 ≤ |σ * φπ| * M₁ := (abs_nonneg _).trans a4
      fin_cases i
      · simp only [taylorW, Fin.zero_eta, Matrix.cons_val_zero]
        rw [abs_div, abs_of_pos hΔp]
        gcongr
        exact (abs_add_le _ _).trans (by linarith)
      · simp only [taylorW, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [abs_div, abs_of_pos hΔp]
        gcongr
        exact (abs_sub _ _).trans (by linarith)
    · have e0 : (fun ω => (κ * σ * (rn t ω - ibar + πbar) + (1 + σ * φx / 4) * u t ω) / Δ) =
          (κ * σ / Δ) • rn t + (fun _ => κ * σ * (πbar - ibar) / Δ) +
            ((1 + σ * φx / 4) / Δ) • u t := by
        funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have e1 : (fun ω => (σ * (rn t ω - ibar + πbar) - σ * φπ * u t ω) / Δ) =
          (σ / Δ) • rn t + (fun _ => σ * (πbar - ibar) / Δ) + (-(σ * φπ) / Δ) • u t := by
        funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      fin_cases i
      · simp only [taylorW, Fin.zero_eta, Matrix.cons_val_zero]
        rw [e0, map_add, map_add, map_smul, map_smul, 𝔼.const, harn t, hau t]
      · simp only [taylorW, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [e1, map_add, map_add, map_smul, map_smul, 𝔼.const, harn t, hau t]
  · refine ⟨fun _ _ => 0, fun _ _ => ibar - πbar, ⟨0, fun _ _ => by simp⟩,
      ⟨|ibar - πbar|, fun _ _ => le_rfl⟩, fun t => 𝔼.const t 0, fun t => 𝔼.const t _, ?_⟩
    funext t i ω
    fin_cases i <;> simp [taylorW]


/-! ### Proposition 7.12 -/

omit 𝔼 in
/-- Woodford (2003), (3.10), p. 514: `D(ρ) = (1 − βρ)(1 − ρ)/(κσ) − ρ`. -/
noncomputable def Drho (β κ σ ρ : ℝ) : ℝ := (1 - β * ρ) * (1 - ρ) / (κ * σ) - ρ

omit 𝔼 in
/-- Woodford (2003), eq. (3.10), p. 514:
`0 < D(ρ) λᵢ < (1 − β)(1 − βρ) λₓ/κ² + 1`. -/
def Cond310 (β κ σ lx li ρ : ℝ) : Prop :=
  0 < Drho β κ σ ρ * li ∧ Drho β κ σ ρ * li < (1 - β) * (1 - β * ρ) / κ ^ 2 * lx + 1

omit 𝔼 in
/-- Woodford (2003), eq. (3.12), p. 514: `φ_π = [D(ρ)]⁻¹ λᵢ⁻¹`. -/
noncomputable def phiPiStar (β κ σ li ρ : ℝ) : ℝ := (Drho β κ σ ρ)⁻¹ * li⁻¹

omit 𝔼 in
/-- Woodford (2003), eq. (3.12), p. 514: `φ_x/4 = (1 − βρ)(λₓ/κ) φ_π`. -/
noncomputable def phiXStar (β κ σ lx li ρ : ℝ) : ℝ :=
  4 * ((1 - β * ρ) * (lx / κ) * phiPiStar β κ σ li ρ)

omit 𝔼 in
/-- Woodford (2003), p. 515: the Taylor-principle expression at (3.12) is
`φ_π [1 + (1 − β)(1 − βρ) λₓ/κ²]`. -/
theorem taylorLHS_star (β κ σ lx li ρ : ℝ) (hκ : κ ≠ 0) :
    taylorLHS β κ (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ) =
      phiPiStar β κ σ li ρ * ((1 - β) * (1 - β * ρ) / κ ^ 2 * lx + 1) := by
  unfold taylorLHS phiXStar
  field_simp
  ring

omit 𝔼 in
/-- Woodford (2003), p. 515 ("(3.10)'s upper bound ⟺ (3.9)"): when `D(ρ) λᵢ > 0`, the upper
bound in (3.10) holds iff the coefficients (3.12) satisfy the Taylor principle (3.9). -/
theorem upper_iff_taylorPrinciple {β κ σ lx li ρ : ℝ} (hκ : κ ≠ 0)
    (hpos : 0 < Drho β κ σ ρ * li) :
    Drho β κ σ ρ * li < (1 - β) * (1 - β * ρ) / κ ^ 2 * lx + 1 ↔
      1 < taylorLHS β κ (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ) := by
  rw [taylorLHS_star β κ σ lx li ρ hκ]
  have hφ : phiPiStar β κ σ li ρ = (Drho β κ σ ρ * li)⁻¹ := by
    unfold phiPiStar; rw [mul_inv]
  rw [hφ, inv_mul_eq_div, one_lt_div hpos]

omit 𝔼 in
/-- Woodford (2003), p. 515 (survey E9, the correct statement): when `D(ρ) λᵢ > 0`,
`φ_π > 1` iff `D(ρ) λᵢ < 1` — not iff the upper bound of (3.10) holds. -/
theorem phiPi_gt_one_iff {β κ σ li ρ : ℝ} (hpos : 0 < Drho β κ σ ρ * li) :
    1 < phiPiStar β κ σ li ρ ↔ Drho β κ σ ρ * li < 1 := by
  have hφ : phiPiStar β κ σ li ρ = (Drho β κ σ ρ * li)⁻¹ := by
    unfold phiPiStar; rw [mul_inv]
  rw [hφ, one_lt_inv₀ hpos]

omit 𝔼 in
/-- **Proposition 7.12, coefficients** (Woodford (2003), pp. 514–515): under (3.10) with
`λₓ > 0`, `κ > 0`, `βρ < 1`, the coefficients (3.12) satisfy `φ_π > 0`, `φ_x > 0` and the
Taylor principle (3.9). (The lower bound of (3.10) is `φ_π > 0`; the upper bound is (3.9).) -/
theorem prop_7_12_coeffs {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hlx : 0 < lx) (hβρ : β * ρ < 1)
    (h : Cond310 β κ σ lx li ρ) :
    0 < phiPiStar β κ σ li ρ ∧ 0 < phiXStar β κ σ lx li ρ ∧
      1 < taylorLHS β κ (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ) := by
  have hφ : phiPiStar β κ σ li ρ = (Drho β κ σ ρ * li)⁻¹ := by
    unfold phiPiStar; rw [mul_inv]
  have h1 : 0 < phiPiStar β κ σ li ρ := by rw [hφ]; exact inv_pos.mpr h.1
  have ha : 0 < 1 - β * ρ := by linarith
  refine ⟨h1, ?_, (upper_iff_taylorPrinciple hκ.ne' h.1).mp h.2⟩
  unfold phiXStar
  positivity

omit 𝔼 in
/-- Woodford (2003), (3.10)–(3.12): `κσ D(ρ) = γ − ρκσ` with `γ = (1 − ρ)(1 − βρ)` of App. F.4. -/
theorem kappa_sigma_Drho {β κ σ ρ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) :
    κ * σ * Drho β κ σ ρ = Noninertial.gamF4 β ρ - ρ * κ * σ := by
  unfold Drho Noninertial.gamF4
  field_simp

omit 𝔼 in
/-- **Proposition 7.12, the `u` responses** (Woodford (2003), p. 514, using App. F.4): with a
common `ρ` and `D(ρ) λᵢ ≠ 0`, the Taylor rule (3.12) reproduces the F.4 interest-rate response:
`i_u = φ_π π_u + (φ_x/4) x_u`. -/
theorem rule_matches_f4_u {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx)
    (hli : 0 ≤ li) (hD : Drho β κ σ ρ * li ≠ 0) :
    Noninertial.iUF4 β κ σ lx li ρ = phiPiStar β κ σ li ρ * Noninertial.piUF4 β κ σ lx li ρ
      + phiXStar β κ σ lx li ρ / 4 * Noninertial.xUF4 β κ σ lx li ρ := by
  have hh := Noninertial.hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx hli
  have hG := kappa_sigma_Drho (β := β) (ρ := ρ) hκ.ne' hσ.ne'
  have hD0 : Drho β κ σ ρ ≠ 0 := left_ne_zero_of_mul hD
  have hli0 : li ≠ 0 := right_ne_zero_of_mul hD
  have hσ' := hσ.ne'
  have hκ' := hκ.ne'
  have hh' := hh.ne'
  unfold Noninertial.iUF4 Noninertial.piUF4 Noninertial.xUF4 phiXStar phiPiStar
  rw [← hG]
  field_simp
  unfold Noninertial.xiF4
  ring

omit 𝔼 in
/-- **Proposition 7.12, the `r̂ⁿ` responses** (Woodford (2003), p. 514, using App. F.4): with a
common `ρ` and `D(ρ) λᵢ ≠ 0`, `i_r = φ_π π_r + (φ_x/4) x_r`. -/
theorem rule_matches_f4_r {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx)
    (hli : 0 ≤ li) (hD : Drho β κ σ ρ * li ≠ 0) :
    Noninertial.iRF4 β κ σ lx li ρ = phiPiStar β κ σ li ρ * Noninertial.piRF4 β κ σ lx li ρ
      + phiXStar β κ σ lx li ρ / 4 * Noninertial.xRF4 β κ σ lx li ρ := by
  have hh := Noninertial.hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx hli
  have hG := kappa_sigma_Drho (β := β) (ρ := ρ) hκ.ne' hσ.ne'
  have hD0 : Drho β κ σ ρ ≠ 0 := left_ne_zero_of_mul hD
  have hli0 : li ≠ 0 := right_ne_zero_of_mul hD
  have hσ' := hσ.ne'
  have hκ' := hκ.ne'
  have hh' := hh.ne'
  unfold Noninertial.iRF4 Noninertial.piRF4 Noninertial.xRF4 phiXStar phiPiStar
  rw [← hG]
  field_simp
  unfold Noninertial.xiF4
  ring


/-! ### Every determinate Taylor rule yields a plan of the form (3.6) -/

/-- Woodford (2003), eq. (3.6), p. 512 (sufficiency of the six restrictions, App. F.4): a plan
(3.6) whose coefficients satisfy `(1 − β)π̄ = κx̄`, `ī = r̄ + π̄` and the two restrictions on each
set of responses satisfies (2.1) and (2.23). -/
theorem plan2_of {β κ σ ρu ρr rbar : ℝ} {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u)
    (hr : 𝔼.IsAR1 ρr r) {πbar xbar ibar fπ fx fi gπ gx gi : ℝ}
    (h1 : (1 - β) * πbar = κ * xbar) (h2 : ibar = rbar + πbar)
    (h3 : (1 - β * ρu) * fπ = κ * fx + 1) (h4 : (1 - ρu) * fx = -σ * (fi - ρu * fπ))
    (h5 : (1 - β * ρr) * gπ = κ * gx) (h6 : (1 - ρr) * gx = -σ * (gi - ρr * gπ - 1)) :
    AS 𝔼 β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u ∧
      IS 𝔼 σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
        (fun t ω => rbar + r t ω) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · rw [Noninertial.E_plan2 𝔼 hu hr]
    funext ω
    simp only [plan2_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h1 + u t ω * h3 + r t ω * h5
  · rw [Noninertial.E_plan2 𝔼 hu hr, Noninertial.E_plan2 𝔼 hu hr]
    funext ω
    simp only [plan2_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination σ * h2 + u t ω * h4 + r t ω * h6

omit 𝔼 in
/-- Woodford (2003), eq. (3.1), p. 507: the Taylor rule applied to plans (3.6) is a plan (3.6),
`i = ī + φ_π (P̄ − π̄) + φ_x (X̄ − x̄)/4 + (φ_π f_π + φ_x f_x/4) u + (φ_π g_π + φ_x g_x/4) r̂`. -/
theorem taylorRule_plan2 (ibar φπ φx πbar xbar P X fπ fx gπ gx : ℝ) (u r : ℕ → Ω → ℝ) :
    taylorRule ibar φπ φx πbar xbar (plan2 P fπ gπ u r) (plan2 X fx gx u r) =
      plan2 (ibar + φπ * (P - πbar) + φx * (X - xbar) / 4) (φπ * fπ + φx * fx / 4)
        (φπ * gπ + φx * gx / 4) u r := by
  funext t ω
  simp only [taylorRule, plan2_apply]
  ring

omit 𝔼 in
/-- Woodford (2003), p. 514 (the equilibrium under a Taylor rule with AR(1) disturbances): the
determinant `(1 − βρ)((1 − ρ) + σφ_x/4) + κσ(φ_π − ρ)` of the linear system for the responses. -/
noncomputable def detT (β κ σ φπ φx ρ : ℝ) : ℝ :=
  (1 - β * ρ) * ((1 - ρ) + σ * φx / 4) + κ * σ * (φπ - ρ)

omit 𝔼 in
/-- Woodford (2003), p. 514: under the Taylor principle (3.9), with `φ_x ≥ 0` and `ρ < 1`,
the response system is nonsingular: `detT > 0`. -/
theorem detT_pos {β κ σ φπ φx ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hφx : 0 ≤ φx) (hρ1 : ρ < 1) (hT : 1 < taylorLHS β κ φπ φx) :
    0 < detT β κ σ φπ φx ρ := by
  unfold detT
  unfold taylorLHS at hT
  have hT' : κ < κ * φπ + (1 - β) * φx / 4 := by
    have h4 : 0 < 4 * κ := by positivity
    have := (lt_div_iff₀ h4).mp (by linarith : (1 - φπ) < (1 - β) * φx / (4 * κ))
    nlinarith
  have ha : 1 - β ≤ 1 - β * ρ := by nlinarith
  have hb : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
  have hc : (1 - β) * (σ * φx) ≤ (1 - β * ρ) * (σ * φx) := mul_le_mul_of_nonneg_right ha hb
  have hd : 0 < (1 - ρ) * ((1 - β * ρ) + κ * σ) := by
    have : 0 < 1 - β * ρ := by nlinarith
    positivity
  nlinarith [mul_lt_mul_of_pos_left hT' hσ]

omit 𝔼 in
/-- Woodford (2003), p. 514: the inflation response to `u` under a Taylor rule. -/
noncomputable def fpiT (β κ σ φπ φx ρ : ℝ) : ℝ := ((1 - ρ) + σ * φx / 4) / detT β κ σ φπ φx ρ
omit 𝔼 in
/-- Woodford (2003), p. 514: the output-gap response to `u` under a Taylor rule. -/
noncomputable def fxT (β κ σ φπ φx ρ : ℝ) : ℝ := -(σ * (φπ - ρ)) / detT β κ σ φπ φx ρ
omit 𝔼 in
/-- Woodford (2003), p. 514: the inflation response to `r̂ⁿ` under a Taylor rule. -/
noncomputable def gpiT (β κ σ φπ φx ρ : ℝ) : ℝ := κ * σ / detT β κ σ φπ φx ρ
omit 𝔼 in
/-- Woodford (2003), p. 514: the output-gap response to `r̂ⁿ` under a Taylor rule. -/
noncomputable def gxT (β κ σ φπ φx ρ : ℝ) : ℝ := (1 - β * ρ) * σ / detT β κ σ φπ φx ρ
omit 𝔼 in
/-- Woodford (2003), p. 514: the long-run inflation rate under a Taylor rule,
`π̄ + κ(r̄ + π̄ − ī)/(κ(φ_π − 1) + (1 − β)φ_x/4)`. -/
noncomputable def pbarT (β κ φπ φx rbar ibar πbar : ℝ) : ℝ :=
  πbar + κ * (rbar + πbar - ibar) / (κ * (φπ - 1) + (1 - β) * φx / 4)
omit 𝔼 in
/-- Woodford (2003), p. 514: the long-run output gap under a Taylor rule. -/
noncomputable def xbarT (β κ φπ φx rbar ibar πbar xbar : ℝ) : ℝ :=
  xbar + (1 - β) * (rbar + πbar - ibar) / (κ * (φπ - 1) + (1 - β) * φx / 4)

/-- Woodford (2003), p. 514 ("this equilibrium is one in which the equilibrium values of `π_t`,
`x_t`, and `i_t` all depend only on the current disturbances"): under a Taylor rule satisfying
(3.9) with `φ_π, φ_x ≥ 0` and AR(1) disturbances (`ρ_u, ρ_r < 1`), the plan (3.6) with the
explicit coefficients `pbarT`, `fpiT`, `gpiT`, … is an equilibrium. -/
theorem taylor_eqm_plan2 {β σ κ φπ φx πbar xbar ibar rbar ρu ρr : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) (hφx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx)
    (hxb : κ * xbar = (1 - β) * πbar) (hρu1 : ρu < 1) (hρr1 : ρr < 1) {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r) :
    TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω)
      (plan2 (pbarT β κ φπ φx rbar ibar πbar) (fpiT β κ σ φπ φx ρu) (gpiT β κ σ φπ φx ρr) u r)
      (plan2 (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρu) (gxT β κ σ φπ φx ρr)
        u r) := by
  have hdu := detT_pos (σ := σ) (φπ := φπ) hβ0 hβ1 hκ hσ hφx hρu1 hT
  have hdr := detT_pos (σ := σ) (φπ := φπ) hβ0 hβ1 hκ hσ hφx hρr1 hT
  have hC : 0 < κ * (φπ - 1) + (1 - β) * φx / 4 := by
    unfold taylorLHS at hT
    have h4 : 0 < 4 * κ := by positivity
    have := (lt_div_iff₀ h4).mp (by linarith : (1 - φπ) < (1 - β) * φx / (4 * κ))
    nlinarith
  have hdu' := hdu.ne'
  have hdr' := hdr.ne'
  have hC' := hC.ne'
  unfold TaylorEqm
  rw [taylorRule_plan2]
  refine plan2_of 𝔼 hu hr ?_ ?_ ?_ ?_ ?_ ?_
  · unfold pbarT xbarT; linear_combination -hxb
  · have hinv : (κ * (φπ - 1) + (1 - β) * φx / 4) * (κ * (φπ - 1) + (1 - β) * φx / 4)⁻¹ = 1 :=
      mul_inv_cancel₀ hC'
    unfold pbarT xbarT
    simp only [div_eq_mul_inv]
    linear_combination (rbar + πbar - ibar) * hinv
  · have hinv := mul_inv_cancel₀ hdu'
    have hdef : detT β κ σ φπ φx ρu =
        (1 - β * ρu) * ((1 - ρu) + σ * φx / 4) + κ * σ * (φπ - ρu) := rfl
    unfold fpiT fxT
    simp only [div_eq_mul_inv]
    linear_combination hinv - (detT β κ σ φπ φx ρu)⁻¹ * hdef
  · unfold fpiT fxT
    simp only [div_eq_mul_inv]
    ring
  · unfold gpiT gxT; field_simp
  · have hinv := mul_inv_cancel₀ hdr'
    have hdef : detT β κ σ φπ φx ρr =
        (1 - β * ρr) * ((1 - ρr) + σ * φx / 4) + κ * σ * (φπ - ρr) := rfl
    unfold gpiT gxT
    simp only [div_eq_mul_inv]
    linear_combination σ * hinv - σ * (detT β κ σ φπ φx ρr)⁻¹ * hdef


/-- Woodford (2003), eq. (3.6), p. 512 (tool): a plan (3.6) of bounded adapted disturbances is
bounded and adapted. -/
theorem plan2_bdd_adapted {u r : ℕ → Ω → ℝ} (hub : BoundedProc u) (hrb : BoundedProc r)
    (hau : 𝔼.Adapted u) (har : 𝔼.Adapted r) (y f g : ℝ) :
    BoundedProc (plan2 y f g u r) ∧ 𝔼.Adapted (plan2 y f g u r) := by
  obtain ⟨M, hM⟩ := hub
  obtain ⟨N, hN⟩ := hrb
  refine ⟨⟨|y| + |f| * M + |g| * N, fun t ω => ?_⟩, fun t => ?_⟩
  · simp only [plan2_apply]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hN t ω) (abs_nonneg _)
  · rw [Noninertial.plan2_eq, map_add, map_add, map_smul, map_smul, 𝔼.const, hau t, har t]

/-- **Proposition 7.12** (Woodford (2003), p. 514): let the disturbances be bounded AR(1)
processes with a common `ρ ∈ [0, 1)`, `rⁿ = r̄ + r̂ⁿ`, and let (3.10) hold (`κ, σ, λₓ, λᵢ > 0`).
Then (i) the coefficients (3.12) are positive and satisfy (3.9); (ii) under the optimal
noninertial plan (corrected F.4: long-run values (3.11), F.4 responses) the interest rate is the
Taylor rule (3.1) with intercepts (3.11) and coefficients (3.12) applied to inflation and output;
(iii) the plan is an equilibrium under that rule; (iv) the rule implies a determinate equilibrium;
(v) hence the plan is the unique bounded adapted equilibrium under the rule. -/
theorem prop_7_12 [Nonempty Ω] {β κ σ rbar lx li istar ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) (hρ1 : ρ < 1)
    (h310 : Cond310 β κ σ lx li ρ) {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hr : 𝔼.IsAR1 ρ r)
    (hub : BoundedProc u) (hrb : BoundedProc r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (0 < phiPiStar β κ σ li ρ ∧ 0 < phiXStar β κ σ lx li ρ ∧
      1 < taylorLHS β κ (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ)) ∧
    plan2 is (Noninertial.iUF4 β κ σ lx li ρ) (Noninertial.iRF4 β κ σ lx li ρ) u r =
      taylorRule is (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ)
        (Noninertial.piBar119 β li rbar istar) xs
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρ)
          (Noninertial.piRF4 β κ σ lx li ρ) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r) ∧
    TaylorEqm 𝔼 β σ κ is (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ)
      (Noninertial.piBar119 β li rbar istar) xs u (fun t ω => rbar + r t ω)
      (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρ)
        (Noninertial.piRF4 β κ σ lx li ρ) u r)
      (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r) ∧
    ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ is (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ)
      (Noninertial.piBar119 β li rbar istar) xs) ∧
    ∀ π x : ℕ → Ω → ℝ, BoundedProc π → BoundedProc x → 𝔼.Adapted π → 𝔼.Adapted x →
      TaylorEqm 𝔼 β σ κ is (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ)
        (Noninertial.piBar119 β li rbar istar) xs u (fun t ω => rbar + r t ω) π x →
      π = plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρ)
        (Noninertial.piRF4 β κ σ lx li ρ) u r ∧
      x = plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r := by
  have hβρ : β * ρ < 1 := by nlinarith [h310.1]
  have hcoef := prop_7_12_coeffs hκ hlx hβρ h310
  have hD : Drho β κ σ ρ * li ≠ 0 := h310.1.ne'
  set πs := Noninertial.piBar119 β li rbar istar
  have hxb : κ * xs = (1 - β) * πs := by rw [hxs]; field_simp
  have hrule : plan2 is (Noninertial.iUF4 β κ σ lx li ρ) (Noninertial.iRF4 β κ σ lx li ρ) u r =
      taylorRule is (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ) πs xs
        (plan2 πs (Noninertial.piUF4 β κ σ lx li ρ) (Noninertial.piRF4 β κ σ lx li ρ) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r) := by
    rw [taylorRule_plan2, rule_matches_f4_u hκ hσ hlx.le hli.le hD,
      rule_matches_f4_r hκ hσ hlx.le hli.le hD]
    congr 1 <;> ring
  have heq : TaylorEqm 𝔼 β σ κ is (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ) πs xs u
      (fun t ω => rbar + r t ω)
      (plan2 πs (Noninertial.piUF4 β κ σ lx li ρ) (Noninertial.piRF4 β κ σ lx li ρ) u r)
      (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r) := by
    obtain ⟨c1, c2⟩ := Noninertial.f4_u_feasible (β := β) (ρ := ρ) hκ hσ hlx.le hli.le
    obtain ⟨c3, c4⟩ := Noninertial.f4_r_feasible (β := β) (ρ := ρ) hκ hσ hlx.le hli.le
    unfold TaylorEqm
    rw [← hrule]
    exact plan2_of 𝔼 hu hr (by linarith [hxb]) his c1 c2 c3 c4
  have hdet := (taylor_determinate_iff 𝔼 (ibar := is) hβ0 hβ1 hσ hκ hcoef.1.le hcoef.2.1.le
    hxb).mpr hcoef.2.2
  refine ⟨hcoef, hrule, heq, hdet, fun π x hπb hxb' hπa hxa hπx => ?_⟩
  have hrn : BoundedProc (fun t ω => rbar + r t ω) := by
    obtain ⟨N, hN⟩ := hrb
    exact ⟨|rbar| + N, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hN t ω))⟩
  have hrna : 𝔼.Adapted (fun t ω => rbar + r t ω) := by
    intro t
    change 𝔼.E t (fun ω => rbar + r t ω) = fun ω => rbar + r t ω
    have e : (fun ω => rbar + r t ω) = (fun _ => rbar) + r t := rfl
    rw [e, map_add, 𝔼.const, hr.1 t]
  obtain ⟨p, -, hpu⟩ := hdet u (fun t ω => rbar + r t ω) hub hrn hu.1 hrna
  obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 πs (Noninertial.piUF4 β κ σ lx li ρ)
    (Noninertial.piRF4 β κ σ lx li ρ)
  obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 xs (Noninertial.xUF4 β κ σ lx li ρ)
    (Noninertial.xRF4 β κ σ lx li ρ)
  have e1 := hpu (π, x) ⟨hπb, hxb', hπa, hxa, hπx⟩
  have e2 := hpu (_, _) ⟨b1, b2, a1, a2, heq⟩
  have := e1.trans e2.symm
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- **Proposition 7.12, "It follows that this is the optimal Taylor rule"** (Woodford (2003),
p. 514): with a common `ρ ∈ [0, 1)`, independent AR(1) disturbances with innovation variances
`s_u, s_r > 0`, non-degenerate as a pair, the pull-out property and (3.10), let `(π, x)` be any
bounded adapted equilibrium under any Taylor rule (3.1) with `φ_π, φ_x ≥ 0` satisfying (3.9)
(intercepts with `κ x̄ = (1 − β) π̄`). Its stabilization loss is at least that of the optimal
noninertial plan, which is the equilibrium under the rule (3.11)–(3.12) (`prop_7_12`). -/
theorem prop_7_12_optimal (hpo : 𝔼.PullOut) {β κ σ rbar lx li istar ρ su sr : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hsu : 0 < su) (hsr : 0 < sr) {u εu r εr : ℕ → Ω → ℝ}
    (hu : Noninertial.AR1Innov 𝔼 ρ su u εu) (hr : Noninertial.AR1Innov 𝔼 ρ sr r εr)
    (hind : ∀ t, 𝔼.E t (εu (t + 1) * εr (t + 1)) = fun _ => 0) (hnd : Nondeg2 u r)
    (hub : BoundedProc u) (hrb : BoundedProc r) (t₀ : ℕ) (ω : Ω) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar)
    {ibar φπ φx πbar xbar : ℝ} (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx)
    (hxb : κ * xbar = (1 - β) * πbar) {π x : ℕ → Ω → ℝ} (hπb : BoundedProc π)
    (hxbd : BoundedProc x) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (heq : TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω) π x) :
    Noninertial.Lstab 𝔼 β lx li t₀
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρ)
          (Noninertial.piRF4 β κ σ lx li ρ) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r)
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρ) (Noninertial.iRF4 β κ σ lx li ρ) u r) ω ≤
      Noninertial.Lstab 𝔼 β lx li t₀ π x (taylorRule ibar φπ φx πbar xbar π x) ω := by
  have hρa : |ρ| < 1 := abs_lt.mpr ⟨by linarith, hρ1⟩
  have hiu := hu.isAR1
  have hir := hr.isAR1
  have hrn : BoundedProc (fun t ω => rbar + r t ω) := by
    obtain ⟨N, hN⟩ := hrb
    exact ⟨|rbar| + N, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hN t ω))⟩
  have hrna : 𝔼.Adapted (fun t ω => rbar + r t ω) := by
    intro t
    change 𝔼.E t (fun ω => rbar + r t ω) = fun ω => rbar + r t ω
    have e : (fun ω => rbar + r t ω) = (fun _ => rbar) + r t := rfl
    rw [e, map_add, 𝔼.const, hr.1 t]
  have : Nonempty Ω := ⟨ω⟩
  have hdet := (taylor_determinate_iff 𝔼 (ibar := ibar) hβ0 hβ1 hσ hκ hφπ hφx hxb).mpr hT
  have hplan := taylor_eqm_plan2 𝔼 (rbar := rbar) (ibar := ibar) hβ0 hβ1 hσ hκ hφx hT hxb hρ1
    hρ1 hiu hir
  obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 (pbarT β κ φπ φx rbar ibar πbar)
    (fpiT β κ σ φπ φx ρ) (gpiT β κ σ φπ φx ρ)
  obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1
    (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρ) (gxT β κ σ φπ φx ρ)
  obtain ⟨p, -, hpu⟩ := hdet u _ hub hrn hu.1 hrna
  have e1 := hpu (π, x) ⟨hπb, hxbd, hπa, hxa, heq⟩
  have e2 := hpu (plan2 (pbarT β κ φπ φx rbar ibar πbar) (fpiT β κ σ φπ φx ρ)
    (gpiT β κ σ φπ φx ρ) u r, plan2 (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρ)
    (gxT β κ σ φπ φx ρ) u r) ⟨b1, b2, a1, a2, hplan⟩
  have hpx := e1.trans e2.symm
  simp only [Prod.mk.injEq] at hpx
  obtain ⟨rfl, rfl⟩ := hpx
  rw [taylorRule_plan2]
  have hAI := hplan
  unfold TaylorEqm at hAI
  rw [taylorRule_plan2] at hAI
  exact ((Noninertial.f4_lstab 𝔼 hpo hβ0 hβ1 hκ hσ hlx hli.le hρa hρa hsu hsr hu hr hind hnd t₀
    ω hxs his).2 _ _ _ _ _ _ _ _ _ hAI.1 hAI.2).1


/-! ### Survey E9: `φ_π > 1` is not implied by (3.10) -/

omit 𝔼 in
/-- Survey E9 (Woodford (2003), p. 515, confirmed false): "`φ_π > 1` as long as `λᵢ` satisfies
the upper bound implied by (3.10)". At `β = .99`, `κ = .024`, `σ = 6.25` (`σ⁻¹ = .16`),
`λₓ = .003`, `λᵢ = .236` and `ρ = .18`, (3.10) holds but `φ_π < 1` (`D λᵢ ≈ 1.018`,
upper bound `≈ 1.043`, `φ_π ≈ 0.983`). -/
theorem e9_counterexample :
    Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (18 / 100) ∧
      phiPiStar (99 / 100) (24 / 1000) (625 / 100) (236 / 1000) (18 / 100) < 1 := by
  refine ⟨?_, ?_⟩
  · unfold Cond310 Drho; norm_num
  · unfold phiPiStar Drho; norm_num

/-! ### (3.10) holds on an interval `(ρ̲, ρ̄)` -/

omit 𝔼 in
/-- Woodford (2003), p. 515 (tool): a quadratic `aρ² + bρ + c` with `a > 0` that is negative at
some `z` has two real roots `m < z < M` and factors as `a(ρ − m)(ρ − M)`. -/
theorem quad_factor {a b c z : ℝ} (ha : 0 < a) (hz : a * z ^ 2 + b * z + c < 0) :
    ∃ m M, m < z ∧ z < M ∧ ∀ ρ, a * ρ ^ 2 + b * ρ + c = a * (ρ - m) * (ρ - M) := by
  set d := b ^ 2 - 4 * a * c with hd
  have hd0 : (2 * a * z + b) ^ 2 < d := by nlinarith
  have hdpos : 0 ≤ d := le_trans (sq_nonneg _) hd0.le
  set s := Real.sqrt d with hs
  have hss : s * s = d := Real.mul_self_sqrt hdpos
  have hs0 : 0 ≤ s := Real.sqrt_nonneg d
  have habs : |2 * a * z + b| < s := by
    rw [hs]; exact (Real.lt_sqrt (abs_nonneg _)).mpr (by rw [sq_abs]; exact hd0)
  obtain ⟨h1, h2⟩ := abs_lt.mp habs
  refine ⟨(-b - s) / (2 * a), (-b + s) / (2 * a), ?_, ?_, fun ρ => ?_⟩
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [lt_div_iff₀ (by positivity)]; linarith
  · field_simp
    linear_combination hss + 2 * hd

omit 𝔼 in
/-- Woodford (2003), (3.10), p. 514: `κσ D(ρ) = βρ² − (1 + β + κσ)ρ + 1`. -/
theorem kappa_sigma_Drho' {β κ σ ρ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) :
    κ * σ * Drho β κ σ ρ = β * ρ ^ 2 + -(1 + β + κ * σ) * ρ + 1 := by
  unfold Drho
  field_simp
  ring

omit 𝔼 in
/-- Woodford (2003), p. 515 ("the inequalities (3.10) are necessarily satisfied for `ρ` in some
nonempty interval `ρ̲ < ρ < ρ̄`, where `0 < ρ̄ < 1`"), sharpened: for `0 < β < 1`,
`κ, σ, λᵢ > 0`, `λₓ ≥ 0` there are `ρ̲ < ρ̄` with `0 < ρ̄ < 1` and `D(ρ̄) = 0` such that, for every
`ρ < 1`, (3.10) holds iff `ρ̲ < ρ < ρ̄`. (`ρ̲` may be negative.) -/
theorem prop_7_12_interval {β κ σ lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 < li) :
    ∃ ρlo ρhi, 0 < ρhi ∧ ρhi < 1 ∧ ρlo < ρhi ∧ Drho β κ σ ρhi = 0 ∧
      ∀ ρ, ρ < 1 → (Cond310 β κ σ lx li ρ ↔ ρlo < ρ ∧ ρ < ρhi) := by
  have hks : 0 < κ * σ := mul_pos hκ hσ
  have hD := fun ρ => kappa_sigma_Drho' (β := β) (ρ := ρ) hκ.ne' hσ.ne'
  -- the roots of `κσ D`
  obtain ⟨m1, M1, hm1, hM1, hq1⟩ := quad_factor (a := β) (b := -(1 + β + κ * σ)) (c := 1)
    (z := 1) hβ0 (by nlinarith)
  have hm0 : 0 < m1 := by
    by_contra hle
    push Not at hle
    have e0 : β * (0 - m1) * (0 - M1) = 1 := by rw [← hq1 0]; ring
    have h1 : 0 ≤ β * (0 - m1) := mul_nonneg hβ0.le (by linarith)
    have h2 : β * (0 - m1) * (0 - M1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 (by linarith)
    linarith
  have hDsign : ∀ ρ, ρ < 1 → (0 < Drho β κ σ ρ ↔ ρ < m1) := by
    intro ρ hρ
    rw [← mul_pos_iff_of_pos_left hks, hD, hq1]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      have h1 : 0 ≤ β * (ρ - m1) := mul_nonneg hβ0.le (by linarith)
      have h2 : β * (ρ - m1) * (ρ - M1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1 (by linarith)
      linarith
    · intro h
      have h1 : β * (ρ - m1) < 0 := mul_neg_of_pos_of_neg hβ0 (by linarith)
      exact mul_pos_of_neg_of_neg h1 (by linarith)
  have hDm1 : Drho β κ σ m1 = 0 := by
    have := hD m1
    rw [hq1 m1, sub_self, mul_zero, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_left hks.ne'
  -- the quadratic `λᵢ D − U`
  set U : ℝ → ℝ := fun ρ => (1 - β) * (1 - β * ρ) / κ ^ 2 * lx + 1 with hU
  have hUpos : 0 < U m1 := by
    have : 0 < 1 - β * m1 := by nlinarith
    have : 0 ≤ (1 - β) * (1 - β * m1) / κ ^ 2 * lx := by
      have : 0 < 1 - β := by linarith
      positivity
    simp only [hU]; linarith
  set a2 := li * β / (κ * σ)
  set b2 := -(li * (1 + β + κ * σ)) / (κ * σ) + (1 - β) * β * lx / κ ^ 2
  set c2 := li / (κ * σ) - (1 - β) * lx / κ ^ 2 - 1
  have hq2 : ∀ ρ, Drho β κ σ ρ * li - U ρ = a2 * ρ ^ 2 + b2 * ρ + c2 := by
    intro ρ
    have e := hD ρ
    have hDρ : Drho β κ σ ρ = (β * ρ ^ 2 + -(1 + β + κ * σ) * ρ + 1) / (κ * σ) := by
      rw [← e]; field_simp
    rw [hDρ]
    simp only [hU, a2, b2, c2]
    field_simp
    ring
  have ha2 : 0 < a2 := by positivity
  obtain ⟨s1, s2, hs1, hs2, hq2f⟩ := quad_factor (a := a2) (b := b2) (c := c2) (z := m1) ha2
    (by rw [← hq2, hDm1, zero_mul]; linarith)
  refine ⟨s1, m1, hm0, hm1, hs1, hDm1, fun ρ hρ => ?_⟩
  unfold Cond310
  rw [mul_pos_iff_of_pos_right hli, hDsign ρ hρ, ← sub_neg (a := Drho β κ σ ρ * li),
    show (1 - β) * (1 - β * ρ) / κ ^ 2 * lx + 1 = U ρ from rfl, hq2, hq2f]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    by_contra hc
    push Not at hc
    have k1 : a2 * (ρ - s1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha2.le (by linarith)
    have k2 : 0 ≤ a2 * (ρ - s1) * (ρ - s2) := mul_nonneg_of_nonpos_of_nonpos k1 (by linarith)
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    have k1 : 0 < a2 * (ρ - s1) := mul_pos ha2 (by linarith)
    exact mul_neg_of_pos_of_neg k1 (by linarith)

omit 𝔼 in
/-- Woodford (2003), p. 515: "this interval also contains some positive values of `ρ`": there is
`ρ ∈ (0, 1)` satisfying (3.10). -/
theorem exists_pos_rho_cond310 {β κ σ lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 < li) :
    ∃ ρ, 0 < ρ ∧ ρ < 1 ∧ Cond310 β κ σ lx li ρ := by
  obtain ⟨ρlo, ρhi, h0, h1, hlo, -, hiff⟩ := prop_7_12_interval hβ0 hβ1 hκ hσ hlx hli
  refine ⟨(max ρlo 0 + ρhi) / 2, ?_, ?_, (hiff _ ?_).mpr ⟨?_, ?_⟩⟩
  · have := le_max_right ρlo 0; linarith
  · have : max ρlo 0 < ρhi := max_lt hlo h0; linarith
  · have : max ρlo 0 < ρhi := max_lt hlo h0; linarith
  · have := le_max_left ρlo 0; have : max ρlo 0 < ρhi := max_lt hlo h0; linarith
  · have : max ρlo 0 < ρhi := max_lt hlo h0; linarith

/-! ### Footnote 32 and survey E10 -/

omit 𝔼 in
/-- Woodford (2003), fn. 32, p. 515, with `λᵢ = .236` and the quarterly `λₓ = .048/16 = .003`
(β = .99, κ = .024, σ⁻¹ = .16): the interval of (3.10) is `(ρ̲, ρ̄)` with `.170 ≤ ρ̲ < .171` and
`.683 < ρ̄ ≤ .684` — the book's "0.17 < ρ < 0.68". -/
theorem fn32_interval :
    ∃ ρlo ρhi, (∀ ρ, ρ < 1 → (Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000)
      (236 / 1000) ρ ↔ ρlo < ρ ∧ ρ < ρhi)) ∧
      170 / 1000 ≤ ρlo ∧ ρlo < 171 / 1000 ∧ 683 / 1000 < ρhi ∧ ρhi ≤ 684 / 1000 := by
  obtain ⟨ρlo, ρhi, -, -, -, -, hiff⟩ := prop_7_12_interval (β := 99 / 100) (κ := 24 / 1000)
    (σ := 625 / 100) (lx := 3 / 1000) (li := 236 / 1000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have a1 : Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (171 / 1000) := by
    unfold Cond310 Drho; norm_num
  have a2 : Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (683 / 1000) := by
    unfold Cond310 Drho; norm_num
  have a3 : ¬ Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (170 / 1000) := by
    unfold Cond310 Drho; norm_num
  have a4 : ¬ Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (684 / 1000) := by
    unfold Cond310 Drho; norm_num
  obtain ⟨b1, b2⟩ := (hiff _ (by norm_num)).mp a1
  obtain ⟨b3, b4⟩ := (hiff _ (by norm_num)).mp a2
  refine ⟨ρlo, ρhi, hiff, ?_, b1, b4, ?_⟩
  · by_contra h
    push Not at h
    exact a3 ((hiff _ (by norm_num)).mpr ⟨h, by linarith⟩)
  · by_contra h
    push Not at h
    exact a4 ((hiff _ (by norm_num)).mpr ⟨by linarith, h⟩)

omit 𝔼 in
/-- Survey E10 (Woodford (2003), fn. 32, confirmed): with Table 6.1's `λᵢ = .077` (and the
quarterly `λₓ = .003`), (3.10) already holds at `ρ = .1`, so the interval is not `.17 < ρ`. -/
theorem e10_table61 :
    Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (77 / 1000) (1 / 10) := by
  unfold Cond310 Drho; norm_num

omit 𝔼 in
/-- Survey E10 (Woodford (2003), fn. 32, confirmed): with `λᵢ = .236` but Table 6.1's annualised
`λₓ = .048` (`= 16 κ/θ`, Ch. 6 fn. 52), (3.10) also holds at `ρ = .1`. -/
theorem e10_annual_lx :
    Cond310 (99 / 100) (24 / 1000) (625 / 100) (48 / 1000) (236 / 1000) (1 / 10) := by
  unfold Cond310 Drho; norm_num

omit 𝔼 in
/-- Woodford (2003), fn. 32: at the fn. 32 calibration (3.10) fails at `ρ = .1`, consistently
with `ρ̲ ≥ .170`. -/
theorem fn32_fails_at_tenth :
    ¬ Cond310 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) (1 / 10) := by
  unfold Cond310 Drho; norm_num


/-! ### (3.13)–(3.14): forecast-based rules -/

/-- Woodford (2003), eq. (3.13), p. 516: the forecast-based rule
`i_t = ī + φ_π (E_t π_{t+k} − π̄) + φ_x (E_t x_{t+k} − x̄)/4`. -/
noncomputable def forecastRule (ibar φπ φx πbar xbar : ℝ) (k : ℕ) (π x : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => ibar + φπ * (𝔼.E t (π (t + k)) ω - πbar) + φx * (𝔼.E t (x (t + k)) ω - xbar) / 4

/-- Woodford (2003), (2.1), (2.23) and (3.13): `(π, x)` is an equilibrium under the forecast-based
rule with horizon `k`. -/
def ForecastEqm (β σ κ ibar φπ φx πbar xbar : ℝ) (k : ℕ) (u rn π x : ℕ → Ω → ℝ) : Prop :=
  AS 𝔼 β κ π x u ∧ IS 𝔼 σ π x (forecastRule 𝔼 ibar φπ φx πbar xbar k π x) rn

/-- Woodford (2003), eq. (3.14), p. 516: with AR(1) disturbances of common persistence `ρ ≠ 0`,
a plan (3.6) centred on the rule's `(π̄, x̄)` has `E_t π_{t+k} − π̄ = ρᵏ (π_t − π̄)`, so the
forecast rule with `φ_y = ρ^{−k} φ̄_y` prescribes the same interest rate as the Taylor rule with
`φ̄_y`: it "is consistent with" the same plan for any `k ≥ 0`. -/
theorem forecast_rule_consistent {ρ : ℝ} (hρ : ρ ≠ 0) {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hr : 𝔼.IsAR1 ρ r) (ibar φπ φx πbar xbar fπ gπ fx gx : ℝ) (k : ℕ) :
    forecastRule 𝔼 ibar ((ρ ^ k)⁻¹ * φπ) ((ρ ^ k)⁻¹ * φx) πbar xbar k (plan2 πbar fπ gπ u r)
      (plan2 xbar fx gx u r) =
      taylorRule ibar φπ φx πbar xbar (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) := by
  have hE : ∀ y f g t, 𝔼.E t (plan2 y f g u r (t + k)) = plan2 y (f * ρ ^ k) (g * ρ ^ k) u r t := by
    intro y f g t
    rw [Noninertial.plan2_eq, map_add, map_add, map_smul, map_smul, 𝔼.const,
      𝔼.ar1_iterate hu, 𝔼.ar1_iterate hr]
    funext ω
    simp only [plan2_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  funext t ω
  simp only [forecastRule, taylorRule, hE]
  simp only [plan2_apply]
  have hk : ρ ^ k ≠ 0 := pow_ne_zero k hρ
  field_simp
  ring

/-! ### Proposition 7.13: indeterminacy of forecast-based rules -/

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (the characteristic function of the forecast-based rule with
horizon `k`): `χ(λ) = (1 − λ)(1 − βλ) − κσλ + κσφ_π λᵏ + σφ_x λᵏ (1 − βλ)/4`; `(π, x) = λᵗ(1,
(1 − βλ)/κ)` solves the homogeneous system iff `χ(λ) = 0`. -/
noncomputable def chiC (β κ σ φπ φx : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * (1 - β * z) - κ * σ * z + κ * σ * φπ * z ^ k + σ * φx * z ^ k * (1 - β * z) / 4

/-- **Prop. 7.13, the mechanism** (Woodford (2003), p. 516): if the characteristic function has a
root `λ ≠ 0` with `|λ| ≤ 1`, then next to any equilibrium `(π, x)` under the forecast rule there is
a second one, `(π_t + Re λᵗ, x_t + Re(λᵗ(1 − βλ)/κ))` — bounded, adapted, and different. -/
theorem indeterminate_of_root {β σ κ ibar φπ φx πbar xbar : ℝ} (hκ : κ ≠ 0) {k : ℕ} {lam : ℂ}
    (hroot : chiC β κ σ φπ φx k lam = 0) (hle : ‖lam‖ ≤ 1) {u rn π x : ℕ → Ω → ℝ}
    (heq : ForecastEqm 𝔼 β σ κ ibar φπ φx πbar xbar k u rn π x) (hπb : BoundedProc π)
    (hxb : BoundedProc x) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) [Nonempty Ω] :
    ∃ π' x' : ℕ → Ω → ℝ, ForecastEqm 𝔼 β σ κ ibar φπ φx πbar xbar k u rn π' x' ∧
      BoundedProc π' ∧ BoundedProc x' ∧ 𝔼.Adapted π' ∧ 𝔼.Adapted x' ∧ π' ≠ π := by
  set c : ℂ := (1 - β * lam) / κ with hc
  set p : ℕ → ℝ := fun t => (lam ^ t).re with hp
  set y : ℕ → ℝ := fun t => (lam ^ t * c).re with hy
  have hκc : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hre : ∀ (a : ℝ) (z : ℂ), ((a : ℂ) * z).re = a * z.re := fun a z => by simp
  have hAS : ∀ t, p t = κ * y t + β * p (t + 1) := by
    intro t
    have e : lam ^ t = (κ : ℂ) * (lam ^ t * c) + (β : ℂ) * lam ^ (t + 1) := by
      rw [hc]; field_simp; ring
    simp only [hp, hy]
    rw [← hre, ← hre, ← Complex.add_re, ← e]
  have hIS : ∀ t, y t = y (t + 1) - σ * (φπ * p (t + k) + φx * y (t + k) / 4 - p (t + 1)) := by
    intro t
    have e : lam ^ t * c = lam ^ (t + 1) * c - (σ : ℂ) * ((φπ : ℂ) * lam ^ (t + k) +
        (φx : ℂ) * (lam ^ (t + k) * c) / 4 - lam ^ (t + 1)) := by
      have h0 := hroot
      unfold chiC at h0
      have hκinv : (κ : ℂ) * (κ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hκc
      rw [hc, div_eq_mul_inv]
      linear_combination (lam ^ t * (κ : ℂ)⁻¹) * h0 -
        lam ^ t * σ * (φπ * lam ^ k - lam) * hκinv
    simp only [hp, hy]
    have : (lam ^ t * c).re = (lam ^ (t + 1) * c - (σ : ℂ) * ((φπ : ℂ) * lam ^ (t + k) +
        (φx : ℂ) * (lam ^ (t + k) * c) / 4 - lam ^ (t + 1))).re := by rw [← e]
    rw [this]
    simp [Complex.sub_re, Complex.mul_re]
  have hpb : ∀ t, |p t| ≤ 1 := by
    intro t
    calc |p t| ≤ ‖lam ^ t‖ := Complex.abs_re_le_norm _
      _ = ‖lam‖ ^ t := norm_pow _ _
      _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hle
  have hyb : ∀ t, |y t| ≤ ‖c‖ := by
    intro t
    calc |y t| ≤ ‖lam ^ t * c‖ := Complex.abs_re_le_norm _
      _ = ‖lam‖ ^ t * ‖c‖ := by rw [norm_mul, norm_pow]
      _ ≤ 1 * ‖c‖ := by gcongr; exact pow_le_one₀ (norm_nonneg _) hle
      _ = ‖c‖ := one_mul _
  obtain ⟨hA, hI⟩ := heq
  refine ⟨fun t => π t + fun _ => p t, fun t => x t + fun _ => y t, ⟨fun t => ?_, fun t => ?_⟩,
    ?_, ?_, fun t => ?_, fun t => ?_, fun h => ?_⟩
  · beta_reduce
    rw [hA t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, 𝔼.const]
    linear_combination hAS t
  · beta_reduce
    rw [hI t]
    funext ω
    simp only [forecastRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add,
      𝔼.const]
    linear_combination hIS t
  · obtain ⟨M, hM⟩ := hπb
    exact ⟨M + 1, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω) (hpb t))⟩
  · obtain ⟨M, hM⟩ := hxb
    exact ⟨M + ‖c‖, fun t ω => (abs_add_le _ _).trans (add_le_add (hM t ω) (hyb t))⟩
  · simp only [map_add, hπa t, 𝔼.const]
  · simp only [map_add, hxa t, 𝔼.const]
  · obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun h 0) ω
    simp [hp] at this

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (tool: Vieta's formula over `ℂ`): a complex polynomial with
constant term `1` whose leading coefficient has modulus `> 1` has a root of modulus `< 1`. -/
theorem exists_root_lt_one {P : Polynomial ℂ} (h0 : P.coeff 0 = 1) (hl : 1 < ‖P.leadingCoeff‖) :
    ∃ z, P.eval z = 0 ∧ ‖z‖ < 1 := by
  have hP : P ≠ 0 := fun h => by simp [h] at h0
  have hs := IsAlgClosed.splits P
  have hv := hs.coeff_zero_eq_leadingCoeff_mul_prod_roots
  by_contra hno
  push Not at hno
  have hge : ∀ r ∈ P.roots, 1 ≤ ‖r‖ := fun r hr =>
    hno r ((Polynomial.mem_roots hP).mp hr)
  have hprod : ∀ s : Multiset ℂ, (∀ r ∈ s, 1 ≤ ‖r‖) → 1 ≤ ‖s.prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro h
      rw [Multiset.prod_cons, norm_mul]
      have h1 := h a (Multiset.mem_cons_self a s)
      have h2 := ih (fun r hr => h r (Multiset.mem_cons_of_mem hr))
      nlinarith
  have := congrArg norm hv
  rw [h0, norm_one, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at this
  have hp := hprod _ hge
  nlinarith [norm_nonneg P.leadingCoeff]

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (tool): a polynomial whose part below the top has degree at most
`n` has leading coefficient equal to the top coefficient. -/
theorem leadingCoeff_top {Q : Polynomial ℂ} {n : ℕ} (hQ : Q.natDegree ≤ n) {b : ℂ} (hb : b ≠ 0) :
    (Q + Polynomial.C b * Polynomial.X ^ (n + 1)).leadingCoeff = b := by
  rw [Polynomial.leadingCoeff_add_of_degree_lt, Polynomial.leadingCoeff_C_mul_X_pow]
  rw [Polynomial.degree_C_mul_X_pow _ hb]
  refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
  exact_mod_cast Nat.lt_succ_of_le hQ

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13: for a horizon `k ≥ 2` the characteristic function is the
polynomial `1 − (1 + β + κσ)z + βz² + (κσφ_π + σφ_x/4) zᵏ − (σβφ_x/4) z^{k+1}`, of leading
coefficient `−σβφ_x/4`; if this exceeds one in modulus, `χ` has a root `λ ≠ 0` with `|λ| < 1`. -/
theorem exists_root_inside {β κ σ φπ φx : ℝ} {k : ℕ} (hk : 2 ≤ k) (hl : 1 < |σ * β * φx / 4|) :
    ∃ lam : ℂ, chiC β κ σ φπ φx k lam = 0 ∧ lam ≠ 0 ∧ ‖lam‖ < 1 := by
  set Q : Polynomial ℂ := Polynomial.C 1 + Polynomial.C (-(1 + (β : ℂ) + κ * σ)) * Polynomial.X +
    Polynomial.C (β : ℂ) * Polynomial.X ^ 2 +
    Polynomial.C ((κ : ℂ) * σ * φπ + σ * φx / 4) * Polynomial.X ^ k with hQ
  set b : ℂ := -((σ : ℂ) * β * φx / 4) with hb
  have hb0 : b ≠ 0 := by
    intro h
    have : ‖b‖ = |σ * β * φx / 4| := by
      rw [hb, norm_neg]
      have : ((σ : ℂ) * β * φx / 4) = ((σ * β * φx / 4 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs]
    rw [h, norm_zero] at this
    linarith [abs_nonneg (σ * β * φx / 4)]
  have hQdeg : Q.natDegree ≤ k := by
    rw [hQ]
    refine Polynomial.natDegree_add_le_of_degree_le (Polynomial.natDegree_add_le_of_degree_le
      (Polynomial.natDegree_add_le_of_degree_le ?_ ?_) ?_) ?_
    · rw [Polynomial.natDegree_C]; omega
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [Polynomial.natDegree_X]; omega)
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
    · exact Polynomial.natDegree_C_mul_X_pow_le _ _
  set P := Q + Polynomial.C b * Polynomial.X ^ (k + 1) with hP
  have hlc : P.leadingCoeff = b := leadingCoeff_top hQdeg hb0
  have hk0 : k ≠ 0 := by omega
  have hc0 : P.coeff 0 = 1 := by
    simp [hP, hQ, Polynomial.coeff_X_pow, hk0, Ne.symm hk0, Polynomial.coeff_X]
  have hev : ∀ z, P.eval z = chiC β κ σ φπ φx k z := by
    intro z
    simp only [hP, hQ, chiC, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, hb]
    ring
  have hnorm : 1 < ‖P.leadingCoeff‖ := by
    rw [hlc, hb, norm_neg]
    have : ((σ : ℂ) * β * φx / 4) = ((σ * β * φx / 4 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact hl
  obtain ⟨z, hz, hz1⟩ := exists_root_lt_one hc0 hnorm
  refine ⟨z, by rw [← hev]; exact hz, fun h => ?_, hz1⟩
  rw [h, hev] at hz
  simp [chiC, hk0] at hz

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 for `k = 1`: the characteristic function is the quadratic
`1 − (1 + β + κσ − κσφ_π − σφ_x/4) z + β(1 − σφ_x/4) z²`; if `|β(1 − σφ_x/4)| > 1` it has a root
`λ ≠ 0` with `|λ| < 1`. -/
theorem exists_root_inside_one {β κ σ φπ φx : ℝ} (hl : 1 < |β * (1 - σ * φx / 4)|) :
    ∃ lam : ℂ, chiC β κ σ φπ φx 1 lam = 0 ∧ lam ≠ 0 ∧ ‖lam‖ < 1 := by
  set Q : Polynomial ℂ := Polynomial.C 1 +
    Polynomial.C (-(1 + (β : ℂ) + κ * σ) + κ * σ * φπ + σ * φx / 4) * Polynomial.X with hQ
  set b : ℂ := (β : ℂ) * (1 - σ * φx / 4) with hb
  have hbr : b = ((β * (1 - σ * φx / 4) : ℝ) : ℂ) := by rw [hb]; push_cast; ring
  have hb0 : b ≠ 0 := by
    intro h
    have : ‖b‖ = |β * (1 - σ * φx / 4)| := by rw [hbr, Complex.norm_real, Real.norm_eq_abs]
    rw [h, norm_zero] at this
    linarith [abs_nonneg (β * (1 - σ * φx / 4))]
  have hQdeg : Q.natDegree ≤ 1 := by
    rw [hQ]
    refine Polynomial.natDegree_add_le_of_degree_le ?_ ?_
    · rw [Polynomial.natDegree_C]; omega
    · exact (Polynomial.natDegree_C_mul_le _ _).trans (by rw [Polynomial.natDegree_X])
  set P := Q + Polynomial.C b * Polynomial.X ^ (1 + 1) with hP
  have hlc : P.leadingCoeff = b := leadingCoeff_top hQdeg hb0
  have hc0 : P.coeff 0 = 1 := by
    simp [hP, hQ, Polynomial.coeff_X]
  have hev : ∀ z, P.eval z = chiC β κ σ φπ φx 1 z := by
    intro z
    simp only [hP, hQ, chiC, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, hb]
    ring
  have hnorm : 1 < ‖P.leadingCoeff‖ := by
    rw [hlc, hbr, Complex.norm_real, Real.norm_eq_abs]
    exact hl
  obtain ⟨z, hz, hz1⟩ := exists_root_lt_one hc0 hnorm
  refine ⟨z, by rw [← hev]; exact hz, fun h => ?_, hz1⟩
  rw [h, hev] at hz
  simp [chiC] at hz


/-! ### Horizon `k = 1`: the exact determinacy criterion -/

omit 𝔼 in
/-- Woodford (2003), (3.13) with `k = 1` (cf. Ch. 4, §2.2 (2.14)): the matrix of the forward form
`z_t = B E_t z_{t+1} + w_t` of (2.1), (2.23) under the one-period-ahead forecast rule,
`B = [[β + κσ(1 − φ_π), κ(1 − σφ_x/4)], [σ(1 − φ_π), 1 − σφ_x/4]]`. -/
noncomputable def fcB1 (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β + κ * σ * (1 - φπ), κ * (1 - σ * φx / 4); σ * (1 - φπ), 1 - σ * φx / 4]

omit 𝔼 in
/-- Woodford (2003), (3.13) with `k = 1`: the forcing `w_t = (κσ e_t + u_t, σ e_t)`,
`e_t = rⁿ_t − ī + π̄`. -/
noncomputable def fcW1 (σ κ ibar πbar : ℝ) (u rn : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![fun ω => κ * σ * (rn t ω - ibar + πbar) + u t ω,
    fun ω => σ * (rn t ω - ibar + πbar)]

omit 𝔼 in
/-- Woodford (2003), (3.13) with `k = 1`, state by state: the AS and IS relations under the
one-period-ahead forecast rule are the forward form in deviations from `(π̄, x̄)`. -/
theorem fc1_pt {β σ κ φπ φx πbar xb ibar : ℝ} (hxb : κ * xb = (1 - β) * πbar)
    {p x P X rn uu r : ℝ} (hr : r = ibar + φπ * (P - πbar) + φx * (X - xb) / 4) :
    (x = X - σ * (r - P - rn) ∧ p = κ * x + β * P + uu) ↔
      (p - πbar = fcB1 β σ κ φπ φx 0 0 * (P - πbar) + fcB1 β σ κ φπ φx 0 1 * (X - xb)
          + (κ * σ * (rn - ibar + πbar) + uu) ∧
        x - xb = fcB1 β σ κ φπ φx 1 0 * (P - πbar) + fcB1 β σ κ φπ φx 1 1 * (X - xb)
          + σ * (rn - ibar + πbar)) := by
  subst hr
  simp only [fcB1, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h2 + κ * h1 + hxb, by linear_combination h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linear_combination h2, by linear_combination h1 - κ * h2 - hxb⟩

/-- Woodford (2003), (3.13) with `k = 1`: the model under the one-period-ahead forecast rule is the
forward system `z_t = B E_t z_{t+1} + w_t` in deviations from `(π̄, x̄)`. -/
theorem forecastEqm_one_iff_solves {β σ κ φπ φx πbar xbar ibar : ℝ}
    (hxb : κ * xbar = (1 - β) * πbar) (u rn π x : ℕ → Ω → ℝ) :
    ForecastEqm 𝔼 β σ κ ibar φπ φx πbar xbar 1 u rn π x ↔
      𝔼.Solves (fcB1 β σ κ φπ φx) (fcW1 σ κ ibar πbar u rn) (devStack π x πbar xbar) := by
  rw [solves_dev_iff, ForecastEqm, AS_iff, IS_iff, ← forall_and]
  refine forall_congr' fun t => ?_
  rw [← forall_and]
  refine forall_congr' fun ω => ?_
  rw [and_comm]
  simp only [fcW1, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact fc1_pt hxb (by simp [forecastRule])

/-- **Prop. 7.13 for `k = 1`, exact** (Woodford (2003), p. 516 and Ch. 4, §2.2): under the
one-period-ahead forecast rule, equilibrium is determinate (exactly one bounded adapted
equilibrium for every bounded adapted `(u, rⁿ)`) iff `B` satisfies the Schur–Cohn condition, with
`tr B = 1 + β + κσ(1 − φ_π) − σφ_x/4` and `det B = β(1 − σφ_x/4)`. -/
theorem forecast1_determinate_iff [Nonempty Ω] {β σ κ φπ φx πbar xbar ibar : ℝ}
    (hxb : κ * xbar = (1 - β) * πbar) :
    ModelDet 𝔼 (ForecastEqm 𝔼 β σ κ ibar φπ φx πbar xbar 1) ↔
      SchurStable (1 + β + κ * σ * (1 - φπ) - σ * φx / 4) (β * (1 - σ * φx / 4)) := by
  have htr : tr2 (fcB1 β σ κ φπ φx) = 1 + β + κ * σ * (1 - φπ) - σ * φx / 4 := by
    simp only [fcB1, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have hdet : det2 (fcB1 β σ κ φπ φx) = β * (1 - σ * φx / 4) := by
    simp only [fcB1, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [← htr, ← hdet]
  refine modelDet_iff_of_reduction 𝔼 (W := fun u rn => fcW1 σ κ ibar πbar u rn)
    (fun u rn π x => forecastEqm_one_iff_solves 𝔼 hxb u rn π x) ?_ ?_
  · intro u rn hu hrn hau harn
    obtain ⟨M₁, hM₁⟩ := hu
    obtain ⟨M₂, hM₂⟩ := hrn
    refine ⟨⟨|κ * σ| * (M₂ + |ibar| + |πbar|) + M₁ + |σ| * (M₂ + |ibar| + |πbar|),
      fun t i ω => ?_⟩, fun t i => ?_⟩
    · have he : |rn t ω - ibar + πbar| ≤ M₂ + |ibar| + |πbar| := by
        calc |rn t ω - ibar + πbar| ≤ |rn t ω - ibar| + |πbar| := abs_add_le _ _
          _ ≤ |rn t ω| + |ibar| + |πbar| := by gcongr; exact abs_sub _ _
          _ ≤ M₂ + |ibar| + |πbar| := by gcongr; exact hM₂ t ω
      have a1 : |κ * σ * (rn t ω - ibar + πbar)| ≤ |κ * σ| * (M₂ + |ibar| + |πbar|) := by
        rw [abs_mul]; gcongr
      have a3 : |σ * (rn t ω - ibar + πbar)| ≤ |σ| * (M₂ + |ibar| + |πbar|) := by
        rw [abs_mul]; gcongr
      have p1 : 0 ≤ |κ * σ| * (M₂ + |ibar| + |πbar|) := (abs_nonneg _).trans a1
      have p3 : 0 ≤ |σ| * (M₂ + |ibar| + |πbar|) := (abs_nonneg _).trans a3
      have p2 : 0 ≤ M₁ := (abs_nonneg _).trans (hM₁ t ω)
      fin_cases i
      · simp only [fcW1, Fin.zero_eta, Matrix.cons_val_zero]
        exact (abs_add_le _ _).trans (by linarith [hM₁ t ω])
      · simp only [fcW1, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        linarith
    · have e0 : (fun ω => κ * σ * (rn t ω - ibar + πbar) + u t ω) =
          (κ * σ) • rn t + (fun _ => κ * σ * (πbar - ibar)) + u t := by
        funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      have e1 : (fun ω => σ * (rn t ω - ibar + πbar)) =
          σ • rn t + (fun _ => σ * (πbar - ibar)) := by
        funext ω; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      fin_cases i
      · simp only [fcW1, Fin.zero_eta, Matrix.cons_val_zero]
        rw [e0, map_add, map_add, map_smul, 𝔼.const, harn t, hau t]
      · simp only [fcW1, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [e1, map_add, map_smul, 𝔼.const, harn t]
  · refine ⟨fun _ _ => 0, fun _ _ => ibar - πbar, ⟨0, fun _ _ => by simp⟩,
      ⟨|ibar - πbar|, fun _ _ => le_rfl⟩, fun t => 𝔼.const t 0, fun t => 𝔼.const t _, ?_⟩
    funext t i ω
    fin_cases i <;> simp [fcW1]


/-! ### Proposition 7.13 and footnote 37 -/

/-- Woodford (2003), (3.14), p. 516: with a common `ρ ≠ 0` and `D(ρ) λᵢ ≠ 0`, the optimal
noninertial plan (long-run values (3.11), F.4 responses) is an equilibrium under the forecast rule
(3.13) with coefficients `φ_y = ρ^{−k} φ̄_y`, `φ̄_y` as in (3.12), for every horizon `k`. -/
theorem oni_forecastEqm {β κ σ rbar lx li istar ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx)
    (hli : 0 ≤ li) (hρ : ρ ≠ 0) (hD : Drho β κ σ ρ * li ≠ 0) {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hr : 𝔼.IsAR1 ρ r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) (k : ℕ) :
    ForecastEqm 𝔼 β σ κ is ((ρ ^ k)⁻¹ * phiPiStar β κ σ li ρ)
      ((ρ ^ k)⁻¹ * phiXStar β κ σ lx li ρ) (Noninertial.piBar119 β li rbar istar) xs k u
      (fun t ω => rbar + r t ω)
      (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρ)
        (Noninertial.piRF4 β κ σ lx li ρ) u r)
      (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r) := by
  set πs := Noninertial.piBar119 β li rbar istar
  have hxb : (1 - β) * πs = κ * xs := by rw [hxs]; field_simp
  have hrule : plan2 is (Noninertial.iUF4 β κ σ lx li ρ) (Noninertial.iRF4 β κ σ lx li ρ) u r =
      taylorRule is (phiPiStar β κ σ li ρ) (phiXStar β κ σ lx li ρ) πs xs
        (plan2 πs (Noninertial.piUF4 β κ σ lx li ρ) (Noninertial.piRF4 β κ σ lx li ρ) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r) := by
    rw [taylorRule_plan2, rule_matches_f4_u hκ hσ hlx hli hD, rule_matches_f4_r hκ hσ hlx hli hD]
    congr 1 <;> ring
  obtain ⟨c1, c2⟩ := Noninertial.f4_u_feasible (β := β) (ρ := ρ) hκ hσ hlx hli
  obtain ⟨c3, c4⟩ := Noninertial.f4_r_feasible (β := β) (ρ := ρ) hκ hσ hlx hli
  have hAI := plan2_of 𝔼 hu hr hxb his c1 c2 c3 c4
  unfold ForecastEqm
  rw [forecast_rule_consistent 𝔼 hρ hu hr, ← hrule]
  exact hAI

/-- **Proposition 7.13** (Woodford (2003), p. 516; proof in Giannoni–Woodford, only cited in the
book; proved here): let the disturbances be bounded AR(1) processes with a common `ρ ∈ (0, 1)`
(`rⁿ = r̄ + r̂ⁿ`), `κ, σ, λₓ, λᵢ > 0`, `0 < β < 1` and `D(ρ) λᵢ > 0` (the lower bound of (3.10)).
Then there is `K` such that for every horizon `k ≥ K` the forecast rule (3.13) with (3.14) is
consistent with the optimal noninertial plan and yet admits a second, different, bounded adapted
equilibrium: equilibrium is indeterminate. Explicitly, any `k ≥ 2` with
`ρᵏ < σβφ̄_x/4` works (Vieta: the characteristic polynomial then has a root inside the unit
disc). -/
theorem prop_7_13 [Nonempty Ω] {β κ σ rbar lx li istar ρ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hD : 0 < Drho β κ σ ρ * li) {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hr : 𝔼.IsAR1 ρ r)
    (hub : BoundedProc u) (hrb : BoundedProc r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    ∃ K, ∀ k, K ≤ k →
      ForecastEqm 𝔼 β σ κ is ((ρ ^ k)⁻¹ * phiPiStar β κ σ li ρ)
        ((ρ ^ k)⁻¹ * phiXStar β κ σ lx li ρ) (Noninertial.piBar119 β li rbar istar) xs k u
        (fun t ω => rbar + r t ω)
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρ)
          (Noninertial.piRF4 β κ σ lx li ρ) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρ) (Noninertial.xRF4 β κ σ lx li ρ) u r) ∧
      ∃ π' x' : ℕ → Ω → ℝ, ForecastEqm 𝔼 β σ κ is ((ρ ^ k)⁻¹ * phiPiStar β κ σ li ρ)
        ((ρ ^ k)⁻¹ * phiXStar β κ σ lx li ρ) (Noninertial.piBar119 β li rbar istar) xs k u
        (fun t ω => rbar + r t ω) π' x' ∧
        BoundedProc π' ∧ BoundedProc x' ∧ 𝔼.Adapted π' ∧ 𝔼.Adapted x' ∧
        π' ≠ plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρ)
          (Noninertial.piRF4 β κ σ lx li ρ) u r := by
  have hφx : 0 < phiXStar β κ σ lx li ρ := by
    have hφ : phiPiStar β κ σ li ρ = (Drho β κ σ ρ * li)⁻¹ := by
      unfold phiPiStar; rw [mul_inv]
    have ha : 0 < 1 - β * ρ := by
      have : 0 < Drho β κ σ ρ := (mul_pos_iff_of_pos_right hli).mp hD
      unfold Drho at this
      by_contra h
      push Not at h
      have : (1 - β * ρ) * (1 - ρ) / (κ * σ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h (by linarith))
          (by positivity)
      linarith
    unfold phiXStar
    rw [hφ]
    have := inv_pos.mpr hD
    positivity
  set ε := σ * β * phiXStar β κ σ lx li ρ / 4 with hε
  have hεpos : 0 < ε := by positivity
  obtain ⟨K0, hK0⟩ := exists_pow_lt_of_lt_one hεpos hρ1
  refine ⟨max K0 2, fun k hk => ⟨oni_forecastEqm 𝔼 hκ hσ hlx.le hli.le hρ0.ne' hD.ne' hu hr hxs
    his k, ?_⟩⟩
  have hk2 : 2 ≤ k := le_trans (le_max_right _ _) hk
  have hkK : K0 ≤ k := le_trans (le_max_left _ _) hk
  have hρk : ρ ^ k < ε := lt_of_le_of_lt (pow_le_pow_of_le_one hρ0.le hρ1.le hkK) hK0
  have hρkpos : 0 < ρ ^ k := pow_pos hρ0 k
  have hl : 1 < |σ * β * ((ρ ^ k)⁻¹ * phiXStar β κ σ lx li ρ) / 4| := by
    have e : σ * β * ((ρ ^ k)⁻¹ * phiXStar β κ σ lx li ρ) / 4 = ε / ρ ^ k := by
      rw [hε]; field_simp
    rw [e, abs_of_pos (by positivity), one_lt_div hρkpos]
    exact hρk
  obtain ⟨lam, hroot, -, hlam⟩ := exists_root_inside (β := β) (κ := κ)
    (φπ := (ρ ^ k)⁻¹ * phiPiStar β κ σ li ρ) hk2 hl
  obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 (Noninertial.piBar119 β li rbar istar)
    (Noninertial.piUF4 β κ σ lx li ρ) (Noninertial.piRF4 β κ σ lx li ρ)
  obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 xs (Noninertial.xUF4 β κ σ lx li ρ)
    (Noninertial.xRF4 β κ σ lx li ρ)
  exact indeterminate_of_root 𝔼 hκ.ne' hroot hlam.le
    (oni_forecastEqm 𝔼 hκ hσ hlx.le hli.le hρ0.ne' hD.ne' hu hr hxs his k) b1 b2 a1 a2

omit 𝔼 in
/-- Woodford (2003), fn. 37 (the calibration inequality): at `β = .99`, `κ = .024`, `σ = 6.25`,
`λₓ = .003`, `λᵢ = .236`, for every `ρ ∈ (0, 1)` with `D(ρ) > 0`, `σβφ̄_x/(4ρ) > 1 + β`. -/
theorem fn37_ineq {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hD : 0 < Drho (99 / 100) (24 / 1000) (625 / 100) ρ) :
    1 + 99 / 100 < 625 / 100 * (99 / 100) * phiXStar (99 / 100) (24 / 1000) (625 / 100)
      (3 / 1000) (236 / 1000) ρ / 4 / ρ := by
  have hφ : phiPiStar (99 / 100) (24 / 1000) (625 / 100) (236 / 1000) ρ =
      (Drho (99 / 100) (24 / 1000) (625 / 100) ρ * (236 / 1000))⁻¹ := by
    unfold phiPiStar; rw [mul_inv]
  have hDl : 0 < Drho (99 / 100) (24 / 1000) (625 / 100) ρ * (236 / 1000) := by positivity
  unfold phiXStar
  rw [hφ, lt_div_iff₀ hρ0]
  have key : Drho (99 / 100) (24 / 1000) (625 / 100) ρ * (236 / 1000) * ((1 + 99 / 100) * ρ) <
      625 / 100 * (99 / 100) * (1 - 99 / 100 * ρ) * (3 / 1000 / (24 / 1000)) := by
    unfold Drho
    have h1 := mul_nonneg (sq_nonneg (ρ - 2 / 5)) (by linarith : (0 : ℝ) ≤ 1 - ρ)
    have h2 := sq_nonneg (ρ - 2 / 5)
    have e1 : (ρ - 2 / 5) ^ 2 * (1 - ρ) = -ρ ^ 3 + 9 / 5 * ρ ^ 2 - 24 / 25 * ρ + 4 / 25 := by
      ring
    have e2 : (ρ - 2 / 5) ^ 2 = ρ ^ 2 - 4 / 5 * ρ + 4 / 25 := by ring
    rw [e1] at h1
    rw [e2] at h2
    have e3 : ((1 - 99 / 100 * ρ) * (1 - ρ) / (24 / 1000 * (625 / 100)) - ρ) * (236 / 1000) *
        ((1 + 99 / 100) * ρ) = 46964 / 15000 * (ρ - 214 / 100 * ρ ^ 2 + 99 / 100 * ρ ^ 3) := by
      ring
    rw [e3]
    linarith [h1, h2]
  rw [show 625 / 100 * (99 / 100) * (4 * ((1 - 99 / 100 * ρ) * (3 / 1000 / (24 / 1000)) *
      (Drho (99 / 100) (24 / 1000) (625 / 100) ρ * (236 / 1000))⁻¹)) / 4 =
      625 / 100 * (99 / 100) * (1 - 99 / 100 * ρ) * (3 / 1000 / (24 / 1000)) /
        (Drho (99 / 100) (24 / 1000) (625 / 100) ρ * (236 / 1000)) by field_simp]
  rw [lt_div_iff₀ hDl]
  linarith

/-- **Footnote 37** (Woodford (2003), p. 516): "in the case of the calibrated parameter values
given in Table 6.1, the rule (3.13) with coefficients (3.14) implies indeterminacy for all
`k ≥ 1`" — proved at `β = .99`, `κ = .024`, `σ = 6.25`, `λₓ = .003`, `λᵢ = .236` (the values that
reproduce fn. 32, survey E10) for every `ρ ∈ (0, 1)` with `D(ρ) > 0` (in particular on the whole
interval (3.10)) and every horizon `k ≥ 1`: the optimal noninertial plan is an equilibrium under
the rule, and so is a different bounded adapted process. -/
theorem fn37 [Nonempty Ω] {rbar istar ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hD : 0 < Drho (99 / 100) (24 / 1000) (625 / 100) ρ) {u r : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ u) (hr : 𝔼.IsAR1 ρ r) (hub : BoundedProc u) (hrb : BoundedProc r)
    {xs is : ℝ}
    (hxs : xs = (1 - 99 / 100) / (24 / 1000) * Noninertial.piBar119 (99 / 100) (236 / 1000) rbar
      istar)
    (his : is = rbar + Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ π' x' : ℕ → Ω → ℝ, ForecastEqm 𝔼 (99 / 100) (625 / 100) (24 / 1000) is
      ((ρ ^ k)⁻¹ * phiPiStar (99 / 100) (24 / 1000) (625 / 100) (236 / 1000) ρ)
      ((ρ ^ k)⁻¹ * phiXStar (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) ρ)
      (Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar) xs k u
      (fun t ω => rbar + r t ω) π' x' ∧
      BoundedProc π' ∧ BoundedProc x' ∧ 𝔼.Adapted π' ∧ 𝔼.Adapted x' ∧
      π' ≠ plan2 (Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar)
        (Noninertial.piUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) ρ)
        (Noninertial.piRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) ρ) u r := by
  have hDl : 0 < Drho (99 / 100) (24 / 1000) (625 / 100) ρ * (236 / 1000) := by positivity
  have hin := fn37_ineq hρ0 hρ1 hD
  set φx := phiXStar (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) ρ with hφx
  have hρkpos : 0 < ρ ^ k := pow_pos hρ0 k
  have hρk : ρ ^ k ≤ ρ := by
    calc ρ ^ k ≤ ρ ^ 1 := pow_le_pow_of_le_one hρ0.le hρ1.le hk
      _ = ρ := pow_one ρ
  have hge : 625 / 100 * (99 / 100) * φx / 4 / ρ ≤ 625 / 100 * (99 / 100) * φx / 4 / ρ ^ k := by
    have hpos : 0 ≤ 625 / 100 * (99 / 100) * φx / 4 := by
      have := hin; have : 0 < 625 / 100 * (99 / 100) * φx / 4 / ρ := by linarith
      have := (div_pos_iff_of_pos_right hρ0).mp this
      linarith
    exact div_le_div_of_nonneg_left hpos hρkpos hρk
  have hbig : 1 + 99 / 100 < 625 / 100 * (99 / 100) * ((ρ ^ k)⁻¹ * φx) / 4 := by
    have : 625 / 100 * (99 / 100) * ((ρ ^ k)⁻¹ * φx) / 4 =
        625 / 100 * (99 / 100) * φx / 4 / ρ ^ k := by field_simp
    rw [this]; linarith
  obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1
    (Noninertial.piBar119 (99 / 100) (236 / 1000) rbar istar)
    (Noninertial.piUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) ρ)
    (Noninertial.piRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) ρ)
  obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 xs
    (Noninertial.xUF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) ρ)
    (Noninertial.xRF4 (99 / 100) (24 / 1000) (625 / 100) (3 / 1000) (236 / 1000) ρ)
  have heq := oni_forecastEqm 𝔼 (β := 99 / 100) (κ := 24 / 1000) (σ := 625 / 100)
    (lx := 3 / 1000) (li := 236 / 1000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hρ0.ne' hDl.ne' hu hr hxs his k
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hk1' : k = 1 := by omega
    subst hk1'
    have hl : 1 < |99 / 100 * (1 - 625 / 100 * ((ρ ^ 1)⁻¹ * φx) / 4)| := by
      rw [abs_of_neg (by nlinarith)]
      nlinarith
    obtain ⟨lam, hroot, -, hlam⟩ := exists_root_inside_one (κ := 24 / 1000)
      (φπ := (ρ ^ 1)⁻¹ * phiPiStar (99 / 100) (24 / 1000) (625 / 100) (236 / 1000) ρ) hl
    exact indeterminate_of_root 𝔼 (by norm_num) hroot hlam.le heq b1 b2 a1 a2
  · have hl : 1 < |625 / 100 * (99 / 100) * ((ρ ^ k)⁻¹ * φx) / 4| := by
      rw [abs_of_pos (by linarith)]
      linarith
    obtain ⟨lam, hroot, -, hlam⟩ := exists_root_inside (β := 99 / 100) (κ := 24 / 1000)
      (φπ := (ρ ^ k)⁻¹ * phiPiStar (99 / 100) (24 / 1000) (625 / 100) (236 / 1000) ρ) hk2 hl
    exact indeterminate_of_root 𝔼 (by norm_num) hroot hlam.le heq b1 b2 a1 a2


/-! ### p. 515: an open set of `(ρ_r, ρ_u)` with `ρ_r ≠ ρ_u`

The book (p. 515) argues that the feedback coefficients making the Taylor rule consistent with the
optimal noninertial plan solve a `2 × 2` linear system, depend continuously on `(ρ_r, ρ_u)` where
the system is nonsingular, and so keep `φ_π, φ_x > 0` and (3.9) on an open set of `(ρ_r, ρ_u)`
around the diagonal points satisfying (3.10). Precisely: the set `RuleSet` of `p = (ρ_r, ρ_u)` at
which the system is nonsingular and its solution is positive and satisfies (3.9) is open
(`ruleSet_open`), contains `(ρ, ρ)` whenever (3.10) holds at `ρ < 1` (`diag_mem_ruleSet`), and
contains points with `0 < ρ_r ≠ ρ_u < 1` (`exists_offdiag_ruleSet`); at every point of it the
rule implements the optimal noninertial plan, is determinate and is the optimal Taylor rule
(`prop_7_12_general`, `prop_7_12_optimal_general`). The book's claim is correct. -/

omit 𝔼 in
/-- Woodford (2003), p. 515: the determinant of the linear system
`φ_π π_u + (φ_x/4) x_u = i_u`, `φ_π π_r + (φ_x/4) x_r = i_r` for `p = (ρ_r, ρ_u)`. -/
noncomputable def detG (β κ σ lx li : ℝ) (p : ℝ × ℝ) : ℝ :=
  Noninertial.piUF4 β κ σ lx li p.2 * Noninertial.xRF4 β κ σ lx li p.1 -
    Noninertial.xUF4 β κ σ lx li p.2 * Noninertial.piRF4 β κ σ lx li p.1

omit 𝔼 in
/-- Woodford (2003), p. 515: the solution `φ_π(ρ_r, ρ_u)` of the system (Cramer's rule). -/
noncomputable def phiPiG (β κ σ lx li : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Noninertial.iUF4 β κ σ lx li p.2 * Noninertial.xRF4 β κ σ lx li p.1 -
    Noninertial.xUF4 β κ σ lx li p.2 * Noninertial.iRF4 β κ σ lx li p.1) / detG β κ σ lx li p

omit 𝔼 in
/-- Woodford (2003), p. 515: the solution `φ_x(ρ_r, ρ_u)` of the system (Cramer's rule). -/
noncomputable def phiXG (β κ σ lx li : ℝ) (p : ℝ × ℝ) : ℝ :=
  4 * ((Noninertial.piUF4 β κ σ lx li p.2 * Noninertial.iRF4 β κ σ lx li p.1 -
    Noninertial.iUF4 β κ σ lx li p.2 * Noninertial.piRF4 β κ σ lx li p.1) / detG β κ σ lx li p)

omit 𝔼 in
/-- Woodford (2003), p. 515: the set of `(ρ_r, ρ_u)` at which the system is nonsingular and its
solution has `φ_π, φ_x > 0` and satisfies the Taylor principle (3.9). -/
def RuleSet (β κ σ lx li : ℝ) : Set (ℝ × ℝ) :=
  {p | detG β κ σ lx li p ≠ 0 ∧ 0 < phiPiG β κ σ lx li p ∧ 0 < phiXG β κ σ lx li p ∧
    1 < taylorLHS β κ (phiPiG β κ σ lx li p) (phiXG β κ σ lx li p)}

omit 𝔼 in
/-- Woodford (2003), p. 515: where the system is nonsingular, `(φ_π, φ_x)(ρ_r, ρ_u)` makes the
Taylor rule reproduce the F.4 interest-rate responses to both disturbances. -/
theorem rule_matches_general {β κ σ lx li : ℝ} {p : ℝ × ℝ} (hd : detG β κ σ lx li p ≠ 0) :
    Noninertial.iUF4 β κ σ lx li p.2 = phiPiG β κ σ lx li p * Noninertial.piUF4 β κ σ lx li p.2
        + phiXG β κ σ lx li p / 4 * Noninertial.xUF4 β κ σ lx li p.2 ∧
      Noninertial.iRF4 β κ σ lx li p.1 = phiPiG β κ σ lx li p *
        Noninertial.piRF4 β κ σ lx li p.1 + phiXG β κ σ lx li p / 4 *
          Noninertial.xRF4 β κ σ lx li p.1 := by
  have hinv := mul_inv_cancel₀ hd
  have hdef : detG β κ σ lx li p = Noninertial.piUF4 β κ σ lx li p.2 *
      Noninertial.xRF4 β κ σ lx li p.1 - Noninertial.xUF4 β κ σ lx li p.2 *
        Noninertial.piRF4 β κ σ lx li p.1 := rfl
  unfold phiPiG phiXG
  simp only [div_eq_mul_inv]
  constructor
  · linear_combination (-Noninertial.iUF4 β κ σ lx li p.2) * hinv +
      Noninertial.iUF4 β κ σ lx li p.2 * (detG β κ σ lx li p)⁻¹ * hdef
  · linear_combination (-Noninertial.iRF4 β κ σ lx li p.1) * hinv +
      Noninertial.iRF4 β κ σ lx li p.1 * (detG β κ σ lx li p)⁻¹ * hdef

omit 𝔼 in
/-- Woodford (2003), p. 515 (tool, Cramer's rule): a solution of a nonsingular `2 × 2` system is
the Cramer solution. -/
theorem cramer_unique {a1 b1 c1 a2 b2 c2 x y : ℝ} (hd : a1 * b2 - b1 * a2 ≠ 0)
    (h1 : c1 = x * a1 + y * b1) (h2 : c2 = x * a2 + y * b2) :
    x = (c1 * b2 - b1 * c2) / (a1 * b2 - b1 * a2) ∧
      y = (a1 * c2 - c1 * a2) / (a1 * b2 - b1 * a2) := by
  constructor
  · rw [eq_div_iff hd, h1, h2]; ring
  · rw [eq_div_iff hd, h1, h2]; ring

omit 𝔼 in
/-- Woodford (2003), p. 515: on the diagonal `ρ_r = ρ_u = ρ` the determinant is
`λᵢ σ⁻¹ (γ − ρκσ)/h`, nonzero when `D(ρ) λᵢ ≠ 0`. -/
theorem detG_diag {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li) :
    detG β κ σ lx li (ρ, ρ) = li * σ⁻¹ * (Noninertial.gamF4 β ρ - ρ * κ * σ) /
      Noninertial.hF4 β κ σ lx li ρ := by
  have hh := (Noninertial.hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx hli).ne'
  have hσ' := hσ.ne'
  unfold detG
  simp only
  unfold Noninertial.piUF4 Noninertial.xRF4 Noninertial.xUF4 Noninertial.piRF4
  field_simp
  unfold Noninertial.hF4 Noninertial.xiF4 Noninertial.gamF4
  field_simp
  ring

omit 𝔼 in
/-- Woodford (2003), p. 515: on the diagonal, when (3.10)'s lower bound holds, the system is
nonsingular and its solution is (3.12). -/
theorem phiG_diag {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 < li)
    (hD : 0 < Drho β κ σ ρ * li) :
    detG β κ σ lx li (ρ, ρ) ≠ 0 ∧ phiPiG β κ σ lx li (ρ, ρ) = phiPiStar β κ σ li ρ ∧
      phiXG β κ σ lx li (ρ, ρ) = phiXStar β κ σ lx li ρ := by
  have hh := Noninertial.hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx hli.le
  have hG : Noninertial.gamF4 β ρ - ρ * κ * σ ≠ 0 := by
    rw [← kappa_sigma_Drho hκ.ne' hσ.ne']
    have : 0 < Drho β κ σ ρ := (mul_pos_iff_of_pos_right hli).mp hD
    positivity
  have hd : detG β κ σ lx li (ρ, ρ) ≠ 0 := by
    rw [detG_diag hκ hσ hlx hli.le]
    have : σ⁻¹ ≠ 0 := inv_ne_zero hσ.ne'
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hli.ne' this) hG) hh.ne'
  obtain ⟨e1, e2⟩ := cramer_unique (x := phiPiStar β κ σ li ρ) (y := phiXStar β κ σ lx li ρ / 4)
    hd (rule_matches_f4_u hκ hσ hlx hli.le hD.ne') (rule_matches_f4_r hκ hσ hlx hli.le hD.ne')
  have e1' : phiPiStar β κ σ li ρ = (Noninertial.iUF4 β κ σ lx li ρ *
      Noninertial.xRF4 β κ σ lx li ρ - Noninertial.xUF4 β κ σ lx li ρ *
        Noninertial.iRF4 β κ σ lx li ρ) / detG β κ σ lx li (ρ, ρ) := e1
  have e2' : phiXStar β κ σ lx li ρ / 4 = (Noninertial.piUF4 β κ σ lx li ρ *
      Noninertial.iRF4 β κ σ lx li ρ - Noninertial.iUF4 β κ σ lx li ρ *
        Noninertial.piRF4 β κ σ lx li ρ) / detG β κ σ lx li (ρ, ρ) := e2
  refine ⟨hd, ?_, ?_⟩
  · unfold phiPiG; rw [e1']
  · unfold phiXG; rw [← e2']; ring

omit 𝔼 in
/-- Woodford (2003), p. 515 (tool): the F.4 coefficients are continuous in `ρ`. -/
theorem f4_continuous {β κ σ lx li : ℝ} (hκ : 0 < κ) (hlx : 0 ≤ lx) (hli : 0 ≤ li) :
    Continuous (fun ρ => Noninertial.piUF4 β κ σ lx li ρ) ∧
      Continuous (fun ρ => Noninertial.xUF4 β κ σ lx li ρ) ∧
      Continuous (fun ρ => Noninertial.iUF4 β κ σ lx li ρ) ∧
      Continuous (fun ρ => Noninertial.piRF4 β κ σ lx li ρ) ∧
      Continuous (fun ρ => Noninertial.xRF4 β κ σ lx li ρ) ∧
      Continuous (fun ρ => Noninertial.iRF4 β κ σ lx li ρ) := by
  have hne : ∀ ρ, Noninertial.hF4 β κ σ lx li ρ ≠ 0 := fun ρ =>
    (Noninertial.hF4_pos hκ.ne' hlx hli).ne'
  have hc : Continuous (fun ρ => Noninertial.hF4 β κ σ lx li ρ) := by
    unfold Noninertial.hF4 Noninertial.gamF4; fun_prop
  unfold Noninertial.piUF4 Noninertial.xUF4 Noninertial.iUF4 Noninertial.piRF4
    Noninertial.xRF4 Noninertial.iRF4
  refine ⟨.div ?_ hc hne, .div ?_ hc hne, .div ?_ hc hne, .div ?_ hc hne, .div ?_ hc hne,
    .div ?_ hc hne⟩ <;>
  · (try unfold Noninertial.xiF4); (try unfold Noninertial.gamF4); fun_prop

omit 𝔼 in
/-- Woodford (2003), p. 515 ("since the required feedback coefficients are continuous functions
of the model parameters … the inequality is also satisfied for all model parameters (including
values of `ρ_r` and `ρ_u`) that are sufficiently close"): `RuleSet` is open in `ℝ²`. -/
theorem ruleSet_open {β κ σ lx li : ℝ} (hκ : 0 < κ) (hlx : 0 ≤ lx) (hli : 0 ≤ li) :
    IsOpen (RuleSet β κ σ lx li) := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := f4_continuous (β := β) (σ := σ) hκ hlx hli
  have hdet : Continuous (detG β κ σ lx li) := by
    unfold detG
    exact ((c1.comp continuous_snd).mul (c5.comp continuous_fst)).sub
      ((c2.comp continuous_snd).mul (c4.comp continuous_fst))
  have hn1 : Continuous fun p : ℝ × ℝ => Noninertial.iUF4 β κ σ lx li p.2 *
      Noninertial.xRF4 β κ σ lx li p.1 - Noninertial.xUF4 β κ σ lx li p.2 *
        Noninertial.iRF4 β κ σ lx li p.1 :=
    ((c3.comp continuous_snd).mul (c5.comp continuous_fst)).sub
      ((c2.comp continuous_snd).mul (c6.comp continuous_fst))
  have hn2 : Continuous fun p : ℝ × ℝ => Noninertial.piUF4 β κ σ lx li p.2 *
      Noninertial.iRF4 β κ σ lx li p.1 - Noninertial.iUF4 β κ σ lx li p.2 *
        Noninertial.piRF4 β κ σ lx li p.1 :=
    ((c1.comp continuous_snd).mul (c6.comp continuous_fst)).sub
      ((c3.comp continuous_snd).mul (c4.comp continuous_fst))
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨hd, h1, h2, h3⟩
  have k1 : ContinuousAt (phiPiG β κ σ lx li) p := hn1.continuousAt.div hdet.continuousAt hd
  have k2 : ContinuousAt (phiXG β κ σ lx li) p :=
    continuousAt_const.mul (hn2.continuousAt.div hdet.continuousAt hd)
  have k3 : ContinuousAt (fun q => taylorLHS β κ (phiPiG β κ σ lx li q)
      (phiXG β κ σ lx li q)) p := by
    unfold taylorLHS
    exact k1.add ((continuousAt_const.mul k2).div_const _)
  filter_upwards [hdet.continuousAt.eventually_ne hd, k1.eventually (lt_mem_nhds h1),
    k2.eventually (lt_mem_nhds h2), k3.eventually (lt_mem_nhds h3)] with q a b c d
  exact ⟨a, b, c, d⟩

omit 𝔼 in
/-- Woodford (2003), p. 515: every diagonal point `(ρ, ρ)` with `ρ < 1` satisfying (3.10) lies in
`RuleSet` (`κ, σ, λₓ, λᵢ > 0`). -/
theorem diag_mem_ruleSet {β κ σ lx li ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) (hρ1 : ρ < 1) (h310 : Cond310 β κ σ lx li ρ) :
    (ρ, ρ) ∈ RuleSet β κ σ lx li := by
  have hβρ : β * ρ < 1 := by nlinarith [h310.1]
  obtain ⟨hd, e1, e2⟩ := phiG_diag hκ hσ hlx.le hli h310.1
  obtain ⟨a, b, c⟩ := prop_7_12_coeffs hκ hlx hβρ h310
  exact ⟨hd, e1 ▸ a, e2 ▸ b, e1 ▸ e2 ▸ c⟩

omit 𝔼 in
/-- Woodford (2003), p. 515 ("there is thus an open set of nonnegative values for `(ρ_r, ρ_u)`"):
`RuleSet` contains a point `(ρ_r, ρ_u)` with `0 < ρ_r, ρ_u < 1` and `ρ_r ≠ ρ_u`. -/
theorem exists_offdiag_ruleSet {β κ σ lx li : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 < li) :
    ∃ ρr ρu, 0 < ρr ∧ ρr < 1 ∧ 0 < ρu ∧ ρu < 1 ∧ ρr ≠ ρu ∧ (ρr, ρu) ∈ RuleSet β κ σ lx li := by
  obtain ⟨ρ, h0, h1, h310⟩ := exists_pos_rho_cond310 hβ0 hβ1 hκ hσ hlx.le hli
  have hmem := diag_mem_ruleSet hβ0 hβ1 hκ hσ hlx hli h1 h310
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (ruleSet_open (β := β) (σ := σ) hκ hlx.le hli.le)
    _ hmem
  set δ := min ε (1 - ρ) / 2 with hδ
  have hδ0 : 0 < δ := by have : 0 < min ε (1 - ρ) := lt_min hε (by linarith); positivity
  have hδ1 : δ < ε := by have := min_le_left ε (1 - ρ); linarith
  have hδ2 : δ < 1 - ρ := by have := min_le_right ε (1 - ρ); linarith
  refine ⟨ρ, ρ + δ, h0, h1, by linarith, by linarith, by linarith, hball ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_self, abs_zero,
    show ρ + δ - ρ = δ by ring, abs_of_pos hδ0, max_eq_right hδ0.le]
  exact hδ1

/-- **Proposition 7.12 for `ρ_r ≠ ρ_u`** (Woodford (2003), p. 515): at every `(ρ_r, ρ_u) ∈ RuleSet`
with `ρ_r, ρ_u < 1`, and bounded AR(1) disturbances `u` (persistence `ρ_u`) and `r̂ⁿ` (`ρ_r`), the
Taylor rule with intercepts (3.11) and coefficients `(φ_π, φ_x)(ρ_r, ρ_u)` (both positive,
satisfying (3.9)) reproduces the optimal noninertial plan's interest rate, the plan is an
equilibrium under it, equilibrium is determinate, and the plan is the unique bounded adapted
equilibrium. -/
theorem prop_7_12_general [Nonempty Ω] {β κ σ rbar lx li istar ρr ρu : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx) (hli : 0 ≤ li)
    (hS : (ρr, ρu) ∈ RuleSet β κ σ lx li) {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u)
    (hr : 𝔼.IsAR1 ρr r) (hub : BoundedProc u) (hrb : BoundedProc r) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r =
      taylorRule is (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu))
        (Noninertial.piBar119 β li rbar istar) xs
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) ∧
    ModelDet 𝔼 (TaylorEqm 𝔼 β σ κ is (phiPiG β κ σ lx li (ρr, ρu))
      (phiXG β κ σ lx li (ρr, ρu)) (Noninertial.piBar119 β li rbar istar) xs) ∧
    ∀ π x : ℕ → Ω → ℝ, BoundedProc π → BoundedProc x → 𝔼.Adapted π → 𝔼.Adapted x →
      (TaylorEqm 𝔼 β σ κ is (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu))
        (Noninertial.piBar119 β li rbar istar) xs u (fun t ω => rbar + r t ω) π x ↔
      π = plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
        (Noninertial.piRF4 β κ σ lx li ρr) u r ∧
      x = plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
  obtain ⟨hd, h1, h2, h3⟩ := hS
  obtain ⟨m1, m2⟩ := rule_matches_general hd
  set πs := Noninertial.piBar119 β li rbar istar
  have hxb : κ * xs = (1 - β) * πs := by rw [hxs]; field_simp
  have hrule : plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r =
      taylorRule is (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu)) πs xs
        (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
    rw [taylorRule_plan2]
    simp only at m1 m2
    rw [m1, m2]
    congr 1 <;> ring
  have heq : TaylorEqm 𝔼 β σ κ is (phiPiG β κ σ lx li (ρr, ρu)) (phiXG β κ σ lx li (ρr, ρu))
      πs xs u (fun t ω => rbar + r t ω)
      (plan2 πs (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.piRF4 β κ σ lx li ρr) u r)
      (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) := by
    obtain ⟨c1, c2⟩ := Noninertial.f4_u_feasible (β := β) (ρ := ρu) hκ hσ hlx hli
    obtain ⟨c3, c4⟩ := Noninertial.f4_r_feasible (β := β) (ρ := ρr) hκ hσ hlx hli
    unfold TaylorEqm
    rw [← hrule]
    exact plan2_of 𝔼 hu hr (by linarith [hxb]) his c1 c2 c3 c4
  have hdet := (taylor_determinate_iff 𝔼 (ibar := is) hβ0 hβ1 hσ hκ h1.le h2.le hxb).mpr h3
  refine ⟨hrule, hdet, fun π x hπb hxb' hπa hxa => ⟨fun hπx => ?_, ?_⟩⟩
  · have hrn : BoundedProc (fun t ω => rbar + r t ω) := by
      obtain ⟨N, hN⟩ := hrb
      exact ⟨|rbar| + N, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hN t ω))⟩
    have hrna : 𝔼.Adapted (fun t ω => rbar + r t ω) := by
      intro t
      change 𝔼.E t (fun ω => rbar + r t ω) = fun ω => rbar + r t ω
      have e : (fun ω => rbar + r t ω) = (fun _ => rbar) + r t := rfl
      rw [e, map_add, 𝔼.const, hr.1 t]
    obtain ⟨p, -, hpu⟩ := hdet u (fun t ω => rbar + r t ω) hub hrn hu.1 hrna
    obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 πs (Noninertial.piUF4 β κ σ lx li ρu)
      (Noninertial.piRF4 β κ σ lx li ρr)
    obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 xs (Noninertial.xUF4 β κ σ lx li ρu)
      (Noninertial.xRF4 β κ σ lx li ρr)
    have e1 := hpu (π, x) ⟨hπb, hxb', hπa, hxa, hπx⟩
    have e2 := hpu (_, _) ⟨b1, b2, a1, a2, heq⟩
    have := e1.trans e2.symm
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨rfl, rfl⟩
    exact heq

/-- **Proposition 7.12, optimality, for `ρ_r ≠ ρ_u`** (Woodford (2003), p. 515): with independent
AR(1) disturbances (persistences `ρ_r`, `ρ_u ∈ [0, 1)`, innovation variances `s_r, s_u > 0`),
non-degenerate as a pair, and the pull-out property, any bounded adapted equilibrium under any
Taylor rule with `φ_π, φ_x ≥ 0` satisfying (3.9) has a stabilization loss at least that of the
optimal noninertial plan — which, for `(ρ_r, ρ_u) ∈ RuleSet`, is the equilibrium under the rule
`(φ_π, φ_x)(ρ_r, ρ_u)` (`prop_7_12_general`). -/
theorem prop_7_12_optimal_general (hpo : 𝔼.PullOut) {β κ σ rbar lx li istar ρr ρu su sr : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li)
    (hρr0 : 0 ≤ ρr) (hρr1 : ρr < 1) (hρu0 : 0 ≤ ρu) (hρu1 : ρu < 1) (hsu : 0 < su) (hsr : 0 < sr)
    {u εu r εr : ℕ → Ω → ℝ}
    (hu : Noninertial.AR1Innov 𝔼 ρu su u εu) (hr : Noninertial.AR1Innov 𝔼 ρr sr r εr)
    (hind : ∀ t, 𝔼.E t (εu (t + 1) * εr (t + 1)) = fun _ => 0) (hnd : Nondeg2 u r)
    (hub : BoundedProc u) (hrb : BoundedProc r) (t₀ : ℕ) (ω : Ω) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar)
    {ibar φπ φx πbar xbar : ℝ} (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hT : 1 < taylorLHS β κ φπ φx)
    (hxb : κ * xbar = (1 - β) * πbar) {π x : ℕ → Ω → ℝ} (hπb : BoundedProc π)
    (hxbd : BoundedProc x) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (heq : TaylorEqm 𝔼 β σ κ ibar φπ φx πbar xbar u (fun t ω => rbar + r t ω) π x) :
    Noninertial.Lstab 𝔼 β lx li t₀
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ω ≤
      Noninertial.Lstab 𝔼 β lx li t₀ π x (taylorRule ibar φπ φx πbar xbar π x) ω := by
  have hρua : |ρu| < 1 := abs_lt.mpr ⟨by linarith, hρu1⟩
  have hρra : |ρr| < 1 := abs_lt.mpr ⟨by linarith, hρr1⟩
  have hrn : BoundedProc (fun t ω => rbar + r t ω) := by
    obtain ⟨N, hN⟩ := hrb
    exact ⟨|rbar| + N, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hN t ω))⟩
  have hrna : 𝔼.Adapted (fun t ω => rbar + r t ω) := by
    intro t
    change 𝔼.E t (fun ω => rbar + r t ω) = fun ω => rbar + r t ω
    have e : (fun ω => rbar + r t ω) = (fun _ => rbar) + r t := rfl
    rw [e, map_add, 𝔼.const, hr.1 t]
  have : Nonempty Ω := ⟨ω⟩
  have hdet := (taylor_determinate_iff 𝔼 (ibar := ibar) hβ0 hβ1 hσ hκ hφπ hφx hxb).mpr hT
  have hplan := taylor_eqm_plan2 𝔼 (rbar := rbar) (ibar := ibar) hβ0 hβ1 hσ hκ hφx hT hxb hρu1
    hρr1 hu.isAR1 hr.isAR1
  obtain ⟨b1, a1⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1 (pbarT β κ φπ φx rbar ibar πbar)
    (fpiT β κ σ φπ φx ρu) (gpiT β κ σ φπ φx ρr)
  obtain ⟨b2, a2⟩ := plan2_bdd_adapted 𝔼 hub hrb hu.1 hr.1
    (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρu) (gxT β κ σ φπ φx ρr)
  obtain ⟨p, -, hpu⟩ := hdet u _ hub hrn hu.1 hrna
  have e1 := hpu (π, x) ⟨hπb, hxbd, hπa, hxa, heq⟩
  have e2 := hpu (plan2 (pbarT β κ φπ φx rbar ibar πbar) (fpiT β κ σ φπ φx ρu)
    (gpiT β κ σ φπ φx ρr) u r, plan2 (xbarT β κ φπ φx rbar ibar πbar xbar) (fxT β κ σ φπ φx ρu)
    (gxT β κ σ φπ φx ρr) u r) ⟨b1, b2, a1, a2, hplan⟩
  have hpx := e1.trans e2.symm
  simp only [Prod.mk.injEq] at hpx
  obtain ⟨rfl, rfl⟩ := hpx
  rw [taylorRule_plan2]
  have hAI := hplan
  unfold TaylorEqm at hAI
  rw [taylorRule_plan2] at hAI
  exact ((Noninertial.f4_lstab 𝔼 hpo hβ0 hβ1 hκ hσ hlx hli hρua hρra hsu hsr hu hr hind hnd t₀
    ω hxs his).2 _ _ _ _ _ _ _ _ _ hAI.1 hAI.2).1

end Woodford.GainsFromCommitment.OptimalTaylor
