/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.LinearizedIdentities
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Block

/-!
# VAR identities: Neumann sums, the inflation decompositions and the PV tautology

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3–4.4, pp. 99–116, and
Online Appendix Chapter 2, §2.2, pp. 604–605.

The terms of the inflation decompositions (4.14)–(4.16) are sums of VAR impulse-response
functions, computed with matrix Neumann series; and with the value of debt in the VAR, the
present-value relation (2.26) is an identity (A2, (2.24)–(2.26)).

## Main definitions

* `innov 𝔼 t x` (from `Innovations`): the innovation (news) operator
  `Δ_{t+1} x = E_{t+1} x − E_t x` (the book's `ΔE_{t+1}`).
* `IsVAR A z ε`: the VAR (4.17) `z_{t+1} = A z_t + ε_{t+1}` with random-variable coordinates;
  `ShockMDS 𝔼 ε`: the shocks are adapted and unforecastable; `obs c y = c'y` an observable.
* `PowDecay A`: the powers of `A` decay geometrically (`powDecay_of_eigs`: implied by all complex
  eigenvalues in the open unit disc, Gelfand's formula).

## Main results

* `inv_one_sub_hasSum`, `neumann_bilin_hasSum` (pp. 111–112): `∑ Aʲ = (I − A)⁻¹`;
  `disc_rate_hasSum`: `∑_{j≥1} (1 − ωʲ) Aʲ = A(I − A)⁻¹ − ωA(I − ωA)⁻¹`.
* `var_forecast`, `var_innov`: `E_t z_{t+k} = Aᵏ z_t`, `Δ_{t+1} z_{t+1+k} = Aᵏ ε_{t+1}`;
  `var_sum_responses`, `var_disc_rate_sum`: the sums of responses of p. 112.
* `identity_4_15`, `identity_4_16`, `identity_4_14`: the decompositions for any processes
  satisfying the flow identity and the bond-return identity (with general `ρ`, `ω`; the book's
  case is `ρ = 1`), with the transversality-type limits and summability as explicit hypotheses;
  `identity_4_14_of_var`, `identity_4_15_of_var`: in a stable VAR satisfying the identities, all
  those hypotheses hold automatically ("all the variables are stationary, impulse-responses die
  out", p. 103).
* `regression_eq_cholesky`, `filled_shock_eq_orthogonalized`, `regression_coeff_single` (4.17):
  filling in shocks by regressions on the inflation shock is the Cholesky orthogonalisation with
  inflation ordered first; `functional_regression`, `surplus_shock_sum` (4.18).
* `flow_restriction_of_identity` (2.25), `flow_restriction_iff_pv` ((2.25) ⇔ (2.26), needing only
  `I − ρA` invertible, survey E18), `var_pv_identity`: in a stable VAR satisfying the flow
  identity, the VAR present value of surpluses *is* the value of debt (the tautology of p. 605).
-/

namespace Cochrane.DebtDeficitsInflation.VARIdentities

open Filter Topology
open scoped Matrix
open Cochrane.DebtDeficitsInflation.Innovations (innov innov_apply innov_of_known)
open Cochrane.DebtDeficitsInflation.LinearizedIdentities (Flow BondReturn seriesTo_of_hasSum
  unexpected_inflation_identity bond_return_identity)

/-! ### The innovation operator, VARs and shocks -/

variable {Ω κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Cochrane (2023), eq. (4.17), p. 104: the VAR `z_{t+1} = A z_t + ε_{t+1}`, coordinate by
coordinate, with random-variable coordinates `z t i : Ω → ℝ`. -/
def IsVAR (A : Matrix κ κ ℝ) (z ε : ℕ → κ → Ω → ℝ) : Prop :=
  ∀ t i, z (t + 1) i = ∑ j, A i j • z t j + ε (t + 1) i

/-- Cochrane (2023), eq. (4.17), p. 104: the VAR shocks are unforecastable, `E_t ε_{t+1} = 0`. -/
def ShockMDS (𝔼 : ExpectationSystem Ω) (ε : ℕ → κ → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (ε (t + 1) i) = 0

/-- Cochrane (2023), p. 112 ("`a_s, a_g` pick `s` and `g` out of the VAR, `s_t = a_s' x_t`"):
the observable `c'y` of a vector of random variables. -/
def obs (c : κ → ℝ) (y : κ → Ω → ℝ) : Ω → ℝ := ∑ i, c i • y i

/-- Cochrane (2023), p. 112: the realisation of a vector of random variables at a state. -/
def vecAt (y : κ → Ω → ℝ) (w : Ω) : κ → ℝ := fun i => y i w

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: an observable evaluated at a state is a dot product. -/
theorem obs_apply (c : κ → ℝ) (y : κ → Ω → ℝ) (w : Ω) : obs c y w = c ⬝ᵥ vecAt y w := by
  simp [obs, vecAt, dotProduct, Finset.sum_apply]

/-! ### Geometric decay of matrix powers -/

/-- Cochrane (2023), p. 103 ("all the variables are stationary, impulse-responses die out"): the
entries of the powers of `A` decay geometrically. -/
def PowDecay (A : Matrix κ κ ℝ) : Prop :=
  ∃ Cb r : ℝ, 0 ≤ Cb ∧ 0 ≤ r ∧ r < 1 ∧ ∀ k i j, |(A ^ k) i j| ≤ Cb * r ^ k

/-- Cochrane (2023), Online Appendix p. 605 ("the eigenvalues of `A` are less than one"): the
complex eigenvalues of a real square matrix, with multiplicity (restated from the Woodford
Chapter 4 project, `InvariantSplit.eigs`). -/
noncomputable def eigs (K : Matrix κ κ ℝ) : Multiset ℂ := (K.map Complex.ofReal).charpoly.roots

/-- Cochrane (2023), Online Appendix p. 605: powers of the complexified matrix are the
complexified powers (restated from the Woodford Chapter 4 project). -/
theorem map_ofReal_pow (K : Matrix κ κ ℝ) (t : ℕ) :
    (K ^ t).map Complex.ofReal = K.map Complex.ofReal ^ t :=
  Matrix.map_pow K Complex.ofRealHom t

/-- Cochrane (2023), Online Appendix p. 605 ("so long as the variables are stationary, the
eigenvalues of `A` are less than one"): if every complex eigenvalue of `A` lies in the open unit
disc, the powers of `A` decay geometrically (Gelfand's formula; restated from the Woodford
Chapter 4 project, `InvariantSplit.pow_entry_bound`). -/
theorem powDecay_of_eigs (K : Matrix κ κ ℝ) (h : ∀ μ ∈ eigs K, ‖μ‖ < 1) : PowDecay K := by
  let _ : NormedRing (Matrix κ κ ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix κ κ ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix κ κ ℂ := K.map Complex.ofReal with hA
  have hspec : ∀ w ∈ spectrum ℂ A, w ∈ A.charpoly.roots.toFinset ∧ ‖w‖ < 1 := by
    intro w hw
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hw
    have hm : w ∈ A.charpoly.roots := by
      rw [Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero]; exact hw
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
  refine ⟨Cb, r, hCb0, hr0.le, hr1, fun k i j => ?_⟩
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

/-- Cochrane (2023), p. 112 (the weights `ωʲ`): scaling a decaying matrix by `|ω| ≤ 1` keeps the
geometric decay of its powers. -/
theorem powDecay_smul {A : Matrix κ κ ℝ} (hA : PowDecay A) {ω : ℝ} (hω : |ω| ≤ 1) :
    PowDecay (ω • A) := by
  obtain ⟨Cb, r, hCb, hr0, hr1, hb⟩ := hA
  refine ⟨Cb, r, hCb, hr0, hr1, fun k i j => ?_⟩
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_pow]
  calc |ω| ^ k * |(A ^ k) i j| ≤ 1 * (Cb * r ^ k) :=
        mul_le_mul (pow_le_one₀ (abs_nonneg _) hω) (hb k i j) (abs_nonneg _) zero_le_one
    _ = Cb * r ^ k := one_mul _

/-- Cochrane (2023), pp. 111–112: each entry of the powers of a decaying matrix is absolutely
summable. -/
theorem summable_pow_entry {A : Matrix κ κ ℝ} (hA : PowDecay A) (i j : κ) :
    Summable (fun k => (A ^ k) i j) := by
  obtain ⟨Cb, r, _, hr0, hr1, hb⟩ := hA
  exact Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left Cb)
    (fun k => by rw [Real.norm_eq_abs]; exact hb k i j)

/-- Cochrane (2023), pp. 111–112: the entries of the powers of a decaying matrix tend to zero. -/
theorem tendsto_pow_entry {A : Matrix κ κ ℝ} (hA : PowDecay A) (i j : κ) :
    Tendsto (fun k => (A ^ k) i j) atTop (𝓝 0) :=
  (summable_pow_entry hA i j).tendsto_atTop_zero

/-- Cochrane (2023), pp. 111–112: the Neumann sum `∑_k Aᵏ`, entry by entry. -/
noncomputable def neumannSum (A : Matrix κ κ ℝ) : Matrix κ κ ℝ :=
  Matrix.of fun i j => ∑' k, (A ^ k) i j

/-- Cochrane (2023), pp. 111–112: `(∑_k Aᵏ)(I − A) = I` for a decaying matrix. -/
theorem neumannSum_mul {A : Matrix κ κ ℝ} (hA : PowDecay A) : neumannSum A * (1 - A) = 1 := by
  ext i j
  have hs := fun l => summable_pow_entry hA i l
  have hrow : ∀ k, ∑ l, (A ^ k) i l * (1 - A) l j = (A ^ k) i j - (A ^ (k + 1)) i j := by
    intro k
    rw [← Matrix.mul_apply, Matrix.mul_sub, Matrix.mul_one, ← pow_succ, Matrix.sub_apply]
  have hS : HasSum (fun k => (A ^ k) i j - (A ^ (k + 1)) i j) ((neumannSum A * (1 - A)) i j) := by
    simp only [Matrix.mul_apply, neumannSum, Matrix.of_apply]
    have := hasSum_sum (s := Finset.univ) fun l _ => (hs l).hasSum.mul_right ((1 - A) l j)
    simpa only [hrow] using this
  have h1 := summable_pow_entry hA i j
  have h2 : Summable (fun k => (A ^ (k + 1)) i j) := (summable_nat_add_iff 1).mpr h1
  rw [← hS.tsum_eq, Summable.tsum_sub h1 h2, h1.tsum_eq_zero_add, pow_zero, add_sub_cancel_right]

/-- Cochrane (2023), pp. 111–112: for a decaying matrix `I − A` is invertible and
`(I − A)⁻¹ = ∑_k Aᵏ`. -/
theorem inv_one_sub_eq {A : Matrix κ κ ℝ} (hA : PowDecay A) : (1 - A)⁻¹ = neumannSum A :=
  Matrix.inv_eq_left_inv (neumannSum_mul hA)

/-- Cochrane (2023), pp. 111–112: for a decaying matrix `I − A` is invertible. -/
theorem isUnit_det_one_sub {A : Matrix κ κ ℝ} (hA : PowDecay A) : IsUnit (1 - A).det :=
  Matrix.isUnit_det_of_left_inverse (neumannSum_mul hA)

/-- Cochrane (2023), pp. 111–112: the matrix Neumann series `∑_k Aᵏ = (I − A)⁻¹`, entry by entry,
for a matrix whose powers decay (e.g. all eigenvalues in the open unit disc). -/
theorem inv_one_sub_hasSum {A : Matrix κ κ ℝ} (hA : PowDecay A) (i j : κ) :
    HasSum (fun k => (A ^ k) i j) ((1 - A)⁻¹ i j) := by
  rw [inv_one_sub_eq hA]
  exact (summable_pow_entry hA i j).hasSum

omit [DecidableEq κ] in
/-- Cochrane (2023), pp. 111–112 (tool): entrywise sums pass to a bilinear form `c'(·)e`. -/
theorem hasSum_bilin {M : ℕ → Matrix κ κ ℝ} {S : Matrix κ κ ℝ}
    (h : ∀ i j, HasSum (fun k => M k i j) (S i j)) (c e : κ → ℝ) :
    HasSum (fun k => c ⬝ᵥ (M k *ᵥ e)) (c ⬝ᵥ (S *ᵥ e)) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine hasSum_sum fun i _ => hasSum_sum fun j _ => ?_
  have := ((h i j).mul_right (e j)).mul_left (c i)
  simpa [mul_assoc] using this

/-- Cochrane (2023), p. 112: `∑_k c'Aᵏe = c'(I − A)⁻¹e` — the sum of the responses of an
observable `c'z` to a VAR shock `e`. -/
theorem neumann_bilin_hasSum {A : Matrix κ κ ℝ} (hA : PowDecay A) (c e : κ → ℝ) :
    HasSum (fun k => c ⬝ᵥ ((A ^ k) *ᵥ e)) (c ⬝ᵥ ((1 - A)⁻¹ *ᵥ e)) :=
  hasSum_bilin (inv_one_sub_hasSum hA) c e

/-- Cochrane (2023), p. 112 (the discount-rate shock): entrywise,
`∑_{j≥1} (1 − ωʲ) Aʲ = A(I − A)⁻¹ − ωA(I − ωA)⁻¹` for a decaying `A` and `|ω| ≤ 1`. -/
theorem disc_rate_hasSum {A : Matrix κ κ ℝ} (hA : PowDecay A) {ω : ℝ} (hω : |ω| ≤ 1)
    (i j : κ) :
    HasSum (fun k => (1 - ω ^ (k + 1)) * (A ^ (k + 1)) i j)
      ((A * (1 - A)⁻¹ - ω • A * (1 - ω • A)⁻¹) i j) := by
  have hωA := powDecay_smul hA hω
  have h1 : HasSum (fun k => (A * A ^ k) i j) ((A * (1 - A)⁻¹) i j) := by
    simp only [Matrix.mul_apply]
    exact hasSum_sum fun l _ => (inv_one_sub_hasSum hA l j).mul_left _
  have h2 : HasSum (fun k => ((ω • A) * (ω • A) ^ k) i j) ((ω • A * (1 - ω • A)⁻¹) i j) := by
    simp only [Matrix.mul_apply]
    exact hasSum_sum fun l _ => (inv_one_sub_hasSum hωA l j).mul_left _
  have h3 := h1.sub h2
  rw [← Matrix.sub_apply] at h3
  convert h3 using 1
  funext k
  rw [← pow_succ', ← pow_succ', smul_pow, Matrix.smul_apply, smul_eq_mul, pow_succ' A k]
  ring

/-! ### VAR forecasts and impulse responses -/

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: the innovation of an observable is the observable of the
innovations. -/
theorem innov_obs (𝔼 : ExpectationSystem Ω) (t : ℕ) (c : κ → ℝ) (y : κ → Ω → ℝ) :
    innov 𝔼 t (obs c y) = obs c (fun i => innov 𝔼 t (y i)) := by
  simp only [innov_apply, obs, map_sum, map_smul, smul_sub]

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: the conditional expectation of an observable is the observable of
the conditional expectations. -/
theorem E_obs (𝔼 : ExpectationSystem Ω) (t : ℕ) (c : κ → ℝ) (y : κ → Ω → ℝ) :
    𝔼.E t (obs c y) = obs c (fun i => 𝔼.E t (y i)) := by
  simp only [obs, map_sum, map_smul]

/-- Cochrane (2023), eq. (4.17), p. 104: VAR forecasts, `E_t z_{t+k} = Aᵏ z_t`. -/
theorem var_forecast (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (t k : ℕ) (i : κ) : 𝔼.E t (z (t + k) i) = ∑ j, (A ^ k) i j • z t j := by
  induction k generalizing i with
  | zero =>
    simp [hz t i, Matrix.one_apply, ite_smul]
  | succ k ih =>
    have e : z (t + (k + 1)) i = ∑ j, A i j • z (t + k) j + ε (t + k + 1) i := hvar (t + k) i
    have hε : 𝔼.E t (ε (t + k + 1) i) = 0 := by
      rw [← 𝔼.tower (Nat.le_add_right t k), hmds (t + k) i, map_zero]
    rw [e, map_add, map_sum, hε, add_zero]
    simp only [map_smul, ih]
    rw [pow_succ']
    simp only [Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm

/-- Cochrane (2023), eq. (4.17) and p. 104 ("I start the VAR at `ε_1`"): the impulse response,
`Δ_{t+1} z_{t+1+k} = Aᵏ ε_{t+1}`. -/
theorem var_innov (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (t k : ℕ) (i : κ) : innov 𝔼 t (z (t + 1 + k) i) = ∑ j, (A ^ k) i j • ε (t + 1) j := by
  have h1 := var_forecast 𝔼 hvar hmds hz (t + 1) k i
  have h2 := var_forecast 𝔼 hvar hmds hz t (k + 1) i
  rw [show t + (k + 1) = t + 1 + k by omega] at h2
  rw [innov_apply, h1, h2]
  simp only [hvar t, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  rw [pow_succ]
  simp only [Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun x y => ((A ^ k) i x * A x y) • z t y)]
  abel

/-- Cochrane (2023), p. 112: the response of an observable, `Δ_{t+1} c'z_{t+1+k} = c'Aᵏε_{t+1}`. -/
theorem var_innov_obs (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (c : κ → ℝ) (t k : ℕ) (w : Ω) :
    innov 𝔼 t (obs c (z (t + 1 + k))) w = c ⬝ᵥ ((A ^ k) *ᵥ vecAt (ε (t + 1)) w) := by
  rw [innov_obs, obs_apply]
  congr 1
  funext i
  simp only [vecAt, var_innov 𝔼 hvar hmds hz t k, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct]

/-- Cochrane (2023), p. 112: the forecast of an observable, `E_t c'z_{t+k} = c'Aᵏz_t`. -/
theorem var_forecast_obs (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (c : κ → ℝ) (t k : ℕ) (w : Ω) :
    𝔼.E t (obs c (z (t + k))) w = c ⬝ᵥ ((A ^ k) *ᵥ vecAt (z t) w) := by
  rw [E_obs, obs_apply]
  congr 1
  funext i
  simp only [vecAt, var_forecast 𝔼 hvar hmds hz t k, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct]

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 103: an observable of an adapted VAR state is known at its date. -/
theorem obs_adapted (𝔼 : ExpectationSystem Ω) {z : ℕ → κ → Ω → ℝ}
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (c : κ → ℝ) (t : ℕ) :
    𝔼.E t (obs c (z t)) = obs c (z t) := by
  rw [E_obs]
  simp only [hz]

/-- Cochrane (2023), p. 112: `ρʲ c'Aʲe = c'(ρA)ʲe`. -/
theorem weight_bilin (A : Matrix κ κ ℝ) (ρ : ℝ) (c e : κ → ℝ) (j : ℕ) :
    ρ ^ j * c ⬝ᵥ ((A ^ j) *ᵥ e) = c ⬝ᵥ (((ρ • A) ^ j) *ᵥ e) := by
  rw [smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Cochrane (2023), pp. 111–112: in a stable VAR, the `ρ`-weighted sum of the responses of an
observable is `∑ ρʲ Δ_{t+1} c'z_{t+1+j} = c'(I − ρA)⁻¹ε_{t+1}` (`|ρ| ≤ 1`). -/
theorem var_weighted_sum (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1) (c : κ → ℝ) (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (obs c (z (t + 1 + j))) w)
      (c ⬝ᵥ ((1 - ρ • A)⁻¹ *ᵥ vecAt (ε (t + 1)) w)) := by
  simp only [var_innov_obs 𝔼 hvar hmds hz, weight_bilin]
  exact neumann_bilin_hasSum (powDecay_smul hA hρ) c _

/-- Cochrane (2023), p. 112: the response of the sum of current and future surpluses and growth,
`Δ_1 ∑_{j≥0} (s̃_{1+j} + g_{1+j}) = (a_s + a_g)'(I − A)⁻¹ε_1`. -/
theorem var_sum_responses (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) (c : κ → ℝ) (t : ℕ) (w : Ω) :
    HasSum (fun j => innov 𝔼 t (obs c (z (t + 1 + j))) w)
      (c ⬝ᵥ ((1 - A)⁻¹ *ᵥ vecAt (ε (t + 1)) w)) := by
  have := var_weighted_sum 𝔼 hvar hmds hz hA (ρ := 1) (by simp) c t w
  simpa using this

/-- Cochrane (2023), p. 112: the response of the discount-rate term, with `c = a_{rⁿ} − a_π`,
`Δ_1 ∑_{j≥1} (1 − ωʲ) r_{1+j} = c'[A(I − A)⁻¹ − ωA(I − ωA)⁻¹]ε_1` (`|ω| ≤ 1`). -/
theorem var_disc_rate_sum (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ω : ℝ} (hω : |ω| ≤ 1) (c : κ → ℝ) (t : ℕ) (w : Ω) :
    HasSum (fun j => (1 - ω ^ (j + 1)) * innov 𝔼 t (obs c (z (t + 2 + j))) w)
      (c ⬝ᵥ ((A * (1 - A)⁻¹ - ω • A * (1 - ω • A)⁻¹) *ᵥ vecAt (ε (t + 1)) w)) := by
  have h := hasSum_bilin (M := fun k => (1 - ω ^ (k + 1)) • A ^ (k + 1))
    (S := A * (1 - A)⁻¹ - ω • A * (1 - ω • A)⁻¹)
    (fun i j => by simpa only [Matrix.smul_apply, smul_eq_mul] using disc_rate_hasSum hA hω i j)
    c (vecAt (ε (t + 1)) w)
  refine h.congr_fun fun j => ?_
  rw [show t + 2 + j = t + 1 + (j + 1) by omega, var_innov_obs 𝔼 hvar hmds hz,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-! ### The inflation decompositions (4.14)–(4.16) -/

/-- Cochrane (2023), eq. (4.15), p. 103 (= (3.20); with the index typo `g_{t+1+j}`, `r_{t+1+j}`
corrected to `g_{1+j}`, `r_{1+j}`, survey E6), for general `ρ` (the book uses `ρ = 1`): if the
flow identity `ρv_{t+1} = v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} − s̃_{t+1}` holds at every date, `v_t`
is known at `t`, the revisions are summable and `ρᵀ Δ v_{t+1+T} → 0`, then
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}ρʲΔr_{t+1+j}`, `r = rⁿ − π`.
Derived from the canonical (3.20), `LinearizedIdentities.unexpected_inflation_identity`. -/
theorem identity_4_15 (𝔼 : ExpectationSystem Ω) {ρ : ℝ} {v s g rn pi : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t + rn (t + 1) - pi (t + 1) - g (t + 1) - s (t + 1))
    (t : ℕ) (hv : 𝔼.E t (v t) = v t) (w : Ω) {S G R : ℝ}
    (hS : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) w) S)
    (hG : HasSum (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) w) G)
    (hR : HasSum (fun j => ρ ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j) - pi (t + 2 + j)) w) R)
    (hlim : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + 1 + T)) w) atTop (𝓝 0)) :
    innov 𝔼 t (pi (t + 1)) w - innov 𝔼 t (rn (t + 1)) w = -S - G + R := by
  have hflow' : Flow ρ v (fun t => rn t - pi t) g s := fun t => by
    rw [hflow t]
    change _ = v t + (rn (t + 1) - pi (t + 1)) - g (t + 1) - s (t + 1)
    abel
  have hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) w) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have h := hlim.const_mul ρ
    rw [mul_zero] at h
    refine h.congr fun T => ?_
    rw [pow_succ, show t + (T + 1) = t + 1 + T by omega]
    ring
  have h1 := unexpected_inflation_identity 𝔼 hflow' (fun _ => rfl) hv hT
    (seriesTo_of_hasSum hS) (seriesTo_of_hasSum hG)
  have h2 := (seriesTo_of_hasSum hR).unique h1
  linarith

/-- Cochrane (2023), eq. (4.16), p. 104 (= (3.21)): if the bond return obeys
`rⁿ_{t+1} = ω q_{t+1} − q_t` (the geometric-maturity identity, `q` the log bond price), `q_t` is
known at `t`, the revisions are summable and `ωᵀ Δ q_{t+1+T} → 0`, then
`Δrⁿ_{t+1} = −∑_{j≥1} ωʲ Δrⁿ_{t+1+j}`. Derived from the canonical (3.21),
`LinearizedIdentities.bond_return_identity`. -/
theorem identity_4_16 (𝔼 : ExpectationSystem Ω) {om : ℝ} {q rn : ℕ → Ω → ℝ}
    (hbond : ∀ t, rn (t + 1) = om • q (t + 1) - q t) (t : ℕ) (hq : 𝔼.E t (q t) = q t)
    (w : Ω) {Q : ℝ} (hQ : HasSum (fun j => om ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j)) w) Q)
    (hlim : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) w) atTop (𝓝 0)) :
    innov 𝔼 t (rn (t + 1)) w = -Q := by
  have h := bond_return_identity 𝔼 (om := om) (q := q) (rn := rn) hbond hq hlim
  have h2 := (seriesTo_of_hasSum hQ).unique h
  linarith

/-- Cochrane (2023), eq. (4.14), p. 103 (= (3.22)), for general `ρ` (the book's case is `ρ = 1`,
where the weights are `1 − ωʲ`): under the hypotheses of `identity_4_15` and `identity_4_16`,
`∑_{j≥0} ωʲΔπ_{t+1+j} = −∑ρʲΔs̃_{t+1+j} − ∑ρʲΔg_{t+1+j} + ∑_{j≥1}(ρʲ − ωʲ)Δr_{t+1+j}`, each
series converging. -/
theorem identity_4_14 (𝔼 : ExpectationSystem Ω) {ρ om : ℝ} {v s g rn pi q : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t + rn (t + 1) - pi (t + 1) - g (t + 1) - s (t + 1))
    (hbond : ∀ t, rn (t + 1) = om • q (t + 1) - q t)
    (t : ℕ) (hv : 𝔼.E t (v t) = v t) (hq : 𝔼.E t (q t) = q t) (w : Ω) {S G R Qr Qp : ℝ}
    (hS : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) w) S)
    (hG : HasSum (fun j => ρ ^ j * innov 𝔼 t (g (t + 1 + j)) w) G)
    (hR : HasSum (fun j => ρ ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j) - pi (t + 2 + j)) w) R)
    (hQr : HasSum (fun j => om ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j) - pi (t + 2 + j)) w) Qr)
    (hQp : HasSum (fun j => om ^ (j + 1) * innov 𝔼 t (pi (t + 2 + j)) w) Qp)
    (hlimv : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + 1 + T)) w) atTop (𝓝 0))
    (hlimq : Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) w) atTop (𝓝 0)) :
    HasSum (fun j => om ^ j * innov 𝔼 t (pi (t + 1 + j)) w) (-S - G + (R - Qr)) ∧
    HasSum (fun j => (ρ ^ (j + 1) - om ^ (j + 1)) *
      innov 𝔼 t (rn (t + 2 + j) - pi (t + 2 + j)) w) (R - Qr) := by
  have hQ : HasSum (fun j => om ^ (j + 1) * innov 𝔼 t (rn (t + 2 + j)) w) (Qr + Qp) := by
    refine (hQr.add hQp).congr_fun fun j => ?_
    simp only [map_sub, Pi.sub_apply]
    ring
  have h16 := identity_4_16 𝔼 hbond t hq w hQ hlimq
  have h15 := identity_4_15 𝔼 hflow t hv w hS hG hR hlimv
  refine ⟨?_, (hR.sub hQr).congr_fun fun j => by ring⟩
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero]
  convert hQp using 1
  · funext j
    rw [show t + 1 + (j + 1) = t + 2 + j by omega]
  · linarith

/-- Cochrane (2023), p. 103: in a stable VAR the shifted weighted sums of responses converge. -/
theorem var_shifted_summable (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (c : κ → ℝ) (t : ℕ) (w : Ω) :
    Summable (fun j => ρ ^ (j + 1) * innov 𝔼 t (obs c (z (t + 2 + j))) w) := by
  have h := (summable_nat_add_iff 1).mpr (var_weighted_sum 𝔼 hvar hmds hz hA hρ c t w).summable
  refine h.congr fun j => ?_
  rw [show t + 1 + (j + 1) = t + 2 + j by omega]

/-- Cochrane (2023), eq. (4.15), p. 103, in a stable VAR (`IsVAR`, `PowDecay`, `|ρ| ≤ 1`) whose
observables satisfy the flow identity at every date: every series converges and
`Δπ_{t+1} − Δrⁿ_{t+1} = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}ρʲΔr` holds with no further hypothesis
(the book's "all the variables are stationary, impulse-responses die out", p. 103). -/
theorem identity_4_15_of_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    {av as ag arn api : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs arn (z (t + 1)) -
      obs api (z (t + 1)) - obs ag (z (t + 1)) - obs as (z (t + 1))) (t : ℕ) (w : Ω) :
    innov 𝔼 t (obs api (z (t + 1))) w - innov 𝔼 t (obs arn (z (t + 1))) w =
      -(∑' j, ρ ^ j * innov 𝔼 t (obs as (z (t + 1 + j))) w)
      - (∑' j, ρ ^ j * innov 𝔼 t (obs ag (z (t + 1 + j))) w)
      + ∑' j, ρ ^ (j + 1) * innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w := by
  have hR : Summable (fun j => ρ ^ (j + 1) *
      innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w) := by
    refine ((var_shifted_summable 𝔼 hvar hmds hz hA hρ arn t w).sub
      (var_shifted_summable 𝔼 hvar hmds hz hA hρ api t w)).congr fun j => ?_
    simp only [map_sub, Pi.sub_apply]
    ring
  refine identity_4_15 𝔼 (v := fun t => obs av (z t)) (s := fun t => obs as (z t))
    (g := fun t => obs ag (z t)) (rn := fun t => obs arn (z t)) (pi := fun t => obs api (z t))
    hflow t (obs_adapted 𝔼 hz av t) w
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ as t w).summable.hasSum
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ ag t w).summable.hasSum hR.hasSum
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ av t w).summable.tendsto_atTop_zero

/-- Cochrane (2023), eqs. (4.14) and (4.16), pp. 103–104, in a stable VAR (`IsVAR`, `PowDecay`,
`|ρ| ≤ 1`, `|ω| ≤ 1`) whose observables satisfy the flow identity and the bond-return identity
`rⁿ_{t+1} = ωq_{t+1} − q_t` at every date: every series converges and
`∑ωʲΔπ_{t+1+j} = −∑ρʲΔs̃ − ∑ρʲΔg + ∑_{j≥1}(ρʲ − ωʲ)Δr_{t+1+j}` (at `ρ = 1`: weights `1 − ωʲ`),
and `Δrⁿ_{t+1} = −∑_{j≥1}ωʲΔrⁿ_{t+1+j}`. -/
theorem identity_4_14_of_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (hA : PowDecay A) {ρ om : ℝ} (hρ : |ρ| ≤ 1)
    (hom : |om| ≤ 1) {av as ag arn api aq : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs arn (z (t + 1)) -
      obs api (z (t + 1)) - obs ag (z (t + 1)) - obs as (z (t + 1)))
    (hbond : ∀ t, obs arn (z (t + 1)) = om • obs aq (z (t + 1)) - obs aq (z t)) (t : ℕ)
    (w : Ω) :
    ∑' j, om ^ j * innov 𝔼 t (obs api (z (t + 1 + j))) w =
      -(∑' j, ρ ^ j * innov 𝔼 t (obs as (z (t + 1 + j))) w)
      - (∑' j, ρ ^ j * innov 𝔼 t (obs ag (z (t + 1 + j))) w)
      + ∑' j, (ρ ^ (j + 1) - om ^ (j + 1)) *
          innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w ∧
    innov 𝔼 t (obs arn (z (t + 1))) w =
      -∑' j, om ^ (j + 1) * innov 𝔼 t (obs arn (z (t + 2 + j))) w := by
  have hsub : ∀ {r : ℝ}, |r| ≤ 1 → Summable (fun j => r ^ (j + 1) *
      innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w) := by
    intro r hr
    refine ((var_shifted_summable 𝔼 hvar hmds hz hA hr arn t w).sub
      (var_shifted_summable 𝔼 hvar hmds hz hA hr api t w)).congr fun j => ?_
    simp only [map_sub, Pi.sub_apply]
    ring
  have hlimv := (var_weighted_sum 𝔼 hvar hmds hz hA hρ av t w).summable.tendsto_atTop_zero
  have hlimq := (var_weighted_sum 𝔼 hvar hmds hz hA hom aq t w).summable.tendsto_atTop_zero
  have h := identity_4_14 𝔼 (v := fun t => obs av (z t)) (s := fun t => obs as (z t))
    (g := fun t => obs ag (z t)) (rn := fun t => obs arn (z t)) (pi := fun t => obs api (z t))
    (q := fun t => obs aq (z t)) hflow hbond t (obs_adapted 𝔼 hz av t) (obs_adapted 𝔼 hz aq t) w
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ as t w).summable.hasSum
    (var_weighted_sum 𝔼 hvar hmds hz hA hρ ag t w).summable.hasSum
    (hsub hρ).hasSum (hsub hom).hasSum
    (var_shifted_summable 𝔼 hvar hmds hz hA hom api t w).hasSum hlimv hlimq
  constructor
  · rw [h.1.tsum_eq, h.2.tsum_eq]
  · exact identity_4_16 𝔼 (q := fun t => obs aq (z t)) (rn := fun t => obs arn (z t)) hbond t
      (obs_adapted 𝔼 hz aq t) w (var_shifted_summable 𝔼 hvar hmds hz hA hom arn t w).hasSum hlimq

/-- Cochrane (2023), eq. (4.14), p. 103, exactly as used in the book (`ρ = 1`): in a stable VAR
whose observables satisfy the flow identity
`v_{t+1} = v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} − s̃_{t+1}` and the bond-return identity, every
series converges and
`∑_{j≥0} ωʲΔπ_{t+1+j} = −∑_{j≥0}Δs̃_{t+1+j} − ∑_{j≥0}Δg_{t+1+j} + ∑_{j≥1}(1 − ωʲ)Δr_{t+1+j}`
(`|ω| ≤ 1`). -/
theorem identity_4_14_rho_one_of_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) (hA : PowDecay A) {om : ℝ} (hom : |om| ≤ 1)
    {av as ag arn api aq : κ → ℝ}
    (hflow : ∀ t, obs av (z (t + 1)) = obs av (z t) + obs arn (z (t + 1)) -
      obs api (z (t + 1)) - obs ag (z (t + 1)) - obs as (z (t + 1)))
    (hbond : ∀ t, obs arn (z (t + 1)) = om • obs aq (z (t + 1)) - obs aq (z t)) (t : ℕ)
    (w : Ω) :
    ∑' j, om ^ j * innov 𝔼 t (obs api (z (t + 1 + j))) w =
      -(∑' j, innov 𝔼 t (obs as (z (t + 1 + j))) w)
      - (∑' j, innov 𝔼 t (obs ag (z (t + 1 + j))) w)
      + ∑' j, (1 - om ^ (j + 1)) *
          innov 𝔼 t (obs arn (z (t + 2 + j)) - obs api (z (t + 2 + j))) w := by
  have h := (identity_4_14_of_var 𝔼 hvar hmds hz hA (ρ := 1) (by simp) hom
    (fun t => by rw [one_smul]; exact hflow t) hbond t w).1
  simpa only [one_pow, one_mul] using h

/-! ### Filling in shocks: regressions and the Cholesky orthogonalisation (4.17)–(4.18) -/

namespace Regression

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

omit [DecidableEq m] in
/-- Cochrane (2023), eq. (4.17), p. 104 (tool): the shock covariance `Σ = LLᵀ` of a block-lower
triangular factor `L = [L₁₁ 0; L₂₁ L₂₂]` (the Cholesky factor with the first block ordered
first) has blocks `L₁₁L₁₁ᵀ`, `L₁₁L₂₁ᵀ`, `L₂₁L₁₁ᵀ`, `L₂₁L₂₁ᵀ + L₂₂L₂₂ᵀ`. -/
theorem cholesky_blocks (L11 : Matrix m m ℝ) (L21 : Matrix n m ℝ) (L22 : Matrix n n ℝ) :
    Matrix.fromBlocks L11 0 L21 L22 * (Matrix.fromBlocks L11 0 L21 L22)ᵀ =
      Matrix.fromBlocks (L11 * L11ᵀ) (L11 * L21ᵀ) (L21 * L11ᵀ) (L21 * L21ᵀ + L22 * L22ᵀ) := by
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp

/-- Cochrane (2023), eq. (4.17), p. 104: filling in the other shocks by regressions on the
first-block shocks (`ε_z = b_{z,π}ε_π + u_z`, the coefficient matrix `B` defined by the
orthogonality condition `Cov(ε₂ − Bε₁, ε₁) = Σ₂₁ − BΣ₁₁ = 0`) gives exactly `B = L₂₁L₁₁⁻¹` for the
Cholesky factor `Σ = LLᵀ` with the first block ordered first. The regression is unique. -/
theorem regression_eq_cholesky {L11 : Matrix m m ℝ} {L21 : Matrix n m ℝ} {L22 : Matrix n n ℝ}
    (hL : IsUnit L11.det) {Sig : Matrix (m ⊕ n) (m ⊕ n) ℝ}
    (hSig : Sig = Matrix.fromBlocks L11 0 L21 L22 * (Matrix.fromBlocks L11 0 L21 L22)ᵀ)
    (B : Matrix n m ℝ) :
    B * Sig.toBlocks₁₁ = Sig.toBlocks₂₁ ↔ B = L21 * L11⁻¹ := by
  rw [hSig, cholesky_blocks, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁]
  have hT : IsUnit L11ᵀ.det := by rwa [Matrix.det_transpose]
  constructor
  · intro h
    have h1 : B * L11 = L21 := by
      have := congrArg (· * L11ᵀ⁻¹) h
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT, Matrix.mul_one] at this
      exact this
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hL, Matrix.mul_one]
  · rintro rfl
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc L11⁻¹, Matrix.nonsing_inv_mul _ hL, Matrix.one_mul]

/-- Cochrane (2023), eq. (4.17), p. 104 ("this procedure is equivalent to the usual
orthogonalization of the shock covariance matrix"): the filled-in shock vector `(x, Bx)` is the
response to orthogonalised shocks `u` (`ε = Lu`, `Var u = I`) loading only on the first block,
`u = (L₁₁⁻¹x, 0)`. -/
theorem filled_shock_eq_orthogonalized {L11 : Matrix m m ℝ} (hL : IsUnit L11.det)
    (L21 : Matrix n m ℝ) (L22 : Matrix n n ℝ) (x : m → ℝ) :
    Sum.elim x ((L21 * L11⁻¹) *ᵥ x) =
      Matrix.fromBlocks L11 0 L21 L22 *ᵥ Sum.elim (L11⁻¹ *ᵥ x) 0 := by
  rw [Matrix.fromBlocks_mulVec]
  simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hL]

omit [DecidableEq m] in
/-- Cochrane (2023), eq. (4.17), p. 104 (single shock, inflation ordered first): the regression
coefficient `b_{z,π} = Σ_{zπ}/Σ_{ππ}` equals the Cholesky first column normalised by its first
entry, `L_{zπ}/L_{ππ}`, so the filled shock `ε_1 = (1, b_{z,π}, …)` is the first orthogonalised
shock scaled to `ε_π = 1`. -/
theorem regression_coeff_single {ℓ : ℝ} (hℓ : ℓ ≠ 0) (L21 : Matrix n Unit ℝ)
    (L22 : Matrix n n ℝ) {Sig : Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ}
    (hSig : Sig = Matrix.fromBlocks (Matrix.of fun _ _ => ℓ) 0 L21 L22 *
      (Matrix.fromBlocks (Matrix.of fun _ _ => ℓ) 0 L21 L22)ᵀ) (z : n) :
    Sig (Sum.inr z) (Sum.inl ()) / Sig (Sum.inl ()) (Sum.inl ()) = L21 z () / ℓ := by
  rw [hSig, cholesky_blocks]
  simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₁₁, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton]
  field_simp

omit [DecidableEq κ] in
/-- Cochrane (2023), eq. (4.18), p. 112: the regression of the shocks on a linear combination
`f'ε` (e.g. `f'ε = (a_s + a_g)'(I − A)⁻¹ε`, the surplus shock), with coefficients defined by
`Cov(ε − b f'ε, f'ε) = Σf − b (f'Σf) = 0`, has the unique solution `b = Σf/(f'Σf)`. -/
theorem functional_regression {Sig : Matrix κ κ ℝ} {f : κ → ℝ} (hf : f ⬝ᵥ (Sig *ᵥ f) ≠ 0)
    (b : κ → ℝ) :
    Sig *ᵥ f = (f ⬝ᵥ (Sig *ᵥ f)) • b ↔ b = (f ⬝ᵥ (Sig *ᵥ f))⁻¹ • (Sig *ᵥ f) := by
  constructor
  · intro h
    calc b = (f ⬝ᵥ (Sig *ᵥ f))⁻¹ • ((f ⬝ᵥ (Sig *ᵥ f)) • b) := by
          rw [smul_smul, inv_mul_cancel₀ hf, one_smul]
      _ = _ := by rw [← h]
  · rintro rfl
    rw [smul_smul, mul_inv_cancel₀ hf, one_smul]

omit [DecidableEq κ] in
/-- Cochrane (2023), eq. (4.18), p. 112: the regression coefficients are normalised so that the
filled-in shock moves the functional by one, `f'b = 1`. -/
theorem functional_regression_normalised {Sig : Matrix κ κ ℝ} {f : κ → ℝ}
    (hf : f ⬝ᵥ (Sig *ᵥ f) ≠ 0) : f ⬝ᵥ ((f ⬝ᵥ (Sig *ᵥ f))⁻¹ • (Sig *ᵥ f)) = 1 := by
  rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hf]

omit [DecidableEq κ] in
/-- Cochrane (2023), eq. (4.18), p. 112: for a positive definite shock covariance and a nonzero
functional, `f'Σf > 0`, so the regression of (4.18) is well defined. -/
theorem quadForm_pos {Sig : Matrix κ κ ℝ} (hSig : Sig.PosDef) {f : κ → ℝ} (hf : f ≠ 0) :
    0 < f ⬝ᵥ (Sig *ᵥ f) := by
  simpa using hSig.dotProduct_mulVec_pos hf

/-- Cochrane (2023), eq. (4.18) and p. 112 ("I start the surplus-shock response function at
`ε_1 = −[b_{rⁿ} b_g b_π …]'`"): in a stable VAR, if the date-`t+1` shock is the negative of the
regression coefficients on `f'ε` with `f = ((I − A)⁻¹)'c` (`c = a_s + a_g`), the response of the
sum of current and future surpluses (and growth) is exactly `−1`. -/
theorem surplus_shock_sum (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) (Sig : Matrix κ κ ℝ) (c : κ → ℝ) (t : ℕ) (w : Ω)
    (hf : (c ᵥ* (1 - A)⁻¹) ⬝ᵥ (Sig *ᵥ (c ᵥ* (1 - A)⁻¹)) ≠ 0)
    (hshock : vecAt (ε (t + 1)) w = -(((c ᵥ* (1 - A)⁻¹) ⬝ᵥ (Sig *ᵥ (c ᵥ* (1 - A)⁻¹)))⁻¹ •
      (Sig *ᵥ (c ᵥ* (1 - A)⁻¹)))) :
    HasSum (fun j => innov 𝔼 t (obs c (z (t + 1 + j))) w) (-1) := by
  have h := var_sum_responses 𝔼 hvar hmds hz hA c t w
  rwa [Matrix.dotProduct_mulVec, hshock, dotProduct_neg,
    functional_regression_normalised hf] at h

end Regression

/-! ### The present-value relation in a VAR is an identity (A2 (2.24)–(2.26)) -/

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: observables are linear in the weights. -/
theorem obs_add (c d : κ → ℝ) (y : κ → Ω → ℝ) : obs (c + d) y = obs c y + obs d y := by
  simp [obs, add_smul, Finset.sum_add_distrib]

omit [DecidableEq κ] in
/-- Cochrane (2023), p. 112: observables are linear in the weights. -/
theorem obs_sub (c d : κ → ℝ) (y : κ → Ω → ℝ) : obs (c - d) y = obs c y - obs d y := by
  simp [obs, sub_smul, Finset.sum_sub_distrib]

/-- Cochrane (2023), Online Appendix eq. (2.25), p. 605: if the flow identity (2.24)
`ρv_{t+1} = v_t + rⁿ_{t+1} − π_{t+1} − g_{t+1} − s_{t+1}` holds identically in the VAR (for every
state `z` and shock `e`, with `v = a_v'z` etc.), then the VAR coefficients obey
`a_v'(I − ρA) = (a_s + a_g − a_{rⁿ} + a_π)'A` — and also `ρa_v = a_{rⁿ} − a_π − a_g − a_s` on the
shocks. "These are not restrictions we need to impose." -/
theorem flow_restriction_of_identity {A : Matrix κ κ ℝ} {ρ : ℝ} {av as ag arn api : κ → ℝ}
    (h : ∀ zz e : κ → ℝ, ρ * (av ⬝ᵥ (A *ᵥ zz + e)) =
      av ⬝ᵥ zz + (arn - api - ag - as) ⬝ᵥ (A *ᵥ zz + e)) :
    av ᵥ* (1 - ρ • A) = (as + ag - arn + api) ᵥ* A ∧ ρ • av = arn - api - ag - as := by
  constructor
  · funext i
    have := h (Pi.single i 1) 0
    simp only [add_zero, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    simp only [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_smul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.add_vecMul, Matrix.sub_vecMul, Pi.add_apply]
    simp only [Matrix.sub_vecMul, Pi.sub_apply] at this
    linarith
  · funext i
    have := h 0 (Pi.single i 1)
    simp only [Matrix.mulVec_zero, zero_add, dotProduct_single, mul_one, dotProduct_zero] at this
    simp only [Pi.smul_apply, smul_eq_mul, this]

/-- Cochrane (2023), Online Appendix p. 605 (tool): `I − ρA` commutes with `A`. -/
theorem one_sub_smul_mul_comm (A : Matrix κ κ ℝ) (ρ : ℝ) :
    (1 - ρ • A) * A = A * (1 - ρ • A) := by
  simp [Matrix.sub_mul, Matrix.mul_sub]

/-- Cochrane (2023), Online Appendix p. 605 (tool): `(I − ρA)⁻¹` commutes with `A`. -/
theorem inv_one_sub_mul_comm {A : Matrix κ κ ℝ} {ρ : ℝ} (hM : IsUnit (1 - ρ • A).det) :
    (1 - ρ • A)⁻¹ * A = A * (1 - ρ • A)⁻¹ := by
  have hc := one_sub_smul_mul_comm A ρ
  calc (1 - ρ • A)⁻¹ * A = (1 - ρ • A)⁻¹ * (A * (1 - ρ • A)) * (1 - ρ • A)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.mul_one]
    _ = (1 - ρ • A)⁻¹ * ((1 - ρ • A) * A) * (1 - ρ • A)⁻¹ := by rw [hc]
    _ = A * (1 - ρ • A)⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]

/-- Cochrane (2023), Online Appendix eqs. (2.25)–(2.26), p. 605: the coefficient restriction
from the flow identity, `a_v'(I − ρA) = d'A`, and the present-value restriction
`a_v' = d'(I − ρA)⁻¹A` (`d = a_s + a_g − a_{rⁿ} + a_π`) are the same restriction. Only the
invertibility of `I − ρA` is needed (the book says "so long as the eigenvalues of `A` are less
than one", survey E18; convergence of the present value is a separate matter, `var_pv_identity`). -/
theorem flow_restriction_iff_pv {A : Matrix κ κ ℝ} {ρ : ℝ} (hM : IsUnit (1 - ρ • A).det)
    (av d : κ → ℝ) : av ᵥ* (1 - ρ • A) = d ᵥ* A ↔ av = d ᵥ* ((1 - ρ • A)⁻¹ * A) := by
  constructor
  · intro h
    have := congrArg (· ᵥ* (1 - ρ • A)⁻¹) h
    simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hM, Matrix.vecMul_one] at this
    rw [this, inv_one_sub_mul_comm hM]
  · rintro rfl
    rw [Matrix.vecMul_vecMul, Matrix.mul_assoc, ← one_sub_smul_mul_comm, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hM, Matrix.one_mul]

/-- Cochrane (2023), Online Appendix p. 605 ("we derived (2.26) by iterating forward (2.24)"):
if `ρv_{t+1} = v_t − y_{t+1}` at every date, `v_t` is known at `t` and `ρᵀE_t v_{t+T} → 0`, then
`v_t = ∑_{j≥0} ρʲ E_t y_{t+1+j}` as the limit of the partial sums. -/
theorem pv_of_flow (𝔼 : ExpectationSystem Ω) {ρ : ℝ} {v y : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) = v t - y (t + 1)) (t : ℕ) (hv : 𝔼.E t (v t) = v t) (w : Ω)
    (hlim : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) w) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (y (t + 1 + j)) w) atTop
      (𝓝 (v t w)) := by
  set F : ℕ → ℝ := fun j => 𝔼.E t (v (t + j)) w with hF
  have hstep : ∀ j, F j = ρ * F (j + 1) + 𝔼.E t (y (t + 1 + j)) w := by
    intro j
    have h := congrArg (fun x => 𝔼.E t x w) (hflow (t + j))
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
    simp only [hF, show t + (j + 1) = t + j + 1 by omega, show t + 1 + j = t + j + 1 by omega]
    linarith
  have hiter : ∀ T, F 0 = ρ ^ T * F T +
      ∑ j ∈ Finset.range T, ρ ^ j * 𝔼.E t (y (t + 1 + j)) w := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [ih, Finset.sum_range_succ, hstep T]
      ring
  have hF0 : F 0 = v t w := by simp [hF, hv]
  have hlim' : Tendsto (fun T => F 0 - ρ ^ T * F T) atTop (𝓝 (F 0 - 0)) :=
    tendsto_const_nhds.sub hlim
  rw [sub_zero, hF0] at hlim'
  refine hlim'.congr fun T => ?_
  rw [← hF0, hiter T]
  ring

/-- Cochrane (2023), Online Appendix eqs. (2.24)–(2.26), p. 605 (the tautology: "with `v_t` in the
VAR … the constructed present value of surpluses comes out to be each day's value of debt,
exactly, and by construction"): in a stable VAR (`PowDecay A`, `|ρ| ≤ 1`) whose observables obey
the flow identity (2.24), the VAR present value converges and equals the value of debt,
`v_t = ∑_{j≥0} ρʲ E_t(s + g − rⁿ + π)_{t+1+j} = d'(I − ρA)⁻¹A z_t`, `d = a_s + a_g − a_{rⁿ} + a_π`.
(2.26) "reduces to `v_t = v_t`". -/
theorem var_pv_identity (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1) {av as ag arn api : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs arn (z (t + 1)) -
      obs api (z (t + 1)) - obs ag (z (t + 1)) - obs as (z (t + 1))) (t : ℕ) (w : Ω) :
    HasSum (fun j => ρ ^ j * 𝔼.E t (obs (as + ag - arn + api) (z (t + 1 + j))) w)
      (obs av (z t) w) ∧
    obs av (z t) w = (as + ag - arn + api) ⬝ᵥ (((1 - ρ • A)⁻¹ * A) *ᵥ vecAt (z t) w) := by
  set d := as + ag - arn + api with hd
  have hflow' : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) - obs d (z (t + 1)) := by
    intro t
    rw [hflow t, hd, obs_add, obs_sub, obs_add]
    abel
  have hterm : ∀ j, ρ ^ j * 𝔼.E t (obs d (z (t + 1 + j))) w =
      d ⬝ᵥ (((ρ • A) ^ j) *ᵥ (A *ᵥ vecAt (z t) w)) := by
    intro j
    rw [show t + 1 + j = t + (j + 1) by omega, var_forecast_obs 𝔼 hvar hmds hz, pow_succ,
      ← Matrix.mulVec_mulVec, weight_bilin]
  have hsum : HasSum (fun j => ρ ^ j * 𝔼.E t (obs d (z (t + 1 + j))) w)
      (d ⬝ᵥ (((1 - ρ • A)⁻¹ * A) *ᵥ vecAt (z t) w)) := by
    simp only [hterm, ← Matrix.mulVec_mulVec]
    exact neumann_bilin_hasSum (powDecay_smul hA hρ) d _
  have hlim : Tendsto (fun T => ρ ^ T * 𝔼.E t (obs av (z (t + T))) w) atTop (𝓝 0) := by
    have h := (neumann_bilin_hasSum (powDecay_smul hA hρ) av (vecAt (z t) w)).summable
    refine h.tendsto_atTop_zero.congr fun T => ?_
    rw [var_forecast_obs 𝔼 hvar hmds hz, weight_bilin]
  have hpv := pv_of_flow 𝔼 (v := fun t => obs av (z t)) (y := fun t => obs d (z t)) hflow' t
    (obs_adapted 𝔼 hz av t) w hlim
  have heq := tendsto_nhds_unique hpv hsum.tendsto_sum_nat
  exact ⟨heq ▸ hsum, heq⟩

end Cochrane.DebtDeficitsInflation.VARIdentities
