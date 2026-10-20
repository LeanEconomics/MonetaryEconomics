/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.Granger
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The present-value relation is an identity; the ex-post discount factor

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix Chapter 2, §2.2
(eqs. (2.24)–(2.26), pp. 604–605) and §2.3 (pp. 606–607); Chapter 22, §22.2.4, p. 499 (the
discount-factor existence theorem applied to government debt) and §22.5, p. 505 ("as
observational equivalence and existence of discount factor theorems should indicate"). (§22.4,
pp. 503–505, "Plausibility and other evidence", is verbal and has no formal content.)

The VAR material (`PowDecay`, Neumann series, `flow_restriction_iff_pv`, `var_pv_identity`, …)
is restated from the Cochrane `DebtDeficitsInflation` project (`VARIdentities`), adapted to this
project's core. The innovation operator `innov`, the ex-post present value `pvExPost`, and the
flow-iteration lemmas `flow_telescope` and `pv_of_flow` are shared with chain A and live in
`ExpectationTools`.

## Main results

* (2.24)–(2.26), the VAR with `v`: `flow_restriction_of_identity` (the flow identity forces the
  coefficient restriction (2.25) `a_v'(I − ρA) = (a_s + a_g − a_{rⁿ} + a_π)'A`),
  `flow_restriction_iff_pv` ((2.25) ⇔ the present-value restriction, needing only `I − ρA`
  invertible), `var_pv_identity` (in a stable VAR satisfying the flow identity, the VAR present
  value converges and equals `v_t` — "(2.26) reduces to `v_t = v_t`").
* `flow_forces_singular`: a VAR satisfying the flow identity pathwise has singular shocks,
  `c'ε_{t+1} = 0` with `c = ρa_v − (a_{rⁿ} − a_π − a_g − a_s)`, and `a_v' = c'A`;
  `nondeg_forces_trivial`: with nondegenerate shocks this forces `v ≡ 0` (implicit in the book).
* §2.3, the linearised identity: `expost_pv_finite`
  `v_t = ∑_{j<T} ρ^j (s_{t+1+j} − r_{t+1+j}) + ρ^T v_{t+T}`, `expost_pv` (its limit, an ex-post
  identity for bounded paths); `pv_identity_exante`; `as_eq_ar_innov`:
  `ΔE_{t+1} ∑ ρ^j s_{t+1+j} = ΔE_{t+1} ∑ ρ^j r_{t+1+j}` in every model obeying the flow identity
  with bounded variables — "`0 = a_s(ρ) − a_r(ρ)` … is an identity"; `const_return_as_zero`: with
  a constant discount rate this becomes the testable `a(ρ) = 0` restriction (a restriction on the
  discount-rate model).
* `genVAR` (`a(ρ)` of an observable of a VAR), `genVAR_hasSum` (`a(ρ) = ∑ ρ^j a_j`),
  `innov_pv_var` (`ΔE_{t+1} ∑ ρ^j (a'z)_{t+1+j} = a(ρ)'ε_{t+1}`), `as_eq_ar_var`
  (`a_s(ρ) = a_r(ρ)` for nondegenerate shocks).
* Ex-post discount factor (p. 499): with one-period nominal debt, the flow
  `B_{t−1} = P_t s_t + Q_t B_t` and `Λ_{t+1}/Λ_t := Q_t P_{t+1}/P_t`: `sdf_pos` (positive when
  bond prices and the price level are positive), `sdf_prices_bond` (it prices the bond exactly),
  `sdf_valuation_finite`, `sdf_valuation_tendsto` and `sdf_valuation_hasSum`
  (`B_{t−1}/P_t = ∑_j (Λ_{t+j}/Λ_t) s_{t+j}` under the transversality condition), the converse
  `tvc_of_sdf_valuation`, and `sdf_valuation_E`
  (`B_{t−1}/P_t = E_t ∑_j (Λ_{t+j}/Λ_t) s_{t+j}` for any `ExpectationSystem`).
-/

namespace Cochrane.ObservationalEquivalence.PresentValueIdentity

open Filter Topology Finset
open scoped Matrix
open Cochrane.ObservationalEquivalence.Granger (IsVAR ShockMDS var_forecast var_innov)
open Cochrane.ObservationalEquivalence.ExpectationTools (innov innov_apply innov_of_known pvExPost
  summable_pow_mul_of_bounded tendsto_pow_mul_of_bounded flow_telescope pv_of_flow)

variable {Ω κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Observables and stable VARs (restated from the `DebtDeficitsInflation` project) -/

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
theorem tendsto_pow_entry_of_powDecay {A : Matrix κ κ ℝ} (hA : PowDecay A) (i j : κ) :
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
than one", Ch. 4–5 survey E18; convergence of the present value is a separate matter,
`var_pv_identity`). -/
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


omit [DecidableEq κ] in
/-- Cochrane (2023), Online Appendix p. 605: observables are homogeneous in the weights. -/
theorem obs_smul (r : ℝ) (c : κ → ℝ) (y : κ → Ω → ℝ) : obs (r • c) y = r • obs c y := by
  simp [obs, Finset.smul_sum, smul_smul]

omit [DecidableEq κ] in
/-- Cochrane (2023), Online Appendix p. 605: in the VAR, `c'z_{t+1} = (c'A) z_t + c'ε_{t+1}`. -/
theorem obs_var_succ {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε)
    (c : κ → ℝ) (t : ℕ) : obs c (z (t + 1)) = obs (c ᵥ* A) (z t) + obs c (ε (t + 1)) := by
  simp only [obs, hvar t, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    Matrix.vecMul, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun x y => (c x * A x y) • z t y)]

/-! ### The exact flow identity forces singular shocks -/

omit [DecidableEq κ] in
/-- Cochrane (2023), Online Appendix eqs. (2.24)–(2.25), p. 605: if the flow identity
`ρv_{t+1} = v_t + d'z_{t+1}` (`d = a_{rⁿ} − a_π − a_g − a_s`) holds pathwise in a VAR with
`v = a_v'z`, then the shocks are singular, `c'ε_{t+1} = 0` with `c = ρa_v − d`, and the value of
debt is `v_t = (c'A) z_t` (the restriction (2.25)). -/
theorem flow_forces_singular (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) {ρ : ℝ} {av d : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs d (z (t + 1))) (t : ℕ) :
    obs (ρ • av - d) (ε (t + 1)) = 0 ∧ obs av (z t) = obs ((ρ • av - d) ᵥ* A) (z t) := by
  set c := ρ • av - d with hc
  have h1 : obs c (z (t + 1)) = obs av (z t) := by
    rw [hc, obs_sub, obs_smul, hflow t]; abel
  rw [obs_var_succ hvar] at h1
  have hE : 𝔼.E t (obs c (ε (t + 1))) = 0 := by
    rw [E_obs]; simp [obs, hmds t]
  have h2 : obs av (z t) = obs (c ᵥ* A) (z t) := by
    have := congrArg (𝔼.E t) h1
    rw [map_add, hE, add_zero, obs_adapted 𝔼 hz, obs_adapted 𝔼 hz] at this
    exact this.symm
  refine ⟨?_, h2⟩
  rw [← h2] at h1
  exact add_eq_left.mp (h2 ▸ h1)

/-- Cochrane (2023), Online Appendix p. 605 (implicit): the shocks at date `t + 1` are
nondegenerate — no nonzero combination of them vanishes identically. -/
def ShockNondeg (ε : ℕ → κ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ c : κ → ℝ, obs c (ε (t + 1)) = 0 → c = 0

omit [DecidableEq κ] in
/-- Cochrane (2023), Online Appendix p. 605 (implicit): if the flow identity holds exactly in a
VAR with nondegenerate shocks at some date, then `ρa_v = a_{rⁿ} − a_π − a_g − a_s` and the value
of debt is identically zero — an exact identity among VAR variables requires a singular shock
covariance. -/
theorem nondeg_forces_trivial (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ}
    {z ε : ℕ → κ → Ω → ℝ} (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε)
    (hz : ∀ t i, 𝔼.E t (z t i) = z t i) {ρ : ℝ} {av d : κ → ℝ}
    (hflow : ∀ t, ρ • obs av (z (t + 1)) = obs av (z t) + obs d (z (t + 1))) {t0 : ℕ}
    (hnd : ShockNondeg ε t0) : ρ • av = d ∧ ∀ t, obs av (z t) = 0 := by
  have hc : ρ • av - d = 0 := hnd _ (flow_forces_singular 𝔼 hvar hmds hz hflow t0).1
  refine ⟨sub_eq_zero.mp hc, fun t => ?_⟩
  rw [(flow_forces_singular 𝔼 hvar hmds hz hflow t).2, hc, Matrix.zero_vecMul]
  simp [obs]

/-! ### §2.3: the linearised present-value identity -/

/-- Cochrane (2023), Online Appendix §2.3, p. 606: iterating the flow identity
`ρv_{t+1} = v_t + r_{t+1} − s_{t+1}` (`r` the ex-post real return) gives the identity
`v_t = ∑_{j<T} ρ^j (s_{t+1+j} − r_{t+1+j}) + ρ^T v_{t+T}`, path by path. -/
theorem expost_pv_finite {ρ : ℝ} {v r s : ℕ → ℝ}
    (hflow : ∀ t, ρ * v (t + 1) = v t + r (t + 1) - s (t + 1)) (t T : ℕ) :
    v t = ∑ j ∈ range T, ρ ^ j * (s (t + 1 + j) - r (t + 1 + j)) + ρ ^ T * v (t + T) := by
  have h := flow_telescope (ρ := ρ) (v := v) (y := fun k => s (k + 1) - r (k + 1))
    (fun k => by rw [smul_eq_mul, hflow k]; ring) t T
  simp only [smul_eq_mul] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show t + j + 1 = t + 1 + j by omega]

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("Imposing convergence of the last term"):
for bounded paths and `|ρ| < 1` the linearised identity holds as a genuine infinite sum,
`v_t = ∑_{j≥0} ρ^j (s_{t+1+j} − r_{t+1+j})` — an ex-post identity. -/
theorem expost_pv {ρ M Kr Ks : ℝ} (hρ : |ρ| < 1) {v r s : ℕ → ℝ} (hv : ∀ t, |v t| ≤ M)
    (hr : ∀ t, |r t| ≤ Kr) (hs : ∀ t, |s t| ≤ Ks)
    (hflow : ∀ t, ρ * v (t + 1) = v t + r (t + 1) - s (t + 1)) (t : ℕ) :
    HasSum (fun j => ρ ^ j * (s (t + 1 + j) - r (t + 1 + j))) (v t) := by
  have hsum : Summable (fun j => ρ ^ j * (s (t + 1 + j) - r (t + 1 + j))) :=
    summable_pow_mul_of_bounded hρ (x := fun j => s (t + 1 + j) - r (t + 1 + j))
      (K := Ks + Kr) fun j => (abs_sub _ _).trans (add_le_add (hs _) (hr _))
  refine (hsum.hasSum_iff_tendsto_nat).mpr ?_
  have hlim : Tendsto (fun T => ρ ^ T * v (t + T)) atTop (𝓝 0) :=
    tendsto_pow_mul_of_bounded hρ (x := fun T => v (t + T)) fun T => hv (t + T)
  have h2 : Tendsto (fun T => v t - ρ ^ T * v (t + T)) atTop (𝓝 (v t - 0)) :=
    tendsto_const_nhds.sub hlim
  rw [sub_zero] at h2
  refine h2.congr fun T => ?_
  rw [expost_pv_finite hflow t T]
  ring

/-- Cochrane (2023), Online Appendix §2.3, p. 606: under the hypotheses of `expost_pv`, the
present values of surpluses and of returns converge separately and
`v_t = ∑ ρ^j s_{t+1+j} − ∑ ρ^j r_{t+1+j}`. -/
theorem expost_pv_split {ρ M Kr Ks : ℝ} (hρ : |ρ| < 1) {v r s : ℕ → ℝ} (hv : ∀ t, |v t| ≤ M)
    (hr : ∀ t, |r t| ≤ Kr) (hs : ∀ t, |s t| ≤ Ks)
    (hflow : ∀ t, ρ * v (t + 1) = v t + r (t + 1) - s (t + 1)) (t : ℕ) :
    v t = ∑' j, ρ ^ j * s (t + 1 + j) - ∑' j, ρ ^ j * r (t + 1 + j) := by
  have hb : ∀ (x : ℕ → ℝ) (K : ℝ), (∀ t, |x t| ≤ K) →
      Summable (fun j => ρ ^ j * x (t + 1 + j)) := fun x K hx =>
    summable_pow_mul_of_bounded hρ (x := fun j => x (t + 1 + j)) fun j => hx _
  rw [← Summable.tsum_sub (hb s Ks hs) (hb r Kr hr), (expost_pv hρ hv hr hs hflow t).tsum_eq.symm]
  exact tsum_congr fun j => by ring

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("It always holds ex-post, so it always holds
ex-ante"): for bounded processes obeying the flow identity with `v` known at `t`,
`v_t = E_t ∑ ρ^j s_{t+1+j} − E_t ∑ ρ^j r_{t+1+j}`. -/
theorem pv_identity_exante (𝔼 : ExpectationSystem Ω) {ρ M Kr Ks : ℝ} (hρ : |ρ| < 1)
    {v r s : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ M) (hr : ∀ t ω, |r t ω| ≤ Kr)
    (hs : ∀ t ω, |s t ω| ≤ Ks) (hflow : ∀ t, ρ • v (t + 1) = v t + r (t + 1) - s (t + 1))
    (hva : 𝔼.Adapted v) (t : ℕ) :
    v t = 𝔼.E t (pvExPost ρ s t) - 𝔼.E t (pvExPost ρ r t) := by
  have hpath : v t = pvExPost ρ s t - pvExPost ρ r t := by
    funext ω
    refine expost_pv_split hρ (v := fun k => v k ω) (r := fun k => r k ω)
      (s := fun k => s k ω) (fun k => hv k ω) (fun k => hr k ω) (fun k => hs k ω)
      (fun k => ?_) t
    have := congrFun (hflow k) ω
    simpa using this
  rw [← map_sub, ← hpath, hva t]

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("taking `ΔE_{t+1}` of both sides, we obtain
`0 = a_s(ρ) − a_r(ρ)` … this relation derives from an identity, so it too is an identity"): in
every model in which bounded processes obey the flow identity and `v_t` is known at `t`, the
revision of the present value of surpluses equals the revision of the present value of
returns. -/
theorem as_eq_ar_innov (𝔼 : ExpectationSystem Ω) {ρ M Kr Ks : ℝ} (hρ : |ρ| < 1)
    {v r s : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ M) (hr : ∀ t ω, |r t ω| ≤ Kr)
    (hs : ∀ t ω, |s t ω| ≤ Ks) (hflow : ∀ t, ρ • v (t + 1) = v t + r (t + 1) - s (t + 1))
    (hva : 𝔼.Adapted v) (t : ℕ) :
    innov 𝔼 t (pvExPost ρ s t) = innov 𝔼 t (pvExPost ρ r t) := by
  have hpath : v t = pvExPost ρ s t - pvExPost ρ r t := by
    funext ω
    refine expost_pv_split hρ (v := fun k => v k ω) (r := fun k => r k ω)
      (s := fun k => s k ω) (fun k => hv k ω) (fun k => hr k ω) (fun k => hs k ω)
      (fun k => ?_) t
    have := congrFun (hflow k) ω
    simpa using this
  have h0 : innov 𝔼 t (v t) = 0 := by
    have h1 : 𝔼.E (t + 1) (𝔼.E t (v t)) = 𝔼.E t (v t) := 𝔼.known (Nat.le_succ t) _
    rw [hva t] at h1
    rw [innov_apply, h1, hva t, sub_self]
  rw [hpath, map_sub] at h0
  exact sub_eq_zero.mp h0

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("the constant discount factor model is just
`a_r(ρ) = 0`"): with a constant ex-post return, the revision of the present value of surpluses
is zero — the Hansen–Roberds–Sargent restriction `a(ρ) = 0`, testable only because it restricts
the discount rate. -/
theorem const_return_as_zero (𝔼 : ExpectationSystem Ω) {ρ M Ks c : ℝ} (hρ : |ρ| < 1)
    {v s : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ M) (hs : ∀ t ω, |s t ω| ≤ Ks)
    (hflow : ∀ t, ρ • v (t + 1) = v t + (fun _ => c) - s (t + 1)) (hva : 𝔼.Adapted v)
    (t : ℕ) : innov 𝔼 t (pvExPost ρ s t) = 0 := by
  rw [as_eq_ar_innov 𝔼 hρ (r := fun _ _ => c) hv (fun _ _ => le_refl |c|) hs hflow hva t,
    innov_apply]
  unfold pvExPost
  rw [𝔼.const, 𝔼.const, sub_self]

/-! ### `a_s(ρ) = a_r(ρ)` in a VAR -/

/-- Cochrane (2023), Online Appendix §2.3, p. 606: for an observable `a'z` of a VAR the
moving-average coefficients are `a_j = (A^j)'a` and `a(ρ) = ∑ ρ^j a_j = ((I − ρA)⁻¹)'a`. -/
noncomputable def genVAR (A : Matrix κ κ ℝ) (ρ : ℝ) (a : κ → ℝ) : κ → ℝ := a ᵥ* (1 - ρ • A)⁻¹

/-- Cochrane (2023), Online Appendix §2.3, p. 606: `a(ρ)'e = ∑_j ρ^j a_j'e` for a stable VAR. -/
theorem genVAR_hasSum {A : Matrix κ κ ℝ} (hA : PowDecay A) {ρ : ℝ} (hρ : |ρ| ≤ 1)
    (a e : κ → ℝ) :
    HasSum (fun j => ρ ^ j * ((a ᵥ* A ^ j) ⬝ᵥ e)) (genVAR A ρ a ⬝ᵥ e) := by
  simp only [genVAR, ← Matrix.dotProduct_mulVec, weight_bilin]
  exact neumann_bilin_hasSum (powDecay_smul hA hρ) a e

/-- Cochrane (2023), Online Appendix §2.3, p. 606: in a stable VAR with bounded states, the
revision of the present value of an observable is `ΔE_{t+1} ∑ ρ^j (a'z)_{t+1+j} = a(ρ)'ε_{t+1}`
(genuine infinite sums, `|ρ| < 1`). -/
theorem innov_pv_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ρ Mz : ℝ} (hρ : |ρ| < 1) (hzb : ∀ t i ω, |z t i ω| ≤ Mz) (a : κ → ℝ)
    (t : ℕ) (w : Ω) :
    innov 𝔼 t (fun ω => ∑' j, ρ ^ j * obs a (z (t + 1 + j)) ω) w =
      genVAR A ρ a ⬝ᵥ vecAt (ε (t + 1)) w := by
  set C : ℝ := (∑ i, |a i|) * Mz with hC
  have hob : ∀ k ω, |obs a (z k) ω| ≤ C := by
    intro k ω
    rw [obs_apply, hC, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [vecAt, abs_mul]
    exact mul_le_mul_of_nonneg_left (hzb k i ω) (abs_nonneg _)
  have hbd : ∀ j ω, |ρ ^ j * obs a (z (t + 1 + j)) ω| ≤ |ρ| ^ j * C := by
    intro j ω
    rw [abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hob _ ω) (pow_nonneg (abs_nonneg _) _)
  have hE1 := 𝔼.E_tsum (abs_nonneg ρ) hρ (f := fun j ω => ρ ^ j * obs a (z (t + 1 + j)) ω)
    hbd (t + 1) w
  have hE0 := 𝔼.E_tsum (abs_nonneg ρ) hρ (f := fun j ω => ρ ^ j * obs a (z (t + 1 + j)) ω)
    hbd t w
  have hgeo : Summable (fun j : ℕ => |ρ| ^ j * C) :=
    (summable_geometric_of_lt_one (abs_nonneg ρ) hρ).mul_right C
  have hs1 : Summable (fun j => 𝔼.E (t + 1) (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) w) :=
    Summable.of_norm_bounded hgeo fun j => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hbd j) _ w
  have hs0 : Summable (fun j => 𝔼.E t (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) w) :=
    Summable.of_norm_bounded hgeo fun j => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hbd j) _ w
  rw [innov_apply, Pi.sub_apply, hE1, hE0, ← Summable.tsum_sub hs1 hs0]
  have hterm : ∀ j, 𝔼.E (t + 1) (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) w -
      𝔼.E t (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) w =
      ρ ^ j * innov 𝔼 t (obs a (z (t + 1 + j))) w := by
    intro j
    have hf : (fun ω => ρ ^ j * obs a (z (t + 1 + j)) ω) = ρ ^ j • obs a (z (t + 1 + j)) := rfl
    rw [hf, map_smul, map_smul, innov_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simp only [hterm]
  rw [(var_weighted_sum 𝔼 hvar hmds hz hA hρ.le a t w).tsum_eq, genVAR,
    ← Matrix.dotProduct_mulVec]

/-- Cochrane (2023), Online Appendix §2.3, p. 606 ("Imposing convergence of the last term …
we obtain `0 = a_s(ρ) − a_r(ρ)`"): if surpluses `s = a_s'z` and ex-post returns `r = a_r'z` are
observables of a stable bounded VAR, and a bounded adapted value of debt obeys the flow identity
`ρv_{t+1} = v_t + r_{t+1} − s_{t+1}`, then `a_s(ρ)'ε_{t+1} = a_r(ρ)'ε_{t+1}`; with nondegenerate
shocks, `a_s(ρ) = a_r(ρ)` — an identity, not a testable restriction. -/
theorem as_eq_ar_var (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (hA : PowDecay A) {ρ Mz M : ℝ} (hρ : |ρ| < 1) (hzb : ∀ t i ω, |z t i ω| ≤ Mz)
    {as ar : κ → ℝ} {v : ℕ → Ω → ℝ} (hv : ∀ t ω, |v t ω| ≤ M) (hva : 𝔼.Adapted v)
    (hflow : ∀ t, ρ • v (t + 1) = v t + obs ar (z (t + 1)) - obs as (z (t + 1))) (t : ℕ) :
    obs (genVAR A ρ as - genVAR A ρ ar) (ε (t + 1)) = 0 ∧
      (ShockNondeg ε t → genVAR A ρ as = genVAR A ρ ar) := by
  have hob : ∀ (a : κ → ℝ) (k : ℕ) (ω : Ω), |obs a (z k) ω| ≤ (∑ i, |a i|) * Mz := by
    intro a k ω
    rw [obs_apply, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [vecAt, abs_mul]
    exact mul_le_mul_of_nonneg_left (hzb k i ω) (abs_nonneg _)
  have hid := as_eq_ar_innov 𝔼 hρ (s := fun k => obs as (z k)) (r := fun k => obs ar (z k)) hv
    (hob ar) (hob as) hflow hva t
  unfold pvExPost at hid
  have hzero : obs (genVAR A ρ as - genVAR A ρ ar) (ε (t + 1)) = 0 := by
    funext w
    rw [obs_sub, Pi.sub_apply, obs_apply, obs_apply,
      ← innov_pv_var 𝔼 hvar hmds hz hA hρ hzb as t w,
      ← innov_pv_var 𝔼 hvar hmds hz hA hρ hzb ar t w, hid, sub_self, Pi.zero_apply]
  exact ⟨hzero, fun hnd => sub_eq_zero.mp (hnd _ hzero)⟩

/-! ### The ex-post discount factor (p. 499) -/

/-- Cochrane (2023), p. 499: the flow constraint with one-period nominal debt,
`B_{t−1} = P_t s_t + Q_t B_t`, written with `D t = B_{t−1}` (debt due at the start of `t`) and
`Q t` the price at `t` of a bond paying one unit of money at `t + 1`. -/
def DebtFlow (D P Q s : ℕ → ℝ) : Prop := ∀ t, D t = P t * s t + Q t * D (t + 1)

/-- Cochrane (2023), p. 499: the one-period ex-post discount factor
`Λ_{t+1}/Λ_t := Q_t P_{t+1}/P_t`. -/
noncomputable def sdfStep (P Q : ℕ → ℝ) (t : ℕ) : ℝ := Q t * P (t + 1) / P t

/-- Cochrane (2023), p. 499: the ex-post discount factor `Λ_t = ∏_{k<t} Q_k P_{k+1}/P_k`,
`Λ_0 = 1`. -/
noncomputable def sdf (P Q : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 => sdf P Q t * sdfStep P Q t

/-- Cochrane (2023), p. 499 ("Absent arbitrage, there is a discount factor"): with positive bond
prices and price levels the ex-post discount factor is strictly positive. -/
theorem sdf_pos {P Q : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t) (t : ℕ) :
    0 < sdf P Q t := by
  induction t with
  | zero => simp [sdf]
  | succ t ih => exact mul_pos ih (div_pos (mul_pos (hQ t) (hP (t + 1))) (hP t))

/-- Cochrane (2023), p. 499: the ex-post discount factor prices the one-period nominal bond
exactly, `(Λ_{t+1}/Λ_t)(1/P_{t+1}) = Q_t/P_t`. -/
theorem sdf_prices_bond {P Q : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t) (t : ℕ) :
    sdf P Q (t + 1) / sdf P Q t * (1 / P (t + 1)) = Q t / P t := by
  have h0 := (sdf_pos hP hQ t).ne'
  have h1 := (hP t).ne'
  have h2 := (hP (t + 1)).ne'
  simp only [sdf, sdfStep]
  field_simp

/-- Cochrane (2023), p. 499: in real terms the flow constraint is a one-period pricing
identity, `B_{t−1}/P_t = s_t + (Λ_{t+1}/Λ_t) B_t/P_{t+1}`. -/
theorem sdf_flow {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t : ℕ) :
    D t / P t = s t + sdf P Q (t + 1) / sdf P Q t * (D (t + 1) / P (t + 1)) := by
  have h0 := (sdf_pos hP hQ t).ne'
  have h1 := (hP t).ne'
  have h2 := (hP (t + 1)).ne'
  rw [hD t]
  simp only [sdf, sdfStep]
  field_simp

/-- Cochrane (2023), p. 499: iterating, `B_{t−1}/P_t = ∑_{j<T} (Λ_{t+j}/Λ_t) s_{t+j} +
(Λ_{t+T}/Λ_t) B_{t+T−1}/P_{t+T}`. -/
theorem sdf_valuation_finite {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t T : ℕ) :
    D t / P t = ∑ j ∈ range T, sdf P Q (t + j) / sdf P Q t * s (t + j) +
      sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T)) := by
  induction T with
  | zero =>
    have h0 := (sdf_pos hP hQ t).ne'
    simp [h0]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, sdf_flow hP hQ hD (t + T),
      show t + (T + 1) = t + T + 1 by omega]
    have h0 := (sdf_pos hP hQ t).ne'
    have h1 := (sdf_pos hP hQ (t + T)).ne'
    field_simp
    ring

/-- Cochrane (2023), p. 499: under the transversality condition
`(Λ_{t+T}/Λ_t) B_{t+T−1}/P_{t+T} → 0`, the partial sums of `∑_j (Λ_{t+j}/Λ_t) s_{t+j}` converge
to `B_{t−1}/P_t`. -/
theorem sdf_valuation_tendsto {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t : ℕ)
    (htvc : Tendsto (fun T => sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T))) atTop
      (𝓝 0)) :
    Tendsto (fun T => ∑ j ∈ range T, sdf P Q (t + j) / sdf P Q t * s (t + j)) atTop
      (𝓝 (D t / P t)) := by
  have h2 : Tendsto (fun T => D t / P t -
      sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T))) atTop (𝓝 (D t / P t - 0)) :=
    tendsto_const_nhds.sub htvc
  rw [sub_zero] at h2
  refine h2.congr fun T => ?_
  rw [sdf_valuation_finite hP hQ hD t T]
  ring

/-- Cochrane (2023), p. 499 (the discount-factor theorem applied to government debt): with
positive bond prices and price levels, the transversality condition and summability of the
discounted surpluses, `B_{t−1}/P_t = ∑_{j≥0} (Λ_{t+j}/Λ_t) s_{t+j}` for the ex-post discount
factor. -/
theorem sdf_valuation_hasSum {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t : ℕ)
    (htvc : Tendsto (fun T => sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T))) atTop
      (𝓝 0))
    (hsum : Summable (fun j => sdf P Q (t + j) / sdf P Q t * s (t + j))) :
    HasSum (fun j => sdf P Q (t + j) / sdf P Q t * s (t + j)) (D t / P t) :=
  hsum.hasSum_iff_tendsto_nat.mpr (sdf_valuation_tendsto hP hQ hD t htvc)

/-- Cochrane (2023), p. 499: conversely, if the valuation formula holds (as a genuine sum), the
transversality condition holds — so given the flow constraint, the valuation equation with the
ex-post discount factor is equivalent to the transversality condition. -/
theorem tvc_of_sdf_valuation {D P Q s : ℕ → ℝ} (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hD : DebtFlow D P Q s) (t : ℕ)
    (hval : HasSum (fun j => sdf P Q (t + j) / sdf P Q t * s (t + j)) (D t / P t)) :
    Tendsto (fun T => sdf P Q (t + T) / sdf P Q t * (D (t + T) / P (t + T))) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := D t / P t)).sub hval.tendsto_sum_nat
  rw [sub_self] at h
  refine h.congr fun T => ?_
  rw [sdf_valuation_finite hP hQ hD t T]
  ring

/-- Cochrane (2023), p. 499, displayed equation: for random processes satisfying the flow
constraint, positivity, the transversality condition and summability state by state, with
`B_{t−1}/P_t` known at `t`, `B_{t−1}/P_t = E_t ∑_{j≥0} (Λ_{t+j}/Λ_t) s_{t+j}` for any
`ExpectationSystem` — present-value "puzzles" are puzzles of the discount factor. -/
theorem sdf_valuation_E (𝔼 : ExpectationSystem Ω) {D P Q s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hQ : ∀ t ω, 0 < Q t ω)
    (hD : ∀ ω, DebtFlow (fun k => D k ω) (fun k => P k ω) (fun k => Q k ω) (fun k => s k ω))
    (t : ℕ)
    (htvc : ∀ ω, Tendsto (fun T => sdf (fun k => P k ω) (fun k => Q k ω) (t + T) /
      sdf (fun k => P k ω) (fun k => Q k ω) t * (D (t + T) ω / P (t + T) ω)) atTop (𝓝 0))
    (hsum : ∀ ω, Summable (fun j => sdf (fun k => P k ω) (fun k => Q k ω) (t + j) /
      sdf (fun k => P k ω) (fun k => Q k ω) t * s (t + j) ω))
    (hknown : 𝔼.E t (fun ω => D t ω / P t ω) = fun ω => D t ω / P t ω) :
    (fun ω => D t ω / P t ω) = 𝔼.E t (fun ω => ∑' j, sdf (fun k => P k ω) (fun k => Q k ω)
      (t + j) / sdf (fun k => P k ω) (fun k => Q k ω) t * s (t + j) ω) := by
  have hpath : (fun ω => ∑' j, sdf (fun k => P k ω) (fun k => Q k ω) (t + j) /
      sdf (fun k => P k ω) (fun k => Q k ω) t * s (t + j) ω) = fun ω => D t ω / P t ω := by
    funext ω
    exact (sdf_valuation_hasSum (fun k => hP k ω) (fun k => hQ k ω) (hD ω) t (htvc ω)
      (hsum ω)).tsum_eq
  rw [hpath, hknown]

end Cochrane.ObservationalEquivalence.PresentValueIdentity
