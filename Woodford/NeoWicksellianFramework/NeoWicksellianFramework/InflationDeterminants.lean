/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.Determinacy2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Order.IntermediateValue

/-!
# Determinants of inflation

Woodford (2003), *Interest and Prices*, Chapter 4, §2.4–2.5, pp. 276–290 (with App. C.2–C.3,
pp. 676–680, for the systems involved). All model equations hold for an arbitrary
`ExpectationSystem` (perfect foresight or genuine uncertainty); forward solutions are genuine
infinite sums; "unique" means unique among bounded adapted processes.

## Main results

* Stable `2 × 2` matrices and Prop. C.1 are those of `BlanchardKahn`
  (`summable_abs_pow_entry`, `inv2_eq_inv`, `tr2_inv`, `det2_inv`) and `SchurCohn`
  (`BothOutside`, `bothOutside_iff_schurStable_inv`).
* The forward solution: `fwdVec`, `fwdVec_solves`, `eq_fwdVec`, `ForwardSys` (E_t z_{t+1} =
  A z_t + a e_t), `forwardSys_existsUnique`, `forwardSys_eq_formula`: **(2.34) corrected**,
  `z_t = −∑ A^{−j−1} a E_t e_{t+j}`; `printed_234_not_solution`: the printed (2.34) (no minus
  sign) is not a solution. `forwardDeterminate_iff` (Blanchard–Kahn for two non-predetermined
  variables).
* The model (1.12)–(1.14): the canonical `BasicModel.IS112`, `BasicModel.NKPCurve`, the rule
  `TaylorRule` (`taylorRule_iff`: it is `Determinacy2.taylorRate`), `Determinacy2.taylorA`,
  `as_is_iff_forwardSys`, `taylor_rootsOutside_iff` (derived from the canonical
  `Determinacy2.taylorB_schurStable_iff`), `taylor_determinate_iff` (Prop. 4.3, uniqueness form);
  **(2.31)–(2.33)**: `psi`, `psiI`, `taylor_equilibrium_formula`,
  `taylor_equilibrium_existsUnique`.
* p. 284 shock equivalence: `shock_equivalence`, `natural_rate_shock_eq_policy_shock`;
  p. 287: `tracking_natural_rate`, `tracking_natural_rate_exists`.
* p. 288 (large responses): `psi_bound`, `psi_uniformly_small`, `psi_tendstoUniformly_phiPi`,
  `psi_tendstoUniformly_phiX` (uniform in the horizon `j`, and the Taylor principle eventually
  holds).
* **(2.35)**: `QuasiDiffRule`, `taylorRule_iff_quasiDiff`.
* One predetermined variable (proved here, not assumed): `PredSys`, `Decomp`, `resM`,
  `solveMN`, `predSys_formula`, `predSys_solution_form`, `predSys_existsUnique`,
  `predSys_zero_forcing`, `decomp_unique`.
* The inertial rule (2.8), p. 277: `inertCubic`, `inertOmega`, `inert_decomp`,
  `inert_identities`, `inert_forward_stable`, `inertCubic_pos_at` (the (C.23) corner claim proved
  directly), `inert_root_exists`, `inert_BK` (sufficiency in Prop. 4.4 for `(φ_π, φ_x) ≠ 0`),
  `inert_no_feedback_unbounded` (with `φ_π = φ_x = 0`, `ρ > 1`, (2.9) holds but there is no
  bounded solution), `InertialRule`, `inertial_iff_predSys`,
  `inertial_equilibrium_existsUnique`, `inertial_equilibrium_formula` (the `ω_π(î_{t−1} − ī_{t−1})`
  form), `inertial_tracking`, `inertial_shock_equivalence`.
* Inflation inertia (2.36)–(2.39): `ASInertia`, `TaylorRuleG`, `inertiaCubic`, `inertiaOmega`,
  `InertiaTaylorPrinciple`, `inertia_decomp`, `inertia_identities`, `inertia_forward_stable`,
  `inertiaCubic_pos_at`, `inertia_root_exists`, `inertia_BK`, `inertia_iff_predSys`,
  `inertia_equilibrium_existsUnique`, `inertia_equilibrium_formula`, `inertia_tracking`.
* Footnote 47, checked exactly: `fn47_gamma_half` (`ω_π ∈ (0.42036, 0.42037)`,
  `ω_x ∈ (−1.9374, −1.9371)`, printed −1.95), `fn47_gamma_one` (`ω_π ∈ (0.72839, 0.72840)`,
  `ω_x ∈ (−3.1563, −3.156)`, printed −3.17).
-/

namespace Woodford.NeoWicksellianFramework.InflationDeterminants

open Filter Topology BlanchardKahn
open SchurCohn (BothOutside bothOutside_iff_schurStable_inv)
open Determinacy2 (taylorA a25 taylorB taylorDelta taylorDelta_pos taylorLHS taylorLHS_eq
  taylorB_eq_inv taylorB_schurStable_iff taylorA_det_eq taylorRate)
open BasicModel (IS112 NKPCurve xbar)

/-! ### Powers of a stable `2 × 2` matrix are absolutely summable -/

/-! ### Eigenvalues outside the unit circle -/

/-! ### The forward solution of a stable two-variable system -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (2.31)–(2.34), pp. 276–277: the response coefficients `c_j = Bʲ v` of a
forward solution `z_t = ∑ c_j E_t e_{t+j}`. -/
def coef (B : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (j : ℕ) : Fin 2 → ℝ := (B ^ j).mulVec v

/-- Woodford (2003), p. 277: `c_0 = v`. -/
theorem coef_zero (B : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) : coef B v 0 = v := by
  simp [coef]

/-- Woodford (2003), p. 277: `c_{j+1} = B c_j`. -/
theorem coef_succ (B : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (j : ℕ) (i : Fin 2) :
    coef B v (j + 1) i = B i 0 * coef B v j 0 + B i 1 * coef B v j 1 := by
  simp only [coef, pow_succ', ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Woodford (2003), p. 277: an entrywise bound on `c_j = Bʲ v`. -/
theorem abs_coef_le (B : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (j : ℕ) (i : Fin 2) :
    |coef B v j i| ≤ (|(B ^ j) i 0| + |(B ^ j) i 1|) * (|v 0| + |v 1|) := by
  simp only [coef, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  nlinarith [abs_nonneg ((B ^ j) i 0), abs_nonneg ((B ^ j) i 1), abs_nonneg (v 0),
    abs_nonneg (v 1)]

/-- Woodford (2003), p. 277: for a stable `B` the coefficients `Bʲ v` are absolutely summable. -/
theorem summable_abs_coef {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : SchurStable (tr2 B) (det2 B))
    (v : Fin 2 → ℝ) (i : Fin 2) : Summable (fun j => |coef B v j i|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_coef_le B v · i)
    (((summable_abs_pow_entry hB i 0).add (summable_abs_pow_entry hB i 1)).mul_right _)

/-- Woodford (2003), p. 277: `∑ c_j X_j` converges for every bounded sequence `X`. -/
theorem summable_coef_mul {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : SchurStable (tr2 B) (det2 B))
    (v : Fin 2 → ℝ) (i : Fin 2) {X : ℕ → ℝ} {M : ℝ} (hX : ∀ j, |X j| ≤ M) :
    Summable (fun j => coef B v j i * X j) :=
  Summable.of_norm_bounded ((summable_abs_coef hB v i).mul_right M) (fun j => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hX j) (abs_nonneg _))

/-- Woodford (2003), (2.34), p. 277 (in the inverted form `z_t = B E_t z_{t+1} + v e_t`): the
forward solution `z_t = ∑_j Bʲ v E_t e_{t+j}`, a genuine infinite sum. -/
noncomputable def fwdVec (B : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (e : ℕ → Ω → ℝ) :
    ℕ → Fin 2 → Ω → ℝ :=
  fun t i ω => ∑' j, coef B v j i * 𝔼.E t (e (t + j)) ω

/-- Woodford (2003), p. 277: `E_s` passes through the forward sum for `s ≤ t`. -/
theorem E_fwdVec {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : SchurStable (tr2 B) (det2 B))
    (v : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ} (he : ∀ t ω, |e t ω| ≤ M) {s t : ℕ} (hst : s ≤ t)
    (i : Fin 2) (ω : Ω) :
    𝔼.E s (fwdVec 𝔼 B v e t i) ω = ∑' j, coef B v j i * 𝔼.E s (e (t + j)) ω := by
  have h := ForwardSolution.E_tsum_dom 𝔼 ((summable_abs_coef hB v i).mul_right M)
    (f := fun j ω' => coef B v j i * 𝔼.E t (e (t + j)) ω') (fun j ω' => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (he (t + j)) t ω') (abs_nonneg _)) s ω
  change 𝔼.E s (fun ω' => ∑' j, coef B v j i * 𝔼.E t (e (t + j)) ω') ω = _
  rw [h]
  refine tsum_congr fun j => ?_
  have hf : (fun ω' => coef B v j i * 𝔼.E t (e (t + j)) ω') =
      coef B v j i • 𝔼.E t (e (t + j)) := rfl
  rw [hf, map_smul, 𝔼.tower hst, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), p. 277: the forward solution is adapted. -/
theorem fwdVec_adapted {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : SchurStable (tr2 B) (det2 B))
    (v : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ} (he : ∀ t ω, |e t ω| ≤ M) :
    𝔼.AdaptedVec (fwdVec 𝔼 B v e) := by
  intro t i
  funext ω
  rw [E_fwdVec 𝔼 hB v he le_rfl i ω]
  rfl

/-- Woodford (2003), p. 277: the forward solution is bounded, by `(∑ |c_j|) M`. -/
theorem abs_fwdVec_le {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : SchurStable (tr2 B) (det2 B))
    (v : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ} (he : ∀ t ω, |e t ω| ≤ M) (t : ℕ) (i : Fin 2)
    (ω : Ω) : |fwdVec 𝔼 B v e t i ω| ≤ (∑' j, |coef B v j i|) * M := by
  have hX : ∀ j, |𝔼.E t (e (t + j)) ω| ≤ M := fun j => 𝔼.abs_E_le (he _) t ω
  have hs := summable_coef_mul hB v i hX
  change |∑' j, coef B v j i * 𝔼.E t (e (t + j)) ω| ≤ _
  have hsn : Summable (fun j => ‖coef B v j i * 𝔼.E t (e (t + j)) ω‖) := by
    simpa only [Real.norm_eq_abs] using hs.abs
  rw [← tsum_mul_right, ← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hsn).trans ?_
  refine Summable.tsum_le_tsum (fun j => ?_) hsn ((summable_abs_coef hB v i).mul_right M)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hX j) (abs_nonneg _)

/-- Woodford (2003), p. 277: the forward solution is a bounded vector process. -/
theorem fwdVec_bounded {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : SchurStable (tr2 B) (det2 B))
    (v : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ} (he : ∀ t ω, |e t ω| ≤ M) :
    BoundedVec (fwdVec 𝔼 B v e) := by
  have h0 : 0 ≤ ∑' j, |coef B v j 0| := tsum_nonneg fun j => abs_nonneg _
  have h1 : 0 ≤ ∑' j, |coef B v j 1| := tsum_nonneg fun j => abs_nonneg _
  refine ⟨((∑' j, |coef B v j 0|) + ∑' j, |coef B v j 1|) * |M|, fun t i ω =>
    (abs_fwdVec_le 𝔼 hB v he t i ω).trans ?_⟩
  have hM := le_abs_self M
  have hM0 := abs_nonneg M
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith

/-- Woodford (2003), (2.34), p. 277: the forward sum solves `z_t = B E_t z_{t+1} + v e_t` for
bounded adapted `e` and stable `B`. -/
theorem fwdVec_solves {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : SchurStable (tr2 B) (det2 B))
    (v : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ} (he : ∀ t ω, |e t ω| ≤ M) (hea : 𝔼.Adapted e) :
    𝔼.Solves B (fun t i => v i • e t) (fwdVec 𝔼 B v e) := by
  intro t i
  funext ω
  have h0 := E_fwdVec 𝔼 hB v he (Nat.le_succ t) 0 ω
  have h1 := E_fwdVec 𝔼 hB v he (Nat.le_succ t) 1 ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h0, h1]
  have hX : ∀ j, |𝔼.E t (e (t + 1 + j)) ω| ≤ M := fun j => 𝔼.abs_E_le (he _) t ω
  have hX' : ∀ j, |𝔼.E t (e (t + j)) ω| ≤ M := fun j => 𝔼.abs_E_le (he _) t ω
  have s0 := summable_coef_mul hB v 0 hX
  have s1 := summable_coef_mul hB v 1 hX
  change ∑' j, coef B v j i * 𝔼.E t (e (t + j)) ω = _
  rw [(summable_coef_mul hB v i hX').tsum_eq_zero_add, coef_zero, add_zero, hea t]
  have hshift : ∑' j, coef B v (j + 1) i * 𝔼.E t (e (t + (j + 1))) ω =
      ∑' j, (B i 0 * (coef B v j 0 * 𝔼.E t (e (t + 1 + j)) ω) +
        B i 1 * (coef B v j 1 * 𝔼.E t (e (t + 1 + j)) ω)) := by
    refine tsum_congr fun j => ?_
    rw [coef_succ, show t + (j + 1) = t + 1 + j by omega]
    ring
  rw [hshift, (s0.mul_left (B i 0)).tsum_add (s1.mul_left (B i 1)), tsum_mul_left,
    tsum_mul_left]
  ring

/-- Woodford (2003), (2.34), p. 277: with `B` stable, the forward sum is the unique bounded
adapted solution of `z_t = B E_t z_{t+1} + v e_t`. -/
theorem eq_fwdVec {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : SchurStable (tr2 B) (det2 B))
    (v : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ} (he : ∀ t ω, |e t ω| ≤ M) (hea : 𝔼.Adapted e)
    {z : ℕ → Fin 2 → Ω → ℝ} (hz : 𝔼.Solves B (fun t i => v i • e t) z) (hza : 𝔼.AdaptedVec z)
    (hzb : BoundedVec z) : z = fwdVec 𝔼 B v e :=
  𝔼.system_unique hB hz (fwdVec_solves 𝔼 hB v he hea) hza (fwdVec_adapted 𝔼 hB v he) hzb
    (fwdVec_bounded 𝔼 hB v he)

/-! ### The system `E_t z_{t+1} = A z_t + a e_t` -/

/-- Woodford (2003), eq. (2.5), p. 252, and (C.19), p. 677: the vector process `z` solves
`E_t z_{t+1} = A z_t + a e_t` at every date. -/
def ForwardSys (A : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (e : ℕ → Ω → ℝ)
    (z : ℕ → Fin 2 → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (z (t + 1) i) = A i 0 • z t 0 + A i 1 • z t 1 + a i • e t

omit 𝔼 in
/-- Woodford (2003), p. 277: the entries of `A B = 1` for `2 × 2` matrices. -/
theorem mul_eq_one_entries {A B : Matrix (Fin 2) (Fin 2) ℝ} (h : A * B = 1) :
    A 0 0 * B 0 0 + A 0 1 * B 1 0 = 1 ∧ A 0 0 * B 0 1 + A 0 1 * B 1 1 = 0 ∧
      A 1 0 * B 0 0 + A 1 1 * B 1 0 = 0 ∧ A 1 0 * B 0 1 + A 1 1 * B 1 1 = 1 := by
  have e := fun i j => congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at e
  exact ⟨by simpa using e 0 0, by simpa using e 0 1, by simpa using e 1 0, by simpa using e 1 1⟩

/-- Woodford (2003), p. 277 (solving (C.19) for `z_t`): with `B = A⁻¹`,
`E_t z_{t+1} = A z_t + a e_t` is equivalent to `z_t = B E_t z_{t+1} − B a e_t`. -/
theorem forwardSys_iff_solves {A B : Matrix (Fin 2) (Fin 2) ℝ} (hAB : A * B = 1)
    (hBA : B * A = 1) (a : Fin 2 → ℝ) (e : ℕ → Ω → ℝ) (z : ℕ → Fin 2 → Ω → ℝ) :
    ForwardSys 𝔼 A a e z ↔ 𝔼.Solves B (fun t i => (-(B.mulVec a)) i • e t) z := by
  obtain ⟨a1, a2, a3, a4⟩ := mul_eq_one_entries hAB
  obtain ⟨b1, b2, b3, b4⟩ := mul_eq_one_entries hBA
  constructor
  · intro h t i
    funext ω
    have h0 := congrFun (h t 0) ω
    have h1 := congrFun (h t 1) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at h0 h1 ⊢
    rw [h0, h1]
    fin_cases i
    · simp only [Fin.zero_eta]
      linear_combination (-(z t 0 ω)) * b1 - z t 1 ω * b2
    · simp only [Fin.mk_one]
      linear_combination (-(z t 0 ω)) * b3 - z t 1 ω * b4
  · intro h t i
    funext ω
    have h0 := congrFun (h t 0) ω
    have h1 := congrFun (h t 1) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] at h0 h1 ⊢
    rw [h0, h1]
    fin_cases i
    · simp only [Fin.zero_eta]
      linear_combination (-(𝔼.E t (z (t + 1) 0) ω) + a 0 * e t ω) * a1 +
        (-(𝔼.E t (z (t + 1) 1) ω) + a 1 * e t ω) * a2
    · simp only [Fin.mk_one]
      linear_combination (-(𝔼.E t (z (t + 1) 0) ω) + a 0 * e t ω) * a3 +
        (-(𝔼.E t (z (t + 1) 1) ω) + a 1 * e t ω) * a4

omit 𝔼 in
/-- Woodford (2003), p. 277: if both eigenvalues of `A` lie outside the unit circle then
`A⁻¹` is a stable matrix (both eigenvalues inside). -/
theorem schurStable_inv_of_rootsOutside {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : BothOutside (tr2 A) (det2 A)) : det2 A ≠ 0 ∧ SchurStable (tr2 A⁻¹) (det2 A⁻¹) := by
  obtain ⟨hd, hS⟩ := (bothOutside_iff_schurStable_inv _ _).mp hA
  rw [tr2_inv A, det2_inv A]
  exact ⟨hd, hS⟩

omit 𝔼 in
/-- Woodford (2003), eq. (2.34), p. 277 (corrected sign): the coefficients of the forward solution
are `c_j = −A^{−j−1} a`. -/
theorem coef_inv (A : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (j : ℕ) :
    coef A⁻¹ (-(A⁻¹.mulVec a)) j = -((A⁻¹ ^ (j + 1)).mulVec a) := by
  simp [coef, Matrix.mulVec_neg, Matrix.mulVec_mulVec, pow_succ]

/-- Woodford (2003), eq. (2.34), p. 277 (corrected sign): the forward solution written as
`z_t = −∑_j A^{−j−1} a E_t e_{t+j}`. -/
theorem fwdVec_inv_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) (e : ℕ → Ω → ℝ)
    (t : ℕ) (i : Fin 2) (ω : Ω) :
    fwdVec 𝔼 A⁻¹ (-(A⁻¹.mulVec a)) e t i ω =
      -∑' j, (A⁻¹ ^ (j + 1)).mulVec a i * 𝔼.E t (e (t + j)) ω := by
  change ∑' j, _ = _
  rw [← tsum_neg]
  refine tsum_congr fun j => ?_
  rw [coef_inv]
  simp

/-- **Woodford (2003), eq. (2.34), p. 277 (corrected).** If both eigenvalues of `A` lie outside
the unit circle (the condition for determinacy), then for every bounded adapted forcing `e` the
system `E_t z_{t+1} = A z_t + a e_t` has exactly one bounded adapted solution, the genuine
infinite sum `z_t = −∑_{j ≥ 0} A^{−j−1} a E_t e_{t+j}`. The printed (2.34) omits the minus sign
(see `printed_234_not_solution`). -/
theorem forwardSys_existsUnique {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : BothOutside (tr2 A) (det2 A)) (a : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ}
    (he : ∀ t ω, |e t ω| ≤ M) (hea : 𝔼.Adapted e) :
    ∃! z : ℕ → Fin 2 → Ω → ℝ, ForwardSys 𝔼 A a e z ∧ 𝔼.AdaptedVec z ∧ BoundedVec z ∧
      ∀ t i ω, z t i ω = -∑' j, (A⁻¹ ^ (j + 1)).mulVec a i * 𝔼.E t (e (t + j)) ω := by
  obtain ⟨hd, hS⟩ := schurStable_inv_of_rootsOutside hA
  have hdA : IsUnit A.det := isUnit_iff_ne_zero.mpr (by rwa [← det2_eq_det])
  have hAB : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdA
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdA
  refine ⟨fwdVec 𝔼 A⁻¹ (-(A⁻¹.mulVec a)) e, ⟨?_, fwdVec_adapted 𝔼 hS _ he,
    fwdVec_bounded 𝔼 hS _ he, fwdVec_inv_apply 𝔼 A a e⟩, ?_⟩
  · exact (forwardSys_iff_solves 𝔼 hAB hBA a e _).mpr (fwdVec_solves 𝔼 hS _ he hea)
  · rintro z ⟨hz, hza, hzb, -⟩
    exact eq_fwdVec 𝔼 hS _ he hea ((forwardSys_iff_solves 𝔼 hAB hBA a e z).mp hz) hza hzb

/-- Woodford (2003), eq. (2.34), p. 277 (corrected; uniqueness): every bounded adapted solution
of `E_t z_{t+1} = A z_t + a e_t` is `z_t = −∑_{j ≥ 0} A^{−j−1} a E_t e_{t+j}`. -/
theorem forwardSys_eq_formula {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : BothOutside (tr2 A) (det2 A)) (a : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ}
    (he : ∀ t ω, |e t ω| ≤ M) (hea : 𝔼.Adapted e) {z : ℕ → Fin 2 → Ω → ℝ}
    (hz : ForwardSys 𝔼 A a e z) (hza : 𝔼.AdaptedVec z) (hzb : BoundedVec z) (t : ℕ) (i : Fin 2)
    (ω : Ω) : z t i ω = -∑' j, (A⁻¹ ^ (j + 1)).mulVec a i * 𝔼.E t (e (t + j)) ω := by
  obtain ⟨_, hS⟩ := schurStable_inv_of_rootsOutside hA
  obtain ⟨-, hd⟩ := (bothOutside_iff_schurStable_inv _ _).mp hA
  have hdA : IsUnit A.det := isUnit_iff_ne_zero.mpr (by rwa [← det2_eq_det])
  rw [eq_fwdVec 𝔼 hS _ he hea ((forwardSys_iff_solves 𝔼 (Matrix.mul_nonsing_inv A hdA)
    (Matrix.nonsing_inv_mul A hdA) a e z).mp hz) hza hzb, fwdVec_inv_apply]

/-- Woodford (2003), eq. (2.34), p. 277, **as printed** (without the minus sign) is not a
solution: whenever `a_i e_t(ω) ≠ 0` for some `i, t, ω`, the process
`∑_j A^{−j−1} a E_t e_{t+j}` violates `E_t z_{t+1} = A z_t + a e_t`. -/
theorem printed_234_not_solution {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : BothOutside (tr2 A) (det2 A)) (a : Fin 2 → ℝ) {e : ℕ → Ω → ℝ} {M : ℝ}
    (he : ∀ t ω, |e t ω| ≤ M) (hea : 𝔼.Adapted e) {t : ℕ} {i : Fin 2} {ω : Ω}
    (hai : a i ≠ 0) (het : e t ω ≠ 0) :
    ¬ ForwardSys 𝔼 A a e
      (fun t i ω => ∑' j, (A⁻¹ ^ (j + 1)).mulVec a i * 𝔼.E t (e (t + j)) ω) := by
  intro hP
  obtain ⟨z, ⟨hz, -, -, hzf⟩, -⟩ := forwardSys_existsUnique 𝔼 hA a he hea
  have hPz : (fun t i ω => ∑' j, (A⁻¹ ^ (j + 1)).mulVec a i * 𝔼.E t (e (t + j)) ω) =
      fun t i => -z t i := by
    funext t i ω
    rw [Pi.neg_apply, hzf, neg_neg]
  rw [hPz] at hP
  have h1 := congrFun (hz t i) ω
  have h2 := congrFun (hP t i) ω
  simp only [map_neg, Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  have : a i * e t ω = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hai h
  · exact het h

/-! ### The basic neo-Wicksellian model -/

/-- Woodford (2003), eq. (1.14), p. 246: the Taylor rule
`î_t = ī_t + φ_π (π_t − π̄) + φ_x (x_t − x̄)/4`. -/
def TaylorRule (β κ φπ φx πbar : ℝ) (π x i ibar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = ibar t + φπ • (π t - fun _ => πbar) + (φx / 4) • (x t - fun _ => xbar β κ πbar)

/-- Woodford (2003), eq. (1.14), p. 246: `TaylorRule` says that the interest rate is the
canonical rule process `Determinacy2.taylorRate`. -/
theorem taylorRule_iff (β κ φπ φx πbar : ℝ) (π x i ibar : ℕ → Ω → ℝ) :
    TaylorRule β κ φπ φx πbar π x i ibar ↔ i = taylorRate β κ φπ φx πbar ibar π x :=
  funext_iff.symm

/-- Woodford (2003), (2.31)–(2.33), pp. 276–277: the exogenous gap `r̂ⁿ_t − ī_t + π̄` between the
natural rate and the intercept of the policy rule. -/
def gapForcing (πbar : ℝ) (rn ibar : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t - ibar t + fun _ => πbar

/-- Woodford (2003), (C.19), p. 677: the vector `z_t = (π_t − π̄, x_t − x̄)`. -/
noncomputable def gapVec (β κ πbar : ℝ) (π x : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![π t - fun _ => πbar, x t - fun _ => xbar β κ πbar]

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677, first row: the Phillips curve (1.13) in deviations from the
steady state is `E_t π_{t+1} − π̄ = β⁻¹(π_t − π̄) − β⁻¹κ (x_t − x̄)`. -/
theorem row0_iff {β κ : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (πt xt Eπ πbar g : ℝ) :
    πt = κ * xt + β * Eπ ↔
      Eπ - πbar = β⁻¹ * (πt - πbar) + -(β⁻¹ * κ) * (xt - xbar β κ πbar) + 0 * g := by
  unfold xbar
  constructor
  · intro h
    field_simp
    linear_combination (-1 : ℝ) * h
  · intro h
    field_simp at h
    linear_combination (-1 : ℝ) * h

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677, second row: given the Phillips curve and the Taylor rule,
the IS112 relation (1.12) `E_t x_{t+1} is − x̄ = σ(φ_π − β⁻¹)(π_t − π̄)
+ (1 + σ(φ_x/4 + β⁻¹κ))(x_t − x̄) − σ (r̂ⁿ_t − ī_t + π̄)`. -/
theorem row1_iff {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (πt xt it Eπ Ex rn ib πbar : ℝ) (has : πt = κ * xt + β * Eπ)
    (hrule : it = ib + φπ * (πt - πbar) + φx / 4 * (xt - xbar β κ πbar)) :
    xt = Ex - σ * (it - Eπ - rn) ↔
      Ex - xbar β κ πbar = σ * (φπ - β⁻¹) * (πt - πbar) +
        (1 + σ * (φx / 4 + β⁻¹ * κ)) * (xt - xbar β κ πbar) + -σ * (rn - ib + πbar) := by
  unfold xbar at hrule ⊢
  have hE : Eπ = β⁻¹ * (πt - κ * xt) := by
    field_simp
    linear_combination (-1 : ℝ) * has
  subst hrule
  rw [hE]
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination (-1 : ℝ) * h
  · intro h
    field_simp at h ⊢
    linear_combination (-1 : ℝ) * h

/-- Woodford (2003), (C.19), p. 677: under the Taylor rule (1.14), the Phillips curve (1.13) and
the IS112 relation (1.12) at every hold date iff the gap vector `z_t = (π_t − π̄, x_t − x̄)` solves
`E_t z_{t+1} = A z_t + a (r̂ⁿ_t − ī_t + π̄)`. -/
theorem as_is_iff_forwardSys {β σ κ φπ φx πbar : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0)
    {π x i rn ibar : ℕ → Ω → ℝ} (hrule : TaylorRule β κ φπ φx πbar π x i ibar) :
    (NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn) ↔
      ForwardSys 𝔼 (taylorA β σ κ φπ φx) (a25 σ) (gapForcing πbar rn ibar)
        (gapVec β κ πbar π x) := by
  constructor
  · rintro ⟨has, his⟩ t j
    funext ω
    have ha := congrFun (has t) ω
    have hi := congrFun (his t) ω
    have hr := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at ha hi hr
    fin_cases j
    · simp only [gapVec, taylorA, a25, gapForcing, Fin.zero_eta, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.empty_val', map_sub, 𝔼.const, Pi.add_apply, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul]
      exact (row0_iff hβ hκ _ _ _ _ _).mp ha
    · simp only [gapVec, taylorA, a25, gapForcing, Fin.mk_one, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.empty_val', map_sub, 𝔼.const, Pi.add_apply, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul]
      exact (row1_iff hβ hκ _ _ _ _ _ _ _ _ ha hr).mp hi
  · intro h
    have has : NKPCurve 𝔼 β κ π x := by
      intro t
      funext ω
      have h0 := congrFun (h t 0) ω
      simp only [gapVec, taylorA, a25, gapForcing, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.empty_val', map_sub, 𝔼.const, Pi.add_apply, Pi.smul_apply,
        Pi.sub_apply, smul_eq_mul] at h0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (row0_iff hβ hκ _ _ _ _ _).mpr h0
    refine ⟨has, fun t => ?_⟩
    funext ω
    have h1 := congrFun (h t 1) ω
    have ha := congrFun (has t) ω
    have hr := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at ha hr ⊢
    simp only [gapVec, taylorA, a25, gapForcing, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val', map_sub, 𝔼.const, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul] at h1
    exact (row1_iff hβ hκ _ _ _ _ _ _ _ _ ha hr).mpr h1

/-- Woodford (2003), eq. (2.7), p. 254: the Taylor principle `φ_π + (1 − β) φ_x / (4κ) > 1`. -/
def TaylorPrinciple (β κ φπ φx : ℝ) : Prop := 1 < φπ + (1 - β) * φx / (4 * κ)

omit 𝔼 in
/-- Woodford (2003), eq. (2.7), p. 254: for `κ > 0` the Taylor principle reads
`κ (1 − φ_π) < (1 − β) φ_x / 4`. -/
theorem taylorPrinciple_iff {β κ φπ φx : ℝ} (hκ : 0 < κ) :
    TaylorPrinciple β κ φπ φx ↔ κ * (1 - φπ) < (1 - β) * φx / 4 := by
  unfold TaylorPrinciple
  have e : φπ + (1 - β) * φx / (4 * κ) - 1 = ((1 - β) * φx / 4 - κ * (1 - φπ)) / κ := by
    field_simp
    ring
  rw [← sub_pos, e, div_pos_iff_of_pos_right hκ, sub_pos]

omit 𝔼 in
/-- Woodford (2003), Prop. 4.3 and eq. (2.7), p. 254 (the root-location half, App. C.2): both
eigenvalues of the matrix `A` of (C.19) lie outside the unit circle iff the Taylor principle
(2.7) holds. -/
theorem taylor_rootsOutside_iff {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hβ1 : β < 1) :
    BothOutside (tr2 (taylorA β σ κ φπ φx)) (det2 (taylorA β σ κ φπ φx)) ↔
      TaylorPrinciple β κ φπ φx := by
  have hD : det2 (taylorA β σ κ φπ φx) ≠ 0 := by
    rw [taylorA_det_eq]; exact div_ne_zero (taylorDelta_pos hσ hκ hφπ hφx).ne' hβ0.ne'
  rw [bothOutside_iff_schurStable_inv, ← tr2_inv2, one_div, ← det2_inv2,
    ← taylorB_eq_inv hβ0.ne', taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx, TaylorPrinciple,
    ← taylorLHS_eq]
  exact and_iff_right hD

/-- Woodford (2003), §2.2, p. 252 and App. C.1, p. 670: determinacy of
`E_t z_{t+1} = A z_t + a e_t`: for every forcing process `e` there is at most one bounded adapted
solution. -/
def ForwardDeterminate (A : Matrix (Fin 2) (Fin 2) ℝ) (a : Fin 2 → ℝ) : Prop :=
  ∀ (e : ℕ → Ω → ℝ) (z₁ z₂ : ℕ → Fin 2 → Ω → ℝ), ForwardSys 𝔼 A a e z₁ → ForwardSys 𝔼 A a e z₂ →
    𝔼.AdaptedVec z₁ → 𝔼.AdaptedVec z₂ → BoundedVec z₁ → BoundedVec z₂ → z₁ = z₂

/-- Woodford (2003), App. C.1, p. 670 (Blanchard–Kahn for two non-predetermined variables,
proved here): for invertible `A`, `E_t z_{t+1} = A z_t + a e_t` is determinate iff both
eigenvalues of `A` lie outside the unit circle. -/
theorem forwardDeterminate_iff [Nonempty Ω] {A : Matrix (Fin 2) (Fin 2) ℝ} (hd : det2 A ≠ 0)
    (a : Fin 2 → ℝ) : ForwardDeterminate 𝔼 A a ↔ BothOutside (tr2 A) (det2 A) := by
  have hdA : IsUnit A.det := isUnit_iff_ne_zero.mpr (by rwa [← det2_eq_det])
  have hAB : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdA
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdA
  have hS : BothOutside (tr2 A) (det2 A) ↔ SchurStable (tr2 A⁻¹) (det2 A⁻¹) := by
    rw [bothOutside_iff_schurStable_inv, tr2_inv, det2_inv]
    exact ⟨fun h => h.2, fun h => ⟨hd, h⟩⟩
  have hw : ∀ z, ForwardSys 𝔼 A a 0 z ↔ 𝔼.Solves A⁻¹ 0 z := by
    intro z
    rw [forwardSys_iff_solves 𝔼 hAB hBA a 0 z]
    have : (fun t (i : Fin 2) => (-(A⁻¹.mulVec a)) i • (0 : ℕ → Ω → ℝ) t) = 0 := by
      funext t i
      simp
    rw [this]
  rw [hS]
  constructor
  · intro hdet
    by_contra hA
    have hz : 𝔼.Solves A⁻¹ 0 0 := fun t i => by simp
    obtain ⟨y, hy, hay, hby, hne⟩ :=
      𝔼.system_not_unique hA hz (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
    exact hne (hdet 0 y 0 ((hw y).mpr hy) ((hw 0).mpr hz) hay (fun t i => by simp) hby
      ⟨0, fun t i ω => by simp⟩)
  · intro hA e z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂
    exact 𝔼.system_unique hA ((forwardSys_iff_solves 𝔼 hAB hBA a e z₁).mp h₁)
      ((forwardSys_iff_solves 𝔼 hAB hBA a e z₂).mp h₂) ha₁ ha₂ hb₁ hb₂

/-- Woodford (2003), Prop. 4.3, p. 254: under the Taylor rule (1.14) (`φ_π, φ_x ≥ 0`) the
equilibrium is determinate iff the Taylor principle (2.7) holds. -/
theorem taylor_determinate_iff [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hβ1 : β < 1) :
    ForwardDeterminate 𝔼 (taylorA β σ κ φπ φx) (a25 σ) ↔ TaylorPrinciple β κ φπ φx := by
  have hD : det2 (taylorA β σ κ φπ φx) ≠ 0 := by
    rw [taylorA_det_eq]; exact div_ne_zero (taylorDelta_pos hσ hκ hφπ hφx).ne' hβ0.ne'
  rw [forwardDeterminate_iff 𝔼 hD, taylor_rootsOutside_iff hβ0 hκ hσ hφπ hφx hβ1]

/-- Woodford (2003), eqs. (2.31)–(2.32), p. 276: the response coefficients
`(ψ^π_j, ψ^x_j) = −A^{−j−1} a` of inflation and the output gap to `E_t(r̂ⁿ − ī + π̄)_{t+j}`. -/
noncomputable def psi (β σ κ φπ φx : ℝ) (j : ℕ) : Fin 2 → ℝ :=
  -(((taylorA β σ κ φπ φx)⁻¹ ^ (j + 1)).mulVec (a25 σ))

/-- Woodford (2003), eq. (2.33), p. 277: the interest-rate coefficients
`ψ^i_j = φ_π ψ^π_j + φ_x ψ^x_j / 4`, obtained by substituting (2.31)–(2.32) into (1.14). -/
noncomputable def psiI (β σ κ φπ φx : ℝ) (j : ℕ) : ℝ :=
  φπ * psi β σ κ φπ φx j 0 + φx / 4 * psi β σ κ φπ φx j 1

omit 𝔼 in
/-- Woodford (2003), p. 277: `ψ_j` are the coefficients `c_j = Bʲ v` of the forward solution with
`B = A⁻¹`, `v = −A⁻¹ a`. -/
theorem psi_eq_coef (β σ κ φπ φx : ℝ) (j : ℕ) :
    psi β σ κ φπ φx j = coef (taylorA β σ κ φπ φx)⁻¹
      (-((taylorA β σ κ φπ φx)⁻¹.mulVec (a25 σ))) j :=
  (coef_inv _ _ _).symm

/-- Woodford (2003), p. 277: the gap vector of adapted `π, x` is adapted. -/
theorem gapVec_adapted {β κ πbar : ℝ} {π x : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hx : 𝔼.Adapted x) : 𝔼.AdaptedVec (gapVec β κ πbar π x) := by
  intro t i
  fin_cases i <;> simp [gapVec, map_sub, 𝔼.const, hπ t, hx t]

omit 𝔼 in
/-- Woodford (2003), p. 277: the gap vector of bounded `π, x` is bounded. -/
theorem gapVec_bounded {β κ πbar : ℝ} {π x : ℕ → Ω → ℝ} (hπ : BoundedProc π)
    (hx : BoundedProc x) : BoundedVec (gapVec β κ πbar π x) := by
  obtain ⟨M₁, h₁⟩ := hπ
  obtain ⟨M₂, h₂⟩ := hx
  refine ⟨M₁ + M₂ + |πbar| + |xbar β κ πbar|, fun t i ω => ?_⟩
  have a1 := h₁ t ω
  have a2 := h₂ t ω
  have b1 := abs_nonneg (π t ω)
  have b2 := abs_nonneg (x t ω)
  have c1 := abs_nonneg πbar
  have c2 := abs_nonneg (xbar β κ πbar)
  fin_cases i
  · simp only [gapVec, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
    have := abs_sub (π t ω) πbar
    linarith
  · simp only [gapVec, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply]
    have := abs_sub (x t ω) (xbar β κ πbar)
    linarith

/-- **Woodford (2003), eqs. (2.31)–(2.33), pp. 276–277 (uniqueness and form).** Under the Taylor
rule (1.14) with the Taylor principle (2.7), every bounded adapted equilibrium of (1.12)–(1.14)
is `π_t = π̄ + ∑ ψ^π_j E_t g_{t+j}`, `x_t = x̄ + ∑ ψ^x_j E_t g_{t+j}`,
`î_t = ī_t + ∑ ψ^i_j E_t g_{t+j}`, where `g = r̂ⁿ − ī + π̄` (genuine infinite sums). -/
theorem taylor_equilibrium_formula {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hβ1 : β < 1)
    (hTP : TaylorPrinciple β κ φπ φx) {rn ibar : ℕ → Ω → ℝ} {M : ℝ}
    (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ M) (hga : 𝔼.Adapted (gapForcing πbar rn ibar))
    {π x i : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn)
    (hrule : TaylorRule β κ φπ φx πbar π x i ibar) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (t : ℕ) (ω : Ω) :
    π t ω = πbar + ∑' j, psi β σ κ φπ φx j 0 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) ω ∧
    x t ω = xbar β κ πbar +
      ∑' j, psi β σ κ φπ φx j 1 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) ω ∧
    i t ω = ibar t ω + ∑' j, psiI β σ κ φπ φx j * 𝔼.E t (gapForcing πbar rn ibar (t + j)) ω := by
  have hRO := (taylor_rootsOutside_iff hβ0 hκ hσ hφπ hφx hβ1).mpr hTP
  have hz := (as_is_iff_forwardSys 𝔼 hβ0.ne' hκ.ne' hrule).mp ⟨has, his⟩
  have hf := forwardSys_eq_formula 𝔼 hRO (a25 σ) hg hga hz (gapVec_adapted 𝔼 hπa hxa)
    (gapVec_bounded hπb hxb) t
  have hneg : ∀ k : Fin 2, -∑' j, ((taylorA β σ κ φπ φx)⁻¹ ^ (j + 1)).mulVec (a25 σ) k *
      𝔼.E t (gapForcing πbar rn ibar (t + j)) ω =
      ∑' j, psi β σ κ φπ φx j k * 𝔼.E t (gapForcing πbar rn ibar (t + j)) ω := by
    intro k
    rw [← tsum_neg]
    refine tsum_congr fun j => ?_
    simp [psi, neg_mul]
  have h0 := hf 0 ω
  have h1 := hf 1 ω
  rw [hneg] at h0 h1
  simp only [gapVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.sub_apply] at h0 h1
  have hπ : π t ω = πbar + ∑' j, psi β σ κ φπ φx j 0 *
      𝔼.E t (gapForcing πbar rn ibar (t + j)) ω := by linarith
  have hx : x t ω = xbar β κ πbar + ∑' j, psi β σ κ φπ φx j 1 *
      𝔼.E t (gapForcing πbar rn ibar (t + j)) ω := by linarith
  refine ⟨hπ, hx, ?_⟩
  obtain ⟨_, hS⟩ := schurStable_inv_of_rootsOutside hRO
  have hX : ∀ j, |𝔼.E t (gapForcing πbar rn ibar (t + j)) ω| ≤ M :=
    fun j => 𝔼.abs_E_le (hg _) t ω
  have s0 := summable_coef_mul hS (-((taylorA β σ κ φπ φx)⁻¹.mulVec (a25 σ))) 0 hX
  have s1 := summable_coef_mul hS (-((taylorA β σ κ φπ φx)⁻¹.mulVec (a25 σ))) 1 hX
  simp only [← psi_eq_coef] at s0 s1
  have hr := congrFun (hrule t) ω
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hr
  rw [hr, hπ, hx]
  have e : ∑' j, psiI β σ κ φπ φx j * 𝔼.E t (gapForcing πbar rn ibar (t + j)) ω =
      φπ * ∑' j, psi β σ κ φπ φx j 0 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) ω +
        φx / 4 * ∑' j, psi β σ κ φπ φx j 1 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) ω := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (s0.mul_left φπ).tsum_add (s1.mul_left (φx / 4))]
    refine tsum_congr fun j => ?_
    simp only [psiI]
    ring
  rw [e]
  ring

/-- **Woodford (2003), eqs. (2.31)–(2.33), pp. 276–277 (existence and uniqueness).** Under the
Taylor rule (1.14) with the Taylor principle (2.7), for bounded adapted `r̂ⁿ − ī + π̄` there is
exactly one equilibrium `(π, x, î)` of (1.12)–(1.14) with `π, x` bounded and adapted. -/
theorem taylor_equilibrium_existsUnique {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hβ1 : β < 1)
    (hTP : TaylorPrinciple β κ φπ φx) {rn ibar : ℕ → Ω → ℝ} {M : ℝ}
    (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ M)
    (hga : 𝔼.Adapted (gapForcing πbar rn ibar)) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      NKPCurve 𝔼 β κ p.1 p.2.1 ∧ IS112 𝔼 σ p.2.1 p.2.2 p.1 rn ∧
        TaylorRule β κ φπ φx πbar p.1 p.2.1 p.2.2 ibar ∧ 𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2.1 ∧
          BoundedProc p.1 ∧ BoundedProc p.2.1 := by
  have hRO := (taylor_rootsOutside_iff hβ0 hκ hσ hφπ hφx hβ1).mpr hTP
  obtain ⟨z, ⟨hz, hza, hzb, -⟩, -⟩ := forwardSys_existsUnique 𝔼 hRO (a25 σ) hg hga
  set π : ℕ → Ω → ℝ := fun t => z t 0 + fun _ => πbar with hπdef
  set x : ℕ → Ω → ℝ := fun t => z t 1 + fun _ => xbar β κ πbar with hxdef
  set i : ℕ → Ω → ℝ := fun t => ibar t + φπ • (π t - fun _ => πbar) +
    (φx / 4) • (x t - fun _ => xbar β κ πbar) with hidef
  have hrule : TaylorRule β κ φπ φx πbar π x i ibar := fun t => rfl
  have hgap : gapVec β κ πbar π x = z := by
    funext t k
    fin_cases k <;> simp [gapVec, hπdef, hxdef]
  have hsys := (as_is_iff_forwardSys 𝔼 hβ0.ne' hκ.ne' hrule).mpr (by rw [hgap]; exact hz)
  obtain ⟨Mz, hMz⟩ := hzb
  have hπa : 𝔼.Adapted π := fun t => by simp [hπdef, map_add, hza t 0, 𝔼.const]
  have hxa : 𝔼.Adapted x := fun t => by simp [hxdef, map_add, hza t 1, 𝔼.const]
  have hπb : BoundedProc π := ⟨Mz + |πbar|, fun t ω => by
    simp only [hπdef, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hMz t 0 ω) le_rfl)⟩
  have hxb : BoundedProc x := ⟨Mz + |xbar β κ πbar|, fun t ω => by
    simp only [hxdef, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hMz t 1 ω) le_rfl)⟩
  refine ⟨(π, x, i), ⟨hsys.1, hsys.2, hrule, hπa, hxa, hπb, hxb⟩, ?_⟩
  rintro ⟨π', x', i'⟩ ⟨has', his', hrule', hπa', hxa', hπb', hxb'⟩
  dsimp only at has' his' hrule' hπa' hxa' hπb' hxb'
  have e1 : π' = π := by
    funext t ω
    rw [(taylor_equilibrium_formula 𝔼 hβ0 hκ hσ hφπ hφx hβ1 hTP hg hga has' his' hrule' hπa'
      hxa' hπb' hxb' t ω).1, (taylor_equilibrium_formula 𝔼 hβ0 hκ hσ hφπ hφx hβ1 hTP hg hga
      hsys.1 hsys.2 hrule hπa hxa hπb hxb t ω).1]
  have e2 : x' = x := by
    funext t ω
    rw [(taylor_equilibrium_formula 𝔼 hβ0 hκ hσ hφπ hφx hβ1 hTP hg hga has' his' hrule' hπa'
      hxa' hπb' hxb' t ω).2.1, (taylor_equilibrium_formula 𝔼 hβ0 hκ hσ hφπ hφx hβ1 hTP hg hga
      hsys.1 hsys.2 hrule hπa hxa hπb hxb t ω).2.1]
  have e3 : i' = i := by
    funext t
    rw [hrule' t, hrule t, e1, e2]
  simp only [e1, e2, e3]

/-! ### Shock equivalence and tracking the natural rate (pp. 284, 287) -/

/-- **Woodford (2003), p. 284 (shock equivalence).** Under (1.14) with the Taylor principle, the
equilibrium depends on `r̂ⁿ` and `ī` only through the gap `r̂ⁿ − ī`: two economies with the same
gap have the same inflation and output gap, and the same `î − ī`. -/
theorem shock_equivalence {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hβ1 : β < 1)
    (hTP : TaylorPrinciple β κ φπ φx) {rn ibar rn' ibar' : ℕ → Ω → ℝ} {M : ℝ}
    (hgap : gapForcing πbar rn ibar = gapForcing πbar rn' ibar')
    (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ M) (hga : 𝔼.Adapted (gapForcing πbar rn ibar))
    {π x i π' x' i' : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn)
    (hrule : TaylorRule β κ φπ φx πbar π x i ibar) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (hπb : BoundedProc π) (hxb : BoundedProc x)
    (has' : NKPCurve 𝔼 β κ π' x') (his' : IS112 𝔼 σ x' i' π' rn')
    (hrule' : TaylorRule β κ φπ φx πbar π' x' i' ibar') (hπa' : 𝔼.Adapted π')
    (hxa' : 𝔼.Adapted x') (hπb' : BoundedProc π') (hxb' : BoundedProc x') :
    π = π' ∧ x = x' ∧ i - ibar = i' - ibar' := by
  have hg' : ∀ t ω, |gapForcing πbar rn' ibar' t ω| ≤ M := by rw [← hgap]; exact hg
  have hga' : 𝔼.Adapted (gapForcing πbar rn' ibar') := by rw [← hgap]; exact hga
  have F := taylor_equilibrium_formula 𝔼 hβ0 hκ hσ hφπ hφx hβ1 hTP hg hga has his hrule hπa hxa
    hπb hxb
  have F' := taylor_equilibrium_formula 𝔼 hβ0 hκ hσ hφπ hφx hβ1 hTP hg' hga' has' his' hrule'
    hπa' hxa' hπb' hxb'
  rw [← hgap] at F'
  refine ⟨funext fun t => funext fun ω => ?_, funext fun t => funext fun ω => ?_,
    funext fun t => funext fun ω => ?_⟩
  · rw [(F t ω).1, (F' t ω).1]
  · rw [(F t ω).2.1, (F' t ω).2.1]
  · simp only [Pi.sub_apply]
    rw [(F t ω).2.2, (F' t ω).2.2]
    ring

/-- Woodford (2003), p. 284: the response to a disturbance `h` to the natural rate of interest
equals the response to a monetary-policy disturbance `−h` to the intercept `ī` (same inflation and
output gap). -/
theorem natural_rate_shock_eq_policy_shock {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hβ1 : β < 1)
    (hTP : TaylorPrinciple β κ φπ φx) {rn ibar h : ℕ → Ω → ℝ} {M : ℝ}
    (hg : ∀ t ω, |gapForcing πbar (rn + h) ibar t ω| ≤ M)
    (hga : 𝔼.Adapted (gapForcing πbar (rn + h) ibar))
    {π x i π' x' i' : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π (rn + h))
    (hrule : TaylorRule β κ φπ φx πbar π x i ibar) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (hπb : BoundedProc π) (hxb : BoundedProc x)
    (has' : NKPCurve 𝔼 β κ π' x') (his' : IS112 𝔼 σ x' i' π' rn)
    (hrule' : TaylorRule β κ φπ φx πbar π' x' i' (ibar - h)) (hπa' : 𝔼.Adapted π')
    (hxa' : 𝔼.Adapted x') (hπb' : BoundedProc π') (hxb' : BoundedProc x') :
    π = π' ∧ x = x' := by
  have hgap : gapForcing πbar (rn + h) ibar = gapForcing πbar rn (ibar - h) := by
    funext t
    simp only [gapForcing, Pi.add_apply, Pi.sub_apply]
    abel
  obtain ⟨h1, h2, -⟩ := shock_equivalence 𝔼 hβ0 hκ hσ hφπ hφx hβ1 hTP hgap hg hga has his hrule
    hπa hxa hπb hxb has' his' hrule' hπa' hxa' hπb' hxb'
  exact ⟨h1, h2⟩

/-- **Woodford (2003), p. 287.** If the intercept tracks the natural rate, `ī_t = r̂ⁿ_t + π̄`, and
the response coefficients imply determinacy (the Taylor principle), the unique bounded adapted
equilibrium has `π_t = π̄`, `x_t = x̄` and `î_t = ī_t` at all dates: complete stabilisation. -/
theorem tracking_natural_rate {β σ κ φπ φx πbar : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hβ1 : β < 1)
    (hTP : TaylorPrinciple β κ φπ φx) {rn ibar : ℕ → Ω → ℝ}
    (htrack : ∀ t, ibar t = rn t + fun _ => πbar)
    {π x i : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn)
    (hrule : TaylorRule β κ φπ φx πbar π x i ibar) (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x)
    (hπb : BoundedProc π) (hxb : BoundedProc x) (t : ℕ) (ω : Ω) :
    π t ω = πbar ∧ x t ω = xbar β κ πbar ∧ i t ω = ibar t ω := by
  have h0 : gapForcing πbar rn ibar = 0 := by
    funext t
    simp only [gapForcing, htrack t, Pi.zero_apply]
    abel
  have hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ 0 := by simp [h0]
  have hga : 𝔼.Adapted (gapForcing πbar rn ibar) := by
    rw [h0]
    intro t
    simp
  have F := taylor_equilibrium_formula 𝔼 hβ0 hκ hσ hφπ hφx hβ1 hTP hg hga has his hrule hπa hxa
    hπb hxb t ω
  simp only [h0, Pi.zero_apply, map_zero, mul_zero, tsum_zero, add_zero] at F
  exact F

/-- Woodford (2003), p. 287 (existence half): with `ī_t = r̂ⁿ_t + π̄` the constant paths
`π_t = π̄`, `x_t = x̄`, `î_t = ī_t` form an equilibrium (for any response coefficients). -/
theorem tracking_natural_rate_exists {β σ κ φπ φx πbar : ℝ} (hκ : 0 < κ)
    {rn ibar : ℕ → Ω → ℝ} (htrack : ∀ t, ibar t = rn t + fun _ => πbar) :
    NKPCurve 𝔼 β κ (fun _ _ => πbar) (fun _ _ => xbar β κ πbar) ∧
      IS112 𝔼 σ (fun _ _ => xbar β κ πbar) ibar (fun _ _ => πbar) rn ∧
      TaylorRule β κ φπ φx πbar (fun _ _ => πbar) (fun _ _ => xbar β κ πbar) ibar ibar := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω
    simp only [𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul, xbar]
    field_simp
    ring
  · funext ω
    have := congrFun (htrack t) ω
    simp only [𝔼.const, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply] at this ⊢
    rw [this]
    ring
  · funext ω
    simp

/-! ### Strong responses make every response coefficient small (p. 288) -/

omit 𝔼 in
/-- Woodford (2003), p. 277: the inverse of the matrix of (C.19) is the forward matrix
`B = Δ⁻¹ [[β + βσφ_x/4 + σκ, κ], [σ(1 − βφ_π), 1]]` (`Determinacy2.taylorB`). -/
theorem taylorA_inv {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) :
    (taylorA β σ κ φπ φx)⁻¹ = taylorB β σ κ φπ φx := by
  rw [← inv2_eq_inv, taylorB_eq_inv hβ]

omit 𝔼 in
/-- Woodford (2003), p. 276: `(ψ^π_0, ψ^x_0) = (σκ/Δ, σ/Δ)`, the impact responses. -/
theorem psi_zero {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) :
    psi β σ κ φπ φx 0 0 = σ * κ / taylorDelta σ κ φπ φx ∧
      psi β σ κ φπ φx 0 1 = σ / taylorDelta σ κ φπ φx := by
  simp only [psi, zero_add, pow_one, taylorA_inv hβ, a25]
  constructor <;> simp [taylorB] <;> ring

omit 𝔼 in
/-- Woodford (2003), p. 276: the recursion `ψ_{j+1} = A⁻¹ ψ_j`. -/
theorem psi_succ {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (j : ℕ) :
    psi β σ κ φπ φx (j + 1) 0 = (β + β * σ * φx / 4 + σ * κ) / taylorDelta σ κ φπ φx *
        psi β σ κ φπ φx j 0 + κ / taylorDelta σ κ φπ φx * psi β σ κ φπ φx j 1 ∧
      psi β σ κ φπ φx (j + 1) 1 = σ * (1 - β * φπ) / taylorDelta σ κ φπ φx *
        psi β σ κ φπ φx j 0 + 1 / taylorDelta σ κ φπ φx * psi β σ κ φπ φx j 1 := by
  have e0 : taylorB β σ κ φπ φx 0 0 = (β + β * σ * φx / 4 + σ * κ) / taylorDelta σ κ φπ φx := by
    simp only [taylorB, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  have e1 : taylorB β σ κ φπ φx 0 1 = κ / taylorDelta σ κ φπ φx := rfl
  have e2 : taylorB β σ κ φπ φx 1 0 = σ * (1 - β * φπ) / taylorDelta σ κ φπ φx := rfl
  have e3 : taylorB β σ κ φπ φx 1 1 = 1 / taylorDelta σ κ φπ φx := rfl
  simp only [psi_eq_coef, coef_succ]
  rw [taylorA_inv hβ, e0, e1, e2, e3]
  exact ⟨rfl, rfl⟩

omit 𝔼 in
/-- **Woodford (2003), p. 288 (explicit bound).** With `Δ = 1 + σφ_x/4 + σκφ_π` large enough,
every response coefficient is bounded uniformly in the horizon `j`:
`|ψ^x_j| ≤ σ(1 + 2β)/Δ` and `|ψ^π_j| ≤ σ(1 + 2β)/Δ · κ/(2β)`. -/
theorem psi_bound {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hK1 : σ * κ + 2 * β ≤ (1 - β) * taylorDelta σ κ φπ φx)
    (hK2 : 1 + σ * κ / β ≤ taylorDelta σ κ φπ φx) (j : ℕ) :
    |psi β σ κ φπ φx j 0| ≤ σ * (1 + 2 * β) / taylorDelta σ κ φπ φx * (κ / (2 * β)) ∧
      |psi β σ κ φπ φx j 1| ≤ σ * (1 + 2 * β) / taylorDelta σ κ φπ φx := by
  set Δ := taylorDelta σ κ φπ φx with hΔdef
  have hΔ1 : 1 + σ * φx / 4 ≤ Δ := by
    have : 0 ≤ σ * κ * φπ := by positivity
    simp only [hΔdef, taylorDelta]
    linarith
  have hΔ2 : 1 + σ * κ * φπ ≤ Δ := by
    have : 0 ≤ σ * φx / 4 := by positivity
    simp only [hΔdef, taylorDelta]
    linarith
  have hΔ : 0 < Δ := by
    have : 0 ≤ σ * φx / 4 := by positivity
    linarith
  set W := σ * (1 + 2 * β) / Δ with hW
  have hW0 : 0 < W := by positivity
  have hr : 0 < κ / (2 * β) := by positivity
  -- row bounds
  have row1 : (β + β * σ * φx / 4 + σ * κ) / Δ + κ / Δ * (2 * β / κ) ≤ 1 := by
    have e : (β + β * σ * φx / 4 + σ * κ) / Δ + κ / Δ * (2 * β / κ) =
        (β * (1 + σ * φx / 4) + σ * κ + 2 * β) / Δ := by
      field_simp
    rw [e, div_le_one hΔ]
    have := mul_le_mul_of_nonneg_left hΔ1 hβ0.le
    nlinarith
  have row2 : σ * (1 + β * φπ) / Δ * (κ / (2 * β)) + 1 / Δ ≤ 1 := by
    have e : σ * (1 + β * φπ) / Δ * (κ / (2 * β)) + 1 / Δ =
        (σ * κ / β + σ * κ * φπ + 2) / (2 * Δ) := by
      field_simp
    rw [e, div_le_one (by positivity)]
    linarith
  have hB00 : 0 ≤ (β + β * σ * φx / 4 + σ * κ) / Δ := by positivity
  have hB01 : 0 ≤ κ / Δ := by positivity
  have hB11 : 0 ≤ 1 / Δ := by positivity
  have hB10 : |σ * (1 - β * φπ) / Δ| ≤ σ * (1 + β * φπ) / Δ := by
    rw [abs_div, abs_of_pos hΔ, abs_mul, abs_of_pos hσ]
    gcongr
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hβ0.le hφπ]
  induction j with
  | zero =>
    obtain ⟨h0, h1⟩ := psi_zero (σ := σ) (κ := κ) (φπ := φπ) (φx := φx) hβ0.ne'
    rw [← hΔdef] at h0 h1
    rw [h0, h1, abs_of_pos (by positivity), abs_of_pos (by positivity)]
    constructor
    · rw [hW]
      field_simp
      nlinarith [mul_pos hσ hκ]
    · rw [hW]
      gcongr
      nlinarith
  | succ j ih =>
    obtain ⟨h0, h1⟩ := psi_succ (σ := σ) (κ := κ) (φπ := φπ) (φx := φx) hβ0.ne' j
    rw [← hΔdef] at h0 h1
    obtain ⟨ih0, ih1⟩ := ih
    rw [h0, h1]
    constructor
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hB00, abs_of_nonneg hB01]
      calc (β + β * σ * φx / 4 + σ * κ) / Δ * |psi β σ κ φπ φx j 0| +
            κ / Δ * |psi β σ κ φπ φx j 1|
          ≤ (β + β * σ * φx / 4 + σ * κ) / Δ * (W * (κ / (2 * β))) + κ / Δ * W := by gcongr
        _ = (W * (κ / (2 * β))) * ((β + β * σ * φx / 4 + σ * κ) / Δ +
            κ / Δ * (2 * β / κ)) := by
          field_simp
        _ ≤ W * (κ / (2 * β)) * 1 := by gcongr
        _ = W * (κ / (2 * β)) := mul_one _
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hB11]
      calc |σ * (1 - β * φπ) / Δ| * |psi β σ κ φπ φx j 0| + 1 / Δ * |psi β σ κ φπ φx j 1|
          ≤ σ * (1 + β * φπ) / Δ * (W * (κ / (2 * β))) + 1 / Δ * W := by
            gcongr
        _ = W * (σ * (1 + β * φπ) / Δ * (κ / (2 * β)) + 1 / Δ) := by ring
        _ ≤ W * 1 := by gcongr
        _ = W := mul_one _

omit 𝔼 in
/-- **Woodford (2003), p. 288.** For every `ε > 0` there is `K` such that whenever
`Δ = 1 + σφ_x/4 + σκφ_π ≥ K` (i.e. `φ_π` or `φ_x` is large enough), the rule satisfies the Taylor
principle (so the equilibrium is determinate) and every response coefficient `ψ^π_j`, `ψ^x_j` (all
horizons `j` at once) is smaller than `ε` in absolute value. -/
theorem psi_uniformly_small {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ φπ φx, 0 ≤ φπ → 0 ≤ φx → K ≤ taylorDelta σ κ φπ φx →
      TaylorPrinciple β κ φπ φx ∧ ∀ j k, |psi β σ κ φπ φx j k| < ε := by
  set C := σ * (1 + 2 * β) * (1 + κ / (2 * β)) with hC
  have hC0 : 0 < C := by positivity
  refine ⟨max (max ((σ * κ + 2 * β) / (1 - β)) (1 + σ * κ / β))
    (max (C / ε + 1) (σ * κ / (1 - β) + 2)), ?_⟩
  intro φπ φx hφπ hφx hK
  set Δ := taylorDelta σ κ φπ φx with hΔdef
  have hK1 : (σ * κ + 2 * β) / (1 - β) ≤ Δ := le_trans (by simp) hK
  have hK2 : 1 + σ * κ / β ≤ Δ := le_trans (by simp) hK
  have hK3 : C / ε + 1 ≤ Δ := le_trans (by simp) hK
  have hK4 : σ * κ / (1 - β) + 2 ≤ Δ := le_trans (by simp) hK
  have h1b : 0 < 1 - β := by linarith
  have hΔ : 0 < Δ := by
    have : 0 ≤ C / ε := by positivity
    linarith
  refine ⟨?_, ?_⟩
  · rw [taylorPrinciple_iff hκ]
    have hd : Δ - 1 = σ * φx / 4 + σ * κ * φπ := by
      simp only [hΔdef, taylorDelta]
      ring
    have h1 : σ * κ < (1 - β) * (σ * φx / 4 + σ * κ * φπ) := by
      rw [← hd]
      have := (div_lt_iff₀ h1b).mp (by linarith : σ * κ / (1 - β) < Δ - 1)
      nlinarith
    have h2 : σ * κ < σ * ((1 - β) * φx / 4 + κ * φπ) := by
      have : (1 - β) * (σ * κ * φπ) ≤ σ * κ * φπ := by
        have : 0 ≤ σ * κ * φπ := by positivity
        nlinarith
      nlinarith
    have h3 := lt_of_mul_lt_mul_left h2 hσ.le
    nlinarith
  · have hB := psi_bound hβ0 hβ1 hκ hσ hφπ hφx ((div_le_iff₀ h1b).mp hK1 |>.trans_eq
      (by ring)) hK2
    have hCD : C / Δ < ε := by
      rw [div_lt_iff₀ hΔ]
      have := (div_lt_iff₀ hε).mp (by linarith : C / ε < Δ)
      linarith
    have hsplit : C / Δ = σ * (1 + 2 * β) / Δ + σ * (1 + 2 * β) / Δ * (κ / (2 * β)) := by
      rw [hC]
      ring
    have hp1 : 0 ≤ σ * (1 + 2 * β) / Δ := by positivity
    have hp2 : 0 ≤ σ * (1 + 2 * β) / Δ * (κ / (2 * β)) := by positivity
    have hW : σ * (1 + 2 * β) / Δ ≤ C / Δ := by linarith
    have hW' : σ * (1 + 2 * β) / Δ * (κ / (2 * β)) ≤ C / Δ := by linarith
    intro j k
    obtain ⟨b0, b1⟩ := hB j
    fin_cases k
    · exact lt_of_le_of_lt (b0.trans hW') hCD
    · exact lt_of_le_of_lt (b1.trans hW) hCD

omit 𝔼 in
/-- **Woodford (2003), p. 288 (limit statement, large `φ_π`).** For fixed `φ_x ≥ 0`, as
`φ_π → ∞` the rule eventually satisfies the Taylor principle and the response coefficients
`ψ^π_j`, `ψ^x_j` tend to zero **uniformly in the horizon `j`**. -/
theorem psi_tendstoUniformly_phiPi {β σ κ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφx : 0 ≤ φx) :
    (∀ᶠ φπ in atTop, TaylorPrinciple β κ φπ φx) ∧ ∀ k : Fin 2,
      TendstoUniformly (fun φπ j => psi β σ κ φπ φx j k) (fun _ => 0) atTop := by
  have key : ∀ ε > 0, ∀ᶠ φπ in atTop, TaylorPrinciple β κ φπ φx ∧
      ∀ j k, |psi β σ κ φπ φx j k| < ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := psi_uniformly_small hβ0 hβ1 hκ hσ hε
    filter_upwards [eventually_ge_atTop (max 0 (K / (σ * κ)))] with φπ hφ
    have h0 : 0 ≤ φπ := le_trans (le_max_left _ _) hφ
    have h1 : K / (σ * κ) ≤ φπ := le_trans (le_max_right _ _) hφ
    refine hK φπ φx h0 hφx ?_
    have := (div_le_iff₀ (by positivity : 0 < σ * κ)).mp h1
    have : 0 ≤ σ * φx / 4 := by positivity
    simp only [taylorDelta]
    nlinarith
  refine ⟨(key 1 one_pos).mono fun _ h => h.1, fun k => ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [key ε hε] with φπ h j
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact h.2 j k

omit 𝔼 in
/-- **Woodford (2003), p. 288 (limit statement, large `φ_x`).** For fixed `φ_π ≥ 0`, as
`φ_x → ∞` the rule eventually satisfies the Taylor principle and the response coefficients
`ψ^π_j`, `ψ^x_j` tend to zero uniformly in the horizon `j`. -/
theorem psi_tendstoUniformly_phiX {β σ κ φπ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hφπ : 0 ≤ φπ) :
    (∀ᶠ φx in atTop, TaylorPrinciple β κ φπ φx) ∧ ∀ k : Fin 2,
      TendstoUniformly (fun φx j => psi β σ κ φπ φx j k) (fun _ => 0) atTop := by
  have key : ∀ ε > 0, ∀ᶠ φx in atTop, TaylorPrinciple β κ φπ φx ∧
      ∀ j k, |psi β σ κ φπ φx j k| < ε := by
    intro ε hε
    obtain ⟨K, hK⟩ := psi_uniformly_small hβ0 hβ1 hκ hσ hε
    filter_upwards [eventually_ge_atTop (max 0 (4 * K / σ))] with φx hφ
    have h0 : 0 ≤ φx := le_trans (le_max_left _ _) hφ
    have h1 : 4 * K / σ ≤ φx := le_trans (le_max_right _ _) hφ
    refine hK φπ φx hφπ h0 ?_
    have := (div_le_iff₀ hσ).mp h1
    have : 0 ≤ σ * κ * φπ := by positivity
    simp only [taylorDelta]
    nlinarith
  refine ⟨(key 1 one_pos).mono fun _ h => h.1, fun k => ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [key ε hε] with φx h j
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact h.2 j k

/-! ### (2.35): an AR(1) intercept is a quasi-differenced rule (p. 281) -/

/-- Woodford (2003), eq. (2.35), p. 281: the quasi-differenced rule
`ĩ_t = ρ ĩ_{t−1} + φ_π(π̃_t − ρ π̃_{t−1}) + (φ_x/4)(x̃_t − ρ x̃_{t−1}) + ε_t` (for `t ≥ 1`), with
`ĩ = î − π̄`, `π̃ = π − π̄`, `x̃ = x − x̄`. -/
def QuasiDiffRule (ρ φπ φx πbar xb : ℝ) (π x i ε : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, i (t + 1) ω - πbar = ρ * (i t ω - πbar) +
    φπ * ((π (t + 1) ω - πbar) - ρ * (π t ω - πbar)) +
    φx / 4 * ((x (t + 1) ω - xb) - ρ * (x t ω - xb)) + ε (t + 1) ω

/-- **Woodford (2003), eq. (2.35), p. 281.** If the intercept follows the AR(1) law
`ī_t − π̄ = ρ(ī_{t−1} − π̄) + ε_t`, the Taylor rule (1.14) at every date is equivalent to (1.14) at
date 0 together with the quasi-differenced rule (2.35) at every later date. -/
theorem taylorRule_iff_quasiDiff {β κ φπ φx πbar ρ : ℝ} {π x i ibar ε : ℕ → Ω → ℝ}
    (hAR : ∀ t ω, ibar (t + 1) ω - πbar = ρ * (ibar t ω - πbar) + ε (t + 1) ω) :
    TaylorRule β κ φπ φx πbar π x i ibar ↔
      (∀ ω, i 0 ω = ibar 0 ω + φπ * (π 0 ω - πbar) + φx / 4 * (x 0 ω - xbar β κ πbar)) ∧
        QuasiDiffRule ρ φπ φx πbar (xbar β κ πbar) π x i ε := by
  have hpt : TaylorRule β κ φπ φx πbar π x i ibar ↔ ∀ t ω,
      i t ω = ibar t ω + φπ * (π t ω - πbar) + φx / 4 * (x t ω - xbar β κ πbar) := by
    constructor
    · intro h t ω
      have := congrFun (h t) ω
      simpa using this
    · intro h t
      funext ω
      simpa using h t ω
  rw [hpt]
  constructor
  · intro h
    refine ⟨h 0, fun t ω => ?_⟩
    rw [h (t + 1) ω, h t ω]
    linear_combination hAR t ω
  · rintro ⟨h0, hq⟩ t
    induction t with
    | zero => exact h0
    | succ t ih =>
      intro ω
      have := hq t ω
      rw [ih ω] at this
      linear_combination this - hAR t ω

/-! ### Systems with one predetermined variable (pp. 277, 284–285) -/

/-- Woodford (2003), pp. 277 and 284–285 (the inertial rule (2.8) and the inflation-inertia
model (2.36)): two non-predetermined variables `z_t` and one predetermined variable `s_t`,
`P z_t = N E_t z_{t+1} + h s_t + k s_{t+1} + b g_t` and `s_{t+1} = ρ s_t + φ · z_t`. -/
def PredSys (P N : Matrix (Fin 2) (Fin 2) ℝ) (h k b φ : Fin 2 → ℝ) (ρ : ℝ) (g : ℕ → Ω → ℝ)
    (z : ℕ → Fin 2 → Ω → ℝ) (s : ℕ → Ω → ℝ) : Prop :=
  (∀ t i, P i 0 • z t 0 + P i 1 • z t 1 = N i 0 • 𝔼.E t (z (t + 1) 0) +
    N i 1 • 𝔼.E t (z (t + 1) 1) + h i • s t + k i • s (t + 1) + b i • g t) ∧
  ∀ t, s (t + 1) = ρ • s t + φ 0 • z t 0 + φ 1 • z t 1

/-- Woodford (2003), p. 277: a decomposition `z_t = ω s_t + ẑ_t`, `s_{t+1} = λ s_t + φ · ẑ_t`:
`(λ, ω)` solve the homogeneous equations `P ω = λ N ω + h + λ k`, `λ = ρ + φ · ω`
(`λ` is the eigenvalue attached to the predetermined variable). -/
def Decomp (P N : Matrix (Fin 2) (Fin 2) ℝ) (h k φ : Fin 2 → ℝ) (ρ lam : ℝ) (ω : Fin 2 → ℝ) :
    Prop :=
  (∀ i, P i 0 * ω 0 + P i 1 * ω 1 = lam * (N i 0 * ω 0 + N i 1 * ω 1) + h i + k i * lam) ∧
    lam = ρ + φ 0 * ω 0 + φ 1 * ω 1

/-- Woodford (2003), p. 277: the matrix `M = P − (N ω + k) φᵀ` of the forward system satisfied
by `ẑ_t = z_t − ω s_t`. -/
def resM (P N : Matrix (Fin 2) (Fin 2) ℝ) (k φ ω : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => P i j - (N i 0 * ω 0 + N i 1 * ω 1 + k i) * φ j

/-- Woodford (2003), p. 277: `w = M⁻¹ b`, written with the adjugate. -/
noncomputable def solvew (M : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(M 1 1 * b 0 - M 0 1 * b 1) / det2 M, (M 0 0 * b 1 - M 1 0 * b 0) / det2 M]

omit 𝔼 in
/-- Woodford (2003), p. 277: the row identity behind the decomposition — given the law of
motion of `s`, row `i` of `P z_t = N E_t z_{t+1} + h s_t + k s_{t+1} + b g_t` is equivalent to
row `i` of `M ẑ_t = N E_t ẑ_{t+1} + b g_t`. -/
theorem row_iff_res {P N : Matrix (Fin 2) (Fin 2) ℝ} {h k b φ ω : Fin 2 → ℝ} {ρ lam : ℝ}
    (hD : Decomp P N h k φ ρ lam ω) (i : Fin 2) {z0 z1 E0 E1 st st1 gt : ℝ}
    (hrec : st1 = ρ * st + φ 0 * z0 + φ 1 * z1) :
    P i 0 * z0 + P i 1 * z1 = N i 0 * E0 + N i 1 * E1 + h i * st + k i * st1 + b i * gt ↔
      resM P N k φ ω i 0 * (z0 - ω 0 * st) + resM P N k φ ω i 1 * (z1 - ω 1 * st) =
        N i 0 * (E0 - ω 0 * st1) + N i 1 * (E1 - ω 1 * st1) + b i * gt := by
  obtain ⟨hW, hL⟩ := hD
  have hWi := hW i
  simp only [resM, Matrix.of_apply]
  constructor
  · intro H
    linear_combination H + (N i 0 * ω 0 + N i 1 * ω 1 + k i) * hrec - st * hWi -
      (N i 0 * ω 0 + N i 1 * ω 1 + k i) * st * hL
  · intro H
    linear_combination H - (N i 0 * ω 0 + N i 1 * ω 1 + k i) * hrec + st * hWi +
      (N i 0 * ω 0 + N i 1 * ω 1 + k i) * st * hL

omit 𝔼 in
/-- Woodford (2003), p. 277: solving `M X = N E + b g` for `X` by the adjugate (`det M ≠ 0`). -/
theorem solve2 {M : Matrix (Fin 2) (Fin 2) ℝ} (hd : det2 M ≠ 0) (N : Matrix (Fin 2) (Fin 2) ℝ)
    (b : Fin 2 → ℝ) {X0 X1 E0 E1 gt : ℝ} :
    (M 0 0 * X0 + M 0 1 * X1 = N 0 0 * E0 + N 0 1 * E1 + b 0 * gt ∧
      M 1 0 * X0 + M 1 1 * X1 = N 1 0 * E0 + N 1 1 * E1 + b 1 * gt) ↔
    (X0 = solveMN M N 0 0 * E0 + solveMN M N 0 1 * E1 + solvew M b 0 * gt ∧
      X1 = solveMN M N 1 0 * E0 + solveMN M N 1 1 * E1 + solvew M b 1 * gt) := by
  rw [rows_mn_iff hd]
  have e0 : solvew M b 0 * gt = M 1 1 / det2 M * (b 0 * gt) - M 0 1 / det2 M * (b 1 * gt) := by
    simp only [solvew, Matrix.cons_val_zero]; ring
  have e1 : solvew M b 1 * gt = M 0 0 / det2 M * (b 1 * gt) - M 1 0 / det2 M * (b 0 * gt) := by
    simp only [solvew, Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring
  rw [e0, e1]

/-- Woodford (2003), p. 277: the forward system `M ẑ_t = N E_t ẑ_{t+1} + b g_t` is equivalent to
`ẑ_t = G E_t ẑ_{t+1} + w g_t` with `G = M⁻¹N`, `w = M⁻¹b`. -/
theorem res_iff_solves {M : Matrix (Fin 2) (Fin 2) ℝ} (hd : det2 M ≠ 0)
    (N : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (g : ℕ → Ω → ℝ)
    (zh : ℕ → Fin 2 → Ω → ℝ) :
    (∀ t i, M i 0 • zh t 0 + M i 1 • zh t 1 = N i 0 • 𝔼.E t (zh (t + 1) 0) +
      N i 1 • 𝔼.E t (zh (t + 1) 1) + b i • g t) ↔
      𝔼.Solves (solveMN M N) (fun t i => solvew M b i • g t) zh := by
  constructor
  · intro H t i
    funext ω
    have h0 := congrFun (H t 0) ω
    have h1 := congrFun (H t 1) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1 ⊢
    obtain ⟨e0, e1⟩ := (solve2 hd N b).mp ⟨h0, h1⟩
    fin_cases i
    · exact e0
    · exact e1
  · intro H t i
    funext ω
    have h0 := congrFun (H t 0) ω
    have h1 := congrFun (H t 1) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1 ⊢
    obtain ⟨e0, e1⟩ := (solve2 hd N b).mpr ⟨h0, h1⟩
    fin_cases i
    · exact e0
    · exact e1

/-- Woodford (2003), p. 277: the path of the predetermined variable,
`s_0` given and `s_{t+1} = λ s_t + φ · F_t`. -/
noncomputable def sPath (lam : ℝ) (φ : Fin 2 → ℝ) (F : ℕ → Fin 2 → Ω → ℝ) (s0 : Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => s0
  | t + 1 => lam • sPath lam φ F s0 t + φ 0 • F t 0 + φ 1 • F t 1

/-- **Woodford (2003), p. 277 (inertial-rule solutions; uniqueness).** Under a decomposition
`(λ, ω)` with `det M ≠ 0` and `G = M⁻¹N` stable, every bounded adapted solution of the
one-predetermined-variable system satisfies `z_t = ω s_t + ∑_j Gʲ w E_t g_{t+j}` and
`s_{t+1} = λ s_t + φ · (z_t − ω s_t)`. -/
theorem predSys_formula {P N : Matrix (Fin 2) (Fin 2) ℝ} {h k b φ ω : Fin 2 → ℝ} {ρ lam : ℝ}
    (hD : Decomp P N h k φ ρ lam ω) (hd : det2 (resM P N k φ ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM P N k φ ω) N)) (det2 (solveMN (resM P N k φ ω) N)))
    {g : ℕ → Ω → ℝ} {Mg : ℝ} (hg : ∀ t ω, |g t ω| ≤ Mg) (hga : 𝔼.Adapted g)
    {z : ℕ → Fin 2 → Ω → ℝ} {s : ℕ → Ω → ℝ} (hsys : PredSys 𝔼 P N h k b φ ρ g z s)
    (hza : 𝔼.AdaptedVec z) (hsa : 𝔼.Adapted s) (hzb : BoundedVec z) (hsb : BoundedProc s) :
    (fun t i => z t i - ω i • s t) = fwdVec 𝔼 (solveMN (resM P N k φ ω) N)
      (solvew (resM P N k φ ω) b) g ∧
    ∀ t, s (t + 1) = lam • s t + φ 0 • (z t 0 - ω 0 • s t) + φ 1 • (z t 1 - ω 1 • s t) := by
  obtain ⟨hrow, hrec⟩ := hsys
  have hE1 : ∀ t, 𝔼.E t (s (t + 1)) = s (t + 1) := by
    intro t
    rw [hrec t]
    simp only [map_add, map_smul, hsa t, hza t 0, hza t 1]
  set zh : ℕ → Fin 2 → Ω → ℝ := fun t i => z t i - ω i • s t with hzh
  have hres : ∀ t i, resM P N k φ ω i 0 • zh t 0 + resM P N k φ ω i 1 • zh t 1 =
      N i 0 • 𝔼.E t (zh (t + 1) 0) + N i 1 • 𝔼.E t (zh (t + 1) 1) + b i • g t := by
    intro t i
    funext x
    have H := congrFun (hrow t i) x
    have R := congrFun (hrec t) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at H R
    simp only [hzh, map_sub, map_smul, hE1 t, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul]
    exact (row_iff_res hD i R).mp H
  have hzha : 𝔼.AdaptedVec zh := by
    intro t i
    simp only [hzh, map_sub, map_smul, hza t i, hsa t]
  have hzhb : BoundedVec zh := by
    obtain ⟨Mz, hMz⟩ := hzb
    obtain ⟨Ms, hMs⟩ := hsb
    refine ⟨Mz + (|ω 0| + |ω 1|) * Ms, fun t i x => ?_⟩
    simp only [hzh, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hMs0 : 0 ≤ Ms := (abs_nonneg _).trans (hMs t x)
    have hωi : |ω i| ≤ |ω 0| + |ω 1| := by
      fin_cases i <;> simp
    refine (abs_sub _ _).trans (add_le_add (hMz t i x) ?_)
    rw [abs_mul]
    exact mul_le_mul hωi (hMs t x) (abs_nonneg _) (by positivity)
  refine ⟨eq_fwdVec 𝔼 hG _ hg hga ((res_iff_solves 𝔼 hd N b g zh).mp hres) hzha hzhb,
    fun t => ?_⟩
  rw [hrec t, hD.2]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- **Woodford (2003), p. 277 (solution form with a predetermined variable).** Every bounded
adapted solution has `z_t = ω s_t + ∑_j ψ_j E_t g_{t+j}` with `ψ_j = Gʲ w` absolutely
summable: for the inertial rule this is
`π_t = π̄ + ω_π(î_{t−1} − ī_{t−1}) + ∑ ψ^π_j E_t(r̂ⁿ − ī + π̄)_{t+j}`. -/
theorem predSys_solution_form {P N : Matrix (Fin 2) (Fin 2) ℝ} {h k b φ ω : Fin 2 → ℝ}
    {ρ lam : ℝ} (hD : Decomp P N h k φ ρ lam ω) (hd : det2 (resM P N k φ ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM P N k φ ω) N)) (det2 (solveMN (resM P N k φ ω) N)))
    {g : ℕ → Ω → ℝ} {Mg : ℝ} (hg : ∀ t ω, |g t ω| ≤ Mg) (hga : 𝔼.Adapted g)
    {z : ℕ → Fin 2 → Ω → ℝ} {s : ℕ → Ω → ℝ} (hsys : PredSys 𝔼 P N h k b φ ρ g z s)
    (hza : 𝔼.AdaptedVec z) (hsa : 𝔼.Adapted s) (hzb : BoundedVec z) (hsb : BoundedProc s)
    (t : ℕ) (i : Fin 2) (x : Ω) :
    z t i x = ω i * s t x + ∑' j, coef (solveMN (resM P N k φ ω) N)
      (solvew (resM P N k φ ω) b) j i * 𝔼.E t (g (t + j)) x := by
  have h1 : z t i x - ω i * s t x = ∑' j, coef (solveMN (resM P N k φ ω) N)
      (solvew (resM P N k φ ω) b) j i * 𝔼.E t (g (t + j)) x :=
    congrFun (congrFun (congrFun (predSys_formula 𝔼 hD hd hG hg hga hsys hza hsa hzb hsb).1 t)
      i) x
  linarith

/-- **Woodford (2003), p. 277 (determinacy with one predetermined variable).** Under a
decomposition `(λ, ω)` with `|λ| < 1`, `det M ≠ 0` and `G = M⁻¹N` stable, for every bounded
adapted forcing `g` and every initial value `s_0` known at date 0 there is exactly one bounded
adapted solution `(z, s)` with `s_0` given. -/
theorem predSys_existsUnique {P N : Matrix (Fin 2) (Fin 2) ℝ} {h k b φ ω : Fin 2 → ℝ}
    {ρ lam : ℝ} (hD : Decomp P N h k φ ρ lam ω) (hl : |lam| < 1)
    (hd : det2 (resM P N k φ ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM P N k φ ω) N)) (det2 (solveMN (resM P N k φ ω) N)))
    {g : ℕ → Ω → ℝ} {Mg : ℝ} (hg : ∀ t ω, |g t ω| ≤ Mg) (hga : 𝔼.Adapted g)
    {s0 : Ω → ℝ} {B : ℝ} (hs0 : 𝔼.E 0 s0 = s0) (hs0b : ∀ x, |s0 x| ≤ B) :
    ∃! p : (ℕ → Fin 2 → Ω → ℝ) × (ℕ → Ω → ℝ), PredSys 𝔼 P N h k b φ ρ g p.1 p.2 ∧
      p.2 0 = s0 ∧ 𝔼.AdaptedVec p.1 ∧ 𝔼.Adapted p.2 ∧ BoundedVec p.1 ∧ BoundedProc p.2 := by
  set G := solveMN (resM P N k φ ω) N with hGdef
  set w := solvew (resM P N k φ ω) b with hwdef
  set F := fwdVec 𝔼 G w g with hFdef
  have hFs := fwdVec_solves 𝔼 hG w hg hga
  have hFa := fwdVec_adapted 𝔼 hG w hg
  obtain ⟨MF, hMF⟩ := fwdVec_bounded 𝔼 hG w hg
  rw [← hFdef] at hFs hFa hMF
  set sp := sPath lam φ F s0 with hspdef
  have hsp1 : ∀ t, sp (t + 1) = lam • sp t + φ 0 • F t 0 + φ 1 • F t 1 := fun t => rfl
  have hspa : 𝔼.Adapted sp := by
    intro t
    induction t with
    | zero => exact hs0
    | succ t ih =>
      rw [hsp1 t, map_add, map_add, map_smul, map_smul, map_smul,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hFa t 0),
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hFa t 1)]
  have hE1 : ∀ t, 𝔼.E t (sp (t + 1)) = sp (t + 1) := by
    intro t
    rw [hsp1 t]
    simp only [map_add, map_smul, hspa t, hFa t 0, hFa t 1]
  have hspb : BoundedProc sp := by
    refine ⟨max B ((|φ 0| + |φ 1|) * MF / (1 - |lam|)), fun t x => ?_⟩
    refine abs_rec_le hl (u := fun t => φ 0 * F t 0 x + φ 1 * F t 1 x) (x := fun t => sp t x)
      (fun t => ?_)
      (hs0b x) (fun t => ?_) t
    · have a0 := hMF t 0 x
      have a1 := hMF t 1 x
      calc |φ 0 * F t 0 x + φ 1 * F t 1 x| ≤ |φ 0| * |F t 0 x| + |φ 1| * |F t 1 x| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ |φ 0| * MF + |φ 1| * MF := by gcongr
        _ = (|φ 0| + |φ 1|) * MF := by ring
    · simp only [hsp1 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  set zp : ℕ → Fin 2 → Ω → ℝ := fun t i => ω i • sp t + F t i with hzpdef
  have hzpa : 𝔼.AdaptedVec zp := by
    intro t i
    simp only [hzpdef, map_add, map_smul, hspa t, hFa t i]
  have hzpb : BoundedVec zp := by
    obtain ⟨Ms, hMs⟩ := hspb
    refine ⟨(|ω 0| + |ω 1|) * Ms + MF, fun t i x => ?_⟩
    simp only [hzpdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hMs0 : 0 ≤ Ms := (abs_nonneg _).trans (hMs t x)
    have hωi : |ω i| ≤ |ω 0| + |ω 1| := by
      fin_cases i <;> simp
    refine (abs_add_le _ _).trans (add_le_add ?_ (hMF t i x))
    rw [abs_mul]
    exact mul_le_mul hωi (hMs t x) (abs_nonneg _) (by positivity)
  have hrec : ∀ t, sp (t + 1) = ρ • sp t + φ 0 • zp t 0 + φ 1 • zp t 1 := by
    intro t
    rw [hsp1 t, hD.2]
    funext x
    simp only [hzpdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hres := (res_iff_solves 𝔼 hd N b g F).mpr hFs
  have hsys : PredSys 𝔼 P N h k b φ ρ g zp sp := by
    refine ⟨fun t i => ?_, hrec⟩
    funext x
    have R := congrFun (hrec t) x
    have H := congrFun (hres t i) x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at R H ⊢
    refine (row_iff_res hD i R).mpr ?_
    have e0 : zp t 0 x - ω 0 * sp t x = F t 0 x := by simp [hzpdef]
    have e1 : zp t 1 x - ω 1 * sp t x = F t 1 x := by simp [hzpdef]
    have f0 : 𝔼.E t (zp (t + 1) 0) x - ω 0 * sp (t + 1) x = 𝔼.E t (F (t + 1) 0) x := by
      simp only [hzpdef, map_add, map_smul, hE1 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have f1 : 𝔼.E t (zp (t + 1) 1) x - ω 1 * sp (t + 1) x = 𝔼.E t (F (t + 1) 1) x := by
      simp only [hzpdef, map_add, map_smul, hE1 t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e0, e1, f0, f1]
    exact H
  refine ⟨(zp, sp), ⟨hsys, rfl, hzpa, hspa, hzpb, hspb⟩, ?_⟩
  rintro ⟨z', s'⟩ ⟨hsys', hs0', hza', hsa', hzb', hsb'⟩
  dsimp only at hsys' hs0' hza' hsa' hzb' hsb'
  obtain ⟨hF', hrec'⟩ := predSys_formula 𝔼 hD hd hG hg hga hsys' hza' hsa' hzb' hsb'
  have hzh : ∀ t i, z' t i - ω i • s' t = F t i := fun t i =>
    congrFun (congrFun hF' t) i
  have hs : s' = sp := by
    funext t
    induction t with
    | zero => exact hs0'
    | succ t ih =>
      rw [hrec' t, hsp1 t, hzh t 0, hzh t 1, ih]
  have hz : z' = zp := by
    funext t i
    have := hzh t i
    rw [hs] at this
    simp only [hzpdef]
    rw [← this]
    abel
  rw [hs, hz]

omit 𝔼 in
/-- Woodford (2003), Prop. C.1, p. 670 (the test used for the forward block): if
`0 < β < d` and `|T| < d + β`, then `(T/d, β/d)` satisfies Schur–Cohn. -/
theorem schurStable_of_bounds {β d T : ℝ} (hβ : 0 < β) (hd : β < d) (hT : |T| < d + β) :
    SchurStable (T / d) (β / d) := by
  have hd0 : 0 < d := by linarith
  refine ⟨?_, ?_⟩
  · rw [abs_div, abs_of_pos hβ, abs_of_pos hd0, div_lt_one hd0]
    exact hd
  · rw [abs_div, abs_of_pos hd0]
    have e : 1 + β / d = (d + β) / d := by field_simp
    rw [e, div_lt_div_iff_of_pos_right hd0]
    exact hT

/-! #### The inertial Taylor rule (2.8) -/

/-- Woodford (2003), (C.21), p. 678: `P` for the inertial rule (2.8)
(rows: Phillips curve, IS relation). -/
def inertP (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, -κ; 0, 1]

/-- Woodford (2003), (C.21), p. 678: `N` (coefficients of `E_t z_{t+1}`), shared by both
models with a predetermined variable. -/
def predN (β σ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![β, 0; σ, 1]

/-- Woodford (2003), (C.21), p. 678: the forcing vector `(0, σ)` of `r̂ⁿ − ī + π̄`. -/
def predB (σ : ℝ) : Fin 2 → ℝ := ![0, σ]

/-- Woodford (2003), (2.8), p. 255: the feedback `(φ_π, φ_x/4)` of the rule. -/
noncomputable def inertPhi (φπ φx : ℝ) : Fin 2 → ℝ := ![φπ, φx / 4]

/-- Woodford (2003), (C.21)–(C.23), pp. 678–679: `β` times the characteristic polynomial of the
3×3 matrix of (C.21), `C(λ) = (λ − ρ) Q(λ) + σ λ (κ φ_π + φ_x (1 − βλ)/4)` with
`Q(λ) = (1 − βλ)(1 − λ) − κσλ`. -/
noncomputable def inertCubic (β σ κ ρ φπ φx lam : ℝ) : ℝ :=
  (lam - ρ) * ((1 - β * lam) * (1 - lam) - κ * σ * lam) +
    σ * lam * (κ * φπ + φx * (1 - β * lam) / 4)

/-- Woodford (2003), p. 277: the coefficients `ω = (ω_π, ω_x)` of `î_{t−1} − ī_{t−1}` attached to
the stable root `λ`: `ω_π = −κσλ/Q(λ)`, `ω_x = −σλ(1 − βλ)/Q(λ)`. -/
noncomputable def inertOmega (β σ κ lam : ℝ) : Fin 2 → ℝ :=
  ![-(κ * σ * lam) / ((1 - β * lam) * (1 - lam) - κ * σ * lam),
    -(σ * lam * (1 - β * lam)) / ((1 - β * lam) * (1 - lam) - κ * σ * lam)]

omit 𝔼 in
/-- Woodford (2003), p. 277: for a root `λ` of the cubic with `Q(λ) ≠ 0`, `(λ, ω(λ))` is a
decomposition of the inertial-rule system. -/
theorem inert_decomp {β σ κ ρ φπ φx lam : ℝ} (hκ : κ ≠ 0)
    (hQ : (1 - β * lam) * (1 - lam) - κ * σ * lam ≠ 0)
    (hC : inertCubic β σ κ ρ φπ φx lam = 0) :
    Decomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam
      (inertOmega β σ κ lam) := by
  unfold inertCubic at hC
  unfold inertOmega
  set Q := (1 - β * lam) * (1 - lam) - κ * σ * lam with hQdef
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · simp [inertP, predN, a25]
      field_simp
      ring
    · simp [inertP, predN, a25]
      field_simp
      linear_combination (-(σ * lam)) * hQdef
  · simp only [inertPhi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    linear_combination 4 * hC - 4 * (lam - ρ) * hQdef

/-- Woodford (2003), p. 277 (the forward block of the inertial-rule system): `T`, the trace
numerator of `G = M⁻¹N`. -/
noncomputable def traceNum (M N : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  M 1 1 * N 0 0 - M 0 1 * N 1 0 + M 0 0 * N 1 1 - M 1 0 * N 0 1

omit 𝔼 in
/-- Woodford (2003), (C.22)–(C.23), pp. 678–679 (the identities behind the root count): for any
decomposition `(λ, ω)` of the inertial-rule system, with `d = det M` and `T` the trace numerator,
`λ d = ρ`, `(1 − λ)(d + β − T) = C(1)` and `(1 + λ)(d + β + T) = −C(−1)`. -/
theorem inert_identities {β σ κ ρ φπ φx lam : ℝ} {ω : Fin 2 → ℝ}
    (hD : Decomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω) :
    lam * det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) = ρ ∧
    (1 - lam) * (det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) + β -
      traceNum (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) (predN β σ)) =
      σ * κ * (φπ - (1 - ρ)) + σ * (1 - β) * φx / 4 ∧
    (1 + lam) * (det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) + β +
      traceNum (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) (predN β σ)) =
      (1 + ρ) * (2 * (1 + β) + κ * σ) + σ * κ * φπ + σ * φx * (1 + β) / 4 := by
  obtain ⟨hW, hL⟩ := hD
  have h1 := hW 0
  have h2 := hW 1
  simp only [inertP, predN, a25, inertPhi, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
    Pi.zero_apply] at h1 h2 hL
  simp only [det2, traceNum, resM, inertP, predN, a25, inertPhi, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']
  refine ⟨?_, ?_, ?_⟩
  · linear_combination hL + φπ * h1 + (φπ * κ + φx / 4) * h2
  · linear_combination (-(1 - β) * φx / 4 - κ * φπ) * h2 - (σ * φx / 4) * h1 + σ * κ * hL
  · linear_combination (2 * φπ - σ * φx / 4) * h1 + (κ * φπ + (1 + β) * φx / 4) * h2 +
      (2 + 2 * β + σ * κ) * hL

/-- Woodford (2003), eq. (2.9), p. 255: the Taylor principle for the inertial rule (2.8),
`φ_π + (1 − β) φ_x / (4κ) > 1 − ρ`. -/
def InertialTaylorPrinciple (β κ ρ φπ φx : ℝ) : Prop := 1 - ρ < φπ + (1 - β) * φx / (4 * κ)

omit 𝔼 in
/-- Woodford (2003), (C.22)–(C.24), pp. 678–679: for any decomposition `(λ, ω)` of the
inertial-rule system with `0 ≤ λ < 1` and `βλ < ρ` (or `λ = ρ = 0`), the Taylor principle (2.9)
makes the forward block `G = M⁻¹N` stable (both of its eigenvalues inside the unit circle,
i.e. the other two roots of the cubic outside). -/
theorem inert_forward_stable {β σ κ ρ φπ φx lam : ℝ} {ω : Fin 2 → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hTP : InertialTaylorPrinciple β κ ρ φπ φx)
    (hD : Decomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hβl : β * lam < ρ ∨ (lam = 0 ∧ ρ = 0)) :
    det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) ≠ 0 ∧
      SchurStable (tr2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω)
        (predN β σ))) (det2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ)
          (inertPhi φπ φx) ω) (predN β σ))) := by
  obtain ⟨I0, I1, I2⟩ := inert_identities hD
  set d := det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) with hd
  set T := traceNum (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) (predN β σ)
    with hT
  have hdβ : β < d := by
    rcases hβl with h | ⟨h0, -⟩
    · have hl : 0 < lam := by
        rcases eq_or_lt_of_le hl0 with h0 | h0
        · rw [← h0] at I0 h
          linarith
        · exact h0
      by_contra hc
      have : lam * d ≤ lam * β := mul_le_mul_of_nonneg_left (not_lt.mp hc) hl0
      linarith
    · obtain ⟨hW, -⟩ := hD
      have h1 := hW 0
      have h2 := hW 1
      simp only [inertP, predN, a25, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Pi.zero_apply,
        h0] at h1 h2
      have e1 : ω 1 = 0 := by linarith
      have e0 : ω 0 = 0 := by rw [e1] at h1; linarith
      have hd' : d = 1 + σ * φx / 4 + σ * κ * φπ := by
        simp only [hd, det2, resM, inertP, predN, a25, inertPhi, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Matrix.empty_val', e0, e1]
        ring
      have : 0 ≤ σ * φx / 4 + σ * κ * φπ := by positivity
      linarith
  have hC1 : 0 < σ * κ * (φπ - (1 - ρ)) + σ * (1 - β) * φx / 4 := by
    unfold InertialTaylorPrinciple at hTP
    have e : σ * κ * (φπ - (1 - ρ)) + σ * (1 - β) * φx / 4 =
        σ * κ * (φπ + (1 - β) * φx / (4 * κ) - (1 - ρ)) := by
      field_simp
      ring
    rw [e]
    have := sub_pos.mpr hTP
    positivity
  have hC2 : 0 < (1 + ρ) * (2 * (1 + β) + κ * σ) + σ * κ * φπ + σ * φx * (1 + β) / 4 := by
    positivity
  have hm : 0 < d + β - T := by
    by_contra hc
    have : (1 - lam) * (d + β - T) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hc)
    linarith
  have hp : 0 < d + β + T := by
    by_contra hc
    have : (1 + lam) * (d + β + T) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hc)
    linarith
  refine ⟨by linarith, ?_⟩
  have hN : det2 (predN β σ) = β := by
    simp [det2, predN]
  have htr : tr2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω)
      (predN β σ)) = T / d := tr2_solveMN _ _
  have hdet : det2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω)
      (predN β σ)) = β / d := by rw [det2_solveMN, hN]
  rw [htr, hdet]
  exact schurStable_of_bounds hβ0 hdβ (abs_lt.mpr ⟨by linarith, by linarith⟩)

omit 𝔼 in
/-- Woodford (2003), (C.22)–(C.23), p. 678: with `ρ = β r`, the cubic at `r` is
`r [(1 − β) Q(r) + σ(κ φ_π + φ_x (1 − βr)/4)]`. -/
theorem inertCubic_at (β σ κ φπ φx r : ℝ) :
    inertCubic β σ κ (β * r) φπ φx r = r * ((1 - β) * ((1 - β * r) * (1 - r) - κ * σ * r) +
      σ * (κ * φπ + φx * (1 - β * r) / 4)) := by
  unfold inertCubic
  ring

omit 𝔼 in
/-- Woodford (2003), (C.23) and the corner argument, p. 679 (here proved directly): if
`0 < ρ < β` and (2.9) holds, the cubic is positive at `λ = ρ/β`. -/
theorem inertCubic_pos_at {β σ κ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ0 : 0 < ρ) (hρβ : ρ < β) (hφx : 0 ≤ φx)
    (hTP : InertialTaylorPrinciple β κ ρ φπ φx) : 0 < inertCubic β σ κ ρ φπ φx (ρ / β) := by
  set r := ρ / β with hr
  have hρ : ρ = β * r := by rw [hr]; field_simp
  have hr0 : 0 < r := div_pos hρ0 hβ0
  have hr1 : r < 1 := by rw [hr, div_lt_one hβ0]; exact hρβ
  rw [hρ, inertCubic_at]
  refine mul_pos hr0 ?_
  unfold InertialTaylorPrinciple at hTP
  rw [hρ] at hTP
  have h1 : κ * (1 - β * r) < κ * φπ + (1 - β) * φx / 4 := by
    have := mul_lt_mul_of_pos_left hTP hκ
    have e : κ * (φπ + (1 - β) * φx / (4 * κ)) = κ * φπ + (1 - β) * φx / 4 := by
      field_simp
    linarith
  have hkey : (1 - β) * ((1 - β * r) * (1 - r) - κ * σ * r) +
      σ * (κ * φπ + φx * (1 - β * r) / 4) - ((1 - β) * (1 - β * r) * (1 - r) +
        σ * κ * (1 - r) + σ * φx * β * (1 - r) / 4) =
      σ * ((κ * φπ + (1 - β) * φx / 4) - κ * (1 - β * r)) := by ring
  have hpos : 0 < (1 - β) * (1 - β * r) * (1 - r) + σ * κ * (1 - r) +
      σ * φx * β * (1 - r) / 4 := by
    have a : 0 < 1 - β * r := by nlinarith
    have b : 0 < 1 - r := by linarith
    have c : 0 ≤ σ * φx * β * (1 - r) / 4 := by positivity
    have d : 0 < σ * κ * (1 - r) := by positivity
    have e : 0 ≤ (1 - β) * (1 - β * r) * (1 - r) := by
      have := mul_pos (mul_pos (by linarith : (0 : ℝ) < 1 - β) a) b
      linarith
    linarith
  have hσpos : 0 < σ * ((κ * φπ + (1 - β) * φx / 4) - κ * (1 - β * r)) :=
    mul_pos hσ (by linarith)
  linarith

omit 𝔼 in
/-- **Woodford (2003), Prop. 4.4 (sufficiency, the part needed for p. 277).** Under (2.8) with
`ρ, φ_π, φ_x ≥ 0`, not both `φ_π = φ_x = 0`, and the Taylor principle (2.9), the cubic has a root
`λ ∈ [0, 1)` with `βλ < ρ` (or `λ = ρ = 0`) and `Q(λ) ≠ 0`. -/
theorem inert_root_exists {β σ κ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hφ : 0 < φπ ∨ 0 < φx)
    (hTP : InertialTaylorPrinciple β κ ρ φπ φx) :
    ∃ lam, inertCubic β σ κ ρ φπ φx lam = 0 ∧ 0 ≤ lam ∧ lam < 1 ∧
      (β * lam < ρ ∨ (lam = 0 ∧ ρ = 0)) ∧
      (1 - β * lam) * (1 - lam) - κ * σ * lam ≠ 0 := by
  have hcont : Continuous (fun l => inertCubic β σ κ ρ φπ φx l) := by
    unfold inertCubic
    fun_prop
  have hC0 : inertCubic β σ κ ρ φπ φx 0 = -ρ := by
    unfold inertCubic
    ring
  have hQne : ∀ l, 0 < l → l < 1 → inertCubic β σ κ ρ φπ φx l = 0 →
      (1 - β * l) * (1 - l) - κ * σ * l ≠ 0 := by
    intro l hl0 hl1 hC hQ
    unfold inertCubic at hC
    rw [hQ, mul_zero, zero_add] at hC
    have hb : 0 < 1 - β * l := by nlinarith
    have : 0 < κ * φπ + φx * (1 - β * l) / 4 := by
      rcases hφ with h | h
      · have : 0 ≤ φx * (1 - β * l) / 4 := by positivity
        have : 0 < κ * φπ := mul_pos hκ h
        linarith
      · have : 0 ≤ κ * φπ := by positivity
        have : 0 < φx * (1 - β * l) / 4 := by positivity
        linarith
    have := mul_pos (mul_pos hσ hl0) this
    linarith
  rcases eq_or_lt_of_le hρ with h0 | hρ0
  · refine ⟨0, ?_, le_rfl, one_pos, Or.inr ⟨rfl, h0.symm⟩, by norm_num⟩
    rw [hC0, ← h0, neg_zero]
  · rcases lt_or_ge ρ β with hρβ | hρβ
    · have hb : 0 ≤ ρ / β := by positivity
      obtain ⟨l, ⟨hl0, hl1⟩, hl⟩ := intermediate_value_Ioo hb hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (inertCubic β σ κ ρ φπ φx 0)
          (inertCubic β σ κ ρ φπ φx (ρ / β)) from
          ⟨by rw [hC0]; linarith,
            inertCubic_pos_at hβ0 hβ1 hκ hσ hρ0 hρβ hφx hTP⟩)
      have hlt1 : l < 1 := lt_trans hl1 (by rw [div_lt_one hβ0]; exact hρβ)
      refine ⟨l, hl, hl0.le, hlt1, Or.inl ?_, hQne l hl0 hlt1 hl⟩
      rw [lt_div_iff₀ hβ0] at hl1
      linarith
    · have hC1 : 0 < inertCubic β σ κ ρ φπ φx 1 := by
        unfold inertCubic
        unfold InertialTaylorPrinciple at hTP
        have e : (1 - ρ) * ((1 - β * 1) * (1 - 1) - κ * σ * 1) +
            σ * 1 * (κ * φπ + φx * (1 - β * 1) / 4) =
            σ * κ * (φπ + (1 - β) * φx / (4 * κ) - (1 - ρ)) := by
          field_simp
          ring
        rw [e]
        have := sub_pos.mpr hTP
        positivity
      obtain ⟨l, ⟨hl0, hl1⟩, hl⟩ := intermediate_value_Ioo zero_le_one hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (inertCubic β σ κ ρ φπ φx 0)
          (inertCubic β σ κ ρ φπ φx 1) from ⟨by rw [hC0]; linarith, hC1⟩)
      refine ⟨l, hl, hl0.le, hl1, Or.inl ?_, hQne l hl0 hl1 hl⟩
      nlinarith

omit 𝔼 in
/-- **Woodford (2003), Prop. 4.4 and p. 277 (the decomposition).** Under (2.8) with
`ρ, φ_π, φ_x ≥ 0`, `(φ_π, φ_x) ≠ 0` and the Taylor principle (2.9), there is a stable root
`λ ∈ [0, 1)` and coefficients `ω = (ω_π, ω_x)` such that `(λ, ω)` decomposes the system and the
remaining forward block is stable: exactly the hypotheses of `predSys_existsUnique`. -/
theorem inert_BK {β σ κ ρ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (hφ : 0 < φπ ∨ 0 < φx)
    (hTP : InertialTaylorPrinciple β κ ρ φπ φx) :
    ∃ lam, 0 ≤ lam ∧ lam < 1 ∧
      Decomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam
        (inertOmega β σ κ lam) ∧
      det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx)
        (inertOmega β σ κ lam)) ≠ 0 ∧
      SchurStable (tr2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx)
        (inertOmega β σ κ lam)) (predN β σ))) (det2 (solveMN (resM (inertP κ) (predN β σ)
          (a25 σ) (inertPhi φπ φx) (inertOmega β σ κ lam)) (predN β σ))) := by
  obtain ⟨lam, hC, hl0, hl1, hβl, hQ⟩ := inert_root_exists hβ0 hβ1 hκ hσ hρ hφπ hφx hφ hTP
  have hD := inert_decomp hκ.ne' hQ hC
  exact ⟨lam, hl0, hl1, hD,
    inert_forward_stable hβ0 hβ1 hκ hσ hρ hφπ hφx hTP hD hl0 hl1 hβl⟩

/-- Woodford (2003), (2.8), p. 255, with `φ_π = φ_x = 0` (a remark on Prop. 4.4): the rule is
`ĩ_t = ρ ĩ_{t−1}`, so `ĩ_t = ρ^{t+1} ĩ_{−1}`; for `ρ > 1` and `ĩ_{−1} ≠ 0` there is no bounded
solution, so condition (2.9) (which holds whenever `ρ > 1`) is not sufficient without
`(φ_π, φ_x) ≠ 0`. -/
theorem inert_no_feedback_unbounded {ρ : ℝ} (hρ : 1 < ρ) {s : ℕ → Ω → ℝ} {x : Ω}
    (hrec : ∀ t, s (t + 1) = ρ • s t) (hs0 : s 0 x ≠ 0) : ¬ BoundedProc s := by
  rintro ⟨M, hM⟩
  have hpow : ∀ t, s t x = ρ ^ t * s 0 x := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hrec t, Pi.smul_apply, smul_eq_mul, ih, pow_succ]
      ring
  exact hs0 (pow_bounded_eq_zero (by rwa [abs_of_pos (by linarith)]) fun t => by
    rw [← hpow t]; exact hM t x)

/-- Woodford (2003), p. 287 (generic form): with no exogenous disturbance (`g = 0`), the unique
bounded solution of a system with one predetermined variable is purely deterministic given the
initial value, `s_t = λᵗ s_0`, `z_t = ω λᵗ s_0`, and dies out as `t → ∞`. -/
theorem predSys_zero_forcing {P N : Matrix (Fin 2) (Fin 2) ℝ} {h k b φ ω : Fin 2 → ℝ}
    {ρ lam : ℝ} (hD : Decomp P N h k φ ρ lam ω) (hl : |lam| < 1)
    (hd : det2 (resM P N k φ ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM P N k φ ω) N)) (det2 (solveMN (resM P N k φ ω) N)))
    {z : ℕ → Fin 2 → Ω → ℝ} {s : ℕ → Ω → ℝ} (hsys : PredSys 𝔼 P N h k b φ ρ 0 z s)
    (hza : 𝔼.AdaptedVec z) (hsa : 𝔼.Adapted s) (hzb : BoundedVec z) (hsb : BoundedProc s) :
    (∀ t, s t = lam ^ t • s 0) ∧ (∀ t i, z t i = (ω i * lam ^ t) • s 0) ∧
      ∀ i x, Tendsto (fun t => z t i x) atTop (𝓝 0) := by
  have hg : ∀ t x, |(0 : ℕ → Ω → ℝ) t x| ≤ 0 := by simp
  have hga : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  obtain ⟨hF, hrec⟩ := predSys_formula 𝔼 hD hd hG hg hga hsys hza hsa hzb hsb
  have hF0 : fwdVec 𝔼 (solveMN (resM P N k φ ω) N) (solvew (resM P N k φ ω) b) 0 = 0 := by
    funext t i x
    simp [fwdVec]
  rw [hF0] at hF
  have hzh : ∀ t i, z t i = ω i • s t := by
    intro t i
    have := congrFun (congrFun hF t) i
    simpa [sub_eq_zero] using this
  have hs : ∀ t, s t = lam ^ t • s 0 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hrec t, hzh t 0, hzh t 1, ih]
      simp [pow_succ, smul_smul, mul_comm]
  refine ⟨hs, fun t i => by rw [hzh t i, hs t, smul_smul], fun i x => ?_⟩
  have hlim : Tendsto (fun t : ℕ => ω i * lam ^ t * s 0 x) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hl).const_mul (ω i)
    simpa using this.mul_const (s 0 x)
  refine hlim.congr fun t => ?_
  rw [hzh t i, hs t]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (2.8), p. 255: the lagged policy gap `s_t = î_{t−1} − ī_{t−1}`, with
`s_0 = î_{−1} − ī_{−1}` given. -/
def lagGap (s0 : Ω → ℝ) (i ibar : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => s0
  | t + 1 => i t - ibar t

omit 𝔼 in
/-- Woodford (2003), (2.8), p. 255: `s_{t+1} = î_t − ī_t`. -/
theorem lagGap_succ (s0 : Ω → ℝ) (i ibar : ℕ → Ω → ℝ) (t : ℕ) :
    lagGap s0 i ibar (t + 1) = i t - ibar t := rfl

/-- Woodford (2003), eq. (2.8), p. 255: the inertial Taylor rule
`î_t − ī_t = ρ(î_{t−1} − ī_{t−1}) + φ_π(π_t − π̄) + φ_x(x_t − x̄)/4`. -/
def InertialRule (β κ ρ φπ φx πbar : ℝ) (s0 : Ω → ℝ) (π x i ibar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t - ibar t = ρ • lagGap s0 i ibar t + φπ • (π t - fun _ => πbar) +
    (φx / 4) • (x t - fun _ => xbar β κ πbar)

/-- Woodford (2003), (C.21), p. 678: the equilibrium conditions (1.12), (1.13), (2.8) are the
one-predetermined-variable system with `z = (π − π̄, x − x̄)`, `s_t = î_{t−1} − ī_{t−1}` and
forcing `r̂ⁿ − ī + π̄`. -/
theorem inertial_iff_predSys {β σ κ ρ φπ φx πbar : ℝ} (hκ : κ ≠ 0) {s0 : Ω → ℝ}
    {π x i rn ibar : ℕ → Ω → ℝ} :
    (NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ InertialRule β κ ρ φπ φx πbar s0 π x i ibar) ↔
      PredSys 𝔼 (inertP κ) (predN β σ) 0 (a25 σ) (predB σ) (inertPhi φπ φx) ρ
        (gapForcing πbar rn ibar) (gapVec β κ πbar π x) (lagGap s0 i ibar) := by
  have hx : κ * xbar β κ πbar = (1 - β) * πbar := by
    unfold xbar
    field_simp
  constructor
  · rintro ⟨has, his, hr⟩
    refine ⟨fun t j => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have ha := congrFun (has t) ω
      have hi := congrFun (his t) ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at ha hi
      fin_cases j
      · simp [gapVec, inertP, predN, a25, predB, lagGap_succ, gapForcing, 𝔼.const]
        linear_combination ha + hx
      · simp [gapVec, inertP, predN, a25, predB, lagGap_succ, gapForcing, 𝔼.const]
        linear_combination hi
    · have h := congrFun (hr t) ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
      simp [gapVec, inertPhi, lagGap_succ]
      linear_combination h
  · rintro ⟨hrow, hrec⟩
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_,
      fun t => funext fun ω => ?_⟩
    · have h0 := congrFun (hrow t 0) ω
      simp [gapVec, inertP, predN, a25, predB, lagGap_succ, gapForcing, 𝔼.const] at h0
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination h0 - hx
    · have h1 := congrFun (hrow t 1) ω
      simp [gapVec, inertP, predN, a25, predB, lagGap_succ, gapForcing, 𝔼.const] at h1
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination h1
    · have h := congrFun (hrec t) ω
      simp [gapVec, inertPhi, lagGap_succ] at h
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination h

/-- Woodford (2003), (2.8), p. 255: the lagged policy gap of an adapted equilibrium is adapted
(`ĩ_{t−1}` is known at date `t`). -/
theorem lagGap_adapted {s0 : Ω → ℝ} (hs0 : 𝔼.E 0 s0 = s0) {i ibar : ℕ → Ω → ℝ}
    (hia : 𝔼.Adapted i) (hiba : 𝔼.Adapted ibar) : 𝔼.Adapted (lagGap s0 i ibar) := by
  intro t
  cases t with
  | zero => exact hs0
  | succ t =>
    rw [lagGap_succ]
    exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (by rw [map_sub, hia t, hiba t])

/-- **Woodford (2003), p. 277 (the inertial rule (2.8): existence and uniqueness).** Given a
decomposition `(λ, ω)` of the inertial-rule system with `|λ| < 1` and a stable forward block
(supplied by `inert_BK` under (2.9)), for every bounded adapted gap `r̂ⁿ − ī + π̄` and every initial
`î_{−1} − ī_{−1}` known at date 0 there is exactly one equilibrium of (1.12), (1.13), (2.8) with
`π`, `x`, `î − ī` bounded and `π`, `x`, `î` adapted. -/
theorem inertial_equilibrium_existsUnique {β σ κ ρ φπ φx πbar lam : ℝ} {ω : Fin 2 → ℝ}
    (hκ : κ ≠ 0)
    (hD : Decomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω)
    (hl : |lam| < 1)
    (hd : det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx)
      ω) (predN β σ))) (det2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ)
        (inertPhi φπ φx) ω) (predN β σ))))
    {rn ibar : ℕ → Ω → ℝ} {Mg : ℝ} (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ Mg)
    (hga : 𝔼.Adapted (gapForcing πbar rn ibar)) (hiba : 𝔼.Adapted ibar)
    {s0 : Ω → ℝ} {B : ℝ} (hs0 : 𝔼.E 0 s0 = s0) (hs0b : ∀ x, |s0 x| ≤ B) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      NKPCurve 𝔼 β κ p.1 p.2.1 ∧ IS112 𝔼 σ p.2.1 p.2.2 p.1 rn ∧
        InertialRule β κ ρ φπ φx πbar s0 p.1 p.2.1 p.2.2 ibar ∧ 𝔼.Adapted p.1 ∧
          𝔼.Adapted p.2.1 ∧ 𝔼.Adapted p.2.2 ∧ BoundedProc p.1 ∧ BoundedProc p.2.1 ∧
            BoundedProc (p.2.2 - ibar) := by
  obtain ⟨⟨z, sv⟩, ⟨hsys, hs0', hza, hsa, hzb, hsb⟩, huniq⟩ :=
    predSys_existsUnique 𝔼 (b := predB σ) hD hl hd hG hg hga hs0 hs0b
  dsimp only at hsys hs0' hza hsa hzb hsb
  set π : ℕ → Ω → ℝ := fun t => z t 0 + fun _ => πbar with hπdef
  set x : ℕ → Ω → ℝ := fun t => z t 1 + fun _ => xbar β κ πbar with hxdef
  set i : ℕ → Ω → ℝ := fun t => sv (t + 1) + ibar t with hidef
  have hgap : gapVec β κ πbar π x = z := by
    funext t k
    fin_cases k <;> simp [gapVec, hπdef, hxdef]
  have hlag : lagGap s0 i ibar = sv := by
    funext t
    cases t with
    | zero => exact hs0'.symm
    | succ t =>
      rw [lagGap_succ]
      simp [hidef]
  have hE1 : ∀ t, 𝔼.E t (sv (t + 1)) = sv (t + 1) := by
    intro t
    rw [hsys.2 t]
    simp only [map_add, map_smul, hsa t, hza t 0, hza t 1]
  have heq := (inertial_iff_predSys 𝔼 (σ := σ) (ρ := ρ) (φπ := φπ) (φx := φx) hκ (s0 := s0)
    (π := π) (x := x) (i := i) (rn := rn) (ibar := ibar)).mpr (by rw [hgap, hlag]; exact hsys)
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨Ms, hMs⟩ := hsb
  refine ⟨(π, x, i), ⟨heq.1, heq.2.1, heq.2.2, fun t => ?_, fun t => ?_, fun t => ?_,
    ⟨Mz + |πbar|, fun t ω => ?_⟩, ⟨Mz + |xbar β κ πbar|, fun t ω => ?_⟩,
    ⟨Ms, fun t ω => ?_⟩⟩, ?_⟩
  · simp [hπdef, map_add, hza t 0, 𝔼.const]
  · simp [hxdef, map_add, hza t 1, 𝔼.const]
  · simp only [hidef, map_add, hE1 t, hiba t]
  · simp only [hπdef, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hMz t 0 ω) le_rfl)
  · simp only [hxdef, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hMz t 1 ω) le_rfl)
  · simp only [hidef, Pi.sub_apply, Pi.add_apply, add_sub_cancel_right]
    exact hMs (t + 1) ω
  · rintro ⟨π', x', i'⟩ ⟨has', his', hr', hπa', hxa', hia', hπb', hxb', hib'⟩
    dsimp only at has' his' hr' hπa' hxa' hia' hπb' hxb' hib'
    have hsys' := (inertial_iff_predSys 𝔼 hκ).mp ⟨has', his', hr'⟩
    have hlb : BoundedProc (lagGap s0 i' ibar) := by
      obtain ⟨Mi, hMi⟩ := hib'
      refine ⟨max B Mi, fun t ω => ?_⟩
      cases t with
      | zero => exact le_max_of_le_left (hs0b ω)
      | succ t =>
        rw [lagGap_succ]
        exact le_max_of_le_right (hMi t ω)
    have hu := huniq (gapVec β κ πbar π' x', lagGap s0 i' ibar)
      ⟨hsys', rfl, gapVec_adapted 𝔼 hπa' hxa', lagGap_adapted 𝔼 hs0 hia' hiba,
        gapVec_bounded hπb' hxb', hlb⟩
    simp only [Prod.mk.injEq] at hu
    obtain ⟨hz', hs'⟩ := hu
    have e1 : π' = π := by
      funext t ω
      have := congrFun (congrFun (congrFun hz' t) 0) ω
      simp only [gapVec, Matrix.cons_val_zero, Pi.sub_apply] at this
      simp only [hπdef, Pi.add_apply]
      linarith
    have e2 : x' = x := by
      funext t ω
      have := congrFun (congrFun (congrFun hz' t) 1) ω
      simp only [gapVec, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply] at this
      simp only [hxdef, Pi.add_apply]
      linarith
    have e3 : i' = i := by
      funext t ω
      have := congrFun (congrFun hs' (t + 1)) ω
      rw [lagGap_succ] at this
      simp only [Pi.sub_apply] at this
      simp only [hidef, Pi.add_apply]
      linarith
    rw [e1, e2, e3]

/-- **Woodford (2003), p. 277 (the form of the inertial-rule solution).** In the equilibrium of
(1.12), (1.13), (2.8): `π_t = π̄ + ω_π (î_{t−1} − ī_{t−1}) + ∑ ψ^π_j E_t g_{t+j}`,
`x_t = x̄ + ω_x (î_{t−1} − ī_{t−1}) + ∑ ψ^x_j E_t g_{t+j}` and
`î_t − ī_t = λ (î_{t−1} − ī_{t−1}) + ∑ (φ_π ψ^π_j + φ_x ψ^x_j/4) E_t g_{t+j}`,
`g = r̂ⁿ − ī + π̄`, with `ψ_j = Gʲ w` absolutely summable. -/
theorem inertial_equilibrium_formula {β σ κ ρ φπ φx πbar lam : ℝ} {ω : Fin 2 → ℝ}
    (hκ : κ ≠ 0)
    (hD : Decomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω)
    (hd : det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx)
      ω) (predN β σ))) (det2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ)
        (inertPhi φπ φx) ω) (predN β σ))))
    {rn ibar : ℕ → Ω → ℝ} {Mg : ℝ} (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ Mg)
    (hga : 𝔼.Adapted (gapForcing πbar rn ibar)) (hiba : 𝔼.Adapted ibar)
    {s0 : Ω → ℝ} {B : ℝ} (hs0 : 𝔼.E 0 s0 = s0) (hs0b : ∀ x, |s0 x| ≤ B)
    {π x i : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn)
    (hr : InertialRule β κ ρ φπ φx πbar s0 π x i ibar) (hπa : 𝔼.Adapted π)
    (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (hib : BoundedProc (i - ibar)) (t : ℕ) (y : Ω) :
    let ψ := coef (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω)
      (predN β σ)) (solvew (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω)
        (predB σ))
    π t y = πbar + ω 0 * lagGap s0 i ibar t y +
        ∑' j, ψ j 0 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y ∧
      x t y = xbar β κ πbar + ω 1 * lagGap s0 i ibar t y +
        ∑' j, ψ j 1 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y ∧
      i t y - ibar t y = lam * lagGap s0 i ibar t y +
        ∑' j, (φπ * ψ j 0 + φx / 4 * ψ j 1) * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y := by
  intro ψ
  have hsys := (inertial_iff_predSys 𝔼 hκ).mp ⟨has, his, hr⟩
  have hlb : BoundedProc (lagGap s0 i ibar) := by
    obtain ⟨Mi, hMi⟩ := hib
    refine ⟨max B Mi, fun t ω => ?_⟩
    cases t with
    | zero => exact le_max_of_le_left (hs0b ω)
    | succ t =>
      rw [lagGap_succ]
      exact le_max_of_le_right (hMi t ω)
  have hza := gapVec_adapted 𝔼 (β := β) (κ := κ) (πbar := πbar) hπa hxa
  have hsa := lagGap_adapted 𝔼 hs0 hia hiba
  have hzb := gapVec_bounded (β := β) (κ := κ) (πbar := πbar) hπb hxb
  have F0 := predSys_solution_form 𝔼 hD hd hG hg hga hsys hza hsa hzb hlb t 0 y
  have F1 := predSys_solution_form 𝔼 hD hd hG hg hga hsys hza hsa hzb hlb t 1 y
  have R := congrFun ((predSys_formula 𝔼 hD hd hG hg hga hsys hza hsa hzb hlb).2 t) y
  simp only [gapVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.sub_apply] at F0 F1
  have hπ : π t y = πbar + ω 0 * lagGap s0 i ibar t y +
      ∑' j, ψ j 0 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y := by linarith
  have hx : x t y = xbar β κ πbar + ω 1 * lagGap s0 i ibar t y +
      ∑' j, ψ j 1 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y := by linarith
  refine ⟨hπ, hx, ?_⟩
  rw [lagGap_succ] at R
  simp only [gapVec, inertPhi, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at R
  rw [R]
  have hX : ∀ j, |𝔼.E t (gapForcing πbar rn ibar (t + j)) y| ≤ Mg :=
    fun j => 𝔼.abs_E_le (hg _) t y
  have s0' := summable_coef_mul hG (solvew (resM (inertP κ) (predN β σ) (a25 σ)
    (inertPhi φπ φx) ω) (predB σ)) 0 hX
  have s1' := summable_coef_mul hG (solvew (resM (inertP κ) (predN β σ) (a25 σ)
    (inertPhi φπ φx) ω) (predB σ)) 1 hX
  have e : ∑' j, (φπ * ψ j 0 + φx / 4 * ψ j 1) * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y =
      φπ * ∑' j, ψ j 0 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y +
        φx / 4 * ∑' j, ψ j 1 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (s0'.mul_left φπ).tsum_add (s1'.mul_left (φx / 4))]
    refine tsum_congr fun j => ?_
    ring
  rw [e, hπ, hx]
  ring

/-- **Woodford (2003), p. 284 (shock equivalence under the inertial rule (2.8)).** Two economies
with the same gap `r̂ⁿ − ī` and the same initial `î_{−1} − ī_{−1}` have the same equilibrium
inflation, output gap and `î − ī`: a natural-rate disturbance `h` has the same effects as a
policy disturbance `−h`. -/
theorem inertial_shock_equivalence {β σ κ ρ φπ φx πbar lam : ℝ} {ω : Fin 2 → ℝ}
    (hκ : κ ≠ 0)
    (hD : Decomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω)
    (hd : det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx)
      ω) (predN β σ))) (det2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ)
        (inertPhi φπ φx) ω) (predN β σ))))
    {rn ibar rn' ibar' : ℕ → Ω → ℝ} {Mg : ℝ}
    (hgap : gapForcing πbar rn ibar = gapForcing πbar rn' ibar')
    (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ Mg)
    (hga : 𝔼.Adapted (gapForcing πbar rn ibar)) (hiba : 𝔼.Adapted ibar)
    (hiba' : 𝔼.Adapted ibar') {s0 : Ω → ℝ} {B : ℝ} (hs0 : 𝔼.E 0 s0 = s0)
    (hs0b : ∀ x, |s0 x| ≤ B) {π x i π' x' i' : ℕ → Ω → ℝ}
    (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn)
    (hr : InertialRule β κ ρ φπ φx πbar s0 π x i ibar) (hπa : 𝔼.Adapted π)
    (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (hib : BoundedProc (i - ibar))
    (has' : NKPCurve 𝔼 β κ π' x') (his' : IS112 𝔼 σ x' i' π' rn')
    (hr' : InertialRule β κ ρ φπ φx πbar s0 π' x' i' ibar') (hπa' : 𝔼.Adapted π')
    (hxa' : 𝔼.Adapted x') (hia' : 𝔼.Adapted i') (hπb' : BoundedProc π')
    (hxb' : BoundedProc x') (hib' : BoundedProc (i' - ibar')) :
    π = π' ∧ x = x' ∧ i - ibar = i' - ibar' := by
  have hg' : ∀ t ω, |gapForcing πbar rn' ibar' t ω| ≤ Mg := by rw [← hgap]; exact hg
  have hga' : 𝔼.Adapted (gapForcing πbar rn' ibar') := by rw [← hgap]; exact hga
  have F := fun t y => inertial_equilibrium_formula 𝔼 hκ hD hd hG hg hga hiba hs0 hs0b has his
    hr hπa hxa hia hπb hxb hib t y
  have F' := fun t y => inertial_equilibrium_formula 𝔼 hκ hD hd hG hg' hga' hiba' hs0 hs0b has'
    his' hr' hπa' hxa' hia' hπb' hxb' hib' t y
  simp only [← hgap] at F'
  have hlag : ∀ t y, lagGap s0 i ibar t y = lagGap s0 i' ibar' t y := by
    intro t
    induction t with
    | zero => intro y; rfl
    | succ t ih =>
      intro y
      rw [lagGap_succ, lagGap_succ, Pi.sub_apply, Pi.sub_apply, (F t y).2.2, (F' t y).2.2, ih y]
  refine ⟨funext fun t => funext fun y => ?_, funext fun t => funext fun y => ?_,
    funext fun t => funext fun y => ?_⟩
  · rw [(F t y).1, (F' t y).1, hlag t y]
  · rw [(F t y).2.1, (F' t y).2.1, hlag t y]
  · simp only [Pi.sub_apply]
    rw [(F t y).2.2, (F' t y).2.2, hlag t y]

/-! #### Inflation inertia (2.36)–(2.39) -/

/-- Woodford (2003), (2.36), p. 284: `P` for the inflation-inertia model under the Taylor rule
(1.14), with `z = (π − π̄, x − x̄)` and predetermined `s_t = π_{t−1} − π̄`. -/
noncomputable def inertiaP (β σ κ γ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + β * γ, -κ; σ * φπ, 1 + σ * φx / 4]

/-- Woodford (2003), (2.36), p. 284: the coefficient `γ` of `π_{t−1} − π̄` in the Phillips curve. -/
def inertiaH (γ : ℝ) : Fin 2 → ℝ := ![γ, 0]

/-- Woodford (2003), (2.36), p. 284: `s_{t+1} = π_t − π̄`, i.e. `φ = (1, 0)`. -/
def inertiaPhi : Fin 2 → ℝ := ![1, 0]

/-- Woodford (2003), (2.36)–(2.38), pp. 284–285: `β` times the characteristic polynomial,
`H(λ) = (λ − γ)(1 − βλ)(1 + σφ_x/4 − λ) − κσλ(λ − φ_π)`. -/
noncomputable def inertiaCubic (β σ κ γ φπ φx lam : ℝ) : ℝ :=
  (lam - γ) * (1 - β * lam) * (1 + σ * φx / 4 - lam) - κ * σ * lam * (lam - φπ)

/-- Woodford (2003), (2.37)–(2.38), p. 285: `ω_π = λ` (the stable root) and
`ω_x = (λ − γ)(1 − βλ)/κ`. -/
noncomputable def inertiaOmega (β κ γ lam : ℝ) : Fin 2 → ℝ :=
  ![lam, (lam - γ) * (1 - β * lam) / κ]

/-- Woodford (2003), (2.36), p. 284: the Taylor principle for the inflation-inertia model,
`φ_π + (1 − γ)(1 − β) φ_x / (4κ) > 1` (the long-run slope of (2.36) is `(1 − γ)(1 − β)/κ`). -/
def InertiaTaylorPrinciple (β κ γ φπ φx : ℝ) : Prop :=
  1 < φπ + (1 - γ) * (1 - β) * φx / (4 * κ)

omit 𝔼 in
/-- Woodford (2003), p. 285: a root of `H` gives a decomposition of the inertia model. -/
theorem inertia_decomp {β σ κ γ φπ φx lam : ℝ} (hκ : κ ≠ 0)
    (hH : inertiaCubic β σ κ γ φπ φx lam = 0) :
    Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam
      (inertiaOmega β κ γ lam) := by
  unfold inertiaCubic at hH
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i
    · simp [inertiaP, predN, inertiaH, inertiaOmega]
      field_simp
      ring
    · simp [inertiaP, predN, inertiaH, inertiaOmega]
      field_simp
      linear_combination 4 * hH
  · simp [inertiaPhi, inertiaOmega]

omit 𝔼 in
/-- Woodford (2003), pp. 284–285 (the identities behind the root count for (2.36)): for any
decomposition, `λ d = γ(1 + σφ_x/4)`, `(1 − λ)(d + β − T) = H(1)`,
`(1 + λ)(d + β + T) = −H(−1)`. -/
theorem inertia_identities {β σ κ γ φπ φx lam : ℝ} {ω : Fin 2 → ℝ}
    (hD : Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam ω) :
    lam * det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) =
        γ * (1 + σ * φx / 4) ∧
    (1 - lam) * (det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) + β -
      traceNum (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) (predN β σ)) =
      (1 - γ) * (1 - β) * (σ * φx / 4) - κ * σ * (1 - φπ) ∧
    (1 + lam) * (det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) + β +
      traceNum (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) (predN β σ)) =
      (1 + γ) * (1 + β) * (2 + σ * φx / 4) + κ * σ * (1 + φπ) := by
  obtain ⟨hW, hL⟩ := hD
  have h1 := hW 0
  have h2 := hW 1
  simp only [inertiaPhi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    at hL
  have hω : ω 0 = lam := by linarith
  simp only [inertiaP, predN, inertiaH, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
    Pi.zero_apply, hω] at h1 h2
  simp only [det2, traceNum, resM, inertiaP, predN, inertiaPhi, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val', Pi.zero_apply, hω]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 + σ * φx / 4) * h1 + κ * h2
  · linear_combination (-(σ * φx / 4)) * h1 - κ * h2
  · linear_combination (2 + σ * φx / 4) * h1 + κ * h2

omit 𝔼 in
/-- Woodford (2003), (2.36), p. 284: for `κ > 0`, the inertia Taylor principle reads
`κσ(1 − φ_π) < (1 − γ)(1 − β) σφ_x/4`, i.e. `H(1) > 0`. -/
theorem inertia_H1_pos {β σ κ γ φπ φx : ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hTP : InertiaTaylorPrinciple β κ γ φπ φx) :
    0 < (1 - γ) * (1 - β) * (σ * φx / 4) - κ * σ * (1 - φπ) := by
  unfold InertiaTaylorPrinciple at hTP
  have e : (1 - γ) * (1 - β) * (σ * φx / 4) - κ * σ * (1 - φπ) =
      σ * κ * (φπ + (1 - γ) * (1 - β) * φx / (4 * κ) - 1) := by
    field_simp
    ring
  rw [e]
  have := sub_pos.mpr hTP
  positivity

omit 𝔼 in
/-- Woodford (2003), pp. 284–285: for any decomposition of the inertia model with `0 ≤ λ < 1` and
`βλ < γ(1 + σφ_x/4)` (or `λ = γ = 0`), the inertia Taylor principle makes the forward block
stable. -/
theorem inertia_forward_stable {β σ κ γ φπ φx lam : ℝ} {ω : Fin 2 → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hγ : 0 ≤ γ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hTP : InertiaTaylorPrinciple β κ γ φπ φx)
    (hD : Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam ω)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hβl : β * lam < γ * (1 + σ * φx / 4) ∨ (lam = 0 ∧ γ = 0)) :
    det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) ≠ 0 ∧
      SchurStable (tr2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
        (predN β σ))) (det2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0
          inertiaPhi ω) (predN β σ))) := by
  obtain ⟨I0, I1, I2⟩ := inertia_identities hD
  set d := det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) with hd
  set T := traceNum (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) (predN β σ)
    with hT
  have hy : 0 ≤ σ * φx / 4 := by positivity
  have hdβ : β < d := by
    rcases hβl with h | ⟨h0, hγ0⟩
    · have hl : 0 < lam := by
        rcases eq_or_lt_of_le hl0 with h0 | h0
        · rw [← h0] at I0 h
          have : γ * (1 + σ * φx / 4) = 0 := by linarith
          linarith
        · exact h0
      by_contra hc
      have : lam * d ≤ lam * β := mul_le_mul_of_nonneg_left (not_lt.mp hc) hl0
      linarith
    · obtain ⟨hW, hL⟩ := hD
      have h1 := hW 0
      simp only [inertiaPhi, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hL
      have e0 : ω 0 = 0 := by linarith
      simp only [inertiaP, predN, inertiaH, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
        Pi.zero_apply, e0, h0, hγ0] at h1
      have e1 : ω 1 = 0 := by
        have : κ * ω 1 = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h hκ.ne'
        · exact h
      have hd' : d = 1 + σ * φx / 4 + κ * σ * φπ := by
        simp only [hd, det2, resM, inertiaP, predN, inertiaPhi, Matrix.of_apply,
          Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Matrix.empty_val', Pi.zero_apply, e0, e1, hγ0]
        ring
      have : 0 ≤ κ * σ * φπ := by positivity
      linarith
  have hC1 := inertia_H1_pos hκ hσ hTP
  have hC2 : 0 < (1 + γ) * (1 + β) * (2 + σ * φx / 4) + κ * σ * (1 + φπ) := by positivity
  have hm : 0 < d + β - T := by
    by_contra hc
    have : (1 - lam) * (d + β - T) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hc)
    linarith
  have hp : 0 < d + β + T := by
    by_contra hc
    have : (1 + lam) * (d + β + T) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (not_lt.mp hc)
    linarith
  refine ⟨by linarith, ?_⟩
  have hN : det2 (predN β σ) = β := by
    simp [det2, predN]
  have htr : tr2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
      (predN β σ)) = T / d := tr2_solveMN _ _
  have hdet : det2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
      (predN β σ)) = β / d := by rw [det2_solveMN, hN]
  rw [htr, hdet]
  exact schurStable_of_bounds hβ0 hdβ (abs_lt.mpr ⟨by linarith, by linarith⟩)

omit 𝔼 in
/-- Woodford (2003), pp. 284–285 (an auxiliary inequality, new): for `0 ≤ u ≤ β < 1`, `y ≥ 0`,
`(1 + y − β)(1 − u)(1 + y − u/β) ≥ (1 + y − u)(1 − β) y`, with equality at `u = β`. -/
theorem inertia_aux_ineq {β y u : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 ≤ y) (hu : u ≤ β) :
    (1 + y - u) * (1 - β) * y ≤ (1 + y - β) * (1 - u) * (1 + y - u / β) := by
  have e : (1 + y - β) * (1 - u) * (1 + y - u / β) - (1 + y - u) * (1 - β) * y =
      (β - u) * (y ^ 2 + (1 + y - β) * (1 - β) / β) + (1 + y - β) / β * (β - u) ^ 2 := by
    field_simp
    ring
  have h1 : 0 ≤ (β - u) * (y ^ 2 + (1 + y - β) * (1 - β) / β) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ (1 + y - β) * (1 - β) / β := by
      apply div_nonneg _ hβ0.le
      exact mul_nonneg (by linarith) (by linarith)
    positivity
  have h2 : 0 ≤ (1 + y - β) / β * (β - u) ^ 2 := by
    apply mul_nonneg _ (sq_nonneg _)
    exact div_nonneg (by linarith) hβ0.le
  linarith

omit 𝔼 in
/-- Woodford (2003), pp. 284–285 (new): if `0 < γ ≤ 1`, `u = γ(1 + σφ_x/4) < β` and the inertia
Taylor principle holds, `H(u/β) > 0`. -/
theorem inertiaCubic_pos_at {β σ κ γ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hγ0 : 0 < γ) (hφx : 0 ≤ φx) (hu : γ * (1 + σ * φx / 4) < β)
    (hTP : InertiaTaylorPrinciple β κ γ φπ φx) :
    0 < inertiaCubic β σ κ γ φπ φx (γ * (1 + σ * φx / 4) / β) := by
  set y := σ * φx / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  set u := γ * (1 + y) with hudef
  set r := u / β with hr
  have hβr : β * r = u := by rw [hr]; field_simp
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one hβ0]; exact hu
  have hrγ : r - γ = γ * (1 + y - β) / β := by
    rw [hr, hudef]; field_simp
  have hA : 0 < (r - γ) * (1 - β * r) * (1 + y - r) := by
    rw [hrγ, hβr]
    have : 0 < 1 + y - β := by linarith
    have : 0 < 1 - u := by linarith
    have : 0 < 1 + y - r := by linarith
    positivity
  unfold inertiaCubic
  rw [← hy]
  rcases le_or_gt r φπ with hle | hlt
  · have : 0 ≤ κ * σ * r * (φπ - r) := by
      have : 0 ≤ φπ - r := by linarith
      positivity
    nlinarith
  · have hTP' : κ * σ * (1 - φπ) < (1 - γ) * (1 - β) * y := by
      have := inertia_H1_pos (β := β) (γ := γ) (φπ := φπ) (φx := φx) hκ hσ hTP
      rw [← hy] at this
      linarith
    have hB : κ * σ * r * (r - φπ) < r * ((1 - γ) * (1 - β) * y) := by
      have h1 : κ * σ * (r - φπ) < κ * σ * (1 - φπ) := by
        have := mul_pos hκ hσ
        nlinarith
      have := mul_lt_mul_of_pos_left (h1.trans hTP') hr0
      linarith
    have hineq := inertia_aux_ineq hβ0 hβ1 hy0 hu.le
    have hkey : r * ((1 - γ) * (1 - β) * y) =
        γ / β * ((1 + y - u) * (1 - β) * y) := by
      rw [hr, hudef]
      field_simp
    have hkey2 : (r - γ) * (1 - β * r) * (1 + y - r) =
        γ / β * ((1 + y - β) * (1 - u) * (1 + y - u / β)) := by
      rw [hrγ, hβr, hr]
      field_simp
    have hg : 0 < γ / β := div_pos hγ0 hβ0
    have := mul_le_mul_of_nonneg_left hineq hg.le
    linarith

omit 𝔼 in
/-- Woodford (2003), pp. 284–285 (the root needed for (2.37)–(2.39), new): for `0 ≤ γ ≤ 1` and
the inertia Taylor principle, `H` has a root `λ ∈ [0, 1)` with `βλ < γ(1 + σφ_x/4)` (or
`λ = γ = 0`). -/
theorem inertia_root_exists {β σ κ γ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hγ0 : 0 ≤ γ) (hφx : 0 ≤ φx) (hTP : InertiaTaylorPrinciple β κ γ φπ φx) :
    ∃ lam, inertiaCubic β σ κ γ φπ φx lam = 0 ∧ 0 ≤ lam ∧ lam < 1 ∧
      (β * lam < γ * (1 + σ * φx / 4) ∨ (lam = 0 ∧ γ = 0)) := by
  have hcont : Continuous (fun l => inertiaCubic β σ κ γ φπ φx l) := by
    unfold inertiaCubic
    fun_prop
  have hy : 0 ≤ σ * φx / 4 := by positivity
  have hH0 : inertiaCubic β σ κ γ φπ φx 0 = -(γ * (1 + σ * φx / 4)) := by
    unfold inertiaCubic
    ring
  rcases eq_or_lt_of_le hγ0 with h0 | hγ
  · refine ⟨0, ?_, le_rfl, one_pos, Or.inr ⟨rfl, h0.symm⟩⟩
    rw [hH0, ← h0]
    ring
  · have hH0neg : inertiaCubic β σ κ γ φπ φx 0 < 0 := by
      rw [hH0]
      have : 0 < γ * (1 + σ * φx / 4) := by positivity
      linarith
    rcases lt_or_ge (γ * (1 + σ * φx / 4)) β with hu | hu
    · have hb : 0 ≤ γ * (1 + σ * φx / 4) / β := by positivity
      obtain ⟨l, ⟨hl0, hl1⟩, hl⟩ := intermediate_value_Ioo hb hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (inertiaCubic β σ κ γ φπ φx 0)
          (inertiaCubic β σ κ γ φπ φx (γ * (1 + σ * φx / 4) / β)) from
          ⟨hH0neg, inertiaCubic_pos_at hβ0 hβ1 hκ hσ hγ hφx hu hTP⟩)
      have hlt1 : l < 1 := lt_trans hl1 (by rw [div_lt_one hβ0]; exact hu)
      refine ⟨l, hl, hl0.le, hlt1, Or.inl ?_⟩
      rw [lt_div_iff₀ hβ0] at hl1
      linarith
    · have hH1 : 0 < inertiaCubic β σ κ γ φπ φx 1 := by
        have := inertia_H1_pos (β := β) (γ := γ) (φπ := φπ) (φx := φx) hκ hσ hTP
        unfold inertiaCubic
        linarith
      obtain ⟨l, ⟨hl0, hl1⟩, hl⟩ := intermediate_value_Ioo zero_le_one hcont.continuousOn
        (show (0 : ℝ) ∈ Set.Ioo (inertiaCubic β σ κ γ φπ φx 0)
          (inertiaCubic β σ κ γ φπ φx 1) from ⟨hH0neg, hH1⟩)
      refine ⟨l, hl, hl0.le, hl1, Or.inl ?_⟩
      nlinarith

omit 𝔼 in
/-- **Woodford (2003), pp. 284–285 (determinacy of the inertia model, the hypotheses of
`predSys_existsUnique`).** Under (1.12), (2.36), (1.14) with `0 ≤ γ ≤ 1` (indeed `γ ≥ 0`),
`φ_π, φ_x ≥ 0` and the inertia Taylor principle, there is a stable root `λ ∈ [0, 1)` with
decomposition `ω = (λ, (λ − γ)(1 − βλ)/κ)` and a stable forward block. -/
theorem inertia_BK {β σ κ γ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hγ0 : 0 ≤ γ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hTP : InertiaTaylorPrinciple β κ γ φπ φx) :
    ∃ lam, 0 ≤ lam ∧ lam < 1 ∧ inertiaCubic β σ κ γ φπ φx lam = 0 ∧
      Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam
        (inertiaOmega β κ γ lam) ∧
      det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi
        (inertiaOmega β κ γ lam)) ≠ 0 ∧
      SchurStable (tr2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi
        (inertiaOmega β κ γ lam)) (predN β σ))) (det2 (solveMN (resM (inertiaP β σ κ γ φπ φx)
          (predN β σ) 0 inertiaPhi (inertiaOmega β κ γ lam)) (predN β σ))) := by
  obtain ⟨lam, hH, hl0, hl1, hβl⟩ := inertia_root_exists hβ0 hβ1 hκ hσ hγ0 hφx hTP
  have hD := inertia_decomp hκ.ne' hH
  exact ⟨lam, hl0, hl1, hH, hD,
    inertia_forward_stable hβ0 hβ1 hκ hσ hγ0 hφπ hφx hTP hD hl0 hl1 hβl⟩

omit 𝔼 in
/-- Woodford (2003), p. 277 (the coefficients `ω` are well defined): two decompositions with
`|λ| < 1`, `det M ≠ 0` and a stable forward block coincide. Hence `ω_π`, `ω_x` (and the stable root
`λ`) are determined by the model, not by the choice of decomposition. -/
theorem decomp_unique {P N : Matrix (Fin 2) (Fin 2) ℝ} {h k b φ ω ω' : Fin 2 → ℝ}
    {ρ lam lam' : ℝ} (hD : Decomp P N h k φ ρ lam ω) (hl : |lam| < 1)
    (hd : det2 (resM P N k φ ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM P N k φ ω) N)) (det2 (solveMN (resM P N k φ ω) N)))
    (hD' : Decomp P N h k φ ρ lam' ω') (hl' : |lam'| < 1)
    (hd' : det2 (resM P N k φ ω') ≠ 0)
    (hG' : SchurStable (tr2 (solveMN (resM P N k φ ω') N))
      (det2 (solveMN (resM P N k φ ω') N))) :
    lam = lam' ∧ ω = ω' := by
  have hg : ∀ t (x : Unit), |(0 : ℕ → Unit → ℝ) t x| ≤ 0 := by simp
  have hga : perfectForesight.Adapted (0 : ℕ → Unit → ℝ) := fun _ => rfl
  obtain ⟨⟨z, sv⟩, ⟨hsys, hs0, hza, hsa, hzb, hsb⟩, -⟩ :=
    predSys_existsUnique perfectForesight (b := b) hD hl hd hG hg hga (s0 := fun _ => 1)
      (B := 1) rfl (fun _ => by simp)
  dsimp only at hsys hs0 hza hsa hzb hsb
  obtain ⟨hs1, hz1, -⟩ := predSys_zero_forcing perfectForesight hD hl hd hG hsys hza hsa hzb hsb
  obtain ⟨hs2, hz2, -⟩ :=
    predSys_zero_forcing perfectForesight hD' hl' hd' hG' hsys hza hsa hzb hsb
  rw [hs0] at hs1 hs2 hz1 hz2
  refine ⟨?_, funext fun i => ?_⟩
  · have := (congrFun (hs1 1) ()).symm.trans (congrFun (hs2 1) ())
    simpa using this
  · have := (congrFun (hz1 0 i) ()).symm.trans (congrFun (hz2 0 i) ())
    simpa using this

/-- Woodford (2003), (2.36), p. 284: lagged inflation `π_{t−1}`, with `π_{−1}` given. -/
def lagPi (p0 : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => p0
  | t + 1 => π t

omit 𝔼 in
/-- Woodford (2003), (2.36), p. 284: `π_{(t+1)−1} = π_t`. -/
theorem lagPi_succ (p0 : Ω → ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) : lagPi p0 π (t + 1) = π t := rfl

/-- Woodford (2003), (2.36), p. 284: the steady-state output gap with inflation inertia,
`x̄ = (1 − γ)(1 − β) π̄ / κ`. -/
noncomputable def xbarG (β κ γ πbar : ℝ) : ℝ := (1 - γ) * (1 - β) * πbar / κ

/-- Woodford (2003), eq. (2.36), p. 284: the Phillips curve with indexation,
`π_t − γ π_{t−1} = κ x_t + β E_t[π_{t+1} − γ π_t]`. -/
def ASInertia (β κ γ : ℝ) (p0 : Ω → ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t - γ • lagPi p0 π t = κ • x t + β • 𝔼.E t (π (t + 1) - γ • π t)

/-- Woodford (2003), eq. (1.14), p. 246, with the steady-state gap `x̄` of (2.36). -/
def TaylorRuleG (β κ γ φπ φx πbar : ℝ) (π x i ibar : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = ibar t + φπ • (π t - fun _ => πbar) + (φx / 4) • (x t - fun _ => xbarG β κ γ πbar)

/-- Woodford (2003), pp. 284–285: the gap vector `(π − π̄, x − x̄)` of the inertia model. -/
noncomputable def gapVecG (β κ γ πbar : ℝ) (π x : ℕ → Ω → ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![π t - fun _ => πbar, x t - fun _ => xbarG β κ γ πbar]

/-- Woodford (2003), pp. 284–285: under (1.14), the equilibrium conditions (1.12), (2.36) are the
one-predetermined-variable system with `z = (π − π̄, x − x̄)` and `s_t = π_{t−1} − π̄`. -/
theorem inertia_iff_predSys {β σ κ γ φπ φx πbar : ℝ} (hκ : κ ≠ 0) {p0 : Ω → ℝ}
    {π x i rn ibar : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π)
    (hrule : TaylorRuleG β κ γ φπ φx πbar π x i ibar) :
    (ASInertia 𝔼 β κ γ p0 π x ∧ IS112 𝔼 σ x i π rn) ↔
      PredSys 𝔼 (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 (predB σ) inertiaPhi 0
        (gapForcing πbar rn ibar) (gapVecG β κ γ πbar π x)
        (fun t => lagPi p0 π t - fun _ => πbar) := by
  have hx : κ * xbarG β κ γ πbar = (1 - γ) * (1 - β) * πbar := by
    unfold xbarG
    field_simp
  have hrec : ∀ t, (fun t => lagPi p0 π t - fun _ => πbar) (t + 1) =
      (0 : ℝ) • (fun t => lagPi p0 π t - fun _ => πbar) t +
        inertiaPhi 0 • gapVecG β κ γ πbar π x t 0 + inertiaPhi 1 • gapVecG β κ γ πbar π x t 1 := by
    intro t
    simp [inertiaPhi, gapVecG, lagPi_succ]
  constructor
  · rintro ⟨has, his⟩
    refine ⟨fun t j => funext fun ω => ?_, hrec⟩
    have ha := congrFun (has t) ω
    have hi := congrFun (his t) ω
    have hr := congrFun (hrule t) ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_sub, map_smul,
      hπa t] at ha hi hr
    fin_cases j
    · simp [gapVecG, inertiaP, predN, inertiaH, predB, gapForcing, 𝔼.const]
      linear_combination ha + hx
    · simp [gapVecG, inertiaP, predN, inertiaH, predB, gapForcing, 𝔼.const]
      linear_combination hi - σ * hr
  · rintro ⟨hrow, -⟩
    refine ⟨fun t => funext fun ω => ?_, fun t => funext fun ω => ?_⟩
    · have h0 := congrFun (hrow t 0) ω
      simp [gapVecG, inertiaP, predN, inertiaH, predB, gapForcing, 𝔼.const] at h0
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_sub, map_smul,
        hπa t]
      linear_combination h0 - hx
    · have h1 := congrFun (hrow t 1) ω
      have hr := congrFun (hrule t) ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hr
      simp [gapVecG, inertiaP, predN, inertiaH, predB, gapForcing, 𝔼.const] at h1
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      linear_combination h1 + σ * hr

/-- Woodford (2003), (2.36), p. 284: the lagged inflation gap of an adapted path is adapted. -/
theorem lagPiGap_adapted {p0 : Ω → ℝ} (hp0 : 𝔼.E 0 p0 = p0) {π : ℕ → Ω → ℝ} (πbar : ℝ)
    (hπa : 𝔼.Adapted π) : 𝔼.Adapted (fun t => lagPi p0 π t - fun _ => πbar) := by
  intro t
  cases t with
  | zero => simp [lagPi, map_sub, hp0, 𝔼.const]
  | succ t =>
    simp only [lagPi_succ]
    exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (by rw [map_sub, hπa t, 𝔼.const])

omit 𝔼 in
/-- Woodford (2003), (2.36), p. 284: the lagged inflation gap of a bounded path is bounded. -/
theorem lagPiGap_bounded {p0 : Ω → ℝ} {B : ℝ} (hp0b : ∀ x, |p0 x| ≤ B) {π : ℕ → Ω → ℝ}
    (πbar : ℝ) (hπb : BoundedProc π) :
    BoundedProc (fun t => lagPi p0 π t - fun _ => πbar) := by
  obtain ⟨M, hM⟩ := hπb
  refine ⟨max B M + |πbar|, fun t ω => ?_⟩
  simp only [Pi.sub_apply]
  refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
  cases t with
  | zero => exact le_max_of_le_left (hp0b ω)
  | succ t => exact le_max_of_le_right (hM t ω)

/-- **Woodford (2003), pp. 284–285 ((2.36)–(2.39): existence and uniqueness).** Given a
decomposition of the inflation-inertia model with `|λ| < 1` and a stable forward block (supplied
by `inertia_BK`), for every bounded adapted gap `r̂ⁿ − ī + π̄` and every `π_{−1}` known at date 0,
there is exactly one equilibrium of (1.12), (2.36), (1.14) with `π, x` bounded and `π, x, î`
adapted. -/
theorem inertia_equilibrium_existsUnique {β σ κ γ φπ φx πbar lam : ℝ} {ω : Fin 2 → ℝ}
    (hκ : κ ≠ 0)
    (hD : Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam ω)
    (hl : |lam| < 1)
    (hd : det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
      (predN β σ))) (det2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
        (predN β σ))))
    {rn ibar : ℕ → Ω → ℝ} {Mg : ℝ} (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ Mg)
    (hga : 𝔼.Adapted (gapForcing πbar rn ibar)) (hiba : 𝔼.Adapted ibar)
    {p0 : Ω → ℝ} {B : ℝ} (hp0 : 𝔼.E 0 p0 = p0) (hp0b : ∀ x, |p0 x| ≤ B) :
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      ASInertia 𝔼 β κ γ p0 q.1 q.2.1 ∧ IS112 𝔼 σ q.2.1 q.2.2 q.1 rn ∧
        TaylorRuleG β κ γ φπ φx πbar q.1 q.2.1 q.2.2 ibar ∧ 𝔼.Adapted q.1 ∧
          𝔼.Adapted q.2.1 ∧ 𝔼.Adapted q.2.2 ∧ BoundedProc q.1 ∧ BoundedProc q.2.1 := by
  have hs0 : 𝔼.E 0 (p0 - fun _ => πbar) = p0 - fun _ => πbar := by
    rw [map_sub, hp0, 𝔼.const]
  have hs0b : ∀ x, |(p0 - fun _ => πbar : Ω → ℝ) x| ≤ B + |πbar| := fun x =>
    (abs_sub _ _).trans (add_le_add (hp0b x) le_rfl)
  obtain ⟨⟨z, sv⟩, ⟨hsys, hs0', hza, hsa, hzb, hsb⟩, huniq⟩ :=
    predSys_existsUnique 𝔼 (b := predB σ) hD hl hd hG hg hga hs0 hs0b
  dsimp only at hsys hs0' hza hsa hzb hsb
  set π : ℕ → Ω → ℝ := fun t => z t 0 + fun _ => πbar with hπdef
  set x : ℕ → Ω → ℝ := fun t => z t 1 + fun _ => xbarG β κ γ πbar with hxdef
  set i : ℕ → Ω → ℝ := fun t => ibar t + φπ • (π t - fun _ => πbar) +
    (φx / 4) • (x t - fun _ => xbarG β κ γ πbar) with hidef
  have hrule : TaylorRuleG β κ γ φπ φx πbar π x i ibar := fun t => rfl
  have hgap : gapVecG β κ γ πbar π x = z := by
    funext t k
    fin_cases k <;> simp [gapVecG, hπdef, hxdef]
  have hlag : (fun t => lagPi p0 π t - fun _ => πbar) = sv := by
    funext t
    cases t with
    | zero => exact hs0'.symm
    | succ t =>
      rw [hsys.2 t]
      simp [lagPi_succ, inertiaPhi, hπdef]
  have hπa : 𝔼.Adapted π := fun t => by simp [hπdef, map_add, hza t 0, 𝔼.const]
  have hxa : 𝔼.Adapted x := fun t => by simp [hxdef, map_add, hza t 1, 𝔼.const]
  have heq := (inertia_iff_predSys 𝔼 (σ := σ) (rn := rn) hκ (p0 := p0) hπa hrule).mpr
    (by rw [hgap, hlag]; exact hsys)
  obtain ⟨Mz, hMz⟩ := hzb
  refine ⟨(π, x, i), ⟨heq.1, heq.2, hrule, hπa, hxa, fun t => ?_,
    ⟨Mz + |πbar|, fun t ω => ?_⟩, ⟨Mz + |xbarG β κ γ πbar|, fun t ω => ?_⟩⟩, ?_⟩
  · simp only [hidef, map_add, map_smul, map_sub, hiba t, hπa t, hxa t, 𝔼.const]
  · simp only [hπdef, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hMz t 0 ω) le_rfl)
  · simp only [hxdef, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hMz t 1 ω) le_rfl)
  · rintro ⟨π', x', i'⟩ ⟨has', his', hr', hπa', hxa', -, hπb', hxb'⟩
    dsimp only at has' his' hr' hπa' hxa' hπb' hxb'
    have hsys' := (inertia_iff_predSys 𝔼 hκ hπa' hr').mp ⟨has', his'⟩
    have hza' : 𝔼.AdaptedVec (gapVecG β κ γ πbar π' x') := by
      intro t k
      fin_cases k <;> simp [gapVecG, map_sub, 𝔼.const, hπa' t, hxa' t]
    have hzb' : BoundedVec (gapVecG β κ γ πbar π' x') := by
      obtain ⟨M₁, h₁⟩ := hπb'
      obtain ⟨M₂, h₂⟩ := hxb'
      refine ⟨M₁ + M₂ + |πbar| + |xbarG β κ γ πbar|, fun t k ω => ?_⟩
      have a1 := h₁ t ω
      have a2 := h₂ t ω
      have b1 := abs_nonneg (π' t ω)
      have b2 := abs_nonneg (x' t ω)
      have c1 := abs_nonneg πbar
      have c2 := abs_nonneg (xbarG β κ γ πbar)
      fin_cases k
      · simp only [gapVecG, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
        have := abs_sub (π' t ω) πbar
        linarith
      · simp only [gapVecG, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          Pi.sub_apply]
        have := abs_sub (x' t ω) (xbarG β κ γ πbar)
        linarith
    have hu := huniq (gapVecG β κ γ πbar π' x', fun t => lagPi p0 π' t - fun _ => πbar)
      ⟨hsys', rfl, hza', lagPiGap_adapted 𝔼 hp0 πbar hπa',
        hzb', lagPiGap_bounded hp0b πbar hπb'⟩
    simp only [Prod.mk.injEq] at hu
    obtain ⟨hz', -⟩ := hu
    have e1 : π' = π := by
      funext t ω
      have := congrFun (congrFun (congrFun hz' t) 0) ω
      simp only [gapVecG, Matrix.cons_val_zero, Pi.sub_apply] at this
      simp only [hπdef, Pi.add_apply]
      linarith
    have e2 : x' = x := by
      funext t ω
      have := congrFun (congrFun (congrFun hz' t) 1) ω
      simp only [gapVecG, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.sub_apply] at this
      simp only [hxdef, Pi.add_apply]
      linarith
    have e3 : i' = i := by
      funext t
      rw [hr' t, hrule t, e1, e2]
    rw [e1, e2, e3]

/-- **Woodford (2003), eqs. (2.37)–(2.39), p. 285 (the solution form).** In the equilibrium of
(1.12), (2.36), (1.14): `π_t = π̄ + ω_π (π_{t−1} − π̄) + ∑ ψ^π_j E_t g_{t+j}`,
`x_t = x̄ + ω_x (π_{t−1} − π̄) + ∑ ψ^x_j E_t g_{t+j}`,
`î_t = ī_t + ω_i (π_{t−1} − π̄) + ∑ ψ^i_j E_t g_{t+j}` with `ω_i = φ_π ω_π + φ_x ω_x / 4`,
`ψ^i_j = φ_π ψ^π_j + φ_x ψ^x_j / 4`, `g = r̂ⁿ + π̄ − ī`. -/
theorem inertia_equilibrium_formula {β σ κ γ φπ φx πbar lam : ℝ} {ω : Fin 2 → ℝ}
    (hκ : κ ≠ 0)
    (hD : Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam ω)
    (hd : det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
      (predN β σ))) (det2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
        (predN β σ))))
    {rn ibar : ℕ → Ω → ℝ} {Mg : ℝ} (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ Mg)
    (hga : 𝔼.Adapted (gapForcing πbar rn ibar))
    {p0 : Ω → ℝ} {B : ℝ} (hp0 : 𝔼.E 0 p0 = p0) (hp0b : ∀ x, |p0 x| ≤ B)
    {π x i : ℕ → Ω → ℝ} (has : ASInertia 𝔼 β κ γ p0 π x) (his : IS112 𝔼 σ x i π rn)
    (hr : TaylorRuleG β κ γ φπ φx πbar π x i ibar) (hπa : 𝔼.Adapted π)
    (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x) (t : ℕ) (y : Ω) :
    let ψ := coef (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
      (predN β σ)) (solvew (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
        (predB σ))
    π t y = πbar + ω 0 * (lagPi p0 π t y - πbar) +
        ∑' j, ψ j 0 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y ∧
      x t y = xbarG β κ γ πbar + ω 1 * (lagPi p0 π t y - πbar) +
        ∑' j, ψ j 1 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y ∧
      i t y = ibar t y + (φπ * ω 0 + φx / 4 * ω 1) * (lagPi p0 π t y - πbar) +
        ∑' j, (φπ * ψ j 0 + φx / 4 * ψ j 1) * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y := by
  intro ψ
  have hsys := (inertia_iff_predSys 𝔼 hκ hπa hr).mp ⟨has, his⟩
  have hza : 𝔼.AdaptedVec (gapVecG β κ γ πbar π x) := by
    intro t k
    fin_cases k <;> simp [gapVecG, map_sub, 𝔼.const, hπa t, hxa t]
  have hzb : BoundedVec (gapVecG β κ γ πbar π x) := by
    obtain ⟨M₁, h₁⟩ := hπb
    obtain ⟨M₂, h₂⟩ := hxb
    refine ⟨M₁ + M₂ + |πbar| + |xbarG β κ γ πbar|, fun t k ω => ?_⟩
    have a1 := h₁ t ω
    have a2 := h₂ t ω
    have b1 := abs_nonneg (π t ω)
    have b2 := abs_nonneg (x t ω)
    have c1 := abs_nonneg πbar
    have c2 := abs_nonneg (xbarG β κ γ πbar)
    fin_cases k
    · simp only [gapVecG, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
      have := abs_sub (π t ω) πbar
      linarith
    · simp only [gapVecG, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Pi.sub_apply]
      have := abs_sub (x t ω) (xbarG β κ γ πbar)
      linarith
  have hsa := lagPiGap_adapted 𝔼 hp0 πbar hπa
  have hsb := lagPiGap_bounded hp0b πbar hπb
  have F0 := predSys_solution_form 𝔼 hD hd hG hg hga hsys hza hsa hzb hsb t 0 y
  have F1 := predSys_solution_form 𝔼 hD hd hG hg hga hsys hza hsa hzb hsb t 1 y
  simp only [gapVecG, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.sub_apply] at F0 F1
  have hπ : π t y = πbar + ω 0 * (lagPi p0 π t y - πbar) +
      ∑' j, ψ j 0 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y := by linarith
  have hx : x t y = xbarG β κ γ πbar + ω 1 * (lagPi p0 π t y - πbar) +
      ∑' j, ψ j 1 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y := by linarith
  refine ⟨hπ, hx, ?_⟩
  have hX : ∀ j, |𝔼.E t (gapForcing πbar rn ibar (t + j)) y| ≤ Mg :=
    fun j => 𝔼.abs_E_le (hg _) t y
  have s0' := summable_coef_mul hG (solvew (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0
    inertiaPhi ω) (predB σ)) 0 hX
  have s1' := summable_coef_mul hG (solvew (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0
    inertiaPhi ω) (predB σ)) 1 hX
  have e : ∑' j, (φπ * ψ j 0 + φx / 4 * ψ j 1) * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y =
      φπ * ∑' j, ψ j 0 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y +
        φx / 4 * ∑' j, ψ j 1 * 𝔼.E t (gapForcing πbar rn ibar (t + j)) y := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (s0'.mul_left φπ).tsum_add (s1'.mul_left (φx / 4))]
    refine tsum_congr fun j => ?_
    ring
  have hri := congrFun (hr t) y
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hri
  rw [e, hri, hπ, hx]
  ring

/-- **Woodford (2003), p. 287 (inertial rule (2.8)).** If `ī_t = r̂ⁿ_t + π̄` at all dates, the
only fluctuations come from the initial `î_{−1} − ī_{−1}`: `π_t − π̄ = ω_π λᵗ s_0`,
`x_t − x̄ = ω_x λᵗ s_0`, deterministic given `s_0`, and `π_t → π̄`, `x_t → x̄`. -/
theorem inertial_tracking {β σ κ ρ φπ φx πbar lam : ℝ} {ω : Fin 2 → ℝ} (hκ : κ ≠ 0)
    (hD : Decomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω)
    (hl : |lam| < 1)
    (hd : det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx)
      ω) (predN β σ))) (det2 (solveMN (resM (inertP κ) (predN β σ) (a25 σ)
        (inertPhi φπ φx) ω) (predN β σ))))
    {rn ibar : ℕ → Ω → ℝ} (htrack : ∀ t, ibar t = rn t + fun _ => πbar)
    (hiba : 𝔼.Adapted ibar) {s0 : Ω → ℝ} {B : ℝ} (hs0 : 𝔼.E 0 s0 = s0)
    (hs0b : ∀ x, |s0 x| ≤ B) {π x i : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x)
    (his : IS112 𝔼 σ x i π rn) (hr : InertialRule β κ ρ φπ φx πbar s0 π x i ibar)
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hia : 𝔼.Adapted i) (hπb : BoundedProc π)
    (hxb : BoundedProc x) (hib : BoundedProc (i - ibar)) (y : Ω) :
    (∀ t, π t y = πbar + ω 0 * lam ^ t * s0 y ∧ x t y = xbar β κ πbar + ω 1 * lam ^ t * s0 y) ∧
      Tendsto (fun t => π t y) atTop (𝓝 πbar) ∧
        Tendsto (fun t => x t y) atTop (𝓝 (xbar β κ πbar)) := by
  have h0 : gapForcing πbar rn ibar = 0 := by
    funext t
    simp only [gapForcing, htrack t, Pi.zero_apply]
    abel
  have hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ 0 := by simp [h0]
  have hga : 𝔼.Adapted (gapForcing πbar rn ibar) := by
    rw [h0]
    intro t
    simp
  have F := fun t => inertial_equilibrium_formula 𝔼 hκ hD hd hG hg hga hiba hs0 hs0b has his hr
    hπa hxa hia hπb hxb hib t y
  simp only [h0, Pi.zero_apply, map_zero, mul_zero, tsum_zero, add_zero] at F
  have hlag : ∀ t, lagGap s0 i ibar t y = lam ^ t * s0 y := by
    intro t
    induction t with
    | zero => simp [lagGap]
    | succ t ih =>
      rw [lagGap_succ, Pi.sub_apply, (F t).2.2, ih, pow_succ]
      ring
  have hform : ∀ t, π t y = πbar + ω 0 * lam ^ t * s0 y ∧
      x t y = xbar β κ πbar + ω 1 * lam ^ t * s0 y := by
    intro t
    rw [(F t).1, (F t).2.1, hlag t]
    constructor <;> ring
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hl
  refine ⟨hform, ?_, ?_⟩
  · have : Tendsto (fun t : ℕ => πbar + ω 0 * lam ^ t * s0 y) atTop (𝓝 πbar) := by
      simpa using ((hp.const_mul (ω 0)).mul_const (s0 y)).const_add πbar
    exact this.congr fun t => (hform t).1.symm
  · have : Tendsto (fun t : ℕ => xbar β κ πbar + ω 1 * lam ^ t * s0 y) atTop
        (𝓝 (xbar β κ πbar)) := by
      simpa using ((hp.const_mul (ω 1)).mul_const (s0 y)).const_add (xbar β κ πbar)
    exact this.congr fun t => (hform t).2.symm

/-- **Woodford (2003), p. 287 (inflation inertia (2.36)).** If `ī_t = r̂ⁿ_t + π̄` at all dates,
`π_t − π̄ = λ^{t+1}(π_{−1} − π̄)` and `x_t − x̄ = ω_x λᵗ (π_{−1} − π̄)`: the only variation is
deterministic given `π_{−1}`, and it dies out. -/
theorem inertia_tracking {β σ κ γ φπ φx πbar lam : ℝ} {ω : Fin 2 → ℝ} (hκ : κ ≠ 0)
    (hD : Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam ω)
    (hl : |lam| < 1)
    (hd : det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
      (predN β σ))) (det2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
        (predN β σ))))
    {rn ibar : ℕ → Ω → ℝ} (htrack : ∀ t, ibar t = rn t + fun _ => πbar)
    {p0 : Ω → ℝ} {B : ℝ} (hp0 : 𝔼.E 0 p0 = p0) (hp0b : ∀ x, |p0 x| ≤ B)
    {π x i : ℕ → Ω → ℝ} (has : ASInertia 𝔼 β κ γ p0 π x) (his : IS112 𝔼 σ x i π rn)
    (hr : TaylorRuleG β κ γ φπ φx πbar π x i ibar) (hπa : 𝔼.Adapted π)
    (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x) (y : Ω) :
    (∀ t, π t y = πbar + lam ^ (t + 1) * (p0 y - πbar) ∧
      x t y = xbarG β κ γ πbar + ω 1 * lam ^ t * (p0 y - πbar)) ∧
      Tendsto (fun t => π t y) atTop (𝓝 πbar) ∧
        Tendsto (fun t => x t y) atTop (𝓝 (xbarG β κ γ πbar)) := by
  have h0 : gapForcing πbar rn ibar = 0 := by
    funext t
    simp only [gapForcing, htrack t, Pi.zero_apply]
    abel
  have hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ 0 := by simp [h0]
  have hga : 𝔼.Adapted (gapForcing πbar rn ibar) := by
    rw [h0]
    intro t
    simp
  have hω0 : ω 0 = lam := by
    have := hD.2
    simp only [inertiaPhi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at this
    linarith
  have F := fun t => inertia_equilibrium_formula 𝔼 hκ hD hd hG hg hga hp0 hp0b has his hr
    hπa hxa hπb hxb t y
  simp only [h0, Pi.zero_apply, map_zero, mul_zero, tsum_zero, add_zero, hω0] at F
  have hlag : ∀ t, lagPi p0 π t y - πbar = lam ^ t * (p0 y - πbar) := by
    intro t
    induction t with
    | zero => simp [lagPi]
    | succ t ih =>
      rw [lagPi_succ, (F t).1, ih, pow_succ]
      ring
  have hform : ∀ t, π t y = πbar + lam ^ (t + 1) * (p0 y - πbar) ∧
      x t y = xbarG β κ γ πbar + ω 1 * lam ^ t * (p0 y - πbar) := by
    intro t
    rw [(F t).1, (F t).2.1, hlag t, pow_succ]
    constructor <;> ring
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hl
  refine ⟨hform, ?_, ?_⟩
  · have hp1 : Tendsto (fun t : ℕ => lam ^ (t + 1)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mpr hp
    have : Tendsto (fun t : ℕ => πbar + lam ^ (t + 1) * (p0 y - πbar)) atTop (𝓝 πbar) := by
      simpa using (hp1.mul_const (p0 y - πbar)).const_add πbar
    exact this.congr fun t => (hform t).1.symm
  · have : Tendsto (fun t : ℕ => xbarG β κ γ πbar + ω 1 * lam ^ t * (p0 y - πbar)) atTop
        (𝓝 (xbarG β κ γ πbar)) := by
      simpa using ((hp.const_mul (ω 1)).mul_const (p0 y - πbar)).const_add (xbarG β κ γ πbar)
    exact this.congr fun t => (hform t).2.symm

/-- **Woodford (2003), pp. 284 and 286 (shock equivalence with inflation inertia (2.36)).** Two
economies with the same gap `r̂ⁿ − ī` and the same `π_{−1}` have the same equilibrium inflation,
output gap and `î − ī`: under (1.12), (2.36), (1.14) only the gap matters, so a natural-rate
disturbance `h` has the same effects as a policy disturbance `−h`. -/
theorem inertia_shock_equivalence {β σ κ γ φπ φx πbar lam : ℝ} {ω : Fin 2 → ℝ}
    (hκ : κ ≠ 0)
    (hD : Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam ω)
    (hd : det2 (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω) ≠ 0)
    (hG : SchurStable (tr2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
      (predN β σ))) (det2 (solveMN (resM (inertiaP β σ κ γ φπ φx) (predN β σ) 0 inertiaPhi ω)
        (predN β σ))))
    {rn ibar rn' ibar' : ℕ → Ω → ℝ} {Mg : ℝ}
    (hgap : gapForcing πbar rn ibar = gapForcing πbar rn' ibar')
    (hg : ∀ t ω, |gapForcing πbar rn ibar t ω| ≤ Mg)
    (hga : 𝔼.Adapted (gapForcing πbar rn ibar))
    {p0 : Ω → ℝ} {B : ℝ} (hp0 : 𝔼.E 0 p0 = p0) (hp0b : ∀ x, |p0 x| ≤ B)
    {π x i π' x' i' : ℕ → Ω → ℝ}
    (has : ASInertia 𝔼 β κ γ p0 π x) (his : IS112 𝔼 σ x i π rn)
    (hr : TaylorRuleG β κ γ φπ φx πbar π x i ibar) (hπa : 𝔼.Adapted π)
    (hxa : 𝔼.Adapted x) (hπb : BoundedProc π) (hxb : BoundedProc x)
    (has' : ASInertia 𝔼 β κ γ p0 π' x') (his' : IS112 𝔼 σ x' i' π' rn')
    (hr' : TaylorRuleG β κ γ φπ φx πbar π' x' i' ibar') (hπa' : 𝔼.Adapted π')
    (hxa' : 𝔼.Adapted x') (hπb' : BoundedProc π') (hxb' : BoundedProc x') :
    π = π' ∧ x = x' ∧ i - ibar = i' - ibar' := by
  have hg' : ∀ t ω, |gapForcing πbar rn' ibar' t ω| ≤ Mg := by rw [← hgap]; exact hg
  have hga' : 𝔼.Adapted (gapForcing πbar rn' ibar') := by rw [← hgap]; exact hga
  have F := fun t y => inertia_equilibrium_formula 𝔼 hκ hD hd hG hg hga hp0 hp0b has his hr
    hπa hxa hπb hxb t y
  have F' := fun t y => inertia_equilibrium_formula 𝔼 hκ hD hd hG hg' hga' hp0 hp0b has' his'
    hr' hπa' hxa' hπb' hxb' t y
  simp only [← hgap] at F'
  have hlag : ∀ t y, lagPi p0 π t y = lagPi p0 π' t y := by
    intro t
    induction t with
    | zero => intro y; rfl
    | succ t ih =>
      intro y
      rw [lagPi_succ, lagPi_succ, (F t y).1, (F' t y).1, ih y]
  refine ⟨funext fun t => funext fun y => ?_, funext fun t => funext fun y => ?_,
    funext fun t => funext fun y => ?_⟩
  · rw [(F t y).1, (F' t y).1, hlag t y]
  · rw [(F t y).2.1, (F' t y).2.1, hlag t y]
  · simp only [Pi.sub_apply]
    rw [(F t y).2.2, (F' t y).2.2, hlag t y]
    ring

/-! #### Footnote 47: the numbers -/

/-- Woodford (2003), p. 277: a decomposition satisfying all hypotheses of
`predSys_existsUnique` (by `decomp_unique` there is at most one). -/
def GoodDecomp (P N : Matrix (Fin 2) (Fin 2) ℝ) (h k φ : Fin 2 → ℝ) (ρ lam : ℝ)
    (ω : Fin 2 → ℝ) : Prop :=
  Decomp P N h k φ ρ lam ω ∧ |lam| < 1 ∧ det2 (resM P N k φ ω) ≠ 0 ∧
    SchurStable (tr2 (solveMN (resM P N k φ ω) N)) (det2 (solveMN (resM P N k φ ω) N))

omit 𝔼 in
/-- Woodford (2003), p. 285, footnote 47 (helper): for the Table 5.1 calibration
(`β = 0.99`, `σ = 1/0.16`, `κ = 0.024`) with `φ_π = 2`, `φ_x = 1`, any root `λ` of `H` in
`[lo, hi] ⊂ [0, 1)` gives the (unique) good decomposition. -/
theorem fn47_good_of_root {γ lam : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hl0 : 0 ≤ lam)
    (hl1 : lam < 1)
    (hH : inertiaCubic (99 / 100) (25 / 4) (3 / 125) γ 2 1 lam = 0)
    (hβl : 99 / 100 * lam < γ * (1 + 25 / 4 * 1 / 4) ∨ (lam = 0 ∧ γ = 0)) :
    GoodDecomp (inertiaP (99 / 100) (25 / 4) (3 / 125) γ 2 1) (predN (99 / 100) (25 / 4))
      (inertiaH γ) 0 inertiaPhi 0 lam (inertiaOmega (99 / 100) (3 / 125) γ lam) := by
  have hTP : InertiaTaylorPrinciple (99 / 100) (3 / 125) γ 2 1 := by
    unfold InertiaTaylorPrinciple
    have : 0 ≤ (1 - γ) * (1 - 99 / 100) * 1 / (4 * (3 / 125)) := by
      have : 0 ≤ 1 - γ := by linarith
      positivity
    linarith
  have hD := inertia_decomp (by norm_num) hH
  obtain ⟨hd, hG⟩ := inertia_forward_stable (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hγ (by norm_num) (by norm_num) hTP hD hl0 hl1 hβl
  exact ⟨hD, by rw [abs_lt]; constructor <;> linarith, hd, hG⟩

omit 𝔼 in
/-- **Woodford (2003), p. 286, footnote 47 (`γ = 0.5`), checked exactly.** For the Table 5.1
calibration with `φ_π = 2`, `φ_x = 1`, `γ = 1/2`, the inflation-inertia model has a (unique)
good decomposition, and for it `ω_π = λ ∈ (0.42036, 0.42037)` and
`ω_x ∈ (−1.9374, −1.9371)`. The printed `ω_π = 0.42` is the correct rounding; the printed
`ω_x = −1.95` is not (it rounds to `−1.94`). -/
theorem fn47_gamma_half :
    (∃ lam ω, GoodDecomp (inertiaP (99 / 100) (25 / 4) (3 / 125) (1 / 2) 2 1)
      (predN (99 / 100) (25 / 4)) (inertiaH (1 / 2)) 0 inertiaPhi 0 lam ω) ∧
    ∀ lam ω, GoodDecomp (inertiaP (99 / 100) (25 / 4) (3 / 125) (1 / 2) 2 1)
      (predN (99 / 100) (25 / 4)) (inertiaH (1 / 2)) 0 inertiaPhi 0 lam ω →
      ω 0 = lam ∧ 42036 / 100000 < ω 0 ∧ ω 0 < 42037 / 100000 ∧
        -19374 / 10000 < ω 1 ∧ ω 1 < -19371 / 10000 := by
  have hcont : Continuous (fun l => inertiaCubic (99 / 100) (25 / 4) (3 / 125) (1 / 2) 2 1 l) := by
    unfold inertiaCubic
    fun_prop
  obtain ⟨l, ⟨hlo, hhi⟩, hl⟩ := intermediate_value_Ioo (by norm_num : (42036 / 100000 : ℝ) ≤
    42037 / 100000) hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo
      (inertiaCubic (99 / 100) (25 / 4) (3 / 125) (1 / 2) 2 1 (42036 / 100000))
      (inertiaCubic (99 / 100) (25 / 4) (3 / 125) (1 / 2) 2 1 (42037 / 100000)) from by
        constructor <;> norm_num [inertiaCubic])
  have hgood := fn47_good_of_root (by norm_num) (by norm_num) (by linarith) (by linarith) hl
    (Or.inl (by linarith))
  refine ⟨⟨l, _, hgood⟩, fun lam ω hω => ?_⟩
  obtain ⟨hD, hl', hd, hG⟩ := hgood
  obtain ⟨hD', hl'', hd', hG'⟩ := hω
  obtain ⟨e1, e2⟩ := decomp_unique (b := 0) hD hl' hd hG hD' hl'' hd' hG'
  subst e1 e2
  simp only [inertiaOmega, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have key : (l - 1 / 2) * (1 - 99 / 100 * l) - (42036 / 100000 - 1 / 2) *
      (1 - 99 / 100 * (42036 / 100000)) = (l - 42036 / 100000) *
        (1 + 99 / 100 * (1 / 2) - 99 / 100 * (l + 42036 / 100000)) := by ring
  have key2 : (42037 / 100000 - 1 / 2) * (1 - 99 / 100 * (42037 / 100000)) -
      (l - 1 / 2) * (1 - 99 / 100 * l) = (42037 / 100000 - l) *
        (1 + 99 / 100 * (1 / 2) - 99 / 100 * (l + 42037 / 100000)) := by ring
  have p1 : 0 < (l - 42036 / 100000) *
      (1 + 99 / 100 * (1 / 2) - 99 / 100 * (l + 42036 / 100000)) :=
    mul_pos (by linarith) (by linarith)
  have p2 : 0 < (42037 / 100000 - l) *
      (1 + 99 / 100 * (1 / 2) - 99 / 100 * (l + 42037 / 100000)) :=
    mul_pos (by linarith) (by linarith)
  refine ⟨trivial, hlo, hhi, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

omit 𝔼 in
/-- **Woodford (2003), p. 286, footnote 47 (`γ = 1`), checked exactly.** For the Table 5.1
calibration with `φ_π = 2`, `φ_x = 1`, `γ = 1`: `ω_π = λ ∈ (0.72839, 0.72840)` and
`ω_x ∈ (−3.1563, −3.156)`. The printed `ω_π = 0.73` is the correct rounding; the printed
`ω_x = −3.17` is not (it rounds to `−3.16`). -/
theorem fn47_gamma_one :
    (∃ lam ω, GoodDecomp (inertiaP (99 / 100) (25 / 4) (3 / 125) 1 2 1)
      (predN (99 / 100) (25 / 4)) (inertiaH 1) 0 inertiaPhi 0 lam ω) ∧
    ∀ lam ω, GoodDecomp (inertiaP (99 / 100) (25 / 4) (3 / 125) 1 2 1)
      (predN (99 / 100) (25 / 4)) (inertiaH 1) 0 inertiaPhi 0 lam ω →
      ω 0 = lam ∧ 72839 / 100000 < ω 0 ∧ ω 0 < 72840 / 100000 ∧
        -31563 / 10000 < ω 1 ∧ ω 1 < -3156 / 1000 := by
  have hcont : Continuous (fun l => inertiaCubic (99 / 100) (25 / 4) (3 / 125) 1 2 1 l) := by
    unfold inertiaCubic
    fun_prop
  obtain ⟨l, ⟨hlo, hhi⟩, hl⟩ := intermediate_value_Ioo (by norm_num : (72839 / 100000 : ℝ) ≤
    72840 / 100000) hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo
      (inertiaCubic (99 / 100) (25 / 4) (3 / 125) 1 2 1 (72839 / 100000))
      (inertiaCubic (99 / 100) (25 / 4) (3 / 125) 1 2 1 (72840 / 100000)) from by
        constructor <;> norm_num [inertiaCubic])
  have hgood := fn47_good_of_root (by norm_num) (by norm_num) (by linarith) (by linarith) hl
    (Or.inl (by linarith))
  refine ⟨⟨l, _, hgood⟩, fun lam ω hω => ?_⟩
  obtain ⟨hD, hl', hd, hG⟩ := hgood
  obtain ⟨hD', hl'', hd', hG'⟩ := hω
  obtain ⟨e1, e2⟩ := decomp_unique (b := 0) hD hl' hd hG hD' hl'' hd' hG'
  subst e1 e2
  simp only [inertiaOmega, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have key : (l - 1) * (1 - 99 / 100 * l) - (72839 / 100000 - 1) *
      (1 - 99 / 100 * (72839 / 100000)) = (l - 72839 / 100000) *
        (1 + 99 / 100 * 1 - 99 / 100 * (l + 72839 / 100000)) := by ring
  have key2 : (72840 / 100000 - 1) * (1 - 99 / 100 * (72840 / 100000)) -
      (l - 1) * (1 - 99 / 100 * l) = (72840 / 100000 - l) *
        (1 + 99 / 100 * 1 - 99 / 100 * (l + 72840 / 100000)) := by ring
  have p1 : 0 < (l - 72839 / 100000) *
      (1 + 99 / 100 * 1 - 99 / 100 * (l + 72839 / 100000)) :=
    mul_pos (by linarith) (by linarith)
  have p2 : 0 < (72840 / 100000 - l) *
      (1 + 99 / 100 * 1 - 99 / 100 * (l + 72840 / 100000)) :=
    mul_pos (by linarith) (by linarith)
  refine ⟨trivial, hlo, hhi, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

omit 𝔼 in
/-- Woodford (2003), p. 285 (helper, any calibration): a root `λ ∈ [0, 1)` of `H` with
`βλ < γ(1 + σφ_x/4)` (or `λ = γ = 0`) gives the (unique) good decomposition of the inertia model
when the inertia Taylor principle holds. -/
theorem inertia_good_of_root {β σ κ γ φπ φx lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hγ : 0 ≤ γ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hTP : InertiaTaylorPrinciple β κ γ φπ φx) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hH : inertiaCubic β σ κ γ φπ φx lam = 0)
    (hβl : β * lam < γ * (1 + σ * φx / 4) ∨ (lam = 0 ∧ γ = 0)) :
    GoodDecomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam
      (inertiaOmega β κ γ lam) := by
  have hD := inertia_decomp hκ.ne' hH
  obtain ⟨hd, hG⟩ := inertia_forward_stable hβ0 hβ1 hκ hσ hγ hφπ hφx hTP hD hl0 hl1 hβl
  exact ⟨hD, by rw [abs_lt]; constructor <;> linarith, hd, hG⟩

omit 𝔼 in
/-- **Woodford (2003), fn. 47, p. 286 (the source of the printed numbers, `γ = 0.5`).** With
`σ⁻¹ = 0.155` instead of Table 5.1's `0.16` (other values as in Table 5.1, `φ_π = 2`, `φ_x = 1`),
`ω_π ∈ (0.41984, 0.41985)` and `ω_x ∈ (−1.9518, −1.9514)`, which round to the printed `0.42` and
`−1.95`. -/
theorem fn47_sigma155_gamma_half :
    (∃ lam ω, GoodDecomp (inertiaP (99 / 100) (200 / 31) (3 / 125) (1 / 2) 2 1)
      (predN (99 / 100) (200 / 31)) (inertiaH (1 / 2)) 0 inertiaPhi 0 lam ω) ∧
    ∀ lam ω, GoodDecomp (inertiaP (99 / 100) (200 / 31) (3 / 125) (1 / 2) 2 1)
      (predN (99 / 100) (200 / 31)) (inertiaH (1 / 2)) 0 inertiaPhi 0 lam ω →
      ω 0 = lam ∧ 41984 / 100000 < ω 0 ∧ ω 0 < 41985 / 100000 ∧
        -19518 / 10000 < ω 1 ∧ ω 1 < -19514 / 10000 := by
  have hcont : Continuous (fun l => inertiaCubic (99 / 100) (200 / 31) (3 / 125) (1 / 2) 2 1
      l) := by
    unfold inertiaCubic
    fun_prop
  obtain ⟨l, ⟨hlo, hhi⟩, hl⟩ := intermediate_value_Ioo (by norm_num : (41984 / 100000 : ℝ) ≤
    41985 / 100000) hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo
      (inertiaCubic (99 / 100) (200 / 31) (3 / 125) (1 / 2) 2 1 (41984 / 100000))
      (inertiaCubic (99 / 100) (200 / 31) (3 / 125) (1 / 2) 2 1 (41985 / 100000)) from by
        constructor <;> norm_num [inertiaCubic])
  have hgood := inertia_good_of_root (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by unfold InertiaTaylorPrinciple; norm_num)
    (by linarith) (by linarith) hl (Or.inl (by linarith))
  refine ⟨⟨l, _, hgood⟩, fun lam ω hω => ?_⟩
  obtain ⟨hD, hl', hd, hG⟩ := hgood
  obtain ⟨hD', hl'', hd', hG'⟩ := hω
  obtain ⟨e1, e2⟩ := decomp_unique (b := 0) hD hl' hd hG hD' hl'' hd' hG'
  subst e1 e2
  simp only [inertiaOmega, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have key : (l - 1 / 2) * (1 - 99 / 100 * l) - (41984 / 100000 - 1 / 2) *
      (1 - 99 / 100 * (41984 / 100000)) = (l - 41984 / 100000) *
        (1 + 99 / 100 * (1 / 2) - 99 / 100 * (l + 41984 / 100000)) := by ring
  have key2 : (41985 / 100000 - 1 / 2) * (1 - 99 / 100 * (41985 / 100000)) -
      (l - 1 / 2) * (1 - 99 / 100 * l) = (41985 / 100000 - l) *
        (1 + 99 / 100 * (1 / 2) - 99 / 100 * (l + 41985 / 100000)) := by ring
  have p1 : 0 < (l - 41984 / 100000) *
      (1 + 99 / 100 * (1 / 2) - 99 / 100 * (l + 41984 / 100000)) :=
    mul_pos (by linarith) (by linarith)
  have p2 : 0 < (41985 / 100000 - l) *
      (1 + 99 / 100 * (1 / 2) - 99 / 100 * (l + 41985 / 100000)) :=
    mul_pos (by linarith) (by linarith)
  refine ⟨trivial, hlo, hhi, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

omit 𝔼 in
/-- **Woodford (2003), fn. 47, p. 286 (the source of the printed numbers, `γ = 1`).** With
`σ⁻¹ = 0.155`: `ω_π ∈ (0.72783, 0.72784)` and `ω_x ∈ (−3.1691, −3.1688)`, which round to the
printed `0.73` and `−3.17`. -/
theorem fn47_sigma155_gamma_one :
    (∃ lam ω, GoodDecomp (inertiaP (99 / 100) (200 / 31) (3 / 125) 1 2 1)
      (predN (99 / 100) (200 / 31)) (inertiaH 1) 0 inertiaPhi 0 lam ω) ∧
    ∀ lam ω, GoodDecomp (inertiaP (99 / 100) (200 / 31) (3 / 125) 1 2 1)
      (predN (99 / 100) (200 / 31)) (inertiaH 1) 0 inertiaPhi 0 lam ω →
      ω 0 = lam ∧ 72783 / 100000 < ω 0 ∧ ω 0 < 72784 / 100000 ∧
        -31691 / 10000 < ω 1 ∧ ω 1 < -31688 / 10000 := by
  have hcont : Continuous (fun l => inertiaCubic (99 / 100) (200 / 31) (3 / 125) 1 2 1 l) := by
    unfold inertiaCubic
    fun_prop
  obtain ⟨l, ⟨hlo, hhi⟩, hl⟩ := intermediate_value_Ioo (by norm_num : (72783 / 100000 : ℝ) ≤
    72784 / 100000) hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo
      (inertiaCubic (99 / 100) (200 / 31) (3 / 125) 1 2 1 (72783 / 100000))
      (inertiaCubic (99 / 100) (200 / 31) (3 / 125) 1 2 1 (72784 / 100000)) from by
        constructor <;> norm_num [inertiaCubic])
  have hgood := inertia_good_of_root (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by unfold InertiaTaylorPrinciple; norm_num)
    (by linarith) (by linarith) hl (Or.inl (by linarith))
  refine ⟨⟨l, _, hgood⟩, fun lam ω hω => ?_⟩
  obtain ⟨hD, hl', hd, hG⟩ := hgood
  obtain ⟨hD', hl'', hd', hG'⟩ := hω
  obtain ⟨e1, e2⟩ := decomp_unique (b := 0) hD hl' hd hG hD' hl'' hd' hG'
  subst e1 e2
  simp only [inertiaOmega, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have key : (l - 1) * (1 - 99 / 100 * l) - (72783 / 100000 - 1) *
      (1 - 99 / 100 * (72783 / 100000)) = (l - 72783 / 100000) *
        (1 + 99 / 100 * 1 - 99 / 100 * (l + 72783 / 100000)) := by ring
  have key2 : (72784 / 100000 - 1) * (1 - 99 / 100 * (72784 / 100000)) -
      (l - 1) * (1 - 99 / 100 * l) = (72784 / 100000 - l) *
        (1 + 99 / 100 * 1 - 99 / 100 * (l + 72784 / 100000)) := by ring
  have p1 : 0 < (l - 72783 / 100000) *
      (1 + 99 / 100 * 1 - 99 / 100 * (l + 72783 / 100000)) :=
    mul_pos (by linarith) (by linarith)
  have p2 : 0 < (72784 / 100000 - l) *
      (1 + 99 / 100 * 1 - 99 / 100 * (l + 72784 / 100000)) :=
    mul_pos (by linarith) (by linarith)
  refine ⟨trivial, hlo, hhi, ?_, ?_⟩
  · rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    linarith

/-! #### The exact determinacy region of the inflation-inertia model -/

/-- Woodford (2003), p. 277 and App. C.1, p. 670 (determinacy with one predetermined variable):
for every bounded adapted forcing `g` and every bounded initial `s_0` known at date 0 there is
exactly one bounded adapted solution. -/
def PredDeterminate (P N : Matrix (Fin 2) (Fin 2) ℝ) (h k b φ : Fin 2 → ℝ) (ρ : ℝ) : Prop :=
  ∀ (g : ℕ → Ω → ℝ) (s0 : Ω → ℝ), BoundedProc g → 𝔼.Adapted g → 𝔼.E 0 s0 = s0 →
    (∃ B, ∀ x, |s0 x| ≤ B) →
    ∃! p : (ℕ → Fin 2 → Ω → ℝ) × (ℕ → Ω → ℝ), PredSys 𝔼 P N h k b φ ρ g p.1 p.2 ∧
      p.2 0 = s0 ∧ 𝔼.AdaptedVec p.1 ∧ 𝔼.Adapted p.2 ∧ BoundedVec p.1 ∧ BoundedProc p.2

/-- Woodford (2003), p. 277: a good decomposition makes the system determinate (for every
expectation system). -/
theorem predDeterminate_of_good {P N : Matrix (Fin 2) (Fin 2) ℝ} {h k φ ω : Fin 2 → ℝ}
    {ρ lam : ℝ} (hgood : GoodDecomp P N h k φ ρ lam ω) (b : Fin 2 → ℝ) :
    PredDeterminate 𝔼 P N h k b φ ρ := by
  obtain ⟨hD, hl, hd, hG⟩ := hgood
  rintro g s0 ⟨Mg, hMg⟩ hga hs0 ⟨B, hB⟩
  exact predSys_existsUnique 𝔼 hD hl hd hG hMg hga hs0 hB

omit 𝔼 in
/-- Perfect foresight: `E_t` is the identity. -/
theorem pf_E (t : ℕ) (x : Unit → ℝ) : perfectForesight.E t x = x := rfl

omit 𝔼 in
/-- **Woodford (2003), p. 277 (necessity of a decomposition).** If the system is determinate
under perfect foresight, the unique bounded solution with `g = 0`, `s_0 = 1` is a single mode
`s_t = cᵗ`, `z_t = ω cᵗ` (time invariance and linearity), so there is a decomposition `(c, ω)`
with `|c| ≤ 1`. -/
theorem predDeterminate_decomp {P N : Matrix (Fin 2) (Fin 2) ℝ} {h k b φ : Fin 2 → ℝ} {ρ : ℝ}
    (hdet : PredDeterminate perfectForesight P N h k b φ ρ) :
    ∃ c ω, Decomp P N h k φ ρ c ω ∧ |c| ≤ 1 := by
  have hg0 : BoundedProc (0 : ℕ → Unit → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hga0 : perfectForesight.Adapted (0 : ℕ → Unit → ℝ) := fun _ => rfl
  obtain ⟨⟨z, s⟩, ⟨hsys, hs0, -, -, hzb, hsb⟩, -⟩ :=
    hdet 0 (fun _ => 1) hg0 hga0 rfl ⟨1, fun _ => by simp⟩
  dsimp only at hsys hs0 hzb hsb
  set c := s 1 () with hc
  -- the shifted solution and the scaled solution have the same initial value `c`
  have hshift : PredSys perfectForesight P N h k b φ ρ 0 (fun t => z (t + 1))
      (fun t => s (t + 1)) := by
    refine ⟨fun t i => ?_, fun t => hsys.2 (t + 1)⟩
    have := hsys.1 (t + 1) i
    simpa only [pf_E, Pi.zero_apply, smul_zero] using this
  have hscale : PredSys perfectForesight P N h k b φ ρ 0 (fun t i => c • z t i)
      (fun t => c • s t) := by
    refine ⟨fun t i => ?_, fun t => ?_⟩
    · funext u
      have := congrFun (hsys.1 t i) u
      simp only [pf_E, Pi.zero_apply, smul_zero, add_zero, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at this ⊢
      linear_combination c * this
    · funext u
      have := congrFun (hsys.2 t) u
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      linear_combination c * this
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨Ms, hMs⟩ := hsb
  obtain ⟨_, -, huniq⟩ := hdet 0 (fun _ => c) hg0 hga0 rfl ⟨|c|, fun _ => le_rfl⟩
  have e1 := huniq ((fun t => z (t + 1)), fun t => s (t + 1))
    ⟨hshift, funext fun u => by cases u; rfl, fun _ _ => rfl, fun _ => rfl,
      ⟨Mz, fun t i x => hMz (t + 1) i x⟩, ⟨Ms, fun t x => hMs (t + 1) x⟩⟩
  have e2 := huniq ((fun t i => c • z t i), fun t => c • s t)
    ⟨hscale, by funext u; simp [hs0], fun _ _ => rfl, fun _ => rfl,
      ⟨|c| * Mz, fun t i x => by
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hMz t i x) (abs_nonneg c)⟩,
      ⟨|c| * Ms, fun t x => by
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hMs t x) (abs_nonneg c)⟩⟩
  have e := e1.trans e2.symm
  simp only [Prod.mk.injEq] at e
  obtain ⟨ez, es⟩ := e
  have hs : ∀ t, s t () = c ^ t := by
    intro t
    induction t with
    | zero => rw [hs0]; simp
    | succ t ih =>
      have := congrFun (congrFun es t) ()
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this, ih, pow_succ, mul_comm]
  have hz : ∀ t i, z t i () = c ^ t * z 0 i () := by
    intro t i
    induction t with
    | zero => simp
    | succ t ih =>
      have := congrFun (congrFun (congrFun ez t) i) ()
      simp only [Pi.smul_apply, smul_eq_mul] at this
      rw [this, ih, pow_succ]
      ring
  refine ⟨c, fun i => z 0 i (), ⟨fun i => ?_, ?_⟩, ?_⟩
  · have := congrFun (hsys.1 0 i) ()
    simp only [pf_E, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero,
      add_zero] at this
    rw [hz 1 0, hz 1 1, hs 0, hs 1] at this
    simp only [pow_one, pow_zero, mul_one] at this
    linear_combination this
  · have := congrFun (hsys.2 0) ()
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [hs 0, hs 1] at this
    simp only [pow_one, pow_zero, mul_one] at this
    linarith
  · by_contra hc1
    push Not at hc1
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Ms hc1
    have := hMs n ()
    rw [hs n, abs_pow] at this
    linarith

/-- Woodford (2003), (2.36), p. 284: the third-order recurrence for `p_t = π_{t−1} − π̄` whose
characteristic polynomial is `H`: `β p_{t+3} + e₂ p_{t+2} + e₁ p_{t+1} + e₀ p_t`. -/
noncomputable def inertiaRec (β σ κ γ φπ φx : ℝ) (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  β * p (t + 3) - (1 + β * (1 + σ * φx / 4) + γ * β + κ * σ) * p (t + 2) +
    (1 + σ * φx / 4 + γ + γ * β * (1 + σ * φx / 4) + κ * σ * φπ) * p (t + 1) -
      γ * (1 + σ * φx / 4) * p t

/-- Woodford (2003), (2.36)–(2.38): `Hq(c) = 3βc² + 2e₂c + e₁`, the derivative of `H` (and the
quotient `H(μ)/(μ − c)` evaluated at `μ = c`). -/
noncomputable def inertiaCubicDeriv (β σ κ γ φπ φx c : ℝ) : ℝ :=
  3 * β * c ^ 2 - 2 * (1 + β * (1 + σ * φx / 4) + γ * β + κ * σ) * c +
    (1 + σ * φx / 4 + γ + γ * β * (1 + σ * φx / 4) + κ * σ * φπ)

/-- Woodford (2003), (2.36)–(2.38): the quotient `H(μ)/(μ − c)`. -/
noncomputable def inertiaQuot (β σ κ γ φπ φx c μ : ℝ) : ℝ :=
  β * μ ^ 2 + (-(1 + β * (1 + σ * φx / 4) + γ * β + κ * σ) + β * c) * μ +
    ((1 + σ * φx / 4 + γ + γ * β * (1 + σ * φx / 4) + κ * σ * φπ) -
      (1 + β * (1 + σ * φx / 4) + γ * β + κ * σ) * c + β * c ^ 2)

omit 𝔼 in
/-- Woodford (2003), (2.36): `H(μ) − H(c) = (μ − c) · Hq(c, μ)`. -/
theorem inertiaCubic_sub (β σ κ γ φπ φx c μ : ℝ) :
    inertiaCubic β σ κ γ φπ φx μ - inertiaCubic β σ κ γ φπ φx c =
      (μ - c) * inertiaQuot β σ κ γ φπ φx c μ := by
  unfold inertiaCubic inertiaQuot
  ring

omit 𝔼 in
/-- Woodford (2003), (2.36): the geometric sequence `μᵗ` solves the recurrence iff `H(μ) = 0`
(`L(μᵗ) = μᵗ H(μ)`). -/
theorem inertiaRec_pow (β σ κ γ φπ φx μ : ℝ) (t : ℕ) :
    inertiaRec β σ κ γ φπ φx (fun n => μ ^ n) t = μ ^ t * inertiaCubic β σ κ γ φπ φx μ := by
  unfold inertiaRec inertiaCubic
  simp only [pow_add]
  ring

omit 𝔼 in
/-- Woodford (2003), (2.36): `L(t cᵗ) = cᵗ (t H(c) + c Hq(c, c))`, so `t cᵗ` solves the
recurrence at a double root. -/
theorem inertiaRec_tpow (β σ κ γ φπ φx c : ℝ) (t : ℕ) :
    inertiaRec β σ κ γ φπ φx (fun n => (n : ℝ) * c ^ n) t =
      c ^ t * ((t : ℝ) * inertiaCubic β σ κ γ φπ φx c +
        c * inertiaQuot β σ κ γ φπ φx c c) := by
  unfold inertiaRec inertiaCubic inertiaQuot
  simp only [pow_add]
  push_cast
  ring

/-- Woodford (2003), (2.36) under (1.14): the processes built from a solution `p` of the
recurrence (`s_t = p_t`, `π_t − π̄ = p_{t+1}`, `x_t − x̄` from (2.36)) solve the system with no
disturbance. -/
theorem inertia_seq_predSys {β σ κ γ φπ φx : ℝ} (hκ : κ ≠ 0) (p : ℕ → ℝ)
    (hp : ∀ t, inertiaRec β σ κ γ φπ φx p t = 0) :
    PredSys perfectForesight (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 (predB σ)
      inertiaPhi 0 0
      (fun t => ![fun _ => p (t + 1),
        fun _ => ((1 + β * γ) * p (t + 1) - β * p (t + 2) - γ * p t) / κ])
      (fun t _ => p t) := by
  refine ⟨fun t i => ?_, fun t => ?_⟩
  · funext u
    have h := hp t
    unfold inertiaRec at h
    fin_cases i
    · simp [pf_E, inertiaP, predN, inertiaH]
      field_simp
      ring
    · rw [show t + 3 = t + 1 + 2 by ring] at h
      simp [pf_E, inertiaP, predN, inertiaH, predB]
      field_simp
      linear_combination 4 * h
  · funext u
    simp [inertiaPhi]

omit 𝔼 in
/-- Woodford (2003), (2.36) under (1.14) (necessity of the inertia Taylor principle, the
boundary case): if `H(1) = 0`, i.e. the Taylor principle holds with equality, then with the
constant disturbance `g ≡ 1` no solution is bounded: `Q_t = (yβ + κσ)(π_t − π̄) + κ(x_t − x̄)
− yγ (π_{t−1} − π̄)` (`y = σφ_x/4`) falls by `κσ` every period. -/
theorem inertia_unbounded_of_H1_zero {β σ κ γ φπ φx : ℝ} (hκ : 0 < κ) (hσ : 0 < σ)
    (hH1 : (1 - γ) * (1 - β) * (σ * φx / 4) - κ * σ * (1 - φπ) = 0)
    {z : ℕ → Fin 2 → Unit → ℝ} {s : ℕ → Unit → ℝ}
    (hsys : PredSys perfectForesight (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0
      (predB σ) inertiaPhi 0 (fun _ _ => 1) z s)
    (hzb : BoundedVec z) (hsb : BoundedProc s) : False := by
  set y := σ * φx / 4 with hy
  set Q : ℕ → ℝ := fun t => (y * β + κ * σ) * z t 0 () + κ * z t 1 () - y * γ * s t () with hQ
  have hstep : ∀ t, Q (t + 1) = Q t - κ * σ := by
    intro t
    have r0 := congrFun (hsys.1 t 0) ()
    have r1 := congrFun (hsys.1 t 1) ()
    have rc := congrFun (hsys.2 t) ()
    simp [pf_E, inertiaP, predN, inertiaH, predB, inertiaPhi] at r0 r1 rc
    simp only [hQ]
    linear_combination (-y) * r0 - κ * r1 + z t 0 () * hH1 - y * γ * rc
  have hlin : ∀ t, Q t = Q 0 - κ * σ * t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hstep t, ih]
      push_cast
      ring
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨Ms, hMs⟩ := hsb
  have hQb : ∀ t, |Q t| ≤ |y * β + κ * σ| * Mz + |κ| * Mz + |y * γ| * Ms := by
    intro t
    simp only [hQ]
    refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMz t 0 ()) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMz t 1 ()) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMs t ()) (abs_nonneg _)
  obtain ⟨n, hn⟩ := exists_nat_gt ((|y * β + κ * σ| * Mz + |κ| * Mz + |y * γ| * Ms + |Q 0|) /
    (κ * σ))
  have hks : 0 < κ * σ := mul_pos hκ hσ
  rw [div_lt_iff₀ hks] at hn
  have h1 := hQb n
  rw [hlin n] at h1
  have h2 := le_abs_self (κ * σ * n - Q 0)
  rw [abs_sub_comm] at h2
  have h3 := le_abs_self (Q 0)
  linarith

omit 𝔼 in
/-- Woodford (2003), (2.36) under (1.14): a decomposition is a root of `H`. -/
theorem inertia_decomp_root {β σ κ γ φπ φx lam : ℝ} {ω : Fin 2 → ℝ}
    (hD : Decomp (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 inertiaPhi 0 lam ω) :
    inertiaCubic β σ κ γ φπ φx lam = 0 := by
  obtain ⟨hW, hL⟩ := hD
  have h1 := hW 0
  have h2 := hW 1
  simp only [inertiaPhi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    at hL
  have hω : ω 0 = lam := by linarith
  simp only [inertiaP, predN, inertiaH, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val',
    Pi.zero_apply, hω] at h1 h2
  unfold inertiaCubic
  linear_combination (1 + σ * φx / 4 - lam) * h1 + κ * h2

omit 𝔼 in
/-- Woodford (2003), (2.36): a sequence `p` with `|p_t| ≤ M` gives bounded processes. -/
theorem inertia_seq_bounded {β κ γ : ℝ} {p : ℕ → ℝ} {M : ℝ} (hp : ∀ t, |p t| ≤ M) :
    BoundedVec (fun t => ![fun (_ : Unit) => p (t + 1),
        fun (_ : Unit) => ((1 + β * γ) * p (t + 1) - β * p (t + 2) - γ * p t) / κ]) ∧
      BoundedProc (fun t (_ : Unit) => p t) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hp 0)
  set K := M + (|1 + β * γ| * M + |β| * M + |γ| * M) / |κ|
  refine ⟨⟨K, fun t i _ => ?_⟩, ⟨M, fun t _ => hp t⟩⟩
  have hX : |((1 + β * γ) * p (t + 1) - β * p (t + 2) - γ * p t) / κ| ≤
      (|1 + β * γ| * M + |β| * M + |γ| * M) / |κ| := by
    rw [abs_div]
    apply div_le_div_of_nonneg_right _ (abs_nonneg κ)
    refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hp _) (abs_nonneg _)
  have hX0 : 0 ≤ (|1 + β * γ| * M + |β| * M + |γ| * M) / |κ| := by positivity
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    have := hp (t + 1)
    linarith
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith

omit 𝔼 in
/-- **Woodford (2003), pp. 284–285 (necessity, new).** Under (1.12), (2.36), (1.14) with
`β, κ, σ > 0`, `γ, φ_π, φ_x ≥ 0`: if the system is determinate (under perfect
foresight, hence a fortiori if it is determinate for every expectation system), the inertia
Taylor principle `φ_π + (1 − γ)(1 − β)φ_x/(4κ) > 1` holds. -/
theorem inertia_TP_of_determinate {β σ κ γ φπ φx : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hσ : 0 < σ) (hγ : 0 ≤ γ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx)
    (hdet : PredDeterminate perfectForesight (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ)
      0 (predB σ) inertiaPhi 0) :
    InertiaTaylorPrinciple β κ γ φπ φx := by
  set y := σ * φx / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  have hH1e : inertiaCubic β σ κ γ φπ φx 1 = (1 - γ) * (1 - β) * y - κ * σ * (1 - φπ) := by
    unfold inertiaCubic; ring
  have hHm1 : inertiaCubic β σ κ γ φπ φx (-1) < 0 := by
    have e : inertiaCubic β σ κ γ φπ φx (-1) =
        -((1 + γ) * (1 + β) * (2 + y) + κ * σ * (1 + φπ)) := by
      unfold inertiaCubic; rw [hy]; ring
    rw [e]
    have : 0 < (1 + γ) * (1 + β) * (2 + y) + κ * σ * (1 + φπ) := by positivity
    linarith
  by_contra hTP
  have hH1 : inertiaCubic β σ κ γ φπ φx 1 ≤ 0 := by
    rw [hH1e]
    by_contra hc
    exact hTP (by
      unfold InertiaTaylorPrinciple
      have e : (1 - γ) * (1 - β) * y - κ * σ * (1 - φπ) =
          σ * κ * (φπ + (1 - γ) * (1 - β) * φx / (4 * κ) - 1) := by
        rw [hy]; field_simp; ring
      rw [e] at hc
      push Not at hc
      have := pos_of_mul_pos_right hc (by positivity : (0 : ℝ) ≤ σ * κ)
      linarith)
  rcases eq_or_lt_of_le hH1 with h0 | hneg
  · -- the boundary: no bounded solution with `g ≡ 1`
    obtain ⟨⟨z, s⟩, ⟨hsys, -, -, -, hzb, hsb⟩, -⟩ :=
      hdet (fun _ _ => 1) (fun _ => 0) ⟨1, fun _ _ => by simp⟩ (fun _ => rfl) rfl
        ⟨0, fun _ => by simp⟩
    exact inertia_unbounded_of_H1_zero hκ hσ (by rw [← hH1e]; exact h0) hsys hzb hsb
  · -- strict failure: two distinct bounded modes with `s_0 = 0`, or a double root
    obtain ⟨c, ω, hD, hc⟩ := predDeterminate_decomp hdet
    have hHc := inertia_decomp_root hD
    have hc1 : c ≠ 1 := fun h => by rw [h] at hHc; linarith
    have hcm1 : c ≠ -1 := fun h => by rw [h] at hHc; linarith
    have hc' : |c| < 1 := lt_of_le_of_ne hc (fun h => by
      rcases abs_eq (zero_le_one) |>.mp h with h | h
      · exact hc1 h
      · exact hcm1 h)
    obtain ⟨hcl, hcu⟩ := abs_lt.mp hc'
    have hq1 : inertiaQuot β σ κ γ φπ φx c 1 < 0 := by
      have := inertiaCubic_sub β σ κ γ φπ φx c 1
      rw [hHc, sub_zero] at this
      by_contra hq
      push Not at hq
      have : 0 ≤ (1 - c) * inertiaQuot β σ κ γ φπ φx c 1 := mul_nonneg (by linarith) hq
      linarith
    have hqm1 : 0 < inertiaQuot β σ κ γ φπ φx c (-1) := by
      have := inertiaCubic_sub β σ κ γ φπ φx c (-1)
      rw [hHc, sub_zero] at this
      by_contra hq
      push Not at hq
      have : 0 ≤ (-1 - c) * inertiaQuot β σ κ γ φπ φx c (-1) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hq
      linarith
    have hcont : Continuous (fun μ => inertiaQuot β σ κ γ φπ φx c μ) := by
      unfold inertiaQuot; fun_prop
    obtain ⟨μ, ⟨hμl, hμu⟩, hμ⟩ := intermediate_value_Ioo' (by norm_num : (-1 : ℝ) ≤ 1)
      hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo (inertiaQuot β σ κ γ φπ φx c 1)
        (inertiaQuot β σ κ γ φπ φx c (-1)) from ⟨hq1, hqm1⟩)
    have hHμ : inertiaCubic β σ κ γ φπ φx μ = 0 := by
      have hμ' : inertiaQuot β σ κ γ φπ φx c μ = 0 := hμ
      have := inertiaCubic_sub β σ κ γ φπ φx c μ
      rw [hHc, sub_zero, hμ', mul_zero] at this
      exact this
    -- a nonzero bounded solution of the recurrence with `p_0 = 0`
    obtain ⟨p, hp, hp0, hp1, M, hpb⟩ : ∃ p : ℕ → ℝ, (∀ t, inertiaRec β σ κ γ φπ φx p t = 0) ∧
        p 0 = 0 ∧ p 1 ≠ 0 ∧ ∃ M, ∀ t, |p t| ≤ M := by
      have hμ' : inertiaQuot β σ κ γ φπ φx c μ = 0 := hμ
      by_cases hμc : μ = c
      · subst hμc
        have hμ0 : μ ≠ 0 := by
          intro h0
          rw [h0] at hμ'
          unfold inertiaQuot at hμ'
          have : 0 < 1 + y + γ + γ * β * (1 + y) + κ * σ * φπ := by positivity
          rw [← hy] at hμ'
          nlinarith
        have hlim := tendsto_self_mul_const_pow_of_abs_lt_one hc'
        obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hlim).exists_norm_le
        refine ⟨fun n => (n : ℝ) * μ ^ n, fun t => ?_, by simp, by simpa using hμ0, M,
          fun t => ?_⟩
        · rw [inertiaRec_tpow, hHc, hμ']
          ring
        · have := hM _ (Set.mem_range_self t)
          rwa [Real.norm_eq_abs] at this
      · refine ⟨fun n => c ^ n - μ ^ n, fun t => ?_, by simp, ?_, 2, fun t => ?_⟩
        · have e : inertiaRec β σ κ γ φπ φx (fun n => c ^ n - μ ^ n) t =
              inertiaRec β σ κ γ φπ φx (fun n => c ^ n) t -
                inertiaRec β σ κ γ φπ φx (fun n => μ ^ n) t := by
            unfold inertiaRec; ring
          rw [e, inertiaRec_pow, inertiaRec_pow, hHc, hHμ]
          ring
        · simp only [pow_one]
          intro h
          exact hμc (by linarith)
        · have a : |c ^ t| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
          have b : |μ ^ t| ≤ 1 := by
            rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨hμl.le, hμu.le⟩)
          exact (abs_sub _ _).trans (by linarith)
    obtain ⟨hzb, hsb⟩ := inertia_seq_bounded (β := β) (κ := κ) (γ := γ) hpb
    obtain ⟨_, -, huniq⟩ := hdet 0 (fun _ => 0) ⟨0, fun _ _ => by simp⟩ (fun _ => rfl) rfl
      ⟨0, fun _ => by simp⟩
    have hA := huniq (_, _) ⟨inertia_seq_predSys hκ.ne' p hp, funext fun _ => hp0,
      fun _ _ => rfl, fun _ => rfl, hzb, hsb⟩
    have hB := huniq ((fun _ _ _ => 0), fun _ _ => 0) ⟨⟨fun t i => by funext u; simp [pf_E],
      fun t => by funext u; simp⟩,
      rfl, fun _ _ => rfl, fun _ => rfl, ⟨0, fun _ _ _ => by simp⟩, ⟨0, fun _ _ => by simp⟩⟩
    have := congrFun (congrFun (congrArg Prod.snd (hA.trans hB.symm)) 1) ()
    exact hp1 this

/-- **Woodford (2003), pp. 284–285 (the exact determinacy region, new).** Under (1.12), (2.36),
(1.14) with `0 < β < 1`, `κ, σ > 0`, `γ, φ_π, φ_x ≥ 0`, the system (with predetermined
`π_{t−1}`) is determinate iff `φ_π + (1 − γ)(1 − β)φ_x/(4κ) > 1`; sufficiency holds for every
expectation system, necessity already under perfect foresight. -/
theorem inertia_determinate_iff {β σ κ γ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hγ : 0 ≤ γ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    (PredDeterminate perfectForesight (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0
      (predB σ) inertiaPhi 0 ↔ InertiaTaylorPrinciple β κ γ φπ φx) ∧
    (InertiaTaylorPrinciple β κ γ φπ φx → PredDeterminate 𝔼 (inertiaP β σ κ γ φπ φx)
      (predN β σ) (inertiaH γ) 0 (predB σ) inertiaPhi 0) := by
  have suff : ∀ {Ω' : Type} (𝔼' : ExpectationSystem Ω'), InertiaTaylorPrinciple β κ γ φπ φx →
      PredDeterminate 𝔼' (inertiaP β σ κ γ φπ φx) (predN β σ) (inertiaH γ) 0 (predB σ)
        inertiaPhi 0 := by
    intro Ω' 𝔼' hTP
    obtain ⟨lam, hl0, hl1, -, hD, hd, hG⟩ := inertia_BK hβ0 hβ1 hκ hσ hγ hφπ hφx hTP
    exact predDeterminate_of_good 𝔼' ⟨hD, by rw [abs_lt]; constructor <;> linarith, hd, hG⟩ _
  refine ⟨⟨inertia_TP_of_determinate hβ0 hκ hσ hγ hφπ hφx, suff perfectForesight⟩, ?_⟩
  intro hTP
  obtain ⟨lam, hl0, hl1, -, hD, hd, hG⟩ := inertia_BK hβ0 hβ1 hκ hσ hγ hφπ hφx hTP
  exact predDeterminate_of_good 𝔼 ⟨hD, by rw [abs_lt]; constructor <;> linarith, hd, hG⟩ _

/-! #### Strong responses under the inertial rule (2.8) (p. 288) -/

omit 𝔼 in
/-- Woodford (2003), p. 288 (a weighted-norm bound): if `|G₀₀| + |G₀₁| W ≤ 1`,
`|G₁₀|/W + |G₁₁| ≤ 1`, `|w₀| ≤ V`, `|w₁| ≤ W V`, then every `Gʲ w` satisfies the same bounds. -/
theorem coef_weighted_bound {G : Matrix (Fin 2) (Fin 2) ℝ} {w : Fin 2 → ℝ} {W V : ℝ}
    (hW : 0 < W) (h1 : |G 0 0| + |G 0 1| * W ≤ 1) (h2 : |G 1 0| / W + |G 1 1| ≤ 1)
    (hw0 : |w 0| ≤ V) (hw1 : |w 1| ≤ W * V) (j : ℕ) :
    |coef G w j 0| ≤ V ∧ |coef G w j 1| ≤ W * V := by
  have hV : 0 ≤ V := (abs_nonneg _).trans hw0
  induction j with
  | zero => rw [coef_zero]; exact ⟨hw0, hw1⟩
  | succ j ih =>
    obtain ⟨a, b⟩ := ih
    rw [coef_succ, coef_succ]
    constructor
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |G 0 0| * |coef G w j 0| + |G 0 1| * |coef G w j 1|
          ≤ |G 0 0| * V + |G 0 1| * (W * V) := by gcongr
        _ = V * (|G 0 0| + |G 0 1| * W) := by ring
        _ ≤ V * 1 := by gcongr
        _ = V := mul_one V
    · refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |G 1 0| * |coef G w j 0| + |G 1 1| * |coef G w j 1|
          ≤ |G 1 0| * V + |G 1 1| * (W * V) := by gcongr
        _ = W * V * (|G 1 0| / W + |G 1 1|) := by field_simp
        _ ≤ W * V * 1 := by gcongr
        _ = W * V := mul_one _

omit 𝔼 in
/-- Woodford (2003), p. 288 (the stable root shrinks): for a root `λ ∈ [0, 1)` of the inertial
cubic, `λ σ (κφ_π + (1 − β)φ_x/4) ≤ (ρ + 1)(1 + κσ)`. -/
theorem inert_root_small {β σ κ ρ φπ φx lam : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφx : 0 ≤ φx) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hC : inertCubic β σ κ ρ φπ φx lam = 0) :
    lam * σ * (κ * φπ + (1 - β) * φx / 4) ≤ (ρ + 1) * (1 + κ * σ) := by
  unfold inertCubic at hC
  set Q := (1 - β * lam) * (1 - lam) - κ * σ * lam with hQ
  have hQa : |Q| ≤ 1 + κ * σ := by
    have a1 : 0 ≤ (1 - β * lam) * (1 - lam) := mul_nonneg (by nlinarith) (by linarith)
    have a2 : (1 - β * lam) * (1 - lam) ≤ 1 := by
      have b1 : 0 ≤ 1 - β * lam := by nlinarith
      have b2 : (1 - β * lam) * (1 - lam) ≤ (1 - β * lam) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) b1
      nlinarith
    have a3 : 0 ≤ κ * σ * lam := by positivity
    have a4 : κ * σ * lam ≤ κ * σ := by nlinarith [mul_pos hκ hσ]
    rw [abs_le]; constructor <;> linarith
  have hr : |ρ - lam| ≤ ρ + 1 := by rw [abs_le]; constructor <;> linarith
  have hlhs : lam * σ * (κ * φπ + (1 - β) * φx / 4) ≤
      σ * lam * (κ * φπ + φx * (1 - β * lam) / 4) := by
    have : φx * (1 - β) ≤ φx * (1 - β * lam) := by
      apply mul_le_mul_of_nonneg_left _ hφx; nlinarith
    have hsl : 0 ≤ σ * lam := by positivity
    nlinarith
  have heq : σ * lam * (κ * φπ + φx * (1 - β * lam) / 4) = (ρ - lam) * Q := by linarith
  have : (ρ - lam) * Q ≤ (ρ + 1) * (1 + κ * σ) := by
    calc (ρ - lam) * Q ≤ |(ρ - lam) * Q| := le_abs_self _
      _ = |ρ - lam| * |Q| := abs_mul _ _
      _ ≤ (ρ + 1) * (1 + κ * σ) := by gcongr
  linarith

omit 𝔼 in
/-- Woodford (2003), p. 288 (the matrix `M` of the inertial-rule forward block), with
`ω = (−a, −b)`: `M = [[1 + βaφ_π, −κ + βaφ_x/4], [cφ_π, 1 + cφ_x/4]]`, `c = σ + σa + b`, and
`det M = 1 + cφ_x/4 + βaφ_π + κcφ_π`. -/
theorem inert_M_explicit {β σ κ φπ φx a b : ℝ} {ω : Fin 2 → ℝ} (h0 : ω 0 = -a) (h1 : ω 1 = -b) :
    resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω 0 0 = 1 + β * a * φπ ∧
    resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω 0 1 = -κ + β * a * φx / 4 ∧
    resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω 1 0 = (σ + σ * a + b) * φπ ∧
    resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω 1 1 =
      1 + (σ + σ * a + b) * φx / 4 ∧
    det2 (resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω) =
      1 + (σ + σ * a + b) * φx / 4 + β * a * φπ + κ * (σ + σ * a + b) * φπ := by
  have e00 : resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω 0 0 =
      1 + β * a * φπ := by
    simp only [resM, inertP, predN, a25, inertPhi, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', h0, h1]
    ring
  have e01 : resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω 0 1 =
      -κ + β * a * φx / 4 := by
    simp only [resM, inertP, predN, a25, inertPhi, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', h0, h1]
    ring
  have e10 : resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω 1 0 =
      (σ + σ * a + b) * φπ := by
    simp only [resM, inertP, predN, a25, inertPhi, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', h0, h1]
    ring
  have e11 : resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx) ω 1 1 =
      1 + (σ + σ * a + b) * φx / 4 := by
    simp only [resM, inertP, predN, a25, inertPhi, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', h0, h1]
    ring
  refine ⟨e00, e01, e10, e11, ?_⟩
  simp only [det2]
  rw [e00, e01, e10, e11]
  ring

omit 𝔼 in
/-- Woodford (2003), p. 288 (bounds on the forward block): if `1 ≤ M₀₀ ≤ m₀₀`, `|M₀₁| ≤ m₀₁`,
`0 ≤ M₁₀`, `κ M₁₀ ≤ d`, `0 ≤ M₁₁ ≤ d` (`d = det M ≥ 1`), then `G = M⁻¹N` and `w = M⁻¹b` satisfy the
weighted-norm conditions with weight `W = 2(σm₀₀ + β/κ) + 1` once `d` is large, and
`|w₀| ≤ S/d`, `|w₁| ≤ W S/d` with `S = σm₀₁ + σm₀₀`. -/
theorem forward_block_bounds {β σ κ m00 m01 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) {M : Matrix (Fin 2) (Fin 2) ℝ} (hd1 : 1 ≤ det2 M)
    (h00 : 1 ≤ M 0 0 ∧ M 0 0 ≤ m00) (h01 : |M 0 1| ≤ m01)
    (h10 : 0 ≤ M 1 0 ∧ κ * M 1 0 ≤ det2 M) (h11 : 0 ≤ M 1 1 ∧ M 1 1 ≤ det2 M)
    (hdA : (σ + (2 * (σ * m00 + β / κ) + 1)) * m01 / (1 - β) ≤ det2 M)
    (hdB : 2 * m00 ≤ det2 M) :
    |solveMN M (predN β σ) 0 0| + |solveMN M (predN β σ) 0 1| * (2 * (σ * m00 + β / κ) + 1) ≤ 1 ∧
    |solveMN M (predN β σ) 1 0| / (2 * (σ * m00 + β / κ) + 1) + |solveMN M (predN β σ) 1 1| ≤ 1 ∧
    |solvew M (predB σ) 0| ≤ (σ * m01 + σ * m00) / det2 M ∧
    |solvew M (predB σ) 1| ≤ (2 * (σ * m00 + β / κ) + 1) * ((σ * m01 + σ * m00) / det2 M) := by
  set d := det2 M with hd
  set W := 2 * (σ * m00 + β / κ) + 1 with hW
  have hd0 : 0 < d := by linarith
  have h1b : 0 < 1 - β := by linarith
  have hm01 : 0 ≤ m01 := (abs_nonneg _).trans h01
  have hKg : 0 < σ * m00 + β / κ := by have : 0 < σ * m00 := by nlinarith
                                       positivity
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := by linarith
  have hG00 : |solveMN M (predN β σ) 0 0| ≤ β + σ * m01 / d := by
    simp only [solveMN, predN, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [← hd, abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hβ0, abs_of_pos hσ, abs_of_nonneg h11.1, add_mul,
      div_mul_cancel₀ _ hd0.ne']
    have := mul_le_mul_of_nonneg_right h01 hσ.le
    nlinarith [h11.2]
  have hG01 : |solveMN M (predN β σ) 0 1| ≤ m01 / d := by
    simp only [solveMN, predN, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', mul_zero, mul_one,
      zero_sub]
    rw [← hd, abs_div, abs_of_pos hd0]
    gcongr
    simpa using h01
  have hG10 : |solveMN M (predN β σ) 1 0| ≤ σ * m00 + β / κ := by
    simp only [solveMN, predN, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val']
    rw [← hd, abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos hβ0,
      abs_of_nonneg (by linarith [h00.1] : 0 ≤ M 0 0), abs_of_nonneg h10.1]
    have e1 : M 0 0 * σ ≤ σ * m00 * d := by
      have hmσ : 0 ≤ σ * m00 := by nlinarith [h00.1, h00.2]
      have a1 := mul_le_mul_of_nonneg_right h00.2 hσ.le
      have a2 := mul_le_mul_of_nonneg_left hd1 hmσ
      linarith
    have e2 : M 1 0 * β ≤ β / κ * d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hκ]; nlinarith [h10.2]
    have : (σ * m00 + β / κ) * d = σ * m00 * d + β / κ * d := by ring
    linarith
  have hG11 : |solveMN M (predN β σ) 1 1| ≤ m00 / d := by
    simp only [solveMN, predN, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', mul_one, mul_zero,
      sub_zero]
    rw [← hd, abs_div, abs_of_pos hd0, abs_of_nonneg (by linarith [h00.1] : 0 ≤ M 0 0)]
    gcongr
    exact h00.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : σ * m01 / d + m01 / d * W ≤ 1 - β := by
      rw [div_mul_eq_mul_div, ← add_div, div_le_iff₀ hd0]
      rw [div_le_iff₀ h1b] at hdA
      nlinarith
    have := mul_le_mul_of_nonneg_right hG01 hW0.le
    linarith
  · have e1 : |solveMN M (predN β σ) 1 0| / W ≤ 1 / 2 := by
      rw [div_le_iff₀ hW0, hW]; linarith
    have e2 : m00 / d ≤ 1 / 2 := by rw [div_le_iff₀ hd0]; linarith
    linarith
  · simp only [solvew, predB, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_zero, zero_sub]
    rw [← hd, abs_div, abs_of_pos hd0]
    gcongr
    rw [abs_neg, abs_mul, abs_of_pos hσ]
    have := mul_le_mul_of_nonneg_right h01 hσ.le
    have : 0 ≤ σ * m00 := by nlinarith
    linarith
  · simp only [solvew, predB, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_zero, sub_zero]
    rw [← hd, abs_div, abs_of_pos hd0, abs_mul, abs_of_pos hσ,
      abs_of_nonneg (by linarith [h00.1] : 0 ≤ M 0 0)]
    have h1 : M 0 0 * σ / d ≤ (σ * m01 + σ * m00) / d := by
      gcongr
      have : 0 ≤ σ * m01 := by positivity
      nlinarith [h00.2]
    have hm00 : 0 ≤ m00 := by linarith [h00.1, h00.2]
    have h2 : (σ * m01 + σ * m00) / d ≤ W * ((σ * m01 + σ * m00) / d) :=
      le_mul_of_one_le_left (div_nonneg (by positivity) hd0.le) hW1
    linarith

omit 𝔼 in
/-- Woodford (2003), p. 288: for the stable root of the inertial cubic with `λΦ ≤ K₁` and
`λ(1 + β + κσ) ≤ 1/2`, the coefficients satisfy `ω = (−a, −b)` with `0 ≤ a ≤ 2κσλ`,
`0 ≤ b ≤ 2σλ`. -/
theorem inert_omega_small {β σ κ l : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) (hl0 : 0 ≤ l)
    (hl : l * (1 + β + κ * σ) ≤ 1 / 2) :
    ∃ a b, inertOmega β σ κ l 0 = -a ∧ inertOmega β σ κ l 1 = -b ∧ 0 ≤ a ∧
      a ≤ 2 * κ * σ * l ∧ 0 ≤ b ∧ b ≤ 2 * σ * l := by
  set Q := (1 - β * l) * (1 - l) - κ * σ * l with hQ
  have hQh : 1 / 2 ≤ Q := by
    have : 0 ≤ β * l * l := by positivity
    nlinarith
  have hQ0 : 0 < Q := by linarith
  have hb1 : 0 ≤ 1 - β * l := by
    have : β * l ≤ l * (1 + β + κ * σ) := by
      nlinarith [mul_nonneg hl0 (by positivity : (0 : ℝ) ≤ 1 + κ * σ)]
    linarith
  refine ⟨κ * σ * l / Q, σ * l * (1 - β * l) / Q, by simp [inertOmega, hQ, neg_div],
    by simp [inertOmega, hQ, neg_div], by positivity, ?_, by positivity, ?_⟩
  · rw [div_le_iff₀ hQ0]; nlinarith [mul_nonneg (mul_nonneg hκ.le hσ.le) hl0]
  · rw [div_le_iff₀ hQ0]
    have : 0 ≤ σ * l := by positivity
    have : 0 ≤ β * l := by positivity
    nlinarith

set_option maxHeartbeats 1000000 in
-- the proof assembles many explicit inequalities in a single large context
omit 𝔼 in
/-- **Woodford (2003), p. 288, for the inertial rule (2.8) (proved here; the book asserts it).**
For fixed `β, σ, κ, ρ`, all response coefficients become uniformly small when
`Φ = κφ_π + (1 − β)φ_x/4` is large: for every `ε > 0` there is `K` such that `Φ ≥ K` implies (2.9),
the existence of the (unique) good decomposition, and, for it, `|ω_π|, |ω_x| < ε` and
`|ψ^π_j|, |ψ^x_j| < ε` for every horizon `j`. -/
theorem inert_coeffs_small {β σ κ ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, 0 < K ∧ ∀ φπ φx, 0 ≤ φπ → 0 ≤ φx → K ≤ κ * φπ + (1 - β) * φx / 4 →
      InertialTaylorPrinciple β κ ρ φπ φx ∧
      (∃ lam ω, GoodDecomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω) ∧
      ∀ lam ω, GoodDecomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω →
        (∀ k, |ω k| < ε) ∧ ∀ j k, |coef (solveMN (resM (inertP κ) (predN β σ) (a25 σ)
          (inertPhi φπ φx) ω) (predN β σ)) (solvew (resM (inertP κ) (predN β σ) (a25 σ)
            (inertPhi φπ φx) ω) (predB σ)) j k| < ε := by
  obtain ⟨K1, hK1, hK1p⟩ : ∃ K1, K1 = (ρ + 1) * (1 + κ * σ) / σ ∧ 0 < K1 :=
    ⟨_, rfl, by positivity⟩
  have h1b : 0 < 1 - β := by linarith
  obtain ⟨m00, hm00, hm00p⟩ : ∃ m, m = 1 + 2 * β * σ * K1 ∧ 1 ≤ m :=
    ⟨_, rfl, by have : 0 ≤ 2 * β * σ * K1 := by positivity
                linarith⟩
  obtain ⟨m01, hm01, hm01p⟩ : ∃ m, m = κ + 2 * β * κ * σ * K1 / (1 - β) ∧ 0 < m :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨W, hW, hW1⟩ : ∃ W, W = 2 * (σ * m00 + β / κ) + 1 ∧ 1 ≤ W :=
    ⟨_, rfl, by have : 0 ≤ σ * m00 + β / κ := by positivity
                linarith⟩
  obtain ⟨S, hS, hS0⟩ : ∃ S, S = σ * m01 + σ * m00 ∧ 0 < S := ⟨_, rfl, by positivity⟩
  have hW0 : 0 < W := by linarith
  obtain ⟨A, hA, hA0⟩ : ∃ A, A = ((σ + W) * m01 / (1 - β) + 2 * m00) / σ ∧ 0 ≤ A :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨B, hB, hB0⟩ : ∃ B, B = W * S / (σ * ε) ∧ 0 ≤ B := ⟨_, rfl, by positivity⟩
  obtain ⟨C, hC', hC0⟩ : ∃ C, C = 2 * (κ * σ + σ) * K1 / ε ∧ 0 ≤ C := ⟨_, rfl, by positivity⟩
  obtain ⟨D, hD', hD0⟩ : ∃ D, D = 2 * (1 + β + κ * σ) * K1 ∧ 0 ≤ D := ⟨_, rfl, by positivity⟩
  refine ⟨D + κ + A + B + C + 1, by linarith, ?_⟩
  intro φπ φx hφπ hφx hK
  obtain ⟨Φ, hΦ⟩ : ∃ Φ, Φ = κ * φπ + (1 - β) * φx / 4 := ⟨_, rfl⟩
  rw [← hΦ] at hK
  have hΦ0 : 0 < Φ := by linarith
  have hφ : 0 < φπ ∨ 0 < φx := by
    by_contra h
    push Not at h
    have e1 : φπ = 0 := le_antisymm h.1 hφπ
    have e2 : φx = 0 := le_antisymm h.2 hφx
    rw [hΦ, e1, e2] at hΦ0
    simp at hΦ0
  have hTP : InertialTaylorPrinciple β κ ρ φπ φx := by
    unfold InertialTaylorPrinciple
    have e : φπ + (1 - β) * φx / (4 * κ) = Φ / κ := by rw [hΦ]; field_simp
    rw [e, lt_div_iff₀ hκ]
    nlinarith
  obtain ⟨l, hCl, hl0, hl1, hβl, hQne⟩ := inert_root_exists hβ0 hβ1 hκ hσ hρ hφπ hφx hφ hTP
  have hDl := inert_decomp hκ.ne' hQne hCl
  obtain ⟨hd, hG⟩ := inert_forward_stable hβ0 hβ1 hκ hσ hρ hφπ hφx hTP hDl hl0 hl1 hβl
  have hgood : GoodDecomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ l
      (inertOmega β σ κ l) := ⟨hDl, by rw [abs_lt]; constructor <;> linarith, hd, hG⟩
  refine ⟨hTP, ⟨l, _, hgood⟩, fun lam ω hω => ?_⟩
  obtain ⟨e1, e2⟩ := decomp_unique (b := 0) hgood.1 hgood.2.1 hgood.2.2.1 hgood.2.2.2
    hω.1 hω.2.1 hω.2.2.1 hω.2.2.2
  subst e1 e2
  have hsmall := inert_root_small hβ0 hβ1 hκ hσ hρ hφx hl0 hl1 hCl
  have hlΦ : l * Φ ≤ K1 := by
    rw [hK1, le_div_iff₀ hσ]
    have : l * Φ * σ = l * σ * (κ * φπ + (1 - β) * φx / 4) := by rw [hΦ]; ring
    linarith
  have hl_small : l * (1 + β + κ * σ) ≤ 1 / 2 := by
    have h1 : l * D ≤ l * Φ := mul_le_mul_of_nonneg_left (by linarith) hl0
    rw [hD'] at h1
    have hK1l : l * (1 + β + κ * σ) * (2 * K1) ≤ K1 := by nlinarith
    nlinarith
  obtain ⟨a, b, ha, hb, ha0, ha2, hb0, hb2⟩ := inert_omega_small hβ0 hκ hσ hl0 hl_small
  obtain ⟨e00, e01, e10, e11, edet⟩ :=
    inert_M_explicit (β := β) (σ := σ) (κ := κ) (φπ := φπ) (φx := φx) ha hb
  -- products with `φ` are bounded
  have hlπ : l * (κ * φπ) ≤ K1 := by
    have : l * (κ * φπ) ≤ l * Φ := by
      apply mul_le_mul_of_nonneg_left _ hl0
      rw [hΦ]; have : 0 ≤ (1 - β) * φx / 4 := by positivity
      linarith
    linarith
  have hlx : l * ((1 - β) * φx / 4) ≤ K1 := by
    have : l * ((1 - β) * φx / 4) ≤ l * Φ := by
      apply mul_le_mul_of_nonneg_left _ hl0
      rw [hΦ]; have : 0 ≤ κ * φπ := by positivity
      linarith
    linarith
  have haπ : a * φπ ≤ 2 * σ * K1 :=
    calc a * φπ ≤ 2 * κ * σ * l * φπ := mul_le_mul_of_nonneg_right ha2 hφπ
      _ = 2 * σ * (l * (κ * φπ)) := by ring
      _ ≤ 2 * σ * K1 := mul_le_mul_of_nonneg_left hlπ (by positivity)
  have haX : β * a * φx / 4 ≤ 2 * β * κ * σ * K1 / (1 - β) := by
    rw [le_div_iff₀ h1b]
    calc β * a * φx / 4 * (1 - β) = β * (1 - β) / 4 * (a * φx) := by ring
      _ ≤ β * (1 - β) / 4 * (2 * κ * σ * l * φx) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha2 hφx) (by positivity)
      _ = 2 * β * κ * σ * (l * ((1 - β) * φx / 4)) := by ring
      _ ≤ 2 * β * κ * σ * K1 := mul_le_mul_of_nonneg_left hlx (by positivity)
  obtain ⟨M, hM⟩ : ∃ M, M = resM (inertP κ) (predN β σ) (a25 σ) (inertPhi φπ φx)
      (inertOmega β σ κ l) := ⟨_, rfl⟩
  rw [← hM] at e00 e01 e10 e11 edet
  rw [← hM]
  have hc0 : 0 ≤ σ + σ * a + b := by positivity
  have hcσ : σ ≤ σ + σ * a + b := by
    have : 0 ≤ σ * a := by positivity
    linarith
  have hdD : 1 + σ * Φ ≤ det2 M := by
    rw [edet, hΦ]
    have x1 : σ * ((1 - β) * φx / 4) ≤ (σ + σ * a + b) * φx / 4 := by
      have hbx : 0 ≤ β * φx := by positivity
      have : (1 - β) * φx ≤ φx := by linarith only [hbx]
      have y1 : σ * ((1 - β) * φx) ≤ σ * φx := mul_le_mul_of_nonneg_left this hσ.le
      have y2 : σ * φx ≤ (σ + σ * a + b) * φx := mul_le_mul_of_nonneg_right hcσ hφx
      linarith only [y1, y2]
    have x2 : σ * (κ * φπ) ≤ κ * (σ + σ * a + b) * φπ := by
      have := mul_le_mul_of_nonneg_right hcσ (by positivity : 0 ≤ κ * φπ)
      linarith only [this]
    have x3 : 0 ≤ β * a * φπ := by positivity
    linarith only [x1, x2, x3]
  have hσΦ : 0 ≤ σ * Φ := by positivity
  have hd1 : 1 ≤ det2 M := by linarith
  have h00 : 1 ≤ M 0 0 ∧ M 0 0 ≤ m00 := by
    rw [e00]; constructor
    · have : 0 ≤ β * a * φπ := by positivity
      linarith
    · rw [hm00]; nlinarith
  have h01 : |M 0 1| ≤ m01 := by
    rw [e01, hm01]
    have : 0 ≤ β * a * φx / 4 := by positivity
    rw [abs_le]; constructor <;> linarith
  have h10 : 0 ≤ M 1 0 ∧ κ * M 1 0 ≤ det2 M := by
    rw [e10, edet]; refine ⟨by positivity, ?_⟩
    have : 0 ≤ (σ + σ * a + b) * φx / 4 := by positivity
    have : 0 ≤ β * a * φπ := by positivity
    nlinarith
  have h11 : 0 ≤ M 1 1 ∧ M 1 1 ≤ det2 M := by
    rw [e11, edet]; refine ⟨by positivity, ?_⟩
    have : 0 ≤ β * a * φπ := by positivity
    have : 0 ≤ κ * (σ + σ * a + b) * φπ := by positivity
    linarith
  have hAσ : (σ + W) * m01 / (1 - β) + 2 * m00 ≤ σ * Φ := by
    have := (div_le_iff₀ hσ).mp (show ((σ + W) * m01 / (1 - β) + 2 * m00) / σ ≤ Φ by
      rw [← hA]; linarith)
    linarith
  have hdA : (σ + (2 * (σ * m00 + β / κ) + 1)) * m01 / (1 - β) ≤ det2 M := by
    rw [← hW]
    have : 0 ≤ 2 * m00 := by positivity
    linarith
  have hdB : 2 * m00 ≤ det2 M := by
    have : 0 ≤ (σ + W) * m01 / (1 - β) := by positivity
    linarith
  obtain ⟨c1, c2, hw0, hw1⟩ := forward_block_bounds hβ0 hβ1 hκ hσ hd1 h00 h01 h10 h11 hdA hdB
  rw [← hW] at c1 c2 hw1
  rw [← hS] at hw0 hw1
  have hBnd := coef_weighted_bound hW0 c1 c2 hw0 hw1
  have hd0 : 0 < det2 M := by linarith
  have hSd : W * (S / det2 M) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hd0]
    have hBΦ : B < Φ := by linarith only [hK, hA0, hC0, hD0, hκ]
    rw [hB, div_lt_iff₀ (by positivity)] at hBΦ
    have h1 : ε * (σ * Φ) ≤ ε * det2 M :=
      mul_le_mul_of_nonneg_left (by linarith only [hdD]) hε.le
    have h2 : 0 < ε := hε
    linarith only [hBΦ, h1, h2]
  have hSd' : S / det2 M < ε :=
    lt_of_le_of_lt (le_mul_of_one_le_left (by positivity) hW1) hSd
  refine ⟨fun k => ?_, fun j k => ?_⟩
  · have hlε : 2 * (κ * σ + σ) * l < ε := by
      have hCΦ : C < Φ := by linarith only [hK, hA0, hB0, hD0, hκ]
      rw [hC', div_lt_iff₀ hε] at hCΦ
      have h3 : 2 * (κ * σ + σ) * (l * Φ) ≤ 2 * (κ * σ + σ) * K1 :=
        mul_le_mul_of_nonneg_left hlΦ (by positivity)
      have h4 : 2 * (κ * σ + σ) * l * Φ < ε * Φ := by linarith only [hCΦ, h3]
      exact lt_of_mul_lt_mul_right h4 hΦ0.le
    fin_cases k
    · simp only [Fin.zero_eta]
      rw [ha, abs_neg, abs_of_nonneg ha0]
      have : 0 ≤ σ * l := by positivity
      linarith only [ha2, hlε, this]
    · simp only [Fin.mk_one]
      rw [hb, abs_neg, abs_of_nonneg hb0]
      have : 0 ≤ κ * σ * l := by positivity
      linarith only [hb2, hlε, this]
  · obtain ⟨b0, b1⟩ := hBnd j
    fin_cases k
    · exact lt_of_le_of_lt b0 hSd'
    · exact lt_of_le_of_lt b1 hSd

omit 𝔼 in
/-- **Woodford (2003), p. 288 (inertial rule, limit form).** For fixed `φ_x ≥ 0` (and fixed
`ρ ≥ 0`), as `φ_π → ∞` all coefficients `ω` and `ψ_j` of the inertial-rule solution tend to zero,
uniformly in the horizon `j`. -/
theorem inert_coeffs_tendsto_phiPi {β σ κ ρ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφx : 0 ≤ φx) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ φπ in atTop, (∃ lam ω, GoodDecomp (inertP κ) (predN β σ) 0 (a25 σ)
      (inertPhi φπ φx) ρ lam ω) ∧
      ∀ lam ω, GoodDecomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω →
        (∀ k, |ω k| < ε) ∧ ∀ j k, |coef (solveMN (resM (inertP κ) (predN β σ) (a25 σ)
          (inertPhi φπ φx) ω) (predN β σ)) (solvew (resM (inertP κ) (predN β σ) (a25 σ)
            (inertPhi φπ φx) ω) (predB σ)) j k| < ε := by
  obtain ⟨K, hK0, hK⟩ := inert_coeffs_small (σ := σ) hβ0 hβ1 hκ hσ hρ hε
  filter_upwards [eventually_ge_atTop (K / κ)] with φπ hφ
  have h0 : 0 ≤ φπ := le_trans (by positivity) hφ
  have := (div_le_iff₀ hκ).mp hφ
  have : 0 ≤ (1 - β) * φx / 4 := by have : 0 < 1 - β := by linarith
                                    positivity
  obtain ⟨-, h1, h2⟩ := hK φπ φx h0 hφx (by linarith)
  exact ⟨h1, h2⟩

omit 𝔼 in
/-- **Woodford (2003), p. 288 (inertial rule, limit form).** For fixed `φ_π ≥ 0` (and fixed
`ρ ≥ 0`), as `φ_x → ∞` all coefficients `ω` and `ψ_j` of the inertial-rule solution tend to zero,
uniformly in the horizon `j`. -/
theorem inert_coeffs_tendsto_phiX {β σ κ ρ φπ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hφπ : 0 ≤ φπ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ φx in atTop, (∃ lam ω, GoodDecomp (inertP κ) (predN β σ) 0 (a25 σ)
      (inertPhi φπ φx) ρ lam ω) ∧
      ∀ lam ω, GoodDecomp (inertP κ) (predN β σ) 0 (a25 σ) (inertPhi φπ φx) ρ lam ω →
        (∀ k, |ω k| < ε) ∧ ∀ j k, |coef (solveMN (resM (inertP κ) (predN β σ) (a25 σ)
          (inertPhi φπ φx) ω) (predN β σ)) (solvew (resM (inertP κ) (predN β σ) (a25 σ)
            (inertPhi φπ φx) ω) (predB σ)) j k| < ε := by
  obtain ⟨K, hK0, hK⟩ := inert_coeffs_small (σ := σ) hβ0 hβ1 hκ hσ hρ hε
  have h1b : 0 < 1 - β := by linarith
  filter_upwards [eventually_ge_atTop (4 * K / (1 - β))] with φx hφ
  have h0 : 0 ≤ φx := le_trans (by positivity) hφ
  have := (div_le_iff₀ h1b).mp hφ
  have : 0 ≤ κ * φπ := by positivity
  obtain ⟨-, h1, h2⟩ := hK φπ φx hφπ h0 (by nlinarith)
  exact ⟨h1, h2⟩

end Woodford.NeoWicksellianFramework.InflationDeterminants
