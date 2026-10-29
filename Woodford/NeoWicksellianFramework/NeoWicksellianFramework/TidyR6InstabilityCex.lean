/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.TidyR6Instability

/-!
# Counterexamples for the E-stability equation (2.20)

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, p. 266 and n. 37: the local stability
of the rest point `θ̄` of `θ̇ = T(θ) − θ` (2.20) "depends on the eigenvalues of the Jacobian
matrix `DT(θ̄) − I`", ignoring the non-generic case of eigenvalues with zero real part. The
module TidyR6Instability proves the exact equivalence in the generic case. This module shows that
its hypotheses cannot be dropped. Both examples work in every dimension (`ι` nonempty).

**Zero real part: the Jacobian does not decide** (`zero_re_undecided`,
`zero_re_undecided_complete`). The polynomial maps `T±(θ)ᵢ = θᵢ ± θᵢ³` (`cubT`), i.e.
`θ̇ᵢ = ±θᵢ³`, are `C¹` (indeed polynomial), have the rest point `0` and the same Jacobian
`DT±(0) = I`. So `DT − I = 0` has the single eigenvalue `0`, neither map is E-stable, and both
lie in the case excluded by n. 37.
* For `T₋` the rest point is locally asymptotically stable: `isLASLoc_cubT_neg`, by
  `d(θᵢ²)/dτ = −2θᵢ⁴` and the barrier `θᵢ² ≤ 1/(1 + τ)`.
* For `T₊` it is unstable: `not_isLASLoc_cubT_pos`, by the barrier `θᵢ ≥ a/2 + a³τ/16`.
* The same holds for `IsLAS` (solutions on `[0, ∞)`) for the globally Lipschitz,
  forward-complete modifications `T± ∘ clampBox`, which have the same Jacobian:
  `isLAS_tMod_cubT_neg`, `not_isLAS_tMod_cubT_pos`.

**Without forward completeness, `IsLAS` cannot detect instability** (`blowup_isLAS_unstable`).
For `T(θ)ᵢ = 2θᵢ + θᵢ|θᵢ|` (`blowT`), i.e. `θ̇ᵢ = θᵢ + θᵢ|θᵢ|`:
* `T` is Lipschitz near `0` and differentiable at `0`, with `DT(0) − I = I`. That is hyperbolic,
  with eigenvalue `1 > 0`, so the rest point is unstable in the textbook sense
  (`TidyR6Instability.not_isLASLoc_of_unstable`).
* Yet every forward solution on `[0, ∞)` is identically `0`, because any other solution blows up
  in finite time (`no_pos_blowup_sol`, `blowT_sol_eq_zero`). So `IsLAS T 0` holds vacuously
  (`isLAS_blowT`), and the equation is not forward complete.
* The forward-completeness hypothesis of `TidyR6Instability.eStableAt_iff_isLAS` is therefore
  necessary.
-/

namespace Woodford.NeoWicksellianFramework.TidyR6InstabilityCex

open Filter Topology TidyR5Lyapunov TidyR6ODEExistence TidyR6Instability
open Determinacy2Learning (EStable EStableAt)
open KroneckerSpectrum (IsEig)
open scoped NNReal

variable {ι : Type*} [Fintype ι]

/-! ### General lemmas -/

/-- Woodford (2003), p. 266: a map with `N(0) = 0` and `‖N(x)‖ ≤ C‖x‖²` for `‖x‖ ≤ 1` has
derivative `0` at `0`. -/
theorem hasFDerivAt_of_quad {N : (ι → ℝ) → ι → ℝ} {C : ℝ} (h0 : N 0 = 0)
    (hb : ∀ x : ι → ℝ, ‖x‖ ≤ 1 → ‖N x‖ ≤ C * ‖x‖ ^ 2) :
    HasFDerivAt N (0 : (ι → ℝ) →L[ℝ] (ι → ℝ)) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, h0, sub_zero, zero_apply]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hC : 0 < |C| + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ι → ℝ) (lt_min one_pos (div_pos hc hC))] with x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  have h1 : ‖x‖ < 1 := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : ‖x‖ < c / (|C| + 1) := lt_of_lt_of_le hx (min_le_right _ _)
  have h3 := hb x h1.le
  have h4 : ‖x‖ * (|C| + 1) ≤ c := by
    rw [lt_div_iff₀ hC] at h2
    exact h2.le
  have hn := norm_nonneg x
  have h5 : C * ‖x‖ ^ 2 ≤ (|C| + 1) * ‖x‖ * ‖x‖ := by
    nlinarith [le_abs_self C, abs_nonneg C]
  calc ‖N x‖ ≤ (|C| + 1) * ‖x‖ * ‖x‖ := h3.trans h5
    _ = (‖x‖ * (|C| + 1)) * ‖x‖ := by ring
    _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_right h4 hn

/-- Woodford (2003), p. 266: if `DT(0) = a I`, the Jacobian matrix is `a I`. -/
theorem jac_of_hasFDerivAt [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {a : ℝ}
    (hT : HasFDerivAt T (a • ContinuousLinearMap.id ℝ (ι → ℝ)) 0) :
    jac T 0 = a • (1 : Matrix ι ι ℝ) := by
  rw [jac, hT.fderiv]
  have : ((a • ContinuousLinearMap.id ℝ (ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ)) :
      (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) = a • LinearMap.id := by
    ext x i
    simp
  rw [this, map_smul, LinearMap.toMatrix'_id]

/-- Woodford (2003), p. 266: the eigenvalues of `aI − I` are exactly `a − 1` (`ι` nonempty). -/
theorem isEig_smul_one_sub_one_iff [DecidableEq ι] [Nonempty ι] (a : ℝ) (ν : ℂ) :
    IsEig ((a • (1 : Matrix ι ι ℝ) - 1).map Complex.ofReal) ν ↔ ν = a - 1 := by
  have hm : (a • (1 : Matrix ι ι ℝ) - 1).map Complex.ofReal = ((a : ℂ) - 1) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [hm]
  constructor
  · rintro ⟨v, hv0, hv⟩
    rw [Matrix.smul_mulVec, Matrix.one_mulVec] at hv
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have := congrFun hv i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this hi
    exact (mul_right_cancel₀ hi this).symm
  · rintro rfl
    refine ⟨fun _ => 1, fun h => ?_, by rw [Matrix.smul_mulVec, Matrix.one_mulVec]⟩
    have := congrFun h (Classical.arbitrary ι)
    simp at this

/-! ### Without forward completeness: a blow-up example -/

/-- Woodford (2003), (2.20): the nonlinear part `θᵢ|θᵢ|` of the blow-up example. -/
def blowN (x : ι → ℝ) : ι → ℝ := fun i => x i * |x i|

/-- Woodford (2003), (2.20): the blow-up example `T(θ) = 2θ + θ|θ|` (coordinatewise), so that
(2.20) reads `θ̇ᵢ = θᵢ + θᵢ|θᵢ|`. -/
def blowT (x : ι → ℝ) : ι → ℝ := (2 : ℝ) • x + blowN x

omit [Fintype ι] in
/-- Woodford (2003), (2.20): `0` is a rest point of the blow-up example. -/
theorem blowT_zero : blowT (0 : ι → ℝ) = 0 := by
  funext i
  simp [blowT, blowN]

/-- Woodford (2003), (2.20): `‖θ|θ|‖ ≤ ‖θ‖²` (sup norm). -/
theorem norm_blowN_le (x : ι → ℝ) : ‖blowN x‖ ≤ ‖x‖ ^ 2 := by
  refine (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2 fun i => ?_
  have hi : |x i| ≤ ‖x‖ := by
    have := norm_le_pi_norm x i
    rwa [Real.norm_eq_abs] at this
  simp only [blowN, Real.norm_eq_abs, abs_mul, abs_abs]
  rw [← sq]
  exact pow_le_pow_left₀ (abs_nonneg _) hi 2

set_option linter.unusedFintypeInType false in
/-- Woodford (2003), p. 266: `DT(0) = 2I` for the blow-up example. -/
theorem hasFDerivAt_blowT :
    HasFDerivAt (blowT (ι := ι)) ((2 : ℝ) • ContinuousLinearMap.id ℝ (ι → ℝ)) 0 := by
  have hN : HasFDerivAt (blowN (ι := ι)) (0 : (ι → ℝ) →L[ℝ] (ι → ℝ)) 0 :=
    hasFDerivAt_of_quad (C := 1) (by funext i; simp [blowN])
      fun x _ => by rw [one_mul]; exact norm_blowN_le x
  have h := ((hasFDerivAt_id (0 : ι → ℝ)).const_smul (2 : ℝ)).add hN
  rw [add_zero] at h
  exact h

/-- Woodford (2003), (2.20): `|a|a| − b|b|| ≤ 2|a − b|` for `|a|, |b| ≤ 1`. -/
theorem abs_mul_abs_sub_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a * abs a - b * abs b| ≤ 2 * |a - b| := by
  rw [abs_le] at ha hb
  rcases le_total 0 a with h1 | h1 <;> rcases le_total 0 b with h2 | h2
  · rw [abs_of_nonneg h1, abs_of_nonneg h2]
    rw [show a * a - b * b = (a - b) * (a + b) by ring, abs_mul]
    have : |a + b| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (a - b)]
  · rw [abs_of_nonneg h1, abs_of_nonpos h2, abs_of_nonneg (by linarith : 0 ≤ a - b),
      abs_of_nonneg (by nlinarith : 0 ≤ a * a - b * -b)]
    nlinarith
  · rw [abs_of_nonpos h1, abs_of_nonneg h2, abs_of_nonpos (by linarith : a - b ≤ 0),
      abs_of_nonpos (by nlinarith : a * -a - b * b ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos h1, abs_of_nonpos h2]
    rw [show a * -a - b * -b = (b - a) * (a + b) by ring, abs_mul, abs_sub_comm b a]
    have : |a + b| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (a - b)]

/-- Woodford (2003), (2.20): the blow-up example is `4`-Lipschitz on the closed unit ball. -/
theorem lipschitzOnWith_blowT :
    LipschitzOnWith 4 (blowT (ι := ι)) (Metric.closedBall 0 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hx hy
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  have hxi : |x i| ≤ 1 := by
    have := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at this
    linarith
  have hyi : |y i| ≤ 1 := by
    have := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at this
    linarith
  have hd : |x i - y i| ≤ dist x y := by
    rw [← Real.dist_eq]
    exact dist_le_pi_dist x y i
  simp only [blowT, blowN, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Real.dist_eq]
  have h1 := abs_mul_abs_sub_le hxi hyi
  have h2 : |2 * x i + x i * abs (x i) - (2 * y i + y i * abs (y i))| ≤
      2 * |x i - y i| + |x i * abs (x i) - y i * abs (y i)| := by
    have := abs_add_le (2 * (x i - y i)) (x i * abs (x i) - y i * abs (y i))
    rw [abs_mul, abs_two] at this
    calc _ = |2 * (x i - y i) + (x i * |x i| - y i * |y i|)| := by ring_nf
      _ ≤ _ := this
  push_cast
  linarith

/-- Woodford (2003), (2.20): **finite-time blow-up**: no continuous `y` on `[0, ∞)` with right
derivatives `y + y|y|` starts at a positive value (it would satisfy `y(τ) ≥ c/(1 − cτ)`,
`c = y(0)`, and explode before `τ = 1/c`). -/
theorem no_pos_blowup_sol {y : ℝ → ℝ} (hc : ContinuousOn y (Set.Ici 0))
    (hd : ∀ τ, 0 ≤ τ → HasDerivWithinAt y (y τ + y τ * |y τ|) (Set.Ici τ) τ) : y 0 ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set c := y 0 with hcdef
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / c)).exists_bound_of_continuousOn
    (hc.mono Set.Icc_subset_Ici_self)
  have hcM : c ≤ M := by
    have := hM 0 ⟨le_rfl, by positivity⟩
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self c).trans this
  have hM1 : 0 < M + 1 := by linarith
  set s₁ := 1 / c - 1 / (M + 1) with hs₁
  have hlt : 1 / (M + 1) < 1 / c := one_div_lt_one_div_of_lt hpos (by linarith)
  have hs₁0 : 0 ≤ s₁ := by rw [hs₁]; linarith
  have hs₁c : s₁ < 1 / c := by rw [hs₁]; linarith [one_div_pos.mpr hM1]
  have hden : ∀ t, t ≤ s₁ → 0 < 1 - c * t := by
    intro t ht
    have : c * t < 1 := by
      calc c * t ≤ c * s₁ := mul_le_mul_of_nonneg_left ht hpos.le
        _ < c * (1 / c) := mul_lt_mul_of_pos_left hs₁c hpos
        _ = 1 := mul_one_div_cancel hpos.ne'
    linarith
  -- the lower barrier `y(t) ≥ c / (1 − c t)` on `[0, s₁]`
  have hbar : ∀ t ∈ Set.Icc 0 s₁, -y t ≤ -(c / (1 - c * t)) := by
    have hf : ContinuousOn (fun t => -y t) (Set.Icc 0 s₁) :=
      (hc.mono Set.Icc_subset_Ici_self).neg
    have hf' : ∀ t ∈ Set.Ico 0 s₁, HasDerivWithinAt (fun t => -y t)
        (-(y t + y t * |y t|)) (Set.Ici t) t := fun t ht => (hd t ht.1).neg
    have hBd : ∀ t, t ≤ s₁ → HasDerivAt (fun t => -(c * (1 - c * t)⁻¹))
        (-(c / (1 - c * t)) ^ 2) t := by
      intro t ht
      have hne := (hden t ht).ne'
      have h1 := ((((hasDerivAt_id' t).const_mul c).const_sub 1).inv hne).const_mul c |>.neg
      refine h1.congr_deriv ?_
      field_simp
    have hB : ContinuousOn (fun t => -(c * (1 - c * t)⁻¹)) (Set.Icc 0 s₁) :=
      fun t ht => (hBd t ht.2).continuousAt.continuousWithinAt
    have hB' : ∀ t ∈ Set.Ico 0 s₁, HasDerivWithinAt (fun t => -(c * (1 - c * t)⁻¹))
        (-(c / (1 - c * t)) ^ 2) (Set.Ici t) t :=
      fun t ht => (hBd t ht.2.le).hasDerivWithinAt
    intro t ht
    rw [div_eq_mul_inv]
    refine image_le_of_deriv_right_lt_deriv_boundary' hf hf' ?_ hB hB' ?_ ht
    · simp [hcdef]
    · intro t ht hcon
      have hyt : y t = c / (1 - c * t) := by rw [div_eq_mul_inv]; linarith
      have hbpos : 0 < c / (1 - c * t) := div_pos hpos (hden t ht.2.le)
      rw [hyt, abs_of_pos hbpos]
      nlinarith
  have h1 := hbar s₁ ⟨hs₁0, le_rfl⟩
  have h2 : c / (1 - c * s₁) = M + 1 := by
    have hc0 : c ≠ 0 := hpos.ne'
    have hM0 : M + 1 ≠ 0 := hM1.ne'
    have e : 1 - c * s₁ = c / (M + 1) := by
      rw [hs₁, mul_sub, mul_one_div_cancel hc0]
      ring
    rw [e, div_div_eq_mul_div, mul_div_cancel_left₀ _ hc0]
  have h3 := hM s₁ ⟨hs₁0, hs₁c.le⟩
  rw [Real.norm_eq_abs] at h3
  have := le_abs_self (y s₁)
  linarith

set_option linter.unusedFintypeInType false in
/-- Woodford (2003), (2.20): in the blow-up example every forward solution on `[0, ∞)` is
identically `0` (any non-zero coordinate, shifted in time, would blow up in finite time). -/
theorem blowT_sol_eq_zero {θ : ℝ → ι → ℝ} (h : IsFwdSol blowT θ) :
    ∀ t, 0 ≤ t → θ t = 0 := by
  intro t ht
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hs := isFwdSol_shift h ht
  have hci : ContinuousOn (fun s => θ (t + s) i) (Set.Ici 0) :=
    (continuous_apply i).comp_continuousOn hs.1
  have hdi : ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => θ (t + s) i)
      (θ (t + τ) i + θ (t + τ) i * |θ (t + τ) i|) (Set.Ici τ) τ := by
    intro τ hτ
    have := hasDerivWithinAt_pi.1 (hs.2 τ hτ) i
    convert this using 1
    simp only [blowT, blowN, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hc' : ContinuousOn (fun s => -θ (t + s) i) (Set.Ici 0) := hci.neg
    have hd' : ∀ τ, 0 ≤ τ → HasDerivWithinAt (fun s => -θ (t + s) i)
        (-θ (t + τ) i + -θ (t + τ) i * |-θ (t + τ) i|) (Set.Ici τ) τ := by
      intro τ hτ
      convert (hdi τ hτ).neg using 1
      rw [abs_neg]
      ring
    have := no_pos_blowup_sol hc' hd'
    simp only [add_zero, Pi.zero_apply] at this hneg
    linarith
  · have := no_pos_blowup_sol hci hdi
    simp only [add_zero, Pi.zero_apply] at this hpos
    linarith

/-- Woodford (2003), p. 264: in the blow-up example `0` is (vacuously) a locally asymptotically
stable rest point in the sense of `IsLAS`: the only forward solution on `[0, ∞)` is `0`. -/
theorem isLAS_blowT : IsLAS (blowT (ι := ι)) 0 := by
  refine ⟨fun ε hε => ⟨1, one_pos, fun θ hθ _ τ hτ => ?_⟩, ⟨1, one_pos, fun θ hθ _ => ?_⟩⟩
  · rw [blowT_sol_eq_zero hθ τ hτ, sub_zero, norm_zero]
    exact hε
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact (blowT_sol_eq_zero hθ τ hτ).symm

set_option linter.unusedFintypeInType false in
/-- Woodford (2003), (2.20): the blow-up example is not forward complete. -/
theorem not_fwdComplete_blowT [Nonempty ι] : ¬FwdComplete (blowT (ι := ι)) := by
  intro hc
  obtain ⟨θ, hθ, h0⟩ := hc (fun _ => 1)
  have := congrFun (h0.symm.trans (blowT_sol_eq_zero hθ 0 le_rfl)) (Classical.arbitrary ι)
  simp at this

/-- Woodford (2003), p. 266 and n. 37: **without forward completeness `IsLAS` cannot detect
instability**: the blow-up example has the rest point `0`, is Lipschitz near `0` and differentiable
at `0`, and `DT(0) − I = I` is hyperbolic with the eigenvalue `1 > 0`. So `0` is not E-stable and
not a (textbook) locally stable rest point; yet `IsLAS` holds, because no non-constant forward
solution on `[0, ∞)` exists. -/
theorem blowup_isLAS_unstable [DecidableEq ι] [Nonempty ι] :
    blowT (0 : ι → ℝ) = 0 ∧ DifferentiableAt ℝ (blowT (ι := ι)) 0 ∧
      LipschitzOnWith 4 (blowT (ι := ι)) (Metric.closedBall 0 1) ∧
      NoZeroRe (jac (blowT (ι := ι)) 0) ∧
      IsEig ((jac (blowT (ι := ι)) 0 - 1).map Complex.ofReal) 1 ∧
      ¬EStableAt (blowT (ι := ι)) 0 ∧ IsLAS (blowT (ι := ι)) 0 ∧
      ¬IsLASLoc (blowT (ι := ι)) 0 ∧ ¬FwdComplete (blowT (ι := ι)) := by
  have hJ := jac_of_hasFDerivAt (hasFDerivAt_blowT (ι := ι))
  have heig : ∀ ν, IsEig ((jac (blowT (ι := ι)) 0 - 1).map Complex.ofReal) ν ↔ ν = 1 := by
    intro ν
    rw [hJ, isEig_smul_one_sub_one_iff]
    norm_num
  have h1 : IsEig ((jac (blowT (ι := ι)) 0 - 1).map Complex.ofReal) 1 := (heig 1).2 rfl
  refine ⟨blowT_zero, hasFDerivAt_blowT.differentiableAt, lipschitzOnWith_blowT,
    fun ν hν => by rw [(heig ν).1 hν]; norm_num, h1, fun hE => ?_, isLAS_blowT,
    not_isLASLoc_of_unstable one_pos lipschitzOnWith_blowT blowT_zero
      hasFDerivAt_blowT.differentiableAt h1 (by norm_num), not_fwdComplete_blowT⟩
  have := hE.2.2 1 h1
  norm_num at this

/-! ### Zero real part: `θ̇ = ±θ³` -/

/-- Woodford (2003), n. 37 p. 266: the maps `T±(θ)ᵢ = θᵢ + s θᵢ³` (`s = ±1`), so that (2.20)
reads `θ̇ᵢ = s θᵢ³`. -/
def cubT (s : ℝ) (x : ι → ℝ) : ι → ℝ := fun i => x i + s * x i ^ 3

omit [Fintype ι] in
/-- Woodford (2003), n. 37: `0` is a rest point of `T±`. -/
theorem cubT_zero (s : ℝ) : cubT s (0 : ι → ℝ) = 0 := by
  funext i
  simp [cubT]

/-- Woodford (2003), n. 37: `T±` is `C¹` (it is polynomial). -/
theorem contDiff_cubT (s : ℝ) : ContDiff ℝ 1 (cubT (ι := ι) s) :=
  contDiff_pi.2 fun i =>
    (contDiff_apply ℝ ℝ i).add (contDiff_const.mul ((contDiff_apply ℝ ℝ i).pow 3))

set_option linter.unusedFintypeInType false in
/-- Woodford (2003), n. 37: `DT±(0) = I`. -/
theorem hasFDerivAt_cubT (s : ℝ) :
    HasFDerivAt (cubT (ι := ι) s) ((1 : ℝ) • ContinuousLinearMap.id ℝ (ι → ℝ)) 0 := by
  have hN : HasFDerivAt (fun x : ι → ℝ => fun i => s * x i ^ 3)
      (0 : (ι → ℝ) →L[ℝ] (ι → ℝ)) 0 := by
    refine hasFDerivAt_of_quad (C := |s|) (by funext i; simp) fun x hx => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have hi : |x i| ≤ ‖x‖ := by
      have := norm_le_pi_norm x i
      rwa [Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h3 : |x i| ^ 3 ≤ ‖x‖ ^ 2 := by
      calc |x i| ^ 3 ≤ ‖x‖ ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hi 3
        _ = ‖x‖ ^ 2 * ‖x‖ := by ring
        _ ≤ ‖x‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
        _ = ‖x‖ ^ 2 := mul_one _
    exact mul_le_mul_of_nonneg_left h3 (abs_nonneg s)
  have h := (hasFDerivAt_id (0 : ι → ℝ)).add hN
  convert h using 1
  · funext x
    funext i
    simp [cubT]
  · simp

/-- Woodford (2003), (2.20): `|a³ − b³| ≤ 3|a − b|` for `|a|, |b| ≤ 1`. -/
theorem abs_cube_sub_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a ^ 3 - b ^ 3| ≤ 3 * |a - b| := by
  rw [show a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) by ring, abs_mul]
  have h : |a ^ 2 + a * b + b ^ 2| ≤ 3 := by
    rw [abs_le] at ha hb ⊢
    constructor <;> nlinarith
  nlinarith [abs_nonneg (a - b)]

/-- Woodford (2003), (2.20): for `|s| ≤ 1`, `T±` is `4`-Lipschitz on the closed unit ball. -/
theorem lipschitzOnWith_cubT {s : ℝ} (hs : |s| ≤ 1) :
    LipschitzOnWith 4 (cubT (ι := ι) s) (Metric.closedBall 0 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right] at hx hy
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  have hxi : |x i| ≤ 1 := by
    have := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at this
    linarith
  have hyi : |y i| ≤ 1 := by
    have := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at this
    linarith
  have hd : |x i - y i| ≤ dist x y := by
    rw [← Real.dist_eq]
    exact dist_le_pi_dist x y i
  simp only [cubT, Real.dist_eq]
  have h1 := abs_cube_sub_le hxi hyi
  have h2 : |x i + s * x i ^ 3 - (y i + s * y i ^ 3)| ≤
      |x i - y i| + |s| * |x i ^ 3 - y i ^ 3| := by
    have := abs_add_le (x i - y i) (s * (x i ^ 3 - y i ^ 3))
    rw [abs_mul] at this
    calc _ = |x i - y i + s * (x i ^ 3 - y i ^ 3)| := by ring_nf
      _ ≤ _ := this
  have h3 : |s| * |x i ^ 3 - y i ^ 3| ≤ 3 * |x i - y i| := by
    calc |s| * |x i ^ 3 - y i ^ 3| ≤ 1 * |x i ^ 3 - y i ^ 3| :=
          mul_le_mul_of_nonneg_right hs (abs_nonneg _)
      _ ≤ 3 * |x i - y i| := by rw [one_mul]; exact h1
  push_cast
  linarith

omit [Fintype ι] in
/-- Woodford (2003), n. 37: along a solution of `θ̇ᵢ = −θᵢ³` on `[0, t₁]`, each `θᵢ²` is
non-increasing. -/
theorem sq_le_of_isSolOn_cubT_neg {θ : ℝ → ι → ℝ} {t₁ : ℝ} (h : IsSolOn (cubT (-1)) θ t₁)
    (i : ι) : ∀ t ∈ Set.Icc 0 t₁, θ t i ^ 2 ≤ θ 0 i ^ 2 := by
  have hc : ContinuousOn (fun t => θ t i ^ 2) (Set.Icc 0 t₁) :=
    ((continuous_apply i).comp_continuousOn h.1).pow 2
  have hd : ∀ t ∈ Set.Ico 0 t₁, HasDerivWithinAt (fun t => θ t i ^ 2)
      (-(2 * θ t i ^ 4)) (Set.Ici t) t := by
    intro t ht
    have h1 := (hasDerivWithinAt_pi.1 (h.2 t ht) i).pow 2
    convert h1 using 1
    simp only [cubT, Pi.sub_apply]
    ring
  refine image_le_of_deriv_right_le_deriv_boundary hc hd le_rfl continuousOn_const
    (fun t _ => hasDerivWithinAt_const t _ _) fun t _ => ?_
  nlinarith [pow_two_nonneg (θ t i ^ 2)]

/-- Woodford (2003), n. 37: along a solution of `θ̇ᵢ = −θᵢ³` on `[0, t₁]`, `‖θ(t)‖ ≤ ‖θ(0)‖`. -/
theorem norm_le_of_isSolOn_cubT_neg {θ : ℝ → ι → ℝ} {t₁ : ℝ} (h : IsSolOn (cubT (-1)) θ t₁) :
    ∀ t ∈ Set.Icc 0 t₁, ‖θ t‖ ≤ ‖θ 0‖ := by
  intro t ht
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 := sq_le_of_isSolOn_cubT_neg h i t ht
  have h2 : |θ t i| ≤ |θ 0 i| := sq_le_sq.mp h1
  have h3 := norm_le_pi_norm (θ 0) i
  rw [Real.norm_eq_abs] at h3 ⊢
  linarith

/-- Woodford (2003), n. 37: **`θ̇ = −θ³` is locally asymptotically stable** at `0` (textbook
sense), although `DT(0) − I = 0` is not E-stable. -/
theorem isLASLoc_cubT_neg : IsLASLoc (cubT (ι := ι) (-1)) 0 := by
  refine ⟨fun ε hε => ⟨ε, hε, fun t₁ θ hθ h0 τ hτ => ?_⟩, ⟨1, one_pos, fun θ hθ h0 => ?_⟩⟩
  · rw [sub_zero] at h0 ⊢
    exact lt_of_le_of_lt (norm_le_of_isSolOn_cubT_neg hθ τ hτ) h0
  · rw [sub_zero] at h0
    rw [tendsto_pi_nhds]
    intro i
    have hbar : ∀ t, 0 ≤ t → θ t i ^ 2 ≤ (1 + t)⁻¹ := by
      intro t ht
      have hsol := isSolOn_of_isFwdSol hθ t
      have hc : ContinuousOn (fun t => θ t i ^ 2) (Set.Icc 0 t) :=
        ((continuous_apply i).comp_continuousOn hsol.1).pow 2
      have hd : ∀ u ∈ Set.Ico 0 t, HasDerivWithinAt (fun t => θ t i ^ 2)
          (-(2 * (θ u i ^ 2) ^ 2)) (Set.Ici u) u := by
        intro u hu
        have h1 := (hasDerivWithinAt_pi.1 (hsol.2 u hu) i).pow 2
        convert h1 using 1
        simp only [cubT, Pi.sub_apply]
        ring
      have hBd : ∀ u, 0 ≤ u → HasDerivAt (fun u : ℝ => (1 + u)⁻¹) (-((1 + u)⁻¹) ^ 2) u := by
        intro u hu
        have hne : (1 + u) ≠ 0 := by positivity
        have h1 := ((hasDerivAt_id' u).const_add 1).inv hne
        refine h1.congr_deriv ?_
        field_simp
      have hB : ContinuousOn (fun u : ℝ => (1 + u)⁻¹) (Set.Icc 0 t) :=
        fun u hu => (hBd u hu.1).continuousAt.continuousWithinAt
      refine image_le_of_deriv_right_lt_deriv_boundary' hc hd ?_ hB
        (fun u hu => (hBd u hu.1).hasDerivWithinAt) ?_ ⟨ht, le_rfl⟩
      · have h1 : |θ 0 i| < 1 := by
          have := norm_le_pi_norm (θ 0) i
          rw [Real.norm_eq_abs] at this
          linarith
        have h2 : θ 0 i ^ 2 < 1 := by
          have := sq_lt_sq' (by linarith [abs_nonneg (θ 0 i), neg_abs_le (θ 0 i)])
            (lt_of_le_of_lt (le_abs_self _) h1)
          simpa using this
        simp only [add_zero, inv_one]
        exact h2.le
      · intro u hu hcon
        have hpos : 0 < (1 + u)⁻¹ := by have := hu.1; positivity
        rw [hcon]
        nlinarith [sq_pos_of_pos hpos]
    have hlim : Tendsto (fun t : ℝ => Real.sqrt (1 + t)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => (1 + t)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 tendsto_id)
      simpa using h1.sqrt
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (hbar t ht)

/-- Woodford (2003), n. 37: along a solution of `θ̇ᵢ = θᵢ³` starting at the constant `a > 0`,
the state cannot stay within distance `1/2` of `0` forever (`θᵢ ≥ a/2 + a³τ/16`). -/
theorem escape_cubT_pos [Nonempty ι] {θ : ℝ → ι → ℝ} (h : IsFwdSol (cubT 1) θ) {a : ℝ}
    (ha : 0 < a) (h0 : θ 0 = fun _ => a) : ∃ τ, 0 ≤ τ ∧ 1 / 2 ≤ ‖θ τ‖ := by
  by_contra hcon
  push Not at hcon
  set i := Classical.arbitrary ι
  have hbar : ∀ t, 0 ≤ t → -θ t i ≤ -(a / 2 + a ^ 3 / 16 * t) := by
    intro t ht
    have hc : ContinuousOn (fun t => -θ t i) (Set.Icc 0 t) :=
      ((continuous_apply i).comp_continuousOn (h.1.mono Set.Icc_subset_Ici_self)).neg
    have hd : ∀ u ∈ Set.Ico 0 t, HasDerivWithinAt (fun t => -θ t i) (-(θ u i ^ 3))
        (Set.Ici u) u := by
      intro u hu
      have h1 := (hasDerivWithinAt_pi.1 (h.2 u hu.1) i).neg
      convert h1 using 1
      simp only [cubT, Pi.sub_apply]
      ring
    have hB : ∀ u, HasDerivAt (fun u => -(a / 2 + a ^ 3 / 16 * u)) (-(a ^ 3 / 16 * 1)) u :=
      fun u => (((hasDerivAt_id u).const_mul (a ^ 3 / 16)).const_add (a / 2)).neg
    refine image_le_of_deriv_right_lt_deriv_boundary hc hd ?_ hB ?_ ⟨ht, le_rfl⟩
    · rw [h0]
      simp only [mul_zero, add_zero, neg_le_neg_iff]
      linarith
    · intro u hu hcontact
      have hyu : θ u i = a / 2 + a ^ 3 / 16 * u := by linarith
      have hge : a / 2 ≤ θ u i := by
        rw [hyu]
        have := hu.1
        nlinarith [pow_pos ha 3]
      have h3 : (a / 2) ^ 3 ≤ θ u i ^ 3 := pow_le_pow_left₀ (by positivity) hge 3
      nlinarith [pow_pos ha 3]
  set t := 16 / a ^ 3 with ht
  have ht0 : 0 ≤ t := by positivity
  have h1 := hbar t ht0
  have h2 : a ^ 3 / 16 * t = 1 := by rw [ht]; field_simp
  have h3 := hcon t ht0
  have h4 := norm_le_pi_norm (θ t) i
  rw [Real.norm_eq_abs] at h4
  have h5 := le_abs_self (θ t i)
  linarith

/-- Woodford (2003), n. 37: for the globally Lipschitz modification of `θ̇ = θ³`, `0` is not a
locally asymptotically stable rest point in the sense of `IsLAS`. -/
theorem not_isLAS_tMod_cubT_pos [Nonempty ι] : ¬IsLAS (tMod (cubT (ι := ι) 1) 0 1) 0 := by
  intro hL
  obtain ⟨δ, hδ, hst⟩ := hL.1 (1 / 2) (by norm_num)
  set a := min (δ / 2) (1 / 4) with ha
  have ha0 : 0 < a := lt_min (by positivity) (by norm_num)
  obtain ⟨θ, hθ, hθ0⟩ := fwdComplete_tMod (r := 1) zero_le_one
    (lipschitzOnWith_cubT (s := 1) (by norm_num)) (fun _ : ι => a)
  have hn0 : ‖θ 0 - 0‖ < δ := by
    rw [hθ0, sub_zero, pi_norm_const, Real.norm_eq_abs, abs_of_pos ha0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hstay : ∀ τ, 0 ≤ τ → ‖θ τ - 0‖ < 1 / 2 := hst θ hθ hn0
  have hsol : IsFwdSol (cubT 1) θ :=
    isFwdSol_of_isFwdSol_tMod hθ fun t ht => by linarith [hstay t ht]
  obtain ⟨τ, hτ, hesc⟩ := escape_cubT_pos hsol ha0 hθ0
  have := hstay τ hτ
  rw [sub_zero] at this
  linarith

/-- Woodford (2003), n. 37: **`θ̇ = θ³` is unstable** at `0` (textbook sense), although it has
the same Jacobian as the stable `θ̇ = −θ³`. -/
theorem not_isLASLoc_cubT_pos [Nonempty ι] : ¬IsLASLoc (cubT (ι := ι) 1) 0 := fun h =>
  not_isLAS_tMod_cubT_pos ((isLAS_tMod_iff one_pos (lipschitzOnWith_cubT (by norm_num))).2 h)

/-- Woodford (2003), n. 37: for the globally Lipschitz modification of `θ̇ = −θ³`, `0` is a
locally asymptotically stable rest point in the sense of `IsLAS`. -/
theorem isLAS_tMod_cubT_neg : IsLAS (tMod (cubT (ι := ι) (-1)) 0 1) 0 :=
  (isLAS_tMod_iff one_pos (lipschitzOnWith_cubT (by norm_num))).2 isLASLoc_cubT_neg

/-- Woodford (2003), p. 266 and n. 37: **the zero-real-part case is not decided by `DT`**: the
polynomial maps `T±(θ) = θ ± θ³` both have the rest point `0` and the same Jacobian `DT(0) = I`,
so `DT(0) − I = 0` has the eigenvalue `0` on the imaginary axis and neither map is E-stable; yet
`0` is a locally asymptotically stable rest point of (2.20) for `T₋` and an unstable one for
`T₊`. -/
theorem zero_re_undecided [DecidableEq ι] [Nonempty ι] :
    ContDiff ℝ 1 (cubT (ι := ι) 1) ∧ ContDiff ℝ 1 (cubT (ι := ι) (-1)) ∧
      cubT (ι := ι) 1 0 = 0 ∧ cubT (ι := ι) (-1) 0 = 0 ∧
      fderiv ℝ (cubT (ι := ι) 1) 0 = fderiv ℝ (cubT (ι := ι) (-1)) 0 ∧
      IsEig ((jac (cubT (ι := ι) 1) 0 - 1).map Complex.ofReal) 0 ∧
      ¬NoZeroRe (jac (cubT (ι := ι) 1) 0) ∧
      ¬EStableAt (cubT (ι := ι) 1) 0 ∧ ¬EStableAt (cubT (ι := ι) (-1)) 0 ∧
      IsLASLoc (cubT (ι := ι) (-1)) 0 ∧ ¬IsLASLoc (cubT (ι := ι) 1) 0 := by
  have heig : ∀ s : ℝ, IsEig ((jac (cubT (ι := ι) s) 0 - 1).map Complex.ofReal) 0 := by
    intro s
    rw [jac_of_hasFDerivAt (hasFDerivAt_cubT s), isEig_smul_one_sub_one_iff]
    norm_num
  have hnE : ∀ s : ℝ, ¬EStableAt (cubT (ι := ι) s) 0 := by
    intro s hE
    have := hE.2.2 0 (heig s)
    norm_num at this
  refine ⟨contDiff_cubT 1, contDiff_cubT (-1), cubT_zero 1, cubT_zero (-1), ?_, heig 1,
    fun h => h 0 (heig 1) (by norm_num), hnE 1, hnE (-1), isLASLoc_cubT_neg,
    not_isLASLoc_cubT_pos⟩
  rw [(hasFDerivAt_cubT 1).fderiv, (hasFDerivAt_cubT (-1)).fderiv]

/-- Woodford (2003), p. 266 and n. 37: **the same for solutions on `[0, ∞)`**: the globally
Lipschitz (hence forward-complete) modifications of `T±(θ) = θ ± θ³` have the rest point `0` and
the same Jacobian `DT(0) = I`, and `0` is a locally asymptotically stable rest point (`IsLAS`) for
one and not for the other. -/
theorem zero_re_undecided_complete [DecidableEq ι] [Nonempty ι] :
    LipschitzWith 4 (tMod (cubT (ι := ι) 1) 0 1) ∧
      LipschitzWith 4 (tMod (cubT (ι := ι) (-1)) 0 1) ∧
      jac (tMod (cubT (ι := ι) 1) 0 1) 0 = jac (tMod (cubT (ι := ι) (-1)) 0 1) 0 ∧
      IsEig ((jac (tMod (cubT (ι := ι) 1) 0 1) 0 - 1).map Complex.ofReal) 0 ∧
      IsLAS (tMod (cubT (ι := ι) (-1)) 0 1) 0 ∧ ¬IsLAS (tMod (cubT (ι := ι) 1) 0 1) 0 := by
  have hloc : ∀ s : ℝ, jac (tMod (cubT (ι := ι) s) 0 1) 0 = (1 : ℝ) • 1 := by
    intro s
    rw [(tMod_local one_pos (cubT_zero s) (hasFDerivAt_cubT s).differentiableAt).2.2,
      jac_of_hasFDerivAt (hasFDerivAt_cubT s)]
  refine ⟨lipschitzWith_tMod zero_le_one (lipschitzOnWith_cubT (by norm_num)),
    lipschitzWith_tMod zero_le_one (lipschitzOnWith_cubT (by norm_num)),
    by rw [hloc, hloc], ?_, isLAS_tMod_cubT_neg, not_isLAS_tMod_cubT_pos⟩
  rw [hloc, isEig_smul_one_sub_one_iff]
  norm_num

end Woodford.NeoWicksellianFramework.TidyR6InstabilityCex
