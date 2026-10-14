/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Log-linearisation and local determinacy on `ℓ∞`

Woodford (2003), *Interest and Prices*, Appendix A.3 "Log-Linearization and Determinacy of
Equilibrium", pp. 630–635, and its uses in Propositions 2.3 (p. 82, proof A.4 p. 635) and 2.6
(p. 91). The book asserts, citing Lang (1983) and without proof, that if the log-linearised
equilibrium conditions have a unique bounded solution, then the exact nonlinear model has a
locally unique equilibrium near the steady state for small disturbances, that it is
approximated by the log-linear solution, and that the error is `O(ξ²)`. This module proves this
rigorously in the **perfect-foresight (deterministic)** setting of A.3 (pp. 631–633), on the
Banach space `ℓ∞` of bounded real sequences, for the class `F(x_t, x_{t+1}, e_t) = 0` (one
forward-looking variable, finite-dimensional disturbance vectors `e_t`). Its subclass
`g(x_t, ν_t) − x_{t+1} = w_t` contains the exact Wicksellian model (Prop. 2.3) and the exact
Taylor-rule model (Prop. 2.6); module `Nonlinear` applies the general class to Props. 2.7, 2.8
and 2.11–2.13.

Main results.

* (i) The general class `F(x_t, x_{t+1}, e_t) = 0` with disturbance vectors `e_t` in a
  finite-dimensional space (`Seq`, `Solves`): the equilibrium map (Nemytskii operator with a
  lead) is strictly Fréchet differentiable at **every** point and `C¹`
  (`hasStrictFDerivAt_eqMap`, `contDiff_eqMap`).
* (ii) `shift`, `norm_shift_le`, `fwdOp`, `isUnit_fwdOp`, `fwdOp_fwdSol`, `fwdOp_inverse_apply`,
  `eq_fwdSol`: the lead operator and `x_t − a x_{t+1}` are bounded linear; for `|a| < 1` the
  latter is invertible with the forward sum as inverse. (A.9) without "generically":
  `isUnit_TOp_iff` (`a + b S` is invertible **iff** `|b| < |a|`) and `isUnit_linOp_iff`
  (`b − S` is invertible iff `|b| > 1`).
* (iii) Implicit-function theorem on `ℓ∞`: `local_determinacy3`, `hasFDerivAt_implicitSol3`
  (the first-order term is the log-linear solution `linSol3`, `linSol3_apply`: a forward sum),
  and with **local** hypotheses (bump cut-off): `local_determinacy_loc`,
  `local_indeterminacy_loc` (a continuum of equilibria when `|a| < |b|`).
* (iv) Second order: `second_order3`, `second_order_loc` (`O(‖e‖²)` under `C^{1,1}`/`C²`).
* The scalar class `g(x_t, ν_t) − x_{t+1} = w_t` is the instance `gF` (`slopes_gF`,
  `solves_gF_iff`): `local_determinacy`, `implicitSol_zero`, `hasFDerivAt_implicitSol`
  (`linSolOp_apply`: the forward sum (1.37)/(2.7)), `local_indeterminacy`,
  `second_order_accuracy` (`C^{1,1}`), `second_order_accuracy_of_contDiff_two` (`C²`).
  Erratum E18: `not_second_order_of_C1` shows the `O(ξ²)` claim fails for a `C¹` model.
* Applied: `wicksell_local_determinacy`, `wicksell_smooth_dependence`, `wicksell_second_order`
  (Prop. 2.3) and `taylor_local_determinacy`, `taylor_smooth_dependence`, `taylor_second_order`,
  `taylor_local_indeterminacy` (Prop. 2.6).

* Price level (fn. 25): `taylor_price_level` — given `P_{-1} > 0`, local existence and
  uniqueness of the equilibrium **price-level** path under a Taylor rule, with each
  `log(P_t/P_{-1})` a `C¹` function of the disturbances.
* Transversality (1.24), p. 72, near the steady state (p. 79): `TVC`, `tvc_of_bounds`,
  `wicksell_tvc`, `taylor_tvc`, `exists_eps_tvc`. They hold under the book's fiscal assumption
  `γ_D < π̄/β` (p. 79) in the form `β γ < θ` (for the Taylor rule, `β γ < θ e^{-ε}`, which a
  small enough band achieves), plus a bound on marginal utility. Counterexamples without the
  fiscal hypothesis: `wicksell_tvc_fails`, `taylor_tvc_fails`.

What is not covered: the stochastic version (A.11)–(A.13) on `L∞` processes, and systems with
predetermined variables or several equations per period (the general (A.9) root count).
-/

namespace Woodford.PriceLevelDetermination.LocalIFT

open scoped ENNReal Topology

/-- Woodford (2003), App. A.3, p. 632: the Banach space `ℓ∞` of bounded real sequences
`{p̂_t}_{t ≥ 0}` with the sup norm, on which the perfect-foresight equilibrium conditions
are posed. -/
abbrev Linf : Type := lp (fun _ : ℕ => ℝ) ∞

/-- Woodford (2003), App. A.3, p. 632: each coordinate of a bounded sequence is bounded by its
sup norm. -/
theorem abs_apply_le (x : Linf) (t : ℕ) : |x t| ≤ ‖x‖ := by
  simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero x t

/-- Woodford (2003), App. A.3, p. 632: a real sequence with a uniform bound, as an element of
`ℓ∞`. -/
noncomputable def mk (x : ℕ → ℝ) (hx : ∃ C, ∀ t, |x t| ≤ C) : Linf :=
  ⟨x, memℓp_infty (by
    obtain ⟨C, hC⟩ := hx
    exact ⟨C, by rintro _ ⟨t, rfl⟩; simpa using hC t⟩)⟩

/-- Woodford (2003), App. A.3, p. 632: coordinates of `mk`. -/
@[simp] theorem mk_apply (x : ℕ → ℝ) (hx : ∃ C, ∀ t, |x t| ≤ C) (t : ℕ) : mk x hx t = x t :=
  rfl

/-- Woodford (2003), App. A.3, p. 632: the sup norm of a sequence is at most any uniform bound
on its coordinates. -/
theorem norm_le_of_abs_le {x : Linf} {C : ℝ} (hC : 0 ≤ C) (h : ∀ t, |x t| ≤ C) : ‖x‖ ≤ C :=
  lp.norm_le_of_forall_le hC (by simpa using h)

/-- Woodford (2003), App. A.3, p. 632: the (lead) shift as a linear map. -/
noncomputable def shiftLM : Linf →ₗ[ℝ] Linf where
  toFun x := mk (fun t => x (t + 1)) ⟨‖x‖, fun t => abs_apply_le x (t + 1)⟩
  map_add' x y := by ext t; simp
  map_smul' c x := by ext t; simp

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the lead operator `(S x)_t = x_{t+1}`, a bounded
linear operator on `ℓ∞` of norm at most one. -/
noncomputable def shift : Linf →L[ℝ] Linf :=
  shiftLM.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_le_of_abs_le (norm_nonneg x) (fun t => abs_apply_le x (t + 1)))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of the lead operator. -/
@[simp] theorem shift_apply (x : Linf) (t : ℕ) : shift x t = x (t + 1) := rfl

/-- Woodford (2003), App. A.3, p. 632: the lead operator is bounded with norm at most one. -/
theorem norm_shift_le : ‖shift‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Woodford (2003), App. A.4, eq. (A.14), p. 636: the forward operator `(x_t − a x_{t+1})_t`
on `ℓ∞`, i.e. `1 − a S` with `S` the lead operator. -/
noncomputable def fwdOp (a : ℝ) : Linf →L[ℝ] Linf := 1 - a • shift

/-- Woodford (2003), App. A.4, eq. (A.14), p. 636: coordinates of the forward operator. -/
@[simp] theorem fwdOp_apply (a : ℝ) (x : Linf) (t : ℕ) :
    fwdOp a x t = x t - a * x (t + 1) := by
  simp [fwdOp]
  rfl

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632, scalar case `f₁ = 0, f₂ = b, f₃ = −1`: the
linearised equilibrium operator `(b x_t − x_{t+1})_t`. -/
noncomputable def linOp (b : ℝ) : Linf →L[ℝ] Linf := b • 1 - shift

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of the linearised operator. -/
@[simp] theorem linOp_apply (b : ℝ) (x : Linf) (t : ℕ) :
    linOp b x t = b * x t - x (t + 1) := by
  simp [linOp]
  rfl

/-- Woodford (2003), App. A.3, p. 632: for `|a| < 1` the operator `a S` has norm below one. -/
theorem norm_smul_shift_lt {a : ℝ} (ha : |a| < 1) : ‖a • shift‖ < 1 := by
  refine (norm_smul_le a shift).trans_lt ?_
  rw [Real.norm_eq_abs]
  calc |a| * ‖shift‖ ≤ |a| * 1 := mul_le_mul_of_nonneg_left norm_shift_le (abs_nonneg a)
    _ < 1 := by linarith

/-- Woodford (2003), App. A.3, p. 632 and Lemma A.14, p. 636: for `|a| < 1` the forward operator
`1 − a S` is invertible on `ℓ∞` (Neumann series). -/
theorem isUnit_fwdOp {a : ℝ} (ha : |a| < 1) : IsUnit (fwdOp a) := by
  have h := (Units.oneSub (a • shift) (norm_smul_shift_lt ha)).isUnit
  simpa [Units.val_oneSub, fwdOp] using h

/-- Woodford (2003), App. A.4, eq. (A.16), p. 636: the forward sum `∑ aᵏ y_{t+k}` converges. -/
theorem summable_fwd {a : ℝ} (ha : |a| < 1) (y : Linf) (t : ℕ) :
    Summable (fun k => a ^ k * y (t + k)) := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_left ‖y‖) (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_apply_le y _) (pow_nonneg (abs_nonneg a) k)

/-- Woodford (2003), App. A.4, eq. (A.16), p. 636: the forward sum is bounded by
`‖y‖ / (1 − |a|)`. -/
theorem abs_tsum_fwd_le {a : ℝ} (ha : |a| < 1) (y : Linf) (t : ℕ) :
    |∑' k, a ^ k * y (t + k)| ≤ ‖y‖ / (1 - |a|) := by
  have hs := summable_geometric_of_lt_one (abs_nonneg a) ha
  calc |∑' k, a ^ k * y (t + k)| ≤ ∑' k, ‖y‖ * |a| ^ k := by
        rw [← Real.norm_eq_abs]
        refine tsum_of_norm_bounded (hs.mul_left ‖y‖).hasSum (fun k => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right (abs_apply_le y _) (pow_nonneg (abs_nonneg a) k)
    _ = ‖y‖ / (1 - |a|) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (abs_nonneg a) ha, div_eq_mul_inv]

/-- Woodford (2003), App. A.4, eq. (A.16), p. 636: the forward solution
`z_t = ∑_{k ≥ 0} aᵏ y_{t+k}` as an element of `ℓ∞`. -/
noncomputable def fwdSol {a : ℝ} (ha : |a| < 1) (y : Linf) : Linf :=
  mk (fun t => ∑' k, a ^ k * y (t + k)) ⟨_, abs_tsum_fwd_le ha y⟩

/-- Woodford (2003), App. A.4, eqs. (A.14)/(A.16), p. 636: the forward solution solves
`z_t − a z_{t+1} = y_t`. -/
theorem fwdOp_fwdSol {a : ℝ} (ha : |a| < 1) (y : Linf) : fwdOp a (fwdSol ha y) = y := by
  ext t
  simp only [fwdOp_apply, fwdSol, mk_apply]
  rw [(summable_fwd ha y t).tsum_eq_zero_add]
  have h : ∑' k, a ^ (k + 1) * y (t + (k + 1)) = a * ∑' k, a ^ k * y (t + 1 + k) := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [pow_succ, show t + (k + 1) = t + 1 + k by ring]
    ring
  rw [h]
  simp

/-- Woodford (2003), App. A.4, Lemma A.14 / eq. (A.16), p. 636: for `|a| < 1` the inverse of the
forward operator `1 − a S` is the forward-sum operator. -/
theorem fwdOp_inverse_apply {a : ℝ} (ha : |a| < 1) (y : Linf) :
    Ring.inverse (fwdOp a) y = fwdSol ha y := by
  have h := congrArg (fun T : Linf →L[ℝ] Linf => T (fwdSol ha y))
    (Ring.inverse_mul_cancel _ (isUnit_fwdOp ha))
  change Ring.inverse (fwdOp a) (fwdOp a (fwdSol ha y)) = fwdSol ha y at h
  rwa [fwdOp_fwdSol] at h

/-- Woodford (2003), App. A.4, Lemma A.14, p. 636 (uniqueness): for `|a| < 1` the only bounded
solution of `z_t − a z_{t+1} = y_t` is the forward sum (A.16). -/
theorem eq_fwdSol {a : ℝ} (ha : |a| < 1) {y z : Linf} (h : ∀ t, z t - a * z (t + 1) = y t) :
    z = fwdSol ha y := by
  have hz : fwdOp a z = y := by
    ext t
    rw [fwdOp_apply, h t]
  rw [← fwdOp_inverse_apply ha, ← hz]
  have h2 := congrArg (fun T : Linf →L[ℝ] Linf => T z)
    (Ring.inverse_mul_cancel _ (isUnit_fwdOp ha))
  exact h2.symm

/-- Woodford (2003), App. A.3, p. 632: `b x_t − x_{t+1} = b (x_t − b⁻¹ x_{t+1})`. -/
theorem linOp_eq_smul_fwdOp {b : ℝ} (hb : b ≠ 0) : linOp b = b • fwdOp b⁻¹ := by
  ext x t
  simp only [linOp_apply, FunLike.coe_smul, Pi.smul_apply, lp.coeFn_smul, fwdOp_apply,
    smul_eq_mul]
  field_simp

/-- Woodford (2003), App. A.3, p. 632: for `|b| > 1` the linearised operator `b − S` is
invertible on `ℓ∞`. -/
theorem isUnit_linOp {b : ℝ} (hb : 1 < |b|) : IsUnit (linOp b) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
    linarith
  have ha : |b⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hb
  obtain ⟨u, hu⟩ := isUnit_fwdOp ha
  have hr : ∀ x, fwdOp b⁻¹ ((↑u⁻¹ : Linf →L[ℝ] Linf) x) = x := fun x => by
    rw [← hu]
    exact congrArg (fun T : Linf →L[ℝ] Linf => T x) u.mul_inv
  have hl : ∀ x, (↑u⁻¹ : Linf →L[ℝ] Linf) (fwdOp b⁻¹ x) = x := fun x => by
    rw [← hu]
    exact congrArg (fun T : Linf →L[ℝ] Linf => T x) u.inv_mul
  rw [linOp_eq_smul_fwdOp hb0]
  refine ⟨⟨b • fwdOp b⁻¹, b⁻¹ • (↑u⁻¹ : Linf →L[ℝ] Linf), ?_, ?_⟩, rfl⟩ <;> ext x : 1 <;>
    simp [hr, hl, smul_smul, hb0]

/-- Woodford (2003), App. A.3, p. 632: for `|b| ≤ 1` the bounded sequence `bᵗ`. -/
noncomputable def geomSeq {b : ℝ} (hb : |b| ≤ 1) : Linf :=
  mk (fun t => b ^ t) ⟨1, fun t => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg b) hb⟩

/-- Woodford (2003), App. A.3, p. 632: `bᵗ` lies in the kernel of `b − S`. -/
theorem linOp_geomSeq {b : ℝ} (hb : |b| ≤ 1) : linOp b (geomSeq hb) = 0 := by
  ext t
  simp [geomSeq, pow_succ]
  ring

/-- Woodford (2003), App. A.3, pp. 632–633 ((A.9), scalar case): for `|b| ≤ 1` the linearised
operator has a nonzero bounded kernel element, so it is not invertible. -/
theorem not_isUnit_linOp {b : ℝ} (hb : |b| ≤ 1) : ¬ IsUnit (linOp b) := by
  intro h
  obtain ⟨v, hv⟩ := h.exists_left_inv
  have h0 : geomSeq hb = 0 := by
    have := congrArg (fun T : Linf →L[ℝ] Linf => T (geomSeq hb)) hv
    simpa [linOp_geomSeq] using this.symm
  have := congrArg (fun x : Linf => x 0) h0
  simp [geomSeq] at this

/-- Woodford (2003), App. A.3, eq. (A.9), pp. 632–633, scalar forward-looking case: the
derivative operator `b − S` of (A.8) is invertible on `ℓ∞` **if and only if** the nonzero root
`λ = b` of the characteristic equation lies outside the unit circle. (For this case the book's
"generically" is not needed.) -/
theorem isUnit_linOp_iff (b : ℝ) : IsUnit (linOp b) ↔ 1 < |b| :=
  ⟨fun h => by
    by_contra h'
    exact not_isUnit_linOp (not_lt.mp h') h, isUnit_linOp⟩

/-- Woodford (2003), App. A.3, p. 632: the inverse of the linearised operator (the unique bounded
solution map of (A.10)). -/
noncomputable def linInv (b : ℝ) : Linf →L[ℝ] Linf := Ring.inverse (linOp b)

/-- Woodford (2003), App. A.3, p. 632: `linInv` is a left inverse. -/
theorem linInv_linOp {b : ℝ} (hb : 1 < |b|) (x : Linf) : linInv b (linOp b x) = x := by
  have h := Ring.inverse_mul_cancel _ (isUnit_linOp hb)
  unfold linInv
  simpa using congrArg (fun T : Linf →L[ℝ] Linf => T x) h

/-- Woodford (2003), App. A.3, p. 632: `linInv` is a right inverse. -/
theorem linOp_linInv {b : ℝ} (hb : 1 < |b|) (y : Linf) : linOp b (linInv b y) = y := by
  have h := Ring.mul_inverse_cancel _ (isUnit_linOp hb)
  unfold linInv
  simpa using congrArg (fun T : Linf →L[ℝ] Linf => T y) h

/-- Woodford (2003), App. A.3, p. 633: any bounded solution of the linearised equations equals
`linInv` of the right-hand side (uniqueness). -/
theorem linInv_eq {b : ℝ} (hb : 1 < |b|) {x y : Linf} (h : linOp b x = y) : linInv b y = x := by
  rw [← h, linInv_linOp hb]

/-- Woodford (2003), eq. (1.37), p. 81 and (A.16), p. 636: the inverse of `b − S` is the forward
sum `x_t = ∑_{k ≥ 0} b^{-(k+1)} y_{t+k}`. -/
theorem linInv_apply {b : ℝ} (hb : 1 < |b|) (y : Linf) (t : ℕ) :
    linInv b y t = ∑' k, (b⁻¹) ^ (k + 1) * y (t + k) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
    linarith
  have ha : |b⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hb
  have h : linOp b (b⁻¹ • fwdSol ha y) = y := by
    rw [linOp_eq_smul_fwdOp hb0, FunLike.coe_smul, Pi.smul_apply, map_smul,
      fwdOp_fwdSol,
      smul_smul, mul_inv_cancel₀ hb0, one_smul]
  rw [linInv_eq hb h]
  simp only [lp.coeFn_smul, Pi.smul_apply, fwdSol, mk_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1
  funext k
  ring

/-- Woodford (2003), App. A.3, p. 631: the constant sequence `p_t = c` (a steady state). -/
noncomputable def const (c : ℝ) : Linf := mk (fun _ => c) ⟨|c|, fun _ => le_rfl⟩

/-- Woodford (2003), App. A.3, p. 631: coordinates of a constant sequence. -/
@[simp] theorem const_apply (c : ℝ) (t : ℕ) : const c t = c := rfl

/-! ### Sequences of vector disturbances -/

/-- Woodford (2003), App. A.3, p. 632: the Banach space `ℓ∞(E)` of bounded sequences of
disturbance vectors `u_t ∈ E` (the book's vector `u_t` of exogenous disturbances). -/
abbrev Seq (E : Type*) [NormedAddCommGroup E] : Type _ := lp (fun _ : ℕ => E) ∞

variable {E : Type*} [NormedAddCommGroup E]

/-- Woodford (2003), App. A.3, p. 632: each disturbance vector is bounded by the sup norm. -/
theorem norm_seq_apply_le (e : Seq E) (t : ℕ) : ‖e t‖ ≤ ‖e‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero e t

/-- Woodford (2003), App. A.3, p. 632: a uniformly bounded sequence of disturbance vectors, as
an element of `ℓ∞(E)`. -/
noncomputable def mkS (f : ℕ → E) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) : Seq E :=
  ⟨f, memℓp_infty (by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, by rintro _ ⟨t, rfl⟩; exact hC t⟩)⟩

/-- Woodford (2003), App. A.3, p. 632: coordinates of `mkS`. -/
@[simp] theorem mkS_apply (f : ℕ → E) (hf : ∃ C, ∀ t, ‖f t‖ ≤ C) (t : ℕ) : mkS f hf t = f t :=
  rfl

/-- Woodford (2003), App. A.3, p. 632: the sup norm of a sequence of disturbance vectors is at
most any uniform bound. -/
theorem norm_seq_le {e : Seq E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ t, ‖e t‖ ≤ C) : ‖e‖ ≤ C :=
  lp.norm_le_of_forall_le hC h

variable [NormedSpace ℝ E]

/-! ### The scalar forward-looking class with vector disturbances

The equilibrium conditions are `F(x_t, x_{t+1}, e_t) = 0` for all `t ≥ 0` — the scalar case
`n = 1` of (A.7), p. 631, with no predetermined variable (`f₁ = 0`) and a vector disturbance
`e_t`. The Wicksellian and Taylor-rule class `g(x_t, ν_t) − x_{t+1} = w_t` of Props. 2.3 and
2.6 is the instance `gF` below; the models of §3 (money-growth targeting, non-separable utility)
and the inertial rules of §2.3 (module `Nonlinear`) need the general form. -/

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the date-`t` argument `(x_t, x_{t+1}, e_t)` of
the period equilibrium condition. -/
def pt3 (q : Seq E × Linf) (t : ℕ) : ℝ × ℝ × E := (q.2 t, q.2 (t + 1), q.1 t)

omit [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: each date-`t` argument is bounded by the sup norm. -/
theorem norm_pt3_le (q : Seq E × Linf) (t : ℕ) : ‖pt3 q t‖ ≤ ‖q‖ := by
  have h1 : ‖q.2 t‖ ≤ ‖q‖ := (abs_apply_le q.2 t).trans (norm_snd_le q)
  have h2 : ‖q.2 (t + 1)‖ ≤ ‖q‖ := (abs_apply_le q.2 (t + 1)).trans (norm_snd_le q)
  have h3 : ‖q.1 t‖ ≤ ‖q‖ := (norm_seq_apply_le q.1 t).trans (norm_fst_le q)
  rw [pt3, norm_prod_le_iff, norm_prod_le_iff]
  exact ⟨h1, h2, h3⟩

omit [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: `pt3` is additive. -/
theorem pt3_add (q q' : Seq E × Linf) (t : ℕ) : pt3 (q + q') t = pt3 q t + pt3 q' t := rfl

omit [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: `pt3` commutes with subtraction. -/
theorem pt3_sub (q q' : Seq E × Linf) (t : ℕ) : pt3 (q - q') t = pt3 q t - pt3 q' t := rfl

/-- Woodford (2003), App. A.3, p. 632: `pt3` is homogeneous. -/
theorem pt3_smul (c : ℝ) (q : Seq E × Linf) (t : ℕ) : pt3 (c • q) t = c • pt3 q t := rfl

omit [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: `pt3` of zero. -/
theorem pt3_zero (t : ℕ) : pt3 (0 : Seq E × Linf) t = 0 := rfl

/-- Woodford (2003), App. A.3, p. 632: a continuous function on a finite-dimensional space is
bounded on balls (compactness). -/
theorem exists_bound_ball3 {G H : Type*} [NormedAddCommGroup G] [ProperSpace G]
    [NormedAddCommGroup H] {h : G → H} (hc : Continuous h) (R : ℝ) :
    ∃ C, ∀ p : G, ‖p‖ ≤ R → ‖h p‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : G) R).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨C, fun p hp => hC p (mem_closedBall_zero_iff.mpr hp)⟩

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: `x` solves the exact perfect-foresight
equilibrium conditions `F(x_t, x_{t+1}, e_t) = 0` (all `t ≥ 0`) given the disturbances `e`. -/
def Solves (F : ℝ × ℝ × E → ℝ) (e : Seq E) (x : Linf) : Prop :=
  ∀ t, F (x t, x (t + 1), e t) = 0

/-- Woodford (2003), App. A.3, p. 632: coordinatewise bound for a multiplication operator. -/
theorem abs_mulOp3_le {L : ℕ → (ℝ × ℝ × E →L[ℝ] ℝ)} {C : ℝ} (hC : ∀ t, ‖L t‖ ≤ C)
    (dq : Seq E × Linf) (t : ℕ) : |L t (pt3 dq t)| ≤ C * ‖dq‖ := by
  rw [← Real.norm_eq_abs]
  exact ((L t).le_of_opNorm_le (hC t) _).trans
    (mul_le_mul_of_nonneg_left (norm_pt3_le dq t) ((norm_nonneg _).trans (hC t)))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the multiplication operator
`dq ↦ (L_t(dx_t, dx_{t+1}, de_t))_t` with uniformly bounded coefficients. -/
noncomputable def mulOp3 (L : ℕ → (ℝ × ℝ × E →L[ℝ] ℝ)) (hL : ∃ C, ∀ t, ‖L t‖ ≤ C) :
    Seq E × Linf →L[ℝ] Linf :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun dq => mk (fun t => L t (pt3 dq t)) (by
        obtain ⟨C, hC⟩ := hL
        exact ⟨C * ‖dq‖, abs_mulOp3_le hC dq⟩)
      map_add' := fun dq dq' => by
        ext t
        simp only [mk_apply, lp.coeFn_add, Pi.add_apply]
        rw [pt3_add, map_add]
      map_smul' := fun c dq => by
        ext t
        simp only [mk_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
        rw [pt3_smul, map_smul] }
    (by
      obtain ⟨C, hC⟩ := hL
      refine ⟨C, fun dq => norm_le_of_abs_le ?_ (abs_mulOp3_le hC dq)⟩
      exact mul_nonneg ((norm_nonneg _).trans (hC 0)) (norm_nonneg _))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of a multiplication operator. -/
@[simp] theorem mulOp3_apply (L : ℕ → (ℝ × ℝ × E →L[ℝ] ℝ)) (hL : ∃ C, ∀ t, ‖L t‖ ≤ C)
    (dq : Seq E × Linf) (t : ℕ) : mulOp3 L hL dq t = L t (pt3 dq t) := rfl

variable [FiniteDimensional ℝ E]

/-- Woodford (2003), App. A.3, eq. (A.4)/(A.7), p. 631: the equilibrium map
`Φ(e, x)_t = F(x_t, x_{t+1}, e_t)` on `ℓ∞(E) × ℓ∞`. -/
noncomputable def eqMap (F : ℝ × ℝ × E → ℝ) (hF : Continuous F) (q : Seq E × Linf) : Linf :=
  mk (fun t => F (pt3 q t)) (by
    obtain ⟨C, hC⟩ := exists_bound_ball3 hF ‖q‖
    exact ⟨C, fun t => by simpa using hC _ (norm_pt3_le q t)⟩)

/-- Woodford (2003), App. A.3, p. 631: coordinates of the equilibrium map. -/
@[simp] theorem eqMap_apply (F : ℝ × ℝ × E → ℝ) (hF : Continuous F) (q : Seq E × Linf)
    (t : ℕ) : eqMap F hF q t = F (pt3 q t) := rfl

/-- Woodford (2003), App. A.3, eq. (A.4), p. 630: zeros of the equilibrium map are exactly the
perfect-foresight equilibria. -/
theorem eqMap_eq_zero_iff (F : ℝ × ℝ × E → ℝ) (hF : Continuous F) (e : Seq E) (x : Linf) :
    eqMap F hF (e, x) = 0 ↔ Solves F e x := by
  constructor
  · intro h t
    simpa [pt3] using congrArg (fun y : Linf => y t) h
  · intro h
    ext t
    simpa [pt3] using h t

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the Fréchet derivative of the equilibrium map
at `q`, `dq ↦ (DF(x_t, x_{t+1}, e_t)(dx_t, dx_{t+1}, de_t))_t`. -/
noncomputable def eqD (F : ℝ × ℝ × E → ℝ) (hF : ContDiff ℝ 1 F) (q : Seq E × Linf) :
    Seq E × Linf →L[ℝ] Linf :=
  mulOp3 (fun t => fderiv ℝ F (pt3 q t)) (by
    obtain ⟨C, hC⟩ := exists_bound_ball3 (hF.continuous_fderiv one_ne_zero) ‖q‖
    exact ⟨C, fun t => hC _ (norm_pt3_le q t)⟩)

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of `eqD`. -/
@[simp] theorem eqD_apply (F : ℝ × ℝ × E → ℝ) (hF : ContDiff ℝ 1 F) (q dq : Seq E × Linf)
    (t : ℕ) : eqD F hF q dq t = fderiv ℝ F (pt3 q t) (pt3 dq t) := rfl

/-- Woodford (2003), App. A.3, p. 632: the derivative of a `C¹` function on a finite-dimensional
space is uniformly continuous on bounded sets (Heine–Cantor). -/
theorem fderiv_close3 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [ProperSpace G]
    {F : G → ℝ} (hF : ContDiff ℝ 1 F) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : G, ‖p‖ ≤ R → ‖q - p‖ < δ → ‖fderiv ℝ F q - fderiv ℝ F p‖ < ε := by
  have hK := isCompact_closedBall (0 : G) (R + 1)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (hF.continuous_fderiv one_ne_zero).continuousOn) ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun p q hp hq => ?_⟩
  have hq1 : ‖q - p‖ < 1 := lt_of_lt_of_le hq (min_le_right _ _)
  have hpK : p ∈ Metric.closedBall (0 : G) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    linarith
  have hqK : q ∈ Metric.closedBall (0 : G) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    have : ‖q‖ ≤ ‖p‖ + ‖q - p‖ := by
      calc ‖q‖ = ‖p + (q - p)‖ := by rw [add_sub_cancel]
        _ ≤ ‖p‖ + ‖q - p‖ := norm_add_le _ _
    linarith
  have := h q hqK p hpK (by rw [dist_eq_norm]; exact lt_of_lt_of_le hq (min_le_left _ _))
  rwa [dist_eq_norm] at this

/-- Woodford (2003), App. A.3, p. 632: **the equilibrium map of a `C¹` period condition is
strictly Fréchet differentiable on `ℓ∞(E) × ℓ∞` at every point** (Nemytskii operator with a lead,
vector disturbances). -/
theorem hasStrictFDerivAt_eqMap {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (q : Seq E × Linf) :
    HasStrictFDerivAt (eqMap F hF.continuous) (eqD F hF q) q := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close3 hF ‖q‖ hc
  have hball : Metric.ball (q, q) (δ / 2) ∈ 𝓝 (q, q) := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [hball] with p hp
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hp
  refine norm_le_of_abs_le (by positivity) (fun t => ?_)
  have hmem : ∀ y : Seq E × Linf, ‖y - q‖ < δ / 2 →
      pt3 y t ∈ Metric.ball (pt3 q t) (δ / 2) := fun y hy => by
    rw [Metric.mem_ball, dist_eq_norm, ← pt3_sub]
    exact (norm_pt3_le _ t).trans_lt hy
  have key := (convex_ball (pt3 q t) (δ / 2)).norm_image_sub_le_of_norm_fderiv_le' (f := F)
    (φ := fderiv ℝ F (pt3 q t)) (C := c) (fun w _ => (hF.differentiable one_ne_zero) w)
    (fun w hw => by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      exact (hclose (pt3 q t) w (norm_pt3_le q t) (by linarith)).le)
    (hmem p.2 hp.2) (hmem p.1 hp.1)
  simp only [lp.coeFn_sub, Pi.sub_apply, eqMap_apply, eqD_apply]
  rw [← Real.norm_eq_abs, pt3_sub]
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
  rw [← pt3_sub]
  exact norm_pt3_le _ t

/-- Woodford (2003), App. A.3, p. 632: the derivative `q ↦ eqD F q` is continuous in operator
norm. -/
theorem continuous_eqD {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) : Continuous (eqD F hF) := by
  rw [Metric.continuous_iff]
  intro q ε hε
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close3 hF ‖q‖ (half_pos hε)
  refine ⟨δ, hδ, fun q' hq' => ?_⟩
  rw [dist_eq_norm] at hq' ⊢
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
    (fun dq => ?_)) (half_lt_self hε)
  refine norm_le_of_abs_le (by positivity) (fun t => ?_)
  simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, eqD_apply]
  rw [← sub_apply, ← Real.norm_eq_abs]
  refine ((fderiv ℝ F (pt3 q' t) - fderiv ℝ F (pt3 q t)).le_opNorm _).trans
    (mul_le_mul (hclose _ _ (norm_pt3_le q t) ?_).le (norm_pt3_le dq t) (norm_nonneg _)
      (half_pos hε).le)
  rw [← pt3_sub]
  exact (norm_pt3_le _ t).trans_lt hq'

/-- Woodford (2003), App. A.3, p. 632: the equilibrium map is `C¹`. -/
theorem contDiff_eqMap {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (eqMap F hF.continuous) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨eqD F hF, continuous_eqD hF, fun q => (hasStrictFDerivAt_eqMap hF q).hasFDerivAt⟩

/-! ### The linearised operator `a + b S` -/

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `∂F/∂x_t` at the steady state. -/
noncomputable def slopeA (F : ℝ × ℝ × E → ℝ) : ℝ := fderiv ℝ F 0 (1, 0, 0)

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `∂F/∂x_{t+1}` at the steady state. -/
noncomputable def slopeB (F : ℝ × ℝ × E → ℝ) : ℝ := fderiv ℝ F 0 (0, 1, 0)

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `∂F/∂e_t` at the steady state. -/
noncomputable def slopeC (F : ℝ × ℝ × E → ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ F 0).comp ((ContinuousLinearMap.inr ℝ ℝ (ℝ × E)).comp
    (ContinuousLinearMap.inr ℝ ℝ E))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the derivative at the steady state in
coordinates, `DF(0)(x, y, v) = a x + b y + c v`. -/
theorem fderiv_zero_apply3 (F : ℝ × ℝ × E → ℝ) (x y : ℝ) (v : E) :
    fderiv ℝ F 0 (x, y, v) = slopeA F * x + slopeB F * y + slopeC F v := by
  have h : ((x, y, v) : ℝ × ℝ × E) =
      x • ((1 : ℝ), (0 : ℝ), (0 : E)) + y • ((0 : ℝ), (1 : ℝ), (0 : E)) +
        ((0 : ℝ), (0 : ℝ), v) := by
    ext <;> simp
  rw [h, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [slopeA, slopeB, slopeC, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply]
  ring

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632, scalar case with `f₁ = 0`: the linearised
operator `(a x_t + b x_{t+1})_t = a + b S` on `ℓ∞`. -/
noncomputable def TOp (a b : ℝ) : Linf →L[ℝ] Linf := a • (1 : Linf →L[ℝ] Linf) + b • shift

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of `a + b S`. -/
@[simp] theorem TOp_apply (a b : ℝ) (x : Linf) (t : ℕ) :
    TOp a b x t = a * x t + b * x (t + 1) := by
  simp [TOp]
  rfl

/-- Woodford (2003), App. A.3, p. 632: `a + b S = a (1 − (−b/a) S)` for `a ≠ 0`. -/
theorem TOp_eq_smul_fwdOp {a : ℝ} (b : ℝ) (ha : a ≠ 0) : TOp a b = a • fwdOp (-b / a) := by
  ext x t
  simp only [TOp_apply, FunLike.coe_smul, Pi.smul_apply, lp.coeFn_smul, fwdOp_apply,
    smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), App. A.3, p. 632: `|b| < |a|` forces `a ≠ 0`. -/
theorem ne_zero_of_abs_lt {a b : ℝ} (h : |b| < |a|) : a ≠ 0 := by
  rintro rfl
  simp only [abs_zero] at h
  linarith [abs_nonneg b]

/-- Woodford (2003), App. A.3, p. 632: `|b| < |a|` means `|−b/a| < 1`. -/
theorem abs_ratio_lt {a b : ℝ} (h : |b| < |a|) : |-b / a| < 1 := by
  rw [abs_div, abs_neg, div_lt_one (abs_pos.mpr (ne_zero_of_abs_lt h))]
  exact h

/-- Woodford (2003), App. A.4, (A.16), p. 636: `Ring.inverse (1 − ρ S)` is a right inverse. -/
theorem fwdOp_ringInv {ρ : ℝ} (hρ : |ρ| < 1) (y : Linf) :
    fwdOp ρ (Ring.inverse (fwdOp ρ) y) = y := by
  have h := Ring.mul_inverse_cancel _ (isUnit_fwdOp hρ)
  simpa using congrArg (fun T : Linf →L[ℝ] Linf => T y) h

/-- Woodford (2003), App. A.4, (A.16), p. 636: `Ring.inverse (1 − ρ S)` is a left inverse. -/
theorem ringInv_fwdOp {ρ : ℝ} (hρ : |ρ| < 1) (x : Linf) :
    Ring.inverse (fwdOp ρ) (fwdOp ρ x) = x := by
  have h := Ring.inverse_mul_cancel _ (isUnit_fwdOp hρ)
  simpa using congrArg (fun T : Linf →L[ℝ] Linf => T x) h

/-- Woodford (2003), App. A.4, (A.16), p. 636: the inverse of `a + b S` for `|b| < |a|`,
`a⁻¹ (1 − (−b/a) S)⁻¹`. -/
noncomputable def TInv (a b : ℝ) : Linf →L[ℝ] Linf := a⁻¹ • Ring.inverse (fwdOp (-b / a))

/-- Woodford (2003), App. A.4, p. 636: `TInv` is a right inverse of `a + b S` (`|b| < |a|`). -/
theorem TOp_TInv {a b : ℝ} (h : |b| < |a|) (y : Linf) : TOp a b (TInv a b y) = y := by
  have ha := ne_zero_of_abs_lt h
  rw [TOp_eq_smul_fwdOp b ha, TInv]
  simp only [FunLike.coe_smul, Pi.smul_apply, map_smul,
    fwdOp_ringInv (abs_ratio_lt h), smul_smul, inv_mul_cancel₀ ha, one_smul]

/-- Woodford (2003), App. A.4, p. 636: `TInv` is a left inverse of `a + b S` (`|b| < |a|`). -/
theorem TInv_TOp {a b : ℝ} (h : |b| < |a|) (x : Linf) : TInv a b (TOp a b x) = x := by
  have ha := ne_zero_of_abs_lt h
  rw [TOp_eq_smul_fwdOp b ha, TInv]
  simp only [FunLike.coe_smul, Pi.smul_apply, map_smul,
    ringInv_fwdOp (abs_ratio_lt h), smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- Woodford (2003), (1.37), p. 81 and (A.16), p. 636: the inverse of `a + b S` is the forward
sum `y ↦ a⁻¹ ∑_k (−b/a)ᵏ y_{t+k}`. -/
theorem TInv_apply {a b : ℝ} (h : |b| < |a|) (y : Linf) (t : ℕ) :
    TInv a b y t = a⁻¹ * ∑' k, (-b / a) ^ k * y (t + k) := by
  rw [TInv, smul_apply, fwdOp_inverse_apply (abs_ratio_lt h)]
  rfl

/-- Woodford (2003), App. A.3, eq. (A.9), pp. 632–633, scalar case of the class
`F(x_t, x_{t+1}, e_t) = 0`: the derivative operator `a + b S` is invertible on `ℓ∞` **if and only
if** `|b| < |a|` (the root `−a/b` lies outside the unit circle; no "generically"). -/
theorem isUnit_TOp_iff (a b : ℝ) : IsUnit (TOp a b) ↔ |b| < |a| := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨u, hu⟩ := h
    have hr : ∀ y, TOp a b ((↑u⁻¹ : Linf →L[ℝ] Linf) y) = y := fun y => by
      rw [← hu]
      exact congrArg (fun T : Linf →L[ℝ] Linf => T y) u.mul_inv
    have hl : ∀ y, (↑u⁻¹ : Linf →L[ℝ] Linf) (TOp a b y) = y := fun y => by
      rw [← hu]
      exact congrArg (fun T : Linf →L[ℝ] Linf => T y) u.inv_mul
    rcases eq_or_ne b 0 with hb | hb
    · have ha : a = 0 := by
        rw [hb, abs_zero] at hc
        exact abs_nonpos_iff.mp hc
      have h1 := hr (const 1)
      have h0 : TOp a b ((↑u⁻¹ : Linf →L[ℝ] Linf) (const 1)) = 0 := by
        ext t
        simp [ha, hb]
      rw [h0] at h1
      have := congrArg (fun y : Linf => y 0) h1
      simp at this
    · have hle : |-a / b| ≤ 1 := by
        rw [abs_div, abs_neg, div_le_one (abs_pos.mpr hb)]
        exact hc
      apply not_isUnit_linOp hle
      have he : ∀ y, TOp a b y = (-b) • linOp (-a / b) y := fun y => by
        ext t
        simp only [TOp_apply, lp.coeFn_smul, Pi.smul_apply, linOp_apply, smul_eq_mul]
        field_simp
        ring
      refine ⟨⟨linOp (-a / b), (-b) • (↑u⁻¹ : Linf →L[ℝ] Linf), ?_, ?_⟩, rfl⟩
      · ext y : 1
        simp only [mul_apply_eq_comp, one_apply_eq_self,
          FunLike.coe_smul, Pi.smul_apply, map_smul]
        have := hr y
        rw [he, ← map_smul] at this
        rw [← map_smul]
        exact this
      · ext y : 1
        simp only [mul_apply_eq_comp, one_apply_eq_self,
          FunLike.coe_smul, Pi.smul_apply]
        rw [← map_smul, ← he]
        exact hl y
  · intro h
    refine ⟨⟨TOp a b, TInv a b, ?_, ?_⟩, rfl⟩
    · ext y : 1
      exact TOp_TInv h y
    · ext y : 1
      exact TInv_TOp h y

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: coordinatewise bound for the disturbance operator. -/
theorem abs_cOp_le (c : E →L[ℝ] ℝ) (e : Seq E) (t : ℕ) : |c (e t)| ≤ ‖c‖ * ‖e‖ := by
  rw [← Real.norm_eq_abs]
  exact (c.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_seq_apply_le e t) (norm_nonneg c))

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the disturbance part `e ↦ (c(e_t))_t` of the
linearised conditions, a bounded linear operator `ℓ∞(E) → ℓ∞`. -/
noncomputable def cOp (c : E →L[ℝ] ℝ) : Seq E →L[ℝ] Linf :=
  LinearMap.mkContinuous
    { toFun := fun e => mk (fun t => c (e t)) ⟨‖c‖ * ‖e‖, abs_cOp_le c e⟩
      map_add' := fun e e' => by
        ext t
        simp
      map_smul' := fun r e => by
        ext t
        simp }
    ‖c‖ (fun e => norm_le_of_abs_le (by positivity) (abs_cOp_le c e))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: coordinates of `cOp`. -/
@[simp] theorem cOp_apply (c : E →L[ℝ] ℝ) (e : Seq E) (t : ℕ) : cOp c e t = c (e t) := rfl

/-! ### The implicit-function theorem for the class `F(x_t, x_{t+1}, e_t) = 0` -/

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the derivative of the equilibrium map at the
steady state, `(de, dx) ↦ (a + b S) dx + (c(de_t))_t`. -/
noncomputable def eqD0 (F : ℝ × ℝ × E → ℝ) : Seq E × Linf →L[ℝ] Linf :=
  (TOp (slopeA F) (slopeB F)).comp (ContinuousLinearMap.snd ℝ (Seq E) Linf) +
    (cOp (slopeC F)).comp (ContinuousLinearMap.fst ℝ (Seq E) Linf)

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: at the steady state the derivative of the
equilibrium map is the linear operator (A.8). -/
theorem eqD_zero {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) : eqD F hF 0 = eqD0 F := by
  refine ContinuousLinearMap.ext (fun q => ?_)
  ext t
  have e1 : eqD F hF 0 q t = fderiv ℝ F 0 (q.2 t, q.2 (t + 1), q.1 t) := rfl
  have e2 : eqD0 F q t = TOp (slopeA F) (slopeB F) q.2 t + cOp (slopeC F) q.1 t := rfl
  rw [e1, e2, fderiv_zero_apply3, TOp_apply, cOp_apply]

/-- Woodford (2003), App. A.3, p. 631: the augmented map `(e, x) ↦ (e, Φ(e, x))`. -/
noncomputable def bigMap3 (F : ℝ × ℝ × E → ℝ) (hF : Continuous F) (q : Seq E × Linf) :
    Seq E × Linf :=
  (q.1, eqMap F hF q)

/-- Woodford (2003), App. A.3, p. 632: the augmented map is `C¹`. -/
theorem contDiff_bigMap3 {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (bigMap3 F hF.continuous) :=
  contDiff_fst.prodMk (contDiff_eqMap hF)

/-- Woodford (2003), App. A.3, p. 632: the derivative of the augmented map at the steady state. -/
noncomputable def bigD3 (F : ℝ × ℝ × E → ℝ) : Seq E × Linf →L[ℝ] Seq E × Linf :=
  (ContinuousLinearMap.fst ℝ (Seq E) Linf).prod (eqD0 F)

/-- Woodford (2003), App. A.3, p. 632: the inverse of `bigD3`,
`(de, dy) ↦ (de, (a + b S)⁻¹(dy − c de))`. -/
noncomputable def bigDInv3 (F : ℝ × ℝ × E → ℝ) : Seq E × Linf →L[ℝ] Seq E × Linf :=
  (ContinuousLinearMap.fst ℝ (Seq E) Linf).prod
    ((TInv (slopeA F) (slopeB F)).comp (ContinuousLinearMap.snd ℝ (Seq E) Linf -
      (cOp (slopeC F)).comp (ContinuousLinearMap.fst ℝ (Seq E) Linf)))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: `bigDInv3` is a left inverse of `bigD3`. -/
theorem bigDInv3_bigD3 {F : ℝ × ℝ × E → ℝ} (hab : |slopeB F| < |slopeA F|) (q : Seq E × Linf) :
    bigDInv3 F (bigD3 F q) = q := by
  refine Prod.ext rfl ?_
  change TInv (slopeA F) (slopeB F) (TOp (slopeA F) (slopeB F) q.2 + cOp (slopeC F) q.1 -
    cOp (slopeC F) q.1) = q.2
  rw [add_sub_cancel_right, TInv_TOp hab]

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: `bigDInv3` is a right inverse of `bigD3`. -/
theorem bigD3_bigDInv3 {F : ℝ × ℝ × E → ℝ} (hab : |slopeB F| < |slopeA F|) (q : Seq E × Linf) :
    bigD3 F (bigDInv3 F q) = q := by
  refine Prod.ext rfl ?_
  change TOp (slopeA F) (slopeB F) (TInv (slopeA F) (slopeB F) (q.2 - cOp (slopeC F) q.1)) +
    cOp (slopeC F) q.1 = q.2
  rw [TOp_TInv hab, sub_add_cancel]

/-- Woodford (2003), App. A.3, p. 632: for `|b| < |a|` the derivative of the augmented map is a
continuous linear equivalence. -/
noncomputable def bigDEquiv3 (F : ℝ × ℝ × E → ℝ) (hab : |slopeB F| < |slopeA F|) :
    (Seq E × Linf) ≃L[ℝ] (Seq E × Linf) :=
  ContinuousLinearEquiv.equivOfInverse (bigD3 F) (bigDInv3 F) (bigDInv3_bigD3 hab)
    (bigD3_bigDInv3 hab)

/-- Woodford (2003), App. A.3, p. 632: the derivative of the augmented map at the steady state. -/
theorem hasFDerivAt_bigMap3 {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F)
    (hab : |slopeB F| < |slopeA F|) :
    HasFDerivAt (bigMap3 F hF.continuous) (bigDEquiv3 F hab : _ →L[ℝ] _) 0 := by
  have h := (hasStrictFDerivAt_eqMap hF 0).hasFDerivAt
  rw [eqD_zero hF] at h
  exact hasFDerivAt_fst.prodMk h

/-- Woodford (2003), App. A.3, pp. 632–633: the local homeomorphism given by the
inverse-function theorem (Lang 1983; Mathlib's `HasStrictFDerivAt.toOpenPartialHomeomorph`). -/
noncomputable def homeo3 (F : ℝ × ℝ × E → ℝ) (hF : ContDiff ℝ 1 F)
    (hab : |slopeB F| < |slopeA F|) : OpenPartialHomeomorph (Seq E × Linf) (Seq E × Linf) :=
  ((contDiff_bigMap3 hF).contDiffAt.hasStrictFDerivAt' (hasFDerivAt_bigMap3 hF hab)
    one_ne_zero).toOpenPartialHomeomorph (bigMap3 F hF.continuous)

/-- Woodford (2003), App. A.3, p. 633: the locally unique equilibrium `x = X(e)`. -/
noncomputable def implicitSol3 (F : ℝ × ℝ × E → ℝ) (hF : ContDiff ℝ 1 F)
    (hab : |slopeB F| < |slopeA F|) (e : Seq E) : Linf :=
  ((homeo3 F hF hab).symm (e, 0)).2

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the solution operator of the linearised
equations `a x̂_t + b x̂_{t+1} + c(e_t) = 0`, `e ↦ −(a + b S)⁻¹(c e)`. -/
noncomputable def linSol3 (F : ℝ × ℝ × E → ℝ) : Seq E →L[ℝ] Linf :=
  -((TInv (slopeA F) (slopeB F)).comp (cOp (slopeC F)))

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: `linSol3` solves the linearised equations. -/
theorem linSol3_solves {F : ℝ × ℝ × E → ℝ} (hab : |slopeB F| < |slopeA F|) (e : Seq E) (t : ℕ) :
    slopeA F * linSol3 F e t + slopeB F * linSol3 F e (t + 1) + slopeC F (e t) = 0 := by
  have h := congrArg (fun y : Linf => y t) (TOp_TInv hab (cOp (slopeC F) e))
  simp only [TOp_apply, cOp_apply] at h
  have e1 : ∀ s, linSol3 F e s = -(TInv (slopeA F) (slopeB F) (cOp (slopeC F) e) s) :=
    fun s => rfl
  rw [e1, e1]
  linarith

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the linearised equations have exactly one
bounded solution, `linSol3 e`. -/
theorem eq_linSol3 {F : ℝ × ℝ × E → ℝ} (hab : |slopeB F| < |slopeA F|) {e : Seq E} {x : Linf}
    (h : ∀ t, slopeA F * x t + slopeB F * x (t + 1) + slopeC F (e t) = 0) :
    x = linSol3 F e := by
  have hT : TOp (slopeA F) (slopeB F) x = -cOp (slopeC F) e := by
    ext t
    rw [TOp_apply, lp.coeFn_neg, Pi.neg_apply, cOp_apply]
    linarith [h t]
  rw [← TInv_TOp hab x, hT, map_neg]
  rfl

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), eq. (1.37), p. 81 and (A.16), p. 636: the log-linear solution as a forward
sum, `x̂_t = −a⁻¹ ∑_{k ≥ 0} (−b/a)ᵏ c(e_{t+k})`. -/
theorem linSol3_apply {F : ℝ × ℝ × E → ℝ} (hab : |slopeB F| < |slopeA F|) (e : Seq E) (t : ℕ) :
    linSol3 F e t =
      -((slopeA F)⁻¹ * ∑' k, (-slopeB F / slopeA F) ^ k * slopeC F (e (t + k))) := by
  have h : linSol3 F e t = -(TInv (slopeA F) (slopeB F) (cOp (slopeC F) e) t) := rfl
  rw [h, TInv_apply hab]
  rfl

/-- Woodford (2003), App. A.3, p. 631: the local homeomorphism is the augmented map. -/
theorem homeo3_apply {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (hab : |slopeB F| < |slopeA F|)
    (q : Seq E × Linf) : homeo3 F hF hab q = bigMap3 F hF.continuous q := rfl

/-- Woodford (2003), App. A.3, p. 632: the steady state lies in the source. -/
theorem zero_mem_homeo3_source {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F)
    (hab : |slopeB F| < |slopeA F|) : (0 : Seq E × Linf) ∈ (homeo3 F hF hab).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

/-- Woodford (2003), App. A.3, p. 631: with no disturbances the steady state is an equilibrium. -/
theorem bigMap3_zero {F : ℝ × ℝ × E → ℝ} (hF : Continuous F) (h0 : F 0 = 0) :
    bigMap3 F hF 0 = 0 := by
  have h : eqMap F hF ((0 : Seq E), (0 : Linf)) = 0 := by
    rw [eqMap_eq_zero_iff]
    intro t
    have hz : (((0 : Linf) t, (0 : Linf) (t + 1), (0 : Seq E) t) : ℝ × ℝ × E) = 0 := by
      simp only [lp.coeFn_zero, Pi.zero_apply, Prod.mk_zero_zero]
    rw [hz]
    exact h0
  exact Prod.ext rfl h

/-- Woodford (2003), App. A.3, p. 632: the steady state lies in the target. -/
theorem zero_mem_homeo3_target {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) : (0 : Seq E × Linf) ∈ (homeo3 F hF hab).target := by
  have h := (homeo3 F hF hab).map_source (zero_mem_homeo3_source hF hab)
  rwa [homeo3_apply, bigMap3_zero hF.continuous h0] at h

/-- Woodford (2003), App. A.3, p. 632: the local inverse maps the steady state to itself. -/
theorem homeo3_symm_zero {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) : (homeo3 F hF hab).symm 0 = 0 := by
  have h := (homeo3 F hF hab).left_inv (zero_mem_homeo3_source hF hab)
  rwa [homeo3_apply, bigMap3_zero hF.continuous h0] at h

/-- Woodford (2003), App. A.3, p. 633: the local inverse is `C¹` at the steady state. -/
theorem contDiffAt_homeo3_symm {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) : ContDiffAt ℝ 1 (homeo3 F hF hab).symm 0 := by
  refine (homeo3 F hF hab).contDiffAt_symm (f₀' := bigDEquiv3 F hab)
    (zero_mem_homeo3_target hF h0 hab) ?_ ?_
  · rw [homeo3_symm_zero hF h0 hab]
    exact hasFDerivAt_bigMap3 hF hab
  · rw [homeo3_symm_zero hF h0 hab]
    exact (contDiff_bigMap3 hF).contDiffAt

/-- Woodford (2003), App. A.3, (A.5), p. 630: the derivative of the local inverse at the steady
state is the inverse of the derivative. -/
theorem hasFDerivAt_homeo3_symm {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) :
    HasFDerivAt (homeo3 F hF hab).symm ((bigDEquiv3 F hab).symm : _ →L[ℝ] _) 0 := by
  refine (homeo3 F hF hab).hasFDerivAt_symm (zero_mem_homeo3_target hF h0 hab) ?_
  rw [homeo3_symm_zero hF h0 hab]
  exact hasFDerivAt_bigMap3 hF hab

/-- Woodford (2003), App. A.3, p. 633: with no disturbances the equilibrium is the steady
state. -/
theorem implicitSol3_zero {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) : implicitSol3 F hF hab 0 = 0 := by
  rw [implicitSol3, Prod.mk_zero_zero, homeo3_symm_zero hF h0 hab]
  rfl

/-- Woodford (2003), App. A.3, p. 633 and (A.5), p. 630: **the first-order term of the exact
equilibrium is the log-linear solution**: `X` is Fréchet differentiable at `0` with derivative
`linSol3`. -/
theorem hasFDerivAt_implicitSol3 {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) : HasFDerivAt (implicitSol3 F hF hab) (linSol3 F) 0 := by
  have hin : HasFDerivAt (fun e : Seq E => ((e, (0 : Linf)) : Seq E × Linf))
      (ContinuousLinearMap.inl ℝ (Seq E) Linf) 0 :=
    (ContinuousLinearMap.inl ℝ (Seq E) Linf).hasFDerivAt
  have hs : HasFDerivAt (homeo3 F hF hab).symm ((bigDEquiv3 F hab).symm : _ →L[ℝ] _)
      ((0 : Seq E), (0 : Linf)) := by
    rw [Prod.mk_zero_zero]
    exact hasFDerivAt_homeo3_symm hF h0 hab
  have h := (ContinuousLinearMap.snd ℝ (Seq E) Linf).hasFDerivAt.comp (0 : Seq E)
    (hs.comp (0 : Seq E) hin)
  refine h.congr_fderiv (ContinuousLinearMap.ext (fun e => ?_))
  change TInv (slopeA F) (slopeB F) ((0 : Linf) - cOp (slopeC F) e) =
    -(TInv (slopeA F) (slopeB F) (cOp (slopeC F) e))
  rw [zero_sub, map_neg]

/-- Woodford (2003), App. A.3, pp. 632–633: **local determinacy of the exact perfect-foresight
model `F(x_t, x_{t+1}, e_t) = 0`** for a `C¹` condition with `F(0) = 0` and `|b| < |a|`: there
are `ε, δ > 0` such that for `‖e‖∞ < δ`, `X(e)` is an equilibrium with `‖X(e)‖∞ < ε/2`, it is
`C¹` near `e`, and every equilibrium with `‖x‖∞ < ε` equals `X(e)`. -/
theorem local_determinacy3 {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) :
    ∃ ε > 0, ∃ δ > 0, δ ≤ ε ∧
      (∀ e : Seq E, ‖e‖ < δ →
        ‖implicitSol3 F hF hab e‖ < ε / 2 ∧ Solves F e (implicitSol3 F hF hab e) ∧
          ContDiffAt ℝ 1 (implicitSol3 F hF hab) e) ∧
      (∀ e : Seq E, ‖e‖ < δ → ∀ x : Linf, ‖x‖ < ε → Solves F e x →
        x = implicitSol3 F hF hab e) := by
  set H := homeo3 F hF hab with hH
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (H.open_source.mem_nhds (zero_mem_homeo3_source hF hab))
  have hcd := contDiffAt_homeo3_symm hF h0 hab
  have hsym0 := homeo3_symm_zero hF h0 hab
  have hev1 : ∀ᶠ y in 𝓝 (0 : Seq E × Linf), y ∈ H.target :=
    H.open_target.mem_nhds (zero_mem_homeo3_target hF h0 hab)
  have hev2 : ∀ᶠ y in 𝓝 (0 : Seq E × Linf), ‖H.symm y‖ < ε / 2 := by
    have ht := hcd.continuousAt.tendsto
    rw [hsym0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds 0 (half_pos hε))).mono
      (fun y hy => by simpa using hy)
  have hev3 : ∀ᶠ y in 𝓝 (0 : Seq E × Linf), ContDiffAt ℝ 1 H.symm y :=
    hcd.eventually (by simp)
  have hpull : Filter.Tendsto (fun e : Seq E => ((e, (0 : Linf)) : Seq E × Linf))
      (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun e : Seq E => ((e, (0 : Linf)) : Seq E × Linf)) :=
      continuous_id.prodMk continuous_const
    have h := hc.tendsto (0 : Seq E)
    rwa [Prod.mk_zero_zero] at h
  obtain ⟨δ, hδ, hδP⟩ :=
    Metric.eventually_nhds_iff.mp (hpull.eventually (hev1.and (hev2.and hev3)))
  refine ⟨ε, hε, min δ ε, lt_min hδ hε, min_le_right _ _, fun e he => ?_,
    fun e he x hx hsol => ?_⟩
  · have heδ : dist e 0 < δ := by
      rw [dist_zero_right]
      exact lt_of_lt_of_le he (min_le_left _ _)
    obtain ⟨htar, hnorm, hcds⟩ := hδP heδ
    have hright : H (H.symm (e, 0)) = (e, 0) := H.right_inv htar
    have hfst : (H.symm (e, 0)).1 = e := congrArg Prod.fst hright
    have hsnd : eqMap F hF.continuous (H.symm (e, 0)) = 0 := congrArg Prod.snd hright
    refine ⟨lt_of_le_of_lt (norm_snd_le _) hnorm, ?_, ?_⟩
    · rw [← eqMap_eq_zero_iff F hF.continuous]
      have hq : ((e, implicitSol3 F hF hab e) : Seq E × Linf) = H.symm (e, 0) :=
        Prod.ext hfst.symm rfl
      rw [hq]
      exact hsnd
    · exact contDiffAt_snd.comp e (hcds.comp e (contDiffAt_id.prodMk contDiffAt_const))
  · have hsrc : ((e, x) : Seq E × Linf) ∈ H.source := by
      apply hεsub
      rw [Metric.mem_ball, dist_zero_right, Prod.norm_mk]
      exact max_lt (lt_of_lt_of_le he (min_le_right _ _)) hx
    have hHx : H (e, x) = (e, 0) :=
      Prod.ext rfl ((eqMap_eq_zero_iff F hF.continuous e x).mpr hsol)
    have h := H.left_inv hsrc
    rw [hHx] at h
    exact (congrArg Prod.snd h).symm

/-! ### Second-order accuracy -/

/-- Woodford (2003), App. A.3, p. 630 ("Taylor's theorem"): if `DF` is Lipschitz at the steady
state on the ball of radius `r`, the first-order Taylor remainder is bounded by `K ‖z‖²`. -/
theorem abs_remainder_le3 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : G → ℝ}
    (hF : ContDiff ℝ 1 F) {K r : ℝ} (hK : 0 ≤ K)
    (hL : ∀ z : G, ‖z‖ ≤ r → ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ K * ‖z‖)
    (z : G) (hz : ‖z‖ ≤ r) : |F z - F 0 - fderiv ℝ F 0 z| ≤ K * ‖z‖ ^ 2 := by
  have key := (convex_closedBall (0 : G) ‖z‖).norm_image_sub_le_of_norm_fderiv_le'
    (f := F) (φ := fderiv ℝ F 0) (C := K * ‖z‖) (fun w _ => (hF.differentiable one_ne_zero) w)
    (fun w hw => by
      rw [mem_closedBall_zero_iff] at hw
      exact (hL w (hw.trans hz)).trans (mul_le_mul_of_nonneg_left hw hK))
    (Metric.mem_closedBall_self (norm_nonneg z)) (mem_closedBall_zero_iff.mpr le_rfl)
  simp only [sub_zero] at key
  rw [← Real.norm_eq_abs]
  calc _ ≤ K * ‖z‖ * ‖z‖ := key
    _ = K * ‖z‖ ^ 2 := by ring

/-- Woodford (2003), App. A.3, p. 633, erratum E18: a `C²` function has a derivative that is
Lipschitz near the steady state. -/
theorem lipschitz_fderiv3 {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : G → ℝ}
    (hF : ContDiff ℝ 2 F) :
    ∃ K r : ℝ, 0 ≤ K ∧ 0 < r ∧
      ∀ z : G, ‖z‖ ≤ r → ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ K * ‖z‖ := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.contDiffAt.exists_lipschitzOnWith (x := 0)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨K, r / 2, K.coe_nonneg, half_pos hr, fun z hz => ?_⟩
  have hz' : z ∈ t := hrt (by rw [mem_ball_zero_iff]; linarith)
  have h0 : (0 : G) ∈ t := hrt (Metric.mem_ball_self hr)
  have h := hK.dist_le_mul z hz' 0 h0
  rwa [dist_eq_norm, dist_eq_norm, sub_zero] at h

/-- Woodford (2003), App. A.3, p. 633, corrected per E18: if `DF` is Lipschitz near the steady
state, the exact equilibrium differs from the log-linear solution by at most `C ‖e‖∞²`. -/
theorem second_order3 {F : ℝ × ℝ × E → ℝ} (hF : ContDiff ℝ 1 F) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) {K r : ℝ} (hK : 0 ≤ K)
    (hL : ∀ z : ℝ × ℝ × E, ‖z‖ ≤ r → ‖fderiv ℝ F z - fderiv ℝ F 0‖ ≤ K * ‖z‖) (hr : 0 < r) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ e : Seq E, ‖e‖ < δ →
      ‖implicitSol3 F hF hab e - linSol3 F e‖ ≤ C * ‖e‖ ^ 2 := by
  obtain ⟨ε, hε, δ₁, hδ₁, -, hex, -⟩ := local_determinacy3 hF h0 hab
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ :=
    Metric.eventually_nhds_iff.mp ((hasFDerivAt_implicitSol3 hF h0 hab).isLittleO.def one_pos)
  set C1 := ‖linSol3 F‖ + 1 with hC1
  have hC1pos : 0 < C1 := by positivity
  have hC1one : 1 ≤ C1 := le_add_of_nonneg_left (norm_nonneg _)
  refine ⟨‖TInv (slopeA F) (slopeB F)‖ * (K * C1 ^ 2), min (min δ₁ δ₂) (r / C1), by positivity,
    fun e he => ?_⟩
  have he1 : ‖e‖ < δ₁ := lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_left _ _))
  have he2 : dist e 0 < δ₂ := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_right _ _))
  have he3 : C1 * ‖e‖ ≤ r := by
    have h : ‖e‖ < r / C1 := lt_of_lt_of_le he (min_le_right _ _)
    rw [lt_div_iff₀ hC1pos] at h
    linarith
  obtain ⟨-, hsol, -⟩ := hex e he1
  set x := implicitSol3 F hF hab e with hx
  have hxb : ‖x‖ ≤ C1 * ‖e‖ := by
    have h := hδ₂P he2
    rw [implicitSol3_zero hF h0 hab, sub_zero, sub_zero, one_mul] at h
    calc ‖x‖ = ‖(x - linSol3 F e) + linSol3 F e‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - linSol3 F e‖ + ‖linSol3 F e‖ := norm_add_le _ _
      _ ≤ ‖e‖ + ‖linSol3 F‖ * ‖e‖ := add_le_add h ((linSol3 F).le_opNorm e)
      _ = C1 * ‖e‖ := by rw [hC1]; ring
  have hcoord : ∀ t, |TOp (slopeA F) (slopeB F) (x - linSol3 F e) t| ≤ K * (C1 * ‖e‖) ^ 2 := by
    intro t
    have hz : ‖pt3 (e, x) t‖ ≤ C1 * ‖e‖ := by
      refine (norm_pt3_le _ t).trans ?_
      rw [Prod.norm_mk]
      exact max_le (le_mul_of_one_le_left (norm_nonneg _) hC1one) hxb
    have hrem := abs_remainder_le3 hF hK hL _ (hz.trans he3)
    have hD : fderiv ℝ F 0 (pt3 (e, x) t) = slopeA F * x t + slopeB F * x (t + 1) +
        slopeC F (e t) := fderiv_zero_apply3 F _ _ _
    have hl := linSol3_solves hab e t
    have hst : F (pt3 (e, x) t) = 0 := hsol t
    have e1 : TOp (slopeA F) (slopeB F) (x - linSol3 F e) t =
        -(F (pt3 (e, x) t) - F 0 - fderiv ℝ F 0 (pt3 (e, x) t)) := by
      rw [TOp_apply, hD, hst, h0]
      simp only [lp.coeFn_sub, Pi.sub_apply]
      linarith
    rw [e1, abs_neg]
    calc _ ≤ K * ‖pt3 (e, x) t‖ ^ 2 := hrem
      _ ≤ K * (C1 * ‖e‖) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) hK
  have hlin : ‖TOp (slopeA F) (slopeB F) (x - linSol3 F e)‖ ≤ K * (C1 * ‖e‖) ^ 2 :=
    norm_le_of_abs_le (by positivity) hcoord
  calc ‖x - linSol3 F e‖ =
        ‖TInv (slopeA F) (slopeB F) (TOp (slopeA F) (slopeB F) (x - linSol3 F e))‖ := by
        rw [TInv_TOp hab]
    _ ≤ ‖TInv (slopeA F) (slopeB F)‖ * ‖TOp (slopeA F) (slopeB F) (x - linSol3 F e)‖ :=
        (TInv _ _).le_opNorm _
    _ ≤ ‖TInv (slopeA F) (slopeB F)‖ * (K * (C1 * ‖e‖) ^ 2) :=
        mul_le_mul_of_nonneg_left hlin (norm_nonneg _)
    _ = ‖TInv (slopeA F) (slopeB F)‖ * (K * C1 ^ 2) * ‖e‖ ^ 2 := by ring

/-! ### Only the behaviour near the steady state matters (bump cut-off)

The book's hypotheses are local ("at least near the zero-inflation steady state", p. 95; "the
functions … need only be defined … near the steady state", A.3). We therefore only assume `F`
to be `C¹` (resp. `C²`) **near** `0`, and reduce to the global theory with a smooth bump
cut-off which equals one near the steady state. -/

/-- Woodford (2003), App. A.3, p. 631: the bump-cut-off version `χ_r · F` of a period condition,
equal to `F` on the ball of radius `r/4` and to `0` outside the ball of radius `r/2`. -/
noncomputable def cutoff (F : ℝ × ℝ × E → ℝ) (r : ℝ) (hr : 0 < r) : ℝ × ℝ × E → ℝ :=
  fun p => (⟨r / 4, r / 2, by positivity, by linarith⟩ : ContDiffBump (0 : ℝ × ℝ × E)) p * F p

/-- Woodford (2003), App. A.3, p. 631: the cut-off agrees with `F` near the steady state. -/
theorem cutoff_eq {F : ℝ × ℝ × E → ℝ} {r : ℝ} (hr : 0 < r) {p : ℝ × ℝ × E}
    (hp : ‖p‖ ≤ r / 4) : cutoff F r hr p = F p := by
  rw [cutoff, ContDiffBump.one_of_mem_closedBall _ (mem_closedBall_zero_iff.mpr hp), one_mul]

/-- Woodford (2003), App. A.3, p. 631: the cut-off agrees with `F` on a neighbourhood of `0`. -/
theorem cutoff_eventuallyEq (F : ℝ × ℝ × E → ℝ) {r : ℝ} (hr : 0 < r) :
    cutoff F r hr =ᶠ[𝓝 0] F := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ × E) (by positivity : 0 < r / 4)] with p hp
  rw [mem_ball_zero_iff] at hp
  exact cutoff_eq hr hp.le

/-- Woodford (2003), App. A.3, p. 632: the cut-off has the same derivative at the steady state. -/
theorem fderiv_cutoff (F : ℝ × ℝ × E → ℝ) {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (cutoff F r hr) 0 = fderiv ℝ F 0 :=
  (cutoff_eventuallyEq F hr).fderiv_eq

/-- Woodford (2003), App. A.3, p. 632: if `F` is `Cⁿ` on the ball of radius `r`, the cut-off is
`Cⁿ` everywhere. -/
theorem contDiff_cutoff {F : ℝ × ℝ × E → ℝ} {r : ℝ} (hr : 0 < r) {n : ℕ}
    (hF : ∀ p : ℝ × ℝ × E, ‖p‖ < r → ContDiffAt ℝ n F p) : ContDiff ℝ n (cutoff F r hr) := by
  set φ : ContDiffBump (0 : ℝ × ℝ × E) := ⟨r / 4, r / 2, by positivity, by linarith⟩ with hφ
  refine contDiff_iff_contDiffAt.mpr fun p => ?_
  by_cases hp : ‖p‖ < r
  · exact φ.contDiffAt.mul (hF p hp)
  · have hnot : p ∉ tsupport φ := by
      rw [φ.tsupport_eq, mem_closedBall_zero_iff]
      have : φ.rOut = r / 2 := rfl
      rw [this]
      push Not at hp ⊢
      linarith
    have hev : cutoff F r hr =ᶠ[𝓝 p] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with q hq
      change φ q * F q = 0
      rw [hq, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: a function `Cⁿ` at the steady state is `Cⁿ` on a ball
around it. -/
theorem exists_ball_contDiffAt {F : ℝ × ℝ × E → ℝ} {n : ℕ} (hF : ContDiffAt ℝ n F 0) :
    ∃ r > 0, ∀ p : ℝ × ℝ × E, ‖p‖ < r → ContDiffAt ℝ n F p := by
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (hF.eventually (by simp))
  exact ⟨r, hr, fun p hp => h (by rwa [dist_zero_right])⟩

/-- Woodford (2003), App. A.3, p. 632: the cut-off has the same slopes and the same log-linear
solution operator as `F`. -/
theorem linSol3_cutoff (F : ℝ × ℝ × E → ℝ) {r : ℝ} (hr : 0 < r) :
    slopeA (cutoff F r hr) = slopeA F ∧ slopeB (cutoff F r hr) = slopeB F ∧
      linSol3 (cutoff F r hr) = linSol3 F := by
  have h := fderiv_cutoff F hr
  refine ⟨by rw [slopeA, slopeA, h], by rw [slopeB, slopeB, h], ?_⟩
  simp only [linSol3, slopeA, slopeB, slopeC, h]

/-- Woodford (2003), App. A.3, p. 631: near the steady state the cut-off conditions and the
original conditions have the same solutions. -/
theorem solves_cutoff_iff {F : ℝ × ℝ × E → ℝ} {r : ℝ} (hr : 0 < r) {e : Seq E} {x : Linf}
    (he : ‖e‖ ≤ r / 4) (hx : ‖x‖ ≤ r / 4) : Solves (cutoff F r hr) e x ↔ Solves F e x := by
  have hp : ∀ t, ‖pt3 (e, x) t‖ ≤ r / 4 := fun t =>
    (norm_pt3_le _ t).trans (by rw [Prod.norm_mk]; exact max_le he hx)
  refine forall_congr' fun t => ?_
  have h : cutoff F r hr (pt3 (e, x) t) = F (pt3 (e, x) t) := cutoff_eq hr (hp t)
  exact ⟨fun h' => h ▸ h', fun h' => h.trans h'⟩

/-- Woodford (2003), App. A.3, pp. 632–633, **local form**: if `F` is `C¹` near the steady state,
`F(0) = 0` and `|b| < |a|`, there are `ε, δ > 0` and a map `X : ℓ∞(E) → ℓ∞` with `X(0) = 0`
and derivative the log-linear solution operator at `0` such that for every `‖e‖∞ < δ`, `X(e)`
is an equilibrium with `‖X(e)‖∞ < ε/2`, `X` is `C¹` near `e`, and every equilibrium with
`‖x‖∞ < ε` equals `X(e)`. The radii can be taken below any prescribed `η > 0`. -/
theorem local_determinacy_loc {F : ℝ × ℝ × E → ℝ} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : Seq E → Linf, X 0 = 0 ∧
      HasFDerivAt X (linSol3 F) 0 ∧
      ∀ e : Seq E, ‖e‖ < δ → ‖X e‖ < ε / 2 ∧ Solves F e (X e) ∧ ContDiffAt ℝ 1 X e ∧
        ∀ x : Linf, ‖x‖ < ε → Solves F e x → x = X e := by
  obtain ⟨r₀, hr₀, hball₀⟩ := exists_ball_contDiffAt hF
  set r := min r₀ η with hrdef
  have hr : 0 < r := lt_min hr₀ hη
  have hrη : r / 4 ≤ η := by linarith [min_le_right r₀ η]
  have hball : ∀ p : ℝ × ℝ × E, ‖p‖ < r → ContDiffAt ℝ 1 F p :=
    fun p hp => hball₀ p (lt_of_lt_of_le hp (min_le_left _ _))
  set G := cutoff F r hr with hG
  have hG1 : ContDiff ℝ 1 G := contDiff_cutoff hr hball
  obtain ⟨hsa, hsb, hls⟩ := linSol3_cutoff F hr
  have hab' : |slopeB G| < |slopeA G| := by rw [hsa, hsb]; exact hab
  have hG0 : G 0 = 0 := by rw [hG, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, -, hex, huniq⟩ := local_determinacy3 hG1 hG0 hab'
  set X := implicitSol3 G hG1 hab' with hX
  have hX0 : X 0 = 0 := implicitSol3_zero hG1 hG0 hab'
  have hcont : ContinuousAt X 0 :=
    (hasFDerivAt_implicitSol3 hG1 hG0 hab').continuousAt
  have hev : ∀ᶠ e in 𝓝 (0 : Seq E), ‖X e‖ < r / 8 := by
    have ht := hcont.tendsto
    rw [hX0] at ht
    exact (ht.eventually (Metric.ball_mem_nhds (0 : Linf) (by positivity : (0 : ℝ) < r / 8))).mono
      (fun e he => by simpa using he)
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min ε₀ (r / 4), lt_min hε₀ (by positivity), (min_le_right _ _).trans hrη,
    min (min δ₀ δ₁) (r / 4), lt_min (lt_min hδ₀ hδ₁) (by positivity),
    (min_le_right _ _).trans hrη, X, hX0, ?_, fun e he => ?_⟩
  · rw [← hls]
    exact hasFDerivAt_implicitSol3 hG1 hG0 hab'
  have he0 : ‖e‖ < δ₀ := lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_left _ _))
  have he1 : dist e 0 < δ₁ := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_right _ _))
  have he4 : ‖e‖ ≤ r / 4 := (lt_of_lt_of_le he (min_le_right _ _)).le
  obtain ⟨hXn, hXs, hXc⟩ := hex e he0
  have hXr := hδ₁P he1
  have hXr4 : ‖X e‖ ≤ r / 4 := by linarith
  refine ⟨by rw [lt_div_iff₀ two_pos]; exact lt_min (by linarith) (by linarith),
    (solves_cutoff_iff hr he4 hXr4).mp hXs, hXc,
    fun x hx hsol => ?_⟩
  have hx4 : ‖x‖ ≤ r / 4 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  exact huniq e he0 x (lt_of_lt_of_le hx (min_le_left _ _))
    ((solves_cutoff_iff hr he4 hx4).mpr hsol)

/-- Woodford (2003), App. A.3, p. 633 ("accurate up to a residual of order `O(ξ²)`"), **local
form**, corrected per E18: if `F` is `C²` near the steady state, every equilibrium with
`‖x‖∞ < ε` satisfies `‖x − x̂(e)‖∞ ≤ C ‖e‖∞²` for `‖e‖∞ < δ`, `x̂` the log-linear solution
(radii below any prescribed `η > 0`). -/
theorem second_order_loc {F : ℝ × ℝ × E → ℝ} (hF : ContDiffAt ℝ 2 F 0) (h0 : F 0 = 0)
    (hab : |slopeB F| < |slopeA F|) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ C : ℝ, ∀ e : Seq E, ‖e‖ < δ → ∀ x : Linf, ‖x‖ < ε →
      Solves F e x → ‖x - linSol3 F e‖ ≤ C * ‖e‖ ^ 2 := by
  obtain ⟨r₀, hr₀, hball₀⟩ := exists_ball_contDiffAt hF
  set r := min r₀ η with hrdef
  have hr : 0 < r := lt_min hr₀ hη
  have hrη : r / 4 ≤ η := by linarith [min_le_right r₀ η]
  have hball : ∀ p : ℝ × ℝ × E, ‖p‖ < r → ContDiffAt ℝ 2 F p :=
    fun p hp => hball₀ p (lt_of_lt_of_le hp (min_le_left _ _))
  set G := cutoff F r hr with hG
  have hG2 : ContDiff ℝ 2 G := contDiff_cutoff hr hball
  have hG1 : ContDiff ℝ 1 G := hG2.of_le (by norm_num)
  obtain ⟨hsa, hsb, hls⟩ := linSol3_cutoff F hr
  have hab' : |slopeB G| < |slopeA G| := by rw [hsa, hsb]; exact hab
  have hG0 : G 0 = 0 := by rw [hG, cutoff_eq hr (by rw [norm_zero]; positivity), h0]
  obtain ⟨ε₀, hε₀, δ₀, hδ₀, -, -, huniq⟩ := local_determinacy3 hG1 hG0 hab'
  obtain ⟨K, r', hK, hr', hL⟩ := lipschitz_fderiv3 hG2
  obtain ⟨C, δ₂, hδ₂, hC⟩ := second_order3 hG1 hG0 hab' hK hL hr'
  refine ⟨min ε₀ (r / 4), lt_min hε₀ (by positivity), (min_le_right _ _).trans hrη,
    min (min δ₀ δ₂) (r / 4), lt_min (lt_min hδ₀ hδ₂) (by positivity),
    (min_le_right _ _).trans hrη, C, fun e he x hx hsol => ?_⟩
  have he0 : ‖e‖ < δ₀ := lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_left _ _))
  have he2 : ‖e‖ < δ₂ := lt_of_lt_of_le he ((min_le_left _ _).trans (min_le_right _ _))
  have he4 : ‖e‖ ≤ r / 4 := (lt_of_lt_of_le he (min_le_right _ _)).le
  have hx4 : ‖x‖ ≤ r / 4 := (lt_of_lt_of_le hx (min_le_right _ _)).le
  have hxX := huniq e he0 x (lt_of_lt_of_le hx (min_le_left _ _))
    ((solves_cutoff_iff hr he4 hx4).mpr hsol)
  rw [← hls, hxX]
  exact hC e he2

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632 and the indeterminacy halves of Props. 2.6–2.8, 2.12–2.13,
**local form**: if `F` is `C¹` near the steady state, `F(0) = 0` and `|a| < |b|` (the root lies
inside the unit circle), then even with no disturbances every initial value `c` with `|c| ≤ r`
starts an exact equilibrium staying within `ε` of the steady state. -/
theorem local_indeterminacy_loc {F : ℝ × ℝ × E → ℝ} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hab : |slopeA F| < |slopeB F|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r →
      ∃ x : Linf, Solves F 0 x ∧ ‖x‖ ≤ ε ∧ x 0 = c := by
  intro ε hε
  set a := slopeA F with ha
  set b := slopeB F with hb
  have hκ : 0 < (|b| - |a|) / 2 := by linarith
  have hlo := ((hF.differentiableAt (by norm_num)).hasFDerivAt.isLittleO.def hκ)
  have hct : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ × E), ContinuousAt F p :=
    (hF.eventually (by simp)).mono fun p hp => hp.continuousAt
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp (hlo.and hct)
  have hb0 : b ≠ 0 := by
    rintro h
    rw [h, abs_zero] at hab
    linarith [abs_nonneg a]
  set r := min ε (ρ / 2) with hr
  have hr0 : 0 < r := lt_min hε (half_pos hρ)
  have hstep : ∀ y : ℝ, |y| ≤ r → ∃ z : ℝ, |z| ≤ |y| ∧ F (y, z, 0) = 0 := by
    intro y hy
    have hyρ : |y| < ρ := by linarith [min_le_right ε (ρ / 2)]
    have hnorm : ∀ z : ℝ, |z| ≤ |y| → ‖((y, z, 0) : ℝ × ℝ × E)‖ = |y| := fun z hz => by
      rw [Prod.norm_mk, Prod.norm_mk, norm_zero, Real.norm_eq_abs, Real.norm_eq_abs,
        max_eq_left (abs_nonneg z), max_eq_left hz]
    have happrox : ∀ z : ℝ, |z| ≤ |y| → |F (y, z, 0) - (a * y + b * z)| ≤ (|b| - |a|) / 2 * |y| :=
      fun z hz => by
        have h := (hρP (by rw [dist_zero_right, hnorm z hz]; exact hyρ)).1
        rw [sub_zero, h0, sub_zero, fderiv_zero_apply3, map_zero, add_zero, hnorm z hz,
          Real.norm_eq_abs] at h
        exact h
    have hcont : ContinuousOn (fun z : ℝ => F (y, z, 0)) (Set.Icc (-|y|) |y|) := by
      intro z hz
      have hz' : |z| ≤ |y| := abs_le.mpr hz
      have hpt : ContinuousAt F ((y, z, 0) : ℝ × ℝ × E) :=
        (hρP (by rw [dist_zero_right, hnorm z hz']; exact hyρ)).2
      have hf : ContinuousAt (fun z : ℝ => ((y, z, 0) : ℝ × ℝ × E)) z := by fun_prop
      exact (ContinuousAt.comp (g := F) (f := fun z : ℝ => ((y, z, 0) : ℝ × ℝ × E)) (x := z)
        hpt hf).continuousWithinAt
    have hle : -|y| ≤ |y| := by linarith [abs_nonneg y]
    have hay : |a * y| ≤ |a| * |y| := (abs_mul a y).le
    have hlow : ∀ z : ℝ, |z| ≤ |y| → b * z = |b| * |y| → 0 ≤ F (y, z, 0) := fun z hz hbz => by
      have h1 := happrox z hz
      have h2 := neg_abs_le (a * y)
      have h3 := (abs_le.mp h1).1
      nlinarith [abs_nonneg y]
    have hup : ∀ z : ℝ, |z| ≤ |y| → b * z = -(|b| * |y|) → F (y, z, 0) ≤ 0 := fun z hz hbz => by
      have h1 := happrox z hz
      have h2 := le_abs_self (a * y)
      have h3 := (abs_le.mp h1).2
      nlinarith [abs_nonneg y]
    have hyy : |(|y|)| ≤ |y| := (abs_abs y).le
    have hnyy : |(-|y|)| ≤ |y| := by rw [abs_neg, abs_abs]
    rcases lt_or_gt_of_ne hb0 with hbneg | hbpos
    · have hA : F (y, |y|, 0) ≤ 0 := hup _ hyy (by rw [abs_of_neg hbneg]; ring)
      have hB : 0 ≤ F (y, -|y|, 0) := hlow _ hnyy (by rw [abs_of_neg hbneg]; ring)
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hle hcont ⟨hA, hB⟩
      exact ⟨z, abs_le.mpr hz, hz0⟩
    · have hA : 0 ≤ F (y, |y|, 0) := hlow _ hyy (by rw [abs_of_pos hbpos])
      have hB : F (y, -|y|, 0) ≤ 0 := hup _ hnyy (by rw [abs_of_pos hbpos]; ring)
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hle hcont ⟨hB, hA⟩
      exact ⟨z, abs_le.mpr hz, hz0⟩
  choose! g hg using hstep
  refine ⟨r, hr0, fun c hc => ?_⟩
  have hseq : ∀ t, |g^[t] c| ≤ |c| := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (hg _ (ih.trans hc)).1.trans ih
  refine ⟨mk (fun t => g^[t] c) ⟨|c|, hseq⟩, fun t => ?_, ?_, rfl⟩
  · simp only [mk_apply, Function.iterate_succ_apply', lp.coeFn_zero, Pi.zero_apply]
    exact (hg _ ((hseq t).trans hc)).2
  · exact (norm_le_of_abs_le (abs_nonneg c) hseq).trans (hc.trans (min_le_left _ _))

/-! ### Slopes from one-dimensional derivatives -/

omit [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the slopes of `F` read off an explicit
derivative at the steady state. -/
theorem slopes_of_hasFDerivAt {F : ℝ × ℝ × E → ℝ} {F' : ℝ × ℝ × E →L[ℝ] ℝ}
    (h : HasFDerivAt F F' 0) :
    slopeA F = F' (1, 0, 0) ∧ slopeB F = F' (0, 1, 0) ∧ ∀ v : E, slopeC F v = F' (0, 0, v) := by
  refine ⟨by rw [slopeA, h.fderiv], by rw [slopeB, h.fderiv], fun v => ?_⟩
  simp only [slopeC, h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-! ### The scalar class `g(x_t, ν_t) − x_{t+1} = w_t` as an instance of the general class

The forward-looking scalar class of Props. 2.3 and 2.6 is the instance
`F(x, x', (ν, w)) = g(x, ν) − x' − w` of the class `F(x_t, x_{t+1}, e_t) = 0`, with the
disturbance vector `e_t = (ν_t, w_t) ∈ ℝ²`; all its results below are derived from the general
ones. -/

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `f₂ = ∂g/∂x` at the steady state. -/
noncomputable def slopeX (g : ℝ × ℝ → ℝ) : ℝ := fderiv ℝ g 0 (1, 0)

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: `∂g/∂ν` at the steady state. -/
noncomputable def slopeU (g : ℝ × ℝ → ℝ) : ℝ := fderiv ℝ g 0 (0, 1)

/-- Woodford (2003), App. A.3, p. 632: the derivative at the steady state in coordinates. -/
theorem fderiv_zero_apply (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ g 0 p = slopeX g * p.1 + slopeU g * p.2 := by
  have h : p = p.1 • ((1 : ℝ), (0 : ℝ)) + p.2 • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [h]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, slopeX, slopeU]
  ring

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631, scalar forward-looking case: the sequence
`x` solves the exact perfect-foresight equilibrium conditions `g(x_t, ν_t) − x_{t+1} = w_t`
(for all `t ≥ 0`) given the disturbance sequences `s = (ν, w)`. -/
def ScalarSolves (g : ℝ × ℝ → ℝ) (s : Linf × Linf) (x : Linf) : Prop :=
  ∀ t, g (x t, s.1 t) - x (t + 1) = s.2 t

/-- Woodford (2003), App. A.3, p. 632: the date-`t` disturbance pair `(ν_t, w_t)` is bounded by
the sup norm of `(ν, w)`. -/
theorem norm_pair_apply_le (s : Linf × Linf) (t : ℕ) : ‖((s.1 t, s.2 t) : ℝ × ℝ)‖ ≤ ‖s‖ := by
  rw [norm_prod_le_iff, Real.norm_eq_abs, Real.norm_eq_abs]
  exact ⟨(abs_apply_le _ t).trans (norm_fst_le s), (abs_apply_le _ t).trans (norm_snd_le s)⟩

/-- Woodford (2003), App. A.3, p. 632: two scalar disturbance sequences `(ν, w)` as one sequence
of disturbance vectors `e_t = (ν_t, w_t)` in `ℓ∞(ℝ²)`. -/
noncomputable def pairL : Linf × Linf →L[ℝ] Seq (ℝ × ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun s => mkS (fun t => ((s.1 t, s.2 t) : ℝ × ℝ)) ⟨‖s‖, norm_pair_apply_le s⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun s => by rw [one_mul]; exact norm_seq_le (norm_nonneg _) (norm_pair_apply_le s))

/-- Woodford (2003), App. A.3, p. 632: coordinates of `pairL`. -/
@[simp] theorem pairL_apply (s : Linf × Linf) (t : ℕ) : pairL s t = (s.1 t, s.2 t) := rfl

/-- Woodford (2003), App. A.3, p. 632: `pairL` does not increase the sup norm. -/
theorem norm_pairL_le (s : Linf × Linf) : ‖pairL s‖ ≤ ‖s‖ :=
  norm_seq_le (norm_nonneg _) (norm_pair_apply_le s)

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the projection `(x, x', (ν, w)) ↦ (x, ν)` onto
the arguments of `g`. -/
noncomputable def projXN : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × (ℝ × ℝ))).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ)))))

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: coordinates of `projXN`. -/
@[simp] theorem projXN_apply (p : ℝ × ℝ × (ℝ × ℝ)) : projXN p = (p.1, p.2.2.1) := rfl

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the linear part `(x, x', (ν, w)) ↦ x' + w` of
the scalar class. -/
noncomputable def leadL : ℝ × ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × (ℝ × ℝ))))

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: coordinates of `leadL`. -/
@[simp] theorem leadL_apply (p : ℝ × ℝ × (ℝ × ℝ)) : leadL p = p.2.1 + p.2.2.2 := rfl

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the scalar class as a period condition of the
general class, `F(x, x', (ν, w)) = g(x, ν) − (x' + w)`. -/
noncomputable def gF (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ × (ℝ × ℝ)) : ℝ := g (projXN p) - leadL p

/-- Woodford (2003), App. A.3, p. 631: the steady state solves the scalar period condition. -/
theorem gF_zero {g : ℝ × ℝ → ℝ} (h0 : g 0 = 0) : gF g 0 = 0 := by
  rw [gF, map_zero, map_zero, h0, sub_zero]

/-- Woodford (2003), App. A.3, p. 632: the scalar period condition is `Cⁿ` if `g` is. -/
theorem contDiff_gF {g : ℝ × ℝ → ℝ} {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (gF g) :=
  (hg.comp projXN.contDiff).sub leadL.contDiff

/-- Woodford (2003), App. A.3, p. 632: the scalar period condition is `Cⁿ` at the steady state
if `g` is. -/
theorem contDiffAt_gF {g : ℝ × ℝ → ℝ} {n : WithTop ℕ∞} (hg : ContDiffAt ℝ n g 0) :
    ContDiffAt ℝ n (gF g) 0 := by
  have hg' : ContDiffAt ℝ n g (projXN 0) := by rw [map_zero]; exact hg
  exact (hg'.comp 0 projXN.contDiff.contDiffAt).sub leadL.contDiff.contDiffAt

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the derivative of the scalar period condition
at any point where `g` is differentiable. -/
theorem fderiv_gF {g : ℝ × ℝ → ℝ} {z : ℝ × ℝ × (ℝ × ℝ)} (hg : DifferentiableAt ℝ g (projXN z)) :
    fderiv ℝ (gF g) z = (fderiv ℝ g (projXN z)).comp projXN - leadL :=
  ((hg.hasFDerivAt.comp z projXN.hasFDerivAt).sub leadL.hasFDerivAt).fderiv

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the slopes of the scalar class,
`a = ∂g/∂x`, `b = −1` and `c(ν, w) = (∂g/∂ν) ν − w`. -/
theorem slopes_gF {g : ℝ × ℝ → ℝ} (hg : DifferentiableAt ℝ g 0) :
    slopeA (gF g) = slopeX g ∧ slopeB (gF g) = -1 ∧
      ∀ v : ℝ × ℝ, slopeC (gF g) v = slopeU g * v.1 - v.2 := by
  have hg' : DifferentiableAt ℝ g (projXN 0) := by rw [map_zero]; exact hg
  obtain ⟨ha, hb, hc⟩ := slopes_of_hasFDerivAt (F := gF g)
    ((hg'.hasFDerivAt.comp 0 projXN.hasFDerivAt).sub leadL.hasFDerivAt)
  simp only [map_zero] at ha hb hc
  refine ⟨?_, ?_, fun v => ?_⟩
  · rw [ha]
    simp [slopeX]
  · rw [hb]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, projXN_apply, leadL_apply,
      fderiv_zero_apply, Prod.fst_zero, Prod.snd_zero]
    ring
  · rw [hc v]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, projXN_apply, leadL_apply,
      fderiv_zero_apply]
    ring

/-- Woodford (2003), App. A.3, eq. (A.9), p. 632: for the scalar class, `|∂g/∂x| > 1` is the
general root condition `|b| < |a|`. -/
theorem abs_slopeB_gF_lt {g : ℝ × ℝ → ℝ} (hg : DifferentiableAt ℝ g 0) (hb : 1 < |slopeX g|) :
    |slopeB (gF g)| < |slopeA (gF g)| := by
  obtain ⟨ha, hb', -⟩ := slopes_gF hg
  rwa [ha, hb', abs_neg, abs_one]

/-- Woodford (2003), App. A.3, eq. (A.7), p. 631: the scalar conditions with disturbances
`(ν, w)` are the general conditions with disturbance vectors `(ν_t, w_t)`. -/
theorem solves_gF_iff (g : ℝ × ℝ → ℝ) (s : Linf × Linf) (x : Linf) :
    Solves (gF g) (pairL s) x ↔ ScalarSolves g s x := by
  unfold Solves ScalarSolves gF
  simp only [projXN_apply, leadL_apply, pairL_apply]
  exact forall_congr' fun t => by constructor <;> intro h <;> linarith

/-- Woodford (2003), App. A.3, p. 633: the locally unique equilibrium `x = X(s)` of the scalar
class as a function of the disturbance sequences `s = (ν, w)`. -/
noncomputable def implicitSol (g : ℝ × ℝ → ℝ) (hg : ContDiff ℝ 1 g) (hb : 1 < |slopeX g|)
    (s : Linf × Linf) : Linf :=
  implicitSol3 (gF g) (contDiff_gF hg)
    (abs_slopeB_gF_lt (hg.differentiable one_ne_zero 0) hb) (pairL s)

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the solution operator of the linearised
equations `b x̂_t − x̂_{t+1} = w_t − c ν_t`, i.e. `s ↦ (b − S)⁻¹(w − c ν)`. -/
noncomputable def linSolOp (g : ℝ × ℝ → ℝ) : Linf × Linf →L[ℝ] Linf :=
  (linInv (slopeX g)).comp
    (ContinuousLinearMap.snd ℝ Linf Linf - slopeU g • ContinuousLinearMap.fst ℝ Linf Linf)

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: `linSolOp` solves the linearised equations. -/
theorem linOp_linSolOp {g : ℝ × ℝ → ℝ} (hb : 1 < |slopeX g|) (s : Linf × Linf) :
    linOp (slopeX g) (linSolOp g s) = s.2 - slopeU g • s.1 :=
  linOp_linInv hb _

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the linearised equations have exactly one
bounded solution, `linSolOp s`. -/
theorem eq_linSolOp {g : ℝ × ℝ → ℝ} (hb : 1 < |slopeX g|) {s : Linf × Linf} {x : Linf}
    (h : ∀ t, slopeX g * x t - x (t + 1) = s.2 t - slopeU g * s.1 t) : x = linSolOp g s := by
  refine (linInv_eq hb ?_).symm
  ext t
  simp [h t]
  rfl

/-- Woodford (2003), eq. (1.37), p. 81 and App. A.4, (A.16): the log-linear solution as a forward
sum, `x̂_t = ∑_{k ≥ 0} b^{-(k+1)} (w_{t+k} − c ν_{t+k})`. -/
theorem linSolOp_apply {g : ℝ × ℝ → ℝ} (hb : 1 < |slopeX g|) (s : Linf × Linf) (t : ℕ) :
    linSolOp g s t = ∑' k, (slopeX g)⁻¹ ^ (k + 1) * (s.2 (t + k) - slopeU g * s.1 (t + k)) := by
  rw [linSolOp, ContinuousLinearMap.comp_apply, linInv_apply hb]
  rfl

/-- Woodford (2003), App. A.3, eq. (A.10), p. 633: the general log-linear solution operator of
the scalar class is `linSolOp`. -/
theorem linSol3_gF {g : ℝ × ℝ → ℝ} (hg : DifferentiableAt ℝ g 0) (hb : 1 < |slopeX g|) :
    (linSol3 (gF g)).comp pairL = linSolOp g := by
  obtain ⟨ha, hb', hc⟩ := slopes_gF hg
  refine ContinuousLinearMap.ext fun s => eq_linSolOp hb fun t => ?_
  have h := linSol3_solves (abs_slopeB_gF_lt hg hb) (pairL s) t
  rw [ha, hb', hc, pairL_apply] at h
  simp only [ContinuousLinearMap.comp_apply]
  linarith

/-- Woodford (2003), App. A.3, p. 633: with no disturbances the locally unique equilibrium is the
steady state. -/
theorem implicitSol_zero {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (h0 : g 0 = 0)
    (hb : 1 < |slopeX g|) : implicitSol g hg hb 0 = 0 := by
  rw [implicitSol, map_zero]
  exact implicitSol3_zero _ (gF_zero h0) _

/-- Woodford (2003), App. A.3, p. 633 and (A.5), p. 630, task (iii): **the first-order term of
the exact equilibrium is the log-linear solution**: the equilibrium map `s ↦ X(s)` is Fréchet
differentiable at `s = 0` with derivative `linSolOp`, the unique bounded solution operator of the
linearised equations (A.10). The scalar instance of `hasFDerivAt_implicitSol3`. -/
theorem hasFDerivAt_implicitSol {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (h0 : g 0 = 0)
    (hb : 1 < |slopeX g|) : HasFDerivAt (implicitSol g hg hb) (linSolOp g) 0 := by
  have hd : DifferentiableAt ℝ g 0 := hg.differentiable one_ne_zero 0
  have h1 : HasFDerivAt (implicitSol3 (gF g) (contDiff_gF hg) (abs_slopeB_gF_lt hd hb))
      (linSol3 (gF g)) (pairL 0) := by
    rw [map_zero]
    exact hasFDerivAt_implicitSol3 _ (gF_zero h0) _
  have h := h1.comp (0 : Linf × Linf) pairL.hasFDerivAt
  rwa [linSol3_gF hd hb] at h

/-- Woodford (2003), App. A.3, pp. 632–633 and Prop. 2.3 (A.4, p. 635), task (iii): **local
determinacy of the exact perfect-foresight model.** If `g` is `C¹`, `g(0,0) = 0` (steady state)
and the linearised operator is invertible (`|∂g/∂x| > 1`), there are radii `ε, δ > 0` such that
for every disturbance pair `s = (ν, w)` with `‖s‖∞ < δ`:
* `X(s)` is an equilibrium with `‖X(s)‖∞ < ε/2`;
* every equilibrium `x` with `‖x‖∞ < ε` equals `X(s)` (local uniqueness);
* `X` is `C¹` near `s` (`C¹` dependence on the shocks).
The scalar instance of `local_determinacy3`. -/
theorem local_determinacy {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (h0 : g 0 = 0)
    (hb : 1 < |slopeX g|) :
    ∃ ε > 0, ∃ δ > 0, δ ≤ ε ∧
      (∀ s : Linf × Linf, ‖s‖ < δ →
        ‖implicitSol g hg hb s‖ < ε / 2 ∧ ScalarSolves g s (implicitSol g hg hb s) ∧
          ContDiffAt ℝ 1 (implicitSol g hg hb) s) ∧
      (∀ s : Linf × Linf, ‖s‖ < δ → ∀ x : Linf, ‖x‖ < ε → ScalarSolves g s x →
        x = implicitSol g hg hb s) := by
  obtain ⟨ε, hε, δ, hδ, hδε, hex, huniq⟩ := local_determinacy3 (contDiff_gF hg) (gF_zero h0)
    (abs_slopeB_gF_lt (hg.differentiable one_ne_zero 0) hb)
  refine ⟨ε, hε, δ, hδ, hδε, fun s hs => ?_, fun s hs x hx hsol => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hex _ ((norm_pairL_le s).trans_lt hs)
    exact ⟨h1, (solves_gF_iff g s _).mp h2, h3.comp s pairL.contDiff.contDiffAt⟩
  · exact huniq _ ((norm_pairL_le s).trans_lt hs) x hx ((solves_gF_iff g s x).mpr hsol)

/-! ### Second-order accuracy (erratum E18) -/

/-- Woodford (2003), App. A.3, p. 633 and Prop. 2.3 ("accurate up to a residual of order
`O(ξ²)`"), task (iv), corrected per E18: **if `Dg` is Lipschitz near the steady state
(`C^{1,1}`, in particular if `g` is `C²`), the exact equilibrium differs from the log-linear
solution by at most `C ‖s‖∞²`** for all disturbances small in `ℓ∞`. The scalar instance of
`second_order3`. -/
theorem second_order_accuracy {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (h0 : g 0 = 0)
    (hb : 1 < |slopeX g|) {K r : ℝ} (hK : 0 ≤ K)
    (hL : ∀ z : ℝ × ℝ, ‖z‖ ≤ r → ‖fderiv ℝ g z - fderiv ℝ g 0‖ ≤ K * ‖z‖) (hr : 0 < r) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : Linf × Linf, ‖s‖ < δ →
      ‖implicitSol g hg hb s - linSolOp g s‖ ≤ C * ‖s‖ ^ 2 := by
  have hd : ∀ z, DifferentiableAt ℝ g z := hg.differentiable one_ne_zero
  have hP : ∀ p : ℝ × ℝ × (ℝ × ℝ), ‖projXN p‖ ≤ ‖p‖ := fun p => by
    rw [projXN_apply, norm_prod_le_iff]
    exact ⟨norm_fst_le p, (norm_fst_le p.2.2).trans ((norm_snd_le p.2).trans (norm_snd_le p))⟩
  have hPn : ‖projXN‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by rw [one_mul]; exact hP p
  have hL' : ∀ z : ℝ × ℝ × (ℝ × ℝ), ‖z‖ ≤ r →
      ‖fderiv ℝ (gF g) z - fderiv ℝ (gF g) 0‖ ≤ K * ‖z‖ := by
    intro z hz
    rw [fderiv_gF (hd _), fderiv_gF (hd _), map_zero, sub_sub_sub_cancel_right,
      ← ContinuousLinearMap.sub_comp]
    calc _ ≤ ‖fderiv ℝ g (projXN z) - fderiv ℝ g 0‖ * ‖projXN‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * ‖projXN z‖ * 1 :=
          mul_le_mul (hL _ ((hP z).trans hz)) hPn (norm_nonneg _) (by positivity)
      _ ≤ K * ‖z‖ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left (hP z) hK
  obtain ⟨C, δ, hδ, hC⟩ := second_order3 (contDiff_gF hg) (gF_zero h0)
    (abs_slopeB_gF_lt (hd 0) hb) hK hL' hr
  refine ⟨max C 0, δ, hδ, fun s hs => ?_⟩
  have h := hC _ ((norm_pairL_le s).trans_lt hs)
  have hl : linSol3 (gF g) (pairL s) = linSolOp g s := by
    rw [← linSol3_gF (hd 0) hb, ContinuousLinearMap.comp_apply]
  rw [hl] at h
  refine h.trans ?_
  calc C * ‖pairL s‖ ^ 2 ≤ max C 0 * ‖pairL s‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (norm_pairL_le s) 2) (le_max_right _ _)

/-- Woodford (2003), App. A.3, p. 633 and Prop. 2.3, task (iv): the `O(ξ²)` accuracy of the
log-linear solution for a `C²` equilibrium condition. -/
theorem second_order_accuracy_of_contDiff_two {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg2 : ContDiff ℝ 2 g) (h0 : g 0 = 0) (hb : 1 < |slopeX g|) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : Linf × Linf, ‖s‖ < δ →
      ‖implicitSol g hg hb s - linSolOp g s‖ ≤ C * ‖s‖ ^ 2 := by
  obtain ⟨K, r, hK, hr, hL⟩ := lipschitz_fderiv3 hg2
  exact second_order_accuracy hg h0 hb hK hL hr

/-- Woodford (2003), App. A.3, p. 633, erratum E18: a `C¹` (not `C^{1,1}`) equilibrium
condition `g(x, ν) = 2x + ν + ν^{3/2}` (real power; `ν^{3/2} = 0` for `ν ≤ 0` in Mathlib). -/
noncomputable def gE (p : ℝ × ℝ) : ℝ := 2 * p.1 + p.2 + p.2 ^ (3 / 2 : ℝ)

/-- Woodford (2003), App. A.3, erratum E18: the counterexample is `C¹`. -/
theorem contDiff_gE : ContDiff ℝ 1 gE := by
  have h : ContDiff ℝ 1 (fun y : ℝ => y ^ (3 / 2 : ℝ)) := by
    have h' := Real.contDiff_rpow_const_of_le (p := 3 / 2) (n := 1) (by norm_num)
    simpa using h'
  exact ((contDiff_const.mul contDiff_fst).add contDiff_snd).add (h.comp contDiff_snd)

/-- Woodford (2003), App. A.3, erratum E18: the derivative of the counterexample at the steady
state. -/
theorem hasFDerivAt_gE : HasFDerivAt gE
    ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ +
      (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := by
  have hr : HasDerivAt (fun y : ℝ => y ^ (3 / 2 : ℝ)) 0 ((0 : ℝ × ℝ).2) := by
    have h' := Real.hasDerivAt_rpow_const (x := 0) (p := 3 / 2) (Or.inr (by norm_num))
    norm_num at h'
    simpa using h'
  exact ((hasFDerivAt_fst.const_mul 2).add hasFDerivAt_snd).add
    (hr.comp_hasFDerivAt (0 : ℝ × ℝ) hasFDerivAt_snd)

/-- Woodford (2003), App. A.3, erratum E18: `∂g/∂x = 2` for the counterexample. -/
theorem slopeX_gE : slopeX gE = 2 := by
  rw [slopeX, hasFDerivAt_gE.fderiv]
  simp

/-- Woodford (2003), App. A.3, erratum E18: `∂g/∂ν = 1` for the counterexample. -/
theorem slopeU_gE : slopeU gE = 1 := by
  rw [slopeU, hasFDerivAt_gE.fderiv]
  simp

/-- Woodford (2003), App. A.3, erratum E18: the counterexample is determinate (`|b| = 2 > 1`). -/
theorem one_lt_abs_slopeX_gE : 1 < |slopeX gE| := by
  rw [slopeX_gE]
  norm_num

/-- Woodford (2003), App. A.3, erratum E18: `(η²)^{3/2} = η³` for `η ≥ 0`. -/
theorem sq_rpow_three_halves {η : ℝ} (hη : 0 ≤ η) : (η ^ 2) ^ (3 / 2 : ℝ) = η ^ 3 := by
  rw [← Real.rpow_natCast η 2, ← Real.rpow_mul hη]
  norm_num

/-- Woodford (2003), App. A.3, p. 633, erratum E18, **counterexample to the printed `O(‖u‖²)`
claim under mere (continuous) differentiability**: for the `C¹` model `gE` the locally unique
exact equilibrium is *not* within `C ‖s‖∞²` of the log-linear solution for any `C`, `δ`
(the error along `ν_t ≡ ξ` is exactly `ξ^{3/2}`). So the book's claim needs `C²` (or `C^{1,1}`),
as in `second_order_accuracy`; for `C¹` only the `o(‖s‖)` statement `hasFDerivAt_implicitSol`
holds. -/
theorem not_second_order_of_C1 :
    ¬ ∃ C δ : ℝ, 0 < δ ∧ ∀ s : Linf × Linf, ‖s‖ < δ →
      ‖implicitSol gE contDiff_gE one_lt_abs_slopeX_gE s - linSolOp gE s‖ ≤ C * ‖s‖ ^ 2 := by
  rintro ⟨C, δ, hδ, hC⟩
  have h0 : gE 0 = 0 := by norm_num [gE]
  obtain ⟨ε, hε, δ₁, hδ₁, -, -, huniq⟩ := local_determinacy contDiff_gE h0 one_lt_abs_slopeX_gE
  set m := min (min (min δ δ₁) (min ε 1)) (1 / (|C| + 1)) with hm
  have hCpos : 0 < |C| + 1 := by positivity
  have hm0 : 0 < m := by
    refine lt_min (lt_min (lt_min hδ hδ₁) (lt_min hε one_pos)) (by positivity)
  set η := m / 2 with hη
  have hη0 : 0 < η := by positivity
  have hmδ : m ≤ δ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hmδ₁ : m ≤ δ₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hmε : m ≤ ε := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm1 : m ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmC : m ≤ 1 / (|C| + 1) := min_le_right _ _
  have hη1 : η < 1 := by linarith
  have hηsq : η ^ 2 < η := by nlinarith
  have hηcube : η ^ 3 < η := by nlinarith
  have hCη : |C| * η < 1 := by
    have h1 : (|C| + 1) * m ≤ 1 := by
      rw [le_div_iff₀ hCpos] at hmC
      linarith
    nlinarith [abs_nonneg C]
  set s : Linf × Linf := (const (η ^ 2), 0) with hs
  have hsnorm : ‖s‖ ≤ η ^ 2 := by
    rw [hs, Prod.norm_mk]
    refine max_le (norm_le_of_abs_le (by positivity) (fun t => ?_)) (by rw [norm_zero]; positivity)
    simp [abs_of_nonneg (sq_nonneg η)]
  have hsδ : ‖s‖ < δ := by linarith
  have hsδ₁ : ‖s‖ < δ₁ := by linarith
  set x : Linf := const (-(η ^ 2 + η ^ 3)) with hx
  have hxsol : ScalarSolves gE s x := by
    intro t
    simp only [hx, hs, const_apply, gE, lp.coeFn_zero, Pi.zero_apply]
    rw [sq_rpow_three_halves hη0.le]
    ring
  have hxnorm : ‖x‖ < ε := by
    have h : ‖x‖ ≤ η ^ 2 + η ^ 3 :=
      norm_le_of_abs_le (by positivity) (fun t => by
        rw [hx, const_apply, abs_neg, abs_of_nonneg (by positivity)])
    linarith
  have hX : x = implicitSol gE contDiff_gE one_lt_abs_slopeX_gE s :=
    huniq s hsδ₁ x hxnorm hxsol
  have hL : const (-(η ^ 2)) = linSolOp gE s := by
    refine eq_linSolOp one_lt_abs_slopeX_gE (fun t => ?_)
    simp only [slopeX_gE, slopeU_gE, const_apply, hs, lp.coeFn_zero, Pi.zero_apply]
    ring
  have herr := hC s hsδ
  rw [← hX, ← hL] at herr
  have hlow : η ^ 3 ≤ ‖x - const (-(η ^ 2))‖ := by
    have h := abs_apply_le (x - const (-(η ^ 2))) 0
    have e : (x - const (-(η ^ 2))) 0 = -(η ^ 3) := by
      simp only [lp.coeFn_sub, Pi.sub_apply, hx, const_apply]
      ring
    rw [e, abs_neg, abs_of_nonneg (by positivity)] at h
    exact h
  have hup : C * ‖s‖ ^ 2 ≤ |C| * (η ^ 2) ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsnorm 2) (abs_nonneg C))
  have hfin : η ^ 3 ≤ |C| * η ^ 4 := by nlinarith
  have hfin' : η ^ 3 * (1 - |C| * η) ≤ 0 := by nlinarith
  have hpos : 0 < η ^ 3 * (1 - |C| * η) := mul_pos (by positivity) (by linarith)
  linarith

/-! ### Local indeterminacy when the root lies inside the unit circle -/

/-- Woodford (2003), App. A.3, p. 632 and Prop. 2.6 (indeterminacy half), exact model: if `g` is
`C¹` near the steady state and `|∂g/∂x| < 1` there, then even with no disturbances there is a
continuum of perfect-foresight equilibria arbitrarily close to the steady state: for every
`ε > 0` there is `r > 0` such that every initial value `c` with `|c| ≤ r` starts an equilibrium
staying within `ε` of the steady state. The scalar instance of `local_indeterminacy_loc`. -/
theorem local_indeterminacy {g : ℝ × ℝ → ℝ} (hg : ContDiffAt ℝ 1 g 0) (h0 : g 0 = 0)
    (hb : |slopeX g| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r →
      ∃ x : Linf, ScalarSolves g 0 x ∧ ‖x‖ ≤ ε ∧ x 0 = c := by
  obtain ⟨ha, hb', -⟩ := slopes_gF (hg.differentiableAt (by norm_num))
  have hab : |slopeA (gF g)| < |slopeB (gF g)| := by rwa [ha, hb', abs_neg, abs_one]
  intro ε hε
  obtain ⟨r, hr, h⟩ := local_indeterminacy_loc (contDiffAt_gF hg) (gF_zero h0) hab ε hε
  refine ⟨r, hr, fun c hc => ?_⟩
  obtain ⟨x, hx, hxn, hx0⟩ := h c hc
  refine ⟨x, (solves_gF_iff g 0 x).mp ?_, hxn, hx0⟩
  rwa [map_zero]

/-! ### The exact Wicksellian and Taylor-rule models under perfect foresight -/

/-- Woodford (2003), eqs. (1.30) and (2.4), pp. 77, 90: the policy rule in logs,
`(a, ν) ↦ log(1 + φ(eᵃ; ν)) + log β = log((1 + i)/(1 + ī))` at a zero-inflation steady state
(`1 + ī = β⁻¹`); `a` is `log(P_t/P_t^*)` (Wicksell) or `log(Π_t/Π_t^*)` (Taylor). -/
noncomputable def logRule (β : ℝ) (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.log (1 + φ (Real.exp p.1, p.2)) + Real.log β

/-- Woodford (2003), eq. (1.34), p. 81 and (2.5), p. 91: the elasticity of `1 + φ` with respect
to its first argument at the steady state (`φ_p` for a Wicksellian rule, `φ_π` for a Taylor
rule): `β ∂φ/∂(P/P*)(1; 0)`. -/
noncomputable def elast (β : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ := β * fderiv ℝ φ (1, 0) (1, 0)

/-- Woodford (2003), fn. 15, p. 81: the coefficient of `ν` in the log-linear rule,
`β ∂φ/∂ν(1; 0)` (normalised to one in the book). -/
noncomputable def elastNu (β : ℝ) (φ : ℝ × ℝ → ℝ) : ℝ := β * fderiv ℝ φ (1, 0) (0, 1)

/-- Woodford (2003), (1.30)/(2.4): if `φ` is `Cⁿ` on `(0, ∞) × ℝ` and `1 + φ > 0`, the log rule is
`Cⁿ` on `ℝ²`. -/
theorem contDiff_logRule {β : ℝ} {φ : ℝ × ℝ → ℝ} {n : WithTop ℕ∞}
    (hφ : ContDiffOn ℝ n φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν)) : ContDiff ℝ n (logRule β φ) := by
  have hE : ContDiff ℝ n (fun p : ℝ × ℝ => (Real.exp p.1, p.2)) :=
    (Real.contDiff_exp.comp contDiff_fst).prodMk contDiff_snd
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => φ (Real.exp p.1, p.2)) :=
    hφ.comp_contDiff hE (fun p => ⟨Real.exp_pos p.1, Set.mem_univ _⟩)
  exact ((contDiff_const.add h1).log (fun p => (hpos _ (Real.exp_pos _) _).ne')).add
    contDiff_const

/-- Woodford (2003), p. 78 (`1 + φ(1; 0) = π̄/β` with `π̄ = 1`): the steady state solves the log
rule. -/
theorem logRule_zero {β : ℝ} {φ : ℝ × ℝ → ℝ} (hss : 1 + φ (1, 0) = β⁻¹) :
    logRule β φ 0 = 0 := by
  simp [logRule, hss, Real.log_inv]

/-- Woodford (2003), eqs. (1.34) and (2.5), pp. 81, 91, as exact derivative facts: the slopes of
the log rule at the steady state are `φ_p` (resp. `φ_π`) and the `ν`-coefficient. -/
theorem slopes_logRule {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφd : DifferentiableAt ℝ φ (1, 0)) :
    slopeX (logRule β φ) = elast β φ ∧ slopeU (logRule β φ) = elastNu β φ := by
  have hE : HasFDerivAt (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
      ((Real.exp (0 : ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) 0 :=
    ((Real.hasDerivAt_exp _).comp_hasFDerivAt (0 : ℝ × ℝ) hasFDerivAt_fst).prodMk
      hasFDerivAt_snd
  have hφ' : HasFDerivAt φ (fderiv ℝ φ (1, 0)) ((fun p : ℝ × ℝ => (Real.exp p.1, p.2)) 0) := by
    simpa using hφd.hasFDerivAt
  have hc := hφ'.comp (0 : ℝ × ℝ) hE
  have hne : 1 + (φ ∘ fun p : ℝ × ℝ => (Real.exp p.1, p.2)) 0 ≠ 0 := by
    simp [hss, hβ.ne']
  have hf : HasFDerivAt (logRule β φ) _ 0 := ((hc.const_add 1).log hne).add_const (Real.log β)
  refine ⟨?_, ?_⟩
  · rw [slopeX, hf.fderiv]
    simp [hss, elast]
  · rw [slopeU, hf.fderiv]
    simp [hss, elastNu]

/-- Woodford (2003), eq. (1.36), p. 81, exact (perfect-foresight) form: the Wicksellian
equilibrium condition in `p_t = log(P_t/P_t^*)` is `gW(p_t, ν_t) − p_{t+1} = w_t` with
`gW(p, ν) = log(1 + φ(eᵖ; ν)) + log β + p`. -/
noncomputable def gW (β : ℝ) (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := logRule β φ p + p.1

/-- Woodford (2003), (1.36): `gW` is `Cⁿ`. -/
theorem contDiff_gW {β : ℝ} {φ : ℝ × ℝ → ℝ} {n : WithTop ℕ∞}
    (hφ : ContDiffOn ℝ n φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν)) : ContDiff ℝ n (gW β φ) :=
  (contDiff_logRule hφ hpos).add contDiff_fst

/-- Woodford (2003), (1.36): the steady state solves `gW`. -/
theorem gW_zero {β : ℝ} {φ : ℝ × ℝ → ℝ} (hss : 1 + φ (1, 0) = β⁻¹) :
    gW β φ 0 = 0 := by
  simp [gW, logRule_zero hss]

/-- Woodford (2003), eq. (1.36), p. 81, as an exact derivative fact: `∂gW/∂p = 1 + φ_p` and
`∂gW/∂ν = ` the `ν`-coefficient. -/
theorem slopes_gW {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφd : DifferentiableAt ℝ φ (1, 0)) (hl : DifferentiableAt ℝ (logRule β φ) 0) :
    slopeX (gW β φ) = 1 + elast β φ ∧ slopeU (gW β φ) = elastNu β φ := by
  have h : HasFDerivAt (gW β φ) (fderiv ℝ (logRule β φ) 0 + ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
    hl.hasFDerivAt.add hasFDerivAt_fst
  obtain ⟨h1, h2⟩ := slopes_logRule hβ hss hφd
  refine ⟨?_, ?_⟩
  · rw [slopeX, h.fderiv, ← h1, slopeX]
    simp
    ring
  · rw [slopeU, h.fderiv, ← h2, slopeU]
    simp

/-- Woodford (2003), (1.30)/(2.4): the level policy rule and its log form are equivalent:
`1 + φ(A; ν) = B` iff `log(1 + φ(A; ν)) + log β = log B + log β` (for `A, B > 0`). -/
theorem rule_iff {β : ℝ} {φ : ℝ × ℝ → ℝ} (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    {A B ν : ℝ} (hA : 0 < A) (hB : 0 < B) :
    1 + φ (A, ν) = B ↔ logRule β φ (Real.log A, ν) = Real.log B + Real.log β := by
  simp only [logRule, Real.exp_log hA]
  constructor
  · intro h
    rw [h]
  · intro h
    have h' : Real.log (1 + φ (A, ν)) = Real.log B := by linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (hpos A hA ν)) (Set.mem_Ioi.mpr hB) h'

/-- Woodford (2003), eq. (1.21), p. 72 (perfect foresight, `C = Y`) and (1.30), p. 77: a
**Wicksellian perfect-foresight equilibrium**: positive prices `P` and interest rates `i` with
`1 + i_t = u_c(t)/(β u_c(t+1)) · P_{t+1}/P_t` and `i_t = φ(P_t/P_t^*; ν_t)` for all `t ≥ 0`,
given the marginal-utility path `u_c(t) = u_c(Y_t; ξ_t) > 0`, the target `P^* > 0` and `ν`. -/
def WicksellEq (β : ℝ) (φ : ℝ × ℝ → ℝ) (uc Pstar ν P i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < P t) ∧ (∀ t, 1 + i t = uc t / (β * uc (t + 1)) * (P (t + 1) / P t)) ∧
    ∀ t, i t = φ (P t / Pstar t, ν t)

/-- Woodford (2003), eqs. (1.33) and (1.36), pp. 80–81: the composite disturbance of the
Wicksellian model, `w_t = r̂_t + π*_{t+1}` with `r̂_t = log(u_c(t)/u_c(t+1))` (the log gross real
rate times `β`) and `π*_{t+1} = log(P*_{t+1}/P*_t)`. -/
noncomputable def wW (uc Pstar : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.log (uc t / uc (t + 1)) + Real.log (Pstar (t + 1) / Pstar t)

/-- Woodford (2003), eq. (1.36), p. 81, exact form: one date of the Wicksellian equilibrium
conditions, in levels and in logs. -/
theorem wicksell_step {β : ℝ} {φ : ℝ × ℝ → ℝ}
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν)) (hβ : 0 < β)
    {P0 P1 S0 S1 u0 u1 ν : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1) (hS0 : 0 < S0) (hS1 : 0 < S1)
    (hu0 : 0 < u0) (hu1 : 0 < u1) :
    1 + φ (P0 / S0, ν) = u0 / (β * u1) * (P1 / P0) ↔
      gW β φ (Real.log (P0 / S0), ν) - Real.log (P1 / S1) =
        Real.log (u0 / u1) + Real.log (S1 / S0) := by
  rw [rule_iff (β := β) hpos (div_pos hP0 hS0) (by positivity)]
  have e1 : Real.log (u0 / (β * u1) * (P1 / P0)) =
      Real.log u0 - Real.log β - Real.log u1 + Real.log P1 - Real.log P0 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul hβ.ne' hu1.ne', Real.log_div hP1.ne' hP0.ne']
    ring
  dsimp only [gW]
  rw [e1, Real.log_div hP0.ne' hS0.ne', Real.log_div hP1.ne' hS1.ne',
    Real.log_div hu0.ne' hu1.ne', Real.log_div hS1.ne' hS0.ne']
  constructor <;> intro h <;> linarith

/-- Woodford (2003), Prop. 2.3, p. 82 and App. A.4, p. 635, **exact perfect-foresight version**
(task (iii)): under a Wicksellian rule `φ` that is `C¹` on `(0, ∞) × ℝ`, keeps `1 + i > 0`,
supports the zero-inflation steady state (`1 + φ(1; 0) = β⁻¹`) and has `φ_p > 0`, there are
`ε, δ > 0` such that for all exogenous paths whose disturbances `ν_t` and
`w_t = r̂_t + π*_{t+1}` stay within `δ`, there is an equilibrium with `|log(P_t/P_t^*)| ≤ ε` for
all `t`, and it is the only one: any two equilibria in that neighbourhood coincide (prices and
interest rates). -/
theorem wicksell_local_determinacy {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    (hss : 1 + φ (1, 0) = β⁻¹) (hφp : 0 < elast β φ) :
    ∃ ε > 0, ∃ δ > 0, ∀ uc Pstar ν : ℕ → ℝ, (∀ t, 0 < uc t) → (∀ t, 0 < Pstar t) →
      (∀ t, |ν t| ≤ δ) → (∀ t, |wW uc Pstar t| ≤ δ) →
      (∃ P i : ℕ → ℝ, WicksellEq β φ uc Pstar ν P i ∧
        ∀ t, |Real.log (P t / Pstar t)| ≤ ε) ∧
      ∀ P i P' i' : ℕ → ℝ, WicksellEq β φ uc Pstar ν P i → WicksellEq β φ uc Pstar ν P' i' →
        (∀ t, |Real.log (P t / Pstar t)| ≤ ε) → (∀ t, |Real.log (P' t / Pstar t)| ≤ ε) →
        P = P' ∧ i = i' := by
  have hg : ContDiff ℝ 1 (gW β φ) := contDiff_gW hφ hpos
  have hφd : DifferentiableAt ℝ φ (1, 0) :=
    (hφ.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr one_pos, Set.mem_univ _⟩))
  have hl : DifferentiableAt ℝ (logRule β φ) 0 :=
    (contDiff_logRule hφ hpos).differentiable one_ne_zero 0
  obtain ⟨hsx, -⟩ := slopes_gW hβ hss hφd hl
  have hb : 1 < |slopeX (gW β φ)| := by
    rw [hsx, abs_of_pos (by linarith)]
    linarith
  obtain ⟨ε, hε, δ, hδ, -, hex, huniq⟩ := local_determinacy hg (gW_zero hss) hb
  refine ⟨ε / 2, half_pos hε, δ / 2, half_pos hδ, fun uc Pstar ν huc hPs hν hw => ?_⟩
  set s : Linf × Linf := (mk ν ⟨δ / 2, hν⟩, mk (wW uc Pstar) ⟨δ / 2, hw⟩) with hsdef
  have hs : ‖s‖ < δ := by
    rw [hsdef, Prod.norm_mk]
    exact max_lt (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hν) (half_lt_self hδ))
      (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hw) (half_lt_self hδ))
  have htrans : ∀ P i : ℕ → ℝ, WicksellEq β φ uc Pstar ν P i → ∀ t,
      gW β φ (Real.log (P t / Pstar t), ν t) - Real.log (P (t + 1) / Pstar (t + 1)) =
        wW uc Pstar t := by
    rintro P i ⟨hP, hF, hi⟩ t
    have h := hF t
    rw [hi t] at h
    exact (wicksell_step hpos hβ (hP t) (hP (t + 1)) (hPs t) (hPs (t + 1)) (huc t)
      (huc (t + 1))).mp h
  have hclass : ∀ P i : ℕ → ℝ, WicksellEq β φ uc Pstar ν P i →
      ∀ hb1 : (∀ t, |Real.log (P t / Pstar t)| ≤ ε / 2),
      mk (fun t => Real.log (P t / Pstar t)) ⟨ε / 2, hb1⟩ = implicitSol (gW β φ) hg hb s := by
    intro P i hE hb1
    exact huniq s hs _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hb1)
      (half_lt_self hε)) (fun t => htrans P i hE t)
  refine ⟨?_, ?_⟩
  · obtain ⟨hxn, hxs, -⟩ := hex s hs
    set x := implicitSol (gW β φ) hg hb s with hx
    have hp : ∀ t, Real.log (Pstar t * Real.exp (x t) / Pstar t) = x t := fun t => by
      rw [mul_div_cancel_left₀ _ (hPs t).ne', Real.log_exp]
    refine ⟨fun t => Pstar t * Real.exp (x t), fun t => φ (Real.exp (x t), ν t),
      ⟨fun t => mul_pos (hPs t) (Real.exp_pos _), fun t => ?_, fun t => ?_⟩, fun t => ?_⟩
    · have h := (wicksell_step (ν := ν t) hpos hβ (mul_pos (hPs t) (Real.exp_pos (x t)))
        (mul_pos (hPs (t + 1)) (Real.exp_pos (x (t + 1)))) (hPs t) (hPs (t + 1))
        (huc t) (huc (t + 1))).mpr (by rw [hp t, hp (t + 1)]; exact hxs t)
      rwa [mul_div_cancel_left₀ _ (hPs t).ne'] at h
    · simp only
      rw [mul_div_cancel_left₀ _ (hPs t).ne']
    · simp only
      rw [hp t]
      exact (abs_apply_le x t).trans hxn.le
  · intro P i P' i' hE hE' hb1 hb2
    have hlog : ∀ t, Real.log (P t / Pstar t) = Real.log (P' t / Pstar t) := fun t =>
      congrArg (fun y : Linf => y t) ((hclass P i hE hb1).trans (hclass P' i' hE' hb2).symm)
    have hPP : P = P' := funext fun t => by
      have h := Real.log_injOn_pos (Set.mem_Ioi.mpr (div_pos (hE.1 t) (hPs t)))
        (Set.mem_Ioi.mpr (div_pos (hE'.1 t) (hPs t))) (hlog t)
      exact (div_left_inj' (hPs t).ne').mp h
    exact ⟨hPP, funext fun t => by rw [hE.2.2 t, hE'.2.2 t, hPP]⟩

/-- Woodford (2003), Prop. 2.3, p. 82 ("(1.37) and (1.38) give a log-linear approximation …
accurate up to a residual of order `O(ξ²)`"), exact perfect-foresight version, task (iv) with the
`C²` hypothesis of erratum E18: there are `ε, δ > 0` and `C` such that, whenever all disturbances
are bounded by `ξ < δ`, every equilibrium with `|log(P_t/P_t^*)| ≤ ε` satisfies
`|log(P_t/P_t^*) − ∑_k (1 + φ_p)^{-(k+1)} (w_{t+k} − c ν_{t+k})| ≤ C ξ²`; with the book's
normalisation `c = 1` (fn. 15) the sum is exactly (1.37). -/
theorem wicksell_second_order {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    (hss : 1 + φ (1, 0) = β⁻¹) (hφp : 0 < elast β φ) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ uc Pstar ν : ℕ → ℝ, ∀ ξ : ℝ, (∀ t, 0 < uc t) →
      (∀ t, 0 < Pstar t) → ξ < δ → (∀ t, |ν t| ≤ ξ) → (∀ t, |wW uc Pstar t| ≤ ξ) →
      ∀ P i : ℕ → ℝ, WicksellEq β φ uc Pstar ν P i → (∀ t, |Real.log (P t / Pstar t)| ≤ ε) →
      ∀ t, |Real.log (P t / Pstar t) - ∑' k, (1 + elast β φ)⁻¹ ^ (k + 1) *
        (wW uc Pstar (t + k) - elastNu β φ * ν (t + k))| ≤ C * ξ ^ 2 := by
  have hφ1 : ContDiffOn ℝ 1 φ (Set.Ioi 0 ×ˢ Set.univ) := hφ.of_le (by norm_num)
  have hg : ContDiff ℝ 1 (gW β φ) := contDiff_gW hφ1 hpos
  have hg2 : ContDiff ℝ 2 (gW β φ) := contDiff_gW hφ hpos
  have hφd : DifferentiableAt ℝ φ (1, 0) :=
    (hφ1.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr one_pos, Set.mem_univ _⟩))
  have hl : DifferentiableAt ℝ (logRule β φ) 0 :=
    (contDiff_logRule hφ1 hpos).differentiable one_ne_zero 0
  obtain ⟨hsx, hsu⟩ := slopes_gW hβ hss hφd hl
  have hb : 1 < |slopeX (gW β φ)| := by
    rw [hsx, abs_of_pos (by linarith)]
    linarith
  obtain ⟨ε, hε, δ₁, hδ₁, -, -, huniq⟩ := local_determinacy hg (gW_zero hss) hb
  obtain ⟨C, δ₂, hδ₂, hC⟩ := second_order_accuracy_of_contDiff_two hg hg2 (gW_zero hss) hb
  refine ⟨ε / 2, half_pos hε, min δ₁ δ₂, lt_min hδ₁ hδ₂, max C 0,
    fun uc Pstar ν ξ huc hPs hξ hν hw P i hE hbd t => ?_⟩
  have hξ0 : 0 ≤ ξ := (abs_nonneg _).trans (hν 0)
  set s : Linf × Linf := (mk ν ⟨ξ, hν⟩, mk (wW uc Pstar) ⟨ξ, hw⟩) with hsdef
  have hsξ : ‖s‖ ≤ ξ := by
    rw [hsdef, Prod.norm_mk]
    exact max_le (norm_le_of_abs_le hξ0 hν) (norm_le_of_abs_le hξ0 hw)
  have hs1 : ‖s‖ < δ₁ := lt_of_le_of_lt hsξ (lt_of_lt_of_le hξ (min_le_left _ _))
  have hs2 : ‖s‖ < δ₂ := lt_of_le_of_lt hsξ (lt_of_lt_of_le hξ (min_le_right _ _))
  have hsol : ScalarSolves (gW β φ) s (mk (fun t => Real.log (P t / Pstar t)) ⟨ε / 2, hbd⟩) := by
    intro t
    obtain ⟨hP, hF, hi⟩ := hE
    have h := hF t
    rw [hi t] at h
    exact (wicksell_step hpos hβ (hP t) (hP (t + 1)) (hPs t) (hPs (t + 1)) (huc t)
      (huc (t + 1))).mp h
  have hX := huniq s hs1 _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hbd)
    (half_lt_self hε)) hsol
  have hbound := hC s hs2
  rw [← hX] at hbound
  have hcoord := abs_apply_le (mk (fun t => Real.log (P t / Pstar t)) ⟨ε / 2, hbd⟩ -
    linSolOp (gW β φ) s) t
  simp only [lp.coeFn_sub, Pi.sub_apply, mk_apply] at hcoord
  rw [linSolOp_apply hb, hsx, hsu] at hcoord
  refine hcoord.trans (hbound.trans ?_)
  calc C * ‖s‖ ^ 2 ≤ max C 0 * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * ξ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsξ 2) (le_max_right _ _)

/-- Woodford (2003), eqs. (1.21) (perfect foresight) and (2.4), pp. 72, 90: a **Taylor-rule
perfect-foresight equilibrium**: positive gross inflation `Π` and interest rates `i` with
`1 + i_t = u_c(t)/(β u_c(t+1)) · Π_{t+1}` and `i_t = φ(Π_t/Π_t^*; ν_t)` for all `t ≥ 0`. (The
price level then follows from the predetermined `P_{-1}`, fn. 25.) -/
def TaylorEq (β : ℝ) (φ : ℝ × ℝ → ℝ) (uc PiStar ν Infl i : ℕ → ℝ) : Prop :=
  (∀ t, 0 < Infl t) ∧ (∀ t, 1 + i t = uc t / (β * uc (t + 1)) * Infl (t + 1)) ∧
    ∀ t, i t = φ (Infl t / PiStar t, ν t)

/-- Woodford (2003), eq. (2.6), p. 91: the composite disturbance of the Taylor-rule model,
`w_t = r̂_t + π*_{t+1}` with `π*_t = log Π*_t`. -/
noncomputable def wT (uc PiStar : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.log (uc t / uc (t + 1)) + Real.log (PiStar (t + 1))

/-- Woodford (2003), eq. (2.6), p. 91, exact form: one date of the Taylor-rule equilibrium
conditions in levels and in logs (`y_t = log(Π_t/Π_t^*)`). -/
theorem taylor_step {β : ℝ} {φ : ℝ × ℝ → ℝ}
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν)) (hβ : 0 < β)
    {P0 P1 S0 S1 u0 u1 ν : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1) (hS0 : 0 < S0) (hS1 : 0 < S1)
    (hu0 : 0 < u0) (hu1 : 0 < u1) :
    1 + φ (P0 / S0, ν) = u0 / (β * u1) * P1 ↔
      logRule β φ (Real.log (P0 / S0), ν) - Real.log (P1 / S1) =
        Real.log (u0 / u1) + Real.log S1 := by
  rw [rule_iff (β := β) hpos (div_pos hP0 hS0) (by positivity)]
  have e1 : Real.log (u0 / (β * u1) * P1) =
      Real.log u0 - Real.log β - Real.log u1 + Real.log P1 := by
    rw [Real.log_mul (by positivity) hP1.ne', Real.log_div hu0.ne' (by positivity),
      Real.log_mul hβ.ne' hu1.ne']
    ring
  rw [e1, Real.log_div hP1.ne' hS1.ne', Real.log_div hu0.ne' hu1.ne']
  constructor <;> intro h <;> linarith

/-- Woodford (2003), Prop. 2.6, p. 91 (determinacy half), **exact perfect-foresight version**:
under a Taylor rule `φ` that is `C¹` on `(0, ∞) × ℝ`, keeps `1 + i > 0`, supports the
zero-inflation steady state and satisfies `|φ_π| > 1` (in particular the Taylor principle
`φ_π > 1`), there are `ε, δ > 0` such that for all exogenous paths with disturbances within `δ`
there is an equilibrium with `|log(Π_t/Π_t^*)| ≤ ε` for all `t`, and it is the only one. -/
theorem taylor_local_determinacy {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    (hss : 1 + φ (1, 0) = β⁻¹) (hφπ : 1 < |elast β φ|) :
    ∃ ε > 0, ∃ δ > 0, ∀ uc PiStar ν : ℕ → ℝ, (∀ t, 0 < uc t) → (∀ t, 0 < PiStar t) →
      (∀ t, |ν t| ≤ δ) → (∀ t, |wT uc PiStar t| ≤ δ) →
      (∃ Infl i : ℕ → ℝ, TaylorEq β φ uc PiStar ν Infl i ∧
        ∀ t, |Real.log (Infl t / PiStar t)| ≤ ε) ∧
      ∀ Infl i Infl' i' : ℕ → ℝ, TaylorEq β φ uc PiStar ν Infl i →
        TaylorEq β φ uc PiStar ν Infl' i' →
        (∀ t, |Real.log (Infl t / PiStar t)| ≤ ε) → (∀ t, |Real.log (Infl' t / PiStar t)| ≤ ε) →
        Infl = Infl' ∧ i = i' := by
  have hg : ContDiff ℝ 1 (logRule β φ) := contDiff_logRule hφ hpos
  have hφd : DifferentiableAt ℝ φ (1, 0) :=
    (hφ.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr one_pos, Set.mem_univ _⟩))
  obtain ⟨hsx, -⟩ := slopes_logRule hβ hss hφd
  have hb : 1 < |slopeX (logRule β φ)| := by rwa [hsx]
  obtain ⟨ε, hε, δ, hδ, -, hex, huniq⟩ := local_determinacy hg (logRule_zero hss) hb
  refine ⟨ε / 2, half_pos hε, δ / 2, half_pos hδ, fun uc PiStar ν huc hPs hν hw => ?_⟩
  set s : Linf × Linf := (mk ν ⟨δ / 2, hν⟩, mk (wT uc PiStar) ⟨δ / 2, hw⟩) with hsdef
  have hs : ‖s‖ < δ := by
    rw [hsdef, Prod.norm_mk]
    exact max_lt (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hν) (half_lt_self hδ))
      (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hw) (half_lt_self hδ))
  have htrans : ∀ Infl i : ℕ → ℝ, TaylorEq β φ uc PiStar ν Infl i → ∀ t,
      logRule β φ (Real.log (Infl t / PiStar t), ν t) - Real.log (Infl (t + 1) / PiStar (t + 1)) =
        wT uc PiStar t := by
    rintro Infl i ⟨hP, hF, hi⟩ t
    have h := hF t
    rw [hi t] at h
    exact (taylor_step hpos hβ (hP t) (hP (t + 1)) (hPs t) (hPs (t + 1)) (huc t)
      (huc (t + 1))).mp h
  have hclass : ∀ Infl i : ℕ → ℝ, TaylorEq β φ uc PiStar ν Infl i →
      ∀ hb1 : (∀ t, |Real.log (Infl t / PiStar t)| ≤ ε / 2),
      mk (fun t => Real.log (Infl t / PiStar t)) ⟨ε / 2, hb1⟩ =
        implicitSol (logRule β φ) hg hb s := by
    intro Infl i hE hb1
    exact huniq s hs _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hb1)
      (half_lt_self hε)) (fun t => htrans Infl i hE t)
  refine ⟨?_, ?_⟩
  · obtain ⟨hxn, hxs, -⟩ := hex s hs
    set x := implicitSol (logRule β φ) hg hb s with hx
    have hp : ∀ t, Real.log (PiStar t * Real.exp (x t) / PiStar t) = x t := fun t => by
      rw [mul_div_cancel_left₀ _ (hPs t).ne', Real.log_exp]
    refine ⟨fun t => PiStar t * Real.exp (x t), fun t => φ (Real.exp (x t), ν t),
      ⟨fun t => mul_pos (hPs t) (Real.exp_pos _), fun t => ?_, fun t => ?_⟩, fun t => ?_⟩
    · have h := (taylor_step (ν := ν t) hpos hβ (mul_pos (hPs t) (Real.exp_pos (x t)))
        (mul_pos (hPs (t + 1)) (Real.exp_pos (x (t + 1)))) (hPs t) (hPs (t + 1))
        (huc t) (huc (t + 1))).mpr (by rw [hp t, hp (t + 1)]; exact hxs t)
      rwa [mul_div_cancel_left₀ _ (hPs t).ne'] at h
    · simp only
      rw [mul_div_cancel_left₀ _ (hPs t).ne']
    · simp only
      rw [hp t]
      exact (abs_apply_le x t).trans hxn.le
  · intro Infl i Infl' i' hE hE' hb1 hb2
    have hlog : ∀ t, Real.log (Infl t / PiStar t) = Real.log (Infl' t / PiStar t) := fun t =>
      congrArg (fun y : Linf => y t) ((hclass Infl i hE hb1).trans (hclass Infl' i' hE' hb2).symm)
    have hPP : Infl = Infl' := funext fun t => by
      have h := Real.log_injOn_pos (Set.mem_Ioi.mpr (div_pos (hE.1 t) (hPs t)))
        (Set.mem_Ioi.mpr (div_pos (hE'.1 t) (hPs t))) (hlog t)
      exact (div_left_inj' (hPs t).ne').mp h
    exact ⟨hPP, funext fun t => by rw [hE.2.2 t, hE'.2.2 t, hPP]⟩

/-- Woodford (2003), Prop. 2.6, p. 91, eq. (2.7) ("a log-linear (first-order Taylor series)
approximation"), exact perfect-foresight version with the `C²` hypothesis of E18: every
equilibrium near the steady state satisfies
`|log(Π_t/Π_t^*) − ∑_k φ_π^{-(k+1)} (w_{t+k} − c ν_{t+k})| ≤ C ξ²` when all disturbances are
bounded by `ξ < δ`. -/
theorem taylor_second_order {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hφ : ContDiffOn ℝ 2 φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    (hss : 1 + φ (1, 0) = β⁻¹) (hφπ : 1 < |elast β φ|) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ uc PiStar ν : ℕ → ℝ, ∀ ξ : ℝ, (∀ t, 0 < uc t) →
      (∀ t, 0 < PiStar t) → ξ < δ → (∀ t, |ν t| ≤ ξ) → (∀ t, |wT uc PiStar t| ≤ ξ) →
      ∀ Infl i : ℕ → ℝ, TaylorEq β φ uc PiStar ν Infl i →
      (∀ t, |Real.log (Infl t / PiStar t)| ≤ ε) →
      ∀ t, |Real.log (Infl t / PiStar t) - ∑' k, (elast β φ)⁻¹ ^ (k + 1) *
        (wT uc PiStar (t + k) - elastNu β φ * ν (t + k))| ≤ C * ξ ^ 2 := by
  have hφ1 : ContDiffOn ℝ 1 φ (Set.Ioi 0 ×ˢ Set.univ) := hφ.of_le (by norm_num)
  have hg : ContDiff ℝ 1 (logRule β φ) := contDiff_logRule hφ1 hpos
  have hg2 : ContDiff ℝ 2 (logRule β φ) := contDiff_logRule hφ hpos
  have hφd : DifferentiableAt ℝ φ (1, 0) :=
    (hφ1.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr one_pos, Set.mem_univ _⟩))
  obtain ⟨hsx, hsu⟩ := slopes_logRule hβ hss hφd
  have hb : 1 < |slopeX (logRule β φ)| := by rwa [hsx]
  obtain ⟨ε, hε, δ₁, hδ₁, -, -, huniq⟩ := local_determinacy hg (logRule_zero hss) hb
  obtain ⟨C, δ₂, hδ₂, hC⟩ :=
    second_order_accuracy_of_contDiff_two hg hg2 (logRule_zero hss) hb
  refine ⟨ε / 2, half_pos hε, min δ₁ δ₂, lt_min hδ₁ hδ₂, max C 0,
    fun uc PiStar ν ξ huc hPs hξ hν hw Infl i hE hbd t => ?_⟩
  have hξ0 : 0 ≤ ξ := (abs_nonneg _).trans (hν 0)
  set s : Linf × Linf := (mk ν ⟨ξ, hν⟩, mk (wT uc PiStar) ⟨ξ, hw⟩) with hsdef
  have hsξ : ‖s‖ ≤ ξ := by
    rw [hsdef, Prod.norm_mk]
    exact max_le (norm_le_of_abs_le hξ0 hν) (norm_le_of_abs_le hξ0 hw)
  have hs1 : ‖s‖ < δ₁ := lt_of_le_of_lt hsξ (lt_of_lt_of_le hξ (min_le_left _ _))
  have hs2 : ‖s‖ < δ₂ := lt_of_le_of_lt hsξ (lt_of_lt_of_le hξ (min_le_right _ _))
  have hsol : ScalarSolves (logRule β φ) s
      (mk (fun t => Real.log (Infl t / PiStar t)) ⟨ε / 2, hbd⟩) := by
    intro t
    obtain ⟨hP, hF, hi⟩ := hE
    have h := hF t
    rw [hi t] at h
    exact (taylor_step hpos hβ (hP t) (hP (t + 1)) (hPs t) (hPs (t + 1)) (huc t)
      (huc (t + 1))).mp h
  have hX := huniq s hs1 _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hbd)
    (half_lt_self hε)) hsol
  have hbound := hC s hs2
  rw [← hX] at hbound
  have hcoord := abs_apply_le (mk (fun t => Real.log (Infl t / PiStar t)) ⟨ε / 2, hbd⟩ -
    linSolOp (logRule β φ) s) t
  simp only [lp.coeFn_sub, Pi.sub_apply, mk_apply] at hcoord
  rw [linSolOp_apply hb, hsx, hsu] at hcoord
  refine hcoord.trans (hbound.trans ?_)
  calc C * ‖s‖ ^ 2 ≤ max C 0 * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    _ ≤ max C 0 * ξ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsξ 2) (le_max_right _ _)

/-- Woodford (2003), Prop. 2.6, p. 91 (indeterminacy half: "If instead `0 ≤ φ_π < 1`, …
indeterminate"), **exact perfect-foresight version**: if `|φ_π| < 1`, then with constant
fundamentals (`u_c` constant, `Π* ≡ 1`, `ν ≡ 0`) and any `ε > 0`, every initial log inflation `c`
with `|c| ≤ r` starts an exact equilibrium staying within `ε` of the steady state; distinct `c`
give distinct equilibria, so there is a continuum of them in every neighbourhood. -/
theorem taylor_local_indeterminacy {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    (hss : 1 + φ (1, 0) = β⁻¹) (hφπ : |elast β φ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, |c| ≤ r → ∃ Infl i : ℕ → ℝ,
      TaylorEq β φ (fun _ => 1) (fun _ => 1) (fun _ => 0) Infl i ∧ Real.log (Infl 0) = c ∧
        ∀ t, |Real.log (Infl t)| ≤ ε := by
  have hg : ContDiff ℝ 1 (logRule β φ) := contDiff_logRule hφ hpos
  have hφd : DifferentiableAt ℝ φ (1, 0) :=
    (hφ.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr one_pos, Set.mem_univ _⟩))
  obtain ⟨hsx, -⟩ := slopes_logRule hβ hss hφd
  have hb : |slopeX (logRule β φ)| < 1 := by rwa [hsx]
  intro ε hε
  obtain ⟨r, hr, hc⟩ := local_indeterminacy hg.contDiffAt (logRule_zero hss) hb ε hε
  refine ⟨r, hr, fun c hcr => ?_⟩
  obtain ⟨x, hxs, hxn, hx0⟩ := hc c hcr
  have hp : ∀ t, Real.log (Real.exp (x t) / 1) = x t := fun t => by
    rw [div_one, Real.log_exp]
  refine ⟨fun t => Real.exp (x t), fun t => φ (Real.exp (x t), 0),
    ⟨fun t => Real.exp_pos _, fun t => ?_, fun t => ?_⟩, ?_, fun t => ?_⟩
  · have h := (taylor_step (ν := 0) hpos hβ (Real.exp_pos (x t)) (Real.exp_pos (x (t + 1)))
      one_pos one_pos one_pos one_pos).mpr (by
        rw [hp t, hp (t + 1)]
        have h' := hxs t
        simp only [Prod.fst_zero, Prod.snd_zero, lp.coeFn_zero, Pi.zero_apply] at h'
        simp [h'])
    rwa [div_one] at h
  · simp only [div_one]
  · simp only [Real.log_exp, hx0]
  · simp only [Real.log_exp]
    exact (abs_apply_le x t).trans hxn

/-- Woodford (2003), Prop. 2.3, p. 82 and App. A.3, p. 633, exact perfect-foresight version
(task (iii), `C¹` dependence): in sequence space the Wicksellian equilibrium `p = X(ν, w)` is a
`C¹` function of the disturbance sequences near zero, `X(0) = 0` (the steady state), and its
Fréchet derivative at zero is the log-linear solution operator (1.37). -/
theorem wicksell_smooth_dependence {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    (hss : 1 + φ (1, 0) = β⁻¹) (hφp : 0 < elast β φ) :
    ∃ δ > 0, ∃ X : Linf × Linf → Linf, X 0 = 0 ∧ HasFDerivAt X (linSolOp (gW β φ)) 0 ∧
      ∀ s : Linf × Linf, ‖s‖ < δ → ScalarSolves (gW β φ) s (X s) ∧ ContDiffAt ℝ 1 X s := by
  have hg : ContDiff ℝ 1 (gW β φ) := contDiff_gW hφ hpos
  have hφd : DifferentiableAt ℝ φ (1, 0) :=
    (hφ.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr one_pos, Set.mem_univ _⟩))
  have hl : DifferentiableAt ℝ (logRule β φ) 0 :=
    (contDiff_logRule hφ hpos).differentiable one_ne_zero 0
  obtain ⟨hsx, -⟩ := slopes_gW hβ hss hφd hl
  have hb : 1 < |slopeX (gW β φ)| := by
    rw [hsx, abs_of_pos (by linarith)]
    linarith
  obtain ⟨ε, hε, δ, hδ, -, hex, -⟩ := local_determinacy hg (gW_zero hss) hb
  exact ⟨δ, hδ, implicitSol (gW β φ) hg hb, implicitSol_zero hg (gW_zero hss) hb,
    hasFDerivAt_implicitSol hg (gW_zero hss) hb,
    fun s hs => ⟨(hex s hs).2.1, (hex s hs).2.2⟩⟩

/-- Woodford (2003), Prop. 2.6, p. 91 and App. A.3, p. 633, exact perfect-foresight version
(task (iii), `C¹` dependence): the Taylor-rule equilibrium `y = X(ν, w)` (`y_t = log(Π_t/Π_t^*)`)
is a `C¹` function of the disturbances near zero with derivative at zero the log-linear solution
operator (2.7). -/
theorem taylor_smooth_dependence {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    (hss : 1 + φ (1, 0) = β⁻¹) (hφπ : 1 < |elast β φ|) :
    ∃ δ > 0, ∃ X : Linf × Linf → Linf, X 0 = 0 ∧ HasFDerivAt X (linSolOp (logRule β φ)) 0 ∧
      ∀ s : Linf × Linf, ‖s‖ < δ → ScalarSolves (logRule β φ) s (X s) ∧ ContDiffAt ℝ 1 X s := by
  have hg : ContDiff ℝ 1 (logRule β φ) := contDiff_logRule hφ hpos
  have hφd : DifferentiableAt ℝ φ (1, 0) :=
    (hφ.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr one_pos, Set.mem_univ _⟩))
  obtain ⟨hsx, -⟩ := slopes_logRule hβ hss hφd
  have hb : 1 < |slopeX (logRule β φ)| := by rwa [hsx]
  obtain ⟨ε, hε, δ, hδ, -, hex, -⟩ := local_determinacy hg (logRule_zero hss) hb
  exact ⟨δ, hδ, implicitSol (logRule β φ) hg hb, implicitSol_zero hg (logRule_zero hss) hb,
    hasFDerivAt_implicitSol hg (logRule_zero hss) hb,
    fun s hs => ⟨(hex s hs).2.1, (hex s hs).2.2⟩⟩

/-! ### The price level under a Taylor rule (fn. 25) -/

/-- Woodford (2003), fn. 25, p. 91: the previous period's price level, with `P_{-1}` given
(`prevLevel P₋₁ P t = P_{t-1}`). -/
def prevLevel (Pm1 : ℝ) (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => Pm1
  | t + 1 => P t

/-- Woodford (2003), (1.21), (2.4) and fn. 25, pp. 72, 90–91: a Taylor-rule perfect-foresight
equilibrium stated in **price levels**: positive prices `P_t` (`t ≥ 0`), given the predetermined
`P_{-1}`, whose gross inflation `Π_t = P_t/P_{t-1}` together with `i` is a `TaylorEq`. -/
def TaylorPriceEq (β : ℝ) (φ : ℝ × ℝ → ℝ) (uc PiStar ν : ℕ → ℝ) (Pm1 : ℝ) (P i : ℕ → ℝ) :
    Prop :=
  (∀ t, 0 < P t) ∧ TaylorEq β φ uc PiStar ν (fun t => P t / prevLevel Pm1 P t) i

/-- Woodford (2003), App. A.3, p. 632: evaluation at date `t` is a bounded linear functional on
`ℓ∞`. -/
noncomputable def evalL (t : ℕ) : Linf →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun x => x t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun x => by
      rw [one_mul, Real.norm_eq_abs]
      exact abs_apply_le x t)

/-- Woodford (2003), fn. 25, p. 91: two price paths with the same `P_{-1}` and the same inflation
rates coincide. -/
theorem price_eq_of_infl_eq {Pm1 : ℝ} {P P' : ℕ → ℝ} (hP' : ∀ t, 0 < P' t) (hm : 0 < Pm1)
    (h : ∀ t, P t / prevLevel Pm1 P t = P' t / prevLevel Pm1 P' t) : P = P' := by
  funext t
  induction t with
  | zero =>
    have h0 := h 0
    simp only [prevLevel] at h0
    exact (div_left_inj' hm.ne').mp h0
  | succ n ih =>
    have h1 := h (n + 1)
    simp only [prevLevel] at h1
    rw [ih] at h1
    exact (div_left_inj' (hP' n).ne').mp h1

/-- Woodford (2003), Prop. 2.6 and fn. 25, p. 91, **exact perfect-foresight version: local
determinacy of the price level**. Under the hypotheses of `taylor_local_determinacy` there are
`ε, δ > 0` and a map `X` of the disturbance sequences, `C¹` near zero in the sense that each
`s ↦ ∑_{k ≤ t} X(s)_k` is `C¹`, such that for every `P_{-1} > 0` and exogenous paths with
disturbances within `δ/2`: there is an equilibrium price path whose inflation stays within the
`ε`-ball, with `log(P_t/P_{-1}) = ∑_{k ≤ t} (X(s)_k + log Π*_k)`, and any two equilibrium price
paths whose inflation stays in the `ε`-ball coincide (prices and interest rates). -/
theorem taylor_price_level {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hφ : ContDiffOn ℝ 1 φ (Set.Ioi 0 ×ˢ Set.univ))
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    (hss : 1 + φ (1, 0) = β⁻¹) (hφπ : 1 < |elast β φ|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : Linf × Linf → Linf,
      (∀ s : Linf × Linf, ‖s‖ < δ → ∀ t : ℕ,
        ContDiffAt ℝ 1 (fun s' => ∑ k ∈ Finset.range (t + 1), X s' k) s) ∧
      ∀ uc PiStar ν : ℕ → ℝ, ∀ Pm1 : ℝ, 0 < Pm1 → (∀ t, 0 < uc t) → (∀ t, 0 < PiStar t) →
      ∀ (hν : ∀ t, |ν t| ≤ δ / 2) (hw : ∀ t, |wT uc PiStar t| ≤ δ / 2),
      (∃ P i : ℕ → ℝ, TaylorPriceEq β φ uc PiStar ν Pm1 P i ∧
        (∀ t, |Real.log (P t / prevLevel Pm1 P t / PiStar t)| ≤ ε) ∧
        ∀ t, Real.log (P t / Pm1) = ∑ k ∈ Finset.range (t + 1),
          (X (mk ν ⟨δ / 2, hν⟩, mk (wT uc PiStar) ⟨δ / 2, hw⟩) k + Real.log (PiStar k))) ∧
      ∀ P i P' i' : ℕ → ℝ, TaylorPriceEq β φ uc PiStar ν Pm1 P i →
        TaylorPriceEq β φ uc PiStar ν Pm1 P' i' →
        (∀ t, |Real.log (P t / prevLevel Pm1 P t / PiStar t)| ≤ ε) →
        (∀ t, |Real.log (P' t / prevLevel Pm1 P' t / PiStar t)| ≤ ε) →
        P = P' ∧ i = i' := by
  have hg : ContDiff ℝ 1 (logRule β φ) := contDiff_logRule hφ hpos
  have hφd : DifferentiableAt ℝ φ (1, 0) :=
    (hφ.differentiableOn one_ne_zero).differentiableAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr one_pos, Set.mem_univ _⟩))
  obtain ⟨hsx, -⟩ := slopes_logRule hβ hss hφd
  have hb : 1 < |slopeX (logRule β φ)| := by rwa [hsx]
  obtain ⟨ε, hε, δ, hδ, -, hex, huniq⟩ := local_determinacy hg (logRule_zero hss) hb
  refine ⟨ε / 2, half_pos hε, δ, hδ, implicitSol (logRule β φ) hg hb, fun s hs t => ?_,
    fun uc PiStar ν Pm1 hm huc hPs hν hw => ?_⟩
  · have hX := (hex s hs).2.2
    exact ContDiffAt.sum (fun k _ => (evalL k).contDiff.contDiffAt.comp s hX)
  set s : Linf × Linf := (mk ν ⟨δ / 2, hν⟩, mk (wT uc PiStar) ⟨δ / 2, hw⟩) with hsdef
  have hs : ‖s‖ < δ := by
    rw [hsdef, Prod.norm_mk]
    exact max_lt (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hν) (half_lt_self hδ))
      (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hw) (half_lt_self hδ))
  have hprev : ∀ (Q : ℕ → ℝ), (∀ t, 0 < Q t) → ∀ t, 0 < prevLevel Pm1 Q t := by
    intro Q hQ t
    cases t with
    | zero => exact hm
    | succ n => exact hQ n
  have hclass : ∀ P i : ℕ → ℝ, TaylorPriceEq β φ uc PiStar ν Pm1 P i →
      ∀ hb1 : (∀ t, |Real.log (P t / prevLevel Pm1 P t / PiStar t)| ≤ ε / 2),
      mk (fun t => Real.log (P t / prevLevel Pm1 P t / PiStar t)) ⟨ε / 2, hb1⟩ =
        implicitSol (logRule β φ) hg hb s := by
    rintro P i ⟨hP, hI, hF, hi⟩ hb1
    refine huniq s hs _ (lt_of_le_of_lt (norm_le_of_abs_le (by positivity) hb1)
      (half_lt_self hε)) (fun t => ?_)
    have h := hF t
    rw [hi t] at h
    exact (taylor_step hpos hβ (hI t) (hI (t + 1)) (hPs t) (hPs (t + 1)) (huc t)
      (huc (t + 1))).mp h
  refine ⟨?_, ?_⟩
  · obtain ⟨hxn, hxs, -⟩ := hex s hs
    set x := implicitSol (logRule β φ) hg hb s with hx
    set Infl : ℕ → ℝ := fun t => PiStar t * Real.exp (x t) with hInfl
    have hIpos : ∀ t, 0 < Infl t := fun t => mul_pos (hPs t) (Real.exp_pos _)
    have hp : ∀ t, Real.log (Infl t / PiStar t) = x t := fun t => by
      rw [hInfl, mul_div_cancel_left₀ _ (hPs t).ne', Real.log_exp]
    set P : ℕ → ℝ := fun t => Pm1 * ∏ k ∈ Finset.range (t + 1), Infl k with hPdef
    have hPpos : ∀ t, 0 < P t := fun t =>
      mul_pos hm (Finset.prod_pos (fun k _ => hIpos k))
    have hratio : ∀ t, P t / prevLevel Pm1 P t = Infl t := by
      intro t
      cases t with
      | zero =>
        simp only [hPdef, prevLevel, zero_add, Finset.prod_range_one]
        field_simp
      | succ n =>
        simp only [hPdef, prevLevel]
        rw [Finset.prod_range_succ]
        have : 0 < ∏ k ∈ Finset.range (n + 1), Infl k :=
          Finset.prod_pos (fun k _ => hIpos k)
        field_simp
    have hfun : (fun t => P t / prevLevel Pm1 P t) = Infl := funext hratio
    refine ⟨P, fun t => φ (Infl t / PiStar t, ν t), ⟨hPpos, ?_⟩, fun t => ?_, fun t => ?_⟩
    · rw [hfun]
      refine ⟨hIpos, fun t => ?_, fun t => rfl⟩
      exact (taylor_step (ν := ν t) hpos hβ (hIpos t) (hIpos (t + 1)) (hPs t) (hPs (t + 1))
        (huc t) (huc (t + 1))).mpr (by rw [hp t, hp (t + 1)]; exact hxs t)
    · rw [hratio t, hp t]
      exact (abs_apply_le x t).trans hxn.le
    · rw [hPdef]
      simp only
      rw [mul_div_cancel_left₀ _ hm.ne', Real.log_prod (fun k _ => (hIpos k).ne')]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hInfl]
      simp only
      rw [Real.log_mul (hPs k).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
  · intro P i P' i' hE hE' hb1 hb2
    have hlog : ∀ t, Real.log (P t / prevLevel Pm1 P t / PiStar t) =
        Real.log (P' t / prevLevel Pm1 P' t / PiStar t) := fun t =>
      congrArg (fun y : Linf => y t) ((hclass P i hE hb1).trans (hclass P' i' hE' hb2).symm)
    have hinfl : ∀ t, P t / prevLevel Pm1 P t = P' t / prevLevel Pm1 P' t := fun t => by
      have h := Real.log_injOn_pos
        (Set.mem_Ioi.mpr (div_pos (div_pos (hE.1 t) (hprev P hE.1 t)) (hPs t)))
        (Set.mem_Ioi.mpr (div_pos (div_pos (hE'.1 t) (hprev P' hE'.1 t)) (hPs t))) (hlog t)
      exact (div_left_inj' (hPs t).ne').mp h
    have hPP : P = P' := price_eq_of_infl_eq hE'.1 hm hinfl
    refine ⟨hPP, funext fun t => ?_⟩
    rw [hE.2.2.2 t, hE'.2.2.2 t]
    change φ (P t / prevLevel Pm1 P t / PiStar t, ν t) =
      φ (P' t / prevLevel Pm1 P' t / PiStar t, ν t)
    rw [hinfl t]

/-! ### The transversality condition (1.24) near the steady state -/

/-- Woodford (2003), eq. (1.24), p. 72 (perfect foresight): the transversality condition on total
government liabilities, `lim_{T→∞} β^T u_c(Y_T; ξ_T) D_T / P_T = 0`. -/
def TVC (β : ℝ) (uc D P : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun T => β ^ T * uc T * D T / P T) Filter.atTop (𝓝 0)

/-- Woodford (2003), eq. (1.24), p. 72: geometric bounds `0 ≤ u_c ≤ U`, `|D_T| ≤ A γ^T` and
`P_T ≥ c κ^T` with `β γ < κ` imply the transversality condition. -/
theorem tvc_of_bounds {β U A c κ γ : ℝ} (hβ : 0 < β) (hc : 0 < c) (hκ : 0 < κ) (hγ : 0 ≤ γ)
    (hlt : β * γ < κ) {uc D P : ℕ → ℝ} (huc0 : ∀ T, 0 ≤ uc T) (hU : ∀ T, uc T ≤ U)
    (hD : ∀ T, |D T| ≤ A * γ ^ T) (hP : ∀ T, c * κ ^ T ≤ P T) : TVC β uc D P := by
  have hU0 : 0 ≤ U := (huc0 0).trans (hU 0)
  have hA0 : 0 ≤ A := by simpa using (abs_nonneg (D 0)).trans (hD 0)
  have hr0 : 0 ≤ β * γ / κ := by positivity
  have hr1 : β * γ / κ < 1 := by rwa [div_lt_one hκ]
  have hlim : Filter.Tendsto (fun T : ℕ => U * A / c * (β * γ / κ) ^ T) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (U * A / c)
  refine squeeze_zero_norm (fun T => ?_) hlim
  have hPT : 0 < P T := lt_of_lt_of_le (by positivity) (hP T)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_of_pos (pow_pos hβ T),
    abs_of_nonneg (huc0 T), abs_of_pos hPT, div_le_iff₀ hPT]
  calc β ^ T * uc T * |D T| ≤ β ^ T * U * (A * γ ^ T) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hU T) (pow_nonneg hβ.le T)) (hD T)
          (abs_nonneg _) (by positivity)
    _ = U * A / c * (β * γ / κ) ^ T * (c * κ ^ T) := by
        rw [div_pow, mul_pow]
        field_simp
    _ ≤ U * A / c * (β * γ / κ) ^ T * P T :=
        mul_le_mul_of_nonneg_left (hP T) (by positivity)

/-- Woodford (2003), p. 79: a fiscal rule with liabilities growing at most at the factor `γ`
(`|D_{t+1}| ≤ γ |D_t|`, the book's `D_{t+1}/D_t = γ_D` up to small fluctuations) gives
`|D_T| ≤ |D_0| γ^T`. -/
theorem abs_D_le {γ : ℝ} {D : ℕ → ℝ} (hγ : 0 ≤ γ) (hD : ∀ t, |D (t + 1)| ≤ γ * |D t|) :
    ∀ T, |D T| ≤ |D 0| * γ ^ T := by
  intro T
  induction T with
  | zero => simp
  | succ n ih =>
    calc |D (n + 1)| ≤ γ * |D n| := hD n
      _ ≤ γ * (|D 0| * γ ^ n) := mul_le_mul_of_nonneg_left ih hγ
      _ = |D 0| * γ ^ (n + 1) := by ring

/-- Woodford (2003), p. 79: a price-level target growing at least at the factor `θ`
(`P*_{t+1} ≥ θ P*_t`) satisfies `P*_T ≥ P*_0 θ^T`. -/
theorem target_ge {θ : ℝ} {S : ℕ → ℝ} (hθ : 0 ≤ θ) (hS : ∀ t, θ * S t ≤ S (t + 1)) :
    ∀ T, S 0 * θ ^ T ≤ S T := by
  intro T
  induction T with
  | zero => simp
  | succ n ih =>
    calc S 0 * θ ^ (n + 1) = θ * (S 0 * θ ^ n) := by ring
      _ ≤ θ * S n := mul_le_mul_of_nonneg_left ih hθ
      _ ≤ S (n + 1) := hS n

/-- Woodford (2003), p. 79 ("condition (1.24) is necessarily satisfied") for Prop. 2.3, exact
perfect-foresight version: if marginal utility is bounded above (`Y_t, ξ_t` in bounded
intervals), total liabilities grow at most at factor `γ`, the target grows at least at factor
`θ`, and **`β γ < θ`** (the book's `γ_D < π̄/β`, preserved under tight enough fluctuations), then
every Wicksellian equilibrium with `|log(P_t/P_t^*)| ≤ ε` satisfies (1.24). -/
theorem wicksell_tvc {β : ℝ} {φ : ℝ × ℝ → ℝ} {uc Pstar ν P i D : ℕ → ℝ} {ε U θ γ : ℝ}
    (hβ : 0 < β) (hE : WicksellEq β φ uc Pstar ν P i) (hbd : ∀ t, |Real.log (P t / Pstar t)| ≤ ε)
    (huc : ∀ t, 0 < uc t) (hU : ∀ t, uc t ≤ U) (hPs : ∀ t, 0 < Pstar t) (hθ : 0 < θ)
    (hS : ∀ t, θ * Pstar t ≤ Pstar (t + 1)) (hγ : 0 ≤ γ) (hD : ∀ t, |D (t + 1)| ≤ γ * |D t|)
    (hlt : β * γ < θ) : TVC β uc D P := by
  refine tvc_of_bounds (c := Pstar 0 * Real.exp (-ε)) (κ := θ) (A := |D 0|) (U := U) hβ
    (mul_pos (hPs 0) (Real.exp_pos _)) hθ hγ hlt (fun t => (huc t).le) hU (abs_D_le hγ hD)
    (fun T => ?_)
  have hr : Real.exp (-ε) ≤ P T / Pstar T := by
    rw [← Real.exp_log (div_pos (hE.1 T) (hPs T))]
    exact Real.exp_le_exp.mpr (neg_le_of_abs_le (hbd T))
  have hPT : P T = Pstar T * (P T / Pstar T) := by field_simp [(hPs T).ne']
  rw [hPT]
  calc Pstar 0 * Real.exp (-ε) * θ ^ T = Pstar 0 * θ ^ T * Real.exp (-ε) := by ring
    _ ≤ Pstar T * (P T / Pstar T) :=
      mul_le_mul (target_ge hθ.le hS T) hr (Real.exp_pos _).le (hPs T).le

/-- Woodford (2003), (1.24) for Prop. 2.6, exact perfect-foresight version: if marginal utility is
bounded, liabilities grow at most at factor `γ`, the inflation target satisfies `Π*_t ≥ θ`, and
`β γ < θ e^{-ε}`, then every Taylor-rule price path with `|log(Π_t/Π_t^*)| ≤ ε` satisfies (1.24).
(Unlike the Wicksellian case the price level is not anchored to a target, so the inflation band
`ε` enters the condition; `exists_eps_tvc` shows a small enough band always works when
`β γ < θ`.) -/
theorem taylor_tvc {β : ℝ} {φ : ℝ × ℝ → ℝ} {uc PiStar ν P i D : ℕ → ℝ} {Pm1 ε U θ γ : ℝ}
    (hβ : 0 < β) (hm : 0 < Pm1) (hE : TaylorPriceEq β φ uc PiStar ν Pm1 P i)
    (hbd : ∀ t, |Real.log (P t / prevLevel Pm1 P t / PiStar t)| ≤ ε)
    (huc : ∀ t, 0 < uc t) (hU : ∀ t, uc t ≤ U) (hθ : 0 < θ) (hS : ∀ t, θ ≤ PiStar t)
    (hγ : 0 ≤ γ) (hD : ∀ t, |D (t + 1)| ≤ γ * |D t|) (hlt : β * γ < θ * Real.exp (-ε)) :
    TVC β uc D P := by
  set κ := θ * Real.exp (-ε) with hκ
  have hκ0 : 0 < κ := mul_pos hθ (Real.exp_pos _)
  have hprev : ∀ t, 0 < prevLevel Pm1 P t := by
    intro t
    cases t with
    | zero => exact hm
    | succ n => exact hE.1 n
  have hinfl : ∀ t, κ * prevLevel Pm1 P t ≤ P t := by
    intro t
    have hPs : 0 < PiStar t := lt_of_lt_of_le hθ (hS t)
    have hr : Real.exp (-ε) ≤ P t / prevLevel Pm1 P t / PiStar t := by
      rw [← Real.exp_log (div_pos (div_pos (hE.1 t) (hprev t)) hPs)]
      exact Real.exp_le_exp.mpr (neg_le_of_abs_le (hbd t))
    have h1 : θ * Real.exp (-ε) ≤ P t / prevLevel Pm1 P t := by
      calc θ * Real.exp (-ε) ≤ PiStar t * (P t / prevLevel Pm1 P t / PiStar t) :=
            mul_le_mul (hS t) hr (Real.exp_pos _).le hPs.le
        _ = P t / prevLevel Pm1 P t := by field_simp
    rw [le_div_iff₀ (hprev t)] at h1
    exact h1
  have hgrow : ∀ T, Pm1 * κ * κ ^ T ≤ P T := by
    intro T
    induction T with
    | zero =>
      have h := hinfl 0
      simp only [prevLevel] at h
      simpa [mul_comm] using h
    | succ n ih =>
      have h := hinfl (n + 1)
      simp only [prevLevel] at h
      calc Pm1 * κ * κ ^ (n + 1) = κ * (Pm1 * κ * κ ^ n) := by ring
        _ ≤ κ * P n := mul_le_mul_of_nonneg_left ih hκ0.le
        _ ≤ P (n + 1) := h
  exact tvc_of_bounds (c := Pm1 * κ) (κ := κ) (A := |D 0|) (U := U) hβ (mul_pos hm hκ0) hκ0 hγ
    hlt (fun t => (huc t).le) hU (abs_D_le hγ hD) hgrow

/-- Woodford (2003), (1.24) for Prop. 2.6: if `β γ < θ`, a small enough inflation band `ε > 0`
keeps `β γ < θ e^{-ε}`, so `taylor_tvc` applies to every equilibrium in that band. -/
theorem exists_eps_tvc {β γ θ : ℝ} (hlt : β * γ < θ) :
    ∃ ε > 0, β * γ < θ * Real.exp (-ε) := by
  have hc : ContinuousAt (fun e : ℝ => θ * Real.exp (-e)) 0 := by fun_prop
  have hev : ∀ᶠ e in 𝓝 (0 : ℝ), β * γ < θ * Real.exp (-e) :=
    hc.eventually (lt_mem_nhds (by simpa using hlt))
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ / 2, half_pos hδ, hP ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
  exact half_lt_self hδ

/-- Woodford (2003), p. 79, **counterexample: (1.24) is not automatic without the fiscal
hypothesis `γ_D < π̄/β`.** With `β ∈ (0, 1)`, constant fundamentals and target, and liabilities
growing at exactly `β⁻¹`, the steady state `P_t ≡ 1` is a Wicksellian equilibrium (inside every
`ε`-ball) for any rule `φ` with `1 + φ(1; 0) = β⁻¹`, yet `β^T u_c D_T / P_T ≡ 1`. -/
theorem wicksell_tvc_fails {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹) :
    WicksellEq β φ (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => φ (1, 0)) ∧
      (∀ t, |Real.log ((fun _ : ℕ => (1 : ℝ)) t / (fun _ : ℕ => (1 : ℝ)) t)| ≤ 0) ∧
      ¬ TVC β (fun _ => 1) (fun T => β⁻¹ ^ T) (fun _ => 1) := by
  refine ⟨⟨fun _ => one_pos, fun t => ?_, fun t => by simp⟩, fun t => by simp, ?_⟩
  · simp [hss]
  · intro h
    have hconst : (fun T : ℕ => β ^ T * (1 : ℝ) * β⁻¹ ^ T / 1) = fun _ => 1 := by
      funext T
      rw [mul_one, div_one, ← mul_pow, mul_inv_cancel₀ hβ.ne', one_pow]
    unfold TVC at h
    rw [hconst] at h
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- Woodford (2003), (1.24) for Prop. 2.6, **counterexample** without the fiscal hypothesis:
with `P_{-1} = 1`, constant fundamentals, `Π* ≡ 1` and liabilities growing at `β⁻¹`, the zero
inflation steady state is a Taylor-rule equilibrium but violates (1.24). -/
theorem taylor_tvc_fails {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hss : 1 + φ (1, 0) = β⁻¹) :
    TaylorPriceEq β φ (fun _ => 1) (fun _ => 1) (fun _ => 0) 1 (fun _ => 1)
        (fun _ => φ (1, 0)) ∧
      ¬ TVC β (fun _ => 1) (fun T => β⁻¹ ^ T) (fun _ => 1) := by
  have hprev : ∀ t, prevLevel 1 (fun _ => (1 : ℝ)) t = 1 := by
    intro t
    cases t <;> rfl
  refine ⟨⟨fun _ => one_pos, fun t => by simp [hprev], fun t => ?_, fun t => by simp [hprev]⟩,
    (wicksell_tvc_fails hβ hss).2.2⟩
  simp [hprev, hss]

end Woodford.PriceLevelDetermination.LocalIFT
