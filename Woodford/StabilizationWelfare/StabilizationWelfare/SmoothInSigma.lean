/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth dependence of the equilibrium policy on the shock scale `σ`

Woodford (2003), *Interest and Prices*, Chapter 6, §1, pp. 383–392 (the expansion parameter
of the second-order approximations), Appendix E, pp. 692–698, and Appendix A.3, pp. 630–635
(log-linearisation justified by the implicit function theorem, citing Lang (1983)).

The second-order welfare results of Chapter 6 (and the perturbation method generally) expand the
equilibrium in the amplitude of the shocks and take for granted that the equilibrium depends
smoothly on it. This module proves that for a general class of stochastic rational-expectations
models, by the implicit function theorem on the Banach space `ℓ∞` of bounded processes on the
event tree (Mathlib's `ContDiffAt.implicitFunction`).

## Setting

* Information is a node `n : List J` of an event tree (the innovations drawn so far, newest
  first); innovations are i.i.d. over time and take FINITELY many values `ε_j` with
  probabilities `π_j`. `Bd ν V = ℓ∞(ν; V)`.
* `Model`: `E_t f(y_{t+1}, y_t, y_{t−1}, x_t, σ ε_{t+1}) = 0` at every node (`Solves`,
  `solves_iff`), with one lag of the decision vector and an exogenous state
  `x_{t+1} = Λ x_t + σ η ε_{t+1}`; `Std`: probabilities and `‖Λ‖ < 1`. All spaces are
  finite-dimensional. Parameters `p = (y_{−1}, x₀, σ)`; steady state `p̄ = (ȳ, 0, 0)` with
  `f(ȳ, ȳ, ȳ, 0, 0) = 0`. The task's class `E_t f(y_{t+1}, y_t, x_t, σε_{t+1}) = 0` is the case
  `C = ∂f/∂y_{t−1} = 0`.

## Main results

* The Nemytskii operator of a `Cᵏ` map on a finite-dimensional space is `Cᵏ` on `ℓ∞` for every
  finite `k` (`contDiff_nem`, with `hasFDerivAt_nem`); hence the equilibrium map `Phi` is `Cᵏ`
  (`contDiff_Phi`) with derivative the linearised operator `linOp`
  `L h = A E_t h_{t+1} + B h_t + C h_{t−1}` (`linOp_apply`, `fderiv_Phi_inr`).
* **Existence, local uniqueness and smoothness**: if `L` is invertible on `ℓ∞` (determinacy),
  there is a local equilibrium `ψ(p)` (`LocalSol`), `Cᵏ` at `p̄` jointly in `(y_{−1}, x₀, σ)`
  as a map into `ℓ∞`, i.e. uniformly over all dates and states (`exists_smooth_solution`); the
  policy function `g(y_{−1}, x, σ)` is `Cᵏ` on a neighbourhood of `p̄` (`exists_smooth_policy`),
  and the equilibrium is Markov, `y_t = g(y_{t−1}, x_t, σ)` at every node (`markov`). The
  smoothness is exactly `Cᵏ`: the sequence-space formulation has no composition operator, so no
  derivative is lost. With `f` smooth only near the steady state: `exists_smooth_solution_local`
  (smooth bump cut-off, `cutoffModel`, `localSol_cutoff_iff`).
* **First order**: `markov_deriv`, `ift_identity`; the matrix quadratic `A G_y² + B G_y + C = 0`
  (`first_order_lag`) and the state coefficient (`first_order_state`); **certainty equivalence**
  `g_σ(ȳ, 0, 0) = 0` when the innovations have mean zero and `A + B + C` is injective
  (`certainty_equivalence`, `certainty_equivalence_local`), the latter automatic without lags
  (`injective_of_noLag`).
* **Second order**: the equation for the risk correction,
  `(A G_y + A + B) g_σσ = −∑_j π_j [A g_xx(ηε_j, ηε_j) + D²f(z̄)(ζ_j, ζ_j)]`,
  `ζ_j = (G_x ηε_j, 0, 0, 0, ε_j)` (`second_order_sigma`, `second_order_sigma_local`), and
  `g(ȳ, 0, σ) = ȳ + (σ²/2) g_σσ + o(σ²)` (`policy_sigma_expansion`, `_local`).
* **Determinacy**: without lags, `B` invertible and `‖B⁻¹A‖ < 1` suffice
  (`isInvertible_linOp_noLag`, Neumann series); in the scalar case `L` is invertible IF AND ONLY
  IF `|a| < |b|` (`isInvertible_linOp_scalar_iff`; otherwise `(−b/a)^{t}` is a bounded
  sunspot direction).
* An illustration satisfying every hypothesis, `π_t = β E_t π_{t+1} + γ E_t π_{t+1}² + κ x_t`
  (`exModel`, `exModel_det`, `exModel_policy`).

## Restrictions, stated exactly

Finitely many innovation values, i.i.d. over time; a linear exogenous state with `‖Λ‖ < 1` in
the chosen norm; at most one lag of the decision vector; finite-dimensional spaces; `k` finite.
Uniqueness is local in the sup norm (among bounded solutions near `ȳ`). Certainty equivalence
with lags is proved under injectivity of `A + B + C`.
-/

namespace Woodford.StabilizationWelfare.SmoothInSigma

open scoped ENNReal Topology ContDiff
open Filter

universe u

/-! ## Bounded families and the Nemytskii operator -/

/-- Woodford (2003), App. E.2, p. 695 (uniform bounds over dates and states): the Banach space
of bounded families `(v_n)_{n ∈ ν}` with the sup norm. -/
abbrev Bd (ν : Type) (V : Type u) [NormedAddCommGroup V] : Type u := lp (fun _ : ν => V) ∞

variable {ν : Type}

/-- Woodford (2003), App. E.2, p. 695: each member of a bounded family is bounded by the sup
norm. -/
theorem norm_apply_le {V : Type u} [NormedAddCommGroup V] (w : Bd ν V) (n : ν) :
    ‖w n‖ ≤ ‖w‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero w n

/-- Woodford (2003), App. E.2, p. 695: a uniformly bounded family as an element of `Bd`. -/
noncomputable def mkBd {V : Type u} [NormedAddCommGroup V] (f : ν → V)
    (hf : ∃ C, ∀ n, ‖f n‖ ≤ C) : Bd ν V :=
  ⟨f, memℓp_infty (by
    obtain ⟨C, hC⟩ := hf
    exact ⟨C, by rintro _ ⟨n, rfl⟩; exact hC n⟩)⟩

/-- Woodford (2003), App. E.2, p. 695: members of `mkBd`. -/
@[simp] theorem mkBd_apply {V : Type u} [NormedAddCommGroup V] (f : ν → V)
    (hf : ∃ C, ∀ n, ‖f n‖ ≤ C) (n : ν) : mkBd f hf n = f n :=
  rfl

/-- Woodford (2003), App. E.2, p. 695: the sup norm is at most any uniform bound. -/
theorem norm_le_of_forall {V : Type u} [NormedAddCommGroup V] {w : Bd ν V} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ n, ‖w n‖ ≤ C) : ‖w‖ ≤ C :=
  lp.norm_le_of_forall_le hC h

variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- Woodford (2003), App. E.1, p. 692: a continuous function on a finite-dimensional space is
bounded on balls (compactness). -/
theorem exists_bound_ball {V : Type u} [NormedAddCommGroup V] {f : W → V} (hf : Continuous f)
    (R : ℝ) : ∃ C, ∀ p : W, ‖p‖ ≤ R → ‖f p‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : W) R).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun p hp => hC p (mem_closedBall_zero_iff.mpr hp)⟩

/-- Woodford (2003), App. E.2, p. 695 (**the Nemytskii operator**): `w ↦ (f(w_n))_n`, sending a
bounded family of arguments to the bounded family of values of a continuous `f`. -/
noncomputable def nem {V : Type u} [NormedAddCommGroup V] (f : W → V) (hf : Continuous f)
    (w : Bd ν W) : Bd ν V :=
  mkBd (fun n => f (w n)) (by
    obtain ⟨C, hC⟩ := exists_bound_ball hf ‖w‖
    exact ⟨C, fun n => hC _ (norm_apply_le w n)⟩)

/-- Woodford (2003), App. E.2, p. 695: members of the Nemytskii operator. -/
@[simp] theorem nem_apply {V : Type u} [NormedAddCommGroup V] (f : W → V) (hf : Continuous f)
    (w : Bd ν W) (n : ν) : nem f hf w n = f (w n) :=
  rfl

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- Woodford (2003), App. E.2, p. 695: the bound behind the multiplication operator. -/
theorem norm_mult_apply_le {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace ℝ W] (a : Bd ν (W →L[ℝ] V)) (h : Bd ν W) (n : ν) :
    ‖a n (h n)‖ ≤ ‖a‖ * ‖h‖ :=
  ((a n).le_opNorm (h n)).trans (mul_le_mul (norm_apply_le a n) (norm_apply_le h n)
    (norm_nonneg _) (norm_nonneg _))

omit [FiniteDimensional ℝ W] in
/-- Woodford (2003), App. E.2, p. 695 (**the multiplication operator**): a bounded family of
linear maps `a_n` acts on bounded families by `(a h)_n = a_n h_n`; bilinear and bounded. -/
noncomputable def mult (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Bd ν (W →L[ℝ] V) →L[ℝ] Bd ν W →L[ℝ] Bd ν V :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun a h => mkBd (fun n => a n (h n)) ⟨‖a‖ * ‖h‖, norm_mult_apply_le a h⟩)
      (fun a a' h => by ext n; simp)
      (fun c a h => by ext n; simp)
      (fun a h h' => by ext n; simp)
      (fun c a h => by ext n; simp))
    1 (fun a h => by
      rw [one_mul]
      exact norm_le_of_forall (by positivity) (norm_mult_apply_le a h))

omit [FiniteDimensional ℝ W] in
/-- Woodford (2003), App. E.2, p. 695: members of the multiplication operator. -/
@[simp] theorem mult_apply {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : Bd ν (W →L[ℝ] V)) (h : Bd ν W) (n : ν) : mult V a h n = a n (h n) :=
  rfl

/-- Woodford (2003), App. E.2, p. 695: the Nemytskii operator of a continuous function on a
finite-dimensional space is continuous on `Bd` (Heine–Cantor on balls). -/
theorem continuous_nem {V : Type u} [NormedAddCommGroup V] {f : W → V} (hf : Continuous f) :
    Continuous (nem (ν := ν) f hf) := by
  rw [Metric.continuous_iff]
  intro w ε hε
  have hK := isCompact_closedBall (0 : W) (‖w‖ + 1)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hf.continuousOn) (ε / 2) (half_pos hε)
  refine ⟨min δ 1, lt_min hδ one_pos, fun w' hw' => ?_⟩
  rw [dist_eq_norm] at hw' ⊢
  refine lt_of_le_of_lt (norm_le_of_forall (half_pos hε).le fun n => ?_) (half_lt_self hε)
  have hn : ‖w' n - w n‖ < min δ 1 :=
    lt_of_le_of_lt (by simpa using norm_apply_le (w' - w) n) hw'
  have hw : w n ∈ Metric.closedBall (0 : W) (‖w‖ + 1) := by
    rw [mem_closedBall_zero_iff]
    linarith [norm_apply_le w n]
  have hw2 : w' n ∈ Metric.closedBall (0 : W) (‖w‖ + 1) := by
    rw [mem_closedBall_zero_iff]
    have h1 : ‖w' n‖ ≤ ‖w n‖ + ‖w' n - w n‖ := by
      calc ‖w' n‖ = ‖w n + (w' n - w n)‖ := by rw [add_sub_cancel]
        _ ≤ ‖w n‖ + ‖w' n - w n‖ := norm_add_le _ _
    linarith [norm_apply_le w n, min_le_right δ 1]
  have := h _ hw2 _ hw (by rw [dist_eq_norm]; exact lt_of_lt_of_le hn (min_le_left _ _))
  rw [dist_eq_norm] at this
  simpa using this.le

/-- Woodford (2003), App. E.1, p. 692: the derivative of a `C¹` map on a finite-dimensional space
is uniformly continuous on bounded sets (Heine–Cantor). -/
theorem fderiv_close {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : W → V}
    (hf : ContDiff ℝ 1 f) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : W, ‖p‖ ≤ R → ‖q - p‖ < δ → ‖fderiv ℝ f q - fderiv ℝ f p‖ < ε := by
  have hK := isCompact_closedBall (0 : W) (R + 1)
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (hf.continuous_fderiv one_ne_zero).continuousOn) ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun p q hp hq => ?_⟩
  have hq1 : ‖q - p‖ < 1 := lt_of_lt_of_le hq (min_le_right _ _)
  have hpK : p ∈ Metric.closedBall (0 : W) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    linarith
  have hqK : q ∈ Metric.closedBall (0 : W) (R + 1) := by
    rw [mem_closedBall_zero_iff]
    have : ‖q‖ ≤ ‖p‖ + ‖q - p‖ := by
      calc ‖q‖ = ‖p + (q - p)‖ := by rw [add_sub_cancel]
        _ ≤ ‖p‖ + ‖q - p‖ := norm_add_le _ _
    linarith
  have := h q hqK p hpK (by rw [dist_eq_norm]; exact lt_of_lt_of_le hq (min_le_left _ _))
  rwa [dist_eq_norm] at this

/-- Woodford (2003), App. E.2, p. 695 (**the Nemytskii operator of a `C¹` map is differentiable
on `Bd`**), with derivative the multiplication operator by `(Df(w_n))_n`. -/
theorem hasFDerivAt_nem {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : W → V}
    (hf : ContDiff ℝ 1 f) (w : Bd ν W) :
    HasFDerivAt (nem f hf.continuous)
      (mult V (nem (fderiv ℝ f) (hf.continuous_fderiv one_ne_zero) w)) w := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hclose⟩ := fderiv_close hf ‖w‖ hc
  filter_upwards [Metric.ball_mem_nhds (0 : Bd ν W) hδ] with h hh
  rw [Metric.mem_ball, dist_zero_right] at hh
  refine norm_le_of_forall (by positivity) fun n => ?_
  have hmem : ∀ y : W, ‖y - w n‖ < δ → y ∈ Metric.ball (w n) δ := fun y hy => by
    rwa [Metric.mem_ball, dist_eq_norm]
  have key := (convex_ball (w n) δ).norm_image_sub_le_of_norm_fderiv_le' (f := f)
    (φ := fderiv ℝ f (w n)) (C := c) (fun z _ => (hf.differentiable one_ne_zero) z)
    (fun z hz => by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact (hclose (w n) z (norm_apply_le w n) hz).le)
    (hmem (w n) (by simpa using hδ)) (hmem (w n + h n) (by
      simpa using lt_of_le_of_lt (norm_apply_le h n) hh))
  have e : (nem f hf.continuous (w + h) - nem f hf.continuous w -
      mult V (nem (fderiv ℝ f) (hf.continuous_fderiv one_ne_zero) w) h) n =
      f (w n + h n) - f (w n) - fderiv ℝ f (w n) (w n + h n - w n) := by
    simp
  rw [e]
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
  simpa using norm_apply_le h n

/-- Woodford (2003), App. E.2, p. 695 (**the Nemytskii operator of a `Cᵏ` map is `Cᵏ` on `Bd`**):
for `f` of class `Cᵏ` on a finite-dimensional space, `w ↦ (f(w_n))_n` is `Cᵏ` on the space of
bounded families, for every finite `k` (induction: its derivative is the multiplication operator
by the Nemytskii operator of `Df`, which is `C^{k-1}`). -/
theorem contDiff_nem : ∀ (k : ℕ) {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : W → V) (hf : ContDiff ℝ k f), ContDiff ℝ k (nem (ν := ν) f hf.continuous)
  | 0, _, _, _, _, hf => contDiff_zero.2 (continuous_nem hf.continuous)
  | k + 1, V, _, _, f, hf => by
    have h1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hder : fderiv ℝ (nem (ν := ν) f hf.continuous) =
        fun w => mult V (nem (fderiv ℝ f) (h1.continuous_fderiv one_ne_zero) w) :=
      funext fun w => (hasFDerivAt_nem h1 w).fderiv
    have hk : ContDiff ℝ k (fderiv ℝ f) := hf.fderiv_right (by push_cast; exact le_rfl)
    have key : ContDiff ℝ ((k : ℕ∞ω) + 1) (nem (ν := ν) f hf.continuous) := by
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun w => (hasFDerivAt_nem h1 w).differentiableAt, fun h => by simp at h, ?_⟩
      rw [hder]
      exact (mult V).contDiff.comp (contDiff_nem k (fderiv ℝ f) hk)
    exact_mod_cast key


/-- Woodford (2003), App. E.2, p. 695: the constant family `(c)_n`. -/
noncomputable def constBd {V : Type u} [NormedAddCommGroup V] (c : V) : Bd ν V :=
  mkBd (fun _ => c) ⟨‖c‖, fun _ => le_rfl⟩

/-- Woodford (2003), App. E.2, p. 695: members of a constant family. -/
@[simp] theorem constBd_apply {V : Type u} [NormedAddCommGroup V] (c : V) (n : ν) :
    (constBd c : Bd ν V) n = c :=
  rfl

/-- Woodford (2003), App. E.2, p. 695: evaluation at the node `n` is a bounded linear map. -/
noncomputable def evalL (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ν) :
    Bd ν V →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := fun w => w n
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun w => (norm_apply_le w n).trans (le_of_eq (one_mul _).symm))

/-- Woodford (2003), App. E.2, p. 695: `evalL V n w = w n`. -/
@[simp] theorem evalL_apply (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] (n : ν)
    (w : Bd ν V) : evalL V n w = w n :=
  rfl

/-! ## Stochastic rational-expectations models on an event tree

Time-`t` information is a node `n : List J` of the event tree, the list of the `t` innovations
drawn so far (newest first); its successors are `j :: n`, reached with probability `π_j`
(innovations i.i.d. over time, taking the FINITELY many values `ε_j`, `j ∈ J`). The model is
`E_t f(y_{t+1}, y_t, y_{t−1}, x_t, σ ε_{t+1}) = 0`, i.e. at every node
`∑_j π_j f(y_{j::n}, y_n, y_{n⁻}, x_n, σ ε_j) = 0`, with `y_{n⁻}` the value at the predecessor
node (the given `y_{−1}` at the root), and the exogenous state obeys
`x_{t+1} = Λ x_t + σ η ε_{t+1}`. The scale `σ` multiplies every innovation; `σ = 0` is the
deterministic economy. -/

variable (J : Type)
variable (Y Z X E : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- Woodford (2003), App. E.2, p. 695, in the general form `E_t f(y_{t+1}, y_t, x_t, σε_{t+1}) = 0`
of the perturbation literature (Schmitt-Grohé and Uribe, 2004), with one lag of the decision
vector allowed (predetermined variables): the primitives of a stochastic rational-expectations
model with finitely many innovation values. -/
structure Model where
  /-- The period equilibrium conditions `f(y_{t+1}, y_t, y_{t−1}, x_t, e_{t+1})`. -/
  f : Y × Y × Y × X × E → Z
  /-- The probabilities `π_j` of the innovation values. -/
  prob : J → ℝ
  /-- The innovation values `ε_j` (bounded: finitely many). -/
  shock : J → E
  /-- The autoregressive matrix `Λ` of the exogenous state. -/
  Λ : X →L[ℝ] X
  /-- The loading `η` of the innovation on the exogenous state. -/
  η : E →L[ℝ] X

variable {J Y Z X E}

/-- Woodford (2003), App. E.2, p. 695: the predecessor value of a family on the tree, `y_{n⁻}`,
equal to the given initial value `y_{−1}` at the root. -/
def lagAt {V : Type} (u : List J → V) (ym : V) : List J → V
  | [] => ym
  | _ :: n => u n

/-- Woodford (2003), App. E.2: `lagAt` at the root. -/
@[simp] theorem lagAt_nil {V : Type} (u : List J → V) (ym : V) : lagAt u ym [] = ym :=
  rfl

/-- Woodford (2003), App. E.2: `lagAt` at a successor node. -/
@[simp] theorem lagAt_cons {V : Type} (u : List J → V) (ym : V) (j : J) (n : List J) :
    lagAt u ym (j :: n) = u n :=
  rfl

/-- Woodford (2003), App. E.2: `lagAt` is additive. -/
theorem lagAt_add {V : Type} [AddCommGroup V] (u u' : List J → V) (a a' : V) (n : List J) :
    lagAt (u + u') (a + a') n = lagAt u a n + lagAt u' a' n := by
  cases n <;> rfl

/-- Woodford (2003), App. E.2: `lagAt` is homogeneous. -/
theorem lagAt_smul {V : Type} [AddCommGroup V] [Module ℝ V] (c : ℝ) (u : List J → V) (a : V)
    (n : List J) : lagAt (c • u) (c • a) n = c • lagAt u a n := by
  cases n <;> rfl

/-- Woodford (2003), App. E.2: the norm of a predecessor value. -/
theorem norm_lagAt_le {V : Type} [NormedAddCommGroup V] (u : Bd (List J) V) (a : V)
    (n : List J) : ‖lagAt u a n‖ ≤ max ‖a‖ ‖u‖ := by
  cases n with
  | nil => exact le_max_left _ _
  | cons j m => exact (norm_apply_le u m).trans (le_max_right _ _)

/-- Woodford (2003), App. E.2: the parameters of the deterministic steady state,
`p̄ = (ȳ, 0, 0)` (initial lag `ȳ`, initial state `0`, scale `σ = 0`). -/
def pbar (ybar : Y) : Y × X × ℝ := (ybar, 0, 0)

/-- Woodford (2003), App. E.2: the steady-state argument of `F`, `w̄ = ((ȳ)_j, ȳ, ȳ, 0, 0)`. -/
def wbar (ybar : Y) : (J → Y) × Y × Y × X × ℝ := (fun _ => ybar, ybar, ybar, 0, 0)

/-- Woodford (2003), App. E.2: the steady-state argument of `f`, `z̄ = (ȳ, ȳ, ȳ, 0, 0)`. -/
def zbar (ybar : Y) : Y × Y × Y × X × E := (ybar, ybar, ybar, 0, 0)

namespace Model

variable (M : Model J Y Z X E)

/-- Woodford (2003), App. E.2, p. 695: the exogenous state at node `n`,
`x_{j::n} = Λ x_n + σ η ε_j`, from the initial state `x₀`. -/
def stateAt (x₀ : X) (σ : ℝ) : List J → X
  | [] => x₀
  | j :: n => M.Λ (stateAt x₀ σ n) + σ • M.η (M.shock j)

/-- Woodford (2003), App. E.2: the state at the root. -/
@[simp] theorem stateAt_nil (x₀ : X) (σ : ℝ) : M.stateAt x₀ σ [] = x₀ :=
  rfl

/-- Woodford (2003), App. E.2: the law of motion of the state. -/
@[simp] theorem stateAt_cons (x₀ : X) (σ : ℝ) (j : J) (n : List J) :
    M.stateAt x₀ σ (j :: n) = M.Λ (M.stateAt x₀ σ n) + σ • M.η (M.shock j) :=
  rfl

/-- Woodford (2003), App. E.2: the state is additive in `(x₀, σ)`. -/
theorem stateAt_add (x x' : X) (σ σ' : ℝ) (n : List J) :
    M.stateAt (x + x') (σ + σ') n = M.stateAt x σ n + M.stateAt x' σ' n := by
  induction n with
  | nil => rfl
  | cons j n ih =>
    simp only [stateAt_cons, ih, map_add, add_smul]
    abel

/-- Woodford (2003), App. E.2: the state is homogeneous in `(x₀, σ)`. -/
theorem stateAt_smul (c : ℝ) (x : X) (σ : ℝ) (n : List J) :
    M.stateAt (c • x) (c * σ) n = c • M.stateAt x σ n := by
  induction n with
  | nil => rfl
  | cons j n ih => simp only [stateAt_cons, ih, map_smul, smul_add, mul_smul]

/-- Woodford (2003), App. E.2: the deterministic steady state `x = 0` with `σ = 0` stays put. -/
@[simp] theorem stateAt_zero (n : List J) : M.stateAt 0 0 n = 0 := by
  induction n with
  | nil => rfl
  | cons j n ih => simp [ih]

/-- Woodford (2003), App. E.2 (**the state is Markov**): the state after the history `m ++ n`
is the state after `m` started from the state at `n`. -/
theorem stateAt_append (x : X) (σ : ℝ) (m n : List J) :
    M.stateAt x σ (m ++ n) = M.stateAt (M.stateAt x σ n) σ m := by
  induction m with
  | nil => rfl
  | cons j m ih => simp only [List.cons_append, stateAt_cons, ih]

variable [Fintype J]

/-- Woodford (2003), App. E.2, p. 695: `K = ∑_j ‖η ε_j‖`, a bound on the state innovations. -/
noncomputable def shockBound : ℝ := ∑ j, ‖M.η (M.shock j)‖

/-- Woodford (2003), App. E.2: `K ≥ 0`. -/
theorem shockBound_nonneg : 0 ≤ M.shockBound :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Woodford (2003), App. E.2: each innovation is bounded by `K`. -/
theorem norm_shock_le (j : J) : ‖M.η (M.shock j)‖ ≤ M.shockBound :=
  Finset.single_le_sum (f := fun j => ‖M.η (M.shock j)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)

/-- Woodford (2003), §2.1, pp. 392–394, and App. E.2 (**the standing assumptions**): the
innovation probabilities are a probability vector and the exogenous state is stable,
`‖Λ‖ < 1`. -/
structure Std where
  /-- `π_j ≥ 0`. -/
  prob_nonneg : ∀ j, 0 ≤ M.prob j
  /-- `∑_j π_j = 1`. -/
  prob_sum : ∑ j, M.prob j = 1
  /-- `‖Λ‖ < 1`: the exogenous state is stable. -/
  norm_Λ_lt : ‖M.Λ‖ < 1

variable {M}

/-- Woodford (2003), App. E.2, p. 695 (**the exogenous state is bounded uniformly over the
tree**): `‖x_n‖ ≤ ‖x₀‖ + |σ| K/(1 − ‖Λ‖)`. -/
theorem norm_stateAt_le (hM : M.Std) (x : X) (σ : ℝ) (n : List J) :
    ‖M.stateAt x σ n‖ ≤ ‖x‖ + |σ| * M.shockBound / (1 - ‖M.Λ‖) := by
  have h1 : 0 < 1 - ‖M.Λ‖ := by linarith [hM.norm_Λ_lt]
  have ha : 0 ≤ |σ| * M.shockBound := mul_nonneg (abs_nonneg σ) M.shockBound_nonneg
  have hid : |σ| * M.shockBound / (1 - ‖M.Λ‖) =
      ‖M.Λ‖ * (|σ| * M.shockBound / (1 - ‖M.Λ‖)) + |σ| * M.shockBound := by
    field_simp
    ring
  induction n with
  | nil =>
    simp only [stateAt_nil]
    have : 0 ≤ |σ| * M.shockBound / (1 - ‖M.Λ‖) := div_nonneg ha h1.le
    linarith
  | cons j n ih =>
    rw [stateAt_cons]
    have hΛ0 : 0 ≤ ‖M.Λ‖ := norm_nonneg _
    have hs : ‖σ • M.η (M.shock j)‖ ≤ |σ| * M.shockBound := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (M.norm_shock_le j) (abs_nonneg σ)
    have hl : ‖M.Λ (M.stateAt x σ n)‖ ≤
        ‖M.Λ‖ * (‖x‖ + |σ| * M.shockBound / (1 - ‖M.Λ‖)) :=
      (M.Λ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ih hΛ0)
    have hx : ‖M.Λ‖ * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) hM.norm_Λ_lt.le
    calc ‖M.Λ (M.stateAt x σ n) + σ • M.η (M.shock j)‖
        ≤ ‖M.Λ (M.stateAt x σ n)‖ + ‖σ • M.η (M.shock j)‖ := norm_add_le _ _
      _ ≤ ‖x‖ + |σ| * M.shockBound / (1 - ‖M.Λ‖) := by nlinarith

variable (M)

/-- Woodford (2003), App. E.2: the constant `C = 1 + K/(1 − ‖Λ‖)` bounding the arguments of
the equilibrium conditions. -/
noncomputable def pointConst : ℝ := 1 + M.shockBound / (1 - ‖M.Λ‖)

variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [Fintype J] in
/-- Woodford (2003), App. E.2, p. 695: the argument of the period-`t` equilibrium condition at
node `n`: the successor values `(y_{j::n})_j`, `y_n`, the predecessor value, the state `x_n`
and the scale `σ`; the parameters are `p = (y_{−1}, x₀, σ)`. -/
def point (u : List J → Y) (p : Y × X × ℝ) (n : List J) : (J → Y) × Y × Y × X × ℝ :=
  (fun j => u (j :: n), u n, lagAt u p.1 n, M.stateAt p.2.1 p.2.2 n, p.2.2)

omit [Fintype J] [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2: the argument is additive in `(u, p)`. -/
theorem point_add (u u' : List J → Y) (p p' : Y × X × ℝ) (n : List J) :
    M.point (u + u') (p + p') n = M.point u p n + M.point u' p' n := by
  simp only [point, Prod.fst_add, Prod.snd_add, lagAt_add, stateAt_add, Pi.add_apply]
  rfl

omit [Fintype J] in
/-- Woodford (2003), App. E.2: the argument is homogeneous in `(u, p)`. -/
theorem point_smul (c : ℝ) (u : List J → Y) (p : Y × X × ℝ) (n : List J) :
    M.point (c • u) (c • p) n = c • M.point u p n := by
  simp only [point, Prod.smul_fst, Prod.smul_snd, lagAt_smul, smul_eq_mul, stateAt_smul,
    Pi.smul_apply]
  rfl

variable {M}

omit [NormedSpace ℝ Y] in
/-- Woodford (2003), App. E.2, p. 695: the arguments of the equilibrium conditions are bounded
uniformly over the tree, `‖point‖ ≤ C ‖(p, u)‖`. -/
theorem norm_point_le (hM : M.Std) (q : (Y × X × ℝ) × Bd (List J) Y) (n : List J) :
    ‖M.point q.2 q.1 n‖ ≤ M.pointConst * ‖q‖ := by
  have h1 : 0 < 1 - ‖M.Λ‖ := by linarith [hM.norm_Λ_lt]
  have hK : 0 ≤ M.shockBound / (1 - ‖M.Λ‖) := div_nonneg M.shockBound_nonneg h1.le
  have hq : 0 ≤ ‖q‖ := norm_nonneg _
  have hu : ‖q.2‖ ≤ ‖q‖ := norm_snd_le q
  have hp : ‖q.1‖ ≤ ‖q‖ := norm_fst_le q
  have hym : ‖q.1.1‖ ≤ ‖q‖ := (norm_fst_le q.1).trans hp
  have hx : ‖q.1.2.1‖ ≤ ‖q‖ := ((norm_fst_le q.1.2).trans (norm_snd_le q.1)).trans hp
  have hσ : ‖q.1.2.2‖ ≤ ‖q‖ := ((norm_snd_le q.1.2).trans (norm_snd_le q.1)).trans hp
  have hC : ‖q‖ ≤ M.pointConst * ‖q‖ := by
    unfold pointConst
    nlinarith
  have hs : ‖M.stateAt q.1.2.1 q.1.2.2 n‖ ≤ M.pointConst * ‖q‖ := by
    refine (norm_stateAt_le hM _ _ n).trans ?_
    rw [Real.norm_eq_abs] at hσ
    have : |q.1.2.2| * M.shockBound / (1 - ‖M.Λ‖) ≤ ‖q‖ * (M.shockBound / (1 - ‖M.Λ‖)) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hσ hK
    unfold pointConst
    nlinarith
  have hc : ‖(fun j => q.2 (j :: n))‖ ≤ M.pointConst * ‖q‖ :=
    (pi_norm_le_iff_of_nonneg (hq.trans hC)).2 fun j => ((norm_apply_le q.2 _).trans hu).trans hC
  have hl : ‖lagAt q.2 q.1.1 n‖ ≤ M.pointConst * ‖q‖ :=
    ((norm_lagAt_le q.2 q.1.1 n).trans (max_le hym hu)).trans hC
  simp only [point, norm_prod_le_iff]
  exact ⟨hc, ((norm_apply_le q.2 n).trans hu).trans hC, hl, hs, hσ.trans hC⟩

/-- Woodford (2003), App. E.2, p. 695: the arguments of the equilibrium conditions as a bounded
linear map `(p, u) ↦ (point u p n)_n` into bounded families. -/
noncomputable def pointL (hM : M.Std) :
    (Y × X × ℝ) × Bd (List J) Y →L[ℝ] Bd (List J) ((J → Y) × Y × Y × X × ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun q => mkBd (M.point q.2 q.1) ⟨M.pointConst * ‖q‖, norm_point_le hM q⟩
      map_add' := fun q q' => by
        refine lp.ext (funext fun n => ?_)
        rw [lp.coeFn_add, Pi.add_apply, mkBd_apply, mkBd_apply, mkBd_apply, Prod.snd_add,
          Prod.fst_add, lp.coeFn_add, M.point_add]
      map_smul' := fun c q => by
        refine lp.ext (funext fun n => ?_)
        rw [lp.coeFn_smul, Pi.smul_apply, mkBd_apply, mkBd_apply, Prod.smul_snd, Prod.smul_fst,
          lp.coeFn_smul, M.point_smul, RingHom.id_apply] }
    M.pointConst (fun q => by
      have h1 : 0 < 1 - ‖M.Λ‖ := by linarith [hM.norm_Λ_lt]
      have hC : 0 ≤ M.pointConst :=
        add_nonneg zero_le_one (div_nonneg M.shockBound_nonneg h1.le)
      exact norm_le_of_forall (mul_nonneg hC (norm_nonneg q)) (norm_point_le hM q))

/-- Woodford (2003), App. E.2: members of `pointL`. -/
@[simp] theorem pointL_apply (hM : M.Std) (q : (Y × X × ℝ) × Bd (List J) Y) (n : List J) :
    M.pointL hM q n = M.point q.2 q.1 n :=
  rfl

variable (M) [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]

/-- Woodford (2003), App. E.2: the linear map `w ↦ (y_{j::n}, y_n, y_{n⁻}, x_n, σ ε_j)` picking
the arguments of `f` in the branch `j`. -/
noncomputable def ell (j : J) :
    ((J → Y) × Y × Y × X × ℝ) →L[ℝ] (Y × Y × Y × X × E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (w.1 j, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2 • M.shock j)
      map_add' := fun w w' => by
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Prod.mk_add_mk]
      map_smul' := fun c w => by
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply, Prod.smul_mk] }

/-- Woodford (2003), App. E.2: members of `ell`. -/
@[simp] theorem ell_apply (j : J)
    (w : (J → Y) × Y × Y × X × ℝ) :
    M.ell j w = (w.1 j, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2 • M.shock j) :=
  rfl

variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Woodford (2003), App. E.2, p. 695 (**the conditional expectation of the period condition**):
`F(w) = ∑_j π_j f(y_{j::n}, y_n, y_{n⁻}, x_n, σ ε_j)`, i.e. `E_t f(·)` at a node. -/
noncomputable def bigF (w : (J → Y) × Y × Y × X × ℝ) : Z :=
  ∑ j, M.prob j • M.f (M.ell j w)

/-- Woodford (2003), App. E.2, p. 695 (**the equilibrium conditions**): `u` solves the model
with parameters `p = (y_{−1}, x₀, σ)` iff at every node
`∑_j π_j f(y_{j::n}, y_n, y_{n⁻}, x_n, σ ε_j) = 0`. -/
def Solves (u : List J → Y) (p : Y × X × ℝ) : Prop :=
  ∀ n, M.bigF (M.point u p n) = 0

/-- Woodford (2003), App. E.2, p. 695: `Solves` written out as `E_t f(...) = 0` at each node. -/
theorem solves_iff (u : List J → Y) (p : Y × X × ℝ) : M.Solves u p ↔
    ∀ n, ∑ j, M.prob j • M.f (u (j :: n), u n, lagAt u p.1 n, M.stateAt p.2.1 p.2.2 n,
      p.2.2 • M.shock j) = 0 :=
  Iff.rfl


/-- Woodford (2003), App. E.2: `F` is continuous when `f` is. -/
theorem continuous_bigF (hf : Continuous M.f) : Continuous M.bigF :=
  continuous_finsetSum _ fun j _ => (hf.comp (M.ell j).continuous).const_smul _

/-- Woodford (2003), App. E.2: `F` is `Cᵏ` when `f` is. -/
theorem contDiff_bigF {k : ℕ∞ω} (hf : ContDiff ℝ k M.f) : ContDiff ℝ k M.bigF :=
  ContDiff.sum fun j _ => (hf.comp (M.ell j).contDiff).const_smul _

/-- Woodford (2003), App. E.2: the derivative of `F`,
`DF(w) v = ∑_j π_j Df(ℓ_j w)(ℓ_j v)`. -/
theorem hasFDerivAt_bigF (hf : ContDiff ℝ 1 M.f) (w : (J → Y) × Y × Y × X × ℝ) :
    HasFDerivAt M.bigF (∑ j, M.prob j • (fderiv ℝ M.f (M.ell j w)).comp (M.ell j)) w := by
  have h : ∀ j ∈ (Finset.univ : Finset J), HasFDerivAt (fun w => M.prob j • M.f (M.ell j w))
      (M.prob j • (fderiv ℝ M.f (M.ell j w)).comp (M.ell j)) w := fun j _ =>
    (((hf.differentiable one_ne_zero) (M.ell j w)).hasFDerivAt.comp w
      (M.ell j).hasFDerivAt).const_smul (M.prob j)
  exact HasFDerivAt.fun_sum h

variable {M}

/-- Woodford (2003), App. E.2, p. 695 (**the equilibrium map**): `Φ(p, u) = (E_t f(·))_n`, the
family of residuals of the equilibrium conditions, a map from parameters `p = (y_{−1}, x₀, σ)`
and bounded candidate solutions `u` to bounded families of residuals. -/
noncomputable def Phi (hM : M.Std) (hc : Continuous M.f)
    (q : (Y × X × ℝ) × Bd (List J) Y) : Bd (List J) Z :=
  nem M.bigF (M.continuous_bigF hc) (M.pointL hM q)

/-- Woodford (2003), App. E.2: members of the equilibrium map. -/
@[simp] theorem Phi_apply (hM : M.Std) (hc : Continuous M.f) (q : (Y × X × ℝ) × Bd (List J) Y)
    (n : List J) : M.Phi hM hc q n = M.bigF (M.point q.2 q.1 n) :=
  rfl

/-- Woodford (2003), App. E.2: the zeros of the equilibrium map are exactly the bounded
solutions of the model. -/
theorem Phi_eq_zero_iff (hM : M.Std) (hc : Continuous M.f) (p : Y × X × ℝ)
    (u : Bd (List J) Y) : M.Phi hM hc (p, u) = 0 ↔ M.Solves u p :=
  ⟨fun h n => by simpa using congrArg (fun w : Bd (List J) Z => w n) h,
    fun h => lp.ext (funext fun n => h n)⟩

/-- Woodford (2003), App. E.2, p. 695 (**the equilibrium map is `Cᵏ`**): if `f` is `Cᵏ`, so is
`Φ` on `(Y × X × ℝ) × ℓ∞`, by `contDiff_nem` (`F` is `Cᵏ` on a finite-dimensional space) and
the boundedness of `pointL`. -/
theorem contDiff_Phi (hM : M.Std) {k : ℕ} (hf : ContDiff ℝ k M.f) :
    ContDiff ℝ k (M.Phi hM hf.continuous) :=
  (contDiff_nem k M.bigF (M.contDiff_bigF hf)).comp (M.pointL hM).contDiff

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: at the steady-state parameters and the constant candidate `ȳ`,
every node's argument is `w̄`. -/
theorem pointL_bar (hM : M.Std) (ybar : Y) :
    M.pointL hM (pbar ybar, constBd ybar) = constBd (wbar ybar) := by
  refine lp.ext (funext fun n => ?_)
  cases n <;> simp [point, pbar, wbar]

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: `ℓ_j w̄ = z̄`. -/
theorem ell_wbar (ybar : Y) (j : J) : M.ell j (wbar ybar) = zbar ybar := by
  simp only [ell_apply, wbar, zbar, zero_smul]

/-- Woodford (2003), App. E.2: the steady state solves the deterministic model, `Φ(p̄, ȳ) = 0`. -/
theorem Phi_bar (hM : M.Std) (hc : Continuous M.f) {ybar : Y} (hss : M.f (zbar ybar) = 0) :
    M.Phi hM hc (pbar ybar, constBd ybar) = 0 := by
  refine lp.ext (funext fun n => ?_)
  have h := congrArg (fun w : Bd (List J) ((J → Y) × Y × Y × X × ℝ) => w n) (pointL_bar hM ybar)
  simp only [constBd_apply] at h
  simp only [Phi, nem_apply, h, bigF, ell_wbar, hss, smul_zero, Finset.sum_const_zero,
    lp.coeFn_zero, Pi.zero_apply]

variable (M)

/-- Woodford (2003), App. E.2, eq. (E.2)-type linearisation: `A = ∂f/∂y_{t+1}` at the steady
state. -/
noncomputable def dA (ybar : Y) : Y →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp (ContinuousLinearMap.inl ℝ Y (Y × Y × X × E))

/-- Woodford (2003), App. E.2: `B = ∂f/∂y_t` at the steady state. -/
noncomputable def dB (ybar : Y) : Y →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp ((ContinuousLinearMap.inr ℝ Y (Y × Y × X × E)).comp
    (ContinuousLinearMap.inl ℝ Y (Y × X × E)))

/-- Woodford (2003), App. E.2: `C = ∂f/∂y_{t−1}` at the steady state. -/
noncomputable def dC (ybar : Y) : Y →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp ((ContinuousLinearMap.inr ℝ Y (Y × Y × X × E)).comp
    ((ContinuousLinearMap.inr ℝ Y (Y × X × E)).comp (ContinuousLinearMap.inl ℝ Y (X × E))))

/-- Woodford (2003), App. E.2: `f_x = ∂f/∂x_t` at the steady state. -/
noncomputable def dX (ybar : Y) : X →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp ((ContinuousLinearMap.inr ℝ Y (Y × Y × X × E)).comp
    ((ContinuousLinearMap.inr ℝ Y (Y × X × E)).comp ((ContinuousLinearMap.inr ℝ Y (X × E)).comp
      (ContinuousLinearMap.inl ℝ X E))))

/-- Woodford (2003), App. E.2: `f_e = ∂f/∂e_{t+1}` at the steady state. -/
noncomputable def dE (ybar : Y) : E →L[ℝ] Z :=
  (fderiv ℝ M.f (zbar ybar)).comp ((ContinuousLinearMap.inr ℝ Y (Y × Y × X × E)).comp
    ((ContinuousLinearMap.inr ℝ Y (Y × X × E)).comp ((ContinuousLinearMap.inr ℝ Y (X × E)).comp
      (ContinuousLinearMap.inr ℝ X E))))

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [Fintype J] in
/-- Woodford (2003), App. E.2: the steady-state derivative of `f` in coordinates,
`Df(z̄)(a, b, c, x, e) = A a + B b + C c + f_x x + f_e e`. -/
theorem fderiv_f_apply (ybar : Y) (a b c : Y) (x : X) (e : E) :
    fderiv ℝ M.f (zbar ybar) (a, b, c, x, e) =
      M.dA ybar a + M.dB ybar b + M.dC ybar c + M.dX ybar x + M.dE ybar e := by
  simp only [dA, dB, dC, dX, dE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

variable {M}

/-- Woodford (2003), App. E.2, p. 695 (**the linearised operator**): the derivative of the
equilibrium map in the candidate solution at the steady state, as a bounded operator on `ℓ∞`
(see `linOp_apply` for its coordinates). -/
noncomputable def linOp (hM : M.Std) (ybar : Y) : Bd (List J) Y →L[ℝ] Bd (List J) Z :=
  (mult Z (constBd (fderiv ℝ M.bigF (wbar ybar)))).comp
    ((M.pointL hM).comp (ContinuousLinearMap.inr ℝ (Y × X × ℝ) (Bd (List J) Y)))

/-- Woodford (2003), App. E.2: the steady-state derivative of `F`. -/
theorem fderiv_bigF_wbar (hf : ContDiff ℝ 1 M.f) (ybar : Y) :
    fderiv ℝ M.bigF (wbar ybar) = ∑ j, M.prob j • (fderiv ℝ M.f (zbar ybar)).comp (M.ell j) := by
  rw [(M.hasFDerivAt_bigF hf (wbar ybar)).fderiv]
  simp only [ell_wbar]

/-- Woodford (2003), App. E.2, p. 695 (**the linearised equilibrium conditions in
coordinates**): `DF(w̄)` applied to the argument of node `n` built from a perturbation `h` of
the solution and `v` of the parameters is
`∑_j π_j A h_{j::n} + B h_n + C h_{n⁻} + f_x x_n + σ f_e(∑_j π_j ε_j)`. -/
theorem DF_point (hM : M.Std) (hf : ContDiff ℝ 1 M.f) (ybar : Y) (h : List J → Y)
    (v : Y × X × ℝ) (n : List J) : fderiv ℝ M.bigF (wbar ybar) (M.point h v n) =
      ∑ j, M.prob j • M.dA ybar (h (j :: n)) + M.dB ybar (h n) + M.dC ybar (lagAt h v.1 n) +
        M.dX ybar (M.stateAt v.2.1 v.2.2 n) + v.2.2 • M.dE ybar (∑ j, M.prob j • M.shock j) := by
  rw [fderiv_bigF_wbar hf]
  simp only [sum_apply, smul_apply, ContinuousLinearMap.comp_apply, ell_apply, point,
    fderiv_f_apply, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hM.prob_sum, one_smul,
    map_sum, map_smul, Finset.smul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/-- Woodford (2003), App. E.2, p. 695 (**the linearised model in coordinates**):
`(L h)_n = ∑_j π_j A h_{j::n} + B h_n + C h_{n⁻}` (with `h_{n⁻} = 0` at the root), i.e. the
linearised equilibrium conditions `A E_t h_{t+1} + B h_t + C h_{t−1}`. -/
theorem linOp_apply (hM : M.Std) (hf : ContDiff ℝ 1 M.f) (ybar : Y) (h : Bd (List J) Y)
    (n : List J) : M.linOp hM ybar h n =
      ∑ j, M.prob j • M.dA ybar (h (j :: n)) + M.dB ybar (h n) + M.dC ybar (lagAt h 0 n) := by
  have e1 : M.linOp hM ybar h n = fderiv ℝ M.bigF (wbar ybar) (M.point h 0 n) := rfl
  rw [e1, DF_point hM hf]
  simp

/-- Woodford (2003), App. E.2: the derivative of the equilibrium map at the steady state,
`DΦ(p̄, ȳ)(v, h) = (DF(w̄)(point h v n))_n`. -/
theorem hasFDerivAt_Phi_bar (hM : M.Std) (hc : Continuous M.f) (hf : ContDiff ℝ 1 M.f)
    (ybar : Y) : HasFDerivAt (M.Phi hM hc)
      ((mult Z (constBd (fderiv ℝ M.bigF (wbar ybar)))).comp (M.pointL hM))
      (pbar ybar, constBd ybar) := by
  have hF : ContDiff ℝ 1 M.bigF := M.contDiff_bigF hf
  have hd := (hasFDerivAt_nem (ν := List J) hF (M.pointL hM (pbar ybar, constBd ybar))).comp
    (pbar ybar, constBd ybar) (M.pointL hM).hasFDerivAt
  have e : nem (fderiv ℝ M.bigF) (hF.continuous_fderiv one_ne_zero)
      (M.pointL hM (pbar ybar, constBd ybar)) = constBd (fderiv ℝ M.bigF (wbar ybar)) := by
    rw [pointL_bar hM ybar]
    rfl
  rw [e] at hd
  exact hd

/-- Woodford (2003), App. E.2: the derivative of the equilibrium map at the steady state,
restricted to the candidate solution, is the linearised operator. -/
theorem fderiv_Phi_inr (hM : M.Std) (hc : Continuous M.f) (hf : ContDiff ℝ 1 M.f) (ybar : Y) :
    (fderiv ℝ (M.Phi hM hc) (pbar ybar, constBd ybar)).comp
      (ContinuousLinearMap.inr ℝ (Y × X × ℝ) (Bd (List J) Y)) = M.linOp hM ybar := by
  rw [(hasFDerivAt_Phi_bar hM hc hf ybar).fderiv]
  rfl

variable (M)

variable (ybar : Y) (ψ : Y × X × ℝ → Bd (List J) Y) in
/-- Woodford (2003), App. E.2, p. 695 (**a local equilibrium policy**): `ψ` maps parameters
`p = (y_{−1}, x₀, σ)` near the steady state `p̄ = (ȳ, 0, 0)` to a bounded solution on the whole
event tree; it equals the steady state at `p̄`, is continuous there, solves the model near `p̄`,
and is the ONLY bounded solution near `ȳ` (sup norm) for parameters near `p̄`. -/
structure LocalSol where
  /-- `ψ(p̄) = ȳ`. -/
  base : ψ (pbar ybar) = constBd ybar
  /-- `ψ` is continuous at `p̄`. -/
  cont : ContinuousAt ψ (pbar ybar)
  /-- `ψ(p)` solves the model for `p` near `p̄`. -/
  solves : ∀ᶠ p in 𝓝 (pbar ybar), M.Solves (ψ p) p
  /-- Local uniqueness. -/
  unique : ∃ δ > 0, ∀ (p : Y × X × ℝ) (u : Bd (List J) Y), dist p (pbar ybar) < δ →
    dist u (constBd ybar) < δ → M.Solves u p → ψ p = u

variable {M}

/-- Woodford (2003), App. E.2, p. 695, and the perturbation method (**existence, local
uniqueness and `Cᵏ` dependence of the equilibrium on the shock scale, the initial state and the
initial lag**): let `f` be `Cᵏ` (`k ≥ 1`) with steady state `f(ȳ, ȳ, ȳ, 0, 0) = 0`, and let the
linearised operator `L h = A E_t h_{t+1} + B h_t + C h_{t−1}` be invertible on `ℓ∞`
(determinacy). Then there is a local equilibrium policy `ψ` on the event tree, and it is `Cᵏ`
at `p̄` jointly in `(y_{−1}, x₀, σ)` as a map into `ℓ∞` (uniformly over all dates and
states). This is the implicit function theorem on the Banach space `ℓ∞` (Mathlib's
`ContDiffAt.implicitFunction`). -/
theorem exists_smooth_solution [FiniteDimensional ℝ Z] (hM : M.Std) {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ k M.f) {ybar : Y} (hss : M.f (zbar ybar) = 0)
    (hdet : (M.linOp hM ybar).IsInvertible) :
    ∃ ψ : Y × X × ℝ → Bd (List J) Y, M.LocalSol ybar ψ ∧ ContDiffAt ℝ k ψ (pbar ybar) := by
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hf1 : ContDiff ℝ 1 M.f := hf.of_le (by exact_mod_cast hk)
  have cdf : ContDiffAt ℝ k (M.Phi hM hf.continuous) (pbar ybar, constBd ybar) :=
    (contDiff_Phi hM hf).contDiffAt
  have hinv : ((fderiv ℝ (M.Phi hM hf.continuous) (pbar ybar, constBd ybar)).comp
      (ContinuousLinearMap.inr ℝ (Y × X × ℝ) (Bd (List J) Y))).IsInvertible := by
    rw [fderiv_Phi_inr hM hf.continuous hf1]
    exact hdet
  have h0 := Phi_bar hM hf.continuous hss
  refine ⟨cdf.implicitFunction hk0 hinv, ⟨cdf.implicitFunction_apply_self hk0 hinv,
    (cdf.contDiffAt_implicitFunction hk0 hinv).continuousAt, ?_, ?_⟩,
    cdf.contDiffAt_implicitFunction hk0 hinv⟩
  · filter_upwards [cdf.eventually_apply_implicitFunction hk0 hinv] with p hp
    rw [h0] at hp
    exact (Phi_eq_zero_iff hM hf.continuous p _).1 hp
  · obtain ⟨δ, hδ, h⟩ :=
      Metric.eventually_nhds_iff.1 (cdf.eventually_apply_eq_iff_implicitFunction hk0 hinv)
    refine ⟨δ, hδ, fun p u hp hu hs => ?_⟩
    have hd : dist (p, u) (pbar ybar, constBd ybar) < δ := by
      rw [Prod.dist_eq]
      exact max_lt hp hu
    exact (h hd).1 (by rw [h0]; exact (Phi_eq_zero_iff hM hf.continuous p u).2 hs)


/-! ## The policy function and its Markov property -/

omit [Fintype J] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2, p. 695 (**the policy function**): `g(y_{−1}, x, σ)`, the decision
at the root when the economy starts from the lagged decision `y_{−1}` and the state `x`, with
shock scale `σ`. -/
def policy (ψ : Y × X × ℝ → Bd (List J) Y) (p : Y × X × ℝ) : Y := ψ p []

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: `C = 1 + K/(1 − ‖Λ‖) ≥ 1`. -/
theorem one_le_pointConst (hM : M.Std) : 1 ≤ M.pointConst := by
  have h1 : 0 < 1 - ‖M.Λ‖ := by linarith [hM.norm_Λ_lt]
  have := div_nonneg M.shockBound_nonneg h1.le
  unfold pointConst
  linarith

/-- Woodford (2003), App. E.2, p. 695 (**the equilibrium is Markov: `y_t = g(y_{t−1}, x_t, σ)`**):
near `p̄`, the local equilibrium at EVERY node `n` of the event tree is the policy function
evaluated at that node's predecessor value, state and scale. The proof shifts the solution to
the subtree below `n`, which solves the model with initial data `(y_{n⁻}, x_n, σ)`, and applies
local uniqueness. -/
theorem markov (hM : M.Std) {ybar : Y} {ψ : Y × X × ℝ → Bd (List J) Y}
    (hψ : M.LocalSol ybar ψ) : ∀ᶠ p in 𝓝 (pbar ybar), ∀ n,
      ψ p n = policy ψ (lagAt (ψ p) p.1 n, M.stateAt p.2.1 p.2.2 n, p.2.2) := by
  obtain ⟨δ, hδ, huniq⟩ := hψ.unique
  have hC := one_le_pointConst hM
  have hCpos : 0 < M.pointConst := by linarith
  have h1 : 0 < 1 - ‖M.Λ‖ := by linarith [hM.norm_Λ_lt]
  have hball : ∀ᶠ p in 𝓝 (pbar ybar), dist (ψ p) (constBd ybar) < δ := by
    have := hψ.cont.tendsto
    rw [hψ.base] at this
    exact this (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hψ.solves, hball, Metric.ball_mem_nhds (pbar ybar) (div_pos hδ hCpos)] with
    p hs hd hp n
  rw [Metric.mem_ball] at hp
  have hδC : δ / M.pointConst ≤ δ := div_le_self hδ.le hC
  have hp1 : dist p.1 ybar ≤ dist p (pbar ybar) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hp2 : dist p.2 ((0 : X), (0 : ℝ)) ≤ dist p (pbar ybar) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hx : ‖p.2.1‖ ≤ dist p (pbar ybar) := by
    refine le_trans ?_ hp2
    rw [Prod.dist_eq, ← dist_zero_right]
    exact le_max_left _ _
  have hσ : |p.2.2| ≤ dist p (pbar ybar) := by
    refine le_trans ?_ hp2
    rw [Prod.dist_eq, ← Real.dist_0_eq_abs, dist_comm]
    exact le_max_right _ _
  let v : Bd (List J) Y := mkBd (fun m => ψ p (m ++ n)) ⟨‖ψ p‖, fun m => norm_apply_le _ _⟩
  let pn : Y × X × ℝ := (lagAt (ψ p) p.1 n, M.stateAt p.2.1 p.2.2 n, p.2.2)
  have hpt : ∀ m, M.point v pn m = M.point (ψ p) p (m ++ n) := fun m => by
    cases m with
    | nil => rfl
    | cons i m =>
      have hs' : M.stateAt pn.2.1 pn.2.2 (i :: m) = M.stateAt p.2.1 p.2.2 (i :: m ++ n) :=
        (M.stateAt_append _ _ (i :: m) n).symm
      simp only [point, lagAt_cons, hs']
      rfl
  have hsv : M.Solves v pn := fun m => by rw [hpt]; exact hs _
  have hdv : dist v (constBd ybar) < δ := by
    refine lt_of_le_of_lt ?_ hd
    rw [dist_eq_norm, dist_eq_norm]
    refine norm_le_of_forall (norm_nonneg _) fun m => ?_
    have := norm_apply_le (ψ p - constBd ybar) (m ++ n)
    rw [lp.coeFn_sub, Pi.sub_apply, constBd_apply] at this
    simpa [v] using this
  have hdl : dist (lagAt (ψ p) p.1 n) ybar < δ := by
    cases n with
    | nil => exact lt_of_le_of_lt hp1 (lt_of_lt_of_le hp hδC)
    | cons i m =>
      refine lt_of_le_of_lt ?_ hd
      rw [lagAt_cons, dist_eq_norm, dist_eq_norm]
      have := norm_apply_le (ψ p - constBd ybar) m
      rwa [lp.coeFn_sub, Pi.sub_apply, constBd_apply] at this
  have hds : ‖M.stateAt p.2.1 p.2.2 n‖ < δ := by
    refine lt_of_le_of_lt (norm_stateAt_le hM _ _ n) ?_
    have hK : 0 ≤ M.shockBound / (1 - ‖M.Λ‖) := div_nonneg M.shockBound_nonneg h1.le
    have e : |p.2.2| * M.shockBound / (1 - ‖M.Λ‖) = |p.2.2| * (M.shockBound / (1 - ‖M.Λ‖)) :=
      mul_div_assoc _ _ _
    have h2 : ‖p.2.1‖ + |p.2.2| * M.shockBound / (1 - ‖M.Λ‖) ≤
        M.pointConst * dist p (pbar ybar) := by
      rw [e]
      unfold pointConst
      nlinarith
    have h3 : M.pointConst * dist p (pbar ybar) < δ := by
      rw [lt_div_iff₀ hCpos] at hp
      linarith
    linarith
  have hdp : dist pn (pbar ybar) < δ := by
    have e1 : dist pn.2.1 (pbar ybar : Y × X × ℝ).2.1 = ‖M.stateAt p.2.1 p.2.2 n‖ :=
      dist_zero_right _
    have e2 : dist pn.2.2 (pbar ybar : Y × X × ℝ).2.2 = |p.2.2| := Real.dist_0_eq_abs _
    rw [Prod.dist_eq, Prod.dist_eq, e1, e2]
    exact max_lt hdl (max_lt hds (lt_of_le_of_lt hσ (lt_of_lt_of_le hp hδC)))
  have h := congrArg (fun w : Bd (List J) Y => w []) (huniq pn v hdp hdv hsv)
  exact h.symm

variable (M)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] [Fintype J] in
/-- Woodford (2003), App. E.2: the state at node `n` as a linear map of `(x₀, σ)`. -/
noncomputable def stateL (n : List J) : X × ℝ →L[ℝ] X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => M.stateAt q.1 q.2 n
      map_add' := fun q q' => M.stateAt_add q.1 q'.1 q.2 q'.2 n
      map_smul' := fun c q => M.stateAt_smul c q.1 q.2 n }

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] [Fintype J] in
/-- Woodford (2003), App. E.2: members of `stateL`. -/
@[simp] theorem stateL_apply (n : List J) (q : X × ℝ) : M.stateL n q = M.stateAt q.1 q.2 n :=
  rfl

omit [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the derivative of the predecessor value `y_{n⁻}(p)` at node `n`
along a solution with derivative `ψ'`. -/
noncomputable def lagD (ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y) : List J → (Y × X × ℝ →L[ℝ] Y)
  | [] => ContinuousLinearMap.fst ℝ Y (X × ℝ)
  | _ :: m => (evalL Y m).comp ψ'

omit [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: members of `lagD`. -/
theorem lagD_apply (ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y) (n : List J) (v : Y × X × ℝ) :
    lagD ψ' n v = lagAt (ψ' v) v.1 n := by
  cases n <;> rfl

omit [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: the predecessor value along a differentiable family of
solutions is differentiable. -/
theorem hasFDerivAt_lag {ψ : Y × X × ℝ → Bd (List J) Y} {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y}
    {p₀ : Y × X × ℝ} (hψ : HasFDerivAt ψ ψ' p₀) (n : List J) :
    HasFDerivAt (fun p => lagAt (ψ p) p.1 n) (lagD ψ' n) p₀ := by
  cases n with
  | nil => exact hasFDerivAt_fst
  | cons i m => exact (evalL Y m).hasFDerivAt.comp p₀ hψ

variable {M}

omit [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: a linear map on `Y × X × ℝ` splits as
`L(a, x, s) = L(a, 0, 0) + L(0, x, 0) + s L(0, 0, 1)`. -/
theorem clm_triple {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Y × X × ℝ →L[ℝ] V) (a : Y) (x : X) (s : ℝ) :
    L (a, x, s) = L (a, 0, 0) + L (0, x, 0) + s • L (0, 0, 1) := by
  rw [← map_smul, ← map_add, ← map_add]
  congr 1
  ext <;> simp

/-- Woodford (2003), App. E.2, p. 695 (**differentiating the Markov property**): if the local
equilibrium `ψ` is differentiable at `p̄` with derivative `ψ'`, then at every node
`ψ' v n = g'(ψ' v n⁻, Dx_n v, v_σ)` with `g' = Dg(p̄)` the derivative of the policy function. -/
theorem markov_deriv (hM : M.Std) {ybar : Y} {ψ : Y × X × ℝ → Bd (List J) Y}
    (hψ : M.LocalSol ybar ψ) {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) (v : Y × X × ℝ) (n : List J) :
    ψ' v n = (evalL Y []).comp ψ' (lagAt (ψ' v) v.1 n, M.stateAt v.2.1 v.2.2 n, v.2.2) := by
  have hg : HasFDerivAt (policy ψ) ((evalL Y []).comp ψ') (pbar ybar) :=
    (evalL Y []).hasFDerivAt.comp (pbar ybar) hψd
  have hin : HasFDerivAt (fun p : Y × X × ℝ => (lagAt (ψ p) p.1 n, M.stateAt p.2.1 p.2.2 n, p.2.2))
      ((lagD ψ' n).prod (((M.stateL n).comp (ContinuousLinearMap.snd ℝ Y (X × ℝ))).prod
        ((ContinuousLinearMap.snd ℝ X ℝ).comp (ContinuousLinearMap.snd ℝ Y (X × ℝ)))))
      (pbar ybar) :=
    (hasFDerivAt_lag hψd n).prodMk
      ((((M.stateL n).comp (ContinuousLinearMap.snd ℝ Y (X × ℝ))).hasFDerivAt).prodMk
        ((ContinuousLinearMap.snd ℝ X ℝ).comp (ContinuousLinearMap.snd ℝ Y (X × ℝ))).hasFDerivAt)
  have hval : (lagAt (ψ (pbar ybar)) (pbar ybar : Y × X × ℝ).1 n,
      M.stateAt (pbar ybar : Y × X × ℝ).2.1 (pbar ybar : Y × X × ℝ).2.2 n,
      (pbar ybar : Y × X × ℝ).2.2) = pbar ybar := by
    rw [hψ.base]
    cases n <;> simp [pbar]
  rw [← hval] at hg
  have hR := hg.comp (pbar ybar) hin
  have hL : HasFDerivAt (fun p => ψ p n) ((evalL Y n).comp ψ') (pbar ybar) :=
    (evalL Y n).hasFDerivAt.comp (pbar ybar) hψd
  have heq : (fun p => ψ p n) =ᶠ[𝓝 (pbar ybar)]
      (policy ψ ∘ fun p => (lagAt (ψ p) p.1 n, M.stateAt p.2.1 p.2.2 n, p.2.2)) := by
    filter_upwards [markov hM hψ] with p hp
    exact hp n
  have hU := hL.unique (hR.congr_of_eventuallyEq heq)
  have := congrArg (fun L : Y × X × ℝ →L[ℝ] Y => L v) hU
  simpa [lagD_apply] using this

/-- Woodford (2003), App. E.2, p. 695 (**the implicit-function identity**): differentiating
`Φ(p, ψ(p)) = 0` at `p̄`, at every node `n`,
`∑_j π_j A ψ'v_{j::n} + B ψ'v_n + C ψ'v_{n⁻} + f_x Dx_n v + v_σ f_e(∑_j π_j ε_j) = 0`. -/
theorem ift_identity [FiniteDimensional ℝ Z] (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar : Y}
    {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ)
    {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y} (hψd : HasFDerivAt ψ ψ' (pbar ybar))
    (v : Y × X × ℝ) (n : List J) :
    ∑ j, M.prob j • M.dA ybar (ψ' v (j :: n)) + M.dB ybar (ψ' v n) +
      M.dC ybar (lagAt (ψ' v) v.1 n) + M.dX ybar (M.stateAt v.2.1 v.2.2 n) +
        v.2.2 • M.dE ybar (∑ j, M.prob j • M.shock j) = 0 := by
  have hP := hasFDerivAt_Phi_bar hM hf.continuous hf ybar
  have hin : HasFDerivAt (fun p : Y × X × ℝ => (p, ψ p))
      ((ContinuousLinearMap.id ℝ (Y × X × ℝ)).prod ψ') (pbar ybar) :=
    (hasFDerivAt_id _).prodMk hψd
  have hval : ((pbar ybar : Y × X × ℝ), ψ (pbar ybar)) = (pbar ybar, constBd ybar) := by
    rw [hψ.base]
  rw [← hval] at hP
  have hcomp := hP.comp (pbar ybar) hin
  have heq : (fun _ : Y × X × ℝ => (0 : Bd (List J) Z)) =ᶠ[𝓝 (pbar ybar)]
      (M.Phi hM hf.continuous ∘ fun p => (p, ψ p)) := by
    filter_upwards [hψ.solves] with p hp
    exact ((Phi_eq_zero_iff hM hf.continuous p (ψ p)).2 hp).symm
  have hU := (hasFDerivAt_const (0 : Bd (List J) Z) (pbar ybar : Y × X × ℝ)).unique
    (hcomp.congr_of_eventuallyEq heq)
  have h1 := congrArg (fun L : Y × X × ℝ →L[ℝ] Bd (List J) Z => L v n) hU
  have h2 : ((mult Z (constBd (fderiv ℝ M.bigF (wbar ybar)))).comp (M.pointL hM) ∘L
      ((ContinuousLinearMap.id ℝ (Y × X × ℝ)).prod ψ')) v n =
      fderiv ℝ M.bigF (wbar ybar) (M.point (ψ' v) v n) := rfl
  rw [h2, DF_point hM hf] at h1
  exact h1.symm

/-- Woodford (2003), App. E.2 (algebra behind certainty equivalence): if
`A G² + B G + C = 0` and `A + B + C` is injective, then `A G + A + B` is injective. -/
theorem ce_algebra {A B C : Y →L[ℝ] Z} {G : Y →L[ℝ] Y}
    (hI1 : ∀ h, A (G (G h)) + B (G h) + C h = 0) (hinj : Function.Injective (A + B + C))
    {c : Y} (hc : A (G c) + A c + B c = 0) : c = 0 := by
  have key : ∀ h, (A + B + C) h = A (G (h - G h)) + A (h - G h) + B (h - G h) := fun h => by
    have := hI1 h
    simp only [add_apply, map_sub]
    linear_combination (norm := abel) this
  have hinjG : Function.Injective ((LinearMap.id : Y →ₗ[ℝ] Y) - (G : Y →ₗ[ℝ] Y)) := by
    intro a b hab
    apply hinj
    have e : a - G a = b - G b := by simpa using hab
    rw [key, key, e]
  obtain ⟨h, hh⟩ := LinearMap.injective_iff_surjective.1 hinjG c
  have hh' : h - G h = c := by simpa using hh
  have : (A + B + C) h = (A + B + C) 0 := by rw [key, hh', hc, map_zero]
  have h0 := hinj this
  rw [← hh', h0, map_zero, sub_zero]


/-! ## First order: the perturbation equations and certainty equivalence -/

/-- Woodford (2003), App. E.2, and the first-order perturbation equations
(Schmitt-Grohé–Uribe): the derivative `g'` of the policy function at the steady state satisfies
the matrix quadratic `A G_y² + B G_y + C = 0` in the coefficient `G_y = g'(·, 0, 0)` on the
lagged decision. -/
theorem first_order_lag [FiniteDimensional ℝ Z] (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar : Y}
    {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ)
    {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y} (hψd : HasFDerivAt ψ ψ' (pbar ybar))
    {g' : Y × X × ℝ →L[ℝ] Y} (hg : HasFDerivAt (policy ψ) g' (pbar ybar)) (h : Y) :
    M.dA ybar (g' (g' (h, 0, 0), 0, 0)) + M.dB ybar (g' (h, 0, 0)) + M.dC ybar h = 0 := by
  have hg' : g' = (evalL Y []).comp ψ' := hg.unique ((evalL Y []).hasFDerivAt.comp _ hψd)
  subst hg'
  have hI := ift_identity hM hf hψ hψd (h, 0, 0) []
  have h0 := markov_deriv hM hψ hψd (h, 0, 0) []
  have hj := fun j : J => markov_deriv hM hψ hψd (h, 0, 0) [j]
  simp only [lagAt_nil, lagAt_cons, stateAt_nil, stateAt_cons, map_zero, zero_smul,
    add_zero] at hI h0 hj
  simp only [hj, ← Finset.sum_smul, hM.prob_sum, one_smul] at hI
  rw [← h0]
  exact hI

/-- Woodford (2003), App. E.2, and the first-order perturbation equations: the coefficient
`G_x = g'(0, ·, 0)` on the exogenous state satisfies
`A(G_y G_x x + G_x Λ x) + B G_x x + f_x x = 0`, written `A g'(g'(0,x,0), Λx, 0) + …`. -/
theorem first_order_state [FiniteDimensional ℝ Z] (hM : M.Std) (hf : ContDiff ℝ 1 M.f)
    {ybar : Y} {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ)
    {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y} (hψd : HasFDerivAt ψ ψ' (pbar ybar))
    {g' : Y × X × ℝ →L[ℝ] Y} (hg : HasFDerivAt (policy ψ) g' (pbar ybar)) (x : X) :
    M.dA ybar (g' (g' (0, x, 0), M.Λ x, 0)) + M.dB ybar (g' (0, x, 0)) + M.dX ybar x = 0 := by
  have hg' : g' = (evalL Y []).comp ψ' := hg.unique ((evalL Y []).hasFDerivAt.comp _ hψd)
  subst hg'
  have hI := ift_identity hM hf hψ hψd (0, x, 0) []
  have h0 := markov_deriv hM hψ hψd (0, x, 0) []
  have hj := fun j : J => markov_deriv hM hψ hψd (0, x, 0) [j]
  simp only [lagAt_nil, lagAt_cons, stateAt_nil, stateAt_cons, map_zero, zero_smul,
    add_zero] at hI h0 hj
  simp only [hj, ← Finset.sum_smul, hM.prob_sum, one_smul] at hI
  rw [← h0]
  exact hI

/-- Woodford (2003), App. E.2, and the perturbation literature (**certainty equivalence at first
order, `g_σ(ȳ, 0, 0) = 0`**): if the innovations have mean zero, `∑_j π_j ε_j = 0`, and the
steady-state Jacobian `A + B + C` is injective, then the derivative of the policy function in
the shock scale vanishes at the steady state. -/
theorem certainty_equivalence [FiniteDimensional ℝ Z] (hM : M.Std) (hf : ContDiff ℝ 1 M.f)
    {ybar : Y} {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ)
    {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y} (hψd : HasFDerivAt ψ ψ' (pbar ybar))
    {g' : Y × X × ℝ →L[ℝ] Y} (hg : HasFDerivAt (policy ψ) g' (pbar ybar))
    (hmean : ∑ j, M.prob j • M.shock j = 0)
    (hinj : Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar)) : g' (0, 0, 1) = 0 := by
  have hI1 := first_order_lag hM hf hψ hψd hg
  have hg' : g' = (evalL Y []).comp ψ' := hg.unique ((evalL Y []).hasFDerivAt.comp _ hψd)
  set G : Y →L[ℝ] Y := g'.comp (ContinuousLinearMap.inl ℝ Y (X × ℝ)) with hG
  have hGa : ∀ a, G a = g' (a, 0, 0) := fun a => rfl
  refine ce_algebra (A := M.dA ybar) (B := M.dB ybar) (C := M.dC ybar) (G := G)
    (fun h => by rw [hGa, hGa]; exact hI1 h) hinj ?_
  subst hg'
  have hI := ift_identity hM hf hψ hψd (0, 0, 1) []
  have h0 := markov_deriv hM hψ hψd (0, 0, 1) []
  have hj := fun j : J => markov_deriv hM hψ hψd (0, 0, 1) [j]
  simp only [lagAt_nil, lagAt_cons, stateAt_nil, stateAt_cons, map_zero, zero_add, one_smul,
    hmean, add_zero] at hI h0 hj
  simp only [hj] at hI
  rw [h0] at hI
  rw [hGa]
  have e : ∀ j, ((evalL Y []).comp ψ') ((evalL Y []).comp ψ' (0, 0, 1), M.η (M.shock j), 1) =
      G ((evalL Y []).comp ψ' (0, 0, 1)) + (evalL Y []).comp ψ' (0, M.η (M.shock j), 0) +
        (evalL Y []).comp ψ' (0, 0, 1) := fun j => by
    rw [clm_triple, one_smul, hGa]
  simp only [e, map_add, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hM.prob_sum,
    one_smul] at hI
  have hz : ∑ j, M.prob j • M.dA ybar ((evalL Y []).comp ψ' (0, M.η (M.shock j), 0)) = 0 := by
    have : ∀ j, M.prob j • M.dA ybar ((evalL Y []).comp ψ' (0, M.η (M.shock j), 0)) =
        M.dA ybar ((evalL Y []).comp ψ' (0, M.η (M.prob j • M.shock j), 0)) := fun j => by
      rw [map_smul, ← map_smul, ← map_smul]
      simp
    rw [Finset.sum_congr rfl fun j _ => this j, ← map_sum]
    have h2 : ∑ j, (evalL Y []).comp ψ' (0, M.η (M.prob j • M.shock j), 0) =
        (evalL Y []).comp ψ' (0, M.η (∑ j, M.prob j • M.shock j), 0) := by
      rw [← map_sum]
      congr 1
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, map_sum]
    rw [h2, hmean, map_zero, Prod.mk_zero_zero, Prod.mk_zero_zero, map_zero, map_zero]
  rw [hz, add_zero] at hI
  rw [← hGa]
  linear_combination (norm := abel) hI

/-- Woodford (2003), App. E.2 (**with no lagged decision, determinacy alone gives certainty
equivalence**): if `C = ∂f/∂y_{t−1} = 0` and the linearised operator is injective on `ℓ∞`, then
`A + B` is injective (a constant sequence `c` has `L c = (A + B) c`). -/
theorem injective_of_noLag (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar : Y}
    (hC : M.dC ybar = 0) (hinj : Function.Injective (M.linOp hM ybar)) :
    Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar) := by
  intro a b hab
  have hc : (M.dA ybar + M.dB ybar) (a - b) = 0 := by
    rw [hC, add_zero] at hab
    rw [map_sub, hab, sub_self]
  have hL : M.linOp hM ybar (constBd (a - b)) = 0 := by
    refine lp.ext (funext fun n => ?_)
    rw [linOp_apply hM hf, hC]
    simp only [constBd_apply, ← Finset.sum_smul, hM.prob_sum, one_smul,
      zero_apply, add_zero, lp.coeFn_zero, Pi.zero_apply]
    simpa using hc
  have h0 : (constBd (a - b) : Bd (List J) Y) = 0 := hinj (by rw [hL, map_zero])
  have := congrArg (fun w : Bd (List J) Y => w []) h0
  simp only [constBd_apply, lp.coeFn_zero, Pi.zero_apply] at this
  exact sub_eq_zero.1 this


/-! ## Second order: the `σ²` correction -/

omit [Fintype J] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), §1, pp. 385–389 (the second-order chain rule along a curve): if
`y = F ∘ a` near `0`, then `y″(0) = D²F(a 0)(a′ 0, a′ 0) + DF(a 0)(a″ 0)`. -/
theorem secondDeriv_comp {V W' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W'] [NormedSpace ℝ W'] {F : V → W'} {F1 : V → V →L[ℝ] W'}
    {F2 : V →L[ℝ] V →L[ℝ] W'} {a a1 : ℝ → V} {a2 : V} {y y1 : ℝ → W'} {y2 : W'}
    (hF : ∀ᶠ x in 𝓝 (a 0), HasFDerivAt F (F1 x) x) (hF1 : HasFDerivAt F1 F2 (a 0))
    (ha : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt a (a1 s) s) (ha1 : HasDerivAt a1 a2 0)
    (hy : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt y (y1 s) s) (hy1 : HasDerivAt y1 y2 0)
    (heq : ∀ᶠ s in 𝓝 (0 : ℝ), y s = F (a s)) : y2 = F2 (a1 0) (a1 0) + F1 (a 0) a2 := by
  have hct : ContinuousAt a 0 := ha.self_of_nhds.continuousAt
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), y1 s = F1 (a s) (a1 s) := by
    filter_upwards [heq.eventually_nhds, ha, hy, hct.tendsto.eventually hF] with s hs has hys hFs
    exact hys.unique ((hFs.comp_hasDerivAt s has).congr_of_eventuallyEq hs)
  have h2 : HasDerivAt (fun s => F1 (a s) (a1 s)) (F2 (a1 0) (a1 0) + F1 (a 0) a2) 0 :=
    (hF1.comp_hasDerivAt 0 ha.self_of_nhds).clm_apply ha1
  exact hy1.unique (h2.congr_of_eventuallyEq h1)

omit [Fintype J] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2 (the second-order chain rule for an expectation that vanishes):
if `∑_i c_i F(a_i s) = 0` near `0`, then
`∑_i c_i [D²F(a_i 0)(a_i′ 0, a_i′ 0) + DF(a_i 0)(a_i″ 0)] = 0`. -/
theorem secondDeriv_sum_comp {ι V W' : Type} [Fintype ι] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W'] [NormedSpace ℝ W'] {F : V → W'}
    {F1 : V → V →L[ℝ] W'} {F2 : ι → V →L[ℝ] V →L[ℝ] W'} {a a1 : ι → ℝ → V} {a2 : ι → V}
    {c : ι → ℝ} (hF : ∀ i, ∀ᶠ x in 𝓝 (a i 0), HasFDerivAt F (F1 x) x)
    (hF1 : ∀ i, HasFDerivAt F1 (F2 i) (a i 0))
    (ha : ∀ i, ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (a i) (a1 i s) s)
    (ha1 : ∀ i, HasDerivAt (a1 i) (a2 i) 0)
    (heq : ∀ᶠ s in 𝓝 (0 : ℝ), ∑ i, c i • F (a i s) = 0) :
    ∑ i, c i • (F2 i (a1 i 0) (a1 i 0) + F1 (a i 0) (a2 i)) = 0 := by
  have ha' : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, HasDerivAt (a i) (a1 i s) s := Filter.eventually_all.2 ha
  have hF' : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, HasFDerivAt F (F1 (a i s)) (a i s) :=
    Filter.eventually_all.2 fun i => (ha i).self_of_nhds.continuousAt.tendsto.eventually (hF i)
  have h1 : ∀ᶠ s in 𝓝 (0 : ℝ), ∑ i, c i • F1 (a i s) (a1 i s) = 0 := by
    filter_upwards [heq.eventually_nhds, ha', hF'] with s hs has hFs
    have hd : HasDerivAt (fun s => ∑ i, c i • F (a i s)) (∑ i, c i • F1 (a i s) (a1 i s)) s :=
      HasDerivAt.fun_sum fun i _ => ((hFs i).comp_hasDerivAt s (has i)).const_smul (c i)
    exact hd.unique ((hasDerivAt_const s (0 : W')).congr_of_eventuallyEq hs)
  have h2 : HasDerivAt (fun s => ∑ i, c i • F1 (a i s) (a1 i s))
      (∑ i, c i • (F2 i (a1 i 0) (a1 i 0) + F1 (a i 0) (a2 i))) 0 :=
    HasDerivAt.fun_sum fun i _ =>
      (((hF1 i).comp_hasDerivAt 0 (ha i).self_of_nhds).clm_apply (ha1 i)).const_smul (c i)
  exact h2.unique ((hasDerivAt_const (0 : ℝ) (0 : W')).congr_of_eventuallyEq h1)

/-- Woodford (2003), App. E.2, and the second-order perturbation equation (Schmitt-Grohé–Uribe,
2004) (**the `σ²` correction of the policy function**): let `f` be `C²`, the innovations have
mean zero and `A + B + C` be injective, and let the local equilibrium `ψ` be `C²` at `p̄` (as
`exists_smooth_solution` provides). Writing `g` for the policy function, `g′ = Dg(p̄)`,
`g″ = D²g(p̄)`, `g_σσ = g″(e_σ, e_σ)` and `ζ_j = (g′(0, ηε_j, 0), 0, 0, 0, ε_j)`,
`(A G_y + A + B) g_σσ = −∑_j π_j [A g″((0, ηε_j, 0), (0, ηε_j, 0)) + D²f(z̄)(ζ_j, ζ_j)]`,
where `G_y = g′(·, 0, 0)`. With `g_σ = 0` (certainty equivalence) this is the whole
`σ`-expansion of the decision rule to second order at the steady state. -/
theorem second_order_sigma [FiniteDimensional ℝ Z] (hM : M.Std) (hf : ContDiff ℝ 2 M.f)
    {ybar : Y} {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) (hmean : ∑ j, M.prob j • M.shock j = 0)
    (hinj : Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar)) :
    M.dA ybar (fderiv ℝ (policy ψ) (pbar ybar)
        (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1), 0, 0)) +
      M.dA ybar (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      M.dB ybar (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      ∑ j, M.prob j • (M.dA ybar (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar)
          (0, M.η (M.shock j), 0) (0, M.η (M.shock j), 0)) +
        fderiv ℝ (fderiv ℝ M.f) (zbar ybar)
          (fderiv ℝ (policy ψ) (pbar ybar) (0, M.η (M.shock j), 0), 0, 0, 0, M.shock j)
          (fderiv ℝ (policy ψ) (pbar ybar) (0, M.η (M.shock j), 0), 0, 0, 0, M.shock j)) =
      0 := by
  obtain ⟨e3, he3⟩ : ∃ e3 : Y × X × ℝ, e3 = (0, 0, 1) := ⟨_, rfl⟩
  rw [← he3]
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (pbar ybar)) (pbar ybar) :=
    (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hψev : ∀ᶠ p in 𝓝 (pbar ybar), HasFDerivAt ψ (fderiv ℝ ψ p) p :=
    (hψ2.eventually (by simp)).mono fun p hp => (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hψF1 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (pbar ybar)) (pbar ybar) :=
    ((hψ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hg2 : ContDiffAt ℝ 2 (policy ψ) (pbar ybar) :=
    (evalL Y []).contDiff.contDiffAt.comp (pbar ybar) hψ2
  have hgd : HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) (pbar ybar)) (pbar ybar) :=
    (hg2.differentiableAt (by norm_num)).hasFDerivAt
  have hgev : ∀ᶠ p in 𝓝 (pbar ybar), HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) p) p :=
    (hg2.eventually (by simp)).mono fun p hp => (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hgF1 : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar))
      (pbar ybar) :=
    ((hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hfd : ∀ z, HasFDerivAt M.f (fderiv ℝ M.f z) z := fun z =>
    (hf.differentiable (by norm_num) z).hasFDerivAt
  have hfF1 : HasFDerivAt (fderiv ℝ M.f) (fderiv ℝ (fderiv ℝ M.f) (zbar ybar)) (zbar ybar) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _).hasFDerivAt
  have hce : fderiv ℝ (policy ψ) (pbar ybar) e3 = 0 := by
    rw [he3]
    exact certainty_equivalence hM (hf.of_le (by norm_num)) hψ hψd hgd hmean hinj
  have hg'eq : fderiv ℝ (policy ψ) (pbar ybar) = (evalL Y []).comp (fderiv ℝ ψ (pbar ybar)) :=
    hgd.unique ((evalL Y []).hasFDerivAt.comp (pbar ybar) hψd)
  have hsm : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (v : V) (s : ℝ),
      HasDerivAt (fun s : ℝ => s • v) v s := fun v s => by
    simpa using (hasDerivAt_id s).smul_const v
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Y × X × ℝ, γ = fun s => (ybar, 0, s) := ⟨_, rfl⟩
  have hγd : ∀ s, HasDerivAt γ e3 s := fun s => by
    rw [hγ, he3]
    exact (hasDerivAt_const s ybar).prodMk ((hasDerivAt_const s (0 : X)).prodMk (hasDerivAt_id s))
  have hγ0 : γ 0 = pbar ybar := by rw [hγ]; rfl
  have hγt : Tendsto γ (𝓝 0) (𝓝 (pbar ybar)) := hγ0 ▸ (hγd 0).continuousAt.tendsto
  obtain ⟨u, hu⟩ : ∃ u : ℝ → Bd (List J) Y, u = fun s => ψ (γ s) := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ → Bd (List J) Y, u1 = fun s => fderiv ℝ ψ (γ s) e3 := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2 : Bd (List J) Y, u2 = fderiv ℝ (fderiv ℝ ψ) (pbar ybar) e3 e3 :=
    ⟨_, rfl⟩
  have hud : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt u (u1 s) s := by
    rw [hu, hu1]
    filter_upwards [hγt.eventually hψev] with s hs
    exact hs.comp_hasDerivAt s (hγd s)
  have hu1d : HasDerivAt u1 u2 0 := by
    have hF : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (pbar ybar)) (γ 0) := by
      rw [hγ0]; exact hψF1
    have h1 := (ContinuousLinearMap.apply ℝ (Bd (List J) Y) e3).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (hF.comp_hasDerivAt (0 : ℝ) (hγd 0))
    rw [hu1, hu2]
    exact h1
  have hun : ∀ n, ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s => u s n) (u1 s n) s := fun n =>
    hud.mono fun s hs => (evalL Y n).hasFDerivAt.comp_hasDerivAt s hs
  have hun1 : ∀ n, HasDerivAt (fun s => u1 s n) (u2 n) 0 := fun n =>
    (evalL Y n).hasFDerivAt.comp_hasDerivAt 0 hu1d
  have hu0 : u 0 = constBd ybar := by rw [hu]; simp only [hγ0]; exact hψ.base
  have hu10 : u1 0 = fderiv ℝ ψ (pbar ybar) e3 := by rw [hu1]; simp only [hγ0]
  -- the root: `u s [] = g (γ s)` exactly
  have hR0 : u2 [] = fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) e3 e3 := by
    have hF : ∀ᶠ x in 𝓝 (γ 0), HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) x) x := by
      rw [hγ0]; exact hgev
    have hF1 : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar))
        (γ 0) := by rw [hγ0]; exact hgF1
    have := secondDeriv_comp (F := policy ψ) (a := γ) (a1 := fun _ => e3) (a2 := 0)
      (y := fun s => u s []) (y1 := fun s => u1 s []) hF hF1 (Eventually.of_forall hγd)
      (hasDerivAt_const 0 e3) (hun []) (hun1 [])
      (Eventually.of_forall fun s => by rw [hu]; rfl)
    rw [this, map_zero, add_zero]
  -- first-order values at the root and its successors
  have h1root : u1 0 [] = 0 := by
    rw [hu10, ← hce, hg'eq]
    rfl
  have h1child : ∀ j, u1 0 [j] = fderiv ℝ (policy ψ) (pbar ybar) (0, M.η (M.shock j), 0) :=
    fun j => by
      have h := markov_deriv hM hψ hψd e3 [j]
      rw [← hg'eq, ← hu10, he3] at h
      simp only [lagAt_cons, stateAt_cons, stateAt_nil, map_zero, zero_add, one_smul] at h
      rw [h1root] at h
      rw [h, clm_triple, ← he3, hce, smul_zero, add_zero, Prod.mk_zero_zero, Prod.mk_zero_zero,
        map_zero, zero_add]
  -- the successors: `u s [j] = g(u s [], s η ε_j, s)` (Markov property)
  have hRj : ∀ j, u2 [j] = fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, M.η (M.shock j), 1)
      (0, M.η (M.shock j), 1) + fderiv ℝ (policy ψ) (pbar ybar) (u2 [], 0, 0) := fun j => by
    obtain ⟨b, hb⟩ : ∃ b : ℝ → Y × X × ℝ, b = fun s => (u s [], s • M.η (M.shock j), s) :=
      ⟨_, rfl⟩
    have hb0 : b 0 = pbar ybar := by
      rw [hb]
      change (u 0 [], (0 : ℝ) • M.η (M.shock j), (0 : ℝ)) = pbar ybar
      rw [hu0, zero_smul]
      rfl
    have hF : ∀ᶠ x in 𝓝 (b 0), HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) x) x := by
      rw [hb0]; exact hgev
    have hF1 : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar))
        (b 0) := by rw [hb0]; exact hgF1
    have ha : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt b (u1 s [], M.η (M.shock j), 1) s := by
      rw [hb]
      exact (hun []).mono fun s hs => hs.prodMk ((hsm _ s).prodMk (hasDerivAt_id s))
    have ha1 : HasDerivAt (fun s => (u1 s [], M.η (M.shock j), (1 : ℝ))) (u2 [], 0, 0) 0 :=
      (hun1 []).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
    have heq : ∀ᶠ s in 𝓝 (0 : ℝ), u s [j] = policy ψ (b s) := by
      filter_upwards [hγt.eventually (markov hM hψ)] with s hs
      have h := hs [j]
      rw [hγ] at h
      simp only [lagAt_cons, stateAt_cons, stateAt_nil, map_zero, zero_add] at h
      rw [hb, hu, hγ]
      exact h
    have := secondDeriv_comp hF hF1 ha ha1 (hun [j]) (hun1 [j]) heq
    rw [this, hb0, h1root]
  -- the equilibrium condition at the root
  have hEq := secondDeriv_sum_comp (F := M.f) (F1 := fderiv ℝ M.f)
    (F2 := fun _ => fderiv ℝ (fderiv ℝ M.f) (zbar ybar)) (c := M.prob)
    (a := fun j s => (u s [j], u s [], ybar, (0 : X), s • M.shock j))
    (a1 := fun j s => (u1 s [j], u1 s [], (0 : Y), (0 : X), M.shock j))
    (a2 := fun j => (u2 [j], u2 [], (0 : Y), (0 : X), (0 : E)))
    (fun _ => Eventually.of_forall hfd)
    (fun j => by
      rw [hu0, constBd_apply, constBd_apply, zero_smul]
      exact hfF1)
    (fun j => ((hun [j]).and (hun [])).mono fun s hs => hs.1.prodMk (hs.2.prodMk
      ((hasDerivAt_const s ybar).prodMk ((hasDerivAt_const s (0 : X)).prodMk (hsm _ s)))))
    (fun j => (hun1 [j]).prodMk ((hun1 []).prodMk ((hasDerivAt_const _ _).prodMk
      ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _)))))
    (by
      filter_upwards [hγt.eventually hψ.solves] with s hs
      have h := hs []
      rw [hγ] at h
      simp only [bigF, ell_apply, point, lagAt_nil, stateAt_nil] at h
      rw [hu, hγ]
      exact h)
  simp only [hu0, constBd_apply, zero_smul] at hEq
  rw [show ((ybar, ybar, ybar, 0, 0) : Y × Y × Y × X × E) = zbar ybar from rfl] at hEq
  simp only [h1root, h1child, fderiv_f_apply, map_zero, add_zero] at hEq
  rw [hR0] at hEq hRj
  -- algebra
  have hsplit : ∀ j : J, ((0 : Y), M.η (M.shock j), (1 : ℝ)) =
      ((0 : Y), M.η (M.shock j), (0 : ℝ)) + e3 := fun j => by
    rw [he3]
    ext <;> simp
  have hsum0 : ∑ j, M.prob j • (((0 : Y), M.η (M.shock j), (0 : ℝ)) : Y × X × ℝ) = 0 := by
    have : ∑ j, M.prob j • (((0 : Y), M.η (M.shock j), (0 : ℝ)) : Y × X × ℝ) =
        ((0 : Y), M.η (∑ j, M.prob j • M.shock j), (0 : ℝ)) := by
      ext <;> simp [Prod.fst_sum, Prod.snd_sum, map_sum]
    rw [this, hmean, map_zero]
    rfl
  set gs := fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) e3 e3 with hgs
  set D1 := fderiv ℝ (policy ψ) (pbar ybar) with hD1
  set D2 := fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) with hD2
  set f2 := fderiv ℝ (fderiv ℝ M.f) (zbar ybar) with hf2
  have hj : ∀ j, M.prob j • (f2 (D1 (0, M.η (M.shock j), 0), 0, 0, 0, M.shock j)
      (D1 (0, M.η (M.shock j), 0), 0, 0, 0, M.shock j) + (M.dA ybar (u2 [j]) + M.dB ybar gs)) =
      M.prob j • (M.dA ybar (D2 (0, M.η (M.shock j), 0) (0, M.η (M.shock j), 0)) +
        f2 (D1 (0, M.η (M.shock j), 0), 0, 0, 0, M.shock j)
          (D1 (0, M.η (M.shock j), 0), 0, 0, 0, M.shock j)) +
      M.prob j • (M.dA ybar (D1 (gs, 0, 0)) + M.dA ybar gs + M.dB ybar gs) +
      M.dA ybar (D2 (M.prob j • ((0 : Y), M.η (M.shock j), (0 : ℝ))) e3) +
      M.dA ybar (D2 e3 (M.prob j • ((0 : Y), M.η (M.shock j), (0 : ℝ)))) := fun j => by
    rw [hRj j, hsplit j]
    simp only [map_add, map_smul, add_apply, smul_apply]
    module
  rw [Finset.sum_congr rfl fun j _ => hj j] at hEq
  simp only [Finset.sum_add_distrib, ← Finset.sum_smul, hM.prob_sum, one_smul, ← map_sum,
    ← sum_apply, hsum0, map_zero, zero_apply, add_zero] at hEq
  rw [← hEq]
  abel


/-! ## The policy function is `Cᵏ` -/

/-- Woodford (2003), App. E.2, and the perturbation method (**the policy function
`g(y_{−1}, x, σ)` is `Cᵏ` jointly in its arguments on a neighbourhood of the steady state**):
under the hypotheses of `exists_smooth_solution`, the local equilibrium `ψ` and the policy
function `g = ψ(·)_root` are `Cᵏ` on a neighbourhood of `p̄ = (ȳ, 0, 0)`, `g(p̄) = ȳ`, and the
equilibrium is Markov in `(y_{t−1}, x_t, σ)` (`markov`). -/
theorem exists_smooth_policy [FiniteDimensional ℝ Z] (hM : M.Std) {k : ℕ} (hk : 1 ≤ k)
    (hf : ContDiff ℝ k M.f) {ybar : Y} (hss : M.f (zbar ybar) = 0)
    (hdet : (M.linOp hM ybar).IsInvertible) :
    ∃ ψ : Y × X × ℝ → Bd (List J) Y, M.LocalSol ybar ψ ∧ policy ψ (pbar ybar) = ybar ∧
      (∃ U ∈ 𝓝 (pbar ybar), ContDiffOn ℝ k ψ U ∧ ContDiffOn ℝ k (policy ψ) U) ∧
      ∀ᶠ p in 𝓝 (pbar ybar), ∀ n,
        ψ p n = policy ψ (lagAt (ψ p) p.1 n, M.stateAt p.2.1 p.2.2 n, p.2.2) := by
  obtain ⟨ψ, hψ, hc⟩ := exists_smooth_solution hM hk hf hss hdet
  obtain ⟨U, hU, hcU⟩ := hc.contDiffOn le_rfl (by simp)
  refine ⟨ψ, hψ, ?_, ⟨U, hU, hcU, (evalL Y []).contDiff.comp_contDiffOn hcU⟩, markov hM hψ⟩
  rw [policy, hψ.base]
  rfl

/-! ## Determinacy: when the linearised operator is invertible -/

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: `‖∑_j π_j h_{j::n}‖ ≤ ‖h‖`. -/
theorem norm_exp_le (hM : M.Std) (h : Bd (List J) Y) (n : List J) :
    ‖∑ j, M.prob j • h (j :: n)‖ ≤ ‖h‖ := by
  calc ‖∑ j, M.prob j • h (j :: n)‖ ≤ ∑ j, ‖M.prob j • h (j :: n)‖ := norm_sum_le _ _
    _ ≤ ∑ j, M.prob j * ‖h‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_smul, Real.norm_of_nonneg (hM.prob_nonneg j)]
        exact mul_le_mul_of_nonneg_left (norm_apply_le h _) (hM.prob_nonneg j)
    _ = ‖h‖ := by rw [← Finset.sum_mul, hM.prob_sum, one_mul]

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2, p. 695: the conditional expectation `h ↦ (E_t h_{t+1})_n =
(∑_j π_j h_{j::n})_n`, a bounded operator of norm at most one on `ℓ∞`. -/
noncomputable def expOp (hM : M.Std) : Bd (List J) Y →L[ℝ] Bd (List J) Y :=
  LinearMap.mkContinuous
    { toFun := fun h => mkBd (fun n => ∑ j, M.prob j • h (j :: n)) ⟨‖h‖, norm_exp_le hM h⟩
      map_add' := fun h h' => by
        refine lp.ext (funext fun n => ?_)
        simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c h => by
        refine lp.ext (funext fun n => ?_)
        simp [Finset.smul_sum, smul_comm c] }
    1 (fun h => by
      rw [one_mul]
      exact norm_le_of_forall (norm_nonneg _) (norm_exp_le hM h))

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: members of `expOp`. -/
@[simp] theorem expOp_apply (hM : M.Std) (h : Bd (List J) Y) (n : List J) :
    expOp hM h n = ∑ j, M.prob j • h (j :: n) :=
  rfl

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: `‖E_t‖ ≤ 1`. -/
theorem norm_expOp_le (hM : M.Std) : ‖expOp hM‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
    rw [one_mul]
    exact norm_le_of_forall (norm_nonneg _) (norm_exp_le hM h)

omit [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] in
/-- Woodford (2003), App. E.2: multiplication by a constant matrix `c` has norm at most `‖c‖`. -/
theorem norm_mult_const_le (c : Y →L[ℝ] Z) :
    ‖(mult Z (constBd c) : Bd (List J) Y →L[ℝ] Bd (List J) Z)‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun h =>
    norm_le_of_forall (by positivity) fun n =>
      (c.le_opNorm (h n)).trans (mul_le_mul_of_nonneg_left (norm_apply_le h n) (norm_nonneg _))

omit [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] in
/-- Woodford (2003), App. E.2: multiplication by an invertible constant matrix is invertible on
`ℓ∞`. -/
theorem isInvertible_mult_const {c : Y →L[ℝ] Z} (hc : c.IsInvertible) :
    (mult Z (constBd c) : Bd (List J) Y →L[ℝ] Bd (List J) Z).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse (g := mult Y (constBd c.inverse))
    (ContinuousLinearMap.ext fun h => lp.ext (funext fun n => by
      simp [hc.self_apply_inverse]))
    (ContinuousLinearMap.ext fun h => lp.ext (funext fun n => by
      simp [hc.inverse_apply_self]))

/-- Woodford (2003), App. E.2 (**the linearised operator without lagged decisions**): when
`C = 0`, `L = A E_t + B`. -/
theorem linOp_eq_noLag (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar : Y} (hC : M.dC ybar = 0) :
    M.linOp hM ybar = (mult Z (constBd (M.dA ybar))).comp (expOp hM) +
      mult Z (constBd (M.dB ybar)) := by
  refine ContinuousLinearMap.ext fun h => lp.ext (funext fun n => ?_)
  rw [linOp_apply hM hf, hC]
  simp [map_sum, map_smul]

/-- Woodford (2003), App. E.2, and Appendix A.3's determinacy condition in matrix form
(**a sufficient condition for determinacy without lagged decisions**): if `C = 0`, `B` is
invertible and `‖B⁻¹A‖ < 1` (all roots of the forward system inside the unit circle in the
induced norm), then `L h = A E_t h_{t+1} + B h_t` is invertible on `ℓ∞` (Neumann series). -/
theorem isInvertible_linOp_noLag (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar : Y}
    (hC : M.dC ybar = 0) (hB : (M.dB ybar).IsInvertible)
    (hAB : ‖(M.dB ybar).inverse.comp (M.dA ybar)‖ < 1) : (M.linOp hM ybar).IsInvertible := by
  obtain ⟨T, hT⟩ : ∃ T : Bd (List J) Y →L[ℝ] Bd (List J) Y,
      T = (mult Y (constBd ((M.dB ybar).inverse.comp (M.dA ybar)))).comp (expOp hM) :=
    ⟨_, rfl⟩
  have hTn : ‖-T‖ < 1 := by
    rw [norm_neg, hT]
    calc ‖(mult Y (constBd ((M.dB ybar).inverse.comp (M.dA ybar)))).comp (expOp hM)‖
        ≤ ‖(mult Y (constBd ((M.dB ybar).inverse.comp (M.dA ybar))) :
          Bd (List J) Y →L[ℝ] Bd (List J) Y)‖ * ‖expOp hM‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖(M.dB ybar).inverse.comp (M.dA ybar)‖ * 1 :=
          mul_le_mul (norm_mult_const_le _) (norm_expOp_le hM) (norm_nonneg _) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact hAB
  obtain ⟨u, hu⟩ : ∃ u : (Bd (List J) Y →L[ℝ] Bd (List J) Y)ˣ, u = Units.oneSub (-T) hTn :=
    ⟨_, rfl⟩
  have hu1 : (u : Bd (List J) Y →L[ℝ] Bd (List J) Y) = 1 + T := by
    rw [hu, Units.val_oneSub, sub_neg_eq_add]
  have hinvU : (u : Bd (List J) Y →L[ℝ] Bd (List J) Y).IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse (g := ((u⁻¹ : (Bd (List J) Y →L[ℝ] _)ˣ) :
      Bd (List J) Y →L[ℝ] Bd (List J) Y))
      (by rw [← ContinuousLinearMap.mul_def, u.mul_inv]; rfl)
      (by rw [← ContinuousLinearMap.mul_def, u.inv_mul]; rfl)
  have heq : M.linOp hM ybar = (mult Z (constBd (M.dB ybar))).comp
      (u : Bd (List J) Y →L[ℝ] Bd (List J) Y) := by
    rw [hu1, linOp_eq_noLag hM hf hC]
    refine ContinuousLinearMap.ext fun h => lp.ext (funext fun n => ?_)
    rw [hT]
    simp only [add_apply, ContinuousLinearMap.comp_apply, mult_apply,
      constBd_apply, one_apply_eq_self, lp.coeFn_add, Pi.add_apply, map_add,
      hB.self_apply_inverse]
    exact add_comm _ _
  rw [heq]
  exact (isInvertible_mult_const hB).comp hinvU

omit [Fintype J] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), App. E.2: a linear map `ℝ → ℝ` is multiplication by its value at `1`. -/
theorem clm_real_apply (L : ℝ →L[ℝ] ℝ) (x : ℝ) : L x = x * L 1 := by
  rw [← smul_eq_mul, ← L.map_smul, smul_eq_mul, mul_one]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z] in
/-- Woodford (2003), App. A.3, eq. (A.9), and Proposition 2.3's determinacy condition on the
event tree (**the scalar forward-looking case, exactly**): for a scalar model without lagged
decision (`C = 0`), the linearised operator `L h = a E_t h_{t+1} + b h_t` is invertible on
`ℓ∞` (of the tree) IF AND ONLY IF `|a| < |b|`. If `|b| ≤ |a|`, the sequence
`h_n = (−b/a)^{t(n)}` is a bounded nonzero solution of `L h = 0` (a sunspot direction). -/
theorem isInvertible_linOp_scalar_iff {N : Model J ℝ ℝ X E} (hN : N.Std)
    (hf : ContDiff ℝ 1 N.f) {ybar : ℝ} (hC : N.dC ybar = 0) :
    (N.linOp hN ybar).IsInvertible ↔ |N.dA ybar 1| < |N.dB ybar 1| := by
  constructor
  · intro hinv
    by_contra hlt
    push Not at hlt
    set a := N.dA ybar 1 with ha
    set b := N.dB ybar 1 with hb
    set r : ℝ := -b / a with hr
    have hr1 : |r| ≤ 1 := by
      rw [hr, abs_div, abs_neg]
      rcases eq_or_ne a 0 with h0 | h0
      · simp [h0]
      · exact (div_le_one (abs_pos.2 h0)).2 hlt
    have hrb : a * r + b = 0 := by
      rcases eq_or_ne a 0 with h0 | h0
      · have : |b| ≤ 0 := by simpa [h0] using hlt
        rw [h0, abs_nonpos_iff.1 this]
        ring
      · rw [hr]
        field_simp
        ring
    let h : Bd (List J) ℝ := mkBd (fun n => r ^ n.length) ⟨1, fun n => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_one₀ (abs_nonneg r) hr1⟩
    have hL : N.linOp hN ybar h = N.linOp hN ybar 0 := by
      rw [map_zero]
      refine lp.ext (funext fun n => ?_)
      rw [linOp_apply hN hf, hC]
      simp only [h, mkBd_apply, List.length_cons, smul_eq_mul, zero_apply,
        add_zero, lp.coeFn_zero, Pi.zero_apply]
      rw [clm_real_apply (N.dA ybar), clm_real_apply (N.dB ybar), ← ha, ← hb]
      simp only [← Finset.sum_mul, hN.prob_sum, one_mul, pow_succ]
      linear_combination r ^ n.length * hrb
    have h0 := hinv.injective hL
    have := congrArg (fun w : Bd (List J) ℝ => w []) h0
    simp [h] at this
  · intro hlt
    set a := N.dA ybar 1 with ha
    set b := N.dB ybar 1 with hb
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hlt
      exact absurd hlt (not_lt.2 (abs_nonneg a))
    have h1 : (N.dB ybar).comp (b⁻¹ • ContinuousLinearMap.id ℝ ℝ) =
        ContinuousLinearMap.id ℝ ℝ := ContinuousLinearMap.ext fun x => by
      rw [ContinuousLinearMap.comp_apply, clm_real_apply (N.dB ybar), ← hb]
      simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      field_simp
    have h2 : (b⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp (N.dB ybar) =
        ContinuousLinearMap.id ℝ ℝ := ContinuousLinearMap.ext fun x => by
      rw [ContinuousLinearMap.comp_apply, clm_real_apply (N.dB ybar) x, ← hb]
      simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      field_simp
    have hBinv : (N.dB ybar).IsInvertible := ContinuousLinearMap.IsInvertible.of_inverse h1 h2
    have hinv : (N.dB ybar).inverse = b⁻¹ • ContinuousLinearMap.id ℝ ℝ :=
      ContinuousLinearMap.inverse_eq h1 h2
    refine isInvertible_linOp_noLag hN hf hC hBinv ?_
    rw [hinv]
    refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (M := |a| / |b|) fun x => ?_) ?_
    · rw [ContinuousLinearMap.comp_apply, clm_real_apply (N.dA ybar), ← ha]
      simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        Real.norm_eq_abs, abs_mul, abs_inv]
      rw [div_eq_mul_inv]
      ring_nf
      exact le_of_eq rfl
    · rw [div_lt_one (abs_pos.2 hb0)]
      exact hlt


/-! ## The expansion of the decision rule in `σ` -/

omit [Fintype J] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Woodford (2003), §1, eq. (1.2), p. 385, for curves in a normed space (second-order Taylor
expansion with a little-o remainder): if `φ′ = φ₁` near `0` and `φ₁′(0) = φ₂`, then
`φ(σ) = φ(0) + σ φ₁(0) + (σ²/2) φ₂ + o(σ²)`. -/
theorem taylor_two_isLittleO {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {φ φ1 : ℝ → V} {φ2 : V} (hφ : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt φ (φ1 s) s)
    (hφ1 : HasDerivAt φ1 φ2 0) :
    (fun σ => φ σ - φ 0 - σ • φ1 0 - (σ ^ 2 / 2) • φ2) =o[𝓝 0] fun σ => σ ^ 2 := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have ho := hasDerivAt_iff_isLittleO.1 hφ1
  rw [Asymptotics.isLittleO_iff] at ho
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hφ (ho hc))
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with σ hσ
  have hσδ : |σ| < δ := by simpa [Real.dist_eq] using hσ
  have hsub : Metric.closedBall (0 : ℝ) |σ| ⊆ Metric.ball 0 δ :=
    Metric.closedBall_subset_ball hσδ
  have hd : ∀ t ∈ Metric.closedBall (0 : ℝ) |σ|, HasDerivWithinAt
      (fun σ => φ σ - φ 0 - σ • φ1 0 - (σ ^ 2 / 2) • φ2) (φ1 t - φ1 0 - t • φ2)
      (Metric.closedBall (0 : ℝ) |σ|) t := fun t ht => by
    have h1 : HasDerivAt φ (φ1 t) t := (hball (hsub ht)).1
    have h2 : HasDerivAt (fun σ : ℝ => σ • φ1 0) (φ1 0) t := by
      simpa using (hasDerivAt_id t).smul_const (φ1 0)
    have h3 : HasDerivAt (fun σ : ℝ => (σ ^ 2 / 2) • φ2) (t • φ2) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).smul_const φ2
      convert this using 2
      push_cast
      ring
    exact (((h1.sub_const (φ 0)).sub h2).sub h3).hasDerivWithinAt
  have hb : ∀ t ∈ Metric.closedBall (0 : ℝ) |σ|, ‖φ1 t - φ1 0 - t • φ2‖ ≤ c * |σ| :=
    fun t ht => by
      have h : ‖φ1 t - φ1 0 - t • φ2‖ ≤ c * ‖t‖ := by simpa using (hball (hsub ht)).2
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hc.le)
      simpa [Real.dist_eq] using ht
  have key := (convex_closedBall (0 : ℝ) |σ|).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (Metric.mem_closedBall_self (abs_nonneg σ)) (by simp : σ ∈ Metric.closedBall (0 : ℝ) |σ|)
  simp only [sub_self, zero_smul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at key
  rw [norm_pow, Real.norm_eq_abs]
  calc _ ≤ c * |σ| * ‖σ‖ := key
    _ = c * |σ| ^ 2 := by rw [Real.norm_eq_abs]; ring

/-- Woodford (2003), App. E.2, and the perturbation method (**the decision rule to second order
in `σ`**): under the hypotheses of `second_order_sigma`, at the steady state
`g(ȳ, 0, σ) = ȳ + (σ²/2) g_σσ + o(σ²)` — no first-order term (certainty equivalence) and a
risk correction `g_σσ` determined by the second-order equation. -/
theorem policy_sigma_expansion [FiniteDimensional ℝ Z] (hM : M.Std) (hf : ContDiff ℝ 2 M.f)
    {ybar : Y} {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) (hmean : ∑ j, M.prob j • M.shock j = 0)
    (hinj : Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar)) :
    (fun σ : ℝ => policy ψ (ybar, 0, σ) - ybar -
      (σ ^ 2 / 2) • fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) =o[𝓝 0]
      fun σ => σ ^ 2 := by
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (pbar ybar)) (pbar ybar) :=
    (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hg2 : ContDiffAt ℝ 2 (policy ψ) (pbar ybar) :=
    (evalL Y []).contDiff.contDiffAt.comp (pbar ybar) hψ2
  have hgd : HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) (pbar ybar)) (pbar ybar) :=
    (hg2.differentiableAt (by norm_num)).hasFDerivAt
  have hgev : ∀ᶠ p in 𝓝 (pbar ybar), HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) p) p :=
    (hg2.eventually (by simp)).mono fun p hp => (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hgF1 : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar))
      (pbar ybar) :=
    ((hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hce : fderiv ℝ (policy ψ) (pbar ybar) (0, 0, 1) = 0 :=
    certainty_equivalence hM (hf.of_le (by norm_num)) hψ hψd hgd hmean hinj
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Y × X × ℝ, γ = fun s => (ybar, 0, s) := ⟨_, rfl⟩
  have hγd : ∀ s, HasDerivAt γ (0, 0, 1) s := fun s => by
    rw [hγ]
    exact (hasDerivAt_const s ybar).prodMk ((hasDerivAt_const s (0 : X)).prodMk (hasDerivAt_id s))
  have hγ0 : γ 0 = pbar ybar := by rw [hγ]; rfl
  have hγt : Tendsto γ (𝓝 0) (𝓝 (pbar ybar)) := hγ0 ▸ (hγd 0).continuousAt.tendsto
  have hφ : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s => policy ψ (γ s))
      (fderiv ℝ (policy ψ) (γ s) (0, 0, 1)) s := by
    filter_upwards [hγt.eventually hgev] with s hs
    exact hs.comp_hasDerivAt s (hγd s)
  have hF : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar))
      (γ 0) := by rw [hγ0]; exact hgF1
  have hφ1 : HasDerivAt (fun s => fderiv ℝ (policy ψ) (γ s) (0, 0, 1))
      (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) 0 :=
    (ContinuousLinearMap.apply ℝ Y ((0, 0, 1) : Y × X × ℝ)).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (hF.comp_hasDerivAt (0 : ℝ) (hγd 0))
  have h := taylor_two_isLittleO hφ hφ1
  rw [hγ] at h
  simp only at h
  have h0 : policy ψ (ybar, (0 : X), (0 : ℝ)) = ybar := by
    change ψ (pbar ybar) [] = ybar
    rw [hψ.base]
    rfl
  have h1 : fderiv ℝ (policy ψ) (ybar, (0 : X), (0 : ℝ)) (0, 0, 1) = 0 := hce
  simp only [h0, h1, smul_zero, sub_zero] at h
  exact h

/-! ## Smoothness of `f` near the steady state only

The results above assume `f` of class `Cᵏ` on the whole space. Since only arguments near the
steady state matter, it suffices that `f` be `Cᵏ` at the steady state: a smooth bump cut-off
`f̃ = χ f` (equal to `f` near `z̄`, `Cᵏ` everywhere) has the same local equilibria, the same
linearisation and the same second derivative at `z̄` (cf. the cut-off of the Chapter 2 project,
module `LocalIFT`). -/

variable (M) in
/-- Woodford (2003), App. A.3, p. 631 (the cut-off of the period condition): the model with
`f̃ = χ f`, `χ` a smooth bump equal to one on the ball of radius `r/4` about `z̄` and zero
outside the ball of radius `r/2`, and the same exogenous structure. -/
noncomputable def cutoffModel [FiniteDimensional ℝ E] (ybar : Y) (r : ℝ) (hr : 0 < r) :
    Model J Y Z X E where
  f := fun z => (⟨r / 4, r / 2, by positivity, by linarith⟩ :
    ContDiffBump (zbar ybar : Y × Y × Y × X × E)) z • M.f z
  prob := M.prob
  shock := M.shock
  Λ := M.Λ
  η := M.η

omit [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] in
/-- Woodford (2003), App. A.3: the cut-off agrees with `f` within `r/4` of the steady state. -/
theorem cutoff_f_eq [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ E]
    {ybar : Y} {r : ℝ} (hr : 0 < r) {z : Y × Y × Y × X × E} (hz : dist z (zbar ybar) ≤ r / 4) :
    (M.cutoffModel ybar r hr).f z = M.f z := by
  change (⟨r / 4, r / 2, by positivity, by linarith⟩ :
    ContDiffBump (zbar ybar : Y × Y × Y × X × E)) z • M.f z = M.f z
  rw [ContDiffBump.one_of_mem_closedBall _ (Metric.mem_closedBall.2 hz), one_smul]

omit [Fintype J] in
/-- Woodford (2003), App. A.3: the cut-off agrees with `f` on a neighbourhood of `z̄`. -/
theorem cutoff_eventuallyEq [FiniteDimensional ℝ E] {ybar : Y} {r : ℝ} (hr : 0 < r) :
    (M.cutoffModel ybar r hr).f =ᶠ[𝓝 (zbar ybar)] M.f := by
  filter_upwards [Metric.ball_mem_nhds (zbar ybar : Y × Y × Y × X × E)
    (by positivity : 0 < r / 4)] with z hz
  exact cutoff_f_eq hr (Metric.mem_ball.1 hz).le

omit [Fintype J] in
/-- Woodford (2003), App. A.3: if `f` is `Cᵏ` within `r` of `z̄`, the cut-off is `Cᵏ` on the whole
space. -/
theorem contDiff_cutoff [FiniteDimensional ℝ E] {ybar : Y} {r : ℝ} (hr : 0 < r) {k : ℕ}
    (hF : ∀ z, dist z (zbar ybar) < r → ContDiffAt ℝ k M.f z) :
    ContDiff ℝ k (M.cutoffModel ybar r hr).f := by
  set φ : ContDiffBump (zbar ybar : Y × Y × Y × X × E) :=
    ⟨r / 4, r / 2, by positivity, by linarith⟩ with hφ
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  by_cases hz : dist z (zbar ybar) < r
  · exact φ.contDiffAt.smul (hF z hz)
  · have hnot : z ∉ tsupport φ := by
      rw [φ.tsupport_eq, Metric.mem_closedBall]
      have : φ.rOut = r / 2 := rfl
      rw [this]
      push Not at hz ⊢
      linarith
    have hev : (M.cutoffModel ybar r hr).f =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnot] with q hq
      change φ q • M.f q = 0
      rw [hq, Pi.zero_apply, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

omit [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] in
/-- Woodford (2003), App. A.3: a function `Cᵏ` at `z̄` is `Cᵏ` on a ball around it. -/
theorem exists_ball_contDiffAt {ybar : Y} {k : ℕ} (hf : ContDiffAt ℝ k M.f (zbar ybar)) :
    ∃ r > 0, ∀ z, dist z (zbar ybar) < r → ContDiffAt ℝ k M.f z := by
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.mp (hf.eventually (by simp))
  exact ⟨r, hr, fun z hz => h hz⟩

/-- Woodford (2003), App. A.3: the cut-off model satisfies the standing assumptions. -/
theorem std_cutoff [FiniteDimensional ℝ E] (hM : M.Std) {ybar : Y} {r : ℝ} (hr : 0 < r) :
    (M.cutoffModel ybar r hr).Std :=
  ⟨hM.prob_nonneg, hM.prob_sum, hM.norm_Λ_lt⟩

omit [Fintype J] in
/-- Woodford (2003), App. A.3: the cut-off model has the same exogenous state. -/
theorem stateAt_cutoff [FiniteDimensional ℝ E] {ybar : Y} {r : ℝ} (hr : 0 < r) (x : X)
    (σ : ℝ) (n : List J) : (M.cutoffModel ybar r hr).stateAt x σ n = M.stateAt x σ n := by
  induction n with
  | nil => rfl
  | cons j n ih =>
    rw [stateAt_cons, stateAt_cons, ih]
    rfl

omit [Fintype J] in
/-- Woodford (2003), App. A.3: the cut-off model has the same arguments of `F`. -/
theorem point_cutoff [FiniteDimensional ℝ E] {ybar : Y} {r : ℝ} (hr : 0 < r) (u : List J → Y)
    (p : Y × X × ℝ) (n : List J) : (M.cutoffModel ybar r hr).point u p n = M.point u p n := by
  simp only [point, stateAt_cutoff]

/-- Woodford (2003), App. A.3: the cut-off model has the same argument map `pointL`. -/
theorem pointL_cutoff [FiniteDimensional ℝ E] (hM : M.Std) {ybar : Y} {r : ℝ} (hr : 0 < r) :
    (M.cutoffModel ybar r hr).pointL (std_cutoff hM hr) = M.pointL hM :=
  ContinuousLinearMap.ext fun q => lp.ext (funext fun n => by
    simp only [pointL_apply, point_cutoff])

/-- Woodford (2003), App. A.3: the cut-off and the original `F` agree near `w̄`. -/
theorem bigF_cutoff_eventuallyEq [FiniteDimensional ℝ E] {ybar : Y} {r : ℝ} (hr : 0 < r) :
    (M.cutoffModel ybar r hr).bigF =ᶠ[𝓝 (wbar ybar)] M.bigF := by
  have hev : ∀ j, ∀ᶠ w in 𝓝 (wbar ybar), (M.cutoffModel ybar r hr).f (M.ell j w) =
      M.f (M.ell j w) := fun j => by
    have ht : Tendsto (M.ell j) (𝓝 (wbar ybar)) (𝓝 (zbar ybar)) := by
      have := (M.ell j).continuous.tendsto (wbar ybar)
      rwa [ell_wbar] at this
    exact ht.eventually (cutoff_eventuallyEq hr)
  filter_upwards [Filter.eventually_all.2 hev] with w hw
  exact Finset.sum_congr rfl fun j _ => by
    change M.prob j • (M.cutoffModel ybar r hr).f (M.ell j w) = M.prob j • M.f (M.ell j w)
    rw [hw j]

/-- Woodford (2003), App. A.3: the cut-off has the same linearised operator. -/
theorem linOp_cutoff [FiniteDimensional ℝ E] (hM : M.Std) {ybar : Y} {r : ℝ} (hr : 0 < r) :
    (M.cutoffModel ybar r hr).linOp (std_cutoff hM hr) ybar = M.linOp hM ybar := by
  have e := (bigF_cutoff_eventuallyEq (M := M) (ybar := ybar) hr).fderiv_eq (𝕜 := ℝ)
  simp only [linOp, e, pointL_cutoff hM hr]

omit [Fintype J] in
/-- Woodford (2003), App. A.3: the cut-off has the same first and second derivatives at `z̄`. -/
theorem fderiv_cutoff [FiniteDimensional ℝ E] {ybar : Y} {r : ℝ} (hr : 0 < r) :
    fderiv ℝ (M.cutoffModel ybar r hr).f (zbar ybar) = fderiv ℝ M.f (zbar ybar) ∧
      fderiv ℝ (fderiv ℝ (M.cutoffModel ybar r hr).f) (zbar ybar) =
        fderiv ℝ (fderiv ℝ M.f) (zbar ybar) :=
  ⟨(cutoff_eventuallyEq hr).fderiv_eq, (cutoff_eventuallyEq hr).fderiv.fderiv_eq⟩

/-- Woodford (2003), App. A.3: near the steady state the cut-off model and the original model
have the same solutions. -/
theorem solves_cutoff_iff [FiniteDimensional ℝ E] (hM : M.Std) {ybar : Y} {r : ℝ}
    (hr : 0 < r) : ∃ ρ > 0, ∀ (p : Y × X × ℝ) (u : Bd (List J) Y), dist p (pbar ybar) < ρ →
      dist u (constBd ybar) < ρ → ((M.cutoffModel ybar r hr).Solves u p ↔ M.Solves u p) := by
  set K : ℝ := (∑ j, ‖M.ell j‖) * ‖M.pointL hM‖ + 1 with hK
  have hK0 : 0 < K := by
    have : 0 ≤ (∑ j, ‖M.ell j‖) * ‖M.pointL hM‖ :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (norm_nonneg _)
    linarith
  refine ⟨r / 4 / K, by positivity, fun p u hp hu => ?_⟩
  have hq : ‖((p - pbar ybar, u - constBd ybar) : (Y × X × ℝ) × Bd (List J) Y)‖ < r / 4 / K := by
    rw [Prod.norm_def, ← dist_eq_norm, ← dist_eq_norm]
    exact max_lt hp hu
  have hpt : ∀ n, M.point u p n - wbar ybar =
      M.pointL hM (p - pbar ybar, u - constBd ybar) n := fun n => by
    have h2 : M.pointL hM (p - pbar ybar, u - constBd ybar) n =
        M.pointL hM (p, u) n - M.pointL hM (pbar ybar, constBd ybar) n := by
      rw [← Prod.mk_sub_mk, map_sub, lp.coeFn_sub, Pi.sub_apply]
    rw [h2, pointL_bar hM ybar, constBd_apply]
    rfl
  have hclose : ∀ n j, dist (M.ell j (M.point u p n)) (zbar ybar) ≤ r / 4 := fun n j => by
    rw [← ell_wbar (M := M) ybar j, dist_eq_norm, ← map_sub, hpt n]
    calc ‖M.ell j (M.pointL hM (p - pbar ybar, u - constBd ybar) n)‖
        ≤ ‖M.ell j‖ * (‖M.pointL hM‖ * ‖((p - pbar ybar, u - constBd ybar) :
          (Y × X × ℝ) × Bd (List J) Y)‖) :=
          (M.ell j).le_opNorm_of_le ((norm_apply_le _ n).trans ((M.pointL hM).le_opNorm _))
      _ ≤ K * (r / 4 / K) := by
          have hj : ‖M.ell j‖ ≤ ∑ j, ‖M.ell j‖ :=
            Finset.single_le_sum (f := fun j => ‖M.ell j‖) (fun _ _ => norm_nonneg _)
              (Finset.mem_univ j)
          have hn := norm_nonneg ((p - pbar ybar, u - constBd ybar) :
            (Y × X × ℝ) × Bd (List J) Y)
          have hP := norm_nonneg (M.pointL hM)
          calc ‖M.ell j‖ * (‖M.pointL hM‖ * ‖((p - pbar ybar, u - constBd ybar) :
                (Y × X × ℝ) × Bd (List J) Y)‖)
              ≤ (∑ j, ‖M.ell j‖) * (‖M.pointL hM‖ * (r / 4 / K)) :=
                mul_le_mul hj (mul_le_mul_of_nonneg_left hq.le hP) (by positivity)
                  (Finset.sum_nonneg fun _ _ => norm_nonneg _)
            _ ≤ K * (r / 4 / K) := by
                rw [← mul_assoc]
                exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = r / 4 := by field_simp
  have hF : ∀ n, (M.cutoffModel ybar r hr).bigF (M.point u p n) = M.bigF (M.point u p n) :=
    fun n => Finset.sum_congr rfl fun j _ => by
      change M.prob j • (M.cutoffModel ybar r hr).f (M.ell j (M.point u p n)) =
        M.prob j • M.f (M.ell j (M.point u p n))
      rw [cutoff_f_eq hr (hclose n j)]
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · have := h n
    rw [point_cutoff, hF n] at this
    exact this
  · rw [point_cutoff, hF n]
    exact h n

/-- Woodford (2003), App. A.3: the local equilibria of the cut-off model and of the original
model coincide. -/
theorem localSol_cutoff_iff [FiniteDimensional ℝ E] (hM : M.Std) {ybar : Y} {r : ℝ}
    (hr : 0 < r) {ψ : Y × X × ℝ → Bd (List J) Y} :
    (M.cutoffModel ybar r hr).LocalSol ybar ψ ↔ M.LocalSol ybar ψ := by
  obtain ⟨ρ, hρ, hiff⟩ := solves_cutoff_iff hM hr (ybar := ybar)
  have key : ∀ {N N' : Model J Y Z X E}, (∀ (p : Y × X × ℝ) (u : Bd (List J) Y),
      dist p (pbar ybar) < ρ → dist u (constBd ybar) < ρ → (N.Solves u p ↔ N'.Solves u p)) →
      N.LocalSol ybar ψ → N'.LocalSol ybar ψ := fun {N N'} h hψ => by
    obtain ⟨δ, hδ, huniq⟩ := hψ.unique
    have hball : ∀ᶠ p in 𝓝 (pbar ybar), dist (ψ p) (constBd ybar) < ρ := by
      have := hψ.cont.tendsto
      rw [hψ.base] at this
      exact this (Metric.ball_mem_nhds _ hρ)
    refine ⟨hψ.base, hψ.cont, ?_, ⟨min δ ρ, lt_min hδ hρ, fun p u hp hu hs => ?_⟩⟩
    · filter_upwards [hψ.solves, hball, Metric.ball_mem_nhds (pbar ybar) hρ] with p hs hd hp
      exact (h p (ψ p) hp hd).1 hs
    · exact huniq p u (lt_of_lt_of_le hp (min_le_left _ _)) (lt_of_lt_of_le hu (min_le_left _ _))
        ((h p u (lt_of_lt_of_le hp (min_le_right _ _))
          (lt_of_lt_of_le hu (min_le_right _ _))).2 hs)
  exact ⟨key hiff, key fun p u hp hu => (hiff p u hp hu).symm⟩

/-- Woodford (2003), App. A.3 and E.2 (**existence, local uniqueness and `Cᵏ` dependence on the
shock scale with `f` smooth only near the steady state**): as `exists_smooth_solution`, assuming
only that `f` is `Cᵏ` at `z̄` (`k ≥ 1`). -/
theorem exists_smooth_solution_local [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E]
    (hM : M.Std) {k : ℕ} (hk : 1 ≤ k) {ybar : Y} (hf : ContDiffAt ℝ k M.f (zbar ybar))
    (hss : M.f (zbar ybar) = 0) (hdet : (M.linOp hM ybar).IsInvertible) :
    ∃ ψ : Y × X × ℝ → Bd (List J) Y, M.LocalSol ybar ψ ∧ ContDiffAt ℝ k ψ (pbar ybar) := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt hf
  have hss' : (M.cutoffModel ybar r hr).f (zbar ybar) = 0 := by
    rw [cutoff_f_eq hr (by rw [dist_self]; positivity), hss]
  have hdet' : ((M.cutoffModel ybar r hr).linOp (std_cutoff hM hr) ybar).IsInvertible := by
    rw [linOp_cutoff hM hr]
    exact hdet
  obtain ⟨ψ, hψ, hc⟩ := exists_smooth_solution (std_cutoff hM hr) hk (contDiff_cutoff hr hball)
    hss' hdet'
  exact ⟨ψ, (localSol_cutoff_iff hM hr).1 hψ, hc⟩

/-- Woodford (2003), App. E.2 (**certainty equivalence with `f` smooth only near the steady
state**): as `certainty_equivalence`, assuming only that `f` is `C¹` at `z̄`. -/
theorem certainty_equivalence_local [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E]
    (hM : M.Std) {ybar : Y} (hf : ContDiffAt ℝ 1 M.f (zbar ybar))
    {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ)
    {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y} (hψd : HasFDerivAt ψ ψ' (pbar ybar))
    {g' : Y × X × ℝ →L[ℝ] Y} (hg : HasFDerivAt (policy ψ) g' (pbar ybar))
    (hmean : ∑ j, M.prob j • M.shock j = 0)
    (hinj : Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar)) : g' (0, 0, 1) = 0 := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt (M := M) (ybar := ybar) (k := 1)
    (by exact_mod_cast hf)
  have hD := (fderiv_cutoff (M := M) hr (ybar := ybar)).1
  have hinj' : Function.Injective ((M.cutoffModel ybar r hr).dA ybar +
      (M.cutoffModel ybar r hr).dB ybar + (M.cutoffModel ybar r hr).dC ybar) := by
    simp only [dA, dB, dC, hD]
    exact hinj
  exact certainty_equivalence (std_cutoff hM hr)
    (by exact_mod_cast contDiff_cutoff (M := M) hr hball)
    ((localSol_cutoff_iff hM hr).2 hψ) hψd hg hmean hinj'

/-- Woodford (2003), App. E.2 (**the `σ²` correction with `f` smooth only near the steady
state**): as `second_order_sigma`, assuming only that `f` is `C²` at `z̄`. -/
theorem second_order_sigma_local [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E] (hM : M.Std)
    {ybar : Y} (hf : ContDiffAt ℝ 2 M.f (zbar ybar)) {ψ : Y × X × ℝ → Bd (List J) Y}
    (hψ : M.LocalSol ybar ψ) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (hmean : ∑ j, M.prob j • M.shock j = 0)
    (hinj : Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar)) :
    M.dA ybar (fderiv ℝ (policy ψ) (pbar ybar)
        (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1), 0, 0)) +
      M.dA ybar (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      M.dB ybar (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) +
      ∑ j, M.prob j • (M.dA ybar (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar)
          (0, M.η (M.shock j), 0) (0, M.η (M.shock j), 0)) +
        fderiv ℝ (fderiv ℝ M.f) (zbar ybar)
          (fderiv ℝ (policy ψ) (pbar ybar) (0, M.η (M.shock j), 0), 0, 0, 0, M.shock j)
          (fderiv ℝ (policy ψ) (pbar ybar) (0, M.η (M.shock j), 0), 0, 0, 0, M.shock j)) =
      0 := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt (M := M) (ybar := ybar) (k := 2)
    (by exact_mod_cast hf)
  obtain ⟨hD, hD2⟩ := fderiv_cutoff (M := M) hr (ybar := ybar)
  have hinj' : Function.Injective ((M.cutoffModel ybar r hr).dA ybar +
      (M.cutoffModel ybar r hr).dB ybar + (M.cutoffModel ybar r hr).dC ybar) := by
    simp only [dA, dB, dC, hD]
    exact hinj
  have h := second_order_sigma (std_cutoff hM hr)
    (by exact_mod_cast contDiff_cutoff (M := M) hr hball)
    ((localSol_cutoff_iff hM hr).2 hψ) hψ2 hmean hinj'
  simp only [dA, dB, hD, hD2] at h
  exact h

/-- Woodford (2003), App. E.2 (**the decision rule to second order in `σ`, `f` smooth only near
the steady state**): as `policy_sigma_expansion`, assuming only that `f` is `C²` at `z̄`. -/
theorem policy_sigma_expansion_local [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E]
    (hM : M.Std) {ybar : Y} (hf : ContDiffAt ℝ 2 M.f (zbar ybar))
    {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (hmean : ∑ j, M.prob j • M.shock j = 0)
    (hinj : Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar)) :
    (fun σ : ℝ => policy ψ (ybar, 0, σ) - ybar -
      (σ ^ 2 / 2) • fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, 0, 1) (0, 0, 1)) =o[𝓝 0]
      fun σ => σ ^ 2 := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt (M := M) (ybar := ybar) (k := 2)
    (by exact_mod_cast hf)
  have hD := (fderiv_cutoff (M := M) hr (ybar := ybar)).1
  have hinj' : Function.Injective ((M.cutoffModel ybar r hr).dA ybar +
      (M.cutoffModel ybar r hr).dB ybar + (M.cutoffModel ybar r hr).dC ybar) := by
    simp only [dA, dB, dC, hD]
    exact hinj
  exact policy_sigma_expansion (std_cutoff hM hr)
    (by exact_mod_cast contDiff_cutoff (M := M) hr hball)
    ((localSol_cutoff_iff hM hr).2 hψ) hψ2 hmean hinj'

/-! ## An illustration: a nonlinear forward-looking condition with a risk term -/

/-- Woodford (2003), Ch. 3–4 (an illustrative instance of the class): the exact forward-looking
condition `π_t = β E_t π_{t+1} + γ E_t π_{t+1}² + κ x_t`, with an exogenous AR(1) state
`x_{t+1} = ρ x_t + σ ε_{t+1}`, `ε = ±1` with probability `1/2` each. -/
noncomputable def exModel (β γ κ ρ : ℝ) : Model Bool ℝ ℝ ℝ ℝ where
  f := fun z => z.2.1 - β * z.1 - γ * z.1 ^ 2 - κ * z.2.2.2.1
  prob := fun _ => 1 / 2
  shock := fun b => if b then 1 else -1
  Λ := ρ • ContinuousLinearMap.id ℝ ℝ
  η := ContinuousLinearMap.id ℝ ℝ

/-- Woodford (2003), the illustration: the standing assumptions hold for `|ρ| < 1`. -/
theorem exModel_std {β γ κ ρ : ℝ} (hρ : |ρ| < 1) : (exModel β γ κ ρ).Std where
  prob_nonneg := fun _ => by norm_num [exModel]
  prob_sum := by norm_num [exModel]
  norm_Λ_lt := by
    simp only [exModel, norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]
    exact hρ

/-- Woodford (2003), the illustration: the period condition is `C^∞`. -/
theorem exModel_contDiff (β γ κ ρ : ℝ) {k : ℕ∞ω} : ContDiff ℝ k (exModel β γ κ ρ).f := by
  simp only [exModel]
  fun_prop

/-- Woodford (2003), the illustration: the innovations have mean zero. -/
theorem exModel_mean (β γ κ ρ : ℝ) :
    ∑ j, (exModel β γ κ ρ).prob j • (exModel β γ κ ρ).shock j = 0 := by
  simp [exModel]

/-- Woodford (2003), the illustration: directional derivatives of `f` at the steady state, computed
along lines. -/
theorem exModel_fderiv (β γ κ ρ : ℝ) (v : ℝ × ℝ × ℝ × ℝ × ℝ) :
    fderiv ℝ (exModel β γ κ ρ).f (zbar 0) v = v.2.1 - β * v.1 - κ * v.2.2.2.1 := by
  have hd : HasFDerivAt (exModel β γ κ ρ).f (fderiv ℝ (exModel β γ κ ρ).f (zbar 0)) (zbar 0) :=
    ((exModel_contDiff β γ κ ρ (k := 1)).differentiable one_ne_zero _).hasFDerivAt
  have hl : HasDerivAt (fun a : ℝ => zbar 0 + a • v) v 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (zbar 0)).congr_deriv (one_smul ℝ v)
  have hd' : HasFDerivAt (exModel β γ κ ρ).f (fderiv ℝ (exModel β γ κ ρ).f (zbar 0))
      ((fun a : ℝ => zbar 0 + a • v) 0) := by
    simp only [zero_smul, add_zero]
    exact hd
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hl
  have e : ((exModel β γ κ ρ).f ∘ fun a : ℝ => zbar 0 + a • v) =
      fun a => a * (v.2.1 - β * v.1 - κ * v.2.2.2.1) - γ * (a * v.1) ^ 2 := by
    funext a
    simp only [Function.comp, exModel, zbar, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    ring
  rw [e] at h1
  have h2 : HasDerivAt (fun a : ℝ => a * (v.2.1 - β * v.1 - κ * v.2.2.2.1) - γ * (a * v.1) ^ 2)
      (v.2.1 - β * v.1 - κ * v.2.2.2.1) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (v.2.1 - β * v.1 - κ * v.2.2.2.1)).sub
      ((((hasDerivAt_id (0 : ℝ)).mul_const v.1).pow 2).const_mul γ)
    convert this using 1
    · funext a
      simp
    · simp
  exact h1.unique h2

/-- Woodford (2003), the illustration (**determinacy, exactly**): the linearised operator is
`h ↦ −β E_t h_{t+1} + h_t`, invertible on `ℓ∞` iff `|β| < 1`. -/
theorem exModel_det {β γ κ ρ : ℝ} (hρ : |ρ| < 1) (hβ : |β| < 1) :
    ((exModel β γ κ ρ).linOp (exModel_std hρ) 0).IsInvertible := by
  have hf := exModel_contDiff β γ κ ρ (k := 1)
  have hC : (exModel β γ κ ρ).dC 0 = 0 := by
    ext
    simp [dC, exModel_fderiv]
  rw [isInvertible_linOp_scalar_iff (exModel_std hρ) hf hC]
  simp [dA, dB, exModel_fderiv, hβ]

/-- Woodford (2003), the illustration (**smooth policy and certainty equivalence**): for `|β| < 1`,
`|ρ| < 1` and every `k ≥ 1` there is a local equilibrium policy, `Cᵏ` jointly in
`(π_{−1}, x, σ)` at the steady state, with `g_σ = 0`. -/
theorem exModel_policy {β γ κ ρ : ℝ} (hρ : |ρ| < 1) (hβ : |β| < 1) {k : ℕ} (hk : 1 ≤ k) :
    ∃ ψ : ℝ × ℝ × ℝ → Bd (List Bool) ℝ, (exModel β γ κ ρ).LocalSol 0 ψ ∧
      ContDiffAt ℝ k ψ (pbar 0) ∧ fderiv ℝ (policy ψ) (pbar 0) (0, 0, 1) = 0 := by
  have hf := exModel_contDiff β γ κ ρ (k := k)
  have hss : (exModel β γ κ ρ).f (zbar 0) = 0 := by simp [exModel, zbar]
  obtain ⟨ψ, hψ, hc⟩ := exists_smooth_solution (exModel_std hρ) hk hf hss (exModel_det hρ hβ)
  refine ⟨ψ, hψ, hc, ?_⟩
  have hk0 : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (pbar 0)) (pbar 0) := (hc.differentiableAt hk0).hasFDerivAt
  have hgd : HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) (pbar 0)) (pbar 0) :=
    (((evalL ℝ []).contDiff.contDiffAt.comp (pbar 0) hc).differentiableAt hk0).hasFDerivAt
  have hinj : Function.Injective ((exModel β γ κ ρ).dA 0 + (exModel β γ κ ρ).dB 0 +
      (exModel β γ κ ρ).dC 0) := by
    intro a b hab
    have h1 : (1 - β) * a = (1 - β) * b := by
      have h := hab
      simp [dA, dB, dC, exModel_fderiv] at h
      linarith
    have hβ1 : 1 - β ≠ 0 := by
      have := (abs_lt.1 hβ).2
      linarith
    exact mul_left_cancel₀ hβ1 h1
  exact certainty_equivalence (exModel_std hρ) (hf.of_le (by exact_mod_cast hk)) hψ hψd hgd
    (exModel_mean β γ κ ρ) hinj

end Model

end Woodford.StabilizationWelfare.SmoothInSigma
