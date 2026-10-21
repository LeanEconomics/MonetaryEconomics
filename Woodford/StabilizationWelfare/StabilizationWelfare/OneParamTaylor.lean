/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Taylor

/-!
# The one-parameter Taylor bridge for second-order welfare approximations

Woodford (2003), *Interest and Prices*, Chapter 6, §1 "Approximation of Loss Functions and
Optimal Policies", pp. 383–392 (eqs. (1.1)–(1.8)), in the one-parameter ("perturbation-ε")
form recommended for the whole chapter.

Woodford's second-order welfare approximations take a smooth welfare function `U` along an
equilibrium that depends on the size of the disturbances. Indexing everything by a scalar `ε`
(the amplitude of the shocks, of the distortions and of the policy deviations) gives a curve
`γ : ℝ → E` of equilibrium outcomes and the welfare along it, `W ε = U (γ ε)`. This module
proves the analytic facts the chapter relies on.

* Second-order Taylor expansion with a cubic remainder in `ε`, as an `IsBigO` at `𝓝 0`:
  `taylor2_isBigO_of_lipschitz` (second derivative Lipschitz at the base point),
  `taylor2_isBigO_of_bounded_third` (bounded third derivative near the base point) and
  `taylor2_isBigO_of_contDiff` (`C³`). With only `C²` the remainder is merely `o(ε²)`
  (`taylor2_isLittleO_of_continuousAt`, `taylor2_isLittleO_of_contDiff_two`), and this cannot
  be improved: `not_taylor2_isBigO_of_contDiff_two` exhibits a `C²` function whose remainder
  is not `O(ε³)` (the point of survey error 19 on Woodford's eq. (1.2)).
* The second derivative of a composite along a curve, `W'' = D²U(γ′, γ′) + DU(γ″)`
  (`hasDerivAt_comp_curve`, `deriv_comp_curve`, `deriv_deriv_comp_curve`), and the cubic
  expansion of `U ∘ γ` (`taylor2_comp_curve`).
* The structural lemma behind eqs. (1.5)–(1.6): when `DU` vanishes at the base point (in the
  direction of the curve's acceleration), `W''(0)` depends only on `γ′(0)` and not on `γ″(0)`
  (`secondDeriv_indep_of_accel`, `secondDeriv_eq_of_firstOrder_eq`), and its parametrised form
  for eqs. (1.7)–(1.8), where the curve also moves a vector of structural parameters
  (`secondDeriv_param_curve`, `secondDeriv_param_curve_indep`).
* The welfare-ranking corollary: if two policies' quadratic losses satisfy `L_A < L_B`, then
  policy `A` gives strictly higher welfare for every small enough `ε ≠ 0`
  (`welfare_ranking`, `welfare_ranking_pos`, `welfare_ranking_of_loss`), with a general
  filter version (`eventually_lt_of_quadratic_gap`).
* Expectations over a finite state space commute with `d/dε` and preserve cubic remainders
  (`expect`, `hasDerivAt_expect`, `deriv_expect`, `isBigO_expect`, `taylor2_expect`).
* Order bookkeeping shared by the whole chapter: `pow_succ_isBigO_self`, `bigO_mul`,
  `bigO_weaken`, `isBigO_cube_of_scaling` (the Layer-A scaling lemma), `not_isBigO_linear`,
  `sq_not_isBigO_cube`, and the first-order Taylor bound `taylor_one_bigO`.
-/

namespace Woodford.StabilizationWelfare.OneParamTaylor

open Filter Topology Asymptotics

/-! ## The one-dimensional second-order Taylor bound -/

/-- Woodford (2003), eq. (1.2), p. 385 (the analytic core): if `f′ = f1`, `f1′ = f2` on the
closed ball of radius `r` about `0`, and `|f2 x − f2 0| ≤ C` there, then the second-order
Taylor remainder at `0` satisfies `|f ε − (f 0 + ε f1 0 + ε²/2 f2 0)| ≤ C ε²` for `|ε| ≤ r`. -/
theorem taylor2_remainder_le {f f1 f2 : ℝ → ℝ} {r C : ℝ}
    (hf : ∀ x ∈ Metric.closedBall (0 : ℝ) r, HasDerivAt f (f1 x) x)
    (hf1 : ∀ x ∈ Metric.closedBall (0 : ℝ) r, HasDerivAt f1 (f2 x) x)
    (hC : ∀ x ∈ Metric.closedBall (0 : ℝ) r, |f2 x - f2 0| ≤ C) {ε : ℝ} (hε : |ε| ≤ r) :
    |f ε - (f 0 + ε * f1 0 + ε ^ 2 / 2 * f2 0)| ≤ C * ε ^ 2 := by
  have hr : 0 ≤ r := (abs_nonneg ε).trans hε
  have h0 : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) r := Metric.mem_closedBall_self hr
  have hC0 : 0 ≤ C := by simpa using hC 0 h0
  have hh : ∀ x ∈ Metric.closedBall (0 : ℝ) r, |f1 x - f1 0 - x * f2 0| ≤ C * |x| := by
    intro x hx
    have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => f1 y - f1 0 - y * f2 0) (f' := fun y => f2 y - f2 0)
      (s := Metric.closedBall 0 r) (C := C) (fun y hy => ?_) (fun y hy => ?_)
      (convex_closedBall 0 r) h0 hx
    · simpa [Real.norm_eq_abs] using key
    · have h1 := HasDerivAt.sub ((hf1 y hy).sub_const (f1 0))
        ((hasDerivAt_id y).mul_const (f2 0))
      exact (h1.congr_deriv (by simp)).hasDerivWithinAt
    · simpa [Real.norm_eq_abs] using hC y hy
  have hsub : Metric.closedBall (0 : ℝ) |ε| ⊆ Metric.closedBall (0 : ℝ) r :=
    Metric.closedBall_subset_closedBall hε
  have h0' : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) |ε| := Metric.mem_closedBall_self (abs_nonneg ε)
  have hε' : ε ∈ Metric.closedBall (0 : ℝ) |ε| := by simp
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y => f y - (f 0 + y * f1 0 + y ^ 2 / 2 * f2 0))
    (f' := fun y => f1 y - f1 0 - y * f2 0)
    (s := Metric.closedBall 0 |ε|) (C := C * |ε|) (fun y hy => ?_) (fun y hy => ?_)
    (convex_closedBall 0 |ε|) h0' hε'
  · have e : |ε| * |ε| = ε ^ 2 := by rw [abs_mul_abs_self, sq]
    simpa [Real.norm_eq_abs, mul_assoc, e] using key
  · have h1 := HasDerivAt.sub (hf y (hsub hy))
      (HasDerivAt.add (HasDerivAt.add (hasDerivAt_const y (f 0))
        ((hasDerivAt_id y).mul_const (f1 0)))
        (((hasDerivAt_pow 2 y).div_const 2).mul_const (f2 0)))
    refine (h1.congr_deriv ?_).hasDerivWithinAt
    simp only [Nat.cast_ofNat]
    ring
  · have hy' : |y| ≤ |ε| := by simpa using hy
    calc ‖f1 y - f1 0 - y * f2 0‖ ≤ C * |y| := by
          simpa [Real.norm_eq_abs] using hh y (hsub hy)
      _ ≤ C * |ε| := mul_le_mul_of_nonneg_left hy' hC0

/-- Three neighbourhood conditions at `0` hold together on some closed ball of positive
radius (a bookkeeping lemma for the Taylor theorems of Woodford (2003), §1, p. 385). -/
theorem exists_closedBall_of_eventually {p q s : ℝ → Prop} (hp : ∀ᶠ x in 𝓝 0, p x)
    (hq : ∀ᶠ x in 𝓝 0, q x) (hs : ∀ᶠ x in 𝓝 0, s x) :
    ∃ r > 0, ∀ x ∈ Metric.closedBall (0 : ℝ) r, p x ∧ q x ∧ s x := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (hp.and (hq.and hs))
  refine ⟨δ / 2, half_pos hδ, fun x hx => h ?_⟩
  have : dist x 0 ≤ δ / 2 := hx
  linarith

/-- Woodford (2003), eq. (1.2), p. 385, with the regularity it needs: if `f` is twice
differentiable near `0` and its second derivative is Lipschitz at `0`
(`|f2 x − f2 0| ≤ L |x|`), the second-order Taylor remainder is `O(ε³)` as `ε → 0`. -/
theorem taylor2_isBigO_of_lipschitz {f f1 f2 : ℝ → ℝ} {L : ℝ}
    (hf : ∀ᶠ x in 𝓝 0, HasDerivAt f (f1 x) x) (hf1 : ∀ᶠ x in 𝓝 0, HasDerivAt f1 (f2 x) x)
    (hL : ∀ᶠ x in 𝓝 0, |f2 x - f2 0| ≤ L * |x|) :
    (fun ε => f ε - (f 0 + ε * f1 0 + ε ^ 2 / 2 * f2 0)) =O[𝓝 0] (fun ε => ε ^ 3) := by
  obtain ⟨r, hr, h⟩ := exists_closedBall_of_eventually hf hf1 hL
  refine IsBigO.of_bound |L| ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hr] with ε hε
  have hεr : |ε| ≤ r := by simpa using hε
  have hsub : Metric.closedBall (0 : ℝ) |ε| ⊆ Metric.closedBall (0 : ℝ) r :=
    Metric.closedBall_subset_closedBall hεr
  have key := taylor2_remainder_le (r := |ε|) (C := |L| * |ε|)
    (fun x hx => (h x (hsub hx)).1) (fun x hx => (h x (hsub hx)).2.1)
    (fun x hx => ?_) le_rfl
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    calc _ ≤ |L| * |ε| * ε ^ 2 := key
      _ = |L| * |ε| ^ 3 := by rw [← sq_abs ε]; ring
  · have hx' : |x| ≤ |ε| := by simpa using hx
    calc |f2 x - f2 0| ≤ L * |x| := (h x (hsub hx)).2.2
      _ ≤ |L| * |x| := mul_le_mul_of_nonneg_right (le_abs_self L) (abs_nonneg x)
      _ ≤ |L| * |ε| := mul_le_mul_of_nonneg_left hx' (abs_nonneg L)

/-- Woodford (2003), eq. (1.2), p. 385, under a bounded third derivative: if `f`, `f1 = f′`,
`f2 = f″` have derivatives `f1`, `f2`, `f3` near `0` and `|f3| ≤ M` there, the second-order
Taylor remainder is `O(ε³)`. -/
theorem taylor2_isBigO_of_bounded_third {f f1 f2 f3 : ℝ → ℝ} {M : ℝ}
    (hf : ∀ᶠ x in 𝓝 0, HasDerivAt f (f1 x) x) (hf1 : ∀ᶠ x in 𝓝 0, HasDerivAt f1 (f2 x) x)
    (hf2 : ∀ᶠ x in 𝓝 0, HasDerivAt f2 (f3 x) x) (hM : ∀ᶠ x in 𝓝 0, |f3 x| ≤ M) :
    (fun ε => f ε - (f 0 + ε * f1 0 + ε ^ 2 / 2 * f2 0)) =O[𝓝 0] (fun ε => ε ^ 3) := by
  refine taylor2_isBigO_of_lipschitz (L := M) hf hf1 ?_
  obtain ⟨r, hr, h⟩ := exists_closedBall_of_eventually hf2 hM hM
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hr] with x hx
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f2) (f' := f3)
    (s := Metric.closedBall 0 r) (C := M) (fun y hy => (h y hy).1.hasDerivWithinAt)
    (fun y hy => by simpa [Real.norm_eq_abs] using (h y hy).2.1) (convex_closedBall 0 r)
    (Metric.mem_closedBall_self hr.le) hx
  simpa [Real.norm_eq_abs] using key

/-- Woodford (2003), eq. (1.2), p. 385, for a `C³` function: the second-order Taylor remainder
`f ε − (f 0 + ε f′(0) + ε²/2 f″(0))` is `O(ε³)` as `ε → 0`. -/
theorem taylor2_isBigO_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) :
    (fun ε => f ε - (f 0 + ε * deriv f 0 + ε ^ 2 / 2 * deriv (deriv f) 0)) =O[𝓝 0]
      (fun ε => ε ^ 3) := by
  have h2 : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have h1 : ContDiff ℝ 1 (deriv (deriv f)) := h2.deriv'
  have hc : Continuous (deriv (deriv (deriv f))) := h1.continuous_deriv le_rfl
  have hb : ∀ᶠ x in 𝓝 0, |deriv (deriv (deriv f)) x| ≤ |deriv (deriv (deriv f)) 0| + 1 := by
    have := (hc.tendsto 0).eventually (Metric.closedBall_mem_nhds _ zero_lt_one)
    filter_upwards [this] with x hx
    have hx' : |deriv (deriv (deriv f)) x - deriv (deriv (deriv f)) 0| ≤ 1 := by
      simpa [Real.dist_eq] using hx
    have := abs_sub_abs_le_abs_sub (deriv (deriv (deriv f)) x) (deriv (deriv (deriv f)) 0)
    linarith
  refine taylor2_isBigO_of_bounded_third
    (Eventually.of_forall fun x => (hf.differentiable (by norm_num) x).hasDerivAt)
    (Eventually.of_forall fun x => (h2.differentiable (by norm_num) x).hasDerivAt)
    (Eventually.of_forall fun x => (h1.differentiable (by norm_num) x).hasDerivAt) hb

/-- Woodford (2003), eq. (1.2), p. 385, with only twice-differentiability (survey error 19):
if `f″` exists near `0` and is continuous at `0`, the second-order Taylor remainder is `o(ε²)`
— the honest order when only `C²` is assumed. -/
theorem taylor2_isLittleO_of_continuousAt {f f1 f2 : ℝ → ℝ}
    (hf : ∀ᶠ x in 𝓝 0, HasDerivAt f (f1 x) x) (hf1 : ∀ᶠ x in 𝓝 0, HasDerivAt f1 (f2 x) x)
    (hc : ContinuousAt f2 0) :
    (fun ε => f ε - (f 0 + ε * f1 0 + ε ^ 2 / 2 * f2 0)) =o[𝓝 0] (fun ε => ε ^ 2) := by
  refine isLittleO_iff.2 fun c hc0 => ?_
  have hcl : ∀ᶠ x in 𝓝 0, |f2 x - f2 0| ≤ c := by
    have := hc.eventually (Metric.closedBall_mem_nhds _ hc0)
    filter_upwards [this] with x hx
    simpa [Real.dist_eq] using hx
  obtain ⟨r, hr, h⟩ := exists_closedBall_of_eventually hf hf1 hcl
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hr] with ε hε
  have hεr : |ε| ≤ r := by simpa using hε
  have key := taylor2_remainder_le (fun x hx => (h x hx).1) (fun x hx => (h x hx).2.1)
    (fun x hx => (h x hx).2.2) hεr
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
  exact key

/-- Woodford (2003), eq. (1.2), p. 385, for a `C²` function: the second-order Taylor remainder
is `o(ε²)` (survey error 19: this is all that "at least twice differentiable" gives). -/
theorem taylor2_isLittleO_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (fun ε => f ε - (f 0 + ε * deriv f 0 + ε ^ 2 / 2 * deriv (deriv f) 0)) =o[𝓝 0]
      (fun ε => ε ^ 2) := by
  have h1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  exact taylor2_isLittleO_of_continuousAt
    (Eventually.of_forall fun x => (hf.differentiable (by norm_num) x).hasDerivAt)
    (Eventually.of_forall fun x => (h1.differentiable (by norm_num) x).hasDerivAt)
    (h1.continuous_deriv le_rfl).continuousAt

/-- The counterexample function `x ↦ x ^ (5/2)` (real power; it vanishes for `x ≤ 0`) used
against an `O(ε³)` remainder for merely `C²` functions (Woodford (2003), eq. (1.2), p. 385). -/
noncomputable def rpowFiveHalves (x : ℝ) : ℝ := x ^ ((5 : ℝ) / 2)

/-- Woodford (2003), eq. (1.2), p. 385: `x ↦ x ^ (5/2)` is `C²` on `ℝ`. -/
theorem rpowFiveHalves_contDiff : ContDiff ℝ 2 rpowFiveHalves := by
  have := Real.contDiff_rpow_const_of_le (p := (5 : ℝ) / 2) (n := 2) (by norm_num)
  exact_mod_cast this

/-- Woodford (2003), eq. (1.2), p. 385: the value, first and second derivatives of
`x ↦ x ^ (5/2)` at `0` all vanish. -/
theorem rpowFiveHalves_derivs :
    rpowFiveHalves 0 = 0 ∧ deriv rpowFiveHalves 0 = 0 ∧ deriv (deriv rpowFiveHalves) 0 = 0 := by
  have hd : deriv rpowFiveHalves = fun x => (5 : ℝ) / 2 * x ^ ((5 : ℝ) / 2 - 1) :=
    Real.deriv_rpow_const' _
  refine ⟨by simp [rpowFiveHalves], ?_, ?_⟩
  · rw [hd]
    simp only
    rw [Real.zero_rpow (by norm_num)]
    simp
  · rw [hd, deriv_const_mul _ ((Real.differentiable_rpow_const (by norm_num)) 0),
      Real.deriv_rpow_const, Real.zero_rpow (by norm_num)]
    simp

/-- Woodford (2003), eq. (1.2), p. 385 (survey error 19, counterexample): a `C²` function whose
second-order Taylor remainder at `0` is NOT `O(ε³)`. So "at least twice differentiable" does not
justify the printed `O(‖ϕ, ξ‖³)` residual; `C³` (or a Lipschitz second derivative) is needed. -/
theorem not_taylor2_isBigO_of_contDiff_two :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧
      ¬ (fun ε => f ε - (f 0 + ε * deriv f 0 + ε ^ 2 / 2 * deriv (deriv f) 0)) =O[𝓝 0]
        (fun ε => ε ^ 3) := by
  refine ⟨rpowFiveHalves, rpowFiveHalves_contDiff, fun H => ?_⟩
  obtain ⟨h0, h1, h2⟩ := rpowFiveHalves_derivs
  have H' : rpowFiveHalves =O[𝓝[>] 0] (fun ε : ℝ => ε ^ 3) := by
    refine (H.mono nhdsWithin_le_nhds).congr_left fun ε => ?_
    simp [h0, h1, h2]
  have ht : Tendsto (fun ε : ℝ => ε ^ ((1 : ℝ) / 2)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_rpow_const (q := (1 : ℝ) / 2) (by norm_num)).tendsto 0
    rw [Real.zero_rpow (by norm_num)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlo : (fun ε : ℝ => ε ^ 3) =o[𝓝[>] 0] rpowFiveHalves := by
    have := ((isLittleO_one_iff ℝ).2 ht).mul_isBigO (isBigO_refl rpowFiveHalves (𝓝[>] 0))
    refine this.congr' ?_ (Eventually.of_forall fun ε => by simp)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    simp only [rpowFiveHalves]
    rw [← Real.rpow_add hε', ← Real.rpow_natCast]
    norm_num
  refine hlo.not_isBigO ?_ H'
  refine (Eventually.frequently ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact pow_ne_zero 3 (ne_of_gt hε)

/-! ## The second derivative of a composite along a curve -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Woodford (2003), §1, pp. 385–389 (the chain rule behind eqs. (1.5)–(1.8)): for welfare
`W s = U (γ s)` along a curve, `W′ s = DU(γ s)(γ′ s)` near `t`, and
`W″ t = D²U(γ t)(γ′ t, γ′ t) + DU(γ t)(γ″ t)`. Here `U1 = DU`, `U2 = D²U(γ t)`, `γ1 = γ′` and
`γ2 = γ″ t`. -/
theorem hasDerivAt_comp_curve {U : E → ℝ} {U1 : E → E →L[ℝ] ℝ} {U2 : E →L[ℝ] E →L[ℝ] ℝ}
    {γ γ1 : ℝ → E} {γ2 : E} {t : ℝ}
    (hU : ∀ᶠ x in 𝓝 (γ t), HasFDerivAt U (U1 x) x) (hU1 : HasFDerivAt U1 U2 (γ t))
    (hγ : ∀ᶠ s in 𝓝 t, HasDerivAt γ (γ1 s) s) (hγ1 : HasDerivAt γ1 γ2 t) :
    (∀ᶠ s in 𝓝 t, HasDerivAt (fun s => U (γ s)) (U1 (γ s) (γ1 s)) s) ∧
      HasDerivAt (fun s => U1 (γ s) (γ1 s)) (U2 (γ1 t) (γ1 t) + U1 (γ t) γ2) t := by
  have hct : ContinuousAt γ t := hγ.self_of_nhds.continuousAt
  refine ⟨?_, ?_⟩
  · filter_upwards [hγ, hct.tendsto.eventually hU] with s h1 h2
    exact h2.comp_hasDerivAt s h1
  · exact (hU1.comp_hasDerivAt t hγ.self_of_nhds).clm_apply hγ1

/-- Woodford (2003), §1, pp. 385–389: for differentiable `U` and `γ`, the derivative of welfare
along the curve is `W′ s = DU(γ s)(γ′ s)`. -/
theorem deriv_comp_curve {U : E → ℝ} {γ : ℝ → E} (hU : Differentiable ℝ U)
    (hγ : Differentiable ℝ γ) :
    deriv (fun s => U (γ s)) = fun s => fderiv ℝ U (γ s) (deriv γ s) :=
  funext fun s => ((hU (γ s)).hasFDerivAt.comp_hasDerivAt s (hγ s).hasDerivAt).deriv

/-- Woodford (2003), §1, pp. 385–389: for `C²` `U` and `γ`, the second derivative of welfare
along the curve is `W″ t = D²U(γ t)(γ′ t, γ′ t) + DU(γ t)(γ″ t)`. -/
theorem deriv_deriv_comp_curve {U : E → ℝ} {γ : ℝ → E} (hU : ContDiff ℝ 2 U)
    (hγ : ContDiff ℝ 2 γ) (t : ℝ) :
    deriv (deriv (fun s => U (γ s))) t =
      fderiv ℝ (fderiv ℝ U) (γ t) (deriv γ t) (deriv γ t) +
        fderiv ℝ U (γ t) (deriv (deriv γ) t) := by
  rw [deriv_comp_curve (hU.differentiable (by norm_num)) (hγ.differentiable (by norm_num))]
  have hU1 : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hγ1 : ContDiff ℝ 1 (deriv γ) := hγ.deriv'
  exact (hasDerivAt_comp_curve (U1 := fderiv ℝ U)
    (Eventually.of_forall fun x => (hU.differentiable (by norm_num) x).hasFDerivAt)
    ((hU1.differentiable (by norm_num) (γ t)).hasFDerivAt)
    (Eventually.of_forall fun s => (hγ.differentiable (by norm_num) s).hasDerivAt)
    ((hγ1.differentiable (by norm_num) t).hasDerivAt)).2.deriv

/-- Woodford (2003), eq. (1.2), p. 385, in one-parameter form (survey §4, Layer B1): for `C³`
`U` and `γ`, welfare along the curve satisfies
`U(γ ε) = U(γ 0) + ε DU(γ′) + ε²/2 [D²U(γ′, γ′) + DU(γ″)] + O(ε³)`. -/
theorem taylor2_comp_curve {U : E → ℝ} {γ : ℝ → E} (hU : ContDiff ℝ 3 U)
    (hγ : ContDiff ℝ 3 γ) :
    (fun ε => U (γ ε) - (U (γ 0) + ε * fderiv ℝ U (γ 0) (deriv γ 0) +
      ε ^ 2 / 2 * (fderiv ℝ (fderiv ℝ U) (γ 0) (deriv γ 0) (deriv γ 0) +
        fderiv ℝ U (γ 0) (deriv (deriv γ) 0)))) =O[𝓝 0] (fun ε => ε ^ 3) := by
  have h := taylor2_isBigO_of_contDiff (hU.comp hγ)
  have h1 : deriv (fun s => U (γ s)) 0 = fderiv ℝ U (γ 0) (deriv γ 0) := by
    rw [deriv_comp_curve (hU.differentiable (by norm_num)) (hγ.differentiable (by norm_num))]
  have h2 := deriv_deriv_comp_curve (hU.of_le (by norm_num)) (hγ.of_le (by norm_num)) 0
  have e : (U ∘ γ) = fun s => U (γ s) := rfl
  rw [e, h2, h1] at h
  exact h

/-! ## When the gradient vanishes, `W″(0)` depends only on the first-order curve -/

/-- Woodford (2003), eqs. (1.5)–(1.6), pp. 386–387 (key structural lemma): if the gradient `DU`
at the base point annihilates the curve's acceleration `γ″ t` — in particular if
`U_x(x̄; 0) = 0` — then `W″ t = D²U(γ′ t, γ′ t)`, which involves only the first-order
(linear) solution `γ′ t` and not the second-order term `γ″ t`. -/
theorem secondDeriv_indep_of_accel {U : E → ℝ} {U1 : E → E →L[ℝ] ℝ}
    {U2 : E →L[ℝ] E →L[ℝ] ℝ} {γ γ1 : ℝ → E} {γ2 : E} {t : ℝ}
    (hU : ∀ᶠ x in 𝓝 (γ t), HasFDerivAt U (U1 x) x) (hU1 : HasFDerivAt U1 U2 (γ t))
    (hγ : ∀ᶠ s in 𝓝 t, HasDerivAt γ (γ1 s) s) (hγ1 : HasDerivAt γ1 γ2 t)
    (h0 : U1 (γ t) γ2 = 0) :
    HasDerivAt (fun s => U1 (γ s) (γ1 s)) (U2 (γ1 t) (γ1 t)) t := by
  simpa [h0] using (hasDerivAt_comp_curve hU hU1 hγ hγ1).2

/-- Woodford (2003), eqs. (1.5)–(1.6), pp. 386–387: two equilibrium curves that agree to first
order at `t` (same `γ t`, same `γ′ t`) but have arbitrary, different second-order terms give
welfare with the SAME second derivative `D²U(γ′ t, γ′ t)`, provided the gradient vanishes at the
base point (`U_x(x̄; 0) = 0`). Hence the linear solution suffices for a second-order welfare
ranking. -/
theorem secondDeriv_eq_of_firstOrder_eq {U : E → ℝ} {U1 : E → E →L[ℝ] ℝ}
    {U2 : E →L[ℝ] E →L[ℝ] ℝ} {γ γ1 δ δ1 : ℝ → E} {γ2 δ2 : E} {t : ℝ}
    (hU : ∀ᶠ x in 𝓝 (γ t), HasFDerivAt U (U1 x) x) (hU1 : HasFDerivAt U1 U2 (γ t))
    (hγ : ∀ᶠ s in 𝓝 t, HasDerivAt γ (γ1 s) s) (hγ1 : HasDerivAt γ1 γ2 t)
    (hδ : ∀ᶠ s in 𝓝 t, HasDerivAt δ (δ1 s) s) (hδ1 : HasDerivAt δ1 δ2 t)
    (hpos : δ t = γ t) (hvel : δ1 t = γ1 t) (h0 : U1 (γ t) = 0) :
    HasDerivAt (fun s => U1 (γ s) (γ1 s)) (U2 (γ1 t) (γ1 t)) t ∧
      HasDerivAt (fun s => U1 (δ s) (δ1 s)) (U2 (γ1 t) (γ1 t)) t := by
  refine ⟨secondDeriv_indep_of_accel hU hU1 hγ hγ1 (by simp [h0]), ?_⟩
  rw [← hpos] at hU hU1 h0
  rw [← hvel]
  exact secondDeriv_indep_of_accel hU hU1 hδ hδ1 (by simp [h0])

variable {P X : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Woodford (2003), eqs. (1.7)–(1.8), p. 389, in one-parameter form: welfare
`W ε = U(ε φ1, x ε)` when the curve also moves a vector of structural parameters
(`Φ = ε φ1`, e.g. the steady-state distortion) linearly. Then
`W″(0) = D²U((φ1, x′ 0), (φ1, x′ 0)) + U_x(x̄; 0)(x″ 0)`. -/
theorem secondDeriv_param_curve {U : P × X → ℝ} {U1 : P × X → (P × X) →L[ℝ] ℝ}
    {U2 : (P × X) →L[ℝ] (P × X) →L[ℝ] ℝ} {φ1 : P} {x x1 : ℝ → X} {x2 : X}
    (hU : ∀ᶠ z in 𝓝 ((0 : P), x 0), HasFDerivAt U (U1 z) z)
    (hU1 : HasFDerivAt U1 U2 ((0 : P), x 0))
    (hx : ∀ᶠ s in 𝓝 0, HasDerivAt x (x1 s) s) (hx1 : HasDerivAt x1 x2 0) :
    (∀ᶠ s in 𝓝 0, HasDerivAt (fun s : ℝ => U (s • φ1, x s)) (U1 (s • φ1, x s) (φ1, x1 s)) s) ∧
      HasDerivAt (fun s : ℝ => U1 (s • φ1, x s) (φ1, x1 s))
        (U2 (φ1, x1 0) (φ1, x1 0) + U1 ((0 : P), x 0) ((0 : P), x2)) 0 := by
  have e : ((0 : ℝ) • φ1, x 0) = ((0 : P), x 0) := by simp
  rw [← e] at hU hU1
  have hγ : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s : ℝ => (s • φ1, x s)) (φ1, x1 s) s := by
    filter_upwards [hx] with s hs
    simpa using ((hasDerivAt_id s).smul_const φ1).prodMk hs
  have hγ1 : HasDerivAt (fun s : ℝ => (φ1, x1 s)) ((0 : P), x2) 0 :=
    (hasDerivAt_const (0 : ℝ) φ1).prodMk hx1
  have key := hasDerivAt_comp_curve (γ := fun s : ℝ => (s • φ1, x s))
    (γ1 := fun s : ℝ => (φ1, x1 s)) hU hU1 hγ hγ1
  rw [e] at key
  exact key

/-- Woodford (2003), eqs. (1.7)–(1.8), p. 389: if the gradient in the endogenous variables
vanishes at the undistorted base point, `U_x(x̄; 0) = 0` (equivalently, `U_x(x̄; Φ) = O(Φ)`),
then along `ε ↦ (ε φ1, x ε)` the second derivative of welfare is `D²U((φ1, x′ 0), (φ1, x′ 0))`:
it involves the cross derivative `U_xΦ` but never the second-order solution `x″ 0`. -/
theorem secondDeriv_param_curve_indep {U : P × X → ℝ} {U1 : P × X → (P × X) →L[ℝ] ℝ}
    {U2 : (P × X) →L[ℝ] (P × X) →L[ℝ] ℝ} {φ1 : P} {x x1 : ℝ → X} {x2 : X}
    (hU : ∀ᶠ z in 𝓝 ((0 : P), x 0), HasFDerivAt U (U1 z) z)
    (hU1 : HasFDerivAt U1 U2 ((0 : P), x 0))
    (hx : ∀ᶠ s in 𝓝 0, HasDerivAt x (x1 s) s) (hx1 : HasDerivAt x1 x2 0)
    (hUx : (U1 ((0 : P), x 0)).comp (ContinuousLinearMap.inr ℝ P X) = 0) :
    HasDerivAt (fun s : ℝ => U1 (s • φ1, x s) (φ1, x1 s)) (U2 (φ1, x1 0) (φ1, x1 0)) 0 := by
  have h0 : U1 ((0 : P), x 0) ((0 : P), x2) = 0 := by
    simpa using congrArg (fun L => L x2) hUx
  simpa [h0] using (secondDeriv_param_curve hU hU1 hx hx1).2

/-! ## The welfare-ranking corollary -/

/-- Woodford (2003), §1, pp. 386–389 (the use made of a second-order approximation), general
filter form: if `W_A − W_B − q = O(s³)` where the quadratic gap satisfies `q ≥ c s²` with
`c > 0`, `s → 0` and `s ≠ 0` eventually, then `W_B < W_A` eventually. -/
theorem eventually_lt_of_quadratic_gap {α : Type*} {l : Filter α} {s WA WB q : α → ℝ} {c : ℝ}
    (hs : Tendsto s l (𝓝 0)) (hc : 0 < c) (hq : ∀ᶠ a in l, c * s a ^ 2 ≤ q a)
    (hne : ∀ᶠ a in l, s a ≠ 0) (hR : (fun a => WA a - WB a - q a) =O[l] (fun a => s a ^ 3)) :
    ∀ᶠ a in l, WB a < WA a := by
  have h3 : (fun a => s a ^ 3) =o[l] (fun a => s a ^ 2) := by
    have := ((isLittleO_one_iff ℝ).2 hs).mul_isBigO (isBigO_refl (fun a => s a ^ 2) l)
    refine this.congr' (Eventually.of_forall fun a => by simp only; ring)
      (Eventually.of_forall fun a => by simp)
  have hlo := hR.trans_isLittleO h3
  filter_upwards [isLittleO_iff.1 hlo (half_pos hc), hq, hne] with a ha hqa hna
  have hp : 0 < s a ^ 2 := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at ha
  have := neg_abs_le (WA a - WB a - q a)
  nlinarith

/-- Woodford (2003), §1, pp. 386–389 (welfare ranking, one-parameter form): if welfare under
policies `A` and `B` has expansions `w0 + ε w1 + ε²/2 a_X + O(ε³)` with common zeroth- and
first-order terms and `a_B < a_A`, then `A` is strictly better for every small `ε ≠ 0`. -/
theorem welfare_ranking {WA WB : ℝ → ℝ} {w0 w1 aA aB : ℝ}
    (hA : (fun ε => WA ε - (w0 + ε * w1 + ε ^ 2 / 2 * aA)) =O[𝓝 0] (fun ε => ε ^ 3))
    (hB : (fun ε => WB ε - (w0 + ε * w1 + ε ^ 2 / 2 * aB)) =O[𝓝 0] (fun ε => ε ^ 3))
    (h : aB < aA) : ∀ᶠ ε in 𝓝[≠] 0, WB ε < WA ε := by
  refine eventually_lt_of_quadratic_gap (s := id) (q := fun ε => ε ^ 2 / 2 * (aA - aB))
    (c := (aA - aB) / 2) (tendsto_id.mono_left nhdsWithin_le_nhds) (by linarith)
    (Eventually.of_forall fun ε => by simp only [id]; nlinarith [sq_nonneg ε])
    self_mem_nhdsWithin ?_
  refine ((hA.sub hB).mono nhdsWithin_le_nhds).congr_left fun ε => ?_
  ring

/-- Woodford (2003), §1, pp. 386–389: the welfare ranking for small positive amplitudes,
`∀ᶠ ε in 𝓝[>] 0` (the shock amplitude `ε` is a positive number). -/
theorem welfare_ranking_pos {WA WB : ℝ → ℝ} {w0 w1 aA aB : ℝ}
    (hA : (fun ε => WA ε - (w0 + ε * w1 + ε ^ 2 / 2 * aA)) =O[𝓝 0] (fun ε => ε ^ 3))
    (hB : (fun ε => WB ε - (w0 + ε * w1 + ε ^ 2 / 2 * aB)) =O[𝓝 0] (fun ε => ε ^ 3))
    (h : aB < aA) : ∀ᶠ ε in 𝓝[>] 0, WB ε < WA ε :=
  (welfare_ranking hA hB h).filter_mono (nhdsWithin_mono _ fun _ hε => ne_of_gt hε)

/-- Woodford (2003), §1, pp. 386–389, and §2 (quadratic loss functions): if welfare under each
policy is `w0 + ε w1 − (k/2) ε² L_X + O(ε³)` with `k > 0` (e.g. `k = Ȳ u_c`) and the
quadratic losses satisfy `L_A < L_B`, then `W_A ε > W_B ε` for all small `ε > 0`. -/
theorem welfare_ranking_of_loss {WA WB : ℝ → ℝ} {w0 w1 k LA LB : ℝ} (hk : 0 < k)
    (hA : (fun ε => WA ε - (w0 + ε * w1 + ε ^ 2 / 2 * (-(k * LA)))) =O[𝓝 0] (fun ε => ε ^ 3))
    (hB : (fun ε => WB ε - (w0 + ε * w1 + ε ^ 2 / 2 * (-(k * LB)))) =O[𝓝 0] (fun ε => ε ^ 3))
    (hL : LA < LB) : ∀ᶠ ε in 𝓝[>] 0, WB ε < WA ε :=
  welfare_ranking_pos hA hB (by nlinarith)

/-! ## Expectations over a finite state space -/

variable {Ω : Type*} [Fintype Ω] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Woodford (2003), §1, p. 385: the expectation `E[f] = ∑_ω p ω • f ω` of a (vector-valued)
random variable on a finite state space with probabilities `p`. -/
def expect (p : Ω → ℝ) (f : Ω → V) : V := ∑ ω, p ω • f ω

/-- Woodford (2003), §1, p. 385: expectation is additive. -/
theorem expect_add (p : Ω → ℝ) (f g : Ω → V) :
    expect p (fun ω => f ω + g ω) = expect p f + expect p g := by
  simp [expect, smul_add, Finset.sum_add_distrib]

/-- Woodford (2003), §1, p. 385: expectation commutes with subtraction. -/
theorem expect_sub (p : Ω → ℝ) (f g : Ω → V) :
    expect p (fun ω => f ω - g ω) = expect p f - expect p g := by
  simp [expect, smul_sub, Finset.sum_sub_distrib]

/-- Woodford (2003), §1, p. 385: expectation is homogeneous. -/
theorem expect_smul (p : Ω → ℝ) (c : ℝ) (f : Ω → V) :
    expect p (fun ω => c • f ω) = c • expect p f := by
  simp [expect, Finset.smul_sum, smul_comm (p _) c]

/-- Woodford (2003), §1, p. 385: the expectation of a constant is that constant when the
probabilities sum to one. -/
theorem expect_const {p : Ω → ℝ} (hp : ∑ ω, p ω = 1) (v : V) : expect p (fun _ => v) = v := by
  simp [expect, ← Finset.sum_smul, hp]

/-- Woodford (2003), §1, p. 385: a continuous linear map commutes with expectation
(`U_x E[x̃] = E[U_x x̃]`). -/
theorem map_expect {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W)
    (p : Ω → ℝ) (f : Ω → V) : L (expect p f) = expect p (fun ω => L (f ω)) := by
  simp [expect, map_sum, map_smul]

/-- Woodford (2003), §1, p. 385 (survey §4, B1): over a finite state space, `d/dε` commutes with
expectation: `d/dε E[f(ε)] = E[f′(ε)]`. -/
theorem hasDerivAt_expect (p : Ω → ℝ) {f : Ω → ℝ → V} {f' : Ω → V} {ε : ℝ}
    (h : ∀ ω, HasDerivAt (f ω) (f' ω) ε) :
    HasDerivAt (fun s => expect p fun ω => f ω s) (expect p f') ε := by
  unfold expect
  exact HasDerivAt.fun_sum fun ω _ => (h ω).const_smul (p ω)

/-- Woodford (2003), §1, p. 385: `deriv` form of `hasDerivAt_expect`. -/
theorem deriv_expect (p : Ω → ℝ) {f : Ω → ℝ → V} {ε : ℝ}
    (h : ∀ ω, DifferentiableAt ℝ (f ω) ε) :
    deriv (fun s => expect p fun ω => f ω s) ε = expect p (fun ω => deriv (f ω) ε) :=
  (hasDerivAt_expect p fun ω => (h ω).hasDerivAt).deriv

/-- Woodford (2003), §1, p. 385: over a finite state space a remainder that is `O(g)` state by
state is `O(g)` in expectation. -/
theorem isBigO_expect {α : Type*} {l : Filter α} (p : Ω → ℝ) {f : Ω → α → V} {g : α → ℝ}
    (h : ∀ ω, f ω =O[l] g) : (fun a => expect p fun ω => f ω a) =O[l] g := by
  unfold expect
  have := IsBigO.sum (s := Finset.univ) fun ω _ => (h ω).const_smul_left (p ω)
  refine this.congr_left fun a => ?_
  simp

/-- Woodford (2003), eq. (1.3), p. 386, in one-parameter form: if welfare in every state has a
second-order expansion with cubic remainder, so does expected welfare, with coefficients the
expectations of the state-by-state coefficients. -/
theorem taylor2_expect (p : Ω → ℝ) {W : Ω → ℝ → ℝ} {w0 w1 a : Ω → ℝ}
    (h : ∀ ω, (fun ε => W ω ε - (w0 ω + ε * w1 ω + ε ^ 2 / 2 * a ω)) =O[𝓝 0]
      (fun ε => ε ^ 3)) :
    (fun ε => expect p (fun ω => W ω ε) -
      (expect p w0 + ε * expect p w1 + ε ^ 2 / 2 * expect p a)) =O[𝓝 0] (fun ε => ε ^ 3) := by
  refine (isBigO_expect p h).congr_left fun ε => ?_
  simp only [expect, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-! ## Order bookkeeping (`O(sⁿ)` along one-parameter families)

The orders of magnitude used throughout Chapter 6 (Woodford (2003), §1, p. 385; (2.10)–(2.11),
p. 395; App. E): products of orders, weakening, the scaling lemma that turns an exact identity
`f(s) = s³ Q(s)` into `f = O(s³)`, and the two non-examples (a first- or second-order term is
not `O(s³)`). -/

/-- Woodford (2003), App. E, p. 693 (bookkeeping of orders): a real function tending to `0`
dominates its own higher powers, `f^{n+1} = O(f)`. -/
theorem pow_succ_isBigO_self {α : Type*} {l : Filter α} {f : α → ℝ} (hf : Tendsto f l (𝓝 0))
    (n : ℕ) : (fun a => f a ^ (n + 1)) =O[l] f := by
  have h1 : (fun a => f a ^ n) =O[l] (fun _ => (1 : ℝ)) := (hf.pow n).isBigO_one ℝ
  refine (h1.mul (isBigO_refl f l)).congr (fun a => by ring) (fun a => by simp)

/-- Woodford (2003), (2.11), p. 395 (restated from the Galí Chapter 4 project): orders
multiply, `f = O(sᵃ)`, `g = O(sᵇ)`, `a + b = c` give `f g = O(sᶜ)`. -/
theorem bigO_mul {f g : ℝ → ℝ} {a b c : ℕ} (hf : f =O[𝓝 0] fun s => s ^ a)
    (hg : g =O[𝓝 0] fun s => s ^ b) (habc : a + b = c) :
    (fun s => f s * g s) =O[𝓝 0] fun s => s ^ c := by
  have := hf.mul hg
  rw [← habc]
  simpa [pow_add] using this

/-- Woodford (2003), (2.11), p. 395 (restated from the Galí Chapter 4 project):
`O(sᵇ) ⊆ O(sᵃ)` for `a ≤ b`. -/
theorem bigO_weaken {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) (hf : f =O[𝓝 0] fun s => s ^ b) :
    f =O[𝓝 0] fun s => s ^ a := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_pow_pow h).isBigO
  · rw [h]
    exact hf

/-- Woodford (2003), App. E (the Layer-A scaling lemmas): a function that is exactly `s³`
times a function continuous at `0` is `O(s³)`. -/
theorem isBigO_cube_of_scaling {f Q : ℝ → ℝ} (hf : ∀ s, f s = s ^ 3 * Q s)
    (hQ : ContinuousAt Q 0) : f =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : Q =O[𝓝 0] fun _ => (1 : ℝ) := hQ.tendsto.isBigO_one ℝ
  have h2 := (isBigO_refl (fun s : ℝ => s ^ 3) (𝓝 0)).mul h1
  simp only [mul_one] at h2
  exact h2.congr_left fun s => (hf s).symm

/-- Woodford (2003), (5.1), p. 455 (survey error 17): a nonzero linear function plus a
constant is not `O(s³)` at `0`. -/
theorem not_isBigO_linear {a : ℝ} (ha : a ≠ 0) (c : ℝ) :
    ¬ (fun s : ℝ => a * s + c) =O[𝓝 0] fun s => s ^ 3 := by
  intro h
  obtain ⟨C, hC⟩ := h.bound
  have h0 := hC.self_of_nhds
  simp only [mul_zero, zero_add, Real.norm_eq_abs, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, abs_zero] at h0
  have hc : c = 0 := abs_nonpos_iff.mp h0
  subst hc
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hC
  have ha' : 0 < |a| := abs_pos.mpr ha
  set s : ℝ := min (δ / 2) (min 1 (|a| / (|C| + 1))) with hs
  have hC1 : 0 < |C| + 1 := by positivity
  have hs0 : 0 < s := lt_min (by linarith) (lt_min one_pos (div_pos ha' hC1))
  have hs1 : s ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hs2 : s ≤ |a| / (|C| + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hs3 : s * (|C| + 1) ≤ |a| := by rwa [le_div_iff₀ hC1] at hs2
  have hsd : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs0]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hb := hball hsd
  simp only [add_zero, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hs0] at hb
  have hb' : |a| * s ≤ |C| * s ^ 3 := hb.trans (by
    have := le_abs_self C
    have : 0 ≤ s ^ 3 := by positivity
    nlinarith)
  have hs2' : 0 < s ^ 2 := by positivity
  have e1 : s * (s * (|C| + 1)) ≤ s * |a| := mul_le_mul_of_nonneg_left hs3 hs0.le
  have e2 : |C| * s ^ 3 ≤ |C| * s ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs0.le hs1 (by norm_num)) (abs_nonneg C)
  have e3 : s * (s * (|C| + 1)) = |C| * s ^ 2 + s ^ 2 := by ring
  have e4 : s * |a| = |a| * s := by ring
  linarith

/-- Woodford (2003), §1, footnote 7, p. 386: `a² ≠ O(a³)` as `a → 0`; a second-order term is
not a third-order residual. -/
theorem sq_not_isBigO_cube : ¬ (fun a : ℝ => a ^ 2) =O[𝓝 0] (fun a => a ^ 3) := by
  intro h
  have hlo : (fun a : ℝ => a ^ 3) =o[𝓝 0] (fun a => a ^ 2) := by
    have := ((isLittleO_one_iff ℝ).2 (tendsto_id : Tendsto (fun a : ℝ => a) (𝓝 0) (𝓝 0))).mul_isBigO
      (isBigO_refl (fun a : ℝ => a ^ 2) (𝓝 0))
    exact this.congr (fun a => by simp only [id]; ring) (fun a => by simp)
  refine hlo.not_isBigO ?_ h
  have : ∀ᶠ a in 𝓝[≠] (0 : ℝ), a ^ 3 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact pow_ne_zero 3 ha
  exact this.frequently.filter_mono nhdsWithin_le_nhds

/-- Woodford (2003), p. 394 (first-order Taylor expansion with a quadratic remainder,
adapted from the Galí Chapter 4 project's `taylor_two`): if `f` is `C²` near `x₀`, then
`f x − f x₀ − f'(x₀)(x − x₀) = O((x − x₀)²)`. -/
theorem taylor_one_bigO {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiffAt ℝ 2 f x₀) :
    (fun x => f x - f x₀ - deriv f x₀ * (x - x₀)) =O[𝓝 x₀] fun x => (x - x₀) ^ 2 := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hs : ContDiffOn ℝ 2 f (Metric.ball x₀ r) := hfU.mono hball
  have hT := taylor_isLittleO (convex_ball x₀ r) (Metric.mem_ball_self hr) hs
  rw [nhdsWithin_eq_nhds.2 (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] at hT
  have hx0 := Metric.mem_ball_self hr (x := x₀)
  have e1 := iteratedDerivWithin_of_isOpen (n := 1) (f := f) Metric.isOpen_ball hx0
  have e2 := iteratedDerivWithin_of_isOpen (n := 2) (f := f) Metric.isOpen_ball hx0
  have heq : (fun x => f x - f x₀ - deriv f x₀ * (x - x₀))
      = fun x => (f x - taylorWithinEval f 2 (Metric.ball x₀ r) x₀ x) +
        iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2 := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, e1, e2,
      iteratedDeriv_one, smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

end Woodford.StabilizationWelfare.OneParamTaylor
