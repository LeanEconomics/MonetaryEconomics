/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.Expectations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The household

Galí (2015), Chapter 2, §2.1 (pp. 18–22), footnotes 3–5, and Appendix 2.1 (p. 44).

Period utility (p. 20) is `U(C, N; Z) = ((C^{1−σ} − 1)/(1 − σ) − N^{1+φ}/(1+φ)) Z` for `σ ≠ 1`
and `(log C − N^{1+φ}/(1+φ)) Z` for `σ = 1` (`periodUtility`). The book allows `σ ≥ 0`; we use
`σ > 0` wherever concavity or `σ⁻¹` is needed (correction C2-1). Several results are restated
from the Chapter 3 project (`Gali/BasicNewKeynesianModel/Household.lean`).

## Main results

* Properties assumed on p. 18: `U_c > 0`, `U_cc ≤ 0`, `U_n ≤ 0`, `U_nn ≤ 0`, `U_cz > 0`,
  separability (p. 21) and `mrs_eq` (`−U_n/U_c = C^σ N^φ`, independent of `Z`).
* Eq. (4), general utility: `static_foc_general_necessary` (variational argument) and
  `static_foc_general_sufficient` (concave `U`), via the tangent-plane inequality
  `concave_le_tangent`. For the book's utility: `static_optimum_iff` (eq. (7)) and
  `labour_supply_log_iff` (eq. (9), exact).
* Eq. (5), general utility: `euler_general_necessary` (finitely many states) and
  `euler_general_sufficient` (any expectation system), `euler_general_ratio` (the printed form).
  For the book's utility under an abstract `ExpectationSystem`: `euler_necessary`,
  `euler_sufficient`, `eulerEq_ratio_form` (eq. (8)).
* The deterministic infinite-horizon problem (`Economy`, `Plan`, `Feasible`, `Optimal`, with
  the no-Ponzi condition (3) in market prices and the overtaking criterion, which needs no
  summability): `optimal_of_foc` (**sufficiency** of budget-binding, (7), (8) and the
  transversality condition (6)); `budgetBinds_of_optimal`, `staticFOC_of_optimal`,
  `eulerDet_of_optimal` (**necessity**, the perturbation arguments of pp. 19–20);
  `tvc_liminf_of_optimal` (the book's p. 20 argument: (3) cannot hold strictly at an optimum)
  and `tvc_of_optimal_of_tendsto` (if the limit in (6) exists it is zero); `optimal_iff`;
  `tsum_le_of_optimal`; `bookTVC_iff` (the book's `Λ_{0,T} B_T/P_T` form).
* Fn. 3: `tvc_of_zero_bonds`, `tvc_of_zero_bonds_stoch` (`B_t = 0` gives (3) and (6)).
* Eq. (10): `hasFDerivAt_eulerKernel` (the Taylor step of App. 2.1 as an exact Fréchet
  derivative at the steady state `i = ρ + π̄ + σγ`), `eulerMoment_family` and
  `hasDerivAt_log_eulerMoment_family` (exact derivative of the stochastic Euler residual),
  `linearisedEuler_eq_zero_iff` (that derivative vanishes iff (10) holds),
  `pf_eulerEq_imp_eulerLogLinear` (exact under perfect foresight).
* Fn. 5: `neg_log_le_inv_sub_one`, `discount_rate_gap`, `discount_rate_gap_isBigO`.
* Eq. (11): `MoneyDemand`, `moneyDemand_iff_price`.
-/

namespace Gali.ClassicalMonetaryModel.Household

open Filter Topology

/-! ### Period utility -/

/-- Galí (2015), p. 20: utility of consumption, `(C^{1−σ} − 1)/(1 − σ)` for `σ ≠ 1` and
`log C` for `σ = 1`. -/
noncomputable def utilC (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 20: disutility of labour `N^{1+φ}/(1+φ)`. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 20: period utility `U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z`. -/
noncomputable def periodUtility (σ φ C N Z : ℝ) : ℝ := (utilC σ C - disutilN φ N) * Z

/-- Galí (2015), eq. (7), p. 21: marginal utility of consumption, `u'(C) = C^{−σ}`, in both
the `σ ≠ 1` and the log case (restated from the Chapter 3 project). -/
theorem hasDerivAt_utilC (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (utilC σ) (C ^ (-σ)) C := by
  by_cases hσ : σ = 1
  · have hfun : utilC σ = Real.log := funext fun x => by simp [utilC, hσ]
    rw [hfun, hσ, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hC.ne'
  · have hfun : utilC σ = fun x => (x ^ (1 - σ) - 1) / (1 - σ) :=
      funext fun x => by simp [utilC, hσ]
    have hs : (1 : ℝ) - σ ≠ 0 := sub_ne_zero.2 (Ne.symm hσ)
    rw [hfun]
    refine (((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hC.ne')).sub_const 1).div_const
      (1 - σ)).congr_deriv ?_
    rw [show (1 : ℝ) - σ - 1 = -σ by ring]
    field_simp

/-- Galí (2015), eq. (7), p. 21: marginal disutility of labour, `N^φ` (restated from the
Chapter 3 project). -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 18: the marginal utility `U_c = C^{−σ} Z` (derivative in `C`). -/
theorem hasDerivAt_periodUtility_C (σ φ N Z : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (fun C' => periodUtility σ φ C' N Z) (C ^ (-σ) * Z) C := by
  unfold periodUtility
  exact ((hasDerivAt_utilC σ hC).sub_const (disutilN φ N)).mul_const Z

/-- Galí (2015), p. 18: the marginal disutility `U_n = −N^φ Z` (derivative in `N`). -/
theorem hasDerivAt_periodUtility_N (σ C Z : ℝ) {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' => periodUtility σ φ C N' Z) (-N ^ φ * Z) N := by
  unfold periodUtility
  have := ((hasDerivAt_disutilN hφ N).const_sub (utilC σ C)).mul_const Z
  simpa using this

/-- Galí (2015), p. 18: `U_c > 0` for `C > 0`, `Z > 0`. -/
theorem margUtilC_pos (σ : ℝ) {C Z : ℝ} (hC : 0 < C) (hZ : 0 < Z) : 0 < C ^ (-σ) * Z :=
  mul_pos (Real.rpow_pos_of_pos hC _) hZ

/-- Galí (2015), p. 18: `U_n ≤ 0` for `N ≥ 0`, `Z > 0`. -/
theorem margUtilN_nonpos (φ : ℝ) {N Z : ℝ} (hN : 0 ≤ N) (hZ : 0 < Z) : -N ^ φ * Z ≤ 0 := by
  have := Real.rpow_nonneg hN φ
  nlinarith

/-- Galí (2015), p. 18: `U_cc = −σ C^{−σ−1} Z ≤ 0` (`σ > 0`, `C > 0`, `Z > 0`). -/
theorem hasDerivAt_margUtilC {σ C Z : ℝ} (hσ : 0 < σ) (hC : 0 < C) (hZ : 0 < Z) :
    HasDerivAt (fun C' => C' ^ (-σ) * Z) (-σ * C ^ (-σ - 1) * Z) C ∧
      -σ * C ^ (-σ - 1) * Z ≤ 0 := by
  refine ⟨((Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hC.ne')).mul_const Z), ?_⟩
  have := Real.rpow_pos_of_pos hC (-σ - 1)
  have : 0 < σ * C ^ (-σ - 1) * Z := by positivity
  linarith

/-- Galí (2015), p. 18: `U_nn = −φ N^{φ−1} Z ≤ 0` (`φ ≥ 0`, `N > 0`, `Z > 0`). -/
theorem hasDerivAt_margUtilN {φ N Z : ℝ} (hφ : 0 ≤ φ) (hN : 0 < N) (hZ : 0 < Z) :
    HasDerivAt (fun N' => -N' ^ φ * Z) (-(φ * N ^ (φ - 1)) * Z) N ∧
      -(φ * N ^ (φ - 1)) * Z ≤ 0 := by
  refine ⟨((Real.hasDerivAt_rpow_const (p := φ) (Or.inl hN.ne')).neg.mul_const Z), ?_⟩
  have := Real.rpow_pos_of_pos hN (φ - 1)
  have : 0 ≤ φ * N ^ (φ - 1) * Z := by positivity
  linarith

/-- Galí (2015), p. 18: `U_cz = C^{−σ} > 0`: the preference shifter raises the marginal utility
of consumption. -/
theorem hasDerivAt_margUtilC_Z (σ : ℝ) {C : ℝ} (hC : 0 < C) (Z : ℝ) :
    HasDerivAt (fun Z' => C ^ (-σ) * Z') (C ^ (-σ)) Z ∧ 0 < C ^ (-σ) := by
  refine ⟨?_, Real.rpow_pos_of_pos hC _⟩
  simpa using (hasDerivAt_id Z).const_mul (C ^ (-σ))

/-- Galí (2015), p. 21 (separability, `U_cn = 0`): the marginal utility of consumption does not
depend on hours. -/
theorem hasDerivAt_margUtilC_N (σ C Z N : ℝ) :
    HasDerivAt (fun _ : ℝ => C ^ (-σ) * Z) 0 N :=
  hasDerivAt_const N _

/-- Galí (2015), p. 21: the intratemporal marginal rate of substitution
`−U_n/U_c = C^σ N^φ` does not depend on the preference shifter `Z`. -/
theorem mrs_eq (σ φ : ℝ) {C N Z : ℝ} (hC : 0 < C) (hZ : 0 < Z) :
    -(-N ^ φ * Z) / (C ^ (-σ) * Z) = C ^ σ * N ^ φ := by
  rw [Real.rpow_neg hC.le]
  have := (Real.rpow_pos_of_pos hC σ).ne'
  field_simp

/-- Galí (2015), p. 18 (`U_cc ≤ 0`): marginal utility `C^{−σ}` is nonincreasing for `σ > 0`
(restated from the Chapter 3 project). -/
theorem antitoneOn_margUtil {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun C : ℝ => C ^ (-σ)) (Set.Ioi 0) :=
  fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (Galí (2015), p. 18, concavity of utility; restated from the Chapter 3
project). -/
theorem le_tangent {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hcont : ContinuousOn f (Set.uIcc x y)) (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z)
    (hanti : AntitoneOn f' (Set.Ioi 0)) : f y ≤ f x + f' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_le hxy.le] at hcont) (fun z hz => hd z (hx.trans hz.1))
    have hle : f' c ≤ f' x := hanti hx (hx.trans hc.1) hc.1.le
    have hpos : 0 < y - x := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_ge hxy.le] at hcont) (fun z hz => hd z (lt_of_le_of_lt hy hz.1))
    have hle : f' x ≤ f' c := hanti (lt_of_le_of_lt hy hc.1) hx hc.2.le
    have hpos : 0 < x - y := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith

/-- Galí (2015), p. 18: the utility of consumption is concave for `σ > 0`, in the
tangent-line form `u(y) ≤ u(x) + x^{−σ}(y − x)` for `x, y > 0`. -/
theorem utilC_le_tangent {σ : ℝ} (hσ : 0 < σ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    utilC σ y ≤ utilC σ x + x ^ (-σ) * (y - x) := by
  refine le_tangent (f' := fun C => C ^ (-σ)) hx hy.le ?_ (fun z hz => hasDerivAt_utilC σ hz)
    (antitoneOn_margUtil hσ)
  intro z hz
  have hz0 : 0 < z := by
    rcases Set.mem_uIcc.1 hz with h | h
    · exact lt_of_lt_of_le hx h.1
    · exact lt_of_lt_of_le hy h.1
  exact (hasDerivAt_utilC σ hz0).continuousAt.continuousWithinAt

/-- Galí (2015), p. 18 (`U_c > 0`): the utility of consumption is strictly increasing,
`u(y) − u(x) ≥ y^{−σ}(y − x) > 0` for `0 < x < y`. -/
theorem utilC_strictMono {σ : ℝ} (hσ : 0 < σ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    utilC σ x < utilC σ y := by
  have hy : 0 < y := hx.trans hxy
  have h := utilC_le_tangent hσ hy hx
  have : 0 < y ^ (-σ) * (y - x) := mul_pos (Real.rpow_pos_of_pos hy _) (sub_pos.2 hxy)
  nlinarith

/-- Galí (2015), p. 18: the disutility of labour is convex for `φ ≥ 0`, in the tangent-line
form `v(x) + x^φ (y − x) ≤ v(y)` for `x > 0`, `y ≥ 0`. -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-! ### Concave functions lie below their tangent planes -/

/-- The tangent-plane inequality for a concave function with a Fréchet derivative, used for
the sufficiency of Galí's first-order conditions (2015, pp. 19–20): if `U` is concave on a
convex set `S` containing `x` and `y` and `HasFDerivAt U L x`, then `U y ≤ U x + L (y − x)`. -/
theorem concave_le_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {U : E → ℝ} {L : E →L[ℝ] ℝ} {x y : E} (hU : ConcaveOn ℝ S U) (hx : x ∈ S)
    (hy : y ∈ S) (hL : HasFDerivAt U L x) : U y ≤ U x + L (y - x) := by
  set h : ℝ → ℝ := fun s => U (x + s • (y - x)) with hh
  have hpath : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hd : HasDerivAt h (L (y - x)) 0 := by
    have hL' : HasFDerivAt U L (x + (0 : ℝ) • (y - x)) := by simpa using hL
    exact hL'.comp_hasDerivAt (0 : ℝ) hpath
  have hlim := hd.tendsto_slope_zero_right
  have hlow : ∀ᶠ s in 𝓝[>] (0 : ℝ), U y - U x ≤ s⁻¹ • (h (0 + s) - h 0) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    have hconc := hU.2 hx hy (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) hs.1.le
      (by ring : (1 - s) + s = 1)
    have heq : (1 - s) • x + s • y = x + s • (y - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq] at hconc
    simp only [hh, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ hs.1]
    simp only [smul_eq_mul] at hconc
    nlinarith
  have := ge_of_tendsto hlim hlow
  linarith

/-- The one-dimensional tangent-line inequality for a concave differentiable function:
`u y ≤ u x + u'(x)(y − x)` (used for Galí (2015), eq. (5), p. 19). -/
theorem concave_le_tangent_real {S : Set ℝ} {u : ℝ → ℝ} {u' x y : ℝ} (hU : ConcaveOn ℝ S u)
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt u u' x) : u y ≤ u x + u' * (y - x) := by
  have h := concave_le_tangent hU hx hy hd.hasFDerivAt
  simpa [mul_comm] using h

/-! ### The static (labour-supply) problem, eq. (4), general utility -/

/-- Galí (2015), eq. (4), p. 19 (**necessity**, general utility): if hours `N` are a local
optimum along the budget line `P C = W N + X` (the perturbation `P dC = W dN`) and `U` has
derivatives `U_c`, `U_n` in `C`, `N` at `(C, N)`, then `U_c (W/P) + U_n = 0`. -/
theorem static_foc_general_necessary {U : ℝ × ℝ → ℝ} {Uc Un P W X C N : ℝ} (hP : 0 < P)
    (hbud : P * C = W * N + X)
    (hU : HasFDerivAt U (Uc • ContinuousLinearMap.fst ℝ ℝ ℝ + Un • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (C, N))
    (hloc : IsLocalMax (fun N' => U ((W * N' + X) / P, N')) N) :
    Uc * (W / P) + Un = 0 := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => ((W * N' + X) / P, N')) (W / P, 1) N := by
    have h1 : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
      simpa using (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    exact h1.prodMk (hasDerivAt_id N)
  have hU' : HasFDerivAt U (Uc • ContinuousLinearMap.fst ℝ ℝ ℝ
      + Un • ContinuousLinearMap.snd ℝ ℝ ℝ) ((W * N + X) / P, N) := by rw [hCeq]; exact hU
  have hg := HasFDerivAt.comp_hasDerivAt (f := fun N' : ℝ => ((W * N' + X) / P, N')) N hU' hin
  have h0 := hloc.hasDerivAt_eq_zero hg
  simpa [mul_comm] using h0

/-- Galí (2015), eq. (4), p. 19: with `U_c ≠ 0` the condition of
`static_foc_general_necessary` is `−U_n/U_c = W/P`. -/
theorem static_foc_general_iff {Uc Un W P : ℝ} (hUc : Uc ≠ 0) :
    Uc * (W / P) + Un = 0 ↔ -Un / Uc = W / P := by
  constructor
  · intro h
    rw [div_eq_iff hUc]
    linarith [show Uc * (W / P) = W / P * Uc by ring]
  · intro h
    rw [div_eq_iff hUc] at h
    linarith [show Uc * (W / P) = W / P * Uc by ring]

/-- Galí (2015), eq. (4), p. 19 (**sufficiency**, general utility): if `U` is concave on a
convex set `S` of plans, differentiable at `(C, N) ∈ S`, and `U_c (W/P) + U_n = 0`, then
`(C, N)` maximises `U` over every plan `(C', N') ∈ S` on the same budget line
`P C' = W N' + X`. -/
theorem static_foc_general_sufficient {U : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {Uc Un P W X C N : ℝ}
    (hP : 0 < P) (hconc : ConcaveOn ℝ S U) (hS : (C, N) ∈ S) (hbud : P * C = W * N + X)
    (hU : HasFDerivAt U (Uc • ContinuousLinearMap.fst ℝ ℝ ℝ + Un • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (C, N))
    (hfoc : Uc * (W / P) + Un = 0) {C' N' : ℝ} (hS' : (C', N') ∈ S)
    (hbud' : P * C' = W * N' + X) : U (C', N') ≤ U (C, N) := by
  have h := concave_le_tangent hconc hS hS' hU
  have hdC : C' - C = W / P * (N' - N) := by
    field_simp
    linarith
  have hlin : (Uc • ContinuousLinearMap.fst ℝ ℝ ℝ + Un • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((C', N') - (C, N)) = (Uc * (W / P) + Un) * (N' - N) := by
    simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
      Pi.smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul]
    rw [hdC]
    ring
  rw [hlin, hfoc, zero_mul, add_zero] at h
  exact h

/-! ### The static (labour-supply) problem -/

/-- Galí (2015), eq. (4), p. 19, and eq. (7), p. 21 (**necessity**): if hours `N > 0`
are a local optimum along the budget line `P C = W N + X` (a perturbation `P dC = W dN`,
everything else unchanged) with `C > 0`, then `W/P = N^φ C^σ`. -/
theorem static_foc_necessary {σ φ P W X Z C N : ℝ} (hφ : 0 ≤ φ) (hP : 0 < P) (hZ : 0 < Z)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hloc : IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z) N) :
    W / P = N ^ φ * C ^ σ := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hin : HasDerivAt (fun N' : ℝ => (W * N' + X) / P) (W / P) N := by
    have := (((hasDerivAt_id N).const_mul W).add_const X).div_const P
    simpa using this
  have hu : HasDerivAt (utilC σ) (((W * N + X) / P) ^ (-σ)) ((W * N + X) / P) :=
    hasDerivAt_utilC σ (by rw [hCeq]; exact hC)
  have hg : HasDerivAt (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z)
      ((C ^ (-σ) * (W / P) - N ^ φ) * Z) N := by
    have := (HasDerivAt.sub (hu.comp N hin) (hasDerivAt_disutilN hφ N)).mul_const Z
    rw [hCeq] at this
    exact this
  have h0 := hloc.hasDerivAt_eq_zero hg
  have h1 : C ^ (-σ) * (W / P) = N ^ φ := by
    have := (mul_eq_zero.1 h0).resolve_right hZ.ne'
    linarith
  have hCs : C ^ σ * C ^ (-σ) = 1 := by
    rw [Real.rpow_neg hC.le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hC σ).ne'
  calc W / P = (C ^ σ * C ^ (-σ)) * (W / P) := by rw [hCs, one_mul]
    _ = N ^ φ * C ^ σ := by rw [mul_assoc, h1, mul_comm]

/-- Galí (2015), p. 19: a global optimum of the static problem over all feasible
plans (`N' ≥ 0`, `C' = (W N' + X)/P > 0`) with `N, C > 0` is a local optimum along the budget
line. -/
theorem static_isLocalMax_of_optimal {σ φ P W X Z C N : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hC : 0 < C) (hbud : P * C = W * N + X)
    (hopt : ∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z) :
    IsLocalMax (fun N' => periodUtility σ φ ((W * N' + X) / P) N' Z) N := by
  have hCeq : (W * N + X) / P = C := by rw [← hbud]; field_simp
  have hcont : Continuous fun N' : ℝ => (W * N' + X) / P := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 N, 0 < (W * N' + X) / P :=
    (hcont.tendsto N).eventually_const_lt (by rw [hCeq]; exact hC)
  filter_upwards [h1, eventually_gt_nhds hN] with N' h1' h2'
  rw [hCeq]
  exact hopt N' h2'.le h1'

/-- Galí (2015), eq. (7), p. 21 (**sufficiency**, by concavity): if `W/P = N^φ C^σ`
at a point `(C, N)` with `C, N > 0` on the budget line, then `(C, N)` maximises utility
among all feasible plans `N' ≥ 0`, `C' = (W N' + X)/P > 0`. -/
theorem static_foc_sufficient {σ φ P W X Z C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hZ : 0 < Z) (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X)
    (hfoc : W / P = N ^ φ * C ^ σ) {N' : ℝ} (hN' : 0 ≤ N') (hC' : 0 < (W * N' + X) / P) :
    periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z := by
  have hu := utilC_le_tangent hσ hC hC'
  have hv := disutilN_tangent_le hφ hN hN'
  have hdiff : (W * N' + X) / P - C = W / P * (N' - N) := by
    rw [show C = (W * N + X) / P by rw [← hbud]; field_simp]
    field_simp
    ring
  have hkey : C ^ (-σ) * (W / P) = N ^ φ := by
    rw [hfoc, Real.rpow_neg hC.le]
    field_simp [(Real.rpow_pos_of_pos hC σ).ne']
  unfold periodUtility
  apply mul_le_mul_of_nonneg_right _ hZ.le
  rw [hdiff] at hu
  nlinarith

/-- Galí (2015), eqs. (4) and (7), pp. 19–21: for `σ > 0`, `φ ≥ 0`, a point with
`C, N > 0` on the budget line solves the static problem iff `W/P = N^φ C^σ`. -/
theorem static_optimum_iff {σ φ P W X Z C N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hP : 0 < P)
    (hZ : 0 < Z) (hN : 0 < N) (hC : 0 < C) (hbud : P * C = W * N + X) :
    (∀ N', 0 ≤ N' → 0 < (W * N' + X) / P →
      periodUtility σ φ ((W * N' + X) / P) N' Z ≤ periodUtility σ φ C N Z) ↔
      W / P = N ^ φ * C ^ σ :=
  ⟨fun h => static_foc_necessary hφ hP hZ hC hbud
      (static_isLocalMax_of_optimal hP hN hC hbud h),
    fun h _ hN' hC' => static_foc_sufficient hσ hφ hP hZ hN hC hbud h hN' hC'⟩

/-- Galí (2015), eq. (9), p. 21, **exact**: for positive levels,
`W/P = N^φ C^σ` iff `w − p = σ c + φ n` in logs. -/
theorem labour_supply_log_iff {σ φ W P C N : ℝ} (hW : 0 < W) (hP : 0 < P) (hC : 0 < C)
    (hN : 0 < N) :
    W / P = N ^ φ * C ^ σ ↔
      Real.log W - Real.log P = σ * Real.log C + φ * Real.log N := by
  have h1 : (0 : ℝ) < W / P := div_pos hW hP
  have h2 : (0 : ℝ) < N ^ φ * C ^ σ :=
    mul_pos (Real.rpow_pos_of_pos hN φ) (Real.rpow_pos_of_pos hC σ)
  rw [← Real.log_injOn_pos.eq_iff h1 h2, Real.log_div hW.ne' hP.ne',
    Real.log_mul (Real.rpow_pos_of_pos hN φ).ne' (Real.rpow_pos_of_pos hC σ).ne',
    Real.log_rpow hN, Real.log_rpow hC]
  constructor <;> intro h <;> linarith

/-! ### The intertemporal problem: the Euler equation -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eqs. (5) and (8), pp. 19–21: the consumption Euler equation
at date `t`, node by node, with the date-`t` variables taken out of `E_t` as numbers:
`Q_t = β (C_t^σ P_t / Z_t) E_t[C_{t+1}^{−σ} Z_{t+1} / P_{t+1}]`. -/
def EulerEq (β σ : ℝ) (Q C P Z : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Q t ω = β * (C t ω ^ σ * P t ω / Z t ω) *
    𝔼.E t (fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') ω

/-- Galí (2015), eq. (8), p. 21: at each node the Euler equation reads
`Q_t = β E_t[(C_{t+1}/C_t)^{−σ} (Z_{t+1}/Z_t) (P_t/P_{t+1})]`, the book's printed form. -/
theorem eulerEq_ratio_form {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ}
    (hC : ∀ ω, 0 < C t ω) (hC1 : ∀ ω, 0 ≤ C (t + 1) ω) (hZ : ∀ ω, 0 < Z t ω) :
    EulerEq 𝔼 β σ Q C P Z t ↔ ∀ ω, Q t ω = β * 𝔼.E t (fun ω' =>
      (C (t + 1) ω' / C t ω) ^ (-σ) * (Z (t + 1) ω' / Z t ω) * (P t ω / P (t + 1) ω')) ω := by
  have key : ∀ ω, (fun ω' =>
      (C (t + 1) ω' / C t ω) ^ (-σ) * (Z (t + 1) ω' / Z t ω) * (P t ω / P (t + 1) ω'))
      = (C t ω ^ σ * P t ω / Z t ω) •
        (fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') := by
    intro ω
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.div_rpow (hC1 ω') (hC ω).le, Real.rpow_neg (hC ω).le]
    have := (Real.rpow_pos_of_pos (hC ω) σ).ne'
    have := (hZ ω).ne'
    field_simp
  unfold EulerEq
  refine forall_congr' fun ω => ?_
  rw [key ω, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Galí (2015), p. 20: expected utility as of date `t` (node `ω`) of the one-period
perturbation that buys `δ` more bonds at `t` (consumption falls by `Q_t δ/P_t`) and consumes
the payoff `δ` at `t + 1` (consumption rises by `δ/P_{t+1}` in every state); hours and all
other dates are unchanged, so by separability only these two terms of
`E_t ∑ β^k U_{t+k}` change. -/
noncomputable def perturbedValue (β σ : ℝ) (Q C P Z : ℕ → Ω → ℝ) (t : ℕ) (δ : ℝ) :
    Ω → ℝ :=
  fun ω => Z t ω * utilC σ (C t ω - Q t ω * δ / P t ω)
    + β * 𝔼.E t (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω')) ω

/-- The concavity sandwich behind Galí (2015), p. 20: for `|δ| < m ≤ P C`, the
date-`t+1` utility gain of the bond perturbation is at least
`(1 + δ/m)^{−σ} δ C^{−σ} Z / P` in every state. -/
theorem utility_gain_lower {σ m δ c p z : ℝ} (hσ : 0 < σ) (hm : 0 < m) (hc : 0 < c)
    (hp : 0 < p) (hz : 0 ≤ z) (hmpc : m ≤ p * c) (hδ : |δ| < m) :
    (1 + δ / m) ^ (-σ) * δ * (c ^ (-σ) * z / p)
      ≤ z * utilC σ (c + δ / p) - z * utilC σ (c + 0 / p) := by
  rw [zero_div, add_zero]
  have hδm := abs_lt.1 hδ
  have hk : 0 < 1 + δ / m := by
    have : -1 < δ / m := by rw [lt_div_iff₀ hm]; linarith
    linarith
  have hcp : 0 < c * (1 + δ / m) := mul_pos hc hk
  -- position of `c + δ/p` relative to `c (1 + δ/m)`
  have hrel : (0 ≤ δ → c + δ / p ≤ c * (1 + δ / m)) ∧ (δ < 0 → c * (1 + δ / m) ≤ c + δ / p) := by
    constructor
    · intro h0
      have : δ / p ≤ δ * c / m := by
        rw [div_le_div_iff₀ hp hm]; nlinarith
      have e : c * (1 + δ / m) = c + δ * c / m := by field_simp
      linarith
    · intro h0
      have : δ * c / m ≤ δ / p := by
        rw [div_le_div_iff₀ hm hp]; nlinarith
      have e : c * (1 + δ / m) = c + δ * c / m := by field_simp
      linarith
  have ha : 0 < c + δ / p := by
    rcases le_or_gt 0 δ with h0 | h0
    · have : 0 ≤ δ / p := div_nonneg h0 hp.le
      linarith
    · linarith [hrel.2 h0]
  -- tangent at `a = c + δ/p` evaluated at `c`
  have htan := utilC_le_tangent hσ ha hc
  have hsplit : (c * (1 + δ / m)) ^ (-σ) = c ^ (-σ) * (1 + δ / m) ^ (-σ) :=
    Real.mul_rpow hc.le hk.le
  have hmain : (1 + δ / m) ^ (-σ) * c ^ (-σ) * (δ / p) ≤ (c + δ / p) ^ (-σ) * (δ / p) := by
    rcases le_or_gt 0 δ with h0 | h0
    · have hle : (c * (1 + δ / m)) ^ (-σ) ≤ (c + δ / p) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos ha (hrel.1 h0) (by linarith)
      rw [hsplit] at hle
      exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg h0 hp.le)
    · have hle : (c + δ / p) ^ (-σ) ≤ (c * (1 + δ / m)) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hcp (hrel.2 h0) (by linarith)
      rw [hsplit] at hle
      exact mul_le_mul_of_nonpos_right (by linarith) (div_nonpos_of_nonpos_of_nonneg h0.le hp.le)
  have hgain : (c + δ / p) ^ (-σ) * (δ / p) ≤ utilC σ (c + δ / p) - utilC σ c := by
    have : c - (c + δ / p) = -(δ / p) := by ring
    rw [this] at htan
    linarith
  have e : (1 + δ / m) ^ (-σ) * δ * (c ^ (-σ) * z / p)
      = z * ((1 + δ / m) ^ (-σ) * c ^ (-σ) * (δ / p)) := by
    field_simp
  rw [e, ← mul_sub]
  exact mul_le_mul_of_nonneg_left (hmain.trans hgain) hz

/-- Galí (2015), eqs. (5) and (8), pp. 19–21 (**necessity of the Euler equation**):
if at every date-`t` node no small bond perturbation `δ` is profitable, then the Euler
equation holds at date `t`. Hypotheses: `σ, β > 0`, positive `C_t, P_t, Z_t`, positive
`C_{t+1}, P_{t+1}`, `Z_{t+1} ≥ 0`, and a uniform lower bound `m > 0` on next period's nominal
expenditure `P_{t+1} C_{t+1}` (automatic for finitely many states). -/
theorem euler_necessary {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 < β)
    (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω) (hZ : ∀ ω, 0 < Z t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hP1 : ∀ ω, 0 < P (t + 1) ω) (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    {m : ℝ} (hm : 0 < m) (hmPC : ∀ ω, m ≤ P (t + 1) ω * C (t + 1) ω)
    (hopt : ∀ ω, ∀ᶠ δ in 𝓝 0,
      perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω) :
    EulerEq 𝔼 β σ Q C P Z t := by
  intro ω
  set G : Ω → ℝ := fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω' with hGdef
  set B := β * 𝔼.E t G ω with hB
  set A := Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω) with hA
  set f : ℝ → ℝ := fun δ => Z t ω * utilC σ (C t ω - Q t ω * δ / P t ω) with hfdef
  set g : ℝ → Ω → ℝ :=
    fun δ ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω') with hgdef
  set k : ℝ → ℝ := fun δ => (1 + δ / m) ^ (-σ) with hkdef
  -- derivative of the date-`t` term
  have hf : HasDerivAt f (-A) 0 := by
    have hin : HasDerivAt (fun δ : ℝ => C t ω - Q t ω * δ / P t ω) (-(Q t ω / P t ω)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (Q t ω)).div_const (P t ω)).const_sub
        (C t ω)
      simpa [mul_div_assoc] using this
    have hu : HasDerivAt (utilC σ) ((C t ω - Q t ω * 0 / P t ω) ^ (-σ))
        (C t ω - Q t ω * 0 / P t ω) := hasDerivAt_utilC σ (by simpa using hC ω)
    have := (hu.comp 0 hin).const_mul (Z t ω)
    refine this.congr_deriv ?_
    simp [hA]
    ring
  -- the lower bound on the change of the date-`t` value
  have hlow : ∀ δ, |δ| < m →
      perturbedValue 𝔼 β σ Q C P Z t δ ω - perturbedValue 𝔼 β σ Q C P Z t 0 ω
        ≥ f δ - f 0 + k δ * δ * B := by
    intro δ hδ
    have hpt : (k δ * δ) • G ≤ g δ - g 0 := by
      intro ω'
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hgdef, hGdef, hkdef]
      exact utility_gain_lower hσ hm (hC1 ω') (hP1 ω') (hZ1 ω') (hmPC ω') hδ
    have hE := 𝔼.mono t hpt ω
    rw [map_smul, map_sub] at hE
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hE
    have hβE := mul_le_mul_of_nonneg_left hE hβ.le
    simp only [perturbedValue, ge_iff_le]
    change f δ - f 0 + k δ * δ * B ≤ f δ + β * 𝔼.E t (g δ) ω - (f 0 + β * 𝔼.E t (g 0) ω)
    rw [hB]
    nlinarith
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), f δ - f 0 + k δ * δ * B ≤ 0 := by
    have hball : ∀ᶠ δ in 𝓝 (0 : ℝ), |δ| < m := by
      have : Tendsto (fun δ : ℝ => |δ|) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_abs.tendsto (0 : ℝ))
      exact this.eventually (gt_mem_nhds hm)
    filter_upwards [hopt ω, hball] with δ h1 h2
    have := hlow δ h2
    linarith
  have hk : Tendsto k (𝓝 0) (𝓝 1) := by
    have hca : ContinuousAt k 0 :=
      (continuousAt_const.add (continuousAt_id.div_const m)).rpow_const (Or.inl (by simp))
    simpa [hkdef] using hca.tendsto
  have hlimR : Tendsto (fun δ => δ⁻¹ * (f δ - f 0) + k δ * B) (𝓝[>] 0) (𝓝 (-A + 1 * B)) := by
    have h1 := hf.tendsto_slope_zero_right
    simp only [zero_add, smul_eq_mul] at h1
    exact h1.add ((hk.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds)
  have hlimL : Tendsto (fun δ => δ⁻¹ * (f δ - f 0) + k δ * B) (𝓝[<] 0) (𝓝 (-A + 1 * B)) := by
    have h1 := hf.tendsto_slope_zero_left
    simp only [zero_add, smul_eq_mul] at h1
    exact h1.add ((hk.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds)
  have hsplit : ∀ δ : ℝ, δ ≠ 0 →
      δ⁻¹ * (f δ - f 0) + k δ * B = δ⁻¹ * (f δ - f 0 + k δ * δ * B) := by
    intro δ hδ
    field_simp
  have hR : -A + 1 * B ≤ 0 := by
    refine le_of_tendsto hlimR ?_
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with δ h1 h2
    rw [hsplit δ (ne_of_gt h2)]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt h2)) h1
  have hL : 0 ≤ -A + 1 * B := by
    refine ge_of_tendsto hlimL ?_
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with δ h1 h2
    rw [hsplit δ (ne_of_lt h2)]
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.2 (le_of_lt h2)) h1
  have hAB : A = B := by linarith
  rw [hA, hB] at hAB
  have hCs : C t ω ^ σ * C t ω ^ (-σ) = 1 := by
    rw [Real.rpow_neg (hC ω).le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (hC ω) σ).ne'
  have hZ0 := (hZ ω).ne'
  have hP0 := (hP ω).ne'
  calc Q t ω = (C t ω ^ σ * C t ω ^ (-σ)) * Q t ω := by rw [hCs, one_mul]
    _ = C t ω ^ σ * P t ω / Z t ω * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)) := by
        field_simp
    _ = β * (C t ω ^ σ * P t ω / Z t ω) * 𝔼.E t G ω := by rw [hAB]; ring

/-- Galí (2015), p. 20: with finitely many states, positive `C_{t+1}` and `P_{t+1}`
have a uniform lower bound `m > 0` on next period's nominal expenditure `P_{t+1} C_{t+1}`. -/
theorem exists_expenditure_lower_bound [Finite Ω] {C P : Ω → ℝ} (hC : ∀ ω, 0 < C ω)
    (hP : ∀ ω, 0 < P ω) : ∃ m, 0 < m ∧ ∀ ω, m ≤ P ω * C ω := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨1, one_pos, fun ω => (IsEmpty.false ω).elim⟩
  · obtain ⟨ω₀, h₀⟩ := Finite.exists_min fun ω => P ω * C ω
    exact ⟨P ω₀ * C ω₀, mul_pos (hP ω₀) (hC ω₀), h₀⟩

/-- Galí (2015), eqs. (5) and (8), pp. 19–21 (**necessity**, finitely many states):
no profitable small bond perturbation at any date-`t` node implies the Euler equation. -/
theorem euler_necessary_finite [Finite Ω] {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ}
    (hσ : 0 < σ) (hβ : 0 < β) (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω)
    (hZ : ∀ ω, 0 < Z t ω) (hC1 : ∀ ω, 0 < C (t + 1) ω) (hP1 : ∀ ω, 0 < P (t + 1) ω)
    (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    (hopt : ∀ ω, ∀ᶠ δ in 𝓝 0,
      perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω) :
    EulerEq 𝔼 β σ Q C P Z t := by
  obtain ⟨m, hm, hmPC⟩ := exists_expenditure_lower_bound hC1 hP1
  exact euler_necessary 𝔼 hσ hβ hC hP hZ hC1 hP1 hZ1 hm hmPC hopt

/-- Galí (2015), eqs. (5) and (8), pp. 19–21 (**sufficiency** for one-period
perturbations, by concavity): if the Euler equation holds at date `t`, no feasible bond
perturbation `δ` (one keeping consumption positive) raises expected utility at any node. -/
theorem euler_sufficient {β σ : ℝ} {Q C P Z : ℕ → Ω → ℝ} {t : ℕ} (hσ : 0 < σ) (hβ : 0 ≤ β)
    (hC : ∀ ω, 0 < C t ω) (hP : ∀ ω, 0 < P t ω) (hZ : ∀ ω, 0 < Z t ω)
    (hC1 : ∀ ω, 0 < C (t + 1) ω) (hZ1 : ∀ ω, 0 ≤ Z (t + 1) ω)
    (heul : EulerEq 𝔼 β σ Q C P Z t) {δ : ℝ} (ω : Ω)
    (hfeas : 0 < C t ω - Q t ω * δ / P t ω) (hfeas1 : ∀ ω', 0 < C (t + 1) ω' + δ / P (t + 1) ω') :
    perturbedValue 𝔼 β σ Q C P Z t δ ω ≤ perturbedValue 𝔼 β σ Q C P Z t 0 ω := by
  set G : Ω → ℝ := fun ω' => C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω' with hGdef
  have hpt : (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + δ / P (t + 1) ω'))
      ≤ (fun ω' => Z (t + 1) ω' * utilC σ (C (t + 1) ω' + 0 / P (t + 1) ω')) + δ • G := by
    intro ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_div, add_zero, hGdef]
    have h := utilC_le_tangent hσ (hC1 ω') (hfeas1 ω')
    have h2 := mul_le_mul_of_nonneg_left h (hZ1 ω')
    have e : Z (t + 1) ω' * (C (t + 1) ω' ^ (-σ) * (C (t + 1) ω' + δ / P (t + 1) ω'
        - C (t + 1) ω')) = δ * (C (t + 1) ω' ^ (-σ) * Z (t + 1) ω' / P (t + 1) ω') := by
      ring
    nlinarith
  have hE := 𝔼.mono t hpt ω
  rw [map_add, map_smul] at hE
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE
  have h0 := utilC_le_tangent hσ (hC ω) hfeas
  have h0' := mul_le_mul_of_nonneg_left h0 (hZ ω).le
  have he : Q t ω = β * (C t ω ^ σ * P t ω / Z t ω) * 𝔼.E t G ω := heul ω
  have hCs : C t ω ^ σ * C t ω ^ (-σ) = 1 := by
    rw [Real.rpow_neg (hC ω).le]
    exact mul_inv_cancel₀ (Real.rpow_pos_of_pos (hC ω) σ).ne'
  -- `Z_t C_t^{−σ} Q_t / P_t = β E_t G`
  have hAB : Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω) = β * 𝔼.E t G ω := by
    have hZ0 := (hZ ω).ne'
    have hP0 := (hP ω).ne'
    calc Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)
        = (C t ω ^ σ * C t ω ^ (-σ)) * β * 𝔼.E t G ω * (Z t ω / Z t ω) * (P t ω / P t ω) := by
          rw [he]; ring
      _ = β * 𝔼.E t G ω := by rw [hCs, div_self hZ0, div_self hP0]; ring
  have e1 : Z t ω * (C t ω ^ (-σ) * (C t ω - Q t ω * δ / P t ω - C t ω))
      = -(δ * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω))) := by ring
  rw [mul_add, e1] at h0'
  have hβE := mul_le_mul_of_nonneg_left hE hβ
  have hδ : δ * (Z t ω * C t ω ^ (-σ) * (Q t ω / P t ω)) = δ * (β * 𝔼.E t G ω) := by rw [hAB]
  simp only [perturbedValue, mul_zero, zero_div, sub_zero]
  simp only [zero_div] at hβE
  nlinarith

/-! ### The Euler equation (5) for a general utility function -/

/-- Galí (2015), eq. (5), pp. 19–20 (**necessity**, general utility, finitely many states):
let `u₀` be the date-`t` utility of consumption at node `ω` (hours and the shifter held fixed)
with marginal utility `U_{c,t}` at `C_t`, and `u₁ ω'` the date-`t+1` utility in state `ω'`
with marginal utility `U_{c,t+1}(ω')`. If buying `δ` more bonds at `t` (consumption falls by
`Q_t δ/P_t`, and rises by `δ/P_{t+1}` in every state at `t + 1`) is not locally profitable,
then `Q_t U_{c,t}/P_t = β E_t[U_{c,t+1}/P_{t+1}]`. With finitely many states `E_t` is a
continuous linear map, so the derivative passes under it. -/
theorem euler_general_necessary {Ω : Type*} [Finite Ω] (𝔼 : ExpectationSystem Ω)
    {β Q P₀ C₀ Uc₀ : ℝ} {u₀ : ℝ → ℝ} {u₁ : Ω → ℝ → ℝ} {C₁ P₁ Uc₁ : Ω → ℝ} (t : ℕ) (ω : Ω)
    (hu₀ : HasDerivAt u₀ Uc₀ C₀) (hu₁ : ∀ ω', HasDerivAt (u₁ ω') (Uc₁ ω') (C₁ ω'))
    (hloc : IsLocalMax (fun δ => u₀ (C₀ - Q * δ / P₀)
      + β * 𝔼.E t (fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω')) ω) 0) :
    Q * Uc₀ / P₀ = β * 𝔼.E t (fun ω' => Uc₁ ω' / P₁ ω') ω := by
  have := Fintype.ofFinite Ω
  have h0 : HasDerivAt (fun δ : ℝ => u₀ (C₀ - Q * δ / P₀)) (Uc₀ * (-(Q / P₀))) 0 := by
    have hin : HasDerivAt (fun δ : ℝ => C₀ - Q * δ / P₀) (-(Q / P₀)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul Q).div_const P₀).const_sub C₀
      simpa [mul_div_assoc] using this
    have hu : HasDerivAt u₀ Uc₀ (C₀ - Q * 0 / P₀) := by simpa using hu₀
    exact hu.comp 0 hin
  have hvec : HasDerivAt (fun δ : ℝ => fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω'))
      (fun ω' => Uc₁ ω' / P₁ ω') 0 := by
    rw [hasDerivAt_pi]
    intro ω'
    have hin : HasDerivAt (fun δ : ℝ => C₁ ω' + δ / P₁ ω') (1 / P₁ ω') 0 :=
      ((hasDerivAt_id (0 : ℝ)).div_const (P₁ ω')).const_add (C₁ ω')
    have hu : HasDerivAt (u₁ ω') (Uc₁ ω') (C₁ ω' + 0 / P₁ ω') := by simpa using hu₁ ω'
    have := hu.comp 0 hin
    rw [mul_one_div] at this
    exact this
  have hE : HasDerivAt (fun δ : ℝ => 𝔼.E t (fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω')))
      (𝔼.E t (fun ω' => Uc₁ ω' / P₁ ω')) 0 := by
    have := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hvec
    exact this
  have hEω := (hasDerivAt_pi.1 hE) ω
  have hsum := h0.add (hEω.const_mul β)
  have h := hloc.hasDerivAt_eq_zero hsum
  have e : Q * Uc₀ / P₀ = Uc₀ * (Q / P₀) := by ring
  rw [e]
  linarith

/-- Galí (2015), eq. (5), p. 19 (**sufficiency**, general concave utility, any expectation
system): if `u₀` and every `u₁ ω'` are concave and differentiable and
`Q_t U_{c,t}/P_t = β E_t[U_{c,t+1}/P_{t+1}]`, then no feasible bond perturbation `δ` raises
expected utility at the node. -/
theorem euler_general_sufficient {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    {β Q P₀ C₀ Uc₀ : ℝ} {S₀ S₁ : Set ℝ} {u₀ : ℝ → ℝ} {u₁ : Ω → ℝ → ℝ} {C₁ P₁ Uc₁ : Ω → ℝ}
    (t : ℕ) (ω : Ω) (hβ : 0 ≤ β) (hc₀ : ConcaveOn ℝ S₀ u₀) (hc₁ : ∀ ω', ConcaveOn ℝ S₁ (u₁ ω'))
    (hu₀ : HasDerivAt u₀ Uc₀ C₀) (hu₁ : ∀ ω', HasDerivAt (u₁ ω') (Uc₁ ω') (C₁ ω'))
    (hm₀ : C₀ ∈ S₀) (hm₁ : ∀ ω', C₁ ω' ∈ S₁)
    (heul : Q * Uc₀ / P₀ = β * 𝔼.E t (fun ω' => Uc₁ ω' / P₁ ω') ω) {δ : ℝ}
    (hf₀ : C₀ - Q * δ / P₀ ∈ S₀) (hf₁ : ∀ ω', C₁ ω' + δ / P₁ ω' ∈ S₁) :
    u₀ (C₀ - Q * δ / P₀) + β * 𝔼.E t (fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω')) ω
      ≤ u₀ C₀ + β * 𝔼.E t (fun ω' => u₁ ω' (C₁ ω')) ω := by
  have h0 := concave_le_tangent_real hc₀ hm₀ hf₀ hu₀
  have hpt : (fun ω' => u₁ ω' (C₁ ω' + δ / P₁ ω'))
      ≤ (fun ω' => u₁ ω' (C₁ ω')) + δ • (fun ω' => Uc₁ ω' / P₁ ω') := by
    intro ω'
    have h1 := concave_le_tangent_real (hc₁ ω') (hm₁ ω') (hf₁ ω') (hu₁ ω')
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : Uc₁ ω' * (C₁ ω' + δ / P₁ ω' - C₁ ω') = δ * (Uc₁ ω' / P₁ ω') := by ring
    linarith
  have hE := 𝔼.mono t hpt ω
  rw [map_add, map_smul] at hE
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hE
  have hβE := mul_le_mul_of_nonneg_left hE hβ
  have e : Uc₀ * (C₀ - Q * δ / P₀ - C₀) = -(δ * (Q * Uc₀ / P₀)) := by ring
  rw [e, heul] at h0
  nlinarith

/-- Galí (2015), eq. (5), p. 19: with `U_{c,t} ≠ 0` and `P_t ≠ 0`, the condition
`Q_t U_{c,t}/P_t = β E_t[U_{c,t+1}/P_{t+1}]` is the book's
`Q_t = β E_t[(U_{c,t+1}/U_{c,t})(P_t/P_{t+1})]`. -/
theorem euler_general_ratio {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β Q P₀ Uc₀ : ℝ}
    {P₁ Uc₁ : Ω → ℝ} (t : ℕ) (ω : Ω) (hUc : Uc₀ ≠ 0) (hP : P₀ ≠ 0) :
    Q * Uc₀ / P₀ = β * 𝔼.E t (fun ω' => Uc₁ ω' / P₁ ω') ω ↔
      Q = β * 𝔼.E t (fun ω' => Uc₁ ω' / Uc₀ * (P₀ / P₁ ω')) ω := by
  have hf : (fun ω' => Uc₁ ω' / Uc₀ * (P₀ / P₁ ω'))
      = (P₀ / Uc₀) • (fun ω' => Uc₁ ω' / P₁ ω') := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hf, map_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/-! ### The deterministic infinite-horizon problem -/

/-- Galí (2015), eqs. (1)–(3), pp. 18–19, deterministic version: the environment of the
household. Preferences `β, σ, φ`; paths of the price level `P`, the wage `W`, dividends `Dv`,
the bond price `Q` and the preference shifter `Z`; initial bond holdings `b₀ = B_{−1}`. -/
structure Economy where
  /-- The discount factor. -/
  β : ℝ
  /-- The curvature of the utility of consumption. -/
  σ : ℝ
  /-- The inverse Frisch elasticity of labour supply. -/
  φ : ℝ
  /-- The price level. -/
  P : ℕ → ℝ
  /-- The nominal wage. -/
  W : ℕ → ℝ
  /-- Nominal dividends. -/
  Dv : ℕ → ℝ
  /-- The price of a one-period nominal bond. -/
  Q : ℕ → ℝ
  /-- The preference shifter. -/
  Z : ℕ → ℝ
  /-- Initial bond holdings `B_{−1}`. -/
  b₀ : ℝ

/-- Galí (2015), p. 18: a household plan: consumption `C_t`, hours `N_t`, and bonds `B_t`
bought at `t` (maturing at `t + 1`). -/
structure Plan where
  /-- Consumption. -/
  C : ℕ → ℝ
  /-- Hours. -/
  N : ℕ → ℝ
  /-- Bonds bought at date `t`. -/
  B : ℕ → ℝ

/-- Galí (2015), eq. (2), p. 18: bonds carried into date `t`, `B_{t−1}` (with `B_{−1} = b₀`). -/
def lagB (b₀ : ℝ) (B : ℕ → ℝ) : ℕ → ℝ
  | 0 => b₀
  | t + 1 => B t

/-- Galí (2015), pp. 18–19: the date-0 price of one unit of money paid at date `T`,
`∏_{s<T} Q_s` (the nominal discount factor implied by bond prices). -/
noncomputable def disc (Q : ℕ → ℝ) (T : ℕ) : ℝ := ∏ s ∈ Finset.range T, Q s

/-- Galí (2015), p. 19: `disc Q 0 = 1`. -/
theorem disc_zero (Q : ℕ → ℝ) : disc Q 0 = 1 := by simp [disc]

/-- Galí (2015), p. 19: `disc Q (T + 1) = disc Q T · Q_T`. -/
theorem disc_succ (Q : ℕ → ℝ) (T : ℕ) : disc Q (T + 1) = disc Q T * Q T :=
  Finset.prod_range_succ _ _

/-- Galí (2015), p. 19: positive bond prices give positive discount factors. -/
theorem disc_pos {Q : ℕ → ℝ} (hQ : ∀ t, 0 < Q t) (T : ℕ) : 0 < disc Q T :=
  Finset.prod_pos fun s _ => hQ s

/-- Galí (2015), eq. (2), p. 18: the flow budget constraint at date `t`,
`P_t C_t + Q_t B_t ≤ B_{t−1} + W_t N_t + D_t`. -/
def Budget (e : Economy) (x : Plan) (t : ℕ) : Prop :=
  e.P t * x.C t + e.Q t * x.B t ≤ lagB e.b₀ x.B t + e.W t * x.N t + e.Dv t

/-- Galí (2015), eq. (3), p. 19, deterministic form: the no-Ponzi condition
`liminf_T (∏_{s≤T} Q_s) B_T ≥ 0` on the date-0 value of the bonds bought at `T`. -/
def NoPonzi (e : Economy) (x : Plan) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ disc e.Q (T + 1) * x.B T

/-- Galí (2015), pp. 18–19: a feasible plan: positive consumption, nonnegative hours, the
budget constraint (2) at every date, and the no-Ponzi condition (3). -/
def Feasible (e : Economy) (x : Plan) : Prop :=
  (∀ t, 0 < x.C t) ∧ (∀ t, 0 ≤ x.N t) ∧ (∀ t, Budget e x t) ∧ NoPonzi e x

/-- Galí (2015), eq. (1), p. 18, deterministic: the finite-horizon sum
`∑_{t<T} β^t U(C_t, N_t; Z_t)` of lifetime utility. -/
noncomputable def partialUtility (e : Economy) (x : Plan) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, e.β ^ t * periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t)

/-- Galí (2015), eq. (1), p. 18: a feasible plan is optimal when no feasible plan overtakes
it: for every feasible `y` and `ε > 0`, eventually `∑_{t<T} β^t U(y_t) ≤ ∑_{t<T} β^t U(x_t) + ε`.
This needs no summability; for summable utility it is `∑' β^t U(y_t) ≤ ∑' β^t U(x_t)`
(`tsum_le_of_optimal`). -/
def Optimal (e : Economy) (x : Plan) : Prop :=
  Feasible e x ∧ ∀ y, Feasible e y → ∀ ε > 0, ∀ᶠ T in atTop,
    partialUtility e y T ≤ partialUtility e x T + ε

/-- Galí (2015), eq. (7), p. 21: the static condition `W_t/P_t = N_t^φ C_t^σ` at every date. -/
def StaticFOC (e : Economy) (x : Plan) : Prop :=
  ∀ t, e.W t / e.P t = x.N t ^ e.φ * x.C t ^ e.σ

/-- Galí (2015), eq. (8), p. 21, deterministic: the Euler equation at every date,
`Q_t = β (C_t^σ P_t/Z_t)(C_{t+1}^{−σ} Z_{t+1}/P_{t+1})`. -/
def EulerDet (e : Economy) (x : Plan) : Prop :=
  ∀ t, e.Q t = e.β * (x.C t ^ e.σ * e.P t / e.Z t) *
    (x.C (t + 1) ^ (-e.σ) * e.Z (t + 1) / e.P (t + 1))

/-- Galí (2015), eq. (2), p. 18: the budget constraint holds with equality at every date. -/
def BudgetBinds (e : Economy) (x : Plan) : Prop :=
  ∀ t, e.P t * x.C t + e.Q t * x.B t = lagB e.b₀ x.B t + e.W t * x.N t + e.Dv t

/-- Galí (2015), eq. (6), p. 19, deterministic form: the transversality condition
`lim_T (∏_{s≤T} Q_s) B_T = 0`. -/
def Transversality (e : Economy) (x : Plan) : Prop :=
  Tendsto (fun T => disc e.Q (T + 1) * x.B T) atTop (𝓝 0)

/-- Galí (2015), p. 19: the discounted marginal utility of money,
`λ_t = β^t U_{c,t}/P_t = β^t Z_t C_t^{−σ}/P_t`. -/
noncomputable def lam (e : Economy) (x : Plan) (t : ℕ) : ℝ :=
  e.β ^ t * e.Z t * x.C t ^ (-e.σ) / e.P t

/-- Galí (2015), eq. (8), p. 21: the deterministic Euler equation at `t` is `λ_{t+1} = Q_t λ_t`. -/
theorem eulerDet_iff_lam (e : Economy) (x : Plan) (t : ℕ) (hβ : 0 < e.β)
    (hC : 0 < x.C t) (hZ : 0 < e.Z t) (hP : 0 < e.P t) :
    e.Q t = e.β * (x.C t ^ e.σ * e.P t / e.Z t) *
      (x.C (t + 1) ^ (-e.σ) * e.Z (t + 1) / e.P (t + 1)) ↔
      lam e x (t + 1) = e.Q t * lam e x t := by
  have hc : 0 < x.C t ^ e.σ := Real.rpow_pos_of_pos hC _
  have hl : 0 < lam e x t := by
    unfold lam
    have := Real.rpow_pos_of_pos hC (-e.σ)
    positivity
  constructor
  · intro h
    rw [h]
    unfold lam
    rw [Real.rpow_neg hC.le]
    field_simp
    ring
  · intro h
    have hq : e.Q t = lam e x (t + 1) / lam e x t := by rw [h]; field_simp
    rw [hq]
    unfold lam
    rw [Real.rpow_neg hC.le]
    field_simp
    ring

/-- Galí (2015), p. 19: along the Euler equation, `λ_T = λ_0 ∏_{s<T} Q_s`. -/
theorem lam_eq_disc (e : Economy) (x : Plan) (hlam : ∀ t, lam e x (t + 1) = e.Q t * lam e x t)
    (T : ℕ) : lam e x T = lam e x 0 * disc e.Q T := by
  induction T with
  | zero => rw [disc_zero, mul_one]
  | succ T ih => rw [hlam, ih, disc_succ]; ring

/-- Summation by parts behind Galí (2015), p. 20: if `g 0 = 0` and `g (t + 1) = f t`, then
`∑_{t ≤ T} (g t − f t) = −f T`. -/
theorem sum_telescope (f g : ℕ → ℝ) (h0 : g 0 = 0) (hs : ∀ t, g (t + 1) = f t) (T : ℕ) :
    ∑ t ∈ Finset.range (T + 1), (g t - f t) = -f T := by
  induction T with
  | zero => simp [h0]
  | succ T ih => rw [Finset.sum_range_succ, ih, hs]; ring

/-- Galí (2015), eqs. (6)–(8), pp. 19–21 (**sufficiency**, deterministic infinite horizon):
a feasible plan with interior hours that satisfies the budget constraint with equality, the
static condition (7), the Euler equation (8) at every date and the transversality condition
(6) is optimal. (`σ > 0` covers the log case `σ = 1`.) -/
theorem optimal_of_foc (e : Economy) (x : Plan) (hβ : 0 < e.β) (hσ : 0 < e.σ) (hφ : 0 ≤ e.φ)
    (hP : ∀ t, 0 < e.P t) (hZ : ∀ t, 0 < e.Z t) (hx : Feasible e x) (hN : ∀ t, 0 < x.N t)
    (hbind : BudgetBinds e x) (hst : StaticFOC e x) (heu : EulerDet e x)
    (htvc : Transversality e x) : Optimal e x := by
  refine ⟨hx, fun y hy ε hε => ?_⟩
  obtain ⟨hCx, -, -, -⟩ := hx
  obtain ⟨hCy, hNy, hBy, hNPy⟩ := hy
  have hlam : ∀ t, lam e x (t + 1) = e.Q t * lam e x t := fun t =>
    (eulerDet_iff_lam e x t hβ (hCx t) (hZ t) (hP t)).1 (heu t)
  have hper : ∀ t, e.β ^ t * periodUtility e.σ e.φ (y.C t) (y.N t) (e.Z t)
      - e.β ^ t * periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t)
      ≤ lam e x t * (lagB e.b₀ y.B t - lagB e.b₀ x.B t) - lam e x (t + 1) * (y.B t - x.B t) := by
    intro t
    have hu := utilC_le_tangent hσ (hCx t) (hCy t)
    have hv := disutilN_tangent_le hφ (hN t) (hNy t)
    have hc : 0 < x.C t ^ e.σ := Real.rpow_pos_of_pos (hCx t) _
    have hm : x.C t ^ (-e.σ) = (x.C t ^ e.σ)⁻¹ := Real.rpow_neg (hCx t).le _
    have hNφ : x.N t ^ e.φ = e.W t / e.P t * x.C t ^ (-e.σ) := by
      rw [hst t, hm]
      field_simp
    have hb := hBy t
    have hbx := hbind t
    unfold Budget at hb
    rw [hlam t]
    unfold periodUtility lam
    have hk : 0 ≤ e.β ^ t * e.Z t := by have := hZ t; positivity
    have hm0 : 0 ≤ x.C t ^ (-e.σ) := (Real.rpow_pos_of_pos (hCx t) _).le
    have hPt := hP t
    have step1 : (utilC e.σ (y.C t) - disutilN e.φ (y.N t))
        - (utilC e.σ (x.C t) - disutilN e.φ (x.N t))
        ≤ x.C t ^ (-e.σ) / e.P t * (e.P t * (y.C t - x.C t) - e.W t * (y.N t - x.N t)) := by
      have e1 : x.C t ^ (-e.σ) / e.P t * (e.P t * (y.C t - x.C t) - e.W t * (y.N t - x.N t))
          = x.C t ^ (-e.σ) * (y.C t - x.C t) - x.N t ^ e.φ * (y.N t - x.N t) := by
        rw [hNφ]
        field_simp
      rw [e1]
      linarith
    have step2 : e.P t * (y.C t - x.C t) - e.W t * (y.N t - x.N t)
        ≤ (lagB e.b₀ y.B t - lagB e.b₀ x.B t) - e.Q t * (y.B t - x.B t) := by
      linarith
    have step3 := mul_le_mul_of_nonneg_left step2 (div_nonneg hm0 hPt.le)
    have step4 := mul_le_mul_of_nonneg_left (step1.trans step3) hk
    have e2 : e.β ^ t * ((utilC e.σ (y.C t) - disutilN e.φ (y.N t)) * e.Z t)
        - e.β ^ t * ((utilC e.σ (x.C t) - disutilN e.φ (x.N t)) * e.Z t)
        = e.β ^ t * e.Z t * ((utilC e.σ (y.C t) - disutilN e.φ (y.N t))
          - (utilC e.σ (x.C t) - disutilN e.φ (x.N t))) := by ring
    rw [e2]
    refine step4.trans (le_of_eq ?_)
    ring
  have hsum : ∀ T, partialUtility e y (T + 1) - partialUtility e x (T + 1)
      ≤ lam e x 0 * (disc e.Q (T + 1) * x.B T) - lam e x 0 * (disc e.Q (T + 1) * y.B T) := by
    intro T
    unfold partialUtility
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_le_sum fun t _ => hper t).trans (le_of_eq ?_)
    rw [sum_telescope (fun t => lam e x (t + 1) * (y.B t - x.B t))
      (fun t => lam e x t * (lagB e.b₀ y.B t - lagB e.b₀ x.B t)) (by simp [lagB])
      (fun t => rfl) T, lam_eq_disc e x hlam]
    ring
  have hl0 : 0 < lam e x 0 := by
    unfold lam
    have := Real.rpow_pos_of_pos (hCx 0) (-e.σ)
    have := hZ 0
    have := hP 0
    positivity
  set δ := ε / (2 * lam e x 0) with hδ
  have hδ0 : 0 < δ := by positivity
  have h1 : ∀ᶠ T in atTop, disc e.Q (T + 1) * x.B T < δ := htvc.eventually (gt_mem_nhds hδ0)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (h1.and (hNPy δ hδ0))
  refine eventually_atTop.2 ⟨T₀ + 1, fun T hT => ?_⟩
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  obtain ⟨ha, hb⟩ := hT₀ T' (by omega)
  have hs := hsum T'
  have hcalc : lam e x 0 * δ + lam e x 0 * δ = ε := by
    rw [hδ]
    field_simp
    ring
  nlinarith

/-- Galí (2015), eq. (1), p. 18: for an optimal plan and any feasible plan whose discounted
utilities are summable, `∑' β^t U(y_t) ≤ ∑' β^t U(x_t)`. -/
theorem tsum_le_of_optimal {e : Economy} {x y : Plan} (hopt : Optimal e x) (hy : Feasible e y)
    (hsx : Summable fun t => e.β ^ t * periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t))
    (hsy : Summable fun t => e.β ^ t * periodUtility e.σ e.φ (y.C t) (y.N t) (e.Z t)) :
    ∑' t, e.β ^ t * periodUtility e.σ e.φ (y.C t) (y.N t) (e.Z t)
      ≤ ∑' t, e.β ^ t * periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hx := hsx.hasSum.tendsto_sum_nat
  have hy' := hsy.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto hy' (hx.add_const ε) (hopt.2 y hy ε hε)

/-- An optimal plan is not overtaken: a feasible deviation whose finite-horizon utility gain is
eventually a constant `g` has `g ≤ 0` (used for the necessity results of Galí (2015),
pp. 19–20). -/
theorem gain_nonpos_of_optimal {e : Economy} {x y : Plan} (hopt : Optimal e x)
    (hy : Feasible e y) {g : ℝ} {T₀ : ℕ}
    (hg : ∀ T, T₀ ≤ T → partialUtility e y T - partialUtility e x T = g) : g ≤ 0 := by
  by_contra h
  push Not at h
  obtain ⟨T, hT1, hT2⟩ := ((hopt.2 y hy (g / 2) (by linarith)).and
    (eventually_ge_atTop T₀)).exists
  have := hg T hT2
  linarith

/-- A sum over `range T` of a function vanishing off `t` is its value at `t` (`t < T`). -/
theorem sum_range_single {f : ℕ → ℝ} {t T : ℕ} (hf : ∀ s, s ≠ t → f s = 0) (hT : t < T) :
    ∑ s ∈ Finset.range T, f s = f t :=
  Finset.sum_eq_single_of_mem t (Finset.mem_range.2 hT) fun s _ hs => hf s hs

/-- A sum over `range T` of a function vanishing off `{t, t + 1}` is `f t + f (t + 1)`. -/
theorem sum_range_pair {f : ℕ → ℝ} {t T : ℕ} (hf : ∀ s, s ≠ t → s ≠ t + 1 → f s = 0)
    (hT : t + 1 < T) : ∑ s ∈ Finset.range T, f s = f t + f (t + 1) :=
  Finset.sum_eq_add_of_mem t (t + 1) (Finset.mem_range.2 (by omega)) (Finset.mem_range.2 hT)
    (by omega) fun s _ hs => hf s hs.1 hs.2

/-- Galí (2015), eq. (2), p. 18 (**necessity**): an optimal plan exhausts the budget at every
date; otherwise consuming the slack at that date raises utility (`U_c > 0`). -/
theorem budgetBinds_of_optimal {e : Economy} {x : Plan} (hβ : 0 < e.β) (hσ : 0 < e.σ)
    (hP : ∀ t, 0 < e.P t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x) : BudgetBinds e x := by
  intro t
  obtain ⟨hC, hN, hB, hNP⟩ := hopt.1
  by_contra hne
  have hlt := lt_of_le_of_ne (hB t) hne
  set s := lagB e.b₀ x.B t + e.W t * x.N t + e.Dv t - (e.P t * x.C t + e.Q t * x.B t) with hs
  have hs0 : 0 < s := by linarith
  have hsp : 0 < s / e.P t := div_pos hs0 (hP t)
  set y : Plan := ⟨Function.update x.C t (x.C t + s / e.P t), x.N, x.B⟩ with hydef
  have hy : Feasible e y := by
    refine ⟨fun r => ?_, hN, fun r => ?_, hNP⟩
    · by_cases hr : r = t
      · subst hr
        simp only [hydef, Function.update_self]
        linarith [hC r]
      · simp only [hydef, Function.update_of_ne hr]
        exact hC r
    · by_cases hr : r = t
      · subst hr
        simp only [Budget, hydef, Function.update_self]
        rw [mul_add, mul_div_cancel₀ _ (hP r).ne']
        linarith
      · simp only [Budget, hydef, Function.update_of_ne hr]
        exact hB r
  have hg : ∀ T, t + 1 ≤ T → partialUtility e y T - partialUtility e x T =
      e.β ^ t * ((utilC e.σ (x.C t + s / e.P t) - utilC e.σ (x.C t)) * e.Z t) := by
    intro T hT
    unfold partialUtility
    rw [← Finset.sum_sub_distrib, sum_range_single (t := t) _ (by omega)]
    · simp only [hydef, Function.update_self, periodUtility]
      ring
    · intro r hr
      simp only [hydef, Function.update_of_ne hr]
      ring
  have hle := gain_nonpos_of_optimal hopt hy hg
  have hu := utilC_strictMono hσ (hC t) (by linarith : x.C t < x.C t + s / e.P t)
  have : 0 < e.β ^ t * ((utilC e.σ (x.C t + s / e.P t) - utilC e.σ (x.C t)) * e.Z t) :=
    mul_pos (pow_pos hβ t) (mul_pos (by linarith) (hZ t))
  linarith

/-- Galí (2015), eqs. (4) and (7), pp. 19–21 (**necessity**, deterministic infinite horizon):
at an optimal plan, every date with positive hours satisfies `W_t/P_t = N_t^φ C_t^σ`. -/
theorem staticFOC_of_optimal {e : Economy} {x : Plan} (hβ : 0 < e.β) (hσ : 0 < e.σ)
    (hφ : 0 ≤ e.φ) (hP : ∀ t, 0 < e.P t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x) (t : ℕ)
    (hNt : 0 < x.N t) : e.W t / e.P t = x.N t ^ e.φ * x.C t ^ e.σ := by
  obtain ⟨hC, hN, hB, hNP⟩ := hopt.1
  have hbind := budgetBinds_of_optimal hβ hσ hP hZ hopt t
  set X := lagB e.b₀ x.B t + e.Dv t - e.Q t * x.B t with hX
  have hbud : e.P t * x.C t = e.W t * x.N t + X := by rw [hX]; linarith
  have hCeq : (e.W t * x.N t + X) / e.P t = x.C t := by rw [← hbud]; field_simp [(hP t).ne']
  refine static_foc_necessary hφ (hP t) (hZ t) (hC t) hbud ?_
  have hcont : Continuous fun N' : ℝ => (e.W t * N' + X) / e.P t := by fun_prop
  have h1 : ∀ᶠ N' in 𝓝 (x.N t), 0 < (e.W t * N' + X) / e.P t :=
    (hcont.tendsto _).eventually_const_lt (by rw [hCeq]; exact hC t)
  filter_upwards [h1, eventually_gt_nhds hNt] with N' h1' h2'
  set y : Plan := ⟨Function.update x.C t ((e.W t * N' + X) / e.P t),
    Function.update x.N t N', x.B⟩ with hydef
  have hy : Feasible e y := by
    refine ⟨fun r => ?_, fun r => ?_, fun r => ?_, hNP⟩
    · by_cases hr : r = t
      · subst hr; simpa only [hydef, Function.update_self] using h1'
      · simp only [hydef, Function.update_of_ne hr]; exact hC r
    · by_cases hr : r = t
      · subst hr; simp only [hydef, Function.update_self]; exact h2'.le
      · simp only [hydef, Function.update_of_ne hr]; exact hN r
    · by_cases hr : r = t
      · subst hr
        simp only [Budget, hydef, Function.update_self]
        rw [mul_div_cancel₀ _ (hP r).ne', hX]
        linarith
      · simp only [Budget, hydef, Function.update_of_ne hr]
        exact hB r
  have hg : ∀ T, t + 1 ≤ T → partialUtility e y T - partialUtility e x T =
      e.β ^ t * (periodUtility e.σ e.φ ((e.W t * N' + X) / e.P t) N' (e.Z t)
        - periodUtility e.σ e.φ (x.C t) (x.N t) (e.Z t)) := by
    intro T hT
    unfold partialUtility
    rw [← Finset.sum_sub_distrib, sum_range_single (t := t) _ (by omega)]
    · simp only [hydef, Function.update_self]
      ring
    · intro r hr
      simp only [hydef, Function.update_of_ne hr]
      ring
  have hle := gain_nonpos_of_optimal hopt hy hg
  have hb := pow_pos hβ t
  rw [hCeq]
  nlinarith

/-- Galí (2015), p. 18: `B_{t−1}` after changing the bonds bought at date `t` only. -/
theorem lagB_update (b₀ : ℝ) (B : ℕ → ℝ) (t : ℕ) (v : ℝ) (r : ℕ) :
    lagB b₀ (Function.update B t v) r = if r = t + 1 then v else lagB b₀ B r := by
  cases r with
  | zero => simp [lagB]
  | succ r =>
    by_cases hr : r = t
    · subst hr; simp [lagB]
    · simp [lagB, hr]

/-- Galí (2015), eqs. (5) and (8), pp. 19–21 (**necessity**, deterministic infinite horizon,
the perturbation argument of p. 20): at an optimal plan the Euler equation holds at every
date. The deviation buys `δ` more bonds at `t`, consumes `Q_t δ/P_t` less at `t` and `δ/P_{t+1}`
more at `t + 1`; it is feasible for small `δ` and changes no other date. -/
theorem eulerDet_of_optimal {e : Economy} {x : Plan} (hβ : 0 < e.β)
    (hP : ∀ t, 0 < e.P t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x) : EulerDet e x := by
  intro t
  obtain ⟨hC, hN, hB, hNP⟩ := hopt.1
  rw [eulerDet_iff_lam e x t hβ (hC t) (hZ t) (hP t)]
  set G : ℝ → ℝ := fun δ => e.β ^ t * e.Z t * utilC e.σ (x.C t - e.Q t * δ / e.P t)
    + e.β ^ (t + 1) * e.Z (t + 1) * utilC e.σ (x.C (t + 1) + δ / e.P (t + 1)) with hGdef
  have hG : HasDerivAt G (e.β ^ t * e.Z t * (x.C t ^ (-e.σ) * (-(e.Q t / e.P t)))
      + e.β ^ (t + 1) * e.Z (t + 1) * (x.C (t + 1) ^ (-e.σ) * (1 / e.P (t + 1)))) 0 := by
    have hin0 : HasDerivAt (fun δ : ℝ => x.C t - e.Q t * δ / e.P t) (-(e.Q t / e.P t)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_mul (e.Q t)).div_const (e.P t)).const_sub (x.C t)
      simpa [mul_div_assoc] using this
    have hin1 : HasDerivAt (fun δ : ℝ => x.C (t + 1) + δ / e.P (t + 1)) (1 / e.P (t + 1)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).div_const (e.P (t + 1))).const_add (x.C (t + 1))
    have hu0 : HasDerivAt (utilC e.σ) (x.C t ^ (-e.σ)) (x.C t - e.Q t * 0 / e.P t) := by
      simpa using hasDerivAt_utilC e.σ (hC t)
    have hu1 : HasDerivAt (utilC e.σ) (x.C (t + 1) ^ (-e.σ)) (x.C (t + 1) + 0 / e.P (t + 1)) := by
      simpa using hasDerivAt_utilC e.σ (hC (t + 1))
    exact ((hu0.comp 0 hin0).const_mul _).add ((hu1.comp 0 hin1).const_mul _)
  have hloc : IsLocalMax G 0 := by
    have hc0 : Continuous fun δ : ℝ => x.C t - e.Q t * δ / e.P t := by fun_prop
    have hc1 : Continuous fun δ : ℝ => x.C (t + 1) + δ / e.P (t + 1) := by fun_prop
    have h0 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < x.C t - e.Q t * δ / e.P t :=
      (hc0.tendsto 0).eventually_const_lt (by simpa using hC t)
    have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < x.C (t + 1) + δ / e.P (t + 1) :=
      (hc1.tendsto 0).eventually_const_lt (by simpa using hC (t + 1))
    filter_upwards [h0, h1] with δ hδ0 hδ1
    set y : Plan := ⟨fun s => if s = t then x.C t - e.Q t * δ / e.P t
      else if s = t + 1 then x.C (t + 1) + δ / e.P (t + 1) else x.C s, x.N,
      Function.update x.B t (x.B t + δ)⟩ with hydef
    have hy : Feasible e y := by
      refine ⟨fun r => ?_, hN, fun r => ?_, fun ε hε => ?_⟩
      · by_cases hr : r = t
        · simp only [hydef, hr, ↓reduceIte]; exact hδ0
        · by_cases hr1 : r = t + 1
          · simp only [hydef, hr1, ↓reduceIte, show t + 1 ≠ t by omega]; exact hδ1
          · simp only [hydef, hr, hr1, ↓reduceIte]; exact hC r
      · unfold Budget
        rw [lagB_update]
        by_cases hr : r = t
        · subst hr
          simp only [hydef, ↓reduceIte, Function.update_self, show r ≠ r + 1 by omega]
          have := hB r
          unfold Budget at this
          have e1 : e.P r * (x.C r - e.Q r * δ / e.P r) = e.P r * x.C r - e.Q r * δ := by
            field_simp [(hP r).ne']
          rw [e1]
          linarith
        · by_cases hr1 : r = t + 1
          · subst hr1
            simp only [hydef, ↓reduceIte, show t + 1 ≠ t by omega,
              Function.update_of_ne (show t + 1 ≠ t by omega)]
            have := hB (t + 1)
            unfold Budget lagB at this
            have e1 : e.P (t + 1) * (x.C (t + 1) + δ / e.P (t + 1))
                = e.P (t + 1) * x.C (t + 1) + δ := by
              field_simp [(hP (t + 1)).ne']
            rw [e1]
            linarith
          · simp only [hydef, hr, hr1, ↓reduceIte, Function.update_of_ne hr]
            exact hB r
      · filter_upwards [hNP ε hε, eventually_gt_atTop t] with T hT1 hT2
        simp only [hydef, Function.update_of_ne (show T ≠ t by omega)]
        exact hT1
    have hg : ∀ T, t + 2 ≤ T → partialUtility e y T - partialUtility e x T = G δ - G 0 := by
      intro T hT
      unfold partialUtility
      rw [← Finset.sum_sub_distrib, sum_range_pair (t := t) _ (by omega)]
      · simp only [hydef, hGdef, ↓reduceIte, show t + 1 ≠ t by omega, periodUtility]
        simp only [mul_zero, zero_div, sub_zero, add_zero]
        ring
      · intro r hr hr1
        simp only [hydef, hr, hr1, ↓reduceIte]
        ring
    linarith [gain_nonpos_of_optimal hopt hy hg]
  have h := hloc.hasDerivAt_eq_zero hG
  unfold lam
  linear_combination h

/-- Galí (2015), p. 20 and eq. (6), p. 19 (**necessity of transversality**, the book's
argument): at an optimal plan the no-Ponzi condition (3) cannot hold with strict inequality.
If the date-0 value of bonds stayed above some `L > 0`, the household could consume `L/P_0`
more at date 0 and roll the debt over forever, which raises utility. Hence, for every `L > 0`,
`(∏_{s≤T} Q_s) B_T < L` for infinitely many `T`: `liminf_T (∏_{s≤T} Q_s) B_T ≤ 0`. -/
theorem tvc_liminf_of_optimal {e : Economy} {x : Plan} (hσ : 0 < e.σ) (hP : ∀ t, 0 < e.P t)
    (hQ : ∀ t, 0 < e.Q t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x) {L : ℝ} (hL : 0 < L) :
    ∃ᶠ T in atTop, disc e.Q (T + 1) * x.B T < L := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨hC, hN, hB, hNP⟩ := hopt.1
  have hd := disc_pos hQ
  set y : Plan := ⟨Function.update x.C 0 (x.C 0 + L / e.P 0), x.N,
    fun s => x.B s - L / disc e.Q (s + 1)⟩ with hydef
  have hy : Feasible e y := by
    refine ⟨fun r => ?_, hN, fun r => ?_, fun ε hε => ?_⟩
    · by_cases hr : r = 0
      · subst hr
        simp only [hydef, Function.update_self]
        have := div_pos hL (hP 0)
        linarith [hC 0]
      · simp only [hydef, Function.update_of_ne hr]
        exact hC r
    · cases r with
      | zero =>
        have := hB 0
        unfold Budget lagB at this ⊢
        simp only [hydef, Function.update_self, disc_succ, disc_zero, one_mul]
        have e1 : e.P 0 * (x.C 0 + L / e.P 0) + e.Q 0 * (x.B 0 - L / e.Q 0)
            = e.P 0 * x.C 0 + e.Q 0 * x.B 0 := by
          field_simp [(hP 0).ne', (hQ 0).ne']
          ring
        rw [e1]
        exact this
      | succ r =>
        have := hB (r + 1)
        unfold Budget lagB at this ⊢
        simp only [hydef, Function.update_of_ne (show r + 1 ≠ 0 by omega)]
        have e1 : e.Q (r + 1) * (x.B (r + 1) - L / disc e.Q (r + 1 + 1))
            = e.Q (r + 1) * x.B (r + 1) - L / disc e.Q (r + 1) := by
          rw [disc_succ e.Q (r + 1)]
          field_simp [(hQ (r + 1)).ne', (hd (r + 1)).ne']
        rw [e1]
        linarith
    · filter_upwards [hcon] with T hT
      push Not at hT
      simp only [hydef]
      rw [mul_sub, mul_div_cancel₀ _ (hd (T + 1)).ne']
      linarith
  have hg : ∀ T, 0 + 1 ≤ T → partialUtility e y T - partialUtility e x T =
      e.β ^ 0 * ((utilC e.σ (x.C 0 + L / e.P 0) - utilC e.σ (x.C 0)) * e.Z 0) := by
    intro T hT
    unfold partialUtility
    rw [← Finset.sum_sub_distrib, sum_range_single (t := 0) _ (by omega)]
    · simp only [hydef, Function.update_self, periodUtility]
      ring
    · intro r hr
      simp only [hydef, Function.update_of_ne hr]
      ring
  have hle := gain_nonpos_of_optimal hopt hy hg
  have hu := utilC_strictMono hσ (hC 0) (by
    have := div_pos hL (hP 0); linarith : x.C 0 < x.C 0 + L / e.P 0)
  have : 0 < e.β ^ 0 * ((utilC e.σ (x.C 0 + L / e.P 0) - utilC e.σ (x.C 0)) * e.Z 0) := by
    rw [pow_zero, one_mul]
    exact mul_pos (by linarith) (hZ 0)
  linarith

/-- Galí (2015), eq. (6), p. 19 (**necessity of transversality**): at an optimal plan, if the
date-0 value of bond holdings `(∏_{s≤T} Q_s) B_T` converges (as the book's `lim` presupposes),
its limit is zero. The no-Ponzi condition (3) gives `≥ 0`; `tvc_liminf_of_optimal` gives `≤ 0`. -/
theorem tvc_of_optimal_of_tendsto {e : Economy} {x : Plan} (hσ : 0 < e.σ)
    (hP : ∀ t, 0 < e.P t) (hQ : ∀ t, 0 < e.Q t) (hZ : ∀ t, 0 < e.Z t) (hopt : Optimal e x)
    {L : ℝ} (hlim : Tendsto (fun T => disc e.Q (T + 1) * x.B T) atTop (𝓝 L)) : L = 0 := by
  rcases lt_trichotomy L 0 with hL | hL | hL
  · exfalso
    have h1 := hopt.1.2.2.2 (-L / 2) (by linarith)
    have h2 : ∀ᶠ T in atTop, disc e.Q (T + 1) * x.B T < L / 2 :=
      hlim.eventually (gt_mem_nhds (by linarith))
    obtain ⟨T, hT1, hT2⟩ := (h1.and h2).exists
    linarith
  · exact hL
  · exfalso
    have h1 := tvc_liminf_of_optimal hσ hP hQ hZ hopt (half_pos hL)
    have h2 : ∀ᶠ T in atTop, L / 2 < disc e.Q (T + 1) * x.B T :=
      hlim.eventually (lt_mem_nhds (by linarith))
    obtain ⟨T, hT1, hT2⟩ := (h1.and_eventually h2).exists
    linarith

/-- Galí (2015), eqs. (2)–(8), pp. 18–21 (**characterisation**, deterministic infinite
horizon): for a feasible plan with positive hours whose discounted bond value converges, the
plan is optimal iff the budget binds, the static condition (7), the Euler equation (8) and the
transversality condition (6) hold. -/
theorem optimal_iff {e : Economy} {x : Plan} (hβ : 0 < e.β) (hσ : 0 < e.σ) (hφ : 0 ≤ e.φ)
    (hP : ∀ t, 0 < e.P t) (hQ : ∀ t, 0 < e.Q t) (hZ : ∀ t, 0 < e.Z t) (hx : Feasible e x)
    (hN : ∀ t, 0 < x.N t)
    (hlim : ∃ L, Tendsto (fun T => disc e.Q (T + 1) * x.B T) atTop (𝓝 L)) :
    Optimal e x ↔ BudgetBinds e x ∧ StaticFOC e x ∧ EulerDet e x ∧ Transversality e x := by
  constructor
  · intro hopt
    obtain ⟨L, hL⟩ := hlim
    have h0 := tvc_of_optimal_of_tendsto hσ hP hQ hZ hopt hL
    subst h0
    exact ⟨budgetBinds_of_optimal hβ hσ hP hZ hopt,
      fun t => staticFOC_of_optimal hβ hσ hφ hP hZ hopt t (hN t),
      eulerDet_of_optimal hβ hP hZ hopt, hL⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact optimal_of_foc e x hβ hσ hφ hP hZ hx hN h1 h2 h3 h4

/-- Galí (2015), eq. (6), p. 19, in the book's notation (date `t = 0`):
`Λ_{0,T} B_T/P_T` with `Λ_{0,T} = β^T U_{c,T}/U_{c,0}` and `U_{c,t} = Z_t C_t^{−σ}`. -/
noncomputable def bookTVCTerm (e : Economy) (x : Plan) (T : ℕ) : ℝ :=
  e.β ^ T * (e.Z T * x.C T ^ (-e.σ)) / (e.Z 0 * x.C 0 ^ (-e.σ)) * x.B T / e.P T

/-- Galí (2015), eq. (6), p. 19: along the Euler equation the book's term is
`Λ_{0,T} B_T/P_T = (∏_{s<T} Q_s) B_T / P_0`. -/
theorem bookTVCTerm_eq {e : Economy} {x : Plan} (hβ : 0 < e.β) (hP : ∀ t, 0 < e.P t)
    (hZ : ∀ t, 0 < e.Z t) (hC : ∀ t, 0 < x.C t) (heu : EulerDet e x) (T : ℕ) :
    bookTVCTerm e x T = disc e.Q T * x.B T / e.P 0 := by
  have hlam : ∀ t, lam e x (t + 1) = e.Q t * lam e x t := fun t =>
    (eulerDet_iff_lam e x t hβ (hC t) (hZ t) (hP t)).1 (heu t)
  have h := lam_eq_disc e x hlam T
  unfold lam at h
  simp only [pow_zero, one_mul] at h
  unfold bookTVCTerm
  have hc0 := Real.rpow_pos_of_pos (hC 0) (-e.σ)
  have hPT := (hP T).ne'
  have hP0 := (hP 0).ne'
  have hZ0 := (hZ 0).ne'
  have e1 : e.β ^ T * (e.Z T * x.C T ^ (-e.σ)) = e.β ^ T * e.Z T * x.C T ^ (-e.σ) / e.P T
      * e.P T := by field_simp
  rw [e1, h]
  field_simp

/-- Galí (2015), eq. (6), p. 19: with bond prices bounded, `0 < q ≤ Q_T ≤ Q̄`, the book's
transversality condition `Λ_{0,T} B_T/P_T → 0` is equivalent to `Transversality`
(`(∏_{s≤T} Q_s) B_T → 0`) along the Euler equation. -/
theorem bookTVC_iff {e : Economy} {x : Plan} (hβ : 0 < e.β) (hP : ∀ t, 0 < e.P t)
    (hZ : ∀ t, 0 < e.Z t) (hC : ∀ t, 0 < x.C t) (heu : EulerDet e x) {q Qb : ℝ} (hq : 0 < q)
    (hQl : ∀ t, q ≤ e.Q t) (hQu : ∀ t, e.Q t ≤ Qb) :
    Tendsto (bookTVCTerm e x) atTop (𝓝 0) ↔ Transversality e x := by
  have hb := bookTVCTerm_eq hβ hP hZ hC heu
  have hP0 := hP 0
  have hQ : ∀ t, 0 < e.Q t := fun t => lt_of_lt_of_le hq (hQl t)
  have hdB : ∀ T, disc e.Q (T + 1) * x.B T = e.Q T * (e.P 0 * bookTVCTerm e x T) := by
    intro T
    rw [hb, disc_succ]
    field_simp
  unfold Transversality
  simp_rw [hdB]
  constructor
  · intro h
    have h' : Tendsto (fun T => e.P 0 * bookTVCTerm e x T) atTop (𝓝 0) := by
      simpa using h.const_mul (e.P 0)
    refine squeeze_zero_norm (a := fun T => Qb * ‖e.P 0 * bookTVCTerm e x T‖) (fun T => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs (e.Q T), abs_of_pos (hQ T)]
      exact mul_le_mul_of_nonneg_right (hQu T) (norm_nonneg _)
    · simpa using (h'.norm).const_mul Qb
  · intro h
    have h' : Tendsto (fun T => e.P 0 * bookTVCTerm e x T) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun T => q⁻¹ * ‖e.Q T * (e.P 0 * bookTVCTerm e x T)‖)
        (fun T => ?_) ?_
      · rw [norm_mul (e.Q T), Real.norm_eq_abs (e.Q T), abs_of_pos (hQ T), ← mul_assoc]
        have : 1 ≤ q⁻¹ * e.Q T := by rw [le_inv_mul_iff₀ hq, mul_one]; exact hQl T
        nlinarith [norm_nonneg (e.P 0 * bookTVCTerm e x T)]
      · simpa using (h.norm).const_mul q⁻¹
    have := h'.const_mul (e.P 0)⁻¹
    simp only [mul_zero] at this
    refine this.congr fun T => ?_
    field_simp

/-- Galí (2015), fn. 3, p. 20 (deterministic): with zero bond holdings, `B_t = 0` for all `t`,
the no-Ponzi condition (3) and the transversality condition (6) both hold. -/
theorem tvc_of_zero_bonds (e : Economy) (x : Plan) (h0 : ∀ t, x.B t = 0) :
    NoPonzi e x ∧ Transversality e x ∧ Tendsto (bookTVCTerm e x) atTop (𝓝 0) := by
  refine ⟨fun ε hε => Eventually.of_forall fun T => ?_, ?_, ?_⟩
  · rw [h0, mul_zero]; linarith
  · simp only [Transversality, h0, mul_zero, tendsto_const_nhds]
  · have : bookTVCTerm e x = fun _ => 0 := by funext T; simp [bookTVCTerm, h0]
    rw [this]
    exact tendsto_const_nhds

/-- Galí (2015), fn. 3, p. 20 (under uncertainty): with zero net bond holdings,
`B_t = 0` in every state, `E_t[Λ_{t,T} B_T/P_T] = 0` for every `T`, so (6) holds at every `t`,
whatever the stochastic discount factor `Λ` and prices `P`. -/
theorem tvc_of_zero_bonds_stoch {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    (Λ : ℕ → ℕ → Ω → ℝ) (B P : ℕ → Ω → ℝ) (h0 : ∀ T ω, B T ω = 0) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => Λ t T ω' * B T ω' / P T ω') ω) atTop (𝓝 0) := by
  have : ∀ T, (fun ω' => Λ t T ω' * B T ω' / P T ω') = 0 := fun T => by
    funext ω'
    simp [h0]
  simp only [this, map_zero, Pi.zero_apply, tendsto_const_nhds]

/-! ### Log forms of the Euler equation -/

/-- Galí (2015), App. 2.1, eq. (51), p. 44: the Euler moment at node `ω`,
`E_t[exp(i_t − ρ − σ(c_{t+1} − c_t) − (p_{t+1} − p_t) + (z_{t+1} − z_t))]`, all variables
in logs, date-`t` values entering as numbers. -/
noncomputable def eulerMoment (σ ρ : ℝ) (i c p z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  𝔼.E t (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
    - (p (t + 1) ω' - p t ω) + (z (t + 1) ω' - z t ω))) ω

/-- Galí (2015), eq. (8), p. 21, and eq. (51), p. 44, **exact**: with `Q = e^{−i}`, `β = e^{−ρ}`,
`C = e^c`, `P = e^p`, `Z = e^z`, the Euler equation at date `t` is equivalent to the Euler
moment being equal to one at every node. -/
theorem eulerEq_iff_moment (σ ρ : ℝ) (i c p z : ℕ → Ω → ℝ) (t : ℕ) :
    EulerEq 𝔼 (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω)) (fun t ω => Real.exp (c t ω))
        (fun t ω => Real.exp (p t ω)) (fun t ω => Real.exp (z t ω)) t ↔
      ∀ ω, eulerMoment 𝔼 σ ρ i c p z t ω = 1 := by
  set G : Ω → ℝ := fun ω' => Real.exp (c (t + 1) ω') ^ (-σ) * Real.exp (z (t + 1) ω')
    / Real.exp (p (t + 1) ω') with hGdef
  have hmom : ∀ ω, eulerMoment 𝔼 σ ρ i c p z t ω
      = Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω) * 𝔼.E t G ω := by
    intro ω
    have hfun : (fun ω' => Real.exp (i t ω - ρ - σ * (c (t + 1) ω' - c t ω)
        - (p (t + 1) ω' - p t ω) + (z (t + 1) ω' - z t ω)))
        = Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω) • G := by
      funext ω'
      simp only [Pi.smul_apply, smul_eq_mul, hGdef]
      rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    rw [eulerMoment, hfun, map_smul, Pi.smul_apply, smul_eq_mul]
  unfold EulerEq
  refine forall_congr' fun ω => ?_
  rw [hmom ω]
  simp only
  rw [← hGdef]
  have e1 : Real.exp (c t ω) ^ σ * Real.exp (p t ω) / Real.exp (z t ω)
      = Real.exp (σ * c t ω + p t ω - z t ω) := by
    rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_sub, mul_comm (c t ω)]
  have e2 : Real.exp (i t ω - ρ + σ * c t ω + p t ω - z t ω)
      = Real.exp (i t ω) * (Real.exp (-ρ) * Real.exp (σ * c t ω + p t ω - z t ω)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [e1, e2]
  have hi : Real.exp (i t ω) * Real.exp (-i t ω) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  constructor
  · intro h
    rw [mul_assoc, ← h, hi]
  · intro h
    have hpos := Real.exp_pos (i t ω)
    have : Real.exp (-i t ω) = Real.exp (-i t ω) * (Real.exp (i t ω) *
        (Real.exp (-ρ) * Real.exp (σ * c t ω + p t ω - z t ω) * 𝔼.E t G ω)) := by
      rw [← mul_assoc (Real.exp (i t ω)), h, mul_one]
    rw [this, ← mul_assoc, mul_comm (Real.exp (-i t ω)), hi, one_mul]

/-- Galí (2015), eqs. (8) and (10), p. 21 (**exact, perfect foresight**): under perfect
foresight the Euler equation holds at date `t` iff, in logs,
`i_t − (p_{t+1} − p_t) − ρ = σ (c_{t+1} − c_t) − (z_{t+1} − z_t)`. -/
theorem pf_eulerEq_iff (σ ρ : ℝ) (i c p z : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω))
        (fun t ω => Real.exp (z t ω)) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ
        = σ * (c (t + 1) ω - c t ω) - (z (t + 1) ω - z t ω) := by
  rw [eulerEq_iff_moment]
  refine forall_congr' fun ω => ?_
  simp only [eulerMoment, perfectForesight, LinearMap.id_apply]
  rw [← Real.exp_zero, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- Galí (2015), eq. (10), p. 21 (**exact, perfect foresight, no preference shock**): with
`Z ≡ 1` the
Euler equation is exactly `i_t − π_{t+1} − ρ = σ (c_{t+1} − c_t)` in logs. -/
theorem pf_eulerEq_iff_noshock (σ ρ : ℝ) (i c p : ℕ → Unit → ℝ) (t : ℕ) :
    EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
        (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω)) (fun _ _ => 1) t ↔
      ∀ ω, i t ω - (p (t + 1) ω - p t ω) - ρ = σ * (c (t + 1) ω - c t ω) := by
  have h := pf_eulerEq_iff σ ρ i c p (fun _ _ => 0) t
  simp only [Real.exp_zero, sub_self, sub_zero] at h
  exact h

/-! ### The first-order approximation under uncertainty -/

/-- Galí (2015), App. 2.1, p. 44 (the first-order step): for a bounded random variable
`Y`, `s ↦ E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. Only linearity,
monotonicity and constants of `E_t` are used: the remainder `exp(sY) − 1 − sY` is bounded by
`s² M²` uniformly, and `|E_t x| ≤ sup |x|`. -/
theorem hasDerivAt_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω) (𝔼.E t Y ω) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  simp only [sub_zero]
  have hO : (fun s : ℝ => 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
      - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω) =O[𝓝 0]
      fun s : ℝ => s ^ 2 := by
    apply Asymptotics.IsBigO.of_bound (M ^ 2)
    have hcont : Continuous (fun s : ℝ => |s| * M) := by fun_prop
    have hlim : Tendsto (fun s : ℝ => |s| * M) (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto 0
      rwa [abs_zero, zero_mul] at this
    filter_upwards [hlim.eventually (ge_mem_nhds one_pos)] with s hs
    have key : 𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω
        - 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω - s • 𝔼.E t Y ω
        = 𝔼.E t (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω') ω := by
      have h1 : (fun ω' => Real.exp (s * Y ω') - 1 - s * Y ω')
          = (fun ω' => Real.exp (s * Y ω')) - (fun _ => (1 : ℝ)) - s • Y := by
        funext ω'
        simp
      have h2 : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
        funext ω'
        simp
      rw [h1, h2, map_sub, map_sub, map_smul, 𝔼.const]
      simp
    rw [key, Real.norm_eq_abs, Real.norm_eq_abs]
    apply 𝔼.abs_E_le
    intro ω'
    have hy : |s * Y ω'| ≤ 1 := by
      rw [abs_mul]
      calc |s| * |Y ω'| ≤ |s| * M := mul_le_mul_of_nonneg_left (hY ω') (abs_nonneg s)
        _ ≤ 1 := hs
    have hsq : (s * Y ω') ^ 2 ≤ M ^ 2 * |s ^ 2| := by
      rw [abs_pow, sq_abs, mul_pow, mul_comm]
      have : Y ω' ^ 2 ≤ M ^ 2 := by
        have := hY ω'
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg s)
    exact (Real.abs_exp_sub_one_sub_id_le hy).trans hsq
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id one_lt_two)

/-- Galí (2015), App. 2.1, p. 44: for a bounded `Y`,
`s ↦ log E_t[exp(s Y)](ω)` has derivative `E_t Y (ω)` at `s = 0`. -/
theorem hasDerivAt_log_E_exp {Y : Ω → ℝ} {M : ℝ} (hY : ∀ ω, |Y ω| ≤ M) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (𝔼.E t (fun ω' => Real.exp (s * Y ω')) ω))
      (𝔼.E t Y ω) 0 := by
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * Y ω')) ω = 1 := by
    have : (fun ω' => Real.exp (0 * Y ω')) = fun _ => (1 : ℝ) := by
      funext ω'
      simp
    rw [this, 𝔼.const]
  have := (hasDerivAt_E_exp 𝔼 hY t ω).log (by rw [h1]; exact one_ne_zero)
  rw [h1, div_one] at this
  exact this

/-! ### The log-linear Euler equation (10) as an exact derivative -/

/-- Galí (2015), App. 2.1, p. 44: the map
`(i, Δc, π, Δz) ↦ exp(i − σ Δc − π − ρ + Δz)` whose conditional expectation is one in
eq. (51). -/
noncomputable def eulerKernel (σ ρ : ℝ) (v : Fin 4 → ℝ) : ℝ :=
  Real.exp (v 0 - σ * v 1 - v 2 - ρ + v 3)

/-- Galí (2015), App. 2.1, p. 44: the perfect-foresight steady state with inflation `π̄` and
consumption growth `γ`, `(i, Δc, π, Δz) = (ρ + π̄ + σγ, γ, π̄, 0)`. -/
noncomputable def steadyPoint (σ ρ πbar γ : ℝ) : Fin 4 → ℝ := ![ρ + πbar + σ * γ, γ, πbar, 0]

/-- Galí (2015), App. 2.1, p. 44: the gradient `(1, −σ, −1, 1)` of `eulerKernel` at the steady
state, as a continuous linear functional. -/
noncomputable def eulerGrad (σ : ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0 - σ • ContinuousLinearMap.proj 1 - ContinuousLinearMap.proj 2
    + ContinuousLinearMap.proj 3

/-- Galí (2015), App. 2.1, p. 44: `eulerGrad σ v = v₀ − σ v₁ − v₂ + v₃`. -/
theorem eulerGrad_apply (σ : ℝ) (v : Fin 4 → ℝ) : eulerGrad σ v = v 0 - σ * v 1 - v 2 + v 3 :=
  rfl

/-- Galí (2015), App. 2.1, p. 44: the steady state `i = ρ + π̄ + σγ` satisfies (51) exactly,
`exp(i − σγ − π̄ − ρ + 0) = 1`. -/
theorem eulerKernel_steady (σ ρ πbar γ : ℝ) : eulerKernel σ ρ (steadyPoint σ ρ πbar γ) = 1 := by
  have h0 : steadyPoint σ ρ πbar γ 0 = ρ + πbar + σ * γ := rfl
  have h1 : steadyPoint σ ρ πbar γ 1 = γ := rfl
  have h2 : steadyPoint σ ρ πbar γ 2 = πbar := rfl
  have h3 : steadyPoint σ ρ πbar γ 3 = 0 := rfl
  simp only [eulerKernel, h0, h1, h2, h3]
  rw [← Real.exp_zero]
  congr 1
  ring

/-- Galí (2015), App. 2.1, p. 44 (**the first-order Taylor expansion as an exact derivative**):
`eulerKernel` has Fréchet derivative `(1, −σ, −1, 1)` at the steady state, i.e. value `1` and
gradient `(1, −σ, −1, 1)` — the coefficients of the book's expansion. -/
theorem hasFDerivAt_eulerKernel (σ ρ πbar γ : ℝ) :
    HasFDerivAt (eulerKernel σ ρ) (eulerGrad σ) (steadyPoint σ ρ πbar γ) := by
  have hfun : eulerKernel σ ρ = fun v => Real.exp (eulerGrad σ v - ρ) := by
    funext v
    simp only [eulerKernel, eulerGrad_apply]
    congr 1
    ring
  have h := ((eulerGrad σ).hasFDerivAt (x := steadyPoint σ ρ πbar γ)).sub_const ρ |>.exp
  rw [hfun]
  have h1 : Real.exp (eulerGrad σ (steadyPoint σ ρ πbar γ) - ρ) = 1 := by
    have := eulerKernel_steady σ ρ πbar γ
    rw [hfun] at this
    exact this
  rw [h1, one_smul] at h
  exact h

/-- Galí (2015), App. 2.1, p. 44: the first-order approximation
`1 + (i − i*) − σ(Δc − γ) − (π − π̄) + Δz` equals `1 + i − σΔc − π − ρ + Δz` (the book's second
line), since `i* = ρ + π̄ + σγ`. -/
theorem eulerKernel_linearisation (σ ρ πbar γ : ℝ) (v : Fin 4 → ℝ) :
    eulerKernel σ ρ (steadyPoint σ ρ πbar γ) + eulerGrad σ (v - steadyPoint σ ρ πbar γ)
      = 1 + v 0 - σ * v 1 - v 2 - ρ + v 3 := by
  have h0 : steadyPoint σ ρ πbar γ 0 = ρ + πbar + σ * γ := rfl
  have h1 : steadyPoint σ ρ πbar γ 1 = γ := rfl
  have h2 : steadyPoint σ ρ πbar γ 2 = πbar := rfl
  have h3 : steadyPoint σ ρ πbar γ 3 = 0 := rfl
  rw [eulerKernel_steady, eulerGrad_apply]
  simp only [Pi.sub_apply, h0, h1, h2, h3]
  ring

/-- Galí (2015), App. 2.1, p. 44: along the family of paths `i = ρ + π̄ + σγ + s î`,
`c_t = c̄ + γ t + s ĉ_t`, `p_t = p̄ + π̄ t + s p̂_t`, `z = s ẑ` around the steady state with
inflation `π̄` and growth `γ`, the Euler moment is `E_t[exp(s Y)]` for the deviation
`Y = î_t + σ ĉ_t + p̂_t − ẑ_t − σ ĉ_{t+1} − p̂_{t+1} + ẑ_{t+1}`. -/
theorem eulerMoment_family (σ ρ πbar γ cbar pbar s : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    eulerMoment 𝔼 σ ρ (fun t ω => ρ + πbar + σ * γ + s * ih t ω)
      (fun t ω => cbar + γ * t + s * ch t ω) (fun t ω => pbar + πbar * t + s * ph t ω)
      (fun t ω => s * zh t ω) t ω
    = 𝔼.E t (fun ω' => Real.exp (s * (ih t ω + σ * ch t ω + ph t ω - zh t ω
        - σ * ch (t + 1) ω' - ph (t + 1) ω' + zh (t + 1) ω'))) ω := by
  unfold eulerMoment
  refine congrArg (fun x => 𝔼.E t x ω) (funext fun ω' => ?_)
  congr 1
  push_cast
  ring

/-- Galí (2015), App. 2.1, p. 44: the steady state with inflation `π̄`, growth `γ` and
`i = ρ + π̄ + σγ` satisfies the Euler equation (51): the Euler moment is one at `s = 0`. -/
theorem eulerMoment_family_zero (σ ρ πbar γ cbar pbar : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) :
    eulerMoment 𝔼 σ ρ (fun t ω => ρ + πbar + σ * γ + 0 * ih t ω)
      (fun t ω => cbar + γ * t + 0 * ch t ω) (fun t ω => pbar + πbar * t + 0 * ph t ω)
      (fun t ω => 0 * zh t ω) t ω = 1 := by
  rw [eulerMoment_family]
  simp only [zero_mul, Real.exp_zero]
  exact congrFun (𝔼.const t 1) ω

/-- Galí (2015), eq. (10), p. 21: the linear expression obtained by linearising the Euler
moment, in deviations (hats): `î_t − σ (E_t ĉ_{t+1} − ĉ_t) − (E_t p̂_{t+1} − p̂_t)
+ (E_t ẑ_{t+1} − ẑ_t)` (restated from the Chapter 3 project). -/
noncomputable def linearisedEuler (σ : ℝ) (ih ch ph zh : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ih t ω - σ * (𝔼.E t (ch (t + 1)) ω - ch t ω) - (𝔼.E t (ph (t + 1)) ω - ph t ω)
    + (𝔼.E t (zh (t + 1)) ω - zh t ω)

/-- Galí (2015), eq. (10), p. 21, and App. 2.1, p. 44 (**exact derivative under
uncertainty**): along the family of `eulerMoment_family` with bounded deviations, the log
Euler residual `s ↦ log E_t[exp(i_t − ρ − σΔc − Δp + Δz)](ω)` has derivative at `s = 0` equal
to `linearisedEuler σ î ĉ p̂ ẑ t ω`. -/
theorem hasDerivAt_log_eulerMoment_family (σ ρ πbar γ cbar pbar : ℝ)
    {ih ch ph zh : ℕ → Ω → ℝ} (hc : BoundedProc ch) (hp : BoundedProc ph)
    (hz : BoundedProc zh) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s : ℝ => Real.log (eulerMoment 𝔼 σ ρ
        (fun t ω => ρ + πbar + σ * γ + s * ih t ω) (fun t ω => cbar + γ * t + s * ch t ω)
        (fun t ω => pbar + πbar * t + s * ph t ω) (fun t ω => s * zh t ω) t ω))
      (linearisedEuler 𝔼 σ ih ch ph zh t ω) 0 := by
  obtain ⟨Mc, hMc⟩ := hc
  obtain ⟨Mp, hMp⟩ := hp
  obtain ⟨Mz, hMz⟩ := hz
  set a : ℝ := ih t ω + σ * ch t ω + ph t ω - zh t ω with ha
  set Y : Ω → ℝ := fun ω' => ih t ω + σ * ch t ω + ph t ω - zh t ω
    - σ * ch (t + 1) ω' - ph (t + 1) ω' + zh (t + 1) ω' with hY
  have hbd : ∀ ω', |Y ω'| ≤ |a| + |σ| * Mc + Mp + Mz := by
    intro ω'
    have h1 := abs_le.1 (show |σ * ch (t + 1) ω'| ≤ |σ| * Mc by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMc _ _) (abs_nonneg σ))
    have h2 := abs_le.1 (hMp (t + 1) ω')
    have h3 := abs_le.1 (hMz (t + 1) ω')
    have h4 := abs_le.1 (le_refl |a|)
    rw [abs_le]
    simp only [hY]
    constructor <;> linarith
  simp_rw [eulerMoment_family]
  have hval : 𝔼.E t Y ω = linearisedEuler 𝔼 σ ih ch ph zh t ω := by
    have hfun : Y = (fun _ => a) + ((-σ) • ch (t + 1) - ph (t + 1) + zh (t + 1)) := by
      funext ω'
      simp only [hY, ha, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, map_add, 𝔼.const, map_add, map_sub, map_smul]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, linearisedEuler, ha]
    ring
  rw [← hval]
  exact hasDerivAt_log_E_exp 𝔼 hbd t ω

/-- Galí (2015), eq. (10), p. 21: the log-linear Euler equation as a model equation,
`c_t = E_t c_{t+1} − σ⁻¹ (i_t − E_t π_{t+1} − ρ) + σ⁻¹ (1 − ρ_z) z_t` (restated from the
Chapter 3 project). -/
def EulerLogLinear (σ ρ ρz : ℝ) (c i infl z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, c t = 𝔼.E t (c (t + 1)) - σ⁻¹ • (i t - 𝔼.E t (infl (t + 1)) - fun _ => ρ)
    + (σ⁻¹ * (1 - ρz)) • z t

/-- Galí (2015), eq. (10), p. 21: for an adapted (log) price level `p̂` with inflation
`π̂_{t+1} = p̂_{t+1} − p̂_t`, the linearised Euler expression is
`î_t − σ (E_t ĉ_{t+1} − ĉ_t) − E_t π̂_{t+1} + (E_t ẑ_{t+1} − ẑ_t)`. -/
theorem linearisedEuler_eq (σ : ℝ) {ih ch ph zh infl : ℕ → Ω → ℝ} (hp : 𝔼.Adapted ph)
    (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t) (t : ℕ) :
    linearisedEuler 𝔼 σ ih ch ph zh t = ih t - σ • (𝔼.E t (ch (t + 1)) - ch t)
      - 𝔼.E t (infl (t + 1)) + (𝔼.E t (zh (t + 1)) - zh t) := by
  funext ω
  rw [hinfl, map_sub, hp t]
  simp [linearisedEuler]

/-- Galí (2015), eq. (10), p. 21 (**the first-order condition is exactly (10)**): for
`σ ≠ 0`, an adapted price level and an AR(1) preference shifter (`E_t ẑ_{t+1} = ρ_z ẑ_t`,
p. 21), the derivative of `hasDerivAt_log_eulerMoment_family` vanishes at every date and node
iff (10) holds for the levels `c_t = c̄ + γ t + ĉ_t`, `i_t = ρ + π̄ + σγ + î_t`,
`π_{t+1} = π̄ + π̂_{t+1}`, `z = ẑ`. -/
theorem linearisedEuler_eq_zero_iff {σ ρ ρz πbar γ cbar : ℝ} (hσ : σ ≠ 0)
    {ih ch ph zh infl : ℕ → Ω → ℝ} (hp : 𝔼.Adapted ph)
    (hinfl : ∀ t, infl (t + 1) = ph (t + 1) - ph t) (hzar : 𝔼.IsAR1 ρz zh) :
    (∀ t, linearisedEuler 𝔼 σ ih ch ph zh t = 0) ↔
      EulerLogLinear 𝔼 σ ρ ρz (fun t => (fun _ => cbar + γ * t) + ch t)
        (fun t => (fun _ => ρ + πbar + σ * γ) + ih t) (fun t => (fun _ => πbar) + infl t) zh := by
  unfold EulerLogLinear
  refine forall_congr' fun t => ?_
  rw [linearisedEuler_eq 𝔼 σ hp hinfl t, hzar.2 t]
  simp only [map_add, 𝔼.const]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    push_cast
    field_simp
    linear_combination e
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    push_cast at e
    field_simp at e
    linear_combination e

/-- Galí (2015), eq. (10), p. 21 (**exact under perfect foresight**): if the nonlinear Euler
equation holds at every date, `π_{t+1} = p_{t+1} − p_t`, and the preference shifter follows
`z_{t+1} = ρ_z z_t`, then (10) holds exactly (`σ ≠ 0`). -/
theorem pf_eulerEq_imp_eulerLogLinear {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {i c p z infl : ℕ → Unit → ℝ}
    (heul : ∀ t, EulerEq perfectForesight (Real.exp (-ρ)) σ (fun t ω => Real.exp (-i t ω))
      (fun t ω => Real.exp (c t ω)) (fun t ω => Real.exp (p t ω))
      (fun t ω => Real.exp (z t ω)) t)
    (hinfl : ∀ t, infl (t + 1) = p (t + 1) - p t) (hz : ∀ t, z (t + 1) = ρz • z t) :
    EulerLogLinear perfectForesight σ ρ ρz c i infl z := by
  intro t
  have h := (pf_eulerEq_iff σ ρ i c p z t).1 (heul t)
  funext ω
  have e := h ω
  have ez := congrFun (hz t) ω
  have ei := congrFun (hinfl t) ω
  simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at e ez ei ⊢
  rw [ei]
  rw [ez] at e
  field_simp
  linear_combination e

/-! ### Footnote 5: the discount rate -/

/-- Galí (2015), fn. 5, p. 22: `ρ = −log β ≤ β⁻¹ − 1` for `β > 0`. -/
theorem neg_log_le_inv_sub_one {β : ℝ} (hβ : 0 < β) : -Real.log β ≤ β⁻¹ - 1 := by
  have := Real.log_le_sub_one_of_pos (inv_pos.2 hβ)
  rwa [Real.log_inv] at this

/-- Galí (2015), fn. 5, p. 22: the gap in `ρ ≃ β⁻¹ − 1` is second order:
`0 ≤ (β⁻¹ − 1) − (−log β) ≤ (1 − β)²/β` for every `β > 0`. -/
theorem discount_rate_gap {β : ℝ} (hβ : 0 < β) :
    0 ≤ (β⁻¹ - 1) - (-Real.log β) ∧ (β⁻¹ - 1) - (-Real.log β) ≤ (1 - β) ^ 2 / β := by
  refine ⟨by linarith [neg_log_le_inv_sub_one hβ], ?_⟩
  have h := Real.log_le_sub_one_of_pos hβ
  have e : (1 - β) ^ 2 / β = β⁻¹ - 1 + (β - 1) := by field_simp; ring
  rw [e]
  linarith

/-- Galí (2015), fn. 5, p. 22: `(β⁻¹ − 1) − (−log β) = O((1 − β)²)` as `β → 1`. -/
theorem discount_rate_gap_isBigO :
    (fun β : ℝ => (β⁻¹ - 1) - (-Real.log β)) =O[𝓝 1] fun β => (1 - β) ^ 2 := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [lt_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num)] with β hβ
  have hβ0 : 0 < β := by linarith
  obtain ⟨h1, h2⟩ := discount_rate_gap hβ0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg (sq_nonneg _)]
  refine h2.trans ?_
  rw [div_le_iff₀ hβ0]
  nlinarith [sq_nonneg (1 - β)]

/-! ### Money demand (11) -/

/-- Galí (2015), eq. (11), p. 22: the log-linear money demand `m_t − p_t = c_t − η i_t`
(up to an additive constant, set to zero), with interest semielasticity `η ≥ 0`. -/
def MoneyDemand (η : ℝ) (m p c i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, m t - p t = c t - η • i t

/-- Galí (2015), eq. (11), p. 22: money demand pins down the price level given money,
consumption and the nominal rate: `p_t = m_t − c_t + η i_t`. -/
theorem moneyDemand_iff_price (η : ℝ) (m p c i : ℕ → Ω → ℝ) :
    MoneyDemand η m p c i ↔ ∀ t, p t = m t - c t + η • i t := by
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> funext ω <;> have e := congrFun h ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢ <;> linarith

/-- Galí (2015), eq. (11), p. 22: `η` is the interest semielasticity of real balances,
`∂(m − p)/∂i = −η`. -/
theorem moneyDemand_semielasticity (η c : ℝ) (i : ℝ) :
    HasDerivAt (fun i' : ℝ => c - η * i') (-η) i := by
  simpa using ((hasDerivAt_id i).const_mul η).const_sub c

end Gali.ClassicalMonetaryModel.Household
