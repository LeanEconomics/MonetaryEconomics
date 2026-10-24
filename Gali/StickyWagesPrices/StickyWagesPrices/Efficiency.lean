/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.LaborAggregation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The efficient allocation with goods and labour types

Galí (2015), Chapter 6, §6.3, pp. 178–179, eqs. (25)–(27).

The planner maximises period utility `U(C, {N(j)}; Z) = (u(C) − ∫ N(j)^{1+φ}/(1+φ) dj) Z`
(the book's utility of p. 167, `u(C) = (C^{1−σ} − 1)/(1 − σ)` or `log C`) where
`C = (∫ C(i)^{(ε_p−1)/ε_p} di)^{ε_p/(ε_p−1)}` is the CES consumption index, each good is produced
with `C(i) = A N(i)^{1−α}` (eq. (1)), the labour input of firm `i` is the CES index
`N(i) = (∫ N(i,j)^{(ε_w−1)/ε_w} dj)^{ε_w/(ε_w−1)}` of the labour types (eq. (2)), and the
supply of type `j` is `N(j) = ∫ N(i,j) di` (market clearing).

Goods are indexed by a probability space `(G, μ)` and labour types by a probability space
`(J, ν)`; an allocation is a jointly measurable `N(·,·) ≥ 0` on `G × J`, integrable for the
product measure, with integrable disutility and positive total hours `∫∫ N(i,j)`
(`Planner.Feasible`). The book's continuum `[0, 1] × [0, 1]` is
`Planner.planner_optimal_iff_unitInterval`.

## Main results

* `Planner.labourIndex_le_firmHours`: the labour index of each firm is at most its total hours
  (power-mean inequality in the labour-type dimension), with equality iff hours are equal
  across types (`cesIndex_eq_integral_iff`).
* `Planner.aggConsumption_le`, `Planner.aggConsumption_eq_iff`: for total hours `L`, the
  consumption index is at most `A L^{1−α}`, with equality **iff** `N(i,j) = L` for a.e.
  `(i, j)` (both CES dimensions at once).
* `Planner.disutility_ge`: `∫ N(j)^{1+φ}/(1+φ) ≥ L^{1+φ}/(1+φ)` (Jensen).
* `Planner.welfare_le_symWelfare`, `Planner.welfare_eq_symWelfare_iff`: welfare is at most the
  welfare of the symmetric allocation with the same total hours, with equality iff symmetric.
* `symWelfare_isMax_iff_foc`: along symmetric allocations `MRS = MPN` (27) is **necessary and
  sufficient**; `existsUnique_efficient`: it has exactly one solution `N*` (`effEmployment`).
* `Planner.planner_optimal_iff`: a feasible allocation is optimal **iff** (25) `C(i) = C`,
  (26) `N(i,j) = N(j) = N(i) = N` and (27) `MRS = MPN`, a.e.;
  `Planner.planner_optimal_iff_effEmployment`, `Planner.planner_existsUnique`: iff
  `N(i,j) = N*` a.e., and the optimum exists and is unique up to null sets.
* `flex_mrs_eq`, `flex_equilibrium`: in the flexible-price-and-wage equilibrium
  (`W/P = M_w MRS`, `P = M_p (1 − τ) W/MPN`), `MRS = MPN/((1 − τ) M_p M_w)` and employment is
  `N((1 − τ) M_p M_w)`; `flex_equilibrium_efficient_iff`: it is efficient **iff**
  `τ = 1 − 1/(M_p M_w)`; `existsUnique_subsidy`: this subsidy exists, is unique, and lies in
  `(0, 1)`; `optimalSubsidy_flexWages` recovers Chapter 4's `τ = 1/ε_p` when `M_w = 1`.

Utility definitions, tangent-line lemmas, the symmetric problem and `flexEmployment` are restated
from the Chapter 4 project (`Efficient.lean`, `Distortions.lean`). The CES aggregator is
`LaborAggregation.laborIndex` (used both for goods, `ε = ε_p`, and labour types, `ε = ε_w`).
-/

namespace Gali.StickyWagesPrices.Efficiency

open MeasureTheory Filter Topology

/-! ### Period utility (restated from the Chapter 4 project) -/

/-- Galí (2015), p. 167: utility of consumption, `(C^{1−σ} − 1)/(1 − σ)` for `σ ≠ 1` and
`log C` for `σ = 1`. Restated from the Chapter 4 project. -/
noncomputable def utilC (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 167: disutility of labour of one type, `N^{1+φ}/(1+φ)`. Restated from the
Chapter 4 project. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 167, evaluated at a symmetric allocation `N(j) = N`: period utility
`U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z`. Restated from the Chapter 4 project. -/
noncomputable def periodUtility (σ φ C N Z : ℝ) : ℝ := (utilC σ C - disutilN φ N) * Z

/-- Galí (2015), p. 178: marginal utility of consumption `u'(C) = C^{−σ}`. Restated from the
Chapter 4 project. -/
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

/-- Galí (2015), p. 178: marginal disutility of labour `N^φ`. Restated from the Chapter 4
project. -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 178 (concavity of utility): marginal utility `C^{−σ}` is nonincreasing for
`σ > 0`. Restated from the Chapter 4 project. -/
theorem antitoneOn_margUtil {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun C : ℝ => C ^ (-σ)) (Set.Ioi 0) :=
  fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its tangent
lines (Galí (2015), p. 178, concavity of utility). Restated from the Chapter 4 project. -/
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

/-- Galí (2015), p. 178: the utility of consumption is concave for `σ > 0`, in tangent-line
form `u(y) ≤ u(x) + x^{−σ}(y − x)`. Restated from the Chapter 4 project. -/
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

/-- Galí (2015), p. 178: the disutility of labour is convex for `φ ≥ 0`, in tangent-line form
`v(x) + x^φ (y − x) ≤ v(y)`. Restated from the Chapter 4 project. -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), p. 178 (`U_c > 0`): the utility of consumption is strictly increasing on
`(0, ∞)`. Restated from the Chapter 4 project. -/
theorem utilC_lt_utilC {σ : ℝ} {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    utilC σ x < utilC σ y := by
  unfold utilC
  by_cases h1 : σ = 1
  · simp only [h1, ↓reduceIte]
    exact Real.log_lt_log hx hxy
  · simp only [h1, ↓reduceIte]
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hs : 0 < 1 - σ := by linarith
      have := Real.rpow_lt_rpow hx.le hxy hs
      exact div_lt_div_of_pos_right (by linarith) hs
    · have hs : 1 - σ < 0 := by linarith
      have := Real.rpow_lt_rpow_of_neg hx hxy hs
      exact (div_lt_div_right_of_neg hs).2 (by linarith)

/-- Galí (2015), eq. (27), p. 178: the marginal utilities `U_c = C^{−σ} Z`, `U_n = −N^φ Z`
(exact derivatives along a symmetric allocation), whose ratio is the marginal rate of
substitution `−U_n/U_c = C^σ N^φ`. -/
theorem marginal_utilities {σ φ C N Z : ℝ} (hφ : 0 ≤ φ) (hC : 0 < C) (hZ : 0 < Z) :
    HasDerivAt (fun c => periodUtility σ φ c N Z) (C ^ (-σ) * Z) C ∧
      HasDerivAt (fun n => periodUtility σ φ C n Z) (-(N ^ φ) * Z) N ∧
      -(-(N ^ φ) * Z) / (C ^ (-σ) * Z) = C ^ σ * N ^ φ := by
  refine ⟨((hasDerivAt_utilC σ hC).sub_const _).mul_const Z, ?_, ?_⟩
  · have h := ((hasDerivAt_disutilN hφ N).const_sub (utilC σ C)).mul_const Z
    simpa [periodUtility] using h
  · have hc : 0 < C ^ (-σ) := Real.rpow_pos_of_pos hC _
    rw [Real.rpow_neg hC.le] at hc ⊢
    field_simp

/-! ### MRS, MPN and a tangent bound for powers -/

/-- Galí (2015), eq. (27), p. 178: the marginal rate of substitution `−U_n/U_c = C^σ N^φ`
(`marginal_utilities`). -/
noncomputable def mrs (σ φ C N : ℝ) : ℝ := C ^ σ * N ^ φ

/-- Galí (2015), p. 178: the marginal product of labour `MPN = (1 − α) A N^{−α}`. -/
noncomputable def mpn (α A N : ℝ) : ℝ := (1 - α) * A * N ^ (-α)

/-- Galí (2015), p. 178: `MPN` is the derivative of the technology `A N^{1−α}`. -/
theorem hasDerivAt_output {α A N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n => A * n ^ (1 - α)) (mpn α A N) N := by
  refine ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A).congr_deriv ?_
  rw [mpn, show (1 : ℝ) - α - 1 = -α by ring]
  ring

/-- Galí (2015), p. 178: `MPN > 0` for `α < 1`, `A > 0`, `N > 0`. -/
theorem mpn_pos {α A N : ℝ} (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) : 0 < mpn α A N :=
  mul_pos (mul_pos (by linarith) hA) (Real.rpow_pos_of_pos hN _)

/-- Concavity of `x ↦ x^q` for `0 ≤ q ≤ 1` (Bernoulli), in tangent form at `N > 0`:
`x^q ≤ N^q (1 + q (x/N − 1))` (Galí (2015), p. 178, concavity of the aggregators and of
technology). Restated from the Chapter 4 project. -/
theorem rpow_le_tangent {q x N : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hN : 0 < N) (hx : 0 ≤ x) :
    x ^ q ≤ N ^ q * (1 + q * (x / N - 1)) := by
  have hs : -1 ≤ x / N - 1 := by have := div_nonneg hx hN.le; linarith
  have h := rpow_one_add_le_one_add_mul_self hs hq0 hq1
  rw [add_sub_cancel, Real.div_rpow hx hN.le] at h
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN q
  rw [div_le_iff₀ hNq] at h
  linarith

/-- Strict concavity of `x ↦ x^q` for `0 < q < 1`: equality in `rpow_le_tangent` forces
`x = N` (Galí (2015), p. 178). Restated from the Chapter 4 project. -/
theorem eq_of_rpow_eq_tangent {q x N : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hN : 0 < N)
    (hx : 0 ≤ x) (h : x ^ q = N ^ q * (1 + q * (x / N - 1))) : x = N := by
  by_contra hne
  have hs : -1 ≤ x / N - 1 := by have := div_nonneg hx hN.le; linarith
  have hs' : x / N - 1 ≠ 0 := by
    intro h0
    apply hne
    have : x / N = 1 := by linarith
    rwa [div_eq_one_iff_eq hN.ne'] at this
  have hlt := rpow_one_add_lt_one_add_mul_self hs hs' hq0 hq1
  rw [add_sub_cancel, Real.div_rpow hx hN.le] at hlt
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN q
  rw [div_lt_iff₀ hNq] at hlt
  linarith

/-! ### The symmetric problem: condition (27) -/

/-- Galí (2015), p. 178: welfare of the symmetric allocation `N(i,j) = N` (so `C = A N^{1−α}`
and `N(j) = N`), `U(A N^{1−α}, N; Z)`. -/
noncomputable def symWelfare (σ φ α A Z N : ℝ) : ℝ := periodUtility σ φ (A * N ^ (1 - α)) N Z

/-- Galí (2015), p. 178: the efficient level of employment, the solution of (27) with
`C = A N^{1−α}`: `N* = ((1 − α) A^{1−σ})^{1/(φ + α + σ(1 − α))}`. -/
noncomputable def effEmployment (σ φ α A : ℝ) : ℝ :=
  ((1 - α) * A ^ (1 - σ)) ^ (φ + α + σ * (1 - α))⁻¹

/-- Galí (2015), p. 178: the derivative of symmetric welfare, `(C^{−σ} MPN − N^φ) Z` with
`C = A N^{1−α}`. -/
theorem hasDerivAt_symWelfare {σ φ α A Z N : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A) (hN : 0 < N) :
    HasDerivAt (symWelfare σ φ α A Z)
      (((A * N ^ (1 - α)) ^ (-σ) * mpn α A N - N ^ φ) * Z) N := by
  have hC : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have h1 := (hasDerivAt_utilC σ hC).comp N (hasDerivAt_output (α := α) (A := A) hN)
  exact (HasDerivAt.sub h1 (hasDerivAt_disutilN hφ N)).mul_const Z

/-- Galí (2015), p. 178 (exponent bookkeeping): `MRS(A N^{1−α}, N) · (1 − α) A^{1−σ}
= MPN(N) · N^{φ + α + σ(1 − α)}`. -/
theorem mrs_mul_eq {σ φ α A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    mrs σ φ (A * N ^ (1 - α)) N * ((1 - α) * A ^ (1 - σ))
      = mpn α A N * N ^ (φ + α + σ * (1 - α)) := by
  have e1 : (A * N ^ (1 - α)) ^ σ = A ^ σ * N ^ ((1 - α) * σ) := by
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le]
  calc mrs σ φ (A * N ^ (1 - α)) N * ((1 - α) * A ^ (1 - σ))
      = (1 - α) * (A ^ σ * A ^ (1 - σ)) * (N ^ ((1 - α) * σ) * N ^ φ) := by
        rw [mrs, e1]; ring
    _ = (1 - α) * A * N ^ ((1 - α) * σ + φ) := by
        rw [← Real.rpow_add hA, ← Real.rpow_add hN]
        norm_num
    _ = (1 - α) * A * (N ^ (-α) * N ^ (φ + α + σ * (1 - α))) := by
        rw [← Real.rpow_add hN, show -α + (φ + α + σ * (1 - α)) = (1 - α) * σ + φ by ring]
    _ = mpn α A N * N ^ (φ + α + σ * (1 - α)) := by rw [mpn]; ring

/-- Galí (2015), p. 178: the exponent `φ + α + σ(1 − α)` is positive. -/
theorem effExponent_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < φ + α + σ * (1 - α) := by
  have := mul_pos hσ (by linarith : (0 : ℝ) < 1 - α)
  linarith

/-- Galí (2015), p. 178: efficient employment is positive. -/
theorem effEmployment_pos {σ φ α A : ℝ} (hα1 : α < 1) (hA : 0 < A) :
    0 < effEmployment σ φ α A :=
  Real.rpow_pos_of_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) _

/-- Galí (2015), eq. (27), p. 178, **existence and uniqueness**: along the symmetric allocation
`C = A N^{1−α}`, `MRS = MPN` holds for `N > 0` iff `N = N*`. -/
theorem mrs_sym_eq_mpn_iff {σ φ α A N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) :
    mrs σ φ (A * N ^ (1 - α)) N = mpn α A N ↔ N = effEmployment σ φ α A := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
  have hm := mpn_pos hα1 hA hN
  have key := mrs_mul_eq (σ := σ) (φ := φ) (α := α) hA hN
  constructor
  · intro h
    rw [h] at key
    have hNk : N ^ (φ + α + σ * (1 - α)) = (1 - α) * A ^ (1 - σ) :=
      (mul_left_cancel₀ hm.ne' key).symm
    rw [effEmployment, ← hNk, Real.rpow_rpow_inv hN.le hk.ne']
  · intro h
    have hNk : N ^ (φ + α + σ * (1 - α)) = (1 - α) * A ^ (1 - σ) := by
      rw [h, effEmployment, Real.rpow_inv_rpow hc.le hk.ne']
    rw [hNk] at key
    exact mul_right_cancel₀ hc.ne' key

/-- Galí (2015), eq. (27), p. 178, **sufficiency**: if `MRS = MPN` at `N₀ > 0` (symmetric
allocation), then `N₀` maximises welfare over all `N > 0`. -/
theorem symWelfare_le_of_foc {σ φ α A Z N₀ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) (hN₀ : 0 < N₀)
    (hfoc : mrs σ φ (A * N₀ ^ (1 - α)) N₀ = mpn α A N₀) {N : ℝ} (hN : 0 < N) :
    symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z N₀ := by
  set x := A * N₀ ^ (1 - α) with hxdef
  set y := A * N ^ (1 - α) with hydef
  have hx : 0 < x := mul_pos hA (Real.rpow_pos_of_pos hN₀ _)
  have hy : 0 < y := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have h1 := utilC_le_tangent hσ hx hy
  have h3 := disutilN_tangent_le hφ hN₀ hN.le
  have h2 := rpow_le_tangent (q := 1 - α) (by linarith) (by linarith) hN₀ hN.le
  have hyx : y - x ≤ mpn α A N₀ * (N - N₀) := by
    have e : mpn α A N₀ * (N - N₀) = A * (N₀ ^ (1 - α) * ((1 - α) * (N / N₀ - 1))) := by
      rw [mpn, Real.rpow_neg hN₀.le, Real.rpow_sub hN₀, Real.rpow_one]
      field_simp
    rw [e, hydef, hxdef]
    nlinarith
  have hxs : 0 < x ^ (-σ) := Real.rpow_pos_of_pos hx _
  have hfoc' : x ^ (-σ) * mpn α A N₀ = N₀ ^ φ := by
    rw [← hfoc, mrs, ← mul_assoc, Real.rpow_neg hx.le, inv_mul_cancel₀
      (Real.rpow_pos_of_pos hx σ).ne', one_mul]
  have h4 : x ^ (-σ) * (y - x) ≤ N₀ ^ φ * (N - N₀) := by
    rw [← hfoc', mul_assoc]
    exact mul_le_mul_of_nonneg_left hyx hxs.le
  unfold symWelfare periodUtility
  rw [← hxdef, ← hydef]
  exact mul_le_mul_of_nonneg_right (by linarith) hZ.le

/-- Galí (2015), eq. (27), p. 178, **necessity**: if `N₀ > 0` maximises symmetric welfare over
`N > 0`, then `MRS = MPN` at `N₀`. -/
theorem foc_of_symWelfare_isMax {σ φ α A Z N₀ : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A) (hZ : 0 < Z)
    (hN₀ : 0 < N₀) (hmax : ∀ N, 0 < N → symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z N₀) :
    mrs σ φ (A * N₀ ^ (1 - α)) N₀ = mpn α A N₀ := by
  have hloc : IsLocalMax (symWelfare σ φ α A Z) N₀ :=
    Filter.mem_of_superset (Ioi_mem_nhds hN₀) fun N hN => hmax N hN
  have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_symWelfare hφ hA hN₀)
  set x := A * N₀ ^ (1 - α) with hxdef
  have hx : 0 < x := mul_pos hA (Real.rpow_pos_of_pos hN₀ _)
  have h1 : x ^ (-σ) * mpn α A N₀ = N₀ ^ φ := by
    rcases mul_eq_zero.1 h0 with h | h
    · linarith
    · exact absurd h hZ.ne'
  have hxs : x ^ σ ≠ 0 := (Real.rpow_pos_of_pos hx σ).ne'
  rw [mrs, ← h1, Real.rpow_neg hx.le]
  field_simp

/-- Galí (2015), eq. (27), p. 178: along symmetric allocations, `N₀ > 0` maximises welfare
**iff** `MRS = MPN` at `N₀` (necessary and sufficient). -/
theorem symWelfare_isMax_iff_foc {σ φ α A Z N₀ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) (hN₀ : 0 < N₀) :
    (∀ N, 0 < N → symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z N₀) ↔
      mrs σ φ (A * N₀ ^ (1 - α)) N₀ = mpn α A N₀ :=
  ⟨foc_of_symWelfare_isMax hφ hA hZ hN₀,
    fun h _ hN => symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ hN₀ h hN⟩

/-- Galí (2015), p. 178: efficient employment `N*` maximises symmetric welfare. -/
theorem symWelfare_le_eff {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {N : ℝ} (hN : 0 < N) :
    symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ (effEmployment_pos hα1 hA)
    ((mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA (effEmployment_pos hα1 hA)).2 rfl) hN

/-- Galí (2015), p. 178: **strict** welfare loss away from efficient employment. -/
theorem symWelfare_lt {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {N : ℝ} (hN : 0 < N)
    (hne : N ≠ effEmployment σ φ α A) :
    symWelfare σ φ α A Z N < symWelfare σ φ α A Z (effEmployment σ φ α A) := by
  refine lt_of_le_of_ne (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN) fun heq => hne ?_
  refine (mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN).1 (foc_of_symWelfare_isMax hφ hA hZ hN ?_)
  intro N' hN'
  rw [heq]
  exact symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN'

/-- Galí (2015), p. 178, **existence and uniqueness** of efficient employment: exactly one
`N > 0` maximises symmetric welfare, namely `N*`. -/
theorem existsUnique_efficient {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) :
    ∃! N, 0 < N ∧ ∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N := by
  refine ⟨effEmployment σ φ α A, ⟨effEmployment_pos hα1 hA,
    fun N' hN' => symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN'⟩, ?_⟩
  rintro N ⟨hN, hmax⟩
  exact (mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN).1 (foc_of_symWelfare_isMax hφ hA hZ hN hmax)

/-! ### CES aggregators on a probability space -/

namespace CES

open Gali.StickyWagesPrices.LaborAggregation

variable {X : Type*} [MeasurableSpace X]

/-- Galí (2015), p. 178: a one-dimensional allocation of hours: measurable, nonnegative,
integrable, with positive total `∫ N > 0`. -/
def PosAlloc (μ : Measure X) (n : X → ℝ) : Prop :=
  Measurable n ∧ (∀ i, 0 ≤ n i) ∧ Integrable n μ ∧ 0 < ∫ i, n i ∂μ

variable {μ : Measure X}

/-- Galí (2015), p. 178: for `ε > 1` the CES exponent `r = (ε − 1)/ε` lies in `(0, 1)`. -/
theorem r_mem {ε : ℝ} (hε : 1 < ε) : 0 < (ε - 1) / ε ∧ (ε - 1) / ε < 1 :=
  ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- Galí (2015), p. 178: the exponent `q = (1 − α)(ε − 1)/ε` lies in `(0, 1)`. Restated from
the Chapter 4 project. -/
theorem q_mem {ε α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < (1 - α) * ((ε - 1) / ε) ∧ (1 - α) * ((ε - 1) / ε) < 1 := by
  obtain ⟨hr0, hr1⟩ := r_mem hε
  refine ⟨mul_pos (by linarith) hr0, ?_⟩
  calc (1 - α) * ((ε - 1) / ε) ≤ 1 * ((ε - 1) / ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
    _ < 1 := by linarith

/-- Galí (2015), p. 178: for `0 ≤ q ≤ 1`, `n^q` is integrable when `n ≥ 0` is measurable and
integrable (on a probability space). Restated from the Chapter 4 project. -/
theorem integrable_rpow [IsProbabilityMeasure μ] {n : X → ℝ} (hm : Measurable n)
    (h0 : ∀ i, 0 ≤ n i) (hi : Integrable n μ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun i => n i ^ q) μ := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hi)
    (hm.pow_const q).aestronglyMeasurable (Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (h0 i) q)]
  have := rpow_le_tangent hq0 hq1 one_pos (h0 i)
  simp only [Real.one_rpow, div_one, one_mul] at this
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right hq1 (h0 i)]

/-- Galí (2015), p. 178 (Jensen): for `0 < q < 1`, `∫ n^q ≤ (∫ n)^q`, with equality **iff**
`n = ∫ n` a.e. Restated from the Chapter 4 project. -/
theorem integral_rpow_le [IsProbabilityMeasure μ] {n : X → ℝ} (hn : PosAlloc μ n) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ i, n i ^ q ∂μ ≤ (∫ i, n i ∂μ) ^ q ∧
      (∫ i, n i ^ q ∂μ = (∫ i, n i ∂μ) ^ q ↔ ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) := by
  set N := ∫ i, n i ∂μ with hNdef
  have hN : 0 < N := hn.2.2.2
  have hf := integrable_rpow hn.1 hn.2.1 hn.2.2.1 hq0.le hq1.le
  set g : X → ℝ := fun i => N ^ q * (1 - q) + N ^ q * q / N * n i with hg
  have hgi : Integrable g μ := (integrable_const _).add (hn.2.2.1.const_mul _)
  have hpt : ∀ i, n i ^ q ≤ g i := fun i => by
    have := rpow_le_tangent hq0.le hq1.le hN (hn.2.1 i)
    simp only [hg]
    have e : N ^ q * (1 + q * (n i / N - 1)) = N ^ q * (1 - q) + N ^ q * q / N * n i := by
      field_simp
      ring
    linarith
  have hgint : ∫ i, g i ∂μ = N ^ q := by
    simp only [hg]
    rw [integral_add (integrable_const _) (hn.2.2.1.const_mul _), integral_const,
      integral_const_mul, ← hNdef]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  have hle : ∫ i, n i ^ q ∂μ ≤ N ^ q := hgint ▸ integral_mono hf hgi hpt
  refine ⟨hle, ⟨fun heq => ?_, fun h => ?_⟩⟩
  · rw [← hgint] at heq
    have hae := (integral_eq_iff_of_ae_le hf hgi (Eventually.of_forall hpt)).1 heq
    filter_upwards [hae] with i hi
    refine eq_of_rpow_eq_tangent hq0 hq1 hN (hn.2.1 i) ?_
    rw [hi]
    simp only [hg]
    field_simp
    ring
  · rw [integral_congr_ae (g := fun _ => N ^ q) (by filter_upwards [h] with i hi; rw [hi])]
    simp

/-- Galí (2015), p. 178: a CES index of an a.e. constant `c ≥ 0` is `c`. -/
theorem cesIndex_of_ae_eq [IsProbabilityMeasure μ] {ε c : ℝ} (hε : 1 < ε) (hc : 0 ≤ c)
    {f : X → ℝ} (hf : ∀ᵐ i ∂μ, f i = c) : laborIndex μ ε f = c := by
  obtain ⟨hr0, -⟩ := r_mem hε
  rw [laborIndex, integral_congr_ae (g := fun _ => c ^ ((ε - 1) / ε))
    (by filter_upwards [hf] with i hi; rw [hi])]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact Real.rpow_rpow_inv hc hr0.ne'

/-- Galí (2015), p. 189 (power-mean inequality, labour-type dimension): the CES index is at
most the arithmetic total, `(∫ f^r)^{1/r} ≤ ∫ f` for `r = (ε − 1)/ε ∈ (0, 1)`. -/
theorem cesIndex_le_integral [IsProbabilityMeasure μ] {ε : ℝ} (hε : 1 < ε) {f : X → ℝ}
    (hm : Measurable f) (h0 : ∀ i, 0 ≤ f i) (hi : Integrable f μ) :
    laborIndex μ ε f ≤ ∫ i, f i ∂μ := by
  obtain ⟨hr0, hr1⟩ := r_mem hε
  have hnn : 0 ≤ fun i => f i := fun i => h0 i
  rcases (integral_nonneg hnn).lt_or_eq with hpos | hzero
  · have h := (integral_rpow_le ⟨hm, h0, hi, hpos⟩ hr0 hr1).1
    calc laborIndex μ ε f ≤ ((∫ i, f i ∂μ) ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹ :=
          Real.rpow_le_rpow (integral_nonneg fun i => Real.rpow_nonneg (h0 i) _) h
            (inv_nonneg.2 hr0.le)
      _ = ∫ i, f i ∂μ := Real.rpow_rpow_inv hpos.le hr0.ne'
  · have hz := (integral_eq_zero_iff_of_nonneg hnn hi).1 hzero.symm
    have hzr : (fun i => f i ^ ((ε - 1) / ε)) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [hz] with i hi
      simp only [Pi.zero_apply] at hi
      rw [hi, Real.zero_rpow hr0.ne']
    rw [laborIndex, integral_congr_ae hzr, integral_zero, Real.zero_rpow (inv_pos.2 hr0).ne',
      ← hzero]

/-- Galí (2015), p. 189: for a positive allocation, the CES index equals the arithmetic total
**iff** the allocation is a.e. constant. -/
theorem cesIndex_eq_integral_iff [IsProbabilityMeasure μ] {ε : ℝ} (hε : 1 < ε) {f : X → ℝ}
    (hf : PosAlloc μ f) : laborIndex μ ε f = ∫ i, f i ∂μ ↔ ∀ᵐ i ∂μ, f i = ∫ j, f j ∂μ := by
  obtain ⟨hr0, hr1⟩ := r_mem hε
  rw [← (integral_rpow_le hf hr0 hr1).2]
  have hI : 0 ≤ ∫ i, f i ^ ((ε - 1) / ε) ∂μ :=
    integral_nonneg fun i => Real.rpow_nonneg (hf.2.1 i) _
  constructor
  · intro h
    rw [← h, laborIndex, Real.rpow_inv_rpow hI hr0.ne']
  · intro h
    rw [laborIndex, h, Real.rpow_rpow_inv hf.2.2.2.le hr0.ne']

/-- Galí (2015), p. 178: `(A x^{1−α})^r = A^r x^{(1−α) r}`. Restated from the Chapter 4
project. -/
theorem output_rpow {A α r x : ℝ} (hA : 0 < A) (hx : 0 ≤ x) :
    (A * x ^ (1 - α)) ^ r = A ^ r * x ^ ((1 - α) * r) := by
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hx _), ← Real.rpow_mul hx]

/-- Galí (2015), p. 178: `(A^r N^{(1−α) r})^{1/r} = A N^{1−α}`. Restated from the Chapter 4
project. -/
theorem symmetric_index {ε A α N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hN : 0 ≤ N) :
    (A ^ ((ε - 1) / ε) * N ^ ((1 - α) * ((ε - 1) / ε))) ^ ((ε - 1) / ε)⁻¹
      = A * N ^ (1 - α) := by
  have hr : (ε - 1) / ε ≠ 0 := (div_pos (by linarith) (by linarith)).ne'
  rw [Real.mul_rpow (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hN _),
    Real.rpow_rpow_inv hA.le hr, ← Real.rpow_mul hN, mul_assoc, mul_inv_cancel₀ hr, mul_one]

end CES

/-! ### The planner with goods and labour types: conditions (25) and (26) -/

namespace Planner

open CES Gali.StickyWagesPrices.LaborAggregation

variable {G J : Type*} [MeasurableSpace G] [MeasurableSpace J]

/-- Galí (2015), eq. (2), p. 164: the labour index of firm `i`,
`N(i) = (∫ N(i,j)^{(ε_w−1)/ε_w} dj)^{ε_w/(ε_w−1)}`. -/
noncomputable def labourIndex (ν : Measure J) (εw : ℝ) (n : G × J → ℝ) (i : G) : ℝ :=
  laborIndex ν εw fun j => n (i, j)

/-- Galí (2015), p. 189: the total hours of all types worked at firm `i`, `∫ N(i,j) dj`. -/
noncomputable def firmHours (ν : Measure J) (n : G × J → ℝ) (i : G) : ℝ := ∫ j, n (i, j) ∂ν

/-- Galí (2015), pp. 166 and 189 (market clearing): the hours supplied by type `j`,
`N(j) = ∫ N(i,j) di`. -/
noncomputable def labourSupply (μ : Measure G) (n : G × J → ℝ) (j : J) : ℝ := ∫ i, n (i, j) ∂μ

/-- Galí (2015), p. 189: total hours `∫∫ N(i,j) di dj`. -/
noncomputable def totalHours (μ : Measure G) (ν : Measure J) (n : G × J → ℝ) : ℝ :=
  ∫ p, n p ∂(μ.prod ν)

/-- Galí (2015), eq. (1), p. 164: output of good `i`, `C(i) = Y(i) = A N(i)^{1−α}`. -/
noncomputable def goodsOutput (ν : Measure J) (εw A α : ℝ) (n : G × J → ℝ) (i : G) : ℝ :=
  A * labourIndex ν εw n i ^ (1 - α)

/-- Galí (2015), p. 178: the consumption index of the allocation `N(·,·)`. -/
noncomputable def aggConsumption (μ : Measure G) (ν : Measure J) (εp εw A α : ℝ)
    (n : G × J → ℝ) : ℝ :=
  laborIndex μ εp (goodsOutput ν εw A α n)

/-- Galí (2015), pp. 167 and 178: the planner's objective
`U(C, {N(j)}; Z) = (u(C) − ∫ N(j)^{1+φ}/(1+φ) dj) Z`. -/
noncomputable def welfare (μ : Measure G) (ν : Measure J) (σ φ εp εw A α Z : ℝ)
    (n : G × J → ℝ) : ℝ :=
  (utilC σ (aggConsumption μ ν εp εw A α n) - ∫ j, disutilN φ (labourSupply μ n j) ∂ν) * Z

/-- Galí (2015), p. 178: a feasible allocation of hours `N(i,j)`: jointly measurable,
nonnegative, integrable, with integrable disutility and positive total hours. -/
def Feasible (μ : Measure G) (ν : Measure J) (φ : ℝ) (n : G × J → ℝ) : Prop :=
  Measurable n ∧ (∀ p, 0 ≤ n p) ∧ Integrable n (μ.prod ν) ∧
    Integrable (fun j => disutilN φ (labourSupply μ n j)) ν ∧ 0 < totalHours μ ν n

variable {μ : Measure G} {ν : Measure J}

/-- Galí (2015), p. 189: firm hours `i ↦ ∫ N(i,j) dj` form a positive one-dimensional
allocation whose total is total hours (Fubini). -/
theorem firmHours_posAlloc [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ : ℝ}
    {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    PosAlloc μ (firmHours ν n) ∧ ∫ i, firmHours ν n i ∂μ = totalHours μ ν n := by
  obtain ⟨hm, h0, hi, -, hpos⟩ := hn
  have htot : ∫ i, firmHours ν n i ∂μ = totalHours μ ν n := (integral_prod n hi).symm
  exact ⟨⟨hm.stronglyMeasurable.integral_prod_right'.measurable,
    fun i => integral_nonneg fun j => h0 _, hi.integral_prod_left, htot ▸ hpos⟩, htot⟩

/-- Galí (2015), p. 189: the supplies `j ↦ N(j)` are integrable and sum to total hours. -/
theorem labourSupply_integral [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {n : G × J → ℝ}
    (hi : Integrable n (μ.prod ν)) :
    Integrable (labourSupply μ n) ν ∧ ∫ j, labourSupply μ n j ∂ν = totalHours μ ν n :=
  ⟨hi.integral_prod_right, (integral_prod_symm n hi).symm⟩

omit [MeasurableSpace G] in
/-- Galí (2015), p. 164: the labour index of every firm is nonnegative. -/
theorem labourIndex_nonneg {εw : ℝ} {n : G × J → ℝ} (h0 : ∀ p, 0 ≤ n p) (i : G) :
    0 ≤ labourIndex ν εw n i :=
  laborIndex_nonneg fun j => h0 (i, j)

/-- Galí (2015), p. 164: the labour index `i ↦ N(i)` is measurable. -/
theorem labourIndex_measurable [IsProbabilityMeasure ν] {εw : ℝ} {n : G × J → ℝ}
    (hm : Measurable n) : Measurable (labourIndex ν εw n) :=
  ((hm.pow_const ((εw - 1) / εw)).stronglyMeasurable.integral_prod_right').measurable.pow_const _

/-- Galí (2015), p. 189 (**power mean, labour types**): for a.e. firm, its labour index is at
most its total hours, `N(i) ≤ ∫ N(i,j) dj`. -/
theorem labourIndex_le_firmHours [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {εw : ℝ}
    (hε : 1 < εw) {n : G × J → ℝ} (hm : Measurable n) (h0 : ∀ p, 0 ≤ n p)
    (hi : Integrable n (μ.prod ν)) :
    ∀ᵐ i ∂μ, labourIndex ν εw n i ≤ firmHours ν n i := by
  filter_upwards [hi.prod_right_ae] with i hii
  exact cesIndex_le_integral hε (hm.comp measurable_prodMk_left) (fun j => h0 _) hii

/-- Galí (2015), p. 178: the consumption index is `C = (A^r ∫ N(i)^q)^{1/r}`,
`r = (ε_p − 1)/ε_p`, `q = (1 − α) r`. -/
theorem aggConsumption_eq {εp εw A α : ℝ} (hA : 0 < A) {n : G × J → ℝ} (h0 : ∀ p, 0 ≤ n p) :
    aggConsumption μ ν εp εw A α n
      = (A ^ ((εp - 1) / εp) *
          ∫ i, labourIndex ν εw n i ^ ((1 - α) * ((εp - 1) / εp)) ∂μ) ^ ((εp - 1) / εp)⁻¹ := by
  rw [aggConsumption, laborIndex, ← integral_const_mul]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun i => output_rpow hA
    (labourIndex_nonneg h0 i))

/-- Galí (2015), p. 178: the integrand `N(i)^q` is integrable and bounded by
`(∫ N(i,j) dj)^q`, whose integral is at most `L^q`, `L` total hours. -/
theorem integral_labourIndex_rpow [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ εw q : ℝ} (hε : 1 < εw) (hq0 : 0 < q) (hq1 : q < 1) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) :
    Integrable (fun i => labourIndex ν εw n i ^ q) μ ∧
      Integrable (fun i => firmHours ν n i ^ q) μ ∧
      (∀ᵐ i ∂μ, labourIndex ν εw n i ^ q ≤ firmHours ν n i ^ q) ∧
      ∫ i, labourIndex ν εw n i ^ q ∂μ ≤ ∫ i, firmHours ν n i ^ q ∂μ ∧
      ∫ i, firmHours ν n i ^ q ∂μ ≤ totalHours μ ν n ^ q := by
  obtain ⟨hP, htot⟩ := firmHours_posAlloc hn
  have hmi := integrable_rpow hP.1 hP.2.1 hP.2.2.1 hq0.le hq1.le
  have hle : ∀ᵐ i ∂μ, labourIndex ν εw n i ^ q ≤ firmHours ν n i ^ q := by
    filter_upwards [labourIndex_le_firmHours hε hn.1 hn.2.1 hn.2.2.1] with i hi
    exact Real.rpow_le_rpow (labourIndex_nonneg hn.2.1 i) hi hq0.le
  have hxi : Integrable (fun i => labourIndex ν εw n i ^ q) μ := by
    refine Integrable.mono' hmi ((labourIndex_measurable hn.1).pow_const q).aestronglyMeasurable ?_
    filter_upwards [hle] with i hi
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) q)]
    exact hi
  refine ⟨hxi, hmi, hle, integral_mono_of_nonneg (Eventually.of_forall fun i =>
    Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) q) hmi hle, ?_⟩
  rw [← htot]
  exact (integral_rpow_le hP hq0 hq1).1

/-- Galí (2015), eqs. (1)–(2), p. 178: for a feasible allocation with total hours `L`, the
consumption index is at most `A L^{1−α}`. -/
theorem aggConsumption_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ εp εw A α : ℝ}
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) :
    aggConsumption μ ν εp εw A α n ≤ A * totalHours μ ν n ^ (1 - α) := by
  obtain ⟨hq0, hq1⟩ := q_mem hεp hα0 hα1
  obtain ⟨hr0, -⟩ := r_mem hεp
  obtain ⟨-, -, -, h1, h2⟩ := integral_labourIndex_rpow (φ := φ) hεw hq0 hq1 hn
  rw [aggConsumption_eq hA hn.2.1, ← symmetric_index hεp hA hn.2.2.2.2.le]
  refine Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hA.le _)
    (integral_nonneg fun i => Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) _)) ?_
    (inv_nonneg.2 hr0.le)
  exact mul_le_mul_of_nonneg_left (h1.trans h2) (Real.rpow_nonneg hA.le _)

/-- Galí (2015), p. 178: if `N(i,j) = c` a.e., then `N(i) = c` for a.e. firm, `N(j) = c` for
a.e. type, `C(i) = A c^{1−α}` for a.e. good and `C = A c^{1−α}`. -/
theorem symmetric_consequences [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {εp εw A α c : ℝ} (hεp : 1 < εp) (hεw : 1 < εw) (hA : 0 < A) (hc : 0 ≤ c)
    {n : G × J → ℝ} (hm : Measurable n) (h : ∀ᵐ p ∂(μ.prod ν), n p = c) :
    (∀ᵐ i ∂μ, labourIndex ν εw n i = c) ∧ (∀ᵐ j ∂ν, labourSupply μ n j = c) ∧
      (∀ᵐ i ∂μ, goodsOutput ν εw A α n i = A * c ^ (1 - α)) ∧
      aggConsumption μ ν εp εw A α n = A * c ^ (1 - α) := by
  have hms : MeasurableSet {p : G × J | n p = c} := measurableSet_eq_fun hm measurable_const
  have hii : ∀ᵐ i ∂μ, ∀ᵐ j ∂ν, n (i, j) = c := (Measure.ae_prod_iff_ae_ae hms).1 h
  have hjj : ∀ᵐ j ∂ν, ∀ᵐ i ∂μ, n (i, j) = c := (Measure.ae_ae_comm (p := fun i j => n (i, j) = c)
    hms).1 hii
  have hL : ∀ᵐ i ∂μ, labourIndex ν εw n i = c := by
    filter_upwards [hii] with i hi
    exact cesIndex_of_ae_eq hεw hc hi
  have hY : ∀ᵐ i ∂μ, goodsOutput ν εw A α n i = A * c ^ (1 - α) := by
    filter_upwards [hL] with i hi
    rw [goodsOutput, hi]
  refine ⟨hL, ?_, hY, cesIndex_of_ae_eq hεp (mul_nonneg hA.le (Real.rpow_nonneg hc _)) hY⟩
  filter_upwards [hjj] with j hj
  rw [labourSupply, integral_congr_ae hj]
  simp

/-- Galí (2015), p. 178: the consumption index of a feasible allocation is positive. -/
theorem aggConsumption_pos [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ εp εw A α : ℝ}
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) : 0 < aggConsumption μ ν εp εw A α n := by
  obtain ⟨hq0, hq1⟩ := q_mem hεp hα0 hα1
  obtain ⟨hr0, -⟩ := r_mem hεw
  obtain ⟨hxi, -, -, -, -⟩ := integral_labourIndex_rpow (φ := φ) hεw hq0 hq1 hn
  obtain ⟨hP, htot⟩ := firmHours_posAlloc hn
  rw [aggConsumption_eq hA hn.2.1]
  refine Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos hA _) ?_) _
  have hnn : 0 ≤ fun i => labourIndex ν εw n i ^ ((1 - α) * ((εp - 1) / εp)) :=
    fun i => Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) _
  rcases (integral_nonneg hnn).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := (integral_eq_zero_iff_of_nonneg hnn hxi).1 h.symm
    have hm0 : ∀ᵐ i ∂μ, firmHours ν n i = 0 := by
      filter_upwards [hz, hn.2.2.1.prod_right_ae] with i hi hii
      have hx0 : labourIndex ν εw n i = 0 :=
        ((Real.rpow_eq_zero_iff_of_nonneg (labourIndex_nonneg hn.2.1 i)).1 hi).1
      have hI0 : ∫ j, n (i, j) ^ ((εw - 1) / εw) ∂ν = 0 :=
        ((Real.rpow_eq_zero_iff_of_nonneg (integral_nonneg fun j =>
          Real.rpow_nonneg (hn.2.1 _) _)).1 hx0).1
      have hpow := (integral_eq_zero_iff_of_nonneg (fun j => Real.rpow_nonneg (hn.2.1 (i, j)) _)
        (integrable_rpow (hn.1.comp measurable_prodMk_left) (fun j => hn.2.1 _) hii hr0.le
          (r_mem hεw).2.le)).1 hI0
      have hsec : (fun j => n (i, j)) =ᵐ[ν] 0 := by
        filter_upwards [hpow] with j hj
        exact ((Real.rpow_eq_zero_iff_of_nonneg (hn.2.1 (i, j))).1 hj).1
      rw [firmHours, integral_congr_ae hsec]
      simp
    have := hn.2.2.2.2
    rw [← htot, integral_congr_ae hm0] at this
    simp at this

/-- Galí (2015), eqs. (25)–(26), p. 178 (**both CES dimensions**): the bound
`C ≤ A L^{1−α}` holds with equality **iff** `N(i,j) = L` for a.e. `(i, j)`. -/
theorem aggConsumption_eq_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ εp εw A α : ℝ} (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A)
    {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    aggConsumption μ ν εp εw A α n = A * totalHours μ ν n ^ (1 - α) ↔
      ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n := by
  obtain ⟨hq0, hq1⟩ := q_mem hεp hα0 hα1
  obtain ⟨hr0, -⟩ := r_mem hεp
  set q := (1 - α) * ((εp - 1) / εp) with hqdef
  set L := totalHours μ ν n with hLdef
  have hL : 0 < L := hn.2.2.2.2
  obtain ⟨hxi, hmi, hle, h1, h2⟩ := integral_labourIndex_rpow (φ := φ) hεw hq0 hq1 hn
  obtain ⟨hP, htot⟩ := firmHours_posAlloc hn
  constructor
  · intro hC
    rw [aggConsumption_eq hA hn.2.1, ← symmetric_index hεp hA hL.le] at hC
    have hAr : 0 < A ^ ((εp - 1) / εp) := Real.rpow_pos_of_pos hA _
    have hIx : ∫ i, labourIndex ν εw n i ^ q ∂μ = L ^ q := by
      by_contra hne
      have hlt := lt_of_le_of_ne (h1.trans h2) hne
      have := Real.rpow_lt_rpow (mul_nonneg hAr.le
        (integral_nonneg fun i => Real.rpow_nonneg (labourIndex_nonneg hn.2.1 i) _))
        (mul_lt_mul_of_pos_left hlt hAr) (inv_pos.2 hr0)
      rw [hC] at this
      exact lt_irrefl _ this
    have hIm : ∫ i, firmHours ν n i ^ q ∂μ = L ^ q := le_antisymm h2 (hIx ▸ h1)
    have hmL : ∀ᵐ i ∂μ, firmHours ν n i = L := by
      have := (integral_rpow_le hP hq0 hq1).2.1 (by rw [htot]; exact hIm)
      rwa [htot] at this
    have hdiff : (fun i => firmHours ν n i ^ q - labourIndex ν εw n i ^ q) =ᵐ[μ] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae
        (f := fun i => firmHours ν n i ^ q - labourIndex ν εw n i ^ q) ?_ (hmi.sub hxi)).1 ?_
      · filter_upwards [hle] with i hi
        exact sub_nonneg.2 hi
      · rw [integral_sub hmi hxi, hIm, hIx, sub_self]
    have hxm : ∀ᵐ i ∂μ, labourIndex ν εw n i = firmHours ν n i := by
      filter_upwards [hdiff] with i hi
      simp only [Pi.zero_apply, sub_eq_zero] at hi
      rw [← Real.rpow_rpow_inv (labourIndex_nonneg hn.2.1 i) hq0.ne', ← hi,
        Real.rpow_rpow_inv (hP.2.1 i) hq0.ne']
    have hii : ∀ᵐ i ∂μ, ∀ᵐ j ∂ν, n (i, j) = L := by
      filter_upwards [hmL, hxm, hn.2.2.1.prod_right_ae] with i hmi' hxi' hint
      have hPi : PosAlloc ν fun j => n (i, j) :=
        ⟨hn.1.comp measurable_prodMk_left, fun j => hn.2.1 _, hint, by
          change 0 < firmHours ν n i
          rw [hmi']
          exact hL⟩
      have := (cesIndex_eq_integral_iff hεw hPi).1 (by
        change labourIndex ν εw n i = firmHours ν n i
        exact hxi')
      filter_upwards [this] with j hj
      rw [hj]
      exact hmi'
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hn.1 measurable_const)).2 hii
  · intro h
    exact (symmetric_consequences (α := α) hεp hεw hA hL.le hn.1 h).2.2.2

/-- Galí (2015), p. 178 (Jensen, labour types): the disutility of a feasible allocation is at
least the disutility of total hours, `∫ N(j)^{1+φ}/(1+φ) ≥ L^{1+φ}/(1+φ)`. -/
theorem disutility_ge [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ : ℝ} (hφ : 0 ≤ φ)
    {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    disutilN φ (totalHours μ ν n) ≤ ∫ j, disutilN φ (labourSupply μ n j) ∂ν := by
  set L := totalHours μ ν n with hLdef
  have hL : 0 < L := hn.2.2.2.2
  obtain ⟨hsi, hsum⟩ := labourSupply_integral (μ := μ) (ν := ν) hn.2.2.1
  have hpt : ∀ j, (disutilN φ L - L ^ φ * L) + L ^ φ * labourSupply μ n j
      ≤ disutilN φ (labourSupply μ n j) := fun j => by
    have := disutilN_tangent_le hφ hL (integral_nonneg (μ := μ) fun i => hn.2.1 (i, j))
    unfold labourSupply at this ⊢
    linarith
  have hint := integral_mono (f := fun j => (disutilN φ L - L ^ φ * L) +
    L ^ φ * labourSupply μ n j) ((integrable_const _).add (hsi.const_mul _)) hn.2.2.2.1 hpt
  rw [integral_add (integrable_const _) (hsi.const_mul _), integral_const_mul, hsum,
    integral_const] at hint
  simp only [probReal_univ, smul_eq_mul, one_mul] at hint
  linarith

/-- Galí (2015), p. 178: welfare of a feasible allocation is at most the welfare of the
symmetric allocation with the same total hours. -/
theorem welfare_le_symWelfare [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    welfare μ ν σ φ εp εw A α Z n ≤ symWelfare σ φ α A Z (totalHours μ ν n) := by
  unfold welfare symWelfare periodUtility
  refine mul_le_mul_of_nonneg_right (sub_le_sub ?_ (disutility_ge hφ hn)) hZ.le
  rcases (aggConsumption_le hεp hεw hα0 hα1 hA hn).lt_or_eq with h | h
  · exact (utilC_lt_utilC (aggConsumption_pos hεp hεw hα0 hα1 hA hn) h).le
  · rw [h]

/-- Galí (2015), eqs. (25)–(26), p. 178: equality in `welfare_le_symWelfare` holds **iff** the
allocation is symmetric, `N(i,j) = L` for a.e. `(i, j)`. -/
theorem welfare_eq_symWelfare_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    welfare μ ν σ φ εp εw A α Z n = symWelfare σ φ α A Z (totalHours μ ν n) ↔
      ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n := by
  rw [← aggConsumption_eq_iff hεp hεw hα0 hα1 hA hn]
  have hD := disutility_ge hφ hn
  constructor
  · intro h
    by_contra hne
    have hlt := lt_of_le_of_ne (aggConsumption_le hεp hεw hα0 hα1 hA hn) hne
    have h1 := utilC_lt_utilC (σ := σ) (aggConsumption_pos hεp hεw hα0 hα1 hA hn) hlt
    unfold welfare symWelfare periodUtility at h
    have h2 := mul_right_cancel₀ hZ.ne' h
    linarith
  · intro h
    have hsym := (aggConsumption_eq_iff hεp hεw hα0 hα1 hA hn).1 h
    obtain ⟨-, hS, -, -⟩ := symmetric_consequences (α := α) hεp hεw hA hn.2.2.2.2.le hn.1 hsym
    have hDeq : ∫ j, disutilN φ (labourSupply μ n j) ∂ν = disutilN φ (totalHours μ ν n) := by
      rw [integral_congr_ae (g := fun _ => disutilN φ (totalHours μ ν n))
        (by filter_upwards [hS] with j hj; rw [hj])]
      simp
    rw [welfare, symWelfare, periodUtility, h, hDeq]

/-- Galí (2015), p. 178: a **non-symmetric** feasible allocation is strictly worse than the
symmetric allocation with the same total hours. -/
theorem welfare_lt_symWelfare [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ} (hn : Feasible μ ν φ n)
    (hns : ¬ ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n) :
    welfare μ ν σ φ εp εw A α Z n < symWelfare σ φ α A Z (totalHours μ ν n) :=
  lt_of_le_of_ne (welfare_le_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn)
    fun h => hns ((welfare_eq_symWelfare_iff hφ hεp hεw hα0 hα1 hA hZ hn).1 h)

/-- Galí (2015), p. 178: a constant allocation `N(i,j) = N > 0` is feasible. -/
theorem feasible_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {φ N : ℝ}
    (hN : 0 < N) : Feasible μ ν φ (fun _ => N) :=
  ⟨measurable_const, fun _ => hN.le, integrable_const N, by
    simp only [labourSupply, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact integrable_const _, by simpa [totalHours] using hN⟩

/-- Galí (2015), p. 178: the welfare of the constant allocation `N(i,j) = N` is the symmetric
welfare `U(A N^{1−α}, N; Z)`. -/
theorem welfare_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {σ φ εp εw A α Z N : ℝ}
    (hεp : 1 < εp) (hεw : 1 < εw) (hA : 0 < A) (hN : 0 < N) :
    welfare μ ν σ φ εp εw A α Z (fun _ => N) = symWelfare σ φ α A Z N := by
  obtain ⟨-, -, -, hC⟩ := symmetric_consequences (μ := μ) (ν := ν) (α := α) hεp hεw hA hN.le
    measurable_const (Eventually.of_forall fun _ => rfl)
  rw [welfare, hC, symWelfare, periodUtility]
  simp [labourSupply]

/-- Galí (2015), p. 178: every feasible allocation is (weakly) worse than the efficient
allocation `N(i,j) = N*`. -/
theorem welfare_le_eff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {σ φ εp εw A α Z : ℝ}
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ} (hn : Feasible μ ν φ n) :
    welfare μ ν σ φ εp εw A α Z n ≤ symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  (welfare_le_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn).trans
    (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hn.2.2.2.2)

/-- Galí (2015), p. 178: any non-symmetric feasible allocation is **strictly** worse than the
efficient allocation. -/
theorem welfare_lt_of_not_symmetric [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) (hns : ¬ ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n) :
    welfare μ ν σ φ εp εw A α Z n < symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  (welfare_lt_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn hns).trans_le
    (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hn.2.2.2.2)

/-- Galí (2015), eqs. (25)–(27), p. 178 (**necessary and sufficient**): a feasible allocation
maximises welfare over all feasible allocations iff
(25) `C(i) = C` for a.e. good;
(26) `N(i,j) = N` for a.e. `(i, j)`, `N(i) = N` for a.e. firm and `N(j) = N` for a.e. type;
(27) `MRS = MPN`;
where `C` is the consumption index and `N` total hours. -/
theorem planner_optimal_iff [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) :
    (∀ n', Feasible μ ν φ n' →
        welfare μ ν σ φ εp εw A α Z n' ≤ welfare μ ν σ φ εp εw A α Z n) ↔
      (∀ᵐ i ∂μ, goodsOutput ν εw A α n i = aggConsumption μ ν εp εw A α n) ∧
      ((∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n) ∧
        (∀ᵐ i ∂μ, labourIndex ν εw n i = totalHours μ ν n) ∧
        (∀ᵐ j ∂ν, labourSupply μ n j = totalHours μ ν n)) ∧
      mrs σ φ (aggConsumption μ ν εp εw A α n) (totalHours μ ν n)
        = mpn α A (totalHours μ ν n) := by
  set N := totalHours μ ν n with hNdef
  have hN : 0 < N := hn.2.2.2.2
  constructor
  · intro hopt
    have hsym : ∀ᵐ p ∂(μ.prod ν), n p = N := by
      refine (welfare_eq_symWelfare_iff (σ := σ) hφ hεp hεw hα0 hα1 hA hZ hn).1 (le_antisymm
        (welfare_le_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn) ?_)
      rw [← welfare_const (μ := μ) (ν := ν) (εp := εp) (εw := εw) hεp hεw hA hN]
      exact hopt _ (feasible_const hN)
    obtain ⟨hL, hS, hY, hC⟩ := symmetric_consequences (α := α) hεp hεw hA hN.le hn.1 hsym
    have hmax : ∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N := by
      intro N' hN'
      rw [← welfare_const (μ := μ) (ν := ν) (εp := εp) (εw := εw) hεp hεw hA hN',
        ← (welfare_eq_symWelfare_iff hφ hεp hεw hα0 hα1 hA hZ hn).2 hsym]
      exact hopt _ (feasible_const hN')
    refine ⟨?_, ⟨hsym, hL, hS⟩, ?_⟩
    · filter_upwards [hY] with i hi
      rw [hi, hC]
    · rw [hC]
      exact foc_of_symWelfare_isMax hφ hA hZ hN hmax
  · rintro ⟨-, ⟨hsym, -, -⟩, hfoc⟩ n' hn'
    obtain ⟨-, -, -, hC⟩ := symmetric_consequences (α := α) hεp hεw hA hN.le hn.1 hsym
    rw [hC] at hfoc
    rw [(welfare_eq_symWelfare_iff hφ hεp hεw hα0 hα1 hA hZ hn).2 hsym]
    exact (welfare_le_symWelfare hφ hεp hεw hα0 hα1 hA hZ hn').trans
      (symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ hN hfoc hn'.2.2.2.2)

/-- Galí (2015), §6.3, p. 178: a feasible allocation is optimal **iff** `N(i,j) = N*` for
a.e. `(i, j)`, where `N*` is efficient employment (`effEmployment`). -/
theorem planner_optimal_iff_effEmployment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G × J → ℝ}
    (hn : Feasible μ ν φ n) :
    (∀ n', Feasible μ ν φ n' →
        welfare μ ν σ φ εp εw A α Z n' ≤ welfare μ ν σ φ εp εw A α Z n) ↔
      ∀ᵐ p ∂(μ.prod ν), n p = effEmployment σ φ α A := by
  rw [planner_optimal_iff hσ hφ hεp hεw hα0 hα1 hA hZ hn]
  have hN : 0 < totalHours μ ν n := hn.2.2.2.2
  constructor
  · rintro ⟨-, ⟨hsym, -, -⟩, hfoc⟩
    rw [(aggConsumption_eq_iff hεp hεw hα0 hα1 hA hn).2 hsym,
      mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN] at hfoc
    filter_upwards [hsym] with p hp
    rw [hp, hfoc]
  · intro h
    have hint : totalHours μ ν n = effEmployment σ φ α A := by
      rw [totalHours, integral_congr_ae h]
      simp
    have hsym : ∀ᵐ p ∂(μ.prod ν), n p = totalHours μ ν n := by
      filter_upwards [h] with p hp
      rw [hp, hint]
    obtain ⟨hL, hS, hY, hC⟩ := symmetric_consequences (α := α) hεp hεw hA hN.le hn.1 hsym
    refine ⟨?_, ⟨hsym, hL, hS⟩, ?_⟩
    · filter_upwards [hY] with i hi
      rw [hi, hC]
    · rw [hC, mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN, hint]

/-- Galí (2015), §6.3, p. 178, **existence and uniqueness**: the efficient allocation
`N(i,j) = N*` is feasible and optimal, and every optimal allocation equals it a.e. -/
theorem planner_existsUnique [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp) (hεw : 1 < εw)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) :
    Feasible μ ν φ (fun _ => effEmployment σ φ α A) ∧
      (∀ n', Feasible μ ν φ n' → welfare μ ν σ φ εp εw A α Z n'
        ≤ welfare μ ν σ φ εp εw A α Z (fun _ => effEmployment σ φ α A)) ∧
      ∀ n, Feasible μ ν φ n →
        (∀ n', Feasible μ ν φ n' →
          welfare μ ν σ φ εp εw A α Z n' ≤ welfare μ ν σ φ εp εw A α Z n) →
        ∀ᵐ p ∂(μ.prod ν), n p = effEmployment σ φ α A := by
  have hf := feasible_const (μ := μ) (ν := ν) (φ := φ) (effEmployment_pos (σ := σ) (φ := φ)
    hα1 hA)
  refine ⟨hf, (planner_optimal_iff_effEmployment hσ hφ hεp hεw hα0 hα1 hA hZ hf).2
    (Eventually.of_forall fun _ => rfl), fun n hn hopt => ?_⟩
  exact (planner_optimal_iff_effEmployment hσ hφ hεp hεw hα0 hα1 hA hZ hn).1 hopt

/-- Galí (2015), p. 178: Lebesgue measure on the continuum `[0, 1]` of goods (or of labour
types) is a probability measure. -/
theorem isProbabilityMeasure_unitInterval :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Icc]⟩

/-- Galí (2015), §6.3, p. 178, on the book's **continua of goods and labour types
`[0, 1] × [0, 1]`**: a feasible allocation is optimal iff `N(i,j) = N*` for a.e. `(i, j)`,
iff (25)–(27) hold. -/
theorem planner_optimal_iff_unitInterval {σ φ εp εw A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    {n : ℝ × ℝ → ℝ}
    (hn : Feasible (volume.restrict (Set.Icc 0 1)) (volume.restrict (Set.Icc 0 1)) φ n) :
    (∀ n' : ℝ × ℝ → ℝ,
        Feasible (volume.restrict (Set.Icc 0 1)) (volume.restrict (Set.Icc 0 1)) φ n' →
        welfare (volume.restrict (Set.Icc 0 1)) (volume.restrict (Set.Icc 0 1)) σ φ εp εw A α Z n'
          ≤ welfare (volume.restrict (Set.Icc 0 1)) (volume.restrict (Set.Icc 0 1))
            σ φ εp εw A α Z n) ↔
      ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))),
        n p = effEmployment σ φ α A := by
  have := isProbabilityMeasure_unitInterval
  exact planner_optimal_iff_effEmployment hσ hφ hεp hεw hα0 hα1 hA hZ hn

end Planner

/-! ### The decentralised flexible-price-and-wage equilibrium (pp. 178–179) -/

/-- Galí (2015), pp. 165 and 168: the desired gross markups `M_p = ε_p/(ε_p − 1)` and
`M_w = ε_w/(ε_w − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), p. 168: `M > 1` for `ε > 1`. -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  rw [markup, one_lt_div (by linarith)]
  linarith

/-- Galí (2015), p. 168: `M > 0` for `ε > 1`. -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  lt_trans one_pos (one_lt_markup hε)

/-- Galí (2015), p. 178: with flexible prices and wages, equal prices and equal wages give
`C(i) = (P(i)/P)^{−ε_p} C = C` (eq. (7)) and `N(i,j) = (W(j)/W)^{−ε_w} N(i) = N(i)` (eq. (3)):
conditions (25) and the first part of (26) hold. -/
theorem demand_at_equal_prices {ε P C : ℝ} (hP : 0 < P) : (P / P) ^ (-ε) * C = C := by
  rw [div_self hP.ne', Real.one_rpow, one_mul]

/-- Galí (2015), p. 178: equilibrium employment when `MRS = MPN/w` along the symmetric
allocation,
`N(w) = ((1 − α) A^{1−σ}/w)^{1/(φ + α + σ(1 − α))}`. Restated from the Chapter 4 project. -/
noncomputable def flexEmployment (σ φ α A w : ℝ) : ℝ :=
  ((1 - α) * A ^ (1 - σ) / w) ^ (φ + α + σ * (1 - α))⁻¹

/-- Galí (2015), p. 178: `N(w) > 0`. Restated from the Chapter 4 project. -/
theorem flexEmployment_pos {σ φ α A w : ℝ} (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    0 < flexEmployment σ φ α A w :=
  Real.rpow_pos_of_pos (div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) hw) _

/-- Galí (2015), p. 178: along the symmetric allocation, `MRS = MPN/w` holds for `N > 0`
**iff** `N = N(w)`. Restated from the Chapter 4 project. -/
theorem mrs_eq_mpn_div_iff {σ φ α A w N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) (hN : 0 < N) :
    mrs σ φ (A * N ^ (1 - α)) N = mpn α A N / w ↔ N = flexEmployment σ φ α A w := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) / w :=
    div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) hw
  have hm := mpn_pos hα1 hA hN
  have key := mrs_mul_eq (σ := σ) (φ := φ) (α := α) hA hN
  constructor
  · intro h
    rw [h] at key
    have hNk : N ^ (φ + α + σ * (1 - α)) = (1 - α) * A ^ (1 - σ) / w := by
      field_simp at key ⊢
      nlinarith [key]
    rw [flexEmployment, ← hNk, Real.rpow_rpow_inv hN.le hk.ne']
  · intro h
    have hNk : N ^ (φ + α + σ * (1 - α)) = (1 - α) * A ^ (1 - σ) / w := by
      rw [h, flexEmployment, Real.rpow_inv_rpow hc.le hk.ne']
    rw [hNk] at key
    have hc' : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
    field_simp at key ⊢
    nlinarith [key]

/-- Galí (2015), p. 178: **existence and uniqueness** of the equilibrium employment level under
a wedge `w > 0`. Restated from the Chapter 4 project. -/
theorem existsUnique_flex {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    ∃! N, 0 < N ∧ mrs σ φ (A * N ^ (1 - α)) N = mpn α A N / w :=
  ⟨flexEmployment σ φ α A w, ⟨flexEmployment_pos hα1 hA hw,
    (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw (flexEmployment_pos hα1 hA hw)).2 rfl⟩,
    fun _ ⟨hN, h⟩ => (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw hN).1 h⟩

/-- Galí (2015), p. 178: the equilibrium level is efficient **iff** there is no wedge,
`N(w) = N* ↔ w = 1` (for `w > 0`). -/
theorem flexEmployment_eq_eff_iff {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    flexEmployment σ φ α A w = effEmployment σ φ α A ↔ w = 1 := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
  constructor
  · intro h
    rw [flexEmployment, effEmployment] at h
    have h2 := congrArg (fun x => x ^ (φ + α + σ * (1 - α))) h
    rw [Real.rpow_inv_rpow (div_pos hc hw).le hk.ne', Real.rpow_inv_rpow hc.le hk.ne'] at h2
    rw [div_eq_iff hw.ne'] at h2
    nlinarith
  · intro h
    rw [h, flexEmployment, effEmployment, div_one]

/-- Galí (2015), p. 178: the flexible-price-and-wage equilibrium conditions, the wage rule
`W/P = M_w MRS` and the price rule `P = M_p (1 − τ) W/MPN` (employment subsidy `τ < 1`), imply
`MRS = MPN/((1 − τ) M_p M_w)`. -/
theorem flex_mrs_eq {Mp Mw τ W P mrsv mpnv : ℝ} (hP : 0 < P) (hτ : τ < 1)
    (hMp : 0 < Mp) (hMw : 0 < Mw) (hwage : W / P = Mw * mrsv)
    (hprice : P = Mp * ((1 - τ) * W / mpnv)) :
    mrsv = mpnv / ((1 - τ) * Mp * Mw) := by
  have h1 : (0 : ℝ) < 1 - τ := by linarith
  rw [hprice] at hwage
  have hW : W ≠ 0 := by
    intro h0
    rw [h0] at hprice
    simp at hprice
    linarith
  field_simp at hwage ⊢
  linear_combination (-1 : ℝ) * hwage

/-- Galí (2015), p. 179: under the flexible-price-and-wage rules, (27) `MRS = MPN` holds
**iff** `(1 − τ) M_p M_w = 1`. -/
theorem flex_efficient_iff_wedge {Mp Mw τ W P mrsv mpnv : ℝ} (hP : 0 < P) (hm : 0 < mpnv)
    (hτ : τ < 1) (hMp : 0 < Mp) (hMw : 0 < Mw) (hwage : W / P = Mw * mrsv)
    (hprice : P = Mp * ((1 - τ) * W / mpnv)) :
    mrsv = mpnv ↔ (1 - τ) * Mp * Mw = 1 := by
  rw [flex_mrs_eq hP hτ hMp hMw hwage hprice]
  have hw : 0 < (1 - τ) * Mp * Mw := mul_pos (mul_pos (by linarith) hMp) hMw
  rw [div_eq_iff hw.ne']
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h, mul_one]

/-- Galí (2015), p. 179: `(1 − τ) M_p M_w = 1` **iff** `τ = 1 − 1/(M_p M_w)`. -/
theorem wedge_eq_one_iff_subsidy {Mp Mw τ : ℝ} (hM : Mp * Mw ≠ 0) :
    (1 - τ) * Mp * Mw = 1 ↔ τ = 1 - 1 / (Mp * Mw) := by
  constructor
  · intro h
    have h1 : 1 - τ = 1 / (Mp * Mw) := by
      rw [eq_div_iff hM, ← mul_assoc]
      exact h
    linarith
  · intro h
    rw [h, sub_sub_cancel, mul_assoc, one_div_mul_cancel hM]

/-- Galí (2015), p. 179: the optimal subsidy `τ* = 1 − 1/(M_p M_w)` lies in `(0, 1)`. -/
theorem optimalSubsidy_mem {εp εw : ℝ} (hεp : 1 < εp) (hεw : 1 < εw) :
    0 < 1 - 1 / (markup εp * markup εw) ∧ 1 - 1 / (markup εp * markup εw) < 1 := by
  have h1 := one_lt_markup hεp
  have h2 := one_lt_markup hεw
  have hM : 1 < markup εp * markup εw := by nlinarith
  have hpos : 0 < 1 / (markup εp * markup εw) := by positivity
  refine ⟨?_, by linarith⟩
  have : 1 / (markup εp * markup εw) < 1 := (div_lt_one (by linarith)).2 hM
  linarith

/-- Galí (2015), p. 179 (consistency with ch. 4): with flexible wages (`M_w = 1`) the optimal
subsidy is Chapter 4's `τ = 1/ε_p`. -/
theorem optimalSubsidy_flexWages {εp : ℝ} (hεp : 1 < εp) :
    1 - 1 / (markup εp * 1) = 1 / εp := by
  have h1 : εp - 1 ≠ 0 := by linarith
  have h2 : εp ≠ 0 := by linarith
  rw [markup, mul_one]
  field_simp
  ring

/-- Galí (2015), pp. 178–179 (**the flexible-price-and-wage equilibrium**): along the
symmetric allocation with employment `N > 0`, if the wage rule `W/P = M_w MRS` and the price
rule `P = M_p (1 − τ) W/MPN` hold, then `N = N((1 − τ) M_p M_w)`, and the allocation is
efficient (`N = N*`) **iff** `τ = 1 − 1/(M_p M_w)`. -/
theorem flex_equilibrium {σ φ εp εw α A τ W P N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp)
    (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hτ : τ < 1) (hP : 0 < P)
    (hN : 0 < N) (hwage : W / P = markup εw * mrs σ φ (A * N ^ (1 - α)) N)
    (hprice : P = markup εp * ((1 - τ) * W / mpn α A N)) :
    N = flexEmployment σ φ α A ((1 - τ) * markup εp * markup εw) ∧
      (N = effEmployment σ φ α A ↔ τ = 1 - 1 / (markup εp * markup εw)) := by
  have hMp := markup_pos hεp
  have hMw := markup_pos hεw
  have hw : 0 < (1 - τ) * markup εp * markup εw := mul_pos (mul_pos (by linarith) hMp) hMw
  have h := flex_mrs_eq hP hτ hMp hMw hwage hprice
  have hN' := (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw hN).1 h
  refine ⟨hN', ?_⟩
  rw [hN', flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA hw,
    wedge_eq_one_iff_subsidy (mul_pos hMp hMw).ne']

/-- Galí (2015), pp. 178–179: the flexible-price-and-wage equilibrium allocation **maximises
welfare iff** `τ = 1 − 1/(M_p M_w)` (in the sense of the symmetric problem, which by
`Planner.planner_optimal_iff` is the planner's problem). -/
theorem flex_equilibrium_efficient_iff {σ φ εp εw α A Z τ W P N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hεp : 1 < εp) (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    (hτ : τ < 1) (hP : 0 < P) (hN : 0 < N)
    (hwage : W / P = markup εw * mrs σ φ (A * N ^ (1 - α)) N)
    (hprice : P = markup εp * ((1 - τ) * W / mpn α A N)) :
    (∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N) ↔
      τ = 1 - 1 / (markup εp * markup εw) := by
  rw [symWelfare_isMax_iff_foc hσ hφ hα0 hα1 hA hZ hN, mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN]
  exact (flex_equilibrium hσ hφ hεp hεw hα0 hα1 hA hτ hP hN hwage hprice).2

/-- Galí (2015), p. 179 (**the optimal subsidy exists and is unique**): exactly one subsidy
`τ < 1` makes the flexible-price-and-wage equilibrium employment efficient, namely
`τ = 1 − 1/(M_p M_w)`. -/
theorem existsUnique_subsidy {σ φ εp εw α A : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hεp : 1 < εp)
    (hεw : 1 < εw) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) :
    ∃! τ, τ < 1 ∧ flexEmployment σ φ α A ((1 - τ) * markup εp * markup εw)
      = effEmployment σ φ α A := by
  have hMp := markup_pos hεp
  have hMw := markup_pos hεw
  have hM : markup εp * markup εw ≠ 0 := (mul_pos hMp hMw).ne'
  have key : ∀ τ, τ < 1 → (flexEmployment σ φ α A ((1 - τ) * markup εp * markup εw)
      = effEmployment σ φ α A ↔ τ = 1 - 1 / (markup εp * markup εw)) := fun τ hτ => by
    rw [flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA
      (mul_pos (mul_pos (by linarith) hMp) hMw), wedge_eq_one_iff_subsidy hM]
  obtain ⟨-, h1⟩ := optimalSubsidy_mem hεp hεw
  exact ⟨1 - 1 / (markup εp * markup εw), ⟨h1, (key _ h1).2 rfl⟩,
    fun τ ⟨hτ, h⟩ => (key τ hτ).1 h⟩

end Gali.StickyWagesPrices.Efficiency
