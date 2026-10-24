/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The efficient allocation

Galí (2015), Chapter 4, §4.1, pp. 98–99, eqs. (1)–(3).

A benevolent planner maximises period utility
`U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z` (the book's utility of ch. 3, p. 54, with
`u(C) = (C^{1−σ} − 1)/(1 − σ)`, `log C` for `σ = 1`) where `C = (∫ C(i)^{(ε−1)/ε})^{ε/(ε−1)}`
is the CES consumption index, subject to the technologies `C(i) = A N(i)^{1−α}` and the labour
resource constraint `∫ N(i) = N`.

Goods are indexed by a probability space `(G, μ)`, which covers both the book's continuum
`[0, 1]` with Lebesgue measure (`planner_optimal_iff_unitInterval`) and finitely many goods with
weights `w i > 0`, `∑ w i = 1` (`planner_optimal_iff_finite`). An allocation is a measurable
`N(·) ≥ 0`, integrable, with `∫ N(i) > 0` (`Feasible`).

## Main results

* `aggConsumption_le`, `aggConsumption_eq_iff`: for a given total `N`, the CES index of
  `A N(i)^{1−α}` is at most `A N^{1−α}`, with equality **iff** `N(i) = N` for a.e. `i`
  (strict concavity of `x ↦ x^{(1−α)(ε−1)/ε}`, integrated Bernoulli/Jensen inequality).
* `welfare_le_symWelfare`, `welfare_eq_symWelfare_iff`: hence welfare is at most the welfare of
  the symmetric allocation with the same total employment, with equality iff symmetric.
* `marginal_utilities`, `hasDerivAt_output`: `−U_n/U_c = C^σ N^φ` (`mrs`) and
  `MPN = (1 − α) A N^{−α}` (`mpn`), as exact derivatives.
* `symWelfare_isMax_iff_foc`: along symmetric allocations, `N > 0` maximises welfare **iff**
  condition (3), `MRS = MPN`, holds (necessity and sufficiency).
* `mrs_sym_eq_mpn_iff`, `existsUnique_efficient`: (3) has exactly one solution,
  `N* = ((1 − α) A^{1−σ})^{1/(φ + α + σ(1 − α))}` (`effEmployment`), which is the unique
  maximiser; `symWelfare_lt` is the strict welfare loss away from `N*`.
* `planner_optimal_iff`: a feasible allocation is optimal **iff** (1) `C(i) = C`, (2)
  `N(i) = N` a.e. and (3) `MRS = MPN`; `planner_optimal_iff_effEmployment`: iff `N(i) = N*`
  a.e.; `planner_existsUnique`: the optimum exists and is unique up to null sets.
* `welfare_lt_of_not_symmetric`: any non-symmetric allocation is strictly worse than the
  optimum.

Utility definitions and the tangent-line lemmas are restated from the Chapter 3 project
(`Household.lean`); `weightMeasure` from its `CES.lean`.
-/

namespace Gali.MonetaryPolicyDesign.Efficient

open MeasureTheory Filter Topology

/-! ### Period utility (restated from the Chapter 3 project) -/

/-- Galí (2015), p. 54 (ch. 3): utility of consumption, `(C^{1−σ} − 1)/(1 − σ)` for `σ ≠ 1`
and `log C` for `σ = 1`. Restated from the Chapter 3 project. -/
noncomputable def utilC (σ C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else (C ^ (1 - σ) - 1) / (1 - σ)

/-- Galí (2015), p. 54 (ch. 3): disutility of labour `N^{1+φ}/(1+φ)`. Restated from the
Chapter 3 project. -/
noncomputable def disutilN (φ N : ℝ) : ℝ := N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 98 and p. 54: period utility `U(C, N; Z) = (u(C) − N^{1+φ}/(1+φ)) Z`.
Restated from the Chapter 3 project. -/
noncomputable def periodUtility (σ φ C N Z : ℝ) : ℝ := (utilC σ C - disutilN φ N) * Z

/-- Galí (2015), p. 99: marginal utility of consumption `u'(C) = C^{−σ}`. Restated from the
Chapter 3 project. -/
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

/-- Galí (2015), p. 99: marginal disutility of labour `N^φ`. Restated from the Chapter 3
project. -/
theorem hasDerivAt_disutilN {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (disutilN φ) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- Galí (2015), p. 99 (concavity of utility): marginal utility `C^{−σ}` is nonincreasing
for `σ > 0`. Restated from the Chapter 3 project. -/
theorem antitoneOn_margUtil {σ : ℝ} (hσ : 0 < σ) :
    AntitoneOn (fun C : ℝ => C ^ (-σ)) (Set.Ioi 0) :=
  fun _ ha _ _ hab => Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its
tangent lines (Galí (2015), p. 99, concavity of utility). Restated from the Chapter 3
project. -/
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

/-- Galí (2015), p. 99: the utility of consumption is concave for `σ > 0`, in tangent-line
form `u(y) ≤ u(x) + x^{−σ}(y − x)`. Restated from the Chapter 3 project. -/
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

/-- Galí (2015), p. 99: the disutility of labour is convex for `φ ≥ 0`, in tangent-line form
`v(x) + x^φ (y − x) ≤ v(y)`. Restated from the Chapter 3 project. -/
theorem disutilN_tangent_le {φ : ℝ} (hφ : 0 ≤ φ) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    disutilN φ x + x ^ φ * (y - x) ≤ disutilN φ y := by
  have h := le_tangent (f := fun N => -disutilN φ N) (f' := fun N => -N ^ φ) hx hy
    (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
      (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutilN hφ z).neg)
    (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
  linarith

/-- Galí (2015), p. 99 (`U_c > 0`): the utility of consumption is strictly increasing on
`(0, ∞)`, in both the `σ ≠ 1` and the log case. -/
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

/-- Galí (2015), p. 99: the marginal utilities `U_c = C^{−σ} Z`, `U_n = −N^φ Z` (exact
derivatives), whose ratio is the marginal rate of substitution `−U_n/U_c = C^σ N^φ`. -/
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

/-- Galí (2015), eq. (3), p. 99: the marginal rate of substitution `−U_n/U_c = C^σ N^φ`
(`marginal_utilities`). -/
noncomputable def mrs (σ φ C N : ℝ) : ℝ := C ^ σ * N ^ φ

/-- Galí (2015), p. 99: the marginal product of labour `MPN = (1 − α) A N^{−α}`. -/
noncomputable def mpn (α A N : ℝ) : ℝ := (1 - α) * A * N ^ (-α)

/-- Galí (2015), p. 99: `MPN` is the derivative of the technology `A N^{1−α}`. -/
theorem hasDerivAt_output {α A N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun n => A * n ^ (1 - α)) (mpn α A N) N := by
  refine ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A).congr_deriv ?_
  rw [mpn, show (1 : ℝ) - α - 1 = -α by ring]
  ring

/-- Galí (2015), p. 99: `MPN > 0` for `α < 1`, `A > 0`, `N > 0`. -/
theorem mpn_pos {α A N : ℝ} (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) : 0 < mpn α A N :=
  mul_pos (mul_pos (by linarith) hA) (Real.rpow_pos_of_pos hN _)

/-- Concavity of `x ↦ x^q` for `0 ≤ q ≤ 1` (Bernoulli), in tangent form at `N > 0`:
`x^q ≤ N^q (1 + q (x/N − 1))` (used for Galí (2015), p. 99, concavity of technology). -/
theorem rpow_le_tangent {q x N : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hN : 0 < N) (hx : 0 ≤ x) :
    x ^ q ≤ N ^ q * (1 + q * (x / N - 1)) := by
  have hs : -1 ≤ x / N - 1 := by have := div_nonneg hx hN.le; linarith
  have h := rpow_one_add_le_one_add_mul_self hs hq0 hq1
  rw [add_sub_cancel, Real.div_rpow hx hN.le] at h
  have hNq : 0 < N ^ q := Real.rpow_pos_of_pos hN q
  rw [div_le_iff₀ hNq] at h
  linarith

/-- Strict concavity of `x ↦ x^q` for `0 < q < 1`: equality in `rpow_le_tangent` forces
`x = N` (Galí (2015), p. 99, "concavity of utility and production functions"). -/
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

/-! ### The symmetric problem: condition (3) -/

/-- Galí (2015), p. 99: welfare of the symmetric allocation with total employment `N`,
`U(A N^{1−α}, N; Z)`. -/
noncomputable def symWelfare (σ φ α A Z N : ℝ) : ℝ := periodUtility σ φ (A * N ^ (1 - α)) N Z

/-- Galí (2015), p. 99: the efficient level of employment, the solution of (3) with
`C = A N^{1−α}`: `N* = ((1 − α) A^{1−σ})^{1/(φ + α + σ(1 − α))}`. -/
noncomputable def effEmployment (σ φ α A : ℝ) : ℝ :=
  ((1 - α) * A ^ (1 - σ)) ^ (φ + α + σ * (1 - α))⁻¹

/-- Galí (2015), p. 99: the derivative of symmetric welfare,
`(C^{−σ} MPN − N^φ) Z` with `C = A N^{1−α}`. -/
theorem hasDerivAt_symWelfare {σ φ α A Z N : ℝ} (hφ : 0 ≤ φ) (hA : 0 < A) (hN : 0 < N) :
    HasDerivAt (symWelfare σ φ α A Z)
      (((A * N ^ (1 - α)) ^ (-σ) * mpn α A N - N ^ φ) * Z) N := by
  have hC : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have h1 := (hasDerivAt_utilC σ hC).comp N (hasDerivAt_output (α := α) (A := A) hN)
  exact (HasDerivAt.sub h1 (hasDerivAt_disutilN hφ N)).mul_const Z

/-- Galí (2015), p. 99 (exponent bookkeeping): `MRS(A N^{1−α}, N) · (1 − α) A^{1−σ}
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

/-- Galí (2015), p. 99: the exponent `φ + α + σ(1 − α)` is positive. -/
theorem effExponent_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < φ + α + σ * (1 - α) := by
  have := mul_pos hσ (by linarith : (0 : ℝ) < 1 - α)
  linarith

/-- Galí (2015), p. 99: efficient employment is positive. -/
theorem effEmployment_pos {σ φ α A : ℝ} (hα1 : α < 1) (hA : 0 < A) :
    0 < effEmployment σ φ α A :=
  Real.rpow_pos_of_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) _

/-- Galí (2015), eq. (3), p. 99, **existence and uniqueness**: along the symmetric allocation
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

/-- Galí (2015), eq. (3), p. 99, **sufficiency**: if `MRS = MPN` at `N₀ > 0` (symmetric
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

/-- Galí (2015), eq. (3), p. 99, **necessity**: if `N₀ > 0` maximises symmetric welfare over
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

/-- Galí (2015), eq. (3), p. 99: along symmetric allocations, `N₀ > 0` maximises welfare
**iff** `MRS = MPN` at `N₀` (necessary and sufficient). -/
theorem symWelfare_isMax_iff_foc {σ φ α A Z N₀ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) (hN₀ : 0 < N₀) :
    (∀ N, 0 < N → symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z N₀) ↔
      mrs σ φ (A * N₀ ^ (1 - α)) N₀ = mpn α A N₀ :=
  ⟨foc_of_symWelfare_isMax hφ hA hZ hN₀,
    fun h _ hN => symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ hN₀ h hN⟩

/-- Galí (2015), p. 99: efficient employment `N*` maximises symmetric welfare. -/
theorem symWelfare_le_eff {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {N : ℝ} (hN : 0 < N) :
    symWelfare σ φ α A Z N ≤ symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ (effEmployment_pos hα1 hA)
    ((mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA (effEmployment_pos hα1 hA)).2 rfl) hN

/-- Galí (2015), p. 99: **strict** welfare loss away from efficient employment: for `N > 0`,
`N ≠ N*`, welfare is strictly below its efficient level. -/
theorem symWelfare_lt {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {N : ℝ} (hN : 0 < N)
    (hne : N ≠ effEmployment σ φ α A) :
    symWelfare σ φ α A Z N < symWelfare σ φ α A Z (effEmployment σ φ α A) := by
  refine lt_of_le_of_ne (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN) fun heq => hne ?_
  refine (mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN).1 (foc_of_symWelfare_isMax hφ hA hZ hN ?_)
  intro N' hN'
  rw [heq]
  exact symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN'

/-- Galí (2015), p. 99, **existence and uniqueness** of efficient employment: exactly one
`N > 0` maximises symmetric welfare, namely `N*`. -/
theorem existsUnique_efficient {σ φ α A Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) :
    ∃! N, 0 < N ∧ ∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N := by
  refine ⟨effEmployment σ φ α A, ⟨effEmployment_pos hα1 hA,
    fun N' hN' => symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hN'⟩, ?_⟩
  rintro N ⟨hN, hmax⟩
  exact (mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN).1 (foc_of_symWelfare_isMax hφ hA hZ hN hmax)

/-! ### Allocation across goods: conditions (1) and (2) -/

namespace Goods

variable {G : Type*} [MeasurableSpace G]

/-- Galí (2015), p. 99: the CES consumption index `C = (∫ C(i)^{(ε−1)/ε})^{ε/(ε−1)}`. -/
noncomputable def cesIndex (μ : Measure G) (ε : ℝ) (c : G → ℝ) : ℝ :=
  (∫ i, c i ^ ((ε - 1) / ε) ∂μ) ^ ((ε - 1) / ε)⁻¹

/-- Galí (2015), p. 99: the resource constraint for good `i`, `C(i) = A N(i)^{1−α}`. -/
noncomputable def goodsOutput (A α : ℝ) (n : G → ℝ) (i : G) : ℝ := A * n i ^ (1 - α)

/-- Galí (2015), p. 99: the consumption index of the allocation `N(·)`. -/
noncomputable def aggConsumption (μ : Measure G) (ε A α : ℝ) (n : G → ℝ) : ℝ :=
  cesIndex μ ε (goodsOutput A α n)

/-- Galí (2015), p. 99: a feasible labour allocation: measurable, `N(i) ≥ 0`, integrable,
with total employment `N = ∫ N(i) > 0`. -/
def Feasible (μ : Measure G) (n : G → ℝ) : Prop :=
  Measurable n ∧ (∀ i, 0 ≤ n i) ∧ Integrable n μ ∧ 0 < ∫ i, n i ∂μ

/-- Galí (2015), p. 98: the planner's objective, `U(C, N; Z)` with `C` the index of the
allocation and `N = ∫ N(i)`. -/
noncomputable def welfare (μ : Measure G) (σ φ ε A α Z : ℝ) (n : G → ℝ) : ℝ :=
  periodUtility σ φ (aggConsumption μ ε A α n) (∫ i, n i ∂μ) Z

variable {μ : Measure G}

/-- Galí (2015), p. 99: `(A x^{1−α})^r = A^r x^{(1−α) r}`. -/
theorem goodsOutput_rpow {A α r x : ℝ} (hA : 0 < A) (hx : 0 ≤ x) :
    (A * x ^ (1 - α)) ^ r = A ^ r * x ^ ((1 - α) * r) := by
  rw [Real.mul_rpow hA.le (Real.rpow_nonneg hx _), ← Real.rpow_mul hx]

/-- Galí (2015), p. 99: for `0 ≤ q ≤ 1`, `N(i)^q` is integrable when `N(·)` is feasible
(on a probability space). -/
theorem integrable_rpow [IsProbabilityMeasure μ] {n : G → ℝ} (hn : Feasible μ n) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Integrable (fun i => n i ^ q) μ := by
  obtain ⟨hm, h0, hi, -⟩ := hn
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add hi)
    (hm.pow_const q).aestronglyMeasurable (Eventually.of_forall fun i => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (h0 i) q)]
  have := rpow_le_tangent hq0 hq1 one_pos (h0 i)
  simp only [Real.one_rpow, div_one, one_mul] at this
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_right hq1 (h0 i)]

/-- Galí (2015), p. 99 (Jensen): for `0 < q < 1`, `∫ N(i)^q ≤ (∫ N(i))^q`, with equality
**iff** `N(i) = ∫ N` for a.e. `i`. -/
theorem integral_rpow_le [IsProbabilityMeasure μ] {n : G → ℝ} (hn : Feasible μ n) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ i, n i ^ q ∂μ ≤ (∫ i, n i ∂μ) ^ q ∧
      (∫ i, n i ^ q ∂μ = (∫ i, n i ∂μ) ^ q ↔ ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) := by
  set N := ∫ i, n i ∂μ with hNdef
  have hN : 0 < N := hn.2.2.2
  have hf := integrable_rpow hn hq0.le hq1.le
  set g : G → ℝ := fun i => N ^ q * (1 - q) + N ^ q * q / N * n i with hg
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

/-- Galí (2015), p. 99: the exponent `q = (1 − α)(ε − 1)/ε` lies in `(0, 1)`. -/
theorem q_mem {ε α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < (1 - α) * ((ε - 1) / ε) ∧ (1 - α) * ((ε - 1) / ε) < 1 := by
  have hr0 : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  have hr1 : (ε - 1) / ε < 1 := (div_lt_one (by linarith)).2 (by linarith)
  refine ⟨mul_pos (by linarith) hr0, ?_⟩
  calc (1 - α) * ((ε - 1) / ε) ≤ 1 * ((ε - 1) / ε) :=
        mul_le_mul_of_nonneg_right (by linarith) hr0.le
    _ < 1 := by linarith

/-- Galí (2015), p. 99: `∫ C(i)^r = A^r ∫ N(i)^{(1−α) r}`. -/
theorem integral_goodsOutput_rpow {A α r : ℝ} (hA : 0 < A) {n : G → ℝ} (hn : ∀ i, 0 ≤ n i) :
    ∫ i, goodsOutput A α n i ^ r ∂μ = A ^ r * ∫ i, n i ^ ((1 - α) * r) ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun i => goodsOutput_rpow hA (hn i))

/-- Galí (2015), p. 99: rewriting the index, `C = (A^r ∫ N(i)^q)^{1/r}`. -/
theorem aggConsumption_eq {ε A α : ℝ} (hA : 0 < A) {n : G → ℝ} (hn : ∀ i, 0 ≤ n i) :
    aggConsumption μ ε A α n
      = (A ^ ((ε - 1) / ε) * ∫ i, n i ^ ((1 - α) * ((ε - 1) / ε)) ∂μ) ^ ((ε - 1) / ε)⁻¹ := by
  rw [aggConsumption, cesIndex, integral_goodsOutput_rpow hA hn]

/-- Galí (2015), p. 99: `(A^r N^{(1−α) r})^{1/r} = A N^{1−α}`. -/
theorem symmetric_index {ε A α N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hN : 0 ≤ N) :
    (A ^ ((ε - 1) / ε) * N ^ ((1 - α) * ((ε - 1) / ε))) ^ ((ε - 1) / ε)⁻¹
      = A * N ^ (1 - α) := by
  have hr : (ε - 1) / ε ≠ 0 := (div_pos (by linarith) (by linarith)).ne'
  rw [Real.mul_rpow (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hN _),
    Real.rpow_rpow_inv hA.le hr, ← Real.rpow_mul hN, mul_assoc, mul_inv_cancel₀ hr, mul_one]

/-- Galí (2015), p. 99: the consumption index of a feasible allocation is positive. -/
theorem aggConsumption_pos [IsProbabilityMeasure μ] {ε A α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) {n : G → ℝ} (hn : Feasible μ n) :
    0 < aggConsumption μ ε A α n := by
  obtain ⟨hq0, hq1⟩ := q_mem hε hα0 hα1
  rw [aggConsumption_eq hA hn.2.1]
  refine Real.rpow_pos_of_pos (mul_pos (Real.rpow_pos_of_pos hA _) ?_) _
  have hnn : 0 ≤ fun i => n i ^ ((1 - α) * ((ε - 1) / ε)) :=
    fun i => Real.rpow_nonneg (hn.2.1 i) _
  rcases (integral_nonneg hnn).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz := (integral_eq_zero_iff_of_nonneg hnn (integrable_rpow hn hq0.le hq1.le)).1 h.symm
    have hn0 : (fun i => n i) =ᵐ[μ] 0 := by
      filter_upwards [hz] with i hi
      exact ((Real.rpow_eq_zero_iff_of_nonneg (hn.2.1 i)).1 hi).1
    have := hn.2.2.2
    rw [integral_congr_ae hn0] at this
    simp at this

/-- Galí (2015), eqs. (1)–(2), p. 99: for a feasible allocation with total employment
`N = ∫ N(i)`, the consumption index is at most `A N^{1−α}`. -/
theorem aggConsumption_le [IsProbabilityMeasure μ] {ε A α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) {n : G → ℝ} (hn : Feasible μ n) :
    aggConsumption μ ε A α n ≤ A * (∫ i, n i ∂μ) ^ (1 - α) := by
  obtain ⟨hq0, hq1⟩ := q_mem hε hα0 hα1
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  rw [aggConsumption_eq hA hn.2.1, ← symmetric_index hε hA hn.2.2.2.le]
  refine Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg hA.le _)
    (integral_nonneg fun i => Real.rpow_nonneg (hn.2.1 i) _)) ?_ (inv_nonneg.2 hr.le)
  exact mul_le_mul_of_nonneg_left (integral_rpow_le hn hq0 hq1).1 (Real.rpow_nonneg hA.le _)

/-- Galí (2015), eqs. (1)–(2), p. 99: the bound `C ≤ A N^{1−α}` holds with equality **iff**
`N(i) = N` for a.e. `i` (strict concavity). -/
theorem aggConsumption_eq_iff [IsProbabilityMeasure μ] {ε A α : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) {n : G → ℝ} (hn : Feasible μ n) :
    aggConsumption μ ε A α n = A * (∫ i, n i ∂μ) ^ (1 - α) ↔
      ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ := by
  obtain ⟨hq0, hq1⟩ := q_mem hε hα0 hα1
  have hr : 0 < (ε - 1) / ε := div_pos (by linarith) (by linarith)
  obtain ⟨hle, hiff⟩ := integral_rpow_le hn hq0 hq1
  rw [← hiff, aggConsumption_eq hA hn.2.1, ← symmetric_index hε hA hn.2.2.2.le]
  have hAr : 0 < A ^ ((ε - 1) / ε) := Real.rpow_pos_of_pos hA _
  constructor
  · intro h
    by_contra hne
    have hlt := lt_of_le_of_ne hle hne
    have := Real.rpow_lt_rpow (mul_nonneg hAr.le
      (integral_nonneg fun i => Real.rpow_nonneg (hn.2.1 i) _))
      (mul_lt_mul_of_pos_left hlt hAr) (inv_pos.2 hr)
    linarith
  · intro h
    rw [h]

/-- Galí (2015), p. 99: a constant allocation `N(i) = N > 0` is feasible. -/
theorem feasible_const [IsProbabilityMeasure μ] {N : ℝ} (hN : 0 < N) :
    Feasible μ (fun _ => N) :=
  ⟨measurable_const, fun _ => hN.le, integrable_const N, by simpa using hN⟩

/-- Galí (2015), p. 99: the welfare of the constant allocation `N(i) = N` is the symmetric
welfare `U(A N^{1−α}, N; Z)`. -/
theorem welfare_const [IsProbabilityMeasure μ] {σ φ ε A α Z N : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hN : 0 < N) :
    welfare μ σ φ ε A α Z (fun _ => N) = symWelfare σ φ α A Z N := by
  have h := (aggConsumption_eq_iff hε hα0 hα1 hA (feasible_const (μ := μ) hN)).2
    (Eventually.of_forall fun _ => by simp)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  rw [welfare, h, symWelfare]
  simp

/-- Galí (2015), p. 99: welfare of a feasible allocation is at most the welfare of the
symmetric allocation with the same total employment. -/
theorem welfare_le_symWelfare [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G → ℝ} (hn : Feasible μ n) :
    welfare μ σ φ ε A α Z n ≤ symWelfare σ φ α A Z (∫ i, n i ∂μ) := by
  unfold welfare symWelfare periodUtility
  refine mul_le_mul_of_nonneg_right (sub_le_sub_right ?_ _) hZ.le
  rcases (aggConsumption_le hε hα0 hα1 hA hn).lt_or_eq with h | h
  · exact (utilC_lt_utilC (aggConsumption_pos hε hα0 hα1 hA hn) h).le
  · rw [h]

/-- Galí (2015), eqs. (1)–(2), p. 99: equality in `welfare_le_symWelfare` holds **iff** the
allocation is symmetric, `N(i) = N` a.e. -/
theorem welfare_eq_symWelfare_iff [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G → ℝ} (hn : Feasible μ n) :
    welfare μ σ φ ε A α Z n = symWelfare σ φ α A Z (∫ i, n i ∂μ) ↔
      ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ := by
  rw [← aggConsumption_eq_iff hε hα0 hα1 hA hn]
  constructor
  · intro h
    by_contra hne
    have hlt := lt_of_le_of_ne (aggConsumption_le hε hα0 hα1 hA hn) hne
    have h1 := utilC_lt_utilC (σ := σ) (aggConsumption_pos hε hα0 hα1 hA hn) hlt
    unfold welfare symWelfare periodUtility at h
    have h2 := mul_right_cancel₀ hZ.ne' h
    linarith
  · intro h
    rw [welfare, symWelfare, h]

/-- Galí (2015), p. 102: a **non-symmetric** allocation (`N(i) ≠ N` on a set of positive
measure) is strictly worse than the symmetric allocation with the same total employment. -/
theorem welfare_lt_symWelfare [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G → ℝ} (hn : Feasible μ n)
    (hns : ¬ ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) :
    welfare μ σ φ ε A α Z n < symWelfare σ φ α A Z (∫ i, n i ∂μ) :=
  lt_of_le_of_ne (welfare_le_symWelfare hε hα0 hα1 hA hZ hn)
    fun h => hns ((welfare_eq_symWelfare_iff hε hα0 hα1 hA hZ hn).1 h)

/-- Galí (2015), p. 99: every feasible allocation is (weakly) worse than the efficient
allocation `N(i) = N*`. -/
theorem welfare_le_eff [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : G → ℝ}
    (hn : Feasible μ n) :
    welfare μ σ φ ε A α Z n ≤ symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  (welfare_le_symWelfare hε hα0 hα1 hA hZ hn).trans
    (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hn.2.2.2)

/-- Galí (2015), p. 102: any non-symmetric feasible allocation is **strictly** worse than
the efficient allocation. -/
theorem welfare_lt_of_not_symmetric [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    {n : G → ℝ} (hn : Feasible μ n) (hns : ¬ ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) :
    welfare μ σ φ ε A α Z n < symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  (welfare_lt_symWelfare hε hα0 hα1 hA hZ hn hns).trans_le
    (symWelfare_le_eff hσ hφ hα0 hα1 hA hZ hn.2.2.2)

/-- Galí (2015), eqs. (1)–(3), p. 99 (**necessary and sufficient**): a feasible allocation
maximises welfare over all feasible allocations iff (1) `C(i) = C` a.e., (2) `N(i) = N` a.e.
and (3) `MRS = MPN`, where `C` is the consumption index and `N = ∫ N(i)`. -/
theorem planner_optimal_iff [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    {n : G → ℝ} (hn : Feasible μ n) :
    (∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n' ≤ welfare μ σ φ ε A α Z n) ↔
      (∀ᵐ i ∂μ, goodsOutput A α n i = aggConsumption μ ε A α n) ∧
      (∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ) ∧
      mrs σ φ (aggConsumption μ ε A α n) (∫ i, n i ∂μ) = mpn α A (∫ i, n i ∂μ) := by
  set N := ∫ i, n i ∂μ with hNdef
  have hN : 0 < N := hn.2.2.2
  constructor
  · intro hopt
    have hsym : ∀ᵐ i ∂μ, n i = N := by
      refine (welfare_eq_symWelfare_iff (σ := σ) (φ := φ) hε hα0 hα1 hA hZ hn).1 (le_antisymm
        (welfare_le_symWelfare hε hα0 hα1 hA hZ hn) ?_)
      rw [← welfare_const (μ := μ) hε hα0 hα1 hA hN]
      exact hopt _ (feasible_const hN)
    have hC := (aggConsumption_eq_iff hε hα0 hα1 hA hn).2 hsym
    have hmax : ∀ N', 0 < N' → symWelfare σ φ α A Z N' ≤ symWelfare σ φ α A Z N := by
      intro N' hN'
      rw [← welfare_const (μ := μ) hε hα0 hα1 hA hN',
        ← (welfare_eq_symWelfare_iff hε hα0 hα1 hA hZ hn).2 hsym]
      exact hopt _ (feasible_const hN')
    refine ⟨?_, hsym, ?_⟩
    · filter_upwards [hsym] with i hi
      rw [goodsOutput, hi, hC]
    · rw [hC]
      exact foc_of_symWelfare_isMax hφ hA hZ hN hmax
  · rintro ⟨-, hsym, hfoc⟩ n' hn'
    have hC := (aggConsumption_eq_iff hε hα0 hα1 hA hn).2 hsym
    rw [hC] at hfoc
    rw [(welfare_eq_symWelfare_iff hε hα0 hα1 hA hZ hn).2 hsym]
    exact (welfare_le_symWelfare hε hα0 hα1 hA hZ hn').trans
      (symWelfare_le_of_foc hσ hφ hα0 hα1 hA hZ hN hfoc hn'.2.2.2)

/-- Galí (2015), §4.1, p. 99: a feasible allocation is optimal **iff** `N(i) = N*` for a.e.
`i`, where `N*` is efficient employment (`effEmployment`). -/
theorem planner_optimal_iff_effEmployment [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ}
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A)
    (hZ : 0 < Z) {n : G → ℝ} (hn : Feasible μ n) :
    (∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n' ≤ welfare μ σ φ ε A α Z n) ↔
      ∀ᵐ i ∂μ, n i = effEmployment σ φ α A := by
  rw [planner_optimal_iff hσ hφ hε hα0 hα1 hA hZ hn]
  have hN : 0 < ∫ i, n i ∂μ := hn.2.2.2
  constructor
  · rintro ⟨-, hsym, hfoc⟩
    rw [(aggConsumption_eq_iff hε hα0 hα1 hA hn).2 hsym,
      mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN] at hfoc
    filter_upwards [hsym] with i hi
    rw [hi, hfoc]
  · intro h
    have hint : ∫ i, n i ∂μ = effEmployment σ φ α A := by
      rw [integral_congr_ae h]
      simp
    have hsym : ∀ᵐ i ∂μ, n i = ∫ j, n j ∂μ := by
      filter_upwards [h] with i hi
      rw [hi, hint]
    have hC := (aggConsumption_eq_iff hε hα0 hα1 hA hn).2 hsym
    refine ⟨?_, hsym, ?_⟩
    · filter_upwards [hsym] with i hi
      rw [goodsOutput, hi, hC]
    · rw [hC, mrs_sym_eq_mpn_iff hσ hφ hα0 hα1 hA hN, hint]

/-- Galí (2015), §4.1, p. 99, **existence and uniqueness**: the efficient allocation
`N(i) = N*` is feasible and optimal, and every optimal allocation equals it a.e. -/
theorem planner_existsUnique [IsProbabilityMeasure μ] {σ φ ε A α Z : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) :
    Feasible μ (fun _ => effEmployment σ φ α A) ∧
      (∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n'
        ≤ welfare μ σ φ ε A α Z (fun _ => effEmployment σ φ α A)) ∧
      ∀ n, Feasible μ n →
        (∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n' ≤ welfare μ σ φ ε A α Z n) →
        ∀ᵐ i ∂μ, n i = effEmployment σ φ α A := by
  have hf := feasible_const (μ := μ) (effEmployment_pos (σ := σ) (φ := φ) hα1 hA)
  refine ⟨hf, (planner_optimal_iff_effEmployment hσ hφ hε hα0 hα1 hA hZ hf).2
    (Eventually.of_forall fun _ => rfl), fun n hn hopt => ?_⟩
  exact (planner_optimal_iff_effEmployment hσ hφ hε hα0 hα1 hA hZ hn).1 hopt

/-! ### The continuum `[0, 1]` -/

/-- Galí (2015), p. 99: Lebesgue measure on the goods continuum `[0, 1]` is a probability
measure. -/
theorem isProbabilityMeasure_unitInterval :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
  ⟨by simp [Real.volume_Icc]⟩

/-- Galí (2015), eqs. (1)–(3), p. 99, on the book's **continuum of goods `[0, 1]`**: a
feasible allocation is optimal iff (1), (2) and (3) hold, iff `N(i) = N*` for a.e. `i`. -/
theorem planner_optimal_iff_unitInterval {σ φ ε A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ)
    (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {n : ℝ → ℝ}
    (hn : Feasible (volume.restrict (Set.Icc 0 1)) n) :
    ((∀ n' : ℝ → ℝ, Feasible (volume.restrict (Set.Icc 0 1)) n' →
        welfare (volume.restrict (Set.Icc 0 1)) σ φ ε A α Z n'
          ≤ welfare (volume.restrict (Set.Icc 0 1)) σ φ ε A α Z n) ↔
      (∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)),
          goodsOutput A α n i = aggConsumption (volume.restrict (Set.Icc 0 1)) ε A α n) ∧
        (∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)), n i = ∫ j in Set.Icc 0 1, n j) ∧
        mrs σ φ (aggConsumption (volume.restrict (Set.Icc 0 1)) ε A α n)
          (∫ i in Set.Icc 0 1, n i) = mpn α A (∫ i in Set.Icc 0 1, n i)) ∧
    ((∀ n' : ℝ → ℝ, Feasible (volume.restrict (Set.Icc 0 1)) n' →
        welfare (volume.restrict (Set.Icc 0 1)) σ φ ε A α Z n'
          ≤ welfare (volume.restrict (Set.Icc 0 1)) σ φ ε A α Z n) ↔
      ∀ᵐ i ∂(volume.restrict (Set.Icc 0 1)), n i = effEmployment σ φ α A) := by
  have := isProbabilityMeasure_unitInterval
  exact ⟨planner_optimal_iff hσ hφ hε hα0 hα1 hA hZ hn,
    planner_optimal_iff_effEmployment hσ hφ hε hα0 hα1 hA hZ hn⟩

end Goods

/-! ### Finitely many goods -/

namespace Finite

open Goods

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Galí (2015), p. 99 (finitely many goods): the measure placing weight `w i` on good `i`.
Restated from the Chapter 3 project. -/
noncomputable def weightMeasure (w : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- Galí (2015), p. 99: the weighted measure gives good `x` mass `w x`. Restated from the
Chapter 3 project. -/
theorem weightMeasure_singleton {w : ι → ℝ} (x : ι) :
    weightMeasure w {x} = ENNReal.ofReal (w x) := by
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [Measure.dirac_apply' _ (measurableSet_singleton x), hb]
  · simp

omit [MeasurableSingletonClass ι] in
/-- Galí (2015), p. 99: with `w ≥ 0` and `∑ w = 1` the weighted measure is a probability
measure. -/
theorem isProbabilityMeasure_weightMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) : IsProbabilityMeasure (weightMeasure w) := by
  constructor
  rw [weightMeasure, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hw i, h1, ENNReal.ofReal_one]

/-- Galí (2015), p. 99: integrals against the weighted measure are weighted sums,
`∫ f = ∑ᵢ w i f i`. Restated from the Chapter 3 project. -/
theorem integral_weightMeasure {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1)
    (f : ι → ℝ) : ∫ i, f i ∂(weightMeasure w) = ∑ i, w i * f i := by
  have := isProbabilityMeasure_weightMeasure hw h1
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.real, weightMeasure_singleton, ENNReal.toReal_ofReal (hw i), smul_eq_mul]

/-- Galí (2015), p. 99: with positive weights, "almost every good" means every good. -/
theorem ae_weightMeasure_iff {w : ι → ℝ} (hw : ∀ i, 0 < w i) {p : ι → Prop} :
    (∀ᵐ i ∂(weightMeasure w), p i) ↔ ∀ i, p i := by
  refine ⟨fun h i => ?_, fun h => Eventually.of_forall h⟩
  by_contra hi
  have hpos : weightMeasure w {i} ≠ 0 := by
    rw [weightMeasure_singleton]
    exact (ENNReal.ofReal_pos.2 (hw i)).ne'
  exact hpos (measure_mono_null (fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hi)
    (ae_iff.1 h))

/-- Galí (2015), p. 99: for finitely many goods, an allocation `N(i) ≥ 0` with
`∑ w N(i) > 0` is feasible. -/
theorem feasible_of_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) {n : ι → ℝ}
    (hn : ∀ i, 0 ≤ n i) (hpos : 0 < ∑ i, w i * n i) : Feasible (weightMeasure w) n := by
  have := isProbabilityMeasure_weightMeasure hw h1
  exact ⟨Measurable.of_discrete, hn, Integrable.of_finite, by
    rwa [integral_weightMeasure hw h1]⟩

/-- Galí (2015), §4.1, p. 99, for **finitely many goods** with weights `w i > 0`,
`∑ w i = 1`: with `C = (∑ w (A N(i)^{1−α})^r)^{1/r}` and `N = ∑ w N(i)`, an allocation
`N(·) ≥ 0` with `N > 0` maximises `U(C, N; Z)` over all such allocations **iff**
`N(i) = N*` for **every** good `i`. -/
theorem planner_optimal_iff_finite {σ φ ε A α Z : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (h1 : ∑ i, w i = 1) {n : ι → ℝ} (hn : ∀ i, 0 ≤ n i) (hpos : 0 < ∑ i, w i * n i) :
    (∀ n' : ι → ℝ, (∀ i, 0 ≤ n' i) → 0 < ∑ i, w i * n' i →
      periodUtility σ φ ((∑ i, w i * (A * n' i ^ (1 - α)) ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹)
          (∑ i, w i * n' i) Z
        ≤ periodUtility σ φ ((∑ i, w i * (A * n i ^ (1 - α)) ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹)
          (∑ i, w i * n i) Z) ↔
      ∀ i, n i = effEmployment σ φ α A := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have := isProbabilityMeasure_weightMeasure hw0 h1
  have hW : ∀ m : ι → ℝ, welfare (weightMeasure w) σ φ ε A α Z m
      = periodUtility σ φ ((∑ i, w i * (A * m i ^ (1 - α)) ^ ((ε - 1) / ε)) ^ ((ε - 1) / ε)⁻¹)
          (∑ i, w i * m i) Z := fun m => by
    rw [welfare, aggConsumption, cesIndex, integral_weightMeasure hw0 h1,
      integral_weightMeasure hw0 h1]
    rfl
  have h := planner_optimal_iff_effEmployment hσ hφ hε hα0 hα1 hA hZ
    (feasible_of_nonneg hw0 h1 hn hpos)
  rw [ae_weightMeasure_iff hw] at h
  rw [← h, hW]
  constructor
  · intro hopt n' hn'
    rw [hW]
    have hf := hn'
    rw [Feasible, integral_weightMeasure hw0 h1] at hf
    exact hopt n' hf.2.1 hf.2.2.2
  · intro hopt n' hn' hpos'
    rw [← hW]
    exact hopt n' (feasible_of_nonneg hw0 h1 hn' hpos')

end Finite

end Gali.MonetaryPolicyDesign.Efficient
