/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MonetaryPolicyDesign.Efficient

/-!
# Sources of suboptimality in the basic New Keynesian model

Galí (2015), Chapter 4, §4.2, pp. 100–102.

## §4.2.1 Monopolistic competition (pp. 100–101)

A firm facing the isoelastic demand `Y(i) = (P(i)/P)^{−ε} Y` with technology
`Y(i) = A N(i)^{1−α}` and an employment subsidy at rate `τ < 1` (labour costs `(1 − τ) W`)
chooses employment (equivalently its price, `inverse_demand_iff`) to maximise profits.

* `firm_optimal_iff`: `N₀ > 0` is profit maximising **iff** the price-setting rule
  `P(i) = M (1 − τ) W / MPN(i)` holds, `M = ε/(ε − 1)`; `firm_existsUnique`: the optimum exists
  and is unique, hence identical across firms (`optimal_identical`); in a symmetric allocation
  this is `P = M (1 − τ) W/MPN` (`flex_price_rule`), and with the household's condition
  `W/P = MRS` gives `MRS = MPN/(M(1 − τ))` (`flex_mrs`), i.e. `MRS = MPN/M < MPN` for `τ = 0`.
* `mrs_eq_mpn_div_iff`, `existsUnique_flex`: for any wedge `w > 0` the condition
  `MRS = MPN/w` has exactly one solution `N(w)` (`flexEmployment`), with `N(1) = N*`.
* `flexEmployment_lt_eff`: a markup `w > 1` gives employment **strictly below** the efficient
  level; `lt_of_wedge` is the book's monotonicity argument (MRS increasing, MPN
  nonincreasing); `flex_welfare_lt`: the welfare loss is strict.
* `wedge_eq_one_iff_subsidy`, `flex_efficient_iff_subsidy`: the flexible-price allocation is
  efficient **iff** `M(1 − τ) = 1` **iff** `τ = 1/ε` (so the optimal subsidy is unique).

## §4.2.2 Sticky prices (pp. 101–102)

* `avgMarkup`, `mrs_eq_avgMarkup`: with the optimal subsidy, `MRS = MPN · M/M_t`;
  `foc_iff_avgMarkup`: (3) holds iff `M_t = M`; `employment_avgMarkup`: employment is
  `N(M_t/M)`, below/at/above `N*` iff `M_t >/=/< M`.
* `dispersion_violates_symmetry`, `dispersion_welfare_loss`: if relative prices are not all
  equal, the induced allocation violates (1) and (2) and is **strictly** worse than both the
  symmetric allocation with the same employment and the efficient allocation.
-/

namespace Gali.MonetaryPolicyDesign.Distortions

open MeasureTheory Filter Topology
open Gali.MonetaryPolicyDesign.Efficient

/-! ### The desired markup -/

/-- Galí (2015), p. 100: the desired (gross) markup `M = ε/(ε − 1)`. -/
noncomputable def markup (ε : ℝ) : ℝ := ε / (ε - 1)

/-- Galí (2015), p. 100: `M > 1` for `ε > 1`. -/
theorem one_lt_markup {ε : ℝ} (hε : 1 < ε) : 1 < markup ε := by
  rw [markup, one_lt_div (by linarith)]
  linarith

/-- Galí (2015), p. 100: `M > 0` for `ε > 1`. -/
theorem markup_pos {ε : ℝ} (hε : 1 < ε) : 0 < markup ε :=
  lt_trans one_pos (one_lt_markup hε)

/-- Galí (2015), p. 100: `M · (ε − 1)/ε = 1`. -/
theorem markup_mul_r {ε : ℝ} (hε : 1 < ε) : markup ε * ((ε - 1) / ε) = 1 := by
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : ε ≠ 0 := by linarith
  rw [markup]
  field_simp

/-! ### The firm's problem under flexible prices -/

/-- Galí (2015), p. 100: the inverse of the isoelastic demand `y = (P(i)/P)^{−ε} Y`, the price
at which the firm sells `y`: `P(i) = P (y/Y)^{−1/ε}`. -/
noncomputable def invDemand (ε P Y y : ℝ) : ℝ := P * (y / Y) ^ (-ε⁻¹)

/-- Galí (2015), p. 100: choosing a price is equivalent to choosing a quantity: for `P(i)`,
`P`, `Y`, `y > 0`, `y = (P(i)/P)^{−ε} Y` iff `P(i) = P (y/Y)^{−1/ε}`. -/
theorem inverse_demand_iff {ε P Y y Pi : ℝ} (hε : 0 < ε) (hP : 0 < P) (hY : 0 < Y)
    (hy : 0 < y) (hPi : 0 < Pi) : y = (Pi / P) ^ (-ε) * Y ↔ Pi = invDemand ε P Y y := by
  have hne : -ε ≠ 0 := by linarith
  have hx : 0 < Pi / P := div_pos hPi hP
  rw [invDemand]
  constructor
  · intro h
    rw [h, mul_div_assoc, div_self hY.ne', mul_one, ← Real.rpow_neg_one ε, ← Real.rpow_mul hx.le]
    rw [show -ε * -ε ^ (-1 : ℝ) = 1 by rw [Real.rpow_neg_one]; field_simp, Real.rpow_one]
    field_simp
  · intro h
    have hyY : 0 < y / Y := div_pos hy hY
    have e : Pi / P = (y / Y) ^ (-ε⁻¹) := by rw [h]; field_simp
    rw [e, ← Real.rpow_mul hyY.le, show -ε⁻¹ * -ε = 1 by field_simp, Real.rpow_one]
    field_simp

/-- Galí (2015), p. 100: profits of a firm employing `N` (subsidy `τ`):
`P(i) Y(i) − (1 − τ) W N` with `Y(i) = A N^{1−α}` sold at the demand price. -/
noncomputable def firmProfit (ε α A W τ P Y N : ℝ) : ℝ :=
  invDemand ε P Y (A * N ^ (1 - α)) * (A * N ^ (1 - α)) - (1 - τ) * W * N

/-- Galí (2015), p. 100: the revenue constant `K = P Y^{1/ε} A^{(ε−1)/ε}`. -/
noncomputable def revConst (ε A P Y : ℝ) : ℝ := P * Y ^ ε⁻¹ * A ^ ((ε - 1) / ε)

/-- Galí (2015), p. 100: revenue is `P(i) Y(i) = K N^q`, `q = (1 − α)(ε − 1)/ε`. -/
theorem revenue_eq {ε α A P Y N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hY : 0 < Y) (hN : 0 < N) :
    invDemand ε P Y (A * N ^ (1 - α)) * (A * N ^ (1 - α))
      = revConst ε A P Y * N ^ ((1 - α) * ((ε - 1) / ε)) := by
  have hy : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  have hε0 : ε ≠ 0 := by linarith
  have e2 : A ^ ((ε - 1) / ε) * N ^ ((1 - α) * ((ε - 1) / ε))
      = (A * N ^ (1 - α)) ^ ((ε - 1) / ε) := (Goods.goodsOutput_rpow hA hN.le).symm
  have e : (A * N ^ (1 - α)) ^ ((ε - 1) / ε)
      = (A * N ^ (1 - α)) ^ (-ε⁻¹) * (A * N ^ (1 - α)) := by
    rw [show (ε - 1) / ε = -ε⁻¹ + 1 by field_simp; ring, Real.rpow_add hy, Real.rpow_one]
  rw [invDemand, revConst, mul_assoc (P * Y ^ ε⁻¹), e2, Real.div_rpow hy.le hY.le,
    Real.rpow_neg hY.le, div_inv_eq_mul, e]
  ring

/-- Galí (2015), p. 100: marginal revenue of labour, `K q N^q / N = r P(i) MPN(i)`
with `r = (ε − 1)/ε`. -/
theorem marginal_revenue_eq {ε α A P Y N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hY : 0 < Y)
    (hN : 0 < N) :
    revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N ^ ((1 - α) * ((ε - 1) / ε)) / N
      = (ε - 1) / ε * invDemand ε P Y (A * N ^ (1 - α)) * mpn α A N := by
  have h := revenue_eq (α := α) (P := P) hε hA hY hN
  have hN1 : N ^ (1 - α) / N = N ^ (-α) := by
    rw [← Real.rpow_sub_one hN.ne']
    ring_nf
  have e : revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N ^ ((1 - α) * ((ε - 1) / ε)) / N
      = (1 - α) * ((ε - 1) / ε) * (revConst ε A P Y * N ^ ((1 - α) * ((ε - 1) / ε))) / N := by
    ring
  rw [e, ← h, mpn, ← hN1]
  ring

/-- Galí (2015), p. 100: the derivative of profits in `N`, `K q N^{q−1} − (1 − τ) W`. -/
theorem hasDerivAt_profit {ε α A W τ P Y N : ℝ} (hε : 1 < ε) (hA : 0 < A) (hY : 0 < Y)
    (hN : 0 < N) :
    HasDerivAt (firmProfit ε α A W τ P Y)
      (revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N ^ ((1 - α) * ((ε - 1) / ε)) / N
        - (1 - τ) * W) N := by
  set q := (1 - α) * ((ε - 1) / ε)
  have hfun : ∀ᶠ M in 𝓝 N, firmProfit ε α A W τ P Y M
      = revConst ε A P Y * M ^ q - (1 - τ) * W * M := by
    filter_upwards [Ioi_mem_nhds hN] with M hM
    rw [firmProfit, revenue_eq hε hA hY hM]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hfun
  have h1 := ((Real.hasDerivAt_rpow_const (p := q) (Or.inl hN.ne')).const_mul
    (revConst ε A P Y))
  have h2 := (hasDerivAt_id N).const_mul ((1 - τ) * W)
  refine (HasDerivAt.sub h1 h2).congr_deriv ?_
  rw [Real.rpow_sub_one hN.ne']
  simp only [mul_one]
  ring

/-- Galí (2015), p. 100: the first-order condition `K q N^q/N = (1 − τ) W` is equivalent to
the price-setting rule `P(i) = M (1 − τ) W / MPN(i)`. -/
theorem foc_iff_price_rule {ε α A W τ P Y N : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hY : 0 < Y) (hN : 0 < N) :
    revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N ^ ((1 - α) * ((ε - 1) / ε)) / N
        = (1 - τ) * W ↔
      invDemand ε P Y (A * N ^ (1 - α)) = markup ε * ((1 - τ) * W / mpn α A N) := by
  rw [marginal_revenue_eq hε hA hY hN]
  have hm := mpn_pos hα1 hA hN
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [markup]
  constructor
  · intro h
    rw [← h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Galí (2015), p. 100: the firm's problem is concave: if the first-order condition holds at
`N₀ > 0` then `N₀` maximises profits over `N > 0` (sufficiency). -/
theorem profit_le_of_foc {ε α A W τ P Y N₀ : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) (hN₀ : 0 < N₀)
    (hfoc : revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)) * N₀ ^ ((1 - α) * ((ε - 1) / ε)) / N₀
      = (1 - τ) * W) {N : ℝ} (hN : 0 < N) :
    firmProfit ε α A W τ P Y N ≤ firmProfit ε α A W τ P Y N₀ := by
  obtain ⟨hq0, hq1⟩ := Goods.q_mem hε hα0 hα1
  set q := (1 - α) * ((ε - 1) / ε) with hqdef
  have hK : 0 < revConst ε A P Y :=
    mul_pos (mul_pos hP (Real.rpow_pos_of_pos hY _)) (Real.rpow_pos_of_pos hA _)
  have ht := rpow_le_tangent hq0.le hq1.le hN₀ hN.le
  rw [firmProfit, firmProfit, revenue_eq hε hA hY hN, revenue_eq hε hA hY hN₀]
  have e : revConst ε A P Y * (N₀ ^ q * (1 + q * (N / N₀ - 1)))
      = revConst ε A P Y * N₀ ^ q + revConst ε A P Y * q * N₀ ^ q / N₀ * (N - N₀) := by
    field_simp
  have h1 := mul_le_mul_of_nonneg_left ht hK.le
  rw [e, hfoc] at h1
  nlinarith

/-- Galí (2015), p. 100: **the firm's optimum** (necessary and sufficient): `N₀ > 0` maximises
profits over `N > 0` iff the price-setting rule `P(i) = M (1 − τ) W / MPN(i)` holds. -/
theorem firm_optimal_iff {ε α A W τ P Y N₀ : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) (hN₀ : 0 < N₀) :
    (∀ N, 0 < N → firmProfit ε α A W τ P Y N ≤ firmProfit ε α A W τ P Y N₀) ↔
      invDemand ε P Y (A * N₀ ^ (1 - α)) = markup ε * ((1 - τ) * W / mpn α A N₀) := by
  rw [← foc_iff_price_rule hε hα1 hA hY hN₀]
  constructor
  · intro hmax
    have hloc : IsLocalMax (firmProfit ε α A W τ P Y) N₀ :=
      Filter.mem_of_superset (Ioi_mem_nhds hN₀) fun N hN => hmax N hN
    have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_profit (W := W) (τ := τ) hε hA hY hN₀)
    linarith
  · intro h N hN
    exact profit_le_of_foc hε hα0 hα1 hA hY hP hN₀ h hN

/-- Galí (2015), p. 100: the profit-maximising employment level,
`N° = ((1 − τ) W/(K q))^{1/(q − 1)}`. -/
noncomputable def firmEmployment (ε α A W τ P Y : ℝ) : ℝ :=
  ((1 - τ) * W / (revConst ε A P Y * ((1 - α) * ((ε - 1) / ε)))) ^
    ((1 - α) * ((ε - 1) / ε) - 1)⁻¹

/-- Galí (2015), p. 100, **existence and uniqueness** of the firm's optimum (for `τ < 1`,
`W > 0`): exactly one `N > 0` maximises profits, `firmEmployment`. -/
theorem firm_existsUnique {ε α A W τ P Y : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) (hτ : τ < 1) (hW : 0 < W) :
    ∃! N, 0 < N ∧ ∀ N', 0 < N' → firmProfit ε α A W τ P Y N' ≤ firmProfit ε α A W τ P Y N := by
  obtain ⟨hq0, hq1⟩ := Goods.q_mem hε hα0 hα1
  set q := (1 - α) * ((ε - 1) / ε) with hqdef
  have hK : 0 < revConst ε A P Y :=
    mul_pos (mul_pos hP (Real.rpow_pos_of_pos hY _)) (Real.rpow_pos_of_pos hA _)
  have hc : 0 < (1 - τ) * W / (revConst ε A P Y * q) :=
    div_pos (mul_pos (by linarith) hW) (mul_pos hK hq0)
  have hq1' : q - 1 ≠ 0 := by linarith
  -- the first-order condition is `N^{q−1} = (1 − τ) W/(K q)`
  have hfoc_iff : ∀ N, 0 < N →
      (revConst ε A P Y * q * N ^ q / N = (1 - τ) * W ↔
        N ^ (q - 1) = (1 - τ) * W / (revConst ε A P Y * q)) := by
    intro N hN
    rw [Real.rpow_sub_one hN.ne', eq_div_iff (mul_pos hK hq0).ne']
    constructor <;> intro h <;> rw [← h] <;> ring
  have hpos : 0 < firmEmployment ε α A W τ P Y := Real.rpow_pos_of_pos hc _
  refine ⟨firmEmployment ε α A W τ P Y, ⟨hpos, fun N' hN' => ?_⟩, ?_⟩
  · refine profit_le_of_foc hε hα0 hα1 hA hY hP hpos ?_ hN'
    rw [hfoc_iff _ hpos, firmEmployment, ← hqdef, Real.rpow_inv_rpow hc.le hq1']
  · rintro N ⟨hN, hmax⟩
    have h := (firm_optimal_iff hε hα0 hα1 hA hY hP hN).1 hmax
    rw [← foc_iff_price_rule hε hα1 hA hY hN, ← hqdef, hfoc_iff _ hN] at h
    rw [firmEmployment, ← hqdef, ← h, Real.rpow_rpow_inv hN.le hq1']

/-- Galí (2015), p. 100: "the profit maximising price is identical across firms": any two
profit-maximising employment levels (hence outputs and prices) coincide. -/
theorem optimal_identical {ε α A W τ P Y N₁ N₂ : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hP : 0 < P) (hτ : τ < 1) (hW : 0 < W) (hN₁ : 0 < N₁)
    (hN₂ : 0 < N₂)
    (h₁ : ∀ N, 0 < N → firmProfit ε α A W τ P Y N ≤ firmProfit ε α A W τ P Y N₁)
    (h₂ : ∀ N, 0 < N → firmProfit ε α A W τ P Y N ≤ firmProfit ε α A W τ P Y N₂) :
    N₁ = N₂ ∧ invDemand ε P Y (A * N₁ ^ (1 - α)) = invDemand ε P Y (A * N₂ ^ (1 - α)) := by
  have h := (firm_existsUnique hε hα0 hα1 hA hY hP hτ hW).unique ⟨hN₁, h₁⟩ ⟨hN₂, h₂⟩
  exact ⟨h, by rw [h]⟩

/-- Galí (2015), p. 100: in a symmetric allocation (`Y = A N^{1−α}`, so the firm's price is the
price level, `P(i) = P`), profit maximisation is the rule `P = M (1 − τ) W/MPN`. -/
theorem flex_price_rule {ε α A W τ P N : ℝ} (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hA : 0 < A) (hP : 0 < P) (hN : 0 < N) :
    (∀ N', 0 < N' → firmProfit ε α A W τ P (A * N ^ (1 - α)) N'
        ≤ firmProfit ε α A W τ P (A * N ^ (1 - α)) N) ↔
      P = markup ε * ((1 - τ) * W / mpn α A N) := by
  have hY : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  rw [firm_optimal_iff hε hα0 hα1 hA hY hP hN, invDemand, div_self hY.ne', Real.one_rpow,
    mul_one]

/-- Galí (2015), p. 100 (τ = 0) and p. 101: with flexible prices `P = M (1 − τ) W/MPN` and the
household's condition `W/P = MRS`, `MRS = MPN/(M (1 − τ))`. For `τ = 0`, `MRS = MPN/M`. -/
theorem flex_mrs {ε α A W τ P C N σ φ : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hN : 0 < N) (hτ : τ < 1) (hW : 0 < W) (hP : P = markup ε * ((1 - τ) * W / mpn α A N))
    (hls : W / P = mrs σ φ C N) : mrs σ φ C N = mpn α A N / (markup ε * (1 - τ)) := by
  have hm := mpn_pos hα1 hA hN
  have hM := markup_pos hε
  have h1 : (0 : ℝ) < 1 - τ := by linarith
  rw [← hls, hP]
  field_simp

/-- Galí (2015), p. 100: with no subsidy the markup wedge violates (3): `MRS = MPN/M < MPN`. -/
theorem flex_mrs_lt_mpn {ε α A W P C N σ φ : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hN : 0 < N) (hW : 0 < W) (hP : P = markup ε * ((1 - 0) * W / mpn α A N))
    (hls : W / P = mrs σ φ C N) : mrs σ φ C N < mpn α A N := by
  rw [flex_mrs hε hα1 hA hN (by norm_num) hW hP hls, sub_zero, mul_one]
  exact div_lt_self (mpn_pos hα1 hA hN) (one_lt_markup hε)

/-! ### Equilibrium employment under a wedge -/

/-- Galí (2015), pp. 100–101: equilibrium employment when `MRS = MPN/w` along the symmetric
allocation, `N(w) = ((1 − α) A^{1−σ}/w)^{1/(φ + α + σ(1 − α))}`. -/
noncomputable def flexEmployment (σ φ α A w : ℝ) : ℝ :=
  ((1 - α) * A ^ (1 - σ) / w) ^ (φ + α + σ * (1 - α))⁻¹

/-- Galí (2015), p. 100: `N(w) > 0`. -/
theorem flexEmployment_pos {σ φ α A w : ℝ} (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    0 < flexEmployment σ φ α A w :=
  Real.rpow_pos_of_pos (div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)) hw) _

/-- Galí (2015), pp. 100–101: along the symmetric allocation, `MRS = MPN/w` holds for `N > 0`
**iff** `N = N(w)` (existence and uniqueness of the distorted equilibrium level). -/
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

/-- Galí (2015), pp. 100–101: **existence and uniqueness** of the equilibrium employment level
under a wedge `w > 0`. -/
theorem existsUnique_flex {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    ∃! N, 0 < N ∧ mrs σ φ (A * N ^ (1 - α)) N = mpn α A N / w :=
  ⟨flexEmployment σ φ α A w, ⟨flexEmployment_pos hα1 hA hw,
    (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw (flexEmployment_pos hα1 hA hw)).2 rfl⟩,
    fun _ ⟨hN, h⟩ => (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw hN).1 h⟩

/-- Galí (2015), p. 101: with no wedge (`w = 1`) the equilibrium level is efficient. -/
theorem flexEmployment_one (σ φ α A : ℝ) :
    flexEmployment σ φ α A 1 = effEmployment σ φ α A := by
  rw [flexEmployment, effEmployment, div_one]

/-- Galí (2015), p. 100: a wedge `w > 1` (e.g. the markup `M`) gives employment **strictly
below** the efficient level, `N(w) < N*`. -/
theorem flexEmployment_lt_eff {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 1 < w) :
    flexEmployment σ φ α A w < effEmployment σ φ α A := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
  exact Real.rpow_lt_rpow (div_pos hc (by linarith)).le (div_lt_self hc hw) (inv_pos.2 hk)

/-- Galí (2015), §4.2.2, p. 101: a wedge `0 < w < 1` gives employment strictly **above** the
efficient level. -/
theorem eff_lt_flexEmployment {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw0 : 0 < w) (hw : w < 1) :
    effEmployment σ φ α A < flexEmployment σ φ α A w := by
  have hk := effExponent_pos hσ hφ hα0 hα1
  have hc : 0 < (1 - α) * A ^ (1 - σ) := mul_pos (by linarith) (Real.rpow_pos_of_pos hA _)
  exact Real.rpow_lt_rpow hc.le ((lt_div_iff₀ hw0).2 (by nlinarith)) (inv_pos.2 hk)

/-- Galí (2015), pp. 100–101: the equilibrium level is efficient **iff** there is no wedge. -/
theorem flexEmployment_eq_eff_iff {σ φ α A w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hw : 0 < w) :
    flexEmployment σ φ α A w = effEmployment σ φ α A ↔ w = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h, flexEmployment_one]⟩
  rcases lt_trichotomy w 1 with hlt | heq | hgt
  · exact absurd h (eff_lt_flexEmployment hσ hφ hα0 hα1 hA hw hlt).ne'
  · exact heq
  · exact absurd h (flexEmployment_lt_eff hσ hφ hα0 hα1 hA hgt).ne

/-- Galí (2015), p. 100: along the symmetric allocation the MRS `A^σ N^{σ(1−α)+φ}` is strictly
increasing in `N`. -/
theorem mrs_sym_strictMonoOn {σ φ α A : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα1 : α < 1)
    (hA : 0 < A) : StrictMonoOn (fun N => mrs σ φ (A * N ^ (1 - α)) N) (Set.Ioi 0) := by
  intro a ha b _ hab
  have ha : (0 : ℝ) < a := ha
  have hb : 0 < b := ha.trans hab
  simp only [mrs]
  have h1 : (A * a ^ (1 - α)) ^ σ < (A * b ^ (1 - α)) ^ σ :=
    Real.rpow_lt_rpow (mul_pos hA (Real.rpow_pos_of_pos ha _)).le
      (mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha.le hab (by linarith)) hA) hσ
  have h2 : a ^ φ ≤ b ^ φ := Real.rpow_le_rpow ha.le hab.le hφ
  have h3 : 0 < a ^ φ := Real.rpow_pos_of_pos ha _
  have h4 : 0 < (A * b ^ (1 - α)) ^ σ := Real.rpow_pos_of_pos (mul_pos hA
    (Real.rpow_pos_of_pos hb _)) _
  calc (A * a ^ (1 - α)) ^ σ * a ^ φ < (A * b ^ (1 - α)) ^ σ * a ^ φ :=
        mul_lt_mul_of_pos_right h1 h3
    _ ≤ (A * b ^ (1 - α)) ^ σ * b ^ φ := mul_le_mul_of_nonneg_left h2 h4.le

/-- Galí (2015), p. 100: the marginal product of labour is nonincreasing in `N`
(`α ≥ 0`). -/
theorem mpn_antitoneOn {α A : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) :
    AntitoneOn (mpn α A) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hab (by linarith))
    (mul_pos (by linarith) hA).le

/-- Galí (2015), p. 100, **the book's monotonicity argument**: if `f` (the MRS) is strictly
increasing, `g` (the MPN) nonincreasing and positive, `f a = g a` (efficiency) and
`f b = g b / w` with `w > 1` (markup), then `b < a`. -/
theorem lt_of_wedge {f g : ℝ → ℝ} {a b w : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf : StrictMonoOn f (Set.Ioi 0)) (hg : AntitoneOn g (Set.Ioi 0)) (hgb : 0 < g b)
    (hw : 1 < w) (hfa : f a = g a) (hfb : f b = g b / w) : b < a := by
  by_contra hab
  push Not at hab
  have h1 : f a ≤ f b := hf.monotoneOn ha hb hab
  have h2 : g b ≤ g a := hg ha hb hab
  have h3 : g b / w < g b := div_lt_self hgb hw
  linarith

/-- Galí (2015), p. 100: the markup distortion leads to inefficiently low employment **and
output**: `N(M) < N*` and `A N(M)^{1−α} < A N*^{1−α}`. -/
theorem markup_inefficiently_low {σ φ ε α A : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) :
    flexEmployment σ φ α A (markup ε) < effEmployment σ φ α A ∧
      A * flexEmployment σ φ α A (markup ε) ^ (1 - α)
        < A * effEmployment σ φ α A ^ (1 - α) := by
  have h := flexEmployment_lt_eff (σ := σ) (φ := φ) hσ hφ hα0 hα1 hA (one_lt_markup hε)
  refine ⟨h, mul_lt_mul_of_pos_left (Real.rpow_lt_rpow
    (flexEmployment_pos hα1 hA (markup_pos hε)).le h (by linarith)) hA⟩

/-- Galí (2015), p. 100: the welfare loss of any wedge `w ≠ 1` is **strict**. -/
theorem flex_welfare_lt {σ φ α A Z w : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z) (hw : 0 < w) (hw1 : w ≠ 1) :
    symWelfare σ φ α A Z (flexEmployment σ φ α A w)
      < symWelfare σ φ α A Z (effEmployment σ φ α A) :=
  symWelfare_lt hσ hφ hα0 hα1 hA hZ (flexEmployment_pos hα1 hA hw)
    fun h => hw1 ((flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA hw).1 h)

/-! ### The optimal subsidy -/

/-- Galí (2015), p. 101: `M (1 − τ) = 1` **iff** `τ = 1/ε`. -/
theorem wedge_eq_one_iff_subsidy {ε τ : ℝ} (hε : 1 < ε) :
    markup ε * (1 - τ) = 1 ↔ τ = 1 / ε := by
  have h1 : ε - 1 ≠ 0 := by linarith
  have h2 : ε ≠ 0 := by linarith
  rw [markup]
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]
    field_simp

/-- Galí (2015), p. 101: the subsidy `τ = 1/ε` delivers `M (1 − τ) = 1`. -/
theorem optimal_subsidy {ε : ℝ} (hε : 1 < ε) : markup ε * (1 - 1 / ε) = 1 :=
  (wedge_eq_one_iff_subsidy hε).2 rfl

/-- Galí (2015), p. 101: the flexible-price equilibrium under subsidy `τ < 1` is efficient
**iff** `τ = 1/ε`: the optimal subsidy exists and is unique. -/
theorem flex_efficient_iff_subsidy {σ φ ε α A τ : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hτ : τ < 1) :
    flexEmployment σ φ α A (markup ε * (1 - τ)) = effEmployment σ φ α A ↔ τ = 1 / ε := by
  rw [flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA (mul_pos (markup_pos hε) (by linarith)),
    wedge_eq_one_iff_subsidy hε]

/-- Galí (2015), p. 101: the flexible-price equilibrium with subsidy `τ`, i.e. the profit
maximisation of `flex_price_rule` and the household's `W/P = MRS` along the symmetric
allocation, has employment `N(M (1 − τ))`; it is efficient (`N = N*`) **iff** `τ = 1/ε`. -/
theorem flex_equilibrium {σ φ ε α A W τ P N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hτ : τ < 1) (hW : 0 < W) (hP : 0 < P)
    (hN : 0 < N)
    (hfirm : ∀ N', 0 < N' → firmProfit ε α A W τ P (A * N ^ (1 - α)) N'
        ≤ firmProfit ε α A W τ P (A * N ^ (1 - α)) N)
    (hls : W / P = mrs σ φ (A * N ^ (1 - α)) N) :
    N = flexEmployment σ φ α A (markup ε * (1 - τ)) ∧
      (N = effEmployment σ φ α A ↔ τ = 1 / ε) := by
  have hrule := (flex_price_rule hε hα0 hα1 hA hP hN).1 hfirm
  have h := flex_mrs hε hα1 hA hN hτ hW hrule hls
  have hN' := (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA
    (mul_pos (markup_pos hε) (by linarith)) hN).1 h
  refine ⟨hN', ?_⟩
  rw [hN']
  exact flex_efficient_iff_subsidy hσ hφ hε hα0 hα1 hA hτ

/-! ### Sticky prices: the average markup -/

/-- Galí (2015), p. 101: the economy's average markup
`M_t = P_t / ((1 − τ)(W_t/MPN_t))`. -/
noncomputable def avgMarkup (τ P W mpnv : ℝ) : ℝ := P / ((1 - τ) * (W / mpnv))

/-- Galí (2015), p. 101: with the optimal subsidy `τ = 1/ε`, `M_t = P M/(W/MPN)`. -/
theorem avgMarkup_subsidy {ε P W m : ℝ} (hε : 1 < ε) (hW : 0 < W) (hm : 0 < m) :
    avgMarkup (1 / ε) P W m = P * markup ε / (W / m) := by
  have h1 : (1 : ℝ) - 1 / ε ≠ 0 := by
    have : 1 / ε < 1 := (div_lt_one (by linarith)).2 hε
    linarith
  have hε0 : ε ≠ 0 := by linarith
  have hε1 : ε - 1 ≠ 0 := by linarith
  rw [avgMarkup, markup]
  field_simp

/-- Galí (2015), p. 101: with the optimal subsidy and `W/P = MRS`,
`MRS = MPN · M/M_t`. -/
theorem mrs_eq_avgMarkup {ε P W m σ φ C N : ℝ} (hε : 1 < ε) (hP : 0 < P) (hW : 0 < W)
    (hm : 0 < m) (hls : W / P = mrs σ φ C N) :
    mrs σ φ C N = m * markup ε / avgMarkup (1 / ε) P W m := by
  have hM := markup_pos hε
  rw [avgMarkup_subsidy hε hW hm, ← hls]
  field_simp

/-- Galí (2015), p. 101: under the optimal subsidy, the efficiency condition (3) `MRS = MPN`
holds **iff** the average markup equals the frictionless markup, `M_t = M`. -/
theorem foc_iff_avgMarkup {ε P W m σ φ C N : ℝ} (hε : 1 < ε) (hP : 0 < P) (hW : 0 < W)
    (hm : 0 < m) (hls : W / P = mrs σ φ C N) :
    mrs σ φ C N = m ↔ avgMarkup (1 / ε) P W m = markup ε := by
  have hM := markup_pos hε
  have hMt : 0 < avgMarkup (1 / ε) P W m := by
    rw [avgMarkup_subsidy hε hW hm]
    exact div_pos (mul_pos hP hM) (div_pos hW hm)
  rw [mrs_eq_avgMarkup hε hP hW hm hls, div_eq_iff hMt.ne']
  constructor
  · intro h
    exact (mul_left_cancel₀ hm.ne' h).symm
  · intro h
    rw [h]

/-- Galí (2015), p. 101: under the optimal subsidy, along the symmetric allocation, employment
is `N(M_t/M)`; it is strictly below `N*` iff `M_t > M`, equal iff `M_t = M`, and strictly above
iff `M_t < M`. -/
theorem employment_avgMarkup {σ φ ε α A P W N : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hε : 1 < ε)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hP : 0 < P) (hW : 0 < W) (hN : 0 < N)
    (hls : W / P = mrs σ φ (A * N ^ (1 - α)) N) :
    N = flexEmployment σ φ α A (avgMarkup (1 / ε) P W (mpn α A N) / markup ε) ∧
      (N < effEmployment σ φ α A ↔ markup ε < avgMarkup (1 / ε) P W (mpn α A N)) ∧
      (N = effEmployment σ φ α A ↔ avgMarkup (1 / ε) P W (mpn α A N) = markup ε) ∧
      (effEmployment σ φ α A < N ↔ avgMarkup (1 / ε) P W (mpn α A N) < markup ε) := by
  have hm := mpn_pos hα1 hA hN
  have hM := markup_pos hε
  set Mt := avgMarkup (1 / ε) P W (mpn α A N) with hMtdef
  have hMt : 0 < Mt := by
    rw [hMtdef, avgMarkup_subsidy hε hW hm]
    exact div_pos (mul_pos hP hM) (div_pos hW hm)
  have hw : 0 < Mt / markup ε := div_pos hMt hM
  have h := mrs_eq_avgMarkup hε hP hW hm hls
  rw [← hMtdef] at h
  have h' : mrs σ φ (A * N ^ (1 - α)) N = mpn α A N / (Mt / markup ε) := by
    rw [h]
    field_simp
  have hN' := (mrs_eq_mpn_div_iff hσ hφ hα0 hα1 hA hw hN).1 h'
  have e1 : Mt / markup ε = 1 ↔ Mt = markup ε := div_eq_one_iff_eq hM.ne'
  have e2 : 1 < Mt / markup ε ↔ markup ε < Mt := one_lt_div hM
  have e3 : Mt / markup ε < 1 ↔ Mt < markup ε := div_lt_one hM
  refine ⟨hN', ?_, ?_, ?_⟩
  · rw [← e2, hN']
    constructor
    · intro hlt
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hl | he
      · exact absurd hlt (eff_lt_flexEmployment hσ hφ hα0 hα1 hA hw hl).not_gt
      · rw [he, flexEmployment_one] at hlt
        exact lt_irrefl _ hlt
    · exact flexEmployment_lt_eff hσ hφ hα0 hα1 hA
  · rw [← e1, hN', flexEmployment_eq_eff_iff hσ hφ hα0 hα1 hA hw]
  · rw [← e3, hN']
    constructor
    · intro hlt
      by_contra hle
      push Not at hle
      rcases hle.lt_or_eq with hl | he
      · exact absurd hlt (flexEmployment_lt_eff hσ hφ hα0 hα1 hA hl).not_gt
      · rw [← he, flexEmployment_one] at hlt
        exact lt_irrefl _ hlt
    · exact eff_lt_flexEmployment hσ hφ hα0 hα1 hA hw

/-! ### Sticky prices: relative-price distortions -/

namespace Dispersion

open Gali.MonetaryPolicyDesign.Efficient.Goods

variable {G : Type*} [MeasurableSpace G] {μ : Measure G}

/-- Galí (2015), p. 102: labour employed by firm `i` when it charges `P(i)`: demand
`C(i) = (P(i)/P)^{−ε} C` produced with `C(i) = A N(i)^{1−α}`, so
`N(i) = ((P(i)/P)^{−ε} C/A)^{1/(1−α)}`. -/
noncomputable def labourDemand (ε α A Pbar C : ℝ) (P : G → ℝ) (i : G) : ℝ :=
  ((P i / Pbar) ^ (-ε) * C / A) ^ (1 - α)⁻¹

omit [MeasurableSpace G] in
/-- Galí (2015), p. 102: firm `i`'s output is its demand, `A N(i)^{1−α} = (P(i)/P)^{−ε} C`. -/
theorem goodsOutput_labourDemand {ε α A Pbar C : ℝ} (hα1 : α < 1) (hA : 0 < A)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i) (i : G) :
    goodsOutput A α (labourDemand ε α A Pbar C P) i = (P i / Pbar) ^ (-ε) * C := by
  have hx : 0 ≤ (P i / Pbar) ^ (-ε) * C / A :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg (div_pos (hP i) hPbar).le _) hC.le) hA.le
  rw [goodsOutput, labourDemand, Real.rpow_inv_rpow hx (by linarith)]
  field_simp

omit [MeasurableSpace G] in
/-- Galí (2015), p. 102: different prices mean different quantities: if two firms produce the
same output then they charge the same price. -/
theorem price_eq_of_output_eq {ε α A Pbar C : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i) {i j : G}
    (h : goodsOutput A α (labourDemand ε α A Pbar C P) i
      = goodsOutput A α (labourDemand ε α A Pbar C P) j) : P i = P j := by
  rw [goodsOutput_labourDemand hα1 hA hPbar hC hP, goodsOutput_labourDemand hα1 hA hPbar hC hP]
    at h
  have h1 : (P i / Pbar) ^ (-ε) = (P j / Pbar) ^ (-ε) := mul_right_cancel₀ hC.ne' h
  have hne : -ε ≠ 0 := by linarith
  have h2 : P i / Pbar = P j / Pbar := by
    rw [← Real.rpow_rpow_inv (div_pos (hP i) hPbar).le hne,
      ← Real.rpow_rpow_inv (div_pos (hP j) hPbar).le hne, h1]
  field_simp at h2
  exact h2

omit [MeasurableSpace G] in
/-- Galí (2015), p. 102: different prices mean different employment: if two firms employ the
same labour then they charge the same price. -/
theorem price_eq_of_labour_eq {ε α A Pbar C : ℝ} (hε : 1 < ε) (hα1 : α < 1) (hA : 0 < A)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i) {i j : G}
    (h : labourDemand ε α A Pbar C P i = labourDemand ε α A Pbar C P j) : P i = P j :=
  price_eq_of_output_eq hε hα1 hA hPbar hC hP (by rw [goodsOutput, goodsOutput, h])

/-- Galí (2015), p. 102: if relative prices are **not** all equal (no constant `c` with
`P(i) = c` a.e.) then the induced allocation violates both efficiency conditions (1) and (2):
neither `C(i)` nor `N(i)` is a.e. constant. -/
theorem dispersion_violates_symmetry [IsProbabilityMeasure μ] {ε α A Pbar C : ℝ} (hε : 1 < ε)
    (hα1 : α < 1) (hA : 0 < A) (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ}
    (hP : ∀ i, 0 < P i) (hdisp : ¬ ∃ c, ∀ᵐ i ∂μ, P i = c) :
    (¬ ∃ c, ∀ᵐ i ∂μ, goodsOutput A α (labourDemand ε α A Pbar C P) i = c) ∧
      ¬ ∃ c, ∀ᵐ i ∂μ, labourDemand ε α A Pbar C P i = c := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨i₀, hi₀⟩ := hc.exists
    refine hdisp ⟨P i₀, ?_⟩
    filter_upwards [hc] with i hi
    exact price_eq_of_output_eq hε hα1 hA hPbar hC hP (hi.trans hi₀.symm)
  · rintro ⟨c, hc⟩
    obtain ⟨i₀, hi₀⟩ := hc.exists
    refine hdisp ⟨P i₀, ?_⟩
    filter_upwards [hc] with i hi
    exact price_eq_of_labour_eq hε hα1 hA hPbar hC hP (hi.trans hi₀.symm)

/-- Galí (2015), p. 102, **strict welfare loss from price dispersion**: if relative prices are
not all equal, the induced (feasible) allocation is strictly worse than the symmetric allocation
with the same total employment, and strictly worse than the efficient allocation. -/
theorem dispersion_welfare_loss [IsProbabilityMeasure μ] {σ φ ε α A Z Pbar C : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i)
    (hfeas : Feasible μ (labourDemand ε α A Pbar C P)) (hdisp : ¬ ∃ c, ∀ᵐ i ∂μ, P i = c) :
    welfare μ σ φ ε A α Z (labourDemand ε α A Pbar C P)
        < symWelfare σ φ α A Z (∫ i, labourDemand ε α A Pbar C P i ∂μ) ∧
      welfare μ σ φ ε A α Z (labourDemand ε α A Pbar C P)
        < symWelfare σ φ α A Z (effEmployment σ φ α A) := by
  have hns : ¬ ∀ᵐ i ∂μ, labourDemand ε α A Pbar C P i = ∫ j, labourDemand ε α A Pbar C P j ∂μ :=
    fun h => (dispersion_violates_symmetry hε hα1 hA hPbar hC hP hdisp).2 ⟨_, h⟩
  exact ⟨welfare_lt_symWelfare hε hα0 hα1 hA hZ hfeas hns,
    welfare_lt_of_not_symmetric hσ hφ hε hα0 hα1 hA hZ hfeas hns⟩

/-- Galí (2015), p. 102: attaining the efficient allocation **requires** equal prices: if the
allocation induced by prices `P(·)` is optimal, then `P(i)` is a.e. constant. -/
theorem prices_equal_of_optimal [IsProbabilityMeasure μ] {σ φ ε α A Z Pbar C : ℝ} (hσ : 0 < σ)
    (hφ : 0 ≤ φ) (hε : 1 < ε) (hα0 : 0 ≤ α) (hα1 : α < 1) (hA : 0 < A) (hZ : 0 < Z)
    (hPbar : 0 < Pbar) (hC : 0 < C) {P : G → ℝ} (hP : ∀ i, 0 < P i)
    (hfeas : Feasible μ (labourDemand ε α A Pbar C P))
    (hopt : ∀ n', Feasible μ n' → welfare μ σ φ ε A α Z n'
      ≤ welfare μ σ φ ε A α Z (labourDemand ε α A Pbar C P)) :
    ∃ c, ∀ᵐ i ∂μ, P i = c := by
  by_contra hdisp
  have h1 := (dispersion_welfare_loss hσ hφ hε hα0 hα1 hA hZ hPbar hC hP hfeas hdisp).2
  have h2 := hopt _ (feasible_const (μ := μ) (effEmployment_pos (σ := σ) (φ := φ) hα1 hA))
  rw [welfare_const hε hα0 hα1 hA (effEmployment_pos hα1 hA)] at h2
  linarith

end Dispersion

end Gali.MonetaryPolicyDesign.Distortions
