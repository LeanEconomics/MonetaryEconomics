/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.GlobalDynamics
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Monetary frictions with the Lucas–Stokey timing convention

Woodford (2003), *Interest and Prices*, Appendix A, §A.16, pp. 649–653.

* **(A.37)–(A.39).** `budget_A39`: with the end-of-period wealth (A.38), the pricing relations
  (1.4)–(1.5) and the portfolio constraint (A.37), the flow budget constraint
  `E_t[Q W_{t+1}] ≤ W_t − T_t − Δ_tM_t + (1 − Δ_t)(P_tY_t − P_tC_t)` holds, for any linear
  conditional-expectation functional (genuine uncertainty). `one_sub_oppCost` is the identity
  `E[Q(1 + i^m)] = 1 − Δ`.
* **(A.40).** `ibc_A40`: under perfect foresight, (A.39) at every date and the natural
  borrowing limit give the intertemporal budget constraint (A.40) (an infinite sum, proved
  summable).
* **(A.41).** `foc_A41`: at an optimum along the budget line the first-order condition
  `u_m/u_c = Δ/(1 − Δ)` holds.
* **(A.42)–(A.46).** `lambda_A44` (`u_c/(1 − Δ) = u_c + u_m`), `euler_A42_iff_A43`,
  `fisher_A46_iff_A43`, and `oddsRatio_strictMonoOn` (the LM equation (A.45) is well defined:
  `Δ/(1 − Δ)` is strictly increasing; with `i^m = 0` it equals `i`, `oddsRatio_oppCost_zero`).
* **(A.47).** `hasDerivAt_log_lambda`: `χ = m̄(u_cm + u_mm)/(u_c + u_m)` is the elasticity of
  `λ = u_c + u_m` with respect to `m`; `chiLS_neg_iff_of_separable`: under separability
  (`u_cm = 0`) `χ < 0` iff `u_mm < 0` (strict concavity is needed); under the Brock timing
  `χ = m̄u_cm/u_c = 0` (`chiBrock_separable`).
* **(A.48)–(A.49).** `A48_optimal_c2`, `A48_lambda_credit` and `A48_lambda_cash`:
  `λ = u_c + u_m = v_C` whatever `m`.
* **Cash/credit goods.** `cashcredit_binding_optimal` (with `v'(m) ≥ w'(C − m)` the cash
  constraint binds), `cashcredit_lambda` (`λ = v_c(m)`), `cashcredit_chi_neg` (strict
  concavity of `v` gives `χ < 0`); for the indirect utility `uCC` itself:
  `cashcredit_indirect_eq` (equals `v(m) + w(C − m)` wherever the constraint binds),
  `cashcredit_indirect_nhds` (on a neighbourhood of any strictly binding point) and
  `cashcredit_indirect_lambda` (`λ = u_c + u_m = v_c(m)` as genuine partial derivatives).
-/

namespace Woodford.PriceLevelDetermination.Timing

open Filter Topology
open Woodford.PriceLevelDetermination.GlobalDynamics

/-! ## (A.39): the flow budget constraint -/

/-- Woodford (2003), (A.39)–(A.40), p. 649: `1 − Δ = (1 + i^m)/(1 + i)`, i.e.
`E_t[Q_{t,t+1}(1 + i^m_t)] = 1 − Δ_t` given `E_tQ_{t,t+1} = 1/(1 + i_t)`. -/
theorem one_sub_oppCost {i im : ℝ} (hi : 1 + i ≠ 0) : 1 - oppCost i im = (1 + im) / (1 + i) := by
  unfold oppCost
  field_simp
  ring

/-- Woodford (2003), (A.37)–(A.39), p. 649: let `E` be the date-`t` conditional expectation (any
linear functional on state-contingent payoffs). If next-period wealth is (A.38)
`W' = A' + (1 + i^m)(M + PY − PC)`, assets are priced by (1.4) `E[QA'] = B` and (1.5)
`E[Q] = 1/(1 + i)`, then `E[QW'] = B + (1 + i^m)(M + PY − PC)/(1 + i)`, and under the portfolio
constraint (A.37) `M + B ≤ W − T` this gives (A.39):
`E[QW'] ≤ W − T − ΔM + (1 − Δ)(PY − PC)`. -/
theorem budget_A39 {Ω : Type*} (E : (Ω → ℝ) →ₗ[ℝ] ℝ) {Q A' W' : Ω → ℝ}
    {M B W T P Y C i im : ℝ} (hi : 1 + i ≠ 0)
    (hW' : W' = A' + fun _ => (1 + im) * (M + P * Y - P * C)) (h14 : E (Q * A') = B)
    (h15 : E Q = 1 / (1 + i)) (h37 : M + B ≤ W - T) :
    E (Q * W') = B + (1 + im) * (M + P * Y - P * C) / (1 + i) ∧
      E (Q * W') ≤ W - T - oppCost i im * M + (1 - oppCost i im) * (P * Y - P * C) := by
  have hsplit : Q * W' = Q * A' + ((1 + im) * (M + P * Y - P * C)) • Q := by
    rw [hW']
    funext ω
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq : E (Q * W') = B + (1 + im) * (M + P * Y - P * C) / (1 + i) := by
    rw [hsplit, map_add, map_smul, h14, h15, smul_eq_mul]
    ring
  refine ⟨heq, ?_⟩
  rw [heq, one_sub_oppCost hi]
  unfold oppCost
  have : (1 + im) * (M + P * Y - P * C) / (1 + i) =
      -((i - im) / (1 + i) * M) + M + (1 + im) / (1 + i) * (P * Y - P * C) := by
    field_simp
    ring
  rw [this]
  linarith

/-! ## (A.40): the intertemporal budget constraint (perfect foresight) -/

/-- Woodford (2003), (A.40), p. 650: the perfect-foresight discount factor
`Q_{0,k} = ∏_{j<k} Q_{j,j+1}`. -/
def discountFrom0 (q : ℕ → ℝ) (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, q j

/-- Woodford (2003), (A.39) ⇒ (A.40), pp. 649–650, under perfect foresight: if the flow budget
constraint (A.39) holds at every date, with one-period discount factors `q > 0`, and the
natural borrowing limit `Q_{0,k}W_k ≥ −∑_{j≥0} Q_{0,k+j}[(1 − Δ)PY − T]_{k+j}` holds (the
present-value income stream being summable), then spending `(1 − Δ)PC + ΔM ≥ 0` has a summable
present value and (A.40) holds:
`∑ Q_{0,s}[(1 − Δ_s)P_sC_s + Δ_sM_s] ≤ W_0 + ∑ Q_{0,s}[(1 − Δ_s)P_sY_s − T_s]`. -/
theorem ibc_A40 {q W Tx Δ M P Y C : ℕ → ℝ} (hq : ∀ k, 0 < q k)
    (hflow : ∀ k, q k * W (k + 1) ≤
      W k - Tx k - Δ k * M k + (1 - Δ k) * (P k * Y k - P k * C k))
    (hΔ0 : ∀ k, 0 ≤ Δ k) (hΔ1 : ∀ k, Δ k ≤ 1) (hP : ∀ k, 0 ≤ P k) (hC : ∀ k, 0 ≤ C k)
    (hM : ∀ k, 0 ≤ M k)
    (hy : Summable fun k => discountFrom0 q k * ((1 - Δ k) * P k * Y k - Tx k))
    (hborrow : ∀ k, -(∑' j, discountFrom0 q (j + k) * ((1 - Δ (j + k)) * P (j + k) * Y (j + k) -
      Tx (j + k))) ≤ discountFrom0 q k * W k) :
    Summable (fun k => discountFrom0 q k * ((1 - Δ k) * P k * C k + Δ k * M k)) ∧
      ∑' k, discountFrom0 q k * ((1 - Δ k) * P k * C k + Δ k * M k) ≤
        W 0 + ∑' k, discountFrom0 q k * ((1 - Δ k) * P k * Y k - Tx k) := by
  set s : ℕ → ℝ := fun k => discountFrom0 q k * ((1 - Δ k) * P k * C k + Δ k * M k) with hs
  set y : ℕ → ℝ := fun k => discountFrom0 q k * ((1 - Δ k) * P k * Y k - Tx k) with hydef
  have hQpos : ∀ k, 0 < discountFrom0 q k := fun k =>
    Finset.prod_pos fun j _ => hq j
  have hs0 : ∀ k, 0 ≤ s k := fun k => by
    have := hΔ1 k; have := hΔ0 k; have := hP k; have := hC k; have := hM k
    have h1 : 0 ≤ 1 - Δ k := by linarith
    have := (hQpos k).le
    simp only [hs]
    positivity
  have htele : ∀ n, ∑ k ∈ Finset.range n, s k + discountFrom0 q n * W n ≤
      W 0 + ∑ k ∈ Finset.range n, y k := by
    intro n
    induction n with
    | zero => simp [discountFrom0]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hQs : discountFrom0 q (n + 1) = discountFrom0 q n * q n := Finset.prod_range_succ _ _
      have h1 : discountFrom0 q n * (q n * W (n + 1)) ≤ discountFrom0 q n *
          (W n - Tx n - Δ n * M n + (1 - Δ n) * (P n * Y n - P n * C n)) :=
        mul_le_mul_of_nonneg_left (hflow n) (hQpos n).le
      rw [hQs]
      simp only [hs, hydef] at ih ⊢
      nlinarith
  have hbound : ∀ n, ∑ k ∈ Finset.range n, s k ≤ W 0 + ∑' k, y k := by
    intro n
    have h1 := htele n
    have h2 := hborrow n
    have h3 := hy.sum_add_tsum_nat_add n
    simp only [hydef] at h3
    linarith
  have hsum : Summable s := summable_of_sum_range_le hs0 hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_range_le hbound⟩

/-! ## (A.41): the first-order condition for money balances -/

/-- Woodford (2003), (A.41), p. 650: let `u` be differentiable at `(C, m)` with partial
derivatives `u_c = L(1,0) > 0` and `u_m = L(0,1)`, and `Δ < 1`. Real spending
`(1 − Δ)C + Δm` is constant along `s ↦ (C − Δs/(1 − Δ), m + s)`; if `(C, m)` maximises `u` locally
along this budget line, then `u_m/u_c = Δ/(1 − Δ)`. -/
theorem foc_A41 {u : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} {C m Δ : ℝ} (hΔ : Δ < 1)
    (hu : HasFDerivAt u L (C, m)) (huc : 0 < L (1, 0))
    (hmax : IsLocalMax (fun s => u (C - Δ / (1 - Δ) * s, m + s)) 0) :
    (∀ s, (1 - Δ) * (C - Δ / (1 - Δ) * s) + Δ * (m + s) = (1 - Δ) * C + Δ * m) ∧
      L (0, 1) / L (1, 0) = Δ / (1 - Δ) := by
  have h1 : (1 - Δ) ≠ 0 := by linarith
  refine ⟨fun s => by field_simp; ring, ?_⟩
  have hline : HasDerivAt (fun s : ℝ => (C - Δ / (1 - Δ) * s, m + s)) (-(Δ / (1 - Δ)), 1) 0 := by
    have ha : HasDerivAt (fun s : ℝ => C - Δ / (1 - Δ) * s) (-(Δ / (1 - Δ))) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (Δ / (1 - Δ))).const_sub C
    have hb : HasDerivAt (fun s : ℝ => m + s) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add m
    exact ha.prodMk hb
  have hcomp : HasDerivAt (fun s => u (C - Δ / (1 - Δ) * s, m + s)) (L (-(Δ / (1 - Δ)), 1)) 0 := by
    have hu' : HasFDerivAt u L (C - Δ / (1 - Δ) * 0, m + 0) := by simpa using hu
    exact hu'.comp_hasDerivAt (0 : ℝ) hline
  have hzero := hmax.hasDerivAt_eq_zero hcomp
  have hlin : L (-(Δ / (1 - Δ)), 1) = -(Δ / (1 - Δ)) * L (1, 0) + L (0, 1) := by
    have : ((-(Δ / (1 - Δ)), 1) : ℝ × ℝ) =
        (-(Δ / (1 - Δ))) • ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  rw [hlin] at hzero
  rw [div_eq_iff huc.ne']
  linarith

/-! ## (A.42)–(A.46) -/

/-- Woodford (2003), (A.44), p. 650: under (A.41), `λ ≡ u_c/(1 − Δ)` equals `u_c + u_m`. -/
theorem lambda_A44 {uc um Δ : ℝ} (hΔ : Δ < 1) (h41 : um / uc = Δ / (1 - Δ)) (huc : uc ≠ 0) :
    uc / (1 - Δ) = uc + um := by
  have h1 : (1 - Δ) ≠ 0 := by linarith
  rw [div_eq_div_iff huc h1] at h41
  field_simp
  linarith

/-- Woodford (2003), (A.42) ⇔ (A.43), p. 650 (in (A.43) the printed `M_{t+1}` should read
`M_{t+1}/P_{t+1}`): with `λ_s = u_{c,s}/(1 − Δ_s)`, the Euler equation
`u_{c,t}/u_{c,t+1} = (β/Q)(P_t/P_{t+1})(1 − Δ_t)/(1 − Δ_{t+1})` is
`λ_t/λ_{t+1} = (β/Q)(P_t/P_{t+1})`. -/
theorem euler_A42_iff_A43 {uc uc1 Δ Δ1 X : ℝ} (hΔ : Δ < 1) (hΔ1 : Δ1 < 1) (huc : 0 < uc)
    (huc1 : 0 < uc1) :
    uc / uc1 = X * ((1 - Δ) / (1 - Δ1)) ↔ (uc / (1 - Δ)) / (uc1 / (1 - Δ1)) = X := by
  have h1 : (1 - Δ) ≠ 0 := by linarith
  have h2 : (1 - Δ1) ≠ 0 := by linarith
  have e : (uc / (1 - Δ)) / (uc1 / (1 - Δ1)) = (uc / uc1) / ((1 - Δ) / (1 - Δ1)) := by
    field_simp
  rw [e, div_eq_iff (div_ne_zero h1 h2)]

/-- Woodford (2003), (A.43) ⇔ (A.46), pp. 650–651, perfect foresight: with `Q = 1/(1 + i)`,
`λ_t/λ_{t+1} = (β/Q)(P_t/P_{t+1})` is the Fisher relation
`1 + i = β⁻¹[(λ_{t+1}/λ_t)(P_t/P_{t+1})]⁻¹`. -/
theorem fisher_A46_iff_A43 {β i lt lt1 Pt Pt1 : ℝ} (hβ : 0 < β) (hi : 0 < 1 + i)
    (hl : 0 < lt) (hl1 : 0 < lt1) (hP : 0 < Pt) (hP1 : 0 < Pt1) :
    lt / lt1 = β / (1 / (1 + i)) * (Pt / Pt1) ↔
      1 + i = β⁻¹ * ((lt1 / lt) * (Pt / Pt1))⁻¹ := by
  have e1 : β / (1 / (1 + i)) * (Pt / Pt1) = β * (1 + i) * Pt / Pt1 := by field_simp
  have e2 : β⁻¹ * ((lt1 / lt) * (Pt / Pt1))⁻¹ = lt * Pt1 / (β * lt1 * Pt) := by field_simp
  rw [e1, e2, div_eq_div_iff hl1.ne' hP1.ne', eq_div_iff (by positivity)]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), (A.45), p. 651: `Δ ↦ Δ/(1 − Δ)` is strictly increasing on `Δ < 1`, so (A.41)
can be solved for real balances exactly as (3.2) was, giving an LM function with the same
signs. -/
theorem oddsRatio_strictMonoOn : StrictMonoOn (fun Δ : ℝ => Δ / (1 - Δ)) (Set.Iio 1) := by
  intro a ha b hb hab
  have ha' : a < 1 := ha
  have hb' : b < 1 := hb
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Woodford (2003), (A.45), p. 651: with `i^m = 0`, `Δ/(1 − Δ) = i`. -/
theorem oddsRatio_oppCost_zero {i : ℝ} (hi : 0 < 1 + i) :
    oppCost i 0 / (1 - oppCost i 0) = i := by
  rw [one_sub_oppCost hi.ne']
  unfold oppCost
  field_simp
  ring

/-! ## (A.47): the coefficient `χ` -/

/-- Woodford (2003), (A.47), p. 651: `χ ≡ m̄(u_cm + u_mm)/(u_c + u_m)` under the Lucas–Stokey
timing. -/
noncomputable def chiLS (mbar uc um ucm umm : ℝ) : ℝ := mbar * (ucm + umm) / (uc + um)

/-- Woodford (2003), (3.10), p. 112: `χ ≡ m̄u_cm/u_c` under the Brock timing. -/
noncomputable def chiBrock (mbar uc ucm : ℝ) : ℝ := mbar * ucm / uc

/-- Woodford (2003), (A.47), p. 651: `χ` is the elasticity of the marginal utility of income
with respect to real balances: if `λ` has derivative `λ'` at `m̄` and `λ(m̄) > 0`, then
`x ↦ log λ(m̄eˣ)` has derivative `m̄λ'/λ(m̄)` at `0`. -/
theorem hasDerivAt_log_lambda {lam : ℝ → ℝ} {mbar l1 : ℝ}
    (hl : HasDerivAt lam l1 mbar) (hpos : 0 < lam mbar) :
    HasDerivAt (fun x => Real.log (lam (mbar * Real.exp x))) (mbar * l1 / lam mbar) 0 := by
  have hin : HasDerivAt (fun x => mbar * Real.exp x) mbar 0 := by
    simpa using (Real.hasDerivAt_exp 0).const_mul mbar
  have hl' : HasDerivAt lam l1 (mbar * Real.exp 0) := by simpa using hl
  have hcomp : HasDerivAt (fun x => lam (mbar * Real.exp x)) (l1 * mbar) 0 := hl'.comp 0 hin
  have hlog := hcomp.log (by simpa using hpos.ne')
  simp only [Real.exp_zero, mul_one] at hlog
  convert hlog using 1
  ring

/-- Woodford (2003), (A.47), p. 651: with `λ = u_c + u_m` (A.44), whose `m`-derivative is
`u_cm + u_mm`, the elasticity of `λ` with respect to `m` is `χ` of (A.47). -/
theorem chiLS_is_elasticity {uc um : ℝ → ℝ} {mbar ucm umm : ℝ}
    (huc : HasDerivAt uc ucm mbar) (hum : HasDerivAt um umm mbar) (hpos : 0 < uc mbar + um mbar) :
    HasDerivAt (fun x => Real.log (uc (mbar * Real.exp x) + um (mbar * Real.exp x)))
      (chiLS mbar (uc mbar) (um mbar) ucm umm) 0 :=
  hasDerivAt_log_lambda (lam := fun m => uc m + um m) (huc.add hum) hpos

/-- Woodford (2003), p. 651: under the Brock timing additive separability (`u_cm = 0`) gives
`χ = 0`. -/
theorem chiBrock_separable (mbar uc : ℝ) : chiBrock mbar uc 0 = 0 := by simp [chiBrock]

/-- Woodford (2003), p. 651, "in the case of the Lucas–Stokey timing, … additive separability
(`u_cm = 0`) implies that `χ < 0`": precisely, with `m̄ > 0` and `u_c + u_m > 0`, `χ < 0` iff
`u_mm < 0` (strict concavity in `m` is needed; `u_mm = 0` gives `χ = 0`). -/
theorem chiLS_neg_iff_of_separable {mbar uc um umm : ℝ} (hm : 0 < mbar) (hpos : 0 < uc + um) :
    chiLS mbar uc um 0 umm < 0 ↔ umm < 0 := by
  unfold chiLS
  rw [zero_add, div_neg_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, _⟩)
    · linarith
    · by_contra h
      push Not at h
      nlinarith
  · intro h
    right
    exact ⟨by nlinarith, hpos⟩

/-! ## (A.48)–(A.49): a payment-technology example with `λ = v_C` -/

/-- Woodford (2003), p. 652: the indirect utility `u(C, m) = v(C) − w(max(C − m, 0))` from (A.48)
with the optimal use (A.49) of the inconvenient payment technology. -/
noncomputable def uA48 (v w : ℝ → ℝ) (C m : ℝ) : ℝ := v C - w (max (C - m) 0)

/-- Woodford (2003), (A.48)–(A.49), p. 652, "the optimal choice of `c₂` is obviously given by
the right-hand side of (A.49)": with `w` nondecreasing on `[0, ∞)`, any feasible
`c₂ ≥ max(C − m, 0)` gives utility at most `u(C, m)`. -/
theorem A48_optimal_c2 {v w : ℝ → ℝ} (hw : MonotoneOn w (Set.Ici 0)) {C m c2 : ℝ}
    (hc2 : max (C - m) 0 ≤ c2) : v C - w c2 ≤ uA48 v w C m := by
  unfold uA48
  have h0 : (0 : ℝ) ≤ max (C - m) 0 := le_max_right _ _
  have := hw (Set.mem_Ici.mpr h0) (Set.mem_Ici.mpr (le_trans h0 hc2)) hc2
  linarith

/-- Woodford (2003), p. 652, "the function `λ(C, m; ξ)` is then equal to `v_C(C; ξ)`, regardless
of the value of `m`", region `C > m` (credit used): `u_c = v'(C) − w'(C − m)`, `u_m = w'(C − m)`,
so `λ = u_c + u_m = v'(C)`. -/
theorem A48_lambda_credit {v w : ℝ → ℝ} {C m v1 w1 : ℝ} (hCm : m < C)
    (hv : HasDerivAt v v1 C) (hw : HasDerivAt w w1 (C - m)) :
    HasDerivAt (fun C' => uA48 v w C' m) (v1 - w1) C ∧
      HasDerivAt (fun m' => uA48 v w C m') w1 m ∧ (v1 - w1) + w1 = v1 := by
  refine ⟨?_, ?_, by ring⟩
  · have hin : HasDerivAt (fun C' => C' - m) 1 C := by simpa using (hasDerivAt_id C).sub_const m
    have h := hv.sub ((hw.comp C hin))
    simp only [mul_one] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hCm] with C' hC'
    simp only [uA48]
    rw [max_eq_left (by linarith [Set.mem_Ioi.mp hC'])]
    rfl
  · have hin : HasDerivAt (fun m' => C - m') (-1) m := by
      simpa using (hasDerivAt_id m).const_sub C
    have h := (hasDerivAt_const m (v C)).sub (hw.comp m hin)
    simp only [zero_sub, mul_neg, mul_one, neg_neg] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hCm] with m' hm'
    simp only [uA48]
    rw [max_eq_left (by linarith [Set.mem_Iio.mp hm'])]
    rfl

/-- Woodford (2003), p. 652, region `C < m` (cash suffices): `u_c = v'(C)`, `u_m = 0`, so again
`λ = v'(C)`. -/
theorem A48_lambda_cash {v w : ℝ → ℝ} {C m v1 : ℝ} (hCm : C < m) (hv : HasDerivAt v v1 C) :
    HasDerivAt (fun C' => uA48 v w C' m) v1 C ∧ HasDerivAt (fun m' => uA48 v w C m') 0 m := by
  refine ⟨?_, ?_⟩
  · have h := hv.sub_const (w 0)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hCm] with C' hC'
    simp only [uA48]
    rw [max_eq_right (by linarith [Set.mem_Iio.mp hC'])]
  · refine (hasDerivAt_const m (v C - w 0)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hCm] with m' hm'
    simp only [uA48]
    rw [max_eq_right (by linarith [Set.mem_Ioi.mp hm'])]

/-! ## Cash and credit goods -/

/-- Woodford (2003), (A.50)–(A.52), p. 653, separable cash/credit preferences
`V = v(c₁) + w(c₂)`: if `v` and `w` are concave and differentiable and `v'(m) ≥ w'(C − m)`, then
`c₁ = m` (the cash-in-advance constraint (A.51) binds) maximises `v(c₁) + w(C − c₁)` over
`c₁ ≤ m`. -/
theorem cashcredit_binding_optimal {v w : ℝ → ℝ} {C m v1 w1 : ℝ}
    (hv : ConcaveOn ℝ Set.univ v) (hw : ConcaveOn ℝ Set.univ w) (hvd : HasDerivAt v v1 m)
    (hwd : HasDerivAt w w1 (C - m)) (hbind : w1 ≤ v1) {c1 : ℝ} (hc1 : c1 ≤ m) :
    v c1 + w (C - c1) ≤ v m + w (C - m) := by
  rcases hc1.lt_or_eq with hlt | heq
  · set f : ℝ → ℝ := fun x => v x + w (C - x) with hf
    have hfconc : ConcaveOn ℝ Set.univ f := by
      refine hv.add ?_
      have : ConcaveOn ℝ Set.univ (fun x => w (C - x)) := by
        refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
        have := hw.2 (Set.mem_univ (C - x)) (Set.mem_univ (C - y)) ha hb hab
        simp only [smul_eq_mul] at this ⊢
        have e : a * (C - x) + b * (C - y) = C - (a * x + b * y) := by
          rw [← sub_eq_zero]
          linear_combination C * hab
        rw [e] at this
        exact this
      exact this
    have hin : HasDerivAt (fun x => C - x) (-1) m := by simpa using (hasDerivAt_id m).const_sub C
    have hfd : HasDerivAt f (v1 - w1) m := by
      have h := hvd.add (hwd.comp m hin)
      simp only [mul_neg, mul_one] at h
      exact h
    have hslope := hfconc.deriv_le_slope (Set.mem_univ c1) (Set.mem_univ m) hlt
      hfd.differentiableAt
    rw [hfd.deriv, slope_def_field] at hslope
    have hpos : 0 < m - c1 := by linarith
    have h1 : 0 ≤ (f m - f c1) / (m - c1) := le_trans (by linarith) hslope
    have h2 : 0 ≤ f m - f c1 := by
      rwa [le_div_iff₀ hpos, zero_mul] at h1
    simp only [hf] at h2
    linarith
  · rw [heq]

/-- Woodford (2003), p. 653, "the marginal utility of additional financial income equals
`λ(C, m; ξ) = v_c(m; ξ)`": where the cash constraint binds, `u(C, m) = v(m) + w(C − m)`, so
`u_c = w'(C − m)`, `u_m = v'(m) − w'(C − m)` and `λ = u_c + u_m = v'(m)`. -/
theorem cashcredit_lambda {v w : ℝ → ℝ} {C m v1 w1 : ℝ} (hv : HasDerivAt v v1 m)
    (hw : HasDerivAt w w1 (C - m)) :
    HasDerivAt (fun C' => v m + w (C' - m)) w1 C ∧
      HasDerivAt (fun m' => v m' + w (C - m')) (v1 - w1) m ∧ w1 + (v1 - w1) = v1 := by
  refine ⟨?_, ?_, by ring⟩
  · have hin : HasDerivAt (fun C' => C' - m) 1 C := by simpa using (hasDerivAt_id C).sub_const m
    have h := (hasDerivAt_const C (v m)).add (hw.comp C hin)
    simp only [zero_add, mul_one] at h
    exact h
  · have hin : HasDerivAt (fun m' => C - m') (-1) m := by
      simpa using (hasDerivAt_id m).const_sub C
    have h := hv.add (hw.comp m hin)
    simp only [mul_neg, mul_one] at h
    exact h

/-- Woodford (2003), p. 653, "strict concavity of the function `v` then implies that `λ` is
decreasing in `m`, so that `χ < 0`": with `λ(m) = v'(m) > 0` and `v''(m) < 0`, the elasticity of
`λ` with respect to `m` (which is `χ`, by (A.47) and `cashcredit_lambda`) is negative. -/
theorem cashcredit_chi_neg {vp : ℝ → ℝ} {mbar v2 : ℝ} (hm : 0 < mbar) (hv2 : HasDerivAt vp v2 mbar)
    (hneg : v2 < 0) (hpos : 0 < vp mbar) :
    HasDerivAt (fun x => Real.log (vp (mbar * Real.exp x))) (mbar * v2 / vp mbar) 0 ∧
      mbar * v2 / vp mbar < 0 :=
  ⟨hasDerivAt_log_lambda hv2 hpos, div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hm hneg) hpos⟩

/-- Woodford (2003), (A.50)–(A.52), p. 653: the indirect utility of the separable cash/credit
model, `u(C, m) = sup {v(c₁) + w(C − c₁) : c₁ ≤ m}` (cash-in-advance constraint (A.51),
`c₂ = C − c₁` by (A.52)). -/
noncomputable def uCC (v w : ℝ → ℝ) (C m : ℝ) : ℝ :=
  sSup ((fun c1 => v c1 + w (C - c1)) '' Set.Iic m)

/-- Woodford (2003), p. 653: at every point where the cash constraint binds,
`w'(C − m) ≤ v'(m)` (with `v`, `w` concave and differentiable), the supremum defining the indirect
utility is attained at `c₁ = m`: `u(C, m) = v(m) + w(C − m)`. -/
theorem cashcredit_indirect_eq {v w vp wp : ℝ → ℝ} (hv : ConcaveOn ℝ Set.univ v)
    (hw : ConcaveOn ℝ Set.univ w) (hvd : ∀ x, HasDerivAt v (vp x) x)
    (hwd : ∀ x, HasDerivAt w (wp x) x) {C m : ℝ} (hbind : wp (C - m) ≤ vp m) :
    uCC v w C m = v m + w (C - m) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨m, Set.mem_Iic.mpr le_rfl, rfl⟩, ?_⟩
  rintro _ ⟨c1, hc1, rfl⟩
  exact cashcredit_binding_optimal hv hw (hvd m) (hwd (C - m)) hbind hc1

/-- Woodford (2003), p. 653: if `v'`, `w'` are continuous and the constraint binds strictly at
`(C, m)` (`w'(C − m) < v'(m)`), then `u = v(m) + w(C − m)` on a whole neighbourhood of `(C, m)`. -/
theorem cashcredit_indirect_nhds {v w vp wp : ℝ → ℝ} (hv : ConcaveOn ℝ Set.univ v)
    (hw : ConcaveOn ℝ Set.univ w) (hvd : ∀ x, HasDerivAt v (vp x) x)
    (hwd : ∀ x, HasDerivAt w (wp x) x) (hvc : Continuous vp) (hwc : Continuous wp) {C m : ℝ}
    (hstrict : wp (C - m) < vp m) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (C, m), uCC v w p.1 p.2 = v p.2 + w (p.1 - p.2) := by
  have hf : Continuous (fun p : ℝ × ℝ => wp (p.1 - p.2)) :=
    hwc.comp (continuous_fst.sub continuous_snd)
  have hg : Continuous (fun p : ℝ × ℝ => vp p.2) := hvc.comp continuous_snd
  filter_upwards [hf.continuousAt.eventually_lt hg.continuousAt hstrict] with p hp
  exact cashcredit_indirect_eq hv hw hvd hwd hp.le

/-- Woodford (2003), p. 653, "the marginal utility of additional financial income equals
`λ(C, m; ξ) = v_c(m; ξ)`", as a statement about the indirect utility itself: where the cash
constraint binds strictly, `∂u/∂C = w'(C − m)`, `∂u/∂m = v'(m) − w'(C − m)`, and
`λ = u_c + u_m = v'(m)`. -/
theorem cashcredit_indirect_lambda {v w vp wp : ℝ → ℝ} (hv : ConcaveOn ℝ Set.univ v)
    (hw : ConcaveOn ℝ Set.univ w) (hvd : ∀ x, HasDerivAt v (vp x) x)
    (hwd : ∀ x, HasDerivAt w (wp x) x) (hvc : Continuous vp) (hwc : Continuous wp) {C m : ℝ}
    (hstrict : wp (C - m) < vp m) :
    HasDerivAt (fun C' => uCC v w C' m) (wp (C - m)) C ∧
      HasDerivAt (fun m' => uCC v w C m') (vp m - wp (C - m)) m ∧
      wp (C - m) + (vp m - wp (C - m)) = vp m := by
  have hev := cashcredit_indirect_nhds hv hw hvd hwd hvc hwc hstrict
  have hl := cashcredit_lambda (C := C) (hvd m) (hwd (C - m))
  have hC : ∀ᶠ C' in 𝓝 C, uCC v w C' m = v m + w (C' - m) :=
    ((continuous_id.prodMk continuous_const : Continuous fun C' : ℝ => (C', m)).tendsto
      C).eventually hev
  have hm : ∀ᶠ m' in 𝓝 m, uCC v w C m' = v m' + w (C - m') :=
    ((continuous_const.prodMk continuous_id : Continuous fun m' : ℝ => (C, m')).tendsto
      m).eventually hev
  exact ⟨hl.1.congr_of_eventuallyEq hC, hl.2.1.congr_of_eventuallyEq hm, hl.2.2⟩

end Woodford.PriceLevelDetermination.Timing
