/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.SurplusMA

/-!
# The generalised Hansen–Roberds–Sargent identities

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2.7, eqs. (4.11)–(4.13),
pp. 97–98, and Online Appendix A2, §2.3, p. 606.

Every series has a vector moving-average representation in a common vector
martingale-difference shock `ε` (`π_t = a_π(L)'ε_t`, `s̃_t = a_s(L)'ε_t`, ...), and the
linearised identities of §3.5 hold. Here `a_r` is the moving average of the ex-post real return
INCLUDING its `j = 0` term, as in (4.12), (4.13) and A2 §2.3.

## Main results

* Survey E4 (p. 98): the line before (4.11), `Δπ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}`,
  is false: its right-hand side is identically zero (`printed_rhs_eq_zero`), so it holds iff
  there is no unexpected inflation (`printed_line_iff`), and it fails in a genuine model
  (`printed_line_counterexample`). The correct statement is `innov_pi_vector`:
  `Δπ_{t+1} − Δrⁿ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(0)]'ε_{t+1}`.
* (4.11) is an identity, not a repayment condition: `identity_4_11` (shock form, every model)
  and `identity_4_11_vec` (coefficient form, non-degenerate shocks); `identity_A2` (A2 §2.3,
  `0 = a_s(ρ) − a_r(ρ)`). The repayment condition (no unexpected inflation with one-period
  debt) is `a_s(ρ) + a_g(ρ) = a_r(ρ) − a_r(0)`: `repayment_iff`, `repayment_iff_vec`; with
  constant expected returns and no growth it is `a_s(ρ) = 0`: `const_expected_return_coeffs`,
  `repayment_reduces`.
* (4.12): `identity_4_12`.
* Campbell–Shiller: `CSReturn`, `campbellShiller_finite`, `campbellShiller`,
  `campbellShiller_expected`; Campbell–Ammer (survey E5 corrected): `campbellAmmer`,
  `campbellAmmer_MA`; the printed display fails: `printed_campbellAmmer_counterexample`;
  (4.13): `identity_4_13`, `identity_4_13_vec`.
* A2 §2.3: the constant-discount-rate present value relation is not an identity
  (`pv_constant_discount_iff`: it holds iff the discounted expected returns sum to zero);
  with constant expected returns `a_r(ρ) = a_r(0)` (`const_discount_gen`).
-/

namespace Cochrane.DebtDeficitsInflation.GeneralizedHRS

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Algebra of `c'ε` -/

/-- Cochrane (2023), §4.2.7, p. 98: `(c + d)'ε = c'ε + d'ε`. -/
theorem dotShock_add {n : ℕ} (c d : Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) :
    dotShock (c + d) ε k = dotShock c ε k + dotShock d ε k := by
  funext ω
  simp [dotShock, add_mul, Finset.sum_add_distrib]

/-- Cochrane (2023), §4.2.7, p. 98: `(c − d)'ε = c'ε − d'ε`. -/
theorem dotShock_sub {n : ℕ} (c d : Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) :
    dotShock (c - d) ε k = dotShock c ε k - dotShock d ε k := by
  funext ω
  simp [dotShock, sub_mul, Finset.sum_sub_distrib]

/-- Cochrane (2023), §4.2.7, p. 98: `(−c)'ε = −c'ε`. -/
theorem dotShock_neg {n : ℕ} (c : Fin n → ℝ) (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) :
    dotShock (-c) ε k = -dotShock c ε k := by
  funext ω
  simp [dotShock, Finset.sum_neg_distrib]

/-- Cochrane (2023), §4.2.7, p. 98: the shocks at date `k` are non-degenerate: no non-zero
combination `c'ε_k` vanishes identically (so coefficient vectors are identified). -/
def Nondeg {n : ℕ} (ε : ℤ → Fin n → Ω → ℝ) (k : ℤ) : Prop :=
  ∀ c : Fin n → ℝ, dotShock c ε k = 0 → c = 0

/-- Cochrane (2023), §4.2.7, p. 98: for `|ρ| ≤ 1`, the innovation sum of a vector moving
average converges, `∑_j ρʲ Δ_{t+1} x_{t+1+j} = a_x(ρ)'ε_{t+1}`. -/
theorem seriesTo_innov_MAVec {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hx : IsMAVec a ε x) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ j * innov 𝔼 t (x (t + 1 + j)) ω)
      (dotShock (genVec a ρ) ε ((t : ℤ) + 1) ω) :=
  seriesTo_of_hasSum (innov_PV_termwise_vec 𝔼 hx hε hM
    (fun i => summable_coeff_mul_pow (hx.1 i) hρ) t ω)

/-- Cochrane (2023), §4.2.7, p. 98 (sums from `j = 1`):
`∑_{j ≥ 1} ρʲ Δ_{t+1} x_{t+1+j} = [a_x(ρ) − a_x(0)]'ε_{t+1}`. -/
theorem seriesTo_innov_MAVec_succ {n : ℕ} {a : ℕ → Fin n → ℝ} {ε : ℤ → Fin n → Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hx : IsMAVec a ε x) (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ρ : ℝ} (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (x (t + 2 + j)) ω)
      (dotShock (genVec a ρ - a 0) ε ((t : ℤ) + 1) ω) := by
  refine (seriesTo_succ_iff.1 (seriesTo_innov_MAVec 𝔼 hx hε hM hρ t ω)).congr
    (fun j => by rw [show t + 1 + (j + 1) = t + 2 + j by omega]) ?_
  rw [dotShock_sub, Pi.sub_apply, innov_MAVec 𝔼 hx hε hM t 0]
  simp

/-- Cochrane (2023), A2 §2.3, p. 606: the generating-function vector at `z = 0` is `a_0`. -/
theorem genVec_zero {n : ℕ} (a : ℕ → Fin n → ℝ) : genVec a 0 = a 0 := by
  funext i
  exact gen_zero _

/-! ### The corrected unexpected-inflation formula and (4.11) -/

/-- Cochrane (2023), §4.2.7, p. 98, corrected (survey E4): from (3.20),
`Δπ_{t+1} − Δrⁿ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(0)]'ε_{t+1}` (for `|ρ| ≤ 1`). -/
theorem innov_pi_vector {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hv : 𝔼.Adapted v)
    (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s)
    (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) - innov 𝔼 t (rn (t + 1)) =
      dotShock (-genVec as ρ - genVec ag ρ + genVec ar ρ - ar 0) ε ((t : ℤ) + 1) := by
  funext ω
  have h1 := unexpected_inflation_identity 𝔼 h hr (hv t) (hT t ω)
    (seriesTo_innov_MAVec 𝔼 hs hε hM hρ t ω) (seriesTo_innov_MAVec 𝔼 hg hε hM hρ t ω)
  have h2 := (seriesTo_innov_MAVec_succ 𝔼 har hε hM hρ t ω).unique h1
  simp only [dotShock_sub, dotShock_add, dotShock_neg, Pi.sub_apply, Pi.add_apply,
    Pi.neg_apply] at h2 ⊢
  linarith

/-- Cochrane (2023), §4.2.7, p. 98, and A2 §2.3, p. 606 ((4.11) in shock form): under the flow
identity and the terminal condition, `[a_s(ρ) + a_g(ρ) − a_r(ρ)]'ε_{t+1} = 0` identically. -/
theorem identity_4_11 {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s)
    (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ}
    (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ}
    (hs : IsMAVec as ε s) (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ) :
    dotShock (genVec as ρ + genVec ag ρ - genVec ar ρ) ε ((t : ℤ) + 1) = 0 := by
  funext ω
  have h0 := rec_seriesTo_map (innov 𝔼 t) ((flow_iff_recursion ρ v r g s).1 h) (hT t ω)
  rw [innov_of_known 𝔼 (hv t)] at h0
  have h1 := ((seriesTo_innov_MAVec 𝔼 hs hε hM hρ t ω).add
    (seriesTo_innov_MAVec 𝔼 hg hε hM hρ t ω)).sub (seriesTo_innov_MAVec 𝔼 har hε hM hρ t ω)
  have h2 := h0.unique (h1.congr (fun j => by
    simp only [map_sub, map_add, Pi.sub_apply, Pi.add_apply]; ring) rfl)
  simp only [dotShock_sub, dotShock_add, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at h2 ⊢
  linarith

/-- Cochrane (2023), eq. (4.11), p. 98, coefficient form: with non-degenerate shocks,
`a_s(ρ) + a_g(ρ) = a_r(ρ)` holds as an identity (in every model satisfying the flow identity and
the terminal condition, whatever the inflation process). -/
theorem identity_4_11_vec {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r g s : ℕ → Ω → ℝ} (h : Flow ρ v r g s)
    (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ}
    (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ}
    (hs : IsMAVec as ε s) (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ)
    (hnd : Nondeg ε ((t : ℤ) + 1)) : genVec as ρ + genVec ag ρ = genVec ar ρ := by
  have := hnd _ (identity_4_11 𝔼 hρ h hv hT hε hM hs hg har t)
  rw [sub_eq_zero] at this
  exact this

/-- Cochrane (2023), A2 §2.3, p. 606: "`0 = a_s(ρ) − a_r(ρ)` ... is an identity" (no growth). -/
theorem identity_A2 {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r s : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {as ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s) (har : IsMAVec ar ε r) (t : ℕ) :
    dotShock (genVec as ρ - genVec ar ρ) ε ((t : ℤ) + 1) = 0 := by
  have hg : IsMAVec (fun _ _ => (0 : ℝ)) ε (fun _ => 0) :=
    ⟨fun _ => by simp, fun t ω => by simp⟩
  have := identity_4_11 𝔼 hρ h hv hT hε hM hs hg har t
  have hz : genVec (n := n) (fun _ _ => (0 : ℝ)) ρ = 0 := by
    funext i; simp [genVec, gen]
  rwa [hz, add_zero] at this

/-- Cochrane (2023), §4.2.7, p. 98 (survey E4): the printed right-hand side
`[−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}` is identically zero. -/
theorem printed_rhs_eq_zero {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s) (hg : IsMAVec ag ε g)
    (har : IsMAVec ar ε r) (t : ℕ) :
    dotShock (-genVec as ρ - genVec ag ρ + genVec ar ρ) ε ((t : ℤ) + 1) = 0 := by
  have := identity_4_11 𝔼 hρ h hv hT hε hM hs hg har t
  rw [show -genVec as ρ - genVec ag ρ + genVec ar ρ =
    -(genVec as ρ + genVec ag ρ - genVec ar ρ) by abel, dotShock_neg, this, neg_zero]

/-- Cochrane (2023), §4.2.7, p. 98 (survey E4): the printed line
`Δπ_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_{t+1}` holds iff there is no unexpected inflation. -/
theorem printed_line_iff {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hv : 𝔼.Adapted v) (hT : InnovTVC 𝔼 ρ v) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s) (hg : IsMAVec ag ε g)
    (har : IsMAVec ar ε r) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) =
        dotShock (-genVec as ρ - genVec ag ρ + genVec ar ρ) ε ((t : ℤ) + 1) ↔
      innov 𝔼 t (infl (t + 1)) = 0 := by
  rw [printed_rhs_eq_zero 𝔼 hρ h hv hT hε hM hs hg har t]

/-- Cochrane (2023), §4.2.7, p. 98: with one-period debt (`rⁿ_{t+1}` known at `t`), no unexpected
inflation iff `[a_s(ρ) + a_g(ρ) − a_r(ρ) + a_r(0)]'ε_{t+1} = 0` (the correct "debt repayment"
condition, survey E4). -/
theorem repayment_iff {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hv : 𝔼.Adapted v)
    (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s)
    (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ)
    (hrn : 𝔼.E t (rn (t + 1)) = rn (t + 1)) :
    innov 𝔼 t (infl (t + 1)) = 0 ↔
      dotShock (genVec as ρ + genVec ag ρ - genVec ar ρ + ar 0) ε ((t : ℤ) + 1) = 0 := by
  have h1 := innov_pi_vector 𝔼 hρ h hr hv hT hε hM hs hg har t
  rw [innov_of_known 𝔼 hrn, sub_zero] at h1
  rw [h1, show genVec as ρ + genVec ag ρ - genVec ar ρ + ar 0 =
    -(-genVec as ρ - genVec ag ρ + genVec ar ρ - ar 0) by abel, dotShock_neg, neg_eq_zero]

/-- Cochrane (2023), eq. (4.11), p. 98, corrected (survey E4): with non-degenerate shocks and
one-period debt, there is no unexpected inflation iff `a_s(ρ) + a_g(ρ) = a_r(ρ) − a_r(0)`. -/
theorem repayment_iff_vec {ρ : ℝ} (hρ : |ρ| ≤ 1) {v r rn infl g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t) (hv : 𝔼.Adapted v)
    (hT : InnovTVC 𝔼 ρ v) {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s)
    (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (t : ℕ)
    (hrn : 𝔼.E t (rn (t + 1)) = rn (t + 1)) (hnd : Nondeg ε ((t : ℤ) + 1)) :
    innov 𝔼 t (infl (t + 1)) = 0 ↔ genVec as ρ + genVec ag ρ = genVec ar ρ - ar 0 := by
  rw [repayment_iff 𝔼 hρ h hr hv hT hε hM hs hg har t hrn]
  constructor
  · intro h0
    have := hnd _ h0
    rw [← sub_eq_zero, ← this]
    abel
  · intro h0
    rw [show genVec as ρ + genVec ag ρ - genVec ar ρ + ar 0 = 0 by rw [h0]; abel]
    funext ω
    simp [dotShock]

/-- Cochrane (2023), p. 98 ("the condition `a(ρ) = 0` is the special case ... of constant
expected returns"): with constant expected returns and non-degenerate shocks, the return has
no moving-average coefficients beyond `j = 0`. -/
theorem const_expected_return_coeffs {r : ℕ → Ω → ℝ} {c : ℝ} (hc : ConstExpReturn 𝔼 r c)
    {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {ar : ℕ → Fin n → ℝ} (har : IsMAVec ar ε r) (t : ℕ)
    (hnd : Nondeg ε ((t : ℤ) + 1)) (j : ℕ) : ar (j + 1) = 0 := by
  refine hnd _ ?_
  rw [← innov_MAVec 𝔼 har hε hM t (j + 1), show t + 1 + (j + 1) = t + 2 + j by omega]
  exact innov_future_return_zero 𝔼 hc t j

/-- Cochrane (2023), A2 §2.3, p. 606: with no return coefficients beyond `j = 0`,
`a_r(ρ) = a_r(0)`. -/
theorem const_discount_gen {n : ℕ} {ar : ℕ → Fin n → ℝ} (h : ∀ j, ar (j + 1) = 0) (ρ : ℝ) :
    genVec ar ρ = ar 0 := by
  funext i
  unfold genVec gen
  rw [tsum_eq_single 0 fun j hj => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [h k]]
  simp

/-- Cochrane (2023), p. 98: "The condition `a(ρ) = 0` is the special case of no growth ... and
of constant expected returns": then the repayment condition `a_s + a_g = a_r(ρ) − a_r(0)` is
`a_s(ρ) = 0`. -/
theorem repayment_reduces {n : ℕ} {as ar : ℕ → Fin n → ℝ} (h : ∀ j, ar (j + 1) = 0) (ρ : ℝ) :
    genVec as ρ + genVec (fun _ _ => (0 : ℝ)) ρ = genVec ar ρ - ar 0 ↔ genVec as ρ = 0 := by
  have hz : genVec (n := n) (fun _ _ => (0 : ℝ)) ρ = 0 := by
    funext i; simp [genVec, gen]
  rw [hz, const_discount_gen h, add_zero, sub_self]

/-! ### A genuine counterexample to the printed line -/

/-- Cochrane (2023), p. 98 (survey E4 counterexample): one coin-flip shock. -/
noncomputable def cxShock : ℤ → Fin 1 → Bool × Bool → ℝ := fun k _ => coinShockZ k

/-- Cochrane (2023), p. 98 (survey E4 counterexample): i.i.d. coefficients as a one-shock
vector. -/
def cxCoeff (j : ℕ) (_ : Fin 1) : ℝ := iidCoeff j

/-- Cochrane (2023), p. 98 (survey E4 counterexample): the i.i.d. surplus `s_t = ε_t`, which is
also the ex-post real return. -/
noncomputable def cxSurplus : ℕ → Bool × Bool → ℝ := fun t => coinShockZ t

/-- Cochrane (2023), p. 98 (survey E4 counterexample): `cxSurplus` is a one-shock vector moving
average with i.i.d. coefficients. -/
theorem cx_isMAVec : IsMAVec cxCoeff cxShock cxSurplus :=
  (isMA_iff_vec iidCoeff coinShockZ (fun t => coinShockZ t)).1 (isMA_iid coinShockZ)

/-- Cochrane (2023), p. 98 (survey E4/E5 counterexamples): the date-1 innovations of the
coin-flip surplus after heads, `Δ_1 s_k = 1` if `k = 1` and `0` otherwise. -/
theorem cx_innov_shock (k : ℕ) :
    innov ExpectationsFiniteTree.coinSystem 0 (cxSurplus k) (true, true) =
      if k = 1 then 1 else 0 := by
  have h := congrFun (innov_shock ExpectationsFiniteTree.coinSystem coinShockZ_isMDS 0 k)
    (true, true)
  simp only [cxSurplus]
  rw [h]
  by_cases hk : k = 1
  · subst hk
    simpa using coinShockZ_one
  · have : (k : ℤ) ≠ ((0 : ℕ) : ℤ) + 1 := by push_cast; omega
    simp [hk]

/-- Cochrane (2023), §4.2.7, p. 98 (survey E4): a genuine model in which the printed line
fails. Take the coin-flip shock, the i.i.d. surplus `s_t = ε_t`, zero value of debt and growth,
the ex-post real return `r_t = ε_t`, a zero nominal rate and inflation `π_t = −ε_t`. Then the
flow identity holds, `a_s(ρ) = a_r(ρ) = 1`, `a_g = 0`, so the printed right-hand side
`[−a_s(ρ) − a_g(ρ) + a_r(ρ)]'ε_1` is `0`, while `Δ_1π_1 = −1` after heads. -/
theorem printed_line_counterexample (ρ : ℝ) :
    Flow ρ (fun _ => 0) cxSurplus (fun _ => 0) cxSurplus ∧
      (∀ t, cxSurplus t = (fun _ => 0) t - (fun t => -cxSurplus t) t) ∧
      IsMAVec cxCoeff cxShock cxSurplus ∧
      innov ExpectationsFiniteTree.coinSystem 0 (-cxSurplus (0 + 1)) (true, true) = -1 ∧
      dotShock (-genVec cxCoeff ρ - genVec (fun _ _ => (0 : ℝ)) ρ + genVec cxCoeff ρ) cxShock
        ((0 : ℕ) + 1) (true, true) = 0 := by
  refine ⟨fun t => by funext ω; simp, fun t => by funext ω; simp, cx_isMAVec, ?_, ?_⟩
  · rw [map_neg, Pi.neg_apply, cx_innov_shock]
    simp
  · simp [dotShock, genVec, gen]

/-! ### (4.12) -/

/-- Cochrane (2023), eq. (4.12), p. 98: with geometric-maturity debt (`|ω| ≤ 1`),
`a_π(ω)'ε_{t+1} = [−a_s(ρ) − a_g(ρ) + a_r(ρ) − a_r(ω)]'ε_{t+1}` (the `j = 0` terms cancel), where
`∑_j ωʲ Δ_{t+1}π_{t+1+j} = a_π(ω)'ε_{t+1}`. -/
theorem identity_4_12 {ρ om : ℝ} (hρ : |ρ| ≤ 1) (hom : |om| ≤ 1)
    {v r rn infl g s q : ℕ → Ω → ℝ} (h : Flow ρ v r g s) (hr : ∀ t, r t = rn t - infl t)
    (hb : BondReturn om q rn) (hv : 𝔼.Adapted v) (hq : 𝔼.Adapted q) (hT : InnovTVC 𝔼 ρ v)
    (hTq : ∀ t ω, Tendsto (fun T => om ^ T * innov 𝔼 t (q (t + 1 + T)) ω) atTop (𝓝 0))
    {n : ℕ} {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ}
    (hM : ∀ k i ω, |ε k i ω| ≤ M) {as ag ar ap : ℕ → Fin n → ℝ} (hs : IsMAVec as ε s)
    (hg : IsMAVec ag ε g) (har : IsMAVec ar ε r) (hp : IsMAVec ap ε infl) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => om ^ j * innov 𝔼 t (infl (t + 1 + j)) ω)
        (dotShock (genVec ap om) ε ((t : ℤ) + 1) ω) ∧
      dotShock (genVec ap om) ε ((t : ℤ) + 1) =
        dotShock (-genVec as ρ - genVec ag ρ + genVec ar ρ - genVec ar om) ε ((t : ℤ) + 1) := by
  have hP := seriesTo_innov_MAVec 𝔼 hp hε hM hom t
  refine ⟨hP ω, ?_⟩
  funext ω'
  have h1 := weighted_inflation_identity 𝔼 h hr hb hv hq (hT t ω') (hTq t ω')
    (seriesTo_innov_MAVec 𝔼 hs hε hM hρ t ω') (seriesTo_innov_MAVec 𝔼 hg hε hM hρ t ω')
    (hP ω')
  have h2 := ((seriesTo_innov_MAVec_succ 𝔼 har hε hM hρ t ω').sub
    (seriesTo_innov_MAVec_succ 𝔼 har hε hM hom t ω')).unique
    (h1.congr (fun j => by ring) rfl)
  simp only [dotShock_sub, dotShock_add, dotShock_neg, Pi.sub_apply, Pi.add_apply,
    Pi.neg_apply] at h2 ⊢
  linarith

/-! ### Campbell–Shiller and Campbell–Ammer -/

/-- Cochrane (2023), p. 98 (Campbell and Shiller 1988): the linearised return identity
`r_{t+1} = ρ (p − d)_{t+1} − (p − d)_t + Δd_{t+1}` (variables in deviations from constants),
with `pd` the log price–dividend ratio and `dd` log dividend growth. -/
def CSReturn (ρ : ℝ) (pd dd r : ℕ → Ω → ℝ) : Prop :=
  ∀ t, r (t + 1) = ρ • pd (t + 1) - pd t + dd (t + 1)

/-- Cochrane (2023), p. 98: the Campbell–Shiller identity is the valuation recursion with payoff
`Δd − r`. -/
theorem csReturn_iff_recursion (ρ : ℝ) (pd dd r : ℕ → Ω → ℝ) :
    CSReturn ρ pd dd r ↔ Recursion ρ pd (fun t => dd t - r t) := by
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> funext ω <;> have := congrFun h ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢ <;> linarith

/-- Cochrane (2023), p. 98 (Campbell–Shiller, finite horizon, ex post):
`p_t − d_t = ∑_{j=1}^{T} ρ^{j−1}(Δd_{t+j} − r_{t+j}) + ρᵀ(p − d)_{t+T}`. -/
theorem campbellShiller_finite {ρ : ℝ} {pd dd r : ℕ → Ω → ℝ} (h : CSReturn ρ pd dd r)
    (t T : ℕ) :
    pd t = ∑ j ∈ Finset.range T, ρ ^ j • (dd (t + 1 + j) - r (t + 1 + j)) +
      ρ ^ T • pd (t + T) :=
  rec_finite ((csReturn_iff_recursion ρ pd dd r).1 h) t T

/-- Cochrane (2023), p. 98 (Campbell and Shiller 1988): ex post, under `ρᵀ(p − d)_{t+T} → 0`,
`p_t − d_t = ∑_{j ≥ 1} ρ^{j−1}(Δd_{t+j} − r_{t+j})`. -/
theorem campbellShiller {ρ : ℝ} {pd dd r : ℕ → Ω → ℝ} (h : CSReturn ρ pd dd r) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * pd (t + T) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * (dd (t + 1 + j) ω - r (t + 1 + j) ω)) (pd t ω) :=
  rec_seriesTo_map LinearMap.id ((csReturn_iff_recursion ρ pd dd r).1 h) hT

/-- Cochrane (2023), p. 98: the Campbell–Shiller identity in expectation,
`p_t − d_t = E_t ∑_{j ≥ 1} ρ^{j−1}(Δd_{t+j} − r_{t+j})` under `ρᵀ E_t(p − d)_{t+T} → 0`. -/
theorem campbellShiller_expected {ρ : ℝ} {pd dd r : ℕ → Ω → ℝ} (h : CSReturn ρ pd dd r)
    (hpd : 𝔼.Adapted pd) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (pd (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * 𝔼.E t (dd (t + 1 + j) - r (t + 1 + j)) ω) (pd t ω) := by
  have h0 := rec_seriesTo_map (𝔼.E t) ((csReturn_iff_recursion ρ pd dd r).1 h) hT
  rwa [hpd t] at h0

/-- Cochrane (2023), p. 98, corrected (survey E5; Campbell and Ammer 1993):
`Δ_{t+1} r_{t+1} = Δ_{t+1} ∑_{j ≥ 1} ρ^{j−1} Δd_{t+j} − Δ_{t+1} ∑_{j ≥ 2} ρ^{j−1} r_{t+j}`: if the
dividend-news sum converges to `D`, the return-news sum `∑_{j≥0} ρ^{j+1}Δ_{t+1}r_{t+2+j}`
converges to `D − Δ_{t+1}r_{t+1}`. -/
theorem campbellAmmer {ρ : ℝ} {pd dd r : ℕ → Ω → ℝ} (h : CSReturn ρ pd dd r)
    (hpd : 𝔼.Adapted pd) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (pd (t + T)) ω) atTop (𝓝 0)) {D : ℝ}
    (hD : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (dd (t + 1 + j)) ω) D) :
    SeriesTo (fun j => ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j)) ω)
      (D - innov 𝔼 t (r (t + 1)) ω) := by
  have h0 := rec_seriesTo_map (innov 𝔼 t) ((csReturn_iff_recursion ρ pd dd r).1 h) hT
  rw [innov_of_known 𝔼 (hpd t)] at h0
  have hR : SeriesTo (fun j => ρ ^ j * innov 𝔼 t (r (t + 1 + j)) ω) (D - 0) :=
    hD.sub h0 |>.congr (fun j => by simp only [map_sub, Pi.sub_apply]; ring) rfl
  refine (seriesTo_succ_iff.1 hR).congr (fun j => ?_) (by simp)
  rw [show t + 1 + (j + 1) = t + 2 + j by omega]

/-- Cochrane (2023), p. 98 (Campbell–Ammer in moving-average form):
`Δ_{t+1} r_{t+1} = {a_d(ρ) − [a_r(ρ) − a_r(0)]}'ε_{t+1}` (for `|ρ| ≤ 1`). -/
theorem campbellAmmer_MA {ρ : ℝ} (hρ : |ρ| ≤ 1) {pd dd r : ℕ → Ω → ℝ}
    (h : CSReturn ρ pd dd r) (hpd : 𝔼.Adapted pd) (hT : InnovTVC 𝔼 ρ pd) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {ad ar : ℕ → Fin n → ℝ} (hd : IsMAVec ad ε dd) (har : IsMAVec ar ε r) (t : ℕ) :
    innov 𝔼 t (r (t + 1)) = dotShock (genVec ad ρ - (genVec ar ρ - ar 0)) ε ((t : ℤ) + 1) := by
  funext ω
  have h1 := campbellAmmer 𝔼 h hpd (hT t ω) (seriesTo_innov_MAVec 𝔼 hd hε hM hρ t ω)
  have h2 := (seriesTo_innov_MAVec_succ 𝔼 har hε hM hρ t ω).unique h1
  simp only [dotShock_sub, Pi.sub_apply] at h2 ⊢
  linarith

/-- Cochrane (2023), eq. (4.13), p. 98: `0 = [a_d(ρ) − a_r(ρ)]'ε_{t+1}`, an identity
generalising the Hansen–Roberds–Sargent test to time-varying expected returns. -/
theorem identity_4_13 {ρ : ℝ} (hρ : |ρ| ≤ 1) {pd dd r : ℕ → Ω → ℝ}
    (h : CSReturn ρ pd dd r) (hpd : 𝔼.Adapted pd) (hT : InnovTVC 𝔼 ρ pd) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {ad ar : ℕ → Fin n → ℝ} (hd : IsMAVec ad ε dd) (har : IsMAVec ar ε r) (t : ℕ) :
    dotShock (genVec ad ρ - genVec ar ρ) ε ((t : ℤ) + 1) = 0 := by
  have h1 := campbellAmmer_MA 𝔼 hρ h hpd hT hε hM hd har t
  rw [innov_MAVec 𝔼 har hε hM t 0] at h1
  have h2 : dotShock (genVec ad ρ - genVec ar ρ) ε ((t : ℤ) + 1) =
      dotShock (genVec ad ρ - (genVec ar ρ - ar 0)) ε ((t : ℤ) + 1) - dotShock (ar 0) ε
        ((t : ℤ) + 1) := by
    rw [← dotShock_sub]
    congr 1
    abel
  rw [h2, ← h1]
  simp

/-- Cochrane (2023), eq. (4.13), p. 98, coefficient form: with non-degenerate shocks,
`a_d(ρ) = a_r(ρ)`. -/
theorem identity_4_13_vec {ρ : ℝ} (hρ : |ρ| ≤ 1) {pd dd r : ℕ → Ω → ℝ}
    (h : CSReturn ρ pd dd r) (hpd : 𝔼.Adapted pd) (hT : InnovTVC 𝔼 ρ pd) {n : ℕ}
    {ε : ℤ → Fin n → Ω → ℝ} (hε : IsMDSVec 𝔼 ε) {M : ℝ} (hM : ∀ k i ω, |ε k i ω| ≤ M)
    {ad ar : ℕ → Fin n → ℝ} (hd : IsMAVec ad ε dd) (har : IsMAVec ar ε r) (t : ℕ)
    (hnd : Nondeg ε ((t : ℤ) + 1)) : genVec ad ρ = genVec ar ρ :=
  sub_eq_zero.1 (hnd _ (identity_4_13 𝔼 hρ h hpd hT hε hM hd har t))

/-- Cochrane (2023), p. 98: the printed Campbell–Ammer right-hand side,
`Δ_{t+1}∑_{j≥1}ρ^{j−1}Δd_{t+1} − Δ_{t+1}∑_{j≥2}ρ^{j−1}Δr_{t+j}` (with
`Δr_{t+j} = r_{t+j} − r_{t+j−1}`, as typeset). -/
noncomputable def printedCampbellAmmer (ρ : ℝ) (dd r : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j : ℕ, ρ ^ j * innov 𝔼 t (dd (t + 1)) ω -
    ∑' j : ℕ, ρ ^ (j + 1) * innov 𝔼 t (r (t + 2 + j) - r (t + 1 + j)) ω

/-- Cochrane (2023), p. 98 (survey E5 counterexample): with i.i.d. coin-flip dividend growth and
returns `Δd_t = r_t = ε_t`, a constant price–dividend ratio and `ρ = 1/2`, the Campbell–Shiller
identity holds and `Δ_1 r_1 = 1` after heads, but the printed display gives `5/2`. -/
theorem printed_campbellAmmer_counterexample :
    CSReturn (1 / 2) (fun _ => 0) cxSurplus cxSurplus ∧
      innov ExpectationsFiniteTree.coinSystem 0 (cxSurplus (0 + 1)) (true, true) = 1 ∧
      printedCampbellAmmer ExpectationsFiniteTree.coinSystem (1 / 2) cxSurplus cxSurplus 0
        (true, true) = 5 / 2 := by
  have hsh := cx_innov_shock
  refine ⟨fun t => by funext ω; simp, by simpa using hsh 1, ?_⟩
  unfold printedCampbellAmmer
  have h1 : ∀ j : ℕ, (1 / 2 : ℝ) ^ j *
      innov ExpectationsFiniteTree.coinSystem 0 (cxSurplus (0 + 1)) (true, true) =
      (1 / 2 : ℝ) ^ j := fun j => by rw [hsh]; simp
  have h2 : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 1) *
      innov ExpectationsFiniteTree.coinSystem 0 (cxSurplus (0 + 2 + j) - cxSurplus (0 + 1 + j))
        (true, true) = if j = 0 then -(1 / 2) else 0 := fun j => by
    rw [map_sub, Pi.sub_apply, hsh, hsh]
    rcases j with _ | j
    · norm_num
    · simp only [show 0 + 2 + (j + 1) ≠ 1 by omega, show 0 + 1 + (j + 1) ≠ 1 by omega,
        ↓reduceIte, sub_self, mul_zero, Nat.add_one_ne_zero]
  simp_rw [h1, h2]
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num), tsum_ite_eq]
  norm_num

/-! ### A2 §2.3: what can and cannot be tested -/

/-- Cochrane (2023), A2 §2.3, p. 606 ("The present value relation in a model with a constant
discount rate is not an identity"): under the flow identity (no growth) and the terminal
condition, `v_t = E_t ∑ ρʲ s̃_{t+1+j}` holds iff the discounted expected returns sum to zero. -/
theorem pv_constant_discount_iff {ρ : ℝ} {v r s : ℕ → Ω → ℝ}
    (h : Flow ρ v r (fun _ => 0) s) (hv : 𝔼.Adapted v) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop (𝓝 0)) {S : ℝ}
    (hS : SeriesTo (fun j => ρ ^ j * 𝔼.E t (s (t + 1 + j)) ω) S) :
    v t ω = S ↔ SeriesTo (fun j => ρ ^ j * 𝔼.E t (r (t + 1 + j)) ω) 0 := by
  have hG : SeriesTo (fun j => ρ ^ j * 𝔼.E t ((fun _ => (0 : Ω → ℝ)) (t + 1 + j)) ω) 0 :=
    seriesTo_zero.congr (fun j => by simp) rfl
  have hR := pv_expected 𝔼 h hv hT hS hG
  constructor
  · intro hvS
    exact hR.congr (fun _ => rfl) (by rw [hvS]; ring)
  · intro h0
    have := h0.unique hR
    linarith

end Cochrane.DebtDeficitsInflation.GeneralizedHRS
