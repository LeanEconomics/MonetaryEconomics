/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.ForwardSolution
import Generality.ExpectationsFiniteTree
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Long-term debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.1, pp. 52–53, eqs.
(3.1)–(3.3), and Online Appendix A1, §1.2.1, pp. 559–561, eqs. (1.14)–(1.16), (1.19), the
forward-guidance display and the roll-over display.

## Setting

Random variables are `Ω → ℝ`, processes `ℕ → Ω → ℝ`, and `E_t` is an arbitrary
`ExpectationSystem` (perfect foresight or genuine uncertainty). Discounting uses one-period
stochastic discount factors `m t = Λ_{t+1}/Λ_t` (known at `t + 1`); the multi-period factor is
`sdf m t n = ∏_{k<n} m (t+k) = Λ_{t+n}/Λ_t`. The book's §3.1 case is the constant factor
`m ≡ β` (`sdf_const`), for which `sdf m t n = βⁿ`; everything below holds for a general `m`
(which §3.3 needs).

Debt: `B t j` is `B_{t−1}^{(t+j)}`, the face value of zero-coupon bonds outstanding at the end of
date `t − 1` that come due at `t + j`; so `B_t^{(t+j)} = B (t+1) (j−1)`. `Q t j` is
`Q_t^{(t+j)}`, the date-`t` price of a bond due at `t + j`.

## Main results

* Discounting machinery (restated from the Woodford Chapter 2 project, `AssetPricing` and
  `IntertemporalBudget`, adapted to signed surpluses): `sdf`, `MonotoneConvergence`, `pv`,
  `telescope`, and the general valuation theorem `flow_tvc_iff_pv`: for an adapted real debt
  value `x`, the flow `x_t = s_t + E_t[m_t x_{t+1}]` at every date plus the transversality
  condition `lim_N E_t[sdf_N x_{t+N}] = 0` at every date hold iff
  `x_t = ∑_n E_t[sdf_n s_{t+n}]` at every date, for signed surpluses with absolutely summable
  present values. `E_tsum_abs`, `pv_eq_E_tsum`: `E_t` may be taken outside the sum.
* (3.1): `ZeroPrice`, `zeroPrice_real`, `zeroPrice_zero`, `zeroPrice_recursive`; under perfect
  foresight `zeroPrice_pf_prod` (the term structure is the product of one-period prices).
* (3.2)–(3.3) with a finite maximum maturity: `FlowLT`, `flowLT_iff_value` (exact algebra),
  `flowLT_iff_recursion` (uses (3.1)), `valuationLT_iff` (flow + TVC ⟺ (3.3) at all dates), and
  survey error E28: the book's converse "derive (3.2) from (3.3)" needs (3.1)
  (`valuationLT_not_imp_flow`).
* (3.2)–(3.3) with a geometric maturity structure `B_{t−1}^{(t+j)} = ωʲ b_t`, genuine infinite
  sums: `GeomFlow`, `geomFlow_iff_recursion`, `valuationGeom_iff`.
* A1 (1.14)–(1.16), (1.19): `geom_value`, `pv_const_value`, `steady_state_1_15`,
  `price_jump_perm`, `price_jump_of_valuation`, `price_jump_lt_one_iff`, `price_jump_omega_zero`,
  `price_jump_perpetuity`, numerical checks; the forward-guidance closed form `price_jump_fg`,
  `fg_tendsto_zero`,
  `fg_drop_antitone_T`, `fg_drop_strictMonoOn_omega`; transitory and mean-reverting rises
  (`annuity_mono_rates`, `price_le_of_annuity_le`, `meanReverting_le_perm`); roll-over
  `geom_rollover` and `steady_flow_iff_1_15`; the knife edge `geom_knife_edge` (no trading iff
  `P_ts_t = ωᵗb_0`), `knife_edge_surplus_known`, `geom_needs_tending`.
-/

namespace Cochrane.Generality.LongTermDebt

open Filter Topology

variable {Ω : Type*}

/-! ### Stochastic discount factors (restated from the Woodford Chapter 2 project) -/

/-- Cochrane (2023), §3.3, p. 55 (and §3.1, p. 53 with `m ≡ β`): the multi-period discount
factor `Λ_{t+n}/Λ_t = ∏_{k<n} m_{t+k}` built from one-period factors `m s = Λ_{s+1}/Λ_s`
(restated from the Woodford Chapter 2 project). -/
def sdf (m : ℕ → Ω → ℝ) (t n : ℕ) : Ω → ℝ := ∏ k ∈ Finset.range n, m (t + k)

/-- Cochrane (2023), p. 55: `Λ_t/Λ_t = 1`. -/
@[simp] theorem sdf_zero (m : ℕ → Ω → ℝ) (t : ℕ) : sdf m t 0 = 1 := by
  simp [sdf]

/-- Cochrane (2023), p. 55: `Λ_{t+n+1}/Λ_t = (Λ_{t+n}/Λ_t)(Λ_{t+n+1}/Λ_{t+n})`. -/
theorem sdf_succ (m : ℕ → Ω → ℝ) (t n : ℕ) : sdf m t (n + 1) = sdf m t n * m (t + n) := by
  simp [sdf, Finset.prod_range_succ]

/-- Cochrane (2023), p. 55: `Λ_{t+n+1}/Λ_t = (Λ_{t+1}/Λ_t)(Λ_{t+1+n}/Λ_{t+1})`. -/
theorem sdf_succ' (m : ℕ → Ω → ℝ) (t n : ℕ) : sdf m t (n + 1) = m t * sdf m (t + 1) n := by
  rw [sdf, Finset.prod_range_succ', sdf, add_zero, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show t + (k + 1) = t + 1 + k by omega]

/-- Cochrane (2023), p. 55: the one-period factor is `Λ_{t+1}/Λ_t`. -/
@[simp] theorem sdf_one (m : ℕ → Ω → ℝ) (t : ℕ) : sdf m t 1 = m t := by
  simp [sdf]

/-- Cochrane (2023), p. 55: `Λ_{t+n+k}/Λ_t = (Λ_{t+n}/Λ_t)(Λ_{t+n+k}/Λ_{t+n})`. -/
theorem sdf_add (m : ℕ → Ω → ℝ) (t n k : ℕ) :
    sdf m t (n + k) = sdf m t n * sdf m (t + n) k := by
  simp only [sdf, Finset.prod_range_add, add_assoc]

/-- Cochrane (2023), §3.1, p. 53: with the constant discount factor `m ≡ β` of the
frictionless constant-real-rate model, `Λ_{t+n}/Λ_t = βⁿ`. -/
theorem sdf_const (β : ℝ) (t n : ℕ) : sdf (fun _ _ => β : ℕ → Ω → ℝ) t n = fun _ => β ^ n := by
  funext ω
  simp [sdf, Finset.prod_apply]

/-- Cochrane (2023), p. 55: nonnegative one-period factors give nonnegative discount factors. -/
theorem sdf_nonneg {m : ℕ → Ω → ℝ} (hm : ∀ s ω, 0 ≤ m s ω) (t n : ℕ) (ω : Ω) :
    0 ≤ sdf m t n ω := by
  simp only [sdf, Finset.prod_apply]
  exact Finset.prod_nonneg fun k _ => hm (t + k) ω

/-- Cochrane (2023), p. 55: positive one-period factors give positive discount factors. -/
theorem sdf_pos {m : ℕ → Ω → ℝ} (hm : ∀ s ω, 0 < m s ω) (t n : ℕ) (ω : Ω) :
    0 < sdf m t n ω := by
  simp only [sdf, Finset.prod_apply]
  exact Finset.prod_pos fun k _ => hm (t + k) ω

variable (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 55 (information accumulates): a variable known at `s` is known at
every later date. -/
theorem known_of_le {s T : ℕ} (h : s ≤ T) {x : Ω → ℝ} (hx : 𝔼.E s x = x) : 𝔼.E T x = x :=
  calc 𝔼.E T x = 𝔼.E T (𝔼.E s x) := by rw [hx]
    _ = 𝔼.E s x := 𝔼.known h x
    _ = x := hx

/-- Cochrane (2023), p. 55 (pull-out): the product of two date-`t` variables is known at `t`. -/
theorem known_mul (hP : 𝔼.PullOut) {t : ℕ} {a b : Ω → ℝ} (ha : 𝔼.E t a = a)
    (hb : 𝔼.E t b = b) : 𝔼.E t (a * b) = a * b := by
  rw [hP t a b ha, hb]

/-- Cochrane (2023), p. 55: expectations of nonnegative variables are nonnegative. -/
theorem E_nonneg {t : ℕ} {x : Ω → ℝ} (hx : ∀ ω, 0 ≤ x ω) (ω : Ω) : 0 ≤ 𝔼.E t x ω := by
  have h := 𝔼.mono t (show (0 : Ω → ℝ) ≤ x from hx) ω
  simpa using h

/-- Cochrane (2023), p. 55: `|E_t x| ≤ E_t |x|`. -/
theorem abs_E_le_E_abs (t : ℕ) (x : Ω → ℝ) (ω : Ω) :
    |𝔼.E t x ω| ≤ 𝔼.E t (fun ω' => |x ω'|) ω := by
  rw [abs_le]
  constructor
  · have h := 𝔼.mono t (show -(fun ω' => |x ω'|) ≤ x from fun ω' => by
      simp only [Pi.neg_apply]; exact neg_abs_le _) ω
    rw [map_neg] at h
    simpa using h
  · exact 𝔼.mono t (show x ≤ fun ω' => |x ω'| from fun ω' => le_abs_self _) ω

/-- Cochrane (2023), p. 55: `Λ_{t+n}/Λ_t` is known at `t + n` when each `m s` is known at
`s + 1`. -/
theorem sdf_known (hP : 𝔼.PullOut) {m : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (t n : ℕ) : 𝔼.E (t + n) (sdf m t n) = sdf m t n := by
  induction n with
  | zero =>
    rw [sdf_zero]
    exact 𝔼.const (t + 0) 1
  | succ n ih =>
    rw [sdf_succ, ← add_assoc]
    exact known_mul 𝔼 hP (known_of_le 𝔼 (Nat.le_succ _) ih) (hm (t + n))

/-- Cochrane (2023), p. 55 (pull-out and the law of iterated expectations):
`E_t[(Λ_{t+n}/Λ_t) E_{t+n} Y] = E_t[(Λ_{t+n}/Λ_t) Y]`. -/
theorem E_sdf_mul_E (hP : 𝔼.PullOut) {m : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (t n : ℕ) (Y : Ω → ℝ) :
    𝔼.E t (sdf m t n * 𝔼.E (t + n) Y) = 𝔼.E t (sdf m t n * Y) := by
  rw [← hP (t + n) _ _ (sdf_known 𝔼 hP hm t n), 𝔼.tower (Nat.le_add_right t n)]

/-! ### Conditional monotone convergence and present values -/

/-- Cochrane (2023), p. 53 and p. 55 (the interchange of `E_t` and infinite sums behind
(3.3) and (3.5), survey E29): conditional monotone convergence. Not implied by the
`ExpectationSystem` axioms, so it is a hypothesis; it holds for perfect foresight and for every
finite event tree (restated from the Woodford Chapter 2 project). -/
def MonotoneConvergence (𝔼 : ExpectationSystem Ω) : Prop :=
  ∀ t (f : ℕ → Ω → ℝ), (∀ k ω, 0 ≤ f k ω) → (∀ ω, Summable fun k => f k ω) →
    ∀ ω, HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω)

/-- Cochrane (2023), p. 55: perfect foresight satisfies conditional monotone convergence. -/
theorem perfectForesight_monotoneConvergence : MonotoneConvergence perfectForesight :=
  fun _ _ _ hs ω => (hs ω).hasSum

/-- Cochrane (2023), p. 55: every finite event tree satisfies conditional monotone
convergence, so the results hold under genuine uncertainty. -/
theorem finiteTree_monotoneConvergence {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : MonotoneConvergence T.toExpectationSystem := by
  classical
  intro t f _ hs ω
  simp only [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    ExpectationsFiniteTree.FiniteTree.condE, ExpectationsFiniteTree.FiniteTree.num]
  refine HasSum.div_const ?_ _
  refine hasSum_sum fun ω' _ => ?_
  split_ifs
  · exact (hs ω').hasSum.mul_left _
  · exact hasSum_zero

/-- Cochrane (2023), p. 55: `E_t` commutes with a series of random variables that converges
absolutely in every state (split into positive and negative parts, then conditional monotone
convergence). -/
theorem E_tsum_abs (hMC : MonotoneConvergence 𝔼) (t : ℕ) {f : ℕ → Ω → ℝ}
    (hf : ∀ ω, Summable fun k => |f k ω|) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (f k) ω) (𝔼.E t (fun ω' => ∑' k, f k ω') ω) := by
  set fp : ℕ → Ω → ℝ := fun k ω' => max (f k ω') 0 with hfp
  set fn : ℕ → Ω → ℝ := fun k ω' => max (-f k ω') 0 with hfn
  have hfp0 : ∀ k ω', 0 ≤ fp k ω' := fun _ _ => le_max_right _ _
  have hfn0 : ∀ k ω', 0 ≤ fn k ω' := fun _ _ => le_max_right _ _
  have hsp : ∀ ω', Summable fun k => fp k ω' := fun ω' =>
    Summable.of_nonneg_of_le (fun k => hfp0 k ω')
      (fun k => max_le (le_abs_self _) (abs_nonneg _)) (hf ω')
  have hsn : ∀ ω', Summable fun k => fn k ω' := fun ω' =>
    Summable.of_nonneg_of_le (fun k => hfn0 k ω')
      (fun k => max_le (neg_le_abs _) (abs_nonneg _)) (hf ω')
  have hsplit : ∀ k, f k = fp k - fn k := fun k => by
    funext ω'
    simp [hfp, hfn, max_zero_sub_max_neg_zero_eq_self]
  have hsum : (fun ω' => ∑' k, f k ω') =
      (fun ω' => ∑' k, fp k ω') - fun ω' => ∑' k, fn k ω' := by
    funext ω'
    rw [Pi.sub_apply, ← (hsp ω').tsum_sub (hsn ω')]
    exact tsum_congr fun k => congrFun (hsplit k) ω'
  rw [hsum, map_sub, Pi.sub_apply]
  convert (hMC t fp hfp0 hsp ω).sub (hMC t fn hfn0 hsn ω) using 1
  funext k
  rw [hsplit k, map_sub, Pi.sub_apply]

/-- Cochrane (2023), eqs. (3.3), (3.5), pp. 53, 55: the date-`t` present value
`∑_{n ≥ 0} E_t[(Λ_{t+n}/Λ_t) s_{t+n}]` of a real surplus stream, as a genuine infinite sum in
each state (summability is an explicit hypothesis wherever it is used). -/
noncomputable def pv (m s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' n, 𝔼.E t (sdf m t n * s (t + n)) ω

/-- Cochrane (2023), pp. 53, 55 (survey E29): the surplus stream has absolutely summable
present values, `∑_n E_t[(Λ_{t+n}/Λ_t)|s_{t+n}|] < ∞` at every date and in every state.
Surpluses are signed, so absolute (not mere) summability is assumed. -/
def SurplusSummable (m s : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Summable fun n => 𝔼.E t (sdf m t n * fun ω' => |s (t + n) ω'|) ω

/-- Cochrane (2023), pp. 53, 55: `|E_t[sdf·s]| ≤ E_t[sdf·|s|]` for nonnegative discount
factors. -/
theorem abs_E_sdf_mul_le {m : ℕ → Ω → ℝ} (hm0 : ∀ s ω, 0 ≤ m s ω) (s : ℕ → Ω → ℝ)
    (t n : ℕ) (ω : Ω) :
    |𝔼.E t (sdf m t n * s (t + n)) ω| ≤ 𝔼.E t (sdf m t n * fun ω' => |s (t + n) ω'|) ω := by
  have h : (fun ω' => |(sdf m t n * s (t + n)) ω'|) = sdf m t n * fun ω' => |s (t + n) ω'| :=
    funext fun ω' => by
      simp only [Pi.mul_apply, abs_mul, abs_of_nonneg (sdf_nonneg hm0 t n ω')]
  rw [← h]
  exact abs_E_le_E_abs 𝔼 t _ ω

/-- Cochrane (2023), pp. 53, 55: absolutely summable surpluses have a summable present-value
series at every date and in every state. -/
theorem summable_pv {m s : ℕ → Ω → ℝ} (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf m t n * s (t + n)) ω :=
  Summable.of_norm_bounded (hs t ω) fun n => by
    rw [Real.norm_eq_abs]; exact abs_E_sdf_mul_le 𝔼 hm0 s t n ω

/-- Cochrane (2023), pp. 53, 55: `E_t` may be taken outside the present-value sum,
`∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}] = E_t ∑_n (Λ_{t+n}/Λ_t)s_{t+n}` (the book's notation), whenever
the discounted surplus series converges absolutely in every state. -/
theorem pv_eq_E_tsum (hMC : MonotoneConvergence 𝔼) {m s : ℕ → Ω → ℝ} (t : ℕ)
    (habs : ∀ ω, Summable fun n => |sdf m t n ω * s (t + n) ω|) :
    pv 𝔼 m s t = 𝔼.E t (fun ω => ∑' n, sdf m t n ω * s (t + n) ω) := by
  funext ω
  exact (E_tsum_abs 𝔼 hMC t (f := fun n => sdf m t n * s (t + n)) habs ω).tsum_eq

/-- Cochrane (2023), p. 55 (restated from the Woodford Chapter 2 project): for a nonnegative
stream `Y` whose date-`(t+N)` present value converges in every state,
`E_t[sdf_N ∑_n E_{t+N}[sdf Y]] = ∑_k E_t[sdf_{k+N} Y_{t+k+N}]`. -/
theorem hasSum_E_sdf_mul_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {m Y : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hY : ∀ s ω, 0 ≤ Y s ω) (t N : ℕ)
    (hs : ∀ ω, Summable fun n => 𝔼.E (t + N) (sdf m (t + N) n * Y (t + N + n)) ω) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (sdf m t (k + N) * Y (t + (k + N))) ω)
      (𝔼.E t (sdf m t N * pv 𝔼 m Y (t + N)) ω) := by
  set f : ℕ → Ω → ℝ :=
    fun n => sdf m t N * 𝔼.E (t + N) (sdf m (t + N) n * Y (t + N + n)) with hf
  have hf0 : ∀ k ω, 0 ≤ f k ω := fun k ω =>
    mul_nonneg (sdf_nonneg hm0 t N ω)
      (E_nonneg 𝔼 (fun ω' => mul_nonneg (sdf_nonneg hm0 _ _ ω') (hY _ ω')) ω)
  have hfs : ∀ ω, Summable fun k => f k ω := fun ω => (hs ω).mul_left (sdf m t N ω)
  have hsum : sdf m t N * pv 𝔼 m Y (t + N) = fun ω' => ∑' k, f k ω' := by
    funext ω'
    simp only [hf, pv, Pi.mul_apply, tsum_mul_left]
  rw [hsum]
  convert hMC t f hf0 hfs ω using 1
  funext k
  simp only [hf]
  rw [E_sdf_mul_E 𝔼 hP hm, ← mul_assoc, ← sdf_add, add_assoc, add_comm N k]

/-- Cochrane (2023), p. 55: the positive part `max s 0` of the surplus. -/
def posPart (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun k ω => max (s k ω) 0

/-- Cochrane (2023), p. 55: the negative part `max (−s) 0` of the surplus (a deficit). -/
def negPart (s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun k ω => max (-s k ω) 0

/-- Cochrane (2023), p. 55: `s = s⁺ − s⁻`. -/
theorem posPart_sub_negPart (s : ℕ → Ω → ℝ) (k : ℕ) : posPart s k - negPart s k = s k := by
  funext ω
  simp [posPart, negPart, max_zero_sub_max_neg_zero_eq_self]

/-- Cochrane (2023), p. 55: absolutely summable surpluses have summable positive-part present
values. -/
theorem summable_posPart {m s : ℕ → Ω → ℝ} (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf m t n * posPart s (t + n)) ω := by
  refine Summable.of_nonneg_of_le (fun n => E_nonneg 𝔼 (fun ω' => mul_nonneg
    (sdf_nonneg hm0 t n ω') (le_max_right _ _)) ω) (fun n => ?_) (hs t ω)
  refine 𝔼.mono t (fun ω' => ?_) ω
  simp only [Pi.mul_apply, posPart]
  exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
    (sdf_nonneg hm0 t n ω')

/-- Cochrane (2023), p. 55: absolutely summable surpluses have summable negative-part present
values. -/
theorem summable_negPart {m s : ℕ → Ω → ℝ} (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t : ℕ) (ω : Ω) :
    Summable fun n => 𝔼.E t (sdf m t n * negPart s (t + n)) ω := by
  refine Summable.of_nonneg_of_le (fun n => E_nonneg 𝔼 (fun ω' => mul_nonneg
    (sdf_nonneg hm0 t n ω') (le_max_right _ _)) ω) (fun n => ?_) (hs t ω)
  refine 𝔼.mono t (fun ω' => ?_) ω
  simp only [Pi.mul_apply, negPart]
  exact mul_le_mul_of_nonneg_left (max_le (neg_le_abs _) (abs_nonneg _))
    (sdf_nonneg hm0 t n ω')

/-- Cochrane (2023), p. 55: the present-value terms of `s` split as those of `s⁺` minus those
of `s⁻`. -/
theorem E_sdf_mul_split (m s : ℕ → Ω → ℝ) (t n : ℕ) :
    𝔼.E t (sdf m t n * s (t + n)) =
      𝔼.E t (sdf m t n * posPart s (t + n)) - 𝔼.E t (sdf m t n * negPart s (t + n)) := by
  rw [← map_sub, ← mul_sub, posPart_sub_negPart]

/-- Cochrane (2023), p. 55, for signed surpluses (restated from the Woodford Chapter 2
project): `E_t[sdf_N · pv_{t+N}] = ∑_k E_t[sdf_{k+N} s_{t+k+N}]`, the tail of the date-`t`
present value. -/
theorem hasSum_E_sdf_mul_pv_signed (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut)
    {m s : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t N : ℕ) (ω : Ω) :
    HasSum (fun k => 𝔼.E t (sdf m t (k + N) * s (t + (k + N))) ω)
      (𝔼.E t (sdf m t N * pv 𝔼 m s (t + N)) ω) := by
  have hp := hasSum_E_sdf_mul_pv 𝔼 hMC hP hm hm0 (Y := posPart s)
    (fun _ _ => le_max_right _ _) t N (summable_posPart 𝔼 hm0 hs (t + N)) ω
  have hn := hasSum_E_sdf_mul_pv 𝔼 hMC hP hm hm0 (Y := negPart s)
    (fun _ _ => le_max_right _ _) t N (summable_negPart 𝔼 hm0 hs (t + N)) ω
  have hpv : pv 𝔼 m s (t + N) = pv 𝔼 m (posPart s) (t + N) - pv 𝔼 m (negPart s) (t + N) := by
    funext ω'
    simp only [pv, Pi.sub_apply]
    rw [← (summable_posPart 𝔼 hm0 hs (t + N) ω').tsum_sub
      (summable_negPart 𝔼 hm0 hs (t + N) ω')]
    refine tsum_congr fun n => ?_
    rw [E_sdf_mul_split 𝔼 m s (t + N) n]
    rfl
  rw [hpv, mul_sub, map_sub]
  convert hp.sub hn using 1
  funext k
  rw [E_sdf_mul_split 𝔼 m s t (k + N)]
  rfl

/-- Cochrane (2023), p. 55: the present value is known at its date. -/
theorem E_pv_self (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {m s : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (t : ℕ) : 𝔼.E t (pv 𝔼 m s t) = pv 𝔼 m s t := by
  funext ω
  have h := hasSum_E_sdf_mul_pv_signed 𝔼 hMC hP hm hm0 hs t 0 ω
  simp only [sdf_zero, one_mul, add_zero] at h
  exact h.tsum_eq.symm

/-! ### Flow, transversality and present value -/

/-- Cochrane (2023), p. 55 (the flow condition in real terms): `x_t = s_t + E_t[m_t x_{t+1}]`
at every date, where `x_t` is the real value of debt at the start of date `t`. -/
def FlowRec (m s x : ℕ → Ω → ℝ) : Prop := ∀ t, x t = s t + 𝔼.E t (m t * x (t + 1))

/-- Cochrane (2023), p. 55: the transversality condition `lim_N E_t[(Λ_{t+N}/Λ_t)x_{t+N}] = 0`
looking forward from date `t`. -/
def TVC (m x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun N => 𝔼.E t (sdf m t N * x (t + N)) ω) atTop (𝓝 0)

/-- Cochrane (2023), p. 55: the slack `x_t − s_t − E_t[m_t x_{t+1}]` in the date-`t` flow. -/
def slack (m s x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := x t - s t - 𝔼.E t (m t * x (t + 1))

/-- Cochrane (2023), p. 53 ("iterating forward") and p. 55, as an exact identity: for `x`
known at `t`, `x_t − ∑_{n<N} E_t[sdf_n s_{t+n}] − E_t[sdf_N x_{t+N}]` is the discounted sum of
flow slacks `∑_{n<N} E_t[sdf_n slack_{t+n}]`. -/
theorem telescope (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) {t : ℕ} (hx : 𝔼.E t (x t) = x t) (N : ℕ) (ω : Ω) :
    x t ω - ∑ n ∈ Finset.range N, 𝔼.E t (sdf m t n * s (t + n)) ω
      - 𝔼.E t (sdf m t N * x (t + N)) ω
      = ∑ n ∈ Finset.range N, 𝔼.E t (sdf m t n * slack 𝔼 m s x (t + n)) ω := by
  induction N with
  | zero => simp [hx]
  | succ N ih =>
    have key : 𝔼.E t (sdf m t N * slack 𝔼 m s x (t + N)) =
        𝔼.E t (sdf m t N * x (t + N)) - 𝔼.E t (sdf m t N * s (t + N)) -
          𝔼.E t (sdf m t (N + 1) * x (t + (N + 1))) := by
      simp only [slack, mul_sub, map_sub]
      rw [E_sdf_mul_E 𝔼 hP hm, ← mul_assoc, ← sdf_succ, add_assoc]
    have k := congrFun key ω
    simp only [Pi.sub_apply] at k
    rw [Finset.sum_range_succ, Finset.sum_range_succ, k]
    linarith

/-- Cochrane (2023), p. 53 and p. 55 (from flow to present value): if the real debt value is
known at `t`, the flow condition holds at all dates from `t` on and the transversality
condition holds at `t`, then `x_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]`, with the series
convergent. -/
theorem hasSum_of_flow_tvc (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) {t : ℕ} (hx : 𝔼.E t (x t) = x t)
    (hflow : ∀ n, x (t + n) = s (t + n) + 𝔼.E (t + n) (m (t + n) * x (t + n + 1)))
    (htvc : TVC 𝔼 m x t) (ω : Ω) :
    HasSum (fun n => 𝔼.E t (sdf m t n * s (t + n)) ω) (x t ω) := by
  have hsl : ∀ n, slack 𝔼 m s x (t + n) = 0 := fun n => by
    funext ω'
    have h := congrFun (hflow n) ω'
    simp only [slack, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] at h ⊢
    linarith
  have hpart : ∀ N, ∑ n ∈ Finset.range N, 𝔼.E t (sdf m t n * s (t + n)) ω =
      x t ω - 𝔼.E t (sdf m t N * x (t + N)) ω := by
    intro N
    have h := telescope 𝔼 hP (s := s) hm hx N ω
    simp only [hsl, mul_zero, map_zero, Pi.zero_apply, Finset.sum_const_zero] at h
    linarith
  have hlim : Tendsto (fun N => ∑ n ∈ Finset.range N, 𝔼.E t (sdf m t n * s (t + n)) ω) atTop
      (𝓝 (x t ω)) := by
    simp_rw [hpart]
    simpa using (tendsto_const_nhds (x := x t ω)).sub (htvc ω)
  have hsum := summable_pv 𝔼 hm0 hs t ω
  rw [tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat]
  exact hsum.hasSum

/-- Cochrane (2023), p. 53 ("derive the flow from the present value at two adjacent dates")
and p. 55: if `x_t` equals the present value at every date, the flow condition holds. -/
theorem flow_of_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω) (hsa : 𝔼.Adapted s)
    (hs : SurplusSummable 𝔼 m s) (hx : ∀ t, x t = pv 𝔼 m s t) : FlowRec 𝔼 m s x := by
  intro t
  funext ω
  have h1 := hasSum_E_sdf_mul_pv_signed 𝔼 hMC hP hm hm0 hs t 1 ω
  simp only [sdf_one] at h1
  have hsum := summable_pv 𝔼 hm0 hs t ω
  rw [hx t, hx (t + 1), Pi.add_apply]
  simp only [pv]
  rw [hsum.tsum_eq_zero_add, ← h1.tsum_eq]
  simp only [sdf_zero, one_mul, add_zero, hsa t]

/-- Cochrane (2023), p. 55: if `x_t` equals the present value at every date, the
transversality condition holds at every date (the discounted value is the tail of a
convergent series). -/
theorem tvc_of_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω)
    (hs : SurplusSummable 𝔼 m s) (hx : ∀ t, x t = pv 𝔼 m s t) (t : ℕ) : TVC 𝔼 m x t := by
  intro ω
  have heq : ∀ N, 𝔼.E t (sdf m t N * x (t + N)) ω =
      ∑' k, 𝔼.E t (sdf m t (k + N) * s (t + (k + N))) ω := fun N => by
    rw [hx (t + N)]
    exact (hasSum_E_sdf_mul_pv_signed 𝔼 hMC hP hm hm0 hs t N ω).tsum_eq.symm
  simp_rw [heq]
  exact tendsto_sum_nat_add fun n => 𝔼.E t (sdf m t n * s (t + n)) ω

/-- Cochrane (2023), p. 53 (the step from (3.2) to (3.3) and back) and p. 55, eq. (3.5): for
an adapted real debt value `x`, nonnegative one-period discount factors known one period ahead,
adapted surpluses with absolutely summable present values, and `E_t` with pull-out and
conditional monotone convergence: the flow condition at every date plus the transversality
condition at every date hold iff `x_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` at every date. -/
theorem flow_tvc_iff_pv (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {m s x : ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ω, 0 ≤ m s ω) (hsa : 𝔼.Adapted s)
    (hs : SurplusSummable 𝔼 m s) (hx : 𝔼.Adapted x) :
    (FlowRec 𝔼 m s x ∧ ∀ t, TVC 𝔼 m x t) ↔ ∀ t, x t = pv 𝔼 m s t := by
  constructor
  · rintro ⟨hflow, htvc⟩ t
    funext ω
    exact (hasSum_of_flow_tvc 𝔼 hP hm hm0 hs (hx t) (fun n => hflow (t + n)) (htvc t)
      ω).tsum_eq.symm
  · intro hpv
    exact ⟨flow_of_pv 𝔼 hMC hP hm hm0 hsa hs hpv, tvc_of_pv 𝔼 hMC hP hm hm0 hs hpv⟩


/-! ### Zero-coupon bond prices (3.1) -/

/-- Cochrane (2023), eq. (3.1), p. 53, with a general discount factor (p. 55):
`Q_t^{(t+j)} = E_t[(Λ_{t+j}/Λ_t) P_t/P_{t+j}]`; the book's case is `m ≡ β`
(`zeroPrice_const_iff`). -/
def ZeroPrice (m P : ℕ → Ω → ℝ) (Q : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∀ t j, Q t j = 𝔼.E t (sdf m t j * fun ξ => P t ξ / P (t + j) ξ)

/-- Cochrane (2023), eq. (3.1), p. 53: with `m ≡ β`, `ZeroPrice` is exactly
`Q_t^{(t+j)} = E_t[βʲ P_t/P_{t+j}]`. -/
theorem zeroPrice_const_iff (β : ℝ) (P : ℕ → Ω → ℝ) (Q : ℕ → ℕ → Ω → ℝ) :
    ZeroPrice 𝔼 (fun _ _ => β) P Q ↔
      ∀ t j, Q t j = 𝔼.E t (fun ξ => β ^ j * (P t ξ / P (t + j) ξ)) := by
  simp only [ZeroPrice, sdf_const]
  rfl

/-- Cochrane (2023), eq. (3.1), p. 53, in real terms: the real price `Q_t^{(t+j)}/P_t` of a
nominal bond, `E_t[(Λ_{t+j}/Λ_t)/P_{t+j}]`. -/
noncomputable def realPrice (m P : ℕ → Ω → ℝ) (t j : ℕ) : Ω → ℝ :=
  𝔼.E t (sdf m t j * fun ξ => (P (t + j) ξ)⁻¹)

/-- Cochrane (2023), eq. (3.1), p. 53: given (3.1) and a price level known at `t`,
`Q_t^{(t+j)} = P_t E_t[(Λ_{t+j}/Λ_t)/P_{t+j}]`. -/
theorem zeroPrice_eq_mul (hP : 𝔼.PullOut) {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : ZeroPrice 𝔼 m P Q) {t : ℕ} (hPa : 𝔼.E t (P t) = P t) (j : ℕ) :
    Q t j = P t * realPrice 𝔼 m P t j := by
  rw [hQ t j, realPrice, ← hP t (P t) _ hPa]
  congr 1
  funext ξ
  simp only [Pi.mul_apply, div_eq_mul_inv]
  ring

/-- Cochrane (2023), eq. (3.1), p. 53: `Q_t^{(t+j)}/P_t = E_t[(Λ_{t+j}/Λ_t)/P_{t+j}]`. -/
theorem zeroPrice_real (hP : 𝔼.PullOut) {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : ZeroPrice 𝔼 m P Q) {t : ℕ} (hPa : 𝔼.E t (P t) = P t) (j : ℕ) {ξ : Ω}
    (hP0 : P t ξ ≠ 0) : Q t j ξ / P t ξ = realPrice 𝔼 m P t j ξ := by
  rw [zeroPrice_eq_mul 𝔼 hP hQ hPa j, Pi.mul_apply]
  field_simp

/-- Cochrane (2023), eq. (3.1), p. 53: maturing bonds are worth their face value,
`Q_t^{(t)} = 1`. -/
theorem zeroPrice_zero {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (hQ : ZeroPrice 𝔼 m P Q)
    {t : ℕ} (hP0 : ∀ ξ, P t ξ ≠ 0) : Q t 0 = 1 := by
  rw [hQ t 0, sdf_zero, one_mul]
  have h : (fun ξ => P t ξ / P (t + 0) ξ) = fun _ => (1 : ℝ) := by
    funext ξ
    simp [hP0 ξ]
  rw [h, 𝔼.const]
  rfl

/-- Cochrane (2023), eq. (3.1), p. 53: real bond prices are nonnegative when discount factors
are nonnegative and the price level is positive. -/
theorem realPrice_nonneg {m P : ℕ → Ω → ℝ} (hm0 : ∀ s ξ, 0 ≤ m s ξ)
    (hPpos : ∀ s ξ, 0 < P s ξ) (t j : ℕ) (ξ : Ω) : 0 ≤ realPrice 𝔼 m P t j ξ :=
  E_nonneg 𝔼 (fun ξ' => mul_nonneg (sdf_nonneg hm0 t j ξ')
    (inv_nonneg.mpr (hPpos (t + j) ξ').le)) ξ

/-- Cochrane (2023), eq. (3.1), p. 53 (tower property and pull-out): real bond prices obey
the recursion `Q_t^{(t+j+1)}/P_t = E_t[(Λ_{t+1}/Λ_t) Q_{t+1}^{(t+j+1)}/P_{t+1}]`. -/
theorem realPrice_succ (hP : 𝔼.PullOut) {m : ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (P : ℕ → Ω → ℝ) (t j : ℕ) :
    realPrice 𝔼 m P t (j + 1) = 𝔼.E t (m t * realPrice 𝔼 m P (t + 1) j) := by
  rw [realPrice, realPrice, ← hP (t + 1) (m t) _ (hm t), 𝔼.tower (Nat.le_succ t), sdf_succ',
    mul_assoc]
  congr 3
  funext ξ
  rw [show t + (j + 1) = t + 1 + j by omega]

/-- Cochrane (2023), eq. (3.1), p. 53: the recursive form of bond pricing,
`Q_t^{(t+j+1)} = E_t[(Λ_{t+1}/Λ_t)(P_t/P_{t+1}) Q_{t+1}^{(t+j+1)}]` (with `m ≡ β`:
`Q_t^{(t+j+1)} = βE_t[(P_t/P_{t+1})Q_{t+1}^{(t+j+1)}]`). -/
theorem zeroPrice_recursive (hP : 𝔼.PullOut) {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (t j : ℕ) :
    Q t (j + 1) = 𝔼.E t (m t * (fun ξ => P t ξ / P (t + 1) ξ) * Q (t + 1) j) := by
  rw [zeroPrice_eq_mul 𝔼 hP hQ (hPa t), realPrice_succ 𝔼 hP hm, ← hP t (P t) _ (hPa t)]
  congr 1
  funext ξ
  rw [zeroPrice_eq_mul 𝔼 hP hQ (hPa (t + 1)) j]
  have := hP0 (t + 1) ξ
  simp only [Pi.mul_apply]
  field_simp

/-- Cochrane (2023), eq. (3.1), p. 53, under perfect foresight: the term structure is the
product of one-period prices, `Q_t^{(t+j)} = ∏_{k<j} Q_{t+k}^{(t+k+1)}`. -/
theorem zeroPrice_pf_prod {m P : ℕ → Unit → ℝ} {Q : ℕ → ℕ → Unit → ℝ}
    (hQ : ZeroPrice perfectForesight m P Q) (hP0 : ∀ s ξ, P s ξ ≠ 0) (t j : ℕ) :
    Q t j = ∏ k ∈ Finset.range j, Q (t + k) 1 := by
  induction j with
  | zero =>
    rw [zeroPrice_zero perfectForesight hQ (hP0 t), Finset.prod_range_zero]
  | succ j ih =>
    rw [Finset.prod_range_succ, ← ih]
    funext ξ
    have h1 := congrFun (hQ t (j + 1)) ξ
    have h2 := congrFun (hQ t j) ξ
    have h3 := congrFun (hQ (t + j) 1) ξ
    simp only [perfectForesight, LinearMap.id_apply, Pi.mul_apply, sdf_one] at h1 h2 h3
    rw [Pi.mul_apply, h1, h2, h3, sdf_succ, Pi.mul_apply]
    have := hP0 (t + j) ξ
    rw [show t + (j + 1) = t + j + 1 by omega]
    field_simp

/-- Cochrane (2023), p. 56 and eq. (3.1), p. 53, under perfect foresight: with the one-period
interest rate defined by `Q_t^{(t+1)} = 1/(1+i_t)`, `Q_t^{(t+j)} = ∏_{k<j} 1/(1+i_{t+k})`. -/
theorem zeroPrice_pf_rates {m P i : ℕ → Unit → ℝ} {Q : ℕ → ℕ → Unit → ℝ}
    (hQ : ZeroPrice perfectForesight m P Q) (hP0 : ∀ s ξ, P s ξ ≠ 0)
    (hi : ∀ s, Q s 1 = fun ξ => (1 + i s ξ)⁻¹) (t j : ℕ) :
    Q t j = fun ξ => ∏ k ∈ Finset.range j, (1 + i (t + k) ξ)⁻¹ := by
  rw [zeroPrice_pf_prod hQ hP0 t j]
  funext ξ
  rw [Finset.prod_apply]
  exact Finset.prod_congr rfl fun k _ => by rw [hi]

/-- Cochrane (2023), p. 53 ("this event means future inflation rather than current
inflation"): under perfect foresight with `m ≡ β > 0`, a bond price below `βʲ` is the same
thing as a price level that rises between `t` and `t + j`. -/
theorem zeroPrice_lt_iff_inflation {β : ℝ} (hβ : 0 < β) {P : ℕ → Unit → ℝ}
    {Q : ℕ → ℕ → Unit → ℝ} (hQ : ZeroPrice perfectForesight (fun _ _ => β) P Q)
    (hPpos : ∀ s ξ, 0 < P s ξ) (t j : ℕ) (ξ : Unit) :
    Q t j ξ < β ^ j ↔ P t ξ < P (t + j) ξ := by
  have h := congrFun (hQ t j) ξ
  simp only [perfectForesight, LinearMap.id_apply, Pi.mul_apply, sdf_const] at h
  rw [h, mul_lt_iff_lt_one_right (pow_pos hβ j), div_lt_one (hPpos _ ξ)]

/-! ### Long-term debt with a finite maximum maturity: (3.2)–(3.3) -/

/-- Cochrane (2023), §3.1, p. 53: no bonds of maturity beyond `K` periods are outstanding,
`B_{t−1}^{(t+j)} = 0` for `j > K` (survey E29: the base case, in which every sum over
maturities is finite). -/
def MaxMaturity (K : ℕ) (B : ℕ → ℕ → Ω → ℝ) : Prop := ∀ t j, K < j → B t j = 0

/-- Cochrane (2023), eq. (3.2), p. 53: the flow condition with long-term debt,
`B_{t−1}^{(t)} = P_ts_t + ∑_{j≥1} Q_t^{(t+j)}(B_t^{(t+j)} − B_{t−1}^{(t+j)})`, where
`B_t^{(t+j)} = B (t+1) (j−1)`; with maximum maturity `K` the sum runs over `j = 1, …, K+1`. -/
def FlowLT (K : ℕ) (P s : ℕ → Ω → ℝ) (Q B : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  B t 0 = P t * s t + ∑ j ∈ Finset.range (K + 1), Q t (j + 1) * (B (t + 1) j - B t (j + 1))

/-- Cochrane (2023), eq. (3.3), p. 53: the nominal market value
`∑_j Q_t^{(t+j)} B_{t−1}^{(t+j)}` of the debt outstanding at the start of date `t`. -/
def mktValue (K : ℕ) (Q B : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range (K + 1), Q t j * B t j

/-- Cochrane (2023), eq. (3.2), p. 53: the date-`t` nominal value
`∑_{j≥1} Q_t^{(t+j)} B_t^{(t+j)}` of the debt carried into date `t + 1`. -/
def purchaseValue (K : ℕ) (Q B : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ j ∈ Finset.range (K + 1), Q t (j + 1) * B (t + 1) j

/-- Cochrane (2023), eq. (3.3), p. 53: the real market value of the debt,
`∑_j Q_t^{(t+j)} B_{t−1}^{(t+j)}/P_t`. -/
noncomputable def realValue (K : ℕ) (Q B : ℕ → ℕ → Ω → ℝ) (P : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ :=
  fun ξ => mktValue K Q B t ξ / P t ξ

/-- Cochrane (2023), eq. (3.2), p. 53, rearranged (exact algebra, no pricing assumption beyond
`Q_t^{(t)} = 1`): the flow condition holds iff the real market value of the debt equals the
surplus plus the real value of the debt carried forward. -/
theorem flowLT_iff_value {K : ℕ} {P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ}
    (hK : MaxMaturity K B) {t : ℕ} (hQ0 : Q t 0 = 1) (hP0 : ∀ ξ, P t ξ ≠ 0) :
    FlowLT K P s Q B t ↔
      realValue K Q B P t = s t + fun ξ => purchaseValue K Q B t ξ / P t ξ := by
  have hsplit : ∀ ξ, mktValue K Q B t ξ =
      B t 0 ξ + ∑ j ∈ Finset.range (K + 1), Q t (j + 1) ξ * B t (j + 1) ξ := by
    intro ξ
    simp only [mktValue, Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_range_succ', Finset.sum_range_succ (fun j => Q t (j + 1) ξ * B t (j + 1) ξ),
      hK t (K + 1) (by omega), hQ0]
    simp only [Pi.one_apply, Pi.zero_apply, mul_zero, add_zero, one_mul]
    ring
  have hflow : FlowLT K P s Q B t ↔ ∀ ξ, B t 0 ξ = P t ξ * s t ξ +
      (purchaseValue K Q B t ξ - ∑ j ∈ Finset.range (K + 1), Q t (j + 1) ξ * B t (j + 1) ξ) := by
    constructor
    · intro h ξ
      have h1 := congrFun h ξ
      simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply, Pi.sub_apply] at h1
      rw [h1, purchaseValue, Finset.sum_apply, ← Finset.sum_sub_distrib]
      simp only [Pi.mul_apply, mul_sub]
    · intro h
      funext ξ
      have h1 := h ξ
      simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply, Pi.sub_apply]
      rw [h1, purchaseValue, Finset.sum_apply, ← Finset.sum_sub_distrib]
      simp only [Pi.mul_apply, mul_sub]
  rw [hflow]
  constructor
  · intro h
    funext ξ
    have h1 := h ξ
    have h2 := hsplit ξ
    have := hP0 ξ
    simp only [realValue, Pi.add_apply]
    field_simp
    linarith
  · intro h ξ
    have h1 := congrFun h ξ
    have h2 := hsplit ξ
    have := hP0 ξ
    simp only [realValue, Pi.add_apply] at h1
    field_simp at h1
    linarith

/-- Cochrane (2023), eqs. (3.1)–(3.2), p. 53: given bond pricing (3.1), the real value of the
debt carried into `t + 1` is `E_t[(Λ_{t+1}/Λ_t) × (real market value at t + 1)]`. -/
theorem purchaseValue_real (hP : 𝔼.PullOut) {K : ℕ} {m P : ℕ → Ω → ℝ}
    {Q B : ℕ → ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hQ : ZeroPrice 𝔼 m P Q)
    (hPa : 𝔼.Adapted P) (hP0 : ∀ s ξ, P s ξ ≠ 0) {t : ℕ}
    (hB1 : ∀ j, 𝔼.E t (B (t + 1) j) = B (t + 1) j) :
    (fun ξ => purchaseValue K Q B t ξ / P t ξ) =
      𝔼.E t (m t * realValue K Q B P (t + 1)) := by
  have hfun : m t * realValue K Q B P (t + 1) =
      ∑ j ∈ Finset.range (K + 1), B (t + 1) j * (m t * realPrice 𝔼 m P (t + 1) j) := by
    funext ξ
    simp only [Pi.mul_apply, realValue, mktValue, Finset.sum_apply, Finset.sum_div,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← zeroPrice_real 𝔼 hP hQ (hPa (t + 1)) j (hP0 (t + 1) ξ)]
    ring
  rw [hfun, map_sum]
  funext ξ
  simp only [purchaseValue, Finset.sum_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hP t _ _ (hB1 j), ← realPrice_succ 𝔼 hP hm, Pi.mul_apply, Pi.mul_apply,
    ← zeroPrice_real 𝔼 hP hQ (hPa t) (j + 1) (hP0 t ξ)]
  ring

/-- Cochrane (2023), eqs. (3.1)–(3.2), p. 53: given bond pricing (3.1), the flow condition
(3.2) at date `t` is equivalent to the real recursion
`v_t = s_t + E_t[(Λ_{t+1}/Λ_t)v_{t+1}]` for the real market value `v` of the debt. -/
theorem flowLT_iff_recursion (hP : 𝔼.PullOut) {K : ℕ} {m P s : ℕ → Ω → ℝ}
    {Q B : ℕ → ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hK : MaxMaturity K B)
    (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P) (hP0 : ∀ s ξ, P s ξ ≠ 0) {t : ℕ}
    (hB1 : ∀ j, 𝔼.E t (B (t + 1) j) = B (t + 1) j) :
    FlowLT K P s Q B t ↔
      realValue K Q B P t = s t + 𝔼.E t (m t * realValue K Q B P (t + 1)) := by
  rw [flowLT_iff_value hK (zeroPrice_zero 𝔼 hQ (hP0 t)) (hP0 t),
    purchaseValue_real 𝔼 hP hm hQ hPa hP0 hB1]

/-- Cochrane (2023), eq. (3.3), p. 53: given (3.1), the real market value of debt is known at
its date when the holdings `B_{t−1}^{(t+j)}` are. -/
theorem realValue_adapted (hP : 𝔼.PullOut) {K : ℕ} {m P : ℕ → Ω → ℝ}
    {Q B : ℕ → ℕ → Ω → ℝ} (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (hBt : ∀ t j, 𝔼.E t (B t j) = B t j) :
    𝔼.Adapted (realValue K Q B P) := by
  intro t
  have hfun : realValue K Q B P t =
      ∑ j ∈ Finset.range (K + 1), B t j * realPrice 𝔼 m P t j := by
    funext ξ
    simp only [realValue, mktValue, Finset.sum_apply, Finset.sum_div, Pi.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← zeroPrice_real 𝔼 hP hQ (hPa t) j (hP0 t ξ)]
    ring
  rw [hfun, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hP t _ _ (hBt t j), realPrice, 𝔼.E_E_self]

/-- Cochrane (2023), eqs. (3.1)–(3.3), p. 53, and survey E28–E29: with a finite maximum
maturity, bond prices given by (3.1), a positive adapted price level, holdings known when
chosen, adapted surpluses with absolutely summable present values, and `E_t` with pull-out and
conditional monotone convergence, the flow condition (3.2) at every date plus the
transversality condition at every date hold iff the valuation equation (3.3)
`∑_j Q_t^{(t+j)}B_{t−1}^{(t+j)}/P_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` holds at every date. -/
theorem valuationLT_iff (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {K : ℕ}
    {m P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hsa : 𝔼.Adapted s) (hs : SurplusSummable 𝔼 m s)
    (hK : MaxMaturity K B) (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hP0 : ∀ s ξ, P s ξ ≠ 0) (hBt : ∀ t j, 𝔼.E t (B t j) = B t j)
    (hB1 : ∀ t j, 𝔼.E t (B (t + 1) j) = B (t + 1) j) :
    ((∀ t, FlowLT K P s Q B t) ∧ ∀ t, TVC 𝔼 m (realValue K Q B P) t) ↔
      ∀ t, realValue K Q B P t = pv 𝔼 m s t := by
  rw [← flow_tvc_iff_pv 𝔼 hMC hP hm hm0 hsa hs (realValue_adapted 𝔼 hP hQ hPa hP0 hBt)]
  have h : (∀ t, FlowLT K P s Q B t) ↔ FlowRec 𝔼 m s (realValue K Q B P) :=
    forall_congr' fun t => flowLT_iff_recursion 𝔼 hP hm hK hQ hPa hP0 (hB1 t)
  rw [h]

/-- Cochrane (2023), eq. (3.3), p. 53: with `m ≡ β` the present value is
`∑_n βⁿ E_t s_{t+n}`. -/
theorem pv_const (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) :
    pv 𝔼 (fun _ _ => β) s t = fun ξ => ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  funext ξ
  simp only [pv, sdf_const]
  refine tsum_congr fun n => ?_
  have h : ((fun _ => β ^ n) * s (t + n) : Ω → ℝ) = β ^ n • s (t + n) := by
    funext ξ'
    simp
  rw [h, map_smul, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eqs. (3.1)–(3.3), p. 53, exactly as printed (constant real rate,
`R = β⁻¹`, `0 ≤ β`): with a finite maximum maturity, (3.1) `Q_t^{(t+j)} = E_t[βʲP_t/P_{t+j}]`,
the flow (3.2) at every date and the transversality condition
`lim_N βᴺ E_t[v_{t+N}] = 0` at every date hold iff (3.3)
`∑_j Q_t^{(t+j)}B_{t−1}^{(t+j)}/P_t = ∑_n βⁿE_t s_{t+n}` at every date. -/
theorem valuationLT_iff_const (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {K : ℕ}
    {β : ℝ} (hβ : 0 ≤ β) {P s : ℕ → Ω → ℝ} {Q B : ℕ → ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hs : SurplusSummable 𝔼 (fun _ _ => β) s) (hK : MaxMaturity K B)
    (hQ : ∀ t j, Q t j = 𝔼.E t (fun ξ => β ^ j * (P t ξ / P (t + j) ξ)))
    (hPa : 𝔼.Adapted P) (hP0 : ∀ s ξ, P s ξ ≠ 0) (hBt : ∀ t j, 𝔼.E t (B t j) = B t j)
    (hB1 : ∀ t j, 𝔼.E t (B (t + 1) j) = B (t + 1) j) :
    ((∀ t, FlowLT K P s Q B t) ∧
        ∀ t ξ, Tendsto (fun N => β ^ N * 𝔼.E t (realValue K Q B P (t + N)) ξ) atTop (𝓝 0)) ↔
      ∀ t ξ, realValue K Q B P t ξ = ∑' n, β ^ n * 𝔼.E t (s (t + n)) ξ := by
  have hiff := valuationLT_iff 𝔼 hMC hP (m := fun _ _ => β) (fun s => 𝔼.const (s + 1) β)
    (fun _ _ => hβ) hsa hs hK ((zeroPrice_const_iff 𝔼 β P Q).mpr hQ) hPa hP0 hBt hB1
  have htvc : ∀ t, TVC 𝔼 (fun _ _ => β) (realValue K Q B P) t ↔
      ∀ ξ, Tendsto (fun N => β ^ N * 𝔼.E t (realValue K Q B P (t + N)) ξ) atTop (𝓝 0) := by
    intro t
    refine forall_congr' fun ξ => ?_
    have h : ∀ N, 𝔼.E t (sdf (fun _ _ => β) t N * realValue K Q B P (t + N)) ξ =
        β ^ N * 𝔼.E t (realValue K Q B P (t + N)) ξ := fun N => by
      have h' : (sdf (fun _ _ => β) t N * realValue K Q B P (t + N) : Ω → ℝ) =
          β ^ N • realValue K Q B P (t + N) := by
        rw [sdf_const]
        funext ξ'
        simp
      rw [h', map_smul, Pi.smul_apply, smul_eq_mul]
    simp_rw [h]
  simp_rw [← htvc, hiff, pv_const, funext_iff]

/-- Cochrane (2023), p. 53 (survey E28): "we can derive (3.2) from (3.3) by considering its
value at two adjacent dates" is false without the bond-pricing equation (3.1). Under perfect
foresight with `β = 1/2`, `P ≡ 1`, `s ≡ 1`, maximum maturity one, `B_{t−1}^{(t)} = 0`,
`B_{t−1}^{(t+1)} = 1`, and the price `Q_t^{(t+1)} = 2` (instead of `β = 1/2`), the valuation
equation (3.3) and the transversality condition hold at every date while the flow condition
(3.2) fails at every date. -/
theorem valuationLT_not_imp_flow :
    ∃ (P s : ℕ → Unit → ℝ) (Q B : ℕ → ℕ → Unit → ℝ),
      MaxMaturity 1 B ∧
      (∀ t, realValue 1 Q B P t = pv perfectForesight (fun _ _ => (1 / 2 : ℝ)) s t) ∧
      (∀ t, TVC perfectForesight (fun _ _ => (1 / 2 : ℝ)) (realValue 1 Q B P) t) ∧
      (∀ t, ¬ FlowLT 1 P s Q B t) ∧
      ¬ ZeroPrice perfectForesight (fun _ _ => (1 / 2 : ℝ)) P Q := by
  refine ⟨fun _ _ => 1, fun _ _ => 1, fun _ j _ => if j = 1 then 2 else (1 / 2) ^ j,
    fun _ j _ => if j = 1 then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro t j hj
    funext ξ
    simp only [show j ≠ 1 by omega, ↓reduceIte]
    rfl
  · intro t
    funext ξ
    rw [pv_const]
    simp only [realValue, mktValue, perfectForesight, LinearMap.id_apply, mul_one]
    rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    simp
    norm_num
  · intro t ξ
    have h : ∀ N, perfectForesight.E t (sdf (fun _ _ => (1 / 2 : ℝ)) t N *
        realValue 1 (fun _ j _ => if j = 1 then 2 else (1 / 2) ^ j)
          (fun _ j _ => if j = 1 then 1 else 0) (fun _ _ => 1) (t + N)) ξ =
        2 * (1 / 2) ^ N := fun N => by
      simp only [perfectForesight, LinearMap.id_apply, Pi.mul_apply, sdf_const, realValue,
        mktValue]
      simp
      ring
    simp_rw [h]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 2
  · intro t h
    have h1 := congrFun h ()
    simp [Finset.sum_range_succ] at h1
    norm_num at h1
  · intro h
    have h1 := congrFun (h 0 1) ()
    simp [perfectForesight] at h1
    norm_num at h1


/-! ### Geometric maturity structure (A1 §1.2.1) with genuine infinite sums -/

/-- Cochrane (2023), A1 §1.2.1, p. 559: the geometric maturity structure
`B_{t−1}^{(t+j)} = ωʲ b_t` (written `w` here, since `ω` names states), with `b_t = B_{t−1}`. -/
def geomDebt (w : ℝ) (b : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ := fun t j ξ => w ^ j * b t ξ

/-- Cochrane (2023), eq. (3.2), p. 53, with the geometric structure of A1 p. 559:
`b_t = P_ts_t + ∑_{j≥0} Q_t^{(t+j+1)}(ωʲ b_{t+1} − ω^{j+1} b_t)`. -/
def GeomFlow (w : ℝ) (P s b : ℕ → Ω → ℝ) (Q : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ξ, b t ξ = P t ξ * s t ξ +
    ∑' j, Q t (j + 1) ξ * (w ^ j * b (t + 1) ξ - w ^ (j + 1) * b t ξ)

/-- Cochrane (2023), A1 eq. (1.14), p. 559: the nominal value `∑_j ωʲ Q_t^{(t+j)}` of the
geometric portfolio per unit of `b_t`. -/
noncomputable def annuity (w : ℝ) (Q : ℕ → ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ξ => ∑' j, w ^ j * Q t j ξ

/-- Cochrane (2023), eq. (3.3), p. 53, with the geometric structure: the real market value
`∑_j Q_t^{(t+j)} ωʲ b_t/P_t` of the debt. -/
noncomputable def geomValue (w : ℝ) (Q : ℕ → ℕ → Ω → ℝ) (b P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ξ => annuity w Q t ξ * b t ξ / P t ξ

/-- Cochrane (2023), eq. (3.3), p. 53: the geometric real market value is
`∑_j Q_t^{(t+j)}B_{t−1}^{(t+j)}/P_t` with `B_{t−1}^{(t+j)} = ωʲb_t`. -/
theorem geomValue_eq_tsum (w : ℝ) (Q : ℕ → ℕ → Ω → ℝ) (b P : ℕ → Ω → ℝ) (t : ℕ) (ξ : Ω) :
    geomValue w Q b P t ξ = (∑' j, Q t j ξ * geomDebt w b t j ξ) / P t ξ := by
  simp only [geomValue, annuity, geomDebt]
  rw [← tsum_mul_right]
  congr 1
  exact tsum_congr fun j => by ring

/-- Cochrane (2023), A1 eq. (1.14), p. 559: the real value `∑_j ωʲ Q_t^{(t+j)}/P_t` of the
geometric portfolio per unit of `b_t`. -/
noncomputable def realAnnuity (w : ℝ) (m P : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ξ => ∑' j, w ^ j * realPrice 𝔼 m P t j ξ

/-- Cochrane (2023), eq. (3.1), p. 53, and A1 p. 559: with (3.1), the nominal annuity value
divided by `P_t` is the real annuity value. -/
theorem annuity_div (hP : 𝔼.PullOut) {w : ℝ} {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hQ : ZeroPrice 𝔼 m P Q) {t : ℕ} (hPa : 𝔼.E t (P t) = P t) {ξ : Ω} (hP0 : P t ξ ≠ 0) :
    annuity w Q t ξ / P t ξ = realAnnuity 𝔼 w m P t ξ := by
  simp only [annuity, realAnnuity]
  rw [← tsum_div_const]
  exact tsum_congr fun j => by
    rw [mul_div_assoc, zeroPrice_real 𝔼 hP hQ hPa j hP0]

/-- Cochrane (2023), eqs. (3.1)–(3.2), p. 53, geometric case (conditional monotone
convergence): the nominal value of the debt carried into `t + 1` per unit of `b_{t+1}`,
`∑_j ωʲ Q_t^{(t+j+1)}`, converges to `P_t E_t[(Λ_{t+1}/Λ_t) × (real annuity at t + 1)]`. -/
theorem hasSum_shift (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {w : ℝ} (hw : 0 ≤ w)
    {m P : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s)
    (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hPpos : ∀ s ξ, 0 < P s ξ) (hQs : ∀ t ξ, Summable fun j => w ^ j * Q t j ξ)
    (t : ℕ) (ξ : Ω) :
    HasSum (fun j => w ^ j * Q t (j + 1) ξ)
      (P t ξ * 𝔼.E t (m t * realAnnuity 𝔼 w m P (t + 1)) ξ) := by
  set f : ℕ → Ω → ℝ := fun j => m t * fun ξ' => w ^ j * realPrice 𝔼 m P (t + 1) j ξ' with hf
  have hf0 : ∀ j ξ', 0 ≤ f j ξ' := fun j ξ' =>
    mul_nonneg (hm0 t ξ') (mul_nonneg (pow_nonneg hw j)
      (realPrice_nonneg 𝔼 hm0 hPpos (t + 1) j ξ'))
  have hrp : ∀ ξ' j, w ^ j * realPrice 𝔼 m P (t + 1) j ξ' =
      w ^ j * Q (t + 1) j ξ' / P (t + 1) ξ' := fun ξ' j => by
    rw [mul_div_assoc, zeroPrice_real 𝔼 hP hQ (hPa (t + 1)) j (hPpos (t + 1) ξ').ne']
  have hfs : ∀ ξ', Summable fun j => f j ξ' := fun ξ' => by
    have h := ((hQs (t + 1) ξ').div_const (P (t + 1) ξ')).mul_left (m t ξ')
    refine h.congr fun j => ?_
    simp only [hf, Pi.mul_apply, hrp]
  have hMCf := hMC t f hf0 hfs ξ
  have hsum : (fun ξ' => ∑' j, f j ξ') = m t * realAnnuity 𝔼 w m P (t + 1) := by
    funext ξ'
    simp only [hf, Pi.mul_apply, realAnnuity, tsum_mul_left]
  rw [hsum] at hMCf
  have hterm : ∀ j, 𝔼.E t (f j) ξ = w ^ j * Q t (j + 1) ξ / P t ξ := fun j => by
    have h' : f j = w ^ j • (m t * realPrice 𝔼 m P (t + 1) j) := by
      funext ξ'
      simp only [hf, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [h', map_smul, ← realPrice_succ 𝔼 hP hm, Pi.smul_apply, smul_eq_mul,
      ← zeroPrice_real 𝔼 hP hQ (hPa t) (j + 1) (hPpos t ξ).ne']
    ring
  simp_rw [hterm] at hMCf
  convert hMCf.mul_left (P t ξ) using 1
  funext j
  have := (hPpos t ξ).ne'
  field_simp

/-- Cochrane (2023), eqs. (3.1)–(3.2), p. 53, with the geometric maturity structure of A1
p. 559: given (3.1), the flow condition at date `t` is equivalent to the real recursion
`v_t = s_t + E_t[(Λ_{t+1}/Λ_t)v_{t+1}]` for the real market value of the debt. -/
theorem geomFlow_iff_recursion (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {w : ℝ}
    (hw : 0 ≤ w) {m P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hQ : ZeroPrice 𝔼 m P Q)
    (hPa : 𝔼.Adapted P) (hPpos : ∀ s ξ, 0 < P s ξ)
    (hQs : ∀ t ξ, Summable fun j => w ^ j * Q t j ξ) {t : ℕ}
    (hb1 : 𝔼.E t (b (t + 1)) = b (t + 1)) :
    GeomFlow w P s b Q t ↔
      geomValue w Q b P t = s t + 𝔼.E t (m t * geomValue w Q b P (t + 1)) := by
  have hE : 𝔼.E t (m t * geomValue w Q b P (t + 1)) =
      b (t + 1) * 𝔼.E t (m t * realAnnuity 𝔼 w m P (t + 1)) := by
    rw [← hP t _ _ hb1]
    congr 1
    funext ξ
    simp only [Pi.mul_apply, geomValue]
    rw [mul_div_right_comm, annuity_div 𝔼 hP hQ (hPa (t + 1)) (hPpos (t + 1) ξ).ne']
    ring
  rw [hE]
  have key : ∀ ξ, (b t ξ = P t ξ * s t ξ +
      ∑' j, Q t (j + 1) ξ * (w ^ j * b (t + 1) ξ - w ^ (j + 1) * b t ξ)) ↔
      geomValue w Q b P t ξ =
        s t ξ + b (t + 1) ξ * 𝔼.E t (m t * realAnnuity 𝔼 w m P (t + 1)) ξ := by
    intro ξ
    set S := P t ξ * 𝔼.E t (m t * realAnnuity 𝔼 w m P (t + 1)) ξ with hS
    have hsh := hasSum_shift 𝔼 hMC hP hw hm hm0 hQ hPa hPpos hQs t ξ
    have h1 : HasSum (fun j => Q t (j + 1) ξ * (w ^ j * b (t + 1) ξ - w ^ (j + 1) * b t ξ))
        (b (t + 1) ξ * S - w * b t ξ * S) := by
      convert (hsh.mul_left (b (t + 1) ξ)).sub (hsh.mul_left (w * b t ξ)) using 1
      funext j
      ring
    have hann : annuity w Q t ξ = 1 + w * S := by
      simp only [annuity]
      rw [(hQs t ξ).tsum_eq_zero_add, zeroPrice_zero 𝔼 hQ (fun ξ' => (hPpos t ξ').ne'),
        show S = ∑' j, w ^ j * Q t (j + 1) ξ from hsh.tsum_eq.symm, ← tsum_mul_left]
      simp only [pow_zero, Pi.one_apply, one_mul]
      congr 1
      exact tsum_congr fun j => by ring
    have hP0 := (hPpos t ξ).ne'
    rw [h1.tsum_eq, geomValue, hann, hS]
    constructor
    · intro h
      field_simp
      linear_combination h
    · intro h
      field_simp at h
      linear_combination h
  constructor
  · intro h
    funext ξ
    exact (key ξ).mp (h ξ)
  · intro h ξ
    exact (key ξ).mpr (congrFun h ξ)

/-- Cochrane (2023), eq. (3.3), p. 53, geometric case: the real market value of the debt is
known at its date when `b_t` is. -/
theorem geomValue_adapted (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {w : ℝ}
    (hw : 0 ≤ w) {m P b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} (hm0 : ∀ s ξ, 0 ≤ m s ξ)
    (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P) (hPpos : ∀ s ξ, 0 < P s ξ)
    (hQs : ∀ t ξ, Summable fun j => w ^ j * Q t j ξ) (hb : 𝔼.Adapted b) :
    𝔼.Adapted (geomValue w Q b P) := by
  intro t
  have hfun : geomValue w Q b P t = b t * realAnnuity 𝔼 w m P t := by
    funext ξ
    simp only [geomValue, Pi.mul_apply]
    rw [mul_div_right_comm, annuity_div 𝔼 hP hQ (hPa t) (hPpos t ξ).ne', mul_comm]
  have hA : 𝔼.E t (realAnnuity 𝔼 w m P t) = realAnnuity 𝔼 w m P t := by
    set g : ℕ → Ω → ℝ := fun j ξ => w ^ j * realPrice 𝔼 m P t j ξ with hg
    have hg0 : ∀ j ξ, 0 ≤ g j ξ := fun j ξ =>
      mul_nonneg (pow_nonneg hw j) (realPrice_nonneg 𝔼 hm0 hPpos t j ξ)
    have hgs : ∀ ξ, Summable fun j => g j ξ := fun ξ => by
      refine ((hQs t ξ).div_const (P t ξ)).congr fun j => ?_
      simp only [hg]
      rw [mul_div_assoc, zeroPrice_real 𝔼 hP hQ (hPa t) j (hPpos t ξ).ne']
    funext ξ
    have h := hMC t g hg0 hgs ξ
    have hEg : ∀ j, 𝔼.E t (g j) ξ = g j ξ := fun j => by
      have h' : g j = w ^ j • realPrice 𝔼 m P t j := by
        funext ξ'
        simp [hg]
      rw [h', map_smul, realPrice, 𝔼.E_E_self]
    simp_rw [hEg] at h
    exact h.tsum_eq.symm
  rw [hfun, hP t _ _ (hb t), hA]

/-- Cochrane (2023), eqs. (3.1)–(3.3), p. 53, with the geometric maturity structure of A1
§1.2.1 (genuine infinite sums over maturities): given (3.1), the flow condition at every date
plus the transversality condition at every date hold iff the valuation equation
`∑_j Q_t^{(t+j)}ωʲb_t/P_t = ∑_n E_t[(Λ_{t+n}/Λ_t)s_{t+n}]` holds at every date. -/
theorem valuationGeom_iff (hMC : MonotoneConvergence 𝔼) (hP : 𝔼.PullOut) {w : ℝ}
    (hw : 0 ≤ w) {m P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hm : ∀ s, 𝔼.E (s + 1) (m s) = m s) (hm0 : ∀ s ξ, 0 ≤ m s ξ) (hsa : 𝔼.Adapted s)
    (hs : SurplusSummable 𝔼 m s) (hQ : ZeroPrice 𝔼 m P Q) (hPa : 𝔼.Adapted P)
    (hPpos : ∀ s ξ, 0 < P s ξ) (hQs : ∀ t ξ, Summable fun j => w ^ j * Q t j ξ)
    (hb : 𝔼.Adapted b) (hb1 : ∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) :
    ((∀ t, GeomFlow w P s b Q t) ∧ ∀ t, TVC 𝔼 m (geomValue w Q b P) t) ↔
      ∀ t, geomValue w Q b P t = pv 𝔼 m s t := by
  rw [← flow_tvc_iff_pv 𝔼 hMC hP hm hm0 hsa hs
    (geomValue_adapted 𝔼 hMC hP hw hm0 hQ hPa hPpos hQs hb)]
  have h : (∀ t, GeomFlow w P s b Q t) ↔ FlowRec 𝔼 m s (geomValue w Q b P) :=
    forall_congr' fun t => geomFlow_iff_recursion 𝔼 hMC hP hw hm hm0 hQ hPa hPpos hQs (hb1 t)
  rw [h]


/-! ### A1 §1.2.1: exact formulas for one-time interest-rate changes -/

/-- Cochrane (2023), A1 p. 559 ("the bond price is then `Q_t^{(t+j)} = 1/(1+i)ʲ`"): under
perfect foresight with (3.1) and a constant one-period rate `i`, the term structure is flat,
`Q_t^{(t+j)} = 1/(1+i)ʲ`. -/
theorem zeroPrice_pf_const_rate {m P : ℕ → Unit → ℝ} {Q : ℕ → ℕ → Unit → ℝ} {i : ℝ}
    (hQ : ZeroPrice perfectForesight m P Q) (hP0 : ∀ s ξ, P s ξ ≠ 0)
    (hi : ∀ s, Q s 1 = fun _ => (1 + i)⁻¹) (t j : ℕ) : Q t j = fun _ => ((1 + i) ^ j)⁻¹ := by
  rw [zeroPrice_pf_rates hQ hP0 (i := fun _ _ => i) hi t j]
  funext ξ
  rw [Finset.prod_const, Finset.card_range, inv_pow]

/-- Cochrane (2023), A1 (1.14), p. 559: for `0 ≤ ω < 1 + i`,
`∑_j ωʲ/(1+i)ʲ = (1+i)/(1+i−ω)`. -/
theorem geom_value {i w : ℝ} (hw : 0 ≤ w) (hwi : w < 1 + i) :
    HasSum (fun j : ℕ => w ^ j / (1 + i) ^ j) ((1 + i) / (1 + i - w)) := by
  have h1 : 0 < 1 + i := by linarith
  have h := hasSum_geometric_of_lt_one (div_nonneg hw h1.le) ((div_lt_one h1).mpr hwi)
  rw [one_sub_div h1.ne', inv_div] at h
  convert h using 1
  funext j
  rw [div_pow]

/-- Cochrane (2023), A1 (1.14), p. 559, right-hand side: with constant surpluses and
`β = 1/(1+r)`, `r > 0`, the present value is `∑_j βʲ s = (1+r)s/r`. -/
theorem pv_const_value {r : ℝ} (hr : 0 < r) (s : ℝ) :
    HasSum (fun j : ℕ => (1 / (1 + r)) ^ j * s) ((1 + r) / r * s) := by
  have h1 : 0 < 1 + r := by linarith
  have h := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ 1 / (1 + r))
    ((div_lt_one h1).mpr (by linarith))).mul_right s
  have hq : (1 - 1 / (1 + r))⁻¹ = (1 + r) / r := by
    rw [one_sub_div h1.ne', inv_div, add_sub_cancel_left]
  rwa [hq] at h

/-- Cochrane (2023), A1 eq. (1.14), p. 559: with a constant rate `i` (`Q_0^{(j)} = 1/(1+i)ʲ`),
geometric debt `B_{−1}^{(j)} = ωʲB_{−1}` and constant surpluses, the valuation equation
`∑_j Q_0^{(j)}ωʲB_{−1}/P_0 = ∑_j βʲ s`, `β = 1/(1+r)`, reads
`(1+i)/(1+i−ω) · B_{−1}/P_0 = (1+r)s/r`. -/
theorem valuation_1_14 {r i w : ℝ} (hr : 0 < r) (hw : 0 ≤ w) (hwi : w < 1 + i)
    (Bm P0 s : ℝ) :
    (∑' j : ℕ, ((1 + i) ^ j)⁻¹ * (w ^ j * Bm) / P0 = ∑' j : ℕ, (1 / (1 + r)) ^ j * s) ↔
      (1 + i) / (1 + i - w) * (Bm / P0) = (1 + r) / r * s := by
  rw [(pv_const_value hr s).tsum_eq]
  have h := ((geom_value hw hwi).mul_right (Bm / P0)).tsum_eq
  rw [← h]
  constructor <;> intro hh <;> rw [← hh] <;> exact tsum_congr fun j => by ring

/-- Cochrane (2023), A1 eq. (1.15), p. 559: in the steady state with `i = r`,
`(1+r)/(1+r−ω) · B/P = (1+r)s/r` iff `B/P = (1+r−ω)s/r`. -/
theorem steady_state_1_15 {r w : ℝ} (hr : 0 < r) (hwr : w < 1 + r) (B P s : ℝ) :
    (1 + r) / (1 + r - w) * (B / P) = (1 + r) / r * s ↔ B / P = (1 + r - w) * s / r := by
  have h1 : (1 + r - w) ≠ 0 := by linarith
  have h2 : (1 + r) ≠ 0 := by linarith
  constructor
  · intro h
    have e : B / P = (1 + r - w) / (1 + r) * ((1 + r) / (1 + r - w) * (B / P)) := by
      field_simp
    rw [e, h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Cochrane (2023), A1 eq. (1.16), p. 559: the price-level ratio
`P_0/P = (1+i)(1+r−ω)/((1+r)(1+i−ω))` after a permanent unexpected rate rise from `r` to
`i`. -/
noncomputable def jumpRatio (r i w : ℝ) : ℝ := (1 + i) * (1 + r - w) / ((1 + r) * (1 + i - w))

/-- Cochrane (2023), A1 eqs. (1.14)–(1.16), p. 559: if the steady-state valuation (1.15) held
at `P` and the valuation (1.14) at the new rate `i` holds at `P_0` (same `B`, same constant
surplus `s ≠ 0`), then `P_0/P = (1+i)(1+r−ω)/((1+r)(1+i−ω))`. -/
theorem price_jump_perm {r i w B P P0 s : ℝ} (hr : 0 < r) (hw : 0 ≤ w) (hwr : w < 1 + r)
    (hwi : w < 1 + i) (hs : s ≠ 0) (hP : P ≠ 0) (hP0 : P0 ≠ 0)
    (h14 : (1 + i) / (1 + i - w) * (B / P0) = (1 + r) / r * s)
    (h15 : (1 + r) / (1 + r - w) * (B / P) = (1 + r) / r * s) :
    P0 / P = jumpRatio r i w := by
  have h1 : (1 + r - w) ≠ 0 := by linarith
  have h2 : (1 + i - w) ≠ 0 := by linarith
  have h3 : (1 + r) ≠ 0 := by linarith
  have hr0 : r ≠ 0 := hr.ne'
  have e15 : B / P = (1 + r - w) * s / r := (steady_state_1_15 hr hwr B P s).mp h15
  have e14 : B / P0 = (1 + r) * (1 + i - w) * s / ((1 + i) * r) := by
    have hi0 : (1 + i) ≠ 0 := by linarith
    have e : B / P0 = (1 + i - w) / (1 + i) * ((1 + i) / (1 + i - w) * (B / P0)) := by
      field_simp
    rw [e, h14]
    field_simp
  have hB : B ≠ 0 := by
    rintro rfl
    rw [zero_div, eq_comm, div_eq_zero_iff] at e15
    rcases e15 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h1 h'
      · exact hs h'
    · exact hr0 h
  have hratio : P0 / P = (B / P) / (B / P0) := by field_simp
  have hi0 : (1 + i) ≠ 0 := by linarith
  rw [hratio, e15, e14, jumpRatio]
  field_simp

/-- Cochrane (2023), A1 (1.14)–(1.16), p. 559, general form (no sign conditions; any common
right-hand side `s`, e.g. the present value of surpluses): the valuation equations before
((1.15)) and after ((1.14)) the permanent rise, with the same debt, give `P_0/P = jumpRatio`.
`price_jump_perm` is the case `s = (1+r)s₀/r`. -/
theorem price_jump_of_valuation {r i w B P P0 s : ℝ} (hB : B ≠ 0) (hP : P ≠ 0) (hP0 : P0 ≠ 0)
    (hr : 1 + r ≠ 0) (hri : 1 + r - w ≠ 0) (hii : 1 + i - w ≠ 0)
    (h14 : (1 + i) / (1 + i - w) * (B / P0) = s) (h15 : (1 + r) / (1 + r - w) * (B / P) = s) :
    P0 / P = jumpRatio r i w := by
  rw [← h15] at h14
  unfold jumpRatio
  field_simp at h14 ⊢
  linear_combination -h14

/-- Cochrane (2023), A1 eq. (1.16), p. 559: `P_0/P − 1 = −ω(i−r)/((1+r)(1+i−ω))`. -/
theorem jumpRatio_sub_one {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i) :
    jumpRatio r i w - 1 = -(w * (i - r) / ((1 + r) * (1 + i - w))) := by
  have h2 : (1 + i - w) ≠ 0 := by linarith
  have h3 : (1 + r) ≠ 0 := by linarith
  unfold jumpRatio
  field_simp
  ring

/-- Cochrane (2023), A1 eq. (1.16), p. 559, and §3.1, p. 53 ("a rise in nominal interest rates
with no change in surpluses … can result in a lower price level"): for `0 ≤ ω < 1 + r` and
`ω < 1 + i`, the price level jumps down, `P_0 < P`, iff the rate rises (`i > r`) and there is
long-term debt (`ω > 0`). -/
theorem price_jump_lt_one_iff {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i) :
    jumpRatio r i w < 1 ↔ 0 < w ∧ r < i := by
  rw [← sub_neg, jumpRatio_sub_one hw hwr hwi, neg_neg_iff_pos]
  have hd : 0 < (1 + r) * (1 + i - w) := mul_pos (by linarith) (by linarith)
  rw [div_pos_iff_of_pos_right hd]
  constructor
  · intro h
    rcases hw.lt_or_eq with hw' | hw'
    · exact ⟨hw', by nlinarith⟩
    · rw [← hw'] at h
      simp at h
  · rintro ⟨h1, h2⟩
    exact mul_pos h1 (by linarith)

/-- Cochrane (2023), A1 p. 560: with one-period debt (`ω = 0`) there is no jump, `P_0 = P`. -/
theorem price_jump_omega_zero {r i : ℝ} (hr : 0 < 1 + r) (hi : 0 < 1 + i) :
    jumpRatio r i 0 = 1 := by
  unfold jumpRatio
  rw [sub_zero, sub_zero, mul_comm (1 + i)]
  exact div_self (mul_ne_zero hr.ne' hi.ne')

/-- Cochrane (2023), A1 eq. (1.16), p. 559: with long-term debt a rate cut (`i < r`) raises
the price level, `P_0 > P`. -/
theorem price_jump_gt_one {r i w : ℝ} (hw : 0 < w) (hwr : w < 1 + r) (hwi : w < 1 + i)
    (hir : i < r) : 1 < jumpRatio r i w := by
  rw [← sub_pos, jumpRatio_sub_one hw.le hwr hwi, neg_pos]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hw (by linarith))
    (mul_pos (by linarith) (by linarith))

/-- Cochrane (2023), A1 eq. (1.16), p. 559: the jump is larger with longer debt: for `i > r`,
`P_0/P` is strictly decreasing in `ω` on `[0, 1 + r)`. -/
theorem jumpRatio_strictAntiOn_omega {r i : ℝ} (hr : 0 < 1 + r) (hir : r < i) :
    StrictAntiOn (fun w => jumpRatio r i w) (Set.Ico 0 (1 + r)) := by
  intro w1 hw1 w2 hw2 h12
  simp only
  have hw1i : w1 < 1 + i := by linarith [hw1.2]
  have hw2i : w2 < 1 + i := by linarith [hw2.2]
  rw [← sub_lt_sub_iff_right 1, jumpRatio_sub_one hw1.1 hw1.2 hw1i,
    jumpRatio_sub_one hw2.1 hw2.2 hw2i, neg_lt_neg_iff,
    div_lt_div_iff₀ (mul_pos hr (by linarith)) (mul_pos hr (by linarith))]
  have key : w2 * (i - r) * ((1 + r) * (1 + i - w1)) - w1 * (i - r) * ((1 + r) * (1 + i - w2)) =
      (i - r) * (1 + r) * (1 + i) * (w2 - w1) := by ring
  have hpos : 0 < (i - r) * (1 + r) * (1 + i) * (w2 - w1) :=
    mul_pos (mul_pos (mul_pos (by linarith) hr) (by linarith)) (by linarith)
  linarith

/-- Cochrane (2023), A1 eq. (1.19), p. 560: for a perpetuity (`ω = 1`),
`P_0 = (1+i)r/((1+r)i) · P`. -/
theorem price_jump_perpetuity (r i : ℝ) :
    jumpRatio r i 1 = (1 + i) * r / ((1 + r) * i) := by
  unfold jumpRatio
  ring_nf

/-- Cochrane (2023), A1 p. 560 ("a rise in interest rates from `r = 3%` to `i = 4%` occasions a
25% price level drop"): in discrete time, (1.19) gives `P_0/P = 78/103`, a drop of
`25/103 ≈ 24.27%`; the exact 25% is the continuous-time (1.20) value `r/i = 3/4`. -/
theorem perpetuity_example :
    jumpRatio 0.03 0.04 1 = 78 / 103 ∧ 1 - jumpRatio 0.03 0.04 1 = 25 / 103 ∧
      (0.2427 : ℝ) < 25 / 103 ∧ (25 / 103 : ℝ) < 0.2428 ∧ (1 : ℝ) - 0.03 / 0.04 = 0.25 := by
  unfold jumpRatio
  norm_num

/-- Cochrane (2023), A1 p. 560 ("with `ω = 0.8`, the permanent interest-rate rise graphed in
Figure 3.1 leads to a 3.5% price level drop"), survey E15: at the figure's rates `r = 2%`,
`i = 3%`, the exact (1.16) gives `P_0/P = 1133/1173`, a drop of `40/1173 ≈ 3.41%`, not 3.5%. -/
theorem omega_08_example :
    jumpRatio 0.02 0.03 0.8 = 1133 / 1173 ∧ 1 - jumpRatio 0.02 0.03 0.8 = 40 / 1173 ∧
      (0.0341 : ℝ) < 40 / 1173 ∧ (40 / 1173 : ℝ) < 0.0342 := by
  unfold jumpRatio
  norm_num

/-! ### Forward guidance (A1 p. 560) -/

/-- Cochrane (2023), A1 p. 560: zero-coupon prices when the rate is `r` before `T` and `i` from
`T` on: `Q_0^{(j)} = 1/(1+r)ʲ` for `j ≤ T` and `1/((1+r)^T(1+i)^{j−T})` for `j > T`. -/
noncomputable def fgPrice (r i : ℝ) (T j : ℕ) : ℝ :=
  if j ≤ T then ((1 + r) ^ j)⁻¹ else ((1 + r) ^ T)⁻¹ * ((1 + i) ^ (j - T))⁻¹

/-- Cochrane (2023), A1 p. 560: `fgPrice` is the term structure `∏_{k<j} 1/(1+i_k)` of the
announced path `i_k = r` for `k < T`, `i_k = i` for `k ≥ T` (cf. `zeroPrice_pf_rates`). -/
theorem fgPrice_eq_prod (r i : ℝ) (T j : ℕ) :
    fgPrice r i T j = ∏ k ∈ Finset.range j, (1 + if k < T then r else i)⁻¹ := by
  unfold fgPrice
  split_ifs with hj
  · rw [Finset.prod_congr rfl (g := fun _ => (1 + r)⁻¹) fun k hk => by
      rw [Finset.mem_range] at hk
      simp only [show k < T by omega, ↓reduceIte], Finset.prod_const, Finset.card_range,
      inv_pow]
  · obtain ⟨d, rfl⟩ : ∃ d, j = T + d := ⟨j - T, by omega⟩
    rw [Finset.prod_range_add, show T + d - T = d by omega]
    rw [Finset.prod_congr rfl (s₁ := Finset.range T) (g := fun _ => (1 + r)⁻¹) fun k hk => by
      rw [Finset.mem_range] at hk
      simp only [hk, ↓reduceIte], Finset.prod_const, Finset.card_range, inv_pow]
    rw [Finset.prod_congr rfl (s₁ := Finset.range d) (g := fun _ => (1 + i)⁻¹) fun k _ => by
      simp only [show ¬ T + k < T by omega, ↓reduceIte], Finset.prod_const, Finset.card_range,
      inv_pow]

/-- Cochrane (2023), A1 p. 560: the value of the geometric portfolio under forward guidance,
`∑_{j≤T} ωʲ/(1+r)ʲ + ∑_{j>T} ω^T/(1+r)^T · ω^{j−T}/(1+i)^{j−T}
= (1 − a^{T+1})/(1 − a) + a^T c/(1 − c)` with `a = ω/(1+r)`, `c = ω/(1+i)`. -/
theorem fg_value {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i) (T : ℕ) :
    HasSum (fun j => w ^ j * fgPrice r i T j)
      ((1 - (w / (1 + r)) ^ (T + 1)) / (1 - w / (1 + r)) +
        (w / (1 + r)) ^ T * ((w / (1 + i)) / (1 - w / (1 + i)))) := by
  have hr1 : 0 < 1 + r := by linarith
  have hi1 : 0 < 1 + i := by linarith
  set a := w / (1 + r) with ha
  set c := w / (1 + i) with hc
  have ha1 : a < 1 := (div_lt_one hr1).mpr hwr
  have hc0 : 0 ≤ c := div_nonneg hw hi1.le
  have hc1 : c < 1 := (div_lt_one hi1).mpr hwi
  rw [← hasSum_nat_add_iff' (T + 1)]
  have hhead : ∑ j ∈ Finset.range (T + 1), w ^ j * fgPrice r i T j =
      (1 - a ^ (T + 1)) / (1 - a) := by
    have he : (1 - a ^ (T + 1)) / (1 - a) = (a ^ (T + 1) - 1) / (a - 1) := by
      rw [← neg_sub, ← neg_sub a, neg_div_neg_eq]
    rw [he, ← geom_sum_eq ha1.ne]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [fgPrice, show j ≤ T by omega, ↓reduceIte, ha, div_eq_mul_inv, mul_pow, inv_pow]
  rw [hhead, add_sub_cancel_left]
  have hgeo := ((hasSum_geometric_of_lt_one hc0 hc1).mul_left (a ^ T * c))
  convert hgeo using 1
  · funext k
    simp only [fgPrice, show ¬ k + (T + 1) ≤ T by omega, ↓reduceIte,
      show k + (T + 1) - T = k + 1 by omega, ha, hc, div_pow]
    field_simp
    ring
  · rw [mul_assoc, div_eq_mul_inv]

/-- Cochrane (2023), A1 p. 560 (forward-guidance display and "with a bit of algebra"): if the
steady-state valuation `(1+r)/(1+r−ω) · B/P = V` held and, after the announcement at `0` that
the rate rises from `r` to `i` at `T`, the valuation `(fg value) · B/P_0 = V` holds (same `B`,
`V ≠ 0`), then `P_0/P − 1 = (ω/(1+r))^T [(1+i)(1+r−ω)/((1+r)(1+i−ω)) − 1]`, generalising
(1.16) (the case `T = 0`). -/
theorem price_jump_fg {r i w B P P0 V : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i)
    (T : ℕ) (hV : V ≠ 0) (hP : P ≠ 0) (hP0 : P0 ≠ 0)
    (hfg : (∑' j, w ^ j * fgPrice r i T j) * (B / P0) = V)
    (hss : (1 + r) / (1 + r - w) * (B / P) = V) :
    P0 / P - 1 = (w / (1 + r)) ^ T * (jumpRatio r i w - 1) := by
  have hr1 : 0 < 1 + r := by linarith
  have hi1 : 0 < 1 + i := by linarith
  have h1 : (1 + r - w) ≠ 0 := by linarith
  have h2 : (1 + i - w) ≠ 0 := by linarith
  have hr0 : (1 + r) ≠ 0 := hr1.ne'
  have hi0 : (1 + i) ≠ 0 := hi1.ne'
  rw [(fg_value hw hwr hwi T).tsum_eq] at hfg
  set a := w / (1 + r) with ha
  set c := w / (1 + i) with hc
  have ha1 : 1 - a ≠ 0 := by
    rw [ha, one_sub_div hr0]; exact div_ne_zero h1 hr0
  have hc1 : 1 - c ≠ 0 := by
    rw [hc, one_sub_div hi0]; exact div_ne_zero h2 hi0
  set S := (1 - a ^ (T + 1)) / (1 - a) + a ^ T * (c / (1 - c)) with hS
  have hS0 : S ≠ 0 := by
    intro h
    rw [h, zero_mul] at hfg
    exact hV hfg.symm
  have hB : B ≠ 0 := by
    rintro rfl
    rw [zero_div, mul_zero] at hss
    exact hV hss.symm
  have hBP : B / P = V * (1 - a) := by
    rw [← hss, ha, one_sub_div hr0]
    field_simp
  have hBP0 : B / P0 = V / S := by
    rw [← hfg]
    field_simp
  have hratio : P0 / P = S * (1 - a) := by
    have e : P0 / P = (B / P) / (B / P0) := by field_simp
    rw [e, hBP, hBP0]
    field_simp
  have hj : jumpRatio r i w = (1 - a) / (1 - c) := by
    rw [jumpRatio, ha, hc, one_sub_div hr0, one_sub_div hi0]
    field_simp
  rw [hratio, hj, hS]
  field_simp
  ring

/-- Cochrane (2023), A1 p. 560–561: the forward-guidance price-level drop
`1 − P_0/P = (ω/(1+r))^T · ω(i−r)/((1+r)(1+i−ω))`. -/
noncomputable def fgDrop (r i w : ℝ) (T : ℕ) : ℝ :=
  (w / (1 + r)) ^ T * (w * (i - r) / ((1 + r) * (1 + i - w)))

/-- Cochrane (2023), A1 p. 560: `(ω/(1+r))^T [(1.16) − 1] = −fgDrop`. -/
theorem fg_eq_neg_drop {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hwi : w < 1 + i) (T : ℕ) :
    (w / (1 + r)) ^ T * (jumpRatio r i w - 1) = -fgDrop r i w T := by
  rw [jumpRatio_sub_one hw hwr hwi, fgDrop]
  ring

/-- Cochrane (2023), A1 p. 561 ("As `T → ∞`, the downward price-level jump goes to zero"). -/
theorem fg_tendsto_zero {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) :
    Tendsto (fun T : ℕ => (w / (1 + r)) ^ T * (jumpRatio r i w - 1)) atTop (𝓝 0) := by
  have hr1 : 0 < 1 + r := by linarith
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hw hr1.le)
    ((div_lt_one hr1).mpr hwr)).mul_const (jumpRatio r i w - 1)

/-- Cochrane (2023), A1 p. 561 ("The price level `P_0` still jumps – forward guidance works"):
with long-term debt (`0 < ω < 1 + r`) and a rise `i > r` announced for any date `T`, the price
level jumps down on announcement. -/
theorem fg_drop_pos {r i w : ℝ} (hw : 0 < w) (hwr : w < 1 + r) (hri : r < i) (T : ℕ) :
    0 < fgDrop r i w T := by
  have hr1 : 0 < 1 + r := by linarith
  exact mul_pos (pow_pos (div_pos hw hr1) T)
    (div_pos (mul_pos hw (by linarith)) (mul_pos hr1 (by linarith)))

/-- Cochrane (2023), A1 p. 561 ("Longer `T` … give a smaller price-level jump"): for `i ≥ r`
the drop is antitone in the announcement horizon `T`. -/
theorem fg_drop_antitone_T {r i w : ℝ} (hw : 0 ≤ w) (hwr : w < 1 + r) (hri : r ≤ i) :
    Antitone (fun T => fgDrop r i w T) := by
  have hr1 : 0 < 1 + r := by linarith
  have hk : 0 ≤ w * (i - r) / ((1 + r) * (1 + i - w)) :=
    div_nonneg (mul_nonneg hw (by linarith)) (mul_pos hr1 (by linarith)).le
  intro T1 T2 h
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (div_nonneg hw hr1.le)
    ((div_le_one hr1).mpr hwr.le) h) hk

/-- Cochrane (2023), A1 p. 561: for `0 < ω` and `i > r` the drop is strictly decreasing in
`T`. -/
theorem fg_drop_strictAnti_T {r i w : ℝ} (hw : 0 < w) (hwr : w < 1 + r) (hri : r < i) :
    StrictAnti (fun T => fgDrop r i w T) := by
  have hr1 : 0 < 1 + r := by linarith
  have hk : 0 < w * (i - r) / ((1 + r) * (1 + i - w)) :=
    div_pos (mul_pos hw (by linarith)) (mul_pos hr1 (by linarith))
  intro T1 T2 h
  exact mul_lt_mul_of_pos_right (pow_lt_pow_right_of_lt_one₀ (div_pos hw hr1)
    ((div_lt_one hr1).mpr hwr) h) hk

/-- Cochrane (2023), A1 p. 561 ("shorter maturity structures — lower ω — give a smaller
price-level jump"): for `i > r` the drop is strictly increasing in `ω` on `[0, 1 + r)`. -/
theorem fg_drop_strictMonoOn_omega {r i : ℝ} (hr : 0 < 1 + r) (hri : r < i) (T : ℕ) :
    StrictMonoOn (fun w => fgDrop r i w T) (Set.Ico 0 (1 + r)) := by
  intro w1 hw1 w2 hw2 h12
  simp only [fgDrop]
  have hw2p : 0 < w2 := lt_of_le_of_lt hw1.1 h12
  have hd1 : 0 < (1 + r) * (1 + i - w1) := mul_pos hr (by linarith [hw1.2])
  have hd2 : 0 < (1 + r) * (1 + i - w2) := mul_pos hr (by linarith [hw2.2])
  have hg : w1 * (i - r) / ((1 + r) * (1 + i - w1)) < w2 * (i - r) / ((1 + r) * (1 + i - w2)) := by
    rw [div_lt_div_iff₀ hd1 hd2]
    have key : w2 * (i - r) * ((1 + r) * (1 + i - w1)) -
        w1 * (i - r) * ((1 + r) * (1 + i - w2)) = (i - r) * (1 + r) * (1 + i) * (w2 - w1) := by
      ring
    have hpos : 0 < (i - r) * (1 + r) * (1 + i) * (w2 - w1) :=
      mul_pos (mul_pos (mul_pos (by linarith) hr) (by linarith [hw2.2])) (by linarith)
    linarith
  have hg1 : 0 ≤ w1 * (i - r) / ((1 + r) * (1 + i - w1)) :=
    div_nonneg (mul_nonneg hw1.1 (by linarith)) hd1.le
  have hp : (w1 / (1 + r)) ^ T ≤ (w2 / (1 + r)) ^ T :=
    pow_le_pow_left₀ (div_nonneg hw1.1 hr.le) (div_le_div_of_nonneg_right h12.le hr.le) T
  calc (w1 / (1 + r)) ^ T * (w1 * (i - r) / ((1 + r) * (1 + i - w1)))
      ≤ (w2 / (1 + r)) ^ T * (w1 * (i - r) / ((1 + r) * (1 + i - w1))) :=
        mul_le_mul_of_nonneg_right hp hg1
    _ < (w2 / (1 + r)) ^ T * (w2 * (i - r) / ((1 + r) * (1 + i - w2))) :=
        mul_lt_mul_of_pos_left hg (pow_pos (div_pos hw2p hr) T)

/-! ### Transitory rate rises (A1 p. 560) -/

/-- Cochrane (2023), A1 p. 560 ("monetary policy changes in interest rates are not permanent
… each factor reducing the size of the effect"): a pointwise lower path of one-period rates
`i'_k ≤ i_k` (with `1 + i'_k > 0`) gives a weakly higher value
`∑_j ωʲ∏_{k<j}(1+i_k)⁻¹` of the geometric portfolio. -/
theorem annuity_mono_rates {w : ℝ} (hw : 0 ≤ w) {i i' : ℕ → ℝ} (hi' : ∀ k, 0 < 1 + i' k)
    (hle : ∀ k, i' k ≤ i k)
    (hs' : Summable fun j => w ^ j * ∏ k ∈ Finset.range j, (1 + i' k)⁻¹) :
    ∑' j, w ^ j * ∏ k ∈ Finset.range j, (1 + i k)⁻¹ ≤
      ∑' j, w ^ j * ∏ k ∈ Finset.range j, (1 + i' k)⁻¹ := by
  have hpos : ∀ k, 0 < 1 + i k := fun k => lt_of_lt_of_le (hi' k) (by linarith [hle k])
  have hterm : ∀ j, w ^ j * ∏ k ∈ Finset.range j, (1 + i k)⁻¹ ≤
      w ^ j * ∏ k ∈ Finset.range j, (1 + i' k)⁻¹ := fun j =>
    mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun k _ => (inv_pos.mpr (hpos k)).le)
      (fun k _ => (inv_le_inv₀ (hpos k) (hi' k)).mpr (by linarith [hle k]))) (pow_nonneg hw j)
  have h0 : ∀ j, 0 ≤ w ^ j * ∏ k ∈ Finset.range j, (1 + i k)⁻¹ := fun j =>
    mul_nonneg (pow_nonneg hw j) (Finset.prod_nonneg fun k _ => (inv_pos.mpr (hpos k)).le)
  exact Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le h0 hterm hs') hs'

/-- Cochrane (2023), A1 p. 560: with the same debt `B > 0` and the same positive present value
of surpluses `V`, a higher portfolio value per unit of debt `A ≤ A'` in the valuation equation
`A · B/P_0 = V` means a higher price level, `P_0 ≤ P_0'`. -/
theorem price_le_of_annuity_le {A A' B V P0 P0' : ℝ} (hA : 0 < A) (hAA : A ≤ A') (hB : 0 < B)
    (hP0 : 0 < P0) (hP0' : 0 < P0') (h : A * (B / P0) = V) (h' : A' * (B / P0') = V) :
    P0 ≤ P0' := by
  have e : A * (B / P0) = A' * (B / P0') := h.trans h'.symm
  rw [mul_div_assoc', mul_div_assoc', div_eq_div_iff hP0.ne' hP0'.ne'] at e
  by_contra hlt
  push Not at hlt
  have h1 : A * B * P0' < A' * B * P0 := by
    have hAB : 0 < A * B := mul_pos hA hB
    calc A * B * P0' < A * B * P0 := mul_lt_mul_of_pos_left hlt hAB
      _ ≤ A' * B * P0 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAA hB.le) hP0.le
  linarith

/-- Cochrane (2023), A1 p. 560 ("A mean-reverting interest-rate rise has a smaller effect
still"): the mean-reverting path `i_k = r + (i − r)φᵏ`, `0 ≤ φ ≤ 1`, `r ≤ i`, lies below the
permanent rise `i`, so (by `annuity_mono_rates` and `price_le_of_annuity_le`) its price-level
drop is no larger. -/
theorem meanReverting_le_perm {r i φ : ℝ} (hri : r ≤ i) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) (k : ℕ) :
    r ≤ r + (i - r) * φ ^ k ∧ r + (i - r) * φ ^ k ≤ i := by
  have h1 : 0 ≤ φ ^ k := pow_nonneg hφ0 k
  have h2 : φ ^ k ≤ 1 := pow_le_one₀ hφ0 hφ1
  constructor <;> nlinarith

/-! ### Roll-over of a geometric maturity structure (A1 p. 561) -/

/-- Cochrane (2023), A1 p. 561: bond sales under the geometric structure,
`B_t^{(t+j)} − B_{t−1}^{(t+j)} = ω^{j−1}b_{t+1} − ωʲb_t` (here with `j + 1` for `j`). -/
theorem geom_rollover (w : ℝ) (b : ℕ → Ω → ℝ) (t j : ℕ) (ξ : Ω) :
    geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ = w ^ j * b (t + 1) ξ -
      w ^ (j + 1) * b t ξ := rfl

/-- Cochrane (2023), A1 p. 561: to maintain a steady state `b_{t+1} = b_t = B`, the government
sells `ω^{j−1}(1−ω)B = ((1−ω)/ω) B_{t−1}^{(t+j)}` of each maturity (`ω ≠ 0`). -/
theorem geom_rollover_steady {w : ℝ} (hw : w ≠ 0) {b : ℕ → Ω → ℝ} {t : ℕ} {ξ : Ω}
    (hb : b (t + 1) ξ = b t ξ) (j : ℕ) :
    geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ = w ^ j * (1 - w) * b t ξ ∧
      geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ =
        (1 - w) / w * geomDebt w b t (j + 1) ξ := by
  rw [geom_rollover, hb]
  simp only [geomDebt]
  constructor
  · ring
  · field_simp
    ring

/-- Cochrane (2023), A1 pp. 559 and 561: in the steady state (constant `P`, `B`, rate `r > 0`,
so `Q^{(j)} = 1/(1+r)ʲ`), the geometric flow condition
`B = Ps + ∑_j Q^{(j+1)}(ωʲB − ω^{j+1}B)` (the roll-over of p. 561) holds iff the steady-state
valuation (1.15) `(1+r)/(1+r−ω) · B/P = (1+r)s/r` holds. -/
theorem steady_flow_iff_1_15 {r w : ℝ} (hr : 0 < r) (hw : 0 ≤ w) (hwr : w < 1 + r)
    {B P s : ℝ} (hP : P ≠ 0) :
    B = P * s + ∑' j : ℕ, ((1 + r) ^ (j + 1))⁻¹ * (w ^ j * B - w ^ (j + 1) * B) ↔
      (1 + r) / (1 + r - w) * (B / P) = (1 + r) / r * s := by
  have hr1 : 0 < 1 + r := by linarith
  have h1 : (1 + r - w) ≠ 0 := by linarith
  have hsum : ∑' j : ℕ, ((1 + r) ^ (j + 1))⁻¹ * (w ^ j * B - w ^ (j + 1) * B) =
      (1 - w) * B / (1 + r - w) := by
    have h := ((geom_value (i := r) hw hwr).mul_left ((1 - w) * B / (1 + r))).tsum_eq
    rw [← show (1 - w) * B / (1 + r) * ((1 + r) / (1 + r - w)) = (1 - w) * B / (1 + r - w) by
      field_simp, ← h]
    refine tsum_congr fun j => ?_
    rw [pow_succ]
    field_simp
    ring
  rw [hsum]
  have hr0 : r ≠ 0 := hr.ne'
  have hr1' : (1 + r) ≠ 0 := hr1.ne'
  rw [steady_state_1_15 hr hwr B P s]
  constructor
  · intro h
    have e : B * r = (1 + r - w) * s * P := by
      have h' : B * (1 + r - w) = P * s * (1 + r - w) + (1 - w) * B := by
        rw [div_eq_mul_inv] at h
        calc B * (1 + r - w) = (P * s + (1 - w) * B * (1 + r - w)⁻¹) * (1 + r - w) := by
              rw [← h]
          _ = P * s * (1 + r - w) + (1 - w) * B := by field_simp
      linear_combination h'
    rw [div_eq_div_iff hP hr0]
    linear_combination e
  · intro h
    rw [div_eq_div_iff hP hr0] at h
    have e : P * s = r * B / (1 + r - w) := by
      rw [eq_div_iff h1]
      linear_combination -h
    rw [e, ← add_div, eq_div_iff h1]
    ring

/-! ### When a geometric maturity structure needs tending (A1 p. 561) -/

/-- Cochrane (2023), A1 p. 561: under the geometric structure the net issuance of each
maturity is `B_t^{(t+j+1)} − B_{t−1}^{(t+j+1)} = ωʲ(b_{t+1} − ωb_t)`. -/
theorem geom_issuance (w : ℝ) (b : ℕ → Ω → ℝ) (t j : ℕ) (ξ : Ω) :
    geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ = w ^ j * (b (t + 1) ξ - w * b t ξ) := by
  simp only [geomDebt]
  ring

/-- Cochrane (2023), A1 p. 561 ("needs tending"): the government never trades, neither issuing
nor repurchasing any outstanding maturity, `B_t^{(t+j)} = B_{t−1}^{(t+j)}` for all `j ≥ 1`;
maturing debt is paid off from surpluses alone. -/
def NoTrade (B : ℕ → ℕ → Ω → ℝ) : Prop := ∀ t j ξ, B (t + 1) j ξ = B t (j + 1) ξ

/-- Cochrane (2023), A1 p. 561: the geometric structure is preserved with no trading iff the
face value shrinks geometrically, `b_{t+1} = ωb_t`. -/
theorem geom_noTrade_iff (w : ℝ) (b : ℕ → Ω → ℝ) :
    NoTrade (geomDebt w b) ↔ ∀ t ξ, b (t + 1) ξ = w * b t ξ := by
  constructor
  · intro h t ξ
    have := h t 0 ξ
    simpa [geomDebt] using this
  · intro h t j ξ
    simp only [geomDebt, h t ξ]
    ring

/-- Cochrane (2023), A1 p. 561: no trading means `b_t = ωᵗ b_0` at every date. -/
theorem geom_noTrade_iff_path (w : ℝ) (b : ℕ → Ω → ℝ) :
    NoTrade (geomDebt w b) ↔ ∀ t ξ, b t ξ = w ^ t * b 0 ξ := by
  rw [geom_noTrade_iff]
  constructor
  · intro h t ξ
    induction t with
    | zero => simp
    | succ t ih => rw [h t ξ, ih, pow_succ]; ring
  · intro h t ξ
    rw [h (t + 1) ξ, h t ξ, pow_succ]
    ring

/-- Cochrane (2023), eq. (3.2), p. 53, geometric case: the flow condition reads
`b_t = P_ts_t + (b_{t+1} − ωb_t)∑_j ωʲQ_t^{(t+j+1)}`. -/
theorem geomFlow_iff_issuance {w : ℝ} {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ} {t : ℕ} :
    GeomFlow w P s b Q t ↔ ∀ ξ, b t ξ = P t ξ * s t ξ +
      (b (t + 1) ξ - w * b t ξ) * ∑' j, w ^ j * Q t (j + 1) ξ := by
  refine forall_congr' fun ξ => ?_
  rw [← tsum_mul_left]
  have h : ∀ j, Q t (j + 1) ξ * (w ^ j * b (t + 1) ξ - w ^ (j + 1) * b t ξ) =
      (b (t + 1) ξ - w * b t ξ) * (w ^ j * Q t (j + 1) ξ) := fun j => by ring
  simp_rw [h]

/-- Cochrane (2023), A1 p. 561 ("A geometric maturity structure needs tending, except in a
knife edge case that surpluses are also nonstochastic and geometric"), made precise: if the
geometric flow condition holds at every date and the value `∑_j ωʲQ_t^{(t+j+1)}` of the debt
carried forward per unit is never zero (e.g. positive bond prices), then the government never
needs to trade iff nominal surpluses are `P_ts_t = ωᵗb_0` at every date. -/
theorem geom_knife_edge {w : ℝ} {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hflow : ∀ t, GeomFlow w P s b Q t) (hS : ∀ t ξ, ∑' j, w ^ j * Q t (j + 1) ξ ≠ 0) :
    NoTrade (geomDebt w b) ↔ ∀ t ξ, P t ξ * s t ξ = w ^ t * b 0 ξ := by
  constructor
  · intro hnt t ξ
    have hf := geomFlow_iff_issuance.mp (hflow t) ξ
    have h1 := (geom_noTrade_iff w b).mp hnt t ξ
    have h2 := (geom_noTrade_iff_path w b).mp hnt t ξ
    rw [h1, sub_self, zero_mul, add_zero] at hf
    rw [← hf, h2]
  · intro hs
    rw [geom_noTrade_iff_path]
    intro t ξ
    induction t with
    | zero => simp
    | succ t ih =>
      have hf := geomFlow_iff_issuance.mp (hflow t) ξ
      rw [hs t ξ, ih] at hf
      have hz : (b (t + 1) ξ - w * (w ^ t * b 0 ξ)) * ∑' j, w ^ j * Q t (j + 1) ξ = 0 := by
        linarith
      rcases mul_eq_zero.mp hz with h | h
      · rw [pow_succ]
        linarith
      · exact absurd h (hS t ξ)

/-- Cochrane (2023), A1 p. 561 ("nonstochastic"): in the knife-edge case nominal surpluses are
known at date 0 (`E_0[P_ts_t] = P_ts_t`) whenever `b_0` is. -/
theorem knife_edge_surplus_known (𝔼 : ExpectationSystem Ω) {w : ℝ} {P s b : ℕ → Ω → ℝ}
    {Q : ℕ → ℕ → Ω → ℝ} (hflow : ∀ t, GeomFlow w P s b Q t) (hnt : NoTrade (geomDebt w b))
    (hb0 : 𝔼.E 0 (b 0) = b 0) (t : ℕ) : 𝔼.E 0 (P t * s t) = P t * s t := by
  have h : P t * s t = w ^ t • b 0 := by
    funext ξ
    have hf := geomFlow_iff_issuance.mp (hflow t) ξ
    rw [(geom_noTrade_iff w b).mp hnt t ξ, sub_self, zero_mul, add_zero] at hf
    rw [Pi.mul_apply, ← hf, Pi.smul_apply, smul_eq_mul, (geom_noTrade_iff_path w b).mp hnt t ξ]
  rw [h, map_smul, hb0]

/-- Cochrane (2023), A1 p. 561 ("To see the needed bond sales"): outside the knife edge — if at
some date and state `P_ts_t ≠ ωᵗb_0` — the government must issue or repurchase debt at some
date: some `B_t^{(t+j)} − B_{t−1}^{(t+j)} = ω^{j−1}(b_{t+1} − ωb_t) ≠ 0`. -/
theorem geom_needs_tending {w : ℝ} {P s b : ℕ → Ω → ℝ} {Q : ℕ → ℕ → Ω → ℝ}
    (hflow : ∀ t, GeomFlow w P s b Q t) (hS : ∀ t ξ, ∑' j, w ^ j * Q t (j + 1) ξ ≠ 0)
    (hne : ∃ t ξ, P t ξ * s t ξ ≠ w ^ t * b 0 ξ) :
    ∃ t j ξ, geomDebt w b (t + 1) j ξ - geomDebt w b t (j + 1) ξ ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨t, ξ, hne⟩ := hne
  exact hne ((geom_knife_edge hflow hS).mp (fun t j ξ => sub_eq_zero.mp (h t j ξ)) t ξ)

end Cochrane.Generality.LongTermDebt
