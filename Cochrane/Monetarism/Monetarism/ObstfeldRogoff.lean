/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.PruningInflation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Obstfeld–Rogoff fix for inflationary equilibria

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix, Chapter 3,
§3.2.2 "The Obstfeld-Rogoff fix for inflationary equilibria" and §3.2.3, eq. (3.6),
Figure 3.2, pp. 621–629. Perfect foresight, separable utility, constant endowment `y`, constant
money `M`; `u₁ = u'(y) > 0`, `v'` the marginal utility of real money.

Following the survey's modelling advice, everything is stated with the value of money
`q_t = 1/P_t ≥ 0`, so that an infinite price level is `q_t = 0`; real balances are `M q_t`.

## Main results

* (3.6): `eq36_iff_value` (levels ⇔ value-of-money form), `eq36_real` (real-balance form),
  the steady state `steady_iff` (`v'(m̿) = (1−β)u'(y)`) and the terminal condition
  `terminal_iff` (`v'(M/P_T) = u'(y)` when `P_{T+1} = ∞`).
* The redemption first-order condition at `T` (p. 626): `redemption_foc_zero`,
  `redemption_raises_balance` (`P_T < P̄`, `M/P_T > M/P̄`).
* Figure 3.2 (`u' = 1`, `M = 1`, `β = 1/2`, `v'(m) = m^{−1/2}`): `fig32_vp_eq_rpow`,
  `fig32_steady` (`m = 4`), `fig32_terminal` (`M/P̄ = 1`), the backward map `fig32_back`
  with `fig32_back_spec`, `fig32_eps0` (`1 + √3/2 ≈ 1.866`), `fig32_eps_half`
  (`(3 + 2√2)/4 ≈ 1.457`), `fig32_numbers`; survey error **E18**: the caption's
  `v(m) = m^{−1/2}` is decreasing (`e18_caption_decreasing`) and admits neither the steady
  state nor the terminal level (`e18_no_steady_state`), while `v(m) = 2√m` has `v' = m^{−1/2}`
  (`e18_correct_v`).
* Obstfeld and Rogoff's finite-price theorem (p. 624 quote): `IsORPath`, `or_balance_step`,
  `or_no_hyperinflation` — with one-way redemption, the arbitrage bound `q_t ≥ ε > 0` and
  (3.6), real balances never fall below the steady state, so no hyperinflation path exists.
  `two_way_steady` / `two_way_needs_sale`: the two-way conversion steady state at `q = ε` needs
  the government to sell money.
* Cochrane's demonetised equilibrium (pp. 625–627), the definitional dispute made explicit:
  `cochrane_sum_identity` and `cochrane_household_optimal` — with a one-time redemption of the
  money carried out of `T`, the path with `q_{T+1} = 0` and all money redeemed solves the
  price-taking household's problem (Walrasian equilibrium); `cochrane_violates_or_bound` — it
  violates Obstfeld and Rogoff's arbitrage bound; `standing_redemption_no_optimum` — if the
  redemption offer also stands for money acquired at `q = 0`, the household can always do
  strictly better, so under that (deviation/arbitrage) reading the path is not an equilibrium.
  Figure 3.2 instance: `fig32_v_supergradient`, `fig32_cochrane_path`,
  `fig32_cochrane_optimal` (the "ε = 0.5" path is household-optimal for every `T`).
-/

namespace Cochrane.Monetarism.ObstfeldRogoff

open Filter Topology

/-! ## Equation (3.6) -/

/-- Cochrane (2023), eq. (3.6), p. 623 (Obstfeld–Rogoff (1983) eq. (4)): in levels,
`u'(y)/P_t − v'(M/P_t)/P_t = βu'(y)/P_{t+1}` iff, with `q = 1/P`,
`(u'(y) − v'(Mq_t))q_t = βu'(y)q_{t+1}`. -/
theorem eq36_iff_value {β u1 M P P' : ℝ} {vp : ℝ → ℝ} :
    u1 / P - vp (M / P) / P = β * u1 / P' ↔
      (u1 - vp (M * (1 / P))) * (1 / P) = β * u1 * (1 / P') := by
  rw [show M * (1 / P) = M / P by ring,
    show (u1 - vp (M / P)) * (1 / P) = u1 / P - vp (M / P) / P by ring,
    show β * u1 * (1 / P') = β * u1 / P' by ring]

/-- Cochrane (2023), eq. (3.6), p. 623, in real balances `m_t = Mq_t`:
`(u'(y) − v'(m_t))m_t = βu'(y)m_{t+1}` (multiply the value form by `M`). -/
theorem eq36_real {β u1 M q q' : ℝ} {vp : ℝ → ℝ} (hM : 0 < M) :
    (u1 - vp (M * q)) * q = β * u1 * q' ↔ (u1 - vp (M * q)) * (M * q) = β * u1 * (M * q') := by
  constructor
  · intro h; rw [← mul_assoc, mul_comm _ M, mul_assoc, h]; ring
  · intro h
    have : M * ((u1 - vp (M * q)) * q) = M * (β * u1 * q') := by linarith [h]
    exact mul_left_cancel₀ hM.ne' this

/-- Cochrane (2023), p. 623: the steady state `P̿` of (3.6) with constant money:
`u'/P − v'(M/P)/P = βu'/P` iff `v'(M/P) = (1−β)u'(y)`. -/
theorem steady_iff {β u1 M P : ℝ} {vp : ℝ → ℝ} (hP : 0 < P) :
    u1 / P - vp (M / P) / P = β * u1 / P ↔ vp (M / P) = (1 - β) * u1 := by
  constructor
  · intro h; field_simp at h; linarith
  · intro h; rw [h]; field_simp; ring

/-- Cochrane (2023), p. 623, "The price level at time `T` is then `v'(M/P_T) = v'(M/P̄) = u'(y)`":
the value form of (3.6) at `T` with `q_{T+1} = 0` (`P_{T+1} = ∞`) and `q_T > 0` holds iff
`v'(Mq_T) = u'(y)`. -/
theorem terminal_iff {β u1 M qT : ℝ} {vp : ℝ → ℝ} (hq : 0 < qT) :
    (u1 - vp (M * qT)) * qT = β * u1 * 0 ↔ vp (M * qT) = u1 := by
  rw [mul_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · exact absurd h1 hq.ne'
  · intro h; rw [h]; ring

/-- Cochrane (2023), p. 626, display: with the redemption promise, the first-order condition at
`T` is `(u'(y) − v'(M/P_T))/P_T = max(βu'(y)/P̲, βu'(y)/P_{T+1})` with `P̲ = 1/ε`; in value form,
with `q_{T+1} = 0`, the right side is `βu'(y)ε`. -/
theorem redemption_foc_zero {β u1 ε : ℝ} (hβ : 0 < β) (hu : 0 < u1) (hε : 0 ≤ ε) :
    max (β * u1 * ε) (β * u1 * 0) = β * u1 * ε := by
  rw [mul_zero]
  exact max_eq_left (by positivity)

/-- Cochrane (2023), p. 626, "This effect gives a small decrease in the price level `P_T < P̄`
and `M/P_T > M/P̄`": if `v'` is strictly decreasing, `v'(m̄) = u'(y)`, and the terminal
condition with redemption `(u' − v'(m_T))m_T = βu'εM` holds with `ε > 0`, then `m_T > m̄`. -/
theorem redemption_raises_balance {β u1 ε M mT mbar : ℝ} {vp : ℝ → ℝ} (hβ : 0 < β)
    (hu : 0 < u1) (hε : 0 < ε) (hM : 0 < M) (hmT : 0 < mT) (hmbar : 0 < mbar)
    (hanti : StrictAntiOn vp (Set.Ioi 0)) (hbar : vp mbar = u1)
    (hfoc : (u1 - vp mT) * mT = β * u1 * ε * M) : mbar < mT := by
  have hpos : 0 < (u1 - vp mT) * mT := by rw [hfoc]; positivity
  have h1 : vp mT < u1 := by
    by_contra h; push Not at h
    have : (u1 - vp mT) * mT ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hmT.le
    linarith
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h | h
  · have := hanti hmT hmbar h; linarith
  · rw [h, hbar] at h1; exact lt_irrefl _ h1

/-! ## Figure 3.2 -/

/-- Cochrane (2023), Figure 3.2, p. 624: the marginal utility of money `v'(m) = 1/√m`. -/
noncomputable def figVp (m : ℝ) : ℝ := 1 / Real.sqrt m

/-- Cochrane (2023), Figure 3.2, p. 624: `1/√m = m^{−1/2}` for `m > 0`. -/
theorem fig32_vp_eq_rpow {m : ℝ} (hm : 0 < m) : figVp m = m ^ (-(1 / 2 : ℝ)) := by
  unfold figVp
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hm.le, one_div]

/-- Cochrane (2023), Figure 3.2, p. 624: `v'` is strictly decreasing on `(0, ∞)`. -/
theorem fig32_vp_strictAnti : StrictAntiOn figVp (Set.Ioi 0) := by
  intro a ha b _ hab
  unfold figVp
  have h1 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h2 : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  exact one_div_lt_one_div_of_lt h1 h2

/-- Cochrane (2023), Figure 3.2, p. 624: with `u' = 1`, `β = 1/2`, the steady state of (3.6)
`v'(m) = (1−β)u'` is `m = 4` ("Steady state" line). -/
theorem fig32_steady {m : ℝ} (hm : 0 < m) : figVp m = (1 - 1 / 2) * 1 ↔ m = 4 := by
  unfold figVp
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  constructor
  · intro h
    have h1 : Real.sqrt m = 2 := by field_simp at h; linarith
    have := Real.sq_sqrt hm.le
    rw [h1] at this; linarith
  · intro h
    rw [h, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

/-- Cochrane (2023), Figure 3.2, p. 624: the terminal level `v'(M/P̄) = u'(y) = 1` is
`M/P̄ = 1` ("the lower horizontal line"). -/
theorem fig32_terminal {m : ℝ} (hm : 0 < m) : figVp m = 1 ↔ m = 1 := by
  unfold figVp
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  constructor
  · intro h
    have h1 : Real.sqrt m = 1 := by field_simp at h; linarith
    have := Real.sq_sqrt hm.le
    rw [h1] at this; linarith
  · intro h; rw [h, Real.sqrt_one]; norm_num

/-- Cochrane (2023), Figure 3.2, p. 624: the backward step of (3.6), `m − √m = m'/2`, solved by
`b(m') = ((1 + √(1 + 2m'))/2)²`. -/
noncomputable def fig32_back (m' : ℝ) : ℝ := ((1 + Real.sqrt (1 + 2 * m')) / 2) ^ 2

/-- Cochrane (2023), Figure 3.2, p. 624: for `m' ≥ 0`, `b(m')` is the unique `m ≥ 1/4` with
`(u' − v'(m))m = βu'm'`, i.e. `m − √m = m'/2`; moreover `b(m') ≥ 1`. -/
theorem fig32_back_spec {m' : ℝ} (hm' : 0 ≤ m') :
    1 ≤ fig32_back m' ∧ (1 - figVp (fig32_back m')) * fig32_back m' = 1 / 2 * 1 * m' ∧
      ∀ m, 1 / 4 ≤ m → (1 - figVp m) * m = 1 / 2 * 1 * m' → m = fig32_back m' := by
  have hr : 1 ≤ Real.sqrt (1 + 2 * m') := by
    have := Real.sqrt_le_sqrt (by linarith : (1 : ℝ) ≤ 1 + 2 * m')
    rwa [Real.sqrt_one] at this
  have hr2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + 2 * m')
  set r := Real.sqrt (1 + 2 * m') with hrdef
  have hsq : Real.sqrt (fig32_back m') = (1 + r) / 2 := by
    unfold fig32_back
    exact Real.sqrt_sq (by linarith)
  have hb1 : 1 ≤ fig32_back m' := by unfold fig32_back; nlinarith
  refine ⟨hb1, ?_, ?_⟩
  · unfold figVp
    rw [hsq]
    unfold fig32_back
    rw [← hrdef]
    field_simp
    nlinarith
  · intro m hm h
    have hm0 : 0 < m := by linarith
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
    have hsm := Real.sq_sqrt hm0.le
    unfold figVp at h
    have h1 : m - Real.sqrt m = m' / 2 := by
      have : (1 - 1 / Real.sqrt m) * m = m - Real.sqrt m := by
        field_simp; nlinarith
      linarith
    have hs2 : 1 / 2 ≤ Real.sqrt m := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hm
    have h2 : Real.sqrt m = (1 + r) / 2 := by
      have hq : (2 * Real.sqrt m - 1) ^ 2 = r ^ 2 := by nlinarith
      have h3 : 2 * Real.sqrt m - 1 = r := by
        have hr0 : 0 ≤ r := by linarith
        nlinarith [sq_nonneg (2 * Real.sqrt m - 1 - r), sq_nonneg (2 * Real.sqrt m - 1 + r)]
      linarith
    rw [← hsm, h2]
    unfold fig32_back
    rw [← hrdef]

/-- Cochrane (2023), Figure 3.2, p. 624, "ε = 0" line: `M/P_T = b(0) = 1` and the previous date
`M/P_{T−1} = b(1) = 1 + √3/2` (≈ 1.866). -/
theorem fig32_eps0 : fig32_back 0 = 1 ∧ fig32_back 1 = 1 + Real.sqrt 3 / 2 := by
  constructor
  · unfold fig32_back; norm_num
  · unfold fig32_back
    have h3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    rw [show (1 : ℝ) + 2 * 1 = 3 by norm_num]
    nlinarith

/-- Cochrane (2023), Figure 3.2, p. 624, "ε = 0.5" line: with redemption value `Mε = 0.5` at
`T + 1`, the terminal condition `m_T − √m_T = βεM/u' = 1/4` gives `M/P_T = b(1/2) = (3 + 2√2)/4`
(≈ 1.457), above `M/P̄ = 1`. -/
theorem fig32_eps_half : fig32_back (1 / 2) = (3 + 2 * Real.sqrt 2) / 4 := by
  unfold fig32_back
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [show (1 : ℝ) + 2 * (1 / 2) = 2 by norm_num]
  nlinarith

/-- Cochrane (2023), Figure 3.2, p. 624: the plotted numbers, `1.866 < 1 + √3/2 < 1.8661` and
`1.457 < (3 + 2√2)/4 < 1.4572`; the redemption value is `Mε = 1 · 0.5`. -/
theorem fig32_numbers :
    (1.866 : ℝ) < 1 + Real.sqrt 3 / 2 ∧ 1 + Real.sqrt 3 / 2 < (1.8661 : ℝ) ∧
      (1.457 : ℝ) < (3 + 2 * Real.sqrt 2) / 4 ∧ (3 + 2 * Real.sqrt 2) / 4 < (1.4572 : ℝ) ∧
      (1 : ℝ) * 0.5 = 0.5 := by
  have h3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have p3 := Real.sqrt_nonneg 3
  have p2 := Real.sqrt_nonneg 2
  refine ⟨?_, ?_, ?_, ?_, by norm_num⟩ <;> nlinarith

/-- Cochrane (2023), Figure 3.2 caption, survey error **E18**: the caption's `v(m) = m^{−1/2}`
has derivative `−½ m^{−3/2} < 0`: money would have negative marginal utility. -/
theorem e18_caption_decreasing {m : ℝ} (hm : 0 < m) :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (-(1 / 2) * m ^ (-(1 / 2 : ℝ) - 1)) m ∧
      -(1 / 2) * m ^ (-(1 / 2 : ℝ) - 1) < 0 := by
  refine ⟨Real.hasDerivAt_rpow_const (Or.inl hm.ne'), ?_⟩
  have := Real.rpow_pos_of_pos hm (-(1 / 2 : ℝ) - 1)
  linarith

/-- Cochrane (2023), Figure 3.2 caption (E18): with `v(m) = m^{−1/2}` (so `v' < 0`) neither the
steady state `v'(m) = (1−β)u' = 1/2` nor the terminal level `v'(m) = u' = 1` has a positive
solution — the figure cannot be drawn from the caption's utility. -/
theorem e18_no_steady_state {m : ℝ} (hm : 0 < m) :
    -(1 / 2) * m ^ (-(1 / 2 : ℝ) - 1) ≠ 1 / 2 ∧ -(1 / 2) * m ^ (-(1 / 2 : ℝ) - 1) ≠ 1 := by
  have := (e18_caption_decreasing hm).2
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), Figure 3.2 (E18, corrected): `v(m) = 2√m` has `v'(m) = m^{−1/2}`, the
marginal utility used for the plotted numbers. -/
theorem e18_correct_v {m : ℝ} (hm : 0 < m) :
    HasDerivAt (fun x => 2 * Real.sqrt x) (figVp m) m := by
  have h := (Real.hasDerivAt_sqrt hm.ne').const_mul 2
  convert h using 1
  unfold figVp
  have : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  field_simp

/-! ## Obstfeld and Rogoff's finite-price theorem -/

/-- Cochrane (2023), pp. 623–624 (Obstfeld–Rogoff (1983), p. 684): a perfect-foresight path
under one-way redemption at `ε`, in Obstfeld and Rogoff's sense: the value of money respects the
arbitrage bound `q_t ≥ ε` (`P_t ≤ P̲ = 1/ε`, finite at every date), money holdings `M_t > 0` can
only fall (dollars may be redeemed but are never sold), and (3.6) holds at every date with
`Mq` replaced by real balances `M_tq_t`. -/
def IsORPath (β u1 ε : ℝ) (vp : ℝ → ℝ) (q Mh : ℕ → ℝ) : Prop :=
  (∀ t, ε ≤ q t) ∧ (∀ t, 0 < Mh t) ∧ (∀ t, Mh (t + 1) ≤ Mh t) ∧
    ∀ t, (u1 - vp (Mh t * q t)) * q t = β * u1 * q (t + 1)

/-- Cochrane (2023), p. 624 (the step in Obstfeld–Rogoff's argument): along such a path real
balances `r_t = M_tq_t` satisfy `v'(r_t) < u'(y)` and
`βu'(y) r_{t+1} ≤ (u'(y) − v'(r_t)) r_t`. -/
theorem or_balance_step {β u1 ε : ℝ} {vp : ℝ → ℝ} {q Mh : ℕ → ℝ} (hβ : 0 < β) (hu : 0 < u1)
    (hε : 0 < ε) (hpath : IsORPath β u1 ε vp q Mh) (t : ℕ) :
    vp (Mh t * q t) < u1 ∧
      β * u1 * (Mh (t + 1) * q (t + 1)) ≤ (u1 - vp (Mh t * q t)) * (Mh t * q t) := by
  obtain ⟨hq, hM, hdec, heq⟩ := hpath
  have hqt : 0 < q t := lt_of_lt_of_le hε (hq t)
  have hqt1 : 0 < q (t + 1) := lt_of_lt_of_le hε (hq (t + 1))
  have h1 : 0 < (u1 - vp (Mh t * q t)) * q t := by rw [heq t]; positivity
  have h2 : vp (Mh t * q t) < u1 := by
    by_contra h; push Not at h
    have : (u1 - vp (Mh t * q t)) * q t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hqt.le
    linarith
  refine ⟨h2, ?_⟩
  have h3 : (u1 - vp (Mh t * q t)) * (Mh t * q t) = Mh t * (β * u1 * q (t + 1)) := by
    rw [← heq t]; ring
  rw [h3]
  have := mul_le_mul_of_nonneg_right (hdec t) (by positivity : (0 : ℝ) ≤ β * u1 * q (t + 1))
  nlinarith

/-- Cochrane (2023), p. 624, Obstfeld and Rogoff's claim "Suppose that `{P_t}` is an equilibrium
path with `P_0 > P̿` … `{P_t}` is not an equilibrium path", in their finite-price sense: if `v'`
is strictly decreasing and continuous, `v'(m̿) = (1−β)u'(y)` (steady state) and
`v'(m̄) = u'(y)` (terminal level), then along every `IsORPath` real balances never fall below
`m̿`: `M_tq_t ≥ m̿` for all `t`. With `M_0 = M` this is `P_0 ≤ P̿ = M/m̿`. (The only role of
`ε > 0` is that it keeps every price level finite.) -/
theorem or_no_hyperinflation {β u1 ε mss mbar : ℝ} {vp : ℝ → ℝ} {q Mh : ℕ → ℝ} (hβ : 0 < β)
    (hu : 0 < u1) (hε : 0 < ε) (hanti : StrictAntiOn vp (Set.Ioi 0))
    (hcont : ContinuousOn vp (Set.Ioi 0)) (hmss : 0 < mss) (hss : vp mss = (1 - β) * u1)
    (hmbar : 0 < mbar) (hbar : vp mbar = u1) (hpath : IsORPath β u1 ε vp q Mh) :
    ∀ t, mss ≤ Mh t * q t := by
  set r : ℕ → ℝ := fun t => Mh t * q t with hr
  have hrpos : ∀ t, 0 < r t := fun t =>
    mul_pos (hpath.2.1 t) (lt_of_lt_of_le hε (hpath.1 t))
  have hstep := or_balance_step hβ hu hε hpath
  -- real balances stay above the terminal level
  have habove : ∀ t, mbar < r t := by
    intro t
    have h := (hstep t).1
    by_contra hc; push Not at hc
    rcases hc.lt_or_eq with hc | hc
    · have := hanti (hrpos t) hmbar hc
      have : vp (r t) < u1 := h
      linarith
    · have : vp (r t) < u1 := h
      rw [hc, hbar] at this; exact lt_irrefl _ this
  -- below the steady state, real balances fall
  have hdown : ∀ x, 0 < x → x < mss → (u1 - vp x) * x < β * u1 * x := by
    intro x hx hxl
    have := hanti hx hmss hxl
    nlinarith
  intro t0
  by_contra hcon
  push Not at hcon
  set y : ℕ → ℝ := fun n => r (t0 + n) with hy
  have hfall : ∀ n, y n < mss ∧ y (n + 1) < y n := by
    intro n
    induction n with
    | zero =>
      have h1 := (hstep t0).2
      have h2 := hdown (r t0) (hrpos t0) hcon
      refine ⟨hcon, ?_⟩
      have : β * u1 * r (t0 + 1) < β * u1 * r t0 := lt_of_le_of_lt h1 h2
      exact lt_of_mul_lt_mul_left this (by positivity)
    | succ n ih =>
      have h0 : y (n + 1) < mss := lt_trans ih.2 ih.1
      have h1 := (hstep (t0 + (n + 1))).2
      have h2 := hdown (r (t0 + (n + 1))) (hrpos _) h0
      refine ⟨h0, ?_⟩
      have : β * u1 * r (t0 + (n + 1) + 1) < β * u1 * r (t0 + (n + 1)) := lt_of_le_of_lt h1 h2
      exact lt_of_mul_lt_mul_left this (by positivity)
  have hanti' : Antitone y := antitone_nat_of_succ_le fun n => (hfall n).2.le
  have hbdd : BddBelow (Set.range y) := ⟨mbar, by rintro _ ⟨n, rfl⟩; exact (habove _).le⟩
  have hlim := tendsto_atTop_ciInf hanti' hbdd
  set L := ⨅ n, y n with hL
  have hLbar : mbar ≤ L := le_ciInf fun n => (habove _).le
  have hL0 : 0 < L := lt_of_lt_of_le hmbar hLbar
  have hLss : L < mss := lt_of_le_of_lt (ciInf_le hbdd 0) (hfall 0).1
  have hc : ContinuousAt (fun x => (u1 - vp x) * x) L :=
    (continuousAt_const.sub (hcont.continuousAt (Ioi_mem_nhds hL0))).mul continuousAt_id
  have h1 : Tendsto (fun n => (u1 - vp (y n)) * y n) atTop (𝓝 ((u1 - vp L) * L)) :=
    hc.tendsto.comp hlim
  have h2 : Tendsto (fun n => β * u1 * y (n + 1)) atTop (𝓝 (β * u1 * L)) :=
    ((tendsto_add_atTop_iff_nat 1).mpr hlim).const_mul _
  have hle : β * u1 * L ≤ (u1 - vp L) * L :=
    le_of_tendsto_of_tendsto' h2 h1 fun n => by
      have := (hstep (t0 + n)).2
      simpa [hy, hr, add_assoc] using this
  have := hdown L hL0 hLss
  linarith

/-- Cochrane (2023), p. 624 and p. 625, "two-way conversion": if the government also sells money
at `P̲ = 1/ε`, the constant value `q = ε` with money holdings `m̿/ε` satisfies (3.6) — the
inflation stops and is an equilibrium. -/
theorem two_way_steady {β u1 ε mss : ℝ} {vp : ℝ → ℝ} (hε : 0 < ε)
    (hss : vp mss = (1 - β) * u1) :
    (u1 - vp (mss / ε * ε)) * ε = β * u1 * ε := by
  rw [div_mul_cancel₀ mss hε.ne', hss]; ring

/-- Cochrane (2023), p. 625, "Obstfeld and Rogoff's government refuses to increase the money
stock": when the backing is small, `Mε < m̿`, the two-way steady state needs money holdings
`m̿/ε > M`, i.e. the government must sell money — excluded by one-way redemption. -/
theorem two_way_needs_sale {ε M mss : ℝ} (hε : 0 < ε) (hsmall : M * ε < mss) : M < mss / ε := by
  rw [lt_div_iff₀ hε]; exact hsmall

/-! ## Cochrane's demonetised Walrasian equilibrium -/

/-- Cochrane (2023), pp. 625–627, the telescoping behind household optimality. Let `w_t` be the
value at `t + 1` of a dollar carried out of `t` (`w_t = q_{t+1}` for `t < T`, `w_T = ε`, the
redemption value, since `q_{T+1} = 0`). If `(u₁ − v'_t)q_t = βu₁w_t` for `t ≤ T` and the
deviations `d_t` of money holdings and `e_t` of consumption satisfy the budget identities
`e_0 = −q_0d_0`, `e_{t+1} = −q_{t+1}d_{t+1} + w_td_t`, then
`∑_{t≤n} βᵗ(u₁e_t + v'_tq_td_t) = −β^{n+1}u₁w_nd_n` for `n ≤ T`. -/
theorem cochrane_sum_identity {β u1 : ℝ} {T : ℕ} {q w vpt d e : ℕ → ℝ}
    (hfoc : ∀ t ≤ T, (u1 - vpt t) * q t = β * u1 * w t) (he0 : e 0 = -(q 0 * d 0))
    (he : ∀ t < T, e (t + 1) = -(q (t + 1) * d (t + 1)) + w t * d t) :
    ∀ n ≤ T, ∑ t ∈ Finset.range (n + 1), β ^ t * (u1 * e t + vpt t * q t * d t) =
      -(β ^ (n + 1) * u1 * w n * d n) := by
  intro n
  induction n with
  | zero =>
    intro h0
    rw [Finset.sum_range_one, he0]
    have := hfoc 0 h0
    have h : vpt 0 * q 0 = u1 * q 0 - β * u1 * w 0 := by linarith
    simp only [pow_zero, one_mul]
    linear_combination d 0 * h
  | succ k ih =>
    intro hk
    rw [Finset.sum_range_succ, ih (by omega), he k (by omega)]
    have := hfoc (k + 1) hk
    have h : vpt (k + 1) * q (k + 1) = u1 * q (k + 1) - β * u1 * w (k + 1) := by linarith
    rw [pow_succ]
    linear_combination (β ^ k * β) * d (k + 1) * h

/-- Cochrane (2023), pp. 625–627, "Given a price level sequence such that `P_{T+1} = ∞`, it is
optimal for consumers to sell all their money to the government … This is an equilibrium, in
the conventional definition of Walrasian equilibrium." Price-taking household problem with a
one-time redemption at `T + 1` of the money carried out of `T`: values `q_0, …, q_T > 0`,
`q_{T+1} = 0`; candidate plan `c_t = y`, money `M` held through `T`, all redeemed at `T + 1`
(financed by the tax `εM`). If `u` and `v` are concave (supergradient form at the candidate) and
(3.6) holds for `t < T` with the redemption condition at `T`, then every budget-feasible plan
`(c, H)` with `H_t ≥ 0` gives no more utility than the candidate. -/
theorem cochrane_household_optimal {β u1 ε y M : ℝ} {T : ℕ} {u v vp : ℝ → ℝ}
    {q c H : ℕ → ℝ} (hβ : 0 < β) (hq : ∀ t, 0 ≤ q t)
    (hu : ∀ x, u x ≤ u y + u1 * (x - y))
    (hv : ∀ t x, 0 ≤ x → v x ≤ v (M * q t) + vp (M * q t) * (x - M * q t))
    (hfoc : ∀ t < T, (u1 - vp (M * q t)) * q t = β * u1 * q (t + 1))
    (hfocT : (u1 - vp (M * q T)) * q T = β * u1 * ε)
    (hH : ∀ t, 0 ≤ H t)
    (hb0 : c 0 + q 0 * H 0 = y + q 0 * M)
    (hb : ∀ t < T, c (t + 1) + q (t + 1) * H (t + 1) = y + q (t + 1) * H t)
    (hbT : c (T + 1) = y + ε * H T - ε * M) :
    ∑ t ∈ Finset.range (T + 1), β ^ t * (u (c t) + v (q t * H t)) + β ^ (T + 1) * u (c (T + 1))
      ≤ ∑ t ∈ Finset.range (T + 1), β ^ t * (u y + v (q t * M)) + β ^ (T + 1) * u y := by
  set w : ℕ → ℝ := fun t => if t < T then q (t + 1) else ε with hw
  set d : ℕ → ℝ := fun t => H t - M with hd
  set e : ℕ → ℝ := fun t => c t - y with he
  have hfoc' : ∀ t ≤ T, (u1 - vp (M * q t)) * q t = β * u1 * w t := by
    intro t ht
    rcases ht.lt_or_eq with h | h
    · simp only [hw, h, ↓reduceIte]; exact hfoc t h
    · simp only [hw, h, lt_irrefl, ↓reduceIte]; exact hfocT
  have he0 : e 0 = -(q 0 * d 0) := by simp only [he, hd]; linarith
  have he' : ∀ t < T, e (t + 1) = -(q (t + 1) * d (t + 1)) + w t * d t := by
    intro t ht
    have := hb t ht
    simp only [he, hd, hw, ht, ↓reduceIte]
    linarith
  have hid := cochrane_sum_identity (vpt := fun t => vp (M * q t)) hfoc' he0 he' T le_rfl
  have hwT : w T = ε := by simp [hw]
  rw [hwT] at hid
  -- termwise concavity bounds
  have hterm : ∀ t, β ^ t * (u (c t) + v (q t * H t)) ≤ β ^ t * (u y + v (q t * M)) +
      β ^ t * (u1 * e t + vp (M * q t) * q t * d t) := by
    intro t
    have h1 := hu (c t)
    have h2 := hv t (q t * H t) (mul_nonneg (hq t) (hH t))
    have hp : 0 ≤ β ^ t := by positivity
    have : u (c t) + v (q t * H t) ≤ u y + v (q t * M) + (u1 * e t + vp (M * q t) * q t * d t) := by
      simp only [he, hd]
      rw [mul_comm (q t) M] at *
      nlinarith
    nlinarith
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.range (T + 1)) => hterm t
  rw [Finset.sum_add_distrib, hid] at hsum
  have hlast : β ^ (T + 1) * u (c (T + 1)) ≤ β ^ (T + 1) * u y + β ^ (T + 1) * u1 * ε * d T := by
    have h1 := hu (c (T + 1))
    have hp : 0 ≤ β ^ (T + 1) := by positivity
    have h2 : c (T + 1) - y = ε * d T := by simp only [hd]; rw [hbT]; ring
    rw [h2] at h1
    nlinarith
  linarith

/-- Cochrane (2023), pp. 626–627: Cochrane's equilibrium has `q_{T+1} = 0 < ε`, i.e.
`P_{T+1} = ∞ > P̲`, violating Obstfeld and Rogoff's arbitrage bound ("the market price of money
on date `T + 1` … will be at least `ε`"); so it is not an `IsORPath`. -/
theorem cochrane_violates_or_bound {β u1 ε : ℝ} {vp : ℝ → ℝ} {q Mh : ℕ → ℝ} {T : ℕ}
    (hε : 0 < ε) (hqT : q (T + 1) = 0) : ¬ IsORPath β u1 ε vp q Mh := by
  intro h
  have := h.1 (T + 1)
  rw [hqT] at this
  linarith

/-- Cochrane (2023), p. 626 and Obstfeld–Rogoff (2021) as quoted on p. 627, "Any individual who
deviates … and instead carries $1 into period `T + 1` will be able to sell it … to the government
for ε": if the redemption offer also stands for dollars acquired at `T + 1`, where `q_{T+1} = 0`,
then for every budget-feasible choice at `T + 1`, `T + 2`, acquiring one more (free) dollar and
redeeming it is feasible and strictly better (with `u` strictly increasing): the price-taking
household has no optimum, so under this reading the demonetised path is not a Walrasian
equilibrium. This is the precise content of the dispute: Cochrane's equilibrium requires that
money bought at an infinite price level cannot be redeemed. -/
theorem standing_redemption_no_optimum {β ε R y2 : ℝ} {u : ℝ → ℝ} {v : ℝ → ℝ} (hβ : 0 < β)
    (hε : 0 < ε) (hu : StrictMono u) (c1 H1 : ℝ) (hb1 : c1 + 0 * H1 = R) :
    c1 + 0 * (H1 + 1) = R ∧
      β * (u c1 + v (0 * H1)) + β ^ 2 * u (y2 + ε * H1) <
        β * (u c1 + v (0 * (H1 + 1))) + β ^ 2 * u (y2 + ε * (H1 + 1)) := by
  refine ⟨by simpa using hb1, ?_⟩
  have h1 : u (y2 + ε * H1) < u (y2 + ε * (H1 + 1)) := hu (by nlinarith)
  simp only [zero_mul]
  have : 0 < β ^ 2 := by positivity
  nlinarith

/-- Cochrane (2023), Figure 3.2: `v(m) = 2√m` is concave in supergradient form,
`2√x ≤ 2√m₀ + v'(m₀)(x − m₀)` for `x ≥ 0`, `m₀ > 0`. -/
theorem fig32_v_supergradient {m0 x : ℝ} (hm0 : 0 < m0) (hx : 0 ≤ x) :
    2 * Real.sqrt x ≤ 2 * Real.sqrt m0 + figVp m0 * (x - m0) := by
  unfold figVp
  have hs : 0 < Real.sqrt m0 := Real.sqrt_pos.mpr hm0
  have h1 := Real.sq_sqrt hm0.le
  have h2 := Real.sq_sqrt hx
  have hr := Real.sqrt_nonneg x
  rw [← h1, ← h2]
  rw [← sub_nonneg]
  have : 2 * Real.sqrt m0 + 1 / Real.sqrt m0 * (Real.sqrt x ^ 2 - Real.sqrt m0 ^ 2) -
      2 * Real.sqrt x = (Real.sqrt x - Real.sqrt m0) ^ 2 / Real.sqrt m0 := by
    field_simp; ring
  rw [h1, h2] at this ⊢
  rw [this]
  positivity

/-- Cochrane (2023), Figure 3.2, "ε = 0.5" (Cochrane's equilibrium): for every `T`, the values
`q_t = M/P_t = b^{T+1−t}(1/2)` (`M = 1`, `t ≤ T`) are at least one, satisfy (3.6) for `t < T`,
and the redemption condition `(u' − v'(q_T))q_T = βu'ε` at `T` (`u' = 1`, `β = ε = 1/2`). -/
theorem fig32_cochrane_path (T : ℕ) :
    (∀ t ≤ T, 1 ≤ fig32_back^[T + 1 - t] (1 / 2)) ∧
      (∀ t < T, (1 - figVp (1 * fig32_back^[T + 1 - t] (1 / 2))) *
          fig32_back^[T + 1 - t] (1 / 2) = 1 / 2 * 1 * fig32_back^[T + 1 - (t + 1)] (1 / 2)) ∧
      (1 - figVp (1 * fig32_back^[T + 1 - T] (1 / 2))) * fig32_back^[T + 1 - T] (1 / 2) =
        1 / 2 * 1 * (1 / 2) := by
  have hge : ∀ n, 0 ≤ fig32_back^[n] (1 / 2) ∧ (0 < n → 1 ≤ fig32_back^[n] (1 / 2)) := by
    intro n
    induction n with
    | zero => exact ⟨by norm_num, fun h => absurd h (lt_irrefl 0)⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := (fig32_back_spec ih.1).1
      exact ⟨by linarith, fun _ => this⟩
  refine ⟨fun t ht => (hge _).2 (by omega), fun t ht => ?_, ?_⟩
  · have hsplit : T + 1 - t = (T + 1 - (t + 1)) + 1 := by omega
    rw [one_mul, hsplit, Function.iterate_succ_apply']
    exact (fig32_back_spec (hge _).1).2.1
  · rw [show T + 1 - T = 0 + 1 by omega, Function.iterate_succ_apply', Function.iterate_zero_apply,
      one_mul]
    exact (fig32_back_spec (by norm_num)).2.1

/-- Cochrane (2023), pp. 624–627, Figure 3.2 instance of `cochrane_household_optimal`: with
`u(c) = c`, `v(m) = 2√m`, `M = 1`, `β = ε = 1/2`, for every `T` the demonetised path
`q_t = b^{T+1−t}(1/2)` (`t ≤ T`), `q_{T+1} = 0`, with all money redeemed at `T + 1`, is optimal
for the price-taking household among all budget-feasible plans. -/
theorem fig32_cochrane_optimal (T : ℕ) {y : ℝ} {c H : ℕ → ℝ} (hH : ∀ t, 0 ≤ H t)
    (hb0 : c 0 + (fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) 0 * H 0 =
      y + (fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) 0 * 1)
    (hb : ∀ t < T, c (t + 1) +
      (fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) (t + 1) * H (t + 1) =
      y + (fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) (t + 1) * H t)
    (hbT : c (T + 1) = y + 1 / 2 * H T - 1 / 2 * 1) :
    ∑ t ∈ Finset.range (T + 1), (1 / 2 : ℝ) ^ t * (c t + 2 * Real.sqrt
        ((fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) t * H t)) +
        (1 / 2 : ℝ) ^ (T + 1) * c (T + 1) ≤
      ∑ t ∈ Finset.range (T + 1), (1 / 2 : ℝ) ^ t * (y + 2 * Real.sqrt
        ((fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0) t * 1)) +
        (1 / 2 : ℝ) ^ (T + 1) * y := by
  set q : ℕ → ℝ := fun t => if t ≤ T then fig32_back^[T + 1 - t] (1 / 2) else 0 with hq
  obtain ⟨hge, hfoc, hfocT⟩ := fig32_cochrane_path T
  have hqT : ∀ t ≤ T, q t = fig32_back^[T + 1 - t] (1 / 2) := fun t ht => by
    simp only [hq, ht, ↓reduceIte]
  have hq0 : ∀ t, 0 ≤ q t := by
    intro t
    by_cases ht : t ≤ T
    · rw [hqT t ht]; linarith [hge t ht]
    · simp only [hq, ht, ↓reduceIte, le_refl]
  have hpos : ∀ t ≤ T, 0 < 1 * q t := fun t ht => by rw [hqT t ht]; linarith [hge t ht]
  -- the concavity bound for `v` is needed only at dates `t ≤ T`; extend it trivially beyond
  have key := cochrane_household_optimal (β := 1 / 2) (u1 := 1) (ε := 1 / 2) (y := y) (M := 1)
    (T := T) (u := id) (v := fun x => 2 * Real.sqrt x)
    (vp := fun x => if 0 < x then figVp x else 0) (q := fun t => if t ≤ T then q t else 1)
    (c := c) (H := H) (by norm_num)
    (fun t => by by_cases ht : t ≤ T <;> simp only [ht, ↓reduceIte] <;> [exact hq0 t; norm_num])
    (fun x => by simp)
    (fun t x hx => by
      have hp : 0 < 1 * (if t ≤ T then q t else 1) := by
        by_cases ht : t ≤ T
        · simp only [ht, ↓reduceIte]; exact hpos t ht
        · simp only [ht, ↓reduceIte]; norm_num
      simp only [hp, ↓reduceIte]
      exact fig32_v_supergradient hp hx)
    (fun t ht => by
      have ht' : t ≤ T := ht.le
      have ht1 : t + 1 ≤ T := ht
      have hp := hpos t ht'
      simp only [ht', ht1, ↓reduceIte, hp]
      rw [hqT t ht', hqT (t + 1) ht1]
      have := hfoc t ht
      rw [one_mul] at this ⊢
      linarith)
    (by
      have hp := hpos T le_rfl
      simp only [le_refl, ↓reduceIte, hp]
      rw [hqT T le_rfl]
      have := hfocT
      rw [one_mul] at this ⊢
      linarith)
    hH
    (by simp only [Nat.zero_le, ↓reduceIte]; exact hb0)
    (fun t ht => by
      have ht1 : t + 1 ≤ T := ht
      simp only [ht1, ↓reduceIte]; exact hb t ht)
    hbT
  have hsum : ∀ (f : ℕ → ℝ → ℝ), ∑ t ∈ Finset.range (T + 1), f t (if t ≤ T then q t else 1) =
      ∑ t ∈ Finset.range (T + 1), f t (q t) := by
    intro f
    refine Finset.sum_congr rfl fun t ht => ?_
    have : t ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    simp only [this, ↓reduceIte]
  have e1 := hsum (fun t z => (1 / 2 : ℝ) ^ t * (id (c t) + 2 * Real.sqrt (z * H t)))
  have e2 := hsum (fun t z => (1 / 2 : ℝ) ^ t * (id y + 2 * Real.sqrt (z * 1)))
  rw [e1, e2] at key
  simpa using key

end Cochrane.Monetarism.ObstfeldRogoff
