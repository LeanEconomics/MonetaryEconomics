/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.MoneyTargetingDynamics

/-!
# Unpleasant arithmetic and fiscal theory

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.6, pp. 456–457,
eqs. (19.39)–(19.40) (Sargent and Wallace (1981)). Perfect foresight, constant output `y` and
velocity `V`, constant discount factor `β`; present values are genuine `HasSum`s.

Notation: `N t = M_{t−1}`, money growth `g_t = M_t/M_{t−1}`, seigniorage
`σ_t = (M_t − M_{t−1})/P_t`.

## Main results

* (19.39): `seigniorage_eq` (`σ_t = (y/V)(1 − M_{t−1}/M_t)`), `inflation_eq_growth`
  (`P_t/P_{t−1} = M_t/M_{t−1}`), `seig_strictMono` (seigniorage increases with money growth),
  `seig_lt_bound`, `any_timing` (every seigniorage level below `y/V` is attained by some money
  growth).
* (19.40) with fixed surpluses: `seigniorage_pv` (the present value of seigniorage is fixed at
  `b_{−1} − ∑βʲs_j`), `unpleasant_shift` (less seigniorage now = exactly that much more present
  value later), `unpleasant_tradeoff` (some later date has more seigniorage),
  `unpleasant_money_growth` (lower money growth now forces higher money growth, hence higher
  inflation, later).
* Nominal vs real debt (p. 457): `nominal_debt_price` (`P_0 = B_{−1}/∑βʲs_j`, unique),
  `nominal_debt_price_anti` (a fall in the present value of surpluses raises `P_0` with no
  money at all), `disinflation_windfall` (a lower price level raises the real value of nominal
  debt, which surpluses must pay), `real_debt_no_price` (with real debt and no seigniorage the
  valuation equation restricts surpluses, not the price level).
-/

namespace Cochrane.Monetarism.UnpleasantArithmetic

open Filter Topology

/-- Cochrane (2023), (19.39)–(19.40), p. 456: seigniorage as a function of gross money growth
`g = M_t/M_{t−1}` under `M_tV = P_ty`: `σ(g) = (y/V)(1 − 1/g)`. -/
noncomputable def seig (y V g : ℝ) : ℝ := y / V * (1 - 1 / g)

/-- Cochrane (2023), eq. (19.39), p. 456: with `M_tV = P_ty`, seigniorage
`(M_t − M_{t−1})/P_t = (y/V)(1 − M_{t−1}/M_t)`. -/
theorem seigniorage_eq {Mt Mprev Pt y V : ℝ} (hM : 0 < Mt) (hV : 0 < V)
    (hP : 0 < Pt) (hq : Mt * V = Pt * y) : (Mt - Mprev) / Pt = seig y V (Mt / Mprev) := by
  unfold seig
  have hy : y = Mt * V / Pt := by field_simp; linarith
  rw [hy]
  field_simp

/-- Cochrane (2023), eq. (19.39), p. 456: with constant `y` and `V`, inflation equals money
growth, `P_t/P_{t−1} = M_t/M_{t−1}`. -/
theorem inflation_eq_growth {Mt Mprev Pt Pprev y V : ℝ} (hV : 0 < V) (hy : 0 < y)
    (hq : Mt * V = Pt * y) (hq' : Mprev * V = Pprev * y) (hMp : 0 < Mprev) :
    Pt / Pprev = Mt / Mprev := by
  have hPp : Pprev = Mprev * V / y := by field_simp; linarith
  have hPt : Pt = Mt * V / y := by field_simp; linarith
  rw [hPt, hPp]
  field_simp

/-- Cochrane (2023), p. 456 ("A monetary tightening can reduce current inflation by slowing
money growth"): seigniorage is strictly increasing in money growth on `(0, ∞)`. -/
theorem seig_strictMono {y V : ℝ} (hy : 0 < y) (hV : 0 < V) :
    StrictMonoOn (seig y V) (Set.Ioi 0) := by
  intro g hg g' hg' h
  have hg0 : (0 : ℝ) < g := hg
  unfold seig
  have : 1 / g' < 1 / g := one_div_lt_one_div_of_lt hg0 h
  have hc : 0 < y / V := div_pos hy hV
  nlinarith

/-- Cochrane (2023), p. 456: seigniorage is bounded by `y/V` (all money printed is at most the
whole money stock). -/
theorem seig_lt_bound {y V g : ℝ} (hy : 0 < y) (hV : 0 < V) (hg : 0 < g) : seig y V g < y / V := by
  unfold seig
  have : 0 < 1 / g := by positivity
  have hc : 0 < y / V := div_pos hy hV
  nlinarith

/-- Cochrane (2023), p. 456 ("the central bank can still decide when it will print more
money"): every seigniorage level `σ < y/V` is produced by exactly the money growth
`g = 1/(1 − Vσ/y) > 0`. -/
theorem any_timing {y V σ : ℝ} (hy : 0 < y) (hV : 0 < V) (hσ : σ < y / V) :
    ∃ g, 0 < g ∧ seig y V g = σ := by
  have hd : 0 < 1 - V * σ / y := by
    have : V * σ < y := by rwa [lt_div_iff₀ hV, mul_comm] at hσ
    have : V * σ / y < 1 := by rwa [div_lt_one hy]
    linarith
  refine ⟨1 / (1 - V * σ / y), by positivity, ?_⟩
  unfold seig
  field_simp
  ring

/-- Cochrane (2023), eq. (19.40), p. 456 ("the present value of seigniorage revenue counts"):
with fixed surpluses, `b_{−1} = ∑βʲ(s_j + σ_j)` fixes the present value of seigniorage at
`b_{−1} − ∑βʲs_j`. -/
theorem seigniorage_pv {β b S : ℝ} {s σ : ℕ → ℝ} (hs : HasSum (fun j => β ^ j * s j) S)
    (hb : HasSum (fun j => β ^ j * (s j + σ j)) b) : HasSum (fun j => β ^ j * σ j) (b - S) := by
  have := hb.sub hs
  refine this.congr_fun fun j => ?_
  ring

/-- Cochrane (2023), p. 456 ("without a change in surpluses, the central bank will have to raise
later money growth … to preserve the present value of seigniorage revenue"): two seigniorage
paths consistent with (19.40) for the same `b_{−1}` and surpluses differ after date 0 in present
value by exactly the date-0 difference. -/
theorem unpleasant_shift {β b S : ℝ} {s σ σ' : ℕ → ℝ} (hs : HasSum (fun j => β ^ j * s j) S)
    (hb : HasSum (fun j => β ^ j * (s j + σ j)) b)
    (hb' : HasSum (fun j => β ^ j * (s j + σ' j)) b) :
    ∑' j, β ^ (j + 1) * σ' (j + 1) - ∑' j, β ^ (j + 1) * σ (j + 1) = σ 0 - σ' 0 := by
  have h1 := seigniorage_pv hs hb
  have h2 := seigniorage_pv hs hb'
  have e1 := h1.summable.tsum_eq_zero_add
  have e2 := h2.summable.tsum_eq_zero_add
  rw [h1.tsum_eq] at e1
  rw [h2.tsum_eq] at e2
  simp only [pow_zero, one_mul] at e1 e2
  linarith

/-- Cochrane (2023), p. 456 ("lowering money growth now forces higher money growth later"): if
date-0 seigniorage is lower, `σ'_0 < σ_0`, then seigniorage is higher at some later date. -/
theorem unpleasant_tradeoff {β b S : ℝ} (hβ : 0 < β) {s σ σ' : ℕ → ℝ}
    (hs : HasSum (fun j => β ^ j * s j) S) (hb : HasSum (fun j => β ^ j * (s j + σ j)) b)
    (hb' : HasSum (fun j => β ^ j * (s j + σ' j)) b) (h0 : σ' 0 < σ 0) :
    ∃ j, 0 < j ∧ σ j < σ' j := by
  by_contra hcon
  push Not at hcon
  have h1 := seigniorage_pv hs hb
  have h2 := seigniorage_pv hs hb'
  have hle : (fun j => β ^ j * σ' j) ≤ fun j => β ^ j * σ j := fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [pow_zero, one_mul]; exact h0.le
    · exact mul_le_mul_of_nonneg_left (hcon j hj) (pow_nonneg hβ.le j)
  have hlt : (fun j => β ^ j * σ' j) 0 < (fun j => β ^ j * σ j) 0 := by
    simp only [pow_zero, one_mul]; exact h0
  have := hasSum_lt hle hlt h2 h1
  linarith

/-- Cochrane (2023), p. 456, in money growth: if date-0 money growth is lower, `g'_0 < g_0`,
the seigniorage `σ = σ(g)` of (19.39) is lower at date 0, so money growth — and by
`inflation_eq_growth`, inflation — must be higher at some later date. -/
theorem unpleasant_money_growth {β b S y V : ℝ} (hβ : 0 < β) (hy : 0 < y) (hV : 0 < V)
    {s g g' : ℕ → ℝ} (hg : ∀ j, 0 < g j) (hg' : ∀ j, 0 < g' j)
    (hs : HasSum (fun j => β ^ j * s j) S)
    (hb : HasSum (fun j => β ^ j * (s j + seig y V (g j))) b)
    (hb' : HasSum (fun j => β ^ j * (s j + seig y V (g' j))) b) (h0 : g' 0 < g 0) :
    ∃ j, 0 < j ∧ g j < g' j := by
  have hσ0 : seig y V (g' 0) < seig y V (g 0) := seig_strictMono hy hV (hg' 0) (hg 0) h0
  obtain ⟨j, hj, hlt⟩ := unpleasant_tradeoff hβ hs hb hb' hσ0
  refine ⟨j, hj, ?_⟩
  by_contra hcon
  push Not at hcon
  rcases hcon.lt_or_eq with h | h
  · exact absurd hlt (not_lt.mpr (seig_strictMono hy hV (hg' j) (hg j) h).le)
  · rw [h] at hlt
    exact lt_irrefl _ hlt

/-- Cochrane (2023), p. 457 ("the left-hand side in fiscal theory may be the real value of
nominal debt `B_{t−1}/P_t`"): with nominal debt `B_{−1} > 0`, no money (`M = 0`) and present
value of surpluses `S > 0`, the valuation equation has exactly one positive price level,
`P_0 = B_{−1}/S`. -/
theorem nominal_debt_price {B S : ℝ} (hB : 0 < B) (hS : 0 < S) :
    ∃! P, 0 < P ∧ B / P = S := by
  refine ⟨B / S, ⟨div_pos hB hS, by field_simp⟩, fun P hP => ?_⟩
  have := hP.1
  rw [eq_div_iff hS.ne', ← hP.2]
  field_simp

/-- Cochrane (2023), p. 457 ("a fall in the present value of surpluses `{s_{t+j}}` can generate a
higher price level `P_t` even with no money demand or seigniorage whatsoever"): `S ↦ B/S` is
strictly decreasing on `(0, ∞)`. -/
theorem nominal_debt_price_anti {B : ℝ} (hB : 0 < B) : StrictAntiOn (fun S => B / S) (Set.Ioi 0) :=
  fun _ hS _ _ h => div_lt_div_of_pos_left hB hS h

/-- Cochrane (2023), p. 457 ("to achieve a monetary tightening that lowers inflation,
governments must finance a real windfall to the holders of outstanding nominal bonds"): the real
value `B/P` of nominal debt, which the present value of surpluses must equal, is strictly larger
at a lower price level. -/
theorem disinflation_windfall {B P P' : ℝ} (hB : 0 < B) (hP' : 0 < P') (h : P' < P) :
    B / P < B / P' :=
  div_lt_div_of_pos_left hB hP' h

/-- Cochrane (2023), p. 456 ("the value on the left-hand side of (19.40) is unaffected by the
price level"): with real debt `b_{−1}` and no money, the valuation equation `b_{−1} = S` places no
restriction on the price level: if it holds, every positive `P_0` is consistent with it, and if
it fails no price level restores it. -/
theorem real_debt_no_price {b S : ℝ} :
    ((∃ P : ℝ, 0 < P ∧ b = S) ↔ b = S) ∧ (b = S → ∀ P : ℝ, 0 < P → b = S) := by
  exact ⟨⟨fun ⟨_, _, h⟩ => h, fun h => ⟨1, one_pos, h⟩⟩, fun h _ _ => h⟩

end Cochrane.Monetarism.UnpleasantArithmetic
