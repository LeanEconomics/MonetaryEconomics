/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import TwoPeriodModel.TidyR6InfiniteActivePassive
import Mathlib.Tactic.IntervalCases

/-!
# The two-period model as a truncation of the infinite horizon

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 1, §1.1, p. 4 ("The world ends
on day 2"), §1.3, pp. 7–8, and §§1.8–1.9, pp. 15–19. The chapter's model has a last day; the
infinite-horizon model of `TidyR6InfiniteHorizon` has a transversality condition instead. This
module makes precise in which sense the first is a truncation of the second.

## The `T`-period model

`FinEqm 𝔼 β T Bm s P Q`: dates `0, …, T`, positive price levels, `P_t` known at `t` for
`t < T`, the flow condition (1.2) and the bond price (1.3) at every `t < T`, and on the last day
the valuation equation (1.1)/(1.4) `B_{T−1}/P_T = s_T` (no debt is issued on the last day).
The backward solution `finSol a u T` of `z_T = u_T`, `z_t = u_t + aE_t z_{t+1}` gives the
`T`-period present value `finSol β s T t = ∑_{j ≤ T−t} β^j E_t s_{t+j}` (`finSol_closed`).

## Main results

* `finEqm_one_iff`: **the `T = 1` model is exactly Cochrane's two-period model**
  (`TwoPeriod.Equilibrium`), with no extra hypothesis; `finSol_one_zero`: its present value is
  `s₀ + βE₀s₁` (`TwoPeriod.pv`).
* `finEqm_iff`, `finEqm_exists`, `finEqm_unique`: every `T`-period model determines the price
  level, `P_t = B_{t−1}/∑_{j ≤ T−t} β^j E_t s_{t+j}`.
* `finSol_tendsto`, `finEqm_price_tendsto` (**the limit theorem**): as the last day `T → ∞`,
  the `T`-period equilibrium price levels converge, date by date and state by state, to the
  infinite-horizon equilibrium price level `B_{t−1}/∑_j β^j E_t s_{t+j}`
  (`TidyR6InfiniteHorizon.equilibrium_iff`).
* `restrict_twoPeriod`, `extend_twoPeriod` (**the two-period model inside the infinite
  horizon**): an infinite-horizon equilibrium in which the debt is retired on day 1
  (`B₁ = 0`) restricted to dates 0, 1 is a two-period equilibrium; conversely a two-period
  equilibrium (with `P₁` known at 1), continued with no debt and no surpluses, is an
  infinite-horizon equilibrium.
* Active and passive rules: `finRule_rec`, `finRule_realDebt` (with a last day the rule
  `s_t = γv_t + ŝ_t` determines the real debt at every date iff `γ ≠ 1`; `finRule_gamma_one`:
  with `γ = 1` the last-day price is free), `finRule_tendsto` (for `|1 − γ| > β` the truncated
  equilibria converge to `ruleF`, the unique infinite-horizon equilibrium when `γ ≤ 0` or
  `γ ≥ 2`, and one of a continuum when `0 < γ < 2`), `truncation_diverges` (for
  `1 − β < γ < 1` the truncated real debt can diverge: the last-day selection has no limit).
-/

namespace Cochrane.TwoPeriodModel.TidyR6Truncation

open Filter Topology Cochrane.TwoPeriodModel.TwoPeriod Cochrane.TwoPeriodModel.ForwardSolution
open Cochrane.TwoPeriodModel.TidyR6InfiniteHorizon
open Cochrane.TwoPeriodModel.TidyR6InfiniteActivePassive

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Backward solutions with a last day -/

/-- Cochrane (2023), §1.1, p. 4 (the last day), backward solution counted from the end:
`finSteps a u T n` is the value at date `T − n` of `z_T = u_T`, `z_t = u_t + aE_t z_{t+1}`. -/
noncomputable def finSteps (a : ℝ) (u : ℕ → Ω → ℝ) (T : ℕ) : ℕ → Ω → ℝ
  | 0 => u T
  | n + 1 => u (T - (n + 1)) + a • 𝔼.E (T - (n + 1)) (finSteps a u T n)

/-- Cochrane (2023), §1.1, p. 4, and eq. (1.5), p. 8: the backward solution at date `t` of
`z_T = u_T`, `z_t = u_t + aE_t z_{t+1}` (`t ≤ T`). -/
noncomputable def finSol (a : ℝ) (u : ℕ → Ω → ℝ) (T t : ℕ) : Ω → ℝ := finSteps 𝔼 a u T (T - t)

/-- Cochrane (2023), §1.1, p. 4: on the last day `z_T = u_T`. -/
theorem finSol_last (a : ℝ) (u : ℕ → Ω → ℝ) (T : ℕ) : finSol 𝔼 a u T T = u T := by
  simp [finSol, finSteps]

/-- Cochrane (2023), eq. (1.5), p. 8: before the last day `z_t = u_t + aE_t z_{t+1}`. -/
theorem finSol_rec (a : ℝ) (u : ℕ → Ω → ℝ) {T t : ℕ} (ht : t < T) :
    finSol 𝔼 a u T t = u t + a • 𝔼.E t (finSol 𝔼 a u T (t + 1)) := by
  unfold finSol
  obtain ⟨n, hn⟩ : ∃ n, T - t = n + 1 := ⟨T - t - 1, by omega⟩
  have h1 : T - (n + 1) = t := by omega
  have h2 : T - (t + 1) = n := by omega
  rw [hn, finSteps, h1, h2]

/-- Cochrane (2023), §1.1, p. 4 (with a last day the solution is unique): every `z` with
`z_T = u_T` and `z_t = u_t + aE_t z_{t+1}` for `t < T` equals `finSol` at every `t ≤ T`. -/
theorem finSol_unique {a : ℝ} {u z : ℕ → Ω → ℝ} {T : ℕ} (hT : z T = u T)
    (hrec : ∀ t < T, z t = u t + a • 𝔼.E t (z (t + 1))) : ∀ t ≤ T, z t = finSol 𝔼 a u T t := by
  have key : ∀ n, n ≤ T → z (T - n) = finSol 𝔼 a u T (T - n) := by
    intro n
    induction n with
    | zero => intro _; simpa [finSol_last] using hT
    | succ n ih =>
      intro hn
      have hlt : T - (n + 1) < T := by omega
      have he : T - (n + 1) + 1 = T - n := by omega
      rw [hrec _ hlt, finSol_rec 𝔼 a u hlt, he, ih (by omega)]
  intro t ht
  have := key (T - t) (Nat.sub_le T t)
  rwa [Nat.sub_sub_self ht] at this

/-- Cochrane (2023), eq. (1.5), p. 8 (the `T`-period present value in closed form): for adapted
`u` and `t ≤ T`, `finSol a u T t = ∑_{j ≤ T−t} a^j E_t u_{t+j}`. -/
theorem finSol_closed {a : ℝ} {u : ℕ → Ω → ℝ} (hua : 𝔼.Adapted u) {T t : ℕ} (ht : t ≤ T) :
    finSol 𝔼 a u T t = ∑ j ∈ Finset.range (T - t + 1), a ^ j • 𝔼.E t (u (t + j)) := by
  have key : ∀ n t, t + n = T →
      finSol 𝔼 a u T t = ∑ j ∈ Finset.range (n + 1), a ^ j • 𝔼.E t (u (t + j)) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      subst ht
      simp [finSol_last, hua t]
    | succ n ih =>
      intro t ht
      rw [finSol_rec 𝔼 a u (by omega), ih (t + 1) (by omega),
        Finset.sum_range_succ' (fun j => a ^ j • 𝔼.E t (u (t + j))) (n + 1)]
      simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, pow_zero, one_smul, add_zero,
        hua t]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [𝔼.tower (Nat.le_succ t), pow_succ, mul_comm a, show t + 1 + j = t + (j + 1) by omega]
  rw [key (T - t) t (by omega)]

/-- Cochrane (2023), eq. (1.5), p. 8: `finSol` is known at its date before the last day when
`u` is (`t < T`). -/
theorem finSol_known {a : ℝ} {u : ℕ → Ω → ℝ} {T t : ℕ} (ht : t < T) (hu : Known 𝔼 t (u t)) :
    Known 𝔼 t (finSol 𝔼 a u T t) := by
  rw [finSol_rec 𝔼 a u ht]
  exact known_add 𝔼 hu (known_smul 𝔼 a (known_E 𝔼 t _))

/-- Cochrane (2023), §1.1, p. 4, and eq. (1.5), p. 8 (**the limit of the last day**): for
`|a| < 1` and bounded adapted `u`, the backward solution with last day `T` converges, as
`T → ∞`, to the forward solution `∑_j a^j E_t u_{t+j}` at every date and state. -/
theorem finSol_tendsto {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => finSol 𝔼 a u T t ω) atTop (𝓝 (𝔼.forwardSeries a u t ω)) := by
  have hlim := ((summable_A16 𝔼 ha hu t ω).hasSum.tendsto_sum_nat).comp
    (tendsto_atTop_atTop_of_monotone (f := fun T : ℕ => T - t + 1)
      (fun x y hxy => by dsimp only; omega) fun b => ⟨b + t, by omega⟩)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [finSol_closed 𝔼 hua hT, Finset.sum_apply]
  rfl

/-! ### The `T`-period model -/

/-- Cochrane (2023), §§1.1–1.3, pp. 4–8, with last day `T`: positive price levels at dates
`0, …, T`, `P_t` known at `t` for `t < T`, the flow condition and the bond price at every
`t < T`, and the last-day valuation `B_{T−1}/P_T = s_T`. -/
def FinEqm (β : ℝ) (T : ℕ) (Bm s P Q : ℕ → Ω → ℝ) : Prop :=
  (∀ t ≤ T, ∀ ω, 0 < P t ω) ∧ (∀ t < T, Known 𝔼 t (P t)) ∧ (∀ t < T, Flow Bm s P Q t) ∧
    (∀ t < T, BondPrice 𝔼 β P Q t) ∧ Valuation1 (Bm T) (P T) (s T)

/-- Cochrane (2023), §§1.1–1.3, pp. 4–8: **the `T = 1` model is the two-period model**: an
equilibrium with last day 1 is exactly `TwoPeriod.Equilibrium` for
`(B₋₁, B₀, s₀, s₁, P₀, P₁, Q₀)`. -/
theorem finEqm_one_iff {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ} :
    FinEqm 𝔼 β 1 Bm s P Q ↔ Equilibrium 𝔼 β (Bm 0) (Bm 1) (s 0) (s 1) (P 0) (P 1) (Q 0) := by
  constructor
  · rintro ⟨hP, hk, hF, hQ, hv⟩
    exact ⟨hP 0 (by omega), hP 1 le_rfl, hk 0 one_pos, hF 0 one_pos, hQ 0 one_pos, hv⟩
  · rintro ⟨hP0, hP1, hk, hF, hQ, hv⟩
    refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, hv⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
      · exact hP0
      · exact hP1
    · obtain rfl : t = 0 := by omega
      exact hk
    · obtain rfl : t = 0 := by omega
      exact hF
    · obtain rfl : t = 0 := by omega
      exact hQ

/-- Cochrane (2023), eq. (1.5), p. 8: with last day 1 the present value at date 0 is
`s₀ + βE₀s₁`, the two-period `TwoPeriod.pv`, and at date 1 it is `s₁`. -/
theorem finSol_one_zero (β : ℝ) (s : ℕ → Ω → ℝ) :
    finSol 𝔼 β s 1 0 = pv 𝔼 β (s 0) (s 1) ∧ finSol 𝔼 β s 1 1 = s 1 := by
  refine ⟨?_, finSol_last 𝔼 β s 1⟩
  rw [finSol_rec 𝔼 β s one_pos, zero_add, finSol_last]
  rfl

/-- Cochrane (2023), eqs. (1.2)–(1.3), p. 8, at one date `t`: given `P_t > 0` known at `t`,
`B_t` known at `t` and (1.3), the flow condition is `v_t = s_t + βE_t v_{t+1}`
(`ExpectationSystem.PullOut`). -/
theorem flow_iff_rec (hPO : 𝔼.PullOut) {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ} {t : ℕ}
    (hP : ∀ ω, 0 < P t ω) (hk : Known 𝔼 t (P t)) (hB : Known 𝔼 t (Bm (t + 1)))
    (hQ : BondPrice 𝔼 β P Q t) :
    Flow Bm s P Q t ↔ realDebt Bm P t = s t + β • 𝔼.E t (realDebt Bm P (t + 1)) := by
  have hr : Q t * Bm (t + 1) = P t * (β • 𝔼.E t (realDebt Bm P (t + 1))) := by
    rw [hQ]
    have e1 : 𝔼.E t (Bm (t + 1) * (P t / P (t + 1))) =
        Bm (t + 1) * 𝔼.E t (P t / P (t + 1)) := hPO t _ _ hB
    have e2 : 𝔼.E t (P t * realDebt Bm P (t + 1)) = P t * 𝔼.E t (realDebt Bm P (t + 1)) :=
      hPO t _ _ hk
    have e3 : Bm (t + 1) * (P t / P (t + 1)) = P t * realDebt Bm P (t + 1) := by
      funext ω
      simp only [realDebt, Pi.mul_apply, Pi.div_apply]
      ring
    rw [e3, e2] at e1
    funext ω
    have := congrFun e1 ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination (-β) * this
  constructor
  · intro hF
    funext ω
    have e1 := congrFun hF ω
    have e2 := congrFun hr ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    have := (hP ω).ne'
    change Bm t ω / P t ω = _
    rw [e1, e2]
    field_simp
  · intro hv
    funext ω
    have e1 := congrFun hv ω
    have e2 := congrFun hr ω
    simp only [realDebt, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
      Pi.div_apply] at e1 e2 ⊢
    have := (hP ω).ne'
    rw [div_eq_iff this] at e1
    rw [e1, e2]
    ring

/-- Cochrane (2023), §§1.1–1.3, pp. 4–8, with last day `T`: **characterisation of the
equilibrium.** With positive known debt, `s_t` known at `t` for `t < T` and
`ExpectationSystem.PullOut`, `(P, Q)`
is a `T`-period equilibrium iff at every `t ≤ T` the present value
`finSol β s T t = ∑_{j ≤ T−t} β^j E_t s_{t+j}` is positive and `P_t = B_{t−1}/finSol β s T t`,
and (1.3) holds at every `t < T`. -/
theorem finEqm_iff (hPO : 𝔼.PullOut) {β : ℝ} {T : ℕ} {Bm s P Q : ℕ → Ω → ℝ}
    (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm) (hs : ∀ t < T, Known 𝔼 t (s t)) :
    FinEqm 𝔼 β T Bm s P Q ↔
      (∀ t ≤ T, ∀ ω, 0 < finSol 𝔼 β s T t ω) ∧ (∀ t ≤ T, P t = Bm t / finSol 𝔼 β s T t) ∧
        ∀ t < T, BondPrice 𝔼 β P Q t := by
  constructor
  · rintro ⟨hP, hk, hF, hQ, hv⟩
    have hrec : ∀ t < T, realDebt Bm P t = s t + β • 𝔼.E t (realDebt Bm P (t + 1)) :=
      fun t ht => (flow_iff_rec 𝔼 hPO (hP t ht.le) (hk t ht) (hB.2 t) (hQ t ht)).mp (hF t ht)
    have hsol := finSol_unique 𝔼 (z := realDebt Bm P) hv hrec
    have hpos : ∀ t ≤ T, ∀ ω, 0 < finSol 𝔼 β s T t ω := fun t ht ω => by
      rw [← hsol t ht]; exact div_pos (hBpos t ω) (hP t ht ω)
    refine ⟨hpos, fun t ht => ?_, hQ⟩
    funext ω
    have := congrFun (hsol t ht) ω
    simp only [realDebt, Pi.div_apply] at this ⊢
    rw [← this]
    field_simp [(hP t ht ω).ne', (hBpos t ω).ne']
  · rintro ⟨hpos, hPeq, hQ⟩
    have hP : ∀ t ≤ T, ∀ ω, 0 < P t ω := fun t ht ω => by
      rw [hPeq t ht]; exact div_pos (hBpos t ω) (hpos t ht ω)
    have hk : ∀ t < T, Known 𝔼 t (P t) := fun t ht => by
      rw [hPeq t ht.le]
      exact known_div 𝔼 hPO (debtKnown_at 𝔼 hB t) (finSol_known 𝔼 ht (hs t ht))
        fun ω => (hpos t ht.le ω).ne'
    have hvs : ∀ t ≤ T, realDebt Bm P t = finSol 𝔼 β s T t := fun t ht => by
      funext ω
      simp only [realDebt, Pi.div_apply, hPeq t ht]
      field_simp [(hpos t ht ω).ne', (hBpos t ω).ne']
    refine ⟨hP, hk, fun t ht => ?_, hQ, ?_⟩
    · rw [flow_iff_rec 𝔼 hPO (hP t ht.le) (hk t ht) (hB.2 t) (hQ t ht), hvs t ht.le,
        hvs (t + 1) ht]
      exact finSol_rec 𝔼 β s ht
    · have := hvs T le_rfl
      rw [finSol_last] at this
      exact this

/-- Cochrane (2023), §§1.1–1.3, pp. 4–8, with last day `T`: **existence.** If the `T`-period
present value is positive at every `t ≤ T`, the prices `P_t = B_{t−1}/finSol β s T t`,
`Q_t = βE_t(P_t/P_{t+1})` are a `T`-period equilibrium. -/
theorem finEqm_exists (hPO : 𝔼.PullOut) {β : ℝ} {T : ℕ} {Bm s : ℕ → Ω → ℝ}
    (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm) (hs : ∀ t < T, Known 𝔼 t (s t))
    (hpos : ∀ t ≤ T, ∀ ω, 0 < finSol 𝔼 β s T t ω) :
    FinEqm 𝔼 β T Bm s (fun t => Bm t / finSol 𝔼 β s T t)
      (fun t => β • 𝔼.E t (Bm t / finSol 𝔼 β s T t / (Bm (t + 1) / finSol 𝔼 β s T (t + 1)))) :=
  (finEqm_iff 𝔼 hPO hBpos hB hs).mpr ⟨hpos, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Cochrane (2023), §§1.1–1.3, pp. 4–8, with last day `T`: **uniqueness.** Two `T`-period
equilibria have the same price levels at every `t ≤ T` and the same bond prices at every
`t < T`. -/
theorem finEqm_unique (hPO : 𝔼.PullOut) {β : ℝ} {T : ℕ} {Bm s P Q P' Q' : ℕ → Ω → ℝ}
    (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm) (hs : ∀ t < T, Known 𝔼 t (s t))
    (he : FinEqm 𝔼 β T Bm s P Q) (he' : FinEqm 𝔼 β T Bm s P' Q') :
    (∀ t ≤ T, P t = P' t) ∧ ∀ t < T, Q t = Q' t := by
  obtain ⟨-, h1, h2⟩ := (finEqm_iff 𝔼 hPO hBpos hB hs).mp he
  obtain ⟨-, h1', h2'⟩ := (finEqm_iff 𝔼 hPO hBpos hB hs).mp he'
  have hPP : ∀ t ≤ T, P t = P' t := fun t ht => by rw [h1 t ht, h1' t ht]
  refine ⟨hPP, fun t ht => ?_⟩
  rw [h2 t ht, h2' t ht, hPP t ht.le, hPP (t + 1) ht]

/-! ### The limit theorem -/

/-- Cochrane (2023), §1.3, pp. 7–8 (**the infinite horizon as the limit of last days**): with
`|β| < 1`, bounded adapted surpluses, positive known debt and `ExpectationSystem.PullOut`, if
`(P^T, Q^T)` is a
`T`-period equilibrium for every `T` and the infinite-horizon present value is nonzero at
`(t, ω)`, then `P^T_t(ω) → B_{t−1}(ω)/∑_j β^j E_t s_{t+j}(ω)`, the infinite-horizon equilibrium
price level (`TidyR6InfiniteHorizon.equilibrium_iff`). -/
theorem finEqm_price_tendsto (hPO : 𝔼.PullOut) {β M : ℝ} (hβ : |β| < 1)
    {Bm s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm) {P Q : ℕ → ℕ → Ω → ℝ}
    (he : ∀ T, FinEqm 𝔼 β T Bm s (P T) (Q T)) (t : ℕ) (ω : Ω)
    (hpv : pvInf 𝔼 β s t ω ≠ 0) :
    Tendsto (fun T => P T t ω) atTop (𝓝 (Bm t ω / pvInf 𝔼 β s t ω)) := by
  have hlim := (tendsto_const_nhds (x := Bm t ω)).div (finSol_tendsto 𝔼 hβ hs hsa t ω) hpv
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  have := ((finEqm_iff 𝔼 hPO hBpos hB fun t _ => hsa t).mp (he T)).2.1 t hT
  rw [this]
  rfl

/-- Cochrane (2023), §1.3, pp. 7–8: the limit price of `finEqm_price_tendsto` is the
infinite-horizon equilibrium price: in every infinite-horizon equilibrium
`P_t = lim_T P^T_t` (same hypotheses). -/
theorem finEqm_limit_is_equilibrium (hPO : 𝔼.PullOut) {β M : ℝ} (hβ : |β| < 1)
    {Bm s : ℕ → Ω → ℝ} (hs : ∀ t ω, |s t ω| ≤ M) (hsa : 𝔼.Adapted s)
    (hBpos : ∀ t ω, 0 < Bm t ω) (hB : DebtKnown 𝔼 Bm) {P Q : ℕ → ℕ → Ω → ℝ}
    (he : ∀ T, FinEqm 𝔼 β T Bm s (P T) (Q T)) {Pinf Qinf : ℕ → Ω → ℝ}
    (hinf : TidyR6InfiniteHorizon.Equilibrium 𝔼 β Bm s Pinf Qinf) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => P T t ω) atTop (𝓝 (Pinf t ω)) := by
  obtain ⟨hpos, hPeq, -⟩ := (equilibrium_iff 𝔼 hPO hβ hs hsa hBpos hB).mp hinf
  rw [hPeq t]
  exact finEqm_price_tendsto 𝔼 hPO hβ hs hsa hBpos hB he t ω (hpos t ω).ne'

/-! ### The two-period model inside the infinite horizon -/

/-- Cochrane (2023), §1.1, p. 4 ("nobody wants to hold … bonds after the end of day 1"): an
infinite-horizon equilibrium in which the debt is retired on day 1, `B₁ = 0`, restricted to
dates 0 and 1 is a two-period equilibrium. -/
theorem restrict_twoPeriod {β : ℝ} {Bm s P Q : ℕ → Ω → ℝ} (h2 : Bm 2 = 0)
    (he : TidyR6InfiniteHorizon.Equilibrium 𝔼 β Bm s P Q) :
    Equilibrium 𝔼 β (Bm 0) (Bm 1) (s 0) (s 1) (P 0) (P 1) (Q 0) := by
  obtain ⟨hP, hPa, hF, hQ, -⟩ := he
  refine ⟨hP 0, hP 1, hPa 0, hF 0, hQ 0, ?_⟩
  funext ω
  have h := congrFun (hF 1) ω
  have h0 := congrFun h2 ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply] at h h0
  simp only [Pi.div_apply]
  rw [div_eq_iff (hP 1 ω).ne', h, h0]
  ring

/-- Cochrane (2023), §1.1, p. 4, conversely: a two-period equilibrium `(P₀, P₁, Q₀)` with `P₁`
known at date 1, continued with no debt after day 1 (`B_t = 0`, `t ≥ 1`) and no surpluses
after day 1, any positive adapted prices after day 1 and `Q_t = βE_t(P_t/P_{t+1})`, is an
infinite-horizon equilibrium. -/
theorem extend_twoPeriod {β : ℝ} {Bm s P : ℕ → Ω → ℝ}
    (hBm : ∀ t, 2 ≤ t → Bm t = 0) (hs : ∀ t, 2 ≤ t → s t = 0)
    (hP : ∀ t, 2 ≤ t → ∀ ω, 0 < P t ω) (hPa : ∀ t, 1 ≤ t → Known 𝔼 t (P t))
    (he : Equilibrium 𝔼 β (Bm 0) (Bm 1) (s 0) (s 1) (P 0) (P 1)
      (β • 𝔼.E 0 (P 0 / P 1))) :
    TidyR6InfiniteHorizon.Equilibrium 𝔼 β Bm s P (fun t => β • 𝔼.E t (P t / P (t + 1))) := by
  obtain ⟨hP0, hP1, hk0, hF0, -, hv⟩ := he
  have hPall : ∀ t ω, 0 < P t ω := fun t ω => by
    rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t
      · exact hP0 ω
      · exact hP1 ω
    · exact hP t h ω
  refine ⟨hPall, fun t => ?_, fun t => ?_, fun _ => rfl, fun t ω => ?_⟩
  · rcases Nat.eq_zero_or_pos t with rfl | h
    · exact hk0
    · exact hPa t h
  · rcases Nat.lt_or_ge t 2 with h | h
    · interval_cases t
      · exact hF0
      · funext ω
        have e := congrFun hv ω
        have h2 := congrFun (hBm 2 le_rfl) ω
        simp only [Pi.div_apply] at e
        rw [div_eq_iff (hP1 ω).ne'] at e
        simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply] at h2 ⊢
        rw [h2, e]; ring
    · funext ω
      have e1 := congrFun (hBm t h) ω
      have e2 := congrFun (hBm (t + 1) (by omega)) ω
      have e3 := congrFun (hs t h) ω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.zero_apply] at e1 e2 e3 ⊢
      rw [e1, e2, e3]; ring
  · have hz : ∀ T : ℕ, 2 ≤ T → 𝔼.E t (realDebt Bm P (t + T)) = 0 := fun T hT => by
      have : realDebt Bm P (t + T) = 0 := by
        funext ω'
        simp only [realDebt, Pi.div_apply, hBm (t + T) (by omega), Pi.zero_apply, zero_div]
      rw [this, map_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with T hT
    rw [hz T hT, Pi.zero_apply, mul_zero]

/-! ### Active and passive rules with a last day -/

/-- Cochrane (2023), §1.9, pp. 18–19, with last day `T`: under the rule `s_t = γv_t + ŝ_t` a
`T`-period equilibrium has `(1 − γ)v_T = ŝ_T` and `(1 − γ)v_t = ŝ_t + βE_t v_{t+1}` for `t < T`
(positive known debt, `ExpectationSystem.PullOut`). -/
theorem finRule_rec (hPO : 𝔼.PullOut) {β γ : ℝ} {T : ℕ} {shat Bm P Q : ℕ → Ω → ℝ}
    (hB : DebtKnown 𝔼 Bm) (he : FinEqm 𝔼 β T Bm (ruleSurplus γ shat Bm P) P Q) :
    (1 - γ) • realDebt Bm P T = shat T ∧
      ∀ t < T, (1 - γ) • realDebt Bm P t = shat t + β • 𝔼.E t (realDebt Bm P (t + 1)) := by
  obtain ⟨hP, hk, hF, hQ, hv⟩ := he
  refine ⟨?_, fun t ht => ?_⟩
  · funext ω
    have e := congrFun hv ω
    simp only [ruleSurplus, realDebt, Pi.div_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    linarith
  · have h := (flow_iff_rec 𝔼 hPO (hP t ht.le) (hk t ht) (hB.2 t) (hQ t ht)).mp (hF t ht)
    funext ω
    have e := congrFun h ω
    simp only [ruleSurplus, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith

/-- Cochrane (2023), §1.9, pp. 18–19 (**with a last day every `γ ≠ 1` is active**): for
`γ ≠ 1` the real debt of every `T`-period rule equilibrium is the backward solution
`v_t = finSol (β/(1 − γ)) (ŝ/(1 − γ)) T t` at every `t ≤ T`. -/
theorem finRule_realDebt (hPO : 𝔼.PullOut) {β γ : ℝ} (hγ : γ ≠ 1) {T : ℕ}
    {shat Bm P Q : ℕ → Ω → ℝ} (hB : DebtKnown 𝔼 Bm)
    (he : FinEqm 𝔼 β T Bm (ruleSurplus γ shat Bm P) P Q) :
    ∀ t ≤ T, realDebt Bm P t =
      finSol 𝔼 (β / (1 - γ)) (fun t => (1 - γ)⁻¹ • shat t) T t := by
  have hc : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  obtain ⟨hT, hrec⟩ := finRule_rec 𝔼 hPO hB he
  refine finSol_unique 𝔼 ?_ fun t ht => ?_
  · funext ω
    have e := congrFun hT ω
    simp only [Pi.smul_apply, smul_eq_mul] at e ⊢
    field_simp
    linarith
  · funext ω
    have e := congrFun (hrec t ht) ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at e ⊢
    field_simp
    linarith

/-- Cochrane (2023), §1.9, p. 19, with last day `T` (the passive rule): for `γ = 1` the last-day
condition reads `ŝ_T = 0`; when it holds, every positive last-day price level `P_T` satisfies
the last-day valuation equation of the rule. -/
theorem finRule_gamma_one {T : ℕ} {shat Bm P : ℕ → Ω → ℝ} :
    Valuation1 (Bm T) (P T) (ruleSurplus 1 shat Bm P T) ↔ shat T = 0 := by
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [ruleSurplus, realDebt, Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      one_mul] at e
    simp only [Pi.zero_apply]
    linarith
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [ruleSurplus, realDebt, Pi.div_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      one_mul, Pi.zero_apply] at e ⊢
    rw [e, add_zero]

/-- Cochrane (2023), §1.9, pp. 18–19 (**truncation selects the forward solution**): for
`|1 − γ| > β` (all active `γ`, and the passive `γ` with `β < |1 − γ| < 1`), bounded adapted
`ŝ`, the real debt of `T`-period rule equilibria converges as `T → ∞` to `ruleF`, the
infinite-horizon forward value: the unique infinite-horizon equilibrium value for `γ ≤ 0` or
`γ ≥ 2` (`TidyR6InfiniteActivePassive.active_valuation`), one of a continuum for `0 < γ < 2`
(`TidyR6InfiniteActivePassive.passive_indeterminate`). -/
theorem finRule_tendsto (hPO : 𝔼.PullOut) {β γ M : ℝ} (hβ0 : 0 < β) (hγβ : β < |1 - γ|)
    {shat Bm : ℕ → Ω → ℝ} (hs : ∀ t ω, |shat t ω| ≤ M) (hsa : 𝔼.Adapted shat)
    (hB : DebtKnown 𝔼 Bm) {P Q : ℕ → ℕ → Ω → ℝ}
    (he : ∀ T, FinEqm 𝔼 β T Bm (ruleSurplus γ shat Bm (P T)) (P T) (Q T)) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => realDebt Bm (P T) t ω) atTop (𝓝 (ruleF 𝔼 β γ shat t ω)) := by
  have hcpos : 0 < |1 - γ| := lt_trans hβ0 hγβ
  have hγ : γ ≠ 1 := fun h => by rw [h, sub_self, abs_zero] at hcpos; exact lt_irrefl 0 hcpos
  have ha1 : |β / (1 - γ)| < 1 := by
    rw [abs_div, abs_of_pos hβ0, div_lt_one hcpos]; exact hγβ
  have huM : ∀ t ω, |((1 - γ)⁻¹ • shat t) ω| ≤ |1 - γ|⁻¹ * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv]
    exact mul_le_mul_of_nonneg_left (hs t ω) (inv_nonneg.mpr (abs_nonneg _))
  have hua : 𝔼.Adapted (fun t => (1 - γ)⁻¹ • shat t) := fun t => by simp only [map_smul, hsa t]
  refine (finSol_tendsto 𝔼 ha1 huM hua t ω).congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [finRule_realDebt 𝔼 hPO hγ hB (he T) t hT]

/-- Cochrane (2023), §1.9, pp. 18–19 (**the last-day selection can diverge**): for
`1 − β < γ < 1` (so `a = β/(1 − γ) > 1`), under perfect foresight with `ŝ ≡ 1 − γ`, the
truncated backward solution at date 0 grows without bound as the last day recedes. -/
theorem truncation_diverges {β γ : ℝ} (hβ : 0 < β) (hγ1 : γ < 1) (hγβ : 1 - β < γ) :
    Tendsto (fun T => finSol perfectForesight (β / (1 - γ))
      (fun t => (1 - γ)⁻¹ • ((fun (_ : ℕ) (_ : Unit) => (1 - γ : ℝ)) t)) T 0 ()) atTop atTop := by
  have hc : 0 < 1 - γ := by linarith
  have ha : 1 < β / (1 - γ) := by rw [one_lt_div hc]; linarith
  have hua : perfectForesight.Adapted
      (fun t => (1 - γ)⁻¹ • ((fun (_ : ℕ) (_ : Unit) => (1 - γ : ℝ)) t)) := fun _ => rfl
  have hval : ∀ T, finSol perfectForesight (β / (1 - γ))
      (fun t => (1 - γ)⁻¹ • ((fun (_ : ℕ) (_ : Unit) => (1 - γ : ℝ)) t)) T 0 () =
        ∑ j ∈ Finset.range (T + 1), (β / (1 - γ)) ^ j := by
    intro T
    rw [finSol_closed perfectForesight hua (Nat.zero_le T), Nat.sub_zero]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, perfectForesight,
      LinearMap.id_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  simp_rw [hval]
  refine tendsto_atTop_mono (f := fun T : ℕ => ((T : ℝ) + 1)) (fun T => ?_) ?_
  · calc ((T : ℝ) + 1) = ∑ _j ∈ Finset.range (T + 1), (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ Finset.range (T + 1), (β / (1 - γ)) ^ j :=
          Finset.sum_le_sum fun j _ => one_le_pow₀ ha.le
  · exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

end Cochrane.TwoPeriodModel.TidyR6Truncation
