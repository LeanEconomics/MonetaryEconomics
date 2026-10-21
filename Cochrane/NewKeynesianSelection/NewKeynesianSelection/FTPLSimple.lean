/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.Innovation

/-!
# The simple fiscal-theory model of monetary policy, and Chapter 12

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.5–2.6, eqs. (2.16)–(2.25),
pp. 34–42, the model that Chapter 16 reads differently (eqs. (16.1)–(16.3), p. 364); and the
precise claims of Chapter 12, "Interest-rate targets", pp. 324–328.

The first part is restated from the Chapter 2 project (`LinearFTMP`), adapted to the
`Cochrane.NewKeynesianSelection` names and to the `Innovation` module. Variables are deviations
from steady state; inflation, rates and shocks are random variables at each date; expectations
are an arbitrary `ExpectationSystem`.

The fiscal-theory equilibrium notion: given an adapted interest-rate path (or an interest-rate
rule with adapted disturbance), a fiscal shock `ε_{Σs}` (the innovation in the present value of
surpluses, `pvNews`) and initial inflation `π_0` (set by date-0 fiscal news), an equilibrium is
an ADAPTED inflation process satisfying the Fisher equation `i_t = E_t π_{t+1}` and the fiscal
condition `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` at every date. No boundedness is imposed: the price
level is determined by the valuation equation, not by ruling out explosive paths.

## Main results

* (2.17): `pvNews`, `innov_forwardSeries`, `pvNews_isShock` (the fiscal shock is a shock).
* (2.19): `pegModel_iff`, `peg_existsUnique`, `pegSol_bounded`; `irf_peg_impact`,
  `irf_peg_later`, `expected_inflation_ahead`.
* p. 39: `passiveShock_isShock`, `passive_any_innovation` (under passive fiscal policy every
  innovation is an equilibrium).
* (2.20)–(2.25): `ruleModel_iff`, `eq224_iff`, `rule_existsUnique` (every `θ`), `rule_eq_peg`,
  `ruleSol_bounded`, `ruleSol_unbounded`.
* Chapter 12, P3 (p. 326, "a peg can be stable, determinate and quiet"): `peg_stable_determinate`,
  `peg_quiet`, `peg_unexpected_sq` (the conditional variance of unexpected inflation is that of
  the fiscal shock; volatile fiscal policy means volatile unexpected inflation).
* Chapter 12, P2 contrast (p. 325, Sargent–Wallace): `fisher_alone_any_innovation` (the Fisher
  equation alone leaves unexpected inflation arbitrary).
* Chapter 12, P4–P5 (p. 326), with a real rate `r_t`: `PegModelR`, `pegR_iff`,
  `pegR_existsUnique`, `pegR_expected` (`E_t π_{t+1} = i_t − r_t`: the real rate passes one for
  one into expected inflation), `real_rate_passthrough`, `zero_peg_deflation` and
  `peg_steady_state_iff` (a peg at zero gives the deflation `π = −r`).
* Chapter 12, P6 (p. 327, "if `φ > 1`, inflation is determinate but unstable"):
  `rule_expected_path` (`E_t π_{t+j} = φʲ π_t`), `rule_determinate_unstable`
  (unique equilibrium for every `φ`, yet `|E_t π_{t+j}| → ∞` whenever `π_t ≠ 0` and
  `|φ| > 1`), `rule_stable` (`|φ| < 1`: expected inflation converges to zero).
-/

namespace Cochrane.NewKeynesianSelection.FTPLSimple

open Filter Topology Innovation

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (2.17): fiscal news (restated from the Chapter 2 project) -/

/-- Cochrane (2023), eqs. (2.7) and (2.17), pp. 22, 35: for bounded surpluses and `0 ≤ β < 1`
the discounted forecasts `∑ βᵏ E_n s_{t+k}` are absolutely summable.
(Restated from the Chapter 2 project, `ExpectationTools.summable_E_shift`.) -/
theorem summable_E_shift {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (n t : ℕ) (ω : Ω) :
    Summable (fun k => β ^ k * 𝔼.E n (s (t + k)) ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h0 h1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + k)) n ω) (pow_nonneg h0 k)

/-- Cochrane (2023), eq. (2.17), p. 35: the shock to the present value of (scaled) surpluses,
`ε_{Σs,t+1} = ΔE_{t+1} ∑_{j ≥ 0} βʲ s̃_{t+1+j} = ∑_{j ≥ 0} βʲ ΔE_{t+1} s̃_{t+1+j}`.
(Restated from the Chapter 2 project.) -/
noncomputable def pvNews (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω

/-- Cochrane (2023), eqs. (2.17)–(2.18), p. 35: `E_t PV_{t+1} = ∑_{k ≥ 0} βᵏ E_t s_{t+1+k}`, with
`PV_{t+1} = E_{t+1} ∑ βᵏ s_{t+1+k}` the forward series (bounded surpluses, `0 ≤ β < 1`).
(Restated from the Chapter 2 project.) -/
theorem E_forwardSeries_succ {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) (ω : Ω) :
    𝔼.E t (𝔼.forwardSeries β s (t + 1)) ω = ∑' k, β ^ k * 𝔼.E t (s (t + 1 + k)) ω := by
  have hb : ∀ k ω', |β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + 1 + k)) (t + 1) ω') (pow_nonneg h0 k)
  change 𝔼.E t (fun ω' => ∑' k, β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω') ω = _
  rw [𝔼.E_tsum h0 h1 hb t ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E t (β ^ k • 𝔼.E (t + 1) (s (t + 1 + k))) ω = _
  rw [map_smul, 𝔼.tower (Nat.le_succ t), Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), eq. (2.17), p. 35: the innovation in the present value of surpluses is the
discounted sum of the innovations in each future surplus,
`ΔE_{t+1} PV_{t+1} = ∑_{k ≥ 0} βᵏ ΔE_{t+1} s_{t+1+k}` (bounded surpluses, `0 ≤ β < 1`).
(Restated from the Chapter 2 project.) -/
theorem innov_forwardSeries {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    innov 𝔼 t (𝔼.forwardSeries β s (t + 1)) = pvNews 𝔼 β s t := by
  funext ω
  unfold innov pvNews
  rw [𝔼.forwardSeries_adapted h0 h1 hs (t + 1), Pi.sub_apply,
    E_forwardSeries_succ 𝔼 h0 h1 hs t ω]
  change ∑' k, β ^ k * 𝔼.E (t + 1) (s (t + 1 + k)) ω - _ = _
  rw [← (summable_E_shift 𝔼 h0 h1 hs (t + 1) (t + 1) ω).tsum_sub
    (summable_E_shift 𝔼 h0 h1 hs t (t + 1) ω)]
  refine tsum_congr fun k => ?_
  rw [← mul_sub]
  rfl

/-- Cochrane (2023), eq. (2.17), p. 35: the fiscal news `ε_{Σs,t+1}` is a shock in the sense of
p. 40 (bounded surpluses, `0 ≤ β < 1`).
(Restated from the Chapter 2 project.) -/
theorem pvNews_isShock {β M : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) : IsShock 𝔼 (fun t => match t with
      | 0 => 0
      | t + 1 => pvNews 𝔼 β s t) := by
  have hb : ∀ t k ω', |β ^ k * innov 𝔼 t (s (t + 1 + k)) ω'| ≤ β ^ k * (2 * M) := by
    intro t k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg h0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg h0 k)
    unfold innov
    rw [Pi.sub_apply, two_mul]
    exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hs _) _ ω') (𝔼.abs_E_le (hs _) _ ω'))
  constructor
  · intro t
    funext ω
    change 𝔼.E (t + 1) (fun ω' => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = _
    rw [𝔼.E_tsum h0 h1 (hb t) (t + 1) ω]
    refine tsum_congr fun k => ?_
    change 𝔼.E (t + 1) (β ^ k • innov 𝔼 t (s (t + 1 + k))) ω = _
    rw [map_smul, innov_known_next, Pi.smul_apply, smul_eq_mul]
  · intro t
    funext ω
    change 𝔼.E t (fun ω' => ∑' k, β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = 0
    rw [𝔼.E_tsum h0 h1 (hb t) t ω]
    have : ∀ k, 𝔼.E t (fun ω' => β ^ k * innov 𝔼 t (s (t + 1 + k)) ω') ω = 0 := by
      intro k
      change 𝔼.E t (β ^ k • innov 𝔼 t (s (t + 1 + k))) ω = 0
      rw [map_smul, E_innov_zero, smul_zero, Pi.zero_apply]
    simp only [this, tsum_zero]

/-- Cochrane (2023), eqs. (2.16)–(2.17), p. 35 (the linear model, variables as deviations from
steady state): `i_t = E_t π_{t+1}` and `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` at every date.
(Restated from the Chapter 2 project.) -/
def PegModel (i ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), eq. (2.19), p. 36: for adapted inflation, an adapted rate path and a fiscal
shock, the model (2.16)–(2.17) holds iff `π_{t+1} = i_t − ε_{Σs,t+1}` at every date.
(Restated from the Chapter 2 project.) -/
theorem pegModel_iff {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hi : 𝔼.Adapted i)
    (hε : IsShock 𝔼 ε) : PegModel 𝔼 i ε π ↔ ∀ t, π (t + 1) = i t - ε (t + 1) := by
  constructor
  · intro h t
    rw [eq_E_add_innov 𝔼 (hπ (t + 1)), ← (h t).1, (h t).2, sub_eq_add_neg]
  · intro h t
    have hE : 𝔼.E t (π (t + 1)) = i t := by
      rw [h t, map_sub, hi t, hε.2 t, sub_zero]
    refine ⟨hE.symm, ?_⟩
    unfold innov
    rw [hE, h t, map_sub, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hi t), hε.1 t]
    abel

/-- Cochrane (2023), eq. (2.19), p. 36: the solution `π_0` given, `π_{t+1} = i_t − ε_{Σs,t+1}`.
(Restated from the Chapter 2 project.) -/
def pegSol (i ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => i t - ε (t + 1)

/-- Cochrane (2023), eq. (2.19), p. 36: the solution is adapted.
(Restated from the Chapter 2 project.) -/
theorem pegSol_adapted {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) : 𝔼.Adapted (pegSol i ε π0) := by
  intro t
  cases t with
  | zero => exact h0
  | succ t =>
    change 𝔼.E (t + 1) (i t - ε (t + 1)) = i t - ε (t + 1)
    rw [map_sub, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hi t), hε.1 t]

/-- Cochrane (2023), eq. (2.19), p. 36 ("the full solution of the model"): for EVERY adapted rate
path `i` and every fiscal shock `ε_{Σs}`, given `π_0` (set by date-0 fiscal news), the model
(2.16)–(2.17) has exactly one adapted solution. No boundedness is imposed.
(Restated from the Chapter 2 project.) -/
theorem peg_existsUnique {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) :
    ∃! π, 𝔼.Adapted π ∧ π 0 = π0 ∧ PegModel 𝔼 i ε π := by
  have ha := pegSol_adapted 𝔼 h0 hi hε
  refine ⟨pegSol i ε π0, ⟨ha, rfl, (pegModel_iff 𝔼 ha hi hε).mpr fun t => rfl⟩, ?_⟩
  rintro π ⟨hπ, hπ0, hm⟩
  have h := (pegModel_iff 𝔼 hπ hi hε).mp hm
  funext t
  cases t with
  | zero => exact hπ0
  | succ t => exact h t

/-- Cochrane (2023), pp. 33, 37 ("inflation is stable under an interest-rate target"): with
bounded `π_0`, rates and shocks the solution (2.19) is bounded.
(Restated from the Chapter 2 project.) -/
theorem pegSol_bounded {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} {A Bi Be : ℝ} (h0 : ∀ ω, |π0 ω| ≤ A)
    (hi : ∀ t ω, |i t ω| ≤ Bi) (hε : ∀ t ω, |ε t ω| ≤ Be) :
    BoundedProc (pegSol i ε π0) := by
  refine ⟨|A| + |Bi| + |Be|, fun t ω => ?_⟩
  cases t with
  | zero =>
    have := (h0 ω).trans (le_abs_self A)
    change |π0 ω| ≤ _
    linarith [abs_nonneg Bi, abs_nonneg Be]
  | succ t =>
    change |i t ω - ε (t + 1) ω| ≤ _
    have h1 := (hi t ω).trans (le_abs_self Bi)
    have h2 := (hε (t + 1) ω).trans (le_abs_self Be)
    linarith [abs_sub (i t ω) (ε (t + 1) ω), abs_nonneg A]

/-- Cochrane (2023), Figure 2.1 and p. 36 ("there is no unexpected time-`t` inflation without a
fiscal shock"): on impact, `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` whatever the rate news.
(Restated from the Chapter 2 project.) -/
theorem irf_peg_impact {i ε π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (t : ℕ) :
    innov 𝔼 t (π (t + 1)) = -ε (t + 1) := by
  rw [h t, innov_sub, innov_of_known 𝔼 (hi t)]
  unfold innov
  rw [hε.1 t, hε.2 t]
  abel

/-- Cochrane (2023), Figure 2.1 and p. 36 ("inflation moves up one period later"): after impact
the inflation response is the rate response one period earlier,
`ΔE_{t+1} π_{t+2+j} = ΔE_{t+1} i_{t+1+j}`.
(Restated from the Chapter 2 project.) -/
theorem irf_peg_later {i ε π : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) (t j : ℕ) :
    innov 𝔼 t (π (t + 2 + j)) = innov 𝔼 t (i (t + 1 + j)) := by
  have e : t + 2 + j = t + 1 + j + 1 := by omega
  rw [e, h, innov_sub, ← e, innov_shock_later 𝔼 hε, sub_zero]

/-- Cochrane (2023), p. 36 ("If `E_{t−k} i_t` rises, then `E_{t−k} π_{t+1}` rises"): for every
`s ≤ t`, `E_s π_{t+1} = E_s i_t`.
(Restated from the Chapter 2 project.) -/
theorem expected_inflation_ahead {i ε π : ℕ → Ω → ℝ} (hε : IsShock 𝔼 ε)
    (h : ∀ t, π (t + 1) = i t - ε (t + 1)) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (π (t + 1)) = 𝔼.E s (i t) := by
  rw [h t, map_sub, ← 𝔼.tower hst (ε (t + 1)), hε.2 t, map_zero, sub_zero]

/-- Cochrane (2023), p. 39: the passive fiscal policy of the new-Keynesian reading,
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` "in response to whatever inflation happens".
(Restated from the Chapter 2 project.) -/
def passiveShock (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => -innov 𝔼 t (π (t + 1))

/-- Cochrane (2023), p. 39 and (16.3), p. 364: the passive fiscal response
`ε_{Σs,t+1} = −ΔE_{t+1} π_{t+1}` to any inflation process is a shock. -/
theorem passiveShock_isShock (π : ℕ → Ω → ℝ) : IsShock 𝔼 (passiveShock 𝔼 π) :=
  ⟨fun t => by simp only [passiveShock, map_neg, innov_known_next],
    fun t => by simp only [passiveShock, map_neg, E_innov_zero, neg_zero]⟩

/-- Cochrane (2023), p. 39: under passive fiscal policy the valuation equation holds for every
inflation path satisfying the Fisher equation.
(Restated from the Chapter 2 project.) -/
theorem passive_valuation_holds {i π : ℕ → Ω → ℝ} (hfis : ∀ t, i t = 𝔼.E t (π (t + 1))) :
    PegModel 𝔼 i (passiveShock 𝔼 π) π := fun t => ⟨hfis t, by
      change _ = -(-innov 𝔼 t (π (t + 1)))
      rw [neg_neg]⟩

/-- Cochrane (2023), p. 39 ("The bank threatens hyperinflation for any but one value of
unexpected inflation"): with passive fiscal policy, EVERY shock `ν` is an equilibrium inflation
innovation: `π_{t+1} = i_t + ν_{t+1}` is adapted, satisfies the model with the passive fiscal
response, and has `ΔE_{t+1} π_{t+1} = ν_{t+1}`.
(Restated from the Chapter 2 project.) -/
theorem passive_any_innovation {i ν : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hν : IsShock 𝔼 ν) :
    𝔼.Adapted (pegSol i (fun t => -ν t) π0) ∧
      PegModel 𝔼 i (passiveShock 𝔼 (pegSol i (fun t => -ν t) π0)) (pegSol i (fun t => -ν t) π0) ∧
      ∀ t, innov 𝔼 t (pegSol i (fun t => -ν t) π0 (t + 1)) = ν (t + 1) := by
  have hs : IsShock 𝔼 (fun t => -ν t) :=
    ⟨fun t => by rw [map_neg, hν.1 t], fun t => by rw [map_neg, hν.2 t, neg_zero]⟩
  have ha := pegSol_adapted 𝔼 h0 hi hs
  have hm := (pegModel_iff 𝔼 ha hi hs).mpr fun t => rfl
  refine ⟨ha, passive_valuation_holds 𝔼 fun t => (hm t).1, fun t => ?_⟩
  rw [(hm t).2, neg_neg]

/-- Cochrane (2023), eqs. (2.20)–(2.22), p. 40: `i_t = E_t π_{t+1}`,
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` and the Taylor-type rule `i_t = θ π_t + u_t`.
(Restated from the Chapter 2 project.) -/
def RuleModel (θ : ℝ) (i u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1) ∧ i t = θ • π t + u t

/-- Cochrane (2023), eq. (2.23), p. 40: the serially correlated disturbance
`u_t = η u_{t−1} + ε_{i,t}`.
(Restated from the Chapter 2 project.) -/
def Disturbance (η : ℝ) (u εi : ℕ → Ω → ℝ) : Prop := ∀ t, u (t + 1) = η • u t + εi (t + 1)

/-- Cochrane (2023), eq. (2.24) with (2.21), p. 40: `E_t π_{t+1} = θ π_t + u_t` and
`ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}`.
(Restated from the Chapter 2 project.) -/
def Eq224 (θ : ℝ) (u ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + u t ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), eqs. (2.20)–(2.24), p. 40 ("Eliminating the interest rate"): the model
(2.20)–(2.22) holds iff the rate is given by the rule and inflation satisfies (2.24), (2.21).
(Restated from the Chapter 2 project.) -/
theorem ruleModel_iff {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} :
    RuleModel 𝔼 θ i u ε π ↔ (∀ t, i t = θ • π t + u t) ∧ Eq224 𝔼 θ u ε π := by
  constructor
  · intro h
    exact ⟨fun t => (h t).2.2, fun t => ⟨(h t).1.symm.trans (h t).2.2, (h t).2.1⟩⟩
  · rintro ⟨hi, h⟩ t
    exact ⟨(hi t).trans (h t).1.symm, (h t).2, hi t⟩

/-- Cochrane (2023), eq. (2.25), p. 40: for adapted inflation and disturbance and a fiscal shock,
(2.24) with (2.21) holds iff `π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`.
(Restated from the Chapter 2 project.) -/
theorem eq224_iff {θ : ℝ} {u ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 ε) :
    Eq224 𝔼 θ u ε π ↔ ∀ t, π (t + 1) = θ • π t + u t - ε (t + 1) := by
  have hk : ∀ t, 𝔼.E t (θ • π t + u t) = θ • π t + u t := fun t => by
    rw [map_add, map_smul, hπ t, hu t]
  constructor
  · intro h t
    rw [eq_E_add_innov 𝔼 (hπ (t + 1)), (h t).1, (h t).2, sub_eq_add_neg]
  · intro h t
    refine ⟨?_, ?_⟩
    · rw [h t, map_sub, hk t, hε.2 t, sub_zero]
    · rw [h t, innov_sub, innov_of_known 𝔼 (hk t), innov_shock 𝔼 hε, zero_sub]

/-- Cochrane (2023), eq. (2.25), p. 40: the solution `π_0` given,
`π_{t+1} = θ π_t + u_t − ε_{Σs,t+1}`.
(Restated from the Chapter 2 project.) -/
def ruleSol (θ : ℝ) (u ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => θ • ruleSol θ u ε π0 t + u t - ε (t + 1)

/-- Cochrane (2023), eq. (2.25), p. 40: the solution is adapted.
(Restated from the Chapter 2 project.) -/
theorem ruleSol_adapted {θ : ℝ} {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε) : 𝔼.Adapted (ruleSol θ u ε π0) := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    change 𝔼.E (t + 1) (θ • ruleSol θ u ε π0 t + u t - ε (t + 1)) = _
    rw [map_sub, map_add, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hu t), hε.1 t]
    rfl

/-- Cochrane (2023), eqs. (2.20)–(2.25), p. 40, the fiscal-theory point of §2.6: for EVERY rule
coefficient `θ ∈ ℝ` (no Taylor principle), every adapted disturbance `u` and every fiscal shock,
given `π_0`, there is exactly one equilibrium `(π, i)` of (2.20)–(2.22) with `π` adapted.
(Restated from the Chapter 2 project.) -/
theorem rule_existsUnique (θ : ℝ) {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hu : 𝔼.Adapted u) (hε : IsShock 𝔼 ε) :
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 ∧ q.1 0 = π0 ∧
      RuleModel 𝔼 θ q.2 u ε q.1 := by
  have ha := ruleSol_adapted 𝔼 (θ := θ) h0 hu hε
  refine ⟨(ruleSol θ u ε π0, fun t => θ • ruleSol θ u ε π0 t + u t), ⟨ha, rfl, ?_⟩, ?_⟩
  · exact (ruleModel_iff 𝔼).mpr ⟨fun t => rfl, (eq224_iff 𝔼 ha hu hε).mpr fun t => rfl⟩
  · rintro ⟨π, i⟩ ⟨hπ, hπ0, hm⟩
    obtain ⟨hi, h224⟩ := (ruleModel_iff 𝔼).mp hm
    have h := (eq224_iff 𝔼 hπ hu hε).mp h224
    dsimp only at hπ0 hi h
    have hπeq : π = ruleSol θ u ε π0 := by
      funext t
      induction t with
      | zero => exact hπ0
      | succ t ih =>
        rw [h t, ih]
        rfl
    refine Prod.ext hπeq ?_
    funext t
    change i t = θ • ruleSol θ u ε π0 t + u t
    rw [hi t, hπeq]

/-- Cochrane (2023), p. 40 ("if we had fed the equilibrium `{i_t}` response ... into the
calculation (2.19) ... as if that path were an exogenous time-varying peg, we would have obtained
the same result"): a solution of the rule model solves the peg model (2.16)–(2.17) with the
equilibrium rate, and equals the peg solution (2.19) for that rate.
(Restated from the Chapter 2 project.) -/
theorem rule_eq_peg {θ : ℝ} {i u ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.Adapted u)
    (hε : IsShock 𝔼 ε) (hm : RuleModel 𝔼 θ i u ε π) :
    PegModel 𝔼 i ε π ∧ π = pegSol i ε (π 0) := by
  have hpeg : PegModel 𝔼 i ε π := fun t => ⟨(hm t).1, (hm t).2.1⟩
  have hi : 𝔼.Adapted i := fun t => by rw [(hm t).2.2, map_add, map_smul, hπ t, hu t]
  refine ⟨hpeg, ?_⟩
  have h := (pegModel_iff 𝔼 hπ hi hε).mp hpeg
  funext t
  cases t with
  | zero => rfl
  | succ t => exact h t

/-- Cochrane (2023), §2.6 (survey item E30): for `|θ| < 1` and bounded `π_0`, disturbance and
shocks, the equilibrium (2.25) is bounded.
(Restated from the Chapter 2 project.) -/
theorem ruleSol_bounded {θ A Bu Be : ℝ} (hθ : |θ| < 1) {u ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ}
    (h0 : ∀ ω, |π0 ω| ≤ A) (hu : ∀ t ω, |u t ω| ≤ Bu) (hε : ∀ t ω, |ε t ω| ≤ Be) :
    BoundedProc (ruleSol θ u ε π0) := by
  set K := |A| + (|Bu| + |Be|) / (1 - |θ|) with hK
  have h1 : 0 < 1 - |θ| := by linarith
  have hfrac : 0 ≤ (|Bu| + |Be|) / (1 - |θ|) := div_nonneg (by positivity) h1.le
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact fun ω => (h0 ω).trans ((le_abs_self A).trans (by linarith))
  | succ t ih =>
    intro ω
    change |θ * ruleSol θ u ε π0 t ω + u t ω - ε (t + 1) ω| ≤ K
    have ha : |θ * ruleSol θ u ε π0 t ω| ≤ |θ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have hb := (hu t ω).trans (le_abs_self Bu)
    have hc := (hε (t + 1) ω).trans (le_abs_self Be)
    have hKe : K * (1 - |θ|) = |A| * (1 - |θ|) + (|Bu| + |Be|) := by
      rw [hK, add_mul, div_mul_cancel₀ _ h1.ne']
    have hB : 0 ≤ |A| * (1 - |θ|) := mul_nonneg (abs_nonneg A) h1.le
    calc |θ * ruleSol θ u ε π0 t ω + u t ω - ε (t + 1) ω|
        ≤ |θ * ruleSol θ u ε π0 t ω + u t ω| + |ε (t + 1) ω| := abs_sub _ _
      _ ≤ |θ * ruleSol θ u ε π0 t ω| + |u t ω| + |ε (t + 1) ω| := by
          gcongr; exact abs_add_le _ _
      _ ≤ K := by nlinarith

/-- Cochrane (2023), §2.6 (survey item E30): for `|θ| > 1` the equilibrium is unbounded as soon
as inflation starts away from zero (no disturbances or shocks: `π_t = θᵗ π_0`), so the
linearisation of §2.5 is not justified along it; the equilibrium still exists and is unique.
(Restated from the Chapter 2 project.) -/
theorem ruleSol_unbounded {θ : ℝ} (hθ : 1 < |θ|) {π0 : Ω → ℝ} {ω : Ω} (hω : π0 ω ≠ 0) :
    ¬ BoundedProc (ruleSol θ 0 0 π0) := by
  have hpow : ∀ t, ruleSol θ 0 0 π0 t ω = θ ^ t * π0 ω := by
    intro t
    induction t with
    | zero => simp [ruleSol]
    | succ t ih =>
      change θ * ruleSol θ 0 0 π0 t ω + 0 - 0 = _
      rw [ih, pow_succ]
      ring
  rintro ⟨M, hM⟩
  have hpos : 0 < |π0 ω| := abs_pos.mpr hω
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hθ).eventually_gt_atTop
    (M / |π0 ω|)).exists
  have h1 := hM t ω
  rw [hpow t, abs_mul, abs_pow] at h1
  rw [div_lt_iff₀ hpos] at ht
  linarith

/-! ### Chapter 12, P3: a peg can be stable, determinate and quiet -/

/-- Cochrane (2023), §12.1, p. 326 (P3: "an interest-rate peg can leave the price level and
inflation stable, determinate, and quiet"): under a peg, for every adapted rate path, every
fiscal shock and every `π_0` there is exactly one equilibrium (determinate); it is bounded when
the rate path, the shock and `π_0` are (stable); and its unexpected inflation is minus the fiscal
shock, whatever the rate path. -/
theorem peg_stable_determinate {i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} {A Bi Be : ℝ}
    (h0 : 𝔼.E 0 π0 = π0) (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) (hA : ∀ ω, |π0 ω| ≤ A)
    (hBi : ∀ t ω, |i t ω| ≤ Bi) (hBe : ∀ t ω, |ε t ω| ≤ Be) :
    (∃! π, 𝔼.Adapted π ∧ π 0 = π0 ∧ PegModel 𝔼 i ε π) ∧ BoundedProc (pegSol i ε π0) ∧
      ∀ t, innov 𝔼 t (pegSol i ε π0 (t + 1)) = -ε (t + 1) :=
  ⟨peg_existsUnique 𝔼 h0 hi hε, pegSol_bounded hA hBi hBe,
    irf_peg_impact 𝔼 hi hε (fun _ => rfl)⟩

/-- Cochrane (2023), §12.1, p. 326 ("quiet (the opposite of volatile)"): with no fiscal news
there is no unexpected inflation under a peg, and inflation `π_{t+1} = i_t` is known one period
ahead. -/
theorem peg_quiet {i π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hi : 𝔼.Adapted i)
    (hm : PegModel 𝔼 i 0 π) (t : ℕ) : innov 𝔼 t (π (t + 1)) = 0 ∧ π (t + 1) = i t := by
  have h := (pegModel_iff 𝔼 hπ hi (isShock_zero 𝔼)).mp hm t
  refine ⟨?_, by rw [h, Pi.zero_apply, sub_zero]⟩
  rw [(hm t).2, Pi.zero_apply, neg_zero]

/-- Cochrane (2023), §12.1, p. 326 (P3: "Countries with volatile fiscal policies ... will see
volatile unexpected inflation under a peg"): the conditional variance of unexpected inflation
equals that of the fiscal shock, `E_t[(ΔE_{t+1} π_{t+1})²] = E_t[ε_{Σs,t+1}²]` (both have
conditional mean zero). -/
theorem peg_unexpected_sq {i ε π : ℕ → Ω → ℝ} (hm : PegModel 𝔼 i ε π) (t : ℕ) :
    𝔼.E t (innov 𝔼 t (π (t + 1)) ^ 2) = 𝔼.E t (ε (t + 1) ^ 2) ∧
      𝔼.E t (innov 𝔼 t (π (t + 1))) = 0 := by
  refine ⟨?_, E_innov_zero 𝔼 t _⟩
  rw [(hm t).2, neg_sq]

/-! ### Chapter 12, P2: the Fisher equation alone (Sargent and Wallace) -/

/-- Cochrane (2023), §12.1, p. 325 (P2, Sargent and Wallace: "unexpected inflation `ΔE_{t+1}π_{t+1}`
can be anything; it is indeterminate"): the Fisher equation alone, under a peg, leaves
unexpected inflation free: for every shock `δ` and every `π_0`, `π_{t+1} = i_t + δ_{t+1}` is
adapted, satisfies `i_t = E_t π_{t+1}`, and has `ΔE_{t+1} π_{t+1} = δ_{t+1}`. -/
theorem fisher_alone_any_innovation {i δ : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hi : 𝔼.Adapted i) (hδ : IsShock 𝔼 δ) :
    𝔼.Adapted (pegSol i (fun t => -δ t) π0) ∧
      (∀ t, i t = 𝔼.E t (pegSol i (fun t => -δ t) π0 (t + 1))) ∧
      ∀ t, innov 𝔼 t (pegSol i (fun t => -δ t) π0 (t + 1)) = δ (t + 1) := by
  obtain ⟨ha, hm, hinn⟩ := passive_any_innovation 𝔼 h0 hi hδ
  exact ⟨ha, fun t => (hm t).1, hinn⟩

/-- Cochrane (2023), §12.1, p. 325 (P2): without the fiscal condition the peg is indeterminate:
the adapted solutions of the Fisher equation `i_t = E_t π_{t+1}` form an uncountable set (already
the initial inflation `π_0` is free). -/
theorem fisher_alone_not_countable [Nonempty Ω] {i : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) :
    ¬ {π : ℕ → Ω → ℝ | 𝔼.Adapted π ∧ ∀ t, i t = 𝔼.E t (π (t + 1))}.Countable := by
  intro hc
  let f : ℝ → ℕ → Ω → ℝ := fun c => pegSol i 0 (fun _ => c)
  have hmaps : Set.MapsTo f Set.univ
      {π : ℕ → Ω → ℝ | 𝔼.Adapted π ∧ ∀ t, i t = 𝔼.E t (π (t + 1))} := by
    intro c _
    have ha := pegSol_adapted 𝔼 (𝔼.const 0 c) hi (isShock_zero 𝔼)
    have hm := (pegModel_iff 𝔼 ha hi (isShock_zero 𝔼)).mpr fun t => rfl
    exact ⟨ha, fun t => (hm t).1⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    exact congrFun (congrFun h 0) ω
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hc)

/-! ### Chapter 12, P4–P5: a real interest rate -/

/-- Cochrane (2023), §12.1, pp. 324–326 (the Fisher relation `i_t = r_t + E_t π_{t+1}` with a
real rate `r_t`) with (2.21): the peg model with a real rate. -/
def PegModelR (r i ε π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = r t + 𝔼.E t (π (t + 1)) ∧ innov 𝔼 t (π (t + 1)) = -ε (t + 1)

/-- Cochrane (2023), §12.1, p. 326: for adapted inflation, real rate and nominal rate and a
fiscal shock, the model holds iff `π_{t+1} = i_t − r_t − ε_{Σs,t+1}`. -/
theorem pegR_iff {r i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hr : 𝔼.Adapted r)
    (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) :
    PegModelR 𝔼 r i ε π ↔ ∀ t, π (t + 1) = i t - r t - ε (t + 1) := by
  constructor
  · intro h t
    have hE : 𝔼.E t (π (t + 1)) = i t - r t := eq_sub_of_add_eq' (h t).1.symm
    rw [eq_E_add_innov 𝔼 (hπ (t + 1)), hE, (h t).2]
    abel
  · intro h t
    have hk : 𝔼.E t (i t - r t) = i t - r t := by rw [map_sub, hi t, hr t]
    have hE : 𝔼.E t (π (t + 1)) = i t - r t := by
      rw [h t, map_sub, hk, hε.2 t, sub_zero]
    refine ⟨by rw [hE]; abel, ?_⟩
    rw [h t, innov_sub, innov_of_known 𝔼 hk, innov_shock 𝔼 hε, zero_sub]

/-- Cochrane (2023), §12.1, p. 326 (P4–P5: a peg is determinate with a time-varying real rate):
for every adapted real rate, peg path, fiscal shock and `π_0` there is exactly one equilibrium. -/
theorem pegR_existsUnique {r i ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hr : 𝔼.Adapted r) (hi : 𝔼.Adapted i) (hε : IsShock 𝔼 ε) :
    ∃! π, 𝔼.Adapted π ∧ π 0 = π0 ∧ PegModelR 𝔼 r i ε π := by
  have hir : 𝔼.Adapted (fun t => i t - r t) := fun t => by
    simp only [map_sub, hi t, hr t]
  have ha := pegSol_adapted 𝔼 h0 hir hε
  refine ⟨pegSol (fun t => i t - r t) ε π0,
    ⟨ha, rfl, (pegR_iff 𝔼 ha hr hi hε).mpr fun t => rfl⟩, ?_⟩
  rintro π ⟨hπ, hπ0, hm⟩
  have h := (pegR_iff 𝔼 hπ hr hi hε).mp hm
  funext t
  cases t with
  | zero => exact hπ0
  | succ t => exact h t

/-- Cochrane (2023), §12.1, p. 325 ("If the central bank pegs the interest rate `i`, then
`E_t π_{t+1}` settles down to `i − r` all on its own") and p. 326 (P5): in every equilibrium,
`E_t π_{t+1} = i_t − r_t`. -/
theorem pegR_expected {r i ε π : ℕ → Ω → ℝ} (hm : PegModelR 𝔼 r i ε π) (t : ℕ) :
    𝔼.E t (π (t + 1)) = i t - r t :=
  eq_sub_of_add_eq' (hm t).1.symm

/-- Cochrane (2023), §12.1, p. 326 (P5: "Under a peg, variation in the real rate of interest
`r_t` ... must express itself in varying expected inflation"): with the same peg, two real-rate
paths move expected inflation one for one, `E_t π'_{t+1} − E_t π_{t+1} = −(r'_t − r_t)`. -/
theorem real_rate_passthrough {r r' i ε ε' π π' : ℕ → Ω → ℝ} (hm : PegModelR 𝔼 r i ε π)
    (hm' : PegModelR 𝔼 r' i ε' π') (t : ℕ) :
    𝔼.E t (π' (t + 1)) - 𝔼.E t (π (t + 1)) = -(r' t - r t) := by
  rw [pegR_expected 𝔼 hm, pegR_expected 𝔼 hm']
  abel

/-- Cochrane (2023), §12.1, p. 326 (P4: "Even a peg at zero interest rate can work. If the
economy demands a positive real rate of interest, a slight deflation would emerge"): with
`i ≡ 0`, a constant real rate `r̄` and no fiscal shocks, every equilibrium has
`π_{t+1} = −r̄`. -/
theorem zero_peg_deflation {rbar : ℝ} {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hm : PegModelR 𝔼 (fun _ _ => rbar) 0 0 π) (t : ℕ) : π (t + 1) = fun _ => -rbar := by
  have hr : 𝔼.Adapted (fun _ _ => rbar) := fun t => 𝔼.const t rbar
  have hi0 : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have h := (pegR_iff 𝔼 hπ hr hi0 (isShock_zero 𝔼)).mp hm t
  rw [h]
  funext ω
  simp

/-- Cochrane (2023), §12.1, p. 326 (P4): the steady states of a peg `ī` with constant real rate
`r̄` and no fiscal shocks are exactly `π̄ = ī − r̄`; for the peg at zero, `π̄ = −r̄`. -/
theorem peg_steady_state_iff [Nonempty Ω] {rbar ibar pibar : ℝ} :
    PegModelR 𝔼 (fun _ _ => rbar) (fun _ _ => ibar) 0 (fun _ _ => pibar) ↔
      pibar = ibar - rbar := by
  constructor
  · intro h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have h1 := congrFun (h 0).1 ω
    rw [𝔼.const] at h1
    simp only [Pi.add_apply] at h1
    linarith
  · intro h t
    refine ⟨?_, ?_⟩
    · rw [𝔼.const]
      funext ω
      simp only [Pi.add_apply]
      linarith
    · rw [innov_const, Pi.zero_apply, neg_zero]

/-! ### Chapter 12, P6: `i_t = φ π_t` is determinate but unstable for `φ > 1` -/

/-- Cochrane (2023), §12.2, p. 327 (P6: "with `i_t = φπ_t` and `i_t = E_tπ_{t+1}`, equilibrium is
`E_tπ_{t+1} = φπ_t`"): in every equilibrium of the rule model with no disturbance,
`E_t π_{t+j} = φʲ π_t`. -/
theorem rule_expected_path {φ : ℝ} {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hm : RuleModel 𝔼 φ i 0 ε π) (t j : ℕ) : 𝔼.E t (π (t + j)) = φ ^ j • π t := by
  induction j with
  | zero => simpa using hπ t
  | succ j ih =>
    have h1 : 𝔼.E (t + j) (π (t + j + 1)) = φ • π (t + j) := by
      rw [← (hm (t + j)).1, (hm (t + j)).2.2, Pi.zero_apply, add_zero]
    rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t j), h1, map_smul, ih, smul_smul]
    congr 1
    ring

/-- Cochrane (2023), §12.2, p. 327 (P6: "If `φ > 1`, inflation is determinate but unstable"):
for `|φ| > 1` the fiscal-theory equilibrium exists and is unique given `π_0` and the fiscal shock
(determinate), yet in every equilibrium expected inflation explodes,
`|E_t π_{t+j}| → ∞`, at every date and state where `π_t ≠ 0` (unstable). -/
theorem rule_determinate_unstable {φ : ℝ} (hφ : 1 < |φ|) {ε : ℕ → Ω → ℝ} {π0 : Ω → ℝ}
    (h0 : 𝔼.E 0 π0 = π0) (hε : IsShock 𝔼 ε) :
    (∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 ∧ q.1 0 = π0 ∧
      RuleModel 𝔼 φ q.2 0 ε q.1) ∧
    ∀ {i π : ℕ → Ω → ℝ}, 𝔼.Adapted π → RuleModel 𝔼 φ i 0 ε π → ∀ t ω, π t ω ≠ 0 →
      Tendsto (fun j => |𝔼.E t (π (t + j)) ω|) atTop atTop := by
  refine ⟨rule_existsUnique 𝔼 φ h0 (fun t => by simp) hε, fun {i π} hπ hm t ω hω => ?_⟩
  have e : (fun j => |𝔼.E t (π (t + j)) ω|) = fun j => |φ| ^ j * |π t ω| := by
    funext j
    rw [rule_expected_path 𝔼 hπ hm t j, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hφ).atTop_mul_const (abs_pos.mpr hω)

/-- Cochrane (2023), §12.2, p. 327 (P6, the passive case): for `|φ| < 1` expected inflation
converges to zero in every equilibrium, `E_t π_{t+j} → 0` (stable), while the equilibrium is
still unique given the fiscal shock (`rule_existsUnique`). -/
theorem rule_stable {φ : ℝ} (hφ : |φ| < 1) {i ε π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hm : RuleModel 𝔼 φ i 0 ε π) (t : ℕ) (ω : Ω) :
    Tendsto (fun j => 𝔼.E t (π (t + j)) ω) atTop (𝓝 0) := by
  have e : (fun j => 𝔼.E t (π (t + j)) ω) = fun j => φ ^ j * π t ω := by
    funext j
    rw [rule_expected_path 𝔼 hπ hm t j, Pi.smul_apply, smul_eq_mul]
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hφ).mul_const (π t ω)

end Cochrane.NewKeynesianSelection.FTPLSimple
