/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5RandomHorizon

/-!
# State-contingent forward guidance with the flow conditions at every date

Cochrane (2023), §7.1, pp. 213–215 (equations (7.1)–(7.3)).

In `TidyR5RandomGuidance.cg_counterexample` and `TidyR5RandomHorizon.cg_horizon_counterexample` an
equilibrium meant the Fisher relations at every date plus the date-0 valuation (7.3). Here the
flow conditions (7.1) **and** the present-value relations (7.2) are imposed at **every** date,
under an explicit debt policy (`FullEqm`).

* `rollD`: **the debt policy.** The inherited debt is one bond maturing at date 2,
  `B_{−1}^{(2)} = 1`. From date 0 on the Treasury buys back all long-term debt and finances
  itself with one-period debt only: `B_t^{(t+1)} = b_t` (known at `t`), nothing longer.
  `rollD_flow_zero_iff`, `rollD_flow_succ_iff`, `rollD_pv_zero_iff`, `rollD_pv_succ_iff`: the
  flow and present-value relations under this policy.
* `rollover_valuation`: in every full equilibrium under this policy, with a nonzero constant
  present value of surpluses `V` from date 1 on, the policy quantities are pinned
  (`b_t (1/P_{t+1}) = V`), `1/P_{t+1}` is known at `t`, and
  `(1/P_0) E_0[(1+i_0)^{-1}(1+i_1)^{-1}] = E_0 ∑ β^j s_j`. So `P_0` is unique given the rates.
* `fullEqm_of_known`, `cg_full`, `cg'_full`, `cg2_full`: the three price paths of the earlier
  counterexamples are full equilibria under this policy, with `b_t = 2 P_{t+1}`.
* `cg_flows_counterexample`, `cg_horizon_flows_counterexample`: **both counterexamples survive.**
  Under the rollover policy each rate path has a full equilibrium, and in every full equilibrium
  `P_0 = 7/48` with the state-contingent guidance `cgRate`, against `P_0 = 1/8` with no
  announcement and with the one-period-delayed guidance `cgRate2`. So with the flow conditions
  imposed at every date, a higher expected rate path still raises `P_0`, and the earlier
  announcement still has the larger effect.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows

open Filter Topology MaturityStructure TidyR5RandomGuidance TidyR5RandomHorizon

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.1 (debt policy): the inherited debt is `B_{−1}^{(2)} = 1` (`cgB`); from
date 0 on all debt is one-period debt, `B_t^{(t+1)} = b_t`, and long-term debt is bought back. -/
noncomputable def rollD (b : ℕ → Ω → ℝ) : ℕ → ℕ → Ω → ℝ
  | 0, m => fun _ => cgB m
  | t + 1, m => if m = t + 1 then b t else 0

/-- Cochrane (2023), §7.1, eqs. (7.1)–(7.3): **a full equilibrium** under the debt policy `D`:
predetermined debt, adapted and positive prices with `x = 1/P`, the announced rates implemented
(`RFisher`), and the flow condition (7.1) and present-value relation (7.2) at every date. -/
def FullEqm (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (P x s i : ℕ → Ω → ℝ) : Prop :=
  Predetermined 𝔼 D ∧ 𝔼.Adapted P ∧ 𝔼.Adapted x ∧ (∀ t ω, P t ω * x t ω = 1) ∧
    (∀ t ω, 0 < P t ω) ∧ RFisher 𝔼 β P x i ∧ (∀ t, RealFlow 𝔼 β D x s t) ∧
    ∀ t, PresentValue 𝔼 β D x s t

/-- Cochrane (2023), §7.1 (debt policy): the rollover policy is predetermined when each `b_t` is
known at `t`. -/
theorem rollD_predetermined {b : ℕ → Ω → ℝ} (hb : ∀ t, 𝔼.E t (b t) = b t) :
    Predetermined 𝔼 (rollD b) := by
  refine ⟨fun m => 𝔼.const 0 _, fun t m => ?_⟩
  simp only [rollD]
  split_ifs
  · exact hb t
  · exact map_zero _

/-- Cochrane (2023), eq. (7.1), p. 213, at date 0 under the rollover policy: the flow condition
holds iff `β b_0 E_0(1/P_1) − β² E_0(1/P_2) = −s_0` (the surplus buys back the long bond net of
the one-period issue). -/
theorem rollD_flow_zero_iff {β : ℝ} {b : ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} :
    RealFlow 𝔼 β (rollD b) x s 0 ↔
      ∀ ω, β * (b 0 ω * 𝔼.E 0 (x 1) ω) - β ^ 2 * 𝔼.E 0 (x 2) ω = -s 0 ω := by
  have hfin : ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) * (sales (rollD b) 0 (0 + (j + 1)) ω *
      𝔼.E 0 (x (0 + (j + 1))) ω)) (β * (b 0 ω * 𝔼.E 0 (x 1) ω) - β ^ 2 * 𝔼.E 0 (x 2) ω) := by
    intro ω
    have hz : ∀ j ∉ ({0, 1} : Finset ℕ), β ^ (j + 1) * (sales (rollD b) 0 (0 + (j + 1)) ω *
        𝔼.E 0 (x (0 + (j + 1))) ω) = 0 := fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      simp [sales, rollD, cgB, hj.1, show j + 1 ≠ 2 by omega]
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hz using 1
    simp [sales, rollD, cgB]
    ring
  constructor
  · intro h ω
    have := (h ω).unique (hfin ω)
    simp only [rollD, cgB] at this
    norm_num at this
    linarith
  · intro h ω
    convert hfin ω using 1
    simp only [rollD, cgB]
    norm_num
    linarith [h ω]

/-- Cochrane (2023), eq. (7.1), p. 213, at date `t + 1` under the rollover policy: the flow
condition holds iff `β b_{t+1} E_{t+1}(1/P_{t+2}) = b_t/P_{t+1} − s_{t+1}`. -/
theorem rollD_flow_succ_iff {β : ℝ} {b : ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (t : ℕ) :
    RealFlow 𝔼 β (rollD b) x s (t + 1) ↔
      ∀ ω, β * (b (t + 1) ω * 𝔼.E (t + 1) (x (t + 2)) ω) = b t ω * x (t + 1) ω - s (t + 1) ω := by
  have hfin : ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) *
      (sales (rollD b) (t + 1) (t + 1 + (j + 1)) ω * 𝔼.E (t + 1) (x (t + 1 + (j + 1))) ω))
      (β * (b (t + 1) ω * 𝔼.E (t + 1) (x (t + 2)) ω)) := by
    intro ω
    have h := hasSum_single (f := fun j : ℕ => β ^ (j + 1) *
      (sales (rollD b) (t + 1) (t + 1 + (j + 1)) ω * 𝔼.E (t + 1) (x (t + 1 + (j + 1))) ω)) 0
      (fun j hj => by
        simp [sales, rollD, hj])
    convert h using 1
    simp [sales, rollD]
  constructor
  · intro h ω
    have := (h ω).unique (hfin ω)
    simp only [rollD, ↓reduceIte] at this
    linarith
  · intro h ω
    convert hfin ω using 1
    simp only [rollD, ↓reduceIte]
    linarith [h ω]

/-- Cochrane (2023), eq. (7.2), p. 213, at date 0 under the rollover policy: the present-value
relation holds iff the surplus series converges and `β² E_0(1/P_2) = E_0 ∑ β^j s_j`. -/
theorem rollD_pv_zero_iff {β : ℝ} {b : ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} :
    PresentValue 𝔼 β (rollD b) x s 0 ↔ ∀ ω, Summable (fun k => surplusTerm 𝔼 β s 0 k ω) ∧
      β ^ 2 * 𝔼.E 0 (x 2) ω = pvSurplus 𝔼 β s 0 ω := by
  have hfin : ∀ ω, HasSum (fun j => debtTerm 𝔼 β (rollD b) x 0 j ω)
      (β ^ 2 * 𝔼.E 0 (x 2) ω) := by
    intro ω
    have h := hasSum_single (f := fun j => debtTerm 𝔼 β (rollD b) x 0 j ω) 2
      (fun j hj => by simp [debtTerm, rollD, cgB, hj])
    convert h using 1
    simp [debtTerm, rollD, cgB]
  constructor
  · intro h ω
    exact ⟨(h ω).1, (hfin ω).unique (h ω).2⟩
  · intro h ω
    refine ⟨(h ω).1, ?_⟩
    rw [← (h ω).2]
    exact hfin ω

/-- Cochrane (2023), eq. (7.2), p. 213, at date `t + 1` under the rollover policy: the
present-value relation holds iff the surplus series converges and
`b_t E_{t+1}(1/P_{t+1}) = E_{t+1} ∑ β^j s_{t+1+j}`. -/
theorem rollD_pv_succ_iff {β : ℝ} {b : ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (t : ℕ) :
    PresentValue 𝔼 β (rollD b) x s (t + 1) ↔
      ∀ ω, Summable (fun k => surplusTerm 𝔼 β s (t + 1) k ω) ∧
        b t ω * 𝔼.E (t + 1) (x (t + 1)) ω = pvSurplus 𝔼 β s (t + 1) ω := by
  have hfin : ∀ ω, HasSum (fun j => debtTerm 𝔼 β (rollD b) x (t + 1) j ω)
      (b t ω * 𝔼.E (t + 1) (x (t + 1)) ω) := by
    intro ω
    have h := hasSum_single (f := fun j => debtTerm 𝔼 β (rollD b) x (t + 1) j ω) 0
      (fun j hj => by simp [debtTerm, rollD, hj])
    convert h using 1
    simp [debtTerm, rollD]
  constructor
  · intro h ω
    exact ⟨(h ω).1, (hfin ω).unique (h ω).2⟩
  · intro h ω
    refine ⟨(h ω).1, ?_⟩
    rw [← (h ω).2]
    exact hfin ω

/-- Cochrane (2023), §7.1, eqs. (7.1)–(7.3): **in every full equilibrium under the rollover
policy** (pull-out, `β ≠ 0`, a nonzero constant present value of surpluses `V` from date 1 on):
the policy quantities are pinned, `b_t/P_{t+1} = V`; `1/P_{t+1}` is known at `t`; and
`(1/P_0) E_0[(1+i_0)^{-1}(1+i_1)^{-1}] = E_0 ∑ β^j s_j`, which determines `P_0` from the
announced rates. -/
theorem rollover_valuation (hpo : 𝔼.PullOut) {β V : ℝ} (hβ : β ≠ 0) (hV : V ≠ 0)
    {b : ℕ → Ω → ℝ} {P x s i : ℕ → Ω → ℝ} (he : FullEqm 𝔼 β (rollD b) P x s i)
    (hpv : ∀ t ω, pvSurplus 𝔼 β s (t + 1) ω = V) :
    (∀ t ω, b t ω * x (t + 1) ω = V) ∧ (∀ t, 𝔼.E t (x (t + 1)) = x (t + 1)) ∧
      ∀ ω, x 0 ω * 𝔼.E 0 (fun ω => (1 + i 0 ω)⁻¹ * (1 + i 1 ω)⁻¹) ω = pvSurplus 𝔼 β s 0 ω := by
  obtain ⟨hD, hP, hx, hPx, -, hF, -, hPV⟩ := he
  have hb : ∀ t ω, b t ω * x (t + 1) ω = V := fun t ω => by
    have := ((rollD_pv_succ_iff 𝔼 t).1 (hPV (t + 1)) ω).2
    rwa [hx (t + 1), hpv] at this
  have hbk : ∀ t, 𝔼.E t (b t) = b t := fun t => by
    have := hD.2 t (t + 1)
    simpa [rollD] using this
  have hxk : ∀ t, 𝔼.E t (x (t + 1)) = x (t + 1) := fun t => by
    have hprod : b t * x (t + 1) = fun _ => V := funext fun ω => hb t ω
    have h1 : 𝔼.E t (b t * x (t + 1)) = b t * 𝔼.E t (x (t + 1)) := hpo t _ _ (hbk t)
    rw [hprod, 𝔼.const] at h1
    funext ω
    have h2 := congrFun h1 ω
    simp only [Pi.mul_apply] at h2
    have hbne : b t ω ≠ 0 := fun h0 => by
      have := hb t ω; rw [h0, zero_mul] at this; exact hV this.symm
    apply mul_left_cancel₀ hbne
    rw [← h2, hb t ω]
  have hstep : ∀ t ω, x (t + 1) ω = x t ω * (1 + i t ω)⁻¹ / β := fun t ω => by
    have h1 := congrFun (hF t) ω
    simp only [bondPrice, pow_one, Pi.smul_apply, smul_eq_mul] at h1
    rw [hpo t _ _ (hP t), hxk t] at h1
    simp only [Pi.mul_apply] at h1
    rw [← h1, eq_div_iff hβ]
    have := hPx t ω
    linear_combination (-(β * x (t + 1) ω)) * this
  refine ⟨hb, hxk, fun ω => ?_⟩
  have hx2 : x 2 = (β ^ 2)⁻¹ • (x 0 * fun ω => (1 + i 0 ω)⁻¹ * (1 + i 1 ω)⁻¹) := by
    funext ω'
    rw [hstep 1 ω', hstep 0 ω']
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    field_simp
  have h0 := ((rollD_pv_zero_iff 𝔼).1 (hPV 0) ω).2
  rw [hx2, map_smul, hpo 0 _ _ (hx 0)] at h0
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h0
  rw [← h0]
  field_simp

/-- Cochrane (2023), §7.1 (counterexample economy): with `β = 1/2` and surpluses `s_t = 1`, the
present value of surpluses is `2` at every date, under every expectation system. -/
theorem pv_one (t : ℕ) (ω : Ω) :
    HasSum (fun k => surplusTerm 𝔼 (1 + 1)⁻¹ (fun _ _ => 1) t k ω) 2 := by
  have h := hasSum_geometric_of_lt_one (r := ((1 : ℝ) + 1)⁻¹) (by norm_num) (by norm_num)
  have e : (1 - ((1 : ℝ) + 1)⁻¹)⁻¹ = 2 := by norm_num
  rw [e] at h
  refine h.congr_fun fun k => ?_
  simp [surplusTerm, 𝔼.const]

/-- Cochrane (2023), §7.1 (counterexample economy): `E_t ∑ β^j s_{t+j} = 2` at every date. -/
theorem pvSurplus_one (t : ℕ) (ω : Ω) : pvSurplus 𝔼 (1 + 1)⁻¹ (fun _ _ => 1) t ω = 2 :=
  (pv_one 𝔼 t ω).tsum_eq

/-- Cochrane (2023), §7.1 (debt policy): the one-period issue `b_t = 2 P_{t+1}`, whose real
value at maturity is the present value of surpluses. -/
noncomputable def rollB (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => 2 * (x (t + 1) ω)⁻¹

/-- Cochrane (2023), §7.1, eqs. (7.1)–(7.3): **sufficient conditions for a full equilibrium**
under the rollover policy with `b_t = 2 P_{t+1}` (`β = 1/2`, `s_t = 1`): an adapted positive price
path implementing the rates, with `1/P_{t+1}` and `2 P_{t+1}` known at `t`, and
`E_0(1/P_2) = 8`. -/
theorem fullEqm_of_known {P x i : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hx : 𝔼.Adapted x)
    (hPx : ∀ t ω, P t ω * x t ω = 1) (hPpos : ∀ t ω, 0 < P t ω)
    (hF : RFisher 𝔼 (1 + 1)⁻¹ P x i) (hxk : ∀ t, 𝔼.E t (x (t + 1)) = x (t + 1))
    (hbk : ∀ t, 𝔼.E t (rollB x t) = rollB x t) (hx2 : ∀ ω, 𝔼.E 0 (x 2) ω = 8) :
    FullEqm 𝔼 (1 + 1)⁻¹ (rollD (rollB x)) P x (fun _ _ => 1) i := by
  have hxne : ∀ t ω, x t ω ≠ 0 := fun t ω h0 => by
    have := hPx t ω; rw [h0, mul_zero] at this; exact zero_ne_one this
  refine ⟨rollD_predetermined 𝔼 hbk, hP, hx, hPx, hPpos, hF, fun t => ?_, fun t => ?_⟩
  · rcases t with _ | t
    · refine (rollD_flow_zero_iff 𝔼).2 fun ω => ?_
      rw [hxk 0, hx2]
      simp only [rollB]
      field_simp [hxne 1 ω]
      norm_num
    · refine (rollD_flow_succ_iff 𝔼 t).2 fun ω => ?_
      rw [hxk (t + 1)]
      simp only [rollB]
      field_simp [hxne (t + 1 + 1) ω, hxne (t + 1) ω]
      norm_num
  · rcases t with _ | t
    · refine (rollD_pv_zero_iff 𝔼).2 fun ω => ⟨(pv_one 𝔼 0 ω).summable, ?_⟩
      rw [hx2, pvSurplus_one]
      norm_num
    · refine (rollD_pv_succ_iff 𝔼 t).2 fun ω => ⟨(pv_one 𝔼 (t + 1) ω).summable, ?_⟩
      rw [hx (t + 1), pvSurplus_one]
      simp only [rollB]
      field_simp [hxne (t + 1) ω]

/-! ### The three counterexample paths are full equilibria -/

/-- Cochrane (2023), §7.1 (counterexample): the guidance path `cgX` with the state-contingent
rates `cgRate` is a full equilibrium under the rollover policy `b_t = 2 P_{t+1}`. -/
theorem cg_full : FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX)) cgP
    cgX (fun _ _ => 1) cgRate := by
  refine fullEqm_of_known _ cgP_adapted cg_adapted (fun t ω => ?_) (fun t ω => ?_) cg_fisher
    (fun t => ?_) (fun t => ?_) (fun ω => ?_)
  · have : cgX t ω ≠ 0 := by simp only [cgX]; split_ifs <;> norm_num
    exact inv_mul_cancel₀ this
  · simp only [cgP, cgX]; split_ifs <;> norm_num
  · rcases t with _ | t
    · have : cgX (0 + 1) = fun _ => 48 / 7 := funext fun ω => by simp [cgX]
      rw [this, ExpectationsFiniteTree.coinSystem.const]
    · exact coin_known (fun ω ω' h => by simp only [cgX, h]) (by omega)
  · rcases t with _ | t
    · have : rollB cgX 0 = fun _ => 2 * (48 / 7)⁻¹ := funext fun ω => by simp [rollB, cgX]
      rw [this, ExpectationsFiniteTree.coinSystem.const]
    · exact coin_known (fun ω ω' h => by simp only [rollB, cgX, h]) (by omega)
  · rw [coin_E0]; simp [cgX]; norm_num

/-- Cochrane (2023), §7.1 (counterexample): the no-announcement path `cgX' = 8` with the constant
rate `r = 1` is a full equilibrium under the rollover policy `b_t = 2 P_{t+1} = 1/4`. -/
theorem cg'_full : FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX'))
    cgP' cgX' (fun _ _ => 1) (fun _ _ => 1) := by
  have hc : ∀ (c : ℝ) t, ExpectationsFiniteTree.coinSystem.E t (fun _ => c) = fun _ => c :=
    fun c t => ExpectationsFiniteTree.coinSystem.const t c
  refine fullEqm_of_known _ (fun t => hc _ t) (fun t => hc _ t) (fun t ω => ?_)
    (fun t ω => ?_) cg_fisher' (fun t => hc _ t) (fun t => hc _ t) (fun ω => ?_)
  · simp [cgP', cgX']
  · simp [cgP']
  · rw [show cgX' 2 = fun _ => (8 : ℝ) from rfl, hc]

/-- Cochrane (2023), §7.1 (counterexample): the delayed path `cgX2` is adapted. -/
theorem cg2_adapted : ExpectationsFiniteTree.coinSystem.Adapted cgX2 := by
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : cgX2 0 = fun _ => 8 := by funext ω; simp [cgX2]
    rw [this, ExpectationsFiniteTree.coinSystem.const]
  · exact coin_known (fun ω ω' h => by simp only [cgX2, h]) ht

/-- Cochrane (2023), §7.1 (counterexample): the delayed price level `cgP2` is adapted. -/
theorem cgP2_adapted : ExpectationsFiniteTree.coinSystem.Adapted cgP2 := by
  intro t
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : cgP2 0 = fun _ => 8⁻¹ := by funext ω; simp [cgP2, cgX2]
    rw [this, ExpectationsFiniteTree.coinSystem.const]
  · exact coin_known (fun ω ω' h => by simp only [cgP2, cgX2, h]) ht

/-- Cochrane (2023), §7.1 (counterexample): the one-period-delayed guidance path `cgX2` with the
rates `cgRate2` is a full equilibrium under the rollover policy `b_t = 2 P_{t+1}`. -/
theorem cg2_full : FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX2))
    cgP2 cgX2 (fun _ _ => 1) cgRate2 := by
  refine fullEqm_of_known _ cgP2_adapted cg2_adapted (fun t ω => ?_) (fun t ω => ?_) cg2_fisher
    (fun t => ?_) (fun t => ?_) (fun ω => ?_)
  · have : cgX2 t ω ≠ 0 := by simp only [cgX2]; split_ifs <;> norm_num
    exact inv_mul_cancel₀ this
  · simp only [cgP2, cgX2]; split_ifs <;> norm_num
  · rcases t with _ | t
    · have : cgX2 (0 + 1) = fun _ => 8 := funext fun ω => by simp [cgX2]
      rw [this, ExpectationsFiniteTree.coinSystem.const]
    · exact coin_known (fun ω ω' h => by simp only [cgX2, h]) (by omega)
  · rcases t with _ | t
    · have : rollB cgX2 0 = fun _ => 2 * 8⁻¹ := funext fun ω => by simp [rollB, cgX2]
      rw [this, ExpectationsFiniteTree.coinSystem.const]
    · exact coin_known (fun ω ω' h => by simp only [rollB, cgX2, h]) (by omega)
  · have : cgX2 2 = fun _ => 8 := funext fun ω => by simp [cgX2]
    rw [this, ExpectationsFiniteTree.coinSystem.const]

/-! ### Uniqueness of `P_0` and the surviving counterexamples -/

/-- Cochrane (2023), §7.1 (counterexample economy): in every full equilibrium under the rollover
policy (`β = 1/2`, `s_t = 1`, coin-flip tree), `P_0 = E_0[(1+i_0)^{-1}(1+i_1)^{-1}]/2` in every
state, and `b_t = 2 P_{t+1}`. -/
theorem coin_rollover_price {b : ℕ → Bool × Bool → ℝ} {P x i : ℕ → Bool × Bool → ℝ}
    (he : FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1) i)
    (ω : Bool × Bool) :
    P 0 ω = ExpectationsFiniteTree.coinSystem.E 0
      (fun ω => (1 + i 0 ω)⁻¹ * (1 + i 1 ω)⁻¹) ω / 2 ∧ ∀ t ω, b t ω = 2 * P (t + 1) ω := by
  obtain ⟨hb, -, hv⟩ := rollover_valuation ExpectationsFiniteTree.coinSystem
    (ExpectationsFiniteTree.finiteTree_pullOut ExpectationsFiniteTree.coinTree) (by norm_num)
    (two_ne_zero) he (fun t ω => pvSurplus_one _ (t + 1) ω)
  obtain ⟨-, -, -, hPx, -⟩ := he
  refine ⟨?_, fun t ω' => ?_⟩
  · have h := hv ω
    rw [pvSurplus_one] at h
    have := hPx 0 ω
    linear_combination (ExpectationsFiniteTree.coinSystem.E 0
      (fun ω => (1 + i 0 ω)⁻¹ * (1 + i 1 ω)⁻¹) ω / 2) * this - P 0 ω / 2 * h
  · have h := hb t ω'
    have := hPx (t + 1) ω'
    linear_combination P (t + 1) ω' * h - b t ω' * this

/-- Cochrane (2023), §7.1, pp. 213–214, **with the flow conditions imposed at every date**: the
state-contingent guidance counterexample survives. Under the rollover policy (buy back the long
bond, then one-period debt only) both the guidance rates `cgRate` (mean `11/10 > r = 1` at date 1)
and the constant rate `r` have full equilibria (`cg_full`, `cg'_full`); in **every** full
equilibrium `P_0 = 7/48` with the guidance and `P_0 = 1/8` without it, so the announced rise in
the expected rate path raises `P_0`. -/
theorem cg_flows_counterexample :
    FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX)) cgP cgX
      (fun _ _ => 1) cgRate ∧
    FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX')) cgP' cgX'
      (fun _ _ => 1) (fun _ _ => 1) ∧
    (∀ (b : ℕ → Bool × Bool → ℝ) (P x : ℕ → Bool × Bool → ℝ),
      FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1) cgRate →
        ∀ ω, P 0 ω = 7 / 48) ∧
    (∀ (b : ℕ → Bool × Bool → ℝ) (P x : ℕ → Bool × Bool → ℝ),
      FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1)
        (fun _ _ => 1) → ∀ ω, P 0 ω = 1 / 8) ∧
    (1 : ℝ) / 8 < 7 / 48 := by
  refine ⟨cg_full, cg'_full, fun b P x he ω => ?_, fun b P x he ω => ?_, by norm_num⟩
  · rw [(coin_rollover_price he ω).1, coin_E0]
    simp [cgRate]
    norm_num
  · rw [(coin_rollover_price he ω).1, coin_E0]
    norm_num

/-- Cochrane (2023), §7.1, p. 213 (first bullet), **with the flow conditions imposed at every
date**: the horizon counterexample survives. Under the rollover policy the guidance `cgRate` and
its one-period delay `cgRate2` both have full equilibria (`cg_full`, `cg2_full`); in every full
equilibrium `P_0 = 7/48` for the earlier announcement and `P_0 = 1/8` for the later one, so the
earlier announcement has the larger effect on `P_0` (contradicting both monotonicity in the
horizon and the immediate-rise comparison). -/
theorem cg_horizon_flows_counterexample :
    FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX)) cgP cgX
      (fun _ _ => 1) cgRate ∧
    FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD (rollB cgX2)) cgP2 cgX2
      (fun _ _ => 1) cgRate2 ∧
    (∀ (b : ℕ → Bool × Bool → ℝ) (P x : ℕ → Bool × Bool → ℝ),
      FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1) cgRate →
        ∀ ω, P 0 ω = 7 / 48) ∧
    (∀ (b : ℕ → Bool × Bool → ℝ) (P x : ℕ → Bool × Bool → ℝ),
      FullEqm ExpectationsFiniteTree.coinSystem (1 + 1)⁻¹ (rollD b) P x (fun _ _ => 1) cgRate2 →
        ∀ ω, P 0 ω = 1 / 8) ∧
    (1 : ℝ) / 8 < 7 / 48 := by
  refine ⟨cg_full, cg2_full, (cg_flows_counterexample).2.2.1, fun b P x he ω => ?_,
    by norm_num⟩
  rw [(coin_rollover_price he ω).1, coin_E0]
  simp [cgRate2]
  norm_num

end Cochrane.LongTermDebtDynamics.TidyR6GuidanceFlows
