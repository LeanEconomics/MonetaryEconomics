/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.SurplusMA

/-!
# Stylised facts and the reasonableness of an s-shaped surplus process

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2.5–§4.2.6, pp. 94–97.

## Main results

* §4.2.5, "the phenomena are tied together". In the simple model, unexpected inflation, the
  debt response and the return innovation are all fixed multiples of the surplus shock with
  the single number `a(ρ)` (`tied_together`). `a(ρ)` is identified from second moments: from
  the inflation–surplus covariance and from the relative volatility of inflation and surpluses
  (`gen_identified`), and from the debt–surplus covariance (`gen_identified_debt`). These are
  the "indirect estimates" of p. 94.
* §4.2.6, p. 95: a borrower who must not inflate or default needs `a(ρ) = 0`
  (`no_inflation_iff_gen_zero`). In the exact model, raising revenue from bond sales after a
  deficit requires promising higher subsequent surpluses (`revenue_rises_iff`).
* §4.2.6, p. 96: with the debt-feedback surplus `s̃_{t+1} = αv_t + u_{s,t+1}` and
  `ρv_{t+1} = v_t − s̃_{t+1}` (no inflation, constant return), surpluses are fully repaid,
  `∑ ρʲ Δ_{t+1}s̃_{t+1+j} = 0`, i.e. `a_s(ρ) = 0` (`feedback_full_repayment`). This holds
  even when the disturbance is a persistent AR(1) with `a_u(ρ) = 1/(1 − ρη) > 1`
  (`ar1_innov_sum`, `feedback_repaid_despite_persistent_u`). Supporting lemmas:
  `fbValue`, `fbSurplus`, `fbValue_bounded`, `fbValue_adapted`, `fb_flow`, `fb_innov_surplus`.
  The book's further remark that this specification is "compatible with active fiscal
  policy" (survey E10) is a Chapter 5 statement and is not treated here.
-/

namespace Cochrane.DebtDeficitsInflation.SurplusProcessFacts

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### §4.2.5: the facts are tied together by `a(ρ)` -/

/-- Cochrane (2023), §4.2.5, p. 94 ("These phenomena are tied together"): in the simple model,
unexpected inflation, the debt response and the ex-post return innovation are all
determined by the single number `a(ρ)`:
`Δπ = −a(ρ)ε`, `ρΔv = (a(ρ) − 1)ε`, `Δr = a(ρ)ε`. -/
theorem tied_together {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -gen a ρ • ε ((t : ℤ) + 1) ∧
      ρ • innov 𝔼 t (v (t + 1)) = (gen a ρ - 1) • ε ((t : ℤ) + 1) ∧
      innov 𝔼 t (r (t + 1)) = gen a ρ • ε ((t : ℤ) + 1) :=
  ⟨innov_infl_eq 𝔼 hm hT hs hε hM hρ t, rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ t,
    (innov_return 𝔼 hm hT hs hε hM hρ t).2⟩

/-- Cochrane (2023), §4.2.5, p. 94 ("the indirect estimate of `a(ρ)` coming from the relative
volatility of inflation and surpluses"): whenever the shock has non-zero conditional variance,
`a(ρ) = −E_t[Δπ ε]/E_t[ε²]` and `a(ρ)² = E_t[(Δπ)²]/E_t[ε²]`. -/
theorem gen_identified {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) (hvar : 𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) ω ≠ 0) :
    gen a ρ = -𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω * ε ((t : ℤ) + 1) ω) ω /
        𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) ω ∧
      gen a ρ ^ 2 = 𝔼.E t (fun ω => innov 𝔼 t (infl (t + 1)) ω ^ 2) ω /
        𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) ω := by
  rw [condCov_innov_infl 𝔼 hm hT hs hε hM hρ, condVar_innov_infl 𝔼 hm hT hs hε hM hρ]
  simp only [Pi.smul_apply, smul_eq_mul]
  constructor <;> field_simp

/-- Cochrane (2023), §4.2.5, p. 94 ("the correlation between surpluses and debt"): the
conditional covariance of the debt innovation with the surplus shock identifies `a(ρ)`,
`ρ E_t[Δv_{t+1} ε_{t+1}] = (a(ρ) − 1) E_t[ε²_{t+1}]`. -/
theorem gen_identified_debt {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (ha0 : a 0 = 1) (hρ : |ρ| ≤ 1) (t : ℕ) :
    ρ • 𝔼.E t (fun ω => innov 𝔼 t (v (t + 1)) ω * ε ((t : ℤ) + 1) ω) =
      (gen a ρ - 1) • 𝔼.E t (fun ω => ε ((t : ℤ) + 1) ω ^ 2) := by
  have h := rho_innov_value_eq 𝔼 hm hT hs hε hM ha0 hρ t
  rw [← map_smul, ← map_smul]
  congr 1
  funext ω
  have hω := congrFun h ω
  simp only [Pi.smul_apply, smul_eq_mul] at hω ⊢
  rw [← mul_assoc, hω]
  ring

/-! ### §4.2.6: an s-shaped surplus process is reasonable -/

/-- Cochrane (2023), §4.2.6, p. 95 ("Governments under the gold standard, members of the euro,
... must follow a surplus process with `a(ρ) = 0` if they wish to avoid default"): in the simple
model, with a state in which the shock is non-zero, unexpected inflation (devaluation) is
ruled out at date `t + 1` iff `a(ρ) = 0`. -/
theorem no_inflation_iff_gen_zero {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {a : ℕ → ℝ}
    {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s) (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M)
    (hρ : |ρ| ≤ 1) (t : ℕ) (hne : ∃ ω, ε ((t : ℤ) + 1) ω ≠ 0) :
    innov 𝔼 t (infl (t + 1)) = 0 ↔ gen a ρ = 0 := by
  rw [innov_infl_eq 𝔼 hm hT hs hε hM hρ t]
  constructor
  · intro h
    obtain ⟨ω, hω⟩ := hne
    have := congrFun h ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, neg_mul, neg_eq_zero] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · exact absurd h1 hω
  · intro h
    rw [h, neg_zero, zero_smul]

/-- Cochrane (2023), §4.2.6, p. 95 ("wish to raise revenue from bond sales rather than just
drive down bond prices. To do so, they must credibly promise to raise subsequent surpluses"):
in the exact model, after a deficit shock `ε_{t+1} < 0`, the revenue from bond sales rises iff
`a(β) < 1`. Equivalently, the discounted value of subsequent surpluses
`β ∑ βʲ s_{t+2+j}` rises. -/
theorem revenue_rises_iff (hpull : 𝔼.PullOut) {β : ℝ} (hβ : |β| < 1) {B P s : ℕ → Ω → ℝ}
    (hP : ∀ t ω, P t ω ≠ 0) (hBP : ∀ t, 𝔼.E t (realDebtEnd B P t) = realDebtEnd B P t)
    (hval : ExactValuation 𝔼 β B P s) {a : ℕ → ℝ} {ε : ℤ → Ω → ℝ} (hs : IsMA a ε s)
    (hε : IsMDS 𝔼 ε) {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) (ha0 : a 0 = 1) (t : ℕ) (ω : Ω)
    (hneg : ε ((t : ℤ) + 1) ω < 0) :
    (0 < innov 𝔼 t (bondPrice 𝔼 β P (t + 1) * realDebtEnd B P (t + 1)) ω ↔ gen a β < 1) ∧
      (0 < (β • innov 𝔼 t (pv β s (t + 1 + 1))) ω ↔ gen a β < 1) := by
  have h1 := revenue_innov 𝔼 hpull hβ hP hBP hval hs hε hM ha0 t
  have h2 := (exact_innov_flow_ma 𝔼 hpull hβ hP hBP hval hs hε hM ha0 t).2
  have key : 0 < (gen a β - 1) * ε ((t : ℤ) + 1) ω ↔ gen a β < 1 := by
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith
    · intro h
      nlinarith
  refine ⟨?_, ?_⟩
  · rw [h1, Pi.smul_apply, smul_eq_mul]; exact key
  · rw [h2, Pi.smul_apply, smul_eq_mul]; exact key

/-! ### §4.2.6, p. 96: surpluses that respond to debt are repaid -/

/-- Cochrane (2023), §4.2.6, p. 96: the value of debt under the debt-feedback surplus
`s̃_{t+1} = αv_t + u_{s,t+1}` and `ρv_{t+1} = v_t − s̃_{t+1}` (no inflation, constant return):
`v_{t+1} = ((1 − α)v_t − u_{t+1})/ρ`, from `v_0`. -/
noncomputable def fbValue (ρ α : ℝ) (v0 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => v0
  | t + 1 => ρ⁻¹ • ((1 - α) • fbValue ρ α v0 u t - u (t + 1))

/-- Cochrane (2023), §4.2.6, p. 96: the debt-feedback surplus `s̃_{t+1} = αv_t + u_{s,t+1}`
(the date-0 value is irrelevant). -/
noncomputable def fbSurplus (ρ α : ℝ) (v0 : Ω → ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => α • fbValue ρ α v0 u t + u (t + 1)

/-- Cochrane (2023), §4.2.6, p. 96: the debt-feedback model satisfies the flow identity
`ρv_{t+1} = v_t + r_{t+1} − s̃_{t+1}` with `r = 0` (constant return, in deviations) and no
growth. -/
theorem fb_flow {ρ α : ℝ} (hρ : ρ ≠ 0) (v0 : Ω → ℝ) (u : ℕ → Ω → ℝ) :
    Flow ρ (fbValue ρ α v0 u) (fun _ => 0) (fun _ => 0) (fbSurplus ρ α v0 u) := by
  intro t
  funext ω
  simp only [fbValue, fbSurplus, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  field_simp
  ring

/-- Cochrane (2023), §4.2.6, p. 96: if `|1 − α| < ρ` and the disturbance is bounded, the value
of debt is bounded (debt is stabilised by the surplus feedback). -/
theorem fbValue_bounded {ρ α : ℝ} (hρ : 0 < ρ) (hα : |1 - α| < ρ) {v0 : Ω → ℝ} {V0 : ℝ}
    (hv0 : ∀ ω, |v0 ω| ≤ V0) {u : ℕ → Ω → ℝ} {K : ℝ} (hu : ∀ t ω, |u t ω| ≤ K) :
    BoundedProc (fbValue ρ α v0 u) := by
  have hd : 0 < ρ - |1 - α| := by linarith
  set B := max V0 (K / (ρ - |1 - α|)) with hB
  refine ⟨B, fun t => ?_⟩
  induction t with
  | zero => intro ω; exact (hv0 ω).trans (le_max_left _ _)
  | succ t ih =>
    intro ω
    have hK : K / (ρ - |1 - α|) ≤ B := le_max_right _ _
    have hK' : K ≤ B * (ρ - |1 - α|) := by
      rwa [div_le_iff₀ hd] at hK
    simp only [fbValue, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [abs_mul, abs_inv, abs_of_pos hρ, inv_mul_le_iff₀ hρ]
    calc |(1 - α) * fbValue ρ α v0 u t ω - u (t + 1) ω|
        ≤ |1 - α| * |fbValue ρ α v0 u t ω| + |u (t + 1) ω| := by
          rw [← abs_mul]; exact abs_sub _ _
      _ ≤ |1 - α| * B + K :=
          add_le_add (mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)) (hu _ ω)
      _ ≤ ρ * B := by nlinarith

/-- Cochrane (2023), §4.2.6, p. 96: with an adapted disturbance and `v_0` known at date 0, the
value of debt is adapted. -/
theorem fbValue_adapted {ρ α : ℝ} {v0 : Ω → ℝ} (hv0 : 𝔼.E 0 v0 = v0) {u : ℕ → Ω → ℝ}
    (hu : 𝔼.Adapted u) : 𝔼.Adapted (fbValue ρ α v0 u) := by
  intro t
  induction t with
  | zero => exact hv0
  | succ t ih =>
    simp only [fbValue]
    rw [map_smul, map_sub, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      hu (t + 1)]

/-- Cochrane (2023), §4.2.6, p. 96: the surplus innovation is the disturbance innovation,
`Δ_{t+1}s̃_{t+1} = Δ_{t+1}u_{s,t+1}` (the feedback term `αv_t` is known at `t`). -/
theorem fb_innov_surplus {ρ α : ℝ} {v0 : Ω → ℝ} (hv0 : 𝔼.E 0 v0 = v0) {u : ℕ → Ω → ℝ}
    (hu : 𝔼.Adapted u) (t : ℕ) :
    innov 𝔼 t (fbSurplus ρ α v0 u (t + 1)) = innov 𝔼 t (u (t + 1)) := by
  simp only [fbSurplus]
  rw [map_add, map_smul, innov_of_known 𝔼 (fbValue_adapted 𝔼 hv0 hu t), smul_zero, zero_add]

/-- Cochrane (2023), §4.2.6, p. 96 ("surpluses themselves `s_t` may be fully repaid with
`a_s(ρ) = 0`"): for `0 < ρ < 1`, `|1 − α| < ρ` and any bounded adapted disturbance, the
discounted sum of surplus innovations is zero, `∑_j ρʲ Δ_{t+1} s̃_{t+1+j} = 0`. -/
theorem feedback_full_repayment {ρ α : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : |1 - α| < ρ)
    {v0 : Ω → ℝ} {V0 : ℝ} (hv0b : ∀ ω, |v0 ω| ≤ V0) (hv0 : 𝔼.E 0 v0 = v0)
    {u : ℕ → Ω → ℝ} {K : ℝ} (hub : ∀ t ω, |u t ω| ≤ K) (hu : 𝔼.Adapted u) (t : ℕ) (ω : Ω) :
    SeriesTo (fun j => ρ ^ j * innov 𝔼 t (fbSurplus ρ α v0 u (t + 1 + j)) ω) 0 := by
  obtain ⟨B, hB⟩ := fbValue_bounded hρ0 hα hv0b hub
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have h0 := rec_seriesTo_map (innov 𝔼 t)
    ((flow_iff_recursion ρ _ _ _ _).1 (fb_flow (α := α) hρ0.ne' v0 u))
    (tvc_innov_of_bounded 𝔼 hρa hB t t ω)
  rw [innov_of_known 𝔼 (fbValue_adapted 𝔼 hv0 hu t)] at h0
  exact h0.congr (fun j => by simp) rfl

/-- Cochrane (2023), §4.2.6, p. 96 (`a_u(ρ) > 1` for a persistent disturbance): for an AR(1)
disturbance (`E_t u_{t+1} = η u_t`, `|ρη| < 1`),
`∑_j ρʲ Δ_{t+1}u_{t+1+j} = Δ_{t+1}u_{t+1}/(1 − ρη)`. -/
theorem ar1_innov_sum {ρ η : ℝ} (h : |ρ * η| < 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 η u)
    (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (u (t + 1 + j)) ω)
      (innov 𝔼 t (u (t + 1)) ω / (1 - ρ * η)) := by
  have hI : ∀ j, innov 𝔼 t (u (t + 1 + j)) ω = η ^ j * innov 𝔼 t (u (t + 1)) ω := by
    intro j
    have h1 : 𝔼.E (t + 1) (u (t + 1 + j)) = η ^ j • u (t + 1) := 𝔼.ar1_iterate hu (t + 1) j
    have h2 : 𝔼.E t (u (t + 1 + j)) = η ^ (j + 1) • u t := by
      rw [show t + 1 + j = t + (j + 1) by omega]; exact 𝔼.ar1_iterate hu t (j + 1)
    have h3 : 𝔼.E t (u (t + 1)) = η • u t := hu.2 t
    rw [innov_apply, innov_apply, Pi.sub_apply, Pi.sub_apply, h1, h2, h3, (hu.1 (t + 1))]
    simp only [Pi.smul_apply, smul_eq_mul, pow_succ]
    ring
  have h1 : 1 - ρ * η ≠ 0 := by
    intro h0
    have : ρ * η = 1 := by linarith
    rw [this, abs_one] at h
    exact lt_irrefl _ h
  have := (hasSum_geometric_of_abs_lt_one h).mul_left (innov 𝔼 t (u (t + 1)) ω)
  convert this using 1
  · funext j
    rw [hI, mul_pow]
    ring
  · field_simp

/-- Cochrane (2023), §4.2.6, p. 96 ("surpluses themselves may be fully repaid with
`a_s(ρ) = 0`, even if `a_u(ρ) > 1`"): with a bounded AR(1) disturbance of persistence `η > 0`,
the disturbance's discounted innovation is `1/(1 − ρη) > 1` times its impact
(`a_u(ρ) > 1`), while the surplus's discounted innovation is zero (`a_s(ρ) = 0`), although
both share the same impact innovation. -/
theorem feedback_repaid_despite_persistent_u {ρ α η : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hα : |1 - α| < ρ) (hη0 : 0 < η) (hρη : |ρ * η| < 1) {v0 : Ω → ℝ} {V0 : ℝ}
    (hv0b : ∀ ω, |v0 ω| ≤ V0) (hv0 : 𝔼.E 0 v0 = v0) {u : ℕ → Ω → ℝ} {K : ℝ}
    (hub : ∀ t ω, |u t ω| ≤ K) (hu : 𝔼.IsAR1 η u) (t : ℕ) (ω : Ω) :
    1 < 1 / (1 - ρ * η) ∧
      HasSum (fun j => ρ ^ j * innov 𝔼 t (u (t + 1 + j)) ω)
        (1 / (1 - ρ * η) * innov 𝔼 t (u (t + 1)) ω) ∧
      SeriesTo (fun j => ρ ^ j * innov 𝔼 t (fbSurplus ρ α v0 u (t + 1 + j)) ω) 0 ∧
      innov 𝔼 t (fbSurplus ρ α v0 u (t + 1)) = innov 𝔼 t (u (t + 1)) := by
  have hpos : 0 < 1 - ρ * η := by linarith [le_abs_self (ρ * η)]
  refine ⟨?_, ?_, feedback_full_repayment 𝔼 hρ0 hρ1 hα hv0b hv0 hub hu.1 t ω,
    fb_innov_surplus 𝔼 hv0 hu.1 t⟩
  · rw [lt_div_iff₀ hpos, one_mul]
    nlinarith
  · have := ar1_innov_sum 𝔼 hρη hu t ω
    convert this using 1
    ring

end Cochrane.DebtDeficitsInflation.SurplusProcessFacts
