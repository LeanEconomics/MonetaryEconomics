/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRulesTargetOpen

/-!
# Theorem FR (d) in the core with a general surplus process `s₀`, `a(β) = 0`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR; the surplus `s_{0,t} = a(L) ε_{s,t}` with
`a(β) = 0`, p. 266).

The core `FiscalRules.fr_unique_bounded` takes the underlying surplus constant,
`s_{0,t} = (1 − β) b̄`. Here the core result (any `ExpectationSystem` with the pull-out property,
the book's target `P* ≡ 1`) is extended to a general surplus process `s₀` whose present value `B`
has no news (`PresentValue`: `B_t = s_{0,t} + β B_{t+1}`, `B_{t+1}` known at `t`, `B` bounded —
what `a(β) = 0` delivers), and to any initial debt `b_0 = B_0 + θ d₀`.

## Main results

* `fr_unique_s0`: every equilibrium with prices bounded above, or bounded away from zero, has
  `1 + (1 − β) d₀ > 0` and `P ≡ 1 + (1 − β) d₀`; with `b_0 = B_0` (`d₀ = 0`) it is `P = P* = 1`
  (`fr_unique_s0_pv`).
* `exists_s0`, `exists_iff_s0`: such an equilibrium exists iff `1 + (1 − β) d₀ > 0`.
* `ma_presentValue`, `fr_unique_ma`: a finite moving average `s_{0,t} = a(L) ε_t` with bounded
  adapted shocks and `a(β) = 0` has such a present value, so FR (d) holds for it in the core.
-/

namespace Cochrane.AssetsRulesBalanceSheets.TidyR5CoreS0

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §9.3.2, p. 266 (`a(β) = 0`): `B` is a present value of the surplus `s₀` with no
news — `B_t = s_{0,t} + β B_{t+1}` on every path, `B_{t+1}` is known at `t`, and `|B| ≤ K`. -/
def PresentValue (β K : ℝ) (s0 B : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, B t ω = s0 t ω + β * B (t + 1) ω) ∧ (∀ t, 𝔼.E t (B (t + 1)) = B (t + 1)) ∧
    ∀ t ω, |B t ω| ≤ K

/-- Cochrane (2023), eqs. (9.8), (9.12), p. 266–267: the core equilibrium conditions of the rule
`s_t = s_{0,t} + θ (P_t − 1)` with target `P* ≡ 1` — positive adapted prices, the interest-rate
target (9.12), the flow (9.8), predetermined real debt and the transversality condition. -/
def CoreEqm (β θ : ℝ) (s0 P b : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ 𝔼.Adapted P ∧ (∀ t, β • 𝔼.E t (P t / P (t + 1)) = fun _ => β) ∧
    (∀ t ω, b t ω = s0 t ω + θ * (P t ω - 1) + β * b (t + 1) ω) ∧
    (∀ t, 𝔼.E t (b (t + 1)) = b (t + 1)) ∧
    ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (b (t + T)) ω) atTop (𝓝 0)

/-- Cochrane (2023), eqs. (9.8), (9.9), p. 266: in an equilibrium with `b_0 = B_0 + θ d₀`, the
process `S_t = 1/(1 − β) + (b_t − B_t)/θ` obeys `S_t = P_t + β S_{t+1}`, `S_{t+1}` known at `t`,
`S_0 = (1 + (1 − β) d₀)/(1 − β)`, the transversality condition, and `S ≥ 0`. -/
theorem value_props {β θ K d0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {s0 B P b : ℕ → Ω → ℝ} (hE : CoreEqm 𝔼 β θ s0 P b) (hPV : PresentValue 𝔼 β K s0 B)
    (hb0 : ∀ ω, b 0 ω = B 0 ω + θ * d0) :
    (∀ t ω, 1 / (1 - β) + (b t ω - B t ω) / θ =
      P t ω + β * (1 / (1 - β) + (b (t + 1) ω - B (t + 1) ω) / θ)) ∧
    (∀ t, 𝔼.E t (fun ω => 1 / (1 - β) + (b (t + 1) ω - B (t + 1) ω) / θ) =
      fun ω => 1 / (1 - β) + (b (t + 1) ω - B (t + 1) ω) / θ) ∧
    (∀ ω, 1 / (1 - β) + (b 0 ω - B 0 ω) / θ = (1 + (1 - β) * d0) / (1 - β)) ∧
    (∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t
      (fun ω => 1 / (1 - β) + (b (t + k) ω - B (t + k) ω) / θ) ω) atTop (𝓝 0)) ∧
    ∀ t ω, 0 ≤ 1 / (1 - β) + (b t ω - B t ω) / θ := by
  obtain ⟨hP, hPa, -, hflow, hpre, htvc⟩ := hE
  obtain ⟨hB, hBpre, hBK⟩ := hPV
  have h1β : 1 - β ≠ 0 := by linarith
  set S : ℕ → Ω → ℝ := fun t ω => 1 / (1 - β) + (b t ω - B t ω) / θ with hS
  have hSlin : ∀ t, S t = (fun _ => 1 / (1 - β)) + θ⁻¹ • (b t - B t) := fun t => by
    funext ω
    simp only [hS, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hrec : ∀ t ω, S t ω = P t ω + β * S (t + 1) ω := fun t ω => by
    simp only [hS]
    rw [hflow t ω, hB t ω]
    field_simp
    ring
  have hSpre : ∀ t, 𝔼.E t (S (t + 1)) = S (t + 1) := fun t => by
    rw [hSlin, map_add, 𝔼.const, map_smul, map_sub, hpre t, hBpre t]
  have hS0 : ∀ ω, S 0 ω = (1 + (1 - β) * d0) / (1 - β) := fun ω => by
    simp only [hS, hb0 ω]
    field_simp
    ring
  have hBE : ∀ t k ω, |𝔼.E t (B (t + k)) ω| ≤ K := fun t k ω =>
    𝔼.abs_E_le (fun ω => hBK (t + k) ω) t ω
  have hTS : ∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t (S (t + k)) ω) atTop (𝓝 0) := by
    intro t ω
    have e : ∀ k, β ^ k * 𝔼.E t (S (t + k)) ω = 1 / (1 - β) * β ^ k +
        θ⁻¹ * (β ^ k * 𝔼.E t (b (t + k)) ω) - θ⁻¹ * (β ^ k * 𝔼.E t (B (t + k)) ω) := by
      intro k
      rw [hSlin, map_add, 𝔼.const, map_smul, map_sub]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    simp_rw [e]
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    have hBt : Tendsto (fun k => β ^ k * 𝔼.E t (B (t + k)) ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.mul_const K)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (hBE t k ω) (pow_pos hβ0 k).le
    simpa using ((hg.const_mul (1 / (1 - β))).add ((htvc t ω).const_mul θ⁻¹)).sub
      (hBt.const_mul θ⁻¹)
  have hsol : ForwardSolution.Solves 𝔼 β P S := fun t => by
    rw [hSpre t]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hrec t ω]
    ring
  exact ⟨hrec, hSpre, hS0, hTS, fun t ω =>
    (FiscalRules.value_bounds 𝔼 hβ0 hβ1 hP hPa hsol hTS t ω).1⟩

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) in the core with a general `s₀`,
`a(β) = 0`, any initial debt**): on any expectation system with the pull-out property, with target
`P* ≡ 1`, the rule `s_t = s_{0,t} + θ (P_t − 1)` (`θ ≠ 0`) where `s₀` has a bounded present value
`B` with no news (`PresentValue`), and initial debt `b_0 = B_0 + θ d₀`: every equilibrium whose
price level is bounded above or bounded away from zero has `1 + (1 − β) d₀ > 0` and
`P_t = 1 + (1 − β) d₀` at every date and state. -/
theorem fr_unique_s0 [Nonempty Ω] (h𝔼 : 𝔼.PullOut) {β θ K d0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B P b : ℕ → Ω → ℝ} (hE : CoreEqm 𝔼 β θ s0 P b)
    (hPV : PresentValue 𝔼 β K s0 B) (hb0 : ∀ ω, b 0 ω = B 0 ω + θ * d0)
    (hbdd : (∃ M, ∀ t ω, P t ω ≤ M) ∨ ∃ m, 0 < m ∧ ∀ t ω, m ≤ P t ω) :
    0 < 1 + (1 - β) * d0 ∧ P = fun _ _ => 1 + (1 - β) * d0 := by
  have h1β : 0 < 1 - β := by linarith
  obtain ⟨hrec, hSpre, hS0, hTS, hSnn⟩ := value_props 𝔼 hβ0 hβ1 hθ hE hPV hb0
  obtain ⟨hP, hPa, h912, -, -, -⟩ := hE
  set S : ℕ → Ω → ℝ := fun t ω => 1 / (1 - β) + (b t ω - B t ω) / θ with hS
  set c : ℝ := 1 + (1 - β) * d0 with hc
  -- positivity of `c`: `S_0 = P_0 + β S_1 ≥ P_0 > 0`
  have hcpos : 0 < c := by
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have e := hrec 0 ω
    have h0 := hS0 ω
    have h1 := hSnn 1 ω
    have hp := hP 0 ω
    have : 0 < (1 + (1 - β) * d0) / (1 - β) := by
      have : 0 < S 0 ω := by
        simp only [hS]
        rw [e]
        exact add_pos_of_pos_of_nonneg hp (mul_nonneg hβ0.le h1)
      have h0' : S 0 ω = (1 + (1 - β) * d0) / (1 - β) := h0
      rwa [h0'] at this
    rw [lt_div_iff₀ h1β, zero_mul] at this
    exact this
  have hTS' : ∀ t ω, Tendsto (fun k => β ^ k * 𝔼.E t (S (t + k)) ω) atTop (𝓝 0) :=
    fun t ω => hTS t ω
  refine ⟨hcpos, ?_⟩
  -- rescaled equilibrium for the core theorem
  set Ph : ℕ → Ω → ℝ := fun t ω => P t ω / c with hPh
  set bh : ℕ → Ω → ℝ := fun t ω => θ * (S t ω / c - 1 / (1 - β)) with hbh
  have hbhlin : ∀ t, bh t = (fun _ => -(θ * (1 / (1 - β)))) + (θ / c) • S t := fun t => by
    funext ω
    simp only [hbh, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hPhp : ∀ t ω, 0 < Ph t ω := fun t ω => div_pos (hP t ω) hcpos
  have hPha : 𝔼.Adapted Ph := fun t => by
    have e : Ph t = c⁻¹ • P t := by
      funext ω
      simp only [hPh, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, map_smul, hPa t]
  have h912h : ∀ t, β • 𝔼.E t (Ph t / Ph (t + 1)) = fun _ => β := fun t => by
    have e : Ph t / Ph (t + 1) = P t / P (t + 1) := by
      funext ω
      simp only [hPh, Pi.div_apply]
      field_simp
    rw [e, h912 t]
  have hflowh : ∀ t ω, bh t ω = (1 - β) * 0 + θ * (Ph t ω - 1) + β * bh (t + 1) ω :=
    fun t ω => by
      simp only [hbh, hPh]
      rw [show S t ω = P t ω + β * S (t + 1) ω from hrec t ω]
      field_simp
      ring
  have hpreh : ∀ t, 𝔼.E t (bh (t + 1)) = bh (t + 1) := fun t => by
    rw [hbhlin, map_add, 𝔼.const, map_smul, hSpre t]
  have hb0h : ∀ ω, bh 0 ω = 0 := fun ω => by
    simp only [hbh]
    rw [show S 0 ω = (1 + (1 - β) * d0) / (1 - β) from hS0 ω]
    field_simp
    ring
  have htvch : ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (bh (t + T)) ω) atTop (𝓝 0) := by
    intro t ω
    have e : ∀ T, β ^ T * 𝔼.E t (bh (t + T)) ω =
        -(θ * (1 / (1 - β))) * β ^ T + θ / c * (β ^ T * 𝔼.E t (S (t + T)) ω) := fun T => by
      rw [hbhlin, map_add, 𝔼.const, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [e]
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul
      (-(θ * (1 / (1 - β))))).add ((hTS' t ω).const_mul (θ / c))
  have hbddh : (∃ M, ∀ t ω, Ph t ω ≤ M) ∨ ∃ m, 0 < m ∧ ∀ t ω, m ≤ Ph t ω := by
    rcases hbdd with ⟨M, hM⟩ | ⟨m, hm, hm'⟩
    · exact Or.inl ⟨M / c, fun t ω => div_le_div_of_nonneg_right (hM t ω) hcpos.le⟩
    · exact Or.inr ⟨m / c, div_pos hm hcpos, fun t ω =>
        div_le_div_of_nonneg_right (hm' t ω) hcpos.le⟩
  have hone := FiscalRules.fr_unique_bounded 𝔼 h𝔼 hβ0 hβ1 hθ (bbar := 0) hPhp hPha h912h
    hflowh hpreh hb0h htvch hbddh
  funext t ω
  have := congrFun (congrFun hone t) ω
  simp only [hPh] at this
  rw [div_eq_one_iff_eq hcpos.ne'] at this
  exact this

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d), core, general `s₀`, `b_0 = B_0`**):
with initial debt equal to the present value of `s₀`, the only equilibrium with prices bounded
above or away from zero is the target, `P ≡ P* = 1`. -/
theorem fr_unique_s0_pv [Nonempty Ω] (h𝔼 : 𝔼.PullOut) {β θ K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B P b : ℕ → Ω → ℝ} (hE : CoreEqm 𝔼 β θ s0 P b)
    (hPV : PresentValue 𝔼 β K s0 B) (hb0 : ∀ ω, b 0 ω = B 0 ω)
    (hbdd : (∃ M, ∀ t ω, P t ω ≤ M) ∨ ∃ m, 0 < m ∧ ∀ t ω, m ≤ P t ω) :
    P = fun _ _ => 1 := by
  have h := (fr_unique_s0 𝔼 h𝔼 hβ0 hβ1 hθ hE hPV (d0 := 0) (fun ω => by rw [hb0 ω]; ring)
    hbdd).2
  rw [h]
  funext t ω
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (existence): if `1 + (1 − β) d₀ > 0`, the constant price
level `P ≡ 1 + (1 − β) d₀` with debt `b_t = B_t + θ d₀` is an equilibrium (`CoreEqm`), bounded
above and away from zero, with `b_0 = B_0 + θ d₀`. -/
theorem exists_s0 {β θ K d0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s0 B : ℕ → Ω → ℝ}
    (hPV : PresentValue 𝔼 β K s0 B) (hc : 0 < 1 + (1 - β) * d0) :
    CoreEqm 𝔼 β θ s0 (fun _ _ => 1 + (1 - β) * d0) (fun t ω => B t ω + θ * d0) := by
  obtain ⟨hB, hBpre, hBK⟩ := hPV
  refine ⟨fun _ _ => hc, fun t => 𝔼.const t _, fun t => ?_, fun t ω => ?_, fun t => ?_,
    fun t ω => ?_⟩
  · have e : ((fun _ => 1 + (1 - β) * d0) / fun _ => 1 + (1 - β) * d0 : Ω → ℝ) =
        fun _ => 1 := by
      funext ω
      simp only [Pi.div_apply]
      exact div_self hc.ne'
    rw [e, 𝔼.const]
    funext ω
    simp
  · change B t ω + θ * d0 = s0 t ω + θ * ((1 + (1 - β) * d0) - 1) + β * (B (t + 1) ω + θ * d0)
    rw [hB t ω]
    ring
  · change 𝔼.E t (fun ω => B (t + 1) ω + θ * d0) = fun ω => B (t + 1) ω + θ * d0
    have e : (fun ω => B (t + 1) ω + θ * d0) = B (t + 1) + fun _ => θ * d0 := by
      funext ω
      simp
    rw [e, map_add, hBpre t, 𝔼.const]
  · have e : ∀ T, β ^ T * 𝔼.E t (fun ω => B (t + T) ω + θ * d0) ω =
        β ^ T * 𝔼.E t (B (t + T)) ω + θ * d0 * β ^ T := fun T => by
      have e' : (fun ω => B (t + T) ω + θ * d0) = B (t + T) + fun _ => θ * d0 := by
        funext ω
        simp
      rw [e', map_add, 𝔼.const]
      simp only [Pi.add_apply]
      ring
    simp_rw [e]
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    have hBt : Tendsto (fun k => β ^ k * 𝔼.E t (B (t + k)) ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.mul_const K)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω => hBK (t + k) ω) t ω)
        (pow_pos hβ0 k).le
    simpa using hBt.add (hg.const_mul (θ * d0))

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**exact existence and uniqueness in the core, general
`s₀` with `a(β) = 0`**): an equilibrium with prices bounded above (or bounded away from zero) and
`b_0 = B_0 + θ d₀` exists **iff** `1 + (1 − β) d₀ > 0`, and then it is `P ≡ 1 + (1 − β) d₀`. -/
theorem exists_iff_s0 [Nonempty Ω] (h𝔼 : 𝔼.PullOut) {β θ K d0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {s0 B : ℕ → Ω → ℝ} (hPV : PresentValue 𝔼 β K s0 B) :
    ((∃ P b : ℕ → Ω → ℝ, CoreEqm 𝔼 β θ s0 P b ∧ (∀ ω, b 0 ω = B 0 ω + θ * d0) ∧
      ((∃ M, ∀ t ω, P t ω ≤ M) ∨ ∃ m, 0 < m ∧ ∀ t ω, m ≤ P t ω)) ↔
      0 < 1 + (1 - β) * d0) ∧
    ∀ P b : ℕ → Ω → ℝ, CoreEqm 𝔼 β θ s0 P b → (∀ ω, b 0 ω = B 0 ω + θ * d0) →
      ((∃ M, ∀ t ω, P t ω ≤ M) ∨ ∃ m, 0 < m ∧ ∀ t ω, m ≤ P t ω) →
      P = fun _ _ => 1 + (1 - β) * d0 := by
  refine ⟨⟨fun ⟨P, b, hE, hb0, hbdd⟩ => (fr_unique_s0 𝔼 h𝔼 hβ0 hβ1 hθ hE hPV hb0 hbdd).1,
    fun hc => ⟨_, _, exists_s0 𝔼 hβ0 hβ1 (θ := θ) hPV hc, fun ω => rfl,
      Or.inl ⟨1 + (1 - β) * d0, fun _ _ => le_rfl⟩⟩⟩,
    fun P b hE hb0 hbdd => (fr_unique_s0 𝔼 h𝔼 hβ0 hβ1 hθ hE hPV hb0 hbdd).2⟩

/-- Cochrane (2023), §9.3.2, p. 266 (`s_{0,t} = a(L) ε_{s,t}` with `a(β) = 0`, core form): for an
adapted shock `|ε| ≤ E`, the finite moving-average surplus `FiscalRulesTargetOpen.MA.surplus` has
the present value `FiscalRulesTargetOpen.MA.value` with no news (`PresentValue`). -/
theorem ma_presentValue {β E : ℝ} {α : ℕ → ℝ} {n : ℕ}
    (hα : ∑ k ∈ Finset.range (n + 1), α k * β ^ k = 0) {ε : ℕ → Ω → ℝ} (hε : 𝔼.Adapted ε)
    (hE : 0 ≤ E) (hεE : ∀ t ω, |ε t ω| ≤ E) :
    PresentValue 𝔼 β ((∑ m ∈ Finset.range n, |FiscalRulesTargetOpen.MA.coef β α n (m + 1)|) * E)
      (FiscalRulesTargetOpen.MA.surplus α n ε) (FiscalRulesTargetOpen.MA.value β α n ε) := by
  refine ⟨fun t ω => FiscalRulesTargetOpen.MA.value_rec hα ε t ω, fun t => ?_, fun t ω => ?_⟩
  · have hlag : ∀ m, 𝔼.E t (FiscalRulesTargetOpen.MA.lagε ε m t) =
        FiscalRulesTargetOpen.MA.lagε ε m t := fun m => by
      by_cases h : m ≤ t
      · have e : FiscalRulesTargetOpen.MA.lagε ε m t = ε (t - m) := funext fun ω => by
          simp [FiscalRulesTargetOpen.MA.lagε, h]
        rw [e]
        exact ForwardSolution.E_of_known 𝔼 (Nat.sub_le t m) (hε (t - m))
      · have e : FiscalRulesTargetOpen.MA.lagε ε m t = fun _ => 0 := funext fun ω => by
          simp [FiscalRulesTargetOpen.MA.lagε, h]
        rw [e, 𝔼.const]
    have e : FiscalRulesTargetOpen.MA.value β α n ε (t + 1) =
        ∑ m ∈ Finset.range n, FiscalRulesTargetOpen.MA.coef β α n (m + 1) •
          FiscalRulesTargetOpen.MA.lagε ε m t := by
      funext ω
      simp [FiscalRulesTargetOpen.MA.value, FiscalRulesTargetOpen.MA.lagε_succ]
    rw [e, map_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [map_smul, hlag m]
  · unfold FiscalRulesTargetOpen.MA.value
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (FiscalRulesTargetOpen.MA.abs_lagε_le hE hεE _ t ω)
      (abs_nonneg _)

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d) in the core with `s_{0,t} = a(L) ε_t`,
`a(β) = 0`**): with bounded adapted shocks, zero pre-sample shocks and initial debt `b_0 = θ d₀`
(the present value of `s₀` at date 0 is `0`), every equilibrium with prices bounded above or away
from zero is `P ≡ 1 + (1 − β) d₀`, and `1 + (1 − β) d₀ > 0`. -/
theorem fr_unique_ma [Nonempty Ω] (h𝔼 : 𝔼.PullOut) {β θ E d0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0)
    {α : ℕ → ℝ} {n : ℕ} (hα : ∑ k ∈ Finset.range (n + 1), α k * β ^ k = 0)
    {ε P b : ℕ → Ω → ℝ} (hε : 𝔼.Adapted ε) (hE : 0 ≤ E) (hεE : ∀ t ω, |ε t ω| ≤ E)
    (hEq : CoreEqm 𝔼 β θ (FiscalRulesTargetOpen.MA.surplus α n ε) P b)
    (hb0 : ∀ ω, b 0 ω = θ * d0)
    (hbdd : (∃ M, ∀ t ω, P t ω ≤ M) ∨ ∃ m, 0 < m ∧ ∀ t ω, m ≤ P t ω) :
    0 < 1 + (1 - β) * d0 ∧ P = fun _ _ => 1 + (1 - β) * d0 :=
  fr_unique_s0 𝔼 h𝔼 hβ0 hβ1 hθ hEq (ma_presentValue 𝔼 hα hε hE hεE)
    (fun ω => by rw [hb0 ω, FiscalRulesTargetOpen.MA.value_zero]; ring) hbdd

/-- Cochrane (2023), §9.3.2, p. 266 (**link** to the core `FiscalRules.fr_unique_bounded`): the
constant surplus `s_{0,t} = (1 − β) b̄` has the present value `B ≡ b̄` with no news, so the core
result is the case `s₀ = (1 − β) b̄`, `d₀ = 0` of `fr_unique_s0`. -/
theorem constant_presentValue (β bbar : ℝ) :
    PresentValue 𝔼 β |bbar| (fun _ _ => (1 - β) * bbar) (fun _ _ => bbar) :=
  ⟨fun _ _ => by ring, fun t => 𝔼.const t _, fun _ _ => le_rfl⟩

end Cochrane.AssetsRulesBalanceSheets.TidyR5CoreS0
