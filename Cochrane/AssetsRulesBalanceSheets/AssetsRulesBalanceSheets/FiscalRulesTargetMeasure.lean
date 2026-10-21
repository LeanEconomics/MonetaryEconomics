/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRulesMeasure

/-!
# Theorem FR (d) with a stochastic target and arbitrary initial debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.2,
eqs. (9.8)–(9.12), pp. 266–267 (Theorem FR, error E9.9; the book allows a "stochastic `P*_t`
target", p. 267).

`FiscalRules.fr_unique_bounded` proves part (d) — bounded price levels restore `P = P*` — for a
constant target `P* ≡ 1` and initial debt `b_{−1}` equal to the present value of `s₀`, on core
expectation systems. Here, on genuine measure-theoretic systems (`ExpectationsMeasure`):

* `fr_unique_stochastic` (prices bounded above) and `fr_unique_stochastic_below` (bounded away from
  zero, with a bounded cumulative target real rate): for an adapted bounded target whose present
  value is predetermined (the target analogue of `a(β) = 0`), every equilibrium of the rule and
  the interest-rate target (9.12) satisfies `P_t = (1 + (b₀ − b̄)/(θ a₀)) P*_t`, where
  `b₀ − b̄` is initial debt minus the present value of `s₀` and `a₀` the target's present value;
  `fr_unique_stochastic_target`: `P = P*` when `b₀ = b̄`; `exists_proportional`: this path is an
  equilibrium.
* `deterministic_target`, `fr_unique_deterministic`: every deterministic target qualifies;
  `sTarget_props`, `sTarget_news`, `fr_unique_sShaped`: a genuinely stochastic one does.
* `initial_debt_of_target`, `fr_initial_debt`: with `b₀ ≠ b̄` the rule never delivers `P = P*`;
  the price level is pinned at a multiple of the target.
* `BoolExample.bool_counterexample`: without a predetermined target value the proportional form
  fails — a bounded stochastic target whose present value has news admits the bounded
  equilibrium `P = P* + 1`, not proportional to `P*`.
* `fr_unique_bounded_link`, `fr_unique_bounded_link_core`: on finite systems the measure theorem
  specialises to the core `FiscalRules.fr_unique_bounded`.
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalRulesTargetMeasure

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure FiscalRulesMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), §9.3.2, p. 267 (Theorem FR (d), measure setting): iterating `Y_t = β E_t
Y_{t+1}` (a.e.) gives `Y_t = β^{k+1} E_t Y_{t+k+1}` (law of iterated expectations). -/
theorem iterate_beta {β : ℝ} {Y : ℕ → Ω → ℝ} (hY : ∀ t, Y t =ᵐ[S.μ] β • S.E t (Y (t + 1)))
    (t k : ℕ) : Y t =ᵐ[S.μ] β ^ (k + 1) • S.E t (Y (t + (k + 1))) := by
  induction k with
  | zero => simpa using hY t
  | succ k ih =>
    have h1 : S.E t (Y (t + (k + 1))) =ᵐ[S.μ]
        S.E t (β • S.E (t + (k + 1)) (Y (t + (k + 1) + 1))) :=
      S.E_congr (hY (t + (k + 1))) t
    have h2 := S.E_smul β (S.E (t + (k + 1)) (Y (t + (k + 1) + 1))) t
    have h3 := S.E_tower (Nat.le_add_right t (k + 1)) (Y (t + (k + 1) + 1))
    filter_upwards [ih, h1, h2, h3] with ω e e1 e2 e3
    simp only [Pi.smul_apply, smul_eq_mul] at e e2 ⊢
    rw [e, e1, e2, e3, show t + (k + 1 + 1) = t + (k + 1) + 1 by ring, pow_succ]
    ring

/-- Cochrane (2023), §9.3.2, p. 267 (Theorem FR (d)): if `Y_t = β^{k+1} E_t Y_{t+k+1}` for all `k`,
with `|Y_{t+k+1}| ≤ W_k` and `E_t W_k = B` not depending on `k`, then `Y_t = 0` a.e. -/
theorem zero_of_iterate {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Y W : ℕ → Ω → ℝ} {B : Ω → ℝ}
    {t : ℕ} (hit : ∀ k, Y t =ᵐ[S.μ] β ^ (k + 1) • S.E t (Y (t + (k + 1))))
    (hYi : ∀ k, Integrable (Y (t + (k + 1))) S.μ) (hWi : ∀ k, Integrable (W k) S.μ)
    (hYW : ∀ k, ∀ᵐ ω ∂S.μ, |Y (t + (k + 1)) ω| ≤ W k ω) (hWB : ∀ k, S.E t (W k) =ᵐ[S.μ] B) :
    Y t =ᵐ[S.μ] 0 := by
  have hup : ∀ k, S.E t (Y (t + (k + 1))) ≤ᵐ[S.μ] S.E t (W k) := fun k =>
    S.E_mono (hYi k) (hWi k) ((hYW k).mono fun ω h => (le_abs_self _).trans h) t
  have hlo : ∀ k, S.E t (-Y (t + (k + 1))) ≤ᵐ[S.μ] S.E t (W k) := fun k =>
    S.E_mono (hYi k).neg (hWi k) ((hYW k).mono fun ω h => (neg_le_abs _).trans h) t
  have hneg : ∀ k, S.E t (-Y (t + (k + 1))) =ᵐ[S.μ] -S.E t (Y (t + (k + 1))) := fun k =>
    condExp_neg _ _
  filter_upwards [ae_all_iff.2 hit, ae_all_iff.2 hup, ae_all_iff.2 hlo, ae_all_iff.2 hneg,
    ae_all_iff.2 hWB] with ω h1 h2 h3 h4 h5
  have hb : ∀ k, |Y t ω| ≤ β ^ (k + 1) * B ω := fun k => by
    rw [h1 k, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (pow_pos hβ0 (k + 1))]
    refine mul_le_mul_of_nonneg_left ?_ (pow_pos hβ0 (k + 1)).le
    rw [abs_le]
    have a2 := h2 k
    have a3 := h3 k
    rw [h4 k, h5 k] at a3
    rw [h5 k] at a2
    simp only [Pi.neg_apply] at a3
    constructor <;> linarith
  have hlim : Tendsto (fun k => β ^ (k + 1) * B ω) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
      (tendsto_add_atTop_nat 1)).mul_const (B ω)
  have := ge_of_tendsto' hlim hb
  simp only [Pi.zero_apply]
  exact abs_nonpos_iff.mp this

/-- Cochrane (2023), §9.3.2, p. 267 (eq. (9.12) with a stochastic target): if `E_t ρ_{t+1} = γ_t
ρ_t` and the deflator satisfies `N_{t+1}⁻¹ γ_t = N_t⁻¹`, then `N⁻¹ ρ` is a martingale,
`E_t(N_{t+k}⁻¹ ρ_{t+k}) = N_t⁻¹ ρ_t` a.e. -/
theorem deflated_martingale {γ ρ Ninv : ℕ → Ω → ℝ}
    (hρm : ∀ t, StronglyMeasurable[S.𝓕 t] (ρ t)) (hρi : ∀ t, Integrable (ρ t) S.μ)
    (hNm : ∀ t, StronglyMeasurable[S.𝓕 t] (Ninv t))
    (hNm' : ∀ t, StronglyMeasurable[S.𝓕 t] (Ninv (t + 1)))
    (hNb : ∀ t, ∃ C, ∀ᵐ ω ∂S.μ, |Ninv t ω| ≤ C)
    (hN : ∀ t, ∀ᵐ ω ∂S.μ, Ninv (t + 1) ω * γ t ω = Ninv t ω)
    (hρ : ∀ t, S.E t (ρ (t + 1)) =ᵐ[S.μ] γ t * ρ t) (t k : ℕ) :
    S.E t (Ninv (t + k) * ρ (t + k)) =ᵐ[S.μ] Ninv t * ρ t := by
  induction k with
  | zero =>
    obtain ⟨C, hC⟩ := hNb t
    refine EventuallyEq.of_eq (S.E_of_stronglyMeasurable ((hNm t).mul (hρm t)) ?_)
    exact (hρi t).bdd_mul ((hNm t).mono (S.𝓕.le t)).aestronglyMeasurable
      (hC.mono fun ω h => by rwa [Real.norm_eq_abs])
  | succ k ih =>
    obtain ⟨C, hC⟩ := hNb (t + k + 1)
    have hb := S.E_pullOut (hNm' (t + k)) hC (hρi (t + k + 1))
    have h : S.E (t + k) (Ninv (t + k + 1) * ρ (t + k + 1)) =ᵐ[S.μ]
        Ninv (t + k) * ρ (t + k) := by
      filter_upwards [hb, hρ (t + k), hN (t + k)] with ω e1 e2 e3
      simp only [Pi.mul_apply] at e1 e2 ⊢
      rw [e1, e2, ← e3]
      ring
    have ha := S.E_tower (Nat.le_add_right t k) (Ninv (t + k + 1) * ρ (t + k + 1))
    exact ha.symm.trans ((S.E_congr h t).trans ih)

/-- Cochrane (2023), eq. (9.9), p. 266: if `V_t = P_t + β V_{t+1}` on every path with `V` adapted,
then `V_t = ∑_{j<k} βʲ E_t P_{t+j} + βᵏ E_t V_{t+k}` a.e. -/
theorem value_partial {β : ℝ} {P V : ℕ → Ω → ℝ} (hV : ∀ t ω, V t ω = P t ω + β * V (t + 1) ω)
    (hVm : ∀ t, StronglyMeasurable[S.𝓕 t] (V t)) (hVi : ∀ t, Integrable (V t) S.μ)
    (hPi : ∀ t, Integrable (P t) S.μ) (t k : ℕ) :
    ∀ᵐ ω ∂S.μ, V t ω = ∑ j ∈ Finset.range k, β ^ j * S.E t (P (t + j)) ω +
      β ^ k * S.E t (V (t + k)) ω := by
  induction k with
  | zero =>
    refine Eventually.of_forall fun ω => ?_
    simp [S.E_of_stronglyMeasurable (hVm t) (hVi t)]
  | succ k ih =>
    have hfun : V (t + k) = P (t + k) + β • V (t + k + 1) := funext fun ω => hV (t + k) ω
    have h1 := S.E_add (hPi (t + k)) ((hVi (t + k + 1)).smul β) t
    have h2 := S.E_smul β (V (t + k + 1)) t
    filter_upwards [ih, h1, h2] with ω e e1 e2
    rw [e, hfun, e1, Pi.add_apply, e2, Finset.sum_range_succ, Pi.smul_apply, smul_eq_mul,
      show t + (k + 1) = t + k + 1 by ring, pow_succ]
    ring

/-- Cochrane (2023), eq. (9.9), p. 266 (supporting Theorem FR (d)): with `0 < P ≤ M` and the
transversality condition `βᵏ E_t V_{t+k} → 0`, the value satisfies `0 ≤ V_t ≤ M/(1 − β)` a.e. -/
theorem value_bounds {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {P V : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hPM : ∀ t ω, P t ω ≤ M)
    (hV : ∀ t ω, V t ω = P t ω + β * V (t + 1) ω)
    (hVm : ∀ t, StronglyMeasurable[S.𝓕 t] (V t)) (hVi : ∀ t, Integrable (V t) S.μ)
    (hPi : ∀ t, Integrable (P t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun k => β ^ k * S.E t (V (t + k)) ω) atTop (𝓝 0))
    (t : ℕ) : ∀ᵐ ω ∂S.μ, 0 ≤ V t ω ∧ V t ω ≤ M / (1 - β) := by
  have hE0 : ∀ j, ∀ᵐ ω ∂S.μ, 0 ≤ S.E t (P (t + j)) ω := fun j => by
    have h := S.E_mono (integrable_const 0) (hPi (t + j))
      (Eventually.of_forall fun ω => (hP (t + j) ω).le) t
    rw [S.E_const] at h
    exact h
  have hEM : ∀ j, ∀ᵐ ω ∂S.μ, S.E t (P (t + j)) ω ≤ M := fun j => by
    have h := S.E_mono (hPi (t + j)) (integrable_const M)
      (Eventually.of_forall fun ω => hPM (t + j) ω) t
    rw [S.E_const] at h
    exact h
  filter_upwards [ae_all_iff.2 (value_partial S hV hVm hVi hPi t), htvc t, ae_all_iff.2 hE0,
    ae_all_iff.2 hEM] with ω h1 h2 h3 h4
  have hM0 : 0 ≤ M := (hP 0 ω).le.trans (hPM 0 ω)
  have hpart : Tendsto (fun k => ∑ j ∈ Finset.range k, β ^ j * S.E t (P (t + j)) ω) atTop
      (𝓝 (V t ω)) := by
    have := (tendsto_const_nhds (x := V t ω)).sub h2
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [h1 k]
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  refine ⟨ge_of_tendsto' hpart fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (pow_nonneg hβ0.le j) (h3 j), le_of_tendsto' hpart fun k => ?_⟩
  calc ∑ j ∈ Finset.range k, β ^ j * S.E t (P (t + j)) ω
      ≤ ∑ j ∈ Finset.range k, β ^ j * M :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (h4 j) (pow_nonneg hβ0.le j)
    _ = M * ∑ j ∈ Finset.range k, β ^ j := by rw [Finset.mul_sum]; ring_nf
    _ ≤ M * ∑' j, β ^ j := mul_le_mul_of_nonneg_left
        (hgeo.sum_le_tsum _ fun j _ => pow_nonneg hβ0.le j) hM0
    _ = M / (1 - β) := by rw [tsum_geometric_of_lt_one hβ0.le hβ1, div_eq_mul_inv]

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §9.3.2, p. 267: a bounded solution of `a_t = P*_t + β a_{t+1}` with `P* ≥ m` is
at least `m/(1 − β)` (it is the present value of the target). -/
theorem targetValue_ge {β m K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar a : ℕ → Ω → ℝ}
    (hPs : ∀ t ω, m ≤ Pstar t ω) (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (haK : ∀ t ω, |a t ω| ≤ K) (t : ℕ) (ω : Ω) : m / (1 - β) ≤ a t ω := by
  have hk : ∀ k t, m * ∑ j ∈ Finset.range k, β ^ j - β ^ k * K ≤ a t ω := by
    intro k
    induction k with
    | zero => intro t; simp only [Finset.range_zero, Finset.sum_empty, mul_zero, pow_zero,
        one_mul, zero_sub]; exact neg_le_of_abs_le (haK t ω)
    | succ k ih =>
      intro t
      have h1 := ih (t + 1)
      rw [ha t ω, Finset.sum_range_succ', pow_succ]
      simp only [pow_zero, pow_succ]
      have h2 := hPs t ω
      have e : ∑ j ∈ Finset.range k, β ^ j * β = β * ∑ j ∈ Finset.range k, β ^ j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e]
      nlinarith
  have hlim : Tendsto (fun k => m * ∑ j ∈ Finset.range k, β ^ j - β ^ k * K) atTop
      (𝓝 (m / (1 - β))) := by
    have h1 := ((hasSum_geometric_of_lt_one hβ0.le hβ1).tendsto_sum_nat).const_mul m
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const K
    have := h1.sub h2
    simpa [div_eq_mul_inv] using this
  exact le_of_tendsto' hlim fun k => hk k t

/-- Cochrane (2023), §9.3.2, p. 267 (Theorem FR (d)): if `Y_t = β^{k+1} E_t Y_{t+k+1}` for all `k`,
with `|Y_{t+k+1}| ≤ W_k` and `β^{k+1} E_t W_k → 0` a.e., then `Y_t = 0` a.e. -/
theorem zero_of_iterate' {β : ℝ} (hβ0 : 0 < β) {Y W : ℕ → Ω → ℝ}
    {t : ℕ} (hit : ∀ k, Y t =ᵐ[S.μ] β ^ (k + 1) • S.E t (Y (t + (k + 1))))
    (hYi : ∀ k, Integrable (Y (t + (k + 1))) S.μ) (hWi : ∀ k, Integrable (W k) S.μ)
    (hYW : ∀ k, ∀ᵐ ω ∂S.μ, |Y (t + (k + 1)) ω| ≤ W k ω)
    (hWlim : ∀ᵐ ω ∂S.μ, Tendsto (fun k => β ^ (k + 1) * S.E t (W k) ω) atTop (𝓝 0)) :
    Y t =ᵐ[S.μ] 0 := by
  have hup : ∀ k, S.E t (Y (t + (k + 1))) ≤ᵐ[S.μ] S.E t (W k) := fun k =>
    S.E_mono (hYi k) (hWi k) ((hYW k).mono fun ω h => (le_abs_self _).trans h) t
  have hlo : ∀ k, S.E t (-Y (t + (k + 1))) ≤ᵐ[S.μ] S.E t (W k) := fun k =>
    S.E_mono (hYi k).neg (hWi k) ((hYW k).mono fun ω h => (neg_le_abs _).trans h) t
  have hneg : ∀ k, S.E t (-Y (t + (k + 1))) =ᵐ[S.μ] -S.E t (Y (t + (k + 1))) := fun k =>
    condExp_neg _ _
  filter_upwards [ae_all_iff.2 hit, ae_all_iff.2 hup, ae_all_iff.2 hlo, ae_all_iff.2 hneg,
    hWlim] with ω h1 h2 h3 h4 h5
  have hb : ∀ k, |Y t ω| ≤ β ^ (k + 1) * S.E t (W k) ω := fun k => by
    rw [h1 k, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (pow_pos hβ0 (k + 1))]
    refine mul_le_mul_of_nonneg_left ?_ (pow_pos hβ0 (k + 1)).le
    rw [abs_le]
    have a2 := h2 k
    have a3 := h3 k
    rw [h4 k] at a3
    simp only [Pi.neg_apply] at a3
    constructor <;> linarith
  have := ge_of_tendsto' h5 hb
  simp only [Pi.zero_apply]
  exact abs_nonpos_iff.mp this

/-- Cochrane (2023), eq. (9.9), p. 266 (supporting Theorem FR (d)): with `P > 0` and the
transversality condition, `V_t ≥ 0` a.e. -/
theorem value_nonneg {β : ℝ} (hβ0 : 0 < β) {P V : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hV : ∀ t ω, V t ω = P t ω + β * V (t + 1) ω)
    (hVm : ∀ t, StronglyMeasurable[S.𝓕 t] (V t)) (hVi : ∀ t, Integrable (V t) S.μ)
    (hPi : ∀ t, Integrable (P t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun k => β ^ k * S.E t (V (t + k)) ω) atTop (𝓝 0))
    (t : ℕ) : ∀ᵐ ω ∂S.μ, 0 ≤ V t ω := by
  have hE0 : ∀ j, ∀ᵐ ω ∂S.μ, 0 ≤ S.E t (P (t + j)) ω := fun j => by
    have h := S.E_mono (integrable_const 0) (hPi (t + j))
      (Eventually.of_forall fun ω => (hP (t + j) ω).le) t
    rw [S.E_const] at h
    exact h
  filter_upwards [ae_all_iff.2 (value_partial S hV hVm hVi hPi t), htvc t, ae_all_iff.2 hE0]
    with ω h1 h2 h3
  have hpart : Tendsto (fun k => ∑ j ∈ Finset.range k, β ^ j * S.E t (P (t + j)) ω) atTop
      (𝓝 (V t ω)) := by
    have := (tendsto_const_nhds (x := V t ω)).sub h2
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [h1 k]
  exact ge_of_tendsto' hpart fun k => Finset.sum_nonneg fun j _ =>
    mul_nonneg (pow_nonneg hβ0.le j) (h3 j)

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d)** with a **stochastic target**, prices
bounded above): on any measure-theoretic expectation system, let the target `P*` be adapted with `0
< m ≤ P* ≤ M*`, and let its present value be predetermined: a bounded `a` with `a_t = P*_t + β
a_{t+1}` on every path and `a_{t+1}` known at `t` (the target analogue of the book's `a(β) = 0`;
then `a_t` is the present value of the target). Let prices be positive, adapted, bounded above, with
`1/P_t` integrable; let the interest-rate target `E_t(P_t/P_{t+1}) = E_t(P*_t/P*_{t+1})` (9.12), the
flow (9.8) with the rule `s_t = (1 − β) b̄ + θ (P_t − P*_t)`, predetermined real debt, initial debt
`b₀` and the transversality condition hold. Then `P_t = (1 + (b₀ − b̄)/(θ a₀)) P*_t` a.e. at every
date. Proof: `Z_t = V_t/P_t` and `Z*_t = a_t/P*_t` (with `V_t = (b_t − b̄)/θ + a_t`) both obey `E_t
Z_{t+1} = γ_t (Z_t − 1)/β`, `γ_t = E_t(P*_t/P*_{t+1})`; deflating `Z − Z*` by `∏ γ_i` gives `Y_t = β
E_t Y_{t+1}`, and boundedness forces `Y = 0`. -/
theorem fr_unique_stochastic {β θ bbar b0 m Ms M K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {Pstar P b a : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hPa : StronglyAdapted S.𝓕 P) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ K)
    (hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1)))
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω)
    (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1))) (hb0 : ∀ ω, b 0 ω = b0)
    (hbi : ∀ t, Integrable (b t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0))
    (t : ℕ) : P t =ᵐ[S.μ] fun ω => (1 + (b0 - bbar) / (θ * a 0 ω)) * Pstar t ω := by
  -- basic facts
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hPi : ∀ t, Integrable (P t) S.μ := fun t =>
    Integrable.of_bound ((hPm t).mono (S.𝓕.le t)).aestronglyMeasurable M
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (hP t ω)]; exact hPM t ω)
  have ham : ∀ t, StronglyMeasurable[S.𝓕 t] (a t) := fun t => by
    have e : a t = fun ω => Pstar t ω + β * a (t + 1) ω := funext (ha t)
    rw [e]
    exact (hPsm t).add ((hapre t).const_mul β)
  have hai : ∀ t, Integrable (a t) S.μ := fun t =>
    Integrable.of_bound ((ham t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact haK t ω)
  have hapos : ∀ t ω, 0 < a t ω := fun t ω =>
    (div_pos hm (by linarith)).trans_le
      (targetValue_ge hβ0 hβ1 (fun t ω => (hPs t ω).1) ha haK t ω)
  set qs : ℕ → Ω → ℝ := fun t ω => 1 / Pstar t ω with hqs_def
  set q : ℕ → Ω → ℝ := fun t ω => 1 / P t ω with hq_def
  have hqsm : ∀ t, StronglyMeasurable[S.𝓕 t] (qs t) := fun t =>
    ((hPsm t).measurable.const_div 1).stronglyMeasurable
  have hqm : ∀ t, StronglyMeasurable[S.𝓕 t] (q t) := fun t =>
    ((hPm t).measurable.const_div 1).stronglyMeasurable
  have hqsb : ∀ t ω, 1 / Ms ≤ qs t ω ∧ qs t ω ≤ 1 / m := fun t ω =>
    ⟨one_div_le_one_div_of_le (hPs0 t ω) (hPs t ω).2, one_div_le_one_div_of_le hm (hPs t ω).1⟩
  have hqsi : ∀ t, Integrable (qs t) S.μ := fun t =>
    Integrable.of_bound ((hqsm t).mono (S.𝓕.le t)).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPs0 t ω))]; exact (hqsb t ω).2)
  -- the value of the price path, `V_t = (b_t − b̄)/θ + a_t`
  set V : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (b t ω - bbar) + a t ω with hV_def
  have hVrec : ∀ t ω, V t ω = P t ω + β * V (t + 1) ω := fun t ω => by
    simp only [hV_def]
    rw [hflow t ω, ha t ω]
    field_simp
    ring
  have hVm' : ∀ t, StronglyMeasurable[S.𝓕 t] (V (t + 1)) := fun t =>
    (((hpre t).sub stronglyMeasurable_const).const_mul θ⁻¹).add (hapre t)
  have hVm : ∀ t, StronglyMeasurable[S.𝓕 t] (V t) := fun t => by
    have e : V t = fun ω => P t ω + β * V (t + 1) ω := funext (hVrec t)
    rw [e]
    exact (hPm t).add ((hVm' t).const_mul β)
  have hVi : ∀ t, Integrable (V t) S.μ := fun t =>
    (((hbi t).sub (integrable_const bbar)).const_mul θ⁻¹).add (hai t)
  have hVtvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun k => β ^ k * S.E t (V (t + k)) ω) atTop (𝓝 0) := by
    intro t
    have hlin : ∀ k, S.E t (V (t + k)) =ᵐ[S.μ]
        fun ω => θ⁻¹ * (S.E t (b (t + k)) ω - bbar) + S.E t (a (t + k)) ω := fun k => by
      have e : V (t + k) = θ⁻¹ • (b (t + k) - fun _ => bbar) + a (t + k) := by
        funext ω
        simp [hV_def]
      have h1 := S.E_add (((hbi (t + k)).sub (integrable_const bbar)).smul θ⁻¹) (hai (t + k)) t
      have h2 := S.E_smul θ⁻¹ (b (t + k) - fun _ => bbar) t
      have h3 := S.E_sub (hbi (t + k)) (integrable_const bbar) t
      rw [e]
      filter_upwards [h1, h2, h3] with ω e1 e2 e3
      rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, Pi.sub_apply, S.E_const, smul_eq_mul]
    have hK : ∀ k, ∀ᵐ ω ∂S.μ, |S.E t (a (t + k)) ω| ≤ K := fun k =>
      S.abs_E_le (Eventually.of_forall fun ω => haK (t + k) ω) t
    filter_upwards [ae_all_iff.2 hlin, ae_all_iff.2 hK, htvc t] with ω h1 h2 h3
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    have hA : Tendsto (fun k => β ^ k * S.E t (a (t + k)) ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.mul_const K)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (h2 k) (pow_pos hβ0 k).le
    have := ((h3.sub (hg.mul_const bbar)).const_mul θ⁻¹).add hA
    simp only [zero_mul, sub_zero, mul_zero, zero_add] at this
    refine this.congr fun k => ?_
    rw [h1 k]
    ring
  have hVb := value_bounds S hβ0 hβ1 hP hPM hVrec hVm hVi hPi hVtvc
  have hVbd : ∀ t, ∀ᵐ ω ∂S.μ, |V t ω| ≤ M / (1 - β) := fun t =>
    (hVb t).mono fun ω h => abs_le.2 ⟨by linarith [h.1, h.2], h.2⟩
  -- `γ_t = E_t(P*_t/P*_{t+1})`, the target's gross real-rate factor
  set γ : ℕ → Ω → ℝ := fun t ω => Pstar t ω * S.E t (qs (t + 1)) ω with hγ_def
  have hEqs : ∀ t, ∀ᵐ ω ∂S.μ, 1 / Ms ≤ S.E t (qs (t + 1)) ω ∧
      S.E t (qs (t + 1)) ω ≤ 1 / m := fun t => by
    have h1 := S.E_mono (integrable_const (1 / Ms)) (hqsi (t + 1))
      (Eventually.of_forall fun ω => (hqsb (t + 1) ω).1) t
    have h2 := S.E_mono (hqsi (t + 1)) (integrable_const (1 / m))
      (Eventually.of_forall fun ω => (hqsb (t + 1) ω).2) t
    rw [S.E_const] at h1 h2
    filter_upwards [h1, h2] with ω e1 e2
    exact ⟨e1, e2⟩
  have hγm : ∀ t, StronglyMeasurable[S.𝓕 t] (γ t) := fun t =>
    (hPsm t).mul (S.stronglyMeasurable_E t _)
  have hγb : ∀ t, ∀ᵐ ω ∂S.μ, m / Ms ≤ γ t ω ∧ γ t ω ≤ Ms / m := fun t => by
    filter_upwards [hEqs t] with ω h
    have hMs : 0 < Ms := (hPs0 t ω).trans_le (hPs t ω).2
    constructor
    · calc m / Ms = m * (1 / Ms) := by ring
        _ ≤ Pstar t ω * S.E t (qs (t + 1)) ω :=
          mul_le_mul (hPs t ω).1 h.1 (by positivity) (hPs0 t ω).le
    · calc Pstar t ω * S.E t (qs (t + 1)) ω ≤ Ms * (1 / m) :=
          mul_le_mul (hPs t ω).2 h.2 ((one_div_pos.2 hMs).le.trans h.1) hMs.le
        _ = Ms / m := by ring
  have hγpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < γ t ω := fun t => by
    filter_upwards [hγb t] with ω h
    have hMs : 0 < Ms := (hPs0 t ω).trans_le (hPs t ω).2
    exact (div_pos hm hMs).trans_le h.1
  -- the interest-rate target (9.12): `E_t q_{t+1} = γ_t q_t`
  have hqrate : ∀ t, S.E t (q (t + 1)) =ᵐ[S.μ] γ t * q t := fun t => by
    have e1 : P t / P (t + 1) = P t * q (t + 1) := by
      funext ω
      simp [hq_def, div_eq_mul_inv]
    have e2 : Pstar t / Pstar (t + 1) = Pstar t * qs (t + 1) := by
      funext ω
      simp [hqs_def, div_eq_mul_inv]
    have h1 := S.E_pullOut (hPm t) (C := M) (Eventually.of_forall fun ω => by
      rw [abs_of_pos (hP t ω)]; exact hPM t ω) (hq (t + 1))
    have h2 := S.E_pullOut (hPsm t) (C := Ms) (Eventually.of_forall fun ω => by
      rw [abs_of_pos (hPs0 t ω)]; exact (hPs t ω).2) (hqsi (t + 1))
    have h3 := hrate t
    rw [e1, e2] at h3
    filter_upwards [h1, h2, h3] with ω f1 f2 f3
    rw [f1, f2] at f3
    simp only [Pi.mul_apply] at f3 ⊢
    have hp := (hP t ω).ne'
    rw [show γ t ω * q t ω = Pstar t ω * S.E t (qs (t + 1)) ω / P t ω by
      simp only [hγ_def, hq_def]; ring, eq_div_iff hp]
    linarith
  have hqsrate : ∀ t, S.E t (qs (t + 1)) = γ t * qs t := fun t => by
    funext ω
    simp only [Pi.mul_apply, hγ_def, hqs_def]
    field_simp [(hPs0 t ω).ne']
  -- `Z_t = V_t/P_t`, `Z*_t = a_t/P*_t` and `X = Z − Z*`
  set Z : ℕ → Ω → ℝ := fun t ω => V t ω * q t ω with hZ_def
  set Zs : ℕ → Ω → ℝ := fun t ω => a t ω * qs t ω with hZs_def
  have hZi : ∀ t, Integrable (Z t) S.μ := fun t =>
    (hq t).bdd_mul ((hVm t).mono (S.𝓕.le t)).aestronglyMeasurable
      ((hVbd t).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hZsi : ∀ t, Integrable (Zs t) S.μ := fun t =>
    (hqsi t).bdd_mul ((ham t).mono (S.𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact haK t ω)
  have hEZ : ∀ t, S.E t (Z (t + 1)) =ᵐ[S.μ] fun ω => V (t + 1) ω * (γ t ω * q t ω) := fun t => by
    have h := S.E_pullOut (hVm' t) (hVbd (t + 1)) (hq (t + 1))
    filter_upwards [h, hqrate t] with ω e1 e2
    change S.E t (V (t + 1) * q (t + 1)) ω = _
    rw [e1, Pi.mul_apply, e2, Pi.mul_apply]
  have hEZs : ∀ t, S.E t (Zs (t + 1)) =ᵐ[S.μ]
      fun ω => a (t + 1) ω * S.E t (qs (t + 1)) ω := fun t => by
    have h := S.E_pullOut (hapre t) (Eventually.of_forall fun ω => haK (t + 1) ω) (hqsi (t + 1))
    filter_upwards [h] with ω e1
    change S.E t (a (t + 1) * qs (t + 1)) ω = _
    rw [e1, Pi.mul_apply]
  set X : ℕ → Ω → ℝ := fun t => Z t - Zs t with hX_def
  have hXi : ∀ t, Integrable (X t) S.μ := fun t => (hZi t).sub (hZsi t)
  have hEX : ∀ t, S.E t (X (t + 1)) =ᵐ[S.μ] fun ω => γ t ω * X t ω / β := fun t => by
    filter_upwards [S.E_sub (hZi (t + 1)) (hZsi (t + 1)) t, hEZ t, hEZs t] with ω e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3]
    have hv : V (t + 1) ω = (V t ω - P t ω) / β := by
      rw [hVrec t ω]; field_simp; ring
    have ha' : a (t + 1) ω = (a t ω - Pstar t ω) / β := by
      rw [ha t ω]; field_simp; ring
    have hp := (hP t ω).ne'
    have hps := (hPs0 t ω).ne'
    simp only [hX_def, hZ_def, hZs_def, hγ_def, hq_def, hqs_def, Pi.sub_apply]
    rw [hv, ha']
    field_simp
    ring
  -- the deflator `Ninv_t = ∏_{i<t} γ_i⁻¹`
  set Ninv : ℕ → Ω → ℝ := fun t ω => ∏ i ∈ Finset.range t, (γ i ω)⁻¹ with hN_def
  have hNmeas : ∀ s t, s ≤ t + 1 → StronglyMeasurable[S.𝓕 t] (Ninv s) := fun s t hst => by
    have : Measurable[S.𝓕 t] (Ninv s) := Finset.measurable_prod _ fun i hi =>
      ((hγm i).mono (S.𝓕.mono (by have := Finset.mem_range.1 hi; omega))).measurable.inv
    exact this.stronglyMeasurable
  have hNb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < Ninv t ω ∧ Ninv t ω ≤ (Ms / m) ^ t := fun t => by
    filter_upwards [ae_all_iff.2 hγb] with ω h
    have hMs : 0 < Ms := (hPs0 0 ω).trans_le (hPs 0 ω).2
    have hpos : ∀ i, 0 < γ i ω := fun i => (div_pos hm hMs).trans_le (h i).1
    refine ⟨Finset.prod_pos fun i _ => inv_pos.2 (hpos i), ?_⟩
    calc Ninv t ω ≤ ∏ _i ∈ Finset.range t, Ms / m :=
          Finset.prod_le_prod₀ (fun i _ => (inv_pos.2 (hpos i)).le) fun i _ => by
            rw [← inv_div]
            exact inv_anti₀ (div_pos hm hMs) (h i).1
      _ = (Ms / m) ^ t := by rw [Finset.prod_const, Finset.card_range]
  have hNbd : ∀ t, ∃ C, ∀ᵐ ω ∂S.μ, |Ninv t ω| ≤ C := fun t =>
    ⟨(Ms / m) ^ t, (hNb t).mono fun ω h => by rw [abs_of_pos h.1]; exact h.2⟩
  have hNγ : ∀ t, ∀ᵐ ω ∂S.μ, Ninv (t + 1) ω * γ t ω = Ninv t ω := fun t => by
    filter_upwards [hγpos t] with ω h
    simp only [hN_def, Finset.prod_range_succ]
    field_simp
  -- `Y_t = Ninv_t X_t` satisfies `Y_t = β E_t Y_{t+1}`
  set Y : ℕ → Ω → ℝ := fun t => Ninv t * X t with hY_def
  have hYi : ∀ t, Integrable (Y t) S.μ := fun t => by
    obtain ⟨C, hC⟩ := hNbd t
    exact (hXi t).bdd_mul ((hNmeas t t (Nat.le_succ t)).mono (S.𝓕.le t)).aestronglyMeasurable
      (hC.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hY : ∀ t, Y t =ᵐ[S.μ] β • S.E t (Y (t + 1)) := fun t => by
    obtain ⟨C, hC⟩ := hNbd (t + 1)
    have h := S.E_pullOut (hNmeas (t + 1) t le_rfl) hC (hXi (t + 1))
    filter_upwards [h, hEX t, hγpos t] with ω e1 e2 e3
    change Ninv t ω * X t ω = β * S.E t (Ninv (t + 1) * X (t + 1)) ω
    rw [e1, Pi.mul_apply, e2]
    simp only [hN_def, Finset.prod_range_succ]
    field_simp
  -- hence `X ≡ 0`
  have hX0 : ∀ s, X s =ᵐ[S.μ] 0 := by
    intro s
    have hNinvY : Y s =ᵐ[S.μ] 0 := by
      have hit := iterate_beta S hY s
      set C1 := M / (1 - β) with hC1
      have hmq := deflated_martingale S (γ := γ) (ρ := q) (Ninv := Ninv) hqm (fun t => hq t)
        (fun t => hNmeas t t (Nat.le_succ t)) (fun t => hNmeas (t + 1) t le_rfl) hNbd hNγ hqrate
      have hmqs := deflated_martingale S (γ := γ) (ρ := qs) (Ninv := Ninv) hqsm hqsi
        (fun t => hNmeas t t (Nat.le_succ t)) (fun t => hNmeas (t + 1) t le_rfl) hNbd hNγ
        (fun t => EventuallyEq.of_eq (hqsrate t))
      have hFi : ∀ n, Integrable (Ninv n * q n) S.μ := fun n => by
        obtain ⟨C, hC⟩ := hNbd n
        exact (hq n).bdd_mul ((hNmeas n n (Nat.le_succ n)).mono (S.𝓕.le n)).aestronglyMeasurable
          (hC.mono fun ω h => by rwa [Real.norm_eq_abs])
      have hGi : ∀ n, Integrable (Ninv n * qs n) S.μ := fun n => by
        obtain ⟨C, hC⟩ := hNbd n
        exact (hqsi n).bdd_mul ((hNmeas n n (Nat.le_succ n)).mono (S.𝓕.le n)).aestronglyMeasurable
          (hC.mono fun ω h => by rwa [Real.norm_eq_abs])
      refine zero_of_iterate S hβ0 hβ1 (t := s)
        (W := fun k => C1 • (Ninv (s + (k + 1)) * q (s + (k + 1))) +
          K • (Ninv (s + (k + 1)) * qs (s + (k + 1))))
        (B := C1 • (Ninv s * q s) + K • (Ninv s * qs s)) hit (fun k => hYi _)
        (fun k => ((hFi _).smul C1).add ((hGi _).smul K)) (fun k => ?_) (fun k => ?_)
      · filter_upwards [hNb (s + (k + 1)), hVbd (s + (k + 1))] with ω e1 e2
        set n := s + (k + 1)
        simp only [hY_def, hX_def, hZ_def, hZs_def, Pi.mul_apply, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        have hqpos : 0 < q n ω := one_div_pos.2 (hP n ω)
        have hqspos : 0 < qs n ω := one_div_pos.2 (hPs0 n ω)
        rw [abs_mul, abs_of_pos e1.1]
        have hb : |V n ω * q n ω - a n ω * qs n ω| ≤ C1 * q n ω + K * qs n ω := by
          calc _ ≤ |V n ω * q n ω| + |a n ω * qs n ω| := abs_sub _ _
            _ = |V n ω| * q n ω + |a n ω| * qs n ω := by
              rw [abs_mul, abs_mul, abs_of_pos hqpos, abs_of_pos hqspos]
            _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right e2 hqpos.le)
              (mul_le_mul_of_nonneg_right (haK n ω) hqspos.le)
        calc Ninv n ω * |V n ω * q n ω - a n ω * qs n ω|
            ≤ Ninv n ω * (C1 * q n ω + K * qs n ω) := mul_le_mul_of_nonneg_left hb e1.1.le
          _ = _ := by ring
      · have h1 := S.E_add ((hFi (s + (k + 1))).smul C1) ((hGi (s + (k + 1))).smul K) s
        have h2 := S.E_smul C1 (Ninv (s + (k + 1)) * q (s + (k + 1))) s
        have h3 := S.E_smul K (Ninv (s + (k + 1)) * qs (s + (k + 1))) s
        filter_upwards [h1, h2, h3, hmq s (k + 1), hmqs s (k + 1)] with ω e1 e2 e3 e4 e5
        rw [e1, Pi.add_apply, e2, e3, Pi.smul_apply, Pi.smul_apply, e4, e5]
        rfl
    filter_upwards [hNinvY, hNb s] with ω e1 e2
    change Ninv s ω * X s ω = 0 at e1
    exact (mul_eq_zero.1 e1).resolve_left e2.1.ne'
  have hXe : ∀ s, ∀ᵐ ω ∂S.μ, V s ω * q s ω = a s ω * qs s ω := fun s => by
    filter_upwards [hX0 s] with ω h
    simp only [hX_def, hZ_def, hZs_def, Pi.sub_apply, Pi.zero_apply] at h
    linarith
  have hr : ∀ s, ∀ᵐ ω ∂S.μ, Pstar (s + 1) ω * q (s + 1) ω = Pstar s ω * q s ω := fun s => by
    have hZZ : Z (s + 1) =ᵐ[S.μ] Zs (s + 1) := by
      filter_upwards [hX0 (s + 1)] with ω h
      simp only [hX_def, Pi.sub_apply, Pi.zero_apply] at h
      linarith
    filter_upwards [S.E_congr hZZ s, hEZ s, hEZs s, hXe (s + 1), hEqs s] with ω e1 e2 e3 e4 e5
    rw [e2, e3] at e1
    have hMs : 0 < Ms := (hPs0 s ω).trans_le (hPs s ω).2
    have hE : 0 < S.E s (qs (s + 1)) ω := (one_div_pos.2 hMs).trans_le e5.1
    have hA : V (s + 1) ω * (Pstar s ω * q s ω) = a (s + 1) ω := by
      have h : (V (s + 1) ω * (Pstar s ω * q s ω)) * S.E s (qs (s + 1)) ω =
          a (s + 1) ω * S.E s (qs (s + 1)) ω := by
        rw [← e1]
        simp only [hγ_def]
        ring
      exact mul_right_cancel₀ hE.ne' h
    have hB : V (s + 1) ω * (Pstar (s + 1) ω * q (s + 1) ω) = a (s + 1) ω := by
      have h1 : Pstar (s + 1) ω * qs (s + 1) ω = 1 := by
        simp only [hqs_def]
        field_simp [(hPs0 (s + 1) ω).ne']
      calc _ = (V (s + 1) ω * q (s + 1) ω) * Pstar (s + 1) ω := by ring
        _ = a (s + 1) ω * (Pstar (s + 1) ω * qs (s + 1) ω) := by rw [e4]; ring
        _ = _ := by rw [h1, mul_one]
    have hV0 : V (s + 1) ω ≠ 0 := fun h => by
      rw [h, zero_mul] at hA
      exact (hapos (s + 1) ω).ne' hA.symm
    exact mul_left_cancel₀ hV0 (hB.trans hA.symm)
  have hr0 : ∀ s, ∀ᵐ ω ∂S.μ, Pstar s ω * q s ω = Pstar 0 ω * q 0 ω := by
    intro s
    induction s with
    | zero => exact Eventually.of_forall fun ω => rfl
    | succ s ih =>
      filter_upwards [ih, hr s] with ω e1 e2
      rw [e2, e1]
  filter_upwards [hr0 t, hXe 0] with ω e1 e2
  have hV0 : V 0 ω = θ⁻¹ * (b0 - bbar) + a 0 ω := by simp only [hV_def, hb0 ω]
  simp only [hq_def, hqs_def] at e1 e2
  rw [hV0] at e2
  have hp0 := (hP 0 ω).ne'
  have hpt := (hP t ω).ne'
  have hs0 := (hPs0 0 ω).ne'
  have hst := (hPs0 t ω).ne'
  have ha0 := (hapos 0 ω).ne'
  field_simp at e1 e2 ⊢
  refine mul_left_cancel₀ hs0 ?_
  linear_combination (-(θ * a 0 ω)) * e1 - Pstar t ω * e2

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d)** with a **stochastic target**, prices
bounded away from zero): as `fr_unique_stochastic`, with prices bounded below by `m_P > 0` and
integrable instead of bounded above, under the additional condition that the target's cumulative
real-rate factor is bounded, `∏_{i<k} E_{t+i}(P*_{t+i}/P*_{t+i+1})⁻¹ ≤ L` (true for deterministic
bounded targets, `deterministic_deflator`). Then `P_t = (1 + (b₀ − b̄)/(θ a₀)) P*_t` a.e. -/
theorem fr_unique_stochastic_below {β θ bbar b0 m Ms mP K L : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {Pstar P b a : ℕ → Ω → ℝ}
    (hPa : StronglyAdapted S.𝓕 P) (hmP : 0 < mP) (hPmP : ∀ t ω, mP ≤ P t ω)
    (hPi : ∀ t, Integrable (P t) S.μ)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ K)
    (hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1)))
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω)
    (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1))) (hb0 : ∀ ω, b 0 ω = b0)
    (hbi : ∀ t, Integrable (b t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0))
    (hL : ∀ t k, ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      (Pstar (t + i) ω * S.E (t + i) (fun ω => 1 / Pstar (t + i + 1) ω) ω)⁻¹ ≤ L)
    (t : ℕ) : P t =ᵐ[S.μ] fun ω => (1 + (b0 - bbar) / (θ * a 0 ω)) * Pstar t ω := by
  -- basic facts
  have hPm : ∀ t, StronglyMeasurable[S.𝓕 t] (P t) := fun t => hPa t
  have hPsm : ∀ t, StronglyMeasurable[S.𝓕 t] (Pstar t) := fun t => hPsa t
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hP : ∀ t ω, 0 < P t ω := fun t ω => hmP.trans_le (hPmP t ω)
  have hqb : ∀ t ω, |1 / P t ω| ≤ 1 / mP := fun t ω => by
    rw [abs_of_pos (one_div_pos.2 (hP t ω))]
    exact one_div_le_one_div_of_le hmP (hPmP t ω)
  have hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ := fun t =>
    Integrable.of_bound (((hPm t).measurable.const_div 1).stronglyMeasurable.mono
      (S.𝓕.le t)).aestronglyMeasurable (1 / mP)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hqb t ω)
  have ham : ∀ t, StronglyMeasurable[S.𝓕 t] (a t) := fun t => by
    have e : a t = fun ω => Pstar t ω + β * a (t + 1) ω := funext (ha t)
    rw [e]
    exact (hPsm t).add ((hapre t).const_mul β)
  have hai : ∀ t, Integrable (a t) S.μ := fun t =>
    Integrable.of_bound ((ham t).mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact haK t ω)
  have hapos : ∀ t ω, 0 < a t ω := fun t ω =>
    (div_pos hm (by linarith)).trans_le
      (targetValue_ge hβ0 hβ1 (fun t ω => (hPs t ω).1) ha haK t ω)
  set qs : ℕ → Ω → ℝ := fun t ω => 1 / Pstar t ω with hqs_def
  set q : ℕ → Ω → ℝ := fun t ω => 1 / P t ω with hq_def
  have hqsm : ∀ t, StronglyMeasurable[S.𝓕 t] (qs t) := fun t =>
    ((hPsm t).measurable.const_div 1).stronglyMeasurable
  have hqm : ∀ t, StronglyMeasurable[S.𝓕 t] (q t) := fun t =>
    ((hPm t).measurable.const_div 1).stronglyMeasurable
  have hqsb : ∀ t ω, 1 / Ms ≤ qs t ω ∧ qs t ω ≤ 1 / m := fun t ω =>
    ⟨one_div_le_one_div_of_le (hPs0 t ω) (hPs t ω).2, one_div_le_one_div_of_le hm (hPs t ω).1⟩
  have hqsi : ∀ t, Integrable (qs t) S.μ := fun t =>
    Integrable.of_bound ((hqsm t).mono (S.𝓕.le t)).aestronglyMeasurable (1 / m)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.2 (hPs0 t ω))]; exact (hqsb t ω).2)
  -- the value of the price path, `V_t = (b_t − b̄)/θ + a_t`
  set V : ℕ → Ω → ℝ := fun t ω => θ⁻¹ * (b t ω - bbar) + a t ω with hV_def
  have hVrec : ∀ t ω, V t ω = P t ω + β * V (t + 1) ω := fun t ω => by
    simp only [hV_def]
    rw [hflow t ω, ha t ω]
    field_simp
    ring
  have hVm' : ∀ t, StronglyMeasurable[S.𝓕 t] (V (t + 1)) := fun t =>
    (((hpre t).sub stronglyMeasurable_const).const_mul θ⁻¹).add (hapre t)
  have hVm : ∀ t, StronglyMeasurable[S.𝓕 t] (V t) := fun t => by
    have e : V t = fun ω => P t ω + β * V (t + 1) ω := funext (hVrec t)
    rw [e]
    exact (hPm t).add ((hVm' t).const_mul β)
  have hVi : ∀ t, Integrable (V t) S.μ := fun t =>
    (((hbi t).sub (integrable_const bbar)).const_mul θ⁻¹).add (hai t)
  have hVtvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun k => β ^ k * S.E t (V (t + k)) ω) atTop (𝓝 0) := by
    intro t
    have hlin : ∀ k, S.E t (V (t + k)) =ᵐ[S.μ]
        fun ω => θ⁻¹ * (S.E t (b (t + k)) ω - bbar) + S.E t (a (t + k)) ω := fun k => by
      have e : V (t + k) = θ⁻¹ • (b (t + k) - fun _ => bbar) + a (t + k) := by
        funext ω
        simp [hV_def]
      have h1 := S.E_add (((hbi (t + k)).sub (integrable_const bbar)).smul θ⁻¹) (hai (t + k)) t
      have h2 := S.E_smul θ⁻¹ (b (t + k) - fun _ => bbar) t
      have h3 := S.E_sub (hbi (t + k)) (integrable_const bbar) t
      rw [e]
      filter_upwards [h1, h2, h3] with ω e1 e2 e3
      rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, Pi.sub_apply, S.E_const, smul_eq_mul]
    have hK : ∀ k, ∀ᵐ ω ∂S.μ, |S.E t (a (t + k)) ω| ≤ K := fun k =>
      S.abs_E_le (Eventually.of_forall fun ω => haK (t + k) ω) t
    filter_upwards [ae_all_iff.2 hlin, ae_all_iff.2 hK, htvc t] with ω h1 h2 h3
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    have hA : Tendsto (fun k => β ^ k * S.E t (a (t + k)) ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (by simpa using hg.mul_const K)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (h2 k) (pow_pos hβ0 k).le
    have := ((h3.sub (hg.mul_const bbar)).const_mul θ⁻¹).add hA
    simp only [zero_mul, sub_zero, mul_zero, zero_add] at this
    refine this.congr fun k => ?_
    rw [h1 k]
    ring
  have hVb := value_nonneg S hβ0 hP hVrec hVm hVi hPi hVtvc
  -- `γ_t = E_t(P*_t/P*_{t+1})`, the target's gross real-rate factor
  set γ : ℕ → Ω → ℝ := fun t ω => Pstar t ω * S.E t (qs (t + 1)) ω with hγ_def
  have hEqs : ∀ t, ∀ᵐ ω ∂S.μ, 1 / Ms ≤ S.E t (qs (t + 1)) ω ∧
      S.E t (qs (t + 1)) ω ≤ 1 / m := fun t => by
    have h1 := S.E_mono (integrable_const (1 / Ms)) (hqsi (t + 1))
      (Eventually.of_forall fun ω => (hqsb (t + 1) ω).1) t
    have h2 := S.E_mono (hqsi (t + 1)) (integrable_const (1 / m))
      (Eventually.of_forall fun ω => (hqsb (t + 1) ω).2) t
    rw [S.E_const] at h1 h2
    filter_upwards [h1, h2] with ω e1 e2
    exact ⟨e1, e2⟩
  have hγm : ∀ t, StronglyMeasurable[S.𝓕 t] (γ t) := fun t =>
    (hPsm t).mul (S.stronglyMeasurable_E t _)
  have hγb : ∀ t, ∀ᵐ ω ∂S.μ, m / Ms ≤ γ t ω ∧ γ t ω ≤ Ms / m := fun t => by
    filter_upwards [hEqs t] with ω h
    have hMs : 0 < Ms := (hPs0 t ω).trans_le (hPs t ω).2
    constructor
    · calc m / Ms = m * (1 / Ms) := by ring
        _ ≤ Pstar t ω * S.E t (qs (t + 1)) ω :=
          mul_le_mul (hPs t ω).1 h.1 (by positivity) (hPs0 t ω).le
    · calc Pstar t ω * S.E t (qs (t + 1)) ω ≤ Ms * (1 / m) :=
          mul_le_mul (hPs t ω).2 h.2 ((one_div_pos.2 hMs).le.trans h.1) hMs.le
        _ = Ms / m := by ring
  have hγpos : ∀ t, ∀ᵐ ω ∂S.μ, 0 < γ t ω := fun t => by
    filter_upwards [hγb t] with ω h
    have hMs : 0 < Ms := (hPs0 t ω).trans_le (hPs t ω).2
    exact (div_pos hm hMs).trans_le h.1
  -- the interest-rate target (9.12): `E_t q_{t+1} = γ_t q_t`
  have hqrate : ∀ t, S.E t (q (t + 1)) =ᵐ[S.μ] γ t * q t := fun t => by
    have e1 : P t / P (t + 1) = P t * q (t + 1) := by
      funext ω
      simp [hq_def, div_eq_mul_inv]
    have e2 : Pstar t / Pstar (t + 1) = Pstar t * qs (t + 1) := by
      funext ω
      simp [hqs_def, div_eq_mul_inv]
    have h1 : S.E t (P t * q (t + 1)) =ᵐ[S.μ] P t * S.E t (q (t + 1)) :=
      condExp_mul_of_stronglyMeasurable_left (hPm t) ((hPi t).mul_bdd
        ((hqm (t + 1)).mono (S.𝓕.le _)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hqb (t + 1) ω)) (hq (t + 1))
    have h2 := S.E_pullOut (hPsm t) (C := Ms) (Eventually.of_forall fun ω => by
      rw [abs_of_pos (hPs0 t ω)]; exact (hPs t ω).2) (hqsi (t + 1))
    have h3 := hrate t
    rw [e1, e2] at h3
    filter_upwards [h1, h2, h3] with ω f1 f2 f3
    rw [f1, f2] at f3
    simp only [Pi.mul_apply] at f3 ⊢
    have hp := (hP t ω).ne'
    rw [show γ t ω * q t ω = Pstar t ω * S.E t (qs (t + 1)) ω / P t ω by
      simp only [hγ_def, hq_def]; ring, eq_div_iff hp]
    linarith
  have hqsrate : ∀ t, S.E t (qs (t + 1)) = γ t * qs t := fun t => by
    funext ω
    simp only [Pi.mul_apply, hγ_def, hqs_def]
    field_simp [(hPs0 t ω).ne']
  -- `Z_t = V_t/P_t`, `Z*_t = a_t/P*_t` and `X = Z − Z*`
  set Z : ℕ → Ω → ℝ := fun t ω => V t ω * q t ω with hZ_def
  set Zs : ℕ → Ω → ℝ := fun t ω => a t ω * qs t ω with hZs_def
  have hZi : ∀ t, Integrable (Z t) S.μ := fun t =>
    (hVi t).mul_bdd ((hqm t).mono (S.𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hqb t ω)
  have hZsi : ∀ t, Integrable (Zs t) S.μ := fun t =>
    (hqsi t).bdd_mul ((ham t).mono (S.𝓕.le t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact haK t ω)
  have hEZ : ∀ t, S.E t (Z (t + 1)) =ᵐ[S.μ] fun ω => V (t + 1) ω * (γ t ω * q t ω) := fun t => by
    have h : S.E t (V (t + 1) * q (t + 1)) =ᵐ[S.μ] V (t + 1) * S.E t (q (t + 1)) :=
      condExp_mul_of_stronglyMeasurable_left (hVm' t) (hZi (t + 1)) (hq (t + 1))
    filter_upwards [h, hqrate t] with ω e1 e2
    change S.E t (V (t + 1) * q (t + 1)) ω = _
    rw [e1, Pi.mul_apply, e2, Pi.mul_apply]
  have hEZs : ∀ t, S.E t (Zs (t + 1)) =ᵐ[S.μ]
      fun ω => a (t + 1) ω * S.E t (qs (t + 1)) ω := fun t => by
    have h := S.E_pullOut (hapre t) (Eventually.of_forall fun ω => haK (t + 1) ω) (hqsi (t + 1))
    filter_upwards [h] with ω e1
    change S.E t (a (t + 1) * qs (t + 1)) ω = _
    rw [e1, Pi.mul_apply]
  set X : ℕ → Ω → ℝ := fun t => Z t - Zs t with hX_def
  have hXi : ∀ t, Integrable (X t) S.μ := fun t => (hZi t).sub (hZsi t)
  have hEX : ∀ t, S.E t (X (t + 1)) =ᵐ[S.μ] fun ω => γ t ω * X t ω / β := fun t => by
    filter_upwards [S.E_sub (hZi (t + 1)) (hZsi (t + 1)) t, hEZ t, hEZs t] with ω e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3]
    have hv : V (t + 1) ω = (V t ω - P t ω) / β := by
      rw [hVrec t ω]; field_simp; ring
    have ha' : a (t + 1) ω = (a t ω - Pstar t ω) / β := by
      rw [ha t ω]; field_simp; ring
    have hp := (hP t ω).ne'
    have hps := (hPs0 t ω).ne'
    simp only [hX_def, hZ_def, hZs_def, hγ_def, hq_def, hqs_def, Pi.sub_apply]
    rw [hv, ha']
    field_simp
    ring
  -- the deflator `Ninv_t = ∏_{i<t} γ_i⁻¹`
  set Ninv : ℕ → Ω → ℝ := fun t ω => ∏ i ∈ Finset.range t, (γ i ω)⁻¹ with hN_def
  have hNmeas : ∀ s t, s ≤ t + 1 → StronglyMeasurable[S.𝓕 t] (Ninv s) := fun s t hst => by
    have : Measurable[S.𝓕 t] (Ninv s) := Finset.measurable_prod _ fun i hi =>
      ((hγm i).mono (S.𝓕.mono (by have := Finset.mem_range.1 hi; omega))).measurable.inv
    exact this.stronglyMeasurable
  have hNb : ∀ t, ∀ᵐ ω ∂S.μ, 0 < Ninv t ω ∧ Ninv t ω ≤ (Ms / m) ^ t := fun t => by
    filter_upwards [ae_all_iff.2 hγb] with ω h
    have hMs : 0 < Ms := (hPs0 0 ω).trans_le (hPs 0 ω).2
    have hpos : ∀ i, 0 < γ i ω := fun i => (div_pos hm hMs).trans_le (h i).1
    refine ⟨Finset.prod_pos fun i _ => inv_pos.2 (hpos i), ?_⟩
    calc Ninv t ω ≤ ∏ _i ∈ Finset.range t, Ms / m :=
          Finset.prod_le_prod₀ (fun i _ => (inv_pos.2 (hpos i)).le) fun i _ => by
            rw [← inv_div]
            exact inv_anti₀ (div_pos hm hMs) (h i).1
      _ = (Ms / m) ^ t := by rw [Finset.prod_const, Finset.card_range]
  have hNbd : ∀ t, ∃ C, ∀ᵐ ω ∂S.μ, |Ninv t ω| ≤ C := fun t =>
    ⟨(Ms / m) ^ t, (hNb t).mono fun ω h => by rw [abs_of_pos h.1]; exact h.2⟩
  have hNγ : ∀ t, ∀ᵐ ω ∂S.μ, Ninv (t + 1) ω * γ t ω = Ninv t ω := fun t => by
    filter_upwards [hγpos t] with ω h
    simp only [hN_def, Finset.prod_range_succ]
    field_simp
  -- `Y_t = Ninv_t X_t` satisfies `Y_t = β E_t Y_{t+1}`
  set Y : ℕ → Ω → ℝ := fun t => Ninv t * X t with hY_def
  have hYi : ∀ t, Integrable (Y t) S.μ := fun t => by
    obtain ⟨C, hC⟩ := hNbd t
    exact (hXi t).bdd_mul ((hNmeas t t (Nat.le_succ t)).mono (S.𝓕.le t)).aestronglyMeasurable
      (hC.mono fun ω h => by rwa [Real.norm_eq_abs])
  have hY : ∀ t, Y t =ᵐ[S.μ] β • S.E t (Y (t + 1)) := fun t => by
    obtain ⟨C, hC⟩ := hNbd (t + 1)
    have h := S.E_pullOut (hNmeas (t + 1) t le_rfl) hC (hXi (t + 1))
    filter_upwards [h, hEX t, hγpos t] with ω e1 e2 e3
    change Ninv t ω * X t ω = β * S.E t (Ninv (t + 1) * X (t + 1)) ω
    rw [e1, Pi.mul_apply, e2]
    simp only [hN_def, Finset.prod_range_succ]
    field_simp
  -- hence `X ≡ 0`
  have hX0 : ∀ s, X s =ᵐ[S.μ] 0 := by
    intro s
    have hNinvY : Y s =ᵐ[S.μ] 0 := by
      have hit := iterate_beta S hY s
      have hmqs := deflated_martingale S (γ := γ) (ρ := qs) (Ninv := Ninv) hqsm hqsi
        (fun t => hNmeas t t (Nat.le_succ t)) (fun t => hNmeas (t + 1) t le_rfl) hNbd hNγ
        (fun t => EventuallyEq.of_eq (hqsrate t))
      have hFi : ∀ n, Integrable (Ninv n * V n) S.μ := fun n => by
        obtain ⟨C, hC⟩ := hNbd n
        exact (hVi n).bdd_mul ((hNmeas n n (Nat.le_succ n)).mono (S.𝓕.le n)).aestronglyMeasurable
          (hC.mono fun ω h => by rwa [Real.norm_eq_abs])
      have hGi : ∀ n, Integrable (Ninv n * qs n) S.μ := fun n => by
        obtain ⟨C, hC⟩ := hNbd n
        exact (hqsi n).bdd_mul ((hNmeas n n (Nat.le_succ n)).mono (S.𝓕.le n)).aestronglyMeasurable
          (hC.mono fun ω h => by rwa [Real.norm_eq_abs])
      -- the deflator over `[s, s + n)` is bounded by `L`
      have hNL : ∀ n, ∀ᵐ ω ∂S.μ, Ninv (s + n) ω ≤ L * Ninv s ω := fun n => by
        filter_upwards [hL s n, hNb s] with ω h1 h2
        simp only [hN_def, Finset.prod_range_add]
        rw [mul_comm L]
        exact mul_le_mul_of_nonneg_left h1 h2.1.le
      have hEV : ∀ n, S.E s (Ninv (s + n) * V (s + n)) ≤ᵐ[S.μ]
          fun ω => L * Ninv s ω * S.E s (V (s + n)) ω := fun n => by
        obtain ⟨C, hC⟩ := hNbd s
        have hLi : Integrable ((fun ω => L * Ninv s ω) * V (s + n)) S.μ :=
          (hVi (s + n)).bdd_mul
            (((hNmeas s s (Nat.le_succ s)).const_mul L).mono (S.𝓕.le s)).aestronglyMeasurable
            (c := |L| * C) (hC.mono fun ω h => by
              rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg L))
        have hmono := S.E_mono (hFi (s + n)) hLi (by
          filter_upwards [hNL n, hVb (s + n)] with ω e1 e2
          simp only [Pi.mul_apply]
          exact mul_le_mul_of_nonneg_right e1 e2) s
        have hpo := S.E_pullOut ((hNmeas s s (Nat.le_succ s)).const_mul L) (C := |L| * C)
          (hC.mono fun ω h => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg L))
          (hVi (s + n))
        filter_upwards [hmono, hpo] with ω e1 e2
        rw [e2] at e1
        exact e1
      refine zero_of_iterate' S hβ0 (t := s)
        (W := fun k => mP⁻¹ • (Ninv (s + (k + 1)) * V (s + (k + 1))) +
          K • (Ninv (s + (k + 1)) * qs (s + (k + 1)))) hit (fun k => hYi _)
        (fun k => ((hFi _).smul _).add ((hGi _).smul K)) (fun k => ?_) ?_
      · filter_upwards [hNb (s + (k + 1)), hVb (s + (k + 1))] with ω e1 e2
        set n := s + (k + 1)
        simp only [hY_def, hX_def, hZ_def, hZs_def, Pi.mul_apply, Pi.sub_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul]
        have hqpos : 0 < q n ω := one_div_pos.2 (hP n ω)
        have hqspos : 0 < qs n ω := one_div_pos.2 (hPs0 n ω)
        rw [abs_mul, abs_of_pos e1.1]
        have hqle : q n ω ≤ mP⁻¹ := by
          have := hqb n ω
          rw [abs_of_pos hqpos, one_div] at this
          exact this
        have hb : |V n ω * q n ω - a n ω * qs n ω| ≤ mP⁻¹ * V n ω + K * qs n ω := by
          calc _ ≤ |V n ω * q n ω| + |a n ω * qs n ω| := abs_sub _ _
            _ = V n ω * q n ω + |a n ω| * qs n ω := by
              rw [abs_mul, abs_mul, abs_of_pos hqpos, abs_of_pos hqspos, abs_of_nonneg e2]
            _ ≤ _ := add_le_add (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hqle e2)
              (mul_le_mul_of_nonneg_right (haK n ω) hqspos.le)
        calc Ninv n ω * |V n ω * q n ω - a n ω * qs n ω|
            ≤ Ninv n ω * (mP⁻¹ * V n ω + K * qs n ω) := mul_le_mul_of_nonneg_left hb e1.1.le
          _ = _ := by ring
      · have h1 : ∀ k, S.E s (mP⁻¹ • (Ninv (s + (k + 1)) * V (s + (k + 1))) +
            K • (Ninv (s + (k + 1)) * qs (s + (k + 1)))) ≤ᵐ[S.μ]
            fun ω => mP⁻¹ * (L * Ninv s ω * S.E s (V (s + (k + 1))) ω) +
              K * (Ninv s ω * qs s ω) := fun k => by
          have e1 := S.E_add ((hFi (s + (k + 1))).smul mP⁻¹) ((hGi (s + (k + 1))).smul K) s
          have e2 := S.E_smul mP⁻¹ (Ninv (s + (k + 1)) * V (s + (k + 1))) s
          have e3 := S.E_smul K (Ninv (s + (k + 1)) * qs (s + (k + 1))) s
          filter_upwards [e1, e2, e3, hEV (k + 1), hmqs s (k + 1)] with ω f1 f2 f3 f4 f5
          rw [f1, Pi.add_apply, f2, f3, Pi.smul_apply, Pi.smul_apply, f5, smul_eq_mul,
            smul_eq_mul]
          have := mul_le_mul_of_nonneg_left f4 (inv_pos.2 hmP).le
          simp only [Pi.mul_apply]
          linarith
        have h0 : ∀ k, ∀ᵐ ω ∂S.μ, 0 ≤ S.E s (mP⁻¹ • (Ninv (s + (k + 1)) * V (s + (k + 1))) +
            K • (Ninv (s + (k + 1)) * qs (s + (k + 1)))) ω := fun k => by
          have hmono := S.E_mono (integrable_const 0) (((hFi _).smul mP⁻¹).add ((hGi _).smul K))
            (by
              filter_upwards [hNb (s + (k + 1)), hVb (s + (k + 1))] with ω e1 e2
              simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
              have : 0 ≤ qs (s + (k + 1)) ω := (one_div_pos.2 (hPs0 _ ω)).le
              have hK : 0 ≤ K := (abs_nonneg _).trans (haK 0 ω)
              exact add_nonneg (mul_nonneg (inv_nonneg.2 hmP.le) (mul_nonneg e1.1.le e2))
                (mul_nonneg hK (mul_nonneg e1.1.le this))) s
          rw [S.E_const] at hmono
          exact hmono
        filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h0, hVtvc s, hNb s] with ω e1 e2 e3 e4
        have hlim : Tendsto (fun k => β ^ (k + 1) * (mP⁻¹ * (L * Ninv s ω *
            S.E s (V (s + (k + 1))) ω) + K * (Ninv s ω * qs s ω))) atTop (𝓝 0) := by
          have h3 := (e3.comp (tendsto_add_atTop_nat 1)).const_mul (mP⁻¹ * L * Ninv s ω)
          have h4 := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
            (tendsto_add_atTop_nat 1)).mul_const (K * (Ninv s ω * qs s ω))
          have := h3.add h4
          simp only [mul_zero, zero_mul, add_zero] at this
          refine this.congr fun k => ?_
          simp only [Function.comp]
          ring
        refine squeeze_zero (fun k => mul_nonneg (pow_pos hβ0 _).le (e2 k)) (fun k => ?_) hlim
        exact mul_le_mul_of_nonneg_left (e1 k) (pow_pos hβ0 _).le
    filter_upwards [hNinvY, hNb s] with ω e1 e2
    change Ninv s ω * X s ω = 0 at e1
    exact (mul_eq_zero.1 e1).resolve_left e2.1.ne'
  have hXe : ∀ s, ∀ᵐ ω ∂S.μ, V s ω * q s ω = a s ω * qs s ω := fun s => by
    filter_upwards [hX0 s] with ω h
    simp only [hX_def, hZ_def, hZs_def, Pi.sub_apply, Pi.zero_apply] at h
    linarith
  have hr : ∀ s, ∀ᵐ ω ∂S.μ, Pstar (s + 1) ω * q (s + 1) ω = Pstar s ω * q s ω := fun s => by
    have hZZ : Z (s + 1) =ᵐ[S.μ] Zs (s + 1) := by
      filter_upwards [hX0 (s + 1)] with ω h
      simp only [hX_def, Pi.sub_apply, Pi.zero_apply] at h
      linarith
    filter_upwards [S.E_congr hZZ s, hEZ s, hEZs s, hXe (s + 1), hEqs s] with ω e1 e2 e3 e4 e5
    rw [e2, e3] at e1
    have hMs : 0 < Ms := (hPs0 s ω).trans_le (hPs s ω).2
    have hE : 0 < S.E s (qs (s + 1)) ω := (one_div_pos.2 hMs).trans_le e5.1
    have hA : V (s + 1) ω * (Pstar s ω * q s ω) = a (s + 1) ω := by
      have h : (V (s + 1) ω * (Pstar s ω * q s ω)) * S.E s (qs (s + 1)) ω =
          a (s + 1) ω * S.E s (qs (s + 1)) ω := by
        rw [← e1]
        simp only [hγ_def]
        ring
      exact mul_right_cancel₀ hE.ne' h
    have hB : V (s + 1) ω * (Pstar (s + 1) ω * q (s + 1) ω) = a (s + 1) ω := by
      have h1 : Pstar (s + 1) ω * qs (s + 1) ω = 1 := by
        simp only [hqs_def]
        field_simp [(hPs0 (s + 1) ω).ne']
      calc _ = (V (s + 1) ω * q (s + 1) ω) * Pstar (s + 1) ω := by ring
        _ = a (s + 1) ω * (Pstar (s + 1) ω * qs (s + 1) ω) := by rw [e4]; ring
        _ = _ := by rw [h1, mul_one]
    have hV0 : V (s + 1) ω ≠ 0 := fun h => by
      rw [h, zero_mul] at hA
      exact (hapos (s + 1) ω).ne' hA.symm
    exact mul_left_cancel₀ hV0 (hB.trans hA.symm)
  have hr0 : ∀ s, ∀ᵐ ω ∂S.μ, Pstar s ω * q s ω = Pstar 0 ω * q 0 ω := by
    intro s
    induction s with
    | zero => exact Eventually.of_forall fun ω => rfl
    | succ s ih =>
      filter_upwards [ih, hr s] with ω e1 e2
      rw [e2, e1]
  filter_upwards [hr0 t, hXe 0] with ω e1 e2
  have hV0 : V 0 ω = θ⁻¹ * (b0 - bbar) + a 0 ω := by simp only [hV_def, hb0 ω]
  simp only [hq_def, hqs_def] at e1 e2
  rw [hV0] at e2
  have hp0 := (hP 0 ω).ne'
  have hpt := (hP t ω).ne'
  have hs0 := (hPs0 0 ω).ne'
  have hst := (hPs0 t ω).ne'
  have ha0 := (hapos 0 ω).ne'
  field_simp at e1 e2 ⊢
  refine mul_left_cancel₀ hs0 ?_
  linear_combination (-(θ * a 0 ω)) * e1 - Pstar t ω * e2

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d)** with a stochastic target): with initial
debt equal to the present value of `s₀` (`b₀ = b̄`), bounded-above prices and a target whose present
value is predetermined, the only equilibrium is `P = P*` (a.e., at every date). -/
theorem fr_unique_stochastic_target {β θ bbar m Ms M K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {Pstar P b a : ℕ → Ω → ℝ}
    (hP : ∀ t ω, 0 < P t ω) (hPa : StronglyAdapted S.𝓕 P) (hPM : ∀ t ω, P t ω ≤ M)
    (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ K)
    (hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ] S.E t (Pstar t / Pstar (t + 1)))
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω)
    (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1))) (hb0 : ∀ ω, b 0 ω = bbar)
    (hbi : ∀ t, Integrable (b t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0))
    (t : ℕ) : P t =ᵐ[S.μ] Pstar t := by
  filter_upwards [fr_unique_stochastic S hβ0 hβ1 hθ hP hPa hPM hq hPsa hm hPs ha hapre haK hrate
    hflow hpre hb0 hbi htvc t] with ω h
  rw [h, sub_self, zero_div, add_zero, one_mul]

/-- Cochrane (2023), §9.3.2, p. 267 (initial debt different from the present value of `s₀`): on any
measure-theoretic system, if the price level equals the target at every date, the flow (9.8) and the
transversality condition force `b₀ = b̄` — with `b₀ ≠ b̄` the rule can never deliver `P = P*`, for
any target and without any bound. -/
theorem initial_debt_of_target {β θ bbar b0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Pstar P b : ℕ → Ω → ℝ}
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - Pstar t ω) + β * b (t + 1) ω)
    (hb0 : ∀ ω, b 0 ω = b0)
    (htvc : ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E 0 (b (0 + T)) ω) atTop (𝓝 0))
    (hPP : ∀ t, P t =ᵐ[S.μ] Pstar t) : b0 = bbar := by
  have hrec : ∀ T, ∀ᵐ ω ∂S.μ, b T ω = bbar + (β ^ T)⁻¹ * (b0 - bbar) := by
    intro T
    induction T with
    | zero => exact Eventually.of_forall fun ω => by simp [hb0 ω]
    | succ T ih =>
      filter_upwards [ih, hPP T] with ω e1 e2
      have h := hflow T ω
      rw [e2, sub_self, mul_zero, add_zero, e1] at h
      have hβT : β ^ T ≠ 0 := pow_ne_zero T hβ0.ne'
      rw [pow_succ, mul_inv]
      field_simp
      field_simp at h
      linarith
  have hE : ∀ T, ∀ᵐ ω ∂S.μ, S.E 0 (b (0 + T)) ω = bbar + (β ^ T)⁻¹ * (b0 - bbar) := by
    intro T
    have h := S.E_congr (hrec T) 0
    rw [S.E_const] at h
    rw [zero_add]
    exact h
  obtain ⟨ω, h1, h2⟩ := (htvc.and (ae_all_iff.2 hE)).exists
  have e : ∀ T, β ^ T * S.E 0 (b (0 + T)) ω = β ^ T * bbar + (b0 - bbar) := fun T => by
    rw [h2 T, mul_add, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero T hβ0.ne'), one_mul]
  simp_rw [e] at h1
  have h3 : Tendsto (fun T => β ^ T * bbar + (b0 - bbar)) atTop (𝓝 (b0 - bbar)) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const bbar).add_const
      (b0 - bbar)
  have := tendsto_nhds_unique h3 h1
  linarith

/-- Cochrane (2023), §9.3.2, p. 267: a deterministic bounded target `p` has the predetermined
present value `a_t = ∑ⱼ βʲ p_{t+j}`, so `fr_unique_stochastic` covers every deterministic target. -/
theorem deterministic_target {β m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (Pstar : ℕ → ℝ)
    (hPs : ∀ t, m ≤ Pstar t ∧ Pstar t ≤ Ms) (hm : 0 < m) :
    (∀ t (ω : Ω), (fun t (_ : Ω) => ∑' j, β ^ j * Pstar (t + j)) t ω =
        Pstar t + β * (fun t (_ : Ω) => ∑' j, β ^ j * Pstar (t + j)) (t + 1) ω) ∧
      (∀ t, StronglyMeasurable[S.𝓕 t] ((fun t (_ : Ω) => ∑' j, β ^ j * Pstar (t + j)) (t + 1))) ∧
      ∀ t (ω : Ω), |(fun t (_ : Ω) => ∑' j, β ^ j * Pstar (t + j)) t ω| ≤ Ms / (1 - β) := by
  have hb : ∀ j, |Pstar j| ≤ Ms := fun j => by
    rw [abs_of_pos (hm.trans_le (hPs j).1)]; exact (hPs j).2
  exact ⟨fun t _ => FiscalRules.tsum_shift hβ0.le hβ1 hb t, fun _ => stronglyMeasurable_const,
    fun t _ => FiscalRules.abs_tsum_le hβ0.le hβ1 hb t⟩

/-- Cochrane (2023), §9.3.2, p. 267: the lag `η_{t−1}` (with `η_{−1} = 0`). -/
def lag (η : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | n + 1 => η n

/-- Cochrane (2023), §9.3.2, p. 267 (a stochastic target with predetermined present value, the
target analogue of `s_{0,t} = a(L) ε_t` with `a(β) = 0`, p. 266): `P*_t = p̄ + η_t − η_{t−1}/β`. -/
noncomputable def sTarget (β pbar : ℝ) (η : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  pbar + η t ω - lag η t ω / β

/-- Cochrane (2023), §9.3.2, p. 267: the present value of `sTarget`, `a_t = p̄/(1 − β) − η_{t−1}/β`.
-/
noncomputable def sValue (β pbar : ℝ) (η : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  pbar / (1 - β) - lag η t ω / β

/-- Cochrane (2023), §9.3.2, p. 267: for adapted `|η| ≤ B` the s-shaped target is adapted, bounded,
and its present value `sValue` is bounded, predetermined and satisfies `a_t = P*_t + β a_{t+1}`. -/
theorem sTarget_props {β pbar B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {η : ℕ → Ω → ℝ}
    (hηa : StronglyAdapted S.𝓕 η) (hηB : ∀ t ω, |η t ω| ≤ B) :
    StronglyAdapted S.𝓕 (sTarget β pbar η) ∧
      (∀ t ω, pbar - B - B / β ≤ sTarget β pbar η t ω ∧
        sTarget β pbar η t ω ≤ pbar + B + B / β) ∧
      (∀ t ω, sValue β pbar η t ω = sTarget β pbar η t ω + β * sValue β pbar η (t + 1) ω) ∧
      (∀ t, StronglyMeasurable[S.𝓕 t] (sValue β pbar η (t + 1))) ∧
      ∀ t ω, |sValue β pbar η t ω| ≤ |pbar| / (1 - β) + B / β := by
  have hlag : ∀ t, StronglyMeasurable[S.𝓕 t] (lag η t) := fun t => by
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ n => exact (hηa n).mono (S.𝓕.mono (Nat.le_succ n))
  have hlagB : ∀ t ω, |lag η t ω| ≤ B := fun t ω => by
    cases t with
    | zero => simpa [lag] using (abs_nonneg _).trans (hηB 0 ω)
    | succ n => exact hηB n ω
  have h1β : 0 < 1 - β := by linarith
  refine ⟨fun t => ?_, fun t ω => ?_, fun t ω => ?_, fun t => ?_, fun t ω => ?_⟩
  · exact (stronglyMeasurable_const.add (hηa t)).sub
      ((hlag t).measurable.div_const β).stronglyMeasurable
  · have h1 := abs_le.1 (hηB t ω)
    have h2 := abs_le.1 (hlagB t ω)
    have h3 : lag η t ω / β ≤ B / β := div_le_div_of_nonneg_right h2.2 hβ0.le
    have h4 : -B / β ≤ lag η t ω / β := div_le_div_of_nonneg_right h2.1 hβ0.le
    simp only [sTarget]
    constructor
    · linarith
    · have : -B / β = -(B / β) := by ring
      linarith
  · simp only [sValue, sTarget, lag]
    field_simp
    ring
  · exact stronglyMeasurable_const.sub ((hηa t).measurable.div_const β).stronglyMeasurable
  · simp only [sValue]
    calc |pbar / (1 - β) - lag η t ω / β| ≤ |pbar / (1 - β)| + |lag η t ω / β| := abs_sub _ _
      _ = |pbar| / (1 - β) + |lag η t ω| / β := by
        rw [abs_div, abs_div, abs_of_pos h1β, abs_of_pos hβ0]
      _ ≤ _ := by gcongr; exact hlagB t ω

namespace BoolExample

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): information on `Bool` — nothing at date 0, the
state at every later date. -/
def boolInfo (t : ℕ) : Setoid Bool where
  r a b := t = 0 ∨ a = b
  iseqv := ⟨fun _ => Or.inr rfl, fun h => h.elim Or.inl fun h => Or.inr h.symm,
    fun h1 h2 => h1.elim Or.inl fun h1 => h2.elim Or.inl fun h2 => Or.inr (h1.trans h2)⟩

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): a fair coin revealed at date 1. -/
noncomputable def boolTree : ExpectationsFiniteTree.FiniteTree Bool where
  prob _ := 1 / 2
  prob_pos _ := by norm_num
  prob_sum := by simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]; norm_num
  info := boolInfo
  refines := fun {s t} hst a b h => h.elim (fun h => Or.inl (by omega)) Or.inr

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the coin as a measure-theoretic expectation
system. -/
noncomputable def boolSystem : MeasExpectationSystem Bool := TreeBridge.treeSystem boolTree

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): both states have positive probability. -/
theorem boolSystem_fullSupport (ω : Bool) : boolSystem.μ {ω} ≠ 0 :=
  TreeBridge.treeSystem_fullSupport boolTree ω

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `E_0 x = (x true + x false)/2`. -/
theorem boolE_zero (x : Bool → ℝ) : boolSystem.E 0 x = fun _ => (x true + x false) / 2 := by
  funext ω
  rw [boolSystem, TreeBridge.treeSystem_E, boolTree.condE_of_trivial (fun a b => Or.inl rfl)]
  simp [boolTree]
  ring

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): from date 1 on everything is known, `E_{t+1} x
= x`. -/
theorem boolE_succ (n : ℕ) (x : Bool → ℝ) : boolSystem.E (n + 1) x = x := by
  funext ω
  rw [boolSystem, TreeBridge.treeSystem_E]
  exact boolTree.condE_of_const_on_cell fun ω' h =>
    h.elim (fun h => absurd h (Nat.succ_ne_zero n)) fun h => by rw [h]

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): every variable is known from date 1. -/
theorem bool_stronglyMeasurable_succ (n : ℕ) (x : Bool → ℝ) :
    StronglyMeasurable[boolSystem.𝓕 (n + 1)] x := by
  have h := boolSystem.stronglyMeasurable_E (n + 1) x
  rwa [boolE_succ] at h

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the stochastic target `P*_0 = 9/7`, then `P*_t
= 3` or `1` forever according to the coin; its present value from date 1 has news at date 1. -/
noncomputable def Ps (t : ℕ) (ω : Bool) : ℝ := if t = 0 then 9 / 7 else if ω then 3 else 1

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the equilibrium price `P_t = P*_t + 1`. -/
noncomputable def Pc (t : ℕ) (ω : Bool) : ℝ := Ps t ω + 1

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): constant real debt `b̄ + θ/(1 − β)`. -/
noncomputable def bc (β θ bbar : ℝ) (_t : ℕ) (_ω : Bool) : ℝ := bbar + θ / (1 - β)

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `1 ≤ P* ≤ 3`. -/
theorem Ps_bounds (t : ℕ) (ω : Bool) : 1 ≤ Ps t ω ∧ Ps t ω ≤ 3 := by
  unfold Ps
  split_ifs <;> norm_num

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): a process with a constant date-0 value is
adapted. -/
theorem bool_adapted (x : ℕ → Bool → ℝ) (hx : ∃ c, ∀ ω, x 0 ω = c) :
    StronglyAdapted boolSystem.𝓕 x := fun t => by
  cases t with
  | zero =>
    obtain ⟨c, hc⟩ := hx
    have : x 0 = fun _ => c := funext hc
    rw [this]
    exact stronglyMeasurable_const
  | succ n => exact bool_stronglyMeasurable_succ n (x (n + 1))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): `P = P* + 1`, `b ≡ b̄ + θ/(1 − β)` is an
equilibrium of the rule (`RuleEqm`) with the stochastic target `Ps` (the coin probabilities make
`E_0(P_0/P_1) = E_0(P*_0/P*_1) = 6/7`). -/
theorem bool_ruleEqm {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (θ bbar : ℝ) :
    RuleEqm boolSystem β θ bbar Ps Pc (bc β θ bbar) := by
  have h1β : (1 : ℝ) - β ≠ 0 := by linarith
  refine ⟨fun t ω => by unfold Pc; linarith [(Ps_bounds t ω).1],
    bool_adapted Pc ⟨16 / 7, fun ω => by simp [Pc, Ps]; norm_num⟩,
    fun _ => Integrable.of_finite, fun _ => Integrable.of_finite, fun t => ?_,
    fun t ω => ?_, fun _ => stronglyMeasurable_const, fun t => ?_, fun t => ?_⟩
  · refine EventuallyEq.of_eq ?_
    cases t with
    | zero =>
      rw [boolE_zero, boolE_zero]
      funext ω
      simp [Pc, Ps]
      norm_num
    | succ n =>
      congr 1
      funext ω
      cases ω <;> norm_num [Pc, Ps]
  · simp only [bc, Pc]
    field_simp
    ring
  · refine Eventually.of_forall fun ω => ?_
    have e : ∀ j, (fun ω' => (1 - β) * bbar + θ * (Pc (t + j) ω' - Ps (t + j) ω')) =
        fun _ => (1 - β) * bbar + θ := fun j => by
      funext ω'
      simp only [Pc]
      ring
    simp only [e, boolSystem.E_const, bc]
    have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left ((1 - β) * bbar + θ)
    convert this using 1
    · funext j
      ring
    · field_simp
  · refine Eventually.of_forall fun ω => ?_
    have e : ∀ T, bc β θ bbar (t + T) = fun _ => bbar + θ / (1 - β) := fun T => rfl
    simp only [e, boolSystem.E_const]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const
      (bbar + θ / (1 - β))

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the equilibrium price is not proportional to
the target, `P ≠ c P*` for every constant `c` (and date-0 variables are constants here). -/
theorem Pc_not_proportional : ¬ ∃ c : ℝ, ∀ t, Pc t =ᵐ[boolSystem.μ] fun ω => c * Ps t ω := by
  rintro ⟨c, hc⟩
  have h := congrFun (boolSystem.eq_of_ae_eq boolSystem_fullSupport (hc 1))
  have h1 := h true
  have h2 := h false
  simp [Pc, Ps] at h1 h2
  linarith

/-- Cochrane (2023), §9.3.2, p. 267 (counterexample): the target's present value is not
predetermined — no bounded `a` with `a_t = P*_t + β a_{t+1}` and `a_{t+1}` known at `t` exists. -/
theorem no_targetValue {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ¬ ∃ a : ℕ → Bool → ℝ, (∀ t ω, a t ω = Ps t ω + β * a (t + 1) ω) ∧
      (∀ t, StronglyMeasurable[boolSystem.𝓕 t] (a (t + 1))) ∧ ∀ t ω, |a t ω| ≤ K := by
  rintro ⟨a, ha, hapre, haK⟩
  have h1β : 0 < 1 - β := by linarith
  have hconst : a 1 true = a 1 false := by
    have h := boolSystem.E_of_stronglyMeasurable (hapre 0) Integrable.of_finite
    rw [boolE_zero] at h
    have e1 := congrFun h true
    have e2 := congrFun h false
    linarith
  have hval : ∀ ω, a 1 ω = Ps 1 ω / (1 - β) := fun ω => by
    set c := Ps 1 ω / (1 - β) with hc
    have hPs : ∀ t, Ps (1 + t) ω = Ps 1 ω := fun t => by simp [Ps]
    have hrec : ∀ k, a 1 ω - c = β ^ k * (a (1 + k) ω - c) := fun k => by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [ih, ha (1 + k) ω, hPs k, show 1 + k + 1 = 1 + (k + 1) by ring, pow_succ]
        rw [hc]
        field_simp
        ring
    have hb : ∀ k, |a 1 ω - c| ≤ β ^ k * (K + |c|) := fun k => by
      rw [hrec k, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith [haK (1 + k) ω]))
        (pow_pos hβ0 k).le
    have hlim : Tendsto (fun k => β ^ k * (K + |c|)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (K + |c|)
    have := ge_of_tendsto' hlim hb
    have h0 := abs_nonpos_iff.mp this
    linarith
  rw [hval, hval] at hconst
  simp [Ps] at hconst
  field_simp at hconst
  norm_num at hconst

/-- Cochrane (2023), §9.3.2, p. 267 (**what fails without a predetermined target value**): with a
bounded stochastic target whose present value has news, and initial debt `b₀ = b̄ + θ/(1 − β) ≠ b̄`,
there is a bounded equilibrium (`2 ≤ P ≤ 4`) that is not of the form `P = c P*` predicted by
`fr_unique_stochastic`; the hypothesis of a predetermined target value fails. -/
theorem bool_counterexample {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {θ : ℝ} (hθ : θ ≠ 0)
    (bbar : ℝ) :
    RuleEqm boolSystem β θ bbar Ps Pc (bc β θ bbar) ∧ (∀ ω, bc β θ bbar 0 ω ≠ bbar) ∧
      (∀ t ω, 2 ≤ Pc t ω ∧ Pc t ω ≤ 4) ∧ StronglyAdapted boolSystem.𝓕 Ps ∧
      (∀ t ω, 1 ≤ Ps t ω ∧ Ps t ω ≤ 3) ∧
      (¬ ∃ c : ℝ, ∀ t, Pc t =ᵐ[boolSystem.μ] fun ω => c * Ps t ω) ∧
      ∀ K, ¬ ∃ a : ℕ → Bool → ℝ, (∀ t ω, a t ω = Ps t ω + β * a (t + 1) ω) ∧
        (∀ t, StronglyMeasurable[boolSystem.𝓕 t] (a (t + 1))) ∧ ∀ t ω, |a t ω| ≤ K := by
  have h1β : (1 : ℝ) - β ≠ 0 := by linarith
  refine ⟨bool_ruleEqm hβ0 hβ1 θ bbar, fun ω h => ?_, fun t ω => ?_,
    bool_adapted Ps ⟨9 / 7, fun ω => by simp [Ps]⟩, Ps_bounds, Pc_not_proportional,
    fun K => no_targetValue (K := K) hβ0 hβ1⟩
  · simp only [bc, add_eq_left, div_eq_zero_iff, h1β, or_false] at h
    exact hθ h
  · have := Ps_bounds t ω
    simp only [Pc]
    constructor <;> linarith

end BoolExample

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d)**, measure setting):
`fr_unique_stochastic` for an equilibrium in the sense of `RuleEqm`. -/
theorem fr_unique_ruleEqm {β θ bbar b0 m Ms M K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {Pstar P b a : ℕ → Ω → ℝ} (hE : RuleEqm S β θ bbar Pstar P b)
    (hPM : ∀ t ω, P t ω ≤ M) (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ K)
    (hb0 : ∀ ω, b 0 ω = b0) (t : ℕ) :
    P t =ᵐ[S.μ] fun ω => (1 + (b0 - bbar) / (θ * a 0 ω)) * Pstar t ω := by
  obtain ⟨hP, hPa, -, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  exact fr_unique_stochastic S hβ0 hβ1 hθ hP hPa hPM hq hPsa hm hPs ha hapre haK hrate hflow
    hpre hb0 hbi htvc t

/-- Cochrane (2023), §9.3.2, p. 267 (**initial debt different from the present value of `s₀`**):
with `b₀ ≠ b̄`, a target with predetermined present value and bounded-above prices, the equilibrium
price level is pinned down, `P_t = (1 + (b₀ − b̄)/(θ a₀)) P*_t`, but it is not the target. -/
theorem fr_initial_debt {β θ bbar b0 m Ms M K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) (hb : b0 ≠ bbar) {Pstar P b a : ℕ → Ω → ℝ}
    (hE : RuleEqm S β θ bbar Pstar P b)
    (hPM : ∀ t ω, P t ω ≤ M) (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ K)
    (hb0 : ∀ ω, b 0 ω = b0) :
    (∀ t, P t =ᵐ[S.μ] fun ω => (1 + (b0 - bbar) / (θ * a 0 ω)) * Pstar t ω) ∧
      ¬ ∀ t, P t =ᵐ[S.μ] Pstar t := by
  refine ⟨fr_unique_ruleEqm S hβ0 hβ1 hθ hE hPM hq hPsa hm hPs ha hapre haK hb0, fun h => hb ?_⟩
  exact initial_debt_of_target S hβ0 hβ1 hE.2.2.2.2.2.1 hb0 (hE.2.2.2.2.2.2.2.2 0) h

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d)**, **link**): on a finite fully supported
system, the hypotheses of the core `FiscalRules.fr_unique_bounded` (bounded-above case, `P* ≡ 1`,
stated for the bridged core system `S.toExpectationSystem`) imply `P ≡ 1` through the
measure-theoretic theorem — the measure result specialises to the core one. -/
theorem fr_unique_bounded_link [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) {β θ bbar M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {P b : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPa : (S.toExpectationSystem hfull).Adapted P)
    (h912 : ∀ t, β • (S.toExpectationSystem hfull).E t (P t / P (t + 1)) = fun _ => β)
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - 1) + β * b (t + 1) ω)
    (hpre : ∀ t, (S.toExpectationSystem hfull).E t (b (t + 1)) = b (t + 1))
    (hb0 : ∀ ω, b 0 ω = bbar)
    (htvc : ∀ t ω, Tendsto (fun T => β ^ T * (S.toExpectationSystem hfull).E t (b (t + T)) ω)
      atTop (𝓝 0)) (hM : ∀ t ω, P t ω ≤ M) :
    P = fun _ _ => 1 := by
  have h1β : 0 < 1 - β := by linarith
  have hsm : ∀ t (x : Ω → ℝ), S.E t x = x → StronglyMeasurable[S.𝓕 t] x := fun t x h => by
    have := S.stronglyMeasurable_E t x
    rwa [h] at this
  have hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ]
      S.E t ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) (t + 1)) := fun t => by
    refine EventuallyEq.of_eq ?_
    have h := h912 t
    rw [S.toExpectationSystem_E] at h
    have e : ((fun _ _ => (1 : ℝ)) t / (fun _ _ => (1 : ℝ)) (t + 1) : Ω → ℝ) = fun _ => 1 := by
      funext ω
      simp
    rw [e, S.E_const]
    funext ω
    have := congrFun h ω
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have := mul_left_cancel₀ hβ0.ne' (this.trans (mul_one β).symm)
    exact this
  funext t
  refine S.eq_of_ae_eq hfull (fr_unique_stochastic_target S (m := 1) (Ms := 1) (M := M)
    (K := 1 / (1 - β)) (a := fun _ _ => 1 / (1 - β)) hβ0 hβ1 hθ hP
    (fun t => hsm t _ (hPa t)) hM (fun _ => Integrable.of_finite)
    (fun _ => stronglyMeasurable_const) one_pos (fun _ _ => ⟨le_rfl, le_rfl⟩)
    (fun _ _ => by field_simp; ring) (fun _ => stronglyMeasurable_const)
    (fun _ _ => by rw [abs_of_pos (one_div_pos.2 h1β)]) hrate hflow
    (fun t => hsm t _ (hpre t)) hb0 (fun _ => Integrable.of_finite)
    (fun t => Eventually.of_forall (htvc t)) t)

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d)**, **link**): the same conclusion from
the core theorem `FiscalRules.fr_unique_bounded` applied to the bridged system (which has the
pull-out property), so the two versions agree. -/
theorem fr_unique_bounded_link_core [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) {β θ bbar M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {P b : ℕ → Ω → ℝ} (hP : ∀ t ω, 0 < P t ω) (hPa : (S.toExpectationSystem hfull).Adapted P)
    (h912 : ∀ t, β • (S.toExpectationSystem hfull).E t (P t / P (t + 1)) = fun _ => β)
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - 1) + β * b (t + 1) ω)
    (hpre : ∀ t, (S.toExpectationSystem hfull).E t (b (t + 1)) = b (t + 1))
    (hb0 : ∀ ω, b 0 ω = bbar)
    (htvc : ∀ t ω, Tendsto (fun T => β ^ T * (S.toExpectationSystem hfull).E t (b (t + T)) ω)
      atTop (𝓝 0)) (hM : ∀ t ω, P t ω ≤ M) :
    P = fun _ _ => 1 :=
  FiscalRules.fr_unique_bounded (S.toExpectationSystem hfull) (S.toExpectationSystem_pullOut hfull)
    hβ0 hβ1 hθ hP hPa h912 hflow hpre hb0 htvc (Or.inl ⟨M, hM⟩)

/-- Cochrane (2023), §9.3.2, p. 267: the s-shaped target is genuinely stochastic — its news is the
news in `η`, `P*_{t+1} − E_t P*_{t+1} = η_{t+1} − E_t η_{t+1}` a.e. -/
theorem sTarget_news {β pbar B : ℝ} {η : ℕ → Ω → ℝ} (hηa : StronglyAdapted S.𝓕 η)
    (hηB : ∀ t ω, |η t ω| ≤ B) (t : ℕ) :
    sTarget β pbar η (t + 1) - S.E t (sTarget β pbar η (t + 1)) =ᵐ[S.μ]
      η (t + 1) - S.E t (η (t + 1)) := by
  have hηi : ∀ n, Integrable (η n) S.μ := fun n =>
    Integrable.of_bound ((hηa n).mono (S.𝓕.le n)).aestronglyMeasurable B
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hηB n ω)
  set g : Ω → ℝ := fun ω => η t ω / β with hg
  have hgm : StronglyMeasurable[S.𝓕 t] g := ((hηa t).measurable.div_const β).stronglyMeasurable
  have hgi : Integrable g S.μ := (hηi t).div_const β
  have e : sTarget β pbar η (t + 1) = ((fun _ => pbar) + η (t + 1)) - g := by
    funext ω
    simp [sTarget, lag, hg]
  rw [e]
  filter_upwards [S.E_sub ((integrable_const pbar).add (hηi (t + 1))) hgi t,
    S.E_add (integrable_const pbar) (hηi (t + 1)) t] with ω e1 e2
  rw [Pi.sub_apply, e1, Pi.sub_apply, Pi.sub_apply, e2, Pi.add_apply, S.E_const,
    S.E_of_stronglyMeasurable hgm hgi]
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d)** for a genuinely stochastic target):
with the s-shaped target and `b₀ = b̄`, the only bounded-above equilibrium is `P = P*`. -/
theorem fr_unique_sShaped {β θ bbar pbar B M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {η P b : ℕ → Ω → ℝ} (hηa : StronglyAdapted S.𝓕 η) (hηB : ∀ t ω, |η t ω| ≤ B)
    (hpos : 0 < pbar - B - B / β) (hE : RuleEqm S β θ bbar (sTarget β pbar η) P b)
    (hPM : ∀ t ω, P t ω ≤ M) (hq : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ)
    (hb0 : ∀ ω, b 0 ω = bbar) (t : ℕ) : P t =ᵐ[S.μ] sTarget β pbar η t := by
  obtain ⟨hsa, hsb, hrec, hpre', hK⟩ := sTarget_props S (pbar := pbar) hβ0 hβ1 hηa hηB
  obtain ⟨hP, hPa, -, hbi, hrate, hflow, hpre, -, htvc⟩ := hE
  exact fr_unique_stochastic_target S hβ0 hβ1 hθ hP hPa hPM hq hsa hpos hsb hrec hpre' hK hrate
    hflow hpre hb0 hbi htvc t

/-- Cochrane (2023), §9.3.2, p. 267: a predetermined target value is adapted. -/
theorem targetValue_adapted {β : ℝ} {Pstar a : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (t : ℕ) :
    StronglyMeasurable[S.𝓕 t] (a t) := by
  have e : a t = fun ω => Pstar t ω + β * a (t + 1) ω := funext (ha t)
  rw [e]
  exact (hPsa t).add ((hapre t).const_mul β)

/-- Cochrane (2023), §9.3.2, p. 267: a predetermined target value is the expected present value of
the target, `∑ⱼ βʲ E_t P*_{t+j} = a_t` a.e. (a genuine `HasSum`). -/
theorem hasSum_E_target {β m Ms K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {Pstar a : ℕ → Ω → ℝ}
    (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ K) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t (Pstar (t + j)) ω) (a t ω) := by
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have ham := targetValue_adapted S hPsa ha hapre t
  have hai : Integrable (a t) S.μ :=
    Integrable.of_bound (ham.mono (S.𝓕.le t)).aestronglyMeasurable K
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact haK t ω)
  have hpath : ∀ ω, HasSum (fun j => β ^ j * Pstar (t + j) ω) (a t ω) := fun ω => by
    have hk : ∀ k, a t ω = ∑ j ∈ Finset.range k, β ^ j * Pstar (t + j) ω +
        β ^ k * a (t + k) ω := fun k => by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [ih, Finset.sum_range_succ, ha (t + k) ω, show t + (k + 1) = t + k + 1 by ring,
          pow_succ]
        ring
    rw [hasSum_iff_tendsto_nat_of_nonneg fun j =>
      (mul_pos (pow_pos hβ0 j) (hPs0 (t + j) ω)).le]
    have hrem : Tendsto (fun k => β ^ k * a (t + k) ω) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_)
        (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const K)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (haK (t + k) ω) (pow_pos hβ0 k).le
    have := (tendsto_const_nhds (x := a t ω)).sub hrem
    rw [sub_zero] at this
    exact this.congr fun k => by linarith [hk k]
  have hE := S.E_hasSum (f := fun j ω => β ^ j * Pstar (t + j) ω) (c := fun j => β ^ j * Ms)
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right Ms)
    (fun j => (((hPsa (t + j)).mono (S.𝓕.le _)).aestronglyMeasurable.const_mul _))
    (fun j => Eventually.of_forall fun ω => by
      rw [abs_mul, abs_of_pos (pow_pos hβ0 j), abs_of_pos (hPs0 (t + j) ω)]
      exact mul_le_mul_of_nonneg_left (hPs (t + j) ω).2 (pow_pos hβ0 j).le) t
  have hfun : (fun ω => ∑' j, (fun j ω => β ^ j * Pstar (t + j) ω) j ω) = a t :=
    funext fun ω => (hpath ω).tsum_eq
  have hEs : ∀ j, S.E t (fun ω => β ^ j * Pstar (t + j) ω) =ᵐ[S.μ]
      fun ω => β ^ j * S.E t (Pstar (t + j)) ω := fun j => S.E_smul (β ^ j) (Pstar (t + j)) t
  filter_upwards [hE, ae_all_iff.2 hEs] with ω h1 h2
  rw [hfun, S.E_of_stronglyMeasurable ham hai] at h1
  convert h1 using 1
  funext j
  rw [h2 j]

/-- Cochrane (2023), §9.3.2, p. 267 (existence for Theorem FR (d) with a stochastic target and any
initial debt): if the target's present value `a` is predetermined and `c = 1 + (b₀ − b̄)/(θ a₀) >
0`, then `P = c P*` with real debt `b_t = b̄ + θ (c − 1) a_t` is an equilibrium (`RuleEqm`) with
initial debt `b₀`. -/
theorem exists_proportional {β θ bbar b0 m Ms K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hθ : θ ≠ 0)
    {Pstar a : ℕ → Ω → ℝ} (hPsa : StronglyAdapted S.𝓕 Pstar) (hm : 0 < m)
    (hPs : ∀ t ω, m ≤ Pstar t ω ∧ Pstar t ω ≤ Ms)
    (ha : ∀ t ω, a t ω = Pstar t ω + β * a (t + 1) ω)
    (hapre : ∀ t, StronglyMeasurable[S.𝓕 t] (a (t + 1))) (haK : ∀ t ω, |a t ω| ≤ K)
    (hc : ∀ ω, 0 < 1 + (b0 - bbar) / (θ * a 0 ω)) :
    RuleEqm S β θ bbar Pstar (fun t ω => (1 + (b0 - bbar) / (θ * a 0 ω)) * Pstar t ω)
        (fun t ω => bbar + θ * ((b0 - bbar) / (θ * a 0 ω)) * a t ω) ∧
      ∀ ω, bbar + θ * ((b0 - bbar) / (θ * a 0 ω)) * a 0 ω = b0 := by
  have h1β : 0 < 1 - β := by linarith
  have hPs0 : ∀ t ω, 0 < Pstar t ω := fun t ω => hm.trans_le (hPs t ω).1
  have hapos : ∀ t ω, m / (1 - β) ≤ a t ω := fun t ω =>
    targetValue_ge hβ0 hβ1 (fun t ω => (hPs t ω).1) ha haK t ω
  have hmb : 0 < m / (1 - β) := div_pos hm h1β
  have ham := targetValue_adapted S hPsa ha hapre
  set d : Ω → ℝ := fun ω => (b0 - bbar) / (θ * a 0 ω) with hd
  set D := |b0 - bbar| / (|θ| * (m / (1 - β))) with hD
  have hdm : StronglyMeasurable[S.𝓕 0] d :=
    (((ham 0).measurable.const_mul θ).const_div (b0 - bbar)).stronglyMeasurable
  have hdmt : ∀ t, StronglyMeasurable[S.𝓕 t] d := fun t => hdm.mono (S.𝓕.mono (Nat.zero_le t))
  have hdb : ∀ ω, |d ω| ≤ D := fun ω => by
    simp only [hd, hD, abs_div, abs_mul]
    rw [abs_of_pos (hmb.trans_le (hapos 0 ω))]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos (abs_pos.2 hθ) hmb)
      (mul_le_mul_of_nonneg_left (hapos 0 ω) (abs_nonneg θ))
  have hD0 : 0 ≤ D := by positivity
  have hcd : ∀ ω, 1 + (b0 - bbar) / (θ * a 0 ω) = 1 + d ω := fun ω => rfl
  refine ⟨⟨fun t ω => mul_pos (hc ω) (hPs0 t ω), fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_, fun t ω => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩, fun ω => ?_⟩
  · exact (stronglyMeasurable_const.add (hdmt t)).mul (hPsa t)
  · refine Integrable.of_bound ((((stronglyMeasurable_const.add (hdmt t)).mul
      (hPsa t)).mono (S.𝓕.le t)).aestronglyMeasurable) ((1 + D) * Ms)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hPs0 t ω)]
    refine mul_le_mul ((abs_add_le _ _).trans ?_) (hPs t ω).2 (hPs0 t ω).le (by positivity)
    rw [abs_one]
    linarith [hdb ω]
  · refine Integrable.of_bound ((stronglyMeasurable_const.add (((hdmt t).const_mul θ).mul
      (ham t))).mono (S.𝓕.le t)).aestronglyMeasurable (|bbar| + |θ| * D * K)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hdb ω) (abs_nonneg θ)) (haK t ω)
      (abs_nonneg _) (by positivity)
  · refine EventuallyEq.of_eq ?_
    congr 1
    funext ω
    simp only [Pi.div_apply]
    rw [mul_div_mul_left _ _ (hc ω).ne']
  · beta_reduce
    rw [ha t ω]
    ring
  · exact stronglyMeasurable_const.add (((hdmt t).const_mul θ).mul (hapre t))
  · change ∀ᵐ ω ∂S.μ, HasSum (fun j => β ^ j * S.E t (fun ω' => (1 - β) * bbar +
      θ * ((1 + d ω') * Pstar (t + j) ω' - Pstar (t + j) ω')) ω) (bbar + θ * d ω * a t ω)
    have hEj : ∀ j, S.E t (fun ω' => (1 - β) * bbar +
        θ * ((1 + d ω') * Pstar (t + j) ω' - Pstar (t + j) ω')) =ᵐ[S.μ]
        fun ω => (1 - β) * bbar + θ * d ω * S.E t (Pstar (t + j)) ω := fun j => by
      have hPi : Integrable (Pstar (t + j)) S.μ :=
        Integrable.of_bound ((hPsa (t + j)).mono (S.𝓕.le _)).aestronglyMeasurable Ms
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_pos (hPs0 _ ω)]; exact (hPs _ ω).2)
      have e : (fun ω' => (1 - β) * bbar + θ * ((1 + d ω') * Pstar (t + j) ω' -
          Pstar (t + j) ω')) =
          (fun _ => (1 - β) * bbar) + (fun ω' => θ * d ω') * Pstar (t + j) := by
        funext ω'
        simp only [Pi.add_apply, Pi.mul_apply]
        ring
      have hpo := S.E_pullOut ((hdmt t).const_mul θ) (C := |θ| * D)
        (Eventually.of_forall fun ω => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hdb ω) (abs_nonneg θ)) hPi
      have hint : Integrable ((fun ω' => θ * d ω') * Pstar (t + j)) S.μ :=
        hPi.bdd_mul (((hdmt t).const_mul θ).mono (S.𝓕.le t)).aestronglyMeasurable
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_left (hdb ω) (abs_nonneg θ))
      rw [e]
      filter_upwards [S.E_add (integrable_const _) hint t, hpo] with ω e1 e2
      rw [e1, Pi.add_apply, e2, S.E_const, Pi.mul_apply]
    filter_upwards [hasSum_E_target S hβ0 hβ1 hPsa hm hPs ha hapre haK t, ae_all_iff.2 hEj]
      with ω h1 h2
    have := ((hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left ((1 - β) * bbar)).add
      (h1.mul_left (θ * d ω))
    convert this using 1
    · funext j
      rw [h2 j]
      ring
    · field_simp
  · change ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (fun ω => bbar + θ * d ω * a (t + T) ω) ω)
      atTop (𝓝 0)
    have hb : ∀ T, ∀ᵐ ω ∂S.μ, |S.E t (fun ω => bbar + θ * d ω * a (t + T) ω) ω| ≤
        |bbar| + |θ| * D * K := fun T =>
      S.abs_E_le (Eventually.of_forall fun ω => by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hdb ω) (abs_nonneg θ)) (haK _ ω)
          (abs_nonneg _) (by positivity)) t
    filter_upwards [ae_all_iff.2 hb] with ω h
    refine squeeze_zero_norm (fun T => ?_) (by simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (|bbar| + |θ| * D * K))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 T)]
    exact mul_le_mul_of_nonneg_left (h T) (pow_pos hβ0 T).le
  · field_simp [(hmb.trans_le (hapos 0 ω)).ne']
    ring

/-- Cochrane (2023), §9.3.2, p. 267: for a deterministic target the cumulative real-rate factor
telescopes, `∏_{i<k} (P*_{t+i}/P*_{t+i+1})⁻¹ = P*_{t+k}/P*_t ≤ M*/m`. -/
theorem deterministic_deflator {m Ms : ℝ} (hm : 0 < m) (p : ℕ → ℝ)
    (hp : ∀ t, m ≤ p t ∧ p t ≤ Ms) (t k : ℕ) :
    ∀ᵐ ω ∂S.μ, ∏ i ∈ Finset.range k,
      ((fun t (_ : Ω) => p t) (t + i) ω *
        S.E (t + i) (fun ω => 1 / (fun t (_ : Ω) => p t) (t + i + 1) ω) ω)⁻¹ ≤ Ms / m := by
  have hp0 : ∀ t, 0 < p t := fun t => hm.trans_le (hp t).1
  refine Eventually.of_forall fun ω => ?_
  simp only [S.E_const]
  have h : ∀ k, ∏ i ∈ Finset.range k, (p (t + i) * (1 / p (t + i + 1)))⁻¹ = p (t + k) / p t := by
    intro k
    induction k with
    | zero => simp [(hp0 t).ne']
    | succ k ih =>
      rw [Finset.prod_range_succ, ih, show t + (k + 1) = t + k + 1 by ring]
      field_simp [(hp0 (t + k)).ne', (hp0 (t + k + 1)).ne', (hp0 t).ne']
  rw [h k]
  exact div_le_div₀ (hm.le.trans ((hp 0).1.trans (hp 0).2)) (hp _).2 hm (hp t).1

/-- Cochrane (2023), §9.3.2, pp. 266–267 (**Theorem FR (d)** for every deterministic bounded target
and every initial debt): with prices bounded above (and `1/P` integrable) or bounded away from zero
(and `P` integrable), `P_t = (1 + (b₀ − b̄)/(θ ∑ⱼ βʲ p_j)) p_t` a.e.; the core theorem is the case
`p ≡ 1`, `b₀ = b̄`. -/
theorem fr_unique_deterministic {β θ bbar b0 m Ms : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hθ : θ ≠ 0) {P b : ℕ → Ω → ℝ} (p : ℕ → ℝ) (hm : 0 < m) (hp : ∀ t, m ≤ p t ∧ p t ≤ Ms)
    (hP : ∀ t ω, 0 < P t ω) (hPa : StronglyAdapted S.𝓕 P)
    (hcase : ((∃ M, ∀ t ω, P t ω ≤ M) ∧ ∀ t, Integrable (fun ω => 1 / P t ω) S.μ) ∨
      ((∃ mP, 0 < mP ∧ ∀ t ω, mP ≤ P t ω) ∧ ∀ t, Integrable (P t) S.μ))
    (hrate : ∀ t, S.E t (P t / P (t + 1)) =ᵐ[S.μ]
      S.E t ((fun t (_ : Ω) => p t) t / (fun t (_ : Ω) => p t) (t + 1)))
    (hflow : ∀ t ω, b t ω = (1 - β) * bbar + θ * (P t ω - p t) + β * b (t + 1) ω)
    (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (b (t + 1))) (hb0 : ∀ ω, b 0 ω = b0)
    (hbi : ∀ t, Integrable (b t) S.μ)
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun T => β ^ T * S.E t (b (t + T)) ω) atTop (𝓝 0))
    (t : ℕ) : P t =ᵐ[S.μ] fun _ =>
      (1 + (b0 - bbar) / (θ * ∑' j, β ^ j * p j)) * p t := by
  obtain ⟨ha, hapre, haK⟩ := deterministic_target S hβ0 hβ1 p hp hm
  have hPsa : StronglyAdapted S.𝓕 (fun t (_ : Ω) => p t) := fun _ => stronglyMeasurable_const
  rcases hcase with ⟨⟨M, hM⟩, hq⟩ | ⟨⟨mP, hmP, hPmP⟩, hPi⟩
  · simpa using fr_unique_stochastic S hβ0 hβ1 hθ hP hPa hM hq hPsa hm (fun t _ => hp t) ha
      hapre haK hrate hflow hpre hb0 hbi htvc t
  · simpa using fr_unique_stochastic_below S hβ0 hβ1 hθ hPa hmP hPmP hPi hPsa hm
      (fun t _ => hp t) ha hapre haK hrate hflow hpre hb0 hbi htvc
      (deterministic_deflator S hm p hp) t

end Cochrane.AssetsRulesBalanceSheets.FiscalRulesTargetMeasure
