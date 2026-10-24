/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.IntertemporalBudget
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Household optimality and rational-expectations equilibrium in the cashless economy

Woodford (2003), *Interest and Prices*, Chapter 2, §1.1, pp. 69–74, eqs. (1.14)–(1.24) and
(1.26)–(1.27).

The marginal utility of consumption along the plan is a positive process `lam t = u_c(C_t; ξ_t)`
and `mu t = lam t / P t` is the marginal utility of nominal wealth. The Euler condition (1.16)
(equivalently (1.20) in equilibrium) prices assets by `Q_{t,t+1} = β (λ_{t+1}/λ_t)(P_t/P_{t+1})`.

## Main results

* `reallocate_spending`, `cashless_optimality`: (1.14)/(1.15). Moving money balances into
  consumption leaves spending `P_tC_t + Δ_tM_t` (hence every budget constraint) unchanged and
  raises consumption wherever `M_t > 0` and `i_t > i^m_t`; so an undominated plan has
  `M_t = 0 ∨ i_t = i^m_t` at every date and in every state. `zeroSpread_of_money_supply`:
  with `M^s > 0`, market clearing forces (1.15).
* `fisher_of_euler`, `E_q_of_euler_fisher`: (1.16) with (1.5) gives the Fisher equation
  (1.17)/(1.21), and conversely.
* `E_q_eq_iff_mu`: (1.5) in marginal-utility form `β E_t μ_{t+1} = μ_t/(1 + i_t)`.
* `sdf_of_euler`, `E_sdf_mul_of_euler`: `Q_{t,t+n} = β^n μ_{t+n}/μ_t` and
  `E_t[Q_{t,t+n}Y] = β^n μ_t⁻¹ E_t[μ_{t+n}Y]` (substitution of (1.20)).
* `tvc_iff_1_22`, `spendingSummable_iff_1_23`: (1.18) ⟺ (1.22) and, with `i = i^m`, `C = Y`,
  (1.19) ⟺ (1.23).
* `REE`: the definition of rational-expectations equilibrium (p. 72).
* `indirectU`, `hasDerivAt_indirectU`, `budget_total_demand`, `fisher_1_26_of_euler`:
  government purchases via the indirect utility `ũ(Y; G, ξ) = u(Y − G; ξ)` (1.26)–(1.27).
-/

namespace Woodford.PriceLevelDetermination.Equilibrium

open Filter Topology AssetPricing IntertemporalBudget

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (1.14)–(1.15): optimal money holdings in the cashless economy -/

/-- Woodford (2003), eq. (1.7), p. 67: nominal spending `P_tC_t + Δ_tM_t`. -/
noncomputable def spending (P C M i im : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun s => P s * C s + delta i im s * M s

/-- Woodford (2003), p. 69: a consumption/money plan `(C, M)` is feasible from initial wealth
`W_0` when some adapted wealth plan satisfies every flow constraint (1.7) and borrowing limit
(1.9). -/
def Feasible (q P C M i im Z : ℕ → Ω → ℝ) (W0 : Ω → ℝ) : Prop :=
  ∃ W : ℕ → Ω → ℝ, W 0 = W0 ∧ 𝔼.Adapted W ∧
    FlowConstraint 𝔼 q (spending P C M i im) Z W ∧ BorrowingLimit 𝔼 q Z W

/-- Woodford (2003), pp. 69–70: a feasible plan is undominated when no feasible plan with
nonnegative money gives at least as much consumption in every state at every date unless it gives
exactly the same consumption (any optimum of (1.1) with `u` strictly increasing in `C` and every
state relevant is undominated). -/
def Undominated (q P C M i im Z : ℕ → Ω → ℝ) (W0 : Ω → ℝ) : Prop :=
  Feasible 𝔼 q P C M i im Z W0 ∧
    ∀ C' M' : ℕ → Ω → ℝ, (∀ s ω, 0 ≤ M' s ω) → Feasible 𝔼 q P C' M' i im Z W0 → C ≤ C' →
      C' = C

/-- Woodford (2003), pp. 69–70 (behind (1.14)–(1.15)): converting money balances into
consumption, `C' = C + Δ M/P`, `M' = 0`, leaves spending `P C + Δ M` unchanged (`P ≠ 0`). -/
theorem reallocate_spending {P C M i im : ℕ → Ω → ℝ} (hP0 : ∀ s ω, P s ω ≠ 0) :
    spending P (fun s ω => C s ω + delta i im s ω * M s ω / P s ω) 0 i im =
      spending P C M i im := by
  funext s ω
  simp only [spending, Pi.add_apply, Pi.mul_apply, Pi.zero_apply, mul_zero, add_zero]
  have := hP0 s ω
  field_simp

/-- Woodford (2003), eqs. (1.14)–(1.15), p. 69: in the cashless economy an undominated plan has,
at each date and in each state, either `M_t = 0` or `i_t = i^m_t` (given `P > 0`, `1 + i > 0`,
`M ≥ 0` and (1.11) `i ≥ i^m`). -/
theorem cashless_optimality {q P C M i im Z : ℕ → Ω → ℝ} {W0 : Ω → ℝ}
    (hPpos : ∀ s ω, 0 < P s ω) (hi : ∀ s ω, 0 < 1 + i s ω) (hM0 : ∀ s ω, 0 ≤ M s ω)
    (h111 : ∀ s ω, im s ω ≤ i s ω) (hopt : Undominated 𝔼 q P C M i im Z W0) :
    ∀ t ω, M t ω = 0 ∨ i t ω = im t ω := by
  obtain ⟨⟨W, h0, hW, hflow, hbl⟩, hund⟩ := hopt
  set C' : ℕ → Ω → ℝ := fun s ω => C s ω + delta i im s ω * M s ω / P s ω with hC'
  have hsp := reallocate_spending (C := C) (M := M) (i := i) (im := im)
    (fun s ω => (hPpos s ω).ne')
  have hfeas : Feasible 𝔼 q P C' 0 i im Z W0 := ⟨W, h0, hW, by rwa [hsp], hbl⟩
  have hle : C ≤ C' := fun s ω => by
    simp only [hC']
    have := mul_nonneg ((delta_nonneg_iff (hi s ω)).mpr (h111 s ω)) (hM0 s ω)
    have := div_nonneg this (hPpos s ω).le
    linarith
  have heq := hund C' 0 (fun _ _ => le_rfl) hfeas hle
  intro t ω
  have h := congrFun (congrFun heq t) ω
  simp only [hC', add_eq_left, div_eq_zero_iff, mul_eq_zero] at h
  rcases h with (h | h) | h
  · exact Or.inr ((delta_eq_zero_iff (hi t ω)).mp h)
  · exact Or.inl h
  · exact absurd h (hPpos t ω).ne'

/-- Woodford (2003), p. 71: with a positive money supply `M^s_t > 0` and market clearing
`M_t = M^s_t`, condition (1.14) cannot hold, so (1.15) `i_t = i^m_t` holds at all times. -/
theorem zeroSpread_of_money_supply {M Ms i im : ℕ → Ω → ℝ}
    (hopt : ∀ t ω, M t ω = 0 ∨ i t ω = im t ω) (hclear : M = Ms) (hMs : ∀ t ω, 0 < Ms t ω) :
    ∀ t, i t = im t := by
  intro t
  funext ω
  rcases hopt t ω with h | h
  · rw [hclear] at h
    exact absurd h (hMs t ω).ne'
  · exact h

/-! ### (1.16)–(1.17): the Euler condition and the Fisher equation -/

/-- Woodford (2003), eqs. (1.16), p. 70, and (1.20), p. 71: the stochastic discount factor
equals the intertemporal marginal rate of substitution,
`Q_{t,t+1} = β (λ_{t+1}/λ_t)(P_t/P_{t+1})` with `λ_t = u_c(C_t; ξ_t)`. -/
def EulerSDF (β : ℝ) (lam P q : ℕ → Ω → ℝ) : Prop :=
  ∀ t, q t = fun ω => β * (lam (t + 1) ω / lam t ω) * (P t ω / P (t + 1) ω)

/-- Woodford (2003), eqs. (1.17), p. 70, and (1.21), p. 71: the Fisher equation
`1 + i_t = β⁻¹ {E_t[(λ_{t+1}/λ_t)(P_t/P_{t+1})]}⁻¹`. -/
def FisherEq (β : ℝ) (lam P i : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, 1 + i t ω =
    β⁻¹ * (𝔼.E t (fun ω' => lam (t + 1) ω' / lam t ω' * (P t ω' / P (t + 1) ω')) ω)⁻¹

/-- Woodford (2003), eq. (1.17), p. 70: the Euler condition (1.16) together with the definition
(1.5) of the riskless rate, `1/(1 + i_t) = E_t Q_{t,t+1}`, gives the Fisher equation. -/
theorem fisher_of_euler {β : ℝ} (hβ : 0 < β) {lam P q i : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (h15 : ∀ t, 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹)
    (hi : ∀ t ω, 0 < 1 + i t ω) : FisherEq 𝔼 β lam P i := by
  intro t ω
  have h := congrFun (h15 t) ω
  have hq : q t = β • fun ω' => lam (t + 1) ω' / lam t ω' * (P t ω' / P (t + 1) ω') := by
    rw [heu t]
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hq, ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul] at h
  have hb := hβ.ne'
  have hii := (hi t ω).ne'
  have he : 𝔼.E t (fun ω' => lam (t + 1) ω' / lam t ω' * (P t ω' / P (t + 1) ω')) ω =
      β⁻¹ * (1 + i t ω)⁻¹ := by
    rw [← h]
    field_simp
  rw [he, mul_inv, inv_inv, inv_inv, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]

/-- Woodford (2003), eqs. (1.5), (1.20)–(1.21), pp. 66 and 71: conversely, the Euler condition
and the Fisher equation give (1.5), `E_t Q_{t,t+1} = 1/(1 + i_t)`. -/
theorem E_q_of_euler_fisher {β : ℝ} {lam P q i : ℕ → Ω → ℝ} (heu : EulerSDF β lam P q)
    (hfis : FisherEq 𝔼 β lam P i) : ∀ t, 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹ := by
  intro t
  funext ω
  have hq : q t = β • fun ω' => lam (t + 1) ω' / lam t ω' * (P t ω' / P (t + 1) ω') := by
    rw [heu t]
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfis t ω, hq, ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul, mul_inv, inv_inv,
    inv_inv]

/-! ### The marginal utility of nominal wealth -/

/-- Woodford (2003), p. 638 (A.5): the marginal utility of nominal wealth
`μ_t = u_c(Y_t; ξ_t)/P_t`. -/
noncomputable def mu (lam P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => lam t ω / P t ω

/-- Woodford (2003), eq. (1.20), p. 71: in terms of `μ = λ/P`, `Q_{t,t+1} = β μ_{t+1}/μ_t`. -/
theorem q_eq_mu {β : ℝ} {lam P q : ℕ → Ω → ℝ} (heu : EulerSDF β lam P q)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (t : ℕ) :
    q t = fun ω => β * mu lam P (t + 1) ω / mu lam P t ω := by
  rw [heu t]
  funext ω
  have := (hlam t ω).ne'
  have := (hlam (t + 1) ω).ne'
  have := (hPpos t ω).ne'
  have := (hPpos (t + 1) ω).ne'
  simp only [mu]
  field_simp

/-- Woodford (2003), eq. (1.20), p. 71: `μ_t > 0`. -/
theorem mu_pos {lam P : ℕ → Ω → ℝ} (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω)
    (t : ℕ) (ω : Ω) : 0 < mu lam P t ω :=
  div_pos (hlam t ω) (hPpos t ω)

/-- Woodford (2003), eqs. (1.5) and (1.20), pp. 66, 71: with `μ_t⁻¹` known at `t`,
`E_t Q_{t,t+1} = β μ_t⁻¹ E_t μ_{t+1}`. -/
theorem E_q_of_euler (hP : 𝔼.PullOut) {β : ℝ} {lam P q : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω)
    {t : ℕ} (hmuinv : 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹) :
    𝔼.E t (q t) = fun ω => β * (mu lam P t ω)⁻¹ * 𝔼.E t (mu lam P (t + 1)) ω := by
  have hq : q t = (fun ω => (mu lam P t ω)⁻¹) * (β • mu lam P (t + 1)) := by
    rw [q_eq_mu heu hlam hPpos t]
    funext ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hq, hP t _ _ hmuinv, ExpectationSystem.E_smul]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (1.21), p. 71, in marginal-utility form (as used in A.5, p. 638):
under (1.20), `E_t Q_{t,t+1} = 1/(1+i_t)` iff `β E_t μ_{t+1} = μ_t/(1+i_t)`. -/
theorem E_q_eq_iff_mu (hP : 𝔼.PullOut) {β : ℝ} {lam P q i : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω)
    {t : ℕ} (hmuinv : 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹) :
    (𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) ↔
      ∀ ω, β * 𝔼.E t (mu lam P (t + 1)) ω = mu lam P t ω * (1 + i t ω)⁻¹ := by
  rw [E_q_of_euler 𝔼 hP heu hlam hPpos hmuinv]
  constructor
  · intro h ω
    have h1 := congrFun h ω
    have hm := (mu_pos hlam hPpos t ω).ne'
    rw [← h1]
    field_simp
  · intro h
    funext ω
    have hm := (mu_pos hlam hPpos t ω).ne'
    rw [mul_assoc, mul_comm (mu lam P t ω)⁻¹, ← mul_assoc, h ω]
    field_simp

/-- Woodford (2003), p. 71 (substituting (1.20) into the discount factors):
`Q_{t,t+n} = β^n μ_{t+n}/μ_t`. -/
theorem sdf_of_euler {β : ℝ} {lam P q : ℕ → Ω → ℝ} (heu : EulerSDF β lam P q)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (t n : ℕ) :
    sdf q t n = fun ω => β ^ n * mu lam P (t + n) ω / mu lam P t ω := by
  induction n with
  | zero =>
    funext ω
    have := (mu_pos hlam hPpos t ω).ne'
    simp [this]
  | succ n ih =>
    rw [sdf_succ, ih, q_eq_mu heu hlam hPpos (t + n)]
    funext ω
    have := (mu_pos hlam hPpos t ω).ne'
    have := (mu_pos hlam hPpos (t + n) ω).ne'
    simp only [Pi.mul_apply, ← add_assoc]
    field_simp
    ring

/-- Woodford (2003), pp. 71–72 (from (1.18)–(1.19) to (1.22)–(1.23)): with `μ_t⁻¹` known at `t`,
`E_t[Q_{t,t+n}Y] = β^n μ_t⁻¹ E_t[μ_{t+n}Y]`. -/
theorem E_sdf_mul_of_euler (hP : 𝔼.PullOut) {β : ℝ} {lam P q : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω)
    {t : ℕ} (hmuinv : 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹)
    (n : ℕ) (Y : Ω → ℝ) :
    𝔼.E t (sdf q t n * Y) =
      fun ω => β ^ n * (mu lam P t ω)⁻¹ * 𝔼.E t (mu lam P (t + n) * Y) ω := by
  have h : sdf q t n * Y = (fun ω => (mu lam P t ω)⁻¹) * (β ^ n • (mu lam P (t + n) * Y)) := by
    rw [sdf_of_euler heu hlam hPpos t n]
    funext ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, hP t _ _ hmuinv, ExpectationSystem.E_smul]
  funext ω
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eqs. (1.18) and (1.22), pp. 70–72: under (1.20), the household
transversality condition `lim_T E_t[Q_{t,T}W_T] = 0` holds iff
`lim_T β^T E_t[u_c(Y_T; ξ_T)W_T/P_T] = 0`. -/
theorem tvc_iff_1_22 (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {lam P q W : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω)
    {t : ℕ} (hmuinv : 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹) :
    TVC 𝔼 q W t ↔ ∀ ω, Tendsto
      (fun T => β ^ T * 𝔼.E t (fun ω' => lam T ω' * W T ω' / P T ω') ω) atTop (𝓝 0) := by
  have hform : ∀ T, (fun ω' => lam T ω' * W T ω' / P T ω') = mu lam P T * W T := by
    intro T
    funext ω'
    simp only [mu, Pi.mul_apply]
    ring
  refine forall_congr' fun ω => ?_
  set c : ℝ := β ^ t * mu lam P t ω with hc
  have hc0 : 0 < c := mul_pos (pow_pos hβ t) (mu_pos hlam hPpos t ω)
  have hrel : ∀ N, β ^ (N + t) * 𝔼.E t (fun ω' => lam (N + t) ω' * W (N + t) ω' /
      P (N + t) ω') ω = c * 𝔼.E t (sdf q t N * W (t + N)) ω := by
    intro N
    rw [E_sdf_mul_of_euler 𝔼 hP heu hlam hPpos hmuinv, hform, add_comm N t]
    have := (mu_pos hlam hPpos t ω).ne'
    simp only [hc, pow_add]
    field_simp
  conv_rhs => rw [← tendsto_add_atTop_iff_nat t]
  show Tendsto (fun N => 𝔼.E t (sdf q t N * W (t + N)) ω) atTop (𝓝 0) ↔
    Tendsto (fun n => β ^ (n + t) * 𝔼.E t (fun ω' => lam (n + t) ω' * W (n + t) ω' /
      P (n + t) ω') ω) atTop (𝓝 0)
  rw [funext hrel]
  constructor
  · intro h
    simpa using h.const_mul c
  · intro h
    have := h.const_mul c⁻¹
    simp only [mul_zero, ← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul] at this
    exact this

/-- Woodford (2003), eqs. (1.19) and (1.23), pp. 70–72: under (1.20), with `i = i^m` (so
`Δ = 0`) and `C = Y`, the spending series `∑_n E_t[Q_{t,t+n}P_{t+n}Y_{t+n}]` converges iff
`∑_n β^{t+n} E_t[u_c(Y_{t+n}; ξ_{t+n})Y_{t+n}]` does. -/
theorem spendingSummable_iff_1_23 (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β)
    {lam P q Y : ℕ → Ω → ℝ} (heu : EulerSDF β lam P q) (hlam : ∀ t ω, 0 < lam t ω)
    (hPpos : ∀ t ω, 0 < P t ω) {t : ℕ}
    (hmuinv : 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹) (ω : Ω) :
    Summable (fun n => 𝔼.E t (sdf q t n * (P (t + n) * Y (t + n))) ω) ↔
      Summable (fun n => β ^ (t + n) * 𝔼.E t (lam (t + n) * Y (t + n)) ω) := by
  set c : ℝ := β ^ t * mu lam P t ω with hc
  have hc0 : 0 < c := mul_pos (pow_pos hβ t) (mu_pos hlam hPpos t ω)
  have hrel : ∀ n, β ^ (t + n) * 𝔼.E t (lam (t + n) * Y (t + n)) ω =
      c * 𝔼.E t (sdf q t n * (P (t + n) * Y (t + n))) ω := by
    intro n
    rw [E_sdf_mul_of_euler 𝔼 hP heu hlam hPpos hmuinv]
    have hform : mu lam P (t + n) * (P (t + n) * Y (t + n)) = lam (t + n) * Y (t + n) := by
      funext ω'
      have := (hPpos (t + n) ω').ne'
      simp only [mu, Pi.mul_apply]
      field_simp
    rw [hform]
    have := (mu_pos hlam hPpos t ω).ne'
    simp only [hc, pow_add]
    field_simp
  simp_rw [hrel]
  exact (summable_mul_left_iff hc0.ne').symm

/-! ### Rational-expectations equilibrium (p. 72) -/

variable (β : ℝ) (lam P i im Ws D Y : ℕ → Ω → ℝ)

/-- Woodford (2003), eq. (1.22), p. 72: `lim_T β^T E_t[u_c(Y_T; ξ_T)W^s_T/P_T] = 0`. -/
def TVCWealth : Prop :=
  ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (fun ω' => lam T ω' * Ws T ω' / P T ω') ω) atTop (𝓝 0)

/-- Woodford (2003), eq. (1.23), p. 72: `∑_{T ≥ t} β^T E_t[u_c(Y_T; ξ_T)Y_T] < ∞`. -/
def FiniteValue : Prop :=
  ∀ t ω, Summable fun n => β ^ (t + n) * 𝔼.E t (lam (t + n) * Y (t + n)) ω

/-- Woodford (2003), eq. (1.24), p. 72: `lim_T β^T E_t[u_c(Y_T; ξ_T)D_T/P_T] = 0`. -/
def TVCDebt : Prop :=
  ∀ t ω, Tendsto (fun T => β ^ T * 𝔼.E t (fun ω' => lam T ω' * D T ω' / P T ω') ω) atTop (𝓝 0)

/-- Woodford (2003), Definition, p. 72: a rational-expectations equilibrium of the cashless
economy is a positive price level `P` and interest rate `i` satisfying (1.15) and (1.21)–(1.24)
at all dates, given the exogenous `{Y_t, ξ_t}` (through `λ_t = u_c(Y_t; ξ_t) > 0`) and the
policy variables `{i^m_t, W^s_t, D_t}`. -/
structure REE where
  /-- The price level is positive. -/
  pricePos : ∀ t ω, 0 < P t ω
  /-- (1.15): `i_t = i^m_t`. -/
  zeroSpread : ∀ t, i t = im t
  /-- (1.21): the Fisher equation. -/
  fisher : FisherEq 𝔼 β lam P i
  /-- (1.22): the transversality condition on wealth. -/
  tvcWealth : TVCWealth 𝔼 β lam P Ws
  /-- (1.23): the present value of output is finite. -/
  finiteValue : FiniteValue 𝔼 β lam Y
  /-- (1.24): the transversality condition on total government liabilities. -/
  tvcDebt : TVCDebt 𝔼 β lam P D

/-! ### Government purchases (1.26)–(1.27) -/

/-- Woodford (2003), eq. (1.27), p. 73: the indirect utility of total demand,
`ũ(Y; G, ξ) ≡ u(Y − G; ξ)`. -/
def indirectU {S : Type*} (u : ℝ → S → ℝ) (Y : ℝ) (Gξ : ℝ × S) : ℝ := u (Y - Gξ.1) Gξ.2

/-- Woodford (2003), p. 73: the marginal indirect utility of total demand is
`ũ_Y(Y; G, ξ) = u_c(Y − G; ξ)`. -/
theorem hasDerivAt_indirectU {S : Type*} {u : ℝ → S → ℝ} {uc : ℝ → S → ℝ} {Y G : ℝ} {ξ : S}
    (hu : HasDerivAt (fun c => u c ξ) (uc (Y - G) ξ) (Y - G)) :
    HasDerivAt (fun Y' => indirectU u Y' (G, ξ)) (uc (Y - G) ξ) Y := by
  have h := hu.comp Y ((hasDerivAt_id Y).sub_const G)
  simpa [indirectU, Function.comp_def] using h

/-- Woodford (2003), p. 74: treating `C + G` as total demand and `T − PG` as the primary
surplus leaves the budget unchanged: `[P(C+G) + ΔM] − [PY − (T − PG)] = [PC + ΔM] − [PY − T]`. -/
theorem budget_total_demand (P C G M Y Tx d : ℝ) :
    (P * (C + G) + d * M) - (P * Y - (Tx - P * G)) = (P * C + d * M) - (P * Y - Tx) := by
  ring

/-- Woodford (2003), eq. (1.26), p. 73: with government purchases and market clearing
`C_t = Y_t − G_t`, the Euler condition with `λ_t = u_c(Y_t − G_t; ξ_t)` and (1.5) give
`1 + i_t = β⁻¹ {E_t[u_c(Y_{t+1} − G_{t+1}; ξ_{t+1}) P_t/(u_c(Y_t − G_t; ξ_t) P_{t+1})]}⁻¹`. -/
theorem fisher_1_26_of_euler {S : Type*} {β : ℝ} (hβ : 0 < β) (uc : ℝ → S → ℝ)
    {ξ : ℕ → Ω → S} {Y G P q i : ℕ → Ω → ℝ}
    (heu : EulerSDF β (fun t ω => uc (Y t ω - G t ω) (ξ t ω)) P q)
    (h15 : ∀ t, 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hi : ∀ t ω, 0 < 1 + i t ω) :
    FisherEq 𝔼 β (fun t ω => uc (Y t ω - G t ω) (ξ t ω)) P i :=
  fisher_of_euler 𝔼 hβ heu h15 hi

end Woodford.PriceLevelDetermination.Equilibrium
