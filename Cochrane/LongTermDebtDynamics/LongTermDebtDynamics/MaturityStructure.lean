/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.ForwardSolution

/-!
# Maturity structure: flow and present-value relations with long-term debt

Cochrane (2023), Chapter 7, pp. 212–213 and 216 (equations (3.2), (3.3) recalled, and (7.1),
(7.2), (7.4), (7.5)).

Flexible prices, a constant real rate `1/β`, risk-neutral bond prices
`Q_t^{(t+j)} = β^j E_t(P_t / P_{t+j})`, and zero-coupon nominal debt of every maturity.

## Indexing

Dates are natural numbers. `D t m` is the face value of debt maturing at date `m` that is
outstanding at the *start* of date `t`, i.e. Cochrane's `B_{t−1}^{(m)}`. So Cochrane's inherited
maturity structure `B_{−1}^{(j)}` is `D 0 j`, his end-of-period-`t` debt `B_t^{(m)}` is
`D (t + 1) m`, and the sales at `t` of maturity-`m` debt are `B_t^{(m)} − B_{t−1}^{(m)} =
D (t + 1) m − D t m` (`sales`). As Cochrane recommends, the primitive price variable is
`x_t = 1/P_t`, so all systems are linear in `x`.

## Main results

* `bondPrice_eq`: `Q_t^{(t+j)} = β^j P_t E_t(1/P_{t+j})` (pull-out of `P_t`).
* `nominalFlow_iff_realFlow`: the nominal flow condition (3.2) is equivalent to the real flow
  condition (7.1)/(7.4) when `P_t > 0`.
* `nominalValue_eq`: the nominal market value of debt is `P_t` times the real value in (7.2).
* `realFlow_iff_recursion`: the flow condition at `t` is equivalent to the one-period
  recursion `V_t = s_t + β E_t V_{t+1}` for the real value of debt `V_t` (the left side of (7.2)).
* `debtValue_iterate`: `V_t = ∑_{k<N} β^k E_t s_{t+k} + β^N E_t V_{t+N}`.
* `presentValue_iff_tvc`: given the flow conditions, the present-value relation (7.2) at `t` is
  equivalent to the transversality condition `β^N E_t V_{t+N} → 0`.
* `flow_tvc_iff_presentValue`: the flow conditions at every date plus the transversality
  conditions are equivalent to the present-value relations (7.2)/(7.5) at every date.
* `presentValue_of_bounded`: with a bounded real value of debt the transversality condition
  holds automatically.
-/

namespace Cochrane.LongTermDebtDynamics.MaturityStructure

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), p. 212: sales at date `t` of debt maturing at `m`,
`B_t^{(m)} − B_{t−1}^{(m)} = D (t + 1) m − D t m`. -/
def sales (D : ℕ → ℕ → Ω → ℝ) (t m : ℕ) : Ω → ℝ := D (t + 1) m - D t m

/-- Cochrane (2023), p. 212: debt is predetermined. The inherited structure `B_{−1}^{(m)} = D 0 m`
is known at date 0 and the end-of-period stock `B_t^{(m)} = D (t + 1) m` is chosen at `t`. -/
def Predetermined (D : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ m, 𝔼.E 0 (D 0 m) = D 0 m) ∧ ∀ t m, 𝔼.E t (D (t + 1) m) = D (t + 1) m

/-- Cochrane (2023), p. 212: debt outstanding at the start of `t` is known at every date
`u ≥ t`. -/
theorem Predetermined.known {D : ℕ → ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) {t u : ℕ}
    (htu : t ≤ u) (m : ℕ) : 𝔼.E u (D t m) = D t m := by
  rcases t with _ | t
  · exact ForwardSolution.E_of_known 𝔼 (Nat.zero_le u) (hD.1 m)
  · exact ForwardSolution.E_of_known 𝔼 (by omega) (hD.2 t m)

/-- Cochrane (2023), p. 212: debt chosen at `t` (the stock `D (t + 1) m`) is known at every
date `u ≥ t`. -/
theorem Predetermined.known_succ {D : ℕ → ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) {t u : ℕ}
    (htu : t ≤ u) (m : ℕ) : 𝔼.E u (D (t + 1) m) = D (t + 1) m :=
  ForwardSolution.E_of_known 𝔼 htu (hD.2 t m)

/-- Cochrane (2023), p. 212: the risk-neutral nominal bond price
`Q_t^{(t+j)} = β^j E_t(P_t / P_{t+j})`, written with `x = 1/P`. -/
noncomputable def bondPrice (β : ℝ) (P x : ℕ → Ω → ℝ) (t j : ℕ) : Ω → ℝ :=
  β ^ j • 𝔼.E t (P t * x (t + j))

/-- Cochrane (2023), p. 212: `Q_t^{(t+j)} = β^j P_t E_t(1/P_{t+j})`, pulling the known `P_t`
out of the expectation. -/
theorem bondPrice_eq (hpo : 𝔼.PullOut) {β : ℝ} {P x : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P)
    (t j : ℕ) : bondPrice 𝔼 β P x t j = β ^ j • (P t * 𝔼.E t (x (t + j))) := by
  rw [bondPrice, hpo t _ _ (hP t)]

/-- Cochrane (2023), eq. (3.2) recalled on p. 212: the nominal flow condition
`B_{t−1}^{(t)} = P_t s_t + ∑_{j≥1} Q_t^{(t+j)} (B_t^{(t+j)} − B_{t−1}^{(t+j)})`, as a genuine
convergent series at every state. -/
def NominalFlow (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (P x s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, HasSum (fun j : ℕ => bondPrice 𝔼 β P x t (j + 1) ω * sales D t (t + (j + 1)) ω)
    (D t t ω - P t ω * s t ω)

/-- Cochrane (2023), eq. (7.1), p. 213 (and (7.4), p. 216): the real flow condition
`B_{t−1}^{(t)}/P_t = s_t + ∑_{j≥1} β^j (B_t^{(t+j)} − B_{t−1}^{(t+j)}) E_t(1/P_{t+j})`. -/
def RealFlow (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
    𝔼.E t (x (t + (j + 1))) ω)) (D t t ω * x t ω - s t ω)

/-- Cochrane (2023), eq. (7.1), p. 213: the nominal flow condition (3.2) divided by `P_t > 0`
is the real flow condition (7.1), and conversely. -/
theorem nominalFlow_iff_realFlow (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hPx : ∀ t ω, P t ω * x t ω = 1)
    (hPpos : ∀ t ω, 0 < P t ω) (t : ℕ) :
    NominalFlow 𝔼 β D P x s t ↔ RealFlow 𝔼 β D x s t := by
  have hterm : ∀ ω j, bondPrice 𝔼 β P x t (j + 1) ω * sales D t (t + (j + 1)) ω =
      P t ω * (β ^ (j + 1) * (sales D t (t + (j + 1)) ω * 𝔼.E t (x (t + (j + 1))) ω)) := by
    intro ω j
    rw [bondPrice_eq 𝔼 hpo hP]
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hval : ∀ ω, D t t ω - P t ω * s t ω = P t ω * (D t t ω * x t ω - s t ω) := by
    intro ω
    have := hPx t ω
    linear_combination (-(D t t ω)) * this
  constructor
  · intro h ω
    have h1 := (h ω).mul_left (P t ω)⁻¹
    simp only [hterm, hval, ← mul_assoc, inv_mul_cancel₀ (hPpos t ω).ne', one_mul] at h1
    convert h1 using 1
    funext j
    ring
  · intro h ω
    have h1 := (h ω).mul_left (P t ω)
    simp only [hterm, hval]
    exact h1

/-- Cochrane (2023), eq. (7.2), p. 213: the terms `β^j B_{t−1}^{(t+j)} E_t(1/P_{t+j})` of the real
value of debt outstanding at the start of `t`. -/
noncomputable def debtTerm (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x : ℕ → Ω → ℝ) (t j : ℕ) (ω : Ω) : ℝ :=
  β ^ j * (D t (t + j) ω * 𝔼.E t (x (t + j)) ω)

/-- Cochrane (2023), eq. (7.2), p. 213: the real value of debt outstanding at the start of `t`,
`V_t = ∑_{j≥0} β^j B_{t−1}^{(t+j)} E_t(1/P_{t+j})`. -/
noncomputable def debtValue (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, debtTerm 𝔼 β D x t j ω

/-- Cochrane (2023), eq. (7.2), p. 213: the terms `β^k E_t s_{t+k}` of the present value of
surpluses. -/
noncomputable def surplusTerm (β : ℝ) (s : ℕ → Ω → ℝ) (t k : ℕ) (ω : Ω) : ℝ :=
  β ^ k * 𝔼.E t (s (t + k)) ω

/-- Cochrane (2023), eq. (7.2), p. 213: the present value of surpluses `E_t ∑_k β^k s_{t+k}`. -/
noncomputable def pvSurplus (β : ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, surplusTerm 𝔼 β s t k ω

/-- Cochrane (2023), eq. (7.2), p. 213 (and (7.5), p. 216): the present-value relation at `t`,
`∑_j β^j B_{t−1}^{(t+j)} E_t(1/P_{t+j}) = E_t ∑_j β^j s_{t+j}`, both sides genuine convergent
series. -/
def PresentValue (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Summable (fun k => surplusTerm 𝔼 β s t k ω) ∧
    HasSum (fun j => debtTerm 𝔼 β D x t j ω) (pvSurplus 𝔼 β s t ω)

/-- Cochrane (2023), eq. (7.2), p. 213: the terms of the real value of debt are dominated by a
summable sequence at date `t` (the hypothesis that lets `E_{t−1}` pass through the series). -/
def DebtDominated (β : ℝ) (D : ℕ → ℕ → Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∃ u : ℕ → ℝ, Summable u ∧ ∀ j ω, |debtTerm 𝔼 β D x t j ω| ≤ u j

/-- Cochrane (2023), eq. (3.3) recalled on p. 212: the nominal market value of debt
`∑_j Q_t^{(t+j)} B_{t−1}^{(t+j)}` equals `P_t` times the real value `V_t` of (7.2). -/
theorem nominalValue_eq (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ} {P x : ℕ → Ω → ℝ}
    (hP : 𝔼.Adapted P) (t : ℕ) (ω : Ω) {v : ℝ} (hv : HasSum (fun j => debtTerm 𝔼 β D x t j ω) v) :
    HasSum (fun j => bondPrice 𝔼 β P x t j ω * D t (t + j) ω) (P t ω * v) := by
  have h := hv.mul_left (P t ω)
  refine h.congr_fun ?_
  intro j
  rw [bondPrice_eq 𝔼 hpo hP, debtTerm]
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), eq. (7.2), p. 213: with `B_t^{(m)}` known at `t`,
`E_t V_{t+1} = ∑_{j≥0} β^j B_t^{(t+1+j)} E_t(1/P_{t+1+j})`, provided the series for `V_{t+1}` is
dominated. -/
theorem hasSum_E_debtValue_succ (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) {t : ℕ} (hdom : DebtDominated 𝔼 β D x (t + 1))
    (ω : Ω) :
    HasSum (fun j => β ^ j * (D (t + 1) (t + 1 + j) ω * 𝔼.E t (x (t + 1 + j)) ω))
      (𝔼.E t (debtValue 𝔼 β D x (t + 1)) ω) := by
  obtain ⟨u, hu, hb⟩ := hdom
  have hE := ForwardSolution.E_tsum_dom 𝔼 hu (f := fun j ω' => debtTerm 𝔼 β D x (t + 1) j ω')
    hb t ω
  have hterm : ∀ j, 𝔼.E t (fun ω' => debtTerm 𝔼 β D x (t + 1) j ω') ω =
      β ^ j * (D (t + 1) (t + 1 + j) ω * 𝔼.E t (x (t + 1 + j)) ω) := by
    intro j
    have hfun : (fun ω' => debtTerm 𝔼 β D x (t + 1) j ω') =
        β ^ j • (D (t + 1) (t + 1 + j) * 𝔼.E (t + 1) (x (t + 1 + j))) := by
      funext ω'
      simp [debtTerm]
    rw [hfun, map_smul, hpo t _ _ (hD.2 t _), 𝔼.tower (Nat.le_succ t)]
    simp
  have hsum : Summable (fun j => 𝔼.E t (fun ω' => debtTerm 𝔼 β D x (t + 1) j ω') ω) :=
    Summable.of_norm_bounded hu (fun j => by
      rw [Real.norm_eq_abs]; exact 𝔼.abs_E_le (hb j) t ω)
  have h2 := hsum.hasSum
  rw [← hE] at h2
  simp only [hterm] at h2
  exact h2

/-- Cochrane (2023), eqs. (7.1)–(7.2), p. 213: the flow condition at `t` is equivalent to the
one-period recursion `V_t = s_t + β E_t V_{t+1}` for the real value of debt, given convergence of
the series for `V_t` and domination of the series for `V_{t+1}`. -/
theorem realFlow_iff_recursion (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hx : 𝔼.Adapted x) {t : ℕ}
    (hsumm : ∀ ω, Summable (fun j => debtTerm 𝔼 β D x t j ω))
    (hdom : DebtDominated 𝔼 β D x (t + 1)) :
    RealFlow 𝔼 β D x s t ↔
      debtValue 𝔼 β D x t = s t + β • 𝔼.E t (debtValue 𝔼 β D x (t + 1)) := by
  -- the flow terms are `β b_j − a_{j+1}`
  have hkey : ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω))
      (β * 𝔼.E t (debtValue 𝔼 β D x (t + 1)) ω - (debtValue 𝔼 β D x t ω - D t t ω * x t ω)) := by
    intro ω
    have hb := (hasSum_E_debtValue_succ 𝔼 hpo hD hdom ω).mul_left β
    have ha := (hasSum_nat_add_iff' 1).mpr (hsumm ω).hasSum
    have ha0 : ∑ i ∈ Finset.range 1, debtTerm 𝔼 β D x t i ω = D t t ω * x t ω := by
      simp [debtTerm, hx t]
    rw [ha0] at ha
    refine (hb.sub ha).congr_fun ?_
    intro j
    simp only [debtTerm, sales, Pi.sub_apply]
    rw [show t + 1 + j = t + (j + 1) by omega, pow_succ]
    ring
  constructor
  · intro h
    funext ω
    have := (h ω).unique (hkey ω)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · intro h ω
    have hω := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hω
    convert hkey ω using 1
    linarith

/-- Cochrane (2023), eq. (7.2), p. 213: the recursion `V_t = s_t + β E_t V_{t+1}` makes `V_t`
known at `t` when surpluses are. -/
theorem debtValue_adapted {β : ℝ} {V s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hrec : ∀ t, V t = s t + β • 𝔼.E t (V (t + 1))) (t : ℕ) : 𝔼.E t (V t) = V t := by
  conv_lhs => rw [hrec t]
  rw [map_add, map_smul, 𝔼.E_E_self, hs t, ← hrec t]

/-- Cochrane (2023), eq. (7.2), p. 213: iterating the recursion,
`V_t = ∑_{k<N} β^k E_t s_{t+k} + β^N E_t V_{t+N}`. -/
theorem debtValue_iterate {β : ℝ} {V s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s)
    (hrec : ∀ t, V t = s t + β • 𝔼.E t (V (t + 1))) (t N : ℕ) :
    V t = ∑ k ∈ Finset.range N, β ^ k • 𝔼.E t (s (t + k)) + β ^ N • 𝔼.E t (V (t + N)) := by
  induction N with
  | zero => simp [debtValue_adapted 𝔼 hs hrec t]
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    have h1 : 𝔼.E t (V (t + N)) = 𝔼.E t (s (t + N)) + β • 𝔼.E t (V (t + (N + 1))) := by
      conv_lhs => rw [hrec (t + N)]
      rw [map_add, map_smul, 𝔼.tower (Nat.le_add_right t N), ← add_assoc]
    rw [h1, smul_add, smul_smul, ← pow_succ]

/-- Cochrane (2023), eq. (7.2), p. 213: with bounded surpluses and `0 ≤ β < 1`, the surplus
series is absolutely convergent. -/
theorem summable_surplusTerm {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : ∀ t ω, |s t ω| ≤ M) (t : ℕ) (ω : Ω) :
    Summable (fun k => surplusTerm 𝔼 β s t k ω) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, surplusTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hs (t + k)) t ω) (pow_nonneg hβ0 k)

/-- Cochrane (2023), eq. (7.2), p. 213: the transversality condition at `t`,
`β^N E_t V_{t+N} → 0`. -/
def Transversality (β : ℝ) (V : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, Tendsto (fun N => β ^ N * 𝔼.E t (V (t + N)) ω) atTop (𝓝 0)

/-- Cochrane (2023), eq. (7.2), p. 213: given the one-period recursion (equivalently the flow
conditions), the present-value relation at `t` holds if and only if the transversality
condition holds. -/
theorem presentValue_iff_tvc {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V s : ℕ → Ω → ℝ}
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hrec : ∀ t, V t = s t + β • 𝔼.E t (V (t + 1))) (t : ℕ) :
    (∀ ω, HasSum (fun k => surplusTerm 𝔼 β s t k ω) (V t ω)) ↔ Transversality 𝔼 β V t := by
  have hpart : ∀ ω N, ∑ k ∈ Finset.range N, surplusTerm 𝔼 β s t k ω =
      V t ω - β ^ N * 𝔼.E t (V (t + N)) ω := by
    intro ω N
    have h := congrFun (debtValue_iterate 𝔼 hs hrec t N) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    simp only [surplusTerm]
    linarith
  constructor
  · intro h ω
    have ht := (h ω).tendsto_sum_nat
    simp only [hpart] at ht
    have := (tendsto_const_nhds (x := V t ω)).sub ht
    simpa using this
  · intro h ω
    rw [(summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω).hasSum_iff_tendsto_nat]
    simp only [hpart]
    simpa using (tendsto_const_nhds (x := V t ω)).sub (h ω)

/-- Cochrane (2023), eq. (7.2), p. 213: the present value of bounded surpluses satisfies the
one-period recursion `PV_t = s_t + β E_t PV_{t+1}`. -/
theorem pvSurplus_recursion {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {s : ℕ → Ω → ℝ}
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    pvSurplus 𝔼 β s t = s t + β • 𝔼.E t (pvSurplus 𝔼 β s (t + 1)) := by
  funext ω
  have hb : ∀ k ω', |surplusTerm 𝔼 β s (t + 1) k ω'| ≤ β ^ k * M := by
    intro k ω'
    rw [surplusTerm, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hsb _) _ ω') (pow_nonneg hβ0 k)
  have hE := 𝔼.E_tsum hβ0 hβ1 hb t ω
  have hterm : ∀ k, 𝔼.E t (surplusTerm 𝔼 β s (t + 1) k) ω = β ^ k * 𝔼.E t (s (t + 1 + k)) ω := by
    intro k
    have hfun : surplusTerm 𝔼 β s (t + 1) k = β ^ k • 𝔼.E (t + 1) (s (t + 1 + k)) := by
      funext ω'; simp [surplusTerm]
    rw [hfun, map_smul, 𝔼.tower (Nat.le_succ t)]
    simp
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ∑' k, surplusTerm 𝔼 β s t k ω =
    s t ω + β * 𝔼.E t (fun ω' => ∑' k, surplusTerm 𝔼 β s (t + 1) k ω') ω
  rw [hE, (summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω).tsum_eq_zero_add]
  simp only [hterm]
  rw [← tsum_mul_left]
  congr 1
  · simp [surplusTerm, hs t]
  · refine tsum_congr fun k => ?_
    simp only [surplusTerm]
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring

/-- Cochrane (2023), eqs. (7.1)–(7.2), p. 213 (and (7.4)–(7.5), p. 216): **flow plus
transversality is equivalent to present value.** With bounded surpluses, predetermined debt,
convergent and dominated debt-value series, the flow conditions (7.1) at every date together with
the transversality conditions are equivalent to the present-value relations (7.2) at every
date. -/
theorem flow_tvc_iff_presentValue (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hx : 𝔼.Adapted x)
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hsumm : ∀ t ω, Summable (fun j => debtTerm 𝔼 β D x t j ω))
    (hdom : ∀ t, DebtDominated 𝔼 β D x t) :
    ((∀ t, RealFlow 𝔼 β D x s t) ∧ ∀ t, Transversality 𝔼 β (debtValue 𝔼 β D x) t) ↔
      ∀ t, PresentValue 𝔼 β D x s t := by
  constructor
  · rintro ⟨hflow, htvc⟩ t ω
    have hrec : ∀ t, debtValue 𝔼 β D x t = s t + β • 𝔼.E t (debtValue 𝔼 β D x (t + 1)) :=
      fun t => (realFlow_iff_recursion 𝔼 hpo hD hx (hsumm t) (hdom (t + 1))).mp (hflow t)
    have hpv := (presentValue_iff_tvc 𝔼 hβ0 hβ1 hs hsb hrec t).mpr (htvc t) ω
    refine ⟨summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω, ?_⟩
    have heq : pvSurplus 𝔼 β s t ω = debtValue 𝔼 β D x t ω := hpv.tsum_eq
    rw [heq]
    exact (hsumm t ω).hasSum
  · intro hpv
    have hV : ∀ t, debtValue 𝔼 β D x t = pvSurplus 𝔼 β s t := by
      intro t
      funext ω
      exact (hpv t ω).2.tsum_eq
    have hrec : ∀ t, debtValue 𝔼 β D x t = s t + β • 𝔼.E t (debtValue 𝔼 β D x (t + 1)) := by
      intro t
      rw [hV t, hV (t + 1)]
      exact pvSurplus_recursion 𝔼 hβ0 hβ1 hs hsb t
    refine ⟨fun t => (realFlow_iff_recursion 𝔼 hpo hD hx (hsumm t) (hdom (t + 1))).mpr
      (hrec t), fun t => ?_⟩
    refine (presentValue_iff_tvc 𝔼 hβ0 hβ1 hs hsb hrec t).mp fun ω => ?_
    rw [hV t]
    exact (summable_surplusTerm 𝔼 hβ0 hβ1 hsb t ω).hasSum

/-- Cochrane (2023), eq. (7.2), p. 213: a bounded real value of debt satisfies the
transversality condition. -/
theorem transversality_of_bounded {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {V : ℕ → Ω → ℝ}
    (hV : ∀ t ω, |V t ω| ≤ K) (t : ℕ) : Transversality 𝔼 β V t := by
  intro ω
  have hlim : Tendsto (fun N : ℕ => β ^ N * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K
  refine squeeze_zero_norm (fun N => ?_) hlim
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hV (t + N)) t ω) (pow_nonneg hβ0 N)

/-- Cochrane (2023), eqs. (7.1)–(7.2), p. 213: with a bounded real value of debt, the flow
conditions at every date imply the present-value relation at every date. -/
theorem presentValue_of_bounded (hpo : 𝔼.PullOut) {β M K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hx : 𝔼.Adapted x)
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hsumm : ∀ t ω, Summable (fun j => debtTerm 𝔼 β D x t j ω))
    (hdom : ∀ t, DebtDominated 𝔼 β D x t) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hV : ∀ t ω, |debtValue 𝔼 β D x t ω| ≤ K) (t : ℕ) : PresentValue 𝔼 β D x s t :=
  (flow_tvc_iff_presentValue 𝔼 hpo hβ0 hβ1 hD hx hs hsb hsumm hdom).mp
    ⟨hflow, transversality_of_bounded 𝔼 hβ0 hβ1 hV⟩ t

end Cochrane.LongTermDebtDynamics.MaturityStructure
