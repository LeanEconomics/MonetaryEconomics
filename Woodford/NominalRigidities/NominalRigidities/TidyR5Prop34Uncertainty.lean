/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Calvo
import NominalRigidities.ExpectationsFiniteTree

/-!
# Proposition 3.4 with `ω̃θ < 0`: uniqueness among all solutions, under uncertainty

Woodford (2003), *Interest and Prices*, Chapter 3, §2.1, Proposition 3.4 (p. 182) and
Appendix B.3 (pp. 659–661).

`Calvo.prop34_pf_unique_of_w_neg` shows that when `ω̃θ < 0` the solution (2.9) is the only
solution of (2.5) and (2.8) — no difference-stationarity restriction needed — but only under
perfect foresight. This module proves the same statement for **every** `ExpectationSystem`.

## Sequential continuity of expectation operators

The only obstacle under uncertainty is passing `E_t` through the infinite sum in (2.8) at `t + 1`
(the step from (2.8) to its recursive form). Without a growth restriction there is no geometric
domination, so the core lemma `ExpectationSystem.E_tsum` does not apply. But the axioms of an
`ExpectationSystem` (linear, monotone, constants preserved, on **all** functions `Ω → ℝ`) already
force a dominated-convergence property:

* `E_tendsto_zero`: if `u_N ≥ 0` and `u_N → 0` pointwise, then `E_t u_N → 0` at every state. The
  proof uses only monotonicity: with `n(ω)` the index after which `u_N(ω) ≤ η` and
  `G(ω) = ∑_{N < n(ω)} u_N(ω)`, one has `u_N ≤ η + n G/(N + 1)` pointwise.
* `E_hasSum`: `E_t` commutes with **every** pointwise convergent series (no domination
  hypothesis).

## Results

* `recursive_reset_price_any`: the recursive form of (2.8) (with the corrected sign, survey error
  E4) for every solution of (2.8), without the difference-stationarity hypothesis of
  `Calvo.recursive_reset_price`; `solution_B14_any`: (B.14) for every predetermined solution.
* `prop34_unique_of_w_neg`: for `ω̃θ < 0`, every predetermined solution of (2.5) and (2.8) with
  initial price level `P0` is (2.9), for every expectation system.
* `prop34_existsUnique_of_w_neg`: existence (under the initial-gap bound of `Calvo.prop34`) and
  uniqueness among **all** predetermined solutions.
* `prop34_unique_of_w_neg_tree`: the instance for every finite event tree
  (`ExpectationsFiniteTree.FiniteTree.toExpectationSystem`), a genuine-uncertainty instance;
  `prop34_unique_of_w_neg_pf` recovers the perfect-foresight statement.

The measure-theoretic counterpart on an infinite probability space (where `E_t` is only defined on
integrable functions and the conclusion fails without an `L¹` condition) is
`TidyR5Prop34Measure`.
-/

namespace Woodford.NominalRigidities.TidyR5Prop34Uncertainty

open Filter Topology Calvo QuadraticRoots

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Sequential continuity of an expectation system -/

/-- Woodford (2003), App. B.3, p. 659 (the step from (2.8) to its recursive form needs `E_t`
to pass through an infinite sum): `E_t` of a nonnegative function sequence converging pointwise
to zero converges to zero at every state. Only linearity, monotonicity and `E_t c = c` are used. -/
theorem E_tendsto_zero {u : ℕ → Ω → ℝ} (hu0 : ∀ N ω, 0 ≤ u N ω)
    (hu : ∀ ω, Tendsto (fun N => u N ω) atTop (𝓝 0)) (t : ℕ) (ω : Ω) :
    Tendsto (fun N => 𝔼.E t (u N) ω) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  have hex : ∀ ω', ∃ n : ℕ, ∀ M, n ≤ M → u M ω' ≤ η := by
    intro ω'
    have h := (hu ω').eventually (gt_mem_nhds hη0)
    obtain ⟨n, hn⟩ := eventually_atTop.mp h
    exact ⟨n, fun M hM => (hn M hM).le⟩
  choose n hn using hex
  set G : Ω → ℝ := fun ω' => ∑ M ∈ Finset.range (n ω'), u M ω' with hG
  set H : Ω → ℝ := fun ω' => (n ω' : ℝ) * G ω' with hH
  have hG0 : ∀ ω', 0 ≤ G ω' := fun ω' => Finset.sum_nonneg fun M _ => hu0 M ω'
  have hH0 : ∀ ω', 0 ≤ H ω' := fun ω' => mul_nonneg (Nat.cast_nonneg _) (hG0 ω')
  have hbound : ∀ N : ℕ, u N ≤ (fun _ => η) + ((N : ℝ) + 1)⁻¹ • H := by
    intro N ω'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    by_cases hc : n ω' ≤ N
    · have := hn ω' N hc
      have : 0 ≤ ((N : ℝ) + 1)⁻¹ * H ω' := mul_nonneg (inv_nonneg.mpr hN1.le) (hH0 ω')
      linarith
    · push Not at hc
      have h1 : u N ω' ≤ G ω' :=
        Finset.single_le_sum (fun M _ => hu0 M ω') (Finset.mem_range.mpr hc)
      have h2 : G ω' ≤ ((N : ℝ) + 1)⁻¹ * H ω' := by
        rw [hH]
        simp only
        rw [← mul_assoc, ← div_eq_inv_mul]
        have hn' : (N : ℝ) + 1 ≤ n ω' := by exact_mod_cast hc
        have : 1 ≤ (n ω' : ℝ) / ((N : ℝ) + 1) := by rw [le_div_iff₀ hN1]; linarith
        nlinarith [hG0 ω']
      linarith
  have hEH0 : 0 ≤ 𝔼.E t H ω := by
    have := 𝔼.mono t (x := fun _ => (0 : ℝ)) (y := H) (fun ω' => hH0 ω') ω
    rwa [𝔼.const] at this
  obtain ⟨N0, hN0⟩ := exists_nat_gt (𝔼.E t H ω / η)
  refine ⟨N0, fun N hN => ?_⟩
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hup : 𝔼.E t (u N) ω ≤ η + ((N : ℝ) + 1)⁻¹ * 𝔼.E t H ω := by
    have := 𝔼.mono t (hbound N) ω
    rwa [map_add, map_smul, 𝔼.const] at this
  have hlow : 0 ≤ 𝔼.E t (u N) ω := by
    have := 𝔼.mono t (x := fun _ => (0 : ℝ)) (y := u N) (fun ω' => hu0 N ω') ω
    rwa [𝔼.const] at this
  have hsmall : ((N : ℝ) + 1)⁻¹ * 𝔼.E t H ω < η := by
    have hNle : (N0 : ℝ) ≤ N := by exact_mod_cast hN
    rw [inv_mul_lt_iff₀ hN1]
    rw [div_lt_iff₀ hη0] at hN0
    nlinarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hlow]
  linarith

/-- Woodford (2003), App. B.3, p. 659: `|E_t x| ≤ E_t |x|` at every state. -/
theorem abs_E_le_E_abs (t : ℕ) (x : Ω → ℝ) (ω : Ω) : |𝔼.E t x ω| ≤ 𝔼.E t (fun ω' => |x ω'|) ω := by
  have h1 := 𝔼.mono t (x := x) (y := fun ω' => |x ω'|) (fun ω' => le_abs_self (x ω')) ω
  have h2 := 𝔼.mono t (x := -x) (y := fun ω' => |x ω'|) (fun ω' => neg_le_abs (x ω')) ω
  rw [map_neg, Pi.neg_apply] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- Woodford (2003), App. B.3, p. 659 (**`E_t` commutes with every pointwise convergent
series**): if `∑_j f_j(ω) = F(ω)` at every state, then `∑_j E_t f_j = E_t F` at every state, with
no domination hypothesis. This is what turns (2.8) into its recursive form without a growth
restriction on the price index. -/
theorem E_hasSum {f : ℕ → Ω → ℝ} {F : Ω → ℝ} (hf : ∀ ω, HasSum (fun j => f j ω) (F ω))
    (t : ℕ) (ω : Ω) : HasSum (fun j => 𝔼.E t (f j) ω) (𝔼.E t F ω) := by
  -- absolute summability of the expectations
  set A : Ω → ℝ := fun ω' => ∑' j, |f j ω'| with hA
  have habs : ∀ ω', Summable (fun j => |f j ω'|) := fun ω' => (hf ω').summable.abs
  have hpart : ∀ N, ∑ j ∈ Finset.range N, |𝔼.E t (f j) ω| ≤ 𝔼.E t A ω := by
    intro N
    have h1 : ∑ j ∈ Finset.range N, |𝔼.E t (f j) ω|
        ≤ ∑ j ∈ Finset.range N, 𝔼.E t (fun ω' => |f j ω'|) ω :=
      Finset.sum_le_sum fun j _ => abs_E_le_E_abs 𝔼 t (f j) ω
    have h2 : ∑ j ∈ Finset.range N, 𝔼.E t (fun ω' => |f j ω'|) ω
        = 𝔼.E t (∑ j ∈ Finset.range N, fun ω' => |f j ω'|) ω := by
      rw [map_sum, Finset.sum_apply]
    have h3 : (∑ j ∈ Finset.range N, fun ω' => |f j ω'|) ≤ A := by
      intro ω'
      rw [Finset.sum_apply]
      exact (habs ω').sum_le_tsum _ fun j _ => abs_nonneg _
    linarith [𝔼.mono t h3 ω]
  have hs : Summable (fun j => 𝔼.E t (f j) ω) := by
    refine Summable.of_abs ?_
    exact summable_of_sum_range_le (fun j => abs_nonneg _) hpart
  -- the partial sums converge to `E_t F`
  set S : ℕ → Ω → ℝ := fun N => ∑ j ∈ Finset.range N, f j with hS
  set u : ℕ → Ω → ℝ := fun N ω' => |F ω' - S N ω'| with hu
  have hu0 : ∀ N ω', 0 ≤ u N ω' := fun N ω' => abs_nonneg _
  have hut : ∀ ω', Tendsto (fun N => u N ω') atTop (𝓝 0) := by
    intro ω'
    have h := (hf ω').tendsto_sum_nat
    have h' : Tendsto (fun N => F ω' - S N ω') atTop (𝓝 (F ω' - F ω')) := by
      refine tendsto_const_nhds.sub ?_
      simpa [hS, Finset.sum_apply] using h
    rw [sub_self] at h'
    simpa [hu] using h'.abs
  have hE := E_tendsto_zero 𝔼 hu0 hut t ω
  have hlim : Tendsto (fun N => ∑ j ∈ Finset.range N, 𝔼.E t (f j) ω) atTop (𝓝 (𝔼.E t F ω)) := by
    have heq : ∀ N, ∑ j ∈ Finset.range N, 𝔼.E t (f j) ω = 𝔼.E t (S N) ω := by
      intro N
      rw [hS, map_sum, Finset.sum_apply]
    have hle : ∀ N, |𝔼.E t (S N) ω - 𝔼.E t F ω| ≤ 𝔼.E t (u N) ω := by
      intro N
      have := abs_E_le_E_abs 𝔼 t (F - S N) ω
      rw [map_sub, Pi.sub_apply, abs_sub_comm] at this
      exact this
    simp_rw [heq]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun N => by rw [Real.norm_eq_abs]; exact hle N) hE
  have := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim
  rw [← this]
  exact hs.hasSum

/-! ### The recursive form of (2.8) and (B.14) without a growth restriction -/

/-- Woodford (2003), App. B.3, p. 659: `log µ + log S_t + ω̃θ log P_t` is known at `t` when
`log S` is adapted and the price index is predetermined. -/
theorem E_costTerm_self {m w : ℝ} {s P : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (t : ℕ) :
    𝔼.E t (costTerm m w s P t) = costTerm m w s P t := by
  have hf : costTerm m w s P t = (fun _ => m) + s t + w • P (t + 1) := by
    funext ω
    simp [costTerm]
  rw [hf, map_add, map_add, 𝔼.const, hsa t, map_smul, hpre t]

/-- Woodford (2003), App. B.3, p. 659 (**the recursive form of (2.8), sign corrected, for every
solution**): if (2.8) holds at every date, `log S` is adapted and the price index predetermined,
then `log p*_t = (1 − αβ)/(1 + ω̃θ)[log µ + log S_t + ω̃θ log P_t] + αβ E_t log p*_{t+1}` — no
difference-stationarity needed (contrast `Calvo.recursive_reset_price`). -/
theorem recursive_reset_price_any {α β w m : ℝ} {s P pstar : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (h28 : Eq28 𝔼 α β w m s P pstar) (t : ℕ) :
    pstar t = ((1 - α * β) / (1 + w)) • costTerm m w s P t + (α * β) • 𝔼.E t (pstar (t + 1)) := by
  set f : ℕ → Ω → ℝ := fun j => (α * β) ^ j • 𝔼.E (t + 1) (costTerm m w s P (t + 1 + j)) with hf
  have hF : pstar (t + 1) = ((1 - α * β) / (1 + w)) • fun ω => ∑' j, f j ω := by
    funext ω
    rw [(h28 (t + 1) ω).2]
    rfl
  have hsumF : ∀ ω, HasSum (fun j => f j ω) (∑' j, f j ω) := fun ω => (h28 (t + 1) ω).1.hasSum
  have hint := fun ω => E_hasSum 𝔼 hsumF t ω
  funext ω
  have hterm : ∀ j, 𝔼.E t (f j) ω = (α * β) ^ j * 𝔼.E t (costTerm m w s P (t + 1 + j)) ω := by
    intro j
    rw [hf]
    simp only
    rw [map_smul, 𝔼.tower (Nat.le_succ t)]
    rfl
  obtain ⟨hs0, hv0⟩ := h28 t ω
  have hEp : 𝔼.E t (pstar (t + 1)) ω
      = (1 - α * β) / (1 + w) * ∑' j, (α * β) ^ j * 𝔼.E t (costTerm m w s P (t + 1 + j)) ω := by
    rw [hF, map_smul, Pi.smul_apply, smul_eq_mul, (hint ω).tsum_eq.symm]
    simp_rw [hterm]
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hEp, hv0,
    hs0.tsum_eq_zero_add]
  have htail : ∑' j, (α * β) ^ (j + 1) * 𝔼.E t (costTerm m w s P (t + (j + 1))) ω
      = α * β * ∑' j, (α * β) ^ j * 𝔼.E t (costTerm m w s P (t + 1 + j)) ω := by
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [show t + (j + 1) = t + 1 + j by omega, pow_succ]
    ring
  rw [htail, pow_zero, one_mul, add_zero, congrFun (E_costTerm_self 𝔼 hsa hpre t) ω]
  ring

/-- Woodford (2003), (B.14), p. 660 (**for every predetermined solution**): every solution of
(2.5) and (2.8) with predetermined price index satisfies
`z_t = λ₂⁻¹ E_t z_{t+1} + (1 − λ₁)(1 − λ₂⁻¹)(log µ + log S_t)`, `z_t = log P_t − λ₁ log P_{t−1}`,
with no difference-stationarity hypothesis (contrast `Calvo.solution_B14`). -/
theorem solution_B14_any {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hw : 0 < 1 + w) {s P pstar : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (h25 : Eq25 α P pstar)
    (h28 : Eq28 𝔼 α β w m s P pstar) (t : ℕ) (ω : Ω) :
    P (t + 1) ω - lam1 β (calvoXi α β w) * P t ω
      = (lam2 β (calvoXi α β w))⁻¹ * (𝔼.E t (P (t + 2)) ω - lam1 β (calvoXi α β w) * P (t + 1) ω)
        + (1 - lam1 β (calvoXi α β w)) * (1 - (lam2 β (calvoXi α β w))⁻¹) * (m + s t ω) := by
  have hr := congrFun (recursive_reset_price_any 𝔼 hsa hpre h28 t) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, costTerm] at hr
  rw [E_pstar_succ 𝔼 hα1 h25 hpre t ω, congrFun (pstar_of_eq25 hα1 h25 t) ω] at hr
  exact (B13_iff_B14 hβ0 (calvoXi_pos hα0 hα1 hβ1 hw) _ _ _ _).mp
    ((recursive_iff_B13 hα0 hα1 hw.ne' _ _ _ _).mp hr)

/-! ### Proposition 3.4 with `ω̃θ < 0`: uniqueness among all solutions -/

omit 𝔼 in
/-- Woodford (2003), Prop. 3.4 and App. B.3, p. 661: when `ω̃θ < 0`, `αβλ₂ ≥ 1` (so the
explosive root is not discounted away by the `(αβ)ʲ` weights of (2.8)). -/
theorem one_le_alpha_beta_lam2 {α β w : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) :
    1 ≤ α * β * lam2 β (calvoXi α β w) := by
  have hξ := calvoXi_pos hα0 hα1 hβ1 hw
  rw [alpha_beta_lam2 hβ0 hξ, one_le_div (lam1_pos hβ0 hξ)]
  by_contra hlt
  push Not at hlt
  have := (alpha_lt_lam1_calvo_iff hα0 hα1 hβ0 hβ1 hw).mp hlt
  linarith

omit 𝔼 in
/-- Woodford (2003), App. B.3, p. 661: for `0 ≤ a < 1`, `aʲ (C + K j) → 0`. -/
theorem tendsto_pow_mul_lin {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (C K : ℝ) :
    Tendsto (fun j : ℕ => a ^ j * (C + K * j)) atTop (𝓝 0) := by
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const C
  have h2 := (tendsto_self_mul_const_pow_of_lt_one ha0 ha1).const_mul K
  have h := h1.add h2
  simp only [zero_mul, mul_zero, add_zero] at h
  refine h.congr fun j => ?_
  ring

/-- Woodford (2003), App. B.3, p. 661: for a difference-stationary `x`, `aʲ E_t x_{t+j} → 0` at
every state when `0 ≤ a < 1`. -/
theorem tendsto_pow_E_of_diffStationary {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {x : ℕ → Ω → ℝ}
    (hx : DiffStationary 𝔼 x) (t : ℕ) (ω : Ω) :
    Tendsto (fun j : ℕ => a ^ j * 𝔼.E t (x (t + j)) ω) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := diffStationary_nonneg 𝔼 hx
  have hb := tendsto_pow_mul_lin ha0 ha1 |x t ω| K
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine squeeze_zero (fun _ => abs_nonneg _) (fun j => ?_) hb
  rw [Function.comp_apply, abs_mul, abs_of_nonneg (pow_nonneg ha0 j)]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ha0 j)
  have := hK t j ω
  have h2 := abs_sub_abs_le_abs_sub (𝔼.E t (x (t + j)) ω) (x t ω)
  linarith

/-- Woodford (2003), **Proposition 3.4 with `ω̃θ < 0`, uniqueness among all solutions, for every
expectation system** (p. 182; App. B.3, pp. 659–661). Let `0 < α < 1`, `0 < β < 1`,
`−1 < ω̃θ < 0`, `log S` adapted with bounded first differences. Every solution
`(log P, log p*)` of (2.5) and (2.8) with predetermined price index and `log P_{−1} = P0` is
(2.9): no difference-stationarity restriction is needed. -/
theorem prop34_unique_of_w_neg {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hsb : BoundedIncr s) {P0 : Ω → ℝ} {P pstar : ℕ → Ω → ℝ} (hP0 : P 0 = P0)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (h25 : Eq25 α P pstar)
    (h28 : Eq28 𝔼 α β w m s P pstar) :
    P = Psol 𝔼 α β w m s P0 ∧ pstar = pstarSol 𝔼 α β w m s P0 := by
  obtain ⟨hξ, hl0, hl1, ha0, -⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  have hs := diffStationary_of_boundedIncr 𝔼 hsa hsb
  obtain ⟨-, hzs, -⟩ := zbar_props 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb
  have hB14 := solution_B14_any 𝔼 hα0 hα1 hβ0 hβ1 hw hsa hpre h25 h28
  have hZ := fun t => congrFun (zbar_rec 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hs t)
  set l1 := lam1 β (calvoXi α β w)
  set l2 := lam2 β (calvoXi α β w)
  set a := l2⁻¹
  set z := zbar 𝔼 α β w m s
  set q := α * β
  have hl2 : 1 < l2 := one_lt_lam2 hβ0 hξ
  have hl2ne : l2 ≠ 0 := by linarith
  have hq0 : 0 ≤ q := (mul_pos hα0 hβ0).le
  have hq1 : q < 1 := by nlinarith
  have hql2 : 1 ≤ q * l2 := one_le_alpha_beta_lam2 hα0 hα1 hβ0 hβ1 hwneg hw
  set d : ℕ → Ω → ℝ := fun t ω => P (t + 1) ω - l1 * P t ω - z t ω with hd_def
  have hd : ∀ t, d t = a • 𝔼.E t (d (t + 1)) := by
    intro t
    have hf : d (t + 1) = P (t + 1 + 1) - l1 • P (t + 1) - z (t + 1) := by
      funext ω; simp [hd_def, smul_eq_mul]
    funext ω
    rw [hf, map_sub, map_sub, map_smul, hpre t]
    have hb := hB14 t ω
    have hz := hZ t ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mcost] at hz ⊢
    simp only [hd_def]
    linear_combination hb - hz
  -- `E_t d_{t+k} = λ₂ᵏ d_t`
  have hEd : ∀ t k ω, 𝔼.E t (d (t + k)) ω = l2 ^ k * d t ω := by
    intro t k ω
    have h := congrFun (𝔼.forward_iterate hd t k) ω
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hl2ne, one_pow, one_mul]
  -- every `d_t` vanishes
  have hd0 : ∀ t ω, d t ω = 0 := by
    intro t ω
    set e : ℕ → ℝ := fun k => 𝔼.E t (P (t + 1 + k)) ω with he
    -- `qᵏ e_k → 0` from the convergence of (2.8) at `t`
    have hcost : Tendsto (fun j : ℕ => q ^ j * 𝔼.E t (costTerm m w s P (t + j)) ω) atTop (𝓝 0) :=
      (h28 t ω).1.tendsto_atTop_zero
    have hsj := tendsto_pow_E_of_diffStationary 𝔼 hq0 hq1 hs t ω
    have hm := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const m
    rw [zero_mul] at hm
    have hcost' : ∀ j, q ^ j * 𝔼.E t (costTerm m w s P (t + j)) ω
        = q ^ j * m + q ^ j * 𝔼.E t (s (t + j)) ω + w * (q ^ j * e j) := by
      intro j
      have hf : costTerm m w s P (t + j) = (fun _ => m) + s (t + j) + w • P (t + 1 + j) := by
        funext ω'
        simp only [costTerm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [show t + j + 1 = t + 1 + j by omega]
      rw [hf, map_add, map_add, 𝔼.const, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he]
      ring
    have hwe : Tendsto (fun j : ℕ => w * (q ^ j * e j)) atTop (𝓝 0) := by
      have h := (hcost.sub hm).sub hsj
      simp only [sub_zero] at h
      refine h.congr fun j => ?_
      rw [hcost' j]
      ring
    have hqe : Tendsto (fun j : ℕ => q ^ j * e j) atTop (𝓝 0) := by
      have h := hwe.const_mul w⁻¹
      rw [mul_zero] at h
      refine h.congr fun j => ?_
      rw [← mul_assoc, inv_mul_cancel₀ hwneg.ne, one_mul]
    -- `qᵏ E_t z_{t+k} → 0`
    have hqz := tendsto_pow_E_of_diffStationary 𝔼 hq0 hq1 hzs t ω
    -- the identity `E_t d_{t+k+1} = e_{k+1} − λ₁ e_k − E_t z_{t+k+1}`
    have hid : ∀ k, (q * l2) ^ (k + 1) * d t ω
        = q ^ (k + 1) * e (k + 1) - q * l1 * (q ^ k * e k)
          - q ^ (k + 1) * 𝔼.E t (z (t + (k + 1))) ω := by
      intro k
      have hdk : d (t + (k + 1)) = P (t + 1 + (k + 1)) - l1 • P (t + 1 + k) - z (t + (k + 1)) := by
        funext ω'
        simp only [hd_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [show t + (k + 1) + 1 = t + 1 + (k + 1) by omega,
          show t + (k + 1) = t + 1 + k by omega]
      have h := hEd t (k + 1) ω
      rw [hdk, map_sub, map_sub, map_smul] at h
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [mul_pow, mul_assoc, ← h]
      simp only [he]
      ring
    have hlim : Tendsto (fun k : ℕ => (q * l2) ^ (k + 1) * d t ω) atTop (𝓝 0) := by
      have h1 := (tendsto_add_atTop_iff_nat 1).mpr hqe
      have h2 := hqe.const_mul (q * l1)
      have h3 := (tendsto_add_atTop_iff_nat 1).mpr hqz
      have h := (h1.sub h2).sub h3
      simp only [mul_zero, sub_zero] at h
      exact h.congr fun k => (hid k).symm
    have hle : ∀ k : ℕ, |d t ω| ≤ |(q * l2) ^ (k + 1) * d t ω| := by
      intro k
      rw [abs_mul, abs_of_nonneg (pow_nonneg (mul_nonneg hq0 (by linarith)) _)]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hql2)
    have h0 : |d t ω| ≤ 0 :=
      ge_of_tendsto' ((continuous_abs.tendsto 0).comp hlim |>.trans (by rw [abs_zero])) hle
    exact abs_nonpos_iff.mp h0
  have hP : P = Psol 𝔼 α β w m s P0 := by
    funext t
    induction t with
    | zero => exact hP0
    | succ t ih =>
      funext ω
      have h := hd0 t ω
      simp only [hd_def] at h
      change P (t + 1) ω = l1 * Psol 𝔼 α β w m s P0 t ω + z t ω
      rw [← ih]
      linarith
  refine ⟨hP, ?_⟩
  funext t ω
  rw [congrFun (pstar_of_eq25 hα1 h25 t) ω, hP]
  rfl

/-- Woodford (2003), **Proposition 3.4 with `ω̃θ < 0`, existence and uniqueness among all
solutions, for every expectation system**: under the hypotheses of `Calvo.prop34` (initial gap
`log P_{−1} − log S_0` bounded) and `−1 < ω̃θ < 0`, (2.9) solves (2.5) and (2.8) with predetermined
price index, and every predetermined solution with the same initial price level is (2.9). -/
theorem prop34_existsUnique_of_w_neg {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ} (hsa : 𝔼.Adapted s)
    (hsb : BoundedIncr s) {P0 : Ω → ℝ} (hP0 : 𝔼.E 0 P0 = P0)
    (hinit : ∃ B, ∀ ω, |P0 ω - s 0 ω| ≤ B) :
    (Psol 𝔼 α β w m s P0 0 = P0 ∧
      (∀ t, 𝔼.E t (Psol 𝔼 α β w m s P0 (t + 1)) = Psol 𝔼 α β w m s P0 (t + 1)) ∧
      Eq25 α (Psol 𝔼 α β w m s P0) (pstarSol 𝔼 α β w m s P0) ∧
      Eq28 𝔼 α β w m s (Psol 𝔼 α β w m s P0) (pstarSol 𝔼 α β w m s P0)) ∧
    ∀ P pstar : ℕ → Ω → ℝ, P 0 = P0 → (∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) →
      Eq25 α P pstar → Eq28 𝔼 α β w m s P pstar →
      P = Psol 𝔼 α β w m s P0 ∧ pstar = pstarSol 𝔼 α β w m s P0 := by
  obtain ⟨⟨h0, hpre, h25, h28, -, -⟩, -⟩ :=
    prop34 𝔼 (m := m) hα0 hα1 hβ0 hβ1 hw hsa hsb hP0 hinit
  exact ⟨⟨h0, hpre, h25, h28⟩, fun P pstar hP0' hpre' h25' h28' =>
    prop34_unique_of_w_neg 𝔼 hα0 hα1 hβ0 hβ1 hwneg hw hsa hsb hP0' hpre' h25' h28'⟩

omit 𝔼 in
/-- Woodford (2003), Prop. 3.4 with `ω̃θ < 0` **on every finite event tree** (genuine
uncertainty, `ExpectationsFiniteTree.FiniteTree.toExpectationSystem`): every predetermined
solution of (2.5) and (2.8) is (2.9). -/
theorem prop34_unique_of_w_neg_tree {Ω : Type*} [Fintype Ω]
    (T : ExpectationsFiniteTree.FiniteTree Ω) {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ}
    (hsa : T.toExpectationSystem.Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    {P pstar : ℕ → Ω → ℝ} (hP0 : P 0 = P0)
    (hpre : ∀ t, T.toExpectationSystem.E t (P (t + 1)) = P (t + 1)) (h25 : Eq25 α P pstar)
    (h28 : Eq28 T.toExpectationSystem α β w m s P pstar) :
    P = Psol T.toExpectationSystem α β w m s P0 ∧
      pstar = pstarSol T.toExpectationSystem α β w m s P0 :=
  prop34_unique_of_w_neg _ hα0 hα1 hβ0 hβ1 hwneg hw hsa hsb hP0 hpre h25 h28

omit 𝔼 in
/-- Woodford (2003), Prop. 3.4 with `ω̃θ < 0` under perfect foresight: the special case
`Calvo.prop34_pf_unique_of_w_neg`, recovered from `prop34_unique_of_w_neg`. -/
theorem prop34_unique_of_w_neg_pf {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s : ℕ → Unit → ℝ} (hsb : BoundedIncr s)
    {P0 : Unit → ℝ} {P pstar : ℕ → Unit → ℝ} (h0 : P 0 = P0) (h25 : Eq25 α P pstar)
    (h28 : Eq28 perfectForesight α β w m s P pstar) :
    P = Psol perfectForesight α β w m s P0 :=
  (prop34_unique_of_w_neg perfectForesight hα0 hα1 hβ0 hβ1 hwneg hw (fun _ => rfl) hsb h0
    (fun _ => rfl) h25 h28).1

end Woodford.NominalRigidities.TidyR5Prop34Uncertainty
