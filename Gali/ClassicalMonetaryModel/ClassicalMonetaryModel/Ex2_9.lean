/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Exercise 2.9: cash and credit goods

Galí (2015), Chapter 2, Exercise 2.9, pp. 50–51. Utility `V(C₁, C₂, N)` (eq. (54)) of a cash
good `C₁`, a credit good `C₂` and hours `N`; both goods cost `P_t`; the budget is
`P_t(C₁ₜ + C₂ₜ) + Q_t B_t + M_t ≤ B_{t−1} + M_{t−1} + W_t N_t + T_t` and the cash-in-advance
constraint `P_t C₁ₜ ≤ M_{t−1} + T_t`. No uncertainty.

**Indexing.** As in Ex. 2.8, `M t`, `B t` are the holdings carried *into* date `t`.
`V` is any function `ℝ × ℝ × ℝ → ℝ`, differentiable at the plan, with partial derivatives
`V₁ = V'(1,0,0)`, `V₂ = V'(0,1,0)`, `V₃ = V'(0,0,1)`.

## (a) First-order conditions (KKT for the single inequality, by hand)

Feasible perturbations of an `Optimal` plan (finite deviations; `optimal_of_tsum_max` links
this to the infinite discounted sum) give:

* `foc_credit_labour` (two-sided): `V₂/P_t = −V₃/W_t`;
* `foc_cash_credit_ineq` (one-sided: only shifting spending *away* from the cash good is
  always feasible; `nonneg_of_left_max`): `V₁ ≥ V₂`, with equality when the CIA is slack
  (`foc_cash_credit_slack`);
* `foc_bonds` (two-sided): `Q_t V₂ₜ/P_t = β V₂,ₜ₊₁/P_{t+1}`;
* `foc_money` (two-sided): `V₂ₜ/P_t = β V₁,ₜ₊₁/P_{t+1}`;
* `kkt`: with `λ_t = V₂ₜ/P_t` (budget) and `μ_t = (V₁ₜ − V₂ₜ)/P_t` (CIA):
  `V₁ = P(λ + μ)`, `V₂ = P λ`, `V₃ = −W λ`, `λ_t Q_t = β λ_{t+1}`,
  `λ_t = β(λ_{t+1} + μ_{t+1})`, `μ_t ≥ 0`, `μ_t (M_t + T_t − P_t C₁ₜ) = 0`.

## (b) The reduced form

With a binding CIA, `C₁ = M/P`, so `U(C, M/P, N) = V(M/P, C − M/P, N)`:
`hasDerivAt_U_m` gives `U_m = V₁ − V₂`, and `U_m_eq_mul_mu`: `U_m = P μ ≥ 0` at an optimum
(`U_m_nonneg`); `U_c = V₂`, `U_n = V₃` (`hasDerivAt_U_c`, `hasDerivAt_U_n`).
-/

namespace Gali.ClassicalMonetaryModel.Ex2_9

open Filter Topology

/-- Galí (2015), Ex. 2.9(a): the chain rule along a curve in `ℝ × ℝ × ℝ`,
`d/ds V(f s, g s, h s) = f' V₁ + g' V₂ + h' V₃`. -/
theorem hasDerivAt_curve3 {V : ℝ × ℝ × ℝ → ℝ} {V' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {f g h : ℝ → ℝ}
    {a b c s : ℝ} (hV : HasFDerivAt V V' (f s, g s, h s)) (hf : HasDerivAt f a s)
    (hg : HasDerivAt g b s) (hh : HasDerivAt h c s) :
    HasDerivAt (fun x => V (f x, g x, h x))
      (a * V' (1, 0, 0) + b * V' (0, 1, 0) + c * V' (0, 0, 1)) s := by
  have hd := hV.comp_hasDerivAt (f := fun x => (f x, g x, h x)) s (hf.prodMk (hg.prodMk hh))
  have hv : ((a, b, c) : ℝ × ℝ × ℝ) =
      a • ((1, 0, 0) : ℝ × ℝ × ℝ) + b • ((0, 1, 0) : ℝ × ℝ × ℝ) + c • ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul] at hd
  exact hd

/-- **KKT for a single inequality, proved by hand** (Galí (2015), Ex. 2.9(a)): if `f` has
derivative `d` at `0` and `f δ ≤ f 0` for all small `δ ≤ 0`, then `d ≥ 0`. -/
theorem nonneg_of_left_max {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (h : ∀ᶠ δ in 𝓝 0, δ ≤ 0 → f δ ≤ f 0) : 0 ≤ d := by
  by_contra hd
  push Not at hd
  have ho := hf.isLittleO
  have hc : 0 < -d / 2 := by linarith
  have h2 := ho.def hc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (h.and h2)
  set δ := -(ε / 2) with hδ
  have hdist : dist δ 0 < ε := by
    rw [Real.dist_eq, hδ, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith
  obtain ⟨h1, h3⟩ := hball hdist
  have hle := h1 (by rw [hδ]; linarith)
  simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs] at h3
  have habs : |δ| = ε / 2 := by rw [hδ, abs_neg, abs_of_pos (by linarith)]
  rw [habs] at h3
  have := (abs_le.1 h3).1
  rw [hδ] at this
  nlinarith

/-! ### The household problem -/

/-- Galí (2015), Ex. 2.9, p. 51: the budget constraint at date `t`. -/
def Budget (P W Q T C₁ C₂ N M B : ℕ → ℝ) (t : ℕ) : Prop :=
  P t * (C₁ t + C₂ t) + Q t * B (t + 1) + M (t + 1) ≤ B t + M t + W t * N t + T t

/-- Galí (2015), Ex. 2.9, p. 51: the CIA constraint `P_t C₁ₜ ≤ M_{t−1} + T_t`. -/
def CIA (P T C₁ M : ℕ → ℝ) (t : ℕ) : Prop := P t * C₁ t ≤ M t + T t

/-- Galí (2015), Ex. 2.9, p. 51: a feasible plan. -/
def Feasible (P W Q T C₁ C₂ N M B : ℕ → ℝ) : Prop :=
  ∀ t, Budget P W Q T C₁ C₂ N M B t ∧ CIA P T C₁ M t ∧ 0 ≤ C₁ t ∧ 0 ≤ C₂ t ∧ 0 ≤ N t

/-- Galí (2015), Ex. 2.9, eq. (54), p. 50: optimality against all feasible finite deviations
with the same initial holdings. -/
def Optimal (β : ℝ) (V : ℝ × ℝ × ℝ → ℝ) (P W Q T C₁ C₂ N M B : ℕ → ℝ) : Prop :=
  Feasible P W Q T C₁ C₂ N M B ∧
    ∀ (C₁' C₂' N' M' B' : ℕ → ℝ) (T₀ : ℕ), Feasible P W Q T C₁' C₂' N' M' B' →
      M' 0 = M 0 → B' 0 = B 0 →
      (∀ s, T₀ ≤ s → C₁' s = C₁ s ∧ C₂' s = C₂ s ∧ N' s = N s ∧ M' s = M s ∧ B' s = B s) →
      ∑ s ∈ Finset.range T₀, β ^ s * V (C₁' s, C₂' s, N' s) ≤
        ∑ s ∈ Finset.range T₀, β ^ s * V (C₁ s, C₂ s, N s)

variable {β : ℝ} {V : ℝ × ℝ × ℝ → ℝ} {P W Q T C₁ C₂ N M B : ℕ → ℝ}

/-- Galí (2015), Ex. 2.9 (**infinite horizon**): a feasible plan maximising the summable
discounted sum `∑' βᵗ V_t` among feasible plans with the same initial holdings is `Optimal`. -/
theorem optimal_of_tsum_max (hf : Feasible P W Q T C₁ C₂ N M B)
    (hs : Summable fun s => β ^ s * V (C₁ s, C₂ s, N s))
    (hmax : ∀ C₁' C₂' N' M' B' : ℕ → ℝ, Feasible P W Q T C₁' C₂' N' M' B' → M' 0 = M 0 →
      B' 0 = B 0 → Summable (fun s => β ^ s * V (C₁' s, C₂' s, N' s)) →
      ∑' s, β ^ s * V (C₁' s, C₂' s, N' s) ≤ ∑' s, β ^ s * V (C₁ s, C₂ s, N s)) :
    Optimal β V P W Q T C₁ C₂ N M B := by
  refine ⟨hf, fun C₁' C₂' N' M' B' T₀ hf' hM hB hagree => ?_⟩
  have htail : (fun s => β ^ (s + T₀) * V (C₁' (s + T₀), C₂' (s + T₀), N' (s + T₀))) =
      fun s => β ^ (s + T₀) * V (C₁ (s + T₀), C₂ (s + T₀), N (s + T₀)) := by
    funext s
    obtain ⟨h1, h2, h3, -⟩ := hagree (s + T₀) (by omega)
    rw [h1, h2, h3]
  have hs' : Summable fun s => β ^ s * V (C₁' s, C₂' s, N' s) := by
    rw [← summable_nat_add_iff T₀, htail]
    exact (summable_nat_add_iff T₀).2 hs
  have h := hmax C₁' C₂' N' M' B' hf' hM hB hs'
  rw [← hs'.sum_add_tsum_nat_add T₀, ← hs.sum_add_tsum_nat_add T₀] at h
  have he : ∑' s, β ^ (s + T₀) * V (C₁' (s + T₀), C₂' (s + T₀), N' (s + T₀)) =
      ∑' s, β ^ (s + T₀) * V (C₁ (s + T₀), C₂ (s + T₀), N (s + T₀)) := by rw [htail]
  linarith

/-- Galí (2015), Ex. 2.9(a): a feasible deviation at dates `t, t+1` (holdings changed only
for `t+1`) does not raise utility. -/
theorem gain_nonpos (hopt : Optimal β V P W Q T C₁ C₂ N M B) {C₁' C₂' N' M' B' : ℕ → ℝ}
    (t : ℕ) (hf : Feasible P W Q T C₁' C₂' N' M' B')
    (hC : ∀ s, s ≠ t → s ≠ t + 1 → C₁' s = C₁ s ∧ C₂' s = C₂ s ∧ N' s = N s)
    (hMB : ∀ s, s ≠ t + 1 → M' s = M s ∧ B' s = B s) :
    β ^ t * (V (C₁' t, C₂' t, N' t) - V (C₁ t, C₂ t, N t)) +
      β ^ (t + 1) * (V (C₁' (t + 1), C₂' (t + 1), N' (t + 1)) -
        V (C₁ (t + 1), C₂ (t + 1), N (t + 1))) ≤ 0 := by
  have h := hopt.2 C₁' C₂' N' M' B' (t + 1 + 1) hf (hMB 0 (by omega)).1 (hMB 0 (by omega)).2
    (fun s hs => ⟨(hC s (by omega) (by omega)).1, (hC s (by omega) (by omega)).2.1,
      (hC s (by omega) (by omega)).2.2, (hMB s (by omega)).1, (hMB s (by omega)).2⟩)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
    Finset.sum_range_succ (n := t)] at h
  have hsame : ∑ s ∈ Finset.range t, β ^ s * V (C₁' s, C₂' s, N' s) =
      ∑ s ∈ Finset.range t, β ^ s * V (C₁ s, C₂ s, N s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    obtain ⟨h1, h2, h3⟩ := hC s (by omega) (by omega)
    rw [h1, h2, h3]
  linarith

variable {V' : ℕ → ℝ × ℝ × ℝ →L[ℝ] ℝ}

/-- Galí (2015), Ex. 2.9(a), p. 51 (**two-sided**): more credit good financed by more work,
`P dC₂ = W dN`: `V₂/P_t = −V₃/W_t`. -/
theorem foc_credit_labour (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₂ : ∀ t, 0 < C₂ t)
    (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hW : ∀ t, 0 < W t) (t : ℕ) :
    V' t (0, 1, 0) / P t = -V' t (0, 0, 1) / W t := by
  set f : ℝ → ℝ := fun δ => β ^ t * (V (C₁ t, C₂ t + δ, N t + P t * δ / W t) -
    V (C₁ t, C₂ t, N t)) with hfdef
  have hloc : IsLocalMax f 0 := by
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), -C₂ t < δ := eventually_gt_nhds (by linarith [hC₂ t])
    have hc : Continuous fun δ : ℝ => N t + P t * δ / W t := by fun_prop
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < N t + P t * δ / W t :=
      (hc.tendsto 0).eventually_const_lt (by simpa using hN t)
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T C₁ (Function.update C₂ t (C₂ t + δ))
        (Function.update N t (N t + P t * δ / W t)) M B := by
      intro s
      obtain ⟨hb, hc', h1', h2', h3'⟩ := hopt.1 s
      have hPW : W t * (P t * δ / W t) = P t * δ := by field_simp [(hW t).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
        first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [hfdef, add_zero, mul_zero, zero_div, sub_self]
    exact hg
  have hd : HasDerivAt f (β ^ t * (0 * V' t (1, 0, 0) + 1 * V' t (0, 1, 0) +
      P t / W t * V' t (0, 0, 1))) 0 := by
    have hin : HasDerivAt (fun δ : ℝ => N t + P t * δ / W t) (P t / W t) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).const_mul (P t)).div_const (W t)).const_add (N t)
      simpa using this
    have hc2 : HasDerivAt (fun δ : ℝ => C₂ t + δ) 1 0 := (hasDerivAt_id' 0).const_add _
    have := hasDerivAt_curve3 (f := fun _ => C₁ t) (g := fun δ => C₂ t + δ)
      (h := fun δ => N t + P t * δ / W t) (s := 0) (by simpa using hV t)
      (hasDerivAt_const 0 (C₁ t)) hc2 hin
    exact (this.sub_const (V (C₁ t, C₂ t, N t))).const_mul (β ^ t)
  have h0 := (mul_eq_zero.1 (hloc.hasDerivAt_eq_zero hd)).resolve_left (pow_pos hβ t).ne'
  have h1 : V' t (0, 1, 0) = -(P t / W t * V' t (0, 0, 1)) := by linarith
  rw [div_eq_div_iff (hP t).ne' (hW t).ne', h1]
  field_simp [(hW t).ne']

/-- Galí (2015), Ex. 2.9(a): the cash–credit shift `C₁ + δ`, `C₂ − δ` is feasible whenever the
CIA still holds and both goods stay nonnegative. -/
theorem cash_credit_feasible (hopt : Optimal β V P W Q T C₁ C₂ N M B) {t : ℕ} {δ : ℝ}
    (h1 : 0 ≤ C₁ t + δ) (h2 : 0 ≤ C₂ t - δ) (h3 : P t * (C₁ t + δ) ≤ M t + T t) :
    Feasible P W Q T (Function.update C₁ t (C₁ t + δ)) (Function.update C₂ t (C₂ t - δ)) N M
      B := by
  intro s
  obtain ⟨hb, hc', h1', h2', h3'⟩ := hopt.1 s
  simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
    first | omega | nlinarith

/-- Galí (2015), Ex. 2.9(a): the gain of the cash–credit shift has derivative
`β^t (V₁ − V₂)` at `δ = 0`. -/
theorem hasDerivAt_cash_credit (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (t : ℕ) :
    HasDerivAt (fun δ => β ^ t * (V (C₁ t + δ, C₂ t - δ, N t) - V (C₁ t, C₂ t, N t)))
      (β ^ t * (1 * V' t (1, 0, 0) + -1 * V' t (0, 1, 0) + 0 * V' t (0, 0, 1))) 0 := by
  have h1 : HasDerivAt (fun δ : ℝ => C₁ t + δ) 1 0 := (hasDerivAt_id' 0).const_add _
  have h2 : HasDerivAt (fun δ : ℝ => C₂ t - δ) (-1) 0 := (hasDerivAt_id' 0).const_sub _
  have := hasDerivAt_curve3 (f := fun δ => C₁ t + δ) (g := fun δ => C₂ t - δ)
    (h := fun _ => N t) (s := 0) (by simpa using hV t) h1 h2 (hasDerivAt_const 0 (N t))
  exact (this.sub_const (V (C₁ t, C₂ t, N t))).const_mul (β ^ t)

/-- Galí (2015), Ex. 2.9(a), p. 51 (**KKT, the inequality**): shifting spending away from the
cash good is always feasible, so `V₁ ≥ V₂`. -/
theorem foc_cash_credit_ineq (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) (hP : ∀ t, 0 < P t) (t : ℕ) :
    V' t (0, 1, 0) ≤ V' t (1, 0, 0) := by
  have hcia := (hopt.1 t).2.1
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), -C₁ t < δ := eventually_gt_nhds (by linarith [hC₁ t])
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < C₂ t := eventually_lt_nhds (hC₂ t)
  have hleft : ∀ᶠ δ in 𝓝 (0 : ℝ), δ ≤ 0 →
      β ^ t * (V (C₁ t + δ, C₂ t - δ, N t) - V (C₁ t, C₂ t, N t)) ≤
        β ^ t * (V (C₁ t + 0, C₂ t - 0, N t) - V (C₁ t, C₂ t, N t)) := by
    filter_upwards [e1, e2] with δ h1 h2 hδ
    have h3 : P t * (C₁ t + δ) ≤ M t + T t := by
      simp only [CIA] at hcia; nlinarith [hP t]
    have hg := gain_nonpos hopt t (cash_credit_feasible hopt (by linarith) (by linarith) h3)
      (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [add_zero, sub_zero, sub_self, mul_zero]
    exact hg
  have h0 := nonneg_of_left_max (hasDerivAt_cash_credit hV t) hleft
  have h1 : 0 ≤ 1 * V' t (1, 0, 0) + -1 * V' t (0, 1, 0) + 0 * V' t (0, 0, 1) :=
    nonneg_of_mul_nonneg_right h0 (pow_pos hβ t)
  linarith

/-- Galí (2015), Ex. 2.9(a), p. 51 (**complementary slackness**): if the CIA is slack,
`V₁ = V₂`. -/
theorem foc_cash_credit_slack (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) {t : ℕ} (hslack : P t * C₁ t < M t + T t) :
    V' t (1, 0, 0) = V' t (0, 1, 0) := by
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), -C₁ t < δ := eventually_gt_nhds (by linarith [hC₁ t])
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < C₂ t := eventually_lt_nhds (hC₂ t)
  have hc3 : Continuous fun δ : ℝ => P t * (C₁ t + δ) := by fun_prop
  have e3 : ∀ᶠ δ in 𝓝 (0 : ℝ), P t * (C₁ t + δ) < M t + T t :=
    (hc3.tendsto 0).eventually_lt_const (by simpa using hslack)
  have hloc : IsLocalMax (fun δ => β ^ t * (V (C₁ t + δ, C₂ t - δ, N t) -
      V (C₁ t, C₂ t, N t))) 0 := by
    filter_upwards [e1, e2, e3] with δ h1 h2 h3
    have hg := gain_nonpos hopt t (cash_credit_feasible hopt (by linarith) (by linarith) h3.le)
      (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [add_zero, sub_zero, sub_self, mul_zero]
    exact hg
  have h0 := (mul_eq_zero.1 (hloc.hasDerivAt_eq_zero (hasDerivAt_cash_credit hV t))).resolve_left
    (pow_pos hβ t).ne'
  linarith

/-- Galí (2015), Ex. 2.9(a), p. 51 (**two-sided**): bonds, buying `δ` bonds with less credit
good at `t` and spending the proceeds on the credit good at `t+1`:
`Q_t V₂ₜ/P_t = β V₂,ₜ₊₁/P_{t+1}`. -/
theorem foc_bonds (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₂ : ∀ t, 0 < C₂ t)
    (hP : ∀ t, 0 < P t) (t : ℕ) :
    Q t * V' t (0, 1, 0) / P t = β * V' (t + 1) (0, 1, 0) / P (t + 1) := by
  set f : ℝ → ℝ := fun δ => β ^ t * (V (C₁ t, C₂ t - Q t * δ / P t, N t) -
    V (C₁ t, C₂ t, N t)) + β ^ (t + 1) * (V (C₁ (t + 1), C₂ (t + 1) + δ / P (t + 1), N (t + 1)) -
      V (C₁ (t + 1), C₂ (t + 1), N (t + 1))) with hfdef
  have hloc : IsLocalMax f 0 := by
    have hc1 : Continuous fun δ : ℝ => C₂ t - Q t * δ / P t := by fun_prop
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C₂ t - Q t * δ / P t :=
      (hc1.tendsto 0).eventually_const_lt (by simpa using hC₂ t)
    have hc2 : Continuous fun δ : ℝ => C₂ (t + 1) + δ / P (t + 1) := by fun_prop
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C₂ (t + 1) + δ / P (t + 1) :=
      (hc2.tendsto 0).eventually_const_lt (by simpa using hC₂ (t + 1))
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T C₁
        (Function.update (Function.update C₂ t (C₂ t - Q t * δ / P t)) (t + 1)
          (C₂ (t + 1) + δ / P (t + 1))) N M (Function.update B (t + 1) (B (t + 1) + δ)) := by
      intro s
      obtain ⟨hb, hc', h1', h2', h3'⟩ := hopt.1 s
      have hPQ : P t * (Q t * δ / P t) = Q t * δ := by field_simp [(hP t).ne']
      have hP1 : P (t + 1) * (δ / P (t + 1)) = δ := by field_simp [(hP (t + 1)).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
        first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas (fun s h1 h2 => by simp [h1, h2]) (fun s h1 => by
      simp [h1])
    simp only [Function.update_self, Function.update_apply, show t ≠ t + 1 by omega,
      ↓reduceIte] at hg
    simp only [hfdef, add_zero, mul_zero, zero_div, sub_zero, sub_self]
    linarith
  have hd : HasDerivAt f (β ^ t * (0 * V' t (1, 0, 0) + -(Q t / P t) * V' t (0, 1, 0) +
      0 * V' t (0, 0, 1)) + β ^ (t + 1) * (0 * V' (t + 1) (1, 0, 0) +
      1 / P (t + 1) * V' (t + 1) (0, 1, 0) + 0 * V' (t + 1) (0, 0, 1))) 0 := by
    have hg1 : HasDerivAt (fun δ : ℝ => C₂ t - Q t * δ / P t) (-(Q t / P t)) 0 := by
      have := (((hasDerivAt_id' (0 : ℝ)).const_mul (Q t)).div_const (P t)).const_sub (C₂ t)
      simpa using this
    have hg2 : HasDerivAt (fun δ : ℝ => C₂ (t + 1) + δ / P (t + 1)) (1 / P (t + 1)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).div_const (P (t + 1))).const_add (C₂ (t + 1))
      simpa using this
    have d1 := hasDerivAt_curve3 (f := fun _ => C₁ t) (g := fun δ => C₂ t - Q t * δ / P t)
      (h := fun _ => N t) (s := 0) (by simpa using hV t) (hasDerivAt_const 0 (C₁ t)) hg1
      (hasDerivAt_const 0 (N t))
    have d2 := hasDerivAt_curve3 (f := fun _ => C₁ (t + 1))
      (g := fun δ => C₂ (t + 1) + δ / P (t + 1)) (h := fun _ => N (t + 1)) (s := 0)
      (by simpa using hV (t + 1)) (hasDerivAt_const 0 (C₁ (t + 1))) hg2
      (hasDerivAt_const 0 (N (t + 1)))
    exact ((d1.sub_const _).const_mul (β ^ t)).add ((d2.sub_const _).const_mul (β ^ (t + 1)))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h1 : β ^ t * (Q t / P t * V' t (0, 1, 0)) =
      β ^ t * (β * (1 / P (t + 1) * V' (t + 1) (0, 1, 0))) := by linarith
  have h2 := mul_left_cancel₀ hb.ne' h1
  field_simp [(hP t).ne', (hP (t + 1)).ne'] at h2 ⊢
  linarith

/-- Galí (2015), Ex. 2.9(a), p. 51 (**two-sided**): money, holding `δ` more cash (less credit
good at `t`) and buying the cash good at `t+1`: `V₂ₜ/P_t = β V₁,ₜ₊₁/P_{t+1}`. -/
theorem foc_money (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) (hP : ∀ t, 0 < P t) (t : ℕ) :
    V' t (0, 1, 0) / P t = β * V' (t + 1) (1, 0, 0) / P (t + 1) := by
  set f : ℝ → ℝ := fun δ => β ^ t * (V (C₁ t, C₂ t - δ / P t, N t) - V (C₁ t, C₂ t, N t)) +
    β ^ (t + 1) * (V (C₁ (t + 1) + δ / P (t + 1), C₂ (t + 1), N (t + 1)) -
      V (C₁ (t + 1), C₂ (t + 1), N (t + 1))) with hfdef
  have hloc : IsLocalMax f 0 := by
    have hc1 : Continuous fun δ : ℝ => C₂ t - δ / P t := by fun_prop
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C₂ t - δ / P t :=
      (hc1.tendsto 0).eventually_const_lt (by simpa using hC₂ t)
    have hc2 : Continuous fun δ : ℝ => C₁ (t + 1) + δ / P (t + 1) := by fun_prop
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C₁ (t + 1) + δ / P (t + 1) :=
      (hc2.tendsto 0).eventually_const_lt (by simpa using hC₁ (t + 1))
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T (Function.update C₁ (t + 1) (C₁ (t + 1) + δ / P (t + 1)))
        (Function.update C₂ t (C₂ t - δ / P t)) N (Function.update M (t + 1) (M (t + 1) + δ))
        B := by
      intro s
      obtain ⟨hb, hc', h1', h2', h3'⟩ := hopt.1 s
      have hP0 : P t * (δ / P t) = δ := by field_simp [(hP t).ne']
      have hP1 : P (t + 1) * (δ / P (t + 1)) = δ := by field_simp [(hP (t + 1)).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
        first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas (fun s h1 h2 => by simp [h1, h2]) (fun s h1 => by
      simp [h1])
    simp only [Function.update_self, Function.update_apply, show t ≠ t + 1 by omega,
      show t + 1 ≠ t by omega, ↓reduceIte] at hg
    simp only [hfdef, add_zero, zero_div, sub_zero, sub_self, mul_zero]
    linarith
  have hd : HasDerivAt f (β ^ t * (0 * V' t (1, 0, 0) + -(1 / P t) * V' t (0, 1, 0) +
      0 * V' t (0, 0, 1)) + β ^ (t + 1) * (1 / P (t + 1) * V' (t + 1) (1, 0, 0) +
      0 * V' (t + 1) (0, 1, 0) + 0 * V' (t + 1) (0, 0, 1))) 0 := by
    have hg1 : HasDerivAt (fun δ : ℝ => C₂ t - δ / P t) (-(1 / P t)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).div_const (P t)).const_sub (C₂ t)
      simpa using this
    have hg2 : HasDerivAt (fun δ : ℝ => C₁ (t + 1) + δ / P (t + 1)) (1 / P (t + 1)) 0 := by
      have := ((hasDerivAt_id' (0 : ℝ)).div_const (P (t + 1))).const_add (C₁ (t + 1))
      simpa using this
    have d1 := hasDerivAt_curve3 (f := fun _ => C₁ t) (g := fun δ => C₂ t - δ / P t)
      (h := fun _ => N t) (s := 0) (by simpa using hV t) (hasDerivAt_const 0 (C₁ t)) hg1
      (hasDerivAt_const 0 (N t))
    have d2 := hasDerivAt_curve3 (f := fun δ => C₁ (t + 1) + δ / P (t + 1))
      (g := fun _ => C₂ (t + 1)) (h := fun _ => N (t + 1)) (s := 0)
      (by simpa using hV (t + 1)) hg2 (hasDerivAt_const 0 (C₂ (t + 1)))
      (hasDerivAt_const 0 (N (t + 1)))
    exact ((d1.sub_const _).const_mul (β ^ t)).add ((d2.sub_const _).const_mul (β ^ (t + 1)))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h1 : β ^ t * (1 / P t * V' t (0, 1, 0)) =
      β ^ t * (β * (1 / P (t + 1) * V' (t + 1) (1, 0, 0))) := by linarith
  have h2 := mul_left_cancel₀ hb.ne' h1
  field_simp [(hP t).ne', (hP (t + 1)).ne'] at h2 ⊢
  linarith

/-- Galí (2015), Ex. 2.9(a), p. 51 (**KKT multipliers**): with `λ_t = V₂ₜ/P_t` and
`μ_t = (V₁ₜ − V₂ₜ)/P_t`: `V₁ = P(λ + μ)`, `V₂ = Pλ`, `V₃ = −Wλ`, `λ_t Q_t = β λ_{t+1}`,
`λ_t = β(λ_{t+1} + μ_{t+1})`, `μ_t ≥ 0` and `μ_t (M_t + T_t − P_t C₁ₜ) = 0`. -/
theorem kkt (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hW : ∀ t, 0 < W t) :
    ∃ lam mu : ℕ → ℝ, (∀ t, V' t (1, 0, 0) = P t * (lam t + mu t)) ∧
      (∀ t, V' t (0, 1, 0) = P t * lam t) ∧ (∀ t, V' t (0, 0, 1) = -(W t * lam t)) ∧
      (∀ t, lam t * Q t = β * lam (t + 1)) ∧ (∀ t, lam t = β * (lam (t + 1) + mu (t + 1))) ∧
      (∀ t, 0 ≤ mu t) ∧ (∀ t, mu t * (M t + T t - P t * C₁ t) = 0) := by
  refine ⟨fun t => V' t (0, 1, 0) / P t, fun t => (V' t (1, 0, 0) - V' t (0, 1, 0)) / P t,
    fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · field_simp [(hP t).ne']; ring
  · field_simp [(hP t).ne']
  · have := foc_credit_labour hopt hβ hV hC₂ hN hP hW t
    dsimp only
    rw [this]; field_simp [(hW t).ne']
  · dsimp only
    rw [mul_comm, ← mul_div_assoc, foc_bonds hopt hβ hV hC₂ hP t, mul_div_assoc]
  · dsimp only
    rw [foc_money hopt hβ hV hC₁ hC₂ hP t]
    field_simp [(hP (t + 1)).ne']
    ring
  · exact div_nonneg (by linarith [foc_cash_credit_ineq hopt hβ hV hC₁ hC₂ hP t]) (hP t).le
  · rcases (hopt.1 t).2.1.lt_or_eq with hlt | heq
    · have := foc_cash_credit_slack hopt hβ hV hC₁ hC₂ hlt
      change (V' t (1, 0, 0) - V' t (0, 1, 0)) / P t * (M t + T t - P t * C₁ t) = 0
      rw [this, sub_self, zero_div, zero_mul]
    · change (V' t (1, 0, 0) - V' t (0, 1, 0)) / P t * (M t + T t - P t * C₁ t) = 0
      rw [heq, sub_self, mul_zero]

/-! ### (b) The reduced form -/

/-- Galí (2015), Ex. 2.9(b), p. 51: the reduced-form utility `U(C, m, N) = V(m, C − m, N)`
when the CIA binds (`C₁ = m = M/P`). -/
def reducedU (V : ℝ × ℝ × ℝ → ℝ) (C m N : ℝ) : ℝ := V (m, C - m, N)

/-- Galí (2015), Ex. 2.9(b), p. 51: `U_m = V₁ − V₂` (chain rule). -/
theorem hasDerivAt_U_m {V'' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {C m N : ℝ}
    (hV : HasFDerivAt V V'' (m, C - m, N)) :
    HasDerivAt (fun m' => reducedU V C m' N) (V'' (1, 0, 0) - V'' (0, 1, 0)) m := by
  have := hasDerivAt_curve3 (f := fun x => x) (g := fun x => C - x) (h := fun _ => N) (s := m)
    hV (hasDerivAt_id' m) ((hasDerivAt_id' m).const_sub C) (hasDerivAt_const m N)
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.9(b), p. 51: `U_c = V₂`. -/
theorem hasDerivAt_U_c {V'' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {C m N : ℝ}
    (hV : HasFDerivAt V V'' (m, C - m, N)) :
    HasDerivAt (fun C' => reducedU V C' m N) (V'' (0, 1, 0)) C := by
  have := hasDerivAt_curve3 (f := fun _ => m) (g := fun x => x - m) (h := fun _ => N) (s := C)
    hV (hasDerivAt_const C m) ((hasDerivAt_id' C).sub_const m) (hasDerivAt_const C N)
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.9(b), p. 51: `U_n = V₃`. -/
theorem hasDerivAt_U_n {V'' : ℝ × ℝ × ℝ →L[ℝ] ℝ} {C m N : ℝ}
    (hV : HasFDerivAt V V'' (m, C - m, N)) :
    HasDerivAt (fun N' => reducedU V C m N') (V'' (0, 0, 1)) N := by
  have := hasDerivAt_curve3 (f := fun _ => m) (g := fun _ => C - m) (h := fun x => x) (s := N)
    hV (hasDerivAt_const N m) (hasDerivAt_const N (C - m)) (hasDerivAt_id' N)
  exact this.congr_deriv (by ring)

/-- Galí (2015), Ex. 2.9(b), p. 51: at an optimum `U_m = V₁ − V₂ = P_t μ_t`, with `μ_t` the
CIA multiplier of `kkt`. -/
theorem U_m_eq_mul_mu (hP : ∀ t, 0 < P t) (t : ℕ) :
    V' t (1, 0, 0) - V' t (0, 1, 0) = P t * ((V' t (1, 0, 0) - V' t (0, 1, 0)) / P t) := by
  field_simp [(hP t).ne']

/-- Galí (2015), Ex. 2.9(b), p. 51 (**`U_m ≥ 0`**): at an optimal plan with a binding CIA
(`C₁ₜ = M_t/P_t = m`, `C₂ₜ = C_t − m`), the reduced-form marginal utility of real balances is
`U_m = V₁ − V₂ = P_t μ_t ≥ 0`. -/
theorem U_m_nonneg (hopt : Optimal β V P W Q T C₁ C₂ N M B) (hβ : 0 < β)
    (hV : ∀ t, HasFDerivAt V (V' t) (C₁ t, C₂ t, N t)) (hC₁ : ∀ t, 0 < C₁ t)
    (hC₂ : ∀ t, 0 < C₂ t) (hP : ∀ t, 0 < P t) (t : ℕ) :
    ∃ Um, HasDerivAt (fun m' => reducedU V (C₁ t + C₂ t) m' (N t)) Um (C₁ t) ∧ 0 ≤ Um := by
  refine ⟨V' t (1, 0, 0) - V' t (0, 1, 0), hasDerivAt_U_m (by simpa using hV t), ?_⟩
  linarith [foc_cash_credit_ineq hopt hβ hV hC₁ hC₂ hP t]

end Gali.ClassicalMonetaryModel.Ex2_9
