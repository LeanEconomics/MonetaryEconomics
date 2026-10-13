/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exercise 2.8: a cash-in-advance economy

Galí (2015), Chapter 2, Exercise 2.8, p. 50. The household maximises
`∑ βᵗ (log C_t − N_t^{1+φ}/(1+φ))` subject to the budget constraints
`P_t C_t + Q_t B_t + M_t ≤ B_{t−1} + M_{t−1} + W_t N_t + T_t` and the cash-in-advance (CIA)
constraint `P_t C_t ≤ M_{t−1} + T_t`. Output is `Y_t = N_t`, money grows at the constant rate
`γ`, and there is no uncertainty.

**Indexing.** `M t` and `B t` denote the money and bonds carried *into* date `t` (the book's
`M_{t−1}`, `B_{t−1}`), so `Budget` reads `P_t C_t + Q_t B_{t+1} + M_{t+1} ≤ B_t + M_t + W_t N_t
+ T_t` and `CIA` reads `P_t C_t ≤ M_t + T_t`.

## (a) Optimality conditions: a KKT argument for the single inequality

`Optimal` is optimality against every feasible plan that keeps the initial holdings and agrees
with the plan from some date on (finite deviations); `optimal_of_tsum_max` shows that a plan
maximising the infinite discounted sum `∑' βᵗ U_t` is `Optimal`. Feasible perturbations give:

* `foc_labour_money` (labour today financing cash for tomorrow, two-sided):
  `N_t^φ = β W_t/(P_{t+1} C_{t+1})`;
* `foc_labour_bonds` (labour today, bonds, less labour tomorrow, two-sided):
  `Q_t N_t^φ/W_t = β N_{t+1}^φ/W_{t+1}`;
* `foc_cia_ineq` (consumption against labour today; only *decreasing* consumption is feasible
  when the CIA binds, `nonneg_of_left_max` is the one-sided Fermat rule proved by hand):
  `N_t^φ P_t/W_t ≤ 1/C_t`, with equality when the CIA is slack (`foc_cia_slack`).
* `kkt`: the multiplier form. With `λ_t = N_t^φ/W_t` and `μ_t = 1/(P_t C_t) − λ_t`:
  `1/C_t = P_t(λ_t + μ_t)`, `λ_t = β(λ_{t+1} + μ_{t+1})`, `λ_t Q_t = β λ_{t+1}`, `μ_t ≥ 0`,
  `μ_t (M_t + T_t − P_t C_t) = 0`.

**Infinite horizon, no-Ponzi and transversality.** `NoPonzi`, `OptimalNP` (overtaking
optimality against all feasible no-Ponzi plans); `optimal_of_optimalNP`;
`tvc_liminf_of_optimalNP` (necessity of transversality: rolling over debt `d` while working
`d/W_0` less); `budget_binds_of_optimal`; `overtakes_of_foc` (**sufficiency**: the conditions of
(a), a binding budget and the transversality condition imply overtaking optimality against all
no-Ponzi plans with nonnegative money).

## (b) Money growth and output

`IsEquilibrium` collects the household conditions of (a), `W = P`, `C = N` and the money
supply `M^s_t = M^s_0 (1+γ)ᵗ`; `isEquilibrium_of_optimal` shows that an optimal plan with
market clearing is one.

* `Q_le_one`: `Q_t ≤ 1` in every equilibrium; `cia_binds_of_Q_lt_one`: if `Q_t < 1` the CIA
  binds at `t+1`.
* `output_of_binding`: when the CIA binds at `t` and `t+1`, `N_t^{1+φ} = β/(1+γ)`, so
  `Y_t = (β/(1+γ))^{1/(1+φ)}` (`output_eq`), strictly decreasing in `γ`
  (`output_strictAnti`).
* `cia_binds_of_tvc`, `output_eq_of_tvc` (**every equilibrium**): with the transversality
  condition `EqTVC` (implied by household optimality, `eqTVC_of_optimalNP`), `0 < β ≤ 1` and
  `γ ≥ 0`, the CIA binds at every date and `Y_t = (β/(1+γ))^{1/(1+φ)}`.
  `slack_equilibrium_counterexample`: for `β < 1 + γ < 1` there is an equilibrium with a slack
  CIA and transversality, so `1 + γ > β` alone does not suffice.
* `stationary_isEquilibrium`: for `1 + γ ≥ β` this allocation, with `P_{t+1}/P_t = 1 + γ` and
  `Q = β/(1+γ)`, is an equilibrium.

## (c) Optimal inflation

* `stationary_utility_le`: period utility `log N − N^{1+φ}/(1+φ)` is maximised only at `N = 1`.
* `hasSum_welfare`: lifetime welfare of the stationary equilibrium is `U*/(1 − β)`.
* `optimal_inflation`: among `1 + γ ≥ β` welfare is maximised exactly at `1 + γ = β`: gross
  inflation `β`, i.e. net inflation `π = β − 1`, and `Q = 1` (`i = 0`, the Friedman rule).
-/

namespace Gali.ClassicalMonetaryModel.Ex2_8

open Filter Topology

/-- Galí (2015), Ex. 2.8, p. 50: period utility `log C − N^{1+φ}/(1+φ)`. -/
noncomputable def u (φ C N : ℝ) : ℝ := Real.log C - N ^ (1 + φ) / (1 + φ)

/-- Galí (2015), p. 21: `d/dN [N^{1+φ}/(1+φ)] = N^φ`. -/
theorem hasDerivAt_disutil {φ : ℝ} (hφ : 0 ≤ φ) (N : ℝ) :
    HasDerivAt (fun N' : ℝ => N' ^ (1 + φ) / (1 + φ)) (N ^ φ) N := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  refine ((Real.hasDerivAt_rpow_const (x := N) (p := 1 + φ) (Or.inr (by linarith))).div_const
    (1 + φ)).congr_deriv ?_
  rw [show (1 : ℝ) + φ - 1 = φ by ring]
  field_simp

/-- **KKT for a single inequality, proved by hand** (used for Galí (2015), Ex. 2.8(a)): if
`f` has derivative `d` at `0` and `f δ ≤ f 0` for all small `δ ≤ 0` (only decreases are
feasible), then `d ≥ 0`. -/
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

/-- Galí (2015), Ex. 2.8, p. 50: the date-`t` budget constraint (with `M t`, `B t` the holdings
carried into `t`). -/
def Budget (P W Q T C N M B : ℕ → ℝ) (t : ℕ) : Prop :=
  P t * C t + Q t * B (t + 1) + M (t + 1) ≤ B t + M t + W t * N t + T t

/-- Galí (2015), Ex. 2.8, p. 50: the cash-in-advance constraint `P_t C_t ≤ M_{t−1} + T_t`. -/
def CIA (P T C M : ℕ → ℝ) (t : ℕ) : Prop := P t * C t ≤ M t + T t

/-- Galí (2015), Ex. 2.8, p. 50: a feasible plan. -/
def Feasible (P W Q T C N M B : ℕ → ℝ) : Prop :=
  ∀ t, Budget P W Q T C N M B t ∧ CIA P T C M t ∧ 0 < C t ∧ 0 ≤ N t

/-- Galí (2015), Ex. 2.8, p. 50: optimality against every feasible plan with the same initial
holdings that agrees with the plan from some date `T₀` on (finite deviations). -/
def Optimal (β φ : ℝ) (P W Q T C N M B : ℕ → ℝ) : Prop :=
  Feasible P W Q T C N M B ∧
    ∀ (C' N' M' B' : ℕ → ℝ) (T₀ : ℕ), Feasible P W Q T C' N' M' B' → M' 0 = M 0 → B' 0 = B 0 →
      (∀ s, T₀ ≤ s → C' s = C s ∧ N' s = N s ∧ M' s = M s ∧ B' s = B s) →
      ∑ s ∈ Finset.range T₀, β ^ s * u φ (C' s) (N' s) ≤
        ∑ s ∈ Finset.range T₀, β ^ s * u φ (C s) (N s)

variable {β φ : ℝ} {P W Q T C N M B : ℕ → ℝ}

/-- Galí (2015), Ex. 2.8, p. 50 (**infinite horizon**): a feasible plan whose discounted
utility is summable and maximal among all feasible plans with the same initial holdings and
summable utility is `Optimal`. -/
theorem optimal_of_tsum_max (hf : Feasible P W Q T C N M B)
    (hs : Summable fun s => β ^ s * u φ (C s) (N s))
    (hmax : ∀ C' N' M' B' : ℕ → ℝ, Feasible P W Q T C' N' M' B' → M' 0 = M 0 → B' 0 = B 0 →
      Summable (fun s => β ^ s * u φ (C' s) (N' s)) →
      ∑' s, β ^ s * u φ (C' s) (N' s) ≤ ∑' s, β ^ s * u φ (C s) (N s)) :
    Optimal β φ P W Q T C N M B := by
  refine ⟨hf, fun C' N' M' B' T₀ hf' hM hB hagree => ?_⟩
  have htail : (fun s => β ^ (s + T₀) * u φ (C' (s + T₀)) (N' (s + T₀))) =
      fun s => β ^ (s + T₀) * u φ (C (s + T₀)) (N (s + T₀)) := by
    funext s
    rw [(hagree (s + T₀) (by omega)).1, (hagree (s + T₀) (by omega)).2.1]
  have hs' : Summable fun s => β ^ s * u φ (C' s) (N' s) := by
    rw [← summable_nat_add_iff T₀]
    rw [htail]
    exact (summable_nat_add_iff T₀).2 hs
  have h := hmax C' N' M' B' hf' hM hB hs'
  rw [← hs'.sum_add_tsum_nat_add T₀, ← hs.sum_add_tsum_nat_add T₀] at h
  have he : ∑' s, β ^ (s + T₀) * u φ (C' (s + T₀)) (N' (s + T₀)) =
      ∑' s, β ^ (s + T₀) * u φ (C (s + T₀)) (N (s + T₀)) := by rw [htail]
  linarith

/-- Galí (2015), Ex. 2.8(a): a feasible deviation at dates `t, t+1` (holdings changed only
for `t+1`) does not raise utility. -/
theorem gain_nonpos (hopt : Optimal β φ P W Q T C N M B) {C' N' M' B' : ℕ → ℝ} (t : ℕ)
    (hf : Feasible P W Q T C' N' M' B')
    (hCN : ∀ s, s ≠ t → s ≠ t + 1 → C' s = C s ∧ N' s = N s)
    (hMB : ∀ s, s ≠ t + 1 → M' s = M s ∧ B' s = B s) :
    β ^ t * (u φ (C' t) (N' t) - u φ (C t) (N t)) +
      β ^ (t + 1) * (u φ (C' (t + 1)) (N' (t + 1)) - u φ (C (t + 1)) (N (t + 1))) ≤ 0 := by
  have h := hopt.2 C' N' M' B' (t + 1 + 1) hf (hMB 0 (by omega)).1 (hMB 0 (by omega)).2
    (fun s hs => ⟨(hCN s (by omega) (by omega)).1, (hCN s (by omega) (by omega)).2,
      (hMB s (by omega)).1, (hMB s (by omega)).2⟩)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ (n := t + 1),
    Finset.sum_range_succ (n := t)] at h
  have hsame : ∑ s ∈ Finset.range t, β ^ s * u φ (C' s) (N' s) =
      ∑ s ∈ Finset.range t, β ^ s * u φ (C s) (N s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := Finset.mem_range.1 hs
    rw [(hCN s (by omega) (by omega)).1, (hCN s (by omega) (by omega)).2]
  linarith

/-- Galí (2015), Ex. 2.8(a), p. 50 (**two-sided perturbation**): working `δ` more at `t`,
holding the extra wage income as cash, and spending it at `t+1`: `N_t^φ = β W_t/(P_{t+1}
C_{t+1})`. -/
theorem foc_labour_money (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (t : ℕ) :
    N t ^ φ = β * W t / (P (t + 1) * C (t + 1)) := by
  have hC := fun s => (hopt.1 s).2.2.1
  set f : ℝ → ℝ := fun δ => β ^ t * (u φ (C t) (N t + δ) - u φ (C t) (N t)) +
    β ^ (t + 1) * (u φ (C (t + 1) + W t * δ / P (t + 1)) (N (t + 1)) -
      u φ (C (t + 1)) (N (t + 1))) with hfdef
  have hloc : IsLocalMax f 0 := by
    have hc : Continuous fun δ : ℝ => C (t + 1) + W t * δ / P (t + 1) := by fun_prop
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C (t + 1) + W t * δ / P (t + 1) :=
      (hc.tendsto 0).eventually_const_lt (by simpa using hC (t + 1))
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), -N t < δ := eventually_gt_nhds (by linarith [hN t])
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T (Function.update C (t + 1) (C (t + 1) + W t * δ / P (t + 1)))
        (Function.update N t (N t + δ)) (Function.update M (t + 1) (M (t + 1) + W t * δ)) B := by
      intro s
      obtain ⟨hb, hc', hCp, hNp⟩ := hopt.1 s
      have hPW : P (t + 1) * (W t * δ / P (t + 1)) = W t * δ := by
        field_simp [(hP (t + 1)).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;> first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas
      (fun s h1 h2 => by simp [h1, h2])
      (fun s h1 => by simp [h1])
    simp only [Function.update_self, Function.update_apply, show t ≠ t + 1 by omega,
      show t + 1 ≠ t by omega, ↓reduceIte] at hg
    simp only [hfdef, add_zero, mul_zero, zero_div, sub_self, mul_zero]
    linarith
  have hd : HasDerivAt f (β ^ t * (-(N t ^ φ)) +
      β ^ (t + 1) * ((C (t + 1))⁻¹ * (W t / P (t + 1)))) 0 := by
    have hn : HasDerivAt (fun δ => u φ (C t) (N t + δ) - u φ (C t) (N t)) (-(N t ^ φ)) 0 := by
      have := ((hasDerivAt_disutil hφ (N t + 0)).comp 0 ((hasDerivAt_id' 0).const_add (N t)))
      have h2 := (this.const_sub (Real.log (C t))).sub_const (u φ (C t) (N t))
      simp only [add_zero, mul_one] at h2
      exact h2.congr_deriv (by ring)
    have hc : HasDerivAt (fun δ => u φ (C (t + 1) + W t * δ / P (t + 1)) (N (t + 1)) -
        u φ (C (t + 1)) (N (t + 1))) ((C (t + 1))⁻¹ * (W t / P (t + 1))) 0 := by
      have hin : HasDerivAt (fun δ : ℝ => C (t + 1) + W t * δ / P (t + 1)) (W t / P (t + 1)) 0 := by
        have := (((hasDerivAt_id' (0 : ℝ)).const_mul (W t)).div_const (P (t + 1))).const_add
          (C (t + 1))
        simpa using this
      have hl := (Real.hasDerivAt_log (by simpa using (hC (t + 1)).ne')).comp 0 hin
      have h2 := (hl.sub_const (N (t + 1) ^ (1 + φ) / (1 + φ))).sub_const
        (u φ (C (t + 1)) (N (t + 1)))
      simp only [mul_zero, zero_div, add_zero] at h2
      exact h2
    exact (hn.const_mul (β ^ t)).add (hc.const_mul (β ^ (t + 1)))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h1 : β ^ t * N t ^ φ = β ^ t * (β * ((C (t + 1))⁻¹ * (W t / P (t + 1)))) := by linarith
  rw [mul_left_cancel₀ hb.ne' h1]
  field_simp

/-- Galí (2015), Ex. 2.8(a), p. 50 (**two-sided perturbation**): working `δ` more at `t`,
buying bonds with the income and working less at `t+1`:
`Q_t N_t^φ/W_t = β N_{t+1}^φ/W_{t+1}` (`λ_t Q_t = β λ_{t+1}`). -/
theorem foc_labour_bonds (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hW : ∀ t, 0 < W t) (hQ : ∀ t, 0 < Q t) (t : ℕ) :
    Q t * N t ^ φ / W t = β * N (t + 1) ^ φ / W (t + 1) := by
  set k := W t / (Q t * W (t + 1)) with hk
  set f : ℝ → ℝ := fun δ => β ^ t * (u φ (C t) (N t + δ) - u φ (C t) (N t)) +
    β ^ (t + 1) * (u φ (C (t + 1)) (N (t + 1) - k * δ) - u φ (C (t + 1)) (N (t + 1))) with hfdef
  have hloc : IsLocalMax f 0 := by
    have hc : Continuous fun δ : ℝ => N (t + 1) - k * δ := by fun_prop
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < N (t + 1) - k * δ :=
      (hc.tendsto 0).eventually_const_lt (by simpa using hN (t + 1))
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), -N t < δ := eventually_gt_nhds (by linarith [hN t])
    filter_upwards [e1, e2] with δ h1 h2
    have hfeas : Feasible P W Q T C
        (Function.update (Function.update N t (N t + δ)) (t + 1) (N (t + 1) - k * δ)) M
        (Function.update B (t + 1) (B (t + 1) + W t * δ / Q t)) := by
      intro s
      obtain ⟨hb, hc', hCp, hNp⟩ := hopt.1 s
      have hQW1 : Q t * (W t * δ / Q t) = W t * δ := by field_simp [(hQ t).ne']
      have hQW2 : W (t + 1) * (k * δ) = W t * δ / Q t := by
        rw [hk]; field_simp [(hQ t).ne', (hW (t + 1)).ne']
      simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;> first | omega | nlinarith
    have hg := gain_nonpos hopt t hfeas
      (fun s h1 h2 => by simp [h1, h2])
      (fun s h1 => by simp [h1])
    simp only [Function.update_self, Function.update_apply, show t ≠ t + 1 by omega,
      ↓reduceIte] at hg
    simp only [hfdef, add_zero, mul_zero, sub_zero, sub_self]
    linarith
  have hd : HasDerivAt f (β ^ t * (-(N t ^ φ)) + β ^ (t + 1) * (-(N (t + 1) ^ φ) * -k)) 0 := by
    have hn : HasDerivAt (fun δ => u φ (C t) (N t + δ) - u φ (C t) (N t)) (-(N t ^ φ)) 0 := by
      have := ((hasDerivAt_disutil hφ (N t + 0)).comp 0 ((hasDerivAt_id' 0).const_add (N t)))
      have h2 := (this.const_sub (Real.log (C t))).sub_const (u φ (C t) (N t))
      simp only [add_zero, mul_one] at h2
      exact h2.congr_deriv (by ring)
    have hm : HasDerivAt (fun δ => u φ (C (t + 1)) (N (t + 1) - k * δ) -
        u φ (C (t + 1)) (N (t + 1))) (-(N (t + 1) ^ φ) * -k) 0 := by
      have hin : HasDerivAt (fun δ : ℝ => N (t + 1) - k * δ) (-k) 0 := by
        have := ((hasDerivAt_id' (0 : ℝ)).const_mul k).const_sub (N (t + 1))
        simpa using this
      have := (hasDerivAt_disutil hφ (N (t + 1) - k * 0)).comp 0 hin
      have h2 := (this.const_sub (Real.log (C (t + 1)))).sub_const (u φ (C (t + 1)) (N (t + 1)))
      simp only [mul_zero, sub_zero] at h2
      exact h2.congr_deriv (by ring)
    exact (hn.const_mul (β ^ t)).add (hm.const_mul (β ^ (t + 1)))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb : 0 < β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h1 : β ^ t * N t ^ φ = β ^ t * (β * N (t + 1) ^ φ * k) := by linarith
  have h2 := mul_left_cancel₀ hb.ne' h1
  rw [hk] at h2
  rw [h2]
  field_simp [(hQ t).ne', (hW t).ne', (hW (t + 1)).ne']

/-- Galí (2015), Ex. 2.8(a): the consumption–labour perturbation at date `t`
(`C_t + δ`, `N_t + P_t δ/W_t`) is feasible whenever the CIA still holds and the levels stay
admissible. -/
theorem cia_family_feasible (hopt : Optimal β φ P W Q T C N M B) (hW : ∀ t, 0 < W t)
    {t : ℕ} {δ : ℝ} (h1 : 0 < C t + δ) (h2 : 0 ≤ N t + P t * δ / W t)
    (h3 : P t * (C t + δ) ≤ M t + T t) :
    Feasible P W Q T (Function.update C t (C t + δ)) (Function.update N t (N t + P t * δ / W t))
      M B := by
  intro s
  obtain ⟨hb, hc', hCp, hNp⟩ := hopt.1 s
  have hPW : W t * (P t * δ / W t) = P t * δ := by field_simp [(hW t).ne']
  simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;> first | omega | nlinarith

/-- Galí (2015), Ex. 2.8(a): the utility gain of the consumption–labour perturbation and its
derivative `β^t (1/C_t − N_t^φ P_t/W_t)` at `δ = 0`. -/
theorem hasDerivAt_cia_family {t : ℕ} (hφ : 0 ≤ φ) (hC : 0 < C t) :
    HasDerivAt (fun δ => β ^ t * (u φ (C t + δ) (N t + P t * δ / W t) - u φ (C t) (N t)))
      (β ^ t * ((C t)⁻¹ - N t ^ φ * (P t / W t))) 0 := by
  have hin : HasDerivAt (fun δ : ℝ => N t + P t * δ / W t) (P t / W t) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).const_mul (P t)).div_const (W t)).const_add (N t)
    simpa using this
  have hl : HasDerivAt (fun δ : ℝ => Real.log (C t + δ)) (C t + 0)⁻¹ 0 :=
    (Real.hasDerivAt_log (by simpa using hC.ne')).comp 0 ((hasDerivAt_id' 0).const_add (C t))
      |>.congr_deriv (by simp)
  have hd := (hasDerivAt_disutil hφ (N t + P t * 0 / W t)).comp 0 hin
  simp only [mul_zero, zero_div, add_zero] at hl hd
  have := ((HasDerivAt.sub hl hd).sub_const (u φ (C t) (N t))).const_mul (β ^ t)
  exact this

/-- Galí (2015), Ex. 2.8(a), p. 50 (**KKT, the inequality**): only *lower* consumption is
always feasible under the CIA, so `N_t^φ P_t/W_t ≤ 1/C_t`. -/
theorem foc_cia_ineq (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hW : ∀ t, 0 < W t) (t : ℕ) :
    N t ^ φ * P t / W t ≤ 1 / C t := by
  have hC := (hopt.1 t).2.2.1
  have hcia := (hopt.1 t).2.1
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C t + δ :=
    (eventually_gt_nhds (show -C t < (0 : ℝ) by linarith)).mono fun δ h => by linarith
  have hc : Continuous fun δ : ℝ => N t + P t * δ / W t := by fun_prop
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < N t + P t * δ / W t :=
    (hc.tendsto 0).eventually_const_lt (by simpa using hN t)
  have hleft : ∀ᶠ δ in 𝓝 (0 : ℝ), δ ≤ 0 →
      β ^ t * (u φ (C t + δ) (N t + P t * δ / W t) - u φ (C t) (N t)) ≤
        β ^ t * (u φ (C t + 0) (N t + P t * 0 / W t) - u φ (C t) (N t)) := by
    filter_upwards [e1, e2] with δ h1 h2 hδ
    have h3 : P t * (C t + δ) ≤ M t + T t := by
      simp only [CIA] at hcia; nlinarith [hP t]
    have hg := gain_nonpos hopt t (cia_family_feasible hopt hW h1 h2.le h3)
      (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [mul_zero, zero_div, add_zero, sub_self, mul_zero]
    exact hg
  have h0 := nonneg_of_left_max (hasDerivAt_cia_family (β := β) (P := P) (W := W) hφ hC) hleft
  have h1 : 0 ≤ (C t)⁻¹ - N t ^ φ * (P t / W t) :=
    nonneg_of_mul_nonneg_right (by linarith) (pow_pos hβ t)
  rw [mul_div_assoc, one_div]
  linarith

/-- Galí (2015), Ex. 2.8(a), p. 50 (**KKT, complementary slackness**): if the CIA is slack at
`t`, the perturbation is feasible in both directions and `N_t^φ P_t/W_t = 1/C_t`. -/
theorem foc_cia_slack (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hW : ∀ t, 0 < W t) {t : ℕ} (hslack : P t * C t < M t + T t) :
    N t ^ φ * P t / W t = 1 / C t := by
  have hC := (hopt.1 t).2.2.1
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C t + δ :=
    (eventually_gt_nhds (show -C t < (0 : ℝ) by linarith)).mono fun δ h => by linarith
  have hc : Continuous fun δ : ℝ => N t + P t * δ / W t := by fun_prop
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < N t + P t * δ / W t :=
    (hc.tendsto 0).eventually_const_lt (by simpa using hN t)
  have hc3 : Continuous fun δ : ℝ => P t * (C t + δ) := by fun_prop
  have e3 : ∀ᶠ δ in 𝓝 (0 : ℝ), P t * (C t + δ) < M t + T t :=
    (hc3.tendsto 0).eventually_lt_const (by simpa using hslack)
  have hloc : IsLocalMax (fun δ => β ^ t * (u φ (C t + δ) (N t + P t * δ / W t) -
      u φ (C t) (N t))) 0 := by
    filter_upwards [e1, e2, e3] with δ h1 h2 h3
    have hg := gain_nonpos hopt t (cia_family_feasible hopt hW h1 h2.le h3.le)
      (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
    simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
      ↓reduceIte, sub_self, mul_zero, add_zero] at hg
    simp only [mul_zero, zero_div, add_zero, sub_self, mul_zero]
    exact hg
  have h0 := hloc.hasDerivAt_eq_zero (hasDerivAt_cia_family hφ hC)
  have h1 : (C t)⁻¹ - N t ^ φ * (P t / W t) = 0 :=
    (mul_eq_zero.1 h0).resolve_left (pow_pos hβ t).ne'
  rw [mul_div_assoc, one_div]
  linarith

/-- Galí (2015), Ex. 2.8(a), p. 50 (**KKT multipliers**): with `λ_t = N_t^φ/W_t` (budget) and
`μ_t = 1/(P_t C_t) − λ_t` (CIA): `1/C_t = P_t(λ_t + μ_t)`, `λ_t = β(λ_{t+1} + μ_{t+1})` (money),
`λ_t Q_t = β λ_{t+1}` (bonds), `μ_t ≥ 0`, and `μ_t (M_t + T_t − P_t C_t) = 0`. -/
theorem kkt (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hW : ∀ t, 0 < W t) (hQ : ∀ t, 0 < Q t) :
    ∃ lam mu : ℕ → ℝ, (∀ t, lam t = N t ^ φ / W t) ∧
      (∀ t, 1 / C t = P t * (lam t + mu t)) ∧ (∀ t, lam t = β * (lam (t + 1) + mu (t + 1))) ∧
      (∀ t, lam t * Q t = β * lam (t + 1)) ∧ (∀ t, 0 ≤ mu t) ∧
      (∀ t, mu t * (M t + T t - P t * C t) = 0) := by
  have hC := fun t => (hopt.1 t).2.2.1
  refine ⟨fun t => N t ^ φ / W t, fun t => 1 / (P t * C t) - N t ^ φ / W t, fun _ => rfl,
    fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · field_simp [(hP t).ne', (hC t).ne']
    ring
  · simp only [add_sub_cancel]
    rw [foc_labour_money hopt hβ hφ hN hP t]
    field_simp [(hW t).ne']
  · rw [mul_comm, ← mul_div_assoc, foc_labour_bonds hopt hβ hφ hN hW hQ t, mul_div_assoc]
  · have := foc_cia_ineq hopt hβ hφ hN hP hW t
    have h2 : N t ^ φ / W t ≤ 1 / (P t * C t) := by
      rw [div_le_div_iff₀ (hW t) (mul_pos (hP t) (hC t))]
      rw [div_le_div_iff₀ (hW t) (hC t)] at this
      nlinarith
    linarith
  · rcases (hopt.1 t).2.1.lt_or_eq with hlt | heq
    · have := foc_cia_slack hopt hβ hφ hN hW hlt
      have h2 : 1 / (P t * C t) - N t ^ φ / W t = 0 := by
        rw [div_eq_div_iff (hW t).ne' (hC t).ne'] at this
        field_simp [(hP t).ne', (hC t).ne', (hW t).ne']
        linarith
      change (1 / (P t * C t) - N t ^ φ / W t) * (M t + T t - P t * C t) = 0
      rw [h2, zero_mul]
    · rw [heq, sub_self, mul_zero]

/-! ### No-Ponzi, overtaking optimality and transversality -/

/-- Galí (2015), p. 19 (ch. 2 notation): the date-0 price `∏_{s<T} Q_s` of one unit of money
delivered at date `T`. -/
noncomputable def disc (Q : ℕ → ℝ) (T : ℕ) : ℝ := ∏ s ∈ Finset.range T, Q s

/-- Galí (2015), p. 19: `disc Q (s+1) = disc Q s · Q_s`. -/
theorem disc_succ (Q : ℕ → ℝ) (s : ℕ) : disc Q (s + 1) = disc Q s * Q s :=
  Finset.prod_range_succ _ _

/-- Galí (2015), p. 19: discount factors are positive when bond prices are. -/
theorem disc_pos {Q : ℕ → ℝ} (hQ : ∀ t, 0 < Q t) (T : ℕ) : 0 < disc Q T :=
  Finset.prod_pos fun s _ => hQ s

/-- Galí (2015), eq. (3), p. 19, for Ex. 2.8: the no-Ponzi condition on total financial wealth
`B_T + M_T` carried into `T`, `liminf_T disc_T (B_T + M_T) ≥ 0`. -/
def NoPonzi (Q M B : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ disc Q T * (B T + M T)

/-- Galí (2015), eqs. (1)–(3), pp. 18–19, for Ex. 2.8: optimality in the overtaking sense
against every feasible plan satisfying the no-Ponzi condition (the infinite-horizon problem;
deviations need not be finite). -/
def OptimalNP (β φ : ℝ) (P W Q T C N M B : ℕ → ℝ) : Prop :=
  (Feasible P W Q T C N M B ∧ NoPonzi Q M B) ∧
    ∀ C' N' M' B' : ℕ → ℝ, Feasible P W Q T C' N' M' B' → NoPonzi Q M' B' → M' 0 = M 0 →
      B' 0 = B 0 → ∀ ε > 0, ∀ᶠ T₀ in atTop,
        ∑ s ∈ Finset.range T₀, β ^ s * u φ (C' s) (N' s) ≤
          ∑ s ∈ Finset.range T₀, β ^ s * u φ (C s) (N s) + ε

/-- Galí (2015), Ex. 2.8(a): an overtaking-optimal plan is optimal against finite deviations,
so all the first-order conditions of (a) apply to it. -/
theorem optimal_of_optimalNP (hopt : OptimalNP β φ P W Q T C N M B) :
    Optimal β φ P W Q T C N M B := by
  refine ⟨hopt.1.1, fun C' N' M' B' T₀ hf hM hB hagree => ?_⟩
  have hNP : NoPonzi Q M' B' := fun ε hε => by
    filter_upwards [hopt.1.2 ε hε, eventually_ge_atTop T₀] with T h1 h2
    rw [(hagree T h2).2.2.1, (hagree T h2).2.2.2]
    exact h1
  have key : ∀ ε > 0, ∑ s ∈ Finset.range T₀, β ^ s * u φ (C' s) (N' s) ≤
      ∑ s ∈ Finset.range T₀, β ^ s * u φ (C s) (N s) + ε := by
    intro ε hε
    obtain ⟨T₁, hT₁⟩ := ((hopt.2 C' N' M' B' hf hNP hM hB ε hε).and
      (eventually_ge_atTop T₀)).exists
    have htail : ∑ s ∈ Finset.Ico T₀ T₁, β ^ s * u φ (C' s) (N' s) =
        ∑ s ∈ Finset.Ico T₀ T₁, β ^ s * u φ (C s) (N s) :=
      Finset.sum_congr rfl fun s hs => by
        rw [(hagree s (Finset.mem_Ico.1 hs).1).1, (hagree s (Finset.mem_Ico.1 hs).1).2.1]
    have h1 := hT₁.1
    rw [← Finset.sum_range_add_sum_Ico _ hT₁.2, ← Finset.sum_range_add_sum_Ico _ hT₁.2,
      htail] at h1
    linarith
  by_contra hcon
  push Not at hcon
  have := key _ (half_pos (sub_pos.2 hcon))
  linarith

/-- Galí (2015), p. 20 and eq. (6), p. 19, for Ex. 2.8 (**necessity of transversality**): at an
overtaking-optimal plan the no-Ponzi condition cannot hold strictly. If the discounted wealth
stayed above `L > 0`, the household could work `d/W_0` less at date 0 and roll the debt `d`
over forever. Hence `disc_T (B_T + M_T) < L` for infinitely many `T`. -/
theorem tvc_liminf_of_optimalNP (hopt : OptimalNP β φ P W Q T C N M B) (hφ : 0 ≤ φ)
    (hQ : ∀ t, 0 < Q t) (hW : 0 < W 0) (hN : 0 < N 0) {L : ℝ} (hL : 0 < L) :
    ∃ᶠ T in atTop, disc Q T * (B T + M T) < L := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  set d := min L (W 0 * N 0) with hd
  have hd0 : 0 < d := lt_min hL (mul_pos hW hN)
  have hdL : d ≤ L := min_le_left _ _
  have hdW : d ≤ W 0 * N 0 := min_le_right _ _
  have hN' : 0 ≤ N 0 - d / W 0 := by
    rw [sub_nonneg, div_le_iff₀ hW]; linarith
  have hNlt : N 0 - d / W 0 < N 0 := by
    have := div_pos hd0 hW; linarith
  set N' := Function.update N 0 (N 0 - d / W 0) with hN'def
  set B' : ℕ → ℝ := fun s => if s = 0 then B 0 else B s - d / disc Q s with hB'def
  have hdisc := disc_pos hQ
  have hfeas : Feasible P W Q T C N' M B' := by
    intro s
    obtain ⟨hb, hc, hCp, hNp⟩ := hopt.1.1 s
    refine ⟨?_, hc, hCp, ?_⟩
    · simp only [Budget] at hb ⊢
      rcases Nat.eq_zero_or_pos s with rfl | hs
      · simp only [hB'def, hN'def, Function.update_self, show (0 + 1 : ℕ) ≠ 0 by omega,
          ↓reduceIte]
        have e1 : Q 0 * (B (0 + 1) - d / disc Q (0 + 1)) = Q 0 * B (0 + 1) - d := by
          rw [disc_succ, show disc Q 0 = 1 from Finset.prod_range_zero _, one_mul]
          field_simp [(hQ 0).ne']
        have e2 : W 0 * (N 0 - d / W 0) = W 0 * N 0 - d := by field_simp [hW.ne']
        rw [e1, e2]
        linarith
      · simp only [hB'def, hN'def, Function.update_of_ne (show s ≠ 0 by omega),
          show s + 1 ≠ 0 by omega, show s ≠ 0 by omega, ↓reduceIte]
        have e1 : Q s * (B (s + 1) - d / disc Q (s + 1)) = Q s * B (s + 1) - d / disc Q s := by
          rw [disc_succ]
          field_simp [(hQ s).ne', (hdisc s).ne']
        rw [e1]
        linarith
    · by_cases hs : s = 0
      · subst hs; simp only [hN'def, Function.update_self]; exact hN'
      · simp only [hN'def, Function.update_of_ne hs]; exact hNp
  have hNP : NoPonzi Q M B' := fun ε hε => by
    filter_upwards [hcon, eventually_ge_atTop 1] with T hT hT1
    push Not at hT
    simp only [hB'def, show T ≠ 0 by omega, ↓reduceIte]
    rw [show disc Q T * (B T - d / disc Q T + M T) = disc Q T * (B T + M T) - d by
      field_simp [(hdisc T).ne']; ring]
    linarith
  have hG : 0 < u φ (C 0) (N 0 - d / W 0) - u φ (C 0) (N 0) := by
    have := Real.rpow_lt_rpow hN' hNlt (by linarith : (0 : ℝ) < 1 + φ)
    have h1 : (0 : ℝ) < 1 + φ := by linarith
    simp only [u]
    have : (N 0 - d / W 0) ^ (1 + φ) / (1 + φ) < N 0 ^ (1 + φ) / (1 + φ) :=
      div_lt_div_of_pos_right this h1
    linarith
  set G := u φ (C 0) (N 0 - d / W 0) - u φ (C 0) (N 0) with hGdef
  obtain ⟨T₁, hT₁⟩ := ((hopt.2 C N' M B' hfeas hNP rfl (by simp [hB'def]) (G / 2)
    (half_pos hG)).and (eventually_ge_atTop 1)).exists
  have h1 := hT₁.1
  obtain ⟨k, hk⟩ : ∃ k, T₁ = k + 1 := ⟨T₁ - 1, by omega⟩
  rw [hk, Finset.sum_range_succ', Finset.sum_range_succ'] at h1
  have hsame : ∑ s ∈ Finset.range k, β ^ (s + 1) * u φ (C (s + 1)) (N' (s + 1)) =
      ∑ s ∈ Finset.range k, β ^ (s + 1) * u φ (C (s + 1)) (N (s + 1)) :=
    Finset.sum_congr rfl fun s _ => by
      rw [hN'def, Function.update_of_ne (show s + 1 ≠ 0 by omega)]
  rw [hsame, hN'def, Function.update_self] at h1
  simp only [pow_zero, one_mul] at h1
  linarith

/-! ### (a) Sufficiency of the first-order conditions -/

/-- A differentiable function on `(0, ∞)` with nonincreasing derivative lies below its tangent
lines (restated from the Chapter 3 project; concavity for Galí (2015), Ex. 2.8(a)). -/
theorem le_tangent {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hcont : ContinuousOn f (Set.uIcc x y)) (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z)
    (hanti : AntitoneOn f' (Set.Ioi 0)) : f y ≤ f x + f' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_le hxy.le] at hcont) (fun z hz => hd z (hx.trans hz.1))
    have hle : f' c ≤ f' x := hanti hx (hx.trans hc.1) hc.1.le
    have hpos : 0 < y - x := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith
  · simp
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope f f' hxy
      (by rwa [Set.uIcc_of_ge hxy.le] at hcont) (fun z hz => hd z (lt_of_le_of_lt hy hz.1))
    have hle : f' x ≤ f' c := hanti (lt_of_le_of_lt hy hc.1) hx hc.2.le
    have hpos : 0 < x - y := sub_pos.2 hxy
    rw [eq_div_iff hpos.ne'] at hcs
    nlinarith

/-- Galí (2015), Ex. 2.8(a): concavity of `u`, in tangent form
`u(C', N') ≤ u(C, N) + (C' − C)/C − N^φ (N' − N)` for `C, C', N > 0`, `N' ≥ 0`. -/
theorem u_le_tangent (hφ : 0 ≤ φ) {C N C' N' : ℝ} (hC : 0 < C) (hN : 0 < N) (hC' : 0 < C')
    (hN' : 0 ≤ N') : u φ C' N' ≤ u φ C N + (C' - C) / C - N ^ φ * (N' - N) := by
  have hlog : Real.log C' ≤ Real.log C + (C' - C) / C := by
    have h := Real.log_le_sub_one_of_pos (div_pos hC' hC)
    rw [Real.log_div hC'.ne' hC.ne'] at h
    have : C' / C - 1 = (C' - C) / C := by field_simp
    linarith
  have hv : N ^ (1 + φ) / (1 + φ) + N ^ φ * (N' - N) ≤ N' ^ (1 + φ) / (1 + φ) := by
    have h := le_tangent (f := fun x => -(x ^ (1 + φ) / (1 + φ))) (f' := fun x => -x ^ φ) hN hN'
      (((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 1 + φ)).div_const
        (1 + φ)).neg.continuousOn) (fun z _ => (hasDerivAt_disutil hφ z).neg)
      (fun a ha b _ hab => neg_le_neg (Real.rpow_le_rpow (le_of_lt ha) hab hφ))
    linarith
  unfold u
  linarith

/-- Galí (2015), Ex. 2.8(a): the discounted budget multiplier `Λ_t = βᵗ N_t^φ/W_t`
(`= βᵗ λ_t`). -/
noncomputable def lamD (β φ : ℝ) (W N : ℕ → ℝ) (t : ℕ) : ℝ := β ^ t * N t ^ φ / W t

/-- Galí (2015), Ex. 2.8(a): the discounted CIA multiplier `βᵗ/(P_t C_t) − Λ_t` (`= βᵗ μ_t`). -/
noncomputable def muD (β φ : ℝ) (P W C N : ℕ → ℝ) (t : ℕ) : ℝ :=
  β ^ t / (P t * C t) - lamD β φ W N t

/-- Galí (2015), Ex. 2.8(a): an optimal plan exhausts its budget at every date where hours are
positive (otherwise working less would be feasible and better). -/
theorem budget_binds_of_optimal (hopt : Optimal β φ P W Q T C N M B) (hβ : 0 < β)
    (hφ : 0 ≤ φ) (hW : ∀ t, 0 < W t) {t : ℕ} (hN : 0 < N t) :
    P t * C t + Q t * B (t + 1) + M (t + 1) = B t + M t + W t * N t + T t := by
  by_contra hne
  have hlt := lt_of_le_of_ne (hopt.1 t).1 hne
  set sl := B t + M t + W t * N t + T t - (P t * C t + Q t * B (t + 1) + M (t + 1)) with hsl
  have hsl0 : 0 < sl := by rw [hsl]; linarith
  set δ := min (N t / 2) (sl / (2 * W t)) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (div_pos hsl0 (by linarith [hW t]))
  have hδN : δ ≤ N t / 2 := min_le_left _ _
  have hδs : δ ≤ sl / (2 * W t) := min_le_right _ _
  have hWδ : W t * δ ≤ sl / 2 := by
    have := mul_le_mul_of_nonneg_left hδs (hW t).le
    rw [show W t * (sl / (2 * W t)) = sl / 2 by field_simp [(hW t).ne']] at this
    exact this
  have hfeas : Feasible P W Q T C (Function.update N t (N t - δ)) M B := by
    intro s
    obtain ⟨hb, hc', hCp, hNp⟩ := hopt.1 s
    simp only [Budget, CIA, Function.update_apply] at hb hc' ⊢
    refine ⟨?_, hc', hCp, ?_⟩ <;> (try split_ifs) <;> (try subst_vars) <;>
      first | omega | nlinarith
  have hg := gain_nonpos hopt t hfeas (fun s h1 _ => by simp [h1]) (fun s _ => by simp)
  simp only [Function.update_self, Function.update_apply, show t + 1 ≠ t by omega,
    ↓reduceIte, sub_self, mul_zero, add_zero] at hg
  have hlt2 : (N t - δ) ^ (1 + φ) < N t ^ (1 + φ) :=
    Real.rpow_lt_rpow (by linarith) (by linarith) (by linarith)
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  have h3 : (N t - δ) ^ (1 + φ) / (1 + φ) < N t ^ (1 + φ) / (1 + φ) :=
    div_lt_div_of_pos_right hlt2 h1
  have hpos : 0 < β ^ t * (u φ (C t) (N t - δ) - u φ (C t) (N t)) := by
    refine mul_pos (pow_pos hβ t) ?_
    simp only [u]
    linarith
  linarith

/-- Galí (2015), Ex. 2.8(a) (**sufficiency of the first-order conditions**): let a feasible
plan with positive hours, prices and wages exhaust its budget and satisfy the
conditions of (a) — the labour–money condition, the bond condition, the KKT inequality with
complementary slackness — and the transversality condition
`disc_{k+1} B_{k+1} + disc_k M_{k+1} → 0`. Then it overtakes every feasible no-Ponzi plan with
the same initial holdings and nonnegative money holdings. The proof is the Lagrangian
argument: concavity gives a per-period bound, the multipliers telescope the budgets, and what
remains is the transversality term of the plan minus the no-Ponzi term of the competitor. -/
theorem overtakes_of_foc (hβ : 0 < β) (hφ : 0 ≤ φ) (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t)
    (hW : ∀ t, 0 < W t) (hfeas : Feasible P W Q T C N M B)
    (hbind : ∀ t, P t * C t + Q t * B (t + 1) + M (t + 1) = B t + M t + W t * N t + T t)
    (hI : ∀ t, N t ^ φ = β * W t / (P (t + 1) * C (t + 1)))
    (hII : ∀ t, Q t * N t ^ φ / W t = β * N (t + 1) ^ φ / W (t + 1))
    (hIII : ∀ t, N t ^ φ * P t / W t ≤ 1 / C t)
    (hsl : ∀ t, P t * C t < M t + T t → N t ^ φ * P t / W t = 1 / C t)
    (htvc : ∀ ε > 0, ∀ᶠ k in atTop, disc Q (k + 1) * B (k + 1) + disc Q k * M (k + 1) ≤ ε)
    {C' N' M' B' : ℕ → ℝ} (hf' : Feasible P W Q T C' N' M' B') (hnp' : NoPonzi Q M' B')
    (hM' : ∀ t, 0 ≤ M' t) (hM0 : M' 0 = M 0) (hB0 : B' 0 = B 0) :
    ∀ ε > 0, ∀ᶠ T₀ in atTop, ∑ s ∈ Finset.range T₀, β ^ s * u φ (C' s) (N' s) ≤
      ∑ s ∈ Finset.range T₀, β ^ s * u φ (C s) (N s) + ε := by
  have hC : ∀ t, 0 < C t := fun t => (hfeas t).2.2.1
  set Λ := lamD β φ W N with hΛ
  set Mu := muD β φ P W C N with hMu
  -- multiplier identities
  have hΛQ : ∀ t, Λ t * Q t = Λ (t + 1) := by
    intro t
    calc Λ t * Q t = β ^ t * (Q t * N t ^ φ / W t) := by simp only [hΛ, lamD]; ring
      _ = β ^ t * (β * N (t + 1) ^ φ / W (t + 1)) := by rw [hII t]
      _ = Λ (t + 1) := by simp only [hΛ, lamD, pow_succ]; ring
  have hΛMu : ∀ t, Λ t = Λ (t + 1) + Mu (t + 1) := by
    intro t
    simp only [hMu, muD, hΛ, add_sub_cancel, lamD, hI t, pow_succ]
    field_simp [(hW t).ne', (hP (t + 1)).ne', (hC (t + 1)).ne']
  have hΛpos : ∀ t, 0 < Λ t := fun t =>
    div_pos (mul_pos (pow_pos hβ t) (Real.rpow_pos_of_pos (hN t) φ)) (hW t)
  have hMu0 : ∀ t, 0 ≤ Mu t := by
    intro t
    have h3 := hIII t
    have e1 : β ^ t * N t ^ φ / W t = (β ^ t / P t) * (N t ^ φ * P t / W t) := by
      field_simp [(hP t).ne', (hW t).ne']
    have e2 : β ^ t / (P t * C t) = (β ^ t / P t) * (1 / C t) := by
      field_simp [(hP t).ne', (hC t).ne']
    simp only [hMu, muD, lamD, sub_nonneg]
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h3 (div_nonneg (pow_pos hβ t).le (hP t).le)
  have hΛdisc : ∀ t, Λ t = Λ 0 * disc Q t := by
    intro t
    induction t with
    | zero => simp [disc]
    | succ t ih => rw [← hΛQ t, ih, disc_succ]; ring
  -- per-period bound
  have hper : ∀ t, β ^ t * (u φ (C' t) (N' t) - u φ (C t) (N t)) ≤
      Λ t * ((B' t - B t) + (M' t - M t) - Q t * (B' (t + 1) - B (t + 1)) -
        (M' (t + 1) - M (t + 1))) + Mu t * (M' t - M t) := by
    intro t
    obtain ⟨hb', hc', hC't, hN't⟩ := hf' t
    have hcon := u_le_tangent hφ (hC t) (hN t) hC't hN't
    have e1 : β ^ t / C t = P t * (Λ t + Mu t) := by
      simp only [hMu, muD, hΛ, add_sub_cancel]; field_simp [(hP t).ne']
    have e2 : β ^ t * N t ^ φ = W t * Λ t := by
      simp only [hΛ, lamD]; field_simp [(hW t).ne']
    have hcon2 : β ^ t * (u φ (C' t) (N' t) - u φ (C t) (N t)) ≤
        P t * (Λ t + Mu t) * (C' t - C t) - W t * Λ t * (N' t - N t) := by
      have := mul_le_mul_of_nonneg_left (show u φ (C' t) (N' t) - u φ (C t) (N t) ≤
        (C' t - C t) / C t - N t ^ φ * (N' t - N t) by linarith) (pow_pos hβ t).le
      rw [← e1, ← e2]
      calc _ ≤ _ := this
        _ = _ := by ring
    have hbud : P t * (C' t - C t) - W t * (N' t - N t) ≤ (B' t - B t) + (M' t - M t) -
        Q t * (B' (t + 1) - B (t + 1)) - (M' (t + 1) - M (t + 1)) := by
      simp only [Budget] at hb'
      linarith [hbind t]
    have hcia : Mu t * (P t * (C' t - C t)) ≤ Mu t * (M' t - M t) := by
      rcases (hfeas t).2.1.lt_or_eq with hlt | heq
      · have hz : Mu t = 0 := by
          have := hsl t hlt
          have e1 : β ^ t * N t ^ φ / W t = (β ^ t / P t) * (N t ^ φ * P t / W t) := by
            field_simp [(hP t).ne', (hW t).ne']
          have e2 : β ^ t / (P t * C t) = (β ^ t / P t) * (1 / C t) := by
            field_simp [(hP t).ne', (hC t).ne']
          simp only [hMu, muD, lamD]
          rw [e1, e2, this, sub_self]
        rw [hz, zero_mul, zero_mul]
      · simp only [CIA] at hc'
        exact mul_le_mul_of_nonneg_left (by linarith) (hMu0 t)
    nlinarith [mul_le_mul_of_nonneg_left hbud (hΛpos t).le]
  -- telescoping
  have htel : ∀ T₀, ∑ t ∈ Finset.range T₀, (Λ t * ((B' t - B t) + (M' t - M t) -
      Q t * (B' (t + 1) - B (t + 1)) - (M' (t + 1) - M (t + 1))) + Mu t * (M' t - M t)) =
      -(Λ T₀ * (B' T₀ - B T₀)) - (Λ T₀ + Mu T₀) * (M' T₀ - M T₀) := by
    intro T₀
    induction T₀ with
    | zero => simp [hM0, hB0]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      linear_combination (-(B' (k + 1) - B (k + 1))) * hΛQ k +
        (-(M' (k + 1) - M (k + 1))) * hΛMu k
  intro ε hε
  have hΛ0 := hΛpos 0
  have hε2 : 0 < ε / (2 * Λ 0) := div_pos hε (by linarith)
  filter_upwards [(tendsto_sub_atTop_nat 1).eventually (htvc _ hε2), hnp' _ hε2,
    eventually_ge_atTop 1] with T₀ h1 h2 h3
  obtain ⟨k, rfl⟩ : ∃ k, T₀ = k + 1 := ⟨T₀ - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h1
  have hsum := Finset.sum_le_sum fun t (_ : t ∈ Finset.range (k + 1)) => hper t
  rw [htel] at hsum
  have hdiff : ∑ s ∈ Finset.range (k + 1), β ^ s * u φ (C' s) (N' s) -
      ∑ s ∈ Finset.range (k + 1), β ^ s * u φ (C s) (N s) =
      ∑ t ∈ Finset.range (k + 1), β ^ t * (u φ (C' t) (N' t) - u φ (C t) (N t)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have hk := hΛMu k
  have hMuM : 0 ≤ Mu (k + 1) * M' (k + 1) := mul_nonneg (hMu0 _) (hM' _)
  have ha := mul_le_mul_of_nonneg_left h1 hΛ0.le
  have hb := mul_le_mul_of_nonneg_left h2 hΛ0.le
  have hc : Λ 0 * (ε / (2 * Λ 0)) = ε / 2 := by field_simp
  rw [hc] at ha
  rw [mul_neg, hc] at hb
  have e1 := hΛdisc (k + 1)
  have e2 := hΛdisc k
  have hx : Λ (k + 1) * B (k + 1) + (Λ (k + 1) + Mu (k + 1)) * M (k + 1) =
      Λ 0 * (disc Q (k + 1) * B (k + 1) + disc Q k * M (k + 1)) := by
    rw [← hk, e1, e2]; ring
  have hy : Λ (k + 1) * (B' (k + 1) + M' (k + 1)) =
      Λ 0 * (disc Q (k + 1) * (B' (k + 1) + M' (k + 1))) := by rw [e1]; ring
  nlinarith

/-! #**Infinite horizon, no-Ponzi and transversality.** `NoPonzi`, `OptimalNP` (overtaking
optimality against all feasible no-Ponzi plans); `optimal_of_optimalNP`;
`tvc_liminf_of_optimalNP` (necessity of transversality: rolling over debt `d` while working
`d/W_0` less); `budget_binds_of_optimal`; `overtakes_of_foc` (**sufficiency**: the conditions of
(a), a binding budget and the transversality condition imply overtaking optimality against all
no-Ponzi plans with nonnegative money).

## (b) Money growth and output -/

variable (β φ γ Ms₀ : ℝ) (C N P W Q Ms : ℕ → ℝ)

/-- Galí (2015), Ex. 2.8(b), p. 50: an equilibrium. The household conditions of (a) (`kkt`),
competitive firms `W = P` (`Y = N`), goods-market clearing `C = N`, and money
`M^s_t = M^s_0 (1+γ)ᵗ` held for purchases at `t` (`M_{t−1} + T_t = M^s_t`). -/
structure IsEquilibrium where
  /-- Positive consumption. -/
  pos_C : ∀ t, 0 < C t
  /-- Positive hours. -/
  pos_N : ∀ t, 0 < N t
  /-- Positive prices. -/
  pos_P : ∀ t, 0 < P t
  /-- Labour–money condition `N_t^φ = β W_t/(P_{t+1} C_{t+1})`. -/
  focI : ∀ t, N t ^ φ = β * W t / (P (t + 1) * C (t + 1))
  /-- Bond condition `Q_t N_t^φ/W_t = β N_{t+1}^φ/W_{t+1}`. -/
  focII : ∀ t, Q t * N t ^ φ / W t = β * N (t + 1) ^ φ / W (t + 1)
  /-- KKT inequality `N_t^φ P_t/W_t ≤ 1/C_t`. -/
  focIII : ∀ t, N t ^ φ * P t / W t ≤ 1 / C t
  /-- Complementary slackness. -/
  slack : ∀ t, P t * C t < Ms t → N t ^ φ * P t / W t = 1 / C t
  /-- The CIA constraint. -/
  cia : ∀ t, P t * C t ≤ Ms t
  /-- Competitive firm with `Y = N`: `W = P`. -/
  firm : ∀ t, W t = P t
  /-- Goods-market clearing `C = Y = N`. -/
  clearing : ∀ t, C t = N t
  /-- Constant money growth. -/
  money : ∀ t, Ms t = Ms₀ * (1 + γ) ^ t

variable {β φ γ Ms₀ C N P W Q Ms}

/-- Galí (2015), Ex. 2.8(b): an optimal household plan (with positive hours, prices, wages
and bond prices) at market-clearing prices is an equilibrium. -/
theorem isEquilibrium_of_optimal {T M B : ℕ → ℝ} (hopt : Optimal β φ P W Q T C N M B)
    (hβ : 0 < β) (hφ : 0 ≤ φ) (hN : ∀ t, 0 < N t) (hP : ∀ t, 0 < P t) (hQ : ∀ t, 0 < Q t)
    (hMT : ∀ t, M t + T t = Ms t) (hfirm : ∀ t, W t = P t) (hclear : ∀ t, C t = N t)
    (hmoney : ∀ t, Ms t = Ms₀ * (1 + γ) ^ t) : IsEquilibrium β φ γ Ms₀ C N P W Q Ms := by
  have hW : ∀ t, 0 < W t := fun t => by rw [hfirm t]; exact hP t
  refine ⟨fun t => (hopt.1 t).2.2.1, hN, hP, foc_labour_money hopt hβ hφ hN hP,
    foc_labour_bonds hopt hβ hφ hN hW hQ, foc_cia_ineq hopt hβ hφ hN hP hW, fun t ht => ?_,
    fun t => ?_, hfirm, hclear, hmoney⟩
  · exact foc_cia_slack hopt hβ hφ hN hW (by rw [hMT t]; exact ht)
  · have := (hopt.1 t).2.1
    simp only [CIA] at this
    rw [← hMT t]; exact this

/-- Galí (2015), Ex. 2.8(b): in every equilibrium `Q_t ≤ 1` (a nonnegative nominal rate:
otherwise money would dominate bonds). -/
theorem Q_le_one (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hβ : 0 ≤ β) (t : ℕ) : Q t ≤ 1 := by
  have hW : ∀ t, 0 < W t := fun t => by rw [h.firm t]; exact h.pos_P t
  have ha : 0 < N t ^ φ / W t := div_pos (Real.rpow_pos_of_pos (h.pos_N t) φ) (hW t)
  have hPC : 0 < P (t + 1) * C (t + 1) := mul_pos (h.pos_P _) (h.pos_C _)
  have hI : N t ^ φ / W t = β / (P (t + 1) * C (t + 1)) := by
    rw [h.focI t]; field_simp [(hW t).ne']
  have hIII : N (t + 1) ^ φ / W (t + 1) ≤ 1 / (P (t + 1) * C (t + 1)) := by
    have := h.focIII (t + 1)
    rw [div_le_div_iff₀ (hW _) (h.pos_C _)] at this
    rw [div_le_div_iff₀ (hW _) hPC]
    nlinarith [h.pos_P (t + 1)]
  have hII : Q t * (N t ^ φ / W t) = β * (N (t + 1) ^ φ / W (t + 1)) := by
    rw [← mul_div_assoc, h.focII t, mul_div_assoc]
  have : Q t * (N t ^ φ / W t) ≤ 1 * (N t ^ φ / W t) := by
    rw [hII, one_mul, hI, div_eq_mul_one_div β]
    exact mul_le_mul_of_nonneg_left hIII hβ
  exact le_of_mul_le_mul_right this ha

/-- Galí (2015), Ex. 2.8(b): if `Q_t < 1` (a positive nominal rate) the CIA binds at `t+1`. -/
theorem cia_binds_of_Q_lt_one (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) {t : ℕ}
    (hQ : Q t < 1) : P (t + 1) * C (t + 1) = Ms (t + 1) := by
  by_contra hne
  have hlt := lt_of_le_of_ne (h.cia (t + 1)) hne
  have hW : ∀ t, 0 < W t := fun t => by rw [h.firm t]; exact h.pos_P t
  have ha : 0 < N t ^ φ / W t := div_pos (Real.rpow_pos_of_pos (h.pos_N t) φ) (hW t)
  have hPC : 0 < P (t + 1) * C (t + 1) := mul_pos (h.pos_P _) (h.pos_C _)
  have hI : N t ^ φ / W t = β / (P (t + 1) * C (t + 1)) := by
    rw [h.focI t]; field_simp [(hW t).ne']
  have hIII : N (t + 1) ^ φ / W (t + 1) = 1 / (P (t + 1) * C (t + 1)) := by
    have := h.slack (t + 1) hlt
    rw [div_eq_div_iff (hW _).ne' (h.pos_C _).ne'] at this
    rw [div_eq_div_iff (hW _).ne' hPC.ne']
    linarith
  have hII : Q t * (N t ^ φ / W t) = β * (N (t + 1) ^ φ / W (t + 1)) := by
    rw [← mul_div_assoc, h.focII t, mul_div_assoc]
  have : Q t * (N t ^ φ / W t) = 1 * (N t ^ φ / W t) := by
    rw [hII, one_mul, hI, hIII, div_eq_mul_one_div β]
  have := mul_right_cancel₀ ha.ne' this
  linarith

/-- Galí (2015), Ex. 2.8(b), p. 50 (**money growth and output**): if the CIA binds at `t` and
`t+1`, then `N_t^{1+φ} = β/(1+γ)`. -/
theorem output_of_binding (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hγ : 0 < 1 + γ)
    {t : ℕ} (hb : P t * C t = Ms t) (hb1 : P (t + 1) * C (t + 1) = Ms (t + 1)) :
    N t ^ (1 + φ) = β / (1 + γ) := by
  have hN := h.pos_N t
  have hI := h.focI t
  rw [hb1, h.firm t, h.money (t + 1), pow_succ] at hI
  have hMs : Ms₀ * (1 + γ) ^ t = P t * N t := by rw [← h.money t, ← hb, h.clearing t]
  rw [← mul_assoc, hMs] at hI
  rw [Real.rpow_add hN, Real.rpow_one, hI]
  field_simp [(h.pos_P t).ne', hN.ne', hγ.ne']

/-- Galí (2015), Ex. 2.8(b), p. 50: hence `Y_t = N_t = (β/(1+γ))^{1/(1+φ)}`. -/
theorem output_eq (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hφ : 0 ≤ φ) (hγ : 0 < 1 + γ)
    {t : ℕ} (hb : P t * C t = Ms t) (hb1 : P (t + 1) * C (t + 1) = Ms (t + 1)) :
    N t = (β / (1 + γ)) ^ (1 + φ)⁻¹ := by
  rw [← output_of_binding h hγ hb hb1, Real.rpow_rpow_inv (h.pos_N t).le (by linarith)]

/-- Galí (2015), Ex. 2.8(b), p. 50: equilibrium output `(β/(1+γ))^{1/(1+φ)}` is strictly
decreasing in money growth `γ` (on `γ > −1`). -/
theorem output_strictAnti (hβ : 0 < β) (hφ : 0 ≤ φ) :
    StrictAntiOn (fun γ : ℝ => (β / (1 + γ)) ^ (1 + φ)⁻¹) (Set.Ioi (-1)) := by
  intro γ₁ h1 γ₂ h2 h12
  simp only [Set.mem_Ioi] at h1 h2
  exact Real.rpow_lt_rpow (div_pos hβ (by linarith)).le
    (div_lt_div_of_pos_left hβ (by linarith) (by linarith)) (inv_pos.2 (by linarith))

/-- Galí (2015), Ex. 2.8(b), p. 50 (**existence**): for `0 < β ≤ 1 + γ` and `M^s_0 > 0`, the
allocation `C_t = N_t = N* = (β/(1+γ))^{1/(1+φ)}`, `P_t = M^s_t/N*`, `W = P`, `Q_t = β/(1+γ)`
is an equilibrium (with a binding CIA). -/
theorem stationary_isEquilibrium (hβ : 0 < β) (hγ : β ≤ 1 + γ) (hφ : 0 ≤ φ) (hM : 0 < Ms₀) :
    IsEquilibrium β φ γ Ms₀ (fun _ => (β / (1 + γ)) ^ (1 + φ)⁻¹)
      (fun _ => (β / (1 + γ)) ^ (1 + φ)⁻¹)
      (fun t => Ms₀ * (1 + γ) ^ t / (β / (1 + γ)) ^ (1 + φ)⁻¹)
      (fun t => Ms₀ * (1 + γ) ^ t / (β / (1 + γ)) ^ (1 + φ)⁻¹)
      (fun _ => β / (1 + γ)) (fun t => Ms₀ * (1 + γ) ^ t) := by
  have hγ0 : 0 < 1 + γ := by linarith
  set n := (β / (1 + γ)) ^ (1 + φ)⁻¹ with hn
  have hnpos : 0 < n := Real.rpow_pos_of_pos (div_pos hβ hγ0) _
  have hn1 : n ^ (1 + φ) = β / (1 + γ) :=
    Real.rpow_inv_rpow (div_pos hβ hγ0).le (by linarith)
  have hnφ : n ^ φ * n = β / (1 + γ) := by
    rw [← hn1, Real.rpow_add hnpos, Real.rpow_one, mul_comm]
  have hnφ' : (1 + γ) * (n ^ φ * n) = β := by rw [hnφ]; field_simp
  have hX : n ^ φ * n ≤ 1 := by rw [hnφ, div_le_one hγ0]; exact hγ
  refine ⟨fun _ => hnpos, fun _ => hnpos, fun t => by positivity, fun t => ?_, fun t => ?_,
    fun t => ?_, fun t ht => ?_, fun t => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · rw [pow_succ]
    field_simp
    linear_combination hnφ'
  · rw [pow_succ]
    field_simp
  · rw [div_le_div_iff₀ (by positivity) hnpos]
    field_simp
    linarith [hX]
  · field_simp at ht
    exact absurd ht (lt_irrefl _)
  · field_simp
    rfl

/-- Galí (2015), Ex. 2.8(b): in the stationary equilibrium gross inflation is
`P_{t+1}/P_t = 1 + γ`. -/
theorem stationary_inflation {n : ℝ} (hγ : 0 < 1 + γ) (hM : 0 < Ms₀) (hn : 0 < n) (t : ℕ) :
    (Ms₀ * (1 + γ) ^ (t + 1) / n) / (Ms₀ * (1 + γ) ^ t / n) = 1 + γ := by
  rw [pow_succ]
  field_simp

/-! ### (b) Transversality and the binding CIA in every equilibrium -/

/-- Galí (2015), eq. (6), p. 19, for Ex. 2.8 in equilibrium (`B = 0`, money held into `T+1` is
`M^s_T`): the transversality condition `liminf_T disc_{T+1} M^s_T ≤ 0`, i.e. for every `L > 0`
infinitely often `disc_{T+1} M^s_T < L`. -/
def EqTVC (Q Ms : ℕ → ℝ) : Prop :=
  ∀ L > 0, ∃ᶠ T in atTop, disc Q (T + 1) * Ms T < L

/-- Galí (2015), Ex. 2.8: an overtaking-optimal household plan with no bonds outstanding
(`B = 0`) and money market clearing (`M_{t+1} = M^s_t`) satisfies the equilibrium
transversality condition. -/
theorem eqTVC_of_optimalNP {T M B : ℕ → ℝ} (hopt : OptimalNP β φ P W Q T C N M B)
    (hφ : 0 ≤ φ) (hQ : ∀ t, 0 < Q t) (hW : 0 < W 0) (hN : 0 < N 0) (hB : ∀ t, B t = 0)
    (hM : ∀ t, M (t + 1) = Ms t) : EqTVC Q Ms := by
  intro L hL
  have h := tvc_liminf_of_optimalNP hopt hφ hQ hW hN hL
  rw [Filter.frequently_atTop] at h ⊢
  intro a
  obtain ⟨b, hb, hbL⟩ := h (a + 1)
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  refine ⟨c, by omega, ?_⟩
  rw [hB, hM, zero_add] at hbL
  exact hbL

/-- Galí (2015), Ex. 2.8(b): bond prices are positive in every equilibrium (`β > 0`). -/
theorem Q_pos (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hβ : 0 < β) (t : ℕ) : 0 < Q t := by
  have hW : ∀ t, 0 < W t := fun t => by rw [h.firm t]; exact h.pos_P t
  have h1 := h.focII t
  have hr : 0 < β * N (t + 1) ^ φ / W (t + 1) :=
    div_pos (mul_pos hβ (Real.rpow_pos_of_pos (h.pos_N _) φ)) (hW _)
  rw [← h1, mul_div_assoc] at hr
  exact pos_of_mul_pos_left hr (div_pos (Real.rpow_pos_of_pos (h.pos_N t) φ) (hW t)).le

/-- Galí (2015), Ex. 2.8(b): if the CIA is slack at `t`, then `N_t = 1` (efficient hours). -/
theorem employment_one_of_slack (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hφ : 0 ≤ φ)
    {t : ℕ} (hs : P t * C t < Ms t) : N t = 1 := by
  have e := h.slack t hs
  rw [h.firm t, h.clearing t, mul_div_assoc, div_self (h.pos_P t).ne', mul_one] at e
  have hN := h.pos_N t
  have h2 : N t ^ (1 + φ) = 1 := by
    rw [Real.rpow_add hN, Real.rpow_one, e]; field_simp
  rw [← Real.rpow_rpow_inv hN.le (by linarith : (1 + φ) ≠ 0), h2, Real.one_rpow]

/-- Galí (2015), Ex. 2.8(b): with `0 < β ≤ 1 + γ` a slack CIA stays slack (real balances grow
at the gross rate `(1+γ)/β`). -/
theorem slack_succ (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hφ : 0 ≤ φ) (hβ : 0 < β)
    (hβγ : β ≤ 1 + γ) {t : ℕ} (hs : P t * C t < Ms t) :
    P (t + 1) * C (t + 1) < Ms (t + 1) := by
  have hN := employment_one_of_slack h hφ hs
  have hI := h.focI t
  rw [hN, Real.one_rpow, h.firm t] at hI
  have hPC : 0 < P (t + 1) * C (t + 1) := mul_pos (h.pos_P _) (h.pos_C _)
  have e : P (t + 1) * C (t + 1) = β * P t := by
    rw [eq_div_iff hPC.ne'] at hI; linarith
  rw [h.clearing t, hN, mul_one] at hs
  have hMs : Ms (t + 1) = (1 + γ) * Ms t := by rw [h.money, h.money, pow_succ]; ring
  have hMs0 : 0 ≤ Ms t := (h.pos_P t).le.trans hs.le
  rw [e, hMs]
  calc β * P t < β * Ms t := mul_lt_mul_of_pos_left hs hβ
    _ ≤ (1 + γ) * Ms t := mul_le_mul_of_nonneg_right hβγ hMs0

/-- Galí (2015), Ex. 2.8(b): if the CIA is slack at `t` and `t+1`, the nominal rate is zero:
`Q_t = 1`. -/
theorem Q_eq_one_of_slack (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (hφ : 0 ≤ φ) {t : ℕ}
    (hs : P t * C t < Ms t) (hs1 : P (t + 1) * C (t + 1) < Ms (t + 1)) : Q t = 1 := by
  have hN := employment_one_of_slack h hφ hs
  have hN1 := employment_one_of_slack h hφ hs1
  have hI := h.focI t
  have hII := h.focII t
  rw [hN, Real.one_rpow, h.firm t, h.clearing (t + 1), hN1, mul_one] at hI
  rw [hN, hN1, Real.one_rpow, h.firm t, h.firm (t + 1), mul_one] at hII
  have hP := h.pos_P t
  have hP1 := h.pos_P (t + 1)
  rw [eq_div_iff hP1.ne', one_mul] at hI
  rw [div_eq_div_iff hP.ne' hP1.ne'] at hII
  have : Q t * P (t + 1) = 1 * P (t + 1) := by linarith
  exact mul_right_cancel₀ hP1.ne' this

/-- Galí (2015), Ex. 2.8(b) (**the CIA binds in every equilibrium**, `γ ≥ 0`): with
`0 < β ≤ 1`, `γ ≥ 0` and the transversality condition, the CIA binds at every date. A slack
CIA would stay slack forever with `Q = 1`, and the discounted money stock
`disc_{T+1} M^s_T` would then grow at the rate `1 + γ ≥ 1`, violating transversality. -/
theorem cia_binds_of_tvc (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (htvc : EqTVC Q Ms)
    (hφ : 0 ≤ φ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hγ : 0 ≤ γ) (t : ℕ) : P t * C t = Ms t := by
  by_contra hne
  have hs : P t * C t < Ms t := lt_of_le_of_ne (h.cia t) hne
  have hβγ : β ≤ 1 + γ := by linarith
  have hall : ∀ k, P (t + k) * C (t + k) < Ms (t + k) := by
    intro k
    induction k with
    | zero => simpa using hs
    | succ k ih => exact slack_succ h hφ hβ hβγ ih
  set D : ℕ → ℝ := fun T => disc Q (T + 1) * Ms T with hD
  have hQp := Q_pos h hβ
  have hDt : 0 < D t := by
    have : 0 < Ms t := (mul_pos (h.pos_P t) (h.pos_C t)).trans hs
    exact mul_pos (disc_pos hQp _) this
  have hgrow : ∀ k, D t ≤ D (t + k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hQ1 : Q (t + k + 1) = 1 := Q_eq_one_of_slack h hφ (hall (k + 1)) (by
        simpa [add_assoc] using hall (k + 2))
      have hstep : D (t + (k + 1)) = (1 + γ) * D (t + k) := by
        simp only [hD]
        rw [show t + (k + 1) = t + k + 1 by ring, disc_succ, hQ1, h.money, h.money, pow_succ]
        ring
      have hD0 : 0 ≤ D (t + k) := hDt.le.trans ih
      rw [hstep]
      nlinarith
  obtain ⟨T, hT1, hT2⟩ := ((htvc (D t) hDt).and_eventually (eventually_ge_atTop t)).exists
  obtain ⟨k, rfl⟩ : ∃ k, T = t + k := ⟨T - t, by omega⟩
  exact absurd (hgrow k) (not_le.2 hT1)

/-- Galí (2015), Ex. 2.8(b), p. 50 (**every equilibrium**): with transversality, `0 < β ≤ 1`
and `γ ≥ 0`, output is `Y_t = N_t = (β/(1+γ))^{1/(1+φ)}` at every date. -/
theorem output_eq_of_tvc (h : IsEquilibrium β φ γ Ms₀ C N P W Q Ms) (htvc : EqTVC Q Ms)
    (hφ : 0 ≤ φ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hγ : 0 ≤ γ) (t : ℕ) :
    N t = (β / (1 + γ)) ^ (1 + φ)⁻¹ :=
  output_eq h hφ (by linarith) (cia_binds_of_tvc h htvc hφ hβ hβ1 hγ t)
    (cia_binds_of_tvc h htvc hφ hβ hβ1 hγ (t + 1))

/-- Galí (2015), Ex. 2.8(b) (**correction**: `1 + γ > β` is not enough when `γ < 0`): for
`β < 1 + γ < 1`, `0 < P₀ < M^s_0`, the path `C = N = 1`, `P_t = W_t = P₀ βᵗ`, `Q = 1` is an
equilibrium satisfying transversality in which the CIA is slack at every date, and output
`1` differs from `(β/(1+γ))^{1/(1+φ)}`. -/
theorem slack_equilibrium_counterexample {P₀ : ℝ} (hβ : 0 < β) (hφ : 0 ≤ φ)
    (hβγ : β < 1 + γ) (hγ1 : 1 + γ < 1) (hP₀ : 0 < P₀) (hPM : P₀ < Ms₀) :
    IsEquilibrium β φ γ Ms₀ (fun _ => 1) (fun _ => 1) (fun t => P₀ * β ^ t)
        (fun t => P₀ * β ^ t) (fun _ => 1) (fun t => Ms₀ * (1 + γ) ^ t) ∧
      EqTVC (fun _ => 1) (fun t => Ms₀ * (1 + γ) ^ t) ∧
      (∀ t, P₀ * β ^ t * 1 < Ms₀ * (1 + γ) ^ t) ∧ (β / (1 + γ)) ^ (1 + φ)⁻¹ < 1 := by
  have hγ0 : 0 < 1 + γ := by linarith
  have hslack : ∀ t : ℕ, P₀ * β ^ t * 1 < Ms₀ * (1 + γ) ^ t := by
    intro t
    rw [mul_one]
    exact mul_lt_mul hPM (pow_le_pow_left₀ hβ.le hβγ.le t) (pow_pos hβ t) (by linarith)
  refine ⟨⟨fun _ => one_pos, fun _ => one_pos, fun t => by positivity, fun t => ?_,
    fun t => ?_, fun t => ?_, fun t _ => ?_, fun t => (hslack t).le, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩, ?_, hslack, ?_⟩
  · simp only [Real.one_rpow, mul_one, pow_succ]
    field_simp
  · simp only [Real.one_rpow, pow_succ]
    field_simp
  · simp only [Real.one_rpow]
    field_simp
    rfl
  · simp only [Real.one_rpow]
    field_simp
  · intro L hL
    have hlim : Tendsto (fun T : ℕ => disc (fun _ => (1 : ℝ)) (T + 1) * (Ms₀ * (1 + γ) ^ T))
        atTop (𝓝 0) := by
      have : (fun T : ℕ => disc (fun _ => (1 : ℝ)) (T + 1) * (Ms₀ * (1 + γ) ^ T)) =
          fun T => Ms₀ * (1 + γ) ^ T := by
        funext T; simp [disc]
      rw [this]
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1).const_mul Ms₀
    exact (hlim.eventually (gt_mem_nhds hL)).frequently
  · exact Real.rpow_lt_one (div_pos hβ hγ0).le ((div_lt_one hγ0).2 hβγ)
      (inv_pos.2 (by linarith))

/-! ### (c) Optimal inflation -/

/-- Galí (2015), Ex. 2.8(c), p. 50: `log N − N^{1+φ}/(1+φ) ≤ −1/(1+φ)` for `N > 0`, with
equality iff `N = 1` (the efficient allocation). -/
theorem stationary_utility_le (hφ : 0 ≤ φ) {n : ℝ} (hn : 0 < n) :
    u φ n n ≤ -1 / (1 + φ) ∧ (u φ n n = -1 / (1 + φ) ↔ n = 1) := by
  have h1 : (0 : ℝ) < 1 + φ := by linarith
  set x := n ^ (1 + φ) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hn _
  have hlog : Real.log n = Real.log x / (1 + φ) := by
    rw [hx, Real.log_rpow hn]; field_simp
  have hu : u φ n n = (Real.log x - x) / (1 + φ) := by
    rw [u, hlog, ← hx]; ring
  have hx1 : x = 1 ↔ n = 1 := by
    constructor
    · intro h
      rw [← Real.rpow_rpow_inv hn.le h1.ne', ← hx, h, Real.one_rpow]
    · intro h; rw [hx, h, Real.one_rpow]
  rw [hu]
  refine ⟨?_, ?_⟩
  · rw [div_le_div_iff_of_pos_right h1]
    linarith [Real.log_le_sub_one_of_pos hxpos]
  · rw [← hx1]
    constructor
    · intro h
      by_contra hne
      have := Real.log_lt_sub_one_of_pos hxpos hne
      have h2 : Real.log x - x = -1 := by
        field_simp at h; linarith
      linarith
    · intro h; rw [h, Real.log_one]; ring

/-- Galí (2015), Ex. 2.8(c) (**infinite horizon**): lifetime welfare of a stationary allocation
is `∑ βᵗ u(N, N) = u(N, N)/(1 − β)`. -/
theorem hasSum_welfare (hβ0 : 0 ≤ β) (hβ1 : β < 1) (n : ℝ) :
    HasSum (fun t : ℕ => β ^ t * u φ n n) (u φ n n / (1 - β)) := by
  have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right (u φ n n)
  rw [div_eq_mul_inv, mul_comm]
  exact this

/-- Galí (2015), Ex. 2.8(c), p. 50 (**optimal inflation**): among money growth rates with
`1 + γ ≥ β` (i.e. `Q = β/(1+γ) ≤ 1`), stationary period utility is maximal exactly when
`1 + γ = β`: gross inflation `P_{t+1}/P_t = β`, net inflation `π = β − 1`, `Q = 1` (the
Friedman rule). -/
theorem optimal_inflation (hβ : 0 < β) (hφ : 0 ≤ φ) {γ : ℝ} (hγ : β ≤ 1 + γ) :
    u φ ((β / (1 + γ)) ^ (1 + φ)⁻¹) ((β / (1 + γ)) ^ (1 + φ)⁻¹) ≤
        u φ ((β / (1 + (β - 1))) ^ (1 + φ)⁻¹) ((β / (1 + (β - 1))) ^ (1 + φ)⁻¹) ∧
      (u φ ((β / (1 + γ)) ^ (1 + φ)⁻¹) ((β / (1 + γ)) ^ (1 + φ)⁻¹) =
          u φ ((β / (1 + (β - 1))) ^ (1 + φ)⁻¹) ((β / (1 + (β - 1))) ^ (1 + φ)⁻¹) ↔
        1 + γ = β) := by
  have hγ0 : 0 < 1 + γ := by linarith
  have hstar : (β / (1 + (β - 1))) ^ (1 + φ)⁻¹ = 1 := by
    rw [show 1 + (β - 1) = β by ring, div_self hβ.ne', Real.one_rpow]
  have hpos : 0 < (β / (1 + γ)) ^ (1 + φ)⁻¹ := Real.rpow_pos_of_pos (div_pos hβ hγ0) _
  have hval : u φ 1 1 = -1 / (1 + φ) := by
    rw [u, Real.log_one, Real.one_rpow]; ring
  obtain ⟨hle, hiff⟩ := stationary_utility_le hφ hpos
  rw [hstar, hval]
  refine ⟨hle, ?_⟩
  rw [hiff]
  constructor
  · intro h
    have h2 := congrArg (fun x : ℝ => x ^ (1 + φ)) h
    simp only [Real.one_rpow] at h2
    rw [Real.rpow_inv_rpow (div_pos hβ hγ0).le (by linarith), div_eq_one_iff_eq hγ0.ne'] at h2
    exact h2.symm
  · intro h
    rw [h, div_self hβ.ne', Real.one_rpow]

/-- Galí (2015), Ex. 2.8(c), p. 50: at the optimum the bond price is `Q = β/(1+γ) = 1`, i.e.
the nominal rate is zero (Friedman rule). -/
theorem friedman_at_optimum (hβ : 0 < β) {γ : ℝ} (h : 1 + γ = β) : β / (1 + γ) = 1 := by
  rw [h, div_self hβ.ne']

end Gali.ClassicalMonetaryModel.Ex2_8
