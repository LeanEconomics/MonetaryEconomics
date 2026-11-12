/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR5GaussianAR1

/-!
# The two-dimensional surplus–debt chain and Kolmogorov's 0-1 law

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197 ("So at some
point the future debt-to-GDP ratio following (6.5) will eventually exceed any bound"), with the
debt equation (6.4)–(6.5), p. 196.

Sampled at integer dates, the continuous-time OU surplus and debt (6.5) form a linear recursion
driven by two-dimensional period innovations `ξ_n = (ξ_n 0, ξ_n 1)` (the surplus innovation and
the period debt noise, correlated with each other). This module studies that recursion on the
sequence space `ℕ → Fin 2 → ℝ` under any probability measure making the coordinates
independent (not necessarily identically distributed):

* `chainU`: `u_0 = u₀`, `u_{n+1} = ρu_n + ξ_n 0` (the surplus gap `s_n − s̄`);
* `chainX`: `x_0 = x₀`, `x_{n+1} = γx_n − c₀ − c₁u_n − ξ_n 1` (the debt ratio `b_n`);
* `chainU_shift`, `chainX_shift`: restarted at `N`,
  `x_{N+k} = γ^k x_N + c₁u_N d_k + y_k(ξ_N, ξ_{N+1}, …)` with `d_k → 0`;
* **`chain_frequently`** (Kolmogorov's 0-1 law): for `|ρ| < 1`, `0 ≤ γ < 1` and any `θ`, if
  `P(θx_{n+2} > M) ≥ q_M > 0` uniformly in `n`, then almost surely `θx_n` exceeds every level
  infinitely often.
-/

namespace Cochrane.FiscalConstraints.TidyR8DebtChain

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.DebtLimitStochasticMeasure
open Cochrane.FiscalConstraints.TidyR5GaussianAR1

/-- Cochrane (2023), p. 197: the surplus gap `u_n = s_n − s̄` of the sampled chain,
`u_0 = u₀`, `u_{n+1} = ρu_n + ξ_n 0`. -/
noncomputable def chainU (ρ u0 : ℝ) : ℕ → (ℕ → Fin 2 → ℝ) → ℝ
  | 0 => fun _ => u0
  | n + 1 => fun ξ => ρ * chainU ρ u0 n ξ + ξ n 0

/-- Cochrane (2023), (6.4)–(6.5), pp. 196–197: the debt ratio of the sampled chain,
`x_0 = x₀`, `x_{n+1} = γx_n − c₀ − c₁u_n − ξ_n 1`. -/
noncomputable def chainX (ρ γ c0 c1 u0 x0 : ℝ) : ℕ → (ℕ → Fin 2 → ℝ) → ℝ
  | 0 => fun _ => x0
  | n + 1 => fun ξ => γ * chainX ρ γ c0 c1 u0 x0 n ξ - c0 - c1 * chainU ρ u0 n ξ - ξ n 1

/-- Cochrane (2023), p. 197: the innovation sequence after date `N`, `k ↦ ξ_{N+k}`. -/
def shiftSeq (N : ℕ) (ξ : ℕ → Fin 2 → ℝ) : ℕ → Fin 2 → ℝ := fun k => ξ (N + k)

/-- Cochrane (2023), p. 197: the σ-algebra of the date-`n` innovation `ξ_n`. -/
abbrev blockSigma (n : ℕ) : MeasurableSpace (ℕ → Fin 2 → ℝ) :=
  MeasurableSpace.comap (fun ξ : ℕ → Fin 2 → ℝ => ξ n) inferInstance

/-- Cochrane (2023), p. 197: the date-`n` σ-algebra is a sub-σ-algebra. -/
theorem blockSigma_le (n : ℕ) : blockSigma n ≤ MeasurableSpace.pi :=
  (measurable_pi_apply n).comap_le

/-- Cochrane (2023), p. 197: the surplus gap restarts at `N`,
`u_{N+k} = ρ^k u_N + u'_k` with `u'` the gap from `0` driven by `ξ_N, ξ_{N+1}, …`.
Restates `TidyR5GaussianAR1.ar1_shift` for the chain. -/
theorem chainU_shift (ρ u0 : ℝ) (N : ℕ) (ξ : ℕ → Fin 2 → ℝ) :
    ∀ k, chainU ρ u0 (N + k) ξ = ρ ^ k * chainU ρ u0 N ξ + chainU ρ 0 k (shiftSeq N ξ) := by
  intro k
  induction k with
  | zero => simp [chainU]
  | succ k ih =>
    rw [← add_assoc]
    change ρ * chainU ρ u0 (N + k) ξ + ξ (N + k) 0
      = _ + (ρ * chainU ρ 0 k (shiftSeq N ξ) + shiftSeq N ξ k 0)
    rw [ih]
    simp only [shiftSeq]
    ring

/-- Cochrane (2023), (6.4)–(6.5), p. 197: debt restarts at `N`,
`x_{N+k} = γ^k x_N + c₁u_N d_k + y_k`, with `d = TidyR5GaussianAR1.dseq γ ρ` and `y` the debt
from `0` driven by `ξ_N, ξ_{N+1}, …`.
Generalises `TidyR5GaussianAR1.arDebt_shift`. -/
theorem chainX_shift (ρ γ c0 c1 u0 x0 : ℝ) (N : ℕ) (ξ : ℕ → Fin 2 → ℝ) :
    ∀ k, chainX ρ γ c0 c1 u0 x0 (N + k) ξ = γ ^ k * chainX ρ γ c0 c1 u0 x0 N ξ
      + chainU ρ u0 N ξ * (c1 * dseq γ ρ k) + chainX ρ γ c0 c1 0 0 k (shiftSeq N ξ) := by
  intro k
  induction k with
  | zero => change _ = _ * _ + _ * (c1 * 0) + 0; simp
  | succ k ih =>
    rw [← add_assoc]
    change γ * chainX ρ γ c0 c1 u0 x0 (N + k) ξ - c0 - c1 * chainU ρ u0 (N + k) ξ - ξ (N + k) 1
      = _ + chainU ρ u0 N ξ * (c1 * (γ * dseq γ ρ k - ρ ^ k))
        + (γ * chainX ρ γ c0 c1 0 0 k (shiftSeq N ξ) - c0 - c1 * chainU ρ 0 k (shiftSeq N ξ)
          - shiftSeq N ξ k 1)
    rw [ih, chainU_shift ρ u0 N ξ k]
    simp only [shiftSeq]
    ring

/-- Cochrane (2023), p. 197: the surplus gap is measurable. -/
theorem measurable_chainU (ρ u0 : ℝ) : ∀ n, Measurable (chainU ρ u0 n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.const_mul ρ).add ((measurable_pi_apply 0).comp (measurable_pi_apply n))

/-- Cochrane (2023), (6.4)–(6.5): the debt ratio of the chain is measurable. -/
theorem measurable_chainX (ρ γ c0 c1 u0 x0 : ℝ) : ∀ n, Measurable (chainX ρ γ c0 c1 u0 x0 n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (((ih.const_mul γ).sub_const c0).sub ((measurable_chainU ρ u0 n).const_mul c1)).sub
      ((measurable_pi_apply 1).comp (measurable_pi_apply n))

/-- Cochrane (2023), p. 197: the innovation `ξ_{N+k}` is measurable with respect to the
innovations from date `N` on. -/
theorem measurable_shiftSeq_apply (N k : ℕ) :
    Measurable[⨆ i ≥ N, blockSigma i] (fun ξ : ℕ → Fin 2 → ℝ => shiftSeq N ξ k) :=
  Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ≥ N) => blockSigma i) (N + k) (by omega))

/-- Cochrane (2023), p. 197: the restarted gap depends only on the innovations from `N` on. -/
theorem measurable_chainU_shift (ρ : ℝ) (N : ℕ) :
    ∀ k, Measurable[⨆ i ≥ N, blockSigma i] (fun ξ => chainU ρ 0 k (shiftSeq N ξ)) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact (ih.const_mul ρ).add ((measurable_pi_apply 0).comp (measurable_shiftSeq_apply N k))

/-- Cochrane (2023), (6.4)–(6.5): the restarted debt depends only on the innovations from `N`
on. -/
theorem measurable_chainX_shift (ρ γ c0 c1 : ℝ) (N : ℕ) :
    ∀ k, Measurable[⨆ i ≥ N, blockSigma i] (fun ξ => chainX ρ γ c0 c1 0 0 k (shiftSeq N ξ)) := by
  intro k
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact (((ih.const_mul γ).sub_const c0).sub ((measurable_chainU_shift ρ N k).const_mul c1)).sub
      ((measurable_pi_apply 1).comp (measurable_shiftSeq_apply N k))

/-- **Cochrane (2023), p. 197 ("debt … will eventually exceed any bound"), the sampled chain.**
Under any probability measure making the innovations `ξ_n` independent, with `|ρ| < 1`,
`0 ≤ γ < 1` and any sign or scale `θ`: if for every level `M` the probability that `θx_{n+2}`
exceeds `M` is bounded below by some `q_M > 0` uniformly in `n`, then almost surely `θx_n`
exceeds every level infinitely often. The events are tail events (`chainX_shift`,
`TidyR5GaussianAR1.dseq_tendsto`), hence of probability one by Kolmogorov's 0-1 law.
Generalises the 0-1 argument of `TidyR5GaussianAR1.ar1_unbounded_of_integrable` to the 2-d chain. -/
theorem chain_frequently {Q : Measure (ℕ → Fin 2 → ℝ)} [IsProbabilityMeasure Q]
    (hind : iIndepFun (fun n (ξ : ℕ → Fin 2 → ℝ) => ξ n) Q) {ρ γ : ℝ} (hρ : |ρ| < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (c0 c1 u0 x0 θ : ℝ)
    (hq : ∀ M : ℝ, ∃ q : ENNReal, q ≠ 0 ∧ ∀ n,
      q ≤ Q {ξ | M < θ * chainX ρ γ c0 c1 u0 x0 (n + 2) ξ}) :
    ∀ᵐ ξ ∂Q, ∀ M : ℝ, ∃ᶠ n in atTop, M < θ * chainX ρ γ c0 c1 u0 x0 n ξ := by
  set x := chainX ρ γ c0 c1 u0 x0 with hx
  have hindep : iIndep blockSigma Q := hind.iIndep
  set E : ℝ → Set (ℕ → Fin 2 → ℝ) := fun a =>
    {ξ | ∀ m : ℕ, ∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < θ * x t ξ} with hE
  have htail : ∀ a, MeasurableSet[limsup blockSigma atTop] (E a) := by
    intro a
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro N
    set y : ℕ → (ℕ → Fin 2 → ℝ) → ℝ := fun k ξ => θ * chainX ρ γ c0 c1 0 0 k (shiftSeq N ξ)
      with hy
    have hym : ∀ k, Measurable[⨆ i ≥ N, blockSigma i] (y k) := fun k =>
      (measurable_chainX_shift ρ γ c0 c1 N k).const_mul θ
    have heq : E a = {ξ | ∀ m : ℕ, ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < y k ξ} := by
      ext ξ
      simp only [hE, Set.mem_ofPred_eq]
      have hshift : ∀ m : ℕ, (∃ᶠ t in atTop, a - 1 / ((m : ℝ) + 1) < θ * x t ξ) ↔
          ∃ᶠ k in atTop, a - 1 / ((m : ℝ) + 1) < θ * x (N + k) ξ :=
        fun m => frequently_shift_iff N
      simp only [hshift]
      have hdiff : Tendsto (fun k => θ * x (N + k) ξ - y k ξ) atTop (𝓝 0) := by
        have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (θ * x N ξ)
        have h2 := ((dseq_tendsto hγ0 hγ1 hρ).const_mul (θ * chainU ρ u0 N ξ * c1))
        rw [zero_mul] at h1
        rw [mul_zero] at h2
        have h3 := h1.add h2
        rw [add_zero] at h3
        refine h3.congr fun k => ?_
        rw [hx, chainX_shift]
        simp only [hy]
        ring
      have hdiff' : Tendsto (fun k => y k ξ - θ * x (N + k) ξ) atTop (𝓝 0) := by
        have := hdiff.neg
        rw [neg_zero] at this
        refine this.congr fun k => ?_
        ring
      exact ⟨fun h m => frequently_near_of_tendsto hdiff h m,
        fun h m => frequently_near_of_tendsto hdiff' h m⟩
    rw [heq]
    exact measurableSet_frequently_near hym a
  have hpos : ∀ a, Q (E a) ≠ 0 := by
    intro a
    obtain ⟨q, hq0, hqa⟩ := hq a
    have hfreq := le_measure_frequently (μ := Q) (A := fun t => {ξ | a < θ * x t ξ})
      (fun t => measurableSet_lt measurable_const
        ((measurable_chainX ρ γ c0 c1 u0 x0 t).const_mul θ)) hqa
    have hsub : {ξ | ∃ᶠ t in atTop, ξ ∈ {ξ' | a < θ * x t ξ'}} ⊆ E a := by
      intro ξ hξ m
      refine hξ.mono fun t ht => ?_
      have : 0 < 1 / ((m : ℝ) + 1) := by positivity
      simp only [Set.mem_ofPred_eq] at ht
      linarith
    intro h0
    exact hq0 (nonpos_iff_eq_zero.1 ((hfreq.trans (measure_mono hsub)).trans_eq h0))
  have hone : ∀ n : ℕ, ∀ᵐ ξ ∂Q, ξ ∈ E n := by
    intro n
    rcases measure_zero_or_one_of_measurableSet_limsup_atTop blockSigma_le hindep (htail n) with
      h | h
    · exact absurd h (hpos n)
    · have hm : MeasurableSet (E n) :=
        (limsup_le_iSup.trans (iSup_le blockSigma_le)) _ (htail n)
      rw [ae_iff]
      have := (prob_compl_eq_zero_iff hm).2 h
      simpa [Set.compl_def] using this
  filter_upwards [ae_all_iff.2 hone] with ξ hξ M
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  refine (hξ n 0).mono fun t ht => ?_
  simp only [CharP.cast_eq_zero, zero_add, div_one] at ht
  linarith

end Cochrane.FiscalConstraints.TidyR8DebtChain
