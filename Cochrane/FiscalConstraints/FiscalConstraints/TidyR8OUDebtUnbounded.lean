/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.TidyR7OUSampled
import FiscalConstraints.TidyR8OURestart
import FiscalConstraints.TidyR8DebtChain

/-!
# Continuous-time debt (6.5) with an OU surplus is almost surely unbounded when `r < g`

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, p. 197: "Suppose we
generate the surplus by an AR(1) … An AR(1) ranges over the entire real line, as does the
integral of an AR(1) (6.5). So at some point the future debt-to-GDP ratio following (6.5) will
eventually exceed any bound." Debt follows (6.4) `ḃ = ab − s` with corrected (6.5)
`b_t = e^{at}b_0 − ∫_0^t e^{a(t−u)}s_u du` (`TidyR7OrnsteinUhlenbeck.ouDebtProc`), `a = r − g`.

The route: at integer dates `(s_n − s̄, b_n)` is the two-dimensional chain of TidyR8DebtChain,
`s_{n+1} − s̄ = e^{−η}(s_n − s̄) + ε_{n+1}`,
`b_{n+1} = e^a b_n − s̄A − D(s_n − s̄) − ζ_{n+1}` (`ouProc_sampled_eq_chainU`,
`ouDebtProc_sampled_eq_chainX`), whose period innovations `(ε_{n+1}, ζ_{n+1})` (`ouBlock`) are
Wiener integrals over `[n, n + 1]`. They are jointly Gaussian (`isGaussianProcess_ouBlock`),
uncorrelated across periods (`covariance_ouBlock`), hence independent (`iIndepFun_ouBlock`). The
Gaussian law of `b_t` (`TidyR7OrnsteinUhlenbeck.ouDebtProc_hasLaw`) with bounded mean
(`TidyR8OURestart.abs_debtMean_le`) and variance at least the one-period variance
(`TidyR8OURestart.integral_debtG_sq_le`) gives uniform probabilities (`prob_debt_gt_ge`,
`prob_debt_lt_ge`), and Kolmogorov's 0-1 law (`TidyR8DebtChain.chain_frequently`) does the rest.

## Main results (`a = r − g < 0`, `η > 0`, `σ ≠ 0`, every `s̄`, `s_0`, `b_0`)

* **`ouDebtProc_frequently_gt`, `ouDebtProc_frequently_lt`**: almost surely debt exceeds every
  level, and falls below every level, at arbitrarily late dates (already at integer dates:
  `sampled_ouDebtProc_frequently`);
* **`ouDebtProc_sup_inf`**: almost surely `sup_{t ≥ 0} b_t = +∞` and `inf_{t ≥ 0} b_t = −∞`;
* **`ouDebtProc_ae_not_sustainable`**: for every debt limit `M`,
  `P(b_t ≤ M for all t ≥ 0) = 0` (the a.s. form of `ouDebtProc_not_sustainable`);
* non-vacuity on bmPath with `r − g = −1%`, `η = σ = 1`: `bmPath_ouDebt_sup_inf`,
  `bmPath_ouDebt_ae_not_sustainable`.

The boundary `r = g` is TidyR8OUDebtRgEqual; for `r > g` the claim fails (TidyR8OUDebtExplosive).
-/

namespace Cochrane.FiscalConstraints.TidyR8OUDebtUnbounded

open Real MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.FiscalConstraints.TidyR7OUPath Cochrane.FiscalConstraints.TidyR7WienerGaussian
open Cochrane.FiscalConstraints.TidyR7OrnsteinUhlenbeck Cochrane.FiscalConstraints.TidyR7OUSampled
open Cochrane.FiscalConstraints.TidyR7BrownianTools
open Cochrane.FiscalConstraints.TidyR8OURestart Cochrane.FiscalConstraints.TidyR8DebtChain
open scoped ENNReal NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-! ### The period innovations -/

/-- Cochrane (2023), p. 197: the Wiener integrands of the period-`n` innovations on
`[n, n + 1]`: `e^{ηu}` for the surplus, `G_1(u − n)` for the debt. -/
noncomputable def blockH (a η : ℝ) (n : ℕ) (i : Fin 2) : ℝ → ℝ :=
  if i = 0 then fun u => exp (η * u) else fun u => debtG a η 1 (u - n)

/-- Cochrane (2023), p. 197: the derivatives of the integrands `blockH`. -/
noncomputable def blockH' (a η : ℝ) (n : ℕ) (i : Fin 2) : ℝ → ℝ :=
  if i = 0 then fun u => exp (η * u) * η else fun u => -debtKernel a η 1 (u - n)

/-- Cochrane (2023), p. 197: the scale factors of the period-`n` innovations. -/
noncomputable def blockC (η σ : ℝ) (n : ℕ) (i : Fin 2) : ℝ :=
  if i = 0 then σ * exp (-η * ((n : ℝ) + 1)) else σ

/-- Cochrane (2023), (6.5), p. 197: the period-`n` innovation pair `(ε_{n+1}, ζ_{n+1})` of the
sampled surplus and debt, as Wiener integrals over `[n, n + 1]`. -/
noncomputable def ouBlock (a η σ : ℝ) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) (i : Fin 2) : ℝ :=
  blockC η σ n i * wienerBP W (blockH a η n i) (blockH' a η n i) n ((n : ℝ) + 1) ω

/-- Cochrane (2023), p. 197: `blockH' ` is the derivative of `blockH`. -/
theorem hasDerivAt_blockH (a η : ℝ) (n : ℕ) (i : Fin 2) (x : ℝ) :
    HasDerivAt (blockH a η n i) (blockH' a η n i x) x := by
  by_cases hi : i = 0
  · simp only [blockH, blockH', hi, ↓reduceIte]
    exact hasDerivAt_expMul η x
  · simp only [blockH, blockH', hi, ↓reduceIte]
    exact (hasDerivAt_debtG a η 1 (x - n)).comp_sub_const x n

/-- Cochrane (2023), p. 197: the derivatives `blockH'` are continuous. -/
theorem continuous_blockH' (a η : ℝ) (n : ℕ) (i : Fin 2) : Continuous (blockH' a η n i) := by
  by_cases hi : i = 0
  · simp only [blockH', hi, ↓reduceIte]
    fun_prop
  · simp only [blockH', hi, ↓reduceIte]
    exact ((continuous_debtKernel a η 1).comp (continuous_id.sub continuous_const)).neg

/-- Cochrane (2023), p. 197: the first coordinate is the OU innovation `ε_{n+1}`
(`TidyR7OUSampled.ouInnov`). -/
theorem ouBlock_zero (a η σ : ℝ) (n : ℕ) (ω : Ω) : ouBlock a η σ W n ω 0 = ouInnov η σ W n ω := by
  rw [ouInnov_eq]
  simp only [ouBlock, blockC, blockH, blockH', ↓reduceIte]

/-- Cochrane (2023), (6.5), p. 197: the second coordinate is the period debt noise
`ζ_{n+1} = σ∫_0^1 w^n(r)k_1(r)dr` of `TidyR8OURestart.ouDebt_succ`. -/
theorem ouBlock_one (a η σ : ℝ) (hcont : ∀ ω, Continuous fun t => W t ω) (n : ℕ) (ω : Ω) :
    ouBlock a η σ W n ω 1 = σ * ∫ r in (0 : ℝ)..1,
      shiftPath (fun u => bmReal W u ω) n r * debtKernel a η 1 r := by
  rw [shift_integral_eq a η (continuous_bmReal (hcont ω)) n]
  simp only [ouBlock, blockC, blockH, blockH', one_ne_zero, ↓reduceIte, wienerBP]

/-- Cochrane (2023), p. 197: each innovation coordinate is square integrable.
Generalises `TidyR7OUSampled.memLp_ouInnov` to the pair of period innovations. -/
theorem memLp_ouBlock (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ) (n : ℕ) (i : Fin 2) :
    MemLp (fun ω => ouBlock a η σ W n ω i) 2 P :=
  (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_blockH a η n i) (continuous_blockH' a η n i)
    (Nat.cast_nonneg n) (by linarith : (n : ℝ) < n + 1)).const_mul _

/-- Cochrane (2023), p. 197: each innovation coordinate is almost everywhere measurable.
Generalises `TidyR7OUSampled.aemeasurable_ouInnov` to the pair of period innovations. -/
theorem aemeasurable_ouBlock (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ) (n : ℕ) (i : Fin 2) :
    AEMeasurable (fun ω => ouBlock a η σ W n ω i) P :=
  (memLp_ouBlock hB hW hcont a η σ n i).aestronglyMeasurable.aemeasurable

/-- Cochrane (2023), p. 197: the innovations have mean zero.
Generalises `TidyR7OUSampled.integral_ouInnov` to the pair of period innovations. -/
theorem integral_ouBlock (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ) (n : ℕ) (i : Fin 2) :
    ∫ ω, ouBlock a η σ W n ω i ∂P = 0 := by
  have hm := (memLp_wienerBP (P := P) hB hW hcont (hasDerivAt_blockH a η n i)
    (continuous_blockH' a η n i) (Nat.cast_nonneg n) (by linarith : (n : ℝ) < n + 1))
    |>.aestronglyMeasurable
    |>.aemeasurable
  have hlaw := map_wienerBP (P := P) hB hW hcont (hasDerivAt_blockH a η n i)
    (continuous_blockH' a η n i) (Nat.cast_nonneg n) (by linarith : (n : ℝ) < n + 1)
  simp only [ouBlock]
  rw [integral_const_mul, show ∫ ω, wienerBP W (blockH a η n i) (blockH' a η n i) n
      ((n : ℝ) + 1) ω ∂P = ∫ x, x ∂(P.map (wienerBP W (blockH a η n i) (blockH' a η n i) n
        ((n : ℝ) + 1))) from (integral_map hm aestronglyMeasurable_id).symm, hlaw,
    integral_id_gaussianReal, mul_zero]

/-- **Cochrane (2023), p. 197: the innovations of different periods are uncorrelated.**
Generalises `TidyR7OUSampled.covariance_ouInnov` to the pair of period innovations. -/
theorem covariance_ouBlock (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ) {m n : ℕ} (hmn : m ≠ n)
    (i j : Fin 2) :
    cov[fun ω => ouBlock a η σ W m ω i, fun ω => ouBlock a η σ W n ω j; P] = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have key : ∀ (m n : ℕ) (i j : Fin 2), m < n →
      ∫ ω, ouBlock a η σ W m ω i * ouBlock a η σ W n ω j ∂P = 0 := by
    intro m n i j hlt
    have h0 := integral_mul_wienerBP_eq_zero (P := P) hB hW hcont (hasDerivAt_blockH a η m i)
      (continuous_blockH' a η m i) (hasDerivAt_blockH a η n j) (continuous_blockH' a η n j)
      (Nat.cast_nonneg m) (by linarith : (m : ℝ) < m + 1)
      (by exact_mod_cast hlt : (m : ℝ) + 1 ≤ n) (by linarith : (n : ℝ) < n + 1)
    simp only [ouBlock]
    have e : ∀ ω, blockC η σ m i * wienerBP W (blockH a η m i) (blockH' a η m i) m (m + 1) ω
        * (blockC η σ n j * wienerBP W (blockH a η n j) (blockH' a η n j) n (n + 1) ω)
        = (blockC η σ m i * blockC η σ n j)
          * (wienerBP W (blockH a η m i) (blockH' a η m i) m (m + 1) ω
            * wienerBP W (blockH a η n j) (blockH' a η n j) n (n + 1) ω) := fun ω => by ring
    simp_rw [e]
    rw [integral_const_mul, h0, mul_zero]
  rw [covariance_eq_sub (memLp_ouBlock hB hW hcont a η σ m i)
    (memLp_ouBlock hB hW hcont a η σ n j), integral_ouBlock hB hW hcont a η σ m i,
    integral_ouBlock hB hW hcont a η σ n j, mul_zero, sub_zero]
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · exact key m n i j hlt
  · have := key n m j i hlt
    simp_rw [mul_comm (ouBlock a η σ W n _ j)] at this
    exact this

/-- **Cochrane (2023), p. 197: the innovations are jointly Gaussian** (finite linear
combinations of Wiener integrals, `TidyR7WienerGaussian.exists_map_sum_wienerBP`).
Generalises `TidyR7OUSampled.isGaussianProcess_ouInnov` to the pair of period innovations. -/
theorem isGaussianProcess_ouBlock (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ) :
    IsGaussianProcess (fun (p : (_ : ℕ) × Fin 2) ω => ouBlock a η σ W p.1 ω p.2) P where
  hasGaussianLaw I := by
    have hV : AEMeasurable (fun ω => I.restrict
        (fun p : (_ : ℕ) × Fin 2 => ouBlock a η σ W p.1 ω p.2)) P :=
      AEMeasurable.of_eval fun i => aemeasurable_ouBlock hB hW hcont a η σ i.1.1 i.1.2
    refine ⟨hV, isGaussian_of_map_eq_gaussianReal fun L => ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hV]
    set d : I → ℝ := fun i => L (fun j => if i = j then 1 else 0)
      * blockC η σ (i : (_ : ℕ) × Fin 2).1 (i : (_ : ℕ) × Fin 2).2
    obtain ⟨v, hv⟩ := exists_map_sum_wienerBP (P := P) hB hW hcont Finset.univ d
      (h := fun i => blockH a η (i : (_ : ℕ) × Fin 2).1 (i : (_ : ℕ) × Fin 2).2)
      (h' := fun i => blockH' a η (i : (_ : ℕ) × Fin 2).1 (i : (_ : ℕ) × Fin 2).2)
      (fun i => hasDerivAt_blockH a η _ _) (fun i => continuous_blockH' a η _ _)
      (s := fun i => ((i : (_ : ℕ) × Fin 2).1 : ℝ))
      (t := fun i => ((i : (_ : ℕ) × Fin 2).1 : ℝ) + 1) (fun _ => by linarith)
    refine ⟨0, v, ?_⟩
    rw [← hv]
    congr 1
    funext ω
    simp only [Function.comp_apply]
    rw [show L (I.restrict fun p : (_ : ℕ) × Fin 2 => ouBlock a η σ W p.1 ω p.2)
      = L.toLinearMap (I.restrict fun p : (_ : ℕ) × Fin 2 => ouBlock a η σ W p.1 ω p.2) from rfl,
      LinearMap.pi_apply_eq_sum_univ]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.restrict, smul_eq_mul, d, ouBlock, ContinuousLinearMap.coe_coe]
    ring

/-- **Cochrane (2023), p. 197: the period innovation pairs are independent across periods.**
Jointly Gaussian and uncorrelated
(`ProbabilityTheory.IsGaussianProcess.iIndepFun_of_covariance_eq_zero`).
Generalises `TidyR7OUSampled.iIndepFun_ouInnov` to the pair of period innovations. -/
theorem iIndepFun_ouBlock (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (a η σ : ℝ) :
    iIndepFun (fun n ω => ouBlock a η σ W n ω) P :=
  IsGaussianProcess.iIndepFun_of_covariance_eq_zero
    (X := fun (n : ℕ) (i : Fin 2) ω => ouBlock a η σ W n ω i)
    (isGaussianProcess_ouBlock hB hW hcont a η σ)
    (fun n i => aemeasurable_ouBlock hB hW hcont a η σ n i)
    (fun _ _ hmn i j => covariance_ouBlock hB hW hcont a η σ hmn i j)

/-! ### The sampled surplus and debt are the chain -/

/-- Cochrane (2023), p. 197: path by path, the sampled surplus gap is the chain gap,
`s_n − s̄ = u_n(ε, ζ)` with `ρ = e^{−η}`, `u_0 = s_0 − s̄`.
`TidyR7OUSampled.ouProc_succ` iterated into the chain form. -/
theorem ouProc_sampled_eq_chainU (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (a η sbar s0 σ : ℝ) (ω : Ω) :
    ∀ n : ℕ, chainU (exp (-η)) (s0 - sbar) n (fun k => ouBlock a η σ W k ω)
      = ouProc η sbar s0 σ W n ω - sbar := by
  intro n
  induction n with
  | zero => simp [chainU, ouProc_zero hW0]
  | succ n ih =>
    change exp (-η) * chainU (exp (-η)) (s0 - sbar) n (fun k => ouBlock a η σ W k ω)
      + ouBlock a η σ W n ω 0 = _
    rw [ih, ouBlock_zero, Nat.cast_succ, ouProc_succ hcont η sbar s0 σ n ω]

/-- **Cochrane (2023), (6.4)–(6.5), pp. 196–197: path by path, the sampled debt is the chain
debt**, `b_n = x_n(ε, ζ)` with `γ = e^a`, `c₀ = s̄A`, `c₁ = D`, `x_0 = b_0`. -/
theorem ouDebtProc_sampled_eq_chainX (hcont : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (a η sbar s0 σ b0 : ℝ) (ω : Ω) :
    ∀ n : ℕ, chainX (exp (-η)) (exp a) (sbar * debtA a) (debtD a η) (s0 - sbar) b0 n
      (fun k => ouBlock a η σ W k ω) = ouDebtProc a η sbar s0 σ b0 W n ω := by
  intro n
  induction n with
  | zero =>
    change b0 = ouDebt a η sbar s0 σ b0 _ ((0 : ℕ) : ℝ)
    rw [Nat.cast_zero, ouDebt_zero]
  | succ n ih =>
    change exp a * chainX (exp (-η)) (exp a) (sbar * debtA a) (debtD a η) (s0 - sbar) b0 n
        (fun k => ouBlock a η σ W k ω) - sbar * debtA a
      - debtD a η * chainU (exp (-η)) (s0 - sbar) n (fun k => ouBlock a η σ W k ω)
      - ouBlock a η σ W n ω 1 = _
    rw [ih, ouProc_sampled_eq_chainU hcont hW0 a η sbar s0 σ ω n, ouBlock_one a η σ hcont,
      Nat.cast_succ]
    simp only [ouDebtProc, ouProc]
    rw [ouDebt_succ a η sbar s0 σ b0 (continuous_bmReal (hcont ω)) n]

/-! ### Uniform probabilities from the Gaussian law -/

/-- Cochrane (2023), p. 197 (tool): if `|m| ≤ C` and `v ≥ v₁ > 0`, then
`N(m, v)(M, ∞) ≥ N(0, 1)(K, ∞)` with `K = (|M| + C)/√v₁`, uniformly in `m` and `v`. -/
theorem gaussianReal_Ioi_ge {m C : ℝ} (hm : |m| ≤ C) {v₁ v : ℝ≥0} (hv₁ : v₁ ≠ 0)
    (hv : v₁ ≤ v) (M : ℝ) :
    gaussianReal 0 1 (Set.Ioi ((|M| + C) / √(v₁ : ℝ))) ≤ gaussianReal m v (Set.Ioi M) := by
  have hs1 : 0 < √(v₁ : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsv : √(v₁ : ℝ) ≤ √(v : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hv)
  have hC : 0 ≤ C := (abs_nonneg m).trans hm
  rw [gaussianReal_eq_map m v, Measure.map_apply (by fun_prop) measurableSet_Ioi]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_Ioi, Set.mem_preimage] at hx ⊢
  have hK : 0 ≤ (|M| + C) / √(v₁ : ℝ) := div_nonneg (by positivity) hs1.le
  have h1 : |M| + C < √(v₁ : ℝ) * x := by
    have := mul_lt_mul_of_pos_left hx hs1
    rwa [mul_div_cancel₀ _ hs1.ne'] at this
  have h2 : √(v₁ : ℝ) * x ≤ √(v : ℝ) * x := mul_le_mul_of_nonneg_right hsv (by linarith)
  have h3 := le_abs_self M
  have h4 := neg_abs_le m
  linarith

/-- Cochrane (2023), p. 197 (tool): if `|m| ≤ C` and `v ≥ v₁ > 0`, then
`N(m, v)(−∞, −M) ≥ N(0, 1)(−∞, −K)` with `K = (|M| + C)/√v₁`. -/
theorem gaussianReal_Iio_ge {m C : ℝ} (hm : |m| ≤ C) {v₁ v : ℝ≥0} (hv₁ : v₁ ≠ 0)
    (hv : v₁ ≤ v) (M : ℝ) :
    gaussianReal 0 1 (Set.Iio (-((|M| + C) / √(v₁ : ℝ)))) ≤ gaussianReal m v (Set.Iio (-M)) := by
  have hs1 : 0 < √(v₁ : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsv : √(v₁ : ℝ) ≤ √(v : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hv)
  have hC : 0 ≤ C := (abs_nonneg m).trans hm
  rw [gaussianReal_eq_map m v, Measure.map_apply (by fun_prop) measurableSet_Iio]
  refine measure_mono fun x hx => ?_
  simp only [Set.mem_Iio, Set.mem_preimage] at hx ⊢
  have hK : 0 ≤ (|M| + C) / √(v₁ : ℝ) := div_nonneg (by positivity) hs1.le
  have h1 : √(v₁ : ℝ) * x < -(|M| + C) := by
    have := mul_lt_mul_of_pos_left hx hs1
    rwa [mul_neg, mul_div_cancel₀ _ hs1.ne'] at this
  have h2 : √(v : ℝ) * x ≤ √(v₁ : ℝ) * x := mul_le_mul_of_nonpos_right hsv (by linarith)
  have h3 := le_abs_self M
  have h4 := le_abs_self m
  linarith

/-- Cochrane (2023), (6.5), p. 197: the debt variance at `t ≥ 1` is at least the one-period
variance.
`σ²` times `TidyR8OURestart.integral_debtG_sq_le`. -/
theorem debtVar_one_le (a η σ : ℝ) {t : ℝ} (ht : 1 ≤ t) : debtVar a η σ 1 ≤ debtVar a η σ t :=
  Real.toNNReal_le_toNNReal (mul_le_mul_of_nonneg_left (integral_debtG_sq_le a η ht)
    (sq_nonneg σ))

/-- **Cochrane (2023), p. 197: with `r < g`, debt exceeds any level with probability bounded
away from zero, uniformly in the date `t ≥ 1`.** -/
theorem prob_debt_gt_ge (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η σ : ℝ} (ha : a < 0)
    (hη : 0 < η) (hσ : σ ≠ 0) (sbar s0 b0 M : ℝ) :
    ∃ q : ℝ≥0∞, q ≠ 0 ∧ ∀ t : ℝ, 1 ≤ t → q ≤ P {ω | M < ouDebtProc a η sbar s0 σ b0 W t ω} := by
  set C := |b0| + |sbar| / (-a) + |s0 - sbar| / η
  refine ⟨gaussianReal 0 1 (Set.Ioi ((|M| + C) / √(debtVar a η σ 1 : ℝ))),
    (gaussianReal_open_pos 0 one_ne_zero isOpen_Ioi Set.nonempty_Ioi).ne', fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hm := aemeasurable_ouDebtProc (P := P) hB hW hcont hW0 a η sbar s0 σ b0 ht0
  have h := Measure.map_apply_of_aemeasurable hm (measurableSet_Ioi (a := M))
  rw [ouDebtProc_hasLaw hB hW hcont hW0 a η sbar s0 σ b0 ht0] at h
  rw [show {ω | M < ouDebtProc a η sbar s0 σ b0 W t ω}
    = ouDebtProc a η sbar s0 σ b0 W t ⁻¹' Set.Ioi M from rfl, ← h]
  exact gaussianReal_Ioi_ge (abs_debtMean_le ha hη sbar s0 b0 ht0.le)
    (debtVar_ne_zero a η hσ one_pos) (debtVar_one_le a η σ ht) M

/-- **Cochrane (2023), p. 197: with `r < g`, debt falls below any level with probability
bounded away from zero, uniformly in the date `t ≥ 1`.** -/
theorem prob_debt_lt_ge (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η σ : ℝ} (ha : a < 0)
    (hη : 0 < η) (hσ : σ ≠ 0) (sbar s0 b0 M : ℝ) :
    ∃ q : ℝ≥0∞, q ≠ 0 ∧ ∀ t : ℝ, 1 ≤ t →
      q ≤ P {ω | ouDebtProc a η sbar s0 σ b0 W t ω < -M} := by
  set C := |b0| + |sbar| / (-a) + |s0 - sbar| / η
  refine ⟨gaussianReal 0 1 (Set.Iio (-((|M| + C) / √(debtVar a η σ 1 : ℝ)))),
    (gaussianReal_open_pos 0 one_ne_zero isOpen_Iio Set.nonempty_Iio).ne', fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hm := aemeasurable_ouDebtProc (P := P) hB hW hcont hW0 a η sbar s0 σ b0 ht0
  have h := Measure.map_apply_of_aemeasurable hm (measurableSet_Iio (a := -M))
  rw [ouDebtProc_hasLaw hB hW hcont hW0 a η sbar s0 σ b0 ht0] at h
  rw [show {ω | ouDebtProc a η sbar s0 σ b0 W t ω < -M}
    = ouDebtProc a η sbar s0 σ b0 W t ⁻¹' Set.Iio (-M) from rfl, ← h]
  exact gaussianReal_Iio_ge (abs_debtMean_le ha hη sbar s0 b0 ht0.le)
    (debtVar_ne_zero a η hσ one_pos) (debtVar_one_le a η σ ht) M

/-! ### Almost-sure unboundedness -/

/-- **Cochrane (2023), p. 197: debt sampled at integer dates is a.s. unbounded in both
directions when `r < g`.** For `a = r − g < 0`, `η > 0`, `σ ≠ 0` and every `s̄`, `s_0`, `b_0`,
almost surely for every level `M`, `θb_n > M` for infinitely many `n`, for `θ = 1` and `θ = −1`. -/
theorem sampled_ouDebtProc_frequently (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η σ : ℝ} (ha : a < 0)
    (hη : 0 < η) (hσ : σ ≠ 0) (sbar s0 b0 : ℝ) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, (∃ᶠ n : ℕ in atTop, M < ouDebtProc a η sbar s0 σ b0 W n ω) ∧
      ∃ᶠ n : ℕ in atTop, ouDebtProc a η sbar s0 σ b0 W n ω < -M := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set B : Ω → ℕ → Fin 2 → ℝ := fun ω n => ouBlock a η σ W n ω with hBdef
  have hBn : ∀ n, AEMeasurable (fun ω => ouBlock a η σ W n ω) P := fun n =>
    AEMeasurable.of_eval fun i => aemeasurable_ouBlock hB hW hcont a η σ n i
  have hBm : AEMeasurable B P := AEMeasurable.of_eval hBn
  have hind := iIndepFun_ouBlock hB hW hcont a η σ
  have hQ : iIndepFun (fun n (ξ : ℕ → Fin 2 → ℝ) => ξ n) (P.map B) := by
    rw [hBdef, hind.map_fun_eq_infinitePi_map₀ hBm]
    exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  set ρ := exp (-η)
  have hρ : |ρ| < 1 := by
    rw [abs_of_pos (exp_pos _)]
    exact exp_lt_one_iff.2 (by linarith)
  have hγ1 : exp a < 1 := exp_lt_one_iff.2 ha
  set x := chainX ρ (exp a) (sbar * debtA a) (debtD a η) (s0 - sbar) b0 with hx
  have hpath : ∀ ω n, x n (B ω) = ouDebtProc a η sbar s0 σ b0 W n ω := fun ω n =>
    ouDebtProc_sampled_eq_chainX hcont hW0 a η sbar s0 σ b0 ω n
  have hprob : ∀ (θ M : ℝ) (n : ℕ),
      P.map B {ξ | M < θ * x (n + 2) ξ} = P {ω | M < θ * ouDebtProc a η sbar s0 σ b0 W
        ((n + 2 : ℕ) : ℝ) ω} := by
    intro θ M n
    rw [Measure.map_apply_of_aemeasurable hBm (measurableSet_lt measurable_const
      ((measurable_chainX _ _ _ _ _ _ (n + 2)).const_mul θ))]
    congr 1
    ext ω
    change M < θ * x (n + 2) (B ω) ↔ _
    rw [hpath]
    exact Iff.rfl
  have hup := chain_frequently hQ hρ (exp_pos a).le hγ1 (sbar * debtA a) (debtD a η)
    (s0 - sbar) b0 1 fun M => by
      obtain ⟨q, hq0, hq⟩ := prob_debt_gt_ge hB hW hcont hW0 ha hη hσ sbar s0 b0 M
      refine ⟨q, hq0, fun n => ?_⟩
      rw [hprob]
      simp only [one_mul]
      exact hq ((n + 2 : ℕ) : ℝ) (by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hdown := chain_frequently hQ hρ (exp_pos a).le hγ1 (sbar * debtA a) (debtD a η)
    (s0 - sbar) b0 (-1) fun M => by
      obtain ⟨q, hq0, hq⟩ := prob_debt_lt_ge hB hW hcont hW0 ha hη hσ sbar s0 b0 M
      refine ⟨q, hq0, fun n => ?_⟩
      rw [hprob]
      have hn2 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
        push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      refine (hq ((n + 2 : ℕ) : ℝ) hn2).trans (measure_mono fun ω hω => ?_)
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith
  filter_upwards [ae_of_ae_map hBm hup, ae_of_ae_map hBm hdown] with ω h1 h2 M
  refine ⟨(h1 M).mono fun n hn => ?_, (h2 M).mono fun n hn => ?_⟩
  · have e := hpath ω n
    change M < 1 * x n (B ω) at hn
    linarith
  · have e := hpath ω n
    change M < -1 * x n (B ω) at hn
    linarith

/-- Cochrane (2023), p. 197 (tool): a property holding at infinitely many integer dates holds
at arbitrarily late real dates.
From Mathlib `Filter.Tendsto.frequently` and `tendsto_natCast_atTop_atTop`. -/
theorem frequently_real_of_nat {p : ℝ → Prop} (h : ∃ᶠ n : ℕ in atTop, p n) :
    ∃ᶠ t : ℝ in atTop, p t := by
  rw [frequently_atTop] at h ⊢
  intro T
  obtain ⟨n, hn, hp⟩ := h ⌈T⌉₊
  exact ⟨n, (Nat.le_ceil T).trans (by exact_mod_cast hn), hp⟩

/-- **Cochrane (2023), p. 197: "the future debt-to-GDP ratio following (6.5) will eventually
exceed any bound", almost surely, in continuous time.** For `a = r − g < 0`, `η > 0`, `σ ≠ 0`
and every `s̄`, `s_0`, `b_0`: almost surely, for every level `M`, debt exceeds `M` at
arbitrarily late dates. -/
theorem ouDebtProc_frequently_gt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η σ : ℝ} (ha : a < 0)
    (hη : 0 < η) (hσ : σ ≠ 0) (sbar s0 b0 : ℝ) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ t in atTop, M < ouDebtProc a η sbar s0 σ b0 W t ω := by
  filter_upwards [sampled_ouDebtProc_frequently hB hW hcont hW0 ha hη hσ sbar s0 b0] with ω h M
  exact frequently_real_of_nat (h M).1

/-- **Cochrane (2023), p. 197: debt also falls below every bound, almost surely**, at
arbitrarily late dates (`a = r − g < 0`, `η > 0`, `σ ≠ 0`, every `s̄`, `s_0`, `b_0`). -/
theorem ouDebtProc_frequently_lt (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η σ : ℝ} (ha : a < 0)
    (hη : 0 < η) (hσ : σ ≠ 0) (sbar s0 b0 : ℝ) :
    ∀ᵐ ω ∂P, ∀ M : ℝ, ∃ᶠ t in atTop, ouDebtProc a η sbar s0 σ b0 W t ω < M := by
  filter_upwards [sampled_ouDebtProc_frequently hB hW hcont hW0 ha hη hσ sbar s0 b0] with ω h M
  exact frequently_real_of_nat (p := fun t => ouDebtProc a η sbar s0 σ b0 W t ω < M)
    (by simpa only [neg_neg] using (h (-M)).2)

/-- **Cochrane (2023), p. 197: almost surely `sup_{t ≥ 0} b_t = +∞` and `inf_{t ≥ 0} b_t = −∞`**
(`a = r − g < 0`, `η > 0`, `σ ≠ 0`, every `s̄`, `s_0`, `b_0`). -/
theorem ouDebtProc_sup_inf (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η σ : ℝ} (ha : a < 0)
    (hη : 0 < η) (hσ : σ ≠ 0) (sbar s0 b0 : ℝ) :
    ∀ᵐ ω ∂P, ¬ BddAbove ((fun t => ouDebtProc a η sbar s0 σ b0 W t ω) '' Set.Ici 0) ∧
      ¬ BddBelow ((fun t => ouDebtProc a η sbar s0 σ b0 W t ω) '' Set.Ici 0) := by
  filter_upwards [ouDebtProc_frequently_gt hB hW hcont hW0 ha hη hσ sbar s0 b0,
    ouDebtProc_frequently_lt hB hW hcont hW0 ha hη hσ sbar s0 b0] with ω h1 h2
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨t, ht1, ht2⟩ := ((h1 M).and_eventually (eventually_ge_atTop 0)).exists
    exact absurd (hM ⟨t, ht2, rfl⟩) (not_le.2 ht1)
  · rintro ⟨M, hM⟩
    obtain ⟨t, ht1, ht2⟩ := ((h2 M).and_eventually (eventually_ge_atTop 0)).exists
    exact absurd (hM ⟨t, ht2, rfl⟩) (not_le.2 ht1)

/-- **Cochrane (2023), p. 197: "the initial value of debt `b_0/y_0` in (6.5) is not
sustainable", almost surely.** For `r < g` and every debt limit `M`, the probability that debt
never exceeds `M` is zero (strengthening `TidyR7OrnsteinUhlenbeck.ouDebtProc_not_sustainable`,
which gives `< 1`). -/
theorem ouDebtProc_ae_not_sustainable (hB : IsPreBrownianReal W P) (hW : ∀ t, Measurable (W t))
    (hcont : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0) {a η σ : ℝ} (ha : a < 0)
    (hη : 0 < η) (hσ : σ ≠ 0) (sbar s0 b0 M : ℝ) :
    P {ω | ∀ t, 0 ≤ t → ouDebtProc a η sbar s0 σ b0 W t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ouDebtProc_sup_inf hB hW hcont hW0 ha hη hσ sbar s0 b0] with ω h hall
  exact h.1 ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact hall t ht⟩

/-! ### Non-vacuity on the constructed Brownian motion -/

open Cochrane.FiscalConstraints.TidyR7BrownianExist
open Cochrane.FiscalConstraints.TidyR7BrownianSchauder

/-- Cochrane (2023), p. 197 (non-vacuity): on bmPath, with `r − g = −1%` and `η = σ = 1`, almost
surely debt has `sup = +∞` and `inf = −∞`, for every `s̄`, `s_0`, `b_0`. -/
theorem bmPath_ouDebt_sup_inf (sbar s0 b0 : ℝ) :
    ∀ᵐ ω ∂gaussSeq,
      ¬ BddAbove ((fun t => ouDebtProc (-1 / 100) 1 sbar s0 1 b0 bmPath t ω) '' Set.Ici 0) ∧
      ¬ BddBelow ((fun t => ouDebtProc (-1 / 100) 1 sbar s0 1 b0 bmPath t ω) '' Set.Ici 0) :=
  ouDebtProc_sup_inf isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath bmPath_zero
    (by norm_num) one_pos one_ne_zero sbar s0 b0

/-- Cochrane (2023), p. 197 (non-vacuity): on bmPath, with `r − g = −1%` and `η = σ = 1`, every
debt limit is violated almost surely. -/
theorem bmPath_ouDebt_ae_not_sustainable (sbar s0 b0 M : ℝ) :
    gaussSeq {ω | ∀ t, 0 ≤ t → ouDebtProc (-1 / 100) 1 sbar s0 1 b0 bmPath t ω ≤ M} = 0 :=
  ouDebtProc_ae_not_sustainable isPreBrownianReal_bmPath measurable_bmPath continuous_bmPath
    bmPath_zero (by norm_num) one_pos one_ne_zero sbar s0 b0 M

end Cochrane.FiscalConstraints.TidyR8OUDebtUnbounded
