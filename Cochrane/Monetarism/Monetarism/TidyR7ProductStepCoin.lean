/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR7ProductStep
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Distributions.Uniform

/-!
# Non-vacuity of the product step of (1.32): a fair coin revealed at time 1

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1, §1.6, "Money in
continuous time", pp. 567–568, eqs. (1.31)–(1.34). A concrete realisation of
`TidyR7ProductStep.ProductStepData` with a NONZERO martingale part and RANDOM bonds, on which both
sides of the product step `TidyR7ProductStep.ProductStepData.product_step` are computed exactly.

## The realisation

`Ω = Bool` with the fair coin `coinMeasure` (`PMF.uniformOfFintype Bool`), `ξ = ±1` (`coinXi`),
revealed at time `1`: `coinFiltration u` is trivial for `u < 1` and everything for `u ≥ 1`.
On `[0, 2]`:
* `M_u = ξ·1{u ≥ 1}` (`coinM`): a càdlàg martingale (`martingale_coinM`), not zero;
* `A = 0`, so `X = M`;
* `B_u = 1 + ξ·(u − 1)⁺` (`coinB`): adapted, continuous, of bounded variation, random.

## Results

* `coinData`: the hypotheses of the product step hold.
* `coin_lhs`: `E_0[B_2X_2 − B_0X_0] = 1`; `coin_intXB`: `∫_0^2 X dB = ξ² = 1` path by path, so
  `E_0[∫X dB] = 1`; `coin_intBA`: `∫_0^2 B dA = 0`. `coin_headline`: both sides computed,
  `1 = 1 + 0`, and the headline indeed holds.
* `coin_sumBM`: for EVERY partition of `[0, 2]`, `Σ B_iΔM_i = ξ` path by path (never `0`), while
  `E_0[Σ B_iΔM_i] = 0` (`coin_condExp_sumBM`): the martingale term vanishes only in conditional
  expectation. Likewise `Σ B_iΔX_i = ξ` pathwise, while `B·E_0 dX = E_0[∫B dA] = 0`
  (`coin_expIncr`).
* **Adaptedness of `B` is needed**: with the anticipating `B = ξ` (`coinBAnt`, continuous, of
  bounded variation, not adapted: `not_adapted_coinBAnt`) the conclusion fails,
  `E_0[B_2X_2 − B_0X_0] = 1 ≠ 0 = E_0[∫X dB] + E_0[∫B dA]` (`coin_anticipating_fails`), because
  `E_0[Σ B_iΔM_i] = 1` (`coin_anticipating_sumBM`).
-/

namespace Cochrane.Monetarism.TidyR7ProductStepCoin

open MeasureTheory Filter Topology
open Cochrane.Monetarism.TidyR7StieltjesIntegral Cochrane.Monetarism.TidyR7StieltjesSums
  Cochrane.Monetarism.TidyR7ProductStep

/-- Cochrane (2023), A1 §1.6, p. 567 (non-vacuity of (1.32)): the fair coin on `Bool`. -/
noncomputable abbrev coinMeasure : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- Cochrane (2023), A1 §1.6, p. 567: the coin `ξ = ±1`. -/
def coinXi (ω : Bool) : ℝ := if ω then 1 else -1

/-- Cochrane (2023), A1 §1.6, p. 567: the filtration revealing the coin at time `1`. -/
noncomputable def coinFiltration : Filtration ℝ (inferInstance : MeasurableSpace Bool) where
  seq u := if u < 1 then ⊥ else inferInstance
  mono' i j hij := by
    by_cases hj : j < 1
    · have hi : i < 1 := lt_of_le_of_lt hij hj
      simp only [hi, hj, ↓reduceIte, le_refl]
    · by_cases hi : i < 1
      · simp only [hi, hj, ↓reduceIte]
        exact bot_le
      · simp only [hi, hj, ↓reduceIte, le_refl]
  le' u := by
    by_cases hu : u < 1
    · simp only [hu, ↓reduceIte]
      exact bot_le
    · simp only [hu, ↓reduceIte, le_refl]

/-- Cochrane (2023), A1 §1.6, p. 567: the martingale part `M_u = ξ·1{u ≥ 1}`. -/
noncomputable def coinM (u : ℝ) (ω : Bool) : ℝ := coinXi ω * heaviside u

/-- Cochrane (2023), A1 §1.6, p. 567: the bonds `B_u = 1 + ξ·(u − 1)⁺`. -/
noncomputable def coinB (u : ℝ) (ω : Bool) : ℝ := 1 + coinXi ω * max (u - 1) 0

/-- Cochrane (2023), A1 §1.6, p. 567: the finite-variation part `A = 0`. -/
def coinA (_ : ℝ) (_ : Bool) : ℝ := 0

/-- Cochrane (2023), A1 §1.6, p. 567: before time `1` the filtration is trivial. -/
theorem coinFiltration_lt {u : ℝ} (hu : u < 1) : coinFiltration u = ⊥ := by
  change (if u < 1 then ⊥ else (inferInstance : MeasurableSpace Bool)) = _
  simp only [hu, ↓reduceIte]

/-- Cochrane (2023), A1 §1.6, p. 567: from time `1` on the filtration is everything. -/
theorem coinFiltration_ge {u : ℝ} (hu : 1 ≤ u) :
    coinFiltration u = (inferInstance : MeasurableSpace Bool) := by
  change (if u < 1 then ⊥ else (inferInstance : MeasurableSpace Bool)) = _
  simp only [not_lt.2 hu, ↓reduceIte]

/-- Cochrane (2023), A1 §1.6, p. 567: the expectation under the fair coin is the average.
Mathlib `PMF.integral_eq_sum` for the uniform PMF. -/
theorem integral_coin (f : Bool → ℝ) : ∫ ω, f ω ∂coinMeasure = (f true + f false) / 2 := by
  rw [coinMeasure, PMF.integral_eq_sum]
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, PMF.uniformOfFintype_apply, Fintype.card_bool,
    smul_eq_mul, ENNReal.toReal_inv]
  norm_num
  ring

/-- Cochrane (2023), A1 §1.6, p. 567: `E[ξ] = 0`. -/
theorem integral_coinXi : ∫ ω, coinXi ω ∂coinMeasure = 0 := by
  rw [integral_coin]
  simp [coinXi]

/-- Cochrane (2023), A1 §1.6, p. 567: conditional expectations given the trivial σ-algebra are
expectations.
From Mathlib `condExp_bot`. -/
theorem condExp_coin_lt {u : ℝ} (hu : u < 1) (f : Bool → ℝ) :
    coinMeasure[f | coinFiltration u] = fun _ => (f true + f false) / 2 := by
  rw [coinFiltration_lt hu, condExp_bot, integral_coin]

/-- Cochrane (2023), A1 §1.6, p. 567: from time `1` on, conditional expectations are the
identity.
From Mathlib `condExp_of_stronglyMeasurable`. -/
theorem condExp_coin_ge {u : ℝ} (hu : 1 ≤ u) (f : Bool → ℝ) :
    coinMeasure[f | coinFiltration u] = f := by
  rw [coinFiltration_ge hu]
  exact condExp_of_stronglyMeasurable le_rfl (measurable_of_finite f).stronglyMeasurable
    Integrable.of_finite

/-- Cochrane (2023), A1 §1.6, p. 567: `M_u = 0` before time `1`. -/
theorem coinM_lt {u : ℝ} (hu : u < 1) : coinM u = fun _ => 0 := by
  funext ω
  simp [coinM, heaviside, not_le.2 hu]

/-- Cochrane (2023), A1 §1.6, p. 567: `M_u = ξ` from time `1` on. -/
theorem coinM_ge {u : ℝ} (hu : 1 ≤ u) : coinM u = coinXi := by
  funext ω
  simp [coinM, heaviside, hu]

/-- Cochrane (2023), A1 §1.6, p. 567: **`M_u = ξ·1{u ≥ 1}` is a martingale** for the coin
filtration. -/
theorem martingale_coinM : Martingale coinM coinFiltration coinMeasure := by
  refine ⟨fun u => ?_, fun i j hij => ?_⟩
  · by_cases hu : u < 1
    · rw [coinM_lt hu]
      exact stronglyMeasurable_const
    · rw [coinFiltration_ge (not_lt.1 hu)]
      exact (measurable_of_finite _).stronglyMeasurable
  · by_cases hi : i < 1
    · rw [condExp_coin_lt hi, coinM_lt hi]
      refine Eventually.of_forall fun ω => ?_
      by_cases hj : j < 1
      · simp [coinM, heaviside, not_le.2 hj]
      · simp [coinM, heaviside, not_lt.1 hj, coinXi]
    · have hj : 1 ≤ j := (not_lt.1 hi).trans hij
      rw [condExp_coin_ge (not_lt.1 hi), coinM_ge hj, coinM_ge (not_lt.1 hi)]

/-- Cochrane (2023), A1 §1.6, p. 567: `|ξ| = 1`. -/
theorem abs_coinXi (ω : Bool) : |coinXi ω| = 1 := by
  cases ω <;> simp [coinXi]

/-- Cochrane (2023), A1 §1.6, p. 567: `ξ² = 1`. -/
theorem coinXi_mul_self (ω : Bool) : coinXi ω * coinXi ω = 1 := by
  cases ω <;> simp [coinXi]

/-- Cochrane (2023), A1 §1.6, p. 567: `B_u = 1` before time `1`. -/
theorem coinB_le {u : ℝ} (hu : u ≤ 1) (ω : Bool) : coinB u ω = 1 := by
  simp [coinB, max_eq_right (by linarith : u - 1 ≤ 0)]

/-- Cochrane (2023), A1 §1.6, p. 567: the paths of `B` are `1`-Lipschitz. -/
theorem lipschitz_coinB (ω : Bool) : LipschitzWith 1 fun u => coinB u ω := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  have h2 := abs_max_sub_max_le_abs (x - 1) (y - 1) 0
  have e : coinB x ω - coinB y ω = coinXi ω * (max (x - 1) 0 - max (y - 1) 0) := by
    simp only [coinB]
    ring
  rw [e, abs_mul, abs_coinXi, one_mul]
  calc |max (x - 1) 0 - max (y - 1) 0| ≤ |x - 1 - (y - 1)| := h2
    _ = |x - y| := by ring_nf

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the coin realisation satisfies the hypotheses of the
product step** on `[0, 2]`. -/
theorem coinData : ProductStepData coinMeasure coinFiltration 0 2 coinB coinA coinM where
  le := by norm_num
  B_adapted u _ := by
    by_cases hu : u < 1
    · have e : coinB u = fun _ => 1 := funext fun ω => coinB_le hu.le ω
      rw [e]
      exact stronglyMeasurable_const
    · rw [coinFiltration_ge (not_lt.1 hu)]
      exact (measurable_of_finite _).stronglyMeasurable
  B_cont ω := (lipschitz_coinB ω).continuous.continuousOn
  B_bv ω := (lipschitz_coinB ω).comp_boundedVariationOn (BoundedVariationOn.id_Icc 0 2)
  A_meas _ _ := measurable_const
  A_cadlag _ := IsCadlag.const
  A_bv _ := by
    rw [BoundedVariationOn, eVariationOn.constant_on
      (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)]
    exact ENNReal.zero_ne_top
  M_mart := martingale_coinM
  M_cadlag ω := isCadlag_heaviside.continuous_comp (continuous_const.mul continuous_id
    (f := fun _ : ℝ => coinXi ω))
  int_XB := Integrable.of_finite
  int_BA := Integrable.of_finite
  int_BM _ _ _ _ _ := Integrable.of_finite

/-! ## Both sides computed -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the left side, `E_0[B_2X_2 − B_0X_0] = 1`**
(`B_2X_2 = (1 + ξ)ξ = 1 + ξ`, `B_0X_0 = 0`, `E[ξ] = 0`). -/
theorem coin_lhs :
    coinMeasure[fun ω => coinB 2 ω * addProc coinA coinM 2 ω -
      coinB 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] = fun _ => 1 := by
  rw [condExp_coin_lt (by norm_num)]
  funext _
  simp [coinB, coinA, coinM, addProc, coinXi, heaviside]
  norm_num

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `∫_0^2 X dB = ξ² = 1` path by path** (`dB = 0`
on `[0, 1]`; `X = ξ` and `B_2 − B_1 = ξ` on `[1, 2]`). -/
theorem coin_intXB (ω : Bool) : intRS 0 2 (addProc coinA coinM) coinB ω = 1 := by
  have hbv := coinData.B_bv ω
  have hX : IsCadlag fun u => addProc coinA coinM u ω := coinData.X_cadlag ω
  simp only [intRS]
  rw [rsInt_add_interval (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2) hbv
    (rsIntegrable_of_isCadlag hX)]
  -- `∫_0^1 X dB = 0`: `B` is constant on `[0, 1]`
  have h01 : rsInt 0 1 (fun u => addProc coinA coinM u ω) (fun u => coinB u ω) = 0 := by
    have hv : eVariationOn (fun u => coinB u ω) (Set.Icc 0 1) = 0 :=
      eVariationOn.constant_on (Set.subsingleton_of_forall_eq (1 : ℝ) fun _ ⟨x, hx, hy⟩ => by
        rw [← hy]; exact coinB_le hx.2 ω)
    have hb := abs_rsInt_le (C := 1) (by norm_num : (0 : ℝ) ≤ 1)
      (hbv.mono (Set.Icc_subset_Icc le_rfl (by norm_num)))
      (f := fun u => addProc coinA coinM u ω) fun x _ => by
        simp only [addProc, coinA, coinM, zero_add, abs_mul, abs_coinXi, one_mul, heaviside]
        split_ifs <;> norm_num
    rw [hv, ENNReal.toReal_zero, mul_zero] at hb
    exact abs_nonpos_iff.1 hb
  -- `∫_1^2 X dB = ξ(B_2 − B_1) = ξ²`
  have h12 : rsInt 1 2 (fun u => addProc coinA coinM u ω) (fun u => coinB u ω) = 1 := by
    have hbv12 : BoundedVariationOn (fun u => coinB u ω) (Set.Icc 1 2) :=
      hbv.mono (Set.Icc_subset_Icc (by norm_num) le_rfl)
    have e : (fun u => addProc coinA coinM u ω) =
        fun u => coinXi ω * 1 + (addProc coinA coinM u ω - coinXi ω * 1) := by
      funext u
      ring
    rw [e, rsInt_add_left (rsIntegrable_of_continuousOn continuousOn_const)
      (rsIntegrable_of_isCadlag (hX.fun_sub IsCadlag.const))]
    have h1 := rsInt_smul_left (a := 1) (b := 2) (coinXi ω) (fun _ => (1 : ℝ))
      (fun u => coinB u ω)
    have h2 := rsInt_one (by norm_num : (1 : ℝ) ≤ 2) hbv12
    have h3 : rsInt 1 2 (fun u => addProc coinA coinM u ω - coinXi ω * 1)
        (fun u => coinB u ω) = 0 := by
      have hb := abs_rsInt_le (C := 0) (by norm_num : (1 : ℝ) ≤ 2) hbv12
        (f := fun u => addProc coinA coinM u ω - coinXi ω * 1) fun x hx => by
          simp [addProc, coinA, coinM, heaviside, hx.1]
      rw [zero_mul] at hb
      exact abs_nonpos_iff.1 hb
    rw [h1, h2, h3]
    simp only [coinB]
    norm_num
    exact coinXi_mul_self ω
  rw [h01, h12, zero_add]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `∫_0^2 B dA = 0`** (`A = 0`). -/
theorem coin_intBA (ω : Bool) : intRS 0 2 coinB coinA ω = 0 := by
  have hv : eVariationOn (fun u => coinA u ω) (Set.Icc 0 2) = 0 :=
    eVariationOn.constant_on (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)
  obtain ⟨C, -, hC⟩ := exists_bound_of_isCadlag (lipschitz_coinB ω).continuous.isCadlag 0 2
  have hb := abs_rsInt_le (by norm_num : (0 : ℝ) ≤ 2) (coinData.A_bv ω) hC
  rw [hv, ENNReal.toReal_zero, mul_zero] at hb
  exact abs_nonpos_iff.1 hb

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: both sides of the product step computed on the
coin.** `E_0[B_2X_2 − B_0X_0] = 1`, `E_0[∫_0^2 X dB] = 1`, `E_0[∫_0^2 B dA] = 0`; and the headline
`TidyR7ProductStep.ProductStepData.product_step` holds there (`1 = 1 + 0`). -/
theorem coin_headline :
    coinMeasure[fun ω => coinB 2 ω * addProc coinA coinM 2 ω -
        coinB 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[intRS 0 2 (addProc coinA coinM) coinB | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[intRS 0 2 coinB coinA | coinFiltration 0] = 0 ∧
      coinMeasure[fun ω => coinB 2 ω * addProc coinA coinM 2 ω -
          coinB 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[intRS 0 2 (addProc coinA coinM) coinB | coinFiltration 0] +
          coinMeasure[intRS 0 2 coinB coinA | coinFiltration 0] := by
  refine ⟨coin_lhs, ?_, ?_, coinData.product_step⟩
  · rw [condExp_coin_lt (by norm_num), coin_intXB, coin_intXB]
    funext _
    norm_num
  · rw [condExp_coin_lt (by norm_num), coin_intBA, coin_intBA]
    funext _
    norm_num

/-! ## The martingale term is nonzero pathwise -/

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: `Σ B_iΔM_i = ξ` path by path, for EVERY
partition of `[0, 2]`** (before time `1`, `B = 1`; from time `1` on, `M` is constant). -/
theorem coin_sumBM (P : Partition 0 2) (ω : Bool) : sumRS P coinB coinM ω = coinXi ω := by
  have hterm : ∀ i, coinB (P.t i) ω * (coinM (P.t (i + 1)) ω - coinM (P.t i) ω) =
      coinM (P.t (i + 1)) ω - coinM (P.t i) ω := by
    intro i
    by_cases hi : P.t i ≤ 1
    · rw [coinB_le hi, one_mul]
    · have hi' : 1 ≤ P.t i := (not_le.1 hi).le
      have hi1 : 1 ≤ P.t (i + 1) := hi'.trans (P.strictMono (Nat.lt_succ_self i)).le
      rw [coinM_ge hi', coinM_ge hi1]
      simp
  have hs : sumRS P coinB coinM ω = ∑ i ∈ Finset.range P.n,
      (coinM (P.t (i + 1)) ω - coinM (P.t i) ω) := by
    simp only [sumRS, rsSum]
    exact Finset.sum_congr rfl fun i _ => hterm i
  rw [hs, Finset.sum_range_sub (fun i => coinM (P.t i) ω), P.last, P.first,
    coinM_ge (by norm_num), coinM_lt (by norm_num), sub_zero]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: yet `E_0[Σ B_iΔM_i] = 0`** at every partition (it
is `E[ξ] = 0`), as `TidyR7ProductStep.ProductStepData.condExp_sumBM_zero` asserts. -/
theorem coin_condExp_sumBM (P : Partition 0 2) :
    coinMeasure[sumRS P coinB coinM | coinFiltration 0] = 0 := by
  rw [condExp_coin_lt (by norm_num), coin_sumBM, coin_sumBM]
  funext _
  simp [coinXi]

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: the expected-increment integral on the coin.**
Path by path `Σ B_iΔX_i = ξ` for every partition, while `B·E_0 dX = E_0[∫_0^2 B dA] = 0`
(`TidyR7ProductStep.ExpIncrLimit`). -/
theorem coin_expIncr :
    (∀ (P : Partition 0 2) (ω : Bool), sumRS P coinB (addProc coinA coinM) ω = coinXi ω) ∧
      ExpIncrLimit coinMeasure coinFiltration 0 2 coinB (addProc coinA coinM) 0 := by
  refine ⟨fun P ω => ?_, ?_⟩
  · rw [sumRS_add_right, coin_sumBM]
    simp [sumRS, rsSum, coinA]
  · have h := expIncrLimit_condExp_rsInt coinData
    have e : coinMeasure[intRS 0 2 coinB coinA | coinFiltration 0] = 0 := coin_headline.2.2.1
    rwa [e] at h

/-! ## Adaptedness of `B` is needed -/

/-- Cochrane (2023), A1 §1.6, p. 567: the anticipating bonds `B_u = ξ` for all `u` (continuous, of
bounded variation, but known before the coin is revealed). -/
def coinBAnt (_ : ℝ) (ω : Bool) : ℝ := coinXi ω

/-- Cochrane (2023), A1 §1.6, p. 567: `B = ξ` is not adapted: `B_0` is not measurable for the
trivial `𝓕_0`. -/
theorem not_adapted_coinBAnt : ¬ StronglyMeasurable[coinFiltration 0] (coinBAnt 0) := by
  rw [coinFiltration_lt (by norm_num)]
  intro h
  have hm := h.measurable (measurableSet_singleton (1 : ℝ))
  rcases MeasurableSpace.measurableSet_bot_iff.1 hm with h0 | h0
  · have : true ∈ coinBAnt 0 ⁻¹' {1} := by simp [coinBAnt, coinXi]
    rw [h0] at this
    exact this
  · have : false ∈ coinBAnt 0 ⁻¹' {1} := by rw [h0]; trivial
    simp [coinBAnt, coinXi] at this
    norm_num at this

/-- **Cochrane (2023), A1 §1.6, (1.32), p. 567: adaptedness of `B` cannot be dropped.** With the
anticipating `B = ξ` (constant paths, so continuous and of bounded variation; all integrability
conditions hold on the finite space) and `X = M = ξ·1{u ≥ 1}`:
`E_0[B_2X_2 − B_0X_0] = E[ξ²] = 1` but `E_0[∫_0^2 X dB] + E_0[∫_0^2 B dA] = 0`, so the conclusion
of `TidyR7ProductStep.ProductStepData.product_step` fails; indeed `E_0[Σ B_iΔM_i] = 1 ≠ 0`. -/
theorem coin_anticipating_fails :
    coinMeasure[fun ω => coinBAnt 2 ω * addProc coinA coinM 2 ω -
        coinBAnt 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] = (fun _ => 1) ∧
      coinMeasure[intRS 0 2 (addProc coinA coinM) coinBAnt | coinFiltration 0] = 0 ∧
      coinMeasure[intRS 0 2 coinBAnt coinA | coinFiltration 0] = 0 ∧
      ¬ (coinMeasure[fun ω => coinBAnt 2 ω * addProc coinA coinM 2 ω -
          coinBAnt 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] =ᵐ[coinMeasure]
        coinMeasure[intRS 0 2 (addProc coinA coinM) coinBAnt | coinFiltration 0] +
          coinMeasure[intRS 0 2 coinBAnt coinA | coinFiltration 0]) := by
  have hv : ∀ ω, eVariationOn (fun u => coinBAnt u ω) (Set.Icc 0 2) = 0 := fun ω =>
    eVariationOn.constant_on (Set.subsingleton_of_forall_eq (coinXi ω) fun _ ⟨_, _, hy⟩ => hy.symm)
  have hva : ∀ ω, eVariationOn (fun u => coinA u ω) (Set.Icc 0 2) = 0 := fun ω =>
    eVariationOn.constant_on (Set.subsingleton_of_forall_eq (0 : ℝ) fun _ ⟨_, _, hy⟩ => hy.symm)
  have hbv : ∀ ω, BoundedVariationOn (fun u => coinBAnt u ω) (Set.Icc 0 2) := fun ω => by
    rw [BoundedVariationOn, hv]; exact ENNReal.zero_ne_top
  have i1 : ∀ ω, intRS 0 2 (addProc coinA coinM) coinBAnt ω = 0 := fun ω => by
    obtain ⟨C, -, hC⟩ := exists_bound_of_isCadlag (coinData.X_cadlag ω) 0 2
    have hb := abs_rsInt_le (by norm_num : (0 : ℝ) ≤ 2) (hbv ω) hC
    rw [hv, ENNReal.toReal_zero, mul_zero] at hb
    exact abs_nonpos_iff.1 hb
  have i2 : ∀ ω, intRS 0 2 coinBAnt coinA ω = 0 := fun ω => by
    have hb := abs_rsInt_le (C := 1) (by norm_num : (0 : ℝ) ≤ 2) (coinData.A_bv ω)
      (f := fun u => coinBAnt u ω) fun _ _ => by simp [coinBAnt, abs_coinXi]
    rw [hva, ENNReal.toReal_zero, mul_zero] at hb
    exact abs_nonpos_iff.1 hb
  have hL : coinMeasure[fun ω => coinBAnt 2 ω * addProc coinA coinM 2 ω -
      coinBAnt 0 ω * addProc coinA coinM 0 ω | coinFiltration 0] = fun _ => 1 := by
    rw [condExp_coin_lt (by norm_num)]
    funext _
    simp [coinBAnt, coinA, coinM, addProc, coinXi, heaviside]
  have hR1 : coinMeasure[intRS 0 2 (addProc coinA coinM) coinBAnt | coinFiltration 0] = 0 := by
    rw [condExp_coin_lt (by norm_num), i1, i1]
    funext _
    norm_num
  have hR2 : coinMeasure[intRS 0 2 coinBAnt coinA | coinFiltration 0] = 0 := by
    rw [condExp_coin_lt (by norm_num), i2, i2]
    funext _
    norm_num
  refine ⟨hL, hR1, hR2, fun h => ?_⟩
  rw [hL, hR1, hR2] at h
  obtain ⟨ω, hω⟩ := h.exists
  simp at hω

/-- Cochrane (2023), A1 §1.6, (1.32), p. 567: with the anticipating `B = ξ`, the martingale sum
does NOT vanish in conditional expectation: `E_0[Σ B_iΔM_i] = E[ξ²] = 1` for every partition of
`[0, 2]`. -/
theorem coin_anticipating_sumBM (P : Partition 0 2) :
    coinMeasure[sumRS P coinBAnt coinM | coinFiltration 0] = fun _ => 1 := by
  have hs : ∀ ω, sumRS P coinBAnt coinM ω = 1 := fun ω => by
    simp only [sumRS, rsSum, coinBAnt]
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => coinM (P.t i) ω), P.last, P.first,
      coinM_ge (by norm_num), coinM_lt (by norm_num), sub_zero, coinXi_mul_self]
  rw [condExp_coin_lt (by norm_num), hs, hs]
  funext _
  norm_num

end Cochrane.Monetarism.TidyR7ProductStepCoin
