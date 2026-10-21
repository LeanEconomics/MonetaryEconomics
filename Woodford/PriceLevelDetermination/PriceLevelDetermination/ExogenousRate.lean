/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.Wicksell
import PriceLevelDetermination.ExpectationsFiniteTree
import Mathlib.Analysis.Real.Cardinality

/-!
# Exogenous interest-rate targets

Woodford (2003), *Interest and Prices*, Chapter 2, §2.1, eqs. (2.1)–(2.3), pp. 86–90,
Proposition 2.5, and its proof in Appendix A, §A.6, pp. 638–639.

## Main results

* `constant_prices_2_1`: (2.1), constant prices require `1 + i_t = β⁻¹ [E_t(u_c'/u_c)]⁻¹`.
* The exact sunspot construction of §A.6: `grossInfl`, `sunspotPrice`. `sunspot_fisher`: for
  ANY process `ν < 1` (mean zero is not needed) the price path solves the exact Fisher equation
  (1.21) with the exogenous rate. `sunspotPrice_injective`: distinct martingale differences give
  distinct price paths. `prop_2_5_uncountable`: in a coin-flip economy there are uncountably
  many exact equilibria (`ν = s ε`, `s ∈ (−1, 1)`).
* `surprise_A6` (survey error E10, corrected): the inflation surprise is
  `π_t − E_{t−1} π_t = −log(1 − ν_t) + E_{t−1} log(1 − ν_t)`; `printed_surprise_false`: the
  printed `−log(1 − ν_t)` is wrong (for `ν = ±1/2` with equal probability, `E log(1 − ν) ≠ 0`).
* Tight bounds (Prop. 2.5, "π_t ∈ P"): `grossInfl_bounds`, `bounds_small`, `infl_small`; and
  the transversality condition (1.24) along these paths, `tvc_tight`.
* The log-linear (2.2)–(2.3): `sol23_solves`, `sol23_bounded`, `eq_sol23` (every solution is of
  the form (2.3)), `bounded_solutions_not_countable`, `worst_case` (inflation of any size with no
  shocks at all).
* `prices_diverge` (p. 88): in an `N`-flip economy two equilibria with `|π_t| ≤ ε` have log price
  levels `εN` apart: price paths "wander arbitrarily far apart".

Expectations: the exact construction uses the pull-out property (`PullOut`) and that functions of
date-`t` known variables are known at `t` (`Closed`); both hold under perfect foresight and on
every finite event tree (`finiteTree_closed`, core `finiteTree_pullOut`).
-/

namespace Woodford.PriceLevelDetermination.ExogenousRate

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (2.1) -/

/-- Woodford (2003), eq. (2.1), p. 86: if prices are constant between `t` and `t + 1`, the exact
Fisher equation (1.21) requires `1 + i_t = β⁻¹ [E_t(u_c(Y_{t+1}; ξ_{t+1})/u_c(Y_t; ξ_t))]⁻¹`. -/
theorem constant_prices_2_1 {β : ℝ} {i uc P : ℕ → Ω → ℝ} {t : ℕ}
    (hP : ∀ ω, P (t + 1) ω = P t ω) (hP0 : ∀ ω, P t ω ≠ 0)
    (h : LogLinear.FisherExact 𝔼 β i uc P t) (ω : Ω) :
    1 + i t ω = β⁻¹ * (𝔼.E t (fun ω' => uc (t + 1) ω' / uc t ω') ω)⁻¹ := by
  have hfun : (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) =
      fun ω' => uc (t + 1) ω' / uc t ω' := by
    funext ω'
    rw [hP ω', mul_div_mul_right _ _ (hP0 ω')]
  have := h ω
  rwa [hfun] at this

/-! ### Information: functions of known variables are known -/

/-- Woodford (2003), App. A, §A.6, p. 639: a function of two date-`t` known variables is known at
date `t` (true conditional expectations have this property). -/
def Closed : Prop :=
  ∀ t (f : ℝ → ℝ → ℝ) (x y : Ω → ℝ), 𝔼.E t x = x → 𝔼.E t y = y →
    𝔼.E t (fun ω => f (x ω) (y ω)) = fun ω => f (x ω) (y ω)

/-- Woodford (2003), App. A, §A.6: perfect foresight has the closure property. -/
theorem perfectForesight_closed : Closed perfectForesight := fun _ _ _ _ _ _ => rfl

/-- Woodford (2003), App. A, §A.6: every finite event tree has the closure property (a function
of cell-constant variables is cell-constant). -/
theorem finiteTree_closed {Ω' : Type*} [Fintype Ω'] (T : ExpectationsFiniteTree.FiniteTree Ω') :
    Closed T.toExpectationSystem := by
  intro t f x y hx hy
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E] at hx hy ⊢
  funext ω
  refine T.condE_of_const_on_cell fun ω' h => ?_
  have hx' : x ω' = x ω := by
    rw [← hx]
    exact T.condE_congr x h
  have hy' : y ω' = y ω := by
    rw [← hy]
    exact T.condE_congr y h
  simp only [hx', hy']

/-! ### The exact construction of §A.6 -/

/-- Woodford (2003), §A.6, p. 639: `K_t = E_t[u_c(Y_{t+1}; ξ_{t+1})(1 − ν_{t+1})]`. -/
noncomputable def Kexp (uc ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω))

/-- Woodford (2003), §A.6, p. 639: gross inflation
`Π_{t+1} = β(1 + i^m_t) E_t[u_c,t+1(1 − ν_{t+1})] / (u_c,t (1 − ν_{t+1}))`. -/
noncomputable def grossInfl (β : ℝ) (i uc ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * (1 + i t ω) * Kexp 𝔼 uc ν t ω / (uc t ω * (1 - ν (t + 1) ω))

/-- Woodford (2003), §A.6, p. 639: the price path `P_0` given, `P_{t+1} = P_t Π_{t+1}`. -/
noncomputable def sunspotPrice (β : ℝ) (P0 : Ω → ℝ) (i uc ν : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => P0
  | t + 1 => fun ω => sunspotPrice β P0 i uc ν t ω * grossInfl 𝔼 β i uc ν t ω

/-- Woodford (2003), §A.6, p. 639: if `u_c,t+1 (1 − ν_{t+1}) ≥ m > 0` then `K_t ≥ m`. -/
theorem Kexp_ge {m : ℝ} {uc ν : ℕ → Ω → ℝ} (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ)
    (ω : Ω) : m ≤ Kexp 𝔼 uc ν t ω := by
  have h := 𝔼.mono t (x := fun _ => m) (y := fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω))
    (fun ω => hm (t + 1) ω) ω
  rwa [𝔼.const] at h

/-- Woodford (2003), §A.6, p. 639: gross inflation is positive. -/
theorem grossInfl_pos {β m : ℝ} (hβ : 0 < β) (hm0 : 0 < m) {i uc ν : ℕ → Ω → ℝ}
    (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) (ω : Ω) : 0 < grossInfl 𝔼 β i uc ν t ω := by
  have hK := Kexp_ge 𝔼 hm t ω
  have h1 := hi t ω
  have h2 := huc t ω
  have h3 : 0 < 1 - ν (t + 1) ω := by linarith [hν (t + 1) ω]
  exact div_pos (mul_pos (mul_pos hβ h1) (lt_of_lt_of_le hm0 hK)) (mul_pos h2 h3)

/-- Woodford (2003), §A.6, p. 639: the price path is positive. -/
theorem sunspotPrice_pos {β m : ℝ} (hβ : 0 < β) (hm0 : 0 < m) {P0 : Ω → ℝ}
    (hP0 : ∀ ω, 0 < P0 ω) {i uc ν : ℕ → Ω → ℝ} (hi : ∀ t ω, 0 < 1 + i t ω)
    (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) (ω : Ω) :
    0 < sunspotPrice 𝔼 β P0 i uc ν t ω := by
  induction t with
  | zero => exact hP0 ω
  | succ t ih => exact mul_pos ih (grossInfl_pos 𝔼 hβ hm0 hi huc hν hm t ω)

/-- Woodford (2003), Proposition 2.5 and §A.6, pp. 87, 639: for an exogenous rate target `i`
(known at each date) and ANY process `ν < 1` with `u_c(1 − ν)` bounded below by `m > 0` (mean
zero is not needed for the Euler equation), the price path of §A.6 satisfies the exact Fisher
equation (1.21) at every date. -/
theorem sunspot_fisher (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β m : ℝ} (hβ : 0 < β)
    (hm0 : 0 < m) {P0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) {i uc ν : ℕ → Ω → ℝ}
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω)
    (hν : ∀ t ω, ν t ω < 1) (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) :
    LogLinear.FisherExact 𝔼 β i uc (sunspotPrice 𝔼 β P0 i uc ν) t := by
  intro ω
  set c : Ω → ℝ := fun ω => (β * (1 + i t ω) * Kexp 𝔼 uc ν t ω)⁻¹ with hc
  set x : Ω → ℝ := fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω) with hx
  have hcK : 𝔼.E t c = c := hC t (fun a b => (β * (1 + a) * b)⁻¹) (i t) (Kexp 𝔼 uc ν t)
    (hia t) (𝔼.E_E_self t _)
  have hfun : (fun ω' => uc (t + 1) ω' * sunspotPrice 𝔼 β P0 i uc ν t ω' /
      (uc t ω' * sunspotPrice 𝔼 β P0 i uc ν (t + 1) ω')) = c * x := by
    funext ω'
    have hP := sunspotPrice_pos 𝔼 hβ hm0 hP0 hi huc hν hm t ω'
    have hK := Kexp_ge 𝔼 hm t ω'
    have h1 := hi t ω'
    have h2 := huc t ω'
    have h3 : 0 < 1 - ν (t + 1) ω' := by linarith [hν (t + 1) ω']
    have hKp : 0 < Kexp 𝔼 uc ν t ω' := lt_of_lt_of_le hm0 hK
    simp only [sunspotPrice, grossInfl, Pi.mul_apply, hc, hx]
    field_simp
  have hE : 𝔼.E t (c * x) ω = (β * (1 + i t ω))⁻¹ := by
    rw [hPO t c x hcK, Pi.mul_apply]
    have hK : 𝔼.E t x ω = Kexp 𝔼 uc ν t ω := rfl
    have hKp : 0 < Kexp 𝔼 uc ν t ω := lt_of_lt_of_le hm0 (Kexp_ge 𝔼 hm t ω)
    have h1 := hi t ω
    rw [hK, hc]
    field_simp
  rw [hfun, hE]
  have h1 := hi t ω
  field_simp

/-- Woodford (2003), §A.6, p. 639 ("the solutions corresponding to different choices of `{ν_t}`
represent distinct equilibria"): if two martingale differences `ν`, `ν'` (`E_t ν_{t+1} = 0`)
give the same price path, they coincide (from date 1 on). -/
theorem sunspotPrice_injective (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β m m' : ℝ} (hβ : 0 < β)
    (hm0 : 0 < m) (hm0' : 0 < m') {P0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) {i uc ν ν' : ℕ → Ω → ℝ}
    (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hν' : ∀ t ω, ν' t ω < 1) (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω))
    (hm' : ∀ t ω, m' ≤ uc t ω * (1 - ν' t ω)) (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0)
    (hmd' : ∀ t, 𝔼.E t (ν' (t + 1)) = 0)
    (heq : sunspotPrice 𝔼 β P0 i uc ν = sunspotPrice 𝔼 β P0 i uc ν') (t : ℕ) :
    ν (t + 1) = ν' (t + 1) := by
  set c : Ω → ℝ := fun ω => Kexp 𝔼 uc ν' t ω / Kexp 𝔼 uc ν t ω with hc
  have hcK : 𝔼.E t c = c := hC t (fun a b => a / b) (Kexp 𝔼 uc ν' t) (Kexp 𝔼 uc ν t)
    (𝔼.E_E_self t _) (𝔼.E_E_self t _)
  -- equal gross inflation
  have hPi : ∀ ω, grossInfl 𝔼 β i uc ν t ω = grossInfl 𝔼 β i uc ν' t ω := by
    intro ω
    have h1 := congrFun (congrFun heq (t + 1)) ω
    have h0 := congrFun (congrFun heq t) ω
    have hP := sunspotPrice_pos 𝔼 hβ hm0 hP0 hi huc hν hm t ω
    simp only [sunspotPrice] at h1
    rw [h0] at h1 hP
    exact mul_left_cancel₀ hP.ne' h1
  have hrel : (fun ω => 1 - ν' (t + 1) ω) = c * fun ω => 1 - ν (t + 1) ω := by
    funext ω
    have h := hPi ω
    have hK := lt_of_lt_of_le hm0 (Kexp_ge 𝔼 hm t ω)
    have hK' := lt_of_lt_of_le hm0' (Kexp_ge 𝔼 hm' t ω)
    have h1 := hi t ω
    have h2 := huc t ω
    have h3 : 0 < 1 - ν (t + 1) ω := by linarith [hν (t + 1) ω]
    have h3' : 0 < 1 - ν' (t + 1) ω := by linarith [hν' (t + 1) ω]
    simp only [grossInfl] at h
    simp only [Pi.mul_apply, hc]
    field_simp at h ⊢
    linear_combination h
  have hone : ∀ μ : ℕ → Ω → ℝ, 𝔼.E t (μ (t + 1)) = 0 →
      𝔼.E t (fun ω => 1 - μ (t + 1) ω) = fun _ => 1 := by
    intro μ hμ
    have : (fun ω => 1 - μ (t + 1) ω) = (fun _ => (1 : ℝ)) - μ (t + 1) := rfl
    rw [this, map_sub, 𝔼.const, hμ, sub_zero]
  have hc1 : c = fun _ => 1 := by
    have h := congrArg (𝔼.E t) hrel
    rw [hone ν' (hmd' t), hPO t c _ hcK, hone ν (hmd t)] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.mul_apply, mul_one] at this
    exact this.symm
  funext ω
  have := congrFun hrel ω
  rw [hc1] at this
  simp only [Pi.mul_apply, one_mul] at this
  linarith

/-! ### The inflation surprise (survey error E10) -/

/-- Woodford (2003), §A.6, p. 639, CORRECTED (survey error E10): along the §A.6 path the
inflation surprise is `π_{t+1} − E_t π_{t+1} = −log(1 − ν_{t+1}) + E_t log(1 − ν_{t+1})`, where
`π_{t+1} = log Π_{t+1}` (the book prints `−log(1 − ν_{t+1})` only). -/
theorem surprise_A6 (hC : Closed 𝔼) {β m : ℝ} (hβ : 0 < β) (hm0 : 0 < m)
    {i uc ν : ℕ → Ω → ℝ} (hia : 𝔼.Adapted i) (huca : 𝔼.Adapted uc)
    (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) :
    (fun ω => Real.log (grossInfl 𝔼 β i uc ν t ω)) -
      𝔼.E t (fun ω => Real.log (grossInfl 𝔼 β i uc ν t ω)) =
      fun ω => -Real.log (1 - ν (t + 1) ω) + 𝔼.E t (fun ω' => Real.log (1 - ν (t + 1) ω')) ω := by
  set y1 : Ω → ℝ := fun ω => β * (1 + i t ω) * Kexp 𝔼 uc ν t ω with hy1
  have hy1k : 𝔼.E t y1 = y1 := hC t (fun a b => β * (1 + a) * b) (i t) (Kexp 𝔼 uc ν t)
    (hia t) (𝔼.E_E_self t _)
  set A : Ω → ℝ := fun ω => Real.log (y1 ω / uc t ω) with hA
  have hAk : 𝔼.E t A = A := hC t (fun a b => Real.log (a / b)) y1 (uc t) hy1k (huca t)
  set L : Ω → ℝ := fun ω => Real.log (1 - ν (t + 1) ω) with hL
  have hsplit : (fun ω => Real.log (grossInfl 𝔼 β i uc ν t ω)) = A - L := by
    funext ω
    have hK := lt_of_lt_of_le hm0 (Kexp_ge 𝔼 hm t ω)
    have h1 := hi t ω
    have h2 := huc t ω
    have h3 : 0 < 1 - ν (t + 1) ω := by linarith [hν (t + 1) ω]
    simp only [grossInfl, Pi.sub_apply, hA, hL, hy1]
    rw [← div_div, Real.log_div (by positivity) h3.ne']
  rw [hsplit, map_sub, hAk]
  funext ω
  simp only [Pi.sub_apply, hL]
  ring

/-- The date-0 information in the coin-flip tree is trivial (restated from the core proofs). -/
theorem coin_info_zero (a b : Bool × Bool) : ExpectationsFiniteTree.coinTree.info 0 a b := by
  change Setoid.ker (ExpectationsFiniteTree.coinObs 0) a b
  rw [Setoid.ker_def]
  simp [ExpectationsFiniteTree.coinObs]

/-- Woodford (2003), §A.6, p. 639, the PRINTED surprise formula is false (survey error E10): for
the mean-zero sunspot `ν_1 = ±1/2` with equal probabilities (coin-flip economy),
`E_0 log(1 − ν_1) = ½ log(3/4) ≠ 0`, so `π_1 − E_0 π_1 ≠ −log(1 − ν_1)`. -/
theorem printed_surprise_false (ω : Bool × Bool) :
    ExpectationsFiniteTree.coinSystem.E 0
      (fun ω' => Real.log (1 - (1 / 2) * ExpectationsFiniteTree.coinShock 1 ω')) ω =
      Real.log (3 / 4) / 2 ∧ Real.log (3 / 4) / 2 < 0 := by
  constructor
  · rw [ExpectationsFiniteTree.coinSystem,
      ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
      ExpectationsFiniteTree.coinTree.condE_of_trivial coin_info_zero]
    simp only [ExpectationsFiniteTree.coinTree, ExpectationsFiniteTree.coinShock,
      Fintype.sum_prod_type, Fintype.univ_bool, ↓reduceIte]
    have h : Real.log (3 / 4) = Real.log (1 / 2) + Real.log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [h]
    norm_num
    ring
  · have : Real.log (3 / 4) < 0 := Real.log_neg (by norm_num) (by norm_num)
    linarith

/-! ### Proposition 2.5: uncountably many exact equilibria -/

/-- Woodford (2003), Proposition 2.5, p. 87 (exact, nonlinear): in the coin-flip economy, with
`u_c ≡ 1`, an exogenous rate `i ≡ β⁻¹ − 1` and `P_0 = 1`, the sunspot equilibria `ν = s ε`
(`ε` the mean-zero coin innovation, `s ∈ (−1, 1)`) of §A.6 are uncountably many distinct
solutions of the exact Fisher equation (1.21). -/
theorem prop_2_5_uncountable {β : ℝ} (hβ : 0 < β) :
    ¬ {P : ℕ → Bool × Bool → ℝ | (∀ t, LogLinear.FisherExact ExpectationsFiniteTree.coinSystem β
        (fun _ _ => β⁻¹ - 1) (fun _ _ => 1) P t) ∧ P 0 = fun _ => 1}.Countable := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem
  have hPO : 𝔼c.PullOut := ExpectationsFiniteTree.finiteTree_pullOut _
  have hC : Closed 𝔼c := finiteTree_closed _
  have hεb : ∀ t ω, |ExpectationsFiniteTree.coinShock t ω| ≤ 1 := by
    intro t ω
    unfold ExpectationsFiniteTree.coinShock
    split_ifs <;> norm_num
  have hi : ∀ (t : ℕ) (ω : Bool × Bool), 0 < 1 + (fun (_ : ℕ) (_ : Bool × Bool) => β⁻¹ - 1) t ω :=
    fun _ _ => by simp [hβ]
  have hia : 𝔼c.Adapted (fun _ _ => β⁻¹ - 1) := fun t => 𝔼c.const t _
  let f : ℝ → ℕ → Bool × Bool → ℝ := fun s => sunspotPrice 𝔼c β (fun _ => 1) (fun _ _ => β⁻¹ - 1)
    (fun _ _ => 1) (fun t => s • ExpectationsFiniteTree.coinShock t)
  have hνlt : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ω,
      (fun t => s • ExpectationsFiniteTree.coinShock t) t ω < 1 := by
    intro s hs t ω
    have h1 : |s * ExpectationsFiniteTree.coinShock t ω| ≤ |s| := by
      rw [abs_mul]
      nlinarith [hεb t ω, abs_nonneg s]
    have h2 : |s| < 1 := abs_lt.mpr hs
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith [le_abs_self (s * ExpectationsFiniteTree.coinShock t ω)]
  have hmlow : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, ∀ t ω, 1 - |s| ≤ (fun (_ : ℕ) (_ : Bool × Bool) =>
      (1 : ℝ)) t ω * (1 - (fun t => s • ExpectationsFiniteTree.coinShock t) t ω) := by
    intro s _ t ω
    have h1 : |s * ExpectationsFiniteTree.coinShock t ω| ≤ |s| := by
      rw [abs_mul]
      nlinarith [hεb t ω, abs_nonneg s]
    simp only [Pi.smul_apply, smul_eq_mul, one_mul]
    linarith [le_abs_self (s * ExpectationsFiniteTree.coinShock t ω)]
  have hmpos : ∀ s ∈ Set.Ioo (-1 : ℝ) 1, 0 < 1 - |s| := fun s hs => by
    have := abs_lt.mpr hs
    linarith
  have hmd : ∀ s : ℝ, ∀ t, 𝔼c.E t ((fun t => s • ExpectationsFiniteTree.coinShock t) (t + 1)) =
      0 := by
    intro s t
    simp only [map_smul]
    rw [ExpectationsFiniteTree.coinShock_mean_zero, smul_zero]
  have hmaps : Set.MapsTo f (Set.Ioo (-1) 1) {P | (∀ t, LogLinear.FisherExact 𝔼c β
      (fun _ _ => β⁻¹ - 1) (fun _ _ => 1) P t) ∧ P 0 = fun _ => 1} := by
    intro s hs
    exact ⟨fun t => sunspot_fisher 𝔼c hPO hC hβ (hmpos s hs) (fun _ => one_pos) hia hi
      (fun _ _ => one_pos) (hνlt s hs) (hmlow s hs) t, rfl⟩
  have hinj : Set.InjOn f (Set.Ioo (-1) 1) := by
    intro s hs s' hs' h
    have := sunspotPrice_injective 𝔼c hPO hC hβ (hmpos s hs) (hmpos s' hs') (fun _ => one_pos)
      hi (fun _ _ => one_pos) (hνlt s hs) (hνlt s' hs') (hmlow s hs) (hmlow s' hs')
      (hmd s) (hmd s') h 0
    have := congrFun this (true, true)
    simpa [ExpectationsFiniteTree.coinShock] using this
  intro hcount
  have := hmaps.countable_of_injOn hinj hcount
  rw [Cardinal.Real.Ioo_countable_iff] at this
  norm_num at this

/-! ### Tight bounds: inflation stays in any neighbourhood of zero -/

/-- Woodford (2003), Proposition 2.5, p. 87 ("tight enough bounds"): if `u_c` stays within a
factor `1 ± δ` of `ū`, `|ν| ≤ δ` and `β(1 + i)` within `1 ± δ` (`0 < δ < 1`), then gross
inflation lies in `[(1 − δ)³/(1 + δ)², (1 + δ)³/(1 − δ)²]`. -/
theorem grossInfl_bounds {β δ ubar : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hu : 0 < ubar)
    {i uc ν : ℕ → Ω → ℝ} (hucl : ∀ t ω, ubar * (1 - δ) ≤ uc t ω)
    (hucu : ∀ t ω, uc t ω ≤ ubar * (1 + δ)) (hν : ∀ t ω, |ν t ω| ≤ δ)
    (hil : ∀ t ω, 1 - δ ≤ β * (1 + i t ω)) (hiu : ∀ t ω, β * (1 + i t ω) ≤ 1 + δ) (t : ℕ)
    (ω : Ω) :
    (1 - δ) ^ 3 / (1 + δ) ^ 2 ≤ grossInfl 𝔼 β i uc ν t ω ∧
      grossInfl 𝔼 β i uc ν t ω ≤ (1 + δ) ^ 3 / (1 - δ) ^ 2 := by
  have hx : ∀ s ω, ubar * (1 - δ) ^ 2 ≤ uc s ω * (1 - ν s ω) ∧
      uc s ω * (1 - ν s ω) ≤ ubar * (1 + δ) ^ 2 := by
    intro s ω
    have h1 := abs_le.mp (hν s ω)
    have h2 := hucl s ω
    have h3 := hucu s ω
    have hl0 : 0 ≤ ubar * (1 - δ) := mul_nonneg hu.le (by linarith)
    constructor
    · calc ubar * (1 - δ) ^ 2 = ubar * (1 - δ) * (1 - δ) := by ring
        _ ≤ uc s ω * (1 - ν s ω) :=
          mul_le_mul h2 (by linarith) (by linarith) (hl0.trans h2)
    · calc uc s ω * (1 - ν s ω) ≤ ubar * (1 + δ) * (1 + δ) :=
          mul_le_mul h3 (by linarith) (by linarith) (hl0.trans (h2.trans h3))
        _ = ubar * (1 + δ) ^ 2 := by ring
  have hKl : ubar * (1 - δ) ^ 2 ≤ Kexp 𝔼 uc ν t ω := by
    have h := 𝔼.mono t (x := fun _ => ubar * (1 - δ) ^ 2)
      (y := fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω)) (fun ω => (hx (t + 1) ω).1) ω
    rwa [𝔼.const] at h
  have hKu : Kexp 𝔼 uc ν t ω ≤ ubar * (1 + δ) ^ 2 := by
    have h := 𝔼.mono t (y := fun _ => ubar * (1 + δ) ^ 2)
      (x := fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω)) (fun ω => (hx (t + 1) ω).2) ω
    rwa [𝔼.const] at h
  have hl0 : 0 ≤ ubar * (1 - δ) := mul_nonneg hu.le (by linarith)
  have hdl : ubar * (1 - δ) ^ 2 ≤ uc t ω * (1 - ν (t + 1) ω) := by
    have h1 := abs_le.mp (hν (t + 1) ω)
    have h2 := hucl t ω
    calc ubar * (1 - δ) ^ 2 = ubar * (1 - δ) * (1 - δ) := by ring
      _ ≤ uc t ω * (1 - ν (t + 1) ω) :=
        mul_le_mul h2 (by linarith) (by linarith) (hl0.trans h2)
  have hdu : uc t ω * (1 - ν (t + 1) ω) ≤ ubar * (1 + δ) ^ 2 := by
    have h1 := abs_le.mp (hν (t + 1) ω)
    have h3 := hucu t ω
    have h2 := hucl t ω
    calc uc t ω * (1 - ν (t + 1) ω) ≤ ubar * (1 + δ) * (1 + δ) :=
        mul_le_mul h3 (by linarith) (by linarith) (hl0.trans (h2.trans h3))
      _ = ubar * (1 + δ) ^ 2 := by ring
  have hpos1 : 0 < ubar * (1 - δ) ^ 2 := by
    have : 0 < 1 - δ := by linarith
    positivity
  have hb0 : 0 ≤ 1 - δ := by linarith
  unfold grossInfl
  constructor
  · have e : (1 - δ) ^ 3 / (1 + δ) ^ 2 = ((1 - δ) * (ubar * (1 - δ) ^ 2)) /
        (ubar * (1 + δ) ^ 2) := by
      field_simp
    rw [e]
    exact div_le_div₀ (mul_nonneg (by linarith [hil t ω]) (hpos1.le.trans hKl))
      (mul_le_mul (hil t ω) hKl hpos1.le (by linarith [hil t ω]))
      (lt_of_lt_of_le hpos1 hdl) hdu
  · have e : (1 + δ) ^ 3 / (1 - δ) ^ 2 = ((1 + δ) * (ubar * (1 + δ) ^ 2)) /
        (ubar * (1 - δ) ^ 2) := by
      have : (1 - δ) ≠ 0 := by linarith
      field_simp
    rw [e]
    exact div_le_div₀ (mul_nonneg (by linarith) (mul_nonneg hu.le (sq_nonneg _)))
      (mul_le_mul (hiu t ω) hKu (hpos1.le.trans hKl) (by linarith)) hpos1 hdl

/-- Woodford (2003), Proposition 2.5, p. 87: for every `ε > 0` and every `ρ < 1` there is
`δ ∈ (0, 1)` with `e^{−ε} ≤ (1 − δ)³/(1 + δ)²`, `(1 + δ)³/(1 − δ)² ≤ e^{ε}` and
`ρ < (1 − δ)³/(1 + δ)²`. -/
theorem bounds_small {ε ρ : ℝ} (hε : 0 < ε) (hρ : ρ < 1) :
    ∃ δ, 0 < δ ∧ δ < 1 ∧ Real.exp (-ε) ≤ (1 - δ) ^ 3 / (1 + δ) ^ 2 ∧
      (1 + δ) ^ 3 / (1 - δ) ^ 2 ≤ Real.exp ε ∧ ρ < (1 - δ) ^ 3 / (1 + δ) ^ 2 := by
  have hg : ContinuousAt (fun δ : ℝ => (1 - δ) ^ 3 / (1 + δ) ^ 2) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have hf : ContinuousAt (fun δ : ℝ => (1 + δ) ^ 3 / (1 - δ) ^ 2) 0 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have hg0 : (fun δ : ℝ => (1 - δ) ^ 3 / (1 + δ) ^ 2) 0 = 1 := by norm_num
  have hf0 : (fun δ : ℝ => (1 + δ) ^ 3 / (1 - δ) ^ 2) 0 = 1 := by norm_num
  have he1 : Real.exp (-ε) < 1 := by
    have := Real.exp_lt_exp.mpr (show -ε < 0 by linarith)
    rwa [Real.exp_zero] at this
  have he2 : 1 < Real.exp ε := by
    have := Real.exp_lt_exp.mpr hε
    rwa [Real.exp_zero] at this
  have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), Real.exp (-ε) < (1 - δ) ^ 3 / (1 + δ) ^ 2 :=
    hg.eventually (lt_mem_nhds (by rw [hg0]; exact he1))
  have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), (1 + δ) ^ 3 / (1 - δ) ^ 2 < Real.exp ε :=
    hf.eventually (gt_mem_nhds (by rw [hf0]; exact he2))
  have h3 : ∀ᶠ δ in 𝓝 (0 : ℝ), ρ < (1 - δ) ^ 3 / (1 + δ) ^ 2 :=
    hg.eventually (lt_mem_nhds (by rw [hg0]; exact hρ))
  have h4 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 1 := gt_mem_nhds (by norm_num)
  have hall := (Filter.Eventually.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    (h1.and (h2.and (h3.and h4)))).and (eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))
  obtain ⟨δ, ⟨ha, hb, hc, hd⟩, he⟩ := hall.exists
  exact ⟨δ, he, hd, ha.le, hb.le, hc⟩

/-- Woodford (2003), Proposition 2.5, p. 87 ("in each of which the inflation rate satisfies
`π_t ∈ P`"): for every `ε > 0` there is `δ > 0` such that, whenever the disturbances satisfy the
`δ`-bounds of `grossInfl_bounds`, the inflation rate `π_{t+1} = log Π_{t+1}` of every §A.6
equilibrium satisfies `|π_{t+1}| ≤ ε`. -/
theorem infl_small {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ < 1 ∧ ∀ {β ubar : ℝ} {i uc ν : ℕ → Ω → ℝ}, 0 < ubar →
      (∀ t ω, ubar * (1 - δ) ≤ uc t ω) → (∀ t ω, uc t ω ≤ ubar * (1 + δ)) →
      (∀ t ω, |ν t ω| ≤ δ) → (∀ t ω, 1 - δ ≤ β * (1 + i t ω)) →
      (∀ t ω, β * (1 + i t ω) ≤ 1 + δ) → ∀ t ω, |Real.log (grossInfl 𝔼 β i uc ν t ω)| ≤ ε := by
  obtain ⟨δ, hδ0, hδ1, hlo, hhi, -⟩ := bounds_small hε (ρ := 0) one_pos
  refine ⟨δ, hδ0, hδ1, fun hu hucl hucu hν hil hiu t ω => ?_⟩
  obtain ⟨hl, hh⟩ := grossInfl_bounds 𝔼 hδ0 hδ1 hu hucl hucu hν hil hiu t ω
  have hpos : 0 < grossInfl 𝔼 _ _ _ _ t ω := lt_of_lt_of_le (Real.exp_pos _) (hlo.trans hl)
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) (hlo.trans hl)
    rw [Real.log_exp] at this
    linarith
  · have := Real.log_le_log hpos (hh.trans hhi)
    rwa [Real.log_exp] at this

/-- Woodford (2003), §A.6 and (1.24), pp. 72, 639: a price path with gross inflation at least
`L > 0` grows at least geometrically, `P_T ≥ p₀ Lᵀ`. -/
theorem sunspotPrice_lower {β L p0 : ℝ} (hL : 0 < L) (hp0 : 0 < p0) {P0 : Ω → ℝ}
    (hP0 : ∀ ω, p0 ≤ P0 ω) {i uc ν : ℕ → Ω → ℝ}
    (hPi : ∀ t ω, L ≤ grossInfl 𝔼 β i uc ν t ω) (T : ℕ) (ω : Ω) :
    p0 * L ^ T ≤ sunspotPrice 𝔼 β P0 i uc ν T ω := by
  induction T with
  | zero =>
    rw [pow_zero, mul_one]
    exact hP0 ω
  | succ T ih =>
    simp only [sunspotPrice, pow_succ, ← mul_assoc]
    exact mul_le_mul ih (hPi T ω) hL.le ((by positivity : (0 : ℝ) ≤ p0 * L ^ T).trans ih)

/-- Woodford (2003), (1.24) and §A.6, pp. 72, 639 ("satisfies (A.2) as well"): if
`0 ≤ D_T ≤ D̄ γᵀ`, `0 < u_c ≤ ū`, and gross inflation is at least `L` with `βγ < L`, the
transversality condition `βᵀ E_t[u_c,T D_T/P_T] → 0` holds along the §A.6 path. -/
theorem tvc_tight {β L p0 γ Dbar ubar : ℝ} (hβ : 0 < β) (hL : 0 < L) (hp0 : 0 < p0)
    (hγ : 0 ≤ γ) (hβγ : β * γ < L) {P0 : Ω → ℝ} (hP0 : ∀ ω, p0 ≤ P0 ω)
    {i uc ν D : ℕ → Ω → ℝ} (hPi : ∀ t ω, L ≤ grossInfl 𝔼 β i uc ν t ω)
    (huc0 : ∀ t ω, 0 ≤ uc t ω) (hucu : ∀ t ω, uc t ω ≤ ubar) (hD0 : ∀ T ω, 0 ≤ D T ω)
    (hDu : ∀ T ω, D T ω ≤ Dbar * γ ^ T) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => β ^ T * 𝔼.E t (fun ω' => uc T ω' * D T ω' /
      sunspotPrice 𝔼 β P0 i uc ν T ω') ω) atTop (𝓝 0) := by
  have hr0 : 0 ≤ β * γ / L := by positivity
  have hr1 : β * γ / L < 1 := (div_lt_one hL).mpr hβγ
  have hb : ∀ T ω', |uc T ω' * D T ω' / sunspotPrice 𝔼 β P0 i uc ν T ω'| ≤
      ubar * Dbar / p0 * (γ / L) ^ T := by
    intro T ω'
    have hP := sunspotPrice_lower 𝔼 hL hp0 hP0 hPi T ω'
    have hPp : 0 < p0 * L ^ T := by positivity
    have hnum0 : 0 ≤ uc T ω' * D T ω' := mul_nonneg (huc0 T ω') (hD0 T ω')
    rw [abs_of_nonneg (div_nonneg hnum0 (hPp.le.trans hP))]
    have hnum : uc T ω' * D T ω' ≤ ubar * (Dbar * γ ^ T) :=
      mul_le_mul (hucu T ω') (hDu T ω') (hD0 T ω') ((huc0 T ω').trans (hucu T ω'))
    calc uc T ω' * D T ω' / sunspotPrice 𝔼 β P0 i uc ν T ω'
        ≤ uc T ω' * D T ω' / (p0 * L ^ T) := div_le_div_of_nonneg_left hnum0 hPp hP
      _ ≤ ubar * (Dbar * γ ^ T) / (p0 * L ^ T) := div_le_div_of_nonneg_right hnum hPp.le
      _ = ubar * Dbar / p0 * (γ / L) ^ T := by rw [div_pow]; field_simp
  have hlim : Tendsto (fun T : ℕ => |ubar * Dbar / p0| * (β * γ / L) ^ T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul |ubar * Dbar / p0|
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos hβ]
  have hE := 𝔼.abs_E_le (fun ω' => (hb T ω').trans (le_abs_self _)) t ω
  calc β ^ T * |𝔼.E t (fun ω' => uc T ω' * D T ω' / sunspotPrice 𝔼 β P0 i uc ν T ω') ω|
      ≤ β ^ T * |ubar * Dbar / p0 * (γ / L) ^ T| := by gcongr
    _ = |ubar * Dbar / p0| * (β * γ / L) ^ T := by
      rw [abs_mul, abs_pow, abs_of_nonneg (div_nonneg hγ hL.le), mul_div_assoc, mul_div_assoc,
        mul_pow]
      ring

/-! ### The log-linear equations (2.2)–(2.3) -/

/-- Woodford (2003), eq. (2.2), p. 87: `ī_t = r̂_t + E_t π_{t+1}`. -/
def Lin22 (ib r π : ℕ → Ω → ℝ) : Prop := ∀ t, ib t = r t + 𝔼.E t (π (t + 1))

/-- Woodford (2003), eq. (2.3), p. 87: `π_0` free and `π_{t+1} = ī_t − r̂_t + ν_{t+1}`. -/
def sol23 (ib r ν : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => ib t - r t + ν (t + 1)

/-- Woodford (2003), eq. (2.3), p. 87: (2.3) solves (2.2) for any `ν` with `E_t ν_{t+1} = 0`. -/
theorem sol23_solves {ib r ν : ℕ → Ω → ℝ} (π0 : Ω → ℝ) (hib : 𝔼.Adapted ib)
    (hr : 𝔼.Adapted r) (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) : Lin22 𝔼 ib r (sol23 ib r ν π0) := by
  intro t
  simp only [sol23, map_add, map_sub, hib t, hr t, hmd t, add_zero]
  abel

/-- Woodford (2003), eq. (2.3), p. 87: (2.3) is bounded when `ī`, `r̂`, `ν` and `π_0` are. -/
theorem sol23_bounded {ib r ν : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (hib : BoundedProc ib)
    (hr : BoundedProc r) (hν : BoundedProc ν) {B : ℝ} (hπ0 : ∀ ω, |π0 ω| ≤ B) :
    BoundedProc (sol23 ib r ν π0) := by
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨Mr, hMr⟩ := hr
  obtain ⟨Mν, hMν⟩ := hν
  refine ⟨|B| + Mi + Mr + Mν, fun t ω => ?_⟩
  have h0 : 0 ≤ Mi := (abs_nonneg _).trans (hMi 0 ω)
  have h1 : 0 ≤ Mr := (abs_nonneg _).trans (hMr 0 ω)
  have h2 : 0 ≤ Mν := (abs_nonneg _).trans (hMν 0 ω)
  rcases t with _ | t
  · simp only [sol23]
    linarith [hπ0 ω, le_abs_self B]
  · simp only [sol23, Pi.add_apply, Pi.sub_apply]
    have := abs_add_le (ib t ω - r t ω) (ν (t + 1) ω)
    have := abs_sub (ib t ω) (r t ω)
    linarith [hMi t ω, hMr t ω, hMν (t + 1) ω, abs_nonneg B]

/-- Woodford (2003), p. 87 ("absolutely any pattern of bounded fluctuations in the unexpected
component of the inflation rate is consistent with it"): every solution of (2.2) is (2.3) with
`ν_{t+1} = π_{t+1} − E_t π_{t+1}`, a martingale difference. -/
theorem eq_sol23 {ib r π : ℕ → Ω → ℝ} (hπ : Lin22 𝔼 ib r π) :
    (∀ t, 𝔼.E t (π (t + 1) - 𝔼.E t (π (t + 1))) = 0) ∧
      π = sol23 ib r (fun t => π t - 𝔼.E (t - 1) (π t)) (π 0) := by
  refine ⟨fun t => by rw [map_sub, 𝔼.E_E_self, sub_self], ?_⟩
  funext t
  rcases t with _ | t
  · rfl
  · simp only [sol23, show t + 1 - 1 = t by omega]
    rw [hπ t]
    abel

/-- Woodford (2003), Proposition 2.5 (log-linear), p. 87: with bounded adapted `ī`, `r̂` the
bounded solutions of (2.2) are uncountably many (the initial inflation rate is free). -/
theorem bounded_solutions_not_countable [Nonempty Ω] {ib r : ℕ → Ω → ℝ} (hib : 𝔼.Adapted ib)
    (hr : 𝔼.Adapted r) (hibb : BoundedProc ib) (hrb : BoundedProc r) :
    ¬ {π | BoundedProc π ∧ Lin22 𝔼 ib r π}.Countable := by
  intro hcount
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  let f : ℝ → ℕ → Ω → ℝ := fun c => sol23 ib r 0 (fun _ => c)
  have hmaps : Set.MapsTo f Set.univ {π | BoundedProc π ∧ Lin22 𝔼 ib r π} := fun c _ =>
    ⟨sol23_bounded hibb hrb hzb (B := |c|) (fun _ => le_rfl),
      sol23_solves 𝔼 _ hib hr (fun t => map_zero _)⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    exact congrFun (congrFun h 0) ω
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Woodford (2003), p. 89 (the worst-case argument): with NO disturbances at all (`ī = r̂ = 0`)
an exogenous target admits bounded equilibria with inflation of any size `c`. -/
theorem worst_case (c : ℝ) :
    BoundedProc (sol23 (0 : ℕ → Ω → ℝ) 0 0 (fun _ => c)) ∧
      Lin22 𝔼 0 0 (sol23 (0 : ℕ → Ω → ℝ) 0 0 (fun _ => c)) ∧
      ∀ ω, sol23 (0 : ℕ → Ω → ℝ) 0 0 (fun _ => c) 0 ω = c := by
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  exact ⟨sol23_bounded hzb hzb hzb (B := |c|) (fun _ => le_rfl),
    sol23_solves 𝔼 _ (fun t => map_zero _) (fun t => map_zero _) (fun t => map_zero _),
    fun _ => rfl⟩

/-! ### Price paths wander arbitrarily far apart (p. 88) -/

/-- Woodford (2003), p. 88 (an `N`-flip economy): coin flip `k` is revealed at date `k + 1`;
`ω ~_t ω'` iff the first `t` flips agree. -/
def flipInfo (N t : ℕ) : Setoid (Fin N → Bool) :=
  ⟨fun a b => ∀ k : Fin N, k.val < t → a k = b k,
    ⟨fun _ _ _ => rfl, fun h k hk => (h k hk).symm,
      fun h1 h2 k hk => (h1 k hk).trans (h2 k hk)⟩⟩

/-- Woodford (2003), p. 88: the `N`-flip event tree with fair, independent flips. -/
noncomputable def flipTree (N : ℕ) : ExpectationsFiniteTree.FiniteTree (Fin N → Bool) where
  prob := fun _ => (1 / 2 : ℝ) ^ N
  prob_pos := fun _ => by positivity
  prob_sum := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← mul_pow]
    norm_num
  info := flipInfo N
  refines := fun hst _ _ h k hk => h k (lt_of_lt_of_le hk hst)

/-- Woodford (2003), p. 88: the expectation system of the `N`-flip tree. -/
noncomputable def flipSystem (N : ℕ) : ExpectationSystem (Fin N → Bool) :=
  (flipTree N).toExpectationSystem

/-- Woodford (2003), p. 88: the innovation `ε_t = ±1` from flip `t − 1` (`1 ≤ t ≤ N`), else `0`. -/
def flipShock (N t : ℕ) (ω : Fin N → Bool) : ℝ :=
  if h : 0 < t ∧ t ≤ N then (if ω ⟨t - 1, by omega⟩ then 1 else -1) else 0

/-- Woodford (2003), p. 88: `|ε_t| ≤ 1`. -/
theorem flipShock_abs_le (N t : ℕ) (ω : Fin N → Bool) : |flipShock N t ω| ≤ 1 := by
  unfold flipShock
  split_ifs <;> norm_num

/-- Woodford (2003), p. 88: the innovations are mean-zero, `E_t ε_{t+1} = 0` (flipping coin `t`
is a measure-preserving involution of each date-`t` cell that changes the sign of `ε_{t+1}`). -/
theorem flipShock_mean_zero (N t : ℕ) : (flipSystem N).E t (flipShock N (t + 1)) = 0 := by
  classical
  funext ω
  rw [flipSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  unfold ExpectationsFiniteTree.FiniteTree.condE
  suffices hnum : (flipTree N).num t (flipShock N (t + 1)) ω = 0 by
    rw [hnum, zero_div]
    rfl
  by_cases htN : t < N
  · set k : Fin N := ⟨t, htN⟩ with hk
    let σ : Equiv.Perm (Fin N → Bool) :=
      ⟨fun ω' => Function.update ω' k (!ω' k), fun ω' => Function.update ω' k (!ω' k),
        fun ω' => by simp, fun ω' => by simp⟩
    have hcell : ∀ ω', (flipTree N).info t (σ ω') ω ↔ (flipTree N).info t ω' ω := by
      intro ω'
      change (∀ j : Fin N, j.val < t → _ = _) ↔ (∀ j : Fin N, j.val < t → _ = _)
      refine forall_congr' fun j => imp_congr_right fun hj => ?_
      have hjk : j ≠ k := by
        intro h
        rw [h, hk] at hj
        exact lt_irrefl _ hj
      simp [σ, Function.update_of_ne hjk]
    have hflip : ∀ ω', flipShock N (t + 1) (σ ω') = -flipShock N (t + 1) ω' := by
      intro ω'
      have h1 : 0 < t + 1 ∧ t + 1 ≤ N := ⟨by omega, by omega⟩
      have hk' : (⟨t + 1 - 1, by omega⟩ : Fin N) = k := by
        rw [hk]
        exact Fin.ext (by simp)
      simp only [flipShock, h1, and_self, ↓reduceDIte, hk']
      simp only [σ, Equiv.coe_fn_mk, Function.update_self]
      cases ω' k <;> norm_num
    unfold ExpectationsFiniteTree.FiniteTree.num
    have hsum := Equiv.sum_comp σ (fun ω' => if (flipTree N).info t ω' ω then
      (flipTree N).prob ω' * flipShock N (t + 1) ω' else 0)
    have hterm : ∀ ω', (if (flipTree N).info t (σ ω') ω then
        (flipTree N).prob (σ ω') * flipShock N (t + 1) (σ ω') else 0) =
        -(if (flipTree N).info t ω' ω then
          (flipTree N).prob ω' * flipShock N (t + 1) ω' else 0) := by
      intro ω'
      by_cases h : (flipTree N).info t ω' ω
      · have h' := (hcell ω').mpr h
        simp only [h, h', ↓reduceIte, hflip, flipTree]
        ring
      · have h' : ¬ (flipTree N).info t (σ ω') ω := fun h'' => h ((hcell ω').mp h'')
        simp only [h, h', ↓reduceIte, neg_zero]
    simp only [hterm, Finset.sum_neg_distrib] at hsum
    linarith
  · have h0 : flipShock N (t + 1) = fun _ => 0 := by
      funext ω'
      unfold flipShock
      split_ifs <;> first | rfl | omega
    rw [h0]
    unfold ExpectationsFiniteTree.FiniteTree.num
    simp

/-- Woodford (2003), p. 88 ("this set of solutions includes alternative paths for the price level
that wander arbitrarily far from one another"): for every `K` and `ε > 0` there is an `N`-flip
economy and two solutions of (2.2) (with `ī = r̂ = 0`) whose inflation rates never exceed `ε`
in absolute value, but whose log price levels `log P_N = log P_{−1} + ∑_{s ≤ N} π_s` (same
`P_{−1}`) differ by more than `K` when all flips are heads. -/
theorem prices_diverge (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ π π' : ℕ → (Fin N → Bool) → ℝ,
      Lin22 (flipSystem N) 0 0 π ∧ Lin22 (flipSystem N) 0 0 π' ∧
      (∀ t ω, |π t ω| ≤ ε) ∧ (∀ t ω, |π' t ω| ≤ ε) ∧
      K < ∑ s ∈ Finset.range (N + 1), (π s (fun _ => true) - π' s (fun _ => true)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (K / ε)
  refine ⟨N, sol23 0 0 (fun t => ε • flipShock N t) 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · refine sol23_solves (flipSystem N) 0 (fun t => map_zero _) (fun t => map_zero _)
      (fun t => ?_)
    simp only [map_smul, flipShock_mean_zero, smul_zero]
  · intro t
    simp
  · intro t ω
    rcases t with _ | t
    · simp [sol23, hε.le]
    · simp only [sol23, Pi.zero_apply, sub_zero, zero_add, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos hε]
      have := flipShock_abs_le N (t + 1) ω
      nlinarith
  · intro t ω
    simp [hε.le]
  · rw [Finset.sum_range_succ']
    have hs : ∀ s ∈ Finset.range N,
        (sol23 0 0 (fun t => ε • flipShock N t) 0 (s + 1) (fun _ => true) -
          (0 : ℕ → (Fin N → Bool) → ℝ) (s + 1) (fun _ => true)) = ε := by
      intro s hs
      rw [Finset.mem_range] at hs
      have h1 : 0 < s + 1 ∧ s + 1 ≤ N := ⟨by omega, by omega⟩
      simp [sol23, flipShock, h1]
    rw [Finset.sum_congr rfl hs, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [sol23, Pi.zero_apply, sub_zero, add_zero]
    rw [div_lt_iff₀ hε] at hN
    linarith

end Woodford.PriceLevelDetermination.ExogenousRate
