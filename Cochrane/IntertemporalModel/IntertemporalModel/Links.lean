/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.LinearFTMP
import IntertemporalModel.Valuation
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Links to the Woodford projects

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4 (p. 33), §2.5–2.6
(pp. 34–42), set against Woodford (2003), *Interest and Prices*, Chapter 2 (Propositions 2.5 and
2.6, eq. (4.2)) and Chapter 4 (eq. (4.1)). The Woodford results are restated here (copied, not
imported) and the contrast with the fiscal theory is proved. The restated closure property
`Closed` lives in `ExpectationTools`; the links among this chapter's own modules are in
`GeneralLinks`.

## Main results

* **Pegs.** Woodford's Proposition 2.5 (restated: `sunspot_fisher`, `sunspotPrice_injective`,
  `prop_2_5_uncountable`): with only the exact Fisher equation an interest-rate peg has
  uncountably many price paths with the same `P_0`. Cochrane p. 33 ("inflation is stable and
  determinate under a peg"): adding the government valuation equation, `PegEqm`, there is
  exactly one equilibrium for every adapted peg `i > −1` and every bounded surplus process with
  present value bounded away from zero (`peg_ftpl_existsUnique`); in the same coin-flip economy
  the equilibrium set is a singleton inside Woodford's uncountable set (`peg_contrast`).
* **Rules.** Woodford's Proposition 2.6 (restated: `prop_2_6_iff`, bounded solutions are unique
  iff `|φ_π| > 1`) against `LinearFTMP.rule_existsUnique` (unique for every `θ`):
  `rule_solves_eq26`, `taylor_contrast`, and in the coin-flip economy with `π_0 = 0` and
  `|θ| < 1`: uncountably many bounded solutions of Woodford's (2.6) versus exactly one
  equilibrium of (2.24)+(2.21) (`taylor_contrast_coin`).
* **Passive fiscal policy.** Woodford's (4.2) (restated: `ricardian_tvc`): a Ricardian rule makes
  the transversality condition hold along every path. Then the valuation equation holds for
  every initial price level (`passive_any_price`), while with exogenous surpluses it pins the
  price level (`active_unique_value`).
* **Timing.** Woodford's (4.1) `Budget` (restated) is Cochrane's (2.4) with `B_t = (1 + i_t) D_t`
  and `P_t s_t = T_t − P_t G_t` (`timing_link`); Woodford's real debt `b_t` is Cochrane's
  `V_t = B_t/P_t`, and `b_t/Π_{t+1} = B_t/P_{t+1}` (`timing_real`).
-/

namespace Cochrane.IntertemporalModel.Links

open Filter Topology ExpectationTools

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Woodford, Chapter 2, Proposition 2.5 (restated) -/

/-- Woodford (2003), eq. (1.21), p. 71 (restated from the Woodford Chapter 2 project): the exact
Fisher equation `1 + i_t = β⁻¹ {E_t[u_c,t+1 P_t/(u_c,t P_{t+1})]}⁻¹`. -/
def FisherExactW (β : ℝ) (i uc P : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, 1 + i t ω = β⁻¹ * (𝔼.E t (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) ω)⁻¹

/-- Cochrane (2023), eq. (2.3), p. 22 (constant marginal utility `c_t = y`) is Woodford's (1.21)
with `u_c ≡ 1`: `1/(1 + i_t) = β E_t(P_t/P_{t+1})` iff `1 + i_t = β⁻¹ [E_t(P_t/P_{t+1})]⁻¹`. -/
theorem fisher_iff_W {β : ℝ} {i P : ℕ → Ω → ℝ} {t : ℕ} :
    LinearFTMP.FisherExact 𝔼 β i P t ↔ FisherExactW 𝔼 β i (fun _ _ => 1) P t := by
  refine forall_congr' fun ω => ?_
  simp only [one_mul, one_div]
  rw [inv_eq_iff_eq_inv, mul_inv]

/-- Woodford (2003), §A.6, p. 639 (restated): `K_t = E_t[u_c,t+1(1 − ν_{t+1})]`. -/
noncomputable def Kexp (uc ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E t (fun ω => uc (t + 1) ω * (1 - ν (t + 1) ω))

/-- Woodford (2003), §A.6, p. 639 (restated): gross inflation
`Π_{t+1} = β(1 + i_t) K_t / (u_c,t (1 − ν_{t+1}))`. -/
noncomputable def grossInfl (β : ℝ) (i uc ν : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * (1 + i t ω) * Kexp 𝔼 uc ν t ω / (uc t ω * (1 - ν (t + 1) ω))

/-- Woodford (2003), §A.6, p. 639 (restated): the sunspot price path, `P_{t+1} = P_t Π_{t+1}`. -/
noncomputable def sunspotPrice (β : ℝ) (P0 : Ω → ℝ) (i uc ν : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => P0
  | t + 1 => fun ω => sunspotPrice β P0 i uc ν t ω * grossInfl 𝔼 β i uc ν t ω

/-- Woodford (2003), §A.6, p. 639 (restated): `u_c(1 − ν) ≥ m` implies `K_t ≥ m`. -/
theorem Kexp_ge {m : ℝ} {uc ν : ℕ → Ω → ℝ} (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ)
    (ω : Ω) : m ≤ Kexp 𝔼 uc ν t ω :=
  const_le_E 𝔼 (fun ω => hm (t + 1) ω) t ω

/-- Woodford (2003), §A.6, p. 639 (restated): gross inflation is positive. -/
theorem grossInfl_pos {β m : ℝ} (hβ : 0 < β) (hm0 : 0 < m) {i uc ν : ℕ → Ω → ℝ}
    (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) (ω : Ω) : 0 < grossInfl 𝔼 β i uc ν t ω := by
  have hK := Kexp_ge 𝔼 hm t ω
  have h1 := hi t ω
  have h2 := huc t ω
  have h3 : 0 < 1 - ν (t + 1) ω := by linarith [hν (t + 1) ω]
  exact div_pos (mul_pos (mul_pos hβ h1) (lt_of_lt_of_le hm0 hK)) (mul_pos h2 h3)

/-- Woodford (2003), §A.6, p. 639 (restated): the sunspot price path is positive. -/
theorem sunspotPrice_pos {β m : ℝ} (hβ : 0 < β) (hm0 : 0 < m) {P0 : Ω → ℝ}
    (hP0 : ∀ ω, 0 < P0 ω) {i uc ν : ℕ → Ω → ℝ} (hi : ∀ t ω, 0 < 1 + i t ω)
    (huc : ∀ t ω, 0 < uc t ω) (hν : ∀ t ω, ν t ω < 1)
    (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) (ω : Ω) :
    0 < sunspotPrice 𝔼 β P0 i uc ν t ω := by
  induction t with
  | zero => exact hP0 ω
  | succ t ih => exact mul_pos ih (grossInfl_pos 𝔼 hβ hm0 hi huc hν hm t ω)

/-- Woodford (2003), Proposition 2.5 and §A.6, pp. 87, 639 (restated): for an exogenous rate
target and any process `ν < 1` with `u_c(1 − ν) ≥ m > 0`, the sunspot price path satisfies the
exact Fisher equation (1.21) at every date. -/
theorem sunspot_fisher (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β m : ℝ} (hβ : 0 < β)
    (hm0 : 0 < m) {P0 : Ω → ℝ} (hP0 : ∀ ω, 0 < P0 ω) {i uc ν : ℕ → Ω → ℝ}
    (hia : 𝔼.Adapted i) (hi : ∀ t ω, 0 < 1 + i t ω) (huc : ∀ t ω, 0 < uc t ω)
    (hν : ∀ t ω, ν t ω < 1) (hm : ∀ t ω, m ≤ uc t ω * (1 - ν t ω)) (t : ℕ) :
    FisherExactW 𝔼 β i uc (sunspotPrice 𝔼 β P0 i uc ν) t := by
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

/-- Woodford (2003), §A.6, p. 639 (restated): distinct martingale differences give distinct
sunspot price paths. -/
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

/-- Woodford (2003), Proposition 2.5, p. 87 (restated from the Woodford Chapter 2 project): in
the coin-flip economy with `u_c ≡ 1`, a peg `i ≡ β⁻¹ − 1` and `P_0 = 1`, there are uncountably
many solutions of the exact Fisher equation (the sunspots `ν = s ε`, `s ∈ (−1, 1)`). -/
theorem prop_2_5_uncountable {β : ℝ} (hβ : 0 < β) :
    ¬ {P : ℕ → Bool × Bool → ℝ | (∀ t, FisherExactW ExpectationsFiniteTree.coinSystem β
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
  have hmaps : Set.MapsTo f (Set.Ioo (-1) 1) {P | (∀ t, FisherExactW 𝔼c β
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

/-! ### Cochrane p. 33: under the fiscal theory the peg is determinate -/

/-- Cochrane (2023), eqs. (2.3) and (2.7), pp. 22, 33: an equilibrium `(P, B)` under the
interest-rate peg `i`, with initial debt `B_{−1}` and present value of surpluses
`PV_t = E_t ∑ βʲ s_{t+j}`: positive adapted prices, adapted debt, the exact Fisher equation at
every date, and the valuation equation `B_{t−1}/P_t = PV_t` at every date. -/
def PegEqm (β : ℝ) (i PV : ℕ → Ω → ℝ) (Bm1 : ℝ) (P B : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted P ∧ 𝔼.Adapted B ∧ (∀ t ω, 0 < P t ω) ∧ (∀ t, LinearFTMP.FisherExact 𝔼 β i P t) ∧
    (∀ ω, Bm1 / P 0 ω = PV 0 ω) ∧ ∀ t ω, B t ω / P (t + 1) ω = PV (t + 1) ω

/-- Cochrane (2023), pp. 31–33 (debt follows from the rate target, cf. (2.18)): in any peg
equilibrium `B_t = β(1 + i_t) P_t E_t PV_{t+1}` and `P_{t+1} = B_t/PV_{t+1}`. -/
theorem pegEqm_debt (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β : ℝ}
    {i PV P B : ℕ → Ω → ℝ} {Bm1 c : ℝ} (hc : 0 < c) (hPV : ∀ t ω, c ≤ PV t ω)
    (hi : ∀ t ω, 0 < 1 + i t ω) (h : PegEqm 𝔼 β i PV Bm1 P B) (t : ℕ) (ω : Ω) :
    B t ω = β * (1 + i t ω) * (P t ω * 𝔼.E t (PV (t + 1)) ω) ∧
      P (t + 1) ω = B t ω / PV (t + 1) ω := by
  obtain ⟨hPa, hBa, hPpos, hfis, -, hval⟩ := h
  have hPV1 : ∀ ω', 0 < PV (t + 1) ω' := fun ω' => hc.trans_le (hPV (t + 1) ω')
  have hBpos : ∀ ω', 0 < B t ω' := fun ω' => by
    have h := hval t ω'
    rw [div_eq_iff (hPpos (t + 1) ω').ne'] at h
    rw [h]
    exact mul_pos (hPV1 ω') (hPpos (t + 1) ω')
  have hP1 : ∀ ω', P (t + 1) ω' = B t ω' / PV (t + 1) ω' := fun ω' => by
    have h := hval t ω'
    have hp := (hPpos (t + 1) ω').ne'
    rw [eq_div_iff (hPV1 ω').ne', ← h]
    field_simp
  have hratio : (fun ω' => P t ω' / P (t + 1) ω') =
      (fun ω' => P t ω' / B t ω') * PV (t + 1) := by
    funext ω'
    rw [hP1 ω', Pi.mul_apply, div_div_eq_mul_div, mul_div_right_comm]
  have hk : 𝔼.E t (fun ω' => P t ω' / B t ω') = fun ω' => P t ω' / B t ω' :=
    hC t (fun a b => a / b) (P t) (B t) (hPa t) (hBa t)
  have hf := hfis t ω
  rw [hratio, hPO t _ _ hk, Pi.mul_apply] at hf
  have hE := hc.trans_le (const_le_E 𝔼 (hPV (t + 1)) t ω)
  have h1 := hi t ω
  have h2 := hBpos ω
  refine ⟨?_, hP1 ω⟩
  field_simp at hf
  linarith

/-- Cochrane (2023), p. 33: the candidate equilibrium price path, `P_0 = B_{−1}/PV_0`,
`P_{t+1} = β(1 + i_t) P_t E_t PV_{t+1} / PV_{t+1}`. -/
noncomputable def ftplPrice (β : ℝ) (i PV : ℕ → Ω → ℝ) (Bm1 : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => Bm1 / PV 0 ω
  | t + 1 => fun ω => β * (1 + i t ω) * (ftplPrice β i PV Bm1 t ω * 𝔼.E t (PV (t + 1)) ω) /
      PV (t + 1) ω

/-- Cochrane (2023), p. 33: the candidate equilibrium debt `B_t = β(1 + i_t) P_t E_t PV_{t+1}`. -/
noncomputable def ftplDebt (β : ℝ) (i PV : ℕ → Ω → ℝ) (Bm1 : ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => β * (1 + i t ω) * (ftplPrice 𝔼 β i PV Bm1 t ω * 𝔼.E t (PV (t + 1)) ω)

/-- Cochrane (2023), p. 33 ("inflation is stable and determinate under a peg", fiscal theory):
for every adapted peg with `1 + i_t > 0`, adapted present values bounded below by `c > 0` and
initial debt `B_{−1} > 0`, there is exactly one peg equilibrium `(P, B)`. Uses the pull-out and
closure properties of the expectations (both hold on finite event trees). -/
theorem peg_ftpl_existsUnique (hPO : 𝔼.PullOut) (hC : Closed 𝔼) {β : ℝ} (hβ : 0 < β)
    {i PV : ℕ → Ω → ℝ} (hia : 𝔼.Adapted i) (hi : ∀ t ω, 0 < 1 + i t ω) (hPVa : 𝔼.Adapted PV)
    {c : ℝ} (hc : 0 < c) (hPV : ∀ t ω, c ≤ PV t ω) {Bm1 : ℝ} (hB : 0 < Bm1) :
    ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), PegEqm 𝔼 β i PV Bm1 q.1 q.2 := by
  have hPVp : ∀ t ω, 0 < PV t ω := fun t ω => hc.trans_le (hPV t ω)
  have hEp : ∀ t ω, 0 < 𝔼.E t (PV (t + 1)) ω := fun t ω =>
    hc.trans_le (const_le_E 𝔼 (hPV (t + 1)) t ω)
  have hpos : ∀ t ω, 0 < ftplPrice 𝔼 β i PV Bm1 t ω := by
    intro t
    induction t with
    | zero => exact fun ω => div_pos hB (hPVp 0 ω)
    | succ t ih =>
      intro ω
      exact div_pos (mul_pos (mul_pos hβ (hi t ω)) (mul_pos (ih ω) (hEp t ω))) (hPVp _ ω)
  have hdebt_of : ∀ t, 𝔼.E t (ftplPrice 𝔼 β i PV Bm1 t) = ftplPrice 𝔼 β i PV Bm1 t →
      𝔼.E t (ftplDebt 𝔼 β i PV Bm1 t) = ftplDebt 𝔼 β i PV Bm1 t := by
    intro t ht
    have hy := hC t (fun a b => a * b) (ftplPrice 𝔼 β i PV Bm1 t) (𝔼.E t (PV (t + 1))) ht
      (𝔼.E_E_self t _)
    exact hC t (fun a b => β * (1 + a) * b) (i t) _ (hia t) hy
  have hPa : 𝔼.Adapted (ftplPrice 𝔼 β i PV Bm1) := by
    intro t
    induction t with
    | zero => exact hC 0 (fun a _ => Bm1 / a) (PV 0) (PV 0) (hPVa 0) (hPVa 0)
    | succ t ih =>
      exact hC (t + 1) (fun a b => a / b) (ftplDebt 𝔼 β i PV Bm1 t) (PV (t + 1))
        (ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hdebt_of t ih)) (hPVa (t + 1))
  have hBa : 𝔼.Adapted (ftplDebt 𝔼 β i PV Bm1) := fun t => hdebt_of t (hPa t)
  have hDpos : ∀ t ω, 0 < ftplDebt 𝔼 β i PV Bm1 t ω := fun t ω =>
    mul_pos (mul_pos hβ (hi t ω)) (mul_pos (hpos t ω) (hEp t ω))
  have heqm : PegEqm 𝔼 β i PV Bm1 (ftplPrice 𝔼 β i PV Bm1) (ftplDebt 𝔼 β i PV Bm1) := by
    refine ⟨hPa, hBa, hpos, fun t ω => ?_, fun ω => ?_, fun t ω => ?_⟩
    · have hratio : (fun ω' => ftplPrice 𝔼 β i PV Bm1 t ω' / ftplPrice 𝔼 β i PV Bm1 (t + 1) ω') =
          (fun ω' => ftplPrice 𝔼 β i PV Bm1 t ω' / ftplDebt 𝔼 β i PV Bm1 t ω') * PV (t + 1) := by
        funext ω'
        change _ / (ftplDebt 𝔼 β i PV Bm1 t ω' / PV (t + 1) ω') = _
        rw [Pi.mul_apply, div_div_eq_mul_div, mul_div_right_comm]
      have hk := hC t (fun a b => a / b) _ _ (hPa t) (hBa t)
      rw [hratio, hPO t _ _ hk, Pi.mul_apply]
      have h1 := hi t ω
      have h2 := hpos t ω
      have h3 := hEp t ω
      unfold ftplDebt
      field_simp
    · change Bm1 / (Bm1 / PV 0 ω) = PV 0 ω
      have := hPVp 0 ω
      field_simp
    · change ftplDebt 𝔼 β i PV Bm1 t ω / (ftplDebt 𝔼 β i PV Bm1 t ω / PV (t + 1) ω) = _
      have := hDpos t ω
      have := hPVp (t + 1) ω
      field_simp
  refine ⟨(ftplPrice 𝔼 β i PV Bm1, ftplDebt 𝔼 β i PV Bm1), heqm, ?_⟩
  rintro ⟨P, B⟩ h
  dsimp only at h
  have hd := pegEqm_debt 𝔼 hPO hC hc hPV hi h
  have hP : P = ftplPrice 𝔼 β i PV Bm1 := by
    funext t ω
    induction t generalizing ω with
    | zero =>
      have h0 := h.2.2.2.2.1 ω
      have hp := h.2.2.1 0 ω
      change P 0 ω = Bm1 / PV 0 ω
      rw [div_eq_iff hp.ne'] at h0
      rw [eq_div_iff (hPVp 0 ω).ne', h0, mul_comm]
    | succ t ih =>
      change P (t + 1) ω = β * (1 + i t ω) * (ftplPrice 𝔼 β i PV Bm1 t ω *
        𝔼.E t (PV (t + 1)) ω) / PV (t + 1) ω
      rw [(hd t ω).2, (hd t ω).1]
      rw [show P t = ftplPrice 𝔼 β i PV Bm1 t from funext ih]
  refine Prod.ext hP ?_
  funext t ω
  change B t ω = ftplDebt 𝔼 β i PV Bm1 t ω
  rw [(hd t ω).1, hP]
  rfl

/-- Cochrane (2023), p. 33: with constant surpluses `s ≡ 1 − β` (`0 ≤ β < 1`) the present value
`PV_t = ∑ βᵏ E_t s_{t+k}` is `1` at every date and state. -/
theorem pv_const {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (t : ℕ) :
    𝔼.forwardSeries β (fun _ _ => 1 - β) t = fun _ => 1 := by
  funext ω
  change ∑' k, β ^ k * 𝔼.E t (fun _ => 1 - β) ω = 1
  simp only [𝔼.const]
  rw [tsum_mul_right, tsum_geometric_of_lt_one h0 h1, inv_mul_cancel₀ (by linarith)]

/-- Cochrane (2023), p. 33 against Woodford (2003), Proposition 2.5, p. 87 ("the fiscal theory
overturns" the indeterminacy of pegs): in the same coin-flip economy with the peg
`i ≡ β⁻¹ − 1` and `u_c ≡ 1`, (a) the exact Fisher equation alone has uncountably many price
paths with `P_0 = 1`; (b) adding the valuation equation (`s ≡ 1 − β`, `B_{−1} = 1`) leaves exactly
one equilibrium price path, `P ≡ 1`; (c) that path is one of the paths in (a). -/
theorem peg_contrast {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    ¬ {P : ℕ → Bool × Bool → ℝ | (∀ t, FisherExactW ExpectationsFiniteTree.coinSystem β
        (fun _ _ => β⁻¹ - 1) (fun _ _ => 1) P t) ∧ P 0 = fun _ => 1}.Countable ∧
      {P : ℕ → Bool × Bool → ℝ | ∃ B, PegEqm ExpectationsFiniteTree.coinSystem β
        (fun _ _ => β⁻¹ - 1) (ExpectationsFiniteTree.coinSystem.forwardSeries β
          (fun _ _ => 1 - β)) 1 P B} = {fun _ _ => 1} ∧
      ∀ P B, PegEqm ExpectationsFiniteTree.coinSystem β (fun _ _ => β⁻¹ - 1)
        (ExpectationsFiniteTree.coinSystem.forwardSeries β (fun _ _ => 1 - β)) 1 P B →
        (∀ t, FisherExactW ExpectationsFiniteTree.coinSystem β (fun _ _ => β⁻¹ - 1)
          (fun _ _ => 1) P t) ∧ P 0 = fun _ => 1 := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem
  have hPO : 𝔼c.PullOut := ExpectationsFiniteTree.finiteTree_pullOut _
  have hC : Closed 𝔼c := finiteTree_closed _
  have hpv := pv_const 𝔼c hβ.le hβ1
  have hia : 𝔼c.Adapted (fun _ _ => β⁻¹ - 1) := fun t => 𝔼c.const t _
  have hi : ∀ (t : ℕ) (ω : Bool × Bool), 0 < 1 + (fun (_ : ℕ) (_ : Bool × Bool) => β⁻¹ - 1) t ω :=
    fun _ _ => by simp [hβ]
  have hPVa : 𝔼c.Adapted (𝔼c.forwardSeries β (fun _ _ => 1 - β)) := fun t => by
    rw [hpv t, 𝔼c.const]
  have hPV : ∀ t ω, (1 : ℝ) ≤ 𝔼c.forwardSeries β (fun _ _ => 1 - β) t ω := fun t ω => by
    rw [hpv t]
  have hone : PegEqm 𝔼c β (fun _ _ => β⁻¹ - 1) (𝔼c.forwardSeries β (fun _ _ => 1 - β)) 1
      (fun _ _ => 1) (fun _ _ => 1) := by
    refine ⟨fun t => 𝔼c.const t 1, fun t => 𝔼c.const t 1, fun _ _ => one_pos, fun t ω => ?_,
      fun ω => ?_, fun t ω => ?_⟩
    · simp only [div_one]
      rw [𝔼c.const]
      field_simp
      ring
    · rw [hpv 0, div_one]
    · rw [hpv (t + 1), div_one]
  have hu := peg_ftpl_existsUnique 𝔼c hPO hC hβ hia hi hPVa one_pos hPV one_pos
  have hfish : ∀ P B, PegEqm 𝔼c β (fun _ _ => β⁻¹ - 1) (𝔼c.forwardSeries β (fun _ _ => 1 - β)) 1
      P B → (∀ t, FisherExactW 𝔼c β (fun _ _ => β⁻¹ - 1) (fun _ _ => 1) P t) ∧
        P 0 = fun _ => 1 := by
    intro P B h
    refine ⟨fun t => (fisher_iff_W 𝔼c).mp (h.2.2.2.1 t), ?_⟩
    funext ω
    have h0 := h.2.2.2.2.1 ω
    rw [hpv 0, div_eq_one_iff_eq (h.2.2.1 0 ω).ne'] at h0
    exact h0.symm
  refine ⟨prop_2_5_uncountable hβ, ?_, hfish⟩
  ext P
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨B, h⟩
    exact congrArg Prod.fst (hu.unique (y₁ := (P, B)) (y₂ := (fun _ _ => 1, fun _ _ => 1)) h hone)
  · rintro rfl
    exact ⟨_, hone⟩

/-! ### Woodford, Chapter 2, Proposition 2.6 (restated) and the Taylor principle -/

/-- Woodford (2003), eq. (2.6), p. 91 (restated from the Woodford Chapter 2 project):
`φ_π π_t = E_t π_{t+1} + (r̂_t − ī_t)`. Used for Cochrane (2023), §2.6. -/
def Eq26 (φπ : ℝ) (r ib π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φπ • π t = 𝔼.E t (π (t + 1)) + (r t - ib t)

/-- Woodford (2003), eq. (2.6), App. A, p. 636 (restated): for `φ_π ≠ 0`, (2.6) is the forward
equation with `a = φ_π⁻¹`, `u_t = φ_π⁻¹(r̂_t − ī_t)`. Used for Cochrane (2023), §2.6. -/
theorem eq26_iff_solves {φπ : ℝ} (hφ : φπ ≠ 0) {r ib π : ℕ → Ω → ℝ} :
    Eq26 𝔼 φπ r ib π ↔ ForwardSolution.Solves 𝔼 φπ⁻¹ (fun t => φπ⁻¹ • (r t - ib t)) π := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp

/-- Woodford (2003), Proposition 2.6, p. 91 (restated from the Woodford Chapter 2 project):
(2.6) has a unique bounded solution for every bounded adapted `{r̂, ī}` iff `|φ_π| > 1`. -/
theorem prop_2_6_iff [Nonempty Ω] (φπ : ℝ) :
    (∀ r ib : ℕ → Ω → ℝ, BoundedProc r → BoundedProc ib → 𝔼.Adapted r → 𝔼.Adapted ib →
      ∃! π, BoundedProc π ∧ Eq26 𝔼 φπ r ib π) ↔ 1 < |φπ| := by
  constructor
  · intro h
    by_contra hc
    have hc' : |φπ| ≤ 1 := not_lt.mp hc
    have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
    obtain ⟨π, -, hu⟩ := h 0 0 hzb hzb (fun t => map_zero _) (fun t => map_zero _)
    have e0 := hu 0 ⟨hzb, fun t => by simp⟩
    have e1 := hu (fun t _ => φπ ^ t) ⟨⟨1, fun t _ => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc'⟩, fun t => by
        rw [𝔼.const]
        funext ω
        simp [pow_succ]
        ring⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (e1.trans e0.symm) 0) ω
    simp at this
  · intro hφ r ib hrb hib hra hia
    have hne : φπ ≠ 0 := by
      intro h
      rw [h, abs_zero] at hφ
      linarith
    have ha : |φπ⁻¹| < 1 := by
      rw [abs_inv]
      exact inv_lt_one_of_one_lt₀ hφ
    obtain ⟨Mr, hr⟩ := hrb
    obtain ⟨Mi, hi⟩ := hib
    have hub : BoundedProc (fun t => φπ⁻¹ • (r t - ib t)) := by
      refine ⟨Mr + Mi, fun t ω => ?_⟩
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
      calc |φπ⁻¹| * |r t ω - ib t ω| ≤ 1 * |r t ω - ib t ω| := by gcongr
        _ ≤ Mr + Mi := by
          rw [one_mul]; exact (abs_sub _ _).trans (add_le_add (hr t ω) (hi t ω))
    have hua : 𝔼.Adapted (fun t => φπ⁻¹ • (r t - ib t)) := by
      intro t
      simp only [map_smul, map_sub, hra t, hia t]
    obtain ⟨z, hz, hu⟩ := ForwardSolution.existsUnique_bounded 𝔼 ha hub hua
    exact ⟨z, ⟨hz.1, (eq26_iff_solves 𝔼 hne).mpr hz.2⟩,
      fun π hπ => hu π ⟨hπ.1, (eq26_iff_solves 𝔼 hne).mp hπ.2⟩⟩

/-- Woodford (2003), App. A, p. 637 (restated): the family `π_0` given,
`π_{t+1} = φ_π π_t − (r̂_t − ī_t) + ν_{t+1}`. Used for Cochrane (2023), §2.6. -/
def sunspotInfl (φπ : ℝ) (r ib ν : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => φπ • sunspotInfl φπ r ib ν π0 t - (r t - ib t) + ν (t + 1)

/-- Woodford (2003), Proposition 2.6, p. 91 (restated): for any `φ_π` and any martingale
difference `ν`, `sunspotInfl` solves (2.6). Used for Cochrane (2023), §2.6. -/
theorem sunspotInfl_solves {φπ : ℝ} {r ib ν : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hra : 𝔼.Adapted r) (hia : 𝔼.Adapted ib) (hνa : 𝔼.Adapted ν)
    (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) : Eq26 𝔼 φπ r ib (sunspotInfl φπ r ib ν π0) := by
  have had : 𝔼.Adapted (sunspotInfl φπ r ib ν π0) := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      simp only [sunspotInfl, map_add, map_sub, map_smul,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hra t),
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hia t), hνa (t + 1)]
  intro t
  simp only [sunspotInfl, map_add, map_sub, map_smul, had t, hra t, hia t, hmd t, add_zero]
  abel

/-- Woodford (2003), Proposition 2.6, p. 91 (restated): for `|φ_π| < 1` the family is bounded
when `π_0`, `r̂ − ī` and `ν` are. Used for Cochrane (2023), §2.6. -/
theorem sunspotInfl_bounded {φπ B G Mν : ℝ} (hφ : |φπ| < 1) {r ib ν : ℕ → Ω → ℝ}
    {π0 : Ω → ℝ} (h0 : ∀ ω, |π0 ω| ≤ B) (hg : ∀ t ω, |r t ω - ib t ω| ≤ G)
    (hν : ∀ t ω, |ν t ω| ≤ Mν) : BoundedProc (sunspotInfl φπ r ib ν π0) := by
  set K := |B| + (|G| + |Mν|) / (1 - |φπ|) with hK
  have h1 : 0 < 1 - |φπ| := by linarith
  have hfrac : 0 ≤ (|G| + |Mν|) / (1 - |φπ|) := div_nonneg (by positivity) h1.le
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact fun ω => (h0 ω).trans ((le_abs_self B).trans (by linarith))
  | succ t ih =>
    intro ω
    simp only [sunspotInfl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have ha : |φπ * sunspotInfl φπ r ib ν π0 t ω| ≤ |φπ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have hb := (hg t ω).trans (le_abs_self G)
    have hc := (hν (t + 1) ω).trans (le_abs_self Mν)
    have hKe : K * (1 - |φπ|) = |B| * (1 - |φπ|) + (|G| + |Mν|) := by
      rw [hK, add_mul, div_mul_cancel₀ _ h1.ne']
    have hB : 0 ≤ |B| * (1 - |φπ|) := mul_nonneg (abs_nonneg B) h1.le
    calc |φπ * sunspotInfl φπ r ib ν π0 t ω - (r t ω - ib t ω) + ν (t + 1) ω|
        ≤ |φπ * sunspotInfl φπ r ib ν π0 t ω - (r t ω - ib t ω)| + |ν (t + 1) ω| :=
          abs_add_le _ _
      _ ≤ |φπ * sunspotInfl φπ r ib ν π0 t ω| + |r t ω - ib t ω| + |ν (t + 1) ω| := by
          gcongr; exact abs_sub _ _
      _ ≤ K := by nlinarith

/-- Cochrane (2023), eq. (2.24), p. 40, is Woodford (2003), eq. (2.6), p. 91, with `φ_π = θ`,
`r̂ = 0` and `ī = u`: `E_t π_{t+1} = θ π_t + u_t` iff `θ π_t = E_t π_{t+1} + (0 − u_t)`. -/
theorem eq26_iff_224 {θ : ℝ} {u π : ℕ → Ω → ℝ} :
    Eq26 𝔼 θ 0 u π ↔ ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + u t := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §2.6, p. 40, against Woodford (2003), Proposition 2.6: every equilibrium of
(2.24)+(2.21) is a solution of Woodford's (2.6) (`φ_π = θ`, `r̂ = 0`, `ī = u`); the valuation
equation (2.21) selects one of them. -/
theorem rule_solves_eq26 {θ : ℝ} {u ε π : ℕ → Ω → ℝ} (hm : LinearFTMP.Eq224 𝔼 θ u ε π) :
    Eq26 𝔼 θ 0 u π :=
  (eq26_iff_224 𝔼).mpr fun t => (hm t).1

/-- Cochrane (2023), §2.6, pp. 39–40 ("no Taylor principle needed") against Woodford (2003),
Proposition 2.6: for `|θ| ≤ 1` the rule fails Woodford's determinacy criterion (bounded
solutions of (2.6) are not unique for all bounded disturbances), yet the fiscal-theory model
(2.20)–(2.22) has exactly one equilibrium for every disturbance, every fiscal shock and every
`π_0`. -/
theorem taylor_contrast [Nonempty Ω] {θ : ℝ} (hθ : |θ| ≤ 1) :
    (¬ ∀ r ib : ℕ → Ω → ℝ, BoundedProc r → BoundedProc ib → 𝔼.Adapted r → 𝔼.Adapted ib →
      ∃! π, BoundedProc π ∧ Eq26 𝔼 θ r ib π) ∧
    ∀ (u ε : ℕ → Ω → ℝ) (π0 : Ω → ℝ), 𝔼.E 0 π0 = π0 → 𝔼.Adapted u → LinearFTMP.IsShock 𝔼 ε →
      ∃! q : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), 𝔼.Adapted q.1 ∧ q.1 0 = π0 ∧
        LinearFTMP.RuleModel 𝔼 θ q.2 u ε q.1 :=
  ⟨fun h => absurd ((prop_2_6_iff 𝔼 θ).mp h) (not_lt.mpr hθ),
    fun _ _ _ h0 hu hε => LinearFTMP.rule_existsUnique 𝔼 θ h0 hu hε⟩

/-- Cochrane (2023), §2.6, against Woodford (2003), Proposition 2.6 ("if instead `0 ≤ φ_π < 1`
... indeterminate"), in the coin-flip economy with no disturbances, `|θ| < 1` and `π_0 = 0`:
Woodford's (2.6) has uncountably many bounded solutions (sunspots `ν = s ε`), while the fiscal
theory's (2.24)+(2.21) with no fiscal shock has exactly one, `π ≡ 0`. -/
theorem taylor_contrast_coin {θ : ℝ} (hθ : |θ| < 1) :
    ¬ {π : ℕ → Bool × Bool → ℝ | BoundedProc π ∧ Eq26 ExpectationsFiniteTree.coinSystem θ 0 0 π ∧
        π 0 = 0}.Countable ∧
      {π : ℕ → Bool × Bool → ℝ | ExpectationsFiniteTree.coinSystem.Adapted π ∧ π 0 = 0 ∧
        LinearFTMP.Eq224 ExpectationsFiniteTree.coinSystem θ 0 0 π} = {0} := by
  set 𝔼c := ExpectationsFiniteTree.coinSystem
  have hAR := ExpectationsFiniteTree.coinAR1_isAR1 0
  have hzero : 𝔼c.Adapted (0 : ℕ → Bool × Bool → ℝ) := fun t => map_zero _
  have hb : ∀ t ω, |ExpectationsFiniteTree.coinAR1 0 t ω| ≤ 1 := by
    intro t ω
    cases t with
    | zero => simp [ExpectationsFiniteTree.coinAR1]
    | succ t =>
      simp only [ExpectationsFiniteTree.coinAR1, zero_mul, zero_add,
        ExpectationsFiniteTree.coinShock]
      split_ifs <;> norm_num
  have hs0 : LinearFTMP.IsShock 𝔼c 0 := ⟨fun t => map_zero _, fun t => map_zero _⟩
  constructor
  · let f : ℝ → ℕ → Bool × Bool → ℝ := fun s =>
      sunspotInfl θ 0 0 (fun t => s • ExpectationsFiniteTree.coinAR1 0 t) (fun _ => 0)
    have hmaps : Set.MapsTo f Set.univ {π | BoundedProc π ∧ Eq26 𝔼c θ 0 0 π ∧ π 0 = 0} := by
      intro s _
      refine ⟨sunspotInfl_bounded hθ (B := 0) (G := 0) (Mν := |s|) (fun _ => by simp)
        (fun _ _ => by simp) (fun t ω => ?_), sunspotInfl_solves 𝔼c (𝔼c.const 0 0) hzero hzero
        (fun t => by rw [map_smul, hAR.1 t]) (fun t => ?_), rfl⟩
      · simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
        nlinarith [hb t ω, abs_nonneg s]
      · rw [map_smul, hAR.2 t, zero_smul, smul_zero]
    have hinj : Set.InjOn f Set.univ := by
      intro s _ s' _ h
      have := congrFun (congrFun h 1) (true, true)
      simpa [f, sunspotInfl, ExpectationsFiniteTree.coinAR1, ExpectationsFiniteTree.coinShock]
        using this
    intro hcount
    exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)
  · ext π
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ha, h0, hm⟩
      have h := (LinearFTMP.eq224_iff 𝔼c ha hzero hs0).mp hm
      funext t
      induction t with
      | zero => exact h0
      | succ t ih =>
        rw [h t, ih]
        simp
    · rintro rfl
      refine ⟨hzero, rfl, (LinearFTMP.eq224_iff 𝔼c hzero hzero hs0).mpr fun t => ?_⟩
      simp

/-! ### Woodford (4.2) (restated) and passive fiscal policy -/

/-- Woodford (2003), §1, p. 66 (restated from the Woodford Chapter 2 project): the
perfect-foresight discount factor `Q_{t,T} = ∏_{s=t}^{T−1} Q_{s,s+1}`. Used for Cochrane (2023),
p. 39. -/
def discount (q : ℕ → ℝ) (t T : ℕ) : ℝ := ∏ s ∈ Finset.Ico t T, q s

/-- Woodford (2003), (4.2), p. 124 (restated): under `T_t = αW_t − Δ_tM_t` the government budget
gives `Q_{t,t+1}W_{t+1} = (1 − α)W_t`. Used for Cochrane (2023), p. 39. -/
theorem ricardian_step {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (t : ℕ)
    (hgov : q t * W (t + 1) = W t - Tx t - Δ t * M t)
    (hrule : Tx t = α * W t - Δ t * M t) : q t * W (t + 1) = (1 - α) * W t := by
  rw [hgov, hrule]; ring

/-- Woodford (2003), (4.2), p. 124 (restated): `Q_{t,t+n}W_{t+n} = (1 − α)ⁿ W_t`. Used for
Cochrane (2023), p. 39. -/
theorem ricardian_discounted {q W Tx Δ M : ℕ → ℝ} {α : ℝ}
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = α * W s - Δ s * M s) (t n : ℕ) :
    discount q t (t + n) * W (t + n) = (1 - α) ^ n * W t := by
  induction n with
  | zero => simp [discount]
  | succ n ih =>
    have hd : discount q t (t + (n + 1)) = discount q t (t + n) * q (t + n) := by
      simp only [discount, ← add_assoc]
      exact Finset.prod_Ico_succ_top (Nat.le_add_right t n) q
    rw [hd, mul_assoc, ← add_assoc, ricardian_step (t + n) (hgov _) (hrule _), ← mul_assoc,
      mul_comm (discount q t (t + n)), mul_assoc, ih]
    ring

/-- Woodford (2003), (4.2), p. 124 (restated from the Woodford Chapter 2 project): for
`0 < α ≤ 1` the transversality condition `Q_{t,T}W_T → 0` holds along every path. Used for
Cochrane (2023), p. 39. -/
theorem ricardian_tvc {q W Tx Δ M : ℕ → ℝ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hgov : ∀ s, q s * W (s + 1) = W s - Tx s - Δ s * M s)
    (hrule : ∀ s, Tx s = α * W s - Δ s * M s) (t : ℕ) :
    Tendsto (fun T => discount q t T * W T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T => (1 - α) ^ (T - t) * W t) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - α)
      (by linarith)).comp (tendsto_sub_atTop_nat t)).mul_const (W t)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
  rw [ricardian_discounted hgov hrule t n]
  simp

/-- Cochrane (2023), eq. (2.5) with perfect foresight and A1 (1.1), p. 554: iterating the flow
condition `w_t = s_t + β w_{t+1}` (`w_t = B_{t−1}/P_t`),
`w_0 = ∑_{j<T} βʲ s_j + β^T w_T`: the perfect-foresight case of `Valuation.telescope`. -/
theorem pv_telescope {β : ℝ} {w s : ℕ → ℝ} (hflow : ∀ t, w t = s t + β * w (t + 1)) (T : ℕ) :
    w 0 = ∑ j ∈ Finset.range T, β ^ j * s j + β ^ T * w T := by
  have h := congrFun (Valuation.telescope perfectForesight (x := fun t _ => w t)
    (s := fun t _ => s t) (t := 0) (fun t => funext fun _ => hflow t) rfl T) ()
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zero_add] at h
  exact h

/-- Cochrane (2023), p. 39 (passive fiscal policy) via Woodford (2003), (4.2): with perfect
foresight, the flow condition `w_t = s_t + β w_{t+1}` and the passive rule `s_t = α w_t`
(`0 < α ≤ 1`), Woodford's `ricardian_tvc` gives the transversality condition along every
path, so the valuation equation `w_0 = ∑ βʲ s_j` holds for EVERY initial real debt `w_0`, i.e.
for every price level `P_0 = B_{−1}/w_0`: it no longer determines the price level. -/
theorem passive_any_price {β α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {w s : ℕ → ℝ}
    (hflow : ∀ t, w t = s t + β * w (t + 1)) (hrule : ∀ t, s t = α * w t) :
    HasSum (fun j => β ^ j * s j) (w 0) := by
  have hgov : ∀ t, (fun _ => β) t * w (t + 1) = w t - s t - (fun _ => (0 : ℝ)) t * 0 := by
    intro t
    have := hflow t
    simp only [zero_mul, sub_zero]
    linarith
  have hrule' : ∀ t, s t = α * w t - (fun _ => (0 : ℝ)) t * 0 := by
    intro t
    simp only [mul_zero, sub_zero]
    exact hrule t
  have hdisc : ∀ T, discount (fun _ => β) 0 T = β ^ T := fun T => by
    simp [discount, Finset.prod_const]
  have htvc := ricardian_tvc (q := fun _ => β) (W := w) (Tx := s) (M := fun _ => 0) hα0 hα1
    hgov hrule' 0
  simp only [hdisc] at htvc
  have hpart : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s j) atTop (𝓝 (w 0)) := by
    have := (tendsto_const_nhds (x := w 0)).sub htvc
    rw [sub_zero] at this
    refine this.congr fun T => ?_
    rw [pv_telescope hflow T]
    ring
  have hgeo : ∀ j, β ^ j * s j = α * w 0 * (1 - α) ^ j := by
    intro j
    have h := ricardian_discounted (q := fun _ => β) (W := w) (Tx := s) (M := fun _ => 0)
      hgov hrule' 0 j
    rw [zero_add, hdisc] at h
    rw [hrule j, ← mul_assoc, mul_comm (β ^ j) α, mul_assoc, h]
    ring
  have hsum : Summable (fun j => β ^ j * s j) := by
    simp_rw [hgeo]
    exact (summable_geometric_of_lt_one (by linarith) (by linarith)).mul_left _
  exact (tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hpart) ▸ hsum.hasSum

/-- Cochrane (2023), eqs. (2.5)–(2.7), p. 22, perfect foresight (the active case, contrasting
`passive_any_price`): with surpluses given and `∑ βʲ s_j` summable, the flow condition and the
transversality condition `β^T w_T → 0` pin down `w_0 = ∑ βʲ s_j`, hence the price level. -/
theorem active_unique_value {β : ℝ} {w s : ℕ → ℝ} (hflow : ∀ t, w t = s t + β * w (t + 1))
    (hsum : Summable (fun j => β ^ j * s j))
    (htvc : Tendsto (fun T => β ^ T * w T) atTop (𝓝 0)) : w 0 = ∑' j, β ^ j * s j := by
  have hpart : Tendsto (fun T => ∑ j ∈ Finset.range T, β ^ j * s j) atTop (𝓝 (w 0)) := by
    have := (tendsto_const_nhds (x := w 0)).sub htvc
    rw [sub_zero] at this
    refine this.congr fun T => ?_
    rw [pv_telescope hflow T]
    ring
  exact tendsto_nhds_unique hpart hsum.hasSum.tendsto_sum_nat

/-- Cochrane (2023), A1, p. 555 (the active case): with given summable surpluses, any initial
real debt other than the present value violates the transversality condition. -/
theorem active_tvc_fails {β : ℝ} {w s : ℕ → ℝ} (hflow : ∀ t, w t = s t + β * w (t + 1))
    (hsum : Summable (fun j => β ^ j * s j)) (hne : w 0 ≠ ∑' j, β ^ j * s j) :
    ¬ Tendsto (fun T => β ^ T * w T) atTop (𝓝 0) :=
  fun htvc => hne (active_unique_value hflow hsum htvc)

/-! ### Woodford (4.1) (restated) and the timing of the budget constraint -/

/-- Woodford (2003), eq. (4.1), p. 311 (restated from the Woodford Chapter 4 project):
`D_{t+1} = (1 + i_t) D_t + (P_{t+1} G_{t+1} − T_{t+1})`, with `D_t` the end-of-period market value
of nominal debt. Used for Cochrane (2023), eq. (2.4), p. 22. -/
def Budget (D i P G T : ℕ → ℝ) : Prop :=
  ∀ t, D (t + 1) = (1 + i t) * D t + (P (t + 1) * G (t + 1) - T (t + 1))

/-- Cochrane (2023), eq. (2.4), p. 22, against Woodford (2003), eq. (4.1): with face value
`B_t = (1 + i_t) D_t` (Cochrane's debt sold at `t`, due at `t + 1`, price `Q_t = 1/(1 + i_t)`)
and nominal surplus `P_t s_t = T_t − P_t G_t`, Woodford's budget is Cochrane's
`B_t = P_{t+1} s_{t+1} + Q_{t+1} B_{t+1}`. -/
theorem timing_link {D i P G T B s : ℕ → ℝ} (hi : ∀ t, 1 + i t ≠ 0)
    (hB : ∀ t, B t = (1 + i t) * D t) (hs : ∀ t, P t * s t = T t - P t * G t) :
    Budget D i P G T ↔ ∀ t, B t = P (t + 1) * s (t + 1) + B (t + 1) / (1 + i (t + 1)) := by
  refine forall_congr' fun t => ?_
  rw [hB t, hB (t + 1), hs (t + 1), mul_div_cancel_left₀ _ (hi (t + 1))]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), eqs. (2.5) and (2.17), pp. 22, 35, against Woodford (2003), p. 312: Woodford's
real debt `b_t = (1 + i_t) D_t/P_t` is Cochrane's `V_t = B_t/P_t`, and deflating by gross
inflation `Π_{t+1} = P_{t+1}/P_t` gives Cochrane's `B_t/P_{t+1}` (the left side of (2.5) at
`t + 1`). -/
theorem timing_real {D i P B : ℕ → ℝ} (hP : ∀ t, P t ≠ 0) (hB : ∀ t, B t = (1 + i t) * D t)
    (t : ℕ) : (1 + i t) * D t / P t = B t / P t ∧
      (1 + i t) * D t / P t / (P (t + 1) / P t) = B t / P (t + 1) := by
  rw [← hB t]
  refine ⟨rfl, ?_⟩
  have h1 := hP t
  have h2 := hP (t + 1)
  field_simp

end Cochrane.IntertemporalModel.Links
