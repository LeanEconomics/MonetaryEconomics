/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6ActiveFiscalTree

/-!
# Active fiscal policy under uncertainty: existence of the standard equilibrium

Cochrane (2023), *The Fiscal Theory of the Price Level*, Ch. 19, §19.5, pp. 448–454 (the
valuation equation (19.35), p. 450, and "active fiscal policy can rule out these multiple
equilibria", p. 454). `TidyR6ActiveFiscalTree.unique_of_standard` shows that the standard
equilibrium `P_t = M_tV/y`, when it exists, is the only equilibrium. Here its existence is
characterised exactly, for every `ExpectationSystem` with the pull-out property (in particular
every finite event tree), with random time-varying money and bounded adapted surpluses.

## The coordination condition

Let `q_t = E_t[βM_t/M_{t+1}]` (`TidyR6ActiveFiscalTree.stdBondPrice`) and let
`x_t = Σ_j β^jE_t[s_{t+j} + (1 − q_{t+j})y/V]` (`stdValue`, the forward valuation of surpluses
plus seigniorage along the standard path). The surplus is **coordinated with money**
(`Coordinated`) iff

1. `q_t ≤ 1` at every date and state (the standard nominal rate is nonnegative);
2. `M_{t+1}x_{t+1}` is known at `t` (the nominal value of next period's liabilities, which the
   government chooses at `t` through `B_t`, is not exposed to date-`t+1` news);
3. `B_{−1} + M_{−1} = (M_0V/y)x_0` (date-0 valuation).

## Main results

* `std_exists_iff`: a standard equilibrium with initial bonds `B_{−1}` exists iff the surplus is
  coordinated with money.
* `std_existsUnique_iff`: with full support, `B_{−1} + M_{−1} ≥ 0` and the pinning condition
  (`B_{−1} + M_{−1} > 0` or `q_0 < 1`), the surplus is coordinated iff there is exactly one
  equilibrium and every equilibrium is the standard one. Whether an uncoordinated economy can
  have a unique non-standard equilibrium is not settled.
-/

namespace Cochrane.Monetarism.TidyR6ActiveFiscalExist

open Filter Topology
open Cochrane.Monetarism.TidyR6ActiveFiscalTree

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), (19.35), p. 450: the undiscounted standard flow
`s_t + (1 − q_t)y/V` (surplus plus seigniorage along `P = MV/y`). -/
noncomputable def stdU (β y V : ℝ) (Min s : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  s t ω + (1 - stdBondPrice 𝔼 β Min t ω) * y / V

/-- Cochrane (2023), (19.35), p. 450: the forward valuation along the standard path,
`x_t = Σ_j β^jE_t[s_{t+j} + (1 − q_{t+j})y/V]`. -/
noncomputable def stdValue (β y V : ℝ) (Min s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries β (stdU 𝔼 β y V Min s)

/-- Cochrane (2023), pp. 453–454: **the surplus is coordinated with money**: `q_t ≤ 1`,
`M_{t+1}x_{t+1}` known at `t`, and `B_{−1} + M_{−1} = (M_0V/y)x_0`. -/
def Coordinated (β y V : ℝ) (B0 : Ω → ℝ) (Min s : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, stdBondPrice 𝔼 β Min t ω ≤ 1) ∧
    (∀ t, 𝔼.E t (fun ω => Min (t + 2) ω * stdValue 𝔼 β y V Min s (t + 1) ω) =
      fun ω => Min (t + 2) ω * stdValue 𝔼 β y V Min s (t + 1) ω) ∧
    ∀ ω, B0 ω + Min 0 ω = Min 1 ω * V / y * stdValue 𝔼 β y V Min s 0 ω

variable {𝔼} {β y V : ℝ} {Min s : ℕ → Ω → ℝ}

/-- Cochrane (2023), p. 454: with positive money and `β ≥ 0`, `q_t ≥ 0`. -/
theorem stdBondPrice_nonneg (hβ : 0 ≤ β) (hM : ∀ t ω, 0 < Min (t + 1) ω) (t : ℕ) (ω : Ω) :
    0 ≤ stdBondPrice 𝔼 β Min t ω := by
  have h := 𝔼.mono t (show (fun _ => (0 : ℝ)) ≤ fun ω => β * Min (t + 1) ω / Min (t + 2) ω
    from fun ω => by have := hM t ω; have := hM (t + 1) ω; positivity)
  rw [𝔼.const] at h
  exact h ω

/-- Cochrane (2023), (19.35), p. 450: with `|s| ≤ S` and `0 ≤ q ≤ 1`, the standard flow is
bounded by `S + y/V`. -/
theorem stdU_bound (hβ : 0 ≤ β) (hy : 0 < y) (hV : 0 < V) (hM : ∀ t ω, 0 < Min (t + 1) ω)
    (hq1 : ∀ t ω, stdBondPrice 𝔼 β Min t ω ≤ 1) {S : ℝ} (hsb : ∀ t ω, |s t ω| ≤ S) (t : ℕ)
    (ω : Ω) : |stdU 𝔼 β y V Min s t ω| ≤ S + y / V := by
  have h0 := stdBondPrice_nonneg (𝔼 := 𝔼) hβ hM t ω
  have h1 := hq1 t ω
  have hyV : 0 < y / V := div_pos hy hV
  have e : (1 - stdBondPrice 𝔼 β Min t ω) * y / V = (1 - stdBondPrice 𝔼 β Min t ω) * (y / V) :=
    by ring
  unfold stdU
  rw [e]
  have h2 : |(1 - stdBondPrice 𝔼 β Min t ω) * (y / V)| ≤ y / V := by
    rw [abs_mul, abs_of_pos hyV, abs_of_nonneg (by linarith)]
    nlinarith
  calc |s t ω + (1 - stdBondPrice 𝔼 β Min t ω) * (y / V)|
      ≤ |s t ω| + |(1 - stdBondPrice 𝔼 β Min t ω) * (y / V)| := abs_add_le _ _
    _ ≤ S + y / V := add_le_add (hsb t ω) h2

/-- Cochrane (2023), (19.35), p. 450: the standard flow is known at its date when the surplus
is. -/
theorem stdU_adapted (hs : ∀ t, 𝔼.E t (s t) = s t) : 𝔼.Adapted (stdU 𝔼 β y V Min s) := by
  intro t
  have e : stdU 𝔼 β y V Min s t = s t + (y / V) • (fun _ => (1 : ℝ)) -
      (y / V) • stdBondPrice 𝔼 β Min t := by
    funext ω
    simp only [stdU, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, map_sub, map_add, map_smul, map_smul, hs t, 𝔼.const]
  unfold stdBondPrice
  rw [𝔼.E_E_self]

/-- Cochrane (2023), (19.35), p. 450: along the standard path the discounted flow of
`TidyR6ActiveFiscalTree.flowTerm` is `β^t(s_t + (1 − q_t)y/V)`. -/
theorem flowTerm_std (hy : 0 < y) (hV : 0 < V) (hM : ∀ t ω, 0 < Min (t + 1) ω) (t : ℕ) :
    flowTerm 𝔼 β y V (stdPrice y V Min) s t = fun ω => β ^ t * stdU 𝔼 β y V Min s t ω := by
  funext ω
  simp only [flowTerm, stdU, bondPriceS_std hy hV hM t]

/-- **Cochrane (2023), pp. 448–454: existence of the standard equilibrium under uncertainty.**
Let `E` have the pull-out property, `0 < β < 1`, `y, V > 0`, money `M_t = Min (t+1)` positive
and known at `t`, surpluses known at their dates and bounded. Then a monetary equilibrium with
the standard price level `P_t = M_tV/y` and initial bonds `B_{−1}` exists iff the surplus is
coordinated with money (`Coordinated`). -/
theorem std_exists_iff (hPO : 𝔼.PullOut) (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (hV : 0 < V) (hM : ∀ t ω, 0 < Min (t + 1) ω) (hMk : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1))
    (hs : ∀ t, 𝔼.E t (s t) = s t) {S : ℝ} (hsb : ∀ t ω, |s t ω| ≤ S) (B0 : Ω → ℝ) :
    (∃ Bs : ℕ → Ω → ℝ, Bs 0 = B0 ∧ StochMonetaryEq 𝔼 β y V (stdPrice y V Min) Bs Min s) ↔
      Coordinated 𝔼 β y V B0 Min s := by
  have hQ := bondPriceS_std (𝔼 := 𝔼) (β := β) hy hV hM
  constructor
  · rintro ⟨Bs, hB0, h⟩
    have hq1 : ∀ t ω, stdBondPrice 𝔼 β Min t ω ≤ 1 := fun t ω => by
      rw [← hQ t]; exact h.rate_nonneg t ω
    have hub := stdU_bound hβ0.le hy hV hM hq1 hsb
    -- real liabilities equal the forward valuation
    have hval : ∀ t ω, wealth (stdPrice y V Min) Bs Min t ω = stdValue 𝔼 β y V Min s t ω := by
      intro t ω
      have hE : ∀ j, 𝔼.E t (flowTerm 𝔼 β y V (stdPrice y V Min) s (t + j)) ω =
          β ^ t * (β ^ j * 𝔼.E t (stdU 𝔼 β y V Min s (t + j)) ω) := by
        intro j
        rw [flowTerm_std hy hV hM]
        have e : (fun ω => β ^ (t + j) * stdU 𝔼 β y V Min s (t + j) ω) =
            β ^ (t + j) • stdU 𝔼 β y V Min s (t + j) := by funext ω; simp
        rw [e, map_smul, Pi.smul_apply, smul_eq_mul, pow_add]
        ring
      have hsum : Summable fun j => 𝔼.E t (flowTerm 𝔼 β y V (stdPrice y V Min) s (t + j)) ω := by
        simp_rw [hE]
        exact (𝔼.forwardSeries_summable hβ0.le hβ1 hub t ω).mul_left _
      have key := (CashInAdvance.Stochastic.pv_iff_tvc 𝔼 (wealth_recursion hPO hV h)
        (flowTerm_known hs) t ω hsum).1 (h.tvc t ω)
      simp_rw [hE] at key
      rw [tsum_mul_left] at key
      have hb := (pow_pos hβ0 t).ne'
      simp only [discWealth] at key
      exact mul_left_cancel₀ hb key
    refine ⟨hq1, fun t => ?_, fun ω => ?_⟩
    · have e : (fun ω => Min (t + 2) ω * stdValue 𝔼 β y V Min s (t + 1) ω) =
          (y / V) • (Bs (t + 1) + Min (t + 1)) := by
        funext ω
        rw [← hval (t + 1) ω]
        have := (hM (t + 1) ω).ne'
        have := hy.ne'
        have := hV.ne'
        simp only [wealth, stdPrice, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        field_simp
      rw [e, map_smul, map_add, h.knownB t, hMk t]
    · have h0 := hval 0 ω
      have := (hM 0 ω).ne'
      have := hy.ne'
      have := hV.ne'
      simp only [wealth, stdPrice, zero_add, hB0] at h0
      rw [← h0]
      field_simp
  · rintro ⟨hq1, hknown, hdate0⟩
    have hub := stdU_bound hβ0.le hy hV hM hq1 hsb
    set x := stdValue 𝔼 β y V Min s with hx
    have hxs : ∀ t, x t = β • 𝔼.E t (x (t + 1)) + stdU 𝔼 β y V Min s t :=
      𝔼.forwardSeries_solves hβ0.le hβ1 hub (stdU_adapted hs)
    obtain ⟨C, hC⟩ := 𝔼.forwardSeries_bounded hβ0.le hβ1 hub
    set Bs : ℕ → Ω → ℝ := fun t ω =>
      if t = 0 then B0 ω else Min (t + 1) ω * V / y * x t ω - Min t ω with hBs
    have hkey : ∀ t ω, Bs t ω + Min t ω = Min (t + 1) ω * V / y * x t ω := by
      intro t ω
      rcases Nat.eq_zero_or_pos t with ht | ht
      · subst ht; simp only [hBs, ↓reduceIte]; exact hdate0 ω
      · simp only [hBs, ht.ne', ↓reduceIte]; ring
    have hB1 : ∀ t, Bs (t + 1) = fun ω => Min (t + 2) ω * V / y * x (t + 1) ω - Min (t + 1) ω :=
      fun t => by funext ω; simp [hBs]
    have hwealth : ∀ t ω, wealth (stdPrice y V Min) Bs Min t ω = x t ω := by
      intro t ω
      have := (hM t ω).ne'
      have := hy.ne'
      have := hV.ne'
      simp only [wealth, stdPrice, hkey]
      field_simp
    refine ⟨Bs, by simp [hBs], ⟨fun t ω => ?_, fun t => ?_, fun t => ?_, hMk, fun t ω => ?_,
      fun t ω => by rw [hQ t]; exact hq1 t ω, fun t ω _ => ?_, fun t ω => ?_, fun t ω => ?_⟩⟩
    · have := hM t ω; simp only [stdPrice]; positivity
    · have e : stdPrice y V Min t = (V / y) • Min (t + 1) := by
        funext ω; simp only [stdPrice, Pi.smul_apply, smul_eq_mul]; ring
      rw [e, map_smul, hMk t]
    · have e : Bs (t + 1) = (V / y) • (fun ω => Min (t + 2) ω * x (t + 1) ω) - Min (t + 1) := by
        rw [hB1 t]; funext ω; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e, map_sub, map_smul, hknown t, hMk t]
    · simp only [stdPrice]; have := hy.ne'; have := hV.ne'; field_simp; rfl
    · simp only [stdPrice]; have := hy.ne'; have := hV.ne'; field_simp
    · -- the flow budget
      have hK : 𝔼.E t (fun ω => Min (t + 2) ω * V / y * x (t + 1) ω) =
          fun ω => Min (t + 2) ω * V / y * x (t + 1) ω := by
        have e : (fun ω => Min (t + 2) ω * V / y * x (t + 1) ω) =
            (V / y) • fun ω => Min (t + 2) ω * x (t + 1) ω := by
          funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [e, map_smul, hknown t]
      set K : Ω → ℝ := fun ω => Min (t + 2) ω * V / y * x (t + 1) ω with hKdef
      set R : Ω → ℝ := fun ω => 1 / Min (t + 2) ω with hR
      have hxK : x (t + 1) = (y / V) • (K * R) := by
        funext ω
        have := (hM (t + 1) ω).ne'
        have := hy.ne'
        have := hV.ne'
        simp only [hKdef, hR, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
        field_simp
      have hEx : 𝔼.E t (x (t + 1)) ω = y / V * (K ω * 𝔼.E t R ω) := by
        rw [hxK, map_smul, hPO t K R hK]; rfl
      have hq : stdBondPrice 𝔼 β Min t ω = Min (t + 1) ω * (β * 𝔼.E t R ω) := by
        have := congrFun (stdBondPrice_eq (β := β) hPO hMk t) ω
        have e : (fun ω => β / Min (t + 2) ω) = β • R := by
          funext ω; simp only [hR, Pi.smul_apply, smul_eq_mul]; ring
        rw [this, Pi.mul_apply, e, map_smul]; rfl
      have hxt := congrFun (hxs t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hxt
      rw [hQ t, hkey t ω, hxt, hEx, hB1 t]
      simp only [hKdef, stdU, stdPrice]
      rw [hq]
      have := hy.ne'
      have := hV.ne'
      field_simp
      ring
    · -- the conditional transversality condition
      have hdw : ∀ T, discWealth β (stdPrice y V Min) Bs Min (t + T) =
          β ^ (t + T) • x (t + T) := by
        intro T; funext ω'
        simp only [discWealth, hwealth, Pi.smul_apply, smul_eq_mul]
      have hbd : ∀ T, |𝔼.E t (discWealth β (stdPrice y V Min) Bs Min (t + T)) ω| ≤
          β ^ (t + T) * C := by
        intro T
        rw [hdw, map_smul, Pi.smul_apply, smul_eq_mul, abs_mul,
          abs_of_nonneg (pow_nonneg hβ0.le _)]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hC (t + T)) t ω) (pow_nonneg hβ0.le _)
      have hlim : Tendsto (fun T => β ^ (t + T) * C) atTop (𝓝 0) := by
        have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
          (tendsto_add_atTop_iff_nat t |>.2 tendsto_id)).mul_const C
        simpa [add_comm] using this
      exact squeeze_zero_norm (fun T => by rw [Real.norm_eq_abs]; exact hbd T) hlim

/-- **Cochrane (2023), pp. 453–454 under uncertainty: the exists-unique characterisation.**
With the pull-out property and full support, `0 < β < 1`, `y, V > 0`, positive known money,
bounded surpluses known at their dates, initial liabilities `B_{−1} + M_{−1} ≥ 0`, and at every
state `B_{−1} + M_{−1} > 0` or `q_0 < 1`: the surplus is coordinated with money iff there is
exactly one monetary equilibrium (price level and bonds) with initial bonds `B_{−1}` and every
equilibrium has the standard price level `P_t = M_tV/y`. (Without coordination the standard
path is not an equilibrium, `std_exists_iff`, so active fiscal policy does not select it.)
Generalises `TidyR5ActiveFiscal.active_fiscal_existsUnique`. -/
theorem std_existsUnique_iff (hPO : 𝔼.PullOut) (hfull : FullSupport 𝔼) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V) (hM : ∀ t ω, 0 < Min (t + 1) ω)
    (hMk : ∀ t, 𝔼.E t (Min (t + 1)) = Min (t + 1)) (hs : ∀ t, 𝔼.E t (s t) = s t) {S : ℝ}
    (hsb : ∀ t ω, |s t ω| ≤ S) (B0 : Ω → ℝ) (hW : ∀ ω, 0 ≤ B0 ω + Min 0 ω)
    (hpin : ∀ ω, 0 < B0 ω + Min 0 ω ∨ stdBondPrice 𝔼 β Min 0 ω < 1) :
    Coordinated 𝔼 β y V B0 Min s ↔
      (∃! e : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), e.2 0 = B0 ∧ StochMonetaryEq 𝔼 β y V e.1 e.2 Min s) ∧
        ∀ e : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), e.2 0 = B0 → StochMonetaryEq 𝔼 β y V e.1 e.2 Min s →
          e.1 = stdPrice y V Min := by
  constructor
  · intro hc
    obtain ⟨Bs, hB0, h⟩ := (std_exists_iff hPO hβ0 hβ1 hy hV hM hMk hs hsb B0).2 hc
    have huniq : ∀ e : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), e.2 0 = B0 →
        StochMonetaryEq 𝔼 β y V e.1 e.2 Min s → e.1 = stdPrice y V Min ∧ e.2 = Bs := by
      rintro ⟨P', B'⟩ hB0' h'
      exact unique_of_standard hPO hfull hβ0 hy hV h' h hs (hB0'.trans hB0.symm)
        (fun ω => by
          change 0 ≤ B' 0 ω + Min 0 ω; rw [show B' 0 = B0 from hB0']; exact hW ω)
        (fun ω => by
          change 0 < B' 0 ω + Min 0 ω ∨ _; rw [show B' 0 = B0 from hB0']; exact hpin ω)
    refine ⟨⟨⟨stdPrice y V Min, Bs⟩, ⟨hB0, h⟩, fun e he => ?_⟩, fun e h1 h2 => (huniq e h1 h2).1⟩
    obtain ⟨e1, e2⟩ := huniq e he.1 he.2
    exact Prod.ext e1 e2
  · rintro ⟨⟨⟨P, Bs⟩, ⟨hB0, h⟩, -⟩, hall⟩
    have hP : P = stdPrice y V Min := hall ⟨P, Bs⟩ hB0 h
    refine (std_exists_iff hPO hβ0 hβ1 hy hV hM hMk hs hsb B0).1 ⟨Bs, hB0, ?_⟩
    rw [← hP]; exact h

end Cochrane.Monetarism.TidyR6ActiveFiscalExist
