/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.CashInAdvance

/-!
# Active fiscal policy determines the cash-in-advance price level across ALL paths

Cochrane (2023), Ch. 19, §19.5.5, pp. 453–454: "Active fiscal policy can rule out these multiple
equilibria" (the zero-rate deflations of the cash-in-advance model), and p. 453: the valuation
equation gives a unique positive price level "if the government always chooses a positive amount
of nominal debt". `CashInAdvance.PF.active_fiscal_prunes` proved the pruning only against the
paths with a permanently zero nominal rate. Here it is proved against EVERY price path.

## Setting

Perfect foresight, constant endowment `y > 0`, velocity `V > 0`, `0 < β < 1`, money
`M_{t−1} = M_{−1}(1+μ)^t` with `M_{−1} > 0` and `1 + μ > β`. Fiscal policy is active: the
surplus is the exogenous constant `s = (b(1 − β) − μy/V)/(1 + μ)` of the standard equilibrium
(`CashInAdvance.PF.usual_equilibrium`) and does not respond to prices; initial nominal wealth is
`B_{−1} + M_{−1} = M_{−1}(bV/y + 1)`. An equilibrium is any `CashInAdvance.PF.MonetaryEq`
(positive prices, optimal money, flow budget, transversality), with any bond path.

## Main results

* `bondPrice_ge`: in every equilibrium `Q_t ≥ β/(1+μ)`, the standard bond price, at every date
  (the cash constraint caps the price level at `M_tV/y`).
* `active_fiscal_price_unique`: if `B_{−1} + M_{−1} ≥ 0` (i.e. `bV + y ≥ 0`), every equilibrium
  has the standard price level `P_t = M_tV/y` and the standard bonds; with
  `active_fiscal_existsUnique`, exactly one equilibrium exists. This covers all mixtures (late
  switches to the zero bound, partial deflations), not only permanent zero-rate deflations.
* `active_fiscal_two_equilibria`: if `B_{−1} + M_{−1} < 0` (the government a net nominal
  creditor), a zero-rate deflation `P_t = β^tP_0` with `P_0 < M_0V/y` is ALSO an equilibrium
  under the same active policy: uniqueness fails.
* `active_fiscal_unique_iff`: the corrected statement — the price level is unique across all
  paths iff `B_{−1} + M_{−1} ≥ 0`, exactly the book's p. 453 proviso (positive nominal debt).
* `active_fiscal_prunes_all`: the book's case `b ≥ 0` of `CashInAdvance.PF.active_fiscal_prunes`,
  now for all paths.
-/

namespace Cochrane.Monetarism.TidyR5ActiveFiscal

open Filter Topology CashInAdvance.PF

variable {β y V : ℝ}

/-- Cochrane (2023), p. 454: **every equilibrium bond price is at least the standard one.** In a
monetary equilibrium with money `M_{t−1} = M_{−1}(1+μ)^t` (`1 + μ > β`), `Q_t ≥ β/(1+μ)` at
every date: if `Q_t < 1` the cash constraint binds, `P_t = M_tV/y`, and `P_{t+1} ≤ M_{t+1}V/y`
gives `P_{t+1} ≤ (1+μ)P_t`; if `Q_t = 1` the bound is `1 + μ > β`. -/
theorem bondPrice_ge (hβ0 : 0 < β) (hy : 0 < y) (hV : 0 < V) {μ Mm1 : ℝ} (hμ : β < 1 + μ)
    {P' Bin' s' : ℕ → ℝ} (h : MonetaryEq β y V P' Bin' (fun t => Mm1 * (1 + μ) ^ t) s')
    (j : ℕ) : β / (1 + μ) ≤ bondPrice β P' j := by
  have hg : 0 < 1 + μ := lt_trans hβ0 hμ
  by_cases hlt : bondPrice β P' j < 1
  · have hb := h.binds j hlt
    have hc := h.cia (j + 1)
    have hyV : 0 < y / V := div_pos hy hV
    have A : P' (j + 1) * (y / V) ≤ ((1 + μ) * P' j) * (y / V) := by
      have e1 : P' (j + 1) * (y / V) = P' (j + 1) * y / V := by ring
      have e2 : ((1 + μ) * P' j) * (y / V) = (1 + μ) * (P' j * y / V) := by ring
      rw [e1, e2, ← hb]
      rw [pow_succ (1 + μ) (j + 1)] at hc
      linarith
    have A' := le_of_mul_le_mul_right A hyV
    have hP1 := h.pos (j + 1)
    unfold bondPrice
    rw [div_le_div_iff₀ hg hP1]
    have := mul_le_mul_of_nonneg_left A' hβ0.le
    linarith
  · have h1 : bondPrice β P' j = 1 := le_antisymm (h.rate_nonneg j) (not_lt.mp hlt)
    rw [h1, div_le_one hg]
    exact hμ.le

/-- **Cochrane (2023), pp. 453–454: active fiscal policy determines the price level across ALL
paths.** With `0 < β < 1`, `y, V > 0`, money `M_{t−1} = M_{−1}(1+μ)^t` (`M_{−1} > 0`,
`1 + μ > β`), the active surplus `s = (b(1 − β) − μy/V)/(1 + μ)` and initial nominal wealth
`B_{−1} + M_{−1} = M_{−1}(bV/y + 1) ≥ 0` (i.e. `bV + y ≥ 0`), every monetary equilibrium has
the standard price level `P_t = M_tV/y` and the standard bonds `B_{t−1} = bM_{t−1}V/y`. -/
theorem active_fiscal_price_unique (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {μ Mm1 b : ℝ} (hμ : β < 1 + μ) (hM : 0 < Mm1) (hA0 : 0 ≤ b * V + y) {P' Bin' : ℕ → ℝ}
    (h : MonetaryEq β y V P' Bin' (fun t => Mm1 * (1 + μ) ^ t)
      (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)))
    (hA : Bin' 0 + Mm1 * (1 + μ) ^ 0 = Mm1 * (b * V / y + 1)) :
    P' = (fun t => Mm1 * V / y * (1 + μ) ^ (t + 1)) ∧
      Bin' = fun t => b * (Mm1 * (1 + μ) ^ t * V / y) := by
  have hg : 0 < 1 + μ := lt_trans hβ0 hμ
  set sv := (b * (1 - β) - μ * y / V) / (1 + μ) with hsv
  set qb := β / (1 + μ) with hqb
  have hqb1 : qb < 1 := by rw [hqb, div_lt_one hg]; exact hμ
  have hqb0 : 0 ≤ qb := by positivity
  have hq : ∀ j, qb ≤ bondPrice β P' j := bondPrice_ge hβ0 hy hV hμ h
  have hyV : 0 < y / V := div_pos hy hV
  -- summability of the valuation series of the candidate path and of the standard one
  have hgeo := summable_geometric_of_lt_one hβ0.le hβ1
  have hs2 : Summable (fun j => β ^ j * ((1 - bondPrice β P' j) * y / V)) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (hgeo.mul_right (y / V))
    · have h1 : 0 ≤ 1 - bondPrice β P' j := by linarith [h.rate_nonneg j]
      have : 0 ≤ (1 - bondPrice β P' j) * y / V := by positivity
      exact mul_nonneg (pow_nonneg hβ0.le j) this
    · have h1 : (1 - bondPrice β P' j) * y / V ≤ y / V := by
        have := hq j
        have e : (1 - bondPrice β P' j) * y / V = (1 - bondPrice β P' j) * (y / V) := by ring
        rw [e]
        nlinarith
      exact mul_le_mul_of_nonneg_left h1 (pow_nonneg hβ0.le j)
  have hsP : Summable (fun j => β ^ j * (sv + (1 - bondPrice β P' j) * y / V)) :=
    ((hgeo.mul_right sv).add hs2).congr fun j => by ring
  have hsS : Summable (fun j => β ^ j * (sv + (1 - qb) * y / V)) :=
    hgeo.mul_right _
  -- the valuation equation along the candidate path
  have e := monetary_valuation hβ0 hV h 0 (by simpa only [zero_add] using hsP)
  simp only [zero_add] at e
  rw [hA] at e
  -- the standard sum equals initial wealth over the standard price level
  have hstd : ∑' j, β ^ j * (sv + (1 - qb) * y / V) = Mm1 * (b * V / y + 1) /
      (Mm1 * V / y * (1 + μ) ^ (0 + 1)) := by
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1, hsv, hqb]
    have := hV.ne'
    have := hy.ne'
    have := hg.ne'
    have := hM.ne'
    have : (1 - β) ≠ 0 := by linarith
    field_simp
    ring
  -- the candidate price level is at most the standard one, so wealth over it is at least
  have hP0 : P' 0 ≤ Mm1 * V / y * (1 + μ) ^ (0 + 1) := by
    have hc := h.cia 0
    rw [div_le_iff₀ hV] at hc
    have e2 : Mm1 * V / y * (1 + μ) ^ (0 + 1) = Mm1 * (1 + μ) ^ (0 + 1) * V / y := by ring
    rw [e2, le_div_iff₀ hy]
    linarith
  have hW : 0 ≤ Mm1 * (b * V / y + 1) := by
    have : b * V / y + 1 = (b * V + y) / y := by field_simp
    rw [this]
    positivity
  have hge : Mm1 * (b * V / y + 1) / (Mm1 * V / y * (1 + μ) ^ (0 + 1)) ≤
      Mm1 * (b * V / y + 1) / P' 0 :=
    div_le_div_of_nonneg_left hW (h.pos 0) hP0
  -- hence every bond price is the standard one
  have hall : ∀ j, bondPrice β P' j = qb := by
    intro j
    by_contra hne
    have hlt : qb < bondPrice β P' j := lt_of_le_of_ne (hq j) (Ne.symm hne)
    have hterm : ∀ i, β ^ i * (sv + (1 - bondPrice β P' i) * y / V) ≤
        β ^ i * (sv + (1 - qb) * y / V) := by
      intro i
      have := mul_le_mul_of_nonneg_right (hq i) hyV.le
      have e1 : (1 - bondPrice β P' i) * y / V = y / V - bondPrice β P' i * (y / V) := by ring
      have e2 : (1 - qb) * y / V = y / V - qb * (y / V) := by ring
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le i)
      rw [e1, e2]
      linarith
    have hstrict : β ^ j * (sv + (1 - bondPrice β P' j) * y / V) <
        β ^ j * (sv + (1 - qb) * y / V) := by
      have := mul_lt_mul_of_pos_right hlt hyV
      have e1 : (1 - bondPrice β P' j) * y / V = y / V - bondPrice β P' j * (y / V) := by ring
      have e2 : (1 - qb) * y / V = y / V - qb * (y / V) := by ring
      refine mul_lt_mul_of_pos_left ?_ (pow_pos hβ0 j)
      rw [e1, e2]
      linarith
    have := Summable.tsum_lt_tsum hterm hstrict hsP hsS
    linarith
  -- the price level
  have hPeq : P' = fun t => Mm1 * V / y * (1 + μ) ^ (t + 1) := by
    funext t
    have hb := h.binds t (by rw [hall t]; exact hqb1)
    rw [eq_div_iff hV.ne'] at hb
    have := hV.ne'
    have := hy.ne'
    field_simp
    linarith
  refine ⟨hPeq, ?_⟩
  -- the bonds, by forward induction on the flow budget
  have hstdEq := usual_equilibrium (b := b) hβ0 hβ1 hy hV hμ.le hM
  subst hPeq
  have hQ : ∀ t, bondPrice β (fun t => Mm1 * V / y * (1 + μ) ^ (t + 1)) t ≠ 0 := by
    intro t
    rw [bondPrice_growth (by positivity) hg.ne']
    positivity
  funext t
  induction t with
  | zero =>
    have := hy.ne'
    simp only [pow_zero, mul_one] at hA ⊢
    field_simp at hA ⊢
    linarith
  | succ k ih =>
    have f1 := h.flow k
    have f2 := hstdEq.flow k
    rw [ih] at f1
    exact mul_left_cancel₀ (hQ k) (by linarith)

/-- Cochrane (2023), pp. 453–454: **existence and uniqueness** under active fiscal policy with
`B_{−1} + M_{−1} ≥ 0`: exactly one perfect-foresight monetary equilibrium (price level and
bonds) has the given money path, the given active surplus and initial wealth
`M_{−1}(bV/y + 1)`, namely the standard one. -/
theorem active_fiscal_existsUnique (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {μ Mm1 b : ℝ} (hμ : β < 1 + μ) (hM : 0 < Mm1) (hA0 : 0 ≤ b * V + y) :
    ∃! e : (ℕ → ℝ) × (ℕ → ℝ), MonetaryEq β y V e.1 e.2 (fun t => Mm1 * (1 + μ) ^ t)
      (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)) ∧
      e.2 0 + Mm1 * (1 + μ) ^ 0 = Mm1 * (b * V / y + 1) := by
  refine ⟨(fun t => Mm1 * V / y * (1 + μ) ^ (t + 1), fun t => b * (Mm1 * (1 + μ) ^ t * V / y)),
    ⟨usual_equilibrium hβ0 hβ1 hy hV hμ.le hM, ?_⟩, ?_⟩
  · have := hy.ne'
    simp only [pow_zero, mul_one]
    field_simp
  · rintro ⟨P', Bin'⟩ ⟨h, hA⟩
    obtain ⟨h1, h2⟩ := active_fiscal_price_unique hβ0 hβ1 hy hV hμ hM hA0 h hA
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩

/-- **Cochrane (2023), pp. 453–454 — the proviso is needed (counterexample).** If initial nominal
government liabilities are negative, `B_{−1} + M_{−1} = M_{−1}(bV/y + 1) < 0` (`bV + y < 0`),
then under the SAME active policy the zero-rate deflation `P_t = β^tP_0` with
`P_0 = (B_{−1} + M_{−1})(1 − β)/s` is also a monetary equilibrium, and `P_0 < M_0V/y`: there are
two equilibria (the other is `CashInAdvance.PF.usual_equilibrium`). -/
theorem active_fiscal_two_equilibria (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {μ Mm1 b : ℝ} (hμ : β < 1 + μ) (hM : 0 < Mm1) (hA0 : b * V + y < 0) :
    ∃ P' Bin' : ℕ → ℝ, MonetaryEq β y V P' Bin' (fun t => Mm1 * (1 + μ) ^ t)
      (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)) ∧
      Bin' 0 + Mm1 * (1 + μ) ^ 0 = Mm1 * (b * V / y + 1) ∧
      P' 0 < Mm1 * V / y * (1 + μ) ^ (0 + 1) := by
  have hg : 0 < 1 + μ := lt_trans hβ0 hμ
  set sv := (b * (1 - β) - μ * y / V) / (1 + μ) with hsv
  set A0 := Mm1 * (b * V / y + 1) with hA0def
  have hA0neg : A0 < 0 := by
    have : b * V / y + 1 = (b * V + y) / y := by field_simp
    rw [hA0def, this]
    exact mul_neg_of_pos_of_neg hM (div_neg_of_neg_of_pos hA0 hy)
  have hsvneg : sv < 0 := by
    have e : sv = (b * V * (1 - β) - μ * y) / (V * (1 + μ)) := by
      rw [hsv]
      field_simp
    rw [e]
    refine div_neg_of_neg_of_pos ?_ (by positivity)
    have h1 : b * V * (1 - β) < -y * (1 - β) := by nlinarith
    nlinarith
  have h1β : 0 < 1 - β := by linarith
  set P0 := A0 * (1 - β) / sv with hP0def
  have hP0pos : 0 < P0 := div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hA0neg h1β) hsvneg
  have hkey : P0 * sv = A0 * (1 - β) := div_mul_cancel₀ _ hsvneg.ne
  set pb := Mm1 * V / y * (1 + μ) ^ (0 + 1) with hpbdef
  have hpbsv : A0 * (1 - β) - pb * sv = Mm1 * (1 - β + μ) := by
    rw [hA0def, hpbdef, hsv]
    have := hV.ne'
    have := hy.ne'
    have := hg.ne'
    field_simp
    ring
  have hlt : P0 < pb := by
    have hpos : 0 < (P0 - pb) * sv := by
      have : 0 < Mm1 * (1 - β + μ) := by
        have : 0 < 1 - β + μ := by linarith
        positivity
      nlinarith
    nlinarith
  have hcap : P0 * y / V ≤ Mm1 * (1 + μ) := by
    rw [div_le_iff₀ hV]
    have e : pb * y = Mm1 * (1 + μ) * V := by
      rw [hpbdef]
      have := hy.ne'
      field_simp
      ring
    nlinarith
  have hd := deflation_equilibrium (y := y) (V := V) (A0 := A0) hβ0 hβ1 hμ.le hM.le hP0pos hcap
  have hs : (fun _ : ℕ => A0 * (1 - β) / P0) = fun _ => sv := by
    funext _
    rw [← hkey]
    field_simp
  rw [hs] at hd
  refine ⟨_, _, hd, ?_, ?_⟩
  · simp only [pow_zero, mul_one]
    ring
  · simpa only [pow_zero, one_mul] using hlt

/-- **Cochrane (2023), pp. 453–454: the corrected statement.** Under the active surplus
`s = (b(1 − β) − μy/V)/(1 + μ)` and money growth `1 + μ > β` (`0 < β < 1`, `y, V, M_{−1} > 0`),
the price level is the same in every monetary equilibrium (across ALL paths) iff initial nominal
government liabilities are nonnegative, `B_{−1} + M_{−1} ≥ 0` (`bV + y ≥ 0`). -/
theorem active_fiscal_unique_iff (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {μ Mm1 b : ℝ} (hμ : β < 1 + μ) (hM : 0 < Mm1) :
    (∀ P' Bin' : ℕ → ℝ, MonetaryEq β y V P' Bin' (fun t => Mm1 * (1 + μ) ^ t)
        (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)) →
        Bin' 0 + Mm1 * (1 + μ) ^ 0 = Mm1 * (b * V / y + 1) →
        P' = fun t => Mm1 * V / y * (1 + μ) ^ (t + 1)) ↔ 0 ≤ b * V + y := by
  constructor
  · intro hu
    by_contra hneg
    push Not at hneg
    obtain ⟨P', Bin', h, hA, hlt⟩ := active_fiscal_two_equilibria hβ0 hβ1 hy hV hμ hM hneg
    have := congrFun (hu P' Bin' h hA) 0
    rw [this] at hlt
    exact lt_irrefl _ hlt
  · intro hA0 P' Bin' h hA
    exact (active_fiscal_price_unique hβ0 hβ1 hy hV hμ hM hA0 h hA).1

/-- Cochrane (2023), p. 454, extending `CashInAdvance.PF.active_fiscal_prunes` (which excluded
only permanently zero-rate paths) to ALL paths: in the book's case `b ≥ 0`, every monetary
equilibrium under the active surplus has the standard price level `P_t = M_tV/y`. -/
theorem active_fiscal_prunes_all (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) (hV : 0 < V)
    {μ Mm1 b : ℝ} (hμ : β < 1 + μ) (hM : 0 < Mm1) (hb : 0 ≤ b) {P' Bin' : ℕ → ℝ}
    (h : MonetaryEq β y V P' Bin' (fun t => Mm1 * (1 + μ) ^ t)
      (fun _ => (b * (1 - β) - μ * y / V) / (1 + μ)))
    (hA : Bin' 0 + Mm1 * (1 + μ) ^ 0 = Mm1 * (b * V / y + 1)) :
    P' = fun t => Mm1 * V / y * (1 + μ) ^ (t + 1) :=
  (active_fiscal_price_unique hβ0 hβ1 hy hV hμ hM (by positivity) h hA).1

end Cochrane.Monetarism.TidyR5ActiveFiscal
