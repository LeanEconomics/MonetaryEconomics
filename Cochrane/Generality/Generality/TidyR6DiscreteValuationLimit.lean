/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.TidyR6DiscreteBondLimit

/-!
# The discrete valuation recursion converges to `V' = rV − s` for time-varying rates

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.3 ((3.5), p. 55) and
§3.6.1 ((3.30)–(3.31), pp. 73–74), with Online Appendix A1.4, pp. 564–565.

`TidyR6DiscreteBondLimit` proved the convergence of the discrete bond-price recursion. Here the
same is done for the valuation of a time-varying surplus stream at a time-varying real rate:
with period length `h`, per-period continuously compounded real rates `r_h(t)` and the surplus
flow `s` paid as `h·s(t)` per period, the discrete value of debt

`V_h(t) = h·s(t) + e^{−h·r_h(t)} V_h(t + h)`

(the forward sum `discVal`, the unique solution with the discrete transversality condition,
`discVal_rec`, `discVal_unique`) converges to the present value `ContinuousShort.pv r s`, the
unique solution of `V' = rV − s` with the transversality condition: uniformly on every `[t₀, X]`
for continuous `r ≥ c > 0` and continuous bounded `s` (`val_tendstoUniformlyOn_Icc`), and
uniformly on `[t₀, ∞)` when `r` and `s` are moreover uniformly continuous and `r` bounded
(`val_tendstoUniformlyOn_Ici`); every transversality solution of the ODE is this limit
(`val_tendsto_unique_ode_solution`).
-/

namespace Cochrane.Generality.TidyR6DiscreteValuationLimit

open MeasureTheory Filter Topology Cochrane.Generality.ContinuousShort
open Cochrane.Generality.TidyR6DiscreteBondLimit

/-! ### The discrete valuation recursion -/

/-- Cochrane (2023), (3.5), p. 55, with period `h`: the discrete value of the surplus flow,
`V_h(t) = h∑_k (∏_{m<k} e^{−h r_h(t+mh)}) s(t + kh)`. -/
noncomputable def discVal (rh : ℝ → ℝ → ℝ) (s : ℝ → ℝ) (h t : ℝ) : ℝ :=
  h * ∑' k, cumFactor rh 0 h t k * s (t + k * h)

/-- Cochrane (2023), (3.5): the discount factor of `discVal` decays geometrically when
`r_h ≥ c` (`cumFactor_le` with no decay `ϖ = 0`). -/
theorem cumFactor_le' {rh : ℝ → ℝ → ℝ} {h t c t₀ : ℝ} (hh : 0 ≤ h) (ht : t₀ ≤ t)
    (hlow : ∀ u, t₀ ≤ u → c ≤ rh h u) (k : ℕ) :
    cumFactor rh 0 h t k ≤ Real.exp (-(c * h)) ^ k :=
  cumFactor_le hh ht (fun u hu => by rw [add_zero]; exact hlow u hu) k

/-- Cochrane (2023), (3.5): the discrete surplus stream is absolutely summable when `s` is
bounded on `[t₀, ∞)` and `r_h ≥ c > 0`. -/
theorem summable_discVal {rh : ℝ → ℝ → ℝ} {s : ℝ → ℝ} {h t c t₀ S : ℝ} (hc : 0 < c)
    (hh : 0 < h) (ht : t₀ ≤ t) (hlow : ∀ u, t₀ ≤ u → c ≤ rh h u)
    (hS : ∀ u, t₀ ≤ u → |s u| ≤ S) :
    Summable fun k : ℕ => cumFactor rh 0 h t k * s (t + k * h) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (Real.exp_pos _).le
    (exp_neg_lt_one (mul_pos hc hh))).mul_right S) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (cumFactor_pos _ _ _ _ k)]
  have hk : t₀ ≤ t + k * h := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh.le]
  exact mul_le_mul (cumFactor_le' hh.le ht hlow k) (hS _ hk) (abs_nonneg _)
    (pow_nonneg (Real.exp_pos _).le k)

/-- Cochrane (2023), (3.5): `|V_h(t)| ≤ S(h + 1/c)`. -/
theorem discVal_bound {rh : ℝ → ℝ → ℝ} {s : ℝ → ℝ} {h t c t₀ S : ℝ} (hc : 0 < c)
    (hh : 0 < h) (ht : t₀ ≤ t) (hlow : ∀ u, t₀ ≤ u → c ≤ rh h u)
    (hS : ∀ u, t₀ ≤ u → |s u| ≤ S) : |discVal rh s h t| ≤ S * (h + 1 / c) := by
  have hx := exp_neg_lt_one (mul_pos hc hh)
  have h0 := (Real.exp_pos (-(c * h))).le
  have hsum := summable_discVal hc hh ht hlow hS
  have hg := summable_geometric_of_lt_one h0 hx
  rw [discVal, abs_mul, abs_of_pos hh]
  calc h * |∑' k, cumFactor rh 0 h t k * s (t + k * h)|
      ≤ h * ∑' k : ℕ, Real.exp (-(c * h)) ^ k * S := by
        refine mul_le_mul_of_nonneg_left ?_ hh.le
        refine (norm_tsum_le_tsum_norm hsum.norm).trans ?_
        refine hsum.norm.tsum_le_tsum (fun k => ?_) (hg.mul_right S)
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (cumFactor_pos _ _ _ _ k)]
        have hk : t₀ ≤ t + k * h := by
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh.le]
        exact mul_le_mul (cumFactor_le' hh.le ht hlow k) (hS _ hk) (abs_nonneg _)
          (pow_nonneg h0 k)
    _ = S * (h / (1 - Real.exp (-(c * h)))) := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one h0 hx]
        ring
    _ ≤ S * (h + 1 / c) := by
        have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS t ht)
        exact mul_le_mul_of_nonneg_left (geom_bound hc hh) hS0

/-- Cochrane (2023), (3.5) and footnote 1, p. 58, with period `h`: the discrete valuation
recursion `V_h(t) = h·s(t) + e^{−h r_h(t)}V_h(t + h)`. -/
theorem discVal_rec {rh : ℝ → ℝ → ℝ} {s : ℝ → ℝ} {h t c t₀ S : ℝ} (hc : 0 < c)
    (hh : 0 < h) (ht : t₀ ≤ t) (hlow : ∀ u, t₀ ≤ u → c ≤ rh h u)
    (hS : ∀ u, t₀ ≤ u → |s u| ≤ S) :
    discVal rh s h t = h * s t + factor rh 0 h t * discVal rh s h (t + h) := by
  have hsum := summable_discVal hc hh ht hlow hS
  rw [discVal, hsum.tsum_eq_zero_add, cumFactor_zero, discVal]
  have e : ∀ k : ℕ, cumFactor rh 0 h t (k + 1) * s (t + ((k + 1 : ℕ) : ℝ) * h) =
      factor rh 0 h t * (cumFactor rh 0 h (t + h) k * s (t + h + k * h)) := fun k => by
    rw [cumFactor_succ]
    have : t + ((k + 1 : ℕ) : ℝ) * h = t + h + k * h := by push_cast; ring
    rw [this]
    ring
  rw [tsum_congr e, tsum_mul_left]
  simp only [Nat.cast_zero, zero_mul, add_zero, one_mul]
  ring

/-- Cochrane (2023), (3.5) and footnote 1, p. 58, with period `h`: **uniqueness.** Any solution of
the discrete recursion along the grid with the discrete transversality condition equals
`discVal`. -/
theorem discVal_unique {rh : ℝ → ℝ → ℝ} {s : ℝ → ℝ} {h t c t₀ S : ℝ} (hc : 0 < c)
    (hh : 0 < h) (ht : t₀ ≤ t) (hlow : ∀ u, t₀ ≤ u → c ≤ rh h u)
    (hS : ∀ u, t₀ ≤ u → |s u| ≤ S) {X : ℝ → ℝ}
    (hX : ∀ k : ℕ, X (t + k * h) =
      h * s (t + k * h) + factor rh 0 h (t + k * h) * X (t + (k + 1 : ℕ) * h))
    (hT : Tendsto (fun N : ℕ => cumFactor rh 0 h t N * X (t + N * h)) atTop (𝓝 0)) :
    X t = discVal rh s h t := by
  have hsum := summable_discVal hc hh ht hlow hS
  have hrec : ∀ k : ℕ, (fun n : ℕ => X (t + n * h)) k =
      (fun n : ℕ => h * s (t + n * h)) k + (fun n : ℕ => factor rh 0 h (t + n * h)) k *
        (fun n : ℕ => X (t + n * h)) (k + 1) := fun k => hX k
  have hs' : Summable fun j => (∏ k ∈ Finset.range j,
      (fun n : ℕ => factor rh 0 h (t + n * h)) (0 + k)) * (fun n : ℕ => h * s (t + n * h))
        (0 + j) := by
    refine (hsum.mul_left h).congr fun j => ?_
    simp only [zero_add, cumFactor]
    ring
  have h1 := (Money.pv_discount_iff hrec 0 hs').mp (by simpa [cumFactor] using hT)
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add] at h1
  rw [h1, discVal, ← tsum_mul_left]
  exact tsum_congr fun j => by rw [cumFactor]; ring

/-! ### The continuous value and the one-step error -/

/-- Cochrane (2023), (3.31), p. 73: with `r ≥ c > 0` and `|s| ≤ S` on `[t, ∞)`, the discounted
surplus stream is integrable. -/
theorem pvIntegrable_of_bound {r s : ℝ → ℝ} {c t S : ℝ} (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hc : 0 < c) (hge : ∀ u, t ≤ u → c ≤ r u)
    (hS : ∀ u, t ≤ u → |s u| ≤ S) : PVIntegrable r s t := by
  have hg : IntegrableOn (fun u => S * Real.exp (c * t) * Real.exp (-c * u)) (Set.Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul _
  refine Integrable.mono' hg ?_ ?_
  · exact (((continuousOn_disc hr).mul hs).mono
      Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hu' : t ≤ u := le_of_lt hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (disc_pos _ _ _)]
    have h1 : disc r t u ≤ Real.exp (c * t) * Real.exp (-c * u) := by
      rw [disc, ← Real.exp_add, Real.exp_le_exp]
      have := cumRate_ge hr hu' hge
      linarith
    have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS u hu')
    calc disc r t u * |s u| ≤ (Real.exp (c * t) * Real.exp (-c * u)) * S :=
          mul_le_mul h1 (hS u hu') (abs_nonneg _) (by positivity)
      _ = S * Real.exp (c * t) * Real.exp (-c * u) := by ring

/-- Cochrane (2023), (3.31), p. 73: with `r ≥ c > 0` and `|s| ≤ S` on `[t, ∞)`, the present value
satisfies `|pv r s t| ≤ S/c`. -/
theorem pv_abs_le {r s : ℝ → ℝ} {c t S : ℝ} (hr : ContinuousOn r (Set.Ici t))
    (hc : 0 < c) (hge : ∀ u, t ≤ u → c ≤ r u) (hS : ∀ u, t ≤ u → |s u| ≤ S) :
    |pv r s t| ≤ S / c := by
  have hJ := pvIntegrable_const hc S t
  rw [← pv_const_const hc S t, pv, pv, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hJ ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun u hu => ?_))
  have hu' : t ≤ u := le_of_lt hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (disc_pos _ _ _)]
  refine mul_le_mul ?_ (hS u hu') (abs_nonneg _) (disc_pos _ _ _).le
  rw [disc, disc, Real.exp_le_exp, neg_le_neg_iff, cumRate_const]
  exact cumRate_ge hr hu' hge

/-- Cochrane (2023), (3.5) and (3.31): the one-step valuation error
`δ_h(t) = (h·s(t) − ∫_t^{t+h}D(t,τ)s(τ)dτ) + (e^{−h r_h(t)} − D(t, t+h))V(t+h)`, with
`V = ContinuousShort.pv r s`. -/
noncomputable def valDelta (rh : ℝ → ℝ → ℝ) (r s : ℝ → ℝ) (h t : ℝ) : ℝ :=
  (h * s t - ∫ τ in t..t + h, disc r t τ * s τ) +
    (factor rh 0 h t - disc r t (t + h)) * pv r s (t + h)

/-- Cochrane (2023), (3.5) and (3.31): the valuation error `e_h = V_h − V` obeys
`e_h(t) = δ_h(t) + e^{−h r_h(t)}e_h(t + h)`. -/
theorem valErr_rec {r s : ℝ → ℝ} {rh : ℝ → ℝ → ℝ} {c h t t₀ S : ℝ}
    (hr : ContinuousOn r (Set.Ici t₀)) (hs : ContinuousOn s (Set.Ici t₀)) (hc : 0 < c)
    (hh : 0 < h) (ht : t₀ ≤ t) (hge : ∀ u, t₀ ≤ u → c ≤ r u)
    (hlow : ∀ u, t₀ ≤ u → c ≤ rh h u) (hS : ∀ u, t₀ ≤ u → |s u| ≤ S) :
    discVal rh s h t - pv r s t = valDelta rh r s h t +
      factor rh 0 h t * (discVal rh s h (t + h) - pv r s (t + h)) := by
  have hrt : ContinuousOn r (Set.Ici t) := hr.mono (Set.Ici_subset_Ici.2 ht)
  have hst : ContinuousOn s (Set.Ici t) := hs.mono (Set.Ici_subset_Ici.2 ht)
  have hI := pvIntegrable_of_bound hrt hst hc (fun u hu => hge u (ht.trans hu))
    (fun u hu => hS u (ht.trans hu))
  have hone := pv_finite hrt hst (flowOn_pv hrt hst hI) (T := t + h) (by linarith)
  have hrec := discVal_rec hc hh ht hlow hS
  unfold valDelta
  linear_combination hrec + hone

/-- Cochrane (2023), (3.5) and (3.31): **the one-step valuation error is `O(h)·(h + moduli)`.**
If `|r| ≤ M`, `|r(u) − r(t)| ≤ η₂` and `|s(u) − s(t)| ≤ η₃` on `[t, t+h]`, `|r_h(t) − r(t)| ≤ η₁`
and `|s| ≤ S` on `[t, ∞)`, then `|δ_h(t)| ≤ h(η₃ + hMS + (η₁ + η₂)S/c)`. -/
theorem valDelta_le {r s : ℝ → ℝ} {rh : ℝ → ℝ → ℝ} {c h t M S η₁ η₂ η₃ : ℝ}
    (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t)) (hc : 0 < c)
    (hh : 0 < h) (hge : ∀ u, t ≤ u → c ≤ r u) (hlow : c ≤ rh h t)
    (hS : ∀ u, t ≤ u → |s u| ≤ S) (hM : ∀ u ∈ Set.Icc t (t + h), |r u| ≤ M)
    (h1 : |rh h t - r t| ≤ η₁) (h2 : ∀ u ∈ Set.Icc t (t + h), |r u - r t| ≤ η₂)
    (h3 : ∀ u ∈ Set.Icc t (t + h), |s u - s t| ≤ η₃) :
    |valDelta rh r s h t| ≤ h * (η₃ + h * M * S + (η₁ + η₂) * S / c) := by
  have hth : t ≤ t + h := by linarith
  have hcum0 : ∀ τ, t ≤ τ → 0 ≤ cumRate r t τ := fun τ hτ =>
    le_trans (mul_nonneg hc.le (by linarith)) (cumRate_ge hr hτ hge)
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS t le_rfl)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t ⟨le_rfl, hth⟩)
  -- the first term
  have hP1 : |h * s t - ∫ τ in t..t + h, disc r t τ * s τ| ≤ (η₃ + M * h * S) * h := by
    have hDint : IntervalIntegrable (fun τ => disc r t τ * s τ) volume t (t + h) :=
      intervalIntegrable_of_ici ((continuousOn_disc hr).mul hs) le_rfl hth
    have he : h * s t - ∫ τ in t..t + h, disc r t τ * s τ =
        ∫ τ in t..t + h, (s t - disc r t τ * s τ) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hDint,
        intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
    rw [he]
    have h' := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := t + h)
      (f := fun τ => s t - disc r t τ * s τ) (C := η₃ + M * h * S) fun τ hτ => by
        rw [Set.uIoc_of_le hth] at hτ
        have hτ' : t ≤ τ := hτ.1.le
        have h0 := hcum0 τ hτ'
        have hb := abs_cumRate_le hτ' fun x hx => hM x ⟨hx.1, hx.2.trans hτ.2⟩
        rw [abs_of_nonneg h0] at hb
        have hx1 := Real.add_one_le_exp (-cumRate r t τ)
        have hx2 : Real.exp (-cumRate r t τ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have hD : |1 - disc r t τ| ≤ M * h := by
          rw [disc, abs_of_nonneg (by linarith)]
          nlinarith [hτ.2]
        have hsτ := hS τ hτ'
        have e : s t - disc r t τ * s τ = (s t - s τ) + (1 - disc r t τ) * s τ := by ring
        rw [Real.norm_eq_abs, e]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_sub_comm]; exact h3 τ ⟨hτ', hτ.2⟩
        · rw [abs_mul]
          exact mul_le_mul hD hsτ (abs_nonneg _) (by positivity)
    rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at h'
    exact h'
  -- the second term
  have hP2 : |factor rh 0 h t - disc r t (t + h)| ≤ h * η₁ + h * η₂ := by
    have hx : 0 ≤ h * (rh h t + 0) := mul_nonneg hh.le (by linarith)
    have hb := abs_exp_neg_sub_le hx (hcum0 (t + h) hth)
    have hsplit : h * (rh h t + 0) - cumRate r t (t + h) =
        h * (rh h t - r t) + ∫ τ in t..t + h, (r t - r τ) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        (intervalIntegrable_of_ici hr le_rfl hth), intervalIntegral.integral_const, smul_eq_mul,
        add_sub_cancel_left, cumRate]
      ring
    have hI2 : |∫ τ in t..t + h, (r t - r τ)| ≤ η₂ * h := by
      have h' := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := t + h)
        (f := fun τ => r t - r τ) (C := η₂) fun τ hτ => by
          rw [Set.uIoc_of_le hth] at hτ
          rw [Real.norm_eq_abs, abs_sub_comm]
          exact h2 τ ⟨hτ.1.le, hτ.2⟩
      rwa [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh] at h'
    refine hb.trans ?_
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos hh]
    nlinarith [mul_le_mul_of_nonneg_left h1 hh.le]
  -- the value
  have hV := pv_abs_le (hr.mono (Set.Ici_subset_Ici.2 hth)) hc
    (fun u hu => hge u (hth.trans hu)) (fun u hu => hS u (hth.trans hu))
  unfold valDelta
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul]
  have hη : 0 ≤ h * η₁ + h * η₂ := (abs_nonneg _).trans hP2
  have h4 : |factor rh 0 h t - disc r t (t + h)| * |pv r s (t + h)| ≤
      (h * η₁ + h * η₂) * (S / c) := mul_le_mul hP2 hV (abs_nonneg _) hη
  have h5 : (h * η₁ + h * η₂) * (S / c) = h * ((η₁ + η₂) * S / c) := by ring
  nlinarith

/-- Cochrane (2023), (3.5) and (3.31): **the global valuation error bound.** If the one-step
errors along the first `N` grid points are at most `hη`, then
`|V_h(t) − V(t)| ≤ (h + 1/c)η + e^{−chN}(S(h + 1/c) + S/c)`. -/
theorem valErr_le {r s : ℝ → ℝ} {rh : ℝ → ℝ → ℝ} {c h t t₀ S η : ℝ}
    (hr : ContinuousOn r (Set.Ici t₀)) (hs : ContinuousOn s (Set.Ici t₀)) (hc : 0 < c)
    (hh : 0 < h) (ht : t₀ ≤ t) (hη : 0 ≤ η) (hge : ∀ u, t₀ ≤ u → c ≤ r u)
    (hlow : ∀ u, t₀ ≤ u → c ≤ rh h u) (hS : ∀ u, t₀ ≤ u → |s u| ≤ S) (N : ℕ)
    (hδ : ∀ k < N, |valDelta rh r s h (t + k * h)| ≤ h * η) :
    |discVal rh s h t - pv r s t| ≤
      (h + 1 / c) * η + Real.exp (-(c * h)) ^ N * (S * (h + 1 / c) + S / c) := by
  have hgrid : ∀ k : ℕ, t₀ ≤ t + k * h := fun k => by
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh.le]
  set x : ℕ → ℝ := fun k => discVal rh s h (t + k * h) - pv r s (t + k * h) with hxdef
  have hrec : ∀ k, x k = (fun k : ℕ => valDelta rh r s h (t + k * h)) k +
      (fun k : ℕ => factor rh 0 h (t + k * h)) k * x (k + 1) := by
    intro k
    have e : t + ((k + 1 : ℕ) : ℝ) * h = t + k * h + h := by push_cast; ring
    simp only [hxdef, e]
    exact valErr_rec hr hs hc hh (hgrid k) hge hlow hS
  have hit := Money.iterate_discount hrec 0 N
  simp only [zero_add] at hit
  have hx0 : x 0 = discVal rh s h t - pv r s t := by simp [hxdef]
  rw [hx0] at hit
  rw [hit]
  have hq0 := (Real.exp_pos (-(c * h))).le
  have hlow' : ∀ u, t₀ ≤ u → c ≤ rh h u + 0 := fun u hu => by rw [add_zero]; exact hlow u hu
  have hS' : |∑ j ∈ Finset.range N, (∏ k ∈ Finset.range j, factor rh 0 h (t + k * h)) *
      valDelta rh r s h (t + j * h)| ≤ (h + 1 / c) * η := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.range N, |(∏ k ∈ Finset.range j, factor rh 0 h (t + k * h)) *
          valDelta rh r s h (t + j * h)|
        ≤ ∑ j ∈ Finset.range N, Real.exp (-(c * h)) ^ j * (h * η) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [abs_mul, abs_of_pos (show 0 < ∏ k ∈ Finset.range j, factor rh 0 h (t + k * h) from
            cumFactor_pos rh 0 h t j)]
          exact mul_le_mul (cumFactor_le hh.le ht hlow' j) (hδ j (Finset.mem_range.mp hj))
            (abs_nonneg _) (pow_nonneg hq0 j)
      _ = η * (h * ∑ j ∈ Finset.range N, Real.exp (-(c * h)) ^ j) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ ≤ η * (h + 1 / c) := mul_le_mul_of_nonneg_left (sum_geom_le hc hh N) hη
      _ = (h + 1 / c) * η := by ring
  have hVd := discVal_bound hc hh (hgrid N) hlow hS
  have hV := pv_abs_le (hr.mono (Set.Ici_subset_Ici.2 (hgrid N))) hc
    (fun u hu => hge u ((hgrid N).trans hu)) (fun u hu => hS u ((hgrid N).trans hu))
  have hT : |(∏ k ∈ Finset.range N, factor rh 0 h (t + k * h)) * x N| ≤
      Real.exp (-(c * h)) ^ N * (S * (h + 1 / c) + S / c) := by
    rw [abs_mul, abs_of_pos (show 0 < ∏ k ∈ Finset.range N, factor rh 0 h (t + k * h) from
      cumFactor_pos rh 0 h t N)]
    refine mul_le_mul (cumFactor_le hh.le ht hlow' N) ?_ (abs_nonneg _) (pow_nonneg hq0 N)
    simp only [hxdef]
    exact (abs_sub _ _).trans (add_le_add hVd hV)
  exact (abs_add_le _ _).trans (add_le_add hS' hT)

/-! ### Uniform convergence -/

/-- Cochrane (2023), (3.5) and (3.31) (auxiliary): the bound on the one-step valuation error used
in both convergence theorems. -/
theorem val_eta_le {h M S c θ : ℝ} (hh : 0 < h) (hM : 0 ≤ M) (hS : 0 ≤ S) (hc : 0 < c)
    (hθ : 0 < θ) (hhM : h < θ / (3 * (M * S + 1))) :
    θ / 3 + h * M * S + (c * θ / (6 * (S + 1)) + c * θ / (6 * (S + 1))) * S / c ≤ θ := by
  have h1 : h * (3 * (M * S + 1)) < θ := (lt_div_iff₀ (by positivity)).mp hhM
  have h2 : (c * θ / (6 * (S + 1)) + c * θ / (6 * (S + 1))) * S / c = θ / 3 * (S / (S + 1)) := by
    field_simp
    ring
  have h3 : S / (S + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  rw [h2]
  nlinarith [mul_nonneg hM hS]

/-- Cochrane (2023), (3.5), (3.30)–(3.31): **the discrete value of debt converges to the
continuous present value uniformly on compacts.** If the real rate is continuous on `[t₀, ∞)`
with `r ≥ c > 0`, the surplus is continuous and bounded on `[t₀, ∞)`, and the per-period rates
`r_h → r` uniformly on every `[t₀, X]` and are eventually `≥ c` on `[t₀, ∞)`, then
`V_h → ContinuousShort.pv r s` uniformly on every `[t₀, X]` as `h → 0⁺`. -/
theorem val_tendstoUniformlyOn_Icc {r s : ℝ → ℝ} {rh : ℝ → ℝ → ℝ} {c t₀ S : ℝ} (hc : 0 < c)
    (hr : ContinuousOn r (Set.Ici t₀)) (hs : ContinuousOn s (Set.Ici t₀))
    (hge : ∀ u, t₀ ≤ u → c ≤ r u) (hS : ∀ u, t₀ ≤ u → |s u| ≤ S)
    (hlow : ∀ᶠ h in 𝓝[>] 0, ∀ u, t₀ ≤ u → c ≤ rh h u)
    (hconv : ∀ X, TendstoUniformlyOn rh r (𝓝[>] 0) (Set.Icc t₀ X)) (X : ℝ) :
    TendstoUniformlyOn (fun h => discVal rh s h) (pv r s) (𝓝[>] 0) (Set.Icc t₀ X) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS t₀ le_rfl)
  have hc1 : 0 < 1 + 1 / c := by positivity
  have hc2 : 0 < S * (1 + 1 / c) + S / c + 1 := by positivity
  set θ := ε / (4 * (1 + 1 / c)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθε : (1 + 1 / c) * θ = ε / 4 := by rw [hθ]; field_simp
  have hexp : Tendsto (fun L : ℝ => Real.exp (-(c * L)) * (S * (1 + 1 / c) + S / c + 1)) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun L : ℝ => -(c * L)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hc)
    simpa using (Real.tendsto_exp_atBot.comp h1).mul_const (S * (1 + 1 / c) + S / c + 1)
  obtain ⟨L, hL, hL0⟩ := ((hexp.eventually (gt_mem_nhds (half_pos hε))).and
    (eventually_gt_atTop 0)).exists
  set Y := max t₀ X + L + 1 with hY
  have hY0 : t₀ ≤ Y := by have := le_max_left t₀ X; linarith
  have hKr : ContinuousOn r (Set.Icc t₀ Y) := hr.mono Set.Icc_subset_Ici_self
  have hKs : ContinuousOn s (Set.Icc t₀ Y) := hs.mono Set.Icc_subset_Ici_self
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hKr
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ ⟨le_rfl, hY0⟩)
  obtain ⟨δr, hδr0, hδr⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hKr) (c * θ / (6 * (S + 1)))
      (by positivity)
  obtain ⟨δs, hδs0, hδs⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hKs) (θ / 3) (by positivity)
  have hconv' := Metric.tendstoUniformlyOn_iff.mp (hconv Y) (c * θ / (6 * (S + 1)))
    (by positivity)
  have hsmall : Set.Ioo (0 : ℝ) (min 1 (min (min δr δs) (θ / (3 * (M * S + 1))))) ∈
      𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hlow, hconv', hsmall] with h hlowh hconvh hhs
  obtain ⟨hh0, hh1⟩ := hhs
  have hh1' : h < 1 := lt_of_lt_of_le hh1 (min_le_left _ _)
  have hhδr : h < δr :=
    lt_of_lt_of_le hh1 ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hhδs : h < δs :=
    lt_of_lt_of_le hh1 ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hhM : h < θ / (3 * (M * S + 1)) :=
    lt_of_lt_of_le hh1 ((min_le_right _ _).trans (min_le_right _ _))
  intro t ht
  have ht' : t₀ ≤ t := ht.1
  have htX : t ≤ max t₀ X := ht.2.trans (le_max_right _ _)
  set N := ⌈L / h⌉₊ with hNdef
  have hN1 : L ≤ N * h := (div_le_iff₀ hh0).mp (Nat.le_ceil _)
  have hN2 : (N : ℝ) * h < L + h := by
    have h1 := Nat.ceil_lt_add_one (div_nonneg hL0.le hh0.le) (R := ℝ)
    rw [← hNdef] at h1
    have h2 := mul_lt_mul_of_pos_right h1 hh0
    rwa [add_mul, div_mul_cancel₀ _ hh0.ne', one_mul] at h2
  set η := θ / 3 + h * M * S + (c * θ / (6 * (S + 1)) + c * θ / (6 * (S + 1))) * S / c
    with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hηθ : η ≤ θ := val_eta_le hh0 hM0 hS0 hc hθ0 hhM
  have hbound := valErr_le hr hs hc hh0 ht' hη0 hge hlowh hS N fun k hk => by
    have hsk : t₀ ≤ t + k * h := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh0.le]
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    have hsY : t + k * h + h ≤ Y := by nlinarith
    have hmem : ∀ u ∈ Set.Icc (t + k * h) (t + k * h + h), u ∈ Set.Icc t₀ Y :=
      fun u hu => ⟨hsk.trans hu.1, hu.2.trans hsY⟩
    have hs0 : t + k * h ∈ Set.Icc t₀ Y := hmem _ ⟨le_rfl, by linarith⟩
    have hd : ∀ u ∈ Set.Icc (t + k * h) (t + k * h + h), dist u (t + k * h) < min δr δs := by
      intro u hu
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
      exact lt_min (by linarith [hu.2]) (by linarith [hu.2])
    have e : h * (θ / 3 + h * M * S + (c * θ / (6 * (S + 1)) + c * θ / (6 * (S + 1))) * S / c) =
        h * η := by rw [hηdef]
    rw [← e]
    refine valDelta_le (hr.mono (Set.Ici_subset_Ici.2 hsk)) (hs.mono (Set.Ici_subset_Ici.2 hsk))
      hc hh0 (fun u hu => hge u (hsk.trans hu)) (hlowh _ hsk) (fun u hu => hS u (hsk.trans hu))
      (fun u hu => by rw [← Real.norm_eq_abs]; exact hM u (hmem u hu)) ?_ ?_ ?_
    · have h1 := hconvh _ hs0
      rw [Real.dist_eq, abs_sub_comm] at h1
      exact h1.le
    · intro u hu
      have h1 := hδr u (hmem u hu) _ hs0 ((hd u hu).trans_le (min_le_left _ _))
      rw [Real.dist_eq] at h1
      exact h1.le
    · intro u hu
      have h1 := hδs u (hmem u hu) _ hs0 ((hd u hu).trans_le (min_le_right _ _))
      rw [Real.dist_eq] at h1
      exact h1.le
  have hq : Real.exp (-(c * h)) ^ N ≤ Real.exp (-(c * L)) := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    nlinarith
  have h2 : (h + 1 / c) * η ≤ (1 + 1 / c) * θ := mul_le_mul (by linarith) hηθ hη0 hc1.le
  have h3 : Real.exp (-(c * h)) ^ N * (S * (h + 1 / c) + S / c) ≤
      Real.exp (-(c * L)) * (S * (1 + 1 / c) + S / c + 1) := by
    refine mul_le_mul hq ?_ (by positivity) (Real.exp_pos _).le
    nlinarith
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- Cochrane (2023), (3.5), (3.30)–(3.31): **the discrete value of debt converges to the
continuous present value uniformly on `[t₀, ∞)`** when the data allow it: the real rate is
bounded and uniformly continuous with `r ≥ c > 0`, the surplus is bounded and uniformly
continuous, and the per-period rates `r_h → r` uniformly on `[t₀, ∞)`, eventually `≥ c`. -/
theorem val_tendstoUniformlyOn_Ici {r s : ℝ → ℝ} {rh : ℝ → ℝ → ℝ} {c t₀ S M : ℝ} (hc : 0 < c)
    (hr : UniformContinuousOn r (Set.Ici t₀)) (hs : UniformContinuousOn s (Set.Ici t₀))
    (hge : ∀ u, t₀ ≤ u → c ≤ r u) (hS : ∀ u, t₀ ≤ u → |s u| ≤ S)
    (hM : ∀ u, t₀ ≤ u → |r u| ≤ M) (hlow : ∀ᶠ h in 𝓝[>] 0, ∀ u, t₀ ≤ u → c ≤ rh h u)
    (hconv : TendstoUniformlyOn rh r (𝓝[>] 0) (Set.Ici t₀)) :
    TendstoUniformlyOn (fun h => discVal rh s h) (pv r s) (𝓝[>] 0) (Set.Ici t₀) := by
  have hrc : ContinuousOn r (Set.Ici t₀) := hr.continuousOn
  have hsc : ContinuousOn s (Set.Ici t₀) := hs.continuousOn
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS t₀ le_rfl)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t₀ le_rfl)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc1 : 0 < 1 + 1 / c := by positivity
  set θ := ε / (2 * (1 + 1 / c)) with hθ
  have hθ0 : 0 < θ := by positivity
  have hθε : (1 + 1 / c) * θ < ε := by
    rw [hθ]
    have : (1 + 1 / c) * (ε / (2 * (1 + 1 / c))) = ε / 2 := by field_simp
    linarith
  obtain ⟨δr, hδr0, hδr⟩ := Metric.uniformContinuousOn_iff.mp hr (c * θ / (6 * (S + 1)))
    (by positivity)
  obtain ⟨δs, hδs0, hδs⟩ := Metric.uniformContinuousOn_iff.mp hs (θ / 3) (by positivity)
  have hconv' := Metric.tendstoUniformlyOn_iff.mp hconv (c * θ / (6 * (S + 1))) (by positivity)
  have hsmall : Set.Ioo (0 : ℝ) (min 1 (min (min δr δs) (θ / (3 * (M * S + 1))))) ∈
      𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
  filter_upwards [hlow, hconv', hsmall] with h hlowh hconvh hhs
  obtain ⟨hh0, hh1⟩ := hhs
  have hh1' : h < 1 := lt_of_lt_of_le hh1 (min_le_left _ _)
  have hhδr : h < δr :=
    lt_of_lt_of_le hh1 ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hhδs : h < δs :=
    lt_of_lt_of_le hh1 ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hhM : h < θ / (3 * (M * S + 1)) :=
    lt_of_lt_of_le hh1 ((min_le_right _ _).trans (min_le_right _ _))
  intro t ht
  have ht' : t₀ ≤ t := ht
  set η := θ / 3 + h * M * S + (c * θ / (6 * (S + 1)) + c * θ / (6 * (S + 1))) * S / c
    with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hηθ : η ≤ θ := val_eta_le hh0 hM0 hS0 hc hθ0 hhM
  have hbound : ∀ N : ℕ, |discVal rh s h t - pv r s t| ≤
      (h + 1 / c) * η + Real.exp (-(c * h)) ^ N * (S * (h + 1 / c) + S / c) := by
    intro N
    refine valErr_le hrc hsc hc hh0 ht' hη0 hge hlowh hS N fun k _ => ?_
    have hsk : t₀ ≤ t + k * h := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hh0.le]
    have hmem : ∀ u ∈ Set.Icc (t + k * h) (t + k * h + h), u ∈ Set.Ici t₀ :=
      fun u hu => hsk.trans hu.1
    have hd : ∀ u ∈ Set.Icc (t + k * h) (t + k * h + h), dist u (t + k * h) < min δr δs := by
      intro u hu
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
      exact lt_min (by linarith [hu.2]) (by linarith [hu.2])
    have e : h * (θ / 3 + h * M * S + (c * θ / (6 * (S + 1)) + c * θ / (6 * (S + 1))) * S / c) =
        h * η := by rw [hηdef]
    rw [← e]
    refine valDelta_le (hrc.mono (Set.Ici_subset_Ici.2 hsk)) (hsc.mono (Set.Ici_subset_Ici.2 hsk))
      hc hh0 (fun u hu => hge u (hsk.trans hu)) (hlowh _ hsk) (fun u hu => hS u (hsk.trans hu))
      (fun u hu => hM u (hmem u hu)) ?_ ?_ ?_
    · have h1 := hconvh _ hsk
      rw [Real.dist_eq, abs_sub_comm] at h1
      exact h1.le
    · intro u hu
      have h1 := hδr u (hmem u hu) _ hsk ((hd u hu).trans_le (min_le_left _ _))
      rw [Real.dist_eq] at h1
      exact h1.le
    · intro u hu
      have h1 := hδs u (hmem u hu) _ hsk ((hd u hu).trans_le (min_le_right _ _))
      rw [Real.dist_eq] at h1
      exact h1.le
  have hlim : Tendsto (fun N : ℕ => (h + 1 / c) * η +
      Real.exp (-(c * h)) ^ N * (S * (h + 1 / c) + S / c)) atTop (𝓝 ((h + 1 / c) * η)) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-(c * h))).le
      (exp_neg_lt_one (mul_pos hc hh0))).mul_const (S * (h + 1 / c) + S / c)
    simpa using h1.const_add ((h + 1 / c) * η)
  have hle := ge_of_tendsto' hlim hbound
  rw [Real.dist_eq, abs_sub_comm]
  have h2 : (h + 1 / c) * η ≤ (1 + 1 / c) * θ := mul_le_mul (by linarith) hηθ hη0 hc1.le
  linarith

/-- Cochrane (2023), (3.30)–(3.31) and A1.4: **the limit of the discrete valuation recursion is
the unique transversality solution of `V' = rV − s`.** Under the hypotheses of
`val_tendstoUniformlyOn_Icc`, every `V` solving the flow identity (3.30) on `[t₀, ∞)` with the
transversality condition is the uniform-on-compacts limit of the discrete values. -/
theorem val_tendsto_unique_ode_solution {r s V : ℝ → ℝ} {rh : ℝ → ℝ → ℝ} {c t₀ S : ℝ}
    (hc : 0 < c) (hr : ContinuousOn r (Set.Ici t₀)) (hs : ContinuousOn s (Set.Ici t₀))
    (hge : ∀ u, t₀ ≤ u → c ≤ r u) (hS : ∀ u, t₀ ≤ u → |s u| ≤ S)
    (hlow : ∀ᶠ h in 𝓝[>] 0, ∀ u, t₀ ≤ u → c ≤ rh h u)
    (hconv : ∀ X, TendstoUniformlyOn rh r (𝓝[>] 0) (Set.Icc t₀ X))
    (hF : FlowOn r s V t₀) (hT : TVC r V t₀) (X : ℝ) :
    TendstoUniformlyOn (fun h => discVal rh s h) V (𝓝[>] 0) (Set.Icc t₀ X) := by
  have hU := eqOn_pv_of_tvc hr hs hF hT (pvIntegrable_of_bound hr hs hc hge hS)
  exact (val_tendstoUniformlyOn_Icc hc hr hs hge hS hlow hconv X).congr_right
    fun u hu => (hU (Set.Icc_subset_Ici_self hu)).symm

/-- Cochrane (2023), (3.5) and (3.31): with exact compounding `r_h = r` the hypotheses on the
per-period rates hold, so `V_h → pv r s` uniformly on every `[t₀, X]`. -/
theorem val_tendstoUniformlyOn_Icc_exact {r s : ℝ → ℝ} {c t₀ S : ℝ} (hc : 0 < c)
    (hr : ContinuousOn r (Set.Ici t₀)) (hs : ContinuousOn s (Set.Ici t₀))
    (hge : ∀ u, t₀ ≤ u → c ≤ r u) (hS : ∀ u, t₀ ≤ u → |s u| ≤ S) (X : ℝ) :
    TendstoUniformlyOn (fun h => discVal (fun _ u => r u) s h) (pv r s) (𝓝[>] 0)
      (Set.Icc t₀ X) := by
  have hge' : ∀ u, t₀ ≤ u → c ≤ r u + 0 := fun u hu => by rw [add_zero]; exact hge u hu
  refine val_tendstoUniformlyOn_Icc hc hr hs hge hS ?_ (fun Y => (exact_hyps hge' _).2) X
  simpa using (exact_hyps hge' Set.univ).1

/-- Cochrane (2023), (3.5) and §3.6.2: the bond price of `TidyR6DiscreteBondLimit` is the
discrete value of the unit coupon at the rate `i + ϖ`. -/
theorem discPrice_eq_discVal (ih : ℝ → ℝ → ℝ) (ϖ h t : ℝ) :
    discPrice ih ϖ h t = discVal (fun h u => ih h u + ϖ) (fun _ => 1) h t := by
  unfold discPrice discVal cumFactor factor
  simp only [mul_one, add_zero]

end Cochrane.Generality.TidyR6DiscreteValuationLimit
