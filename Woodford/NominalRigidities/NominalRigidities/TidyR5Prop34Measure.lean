/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.TidyR5Prop34Uncertainty
import NominalRigidities.TidyR5ExpectationsMeasure

/-!
# Proposition 3.4 with `ω̃θ < 0` on a genuine probability space

Woodford (2003), *Interest and Prices*, Chapter 3, §2.1, Proposition 3.4 (p. 182) and
Appendix B.3 (pp. 659–661), with `E_t` Mathlib's conditional expectation on a probability space
(`TidyR5ExpectationsMeasure.MeasExpectationSystem`).

On an infinite probability space `E_t` is only defined (non-junk) on integrable functions, and the
dominated-convergence argument of `TidyR5Prop34Uncertainty.E_hasSum` is no longer available: an
almost-everywhere convergent forward sum need not commute with `E_t`. The correct statement
needs the forward sum of (2.8) to converge **in `L¹`** (`L1Fwd`), and then:

* `prop34_unique_of_w_neg_L1`: for `−1 < ω̃θ < 0`, any two solutions of (2.5) and (2.8)
  (`MEq28`, the a.e. form of (2.8)) with integrable, predetermined price indices, the same initial
  price level and `L¹`-convergent forward sums coincide almost surely — no difference-stationarity
  restriction and no restriction on marginal cost beyond integrability.

Without `L1Fwd` the statement is false: `TidyR5Prop34NonUnique` builds, on an i.i.d. economy,
a second integrable predetermined solution of (2.5) and (2.8) with absolutely convergent forward
sums at every state. The key analytic lemma is `condExp_tsum_of_summable_integral`
(`E_t` through an `L¹`-convergent series).

On a finite fully supported probability space the measure-theoretic system is a core
`ExpectationSystem` (`TidyR5ExpectationsMeasure.MeasExpectationSystem.toExpectationSystem`), and
uniqueness holds with no `L¹` condition (`prop34_unique_of_w_neg_finite`).
-/

namespace Woodford.NominalRigidities.TidyR5Prop34Measure

open MeasureTheory Filter Topology Calvo QuadraticRoots
open TidyR5ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Woodford (2003), eq. (2.8), p. 181, on a probability space: almost surely, at every date the
forward sum `∑_j (αβ)ʲ E_t[log µ + log S_{t+j} + ω̃θ log P_{t+j}]` converges and
`log p*_t = (1 − αβ)/(1 + ω̃θ)` times it. -/
def MEq28 (α β w m : ℝ) (s P pstar : ℕ → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂S.μ, ∀ t, Summable (fun j => (α * β) ^ j * S.E t (costTerm m w s P (t + j)) ω) ∧
    pstar t ω = (1 - α * β) / (1 + w) * ∑' j, (α * β) ^ j * S.E t (costTerm m w s P (t + j)) ω

/-- Woodford (2003), eq. (2.8), p. 181 (**the forward sum converges in `L¹`**):
`∑_j (αβ)ʲ ‖E_t c_{t+j}‖_{L¹} < ∞` at every date. -/
def L1Fwd (α β : ℝ) (c : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Summable (fun j => (α * β) ^ j * ∫ ω, |S.E t (c (t + j)) ω| ∂S.μ)

omit [MeasurableSpace Ω] in
/-- Woodford (2003), eq. (2.8): the cost terms of two price paths differ by `ω̃θ` times the
difference of the price indices. -/
theorem costTerm_sub (m w : ℝ) (s P P' : ℕ → Ω → ℝ) (t j : ℕ) :
    costTerm m w s P (t + j) - costTerm m w s P' (t + j)
      = w • (P (t + 1 + j) - P' (t + 1 + j)) := by
  funext ω
  simp only [costTerm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show t + j + 1 = t + 1 + j by omega]
  ring

/-- Woodford (2003), App. B.3, p. 659 (**`E_t` through an `L¹`-convergent series**): if every
`f_j` is integrable and `∑_j ‖f_j‖_{L¹} < ∞`, then `E_t ∑_j f_j = ∑_j E_t f_j` a.e. -/
theorem condExp_tsum_of_summable_integral {f : ℕ → Ω → ℝ} (hf : ∀ j, Integrable (f j) S.μ)
    (hs : Summable (fun j => ∫ ω, |f j ω| ∂S.μ)) (t : ℕ) :
    S.E t (fun ω => ∑' j, f j ω) =ᵐ[S.μ] fun ω => ∑' j, S.E t (f j) ω := by
  refine condExp_tsum (fun j => (hf j).aestronglyMeasurable) ?_
  have he : ∀ j, ∫⁻ ω, ‖f j ω‖ₑ ∂S.μ = ENNReal.ofReal (∫ ω, |f j ω| ∂S.μ) := by
    intro j
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf j)]
    rfl
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg fun ω => abs_nonneg _) hs]
  exact ENNReal.ofReal_ne_top

/-- Woodford (2003), **Proposition 3.4 with `ω̃θ < 0` on a probability space** (p. 182; App. B.3,
pp. 659–661). Let `0 < α < 1`, `0 < β < 1`, `−1 < ω̃θ < 0`, and let marginal cost `log S_t` be
integrable at every date. Take two solutions `(log P, log p*)`, `(log P', log p*')` of (2.5) and
(2.8) (a.e. form `MEq28`) with integrable price indices, predetermined (`log P_t` known at `t`),
almost surely equal initial price levels, and forward sums converging in `L¹` (`L1Fwd`). Then
the price indices and reset prices coincide almost surely at every date. -/
theorem prop34_unique_of_w_neg_L1 {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s P pstar P' pstar' : ℕ → Ω → ℝ}
    (hsi : ∀ t, Integrable (s t) S.μ) (hPi : ∀ t, Integrable (P t) S.μ)
    (hPi' : ∀ t, Integrable (P' t) S.μ) (hpre : ∀ t, StronglyMeasurable[S.𝓕 t] (P (t + 1)))
    (hpre' : ∀ t, StronglyMeasurable[S.𝓕 t] (P' (t + 1))) (h0 : P 0 =ᵐ[S.μ] P' 0)
    (h25 : Eq25 α P pstar) (h25' : Eq25 α P' pstar') (h28 : MEq28 S α β w m s P pstar)
    (h28' : MEq28 S α β w m s P' pstar') (hL : L1Fwd S α β (costTerm m w s P))
    (hL' : L1Fwd S α β (costTerm m w s P')) :
    ∀ t, P t =ᵐ[S.μ] P' t ∧ pstar t =ᵐ[S.μ] pstar' t := by
  obtain ⟨hξ, hl0, -, -, -⟩ := calvo_roots hα0 hα1 hβ0 hβ1 hw
  set l1 := lam1 β (calvoXi α β w)
  set l2 := lam2 β (calvoXi α β w)
  have hl2 : 1 < l2 := one_lt_lam2 hβ0 hξ
  have hl2ne : l2 ≠ 0 := by linarith
  have hq0 : 0 ≤ α * β := (mul_pos hα0 hβ0).le
  have hql2 : 1 ≤ α * β * l2 :=
    TidyR5Prop34Uncertainty.one_le_alpha_beta_lam2 hα0 hα1 hβ0 hβ1 hwneg hw
  have hw0 : w ≠ 0 := hwneg.ne
  have h1a : (1 : ℝ) - α ≠ 0 := by linarith
  set X : ℕ → Ω → ℝ := fun t => P t - P' t with hX
  have hXi : ∀ t, Integrable (X t) S.μ := fun t => (hPi t).sub (hPi' t)
  have hXm : ∀ t, StronglyMeasurable[S.𝓕 t] (X (t + 1)) := fun t => (hpre t).sub (hpre' t)
  have hXE : ∀ t, S.E t (X (t + 1)) = X (t + 1) := fun t =>
    S.E_of_stronglyMeasurable (hXm t) (hXi (t + 1))
  have hci : ∀ (Q : ℕ → Ω → ℝ), (∀ t, Integrable (Q t) S.μ) → ∀ T,
      Integrable (costTerm m w s Q T) S.μ := by
    intro Q hQ T
    exact ((integrable_const m).add (hsi T)).add ((hQ (T + 1)).const_mul w)
  -- forecasts of the price difference
  set Y : ℕ → ℕ → Ω → ℝ := fun t j => S.E t (X (t + 1 + j)) with hY
  have hEdiff : ∀ t j, S.E t (costTerm m w s P (t + j)) - S.E t (costTerm m w s P' (t + j))
      =ᵐ[S.μ] w • Y t j := by
    intro t j
    refine (S.E_sub (hci P hPi (t + j)) (hci P' hPi' (t + j)) t).symm.trans ?_
    rw [costTerm_sub]
    exact S.E_smul w _ t
  have hEdiff' : ∀ᵐ ω ∂S.μ, ∀ t j, S.E t (costTerm m w s P (t + j)) ω
      - S.E t (costTerm m w s P' (t + j)) ω = w * Y t j ω := by
    rw [ae_all_iff]; intro t; rw [ae_all_iff]; intro j
    filter_upwards [hEdiff t j] with ω h
    simpa using h
  -- the difference solves the homogeneous forward condition a.e.
  have hC : ∀ᵐ ω ∂S.μ, ∀ t, Summable (fun j => (α * β) ^ j * Y t j ω) ∧
      X (t + 1) ω - α * X t ω
        = (1 - α) * ((1 - α * β) / (1 + w)) * w * ∑' j, (α * β) ^ j * Y t j ω := by
    filter_upwards [h28, h28', hEdiff'] with ω h1 h2 h3 t
    obtain ⟨hs1, hv1⟩ := h1 t
    obtain ⟨hs2, hv2⟩ := h2 t
    have hterm : ∀ j, (α * β) ^ j * Y t j ω = w⁻¹ * ((α * β) ^ j *
        S.E t (costTerm m w s P (t + j)) ω
          - (α * β) ^ j * S.E t (costTerm m w s P' (t + j)) ω) := by
      intro j
      rw [← mul_sub, h3 t j]
      field_simp
    have hsum : Summable (fun j => (α * β) ^ j * Y t j ω) := by
      simp_rw [hterm]
      exact (hs1.sub hs2).mul_left _
    refine ⟨hsum, ?_⟩
    have hdiff : pstar t ω - pstar' t ω
        = (1 - α * β) / (1 + w) * w * ∑' j, (α * β) ^ j * Y t j ω := by
      rw [hv1, hv2, ← mul_sub, ← hs1.tsum_sub hs2]
      simp_rw [hterm]
      rw [tsum_mul_left]
      field_simp
    simp only [hX, Pi.sub_apply]
    rw [h25 t ω, h25' t ω]
    linear_combination (1 - α) * hdiff
  -- `L¹` bounds on the forecasts of the difference
  have hYL : ∀ t, Summable (fun j => (α * β) ^ j * ∫ ω, |Y t j ω| ∂S.μ) := by
    intro t
    have hb : ∀ j, (α * β) ^ j * ∫ ω, |Y t j ω| ∂S.μ ≤ |w|⁻¹ * ((α * β) ^ j *
        ∫ ω, |S.E t (costTerm m w s P (t + j)) ω| ∂S.μ + (α * β) ^ j *
        ∫ ω, |S.E t (costTerm m w s P' (t + j)) ω| ∂S.μ) := by
      intro j
      have hint : ∫ ω, |Y t j ω| ∂S.μ ≤ |w|⁻¹ * (∫ ω, |S.E t (costTerm m w s P (t + j)) ω| ∂S.μ
          + ∫ ω, |S.E t (costTerm m w s P' (t + j)) ω| ∂S.μ) := by
        rw [← integral_add (S.integrable_E t _).abs (S.integrable_E t _).abs,
          ← integral_const_mul]
        refine integral_mono_ae (S.integrable_E t _).abs
          (((S.integrable_E t _).abs.add (S.integrable_E t _).abs).const_mul _) ?_
        filter_upwards [hEdiff'] with ω h
        have e : |Y t j ω| = |w|⁻¹ * |S.E t (costTerm m w s P (t + j)) ω
            - S.E t (costTerm m w s P' (t + j)) ω| := by
          rw [h t j, abs_mul]
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left (abs_sub _ _) (inv_nonneg.mpr (abs_nonneg w))
      calc (α * β) ^ j * ∫ ω, |Y t j ω| ∂S.μ
          ≤ (α * β) ^ j * (|w|⁻¹ * (∫ ω, |S.E t (costTerm m w s P (t + j)) ω| ∂S.μ
            + ∫ ω, |S.E t (costTerm m w s P' (t + j)) ω| ∂S.μ)) :=
            mul_le_mul_of_nonneg_left hint (pow_nonneg hq0 j)
        _ = _ := by ring
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hq0 j)
      (integral_nonneg fun ω => abs_nonneg _)) hb ?_
    exact ((hL t).add (hL' t)).mul_left _
  -- `E_t` passes through the date-`t+1` forward sum
  have hswap : ∀ t, S.E t (fun ω => ∑' j, (α * β) ^ j * Y (t + 1) j ω)
      =ᵐ[S.μ] fun ω => ∑' j, (α * β) ^ j * Y t (j + 1) ω := by
    intro t
    have hfi : ∀ j, Integrable (fun ω => (α * β) ^ j * Y (t + 1) j ω) S.μ :=
      fun j => (S.integrable_E _ _).const_mul _
    have hfs : Summable (fun j => ∫ ω, |(α * β) ^ j * Y (t + 1) j ω| ∂S.μ) := by
      refine (hYL (t + 1)).congr fun j => ?_
      simp_rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 j)]
      rw [integral_const_mul]
    refine (condExp_tsum_of_summable_integral S hfi hfs t).trans ?_
    have hterm : ∀ j, S.E t (fun ω => (α * β) ^ j * Y (t + 1) j ω)
        =ᵐ[S.μ] fun ω => (α * β) ^ j * Y t (j + 1) ω := by
      intro j
      have e1 : (fun ω => (α * β) ^ j * Y (t + 1) j ω) = (α * β) ^ j • Y (t + 1) j := rfl
      rw [e1]
      refine (S.E_smul _ _ t).trans ?_
      have e2 : Y t (j + 1) = S.E t (X (t + 1 + 1 + j)) := by
        simp only [hY]
        rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega]
      filter_upwards [S.E_tower (Nat.le_succ t) (X (t + 1 + 1 + j))] with ω h
      simp only [Pi.smul_apply, smul_eq_mul, hY] at h ⊢
      rw [h, ← congrFun e2 ω]
    filter_upwards [ae_all_iff.mpr hterm] with ω h
    exact tsum_congr fun j => h j
  -- the homogeneous (B.13): `X_{t+1} − αX_t = cX_{t+1} + αβ(E_t X_{t+2} − αX_{t+1})`
  have hrec : ∀ t, ∀ᵐ ω ∂S.μ, X (t + 1) ω - α * X t ω
      = (1 - α) * ((1 - α * β) / (1 + w)) * w * X (t + 1) ω
      + α * β * (S.E t (X (t + 1 + 1)) ω - α * X (t + 1) ω) := by
    intro t
    have hnext : (fun ω => X (t + 1 + 1) ω - α * X (t + 1) ω)
        =ᵐ[S.μ] ((1 - α) * ((1 - α * β) / (1 + w)) * w) •
          fun ω => ∑' j, (α * β) ^ j * Y (t + 1) j ω := by
      filter_upwards [hC] with ω h
      rw [(h (t + 1)).2]
      rfl
    have hE := S.E_congr hnext t
    have hl : S.E t (fun ω => X (t + 1 + 1) ω - α * X (t + 1) ω)
        =ᵐ[S.μ] fun ω => S.E t (X (t + 1 + 1)) ω - α * X (t + 1) ω := by
      have e : (fun ω => X (t + 1 + 1) ω - α * X (t + 1) ω) = X (t + 1 + 1) - α • X (t + 1) := rfl
      rw [e]
      filter_upwards [S.E_sub (hXi _) ((hXi _).smul α) t, S.E_smul α (X (t + 1)) t]
        with ω h1 h2
      rw [h1, Pi.sub_apply, h2, Pi.smul_apply, hXE t, smul_eq_mul]
    filter_upwards [hC, hE, hl, S.E_smul ((1 - α) * ((1 - α * β) / (1 + w)) * w) _ t, hswap t]
      with ω hc he hl' hs hsw
    obtain ⟨hsum, hv⟩ := hc t
    rw [hl', hs, Pi.smul_apply, hsw, smul_eq_mul] at he
    rw [hv, hsum.tsum_eq_zero_add]
    have hY0 : Y t 0 ω = X (t + 1) ω := by
      simp only [hY, add_zero]
      rw [hXE t]
    have htail : ∑' j, (α * β) ^ (j + 1) * Y t (j + 1) ω
        = α * β * ∑' j, (α * β) ^ j * Y t (j + 1) ω := by
      rw [← tsum_mul_left]
      exact tsum_congr fun j => by rw [pow_succ]; ring
    rw [htail, pow_zero, one_mul, hY0]
    linear_combination (-(α * β)) * he
  -- (B.14) for the difference: `d_t = λ₂⁻¹ E_t d_{t+1}` with `d_t = X_{t+1} − λ₁ X_t`
  set d : ℕ → Ω → ℝ := fun t => X (t + 1) - l1 • X t with hd_def
  have hEd1 : ∀ t, S.E t (d (t + 1))
      =ᵐ[S.μ] fun ω => S.E t (X (t + 1 + 1)) ω - l1 * X (t + 1) ω := by
    intro t
    filter_upwards [S.E_sub (hXi _) ((hXi _).smul l1) t, S.E_smul l1 (X (t + 1)) t] with ω h1 h2
    simp only [hd_def]
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, hXE t, smul_eq_mul]
  have hd : ∀ t, d t =ᵐ[S.μ] l2⁻¹ • S.E t (d (t + 1)) := by
    intro t
    filter_upwards [hrec t, hEd1 t] with ω hr he
    rw [Pi.smul_apply, he, smul_eq_mul]
    have hB13 := (recursive_iff_B13 (β := β) hα0 hα1 hw.ne' (X t ω) (X (t + 1) ω)
      (S.E t (X (t + 1 + 1)) ω) 0).mp (by
        have key : (X (t + 1) ω - α * X t ω) / (1 - α) - ((1 - α * β) / (1 + w) * (0 + w *
            X (t + 1) ω) + α * β * ((S.E t (X (t + 1 + 1)) ω - α * X (t + 1) ω) / (1 - α)))
            = (X (t + 1) ω - α * X t ω - ((1 - α) * ((1 - α * β) / (1 + w)) * w * X (t + 1) ω
              + α * β * (S.E t (X (t + 1 + 1)) ω - α * X (t + 1) ω))) / (1 - α) := by
          field_simp
          ring
        rw [sub_eq_zero.mpr hr, zero_div] at key
        linear_combination key)
    have hB14 := (B13_iff_B14 hβ0 hξ _ _ _ _).mp hB13
    simp only [hd_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hB14]
    ring
  -- iterate: `E_t d_{t+k} = λ₂ᵏ d_t`
  have hdm : ∀ t, AEStronglyMeasurable[S.𝓕 t] (d t) S.μ := fun t =>
    ⟨l2⁻¹ • S.E t (d (t + 1)), (S.stronglyMeasurable_E t _).const_smul _, hd t⟩
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => (hXi _).sub ((hXi t).smul l1)
  have hiter : ∀ t k, S.E t (d (t + k)) =ᵐ[S.μ] l2 ^ k • d t := by
    intro t k
    induction k with
    | zero =>
      simp only [add_zero, pow_zero, one_smul]
      exact S.E_of_aestronglyMeasurable (hdm t) (hdi t)
    | succ k ih =>
      have hstep : S.E (t + k) (d (t + k + 1)) =ᵐ[S.μ] l2 • d (t + k) := by
        filter_upwards [hd (t + k)] with ω h
        rw [Pi.smul_apply, h, Pi.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ hl2ne, one_mul]
      rw [show t + (k + 1) = t + k + 1 by omega]
      refine (S.E_tower (Nat.le_add_right t k) (d (t + k + 1))).symm.trans ?_
      refine (S.E_congr hstep t).trans ((S.E_smul l2 _ t).trans ?_)
      filter_upwards [ih] with ω h
      rw [Pi.smul_apply, h, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        pow_succ]
      ring
  -- `E_t d_{t+k+1} = Y_{t,k+1} − λ₁ Y_{t,k}`
  have hEdY : ∀ t k, S.E t (d (t + (k + 1))) =ᵐ[S.μ] fun ω => Y t (k + 1) ω - l1 * Y t k ω := by
    intro t k
    have e : d (t + (k + 1)) = X (t + 1 + (k + 1)) - l1 • X (t + 1 + k) := by
      simp only [hd_def]
      rw [show t + (k + 1) + 1 = t + 1 + (k + 1) by omega,
        show t + (k + 1) = t + 1 + k by omega]
    rw [e]
    filter_upwards [S.E_sub (hXi _) ((hXi _).smul l1) t, S.E_smul l1 (X (t + 1 + k)) t] with ω h1 h2
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]
  -- every `d_t` vanishes a.e.
  have hd0 : ∀ t, d t =ᵐ[S.μ] 0 := by
    intro t
    filter_upwards [hC, ae_all_iff.mpr (fun k => hiter t (k + 1)),
      ae_all_iff.mpr (fun k => hEdY t k)] with ω hc hit hey
    have hqe : Tendsto (fun k : ℕ => (α * β) ^ k * Y t k ω) atTop (𝓝 0) :=
      (hc t).1.tendsto_atTop_zero
    have hid : ∀ k, (α * β * l2) ^ (k + 1) * d t ω
        = (α * β) ^ (k + 1) * Y t (k + 1) ω - α * β * l1 * ((α * β) ^ k * Y t k ω) := by
      intro k
      have h1 := hit k
      have h2 := hey k
      rw [h2, Pi.smul_apply, smul_eq_mul] at h1
      rw [mul_pow, mul_assoc, ← h1]
      ring
    have hlim : Tendsto (fun k : ℕ => (α * β * l2) ^ (k + 1) * d t ω) atTop (𝓝 0) := by
      have h1 := (tendsto_add_atTop_iff_nat 1).mpr hqe
      have h2 := hqe.const_mul (α * β * l1)
      have h := h1.sub h2
      simp only [mul_zero, sub_zero] at h
      exact h.congr fun k => (hid k).symm
    have hle : ∀ k : ℕ, |d t ω| ≤ |(α * β * l2) ^ (k + 1) * d t ω| := by
      intro k
      rw [abs_mul, abs_of_nonneg (pow_nonneg (mul_nonneg hq0 (by linarith)) _)]
      exact le_mul_of_one_le_left (abs_nonneg _) (one_le_pow₀ hql2)
    have h0' : |d t ω| ≤ 0 :=
      ge_of_tendsto' ((continuous_abs.tendsto 0).comp hlim |>.trans (by rw [abs_zero])) hle
    exact abs_nonpos_iff.mp h0'
  -- hence `X = 0` a.e. at every date
  have hX0 : ∀ t, X t =ᵐ[S.μ] 0 := by
    intro t
    induction t with
    | zero =>
      filter_upwards [h0] with ω h
      simp [hX, h]
    | succ t ih =>
      filter_upwards [hd0 t, ih] with ω h1 h2
      simp only [hd_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
      rw [h2, mul_zero, sub_zero] at h1
      exact h1
  have hPP : ∀ t, P t =ᵐ[S.μ] P' t := by
    intro t
    filter_upwards [hX0 t] with ω h
    simp only [hX, Pi.sub_apply, Pi.zero_apply] at h
    linarith
  intro t
  refine ⟨hPP t, ?_⟩
  filter_upwards [hPP t, hPP (t + 1)] with ω h1 h2
  rw [congrFun (pstar_of_eq25 hα1 h25 t) ω, congrFun (pstar_of_eq25 hα1 h25' t) ω, h1, h2]

/-- Woodford (2003), Prop. 3.4 with `ω̃θ < 0` **on a finite, fully supported probability space**:
the measure-theoretic system is a core `ExpectationSystem`
(`MeasExpectationSystem.toExpectationSystem`), so every predetermined solution of (2.5) and
(2.8) is (2.9), with no `L¹` condition (`TidyR5Prop34Uncertainty.prop34_unique_of_w_neg`). -/
theorem prop34_unique_of_w_neg_finite [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) {α β w m : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hwneg : w < 0) (hw : 0 < 1 + w) {s : ℕ → Ω → ℝ}
    (hsa : (S.toExpectationSystem hfull).Adapted s) (hsb : BoundedIncr s) {P0 : Ω → ℝ}
    {P pstar : ℕ → Ω → ℝ} (hP0 : P 0 = P0)
    (hpre : ∀ t, (S.toExpectationSystem hfull).E t (P (t + 1)) = P (t + 1))
    (h25 : Eq25 α P pstar) (h28 : Eq28 (S.toExpectationSystem hfull) α β w m s P pstar) :
    P = Psol (S.toExpectationSystem hfull) α β w m s P0 ∧
      pstar = pstarSol (S.toExpectationSystem hfull) α β w m s P0 :=
  TidyR5Prop34Uncertainty.prop34_unique_of_w_neg _ hα0 hα1 hβ0 hβ1 hwneg hw hsa hsb hP0 hpre
    h25 h28

end Woodford.NominalRigidities.TidyR5Prop34Measure
