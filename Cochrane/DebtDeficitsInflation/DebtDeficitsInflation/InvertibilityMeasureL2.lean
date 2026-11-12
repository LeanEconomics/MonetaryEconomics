/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.InvertibilityMeasure
import DebtDeficitsInflation.ExpectationsMeasureIID
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Invertibility, Wold and Granger causality in `L²` of an i.i.d. probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.3, p. 102, and Online
Appendix Chapter 2, §§2.1.4–2.1.6, pp. 597–601.

The Hilbert-space statements of `Invertibility` and `InvertibilityMeasure` are instantiated in the
genuine probability setting: `H = L²(Ω, P)` with `Ω = ℕ → ℝ`, `P = ν^ℕ` the i.i.d. product of
`ExpectationsMeasureIID` (not finitely supported), and the structural shocks
`e_t = ε_{φ(t)}` for a bijection `φ : ℤ ≃ ℕ` (a `ℤ`-indexed i.i.d. sequence). Inner products are
covariances `E[XY]`, closed spans are mean-square limits of linear combinations, and orthogonal
projections are best linear forecasts (what a VAR estimates).

## Main results

* `iid_whiteNoise`: the shocks are white noise in `L²` (independence and mean zero).
* `iid_not_filter`: `a(ρ) = 0`, `|ρ| ≤ 1` (including `ρ = 1`): no absolutely summable filter of
  the surplus history converges in mean square to the shock.
* `iid_not_mem_pastSpan` (`|ρ| < 1`: the shock is not in the closed span of the surplus history).
* `iid_unit_root`: correction at `ρ = ±1` — the shock IS a mean-square limit of linear
  combinations of current and past surpluses for `s_t = e_t − ρe_{t−1}`;
  `closedSpan_fails_at_unit_root`: so the closed-span statement is false for `|ρ| ≤ 1`.
* `iid_wold_factor`, `iid_granger_general`, `iid_granger_factor`: the factorised Wold statement and
  "debt Granger-causes surpluses" in `L²`.
* `coin_L2`: the fair-coin instance (`σ² = 1`).
-/

namespace Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2

open MeasureTheory ProbabilityTheory Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations (gen)
open Cochrane.DebtDeficitsInflation.ExpectationsMeasure
open Cochrane.DebtDeficitsInflation.ExpectationsMeasureIID
open Cochrane.DebtDeficitsInflation.Invertibility
open Cochrane.DebtDeficitsInflation.Invertibility.Hilbert
open Cochrane.DebtDeficitsInflation.InvertibilityMeasure
open scoped RealInnerProductSpace

variable {ν : ProbabilityMeasure ℝ}

/-- Cochrane (2023), p. 102 (the shocks as second-moment random variables): a bounded i.i.d.
shock is square integrable. -/
theorem memLp_coord {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (i : ℕ) :
    MemLp (fun ω : ℕ → ℝ => ω i) 2 (iidSystem ν).μ :=
  MemLp.of_bound (measurable_pi_apply i).aestronglyMeasurable B
    ((shock_ae_bdd ν hbdd i).mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), p. 102 and Online Appendix p. 597: the structural shocks as elements of
`L²(ν^ℕ)`, `e_t = ε_{φ(t)}` with `φ : ℤ ≃ ℕ`. -/
noncomputable def shockL2 {B : ℝ} (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (t : ℤ) :
    Lp ℝ 2 (iidSystem ν).μ :=
  (memLp_coord hbdd (Equiv.intEquivNat t)).toLp _

/-- Cochrane (2023), p. 102 (tool): distinct coordinates of the i.i.d. product are uncorrelated
when the mean is zero, `E[ε_iε_j] = 0`. -/
theorem integral_coord_mul {i j : ℕ} (hij : i ≠ j) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) :
    ∫ ω, ω i * ω j ∂(iidSystem ν).μ = 0 := by
  have hind : iIndepFun (fun k (ω : ℕ → ℝ) => ω k) (iidSystem ν).μ :=
    iIndepFun_infinitePi (P := fun _ => (ν : Measure ℝ)) (X := fun _ => id)
      (fun _ => measurable_id)
  rw [(hind.indepFun hij).integral_fun_mul_eq_mul_integral
    (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable]
  have h := integral_shock_fun ν i (f := id) measurable_id
  simp only [id] at h
  change (∫ ω, ω i ∂(iidSystem ν).μ) * _ = 0
  rw [h, hmean, zero_mul]

/-- Cochrane (2023), p. 102, and Online Appendix p. 597: i.i.d. shocks with mean `0`, variance
`σ²` and bounded support are white noise in `L²(ν^ℕ)`: `E[e_te_u] = σ²` if `t = u`, `0`
otherwise. -/
theorem iid_whiteNoise {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    WhiteNoise (shockL2 hbdd) σ2 := by
  intro t u
  rw [L2.inner_def]
  have hc : ∀ τ, (shockL2 hbdd τ : (ℕ → ℝ) → ℝ) =ᵐ[(iidSystem ν).μ]
      fun ω => ω (Equiv.intEquivNat τ) := fun τ => MemLp.coeFn_toLp _
  have hcongr : (fun ω => ⟪(shockL2 hbdd t : (ℕ → ℝ) → ℝ) ω,
      (shockL2 hbdd u : (ℕ → ℝ) → ℝ) ω⟫) =ᵐ[(iidSystem ν).μ]
      fun ω => ω (Equiv.intEquivNat t) * ω (Equiv.intEquivNat u) := by
    filter_upwards [hc t, hc u] with ω h1 h2
    rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
      mul_comm]
  rw [integral_congr_ae hcongr]
  by_cases htu : t = u
  · subst htu
    simp only [↓reduceIte]
    have h := integral_shock_fun ν (Equiv.intEquivNat t) (f := fun x => x ^ 2)
      (measurable_id.pow_const 2)
    rw [hvar] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  · simp only [htu, ↓reduceIte]
    exact integral_coord_mul ((Equiv.intEquivNat).injective.ne htu) hmean

/-! ### The statements in `L²` -/

/-- Cochrane (2023), p. 102, and Online Appendix p. 600, in `L²` of the i.i.d. probability space,
for every `|ρ| ≤ 1` including `ρ = 1`: if `a(ρ) = 0`, no absolutely summable filter of current and
past surpluses converges in mean square to the structural shock. -/
theorem iid_not_filter {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|))
    {ρ : ℝ} (hρ : |ρ| ≤ 1) (h0 : gen a ρ = 0) (t : ℤ) :
    ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc a (shockL2 hbdd) (t - k)) (shockL2 hbdd t) :=
  not_filter_of_aRho_eq_zero (iid_whiteNoise hmean hvar hbdd) hσ.ne' ha hρ h0 t

/-- Cochrane (2023), p. 102 and Online Appendix p. 597, **correction at `ρ = ±1`**, in `L²`: for
`s_t = e_t − ρe_{t−1}` with `ρ² = 1` (so `a(ρ) = 0`), the structural shock is in the closed span of
current and past surpluses (a mean-square limit of linear combinations of them), although no
absolutely summable filter recovers it. -/
theorem iid_unit_root {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {ρ : ℝ} (hρ : ρ ^ 2 = 1) (t : ℤ) :
    gen (armaCoeff 0 ρ) ρ = 0 ∧
    shockL2 hbdd t ∈ pastSpan (maProc (armaCoeff 0 ρ) (shockL2 hbdd)) t ∧
    ¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc (armaCoeff 0 ρ) (shockL2 hbdd) (t - k))
        (shockL2 hbdd t) := by
  have he := iid_whiteNoise hmean hvar hbdd
  have hρ1 : |ρ| ≤ 1 := by
    have : |ρ| ^ 2 = 1 := by rw [sq_abs, hρ]
    nlinarith [abs_nonneg ρ]
  obtain ⟨h0, hmem⟩ := mem_pastSpan_unit_root he hρ t
  exact ⟨h0, hmem, not_filter_of_aRho_eq_zero he hσ.ne' (summable_abs_armaCoeff (by simp) ρ)
    hρ1 h0 t⟩

/-- Cochrane (2023), Online Appendix pp. 597 and 600, in `L²`: the factorised Wold statement
(`InvertibilityMeasure.wold_factor`) for i.i.d. shocks — the autoregression's error `w` has
variance `θ²σ²`, the fitted moving average has the flipped root and `ã(θ⁻¹) ≠ 0`, and
`w_t ≠ e_t`. -/
theorem iid_wold_factor {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ}
    (hg : Summable (fun k => |g k|)) (hg0 : g 0 = 1) (hrec : Recoverable g) (t : ℤ) :
    ⟪woldInnov θ (maOne θ (shockL2 hbdd)) t, woldInnov θ (maOne θ (shockL2 hbdd)) t⟫ =
      θ ^ 2 * σ2 ∧
    HasSum (fun n : ℕ => factorCoeff θ⁻¹ g n • woldInnov θ (maOne θ (shockL2 hbdd)) (t - n))
      (maProc (factorCoeff θ g) (shockL2 hbdd) t) ∧
    gen (factorCoeff θ g) θ⁻¹ = 0 ∧ gen (factorCoeff θ⁻¹ g) θ⁻¹ ≠ 0 ∧
    shockL2 hbdd t ∉ pastSpan (maProc (factorCoeff θ g) (shockL2 hbdd)) t ∧
    woldInnov θ (maOne θ (shockL2 hbdd)) t ≠ shockL2 hbdd t := by
  obtain ⟨-, hn, -, hfit, hroot, -, hne, hnot, hw⟩ :=
    wold_factor (iid_whiteNoise hmean hvar hbdd) hσ.ne' hθ hg hg0 hrec t
  exact ⟨hn, hfit, hroot, hne, hnot, hw⟩

/-- Cochrane (2023), Online Appendix eq. (2.21), p. 601 ("debt Granger-causes surpluses"), in the
genuine probability setting, for an ARBITRARY absolutely summable moving average with `a₀ ≠ 0`,
`a(ρ) = 0`, `|ρ| < 1`: the mean-square error of the best linear forecast of `s_{t+1}` from
current and past surpluses and debt is strictly smaller than from surpluses alone. -/
theorem iid_granger_general {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|))
    (ha0 : a 0 ≠ 0) {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0) (t : ℤ) :
    (haveI : (pastSpan (maProc a (shockL2 hbdd)) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
    haveI : (jointSpan (maProc a (shockL2 hbdd))
        (maProc (hsCoeff a ρ) (shockL2 hbdd)) t).HasOrthogonalProjection := by
        unfold jointSpan; infer_instance
      ‖maProc a (shockL2 hbdd) (t + 1) - Submodule.starProjection
        (jointSpan (maProc a (shockL2 hbdd)) (maProc (hsCoeff a ρ) (shockL2 hbdd)) t)
        (maProc a (shockL2 hbdd) (t + 1))‖ <
      ‖maProc a (shockL2 hbdd) (t + 1) - Submodule.starProjection
        (pastSpan (maProc a (shockL2 hbdd)) t) (maProc a (shockL2 hbdd) (t + 1))‖) :=
  (granger_general (iid_whiteNoise hmean hvar hbdd) hσ.ne' ha ha0 hρ h0 t).2

/-- Cochrane (2023), Online Appendix eqs. (2.20)–(2.21), p. 601, in `L²`: for
`a(L) = (1 − θL)g(L)` with `g` invertible, the debt history reveals the shock, the joint forecast
error of `s_{t+1}` is `e_{t+1}` (variance `σ²`) and the surplus-only one has variance
`θ²σ² > σ²`. -/
theorem iid_granger_factor {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {θ : ℝ} (hθ : 1 < |θ|) {g : ℕ → ℝ}
    (hg : Summable (fun k => |g k|)) (hg0 : g 0 = 1) (hrec : Recoverable g) (t : ℤ) :
    shockL2 hbdd t ∈ pastSpan (maProc (hsCoeff (factorCoeff θ g) θ⁻¹) (shockL2 hbdd)) t ∧
    (haveI : (pastSpan (maProc (factorCoeff θ g) (shockL2 hbdd)) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      ‖maProc (factorCoeff θ g) (shockL2 hbdd) (t + 1) - Submodule.starProjection
        (pastSpan (maProc (factorCoeff θ g) (shockL2 hbdd)) t)
        (maProc (factorCoeff θ g) (shockL2 hbdd) (t + 1))‖ ^ 2) = θ ^ 2 * σ2 ∧
    ‖shockL2 hbdd (t + 1)‖ ^ 2 = σ2 ∧ σ2 < θ ^ 2 * σ2 := by
  have he := iid_whiteNoise hmean hvar hbdd
  obtain ⟨-, h2, h3, h4⟩ := granger_factor he hσ.ne' hθ hg hg0 hrec t
  exact ⟨shock_mem_debtSpan he hθ hg hrec t, h2, h3, h4⟩

/-- Cochrane (2023), p. 102 and Online Appendix pp. 597–601, for the fair `±1` coin (`σ² = 1`) on
the non-finitely-supported space `{±1}^ℕ`: (i) the MA(1) `s_t = e_t − e_{t−1}` (`ρ = 1`) has
`a(1) = 0`, its shock is in the closed span of past surpluses but no summable filter recovers it;
(ii) for `|ρ| < 1` the MA(1) `s_t = e_t − ρ⁻¹e_{t−1}` has `a(ρ) = 0` and debt strictly improves the
forecast of surpluses (error variances `1` versus `ρ⁻²`). -/
theorem coin_L2 {ρ : ℝ} (hρ0 : 0 < |ρ|) (hρ : |ρ| < 1) (t : ℤ) :
    (∀ F : Finset (ℕ → ℝ), (iidSystem coin).μ ↑F ≠ 1) ∧
    gen (armaCoeff 0 1) 1 = 0 ∧
    shockL2 coin_bdd t ∈ pastSpan (maProc (armaCoeff 0 1) (shockL2 coin_bdd)) t ∧
    (¬ ∃ b : ℕ → ℝ, Summable (fun k => |b k|) ∧
      HasSum (fun k : ℕ => b k • maProc (armaCoeff 0 1) (shockL2 coin_bdd) (t - k))
        (shockL2 coin_bdd t)) ∧
    ‖shockL2 coin_bdd (t + 1)‖ ^ 2 = 1 ∧
    (haveI : (pastSpan (maProc (factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0))
        (shockL2 coin_bdd)) t).HasOrthogonalProjection := by
        unfold pastSpan; infer_instance
      ‖maProc (factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0)) (shockL2 coin_bdd) (t + 1) -
        Submodule.starProjection (pastSpan (maProc (factorCoeff ρ⁻¹
          (fun k => if k = 0 then 1 else 0)) (shockL2 coin_bdd)) t)
        (maProc (factorCoeff ρ⁻¹ (fun k => if k = 0 then 1 else 0)) (shockL2 coin_bdd)
          (t + 1))‖ ^ 2) = (ρ⁻¹) ^ 2 * 1 ∧
    (1 : ℝ) < (ρ⁻¹) ^ 2 * 1 := by
  have hθ : 1 < |ρ⁻¹| := by rw [abs_inv]; exact one_lt_inv_iff₀.mpr ⟨hρ0, hρ⟩
  have hδ : Summable (fun k : ℕ => |(if k = 0 then (1 : ℝ) else 0)|) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by simp_all
  have hrec := recoverable_delta
  obtain ⟨h1, h2, h3⟩ := iid_unit_root coin_mean coin_var one_pos coin_bdd (ρ := 1) (by norm_num) t
  obtain ⟨-, h5, h6, h7⟩ := iid_granger_factor coin_mean coin_var one_pos coin_bdd hθ hδ
    (by simp) hrec t
  exact ⟨iid_not_finitely_supported coin_mean coin_var one_pos, h1, h2, h3, h6, h5, h7⟩

/-- Cochrane (2023), p. 102 and Online Appendix p. 597, for `|ρ| < 1` in `L²` (the existing
`Invertibility.Hilbert.not_mem_pastSpan_of_aRho_eq_zero`, instantiated): with `a(ρ) = 0` the
shock is not in the closed span of current and past surpluses. -/
theorem iid_not_mem_pastSpan {σ2 B : ℝ} (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hσ : 0 < σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {a : ℕ → ℝ} (ha : Summable (fun k => |a k|))
    {ρ : ℝ} (hρ : |ρ| < 1) (h0 : gen a ρ = 0) (t : ℤ) :
    shockL2 hbdd t ∉ pastSpan (maProc a (shockL2 hbdd)) t :=
  not_mem_pastSpan_of_aRho_eq_zero (iid_whiteNoise hmean hvar hbdd) hσ.ne' ha hρ h0 t

/-- Cochrane (2023), p. 102 and Online Appendix p. 597 ("`ρ ≤ 1`"), **counterexample**: the
closed-span non-invertibility statement is false when extended to `|ρ| ≤ 1` — in `L²` of the
fair-coin product, the MA(1) `1 − L` has `a(1) = 0` but its shock is in the closed span of the
surplus history. -/
theorem closedSpan_fails_at_unit_root (t : ℤ) :
    ¬ ∀ a : ℕ → ℝ, Summable (fun k => |a k|) → ∀ ρ : ℝ, |ρ| ≤ 1 → gen a ρ = 0 →
      shockL2 coin_bdd t ∉ pastSpan (maProc a (shockL2 coin_bdd)) t := by
  intro h
  obtain ⟨h0, hmem, -⟩ := iid_unit_root coin_mean coin_var one_pos coin_bdd (ρ := 1)
    (by norm_num) t
  exact h _ (summable_abs_armaCoeff (by simp) 1) 1 (by simp) h0 hmem

end Cochrane.DebtDeficitsInflation.InvertibilityMeasureL2
