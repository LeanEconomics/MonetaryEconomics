/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.SurplusProcessFacts
import DebtDeficitsInflation.PermanentTransitory
import DebtDeficitsInflation.ConditioningDown

/-!
# Links between the innovation-accounting and the VAR/invertibility modules

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 4, §4.2–4.3, pp. 87–112, and
Online Appendix Chapter 2, §§2.1–2.4, pp. 594–611.

The Hansen–Roberds–Sargent identity `Δπ_{t+1} = −a(ρ)ε_{t+1}` (`SurplusMA.innov_infl_eq`, for
moving averages in `ℤ`-indexed shocks) is applied to the surplus processes of the Online
Appendix (ARMA(1,1), MA(1), permanent–transitory), which are written in `ℕ`-indexed
martingale-difference shocks and in "revision form" `Δ_{t+1}s_{t+1+j} = a_j ε_{t+1}`.

## Main results

* Variant definitions: `armaCoeff_zero_eq_ma1Coeff` (`Invertibility.armaCoeff 0 θ` is
  `SurplusMA.ma1Coeff θ`), `armaCoeff_ar1`, `gen_armaCoeff_ar1`; `isMDSNat_iff_shockMDS` (the
  VAR shock condition `ShockMDS` plus adaptedness is `IsMDSNat` componentwise).
* `presample`, `isMDS_presample`, `maSeries_isMA`: the zero-presample moving average
  `Invertibility.maSeries` is an `Innovations.IsMA`; `innov_PV_maSeries` ((4.2) for it) and
  `hansenSargent_innov` (the Hansen–Sargent forecasts (2.19) revise by `a(ρ)ε_{t+1}`).
* `innov_infl_of_revision`: the HRS identity for any surplus in revision form;
  `arma11_innov_infl` (`Δπ = −β_sε`, A2 (2.3)), `ma1_revision`, `ma1_innov_infl`,
  `ma1_innov_infl_repay` (p. 102), `pt_innov_infl` (A2 p. 608, `Δπ = −β_sε_s`, the link the
  permanent–transitory module's `pt_inflation_eq` relies on), `pt_pv_revision_via_ar1`.
* `condDown_flow`: with the flow identity (3.17) holding ex post, the present value computed with
  any information set converges to `E^I_t v_t`, hence to `v_t` iff `v_t ∈ I_t` (p. 101, matching
  `ConditioningDown.condDown_iff`).
-/

namespace Cochrane.DebtDeficitsInflation.Links

open Filter Topology
open Cochrane.DebtDeficitsInflation.Innovations
open Cochrane.DebtDeficitsInflation.LinearizedIdentities
open Cochrane.DebtDeficitsInflation.SurplusMA (SimpleModel InnovTVC ma1Coeff)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Variant definitions of the same objects -/

/-- Cochrane (2023), p. 88, and Online Appendix eq. (2.3), p. 595: the MA(1) coefficients
`1 − θL` of the ARMA family `(1 − θL)/(1 − φL)` at `φ = 0` are the MA(1) coefficients of
§4.2. -/
theorem armaCoeff_zero_eq_ma1Coeff (θ : ℝ) : Invertibility.armaCoeff 0 θ = ma1Coeff θ := by
  funext j
  rcases j with _ | _ | j <;> simp [Invertibility.armaCoeff, ma1Coeff]

/-- Cochrane (2023), eq. (4.3), p. 88, and Online Appendix eq. (2.3), p. 595: at `θ = 0` the
ARMA coefficients are those of the AR(1), `aⱼ = φʲ`. -/
theorem armaCoeff_ar1 (φ : ℝ) : Invertibility.armaCoeff φ 0 = fun j => φ ^ j := by
  funext j
  rcases j with _ | j <;> simp [Invertibility.armaCoeff, pow_succ']

/-- Cochrane (2023), eq. (4.3), p. 88, and Online Appendix eq. (2.3), p. 595: the two closed
forms of the AR(1) generating function agree, `a(z) = 1/(1 − zφ) = (1 − 0·z)/(1 − φz)`. -/
theorem gen_armaCoeff_ar1 {φ z : ℝ} (h : |z * φ| < 1) :
    gen (Invertibility.armaCoeff φ 0) z = 1 / (1 - z * φ) ∧
    gen (Invertibility.armaCoeff φ 0) z = (1 - 0 * z) / (1 - φ * z) := by
  refine ⟨by rw [armaCoeff_ar1, SurplusMA.gen_ar1 h], ?_⟩
  exact Invertibility.genFn_armaCoeff (by rwa [mul_comm])

/-- Cochrane (2023), p. 88, and Online Appendix p. 600: the two MA(1) generating functions agree,
`a(ρ) = 1 − θρ`. -/
theorem gen_armaCoeff_zero (θ ρ : ℝ) :
    gen (Invertibility.armaCoeff 0 θ) ρ = gen (ma1Coeff θ) ρ ∧
    gen (Invertibility.armaCoeff 0 θ) ρ = 1 - θ * ρ :=
  ⟨by rw [armaCoeff_zero_eq_ma1Coeff], by rw [armaCoeff_zero_eq_ma1Coeff, SurplusMA.gen_ma1]⟩

/-- Cochrane (2023), eq. (4.17), p. 104, and eq. (4.1), p. 87: the VAR shocks are martingale
differences in every coordinate (`IsMDSNat`) iff they are unforecastable (`ShockMDS`) and
adapted. -/
theorem isMDSNat_iff_shockMDS {κ : Type*} (ε : ℕ → κ → Ω → ℝ) :
    (∀ i, IsMDSNat 𝔼 (fun t => ε t i)) ↔
      VARIdentities.ShockMDS 𝔼 ε ∧ ∀ t i, 𝔼.E t (ε t i) = ε t i :=
  ⟨fun h => ⟨fun t i => (h i).2 t, fun t i => (h i).1 t⟩,
    fun h i => ⟨fun t => h.2 t i, fun t => h.1 t i⟩⟩

/-! ### The zero-presample moving average and the Hansen–Sargent formula -/

/-- Cochrane (2023), eq. (4.1), p. 87, and Online Appendix p. 600: an `ℕ`-indexed shock
`e_0, e_1, …` placed on the integers, with zero shocks before date `0`. -/
def presample (e : ℕ → Ω → ℝ) (k : ℤ) : Ω → ℝ := if 0 ≤ k then e k.toNat else 0

/-- Cochrane (2023), eq. (4.1), p. 87: `presample e (t + 1) = e (t + 1)`. -/
theorem presample_succ (e : ℕ → Ω → ℝ) (t : ℕ) : presample e ((t : ℤ) + 1) = e (t + 1) := by
  have h0 : (0 : ℤ) ≤ (t : ℤ) + 1 := by omega
  have h1 : ((t : ℤ) + 1).toNat = t + 1 := by omega
  simp only [presample, h0, ↓reduceIte, h1]

/-- Cochrane (2023), eq. (4.1), p. 87: an `ℕ`-indexed martingale difference, extended by zero to
the past, is a martingale difference on `ℤ`. -/
theorem isMDS_presample {e : ℕ → Ω → ℝ} (h : IsMDSNat 𝔼 e) : IsMDS 𝔼 (presample e) := by
  refine ⟨fun t k hk => ?_, fun t => ?_⟩
  · by_cases h0 : (0 : ℤ) ≤ k
    · simp only [presample, h0, ↓reduceIte]
      exact h.E_past (by omega)
    · simp only [presample, h0, ↓reduceIte, map_zero]
  · rw [presample_succ]
    exact h.2 t

/-- Cochrane (2023), eq. (4.1), p. 87: the presample shock inherits a bound. -/
theorem abs_presample_le {e : ℕ → Ω → ℝ} {M : ℝ} (hM : ∀ t ω, |e t ω| ≤ M) (k : ℤ) (ω : Ω) :
    |presample e k ω| ≤ M := by
  by_cases h0 : (0 : ℤ) ≤ k
  · simp only [presample, h0, ↓reduceIte]
    exact hM _ ω
  · simp only [presample, h0, ↓reduceIte, Pi.zero_apply, abs_zero]
    exact (abs_nonneg _).trans (hM 0 ω)

/-- Cochrane (2023), eq. (4.1), p. 87, and Online Appendix p. 600: the zero-presample moving
average `s_t = ∑_{j ≤ t} aⱼ e_{t−j}` of the Invertibility module is a moving average (4.1) in the
`ℤ`-indexed shock `presample e`. -/
theorem maSeries_isMA {a : ℕ → ℝ} (ha : Summable fun j => |a j|) (e : ℕ → Ω → ℝ) :
    IsMA a (presample e) (Invertibility.maSeries a e) := by
  refine ⟨ha, fun t ω => ?_⟩
  have hz : ∀ j ∉ Finset.range (t + 1), a j * presample e ((t : ℤ) - j) ω = 0 := by
    intro j hj
    have hj' : t < j := by simpa using hj
    have h0 : ¬ (0 : ℤ) ≤ (t : ℤ) - j := by omega
    simp only [presample, h0, ↓reduceIte, Pi.zero_apply, mul_zero]
  rw [tsum_eq_sum hz]
  simp only [Invertibility.maSeries, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have h0 : (0 : ℤ) ≤ (t : ℤ) - j := by omega
  have h1 : ((t : ℤ) - j).toNat = t - j := by omega
  simp only [presample, h0, ↓reduceIte, h1]

/-- Cochrane (2023), eq. (4.2), p. 87, for the zero-presample moving average of the Online
Appendix: `∑ ρʲ Δ_{t+1} s_{t+1+j} = a(ρ) e_{t+1}` (`|ρ| ≤ 1`, bounded shocks). -/
theorem innov_PV_maSeries {e : ℕ → Ω → ℝ} (he : IsMDSNat 𝔼 e) {M : ℝ}
    (hM : ∀ t ω, |e t ω| ≤ M) {a : ℕ → ℝ} (ha : Summable fun j => |a j|) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (Invertibility.maSeries a e (t + 1 + j)) ω)
      (gen a ρ * e (t + 1) ω) := by
  have h := innov_PV_termwise 𝔼 (maSeries_isMA ha e) (isMDS_presample 𝔼 he)
    (abs_presample_le hM) hρ t ω
  rwa [presample_succ] at h

/-- Cochrane (2023), Online Appendix eq. (2.19), p. 601, and eq. (4.2), p. 87: the Hansen–Sargent
forecasts revise by `a(ρ)` times the shock. With `HS_t = ∑_{k ≤ t} c_k e_{t−k}` the forecast
`E_t ∑ ρⁱ s_{t+1+i}`, `s_{t+1} + ρ HS_{t+1} − HS_t = a(ρ) e_{t+1}`. -/
theorem hansenSargent_innov {e : ℕ → Ω → ℝ} (he : IsMDSNat 𝔼 e) {M : ℝ}
    (hM : ∀ t ω, |e t ω| ≤ M) {a : ℕ → ℝ} (ha : Summable fun j => |a j|) {ρ : ℝ}
    (hρ : |ρ| ≤ 1) (t : ℕ) (ω : Ω) :
    Invertibility.maSeries a e (t + 1) ω +
        ρ * ∑ k ∈ Finset.range (t + 1 + 1), Invertibility.hsCoeff a ρ k * e (t + 1 - k) ω -
      ∑ k ∈ Finset.range (t + 1), Invertibility.hsCoeff a ρ k * e (t - k) ω =
      gen a ρ * e (t + 1) ω := by
  set s := Invertibility.maSeries a e with hsdef
  have hk : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
    rw [hsdef, Invertibility.maSeries, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, he.E_past (Nat.sub_le _ _)]
  have h1 := Invertibility.hansenSargent 𝔼 he ha hρ (t + 1) ω
  have h0 := Invertibility.hansenSargent 𝔼 he ha hρ t ω
  have hA : HasSum (fun j => ρ ^ j * 𝔼.E (t + 1) (s (t + 1 + j)) ω)
      (s (t + 1) ω + ρ * ∑ k ∈ Finset.range (t + 1 + 1),
        Invertibility.hsCoeff a ρ k * e (t + 1 - k) ω) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, add_zero, hk,
      add_sub_cancel_left]
    refine (h1.mul_left ρ).congr_fun fun j => ?_
    rw [show t + 1 + (j + 1) = t + 1 + 1 + j by omega, pow_succ]
    ring
  have hI := innov_PV_maSeries 𝔼 he hM ha hρ t ω
  have hD : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
      (s (t + 1) ω + ρ * ∑ k ∈ Finset.range (t + 1 + 1),
        Invertibility.hsCoeff a ρ k * e (t + 1 - k) ω -
        ∑ k ∈ Finset.range (t + 1), Invertibility.hsCoeff a ρ k * e (t - k) ω) := by
    refine (hA.sub h0).congr_fun fun j => ?_
    rw [innov_apply, Pi.sub_apply]
    ring
  exact hD.unique hI

/-! ### The HRS identity applied to the Online-Appendix surplus processes -/

/-- Cochrane (2023), eq. (4.2), p. 87 (Hansen, Roberds and Sargent 1992), for a surplus given in
revision form: in the simple model, if `Δ_{t+1}s_{t+1+j} = aⱼ e` with `∑ aⱼρʲ` convergent, then
`Δ_{t+1}π_{t+1} = −a(ρ) e`. -/
theorem innov_infl_of_revision {ρ c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) {t : ℕ} {ω : Ω}
    (hT : Tendsto (fun T => ρ ^ T * innov 𝔼 t (v (t + T)) ω) atTop (𝓝 0)) {a : ℕ → ℝ}
    {e : Ω → ℝ} (hrev : ∀ j, innov 𝔼 t (s (t + 1 + j)) = a j • e)
    (ha : Summable fun j => a j * ρ ^ j) :
    innov 𝔼 t (infl (t + 1)) ω = -(gen a ρ * e ω) := by
  obtain ⟨hf, hr, hv, hrn, hc⟩ := hm
  have hS : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω) (gen a ρ * e ω) := by
    refine (ha.hasSum.mul_right (e ω)).congr_fun fun j => ?_
    simp only [hrev j, Pi.smul_apply, smul_eq_mul]
    ring
  exact inflation_identity_one_period_const 𝔼 hf hr hc hv (hrn t) hT (seriesTo_of_hasSum hS)

/-- Cochrane (2023), Online Appendix eq. (2.3), p. 595 ("`β_s` controls how much of a shock is
repaid, and how much results in inflation") with eq. (4.2), p. 87: if the surplus follows the
ARMA(1,1) of (2.1)–(2.3), `s_{t+1} = αv_t + ε_{t+1}`, `ρv_{t+1} = v_t + β_sε_{t+1} − s_{t+1}`
(`0 < α < 2`), then in the simple model unexpected inflation is `Δπ_{t+1} = −β_s ε_{t+1}`. -/
theorem arma11_innov_infl {ρ c α βs : ℝ} {v' r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v' r rn infl s) (hT : InnovTVC 𝔼 ρ v') (hρ : ρ ≠ 0) (hα0 : 0 < α)
    (hα2 : α < 2) {v ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε) (hvad : 𝔼.Adapted v)
    (hs : ∀ t, s (t + 1) = α • v t + ε (t + 1))
    (hv : ∀ t, ρ • v (t + 1) = v t + βs • ε (t + 1) - s (t + 1)) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -βs • ε (t + 1) := by
  funext ω
  have h : |(1 - α) / ρ * ρ| < 1 := by
    rw [div_mul_cancel₀ _ hρ, abs_lt]; constructor <;> linarith
  rw [innov_infl_of_revision 𝔼 hm (hT t ω)
    (fun j => Invertibility.arma11_revision 𝔼 hρ hmds hvad hs hv t j)
    (Invertibility.armaCoeff_hasSum (θ := (1 - α * βs) / ρ) h).summable,
    Invertibility.arma11_aRho_params hρ hα0 hα2]
  simp

/-- Cochrane (2023), p. 102, and Online Appendix eq. (2.9), p. 598: the MA(1)
`s_{t+1} = ε_{t+1} + cε_t` in revision form, `Δ_{t+1}s_{t+1+j} = aⱼε_{t+1}` with the MA(1)
coefficients `1, c, 0, 0, …` (`armaCoeff 0 (−c)`). -/
theorem ma1_revision {c : ℝ} {s ε : ℕ → Ω → ℝ} (hmds : IsMDSNat 𝔼 ε)
    (hs : ∀ t, s (t + 1) = ε (t + 1) + c • ε t) (t j : ℕ) :
    innov 𝔼 t (s (t + 1 + j)) = Invertibility.armaCoeff 0 (-c) j • ε (t + 1) := by
  obtain ⟨h0, h0'⟩ := Invertibility.ma1_forecasts 𝔼 hmds hs t
  obtain ⟨h1, h1'⟩ := Invertibility.ma1_forecasts 𝔼 hmds hs (t + 1)
  rcases j with _ | _ | k
  · have hk : 𝔼.E (t + 1) (s (t + 1)) = s (t + 1) := by
      rw [hs t, map_add, map_smul, hmds.1 (t + 1), hmds.E_past (Nat.le_succ t)]
    rw [add_zero, innov_apply, hk, h0, hs t]
    simp [Invertibility.armaCoeff]
  · have h2 := h0' 0
    rw [add_zero] at h2
    rw [show t + 1 + (0 + 1) = t + 2 by omega, innov_apply, h2, show t + 2 = t + 1 + 1 by omega,
      h1]
    simp [Invertibility.armaCoeff]
  · have h2 := h0' (k + 1)
    have h3 := h1' k
    rw [show t + 1 + (k + 1 + 1) = t + 1 + 2 + k by omega, innov_apply, h3,
      show t + 1 + 2 + k = t + 2 + (k + 1) by omega, h2]
    simp [Invertibility.armaCoeff]

/-- Cochrane (2023), p. 102, and Online Appendix eqs. (2.9)–(2.13), pp. 598–599, with eq. (4.2),
p. 87: for the MA(1) `s_{t+1} = ε_{t+1} + cε_t`, unexpected inflation in the simple model is
`Δπ_{t+1} = −(1 + cρ)ε_{t+1} = −a(ρ)ε_{t+1}`. -/
theorem ma1_innov_infl {ρ c0 c : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c0 v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + c • ε t) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -(1 + c * ρ) • ε (t + 1) := by
  funext ω
  have h : |(0 : ℝ) * ρ| < 1 := by simp
  rw [innov_infl_of_revision 𝔼 hm (hT t ω) (ma1_revision 𝔼 hmds hs t)
    (Invertibility.armaCoeff_hasSum (θ := -c) h).summable, Invertibility.ma1_aRho]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), p. 102 ("`θ = ρ⁻¹` ... the government repays its debts"): for the MA(1)
`s_{t+1} = ε_{t+1} − ρ⁻¹ε_t`, `a(ρ) = 0` and there is no unexpected inflation. -/
theorem ma1_innov_infl_repay {ρ c0 : ℝ} (hρ : ρ ≠ 0) {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c0 v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {ε : ℕ → Ω → ℝ}
    (hmds : IsMDSNat 𝔼 ε) (hs : ∀ t, s (t + 1) = ε (t + 1) + (-ρ⁻¹) • ε t) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = 0 := by
  rw [ma1_innov_infl 𝔼 hm hT hmds hs t, neg_mul, inv_mul_cancel₀ hρ, add_neg_cancel, neg_zero,
    zero_smul]

/-- Cochrane (2023), Online Appendix eq. (2.30), p. 608, from the AR(1) news formula of §4.2.6
(`SurplusProcessFacts.ar1_innov_sum`): `∑ρʲΔ(z + x)_{t+1+j} = Δz_{t+1}/(1 − ρη_z) +
Δx_{t+1}/(1 − ρη_x)`, with `Δz_{t+1} = ε_{z,t+1}` and `Δx_{t+1} = ε_{x,t+1}` (so this is
`PermanentTransitory.pt_pv_revision`). -/
theorem pt_pv_revision_via_ar1 {ρ ηz ηx : ℝ} {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1) (t : ℕ) (ω : Ω) :
    HasSum (fun j => ρ ^ j * innov 𝔼 t (z (t + 1 + j) + x (t + 1 + j)) ω)
      (innov 𝔼 t (z (t + 1)) ω / (1 - ρ * ηz) + innov 𝔼 t (x (t + 1)) ω / (1 - ρ * ηx)) ∧
    innov 𝔼 t (z (t + 1)) = εz (t + 1) ∧ innov 𝔼 t (x (t + 1)) = εx (t + 1) := by
  have hzA := PermanentTransitory.isAR1_of_shocks 𝔼 hεz hzad hz
  have hxA := PermanentTransitory.isAR1_of_shocks 𝔼 hεx hxad hx
  refine ⟨?_, ?_, ?_⟩
  · refine ((SurplusProcessFacts.ar1_innov_sum 𝔼 hρz hzA t ω).add
      (SurplusProcessFacts.ar1_innov_sum 𝔼 hρx hxA t ω)).congr_fun fun j => ?_
    rw [map_add, Pi.add_apply]
    ring
  · rw [innov_apply, hzad (t + 1), hzA.2 t, hz t]
    abel
  · rw [innov_apply, hxad (t + 1), hxA.2 t, hx t]
    abel

/-- Cochrane (2023), Online Appendix p. 608 ("the inflation innovation is
`ΔE_{t+1}π_{t+1} = −β_sε_{s,t+1}`"): in the simple model with the permanent–transitory surplus
`s = z + x` and the policy response (2.31), `ε_z = −kε_x`, unexpected inflation is
`Δπ_{t+1} = −β_s(ε_{z,t+1} + ε_{x,t+1})`. This is the HRS identity (4.2) applied to the
present-value revision (2.30), via `PermanentTransitory.pt_inflation_eq`. -/
theorem pt_innov_infl {ρ c ηz ηx βs : ℝ} {v r rn infl s : ℕ → Ω → ℝ}
    (hm : SimpleModel 𝔼 ρ c v r rn infl s) (hT : InnovTVC 𝔼 ρ v) {z x εz εx : ℕ → Ω → ℝ}
    (hεz : IsMDSNat 𝔼 εz) (hεx : IsMDSNat 𝔼 εx) (hzad : 𝔼.Adapted z) (hxad : 𝔼.Adapted x)
    (hz : ∀ t, z (t + 1) = ηz • z t + εz (t + 1)) (hx : ∀ t, x (t + 1) = ηx • x t + εx (t + 1))
    (hsum : ∀ t, s t = z t + x t)
    (hpol : ∀ t, εz t = -PermanentTransitory.kcoef ρ ηx ηz βs • εx t)
    (hρz : |ρ * ηz| < 1) (hρx : |ρ * ηx| < 1) (hD1 : 1 - (1 - ρ * ηz) * βs ≠ 0) (t : ℕ) :
    innov 𝔼 t (infl (t + 1)) = -βs • (εz (t + 1) + εx (t + 1)) := by
  funext ω
  obtain ⟨hf, hr, hv, hrn, hc⟩ := hm
  have hz1 : 1 - ρ * ηz ≠ 0 := by
    intro h0; rw [show ρ * ηz = 1 by linarith, abs_one] at hρz; exact lt_irrefl _ hρz
  have hx1 : 1 - ρ * ηx ≠ 0 := by
    intro h0; rw [show ρ * ηx = 1 by linarith, abs_one] at hρx; exact lt_irrefl _ hρx
  have hS := PermanentTransitory.pt_pv_revision 𝔼 hεz hεx hzad hxad hz hx hρz hρx t ω
  have hS' : HasSum (fun j => ρ ^ j * innov 𝔼 t (s (t + 1 + j)) ω)
      (εz (t + 1) ω / (1 - ρ * ηz) + εx (t + 1) ω / (1 - ρ * ηx)) :=
    hS.congr_fun fun j => by rw [hsum]
  rw [inflation_identity_one_period_const 𝔼 hf hr hc hv (hrn t) (hT t ω)
    (seriesTo_of_hasSum hS')]
  have hp := congrFun (hpol (t + 1)) ω
  simp only [Pi.smul_apply, smul_eq_mul] at hp
  rw [hp, PermanentTransitory.pt_inflation_eq hD1 hz1 hx1]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hp]
  ring

/-! ### Information sets: the flow identity and conditioning down -/

/-- Cochrane (2023), p. 101, and Online Appendix eqs. (2.22)–(2.23), p. 602, with eq. (3.19),
p. 64: because the flow identity (3.17) holds ex post, under people's information `𝔼Ω` (where
`v` is known) the present value of `s̃ + g − r` converges to `v_t`, while under ANY information
system `𝔼I` (with its terminal condition) it converges to `E^I_t v_t` — hence to `v_t` iff
`v_t ∈ I_t` (the conditioning-down condition of `ConditioningDown.condDown_iff`). -/
theorem condDown_flow {𝔼I 𝔼Ω : ExpectationSystem Ω} {ρ : ℝ} {v r g s : ℕ → Ω → ℝ}
    (h : Flow ρ v r g s) (hv : 𝔼Ω.Adapted v) {t : ℕ} {ω : Ω}
    (hTΩ : Tendsto (fun T => ρ ^ T * 𝔼Ω.E t (v (t + T)) ω) atTop (𝓝 0))
    (hTI : Tendsto (fun T => ρ ^ T * 𝔼I.E t (v (t + T)) ω) atTop (𝓝 0)) :
    SeriesTo (fun j => ρ ^ j * 𝔼Ω.E t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω)
      (v t ω) ∧
    SeriesTo (fun j => ρ ^ j * 𝔼I.E t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω)
      (𝔼I.E t (v t) ω) ∧
    (SeriesTo (fun j => ρ ^ j * 𝔼I.E t (s (t + 1 + j) + g (t + 1 + j) - r (t + 1 + j)) ω)
      (v t ω) ↔ 𝔼I.E t (v t) ω = v t ω) := by
  have hI := rec_seriesTo_map (𝔼I.E t) ((flow_iff_recursion ρ v r g s).1 h) hTI
  refine ⟨pv_expected_combined 𝔼Ω h hv hTΩ, hI, ⟨fun h1 => hI.unique h1, fun he => ?_⟩⟩
  rw [← he]
  exact hI

end Cochrane.DebtDeficitsInflation.Links
