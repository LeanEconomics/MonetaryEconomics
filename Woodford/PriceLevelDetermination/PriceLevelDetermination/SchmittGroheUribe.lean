/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.MoneyTargetingDynamics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The example of Schmitt-Grohé and Uribe

Woodford (2003), *Interest and Prices*, Appendix A, §A.17, pp. 653–655 (with Chapter 2, §4.3,
p. 137). Cash/credit preferences `log c₁ + θ log c₂`, a linear Taylor rule truncated at zero,
perfect foresight.

* **Cash purchases.** `c1opt_optimal`: `c₁ = min(m, C/(1+θ))` is optimal.
* **(A.54).** `lambda_A54_binding`, `lambda_A54_satiated`: `λ = u_c + u_m = 1/min(m, C/(1+θ))`.
* **(A.55).** `money_demand_A55`: (A.41) with `i^m = 0` gives `L(Y, i) = Y/(1 + θ(1 + i))`.
* **`λ(i)`.** `lambda_of_i`: `λ(i) = (1 + θ(1 + i))/Ȳ`; `lamSGU_tendsto_atTop` (unbounded);
  `elasticity_lt_one`, `elasticity_tendsto_one` (elasticity below one but not uniformly),
  `elasticity_i_lt_one`.
* **(A.56).** `phiSGU`, `phiSGU_target`, `taylorCoeff_phiSGU` (Taylor coefficient `φ_π`).
* **The functions `A`, `B`.** `eq45_iff_AB` ((4.5) ⇔ `B(Π_{t+1}) = A(Π_t)`), `sguA_antitone`,
  `sguA_tendsto` (limit `θ/Ȳ`; the text omits `1/Ȳ`), `sguB_formula`,
  `sguB_strictAntiOn` and `sguB_gt` under `β + θΠ*(1 − φ_π) > 0` (error E5),
  `sguPibar_spec` and `sgu_no_successor` (the bound `Π̄`).
* **Exclusion of hyperinflation (E5 hypothesis added).** `sgu_no_hyperinflation`: every
  perfect-foresight path has `Π_t ≤ Π*`.
* **Exclusion of deflation.** `sgu_deflation_tendsto` and `sgu_unique_pf_equilibrium`: with
  liabilities growing at `1 < μ̄ < Π*/β`, `Π_t ≡ Π*` is the unique perfect-foresight
  equilibrium.
* **Error E5.** `e5_counterexample`: with `β = 1/2, θ = 1, φ_π = 3/2, Π* = 3, Ȳ = 1` (so
  `β + θΠ*(1 − φ_π) = −1 < 0`) the printed bound `Π̄ = 5/3` lies below `Π*`, the claim "no
  `Π_{t+1}` solves (4.5) once `Π_t ≥ Π̄`" fails, and there is a second perfect-foresight
  equilibrium (satisfying (4.5), (4.4) and the transversality condition) starting at
  `Π₀ = 4 > Π*`: uniqueness and "`Π_t ≤ Π*` at all times" both fail.
-/

namespace Woodford.PriceLevelDetermination.SchmittGroheUribe

open Filter Topology
open Woodford.PriceLevelDetermination.GlobalDynamics
open Woodford.PriceLevelDetermination.MoneyTargetingDynamics

/-! ## Preferences, (A.54) and (A.55) -/

/-- Woodford (2003), p. 654: the optimal cash-goods purchases `c₁ = min(m, C/(1 + θ))`. -/
noncomputable def c1opt (θ C m : ℝ) : ℝ := min m (C / (1 + θ))

/-- Woodford (2003), (A.53), p. 654: the indirect utility
`u(C, m) = log c₁ + θ log(C − c₁)` at the optimal `c₁`. -/
noncomputable def uSGU (θ C m : ℝ) : ℝ :=
  Real.log (c1opt θ C m) + θ * Real.log (C - c1opt θ C m)

/-- Woodford (2003), (A.53), p. 654, "the optimal level of cash goods purchases is equal to
`c₁ = min(m, C/(1 + θ))`": for `θ, C, m > 0`, every feasible `c₁ ∈ (0, m]` with `c₁ < C` gives
`log c₁ + θ log(C − c₁) ≤ u(C, m)`. -/
theorem c1opt_optimal {θ C m c1 : ℝ} (hθ : 0 < θ) (hC : 0 < C) (hm : 0 < m) (h0 : 0 < c1)
    (hc1m : c1 ≤ m) (hc1C : c1 < C) :
    Real.log c1 + θ * Real.log (C - c1) ≤ uSGU θ C m := by
  unfold uSGU
  set cs := c1opt θ C m with hcs
  have hθ1 : 0 < 1 + θ := by linarith
  have hcsle : cs ≤ C / (1 + θ) := min_le_right _ _
  have hcspos : 0 < cs := lt_min hm (div_pos hC hθ1)
  have hCcs : 0 < C - cs := by
    have : C / (1 + θ) < C := by rw [div_lt_iff₀ hθ1]; nlinarith
    linarith
  have h1 : Real.log c1 - Real.log cs ≤ c1 / cs - 1 := by
    rw [← Real.log_div h0.ne' hcspos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos h0 hcspos)
  have h2 : Real.log (C - c1) - Real.log (C - cs) ≤ (C - c1) / (C - cs) - 1 := by
    rw [← Real.log_div (by linarith) hCcs.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hCcs)
  have hkey : (c1 / cs - 1) + θ * ((C - c1) / (C - cs) - 1) ≤ 0 := by
    have e : (c1 / cs - 1) + θ * ((C - c1) / (C - cs) - 1) =
        (c1 - cs) * ((C - cs) - θ * cs) / (cs * (C - cs)) := by
      field_simp
      ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rcases le_total m (C / (1 + θ)) with hle | hle
    · have hcsm : cs = m := min_eq_left hle
      have hA : c1 - cs ≤ 0 := by rw [hcsm]; linarith
      have hB : 0 ≤ (C - cs) - θ * cs := by
        rw [hcsm]
        rw [le_div_iff₀ hθ1] at hle
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg hA hB
    · have hcsC : cs = C / (1 + θ) := min_eq_right hle
      have hB : (C - cs) - θ * cs = 0 := by rw [hcsC]; field_simp; ring
      rw [hB, mul_zero]
  nlinarith

/-- Woodford (2003), (A.54), p. 654, region where the cash constraint binds
(`m < C/(1 + θ)`): `u_C = θ/(C − m)`, `u_m = 1/m − θ/(C − m)`, so
`λ = u_C + u_m = 1/m = 1/min(m, C/(1 + θ))`. -/
theorem lambda_A54_binding {θ C m : ℝ} (hθ : 0 < θ) (hm : 0 < m) (hmC : m < C / (1 + θ)) :
    HasDerivAt (fun C' => uSGU θ C' m) (θ / (C - m)) C ∧
      HasDerivAt (fun m' => uSGU θ C m') (1 / m - θ / (C - m)) m ∧
      θ / (C - m) + (1 / m - θ / (C - m)) = 1 / c1opt θ C m := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hmC' : m * (1 + θ) < C := by rwa [lt_div_iff₀ hθ1] at hmC
  have hCm : 0 < C - m := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · have h := ((hasDerivAt_id C).sub_const m).log hCm.ne'
    have h2 := (h.const_mul θ).const_add (Real.log m)
    simp only [id, one_div] at h2
    refine (h2.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hmC'] with C' hC'
    have : m ≤ C' / (1 + θ) := by rw [le_div_iff₀ hθ1]; exact (Set.mem_Ioi.mp hC').le
    simp only [uSGU, c1opt, min_eq_left this]
  · have h1 := (hasDerivAt_id m).log hm.ne'
    have h2 := (((hasDerivAt_id m).const_sub C).log hCm.ne').const_mul θ
    have h3 := h1.add h2
    simp only [id] at h3
    refine (h3.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hmC] with m' hm'
    simp only [uSGU, c1opt, min_eq_left (Set.mem_Iio.mp hm').le]
    rfl
  · simp only [c1opt, min_eq_left hmC.le]
    field_simp
    ring

/-- Woodford (2003), (A.54), p. 654, region beyond satiation (`m > C/(1 + θ)`):
`u_C = (1 + θ)/C`, `u_m = 0`, so `λ = (1 + θ)/C = 1/min(m, C/(1 + θ))`. -/
theorem lambda_A54_satiated {θ C m : ℝ} (hθ : 0 < θ) (hC : 0 < C) (hmC : C / (1 + θ) < m) :
    HasDerivAt (fun C' => uSGU θ C' m) ((1 + θ) / C) C ∧
      HasDerivAt (fun m' => uSGU θ C m') 0 m ∧ (1 + θ) / C + 0 = 1 / c1opt θ C m := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hmC' : C < m * (1 + θ) := by rwa [div_lt_iff₀ hθ1] at hmC
  refine ⟨?_, ?_, ?_⟩
  · have ha : HasDerivAt (fun C' : ℝ => C' / (1 + θ)) (1 / (1 + θ)) C := by
      simpa using (hasDerivAt_id C).div_const (1 + θ)
    have hb : HasDerivAt (fun C' : ℝ => C' - C' / (1 + θ)) (1 - 1 / (1 + θ)) C :=
      (hasDerivAt_id C).sub ha
    have hpos1 : C / (1 + θ) ≠ 0 := (div_pos hC hθ1).ne'
    have hpos2 : C - C / (1 + θ) ≠ 0 := by
      have : C / (1 + θ) < C := by rw [div_lt_iff₀ hθ1]; nlinarith
      linarith
    have h := (ha.log hpos1).add ((hb.log hpos2).const_mul θ)
    have hθ0 : θ ≠ 0 := hθ.ne'
    have hC0 : C ≠ 0 := hC.ne'
    have e1 : (1 : ℝ) - 1 / (1 + θ) = θ / (1 + θ) := by field_simp; ring
    have e2 : C - C / (1 + θ) = C * θ / (1 + θ) := by field_simp; ring
    refine (h.congr_deriv (by rw [e1, e2]; field_simp)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hmC'] with C' hC'
    have : C' / (1 + θ) ≤ m := by rw [div_le_iff₀ hθ1]; exact (Set.mem_Iio.mp hC').le
    simp only [uSGU, c1opt, min_eq_right this]
    rfl
  · refine (hasDerivAt_const m (uSGU θ C m)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hmC] with m' hm'
    simp only [uSGU, c1opt, min_eq_right (Set.mem_Ioi.mp hm').le, min_eq_right hmC.le]
  · simp only [c1opt, min_eq_right hmC.le]
    field_simp
    ring

/-- Woodford (2003), (A.55), p. 654: the liquidity-preference function
`L(Y, i) = Y/(1 + θ(1 + i))`. -/
noncomputable def LSGU (θ Y i : ℝ) : ℝ := Y / (1 + θ * (1 + i))

/-- Woodford (2003), (A.41) ⇒ (A.55), p. 654: with `i^m = 0`, (A.41) reads `u_m/u_C = i`
(`Timing.oddsRatio_oppCost_zero`). For `i > 0` the real balances `m = L(Y, i)` lie in the region
where the cash constraint binds, and there `u_m/u_C = i` holds iff `m = Y/(1 + θ(1 + i))`. -/
theorem money_demand_A55 {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 < i) :
    0 < LSGU θ Y i ∧ LSGU θ Y i < Y / (1 + θ) ∧
      ∀ m, 0 < m → m < Y / (1 + θ) →
        ((1 / m - θ / (Y - m)) / (θ / (Y - m)) = i ↔ m = LSGU θ Y i) := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  refine ⟨div_pos hY hd, ?_, fun m hm hmY => ?_⟩
  · unfold LSGU
    exact div_lt_div_of_pos_left hY hθ1 (by nlinarith)
  · have hmY' : m * (1 + θ) < Y := by rwa [lt_div_iff₀ hθ1] at hmY
    have hYm : 0 < Y - m := by nlinarith
    have e : (1 / m - θ / (Y - m)) / (θ / (Y - m)) = (Y - m) / (θ * m) - 1 := by
      field_simp
    rw [e, LSGU, eq_div_iff hd.ne', sub_eq_iff_eq_add, div_eq_iff (by positivity)]
    constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 654: `λ(i) = (1 + θ(1 + i))/Ȳ`. -/
noncomputable def lamSGU (θ Y i : ℝ) : ℝ := (1 + θ * (1 + i)) / Y

/-- Woodford (2003), p. 654, "substituting (A.55) into (A.54) … `λ(i) = (1 + θ(1 + i))/Ȳ` for all
`i ≥ 0`". -/
theorem lambda_of_i {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    1 / c1opt θ Y (LSGU θ Y i) = lamSGU θ Y i := by
  have hθ1 : 0 < 1 + θ := by linarith
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  have hle : LSGU θ Y i ≤ Y / (1 + θ) := by
    unfold LSGU
    exact div_le_div_of_nonneg_left hY.le hθ1 (by nlinarith)
  rw [c1opt, min_eq_left hle, LSGU, lamSGU]
  field_simp

/-- Woodford (2003), p. 654, "it can be made unboundedly large in the case of a high enough
interest rate". -/
theorem lamSGU_tendsto_atTop {θ Y : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    Tendsto (lamSGU θ Y) atTop atTop := by
  unfold lamSGU
  refine Tendsto.atTop_div_const hY ?_
  exact tendsto_atTop_add_const_left _ 1
    (Tendsto.const_mul_atTop hθ (tendsto_atTop_add_const_left _ 1 tendsto_id))

/-- Woodford (2003), p. 654: the elasticity of `λ(i)` with respect to `1 + i`,
`(1 + i)λ'(i)/λ(i)` with `λ' = θ/Ȳ`. -/
noncomputable def elasticity (θ Y i : ℝ) : ℝ := (1 + i) * (θ / Y) / lamSGU θ Y i

/-- Woodford (2003), p. 654: `λ'(i) = θ/Ȳ`. -/
theorem hasDerivAt_lamSGU (θ Y i : ℝ) : HasDerivAt (lamSGU θ Y) (θ / Y) i := by
  have h := (((hasDerivAt_id i).const_add 1).const_mul θ).const_add 1
  exact (h.div_const Y).congr_deriv (by ring)

/-- Woodford (2003), p. 654 ("the elasticity of `λ(i)` with respect to `i` remains bounded below
1") and p. 137 (elasticity with respect to `1 + i` "positive, but bounded below one"): for
`i ≥ 0` the elasticity equals `θ(1 + i)/(1 + θ(1 + i)) ∈ (0, 1)`. -/
theorem elasticity_lt_one {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    elasticity θ Y i = θ * (1 + i) / (1 + θ * (1 + i)) ∧ 0 < elasticity θ Y i ∧
      elasticity θ Y i < 1 := by
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  have e : elasticity θ Y i = θ * (1 + i) / (1 + θ * (1 + i)) := by
    unfold elasticity lamSGU
    field_simp
  refine ⟨e, ?_, ?_⟩
  · rw [e]; have : 0 < 1 + i := by linarith
    positivity
  · rw [e, div_lt_one hd]; linarith

/-- Woodford (2003), p. 654, precision: the elasticity tends to `1` as `i → ∞`, so it is below one
at every `i` but admits no uniform bound `k < 1`. -/
theorem elasticity_tendsto_one {θ Y : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    Tendsto (elasticity θ Y) atTop (𝓝 1) := by
  have h1 : Tendsto (fun i : ℝ => θ * (1 + i)) atTop atTop :=
    Tendsto.const_mul_atTop hθ (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have h2 : Tendsto (fun i : ℝ => 1 - 1 / (1 + θ * (1 + i))) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 h1))
  rw [sub_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with i hi
  rw [(elasticity_lt_one hθ hY hi).1]
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  field_simp
  ring

/-- Woodford (2003), p. 654: the elasticity with respect to `i`, `iλ'(i)/λ(i) = θi/(1 + θ(1 + i))`,
is also below one for `i ≥ 0`. -/
theorem elasticity_i_lt_one {θ Y i : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hi : 0 ≤ i) :
    i * (θ / Y) / lamSGU θ Y i < 1 := by
  have hd : 0 < 1 + θ * (1 + i) := by nlinarith
  unfold lamSGU
  rw [div_lt_one (by positivity)]
  rw [mul_div_assoc', div_lt_div_iff_of_pos_right hY]
  nlinarith

/-! ## The Taylor rule (A.56) -/

/-- Woodford (2003), (A.56), p. 654: `1 + φ(Π) = β⁻¹[Π* + φ_π(Π − Π*)]` on its linear range. -/
noncomputable def ellSGU (β Pis φπ x : ℝ) : ℝ := (Pis + φπ * (x - Pis)) / β

/-- Woodford (2003), (A.56) and fn. 8, p. 655: the rule
`φ(Π) = β⁻¹[Π* + φ_π(Π − Π*)] − 1`, truncated at zero ("this form holds … only for inflation
rates for which it implies a nonnegative interest rate"). -/
noncomputable def phiSGU (β Pis φπ x : ℝ) : ℝ := max 0 (ellSGU β Pis φπ x - 1)

/-- Woodford (2003), (A.56): `1 + φ(Π) = max(1, ℓ(Π))`. -/
theorem one_add_phiSGU (β Pis φπ x : ℝ) :
    1 + phiSGU β Pis φπ x = max 1 (ellSGU β Pis φπ x) := by
  unfold phiSGU
  rw [← max_add_add_left]
  simp

/-- Woodford (2003), (A.56): `φ ≥ 0`. -/
theorem phiSGU_nonneg (β Pis φπ x : ℝ) : 0 ≤ phiSGU β Pis φπ x := le_max_left _ _

/-- Woodford (2003), (A.56): the rule is continuous. -/
theorem phiSGU_continuous (β Pis φπ : ℝ) : Continuous (phiSGU β Pis φπ) := by
  unfold phiSGU ellSGU
  fun_prop

/-- Woodford (2003), (A.56), p. 655: the rule is "consistent with a steady-state inflation rate
`Π*`": `φ(Π*) = β⁻¹Π* − 1` when `Π* ≥ β`. -/
theorem phiSGU_target {β Pis φπ : ℝ} (hβ : 0 < β) (hPis : β ≤ Pis) :
    phiSGU β Pis φπ Pis = Pis / β - 1 := by
  unfold phiSGU ellSGU
  rw [sub_self, mul_zero, add_zero, max_eq_right]
  rw [sub_nonneg, le_div_iff₀ hβ]
  linarith

/-- Woodford (2003), p. 655, "such a rule satisfies the Taylor principle if and only if
`φ_π > 1`": for `Π* > β`, `φ'(Π*) = φ_π/β`, and the Taylor coefficient `Π*φ'(Π*)/(1 + φ(Π*))`
(= the slope `βφ'(Π*)` of the map (4.6), `GlobalDynamics.taylorCoeff_eq_slope`) equals `φ_π`. -/
theorem taylorCoeff_phiSGU {β Pis φπ : ℝ} (hβ : 0 < β) (hPis : β < Pis) :
    HasDerivAt (phiSGU β Pis φπ) (φπ / β) Pis ∧
      Pis * (φπ / β) / (1 + phiSGU β Pis φπ Pis) = φπ := by
  have hlin : HasDerivAt (fun x => ellSGU β Pis φπ x - 1) (φπ / β) Pis := by
    have h := ((((hasDerivAt_id Pis).sub_const Pis).const_mul φπ).const_add Pis).div_const β
    simpa [ellSGU] using h.sub_const 1
  have hval : 0 < ellSGU β Pis φπ Pis - 1 := by
    unfold ellSGU
    rw [sub_self, mul_zero, add_zero, sub_pos, one_lt_div hβ]
    exact hPis
  have hev : (phiSGU β Pis φπ) =ᶠ[𝓝 Pis] fun x => ellSGU β Pis φπ x - 1 := by
    have hc : ContinuousAt (fun x => ellSGU β Pis φπ x - 1) Pis := hlin.continuousAt
    filter_upwards [hc.eventually (lt_mem_nhds hval)] with x hx
    unfold phiSGU
    rw [max_eq_right hx.le]
  refine ⟨hlin.congr_of_eventuallyEq hev, ?_⟩
  rw [taylorCoeff_eq_slope hβ (by linarith) (phiSGU_target hβ hPis.le)]
  field_simp

/-! ## The functions `A` and `B` -/

/-- Woodford (2003), p. 655: `A(Π) ≡ λ(φ(Π))/(1 + φ(Π))`. -/
noncomputable def sguA (θ Y β Pis φπ x : ℝ) : ℝ :=
  lamSGU θ Y (phiSGU β Pis φπ x) / (1 + phiSGU β Pis φπ x)

/-- Woodford (2003), p. 655: `B(Π) ≡ βλ(φ(Π))/Π`. -/
noncomputable def sguB (θ Y β Pis φπ x : ℝ) : ℝ := β * lamSGU θ Y (phiSGU β Pis φπ x) / x

/-- Woodford (2003), p. 655 (error E5): the constant `β + θΠ*(1 − φ_π)`, whose sign decides the
direction of monotonicity of `B`. -/
def sguC (θ β Pis φπ : ℝ) : ℝ := β + θ * Pis * (1 - φπ)

/-- Woodford (2003), p. 654: `λ(φ(Π)) > 0`. -/
theorem lamSGU_phi_pos {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) :
    0 < lamSGU θ Y (phiSGU β Pis φπ x) := by
  unfold lamSGU
  have := phiSGU_nonneg β Pis φπ x
  have : 0 < 1 + θ * (1 + phiSGU β Pis φπ x) := by nlinarith
  positivity

/-- Woodford (2003), (4.5) ⇔ p. 655: for positive inflation rates, (4.5) is
`B(Π_{t+1}) = A(Π_t)`. -/
theorem eq45_iff_AB {θ Y β Pis φπ x x' : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hx' : 0 < x') :
    x' / lamSGU θ Y (phiSGU β Pis φπ x') =
        β * (1 + phiSGU β Pis φπ x) / lamSGU θ Y (phiSGU β Pis φπ x) ↔
      sguB θ Y β Pis φπ x' = sguA θ Y β Pis φπ x := by
  have h1 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := x) hθ hY
  have h2 := lamSGU_phi_pos (β := β) (Pis := Pis) (φπ := φπ) (x := x') hθ hY
  have h3 : 0 < 1 + phiSGU β Pis φπ x := by linarith [phiSGU_nonneg β Pis φπ x]
  unfold sguA sguB
  rw [div_eq_div_iff h2.ne' h1.ne', div_eq_div_iff hx'.ne' h3.ne']
  constructor <;> intro h <;> nlinarith

/-- Woodford (2003), p. 655: in terms of `M = 1 + φ(Π) = max(1, ℓ(Π))`,
`A = (1 + θM)/(ȲM)` and `B = β(1 + θM)/(ȲΠ)`. -/
theorem sguAB_formula (θ Y β Pis φπ x : ℝ) :
    sguA θ Y β Pis φπ x = (1 + θ * max 1 (ellSGU β Pis φπ x)) / Y / max 1 (ellSGU β Pis φπ x) ∧
      sguB θ Y β Pis φπ x = β * ((1 + θ * max 1 (ellSGU β Pis φπ x)) / Y) / x := by
  unfold sguA sguB lamSGU
  rw [one_add_phiSGU]
  exact ⟨rfl, rfl⟩

/-- Woodford (2003), p. 655, with the factor `1/Ȳ` restored: on the linear range of the rule,
`B(Π) = [β + θΠ*(1 − φ_π)]/(ȲΠ) + θφ_π/Ȳ`. -/
theorem sguB_formula {θ Y β Pis φπ x : ℝ} (hβ : 0 < β) (hY : 0 < Y) (hx : 0 < x)
    (hl : 1 ≤ ellSGU β Pis φπ x) :
    sguB θ Y β Pis φπ x = sguC θ β Pis φπ / (Y * x) + θ * φπ / Y := by
  rw [(sguAB_formula θ Y β Pis φπ x).2, max_eq_right hl]
  unfold ellSGU sguC
  field_simp
  ring

/-- Woodford (2003), p. 655, "`A(Π)` is a monotonically decreasing function of `Π`": for
`φ_π ≥ 0`. -/
theorem sguA_antitone {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 0 ≤ φπ) : Antitone (sguA θ Y β Pis φπ) := by
  intro a b hab
  have hM : max 1 (ellSGU β Pis φπ a) ≤ max 1 (ellSGU β Pis φπ b) := by
    refine max_le_max le_rfl ?_
    unfold ellSGU
    exact div_le_div_of_nonneg_right (by nlinarith) hβ.le
  have ha1 : 1 ≤ max 1 (ellSGU β Pis φπ a) := le_max_left _ _
  rw [(sguAB_formula θ Y β Pis φπ a).1, (sguAB_formula θ Y β Pis φπ b).1]
  set Ma := max 1 (ellSGU β Pis φπ a)
  set Mb := max 1 (ellSGU β Pis φπ b)
  rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hY (by linarith : (0 : ℝ) < Ma)]

/-- Woodford (2003), p. 655, "approaches the asymptotic value of `θ`" — with the factor `1/Ȳ`
the text omits: `A(Π) → θ/Ȳ` as `Π → ∞` (for `φ_π > 0`). -/
theorem sguA_tendsto {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hφπ : 0 < φπ) :
    Tendsto (sguA θ Y β Pis φπ) atTop (𝓝 (θ / Y)) := by
  have hl : Tendsto (ellSGU β Pis φπ) atTop atTop := by
    unfold ellSGU
    refine Tendsto.atTop_div_const hβ ?_
    exact tendsto_atTop_add_const_left _ Pis
      (Tendsto.const_mul_atTop hφπ (tendsto_atTop_add_const_right _ (-Pis) tendsto_id))
  have h1 : Tendsto (fun x => 1 / (Y * ellSGU β Pis φπ x) + θ / Y) atTop (𝓝 (0 + θ / Y)) :=
    (tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hY hl)).add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [hl.eventually (eventually_ge_atTop 1)] with x hx
  rw [(sguAB_formula θ Y β Pis φπ x).1, max_eq_right hx]
  field_simp

/-- Woodford (2003), p. 655, error E5: if `β + θΠ*(1 − φ_π) > 0`, `B` is strictly decreasing on
`(0, ∞)` (on both the linear and the truncated range of the rule). -/
theorem sguB_strictAntiOn {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hc : 0 < sguC θ β Pis φπ) : StrictAntiOn (sguB θ Y β Pis φπ) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  rw [(sguAB_formula θ Y β Pis φπ a).2, (sguAB_formula θ Y β Pis φπ b).2]
  set Ma := max 1 (ellSGU β Pis φπ a) with hMa
  set Mb := max 1 (ellSGU β Pis φπ b) with hMb
  have hMa1 : 1 ≤ Ma := le_max_left _ _
  have hMal : ellSGU β Pis φπ a ≤ Ma := le_max_right _ _
  have hid : ∀ x, β * (1 + θ * ellSGU β Pis φπ x) = sguC θ β Pis φπ + θ * φπ * x := by
    intro x; unfold ellSGU sguC; field_simp; ring
  rw [div_lt_div_iff₀ hb' ha']
  suffices key : β * (1 + θ * Mb) * a < β * (1 + θ * Ma) * b by
    have e1 : β * ((1 + θ * Mb) / Y) * a = (1 / Y) * (β * (1 + θ * Mb) * a) := by ring
    have e2 : β * ((1 + θ * Ma) / Y) * b = (1 / Y) * (β * (1 + θ * Ma) * b) := by ring
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left key (by positivity)
  rcases le_total 1 (ellSGU β Pis φπ b) with hl | hl
  · have hMbe : Mb = ellSGU β Pis φπ b := max_eq_right hl
    rw [hMbe, hid b]
    have h1 : β * (1 + θ * ellSGU β Pis φπ a) ≤ β * (1 + θ * Ma) := by
      have := mul_le_mul_of_nonneg_left hMal hθ.le; nlinarith
    rw [hid a] at h1
    nlinarith [mul_lt_mul_of_pos_left hab hc]
  · have hMbe : Mb = 1 := max_eq_left hl
    rw [hMbe]
    have h1 : β * (1 + θ * 1) ≤ β * (1 + θ * Ma) := by
      have := mul_le_mul_of_nonneg_left hMa1 hθ.le; nlinarith
    have h2 : 0 < β * (1 + θ * 1) := by positivity
    nlinarith [mul_lt_mul_of_pos_left hab h2]

/-- Woodford (2003), p. 655 (error E5): if `β + θΠ*(1 − φ_π) > 0` then `B(Π) > θφ_π/Ȳ` for every
`Π > 0` ("approaches the asymptotic value `φ_πθ`" from above). -/
theorem sguB_gt {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β) (hx : 0 < x)
    (hc : 0 < sguC θ β Pis φπ) : θ * φπ / Y < sguB θ Y β Pis φπ x := by
  rw [(sguAB_formula θ Y β Pis φπ x).2]
  have hle : ellSGU β Pis φπ x ≤ max 1 (ellSGU β Pis φπ x) := le_max_right _ _
  have hid : β * (1 + θ * ellSGU β Pis φπ x) = sguC θ β Pis φπ + θ * φπ * x := by
    unfold ellSGU sguC; field_simp; ring
  rw [lt_div_iff₀ hx, div_mul_eq_mul_div, mul_div_assoc', div_lt_div_iff_of_pos_right hY]
  have : β * (1 + θ * ellSGU β Pis φπ x) ≤ β * (1 + θ * max 1 (ellSGU β Pis φπ x)) := by
    have := mul_le_mul_of_nonneg_left hle hθ.le; nlinarith
  nlinarith

/-- Woodford (2003), p. 655: `B(Π) → θφ_π/Ȳ` as `Π → ∞` (for `φ_π > 0`). -/
theorem sguB_tendsto {θ Y β Pis φπ : ℝ} (hY : 0 < Y) (hβ : 0 < β) (hφπ : 0 < φπ) :
    Tendsto (sguB θ Y β Pis φπ) atTop (𝓝 (θ * φπ / Y)) := by
  have hl : Tendsto (ellSGU β Pis φπ) atTop atTop := by
    unfold ellSGU
    refine Tendsto.atTop_div_const hβ ?_
    exact tendsto_atTop_add_const_left _ Pis
      (Tendsto.const_mul_atTop hφπ (tendsto_atTop_add_const_right _ (-Pis) tendsto_id))
  have h1 : Tendsto (fun x => sguC θ β Pis φπ / (Y * x) + θ * φπ / Y) atTop
      (𝓝 (0 + θ * φπ / Y)) :=
    (tendsto_const_nhds.div_atTop (Tendsto.const_mul_atTop hY tendsto_id)).add
      tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [hl.eventually (eventually_ge_atTop 1), eventually_gt_atTop (0 : ℝ)]
    with x hx hx0
  rw [sguB_formula hβ hY hx0 hx]

/-- Woodford (2003), p. 655 (and the E6 condition of §4.1): if `φ_π > 1` and `Π* > β`, then
`A(Π) < B(Π)` for every `Π > Π*` — the curve (4.5) lies above the diagonal above the target. -/
theorem sguA_lt_B_above {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hx : Pis < x) :
    sguA θ Y β Pis φπ x < sguB θ Y β Pis φπ x := by
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ ellSGU β Pis φπ x := by
    unfold ellSGU; rw [le_div_iff₀ hβ]; nlinarith
  have hl0 : 0 < ellSGU β Pis φπ x := by linarith
  rw [(sguAB_formula θ Y β Pis φπ x).1, (sguAB_formula θ Y β Pis φπ x).2, max_eq_right hl]
  have hkey : x < β * ellSGU β Pis φπ x := by
    unfold ellSGU; field_simp; nlinarith
  have hp : 0 < (1 + θ * ellSGU β Pis φπ x) / Y := by positivity
  rw [div_lt_div_iff₀ hl0 hx0]
  nlinarith [mul_lt_mul_of_pos_left hkey hp]

/-- Woodford (2003), p. 655: if `φ_π > 1` and `Π* > β`, then `B(Π) < A(Π)` for `β < Π < Π*`. -/
theorem sguB_lt_A_below {θ Y β Pis φπ x : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hx1 : β < x) (hx2 : x < Pis) :
    sguB θ Y β Pis φπ x < sguA θ Y β Pis φπ x := by
  have hx0 : 0 < x := by linarith
  rw [(sguAB_formula θ Y β Pis φπ x).1, (sguAB_formula θ Y β Pis φπ x).2]
  rcases le_total 1 (ellSGU β Pis φπ x) with hl | hl
  · rw [max_eq_right hl]
    have hl0 : 0 < ellSGU β Pis φπ x := by linarith
    have hkey : β * ellSGU β Pis φπ x < x := by
      unfold ellSGU; field_simp; nlinarith
    have hp : 0 < (1 + θ * ellSGU β Pis φπ x) / Y := by positivity
    rw [div_lt_div_iff₀ hx0 hl0]
    nlinarith [mul_lt_mul_of_pos_left hkey hp]
  · rw [max_eq_left hl, div_one, div_lt_iff₀ hx0]
    have hp : 0 < (1 + θ * 1) / Y := by positivity
    nlinarith [mul_lt_mul_of_pos_left hx1 hp]

/-- Woodford (2003), p. 655: `ℓ(β) < 1` (so `φ(β) = 0` and `Π** = β`) when `φ_π > 1`, `Π* > β`;
hence `A(Π) = (1 + θ)/Ȳ = B(β)` for all `Π ≤ β`, and `A ≤ (1 + θ)/Ȳ` everywhere. -/
theorem sgu_at_beta {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β) (hφπ : 1 < φπ)
    (hPis : β < Pis) :
    ellSGU β Pis φπ β < 1 ∧ phiSGU β Pis φπ β = 0 ∧ sguB θ Y β Pis φπ β = (1 + θ) / Y ∧
      (∀ x, x ≤ β → sguA θ Y β Pis φπ x = (1 + θ) / Y) ∧
      ∀ x, sguA θ Y β Pis φπ x ≤ (1 + θ) / Y := by
  have hlβ : ellSGU β Pis φπ β < 1 := by
    unfold ellSGU; rw [div_lt_one hβ]; nlinarith
  have hmono : ∀ x, x ≤ β → ellSGU β Pis φπ x ≤ ellSGU β Pis φπ β := fun x hx => by
    unfold ellSGU; exact div_le_div_of_nonneg_right (by nlinarith) hβ.le
  refine ⟨hlβ, ?_, ?_, fun x hx => ?_, fun x => ?_⟩
  · unfold phiSGU; exact max_eq_left (by linarith)
  · rw [(sguAB_formula θ Y β Pis φπ β).2, max_eq_left hlβ.le]
    field_simp
  · rw [(sguAB_formula θ Y β Pis φπ x).1, max_eq_left (le_trans (hmono x hx) hlβ.le)]
    simp
  · rw [(sguAB_formula θ Y β Pis φπ x).1]
    have hM : 1 ≤ max 1 (ellSGU β Pis φπ x) := le_max_left _ _
    rw [div_div, div_le_div_iff₀ (by positivity) hY]
    nlinarith

/-- Woodford (2003), p. 655: the bound `Π̄`, defined by `1 + φ(Π̄) = 1/(θ(φ_π − 1))`. -/
noncomputable def sguPibar (θ β Pis φπ : ℝ) : ℝ := Pis + (β / (θ * (φπ - 1)) - Pis) / φπ

/-- Woodford (2003), p. 655, "there exists a finite `Π̄` such that `A(Π̄) = φ_πθ`" (with `1/Ȳ`):
under `φ_π > 1`, `Π* > β` and the E5 hypothesis `β + θΠ*(1 − φ_π) > 0`, `Π̄ > Π*`, and
`A(Π̄) = θφ_π/Ȳ`. -/
theorem sguPibar_spec {θ Y β Pis φπ : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ) :
    Pis < sguPibar θ β Pis φπ ∧ ellSGU β Pis φπ (sguPibar θ β Pis φπ) = 1 / (θ * (φπ - 1)) ∧
      sguA θ Y β Pis φπ (sguPibar θ β Pis φπ) = θ * φπ / Y := by
  have hk : 0 < θ * (φπ - 1) := by nlinarith
  have hφ0 : 0 < φπ := by linarith
  have hk1 : φπ - 1 ≠ 0 := by linarith
  have hkP : θ * (φπ - 1) * Pis < β := by unfold sguC at hc; nlinarith
  have hgt : Pis < β / (θ * (φπ - 1)) := by rw [lt_div_iff₀ hk]; linarith
  have hell : ellSGU β Pis φπ (sguPibar θ β Pis φπ) = 1 / (θ * (φπ - 1)) := by
    unfold ellSGU sguPibar
    field_simp
    ring
  have hPi : Pis < sguPibar θ β Pis φπ := by
    unfold sguPibar
    have : 0 < (β / (θ * (φπ - 1)) - Pis) / φπ := div_pos (by linarith) hφ0
    linarith
  refine ⟨hPi, hell, ?_⟩
  have h1 : 1 ≤ 1 / (θ * (φπ - 1)) := by
    rw [le_div_iff₀ hk, one_mul]
    have : Pis / β > 1 := (one_lt_div hβ).mpr hPis
    have h2 : θ * (φπ - 1) * Pis < β := hkP
    nlinarith
  rw [(sguAB_formula θ Y β Pis φπ _).1, hell, max_eq_right h1]
  field_simp
  ring

/-- Woodford (2003), p. 655, "in the case of any `Π_t ≥ Π̄`, there is no value for `Π_{t+1}` that
would satisfy (4.5)" — true under the E5 hypothesis. -/
theorem sgu_no_successor {θ Y β Pis φπ x x' : ℝ} (hθ : 0 < θ) (hY : 0 < Y) (hβ : 0 < β)
    (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hx : sguPibar θ β Pis φπ ≤ x) (hx' : 0 < x') :
    sguB θ Y β Pis φπ x' ≠ sguA θ Y β Pis φπ x := by
  have h1 := sguA_antitone (θ := θ) (Pis := Pis) hY hβ (by linarith : (0 : ℝ) ≤ φπ) hx
  rw [(sguPibar_spec hθ hY hβ hφπ hPis hc).2.2] at h1
  have h2 := sguB_gt hθ hY hβ hx' hc (Pis := Pis) (φπ := φπ)
  intro h
  linarith

/-- Woodford (2003), p. 655: `A` and `B` are continuous at every `Π > 0`. -/
theorem sguAB_continuousAt {θ Y β Pis φπ x : ℝ} (hY : 0 < Y) (hx : 0 < x) :
    ContinuousAt (sguA θ Y β Pis φπ) x ∧ ContinuousAt (sguB θ Y β Pis φπ) x := by
  have hφ := (phiSGU_continuous β Pis φπ).continuousAt (x := x)
  have hl : ContinuousAt (fun z => lamSGU θ Y (phiSGU β Pis φπ z)) x := by
    unfold lamSGU
    exact ((continuousAt_const.add (continuousAt_const.mul (continuousAt_const.add hφ)))).div
      continuousAt_const hY.ne'
  refine ⟨hl.div (continuousAt_const.add hφ) (by linarith [phiSGU_nonneg β Pis φπ x]), ?_⟩
  exact (continuousAt_const.mul hl).div continuousAt_id hx.ne'

/-! ## Exclusion of self-fulfilling inflations and deflations -/

/-- Woodford (2003), p. 655, "it is not possible to have a perfect-foresight equilibrium sequence
… in which `Π_t > Π*` in any period", under the added E5 hypothesis
`β + θΠ*(1 − φ_π) > 0` (with `φ_π > 1`, `Π* > β`): every solution of (4.5) satisfies `Π_t ≤ Π*`
at all dates. (Proof: above `Π*` the path must rise — `B > A` there and `B` is decreasing —
while `B > θφ_π/Ȳ` keeps it below `Π̄`; a bounded increasing path would converge to a steady
state above `Π*`, which does not exist.) -/
theorem sgu_no_hyperinflation {θ Y β Pis φπ : ℝ} {Pi_ : ℕ → ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) : ∀ t, Pi_ t ≤ Pis := by
  intro t0
  by_contra hcon
  push Not at hcon
  have hAB : ∀ t, sguB θ Y β Pis φπ (Pi_ (t + 1)) = sguA θ Y β Pis φπ (Pi_ t) := fun t =>
    (eq45_iff_AB hθ hY (hpath.1 (t + 1))).mp (hpath.2 t)
  have hsa := sguB_strictAntiOn (Y := Y) hθ hY hβ hc
  set y : ℕ → ℝ := fun n => Pi_ (n + t0) with hy
  have hyAB : ∀ n, sguB θ Y β Pis φπ (y (n + 1)) = sguA θ Y β Pis φπ (y n) := fun n => by
    simp only [hy, show n + 1 + t0 = n + t0 + 1 by omega]; exact hAB _
  have hypos : ∀ n, 0 < y n := fun n => hpath.1 _
  have hstep : ∀ n, Pis < y n ∧ y n < y (n + 1) := by
    intro n
    induction n with
    | zero =>
      have h0 : Pis < y 0 := by simp only [hy, zero_add]; exact hcon
      refine ⟨h0, ?_⟩
      by_contra hle
      push Not at hle
      have h1 := hsa.antitoneOn (hypos 1) (hypos 0) hle
      have h2 := sguA_lt_B_above hθ hY hβ hφπ hPis h0 (Y := Y)
      rw [hyAB 0] at h1
      linarith
    | succ n ih =>
      have h0 : Pis < y (n + 1) := by linarith [ih.1, ih.2]
      refine ⟨h0, ?_⟩
      by_contra hle
      push Not at hle
      have h1 := hsa.antitoneOn (hypos _) (hypos _) hle
      have h2 := sguA_lt_B_above hθ hY hβ hφπ hPis h0 (Y := Y)
      rw [hyAB (n + 1)] at h1
      linarith
  have hmono : Monotone y := monotone_nat_of_le_succ fun n => (hstep n).2.le
  have hbdd : BddAbove (Set.range y) := by
    refine ⟨sguPibar θ β Pis φπ, ?_⟩
    rintro _ ⟨n, rfl⟩
    by_contra hgt
    push Not at hgt
    exact sgu_no_successor hθ hY hβ hφπ hPis hc hgt.le (hypos (n + 1)) (hyAB n)
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ n, y n with hL
  have hL0 : y 0 ≤ L := le_ciSup hbdd 0
  have hLpos : 0 < L := by linarith [hypos 0]
  have hcont := sguAB_continuousAt (θ := θ) (β := β) (Pis := Pis) (φπ := φπ) hY hLpos
  have h1 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguB θ Y β Pis φπ L)) :=
    hcont.2.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguA θ Y β Pis φπ L)) := by
    simp only [hyAB]; exact hcont.1.tendsto.comp hlim
  have heq := tendsto_nhds_unique h1 h2
  have := sguA_lt_B_above hθ hY hβ hφπ hPis (by linarith [(hstep 0).1] : Pis < L) (Y := Y)
  linarith

/-- Woodford (2003), p. 655 and §4.2: under the hypotheses of `sgu_no_hyperinflation`, a
perfect-foresight path that is ever below `Π*` converges to the Friedman rate `Π** = β`. -/
theorem sgu_deflation_tendsto {θ Y β Pis φπ : ℝ} {Pi_ : ℕ → ℝ} (hθ : 0 < θ) (hY : 0 < Y)
    (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) {t0 : ℕ} (ht0 : Pi_ t0 < Pis) :
    Tendsto Pi_ atTop (𝓝 β) := by
  have hAB : ∀ t, sguB θ Y β Pis φπ (Pi_ (t + 1)) = sguA θ Y β Pis φπ (Pi_ t) := fun t =>
    (eq45_iff_AB hθ hY (hpath.1 (t + 1))).mp (hpath.2 t)
  have hsa := sguB_strictAntiOn (Y := Y) hθ hY hβ hc
  obtain ⟨-, -, hBβ, hAle, hAmax⟩ := sgu_at_beta (Y := Y) hθ hY hβ hφπ hPis
  -- the successor of any `Π < Π*` lies in `[β, max(Π, β)]`, strictly below `Π` if `Π > β`
  have hsucc : ∀ x x', 0 < x → x < Pis → 0 < x' →
      sguB θ Y β Pis φπ x' = sguA θ Y β Pis φπ x → β ≤ x' ∧ (x ≤ β → x' = β) ∧
        (β < x → x' < x) := by
    intro x x' hx hxP hx' hBA
    have hlow : β ≤ x' := by
      by_contra hlt
      push Not at hlt
      have := hsa hx' hβ hlt
      rw [hBA, hBβ] at this
      linarith [hAmax x]
    refine ⟨hlow, fun hxβ => ?_, fun hxβ => ?_⟩
    · rw [hAle x hxβ, ← hBβ] at hBA
      exact hsa.injOn hx' hβ hBA
    · by_contra hge
      push Not at hge
      have h1 := hsa.antitoneOn hx hx' hge
      have h2 := sguB_lt_A_below (Y := Y) hθ hY hβ hφπ hxβ hxP
      rw [hBA] at h1
      linarith
  set y : ℕ → ℝ := fun n => Pi_ (n + (t0 + 1)) with hy
  have hyAB : ∀ n, sguB θ Y β Pis φπ (y (n + 1)) = sguA θ Y β Pis φπ (y n) := fun n => by
    simp only [hy, show n + 1 + (t0 + 1) = n + (t0 + 1) + 1 by omega]; exact hAB _
  have hypos : ∀ n, 0 < y n := fun n => hpath.1 _
  have hy0 : β ≤ y 0 ∧ y 0 < Pis := by
    have h := hsucc _ _ (hpath.1 t0) ht0 (hpath.1 (t0 + 1)) (hAB t0)
    simp only [hy, zero_add]
    refine ⟨h.1, ?_⟩
    rcases le_or_gt (Pi_ t0) β with hle | hlt
    · rw [h.2.1 hle]; exact hPis
    · exact lt_trans (h.2.2 hlt) ht0
  have hstep : ∀ n, (β ≤ y n ∧ y n < Pis) ∧ y (n + 1) ≤ y n := by
    intro n
    induction n with
    | zero =>
      refine ⟨hy0, ?_⟩
      have h := hsucc _ _ (hypos 0) hy0.2 (hypos 1) (hyAB 0)
      rcases hy0.1.lt_or_eq with hlt | heq
      · exact (h.2.2 hlt).le
      · rw [h.2.1 heq.symm.le, heq]
    | succ n ih =>
      have h := hsucc _ _ (hypos n) ih.1.2 (hypos (n + 1)) (hyAB n)
      have hmem : β ≤ y (n + 1) ∧ y (n + 1) < Pis := ⟨h.1, lt_of_le_of_lt ih.2 ih.1.2⟩
      refine ⟨hmem, ?_⟩
      have h' := hsucc _ _ (hypos (n + 1)) hmem.2 (hypos (n + 2)) (hyAB (n + 1))
      rcases hmem.1.lt_or_eq with hlt | heq
      · exact (h'.2.2 hlt).le
      · rw [h'.2.1 heq.symm.le, heq]
  have hanti : Antitone y := antitone_nat_of_succ_le fun n => (hstep n).2
  have hbdd : BddBelow (Set.range y) := ⟨β, by rintro _ ⟨n, rfl⟩; exact (hstep n).1.1⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set L := ⨅ n, y n with hL
  have hLβ : β ≤ L := le_ciInf fun n => (hstep n).1.1
  have hLP : L < Pis := lt_of_le_of_lt (ciInf_le hbdd 0) (hstep 0).1.2
  have hcont := sguAB_continuousAt (θ := θ) (β := β) (Pis := Pis) (φπ := φπ) hY
    (by linarith : 0 < L) (Y := Y)
  have h1 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguB θ Y β Pis φπ L)) :=
    hcont.2.tendsto.comp ((tendsto_add_atTop_iff_nat 1).mpr hlim)
  have h2 : Tendsto (fun n => sguB θ Y β Pis φπ (y (n + 1))) atTop
      (𝓝 (sguA θ Y β Pis φπ L)) := by
    simp only [hyAB]; exact hcont.1.tendsto.comp hlim
  have heq := tendsto_nhds_unique h1 h2
  have hLeq : L = β := by
    rcases hLβ.lt_or_eq with hlt | heq'
    · have := sguB_lt_A_below (Y := Y) hθ hY hβ hφπ hlt hLP
      linarith
    · exact heq'.symm
  rw [hLeq] at hlim
  exact (tendsto_add_atTop_iff_nat (t0 + 1)).mp hlim

/-- Woodford (2003), p. 655, "Schmitt-Grohé and Uribe establish that in the case of an
interest-rate rule satisfying the Taylor principle and a balanced-budget fiscal rule, the unique
perfect-foresight equilibrium is the one in which `Π_t = Π*` at all times", under the added E5
hypothesis `β + θΠ*(1 − φ_π) > 0`: with nominal liabilities growing at `μ̄`, `1 < μ̄ < Π*/β`,
the constant path `Π*` solves (4.5) and satisfies the transversality condition (1.24), and a
solution of (4.5) satisfies (1.24) iff it is that constant path. -/
theorem sgu_unique_pf_equilibrium {θ Y β Pis φπ μ : ℝ} {Pi_ P D : ℕ → ℝ} (hθ : 0 < θ)
    (hY : 0 < Y) (hβ : 0 < β) (hφπ : 1 < φπ) (hPis : β < Pis) (hc : 0 < sguC θ β Pis φπ)
    (hμ : 1 < μ) (hμPis : β * μ < Pis)
    (hpath : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_) (hP : ∀ t, 0 < P t)
    (hPrec : ∀ t, P (t + 1) = Pi_ (t + 1) * P t) (hD : ∀ t, D (t + 1) = μ * D t)
    (hDpos : ∀ t, 0 < D t) :
    IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) (fun _ => Pis) ∧
      (Tendsto (tvcValue β (lamSGU θ Y) (phiSGU β Pis φπ) Pi_ P D) atTop (𝓝 0) ↔
        ∀ t, Pi_ t = Pis) := by
  have htarget : 1 + phiSGU β Pis φπ Pis = Pis / β := by
    rw [phiSGU_target hβ hPis.le]; ring
  have hconst : IsPath45 β (lamSGU θ Y) (phiSGU β Pis φπ) (fun _ => Pis) :=
    ⟨fun _ => by linarith, fun _ => by
      rw [htarget]; field_simp⟩
  refine ⟨hconst, ⟨fun htvc t => ?_, fun hall => ?_⟩⟩
  · have hle := sgu_no_hyperinflation hθ hY hβ hφπ hPis hc hpath t
    by_contra hne
    have hlt : Pi_ t < Pis := lt_of_le_of_ne hle hne
    have hlim := sgu_deflation_tendsto hθ hY hβ hφπ hPis hc hpath hlt
    obtain ⟨-, hφβ, -, -, -⟩ := sgu_at_beta (Y := Y) hθ hY hβ hφπ hPis
    exact deflation_tvc_violated hβ hpath (fun s => lamSGU_phi_pos hθ hY)
      (fun s => phiSGU_nonneg _ _ _ _) hP hPrec hD hDpos hlim
      (phiSGU_continuous β Pis φπ).continuousAt (by rw [hφβ, div_self hβ.ne']; ring)
      (by rw [div_self hβ.ne']; exact hμ) htvc
  · have hPi : Pi_ = fun _ => Pis := funext hall
    subst hPi
    exact (target_tvc_iff hβ (by linarith) (by linarith) htarget (lamSGU_phi_pos hθ hY) hP
      hPrec hD hDpos).mpr hμPis

/-! ## Error E5: a counterexample when `β + θΠ*(1 − φ_π) < 0` -/

/-- Woodford (2003), A.17, error E5: the successor map on the upper branch of (4.5) in the
counterexample `β = 1/2, θ = 1, φ_π = 3/2, Π* = 3, Ȳ = 1`: `Π ↦ (6Π − 6)/(3Π − 5)`. -/
noncomputable def gE5 (x : ℝ) : ℝ := (6 * x - 6) / (3 * x - 5)

/-- Woodford (2003), A.17, error E5: the price level `P_t = ∏_{s<t} Π_{s+1}` (with `P₀ = 1`). -/
def priceFrom (Pi_ : ℕ → ℝ) (t : ℕ) : ℝ := ∏ s ∈ Finset.range t, Pi_ (s + 1)

/-- Woodford (2003), A.17, error E5: in the counterexample, `φ(Π) = 3Π − 4` for `Π ≥ 4/3`. -/
theorem phiE5 {x : ℝ} (hx : 4 / 3 ≤ x) : phiSGU (1 / 2) 3 (3 / 2) x = 3 * x - 4 := by
  unfold phiSGU ellSGU
  rw [max_eq_right (by linarith)]
  ring

/-- Woodford (2003), A.17, error E5: the interval `[32/13, 4]` is invariant under the upper
branch map. -/
theorem gE5_mem {x : ℝ} (h1 : 32 / 13 ≤ x) (h2 : x ≤ 4) : 32 / 13 ≤ gE5 x ∧ gE5 x ≤ 4 := by
  unfold gE5
  have hd : 0 < 3 * x - 5 := by linarith
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd]; linarith

/-- Woodford (2003), A.17, error E5: on `[32/13, 4]` the upper branch map solves (4.5). -/
theorem gE5_eq45 {x : ℝ} (h1 : 32 / 13 ≤ x) (h2 : x ≤ 4) :
    gE5 x / lamSGU 1 1 (phiSGU (1 / 2) 3 (3 / 2) (gE5 x)) =
      1 / 2 * (1 + phiSGU (1 / 2) 3 (3 / 2) x) / lamSGU 1 1 (phiSGU (1 / 2) 3 (3 / 2) x) := by
  have hg := gE5_mem h1 h2
  rw [phiE5 (by linarith), phiE5 (by linarith [hg.1])]
  unfold lamSGU gE5
  have hd : 0 < 3 * x - 5 := by linarith
  have e1 : (1 + 1 * (1 + (3 * ((6 * x - 6) / (3 * x - 5)) - 4))) / 1 =
      (12 * x - 8) / (3 * x - 5) := by
    field_simp; ring
  have e2 : (1 + 1 * (1 + (3 * x - 4))) / 1 = 3 * x - 2 := by ring
  rw [e1, e2, div_div_div_cancel_right₀ hd.ne', div_eq_div_iff (by linarith) (by linarith)]
  ring

/-- Woodford (2003), A.17, p. 655, error E5 — counterexample. Take `β = 1/2`, `θ = 1`,
`φ_π = 3/2 > 1` (Taylor principle), `Π* = 3`, `Ȳ = 1`; then `β + θΠ*(1 − φ_π) = −1 < 0`, and:
(i) the printed bound `Π̄` (`A(Π̄) = θφ_π/Ȳ`) is `5/3 < Π*`; (ii) `B` is not decreasing
(`B(3) < B(4)`); (iii) contrary to "in the case of any `Π_t ≥ Π̄` there is no value for `Π_{t+1}`
that would satisfy (4.5)", `Π_t = 4` has the successor `18/7`; (iv) with nominal liabilities
`D_t = 2^t` (`μ̄ = 2 ∈ (1, Π*/β)`) and `P_t = ∏_{s<t}Π_{s+1}`, both `Π_t ≡ 3` and the path
`Π_0 = 4`, `Π_{t+1} = (6Π_t − 6)/(3Π_t − 5)` solve (4.5), satisfy (4.4) (with
`L(i) = Ȳ/(1 + θ(1 + i))`) and satisfy the transversality condition (1.24): the
perfect-foresight equilibrium is not unique, and `Π_0 = 4 > Π*` refutes "`Π_t ≤ Π*` at all
times". -/
theorem e5_counterexample :
    sguC 1 (1 / 2) 3 (3 / 2) = -1 ∧
      (sguA 1 1 (1 / 2) 3 (3 / 2) (5 / 3) = 1 * (3 / 2) / 1 ∧ (5 / 3 : ℝ) < 3) ∧
      sguB 1 1 (1 / 2) 3 (3 / 2) 3 < sguB 1 1 (1 / 2) 3 (3 / 2) 4 ∧
      sguB 1 1 (1 / 2) 3 (3 / 2) (18 / 7) = sguA 1 1 (1 / 2) 3 (3 / 2) 4 ∧
      (IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) (fun _ => 3) ∧
        Tendsto (tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) (fun _ => 3)
          (priceFrom fun _ => 3) (fun t => 2 ^ t)) atTop (𝓝 0)) ∧
      ∃ Pi_ : ℕ → ℝ, Pi_ 0 = 4 ∧ IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ ∧
        Summable (bound44Term (1 / 2) 1 (lamSGU 1 1) (LSGU 1 1)
          (fun t => phiSGU (1 / 2) 3 (3 / 2) (Pi_ t))) ∧
        Tendsto (tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ (priceFrom Pi_)
          (fun t => 2 ^ t)) atTop (𝓝 0) := by
  have hφ3 : phiSGU (1 / 2) 3 (3 / 2) 3 = 5 := by rw [phiE5 (by norm_num)]; norm_num
  have hφ4 : phiSGU (1 / 2) 3 (3 / 2) 4 = 8 := by rw [phiE5 (by norm_num)]; norm_num
  refine ⟨by unfold sguC; norm_num, ⟨?_, by norm_num⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · unfold sguA lamSGU; rw [phiE5 (by norm_num)]; norm_num
  · unfold sguB lamSGU; rw [hφ3, hφ4]; norm_num
  · unfold sguA sguB lamSGU; rw [phiE5 (by norm_num), hφ4]; norm_num
  · exact ⟨fun _ => by norm_num, fun _ => by unfold lamSGU; rw [hφ3]; norm_num⟩
  · refine (target_tvc_iff (μ := 2) (by norm_num) (by norm_num) (by norm_num)
      (by rw [hφ3]; norm_num)
      (by unfold lamSGU; rw [hφ3]; norm_num) (fun t => by unfold priceFrom; positivity)
      (fun t => by unfold priceFrom; rw [Finset.prod_range_succ, mul_comm])
      (fun t => by show (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t; ring) (fun t => by positivity)).mpr
      (by norm_num)
  · set Pi_ : ℕ → ℝ := fun t => gE5^[t] 4 with hPi
    have hsucc : ∀ t, Pi_ (t + 1) = gE5 (Pi_ t) := fun t => Function.iterate_succ_apply' _ _ _
    have hmem : ∀ t, 32 / 13 ≤ Pi_ t ∧ Pi_ t ≤ 4 := by
      intro t
      induction t with
      | zero => simp only [hPi, Function.iterate_zero, id]; norm_num
      | succ n ih => rw [hsucc]; exact gE5_mem ih.1 ih.2
    have hpos : ∀ t, 0 < Pi_ t := fun t => by linarith [(hmem t).1]
    have hpath : IsPath45 (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ :=
      ⟨hpos, fun t => by rw [hsucc]; exact gE5_eq45 (hmem t).1 (hmem t).2⟩
    have hφ : ∀ t, phiSGU (1 / 2) 3 (3 / 2) (Pi_ t) = 3 * Pi_ t - 4 := fun t =>
      phiE5 (by linarith [(hmem t).1])
    refine ⟨Pi_, rfl, hpath, ?_, ?_⟩
    · refine (bound44_summable (β := 1 / 2) (ybar := 1) (Λ := 10) (K := 1) (by norm_num)
        (by norm_num) (by norm_num)
        (fun T => phiSGU_nonneg _ _ _ _) (fun T => lamSGU_phi_pos one_pos one_pos)
        (fun T => ?_) (fun j hj => ?_) (fun j hj => ?_)).2
      · unfold lamSGU; rw [hφ T]; linarith [(hmem T).2]
      · unfold LSGU; positivity
      · unfold LSGU
        rw [mul_div_assoc', div_le_one (by linarith)]
        linarith
    · have hP : ∀ t, 0 < priceFrom Pi_ t := fun t =>
        Finset.prod_pos fun s _ => hpos (s + 1)
      have hPrec : ∀ t, priceFrom Pi_ (t + 1) = Pi_ (t + 1) * priceFrom Pi_ t := fun t => by
        unfold priceFrom; rw [Finset.prod_range_succ, mul_comm]
      have hD : ∀ t, (2 : ℝ) ^ (t + 1) = 2 * 2 ^ t := fun t => by ring
      set V := tvcValue (1 / 2) (lamSGU 1 1) (phiSGU (1 / 2) 3 (3 / 2)) Pi_ (priceFrom Pi_)
        (fun t => 2 ^ t) with hV
      have hVsucc : ∀ T, V (T + 1) = V T * (2 / (1 + phiSGU (1 / 2) 3 (3 / 2) (Pi_ T))) :=
        tvcValue_succ (by norm_num) hpath (fun t => lamSGU_phi_pos one_pos one_pos)
          (fun t => by linarith [phiSGU_nonneg (1 / 2) 3 (3 / 2) (Pi_ t)]) hP hPrec hD
      have hV0 : ∀ T, 0 ≤ V T := fun T => by
        simp only [hV, tvcValue]
        have := lamSGU_phi_pos (β := 1 / 2) (Pis := 3) (φπ := 3 / 2) (x := Pi_ T)
          one_pos one_pos
        have := hP T
        positivity
      have hVle : ∀ T, V T ≤ V 0 * (26 / 57) ^ T := by
        intro T
        induction T with
        | zero => simp
        | succ n ih =>
          rw [hVsucc, hφ n, pow_succ]
          have h1 : 2 / (1 + (3 * Pi_ n - 4)) ≤ 26 / 57 := by
            rw [div_le_div_iff₀ (by linarith [(hmem n).1]) (by norm_num)]
            linarith [(hmem n).1]
          have h2 : 0 ≤ 2 / (1 + (3 * Pi_ n - 4)) := div_nonneg (by norm_num)
            (by linarith [(hmem n).1])
          calc V n * (2 / (1 + (3 * Pi_ n - 4))) ≤ V 0 * (26 / 57) ^ n * (2 / (1 + (3 * Pi_ n - 4)))
                := mul_le_mul_of_nonneg_right ih h2
            _ ≤ V 0 * (26 / 57) ^ n * (26 / 57) :=
                mul_le_mul_of_nonneg_left h1 (mul_nonneg (hV0 0) (by positivity))
            _ = V 0 * ((26 / 57) ^ n * (26 / 57)) := by ring
      have hlim : Tendsto (fun T => V 0 * (26 / 57 : ℝ) ^ T) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 26 / 57)
          (by norm_num)).const_mul (V 0)
      exact squeeze_zero hV0 hVle hlim

end Woodford.PriceLevelDetermination.SchmittGroheUribe
