/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.SmallModels
import PolicyResponseDynamics.Habit
import PolicyResponseDynamics.InvestmentLimits
import PolicyResponseDynamics.InvestmentNaturalRate

/-!
# Links between the modules of Chapter 5

Woodford (2003), *Interest and Prices*, Chapter 5 and Appendix D. Several modules take as
parameters or hypotheses relations that another module derives. This module proves that the
derived objects satisfy those hypotheses, so the downstream results hold for the derived model.

## Main results

* The investment model (§3, `InvestmentModel`) supplies Proposition 5.1 (`Prop51`):
  `investParams` (the coefficients `ω = νφ_h + ω_p`, `ρ_y`, `ρ_k = ρ_y − ν` of pp. 356–358),
  `investParams_admissible`, `capitalEuler_iff_eq37` ((3.7) of `Prop51` is the corrected (3.7)),
  `eq313_iff`, `calvoFOC_iff`, `mc312_of_eq311` ((3.12) from (3.11) and the demand curve), and
  `prop51_investmentModel`: **Proposition 5.1 for the derived model**;
  `a_sub_b_pos_investmentModel`: `a − b > 0` at every `ε_ψ` for the derived coefficients.
* The investment model supplies the IS block (`ISBlock`, `InvestmentNaturalRate`): `isPar`,
  `isPar_pos`, `capitalEuler_iff_eq37_IS` ((3.7) of `ISBlock` with `u_t = −c'ω E_t q_{t+1}`),
  `investEq_of_hasDerivAt` and `muEq_of_hasDerivAt` ((3.8), (3.9) are the exact derivatives of
  `InvestmentModel.eq_3_8`, `eq_3_9`), `mcEq_of_eq311` ((3.18) from (3.11) and (3.9)), and
  `prop52_investmentModel`: **Proposition 5.2 for the derived model**.
* (3.36) uses the (3.17) coefficients of `InvestmentLimits`: `sys36_row2_iff_solves317`,
  `sys36_row2_iff_eq314` (the third block of (3.36) is (3.17), equivalently Proposition 5.1's
  (3.14), when `ξ₀, ξ₁, ψ₁, ψ₂` are those of (3.17)), `eq327_S36`.
* Habit persistence (`Habit`) supplies (2.4) of `SmallModels`: `xTilde_eq_habit`,
  `eq24_of_habit`.
* The delayed Calvo derivation (`Predetermined`) supplies the Chapter 3 aggregate-supply
  relation that `Habit` takes as given: `asch3_of_calvo`.
* The habit root `δ` of (1.28) is the smaller root `μ₁` of the `(D.2)` polynomial family of
  `Prop51`: `habDelta_eq_mu1`.
-/

namespace Woodford.PolicyResponseDynamics.Links

open Filter Topology MeasureTheory

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The investment model and Proposition 5.1 -/

/-- Woodford (2003), pp. 356–359: the coefficients of Proposition 5.1 derived from the
primitives of §3.1: `ω = νφ_h + ω_p`, `ρ_y = νφ_h + φ_h ω_p/(φ_h − 1)`, `ρ_k = ρ_y − ν`
(`InvestmentModel.omega`, `rhoY`, `rhoK`). -/
noncomputable def investParams (α β δ θ ν φh ωp : ℝ) : Prop51.Params :=
  ⟨α, β, δ, θ, InvestmentModel.omega ν φh ωp, ν, InvestmentModel.rhoY ν φh ωp,
    InvestmentModel.rhoK ν φh ωp⟩

/-- Woodford (2003), pp. 356–359: for the book's primitives (`0 < α < 1`, `0 < β < 1`,
`0 < δ < 1`, `θ > 0`, `ν > 0`, `φ_h > 1`, `ω_p ≥ 0`) the derived coefficients satisfy every
restriction Proposition 5.1 uses (`Prop51.Admissible`). -/
theorem investParams_admissible {α β δ θ ν φh ωp : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hθ : 0 < θ) (hν : 0 < ν)
    (hφ : 1 < φh) (hωp : 0 ≤ ωp) : Prop51.Admissible (investParams α β δ θ ν φh ωp) where
  hα0 := hα0
  hα1 := hα1
  hβ0 := hβ0
  hβ1 := hβ1
  hδ0 := hδ0
  hδ1 := hδ1
  hθ := hθ
  hν := hν
  hων := by
    have := InvestmentModel.omega_sub_nu_pos hν hφ hωp
    change ν < InvestmentModel.omega ν φh ωp
    linarith
  hρk := (InvestmentModel.rhoY_gt_rhoK_pos hν hφ hωp).2
  hρy := by
    change InvestmentModel.rhoY ν φh ωp = InvestmentModel.rhoK ν φh ωp + ν
    rw [InvestmentModel.rhoK]; ring

/-- Woodford (2003), (3.7), p. 356: the capital Euler equation of `Prop51` (firm or aggregate) is
exactly the corrected (3.7) of `InvestmentModel` (`Linear.Eq37`) at every date, for any
coefficients. -/
theorem capitalEuler_iff_eq37 (P : Prop51.Params) (ε : ℝ) (lam y k q : ℕ → Ω → ℝ) :
    Prop51.CapitalEuler P 𝔼 ε lam y k q ↔
      ∀ t, InvestmentModel.Linear.Eq37 𝔼 P.β P.δ ε P.ρy P.ρk P.ω lam y k q t :=
  Iff.rfl

/-- Woodford (2003), (3.13), p. 359: (3.13) of `Prop51` is (3.13) of `InvestmentModel`. -/
theorem eq313_iff (P : Prop51.Params) (p s k : ℕ → Ω → ℝ) (t : ℕ) :
    Prop51.Eq313 P 𝔼 p s k t ↔ InvestmentModel.Linear.Eq313 𝔼 P.α P.β P.ω P.ν P.θ p s k t := by
  unfold Prop51.Eq313 InvestmentModel.Linear.Eq313
  rw [funext_iff]

/-- Woodford (2003), p. 359 (the Chapter 3 Calvo condition): the two modules' statements of the
resetting firm's first-order condition agree. -/
theorem calvoFOC_iff (P : Prop51.Params) (p sf : ℕ → Ω → ℝ) (t : ℕ) :
    Prop51.CalvoFOC P 𝔼 p sf t ↔ InvestmentModel.Linear.CalvoFOC 𝔼 P.α P.β p sf t := by
  unfold Prop51.CalvoFOC InvestmentModel.Linear.CalvoFOC
  rw [funext_iff]

omit 𝔼 in
/-- Woodford (2003), (3.12), p. 358: (3.11) for a firm and for the aggregate, with the demand
curve `ŷ(i) − Ŷ = −θ p̂(i)`, give (3.12) of `Prop51` for the relative capital stock
`k̃(i) = k̂(i) − K̂` (`InvestmentModel.Linear.eq_3_12`, date by date). -/
theorem mc312_of_eq311 (P : Prop51.Params) {sf s y Y kf K lam q p : ℕ → Ω → ℝ}
    (hf : ∀ τ, InvestmentModel.Linear.Eq311 P.ω P.ν sf y kf lam q τ)
    (ha : ∀ τ, InvestmentModel.Linear.Eq311 P.ω P.ν s Y K lam q τ)
    (hdem : ∀ τ, y τ - Y τ = (-P.θ) • p τ) : Prop51.MC312 P sf s (kf - K) p := by
  intro τ
  funext u
  have e1 := congrFun (hf τ) u
  have e2 := congrFun (ha τ) u
  have e3 := congrFun (hdem τ) u
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
  exact InvestmentModel.Linear.eq_3_12 e1 e2 e3

/-- **Woodford (2003), Proposition 5.1, (3.14), p. 359, for the model of §3.1–3.2.** Let every
firm `i` satisfy the corrected (3.7) (`InvestmentModel.Linear.Eq37`) and (3.11), the aggregates
satisfy them too, the demand curve hold, and every resetting firm satisfy the Chapter 3 Calvo
condition, with the coefficients derived from the primitives (`investParams`). Then, with the
relative capital stocks `k̃(i) = k̂(i) − K̂` bounded, adapted and predetermined and the
averaging hypotheses of `Prop51.prop51`, the identity (3.14) holds. -/
theorem prop51_investmentModel {α β δ θ ν φh ωp ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hθ : 0 < θ) (hν : 0 < ν)
    (hφ : 1 < φh) (hωp : 0 ≤ ωp) (hε : 0 < ε)
    (hD : α * β * Prop51.mu2 β (Prop51.cD (investParams α β δ θ ν φh ωp) ε) ≠ 1)
    {ι : Type*} [MeasurableSpace ι] (wt : Measure ι) [IsProbabilityMeasure wt]
    {y kf p sf : ι → ℕ → Ω → ℝ} {Y K lam q s infl : ℕ → Ω → ℝ} {pstar : Ω → ℝ} {B Bs Bπ : ℝ}
    (hfirm : ∀ i t, InvestmentModel.Linear.Eq37 𝔼 β δ ε (InvestmentModel.rhoY ν φh ωp)
      (InvestmentModel.rhoK ν φh ωp) (InvestmentModel.omega ν φh ωp) lam (y i) (kf i) q t)
    (hagg : ∀ t, InvestmentModel.Linear.Eq37 𝔼 β δ ε (InvestmentModel.rhoY ν φh ωp)
      (InvestmentModel.rhoK ν φh ωp) (InvestmentModel.omega ν φh ωp) lam Y K q t)
    (hdem : ∀ i τ, y i τ - Y τ = (-θ) • p i τ)
    (h311f : ∀ i τ, InvestmentModel.Linear.Eq311 (InvestmentModel.omega ν φh ωp) ν (sf i) (y i)
      (kf i) lam q τ)
    (h311a : ∀ τ, InvestmentModel.Linear.Eq311 (InvestmentModel.omega ν φh ωp) ν s Y K lam q τ)
    (t : ℕ) (hcalvo : ∀ i, InvestmentModel.Linear.CalvoFOC 𝔼 α β (p i) (sf i) t)
    (hp : ∀ i τ ω, |p i τ ω| ≤ B) (hk : ∀ i, BoundedProc (kf i - K))
    (hka : ∀ i, 𝔼.Adapted (kf i - K)) (hpre : ∀ i τ, 𝔼.E τ ((kf i - K) (τ + 1)) =
      (kf i - K) (τ + 1))
    (hs : ∀ τ ω, |s τ ω| ≤ Bs) (hπ : ∀ τ ω, |infl τ ω| ≤ Bπ)
    (hik : ∀ ω, Integrable (fun i => (kf i - K) t ω) wt)
    (hip : ∀ n ω, Integrable (fun i => 𝔼.E t (p i (t + n)) ω) wt)
    (havk : ∀ ω, ∫ i, (kf i - K) t ω ∂wt = 0)
    (havp : ∀ n ω, ∫ i, 𝔼.E t (p i (t + n)) ω ∂wt =
      pstar ω - ∑ j ∈ Finset.range n, 𝔼.E t (infl (t + j + 1)) ω) (ω : Ω) :
    (Prop51.aM (investParams α β δ θ ν φh ωp) ε - Prop51.bM (investParams α β δ θ ν φh ωp) ε) *
        pstar ω =
      ∑' k, (α * β) ^ k * 𝔼.E t (s (t + k)) ω +
        Prop51.aM (investParams α β δ θ ν φh ωp) ε *
          ∑' k, (α * β) ^ (k + 1) * 𝔼.E t (infl (t + k + 1)) ω -
        Prop51.bM (investParams α β δ θ ν φh ωp) ε *
          ∑' k, (Prop51.mu2 β (Prop51.cD (investParams α β δ θ ν φh ωp) ε))⁻¹ ^ (k + 1) *
            𝔼.E t (infl (t + k + 1)) ω := by
  set P := investParams α β δ θ ν φh ωp with hPdef
  have hP : Prop51.Admissible P :=
    investParams_admissible hα0 hα1 hβ0 hβ1 hδ0 hδ1 hθ hν hφ hωp
  have hD3 : ∀ i, Prop51.D3 𝔼 P.β (Prop51.cD P ε) (Prop51.MD P ε) (kf i - K) (p i) := fun i =>
    Prop51.D3_of_firm_capital_euler 𝔼 hε.ne' ((capitalEuler_iff_eq37 𝔼 P ε _ _ _ _).2
      (hfirm i)) ((capitalEuler_iff_eq37 𝔼 P ε _ _ _ _).2 hagg) (hdem i)
  have h313 : ∀ i, Prop51.Eq313 P 𝔼 (p i) s (kf i - K) t := fun i =>
    Prop51.eq313_of_calvo 𝔼 ((calvoFOC_iff 𝔼 P _ _ t).2 (hcalvo i))
      (mc312_of_eq311 P (h311f i) h311a (hdem i))
  exact Prop51.prop51 𝔼 hP hε hD wt hp hk hka hpre hD3 hs hπ t h313 hik hip havk havp ω

/-- Woodford (2003), Prop. 5.1, p. 359 (the survey's conjecture `a − b > 0`): for the
coefficients derived from the primitives, `ω ≤ ρ_y` holds automatically (`ρ_y − ω =
ω_p/(φ_h − 1) ≥ 0`), so `a − b > 0` at every adjustment cost `ε_ψ > 0` with `αβμ₂ ≠ 1`. -/
theorem a_sub_b_pos_investmentModel {α β δ θ ν φh ωp ε : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hθ : 0 < θ) (hν : 0 < ν)
    (hφ : 1 < φh) (hωp : 0 ≤ ωp) (hε : 0 < ε)
    (hD : α * β * Prop51.mu2 β (Prop51.cD (investParams α β δ θ ν φh ωp) ε) ≠ 1) :
    0 < Prop51.aM (investParams α β δ θ ν φh ωp) ε -
      Prop51.bM (investParams α β δ θ ν φh ωp) ε := by
  refine Prop51.a_sub_b_pos (investParams_admissible hα0 hα1 hβ0 hβ1 hδ0 hδ1 hθ hν hφ hωp)
    hε hD ?_
  change InvestmentModel.omega ν φh ωp ≤ InvestmentModel.rhoY ν φh ωp
  rw [InvestmentModel.rhoY_eq_omega_add (ne_of_gt hφ)]
  have : 0 ≤ ωp / (φh - 1) := div_nonneg hωp (by linarith)
  linarith

/-! ### The investment model and the IS block (§3.3–3.4, Proposition 5.2) -/

/-- Woodford (2003), §3.1–3.3: the parameters of the IS block (`ISBlock.Par`) derived from the
primitives: `ρ_y = InvestmentModel.rhoY`, `ρ_k = InvestmentModel.rhoK`; `k` the
capital–output ratio and `σ` the expenditure elasticity of (3.9). -/
noncomputable def isPar (β δ εψ ν φh ωp k σ : ℝ) : ISBlock.Par :=
  ⟨β, δ, εψ, InvestmentModel.rhoY ν φh ωp, InvestmentModel.rhoK ν φh ωp, k, σ⟩

/-- Woodford (2003), p. 365: for the book's primitives (`0 < β < 1`, `δ > 0`, `ε_ψ > 0`,
`ν > 0`, `φ_h > 1`, `ω_p ≥ 0`, `k > 0`) the derived IS-block parameters satisfy the hypotheses of
`ISBlock.Par.roots_iff`: `ε_ψ > 0`, `c' > 0`, `a₀ > 0`. -/
theorem isPar_pos {β δ εψ ν φh ωp k σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hδ0 : 0 < δ)
    (hε : 0 < εψ) (hν : 0 < ν) (hφ : 1 < φh) (hωp : 0 ≤ ωp) (hk : 0 < k) :
    0 < (isPar β δ εψ ν φh ωp k σ).eps ∧ 0 < (isPar β δ εψ ν φh ωp k σ).cp ∧
      0 < (isPar β δ εψ ν φh ωp k σ).a0 := by
  have hρ := InvestmentModel.rhoY_gt_rhoK_pos hν hφ hωp
  have hcp : 0 < 1 - β * (1 - δ) := by nlinarith
  refine ⟨hε, hcp, ?_⟩
  change 0 < β * εψ + (1 - β * (1 - δ)) * InvestmentModel.rhoY ν φh ωp * k
  have : 0 < InvestmentModel.rhoY ν φh ωp := by linarith
  positivity

/-- Woodford (2003), (3.7), p. 356: the IS block's (3.7), with its exogenous term
`u_t = −c'ω E_t q_{t+1}`, is exactly the corrected (3.7) of `InvestmentModel` (any parameters,
any `ω`). -/
theorem capitalEuler_iff_eq37_IS (P : ISBlock.Par) (ω : ℝ) (lam Y K q : ℕ → Ω → ℝ) :
    ISBlock.CapitalEuler 𝔼 P lam Y K (fun t => -(P.cp * ω) • 𝔼.E t (q (t + 1))) ↔
      ∀ t, InvestmentModel.Linear.Eq37 𝔼 P.β P.δ P.eps P.ρy P.ρk ω lam Y K q t := by
  refine forall_congr' fun t => ?_
  unfold InvestmentModel.Linear.Eq37
  rw [funext_iff, funext_iff]
  refine forall_congr' fun u => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ISBlock.Par.cp]
  constructor <;> intro h <;> linarith

omit 𝔼 in
/-- Woodford (2003), (3.8), p. 357: if, at every date and state, `Î_t` is the exact derivative of
investment along the log deviations `(K̂_t, K̂_{t+1})` (`InvestmentModel.eq_3_8`), then the IS
block's (3.8) holds with `k = K̄/Ȳ` and the adjustment-cost `δ`. -/
theorem investEq_of_hasDerivAt (A : InvestmentModel.AdjCost) {Kbar Ybar : ℝ} (hK : Kbar ≠ 0)
    (P : ISBlock.Par) (hk : P.k = Kbar / Ybar) (hδ : P.δ = A.δ) {I K : ℕ → Ω → ℝ}
    (hI : ∀ t u, HasDerivAt (fun ε => (A.I (InvestmentModel.dev Kbar (K (t + 1) u) ε /
      InvestmentModel.dev Kbar (K t u) ε) * InvestmentModel.dev Kbar (K t u) ε - A.δ * Kbar) /
        Ybar) (I t u) 0) : ISBlock.InvestEq P I K := by
  intro t
  funext u
  have h := (hI t u).unique (InvestmentModel.eq_3_8 A hK (K t u) (K (t + 1) u))
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hk, hδ]
  exact h

omit 𝔼 in
/-- Woodford (2003), (3.9), p. 357: if, at every date and state, `λ̂_t` is the exact
log-derivative of `u_c(Y − I − G; ξ)` (`InvestmentModel.eq_3_9`) and `σ⁻¹ = −u_cc Ȳ/u_c`, then the
IS block's (3.9) holds with `g = Ĝ − u_cξ ξ̂/(Ȳ u_cc)`. -/
theorem muEq_of_hasDerivAt {uc : ℝ × ℝ → ℝ} {ucc ucx Ybar Ibar Gbar : ℝ} (hY : Ybar ≠ 0)
    (hC : Ybar - Ibar - Gbar ≠ 0) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucx • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Ibar - Gbar, 0))
    (hu0 : uc (Ybar - Ibar - Gbar, 0) ≠ 0) (P : ISBlock.Par)
    (hσ : P.σ⁻¹ = -ucc * Ybar / uc (Ybar - Ibar - Gbar, 0)) {lam Y I G xi : ℕ → Ω → ℝ}
    (hlam : ∀ t u, HasDerivAt (fun ε => Real.log (uc (InvestmentModel.dev Ybar (Y t u) ε -
      (Ibar + ε * (Ybar * I t u)) - (Gbar + ε * (Ybar * G t u)), ε * xi t u))) (lam t u) 0) :
    ISBlock.MUEq P lam Y I (fun t u => G t u - ucx * xi t u / (Ybar * ucc)) := by
  intro t
  funext u
  have h := (hlam t u).unique
    (InvestmentModel.eq_3_9 hY hC hcc huc hu0 (Y t u) (I t u) (G t u) (xi t u))
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hσ]
  rw [h]

omit 𝔼 in
/-- Woodford (2003), (3.18), p. 360: averaging (3.11) and substituting the IS block's (3.9)
gives (3.18) in the form used by `InvestmentNaturalRate` (`InvestmentModel.Linear.eq_3_18`, date
by date). -/
theorem mcEq_of_eq311 {P : ISBlock.Par} {ω ν : ℝ} {s Y I K lam g q : ℕ → Ω → ℝ}
    (h311 : ∀ t, InvestmentModel.Linear.Eq311 ω ν s Y K lam q t)
    (h39 : ISBlock.MUEq P lam Y I g) : InvestmentNaturalRate.MCEq P.σ ω ν s Y I K g q := by
  intro t
  funext u
  have e1 := congrFun (h311 t) u
  have e2 := congrFun (h39 t) u
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul] at e1 e2 ⊢
  exact InvestmentModel.Linear.eq_3_18 e1 (by rw [e2]; ring)

/-- **Woodford (2003), Proposition 5.2, (3.28)/(D.7), pp. 374, 691, for the model of §3.1–3.2.**
With the IS-block parameters derived from the primitives (`isPar`) and the disturbance
`u_t = −c'ω E_t q_{t+1}` of the corrected (3.7): given the affine natural values and (3.7) in the
flexible-price equilibrium, the corrected (3.7) of `InvestmentModel` holds at every date iff the
gaps satisfy the corrected (3.28) (`InvestmentNaturalRate.prop52`). -/
theorem prop52_investmentModel {β δ εψ ν φh ωp k σ ηl ηy ηk : ℝ}
    {lam Y K q lamn Yn Kn lamcc Ycc Kcc : ℕ → Ω → ℝ}
    (hA : InvestmentNaturalRate.NaturalAffine ηl ηy ηk lamn Yn Kn lamcc Ycc Kcc K)
    (hflex : InvestmentNaturalRate.FlexEuler 𝔼 (isPar β δ εψ ν φh ωp k σ) ηl ηy ηk lamn Kn lamcc
      Ycc Kcc K (fun t => -((isPar β δ εψ ν φh ωp k σ).cp * InvestmentModel.omega ν φh ωp) •
        𝔼.E t (q (t + 1)))) :
    (∀ t, InvestmentModel.Linear.Eq37 𝔼 β δ εψ (InvestmentModel.rhoY ν φh ωp)
      (InvestmentModel.rhoK ν φh ωp) (InvestmentModel.omega ν φh ωp) lam Y K q t) ↔
      InvestmentNaturalRate.GapEuler 𝔼 (isPar β δ εψ ν φh ωp k σ) ηl ηy ηk
        (fun t => lam t - lamn t) (fun t => Y t - Yn t) (fun t => K t - Kn t) := by
  rw [← InvestmentNaturalRate.prop52 𝔼 hA hflex]
  exact (capitalEuler_iff_eq37_IS 𝔼 (isPar β δ εψ ν φh ωp k σ) _ lam Y K q).symm

/-! ### The (3.17) coefficients in the system (3.36) -/

/-- Woodford (2003), (3.36), p. 376: the third block of the equilibrium conditions (3.36) at
every date is exactly (3.17) of `InvestmentLimits` (`Solves317`) for real marginal cost
`ŝ = m_Y X − m_I J` (3.27). -/
theorem sys36_row2_iff_solves317 (S : InvestmentNaturalRate.Sys36) (X J Pv : ℕ → Ω → ℝ) :
    (∀ t, Pv t = S.ξ0 • InvestmentNaturalRate.S36 S X J t -
        S.ξ1 • 𝔼.E t (InvestmentNaturalRate.S36 S X J (t + 1)) + S.ψ1 • 𝔼.E t (Pv (t + 1)) -
        S.ψ2 • 𝔼.E t (Pv (t + 2))) ↔
      InvestmentLimits.Solves317 𝔼 S.ξ0 S.ξ1 S.ψ1 S.ψ2 (InvestmentNaturalRate.S36 S X J) Pv :=
  Iff.rfl

/-- Woodford (2003), (3.14)–(3.17) and (3.36), pp. 359–376: when the (3.17) coefficients of the
system (3.36) are those of `InvestmentLimits` (`ξ₀ = xi0`, `ξ₁ = xi1`, `ψ₁ = psi1`, `ψ₂ = psi2`
built from `a`, `b`, `μ₂` of Proposition 5.1), its third block holds at every date iff
Proposition 5.1's aggregate relation (3.14) holds at every date (`eq314_iff_eq317`), for bounded
adapted `ŝ` and `p̂*` with `π = ((1 − α)/α) p̂*`. -/
theorem sys36_row2_iff_eq314 {α β a b μ₂ Bs Bp : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hab : a - b ≠ 0) (hμ : 1 < μ₂) (S : InvestmentNaturalRate.Sys36)
    (h0 : S.ξ0 = InvestmentLimits.xi0 α a b) (h1 : S.ξ1 = InvestmentLimits.xi1 α a b μ₂)
    (h2 : S.ψ1 = InvestmentLimits.psi1 α β a b μ₂) (h3 : S.ψ2 = InvestmentLimits.psi2 β μ₂)
    {X J Pv pstar : ℕ → Ω → ℝ} (hs : ∀ τ ω, |InvestmentNaturalRate.S36 S X J τ ω| ≤ Bs)
    (hsa : 𝔼.Adapted (InvestmentNaturalRate.S36 S X J)) (hp : ∀ τ ω, |pstar τ ω| ≤ Bp)
    (hpa : 𝔼.Adapted pstar) (hπp : ∀ τ, Pv τ = ((1 - α) / α) • pstar τ) :
    (∀ t, (a - b) • pstar t =
        InvestmentLimits.rhs314 𝔼 a b (α * β) μ₂⁻¹ (InvestmentNaturalRate.S36 S X J) Pv t) ↔
      ∀ t, Pv t = S.ξ0 • InvestmentNaturalRate.S36 S X J t -
        S.ξ1 • 𝔼.E t (InvestmentNaturalRate.S36 S X J (t + 1)) + S.ψ1 • 𝔼.E t (Pv (t + 1)) -
        S.ψ2 • 𝔼.E t (Pv (t + 2)) := by
  rw [sys36_row2_iff_solves317, h0, h1, h2, h3]
  exact InvestmentLimits.eq314_iff_eq317 𝔼 hα0 hα1 hβ0 hβ1 hab hμ hs hsa hp hpa hπp

omit 𝔼 in
/-- Woodford (2003), (3.27), p. 374, and (3.36): with the (3.27) weights `m_Y = ω + σ⁻¹`,
`m_I = σ⁻¹`, real marginal cost is the `ŝ` of the system (3.36) evaluated at the gaps. -/
theorem eq327_S36 {σ ω ν : ℝ} (S : InvestmentNaturalRate.Sys36) (hY : S.mY = ω + σ⁻¹)
    (hI : S.mI = σ⁻¹) {s Y I Yn In K g q : ℕ → Ω → ℝ}
    (h : InvestmentNaturalRate.MCEq σ ω ν s Y I K g q)
    (hn : InvestmentNaturalRate.MCEq σ ω ν 0 Yn In K g q) (t : ℕ) :
    s t = InvestmentNaturalRate.S36 S (fun τ => Y τ - Yn τ) (fun τ => I τ - In τ) t := by
  rw [InvestmentNaturalRate.eq327 h hn t, InvestmentNaturalRate.S36, hY, hI]

/-! ### Habit persistence and (2.4) -/

/-- Woodford (2003), p. 333 and (2.4), p. 348: the habit-adjusted gap of `SmallModels` (with the
truncated lag) agrees with that of `Habit` (with the initial value `x_{−1}`) at every date
`s ≥ 1`. -/
theorem xTilde_eq_habit (β η : ℝ) (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) :
    SmallModels.xTilde 𝔼 β η x (t + 1) = Habit.xTilde 𝔼 β η xm1 x (t + 1) := by
  simp only [SmallModels.xTilde, Habit.xTilde, Habit.lag_succ, Nat.add_sub_cancel]

/-- **Woodford (2003), (2.4), p. 348, from the habit model of §1.2.** The hypothesis of
`SmallModels.eq24` (the habit analogue of (1.6)) holds whenever the log marginal utility of
income has the form derived in `Habit` (`Habit.lamOf_hasDerivAt`, `Habit.uhC_eq`):
`λ̂_s = −φ x̃_s + ζ_s` with exogenous `ζ`; then `z = φ⁻¹ ζ` and, with the natural rate
`r̂ⁿ_s = φ E_s(z_s − z_{s+1})`, the forecastable IS relation (2.4) holds. -/
theorem eq24_of_habit {φ β η : ℝ} (hφ : φ ≠ 0) {xm1 : Ω → ℝ} {x i infl lam rn ζ : ℕ → Ω → ℝ}
    (hlam : Predetermined.LamEq 𝔼 i infl lam)
    (hhab : ∀ s, lam s = -φ • Habit.xTilde 𝔼 β η xm1 x s + ζ s)
    (hrn : ∀ s, rn s = φ • 𝔼.E s (φ⁻¹ • ζ s - φ⁻¹ • ζ (s + 1))) (t : ℕ) :
    𝔼.E t (SmallModels.xTilde 𝔼 β η x (t + 2)) = 𝔼.E t (SmallModels.xTilde 𝔼 β η x (t + 3)) -
      φ⁻¹ • 𝔼.E t (i (t + 2) - infl (t + 3) - rn (t + 2)) := by
  refine SmallModels.eq24 𝔼 hφ (z := fun s => φ⁻¹ • ζ s) hlam (fun t => ?_) hrn t
  rw [hhab (t + 2), xTilde_eq_habit 𝔼 β η xm1 x (t + 1), show t + 1 + 1 = t + 2 from rfl]
  simp only [map_add, map_sub, map_smul]
  funext u
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-! ### The Calvo derivation and the Chapter 3 AS relation used by `Habit` -/

/-- Woodford (2003), (1.26), p. 334, and (1.20), p. 330 (with no price lag, `s = 0`): the
Chapter 3 aggregate-supply relation that `Habit.ASch3` takes as given follows from the
recursive Calvo condition and the price index (`Predetermined.delayed_calvo`) when real marginal
cost enters as `c = A⁻¹(ω x − (λ̂ − λ̂ⁿ))` with `x` and the gap `λ̂ − λ̂ⁿ` adapted, with
`ξ_p = ξ/A`, `ξ = (1 − α)(1 − αβ)/α`. -/
theorem asch3_of_calvo {α β ω A : ℝ} (hα : α ≠ 0) {q infl c x lamgap : ℕ → Ω → ℝ}
    (hrec : Predetermined.CalvoRec 𝔼 α β q infl c) (hidx : Predetermined.IndexLawLag 𝔼 α 0 q infl)
    (hc : ∀ r, c r = A⁻¹ • (ω • x r - lamgap r)) (hx : 𝔼.Adapted x) (hl : 𝔼.Adapted lamgap) :
    Habit.ASch3 𝔼 (Predetermined.calvoXi α β / A) ω β lamgap x infl := by
  intro t
  have h := Predetermined.delayed_calvo 𝔼 hα hrec hidx t
  simp only [add_zero] at h
  rw [h, hc t, map_smul, map_sub, map_smul, hx t, hl t, smul_smul]
  congr 2

/-! ### The habit root and the `(D.2)` polynomial family -/

/-- Woodford (2003), (1.28), p. 335, and (D.2), p. 688: for `η > 0` the habit root `δ` of
`ηφ(1 + βδ²) = Bδ` is the smaller root `μ₁` of `P(μ) = βμ² − (1 + β + c)μ + 1` of Appendix D
with `c = B/(ηφ) − 1 − β = [ω + φ(1 − η)(1 − βη)]/(ηφ)`, which is positive whenever `ω > 0`
(so the two root theories are one theory up to parameters). -/
theorem habDelta_eq_mu1 {β ω vphi η : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hω : 0 < ω)
    (hφ : 0 < vphi) (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < Habit.habB β ω vphi η / (η * vphi) - 1 - β ∧
      Habit.habDelta β ω vphi η = Prop51.mu1 β (Habit.habB β ω vphi η / (η * vphi) - 1 - β) := by
  set c := Habit.habB β ω vphi η / (η * vphi) - 1 - β with hc
  have hηφ : 0 < η * vphi := mul_pos hη hφ
  have hcpos : 0 < c := by
    rw [hc, Habit.habB, sub_sub, sub_pos, lt_div_iff₀ hηφ]
    have hβη : β * η ≤ 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hη1) (sub_nonneg.2 hβη), mul_pos hφ hη]
  refine ⟨hcpos, ?_⟩
  -- both are roots of `P` lying below `1`; `μ₂ > 1` is the other root
  have hroot := Habit.habDelta_root hβ0.le hω.le hφ (η := η)
  have hP : Prop51.Ppoly β c (Habit.habDelta β ω vphi η) = 0 := by
    unfold Prop51.Ppoly
    rw [hc]
    field_simp
    linear_combination hroot
  have hle := Habit.habDelta_le hβ0.le hω.le hφ hη.le
  rw [Prop51.Ppoly_factor hβ0 hcpos] at hP
  have h2 := Prop51.one_lt_mu2 hβ0 hβ1 hcpos
  rcases mul_eq_zero.mp hP with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h hβ0.ne'
    · linarith
  · linarith

end Woodford.PolicyResponseDynamics.Links
