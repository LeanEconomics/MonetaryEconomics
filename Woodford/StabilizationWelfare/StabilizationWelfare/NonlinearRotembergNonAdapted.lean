/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyAEIFT

/-!
# Uniqueness of the a.s. Rotemberg Ramsey equilibrium among NON-adapted processes

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 and Appendix A.3, for the exact
Rotemberg Ramsey conditions; the argument of `NonlinearNKMarkovRamseyNonAdapted` (Calvo).

`NonlinearRotembergRamseyAEIFT.ramsey_existence_ae` proves a.s. uniqueness among ADAPTED, a.s.
bounded processes. Here the restriction is removed: every solution within `r` (not assumed
adapted, nor measurable) with an `𝓕₀`-measurable predetermined initial value is adapted, hence
equal to the adapted solution.

* `DQcur`; **`DQcur_injective`**: the derivative of the current-date conditions in the current
  variables is invertible when `G > 0` (`ĉ = ŷ`, the NKPC `ψπ = θm(σ+ω)ŷ`, `λ̂ = γ̄π`, and the
  combined condition `(G + θm(σ+ω)γ̄κ)ŷ = 0`).
* **`ramsey_solution_adapted`**: by induction on the date, a contraction in the current
  variables whose iterates from `0` are `𝓕_t`-measurable and converge to `z_t`.
* **`ramsey_unique_all`**: existence and a.s. uniqueness among ALL a.s. bounded processes.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergNonAdapted

open MeasureTheory Filter Topology
open NonlinearNKMarkovAE (MvA Bd)
open NonlinearNKMarkovAEAdapted (AdA aesmSub_lim adA_MvA)
open NonlinearNKMarkovRamseyIFT (remainder_gen)
open ExpectationsMeasure
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyAE (gamb_pos)
open NonlinearRotembergRamseyAEIFT (lagIA PhiRA adV_mono ramsey_existence_ae)

/-- Woodford (2003), Ch. 7: the derivative of the current-date Rotemberg Ramsey conditions in
the current-date variables (zero lag), as a linear map. -/
noncomputable def DQcur (p : Par) : (Fin 5 → ℝ) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun u := DQr p 0 u
  map_add' u u' := by funext i; fin_cases i <;> simp [DQr] <;> ring
  map_smul' c u := by funext i; fin_cases i <;> simp [DQr] <;> ring

/-- Woodford (2003), Ch. 7 (**the current-date block is invertible**): if `G > 0`, the
derivative of the current-date Rotemberg Ramsey conditions in the current variables is
injective. -/
theorem DQcur_injective {p : Par} (hp : p.Basic) (hG : 0 < Gw p) :
    Function.Injective (DQcur p) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h : DQr p 0 u = 0 := hu
  have hr : ∀ i, DQr p 0 u i = 0 := fun i => by rw [h]; rfl
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hk := hp.κ_mul
  have hκ := hp.κ_pos
  have h4 := hr 4
  have h3 := hr 3
  have h1 := hr 1
  have h02 := red_lam hp 0 u
  rw [hr 0, hr 2] at h02
  simp only [DQr, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero,
    Pi.zero_apply, sub_zero] at h4 h3 h1
  have hu2 : u 2 = u 0 := by linarith
  have hu1 : u 1 = p.κ * u 0 := by
    have : p.ψ * (u 1 - p.κ * u 0) = 0 := by
      linear_combination h3 + (p.θ * p.m * p.σ) * hu2 - u 0 * hk
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hψ.ne')
  have hu3 : u 3 = gamb p * u 1 := by
    have : p.ψ * (u 3 - gamb p * u 1) = 0 := by linear_combination h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hψ.ne')
  have hpos : 0 < Gw p + p.θ * p.m * (p.σ + p.ω) * gamb p * p.κ := by
    have : 0 < p.θ * p.m * (p.σ + p.ω) := by rw [← hk]; positivity
    positivity
  have hu0 : u 0 = 0 := by
    have : (Gw p + p.θ * p.m * (p.σ + p.ω) * gamb p * p.κ) * u 0 = 0 := by
      rw [hu2, hu3, hu1, sub_self, mul_zero, add_zero] at h02
      linear_combination h02
    exact (mul_eq_zero.1 this).resolve_left hpos.ne'
  have h2 := hr 2
  simp only [DQr, Matrix.cons_val] at h2
  rw [hu2, hu0, hu3, hu1, hu0] at h2
  have hu4 : u 4 = 0 := by linarith
  funext i
  fin_cases i
  · exact hu0
  · simp [hu1, hu0]
  · simp [hu2, hu0]
  · simp [hu3, hu1, hu0]
  · exact hu4

/-- Woodford (2003), Ch. 7 and App. A.3 (**every a.s. bounded solution is adapted**): if
`G > 0`, there are `r, δ > 0` such that on every filtered probability space, for adapted
disturbances and an `𝓕₀`-measurable initial value with `‖e_t‖, ‖d‖ ≤ δ` a.s., every process
`z` (NOT assumed adapted, nor even a.s. measurable) with `‖z_t‖ ≤ r` a.s. that solves the exact
Ramsey conditions a.s. at every date is adapted. -/
theorem ramsey_solution_adapted {p : Par} (hp : p.Basic) (hG : 0 < Gw p) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 3 → ℝ) (d : Ω → Fin 5 → ℝ), AdA E e → Bd E e δ →
        AEStronglyMeasurable[E.𝓕 0] d E.μ → (∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δ) →
        ∀ z : ℕ → Ω → Fin 5 → ℝ, Bd E z r →
          (∀ t, PhiRA E p e d z t =ᵐ[E.μ] 0) → AdA E z := by
  set D := LinearEquiv.ofInjectiveEndo (DQcur p) (DQcur_injective hp hG) with hD
  set Di := LinearMap.toContinuousLinearMap D.symm.toLinearMap with hDi
  set N := ‖Di‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set η := 1 / (2 * (N + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρ, hρ, hQ⟩ := remainder_gen (contDiff_Qd (n := 1) p) hη0
  -- the pointwise contraction
  have hDi : ∀ v, Di (DQr p 0 v) = v := fun v => by
    change D.symm (DQcur p v) = v
    have : DQcur p v = D v := rfl
    rw [this, LinearEquiv.symm_apply_apply]
  have hcon : ∀ (x : Fin 3 → ℝ) (y w c a : Fin 5 → ℝ), ‖x‖ ≤ ρ → ‖y‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖a‖ ≤ ρ → Qd p (x, y, w) + c = 0 →
        ‖(a - Di (Qd p (x, y, a) + c)) - w‖ ≤ ‖a - w‖ / 2 := by
    intro x y w c a hx hy hw ha hc
    have hq := hQ x (y, a) (y, w) hx (by rw [Prod.norm_def]; exact max_le hy ha)
      (by rw [Prod.norm_def]; exact max_le hy hw)
    rw [Prod.mk_sub_mk, sub_self, show fderiv ℝ (Qd p) ((0 : Fin 3 → ℝ),
      (0 : (Fin 5 → ℝ) × (Fin 5 → ℝ))) = fderiv ℝ (Qd p) 0 from rfl, fderiv_Qd,
      Prod.norm_def, norm_zero] at hq
    have hmax : max 0 ‖a - w‖ = ‖a - w‖ := max_eq_right (norm_nonneg _)
    rw [hmax] at hq
    have e1 : (a - Di (Qd p (x, y, a) + c)) - w =
        -Di (Qd p (x, y, a) - Qd p (x, y, w) - DQr p 0 (a - w)) := by
      have hcw : c = -Qd p (x, y, w) := by linear_combination hc
      rw [map_sub, map_sub, hDi, hcw]
      rw [map_add, map_neg]
      abel
    rw [e1, norm_neg]
    calc _ ≤ N * (η * ‖a - w‖) := (Di.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left hq hN0)
      _ ≤ ‖a - w‖ / 2 := by
          have hNe : N * η ≤ 1 / 2 := by
            rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
          have h1 := mul_le_mul_of_nonneg_right hNe (norm_nonneg (a - w))
          have e : N * (η * ‖a - w‖) = N * η * ‖a - w‖ := by ring
          rw [e]; linarith
  refine ⟨ρ / 2, by positivity, ρ / 2, by positivity,
    fun Ω _ E e d he heb hd hdb z hzb hz => ?_⟩
  set c : ℕ → Ω → Fin 5 → ℝ := MvA E (fun s ω' => Nd p (z s ω')) with hc
  have hcA : AdA E c := adA_MvA E _
  set F : (Fin 3 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) → (Fin 5 → ℝ) :=
    fun q => q.2.2.1 - Di (Qd p (q.1, q.2.1, q.2.2.1) + q.2.2.2) with hFdef
  have hF : Continuous F := by
    have hQc := (contDiff_Qd (n := 0) p).continuous
    exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).sub (Di.continuous.comp
      ((hQc.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd))))).add
          (continuous_snd.comp (continuous_snd.comp continuous_snd))))
  have step : ∀ t, AEStronglyMeasurable[E.𝓕 t] (lagIA z d t) E.μ →
      (∀ᵐ ω ∂E.μ, ‖lagIA z d t ω‖ ≤ ρ) → AEStronglyMeasurable[E.𝓕 t] (z t) E.μ := by
    intro t hlag hlagB
    set it : ℕ → Ω → Fin 5 → ℝ := fun k ω =>
      (fun a => F (e t ω, lagIA z d t ω, a, c t ω))^[k] 0 with hit
    have hm : ∀ k, AEStronglyMeasurable[E.𝓕 t] (it k) E.μ := by
      intro k
      induction k with
      | zero => exact aestronglyMeasurable_const
      | succ k ihk =>
        have e1 : it (k + 1) = fun ω => F (e t ω, lagIA z d t ω, it k ω, c t ω) := by
          funext ω; simp only [hit, Function.iterate_succ_apply']
        rw [e1]
        exact hF.comp_aestronglyMeasurable ((he t).prodMk (hlag.prodMk (ihk.prodMk (hcA t))))
    refine aesmSub_lim hm ?_
    filter_upwards [heb t, hlagB, hzb t, hz t] with ω h1 h2 h3 h4
    have hc0 : Qd p (e t ω, lagIA z d t ω, z t ω) + c t ω = 0 := by
      simpa [PhiRA, hc] using h4
    have hk : ∀ k, ‖it k ω - z t ω‖ ≤ ρ / 2 / 2 ^ k := by
      intro k
      induction k with
      | zero => simpa [hit] using h3
      | succ k ihk =>
        have ha : ‖it k ω‖ ≤ ρ := by
          have : ρ / 2 / 2 ^ k ≤ ρ / 2 := div_le_self (by positivity) (one_le_pow₀ (by norm_num))
          have h5 : ‖it k ω‖ ≤ ‖it k ω - z t ω‖ + ‖z t ω‖ := by
            have := norm_add_le (it k ω - z t ω) (z t ω); simpa using this
          linarith
        have e1 : it (k + 1) ω = F (e t ω, lagIA z d t ω, it k ω, c t ω) := by
          simp only [hit, Function.iterate_succ_apply']
        rw [e1]
        have := hcon (e t ω) (lagIA z d t ω) (z t ω) (c t ω) (it k ω) (h1.trans (by linarith))
          h2 (h3.trans (by linarith)) ha hc0
        calc _ ≤ ‖it k ω - z t ω‖ / 2 := this
          _ ≤ ρ / 2 / 2 ^ k / 2 := by linarith
          _ = ρ / 2 / 2 ^ (k + 1) := by rw [pow_succ]; ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hg : Tendsto (fun k : ℕ => ρ / 2 / 2 ^ k) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (ρ / 2)
      simp only [mul_zero] at this
      refine this.congr fun k => ?_
      rw [one_div, inv_pow]; field_simp
    exact squeeze_zero (fun _ => norm_nonneg _) hk hg
  intro t
  induction t with
  | zero =>
    refine step 0 hd ?_
    filter_upwards [hdb] with ω h; exact h.trans (by linarith)
  | succ t ih =>
    refine step (t + 1) (adV_mono E (Nat.le_succ t) ih) ?_
    filter_upwards [hzb t] with ω h; exact h.trans (by linarith)

/-- Woodford (2003), Ch. 7 and App. A.3 (**the uniqueness class is ALL a.s. bounded processes**):
if `G > 0`, there are `0 < r′ ≤ r` and `δ > 0` such that on every filtered probability space,
for adapted `e` and `𝓕₀`-measurable `d` with `‖e_t‖, ‖d‖ ≤ δ` a.s., the exact Ramsey conditions
have an adapted solution with `‖z_t‖ ≤ r` a.s., and EVERY process `z′` with `‖z′_t‖ ≤ r′` a.s.
solving them a.s. (adapted or not, measurable or not) is a.s. equal to it at every date. -/
theorem ramsey_unique_all {p : Par} (hp : p.Basic) (hG : 0 < Gw p) :
    ∃ r > 0, ∃ r' > 0, r' ≤ r ∧ ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (e : ℕ → Ω → Fin 3 → ℝ) (d : Ω → Fin 5 → ℝ), AdA E e →
        Bd E e δ → AEStronglyMeasurable[E.𝓕 0] d E.μ → (∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δ) →
        ∃ z : ℕ → Ω → Fin 5 → ℝ, (AdA E z ∧ Bd E z r ∧ ∀ t, PhiRA E p e d z t =ᵐ[E.μ] 0) ∧
          ∀ z' : ℕ → Ω → Fin 5 → ℝ, Bd E z' r' → (∀ t, PhiRA E p e d z' t =ᵐ[E.μ] 0) →
            ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨ra, hra, δa, hδa, hae⟩ := ramsey_existence_ae hp hG
  obtain ⟨rn, hrn, δn, hδn, hna⟩ := ramsey_solution_adapted hp hG
  refine ⟨ra, hra, min ra rn, lt_min hra hrn, min_le_left _ _, min δa δn, lt_min hδa hδn,
    fun Ω _ E e d he heb hd hdb => ?_⟩
  have heba : Bd E e δa := fun t => by
    filter_upwards [heb t] with ω h; exact h.trans (min_le_left _ _)
  have hebn : Bd E e δn := fun t => by
    filter_upwards [heb t] with ω h; exact h.trans (min_le_right _ _)
  have hdba : ∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δa := by
    filter_upwards [hdb] with ω h; exact h.trans (min_le_left _ _)
  have hdbn : ∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δn := by
    filter_upwards [hdb] with ω h; exact h.trans (min_le_right _ _)
  obtain ⟨z, hz, hu⟩ := hae Ω E e d he heba hd hdba
  refine ⟨z, hz, fun z' hz'B hz'E => ?_⟩
  have hz'A := hna Ω E e d he hebn hd hdbn z' (fun t => by
    filter_upwards [hz'B t] with ω h; exact h.trans (min_le_right _ _)) hz'E
  exact hu z' hz'A (fun t => by filter_upwards [hz'B t] with ω h; exact h.trans (min_le_left _ _))
    hz'E

end Woodford.StabilizationWelfare.NonlinearRotembergNonAdapted
