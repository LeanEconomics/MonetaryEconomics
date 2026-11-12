/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovRamseyAEIFT

/-!
# Uniqueness of the a.s. Ramsey equilibrium among NON-adapted processes

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 and Appendix A.3.

`NonlinearNKMarkovRamseyAEIFT.ramsey_existence_ae` proves a.s. uniqueness of the timeless Ramsey
equilibrium among ADAPTED, a.s. bounded processes. Here the restriction is removed: every a.s.
measurable, a.s. bounded solution within `r` (not assumed adapted) with an `𝓕₀`-measurable
predetermined initial value is automatically adapted, hence equal to the adapted solution. So
the uniqueness class is ALL a.s. measurable, essentially bounded processes; no counterexample
exists.

* `DQcur`: the derivative of the current-date conditions in the current variables;
  **`DQcur_injective`**: it is invertible whenever `A_uG ≠ 0` (from the reduction of
  `NonlinearNKMarkovRamseyLin`: `Δ̂ = 0`, `μ = 0`, the NKPC `π = κŷ`, the targeting rule
  `ŷ + θπ = 0`, so `(1 + κθ)ŷ = 0`, and the rest follows).
* **`ramsey_solution_adapted`**: induction on the date. Given the past, `z_t` solves
  `Q(e_t, z_{t−1}, z_t) = −E_t N(z_{t+1})` with known right side; on the small ball the map
  `u ↦ u − DQcur⁻¹(Q(e_t, z_{t−1}, u) + E_t N)` is a contraction whose iterates from `0` are
  `𝓕_t`-measurable and converge to `z_t`.
* **`ramsey_unique_all`**: existence and a.s. uniqueness among all a.s. measurable bounded
  processes.
* **`taylor_solution_adapted`**: the same record for the Taylor-rule equilibrium, where
  `NonlinearNKMarkovAE.seq_uniqueness_ae` already holds among all a.s. measurable bounded
  processes: every such solution within `r` is adapted.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyNonAdapted

open MeasureTheory Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree ExpectationsMeasure NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted
open NonlinearNKMarkovRamseyAE NonlinearNKMarkovRamseyIFT NonlinearNKMarkovRamseyAEIFT

/-- Woodford (2003), §5: the derivative of the current-date Ramsey conditions in the
current-date variables, as a linear map. -/
noncomputable def DQcur (p : Par) (R : RPar) : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ) where
  toFun u := DQr p R 0 u
  map_add' u u' := by funext i; fin_cases i <;> simp [DQr] <;> ring
  map_smul' c u := by funext i; fin_cases i <;> simp [DQr] <;> ring

/-- Woodford (2003), Ch. 7 (**the current-date block is invertible**): if `A_uG ≠ 0`, the
derivative of the current-date conditions in the current variables is injective. -/
theorem DQcur_injective {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    Function.Injective (DQcur p R) := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hκθ : 0 < 1 + p.κ * p.θ := by
    have := mul_pos hp.κ_pos (by linarith [hp.one_lt_θ] : 0 < p.θ); linarith
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h : DQr p R 0 u + DNr p R 0 = 0 := by
    have : DNr p R 0 = 0 := by funext i; fin_cases i <;> simp [DNr]
    rw [this, add_zero]; exact hu
  have hr : ∀ i, (DQr p R 0 u + DNr p R 0) i = 0 := fun i => by rw [h]; rfl
  have hD := red_D R hp 0 u 0
  have hμ := red_mu R hp 0 u 0
  have hpc := red_pc R hp 0 u 0
  have ht := red_target R hp 0 u 0 0 (by simp)
  have h0 := red_l1 R hp 0 u 0
  simp only [hr, Pi.zero_apply, mul_zero, add_zero, zero_div, sub_self] at hD hμ hpc
  simp only [hr, Pi.zero_apply, mul_zero, add_zero, sub_zero, sub_self] at ht h0
  rw [hD, hμ] at ht
  simp only [mul_zero, sub_zero] at ht
  have hy : R.Au * Gw p R * (u 0 + p.θ * u 1) = 0 := by linear_combination ht
  have hy' : u 0 + p.θ * u 1 = 0 := (mul_eq_zero.1 hy).resolve_left hG
  rw [hpc] at hy'
  have hu0 : u 0 = 0 := by
    have : (1 + p.κ * p.θ) * u 0 = 0 := by linear_combination hy'
    exact (mul_eq_zero.1 this).resolve_left hκθ.ne'
  have hu1 : u 1 = 0 := by rw [hpc, hu0]; ring
  have h5 := hr 5
  have h6 := hr 6
  have h7 := hr 7
  have h4 := hr 4
  have h2 := hr 2
  simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, Pi.zero_apply] at h5 h6 h4
  rw [hu0] at h5 h6 h4
  have hu2 : u 2 = 0 := by linarith
  have hu3 : u 3 = 0 := by linarith
  have hu8 : u 8 = 0 := by linarith
  rw [hu0, hD, hμ] at h0
  have hu5 : u 5 = 0 := by
    have : (1 - p.α * p.β) * (p.σ + p.ω) * u 5 = 0 := by linear_combination h0
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero hab hωσ)
  have hu6 : u 6 = 0 := by linarith
  simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, Pi.zero_apply, hu1, hu2, hu3, hu5,
    hu8] at h2
  have hu7 : u 7 = 0 := by
    have : (1 - p.α) * ((p.θ - 1) / p.c0) * u 7 = 0 := by linear_combination h2
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero h1α (div_ne_zero hθ hc0))
  funext i
  fin_cases i
  exacts [hu0, hu1, hu2, hu3, hD, hu5, hu6, hu7, hu8]

/-- Woodford (2003), Ch. 7 and App. A.3 (**every a.s. bounded solution is adapted**): if
`A_uG ≠ 0`, there are `r, δ > 0` such that on every filtered probability space, for adapted
disturbances and an `𝓕₀`-measurable initial value with `‖e_t‖, ‖d‖ ≤ δ` a.s., every process
`z` (NOT assumed adapted, nor even a.s. measurable) with `‖z_t‖ ≤ r` a.s. that solves the exact
Ramsey conditions a.s. at every date is adapted. -/
theorem ramsey_solution_adapted {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 5 → ℝ) (d : Ω → Fin 9 → ℝ), AdA E e → Bd E e δ →
        AEStronglyMeasurable[E.𝓕 0] d E.μ → (∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δ) →
        ∀ z : ℕ → Ω → Fin 9 → ℝ, Bd E z r →
          (∀ t, PhiRA E p R e d z t =ᵐ[E.μ] 0) → AdA E z := by
  set D := LinearEquiv.ofInjectiveEndo (DQcur p R) (DQcur_injective R hp hG) with hD
  set Di := LinearMap.toContinuousLinearMap D.symm.toLinearMap with hDi
  set N := ‖Di‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set η := 1 / (2 * (N + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρ, hρ, hQ⟩ := remainder_gen (contDiff_Qd (n := 1) p R) hη0
  -- the pointwise contraction
  have hDi : ∀ v, Di (DQr p R 0 v) = v := fun v => by
    change D.symm (DQcur p R v) = v
    have : DQcur p R v = D v := rfl
    rw [this, LinearEquiv.symm_apply_apply]
  have hcon : ∀ (x : Fin 5 → ℝ) (y w c a : Fin 9 → ℝ), ‖x‖ ≤ ρ → ‖y‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖a‖ ≤ ρ → Qd p R (x, y, w) + c = 0 →
        ‖(a - Di (Qd p R (x, y, a) + c)) - w‖ ≤ ‖a - w‖ / 2 := by
    intro x y w c a hx hy hw ha hc
    have hq := hQ x (y, a) (y, w) hx (by rw [Prod.norm_def]; exact max_le hy ha)
      (by rw [Prod.norm_def]; exact max_le hy hw)
    rw [Prod.mk_sub_mk, sub_self, show fderiv ℝ (Qd p R) ((0 : Fin 5 → ℝ),
      (0 : (Fin 9 → ℝ) × (Fin 9 → ℝ))) = fderiv ℝ (Qd p R) 0 from rfl, fderiv_Qd R hp,
      Prod.norm_def, norm_zero] at hq
    have hmax : max 0 ‖a - w‖ = ‖a - w‖ := max_eq_right (norm_nonneg _)
    rw [hmax] at hq
    have e1 : (a - Di (Qd p R (x, y, a) + c)) - w =
        -Di (Qd p R (x, y, a) - Qd p R (x, y, w) - DQr p R 0 (a - w)) := by
      have hcw : c = -Qd p R (x, y, w) := by linear_combination hc
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
  set c : ℕ → Ω → Fin 9 → ℝ := MvA E (fun s ω' => Nd p R (z s ω')) with hc
  have hcA : AdA E c := adA_MvA E _
  set F : (Fin 5 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) → (Fin 9 → ℝ) :=
    fun q => q.2.2.1 - Di (Qd p R (q.1, q.2.1, q.2.2.1) + q.2.2.2) with hFdef
  have hF : Continuous F := by
    have hQc := (contDiff_Qd (n := 0) p R).continuous
    exact (continuous_fst.comp (continuous_snd.comp continuous_snd)).sub (Di.continuous.comp
      ((hQc.comp (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd))))).add
          (continuous_snd.comp (continuous_snd.comp continuous_snd))))
  have step : ∀ t, AEStronglyMeasurable[E.𝓕 t] (lagIA z d t) E.μ →
      (∀ᵐ ω ∂E.μ, ‖lagIA z d t ω‖ ≤ ρ) → AEStronglyMeasurable[E.𝓕 t] (z t) E.μ := by
    intro t hlag hlagB
    set it : ℕ → Ω → Fin 9 → ℝ := fun k ω =>
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
    have hc0 : Qd p R (e t ω, lagIA z d t ω, z t ω) + c t ω = 0 := by
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
if `A_uG ≠ 0`, there are `0 < r′ ≤ r` and `δ > 0` such that on every filtered probability space,
for adapted `e` and `𝓕₀`-measurable `d` with `‖e_t‖, ‖d‖ ≤ δ` a.s., the exact Ramsey conditions
have an adapted solution with `‖z_t‖ ≤ r` a.s., and EVERY process `z′` with `‖z′_t‖ ≤ r′` a.s.
solving them a.s. (adapted or not, measurable or not) is a.s. equal to it at every date. -/
theorem ramsey_unique_all {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ r' > 0, r' ≤ r ∧ ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (e : ℕ → Ω → Fin 5 → ℝ) (d : Ω → Fin 9 → ℝ), AdA E e →
        Bd E e δ → AEStronglyMeasurable[E.𝓕 0] d E.μ → (∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δ) →
        ∃ z : ℕ → Ω → Fin 9 → ℝ, (AdA E z ∧ Bd E z r ∧ ∀ t, PhiRA E p R e d z t =ᵐ[E.μ] 0) ∧
          ∀ z' : ℕ → Ω → Fin 9 → ℝ, Bd E z' r' → (∀ t, PhiRA E p R e d z' t =ᵐ[E.μ] 0) →
            ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨ra, hra, δa, hδa, hae⟩ := ramsey_existence_ae R hp hG
  obtain ⟨rn, hrn, δn, hδn, hna⟩ := ramsey_solution_adapted R hp hG
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

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**the Taylor-rule record**): under the
Taylor principle there are `r, δ > 0` such that on every filtered probability space, for adapted,
a.s. measurable disturbances with `‖e_t‖ ≤ δ` a.s., every a.s. measurable solution with
`‖z_t‖ ≤ r` a.s. of the exact stochastic conditions (not assumed adapted) is adapted: there
`NonlinearNKMarkovAE.seq_uniqueness_ae` already holds among ALL a.s. measurable bounded
processes, and the solution is adapted (`seq_existence_ae_adapted`). -/
theorem taylor_solution_adapted {p : Par} (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 5 → ℝ), Gd E e → Bd E e δ → AdA E e →
        ∀ z' : ℕ → Ω → Fin 4 → ℝ, Gd E z' → Bd E z' r → SeqEqmAE E p e z' → AdA E z' := by
  obtain ⟨r, hr, δ, hδ, h⟩ := seq_existence_ae_adapted hp
  refine ⟨r, hr, δ, hδ, fun Ω _ E e he heb heA z' hz'G hz'B hz' t => ?_⟩
  obtain ⟨z, ⟨-, hzA⟩, hu⟩ := h Ω E e he heb heA
  exact (hzA t).congr (hu z' hz'G hz'B hz' t).symm

end Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyNonAdapted
