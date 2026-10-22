/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergAE
import StabilizationWelfare.NonlinearNKMarkovAR1Markov

/-!
# The Markov representation `z_t = g(x_t)` of the Rotemberg equilibrium, any bounded AR(1) law

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392: the equilibrium as a
time-invariant function of the exogenous state) and Appendix A.3 (pp. 631–635), for the exact
Rotemberg model of `NonlinearRotemberg`.

The route of `NonlinearNKMarkovAR1Markov` (Calvo), reused by import: the Markov equilibrium is
built on the bounded state interval with the Hahn–Banach AR(1) transition operator
(`NonlinearNKMarkovAR1Markov.arOp`), it is MEASURABLE because bounded measurability passes through
the inverse and the residual (`bm_linSol`, `bm_PhiG`, `markov_existence_meas`), and it is
transferred to the i.i.d. product space by the freezing lemma
(`NonlinearNKMarkovAR1Markov.freeze`).

* **`ar1_markov_representation`**: under the Taylor principle there are `r, δ > 0` such that for
  ANY innovation law `ν` with bounded support, `|ρ| < 1` and small `c`, there is ONE measurable
  `g : ℝ → ℝ³`, the same at every date, with `z_t = g(x_t)` solving the exact stochastic
  conditions a.s., and every a.s. measurable solution within `r` equal to `g(x_t)` a.s.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergAR1

open MeasureTheory ProbabilityTheory Filter Topology
open NonlinearNKMarkov (Mv IsMarkov)
open NonlinearNKMarkovGeneral (fwdSol ARState)
open NonlinearNKMarkovAE ExpectationsMeasure ExpectationsMeasureIID
open NonlinearNKMarkovAR1Markov
open NonlinearRotemberg NonlinearRotembergNewton NonlinearRotembergMarkov NonlinearRotembergAE
open NonlinearRotembergAENewton

variable {p : Par} {X : Type*}

/-- Woodford (2003), App. A.3, (A.13), Rotemberg pricing: the inverse of the linearised operator
maps bounded measurable functions to bounded measurable functions. -/
theorem bm_linSol [MeasurableSpace X] (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    (hMP : MeasPres M) {r : X → Fin 3 → ℝ} (hr : BM r) : BM (linSol p M r) := by
  have hb : BM (bR p r) := bm_comp (Ψ := bRv p) hr continuous_bRv
  have hu : BM (uR p M r) := bm_fwdSol hM hMP (summable_Arot hp) hb
  exact bm_comp (Ψ := fun q : (Fin 2 → ℝ) × (Fin 3 → ℝ) => ![q.1 0 - q.2 2, q.1 1, q.1 0])
    (bm_pair hu hr) (continuous_pi fun i => by
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop)

/-- Woodford (2003), (A.11): the residual of a bounded measurable function with bounded measurable
disturbances is bounded measurable. -/
theorem bm_PhiG [MeasurableSpace X] {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    (hMP : MeasPres M) {e : X → Fin 3 → ℝ} (he : BM e) {z : X → Fin 3 → ℝ} (hz : BM z) :
    BM (PhiG (Qmap p) (Nmap p) M e z) :=
  bm_comp (Ψ := fun q : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ) => Qmap p q.1 + q.2)
    (bm_pair (bm_pair he hz) (bm_Mv hM hMP (bm_comp (bm_pair he hz)
      (contDiff_Nmap (p := p) (n := 0)).continuous)))
    (((contDiff_Qmap (p := p) (n := 0)).continuous.comp continuous_fst).add continuous_snd)

/-- Woodford (2003), App. A.3 (**the Markov equilibrium is measurable**): under the Taylor
principle there is `r₀ > 0` such that for every `0 < r ≤ r₀` there is `δ > 0` such that on every
measurable state space with a Markov operator preserving bounded measurability and every
measurable disturbance pattern with `‖e‖ ≤ δ`, a MEASURABLE Markov equilibrium within `r`
exists. -/
theorem markov_existence_meas (hp : p.Std) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (X : Type*) [MeasurableSpace X]
      (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M → MeasPres M → ∀ e : X → Fin 3 → ℝ,
        Measurable e → (∀ x, ‖e x‖ ≤ δ) →
          ∃ z : X → Fin 3 → ℝ, ((∀ x, ‖z x‖ ≤ r) ∧ PhiG (Qmap p) (Nmap p) M e z = 0) ∧
            Measurable z := by
  obtain ⟨r0, hr0, hex⟩ := newton_exist (contDiff_Qmap (p := p) (n := 1))
    (contDiff_Nmap (p := p) (n := 1)) steadyState_zero (KL_pos hp.basic)
  refine ⟨r0, hr0, fun r hr hrr0 => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hex r hr hrr0
  refine ⟨δ, hδ, fun X _ M hM hMP e hem heδ => ?_⟩
  have heB : BM e := ⟨hem, δ, heδ⟩
  obtain ⟨z, hzm, hzB, hz⟩ := h X M hM (linSol p M) (linSol_right hp hM)
    (fun ρ ρ' a a' ha ha' h1 h2 => linSol_sub hp hM ha ha' h1 h2) (fun z => Measurable z)
    (fun v w _ _ D hD => linSol_left hp hM v w trivial trivial D hD) e heδ measurable_zero
    (fun z hzm hz => hzm.sub (bm_linSol hp hM hMP (bm_PhiG hM hMP heB ⟨hzm, r, hz⟩)).1)
    (fun zs z hzs hlim => measurable_of_tendsto_metrizable hzs (tendsto_pi_nhds.2 hlim))
  exact ⟨z, ⟨hzB, hz⟩, hzm⟩

/-- Woodford (2003), Ch. 6, §1 and App. A.3, Rotemberg pricing (**MARKOV REPRESENTATION with a
GENERAL bounded innovation law**): under the Taylor principle there are `r, δ > 0` such that on
the i.i.d. product space of any innovation law `ν` with `|ε| ≤ B` a.s., with the AR(1) state
`x_t = ρx_{t−1} + ε_t` (`|ρ| < 1`) and disturbances `e_t = x_t c` with `B‖c‖/(1 − |ρ|) ≤ δ`,
there is ONE measurable `g : ℝ → ℝ³` with `‖g‖ ≤ r`, independent of the date, such that
`z_t = g(x_t)` solves the exact stochastic conditions a.s., and every a.s. measurable solution
within `r` equals `g(x_t)` a.s. at every date. -/
theorem ar1_markov_representation (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (ν : ProbabilityMeasure ℝ) (B ρ : ℝ), |ρ| < 1 →
      (∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) → ∀ c : Fin 3 → ℝ, B / (1 - |ρ|) * ‖c‖ ≤ δ →
        ∃ g : ℝ → Fin 3 → ℝ, Measurable g ∧ (∀ y, ‖g y‖ ≤ r) ∧
          (Gd (iidSystem ν) (fun t ω => g (ar1 ρ t ω)) ∧
            Bd (iidSystem ν) (fun t ω => g (ar1 ρ t ω)) r ∧
            SeqEqmAE (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) (fun t ω => g (ar1 ρ t ω))) ∧
          ∀ z : ℕ → (ℕ → ℝ) → Fin 3 → ℝ, Gd (iidSystem ν) z → Bd (iidSystem ν) z r →
            SeqEqmAE (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) z →
              ∀ t, z t =ᵐ[(iidSystem ν).μ] fun ω => g (ar1 ρ t ω) := by
  obtain ⟨ρu, hρu, δu, hδu, huniq⟩ := seq_existence_ae hp
  obtain ⟨r0, hr0, hex⟩ := markov_existence_meas hp
  set r := min r0 ρu with hr
  have hr0' : 0 < r := lt_min hr0 hρu
  obtain ⟨δ1, hδ1, hM⟩ := hex r hr0' (min_le_left _ _)
  refine ⟨r, hr0', min δ1 δu, lt_min hδ1 hδu, fun ν B ρ hρ hB c hc => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hB.exists
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hx₀
  have h1ρ : 0 < 1 - |ρ| := by linarith
  set Bx := B / (1 - |ρ|) with hBx
  have hBx0 : 0 ≤ Bx := div_nonneg hB0 h1ρ.le
  set M := arOp ν ρ Bx hBx0 with hMdef
  set ξ : ARState Bx → Fin 3 → ℝ := fun x => (x : ℝ) • c with hξ
  have hξm : Measurable ξ := (continuous_subtype_val.smul continuous_const).measurable
  have hξδ : ∀ x, ‖ξ x‖ ≤ δ1 := fun x => by
    rw [hξ, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right x.2 (norm_nonneg c)).trans (hc.trans (min_le_left _ _))
  obtain ⟨gX, ⟨hgB, hgE⟩, hgm⟩ := hM (ARState Bx) M (arOp_isMarkov ν ρ Bx hBx0)
    (arOp_measPres ν ρ Bx hBx0) ξ hξm hξδ
  set g : ℝ → Fin 3 → ℝ := fun y => gX (clampX Bx hBx0 y) with hg
  have hgm' : Measurable g := hgm.comp (continuous_clampX Bx hBx0).measurable
  have hgB' : ∀ y, ‖g y‖ ≤ r := fun y => hgB _
  set E := iidSystem ν with hE
  have har : ∀ t, Measurable[E.𝓕 t] (ar1 ρ t) := fun t => (ar1_adapted ν ρ t).measurable
  have har0 : ∀ t, Measurable (ar1 ρ t) := fun t => (har t).mono (E.𝓕.le t) le_rfl
  have hx : ∀ t, ∀ᵐ ω ∂E.μ, |ar1 ρ t ω| ≤ Bx := fun t => ar1_bdd (ν := ν) hρ hB t
  have heG : Gd E (fun t ω => ar1 ρ t ω • c) := fun t =>
    ((har0 t).smul_const c).aestronglyMeasurable
  have hzG : Gd E (fun t ω => g (ar1 ρ t ω)) := fun t => (hgm'.comp (har0 t)).aestronglyMeasurable
  have hzB : Bd E (fun t ω => g (ar1 ρ t ω)) r := fun t => Eventually.of_forall fun ω => hgB' _
  have hNB : BM (fun x : ARState Bx => Nmap p (ξ x, gX x)) :=
    bm_comp (bm_pair ⟨hξm, δ1, hξδ⟩ ⟨hgm, r, hgB⟩) (contDiff_Nmap (p := p) (n := 0)).continuous
  have key : ∀ t (i : Fin 3), E.E t (fun ω' => Nmap p (ar1 ρ (t + 1) ω' • c,
      g (ar1 ρ (t + 1) ω')) i) =ᵐ[E.μ] fun ω =>
        M (fun x' => Nmap p (ξ x', gX x') i) (clampX Bx hBx0 (ar1 ρ t ω)) := by
    intro t i
    have hNi : BM (fun x : ARState Bx => Nmap p (ξ x, gX x) i) :=
      bm_comp hNB (continuous_apply i)
    obtain ⟨C, hC⟩ := hNi.2
    set F : ARState Bx × ℝ → ℝ := fun q => Nmap p (ξ (arSucc ρ Bx hBx0 q.1 q.2),
      gX (arSucc ρ Bx hBx0 q.1 q.2)) i with hF
    have hFm : Measurable F := hNi.1.comp (continuous_arSucc ρ Bx hBx0).measurable
    have hFb : ∀ q, |F q| ≤ C := fun q => by rw [← Real.norm_eq_abs]; exact hC _
    have hW : Measurable[E.𝓕 t] fun ω => clampX Bx hBx0 (ar1 ρ t ω) :=
      (continuous_clampX Bx hBx0).measurable.comp (har t)
    have hY : Measurable fun ω : ℕ → ℝ => ω (t + 1) := measurable_pi_apply (t + 1)
    have hind : Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ => ω (t + 1)) inferInstance)
        (E.𝓕 t) E.μ :=
      indep_of_indep_of_le_left (indep_future ν t)
        (measurable_future_fun t measurable_id).comap_le
    have hfr := freeze (μ := E.μ) (E.𝓕.le t) hW hY hind hFm hFb
    have hlaw : E.μ.map (fun ω : ℕ → ℝ => ω (t + 1)) = (ν : Measure ℝ) :=
      Measure.infinitePi_map_eval _ (t + 1)
    have hcongr : (fun ω' => Nmap p (ar1 ρ (t + 1) ω' • c, g (ar1 ρ (t + 1) ω')) i) =ᵐ[E.μ]
        fun ω' => F (clampX Bx hBx0 (ar1 ρ t ω'), ω' (t + 1)) := by
      filter_upwards [hx t, hx (t + 1)] with ω' ht ht1
      have e1 : arSucc ρ Bx hBx0 (clampX Bx hBx0 (ar1 ρ t ω')) (ω' (t + 1)) =
          clampX Bx hBx0 (ar1 ρ (t + 1) ω') := by
        simp only [arSucc, clampX_of hBx0 ht]
        rfl
      simp only [hF, e1, hg, hξ, clampX_of hBx0 ht1]
    filter_upwards [E.E_congr hcongr t, hfr] with ω h1 h2
    rw [h1]
    refine h2.trans ?_
    rw [hlaw, hMdef, arOp_eq ν ρ Bx hBx0 hNi.1 ⟨C, fun x => by
      rw [← Real.norm_eq_abs]; exact hC x⟩]
  have hzE : SeqEqmAE E p (fun t ω => ar1 ρ t ω • c) (fun t ω => g (ar1 ρ t ω)) := fun t => by
    filter_upwards [hx t, ae_all_iff.2 (key t)] with ω h1 h2
    have e1 : MvA E (fun s ω' => Nmap p (ar1 ρ s ω' • c, g (ar1 ρ s ω'))) t ω =
        Mv M (fun x' => Nmap p (ξ x', gX x')) (clampX Bx hBx0 (ar1 ρ t ω)) :=
      funext fun i => h2 i
    have e2 : ar1 ρ t ω • c = ξ (clampX Bx hBx0 (ar1 ρ t ω)) := by
      rw [hξ]; simp only [clampX_of hBx0 h1]
    change Qmap p (ar1 ρ t ω • c, g (ar1 ρ t ω)) + MvA E _ t ω = 0
    rw [e1, e2]
    exact congrFun hgE (clampX Bx hBx0 (ar1 ρ t ω))
  refine ⟨g, hgm', hgB', ⟨hzG, hzB, hzE⟩, fun z hzG' hzB' hz t => ?_⟩
  have heb : Bd E (fun t ω => ar1 ρ t ω • c) δu := fun t => by
    filter_upwards [hx t] with ω hω
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hω (norm_nonneg c)).trans (hc.trans (min_le_right _ _))
  obtain ⟨w, -, hw⟩ := huniq (ℕ → ℝ) E _ heG heb
  have h1 := hw z hzG' (fun t => by
    filter_upwards [hzB' t] with ω hω; exact hω.trans (min_le_right _ _)) hz t
  have h2 := hw (fun t ω => g (ar1 ρ t ω)) hzG (fun t => Eventually.of_forall fun ω =>
    (hgB' _).trans (min_le_right _ _)) hzE t
  exact h1.trans h2.symm

end Woodford.StabilizationWelfare.NonlinearRotembergAR1
