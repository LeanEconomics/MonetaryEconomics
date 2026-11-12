/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovAE

/-!
# The measure-theoretic sequence-space equilibrium is adapted

Woodford (2003), *Interest and Prices*, Appendix A.3 (p. 633: endogenous variables are functions
of the information) and Chapter 6, §1.

`NonlinearNKMarkovAE.seq_existence_ae` gives an a.s. unique, a.s. measurable solution of the exact
stochastic conditions on any filtered probability space. This module proves it is ADAPTED: if the
disturbances are, then `z_t` is a.s. equal to an `𝓕_t`-strongly measurable variable.

* `aesmSub_vec`, `aesmSub_lim`: a.s. strong measurability with respect to a sub-σ-algebra is
  coordinatewise and closed under a.s. limits (`StronglyMeasurable.limUnder`).
* `seq_existence_ae_inv`: the Newton–Picard fixed point lies in every set of processes containing
  `0`, invariant under the Newton step and closed under a.s. limits.
* `adA_MvA`, `adA_iterA`, `adA_fwdSolA`, `adA_linSolA`, `adA_PhiA`: adaptedness passes through the
  forecasts, the forward series, the inverse of the linearised operator and the residual.
* **`seq_existence_ae_adapted`**: the a.s. unique solution within `r` is adapted.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovAEAdapted

open MeasureTheory Filter Topology Asymptotics
open NonlinearNKMarkov NonlinearNKMarkovLinks NonlinearNKMarkovGeneral ExpectationsMeasure
open NonlinearNKMarkovAE

/-- Woodford (2003), App. A.3 (**invariant-set form of the a.s. existence theorem**): for every
radius `r ≤ r0` there is `δ > 0` such that, for a.s. measurable disturbances with `‖e_t‖ ≤ δ`,
the Newton–Picard solution within `r` belongs to every property `A` of processes holding at `0`,
preserved by the Newton step on processes within `r`, and closed under a.s. limits. -/
theorem seq_existence_ae_inv {p : Par} (hp : p.Std) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (e : ℕ → Ω → Fin 5 → ℝ), Gd E e → Bd E e δ →
        ∀ A : (ℕ → Ω → Fin 4 → ℝ) → Prop, A (fun _ _ => 0) →
          (∀ z, Gd E z → Bd E z r → A z →
            A (fun t ω => z t ω - linSolA E p (PhiA E p e z) t ω)) →
          (∀ (zs : ℕ → ℕ → Ω → Fin 4 → ℝ) (z : ℕ → Ω → Fin 4 → ℝ), (∀ n, A (zs n)) →
            (∀ t, ∀ᵐ ω ∂E.μ, Tendsto (fun n => zs n t ω) atTop (𝓝 (z t ω))) → A z) →
        ∃ z : ℕ → Ω → Fin 4 → ℝ, (Gd E z ∧ Bd E z r ∧ SeqEqmAE E p e z) ∧ A z := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_small (contDiff_Qmap (p := p) (n := 1)) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_small (contDiff_Nmap (p := p) (n := 1)) hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Qmap (p := p) (n := 0)).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Nmap (p := p) (n := 0)).continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr00.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr00.le))
  refine ⟨r0, hr00, fun r hr0' hrr0 => ?_⟩
  set τ := r / (4 * Kap p) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcQ : ContinuousAt (fun e : Fin 5 → ℝ => Qmap p (e, 0)) 0 :=
    ((contDiff_Qmap (p := p) (n := 0)).continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  have hcN : ContinuousAt (fun e : Fin 5 → ℝ => Nmap p (e, 0)) 0 :=
    ((contDiff_Nmap (p := p) (n := 0)).continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 hcQ τ hτ0
  obtain ⟨δN, hδN, hNc⟩ := Metric.continuousAt_iff.1 hcN τ hτ0
  set δ := min r (min (δQ / 2) (δN / 2)) with hδ
  have hδ0 : 0 < δ := lt_min hr0' (lt_min (by positivity) (by positivity))
  refine ⟨δ, hδ0, fun Ω _ E e he heb A hA0 hAT hAlim => ?_⟩
  have heb0 : Bd E e r0 := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans ((min_le_left _ _).trans hrr0)
  -- `Φ` is good and bounded on the ball
  have hPhiG : ∀ z, Gd E z → Gd E (PhiA E p e z) := fun z hz =>
    gd_add E (gd_pair E (contDiff_Qmap (p := p) (n := 0)).continuous he hz) (MvA_gd E _)
  have hPhiB : ∀ z, Bd E z r → Bd E (PhiA E p e z) (CQ + CN) := fun z hz t => by
    have hNb : Bd E (fun s ω => Nmap p (e s ω, z s ω)) CN := fun t => by
      filter_upwards [heb0 t, hz t] with ω h1 h2
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                      exact max_le h1 (h2.trans hrr0))
    filter_upwards [heb0 t, hz t, MvA_bd E hCN0 hNb t] with ω h1 h2 h3
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le h1 (h2.trans hrr0))) h3)
  -- the Newton map
  set T : (ℕ → Ω → Fin 4 → ℝ) → (ℕ → Ω → Fin 4 → ℝ) :=
    fun z t ω => z t ω - linSolA E p (PhiA E p e z) t ω with hT
  have hTG : ∀ z, Gd E z → Bd E z r → Gd E (T z) := fun z hz hzb t =>
    (hz t).sub ((linSolA_spec E hp (hPhiG z hz) (add_nonneg hCQ0 hCN0) (hPhiB z hzb)).1 t)
  have hcontr : ∀ z z', Gd E z → Gd E z' → Bd E z r → Bd E z' r → ∀ D, 0 ≤ D →
      Bd E (fun s ω => z s ω - z' s ω) D → Bd E (fun s ω => T z s ω - T z' s ω) (D / 2) := by
    intro z z' hz hz' hzb hz'b D hD0 hD
    have hzb0 : Bd E z r0 := fun t => by
      filter_upwards [hzb t] with ω hω; exact hω.trans hrr0
    have hz'b0 : Bd E z' r0 := fun t => by
      filter_upwards [hz'b t] with ω hω; exact hω.trans hrr0
    have hR := resid_ae E (p := p) hη0.le hQ hN hCN he hz hz' heb0 hzb0 hz'b0 hD0 hD
    have hdG : Gd E (fun s ω => z s ω - z' s ω) := fun t => (hz t).sub (hz' t)
    have hLd := bd_LopA E (p := p) hD0 hD
    have hPd : Bd E (fun s ω => PhiA E p e z s ω - PhiA E p e z' s ω) (CQ + CN + (CQ + CN)) :=
      fun t => by
        filter_upwards [hPhiB z hzb t, hPhiB z' hz'b t] with ω h1 h2
        exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hPdG : Gd E (fun s ω => PhiA E p e z s ω - PhiA E p e z' s ω) := fun t =>
      ((hPhiG z hz) t).sub ((hPhiG z' hz') t)
    have e1 := linSolA_sub E hp (hPhiG z hz) (hPhiG z' hz') (add_nonneg hCQ0 hCN0)
      (add_nonneg hCQ0 hCN0) (hPhiB z hzb) (hPhiB z' hz'b)
    have e2 := linSolA_sub E hp hPdG (gd_LopA E hdG) (by positivity)
      (mul_nonneg (by positivity) hD0) hPd hLd
    have e3 := linSolA_Lop E hp hdG hD0 hD
    have hRG : Gd E (fun s ω => PhiA E p e z s ω - PhiA E p e z' s ω -
        LopA E p (fun s ω => z s ω - z' s ω) s ω) := fun t => (hPdG t).sub (gd_LopA E hdG t)
    have hb := bd_linSolA E hp hRG (by positivity) hR
    intro t
    filter_upwards [e1 t, e2 t, e3 t, hb t] with ω h1 h2 h3 h4
    have key : T z t ω - T z' t ω = -linSolA E p (fun s ω => PhiA E p e z s ω -
        PhiA E p e z' s ω - LopA E p (fun s ω => z s ω - z' s ω) s ω) t ω := by
      rw [h2]
      simp only [hT]
      rw [h1, h3]
      abel
    rw [key, norm_neg]
    calc _ ≤ _ := h4
      _ = D / 2 := by rw [hη]; field_simp; ring
  -- `T 0` is small
  have hT0 : Bd E (T fun _ _ => 0) (r / 2) := by
    have hb : Bd E (PhiA E p e fun _ _ => 0) (2 * τ) := fun t => by
      have hs : Qmap p (0, 0) + Nmap p (0, 0) = 0 := by
        funext i; fin_cases i <;> simp [Qmap, Nmap]
      have hNg : Gd E (fun s ω => Nmap p (e s ω, (0 : Fin 4 → ℝ))) :=
        gd_pair E (contDiff_Nmap (p := p) (n := 0)).continuous he
        (fun _ => aestronglyMeasurable_const)
      have hNb : Bd E (fun s ω => Nmap p (e s ω, (0 : Fin 4 → ℝ))) CN := fun t => by
        filter_upwards [heb0 t] with ω h1
        exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                        exact max_le h1 (by simp [hr00.le]))
      have m := MvA_sub E hNg (fun _ => aestronglyMeasurable_const) hNb
        (C := CN) (D := ‖Nmap p (0, 0)‖) (h := fun s ω => Nmap p (e s ω, 0))
        (g := fun _ _ => Nmap p (0, 0)) (fun _ => Eventually.of_forall fun _ => le_rfl) t
      have hbN : Bd E (fun s ω => Nmap p (e s ω, (0 : Fin 4 → ℝ)) - Nmap p (0, 0)) τ :=
        fun t => by
          filter_upwards [heb t] with ω h1
          have h := hNc (x := e t ω) (by
            rw [dist_zero_right]; exact lt_of_le_of_lt (h1.trans
              ((min_le_right _ _).trans (min_le_right _ _))) (by linarith))
          rw [dist_eq_norm] at h; exact h.le
      filter_upwards [heb t, m, MvA_bd E hτ0.le hbN t] with ω h1 hm h3
      have hq : ‖Qmap p (e t ω, 0) - Qmap p (0, 0)‖ ≤ τ := by
        have h := hQc (x := e t ω) (by
          rw [dist_zero_right]; exact lt_of_le_of_lt (h1.trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have key : PhiA E p e (fun _ _ => 0) t ω = (Qmap p (e t ω, 0) - Qmap p (0, 0)) +
          MvA E (fun s ω => Nmap p (e s ω, 0) - Nmap p (0, 0)) t ω := by
        rw [hm, MvA_const]
        simp only [PhiA]
        linear_combination (norm := abel_nf) hs
      rw [key]
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ τ + τ := add_le_add hq h3
        _ = 2 * τ := by ring
    have hl := bd_linSolA E hp (hPhiG _ fun _ => aestronglyMeasurable_const) (by positivity) hb
    intro t
    filter_upwards [hl t] with ω hω
    simp only [hT, zero_sub, norm_neg]
    calc _ ≤ Kap p * (2 * τ) := hω
      _ = r / 2 := by rw [hτ]; field_simp; ring
  have hballB : ∀ z, Gd E z → Bd E z r → Bd E (T z) r := by
    intro z hz hzb t
    have h1 := hcontr z (fun _ _ => 0) hz (fun _ => aestronglyMeasurable_const) hzb
      (fun t => Eventually.of_forall fun _ => by simp [hr0'.le]) r hr0'.le
      (fun t => by filter_upwards [hzb t] with ω hω; simpa using hω) t
    filter_upwards [h1, hT0 t] with ω e1 e2
    calc ‖T z t ω‖ ≤ ‖T z t ω - T (fun _ _ => 0) t ω‖ + ‖T (fun _ _ => 0) t ω‖ := by
          have := norm_add_le (T z t ω - T (fun _ _ => 0) t ω) (T (fun _ _ => 0) t ω)
          simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add e1 e2
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → ℕ → Ω → Fin 4 → ℝ := fun n => T^[n] fun _ _ => 0 with hzs
  have hzsI : ∀ n, Gd E (zs n) ∧ Bd E (zs n) r := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun _ => aestronglyMeasurable_const,
        fun t => Eventually.of_forall fun _ => by simp [hzs, hr0'.le]⟩
    | succ n ih =>
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e]; exact ⟨hTG _ ih.1 ih.2, hballB _ ih.1 ih.2⟩
  have hzsA : ∀ n, A (zs n) := by
    intro n
    induction n with
    | zero => simpa [hzs] using hA0
    | succ n ih =>
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e]; exact hAT _ (hzsI n).1 (hzsI n).2 ih
  have hstep : ∀ n, Bd E (fun s ω => zs n s ω - zs (n + 1) s ω) (r / 2 / 2 ^ n) := by
    intro n
    induction n with
    | zero =>
      intro t
      filter_upwards [hT0 t] with ω hω
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hω
    | succ n ih =>
      have e1 : zs (n + 1 + 1) = T (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      have h := hcontr (zs (n + 1)) (zs n) (hzsI _).1 (hzsI _).1 (hzsI _).2 (hzsI _).2
        (r / 2 / 2 ^ n) (by positivity) (fun t => by
          filter_upwards [ih t] with ω hω; rwa [norm_sub_rev])
      intro t
      filter_upwards [h t] with ω hω
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) t ω = T (zs n) t ω from by rw [e2]]
      calc _ ≤ r / 2 / 2 ^ n / 2 := hω
        _ = r / 2 / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hall : ∀ t, ∀ᵐ ω ∂E.μ, ∀ n, ‖zs n t ω - zs (n + 1) t ω‖ ≤ r / 2 / 2 ^ n := fun t =>
    ae_all_iff.2 fun n => hstep n t
  set z : ℕ → Ω → Fin 4 → ℝ := fun t ω => limUnder atTop fun n => zs n t ω with hz
  have hconv : ∀ t, ∀ᵐ ω ∂E.μ, Tendsto (fun n => zs n t ω) atTop (𝓝 (z t ω)) := fun t => by
    filter_upwards [hall t] with ω hω
    have hc : CauchySeq fun n => zs n t ω :=
      cauchySeq_of_le_geometric_two (C := r) fun n => by rw [dist_eq_norm]; exact hω n
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hc
    exact tendsto_nhds_limUnder ⟨l, hl⟩
  have hzG : Gd E z := fun t =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hzsI n).1 t) (hconv t)
  have hzdist : ∀ n, Bd E (fun s ω => zs n s ω - z s ω) (r / 2 ^ n) := fun n t => by
    filter_upwards [hall t, hconv t] with ω hω hc
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun n => zs n t ω)
      (fun n => by rw [dist_eq_norm]; exact hω n) hc n
    rwa [dist_eq_norm] at this
  have hzB : Bd E z r := fun t => by
    filter_upwards [hconv t, ae_all_iff.2 fun n => (hzsI n).2 t] with ω hc hb
    exact le_of_tendsto' hc.norm hb
  -- fixed point
  have hfix : ∀ t, T z t =ᵐ[E.μ] z t := by
    intro t
    have hTn : ∀ n, Bd E (fun s ω => T z s ω - T (zs n) s ω) (r / 2 ^ n / 2) := fun n =>
      hcontr z (zs n) hzG (hzsI n).1 hzB (hzsI n).2 (r / 2 ^ n) (by positivity) (fun t => by
        filter_upwards [hzdist n t] with ω hω; rwa [norm_sub_rev])
    filter_upwards [hconv t, ae_all_iff.2 fun n => hTn n t] with ω hc hT'
    have hlim : Tendsto (fun n => zs (n + 1) t ω) atTop (𝓝 (T z t ω)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun n : ℕ => r / 2 ^ n / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun n => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hT' n
    exact tendsto_nhds_unique hlim (hc.comp (tendsto_add_atTop_nat 1))
  -- the fixed point solves the conditions
  have hl0 : ∀ t, linSolA E p (PhiA E p e z) t =ᵐ[E.μ] fun _ => 0 := fun t => by
    filter_upwards [hfix t] with ω hω
    have := congrArg (fun v => z t ω - v) hω
    simp only [hT, sub_sub_cancel, sub_self] at this
    exact this
  obtain ⟨-, -, hL⟩ := linSolA_spec E hp (hPhiG z hzG) (add_nonneg hCQ0 hCN0) (hPhiB z hzB)
  have hEq : SeqEqmAE E p e z := fun t => by
    have hc := LopA_congr E (p := p) hl0 t
    rw [LopA_zero] at hc
    filter_upwards [hL t, hc] with ω h1 h2
    change PhiA E p e z t ω = 0
    rw [← h1, h2]
  exact ⟨z, ⟨hzG, hzB, hEq⟩, hAlim zs z hzsA hconv⟩

/-! ## Adaptedness: measurability with respect to the date-`t` information -/

variable {Ω : Type*}

/-- Woodford (2003), App. A.3: a vector a.s. measurable for a sub-σ-algebra coordinatewise is
a.s. measurable for it. -/
theorem aesmSub_vec {m m0 : MeasurableSpace Ω} {μ : Measure[m0] Ω} {n : ℕ} {f : Ω → Fin n → ℝ}
    (hf : ∀ i, AEStronglyMeasurable[m] (fun ω => f ω i) μ) : AEStronglyMeasurable[m] f μ := by
  refine ⟨fun ω i => (hf i).mk _ ω, ?_, ?_⟩
  · let _ := m
    exact (measurable_pi_iff.2 fun i => (hf i).stronglyMeasurable_mk.measurable).stronglyMeasurable
  · filter_upwards [ae_all_iff.2 fun i => (hf i).ae_eq_mk] with ω hω
    funext i; exact hω i

/-- Woodford (2003), App. A.3: a.s. limits of variables a.s. measurable for a sub-σ-algebra are
a.s. measurable for it. -/
theorem aesmSub_lim {m m0 : MeasurableSpace Ω} {μ : Measure[m0] Ω} {n : ℕ}
    {f : ℕ → Ω → Fin n → ℝ} {g : Ω → Fin n → ℝ} (hf : ∀ k, AEStronglyMeasurable[m] (f k) μ)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun k => f k x) atTop (𝓝 (g x))) : AEStronglyMeasurable[m] g μ := by
  refine ⟨fun x => limUnder atTop (fun k => (hf k).mk _ x), ?_, ?_⟩
  · let _ := m
    exact StronglyMeasurable.limUnder fun k => (hf k).stronglyMeasurable_mk
  · filter_upwards [hl, ae_all_iff.2 fun k => (hf k).ae_eq_mk] with x h1 h2
    have : Tendsto (fun k => (hf k).mk _ x) atTop (𝓝 (g x)) := by
      have e : (fun k => (hf k).mk _ x) = fun k => f k x := funext fun k => (h2 k).symm
      rw [e]; exact h1
    exact this.limUnder_eq.symm

variable [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- Woodford (2003), App. A.3: a process is adapted when each `z_t` is a.s. equal to an
`𝓕_t`-strongly measurable variable. -/
def AdA {n : ℕ} (z : ℕ → Ω → Fin n → ℝ) : Prop := ∀ t, AEStronglyMeasurable[E.𝓕 t] (z t) E.μ

/-- Forecasts are adapted. -/
theorem adA_MvA {n : ℕ} (h : ℕ → Ω → Fin n → ℝ) : AdA E (MvA E h) := fun t =>
  aesmSub_vec fun _ => (E.stronglyMeasurable_E t _).aestronglyMeasurable

/-- Iterated forecasts of an adapted process are adapted. -/
theorem adA_iterA {n : ℕ} {b : ℕ → Ω → Fin n → ℝ} (hb : AdA E b) (k : ℕ) :
    AdA E (iterA E k b) := by
  cases k with
  | zero => exact hb
  | succ k => rw [iterA_succ]; exact adA_MvA E _

/-- Woodford (2003), (A.13): the forward series of an adapted bounded process is adapted. -/
theorem adA_fwdSolA {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : Summable fun k => mnorm (B ^ k)) {b : ℕ → Ω → Fin n → ℝ} {Bb : ℝ} (hBb : 0 ≤ Bb)
    (hbb : Bd E b Bb) (hbA : AdA E b) : AdA E (fwdSolA E B b) := by
  intro t
  have hsB : Summable fun k => mnorm (B ^ k) * Bb := hB.mul_right Bb
  have hS : ∀ N, AEStronglyMeasurable[E.𝓕 t]
      (fun ω => ∑ k ∈ Finset.range N, (B ^ k).mulVec (iterA E k b t ω)) E.μ := by
    intro N
    induction N with
    | zero => simpa using (aestronglyMeasurable_const (m := E.𝓕 t) (μ := E.μ)
        (b := (0 : Fin n → ℝ)))
    | succ N ih =>
      simp only [Finset.sum_range_succ]
      exact ih.add ((Matrix.mulVecLin (B ^ N)).toContinuousLinearMap.continuous
        |>.comp_aestronglyMeasurable (adA_iterA E hbA N t))
  refine aesmSub_lim hS ?_
  filter_upwards [ae_all_iff.2 fun k => iterA_bd E hBb hbb k t] with ω h
  exact (Summable.of_norm_bounded hsB fun k => (norm_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_left (h k) (mnorm_nonneg _))).hasSum.tendsto_sum_nat

/-- Scalar forecasts are adapted. -/
theorem adS_Ms (f : ℕ → Ω → ℝ) (t : ℕ) : AEStronglyMeasurable[E.𝓕 t] (Ms E f t) E.μ :=
  (E.stronglyMeasurable_E t _).aestronglyMeasurable

/-- Coordinates of an adapted process are adapted. -/
theorem adA_comp {n : ℕ} {z : ℕ → Ω → Fin n → ℝ} (hz : AdA E z) (i : Fin n) (t : ℕ) :
    AEStronglyMeasurable[E.𝓕 t] (fun ω => z t ω i) E.μ :=
  (continuous_apply i).comp_aestronglyMeasurable (hz t)

/-- Division of an adapted variable by a constant. -/
theorem adS_div {t : ℕ} {f : Ω → ℝ} (hf : AEStronglyMeasurable[E.𝓕 t] f E.μ) (c : ℝ) :
    AEStronglyMeasurable[E.𝓕 t] (fun ω => f ω / c) E.μ := by
  simpa [div_eq_mul_inv] using hf.mul_const c⁻¹

/-- Woodford (2003), App. A.3: the inverse of the linearised operator maps adapted bounded
processes to adapted processes. -/
theorem adA_linSolA {p : Par} (hp : p.Std) {r : ℕ → Ω → Fin 4 → ℝ} (hrG : Gd E r) {a : ℝ}
    (ha0 : 0 ≤ a) (hr : Bd E r a) (hrA : AdA E r) : AdA E (linSolA E p r) := by
  have hrc : ∀ i t, ∀ᵐ ω ∂E.μ, |r t ω i| ≤ a := fun i t => bd_comp E (hr t) i
  have hd := hp.dd_pos
  have hcR := hp.cR_pos
  have hk3 := hp.k3_pos
  have hab0 := hp.ab_pos
  have hab1 := hp.ab_lt_one
  have hθ1 : 0 < p.θ - 1 := by linarith [hp.one_lt_θ]
  have hm3 : ∀ t, ∀ᵐ ω ∂E.μ, |Ms E (fun s ω => r s ω 3) t ω| ≤ a := fun t =>
    E.abs_E_le (hrc 3 (t + 1)) t
  have hs1G : Gd E (s1A E p r) := fun t => by
    unfold s1A
    exact aesm_div E ((((aesm_comp E (hrG t) 2).sub (aesm_comp E (hrG t) 1)).add
      ((aesm_comp E (hrG t) 3).const_mul p.k3)).sub ((aesm_E E t _).const_mul
        (p.α * p.β * p.k3))) p.cR
  have hs1A : ∀ t, AEStronglyMeasurable[E.𝓕 t] (s1A E p r t) E.μ := fun t => by
    unfold s1A
    exact adS_div E ((((adA_comp E hrA 2 t).sub (adA_comp E hrA 1 t)).add
      ((adA_comp E hrA 3 t).const_mul p.k3)).sub ((adS_Ms E _ t).const_mul
        (p.α * p.β * p.k3))) p.cR
  set S1 := (2 + p.k3 + p.α * p.β * p.k3) / p.cR * a with hS1
  have hS10 : 0 ≤ S1 := by positivity
  have hs1 : ∀ t, ∀ᵐ ω ∂E.μ, |s1A E p r t ω| ≤ S1 := by
    intro t
    filter_upwards [hrc 1 t, hrc 2 t, hrc 3 t, hm3 t] with ω h1 h2 h3 h4
    simp only [s1A, hS1]
    rw [abs_div, abs_of_pos hcR, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hcR]
    calc |r t ω 2 - r t ω 1 + p.k3 * r t ω 3 - p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω|
        ≤ |r t ω 2| + |r t ω 1| + p.k3 * |r t ω 3| +
            p.α * p.β * p.k3 * |Ms E (fun s ω => r s ω 3) t ω| := by
          have e1 := abs_sub (r t ω 2 - r t ω 1 + p.k3 * r t ω 3)
            (p.α * p.β * p.k3 * Ms E (fun s ω => r s ω 3) t ω)
          have e2 := abs_add_le (r t ω 2 - r t ω 1) (p.k3 * r t ω 3)
          have e3 := abs_sub (r t ω 2) (r t ω 1)
          rw [abs_mul (p.α * p.β * p.k3), abs_of_pos (by positivity : 0 < p.α * p.β * p.k3),
            abs_mul, abs_of_pos hk3] at *
          linarith
      _ ≤ a + a + p.k3 * a + p.α * p.β * p.k3 * a := by gcongr
      _ = (2 + p.k3 + p.α * p.β * p.k3) * a := by ring
  set Bb := (a + p.φ * S1 + p.κ * a + (p.σ + p.φy) * S1) / p.dd with hBb
  have hBb0 : 0 ≤ Bb := by
    have := hp.φ_nonneg; have := hp.κ_pos; have := hp.σ_pos; have := hp.φy_nonneg
    positivity
  have hbG : Gd E (bA E p r) := fun t => aesm_vec E fun i => by
    fin_cases i
    · simp only [bA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact aesm_div E ((aesm_comp E (hrG t) 0).sub ((hs1G t).const_mul p.φ)) p.dd
    · simp only [bA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact aesm_div E (((aesm_comp E (hrG t) 0).const_mul p.κ).add
        ((hs1G t).const_mul (p.σ + p.φy))) p.dd
  have hbA : AdA E (bA E p r) := fun t => aesmSub_vec fun i => by
    fin_cases i
    · simp only [bA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact adS_div E ((adA_comp E hrA 0 t).sub ((hs1A t).const_mul p.φ)) p.dd
    · simp only [bA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact adS_div E (((adA_comp E hrA 0 t).const_mul p.κ).add
        ((hs1A t).const_mul (p.σ + p.φy))) p.dd
  have hbb : Bd E (bA E p r) Bb := fun t => by
    filter_upwards [hrc 0 t, hs1 t] with ω h0 hs
    have hφ := hp.φ_nonneg
    have hκ := hp.κ_pos
    have hσφ : 0 ≤ p.σ + p.φy := by linarith [hp.σ_pos, hp.φy_nonneg]
    refine (pi_norm_le_iff_of_nonneg hBb0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    fin_cases i
    · simp only [bA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [abs_div, abs_of_pos hd, hBb]
      refine div_le_div_of_nonneg_right ?_ hd.le
      have := abs_sub (r t ω 0) (p.φ * s1A E p r t ω)
      rw [abs_mul, abs_of_nonneg hφ] at this
      have := mul_le_mul_of_nonneg_left hs hφ
      nlinarith [mul_nonneg hκ.le ha0, mul_nonneg hσφ hS10]
    · simp only [bA, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [abs_div, abs_of_pos hd, hBb]
      refine div_le_div_of_nonneg_right ?_ hd.le
      have := abs_add_le (p.κ * r t ω 0) ((p.σ + p.φy) * s1A E p r t ω)
      rw [abs_mul, abs_of_pos hκ, abs_mul, abs_of_nonneg hσφ] at this
      have := mul_le_mul_of_nonneg_left hs hσφ
      have := mul_le_mul_of_nonneg_left h0 hκ.le
      nlinarith [mul_nonneg hφ hS10]
  obtain ⟨huG, huB, -⟩ := fwdSolA_spec E (summable_mnorm_Amat hp) hbG hBb0 hbb
  have huA : AdA E (uA E p r) := adA_fwdSolA E (summable_mnorm_Amat hp) hBb0 hbb hbA
  set U := (∑' k, mnorm (Amat p ^ k)) * Bb with hU
  have hU0 : 0 ≤ U := mul_nonneg (tsum_nonneg fun _ => mnorm_nonneg _) hBb0
  have huc : ∀ i t, ∀ᵐ ω ∂E.μ, |uA E p r t ω i| ≤ U := fun i t => bd_comp E (huB t) i
  have hmu : ∀ i t, ∀ᵐ ω ∂E.μ, |Ms E (fun s ω => uA E p r s ω i) t ω| ≤ U := fun i t =>
    E.abs_E_le (huc i (t + 1)) t
  set G := a + (1 - p.α * p.β) * |1 - p.σ| * U + p.α * p.β * (p.θ - 1) * U with hG
  have hG0 : 0 ≤ G := by
    have : 0 < 1 - p.α * p.β := by linarith
    positivity
  have hgb : Bd E (fun t ω => ![gA E p r t ω]) G := fun t => by
    filter_upwards [hrc 1 t, huc 0 t, hmu 1 t] with ω hR hY hP
    refine (pi_norm_le_iff_of_nonneg hG0).2 fun i => ?_
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one, Real.norm_eq_abs, gA]
    have e1 := abs_add_le (r t ω 1 + (1 - p.α * p.β) * (1 - p.σ) * uA E p r t ω 0)
      (p.α * p.β * (p.θ - 1) * Ms E (fun s ω => uA E p r s ω 1) t ω)
    have e2 := abs_add_le (r t ω 1) ((1 - p.α * p.β) * (1 - p.σ) * uA E p r t ω 0)
    have t1 : |(1 - p.α * p.β) * (1 - p.σ) * uA E p r t ω 0| ≤
        (1 - p.α * p.β) * |1 - p.σ| * U := by
      rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 - p.α * p.β)]
      exact mul_le_mul_of_nonneg_left hY (mul_nonneg
        (by linarith : (0 : ℝ) ≤ 1 - p.α * p.β) (abs_nonneg (1 - p.σ)))
    have t2 : |p.α * p.β * (p.θ - 1) * Ms E (fun s ω => uA E p r s ω 1) t ω| ≤
        p.α * p.β * (p.θ - 1) * U := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < p.α * p.β * (p.θ - 1))]
      exact mul_le_mul_of_nonneg_left hP (by positivity)
    linarith
  have hgA : AdA E (fun t ω => ![gA E p r t ω]) := fun t => aesmSub_vec fun i => by
    fin_cases i
    simp only [gA, Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
    exact ((adA_comp E hrA 1 t).add ((adA_comp E huA 0 t).const_mul _)).add
      ((adS_Ms E _ t).const_mul _)
  have habs : mnorm !![p.α * p.β] < 1 := by
    rw [mnorm_ab, abs_of_pos hab0]; exact hab1
  have hFA : AdA E (fwdSolA E !![p.α * p.β] (fun t ω => ![gA E p r t ω])) :=
    adA_fwdSolA E (summable_mnorm_pow_of_lt habs) hG0 hgb hgA
  intro t
  refine aesmSub_vec fun i => ?_
  fin_cases i
  · exact adA_comp E huA 0 t
  · exact adA_comp E huA 1 t
  · exact adA_comp E hFA 0 t
  · simp only [linSolA, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    exact ((adA_comp E hFA 0 t).add ((adA_comp E huA 1 t).const_mul _)).sub
      ((adA_comp E hrA 3 t).const_mul _)

/-- Woodford (2003), (A.11): the residual of an adapted process with adapted disturbances is
adapted. -/
theorem adA_PhiA {p : Par} {e : ℕ → Ω → Fin 5 → ℝ} {z : ℕ → Ω → Fin 4 → ℝ} (he : AdA E e)
    (hz : AdA E z) : AdA E (PhiA E p e z) := fun t =>
  ((contDiff_Qmap (p := p) (n := 0)).continuous.comp_aestronglyMeasurable
    ((he t).prodMk (hz t))).add (adA_MvA E _ t)

/-- Woodford (2003), App. A.3, p. 633, on a general probability space (**the a.s. unique
equilibrium is ADAPTED**): under the Taylor principle there are `r, δ > 0` such that on every
filtered probability space, for every adapted, a.s. measurable disturbance process with
`‖e_t‖ ≤ δ` a.s., the solution of the exact stochastic conditions within `r` is adapted (each
`z_t` a.s. equal to an `𝓕_t`-strongly measurable variable) and is a.s. unique within `r`. -/
theorem seq_existence_ae_adapted {p : Par} (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 5 → ℝ), Gd E e → Bd E e δ → AdA E e →
        ∃ z : ℕ → Ω → Fin 4 → ℝ, ((Gd E z ∧ Bd E z r ∧ SeqEqmAE E p e z) ∧ AdA E z) ∧
          ∀ z' : ℕ → Ω → Fin 4 → ℝ, Gd E z' → Bd E z' r → SeqEqmAE E p e z' →
            ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨ρu, hρu, huniq⟩ := seq_uniqueness_ae hp
  obtain ⟨r0, hr0, hex⟩ := seq_existence_ae_inv hp
  set r := min r0 ρu with hr
  have hr0' : 0 < r := lt_min hr0 hρu
  obtain ⟨δ1, hδ1, hex1⟩ := hex r hr0' (min_le_left _ _)
  set δ := min δ1 ρu with hδ
  refine ⟨r, hr0', δ, lt_min hδ1 hρu, fun Ω _ E e he heb heA => ?_⟩
  have heb1 : Bd E e δ1 := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans (min_le_left _ _)
  set R := max δ r with hR
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    R).exists_bound_of_continuousOn ((contDiff_Qmap (p := p) (n := 0)).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    R).exists_bound_of_continuousOn ((contDiff_Nmap (p := p) (n := 0)).continuous.continuousOn)
  have hR0 : 0 ≤ R := le_max_of_le_right hr0'.le
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hR0))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hR0))
  have hPhiB : ∀ z, Bd E z r → Bd E (PhiA E p e z) (CQ + CN) := fun z hz t => by
    have hNb : Bd E (fun s ω => Nmap p (e s ω, z s ω)) CN := fun t => by
      filter_upwards [heb t, hz t] with ω h1 h2
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                      exact max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)))
    filter_upwards [heb t, hz t, MvA_bd E hCN0 hNb t] with ω h1 h2 h3
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)))) h3)
  have hPhiG : ∀ z, Gd E z → Gd E (PhiA E p e z) := fun z hz =>
    gd_add E (gd_pair E (contDiff_Qmap (p := p) (n := 0)).continuous he hz) (MvA_gd E _)
  obtain ⟨z, ⟨hzG, hzB, hzE⟩, hzA⟩ := hex1 Ω E e he heb1 (AdA E)
    (fun t => aestronglyMeasurable_const)
    (fun z hzG hzB hzA t => (hzA t).sub (adA_linSolA E hp (hPhiG z hzG) (add_nonneg hCQ0 hCN0)
      (hPhiB z hzB) (adA_PhiA E heA hzA) t))
    (fun zs z hzs hlim t => aesmSub_lim (fun n => hzs n t) (hlim t))
  refine ⟨z, ⟨⟨hzG, hzB, hzE⟩, hzA⟩, fun z' hz'G hz'B hz' => ?_⟩
  have hb : Bd E e ρu := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans (min_le_right _ _)
  exact huniq Ω E e z' z he hz'G hzG hb (fun t => by
      filter_upwards [hz'B t] with ω hω; exact hω.trans (min_le_right _ _))
    (fun t => by filter_upwards [hzB t] with ω hω; exact hω.trans (min_le_right _ _)) hz' hzE

end Woodford.StabilizationWelfare.NonlinearNKMarkovAEAdapted
