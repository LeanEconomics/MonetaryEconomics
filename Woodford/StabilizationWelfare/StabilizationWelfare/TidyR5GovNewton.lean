/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovAEAdapted
import StabilizationWelfare.NonlinearNKMarkovRamseyIFT

/-!
# The Newton step for any model with the linearisation of the New Keynesian model

Woodford (2003), *Interest and Prices*, Chapter 6, §1 and §5, Chapter 4, Proposition 4.3, and
Appendix A.3 (the implicit function theorem in sequence space).

The existence and uniqueness proofs of NonlinearNKMarkovGeneral, NonlinearNKMarkovAE and
NonlinearNKMarkovAEAdapted use the exact conditions `Qmap`, `Nmap` only through: smoothness,
the steady state `Q(0,0) + N(0,0) = 0`, and the partial derivatives in the endogenous variables
`DQ0`, `DN0`. Everything linear (`Lop`, `linSol`, `apriori`, `LopA`, `linSolA`, `apriori_ae`) is
reused unchanged from the imports; the nonlinear Newton step is restated here for ANY maps
`Q, N` with disturbances in `ℝᵏ` and the same linearisation (`NKMaps`). The
government-purchases model of TidyR5GovPurchases is an instance.

## Main results

* `NKMaps`, `GPhi`, `GEqm`: the maps and the Markov conditions.
* **`gen_existence`**, **`gen_uniqueness`**, **`gen_markov_equilibrium`**: existence and local
  uniqueness on every state space with every Markov operator, radii uniform.
* `GSeqEqm`, `gseqEqm_iff`, **`gen_seq_uniqueness`**, **`gen_seq_existence`**: sequence space for
  every `ExpectationSystem` (in particular every event tree).
* `GSeqEqmAE`, `GPhiA`, **`gen_seq_uniqueness_ae`**, `gen_resid_ae`, `gen_seq_existence_ae_inv`,
  `gen_adA_PhiA`, **`gen_seq_existence_ae_adapted`**: almost surely on every filtered probability
  space with Mathlib's conditional expectations; the solution is adapted and a.s. unique.
-/

namespace Woodford.StabilizationWelfare.TidyR5GovNewton

open MeasureTheory Filter Topology Asymptotics
open NonlinearNKMarkov NonlinearNKMarkovLinks NonlinearNKMarkovGeneral ExpectationsMeasure
open NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted
open NonlinearNKMarkovRamseyIFT (remainder_gen)

variable (p : Par) (k : ℕ)

/-- Woodford (2003), §1 and App. A.3 (**a model with the linearisation of the New Keynesian
model**): smooth current and lead parts `Q, N : ℝᵏ × ℝ⁴ → ℝ⁴` of the equilibrium conditions with
the steady state at `0` and partial derivatives `DQ0`, `DN0` in the endogenous variables. -/
structure NKMaps where
  /-- Woodford (2003), App. A.3: the current-date part of the conditions. -/
  Q : (Fin k → ℝ) × (Fin 4 → ℝ) → Fin 4 → ℝ
  /-- Woodford (2003), App. A.3: the part of the conditions inside `Eₜ`. -/
  N : (Fin k → ℝ) × (Fin 4 → ℝ) → Fin 4 → ℝ
  /-- Woodford (2003), App. A.3: `Q` is `C¹`. -/
  smoothQ : ContDiff ℝ 1 Q
  /-- Woodford (2003), App. A.3: `N` is `C¹`. -/
  smoothN : ContDiff ℝ 1 N
  /-- Woodford (2003), App. A.3: the partial derivative of `Q` in the endogenous variables. -/
  derivQ : ∀ v, fderiv ℝ Q (0, 0) (0, v) = DQ0 p v
  /-- Woodford (2003), App. A.3: the partial derivative of `N` in the endogenous variables. -/
  derivN : ∀ v, fderiv ℝ N (0, 0) (0, v) = DN0 p v
  /-- Woodford (2003), App. A.3: the deterministic steady state solves the conditions. -/
  steady : Q (0, 0) + N (0, 0) = 0

variable {p k} {X : Type*}

/-- The norm of `(0, w)` in `ℝᵏ × ℝ⁴` is `‖w‖` (Woodford (2003), App. A.3, bookkeeping). -/
theorem gnorm_pair_zero (w : Fin 4 → ℝ) : ‖((0 : Fin k → ℝ), w)‖ = ‖w‖ := by
  rw [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]

/-- Woodford (2003), App. A.3: the residual of the Markov conditions,
`Φ(ε, z)(x) = Q(εξ(x), z(x)) + M[N(εξ, z)](x)`. -/
noncomputable def GPhi (F : NKMaps p k) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (ξ : X → Fin k → ℝ) (ε : ℝ)
    (z : X → Fin 4 → ℝ) : X → Fin 4 → ℝ :=
  fun x => F.Q (ε • ξ x, z x) + Mv M (fun x' => F.N (ε • ξ x', z x')) x

/-- Woodford (2003), App. A.3: a Markov equilibrium of amplitude `ε`. -/
def GEqm (F : NKMaps p k) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (ξ : X → Fin k → ℝ) (ε : ℝ)
    (z : X → Fin 4 → ℝ) : Prop :=
  GPhi F M ξ ε z = 0

/-- Woodford (2003), App. A.3: the residual minus its linearisation is small: for `z, z′` and
disturbances within the radii of `remainder_small`, `‖Φz − Φz′ − L(z − z′)‖ ≤ 2η sup‖z − z′‖`. -/
theorem gen_resid_diff_bound (F : NKMaps p k) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {η ρQ ρN : ℝ}
    (hη0 : 0 ≤ η)
    (hQ : ∀ e w w', ‖e‖ ≤ ρQ → ‖w‖ ≤ ρQ → ‖w'‖ ≤ ρQ →
      ‖F.Q (e, w) - F.Q (e, w') - fderiv ℝ (F.Q) (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    (hN : ∀ e w w', ‖e‖ ≤ ρN → ‖w‖ ≤ ρN → ‖w'‖ ≤ ρN →
      ‖F.N (e, w) - F.N (e, w') - fderiv ℝ (F.N) (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    {ξ : X → Fin k → ℝ} {ε : ℝ} {z z' : X → Fin 4 → ℝ}
    (he : ∀ x, ‖ε • ξ x‖ ≤ min ρQ ρN) (hz : ∀ x, ‖z x‖ ≤ min ρQ ρN)
    (hz' : ∀ x, ‖z' x‖ ≤ min ρQ ρN) {D : ℝ} (hD : ∀ x, ‖z x - z' x‖ ≤ D) (x : X) :
    ‖GPhi F M ξ ε z x - GPhi F M ξ ε z' x - Lop p M (fun x => z x - z' x) x‖ ≤ 2 * η * D := by
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
  have e2 : ∀ x', ‖F.N (ε • ξ x', z x') - F.N (ε • ξ x', z' x') -
      fderiv ℝ (F.N) (0, 0) (0, z x' - z' x')‖ ≤ η * D := fun x' =>
    (hN _ _ _ ((he x').trans (min_le_right _ _)) ((hz x').trans (min_le_right _ _))
      ((hz' x').trans (min_le_right _ _))).trans (mul_le_mul_of_nonneg_left (hD x') hη0)
  have e1 := (hQ (ε • ξ x) (z x) (z' x) ((he x).trans (min_le_left _ _))
    ((hz x).trans (min_le_left _ _)) ((hz' x).trans (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_left (hD x) hη0)
  have e3 := Mv_norm_le hM (mul_nonneg hη0 hD0) e2 x
  have key : GPhi F M ξ ε z x - GPhi F M ξ ε z' x - Lop p M (fun x => z x - z' x) x =
      (F.Q (ε • ξ x, z x) - F.Q (ε • ξ x, z' x) -
        fderiv ℝ (F.Q) (0, 0) (0, z x - z' x)) +
      Mv M (fun x' => F.N (ε • ξ x', z x') - F.N (ε • ξ x', z' x') -
        fderiv ℝ (F.N) (0, 0) (0, z x' - z' x')) x := by
    simp only [F.derivQ, F.derivN]
    have m1 := congrFun (Mv_sub M (fun x' => F.N (ε • ξ x', z x') -
      F.N (ε • ξ x', z' x')) (fun x' => DN0 p (z x' - z' x'))) x
    have m2 := congrFun (Mv_sub M (fun x' => F.N (ε • ξ x', z x'))
      (fun x' => F.N (ε • ξ x', z' x'))) x
    rw [m1, m2]
    simp only [GPhi, Lop]
    abel
  rw [key]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ η * D + η * D := add_le_add e1 e3
    _ = 2 * η * D := by ring

/-- `Φ(ε, 0)` at the steady state: `Φ(ε, 0) = [Q(εξ, 0) − Q(0, 0)] + M[N(εξ, 0) − N(0, 0)]`. -/
theorem gen_Phi_zero_eq (F : NKMaps p k) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    (ξ : X → Fin k → ℝ) (ε : ℝ)
    (x : X) : GPhi F M ξ ε 0 x = (F.Q (ε • ξ x, 0) - F.Q (0, 0)) +
      Mv M (fun x' => F.N (ε • ξ x', 0) - F.N (0, 0)) x := by
  have hs : F.Q (0, 0) + Mv M (fun _ => F.N (0, 0)) x = 0 := by
    rw [Mv_const hM]
    exact F.steady
  have m := congrFun (Mv_sub M (fun x' => F.N (ε • ξ x', 0))
    (fun _ => F.N (0, 0))) x
  simp only [GPhi, Pi.zero_apply]
  rw [m]
  linear_combination hs

/-- Woodford (2003), App. A.3 (**a quantitative implicit function theorem on bounded functions:
existence**). Under the Taylor principle there is `r₀ > 0` such that for every radius
`0 < r ≤ r₀` there is `δ > 0`, depending ONLY on the parameters, with: for EVERY state space, EVERY
Markov operator and EVERY disturbance pattern with `‖εξ(x)‖ ≤ δ`, a Markov equilibrium with
`‖z(x)‖ ≤ r` exists (the limit of the Newton iteration `z ↦ z − L⁻¹Φ(ε, z)`, a contraction with
factor `1/2` on the ball). -/
theorem gen_existence (F : NKMaps p k) (hp : p.Std) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)),
      IsMarkov M → ∀ (ξ : X → Fin k → ℝ) (ε : ℝ), (∀ x, ‖ε • ξ x‖ ≤ δ) →
        ∃ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) ∧ GEqm F M ξ ε z := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_gen F.smoothQ hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_gen F.smoothN hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  -- bounds of `Q`, `N` on the ball
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn (F.smoothQ.continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn (F.smoothN.continuous.continuousOn)
  refine ⟨r0, hr00, fun r hr hrr0 => ?_⟩
  set τ := r / (4 * Kap p) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcQ : ContinuousAt (fun e : Fin k → ℝ => F.Q (e, 0)) 0 :=
    (F.smoothQ.continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  have hcN : ContinuousAt (fun e : Fin k → ℝ => F.N (e, 0)) 0 :=
    (F.smoothN.continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 hcQ τ hτ0
  obtain ⟨δN, hδN, hNc⟩ := Metric.continuousAt_iff.1 hcN τ hτ0
  refine ⟨min r (min (δQ / 2) (δN / 2)), lt_min hr (lt_min (by positivity) (by positivity)),
    fun X M hM ξ ε hξ => ?_⟩
  have hξr : ∀ x, ‖ε • ξ x‖ ≤ r := fun x => (hξ x).trans (min_le_left _ _)
  have hξ0 : ∀ x, ‖ε • ξ x‖ ≤ r0 := fun x => (hξr x).trans hrr0
  -- `Φ` is bounded on the ball
  have hPhiB : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖GPhi F M ξ ε z x‖ ≤ CQ + CN := by
    intro z hz x
    have hin : ∀ x', (ε • ξ x', z x') ∈ Metric.closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ)) r0 :=
      fun x' => by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        exact max_le (hξ0 x') ((hz x').trans hrr0)
    have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN _ (hin x))
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (hin x))
      (Mv_norm_le hM hCN0 (fun x' => hCN _ (hin x')) x))
  -- the Newton map
  set T : (X → Fin 4 → ℝ) → (X → Fin 4 → ℝ) := fun z x => z x - linSol p M (GPhi F M ξ ε z) x
    with hT
  have hCQN : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → 0 ≤ CQ + CN := fun z hz => by
    by_cases hX : Nonempty X
    · obtain ⟨x⟩ := hX; exact (norm_nonneg _).trans (hPhiB z hz x)
    · have hin : ((0 : Fin k → ℝ), (0 : Fin 4 → ℝ)) ∈ Metric.closedBall 0 r0 :=
        Metric.mem_closedBall_self hr00.le
      exact add_nonneg ((norm_nonneg _).trans (hCQ _ hin)) ((norm_nonneg _).trans (hCN _ hin))
  have hcontr : ∀ z z' : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → (∀ x, ‖z' x‖ ≤ r) → ∀ D,
      (∀ x, ‖z x - z' x‖ ≤ D) → ∀ x, ‖T z x - T z' x‖ ≤ D / 2 := by
    intro z z' hz hz' D hD x
    have hD0 : 0 ≤ D := by
      by_cases hX : Nonempty X
      · obtain ⟨x⟩ := hX; exact (norm_nonneg _).trans (hD x)
      · exact absurd ⟨x⟩ hX
    have hz0 : ∀ x, ‖z x‖ ≤ r0 := fun x => (hz x).trans hrr0
    have hz'0 : ∀ x, ‖z' x‖ ≤ r0 := fun x => (hz' x).trans hrr0
    have hC := hCQN z hz
    have hLd := Lop_bounded (p := p) hM hD0 hD
    set c := (‖fderiv ℝ (Qmap p) (0, 0)‖ + ‖fderiv ℝ (Nmap p) (0, 0)‖) * D
    have hc0 : 0 ≤ c := mul_nonneg (by positivity) hD0
    have hres := gen_resid_diff_bound F hM hη0.le hQ hN hξ0 hz0 hz'0 hD
    -- `T z − T z′ = −L⁻¹(Φz − Φz′ − L(z − z′))`
    have e1 := linSol_sub hp hM hC hC (hPhiB z hz) (hPhiB z' hz')
    have e2 := linSol_sub hp hM (a := CQ + CN + (CQ + CN)) (a' := c) (by positivity) hc0
      (r := fun x => GPhi F M ξ ε z x - GPhi F M ξ ε z' x)
      (fun x => (norm_sub_le _ _).trans (add_le_add (hPhiB z hz x) (hPhiB z' hz' x))) hLd
    have e3 := linSol_Lop hp hM hD0 hD
    have key : T z x - T z' x = -linSol p M (fun x => GPhi F M ξ ε z x - GPhi F M ξ ε z' x -
        Lop p M (fun x => z x - z' x) x) x := by
      rw [e2, e1, e3]
      simp only [hT]
      ring
    rw [key, norm_neg]
    have hr2 := norm_linSol_le hp hM (by positivity) hres x
    calc _ ≤ Kap p * (2 * η * D) := hr2
      _ = D / 2 := by rw [hη]; field_simp; ring
  -- `T 0` is small
  have hT0 : ∀ x, ‖T 0 x‖ ≤ r / 2 := by
    intro x
    have hb : ∀ x, ‖GPhi F M ξ ε 0 x‖ ≤ 2 * τ := fun x => by
      rw [gen_Phi_zero_eq F hM]
      have hq : ∀ x', ‖F.Q (ε • ξ x', 0) - F.Q (0, 0)‖ ≤ τ := fun x' => by
        have h := hQc (x := ε • ξ x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have hn : ∀ x', ‖F.N (ε • ξ x', 0) - F.N (0, 0)‖ ≤ τ := fun x' => by
        have h := hNc (x := ε • ξ x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_right _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ τ + τ := add_le_add (hq x) (Mv_norm_le hM hτ0.le hn x)
        _ = 2 * τ := by ring
    have h := norm_linSol_le hp hM (by positivity) hb x
    simp only [hT, Pi.zero_apply, zero_sub, norm_neg]
    calc _ ≤ Kap p * (2 * τ) := h
      _ = r / 2 := by rw [hτ]; field_simp; ring
  have hball : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖T z x‖ ≤ r := by
    intro z hz x
    have h1 := hcontr z 0 hz (fun x => by simp [hr.le]) r (fun x => by simpa using hz x) x
    calc ‖T z x‖ ≤ ‖T z x - T 0 x‖ + ‖T 0 x‖ := by
          have := norm_add_le (T z x - T 0 x) (T 0 x); simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add h1 (hT0 x)
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → X → Fin 4 → ℝ := fun n => T^[n] 0 with hzs
  have hzsB : ∀ n x, ‖zs n x‖ ≤ r := by
    intro n
    induction n with
    | zero => intro x; simp [hzs, hr.le]
    | succ n ih =>
      intro x
      simp only [hzs, Function.iterate_succ_apply']
      exact hball _ ih x
  have hstep : ∀ n x, ‖zs n x - zs (n + 1) x‖ ≤ r / 2 / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hT0 x
    | succ n ih =>
      intro x
      have h := hcontr (zs (n + 1)) (zs n) (hzsB _) (hzsB _) (r / 2 / 2 ^ n)
        (fun x => by rw [norm_sub_rev]; exact ih x) x
      have e1 : zs (n + 1 + 1) = T (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) x = T (zs n) x from congrFun e2 x]
      calc _ ≤ r / 2 / 2 ^ n / 2 := h
        _ = r / 2 / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hcau : ∀ x, CauchySeq fun n => zs n x := fun x =>
    cauchySeq_of_le_geometric_two (C := r) fun n => by rw [dist_eq_norm]; exact hstep n x
  choose z hz using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hzdist : ∀ n x, ‖zs n x - z x‖ ≤ r / 2 ^ n := fun n x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun n => zs n x)
      (fun n => by rw [dist_eq_norm]; exact hstep n x) (hz x) n
    rwa [dist_eq_norm] at this
  have hzB : ∀ x, ‖z x‖ ≤ r := fun x =>
    le_of_tendsto' ((hz x).norm) fun n => hzsB n x
  -- `z` is a fixed point of `T`
  have hfix : T z = z := by
    funext x
    have hlim : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (T z x)) := by
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
      exact hcontr z (zs n) hzB (hzsB n) (r / 2 ^ n) (fun x => by
        rw [norm_sub_rev]; exact hzdist n x) x
    have hlim2 : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (z x)) :=
      (hz x).comp (tendsto_add_atTop_nat 1)
    exact tendsto_nhds_unique hlim hlim2
  refine ⟨z, hzB, ?_⟩
  -- the fixed point solves `Φ = 0`
  have hl : linSol p M (GPhi F M ξ ε z) = 0 := by
    funext x
    have := congrFun hfix x
    simp only [hT] at this
    have h2 : linSol p M (GPhi F M ξ ε z) x = 0 := by
      have := congrArg (fun v => z x - v) this
      simp only [sub_sub_cancel, sub_self] at this
      exact this
    exact h2
  obtain ⟨-, hL⟩ := linSol_spec hp hM (hCQN z hzB) (hPhiB z hzB)
  unfold GEqm
  rw [← hL, hl]
  funext x
  have := congrFun (Lop_sub (p := p) M (0 : X → Fin 4 → ℝ) 0) x
  simp only [Pi.zero_apply, sub_self] at this
  exact this

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**local uniqueness of Markov equilibria,
uniform over state spaces and Markov operators**): under the Taylor principle there is `ρ > 0`,
depending only on the parameters, such that for every state space `X`, every Markov operator `M`,
every disturbance pattern and amplitude with `‖εξ(x)‖ ≤ ρ`, any two Markov equilibria `z, z′` with
`‖z(x)‖, ‖z′(x)‖ ≤ ρ` everywhere coincide. -/
theorem gen_uniqueness (F : NKMaps p k) (hp : p.Std) :
    ∃ ρ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ (ξ : X → Fin k → ℝ) (ε : ℝ) (z z' : X → Fin 4 → ℝ), (∀ x, ‖ε • ξ x‖ ≤ ρ) →
        (∀ x, ‖z x‖ ≤ ρ) → (∀ x, ‖z' x‖ ≤ ρ) → GEqm F M ξ ε z →
          GEqm F M ξ ε z' → z = z' := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_gen F.smoothQ hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_gen F.smoothN hη0
  refine ⟨min ρQ ρN, lt_min hρQ hρN, fun X M hM ξ ε z z' he hz hz' hE hE' => ?_⟩
  set d : X → Fin 4 → ℝ := fun x => z x - z' x with hd
  have hd0 : ∀ x, ‖d x‖ ≤ 2 * min ρQ ρN := fun x => by
    calc ‖d x‖ ≤ ‖z x‖ + ‖z' x‖ := norm_sub_le _ _
      _ ≤ _ := by linarith [hz x, hz' x]
  have himp : ∀ U, (∀ x, ‖d x‖ ≤ U) → ∀ x, ‖d x‖ ≤ 0 + 1 / 2 * U := by
    intro U hU x
    have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU x)
    -- the residual identity
    have hres : ∀ x, Lop p M d x = -(F.Q (ε • ξ x, z x) - F.Q (ε • ξ x, z' x) -
        fderiv ℝ (F.Q) (0, 0) (0, d x)) - Mv M (fun x' => F.N (ε • ξ x', z x') -
          F.N (ε • ξ x', z' x') - fderiv ℝ (F.N) (0, 0) (0, d x')) x := fun x => by
      have h1 := congrFun hE x
      have h2 := congrFun hE' x
      simp only [GPhi, Pi.zero_apply] at h1 h2
      simp only [F.derivQ, F.derivN]
      have e1 := congrFun (Mv_sub M (fun x' => F.N (ε • ξ x', z x') -
        F.N (ε • ξ x', z' x')) (fun x' => DN0 p (d x'))) x
      have e2 := congrFun (Mv_sub M (fun x' => F.N (ε • ξ x', z x'))
        (fun x' => F.N (ε • ξ x', z' x'))) x
      rw [e1, e2]
      simp only [Lop]
      linear_combination h1 - h2
    have hnorm : ∀ x, ‖Lop p M d x‖ ≤ 2 * η * U := fun x => by
      rw [hres x]
      have hzx := (hz x).trans (min_le_left _ _)
      have hz'x := (hz' x).trans (min_le_left _ _)
      have hex := (he x).trans (min_le_left _ _)
      have e1 := hQ (ε • ξ x) (z x) (z' x) hex hzx hz'x
      have e2 : ∀ x', ‖F.N (ε • ξ x', z x') - F.N (ε • ξ x', z' x') -
          fderiv ℝ (F.N) (0, 0) (0, d x')‖ ≤ η * U := fun x' => by
        have := hN (ε • ξ x') (z x') (z' x') ((he x').trans (min_le_right _ _))
          ((hz x').trans (min_le_right _ _)) ((hz' x').trans (min_le_right _ _))
        exact this.trans (mul_le_mul_of_nonneg_left (hU x') hη0.le)
      have e3 := Mv_norm_le hM (mul_nonneg hη0.le hU0) e2 x
      calc _ ≤ ‖-(F.Q (ε • ξ x, z x) - F.Q (ε • ξ x, z' x) -
              fderiv ℝ (F.Q) (0, 0) (0, d x))‖ + ‖Mv M (fun x' => F.N (ε • ξ x', z x') -
              F.N (ε • ξ x', z' x') - fderiv ℝ (F.N) (0, 0) (0, d x')) x‖ :=
            norm_sub_le _ _
        _ ≤ η * U + η * U := by
            rw [norm_neg]
            exact add_le_add (e1.trans (mul_le_mul_of_nonneg_left (hU x) hη0.le)) e3
        _ = 2 * η * U := by ring
    have := apriori hp hM hd0 hnorm x
    calc ‖d x‖ ≤ Kap p * (2 * η * U) := this
      _ = 0 + 1 / 2 * U := by rw [hη]; field_simp; ring
  funext x
  have h := bound_of_improve (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hd0 himp x
  have : d x = 0 := norm_le_zero_iff.1 (by simpa using h)
  exact sub_eq_zero.1 this

/-- Woodford (2003), Ch. 6, §1, App. A.3 and Proposition 4.3 (**EXISTENCE AND LOCAL UNIQUENESS OF
A MARKOV EQUILIBRIUM ON A GENERAL SHOCK SPACE**). Under the Taylor principle there are `r, δ > 0`,
depending ONLY on the parameters, such that for every state space `X`, every Markov operator
`M` (`E_t[h(x_{t+1})] = (Mh)(x_t)`) and every bounded disturbance pattern with `‖εξ(x)‖ ≤ δ`,
there is exactly one Markov equilibrium `z : X → ℝ⁴` with `‖z(x)‖ ≤ r` for all `x`. -/
theorem gen_markov_equilibrium (F : NKMaps p k) (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)), IsMarkov M →
      ∀ (ξ : X → Fin k → ℝ) (ε : ℝ), (∀ x, ‖ε • ξ x‖ ≤ δ) →
        ∃ z : X → Fin 4 → ℝ, ((∀ x, ‖z x‖ ≤ r) ∧ GEqm F M ξ ε z) ∧
          ∀ z' : X → Fin 4 → ℝ, (∀ x, ‖z' x‖ ≤ r) → GEqm F M ξ ε z' → z' = z := by
  obtain ⟨ρ, hρ, huniq⟩ := gen_uniqueness F hp
  obtain ⟨r0, hr0, hex⟩ := gen_existence F hp
  obtain ⟨δ1, hδ1, hex1⟩ := hex (min r0 ρ) (lt_min hr0 hρ) (min_le_left _ _)
  refine ⟨min r0 ρ, lt_min hr0 hρ, min δ1 ρ, lt_min hδ1 hρ, fun X M hM ξ ε hξ => ?_⟩
  obtain ⟨z, hzB, hz⟩ := hex1 X M hM ξ ε fun x => (hξ x).trans (min_le_left _ _)
  refine ⟨z, ⟨hzB, hz⟩, fun z' hz'B hz' => huniq X M hM ξ ε z' z
    (fun x => (hξ x).trans (min_le_right _ _)) (fun x => (hz'B x).trans (min_le_right _ _))
    (fun x => (hzB x).trans (min_le_right _ _)) hz' hz⟩

/-- Woodford (2003), (A.11) (**the exact stochastic equilibrium conditions in sequence space**): the
process `z_t(ω)` with disturbances `e_t(ω)` satisfies, at every date and state, `Q(e_t, z_t) +
E_t[N(e_{t+1}, z_{t+1})] = 0` for generic maps `F : NKMaps` (for the Calvo model: the Euler equation
with the rule, the Calvo recursions, the price index). No Markov structure and no adaptedness are
imposed. -/
def GSeqEqm {Ω : Type*} (F : NKMaps p k) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin k → ℝ)
    (z : ℕ → Ω → Fin 4 → ℝ) : Prop :=
  ∀ t ω, F.Q (e t ω, z t ω) +
    (fun i => 𝔼.E t (fun ω' => F.N (e (t + 1) ω', z (t + 1) ω') i) ω) = 0

/-- The sequence-space conditions are the Markov conditions on `ℕ × Ω` with `seqOp`. -/
theorem gseqEqm_iff {Ω : Type*} (F : NKMaps p k) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin k → ℝ)
    (z : ℕ → Ω → Fin 4 → ℝ) :
    GSeqEqm F 𝔼 e z ↔
      GEqm F (seqOp 𝔼) (fun q => e q.1 q.2) 1 (fun q => z q.1 q.2) := by
  constructor
  · intro h
    funext q
    simp only [GPhi, one_smul, Pi.zero_apply]
    exact h q.1 q.2
  · intro h t ω
    have := congrFun h (t, ω)
    simp only [GPhi, one_smul, Pi.zero_apply] at this
    exact this

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**SEQUENCE-SPACE DETERMINACY: uniqueness among
ALL bounded processes**). Under the Taylor principle there is `ρ > 0` such that for EVERY
expectation system and EVERY disturbance process with `‖e_t(ω)‖ ≤ ρ`, two solutions of the exact
stochastic equilibrium conditions with `‖z_t(ω)‖, ‖z′_t(ω)‖ ≤ ρ` coincide. Neither the Markov
property nor adaptedness is assumed. -/
theorem gen_seq_uniqueness (F : NKMaps p k) (hp : p.Std) :
    ∃ ρ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin k → ℝ)
      (z z' : ℕ → Ω → Fin 4 → ℝ), (∀ t ω, ‖e t ω‖ ≤ ρ) → (∀ t ω, ‖z t ω‖ ≤ ρ) →
        (∀ t ω, ‖z' t ω‖ ≤ ρ) → GSeqEqm F 𝔼 e z → GSeqEqm F 𝔼 e z' → z = z' := by
  obtain ⟨ρ, hρ, h⟩ := gen_uniqueness F hp
  refine ⟨ρ, hρ, fun Ω 𝔼 e z z' he hz hz' hE hE' => ?_⟩
  have := h (ℕ × Ω) (seqOp 𝔼) (seqOp_isMarkov 𝔼) (fun q => e q.1 q.2) 1
    (fun q => z q.1 q.2) (fun q => z' q.1 q.2) (fun q => by simpa using he q.1 q.2)
    (fun q => hz q.1 q.2) (fun q => hz' q.1 q.2) ((gseqEqm_iff F 𝔼 e z).1 hE)
    ((gseqEqm_iff F 𝔼 e z').1 hE')
  funext t ω
  exact congrFun this (t, ω)

/-- Woodford (2003), App. A.3 (**sequence-space existence**): for every expectation system and
every disturbance process with `‖e_t(ω)‖ ≤ δ`, a bounded solution of the exact stochastic
equilibrium conditions within `r` exists, and it is the only one within `r`. -/
theorem gen_seq_existence (F : NKMaps p k) (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin k → ℝ),
      (∀ t ω, ‖e t ω‖ ≤ δ) → ∃ z : ℕ → Ω → Fin 4 → ℝ, ((∀ t ω, ‖z t ω‖ ≤ r) ∧
        GSeqEqm F 𝔼 e z) ∧ ∀ z' : ℕ → Ω → Fin 4 → ℝ, (∀ t ω, ‖z' t ω‖ ≤ r) →
          GSeqEqm F 𝔼 e z' → z' = z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := gen_markov_equilibrium F hp
  refine ⟨r, hr, δ, hδ, fun Ω 𝔼 e he => ?_⟩
  obtain ⟨z, ⟨hzB, hz⟩, hu⟩ := h (ℕ × Ω) (seqOp 𝔼) (seqOp_isMarkov 𝔼) (fun q => e q.1 q.2) 1
    (fun q => by simpa using he q.1 q.2)
  refine ⟨fun t ω => z (t, ω), ⟨fun t ω => hzB (t, ω), (gseqEqm_iff F 𝔼 e _).2 hz⟩,
    fun z' hz'B hz' => ?_⟩
  have := hu (fun q => z' q.1 q.2) (fun q => hz'B q.1 q.2) ((gseqEqm_iff F 𝔼 e z').1 hz')
  funext t ω; exact congrFun this (t, ω)

/-! ## Almost surely on a filtered probability space -/

variable {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- Woodford (2003), (A.11) on a probability space (**the exact stochastic conditions almost
surely**): `Q(e_t, z_t) + μ[N(e_{t+1}, z_{t+1}) | 𝓕_t] = 0` a.s. at every date. -/
def GSeqEqmAE (F : NKMaps p k) (e : ℕ → Ω → Fin k → ℝ) (z : ℕ → Ω → Fin 4 → ℝ) : Prop :=
  ∀ t, (fun ω => F.Q (e t ω, z t ω) + MvA E (fun s ω' => F.N (e s ω', z s ω')) t ω)
    =ᵐ[E.μ] 0

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**SEQUENCE-SPACE DETERMINACY ON A GENERAL
PROBABILITY SPACE**): under the Taylor principle there is `ρ > 0` such that on every filtered
probability space, for every a.s. measurable disturbance process with `‖e_t‖ ≤ ρ` a.s., two
a.s. measurable solutions of the exact conditions with Mathlib's conditional expectations and
`‖z_t‖, ‖z′_t‖ ≤ ρ` a.s. coincide almost surely at every date. -/
theorem gen_seq_uniqueness_ae (F : NKMaps p k) (hp : p.Std) :
    ∃ ρ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin k → ℝ) (z z' : ℕ → Ω → Fin 4 → ℝ), Gd E e → Gd E z → Gd E z' →
        Bd E e ρ → Bd E z ρ → Bd E z' ρ → GSeqEqmAE E F e z → GSeqEqmAE E F e z' →
          ∀ t, z t =ᵐ[E.μ] z' t := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_gen F.smoothQ hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_gen F.smoothN hη0
  set ρ := min ρQ ρN with hρdef
  have hρ0 : 0 < ρ := lt_min hρQ hρN
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ))
    ρ).exists_bound_of_continuousOn (F.smoothN.continuous.continuousOn)
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hρ0.le))
  refine ⟨ρ, hρ0, fun Ω _ E e z z' he hz hz' heb hzb hz'b hE hE' => ?_⟩
  have hNb : ∀ w : ℕ → Ω → Fin 4 → ℝ, Bd E w ρ →
      Bd E (fun s ω => F.N (e s ω, w s ω)) CN := fun w hw t => by
    filter_upwards [heb t, hw t] with ω h1 h2
    exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]; exact max_le h1 h2)
  have hNg : ∀ w : ℕ → Ω → Fin 4 → ℝ, Gd E w → Gd E (fun s ω => F.N (e s ω, w s ω)) :=
    fun w hw => gd_pair E F.smoothN.continuous he hw
  set d : ℕ → Ω → Fin 4 → ℝ := fun s ω => z s ω - z' s ω with hd
  have hdG : Gd E d := fun t => (hz t).sub (hz' t)
  have hdb : Bd E d (2 * ρ) := fun t => by
    filter_upwards [hzb t, hz'b t] with ω h1 h2
    exact (norm_sub_le _ _).trans (by linarith)
  have himp : ∀ U, Bd E d U → Bd E d (0 + 1 / 2 * U) := by
    intro U hU
    by_cases hU0 : 0 ≤ U
    · -- the residual bound
      have hRN : Bd E (fun s ω => F.N (e s ω, z s ω) - F.N (e s ω, z' s ω) -
          DN0 p (d s ω)) (η * U) := fun t => by
        filter_upwards [heb t, hzb t, hz'b t, hU t] with ω h1 h2 h3 h4
        have := hN (e t ω) (z t ω) (z' t ω) (h1.trans (min_le_right _ _))
          (h2.trans (min_le_right _ _)) (h3.trans (min_le_right _ _))
        rw [F.derivN] at this
        exact this.trans (mul_le_mul_of_nonneg_left h4 hη0.le)
      have hDNg : Gd E (fun s ω => DN0 p (d s ω)) := fun t =>
        ((gd_pair E (φ := fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) => DN0 p q.1) (by
          refine continuous_pi fun i => ?_
          fin_cases i <;> simp only [DN0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
            Fin.isValue, Matrix.cons_val] <;> fun_prop) hdG hdG) t)
      have hDNb : Bd E (fun s ω => DN0 p (d s ω))
          (‖fderiv ℝ (F.N) (0, 0)‖ * (2 * ρ)) := fun t => by
        filter_upwards [hdb t] with ω hω
        rw [← F.derivN]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left (by rw [gnorm_pair_zero]; exact hω) (norm_nonneg _))
      have hNdg : Gd E (fun s ω => F.N (e s ω, z s ω) - F.N (e s ω, z' s ω)) := fun t =>
        ((hNg z hz) t).sub ((hNg z' hz') t)
      have hNdb : Bd E (fun s ω => F.N (e s ω, z s ω) - F.N (e s ω, z' s ω)) (CN + CN) :=
        fun t => by
          filter_upwards [hNb z hzb t, hNb z' hz'b t] with ω h1 h2
          exact (norm_sub_le _ _).trans (add_le_add h1 h2)
      have hLd : Bd E (LopA E p d) (2 * η * U) := by
        intro t
        have s1 := MvA_sub E (hNg z hz) (hNg z' hz') (hNb z hzb) (hNb z' hz'b) t
        have s2 := MvA_sub E hNdg hDNg hNdb hDNb t
        have hRb := MvA_bd E (mul_nonneg hη0.le hU0) hRN t
        filter_upwards [hE t, hE' t, s1, s2, hRb, heb t, hzb t, hz'b t, hU t]
          with ω e1 e2 m1 m2 hR h1 h2 h3 h4
        simp only [Pi.zero_apply] at e1 e2
        have hQx := hQ (e t ω) (z t ω) (z' t ω) (h1.trans (min_le_left _ _))
          (h2.trans (min_le_left _ _)) (h3.trans (min_le_left _ _))
        rw [F.derivQ] at hQx
        have m2' : MvA E (fun s ω => F.N (e s ω, z s ω) - F.N (e s ω, z' s ω) -
            DN0 p (d s ω)) t ω = MvA E (fun s ω => F.N (e s ω, z s ω)) t ω -
              MvA E (fun s ω => F.N (e s ω, z' s ω)) t ω -
              MvA E (fun s ω => DN0 p (d s ω)) t ω := by
          rw [m2, m1]
        have key : LopA E p d t ω = -(F.Q (e t ω, z t ω) - F.Q (e t ω, z' t ω) -
            DQ0 p (z t ω - z' t ω)) - MvA E (fun s ω => F.N (e s ω, z s ω) -
              F.N (e s ω, z' s ω) - DN0 p (d s ω)) t ω := by
          rw [m2']
          simp only [LopA, hd]
          linear_combination (norm := abel_nf) e1 - e2
        rw [key]
        calc _ ≤ _ := norm_sub_le _ _
          _ ≤ η * U + η * U := by
              rw [norm_neg]
              exact add_le_add (hQx.trans (mul_le_mul_of_nonneg_left h4 hη0.le)) hR
          _ = 2 * η * U := by ring
      have h := apriori_ae E hp hdG (by positivity) hdb (by positivity) hLd
      intro t
      filter_upwards [h t] with ω hω
      calc _ ≤ _ := hω
        _ = 0 + 1 / 2 * U := by rw [hη]; field_simp; ring
    · intro t
      have : ∀ᵐ ω ∂E.μ, False := by
        filter_upwards [hU t] with ω hω; exact hU0 ((norm_nonneg _).trans hω)
      filter_upwards [this] with ω hω; exact hω.elim
  have h0 := bound_improve_ae E (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hdb himp
  intro t
  filter_upwards [h0 t] with ω hω
  have : d t ω = 0 := norm_le_zero_iff.1 (by simpa using hω)
  exact sub_eq_zero.1 this

/-- Woodford (2003), (A.11) a.s.: the residual of the exact stochastic conditions,
`Q(e_t, z_t) + μ[N(e_{t+1}, z_{t+1}) | 𝓕_t]`. -/
noncomputable def GPhiA (F : NKMaps p k) (e : ℕ → Ω → Fin k → ℝ) (z : ℕ → Ω → Fin 4 → ℝ) :
    ℕ → Ω → Fin 4 → ℝ :=
  fun t ω => F.Q (e t ω, z t ω) + MvA E (fun s ω' => F.N (e s ω', z s ω')) t ω

/-- Woodford (2003), App. A.3 a.s. (**the residual minus its linearisation is small**). -/
theorem gen_resid_ae (F : NKMaps p k) {η ρQ ρN : ℝ} (hη0 : 0 ≤ η)
    (hQ : ∀ e w w', ‖e‖ ≤ ρQ → ‖w‖ ≤ ρQ → ‖w'‖ ≤ ρQ →
      ‖F.Q (e, w) - F.Q (e, w') - fderiv ℝ (F.Q) (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    (hN : ∀ e w w', ‖e‖ ≤ ρN → ‖w‖ ≤ ρN → ‖w'‖ ≤ ρN →
      ‖F.N (e, w) - F.N (e, w') - fderiv ℝ (F.N) (0, 0) (0, w - w')‖ ≤ η * ‖w - w'‖)
    {CN : ℝ} (hCN : ∀ q ∈ Metric.closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ)) (min ρQ ρN),
      ‖F.N q‖ ≤ CN)
    {e : ℕ → Ω → Fin k → ℝ} {z z' : ℕ → Ω → Fin 4 → ℝ} (he : Gd E e) (hz : Gd E z)
    (hz' : Gd E z') (heb : Bd E e (min ρQ ρN)) (hzb : Bd E z (min ρQ ρN))
    (hz'b : Bd E z' (min ρQ ρN)) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : Bd E (fun s ω => z s ω - z' s ω) D) :
    Bd E (fun s ω => GPhiA E F e z s ω - GPhiA E F e z' s ω -
      LopA E p (fun s ω => z s ω - z' s ω) s ω) (2 * η * D) := by
  set ρ := min ρQ ρN
  have hNb : ∀ w : ℕ → Ω → Fin 4 → ℝ, Bd E w ρ →
      Bd E (fun s ω => F.N (e s ω, w s ω)) CN := fun w hw t => by
    filter_upwards [heb t, hw t] with ω h1 h2
    exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]; exact max_le h1 h2)
  have hNg : ∀ w : ℕ → Ω → Fin 4 → ℝ, Gd E w → Gd E (fun s ω => F.N (e s ω, w s ω)) :=
    fun w hw => gd_pair E F.smoothN.continuous he hw
  set d : ℕ → Ω → Fin 4 → ℝ := fun s ω => z s ω - z' s ω with hd
  have hdG : Gd E d := fun t => (hz t).sub (hz' t)
  have hRN : Bd E (fun s ω => F.N (e s ω, z s ω) - F.N (e s ω, z' s ω) -
      DN0 p (d s ω)) (η * D) := fun t => by
    filter_upwards [heb t, hzb t, hz'b t, hD t] with ω h1 h2 h3 h4
    have := hN (e t ω) (z t ω) (z' t ω) (h1.trans (min_le_right _ _))
      (h2.trans (min_le_right _ _)) (h3.trans (min_le_right _ _))
    rw [F.derivN] at this
    exact this.trans (mul_le_mul_of_nonneg_left h4 hη0)
  have hNdg : Gd E (fun s ω => F.N (e s ω, z s ω) - F.N (e s ω, z' s ω)) := fun t =>
    ((hNg z hz) t).sub ((hNg z' hz') t)
  have hNdb : Bd E (fun s ω => F.N (e s ω, z s ω) - F.N (e s ω, z' s ω)) (CN + CN) :=
    fun t => by
      filter_upwards [hNb z hzb t, hNb z' hz'b t] with ω h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  intro t
  have s1 := MvA_sub E (hNg z hz) (hNg z' hz') (hNb z hzb) (hNb z' hz'b) t
  have s2 := MvA_sub E hNdg (gd_DN0 E (p := p) hdG) hNdb (bd_DN0 E (p := p) hD) t
  have hRb := MvA_bd E (mul_nonneg hη0 hD0) hRN t
  filter_upwards [s1, s2, hRb, heb t, hzb t, hz'b t, hD t] with ω m1 m2 hR h1 h2 h3 h4
  have hQx := hQ (e t ω) (z t ω) (z' t ω) (h1.trans (min_le_left _ _))
    (h2.trans (min_le_left _ _)) (h3.trans (min_le_left _ _))
  rw [F.derivQ] at hQx
  have key : GPhiA E F e z t ω - GPhiA E F e z' t ω - LopA E p d t ω =
      (F.Q (e t ω, z t ω) - F.Q (e t ω, z' t ω) - DQ0 p (z t ω - z' t ω)) +
      MvA E (fun s ω => F.N (e s ω, z s ω) - F.N (e s ω, z' s ω) - DN0 p (d s ω)) t ω := by
    rw [m2, m1]
    simp only [GPhiA, LopA, hd]
    abel
  rw [key]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ η * D + η * D := add_le_add (hQx.trans (mul_le_mul_of_nonneg_left h4 hη0)) hR
    _ = 2 * η * D := by ring

/-- Woodford (2003), App. A.3 (**invariant-set form of the a.s. existence theorem**): for every
radius `r ≤ r0` there is `δ > 0` such that, for a.s. measurable disturbances with `‖e_t‖ ≤ δ`,
the Newton–Picard solution within `r` belongs to every property `A` of processes holding at `0`,
preserved by the Newton step on processes within `r`, and closed under a.s. limits. -/
theorem gen_seq_existence_ae_inv (F : NKMaps p k) (hp : p.Std) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (e : ℕ → Ω → Fin k → ℝ), Gd E e → Bd E e δ →
        ∀ A : (ℕ → Ω → Fin 4 → ℝ) → Prop, A (fun _ _ => 0) →
          (∀ z, Gd E z → Bd E z r → A z →
            A (fun t ω => z t ω - linSolA E p (GPhiA E F e z) t ω)) →
          (∀ (zs : ℕ → ℕ → Ω → Fin 4 → ℝ) (z : ℕ → Ω → Fin 4 → ℝ), (∀ n, A (zs n)) →
            (∀ t, ∀ᵐ ω ∂E.μ, Tendsto (fun n => zs n t ω) atTop (𝓝 (z t ω))) → A z) →
        ∃ z : ℕ → Ω → Fin 4 → ℝ, (Gd E z ∧ Bd E z r ∧ GSeqEqmAE E F e z) ∧ A z := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_gen F.smoothQ hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_gen F.smoothN hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn (F.smoothQ.continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn (F.smoothN.continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr00.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr00.le))
  refine ⟨r0, hr00, fun r hr0' hrr0 => ?_⟩
  set τ := r / (4 * Kap p) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcQ : ContinuousAt (fun e : Fin k → ℝ => F.Q (e, 0)) 0 :=
    (F.smoothQ.continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  have hcN : ContinuousAt (fun e : Fin k → ℝ => F.N (e, 0)) 0 :=
    (F.smoothN.continuous.comp (continuous_id.prodMk continuous_const))
      |>.continuousAt
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 hcQ τ hτ0
  obtain ⟨δN, hδN, hNc⟩ := Metric.continuousAt_iff.1 hcN τ hτ0
  set δ := min r (min (δQ / 2) (δN / 2)) with hδ
  have hδ0 : 0 < δ := lt_min hr0' (lt_min (by positivity) (by positivity))
  refine ⟨δ, hδ0, fun Ω _ E e he heb A hA0 hAT hAlim => ?_⟩
  have heb0 : Bd E e r0 := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans ((min_le_left _ _).trans hrr0)
  -- `Φ` is good and bounded on the ball
  have hPhiG : ∀ z, Gd E z → Gd E (GPhiA E F e z) := fun z hz =>
    gd_add E (gd_pair E F.smoothQ.continuous he hz) (MvA_gd E _)
  have hPhiB : ∀ z, Bd E z r → Bd E (GPhiA E F e z) (CQ + CN) := fun z hz t => by
    have hNb : Bd E (fun s ω => F.N (e s ω, z s ω)) CN := fun t => by
      filter_upwards [heb0 t, hz t] with ω h1 h2
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                      exact max_le h1 (h2.trans hrr0))
    filter_upwards [heb0 t, hz t, MvA_bd E hCN0 hNb t] with ω h1 h2 h3
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le h1 (h2.trans hrr0))) h3)
  -- the Newton map
  set T : (ℕ → Ω → Fin 4 → ℝ) → (ℕ → Ω → Fin 4 → ℝ) :=
    fun z t ω => z t ω - linSolA E p (GPhiA E F e z) t ω with hT
  have hTG : ∀ z, Gd E z → Bd E z r → Gd E (T z) := fun z hz hzb t =>
    (hz t).sub ((linSolA_spec E hp (hPhiG z hz) (add_nonneg hCQ0 hCN0) (hPhiB z hzb)).1 t)
  have hcontr : ∀ z z', Gd E z → Gd E z' → Bd E z r → Bd E z' r → ∀ D, 0 ≤ D →
      Bd E (fun s ω => z s ω - z' s ω) D → Bd E (fun s ω => T z s ω - T z' s ω) (D / 2) := by
    intro z z' hz hz' hzb hz'b D hD0 hD
    have hzb0 : Bd E z r0 := fun t => by
      filter_upwards [hzb t] with ω hω; exact hω.trans hrr0
    have hz'b0 : Bd E z' r0 := fun t => by
      filter_upwards [hz'b t] with ω hω; exact hω.trans hrr0
    have hR := gen_resid_ae E F hη0.le hQ hN hCN he hz hz' heb0 hzb0 hz'b0 hD0 hD
    have hdG : Gd E (fun s ω => z s ω - z' s ω) := fun t => (hz t).sub (hz' t)
    have hLd := bd_LopA E (p := p) hD0 hD
    have hPd : Bd E (fun s ω => GPhiA E F e z s ω - GPhiA E F e z' s ω) (CQ + CN + (CQ + CN)) :=
      fun t => by
        filter_upwards [hPhiB z hzb t, hPhiB z' hz'b t] with ω h1 h2
        exact (norm_sub_le _ _).trans (add_le_add h1 h2)
    have hPdG : Gd E (fun s ω => GPhiA E F e z s ω - GPhiA E F e z' s ω) := fun t =>
      ((hPhiG z hz) t).sub ((hPhiG z' hz') t)
    have e1 := linSolA_sub E hp (hPhiG z hz) (hPhiG z' hz') (add_nonneg hCQ0 hCN0)
      (add_nonneg hCQ0 hCN0) (hPhiB z hzb) (hPhiB z' hz'b)
    have e2 := linSolA_sub E hp hPdG (gd_LopA E hdG) (by positivity)
      (mul_nonneg (by positivity) hD0) hPd hLd
    have e3 := linSolA_Lop E hp hdG hD0 hD
    have hRG : Gd E (fun s ω => GPhiA E F e z s ω - GPhiA E F e z' s ω -
        LopA E p (fun s ω => z s ω - z' s ω) s ω) := fun t => (hPdG t).sub (gd_LopA E hdG t)
    have hb := bd_linSolA E hp hRG (by positivity) hR
    intro t
    filter_upwards [e1 t, e2 t, e3 t, hb t] with ω h1 h2 h3 h4
    have key : T z t ω - T z' t ω = -linSolA E p (fun s ω => GPhiA E F e z s ω -
        GPhiA E F e z' s ω - LopA E p (fun s ω => z s ω - z' s ω) s ω) t ω := by
      rw [h2]
      simp only [hT]
      rw [h1, h3]
      abel
    rw [key, norm_neg]
    calc _ ≤ _ := h4
      _ = D / 2 := by rw [hη]; field_simp; ring
  -- `T 0` is small
  have hT0 : Bd E (T fun _ _ => 0) (r / 2) := by
    have hb : Bd E (GPhiA E F e fun _ _ => 0) (2 * τ) := fun t => by
      have hs : F.Q (0, 0) + F.N (0, 0) = 0 := F.steady
      have hNg : Gd E (fun s ω => F.N (e s ω, (0 : Fin 4 → ℝ))) :=
        gd_pair E F.smoothN.continuous he
        (fun _ => aestronglyMeasurable_const)
      have hNb : Bd E (fun s ω => F.N (e s ω, (0 : Fin 4 → ℝ))) CN := fun t => by
        filter_upwards [heb0 t] with ω h1
        exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                        exact max_le h1 (by simp [hr00.le]))
      have m := MvA_sub E hNg (fun _ => aestronglyMeasurable_const) hNb
        (C := CN) (D := ‖F.N (0, 0)‖) (h := fun s ω => F.N (e s ω, 0))
        (g := fun _ _ => F.N (0, 0)) (fun _ => Eventually.of_forall fun _ => le_rfl) t
      have hbN : Bd E (fun s ω => F.N (e s ω, (0 : Fin 4 → ℝ)) - F.N (0, 0)) τ :=
        fun t => by
          filter_upwards [heb t] with ω h1
          have h := hNc (x := e t ω) (by
            rw [dist_zero_right]; exact lt_of_le_of_lt (h1.trans
              ((min_le_right _ _).trans (min_le_right _ _))) (by linarith))
          rw [dist_eq_norm] at h; exact h.le
      filter_upwards [heb t, m, MvA_bd E hτ0.le hbN t] with ω h1 hm h3
      have hq : ‖F.Q (e t ω, 0) - F.Q (0, 0)‖ ≤ τ := by
        have h := hQc (x := e t ω) (by
          rw [dist_zero_right]; exact lt_of_le_of_lt (h1.trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have key : GPhiA E F e (fun _ _ => 0) t ω = (F.Q (e t ω, 0) - F.Q (0, 0)) +
          MvA E (fun s ω => F.N (e s ω, 0) - F.N (0, 0)) t ω := by
        rw [hm, MvA_const]
        simp only [GPhiA]
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
  have hl0 : ∀ t, linSolA E p (GPhiA E F e z) t =ᵐ[E.μ] fun _ => 0 := fun t => by
    filter_upwards [hfix t] with ω hω
    have := congrArg (fun v => z t ω - v) hω
    simp only [hT, sub_sub_cancel, sub_self] at this
    exact this
  obtain ⟨-, -, hL⟩ := linSolA_spec E hp (hPhiG z hzG) (add_nonneg hCQ0 hCN0) (hPhiB z hzB)
  have hEq : GSeqEqmAE E F e z := fun t => by
    have hc := LopA_congr E (p := p) hl0 t
    rw [LopA_zero] at hc
    filter_upwards [hL t, hc] with ω h1 h2
    change GPhiA E F e z t ω = 0
    rw [← h1, h2]
  exact ⟨z, ⟨hzG, hzB, hEq⟩, hAlim zs z hzsA hconv⟩

/-- Woodford (2003), (A.11): the residual of an adapted process with adapted disturbances is
adapted. -/
theorem gen_adA_PhiA (F : NKMaps p k) {e : ℕ → Ω → Fin k → ℝ} {z : ℕ → Ω → Fin 4 → ℝ} (he : AdA E e)
    (hz : AdA E z) : AdA E (GPhiA E F e z) := fun t =>
  (F.smoothQ.continuous.comp_aestronglyMeasurable
    ((he t).prodMk (hz t))).add (adA_MvA E _ t)

/-- Woodford (2003), App. A.3, p. 633, on a general probability space (**the a.s. unique
equilibrium is ADAPTED**): under the Taylor principle there is `r₁ > 0` such that for every
radius `0 < r ≤ r₁` there is `δ > 0` such that on every filtered probability space, for every
adapted, a.s. measurable disturbance process with `‖e_t‖ ≤ δ` a.s., the solution of the exact
stochastic conditions within `r` is adapted (each `z_{t}` a.s. equal to an `𝓕_t`-strongly
measurable variable) and is a.s. unique within `r`. -/
theorem gen_seq_existence_ae_adapted (F : NKMaps p k) (hp : p.Std) :
    ∃ r1 > 0, ∀ r, 0 < r → r ≤ r1 → ∃ δ > 0, ∀ (Ω : Type*) [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (e : ℕ → Ω → Fin k → ℝ), Gd E e → Bd E e δ → AdA E e →
        ∃ z : ℕ → Ω → Fin 4 → ℝ, ((Gd E z ∧ Bd E z r ∧ GSeqEqmAE E F e z) ∧ AdA E z) ∧
          ∀ z' : ℕ → Ω → Fin 4 → ℝ, Gd E z' → Bd E z' r → GSeqEqmAE E F e z' →
            ∀ t, z' t =ᵐ[E.μ] z t := by
  obtain ⟨ρu, hρu, huniq⟩ := gen_seq_uniqueness_ae F hp
  obtain ⟨r0, hr0, hex⟩ := gen_seq_existence_ae_inv F hp
  refine ⟨min r0 ρu, lt_min hr0 hρu, fun r hr0' hrr => ?_⟩
  have hrr0 : r ≤ r0 := hrr.trans (min_le_left _ _)
  have hrρ : r ≤ ρu := hrr.trans (min_le_right _ _)
  obtain ⟨δ1, hδ1, hex1⟩ := hex r hr0' hrr0
  set δ := min δ1 ρu with hδ
  refine ⟨δ, lt_min hδ1 hρu, fun Ω _ E e he heb heA => ?_⟩
  have heb1 : Bd E e δ1 := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans (min_le_left _ _)
  set R := max δ r with hR
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ))
    R).exists_bound_of_continuousOn (F.smoothQ.continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin 4 → ℝ))
    R).exists_bound_of_continuousOn (F.smoothN.continuous.continuousOn)
  have hR0 : 0 ≤ R := le_max_of_le_right hr0'.le
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hR0))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hR0))
  have hPhiB : ∀ z, Bd E z r → Bd E (GPhiA E F e z) (CQ + CN) := fun z hz t => by
    have hNb : Bd E (fun s ω => F.N (e s ω, z s ω)) CN := fun t => by
      filter_upwards [heb t, hz t] with ω h1 h2
      exact hCN _ (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
                      exact max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)))
    filter_upwards [heb t, hz t, MvA_bd E hCN0 hNb t] with ω h1 h2 h3
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (by
      rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
      exact max_le (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)))) h3)
  have hPhiG : ∀ z, Gd E z → Gd E (GPhiA E F e z) := fun z hz =>
    gd_add E (gd_pair E F.smoothQ.continuous he hz) (MvA_gd E _)
  obtain ⟨z, ⟨hzG, hzB, hzE⟩, hzA⟩ := hex1 Ω E e he heb1 (AdA E)
    (fun t => aestronglyMeasurable_const)
    (fun z hzG hzB hzA t => (hzA t).sub (adA_linSolA E hp (hPhiG z hzG) (add_nonneg hCQ0 hCN0)
      (hPhiB z hzB) (gen_adA_PhiA E F heA hzA) t))
    (fun zs z hzs hlim t => aesmSub_lim (fun n => hzs n t) (hlim t))
  refine ⟨z, ⟨⟨hzG, hzB, hzE⟩, hzA⟩, fun z' hz'G hz'B hz' => ?_⟩
  have hb : Bd E e ρu := fun t => by
    filter_upwards [heb t] with ω hω; exact hω.trans (min_le_right _ _)
  exact huniq Ω E e z' z he hz'G hzG hb (fun t => by
      filter_upwards [hz'B t] with ω hω; exact hω.trans hrρ)
    (fun t => by filter_upwards [hzB t] with ω hω; exact hω.trans hrρ) hz' hzE

end Woodford.StabilizationWelfare.TidyR5GovNewton
