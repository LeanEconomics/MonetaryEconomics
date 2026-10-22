/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovGeneral
import StabilizationWelfare.ExpectationsFiniteTree

/-!
# Adaptedness of the sequence-space equilibrium

Woodford (2003), *Interest and Prices*, Appendix A.3, p. 633 ("endogenous variables … functions
of the state"), and Chapter 6, §1.

`NonlinearNKMarkovGeneral.seq_existence` gives, for any `ExpectationSystem` and any bounded
disturbance process, a unique bounded solution of the exact stochastic equilibrium conditions near
the steady state, without asserting adaptedness. This module proves that the solution is constant on
the date-`t` information cells whenever the disturbances are (`seq_existence_cellConst`), and hence
ADAPTED (`E_t z_t = z_t`) when the expectation system is informationally closed
(`seq_existence_adapted`).

* The informational-closure notions `Indist`, `CellConst`, `InfoClosed`, `cellConst_of_known`,
  `cellConst_E`, `finiteTree_infoClosed` are restated from the Woodford Chapter 2 project
  (`PriceLevelDetermination.LocalIFTStochastic`).
* `general_existence_inv`: the Newton–Picard existence proof of
  `NonlinearNKMarkovGeneral.general_existence` keeps the fixed point inside every set that
  contains `0`, is invariant under the Newton map and is closed under pointwise limits.
* Cell-constancy is a pointwise property, so it passes through the forward series, the inverse
  `linSol` and the residual (`cc_Mv`, `cc_iter`, `cc_fwdSol`, `cc_linSol`, `cc_Phi`), and through
  the Picard limit; no interchange of `E_t` and limits is needed. Informational closure is used
  only at the end, to turn cell-constancy into `E_t z_t = z_t`.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovAdapted

open Filter Topology Asymptotics
open NonlinearNKMarkov NonlinearNKMarkovLinks NonlinearNKMarkovGeneral

variable {p : Par} {X : Type*}

/-- Woodford (2003), App. A.3 (**existence with an invariant**): the Newton–Picard fixed point of
`NonlinearNKMarkovGeneral.general_existence` lies in every set containing `0`, invariant under
the Newton map `z ↦ z − L⁻¹Φ(ε, z)` and closed under pointwise limits. -/
theorem general_existence_inv (hp : p.Std) :
    ∃ r0 > 0, ∀ r, 0 < r → r ≤ r0 → ∃ δ > 0, ∀ (X : Type*) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)),
      IsMarkov M → ∀ (ξ : X → Fin 5 → ℝ) (ε : ℝ), (∀ x, ‖ε • ξ x‖ ≤ δ) →
        ∀ A : (X → Fin 4 → ℝ) → Prop, A 0 →
          (∀ z, A z → A (fun x => z x - linSol p M (Phi p M ξ ε z) x)) →
          (∀ (zs : ℕ → X → Fin 4 → ℝ) (z : X → Fin 4 → ℝ), (∀ n, A (zs n)) →
            (∀ x, Tendsto (fun n => zs n x) atTop (𝓝 (z x))) → A z) →
        ∃ z : X → Fin 4 → ℝ, ((∀ x, ‖z x‖ ≤ r) ∧ IsMarkovEqm p M ξ ε z) ∧ A z := by
  have hK := Kap_pos hp
  set η := 1 / (4 * Kap p) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_small (contDiff_Qmap (p := p) (n := 1)) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_small (contDiff_Nmap (p := p) (n := 1)) hη0
  set r0 := min ρQ ρN with hr0
  have hr00 : 0 < r0 := lt_min hρQ hρN
  -- bounds of `Q`, `N` on the ball
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Qmap (p := p) (n := 0)).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ))
    r0).exists_bound_of_continuousOn ((contDiff_Nmap (p := p) (n := 0)).continuous.continuousOn)
  refine ⟨r0, hr00, fun r hr hrr0 => ?_⟩
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
  refine ⟨min r (min (δQ / 2) (δN / 2)), lt_min hr (lt_min (by positivity) (by positivity)),
    fun X M hM ξ ε hξ A hA0 hAT hAlim => ?_⟩
  have hξr : ∀ x, ‖ε • ξ x‖ ≤ r := fun x => (hξ x).trans (min_le_left _ _)
  have hξ0 : ∀ x, ‖ε • ξ x‖ ≤ r0 := fun x => (hξr x).trans hrr0
  -- `Φ` is bounded on the ball
  have hPhiB : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → ∀ x, ‖Phi p M ξ ε z x‖ ≤ CQ + CN := by
    intro z hz x
    have hin : ∀ x', (ε • ξ x', z x') ∈ Metric.closedBall (0 : (Fin 5 → ℝ) × (Fin 4 → ℝ)) r0 :=
      fun x' => by
        rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
        exact max_le (hξ0 x') ((hz x').trans hrr0)
    have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN _ (hin x))
    exact (norm_add_le _ _).trans (add_le_add (hCQ _ (hin x))
      (Mv_norm_le hM hCN0 (fun x' => hCN _ (hin x')) x))
  -- the Newton map
  set T : (X → Fin 4 → ℝ) → (X → Fin 4 → ℝ) := fun z x => z x - linSol p M (Phi p M ξ ε z) x
    with hT
  have hCQN : ∀ z : X → Fin 4 → ℝ, (∀ x, ‖z x‖ ≤ r) → 0 ≤ CQ + CN := fun z hz => by
    by_cases hX : Nonempty X
    · obtain ⟨x⟩ := hX; exact (norm_nonneg _).trans (hPhiB z hz x)
    · have hin : ((0 : Fin 5 → ℝ), (0 : Fin 4 → ℝ)) ∈ Metric.closedBall 0 r0 :=
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
    have hres := resid_diff_bound (p := p) hM hη0.le hQ hN hξ0 hz0 hz'0 hD
    -- `T z − T z′ = −L⁻¹(Φz − Φz′ − L(z − z′))`
    have e1 := linSol_sub hp hM hC hC (hPhiB z hz) (hPhiB z' hz')
    have e2 := linSol_sub hp hM (a := CQ + CN + (CQ + CN)) (a' := c) (by positivity) hc0
      (r := fun x => Phi p M ξ ε z x - Phi p M ξ ε z' x)
      (fun x => (norm_sub_le _ _).trans (add_le_add (hPhiB z hz x) (hPhiB z' hz' x))) hLd
    have e3 := linSol_Lop hp hM hD0 hD
    have key : T z x - T z' x = -linSol p M (fun x => Phi p M ξ ε z x - Phi p M ξ ε z' x -
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
    have hb : ∀ x, ‖Phi p M ξ ε 0 x‖ ≤ 2 * τ := fun x => by
      rw [Phi_zero_eq hM]
      have hq : ∀ x', ‖Qmap p (ε • ξ x', 0) - Qmap p (0, 0)‖ ≤ τ := fun x' => by
        have h := hQc (x := ε • ξ x') (by
          rw [dist_zero_right]; exact lt_of_le_of_lt ((hξ x').trans
            ((min_le_right _ _).trans (min_le_left _ _))) (by linarith))
        rw [dist_eq_norm] at h; exact h.le
      have hn : ∀ x', ‖Nmap p (ε • ξ x', 0) - Nmap p (0, 0)‖ ≤ τ := fun x' => by
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
  have hzsA : ∀ n, A (zs n) := by
    intro n
    induction n with
    | zero => simpa [hzs] using hA0
    | succ n ih =>
      have e : zs (n + 1) = T (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e]; exact hAT _ ih
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
  refine ⟨z, ⟨hzB, ?_⟩, hAlim zs z hzsA hz⟩
  -- the fixed point solves `Φ = 0`
  have hl : linSol p M (Phi p M ξ ε z) = 0 := by
    funext x
    have := congrFun hfix x
    simp only [hT] at this
    have h2 : linSol p M (Phi p M ξ ε z) x = 0 := by
      have := congrArg (fun v => z x - v) this
      simp only [sub_sub_cancel, sub_self] at this
      exact this
    exact h2
  obtain ⟨-, hL⟩ := linSol_spec hp hM (hCQN z hzB) (hPhiB z hzB)
  unfold IsMarkovEqm
  rw [← hL, hl]
  funext x
  have := congrFun (Lop_sub (p := p) M (0 : X → Fin 4 → ℝ) 0) x
  simp only [Pi.zero_apply, sub_self] at this
  exact this


/-! ## Informational closure (restated from the Chapter 2 project) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 633: `ω, ω′` are indistinguishable at `t` (every forecast agrees).
Restated from `PriceLevelDetermination.LocalIFTStochastic`. -/
def Indist (t : ℕ) (ω ω' : Ω) : Prop := ∀ z : Ω → ℝ, 𝔼.E t z ω = 𝔼.E t z ω'

/-- Woodford (2003), p. 633: a function is constant on date-`t` information cells. -/
def CellConst {α : Type*} (t : ℕ) (f : Ω → α) : Prop := ∀ ω ω', Indist 𝔼 t ω ω' → f ω = f ω'

/-- Woodford (2003), p. 633: the expectation system is informationally closed when every
variable constant on date-`t` information cells is known at `t`. -/
def InfoClosed : Prop := ∀ t (y : Ω → ℝ), CellConst 𝔼 t y → 𝔼.E t y = y

/-- Woodford (2003), p. 633: a known variable is constant on information cells. -/
theorem cellConst_of_known {t : ℕ} {y : Ω → ℝ} (hy : 𝔼.E t y = y) : CellConst 𝔼 t y :=
  fun ω ω' h => by rw [← hy]; exact h y

/-- Woodford (2003), p. 633: every forecast `E_t z` is constant on information cells. -/
theorem cellConst_E (t : ℕ) (z : Ω → ℝ) : CellConst 𝔼 t (𝔼.E t z) := fun _ _ h => h z

/-- Woodford (2003), p. 633: every finite event tree is informationally closed (restated from the
Chapter 2 project). -/
theorem finiteTree_infoClosed {Ω' : Type*} [Fintype Ω']
    (T : ExpectationsFiniteTree.FiniteTree Ω') : InfoClosed T.toExpectationSystem := by
  intro t y hy
  funext ω
  rw [ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact T.condE_of_const_on_cell fun ω' h => hy ω' ω (fun z => T.condE_congr z h)

/-! ## Cell-constancy passes through the construction -/

/-- A function on dates × states is cell-constant at every date. -/
def CC {α : Type*} (h : ℕ × Ω → α) : Prop :=
  ∀ t ω ω', Indist 𝔼 t ω ω' → h (t, ω) = h (t, ω')

/-- Woodford (2003), p. 633: one-step-ahead forecasts are cell-constant. -/
theorem cc_seqOp (f : ℕ × Ω → ℝ) : CC 𝔼 (seqOp 𝔼 f) := fun t _ _ h =>
  h (fun ω'' => f (t + 1, ω''))

/-- Woodford (2003), p. 633: `Mv` of the forecast operator is cell-constant. -/
theorem cc_Mv {n : ℕ} (f : ℕ × Ω → Fin n → ℝ) : CC 𝔼 (Mv (seqOp 𝔼) f) := fun t ω ω' h => by
  funext i; exact h (fun ω'' => f (t + 1, ω'') i)

/-- Iterates of the forecast operator preserve cell-constancy. -/
theorem cc_iter {n : ℕ} {f : ℕ × Ω → Fin n → ℝ} (hf : CC 𝔼 f) (k : ℕ) :
    CC 𝔼 ((Mv (seqOp 𝔼))^[k] f) := by
  cases k with
  | zero => exact hf
  | succ k => rw [Function.iterate_succ']; exact cc_Mv 𝔼 _

/-- The forward series preserves cell-constancy (a pointwise property passes through `tsum`). -/
theorem cc_fwdSol {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) {f : ℕ × Ω → Fin n → ℝ}
    (hf : CC 𝔼 f) : CC 𝔼 (fwdSol B (seqOp 𝔼) f) := fun t ω ω' h => by
  unfold fwdSol
  exact tsum_congr fun k => by rw [cc_iter 𝔼 hf k t ω ω' h]

/-- Woodford (2003), App. A.3: the inverse of the linearised operator preserves cell-constancy. -/
theorem cc_linSol {r : ℕ × Ω → Fin 4 → ℝ} (hr : CC 𝔼 r) : CC 𝔼 (linSol p (seqOp 𝔼) r) := by
  have hs1 : CC 𝔼 (s1F p (seqOp 𝔼) r) := fun t ω ω' h => by
    simp only [s1F, hr t ω ω' h, cc_seqOp 𝔼 (fun x' => r x' 3) t ω ω' h]
  have hb : CC 𝔼 (bF p (seqOp 𝔼) r) := fun t ω ω' h => by
    simp only [bF, hr t ω ω' h, hs1 t ω ω' h]
  have hu : CC 𝔼 (uF p (seqOp 𝔼) r) := cc_fwdSol 𝔼 _ hb
  have hg : CC 𝔼 (fun x => ![gF p (seqOp 𝔼) r x]) := fun t ω ω' h => by
    simp only [gF, hr t ω ω' h, hu t ω ω' h,
      cc_seqOp 𝔼 (fun x' => uF p (seqOp 𝔼) r x' 1) t ω ω' h]
  have hF : CC 𝔼 (FF p (seqOp 𝔼) r) := fun t ω ω' h => by
    unfold FF
    rw [cc_fwdSol 𝔼 _ hg t ω ω' h]
  intro t ω ω' h
  simp only [linSol, hr t ω ω' h, hu t ω ω' h, hF t ω ω' h]

/-- Woodford (2003), (A.11): the residual of the stochastic conditions preserves
cell-constancy when the disturbances are cell-constant. -/
theorem cc_Phi (ξ : ℕ × Ω → Fin 5 → ℝ) (hξ : CC 𝔼 ξ) (ε : ℝ) {z : ℕ × Ω → Fin 4 → ℝ}
    (hz : CC 𝔼 z) : CC 𝔼 (Phi p (seqOp 𝔼) ξ ε z) := fun t ω ω' h => by
  simp only [Phi]
  rw [hξ t ω ω' h, hz t ω ω' h, cc_Mv 𝔼 _ t ω ω' h]

/-- Pointwise limits of cell-constant functions are cell-constant. -/
theorem cc_lim {n : ℕ} {zs : ℕ → ℕ × Ω → Fin n → ℝ} {z : ℕ × Ω → Fin n → ℝ}
    (hzs : ∀ k, CC 𝔼 (zs k)) (hz : ∀ x, Tendsto (fun k => zs k x) atTop (𝓝 (z x))) :
    CC 𝔼 z := fun t ω ω' h => by
  have h1 := hz (t, ω)
  have h2 := hz (t, ω')
  have e : (fun k => zs k (t, ω)) = fun k => zs k (t, ω') := funext fun k => hzs k t ω ω' h
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

/-! ## The sequence-space equilibrium is adapted -/

/-- Woodford (2003), App. A.3, p. 633 and Proposition 4.3 (**the sequence-space equilibrium is a
function of the information**). Under the Taylor principle there are `r, δ > 0` such that for
every expectation system and every disturbance process with `‖e_t(ω)‖ ≤ δ` that is constant on
the date-`t` information cells, the unique solution within `r` of the exact stochastic conditions
(`NonlinearNKMarkovGeneral.SeqEqm`) is constant on the date-`t` information cells. -/
theorem seq_existence_cellConst (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω) (e : ℕ → Ω → Fin 5 → ℝ),
      (∀ t ω, ‖e t ω‖ ≤ δ) → (∀ t, CellConst 𝔼 t (e t)) →
        ∃ z : ℕ → Ω → Fin 4 → ℝ, (((∀ t ω, ‖z t ω‖ ≤ r) ∧ SeqEqm p 𝔼 e z) ∧
          ∀ t, CellConst 𝔼 t (z t)) ∧ ∀ z' : ℕ → Ω → Fin 4 → ℝ, (∀ t ω, ‖z' t ω‖ ≤ r) →
            SeqEqm p 𝔼 e z' → z' = z := by
  obtain ⟨ρ, hρ, huniq⟩ := seq_uniqueness hp
  obtain ⟨r0, hr0, hex⟩ := general_existence_inv hp
  obtain ⟨δ1, hδ1, hex1⟩ := hex (min r0 ρ) (lt_min hr0 hρ) (min_le_left _ _)
  refine ⟨min r0 ρ, lt_min hr0 hρ, min δ1 ρ, lt_min hδ1 hρ, fun Ω 𝔼 e he hce => ?_⟩
  have hξ : CC 𝔼 (fun q : ℕ × Ω => e q.1 q.2) := fun t ω ω' h => hce t ω ω' h
  obtain ⟨z, ⟨hzB, hz⟩, hzA⟩ := hex1 (ℕ × Ω) (seqOp 𝔼) (seqOp_isMarkov 𝔼)
    (fun q => e q.1 q.2) 1 (fun q => by simpa using (he q.1 q.2).trans (min_le_left _ _))
    (CC 𝔼) (fun _ _ _ _ => rfl)
    (fun z hz => fun t ω ω' h => by
      have h1 := cc_linSol 𝔼 (p := p) (cc_Phi (p := p) 𝔼 _ hξ 1 hz) t ω ω' h
      simp only [hz t ω ω' h, h1])
    (fun zs z hzs hlim => cc_lim 𝔼 hzs hlim)
  have hzS : SeqEqm p 𝔼 e (fun t ω => z (t, ω)) := (seqEqm_iff 𝔼 e _).2 hz
  refine ⟨fun t ω => z (t, ω), ⟨⟨fun t ω => hzB (t, ω), hzS⟩, fun t ω ω' h => hzA t ω ω' h⟩,
    fun z' hz'B hz' => huniq Ω 𝔼 e z' _ (fun t ω => (he t ω).trans (min_le_right _ _))
      (fun t ω => (hz'B t ω).trans (min_le_right _ _))
      (fun t ω => (hzB (t, ω)).trans (min_le_right _ _)) hz' hzS⟩

/-- Woodford (2003), App. A.3, p. 633 (**ADAPTEDNESS of the sequence-space equilibrium under
informational closure**): if the expectation system is informationally closed and the
disturbances are known at each date (`E_t e_t = e_t`), the unique solution within `r` of the exact
stochastic conditions is adapted: `E_t z_t = z_t` for every component. -/
theorem seq_existence_adapted (hp : p.Std) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type*) (𝔼 : ExpectationSystem Ω), InfoClosed 𝔼 →
      ∀ e : ℕ → Ω → Fin 5 → ℝ, (∀ t ω, ‖e t ω‖ ≤ δ) →
        (∀ t (i : Fin 5), 𝔼.E t (fun ω => e t ω i) = fun ω => e t ω i) →
        ∃ z : ℕ → Ω → Fin 4 → ℝ, (((∀ t ω, ‖z t ω‖ ≤ r) ∧ SeqEqm p 𝔼 e z) ∧
          ∀ t (i : Fin 4), 𝔼.E t (fun ω => z t ω i) = fun ω => z t ω i) ∧
          ∀ z' : ℕ → Ω → Fin 4 → ℝ, (∀ t ω, ‖z' t ω‖ ≤ r) → SeqEqm p 𝔼 e z' → z' = z := by
  obtain ⟨r, hr, δ, hδ, h⟩ := seq_existence_cellConst hp
  refine ⟨r, hr, δ, hδ, fun Ω 𝔼 hcl e he hek => ?_⟩
  have hce : ∀ t, CellConst 𝔼 t (e t) := fun t ω ω' hi => by
    funext i; exact cellConst_of_known 𝔼 (hek t i) ω ω' hi
  obtain ⟨z, ⟨hzS, hzc⟩, hu⟩ := h Ω 𝔼 e he hce
  exact ⟨z, ⟨hzS, fun t i => hcl t _ fun ω ω' hi => by rw [hzc t ω ω' hi]⟩, hu⟩

end Woodford.StabilizationWelfare.NonlinearNKMarkovAdapted
