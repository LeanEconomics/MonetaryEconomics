/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LocalIFTStochastic

/-!
# Chapter 2 models under uncertainty: levels, transversality, random sunspots

Woodford (2003), *Interest and Prices*, Chapter 2, Props. 2.3, 2.6–2.8, 2.11–2.13, with
Appendix A.3, pp. 633–635. Module `LocalIFTStochastic` proves stochastic local (in)determinacy for
the exact period conditions in log coordinates. This module adds:

* **Levels.** For each model the stochastic equilibrium in levels in the book's form
  `1 + i_t = β⁻¹{E_t[u_c(t+1)P_t/(u_c(t)P_{t+1})]}⁻¹` (`StochTaylorEq`, `StochWicksellEq`,
  `StochSmoothEq`, `StochInertialEq`, `StochMGEq`, `StochNSWEq`, `StochNSIEq`), proved
  **equivalent** to the log-coordinate statement `SolvesS 𝔼 (liftII …) e x` (`taylor_solvesS_iff`,
  `wicksell_solvesS_iff`, `smooth_solvesS_iff`, `inertial_solvesS_iff`, `mg_solvesS_iff`,
  `nsw_solvesS_iff`, `nsi_solvesS_iff`), via exact pointwise identities (`*_exp_identity`) and
  `book_iff`. Assumptions: informational closure, the pull-out property, and known exogenous
  variables where the policy rule uses them.
* **Transversality (1.24) under uncertainty** from pathwise bounds (`stochTVC_of_bounds`) for every
  level equilibrium in the bands of the local theorems: `taylor_tvcS`, `wicksell_tvcS` (also 2.12),
  `smooth_tvcS`, `inflBand_tvcS` (2.8, 2.13), `mg_tvcS`.
* **Genuinely random sunspots** on the core coin-flip tree when the root lies inside the unit circle
  (`random_sunspotII`, `random_sunspot_expII`): `taylor_random_sunspot`, `smooth_random_sunspot`,
  `inertial_random_sunspot`, `nsw_random_sunspot`, `nsi_random_sunspot`.
-/

namespace Woodford.PriceLevelDetermination.LocalIFTStochasticModels

open Filter Topology
open Woodford.PriceLevelDetermination.LocalIFT (slopeA slopeB slopeC fderiv_zero_apply3)
open Woodford.PriceLevelDetermination.LocalIFTStochastic (Proc SProc slice mkB mkB_apply
  norm_apply_le norm_le_of_forall)
open Woodford.PriceLevelDetermination.LocalIFTStochastic.Ops (SolvesS liftII expT expT_zero
  contDiffAt_expT slopes_expT InfoClosed CellConst cellConst_of_known)
open Woodford.PriceLevelDetermination.ExpectationsFiniteTree (coinSystem coinTree coinObs)

/-! ## The book's form of (1.21) and the pull-out property -/

/-- Woodford (2003), (1.21), p. 71: with the pull-out property and a factor `k` known at `t`, the
book's form `k · E_t[X] = 1` is the expectational condition `E_t[k X − 1] = 0`. -/
theorem book_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {t : ℕ}
    {k : Ω → ℝ} (hk : 𝔼.E t k = k) (X : Ω → ℝ) :
    (∀ ω, k ω * 𝔼.E t X ω = 1) ↔ 𝔼.E t (fun ω => k ω * X ω - 1) = 0 := by
  have h : 𝔼.E t (fun ω => k ω * X ω - 1) = k * 𝔼.E t X - fun _ => 1 := by
    have e : (fun ω => k ω * X ω - 1) = k * X - fun _ => 1 := rfl
    rw [e, map_sub, hpo t k X hk, 𝔼.const]
  rw [h]
  constructor
  · intro h1
    funext ω
    simp [h1 ω]
  · intro h1 ω
    have := congrFun h1 ω
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply] at this
    linarith

/-! ## The stochastic transversality condition from pathwise bounds -/

/-- Woodford (2003), (1.24), p. 72, under uncertainty: if `0 ≤ u_c ≤ U`, `|D_T| ≤ A γ^T` and
`P_T ≥ c κ^T` in every state with `β γ < κ`, then `lim_T β^T E_t[u_c(T) D_T/P_T] = 0` at every date
and state. -/
theorem stochTVC_of_bounds {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β U A c κ γ : ℝ}
    (hβ : 0 < β) (hc : 0 < c) (hκ : 0 < κ) (hγ : 0 ≤ γ) (hlt : β * γ < κ)
    {uc D P : ℕ → Ω → ℝ} (huc0 : ∀ T ω, 0 ≤ uc T ω) (hU : ∀ T ω, uc T ω ≤ U)
    (hD : ∀ T ω, |D T ω| ≤ A * γ ^ T) (hP : ∀ T ω, c * κ ^ T ≤ P T ω) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => β ^ T * uc T ω' * D T ω' / P T ω') ω) atTop (𝓝 0) := by
  obtain ⟨ω₀⟩ : Nonempty Ω := ⟨ω⟩
  have hU0 : 0 ≤ U := (huc0 0 ω₀).trans (hU 0 ω₀)
  have hA0 : 0 ≤ A := by simpa using (abs_nonneg (D 0 ω₀)).trans (hD 0 ω₀)
  have hr0 : 0 ≤ β * γ / κ := by positivity
  have hr1 : β * γ / κ < 1 := by rwa [div_lt_one hκ]
  have hbd : ∀ T ω', |β ^ T * uc T ω' * D T ω' / P T ω'| ≤ U * A / c * (β * γ / κ) ^ T := by
    intro T ω'
    have hPT : 0 < P T ω' := lt_of_lt_of_le (by positivity) (hP T ω')
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (pow_pos hβ T), abs_of_nonneg (huc0 T ω'),
      abs_of_pos hPT, div_le_iff₀ hPT]
    calc β ^ T * uc T ω' * |D T ω'| ≤ β ^ T * U * (A * γ ^ T) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hU T ω') (pow_nonneg hβ.le T)) (hD T ω')
            (abs_nonneg _) (by positivity)
      _ = U * A / c * (β * γ / κ) ^ T * (c * κ ^ T) := by
          rw [div_pow, mul_pow]
          field_simp
      _ ≤ U * A / c * (β * γ / κ) ^ T * P T ω' :=
          mul_le_mul_of_nonneg_left (hP T ω') (by positivity)
  have hlim : Tendsto (fun T : ℕ => U * A / c * (β * γ / κ) ^ T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul (U * A / c)
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [Real.norm_eq_abs]
  exact 𝔼.abs_E_le (hbd T) t ω

/-- Woodford (2003), p. 79: a process growing at least at the factor `κ` from `P₀ ≥ c` satisfies
`P_T ≥ c κ^T`. -/
theorem growth_lower {Ω : Type*} {κ c : ℝ} (hκ : 0 ≤ κ) {P : ℕ → Ω → ℝ}
    (h0 : ∀ ω, c ≤ P 0 ω) (hg : ∀ t ω, κ * P t ω ≤ P (t + 1) ω) (T : ℕ) (ω : Ω) :
    c * κ ^ T ≤ P T ω := by
  induction T with
  | zero => simpa using h0 ω
  | succ n ih =>
    calc c * κ ^ (n + 1) = κ * (c * κ ^ n) := by ring
      _ ≤ κ * P n ω := mul_le_mul_of_nonneg_left ih hκ
      _ ≤ P (n + 1) ω := hg n ω

/-! ## Genuinely random sunspot equilibria on the coin-flip tree -/

/-- Coin-flip tree used for the sunspots of Woodford (2003), Ch. 2: states in the same
date-`(k+1)` information cell have the same first flip. -/
theorem coin_info_fst {k : ℕ} {ω ω' : Bool × Bool} (h : coinTree.info (k + 1) ω' ω) :
    ω'.1 = ω.1 := by
  change Setoid.ker (coinObs (k + 1)) ω' ω at h
  rw [Setoid.ker_def] at h
  simp only [coinObs, Prod.mk.injEq] at h
  simpa using h.1

/-- Woodford (2003), App. A.3: a variable depending only on the first coin flip is known from
date `1` on. -/
theorem coin_known_fst (k : ℕ) (f : Bool → ℝ) :
    coinSystem.E (k + 1) (fun ω => f ω.1) = fun ω => f ω.1 := by
  funext ω
  rw [coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact coinTree.condE_of_const_on_cell fun ω' h => by rw [coin_info_fst h]

/-- Woodford (2003), App. A.3: at date `0` the coin system takes the unconditional mean. -/
theorem coin_E0 (y : Bool × Bool → ℝ) (ω : Bool × Bool) :
    coinSystem.E 0 y ω = (y (true, true) + y (true, false) + y (false, true) +
      y (false, false)) / 4 := by
  have htriv : ∀ a b, coinTree.info 0 a b := fun a b => by
    change Setoid.ker (coinObs 0) a b
    rw [Setoid.ker_def]
    simp [coinObs]
  rw [coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E,
    coinTree.condE_of_trivial htriv]
  simp only [Fintype.sum_prod_type, Fintype.univ_bool, Finset.mem_singleton,
    Finset.sum_insert, Finset.sum_singleton, Bool.true_eq_false, not_false_eq_true]
  change 1 / 4 * y (true, true) + 1 / 4 * y (true, false) +
    (1 / 4 * y (false, true) + 1 / 4 * y (false, false)) = _
  ring

/-- Woodford (2003), App. A.3, p. 634 and the indeterminacy halves of Props. 2.6–2.8, 2.12–2.13,
**genuinely random sunspot equilibria**: if `F` is `C¹` near the steady state, `F(0) = 0` and
`|∂F/∂x_t| < |∂F/∂x_{t+1}|`, then on the two-period coin-flip tree (the core system `coinSystem`
with genuine uncertainty) for every `ε > 0` there is `r > 0` such that every initial value
`0 < |c| ≤ r` starts a bounded adapted solution of `E_t[F(x_t, x_{t+1}, 0)] = 0` (no fundamental
disturbances) within `ε` of the steady state whose date-1 value **depends on the first coin flip**
(a sunspot). -/
theorem random_sunspotII {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {F : ℝ × ℝ × E → ℝ} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hab : |slopeA F| < |slopeB F|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, c ≠ 0 → |c| ≤ r → ∃ x : Proc (Bool × Bool),
      SolvesS coinSystem (liftII F) 0 x ∧ ‖x‖ ≤ ε ∧ (∀ ω, x (0, ω) = c) ∧
        x (1, (true, true)) ≠ x (1, (false, true)) := by
  intro ε hε
  set a := slopeA F with ha
  set b := slopeB F with hb
  have hb0 : b ≠ 0 := by
    rintro h
    rw [h, abs_zero] at hab
    linarith [abs_nonneg a]
  have hbpos : 0 < |b| := abs_pos.mpr hb0
  set κ := (|b| - |a|) / 4 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set θ := (|b| - |a|) / (4 * |b|) with hθ
  have hθ0 : 0 < θ := by rw [hθ]; exact div_pos (by linarith) (by positivity)
  have hθ1 : θ ≤ 1 / 4 := by
    rw [hθ, div_le_iff₀ (by positivity)]
    linarith [abs_nonneg a]
  have hθb : |b| * θ = κ := by rw [hθ, hκ]; field_simp
  have hlo := (hF.differentiableAt (by norm_num)).hasFDerivAt.isLittleO.def hκ0
  have hct : ∀ᶠ p in 𝓝 (0 : ℝ × ℝ × E), ContinuousAt F p :=
    (hF.eventually (by simp)).mono fun p hp => hp.continuousAt
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp (hlo.and hct)
  obtain ⟨r₁, hr₁, hpath⟩ := LocalIFT.local_indeterminacy_loc hF h0 hab ε hε
  refine ⟨min (min r₁ ε) (ρ / 2), lt_min (lt_min hr₁ hε) (half_pos hρ),
    fun c hc0 hcr => ?_⟩
  have hcr₁ : |c| ≤ r₁ := hcr.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hcε : |c| ≤ ε := hcr.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hcρ : |c| < ρ := lt_of_le_of_lt (hcr.trans (min_le_right _ _)) (half_lt_self hρ)
  have hcpos : 0 < |c| := abs_pos.mpr hc0
  have hnorm : ∀ w : ℝ, |w| ≤ |c| → ‖((c, w, 0) : ℝ × ℝ × E)‖ = |c| := fun w hw => by
    rw [Prod.norm_mk, Prod.norm_mk, norm_zero, Real.norm_eq_abs, Real.norm_eq_abs,
      max_eq_left (abs_nonneg w), max_eq_left hw]
  have happrox : ∀ w : ℝ, |w| ≤ |c| → |F (c, w, 0) - (a * c + b * w)| ≤ κ * |c| :=
    fun w hw => by
      have h := (hρP (by rw [dist_zero_right, hnorm w hw]; exact hcρ)).1
      rw [sub_zero, h0, sub_zero, fderiv_zero_apply3, map_zero, add_zero, hnorm w hw,
        Real.norm_eq_abs] at h
      exact h
  have hcontF : ∀ w : ℝ, |w| ≤ |c| → ContinuousAt (fun w : ℝ => F (c, w, 0)) w := fun w hw => by
    have hpt : ContinuousAt F ((c, w, 0) : ℝ × ℝ × E) :=
      (hρP (by rw [dist_zero_right, hnorm w hw]; exact hcρ)).2
    have hf : ContinuousAt (fun w : ℝ => ((c, w, 0) : ℝ × ℝ × E)) w := by fun_prop
    exact ContinuousAt.comp (g := F) (f := fun w : ℝ => ((c, w, 0) : ℝ × ℝ × E)) hpt hf
  set L := (1 - θ) * |c| with hL
  set δ := θ * |c| with hδ
  have hLδ : L + δ = |c| := by rw [hL, hδ]; ring
  have hδ0 : 0 < δ := by positivity
  have hL0 : 0 ≤ L := by rw [hL]; nlinarith
  set h : ℝ → ℝ := fun z => F (c, z + δ, 0) + F (c, z - δ, 0) with hh
  have hin : ∀ z, |z| ≤ L → |z + δ| ≤ |c| ∧ |z - δ| ≤ |c| := fun z hz => by
    constructor
    · calc |z + δ| ≤ |z| + |δ| := abs_add_le _ _
        _ ≤ L + δ := by rw [abs_of_pos hδ0]; linarith
        _ = |c| := hLδ
    · calc |z - δ| ≤ |z| + |δ| := abs_sub _ _
        _ ≤ L + δ := by rw [abs_of_pos hδ0]; linarith
        _ = |c| := hLδ
  have hcont : ContinuousOn h (Set.Icc (-L) L) := by
    intro z hz
    have hz' : |z| ≤ L := abs_le.mpr hz
    obtain ⟨h1, h2⟩ := hin z hz'
    have c1 : ContinuousAt (fun z : ℝ => F (c, z + δ, 0)) z :=
      ContinuousAt.comp (g := fun w : ℝ => F (c, w, 0)) (hcontF _ h1) (by fun_prop)
    have c2 : ContinuousAt (fun z : ℝ => F (c, z - δ, 0)) z :=
      ContinuousAt.comp (g := fun w : ℝ => F (c, w, 0)) (hcontF _ h2) (by fun_prop)
    exact (c1.add c2).continuousWithinAt
  have hbnd : ∀ z, |z| ≤ L → |h z - (2 * a * c + 2 * b * z)| ≤ 2 * κ * |c| := fun z hz => by
    obtain ⟨h1, h2⟩ := hin z hz
    have e1 := happrox _ h1
    have e2 := happrox _ h2
    have : h z - (2 * a * c + 2 * b * z) =
        (F (c, z + δ, 0) - (a * c + b * (z + δ))) + (F (c, z - δ, 0) - (a * c + b * (z - δ))) := by
      simp only [hh]; ring
    rw [this]
    calc _ ≤ |F (c, z + δ, 0) - (a * c + b * (z + δ))| +
          |F (c, z - δ, 0) - (a * c + b * (z - δ))| := abs_add_le _ _
      _ ≤ κ * |c| + κ * |c| := add_le_add e1 e2
      _ = 2 * κ * |c| := by ring
  have hac : |a * c| ≤ |a| * |c| := (abs_mul a c).le
  have hLabs : |L| ≤ L := (abs_of_nonneg hL0).le
  have hmLabs : |-L| ≤ L := by rw [abs_neg]; exact hLabs
  have hkey : |b| * L = |b| * |c| - κ * |c| := by
    rw [hL, sub_mul, one_mul, mul_sub, ← mul_assoc, hθb]
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Set.Icc (-L) L, h z = 0 := by
    have hle : -L ≤ L := by linarith
    have hA := hbnd L hLabs
    have hB := hbnd (-L) hmLabs
    have hac1 := (abs_le.mp hac)
    have hκc : κ * |c| = (|b| * |c| - |a| * |c|) / 4 := by rw [hκ]; ring
    have hab' : |a| * |c| ≤ |b| * |c| := mul_le_mul_of_nonneg_right hab.le (abs_nonneg c)
    have hA1 := (abs_le.mp hA).1
    have hA2 := (abs_le.mp hA).2
    have hB1 := (abs_le.mp hB).1
    have hB2 := (abs_le.mp hB).2
    rcases lt_or_gt_of_ne hb0 with hbneg | hbpos'
    · have hbL : b * L = -(|b| * L) := by rw [abs_of_neg hbneg]; ring
      have h1 : h L ≤ 0 := by linarith
      have h2 : 0 ≤ h (-L) := by linarith
      exact intermediate_value_Icc' hle hcont ⟨h1, h2⟩
    · have hbL : b * L = |b| * L := by rw [abs_of_pos hbpos']
      have h1 : 0 ≤ h L := by linarith
      have h2 : h (-L) ≤ 0 := by linarith
      exact intermediate_value_Icc hle hcont ⟨h2, h1⟩
  have hz' : |z| ≤ L := abs_le.mpr hz
  obtain ⟨hzT, hzF⟩ := hin z hz'
  obtain ⟨yT, hyT, hyTn, hyT0⟩ := hpath (z + δ) (hzT.trans hcr₁)
  obtain ⟨yF, hyF, hyFn, hyF0⟩ := hpath (z - δ) (hzF.trans hcr₁)
  set path : Bool → LocalIFT.Linf := fun β => if β then yT else yF with hpathdef
  have hpn : ∀ β k, |path β k| ≤ ε := fun β k => by
    cases β
    · exact (LocalIFT.abs_apply_le yF k).trans hyFn
    · exact (LocalIFT.abs_apply_le yT k).trans hyTn
  set xf : ℕ × (Bool × Bool) → ℝ := fun q => if q.1 = 0 then c else path q.2.1 (q.1 - 1)
    with hxf
  have hxb : ∀ q, ‖xf q‖ ≤ ε := fun q => by
    rw [Real.norm_eq_abs, hxf]
    simp only
    split_ifs
    · exact hcε
    · exact hpn _ _
  refine ⟨mkB xf ⟨ε, hxb⟩, ⟨fun t => ?_, fun t => ?_⟩, norm_le_of_forall hε.le hxb,
    fun ω => by simp [hxf], ?_⟩
  · rcases t with _ | k
    · have : slice (mkB xf ⟨ε, hxb⟩) 0 = fun _ => c := by
        funext ω; simp [slice, hxf]
      rw [this, coinSystem.const]
    · have : slice (mkB xf ⟨ε, hxb⟩) (k + 1) = fun ω => path ω.1 k := by
        funext ω; simp [slice, hxf]
      rw [this]
      exact coin_known_fst k (fun β => path β k)
  · rcases t with _ | k
    · have hfun : (fun ω => liftII F ((mkB xf ⟨ε, hxb⟩) (0, ω), (mkB xf ⟨ε, hxb⟩) (0 + 1, ω),
          coinSystem.E 0 (slice (mkB xf ⟨ε, hxb⟩) (0 + 1)) ω,
          (0 : SProc (Bool × Bool) E) (0, ω))) = fun ω => F (c, path ω.1 0, 0) := by
        funext ω
        simp [liftII, LocalIFTStochastic.Ops.projII, hxf]
      rw [hfun]
      funext ω
      rw [coin_E0]
      have e1 : path true 0 = z + δ := by simp [hpathdef, hyT0]
      have e2 : path false 0 = z - δ := by simp [hpathdef, hyF0]
      simp only [e1, e2, Pi.zero_apply]
      have : F (c, z + δ, 0) + F (c, z - δ, 0) = 0 := hz0
      linarith
    · have hfun : (fun ω => liftII F ((mkB xf ⟨ε, hxb⟩) (k + 1, ω),
          (mkB xf ⟨ε, hxb⟩) (k + 1 + 1, ω),
          coinSystem.E (k + 1) (slice (mkB xf ⟨ε, hxb⟩) (k + 1 + 1)) ω,
          (0 : SProc (Bool × Bool) E) (k + 1, ω))) = 0 := by
        funext ω
        simp only [liftII, LocalIFTStochastic.Ops.projII, hxf, mkB_apply]
        simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
          ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_snd',
          add_eq_zero, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right, lp.coeFn_zero,
          Pi.zero_apply]
        cases ω.1
        · have := hyF k
          simpa [hpathdef] using this
        · have := hyT k
          simpa [hpathdef] using this
      rw [hfun, map_zero]
  · have e1 : (mkB xf ⟨ε, hxb⟩) (1, (true, true)) = z + δ := by simp [hxf, hpathdef, hyT0]
    have e2 : (mkB xf ⟨ε, hxb⟩) (1, (false, true)) = z - δ := by simp [hxf, hpathdef, hyF0]
    rw [e1, e2]
    intro h'
    linarith

/-- Woodford (2003), App. A.3, **random sunspots for the exponential (A.11) form**
`E_t[exp(F/κ)] = 1`: under `|∂F/∂x_t| < |∂F/∂x_{t+1}|` the conclusion of `random_sunspotII`. -/
theorem random_sunspot_expII {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {κ : ℝ} (hκ : κ ≠ 0) {F : ℝ × ℝ × E → ℝ}
    (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0) (hab : |slopeA F| < |slopeB F|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, c ≠ 0 → |c| ≤ r → ∃ x : Proc (Bool × Bool),
      SolvesS coinSystem (liftII (expT κ F)) 0 x ∧ ‖x‖ ≤ ε ∧ (∀ ω, x (0, ω) = c) ∧
        x (1, (true, true)) ≠ x (1, (false, true)) := by
  obtain ⟨ha, hb, -⟩ := slopes_expT κ (hF.differentiableAt (by norm_num)) h0
  refine random_sunspotII (contDiffAt_expT κ hF) (expT_zero κ h0) ?_
  rw [ha, hb, abs_mul, abs_mul]
  exact mul_lt_mul_of_pos_left hab (abs_pos.mpr (inv_ne_zero hκ))

/-! ## Transfer lemmas between levels and log coordinates -/

/-- Woodford (2003), p. 633: under informational closure a function of cell-constant data is
known. -/
theorem known_of_fn {Ω α : Type*} {𝔼 : ExpectationSystem Ω} (hcl : InfoClosed 𝔼) {t : ℕ}
    {Y : Ω → α} (hY : CellConst 𝔼 t Y) (f : α → ℝ) {x : Ω → ℝ} (hx : ∀ ω, x ω = f (Y ω)) :
    𝔼.E t x = x :=
  hcl t x (fun ω ω' h => by rw [hx, hx, hY ω ω' h])

/-- Woodford (2003), p. 633: pairs of cell-constant variables are cell-constant. -/
theorem cellConst_pair {Ω α γ : Type*} {𝔼 : ExpectationSystem Ω} {t : ℕ} {a : Ω → α}
    {b : Ω → γ} (ha : CellConst 𝔼 t a) (hb : CellConst 𝔼 t b) :
    CellConst 𝔼 t (fun ω => (a ω, b ω)) :=
  fun ω ω' h => by
    change (a ω, b ω) = (a ω', b ω')
    rw [ha ω ω' h, hb ω ω' h]

/-- Woodford (2003), (1.21): the stochastic Euler conditions in log coordinates are the book's
form once a pointwise identity `G(x_t, x_{t+1}, e_t) = k_t X_t − 1` with `k_t` known holds. -/
theorem euler_iff_of_identity {Ω E : Type*} [NormedAddCommGroup E] (𝔼 : ExpectationSystem Ω)
    (hpo : 𝔼.PullOut) {G : ℝ × ℝ × E → ℝ} {x : Proc Ω} {e : SProc Ω E} {k X : ℕ → Ω → ℝ}
    (hk : ∀ t, 𝔼.E t (k t) = k t)
    (hid : ∀ t ω, G (x (t, ω), x (t + 1, ω), e (t, ω)) = k t ω * X t ω - 1) :
    (∀ t, 𝔼.E t (fun ω => G (x (t, ω), x (t + 1, ω), e (t, ω))) = 0) ↔
      ∀ t ω, k t ω * 𝔼.E t (X t) ω = 1 := by
  refine forall_congr' fun t => ?_
  have hfun : (fun ω => G (x (t, ω), x (t + 1, ω), e (t, ω))) = fun ω => k t ω * X t ω - 1 :=
    funext (hid t)
  rw [hfun]
  exact (book_iff 𝔼 hpo (hk t) (X t)).symm

/-- Woodford (2003), (A.11): the solutions of the lifted (A.11) class, written with `x`, `e`. -/
theorem solvesS_liftII_eq {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (𝔼 : ExpectationSystem Ω) (G : ℝ × ℝ × E → ℝ) (e : SProc Ω E) (x : Proc Ω) :
    SolvesS 𝔼 (liftII G) e x ↔ (∀ t, 𝔼.E t (slice x t) = slice x t) ∧
      ∀ t, 𝔼.E t (fun ω => G (x (t, ω), x (t + 1, ω), e (t, ω))) = 0 := Iff.rfl

/-! ## Proposition 2.6: the Taylor rule in levels -/

/-- Woodford (2003), (1.21) and (2.4), pp. 72, 90, **under uncertainty, in levels and in the
book's form**: positive adapted gross inflation `Π`, `i_t = φ(Π_t/Π*_t; ν_t)` and
`(1 + i_t) β E_t[u_c(t+1)/(u_c(t) Π_{t+1})] = 1`. -/
def StochTaylorEq {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β : ℝ) (φ : ℝ × ℝ → ℝ)
    (uc PiStar ν Infl i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < Infl t ω) ∧ (∀ t, 𝔼.E t (Infl t) = Infl t) ∧
    (∀ t ω, i t ω = φ (Infl t ω / PiStar t ω, ν t ω)) ∧
    ∀ t ω, (1 + i t ω) * (β * 𝔼.E t (fun ω' => uc (t + 1) ω' / (uc t ω' * Infl (t + 1) ω')) ω) = 1

/-- Woodford (2003), **Prop. 2.6 under uncertainty: the level form (1.21) is exactly the
log-coordinate form** `SolvesS (liftII (expT 1 (gF logRule)))` used in
`taylor_local_determinacyS`, with `x_t = log(Π_t/Π*_t)` and
`e_t = (ν_t, log(u_c(t)/u_c(t+1)) + log Π*_{t+1})`, given informational closure, the pull-out
property, known `Π*_t`, `ν_t`, and `i_t = φ(Π_t/Π*_t; ν_t)`. -/
theorem taylor_solvesS_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hcl : InfoClosed 𝔼)
    (hpo : 𝔼.PullOut) {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν)) {uc PiStar ν Infl i : ℕ → Ω → ℝ}
    (huc : ∀ t ω, 0 < uc t ω) (hPS : ∀ t ω, 0 < PiStar t ω)
    (hPSk : ∀ t, 𝔼.E t (PiStar t) = PiStar t) (hνk : ∀ t, 𝔼.E t (ν t) = ν t)
    (hInfl : ∀ t ω, 0 < Infl t ω) (hrule : ∀ t ω, i t ω = φ (Infl t ω / PiStar t ω, ν t ω))
    {x : Proc Ω} {e : SProc Ω (ℝ × ℝ)} (hx : ∀ t ω, x (t, ω) = Real.log (Infl t ω / PiStar t ω))
    (he : ∀ t ω, e (t, ω) =
      (ν t ω, Real.log (uc t ω / uc (t + 1) ω) + Real.log (PiStar (t + 1) ω))) :
    SolvesS 𝔼 (liftII (expT 1 (LocalIFT.gF (LocalIFT.logRule β φ)))) e x ↔
      StochTaylorEq 𝔼 β φ uc PiStar ν Infl i := by
  have hadapt : ∀ t, 𝔼.E t (slice x t) = slice x t ↔ 𝔼.E t (Infl t) = Infl t := by
    intro t
    have hPc := cellConst_of_known 𝔼 (hPSk t)
    constructor
    · intro h
      refine known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 h) hPc)
        (fun q => q.2 * Real.exp q.1) (fun ω => ?_)
      change Infl t ω = PiStar t ω * Real.exp (x (t, ω))
      rw [hx, Real.exp_log (div_pos (hInfl t ω) (hPS t ω))]
      field_simp [(hPS t ω).ne']
    · intro h
      exact known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 h) hPc)
        (fun q => Real.log (q.1 / q.2)) (fun ω => hx t ω)
  have hik : (∀ t, 𝔼.E t (Infl t) = Infl t) →
      ∀ t, 𝔼.E t (fun ω => β * (1 + i t ω)) = fun ω => β * (1 + i t ω) := by
    intro h t
    refine known_of_fn hcl (cellConst_pair (cellConst_pair (cellConst_of_known 𝔼 (h t))
      (cellConst_of_known 𝔼 (hPSk t))) (cellConst_of_known 𝔼 (hνk t)))
      (fun q => β * (1 + φ (q.1.1 / q.1.2, q.2))) (fun ω => ?_)
    simp only [hrule t ω]
  have hid : ∀ t ω, expT 1 (LocalIFT.gF (LocalIFT.logRule β φ)) (x (t, ω), x (t + 1, ω), e (t, ω)) =
      β * (1 + i t ω) * (uc (t + 1) ω / (uc t ω * Infl (t + 1) ω)) - 1 := by
    intro t ω
    rw [hx, hx, he, LocalIFTStochastic.Models.taylor_exp_identity hβ
      (div_pos (hInfl t ω) (hPS t ω)) (hpos _ (div_pos (hInfl t ω) (hPS t ω)) _)
      (hInfl (t + 1) ω) (hPS (t + 1) ω) (huc t ω) (huc (t + 1) ω), ← hrule]
    field_simp
  rw [solvesS_liftII_eq]
  constructor
  · rintro ⟨had, hE⟩
    have hInk : ∀ t, 𝔼.E t (Infl t) = Infl t := fun t => (hadapt t).mp (had t)
    refine ⟨hInfl, hInk, hrule, fun t ω => ?_⟩
    have h := ((euler_iff_of_identity 𝔼 hpo (hik hInk) hid).mp hE) t ω
    linarith
  · rintro ⟨-, hInk, -, hE⟩
    refine ⟨fun t => (hadapt t).mpr (hInk t), (euler_iff_of_identity 𝔼 hpo (hik hInk) hid).mpr
      fun t ω => ?_⟩
    have := hE t ω
    linarith

/-- Woodford (2003), (1.24) for **Prop. 2.6 under uncertainty**: if `u_c ≤ U`, total liabilities
grow at most at factor `γ` in every state, `Π*_t ≥ θ`, and `β γ < θ e^{-ε}`, every Taylor-rule
price process `P_{t} = Π_t P_{t−1}` (`P_{−1} > 0`) with `|log(Π_t/Π*_t)| ≤ ε` satisfies the
stochastic transversality condition `β^T E_t[u_c D_T/P_T] → 0` at every date and state. -/
theorem taylor_tvcS {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β ε U θ γ Pm1 : ℝ} (hβ : 0 < β)
    (hθ : 0 < θ) (hγ : 0 ≤ γ) (hm : 0 < Pm1) (hlt : β * γ < θ * Real.exp (-ε))
    {uc PiStar Infl P D : ℕ → Ω → ℝ} (huc : ∀ t ω, 0 < uc t ω) (hU : ∀ t ω, uc t ω ≤ U)
    (hS : ∀ t ω, θ ≤ PiStar t ω) (hInfl : ∀ t ω, 0 < Infl t ω)
    (hbd : ∀ t ω, |Real.log (Infl t ω / PiStar t ω)| ≤ ε)
    (hP0 : ∀ ω, P 0 ω = Infl 0 ω * Pm1) (hP : ∀ t ω, P (t + 1) ω = Infl (t + 1) ω * P t ω)
    (hD : ∀ t ω, |D (t + 1) ω| ≤ γ * |D t ω|) {A : ℝ} (hA : ∀ ω, |D 0 ω| ≤ A) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => β ^ T * uc T ω' * D T ω' / P T ω') ω) atTop (𝓝 0) := by
  set κ := θ * Real.exp (-ε) with hκ
  have hκ0 : 0 < κ := mul_pos hθ (Real.exp_pos _)
  have hlow : ∀ t ω, κ ≤ Infl t ω := fun t ω => by
    have hPS : 0 < PiStar t ω := lt_of_lt_of_le hθ (hS t ω)
    have hr : Real.exp (-ε) ≤ Infl t ω / PiStar t ω := by
      rw [← Real.exp_log (div_pos (hInfl t ω) hPS)]
      exact Real.exp_le_exp.mpr (neg_le_of_abs_le (hbd t ω))
    calc κ ≤ PiStar t ω * (Infl t ω / PiStar t ω) :=
          mul_le_mul (hS t ω) hr (Real.exp_pos _).le hPS.le
      _ = Infl t ω := by field_simp
  have hPpos : ∀ t ω, 0 < P t ω := by
    intro t
    induction t with
    | zero => intro ω; rw [hP0]; exact mul_pos (hInfl 0 ω) hm
    | succ n ih => intro ω; rw [hP]; exact mul_pos (hInfl _ ω) (ih ω)
  have hDb : ∀ T ω, |D T ω| ≤ A * γ ^ T := by
    intro T ω
    induction T with
    | zero => simpa using hA ω
    | succ n ih =>
      calc |D (n + 1) ω| ≤ γ * |D n ω| := hD n ω
        _ ≤ γ * (A * γ ^ n) := mul_le_mul_of_nonneg_left ih hγ
        _ = A * γ ^ (n + 1) := by ring
  refine stochTVC_of_bounds 𝔼 hβ (mul_pos hm hκ0) hκ0 hγ hlt (fun T ω => (huc T ω).le) hU hDb
    (growth_lower hκ0.le (fun ω => ?_) (fun t ω => ?_)) t ω
  · rw [hP0, mul_comm Pm1 κ]
    exact mul_le_mul_of_nonneg_right (hlow 0 ω) hm.le
  · rw [hP]
    exact mul_le_mul_of_nonneg_right (hlow (t + 1) ω) (hPpos t ω).le

/-- Woodford (2003), **Prop. 2.6, indeterminacy half, genuinely random sunspots**: if
`|φ_π| < 1`, the exact stochastic Euler equation of the Taylor-rule model has, on the coin-flip
tree and with no fundamental disturbances, bounded adapted sunspot equilibria arbitrarily close to
the steady state whose inflation depends on the coin. -/
theorem taylor_random_sunspot {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hφπ : |LocalIFT.elast β φ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, c ≠ 0 → |c| ≤ r → ∃ x : Proc (Bool × Bool),
      SolvesS coinSystem (liftII (expT 1 (LocalIFT.gF (LocalIFT.logRule β φ)))) 0 x ∧
        ‖x‖ ≤ ε ∧ (∀ ω, x (0, ω) = c) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  have hg : ContDiffAt ℝ 1 (LocalIFT.logRule β φ) 0 := Nonlinear.contDiffAt_logRule hβ hss hφ
  have hgd : DifferentiableAt ℝ (LocalIFT.logRule β φ) 0 := hg.differentiableAt (by norm_num)
  obtain ⟨hx, -⟩ := LocalIFT.slopes_logRule hβ hss (hφ.differentiableAt (by norm_num))
  obtain ⟨ha, hb, -⟩ := LocalIFT.slopes_gF hgd
  refine random_sunspot_expII one_ne_zero (LocalIFT.contDiffAt_gF hg)
    (LocalIFT.gF_zero (LocalIFT.logRule_zero hss)) ?_
  rw [ha, hb, hx]
  simpa using hφπ

/-! ## Proposition 2.3: the Wicksellian rule in levels -/

/-- Woodford (2003), (1.21) and (1.30), **Wicksellian Euler equation under uncertainty**: with
`p = log(P_t/P*_t)`, `p' = log(P_{t+1}/P*_{t+1})`, `w = log(u_c(t)/u_c(t+1)) + log(P*_{t+1}/P*_t)`,
the exponential form of the period condition is `β(1 + i_t) u_c(t+1) P_t/(u_c(t) P_{t+1}) − 1`. -/
theorem wicksell_exp_identity {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) {P0 P1 S0 S1 ν u0 u1 : ℝ}
    (hP0 : 0 < P0) (hP1 : 0 < P1) (hS0 : 0 < S0) (hS1 : 0 < S1)
    (hφ : 0 < 1 + φ (P0 / S0, ν)) (hu0 : 0 < u0) (hu1 : 0 < u1) :
    expT 1 (LocalIFT.gF (LocalIFT.gW β φ))
        (Real.log (P0 / S0), Real.log (P1 / S1), (ν, Real.log (u0 / u1) + Real.log (S1 / S0))) =
      β * (1 + φ (P0 / S0, ν)) * (u1 * P0 / (u0 * P1)) - 1 := by
  have h : LocalIFT.gF (LocalIFT.gW β φ)
      (Real.log (P0 / S0), Real.log (P1 / S1), (ν, Real.log (u0 / u1) + Real.log (S1 / S0))) =
      Real.log (β * (1 + φ (P0 / S0, ν)) * (u1 * P0 / (u0 * P1))) := by
    simp only [LocalIFT.gF, LocalIFT.projXN_apply, LocalIFT.leadL_apply, LocalIFT.gW,
      LocalIFT.logRule, Real.exp_log (div_pos hP0 hS0)]
    have e : Real.log (β * (1 + φ (P0 / S0, ν)) * (u1 * P0 / (u0 * P1))) =
        Real.log β + Real.log (1 + φ (P0 / S0, ν)) + (Real.log u1 + Real.log P0) -
          (Real.log u0 + Real.log P1) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hβ.ne' hφ.ne',
        Real.log_div (by positivity) (by positivity), Real.log_mul hu1.ne' hP0.ne',
        Real.log_mul hu0.ne' hP1.ne']
      ring
    rw [e, Real.log_div hP0.ne' hS0.ne', Real.log_div hP1.ne' hS1.ne',
      Real.log_div hu0.ne' hu1.ne', Real.log_div hS1.ne' hS0.ne']
    ring
  rw [expT, inv_one, one_mul, h, Real.exp_log (by positivity)]

/-- Woodford (2003), (1.21) and (1.30), pp. 72, 77, **Wicksellian equilibrium under uncertainty
in levels, book form**: positive adapted `P`, `i_t = φ(P_t/P*_t; ν_t)` and
`(1 + i_t) β E_t[u_c(t+1) P_t/(u_c(t) P_{t+1})] = 1`. -/
def StochWicksellEq {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β : ℝ) (φ : ℝ × ℝ → ℝ)
    (uc Pstar ν P i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ (∀ t, 𝔼.E t (P t) = P t) ∧
    (∀ t ω, i t ω = φ (P t ω / Pstar t ω, ν t ω)) ∧
    ∀ t ω, (1 + i t ω) *
      (β * 𝔼.E t (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) ω) = 1

/-- Woodford (2003), **Prop. 2.3 under uncertainty: the level form is exactly the
log-coordinate form** used in `wicksell_local_determinacyS`, with `x_t = log(P_t/P*_t)` and
`e_t = (ν_t, log(u_c(t)/u_c(t+1)) + log(P*_{t+1}/P*_t))` (closure, pull-out, known `P*_t`,
`ν_t`). -/
theorem wicksell_solvesS_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hcl : InfoClosed 𝔼)
    (hpo : 𝔼.PullOut) {β : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν)) {uc Pstar ν P i : ℕ → Ω → ℝ}
    (huc : ∀ t ω, 0 < uc t ω) (hPS : ∀ t ω, 0 < Pstar t ω)
    (hPSk : ∀ t, 𝔼.E t (Pstar t) = Pstar t) (hνk : ∀ t, 𝔼.E t (ν t) = ν t)
    (hP : ∀ t ω, 0 < P t ω) (hrule : ∀ t ω, i t ω = φ (P t ω / Pstar t ω, ν t ω))
    {x : Proc Ω} {e : SProc Ω (ℝ × ℝ)} (hx : ∀ t ω, x (t, ω) = Real.log (P t ω / Pstar t ω))
    (he : ∀ t ω, e (t, ω) =
      (ν t ω, Real.log (uc t ω / uc (t + 1) ω) + Real.log (Pstar (t + 1) ω / Pstar t ω))) :
    SolvesS 𝔼 (liftII (expT 1 (LocalIFT.gF (LocalIFT.gW β φ)))) e x ↔
      StochWicksellEq 𝔼 β φ uc Pstar ν P i := by
  have hadapt : ∀ t, 𝔼.E t (slice x t) = slice x t ↔ 𝔼.E t (P t) = P t := by
    intro t
    have hPc := cellConst_of_known 𝔼 (hPSk t)
    constructor
    · intro h
      refine known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 h) hPc)
        (fun q => q.2 * Real.exp q.1) (fun ω => ?_)
      change P t ω = Pstar t ω * Real.exp (x (t, ω))
      rw [hx, Real.exp_log (div_pos (hP t ω) (hPS t ω))]
      field_simp [(hPS t ω).ne']
    · intro h
      exact known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 h) hPc)
        (fun q => Real.log (q.1 / q.2)) (fun ω => hx t ω)
  have hik : (∀ t, 𝔼.E t (P t) = P t) →
      ∀ t, 𝔼.E t (fun ω => β * (1 + i t ω)) = fun ω => β * (1 + i t ω) := by
    intro h t
    refine known_of_fn hcl (cellConst_pair (cellConst_pair (cellConst_of_known 𝔼 (h t))
      (cellConst_of_known 𝔼 (hPSk t))) (cellConst_of_known 𝔼 (hνk t)))
      (fun q => β * (1 + φ (q.1.1 / q.1.2, q.2))) (fun ω => ?_)
    simp only [hrule t ω]
  have hid : ∀ t ω, expT 1 (LocalIFT.gF (LocalIFT.gW β φ)) (x (t, ω), x (t + 1, ω), e (t, ω)) =
      β * (1 + i t ω) * (uc (t + 1) ω * P t ω / (uc t ω * P (t + 1) ω)) - 1 := by
    intro t ω
    rw [hx, hx, he, wicksell_exp_identity hβ (hP t ω) (hP (t + 1) ω) (hPS t ω) (hPS (t + 1) ω)
      (hpos _ (div_pos (hP t ω) (hPS t ω)) _) (huc t ω) (huc (t + 1) ω), ← hrule]
  rw [solvesS_liftII_eq]
  constructor
  · rintro ⟨had, hE⟩
    have hPk : ∀ t, 𝔼.E t (P t) = P t := fun t => (hadapt t).mp (had t)
    refine ⟨hP, hPk, hrule, fun t ω => ?_⟩
    have h := ((euler_iff_of_identity 𝔼 hpo (hik hPk) hid).mp hE) t ω
    linarith
  · rintro ⟨-, hPk, -, hE⟩
    refine ⟨fun t => (hadapt t).mpr (hPk t), (euler_iff_of_identity 𝔼 hpo (hik hPk) hid).mpr
      fun t ω => ?_⟩
    have := hE t ω
    linarith

/-- Woodford (2003), (1.24) and p. 79 for **Props. 2.3 and 2.12 under uncertainty** (for 2.12 take
`u_c(t) = u_c(Y_t, m_t; ξ_t)`): if `u_c ≤ U`, total
liabilities grow at most at factor `γ`, the target grows at least at factor `θ` from
`P*_0 ≥ s₀ > 0` in every state, and `β γ < θ`, every price process with `|log(P_t/P*_t)| ≤ ε`
satisfies the stochastic transversality condition at every date and state. -/
theorem wicksell_tvcS {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β ε U θ γ s0 A : ℝ} (hβ : 0 < β)
    (hθ : 0 < θ) (hγ : 0 ≤ γ) (hs0 : 0 < s0) (hlt : β * γ < θ)
    {uc Pstar P D : ℕ → Ω → ℝ} (huc : ∀ t ω, 0 < uc t ω) (hU : ∀ t ω, uc t ω ≤ U)
    (hPS0 : ∀ ω, s0 ≤ Pstar 0 ω) (hS : ∀ t ω, θ * Pstar t ω ≤ Pstar (t + 1) ω)
    (hP : ∀ t ω, 0 < P t ω) (hbd : ∀ t ω, |Real.log (P t ω / Pstar t ω)| ≤ ε)
    (hD : ∀ t ω, |D (t + 1) ω| ≤ γ * |D t ω|) (hA : ∀ ω, |D 0 ω| ≤ A) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => β ^ T * uc T ω' * D T ω' / P T ω') ω) atTop (𝓝 0) := by
  have hDb : ∀ T ω, |D T ω| ≤ A * γ ^ T := by
    intro T ω
    induction T with
    | zero => simpa using hA ω
    | succ n ih =>
      calc |D (n + 1) ω| ≤ γ * |D n ω| := hD n ω
        _ ≤ γ * (A * γ ^ n) := mul_le_mul_of_nonneg_left ih hγ
        _ = A * γ ^ (n + 1) := by ring
  have hPSg := growth_lower hθ.le hPS0 hS
  have hPSpos : ∀ T ω, 0 < Pstar T ω := fun T ω =>
    lt_of_lt_of_le (by positivity) (hPSg T ω)
  refine stochTVC_of_bounds 𝔼 hβ (mul_pos hs0 (Real.exp_pos (-ε))) hθ hγ hlt
    (fun T ω => (huc T ω).le) hU hDb (fun T ω => ?_) t ω
  have hr : Real.exp (-ε) ≤ P T ω / Pstar T ω := by
    rw [← Real.exp_log (div_pos (hP T ω) (hPSpos T ω))]
    exact Real.exp_le_exp.mpr (neg_le_of_abs_le (hbd T ω))
  calc s0 * Real.exp (-ε) * θ ^ T = s0 * θ ^ T * Real.exp (-ε) := by ring
    _ ≤ Pstar T ω * (P T ω / Pstar T ω) :=
      mul_le_mul (hPSg T ω) hr (Real.exp_pos _).le (hPSpos T ω).le
    _ = P T ω := by field_simp [(hPSpos T ω).ne']

/-! ## Inflation-based price levels: a generic transversality lemma -/

/-- Woodford (2003), (1.24) under uncertainty: if `Π_t ≥ κ` in every state, `P_0 = Π_0 P_{−1}`,
`P_{t+1} = Π_{t+1} P_t`, `0 < u_c ≤ U`, liabilities grow at most at factor `γ` and `β γ < κ`,
the stochastic transversality condition holds at every date and state. -/
theorem infl_tvcS {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β κ U γ Pm1 A : ℝ} (hβ : 0 < β)
    (hκ : 0 < κ) (hγ : 0 ≤ γ) (hm : 0 < Pm1) (hlt : β * γ < κ)
    {uc Infl P D : ℕ → Ω → ℝ} (huc : ∀ t ω, 0 < uc t ω) (hU : ∀ t ω, uc t ω ≤ U)
    (hlow : ∀ t ω, κ ≤ Infl t ω) (hP0 : ∀ ω, P 0 ω = Infl 0 ω * Pm1)
    (hP : ∀ t ω, P (t + 1) ω = Infl (t + 1) ω * P t ω)
    (hD : ∀ t ω, |D (t + 1) ω| ≤ γ * |D t ω|) (hA : ∀ ω, |D 0 ω| ≤ A) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => β ^ T * uc T ω' * D T ω' / P T ω') ω) atTop (𝓝 0) := by
  have hInfl : ∀ t ω, 0 < Infl t ω := fun t ω => lt_of_lt_of_le hκ (hlow t ω)
  have hPpos : ∀ t ω, 0 < P t ω := by
    intro t
    induction t with
    | zero => intro ω; rw [hP0]; exact mul_pos (hInfl 0 ω) hm
    | succ n ih => intro ω; rw [hP]; exact mul_pos (hInfl _ ω) (ih ω)
  have hDb : ∀ T ω, |D T ω| ≤ A * γ ^ T := by
    intro T ω
    induction T with
    | zero => simpa using hA ω
    | succ n ih =>
      calc |D (n + 1) ω| ≤ γ * |D n ω| := hD n ω
        _ ≤ γ * (A * γ ^ n) := mul_le_mul_of_nonneg_left ih hγ
        _ = A * γ ^ (n + 1) := by ring
  refine stochTVC_of_bounds 𝔼 hβ (mul_pos hm hκ) hκ hγ hlt (fun T ω => (huc T ω).le) hU hDb
    (growth_lower hκ.le (fun ω => ?_) (fun t ω => ?_)) t ω
  · rw [hP0, mul_comm Pm1 κ]
    exact mul_le_mul_of_nonneg_right (hlow 0 ω) hm.le
  · rw [hP]
    exact mul_le_mul_of_nonneg_right (hlow (t + 1) ω) (hPpos t ω).le

/-- Woodford (2003), p. 633: a variable known at `s` is known at every later date. -/
theorem known_later {Ω : Type*} (𝔼 : ExpectationSystem Ω) {s t : ℕ} (hst : s ≤ t)
    {y : Ω → ℝ} (hy : 𝔼.E s y = y) : 𝔼.E t y = y := by
  rw [← hy, 𝔼.known hst]

/-! ## Proposition 2.7: a rule on smoothed inflation, in levels -/

/-- Woodford (2003), (1.21) and (2.9), **Euler equation under uncertainty for the smoothed-inflation
rule**: with `π̄' = δ π̄ + (1 − δ) log Π'` and `r̂ = log(u_c(t)/u_c(t+1))`, the exponential form
`exp(F7/(1 − δ)) − 1` is `β(1 + φ(e^{π̄}; ν)) u_c(t+1)/(u_c(t) Π') − 1`. -/
theorem smooth_exp_identity {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    {x ν Q u0 u1 : ℝ} (hφ : 0 < 1 + φ (Real.exp x, ν)) (hQ : 0 < Q) (hu0 : 0 < u0)
    (hu1 : 0 < u1) :
    expT (1 - dl) (Nonlinear.F7 β dl φ)
        (x, dl * x + (1 - dl) * Real.log Q, (ν, Real.log (u0 / u1))) =
      β * (1 + φ (Real.exp x, ν)) * (u1 / (u0 * Q)) - 1 := by
  have hk : (1 - dl) ≠ 0 := by linarith
  have h : (1 - dl)⁻¹ * Nonlinear.F7 β dl φ
      (x, dl * x + (1 - dl) * Real.log Q, (ν, Real.log (u0 / u1))) =
      Real.log (β * (1 + φ (Real.exp x, ν)) * (u1 / (u0 * Q))) := by
    simp only [Nonlinear.F7, LocalIFT.logRule]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hβ.ne' hφ.ne',
      Real.log_div hu1.ne' (by positivity), Real.log_mul hu0.ne' hQ.ne',
      Real.log_div hu0.ne' hu1.ne']
    field_simp
    ring
  rw [expT, h, Real.exp_log (by positivity)]

/-- Woodford (2003), (1.21) and (2.9), pp. 72, 95, **smoothed-inflation-rule equilibrium under
uncertainty, levels, book form**: positive adapted `Π`, `i_t = φ(exp π̄_t; ν_t)` with `π̄` the
smoothed log inflation (2.8) of each path, and `(1 + i_t) β E_t[u_c(t+1)/(u_c(t) Π_{t+1})] = 1`. -/
def StochSmoothEq {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β dl : ℝ) (φ : ℝ × ℝ → ℝ)
    (uc ν : ℕ → Ω → ℝ) (pbm1 : ℝ) (Infl i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < Infl t ω) ∧ (∀ t, 𝔼.E t (Infl t) = Infl t) ∧
    (∀ t ω, i t ω = φ (Real.exp (Nonlinear.smoothLog dl pbm1 (fun s => Infl s ω) t), ν t ω)) ∧
    ∀ t ω, (1 + i t ω) *
      (β * 𝔼.E t (fun ω' => uc (t + 1) ω' / (uc t ω' * Infl (t + 1) ω')) ω) = 1

/-- Woodford (2003), **Prop. 2.7 under uncertainty: the level form is exactly the
log-coordinate form** used in `smooth_local_determinacyS`, with `x_t = π̄_t` and
`e_t = (ν_t, log(u_c(t)/u_c(t+1)))` (closure, pull-out, known `ν_t`). -/
theorem smooth_solvesS_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hcl : InfoClosed 𝔼)
    (hpo : 𝔼.PullOut) {β dl pbm1 : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν)) {uc ν Infl i : ℕ → Ω → ℝ}
    (huc : ∀ t ω, 0 < uc t ω) (hνk : ∀ t, 𝔼.E t (ν t) = ν t) (hInfl : ∀ t ω, 0 < Infl t ω)
    (hrule : ∀ t ω,
      i t ω = φ (Real.exp (Nonlinear.smoothLog dl pbm1 (fun s => Infl s ω) t), ν t ω))
    {x : Proc Ω} {e : SProc Ω (ℝ × ℝ)}
    (hx : ∀ t ω, x (t, ω) = Nonlinear.smoothLog dl pbm1 (fun s => Infl s ω) t)
    (he : ∀ t ω, e (t, ω) = (ν t ω, Real.log (uc t ω / uc (t + 1) ω))) :
    SolvesS 𝔼 (liftII (expT (1 - dl) (Nonlinear.F7 β dl φ))) e x ↔
      StochSmoothEq 𝔼 β dl φ uc ν pbm1 Infl i := by
  have hk : (1 - dl) ≠ 0 := by linarith
  have hrec : ∀ t ω, x (t + 1, ω) = dl * x (t, ω) + (1 - dl) * Real.log (Infl (t + 1) ω) :=
    fun t ω => by rw [hx, hx]; rfl
  have hx0 : ∀ ω, x (0, ω) = dl * pbm1 + (1 - dl) * Real.log (Infl 0 ω) :=
    fun ω => by rw [hx]; rfl
  have hadapt : (∀ t, 𝔼.E t (slice x t) = slice x t) ↔ ∀ t, 𝔼.E t (Infl t) = Infl t := by
    constructor
    · intro h t
      rcases t with _ | t
      · refine known_of_fn hcl (cellConst_of_known 𝔼 (h 0))
          (fun a => Real.exp ((a - dl * pbm1) / (1 - dl))) (fun ω => ?_)
        change Infl 0 ω = Real.exp ((x (0, ω) - dl * pbm1) / (1 - dl))
        rw [hx0, show dl * pbm1 + (1 - dl) * Real.log (Infl 0 ω) - dl * pbm1 =
          (1 - dl) * Real.log (Infl 0 ω) by ring, mul_div_cancel_left₀ _ hk,
          Real.exp_log (hInfl 0 ω)]
      · refine known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 (h (t + 1)))
          (cellConst_of_known 𝔼 (known_later 𝔼 (Nat.le_succ t) (h t))))
          (fun q => Real.exp ((q.1 - dl * q.2) / (1 - dl))) (fun ω => ?_)
        change Infl (t + 1) ω = Real.exp ((x (t + 1, ω) - dl * x (t, ω)) / (1 - dl))
        rw [hrec, show dl * x (t, ω) + (1 - dl) * Real.log (Infl (t + 1) ω) - dl * x (t, ω) =
          (1 - dl) * Real.log (Infl (t + 1) ω) by ring, mul_div_cancel_left₀ _ hk,
          Real.exp_log (hInfl _ ω)]
    · intro h t
      induction t with
      | zero =>
        exact known_of_fn hcl (cellConst_of_known 𝔼 (h 0))
          (fun a => dl * pbm1 + (1 - dl) * Real.log a) (fun ω => hx0 ω)
      | succ n ih =>
        exact known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 (h (n + 1)))
          (cellConst_of_known 𝔼 (known_later 𝔼 (Nat.le_succ n) ih)))
          (fun q => dl * q.2 + (1 - dl) * Real.log q.1) (fun ω => hrec n ω)
  have hik : (∀ t, 𝔼.E t (slice x t) = slice x t) →
      ∀ t, 𝔼.E t (fun ω => β * (1 + i t ω)) = fun ω => β * (1 + i t ω) := by
    intro h t
    refine known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 (h t))
      (cellConst_of_known 𝔼 (hνk t))) (fun q => β * (1 + φ (Real.exp q.1, q.2))) (fun ω => ?_)
    change β * (1 + i t ω) = β * (1 + φ (Real.exp (x (t, ω)), ν t ω))
    rw [hrule, hx]
  have hid : ∀ t ω, expT (1 - dl) (Nonlinear.F7 β dl φ) (x (t, ω), x (t + 1, ω), e (t, ω)) =
      β * (1 + i t ω) * (uc (t + 1) ω / (uc t ω * Infl (t + 1) ω)) - 1 := by
    intro t ω
    rw [hrec, he, smooth_exp_identity hβ hdl (hpos _ (Real.exp_pos _) _) (hInfl (t + 1) ω)
      (huc t ω) (huc (t + 1) ω), hrule, hx]
  rw [solvesS_liftII_eq]
  constructor
  · rintro ⟨had, hE⟩
    refine ⟨hInfl, hadapt.mp had, hrule, fun t ω => ?_⟩
    have h := ((euler_iff_of_identity 𝔼 hpo (hik had) hid).mp hE) t ω
    linarith
  · rintro ⟨-, hInk, -, hE⟩
    have had := hadapt.mpr hInk
    refine ⟨had, (euler_iff_of_identity 𝔼 hpo (hik had) hid).mpr fun t ω => ?_⟩
    have := hE t ω
    linarith

/-- Woodford (2003), (1.24) for **Prop. 2.7 under uncertainty**: if `|π̄_t| ≤ ε` along every path,
`|π̄_{−1}| ≤ ε`, `0 ≤ δ < 1`, `0 < u_c ≤ U`, liabilities grow at most at factor `γ`, and
`β γ < exp(−(1 + δ) ε/(1 − δ))`, then the stochastic transversality condition holds for
`P_t = Π_t P_{t−1}`. -/
theorem smooth_tvcS {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β dl pbm1 ε U γ Pm1 A : ℝ}
    (hβ : 0 < β) (hdl0 : 0 ≤ dl) (hdl : dl < 1) (hγ : 0 ≤ γ) (hm : 0 < Pm1)
    (hpb : |pbm1| ≤ ε) (hlt : β * γ < Real.exp (-((1 + dl) * ε / (1 - dl))))
    {uc Infl P D : ℕ → Ω → ℝ} (huc : ∀ t ω, 0 < uc t ω) (hU : ∀ t ω, uc t ω ≤ U)
    (hInfl : ∀ t ω, 0 < Infl t ω)
    (hbd : ∀ t ω, |Nonlinear.smoothLog dl pbm1 (fun s => Infl s ω) t| ≤ ε)
    (hP0 : ∀ ω, P 0 ω = Infl 0 ω * Pm1) (hP : ∀ t ω, P (t + 1) ω = Infl (t + 1) ω * P t ω)
    (hD : ∀ t ω, |D (t + 1) ω| ≤ γ * |D t ω|) (hA : ∀ ω, |D 0 ω| ≤ A) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => β ^ T * uc T ω' * D T ω' / P T ω') ω) atTop (𝓝 0) := by
  have hk : 0 < 1 - dl := by linarith
  have hlog : ∀ s ω, -((1 + dl) * ε / (1 - dl)) ≤ Real.log (Infl s ω) := by
    intro s ω
    have key : ∀ a b : ℝ, |a| ≤ ε → |b| ≤ ε → b = dl * a + (1 - dl) * Real.log (Infl s ω) →
        -((1 + dl) * ε / (1 - dl)) ≤ Real.log (Infl s ω) := by
      intro a b ha hb hab
      rw [neg_le, le_div_iff₀ hk]
      have h1 := (abs_le.mp ha).2
      have h2 := (abs_le.mp hb).1
      have h3 : dl * a ≤ dl * ε := mul_le_mul_of_nonneg_left h1 hdl0
      linarith
    rcases s with _ | s
    · exact key pbm1 _ hpb (hbd 0 ω) rfl
    · exact key _ _ (hbd s ω) (hbd (s + 1) ω) rfl
  refine infl_tvcS 𝔼 hβ (Real.exp_pos _) hγ hm hlt huc hU (fun s ω => ?_) hP0 hP hD hA t ω
  rw [← Real.exp_log (hInfl s ω)]
  exact Real.exp_le_exp.mpr (hlog s ω)

/-- Woodford (2003), **Prop. 2.7, indeterminacy half, genuinely random sunspots**: if
`|δ + (1 − δ)Φ_π| < 1`, the exact stochastic Euler equation has, on the coin-flip tree and with no
fundamental disturbances, bounded adapted sunspot equilibria arbitrarily close to the steady state
whose smoothed inflation depends on the coin. -/
theorem smooth_random_sunspot {β dl : ℝ} {φ : ℝ × ℝ → ℝ} (hβ : 0 < β) (hdl : dl < 1)
    (hss : 1 + φ (1, 0) = β⁻¹) (hφ : ContDiffAt ℝ 1 φ (1, 0))
    (hind : |dl + (1 - dl) * LocalIFT.elast β φ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, c ≠ 0 → |c| ≤ r → ∃ x : Proc (Bool × Bool),
      SolvesS coinSystem (liftII (expT (1 - dl) (Nonlinear.F7 β dl φ))) 0 x ∧ ‖x‖ ≤ ε ∧
        (∀ ω, x (0, ω) = c) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F7 (dl := dl) hβ hss hφ
  refine random_sunspot_expII (by linarith : (1 : ℝ) - dl ≠ 0)
    (Nonlinear.contDiffAt_F7 hβ hss hφ) (Nonlinear.F7_zero hss) ?_
  rw [ha, hb, abs_neg, abs_one]
  exact hind

/-- Woodford (2003), (1.24) under uncertainty for **Props. 2.6 (with `Π* ≡ 1`), 2.8 and 2.13**:
every inflation process with `|log Π_t| ≤ η` in every state, `P_t = Π_t P_{t−1}`, `0 < u_c ≤ U`,
liabilities growing at most at factor `γ` and `β γ < e^{−η}` satisfies the stochastic
transversality condition at every date and state. -/
theorem inflBand_tvcS {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β η U γ Pm1 A : ℝ} (hβ : 0 < β)
    (hγ : 0 ≤ γ) (hm : 0 < Pm1) (hlt : β * γ < Real.exp (-η))
    {uc Infl P D : ℕ → Ω → ℝ} (huc : ∀ t ω, 0 < uc t ω) (hU : ∀ t ω, uc t ω ≤ U)
    (hInfl : ∀ t ω, 0 < Infl t ω) (hbd : ∀ t ω, |Real.log (Infl t ω)| ≤ η)
    (hP0 : ∀ ω, P 0 ω = Infl 0 ω * Pm1) (hP : ∀ t ω, P (t + 1) ω = Infl (t + 1) ω * P t ω)
    (hD : ∀ t ω, |D (t + 1) ω| ≤ γ * |D t ω|) (hA : ∀ ω, |D 0 ω| ≤ A) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => β ^ T * uc T ω' * D T ω' / P T ω') ω) atTop (𝓝 0) := by
  refine infl_tvcS 𝔼 hβ (Real.exp_pos _) hγ hm hlt huc hU (fun s ω => ?_) hP0 hP hD hA t ω
  rw [← Real.exp_log (hInfl s ω)]
  exact Real.exp_le_exp.mpr (neg_le_of_abs_le (hbd s ω))

/-! ## Proposition 2.8: an inertial rule, in levels -/

/-- Woodford (2003), (1.21), **inertial-rule Euler equation under uncertainty**: if
`Θ(ĵ_{t+1}, ĵ_t, ν_{t+1}) = log Π_{t+1}` (the rule inverted for inflation), the exponential form of
`F8` at `(ĵ_t, ĵ_{t+1}, (r̂_t, ν_{t+1}))` is `β(1 + i_t) u_c(t+1)/(u_c(t) Π_{t+1}) − 1`. -/
theorem inertial_exp_identity {ψ : ℝ × ℝ × ℝ → ℝ} {hψ : ContDiffAt ℝ 1 ψ 0}
    {hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0} {β i x' ν' Q u0 u1 : ℝ} (hβ : 0 < β) (hi : 0 < 1 + i)
    (hQ : 0 < Q) (hu0 : 0 < u0) (hu1 : 0 < u1)
    (hΘ : Nonlinear.solveRule ψ hψ hφ (x', Real.log (β * (1 + i)), ν') = Real.log Q) :
    expT 1 (Nonlinear.F8 ψ hψ hφ) (Real.log (β * (1 + i)), x', (Real.log (u0 / u1), ν')) =
      β * (1 + i) * (u1 / (u0 * Q)) - 1 := by
  have h : Nonlinear.F8 ψ hψ hφ (Real.log (β * (1 + i)), x', (Real.log (u0 / u1), ν')) =
      Real.log (β * (1 + i) * (u1 / (u0 * Q))) := by
    simp only [Nonlinear.F8, Nonlinear.lagMap_apply]
    have e : Real.log (β * (1 + i) * (u1 / (u0 * Q))) =
        Real.log (β * (1 + i)) + (Real.log u1 - (Real.log u0 + Real.log Q)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_div hu1.ne' (by positivity),
        Real.log_mul hu0.ne' hQ.ne']
    rw [hΘ, e, Real.log_div hu0.ne' hu1.ne']
    ring
  rw [expT, inv_one, one_mul, h, Real.exp_log (by positivity)]

/-- Woodford (2003), (1.21) and (2.12), pp. 72, 96, **inertial-rule equilibrium under uncertainty,
levels, book form**: positive `Π`, `1 + i > 0` with `i` adapted,
`log β(1 + i_t) = ψ(log Π_t, log β(1 + i_{t−1}), ν_t)` (`i_{−1}` given) and
`(1 + i_t) β E_t[u_c(t+1)/(u_c(t) Π_{t+1})] = 1`. -/
def StochInertialEq {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β : ℝ) (ψ : ℝ × ℝ × ℝ → ℝ)
    (uc ν : ℕ → Ω → ℝ) (im1 : ℝ) (Infl i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < Infl t ω) ∧ (∀ t ω, 0 < 1 + i t ω) ∧ (∀ t, 𝔼.E t (i t) = i t) ∧
    (∀ t ω, Real.log (β * (1 + i t ω)) =
      ψ (Real.log (Infl t ω), Nonlinear.jLag β im1 (fun s => i s ω) t, ν t ω)) ∧
    ∀ t ω, (1 + i t ω) *
      (β * 𝔼.E t (fun ω' => uc (t + 1) ω' / (uc t ω' * Infl (t + 1) ω')) ω) = 1

/-- Woodford (2003), **Prop. 2.8 under uncertainty: the level form is exactly the
log-coordinate form** used in `inertial_local_determinacyS`, with `x_t = log β(1 + i_t)` and
`e_t = (log(u_c(t)/u_c(t+1)), ν_{t+1})`, for all processes within the radius `ρ` on which the
rule can be inverted for inflation (closure, pull-out). -/
theorem inertial_solvesS_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hcl : InfoClosed 𝔼)
    (hpo : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β) {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) :
    ∃ ρ > 0, ∀ (uc ν Infl i : ℕ → Ω → ℝ) (im1 : ℝ) (x : Proc Ω) (e : SProc Ω (ℝ × ℝ)),
      (∀ t ω, 0 < uc t ω) → (∀ t ω, 0 < Infl t ω) → (∀ t ω, 0 < 1 + i t ω) →
      (∀ t ω, Real.log (β * (1 + i t ω)) =
        ψ (Real.log (Infl t ω), Nonlinear.jLag β im1 (fun s => i s ω) t, ν t ω)) →
      (∀ t ω, |Real.log (Infl t ω)| < ρ ∧ |Real.log (β * (1 + i t ω))| < ρ ∧ |ν t ω| < ρ) →
      (∀ t ω, x (t, ω) = Real.log (β * (1 + i t ω))) →
      (∀ t ω, e (t, ω) = (Real.log (uc t ω / uc (t + 1) ω), ν (t + 1) ω)) →
      (SolvesS 𝔼 (liftII (expT 1 (Nonlinear.F8 ψ hψ hφ))) e x ↔
        StochInertialEq 𝔼 β ψ uc ν im1 Infl i) := by
  obtain ⟨ρ, hρ, hL, -⟩ := Nonlinear.solveRule_local hψ hφ h0
  refine ⟨ρ, hρ, fun uc ν Infl i im1 x e huc hInfl hi hrule hsm hx he => ?_⟩
  have hΘ : ∀ t ω, Nonlinear.solveRule ψ hψ hφ (Real.log (β * (1 + i (t + 1) ω)),
      Real.log (β * (1 + i t ω)), ν (t + 1) ω) = Real.log (Infl (t + 1) ω) := by
    intro t ω
    have hq : ‖((Real.log (Infl (t + 1) ω), Real.log (β * (1 + i t ω)), ν (t + 1) ω) :
        ℝ × ℝ × ℝ)‖ < ρ := by
      rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt (hsm (t + 1) ω).1 (max_lt (hsm t ω).2.1 (hsm (t + 1) ω).2.2)
    have h := hL _ hq
    have hr := hrule (t + 1) ω
    change Real.log (β * (1 + i (t + 1) ω)) =
      ψ (Real.log (Infl (t + 1) ω), Real.log (β * (1 + i t ω)), ν (t + 1) ω) at hr
    rw [← hr] at h
    exact h
  have hadapt : ∀ t, 𝔼.E t (slice x t) = slice x t ↔ 𝔼.E t (i t) = i t := by
    intro t
    constructor
    · intro h
      refine known_of_fn hcl (cellConst_of_known 𝔼 h) (fun a => Real.exp a / β - 1)
        (fun ω => ?_)
      change i t ω = Real.exp (x (t, ω)) / β - 1
      rw [hx, Real.exp_log (mul_pos hβ (hi t ω))]
      field_simp
      ring
    · intro h
      exact known_of_fn hcl (cellConst_of_known 𝔼 h) (fun a => Real.log (β * (1 + a)))
        (fun ω => hx t ω)
  have hik : (∀ t, 𝔼.E t (i t) = i t) →
      ∀ t, 𝔼.E t (fun ω => β * (1 + i t ω)) = fun ω => β * (1 + i t ω) := fun h t =>
    known_of_fn hcl (cellConst_of_known 𝔼 (h t)) (fun a => β * (1 + a)) (fun _ => rfl)
  have hid : ∀ t ω, expT 1 (Nonlinear.F8 ψ hψ hφ) (x (t, ω), x (t + 1, ω), e (t, ω)) =
      β * (1 + i t ω) * (uc (t + 1) ω / (uc t ω * Infl (t + 1) ω)) - 1 := by
    intro t ω
    rw [hx, hx, he]
    exact inertial_exp_identity hβ (hi t ω) (hInfl (t + 1) ω) (huc t ω) (huc (t + 1) ω)
      (hΘ t ω)
  rw [solvesS_liftII_eq]
  constructor
  · rintro ⟨had, hE⟩
    have hik' : ∀ t, 𝔼.E t (i t) = i t := fun t => (hadapt t).mp (had t)
    refine ⟨hInfl, hi, hik', hrule, fun t ω => ?_⟩
    have h := ((euler_iff_of_identity 𝔼 hpo (hik hik') hid).mp hE) t ω
    linarith
  · rintro ⟨-, -, hik', -, hE⟩
    refine ⟨fun t => (hadapt t).mpr (hik' t),
      (euler_iff_of_identity 𝔼 hpo (hik hik') hid).mpr fun t ω => ?_⟩
    have := hE t ω
    linarith

/-- Woodford (2003), **Prop. 2.8, indeterminacy half, genuinely random sunspots**: if
`|φ_π + ρ| < 1`, the exact stochastic Euler equation of the inertial-rule model has, on the
coin-flip tree and with no fundamental disturbances, bounded adapted sunspot equilibria
arbitrarily close to the steady state whose interest rate depends on the coin. -/
theorem inertial_random_sunspot {ψ : ℝ × ℝ × ℝ → ℝ} (hψ : ContDiffAt ℝ 1 ψ 0)
    (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hind : |Nonlinear.phiPi ψ + Nonlinear.rhoR ψ| < 1) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, c ≠ 0 → |c| ≤ r → ∃ x : Proc (Bool × Bool),
      SolvesS coinSystem (liftII (expT 1 (Nonlinear.F8 ψ hψ hφ))) 0 x ∧ ‖x‖ ≤ ε ∧
        (∀ ω, x (0, ω) = c) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F8 hψ hφ h0
  refine random_sunspot_expII one_ne_zero (Nonlinear.contDiffAt_F8 hψ hφ h0 hψ)
    (Nonlinear.F8_zero hψ hφ h0) ?_
  rw [ha, hb]
  exact (Nonlinear.inertial_slope_iff' hφ).mpr hind

/-! ## Proposition 2.11: money-growth targeting, in levels -/

/-- Woodford (2003), (1.21): with the pull-out property, if `G(x_t, x_{t+1}, e_t) =
c_t (k_t X_t − 1)` with `c_t ≠ 0` and `k_t` known, the stochastic conditions are the book's form
`k_t E_t[X_t] = 1`. -/
theorem euler_iff_of_identity' {Ω E : Type*} [NormedAddCommGroup E] (𝔼 : ExpectationSystem Ω)
    (hpo : 𝔼.PullOut) {G : ℝ × ℝ × E → ℝ} {x : Proc Ω} {e : SProc Ω E} {c k X : ℕ → Ω → ℝ}
    (hc : ∀ t, 𝔼.E t (c t) = c t) (hc0 : ∀ t ω, c t ω ≠ 0) (hk : ∀ t, 𝔼.E t (k t) = k t)
    (hid : ∀ t ω, G (x (t, ω), x (t + 1, ω), e (t, ω)) = c t ω * (k t ω * X t ω - 1)) :
    (∀ t, 𝔼.E t (fun ω => G (x (t, ω), x (t + 1, ω), e (t, ω))) = 0) ↔
      ∀ t ω, k t ω * 𝔼.E t (X t) ω = 1 := by
  refine forall_congr' fun t => ?_
  have hfun : (fun ω => G (x (t, ω), x (t + 1, ω), e (t, ω))) =
      c t * fun ω => k t ω * X t ω - 1 := funext (hid t)
  have h1 : 𝔼.E t (fun ω => k t ω * X t ω - 1) = k t * 𝔼.E t (X t) - fun _ => 1 := by
    have e1 : (fun ω => k t ω * X t ω - 1) = k t * X t - fun _ => 1 := rfl
    rw [e1, map_sub, hpo t (k t) (X t) (hk t), 𝔼.const]
  rw [hfun, hpo t (c t) _ (hc t), h1]
  constructor
  · intro h ω
    have := congrFun h ω
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.zero_apply] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (hc0 t ω)
    · linarith
  · intro h
    funext ω
    simp [h ω]

/-- Woodford (2003), (3.3) and (1.21), **money-growth Euler equation under uncertainty**: if
`R(Y, M/P; ξ) = (i − iᵐ)/(1 + i)`, then at `x = log(M/(P m̄))`, `x' = log(M'/(P' m̄))`,
`e = (log(Y/Ȳ), ξ, log(u_c/u_c') + log(M'/M) − log((1 + iᵐ)/(1 + īᵐ)))`,
`FMGS = −(1 + iᵐ)/(1 + i) · M/(P m̄) · (β(1 + i) u_c' P/(u_c P') − 1)`. -/
theorem mg_exp_identity {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hYb : 0 < Ybar)
    (hm : 0 < mbar) (hibm : 0 < 1 + ibm) {P0 P1 M0 M1 u0 u1 Y ξ im i : ℝ} (hP0 : 0 < P0)
    (hP1 : 0 < P1) (hM0 : 0 < M0) (hM1 : 0 < M1) (hu0 : 0 < u0) (hu1 : 0 < u1) (hY : 0 < Y)
    (him : 0 < 1 + im) (hi : 0 < 1 + i) (hR : R (Y, M0 / P0, ξ) = (i - im) / (1 + i)) :
    LocalIFTStochastic.Models.FMGS β ibm Ybar mbar R (Real.log (M0 / (P0 * mbar)),
        Real.log (M1 / (P1 * mbar)), (Real.log (Y / Ybar), ξ, Real.log (u0 / u1) +
          Real.log (M1 / M0) - Real.log ((1 + im) / (1 + ibm)))) =
      -((1 + im) / (1 + i) * (M0 / (P0 * mbar)) * (β * (1 + i) * (u1 * P0 / (u0 * P1)) - 1)) := by
  simp only [LocalIFTStochastic.Models.FMGS, Nonlinear.FMG]
  rw [Real.exp_log (div_pos hY hYb), Real.exp_log (by positivity : 0 < M0 / (P0 * mbar))]
  have e1 : Ybar * (Y / Ybar) = Y := by field_simp
  have e2 : mbar * (M0 / (P0 * mbar)) = M0 / P0 := by field_simp
  rw [e1, e2, hR, Real.exp_neg, Real.exp_add, Real.exp_log (by positivity : 0 < M0 / (P0 * mbar)),
    Real.exp_sub, Real.exp_add, Real.exp_log (div_pos hu0 hu1), Real.exp_log (div_pos hM1 hM0),
    Real.exp_log (div_pos him hibm), Real.exp_log (by positivity : 0 < M1 / (P1 * mbar))]
  field_simp
  ring

/-- Woodford (2003), (1.21) and (3.3), pp. 72, 104, **money-growth-targeting equilibrium under
uncertainty, levels, book form**: positive adapted `P`, `1 + i > 0`,
`u_m/u_c(Y_t, M_t/P_t; ξ_t) = (i_t − iᵐ_t)/(1 + i_t)` and
`(1 + i_t) β E_t[u_c(t+1) P_t/(u_c(t) P_{t+1})] = 1`. -/
def StochMGEq {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β : ℝ) (R : ℝ × ℝ × ℝ → ℝ)
    (uc M im Y ξ P i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ (∀ t, 𝔼.E t (P t) = P t) ∧ (∀ t ω, 0 < 1 + i t ω) ∧
    (∀ t ω, R (Y t ω, M t ω / P t ω, ξ t ω) = (i t ω - im t ω) / (1 + i t ω)) ∧
    ∀ t ω, (1 + i t ω) *
      (β * 𝔼.E t (fun ω' => uc (t + 1) ω' * P t ω' / (uc t ω' * P (t + 1) ω')) ω) = 1

/-- Woodford (2003), **Prop. 2.11 under uncertainty: the level form is exactly the
log-coordinate form** `E_t[FMGS] = 0` used in `mg_local_determinacyS`, with
`x_t = log(M_t/(P_t m̄))` and
`e_t = (log(Y_t/Ȳ), ξ_t, log(u_c(t)/u_c(t+1)) + log(M_{t+1}/M_t) − log((1 + iᵐ_t)/(1 + īᵐ)))`
(closure, pull-out, known `M_t, iᵐ_t, Y_t, ξ_t`). -/
theorem mg_solvesS_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hcl : InfoClosed 𝔼)
    (hpo : 𝔼.PullOut) {β ibm Ybar mbar : ℝ} {R : ℝ × ℝ × ℝ → ℝ} (hYb : 0 < Ybar)
    (hm : 0 < mbar) (hibm : 0 < 1 + ibm) {uc M im Y ξ P i : ℕ → Ω → ℝ}
    (huc : ∀ t ω, 0 < uc t ω) (hM : ∀ t ω, 0 < M t ω) (him : ∀ t ω, 0 < 1 + im t ω)
    (hY : ∀ t ω, 0 < Y t ω) (hMk : ∀ t, 𝔼.E t (M t) = M t) (himk : ∀ t, 𝔼.E t (im t) = im t)
    (hYk : ∀ t, 𝔼.E t (Y t) = Y t) (hξk : ∀ t, 𝔼.E t (ξ t) = ξ t) (hP : ∀ t ω, 0 < P t ω)
    (hi : ∀ t ω, 0 < 1 + i t ω)
    (hR : ∀ t ω, R (Y t ω, M t ω / P t ω, ξ t ω) = (i t ω - im t ω) / (1 + i t ω))
    {x : Proc Ω} {e : SProc Ω (ℝ × ℝ × ℝ)}
    (hx : ∀ t ω, x (t, ω) = Real.log (M t ω / (P t ω * mbar)))
    (he : ∀ t ω, e (t, ω) = (Real.log (Y t ω / Ybar), ξ t ω, Real.log (uc t ω / uc (t + 1) ω) +
      Real.log (M (t + 1) ω / M t ω) - Real.log ((1 + im t ω) / (1 + ibm)))) :
    SolvesS 𝔼 (liftII (LocalIFTStochastic.Models.FMGS β ibm Ybar mbar R)) e x ↔
      StochMGEq 𝔼 β R uc M im Y ξ P i := by
  have hadapt : ∀ t, 𝔼.E t (slice x t) = slice x t ↔ 𝔼.E t (P t) = P t := by
    intro t
    have hMc := cellConst_of_known 𝔼 (hMk t)
    constructor
    · intro h
      refine known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 h) hMc)
        (fun q => q.2 / (mbar * Real.exp q.1)) (fun ω => ?_)
      change P t ω = M t ω / (mbar * Real.exp (x (t, ω)))
      rw [hx, Real.exp_log (div_pos (hM t ω) (mul_pos (hP t ω) hm))]
      field_simp [(hM t ω).ne']
    · intro h
      exact known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 h) hMc)
        (fun q => Real.log (q.2 / (q.1 * mbar))) (fun ω => hx t ω)
  have hiform : ∀ t ω, i t ω = (R (Y t ω, M t ω / P t ω, ξ t ω) + im t ω) /
      (1 - R (Y t ω, M t ω / P t ω, ξ t ω)) := by
    intro t ω
    have h1 := hi t ω
    have h2 := him t ω
    rw [hR]
    have hne : 1 - (i t ω - im t ω) / (1 + i t ω) ≠ 0 := by
      rw [one_sub_div h1.ne']
      exact div_ne_zero (by linarith) h1.ne'
    rw [eq_div_iff hne]
    field_simp
    ring
  have hknown : (∀ t, 𝔼.E t (P t) = P t) → ∀ t,
      CellConst 𝔼 t (fun ω => ((P t ω, M t ω), (im t ω, Y t ω), ξ t ω)) := fun h t =>
    cellConst_pair (cellConst_pair (cellConst_of_known 𝔼 (h t)) (cellConst_of_known 𝔼 (hMk t)))
      (cellConst_pair (cellConst_pair (cellConst_of_known 𝔼 (himk t))
        (cellConst_of_known 𝔼 (hYk t))) (cellConst_of_known 𝔼 (hξk t)))
  have hik : (∀ t, 𝔼.E t (P t) = P t) →
      ∀ t, 𝔼.E t (fun ω => β * (1 + i t ω)) = fun ω => β * (1 + i t ω) := fun h t =>
    known_of_fn hcl (hknown h t) (fun q => β * (1 + (R (q.2.1.2, q.1.2 / q.1.1, q.2.2) +
      q.2.1.1) / (1 - R (q.2.1.2, q.1.2 / q.1.1, q.2.2)))) (fun ω => by rw [hiform t ω])
  have hck : (∀ t, 𝔼.E t (P t) = P t) → ∀ t,
      𝔼.E t (fun ω => -((1 + im t ω) / (1 + i t ω) * (M t ω / (P t ω * mbar)))) =
        fun ω => -((1 + im t ω) / (1 + i t ω) * (M t ω / (P t ω * mbar))) := fun h t =>
    known_of_fn hcl (hknown h t) (fun q => -((1 + q.2.1.1) / (1 + (R (q.2.1.2, q.1.2 / q.1.1,
      q.2.2) + q.2.1.1) / (1 - R (q.2.1.2, q.1.2 / q.1.1, q.2.2))) * (q.1.2 / (q.1.1 * mbar))))
      (fun ω => by rw [hiform t ω])
  have hc0 : ∀ t ω, -((1 + im t ω) / (1 + i t ω) * (M t ω / (P t ω * mbar))) ≠ 0 := by
    intro t ω
    have h1 := hi t ω
    have h2 := him t ω
    have h3 := hM t ω
    have h4 := hP t ω
    have : 0 < (1 + im t ω) / (1 + i t ω) * (M t ω / (P t ω * mbar)) := by positivity
    linarith
  have hid : ∀ t ω, LocalIFTStochastic.Models.FMGS β ibm Ybar mbar R
      (x (t, ω), x (t + 1, ω), e (t, ω)) =
      -((1 + im t ω) / (1 + i t ω) * (M t ω / (P t ω * mbar))) *
        (β * (1 + i t ω) * (uc (t + 1) ω * P t ω / (uc t ω * P (t + 1) ω)) - 1) := by
    intro t ω
    rw [hx, hx, he, mg_exp_identity hYb hm hibm (hP t ω) (hP (t + 1) ω) (hM t ω) (hM (t + 1) ω)
      (huc t ω) (huc (t + 1) ω) (hY t ω) (him t ω) (hi t ω) (hR t ω)]
    ring
  rw [solvesS_liftII_eq]
  constructor
  · rintro ⟨had, hE⟩
    have hPk : ∀ t, 𝔼.E t (P t) = P t := fun t => (hadapt t).mp (had t)
    refine ⟨hP, hPk, hi, hR, fun t ω => ?_⟩
    have h := ((euler_iff_of_identity' 𝔼 hpo (hck hPk) hc0 (hik hPk) hid).mp hE) t ω
    linarith
  · rintro ⟨-, hPk, -, -, hE⟩
    refine ⟨fun t => (hadapt t).mpr (hPk t),
      (euler_iff_of_identity' 𝔼 hpo (hck hPk) hc0 (hik hPk) hid).mpr fun t ω => ?_⟩
    have := hE t ω
    linarith

/-- Woodford (2003), (1.24) for **Prop. 2.11 under uncertainty**: if `0 < u_c ≤ U`, money grows at
least at factor `θ` from `M_0 ≥ s₀ > 0`, total liabilities grow at most at factor `γ`, and
`β γ < θ`, every price process with `|log(M_t/(P_t m̄))| ≤ ε` satisfies the stochastic
transversality condition at every date and state. -/
theorem mg_tvcS {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β ε U θ γ s0 A mbar : ℝ} (hβ : 0 < β)
    (hθ : 0 < θ) (hγ : 0 ≤ γ) (hs0 : 0 < s0) (hm : 0 < mbar) (hlt : β * γ < θ)
    {uc M P D : ℕ → Ω → ℝ} (huc : ∀ t ω, 0 < uc t ω) (hU : ∀ t ω, uc t ω ≤ U)
    (hM0 : ∀ ω, s0 ≤ M 0 ω) (hMg : ∀ t ω, θ * M t ω ≤ M (t + 1) ω) (hP : ∀ t ω, 0 < P t ω)
    (hbd : ∀ t ω, |Real.log (M t ω / (P t ω * mbar))| ≤ ε)
    (hD : ∀ t ω, |D (t + 1) ω| ≤ γ * |D t ω|) (hA : ∀ ω, |D 0 ω| ≤ A) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E t (fun ω' => β ^ T * uc T ω' * D T ω' / P T ω') ω) atTop (𝓝 0) := by
  have hDb : ∀ T ω, |D T ω| ≤ A * γ ^ T := by
    intro T ω
    induction T with
    | zero => simpa using hA ω
    | succ n ih =>
      calc |D (n + 1) ω| ≤ γ * |D n ω| := hD n ω
        _ ≤ γ * (A * γ ^ n) := mul_le_mul_of_nonneg_left ih hγ
        _ = A * γ ^ (n + 1) := by ring
  have hMgr := growth_lower hθ.le hM0 hMg
  have hMpos : ∀ T ω, 0 < M T ω := fun T ω => lt_of_lt_of_le (by positivity) (hMgr T ω)
  refine stochTVC_of_bounds 𝔼 hβ (by positivity : 0 < s0 * Real.exp (-ε) / mbar) hθ hγ hlt
    (fun T ω => (huc T ω).le) hU hDb (fun T ω => ?_) t ω
  have hr : M T ω / (P T ω * mbar) ≤ Real.exp ε := by
    rw [← Real.exp_log (div_pos (hMpos T ω) (mul_pos (hP T ω) hm))]
    exact Real.exp_le_exp.mpr (le_of_abs_le (hbd T ω))
  rw [div_le_iff₀ (mul_pos (hP T ω) hm)] at hr
  have hPl : M T ω * Real.exp (-ε) / mbar ≤ P T ω := by
    rw [div_le_iff₀ hm, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos ε)]
    linarith
  calc s0 * Real.exp (-ε) / mbar * θ ^ T = s0 * θ ^ T * Real.exp (-ε) / mbar := by ring
    _ ≤ M T ω * Real.exp (-ε) / mbar := by
        gcongr
        exact hMgr T ω
    _ ≤ P T ω := hPl

/-! ## Proposition 2.12: a Wicksellian rule with non-separable utility, in levels -/

/-- Woodford (2003), (1.21), (3.5), (1.30), **Euler equation under uncertainty with non-separable
utility**: at `p = log(P_t/P*_t)`, `p' = log(P_{t+1}/P*_{t+1})` and the disturbance vector of
`Nonlinear.nsw_step`, `exp FW − 1 = β(1 + i_t) U_c(t+1) P_t/(U_c(t) P_{t+1}) − 1` with
`i = φ(P/P*; ν)` and `U_c(t) = u_c(Y_t, L(Y_t, (i_t − īᵐ)/(1 + i_t); ξ_t); ξ_t)`. -/
theorem nsw_exp_identity {β ibm Ybar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar) {P0 P1 S0 S1 Y0 Y1 ν0 ν1 ξ0 ξ1 : ℝ} (hP0 : 0 < P0) (hP1 : 0 < P1)
    (hS0 : 0 < S0) (hS1 : 0 < S1) (hY0 : 0 < Y0) (hY1 : 0 < Y1)
    (hi0 : 0 < 1 + φ (P0 / S0, ν0)) (hi1 : 0 < 1 + φ (P1 / S1, ν1))
    (hU0 : 0 < Uc (Y0, L (Y0, (φ (P0 / S0, ν0) - ibm) / (1 + φ (P0 / S0, ν0)), ξ0), ξ0))
    (hU1 : 0 < Uc (Y1, L (Y1, (φ (P1 / S1, ν1) - ibm) / (1 + φ (P1 / S1, ν1)), ξ1), ξ1)) :
    expT 1 (Nonlinear.FW β ibm Ybar φ L Uc) (Real.log (P0 / S0), Real.log (P1 / S1),
        ((ν0, Real.log (Y0 / Ybar), ξ0), (ν1, Real.log (Y1 / Ybar), ξ1), Real.log (S1 / S0))) =
      β * (1 + φ (P0 / S0, ν0)) *
        (Uc (Y1, L (Y1, (φ (P1 / S1, ν1) - ibm) / (1 + φ (P1 / S1, ν1)), ξ1), ξ1) * P0 /
          (Uc (Y0, L (Y0, (φ (P0 / S0, ν0) - ibm) / (1 + φ (P0 / S0, ν0)), ξ0), ξ0) * P1)) - 1 := by
  set U0 := Uc (Y0, L (Y0, (φ (P0 / S0, ν0) - ibm) / (1 + φ (P0 / S0, ν0)), ξ0), ξ0) with hU0d
  set U1 := Uc (Y1, L (Y1, (φ (P1 / S1, ν1) - ibm) / (1 + φ (P1 / S1, ν1)), ξ1), ξ1) with hU1d
  have h : Nonlinear.FW β ibm Ybar φ L Uc (Real.log (P0 / S0), Real.log (P1 / S1),
      ((ν0, Real.log (Y0 / Ybar), ξ0), (ν1, Real.log (Y1 / Ybar), ξ1), Real.log (S1 / S0))) =
      Real.log (β * (1 + φ (P0 / S0, ν0)) * (U1 * P0 / (U0 * P1))) := by
    simp only [Nonlinear.FW]
    rw [Nonlinear.logRule_at hβ (div_pos hP0 hS0) hi0,
      Nonlinear.logRule_at hβ (div_pos hP1 hS1) hi1, Nonlinear.lamI_at hβ hYb hY0 hi0,
      Nonlinear.lamI_at hβ hYb hY1 hi1]
    have e : Real.log (β * (1 + φ (P0 / S0, ν0)) * (U1 * P0 / (U0 * P1))) =
        Real.log (β * (1 + φ (P0 / S0, ν0))) + (Real.log U1 + Real.log P0) -
          (Real.log U0 + Real.log P1) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity)
        (by positivity), Real.log_mul hU1.ne' hP0.ne', Real.log_mul hU0.ne' hP1.ne']
      ring
    rw [e, Real.log_div hP0.ne' hS0.ne', Real.log_div hP1.ne' hS1.ne',
      Real.log_div hS1.ne' hS0.ne']
    ring
  rw [expT, inv_one, one_mul, h, Real.exp_log (by positivity)]

/-- Woodford (2003), Definition p. 105 with (1.21), (3.5), (1.30), **Wicksellian equilibrium with
non-separable utility under uncertainty, levels, book form**: positive adapted `P`,
`i_t = φ(P_t/P*_t; ν_t)`, `m_t = L(Y_t, (i_t − īᵐ)/(1 + i_t); ξ_t)` and
`(1 + i_t) β E_t[u_c(Y_{t+1}, m_{t+1}; ξ_{t+1}) P_t/(u_c(Y_t, m_t; ξ_t) P_{t+1})] = 1`. -/
def StochNSWEq {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β ibm : ℝ) (φ : ℝ × ℝ → ℝ)
    (L Uc : ℝ × ℝ × ℝ → ℝ) (Y ξ ν Pstar P i m : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < P t ω) ∧ (∀ t, 𝔼.E t (P t) = P t) ∧
    (∀ t ω, i t ω = φ (P t ω / Pstar t ω, ν t ω)) ∧
    (∀ t ω, m t ω = L (Y t ω, (i t ω - ibm) / (1 + i t ω), ξ t ω)) ∧
    ∀ t ω, (1 + i t ω) * (β * 𝔼.E t (fun ω' => Uc (Y (t + 1) ω', m (t + 1) ω', ξ (t + 1) ω') *
      P t ω' / (Uc (Y t ω', m t ω', ξ t ω') * P (t + 1) ω')) ω) = 1

/-- Woodford (2003), **Prop. 2.12 under uncertainty: the level form is exactly the
log-coordinate form** used in `nsw_local_determinacyS`, with `x_t = log(P_t/P*_t)` and
`e_t = ((ν_t, log(Y_t/Ȳ), ξ_t), (ν_{t+1}, log(Y_{t+1}/Ȳ), ξ_{t+1}), log(P*_{t+1}/P*_t))`
(closure, pull-out, known `P*_t`, `ν_t`). -/
theorem nsw_solvesS_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hcl : InfoClosed 𝔼)
    (hpo : 𝔼.PullOut) {β ibm Ybar : ℝ} {φ : ℝ × ℝ → ℝ} {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β)
    (hYb : 0 < Ybar) (hpos : ∀ A : ℝ, 0 < A → ∀ ν : ℝ, 0 < 1 + φ (A, ν))
    {Y ξ ν Pstar P i m : ℕ → Ω → ℝ} (hY : ∀ t ω, 0 < Y t ω) (hPS : ∀ t ω, 0 < Pstar t ω)
    (hPSk : ∀ t, 𝔼.E t (Pstar t) = Pstar t) (hνk : ∀ t, 𝔼.E t (ν t) = ν t)
    (hP : ∀ t ω, 0 < P t ω) (hrule : ∀ t ω, i t ω = φ (P t ω / Pstar t ω, ν t ω))
    (hmr : ∀ t ω, m t ω = L (Y t ω, (i t ω - ibm) / (1 + i t ω), ξ t ω))
    (hU : ∀ t ω, 0 < Uc (Y t ω, m t ω, ξ t ω))
    {x : Proc Ω} {e : SProc Ω ((ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) × ℝ)}
    (hx : ∀ t ω, x (t, ω) = Real.log (P t ω / Pstar t ω))
    (he : ∀ t ω, e (t, ω) = ((ν t ω, Real.log (Y t ω / Ybar), ξ t ω),
      (ν (t + 1) ω, Real.log (Y (t + 1) ω / Ybar), ξ (t + 1) ω),
      Real.log (Pstar (t + 1) ω / Pstar t ω))) :
    SolvesS 𝔼 (liftII (expT 1 (Nonlinear.FW β ibm Ybar φ L Uc))) e x ↔
      StochNSWEq 𝔼 β ibm φ L Uc Y ξ ν Pstar P i m := by
  have hadapt : ∀ t, 𝔼.E t (slice x t) = slice x t ↔ 𝔼.E t (P t) = P t := by
    intro t
    have hPc := cellConst_of_known 𝔼 (hPSk t)
    constructor
    · intro h
      refine known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 h) hPc)
        (fun q => q.2 * Real.exp q.1) (fun ω => ?_)
      change P t ω = Pstar t ω * Real.exp (x (t, ω))
      rw [hx, Real.exp_log (div_pos (hP t ω) (hPS t ω))]
      field_simp [(hPS t ω).ne']
    · intro h
      exact known_of_fn hcl (cellConst_pair (cellConst_of_known 𝔼 h) hPc)
        (fun q => Real.log (q.1 / q.2)) (fun ω => hx t ω)
  have hik : (∀ t, 𝔼.E t (P t) = P t) →
      ∀ t, 𝔼.E t (fun ω => β * (1 + i t ω)) = fun ω => β * (1 + i t ω) := by
    intro h t
    refine known_of_fn hcl (cellConst_pair (cellConst_pair (cellConst_of_known 𝔼 (h t))
      (cellConst_of_known 𝔼 (hPSk t))) (cellConst_of_known 𝔼 (hνk t)))
      (fun q => β * (1 + φ (q.1.1 / q.1.2, q.2))) (fun ω => ?_)
    simp only [hrule t ω]
  have hid : ∀ t ω, expT 1 (Nonlinear.FW β ibm Ybar φ L Uc) (x (t, ω), x (t + 1, ω), e (t, ω)) =
      β * (1 + i t ω) * (Uc (Y (t + 1) ω, m (t + 1) ω, ξ (t + 1) ω) * P t ω /
        (Uc (Y t ω, m t ω, ξ t ω) * P (t + 1) ω)) - 1 := by
    intro t ω
    have hU0 := hU t ω
    have hU1 := hU (t + 1) ω
    rw [hmr, hrule] at hU0 hU1
    rw [hx, hx, he, nsw_exp_identity hβ hYb (hP t ω) (hP (t + 1) ω) (hPS t ω) (hPS (t + 1) ω)
      (hY t ω) (hY (t + 1) ω) (hpos _ (div_pos (hP t ω) (hPS t ω)) _)
      (hpos _ (div_pos (hP (t + 1) ω) (hPS (t + 1) ω)) _) hU0 hU1, hmr t ω, hmr (t + 1) ω,
      hrule t ω, hrule (t + 1) ω]
  rw [solvesS_liftII_eq]
  constructor
  · rintro ⟨had, hE⟩
    have hPk : ∀ t, 𝔼.E t (P t) = P t := fun t => (hadapt t).mp (had t)
    refine ⟨hP, hPk, hrule, hmr, fun t ω => ?_⟩
    have h := ((euler_iff_of_identity 𝔼 hpo (hik hPk) hid).mp hE) t ω
    linarith
  · rintro ⟨-, hPk, -, -, hE⟩
    refine ⟨fun t => (hadapt t).mpr (hPk t), (euler_iff_of_identity 𝔼 hpo (hik hPk) hid).mpr
      fun t ω => ?_⟩
    have := hE t ω
    linarith

/-- Woodford (2003), **Prop. 2.12, indeterminacy half, genuinely random sunspots**: if
`|A| < |B|` ((A.32) fails strictly), the exact stochastic Euler equation has, on the coin-flip
tree and with no fundamental disturbances, bounded adapted sunspot equilibria arbitrarily close to
the steady state whose price level depends on the coin. -/
theorem nsw_random_sunspot {β ibm Ybar mbar : ℝ} {φ : ℝ × ℝ → ℝ}
    {L Uc : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) (hm : 0 < mbar) (hss : 1 + φ (1, 0) = β⁻¹)
    (hφ : ContDiffAt ℝ 1 φ (1, 0)) (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hBA : |NonSeparable.A212 (Nonlinear.etaNS β ibm mbar Ybar L) (Nonlinear.chiNS Ybar mbar Uc)
      (LocalIFT.elast β φ)| < |NonSeparable.B212 (Nonlinear.etaNS β ibm mbar Ybar L)
        (Nonlinear.chiNS Ybar mbar Uc) (LocalIFT.elast β φ)|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, c ≠ 0 → |c| ≤ r →
      ∃ x : Proc (Bool × Bool),
        SolvesS coinSystem (liftII (expT 1 (Nonlinear.FW β ibm Ybar φ L Uc))) 0 x ∧
        ‖x‖ ≤ ε ∧ (∀ ω, x (0, ω) = c) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  obtain ⟨ha, hb⟩ := Nonlinear.slopes_FW hβ hm hss hφ hL hLss hU hUpos
  refine random_sunspot_expII one_ne_zero (Nonlinear.contDiffAt_FW hβ hss hφ hL hLss hU hUpos)
    (Nonlinear.FW_zero hss) ?_
  rw [ha, hb, abs_neg]
  exact hBA

/-! ## Proposition 2.13: an inertial rule with non-separable utility, in levels -/

/-- Woodford (2003), (1.21), (3.5), **inertial-rule Euler equation under uncertainty with
non-separable utility**: if `Θ(ĵ_{t+1}, ĵ_t, ν_{t+1}) = log Π_{t+1}`, then
`exp F13 − 1 = β(1 + i_t) U_c(t+1)/(U_c(t) Π_{t+1}) − 1` with
`U_c(t) = u_c(Y_t, L(Y_t, (i_t − īᵐ)/(1 + i_t); ξ_t); ξ_t)`. -/
theorem nsi_exp_identity {β ibm Ybar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} {hψ : ContDiffAt ℝ 1 ψ 0}
    {hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0} (hβ : 0 < β) (hYb : 0 < Ybar)
    {i0 i1 Y0 Y1 ξ0 ξ1 ν1 Q : ℝ} (hi0 : 0 < 1 + i0) (hi1 : 0 < 1 + i1) (hY0 : 0 < Y0)
    (hY1 : 0 < Y1) (hQ : 0 < Q)
    (hU0 : 0 < Uc (Y0, L (Y0, (i0 - ibm) / (1 + i0), ξ0), ξ0))
    (hU1 : 0 < Uc (Y1, L (Y1, (i1 - ibm) / (1 + i1), ξ1), ξ1))
    (hΘ : Nonlinear.solveRule ψ hψ hφ (Real.log (β * (1 + i1)), Real.log (β * (1 + i0)), ν1) =
      Real.log Q) :
    expT 1 (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ) (Real.log (β * (1 + i0)),
        Real.log (β * (1 + i1)), ((Real.log (Y0 / Ybar), ξ0), (Real.log (Y1 / Ybar), ξ1), ν1)) =
      β * (1 + i0) * (Uc (Y1, L (Y1, (i1 - ibm) / (1 + i1), ξ1), ξ1) /
        (Uc (Y0, L (Y0, (i0 - ibm) / (1 + i0), ξ0), ξ0) * Q)) - 1 := by
  set U0 := Uc (Y0, L (Y0, (i0 - ibm) / (1 + i0), ξ0), ξ0) with hU0d
  set U1 := Uc (Y1, L (Y1, (i1 - ibm) / (1 + i1), ξ1), ξ1) with hU1d
  obtain ⟨m1, m2, m3⟩ := Nonlinear.maps13_apply (Real.log (β * (1 + i0)))
    (Real.log (β * (1 + i1))) (Real.log (Y0 / Ybar)) ξ0 (Real.log (Y1 / Ybar)) ξ1 ν1
  have h : Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ (Real.log (β * (1 + i0)),
      Real.log (β * (1 + i1)), ((Real.log (Y0 / Ybar), ξ0), (Real.log (Y1 / Ybar), ξ1), ν1)) =
      Real.log (β * (1 + i0) * (U1 / (U0 * Q))) := by
    simp only [Nonlinear.F13]
    rw [m1, m2, m3, Nonlinear.lamI_at hβ hYb hY0 hi0, Nonlinear.lamI_at hβ hYb hY1 hi1, hΘ]
    have e : Real.log (β * (1 + i0) * (U1 / (U0 * Q))) =
        Real.log (β * (1 + i0)) + (Real.log U1 - (Real.log U0 + Real.log Q)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_div hU1.ne' (by positivity),
        Real.log_mul hU0.ne' hQ.ne']
    rw [e]
    ring
  rw [expT, inv_one, one_mul, h, Real.exp_log (by positivity)]

/-- Woodford (2003), (1.21), (3.5), (2.12), **inertial-rule equilibrium with non-separable utility
under uncertainty, levels, book form**: positive `Π`, adapted `i` with `1 + i > 0`,
`m_t = L(Y_t, (i_t − īᵐ)/(1 + i_t); ξ_t)`, `log β(1 + i_t) = ψ(log Π_t, log β(1 + i_{t−1}), ν_t)`
and `(1 + i_t) β E_t[u_c(Y_{t+1}, m_{t+1}; ξ_{t+1})/(u_c(Y_t, m_t; ξ_t) Π_{t+1})] = 1`. -/
def StochNSIEq {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β ibm : ℝ) (L Uc ψ : ℝ × ℝ × ℝ → ℝ)
    (Y ξ ν : ℕ → Ω → ℝ) (im1 : ℝ) (Infl i m : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < Infl t ω) ∧ (∀ t ω, 0 < 1 + i t ω) ∧ (∀ t, 𝔼.E t (i t) = i t) ∧
    (∀ t ω, m t ω = L (Y t ω, (i t ω - ibm) / (1 + i t ω), ξ t ω)) ∧
    (∀ t ω, Real.log (β * (1 + i t ω)) =
      ψ (Real.log (Infl t ω), Nonlinear.jLag β im1 (fun s => i s ω) t, ν t ω)) ∧
    ∀ t ω, (1 + i t ω) * (β * 𝔼.E t (fun ω' => Uc (Y (t + 1) ω', m (t + 1) ω', ξ (t + 1) ω') /
      (Uc (Y t ω', m t ω', ξ t ω') * Infl (t + 1) ω')) ω) = 1

/-- Woodford (2003), **Prop. 2.13 under uncertainty: the level form is exactly the
log-coordinate form** used in `nsi_local_determinacyS`, with `x_t = log β(1 + i_t)` and
`e_t = ((log(Y_t/Ȳ), ξ_t), (log(Y_{t+1}/Ȳ), ξ_{t+1}), ν_{t+1})`, for all processes within the
radius `ρ` on which the rule can be inverted for inflation (closure, pull-out). -/
theorem nsi_solvesS_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) (hcl : InfoClosed 𝔼)
    (hpo : 𝔼.PullOut) {β ibm Ybar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hβ : 0 < β) (hYb : 0 < Ybar)
    (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0) :
    ∃ ρ > 0, ∀ (Y ξ ν Infl i m : ℕ → Ω → ℝ) (im1 : ℝ) (x : Proc Ω)
      (e : SProc Ω ((ℝ × ℝ) × (ℝ × ℝ) × ℝ)),
      (∀ t ω, 0 < Y t ω) → (∀ t ω, 0 < Infl t ω) → (∀ t ω, 0 < 1 + i t ω) →
      (∀ t ω, m t ω = L (Y t ω, (i t ω - ibm) / (1 + i t ω), ξ t ω)) →
      (∀ t ω, 0 < Uc (Y t ω, m t ω, ξ t ω)) →
      (∀ t ω, Real.log (β * (1 + i t ω)) =
        ψ (Real.log (Infl t ω), Nonlinear.jLag β im1 (fun s => i s ω) t, ν t ω)) →
      (∀ t ω, |Real.log (Infl t ω)| < ρ ∧ |Real.log (β * (1 + i t ω))| < ρ ∧ |ν t ω| < ρ) →
      (∀ t ω, x (t, ω) = Real.log (β * (1 + i t ω))) →
      (∀ t ω, e (t, ω) = ((Real.log (Y t ω / Ybar), ξ t ω),
        (Real.log (Y (t + 1) ω / Ybar), ξ (t + 1) ω), ν (t + 1) ω)) →
      (SolvesS 𝔼 (liftII (expT 1 (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ))) e x ↔
        StochNSIEq 𝔼 β ibm L Uc ψ Y ξ ν im1 Infl i m) := by
  obtain ⟨ρ, hρ, hL, -⟩ := Nonlinear.solveRule_local hψ hφ h0
  refine ⟨ρ, hρ, fun Y ξ ν Infl i m im1 x e hY hInfl hi hmr hU hrule hsm hx he => ?_⟩
  have hΘ : ∀ t ω, Nonlinear.solveRule ψ hψ hφ (Real.log (β * (1 + i (t + 1) ω)),
      Real.log (β * (1 + i t ω)), ν (t + 1) ω) = Real.log (Infl (t + 1) ω) := by
    intro t ω
    have hq : ‖((Real.log (Infl (t + 1) ω), Real.log (β * (1 + i t ω)), ν (t + 1) ω) :
        ℝ × ℝ × ℝ)‖ < ρ := by
      rw [Prod.norm_mk, Prod.norm_mk, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt (hsm (t + 1) ω).1 (max_lt (hsm t ω).2.1 (hsm (t + 1) ω).2.2)
    have h := hL _ hq
    have hr := hrule (t + 1) ω
    change Real.log (β * (1 + i (t + 1) ω)) =
      ψ (Real.log (Infl (t + 1) ω), Real.log (β * (1 + i t ω)), ν (t + 1) ω) at hr
    rw [← hr] at h
    exact h
  have hadapt : ∀ t, 𝔼.E t (slice x t) = slice x t ↔ 𝔼.E t (i t) = i t := by
    intro t
    constructor
    · intro h
      refine known_of_fn hcl (cellConst_of_known 𝔼 h) (fun a => Real.exp a / β - 1)
        (fun ω => ?_)
      change i t ω = Real.exp (x (t, ω)) / β - 1
      rw [hx, Real.exp_log (mul_pos hβ (hi t ω))]
      field_simp
      ring
    · intro h
      exact known_of_fn hcl (cellConst_of_known 𝔼 h) (fun a => Real.log (β * (1 + a)))
        (fun ω => hx t ω)
  have hik : (∀ t, 𝔼.E t (i t) = i t) →
      ∀ t, 𝔼.E t (fun ω => β * (1 + i t ω)) = fun ω => β * (1 + i t ω) := fun h t =>
    known_of_fn hcl (cellConst_of_known 𝔼 (h t)) (fun a => β * (1 + a)) (fun _ => rfl)
  have hid : ∀ t ω, expT 1 (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ)
      (x (t, ω), x (t + 1, ω), e (t, ω)) =
      β * (1 + i t ω) * (Uc (Y (t + 1) ω, m (t + 1) ω, ξ (t + 1) ω) /
        (Uc (Y t ω, m t ω, ξ t ω) * Infl (t + 1) ω)) - 1 := by
    intro t ω
    have hU0 := hU t ω
    have hU1 := hU (t + 1) ω
    rw [hmr] at hU0 hU1
    rw [hx, hx, he, nsi_exp_identity hβ hYb (hi t ω) (hi (t + 1) ω) (hY t ω) (hY (t + 1) ω)
      (hInfl (t + 1) ω) hU0 hU1 (hΘ t ω), hmr t ω, hmr (t + 1) ω]
  rw [solvesS_liftII_eq]
  constructor
  · rintro ⟨had, hE⟩
    have hik' : ∀ t, 𝔼.E t (i t) = i t := fun t => (hadapt t).mp (had t)
    refine ⟨hInfl, hi, hik', hmr, hrule, fun t ω => ?_⟩
    have h := ((euler_iff_of_identity 𝔼 hpo (hik hik') hid).mp hE) t ω
    linarith
  · rintro ⟨-, -, hik', -, -, hE⟩
    refine ⟨fun t => (hadapt t).mpr (hik' t),
      (euler_iff_of_identity 𝔼 hpo (hik hik') hid).mpr fun t ω => ?_⟩
    have := hE t ω
    linarith

/-- Woodford (2003), **Prop. 2.13, indeterminacy half, genuinely random sunspots**: if
`|γ₀| < |γ₁|`, the exact stochastic Euler equation has, on the coin-flip tree and with no
fundamental disturbances, bounded adapted sunspot equilibria arbitrarily close to the steady
state whose interest rate depends on the coin. -/
theorem nsi_random_sunspot {β ibm Ybar mbar : ℝ} {L Uc ψ : ℝ × ℝ × ℝ → ℝ} (hm : 0 < mbar)
    (hψ : ContDiffAt ℝ 1 ψ 0) (h0 : ψ 0 = 0) (hφ : fderiv ℝ ψ 0 (1, 0, 0) ≠ 0)
    (hL : ContDiffAt ℝ 1 L (Ybar, 1 - β * (1 + ibm), 0))
    (hLss : L (Ybar, 1 - β * (1 + ibm), 0) = mbar)
    (hU : ContDiffAt ℝ 1 Uc (Ybar, mbar, 0)) (hUpos : 0 < Uc (Ybar, mbar, 0))
    (hγ : |NonSeparable.gamma0 (Nonlinear.etaNS β ibm mbar Ybar L)
      (Nonlinear.chiNS Ybar mbar Uc) (Nonlinear.phiPi ψ) (Nonlinear.rhoR ψ)| <
      |NonSeparable.gamma1 (Nonlinear.etaNS β ibm mbar Ybar L) (Nonlinear.chiNS Ybar mbar Uc)
        (Nonlinear.phiPi ψ)|) :
    ∀ ε > 0, ∃ r > 0, ∀ c : ℝ, c ≠ 0 → |c| ≤ r →
      ∃ x : Proc (Bool × Bool),
        SolvesS coinSystem (liftII (expT 1 (Nonlinear.F13 β ibm Ybar L Uc ψ hψ hφ))) 0 x ∧
        ‖x‖ ≤ ε ∧ (∀ ω, x (0, ω) = c) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  obtain ⟨ha, hb, -⟩ := Nonlinear.slopes_F13 hψ hφ h0 hm hL hLss hU hUpos
  refine random_sunspot_expII one_ne_zero
    (Nonlinear.contDiffAt_F13 hψ hφ h0 hψ hL hLss hU hUpos) (Nonlinear.F13_zero hψ hφ h0) ?_
  have hpos : 0 < |Nonlinear.phiPi ψ| := abs_pos.mpr hφ
  rw [ha, hb, abs_neg, abs_div, abs_div]
  exact div_lt_div_of_pos_right hγ hpos

end Woodford.PriceLevelDetermination.LocalIFTStochasticModels
