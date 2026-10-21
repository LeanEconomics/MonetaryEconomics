/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LocalIFTSystemsStochastic
import PriceLevelDetermination.LocalIFTSystemsApps
import PriceLevelDetermination.LocalIFTStochasticModels

/-!
# Applications of the stochastic `n`-dimensional theory

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 633–635 (eqs. (A.11)–(A.13)), applied
to a model of the book with a predetermined variable, and linked to the scalar stochastic theory
of `LocalIFTStochastic`.

## The inertial rule (2.12) under uncertainty (Prop. 2.8, p. 96; (A.22))

The exact conditions in the book's stochastic form (A.11), with `x_t = (π_t, î_t)` and
disturbances `e_t = (r̂_t, ν_t)` (not necessarily adapted), are
`E_t[î_t − π_{t+1} − r̂_t] = 0` and `E_t[î_t − Ψ(π_t, î_{t−1}) − ν_t] = 0`
(`LocalIFTSystemsApps.Finert` inside `E_t`); `î_{t−1}` is predetermined.

* `isUnit_linOpS_inert_iff`, `inert_linDeterminateS_iff`: for every expectation system on a
  nonempty state space the exact root condition is `φ_π ≠ 0` and `|φ_π + ρ| > 1` — condition
  (A.22), unchanged by uncertainty.
* `inertial_local_determinacyS`, `inertial_second_orderS`, `inertial_iffS`: stochastic local
  determinacy of the exact model under (A.22), the `O(‖u‖²)` bound for a `C²` rule, and the
  converse.
* Indeterminacy: `inert_nonuniqueS` (outside (A.22), nonzero bounded adapted solutions of the
  linear model), `inert_nonexistS_of_unit` (`|φ_π + ρ| = 1`: non-existence),
  `inert_coin_random_sunspot` (genuinely random linear sunspots on the coin tree), and
  `inertial_random_sunspot` (**genuinely random sunspot equilibria of the exact nonlinear model**
  on the coin tree, arbitrarily close to the steady state, for `|φ_π + ρ| < 1`).

## The scalar case `n = 1`

* `solvesSV_embedF_iff`: the book form `E_t[F(x_t, x_{t+1}, e_t)] = 0` of `LocalIFTStochastic`
  (`Ops.SolvesS (Ops.liftII F)`) is the `n = 1` case of `SolvesSV`;
  `isUnit_linOpS_embedF_iff`: the operator (A.12) is invertible iff the scalar operator
  `Ops.TOpS a b` is (`|b| < |a|`); `linSolS_embedF`: the linear RE solutions agree;
  `scalar_local_determinacyS_recovered`: the statement of `Ops.local_determinacyII` follows from
  the `n`-dimensional theorem.
-/

namespace Woodford.PriceLevelDetermination.LocalIFTSystemsStochasticApps

open scoped Topology Matrix
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic SystemsBK.GeneralBKForward
open LocalIFTSystems (Arg d1 d2 d3 dE M1 M2 M3 mulVec_M)
open LocalIFTSystemsApps (Finert ruleD inF1 inF2 inF3 contDiffAt_Finert Finert_zero)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The inertial rule under uncertainty -/

/-- **Prop. 2.8 / (A.22) under uncertainty** (Woodford (2003), Prop. 2.8, p. 96, and App. A.3,
pp. 633–634): for every expectation system on a nonempty state space, the operator (A.12) of the
exact inertial system is invertible iff `φ_π ≠ 0` and `|φ_π + ρ| > 1`. -/
theorem isUnit_linOpS_inert_iff [Nonempty Ω] {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) :
    IsUnit (linOpS 𝔼 (Finert Ψ)) ↔ φ ≠ 0 ∧ 1 < |φ + ρ| := by
  rw [isUnit_linOpS_iff_linOp, LocalIFTSystemsApps.isUnit_linOp_inert_iff hΨ]

/-- Woodford (2003), Prop. 2.8, p. 96, (1.32) and (2.12) under uncertainty: the linear model
`î_t = E_t π_{t+1} + r̂_t`, `î_t = φ_π π_t + ρ î_{t−1} + ν_t` has a unique bounded adapted solution
for every bounded adapted forcing and every `î_{−1}` iff `φ_π ≠ 0` and `|φ_π + ρ| > 1`. -/
theorem inert_linDeterminateS_iff [Nonempty Ω] (φ ρ : ℝ) :
    LinDeterminateS 𝔼 (inF1 ρ) (inF2 φ) inF3 ↔ φ ≠ 0 ∧ 1 < |φ + ρ| := by
  rw [linDeterminateS_iff_roots]
  exact LocalIFTSystemsApps.rootCondition_inert_iff φ ρ

/-- **Stochastic local determinacy of the exact inertial-rule model** (Woodford (2003),
Prop. 2.8, p. 96, and App. A.3, pp. 633–635): for any expectation system on a nonempty state
space and a rule `C¹` near the steady state with slopes `φ_π ≠ 0`, `ρ`, `|φ_π + ρ| > 1`: for
every `î_{−1}` near the steady state and all small bounded disturbance processes there is a
unique bounded adapted equilibrium near the steady state, `C¹` in `(î_{−1}, r̂, ν)`, whose
derivative is the linear RE solution. -/
theorem inertial_local_determinacyS [Nonempty Ω] {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨc : ContDiffAt ℝ 1 Ψ 0) (hΨ0 : Ψ 0 = 0) (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) (hφ : φ ≠ 0)
    (ha : 1 < |φ + ρ|) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧
      ∃ X : ParS (Fin 2) (Fin 2 → ℝ) Ω → SProcV (Fin 2) Ω, X 0 = 0 ∧
      HasFDerivAt X (linSolS 𝔼 (Finert Ψ)) 0 ∧
      ∀ u : ParS (Fin 2) (Fin 2 → ℝ) Ω, ‖u‖ < δ → ‖X u‖ < ε / 2 ∧
        SolvesSV 𝔼 (Finert Ψ) u (X u) ∧ ContDiffAt ℝ 1 X u ∧
        ∀ x : SProcV (Fin 2) Ω, ‖x‖ < ε → SolvesSV 𝔼 (Finert Ψ) u x → x = X u :=
  local_determinacyS 𝔼 (contDiffAt_Finert hΨc) (Finert_zero hΨ0)
    ((isUnit_linOpS_inert_iff 𝔼 hΨ).mpr ⟨hφ, ha⟩) hη

/-- Woodford (2003), Prop. 2.8, p. 96, and App. A.3, p. 634, E18, under uncertainty: for a `C²`
rule under (A.22), every bounded adapted equilibrium near the steady state is within
`C ‖(î_{−1}, e)‖²` of the linear RE solution. -/
theorem inertial_second_orderS [Nonempty Ω] {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ}
    (hΨc : ContDiffAt ℝ 2 Ψ 0) (hΨ0 : Ψ 0 = 0) (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) (hφ : φ ≠ 0)
    (ha : 1 < |φ + ρ|) :
    ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ u : ParS (Fin 2) (Fin 2 → ℝ) Ω, ‖u‖ < δ →
      ∀ x : SProcV (Fin 2) Ω, ‖x‖ < ε → SolvesSV 𝔼 (Finert Ψ) u x →
        ‖x - linSolS 𝔼 (Finert Ψ) u‖ ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨ε, hε, -, δ, hδ, -, C, hC⟩ := second_order_locS 𝔼 (contDiffAt_Finert hΨc)
    (Finert_zero hΨ0) ((isUnit_linOpS_inert_iff 𝔼 hΨ).mpr ⟨hφ, ha⟩) one_pos
  exact ⟨ε, hε, δ, hδ, C, hC⟩

/-- **Prop. 2.8 under uncertainty, both directions** (Woodford (2003), Prop. 2.8, p. 96, and
App. A.3, pp. 633–634): on a nonempty state space, (A.22) holds iff the exact inertial model is
locally determinate with a solution map differentiable at the steady state. -/
theorem inertial_iffS [Nonempty Ω] {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨc : ContDiffAt ℝ 1 Ψ 0)
    (hΨ0 : Ψ 0 = 0) (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0) :
    (φ ≠ 0 ∧ 1 < |φ + ρ|) ↔ ∃ ε > 0, ∃ δ > 0,
      ∃ X : ParS (Fin 2) (Fin 2 → ℝ) Ω → SProcV (Fin 2) Ω, X 0 = 0 ∧ DifferentiableAt ℝ X 0 ∧
        ∀ u : ParS (Fin 2) (Fin 2 → ℝ) Ω, ‖u‖ < δ → SolvesSV 𝔼 (Finert Ψ) u (X u) ∧
          ∀ x : SProcV (Fin 2) Ω, ‖x‖ < ε → SolvesSV 𝔼 (Finert Ψ) u x → x = X u := by
  rw [← isUnit_linOpS_inert_iff 𝔼 hΨ]
  refine isUnit_linOpS_iff_local_determinacyS 𝔼 (contDiffAt_Finert hΨc) (Finert_zero hΨ0) ?_
  intro y
  exact ⟨-y, by rw [LocalIFTSystemsApps.dE_Finert hΨ, neg_neg]⟩

/-- Woodford (2003), Prop. 2.8, p. 96, under uncertainty (**indeterminacy**): outside (A.22) the
linear model has nonzero bounded adapted solutions with no fundamental shocks and `î_{−1} = 0`,
for every expectation system on a nonempty state space. -/
theorem inert_nonuniqueS [Nonempty Ω] {φ ρ : ℝ} (h : ¬ (φ ≠ 0 ∧ 1 < |φ + ρ|)) :
    NonuniqueS 𝔼 (inF1 ρ) (inF2 φ) inF3 := by
  rw [nonuniqueS_iff, ← homInjective_iff_injective, LocalIFTSystemsApps.homInjective_inert_iff]
  exact h

/-- Woodford (2003), Prop. 2.8, p. 96, under uncertainty: when `|φ_π + ρ| = 1` the root
`φ_π + ρ` of (A.9) lies on the unit circle and some bounded deterministic forcing admits no
bounded solution at all. -/
theorem inert_nonexistS_of_unit [Nonempty Ω] {φ ρ : ℝ} (h1 : |φ + ρ| = 1) :
    NonexistS 𝔼 (inF1 ρ) (inF2 φ) inF3 := by
  refine stoch_nonexist_of_unit_root 𝔼 (μ := ((φ + ρ : ℝ) : ℂ)) ?_ ?_
  · rw [LocalIFTSystemsApps.roots_inert]
    exact Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _))
  · rw [Complex.norm_real, Real.norm_eq_abs, h1]

/-- **Random linear sunspots for the inertial rule** (Woodford (2003), Prop. 2.8, p. 96, under
uncertainty): outside (A.22), on the core two-coin tree, the linear model with no fundamental
shocks and `î_{−1} = 0` has bounded adapted solutions of every scale whose date-1 value differs
across the first coin flip. -/
theorem inert_coin_random_sunspot {φ ρ : ℝ} (h : ¬ (φ ≠ 0 ∧ 1 < |φ + ρ|)) {c : ℝ}
    (hc : c ≠ 0) :
    ∃ x : ℕ → Fin 2 → Bool × Bool → ℝ, BoundedV x ∧
      AdaptedV ExpectationsFiniteTree.coinSystem x ∧
      SolvesLinS ExpectationsFiniteTree.coinSystem (inF1 ρ) (inF2 φ) inF3 0 0 x ∧ x 0 = 0 ∧
      (fun i => x 1 i (true, true)) ≠ fun i => x 1 i (false, true) :=
  coin_random_sunspot (by rw [LocalIFTSystemsApps.homInjective_inert_iff]; exact h) hc

/-! ### Random sunspot equilibria of the exact inertial model -/

/-- Woodford (2003), Prop. 2.8, p. 96 (sunspot construction): the interest-rate path after a
date-1 inflation surprise `s`, `i_1 = Ψ(s, 0)`, `i_{t+1} = Ψ(i_t, i_t)` (from date 1 on,
`π_{t+1} = i_t`). -/
noncomputable def inertIter (Ψ : ℝ × ℝ → ℝ) (s : ℝ) : ℕ → ℝ
  | 0 => Ψ (s, 0)
  | t + 1 => Ψ (inertIter Ψ s t, inertIter Ψ s t)

/-- Woodford (2003), Prop. 2.8, p. 96 (sunspot construction): the interest rate,
`î_0 = 0`, `î_{t+1} = inertIter t`. -/
noncomputable def inertI (Ψ : ℝ × ℝ → ℝ) (s : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => inertIter Ψ s t

/-- Woodford (2003), Prop. 2.8, p. 96 (sunspot construction): inflation, `π_0 = 0`, `π_1 = s`
(the sunspot innovation), `π_{t+2} = î_{t+1}`. -/
noncomputable def inertPi (Ψ : ℝ × ℝ → ℝ) (s : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => s
  | t + 2 => inertIter Ψ s t

/-- Woodford (2003), Prop. 2.8, p. 96 (sunspot construction): the sunspot path in state `ω`
of the two-coin tree, driven by the first flip (`π_1 = ±a`). -/
noncomputable def inertSun (Ψ : ℝ × ℝ → ℝ) (a : ℝ) (t : ℕ) (ω : Bool × Bool) : Fin 2 → ℝ :=
  ![inertPi Ψ (if ω.1 then a else -a) t, inertI Ψ (if ω.1 then a else -a) t]

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): if `|Ψ(i, i)| ≤ |i|` on `[−r, r]` and
`|Ψ(s, 0)| ≤ m ≤ r`, the interest-rate path stays in `[−m, m]`. -/
theorem abs_inertIter_le {Ψ : ℝ × ℝ → ℝ} {r m s : ℝ} (hmr : m ≤ r)
    (hc : ∀ i : ℝ, |i| ≤ r → |Ψ (i, i)| ≤ |i|) (h1 : |Ψ (s, 0)| ≤ m) (t : ℕ) :
    |inertIter Ψ s t| ≤ m := by
  induction t with
  | zero => exact h1
  | succ t ih => exact (hc _ (ih.trans hmr)).trans ih

/-- **Genuinely random sunspot equilibria of the exact inertial model** (Woodford (2003),
Prop. 2.8, p. 96, indeterminacy half, under uncertainty; App. A.3, pp. 633–634): for a rule `Ψ`
differentiable at the steady state with slopes `φ_π`, `ρ`, `|φ_π + ρ| < 1` and `Ψ(0) = 0`, on the
core two-coin tree, for every `ε > 0` there is a bounded adapted solution of the exact stochastic
conditions `E_t[î_t − π_{t+1}] = 0`, `î_t = Ψ(π_t, î_{t−1})` with no fundamental shocks and
`î_{−1} = 0`, within `ε` of the steady state, starting at the steady state, whose date-1 value
differs across the first coin flip (inflation jumps to `±a` with the sunspot, and the nominal
rate then converges back since `|φ_π + ρ| < 1`). -/
theorem inertial_random_sunspot {Ψ : ℝ × ℝ → ℝ} {φ ρ : ℝ} (hΨ : HasFDerivAt Ψ (ruleD φ ρ) 0)
    (hΨ0 : Ψ 0 = 0) (hind : |φ + ρ| < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV (Fin 2) (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem (Finert Ψ) 0 x ∧ ‖x‖ ≤ ε ∧
      (∀ ω, x (0, ω) = 0) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  set k := |φ + ρ| with hk
  have h00 : Ψ ((0 : ℝ), (0 : ℝ)) = 0 := by rw [Prod.mk_zero_zero]; exact hΨ0
  -- the diagonal map `i ↦ Ψ(i, i)` has slope `φ_π + ρ`
  have hdiag : HasDerivAt (fun i : ℝ => Ψ (i, i)) (φ + ρ) 0 := by
    have hd : HasFDerivAt (fun i : ℝ => ((i, i) : ℝ × ℝ))
        ((ContinuousLinearMap.id ℝ ℝ).prod (ContinuousLinearMap.id ℝ ℝ)) 0 :=
      (hasFDerivAt_id 0).prodMk (hasFDerivAt_id 0)
    have hΨ' : HasFDerivAt Ψ (ruleD φ ρ) ((fun i : ℝ => ((i, i) : ℝ × ℝ)) 0) := hΨ
    have h := (HasFDerivAt.comp (f := fun i : ℝ => ((i, i) : ℝ × ℝ)) (0 : ℝ) hΨ' hd).hasDerivAt
    have e : ((ruleD φ ρ).comp ((ContinuousLinearMap.id ℝ ℝ).prod
        (ContinuousLinearMap.id ℝ ℝ))) 1 = φ + ρ := by
      simp [ruleD]
    rw [e] at h
    exact h
  -- a contraction near the steady state
  obtain ⟨r, hr, hrP⟩ : ∃ r > 0, ∀ i : ℝ, |i| ≤ r → |Ψ (i, i)| ≤ |i| := by
    have hc : 0 < (1 - k) / 2 := by linarith
    obtain ⟨r, hr, hP⟩ :=
      Metric.eventually_nhds_iff.mp ((hasDerivAt_iff_isLittleO.mp hdiag).def hc)
    refine ⟨r / 2, by positivity, fun i hi => ?_⟩
    have h := hP (show dist i 0 < r by rw [Real.dist_0_eq_abs]; linarith)
    simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, h00] at h
    have hk0 : 0 ≤ k := abs_nonneg _
    calc |Ψ (i, i)| = |(Ψ (i, i) - i * (φ + ρ)) + i * (φ + ρ)| := by ring_nf
      _ ≤ |Ψ (i, i) - i * (φ + ρ)| + |i * (φ + ρ)| := abs_add_le _ _
      _ ≤ (1 - k) / 2 * |i| + |i| * k := by rw [abs_mul, ← hk]; linarith
      _ ≤ |i| := by nlinarith [abs_nonneg i]
  -- a small sunspot innovation
  set m := min r ε with hm
  have hm0 : 0 < m := lt_min hr hε
  obtain ⟨d, hd, hdP⟩ := Metric.continuousAt_iff.mp hΨ.continuousAt m hm0
  set a := min (d / 2) ε with ha
  have ha0 : 0 < a := lt_min (by positivity) hε
  have haε : a ≤ ε := min_le_right _ _
  have hsmall : ∀ b : Bool, |Ψ ((if b then a else -a), 0)| ≤ m := by
    intro b
    have hdist : dist (((if b then a else -a), (0 : ℝ)) : ℝ × ℝ) 0 < d := by
      rw [dist_zero_right, Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _),
        Real.norm_eq_abs]
      have : |(if b then a else -a)| = a := by cases b <;> simp [abs_of_pos ha0]
      rw [this]
      linarith [min_le_left (d / 2) ε]
    have h := hdP hdist
    rw [hΨ0, dist_zero_right, Real.norm_eq_abs] at h
    simpa using h.le
  have hiter : ∀ (b : Bool) (t : ℕ), |inertIter Ψ (if b then a else -a) t| ≤ m := fun b t =>
    abs_inertIter_le (min_le_left r ε) hrP (hsmall b) t
  have hmε : m ≤ ε := min_le_right _ _
  have hbound : ∀ t ω, ‖inertSun Ψ a t ω‖ ≤ ε := by
    intro t ω
    refine (pi_norm_le_iff_of_nonneg hε.le).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    fin_cases i
    · change |inertPi Ψ (if ω.1 then a else -a) t| ≤ ε
      rcases t with _ | _ | t
      · change |(0 : ℝ)| ≤ ε
        rw [abs_zero]
        exact hε.le
      · change |(if ω.1 then a else -a)| ≤ ε
        cases ω.1 <;> simp [abs_of_pos ha0, haε]
      · exact (hiter ω.1 t).trans hmε
    · change |inertI Ψ (if ω.1 then a else -a) t| ≤ ε
      rcases t with _ | t
      · change |(0 : ℝ)| ≤ ε
        rw [abs_zero]
        exact hε.le
      · exact (hiter ω.1 t).trans hmε
  set x : SProcV (Fin 2) (Bool × Bool) :=
    LocalIFTStochastic.mkB (fun p => inertSun Ψ a p.1 p.2) ⟨ε, fun p => hbound p.1 p.2⟩ with hx
  have hxv : ∀ t ω, x (t, ω) = inertSun Ψ a t ω := fun _ _ => rfl
  refine ⟨x, ⟨?_, ?_⟩, LocalIFTStochastic.norm_le_of_forall hε.le fun p => hbound p.1 p.2,
    fun ω => ?_, ?_⟩
  · -- adaptedness
    intro t i
    rcases t with _ | t
    · have h0 : toP x 0 i = fun _ => 0 := by
        funext ω
        fin_cases i <;> rfl
      rw [h0]
      exact ExpectationsFiniteTree.coinSystem.const 0 0
    · have h1 : toP x (t + 1) i = fun ω => (fun b : Bool => inertSun Ψ a (t + 1) (b, b) i) ω.1 :=
        by funext ω; rfl
      rw [h1]
      exact LocalIFTStochasticModels.coin_known_fst t
        (fun b : Bool => inertSun Ψ a (t + 1) (b, b) i)
  · -- the two book conditions
    have hfis0 : ∀ t, ExpectationsFiniteTree.coinSystem.E t (fun ω => Finert Ψ
        (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x) (t, ω)) 0) = 0 := by
      intro t
      rcases t with _ | t
      · have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
            (0, ω)) 0) = fun ω => -(if ω.1 then a else -a) := by
          funext ω
          simp [Finert, ptS, hxv, inertSun, inertI, inertPi]
        rw [hf]
        funext ω
        rw [LocalIFTStochasticModels.coin_E0]
        simp
      · have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
            (t + 1, ω)) 0) = 0 := by
          funext ω
          simp [Finert, ptS, hxv, inertSun, inertI, inertPi]
        rw [hf]
        exact map_zero _
    have hfis1 : ∀ t, ExpectationsFiniteTree.coinSystem.E t (fun ω => Finert Ψ
        (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x) (t, ω)) 1) = 0 := by
      intro t
      have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
          (t, ω)) 1) = 0 := by
        funext ω
        rcases t with _ | _ | t
        · simp [Finert, ptS, hxv, inertSun, inertI, inertPi, h00]
        · simp [Finert, ptS, hxv, inertSun, inertI, inertPi, inertIter]
        · simp [Finert, ptS, hxv, inertSun, inertI, inertPi, inertIter]
      rw [hf]
      exact map_zero _
    intro t i
    fin_cases i
    · exact hfis0 t
    · exact hfis1 t
  · funext i
    fin_cases i <;> rfl
  · intro h
    have := congrFun h 0
    simp only [hxv, inertSun] at this
    change a = -a at this
    linarith

/-! ### The scalar case `n = 1` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Woodford (2003), App. A.3, p. 634 (tool): the scalar process of a one-dimensional vector
process. -/
noncomputable def scal1 : SProcV (Fin 1) Ω →L[ℝ] LocalIFTStochastic.Proc Ω :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFTStochastic.mkB (fun p => x p 0) ⟨‖x‖, fun p =>
        (norm_le_pi_norm (x p) 0).trans (LocalIFTStochastic.norm_apply_le x p)⟩
      map_add' := fun x y => lp.ext (funext fun p => rfl)
      map_smul' := fun c x => lp.ext (funext fun p => rfl) }
    1 (fun x => by
      rw [one_mul]
      exact LocalIFTStochastic.norm_le_of_forall (norm_nonneg _) fun p =>
        (norm_le_pi_norm (x p) 0).trans (LocalIFTStochastic.norm_apply_le x p))

/-- Woodford (2003), App. A.3, p. 634 (tool): a scalar process as a one-dimensional vector
process. -/
noncomputable def vec1 : LocalIFTStochastic.Proc Ω →L[ℝ] SProcV (Fin 1) Ω :=
  LinearMap.mkContinuous
    { toFun := fun x => LocalIFTStochastic.mkB (fun p _ => x p) ⟨‖x‖, fun p =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun _ =>
          LocalIFTStochastic.norm_apply_le x p⟩
      map_add' := fun x y => lp.ext (funext fun p => rfl)
      map_smul' := fun c x => lp.ext (funext fun p => rfl) }
    1 (fun x => by
      rw [one_mul]
      exact LocalIFTStochastic.norm_le_of_forall (norm_nonneg _) fun p =>
        (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun _ =>
          LocalIFTStochastic.norm_apply_le x p)

/-- Woodford (2003), App. A.3, p. 634 (tool): `scal1 ∘ vec1 = id`. -/
theorem scal1_vec1 (x : LocalIFTStochastic.Proc Ω) : scal1 (vec1 x) = x := lp.ext rfl

/-- Woodford (2003), App. A.3, p. 634 (tool): `vec1 ∘ scal1 = id`. -/
theorem vec1_scal1 (x : SProcV (Fin 1) Ω) : vec1 (scal1 x) = x := by
  ext p i
  fin_cases i
  rfl

/-- Woodford (2003), App. A.3, p. 634 (tool): `vec1` does not increase norms. -/
theorem norm_vec1_le (x : LocalIFTStochastic.Proc Ω) : ‖vec1 x‖ ≤ ‖x‖ :=
  LocalIFTStochastic.norm_le_of_forall (norm_nonneg _) fun p =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun _ => LocalIFTStochastic.norm_apply_le x p

/-- Woodford (2003), App. A.3, p. 634 (tool): `scal1` does not increase norms. -/
theorem norm_scal1_le (x : SProcV (Fin 1) Ω) : ‖scal1 x‖ ≤ ‖x‖ :=
  LocalIFTStochastic.norm_le_of_forall (norm_nonneg _) fun p =>
    (norm_le_pi_norm (x p) 0).trans (LocalIFTStochastic.norm_apply_le x p)

/-- Woodford (2003), eq. (A.11), p. 633: **the scalar book form is the case `n = 1`**: `x`
solves `E_t[F(x_t, x_{t+1}, e_t)] = 0` (`LocalIFTStochastic`) iff the one-dimensional process
`vec1 x` solves the `n`-dimensional stochastic conditions for `embedF F` (no predetermined
variable enters). -/
theorem solvesSV_embedF_iff (F : ℝ × ℝ × E → ℝ) (e : LocalIFTStochastic.SProc Ω E)
    (x : LocalIFTStochastic.Proc Ω) :
    SolvesSV 𝔼 (LocalIFTSystemsApps.embedF F) (0, e) (vec1 x) ↔
      LocalIFTStochastic.Ops.SolvesS 𝔼 (LocalIFTStochastic.Ops.liftII F) e x := by
  rw [LocalIFTStochastic.Ops.solvesS_liftII_iff]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨fun t => ha t 0, fun t => hb t 0⟩
  · rintro ⟨ha, hb⟩
    exact ⟨fun t _ => ha t, fun t _ => hb t⟩

omit [NormedSpace ℝ E] in
/-- Woodford (2003), App. A.3, p. 634 (tool): the derivative of the embedded condition in
blocks. -/
theorem fderiv_embedF_blocks {F : ℝ × ℝ × E → ℝ} [NormedSpace ℝ E]
    (hF : DifferentiableAt ℝ F 0) (v : Fin 1 → ℝ) (w : E) :
    d1 (LocalIFTSystemsApps.embedF F) v = 0 ∧
      d2 (LocalIFTSystemsApps.embedF F) v = (fun _ => LocalIFT.slopeA F * v 0) ∧
      d3 (LocalIFTSystemsApps.embedF F) v = (fun _ => LocalIFT.slopeB F * v 0) ∧
      dE (LocalIFTSystemsApps.embedF F) w = (fun _ => LocalIFT.slopeC F w) := by
  simp only [d1, d2, d3, dE, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, LocalIFTSystemsApps.fderiv_embedF_apply hF]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> simp

/-- **The operator criterion for `n = 1` is the scalar one** (Woodford (2003), eq. (A.12),
p. 634): on a nonempty state space, the operator (A.12) of `embedF F` is invertible iff the
scalar stochastic operator `a + b L` of `LocalIFTStochastic` is, i.e. iff `|b| < |a|`. -/
theorem isUnit_linOpS_embedF_iff [Nonempty Ω] {F : ℝ × ℝ × E → ℝ} [FiniteDimensional ℝ E]
    (hF : DifferentiableAt ℝ F 0) :
    IsUnit (linOpS 𝔼 (LocalIFTSystemsApps.embedF F)) ↔
      IsUnit (LocalIFTStochastic.Ops.TOpS 𝔼 (LocalIFT.slopeA F) (LocalIFT.slopeB F)) := by
  rw [isUnit_linOpS_iff_linOp, LocalIFTSystemsApps.isUnit_linOp_embedF_iff hF,
    LocalIFTStochastic.Ops.isUnit_TOpS_iff]

/-- Woodford (2003), eq. (A.13), p. 634: **the linear RE solutions agree for `n = 1`**: the
`n`-dimensional solution of the embedded condition with `x_{−1} = 0` is the scalar solution
`LocalIFTStochastic.Ops.linSolS a b c` (`−a⁻¹` times the core `forwardSeries`). -/
theorem linSolS_embedF [Nonempty Ω] {F : ℝ × ℝ × E → ℝ} [FiniteDimensional ℝ E]
    (hF : DifferentiableAt ℝ F 0)
    (hab : |LocalIFT.slopeB F| < |LocalIFT.slopeA F|) (e : LocalIFTStochastic.SProc Ω E) :
    scal1 (linSolS 𝔼 (LocalIFTSystemsApps.embedF F) (0, e)) =
      LocalIFTStochastic.Ops.linSolS 𝔼 (LocalIFT.slopeA F) (LocalIFT.slopeB F)
        (LocalIFT.slopeC F) e := by
  set a := LocalIFT.slopeA F
  set b := LocalIFT.slopeB F
  set c := LocalIFT.slopeC F
  have hL : IsUnit (linOpS 𝔼 (LocalIFTSystemsApps.embedF F)) :=
    (isUnit_linOpS_embedF_iff 𝔼 hF).mpr (LocalIFTStochastic.Ops.isUnit_TOpS 𝔼 hab)
  obtain ⟨ha, hs⟩ := linSolS_solves 𝔼 hL (0, e)
  set y := linSolS 𝔼 (LocalIFTSystemsApps.embedF F) (0, e) with hy
  have hT : LocalIFTStochastic.Ops.TOpS 𝔼 a b (scal1 y) +
      LocalIFTStochastic.Ops.cOpS 𝔼 c e = 0 := by
    ext ⟨t, ω⟩
    have h := congrFun (congrFun (hs t) 0) ω
    have hmv : ∀ (M : Matrix (Fin 1) (Fin 1) ℝ) (V : Fin 1 → Ω → ℝ),
        mv M V 0 ω = (M *ᵥ fun j => V j ω) 0 := fun M V => mv_apply M V 0 ω
    simp only [Pi.add_apply, hmv, (mulVec_M _ _).1, (mulVec_M _ _).2.1, (mulVec_M _ _).2.2,
      (fderiv_embedF_blocks hF _ (0 : E)).1, (fderiv_embedF_blocks hF _ (0 : E)).2.1,
      (fderiv_embedF_blocks hF _ (0 : E)).2.2.1, Pi.zero_apply, zero_add, Pi.neg_apply] at h
    have hdE : (fun ω => dE (LocalIFTSystemsApps.embedF F) ((0, e).2 (t, ω)) 0) =
        fun ω => c (e (t, ω)) := by
      funext ω
      rw [(fderiv_embedF_blocks hF (0 : Fin 1 → ℝ) _).2.2.2]
    rw [hdE] at h
    change a * scal1 y (t, ω) + b * 𝔼.E t (LocalIFTStochastic.slice (scal1 y) (t + 1)) ω +
      𝔼.E t (LocalIFTStochastic.slice (LocalIFTStochastic.Ops.ptc c e) t) ω = 0
    have hs1 : LocalIFTStochastic.slice (LocalIFTStochastic.Ops.ptc c e) t =
        fun ω => c (e (t, ω)) := rfl
    rw [hs1]
    change a * toP y t 0 ω + b * 𝔼.E t (toP y (t + 1) 0) ω + _ = 0
    linarith
  have hT2 := LocalIFTStochastic.Ops.linSolS_solves 𝔼 hab c e
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp
    (LocalIFTStochastic.Ops.isUnit_TOpS 𝔼 hab)).1
  apply hinj
  rw [← sub_eq_zero, ← map_sub]
  have := congrArg₂ (· - ·) hT hT2
  simp only [sub_self, add_sub_add_right_eq_sub] at this
  rw [map_sub]
  exact this

/-- **`n = 1` recovers `LocalIFTStochastic`** (Woodford (2003), App. A.3, pp. 633–635): the
statement of `LocalIFTStochastic.Ops.local_determinacyII` (the scalar book form
`E_t[F(x_t, x_{t+1}, e_t)] = 0` with `|∂F/∂x_{t+1}| < |∂F/∂x_t|`) follows from the
`n`-dimensional stochastic theorem `local_determinacyS` applied to `embedF F`. -/
theorem scalar_local_determinacyS_recovered [Nonempty Ω] [FiniteDimensional ℝ E]
    {F : ℝ × ℝ × E → ℝ} (hF : ContDiffAt ℝ 1 F 0) (h0 : F 0 = 0)
    (hab : |LocalIFT.slopeB F| < |LocalIFT.slopeA F|) :
    ∃ ε > 0, ∃ δ > 0, ∃ X : LocalIFTStochastic.SProc Ω E → LocalIFTStochastic.Proc Ω, X 0 = 0 ∧
      HasFDerivAt X (LocalIFTStochastic.Ops.linSolS 𝔼 (LocalIFT.slopeA F) (LocalIFT.slopeB F)
        (LocalIFT.slopeC F)) 0 ∧
      ∀ e : LocalIFTStochastic.SProc Ω E, ‖e‖ < δ →
        LocalIFTStochastic.Ops.SolvesS 𝔼 (LocalIFTStochastic.Ops.liftII F) e (X e) ∧
        ‖X e‖ < ε ∧ ContDiffAt ℝ 1 X e ∧
        ∀ x : LocalIFTStochastic.Proc Ω, ‖x‖ < ε →
          LocalIFTStochastic.Ops.SolvesS 𝔼 (LocalIFTStochastic.Ops.liftII F) e x → x = X e := by
  have hFd : DifferentiableAt ℝ F 0 := hF.differentiableAt (by norm_num)
  have hG : ContDiffAt ℝ 1 (LocalIFTSystemsApps.embedF F) 0 := by
    rw [LocalIFTSystemsApps.embedF_eq]
    have h0' : LocalIFTSystemsApps.scalarArg (0 : Arg (Fin 1) E) = 0 := map_zero _
    have hF' : ContDiffAt ℝ 1 F (LocalIFTSystemsApps.scalarArg (0 : Arg (Fin 1) E)) := by
      rw [h0']; exact hF
    exact LocalIFTSystemsApps.constEmb.contDiff.contDiffAt.comp 0
      (hF'.comp 0 (LocalIFTSystemsApps.scalarArg (E := E)).contDiff.contDiffAt)
  have hG0 : LocalIFTSystemsApps.embedF F 0 = 0 := by
    funext i
    exact h0
  have hL : IsUnit (linOpS 𝔼 (LocalIFTSystemsApps.embedF F)) :=
    (isUnit_linOpS_embedF_iff 𝔼 hFd).mpr (LocalIFTStochastic.Ops.isUnit_TOpS 𝔼 hab)
  obtain ⟨ε, hε, -, δ, hδ, -, XS, hX0, hXd, hX⟩ := local_determinacyS 𝔼 hG hG0 hL one_pos
  set P := ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (LocalIFTStochastic.SProc Ω E) with hP
  refine ⟨ε, hε, δ, hδ, fun e => scal1 (XS (P e)), ?_, ?_, fun e he => ?_⟩
  · simp only [map_zero, hX0]
  · have hd : HasFDerivAt XS (linSolS 𝔼 (LocalIFTSystemsApps.embedF F)) (P 0) := by
      rw [map_zero]; exact hXd
    have h := scal1.hasFDerivAt.comp (0 : LocalIFTStochastic.SProc Ω E) (hd.comp 0 P.hasFDerivAt)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    change scal1 (linSolS 𝔼 (LocalIFTSystemsApps.embedF F) (0, v)) = _
    exact linSolS_embedF 𝔼 hFd hab v
  · have hPe : ‖P e‖ < δ := by
      rw [hP, ContinuousLinearMap.inr_apply, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
      exact he
    obtain ⟨hn, hs, hc, hun⟩ := hX (P e) hPe
    have hXe : XS (P e) = vec1 (scal1 (XS (P e))) := (vec1_scal1 _).symm
    refine ⟨?_, lt_of_le_of_lt (norm_scal1_le _) (by linarith), ?_, fun x hx hsol => ?_⟩
    · rw [hXe] at hs
      exact (solvesSV_embedF_iff 𝔼 F e _).mp hs
    · exact scal1.contDiff.contDiffAt.comp e (hc.comp e P.contDiff.contDiffAt)
    · have hxs := (solvesSV_embedF_iff 𝔼 F e x).mpr hsol
      have h := hun (vec1 x) (lt_of_le_of_lt (norm_vec1_le x) hx) hxs
      change x = scal1 (XS (P e))
      rw [← h, scal1_vec1]

/-! ### E18 under uncertainty: `C¹` gives only `o(‖u‖)` -/

/-- **E18 under uncertainty** (Woodford (2003), App. A.3, p. 634): for every expectation system
on a nonempty state space, the `C¹` (not `C²`) condition `F0g` of
`LocalIFTSystemsApps.not_second_order_C1` gives an invertible operator (A.12), but no bound
`‖x − x̂‖ ≤ C ‖(x_{−1}, e)‖²` holds near the steady state: deterministic disturbances already
violate it. So `second_order_locS` needs `C²`; for `C¹` only `first_order_locS` holds. -/
theorem not_second_order_C1S [Nonempty Ω] :
    IsUnit (linOpS 𝔼 (LocalIFTSystemsApps.embedF LocalIFTSystemsApps.F0g)) ∧
      ¬ ∃ ε > 0, ∃ δ > 0, ∃ C : ℝ, ∀ u : ParS (Fin 1) ℝ Ω, ‖u‖ < δ → ∀ x : SProcV (Fin 1) Ω,
        ‖x‖ < ε → SolvesSV 𝔼 (LocalIFTSystemsApps.embedF LocalIFTSystemsApps.F0g) u x →
          ‖x - linSolS 𝔼 (LocalIFTSystemsApps.embedF LocalIFTSystemsApps.F0g) u‖ ≤
            C * ‖u‖ ^ 2 := by
  obtain ⟨-, -, hLP, hno⟩ := LocalIFTSystemsApps.not_second_order_C1
  have hL : IsUnit (linOpS 𝔼 (LocalIFTSystemsApps.embedF LocalIFTSystemsApps.F0g)) :=
    (isUnit_linOpS_iff_linOp 𝔼 _).mpr hLP
  refine ⟨hL, fun ⟨ε, hε, δ, hδ, C, hC⟩ => hno ⟨ε, hε, δ, hδ, |C|, fun u hu x hx hsol => ?_⟩⟩
  have hPu : ‖embPar (Ω := Ω) u‖ ≤ ‖u‖ := norm_embPar_le u
  have h := hC (embPar u) (lt_of_le_of_lt hPu hu) (embG (Fin 1 → ℝ) x)
    (by rw [norm_embG]; exact hx) ((solvesSV_embG_iff 𝔼 _ u x).mpr hsol)
  rw [linSolS_embPar 𝔼 hL, ← map_sub, norm_embG] at h
  calc _ ≤ C * ‖embPar (Ω := Ω) u‖ ^ 2 := h
    _ ≤ |C| * ‖embPar (Ω := Ω) u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ‖u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hPu 2) (abs_nonneg C)

end Woodford.PriceLevelDetermination.LocalIFTSystemsStochasticApps
