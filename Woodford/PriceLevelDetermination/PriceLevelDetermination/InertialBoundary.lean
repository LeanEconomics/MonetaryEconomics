/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.SunspotsNotOntoExamples
import PriceLevelDetermination.LocalIFTSystemsStochasticApps

/-!
# The inertial rule on the boundary of the determinacy region: the exact model

Woodford (2003), *Interest and Prices*, Prop. 2.8, p. 96, and App. A.3, pp. 632–634. The exact
model is the Fisher equation `E_t[î_t − π_{t+1} − r̂_t] = 0` and a nonlinear inertial rule
`E_t[î_t − Ψ(π_t, î_{t−1}) − ν_t] = 0` (`LocalIFTSystemsApps.Finert`), with slopes
`φ_π = ∂Ψ/∂π`, `ρ = ∂Ψ/∂î_{−1}` at the steady state. (A.22) — `φ_π ≠ 0` and `|φ_π + ρ| > 1` — is
exactly local determinacy with a differentiable solution map (`inertial_iffS`), and for
`|φ_π + ρ| < 1` the exact model has random sunspots (`inertial_random_sunspot`; this includes
`φ_π = 0, |ρ| < 1`). This module settles the **boundary** `|φ_π + ρ| = 1` (any `φ_π`) and
`φ_π = 0, |ρ| > 1`.

## Answer: the linearisation does not decide; the higher-order terms do

* **Sunspots** (on the coin tree, `î_{−1} = 0`, no shocks, at every scale):
  `random_sunspot_of_diag` whenever the diagonal map `i ↦ Ψ(i, i)` does not increase `|i|` near
  `0` (e.g. the linear rule on `|φ_π + ρ| = 1`, or the attracting cubic `ruleCubI`);
  `random_sunspot_of_flat` whenever `Ψ(π, 0) = 0` for small `π` (e.g. `Ψ = ρ î_{−1}`).
* **Uniqueness and existence** (under informational closure: perfect foresight, every finite
  event tree): `unique_affine` — for a rule `φ_π π + h(î_{−1})` with `φ_π ≠ 0` whose diagonal
  `i ↦ φ_π i + h(i)` is uniformly expanding, `|g(i) − g(i')| ≥ |i − i'| + κ|i − i'|³`, there is
  **at most one** bounded equilibrium for every initial rate and disturbance process (globally,
  not only near the steady state); `unique_cube` — the same for `ρ î_{−1} + σπ³` with `φ_π = 0`,
  `σ² = 1`, `σρ ≥ 1`. With no shocks the equilibrium exists for every `î_{−1}`
  (`solvesSV_jump`), so there are no sunspots of any kind.
* **Non-existence**: `no_eq_flat` — `Ψ = ρ î_{−1}` with `|ρ| > 1` has no bounded equilibrium at
  all for any `î_{−1} ≠ 0`; `no_eq_unit` — the linear rule with `|φ_π + ρ| = 1` has no bounded
  equilibrium for the deterministic disturbance `ν_t = δ(φ_π + ρ)ᵗ`, for every `δ ≠ 0` (so for
  arbitrarily small shocks).
* Summaries with rules having **identical slopes**: `boundary_unit_circle` (`|φ_π + ρ| = 1`) and
  `boundary_flat` (`φ_π = 0`, `|ρ| > 1`).

Throughout, `inertial_iffS` (`LocalIFTSystemsStochasticApps`) already shows that on the boundary
there is never a locally unique equilibrium map that exists for all small disturbances and is
differentiable at the steady state; the results here say what does and does not survive.
-/

namespace Woodford.PriceLevelDetermination.InertialBoundary

open scoped Topology Matrix
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic SunspotsBoundedBelow
open SunspotsNotOntoExamples (known_comp abs_att_le)
open LocalIFTSystems (Arg cbrt cbrt_pow)
open LocalIFTSystemsApps (Finert ruleD)
open LocalIFTSystemsStochasticApps (inertIter inertI inertPi inertSun abs_inertIter_le)

variable {Ω : Type*} {𝔼 : ExpectationSystem Ω}

/-! ### The two conditions in closed form -/

/-- Woodford (2003), eq. (1.32), p. 79, under uncertainty (tool): in an equilibrium the Fisher
equation reads `E_t π_{t+1} = î_t − E_t r̂_t`. -/
theorem eq0_of_solves {Ψ : ℝ × ℝ → ℝ} {u : ParS (Fin 2) (Fin 2 → ℝ) Ω} {x : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert Ψ) u x) (t : ℕ) :
    𝔼.E t (toP x (t + 1) 0) = toP x t 1 - 𝔼.E t (fun ω => u.2 (t, ω) 0) := by
  have h := hx.2 t 0
  have hf : (fun ω => Finert Ψ (ptS (u, x) (t, ω)) 0) =
      toP x t 1 - toP x (t + 1) 0 - fun ω => u.2 (t, ω) 0 := rfl
  rw [hf, map_sub, map_sub, hx.1 t 1] at h
  linear_combination -h

/-- Woodford (2003), eq. (2.12), p. 96, under uncertainty (tool): in an equilibrium the rule reads
`î_t = E_t Ψ(π_t, î_{t−1}) + E_t ν_t`. -/
theorem eq1_of_solves {Ψ : ℝ × ℝ → ℝ} {u : ParS (Fin 2) (Fin 2 → ℝ) Ω} {x : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert Ψ) u x) (t : ℕ) :
    toP x t 1 = 𝔼.E t (fun ω => Ψ (x (t, ω) 0, lagV u.1 (fun s => x (s, ω)) t 1)) +
      𝔼.E t (fun ω => u.2 (t, ω) 1) := by
  have h := hx.2 t 1
  have hf : (fun ω => Finert Ψ (ptS (u, x) (t, ω)) 1) = toP x t 1 -
      (fun ω => Ψ (x (t, ω) 0, lagV u.1 (fun s => x (s, ω)) t 1)) - fun ω => u.2 (t, ω) 1 := rfl
  rw [hf, map_sub, map_sub, hx.1 t 1] at h
  linear_combination h

/-- Woodford (2003), (2.12), p. 96 (tool): the lagged interest rate `î_{t−1}` is known at `t`. -/
theorem lag_known {Ψ : ℝ × ℝ → ℝ} {u : ParS (Fin 2) (Fin 2 → ℝ) Ω} {x : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert Ψ) u x) (t : ℕ) :
    𝔼.E t (fun ω => lagV u.1 (fun s => x (s, ω)) t 1) =
      fun ω => lagV u.1 (fun s => x (s, ω)) t 1 := by
  cases t with
  | zero => exact 𝔼.const 0 _
  | succ s =>
    change 𝔼.E (s + 1) (toP x s 1) = toP x s 1
    conv_lhs => rw [← hx.1 s 1]
    rw [𝔼.known (Nat.le_succ s), hx.1 s 1]

/-! ### Sunspots on the boundary -/

/-- **Random sunspots when the diagonal does not expand** (Woodford (2003), Prop. 2.8, p. 96;
App. A.3, pp. 633–634): for a rule `Ψ` continuous at the steady state with `Ψ(0) = 0` and
`|Ψ(i, i)| ≤ |i|` for small `i` — whatever its slopes, in particular on `|φ_π + ρ| = 1` — on the
core coin tree, for every `ε > 0`, the exact model with `î_{−1} = 0` and no fundamental shocks has
a bounded adapted equilibrium within `ε` of the steady state, starting at it, whose date-1 value
differs across the first flip (`π_1 = ±a`, then `î_{t+1} = Ψ(î_t, î_t)` stays small). -/
theorem random_sunspot_of_diag {Ψ : ℝ × ℝ → ℝ} (hc : ContinuousAt Ψ 0) (hΨ0 : Ψ 0 = 0)
    (hdiag : ∃ r > 0, ∀ i : ℝ, |i| ≤ r → |Ψ (i, i)| ≤ |i|) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV (Fin 2) (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem (Finert Ψ) 0 x ∧ ‖x‖ ≤ ε ∧
      (∀ ω, x (0, ω) = 0) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  obtain ⟨r, hr, hrP⟩ := hdiag
  have h00 : Ψ ((0 : ℝ), (0 : ℝ)) = 0 := by rw [Prod.mk_zero_zero]; exact hΨ0
  set m := min r ε with hm
  have hm0 : 0 < m := lt_min hr hε
  obtain ⟨d, hd, hdP⟩ := Metric.continuousAt_iff.mp hc m hm0
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
  · intro t i
    rcases t with _ | t
    · have h0 : toP x 0 i = fun _ => 0 := by
        funext ω
        fin_cases i <;> rfl
      rw [h0]
      exact ExpectationsFiniteTree.coinSystem.const 0 0
    · have h1 : toP x (t + 1) i =
          fun ω => (fun b : Bool => inertSun Ψ a (t + 1) (b, b) i) ω.1 := by
        funext ω
        rfl
      rw [h1]
      exact LocalIFTStochasticModels.coin_known_fst t
        (fun b : Bool => inertSun Ψ a (t + 1) (b, b) i)
  · have hfis0 : ∀ t, ExpectationsFiniteTree.coinSystem.E t (fun ω => Finert Ψ
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

/-- Woodford (2003), Prop. 2.8, p. 96 (sunspot construction for a rule flat in inflation): the
path `x_0 = 0`, `(π_1, î_1) = (s, 0)`, `x_t = 0` for `t ≥ 2`. -/
noncomputable def flatSun (a : ℝ) (t : ℕ) (ω : Bool × Bool) : Fin 2 → ℝ :=
  if t = 1 then ![if ω.1 then a else -a, 0] else 0

/-- **Random sunspots when the rule ignores inflation at the steady-state rate** (Woodford (2003),
Prop. 2.8, p. 96; App. A.3, p. 634): if `Ψ(0) = 0` and `Ψ(π, 0) = 0` for small `π` (so
`φ_π = 0`; e.g. `Ψ = ρ î_{−1}` with any `ρ`), then on the coin tree, for every `ε > 0`, the exact
model with `î_{−1} = 0` and no shocks has a bounded adapted equilibrium within `ε`, starting at the
steady state, with `π_1 = ±a` and the interest rate never moving. -/
theorem random_sunspot_of_flat {Ψ : ℝ × ℝ → ℝ} (hΨ0 : Ψ 0 = 0)
    (hflat : ∃ r > 0, ∀ π : ℝ, |π| ≤ r → Ψ (π, 0) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV (Fin 2) (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem (Finert Ψ) 0 x ∧ ‖x‖ ≤ ε ∧
      (∀ ω, x (0, ω) = 0) ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  obtain ⟨r, hr, hrP⟩ := hflat
  have h00 : Ψ ((0 : ℝ), (0 : ℝ)) = 0 := by rw [Prod.mk_zero_zero]; exact hΨ0
  set a := min r ε with ha
  have ha0 : 0 < a := lt_min hr hε
  have hab : ∀ b : Bool, |(if b then a else -a)| = a := fun b => by
    cases b <;> simp [abs_of_pos ha0]
  have hbound : ∀ t ω, ‖flatSun a t ω‖ ≤ ε := by
    intro t ω
    refine (pi_norm_le_iff_of_nonneg hε.le).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    unfold flatSun
    by_cases ht : t = 1
    · simp only [ht, ↓reduceIte]
      fin_cases i
      · change |(if ω.1 then a else -a)| ≤ ε
        rw [hab]
        exact min_le_right _ _
      · change |(0 : ℝ)| ≤ ε
        rw [abs_zero]
        exact hε.le
    · simp only [ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact hε.le
  set x : SProcV (Fin 2) (Bool × Bool) :=
    LocalIFTStochastic.mkB (fun p => flatSun a p.1 p.2) ⟨ε, fun p => hbound p.1 p.2⟩ with hx
  have hxv : ∀ t ω, x (t, ω) = flatSun a t ω := fun _ _ => rfl
  have hΨa : ∀ b : Bool, Ψ ((if b then a else -a), 0) = 0 := fun b =>
    hrP _ ((hab b).trans_le (min_le_left _ _))
  refine ⟨x, ⟨?_, fun t i => ?_⟩,
    LocalIFTStochastic.norm_le_of_forall hε.le fun p => hbound p.1 p.2, fun ω => ?_, ?_⟩
  · intro t i
    rcases t with _ | t
    · have h0 : toP x 0 i = fun _ => 0 := by
        funext ω
        simp [toP, hxv, flatSun]
      rw [h0]
      exact ExpectationsFiniteTree.coinSystem.const 0 0
    · have h1 : toP x (t + 1) i =
          fun ω => (fun b : Bool => flatSun a (t + 1) (b, b) i) ω.1 := by
        funext ω
        rfl
      rw [h1]
      exact LocalIFTStochasticModels.coin_known_fst t (fun b : Bool => flatSun a (t + 1) (b, b) i)
  · fin_cases i
    · rcases t with _ | t
      · have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
            (0, ω)) 0) = fun ω => -(if ω.1 then a else -a) := by
          funext ω
          simp [Finert, ptS, hxv, flatSun]
        change ExpectationsFiniteTree.coinSystem.E 0 (fun ω => Finert Ψ
          (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x) (0, ω)) 0) = 0
        rw [hf]
        funext ω
        rw [LocalIFTStochasticModels.coin_E0]
        simp
      · have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
            (t + 1, ω)) 0) = 0 := by
          funext ω
          have e1 : flatSun a (t + 1 + 1) ω = 0 := by simp [flatSun]
          have e2 : flatSun a (t + 1) ω 1 = 0 := by
            unfold flatSun
            split_ifs <;> simp
          simp [Finert, ptS, hxv, e1, e2]
        change ExpectationsFiniteTree.coinSystem.E (t + 1) (fun ω => Finert Ψ
          (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x) (t + 1, ω)) 0) = 0
        rw [hf]
        exact map_zero _
    · have hf : (fun ω => Finert Ψ (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x)
          (t, ω)) 1) = 0 := by
        funext ω
        rcases t with _ | _ | t
        · simp [Finert, ptS, hxv, flatSun, h00]
        · simp [Finert, ptS, hxv, flatSun, hΨa ω.1]
        · have e1 : flatSun a (t + 1 + 1) ω = 0 := by simp [flatSun]
          have e2 : flatSun a (t + 1) ω 1 = 0 := by
            unfold flatSun
            split_ifs <;> simp
          simp [Finert, ptS, hxv, e1, e2, h00]
      change ExpectationsFiniteTree.coinSystem.E t (fun ω => Finert Ψ
        (ptS ((0 : ParS (Fin 2) (Fin 2 → ℝ) (Bool × Bool)), x) (t, ω)) 1) = 0
      rw [hf]
      exact map_zero _
  · simp [hxv, flatSun]
  · intro h
    have := congrFun h 0
    simp only [hxv, flatSun, ↓reduceIte, Matrix.cons_val_zero] at this
    simp at this
    linarith

/-! ### Existence without shocks -/

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the path `x_0 = (c, 0)`, `x_t = 0` for `t ≥ 1`. -/
noncomputable def jumpSeq (c : ℝ) (t : ℕ) : Fin 2 → ℝ := if t = 0 then ![c, 0] else 0

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): `jumpSeq` as a bounded process. -/
noncomputable def jumpP (c : ℝ) : SProcV (Fin 2) Ω :=
  LocalIFTStochastic.mkB (fun p => jumpSeq c p.1) ⟨|c|, fun p => by
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg c)).mpr fun i => ?_
    rw [Real.norm_eq_abs, jumpSeq]
    split_ifs
    · fin_cases i <;> simp
    · simp⟩

/-- **Existence without shocks** (Woodford (2003), Prop. 2.8, p. 96): if `Ψ(0, 0) = 0` and
`Ψ(c, î_{−1}) = 0`, then for every expectation system the path that sets `π_0 = c` (so that
`î_0 = 0`) and stays at the steady state afterwards is a bounded adapted equilibrium with initial
rate `î_{−1}` and no disturbances. -/
theorem solvesSV_jump {Ψ : ℝ × ℝ → ℝ} (h00 : Ψ (0, 0) = 0) {xm : Fin 2 → ℝ} {c : ℝ}
    (hc : Ψ (c, xm 1) = 0) :
    SolvesSV 𝔼 (Finert Ψ) (xm, 0) (jumpP (Ω := Ω) c) := by
  have hv : ∀ t ω, (jumpP (Ω := Ω) c) (t, ω) = jumpSeq c t := fun _ _ => rfl
  refine ⟨fun t i => ?_, fun t i => ?_⟩
  · change 𝔼.E t (fun _ => jumpSeq c t i) = fun _ => jumpSeq c t i
    exact 𝔼.const t _
  · have hf : (fun ω => Finert Ψ (ptS (((xm, 0) : ParS (Fin 2) (Fin 2 → ℝ) Ω), jumpP c)
        (t, ω)) i) = fun _ => 0 := by
      funext ω
      fin_cases i
      · rcases t with _ | t
        · simp [Finert, ptS, hv, jumpSeq]
        · simp [Finert, ptS, hv, jumpSeq]
      · rcases t with _ | _ | t
        · simp [Finert, ptS, hv, jumpSeq, hc]
        · simp [Finert, ptS, hv, jumpSeq, h00]
        · simp [Finert, ptS, hv, jumpSeq, h00]
    rw [hf]
    exact 𝔼.const t 0

/-! ### Uniqueness: a rule affine in inflation with an expanding diagonal -/

/-- **Uniqueness on the boundary, `φ_π ≠ 0`** (Woodford (2003), Prop. 2.8, p. 96; App. A.3,
p. 634): under informational closure, for a rule `Ψ(π, i) = φ_π π + h(i)` with `φ_π ≠ 0` whose
diagonal `g(i) = φ_π i + h(i)` is uniformly expanding,
`|g(i) − g(i')| ≥ |i − i'| + κ|i − i'|³` (`κ > 0`), any two bounded adapted equilibria with the
same initial rate and disturbances coincide. (`E_t(î_{t+1} − î'_{t+1}) = g(î_t) − g(î'_t)`, so the
gap would grow beyond its supremum.) -/
theorem unique_affine (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {Ψ : ℝ × ℝ → ℝ}
    {φ κ : ℝ} {h : ℝ → ℝ} (hΨ : ∀ π i, Ψ (π, i) = φ * π + h i) (hφ : φ ≠ 0) (hκ : 0 < κ)
    (hexp : ∀ i i', |i - i'| + κ * |i - i'| ^ 3 ≤ |(φ * i + h i) - (φ * i' + h i')|)
    {u : ParS (Fin 2) (Fin 2 → ℝ) Ω} {x y : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert Ψ) u x) (hy : SolvesSV 𝔼 (Finert Ψ) u y) : x = y := by
  have hrule : ∀ z : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) u z → ∀ t,
      toP z t 1 = φ • toP z t 0 + (fun ω => h (lagV u.1 (fun s => z (s, ω)) t 1)) +
        𝔼.E t (fun ω => u.2 (t, ω) 1) := by
    intro z hz t
    rw [eq1_of_solves hz t]
    have e : (fun ω => Ψ (z (t, ω) 0, lagV u.1 (fun s => z (s, ω)) t 1)) =
        φ • toP z t 0 + fun ω => h (lagV u.1 (fun s => z (s, ω)) t 1) := by
      funext ω
      simp only [hΨ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    have hk := known_comp hcl (lag_known hz t) h
    beta_reduce at hk
    rw [e, map_add, map_smul, hz.1 t 0, hk]
  set D : ℕ → Ω → ℝ := fun t => toP x t 1 - toP y t 1 with hD
  have hED : ∀ t, 𝔼.E t (D (t + 1)) = fun ω =>
      (φ * toP x t 1 ω + h (toP x t 1 ω)) - (φ * toP y t 1 ω + h (toP y t 1 ω)) := by
    intro t
    have hdiff : D (t + 1) = φ • (toP x (t + 1) 0 - toP y (t + 1) 0) +
        ((fun ω => h (toP x t 1 ω)) - fun ω => h (toP y t 1 ω)) := by
      change toP x (t + 1) 1 - toP y (t + 1) 1 = _
      rw [hrule x hx (t + 1), hrule y hy (t + 1)]
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lagV_succ]
      change _ = _ + (h (x (t, ω) 1) - h (y (t, ω) 1))
      ring
    have hkx := known_comp hcl (hx.1 t 1) h
    have hky := known_comp hcl (hy.1 t 1) h
    rw [hdiff, map_add, map_smul, map_sub, map_sub, eq0_of_solves hx t, eq0_of_solves hy t, hkx,
      hky]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hD0 : ∀ p : ℕ × Ω, D p.1 p.2 = 0 := by
    refine eq_zero_of_push (fun p : ℕ × Ω => D p.1 p.2) ⟨‖x‖ + ‖y‖, fun p => ?_⟩
      (inv_pos.mpr hκ) fun B hB p => ?_
    · have h1 := abs_le.mp (abs_apply_le x p.1 p.2 1)
      have h2 := abs_le.mp (abs_apply_le y p.1 p.2 1)
      change |x p 1 - y p 1| ≤ _
      exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    · obtain ⟨t, ω⟩ := p
      have hb := 𝔼.abs_E_le (fun ω' => hB (t + 1, ω')) t ω
      change |𝔼.E t (D (t + 1)) ω| ≤ B at hb
      rw [hED t] at hb
      have he := hexp (toP x t 1 ω) (toP y t 1 ω)
      change |D t ω| ^ 3 ≤ κ⁻¹ * (B - |D t ω|)
      change |toP x t 1 ω - toP y t 1 ω| + κ * |toP x t 1 ω - toP y t 1 ω| ^ 3 ≤ _ at he
      change |toP x t 1 ω - toP y t 1 ω| ^ 3 ≤ κ⁻¹ * (B - |toP x t 1 ω - toP y t 1 ω|)
      rw [inv_mul_eq_div, le_div_iff₀ hκ]
      linarith
  have hI : ∀ t, toP x t 1 = toP y t 1 := fun t => funext fun ω => sub_eq_zero.mp (hD0 (t, ω))
  have hlag : ∀ t ω, lagV u.1 (fun s => x (s, ω)) t 1 = lagV u.1 (fun s => y (s, ω)) t 1 := by
    intro t ω
    cases t with
    | zero => rfl
    | succ s => exact congrFun (hI s) ω
  have hπ : ∀ t, toP x t 0 = toP y t 0 := by
    intro t
    have e1 := hrule x hx t
    have e2 := hrule y hy t
    rw [hI t] at e1
    have hl : (fun ω => h (lagV u.1 (fun s => x (s, ω)) t 1)) =
        fun ω => h (lagV u.1 (fun s => y (s, ω)) t 1) := funext fun ω => by rw [hlag t ω]
    rw [hl] at e1
    have hs : φ • toP x t 0 = φ • toP y t 0 :=
      add_right_cancel (add_right_cancel (e1.symm.trans e2))
    exact smul_right_injective _ hφ hs
  ext ⟨t, ω⟩ i
  fin_cases i
  · exact congrFun (hπ t) ω
  · exact congrFun (hI t) ω

/-! ### Uniqueness: `φ_π = 0` with a cubic response to inflation -/

/-- Woodford (2003), App. A.3, p. 634 (tool): `(a − b)³ ≤ 4(a³ − b³)` when `a ≥ b`. -/
theorem cube_gap {a b : ℝ} (h : b ≤ a) : (a - b) ^ 3 ≤ 4 * (a ^ 3 - b ^ 3) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg (a + b))]

/-- Woodford (2003), App. A.3, p. 634 (tool): `∛y ≥ 0` for `y ≥ 0`. -/
theorem cbrt_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ cbrt y := by
  simp only [cbrt, hy, ↓reduceIte]
  exact Real.rpow_nonneg hy _

/-- Woodford (2003), App. A.3, p. 634 (tool): `a³ − b³ ≤ m` implies `a − b ≤ ∛(4 max(m, 0))`. -/
theorem sub_le_cbrt {a b m : ℝ} (h : a ^ 3 - b ^ 3 ≤ m) : a - b ≤ cbrt (4 * max m 0) := by
  have hc0 : 0 ≤ cbrt (4 * max m 0) := cbrt_nonneg (by positivity)
  by_cases hab : b ≤ a
  · have h1 : (a - b) ^ 3 ≤ cbrt (4 * max m 0) ^ 3 := by
      rw [cbrt_pow]
      have := cube_gap hab
      have := le_max_left m 0
      linarith
    exact (pow_le_pow_iff_left₀ (sub_nonneg.mpr hab) hc0 (by norm_num)).mp h1
  · push Not at hab
    linarith

/-- Woodford (2003), App. A.3, p. 634 (tool): `0 ≤ d ≤ ∛(4 max(m, 0))` implies
`d³ ≤ 4 max(m, 0)`. -/
theorem pow_le_of_le_cbrt {d m : ℝ} (hd : 0 ≤ d) (h : d ≤ cbrt (4 * max m 0)) :
    d ^ 3 ≤ 4 * max m 0 := by
  have := pow_le_pow_left₀ hd h 3
  rwa [cbrt_pow] at this

/-- **Uniqueness on the boundary, `φ_π = 0`** (Woodford (2003), Prop. 2.8, p. 96; App. A.3,
p. 634): under informational closure, for the rule `Ψ(π, i) = ρ i + σ π³` with `σ² = 1` and
`σρ ≥ 1` (slopes `φ_π = 0`, `ρ`, `|ρ| ≥ 1`), any two bounded adapted equilibria with the same
initial rate and disturbances coincide. -/
theorem unique_cube (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {Ψ : ℝ × ℝ → ℝ} {ρ σ : ℝ}
    (hΨ : ∀ π i, Ψ (π, i) = ρ * i + σ * π ^ 3) (hσ : σ * σ = 1) (hτ : 1 ≤ σ * ρ)
    {u : ParS (Fin 2) (Fin 2 → ℝ) Ω} {x y : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 (Finert Ψ) u x) (hy : SolvesSV 𝔼 (Finert Ψ) u y) : x = y := by
  have hrule : ∀ z : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert Ψ) u z → ∀ t,
      toP z t 1 = ρ • (fun ω => lagV u.1 (fun s => z (s, ω)) t 1) +
        σ • (fun ω => toP z t 0 ω ^ 3) + 𝔼.E t (fun ω => u.2 (t, ω) 1) := by
    intro z hz t
    rw [eq1_of_solves hz t]
    have e : (fun ω => Ψ (z (t, ω) 0, lagV u.1 (fun s => z (s, ω)) t 1)) =
        ρ • (fun ω => lagV u.1 (fun s => z (s, ω)) t 1) + σ • (fun ω => toP z t 0 ω ^ 3) := by
      funext ω
      simp only [hΨ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    have hk := known_comp hcl (hz.1 t 0) (fun w => w ^ 3)
    beta_reduce at hk
    rw [e, map_add, map_smul, map_smul, lag_known hz t, hk]
  set D : ℕ → Ω → ℝ := fun t => toP x t 1 - toP y t 1 with hD
  set τ := σ * ρ with hτdef
  -- the cubic gap of inflation at `t + 1`
  have hgap : ∀ t ω, toP x (t + 1) 0 ω ^ 3 - toP y (t + 1) 0 ω ^ 3 =
      σ * D (t + 1) ω - τ * D t ω := by
    intro t ω
    have e1 := congrFun (hrule x hx (t + 1)) ω
    have e2 := congrFun (hrule y hy (t + 1)) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lagV_succ] at e1 e2
    change σ * σ = 1 at hσ
    change _ = σ * (toP x (t + 1) 1 ω - toP y (t + 1) 1 ω) -
      σ * ρ * (toP x t 1 ω - toP y t 1 ω)
    change toP x (t + 1) 1 ω = ρ * toP x t 1 ω + σ * toP x (t + 1) 0 ω ^ 3 + _ at e1
    change toP y (t + 1) 1 ω = ρ * toP y t 1 ω + σ * toP y (t + 1) 0 ω ^ 3 + _ at e2
    rw [e1, e2]
    linear_combination (toP y (t + 1) 0 ω ^ 3 - toP x (t + 1) 0 ω ^ 3) * hσ
  have hEπ : ∀ t, 𝔼.E t (toP x (t + 1) 0 - toP y (t + 1) 0) = D t := by
    intro t
    rw [map_sub, eq0_of_solves hx t, eq0_of_solves hy t]
    change _ = toP x t 1 - toP y t 1
    abel
  have hDk : ∀ t, 𝔼.E t (D t) = D t := fun t => by
    change 𝔼.E t (toP x t 1 - toP y t 1) = toP x t 1 - toP y t 1
    rw [map_sub, hx.1 t 1, hy.1 t 1]
  have hD0 : ∀ p : ℕ × Ω, D p.1 p.2 = 0 := by
    refine eq_zero_of_push (fun p : ℕ × Ω => D p.1 p.2) ⟨‖x‖ + ‖y‖, fun p => ?_⟩
      (by norm_num : (0 : ℝ) < 4) fun B hB p => ?_
    · have h1 := abs_le.mp (abs_apply_le x p.1 p.2 1)
      have h2 := abs_le.mp (abs_apply_le y p.1 p.2 1)
      change |x p 1 - y p 1| ≤ _
      exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    · obtain ⟨t, ω⟩ := p
      have hBn : ∀ ω', |σ * D (t + 1) ω'| ≤ B := fun ω' => by
        rw [abs_mul, show |σ| = 1 by nlinarith [abs_mul_abs_self σ, abs_nonneg σ], one_mul]
        exact hB (t + 1, ω')
      -- upper bound
      have hup : ∀ ω', (toP x (t + 1) 0 - toP y (t + 1) 0) ω' ≤
          cbrt (4 * max (B - τ * D t ω') 0) := fun ω' => by
        refine sub_le_cbrt ?_
        rw [hgap t ω']
        linarith [(abs_le.mp (hBn ω')).2]
      have hlo : ∀ ω', (toP y (t + 1) 0 - toP x (t + 1) 0) ω' ≤
          cbrt (4 * max (B + τ * D t ω') 0) := fun ω' => by
        refine sub_le_cbrt ?_
        have := hgap t ω'
        linarith [(abs_le.mp (hBn ω')).1]
      have hU := 𝔼.mono t (show (toP x (t + 1) 0 - toP y (t + 1) 0) ≤
        fun ω' => cbrt (4 * max (B - τ * D t ω') 0) from hup)
      have hL := 𝔼.mono t (show (toP y (t + 1) 0 - toP x (t + 1) 0) ≤
        fun ω' => cbrt (4 * max (B + τ * D t ω') 0) from hlo)
      have hkU := known_comp hcl (hDk t) (fun w => cbrt (4 * max (B - τ * w) 0))
      have hkL := known_comp hcl (hDk t) (fun w => cbrt (4 * max (B + τ * w) 0))
      beta_reduce at hkU hkL
      rw [hEπ, hkU] at hU
      rw [show toP y (t + 1) 0 - toP x (t + 1) 0 = -(toP x (t + 1) 0 - toP y (t + 1) 0) by abel,
        map_neg, hEπ, hkL] at hL
      have hU' := hU ω
      have hL' := hL ω
      simp only [Pi.neg_apply] at hL'
      change |D t ω| ^ 3 ≤ 4 * (B - |D t ω|)
      set d := D t ω with hd
      have hdB : |d| ≤ B := hB (t, ω)
      change |d| ^ 3 ≤ 4 * (B - |d|)
      rcases le_or_gt 0 d with h0 | h0
      · have h3 := pow_le_of_le_cbrt h0 hU'
        have hm : max (B - τ * d) 0 ≤ B - |d| := by
          rw [abs_of_nonneg h0]
          refine max_le (by nlinarith) (by linarith [le_abs_self d])
        rw [abs_of_nonneg h0] at hm ⊢
        linarith
      · have h3 := pow_le_of_le_cbrt (by linarith) hL'
        have hm : max (B + τ * d) 0 ≤ B - |d| := by
          rw [abs_of_neg h0]
          refine max_le (by nlinarith) (by linarith [neg_abs_le d, abs_of_neg h0])
        rw [abs_of_neg h0]
        rw [abs_of_neg h0] at hm
        nlinarith
  have hI : ∀ t, toP x t 1 = toP y t 1 := fun t => funext fun ω => sub_eq_zero.mp (hD0 (t, ω))
  have hπ : ∀ t, toP x t 0 = toP y t 0 := by
    intro t
    funext ω
    have e1 := congrFun (hrule x hx t) ω
    have e2 := congrFun (hrule y hy t) ω
    have hl : lagV u.1 (fun s => x (s, ω)) t 1 = lagV u.1 (fun s => y (s, ω)) t 1 := by
      cases t with
      | zero => rfl
      | succ s => exact congrFun (hI s) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    rw [congrFun (hI t) ω, hl] at e1
    have hcube : toP x t 0 ω ^ 3 = toP y t 0 ω ^ 3 := by
      have h3 : σ * toP x t 0 ω ^ 3 = σ * toP y t 0 ω ^ 3 := by linarith
      have := congrArg (fun w => σ * w) h3
      rw [← mul_assoc, ← mul_assoc, hσ, one_mul, one_mul] at this
      exact this
    exact (Odd.pow_injective (by decide : Odd 3)) hcube
  ext ⟨t, ω⟩ i
  fin_cases i
  · exact congrFun (hπ t) ω
  · exact congrFun (hI t) ω

/-! ### Non-existence on the boundary -/

/-- **Non-existence for `φ_π = 0`, `|ρ| > 1`** (Woodford (2003), Prop. 2.8, p. 96): for the rule
`Ψ(π, i) = ρ i` with `|ρ| > 1`, for every expectation system on a nonempty state space and every
initial rate `î_{−1} ≠ 0` there is no bounded adapted equilibrium without shocks
(`î_t = ρ^{t+1} î_{−1}`). -/
theorem no_eq_flat [Nonempty Ω] {ρ : ℝ} (hρ : 1 < |ρ|) {xm : Fin 2 → ℝ} (hxm : xm 1 ≠ 0) :
    ¬ ∃ x : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert fun p => ρ * p.2) (xm, 0) x := by
  rintro ⟨x, hx⟩
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  have hval : ∀ t, toP x t 1 = fun _ => ρ ^ (t + 1) * xm 1 := by
    intro t
    induction t with
    | zero =>
      rw [eq1_of_solves hx 0]
      change 𝔼.E 0 (fun _ => ρ * xm 1) + 𝔼.E 0 (fun _ => 0) = _
      rw [𝔼.const, 𝔼.const]
      funext ω
      simp
    | succ t ih =>
      rw [eq1_of_solves hx (t + 1)]
      change 𝔼.E (t + 1) (fun ω => ρ * toP x t 1 ω) + 𝔼.E (t + 1) (fun _ => 0) = _
      rw [ih, 𝔼.const, 𝔼.const]
      funext ω
      simp only [Pi.add_apply, add_zero]
      ring
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt (‖x‖ / |xm 1|) hρ
  have h1 := abs_apply_le x t ω₀ 1
  change |toP x t 1 ω₀| ≤ ‖x‖ at h1
  rw [hval t, abs_mul, abs_pow] at h1
  have hx0 : 0 < |xm 1| := abs_pos.mpr hxm
  rw [div_lt_iff₀ hx0] at ht
  have : |ρ| ^ t ≤ |ρ| ^ (t + 1) := pow_le_pow_right₀ hρ.le (Nat.le_succ t)
  nlinarith

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the deterministic policy shock `ν_t = δ σᵗ`
(`r̂ = 0`) as a bounded disturbance process, for `σ² = 1`. -/
noncomputable def resShock (δ σ : ℝ) (hσ : σ * σ = 1) :
    LocalIFTStochastic.BFun (ℕ × Ω) (Fin 2 → ℝ) :=
  LocalIFTStochastic.mkB (fun p => ![0, δ * σ ^ p.1]) ⟨|δ|, fun p => by
    have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg δ)).mpr fun i => ?_
    fin_cases i
    · simp
    · simp [hs]⟩

/-- Woodford (2003), Prop. 2.8, p. 96 (tool): the resonant shock has norm at most `|δ|`. -/
theorem norm_resShock_le (δ σ : ℝ) (hσ : σ * σ = 1) : ‖resShock (Ω := Ω) δ σ hσ‖ ≤ |δ| := by
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  refine LocalIFTStochastic.norm_le_of_forall (abs_nonneg δ) fun p => ?_
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg δ)).mpr fun i => ?_
  fin_cases i
  · simp [resShock]
  · simp [resShock, hs]

/-- **Non-existence for arbitrarily small shocks on `|φ_π + ρ| = 1`** (Woodford (2003),
Prop. 2.8, p. 96): for the linear rule `Ψ = φ_π π + ρ i` with `σ = φ_π + ρ`, `σ² = 1`, for every
expectation system on a nonempty state space, every initial rate and every `δ ≠ 0`, the
deterministic policy shock `ν_t = δ σᵗ` (`‖ν‖ = |δ|`) admits no bounded adapted equilibrium:
`E_0[σᵗ î_t] = î_0 + t δ`. -/
theorem no_eq_unit [Nonempty Ω] {φ ρ : ℝ} (hσ : (φ + ρ) * (φ + ρ) = 1) {δ : ℝ} (hδ : δ ≠ 0)
    (xm : Fin 2 → ℝ) :
    ¬ ∃ x : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert fun p => φ * p.1 + ρ * p.2)
      (xm, resShock δ (φ + ρ) hσ) x := by
  rintro ⟨x, hx⟩
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  set σ := φ + ρ with hσdef
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  have hr : ∀ t, 𝔼.E t (fun ω => (resShock (Ω := Ω) δ σ hσ) (t, ω) 0) = 0 := fun t => by
    change 𝔼.E t (fun _ => 0) = 0
    exact 𝔼.const t 0
  have hn : ∀ t, 𝔼.E t (fun ω => (resShock (Ω := Ω) δ σ hσ) (t, ω) 1) = fun _ => δ * σ ^ t :=
    fun t => by
      change 𝔼.E t (fun _ => δ * σ ^ t) = _
      exact 𝔼.const t _
  -- `E_t î_{t+1} = σ î_t + δ σ^{t+1}`
  have hstep : ∀ t, 𝔼.E t (toP x (t + 1) 1) = σ • toP x t 1 + fun _ => δ * σ ^ (t + 1) := by
    intro t
    have e1 := eq1_of_solves hx (t + 1)
    have e : (fun ω => (fun p : ℝ × ℝ => φ * p.1 + ρ * p.2)
        (x (t + 1, ω) 0, lagV xm (fun s => x (s, ω)) (t + 1) 1)) =
        φ • toP x (t + 1) 0 + ρ • toP x t 1 := by
      funext ω
      rfl
    rw [e, map_add, map_smul, map_smul, hx.1 (t + 1) 0, (hx.1 t 1 ▸
      (𝔼.known (Nat.le_succ t) (toP x t 1)) : 𝔼.E (t + 1) (toP x t 1) = toP x t 1), hn] at e1
    rw [e1, map_add, map_add, map_smul, map_smul, eq0_of_solves hx t, hr, sub_zero,
      hx.1 t 1, 𝔼.const]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hσdef]
    ring
  -- `E_0 [σ^t î_t] = î_0 + t δ`
  have hmean : ∀ t, 𝔼.E 0 (σ ^ t • toP x t 1) = toP x 0 1 + fun _ => (t : ℝ) * δ := by
    intro t
    induction t with
    | zero =>
      rw [pow_zero, one_smul, hx.1 0 1]
      funext ω
      simp
    | succ t ih =>
      rw [← 𝔼.tower (Nat.zero_le t), map_smul, hstep t, smul_add, smul_smul,
        show σ ^ (t + 1) * σ = σ ^ t by rw [pow_succ, mul_assoc, hσ, mul_one],
        map_add, ih, map_smul, 𝔼.const]
      have hσ2 : σ ^ (t + 1) * σ ^ (t + 1) = 1 := by
        rw [← mul_pow, hσ, one_pow]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [show σ ^ (t + 1) * (δ * σ ^ (t + 1)) = δ * (σ ^ (t + 1) * σ ^ (t + 1)) by ring, hσ2]
      push_cast
      ring
  obtain ⟨t, ht⟩ := exists_nat_gt (2 * ‖x‖ / |δ|)
  have hb : |𝔼.E 0 (σ ^ t • toP x t 1) ω₀| ≤ ‖x‖ := by
    refine 𝔼.abs_E_le (fun ω => ?_) 0 ω₀
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, hs, one_pow, one_mul]
    exact abs_apply_le x t ω 1
  rw [hmean t] at hb
  have h0 := abs_apply_le x 0 ω₀ 1
  change |toP x 0 1 ω₀| ≤ ‖x‖ at h0
  simp only [Pi.add_apply] at hb
  have hδ0 : 0 < |δ| := abs_pos.mpr hδ
  rw [div_lt_iff₀ hδ0] at ht
  have h3 : |(t : ℝ) * δ| ≤ 2 * ‖x‖ := by
    calc |(t : ℝ) * δ| = |(toP x 0 1 ω₀ + t * δ) - toP x 0 1 ω₀| := by ring_nf
      _ ≤ |toP x 0 1 ω₀ + t * δ| + |toP x 0 1 ω₀| := abs_sub _ _
      _ ≤ 2 * ‖x‖ := by linarith
  rw [abs_mul, Nat.abs_cast] at h3
  linarith

/-! ### The explicit rules and the summaries -/

/-- Woodford (2003), (2.12), p. 96: the linear inertial rule `φ_π π + ρ î_{−1}`. -/
def ruleLin (φ ρ : ℝ) (p : ℝ × ℝ) : ℝ := φ * p.1 + ρ * p.2

/-- Woodford (2003), (2.12), p. 96 (with a cubic term in the lagged rate):
`φ_π π + ρ î_{−1} + κ î_{−1}³`. -/
def ruleCubI (φ ρ κ : ℝ) (p : ℝ × ℝ) : ℝ := φ * p.1 + ρ * p.2 + κ * p.2 ^ 3

/-- Woodford (2003), (2.12), p. 96 (with a cubic response to inflation): `ρ î_{−1} + σ π³`
(`φ_π = 0`). -/
def ruleCubPi (ρ σ : ℝ) (p : ℝ × ℝ) : ℝ := ρ * p.2 + σ * p.1 ^ 3

/-- Woodford (2003), (2.12), p. 96: **all three rules have the slopes of the linear rule**:
`ruleLin φ ρ` and `ruleCubI φ ρ κ` have derivative `ruleD φ ρ`, `ruleCubPi ρ σ` has
`ruleD 0 ρ`; all are `C^∞` and vanish at the steady state. -/
theorem rules_slopes (φ ρ κ σ : ℝ) :
    HasFDerivAt (ruleLin φ ρ) (ruleD φ ρ) 0 ∧ HasFDerivAt (ruleCubI φ ρ κ) (ruleD φ ρ) 0 ∧
      HasFDerivAt (ruleCubPi ρ σ) (ruleD 0 ρ) 0 ∧
      (∀ k : ℕ, ContDiff ℝ k (ruleLin φ ρ) ∧ ContDiff ℝ k (ruleCubI φ ρ κ) ∧
        ContDiff ℝ k (ruleCubPi ρ σ)) ∧
      ruleLin φ ρ 0 = 0 ∧ ruleCubI φ ρ κ 0 = 0 ∧ ruleCubPi ρ σ 0 = 0 := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) 0 :=
    hasFDerivAt_snd
  have hlin : ruleLin φ ρ = ruleD φ ρ := by
    funext p
    simp [ruleLin, ruleD]
  refine ⟨?_, ?_, ?_, fun k => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hlin]
    exact (ruleD φ ρ).hasFDerivAt
  · have h := (((h1.const_mul φ).add (h2.const_mul ρ)).add ((h2.pow 3).const_mul κ))
    refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    simp [ruleD]
  · have h := (h2.const_mul ρ).add ((h1.pow 3).const_mul σ)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    simp [ruleD]
  · exact (contDiff_const.mul contDiff_fst).add (contDiff_const.mul contDiff_snd)
  · exact ((contDiff_const.mul contDiff_fst).add (contDiff_const.mul contDiff_snd)).add
      (contDiff_const.mul (contDiff_snd.pow 3))
  · exact (contDiff_const.mul contDiff_snd).add (contDiff_const.mul (contDiff_fst.pow 3))
  · simp [ruleLin]
  · simp [ruleCubI]
  · simp [ruleCubPi]

/-- Woodford (2003), App. A.3, p. 634 (tool): the expanding cubic diagonal
`g(i) = σ(i + i³)` (`σ² = 1`) satisfies `|g(i) − g(i')| ≥ |i − i'| + |i − i'|³/4`. -/
theorem expand_cubic {σ : ℝ} (hσ : σ * σ = 1) (i i' : ℝ) :
    |i - i'| + 1 / 4 * |i - i'| ^ 3 ≤ |σ * (i + i ^ 3) - σ * (i' + i' ^ 3)| := by
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  have e : σ * (i + i ^ 3) - σ * (i' + i' ^ 3) =
      σ * ((i - i') * (1 + i ^ 2 + i * i' + i' ^ 2)) := by
    ring
  have hq : 1 + (i - i') ^ 2 / 4 ≤ 1 + i ^ 2 + i * i' + i' ^ 2 := by nlinarith [sq_nonneg (i + i')]
  rw [e, abs_mul, hs, one_mul, abs_mul, abs_of_pos (by linarith [sq_nonneg (i - i')] :
    (0 : ℝ) < 1 + i ^ 2 + i * i' + i' ^ 2)]
  have h3 : |i - i'| ^ 3 = |i - i'| * (i - i') ^ 2 := by
    rw [pow_succ', ← sq_abs (i - i')]
  rw [h3]
  nlinarith [abs_nonneg (i - i')]

/-- **The boundary `|φ_π + ρ| = 1`: the linearisation does not decide** (Woodford (2003),
Prop. 2.8, p. 96; App. A.3, pp. 632–634). Let `σ = φ_π + ρ` with `σ² = 1`. Then:
(a) the linear rule has genuinely random sunspot equilibria at every scale (coin tree, `î_{−1} = 0`,
no shocks) **and** no bounded equilibrium at all for the shock `ν_t = δσᵗ`, any `δ ≠ 0`;
(b) the rule `φ_π π + ρ i − σ i³`, with the same slopes, also has random sunspots;
(c) if `φ_π ≠ 0`, the rule `φ_π π + ρ i + σ i³`, with the same slopes, has under informational
closure at most one bounded equilibrium for every initial rate and disturbance process, and
exactly one (no sunspots) for every initial rate without shocks; (d) if `φ_π = 0` (so `ρ = σ`),
the same holds for `ρ i + ρ π³`. -/
theorem boundary_unit_circle {φ ρ : ℝ} (hσ : (φ + ρ) * (φ + ρ) = 1) :
    -- (a)
    (∀ ε > 0, ∃ x : SProcV (Fin 2) (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem (Finert (ruleLin φ ρ)) 0 x ∧ ‖x‖ ≤ ε ∧
        x (1, (true, true)) ≠ x (1, (false, true))) ∧
    (∀ {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (δ : ℝ), δ ≠ 0 → ∀ xm : Fin 2 → ℝ,
      ¬ ∃ x : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert (ruleLin φ ρ))
        (xm, resShock δ (φ + ρ) hσ) x) ∧
    -- (b)
    (∀ ε > 0, ∃ x : SProcV (Fin 2) (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem (Finert (ruleCubI φ ρ (-(φ + ρ)))) 0 x ∧
        ‖x‖ ≤ ε ∧ x (1, (true, true)) ≠ x (1, (false, true))) ∧
    -- (c)
    (φ ≠ 0 → ∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω), LocalIFTStochastic.Ops.InfoClosed 𝔼 →
      ∀ xm : Fin 2 → ℝ, ∃! x : SProcV (Fin 2) Ω,
        SolvesSV 𝔼 (Finert (ruleCubI φ ρ (φ + ρ))) (xm, 0) x) ∧
    -- (d)
    (φ = 0 → ∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω), LocalIFTStochastic.Ops.InfoClosed 𝔼 →
      ∀ xm : Fin 2 → ℝ, ∃! x : SProcV (Fin 2) Ω,
        SolvesSV 𝔼 (Finert (ruleCubPi ρ ρ)) (xm, 0) x) := by
  obtain ⟨-, -, -, hcd, -, -, -⟩ := rules_slopes φ ρ 0 0
  have hs : |φ + ρ| = 1 := by nlinarith [abs_mul_abs_self (φ + ρ), abs_nonneg (φ + ρ)]
  refine ⟨fun ε hε => ?_, fun 𝔼 δ hδ xm => ?_, fun ε hε => ?_, fun hφ Ω 𝔼 hcl xm => ?_,
    fun hφ Ω 𝔼 hcl xm => ?_⟩
  · obtain ⟨x, h1, h2, -, h3⟩ := random_sunspot_of_diag (Ψ := ruleLin φ ρ)
      ((hcd 1).1.continuous.continuousAt) (by simp [ruleLin])
      ⟨1, one_pos, fun i _ => by
        rw [show ruleLin φ ρ (i, i) = (φ + ρ) * i by simp [ruleLin]; ring, abs_mul, hs,
          one_mul]⟩ hε
    exact ⟨x, h1, h2, h3⟩
  · exact no_eq_unit (𝔼 := 𝔼) hσ hδ xm
  · obtain ⟨x, h1, h2, -, h3⟩ := random_sunspot_of_diag (Ψ := ruleCubI φ ρ (-(φ + ρ)))
      ((rules_slopes φ ρ (-(φ + ρ)) 0).2.2.2.1 1).2.1.continuous.continuousAt
      (by simp [ruleCubI])
      ⟨1, one_pos, fun i hi => by
        rw [show ruleCubI φ ρ (-(φ + ρ)) (i, i) = (φ + ρ) * (i - i ^ 3) by
          simp [ruleCubI]; ring, abs_mul, hs, one_mul]
        exact abs_att_le hi⟩ hε
    exact ⟨x, h1, h2, h3⟩
  · have hΨ : ∀ π i, ruleCubI φ ρ (φ + ρ) (π, i) = φ * π + (ρ * i + (φ + ρ) * i ^ 3) :=
      fun π i => by simp [ruleCubI]; ring
    have hexp : ∀ i i', |i - i'| + 1 / 4 * |i - i'| ^ 3 ≤
        |(φ * i + (ρ * i + (φ + ρ) * i ^ 3)) - (φ * i' + (ρ * i' + (φ + ρ) * i' ^ 3))| := by
      intro i i'
      have := expand_cubic hσ i i'
      convert this using 2
      ring
    refine ⟨jumpP (-(ρ * xm 1 + (φ + ρ) * xm 1 ^ 3) / φ), solvesSV_jump (by simp [ruleCubI]) ?_,
      fun y hy => unique_affine hcl hΨ hφ (by norm_num) hexp hy
        (solvesSV_jump (by simp [ruleCubI]) ?_)⟩
    · rw [hΨ]
      field_simp
      ring
    · rw [hΨ]
      field_simp
      ring
  · have hρ : ρ * ρ = 1 := by rw [hφ, zero_add] at hσ; exact hσ
    have hΨ : ∀ π i, ruleCubPi ρ ρ (π, i) = ρ * i + ρ * π ^ 3 := fun π i => rfl
    have hroot : ruleCubPi ρ ρ (cbrt (-(xm 1)), xm 1) = 0 := by
      rw [hΨ, cbrt_pow]
      ring
    refine ⟨jumpP (cbrt (-(xm 1))), solvesSV_jump (by simp [ruleCubPi]) hroot,
      fun y hy => unique_cube hcl hΨ hρ hρ.ge hy (solvesSV_jump (by simp [ruleCubPi]) hroot)⟩

/-- **The boundary `φ_π = 0`, `|ρ| > 1`: the linearisation does not decide** (Woodford (2003),
Prop. 2.8, p. 96; App. A.3, pp. 632–634): (a) the linear rule `ρ î_{−1}` has random sunspot
equilibria at every scale when `î_{−1} = 0` (coin tree, no shocks) and no bounded equilibrium at
all for any `î_{−1} ≠ 0`; (b) the rule `ρ î_{−1} + σπ³` with `σ = sign ρ` — the same slopes — has,
under informational closure, exactly one bounded equilibrium for every initial rate without
shocks (no sunspots), and at most one for every disturbance process. -/
theorem boundary_flat {ρ : ℝ} (hρ : 1 < |ρ|) :
    (∀ ε > 0, ∃ x : SProcV (Fin 2) (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem (Finert (ruleLin 0 ρ)) 0 x ∧ ‖x‖ ≤ ε ∧
        x (1, (true, true)) ≠ x (1, (false, true))) ∧
    (∀ {Ω : Type*} [Nonempty Ω] (𝔼 : ExpectationSystem Ω) (xm : Fin 2 → ℝ), xm 1 ≠ 0 →
      ¬ ∃ x : SProcV (Fin 2) Ω, SolvesSV 𝔼 (Finert (ruleLin 0 ρ)) (xm, 0) x) ∧
    ∃ σ : ℝ, σ * σ = 1 ∧ 1 ≤ σ * ρ ∧
      (∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω), LocalIFTStochastic.Ops.InfoClosed 𝔼 →
        (∀ xm : Fin 2 → ℝ, ∃! x : SProcV (Fin 2) Ω,
          SolvesSV 𝔼 (Finert (ruleCubPi ρ σ)) (xm, 0) x) ∧
        ∀ (u : ParS (Fin 2) (Fin 2 → ℝ) Ω) (x y : SProcV (Fin 2) Ω),
          SolvesSV 𝔼 (Finert (ruleCubPi ρ σ)) u x → SolvesSV 𝔼 (Finert (ruleCubPi ρ σ)) u y →
            x = y) := by
  refine ⟨fun ε hε => ?_, fun 𝔼 xm hxm => ?_, ?_⟩
  · obtain ⟨x, h1, h2, -, h3⟩ := random_sunspot_of_flat (Ψ := ruleLin 0 ρ) (by simp [ruleLin])
      ⟨1, one_pos, fun π _ => by simp [ruleLin]⟩ hε
    exact ⟨x, h1, h2, h3⟩
  · have e : (Finert (ruleLin 0 ρ)) = Finert fun p => ρ * p.2 := by
      congr 1
      funext p
      simp [ruleLin]
    rw [e]
    exact no_eq_flat (𝔼 := 𝔼) hρ hxm
  · set σ : ℝ := if 0 < ρ then 1 else -1 with hσdef
    have hσ : σ * σ = 1 := by rw [hσdef]; split_ifs <;> norm_num
    have hτ : 1 ≤ σ * ρ := by
      rw [hσdef]
      split_ifs with h
      · rw [abs_of_pos h] at hρ
        linarith
      · push Not at h
        rcases h.lt_or_eq with h' | h'
        · rw [abs_of_neg h'] at hρ
          linarith
        · rw [h', abs_zero] at hρ
          linarith
    have hΨ : ∀ π i, ruleCubPi ρ σ (π, i) = ρ * i + σ * π ^ 3 := fun π i => rfl
    refine ⟨σ, hσ, hτ, fun 𝔼 hcl => ⟨fun xm => ?_, fun u x y hx hy => unique_cube hcl hΨ hσ hτ
      hx hy⟩⟩
    have hroot : ruleCubPi ρ σ (cbrt (-(σ * ρ * xm 1)), xm 1) = 0 := by
      rw [hΨ, cbrt_pow]
      linear_combination (-(ρ * xm 1)) * hσ
    exact ⟨jumpP (cbrt (-(σ * ρ * xm 1))), solvesSV_jump (by simp [ruleCubPi]) hroot,
      fun y hy => unique_cube hcl hΨ hσ hτ hy (solvesSV_jump (by simp [ruleCubPi]) hroot)⟩

end Woodford.PriceLevelDetermination.InertialBoundary
