/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.BlanchardKahn
import NeoWicksellianFramework.BasicModel

/-!
# Determinacy under exogenous and Taylor-type interest-rate rules

Woodford (2003), *Interest and Prices*, Chapter 4, §2.2, pp. 252–261, with Appendix C.2
(pp. 676–677) and C.4 (p. 681).

The basic neo-Wicksellian model is the intertemporal IS relation (1.12) and the New Keynesian
Phillips curve (1.13). Every policy rule studied here that responds only to current inflation,
expected inflation and the output gap turns the model into a two-dimensional system with no
predetermined variable, `z_t = B E_t z_{t+1} + b e_t`, `z = (π, x)`. All results hold for an
arbitrary `ExpectationSystem` (perfect foresight and genuine uncertainty).

## Main results

* Determinacy in the genuine sense — for every bounded adapted forcing there is exactly one
  bounded adapted solution — holds iff `B` satisfies the Schur–Cohn condition
  (`BlanchardKahn.fwdDeterminate_iff`, here lifted to the model: `modelDeterminate_iff`).
* The model equations are the canonical (1.12) `BasicModel.IS112` and (1.13)
  `BasicModel.NKPCurve`, with `x̄ = BasicModel.xbar`.
* (2.5)–(2.6): `model_iff_system25`, the characteristic polynomial and the root location
  `0 < μ₁ < 1 < μ₂` (`charPoly25_zero`, `charPoly25_one`, `mu_roots`, `mu_location`).
* **Proposition 4.2** (`prop_4_2_family`, `prop_4_2_complete`, `prop_4_2_continuum`,
  `prop_4_2`): under an
  exogenous interest-rate path the bounded adapted equilibria are exactly an explicit family
  indexed by an initial condition and a martingale-difference sunspot; in particular a continuum.
* **Proposition 4.3** (`prop_4_3`): the Taylor rule (1.14) is determinate iff (2.7)
  `φ_π + (1 − β) φ_x / (4κ) > 1`, by the book's route through `tr A`, `det A` of the (C.19)
  matrix (`taylorA_tr`, `taylorA_det`, `taylorB_eq_inv`) and Case I of Proposition C.1
  (`BlanchardKahn.schurStable_inv_iff_caseI`).
  Long-run interpretation (`longRun_rate_response`), the p. 255 Taylor numbers.
* Footnote 27 (survey E19): at equality in (2.7) the unit-eigenvalue eigenvector is
  `(1, (1 − β)/κ)` in the units of (1.14) (`fn27_eigenvector`), not `(1, (1 − β)/(4κ))`
  (`fn27_printed_not_eigenvector`); the constant-shift invariance (`fn27_shift`).
* Proposition 4.5, the Clarida et al. numbers and (2.14)–(2.15) are in `Determinacy2Forward`;
  Proposition 4.8 (learning) is in `Determinacy2Learning`.
-/

namespace Woodford.NeoWicksellianFramework.Determinacy2

open Filter Topology BlanchardKahn
open BasicModel (IS112 NKPCurve xbar)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

omit 𝔼 in
/-- Woodford (2003), eq. (2.6), p. 252 and (C.19), p. 677: the vector `z_t = (π_t − π̄, x_t − x̄)`
of deviations of inflation and the output gap from their steady-state values. -/
def devStack (infl x : ℕ → Ω → ℝ) (p0 x0 : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t => ![infl t - fun _ => p0, x t - fun _ => x0]

omit 𝔼 in
/-- Woodford (2003), eq. (C.19), p. 677: the forcing term `b (r̂ⁿ_t − ī_t + c)` of the forward
form of the model. -/
def fwdForcing (b : Fin 2 → ℝ) (rn ib : ℕ → Ω → ℝ) (c : ℝ) : ℕ → Fin 2 → Ω → ℝ :=
  fun t i => b i • (rn t - ib t + fun _ => c)

/-- Woodford (2003), Ch. 4, §2.2, p. 252 and fn. 24 (determinacy of equilibrium, in the genuine
sense): for every bounded adapted path of the natural rate `r̂ⁿ` and of the policy intercept
`ī`, the model has exactly one bounded adapted equilibrium `(π, x)`. -/
def ModelDeterminate
    (Eqm : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop) : Prop :=
  ∀ rn ib : ℕ → Ω → ℝ, BoundedProc rn → BoundedProc ib → 𝔼.Adapted rn → 𝔼.Adapted ib →
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), BoundedProc p.1 ∧ BoundedProc p.2 ∧
      𝔼.Adapted p.1 ∧ 𝔼.Adapted p.2 ∧ Eqm rn ib p.1 p.2

omit 𝔼 in
/-- Woodford (2003), eq. (2.6), p. 252: the deviation vector of bounded processes is bounded. -/
theorem devStack_bounded {infl x : ℕ → Ω → ℝ} (h1 : BoundedProc infl) (h2 : BoundedProc x)
    (p0 x0 : ℝ) : BoundedVec (devStack infl x p0 x0) := by
  obtain ⟨M₁, hM₁⟩ := h1
  obtain ⟨M₂, hM₂⟩ := h2
  refine ⟨M₁ + M₂ + |p0| + |x0|, fun t i ω => ?_⟩
  have hp := abs_nonneg p0
  have hx := abs_nonneg x0
  have h1' := (abs_nonneg _).trans (hM₁ t ω)
  have h2' := (abs_nonneg _).trans (hM₂ t ω)
  fin_cases i
  · simp only [devStack, Fin.zero_eta, Matrix.cons_val_zero, Pi.sub_apply]
    exact (abs_sub _ _).trans (by linarith [hM₁ t ω])
  · simp only [devStack, Fin.mk_one, Matrix.cons_val_one]
    exact (abs_sub _ _).trans (by linarith [hM₂ t ω])

/-- Woodford (2003), eq. (2.6), p. 252: the deviation vector of adapted processes is adapted. -/
theorem devStack_adapted {infl x : ℕ → Ω → ℝ} (h1 : 𝔼.Adapted infl) (h2 : 𝔼.Adapted x)
    (p0 x0 : ℝ) : 𝔼.AdaptedVec (devStack infl x p0 x0) := by
  intro t i
  fin_cases i
  · simp [devStack, map_sub, h1 t, 𝔼.const]
  · simp [devStack, map_sub, h2 t, 𝔼.const]

/-- Woodford (2003), eq. (C.19), p. 677: the forcing of bounded adapted disturbances is bounded
and adapted. -/
theorem fwdForcing_bounded_adapted (b : Fin 2 → ℝ) {rn ib : ℕ → Ω → ℝ} (hrn : BoundedProc rn)
    (hib : BoundedProc ib) (harn : 𝔼.Adapted rn) (haib : 𝔼.Adapted ib) (c : ℝ) :
    BoundedVec (fwdForcing b rn ib c) ∧ 𝔼.AdaptedVec (fwdForcing b rn ib c) := by
  obtain ⟨M₁, hM₁⟩ := hrn
  obtain ⟨M₂, hM₂⟩ := hib
  refine ⟨⟨(|b 0| + |b 1|) * (M₁ + M₂ + |c|), fun t i ω => ?_⟩, fun t i => ?_⟩
  · simp only [fwdForcing, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    have hb : |b i| ≤ |b 0| + |b 1| := by
      fin_cases i <;> simp
    have he : |rn t ω - ib t ω + c| ≤ M₁ + M₂ + |c| := by
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans ?_) le_rfl)
      exact add_le_add (hM₁ t ω) (hM₂ t ω)
    exact mul_le_mul hb he (abs_nonneg _) (by positivity)
  · simp only [fwdForcing, map_smul, map_add, map_sub, harn t, haib t, 𝔼.const]

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: recovering `(π, x)` from the deviation vector
`z = (π − p₀, x − x₀)`. -/
def ofDevStack (p0 x0 : ℝ) (z : ℕ → Fin 2 → Ω → ℝ) : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) :=
  (fun t => z t 0 + fun _ => p0, fun t => z t 1 + fun _ => x0)

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: `devStack` inverts `ofDevStack`. -/
theorem devStack_ofDevStack (p0 x0 : ℝ) (z : ℕ → Fin 2 → Ω → ℝ) :
    devStack (ofDevStack p0 x0 z).1 (ofDevStack p0 x0 z).2 p0 x0 = z := by
  funext t i
  fin_cases i <;> simp [devStack, ofDevStack]

omit 𝔼 in
/-- Woodford (2003), (C.19), p. 677: `devStack` is injective. -/
theorem devStack_inj {p0 x0 : ℝ} {infl x infl' x' : ℕ → Ω → ℝ}
    (h : devStack infl x p0 x0 = devStack infl' x' p0 x0) : infl = infl' ∧ x = x' := by
  constructor
  · funext t ω
    have := congrFun (congrFun (congrFun h t) 0) ω
    simpa [devStack] using this
  · funext t ω
    have := congrFun (congrFun (congrFun h t) 1) ω
    simpa [devStack] using this

/-- Woodford (2003), (C.19), p. 677: `ofDevStack` of a bounded adapted vector is bounded and
adapted. -/
theorem ofDevStack_bounded_adapted {p0 x0 : ℝ} {z : ℕ → Fin 2 → Ω → ℝ} (hz : BoundedVec z)
    (haz : 𝔼.AdaptedVec z) :
    𝔼.Adapted (ofDevStack p0 x0 z).1 ∧ 𝔼.Adapted (ofDevStack p0 x0 z).2 ∧
      BoundedProc (ofDevStack p0 x0 z).1 ∧ BoundedProc (ofDevStack p0 x0 z).2 := by
  obtain ⟨M, hM⟩ := hz
  refine ⟨fun t => ?_, fun t => ?_, ⟨M + |p0|, fun t ω => ?_⟩, ⟨M + |x0|, fun t ω => ?_⟩⟩
  · simp [ofDevStack, map_add, haz t 0, 𝔼.const]
  · simp [ofDevStack, map_add, haz t 1, 𝔼.const]
  · simpa [ofDevStack] using (abs_add_le _ _).trans (add_le_add (hM t 0 ω) le_rfl)
  · simpa [ofDevStack] using (abs_add_le _ _).trans (add_le_add (hM t 1 ω) le_rfl)

/-- Woodford (2003), Ch. 4, §2.2, pp. 252–254, p. 314 and App. C.1 (the determinacy criterion
at the level of the model, general forcing): if the equilibrium conditions are equivalent to a
forward system `z_t = K E_t z_{t+1} + W_t(r̂ⁿ, ī)` in the deviations `z = (π − p₀, x − x₀)`,
the forcing of bounded adapted disturbances is bounded and adapted, and some bounded adapted
disturbances give zero forcing, the model is determinate iff `K` satisfies the Schur–Cohn
condition. -/
theorem modelDeterminate_iff_of_reduction [Nonempty Ω] {K : Matrix (Fin 2) (Fin 2) ℝ}
    {p0 x0 : ℝ} {Eqm : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop}
    {W : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → ℕ → Fin 2 → Ω → ℝ}
    (hred : ∀ rn ib infl x, Eqm rn ib infl x ↔ 𝔼.Solves K (W rn ib) (devStack infl x p0 x0))
    (hW : ∀ rn ib, BoundedProc rn → BoundedProc ib → 𝔼.Adapted rn → 𝔼.Adapted ib →
      BoundedVec (W rn ib) ∧ 𝔼.AdaptedVec (W rn ib))
    (hW0 : ∃ rn ib, BoundedProc rn ∧ BoundedProc ib ∧ 𝔼.Adapted rn ∧ 𝔼.Adapted ib ∧
      W rn ib = 0) :
    ModelDeterminate 𝔼 Eqm ↔ SchurStable (tr2 K) (det2 K) := by
  constructor
  · intro hdet
    by_contra hA
    obtain ⟨rn, ib, h1, h2, h3, h4, hw0⟩ := hW0
    obtain ⟨y, hy, hay, hby, hne⟩ := 𝔼.system_not_unique hA (x := 0) (w := 0)
      (fun t i => by simp) (fun t i => by simp) ⟨0, fun t i ω => by simp⟩
    obtain ⟨p, _, hpu⟩ := hdet rn ib h1 h2 h3 h4
    have hsol : ∀ z, 𝔼.Solves K 0 z → BoundedVec z → 𝔼.AdaptedVec z →
        ofDevStack p0 x0 z = p := by
      intro z hz hbz haz
      obtain ⟨a1, a2, b1, b2⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := p0) (x0 := x0) hbz haz
      refine hpu _ ⟨b1, b2, a1, a2, ?_⟩
      rw [hred, devStack_ofDevStack, hw0]
      exact hz
    have e1 := hsol y hy hby hay
    have e2 := hsol 0 (fun t i => by simp) ⟨0, fun t i ω => by simp⟩ (fun t i => by simp)
    apply hne
    rw [← devStack_ofDevStack p0 x0 y, ← devStack_ofDevStack p0 x0 (0 : ℕ → Fin 2 → Ω → ℝ),
      e1, e2]
  · intro hK rn ib hrn hib harn haib
    obtain ⟨hwb, hwa⟩ := hW rn ib hrn hib harn haib
    obtain ⟨z, ⟨hz, haz, hbz⟩, hzu⟩ := fwd_existsUnique 𝔼 hK hwb hwa
    obtain ⟨a1, a2, b1, b2⟩ := ofDevStack_bounded_adapted 𝔼 (p0 := p0) (x0 := x0) hbz haz
    refine ⟨ofDevStack p0 x0 z, ⟨b1, b2, a1, a2, ?_⟩, fun q ⟨d1, d2, c1, c2, hq⟩ => ?_⟩
    · rw [hred, devStack_ofDevStack]
      exact hz
    · have := hzu (devStack q.1 q.2 p0 x0)
        ⟨(hred _ _ _ _).mp hq, devStack_adapted 𝔼 c1 c2 p0 x0, devStack_bounded d1 d2 p0 x0⟩
      rw [← this]
      obtain ⟨e1, e2⟩ := devStack_inj (devStack_ofDevStack p0 x0 (devStack q.1 q.2 p0 x0))
      exact Prod.ext e1.symm e2.symm

/-- Woodford (2003), Ch. 4, §2.2, pp. 252–254, and App. C.1 (the determinacy criterion at the
level of the model): if the equilibrium conditions are equivalent to a forward system
`z_t = K E_t z_{t+1} + b (r̂ⁿ_t − ī_t + c)` in the deviations `z = (π − p₀, x − x₀)`, the model
is determinate iff `K` satisfies the Schur–Cohn condition. -/
theorem modelDeterminate_iff [Nonempty Ω] (K : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ)
    (c p0 x0 : ℝ)
    (Eqm : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    (hE : ∀ rn ib infl x, Eqm rn ib infl x ↔
      𝔼.Solves K (fwdForcing b rn ib c) (devStack infl x p0 x0)) :
    ModelDeterminate 𝔼 Eqm ↔ SchurStable (tr2 K) (det2 K) := by
  refine modelDeterminate_iff_of_reduction 𝔼 (W := fun rn ib => fwdForcing b rn ib c) hE
    (fun rn ib hrn hib harn haib => fwdForcing_bounded_adapted 𝔼 b hrn hib harn haib c)
    ⟨fun _ _ => 0, fun _ _ => c, ⟨0, fun _ _ => by simp⟩, ⟨|c|, fun _ _ => le_rfl⟩,
      fun t => 𝔼.const t 0, fun t => 𝔼.const t c, ?_⟩
  funext t i ω
  simp [fwdForcing]

/-- Woodford (2003), eq. (C.19), p. 677: the forward system in the deviations, written out
date by date and state by state. -/
theorem solves_dev_iff (K : Matrix (Fin 2) (Fin 2) ℝ) (b : Fin 2 → ℝ) (c p0 x0 : ℝ)
    (infl x rn ib : ℕ → Ω → ℝ) :
    𝔼.Solves K (fwdForcing b rn ib c) (devStack infl x p0 x0) ↔ ∀ t ω,
      (infl t ω - p0 = K 0 0 * (𝔼.E t (infl (t + 1)) ω - p0)
        + K 0 1 * (𝔼.E t (x (t + 1)) ω - x0) + b 0 * (rn t ω - ib t ω + c)) ∧
      (x t ω - x0 = K 1 0 * (𝔼.E t (infl (t + 1)) ω - p0)
        + K 1 1 * (𝔼.E t (x (t + 1)) ω - x0) + b 1 * (rn t ω - ib t ω + c)) := by
  simp only [ExpectationSystem.Solves, Fin.forall_fin_two, devStack, fwdForcing, funext_iff,
    ← forall_and]
  simp [map_sub, 𝔼.const, mul_add]

/-! ### The basic model (1.12)–(1.13) -/

/-- Woodford (2003), eq. (1.12), p. 246, state by state. -/
theorem IS_iff (σ : ℝ) (infl x i rn : ℕ → Ω → ℝ) :
    IS112 𝔼 σ x i infl rn ↔ ∀ t ω,
      x t ω = 𝔼.E t (x (t + 1)) ω - σ * (i t ω - 𝔼.E t (infl (t + 1)) ω - rn t ω) := by
  simp only [IS112, funext_iff, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), eq. (1.13), p. 246, state by state. -/
theorem NKPC_iff (β κ : ℝ) (infl x : ℕ → Ω → ℝ) :
    NKPCurve 𝔼 β κ infl x ↔ ∀ t ω, infl t ω = κ * x t ω + β * 𝔼.E t (infl (t + 1)) ω := by
  simp only [NKPCurve, funext_iff, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), p. 246: `κ x̄ = (1 − β) π̄`, so `(π̄, x̄)` is a steady state of the NKPC. -/
theorem kappa_mul_xbar {β κ : ℝ} (hκ : κ ≠ 0) (πbar : ℝ) :
    κ * xbar β κ πbar = (1 - β) * πbar := by
  unfold xbar; field_simp

/-- Woodford (2003), p. 246: constant inflation `π̄` and output gap `x̄` satisfy the NKPC. -/
theorem nkpc_steady {β κ : ℝ} (hκ : κ ≠ 0) (πbar : ℝ) :
    NKPCurve 𝔼 β κ (fun _ _ => πbar) (fun _ _ => xbar β κ πbar) := by
  rw [NKPC_iff]
  intro t ω
  simp only [𝔼.const]
  linear_combination -(kappa_mul_xbar hκ πbar)

omit 𝔼 in
/-- Woodford (2003), eq. (1.14), p. 246: the Taylor rule
`î_t = ī_t + φ_π (π_t − π̄) + φ_x (x_t − x̄)/4`, as a process. -/
noncomputable def taylorRate (β κ φπ φx πbar : ℝ) (ib infl x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ib t + φπ • (infl t - fun _ => πbar) + (φx / 4) • (x t - fun _ => xbar β κ πbar)

/-- Woodford (2003), eqs. (1.12)–(1.14), p. 246: `(π, x)` is an equilibrium under the Taylor
rule (1.14) (the interest rate is then given by the rule). -/
def TaylorEqm (β σ κ φπ φx πbar : ℝ) (rn ib infl x : ℕ → Ω → ℝ) : Prop :=
  IS112 𝔼 σ x (taylorRate β κ φπ φx πbar ib infl x) infl rn ∧ NKPCurve 𝔼 β κ infl x

/-- Woodford (2003), eqs. (1.12)–(1.14), p. 246: a triple `(π, x, î)` satisfies (1.12), (1.13)
and the rule (1.14) iff `î` is given by the rule and `(π, x)` is a `TaylorEqm`; so uniqueness
of `(π, x)` is uniqueness of the triple. -/
theorem taylor_triple_iff (β σ κ φπ φx πbar : ℝ) (rn ib infl x i : ℕ → Ω → ℝ) :
    (IS112 𝔼 σ x i infl rn ∧ NKPCurve 𝔼 β κ infl x ∧ i = taylorRate β κ φπ φx πbar ib infl x) ↔
      (i = taylorRate β κ φπ φx πbar ib infl x ∧ TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib infl x) := by
  constructor
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨rfl, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩
    exact ⟨h1, h2, rfl⟩

/-- Woodford (2003), App. C.2, p. 677: `Δ = 1 + σ φ_x/4 + σ κ φ_π = β det A` for the (C.19)
matrix `A`. -/
noncomputable def taylorDelta (σ κ φπ φx : ℝ) : ℝ := 1 + σ * φx / 4 + σ * κ * φπ

/-- Woodford (2003), eq. (2.18), p. 263 (the matrix `B` of the temporary-equilibrium map,
`B = A⁻¹` for the (C.19) matrix `A`): the forward form `z_t = B E_t z_{t+1} + b e_t` of the
model under the Taylor rule (1.14). -/
noncomputable def taylorB (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx, κ / taylorDelta σ κ φπ φx;
    σ * (1 - β * φπ) / taylorDelta σ κ φπ φx, 1 / taylorDelta σ κ φπ φx]

/-- Woodford (2003), eq. (2.18), p. 263: the forcing coefficients `b` of the forward form under
(1.14). -/
noncomputable def taylorb (σ κ φπ φx : ℝ) : Fin 2 → ℝ :=
  ![κ * σ / taylorDelta σ κ φπ φx, σ / taylorDelta σ κ φπ φx]

/-- Woodford (2003), eq. (2.18), p. 263, state by state: under the Taylor rule, the IS relation
and the NKPC are equivalent to the forward form `z = B E z′ + b (r̂ⁿ − ī + π̄)` in deviations
from `(π̄, x̄)`. The values `P`, `X` are arbitrary (rational or subjective) expectations. -/
theorem taylor_pt {β σ κ φπ φx πbar xb : ℝ} (hxb : κ * xb = (1 - β) * πbar)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {p x P X rn ib r : ℝ}
    (hr : r = ib + φπ * (p - πbar) + φx / 4 * (x - xb)) :
    (x = X - σ * (r - P - rn) ∧ p = κ * x + β * P) ↔
      (p - πbar = taylorB β σ κ φπ φx 0 0 * (P - πbar) + taylorB β σ κ φπ φx 0 1 * (X - xb)
          + taylorb σ κ φπ φx 0 * (rn - ib + πbar) ∧
        x - xb = taylorB β σ κ φπ φx 1 0 * (P - πbar) + taylorB β σ κ φπ φx 1 1 * (X - xb)
          + taylorb σ κ φπ φx 1 * (rn - ib + πbar)) := by
  subst hr
  simp only [taylorB, taylorb, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  set Δ := taylorDelta σ κ φπ φx with hΔdef
  have hΔe : Δ = 1 + σ * φx / 4 + σ * κ * φπ := rfl
  constructor
  · rintro ⟨h1, h2⟩
    have k1 : Δ * (x - xb) = σ * (1 - β * φπ) * (P - πbar) + (X - xb)
        + σ * (rn - ib + πbar) := by
      rw [hΔe]; linear_combination h1 - σ * φπ * h2 - σ * φπ * hxb
    have k2 : Δ * (p - πbar) = (β + σ * κ + β * σ * φx / 4) * (P - πbar) + κ * (X - xb)
        + κ * σ * (rn - ib + πbar) := by
      rw [hΔe]
      linear_combination κ * h1 + (1 + σ * φx / 4) * h2 + (1 + σ * φx / 4) * hxb
    constructor
    · apply mul_left_cancel₀ hΔ
      rw [k2]
      field_simp
    · apply mul_left_cancel₀ hΔ
      rw [k1]
      field_simp
  · rintro ⟨h1, h2⟩
    have k2 : Δ * (p - πbar) = (β + σ * κ + β * σ * φx / 4) * (P - πbar) + κ * (X - xb)
        + κ * σ * (rn - ib + πbar) := by
      rw [h1]; field_simp
    have k1 : Δ * (x - xb) = σ * (1 - β * φπ) * (P - πbar) + (X - xb)
        + σ * (rn - ib + πbar) := by
      rw [h2]; field_simp
    have e : Δ * (p - κ * x - β * P) = 0 := by
      rw [hΔe] at k1 k2 ⊢
      linear_combination k2 - κ * k1 - (1 + σ * φx / 4 + σ * κ * φπ) * hxb
    have hn : p = κ * x + β * P := by
      have := (mul_eq_zero.mp e).resolve_left hΔ
      linarith
    refine ⟨?_, hn⟩
    rw [hΔe] at k1
    linear_combination k1 + σ * φπ * hn + σ * φπ * hxb

/-- Woodford (2003), eq. (2.18), p. 263 (and App. C.2): under the Taylor rule (1.14) the model
(1.12)–(1.13) is exactly the forward system `z_t = B E_t z_{t+1} + b (r̂ⁿ_t − ī_t + π̄)` in the
deviations `z = (π − π̄, x − x̄)`. -/
theorem taylorEqm_iff_solves {β σ κ φπ φx : ℝ} (hκ : κ ≠ 0) (hΔ : taylorDelta σ κ φπ φx ≠ 0)
    (πbar : ℝ) (rn ib infl x : ℕ → Ω → ℝ) :
    TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib infl x ↔
      𝔼.Solves (taylorB β σ κ φπ φx) (fwdForcing (taylorb σ κ φπ φx) rn ib πbar)
        (devStack infl x πbar (xbar β κ πbar)) := by
  rw [solves_dev_iff, TaylorEqm, IS_iff, NKPC_iff, ← forall_and]
  refine forall_congr' fun t => ?_
  rw [← forall_and]
  refine forall_congr' fun ω => ?_
  exact taylor_pt (kappa_mul_xbar hκ πbar) hΔ (by simp [taylorRate])

/-- Woodford (2003), App. C.2, p. 677: `Δ ≥ 1` under the sign restrictions. -/
theorem one_le_taylorDelta {σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) : 1 ≤ taylorDelta σ κ φπ φx := by
  unfold taylorDelta
  have h1 : 0 ≤ σ * φx := mul_nonneg hσ.le hφx
  have h2 : 0 ≤ σ * κ * φπ := mul_nonneg (mul_nonneg hσ.le hκ.le) hφπ
  linarith

/-- Woodford (2003), App. C.2, p. 677: `Δ > 0` under the sign restrictions. -/
theorem taylorDelta_pos {σ κ φπ φx : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (hφx : 0 ≤ φx) : 0 < taylorDelta σ κ φπ φx :=
  lt_of_lt_of_le one_pos (one_le_taylorDelta hσ hκ hφπ hφx)

/-! ### Proposition 4.3 -/

/-- Woodford (2003), eq. (C.19), p. 677: the matrix `A` of `E_t z_{t+1} = A z_t + a e_t` under
the Taylor rule (1.14). -/
noncomputable def taylorA (β σ κ φπ φx : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β⁻¹, -(β⁻¹ * κ); σ * (φπ - β⁻¹), 1 + σ * (φx / 4 + β⁻¹ * κ)]

/-- Woodford (2003), App. C.2, p. 677: `tr A = 1 + β⁻¹(1 + κσ) + σ φ_x/4`. -/
theorem taylorA_tr (β σ κ φπ φx : ℝ) :
    tr2 (taylorA β σ κ φπ φx) = 1 + β⁻¹ * (1 + κ * σ) + σ * φx / 4 := by
  simp only [taylorA, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), App. C.2, p. 677: `det A = β⁻¹[1 + σ(φ_x/4 + κ φ_π)]`. -/
theorem taylorA_det (β σ κ φπ φx : ℝ) :
    det2 (taylorA β σ κ φπ φx) = β⁻¹ * (1 + σ * (φx / 4 + κ * φπ)) := by
  simp only [taylorA, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), App. C.2, p. 677: `det A = Δ / β`. -/
theorem taylorA_det_eq (β σ κ φπ φx : ℝ) :
    det2 (taylorA β σ κ φπ φx) = taylorDelta σ κ φπ φx / β := by
  rw [taylorA_det, taylorDelta]
  ring

/-- Woodford (2003), eq. (2.18), p. 263 and (C.19), p. 677 (survey E18): the matrix `B` of the
forward form under (1.14) is the inverse of the (C.19) matrix `A`. -/
theorem taylorB_eq_inv {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) :
    taylorB β σ κ φπ φx = inv2 (taylorA β σ κ φπ φx) := by
  have hd := taylorA_det_eq β σ κ φπ φx
  unfold taylorDelta at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [taylorB, inv2, hd, taylorDelta, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one] <;>
    simp only [taylorA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    field_simp <;> ring

/-- Woodford (2003), eq. (2.7), p. 254: the left-hand side `φ_π + (1 − β) φ_x / (4κ)` of the
Taylor-principle condition — the long-run increase in the interest rate per unit permanent
increase in inflation. -/
noncomputable def taylorLHS (β κ φπ φx : ℝ) : ℝ := φπ + (1 - β) / (4 * κ) * φx

/-- Woodford (2003), eq. (2.7), p. 254: the left-hand side of (2.7) written as
`φ_π + (1 − β) φ_x / (4κ)`. -/
theorem taylorLHS_eq (β κ φπ φx : ℝ) : taylorLHS β κ φπ φx = φπ + (1 - β) * φx / (4 * κ) := by
  unfold taylorLHS
  ring

/-- Woodford (2003), App. C.2, p. 677: `det A − tr A + 1 = (σκ/β)(φ_π + (1 − β)φ_x/(4κ) − 1)`. -/
theorem taylorA_C2_eq {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) :
    det2 (taylorA β σ κ φπ φx) - tr2 (taylorA β σ κ φπ φx) + 1 =
      σ * κ / β * (taylorLHS β κ φπ φx - 1) := by
  rw [taylorA_det, taylorA_tr, taylorLHS]
  field_simp
  ring

/-- Woodford (2003), App. C.2, p. 677: under the sign restrictions (C.2) is equivalent to (2.7)
(= (C.18)). -/
theorem taylorA_C2_iff {β σ κ φπ φx : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    -1 < det2 (taylorA β σ κ φπ φx) - tr2 (taylorA β σ κ φπ φx) ↔
      1 < taylorLHS β κ φπ φx := by
  have e := taylorA_C2_eq (σ := σ) (φπ := φπ) (φx := φx) hβ.ne' hκ.ne'
  have hc : 0 < σ * κ / β := by positivity
  constructor
  · intro h
    have : 0 < σ * κ / β * (taylorLHS β κ φπ φx - 1) := by linarith
    have := (pos_iff_pos_of_mul_pos this).mp hc
    linarith
  · intro h
    have : 0 < σ * κ / β * (taylorLHS β κ φπ φx - 1) := mul_pos hc (by linarith)
    linarith

/-- Woodford (2003), App. C.2, p. 677: under the sign restrictions (C.1) `det A > 1` holds. -/
theorem taylorA_C1 {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) : 1 < det2 (taylorA β σ κ φπ φx) := by
  rw [taylorA_det_eq, lt_div_iff₀ hβ0]
  have := one_le_taylorDelta hσ hκ hφπ hφx
  linarith

/-- Woodford (2003), App. C.2, p. 677: under the sign restrictions (C.3) holds and (C.5) is
violated (`det A + tr A > 0`). -/
theorem taylorA_C3 {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) : 0 < det2 (taylorA β σ κ φπ φx) + tr2 (taylorA β σ κ φπ φx) := by
  have h1 := taylorA_C1 hβ0 hβ1 hσ hκ hφπ hφx
  rw [taylorA_tr]
  have : 0 < β⁻¹ * (1 + κ * σ) := by positivity
  have : 0 ≤ σ * φx / 4 := by positivity
  linarith

/-- Woodford (2003), App. C.2, pp. 676–677: both eigenvalues of `A` (C.19) are outside the unit
circle — `B = A⁻¹` is Schur–Cohn stable — iff (2.7). -/
theorem taylorB_schurStable_iff {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) :
    SchurStable (tr2 (taylorB β σ κ φπ φx)) (det2 (taylorB β σ κ φπ φx)) ↔
      1 < taylorLHS β κ φπ φx := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  have h1 := taylorA_C1 hβ0 hβ1 hσ hκ hφπ hφx
  rw [taylorB_eq_inv hβ0.ne', schurStable_inv_iff_caseI (by linarith),
    ← taylorA_C2_iff hβ0 hσ hκ]
  constructor
  · exact fun h => h.2.1
  · intro h
    exact ⟨h1, h, by linarith [taylorA_C3 hβ0 hβ1 hσ hκ hφπ hφx]⟩

/-- Woodford (2003), App. C.2: `tr B = (1 + β + σκ + βσφ_x/4)/Δ` under (1.14). -/
theorem taylorB_tr (β σ κ φπ φx : ℝ) :
    tr2 (taylorB β σ κ φπ φx) = (1 + β + σ * κ + β * σ * φx / 4) / taylorDelta σ κ φπ φx := by
  simp only [taylorB, tr2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), App. C.2: `det B = β/Δ` under (1.14). -/
theorem taylorB_det {β σ κ φπ φx : ℝ} (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    det2 (taylorB β σ κ φπ φx) = β / taylorDelta σ κ φπ φx := by
  simp only [taylorB, det2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  field_simp
  unfold taylorDelta
  ring

/-- Woodford (2003), p. 266: `det(B − I) = 1 − tr B + det B = σκ(φ_π + (1 − β)φ_x/(4κ) − 1)/Δ`. -/
theorem taylorB_one_sub {β σ κ φπ φx : ℝ} (hκ : κ ≠ 0) (hΔ : taylorDelta σ κ φπ φx ≠ 0) :
    det2 (taylorB β σ κ φπ φx) - tr2 (taylorB β σ κ φπ φx) + 1 =
      σ * κ * (taylorLHS β κ φπ φx - 1) / taylorDelta σ κ φπ φx := by
  rw [taylorB_det hΔ, taylorB_tr, taylorLHS]
  field_simp
  unfold taylorDelta
  ring

/-- **Proposition 4.3** (Woodford (2003), p. 254, proof App. C.2, pp. 676–677): under the
Taylor rule (1.14) with `φ_π, φ_x ≥ 0`, equilibrium is determinate — for every bounded adapted
`r̂ⁿ` and `ī` there is exactly one bounded adapted equilibrium `(π, x)` — iff (2.7)
`φ_π + (1 − β) φ_x / (4κ) > 1`. Necessity and sufficiency are both exact: no boundary case is
excluded (at equality the equilibrium is indeterminate). -/
theorem prop_4_3 [Nonempty Ω] {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (hφπ : 0 ≤ φπ) (hφx : 0 ≤ φx) (πbar : ℝ) :
    ModelDeterminate 𝔼 (TaylorEqm 𝔼 β σ κ φπ φx πbar) ↔ 1 < taylorLHS β κ φπ φx := by
  have hΔ := one_le_taylorDelta hσ hκ hφπ hφx
  rw [modelDeterminate_iff 𝔼 (taylorB β σ κ φπ φx) (taylorb σ κ φπ φx) πbar πbar
    (xbar β κ πbar) _ (fun rn ib infl x =>
      taylorEqm_iff_solves 𝔼 hκ.ne' (by linarith) πbar rn ib infl x)]
  exact taylorB_schurStable_iff hβ0 hβ1 hσ hκ hφπ hφx

/-- Woodford (2003), eq. (C.19), p. 677, state by state: under the Taylor rule, the IS relation
and the NKPC are equivalent to `E_t z_{t+1} = A z_t + a (r̂ⁿ_t − ī_t + π̄)` with the (C.19)
matrix `A` and `a = (0, −σ)`. -/
theorem taylor_C19_pt {β σ κ φπ φx πbar xb : ℝ} (hβ : β ≠ 0) (hxb : κ * xb = (1 - β) * πbar)
    {p x P X rn ib r : ℝ} (hr : r = ib + φπ * (p - πbar) + φx / 4 * (x - xb)) :
    (x = X - σ * (r - P - rn) ∧ p = κ * x + β * P) ↔
      (P - πbar = taylorA β σ κ φπ φx 0 0 * (p - πbar) + taylorA β σ κ φπ φx 0 1 * (x - xb)
          + 0 * (rn - ib + πbar) ∧
        X - xb = taylorA β σ κ φπ φx 1 0 * (p - πbar) + taylorA β σ κ φπ φx 1 1 * (x - xb)
          + -σ * (rn - ib + πbar)) := by
  subst hr
  simp only [taylorA, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  constructor
  · rintro ⟨h1, h2⟩
    have hb : β * (P - πbar) = (p - πbar) - κ * (x - xb) := by linear_combination -h2 - hxb
    have hP : P - πbar = β⁻¹ * ((p - πbar) - κ * (x - xb)) := by
      rw [← hb]; field_simp
    refine ⟨by rw [hP]; ring, ?_⟩
    linear_combination -h1 - σ * hP
  · rintro ⟨h1, h2⟩
    have hb : β * (P - πbar) = (p - πbar) - κ * (x - xb) := by rw [h1]; field_simp; ring
    have hP : P - πbar = β⁻¹ * ((p - πbar) - κ * (x - xb)) := by rw [h1]; ring
    refine ⟨?_, by linear_combination -hb - hxb⟩
    linear_combination -h2 - σ * hP

/-- Woodford (2003), eq. (C.19), p. 677: under the Taylor rule (1.14) the model (1.12)–(1.13)
is `E_t z_{t+1} = A z_t + a (r̂ⁿ_t − ī_t + π̄)` in the deviations `z = (π − π̄, x − x̄)`. -/
theorem taylorEqm_iff_C19 {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (πbar : ℝ)
    (rn ib infl x : ℕ → Ω → ℝ) :
    TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib infl x ↔ ∀ t ω,
      (𝔼.E t (infl (t + 1)) ω - πbar =
          taylorA β σ κ φπ φx 0 0 * (infl t ω - πbar)
          + taylorA β σ κ φπ φx 0 1 * (x t ω - xbar β κ πbar) + 0 * (rn t ω - ib t ω + πbar)) ∧
      (𝔼.E t (x (t + 1)) ω - xbar β κ πbar =
          taylorA β σ κ φπ φx 1 0 * (infl t ω - πbar)
          + taylorA β σ κ φπ φx 1 1 * (x t ω - xbar β κ πbar)
          + -σ * (rn t ω - ib t ω + πbar)) := by
  rw [TaylorEqm, IS_iff, NKPC_iff, ← forall_and]
  refine forall_congr' fun t => ?_
  rw [← forall_and]
  refine forall_congr' fun ω => ?_
  exact taylor_C19_pt hβ (kappa_mul_xbar hκ πbar) (by simp [taylorRate])

/-! ### Interpretation of (2.7) and the Taylor (1999) numbers -/

/-- Woodford (2003), p. 254: constant inflation `π` and output gap `x` satisfy the NKPC iff
`x = (1 − β) π / κ`: the long-run Phillips curve is not vertical (fn. 25). -/
theorem nkpc_const_iff [Nonempty Ω] {β κ : ℝ} (hκ : κ ≠ 0) (p y : ℝ) :
    NKPCurve 𝔼 β κ (fun _ _ => p) (fun _ _ => y) ↔ y = (1 - β) * p / κ :=
  BasicModel.const_nkpc_iff 𝔼 hκ p y

/-- Woodford (2003), p. 254 (interpretation of (2.7)): a permanent increase of inflation by `d`
above `π̄`, with the output gap raised by `(1 − β) d / κ` as the NKPC requires, raises the
interest rate prescribed by (1.14) by `(φ_π + (1 − β) φ_x/(4κ)) d`. A quarter-point quarterly
increase (one annualised percentage point, `d = 1/4`) raises the gap by `(1 − β)/(4κ)`. -/
theorem longRun_rate_response {β κ : ℝ} (hκ : κ ≠ 0) (φπ φx πbar d : ℝ) (ib : ℕ → Ω → ℝ)
    (t : ℕ) :
    taylorRate β κ φπ φx πbar ib (fun _ _ => πbar + d)
        (fun _ _ => xbar β κ πbar + (1 - β) * d / κ) t =
      (ib t + fun _ => taylorLHS β κ φπ φx * d) ∧
      (1 - β) * (1 / 4) / κ = (1 - β) / (4 * κ) := by
  refine ⟨?_, by ring⟩
  funext ω
  simp only [taylorRate, taylorLHS, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), p. 254 (the Taylor principle): for a permanent inflation increase `d > 0`
the long-run increase in the interest rate exceeds the increase in inflation iff (2.7). -/
theorem taylorPrinciple_iff {β κ φπ φx d : ℝ} (hd : 0 < d) :
    d < taylorLHS β κ φπ φx * d ↔ 1 < taylorLHS β κ φπ φx := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-- Woodford (2003), p. 254: a large enough inflation response guarantees determinacy:
`φ_π > 1` gives (2.7) for every `φ_x ≥ 0`. -/
theorem taylor_large_phiPi {β κ φπ φx : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hφx : 0 ≤ φx)
    (h : 1 < φπ) : 1 < taylorLHS β κ φπ φx := by
  unfold taylorLHS
  have : 0 ≤ (1 - β) / (4 * κ) * φx := mul_nonneg (div_nonneg (by linarith) (by linarith)) hφx
  linarith

/-- Woodford (2003), p. 254: a large enough output-gap response also guarantees determinacy,
whatever `φ_π ≥ 0`: `φ_x > 4κ/(1 − β)` gives (2.7). -/
theorem taylor_large_phiX {β κ φπ φx : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hφπ : 0 ≤ φπ)
    (h : 4 * κ / (1 - β) < φx) : 1 < taylorLHS β κ φπ φx := by
  unfold taylorLHS
  have h1 : 0 < 1 - β := by linarith
  rw [div_lt_iff₀ h1] at h
  have : 1 < (1 - β) / (4 * κ) * φx := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by linarith)]
    linarith
  linarith

/-- Woodford (2003), p. 255: with the Table 5.1 values `β = 0.99`, `κ = 0.024`, the weight on
`φ_x` in (2.7) is `(1 − β)/(4κ) = 0.104…`, "0.1" in the text. -/
theorem table51_weight :
    (1 - (0.99 : ℝ)) / (4 * 0.024) = 0.01 / 0.096 ∧
      (0.104 : ℝ) < (1 - 0.99) / (4 * 0.024) ∧ (1 - (0.99 : ℝ)) / (4 * 0.024) < 0.105 := by
  norm_num

/-- Woodford (2003), p. 255: Taylor's pre-Volcker (1960–1979) estimates `φ_π = 0.81`,
`φ_x = 0.25` give a long-run response `0.81 + 0.104 · 0.25 ≈ 0.84 < 1`, so (2.7) fails. -/
theorem taylor_preVolcker_LHS :
    taylorLHS 0.99 0.024 0.81 0.25 < 1 ∧ (0.83 : ℝ) < taylorLHS 0.99 0.024 0.81 0.25 ∧
      taylorLHS 0.99 0.024 0.81 0.25 < 0.84 := by
  unfold taylorLHS
  norm_num

/-- Woodford (2003), p. 255: under Taylor's pre-Volcker estimates and the Table 5.1 structural
parameters (`σ = 1/0.16`), equilibrium is indeterminate (Proposition 4.3). -/
theorem taylor_preVolcker_indeterminate [Nonempty Ω] (πbar : ℝ) :
    ¬ ModelDeterminate 𝔼 (TaylorEqm 𝔼 0.99 (1 / 0.16) 0.024 0.81 0.25 πbar) := by
  rw [prop_4_3 𝔼 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  exact not_lt.mpr taylor_preVolcker_LHS.1.le

/-- Woodford (2003), p. 255: under Taylor's post-Volcker (1987–1997) estimates `φ_π = 1.53`,
`φ_x = 0.77` (Table 1.1) equilibrium is determinate. -/
theorem taylor_postVolcker_determinate [Nonempty Ω] (πbar : ℝ) :
    ModelDeterminate 𝔼 (TaylorEqm 𝔼 0.99 (1 / 0.16) 0.024 1.53 0.77 πbar) := by
  rw [prop_4_3 𝔼 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)]
  unfold taylorLHS
  norm_num

/-! ### Footnote 27: the unit eigenvalue at the boundary of the Taylor principle -/

/-- Woodford (2003), fn. 27, p. 256: `det(A − I) = 1 − tr A + det A = (σκ/β)(LHS(2.7) − 1)`, so
the (C.19) matrix has the eigenvalue `1` iff (2.7) holds with equality. -/
theorem taylorA_eig_one_iff {β σ κ φπ φx : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    (1 : ℝ) ^ 2 - tr2 (taylorA β σ κ φπ φx) * 1 + det2 (taylorA β σ κ φπ φx) = 0 ↔
      taylorLHS β κ φπ φx = 1 := by
  have e := taylorA_C2_eq (σ := σ) (φπ := φπ) (φx := φx) hβ.ne' hκ.ne'
  have hc : σ * κ / β ≠ 0 := by positivity
  constructor
  · intro h
    have : σ * κ / β * (taylorLHS β κ φπ φx - 1) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hc
    linarith
  · intro h
    rw [h, sub_self, mul_zero] at e
    linarith

/-- Woodford (2003), fn. 27, p. 256, corrected (survey E19): when (2.7) holds with equality,
`v = (1, (1 − β)/κ)` — inflation and the interest rate up by one unit, the output gap by
`(1 − β)/κ` — is an eigenvector of the (C.19) matrix `A` (and so of `B = A⁻¹`) with eigenvalue
`1`. -/
theorem fn27_eigenvector {β σ κ φπ φx : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) (h : taylorLHS β κ φπ φx = 1) :
    (taylorA β σ κ φπ φx).mulVec ![1, (1 - β) / κ] = ![1, (1 - β) / κ] ∧
      (taylorB β σ κ φπ φx).mulVec ![1, (1 - β) / κ] = ![1, (1 - β) / κ] := by
  unfold taylorLHS at h
  have hA : (taylorA β σ κ φπ φx).mulVec ![1, (1 - β) / κ] = ![1, (1 - β) / κ] := by
    ext i
    fin_cases i <;>
      simp [taylorA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp
    · ring
    · field_simp at h
      linear_combination σ * β * h
  refine ⟨hA, ?_⟩
  have hd : det2 (taylorA β σ κ φπ φx) ≠ 0 := by
    rw [taylorA_det_eq]; exact div_ne_zero hΔ hβ
  rw [taylorB_eq_inv hβ]
  calc (inv2 (taylorA β σ κ φπ φx)).mulVec ![1, (1 - β) / κ]
      = (inv2 (taylorA β σ κ φπ φx)).mulVec ((taylorA β σ κ φπ φx).mulVec
          ![1, (1 - β) / κ]) := by rw [hA]
    _ = ![1, (1 - β) / κ] := by rw [Matrix.mulVec_mulVec, inv2_mul hd, Matrix.one_mulVec]

/-- Woodford (2003), fn. 27, p. 256, survey E19 (counterexample to the printed eigenvector): in
the units of (1.14) (quarterly `π`, `î`), the vector `(1, (1 − β)/(4κ))` printed in the footnote
is not mapped to itself by the (C.19) matrix for any `0 < β < 1` (its first component becomes
`(3 + β)/(4β) ≠ 1`); the printed entry is the gap response per annualised point of inflation. -/
theorem fn27_printed_not_eigenvector {β σ κ φπ φx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) :
    (taylorA β σ κ φπ φx).mulVec ![1, (1 - β) / (4 * κ)] ≠ ![1, (1 - β) / (4 * κ)] := by
  intro h
  have h0 := congrFun h 0
  simp [taylorA, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  field_simp at h0
  nlinarith

/-- Woodford (2003), fn. 27, p. 256: when (2.7) holds with equality, the IS relation, the NKPC
and the rule (1.14) are all unchanged when inflation (and the interest rate) are raised by `c`
and the output gap by `c (1 − β)/κ` at all dates: every equilibrium has a continuum of
neighbours, so equilibrium is indeterminate. -/
theorem fn27_shift {β σ κ φπ φx πbar : ℝ} (hκ : κ ≠ 0) (h : taylorLHS β κ φπ φx = 1)
    {rn ib infl x : ℕ → Ω → ℝ} (hE : TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib infl x) (c : ℝ) :
    TaylorEqm 𝔼 β σ κ φπ φx πbar rn ib (fun t => infl t + fun _ => c)
        (fun t => x t + fun _ => c * (1 - β) / κ) ∧
      taylorRate β κ φπ φx πbar ib (fun t => infl t + fun _ => c)
          (fun t => x t + fun _ => c * (1 - β) / κ) =
        fun t => taylorRate β κ φπ φx πbar ib infl x t + fun _ => c := by
  unfold taylorLHS at h
  have hrate : taylorRate β κ φπ φx πbar ib (fun t => infl t + fun _ => c)
      (fun t => x t + fun _ => c * (1 - β) / κ) =
        fun t => taylorRate β κ φπ φx πbar ib infl x t + fun _ => c := by
    funext t ω
    simp only [taylorRate, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp at h ⊢
    linear_combination c * h
  obtain ⟨h1, h2⟩ := hE
  refine ⟨⟨?_, ?_⟩, hrate⟩
  · rw [hrate]
    rw [IS_iff] at h1 ⊢
    intro t ω
    have := h1 t ω
    simp only [map_add, 𝔼.const, Pi.add_apply]
    linarith
  · rw [NKPC_iff] at h2 ⊢
    intro t ω
    have := h2 t ω
    simp only [map_add, 𝔼.const, Pi.add_apply]
    field_simp
    linear_combination this

/-! ### Exogenous interest rate: (2.5)–(2.6) -/

/-- Woodford (2003), §2.2, p. 252: `(π, x)` is an equilibrium of (1.12)–(1.13) when the
nominal interest rate follows the exogenous path `î_t = ī_t`. -/
def ExoEqm (β σ κ : ℝ) (rn ib infl x : ℕ → Ω → ℝ) : Prop :=
  IS112 𝔼 σ x ib infl rn ∧ NKPCurve 𝔼 β κ infl x

/-- Woodford (2003), eq. (2.5), p. 252: the matrix `A` of `E_t z_{t+1} = A z_t + a (r̂ⁿ_t − î_t)`
for an exogenous interest rate. -/
noncomputable def A25 (β σ κ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![β⁻¹, -(β⁻¹ * κ); -(β⁻¹ * σ), 1 + β⁻¹ * κ * σ]

/-- Woodford (2003), eq. (2.5), p. 252: the coefficient vector `a = (0, −σ)`. -/
def a25 (σ : ℝ) : Fin 2 → ℝ := ![0, -σ]

/-- Woodford (2003), eq. (2.5), p. 252: the (2.5) matrix is the (C.19) matrix with
`φ_π = φ_x = 0`. -/
theorem A25_eq_taylorA (β σ κ : ℝ) : A25 β σ κ = taylorA β σ κ 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [A25, taylorA] <;> ring

/-- Woodford (2003), §2.2, p. 252: an exogenous interest-rate path is the Taylor rule (1.14) with
`φ_π = φ_x = 0` and `π̄ = 0`. -/
theorem exoEqm_eq_taylor (β σ κ : ℝ) : ExoEqm 𝔼 β σ κ = TaylorEqm 𝔼 β σ κ 0 0 0 := by
  funext rn ib infl x
  have : taylorRate β κ 0 0 0 ib infl x = ib := by
    funext t
    simp [taylorRate]
  rw [ExoEqm, TaylorEqm, this]

/-- Woodford (2003), eqs. (2.5)–(2.6), p. 252: with an exogenous interest rate, (1.12)–(1.13)
are equivalent to `E_t z_{t+1} = A z_t + a (r̂ⁿ_t − î_t)`, `z = (π, x)`. -/
theorem model_iff_system25 {β σ κ : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (rn ib infl x : ℕ → Ω → ℝ) :
    ExoEqm 𝔼 β σ κ rn ib infl x ↔ ∀ t ω,
      (𝔼.E t (infl (t + 1)) ω = A25 β σ κ 0 0 * infl t ω + A25 β σ κ 0 1 * x t ω
          + a25 σ 0 * (rn t ω - ib t ω)) ∧
      (𝔼.E t (x (t + 1)) ω = A25 β σ κ 1 0 * infl t ω + A25 β σ κ 1 1 * x t ω
          + a25 σ 1 * (rn t ω - ib t ω)) := by
  rw [exoEqm_eq_taylor, taylorEqm_iff_C19 𝔼 hβ hκ 0, A25_eq_taylorA]
  simp [xbar, a25]

/-- Woodford (2003), p. 252: the characteristic polynomial
`P(μ) = μ² − [1 + β⁻¹(1 + κσ)] μ + β⁻¹` of the (2.5) matrix. -/
noncomputable def charPoly25 (β σ κ μ : ℝ) : ℝ := μ ^ 2 - (1 + β⁻¹ * (1 + κ * σ)) * μ + β⁻¹

/-- Woodford (2003), p. 252: `tr A = 1 + β⁻¹(1 + κσ)` and `det A = β⁻¹` for (2.5), so
`det(A − μ I) = P(μ)`. -/
theorem A25_tr_det (β σ κ μ : ℝ) :
    tr2 (A25 β σ κ) = 1 + β⁻¹ * (1 + κ * σ) ∧
      (β ≠ 0 → det2 (A25 β σ κ) = β⁻¹) ∧
      μ ^ 2 - tr2 (A25 β σ κ) * μ + β⁻¹ = charPoly25 β σ κ μ := by
  refine ⟨?_, fun hβ => ?_, ?_⟩
  · simp [A25, tr2]; ring
  · simp [A25, det2]; field_simp; ring
  · unfold charPoly25 tr2
    simp only [A25, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring

/-- Woodford (2003), p. 252: `P(0) = β⁻¹ > 0`. -/
theorem charPoly25_zero {β : ℝ} (hβ : 0 < β) (σ κ : ℝ) : 0 < charPoly25 β σ κ 0 := by
  simp [charPoly25, hβ]

/-- Woodford (2003), p. 252: `P(1) = −β⁻¹κσ < 0`. -/
theorem charPoly25_one {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    charPoly25 β σ κ 1 = -(β⁻¹ * κ * σ) ∧ charPoly25 β σ κ 1 < 0 := by
  have e : charPoly25 β σ κ 1 = -(β⁻¹ * κ * σ) := by simp [charPoly25]; ring
  have : 0 < β⁻¹ * κ * σ := by positivity
  refine ⟨e, ?_⟩
  rw [e]
  linarith

/-- Woodford (2003), p. 252: `P(μ) > 0` again for large `μ > 1`: `P(T) = β⁻¹ > 0` at
`T = 1 + β⁻¹(1 + κσ) > 1`. -/
theorem charPoly25_large {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    1 < 1 + β⁻¹ * (1 + κ * σ) ∧ 0 < charPoly25 β σ κ (1 + β⁻¹ * (1 + κ * σ)) := by
  have : 0 < β⁻¹ * (1 + κ * σ) := by positivity
  refine ⟨by linarith, ?_⟩
  simp only [charPoly25]
  ring_nf
  positivity

/-- Woodford (2003), p. 252: the discriminant of `P`. -/
noncomputable def disc25 (β σ κ : ℝ) : ℝ := (1 + β⁻¹ * (1 + κ * σ)) ^ 2 - 4 * β⁻¹

/-- Woodford (2003), p. 253: the smaller eigenvalue `μ₁` of the (2.5) matrix. -/
noncomputable def mu1 (β σ κ : ℝ) : ℝ := (1 + β⁻¹ * (1 + κ * σ) - Real.sqrt (disc25 β σ κ)) / 2

/-- Woodford (2003), p. 253: the larger eigenvalue `μ₂` of the (2.5) matrix. -/
noncomputable def mu2 (β σ κ : ℝ) : ℝ := (1 + β⁻¹ * (1 + κ * σ) + Real.sqrt (disc25 β σ κ)) / 2

/-- Woodford (2003), p. 252: the discriminant is positive (the eigenvalues are real and
distinct), because `P(1) < 0`. -/
theorem disc25_pos {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) : 0 < disc25 β σ κ := by
  have h1 := (charPoly25_one hβ hσ hκ).2
  have hb : 0 < β⁻¹ := inv_pos.mpr hβ
  unfold charPoly25 at h1
  unfold disc25
  nlinarith [sq_nonneg (1 - β⁻¹)]

/-- Woodford (2003), p. 253: `μ₁` and `μ₂` are the roots of `P`: `μ₁ + μ₂ = tr A`,
`μ₁ μ₂ = det A`, `P(μ₁) = P(μ₂) = 0`. -/
theorem mu_roots {β σ κ : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hκ : 0 < κ) :
    mu1 β σ κ + mu2 β σ κ = 1 + β⁻¹ * (1 + κ * σ) ∧ mu1 β σ κ * mu2 β σ κ = β⁻¹ ∧
      charPoly25 β σ κ (mu1 β σ κ) = 0 ∧ charPoly25 β σ κ (mu2 β σ κ) = 0 := by
  have hs : Real.sqrt (disc25 β σ κ) ^ 2 = (1 + β⁻¹ * (1 + κ * σ)) ^ 2 - 4 * β⁻¹ :=
    Real.sq_sqrt (disc25_pos hβ hσ hκ).le
  unfold mu1 mu2 charPoly25
  refine ⟨by ring, ?_, ?_, ?_⟩
  · linear_combination (-1 / 4 : ℝ) * hs
  · linear_combination (1 / 4 : ℝ) * hs
  · linear_combination (1 / 4 : ℝ) * hs

/-- Woodford (2003), p. 253: the root location `0 < μ₁ < 1 < μ₂`. -/
theorem mu_location {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) :
    0 < mu1 β σ κ ∧ mu1 β σ κ < 1 ∧ 1 < mu2 β σ κ := by
  have hd := disc25_pos hβ0 hσ hκ
  have hs0 := Real.sqrt_nonneg (disc25 β σ κ)
  have hb : 1 < β⁻¹ := (one_lt_inv₀ hβ0).mpr hβ1
  have hT : 2 < 1 + β⁻¹ * (1 + κ * σ) := by
    have : β⁻¹ ≤ β⁻¹ * (1 + κ * σ) := le_mul_of_one_le_right (by linarith) (by nlinarith)
    linarith
  have h1 := (charPoly25_one hβ0 hσ hκ).2
  unfold charPoly25 at h1
  refine ⟨?_, ?_, ?_⟩
  · unfold mu1
    have : Real.sqrt (disc25 β σ κ) < 1 + β⁻¹ * (1 + κ * σ) := by
      rw [Real.sqrt_lt' (by linarith)]
      unfold disc25
      have : 0 < β⁻¹ := by linarith
      linarith
    linarith
  · unfold mu1
    have : 1 + β⁻¹ * (1 + κ * σ) - 2 < Real.sqrt (disc25 β σ κ) := by
      rw [Real.lt_sqrt (by linarith)]
      unfold disc25
      nlinarith
    linarith
  · unfold mu2
    linarith

/-- Woodford (2003), p. 253: `μ₁ ≠ μ₂`. -/
theorem mu1_ne_mu2 {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ) :
    mu1 β σ κ ≠ mu2 β σ κ := by
  have := mu_location hβ0 hβ1 hσ hκ
  intro h
  linarith [this.2.1, this.2.2]

/-- Woodford (2003), p. 252: for a root `μ` of `P`, `v = (κ, 1 − βμ)` is a right eigenvector of
the (2.5) matrix: both eigenvalues are real. -/
theorem A25_eigenvector {β σ κ μ : ℝ} (hβ : β ≠ 0) (hμ : charPoly25 β σ κ μ = 0) :
    (A25 β σ κ).mulVec ![κ, 1 - β * μ] = μ • ![κ, 1 - β * μ] := by
  unfold charPoly25 at hμ
  ext i
  fin_cases i <;> simp [A25, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · field_simp; ring
  · field_simp
    field_simp at hμ
    linear_combination β * hμ

/-- Woodford (2003), p. 252: `β P(μ) = β μ² − (1 + β + κσ) μ + 1`. -/
theorem charPoly25_mul {β σ κ μ : ℝ} (hβ : β ≠ 0) :
    β * charPoly25 β σ κ μ = β * μ ^ 2 - (β + 1 + κ * σ) * μ + 1 := by
  unfold charPoly25
  field_simp
  ring

/-! ### Proposition 4.2: decoupling along the left eigenvectors -/

/-- Woodford (2003), p. 253 (proof of Proposition 4.2), state by state: with roots `μ₁ ≠ μ₂` of
`P`, the model (1.12)–(1.13) with exogenous `î` is equivalent to the two scalar equations
`y_j = μ_j⁻¹ E y_j′ + σ(1 − βμ_j)/μ_j · (r̂ⁿ − î)` for the left-eigenvector coordinates
`y_j = σ π + (1 − βμ_j) x`. -/
theorem exo_decouple_pt {β σ κ μ₁ μ₂ : ℝ} (hσ : σ ≠ 0) (h12 : μ₁ ≠ μ₂) (h1 : μ₁ ≠ 0)
    (h2 : μ₂ ≠ 0) (hr1 : β * μ₁ ^ 2 - (β + 1 + κ * σ) * μ₁ + 1 = 0)
    (hr2 : β * μ₂ ^ 2 - (β + 1 + κ * σ) * μ₂ + 1 = 0) {p x P X rn i : ℝ} :
    (x = X - σ * (i - P - rn) ∧ p = κ * x + β * P) ↔
      (σ * p + (1 - β * μ₁) * x = μ₁⁻¹ * (σ * P + (1 - β * μ₁) * X)
          + σ * (1 - β * μ₁) / μ₁ * (rn - i) ∧
        σ * p + (1 - β * μ₂) * x = μ₂⁻¹ * (σ * P + (1 - β * μ₂) * X)
          + σ * (1 - β * μ₂) / μ₂ * (rn - i)) := by
  have hm : (x = X - σ * (i - P - rn) ∧ p = κ * x + β * P) ↔
      (β * P = p - κ * x ∧ X = x + σ * (i - P - rn)) :=
    ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩
  have hs : ∀ μ : ℝ, μ ≠ 0 →
      (σ * p + (1 - β * μ) * x = μ⁻¹ * (σ * P + (1 - β * μ) * X)
          + σ * (1 - β * μ) / μ * (rn - i) ↔
        μ * (σ * p + (1 - β * μ) * x) = σ * P + (1 - β * μ) * X
          + σ * (1 - β * μ) * (rn - i)) := by
    intro μ hμ
    have e : μ⁻¹ * (σ * P + (1 - β * μ) * X) + σ * (1 - β * μ) / μ * (rn - i) =
        μ⁻¹ * (σ * P + (1 - β * μ) * X + σ * (1 - β * μ) * (rn - i)) := by ring
    rw [e, eq_inv_mul_iff_mul_eq₀ hμ]
  rw [hm, hs μ₁ h1, hs μ₂ h2]
  constructor
  · rintro ⟨m1, m2⟩
    exact ⟨by linear_combination (-x) * hr1 - μ₁ * σ * m1 - (1 - β * μ₁) * m2,
      by linear_combination (-x) * hr2 - μ₂ * σ * m1 - (1 - β * μ₂) * m2⟩
  · rintro ⟨s1, s2⟩
    have q1 : σ * (μ₁ - μ₂) * (β * P - (p - κ * x)) = 0 := by
      linear_combination (-(1 - β * μ₂)) * s1 + (-(1 - β * μ₂) * x) * hr1
        + (1 - β * μ₁) * s2 + ((1 - β * μ₁) * x) * hr2
    have q2 : (μ₂ - μ₁) * (X - (x + σ * (i - P - rn))) = 0 := by
      linear_combination (-μ₂) * s1 + (-μ₂ * x) * hr1 + μ₁ * s2 + (μ₁ * x) * hr2
    have hd1 : σ * (μ₁ - μ₂) ≠ 0 := mul_ne_zero hσ (sub_ne_zero.mpr h12)
    have hd2 : μ₂ - μ₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
    have e1 := (mul_eq_zero.mp q1).resolve_left hd1
    have e2 := (mul_eq_zero.mp q2).resolve_left hd2
    exact ⟨by linarith, by linarith⟩

omit 𝔼 in
/-- Woodford (2003), p. 253: the left-eigenvector coordinate `y_t = σ π_t + (1 − βμ) x_t`. -/
def yproc (β σ μ : ℝ) (infl x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => σ • infl t + (1 - β * μ) • x t

omit 𝔼 in
/-- Woodford (2003), p. 253: the forcing `σ(1 − βμ)/μ · (r̂ⁿ_t − î_t)` of the scalar equation
for `y`. -/
noncomputable def uproc (β σ μ : ℝ) (rn ib : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (σ * (1 - β * μ) / μ) • (rn t - ib t)

/-- Woodford (2003), p. 253 (Proposition 4.2): with an exogenous interest rate the model is
equivalent to two decoupled scalar equations (A.14): `y₁ = μ₁⁻¹ E y₁′ + u₁` with `μ₁⁻¹ > 1`
and `y₂ = μ₂⁻¹ E y₂′ + u₂` with `0 < μ₂⁻¹ < 1`. -/
theorem exoEqm_iff_decoupled {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) (rn ib infl x : ℕ → Ω → ℝ) :
    ExoEqm 𝔼 β σ κ rn ib infl x ↔
      ForwardSolution.Solves 𝔼 (mu1 β σ κ)⁻¹ (uproc β σ (mu1 β σ κ) rn ib)
          (yproc β σ (mu1 β σ κ) infl x) ∧
        ForwardSolution.Solves 𝔼 (mu2 β σ κ)⁻¹ (uproc β σ (mu2 β σ κ) rn ib)
          (yproc β σ (mu2 β σ κ) infl x) := by
  obtain ⟨-, -, hp1, hp2⟩ := mu_roots hβ0 hσ hκ
  obtain ⟨hm1, -, hm2⟩ := mu_location hβ0 hβ1 hσ hκ
  have hr1 := charPoly25_mul (σ := σ) (κ := κ) (μ := mu1 β σ κ) hβ0.ne'
  have hr2 := charPoly25_mul (σ := σ) (κ := κ) (μ := mu2 β σ κ) hβ0.ne'
  rw [hp1, mul_zero] at hr1
  rw [hp2, mul_zero] at hr2
  rw [ExoEqm, IS_iff, NKPC_iff, ← forall_and]
  simp only [ForwardSolution.Solves, funext_iff, yproc, uproc, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_smul, Pi.sub_apply, ← forall_and]
  refine forall₂_congr fun t ω => ?_
  exact exo_decouple_pt hσ.ne' (mu1_ne_mu2 hβ0 hβ1 hσ hκ) hm1.ne' (by linarith) hr1.symm
    hr2.symm

omit 𝔼 in
/-- Woodford (2003), p. 253: recovering the output gap from the coordinates,
`x = (y₁ − y₂)/(β(μ₂ − μ₁))`. -/
noncomputable def recX (β μ₁ μ₂ : ℝ) (y₁ y₂ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (β * (μ₂ - μ₁))⁻¹ • (y₁ t - y₂ t)

omit 𝔼 in
/-- Woodford (2003), p. 253: recovering inflation from the coordinates,
`π = (y₁ − (1 − βμ₁) x)/σ`. -/
noncomputable def recP (β σ μ₁ μ₂ : ℝ) (y₁ y₂ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => σ⁻¹ • (y₁ t - (1 - β * μ₁) • recX β μ₁ μ₂ y₁ y₂ t)

omit 𝔼 in
/-- Woodford (2003), p. 253: the coordinates of the recovered `(π, x)` are `(y₁, y₂)`. -/
theorem yproc_rec {β σ μ₁ μ₂ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0) (h12 : μ₁ ≠ μ₂)
    (y₁ y₂ : ℕ → Ω → ℝ) :
    yproc β σ μ₁ (recP β σ μ₁ μ₂ y₁ y₂) (recX β μ₁ μ₂ y₁ y₂) = y₁ ∧
      yproc β σ μ₂ (recP β σ μ₁ μ₂ y₁ y₂) (recX β μ₁ μ₂ y₁ y₂) = y₂ := by
  have hd : μ₂ - μ₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  constructor <;> funext t ω <;>
    simp only [yproc, recP, recX, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] <;>
    field_simp <;> ring

omit 𝔼 in
/-- Woodford (2003), p. 253: `(π, x)` is recovered from its coordinates `(y₁, y₂)`. -/
theorem rec_yproc {β σ μ₁ μ₂ : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0) (h12 : μ₁ ≠ μ₂)
    (infl x : ℕ → Ω → ℝ) :
    recP β σ μ₁ μ₂ (yproc β σ μ₁ infl x) (yproc β σ μ₂ infl x) = infl ∧
      recX β μ₁ μ₂ (yproc β σ μ₁ infl x) (yproc β σ μ₂ infl x) = x := by
  have hd : μ₂ - μ₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  constructor <;> funext t ω <;>
    simp only [yproc, recP, recX, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] <;>
    field_simp <;> ring

omit 𝔼 in
/-- Woodford (2003), p. 253: bounded coordinates give bounded `(π, x)`. -/
theorem rec_bounded (β σ μ₁ μ₂ : ℝ) {y₁ y₂ : ℕ → Ω → ℝ} (h1 : BoundedProc y₁)
    (h2 : BoundedProc y₂) :
    BoundedProc (recP β σ μ₁ μ₂ y₁ y₂) ∧ BoundedProc (recX β μ₁ μ₂ y₁ y₂) := by
  obtain ⟨M₁, hM₁⟩ := h1
  obtain ⟨M₂, hM₂⟩ := h2
  set c := (β * (μ₂ - μ₁))⁻¹
  have hx : ∀ t ω, |recX β μ₁ μ₂ y₁ y₂ t ω| ≤ |c| * (M₁ + M₂) := by
    intro t ω
    simp only [recX, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω)))
      (abs_nonneg _)
  refine ⟨⟨|σ⁻¹| * (M₁ + |1 - β * μ₁| * (|c| * (M₁ + M₂))), fun t ω => ?_⟩, ⟨_, hx⟩⟩
  simp only [recP, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
  refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM₁ t ω) ?_))
    (abs_nonneg _)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hx t ω) (abs_nonneg _)

/-- Woodford (2003), p. 253: adapted coordinates give adapted `(π, x)`. -/
theorem rec_adapted (β σ μ₁ μ₂ : ℝ) {y₁ y₂ : ℕ → Ω → ℝ} (h1 : 𝔼.Adapted y₁)
    (h2 : 𝔼.Adapted y₂) :
    𝔼.Adapted (recP β σ μ₁ μ₂ y₁ y₂) ∧ 𝔼.Adapted (recX β μ₁ μ₂ y₁ y₂) := by
  have hx : 𝔼.Adapted (recX β μ₁ μ₂ y₁ y₂) := by
    intro t
    simp only [recX, map_smul, map_sub, h1 t, h2 t]
  refine ⟨fun t => ?_, hx⟩
  simp only [recP, map_smul, map_sub, h1 t, hx t]

/-- Woodford (2003), p. 253: the forcing of the scalar equations is bounded and adapted. -/
theorem uproc_bounded_adapted (β σ μ : ℝ) {rn ib : ℕ → Ω → ℝ} (hrn : BoundedProc rn)
    (hib : BoundedProc ib) (harn : 𝔼.Adapted rn) (haib : 𝔼.Adapted ib) :
    (∃ M, ∀ t ω, |uproc β σ μ rn ib t ω| ≤ M) ∧ 𝔼.Adapted (uproc β σ μ rn ib) := by
  obtain ⟨M₁, hM₁⟩ := hrn
  obtain ⟨M₂, hM₂⟩ := hib
  refine ⟨⟨|σ * (1 - β * μ) / μ| * (M₁ + M₂), fun t ω => ?_⟩, fun t => ?_⟩
  · simp only [uproc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω)))
      (abs_nonneg _)
  · simp only [uproc, map_smul, map_sub, harn t, haib t]

/-- Woodford (2003), p. 253 (Proposition 4.2): the explicit family of equilibria under an
exogenous interest rate. The stable coordinate `y₂` is the forward sum
`∑ μ₂⁻ᵏ E_t u₂_{t+k}`; the unstable coordinate `y₁` starts at an arbitrary date-0 value `z₀`
and evolves as `y₁_{t+1} = μ₁ (y₁_t − u₁_t) + ν_{t+1}` for an arbitrary martingale-difference
sunspot `ν` (eq. (A.17)). -/
noncomputable def fam25 (β σ κ : ℝ) (rn ib : ℕ → Ω → ℝ) (z0 : Ω → ℝ) (ν : ℕ → Ω → ℝ) :
    (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) :=
  (recP β σ (mu1 β σ κ) (mu2 β σ κ)
      (ForwardSolution.sunspotFamily (mu1 β σ κ)⁻¹ (uproc β σ (mu1 β σ κ) rn ib) ν z0)
      (𝔼.forwardSeries (mu2 β σ κ)⁻¹ (uproc β σ (mu2 β σ κ) rn ib)),
    recX β (mu1 β σ κ) (mu2 β σ κ)
      (ForwardSolution.sunspotFamily (mu1 β σ κ)⁻¹ (uproc β σ (mu1 β σ κ) rn ib) ν z0)
      (𝔼.forwardSeries (mu2 β σ κ)⁻¹ (uproc β σ (mu2 β σ κ) rn ib)))

/-- **Proposition 4.2** (Woodford (2003), p. 253), existence part: for any bounded adapted
natural rate `r̂ⁿ` and exogenous interest-rate path `ī`, every member of `fam25` — any bounded
date-0 value `z₀` and any bounded adapted sunspot `ν` with `E_t ν_{t+1} = 0` — is a bounded
adapted equilibrium. -/
theorem prop_4_2_family {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    {rn ib : ℕ → Ω → ℝ} (hrn : BoundedProc rn) (hib : BoundedProc ib) (harn : 𝔼.Adapted rn)
    (haib : 𝔼.Adapted ib) {z0 : Ω → ℝ} {B : ℝ} (hz0 : ∀ ω, |z0 ω| ≤ B) (hz0a : 𝔼.E 0 z0 = z0)
    {ν : ℕ → Ω → ℝ} {Mν : ℝ} (hν : ∀ t ω, |ν t ω| ≤ Mν) (hνa : 𝔼.Adapted ν)
    (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) :
    BoundedProc (fam25 𝔼 β σ κ rn ib z0 ν).1 ∧ BoundedProc (fam25 𝔼 β σ κ rn ib z0 ν).2 ∧
      𝔼.Adapted (fam25 𝔼 β σ κ rn ib z0 ν).1 ∧ 𝔼.Adapted (fam25 𝔼 β σ κ rn ib z0 ν).2 ∧
      ExoEqm 𝔼 β σ κ rn ib (fam25 𝔼 β σ κ rn ib z0 ν).1 (fam25 𝔼 β σ κ rn ib z0 ν).2 := by
  obtain ⟨hm1, hm11, hm2⟩ := mu_location hβ0 hβ1 hσ hκ
  have h12 := mu1_ne_mu2 hβ0 hβ1 hσ hκ
  obtain ⟨⟨M₁, hu1⟩, hu1a⟩ := uproc_bounded_adapted 𝔼 β σ (mu1 β σ κ) hrn hib harn haib
  obtain ⟨⟨M₂, hu2⟩, hu2a⟩ := uproc_bounded_adapted 𝔼 β σ (mu2 β σ κ) hrn hib harn haib
  have ha1 : 1 < |(mu1 β σ κ)⁻¹| := by
    rw [abs_inv, abs_of_pos hm1]; exact (one_lt_inv₀ hm1).mpr hm11
  have ha2 : |(mu2 β σ κ)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hm2
  set y₁ := ForwardSolution.sunspotFamily (mu1 β σ κ)⁻¹ (uproc β σ (mu1 β σ κ) rn ib) ν z0
  set y₂ := 𝔼.forwardSeries (mu2 β σ κ)⁻¹ (uproc β σ (mu2 β σ κ) rn ib)
  have hy1 := ForwardSolution.sunspotFamily_solves 𝔼 (inv_ne_zero hm1.ne') hz0a hu1a hνa hmd
  have hy1b := ForwardSolution.sunspotFamily_bounded (u := uproc β σ (mu1 β σ κ) rn ib)
    ha1 hz0 hu1 hν
  have hy1a := ForwardSolution.sunspotFamily_adapted (a := (mu1 β σ κ)⁻¹) 𝔼 hz0a hu1a hνa
  have hy2 := ForwardSolution.forwardSeries_solves_abs 𝔼 ha2 hu2 hu2a
  have hy2b := ForwardSolution.forwardSeries_bounded_abs 𝔼 ha2 hu2
  have hy2a := ForwardSolution.forwardSeries_adapted_abs 𝔼 ha2 hu2
  obtain ⟨hb1, hb2⟩ := rec_bounded β σ (mu1 β σ κ) (mu2 β σ κ) hy1b hy2b
  obtain ⟨ha1', ha2'⟩ := rec_adapted 𝔼 β σ (mu1 β σ κ) (mu2 β σ κ) hy1a hy2a
  refine ⟨hb1, hb2, ha1', ha2', ?_⟩
  rw [exoEqm_iff_decoupled 𝔼 hβ0 hβ1 hσ hκ]
  obtain ⟨e1, e2⟩ := yproc_rec (σ := σ) hβ0.ne' hσ.ne' h12 y₁ y₂
  simp only [fam25]
  rw [e1, e2]
  exact ⟨hy1, hy2⟩

/-- **Proposition 4.2** (Woodford (2003), p. 253), completeness: every bounded adapted
equilibrium under an exogenous interest rate belongs to `fam25`, with `z₀ = σπ₀ + (1 − βμ₁)x₀`
and the sunspot `ν_{t+1} = y₁_{t+1} − E_t y₁_{t+1}`. -/
theorem prop_4_2_complete {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ) (hκ : 0 < κ)
    {rn ib : ℕ → Ω → ℝ} (hrn : BoundedProc rn) (hib : BoundedProc ib) (harn : 𝔼.Adapted rn)
    (haib : 𝔼.Adapted ib) {infl x : ℕ → Ω → ℝ} (hπb : BoundedProc infl) (hxb : BoundedProc x)
    (hπa : 𝔼.Adapted infl) (hxa : 𝔼.Adapted x) (hE : ExoEqm 𝔼 β σ κ rn ib infl x) :
    ∃ (z0 : Ω → ℝ) (ν : ℕ → Ω → ℝ), (∃ B, ∀ ω, |z0 ω| ≤ B) ∧ 𝔼.E 0 z0 = z0 ∧
      (∃ Mν, ∀ t ω, |ν t ω| ≤ Mν) ∧ 𝔼.Adapted ν ∧ (∀ t, 𝔼.E t (ν (t + 1)) = 0) ∧
      (infl, x) = fam25 𝔼 β σ κ rn ib z0 ν := by
  obtain ⟨hm1, hm11, hm2⟩ := mu_location hβ0 hβ1 hσ hκ
  have h12 := mu1_ne_mu2 hβ0 hβ1 hσ hκ
  obtain ⟨⟨M₂, hu2⟩, hu2a⟩ := uproc_bounded_adapted 𝔼 β σ (mu2 β σ κ) hrn hib harn haib
  have ha2 : |(mu2 β σ κ)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hm2
  obtain ⟨hs1, hs2⟩ := (exoEqm_iff_decoupled 𝔼 hβ0 hβ1 hσ hκ rn ib infl x).mp hE
  set y₁ := yproc β σ (mu1 β σ κ) infl x with hy₁
  set y₂ := yproc β σ (mu2 β σ κ) infl x with hy₂
  -- boundedness and adaptedness of the coordinates
  obtain ⟨Mπ, hMπ⟩ := hπb
  obtain ⟨Mx, hMx⟩ := hxb
  have hyb : ∀ μ : ℝ, ∀ t ω, |yproc β σ μ infl x t ω| ≤ |σ| * Mπ + |1 - β * μ| * Mx := by
    intro μ t ω
    simp only [yproc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul_of_nonneg_left (hMπ t ω) (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_left (hMx t ω) (abs_nonneg _)
  have hya : ∀ μ : ℝ, 𝔼.Adapted (yproc β σ μ infl x) := by
    intro μ t
    simp only [yproc, map_add, map_smul, hπa t, hxa t]
  have hy2 : y₂ = 𝔼.forwardSeries (mu2 β σ κ)⁻¹ (uproc β σ (mu2 β σ κ) rn ib) :=
    ForwardSolution.eq_forwardSeries_abs 𝔼 ha2 hu2 hu2a hs2 ⟨_, hyb _⟩
  obtain ⟨hmd, hy1⟩ := ForwardSolution.eq_sunspotFamily 𝔼 (inv_ne_zero hm1.ne') hs1
  set ν : ℕ → Ω → ℝ := fun t => y₁ t - 𝔼.E (t - 1) (y₁ t) with hν
  refine ⟨y₁ 0, ν, ⟨_, hyb _ 0⟩, hya _ 0, ⟨2 * (|σ| * Mπ + |1 - β * mu1 β σ κ| * Mx),
    fun t ω => ?_⟩, fun t => ?_, fun t => ?_, ?_⟩
  · simp only [hν, Pi.sub_apply]
    refine (abs_sub _ _).trans ?_
    have := 𝔼.abs_E_le (fun ω' => hyb (mu1 β σ κ) t ω') (t - 1) ω
    linarith [hyb (mu1 β σ κ) t ω]
  · have h1 : 𝔼.E t (y₁ t) = y₁ t := hya _ t
    simp only [hν, map_sub, h1,
      ForwardSolution.E_of_known 𝔼 (Nat.sub_le t 1) (𝔼.E_E_self (t - 1) (y₁ t))]
  · simpa [hν] using hmd t
  · obtain ⟨r1, r2⟩ := rec_yproc (β := β) hβ0.ne' hσ.ne' h12 infl x
    simp only [fam25]
    rw [← hy2, ← hy1]
    exact Prod.ext r1.symm r2.symm

/-- **Proposition 4.2** (Woodford (2003), p. 253): an explicit continuum of bounded adapted
equilibria, for every bounded adapted `r̂ⁿ` and every bounded adapted exogenous path `ī`,
indexed injectively by the date-0 value `c` of the unstable coordinate. -/
theorem prop_4_2_continuum [Nonempty Ω] {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) {rn ib : ℕ → Ω → ℝ} (hrn : BoundedProc rn) (hib : BoundedProc ib)
    (harn : 𝔼.Adapted rn) (haib : 𝔼.Adapted ib) :
    Function.Injective (fun c : ℝ => fam25 𝔼 β σ κ rn ib (fun _ => c) (fun _ _ => 0)) ∧
      ∀ c : ℝ, BoundedProc (fam25 𝔼 β σ κ rn ib (fun _ => c) (fun _ _ => 0)).1 ∧
        BoundedProc (fam25 𝔼 β σ κ rn ib (fun _ => c) (fun _ _ => 0)).2 ∧
        𝔼.Adapted (fam25 𝔼 β σ κ rn ib (fun _ => c) (fun _ _ => 0)).1 ∧
        𝔼.Adapted (fam25 𝔼 β σ κ rn ib (fun _ => c) (fun _ _ => 0)).2 ∧
        ExoEqm 𝔼 β σ κ rn ib (fam25 𝔼 β σ κ rn ib (fun _ => c) (fun _ _ => 0)).1
          (fam25 𝔼 β σ κ rn ib (fun _ => c) (fun _ _ => 0)).2 := by
  refine ⟨fun c c' h => ?_, fun c => prop_4_2_family 𝔼 hβ0 hβ1 hσ hκ hrn hib harn haib
    (B := |c|) (fun _ => le_rfl) (𝔼.const 0 c) (Mν := 0) (fun _ _ => by simp)
    (fun t => 𝔼.const t 0) (fun t => 𝔼.const t 0)⟩
  have h12 := mu1_ne_mu2 hβ0 hβ1 hσ hκ
  have key : ∀ d : ℝ, yproc β σ (mu1 β σ κ) (fam25 𝔼 β σ κ rn ib (fun _ => d) (fun _ _ => 0)).1
      (fam25 𝔼 β σ κ rn ib (fun _ => d) (fun _ _ => 0)).2 0 = fun _ => d := by
    intro d
    simp only [fam25]
    rw [(yproc_rec (σ := σ) hβ0.ne' hσ.ne' h12 _ _).1]
    rfl
  have := key c
  simp only at h
  rw [h, key c'] at this
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  exact (congrFun this ω).symm

/-- **Proposition 4.2** (Woodford (2003), p. 253): if the nominal interest rate follows an
exogenous path, rational-expectations equilibrium is indeterminate, whatever the target process
(for every bounded adapted `r̂ⁿ` and `ī` there are infinitely many bounded adapted equilibria,
`prop_4_2_continuum`; in particular the model is not determinate). -/
theorem prop_4_2 [Nonempty Ω] {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : 0 < σ)
    (hκ : 0 < κ) : ¬ ModelDeterminate 𝔼 (ExoEqm 𝔼 β σ κ) := by
  intro h
  have hz : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hza : 𝔼.Adapted (fun _ _ => (0 : ℝ) : ℕ → Ω → ℝ) := fun t => 𝔼.const t 0
  obtain ⟨hinj, hall⟩ := prop_4_2_continuum 𝔼 hβ0 hβ1 hσ hκ hz hz hza hza
  obtain ⟨p, -, hpu⟩ := h _ _ hz hz hza hza
  have e0 := hpu _ (hall 0)
  have e1 := hpu _ (hall 1)
  have := hinj (e0.trans e1.symm)
  norm_num at this

/-- Woodford (2003), p. 253 (Proposition 4.2 via Proposition 4.3): the exogenous-rate model is
the Taylor rule with `φ_π = φ_x = 0`, for which (2.7) fails. -/
theorem prop_4_2_via_prop_4_3 [Nonempty Ω] {β σ κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : 0 < σ) (hκ : 0 < κ) : ¬ ModelDeterminate 𝔼 (ExoEqm 𝔼 β σ κ) := by
  rw [exoEqm_eq_taylor, prop_4_3 𝔼 hβ0 hβ1 hσ hκ le_rfl le_rfl]
  simp [taylorLHS]

end Woodford.NeoWicksellianFramework.Determinacy2
