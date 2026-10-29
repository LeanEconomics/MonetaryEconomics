/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.TidyR6ODEExistence
import NeoWicksellianFramework.TidyR6Chetaev

/-!
# Lyapunov's indirect method for (2.20): the instability half and the exact equivalence

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, pp. 264–266 and n. 37: an s.c.e. `θ̄`
is E-stable if it is a locally stable rest point of `θ̇ = T(θ) − θ` (2.20); "the local
stability … depends on the eigenvalues of the Jacobian matrix `DT(θ̄) − I`", ignoring the
non-generic case of eigenvalues with zero real part. The stability half (negative real parts ⇒
locally asymptotically stable) is `TidyR5Lyapunov.isLAS_of_eStableAt`. Here the instability half
is proved for a general nonlinear `T`, and the two halves are combined.

Stability notions. `TidyR5Lyapunov.IsLAS` quantifies over forward solutions defined on all of
`[0, ∞)`. Here `IsLASLoc` is the textbook notion, in which Lyapunov stability also covers
solutions on finite intervals `[0, t₁]` (so a solution that leaves a neighbourhood and then blows
up in finite time counts as leaving). `isLAS_of_isLASLoc`: the textbook notion implies `IsLAS`.
The two differ: the module TidyR6InstabilityCex gives a hyperbolic, unstable `T` for which `IsLAS`
holds vacuously, because every non-constant solution blows up in finite time.

* **`unstable_loc`**: if `T` is Lipschitz on a closed ball around a rest point `θ̄`,
  differentiable at `θ̄`, and `DT(θ̄) − I` has an eigenvalue with positive real part, then for some
  `ε > 0` every neighbourhood of `θ̄` contains the start of a solution on some `[0, t₁]` that
  reaches distance `ε` from `θ̄`; `not_isLASLoc_of_unstable`: `θ̄` is not a (textbook) locally
  stable rest point. The solutions come from the globally Lipschitz modification `T ∘ clampBox`
  (Picard–Lindelöf plus continuation, TidyR6ODEExistence), the escape from the Chetaev function of
  TidyR6Chetaev, and a first-exit time.
* `unstable_of_fwdComplete`, `not_isLAS_of_unstable`: if the equation is forward complete (no
  Lipschitz condition needed), escaping forward solutions on `[0, ∞)` exist and `IsLAS` fails.
* `isLASLoc_of_eStableAt`: the stability half in the textbook sense.
* `isLAS_tMod_iff`: for `T` Lipschitz on a closed ball around `θ̄`, the textbook notion for `T`
  coincides with `IsLAS` for the globally Lipschitz, forward-complete modification
  `T ∘ clampBox` (`isLAS_tMod_of_isLASLoc`, `isLASLoc_of_isLAS_tMod`).
* **`eStableAt_iff_isLASLoc`**: when no eigenvalue of `DT(θ̄) − I` has zero real part
  (`NoZeroRe`), E-stability ⟺ `θ̄` is a locally asymptotically stable rest point of (2.20), for
  any `T` Lipschitz near `θ̄` and differentiable at `θ̄`; `eStableAt_iff_isLASLoc_of_contDiffAt`
  for `C¹` maps. **`eStableAt_iff_isLAS`**: the same for the solutions-on-`[0, ∞)` notion
  `IsLAS`, under forward completeness; `eStableAt_iff_of_lipschitz` for globally Lipschitz `T`.
  The zero-real-part case is genuinely undecided by `DT` (TidyR6InstabilityCex).
-/

namespace Woodford.NeoWicksellianFramework.TidyR6Instability

open Filter Topology TidyR5Lyapunov TidyR6ODEExistence TidyR6Chetaev
open Determinacy2Learning (EStable EStableAt)
open KroneckerSpectrum (IsEig)
open scoped NNReal

variable {ι : Type*} [Fintype ι]

/-! ### Definitions -/

/-- Woodford (2003), p. 264: `θ̄` is a **locally asymptotically stable rest point** of (2.20) in
the textbook sense: every solution, on any interval `[0, t₁]`, that starts close stays close
(Lyapunov stability), and forward solutions starting close enough converge to `θ̄`. -/
def IsLASLoc (T : (ι → ℝ) → ι → ℝ) (θs : ι → ℝ) : Prop :=
  (∀ ε > 0, ∃ δ > 0, ∀ (t₁ : ℝ) (θ : ℝ → ι → ℝ), IsSolOn T θ t₁ → ‖θ 0 - θs‖ < δ →
      ∀ τ ∈ Set.Icc 0 t₁, ‖θ τ - θs‖ < ε) ∧
    ∃ δ > 0, ∀ θ, IsFwdSol T θ → ‖θ 0 - θs‖ < δ → Tendsto θ atTop (𝓝 θs)

/-- Woodford (2003), n. 37 p. 266: the generic (hyperbolic) case: no eigenvalue of `J − I` has
zero real part. -/
def NoZeroRe [DecidableEq ι] (J : Matrix ι ι ℝ) : Prop :=
  ∀ ν : ℂ, IsEig ((J - 1).map Complex.ofReal) ν → ν.re ≠ 0

/-- Woodford (2003), p. 266: the Jacobian matrix `DT(θ̄)` of `T` at `θ̄`. -/
noncomputable abbrev jac [DecidableEq ι] (T : (ι → ℝ) → ι → ℝ) (θs : ι → ℝ) : Matrix ι ι ℝ :=
  LinearMap.toMatrix' (fderiv ℝ T θs : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-! ### Elementary facts -/

/-- Woodford (2003), p. 264: the textbook notion implies `IsLAS` (forward solutions restricted to
`[0, τ]` are solutions there). -/
theorem isLAS_of_isLASLoc {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} (h : IsLASLoc T θs) :
    IsLAS T θs := by
  refine ⟨fun ε hε => ?_, h.2⟩
  obtain ⟨δ, hδ, hst⟩ := h.1 ε hε
  exact ⟨δ, hδ, fun θ hθ h0 τ hτ =>
    hst τ θ (isSolOn_of_isFwdSol hθ τ) h0 τ ⟨hτ, le_rfl⟩⟩

omit [Fintype ι] in
/-- Woodford (2003), (2.20): a solution on `[0, t₁]` is a solution on `[0, s]` for `s ≤ t₁`. -/
theorem isSolOn_mono {T : (ι → ℝ) → ι → ℝ} {θ : ℝ → ι → ℝ} {s t₁ : ℝ} (h : IsSolOn T θ t₁)
    (hs : s ≤ t₁) : IsSolOn T θ s :=
  ⟨h.1.mono (Set.Icc_subset_Icc_right hs), fun τ hτ => h.2 τ ⟨hτ.1, lt_of_lt_of_le hτ.2 hs⟩⟩

/-- Woodford (2003), p. 266, n. 37: if `J` is not E-stable and no eigenvalue of `J − I` has
zero real part, some eigenvalue of `J − I` has positive real part. -/
theorem exists_pos_eig_of_not_eStable [DecidableEq ι] {J : Matrix ι ι ℝ} (hJ : ¬EStable J)
    (hnz : NoZeroRe J) : ∃ μ : ℂ, IsEig ((J - 1).map Complex.ofReal) μ ∧ 0 < μ.re := by
  unfold EStable at hJ
  push Not at hJ
  obtain ⟨μ, hμ, hre⟩ := hJ
  exact ⟨μ, hμ, lt_of_le_of_ne hre (hnz μ hμ).symm⟩

/-- Woodford (2003), p. 266: the modified map `T ∘ clampBox` has the same rest point, is
differentiable there and has the same Jacobian. -/
theorem tMod_local [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ} (hr : 0 < r)
    (hfix : T θs = θs) (hd : DifferentiableAt ℝ T θs) :
    tMod T θs r θs = θs ∧ DifferentiableAt ℝ (tMod T θs r) θs ∧
      jac (tMod T θs r) θs = jac T θs := by
  have hEq := eventuallyEq_tMod T θs hr
  refine ⟨?_, hEq.differentiableAt_iff.mpr hd, by rw [jac, jac, hEq.fderiv_eq]⟩
  rw [tMod_of_le T θs (by simp [hr.le]), hfix]

/-! ### The instability half -/

/-- Woodford (2003), pp. 264–266: **instability (textbook sense)**: if `T(θ̄) = θ̄`, `T` is
Lipschitz on a closed ball around `θ̄` and differentiable at `θ̄`, and `DT(θ̄) − I` has an
eigenvalue with positive real part, there is `ε > 0` such that within every distance `δ > 0` of
`θ̄` starts a solution of (2.20) on some `[0, t₁]` that reaches distance `ε` from `θ̄`. -/
theorem unstable_loc [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ} {K : ℝ≥0}
    (hr : 0 < r) (hL : LipschitzOnWith K T (Metric.closedBall θs r)) (hfix : T θs = θs)
    (hd : DifferentiableAt ℝ T θs) {μ : ℂ} (hμ : IsEig ((jac T θs - 1).map Complex.ofReal) μ)
    (hre : 0 < μ.re) :
    ∃ ε > 0, ∀ δ > 0, ∃ t₁ : ℝ, 0 ≤ t₁ ∧ ∃ θ : ℝ → ι → ℝ, IsSolOn T θ t₁ ∧
      ‖θ 0 - θs‖ < δ ∧ ε ≤ ‖θ t₁ - θs‖ := by
  obtain ⟨hfix', hd', hJ⟩ := tMod_local hr hfix hd
  rw [← hJ] at hμ
  obtain ⟨ρ, hρ, hesc⟩ := escape_of_unstable hfix' hd' hμ hre
  refine ⟨min ρ r, lt_min hρ hr, fun δ hδ => ?_⟩
  obtain ⟨x0, hx0, hall⟩ := hesc δ hδ
  obtain ⟨θ, hθ, hθ0⟩ := fwdComplete_tMod hr.le hL x0
  obtain ⟨τ, hτ, hτρ⟩ := hall θ hθ hθ0
  obtain ⟨s, hs0, -, hsε, hbefore⟩ := exists_first_exit hτ
    (hθ.1.mono Set.Icc_subset_Ici_self) (le_trans (min_le_left _ _) hτρ)
  exact ⟨s, hs0, θ, isSolOn_of_isFwdSol_tMod hθ
    (fun t ht => (hbefore t ht).le.trans (min_le_right _ _)), by rwa [hθ0], hsε⟩

/-- Woodford (2003), pp. 264–266: **an eigenvalue of `DT − I` with positive real part makes the
rest point unstable**: under the hypotheses of `unstable_loc`, `θ̄` is not a (textbook) locally
stable rest point of (2.20). -/
theorem not_isLASLoc_of_unstable [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ}
    {K : ℝ≥0} (hr : 0 < r) (hL : LipschitzOnWith K T (Metric.closedBall θs r))
    (hfix : T θs = θs) (hd : DifferentiableAt ℝ T θs) {μ : ℂ}
    (hμ : IsEig ((jac T θs - 1).map Complex.ofReal) μ) (hre : 0 < μ.re) : ¬IsLASLoc T θs := by
  intro h
  obtain ⟨ε, hε, hun⟩ := unstable_loc hr hL hfix hd hμ hre
  obtain ⟨δ, hδ, hst⟩ := h.1 ε hε
  obtain ⟨t₁, ht₁, θ, hθ, h0, hesc⟩ := hun δ hδ
  exact absurd (hst t₁ θ hθ h0 t₁ ⟨ht₁, le_rfl⟩) (not_lt.mpr hesc)

/-- Woodford (2003), pp. 264–266: **instability for forward-complete equations**: if every initial
belief has a forward solution on `[0, ∞)`, `T(θ̄) = θ̄`, `T` is differentiable at `θ̄` and
`DT(θ̄) − I` has an eigenvalue with positive real part, then arbitrarily close to `θ̄` start
forward solutions that reach a fixed distance `ε` from `θ̄` (no Lipschitz condition needed). -/
theorem unstable_of_fwdComplete [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ}
    (hc : FwdComplete T) (hfix : T θs = θs) (hd : DifferentiableAt ℝ T θs) {μ : ℂ}
    (hμ : IsEig ((jac T θs - 1).map Complex.ofReal) μ) (hre : 0 < μ.re) :
    ∃ ε > 0, ∀ δ > 0, ∃ θ : ℝ → ι → ℝ, IsFwdSol T θ ∧ ‖θ 0 - θs‖ < δ ∧
      ∃ τ : ℝ, 0 ≤ τ ∧ ε ≤ ‖θ τ - θs‖ := by
  obtain ⟨ρ, hρ, hesc⟩ := escape_of_unstable hfix hd hμ hre
  refine ⟨ρ, hρ, fun δ hδ => ?_⟩
  obtain ⟨x0, hx0, hall⟩ := hesc δ hδ
  obtain ⟨θ, hθ, hθ0⟩ := hc x0
  exact ⟨θ, hθ, by rwa [hθ0], hall θ hθ hθ0⟩

/-- Woodford (2003), pp. 264–266: for a forward-complete equation, an eigenvalue of `DT − I`
with positive real part means `θ̄` is not a locally asymptotically stable rest point (`IsLAS`). -/
theorem not_isLAS_of_unstable [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ}
    (hc : FwdComplete T) (hfix : T θs = θs) (hd : DifferentiableAt ℝ T θs) {μ : ℂ}
    (hμ : IsEig ((jac T θs - 1).map Complex.ofReal) μ) (hre : 0 < μ.re) : ¬IsLAS T θs := by
  intro h
  obtain ⟨ε, hε, hun⟩ := unstable_of_fwdComplete hc hfix hd hμ hre
  obtain ⟨δ, hδ, hst⟩ := h.1 ε hε
  obtain ⟨θ, hθ, h0, τ, hτ, hesc⟩ := hun δ hδ
  exact absurd (hst θ hθ h0 τ hτ) (not_lt.mpr hesc)

/-! ### The stability half in the textbook sense -/

/-- Woodford (2003), pp. 264–266: **E-stability implies local asymptotic stability in the
textbook sense** (solutions on finite intervals included), for `T` Lipschitz near `θ̄`. A solution
on `[0, t₁]` that left the `ε`-ball would, up to its first exit, also solve the modified equation
`T ∘ clampBox`; continued by a forward solution of that equation it would contradict the Lyapunov
stability given by `TidyR5Lyapunov.isLAS_of_eStableAt`. -/
theorem isLASLoc_of_eStableAt [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ}
    {K : ℝ≥0} (hr : 0 < r) (hL : LipschitzOnWith K T (Metric.closedBall θs r))
    (h : EStableAt T θs) : IsLASLoc T θs := by
  obtain ⟨hfix', hd', hJ⟩ := tMod_local hr h.1 h.2.1
  have hE' : EStableAt (tMod T θs r) θs := ⟨hfix', hd', by rw [← jac, hJ]; exact h.2.2⟩
  have hT' := isLAS_of_eStableAt hE'
  refine ⟨fun ε hε => ?_, (isLAS_of_eStableAt h).2⟩
  set ε' := min ε r with hε'
  have hε'0 : 0 < ε' := lt_min hε hr
  obtain ⟨δ, hδ, hstab⟩ := hT'.1 ε' hε'0
  refine ⟨min δ ε', lt_min hδ hε'0, fun t₁ θ hθ h0 τ hτ => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs0, hsτ, hsε, hbefore⟩ := exists_first_exit hτ.1
    (hθ.1.mono (Set.Icc_subset_Icc_right hτ.2)) (le_trans (min_le_left _ _) hcon)
  have hin : ∀ t ∈ Set.Ico 0 s, ‖θ t - θs‖ ≤ r :=
    fun t ht => (hbefore t ht).le.trans (min_le_right _ _)
  have h1 : IsSolOn (tMod T θs r) θ s :=
    isSolOn_tMod_of_isSolOn (isSolOn_mono hθ (le_trans hsτ hτ.2)) hin
  obtain ⟨θ₂, hθ₂, hθ₂0⟩ := fwdComplete_tMod hr.le hL (θ s)
  have hg := isFwdSol_glue h1 hθ₂ hθ₂0
  have hg0 : glue θ θ₂ s 0 = θ 0 := by simp [glue, hs0]
  have hgs : glue θ θ₂ s s = θ s := by simp [glue]
  have := hstab _ hg (by rw [hg0]; exact lt_of_lt_of_le h0 (min_le_left _ _)) s hs0
  rw [hgs] at this
  exact absurd this (not_lt.mpr hsε)

/-! ### The textbook notion and the modified equation -/

/-- Woodford (2003), (2.20): a forward solution of the modified equation `T ∘ clampBox` that
stays in the closed ball of radius `r` is a forward solution of the original equation. -/
theorem isFwdSol_of_isFwdSol_tMod {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ}
    {θ : ℝ → ι → ℝ} (h : IsFwdSol (tMod T θs r) θ) (hin : ∀ t, 0 ≤ t → ‖θ t - θs‖ ≤ r) :
    IsFwdSol T θ := by
  refine ⟨h.1, fun τ hτ => ?_⟩
  have hd := h.2 τ hτ
  rwa [tMod_of_le T θs (hin τ hτ)] at hd

/-- Woodford (2003), (2.20): a forward solution of the original equation that stays in the
closed ball of radius `r` is a forward solution of the modified equation. -/
theorem isFwdSol_tMod_of_isFwdSol {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ}
    {θ : ℝ → ι → ℝ} (h : IsFwdSol T θ) (hin : ∀ t, 0 ≤ t → ‖θ t - θs‖ ≤ r) :
    IsFwdSol (tMod T θs r) θ := by
  refine ⟨h.1, fun τ hτ => ?_⟩
  rw [tMod_of_le T θs (hin τ hτ)]
  exact h.2 τ hτ

/-- Woodford (2003), p. 264: if `θ̄` is a locally asymptotically stable rest point of (2.20) in
the textbook sense, it is one in the sense of `IsLAS` for the globally Lipschitz modification
`T ∘ clampBox` (a forward solution of the modification that left the ball would, up to its first
exit, solve the original equation). -/
theorem isLAS_tMod_of_isLASLoc {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ} (hr : 0 < r)
    (h : IsLASLoc T θs) : IsLAS (tMod T θs r) θs := by
  have hly : ∀ ε > 0, ∃ δ > 0, ∀ θ, IsFwdSol (tMod T θs r) θ → ‖θ 0 - θs‖ < δ →
      ∀ τ : ℝ, 0 ≤ τ → ‖θ τ - θs‖ < ε := by
    intro ε hε
    set ε' := min ε r with hε'
    have hε'0 : 0 < ε' := lt_min hε hr
    obtain ⟨δ, hδ, hst⟩ := h.1 ε' hε'0
    refine ⟨δ, hδ, fun θ hθ h0 τ hτ => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs0, -, hsε, hbefore⟩ := exists_first_exit hτ
      (hθ.1.mono Set.Icc_subset_Ici_self) (le_trans (min_le_left _ _) hcon)
    have h1 : IsSolOn T θ s := isSolOn_of_isFwdSol_tMod hθ
      (fun t ht => (hbefore t ht).le.trans (min_le_right _ _))
    exact absurd (hst s θ h1 h0 s ⟨hs0, le_rfl⟩) (not_lt.mpr hsε)
  refine ⟨hly, ?_⟩
  obtain ⟨δ₁, hδ₁, hst⟩ := hly r hr
  obtain ⟨δ₂, hδ₂, hat⟩ := h.2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun θ hθ h0 => ?_⟩
  have hin : ∀ t, 0 ≤ t → ‖θ t - θs‖ ≤ r :=
    fun t ht => (hst θ hθ (lt_of_lt_of_le h0 (min_le_left _ _)) t ht).le
  exact hat θ (isFwdSol_of_isFwdSol_tMod hθ hin) (lt_of_lt_of_le h0 (min_le_right _ _))

/-- Woodford (2003), p. 264: conversely, if `T` is Lipschitz on the closed ball and `θ̄` is a
locally asymptotically stable rest point (`IsLAS`) of the modified equation `T ∘ clampBox`, it is
one of the original equation in the textbook sense. -/
theorem isLASLoc_of_isLAS_tMod {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ} {K : ℝ≥0}
    (hr : 0 < r) (hL : LipschitzOnWith K T (Metric.closedBall θs r))
    (h : IsLAS (tMod T θs r) θs) : IsLASLoc T θs := by
  have hly : ∀ ε > 0, ∃ δ > 0, ∀ (t₁ : ℝ) (θ : ℝ → ι → ℝ), IsSolOn T θ t₁ → ‖θ 0 - θs‖ < δ →
      ∀ τ ∈ Set.Icc 0 t₁, ‖θ τ - θs‖ < ε := by
    intro ε hε
    set ε' := min ε r with hε'
    have hε'0 : 0 < ε' := lt_min hε hr
    obtain ⟨δ, hδ, hstab⟩ := h.1 ε' hε'0
    refine ⟨min δ ε', lt_min hδ hε'0, fun t₁ θ hθ h0 τ hτ => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨s, hs0, hsτ, hsε, hbefore⟩ := exists_first_exit hτ.1
      (hθ.1.mono (Set.Icc_subset_Icc_right hτ.2)) (le_trans (min_le_left _ _) hcon)
    have hin : ∀ t ∈ Set.Ico 0 s, ‖θ t - θs‖ ≤ r :=
      fun t ht => (hbefore t ht).le.trans (min_le_right _ _)
    have h1 : IsSolOn (tMod T θs r) θ s :=
      isSolOn_tMod_of_isSolOn (isSolOn_mono hθ (le_trans hsτ hτ.2)) hin
    obtain ⟨θ₂, hθ₂, hθ₂0⟩ := fwdComplete_tMod hr.le hL (θ s)
    have hg := isFwdSol_glue h1 hθ₂ hθ₂0
    have hg0 : glue θ θ₂ s 0 = θ 0 := by simp [glue, hs0]
    have hgs : glue θ θ₂ s s = θ s := by simp [glue]
    have := hstab _ hg (by rw [hg0]; exact lt_of_lt_of_le h0 (min_le_left _ _)) s hs0
    rw [hgs] at this
    exact absurd this (not_lt.mpr hsε)
  refine ⟨hly, ?_⟩
  obtain ⟨δ₁, hδ₁, hst⟩ := hly r hr
  obtain ⟨δ₂, hδ₂, hat⟩ := h.2
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun θ hθ h0 => ?_⟩
  have hin : ∀ t, 0 ≤ t → ‖θ t - θs‖ ≤ r := fun t ht =>
    (hst t θ (isSolOn_of_isFwdSol hθ t) (lt_of_lt_of_le h0 (min_le_left _ _)) t
      ⟨ht, le_rfl⟩).le
  exact hat θ (isFwdSol_tMod_of_isFwdSol hθ hin) (lt_of_lt_of_le h0 (min_le_right _ _))

/-- Woodford (2003), p. 264: for `T` Lipschitz on a closed ball around `θ̄`, the textbook notion
of a locally asymptotically stable rest point of (2.20) coincides with `IsLAS` for the globally
Lipschitz (hence forward-complete) modification `T ∘ clampBox`. -/
theorem isLAS_tMod_iff {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ} {K : ℝ≥0} (hr : 0 < r)
    (hL : LipschitzOnWith K T (Metric.closedBall θs r)) :
    IsLAS (tMod T θs r) θs ↔ IsLASLoc T θs :=
  ⟨isLASLoc_of_isLAS_tMod hr hL, isLAS_tMod_of_isLASLoc hr⟩

/-! ### The exact equivalences -/

/-- Woodford (2003), p. 266 and n. 37: **Lyapunov's indirect method for (2.20), both halves**:
for `T` Lipschitz on a closed ball around a rest point `θ̄` and differentiable at `θ̄`, when no
eigenvalue of `DT(θ̄) − I` has zero real part, `θ̄` is E-stable iff it is a locally asymptotically
stable rest point of `θ̇ = T(θ) − θ` (textbook sense). -/
theorem eStableAt_iff_isLASLoc [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ} {r : ℝ}
    {K : ℝ≥0} (hr : 0 < r) (hL : LipschitzOnWith K T (Metric.closedBall θs r))
    (hfix : T θs = θs) (hd : DifferentiableAt ℝ T θs) (hnz : NoZeroRe (jac T θs)) :
    EStableAt T θs ↔ IsLASLoc T θs := by
  refine ⟨isLASLoc_of_eStableAt hr hL, fun h => ?_⟩
  by_contra hE
  have hJ : ¬EStable (jac T θs) := fun hJ => hE ⟨hfix, hd, hJ⟩
  obtain ⟨μ, hμ, hre⟩ := exists_pos_eig_of_not_eStable hJ hnz
  exact not_isLASLoc_of_unstable hr hL hfix hd hμ hre h

/-- Woodford (2003), p. 266 and n. 37: **the equivalence for solutions on `[0, ∞)`**: if the
equation is forward complete, `T(θ̄) = θ̄`, `T` is differentiable at `θ̄` and no eigenvalue of
`DT(θ̄) − I` has zero real part, then `θ̄` is E-stable iff it is a locally asymptotically stable
rest point in the sense of `IsLAS`. -/
theorem eStableAt_iff_isLAS [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ}
    (hc : FwdComplete T) (hfix : T θs = θs) (hd : DifferentiableAt ℝ T θs)
    (hnz : NoZeroRe (jac T θs)) : EStableAt T θs ↔ IsLAS T θs := by
  refine ⟨isLAS_of_eStableAt, fun h => ?_⟩
  by_contra hE
  have hJ : ¬EStable (jac T θs) := fun hJ => hE ⟨hfix, hd, hJ⟩
  obtain ⟨μ, hμ, hre⟩ := exists_pos_eig_of_not_eStable hJ hnz
  exact not_isLAS_of_unstable hc hfix hd hμ hre h

/-- Woodford (2003), p. 266 and n. 37: for a **globally Lipschitz** `T` (forward complete by
Picard–Lindelöf and continuation), differentiable at a rest point `θ̄` with no eigenvalue of
`DT(θ̄) − I` on the imaginary axis, E-stability ⟺ `IsLAS` ⟺ `IsLASLoc`. -/
theorem eStableAt_iff_of_lipschitz [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ}
    {K : ℝ≥0} (hL : LipschitzWith K T) (hfix : T θs = θs) (hd : DifferentiableAt ℝ T θs)
    (hnz : NoZeroRe (jac T θs)) :
    (EStableAt T θs ↔ IsLAS T θs) ∧ (EStableAt T θs ↔ IsLASLoc T θs) :=
  ⟨eStableAt_iff_isLAS (fwdComplete_of_lipschitz hL) hfix hd hnz,
    eStableAt_iff_isLASLoc one_pos hL.lipschitzOnWith hfix hd hnz⟩

/-- Woodford (2003), p. 266: a map that is `C¹` at `θ̄` is Lipschitz on a closed ball around
`θ̄` and differentiable at `θ̄`. -/
theorem lipschitz_of_contDiffAt {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ}
    (hT : ContDiffAt ℝ 1 T θs) :
    ∃ r > 0, ∃ K : ℝ≥0, LipschitzOnWith K T (Metric.closedBall θs r) := by
  obtain ⟨K, t, ht, hK⟩ := hT.exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  exact ⟨ε / 2, by positivity, K,
    hK.mono ((Metric.closedBall_subset_ball (by linarith)).trans hball)⟩

/-- Woodford (2003), p. 266 and n. 37: **Lyapunov's indirect method for `C¹` maps**: if `T` is
`C¹` at a rest point `θ̄` and no eigenvalue of `DT(θ̄) − I` has zero real part, `θ̄` is E-stable
iff it is a locally asymptotically stable rest point of (2.20) (textbook sense); and an
eigenvalue with positive real part makes `θ̄` unstable. -/
theorem eStableAt_iff_isLASLoc_of_contDiffAt [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ}
    {θs : ι → ℝ} (hT : ContDiffAt ℝ 1 T θs) (hfix : T θs = θs) (hnz : NoZeroRe (jac T θs)) :
    EStableAt T θs ↔ IsLASLoc T θs := by
  obtain ⟨r, hr, K, hL⟩ := lipschitz_of_contDiffAt hT
  exact eStableAt_iff_isLASLoc hr hL hfix (hT.differentiableAt one_ne_zero) hnz

/-- Woodford (2003), pp. 264–266: **instability for `C¹` maps**: if `T` is `C¹` at a rest point
`θ̄` and `DT(θ̄) − I` has an eigenvalue with positive real part, `θ̄` is not a locally stable rest
point of (2.20) (no genericity assumption needed for this half). -/
theorem not_isLASLoc_of_contDiffAt [DecidableEq ι] {T : (ι → ℝ) → ι → ℝ} {θs : ι → ℝ}
    (hT : ContDiffAt ℝ 1 T θs) (hfix : T θs = θs) {μ : ℂ}
    (hμ : IsEig ((jac T θs - 1).map Complex.ofReal) μ) (hre : 0 < μ.re) : ¬IsLASLoc T θs := by
  obtain ⟨r, hr, K, hL⟩ := lipschitz_of_contDiffAt hT
  exact not_isLASLoc_of_unstable hr hL hfix (hT.differentiableAt one_ne_zero) hμ hre

end Woodford.NeoWicksellianFramework.TidyR6Instability
