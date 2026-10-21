/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LocalIFTSystems

/-!
# Local determinacy at an arbitrary steady state `x̄`

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 631–633: the conditions (A.7)
`G(p_{t−1}, p_t, p_{t+1}; u_t) = 0` in levels, with a steady state `p̄`,
`G(p̄, p̄, p̄; 0) = 0`. `LocalIFTSystems` works in deviations (`F(0) = 0`); this module states the
theorems for an arbitrary `x̄` by translation, `F = shiftF G x̄`,
`F(a, b, c, e) = G(a + x̄, b + x̄, c + x̄, e)`, whose derivative at `0` is that of `G` at the steady
state (`fderiv_shiftF`), so the root condition is on `f_j = D_jG(x̄, x̄, x̄, 0)`.

* `solves_shift_iff`: `x` solves the level conditions with initial condition `x_{−1}` iff
  `x − x̄` solves the deviation conditions with initial condition `x_{−1} − x̄`.
* `local_determinacy_at`: for `(x_{−1}, e)` near `(x̄, 0)` there is a unique equilibrium within
  `ε` of the steady state path, `C¹` in `(x_{−1}, e)`, with derivative the solution of (A.10).
* `isUnit_iff_local_determinacy_at`: the converse (disturbances moving every equation).
* `second_order_at`: the `O(‖(x_{−1} − x̄, e)‖²)` bound for `C²` conditions (E18).
-/

namespace Woodford.PriceLevelDetermination.LocalIFTSystemsBar

open scoped Topology
open LinearSystems LocalIFTSystems

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Woodford (2003), App. A.3, p. 631: the steady-state argument `(x̄, x̄, x̄, 0)`. -/
def ssArg (E : Type*) [NormedAddCommGroup E] (xbar : ι → ℝ) : Arg ι E := (xbar, xbar, xbar, 0)

/-- Woodford (2003), App. A.3, p. 631, fn. 3: the parameters at the steady state,
`x_{−1} = x̄` and no disturbances. -/
noncomputable def ssPar (E : Type*) [NormedAddCommGroup E] (xbar : ι → ℝ) : Par ι E := (xbar, 0)

/-- Woodford (2003), App. A.3, p. 631: the steady-state path `x_t = x̄`. -/
noncomputable def constSeq (xbar : ι → ℝ) : SeqV ι :=
  LocalIFT.mkS (fun _ => xbar) ⟨‖xbar‖, fun _ => le_rfl⟩

/-- Woodford (2003), App. A.3, p. 632: the conditions in deviations from the steady state,
`F(a, b, c, e) = G(a + x̄, b + x̄, c + x̄, e)`. -/
def shiftF (G : Arg ι E → (ι → ℝ)) (xbar : ι → ℝ) : Arg ι E → (ι → ℝ) :=
  fun p => G (p + ssArg E xbar)

omit [Fintype ι] [DecidableEq ι] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 631: the steady state of `G` is the zero of `shiftF G x̄`. -/
theorem shiftF_zero {G : Arg ι E → (ι → ℝ)} {xbar : ι → ℝ} (h0 : G (ssArg E xbar) = 0) :
    shiftF G xbar 0 = 0 := by
  rw [shiftF, zero_add, h0]

omit [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 632: smoothness at the steady state transfers to the deviation
form. -/
theorem contDiffAt_shiftF {G : Arg ι E → (ι → ℝ)} {xbar : ι → ℝ} {k : ℕ}
    (hG : ContDiffAt ℝ k G (ssArg E xbar)) : ContDiffAt ℝ k (shiftF G xbar) 0 := by
  have ht : ContDiffAt ℝ k (fun p : Arg ι E => p + ssArg E xbar) 0 :=
    contDiffAt_id.add contDiffAt_const
  have hG' : ContDiffAt ℝ k G ((fun p : Arg ι E => p + ssArg E xbar) 0) := by
    simpa using hG
  exact hG'.comp 0 ht

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, eq. (A.8), p. 632: the derivative of the deviation form at `0`
is `DG(x̄, x̄, x̄, 0)`, so `f_j = D_jG` at the steady state. -/
theorem fderiv_shiftF [Finite ι] (G : Arg ι E → (ι → ℝ)) (xbar : ι → ℝ) :
    fderiv ℝ (shiftF G xbar) 0 = fderiv ℝ G (ssArg E xbar) := by
  have := Fintype.ofFinite ι
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := G) (x := (0 : Arg ι E)) (ssArg E xbar)
  rwa [zero_add] at h

omit [DecidableEq ι] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Woodford (2003), App. A.3, p. 631: `x` solves the level conditions with parameters `u`
iff `x − x̄` solves the deviation conditions with parameters `u − (x̄, 0)`. -/
theorem solves_shift_iff (G : Arg ι E → (ι → ℝ)) (xbar : ι → ℝ) (u : Par ι E) (x : SeqV ι) :
    Solves G u x ↔ Solves (shiftF G xbar) (u - ssPar E xbar) (x - constSeq xbar) := by
  refine forall_congr' fun t => ?_
  have e : ((lagV (u - ssPar E xbar).1 (fun s => (x - constSeq xbar) s) t,
      (x - constSeq xbar) t, (x - constSeq xbar) (t + 1), (u - ssPar E xbar).2 t) : Arg ι E) +
      ssArg E xbar = (lagV u.1 (fun s => x s) t, x t, x (t + 1), u.2 t) := by
    cases t <;> simp [ssArg, ssPar, constSeq]
  rw [shiftF, e]

/-- **Local determinacy at an arbitrary steady state** (Woodford (2003), App. A.3, pp. 632–633):
if `G` is `C¹` near `(x̄, x̄, x̄, 0)`, `G(x̄, x̄, x̄, 0) = 0` and the operator (A.8) built from
`f_j = D_jG(x̄, x̄, x̄, 0)` is invertible (the root condition, `LocalIFTSystems.isUnit_linOp_iff`
applied to `shiftF G x̄`), then for every `(x_{−1}, e)` within `δ` of `(x̄, 0)` there is an
equilibrium `X(x_{−1}, e)` within `ε/2` of the steady-state path, it is the only equilibrium
within `ε` of that path, `X` is `C¹`, `X(x̄, 0) = x̄`, and its derivative at `(x̄, 0)` is the
solution operator of the linearised system (A.10). -/
theorem local_determinacy_at {G : Arg ι E → (ι → ℝ)} {xbar : ι → ℝ}
    (hG : ContDiffAt ℝ 1 G (ssArg E xbar)) (h0 : G (ssArg E xbar) = 0)
    (hL : IsUnit (linOp (shiftF G xbar))) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ X : Par ι E → SeqV ι, X (ssPar E xbar) = constSeq xbar ∧
      HasFDerivAt X (linSol (shiftF G xbar)) (ssPar E xbar) ∧
      ∀ u : Par ι E, ‖u - ssPar E xbar‖ < δ → ‖X u - constSeq xbar‖ < ε / 2 ∧ Solves G u (X u) ∧
        ContDiffAt ℝ 1 X u ∧
        ∀ x : SeqV ι, ‖x - constSeq xbar‖ < ε → Solves G u x → x = X u := by
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, X₀, hX0, hXd, hX⟩ :=
    local_determinacy (contDiffAt_shiftF hG) (shiftF_zero h0) hL hη
  set ub := ssPar E xbar with hub
  set c := constSeq xbar with hc
  refine ⟨ε, hε, hεη, δ, hδ, hδη, fun u => c + X₀ (u - ub), by simp [hX0], ?_, fun u hu => ?_⟩
  · have hs : HasFDerivAt (fun u : Par ι E => u - ub) (ContinuousLinearMap.id ℝ (Par ι E)) ub :=
      (hasFDerivAt_id ub).sub_const ub
    have hXd' : HasFDerivAt X₀ (linSol (shiftF G xbar)) (ub - ub) := by
      rw [sub_self]
      exact hXd
    have h2 := (HasFDerivAt.comp (f := fun u : Par ι E => u - ub) ub hXd' hs).const_add c
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  · obtain ⟨hn, hsol, hcd, huniq⟩ := hX (u - ub) hu
    refine ⟨by simpa using hn, ?_, ?_, fun x hx hsx => ?_⟩
    · rw [solves_shift_iff G xbar, ← hub, ← hc, add_sub_cancel_left]
      exact hsol
    · exact contDiffAt_const.add (hcd.comp u (contDiffAt_id.sub contDiffAt_const))
    · have := huniq (x - c) hx ((solves_shift_iff G xbar u x).mp hsx)
      change x = c + X₀ (u - ub)
      rw [← this, add_sub_cancel]

/-- **The converse at an arbitrary steady state** (Woodford (2003), App. A.3, pp. 632–633): if
the disturbances move every equation (`D₄G` onto at the steady state), the level system is
locally determinate around `x̄` with a solution map differentiable at `(x̄, 0)` **iff** the
operator (A.8) built from `D_jG(x̄, x̄, x̄, 0)` is invertible, i.e. iff the root condition holds. -/
theorem isUnit_iff_local_determinacy_at {G : Arg ι E → (ι → ℝ)} {xbar : ι → ℝ}
    (hG : ContDiffAt ℝ 1 G (ssArg E xbar)) (h0 : G (ssArg E xbar) = 0)
    (hE : Function.Surjective (dE (shiftF G xbar))) :
    IsUnit (linOp (shiftF G xbar)) ↔ ∃ ε > 0, ∃ δ > 0, ∃ X : Par ι E → SeqV ι,
      X (ssPar E xbar) = constSeq xbar ∧ DifferentiableAt ℝ X (ssPar E xbar) ∧
      ∀ u : Par ι E, ‖u - ssPar E xbar‖ < δ → Solves G u (X u) ∧
        ∀ x : SeqV ι, ‖x - constSeq xbar‖ < ε → Solves G u x → x = X u := by
  rw [isUnit_linOp_iff_local_determinacy (contDiffAt_shiftF hG) (shiftF_zero h0) hE]
  set ub := ssPar E xbar with hub
  set c := constSeq xbar with hc
  constructor
  · rintro ⟨ε, hε, δ, hδ, X₀, hX0, hXd, hX⟩
    refine ⟨ε, hε, δ, hδ, fun u => c + X₀ (u - ub), by simp [hX0], ?_, fun u hu => ?_⟩
    · have hXd' : DifferentiableAt ℝ X₀ (ub - ub) := by
        rw [sub_self]
        exact hXd
      exact (DifferentiableAt.comp (f := fun u : Par ι E => u - ub) ub hXd'
        (differentiableAt_id.sub_const ub)).const_add c
    · obtain ⟨hsol, huniq⟩ := hX (u - ub) hu
      refine ⟨?_, fun x hx hsx => ?_⟩
      · rw [solves_shift_iff G xbar, ← hub, ← hc, add_sub_cancel_left]
        exact hsol
      · have := huniq (x - c) hx ((solves_shift_iff G xbar u x).mp hsx)
        change x = c + X₀ (u - ub)
        rw [← this, add_sub_cancel]
  · rintro ⟨ε, hε, δ, hδ, X, hX0, hXd, hX⟩
    refine ⟨ε, hε, δ, hδ, fun v => X (v + ub) - c, by simp [hX0], ?_, fun v hv => ?_⟩
    · have hXd' : DifferentiableAt ℝ X (0 + ub) := by
        rw [zero_add]
        exact hXd
      exact (DifferentiableAt.comp (f := fun v : Par ι E => v + ub) 0 hXd'
        (differentiableAt_id.add_const ub)).sub_const c
    · have hu : ‖(v + ub) - ub‖ < δ := by rwa [add_sub_cancel_right]
      obtain ⟨hsol, huniq⟩ := hX (v + ub) hu
      refine ⟨?_, fun x hx hsx => ?_⟩
      · have := (solves_shift_iff G xbar (v + ub) _).mp hsol
        rwa [add_sub_cancel_right] at this
      · have hs : Solves G (v + ub) (x + c) := by
          rw [solves_shift_iff G xbar, add_sub_cancel_right, ← hc, add_sub_cancel_right]
          exact hsx
        have := huniq (x + c) (by rwa [add_sub_cancel_right]) hs
        change x = X (v + ub) - c
        rw [← this, add_sub_cancel_right]

/-- Woodford (2003), App. A.3, p. 633, corrected per E18, **at an arbitrary steady state**: if
`G` is `C²` near `(x̄, x̄, x̄, 0)` and (A.8) is invertible, every equilibrium within `ε` of the
steady-state path differs from `x̄ + x̂(x_{−1} − x̄, e)` (`x̂` the solution of (A.10)) by at most
`C ‖(x_{−1} − x̄, e)‖²`. -/
theorem second_order_at {G : Arg ι E → (ι → ℝ)} {xbar : ι → ℝ}
    (hG : ContDiffAt ℝ 2 G (ssArg E xbar)) (h0 : G (ssArg E xbar) = 0)
    (hL : IsUnit (linOp (shiftF G xbar))) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ε ≤ η ∧ ∃ δ > 0, δ ≤ η ∧ ∃ C : ℝ, ∀ u : Par ι E, ‖u - ssPar E xbar‖ < δ →
      ∀ x : SeqV ι, ‖x - constSeq xbar‖ < ε → Solves G u x →
        ‖x - (constSeq xbar + linSol (shiftF G xbar) (u - ssPar E xbar))‖ ≤
          C * ‖u - ssPar E xbar‖ ^ 2 := by
  obtain ⟨ε, hε, hεη, δ, hδ, hδη, C, hC⟩ :=
    second_order_loc (contDiffAt_shiftF hG) (shiftF_zero h0) hL hη
  refine ⟨ε, hε, hεη, δ, hδ, hδη, C, fun u hu x hx hsx => ?_⟩
  rw [← sub_sub]
  exact hC _ hu _ hx ((solves_shift_iff G xbar u x).mp hsx)

end Woodford.PriceLevelDetermination.LocalIFTSystemsBar
