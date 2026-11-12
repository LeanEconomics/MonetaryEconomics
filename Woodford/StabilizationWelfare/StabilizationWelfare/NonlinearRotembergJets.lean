/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergLinks

/-!
# Second-order jets at zero

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392: second-order approximations
of welfare along one-parameter families). A small calculus of second-order jets at `0`:
`J2 f v₁ v₂` says that `f` is differentiable near `0` with a derivative that is differentiable at
`0`, with `f′(0) = v₁` and `f″(0) = v₂`. It is closed under sums, scalar multiples, products and
composition with functions twice differentiable at the inner value (`J2_comp`), which is what the
welfare computations of `NonlinearRotembergTrendWelfare` need.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergJets

open Filter Topology

/-- Woodford (2003), Ch. 6, §1: `f′(0) = v₁` and `f″(0) = v₂`, through a derivative function
defined near `0` and differentiable at `0`. -/
def J2 (f : ℝ → ℝ) (v1 v2 : ℝ) : Prop :=
  ∃ f1 : ℝ → ℝ, (∀ᶠ x in 𝓝 0, HasDerivAt f (f1 x) x) ∧ HasDerivAt f1 v2 0 ∧ f1 0 = v1

/-- A jet gives the first and second derivatives at `0`. -/
theorem J2_deriv {f : ℝ → ℝ} {v1 v2 : ℝ} (h : J2 f v1 v2) :
    deriv f 0 = v1 ∧ deriv (deriv f) 0 = v2 := by
  obtain ⟨f1, hf, hf1, h0⟩ := h
  have he : deriv f =ᶠ[𝓝 0] f1 := hf.mono fun x hx => hx.deriv
  refine ⟨by rw [he.eq_of_nhds, h0], ?_⟩
  rw [he.deriv_eq]; exact hf1.deriv

/-- A jet gives continuity at `0`. -/
theorem J2_continuousAt {f : ℝ → ℝ} {v1 v2 : ℝ} (h : J2 f v1 v2) : ContinuousAt f 0 := by
  obtain ⟨f1, hf, -, -⟩ := h
  exact hf.self_of_nhds.continuousAt

/-- The jet of `x ↦ x`. -/
theorem J2_id : J2 (fun x => x) 1 0 :=
  ⟨fun _ => 1, Eventually.of_forall fun x => hasDerivAt_id' x, hasDerivAt_const _ _, rfl⟩

/-- The jet of a constant. -/
theorem J2_const (c : ℝ) : J2 (fun _ => c) 0 0 :=
  ⟨fun _ => 0, Eventually.of_forall fun x => hasDerivAt_const x c, hasDerivAt_const _ _, rfl⟩

/-- Jets add. -/
theorem J2_add {f g : ℝ → ℝ} {a1 a2 b1 b2 : ℝ} (hf : J2 f a1 a2) (hg : J2 g b1 b2) :
    J2 (fun x => f x + g x) (a1 + b1) (a2 + b2) := by
  obtain ⟨f1, hf, hf1, h0⟩ := hf
  obtain ⟨g1, hg, hg1, k0⟩ := hg
  exact ⟨fun x => f1 x + g1 x, (hf.and hg).mono fun x h => h.1.add h.2, hf1.add hg1,
    by simp [h0, k0]⟩

/-- Jets subtract. -/
theorem J2_sub {f g : ℝ → ℝ} {a1 a2 b1 b2 : ℝ} (hf : J2 f a1 a2) (hg : J2 g b1 b2) :
    J2 (fun x => f x - g x) (a1 - b1) (a2 - b2) := by
  obtain ⟨f1, hf, hf1, h0⟩ := hf
  obtain ⟨g1, hg, hg1, k0⟩ := hg
  exact ⟨fun x => f1 x - g1 x, (hf.and hg).mono fun x h => h.1.sub h.2, hf1.sub hg1,
    by simp [h0, k0]⟩

/-- Jets scale. -/
theorem J2_const_mul (c : ℝ) {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) :
    J2 (fun x => c * f x) (c * a1) (c * a2) := by
  obtain ⟨f1, hf, hf1, h0⟩ := hf
  exact ⟨fun x => c * f1 x, hf.mono fun x h => h.const_mul c, hf1.const_mul c, by simp [h0]⟩

/-- Jets of products: `(fg)″ = f″g + 2f′g′ + fg″`. -/
theorem J2_mul {f g : ℝ → ℝ} {a1 a2 b1 b2 : ℝ} (hf : J2 f a1 a2) (hg : J2 g b1 b2) :
    J2 (fun x => f x * g x) (a1 * g 0 + f 0 * b1) (a2 * g 0 + 2 * a1 * b1 + f 0 * b2) := by
  obtain ⟨f1, hf, hf1, h0⟩ := hf
  obtain ⟨g1, hg, hg1, k0⟩ := hg
  have hfd := hf.self_of_nhds
  have hgd := hg.self_of_nhds
  refine ⟨fun x => f1 x * g x + f x * g1 x, (hf.and hg).mono fun x h => h.1.mul h.2, ?_,
    by simp [h0, k0]⟩
  have := (hf1.mul hgd).add (hfd.mul hg1)
  refine this.congr_deriv ?_
  rw [h0, k0]; ring

/-- Jets of compositions: if `F′ = F₁` near `f(0)` and `F₁′(f 0) = c`, then
`(F∘f)′(0) = F₁(f 0)f′(0)` and `(F∘f)″(0) = c f′(0)² + F₁(f 0) f″(0)`. -/
theorem J2_comp {F F1 f : ℝ → ℝ} {c a1 a2 : ℝ} (hF : ∀ᶠ y in 𝓝 (f 0), HasDerivAt F (F1 y) y)
    (hF1 : HasDerivAt F1 c (f 0)) (hf : J2 f a1 a2) :
    J2 (fun x => F (f x)) (F1 (f 0) * a1) (c * a1 * a1 + F1 (f 0) * a2) := by
  have hc := J2_continuousAt hf
  obtain ⟨f1, hfe, hf1, h0⟩ := hf
  have hFe : ∀ᶠ x in 𝓝 (0 : ℝ), HasDerivAt F (F1 (f x)) (f x) := hc.eventually hF
  refine ⟨fun x => F1 (f x) * f1 x, (hfe.and hFe).mono fun x h => ?_, ?_, by simp [h0]⟩
  · exact h.2.comp x h.1
  · have hfd := hfe.self_of_nhds
    have h1 : HasDerivAt (fun x => F1 (f x)) (c * f1 0) 0 := hF1.comp 0 hfd
    have := h1.mul hf1
    refine this.congr_deriv ?_
    rw [h0]

/-- The jet of `x ↦ e^{cx}`. -/
theorem J2_exp (c : ℝ) : J2 (fun x => Real.exp (c * x)) c (c * c) := by
  refine ⟨fun x => c * Real.exp (c * x), Eventually.of_forall fun x => ?_, ?_, by simp⟩
  · have := ((hasDerivAt_id' x).const_mul c).exp
    simpa [mul_comm] using this
  · have := (((hasDerivAt_id' (0 : ℝ)).const_mul c).exp).const_mul c
    simpa [mul_comm] using this

/-- The derivative of `log` near a positive point. -/
theorem log_deriv_near {y0 : ℝ} (hy : 0 < y0) :
    ∀ᶠ y in 𝓝 y0, HasDerivAt Real.log (y⁻¹) y :=
  (lt_mem_nhds hy).mono fun _ h => Real.hasDerivAt_log h.ne'

/-- The derivative of `y ↦ y⁻¹` at a positive point. -/
theorem inv_deriv {y0 : ℝ} (hy : 0 < y0) : HasDerivAt (fun y : ℝ => y⁻¹) (-(y0 ^ 2)⁻¹) y0 :=
  hasDerivAt_inv hy.ne'

/-- Jets of `log ∘ f` with `f 0 > 0`. -/
theorem J2_log {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) (h0 : 0 < f 0) :
    J2 (fun x => Real.log (f x)) ((f 0)⁻¹ * a1) (-(f 0 ^ 2)⁻¹ * a1 * a1 + (f 0)⁻¹ * a2) :=
  J2_comp (log_deriv_near h0) (inv_deriv h0) hf

/-- Jets of `exp ∘ f`. -/
theorem J2_expc {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) :
    J2 (fun x => Real.exp (f x)) (Real.exp (f 0) * a1)
      (Real.exp (f 0) * a1 * a1 + Real.exp (f 0) * a2) :=
  J2_comp (Eventually.of_forall fun y => Real.hasDerivAt_exp y) (Real.hasDerivAt_exp _) hf

/-- Jets transfer along pointwise equality. -/
theorem J2_congr {f g : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) (h : ∀ x, g x = f x) :
    J2 g a1 a2 := by
  have : g = f := funext h
  rwa [this]

/-- Jets transfer along equality of the values. -/
theorem J2_eq {f : ℝ → ℝ} {a1 a2 b1 b2 : ℝ} (hf : J2 f a1 a2) (h1 : a1 = b1) (h2 : a2 = b2) :
    J2 f b1 b2 := by
  rw [← h1, ← h2]; exact hf

end Woodford.StabilizationWelfare.NonlinearRotembergJets
