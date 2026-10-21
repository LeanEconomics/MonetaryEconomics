/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Production costs and the real marginal cost function

Woodford (2003), *Interest and Prices*, Chapter 3, §1.1, pp. 148–152: the production function
(1.7), nominal marginal cost (1.8), the function `Ψ` of (1.9), the real marginal cost function
(1.10), the yeoman-farmer equivalence (1.11), and the log-linearisation (1.15)–(1.16).

## Main results

* `Technology` (eq. (1.7)): a production function `f` with `f' > 0`, a bijection of `(0, ∞)`
  with inverse `f⁻¹`. `hasDerivAt_finv`: `(f⁻¹)' = Ψ`; `hasDerivAt_variableCost`: (1.8), the
  marginal cost of `w f⁻¹(y/A)` is `(w/A) Ψ(y/A)`; `Psi_pos`, `Psi_monotoneOn` (concave `f`),
  `Psi_strictMonoOn` (strictly concave `f`): (1.9).
* `rmc` (eq. (1.10)), `rmc_eq_real_wage_cost` ((1.8) with the labour supply (1.6) substituted),
  `rmc_strictMonoOn_y`, `rmc_strictMonoOn_Y`: `s` is increasing in both arguments;
  `yeoman_hasDerivAt`, `yeoman_rmc`: the yeoman-farmer marginal disutility `ṽ_y / u_c` equals
  (1.10) (p. 150).
* Elasticities at the steady state: `elasticity_rmc_y` (ω = ω_w + ω_p, eq. (1.16)),
  `elasticity_rmc_Y` (σ⁻¹), `elasticity_rmc_A` (`−(1 + ω)`); `omegaP_pos_iff`,
  `omegaW_pos_iff`, `sigmaInv_pos_iff`.
* `logRmcGap_differentiableAt`, `fderiv_logRmcGap` and `eq_1_15`: (1.15) as the EXACT
  Fréchet derivative of `log s` in `(log y, log Y, log A, ξ)` at the steady state, with the
  shock terms equal to `−(ω + σ⁻¹)` times the derivative of the (log) natural rate;
  `naturalRate_deriv`: `(ω + σ⁻¹) dŶⁿ = (1 + ω) a − (∂_ξ log s) ξ`.
* Imprecisions: the book's "`f` increasing, concave" and "`v` increasing, convex" give only
  `ω_p ≥ 0`, `ω_w ≥ 0`; the printed `ω_p > 0`, `ω_w > 0` and "`Ψ` increasing" need strict
  curvature at the steady state (`linearTech`, `linearTech_Psi`, `linearTech_not_strictMono`,
  `linearTech_omegaP`, `rmc_linear_const`).
-/

namespace Woodford.NominalRigidities.MarginalCost

open Filter Topology

/-- Woodford (2003), eq. (1.7), p. 148: the production function `y = A f(h)`, with `f` increasing
(`f' > 0`) and mapping `(0, ∞)` bijectively onto `(0, ∞)` with inverse `f⁻¹`. -/
structure Technology where
  f : ℝ → ℝ
  df : ℝ → ℝ
  finv : ℝ → ℝ
  hasDerivAt_f : ∀ h : ℝ, 0 < h → HasDerivAt f (df h) h
  df_pos : ∀ h : ℝ, 0 < h → 0 < df h
  f_pos : ∀ h : ℝ, 0 < h → 0 < f h
  finv_pos : ∀ y : ℝ, 0 < y → 0 < finv y
  f_finv : ∀ y : ℝ, 0 < y → f (finv y) = y
  finv_f : ∀ h : ℝ, 0 < h → finv (f h) = h

namespace Technology

variable (T : Technology)

/-- Woodford (2003), eq. (1.9), p. 148: `Ψ(y) = 1 / f'(f⁻¹(y))`. -/
noncomputable def Psi (y : ℝ) : ℝ := 1 / T.df (T.finv y)

/-- Woodford (2003), eq. (1.7), p. 148: `f` is strictly increasing on `(0, ∞)`. -/
theorem f_strictMonoOn : StrictMonoOn T.f (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun h hh => (T.hasDerivAt_f h hh).continuousAt.continuousWithinAt) fun h hh => ?_
  rw [interior_Ioi] at hh
  rw [(T.hasDerivAt_f h hh).deriv]
  exact T.df_pos h hh

/-- Woodford (2003), p. 148: the labour requirement `f⁻¹` is strictly increasing. -/
theorem finv_strictMonoOn : StrictMonoOn T.finv (Set.Ioi 0) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  by_contra hle
  push Not at hle
  have := T.f_strictMonoOn.monotoneOn (T.finv_pos y₂ hy₂) (T.finv_pos y₁ hy₁) hle
  rw [T.f_finv y₁ hy₁, T.f_finv y₂ hy₂] at this
  exact absurd hlt (not_lt.2 this)

/-- Woodford (2003), p. 148: `f⁻¹` is continuous on `(0, ∞)`. -/
theorem finv_continuousAt {y : ℝ} (hy : 0 < y) : ContinuousAt T.finv y :=
  T.finv_strictMonoOn.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hy)
    (Filter.mem_of_superset (Ioi_mem_nhds (T.finv_pos y hy)) fun h hh =>
      ⟨T.f h, T.f_pos h hh, T.finv_f h hh⟩)

/-- Woodford (2003), eqs. (1.8)–(1.9), p. 148: `(f⁻¹)'(y) = 1/f'(f⁻¹(y)) = Ψ(y)`. -/
theorem hasDerivAt_finv {y : ℝ} (hy : 0 < y) : HasDerivAt T.finv (T.Psi y) y := by
  have h := HasDerivAt.of_local_left_inverse (T.finv_continuousAt hy)
    (T.hasDerivAt_f _ (T.finv_pos y hy)) (T.df_pos _ (T.finv_pos y hy)).ne'
    (by filter_upwards [Ioi_mem_nhds hy] with z hz using T.f_finv z hz)
  rwa [Psi, one_div]

/-- Woodford (2003), eq. (1.9), p. 148: `Ψ` is positive. -/
theorem Psi_pos {y : ℝ} (hy : 0 < y) : 0 < T.Psi y :=
  one_div_pos.2 (T.df_pos _ (T.finv_pos y hy))

/-- Woodford (2003), eq. (1.9), p. 148: for concave `f` (`f'` nonincreasing), `Ψ` is
nondecreasing. -/
theorem Psi_monotoneOn (hdf : AntitoneOn T.df (Set.Ioi 0)) : MonotoneOn T.Psi (Set.Ioi 0) := by
  intro y₁ hy₁ y₂ hy₂ hle
  have hh := T.finv_strictMonoOn.monotoneOn hy₁ hy₂ hle
  exact one_div_le_one_div_of_le (T.df_pos _ (T.finv_pos y₂ hy₂))
    (hdf (T.finv_pos y₁ hy₁) (T.finv_pos y₂ hy₂) hh)

/-- Woodford (2003), eq. (1.9), p. 148: "`Ψ` is an increasing positive function" — true in the
strict sense when `f` is strictly concave (`f'` strictly decreasing). -/
theorem Psi_strictMonoOn (hdf : StrictAntiOn T.df (Set.Ioi 0)) :
    StrictMonoOn T.Psi (Set.Ioi 0) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  have hh := T.finv_strictMonoOn hy₁ hy₂ hlt
  exact one_div_lt_one_div_of_lt (T.df_pos _ (T.finv_pos y₂ hy₂))
    (hdf (T.finv_pos y₁ hy₁) (T.finv_pos y₂ hy₂) hh)

/-- Woodford (2003), eq. (1.8), p. 148: the variable cost `w f⁻¹(y/A)` has derivative
(nominal marginal cost) `S = (w/A) Ψ(y/A)`. -/
theorem hasDerivAt_variableCost (w : ℝ) {A y : ℝ} (hA : 0 < A) (hy : 0 < y) :
    HasDerivAt (fun y => w * T.finv (y / A)) (w / A * T.Psi (y / A)) y := by
  have h := ((T.hasDerivAt_finv (div_pos hy hA)).comp y
    ((hasDerivAt_id y).div_const A)).const_mul w
  exact HasDerivAt.congr_deriv h (by ring)

/-- Woodford (2003), eq. (1.9), p. 148: if `f'` is differentiable at `f⁻¹(y)` with derivative
`f''`, then `Ψ'(y) = −f''/f'³`. -/
theorem hasDerivAt_Psi {y d2f : ℝ} (hy : 0 < y) (hd2f : HasDerivAt T.df d2f (T.finv y)) :
    HasDerivAt T.Psi (-d2f / T.df (T.finv y) ^ 3) y := by
  have h1 := hd2f.comp y (T.hasDerivAt_finv hy)
  have h2 := h1.inv (T.df_pos _ (T.finv_pos y hy)).ne'
  have hfun : T.Psi = fun x => ((T.df ∘ T.finv) x)⁻¹ := funext fun x => by
    simp [Psi]
  rw [hfun]
  refine HasDerivAt.congr_deriv h2 ?_
  have := (T.df_pos _ (T.finv_pos y hy)).ne'
  simp only [Function.comp_apply, Psi]
  field_simp

/-- Woodford (2003), eq. (1.9), p. 148: `Ψ` is continuous when `f'` is. -/
theorem Psi_continuousOn (hdfc : ContinuousOn T.df (Set.Ioi 0)) :
    ContinuousOn T.Psi (Set.Ioi 0) := by
  intro y hy
  have h1 : ContinuousAt (T.df ∘ T.finv) y :=
    ContinuousAt.comp ((hdfc.continuousAt (Ioi_mem_nhds (T.finv_pos y hy))))
      (T.finv_continuousAt hy)
  exact (continuousAt_const.div h1 (T.df_pos _ (T.finv_pos y hy)).ne').continuousWithinAt

end Technology

/-- Woodford (2003), p. 148 (the book's hypotheses are only "increasing, concave"): the linear
technology `f(h) = h`. -/
def linearTech : Technology where
  f := id
  df := fun _ => 1
  finv := id
  hasDerivAt_f := fun h _ => hasDerivAt_id h
  df_pos := fun _ _ => one_pos
  f_pos := fun _ hh => hh
  finv_pos := fun _ hy => hy
  f_finv := fun _ _ => rfl
  finv_f := fun _ _ => rfl

/-- Woodford (2003), eq. (1.9), p. 148: for the linear technology `Ψ ≡ 1`. -/
theorem linearTech_Psi (y : ℝ) : linearTech.Psi y = 1 := by
  simp [Technology.Psi, linearTech]

/-- Woodford (2003), p. 148 (**imprecision**): `f(h) = h` is increasing and concave, yet `Ψ` is
not (strictly) increasing; "`Ψ` increasing" needs strict concavity. -/
theorem linearTech_not_strictMono : ConcaveOn ℝ (Set.Ioi 0) linearTech.f ∧
    ¬ StrictMonoOn linearTech.Psi (Set.Ioi 0) := by
  refine ⟨concaveOn_id (convex_Ioi 0), fun h => ?_⟩
  have := h (Set.mem_Ioi.2 one_pos) (Set.mem_Ioi.2 two_pos)
    one_lt_two
  rw [linearTech_Psi, linearTech_Psi] at this
  exact lt_irrefl _ this

variable {E : Type*}

/-- Woodford (2003), eq. (1.10), p. 149: the real marginal cost function
`s(y, Y; ξ̃) = v_h(f⁻¹(y/A); ξ) / (u_c(Y; ξ) A) · Ψ(y/A)`, with `ξ̃ = (A, ξ)`. -/
noncomputable def rmc (T : Technology) (vh uc : ℝ → E → ℝ) (y Y A : ℝ) (ξ : E) : ℝ :=
  vh (T.finv (y / A)) ξ / (uc Y ξ * A) * T.Psi (y / A)

/-- Woodford (2003), eqs. (1.6), (1.8), (1.10), pp. 147–149: substituting the labour supply
condition `w/P = v_h(h; ξ)/u_c(Y; ξ)` at the labour requirement `h = f⁻¹(y/A)` into the
nominal marginal cost `S = (w/A) Ψ(y/A)` gives real marginal cost `S/P = s(y, Y; ξ̃)`. -/
theorem rmc_eq_real_wage_cost (T : Technology) (vh uc : ℝ → E → ℝ) {y Y A P w : ℝ} {ξ : E}
    (hP : 0 < P) (hA : 0 < A) (huc : 0 < uc Y ξ)
    (hw : w / P = vh (T.finv (y / A)) ξ / uc Y ξ) :
    w / A * T.Psi (y / A) / P = rmc T vh uc y Y A ξ := by
  have hw' : w = P * (vh (T.finv (y / A)) ξ / uc Y ξ) := by
    rw [← hw]; field_simp
  rw [rmc, hw']
  have := hA.ne'
  have := huc.ne'
  have := hP.ne'
  field_simp

/-- Woodford (2003), p. 151 ("`s` is increasing in its first argument"): if `v_h(·; ξ)` is
positive and nondecreasing (`v` increasing, convex) and `f` is concave, and at least one of
them is strict, then `s(·, Y; ξ̃)` is strictly increasing on `(0, ∞)`. -/
theorem rmc_strictMonoOn_y (T : Technology) (vh uc : ℝ → E → ℝ) {Y A : ℝ} {ξ : E}
    (hA : 0 < A) (huc : 0 < uc Y ξ) (hvh : ∀ h, 0 < h → 0 < vh h ξ)
    (hvm : MonotoneOn (fun h => vh h ξ) (Set.Ioi 0)) (hdf : AntitoneOn T.df (Set.Ioi 0))
    (hstrict : StrictMonoOn (fun h => vh h ξ) (Set.Ioi 0) ∨ StrictAntiOn T.df (Set.Ioi 0)) :
    StrictMonoOn (fun y => rmc T vh uc y Y A ξ) (Set.Ioi 0) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  have hu₁ : 0 < y₁ / A := div_pos hy₁ hA
  have hu₂ : 0 < y₂ / A := div_pos hy₂ hA
  have hu : y₁ / A < y₂ / A := div_lt_div_of_pos_right hlt hA
  have hh₁ := T.finv_pos _ hu₁
  have hh₂ := T.finv_pos _ hu₂
  have hh := T.finv_strictMonoOn hu₁ hu₂ hu
  have hv₁ := hvh _ hh₁
  have hΨ₂ := T.Psi_pos hu₂
  have hk : 0 < uc Y ξ * A := mul_pos huc hA
  have key : vh (T.finv (y₁ / A)) ξ * T.Psi (y₁ / A) < vh (T.finv (y₂ / A)) ξ * T.Psi (y₂ / A) := by
    rcases hstrict with hs | hs
    · calc vh (T.finv (y₁ / A)) ξ * T.Psi (y₁ / A)
          ≤ vh (T.finv (y₁ / A)) ξ * T.Psi (y₂ / A) :=
            mul_le_mul_of_nonneg_left (T.Psi_monotoneOn hdf hu₁ hu₂ hu.le) hv₁.le
        _ < vh (T.finv (y₂ / A)) ξ * T.Psi (y₂ / A) :=
            mul_lt_mul_of_pos_right (hs hh₁ hh₂ hh) hΨ₂
    · calc vh (T.finv (y₁ / A)) ξ * T.Psi (y₁ / A)
          < vh (T.finv (y₁ / A)) ξ * T.Psi (y₂ / A) :=
            mul_lt_mul_of_pos_left (T.Psi_strictMonoOn hs hu₁ hu₂ hu) hv₁
        _ ≤ vh (T.finv (y₂ / A)) ξ * T.Psi (y₂ / A) :=
            mul_le_mul_of_nonneg_right (hvm hh₁ hh₂ hh.le) hΨ₂.le
  simp only [rmc, div_mul_eq_mul_div]
  exact div_lt_div_of_pos_right key hk

/-- Woodford (2003), p. 151 ("`s` is also increasing in its second argument"): if `u_c(·; ξ)`
is positive and strictly decreasing (`u` strictly concave), `s(y, ·; ξ̃)` is strictly
increasing. -/
theorem rmc_strictMonoOn_Y (T : Technology) (vh uc : ℝ → E → ℝ) {y A : ℝ} {ξ : E}
    (hy : 0 < y) (hA : 0 < A) (hvh : ∀ h, 0 < h → 0 < vh h ξ)
    (huc : ∀ Y, 0 < Y → 0 < uc Y ξ) (hanti : StrictAntiOn (fun Y => uc Y ξ) (Set.Ioi 0)) :
    StrictMonoOn (fun Y => rmc T vh uc y Y A ξ) (Set.Ioi 0) := by
  intro Y₁ hY₁ Y₂ hY₂ hlt
  have hu : 0 < y / A := div_pos hy hA
  have hnum : 0 < vh (T.finv (y / A)) ξ * T.Psi (y / A) :=
    mul_pos (hvh _ (T.finv_pos _ hu)) (T.Psi_pos hu)
  simp only [rmc, div_mul_eq_mul_div]
  exact div_lt_div_of_pos_left hnum (mul_pos (huc Y₂ hY₂) hA)
    (mul_lt_mul_of_pos_right (hanti hY₁ hY₂ hlt) hA)

/-- Woodford (2003), p. 151 (**imprecision**): with a linear technology and a linear disutility
of labour (`v` increasing and convex, `v_h ≡ c`), real marginal cost does not vary with own
output, so "`s` increasing in its first argument" needs strict curvature somewhere. -/
theorem rmc_linear_const (uc : ℝ → E → ℝ) (c : ℝ) (y₁ y₂ Y : ℝ) (ξ : E) :
    rmc linearTech (fun _ _ => c) uc y₁ Y 1 ξ = rmc linearTech (fun _ _ => c) uc y₂ Y 1 ξ := by
  simp [rmc, linearTech_Psi]

/-- Woodford (2003), eq. (1.11), p. 150 (yeoman farmer): the disutility of supplying `y`,
`ṽ(y; ξ̃) = v(f⁻¹(y/A); ξ)`, has derivative `ṽ_y = v_h(f⁻¹(y/A); ξ) Ψ(y/A)/A`. -/
theorem yeoman_hasDerivAt (T : Technology) {v vh : ℝ → E → ℝ} {ξ : E}
    (hv : ∀ h, 0 < h → HasDerivAt (fun h => v h ξ) (vh h ξ) h) {A y : ℝ} (hA : 0 < A)
    (hy : 0 < y) :
    HasDerivAt (fun y => v (T.finv (y / A)) ξ)
      (vh (T.finv (y / A)) ξ * T.Psi (y / A) / A) y := by
  have h1 := (T.hasDerivAt_finv (div_pos hy hA)).comp y ((hasDerivAt_id y).div_const A)
  have h2 := (hv _ (T.finv_pos _ (div_pos hy hA))).comp y h1
  exact HasDerivAt.congr_deriv h2 (by ring)

/-- Woodford (2003), p. 150 (**yeoman-farmer equivalence**): the marginal disutility of supply
in units of the aggregate, `ṽ_y(y; ξ̃)/u_c(Y; ξ)`, is exactly the real marginal cost (1.10). -/
theorem yeoman_rmc (T : Technology) {v vh : ℝ → E → ℝ} (uc : ℝ → E → ℝ) {ξ : E}
    (hv : ∀ h, 0 < h → HasDerivAt (fun h => v h ξ) (vh h ξ) h) {A y Y : ℝ} (hA : 0 < A)
    (hy : 0 < y) :
    HasDerivAt (fun y => v (T.finv (y / A)) ξ / uc Y ξ) (rmc T vh uc y Y A ξ) y := by
  have h := (yeoman_hasDerivAt T hv hA hy).div_const (uc Y ξ)
  refine HasDerivAt.congr_deriv h ?_
  rw [rmc]
  ring

variable [Zero E]

/-! ### Elasticities at the steady state (eqs. (1.15)–(1.16), p. 152)

The steady state has `A = 1` (`a = log A = 0`, footnote 11), `ξ = 0` and output `Ȳ > 0`,
with labour `h̄ = f⁻¹(Ȳ)`. -/

/-- Woodford (2003), eq. (1.16), p. 152: `ω_w`, the elasticity of the marginal disutility of
work `v_h(f⁻¹(y); 0)` with respect to output at `Ȳ`. -/
noncomputable def omegaW (T : Technology) (vh : ℝ → E → ℝ) (vhh Ybar : ℝ) : ℝ :=
  Ybar * vhh * T.Psi Ybar / vh (T.finv Ybar) 0

/-- Woodford (2003), eq. (1.16), p. 152: `ω_p = −Ȳ f''(h̄)/f'(h̄)²`, the elasticity of `Ψ`. -/
noncomputable def omegaP (T : Technology) (d2f Ybar : ℝ) : ℝ :=
  -(Ybar * d2f / T.df (T.finv Ybar) ^ 2)

/-- Woodford (2003), p. 152: `σ⁻¹ = −Ȳ u_cc/u_c`, the inverse intertemporal elasticity. -/
noncomputable def sigmaInv (uc : ℝ → E → ℝ) (ucc Ybar : ℝ) : ℝ :=
  -(Ybar * ucc / uc Ybar 0)

/-- Woodford (2003), p. 152: the map `x ↦ Ȳ eˣ` has derivative `Ȳ` at `0`. -/
theorem hasDerivAt_scale (Ybar : ℝ) :
    HasDerivAt (fun x => Ybar * Real.exp x) Ybar 0 := by
  have h := (Real.hasDerivAt_exp 0).const_mul Ybar
  simpa using h

/-- Woodford (2003), eq. (1.16), p. 152: the elasticity of `v_h(f⁻¹(y); 0)` is `ω_w`. -/
theorem elasticity_vh (T : Technology) (vh : ℝ → E → ℝ) {vhh Ybar : ℝ} (hY : 0 < Ybar)
    (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar)) (hvh : 0 < vh (T.finv Ybar) 0) :
    HasDerivAt (fun x => Real.log (vh (T.finv (Ybar * Real.exp x)) 0))
      (omegaW T vh vhh Ybar) 0 := by
  have h1 := (T.hasDerivAt_finv hY).comp_of_eq 0 (hasDerivAt_scale Ybar) (by simp)
  have h2 := hvhh.comp_of_eq 0 h1 (by simp)
  have h3 := h2.log (by simpa using hvh.ne')
  refine HasDerivAt.congr_deriv h3 ?_
  simp only [Function.comp_apply, Real.exp_zero, mul_one, omegaW]
  ring

/-- Woodford (2003), eq. (1.16), p. 152: the elasticity of `Ψ` at `Ȳ` is `ω_p`. -/
theorem elasticity_Psi (T : Technology) {d2f Ybar : ℝ} (hY : 0 < Ybar)
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar)) :
    HasDerivAt (fun x => Real.log (T.Psi (Ybar * Real.exp x))) (omegaP T d2f Ybar) 0 := by
  have h1 := (T.hasDerivAt_Psi hY hd2f).comp_of_eq 0 (hasDerivAt_scale Ybar) (by simp)
  have h2 := h1.log (by simpa using (T.Psi_pos hY).ne')
  refine HasDerivAt.congr_deriv h2 ?_
  have := (T.df_pos _ (T.finv_pos _ hY)).ne'
  simp only [Function.comp_apply, Real.exp_zero, mul_one, omegaP, Technology.Psi]
  field_simp

/-- Woodford (2003), p. 152: the elasticity of `u_c(Y; 0)` at `Ȳ` is `−σ⁻¹`. -/
theorem elasticity_uc (uc : ℝ → E → ℝ) {ucc Ybar : ℝ}
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar) (huc : 0 < uc Ybar 0) :
    HasDerivAt (fun X => Real.log (uc (Ybar * Real.exp X) 0)) (-sigmaInv uc ucc Ybar) 0 := by
  have h1 := hucc.comp_of_eq 0 (hasDerivAt_scale Ybar) (by simp)
  have h2 := h1.log (by simpa using huc.ne')
  refine HasDerivAt.congr_deriv h2 ?_
  simp only [Function.comp_apply, Real.exp_zero, mul_one, sigmaInv]
  ring

omit [Zero E] in
/-- Woodford (2003), p. 152: `log s` splits as `log v_h − log (u_c A) + log Ψ`. -/
theorem log_rmc (T : Technology) (vh uc : ℝ → E → ℝ) {y Y A : ℝ} {ξ : E} (hy : 0 < y)
    (hA : 0 < A) (hvh : 0 < vh (T.finv (y / A)) ξ) (huc : 0 < uc Y ξ) :
    Real.log (rmc T vh uc y Y A ξ) = Real.log (vh (T.finv (y / A)) ξ) - Real.log (uc Y ξ)
      - Real.log A + Real.log (T.Psi (y / A)) := by
  rw [rmc, Real.log_mul (div_pos hvh (mul_pos huc hA)).ne' (T.Psi_pos (div_pos hy hA)).ne',
    Real.log_div hvh.ne' (mul_pos huc hA).ne', Real.log_mul huc.ne' hA.ne']
  ring

/-- Woodford (2003), eqs. (1.15)–(1.16), p. 152: **the elasticity of real marginal cost with
respect to own output is `ω = ω_w + ω_p`**: `d log s(Ȳ eˣ, Ȳ; 1, 0)/dx = ω_w + ω_p` at `0`. -/
theorem elasticity_rmc_y (T : Technology) (vh uc : ℝ → E → ℝ) {vhh d2f Ybar : ℝ}
    (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar)) (hvh : ∀ h, 0 < h → 0 < vh h 0)
    (huc : 0 < uc Ybar 0) :
    HasDerivAt (fun x => Real.log (rmc T vh uc (Ybar * Real.exp x) Ybar 1 0))
      (omegaW T vh vhh Ybar + omegaP T d2f Ybar) 0 := by
  have h := ((elasticity_vh T vh hY hvhh (hvh _ (T.finv_pos _ hY))).sub_const
    (Real.log (uc Ybar 0) + Real.log 1)).add (elasticity_Psi T hY hd2f)
  refine (HasDerivAt.congr_deriv h (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => ?_)
  have hx : 0 < Ybar * Real.exp x := mul_pos hY (Real.exp_pos x)
  simp only [Pi.add_apply]
  rw [log_rmc T vh uc hx one_pos (hvh _ (T.finv_pos _ (by simpa using hx))) huc]
  simp only [div_one]
  ring

/-- Woodford (2003), eq. (1.15), p. 152: **the elasticity of real marginal cost with respect to
aggregate output is `σ⁻¹`**: `d log s(Ȳ, Ȳ e^X; 1, 0)/dX = σ⁻¹` at `0`. -/
theorem elasticity_rmc_Y (T : Technology) (vh uc : ℝ → E → ℝ) {ucc Ybar : ℝ} (hY : 0 < Ybar)
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar) (hvh : 0 < vh (T.finv Ybar) 0)
    (huc : ∀ Y, 0 < Y → 0 < uc Y 0) :
    HasDerivAt (fun X => Real.log (rmc T vh uc Ybar (Ybar * Real.exp X) 1 0))
      (sigmaInv uc ucc Ybar) 0 := by
  have h := ((elasticity_uc uc hucc (huc _ hY)).const_sub
    (Real.log (vh (T.finv Ybar) 0) + Real.log (T.Psi Ybar))).sub_const (Real.log 1)
  refine (HasDerivAt.congr_deriv h (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun X => ?_)
  have hX : 0 < Ybar * Real.exp X := mul_pos hY (Real.exp_pos X)
  dsimp only
  rw [log_rmc T vh uc hY one_pos (by simpa using hvh) (huc _ hX)]
  simp only [div_one]
  ring

/-- Woodford (2003), p. 152 and n. 11: **the elasticity of real marginal cost with respect to
technology** `a = log A` is `−(1 + ω)`. -/
theorem elasticity_rmc_A (T : Technology) (vh uc : ℝ → E → ℝ) {vhh d2f Ybar : ℝ}
    (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar)) (hvh : ∀ h, 0 < h → 0 < vh h 0)
    (huc : 0 < uc Ybar 0) :
    HasDerivAt (fun a => Real.log (rmc T vh uc Ybar Ybar (Real.exp a) 0))
      (-(1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar))) 0 := by
  have hneg : HasDerivAt (fun a : ℝ => -a) (-1) 0 := hasDerivAt_neg 0
  have hv := (elasticity_vh T vh hY hvhh (hvh _ (T.finv_pos _ hY))).comp_of_eq 0 hneg (by simp)
  have hp := (elasticity_Psi T hY hd2f).comp_of_eq 0 hneg (by simp)
  have h := ((hv.sub_const (Real.log (uc Ybar 0))).sub (hasDerivAt_id (0 : ℝ))).add hp
  refine (HasDerivAt.congr_deriv h (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun a => ?_)
  have hu : Ybar / Real.exp a = Ybar * Real.exp (-a) := by
    rw [Real.exp_neg, div_eq_mul_inv]
  have hpos : 0 < Ybar / Real.exp a := div_pos hY (Real.exp_pos a)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [log_rmc T vh uc hY (Real.exp_pos a) (hvh _ (T.finv_pos _ hpos)) huc, Real.log_exp, hu]
  simp only [Function.comp_apply, id]

/-- Woodford (2003), p. 152 ("`ω_p > 0`"): `ω_p > 0` iff `f''(h̄) < 0`. -/
theorem omegaP_pos_iff (T : Technology) {d2f Ybar : ℝ} (hY : 0 < Ybar) :
    0 < omegaP T d2f Ybar ↔ d2f < 0 := by
  have hdf := T.df_pos _ (T.finv_pos _ hY)
  have hsq : 0 < T.df (T.finv Ybar) ^ 2 := by positivity
  rw [omegaP, neg_pos, div_lt_iff₀ hsq, zero_mul]
  constructor <;> intro h <;> nlinarith

/-- Woodford (2003), p. 152 ("`ω_w > 0`"): `ω_w > 0` iff `v_hh(h̄) > 0`. -/
theorem omegaW_pos_iff (T : Technology) (vh : ℝ → E → ℝ) {vhh Ybar : ℝ} (hY : 0 < Ybar)
    (hvh : 0 < vh (T.finv Ybar) 0) : 0 < omegaW T vh vhh Ybar ↔ 0 < vhh := by
  have hΨ := T.Psi_pos hY
  rw [omegaW, div_pos_iff_of_pos_right hvh]
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have : Ybar * vhh * T.Psi Ybar ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hY.le h') hΨ.le
    linarith
  · intro h
    positivity

/-- Woodford (2003), p. 152 ("`σ > 0`"): `σ⁻¹ > 0` iff `u_cc(Ȳ) < 0`. -/
theorem sigmaInv_pos_iff (uc : ℝ → E → ℝ) {ucc Ybar : ℝ} (hY : 0 < Ybar) (huc : 0 < uc Ybar 0) :
    0 < sigmaInv uc ucc Ybar ↔ ucc < 0 := by
  rw [sigmaInv, neg_pos, div_lt_iff₀ huc, zero_mul]
  constructor <;> intro h <;> nlinarith

/-- Woodford (2003), p. 152 (**imprecision**): for the linear technology (increasing, concave)
`f'' = 0`, so `ω_p = 0`: the printed `ω_p > 0` fails without strict concavity. -/
theorem linearTech_omegaP (Ybar h : ℝ) :
    HasDerivAt linearTech.df 0 h ∧ omegaP linearTech 0 Ybar = 0 := by
  refine ⟨hasDerivAt_const h 1, ?_⟩
  simp [omegaP]

/-! ### Equation (1.15) as an exact Fréchet derivative -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Woodford (2003), eq. (1.15), p. 152: `ŝ(x, X, a, ξ) = log s(Ȳ eˣ, Ȳ e^X; eᵃ, ξ) − log s̄`, real
marginal cost in log deviations, as a function of `(ŷ, Ŷ, a, ξ)`. -/
noncomputable def logRmcGap (T : Technology) (vh uc : ℝ → F → ℝ) (Ybar : ℝ)
    (p : ℝ × ℝ × ℝ × F) : ℝ :=
  Real.log (rmc T vh uc (Ybar * Real.exp p.1) (Ybar * Real.exp p.2.1) (Real.exp p.2.2.1)
    p.2.2.2) - Real.log (rmc T vh uc Ybar Ybar 1 0)

/-- Woodford (2003), p. 152: `ŝ` is (Fréchet) differentiable at the steady state when
`v_h`, `u_c` are jointly differentiable in (quantity, shock) and `f'` is differentiable. -/
theorem logRmcGap_differentiableAt (T : Technology) (vh uc : ℝ → F → ℝ) {d2f Ybar : ℝ}
    (hY : 0 < Ybar) (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : 0 < vh (T.finv Ybar) 0) (huc : 0 < uc Ybar 0) :
    DifferentiableAt ℝ (logRmcGap T vh uc Ybar) 0 := by
  set u : ℝ × ℝ × ℝ × F → ℝ := fun p => Ybar * Real.exp p.1 / Real.exp p.2.2.1 with hu
  have hu0 : u 0 = Ybar := by simp [hu]
  have hud : DifferentiableAt ℝ u 0 := by
    have hnum : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × F => Ybar * Real.exp p.1) 0 :=
      (differentiableAt_const Ybar).mul (Real.differentiableAt_exp.comp _ differentiableAt_fst)
    have hden : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × F => Real.exp p.2.2.1) 0 :=
      Real.differentiableAt_exp.comp _ (differentiableAt_fst.comp _
        (differentiableAt_snd.comp _ differentiableAt_snd))
    exact (hnum.mul (hden.inv (Real.exp_pos _).ne')).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by simp [hu, div_eq_mul_inv])
  have hfinv : DifferentiableAt ℝ T.finv (u 0) := by
    rw [hu0]; exact (T.hasDerivAt_finv hY).differentiableAt
  have hPsi : DifferentiableAt ℝ T.Psi (u 0) := by
    rw [hu0]; exact (T.hasDerivAt_Psi hY hd2f).differentiableAt
  have hinner : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × F => (T.finv (u p), p.2.2.2)) 0 :=
    (hfinv.comp 0 hud).prodMk (differentiableAt_snd.comp _ (differentiableAt_snd.comp _
      differentiableAt_snd))
  have hV : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × F => vh (T.finv (u p)) p.2.2.2) 0 := by
    have hpt : (fun p : ℝ × ℝ × ℝ × F => (T.finv (u p), p.2.2.2)) 0 = (T.finv Ybar, 0) := by
      simp [hu0]
    have h := hvhd
    rw [← hpt] at h
    exact DifferentiableAt.comp (f := fun p : ℝ × ℝ × ℝ × F => (T.finv (u p), p.2.2.2)) 0 h hinner
  have hinner2 : DifferentiableAt ℝ
      (fun p : ℝ × ℝ × ℝ × F => (Ybar * Real.exp p.2.1, p.2.2.2)) 0 :=
    ((differentiableAt_const Ybar).mul (Real.differentiableAt_exp.comp _
      (differentiableAt_fst.comp _ differentiableAt_snd))).prodMk
      (differentiableAt_snd.comp _ (differentiableAt_snd.comp _ differentiableAt_snd))
  have hU : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × F => uc (Ybar * Real.exp p.2.1) p.2.2.2) 0 := by
    have hpt : (fun p : ℝ × ℝ × ℝ × F => (Ybar * Real.exp p.2.1, p.2.2.2)) 0 = (Ybar, 0) := by
      simp
    have h := hucd
    rw [← hpt] at h
    exact DifferentiableAt.comp
      (f := fun p : ℝ × ℝ × ℝ × F => (Ybar * Real.exp p.2.1, p.2.2.2)) 0 h hinner2
  have hA : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × F => Real.exp p.2.2.1) 0 :=
    Real.differentiableAt_exp.comp _ (differentiableAt_fst.comp _
      (differentiableAt_snd.comp _ differentiableAt_snd))
  have hden : (fun p : ℝ × ℝ × ℝ × F => uc (Ybar * Real.exp p.2.1) p.2.2.2 *
      Real.exp p.2.2.1) 0 ≠ 0 := by
    simpa using huc.ne'
  have hR : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × F =>
      rmc T vh uc (Ybar * Real.exp p.1) (Ybar * Real.exp p.2.1) (Real.exp p.2.2.1) p.2.2.2) 0 := by
    have h := (hV.mul ((hU.mul hA).inv hden)).mul (hPsi.comp 0 hud)
    exact h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun p => by simp [rmc, hu, div_eq_mul_inv])
  have hR0 : rmc T vh uc (Ybar * Real.exp (0 : ℝ × ℝ × ℝ × F).1)
      (Ybar * Real.exp (0 : ℝ × ℝ × ℝ × F).2.1) (Real.exp (0 : ℝ × ℝ × ℝ × F).2.2.1)
      (0 : ℝ × ℝ × ℝ × F).2.2.2 ≠ 0 := by
    simp only [Prod.fst_zero, Prod.snd_zero, Real.exp_zero, mul_one, rmc, div_one]
    exact (mul_pos (div_pos hvh huc) (T.Psi_pos hY)).ne'
  exact (hR.log hR0).sub_const _

/-- Woodford (2003), eq. (1.15), p. 152 (**the partial derivatives of `ŝ`**): for the Fréchet
derivative `D` of `ŝ` at the steady state,
`D(x, X, a, ξ) = ω x + σ⁻¹ X − (1 + ω) a + D(0, 0, 0, ξ)` with `ω = ω_w + ω_p`. -/
theorem fderiv_logRmcGap (T : Technology) (vh uc : ℝ → F → ℝ) {vhh d2f ucc Ybar : ℝ}
    (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0) (x X a : ℝ) (ξ : F) :
    fderiv ℝ (logRmcGap T vh uc Ybar) 0 (x, X, a, ξ)
      = (omegaW T vh vhh Ybar + omegaP T d2f Ybar) * x + sigmaInv uc ucc Ybar * X
        - (1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar)) * a
        + fderiv ℝ (logRmcGap T vh uc Ybar) 0 (0, 0, 0, ξ) := by
  have hD := (logRmcGap_differentiableAt T vh uc hY hd2f hvhd hucd (hvh _ (T.finv_pos _ hY))
    (huc _ hY)).hasFDerivAt
  set D := fderiv ℝ (logRmcGap T vh uc Ybar) 0
  have hc0 := hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hcE := hasDerivAt_const (0 : ℝ) (0 : F)
  have hid := hasDerivAt_id (0 : ℝ)
  -- direction `x`
  have h1 := hD.comp_hasDerivAt_of_eq 0 (hid.prodMk (hc0.prodMk (hc0.prodMk hcE))) rfl
  have e1 := (elasticity_rmc_y T vh uc hY hvhh hd2f hvh (huc _ hY)).sub_const
    (Real.log (rmc T vh uc Ybar Ybar 1 0))
  have d1 : D (1, 0, 0, 0) = omegaW T vh vhh Ybar + omegaP T d2f Ybar :=
    h1.unique (e1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp [logRmcGap]))
  -- direction `X`
  have h2 := hD.comp_hasDerivAt_of_eq 0 (hc0.prodMk (hid.prodMk (hc0.prodMk hcE))) rfl
  have e2 := (elasticity_rmc_Y T vh uc hY hucc (hvh _ (T.finv_pos _ hY)) huc).sub_const
    (Real.log (rmc T vh uc Ybar Ybar 1 0))
  have d2 : D (0, 1, 0, 0) = sigmaInv uc ucc Ybar :=
    h2.unique (e2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp [logRmcGap]))
  -- direction `a`
  have h3 := hD.comp_hasDerivAt_of_eq 0 (hc0.prodMk (hc0.prodMk (hid.prodMk hcE))) rfl
  have e3 := (elasticity_rmc_A T vh uc hY hvhh hd2f hvh (huc _ hY)).sub_const
    (Real.log (rmc T vh uc Ybar Ybar 1 0))
  have d3 : D (0, 0, 1, 0) = -(1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar)) :=
    h3.unique (e3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      simp [logRmcGap]))
  have hsplit : ((x, X, a, ξ) : ℝ × ℝ × ℝ × F) = x • ((1 : ℝ), (0 : ℝ), (0 : ℝ), (0 : F)) +
      X • ((0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : F)) + a • ((0 : ℝ), (0 : ℝ), (1 : ℝ), (0 : F)) +
      ((0 : ℝ), (0 : ℝ), (0 : ℝ), ξ) := by
    simp
  rw [hsplit, map_add, map_add, map_add, map_smul, map_smul, map_smul, d1, d2, d3,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (1.15), p. 152 (**the log-linear real marginal cost function, exact**):
let `n(a, ξ) = log(Yⁿ/Ȳ)` be the log natural rate, defined by `s(Yⁿ, Yⁿ; ξ̃) = s̄` (= `μ⁻¹`,
(1.14)) near the steady state and differentiable there with derivative `Dn`. Then the Fréchet
derivative of `ŝ` at the steady state is
`D(ŷ, Ŷ, a, ξ) = ω ŷ + σ⁻¹ Ŷ − (ω + σ⁻¹) Dn(a, ξ)`. -/
theorem eq_1_15 (T : Technology) (vh uc : ℝ → F → ℝ) {vhh d2f ucc Ybar : ℝ}
    (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0)
    {n : ℝ × F → ℝ} {Dn : ℝ × F →L[ℝ] ℝ} (hn : HasFDerivAt n Dn 0) (hn0 : n 0 = 0)
    (hnat : ∀ᶠ z in 𝓝 (0 : ℝ × F), logRmcGap T vh uc Ybar (n z, n z, z.1, z.2) = 0)
    (x X a : ℝ) (ξ : F) :
    fderiv ℝ (logRmcGap T vh uc Ybar) 0 (x, X, a, ξ)
      = (omegaW T vh vhh Ybar + omegaP T d2f Ybar) * x + sigmaInv uc ucc Ybar * X
        - (omegaW T vh vhh Ybar + omegaP T d2f Ybar + sigmaInv uc ucc Ybar) * Dn (a, ξ) := by
  have hD := (logRmcGap_differentiableAt T vh uc hY hd2f hvhd hucd (hvh _ (T.finv_pos _ hY))
    (huc _ hY)).hasFDerivAt
  set D := fderiv ℝ (logRmcGap T vh uc Ybar) 0
  have hψ : HasFDerivAt (fun z : ℝ × F => (n z, n z, z.1, z.2))
      (Dn.prod (Dn.prod ((ContinuousLinearMap.fst ℝ ℝ F).prod (ContinuousLinearMap.snd ℝ ℝ F))))
      0 :=
    hn.prodMk (hn.prodMk (hasFDerivAt_fst.prodMk hasFDerivAt_snd))
  have hψ0 : (fun z : ℝ × F => (n z, n z, z.1, z.2)) 0 = 0 := by
    simp [hn0]
  have hcomp := (hψ0 ▸ hD).comp (0 : ℝ × F) hψ
  have hzero : HasFDerivAt (logRmcGap T vh uc Ybar ∘ fun z : ℝ × F => (n z, n z, z.1, z.2))
      (0 : ℝ × F →L[ℝ] ℝ) 0 :=
    (hasFDerivAt_const (0 : ℝ) (0 : ℝ × F)).congr_of_eventuallyEq (by
      filter_upwards [hnat] with z hz
      simp only [Function.comp_apply]
      exact hz)
  have huniq := hcomp.unique hzero
  have hza : D (Dn (a, ξ), Dn (a, ξ), a, ξ) = 0 := by
    have := congrArg (fun L : ℝ × F →L[ℝ] ℝ => L (a, ξ)) huniq
    simpa using this
  have h1 := fderiv_logRmcGap T vh uc hY hvhh hd2f hucc hvhd hucd hvh huc x X a ξ
  have h2 := fderiv_logRmcGap T vh uc hY hvhh hd2f hucc hvhd hucd hvh huc (Dn (a, ξ))
    (Dn (a, ξ)) a ξ
  rw [hza] at h2
  rw [h1]
  linarith

/-- Woodford (2003), eq. (1.15), p. 152 (**the derivative of the natural rate**): under the
hypotheses of `eq_1_15`, `(ω + σ⁻¹) Dn(a, ξ) = (1 + ω) a − D(0, 0, 0, ξ)`; in particular the
natural rate responds to technology with elasticity `(1 + ω)/(ω + σ⁻¹)`. -/
theorem naturalRate_deriv (T : Technology) (vh uc : ℝ → F → ℝ) {vhh d2f ucc Ybar : ℝ}
    (hY : 0 < Ybar) (hvhh : HasDerivAt (fun h => vh h 0) vhh (T.finv Ybar))
    (hd2f : HasDerivAt T.df d2f (T.finv Ybar))
    (hucc : HasDerivAt (fun Y => uc Y 0) ucc Ybar)
    (hvhd : DifferentiableAt ℝ (fun q : ℝ × F => vh q.1 q.2) (T.finv Ybar, 0))
    (hucd : DifferentiableAt ℝ (fun q : ℝ × F => uc q.1 q.2) (Ybar, 0))
    (hvh : ∀ h, 0 < h → 0 < vh h 0) (huc : ∀ Y, 0 < Y → 0 < uc Y 0)
    {n : ℝ × F → ℝ} {Dn : ℝ × F →L[ℝ] ℝ} (hn : HasFDerivAt n Dn 0) (hn0 : n 0 = 0)
    (hnat : ∀ᶠ z in 𝓝 (0 : ℝ × F), logRmcGap T vh uc Ybar (n z, n z, z.1, z.2) = 0)
    (a : ℝ) (ξ : F) :
    (omegaW T vh vhh Ybar + omegaP T d2f Ybar + sigmaInv uc ucc Ybar) * Dn (a, ξ)
      = (1 + (omegaW T vh vhh Ybar + omegaP T d2f Ybar)) * a
        - fderiv ℝ (logRmcGap T vh uc Ybar) 0 (0, 0, 0, ξ) := by
  have h1 := eq_1_15 T vh uc hY hvhh hd2f hucc hvhd hucd hvh huc hn hn0 hnat 0 0 a ξ
  have h2 := fderiv_logRmcGap T vh uc hY hvhh hd2f hucc hvhd hucd hvh huc 0 0 a ξ
  linarith

end Woodford.NominalRigidities.MarginalCost
