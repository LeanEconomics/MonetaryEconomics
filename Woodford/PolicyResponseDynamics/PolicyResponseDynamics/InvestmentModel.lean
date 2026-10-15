/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PolicyResponseDynamics.ExpectationCalculus
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Investment demand with firm-specific capital

Woodford (2003), *Interest and Prices*, Chapter 5, §3.1–§3.2 (pp. 352–360), the long-run
relations of §3.3 (p. 365) and §3.4 (pp. 372–374): the model with firm-specific capital and
convex investment adjustment costs, with every log-linear equation linked to the nonlinear model
as an EXACT derivative at the steady state.

## Main results

* Log-derivative calculus along directions of log deviations: `LogDeriv`, `dev`,
  `LogDeriv.mul/div/sub/comp/comp₂`, `LogDeriv.hasDerivAt_log`.
* (3.1)–(3.2): `Technology` (restated from the Woodford Chapter 3 project), `output`, `labour`,
  `output_labour`, `labour_output`, `effective_ratio`; `Linear.eq_3_2_log` (demand, exact in logs);
  `AdjCost` (`I(1) = δ`, `I'(1) = 1`, `I''(1) = ε_ψ`) with the instance `AdjCost.quadratic`.
* p. 355: `hasDerivAt_wageBill_k` (the shadow value of capital is the wage-bill saving from a
  marginal unit of capital at given output); (3.4): `eq_3_4`; `rho_eq_rmc_mul`.
* (3.3): `FOC.eq_3_3_bounded` (exact, ANY state space, uniformly bounded deviations, no extra
  hypothesis: the uniform remainder is derived from primitives via `FOC.UnifDeriv`,
  `FOC.unifDeriv_integrand`, `FOC.hasDerivAt_E_of_unifDeriv`), `FOC.eq_3_3_finite` (exact, any
  finite state space), `FOC.eq_3_3` (general state space, assumed uniform `O(ε²)` remainder),
  `FOC.residual_zero` (uses `β(ρ̄ + 1 − δ) = 1`), `FOC.eq_3_3_iff`.
* (3.6), (3.11): `Linearise.eq_3_6`, `Linearise.eq_3_11`, `Linearise.eq_3_11_q`, with the
  coefficients `omega`, `rhoY`, `rhoK`, `qDist` and the primitives' elasticities `phi`, `omegaP`,
  `nuOf`, `xiOf`; `rhoY_gt_rhoK_pos` (`ρ_y > ρ_k > 0`), `rhoY_sub_rhoK` (`ρ_y − ρ_k = ν`).
* (3.7): `Linear.eq_3_7_iff` ((3.3) + (3.6) ⟺ corrected (3.7)), `Linear.eq_3_7_aggregate`.
* (3.8)–(3.10): `eq_3_8`, `eq_3_8_steady`, `eq_3_9`, `eq_3_10` (exact derivatives).
* p. 363: `steady_state_k`, `steady_state_k_iff`, `ten_quarters` (`k ∈ (9.87, 9.88)` at
  `δ = .012`), `ten_quarters_delta`.
* (3.11)–(3.13): `Linear.eq_3_11_average`, `Linear.rmc_relative`, `Linear.eq_3_12`,
  `Linear.eq_3_13_iff` (conditional on the Chapter 3 Calvo condition `Linear.CalvoFOC`).
* (3.18): `Linear.eq_3_18`. Long run (p. 365): `Linear.longrun_lambda`,
  `Linear.longrun_investment`, `Linear.longrun_rmc`, `Linear.longrun_inflation`,
  `Linear.longrun_solve` (iff `σ⁻¹(ρ_y δ k − ρ_k) ≠ 0`), `Linear.longrun_singular`,
  `Linear.longrun_rmc_multiple`, `Linear.longrun_lambda_of_pi`.
* pp. 373–374: `Linear.natural_output`, `Linear.natural_decomposition`, `Linear.eq_3_27`.

## Corrections to the book

* The `q_t` printed below (3.6) (p. 356), `(1 + ω⁻¹) a + ω⁻¹ ν h̄`, is the Hicks-neutral
  definition of Chapter 4, eq. (2.3), p. 249; with labour-augmenting technology the derivative
  gives `q = ω⁻¹[ν h̄ + (1 + ν) a]` (the definition below (3.11)): `Linearise.eq_3_6`;
  counterexamples `Linearise.eq_3_6_printed_q_false` and the fully concrete
  `CobbDouglas.eq_3_6_printed_q_false_concrete`. Footnote 29's "Section 2.1 above" refers to
  Chapter 4, §2.1 (eq. (2.3), p. 249); Chapter 5's own §2.1 does not define `q`.
* (3.7) has `ω q_t` inside the date-`t+1` bracket; it must be `ω E_t q_{t+1}`:
  `Linear.eq_3_7_iff`, counterexample `Linear.eq_3_7_printed_false`.
* p. 365 attributes `λ∞ = ρ_y Y∞ − ρ_k K∞` to "(3.8) and (3.9)"; it is the steady state of (3.7)
  (`Linear.longrun_lambda`, `Linear.longrun_lambda_not_from_38_39`).
* Imprecision: solving the long-run relations needs `ρ_y δ k ≠ ρ_k` (`Linear.longrun_solve`,
  `Linear.longrun_singular`).
-/

namespace Woodford.PolicyResponseDynamics.InvestmentModel

open Filter Topology ExpectationCalculus

/-! ### Log-derivatives along a direction of log deviations -/

/-- Woodford (2003), §3.1, p. 355 (log-linearisation): `c` has log-derivative `e` at `0`, i.e.
`c 0 ≠ 0` and `c'(0) = c(0) e`, so that `log |c|` has derivative `e`. -/
def LogDeriv (c : ℝ → ℝ) (e : ℝ) : Prop := c 0 ≠ 0 ∧ HasDerivAt c (c 0 * e) 0

/-- Woodford (2003), §3.1, p. 355: the level of a variable with steady-state value `b` along the
direction `u` of log deviations, `b e^{ε u}`. -/
noncomputable def dev (b u ε : ℝ) : ℝ := b * Real.exp (ε * u)

/-- Woodford (2003), §3.1, p. 355: `dev b u 0 = b`. -/
@[simp] theorem dev_zero (b u : ℝ) : dev b u 0 = b := by simp [dev]

/-- Woodford (2003), §3.1, p. 355: `dev b u ε > 0` for `b > 0`. -/
theorem dev_pos {b : ℝ} (hb : 0 < b) (u ε : ℝ) : 0 < dev b u ε :=
  mul_pos hb (Real.exp_pos _)

/-- Woodford (2003), §3.1, p. 355: `b e^{ε u}` has log-derivative `u`. -/
theorem logDeriv_dev {b : ℝ} (hb : b ≠ 0) (u : ℝ) : LogDeriv (dev b u) u := by
  refine ⟨by simpa using hb, ?_⟩
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const u).exp).const_mul b
  convert h using 1
  · funext ε
    simp [dev]
  · simp [dev]

/-- Woodford (2003), §3.1, p. 355: the log-derivative gives the derivative of `log c`. -/
theorem LogDeriv.hasDerivAt_log {c : ℝ → ℝ} {e : ℝ} (h : LogDeriv c e) :
    HasDerivAt (fun ε => Real.log (c ε)) e 0 := by
  have h2 := h.2.log h.1
  convert h2 using 1
  field_simp [h.1]

/-- Woodford (2003), §3.1, p. 355: log-derivatives add over products. -/
theorem LogDeriv.mul {c d : ℝ → ℝ} {e f : ℝ} (hc : LogDeriv c e) (hd : LogDeriv d f) :
    LogDeriv (fun ε => c ε * d ε) (e + f) := by
  refine ⟨mul_ne_zero hc.1 hd.1, ?_⟩
  convert hc.2.mul hd.2 using 1
  ring

/-- Woodford (2003), §3.1, p. 355: log-derivatives subtract over quotients. -/
theorem LogDeriv.div {c d : ℝ → ℝ} {e f : ℝ} (hc : LogDeriv c e) (hd : LogDeriv d f) :
    LogDeriv (fun ε => c ε / d ε) (e - f) := by
  refine ⟨div_ne_zero hc.1 hd.1, ?_⟩
  convert hc.2.div hd.2 hd.1 using 1
  field_simp

/-- Woodford (2003), §3.1, p. 355: the log-derivative of a difference is the share-weighted
difference of the log-derivatives. -/
theorem LogDeriv.sub {c d : ℝ → ℝ} {e f : ℝ} (hc : LogDeriv c e) (hd : LogDeriv d f)
    (h0 : c 0 - d 0 ≠ 0) :
    LogDeriv (fun ε => c ε - d ε) ((c 0 * e - d 0 * f) / (c 0 - d 0)) := by
  refine ⟨h0, ?_⟩
  convert HasDerivAt.sub hc.2 hd.2 using 1
  field_simp

/-- Woodford (2003), §3.1, p. 355: chain rule for log-derivatives; the elasticity of `g` at `p`
multiplies the log-derivative of the argument. -/
theorem LogDeriv.comp {c g : ℝ → ℝ} {e g' p : ℝ} (hc : LogDeriv c e) (hg : HasDerivAt g g' p)
    (hp : c 0 = p) (hgp : g p ≠ 0) :
    LogDeriv (fun ε => g (c ε)) (p * g' / g p * e) := by
  refine ⟨show g (c 0) ≠ 0 by rw [hp]; exact hgp, ?_⟩
  have hg' : HasDerivAt g g' (c 0) := by rw [hp]; exact hg
  have h := hg'.comp (0 : ℝ) hc.2
  refine h.congr_deriv ?_
  change g' * (c 0 * e) = g (c 0) * (p * g' / g p * e)
  rw [hp]
  field_simp

/-- Woodford (2003), §3.1, p. 356 (a function of a quantity and an exogenous shift, such as
`v_h(h; ξ)`): chain rule for a function of two variables, the second moving linearly. -/
theorem LogDeriv.comp₂ {c : ℝ → ℝ} {v : ℝ × ℝ → ℝ} {e p vh vx : ℝ} (hc : LogDeriv c e)
    (hv : HasFDerivAt v (vh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vx • ContinuousLinearMap.snd ℝ ℝ ℝ) (p, 0))
    (hp : c 0 = p) (hv0 : v (p, 0) ≠ 0) (u : ℝ) :
    LogDeriv (fun ε => v (c ε, ε * u)) (p * vh / v (p, 0) * e + vx / v (p, 0) * u) := by
  have hpath : HasDerivAt (fun ε : ℝ => (c ε, ε * u)) (c 0 * e, 1 * u) 0 :=
    hc.2.prodMk ((hasDerivAt_id (0 : ℝ)).mul_const u)
  have h00 : (fun ε : ℝ => (c ε, ε * u)) 0 = (p, 0) := by simp [hp]
  have hv' : HasFDerivAt v (vh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vx • ContinuousLinearMap.snd ℝ ℝ ℝ) ((fun ε : ℝ => (c ε, ε * u)) 0) := by
    rw [h00]; exact hv
  have h := hv'.comp_hasDerivAt (0 : ℝ) hpath
  refine ⟨show v (c 0, 0 * u) ≠ 0 by rw [hp, zero_mul]; exact hv0, ?_⟩
  refine h.congr_deriv ?_
  change (vh • ContinuousLinearMap.fst ℝ ℝ ℝ + vx • ContinuousLinearMap.snd ℝ ℝ ℝ) (c 0 * e, 1 * u)
    = v (c 0, 0 * u) * (p * vh / v (p, 0) * e + vx / v (p, 0) * u)
  rw [hp, zero_mul]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  field_simp

/-- Woodford (2003), §3.1, p. 355: rewriting the value of a log-derivative. -/
theorem LogDeriv.of_eq {c : ℝ → ℝ} {e e' : ℝ} (h : LogDeriv c e) (he : e = e') : LogDeriv c e' :=
  he ▸ h

/-! ### The production function (3.1) -/

/-- Woodford (2003), eq. (3.1), p. 353 (restated from the Woodford Chapter 3 project,
`MarginalCost.Technology`): the intensive production function `f`, with `f' > 0`, mapping
`(0, ∞)` bijectively onto `(0, ∞)` with inverse `f⁻¹`. -/
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

/-- Woodford (2003), p. 356 (restated from the Woodford Chapter 3 project): `Ψ(x) = 1/f'(f⁻¹(x))`,
the derivative of the labour requirement `f⁻¹`. -/
noncomputable def Psi (x : ℝ) : ℝ := 1 / T.df (T.finv x)

/-- Woodford (2003), eq. (3.1), p. 353 (restated from the Woodford Chapter 3 project): `f` is
strictly increasing on `(0, ∞)`. -/
theorem f_strictMonoOn : StrictMonoOn T.f (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun h hh => (T.hasDerivAt_f h hh).continuousAt.continuousWithinAt) fun h hh => ?_
  rw [interior_Ioi] at hh
  rw [(T.hasDerivAt_f h hh).deriv]
  exact T.df_pos h hh

/-- Woodford (2003), eq. (3.1), p. 353 (restated from the Woodford Chapter 3 project): `f⁻¹` is
strictly increasing. -/
theorem finv_strictMonoOn : StrictMonoOn T.finv (Set.Ioi 0) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  by_contra hle
  push Not at hle
  have := T.f_strictMonoOn.monotoneOn (T.finv_pos y₂ hy₂) (T.finv_pos y₁ hy₁) hle
  rw [T.f_finv y₁ hy₁, T.f_finv y₂ hy₂] at this
  exact absurd hlt (not_lt.2 this)

/-- Woodford (2003), eq. (3.1), p. 353 (restated from the Woodford Chapter 3 project): `f⁻¹` is
continuous on `(0, ∞)`. -/
theorem finv_continuousAt {y : ℝ} (hy : 0 < y) : ContinuousAt T.finv y :=
  T.finv_strictMonoOn.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hy)
    (Filter.mem_of_superset (Ioi_mem_nhds (T.finv_pos y hy)) fun h hh =>
      ⟨T.f h, T.f_pos h hh, T.finv_f h hh⟩)

/-- Woodford (2003), p. 356 (restated from the Woodford Chapter 3 project):
`(f⁻¹)'(x) = 1/f'(f⁻¹(x)) = Ψ(x)`. -/
theorem hasDerivAt_finv {y : ℝ} (hy : 0 < y) : HasDerivAt T.finv (T.Psi y) y := by
  have h := HasDerivAt.of_local_left_inverse (T.finv_continuousAt hy)
    (T.hasDerivAt_f _ (T.finv_pos y hy)) (T.df_pos _ (T.finv_pos y hy)).ne'
    (by filter_upwards [Ioi_mem_nhds hy] with z hz using T.f_finv z hz)
  rwa [Psi, one_div]

end Technology

/-- Woodford (2003), eq. (3.1), p. 353: output `y = k f(A h / k)` of a firm with capital `k`,
labour-augmenting technology `A` and labour `h`. -/
noncomputable def output (T : Technology) (k A h : ℝ) : ℝ := k * T.f (A * h / k)

/-- Woodford (2003), eqs. (3.1) and (3.5), pp. 353, 356: the labour needed to produce `y` with
capital `k`, `h = f⁻¹(y/k) k / A`. -/
noncomputable def labour (T : Technology) (y k A : ℝ) : ℝ := T.finv (y / k) * k / A

/-- Woodford (2003), eq. (3.1), p. 353: the labour requirement produces `y`. -/
theorem output_labour (T : Technology) {y k A : ℝ} (hy : 0 < y) (hk : 0 < k) (hA : 0 < A) :
    output T k A (labour T y k A) = y := by
  have h : A * (T.finv (y / k) * k / A) / k = T.finv (y / k) := by field_simp
  rw [output, labour, h, T.f_finv _ (div_pos hy hk)]
  field_simp

/-- Woodford (2003), eq. (3.1), p. 353: `labour` inverts `output`, so `y = k f(Ah/k)` if and only
if `h = f⁻¹(y/k) k/A`. -/
theorem labour_output (T : Technology) {k A h : ℝ} (hk : 0 < k) (hA : 0 < A) (hh : 0 < h) :
    labour T (output T k A h) k A = h := by
  have h1 : k * T.f (A * h / k) / k = T.f (A * h / k) := by field_simp
  rw [labour, output, h1, T.finv_f _ (by positivity)]
  field_simp

/-- Woodford (2003), p. 355: the effective labour–capital ratio `h̃ = A h / k` equals
`f⁻¹(y/k)`. -/
theorem effective_ratio (T : Technology) {y k A : ℝ} (hk : 0 < k) (hA : 0 < A) :
    A * labour T y k A / k = T.finv (y / k) := by
  rw [labour]
  field_simp

/-- Woodford (2003), p. 355: the shadow value of capital,
`ρ = w (f(h̃) − h̃ f'(h̃)) / (A f'(h̃))` with `h̃ = f⁻¹(y/k)`. -/
noncomputable def shadowValue (T : Technology) (w y k A : ℝ) : ℝ :=
  w * (T.f (T.finv (y / k)) - T.finv (y / k) * T.df (T.finv (y / k))) /
    (A * T.df (T.finv (y / k)))

/-- Woodford (2003), p. 355: the shadow value of capital is the saving in the wage bill from a
marginal unit of capital, holding output fixed: `∂(w h)/∂k |_y = −ρ`. -/
theorem hasDerivAt_wageBill_k (T : Technology) (w : ℝ) {y k A : ℝ} (hy : 0 < y) (hk : 0 < k)
    (hA : A ≠ 0) :
    HasDerivAt (fun κ => w * labour T y κ A) (-shadowValue T w y k A) k := by
  have hx : HasDerivAt (fun κ : ℝ => y / κ) ((0 * k - y * 1) / k ^ 2) k :=
    (hasDerivAt_const k y).div (hasDerivAt_id k) hk.ne'
  have hfi := (T.hasDerivAt_finv (div_pos hy hk)).comp k hx
  have h := ((hfi.mul (hasDerivAt_id k)).div_const A).const_mul w
  refine h.congr_deriv ?_
  have hD := T.df_pos _ (T.finv_pos _ (div_pos hy hk))
  rw [shadowValue, T.f_finv _ (div_pos hy hk), Technology.Psi]
  simp only [id, Function.comp_apply]
  field_simp
  ring

/-- Woodford (2003), the reciprocal of the elasticity of `f` at `f⁻¹(x)`:
`φ(x) = x / (f⁻¹(x) f'(f⁻¹(x)))` (p. 356); `φ_h` is its steady-state value. -/
noncomputable def phi (T : Technology) (x : ℝ) : ℝ := x / (T.finv x * T.df (T.finv x))

/-- Woodford (2003), eq. (3.4), p. 356: `ρ = (w/A) f⁻¹(y/k) [φ(y/k) − 1]`. -/
theorem eq_3_4 (T : Technology) (w : ℝ) {y k A : ℝ} (hy : 0 < y) (hk : 0 < k) (hA : A ≠ 0) :
    shadowValue T w y k A = w / A * T.finv (y / k) * (phi T (y / k) - 1) := by
  have hx := div_pos hy hk
  have hh := T.finv_pos _ hx
  have hD := T.df_pos _ hh
  rw [shadowValue, phi, T.f_finv _ hx]
  field_simp

/-- Woodford (2003), eq. (3.5), p. 356: the real wage `w = v_h(f⁻¹(y/k) k/A; ξ) / λ`. -/
noncomputable def wage (T : Technology) (vh : ℝ × ℝ → ℝ) (y k A lam ξ : ℝ) : ℝ :=
  vh (labour T y k A, ξ) / lam

/-- Woodford (2003), p. 358: real marginal cost
`s = v_h(f⁻¹(y/k) k/A; ξ) / (λ A f'(f⁻¹(y/k)))`. -/
noncomputable def rmc (T : Technology) (vh : ℝ × ℝ → ℝ) (y k A lam ξ : ℝ) : ℝ :=
  vh (labour T y k A, ξ) / (lam * A * T.df (T.finv (y / k)))

/-- Woodford (2003), eqs. (3.4)–(3.5), p. 356: the shadow value of capital with the wage (3.5). -/
noncomputable def rho (T : Technology) (vh : ℝ × ℝ → ℝ) (y k A lam ξ : ℝ) : ℝ :=
  shadowValue T (wage T vh y k A lam ξ) y k A

/-- Woodford (2003), p. 358: the marginal product of labour is `∂y/∂h = A f'(A h/k)`. -/
theorem hasDerivAt_output_h (T : Technology) {k A h : ℝ} (hk : 0 < k) (hA : 0 < A)
    (hh : 0 < h) : HasDerivAt (fun η => output T k A η) (k * (T.df (A * h / k) * (A / k))) h := by
  have h1 : HasDerivAt (fun η : ℝ => A * η / k) (A * 1 / k) h :=
    ((hasDerivAt_id h).const_mul A).div_const k
  have h2 := (T.hasDerivAt_f _ (by positivity : 0 < A * h / k)).comp h h1
  exact (h2.const_mul k).congr_deriv (by ring)

/-- Woodford (2003), p. 358: real marginal cost is the real wage divided by the marginal product
of labour, `s = w / (A f'(f⁻¹(y/k)))`. -/
theorem rmc_eq_wage_div_mpl (T : Technology) (vh : ℝ × ℝ → ℝ) {y k A lam ξ : ℝ} (hk : 0 < k)
    (hA : 0 < A) (hl : lam ≠ 0) :
    rmc T vh y k A lam ξ = wage T vh y k A lam ξ /
      (k * (T.df (A * labour T y k A / k) * (A / k))) := by
  rw [effective_ratio T hk hA, rmc, wage]
  field_simp

/-- Woodford (2003), pp. 355–358: the shadow value of capital is real marginal cost times
`y/k − h̃ f'(h̃)`, the output–capital ratio net of labour's marginal contribution. -/
theorem rho_eq_rmc_mul (T : Technology) (vh : ℝ × ℝ → ℝ) {y k A lam ξ : ℝ} (hy : 0 < y)
    (hk : 0 < k) (hA : A ≠ 0) (hl : lam ≠ 0) :
    rho T vh y k A lam ξ = rmc T vh y k A lam ξ *
      (y / k - T.finv (y / k) * T.df (T.finv (y / k))) := by
  have hD := T.df_pos _ (T.finv_pos _ (div_pos hy hk))
  rw [rho, shadowValue, rmc, wage, T.f_finv _ (div_pos hy hk)]
  field_simp

/-! ### Elasticities at the steady state and the linear coefficients -/

/-- Woodford (2003), p. 356: `ω_p`, the negative of the elasticity of `f'(f⁻¹(x))` with respect
to `x` at `x̄`, given `f''(f⁻¹(x̄)) = d2f`. -/
noncomputable def omegaP (T : Technology) (d2f x : ℝ) : ℝ :=
  -(x * (d2f * T.Psi x) / T.df (T.finv x))

/-- Woodford (2003), p. 356: `ν`, the elasticity of `v_h` with respect to hours at the steady
state `(L̄, 0)`, given `∂_h v_h = vhh`. -/
noncomputable def nuOf (vh : ℝ × ℝ → ℝ) (vhh L : ℝ) : ℝ := L * vhh / vh (L, 0)

/-- Woodford (2003), p. 358: the semi-elasticity of `v_h` with respect to the preference shock
`ξ`, given `∂_ξ v_h = vhx`. The labour-supply shift `h̄` of p. 358 satisfies `ν h̄ = −xiOf · ξ`. -/
noncomputable def xiOf (vh : ℝ × ℝ → ℝ) (vhx L : ℝ) : ℝ := vhx / vh (L, 0)

/-- Woodford (2003), p. 358: `ω = ω_w + ω_p = ν φ_h + ω_p`, the elasticity of real marginal cost
with respect to own output. -/
def omega (ν φh ωp : ℝ) : ℝ := ν * φh + ωp

/-- Woodford (2003), p. 356, below (3.7): `ρ_y = ν φ_h + φ_h/(φ_h − 1) ω_p`. -/
noncomputable def rhoY (ν φh ωp : ℝ) : ℝ := ν * φh + φh / (φh - 1) * ωp

/-- Woodford (2003), p. 356, below (3.7): `ρ_k = ρ_y − ν`. -/
noncomputable def rhoK (ν φh ωp : ℝ) : ℝ := rhoY ν φh ωp - ν

/-- Woodford (2003), p. 358, below (3.11): the composite disturbance
`q = ω⁻¹ [ν h̄ + (1 + ν) a]` (the correct definition for labour-augmenting technology). -/
noncomputable def qDist (ω ν hbar a : ℝ) : ℝ := ω⁻¹ * (ν * hbar + (1 + ν) * a)

/-- Woodford (2003), p. 356, below (3.6), AS PRINTED: `q = (1 + ω⁻¹) a + ω⁻¹ ν h̄`, the
Hicks-neutral definition of Chapter 4, eq. (2.3), p. 249. It is wrong here
(`eq_3_6_printed_q_false`). -/
noncomputable def qPrinted (ω ν hbar a : ℝ) : ℝ := (1 + ω⁻¹) * a + ω⁻¹ * ν * hbar

/-- Woodford (2003), p. 356: `ρ_y − ρ_k = ν`. -/
theorem rhoY_sub_rhoK (ν φh ωp : ℝ) : rhoY ν φh ωp - rhoK ν φh ωp = ν := by
  rw [rhoK]; ring

/-- Woodford (2003), p. 356: `ρ_k = ν(φ_h − 1) + φ_h/(φ_h − 1) ω_p`. -/
theorem rhoK_eq (ν φh ωp : ℝ) : rhoK ν φh ωp = ν * (φh - 1) + φh / (φh - 1) * ωp := by
  rw [rhoK, rhoY]; ring

/-- Woodford (2003), p. 356: `ρ_y > ρ_k > 0` when `ν > 0`, `φ_h > 1` and `ω_p ≥ 0`. -/
theorem rhoY_gt_rhoK_pos {ν φh ωp : ℝ} (hν : 0 < ν) (hφ : 1 < φh) (hω : 0 ≤ ωp) :
    rhoK ν φh ωp < rhoY ν φh ωp ∧ 0 < rhoK ν φh ωp := by
  refine ⟨by linarith [rhoY_sub_rhoK ν φh ωp], ?_⟩
  rw [rhoK_eq]
  have h1 : 0 < ν * (φh - 1) := mul_pos hν (by linarith)
  have h2 : 0 ≤ φh / (φh - 1) * ωp := mul_nonneg (div_nonneg (by linarith) (by linarith)) hω
  linarith

/-- Woodford (2003), p. 356: `ρ_y = ω + ω_p/(φ_h − 1)`. -/
theorem rhoY_eq_omega_add {ν φh ωp : ℝ} (hφ : φh ≠ 1) :
    rhoY ν φh ωp = omega ν φh ωp + ωp / (φh - 1) := by
  have : φh - 1 ≠ 0 := sub_ne_zero.2 hφ
  rw [rhoY, omega]
  field_simp
  ring

/-- Woodford (2003), p. 358: `ω − ν = ν(φ_h − 1) + ω_p > 0` when `ν > 0`, `φ_h > 1`,
`ω_p ≥ 0`. -/
theorem omega_sub_nu_pos {ν φh ωp : ℝ} (hν : 0 < ν) (hφ : 1 < φh) (hω : 0 ≤ ωp) :
    0 < omega ν φh ωp - ν := by
  rw [omega]
  nlinarith

/-! ### (3.6) and (3.11) as exact derivatives at the steady state

The steady state has output `ȳ`, capital `K̄`, marginal utility `λ̄`, technology `Ā = 1` and
preference shock `ξ̄ = 0`. A direction of log deviations `(ŷ, k̂, λ̂, a, ξ̂)` moves the variables
along `ε ↦ (ȳ e^{εŷ}, K̄ e^{εk̂}, e^{εa}, λ̄ e^{ελ̂}, ε ξ̂)`. -/

namespace Linearise

variable {T : Technology} {vh : ℝ × ℝ → ℝ} {d2f vhh vhx ybar Kbar lbar : ℝ}

/-- Woodford (2003), p. 356: the output–capital ratio `y/k` has log-derivative `ŷ − k̂`. -/
theorem logDeriv_ratio (hy : 0 < ybar) (hK : 0 < Kbar) (yh kh : ℝ) :
    LogDeriv (fun ε => dev ybar yh ε / dev Kbar kh ε) (yh - kh) :=
  (logDeriv_dev hy.ne' yh).div (logDeriv_dev hK.ne' kh)

/-- Woodford (2003), p. 356: `h̃ = f⁻¹(y/k)` has log-derivative `φ_h (ŷ − k̂)`. -/
theorem logDeriv_finv (hy : 0 < ybar) (hK : 0 < Kbar) (yh kh : ℝ) :
    LogDeriv (fun ε => T.finv (dev ybar yh ε / dev Kbar kh ε))
      (phi T (ybar / Kbar) * (yh - kh)) := by
  have hx : 0 < ybar / Kbar := div_pos hy hK
  have hh := T.finv_pos _ hx
  have hD := T.df_pos _ hh
  refine ((logDeriv_ratio hy hK yh kh).comp (T.hasDerivAt_finv hx) (by simp) hh.ne').of_eq ?_
  rw [phi, Technology.Psi]
  field_simp

/-- Woodford (2003), p. 356: `f'(f⁻¹(y/k))` has log-derivative `−ω_p (ŷ − k̂)`. -/
theorem logDeriv_dfinv (hy : 0 < ybar) (hK : 0 < Kbar)
    (hd2f : HasDerivAt T.df d2f (T.finv (ybar / Kbar))) (yh kh : ℝ) :
    LogDeriv (fun ε => T.df (T.finv (dev ybar yh ε / dev Kbar kh ε)))
      (-omegaP T d2f (ybar / Kbar) * (yh - kh)) := by
  have hx : 0 < ybar / Kbar := div_pos hy hK
  have hD := T.df_pos _ (T.finv_pos _ hx)
  have hg : HasDerivAt (fun x => T.df (T.finv x)) (d2f * T.Psi (ybar / Kbar)) (ybar / Kbar) :=
    hd2f.comp (ybar / Kbar) (T.hasDerivAt_finv hx)
  refine ((logDeriv_ratio hy hK yh kh).comp hg (by simp) hD.ne').of_eq ?_
  rw [omegaP]
  ring

/-- Woodford (2003), eq. (3.5), p. 356: hours `f⁻¹(y/k) k/A` have log-derivative
`φ_h (ŷ − k̂) + k̂ − a`. -/
theorem logDeriv_labour (hy : 0 < ybar) (hK : 0 < Kbar) (yh kh a : ℝ) :
    LogDeriv (fun ε => labour T (dev ybar yh ε) (dev Kbar kh ε) (dev 1 a ε))
      (phi T (ybar / Kbar) * (yh - kh) + kh - a) :=
  ((logDeriv_finv hy hK yh kh).mul (logDeriv_dev hK.ne' kh)).div (logDeriv_dev one_ne_zero a)

/-- Woodford (2003), eq. (3.11), p. 358: real marginal cost has log-derivative
`ω(ŷ − k̂) + ν k̂ − λ̂ − (1 + ν) a + (v_hξ/v_h) ξ̂` (raw form). -/
theorem logDeriv_rmc (hy : 0 < ybar) (hK : 0 < Kbar) (hl : 0 < lbar)
    (hd2f : HasDerivAt T.df d2f (T.finv (ybar / Kbar)))
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhx • ContinuousLinearMap.snd ℝ ℝ ℝ) (labour T ybar Kbar 1, 0))
    (hv0 : vh (labour T ybar Kbar 1, 0) ≠ 0) (yh kh lh a xh : ℝ) :
    LogDeriv (fun ε => rmc T vh (dev ybar yh ε) (dev Kbar kh ε) (dev 1 a ε) (dev lbar lh ε)
      (ε * xh))
      (omega (nuOf vh vhh (labour T ybar Kbar 1)) (phi T (ybar / Kbar))
        (omegaP T d2f (ybar / Kbar)) * (yh - kh) + nuOf vh vhh (labour T ybar Kbar 1) * kh - lh
        - (1 + nuOf vh vhh (labour T ybar Kbar 1)) * a
        + xiOf vh vhx (labour T ybar Kbar 1) * xh) := by
  have hv := (logDeriv_labour (T := T) hy hK yh kh a).comp₂ hvh (by simp) hv0 xh
  have hden := ((logDeriv_dev hl.ne' lh).mul (logDeriv_dev one_ne_zero a)).mul
    (logDeriv_dfinv hy hK hd2f yh kh)
  refine (hv.div hden).of_eq ?_
  rw [nuOf, xiOf, omega]
  ring

/-- Woodford (2003), p. 356: `y/k − f⁻¹(y/k) f'(f⁻¹(y/k))` has log-derivative
`ω_p/(φ_h − 1) (ŷ − k̂)`. -/
theorem logDeriv_netRatio (hy : 0 < ybar) (hK : 0 < Kbar)
    (hd2f : HasDerivAt T.df d2f (T.finv (ybar / Kbar))) (hφ : phi T (ybar / Kbar) ≠ 1)
    (yh kh : ℝ) :
    LogDeriv (fun ε => dev ybar yh ε / dev Kbar kh ε -
      T.finv (dev ybar yh ε / dev Kbar kh ε) * T.df (T.finv (dev ybar yh ε / dev Kbar kh ε)))
      (omegaP T d2f (ybar / Kbar) / (phi T (ybar / Kbar) - 1) * (yh - kh)) := by
  have hx : 0 < ybar / Kbar := div_pos hy hK
  have hh := T.finv_pos _ hx
  have hD := T.df_pos _ hh
  have hφ1 : phi T (ybar / Kbar) - 1 ≠ 0 := sub_ne_zero.2 hφ
  have hne : ybar / Kbar - T.finv (ybar / Kbar) * T.df (T.finv (ybar / Kbar)) ≠ 0 := by
    intro h0
    apply hφ
    rw [phi, div_eq_one_iff_eq (by positivity)]
    linarith
  have h := (logDeriv_ratio hy hK yh kh).sub
    ((logDeriv_finv (T := T) hy hK yh kh).mul (logDeriv_dfinv hy hK hd2f yh kh))
    (by simpa using hne)
  refine h.of_eq ?_
  simp only [dev_zero]
  rw [phi] at hφ1 ⊢
  field_simp
  ring

/-- Woodford (2003), eq. (3.6), p. 356: the shadow value of capital (3.4) with the wage (3.5)
has log-derivative `ρ_y(ŷ − k̂) + ν k̂ − λ̂ − (1 + ν) a + (v_hξ/v_h) ξ̂` (raw form). -/
theorem logDeriv_rho (hy : 0 < ybar) (hK : 0 < Kbar) (hl : 0 < lbar)
    (hd2f : HasDerivAt T.df d2f (T.finv (ybar / Kbar)))
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhx • ContinuousLinearMap.snd ℝ ℝ ℝ) (labour T ybar Kbar 1, 0))
    (hv0 : vh (labour T ybar Kbar 1, 0) ≠ 0) (hφ : phi T (ybar / Kbar) ≠ 1)
    (yh kh lh a xh : ℝ) :
    LogDeriv (fun ε => rho T vh (dev ybar yh ε) (dev Kbar kh ε) (dev 1 a ε) (dev lbar lh ε)
      (ε * xh))
      (rhoY (nuOf vh vhh (labour T ybar Kbar 1)) (phi T (ybar / Kbar))
        (omegaP T d2f (ybar / Kbar)) * (yh - kh) + nuOf vh vhh (labour T ybar Kbar 1) * kh - lh
        - (1 + nuOf vh vhh (labour T ybar Kbar 1)) * a
        + xiOf vh vhx (labour T ybar Kbar 1) * xh) := by
  have hfun : (fun ε => rho T vh (dev ybar yh ε) (dev Kbar kh ε) (dev 1 a ε) (dev lbar lh ε)
      (ε * xh)) = fun ε => rmc T vh (dev ybar yh ε) (dev Kbar kh ε) (dev 1 a ε)
      (dev lbar lh ε) (ε * xh) * (dev ybar yh ε / dev Kbar kh ε -
      T.finv (dev ybar yh ε / dev Kbar kh ε) *
        T.df (T.finv (dev ybar yh ε / dev Kbar kh ε))) := by
    funext ε
    exact rho_eq_rmc_mul T vh (dev_pos hy _ _) (dev_pos hK _ _)
      (dev_pos one_pos _ _).ne' (dev_pos hl _ _).ne'
  rw [hfun]
  refine ((logDeriv_rmc hy hK hl hd2f hvh hv0 yh kh lh a xh).mul
    (logDeriv_netRatio hy hK hd2f hφ yh kh)).of_eq ?_
  rw [rhoY_eq_omega_add hφ]
  ring

/-- Woodford (2003), eq. (3.11), p. 358, as an EXACT derivative: with the labour-supply shift
`h̄` defined by `ν h̄ = −(v_hξ/v_h) ξ̂`, the log of real marginal cost has derivative
`ω(ŷ − k̂) + ν k̂ − λ̂ − [ν h̄ + (1 + ν) a]` at the steady state. -/
theorem eq_3_11 {ν φh ωp ξe hbar : ℝ} (hy : 0 < ybar) (hK : 0 < Kbar) (hl : 0 < lbar)
    (hd2f : HasDerivAt T.df d2f (T.finv (ybar / Kbar)))
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhx • ContinuousLinearMap.snd ℝ ℝ ℝ) (labour T ybar Kbar 1, 0))
    (hv0 : vh (labour T ybar Kbar 1, 0) ≠ 0) (hν : nuOf vh vhh (labour T ybar Kbar 1) = ν)
    (hφ : phi T (ybar / Kbar) = φh) (hωp : omegaP T d2f (ybar / Kbar) = ωp)
    (hξ : xiOf vh vhx (labour T ybar Kbar 1) = ξe) (yh kh lh a xh : ℝ)
    (hh : ν * hbar = -(ξe * xh)) :
    HasDerivAt (fun ε => Real.log (rmc T vh (dev ybar yh ε) (dev Kbar kh ε) (dev 1 a ε)
      (dev lbar lh ε) (ε * xh)))
      (omega ν φh ωp * (yh - kh) + ν * kh - lh - (ν * hbar + (1 + ν) * a)) 0 := by
  refine ((logDeriv_rmc hy hK hl hd2f hvh hv0 yh kh lh a xh).of_eq ?_).hasDerivAt_log
  rw [hν, hφ, hωp, hξ, hh]
  ring

/-- Woodford (2003), eq. (3.11), p. 358, in terms of `q = ω⁻¹[ν h̄ + (1 + ν) a]`:
`ŝ = ω(ŷ − k̂) + ν k̂ − λ̂ − ω q`. -/
theorem eq_3_11_q {ν φh ωp ξe hbar : ℝ} (hy : 0 < ybar) (hK : 0 < Kbar) (hl : 0 < lbar)
    (hd2f : HasDerivAt T.df d2f (T.finv (ybar / Kbar)))
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhx • ContinuousLinearMap.snd ℝ ℝ ℝ) (labour T ybar Kbar 1, 0))
    (hv0 : vh (labour T ybar Kbar 1, 0) ≠ 0) (hν : nuOf vh vhh (labour T ybar Kbar 1) = ν)
    (hφ : phi T (ybar / Kbar) = φh) (hωp : omegaP T d2f (ybar / Kbar) = ωp)
    (hξ : xiOf vh vhx (labour T ybar Kbar 1) = ξe) (hω : omega ν φh ωp ≠ 0) (yh kh lh a xh : ℝ)
    (hh : ν * hbar = -(ξe * xh)) :
    HasDerivAt (fun ε => Real.log (rmc T vh (dev ybar yh ε) (dev Kbar kh ε) (dev 1 a ε)
      (dev lbar lh ε) (ε * xh)))
      (omega ν φh ωp * (yh - kh) + ν * kh - lh - omega ν φh ωp * qDist (omega ν φh ωp) ν hbar a)
      0 := by
  refine (eq_3_11 hy hK hl hd2f hvh hv0 hν hφ hωp hξ yh kh lh a xh hh).congr_deriv ?_
  rw [qDist, ← mul_assoc, mul_inv_cancel₀ hω, one_mul]

/-- Woodford (2003), eq. (3.6), p. 356, CORRECTED, as an EXACT derivative: the log of the shadow
value of capital has derivative `ρ_y(ŷ − k̂) + ν k̂ − λ̂ − ω q` with
`q = ω⁻¹[ν h̄ + (1 + ν) a]` (the definition below (3.11), not the one printed below (3.6)). -/
theorem eq_3_6 {ν φh ωp ξe hbar : ℝ} (hy : 0 < ybar) (hK : 0 < Kbar) (hl : 0 < lbar)
    (hd2f : HasDerivAt T.df d2f (T.finv (ybar / Kbar)))
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhx • ContinuousLinearMap.snd ℝ ℝ ℝ) (labour T ybar Kbar 1, 0))
    (hv0 : vh (labour T ybar Kbar 1, 0) ≠ 0) (hν : nuOf vh vhh (labour T ybar Kbar 1) = ν)
    (hφ : phi T (ybar / Kbar) = φh) (hωp : omegaP T d2f (ybar / Kbar) = ωp)
    (hξ : xiOf vh vhx (labour T ybar Kbar 1) = ξe) (hφ1 : φh ≠ 1) (hω : omega ν φh ωp ≠ 0)
    (yh kh lh a xh : ℝ) (hh : ν * hbar = -(ξe * xh)) :
    HasDerivAt (fun ε => Real.log (rho T vh (dev ybar yh ε) (dev Kbar kh ε) (dev 1 a ε)
      (dev lbar lh ε) (ε * xh)))
      (rhoY ν φh ωp * (yh - kh) + ν * kh - lh - omega ν φh ωp * qDist (omega ν φh ωp) ν hbar a)
      0 := by
  refine ((logDeriv_rho hy hK hl hd2f hvh hv0 (hφ ▸ hφ1) yh kh lh a xh).of_eq ?_).hasDerivAt_log
  rw [qDist, ← mul_assoc, mul_inv_cancel₀ hω, one_mul, hν, hφ, hωp, hξ, hh]
  ring

/-- Woodford (2003), eq. (3.6), p. 356 — the q definition AS PRINTED is FALSE: in the direction
of a pure technology shock (`a = 1`, all other deviations `0`) the log of the shadow value of
capital does NOT have derivative `ρ_y·0 + ν·0 − 0 − ω q` with the printed
`q = (1 + ω⁻¹) a + ω⁻¹ ν h̄`, whenever `ν > 0`, `φ_h > 1`, `ω_p ≥ 0` (the true derivative is
`−(1 + ν)`, the printed one `−(1 + ω)`, and `ω − ν = ν(φ_h − 1) + ω_p > 0`; this holds for
every `ω_p ≥ 0`, in particular for the model's `omegaP`). -/
theorem eq_3_6_printed_q_false {ν φh ωp : ℝ} (hy : 0 < ybar) (hK : 0 < Kbar) (hl : 0 < lbar)
    (hd2f : HasDerivAt T.df d2f (T.finv (ybar / Kbar)))
    (hvh : HasFDerivAt vh (vhh • ContinuousLinearMap.fst ℝ ℝ ℝ +
      vhx • ContinuousLinearMap.snd ℝ ℝ ℝ) (labour T ybar Kbar 1, 0))
    (hv0 : vh (labour T ybar Kbar 1, 0) ≠ 0) (hν : nuOf vh vhh (labour T ybar Kbar 1) = ν)
    (hφ : phi T (ybar / Kbar) = φh)
    (hν0 : 0 < ν) (hφ1 : 1 < φh) (hωp0 : 0 ≤ ωp) :
    ¬ HasDerivAt (fun ε => Real.log (rho T vh (dev ybar 0 ε) (dev Kbar 0 ε) (dev 1 1 ε)
      (dev lbar 0 ε) (ε * 0)))
      (rhoY ν φh ωp * (0 - 0) + ν * 0 - 0 - omega ν φh ωp * qPrinted (omega ν φh ωp) ν 0 1) 0 := by
  intro hprinted
  have htrue := (logDeriv_rho hy hK hl hd2f hvh hv0 (hφ ▸ hφ1.ne') 0 0 0 1 0).hasDerivAt_log
  have heq := htrue.unique hprinted
  have hpos := omega_sub_nu_pos hν0 hφ1 hωp0
  have hω : omega ν φh ωp ≠ 0 := by
    have : 0 < omega ν φh ωp := by linarith
    exact this.ne'
  rw [hν, qPrinted] at heq
  simp only [sub_self, mul_zero, add_zero, zero_sub, mul_one] at heq
  rw [mul_add, mul_one, mul_inv_cancel₀ hω] at heq
  linarith

end Linearise

/-! ### Investment adjustment costs and the investment first-order condition (3.3) -/

/-- Woodford (2003), §3.1, p. 354: the investment technology `I_t = I(k_{t+1}/k_t) k_t`, with
`I(1) = δ`, `I'(1) = 1`, `I''(1) = ε_ψ`. Only differentiability of `I` and twice-differentiability
at `1` are required (weaker than the book's smooth convex `I`). -/
structure AdjCost where
  I : ℝ → ℝ
  dI : ℝ → ℝ
  δ : ℝ
  εψ : ℝ
  hasDerivAt_I : ∀ x : ℝ, HasDerivAt I (dI x) x
  hasDerivAt_dI : HasDerivAt dI εψ 1
  I_one : I 1 = δ
  dI_one : dI 1 = 1

namespace AdjCost

variable (A : AdjCost)

/-- Woodford (2003), p. 355: the continuation term `G(x) = x I'(x) − I(x)` of the investment
first-order condition (the saving in future investment from a higher capital stock). -/
noncomputable def G (x : ℝ) : ℝ := x * A.dI x - A.I x

/-- Woodford (2003), p. 355: `G(1) = 1 − δ`. -/
theorem G_one : A.G 1 = 1 - A.δ := by
  rw [G, A.dI_one, A.I_one, one_mul]

/-- Woodford (2003), p. 355: `G'(1) = I'(1) + I''(1) − I'(1) = ε_ψ`. -/
theorem hasDerivAt_G : HasDerivAt A.G A.εψ 1 := by
  have h := HasDerivAt.sub ((hasDerivAt_id (1 : ℝ)).mul A.hasDerivAt_dI) (A.hasDerivAt_I 1)
  refine h.congr_deriv ?_
  simp [A.dI_one]

/-- Woodford (2003), p. 354: the quadratic adjustment cost `I(x) = δ + (x − 1) + ε_ψ (x − 1)²/2`
satisfies all the hypotheses (so `AdjCost` is not vacuous). -/
noncomputable def quadratic (δ εψ : ℝ) : AdjCost where
  I := fun x => δ + (x - 1) + εψ * (x - 1) ^ 2 / 2
  dI := fun x => 1 + εψ * (x - 1)
  δ := δ
  εψ := εψ
  hasDerivAt_I := fun x => by
    have h := ((hasDerivAt_id x).sub_const 1).const_add δ |>.add
      ((((hasDerivAt_id x).sub_const 1).pow 2).const_mul εψ |>.div_const 2)
    refine h.congr_deriv ?_
    simp
    ring
  hasDerivAt_dI := by
    have h := (((hasDerivAt_id (1 : ℝ)).sub_const 1).const_mul εψ).const_add 1
    refine h.congr_deriv ?_
    simp
  I_one := by simp
  dI_one := by simp

end AdjCost

/-- Woodford (2003), §3.1, p. 355: the ratio `b e^{εu} / (b e^{εv})` has derivative `u − v`. -/
theorem hasDerivAt_devRatio {b : ℝ} (hb : b ≠ 0) (u v : ℝ) :
    HasDerivAt (fun ε => dev b u ε / dev b v ε) (u - v) 0 := by
  have h := ((logDeriv_dev hb u).div (logDeriv_dev hb v)).2
  refine h.congr_deriv ?_
  simp [hb]

/-- Woodford (2003), §3.1, p. 355: the ratio is `1` at the steady state. -/
theorem devRatio_zero {b : ℝ} (hb : b ≠ 0) (u v : ℝ) : dev b u 0 / dev b v 0 = 1 := by
  simp [hb]

namespace FOC

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 355: the integrand of the investment first-order condition,
`β (λ_{t+1}/λ_t) [ρ_{t+1} + x_{t+2} I'(x_{t+2}) − I(x_{t+2})]` with `x_{t+2} = k_{t+2}/k_{t+1}`,
along the direction of log deviations `(λ̂, ρ̂, k̂)` (steady state `λ̄, ρ̄, K̄`). -/
noncomputable def integrand (A : AdjCost) (β lbar rbar Kbar : ℝ) (lam r k : ℕ → Ω → ℝ) (t : ℕ)
    (ε : ℝ) : Ω → ℝ := fun ω =>
  β * (dev lbar (lam (t + 1) ω) ε / dev lbar (lam t ω) ε) *
    (dev rbar (r (t + 1) ω) ε + A.G (dev Kbar (k (t + 2) ω) ε / dev Kbar (k (t + 1) ω) ε))

/-- Woodford (2003), p. 355: the residual of the investment first-order condition
`I'(k_{t+1}/k_t) − E_t[β (λ_{t+1}/λ_t){ρ_{t+1} + x_{t+2} I'(x_{t+2}) − I(x_{t+2})}]`, the real
stochastic discount factor being `β λ_{t+1}/λ_t`. -/
noncomputable def residual (A : AdjCost) (β lbar rbar Kbar : ℝ) (lam r k : ℕ → Ω → ℝ) (t : ℕ)
    (ε : ℝ) (ω : Ω) : ℝ :=
  A.dI (dev Kbar (k (t + 1) ω) ε / dev Kbar (k t ω) ε) -
    𝔼.E t (integrand A β lbar rbar Kbar lam r k t ε) ω

/-- Woodford (2003), p. 355: the derivative of the integrand in each state,
`β(ρ̄ + 1 − δ)(λ̂_{t+1} − λ̂_t) + β ρ̄ ρ̂_{t+1} + β ε_ψ (k̂_{t+2} − k̂_{t+1})`. -/
noncomputable def integrandDeriv (A : AdjCost) (β rbar : ℝ) (lam r k : ℕ → Ω → ℝ) (t : ℕ) :
    Ω → ℝ := fun ω =>
  β * (rbar + 1 - A.δ) * (lam (t + 1) ω - lam t ω) + β * rbar * r (t + 1) ω +
    β * A.εψ * (k (t + 2) ω - k (t + 1) ω)

omit 𝔼 in
/-- Woodford (2003), p. 355: the integrand has derivative `integrandDeriv` in every state. -/
theorem hasDerivAt_integrand (A : AdjCost) {β lbar rbar Kbar : ℝ} (hl : lbar ≠ 0)
    (hK : Kbar ≠ 0) (lam r k : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    HasDerivAt (fun ε => integrand A β lbar rbar Kbar lam r k t ε ω)
      (integrandDeriv A β rbar lam r k t ω) 0 := by
  have hlm := (hasDerivAt_devRatio hl (lam (t + 1) ω) (lam t ω)).const_mul β
  have hG' : HasDerivAt A.G A.εψ (dev Kbar (k (t + 2) ω) 0 / dev Kbar (k (t + 1) ω) 0) := by
    rw [devRatio_zero hK]; exact A.hasDerivAt_G
  have hG := hG'.comp (0 : ℝ) (hasDerivAt_devRatio hK (k (t + 2) ω) (k (t + 1) ω))
  have hr' : HasDerivAt (fun ε => dev rbar (r (t + 1) ω) ε) (rbar * r (t + 1) ω) 0 := by
    have h2 := (((hasDerivAt_id (0 : ℝ)).mul_const (r (t + 1) ω)).exp).const_mul rbar
    refine h2.congr_deriv ?_
    simp
  have h := hlm.mul (hr'.add hG)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Function.comp_apply, dev_zero, div_self hl, div_self hK, A.G_one,
    integrandDeriv]
  ring

/-- Woodford (2003), eq. (3.3), p. 355: the log-linearised investment first-order condition
`λ̂_t + ε_ψ(k̂_{t+1} − k̂_t) = E_t λ̂_{t+1} + [1 − β(1 − δ)] E_t ρ̂_{t+1}
  + β ε_ψ E_t(k̂_{t+2} − k̂_{t+1})`. -/
def Eq33 (β δ εψ : ℝ) (lam r k : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  lam t + εψ • (k (t + 1) - k t) = 𝔼.E t (lam (t + 1)) + (1 - β * (1 - δ)) • 𝔼.E t (r (t + 1))
    + (β * εψ) • (𝔼.E t (k (t + 2)) - k (t + 1))

/-- Woodford (2003), p. 355: the expectation of `integrandDeriv` given `β(ρ̄ + 1 − δ) = 1`,
`λ̂_t` and `k̂_{t+1}` known at `t`. -/
theorem E_integrandDeriv (A : AdjCost) {β rbar : ℝ} (hss : β * (rbar + 1 - A.δ) = 1)
    {lam r k : ℕ → Ω → ℝ} {t : ℕ} (hlam : 𝔼.E t (lam t) = lam t)
    (hk : 𝔼.E t (k (t + 1)) = k (t + 1)) :
    𝔼.E t (integrandDeriv A β rbar lam r k t) = 𝔼.E t (lam (t + 1)) - lam t
      + (1 - β * (1 - A.δ)) • 𝔼.E t (r (t + 1)) + (β * A.εψ) • (𝔼.E t (k (t + 2)) - k (t + 1)) := by
  have hfun : integrandDeriv A β rbar lam r k t = (β * (rbar + 1 - A.δ)) • (lam (t + 1) - lam t)
      + (β * rbar) • r (t + 1) + (β * A.εψ) • (k (t + 2) - k (t + 1)) := by
    funext ω
    simp [integrandDeriv]
  have hbr : β * rbar = 1 - β * (1 - A.δ) := by linarith
  rw [hfun, hss, hbr, map_add, map_add, map_smul, map_smul, map_smul, map_sub, map_sub, hlam, hk,
    one_smul]

/-- Woodford (2003), p. 355: at the steady state `β(ρ̄ + 1 − δ) = 1` the first-order condition
holds exactly (`I'(1) = 1`). -/
theorem residual_zero (A : AdjCost) {β lbar rbar Kbar : ℝ} (hl : lbar ≠ 0) (hK : Kbar ≠ 0)
    (hss : β * (rbar + 1 - A.δ) = 1) (lam r k : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    residual 𝔼 A β lbar rbar Kbar lam r k t 0 ω = 0 := by
  have hint : integrand A β lbar rbar Kbar lam r k t 0 = fun _ => 1 := by
    funext ω'
    simp only [integrand, dev_zero, div_self hl, div_self hK, A.G_one]
    linarith
  rw [residual, hint, 𝔼.const, devRatio_zero hK, A.dI_one]
  simp

/-- Woodford (2003), eq. (3.3), p. 355, as an EXACT derivative on a finite state space: the
residual of the nonlinear investment first-order condition has derivative
`[λ̂_t + ε_ψ(k̂_{t+1} − k̂_t)] − [E_t λ̂_{t+1} + (1 − β(1 − δ)) E_t ρ̂_{t+1}
  + β ε_ψ E_t(k̂_{t+2} − k̂_{t+1})]` at the steady state, using `β(ρ̄ + 1 − δ) = 1`. -/
theorem eq_3_3_finite [Finite Ω] (A : AdjCost) {β lbar rbar Kbar : ℝ} (hl : lbar ≠ 0)
    (hK : Kbar ≠ 0) (hss : β * (rbar + 1 - A.δ) = 1) {lam r k : ℕ → Ω → ℝ} {t : ℕ}
    (hlam : 𝔼.E t (lam t) = lam t) (hk : 𝔼.E t (k (t + 1)) = k (t + 1)) (ω : Ω) :
    HasDerivAt (fun ε => residual 𝔼 A β lbar rbar Kbar lam r k t ε ω)
      ((lam t + A.εψ • (k (t + 1) - k t)) ω - (𝔼.E t (lam (t + 1))
        + (1 - β * (1 - A.δ)) • 𝔼.E t (r (t + 1))
        + (β * A.εψ) • (𝔼.E t (k (t + 2)) - k (t + 1))) ω) 0 := by
  have hL' : HasDerivAt A.dI A.εψ (dev Kbar (k (t + 1) ω) 0 / dev Kbar (k t ω) 0) := by
    rw [devRatio_zero hK]; exact A.hasDerivAt_dI
  have hL := hL'.comp (0 : ℝ) (hasDerivAt_devRatio hK (k (t + 1) ω) (k t ω))
  have hE := hasDerivAt_E 𝔼
    (hasDerivAt_integrand A (β := β) (rbar := rbar) hl hK lam r k t) t ω
  have h := HasDerivAt.sub hL hE
  refine h.congr_deriv ?_
  rw [E_integrandDeriv 𝔼 A hss hlam hk]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (3.3), p. 355, as an EXACT derivative on a general state space, provided
the integrand's second-order remainder is uniformly `O(ε²)` (true e.g. for bounded deviations
and `I` with Lipschitz derivative near `1`). -/
theorem eq_3_3 (A : AdjCost) {β lbar rbar Kbar C δ : ℝ} (hK : Kbar ≠ 0)
    (hss : β * (rbar + 1 - A.δ) = 1) {lam r k : ℕ → Ω → ℝ} {t : ℕ}
    (hlam : 𝔼.E t (lam t) = lam t) (hk : 𝔼.E t (k (t + 1)) = k (t + 1)) (hδ : 0 < δ)
    (hrem : ∀ h, |h| < δ → ∀ ω, |integrand A β lbar rbar Kbar lam r k t (0 + h) ω -
      integrand A β lbar rbar Kbar lam r k t 0 ω - h * integrandDeriv A β rbar lam r k t ω|
        ≤ C * h ^ 2) (ω : Ω) :
    HasDerivAt (fun ε => residual 𝔼 A β lbar rbar Kbar lam r k t ε ω)
      ((lam t + A.εψ • (k (t + 1) - k t)) ω - (𝔼.E t (lam (t + 1))
        + (1 - β * (1 - A.δ)) • 𝔼.E t (r (t + 1))
        + (β * A.εψ) • (𝔼.E t (k (t + 2)) - k (t + 1))) ω) 0 := by
  have hL' : HasDerivAt A.dI A.εψ (dev Kbar (k (t + 1) ω) 0 / dev Kbar (k t ω) 0) := by
    rw [devRatio_zero hK]; exact A.hasDerivAt_dI
  have hL := hL'.comp (0 : ℝ) (hasDerivAt_devRatio hK (k (t + 1) ω) (k t ω))
  have hE := hasDerivAt_E_of_remainder 𝔼 (g := integrand A β lbar rbar Kbar lam r k t) hδ hrem t ω
  have h := HasDerivAt.sub hL hE
  refine h.congr_deriv ?_
  rw [E_integrandDeriv 𝔼 A hss hlam hk]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (3.3), p. 355: the derivative of the first-order condition vanishes in
every state if and only if (3.3) holds. -/
theorem eq_3_3_iff {β δ εψ : ℝ} {lam r k : ℕ → Ω → ℝ} {t : ℕ} :
    (∀ ω, (lam t + εψ • (k (t + 1) - k t)) ω - (𝔼.E t (lam (t + 1))
        + (1 - β * (1 - δ)) • 𝔼.E t (r (t + 1))
        + (β * εψ) • (𝔼.E t (k (t + 2)) - k (t + 1))) ω = 0) ↔ Eq33 𝔼 β δ εψ lam r k t := by
  constructor
  · intro h
    funext ω
    exact sub_eq_zero.1 (h ω)
  · intro h ω
    rw [Eq33] at h
    rw [h, sub_self]

/-! #### (3.3) on a general state space from primitives: uniform first-order expansions

For uniformly bounded log-deviation processes, the integrand of the first-order condition has a
first-order expansion whose remainder is `o(ε)` UNIFORMLY in the state. Only the hypotheses of
`AdjCost` are needed (`I` differentiable, `I'` differentiable at `1`); boundedness of the
deviations makes the remainder of `G` at `1` uniform. -/

/-- Woodford (2003), p. 355: `f` has a uniform first-order expansion at `0` with derivative
`f'`: for every `η > 0` there is `δ > 0` with `|f h − f 0 − h f'| ≤ η |h|` for `|h| < δ`, in
every state. -/
def UnifDeriv (f : ℝ → Ω → ℝ) (f' : Ω → ℝ) : Prop :=
  ∀ η > 0, ∃ δ > 0, ∀ h : ℝ, |h| < δ → ∀ ω, |f h ω - f 0 ω - h * f' ω| ≤ η * |h|

/-- Woodford (2003), p. 355: a uniform first-order expansion lets `E_t` commute with the
derivative, on any state space. -/
theorem hasDerivAt_E_of_unifDeriv {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} (hf : UnifDeriv f f') (t : ℕ)
    (ω : Ω) : HasDerivAt (fun z => 𝔼.E t (f z) ω) (𝔼.E t f' ω) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := hf c hc
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  have hh' : |h| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hh
  have key : 𝔼.E t (f (0 + h)) ω - 𝔼.E t (f 0) ω - h • 𝔼.E t f' ω
      = 𝔼.E t (f h - f 0 - h • f') ω := by
    simp [map_sub, map_smul]
  rw [key, Real.norm_eq_abs, Real.norm_eq_abs]
  exact 𝔼.abs_E_le (fun ω' => by simpa [smul_eq_mul] using hb h hh' ω') t ω

/-- Woodford (2003), p. 355: transport a uniform expansion along equal functions. -/
theorem UnifDeriv.congr {f g : ℝ → Ω → ℝ} {f' g' : Ω → ℝ} (hf : UnifDeriv f f')
    (hfg : ∀ h ω, f h ω = g h ω) (h' : ∀ ω, f' ω = g' ω) : UnifDeriv g g' := by
  intro η hη
  obtain ⟨δ, hδ, hb⟩ := hf η hη
  exact ⟨δ, hδ, fun h hh ω => by rw [← hfg h ω, ← hfg 0 ω, ← h' ω]; exact hb h hh ω⟩

/-- Woodford (2003), p. 355: `e^{ε u}` has the uniform expansion `1 + ε u` when `|u| ≤ B`. -/
theorem unifDeriv_exp {u : Ω → ℝ} {B : ℝ} (hu : ∀ ω, |u ω| ≤ B) :
    UnifDeriv (fun h ω => Real.exp (h * u ω)) u := by
  intro η hη
  have hB'0 : 0 < |B| + 1 := by positivity
  refine ⟨min (1 / (|B| + 1)) (η / (|B| + 1) ^ 2), by positivity, fun h hh ω => ?_⟩
  have h1 : |h| < 1 / (|B| + 1) := lt_of_lt_of_le hh (min_le_left _ _)
  have h2 : |h| < η / (|B| + 1) ^ 2 := lt_of_lt_of_le hh (min_le_right _ _)
  have huB : |u ω| ≤ |B| + 1 := by linarith [hu ω, le_abs_self B]
  have hx : |h * u ω| ≤ 1 := by
    rw [abs_mul]
    calc |h| * |u ω| ≤ |h| * (|B| + 1) := mul_le_mul_of_nonneg_left huB (abs_nonneg h)
      _ ≤ 1 / (|B| + 1) * (|B| + 1) := mul_le_mul_of_nonneg_right h1.le hB'0.le
      _ = 1 := by field_simp
  simp only [zero_mul, Real.exp_zero]
  calc |Real.exp (h * u ω) - 1 - h * u ω| ≤ (h * u ω) ^ 2 := Real.abs_exp_sub_one_sub_id_le hx
    _ = |h| * (|h| * |u ω| ^ 2) := by
        rw [sq_abs, show |h| * (|h| * u ω ^ 2) = (|h| * |h|) * u ω ^ 2 by ring,
          abs_mul_abs_self]
        ring
    _ ≤ |h| * (η / (|B| + 1) ^ 2 * (|B| + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h2.le (pow_le_pow_left₀ (abs_nonneg _) huB 2)
          (by positivity) (by positivity)) (abs_nonneg h)
    _ = η * |h| := by field_simp

/-- Woodford (2003), p. 355: uniform expansions scale by constants. -/
theorem UnifDeriv.const_mul {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} (hf : UnifDeriv f f') (c : ℝ) :
    UnifDeriv (fun h ω => c * f h ω) (fun ω => c * f' ω) := by
  intro η hη
  obtain ⟨δ, hδ, hb⟩ := hf (η / (|c| + 1)) (by positivity)
  refine ⟨δ, hδ, fun h hh ω => ?_⟩
  have e : c * f h ω - c * f 0 ω - h * (c * f' ω) = c * (f h ω - f 0 ω - h * f' ω) := by ring
  rw [e, abs_mul]
  calc |c| * |f h ω - f 0 ω - h * f' ω| ≤ (|c| + 1) * (η / (|c| + 1) * |h|) :=
        mul_le_mul (by linarith) (hb h hh ω) (abs_nonneg _) (by positivity)
    _ = η * |h| := by field_simp

/-- Woodford (2003), p. 355: uniform expansions add. -/
theorem UnifDeriv.add {f g : ℝ → Ω → ℝ} {f' g' : Ω → ℝ} (hf : UnifDeriv f f')
    (hg : UnifDeriv g g') : UnifDeriv (fun h ω => f h ω + g h ω) (fun ω => f' ω + g' ω) := by
  intro η hη
  obtain ⟨δ1, hδ1, h1⟩ := hf (η / 2) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := hg (η / 2) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun h hh ω => ?_⟩
  have a := h1 h (lt_of_lt_of_le hh (min_le_left _ _)) ω
  have b := h2 h (lt_of_lt_of_le hh (min_le_right _ _)) ω
  have e : f h ω + g h ω - (f 0 ω + g 0 ω) - h * (f' ω + g' ω) =
      (f h ω - f 0 ω - h * f' ω) + (g h ω - g 0 ω - h * g' ω) := by ring
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ η / 2 * |h| + η / 2 * |h| := add_le_add a b
    _ = η * |h| := by ring

/-- Woodford (2003), p. 355: a uniform expansion with a bounded derivative gives a uniform
Lipschitz bound on increments, `|f h − f 0| ≤ (1 + |D|)|h|`. -/
theorem UnifDeriv.incr {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} (hf : UnifDeriv f f') {D : ℝ}
    (hD : ∀ ω, |f' ω| ≤ D) :
    ∃ δ > 0, ∀ h : ℝ, |h| < δ → ∀ ω, |f h ω - f 0 ω| ≤ (1 + |D|) * |h| := by
  obtain ⟨δ, hδ, hb⟩ := hf 1 one_pos
  refine ⟨δ, hδ, fun h hh ω => ?_⟩
  have e : f h ω - f 0 ω = (f h ω - f 0 ω - h * f' ω) + h * f' ω := by ring
  rw [e]
  have h2 : |h * f' ω| ≤ |h| * |D| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hD ω).trans (le_abs_self D)) (abs_nonneg h)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 1 * |h| + |h| * |D| := add_le_add (hb h hh ω) h2
    _ = (1 + |D|) * |h| := by ring

/-- Woodford (2003), p. 355: product rule for uniform expansions (bounded derivatives and
bounded values at `0`). -/
theorem UnifDeriv.mul {f g : ℝ → Ω → ℝ} {f' g' : Ω → ℝ} {Df Dg Cf Cg : ℝ}
    (hf : UnifDeriv f f') (hg : UnifDeriv g g') (hDf : ∀ ω, |f' ω| ≤ Df)
    (hDg : ∀ ω, |g' ω| ≤ Dg) (hCf : ∀ ω, |f 0 ω| ≤ Cf) (hCg : ∀ ω, |g 0 ω| ≤ Cg) :
    UnifDeriv (fun h ω => f h ω * g h ω) (fun ω => f' ω * g 0 ω + f 0 ω * g' ω) := by
  intro η hη
  have hK0 : 0 < 1 + |Dg| := by positivity
  have hB0 : 0 < |Cg| + (1 + |Dg|) := by positivity
  have hF0 : 0 < (|Df| + 1) * (1 + |Dg|) := by positivity
  obtain ⟨δ1, hδ1, h1⟩ := hf (η / (3 * (|Cg| + (1 + |Dg|)))) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := hg (η / (3 * (|Cf| + 1))) (by positivity)
  obtain ⟨δ3, hδ3, h3⟩ := hg.incr hDg
  refine ⟨min (min δ1 δ2) (min δ3 (min 1 (η / (3 * ((|Df| + 1) * (1 + |Dg|)))))),
    by positivity, fun h hh ω => ?_⟩
  simp only [lt_min_iff] at hh
  obtain ⟨⟨hh1, hh2⟩, hh3, hh4, hh5⟩ := hh
  have a := h1 h hh1 ω
  have b := h2 h hh2 ω
  have c := h3 h hh3 ω
  have hgh : |g h ω| ≤ |Cg| + (1 + |Dg|) := by
    have e : g h ω = g 0 ω + (g h ω - g 0 ω) := by ring
    rw [e]
    calc _ ≤ |g 0 ω| + |g h ω - g 0 ω| := abs_add_le _ _
      _ ≤ |Cg| + (1 + |Dg|) * 1 := add_le_add ((hCg ω).trans (le_abs_self _))
          (c.trans (mul_le_mul_of_nonneg_left hh4.le hK0.le))
      _ = |Cg| + (1 + |Dg|) := by ring
  have e : f h ω * g h ω - f 0 ω * g 0 ω - h * (f' ω * g 0 ω + f 0 ω * g' ω) =
      (f h ω - f 0 ω - h * f' ω) * g h ω + f 0 ω * (g h ω - g 0 ω - h * g' ω)
        + h * f' ω * (g h ω - g 0 ω) := by ring
  rw [e]
  have t1 : |(f h ω - f 0 ω - h * f' ω) * g h ω| ≤ η / 3 * |h| := by
    rw [abs_mul]
    calc _ ≤ (η / (3 * (|Cg| + (1 + |Dg|))) * |h|) * (|Cg| + (1 + |Dg|)) :=
          mul_le_mul a hgh (abs_nonneg _) (by positivity)
      _ = η / 3 * |h| := by field_simp
  have t2 : |f 0 ω * (g h ω - g 0 ω - h * g' ω)| ≤ η / 3 * |h| := by
    rw [abs_mul]
    calc _ ≤ (|Cf| + 1) * (η / (3 * (|Cf| + 1)) * |h|) :=
          mul_le_mul (by linarith [(hCf ω).trans (le_abs_self Cf)]) b (abs_nonneg _)
            (by positivity)
      _ = η / 3 * |h| := by field_simp
  have t3 : |h * f' ω * (g h ω - g 0 ω)| ≤ η / 3 * |h| := by
    rw [abs_mul, abs_mul]
    have hf' : |f' ω| ≤ |Df| + 1 := by linarith [(hDf ω).trans (le_abs_self Df)]
    calc |h| * |f' ω| * |g h ω - g 0 ω| ≤ |h| * (|Df| + 1) * ((1 + |Dg|) * |h|) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hf' (abs_nonneg h)) c (abs_nonneg _)
            (by positivity)
      _ = |h| * ((|Df| + 1) * (1 + |Dg|) * |h|) := by ring
      _ ≤ |h| * ((|Df| + 1) * (1 + |Dg|) * (η / (3 * ((|Df| + 1) * (1 + |Dg|))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh5.le hF0.le) (abs_nonneg h)
      _ = η / 3 * |h| := by field_simp
  linarith [abs_add_three ((f h ω - f 0 ω - h * f' ω) * g h ω)
    (f 0 ω * (g h ω - g 0 ω - h * g' ω)) (h * f' ω * (g h ω - g 0 ω))]

/-- Woodford (2003), p. 355: chain rule for uniform expansions: if `f` has a uniform expansion
with bounded derivative and `f 0 ≡ p`, and `g` is differentiable at `p`, then `g ∘ f` has the
uniform expansion with derivative `g'(p) f'`. -/
theorem UnifDeriv.comp {f : ℝ → Ω → ℝ} {f' : Ω → ℝ} {p D g' : ℝ} {g : ℝ → ℝ}
    (hf : UnifDeriv f f') (hD : ∀ ω, |f' ω| ≤ D) (hp : ∀ ω, f 0 ω = p) (hg : HasDerivAt g g' p) :
    UnifDeriv (fun h ω => g (f h ω)) (fun ω => g' * f' ω) := by
  intro η hη
  have hK0 : 0 < 1 + |D| := by positivity
  obtain ⟨ρ, hρ, hρb⟩ : ∃ ρ > 0, ∀ k : ℝ, |k| < ρ →
      |g (p + k) - g p - k * g'| ≤ η / (2 * (1 + |D|)) * |k| := by
    have hlo := (hasDerivAt_iff_isLittleO_nhds_zero.1 hg).def
      (c := η / (2 * (1 + |D|))) (by positivity)
    rcases Metric.eventually_nhds_iff.1 hlo with ⟨ρ, hρ, hb⟩
    refine ⟨ρ, hρ, fun k hk => ?_⟩
    have := hb (y := k) (by simpa [Real.dist_eq] using hk)
    simpa [Real.norm_eq_abs, smul_eq_mul] using this
  obtain ⟨δ1, hδ1, h1⟩ := hf (η / (2 * (|g'| + 1))) (by positivity)
  obtain ⟨δ2, hδ2, h2⟩ := hf.incr hD
  refine ⟨min (min δ1 δ2) (ρ / (1 + |D|)), by positivity, fun h hh ω => ?_⟩
  simp only [lt_min_iff] at hh
  obtain ⟨⟨hh1, hh2⟩, hh3⟩ := hh
  have hinc := h2 h hh2 ω
  rw [hp ω] at hinc
  have hk : |f h ω - p| < ρ :=
    calc _ ≤ (1 + |D|) * |h| := hinc
      _ < (1 + |D|) * (ρ / (1 + |D|)) := mul_lt_mul_of_pos_left hh3 hK0
      _ = ρ := by field_simp
  have a := hρb (f h ω - p) hk
  rw [add_sub_cancel] at a
  have b := h1 h hh1 ω
  beta_reduce
  rw [hp ω] at b ⊢
  have e : g (f h ω) - g p - h * (g' * f' ω) =
      (g (f h ω) - g p - (f h ω - p) * g') + g' * (f h ω - p - h * f' ω) := by ring
  rw [e]
  have t1 : |g (f h ω) - g p - (f h ω - p) * g'| ≤ η / 2 * |h| :=
    calc _ ≤ η / (2 * (1 + |D|)) * |f h ω - p| := a
      _ ≤ η / (2 * (1 + |D|)) * ((1 + |D|) * |h|) :=
          mul_le_mul_of_nonneg_left hinc (by positivity)
      _ = η / 2 * |h| := by field_simp
  have t2 : |g' * (f h ω - p - h * f' ω)| ≤ η / 2 * |h| := by
    rw [abs_mul]
    calc _ ≤ (|g'| + 1) * (η / (2 * (|g'| + 1)) * |h|) :=
          mul_le_mul (by linarith) b (abs_nonneg _) (by positivity)
      _ = η / 2 * |h| := by field_simp
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ η / 2 * |h| + η / 2 * |h| := add_le_add t1 t2
    _ = η * |h| := by ring

/-- Woodford (2003), p. 355: the ratio `b e^{εu}/(b e^{εv})` is `e^{ε(u − v)}`. -/
theorem devRatio_eq_exp {b : ℝ} (hb : b ≠ 0) (u v ε : ℝ) :
    dev b u ε / dev b v ε = Real.exp (ε * (u - v)) := by
  rw [dev, dev, mul_div_mul_left _ _ hb, ← Real.exp_sub, mul_sub]

/-- Woodford (2003), p. 355: for uniformly bounded log-deviation processes (`|λ̂|, |ρ̂|, |k̂| ≤ M`),
the integrand of the investment first-order condition has a uniform first-order expansion with
derivative `integrandDeriv`. -/
theorem unifDeriv_integrand (A : AdjCost) {β lbar rbar Kbar M : ℝ} (hl : lbar ≠ 0)
    (hK : Kbar ≠ 0) {lam r k : ℕ → Ω → ℝ} (hlamB : ∀ s ω, |lam s ω| ≤ M)
    (hrB : ∀ s ω, |r s ω| ≤ M) (hkB : ∀ s ω, |k s ω| ≤ M) (t : ℕ) :
    UnifDeriv (integrand A β lbar rbar Kbar lam r k t) (integrandDeriv A β rbar lam r k t) := by
  have hdiff : ∀ (x : ℕ → Ω → ℝ), (∀ s ω, |x s ω| ≤ M) → ∀ s s' ω,
      |x s ω - x s' ω| ≤ 2 * M := by
    intro x hx s s' ω
    have := abs_sub_le (x s ω) 0 (x s' ω)
    simp only [sub_zero, zero_sub, abs_neg] at this
    linarith [hx s ω, hx s' ω]
  have hu := hdiff lam hlamB (t + 1) t
  have hv := hdiff k hkB (t + 2) (t + 1)
  have f1 := unifDeriv_exp hu
  have fr := (unifDeriv_exp (u := fun ω => r (t + 1) ω) (fun ω => hrB _ ω)).const_mul rbar
  have fG := (unifDeriv_exp hv).comp hv (p := 1) (fun ω => by simp) A.hasDerivAt_G
  have f2 := fr.add fG
  have f12 := f1.mul f2 (Df := 2 * M) (Dg := |rbar| * M + |A.εψ| * (2 * M)) (Cf := 1)
    (Cg := |rbar| + |A.G 1|) hu
    (fun ω => by
      calc _ ≤ |rbar * r (t + 1) ω| + |A.εψ * (k (t + 2) ω - k (t + 1) ω)| := abs_add_le _ _
        _ ≤ |rbar| * M + |A.εψ| * (2 * M) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (hrB _ ω) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (hv ω) (abs_nonneg _)))
    (fun ω => by simp)
    (fun ω => by
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact abs_add_le _ _)
  refine (f12.const_mul β).congr (fun h ω => ?_) (fun ω => ?_)
  · simp only [integrand]
    rw [devRatio_eq_exp hl, devRatio_eq_exp hK, dev]
    ring
  · simp only [zero_mul, Real.exp_zero, mul_one, one_mul, A.G_one, integrandDeriv]
    ring

/-- Woodford (2003), eq. (3.3), p. 355, as an EXACT derivative on a GENERAL state space with no
remainder hypothesis: for uniformly bounded log-deviation processes, the residual of the
nonlinear investment first-order condition has derivative
`[λ̂_t + ε_ψ(k̂_{t+1} − k̂_t)] − [E_t λ̂_{t+1} + (1 − β(1 − δ)) E_t ρ̂_{t+1}
  + β ε_ψ E_t(k̂_{t+2} − k̂_{t+1})]` at the steady state. -/
theorem eq_3_3_bounded (A : AdjCost) {β lbar rbar Kbar M : ℝ} (hl : lbar ≠ 0) (hK : Kbar ≠ 0)
    (hss : β * (rbar + 1 - A.δ) = 1) {lam r k : ℕ → Ω → ℝ} {t : ℕ}
    (hlam : 𝔼.E t (lam t) = lam t) (hk : 𝔼.E t (k (t + 1)) = k (t + 1))
    (hlamB : ∀ s ω, |lam s ω| ≤ M) (hrB : ∀ s ω, |r s ω| ≤ M) (hkB : ∀ s ω, |k s ω| ≤ M)
    (ω : Ω) :
    HasDerivAt (fun ε => residual 𝔼 A β lbar rbar Kbar lam r k t ε ω)
      ((lam t + A.εψ • (k (t + 1) - k t)) ω - (𝔼.E t (lam (t + 1))
        + (1 - β * (1 - A.δ)) • 𝔼.E t (r (t + 1))
        + (β * A.εψ) • (𝔼.E t (k (t + 2)) - k (t + 1))) ω) 0 := by
  have hL' : HasDerivAt A.dI A.εψ (dev Kbar (k (t + 1) ω) 0 / dev Kbar (k t ω) 0) := by
    rw [devRatio_zero hK]; exact A.hasDerivAt_dI
  have hL := hL'.comp (0 : ℝ) (hasDerivAt_devRatio hK (k (t + 1) ω) (k t ω))
  have hE := hasDerivAt_E_of_unifDeriv 𝔼
    (unifDeriv_integrand A (β := β) (rbar := rbar) hl hK hlamB hrB hkB t) t ω
  have h := HasDerivAt.sub hL hE
  refine h.congr_deriv ?_
  rw [E_integrandDeriv 𝔼 A hss hlam hk]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end FOC

/-! ### The aggregate capital Euler equation (3.7) -/

namespace Linear

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (3.6), p. 356 (with the corrected `q`): the log-linear shadow value of
capital, `ρ̂_t = ρ_y(ŷ_t − k̂_t) + ν k̂_t − λ̂_t − ω q_t`. -/
def Eq36 (ρy ν ω : ℝ) (r y k lam q : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  r t = ρy • (y t - k t) + ν • k t - lam t - ω • q t

/-- Woodford (2003), eq. (3.7), p. 356, CORRECTED (`E_t q_{t+1}` in place of the printed `q_t`):
`λ̂_t + ε_ψ(K̂_{t+1} − K̂_t) = β(1 − δ) E_t λ̂_{t+1}
  + [1 − β(1 − δ)][ρ_y E_t Ŷ_{t+1} − ρ_k K̂_{t+1} − ω E_t q_{t+1}]
  + β ε_ψ (E_t K̂_{t+2} − K̂_{t+1})`. -/
def Eq37 (β δ εψ ρy ρk ω : ℝ) (lam Y K q : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  lam t + εψ • (K (t + 1) - K t) = (β * (1 - δ)) • 𝔼.E t (lam (t + 1))
    + (1 - β * (1 - δ)) • (ρy • 𝔼.E t (Y (t + 1)) - ρk • K (t + 1) - ω • 𝔼.E t (q (t + 1)))
    + (β * εψ) • (𝔼.E t (K (t + 2)) - K (t + 1))

/-- Woodford (2003), eq. (3.7), p. 356, AS PRINTED, with `ω q_t` inside the bracket. -/
def Eq37printed (β δ εψ ρy ρk ω : ℝ) (lam Y K q : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  lam t + εψ • (K (t + 1) - K t) = (β * (1 - δ)) • 𝔼.E t (lam (t + 1))
    + (1 - β * (1 - δ)) • (ρy • 𝔼.E t (Y (t + 1)) - ρk • K (t + 1) - ω • q t)
    + (β * εψ) • (𝔼.E t (K (t + 2)) - K (t + 1))

/-- Woodford (2003), eq. (3.7), p. 356: substituting (3.6) at date `t + 1` into (3.3) gives
exactly the corrected (3.7) (with `ρ_k = ρ_y − ν` and `K̂_{t+1}` known at `t`), and conversely. -/
theorem eq_3_7_iff {β δ εψ ρy ρk ν ω : ℝ} (hρ : ρk = ρy - ν) {lam r Y K q : ℕ → Ω → ℝ} {t : ℕ}
    (h36 : Eq36 ρy ν ω r Y K lam q (t + 1)) (hK : 𝔼.E t (K (t + 1)) = K (t + 1)) :
    FOC.Eq33 𝔼 β δ εψ lam r K t ↔ Eq37 𝔼 β δ εψ ρy ρk ω lam Y K q t := by
  unfold FOC.Eq33 Eq37
  rw [Eq36] at h36
  rw [h36]
  simp only [map_sub, map_add, map_smul, hK]
  constructor <;> intro h <;> rw [h] <;> funext ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> rw [hρ] <;> ring

/-- Woodford (2003), eq. (3.7), p. 356 — the printed `ω q_t` is WRONG: for any `ω ≠ 0` and
`β(1 − δ) ≠ 1` there are (perfect-foresight) paths satisfying (3.3) and (3.6) at every date,
hence the corrected (3.7), but violating the printed (3.7) at date `0`. Take `K̂ = Ŷ = 0`,
`q_0 = 0`, `q_t = 1` for `t ≥ 1`, `λ̂ ≡ −ω`, `ρ̂_t = ω − ω q_t`. -/
theorem eq_3_7_printed_false {β δ εψ ρy ν ω : ℝ} (hω : ω ≠ 0) (hβδ : β * (1 - δ) ≠ 1) :
    ∃ lam r Y K q : ℕ → Unit → ℝ,
      (∀ t, FOC.Eq33 perfectForesight β δ εψ lam r K t) ∧
      (∀ t, Eq36 ρy ν ω r Y K lam q t) ∧
      (∀ t, Eq37 perfectForesight β δ εψ ρy (ρy - ν) ω lam Y K q t) ∧
      ¬ Eq37printed perfectForesight β δ εψ ρy (ρy - ν) ω lam Y K q 0 := by
  set q : ℕ → Unit → ℝ := fun t _ => if t = 0 then 0 else 1 with hq
  set r : ℕ → Unit → ℝ := fun t u => ω - ω * q t u with hr
  have h33 : ∀ t, FOC.Eq33 perfectForesight β δ εψ (fun _ _ => -ω) r (fun _ _ => 0) t := by
    intro t
    funext u
    simp [perfectForesight, hr, hq]
  have h36 : ∀ t, Eq36 ρy ν ω r (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -ω) q t := by
    intro t
    funext u
    simp [hr]
  refine ⟨fun _ _ => -ω, r, fun _ _ => 0, fun _ _ => 0, q, h33, h36, fun t =>
    (eq_3_7_iff perfectForesight rfl (h36 (t + 1)) rfl).1 (h33 t), ?_⟩
  intro hp
  have h : -ω + εψ * (0 - 0) = β * (1 - δ) * (-ω) + (1 - β * (1 - δ)) * (ρy * 0 - (ρy - ν) * 0
      - ω * 0) + β * εψ * (0 - 0) := congrFun hp ()
  apply hβδ
  have : ω * (1 - β * (1 - δ)) = 0 := by linear_combination (-1 : ℝ) * h
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 hω
  · linarith

/-- Woodford (2003), p. 356: "an equation of the same form holds for the aggregate capital
stock": if every firm `i` (weights `w i` summing to one) satisfies (3.7) with its own `ŷ(i)`,
`k̂(i)` and the common `λ̂`, `q`, then the weighted averages `Ŷ = ∑ w_i ŷ(i)`,
`K̂ = ∑ w_i k̂(i)` satisfy (3.7). -/
theorem eq_3_7_aggregate {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∑ i, w i = 1)
    {β δ εψ ρy ρk ω : ℝ} {lam q : ℕ → Ω → ℝ} {y k : ι → ℕ → Ω → ℝ} {t : ℕ}
    (h : ∀ i, Eq37 𝔼 β δ εψ ρy ρk ω lam (y i) (k i) q t) :
    Eq37 𝔼 β δ εψ ρy ρk ω lam (fun s => ∑ i, w i • y i s) (fun s => ∑ i, w i • k i s) q t := by
  funext u
  have hi : ∀ i, (lam t + εψ • (k i (t + 1) - k i t)) u = ((β * (1 - δ)) • 𝔼.E t (lam (t + 1))
      + (1 - β * (1 - δ)) • (ρy • 𝔼.E t (y i (t + 1)) - ρk • k i (t + 1)
        - ω • 𝔼.E t (q (t + 1))) + (β * εψ) • (𝔼.E t (k i (t + 2)) - k i (t + 1))) u :=
    fun i => congrFun (h i) u
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_smul,
    Finset.sum_apply]
  have key : ∑ i, w i * ((lam t u + εψ * (k i (t + 1) u - k i t u)) -
      (β * (1 - δ) * 𝔼.E t (lam (t + 1)) u + (1 - β * (1 - δ)) * (ρy * 𝔼.E t (y i (t + 1)) u
        - ρk * k i (t + 1) u - ω * 𝔼.E t (q (t + 1)) u)
        + β * εψ * (𝔼.E t (k i (t + 2)) u - k i (t + 1) u))) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hi i, sub_self, mul_zero]
  have expand : ∑ i, w i * ((lam t u + εψ * (k i (t + 1) u - k i t u)) -
      (β * (1 - δ) * 𝔼.E t (lam (t + 1)) u + (1 - β * (1 - δ)) * (ρy * 𝔼.E t (y i (t + 1)) u
        - ρk * k i (t + 1) u - ω * 𝔼.E t (q (t + 1)) u)
        + β * εψ * (𝔼.E t (k i (t + 2)) u - k i (t + 1) u))) =
      (∑ i, w i) * (lam t u - β * (1 - δ) * 𝔼.E t (lam (t + 1)) u
        + (1 - β * (1 - δ)) * ω * 𝔼.E t (q (t + 1)) u)
      + (εψ + (1 - β * (1 - δ)) * ρk + β * εψ) * ∑ i, w i * k i (t + 1) u
      - εψ * ∑ i, w i * k i t u
      - (1 - β * (1 - δ)) * ρy * ∑ i, w i * 𝔼.E t (y i (t + 1)) u
      - β * εψ * ∑ i, w i * 𝔼.E t (k i (t + 2)) u := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hw, one_mul] at expand
  linear_combination key.symm.trans expand |>.symm

end Linear

/-! ### Investment (3.8), the marginal utility of income (3.9) and the interest rate (3.10) -/

/-- Woodford (2003), eq. (3.8), p. 357, as an EXACT derivative: investment
`I_t = I(K_{t+1}/K_t) K_t`, measured as `(I_t − δ K̄)/Ȳ`, has derivative
`k[K̂_{t+1} − (1 − δ) K̂_t]` (`k = K̄/Ȳ`) along log deviations `(K̂_t, K̂_{t+1})`. -/
theorem eq_3_8 (A : AdjCost) {Kbar Ybar : ℝ} (hK : Kbar ≠ 0) (K0 K1 : ℝ) :
    HasDerivAt (fun ε => (A.I (dev Kbar K1 ε / dev Kbar K0 ε) * dev Kbar K0 ε - A.δ * Kbar) / Ybar)
      (Kbar / Ybar * (K1 - (1 - A.δ) * K0)) 0 := by
  have hI' : HasDerivAt A.I (A.dI 1) (dev Kbar K1 0 / dev Kbar K0 0) := by
    rw [devRatio_zero hK]; exact A.hasDerivAt_I 1
  have hI := hI'.comp (0 : ℝ) (hasDerivAt_devRatio hK K1 K0)
  have hk : HasDerivAt (fun ε => dev Kbar K0 ε) (Kbar * K0) 0 := by
    have h := (logDeriv_dev hK K0).2
    simpa using h
  have h := ((hI.mul hk).sub_const (A.δ * Kbar)).div_const Ybar
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, dev_zero, div_self hK, A.I_one, A.dI_one]
  ring

/-- Woodford (2003), eq. (3.8), p. 357: the steady-state level of `I_t/Ȳ` is `δ k`. -/
theorem eq_3_8_steady (A : AdjCost) {Kbar : ℝ} (hK : Kbar ≠ 0) (Ybar K0 K1 : ℝ) :
    A.I (dev Kbar K1 0 / dev Kbar K0 0) * dev Kbar K0 0 / Ybar = A.δ * (Kbar / Ybar) := by
  rw [devRatio_zero hK, A.I_one, dev_zero]
  ring

/-- Woodford (2003), eq. (3.9), p. 357, as an EXACT derivative: `λ = u_c(Y − I − G; ξ)` along
`Y = Ȳ e^{εŶ}`, `I = Ī + ε Ȳ Î`, `G = Ḡ + ε Ȳ Ĝ`, `ξ = ε ξ̂` has log-derivative
`−σ⁻¹(Ŷ − Î − g)`, with `σ⁻¹ = −u_cc Ȳ / u_c` (fn. 28: `σ` is `C̄/Ȳ` times the intertemporal
elasticity of substitution) and the composite disturbance `g = Ĝ − u_cξ ξ̂/(Ȳ u_cc)`. -/
theorem eq_3_9 {uc : ℝ × ℝ → ℝ} {ucc ucx Ybar Ibar Gbar : ℝ} (hY : Ybar ≠ 0)
    (hC : Ybar - Ibar - Gbar ≠ 0) (hcc : ucc ≠ 0)
    (huc : HasFDerivAt uc (ucc • ContinuousLinearMap.fst ℝ ℝ ℝ +
      ucx • ContinuousLinearMap.snd ℝ ℝ ℝ) (Ybar - Ibar - Gbar, 0))
    (hu0 : uc (Ybar - Ibar - Gbar, 0) ≠ 0) (Yh Ih Gh xh : ℝ) :
    HasDerivAt (fun ε => Real.log (uc (dev Ybar Yh ε - (Ibar + ε * (Ybar * Ih)) -
      (Gbar + ε * (Ybar * Gh)), ε * xh)))
      (-(-ucc * Ybar / uc (Ybar - Ibar - Gbar, 0)) *
        (Yh - Ih - (Gh - ucx * xh / (Ybar * ucc)))) 0 := by
  have hc : LogDeriv (fun ε => dev Ybar Yh ε - (Ibar + ε * (Ybar * Ih)) -
      (Gbar + ε * (Ybar * Gh))) (Ybar * (Yh - Ih - Gh) / (Ybar - Ibar - Gbar)) := by
    refine ⟨by simpa using hC, ?_⟩
    have h1 := (logDeriv_dev hY Yh).2
    have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const (Ybar * Ih)).const_add Ibar
    have h3 := ((hasDerivAt_id (0 : ℝ)).mul_const (Ybar * Gh)).const_add Gbar
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    simp only [dev_zero, zero_mul, add_zero]
    field_simp
  have h := (hc.comp₂ huc (by simp) hu0 xh).hasDerivAt_log
  refine h.congr_deriv ?_
  field_simp
  ring

/-- Woodford (2003), p. 357: the gross nominal interest rate
`1 + i_t = (β E_t[λ_{t+1}/(λ_t Π_{t+1})])⁻¹` along log deviations `(λ̂, π)` (`Π = e^{επ}`). -/
noncomputable def grossRate {Ω : Type*} (𝔼 : ExpectationSystem Ω) (β lbar : ℝ)
    (lam pi : ℕ → Ω → ℝ) (t : ℕ) (ε : ℝ) (ω : Ω) : ℝ :=
  (β * 𝔼.E t (fun ω' => dev lbar (lam (t + 1) ω') ε /
    (dev lbar (lam t ω') ε * Real.exp (ε * pi (t + 1) ω'))) ω)⁻¹

/-- Woodford (2003), eq. (3.10), p. 357, as an EXACT derivative (general state space, bounded
deviations): `log(1 + i_t)` has derivative `E_t π_{t+1} + λ̂_t − E_t λ̂_{t+1}` at the steady
state, `λ̂_t` being known at `t`. -/
theorem eq_3_10 {Ω : Type*} (𝔼 : ExpectationSystem Ω) {β lbar K : ℝ} (hβ : β ≠ 0)
    (hl : lbar ≠ 0) {lam pi : ℕ → Ω → ℝ} {t : ℕ} (hla : 𝔼.E t (lam t) = lam t)
    (hb : ∀ ω, |lam (t + 1) ω - lam t ω - pi (t + 1) ω| ≤ K) (ω : Ω) :
    HasDerivAt (fun ε => Real.log (grossRate 𝔼 β lbar lam pi t ε ω))
      (𝔼.E t (pi (t + 1)) ω + lam t ω - 𝔼.E t (lam (t + 1)) ω) 0 := by
  have hfun : ∀ ε, (fun ω' => dev lbar (lam (t + 1) ω') ε /
      (dev lbar (lam t ω') ε * Real.exp (ε * pi (t + 1) ω'))) =
      fun ω' => Real.exp (ε * (lam (t + 1) ω' - lam t ω' - pi (t + 1) ω')) := by
    intro ε
    funext ω'
    rw [dev, dev, mul_sub, mul_sub, Real.exp_sub, Real.exp_sub]
    field_simp
  have hE := hasDerivAt_E_exp 𝔼 hb t ω
  have h0 : 𝔼.E t (fun ω' => Real.exp (0 * (lam (t + 1) ω' - lam t ω' - pi (t + 1) ω'))) ω
      = 1 := by
    simp only [zero_mul, Real.exp_zero]
    rw [𝔼.const]
  have hne : β * 𝔼.E t (fun ω' => Real.exp (0 * (lam (t + 1) ω' - lam t ω' - pi (t + 1) ω'))) ω
      ≠ 0 := by
    rw [h0, mul_one]; exact hβ
  have hinv := (hE.const_mul β).inv hne
  have hlog := hinv.log (inv_ne_zero hne)
  have hg : (fun ε => Real.log (grossRate 𝔼 β lbar lam pi t ε ω)) =
      fun ε => Real.log ((β * 𝔼.E t (fun ω' => Real.exp (ε * (lam (t + 1) ω' - lam t ω'
        - pi (t + 1) ω'))) ω)⁻¹) := by
    funext ε
    rw [grossRate, hfun ε]
  rw [hg]
  refine hlog.congr_deriv ?_
  simp only [Pi.inv_apply, h0, mul_one]
  have hX : (fun ω' => lam (t + 1) ω' - lam t ω' - pi (t + 1) ω') =
      lam (t + 1) - lam t - pi (t + 1) := rfl
  rw [hX, map_sub, map_sub, hla]
  simp only [Pi.sub_apply]
  field_simp
  ring

/-! ### The steady state and the capital–output ratio (p. 363) -/

/-- Woodford (2003), p. 363: in the flexible-price steady state (`s̄ = (θ − 1)/θ`, from the
Chapter 3 pricing condition) with `β(ρ̄ + 1 − δ) = 1` (the steady state of the investment
first-order condition), the capital–output ratio `k = K̄/Ȳ` satisfies
`β⁻¹ = ((θ − 1)/θ)((φ_h − 1)/φ_h)/k + (1 − δ)`. -/
theorem steady_state_k (T : Technology) (vh : ℝ × ℝ → ℝ) {ybar Kbar lbar β δ θ : ℝ}
    (hy : 0 < ybar) (hK : 0 < Kbar) (hl : lbar ≠ 0) (hβ : β ≠ 0)
    (hs : rmc T vh ybar Kbar 1 lbar 0 = (θ - 1) / θ)
    (hss : β * (rho T vh ybar Kbar 1 lbar 0 + 1 - δ) = 1) :
    β⁻¹ = (θ - 1) / θ * ((phi T (ybar / Kbar) - 1) / phi T (ybar / Kbar)) / (Kbar / ybar)
      + (1 - δ) := by
  have hx := div_pos hy hK
  have hh := T.finv_pos _ hx
  have hD := T.df_pos _ hh
  rw [rho_eq_rmc_mul T vh hy hK one_ne_zero hl, hs] at hss
  have hb : β⁻¹ = (θ - 1) / θ * (ybar / Kbar - T.finv (ybar / Kbar) *
      T.df (T.finv (ybar / Kbar))) + 1 - δ := by
    calc β⁻¹ = β⁻¹ * (β * ((θ - 1) / θ * (ybar / Kbar - T.finv (ybar / Kbar) *
          T.df (T.finv (ybar / Kbar))) + 1 - δ)) := by rw [hss, mul_one]
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hβ, one_mul]
  rw [hb, phi]
  field_simp
  ring

/-- Woodford (2003), p. 363: solving the steady-state relation for `k`:
`k = ((θ − 1)/θ)((φ_h − 1)/φ_h) / (β⁻¹ − 1 + δ)`. -/
theorem steady_state_k_iff {β δ θ φh k : ℝ} (hk : k ≠ 0) (hden : β⁻¹ - 1 + δ ≠ 0) :
    β⁻¹ = (θ - 1) / θ * ((φh - 1) / φh) / k + (1 - δ) ↔
      k = (θ - 1) / θ * ((φh - 1) / φh) / (β⁻¹ - 1 + δ) := by
  constructor
  · intro h
    rw [eq_div_iff hden]
    have : β⁻¹ - 1 + δ = (θ - 1) / θ * ((φh - 1) / φh) / k := by linarith
    rw [this]
    field_simp
  · intro h
    set c := (θ - 1) / θ * ((φh - 1) / φh) with hc
    have hc0 : c ≠ 0 := by
      intro h0
      apply hk
      rw [h, h0, zero_div]
    rw [h]
    field_simp
    ring

/-- Woodford (2003), p. 363 ("ten quarters"): with the Table 5.1 values `β = 0.99`,
`θ = 7.88`, `φ_h = 1/0.75`, a quarterly depreciation rate `δ = 0.012` gives a capital–output
ratio `k ∈ (9.87, 9.88)`. -/
theorem ten_quarters :
    let k : ℝ := (7.88 - 1) / 7.88 * ((1 / 0.75 - 1) / (1 / 0.75)) / ((0.99 : ℝ)⁻¹ - 1 + 0.012)
    9.87 < k ∧ k < 9.88 := by
  norm_num

/-- Woodford (2003), p. 363: conversely, `k = 10` exactly requires `δ ∈ (0.0117, 0.0118)`, i.e.
`δ ≈ 0.012` (about 5% a year). -/
theorem ten_quarters_delta :
    let δ : ℝ := 1 - (0.99 : ℝ)⁻¹ + (7.88 - 1) / 7.88 * ((1 / 0.75 - 1) / (1 / 0.75)) / 10
    0.0117 < δ ∧ δ < 0.0118 := by
  norm_num

/-! ### Pricing with endogenous capital: (3.11)–(3.13) in the linear model -/

namespace Linear

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (3.2), p. 354, in logs (exact): the demand curve
`y(i) = Y (p(i)/P)^{−θ}` gives `log y(i) − log Y = −θ log(p(i)/P)`, i.e. `ŷ(i) − Ŷ = −θ p̂(i)`. -/
theorem eq_3_2_log {Y p P θ : ℝ} (hY : 0 < Y) (hp : 0 < p) (hP : 0 < P) :
    Real.log (Y * (p / P) ^ (-θ)) - Real.log Y = -θ * Real.log (p / P) := by
  rw [Real.log_mul hY.ne' (Real.rpow_pos_of_pos (div_pos hp hP) _).ne',
    Real.log_rpow (div_pos hp hP)]
  ring

/-- Woodford (2003), eq. (3.11), p. 358 (linear form, firm or aggregate, date by date):
`ŝ = ω(ŷ − k̂) + ν k̂ − λ̂ − ω q`. -/
def Eq311 (ω ν : ℝ) (s y k lam q : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  s t = ω • (y t - k t) + ν • k t - lam t - ω • q t

/-- Woodford (2003), p. 358: averaging (3.11) over firms (weights `w i` summing to one, common
`λ̂`, `q`) gives (3.11) for the averages `ŝ = ∑ w_i ŝ(i)`, `Ŷ = ∑ w_i ŷ(i)`, `K̂ = ∑ w_i k̂(i)`. -/
theorem eq_3_11_average {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∑ i, w i = 1) {ω ν : ℝ}
    {lam q : ℕ → Ω → ℝ} {s y k : ι → ℕ → Ω → ℝ} {t : ℕ}
    (h : ∀ i, Eq311 ω ν (s i) (y i) (k i) lam q t) :
    Eq311 ω ν (fun r => ∑ i, w i • s i r) (fun r => ∑ i, w i • y i r) (fun r => ∑ i, w i • k i r)
      lam q t := by
  funext u
  have hi : ∀ i, s i t u = ω * (y i t u - k i t u) + ν * k i t u - lam t u - ω * q t u := by
    intro i
    have := congrFun (h i) u
    simpa using this
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  have e1 : ∑ i, w i * s i t u = ∑ i, (w i * (ω * (y i t u - k i t u) + ν * k i t u)
      - w i * (lam t u + ω * q t u)) :=
    Finset.sum_congr rfl fun i _ => by rw [hi i]; ring
  rw [e1, Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
  have e2 : ∑ i, w i * (ω * (y i t u - k i t u) + ν * k i t u) =
      ω * (∑ i, w i * y i t u - ∑ i, w i * k i t u) + ν * ∑ i, w i * k i t u := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e2]
  ring

/-- Woodford (2003), p. 358 (display before (3.12)): (3.11) for firm `i` and for the average
imply `ŝ(i) = ŝ + ω(ŷ(i) − Ŷ) − (ω − ν)(k̂(i) − K̂)`. -/
theorem rmc_relative {ω ν si s yi Y ki K lam q : ℝ}
    (hi : si = ω * (yi - ki) + ν * ki - lam - ω * q)
    (h : s = ω * (Y - K) + ν * K - lam - ω * q) :
    si = s + ω * (yi - Y) - (ω - ν) * (ki - K) := by
  rw [hi, h]; ring

/-- Woodford (2003), eq. (3.12), p. 358: with the demand curve `ŷ(i) − Ŷ = −θ p̂(i)`,
`ŝ(i) = ŝ − (ω − ν) k̃(i) − ωθ p̂(i)`, `k̃(i) = k̂(i) − K̂`. -/
theorem eq_3_12 {ω ν θ si s yi Y ki K lam q pi : ℝ}
    (hi : si = ω * (yi - ki) + ν * ki - lam - ω * q)
    (h : s = ω * (Y - K) + ν * K - lam - ω * q) (hd : yi - Y = -θ * pi) :
    si = s - (ω - ν) * (ki - K) - ω * θ * pi := by
  rw [rmc_relative hi h, hd]; ring

/-- Woodford (2003), p. 359 (the Calvo first-order condition of Chapter 3, eq. (2.7) there):
`∑_k (αβ)^k E_t[p̂_{t+k}(i) − ŝ_{t+k}(i)] = 0` for a firm resetting its price at `t`. -/
def CalvoFOC (α β : ℝ) (p si : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  (fun u => ∑' j, (α * β) ^ j * 𝔼.E t (p (t + j) - si (t + j)) u) = fun _ => 0

/-- Woodford (2003), eq. (3.13), p. 359:
`∑_k (αβ)^k E_t[(1 + ωθ) p̂_{t+k}(i) − ŝ_{t+k} + (ω − ν) k̃_{t+k}(i)] = 0`. -/
def Eq313 (α β ω ν θ : ℝ) (p s kt : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  (fun u => ∑' j, (α * β) ^ j * 𝔼.E t ((1 + ω * θ) • p (t + j) - s (t + j)
    + (ω - ν) • kt (t + j)) u) = fun _ => 0

/-- Woodford (2003), eq. (3.13), p. 359 (conditional on the Chapter 3 Calvo first-order
condition): substituting (3.12) at every future date into the Calvo condition gives exactly
(3.13) — the two are equivalent, term by term (no summability is needed). -/
theorem eq_3_13_iff {α β ω ν θ : ℝ} {p si s kt : ℕ → Ω → ℝ} {t : ℕ}
    (h312 : ∀ j, si (t + j) = s (t + j) - (ω - ν) • kt (t + j) - (ω * θ) • p (t + j)) :
    CalvoFOC 𝔼 α β p si t ↔ Eq313 𝔼 α β ω ν θ p s kt t := by
  have hterm : ∀ j, p (t + j) - si (t + j) =
      (1 + ω * θ) • p (t + j) - s (t + j) + (ω - ν) • kt (t + j) := by
    intro j
    rw [h312 j]
    funext u
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold CalvoFOC Eq313
  simp only [hterm]

/-! ### The aggregate-supply relation (3.18) -/

/-- Woodford (2003), eq. (3.18), p. 360: averaging (3.11) (`ŝ = ω(Ŷ − K̂) + ν K̂ − λ̂ − ω q`)
and substituting (3.9) (`λ̂ = −σ⁻¹(Ŷ − Î − g)`) gives
`ŝ = (ω + σ⁻¹) Ŷ − σ⁻¹ Î − (ω − ν) K̂ − [σ⁻¹ g + ω q]` (date by date, state by state). -/
theorem eq_3_18 {ω ν σi s Y K I lam g q : ℝ} (h311 : s = ω * (Y - K) + ν * K - lam - ω * q)
    (h39 : lam = -σi * (Y - I - g)) :
    s = (ω + σi) * Y - σi * I - (ω - ν) * K - (σi * g + ω * q) := by
  rw [h311, h39]; ring

/-! ### Long-run relations (p. 365) -/

/-- Woodford (2003), p. 365, first relation: in a steady state of the CORRECTED (3.7)
(constant `λ̂ = λ∞`, `Ŷ = Y∞`, `K̂ = K∞`, `q = 0`), `λ∞ = ρ_y Y∞ − ρ_k K∞`, provided
`β(1 − δ) ≠ 1`. This relation comes from (3.7), not from "(3.8) and (3.9)" as the text says
(see `longrun_lambda_not_from_38_39`). -/
theorem longrun_lambda {β δ εψ ρy ρk ω lamInf YInf KInf : ℝ} (hβδ : β * (1 - δ) ≠ 1)
    (h : Eq37 𝔼 β δ εψ ρy ρk ω (fun _ _ => lamInf) (fun _ _ => YInf) (fun _ _ => KInf)
      (fun _ _ => 0) 0) [Nonempty Ω] :
    lamInf = ρy * YInf - ρk * KInf := by
  obtain ⟨u⟩ := ‹Nonempty Ω›
  have hu := congrFun h u
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, 𝔼.const] at hu
  have hc : 1 - β * (1 - δ) ≠ 0 := sub_ne_zero.2 (Ne.symm hβδ)
  apply mul_left_cancel₀ hc
  linear_combination hu

/-- Woodford (2003), p. 365, second relation: the steady state of (3.8)
(`Î = k[K̂_{+1} − (1 − δ) K̂]`) is `I∞ = δ k K∞`. -/
theorem longrun_investment {δ k KInf IInf : ℝ} (h : IInf = k * (KInf - (1 - δ) * KInf)) :
    IInf = δ * k * KInf := by
  rw [h]; ring

/-- Woodford (2003), p. 365 (survey error 10): the first long-run relation is NOT a consequence
of (3.8) and (3.9): `Y∞ = 1`, `K∞ = I∞ = 0`, `λ∞ = −σ⁻¹` satisfy both steady-state relations
(with `g = 0`) but not `λ∞ = ρ_y Y∞ − ρ_k K∞` when `σ⁻¹ > 0` and `ρ_y > 0`. -/
theorem longrun_lambda_not_from_38_39 {δ k σi ρy ρk : ℝ} (hσ : 0 < σi) (hρ : 0 < ρy) :
    ∃ lamInf YInf KInf IInf : ℝ, IInf = k * (KInf - (1 - δ) * KInf) ∧
      lamInf = -σi * (YInf - IInf) ∧ lamInf ≠ ρy * YInf - ρk * KInf := by
  refine ⟨-σi, 1, 0, 0, by ring, by ring, ?_⟩
  intro h
  linarith

/-- Woodford (2003), p. 365, third relation: the steady state of (3.11) with `q = 0`,
`ŝ∞ = ω Y∞ − (ω − ν) K∞ − λ∞`. -/
theorem longrun_rmc {ω ν sInf YInf KInf lamInf : ℝ}
    (h : sInf = ω * (YInf - KInf) + ν * KInf - lamInf - ω * 0) :
    sInf = ω * YInf - (ω - ν) * KInf - lamInf := by
  rw [h]; ring

/-- Woodford (2003), p. 365, fourth relation: the steady state of (3.17)
(`π = ξ₀ ŝ − ξ₁ ŝ + ψ₁ π − ψ₂ π`) is `π∞ = (ξ₀ − ξ₁)/(1 − ψ₁ + ψ₂) ŝ∞`, provided
`1 − ψ₁ + ψ₂ ≠ 0`. -/
theorem longrun_inflation {ξ0 ξ1 ψ1 ψ2 piInf sInf : ℝ} (hψ : 1 - ψ1 + ψ2 ≠ 0)
    (h : piInf = ξ0 * sInf - ξ1 * sInf + ψ1 * piInf - ψ2 * piInf) :
    piInf = (ξ0 - ξ1) / (1 - ψ1 + ψ2) * sInf := by
  rw [div_mul_eq_mul_div, eq_div_iff hψ]
  linear_combination h

/-- Woodford (2003), p. 365: the three long-run relations `λ∞ = ρ_y Y∞ − ρ_k K∞`,
`I∞ = δ k K∞`, `λ∞ = −σ⁻¹(Y∞ − I∞)` determine `Y∞`, `K∞` as multiples of `λ∞` if and only if
`D = σ⁻¹(ρ_y δ k − ρ_k) ≠ 0`: then `Y∞ = λ∞(σ⁻¹ δ k + ρ_k)/D`, `K∞ = λ∞(ρ_y + σ⁻¹)/D`. -/
theorem longrun_solve {ρy ρk δ k σi lamInf YInf KInf : ℝ} (hD : σi * (ρy * δ * k - ρk) ≠ 0) :
    (lamInf = ρy * YInf - ρk * KInf ∧ lamInf = -σi * (YInf - δ * k * KInf)) ↔
      (YInf = lamInf * (σi * δ * k + ρk) / (σi * (ρy * δ * k - ρk)) ∧
        KInf = lamInf * (ρy + σi) / (σi * (ρy * δ * k - ρk))) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [eq_div_iff hD]
      linear_combination (-(σi * δ * k)) * h1 + (-ρk) * h2
    · rw [eq_div_iff hD]
      linear_combination (-σi) * h1 + (-ρy) * h2
  · rintro ⟨h1, h2⟩
    have hinv : σi * (ρy * δ * k - ρk) * (σi * (ρy * δ * k - ρk))⁻¹ = 1 := mul_inv_cancel₀ hD
    rw [h1, h2, div_eq_mul_inv, div_eq_mul_inv]
    constructor <;> linear_combination (-lamInf) * hinv

/-- Woodford (2003), p. 365: when `ρ_y δ k = ρ_k` the long-run relations do NOT pin down
`Y∞`, `K∞` as multiples of `λ∞`: `(Y∞, K∞) = (ρ_k, ρ_y) ≠ 0` solves them with `λ∞ = 0`. -/
theorem longrun_singular {ρy ρk δ k σi : ℝ} (hsing : ρy * δ * k = ρk) (hρ : ρy ≠ 0) :
    (0 : ℝ) = ρy * ρk - ρk * ρy ∧ (0 : ℝ) = -σi * (ρk - δ * k * ρy) ∧ (ρk, ρy) ≠ (0, 0) := by
  refine ⟨by ring, ?_, fun h => hρ (Prod.ext_iff.1 h).2⟩
  rw [← hsing]; ring

/-- Woodford (2003), p. 365: substituting the long-run solution, `ŝ∞` is the multiple
`[ω(σ⁻¹ δ k + ρ_k) − (ω − ν)(ρ_y + σ⁻¹)]/D − 1` of `λ∞`. -/
theorem longrun_rmc_multiple {ρy ρk δ k σi ω ν lamInf YInf KInf sInf : ℝ}
    (hD : σi * (ρy * δ * k - ρk) ≠ 0)
    (h1 : lamInf = ρy * YInf - ρk * KInf) (h2 : lamInf = -σi * (YInf - δ * k * KInf))
    (hs : sInf = ω * YInf - (ω - ν) * KInf - lamInf) :
    sInf = lamInf * ((ω * (σi * δ * k + ρk) - (ω - ν) * (ρy + σi)) / (σi * (ρy * δ * k - ρk))
      - 1) := by
  obtain ⟨hY, hK⟩ := (longrun_solve hD).1 ⟨h1, h2⟩
  rw [hs, hY, hK]
  field_simp

/-- Woodford (2003), p. 365: "allows one to solve for `λ∞` … as multiples of `π∞`": if
`ŝ∞ = c λ∞` and `π∞ = (ξ₀ − ξ₁)/(1 − ψ₁ + ψ₂) ŝ∞` with `(ξ₀ − ξ₁) c ≠ 0`, then
`λ∞ = (1 − ψ₁ + ψ₂)/((ξ₀ − ξ₁) c) π∞`. -/
theorem longrun_lambda_of_pi {ξ0 ξ1 ψ1 ψ2 c piInf sInf lamInf : ℝ} (hψ : 1 - ψ1 + ψ2 ≠ 0)
    (hc : (ξ0 - ξ1) * c ≠ 0) (hs : sInf = c * lamInf)
    (hpi : piInf = (ξ0 - ξ1) / (1 - ψ1 + ψ2) * sInf) :
    lamInf = (1 - ψ1 + ψ2) / ((ξ0 - ξ1) * c) * piInf := by
  have h1 : ξ0 - ξ1 ≠ 0 := left_ne_zero_of_mul hc
  have h2 : c ≠ 0 := right_ne_zero_of_mul hc
  rw [hpi, hs]
  field_simp

/-! ### Capital and the natural rate (pp. 373–374) -/

/-- Woodford (2003), p. 373: with flexible prices real marginal cost is constant (`ŝ = 0`), so
(3.18) gives the natural rate of output
`Ŷⁿ = (ω − ν)/(ω + σ⁻¹) K̂ + σ⁻¹/(ω + σ⁻¹) Îⁿ + σ⁻¹/(ω + σ⁻¹) g + ω/(ω + σ⁻¹) q`
(given the ACTUAL capital stock `K̂`), and conversely. -/
theorem natural_output {ω ν σi Yn In K g q : ℝ} (hω : ω + σi ≠ 0) :
    0 = (ω + σi) * Yn - σi * In - (ω - ν) * K - (σi * g + ω * q) ↔
      Yn = (ω - ν) / (ω + σi) * K + σi / (ω + σi) * In + σi / (ω + σi) * g
        + ω / (ω + σi) * q := by
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Woodford (2003), p. 373: if the natural rates are affine in the capital stock,
`Ŷⁿ = Ŷⁿᶜᶜ + η_y K̂`, `Îⁿ = Îⁿᶜᶜ + η_i K̂`, and the flexible-price relation `ŝ = 0` holds for
EVERY capital stock, then the constant-capital intercepts satisfy
`Ŷⁿᶜᶜ = σ⁻¹/(ω + σ⁻¹)(Îⁿᶜᶜ + g) + ω/(ω + σ⁻¹) q` and the slopes
`η_y = (ω − ν + σ⁻¹ η_i)/(ω + σ⁻¹)`. -/
theorem natural_decomposition {ω ν σi Yncc ηy Incc ηi g q : ℝ} (hω : ω + σi ≠ 0)
    (h : ∀ K : ℝ, 0 = (ω + σi) * (Yncc + ηy * K) - σi * (Incc + ηi * K) - (ω - ν) * K
      - (σi * g + ω * q)) :
    Yncc = σi / (ω + σi) * (Incc + g) + ω / (ω + σi) * q ∧
      ηy = (ω - ν + σi * ηi) / (ω + σi) := by
  have h0 := h 0
  have h1 := h 1
  constructor
  · field_simp
    linarith
  · field_simp
    linarith

/-- Woodford (2003), eq. (3.27), p. 374: subtracting the flexible-price version of (3.18) from
(3.18) (same `K̂`, `g`, `q`) gives `ŝ = (ω + σ⁻¹) Ỹ − σ⁻¹ Ĩ` with `Ỹ = Ŷ − Ŷⁿ`, `Ĩ = Î − Îⁿ`. -/
theorem eq_3_27 {ω ν σi s Y I Yn In K g q : ℝ}
    (h318 : s = (ω + σi) * Y - σi * I - (ω - ν) * K - (σi * g + ω * q))
    (hn : 0 = (ω + σi) * Yn - σi * In - (ω - ν) * K - (σi * g + ω * q)) :
    s = (ω + σi) * (Y - Yn) - σi * (I - In) := by
  linear_combination h318 - hn

end Linear

/-! ### A concrete model: Cobb–Douglas technology and isoelastic labour disutility

These instances show that the hypotheses of the exact-derivative theorems are satisfiable, and
make the counterexample to the printed `q` of (3.6) fully concrete. -/

namespace CobbDouglas

/-- Woodford (2003), p. 341 (the Rotemberg–Woodford calibration uses `f(h) = h^α`): the
Cobb–Douglas technology, `f(h) = h^α`, `f'(h) = α h^{α−1}`, `f⁻¹(y) = y^{1/α}`. -/
noncomputable def tech (α : ℝ) (hα : 0 < α) : Technology where
  f := fun h => h ^ α
  df := fun h => α * h ^ (α - 1)
  finv := fun y => y ^ α⁻¹
  hasDerivAt_f := fun _ hh => Real.hasDerivAt_rpow_const (Or.inl hh.ne')
  df_pos := fun _ hh => mul_pos hα (Real.rpow_pos_of_pos hh _)
  f_pos := fun _ hh => Real.rpow_pos_of_pos hh _
  finv_pos := fun _ hy => Real.rpow_pos_of_pos hy _
  f_finv := fun _ hy => Real.rpow_inv_rpow hy.le hα.ne'
  finv_f := fun _ hh => Real.rpow_rpow_inv hh.le hα.ne'

/-- Woodford (2003), p. 342: for Cobb–Douglas `φ ≡ 1/α` (`φ_h = 1/.75` in Table 5.1). -/
theorem phi_tech {α : ℝ} (hα : 0 < α) {x : ℝ} (hx : 0 < x) : phi (tech α hα) x = α⁻¹ := by
  have h1 : (x ^ α⁻¹) ^ (α - 1) = x ^ (α⁻¹ * (α - 1)) := (Real.rpow_mul hx.le _ _).symm
  have h2 : x ^ α⁻¹ * x ^ (α⁻¹ * (α - 1)) = x := by
    rw [← Real.rpow_add hx]
    have : α⁻¹ + α⁻¹ * (α - 1) = 1 := by field_simp; ring
    rw [this, Real.rpow_one]
  simp only [phi, tech]
  rw [h1, ← mul_assoc, mul_comm (x ^ α⁻¹) α, mul_assoc, h2]
  field_simp

/-- Woodford (2003), p. 356: the second derivative of the Cobb–Douglas `f`. -/
theorem hasDerivAt_df {α : ℝ} (hα : 0 < α) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (tech α hα).df (α * ((α - 1) * h ^ (α - 1 - 1))) h :=
  (Real.hasDerivAt_rpow_const (Or.inl hh.ne')).const_mul α

/-- Woodford (2003), p. 356: for Cobb–Douglas with `α < 1`, `ω_p ≥ 0` (in fact
`ω_p = (1 − α)/α`). -/
theorem omegaP_nonneg {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {x : ℝ} (hx : 0 < x) :
    0 ≤ omegaP (tech α hα) (α * ((α - 1) * ((tech α hα).finv x) ^ (α - 1 - 1))) x := by
  have hh : 0 < (tech α hα).finv x := (tech α hα).finv_pos x hx
  have hD := (tech α hα).df_pos _ hh
  have hP : 0 < (tech α hα).Psi x := one_div_pos.2 hD
  have hneg : α * ((α - 1) * ((tech α hα).finv x) ^ (α - 1 - 1)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hα.le
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_pos_of_pos hh _).le)
  rw [omegaP, neg_nonneg]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hx.le (mul_nonpos_of_nonpos_of_nonneg hneg hP.le)) hD.le

/-- Woodford (2003), p. 356: the isoelastic marginal disutility of labour with a multiplicative
preference shock, `v_h(h; ξ) = e^ξ h^ν` (elasticity `ν`). -/
noncomputable def vh (ν : ℝ) (p : ℝ × ℝ) : ℝ := Real.exp p.2 * p.1 ^ ν

/-- Woodford (2003), p. 356: `v_h(h; ξ) = e^ξ h^ν` is differentiable at `(L, 0)`, `L > 0`, with
partial derivatives `∂_h = ν L^{ν−1}`, `∂_ξ = L^ν`. -/
theorem hasFDerivAt_vh (ν : ℝ) {L : ℝ} (hL : 0 < L) :
    HasFDerivAt (vh ν) ((ν * L ^ (ν - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      L ^ ν • ContinuousLinearMap.snd ℝ ℝ ℝ) (L, 0) := by
  have h1 := (hasFDerivAt_snd (𝕜 := ℝ) (p := ((L, 0) : ℝ × ℝ))).exp
  have h2 := (hasFDerivAt_fst (𝕜 := ℝ) (p := ((L, 0) : ℝ × ℝ))).rpow_const (p := ν)
    (Or.inl hL.ne')
  have h := h1.mul h2
  refine h.congr_fderiv ?_
  ext <;> simp

/-- Woodford (2003), p. 356: for `v_h = e^ξ h^ν`, the elasticity `nuOf` is exactly `ν`. -/
theorem nuOf_vh (ν : ℝ) {L : ℝ} (hL : 0 < L) : nuOf (vh ν) (ν * L ^ (ν - 1)) L = ν := by
  have hp : 0 < L ^ ν := Real.rpow_pos_of_pos hL ν
  rw [nuOf, vh, Real.rpow_sub_one hL.ne']
  simp only [Real.exp_zero, one_mul]
  field_simp

/-- Woodford (2003), eq. (3.6), p. 356 — a fully concrete counterexample to the printed `q`:
with `f(h) = h^α` (`0 < α < 1`), `v_h = e^ξ h^ν` (`ν > 0`) and any positive steady state, the
log shadow value of capital in a pure technology direction does not have the derivative that
the printed `q = (1 + ω⁻¹) a + ω⁻¹ ν h̄` implies. -/
theorem eq_3_6_printed_q_false_concrete {α ν ybar Kbar lbar : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hν : 0 < ν) (hy : 0 < ybar) (hK : 0 < Kbar) (hl : 0 < lbar) :
    ¬ HasDerivAt (fun ε => Real.log (rho (tech α hα) (vh ν) (dev ybar 0 ε) (dev Kbar 0 ε)
      (dev 1 1 ε) (dev lbar 0 ε) (ε * 0)))
      (rhoY ν α⁻¹ (omegaP (tech α hα)
        (α * ((α - 1) * ((tech α hα).finv (ybar / Kbar)) ^ (α - 1 - 1))) (ybar / Kbar)) * (0 - 0)
        + ν * 0 - 0 - omega ν α⁻¹ (omegaP (tech α hα)
          (α * ((α - 1) * ((tech α hα).finv (ybar / Kbar)) ^ (α - 1 - 1))) (ybar / Kbar)) *
        qPrinted (omega ν α⁻¹ (omegaP (tech α hα)
          (α * ((α - 1) * ((tech α hα).finv (ybar / Kbar)) ^ (α - 1 - 1))) (ybar / Kbar))) ν 0 1)
      0 := by
  have hx : 0 < ybar / Kbar := div_pos hy hK
  have hL : 0 < labour (tech α hα) ybar Kbar 1 := by
    rw [labour]
    have := (tech α hα).finv_pos _ hx
    positivity
  have hv0 : vh ν (labour (tech α hα) ybar Kbar 1, 0) ≠ 0 := by
    rw [vh]
    exact (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hL ν)).ne'
  exact Linearise.eq_3_6_printed_q_false hy hK hl
    (hasDerivAt_df hα ((tech α hα).finv_pos _ hx)) (hasFDerivAt_vh ν hL) hv0
    (nuOf_vh ν hL) (phi_tech hα hx) hν ((one_lt_inv₀ hα).2 hα1) (omegaP_nonneg hα hα1 hx)

end CobbDouglas

end Woodford.PolicyResponseDynamics.InvestmentModel
