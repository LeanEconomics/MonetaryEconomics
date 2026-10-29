/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergLogWelfare
import StabilizationWelfare.NonlinearRotembergWelfare
import StabilizationWelfare.NonlinearRotembergCentreLocal

/-!
# Second-order welfare under stochastic fluctuations: Rotemberg versus Calvo

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392: welfare along a one-parameter
family of economies with disturbances of amplitude `ε`), §2 (pp. 393–405), Appendix E.2 (p. 695:
the dispersion law) and Chapter 3, footnote 44 (the Rotemberg (1982) model), with a distorted
steady state `Φ = 1 − m` (§4.1).

Both economies are hit by the same disturbances of amplitude `ε` (any process of a finite
exogenous state `s_t`); their equilibria are the Markov policies `ε ↦ z_ε(s)` of class `C²`
(`NonlinearRotembergSmooth.markov_equilibrium_smooth`, `NonlinearNKMarkov.markov_equilibrium`).
Welfare is EXACT expected discounted utility (units `u_cȲ = 1`; utility `uG σ`, which is
`log C` at `σ = 1`): Rotemberg `u(C_t) − m·v(Y_t)` with `C = Y(1 − (ψ/2)(Π − 1)²)` (`URf`), Calvo
`u(Y_t) − m·v(Y_t)Δ_t` with the EXACT dispersion `Δ_t` from `Δ_{−1} = 1` (`UCf`, `Dpath`).

## Main results

* `taylor_J2`, `J2_of_contDiffAt`, `J2_congr_ev`: second-order jets give `o(ε²)` expansions.
* **`WR_expansion`**, **`WC_expansion`** (the second-order welfare of each model, uniformly over
  all shock paths): `W(ε) = ε(1−m)Σβᵗŷ₁ + (ε²/2)W₂ + o(ε²)` with
  `W₂ᴿ = Σβᵗ[(1−m)ŷ₂ᴿ + (1−σ−m(1+ω))ŷ₁² − ψπ₁²]` and
  `W₂ᶜ = Σβᵗ[(1−m)ŷ₂ᶜ + (1−σ−m(1+ω))ŷ₁² − m/(1+ω)·D_t]`, `D_t = αD_{t−1} + 2c_Cπ₁²` the exact
  second-order dispersion (`disp_expansion`).
* **`welfare_difference`**: if the first-order paths agree (they do under the equivalence map,
  `NonlinearRotembergLinks.first_order_agree`), then along every shock path
  `W_R(ε) − W_C(ε) = (ε²/2)(1 − m)Σβᵗ(ŷ₂ᴿ − ŷ₂ᶜ) + o(ε²)`, uniformly in the path: the inflation
  costs cancel EXACTLY (`NonlinearRotembergWelfare.discounted_cost_equiv`), and the whole
  difference is the distortion times the discounted difference of SECOND-ORDER output.
* **`expected_welfare_difference`**: the same for expected discounted welfare under any
  `ExpectationSystem`; **`welfare_coincide_efficient`**: with an efficient steady state (`m = 1`)
  the second-order welfare of the two models coincides.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergStochWelfare

open Filter Topology Asymptotics
open NonlinearRotembergJets NonlinearRotembergLogWelfare
open NonlinearRotembergLinks (wedge)
open NonlinearRotembergTrendWelfare (vv J_vv J_lw)

/-! ## Jets and `o(ε²)` expansions -/

/-- Woodford (2003), App. A.3: A `C²` function at `0` has the jet `(f′(0), f″(0))`. -/
theorem J2_of_contDiffAt {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    J2 f (deriv f 0) (deriv (deriv f) 0) := by
  refine ⟨deriv f, ?_, ?_, rfl⟩
  · filter_upwards [hf.eventually (by simp)] with x hx
    exact (hx.differentiableAt (by norm_num)).hasDerivAt
  · have h1 : ContDiffAt ℝ 1 (deriv f) 0 := hf.derivWithin (by norm_num)
    exact (h1.differentiableAt (by norm_num)).hasDerivAt

/-- Woodford (2003), App. A.3: Jets only depend on the function near `0`. -/
theorem J2_congr_ev {f g : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) (h : f =ᶠ[𝓝 0] g) :
    J2 g a1 a2 := by
  obtain ⟨f1, hev, hd, h0⟩ := hf
  refine ⟨f1, ?_, hd, h0⟩
  filter_upwards [hev, h.eventually_nhds] with x hx hx'
  exact hx.congr_of_eventuallyEq (show f =ᶠ[𝓝 x] g from hx').symm

/-- Woodford (2003), Ch. 6, §1 (**a jet gives an `o(ε²)` expansion**): if `J2 f a₁ a₂`, then for
every `η > 0`, `|f(ε) − f(0) − a₁ε − (a₂/2)ε²| ≤ ηε²` for `ε` near `0`. -/
theorem taylor_J2 {f : ℝ → ℝ} {a1 a2 : ℝ} (hf : J2 f a1 a2) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝 0, |f ε - (f 0 + a1 * ε + a2 / 2 * ε ^ 2)| ≤ η * ε ^ 2 := by
  obtain ⟨f1, hev, hd, h10⟩ := hf
  obtain ⟨ρ1, hρ1, hr⟩ := NonlinearRotembergBoundary.small_remainder hd.differentiableAt hη
  obtain ⟨ρ2, hρ2, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hfd : fderiv ℝ f1 0 = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a2 :=
    hd.hasFDerivAt.fderiv
  rw [Metric.eventually_nhds_iff]
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun x hx => ?_⟩
  rw [Real.dist_eq, sub_zero] at hx
  set g : ℝ → ℝ := fun t => f t - (f 0 + a1 * t + a2 / 2 * t ^ 2)
  have hseg : ∀ t ∈ Set.uIcc 0 x, |t| ≤ |x| := fun t ht => by
    rcases le_total 0 x with h | h
    · rw [Set.uIcc_of_le h] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg h]; exact ht.2
    · rw [Set.uIcc_of_ge h] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos h]; linarith [ht.1]
  have hder : ∀ t ∈ Set.uIcc 0 x, HasDerivWithinAt g (f1 t - a1 - a2 * t) (Set.uIcc 0 x) t :=
    fun t ht => by
      have ht2 : dist t 0 < ρ2 := by
        rw [Real.dist_eq, sub_zero]
        exact lt_of_le_of_lt (hseg t ht) (hx.trans_le (min_le_right _ _))
      have h1 := hball ht2
      have h2 := ((hasDerivAt_id t).const_mul a1).const_add (f 0)
      have h3 := (hasDerivAt_pow 2 t).const_mul (a2 / 2)
      refine (h1.sub (h2.add h3)).hasDerivWithinAt.congr_deriv ?_
      push_cast; ring
  have hbound : ∀ t ∈ Set.uIcc 0 x, ‖f1 t - a1 - a2 * t‖ ≤ η * |x| := fun t ht => by
    have ht1 : ‖t‖ < ρ1 := by
      rw [Real.norm_eq_abs]
      exact lt_of_le_of_lt (hseg t ht) (hx.trans_le (min_le_left _ _))
    have := hr t ht1
    rw [hfd, h10] at this
    simp only [ContinuousLinearMap.smulRight_apply, smul_eq_mul, Real.norm_eq_abs] at this
    rw [Real.norm_eq_abs, show f1 t - a1 - a2 * t = f1 t - a1 - (1 : ℝ →L[ℝ] ℝ) t * a2 by
      simp; ring]
    exact this.trans (mul_le_mul_of_nonneg_left (hseg t ht) hη.le)
  have hmv := (convex_uIcc (0 : ℝ) x).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  calc |f x - (f 0 + a1 * x + a2 / 2 * x ^ 2)| = |g x| := rfl
    _ ≤ η * |x| * |x| := hmv
    _ = η * x ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- Woodford (2003), App. A.3: A function differentiable at `0` with `f 0 = 0` is `O(ε)`. -/
theorem abs_le_lin {f : ℝ → ℝ} {a : ℝ} (hf : HasDerivAt f a 0) (h0 : f 0 = 0) :
    ∃ C ≥ 0, ∀ᶠ ε in 𝓝 0, |f ε| ≤ C * |ε| := by
  obtain ⟨C, hC⟩ := hf.isBigO_sub.bound
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hC] with x hx
  simp only [h0, sub_zero, Real.norm_eq_abs] at hx
  exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

/-! ## The period utilities and the dispersion path -/

/-- Woodford (2003), Ch. 6 and Ch. 3 fn. 44 (**Rotemberg period utility**, units `u_cȲ = 1`):
`u(Ĉ) − m·v(Ŷ)` at `x = (ŷ, π, ĉ)`, with `C = Y(1 − (ψ/2)(Π − 1)²)` built into `ĉ`. -/
noncomputable def URf (σ ω m : ℝ) (z : Fin 3 → ℝ) : ℝ := uG σ (z 2) - m * vv ω (z 0)

/-- Woodford (2003), App. E.2: the Calvo dispersion law
`Δ′ = αΔe^{θ(1+ω)π} + (1−α)e^{−θ(1+ω)x̂}`, `x̂ = (K̂ − F̂)/(1+ωθ)`, at `w = (ŷ, π, F̂, K̂)`. -/
noncomputable def dispL (α θ ω Δ : ℝ) (w : Fin 4 → ℝ) : ℝ :=
  α * Δ * Real.exp (θ * (1 + ω) * w 1) +
    (1 - α) * Real.exp (-(θ * (1 + ω) * ((w 3 - w 2) / (1 + ω * θ))))

variable {S : Type*} [Fintype S]

/-- Woodford (2003), App. E.2 (**the exact dispersion along a shock path**), from `Δ_{−1} = 1`:
`Δ_0 = dispL(1, z(s₀))`, `Δ_{t+1} = dispL(Δ_t, z(s_{t+1}))`. -/
noncomputable def Dpath (α θ ω : ℝ) (zC : ℝ → S → Fin 4 → ℝ) (ε : ℝ) (σ : ℕ → S) : ℕ → ℝ
  | 0 => dispL α θ ω 1 (zC ε (σ 0))
  | t + 1 => dispL α θ ω (Dpath α θ ω zC ε σ t) (zC ε (σ (t + 1)))

/-- Woodford (2003), Ch. 6, §2 (**Calvo period utility**): `u(Ŷ) − m(e^{(1+ω)ŷ}Δ − 1)/(1+ω)`. -/
noncomputable def UCf (σ ω m : ℝ) (w : Fin 4 → ℝ) (Δ : ℝ) : ℝ :=
  uG σ (w 0) - m * (Real.exp ((1 + ω) * w 0) * Δ - 1) / (1 + ω)

/-- Woodford (2003), Ch. 6, §1: expected-utility-free (realised) discounted Rotemberg welfare
along the shock path `σ`. -/
noncomputable def WRp (β σ ω m : ℝ) (zR : ℝ → S → Fin 3 → ℝ) (ε : ℝ) (sp : ℕ → S) : ℝ :=
  ∑' t, β ^ t * URf σ ω m (zR ε (sp t))

/-- Woodford (2003), Ch. 6, §1: realised discounted Calvo welfare along the shock path, with the
exact dispersion from `Δ_{−1} = 1`. -/
noncomputable def WCp (β σ ω m α θ : ℝ) (zC : ℝ → S → Fin 4 → ℝ) (ε : ℝ) (sp : ℕ → S) : ℝ :=
  ∑' t, β ^ t * UCf σ ω m (zC ε (sp t)) (Dpath α θ ω zC ε sp t)

/-- Woodford (2003), App. A.3: The first-order coefficient `∂z_i(s)/∂ε` at `0`. -/
noncomputable def d1 {n : ℕ} (z : ℝ → S → Fin n → ℝ) (s : S) (i : Fin n) : ℝ :=
  deriv (fun ε => z ε s i) 0

/-- Woodford (2003), App. A.3: The second-order coefficient `∂²z_i(s)/∂ε²` at `0`. -/
noncomputable def d2 {n : ℕ} (z : ℝ → S → Fin n → ℝ) (s : S) (i : Fin n) : ℝ :=
  deriv (deriv (fun ε => z ε s i)) 0

/-- Woodford (2003), App. A.3: Components of a `C²` family are `C²`. -/
theorem contDiffAt_comp {n : ℕ} {z : ℝ → S → Fin n → ℝ} (hz : ContDiffAt ℝ 2 z 0) (s : S)
    (i : Fin n) : ContDiffAt ℝ 2 (fun ε => z ε s i) 0 :=
  contDiffAt_pi.1 (contDiffAt_pi.1 hz s) i

/-- Woodford (2003), App. A.3: The jet of a component. -/
theorem J_comp {n : ℕ} {z : ℝ → S → Fin n → ℝ} (hz : ContDiffAt ℝ 2 z 0) (s : S) (i : Fin n) :
    J2 (fun ε => z ε s i) (d1 z s i) (d2 z s i) :=
  J2_of_contDiffAt (contDiffAt_comp hz s i)

/-! ## The period expansions -/

/-- Woodford (2003), Ch. 6, §2 and Ch. 3 fn. 44 (**Rotemberg period utility to second order**):
on the resource manifold `ĉ = ŷ + log(C/Y)`, the jet of `ε ↦ u(Ĉ) − m·v(Ŷ)` at state `s` is
`((1−m)ŷ₁, (1−m)ŷ₂ + (1−σ−m(1+ω))ŷ₁² − ψπ₁²)`. -/
theorem J_UR (σ ω m ψ : ℝ) (hω : 0 ≤ ω) {zR : ℝ → S → Fin 3 → ℝ} (hR0 : zR 0 = 0)
    (hRC : ContDiffAt ℝ 2 zR 0)
    (hres : ∀ᶠ ε in 𝓝 0, ∀ s, zR ε s 2 = zR ε s 0 + Real.log (wedge ψ (zR ε s 1))) (s : S) :
    J2 (fun ε => URf σ ω m (zR ε s)) ((1 - m) * d1 zR s 0)
      ((1 - m) * d2 zR s 0 + (1 - σ - m * (1 + ω)) * d1 zR s 0 ^ 2 - ψ * d1 zR s 1 ^ 2) := by
  have hy := J_comp hRC s 0
  have hπ := J_comp hRC s 1
  have hy0 : (fun ε => zR ε s 0) 0 = 0 := by simp [hR0]
  have hπ0 : (fun ε => zR ε s 1) 0 = 0 := by simp [hR0]
  obtain ⟨F1, hF, hF1, hF0⟩ := J_lw ψ
  have hF' : ∀ᶠ y in 𝓝 ((fun ε => zR ε s 1) 0), HasDerivAt (fun π => Real.log (wedge ψ π))
      (F1 y) y := by rw [hπ0]; exact hF
  have hF1' : HasDerivAt F1 (-ψ) ((fun ε => zR ε s 1) 0) := by rw [hπ0]; exact hF1
  have hl := J2_comp hF' hF1' hπ
  have hc := J2_add hy hl
  have hc0 : (fun ε => zR ε s 0 + Real.log (wedge ψ (zR ε s 1))) 0 = 0 := by
    simp [hR0, wedge]
  have hu := J_uG σ hc hc0
  have hv := J_vv hω hy hy0
  have h := J2_sub hu (J2_const_mul m hv)
  have hF00 : F1 ((fun ε => zR ε s 1) 0) = 0 := by rw [hπ0]; exact hF0
  refine J2_eq (J2_congr_ev h ?_) ?_ ?_
  · filter_upwards [hres] with ε hε
    simp only [URf, hε s]
  · rw [hF00]; ring
  · rw [hF00]; ring

/-- Woodford (2003), Ch. 6, §2 (**the smooth part of Calvo period utility to second order**): the
jet of `ε ↦ u(Ŷ) − m·v(Ŷ)` is `((1−m)ŷ₁, (1−m)ŷ₂ + (1−σ−m(1+ω))ŷ₁²)`. -/
theorem J_UCs (σ ω m : ℝ) (hω : 0 ≤ ω) {zC : ℝ → S → Fin 4 → ℝ} (hC0 : zC 0 = 0)
    (hCC : ContDiffAt ℝ 2 zC 0) (s : S) :
    J2 (fun ε => uG σ (zC ε s 0) - m * vv ω (zC ε s 0)) ((1 - m) * d1 zC s 0)
      ((1 - m) * d2 zC s 0 + (1 - σ - m * (1 + ω)) * d1 zC s 0 ^ 2) := by
  have hy := J_comp hCC s 0
  have hy0 : (fun ε => zC ε s 0) 0 = 0 := by simp [hC0]
  have hu := J_uG σ hy hy0
  have hv := J_vv hω hy hy0
  exact J2_eq (J2_sub hu (J2_const_mul m hv)) (by ring) (by ring)

/-- Woodford (2003), App. A.3: `fdisp` is `C²` at `0`. -/
theorem contDiffAt_fdisp {α a b : ℝ} (hα1 : α < 1) :
    ContDiffAt ℝ 2 (NonlinearRotembergWelfare.fdisp α a b) 0 := by
  unfold NonlinearRotembergWelfare.fdisp
  have h1 : ContDiffAt ℝ 2 (fun π : ℝ => 1 - α * Real.exp (b * π)) 0 := by fun_prop
  have h2 := h1.rpow_const_of_ne (p := a / b) (by simp; linarith)
  exact (contDiffAt_const.mul (by fun_prop)).add (contDiffAt_const.mul h2)

/-- Woodford (2003), App. E.2 (**the dispersion law on the price-index curve to second order**):
the jet of `ε ↦ fdisp(π_ε(s))` is `(0, 2c_Cπ₁²)`, `c_C = αθ(1+ω)(1+ωθ)/(2(1−α))`. -/
theorem J_fdisp {α θ ω : ℝ} (hα1 : α < 1) (hθ : 1 < θ) {zC : ℝ → S → Fin 4 → ℝ}
    (hC0 : zC 0 = 0) (hCC : ContDiffAt ℝ 2 zC 0) (s : S) :
    J2 (fun ε => NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC ε s 1)) 0
      (2 * NonlinearRotembergWelfare.cC α θ ω * d1 zC s 1 ^ 2) := by
  have hπ := J_comp hCC s 1
  have hπ0 : (fun ε => zC ε s 1) 0 = 0 := by simp [hC0]
  have hf := J2_of_contDiffAt (contDiffAt_fdisp (a := θ * (1 + ω)) (b := θ - 1) hα1)
  obtain ⟨-, hd1, -⟩ := NonlinearRotembergWelfare.fdisp_second_order (a := θ * (1 + ω)) hα1
    (by linarith : θ - 1 ≠ 0)
  rw [hd1, ← NonlinearRotembergWelfare.cC_eq hα1 hθ] at hf
  obtain ⟨F1, hF, hF1, hF0⟩ := hf
  have hF' : ∀ᶠ y in 𝓝 ((fun ε => zC ε s 1) 0),
      HasDerivAt (NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1)) (F1 y) y := by
    rw [hπ0]; exact hF
  have hF1' : HasDerivAt F1 (2 * NonlinearRotembergWelfare.cC α θ ω)
      ((fun ε => zC ε s 1) 0) := by rw [hπ0]; exact hF1
  have h := J2_comp hF' hF1' hπ
  have hF00 : F1 ((fun ε => zC ε s 1) 0) = 0 := by rw [hπ0]; exact hF0
  exact J2_eq h (by rw [hF00]; ring) (by rw [hF00]; ring)

/-! ## Uniformity over the finite state space -/

omit [Fintype S] in
/-- Woodford (2003), Ch. 6, §2 (bounded fluctuations): finitely many jets give a UNIFORM `o(ε²)`
expansion. -/
theorem unif_taylor [Finite S] {f : S → ℝ → ℝ} {a1 a2 : S → ℝ} (hf : ∀ s, J2 (f s) (a1 s) (a2 s))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝 0, ∀ s, |f s ε - (f s 0 + a1 s * ε + a2 s / 2 * ε ^ 2)| ≤ η * ε ^ 2 :=
  Filter.eventually_all.2 fun s => taylor_J2 (hf s) hη

omit [Fintype S] in
/-- Woodford (2003), App. A.3: Finitely many functions differentiable at `0` and vanishing there
are `O(ε)` uniformly. -/
theorem unif_lin [Finite S] {g : S → ℝ → ℝ} {a : S → ℝ} (hg : ∀ s, HasDerivAt (g s) (a s) 0)
    (h0 : ∀ s, g s 0 = 0) : ∃ C ≥ 0, ∀ᶠ ε in 𝓝 0, ∀ s, |g s ε| ≤ C * |ε| := by
  let := Fintype.ofFinite S
  choose C hC0 hC using fun s => abs_le_lin (hg s) (h0 s)
  refine ⟨∑ s, C s, Finset.sum_nonneg fun s _ => hC0 s, ?_⟩
  filter_upwards [Filter.eventually_all.2 hC] with ε hε s
  refine (hε s).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  exact Finset.single_le_sum (f := C) (fun s _ => hC0 s) (Finset.mem_univ s)

/-- Woodford (2003), App. A.3: A uniform bound for a finite family. -/
theorem fin_bound (f : S → ℝ) : ∀ s, |f s| ≤ ∑ s', |f s'| := fun s =>
  Finset.single_le_sum (f := fun s' => |f s'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

/-- Woodford (2003), App. E.2: second-order dispersion is nonnegative and bounded,
`0 ≤ D_t ≤ cB²/(1 − α)`. -/
theorem Dsec_bound {α c B : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hc : 0 ≤ c) {π : ℕ → ℝ}
    (hB : ∀ t, |π t| ≤ B) (t : ℕ) :
    0 ≤ NonlinearRotembergWelfare.Dsec α c π t ∧
      NonlinearRotembergWelfare.Dsec α c π t ≤ c * B ^ 2 / (1 - α) := by
  have h1α : 0 < 1 - α := by linarith
  have hπ2 : ∀ t, π t ^ 2 ≤ B ^ 2 := fun t => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB t) 2
  have hcB : c * B ^ 2 ≤ c * B ^ 2 / (1 - α) := by
    rw [le_div_iff₀ h1α]; nlinarith [mul_nonneg hc (sq_nonneg B)]
  induction t with
  | zero =>
    rw [(NonlinearRotembergWelfare.Dsec_rec α c π 0).1]
    exact ⟨mul_nonneg hc (sq_nonneg _), (mul_le_mul_of_nonneg_left (hπ2 0) hc).trans hcB⟩
  | succ t ih =>
    rw [(NonlinearRotembergWelfare.Dsec_rec α c π t).2]
    refine ⟨add_nonneg (mul_nonneg hα0 ih.1) (mul_nonneg hc (sq_nonneg _)), ?_⟩
    have a := mul_le_mul_of_nonneg_left ih.2 hα0
    have b := mul_le_mul_of_nonneg_left (hπ2 (t + 1)) hc
    have e : α * (c * B ^ 2 / (1 - α)) + c * B ^ 2 = c * B ^ 2 / (1 - α) := by
      field_simp; ring
    linarith

set_option maxHeartbeats 1000000 in
-- the induction along the path with explicit constants
/-- Woodford (2003), App. E.2, p. 695 (**exact dispersion to second order, uniformly in the shock
path and the date**): if the policies are on the price-index curve, then for every `η > 0`,
for `ε` near `0`, along EVERY shock path and at EVERY date,
`|Δ_t − 1 − (ε²/2)D_t| ≤ ηε²`, with `D_t = αD_{t−1} + 2c_Cπ₁(s_t)²` from `D_{−1} = 0`. -/
theorem disp_expansion {α θ ω : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 1 < θ) (hω : 0 ≤ ω)
    {zC : ℝ → S → Fin 4 → ℝ} (hC0 : zC 0 = 0) (hCC : ContDiffAt ℝ 2 zC 0)
    (hCpi : ∀ᶠ ε in 𝓝 0, ∀ s, α * (Real.exp ((θ - 1) * zC ε s 1) - 1) +
      (1 - α) * (Real.exp (-((θ - 1) * ((zC ε s 3 - zC ε s 2) / (1 + ω * θ)))) - 1) = 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝 0, ∀ (sp : ℕ → S) (t : ℕ), |Dpath α θ ω zC ε sp t - 1 - ε ^ 2 / 2 *
      NonlinearRotembergWelfare.Dsec α (2 * NonlinearRotembergWelfare.cC α θ ω)
        (fun t => d1 zC (sp t) 1) t| ≤ η * ε ^ 2 := by
  have h1α : 0 < 1 - α := by linarith
  set κ := 2 * NonlinearRotembergWelfare.cC α θ ω with hκ
  have hκ0 : 0 ≤ κ := by
    simp only [hκ, NonlinearRotembergWelfare.cC]
    have : 0 ≤ θ := by linarith
    positivity
  set B := ∑ s, |d1 zC s 1| with hB
  have hBs : ∀ s, |d1 zC s 1| ≤ B := fin_bound _
  set η' := η * (1 - α) / 4 with hη'
  have hη'0 : 0 < η' := by positivity
  -- the dispersion law on the curve
  have hT := unif_taylor (f := fun s ε =>
    NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC ε s 1))
    (fun s => J_fdisp hα1 hθ hC0 hCC s) hη'0
  -- `e^{θ(1+ω)π} − 1 = O(ε)`
  have hπd : ∀ s, HasDerivAt (fun ε => zC ε s 1) (d1 zC s 1) 0 := fun s =>
    ((contDiffAt_comp hCC s 1).differentiableAt (by norm_num)).hasDerivAt
  obtain ⟨Cg, hCg0, hCg⟩ := unif_lin (g := fun s ε => Real.exp (θ * (1 + ω) * zC ε s 1) - 1)
    (fun s => (((hπd s).const_mul (θ * (1 + ω))).exp).sub_const 1)
    (fun s => by simp [hC0])
  set ε1 := min ((1 - α) / (2 * (α * Cg + 1)))
    (η' * 2 * (1 - α) / (α * Cg * κ * B ^ 2 + 1)) with hε1
  have hε10 : 0 < ε1 := lt_min (by positivity) (by positivity)
  have hsmall : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < ε1 := by
    have := Metric.ball_mem_nhds (0 : ℝ) hε10
    filter_upwards [this] with ε hε
    simpa [Real.dist_eq] using hε
  filter_upwards [hT, hCg, hCpi, hsmall] with ε hTε hCgε hpiε hεs
  intro sp
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  set D2 := NonlinearRotembergWelfare.Dsec α κ (fun t => d1 zC (sp t) 1) with hD2
  have hDb := Dsec_bound hα0 hα1 hκ0 (π := fun t => d1 zC (sp t) 1) (B := B) (fun t => hBs _)
  -- on the curve the dispersion law is `αG(Δ − 1) + fdisp(π)`
  have hcurve : ∀ s Δ, dispL α θ ω Δ (zC ε s) = α * Real.exp (θ * (1 + ω) * zC ε s 1) * (Δ - 1) +
      NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC ε s 1) := fun s Δ => by
    have h := NonlinearRotembergWelfare.disp_on_curve (a := θ * (1 + ω)) hα1
      (by linarith : θ - 1 ≠ 0) (hpiε s)
    rw [← h]; simp only [dispL]; ring
  -- the remainder at each state
  have hr : ∀ s, |NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC ε s 1) - 1 -
      ε ^ 2 / 2 * (κ * d1 zC s 1 ^ 2)| ≤ η' * ε ^ 2 := fun s => by
    have h := hTε s
    have h0 : NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC 0 s 1) = 1 := by
      simp only [hC0, Pi.zero_apply]
      exact (NonlinearRotembergWelfare.fdisp_second_order hα1 (by linarith : θ - 1 ≠ 0)).1
    simp only [h0, zero_mul, add_zero] at h
    have e : NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC ε s 1) - 1 -
        ε ^ 2 / 2 * (κ * d1 zC s 1 ^ 2) = NonlinearRotembergWelfare.fdisp α (θ * (1 + ω))
          (θ - 1) (zC ε s 1) - (1 + κ * d1 zC s 1 ^ 2 / 2 * ε ^ 2) := by ring
    rw [e]; exact h
  -- `αG ≤ (1 + α)/2` and the cross term
  have hG : ∀ s, 0 ≤ α * Real.exp (θ * (1 + ω) * zC ε s 1) ∧
      α * Real.exp (θ * (1 + ω) * zC ε s 1) ≤ (1 + α) / 2 := fun s => by
    refine ⟨mul_nonneg hα0 (Real.exp_pos _).le, ?_⟩
    have h1 := (abs_le.1 (hCgε s)).2
    have hε' : |ε| ≤ (1 - α) / (2 * (α * Cg + 1)) := hεs.le.trans (min_le_left _ _)
    have h3 : α * (Cg * |ε|) ≤ (1 - α) / 2 := by
      calc α * (Cg * |ε|) ≤ (α * Cg + 1) * |ε| := by nlinarith [abs_nonneg ε]
        _ ≤ (α * Cg + 1) * ((1 - α) / (2 * (α * Cg + 1))) := by gcongr
        _ = (1 - α) / 2 := by field_simp
    have := mul_le_mul_of_nonneg_left h1 hα0
    linarith
  have hcross : ∀ s t, α * |Real.exp (θ * (1 + ω) * zC ε s 1) - 1| * (ε ^ 2 / 2 * D2 t) ≤
      η' * ε ^ 2 := fun s t => by
    have hε' : |ε| ≤ η' * 2 * (1 - α) / (α * Cg * κ * B ^ 2 + 1) := hεs.le.trans (min_le_right _ _)
    have h1 : α * |Real.exp (θ * (1 + ω) * zC ε s 1) - 1| ≤ α * (Cg * |ε|) :=
      mul_le_mul_of_nonneg_left (hCgε s) hα0
    have h2 : ε ^ 2 / 2 * D2 t ≤ ε ^ 2 / 2 * (κ * B ^ 2 / (1 - α)) :=
      mul_le_mul_of_nonneg_left (hDb t).2 (by positivity)
    have h3 : α * (Cg * |ε|) * (ε ^ 2 / 2 * (κ * B ^ 2 / (1 - α))) =
        (α * Cg * κ * B ^ 2) * |ε| / (2 * (1 - α)) * ε ^ 2 := by field_simp
    have h4 : (α * Cg * κ * B ^ 2) * |ε| / (2 * (1 - α)) ≤ η' := by
      rw [div_le_iff₀ (by positivity)]
      calc (α * Cg * κ * B ^ 2) * |ε| ≤ (α * Cg * κ * B ^ 2 + 1) * |ε| := by
            nlinarith [abs_nonneg ε]
        _ ≤ (α * Cg * κ * B ^ 2 + 1) * (η' * 2 * (1 - α) / (α * Cg * κ * B ^ 2 + 1)) := by
            gcongr
        _ = η' * (2 * (1 - α)) := by field_simp
    calc α * |Real.exp (θ * (1 + ω) * zC ε s 1) - 1| * (ε ^ 2 / 2 * D2 t)
        ≤ α * (Cg * |ε|) * (ε ^ 2 / 2 * (κ * B ^ 2 / (1 - α))) := by
          gcongr
          exact mul_nonneg (by positivity) (hDb t).1
      _ ≤ η' * ε ^ 2 := by rw [h3]; exact mul_le_mul_of_nonneg_right h4 hε2
  -- the induction along the path
  have key : ∀ t, |Dpath α θ ω zC ε sp t - 1 - ε ^ 2 / 2 * D2 t| ≤ 4 * η' / (1 - α) * ε ^ 2 := by
    intro t
    induction t with
    | zero =>
      have e : Dpath α θ ω zC ε sp 0 - 1 - ε ^ 2 / 2 * D2 0 =
          NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC ε (sp 0) 1) - 1 -
            ε ^ 2 / 2 * (κ * d1 zC (sp 0) 1 ^ 2) := by
        simp only [Dpath, hD2, (NonlinearRotembergWelfare.Dsec_rec α κ _ 0).1, hcurve]; ring
      rw [e]
      refine (hr (sp 0)).trans ?_
      have : η' ≤ 4 * η' / (1 - α) := by
        rw [le_div_iff₀ h1α]; nlinarith
      exact mul_le_mul_of_nonneg_right this hε2
    | succ t ih =>
      set G := α * Real.exp (θ * (1 + ω) * zC ε (sp (t + 1)) 1) with hGd
      have e : Dpath α θ ω zC ε sp (t + 1) - 1 - ε ^ 2 / 2 * D2 (t + 1) =
          G * (Dpath α θ ω zC ε sp t - 1 - ε ^ 2 / 2 * D2 t) +
          α * (Real.exp (θ * (1 + ω) * zC ε (sp (t + 1)) 1) - 1) * (ε ^ 2 / 2 * D2 t) +
          (NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC ε (sp (t + 1)) 1) - 1 -
            ε ^ 2 / 2 * (κ * d1 zC (sp (t + 1)) 1 ^ 2)) := by
        simp only [Dpath, hD2, (NonlinearRotembergWelfare.Dsec_rec α κ _ t).2, hcurve, hGd]
        ring
      rw [e]
      obtain ⟨hG0, hG1⟩ := hG (sp (t + 1))
      have a1 : |G * (Dpath α θ ω zC ε sp t - 1 - ε ^ 2 / 2 * D2 t)| ≤
          (1 + α) / 2 * (4 * η' / (1 - α) * ε ^ 2) := by
        rw [abs_mul, abs_of_nonneg hG0]
        exact mul_le_mul hG1 ih (abs_nonneg _) (by linarith)
      have a2 : |α * (Real.exp (θ * (1 + ω) * zC ε (sp (t + 1)) 1) - 1) * (ε ^ 2 / 2 * D2 t)| ≤
          η' * ε ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα0,
          abs_of_nonneg (mul_nonneg (by positivity) (hDb t).1)]
        exact hcross _ t
      have a3 := hr (sp (t + 1))
      have e2 : (1 + α) / 2 * (4 * η' / (1 - α) * ε ^ 2) + η' * ε ^ 2 + η' * ε ^ 2 =
          4 * η' / (1 - α) * ε ^ 2 := by field_simp; ring
      calc _ ≤ |G * (Dpath α θ ω zC ε sp t - 1 - ε ^ 2 / 2 * D2 t)| +
            |α * (Real.exp (θ * (1 + ω) * zC ε (sp (t + 1)) 1) - 1) * (ε ^ 2 / 2 * D2 t)| +
            |NonlinearRotembergWelfare.fdisp α (θ * (1 + ω)) (θ - 1) (zC ε (sp (t + 1)) 1) - 1 -
              ε ^ 2 / 2 * (κ * d1 zC (sp (t + 1)) 1 ^ 2)| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ _ := by linarith
  intro t
  have e : 4 * η' / (1 - α) = η := by simp only [hη']; field_simp
  rw [← e]; exact key t

/-! ## Discounted sums -/

omit [Fintype S] in
/-- Woodford (2003), App. A.3: Discounted bounded sequences are summable. -/
theorem summable_disc {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → ℝ}
    (hf : ∀ t, |f t| ≤ K) : Summable fun t => β ^ t * f t := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
  exact mul_le_mul_of_nonneg_left (hf t) (pow_nonneg hβ0 t)

omit [Fintype S] in
/-- Woodford (2003), App. A.3: `|Σβᵗf_t − Σβᵗg_t| ≤ c/(1 − β)` when `|f_t − g_t| ≤ c` and both are
bounded. -/
theorem tsum_approx {β Kf Kg c : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → ℝ}
    (hf : ∀ t, |f t| ≤ Kf) (hg : ∀ t, |g t| ≤ Kg) (hfg : ∀ t, |f t - g t| ≤ c) :
    |∑' t, β ^ t * f t - ∑' t, β ^ t * g t| ≤ c / (1 - β) := by
  have hsf := summable_disc hβ0 hβ1 hf
  have hsg := summable_disc hβ0 hβ1 hg
  have hgeo := summable_geometric_of_lt_one hβ0 hβ1
  rw [← hsf.tsum_sub hsg]
  have hd : Summable fun t => β ^ t * f t - β ^ t * g t := hsf.sub hsg
  have hb : ∀ t, |β ^ t * f t - β ^ t * g t| ≤ β ^ t * c := fun t => by
    rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t)]
    exact mul_le_mul_of_nonneg_left (hfg t) (pow_nonneg hβ0 t)
  calc |∑' t, (β ^ t * f t - β ^ t * g t)| ≤ ∑' t, |β ^ t * f t - β ^ t * g t| := by
        have := norm_tsum_le_tsum_norm hd.norm
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' t, β ^ t * c := hd.abs.tsum_le_tsum hb (hgeo.mul_right c)
    _ = c / (1 - β) := by rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]; ring

omit [Fintype S] in
/-- Woodford (2003), App. A.3: `Σβᵗ(a_tε + (b_t/2)ε²) = εΣβᵗa_t + (ε²/2)Σβᵗb_t` for bounded `a`,
`b`. -/
theorem tsum_lin2 {β Ka Kb : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {a b : ℕ → ℝ}
    (ha : ∀ t, |a t| ≤ Ka) (hb : ∀ t, |b t| ≤ Kb) (ε : ℝ) :
    ∑' t, β ^ t * (a t * ε + b t / 2 * ε ^ 2) =
      ε * ∑' t, β ^ t * a t + ε ^ 2 / 2 * ∑' t, β ^ t * b t := by
  have hsa := summable_disc hβ0 hβ1 ha
  have hsb := summable_disc hβ0 hβ1 hb
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hsa.mul_left ε).tsum_add (hsb.mul_left (ε ^ 2 / 2))]
  exact tsum_congr fun t => by ring

/-! ## The second-order welfare of each model -/

/-- Woodford (2003), App. A.3: The second-order coefficient of Rotemberg period utility,
`(1−m)ŷ₂ + (1−σ−m(1+ω))ŷ₁² − ψπ₁²`. -/
noncomputable def A2R (σ ω m ψ : ℝ) (zR : ℝ → S → Fin 3 → ℝ) (s : S) : ℝ :=
  (1 - m) * d2 zR s 0 + (1 - σ - m * (1 + ω)) * d1 zR s 0 ^ 2 - ψ * d1 zR s 1 ^ 2

/-- Woodford (2003), App. A.3: The second-order coefficient of the smooth part of Calvo period
utility,
`(1−m)ŷ₂ + (1−σ−m(1+ω))ŷ₁²`. -/
noncomputable def A2C (σ ω m : ℝ) (zC : ℝ → S → Fin 4 → ℝ) (s : S) : ℝ :=
  (1 - m) * d2 zC s 0 + (1 - σ - m * (1 + ω)) * d1 zC s 0 ^ 2

/-- Woodford (2003), App. E.2: the second-order dispersion path `D_t = αD_{t−1} + 2c_Cπ₁(s_t)²`. -/
noncomputable def D2p (α θ ω : ℝ) (zC : ℝ → S → Fin 4 → ℝ) (sp : ℕ → S) (t : ℕ) : ℝ :=
  NonlinearRotembergWelfare.Dsec α (2 * NonlinearRotembergWelfare.cC α θ ω)
    (fun t => d1 zC (sp t) 1) t

set_option maxHeartbeats 1000000 in
-- the summation of the period expansions
/-- Woodford (2003), Ch. 6, §1–§2 and Ch. 3 fn. 44 (**Rotemberg welfare to second order, uniformly
over shock paths**): for every `η > 0`, for `ε` near `0` and EVERY path,
`|W_R(ε) − εΣβᵗ(1−m)ŷ₁ − (ε²/2)Σβᵗ[(1−m)ŷ₂ᴿ + (1−σ−m(1+ω))ŷ₁² − ψπ₁²]| ≤ ηε²`. -/
theorem WR_expansion {β σ ω m ψ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hω : 0 ≤ ω)
    {zR : ℝ → S → Fin 3 → ℝ} (hR0 : zR 0 = 0) (hRC : ContDiffAt ℝ 2 zR 0)
    (hres : ∀ᶠ ε in 𝓝 0, ∀ s, zR ε s 2 = zR ε s 0 + Real.log (wedge ψ (zR ε s 1)))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝 0, ∀ sp : ℕ → S, |WRp β σ ω m zR ε sp -
      (ε * ∑' t, β ^ t * ((1 - m) * d1 zR (sp t) 0) +
        ε ^ 2 / 2 * ∑' t, β ^ t * A2R σ ω m ψ zR (sp t))| ≤ η * ε ^ 2 := by
  have hT := unif_taylor (f := fun s ε => URf σ ω m (zR ε s))
    (fun s => J_UR σ ω m ψ hω hR0 hRC hres s) (by positivity : (0 : ℝ) < η * (1 - β))
  filter_upwards [hT] with ε hε sp
  have hU0 : ∀ s, URf σ ω m (zR 0 s) = 0 := fun s => by
    simp [URf, hR0, uG, NonlinearRotembergTrendWelfare.uu, vv]
  set a := fun t => (1 - m) * d1 zR (sp t) 0
  set b := fun t => A2R σ ω m ψ zR (sp t)
  have ha : ∀ t, |a t| ≤ ∑ s, |(1 - m) * d1 zR s 0| := fun t =>
    fin_bound (fun s => (1 - m) * d1 zR s 0) (sp t)
  have hb : ∀ t, |b t| ≤ ∑ s, |A2R σ ω m ψ zR s| := fun t =>
    fin_bound (fun s => A2R σ ω m ψ zR s) (sp t)
  have hf : ∀ t, |URf σ ω m (zR ε (sp t))| ≤ ∑ s, |URf σ ω m (zR ε s)| := fun t =>
    fin_bound (fun s => URf σ ω m (zR ε s)) _
  have hg : ∀ t, |a t * ε + b t / 2 * ε ^ 2| ≤
      (∑ s, |(1 - m) * d1 zR s 0|) * |ε| + (∑ s, |A2R σ ω m ψ zR s|) / 2 * ε ^ 2 := fun t => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ha t) (abs_nonneg _)
    · rw [abs_mul, abs_div, abs_two, abs_of_nonneg (sq_nonneg ε)]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hb t) (by norm_num))
        (sq_nonneg _)
  have hfg : ∀ t, |URf σ ω m (zR ε (sp t)) - (a t * ε + b t / 2 * ε ^ 2)| ≤
      η * (1 - β) * ε ^ 2 := fun t => by
    have h := hε (sp t)
    rw [hU0, zero_add] at h
    simp only [a, b, A2R] at h ⊢
    exact h
  have happ := tsum_approx hβ0.le hβ1 hf hg hfg
  rw [tsum_lin2 hβ0.le hβ1 ha hb ε] at happ
  have e : η * (1 - β) * ε ^ 2 / (1 - β) = η * ε ^ 2 := by
    have : 1 - β ≠ 0 := by linarith
    field_simp
  rw [e] at happ
  exact happ

set_option maxHeartbeats 2000000 in
-- the summation of the period expansions with the dispersion path
/-- Woodford (2003), Ch. 6, §2 and App. E.2 (**Calvo welfare to second order, with the exact
dispersion, uniformly over shock paths**): for every `η > 0`, for `ε` near `0` and EVERY path,
`|W_C(ε) − εΣβᵗ(1−m)ŷ₁ − (ε²/2)Σβᵗ[(1−m)ŷ₂ᶜ + (1−σ−m(1+ω))ŷ₁² − m/(1+ω)·D_t]| ≤ ηε²`. -/
theorem WC_expansion {β σ ω m α θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hω : 0 ≤ ω)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 1 < θ)
    {zC : ℝ → S → Fin 4 → ℝ} (hC0 : zC 0 = 0) (hCC : ContDiffAt ℝ 2 zC 0)
    (hCpi : ∀ᶠ ε in 𝓝 0, ∀ s, α * (Real.exp ((θ - 1) * zC ε s 1) - 1) +
      (1 - α) * (Real.exp (-((θ - 1) * ((zC ε s 3 - zC ε s 2) / (1 + ω * θ)))) - 1) = 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝 0, ∀ sp : ℕ → S, |WCp β σ ω m α θ zC ε sp -
      (ε * ∑' t, β ^ t * ((1 - m) * d1 zC (sp t) 0) +
        ε ^ 2 / 2 * ∑' t, β ^ t * (A2C σ ω m zC (sp t) - m / (1 + ω) * D2p α θ ω zC sp t))| ≤
        η * ε ^ 2 := by
  have h1β : 0 < 1 - β := by linarith
  have h1ω : 0 < 1 + ω := by linarith
  have h1α : 0 < 1 - α := by linarith
  set κ := 2 * NonlinearRotembergWelfare.cC α θ ω with hκ
  have hκ0 : 0 ≤ κ := by
    simp only [hκ, NonlinearRotembergWelfare.cC]
    have : 0 ≤ θ := by linarith
    positivity
  set B := ∑ s, |d1 zC s 1| with hB
  have hBs : ∀ s, |d1 zC s 1| ≤ B := fin_bound _
  set CΔ := 1 + κ * B ^ 2 / (1 - α) / 2 with hCΔ
  have hCΔ0 : 0 < CΔ := by positivity
  -- the smooth part
  set η1 := η * (1 - β) / 2 with hη1
  have hT := unif_taylor (f := fun s ε => uG σ (zC ε s 0) - m * vv ω (zC ε s 0))
    (fun s => J_UCs σ ω m hω hC0 hCC s) (by positivity : 0 < η1)
  -- the dispersion part
  set ηd := min 1 (η * (1 - β) * (1 + ω) / (4 * (|m| + 1))) with hηd
  have hηd0 : 0 < ηd := lt_min one_pos (by positivity)
  have hηd1 : ηd ≤ 1 := min_le_left _ _
  have hD := disp_expansion hα0 hα1 hθ hω hC0 hCC hCpi hηd0
  have hyd : ∀ s, HasDerivAt (fun ε => zC ε s 0) (d1 zC s 0) 0 := fun s =>
    ((contDiffAt_comp hCC s 0).differentiableAt (by norm_num)).hasDerivAt
  obtain ⟨Cy, hCy0, hCy⟩ := unif_lin (g := fun s ε => Real.exp ((1 + ω) * zC ε s 0) - 1)
    (fun s => (((hyd s).const_mul (1 + ω)).exp).sub_const 1)
    (fun s => by simp [hC0])
  have hsmall : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < ηd / (Cy * CΔ + 1) := by
    have := Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ηd / (Cy * CΔ + 1))
    filter_upwards [this] with ε hε
    simpa [Real.dist_eq] using hε
  filter_upwards [hT, hD, hCy, hsmall] with ε hTε hDε hCyε hεs sp
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hU0 : ∀ s, uG σ (zC 0 s 0) - m * vv ω (zC 0 s 0) = 0 := fun s => by
    simp [hC0, uG, NonlinearRotembergTrendWelfare.uu, vv]
  set D := Dpath α θ ω zC ε sp with hDdef
  set D2 := D2p α θ ω zC sp with hD2def
  have hDb : ∀ t, 0 ≤ D2 t ∧ D2 t ≤ κ * B ^ 2 / (1 - α) := fun t =>
    Dsec_bound hα0 hα1 hκ0 (π := fun t => d1 zC (sp t) 1) (fun t => hBs _) t
  have hDe : ∀ t, |D t - 1 - ε ^ 2 / 2 * D2 t| ≤ ηd * ε ^ 2 := fun t => hDε sp t
  have hD1 : ∀ t, |D t - 1| ≤ CΔ * ε ^ 2 := fun t => by
    have h := hDe t
    have h2 : |ε ^ 2 / 2 * D2 t| ≤ κ * B ^ 2 / (1 - α) / 2 * ε ^ 2 := by
      rw [abs_of_nonneg (mul_nonneg (by positivity) (hDb t).1)]
      have := mul_le_mul_of_nonneg_left (hDb t).2 (by positivity : (0 : ℝ) ≤ ε ^ 2 / 2)
      linarith
    have := abs_sub_abs_le_abs_sub (D t - 1) (ε ^ 2 / 2 * D2 t)
    have e : CΔ * ε ^ 2 = ηd * ε ^ 2 + (1 - ηd) * ε ^ 2 + κ * B ^ 2 / (1 - α) / 2 * ε ^ 2 := by
      simp only [hCΔ]; ring
    have : 0 ≤ (1 - ηd) * ε ^ 2 := mul_nonneg (by linarith) hε2
    linarith
  -- the period approximation
  set a := fun t => (1 - m) * d1 zC (sp t) 0
  set b := fun t => A2C σ ω m zC (sp t) - m / (1 + ω) * D2 t
  have ha : ∀ t, |a t| ≤ ∑ s, |(1 - m) * d1 zC s 0| := fun t =>
    fin_bound (fun s => (1 - m) * d1 zC s 0) (sp t)
  have hb : ∀ t, |b t| ≤ ∑ s, |A2C σ ω m zC s| + |m| / (1 + ω) * (κ * B ^ 2 / (1 - α)) :=
    fun t => by
      refine (abs_sub _ _).trans (add_le_add (fin_bound (fun s => A2C σ ω m zC s) (sp t)) ?_)
      rw [abs_mul, abs_div, abs_of_pos h1ω, abs_of_nonneg (hDb t).1]
      exact mul_le_mul_of_nonneg_left (hDb t).2 (by positivity)
  have hfg : ∀ t, |UCf σ ω m (zC ε (sp t)) (D t) - (a t * ε + b t / 2 * ε ^ 2)| ≤
      η * (1 - β) * ε ^ 2 := fun t => by
    have hs := hTε (sp t)
    rw [hU0, zero_add] at hs
    have eU : UCf σ ω m (zC ε (sp t)) (D t) = (uG σ (zC ε (sp t) 0) - m * vv ω (zC ε (sp t) 0)) -
        m / (1 + ω) * (Real.exp ((1 + ω) * zC ε (sp t) 0) * (D t - 1)) := by
      simp only [UCf, vv]; field_simp; ring
    have eb : a t * ε + b t / 2 * ε ^ 2 = ((1 - m) * d1 zC (sp t) 0 * ε +
        A2C σ ω m zC (sp t) / 2 * ε ^ 2) - m / (1 + ω) * (ε ^ 2 / 2 * D2 t) := by
      simp only [a, b]; ring
    rw [eU, eb]
    have ed : Real.exp ((1 + ω) * zC ε (sp t) 0) * (D t - 1) - ε ^ 2 / 2 * D2 t =
        (D t - 1 - ε ^ 2 / 2 * D2 t) + (Real.exp ((1 + ω) * zC ε (sp t) 0) - 1) * (D t - 1) := by
      ring
    have hcr : |(Real.exp ((1 + ω) * zC ε (sp t) 0) - 1) * (D t - 1)| ≤ ηd * ε ^ 2 := by
      rw [abs_mul]
      calc |Real.exp ((1 + ω) * zC ε (sp t) 0) - 1| * |D t - 1| ≤ (Cy * |ε|) * (CΔ * ε ^ 2) :=
            mul_le_mul (hCyε (sp t)) (hD1 t) (abs_nonneg _) (by positivity)
        _ = (Cy * CΔ) * |ε| * ε ^ 2 := by ring
        _ ≤ ηd * ε ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ hε2
            have h' := hεs.le
            rw [le_div_iff₀ (by positivity)] at h'
            nlinarith [abs_nonneg ε, mul_nonneg hCy0 hCΔ0.le]
    have hdisp : |Real.exp ((1 + ω) * zC ε (sp t) 0) * (D t - 1) - ε ^ 2 / 2 * D2 t| ≤
        2 * ηd * ε ^ 2 := by
      rw [ed]; refine (abs_add_le _ _).trans ?_; linarith [hDe t]
    have hm : |m / (1 + ω)| * (2 * ηd * ε ^ 2) ≤ η * (1 - β) / 2 * ε ^ 2 := by
      rw [abs_div, abs_of_pos h1ω]
      have h' : ηd ≤ η * (1 - β) * (1 + ω) / (4 * (|m| + 1)) := min_le_right _ _
      have : |m| / (1 + ω) * (2 * ηd) ≤ η * (1 - β) / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h1ω]
        calc |m| * (2 * ηd) ≤ (|m| + 1) * (2 * ηd) := by nlinarith [abs_nonneg m]
          _ ≤ (|m| + 1) * (2 * (η * (1 - β) * (1 + ω) / (4 * (|m| + 1)))) := by gcongr
          _ = η * (1 - β) / 2 * (1 + ω) := by field_simp; ring
      nlinarith
    have e2 : (uG σ (zC ε (sp t) 0) - m * vv ω (zC ε (sp t) 0) -
        m / (1 + ω) * (Real.exp ((1 + ω) * zC ε (sp t) 0) * (D t - 1))) -
        (((1 - m) * d1 zC (sp t) 0 * ε + A2C σ ω m zC (sp t) / 2 * ε ^ 2) -
          m / (1 + ω) * (ε ^ 2 / 2 * D2 t)) =
        (uG σ (zC ε (sp t) 0) - m * vv ω (zC ε (sp t) 0) -
          ((1 - m) * d1 zC (sp t) 0 * ε + A2C σ ω m zC (sp t) / 2 * ε ^ 2)) -
        m / (1 + ω) * (Real.exp ((1 + ω) * zC ε (sp t) 0) * (D t - 1) - ε ^ 2 / 2 * D2 t) := by
      ring
    rw [e2]
    have hs' : |uG σ (zC ε (sp t) 0) - m * vv ω (zC ε (sp t) 0) -
        ((1 - m) * d1 zC (sp t) 0 * ε + A2C σ ω m zC (sp t) / 2 * ε ^ 2)| ≤ η1 * ε ^ 2 := by
      simp only [A2C]; exact hs
    have h3 : |m / (1 + ω) * (Real.exp ((1 + ω) * zC ε (sp t) 0) * (D t - 1) -
        ε ^ 2 / 2 * D2 t)| ≤ η * (1 - β) / 2 * ε ^ 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hdisp (abs_nonneg _)).trans hm
    calc _ ≤ _ := abs_sub _ _
      _ ≤ η1 * ε ^ 2 + η * (1 - β) / 2 * ε ^ 2 := add_le_add hs' h3
      _ = η * (1 - β) * ε ^ 2 := by simp only [hη1]; ring
  -- bounds for the summation
  have hf : ∀ t, |UCf σ ω m (zC ε (sp t)) (D t)| ≤
      ((∑ s, |(1 - m) * d1 zC s 0|) * |ε| +
        (∑ s, |A2C σ ω m zC s| + |m| / (1 + ω) * (κ * B ^ 2 / (1 - α))) / 2 * ε ^ 2) +
      η * (1 - β) * ε ^ 2 := fun t => by
    have h1 := hfg t
    have h2 : |a t * ε + b t / 2 * ε ^ 2| ≤ (∑ s, |(1 - m) * d1 zC s 0|) * |ε| +
        (∑ s, |A2C σ ω m zC s| + |m| / (1 + ω) * (κ * B ^ 2 / (1 - α))) / 2 * ε ^ 2 := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ha t) (abs_nonneg _)
      · rw [abs_mul, abs_div, abs_two, abs_of_nonneg hε2]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hb t) (by norm_num)) hε2
    have := abs_sub_abs_le_abs_sub (UCf σ ω m (zC ε (sp t)) (D t)) (a t * ε + b t / 2 * ε ^ 2)
    linarith
  have hg : ∀ t, |a t * ε + b t / 2 * ε ^ 2| ≤ (∑ s, |(1 - m) * d1 zC s 0|) * |ε| +
      (∑ s, |A2C σ ω m zC s| + |m| / (1 + ω) * (κ * B ^ 2 / (1 - α))) / 2 * ε ^ 2 := fun t => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ha t) (abs_nonneg _)
    · rw [abs_mul, abs_div, abs_two, abs_of_nonneg hε2]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hb t) (by norm_num)) hε2
  have happ := tsum_approx hβ0.le hβ1 hf hg hfg
  rw [tsum_lin2 hβ0.le hβ1 ha hb ε] at happ
  have e : η * (1 - β) * ε ^ 2 / (1 - β) = η * ε ^ 2 := by field_simp
  rw [e] at happ
  exact happ

/-! ## The comparison -/

/-- Woodford (2003), App. A.3: `Dsec` is linear in its coefficient: `D(2c) = 2D(c)`. -/
theorem Dsec_two (α c : ℝ) (π : ℕ → ℝ) (t : ℕ) :
    NonlinearRotembergWelfare.Dsec α (2 * c) π t = 2 * NonlinearRotembergWelfare.Dsec α c π t := by
  unfold NonlinearRotembergWelfare.Dsec
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

set_option maxHeartbeats 1000000 in
-- the algebra of the discounted coefficients
omit [Fintype S] in
/-- Woodford (2003), Ch. 6, §2 and Ch. 3 fn. 44 (**the second-order coefficients differ only by
the distortion times second-order output**): if the first-order paths agree and
`ψ = θmα(1+ωθ)/((1−α)(1−αβ))`, then along every path
`Σβᵗ W₂ᴿ − Σβᵗ W₂ᶜ = (1 − m)Σβᵗ(ŷ₂ᴿ − ŷ₂ᶜ)`: the inflation costs cancel by
`NonlinearRotembergWelfare.discounted_cost_equiv`. -/
theorem second_coeff_diff [Finite S] {β σ ω m ψ α θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hω : 0 ≤ ω)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 1 < θ)
    (hψ : ψ = θ * m * α * (1 + ω * θ) / ((1 - α) * (1 - α * β)))
    {zR : ℝ → S → Fin 3 → ℝ} {zC : ℝ → S → Fin 4 → ℝ}
    (h1 : ∀ s, d1 zR s 0 = d1 zC s 0) (h2 : ∀ s, d1 zR s 1 = d1 zC s 1) (sp : ℕ → S) :
    ∑' t, β ^ t * A2R σ ω m ψ zR (sp t) -
        ∑' t, β ^ t * (A2C σ ω m zC (sp t) - m / (1 + ω) * D2p α θ ω zC sp t) =
      (1 - m) * ∑' t, β ^ t * (d2 zR (sp t) 0 - d2 zC (sp t) 0) := by
  let := Fintype.ofFinite S
  have h1α : 0 < 1 - α := by linarith
  set B := ∑ s, |d1 zC s 1| with hB
  have hBs : ∀ t, |d1 zC (sp t) 1| ≤ B := fun t => fin_bound (fun s => d1 zC s 1) (sp t)
  have hc0 : 0 ≤ NonlinearRotembergWelfare.cC α θ ω := by
    unfold NonlinearRotembergWelfare.cC
    have : 0 ≤ θ := by linarith
    positivity
  have hDb := fun t => Dsec_bound hα0 hα1 (by linarith : 0 ≤ 2 * NonlinearRotembergWelfare.cC α θ ω)
    (π := fun t => d1 zC (sp t) 1) (B := B) hBs t
  have hD2b : ∀ t, |D2p α θ ω zC sp t| ≤ 2 * NonlinearRotembergWelfare.cC α θ ω * B ^ 2 / (1 - α) :=
    fun t => by unfold D2p; rw [abs_of_nonneg (hDb t).1]; exact (hDb t).2
  have hπ2 : ∀ t, |d1 zC (sp t) 1 ^ 2| ≤ B ^ 2 := fun t => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hBs t) 2
  -- summabilities
  have sR := summable_disc hβ0.le hβ1 (fun t => fin_bound (fun s => A2R σ ω m ψ zR s) (sp t))
  have sC := summable_disc hβ0.le hβ1 (f := fun t => A2C σ ω m zC (sp t) -
      m / (1 + ω) * D2p α θ ω zC sp t)
    (K := ∑ s, |A2C σ ω m zC s| + |m / (1 + ω)| * (2 * NonlinearRotembergWelfare.cC α θ ω *
      B ^ 2 / (1 - α))) (fun t => (abs_sub _ _).trans (add_le_add
        (fin_bound (fun s => A2C σ ω m zC s) (sp t))
        (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD2b t) (abs_nonneg _))))
  have sY := summable_disc hβ0.le hβ1
    (fun t => fin_bound (fun s => d2 zR s 0 - d2 zC s 0) (sp t))
  have sD := summable_disc hβ0.le hβ1 (f := fun t => m / (1 + ω) * D2p α θ ω zC sp t)
    (fun t => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hD2b t) (abs_nonneg _))
  have sP := summable_disc hβ0.le hβ1 (f := fun t => ψ * d1 zC (sp t) 1 ^ 2)
    (fun t => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hπ2 t) (abs_nonneg _))
  -- the cost terms cancel
  have hcost : ∑' t, β ^ t * (m / (1 + ω) * D2p α θ ω zC sp t) =
      ∑' t, β ^ t * (ψ * d1 zC (sp t) 1 ^ 2) := by
    have e1 : (fun t => β ^ t * (m / (1 + ω) * D2p α θ ω zC sp t)) = fun t => 2 * (β ^ t *
        (m / (1 + ω) * NonlinearRotembergWelfare.Dsec α (NonlinearRotembergWelfare.cC α θ ω)
          (fun t => d1 zC (sp t) 1) t)) := by
      funext t; simp only [D2p, Dsec_two]; ring
    have e2 : (fun t => β ^ t * (ψ * d1 zC (sp t) 1 ^ 2)) =
        fun t => 2 * (β ^ t * (ψ / 2 * d1 zC (sp t) 1 ^ 2)) := by funext t; ring
    rw [e1, e2, tsum_mul_left, tsum_mul_left,
      NonlinearRotembergWelfare.discounted_cost_equiv hα0 hα1 hβ0 hβ1 hω hψ _ hBs]
  have hpt : ∀ t, β ^ t * A2R σ ω m ψ zR (sp t) -
      β ^ t * (A2C σ ω m zC (sp t) - m / (1 + ω) * D2p α θ ω zC sp t) =
      (1 - m) * (β ^ t * (d2 zR (sp t) 0 - d2 zC (sp t) 0)) +
        (β ^ t * (m / (1 + ω) * D2p α θ ω zC sp t) - β ^ t * (ψ * d1 zC (sp t) 1 ^ 2)) :=
    fun t => by simp only [A2R, A2C, h1, h2]; ring
  rw [← sR.tsum_sub sC, tsum_congr hpt, (sY.mul_left (1 - m)).tsum_add (sD.sub sP),
    tsum_mul_left, sD.tsum_sub sP, hcost, sub_self, add_zero]

set_option maxHeartbeats 1000000 in
-- combining the two expansions
/-- Woodford (2003), Ch. 6, §1–§2, App. E.2 and Ch. 3 fn. 44 (**Rotemberg versus Calvo welfare
under stochastic fluctuations, to second order**): if the first-order output and inflation paths
agree and `ψ = θmα(1+ωθ)/((1−α)(1−αβ))`, then for every `η > 0`, for `ε` near `0` and EVERY
shock path,
`|W_R(ε) − W_C(ε) − (ε²/2)(1 − m)Σβᵗ(ŷ₂ᴿ(s_t) − ŷ₂ᶜ(s_t))| ≤ ηε²`. -/
theorem welfare_difference {β σ ω m ψ α θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hω : 0 ≤ ω)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 1 < θ)
    (hψ : ψ = θ * m * α * (1 + ω * θ) / ((1 - α) * (1 - α * β)))
    {zR : ℝ → S → Fin 3 → ℝ} (hR0 : zR 0 = 0) (hRC : ContDiffAt ℝ 2 zR 0)
    (hres : ∀ᶠ ε in 𝓝 0, ∀ s, zR ε s 2 = zR ε s 0 + Real.log (wedge ψ (zR ε s 1)))
    {zC : ℝ → S → Fin 4 → ℝ} (hC0 : zC 0 = 0) (hCC : ContDiffAt ℝ 2 zC 0)
    (hCpi : ∀ᶠ ε in 𝓝 0, ∀ s, α * (Real.exp ((θ - 1) * zC ε s 1) - 1) +
      (1 - α) * (Real.exp (-((θ - 1) * ((zC ε s 3 - zC ε s 2) / (1 + ω * θ)))) - 1) = 0)
    (h1 : ∀ s, d1 zR s 0 = d1 zC s 0) (h2 : ∀ s, d1 zR s 1 = d1 zC s 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝 0, ∀ sp : ℕ → S, |WRp β σ ω m zR ε sp - WCp β σ ω m α θ zC ε sp -
      ε ^ 2 / 2 * ((1 - m) * ∑' t, β ^ t * (d2 zR (sp t) 0 - d2 zC (sp t) 0))| ≤ η * ε ^ 2 := by
  have hR := WR_expansion (σ := σ) (m := m) hβ0 hβ1 hω hR0 hRC hres (by positivity :
    (0 : ℝ) < η / 2)
  have hC := WC_expansion (σ := σ) (m := m) hβ0 hβ1 hω hα0 hα1 hθ hC0 hCC hCpi (by positivity :
    (0 : ℝ) < η / 2)
  filter_upwards [hR, hC] with ε hRε hCε sp
  have a := hRε sp
  have b := hCε sp
  have hdiff := second_coeff_diff (σ := σ) hβ0 hβ1 hω hα0 hα1 hθ hψ h1 h2 sp
  have h1t : ∑' t, β ^ t * ((1 - m) * d1 zR (sp t) 0) =
      ∑' t, β ^ t * ((1 - m) * d1 zC (sp t) 0) := tsum_congr fun t => by rw [h1]
  rw [h1t] at a
  have e : WRp β σ ω m zR ε sp - WCp β σ ω m α θ zC ε sp -
      ε ^ 2 / 2 * ((1 - m) * ∑' t, β ^ t * (d2 zR (sp t) 0 - d2 zC (sp t) 0)) =
      (WRp β σ ω m zR ε sp - (ε * ∑' t, β ^ t * ((1 - m) * d1 zC (sp t) 0) +
        ε ^ 2 / 2 * ∑' t, β ^ t * A2R σ ω m ψ zR (sp t))) -
      (WCp β σ ω m α θ zC ε sp - (ε * ∑' t, β ^ t * ((1 - m) * d1 zC (sp t) 0) +
        ε ^ 2 / 2 * ∑' t, β ^ t * (A2C σ ω m zC (sp t) - m / (1 + ω) * D2p α θ ω zC sp t))) := by
    rw [← hdiff]; ring
  rw [e]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ η / 2 * ε ^ 2 + η / 2 * ε ^ 2 := add_le_add a b
    _ = η * ε ^ 2 := by ring

/-- Woodford (2003), Ch. 6, §2 (**with an efficient steady state the second-order welfare of the
two models coincides**): at `m = 1`, `W_R(ε) − W_C(ε) = o(ε²)` uniformly over shock paths. -/
theorem welfare_coincide_efficient {β σ ω ψ α θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hω : 0 ≤ ω)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 1 < θ)
    (hψ : ψ = θ * 1 * α * (1 + ω * θ) / ((1 - α) * (1 - α * β)))
    {zR : ℝ → S → Fin 3 → ℝ} (hR0 : zR 0 = 0) (hRC : ContDiffAt ℝ 2 zR 0)
    (hres : ∀ᶠ ε in 𝓝 0, ∀ s, zR ε s 2 = zR ε s 0 + Real.log (wedge ψ (zR ε s 1)))
    {zC : ℝ → S → Fin 4 → ℝ} (hC0 : zC 0 = 0) (hCC : ContDiffAt ℝ 2 zC 0)
    (hCpi : ∀ᶠ ε in 𝓝 0, ∀ s, α * (Real.exp ((θ - 1) * zC ε s 1) - 1) +
      (1 - α) * (Real.exp (-((θ - 1) * ((zC ε s 3 - zC ε s 2) / (1 + ω * θ)))) - 1) = 0)
    (h1 : ∀ s, d1 zR s 0 = d1 zC s 0) (h2 : ∀ s, d1 zR s 1 = d1 zC s 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝 0, ∀ sp : ℕ → S,
      |WRp β σ ω 1 zR ε sp - WCp β σ ω 1 α θ zC ε sp| ≤ η * ε ^ 2 := by
  filter_upwards [welfare_difference hβ0 hβ1 hω hα0 hα1 hθ hψ hR0 hRC hres hC0 hCC hCpi h1 h2
    hη] with ε hε sp
  have := hε sp
  simpa using this

/-- Woodford (2003), Ch. 6, §1 (**expected discounted welfare**): for ANY expectation system and
any process `s_t(ω)` of the exogenous state, under the hypotheses of `welfare_difference`,
`|E₀W_R(ε) − E₀W_C(ε) − (ε²/2)(1 − m)E₀Σβᵗ(ŷ₂ᴿ − ŷ₂ᶜ)| ≤ ηε²` for `ε` near `0`, in every
state of the world. -/
theorem expected_welfare_difference {Ω : Type*} (𝔼 : ExpectationSystem Ω) (sh : ℕ → Ω → S)
    {β σ ω m ψ α θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hω : 0 ≤ ω)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : 1 < θ)
    (hψ : ψ = θ * m * α * (1 + ω * θ) / ((1 - α) * (1 - α * β)))
    {zR : ℝ → S → Fin 3 → ℝ} (hR0 : zR 0 = 0) (hRC : ContDiffAt ℝ 2 zR 0)
    (hres : ∀ᶠ ε in 𝓝 0, ∀ s, zR ε s 2 = zR ε s 0 + Real.log (wedge ψ (zR ε s 1)))
    {zC : ℝ → S → Fin 4 → ℝ} (hC0 : zC 0 = 0) (hCC : ContDiffAt ℝ 2 zC 0)
    (hCpi : ∀ᶠ ε in 𝓝 0, ∀ s, α * (Real.exp ((θ - 1) * zC ε s 1) - 1) +
      (1 - α) * (Real.exp (-((θ - 1) * ((zC ε s 3 - zC ε s 2) / (1 + ω * θ)))) - 1) = 0)
    (h1 : ∀ s, d1 zR s 0 = d1 zC s 0) (h2 : ∀ s, d1 zR s 1 = d1 zC s 1)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in 𝓝 0, ∀ ω0 : Ω,
      |𝔼.E 0 (fun ω' => WRp β σ ω m zR ε fun t => sh t ω') ω0 -
        𝔼.E 0 (fun ω' => WCp β σ ω m α θ zC ε fun t => sh t ω') ω0 -
        ε ^ 2 / 2 * ((1 - m) * 𝔼.E 0 (fun ω' => ∑' t, β ^ t *
          (d2 zR (sh t ω') 0 - d2 zC (sh t ω') 0)) ω0)| ≤ η * ε ^ 2 := by
  filter_upwards [welfare_difference hβ0 hβ1 hω hα0 hα1 hθ hψ hR0 hRC hres hC0 hCC hCpi h1 h2
    hη] with ε hε ω0
  set X : Ω → ℝ := fun ω' => WRp β σ ω m zR ε fun t => sh t ω'
  set Y : Ω → ℝ := fun ω' => WCp β σ ω m α θ zC ε fun t => sh t ω'
  set Z : Ω → ℝ := fun ω' => ∑' t, β ^ t * (d2 zR (sh t ω') 0 - d2 zC (sh t ω') 0)
  have hb : ∀ ω', |(X - Y - (ε ^ 2 / 2 * (1 - m)) • Z) ω'| ≤ η * ε ^ 2 := fun ω' => by
    have := hε fun t => sh t ω'
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, X, Y, Z]
    rw [show ε ^ 2 / 2 * (1 - m) * ∑' t, β ^ t * (d2 zR (sh t ω') 0 - d2 zC (sh t ω') 0) =
      ε ^ 2 / 2 * ((1 - m) * ∑' t, β ^ t * (d2 zR (sh t ω') 0 - d2 zC (sh t ω') 0)) by ring]
    exact this
  have h := 𝔼.abs_E_le hb 0 ω0
  rw [map_sub, map_sub, map_smul] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [show ε ^ 2 / 2 * ((1 - m) * 𝔼.E 0 Z ω0) = ε ^ 2 / 2 * (1 - m) * 𝔼.E 0 Z ω0 by ring]
  exact h

end Woodford.StabilizationWelfare.NonlinearRotembergStochWelfare
