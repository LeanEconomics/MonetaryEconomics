/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergCentreLocal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# A chart of the resource manifold and the forward map in the exact coordinates `(L, V)`

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.3 (p. 254) and Appendix A.3
(the implicit function theorem), for the exact Rotemberg model of `NonlinearRotembergCentreLocal`.
A perfect-foresight equilibrium determines next period's `σĉ′ + π′` and `G(x′)` EXPLICITLY from
today's state; the state itself is recovered from `(σĉ + π, G)` on the resource manifold by
inverting ONE scalar function,
`h(π) = e^{−(1−σ)π/σ}(e^π − 1)e^π/(1 − (ψ/2)(e^π − 1)²)` (`hfun`, `h(0) = 0`, `h′(0) = 1`),
with Mathlib's inverse function theorem (`phH`).

## Main results

* `Za_spec`: the chart `Za(a₁, a₂)` lies on the resource manifold with `σĉ + π = a₁` and
  `G = a₂`; `Zc_spec`: in the exact coordinates, `L(Zc q) = q₁`, `V(Zc q) = q₂`.
* `chart_local`: there is a ball around `0` on which the chart is defined, CONTINUOUS, and
  `Zc q → 0` as `q → 0`.
* `Tm` (the forward map `q ↦ (L, V)` of next period's state), `Tm_eq`:
  `Tm q = (L + D + ν, μV + E + ψΘν)` at `x = Zc q`; `continuousOn_Tm`.
* **`orbit_pfeq`**: every forward orbit of `Tm` inside the chart's ball gives an exact
  perfect-foresight equilibrium `x_t = Zc(Tmᵗ q₀)`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergCentreChart

open Filter Topology
open NonlinearRotemberg NonlinearRotembergCentreLocal
open NonlinearRotembergLinks (wedge)
open NonlinearRotembergBoundaryPair (Lf kc)

variable {p : Par}

/-! ## The scalar function and its local inverse -/

/-- Woodford (2003), App. A.3: `h(π) = e^{−(1−σ)π/σ}(e^π − 1)e^π/(C/Y)(π)`. -/
noncomputable def hfun (p : Par) (π : ℝ) : ℝ :=
  Real.exp (-(1 - p.σ) / p.σ * π) * ((Real.exp π - 1) * Real.exp π) / wedge p.ψ π

/-- Woodford (2003), App. A.3: `h(0) = 0`. -/
theorem hfun_zero : hfun p 0 = 0 := by simp [hfun]

/-- Woodford (2003), App. A.3: `h′(0) = 1`. -/
theorem hasDerivAt_hfun : HasDerivAt (hfun p) 1 0 := by
  have hw0 : wedge p.ψ 0 = 1 := by simp [wedge]
  have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul (-(1 - p.σ) / p.σ)).exp
  have h2 := ((Real.hasDerivAt_exp 0).sub_const 1).mul (Real.hasDerivAt_exp 0)
  have h3 := NonlinearRotembergLinks.hasDerivAt_wedge p.ψ 0
  have h := (h1.mul h2).div h3 (by rw [hw0]; norm_num)
  refine h.congr_deriv ?_
  simp [hw0]

/-- Woodford (2003), App. A.3: `h` is `C¹` at `0`. -/
theorem contDiffAt_hfun : ContDiffAt ℝ 1 (hfun p) 0 := by
  have hw : ContDiffAt ℝ 1 (wedge p.ψ) 0 := by unfold wedge; fun_prop
  have hn : ContDiffAt ℝ 1 (fun π : ℝ => Real.exp (-(1 - p.σ) / p.σ * π) *
      ((Real.exp π - 1) * Real.exp π)) 0 := by fun_prop
  exact hn.div hw (by simp [wedge])

/-- Woodford (2003), App. A.3: `h` has strict derivative `1` at `0`. -/
theorem hasStrictDerivAt_hfun : HasStrictDerivAt (hfun p) 1 0 :=
  contDiffAt_hfun.hasStrictDerivAt' hasDerivAt_hfun (by norm_num)

/-- Woodford (2003), App. A.3 (the inverse function theorem): a local homeomorphism inverting `h`
near `0`. -/
noncomputable def phH (p : Par) : OpenPartialHomeomorph ℝ ℝ :=
  (hasStrictDerivAt_hfun (p := p)).hasStrictFDerivAt_equiv one_ne_zero |>.toOpenPartialHomeomorph
    (hfun p)

/-- Woodford (2003), App. A.3: `phH` is `h`. -/
theorem phH_coe : (phH p : ℝ → ℝ) = hfun p := rfl

/-- Woodford (2003), App. A.3: `0` is in the source. -/
theorem zero_mem_source : (0 : ℝ) ∈ (phH p).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _

/-- Woodford (2003), App. A.3: `0` is in the target. -/
theorem zero_mem_target : (0 : ℝ) ∈ (phH p).target := by
  have := (phH p).map_source (zero_mem_source (p := p))
  rwa [phH_coe, hfun_zero] at this

/-- Woodford (2003), App. A.3: `h⁻¹(0) = 0`. -/
theorem symm_zero : (phH p).symm 0 = 0 := by
  have := (phH p).left_inv (zero_mem_source (p := p))
  rwa [phH_coe, hfun_zero] at this

/-! ## The chart -/

/-- Woodford (2003), App. A.3: The argument `b = a₂e^{−(1−σ)a₁/σ}/ψ` of `h⁻¹`. -/
noncomputable def bq (p : Par) (a1 a2 : ℝ) : ℝ := a2 * Real.exp (-(1 - p.σ) / p.σ * a1) / p.ψ

/-- Woodford (2003), Prop. 4.3: the chart `(a₁, a₂) ↦ x` with `π = h⁻¹(b)`, `ĉ = (a₁ − π)/σ`,
`ŷ = ĉ − log(C/Y)`. -/
noncomputable def Za (p : Par) (a1 a2 : ℝ) : Fin 3 → ℝ :=
  ![(a1 - (phH p).symm (bq p a1 a2)) / p.σ - Real.log (wedge p.ψ ((phH p).symm (bq p a1 a2))),
    (phH p).symm (bq p a1 a2), (a1 - (phH p).symm (bq p a1 a2)) / p.σ]

/-- Woodford (2003), Prop. 4.3 (**the chart inverts `(σĉ + π, G)` on the resource manifold**): if
`b ∈ target` and `C/Y > 0` at `π = h⁻¹(b)`, then `Za(a₁, a₂)` is on the resource manifold, with
`σĉ + π = a₁` and `G = a₂`. -/
theorem Za_spec (hp : p.Basic) {a1 a2 : ℝ} (ht : bq p a1 a2 ∈ (phH p).target)
    (hw : 0 < wedge p.ψ ((phH p).symm (bq p a1 a2))) :
    Res p (Za p a1 a2) ∧ p.σ * Za p a1 a2 2 + Za p a1 a2 1 = a1 ∧ Gadj p (Za p a1 a2) = a2 := by
  have hσ := hp.σ_pos.ne'
  have hψ := hp.ψ_pos.ne'
  set π := (phH p).symm (bq p a1 a2) with hπ
  have hh : hfun p π = bq p a1 a2 := (phH p).right_inv ht
  set w := wedge p.ψ π
  have hz0 : Za p a1 a2 0 = (a1 - π) / p.σ - Real.log w := rfl
  have hz1 : Za p a1 a2 1 = π := rfl
  have hz2 : Za p a1 a2 2 = (a1 - π) / p.σ := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Res, Qmap, Matrix.cons_val]
    rw [hz0, hz1, hz2, Real.exp_sub, Real.exp_log hw]
    change Real.exp ((a1 - π) / p.σ) - Real.exp ((a1 - π) / p.σ) / w * w = 0
    rw [div_mul_cancel₀ _ hw.ne', sub_self]
  · rw [hz1, hz2]; field_simp; ring
  · simp only [Gadj]
    rw [hz0, hz1, hz2]
    have e : (a1 - π) / p.σ - Real.log w - p.σ * ((a1 - π) / p.σ) =
        (-(1 - p.σ) / p.σ * π - Real.log w) + (1 - p.σ) / p.σ * a1 := by field_simp; ring
    rw [e, Real.exp_add, Real.exp_sub, Real.exp_log hw]
    simp only [hfun, bq] at hh
    have e2 : Real.exp (-(1 - p.σ) / p.σ * π) / w * ((Real.exp π - 1) * Real.exp π) =
        a2 * Real.exp (-(1 - p.σ) / p.σ * a1) / p.ψ := by
      rw [← hh]; ring
    have e3 : Real.exp (-(1 - p.σ) / p.σ * a1) * Real.exp ((1 - p.σ) / p.σ * a1) = 1 := by
      rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
    calc p.ψ * (Real.exp (-(1 - p.σ) / p.σ * π) / w * Real.exp ((1 - p.σ) / p.σ * a1) *
          ((Real.exp π - 1) * Real.exp π)) =
        p.ψ * (Real.exp (-(1 - p.σ) / p.σ * π) / w * ((Real.exp π - 1) * Real.exp π)) *
          Real.exp ((1 - p.σ) / p.σ * a1) := by ring
      _ = a2 * (Real.exp (-(1 - p.σ) / p.σ * a1) * Real.exp ((1 - p.σ) / p.σ * a1)) := by
          rw [e2]; field_simp
      _ = a2 := by rw [e3, mul_one]

/-- Woodford (2003), App. A.3: The denominator `ψΘkβ − (σ(1−β)ψ + Θ) < 0` of the inverse coordinate
change. -/
noncomputable def dn (p : Par) : ℝ := p.ψ * Th p * kc p * p.β - cE p

/-- Woodford (2003), App. A.3: `dn < 0`. -/
theorem dn_neg (hp : p.Basic) : dn p < 0 := by
  unfold dn
  have h1 : p.ψ * Th p * kc p * p.β ≤ 0 := by
    have := kc_nonpos hp; have := Th_pos hp; have := hp.ψ_pos; have := hp.β_pos
    have : 0 ≤ p.ψ * Th p := by positivity
    nlinarith [mul_nonpos_of_nonneg_of_nonpos this (kc_nonpos hp)]
  linarith [cE_pos hp]

/-- Woodford (2003), App. A.3: The linear coordinate change `(a₁, a₂) ↦ (L, V) = (a₁ − kβa₂, ψΘa₁ −
(σ(1−β)ψ + Θ)a₂)`. -/
noncomputable def Lmap (p : Par) (a : ℝ × ℝ) : ℝ × ℝ :=
  (a.1 - kc p * p.β * a.2, p.ψ * Th p * a.1 - cE p * a.2)

/-- Woodford (2003), App. A.3: Its inverse. -/
noncomputable def Ainv (p : Par) (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 + kc p * p.β * ((q.2 - p.ψ * Th p * q.1) / dn p), (q.2 - p.ψ * Th p * q.1) / dn p)

/-- Woodford (2003), App. A.3: `Lmap ∘ Ainv = id`. -/
theorem Lmap_Ainv (hp : p.Basic) (q : ℝ × ℝ) : Lmap p (Ainv p q) = q := by
  have hd := (dn_neg hp).ne
  ext
  · simp only [Lmap, Ainv]; ring
  · simp only [Lmap, Ainv]; unfold dn at hd ⊢; field_simp; ring

/-- Woodford (2003), App. A.3: `Ainv ∘ Lmap = id`. -/
theorem Ainv_Lmap (hp : p.Basic) (a : ℝ × ℝ) : Ainv p (Lmap p a) = a := by
  have hd := (dn_neg hp).ne
  have hq : (p.ψ * Th p * a.1 - cE p * a.2 - p.ψ * Th p * (a.1 - kc p * p.β * a.2)) / dn p =
      a.2 := by
    rw [div_eq_iff hd]; unfold dn; ring
  ext
  · simp only [Lmap, Ainv]; rw [hq]; ring
  · simp only [Lmap, Ainv]; rw [hq]

/-- Woodford (2003), Prop. 4.3: the chart in the exact coordinates, `Zc q = Za(Ainv q)`. -/
noncomputable def Zc (p : Par) (q : ℝ × ℝ) : Fin 3 → ℝ := Za p (Ainv p q).1 (Ainv p q).2

/-- Woodford (2003), App. A.3: The domain condition of the chart at `q`. -/
def Dom (p : Par) (q : ℝ × ℝ) : Prop :=
  bq p (Ainv p q).1 (Ainv p q).2 ∈ (phH p).target ∧
    0 < wedge p.ψ ((phH p).symm (bq p (Ainv p q).1 (Ainv p q).2))

/-- Woodford (2003), Prop. 4.3 (**the chart in exact coordinates**): on its domain, `Zc q` lies on
the resource manifold, with `L(Zc q) = q₁` and `V(Zc q) = q₂`. -/
theorem Zc_spec (hp : p.Basic) {q : ℝ × ℝ} (hq : Dom p q) :
    Res p (Zc p q) ∧ Lf p (Zc p q) = q.1 ∧ Vf p (Zc p q) = q.2 := by
  have h1 : Res p (Zc p q) := (Za_spec hp hq.1 hq.2).1
  have h2 : p.σ * Zc p q 2 + Zc p q 1 = (Ainv p q).1 := (Za_spec hp hq.1 hq.2).2.1
  have h3 : Gadj p (Zc p q) = (Ainv p q).2 := (Za_spec hp hq.1 hq.2).2.2
  have hL := congrArg Prod.fst (Lmap_Ainv hp q)
  have hV := congrArg Prod.snd (Lmap_Ainv hp q)
  simp only [Lmap] at hL hV
  refine ⟨h1, ?_, ?_⟩
  · calc Lf p (Zc p q) = (p.σ * Zc p q 2 + Zc p q 1) - kc p * p.β * Gadj p (Zc p q) := rfl
      _ = q.1 := by rw [h2, h3, hL]
  · calc Vf p (Zc p q) = p.ψ * Th p * (p.σ * Zc p q 2 + Zc p q 1) - cE p * Gadj p (Zc p q) :=
          rfl
      _ = q.2 := by rw [h2, h3, hV]

/-- Woodford (2003), App. A.3: `Zc 0 = 0`. -/
theorem Zc_zero : Zc p 0 = 0 := by
  have hA : Ainv p 0 = 0 := by ext <;> simp [Ainv]
  have hb : bq p 0 0 = 0 := by simp [bq]
  funext i
  fin_cases i <;> simp [Zc, Za, hA, hb, symm_zero, wedge]

/-- Woodford (2003), App. A.3: `Ainv` is continuous. -/
theorem continuous_Ainv : Continuous (Ainv p) := by
  unfold Ainv; fun_prop

/-- Woodford (2003), App. A.3 (**the chart is defined and continuous near `0`**): there is
`ρ > 0` such that every `q` with `‖q‖ < ρ` is in the domain, `Zc` is continuous on that ball, and
`Zc q → 0` as `q → 0`. -/
theorem chart_local : ∃ ρ > 0, (∀ q : ℝ × ℝ, ‖q‖ < ρ → Dom p q) ∧
    ContinuousOn (Zc p) (Metric.ball 0 ρ) ∧ Tendsto (Zc p) (𝓝 0) (𝓝 0) := by
  set B : ℝ × ℝ → ℝ := fun q => bq p (Ainv p q).1 (Ainv p q).2 with hB
  have hBc : Continuous B := by
    simp only [hB, bq]
    have := continuous_Ainv (p := p)
    fun_prop
  have hB0 : B 0 = 0 := by
    have hA : Ainv p 0 = 0 := by ext <;> simp [Ainv]
    simp [hB, hA, bq]
  have htn : (phH p).target ∈ 𝓝 (B 0) := by
    rw [hB0]; exact (phH p).open_target.mem_nhds zero_mem_target
  have ht : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), B q ∈ (phH p).target :=
    hBc.continuousAt.preimage_mem_nhds htn
  have hsc : ContinuousAt (fun q => (phH p).symm (B q)) 0 := by
    have := (phH p).continuousAt_symm (show B 0 ∈ (phH p).target by
      rw [hB0]; exact zero_mem_target)
    exact this.comp hBc.continuousAt
  have hs0 : (phH p).symm (B 0) = 0 := by rw [hB0, symm_zero]
  have hwc : Continuous (wedge p.ψ) := by unfold wedge; fun_prop
  have hw : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), 0 < wedge p.ψ ((phH p).symm (B q)) := by
    have := (hwc.continuousAt.comp hsc)
    have h1 : 0 < wedge p.ψ ((phH p).symm (B 0)) := by rw [hs0]; simp [wedge]
    exact this.eventually (lt_mem_nhds h1)
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (ht.and hw)
  have hdom : ∀ q : ℝ × ℝ, ‖q‖ < ρ → Dom p q := fun q hq =>
    hball (by simpa [dist_zero_right] using hq)
  refine ⟨ρ, hρ, hdom, ?_, ?_⟩
  · have hmaps : Set.MapsTo B (Metric.ball 0 ρ) (phH p).target := fun q hq =>
      (hdom q (by simpa using hq)).1
    have hsym : ContinuousOn (fun q => (phH p).symm (B q)) (Metric.ball 0 ρ) :=
      (phH p).continuousOn_symm.comp hBc.continuousOn hmaps
    have hA1 : Continuous fun q => (Ainv p q).1 := continuous_fst.comp continuous_Ainv
    have hlog : ContinuousOn (fun q => Real.log (wedge p.ψ ((phH p).symm (B q))))
        (Metric.ball 0 ρ) :=
      (hwc.comp_continuousOn hsym).log fun q hq => (hdom q (by simpa using hq)).2.ne'
    refine continuousOn_pi.2 fun i => ?_
    fin_cases i
    · exact ((hA1.continuousOn.sub hsym).div_const _).sub hlog
    · exact hsym
    · exact (hA1.continuousOn.sub hsym).div_const _
  · have hA1 : Continuous fun q => (Ainv p q).1 := continuous_fst.comp continuous_Ainv
    have hlog : ContinuousAt (fun q => Real.log (wedge p.ψ ((phH p).symm (B q)))) 0 :=
      (hwc.continuousAt.comp hsc).log (by rw [Function.comp_apply, hs0]; simp [wedge])
    have hc : ContinuousAt (Zc p) 0 := by
      refine continuousAt_pi.2 fun i => ?_
      fin_cases i
      · exact ((hA1.continuousAt.sub hsc).div_const _).sub hlog
      · exact hsc
      · exact (hA1.continuousAt.sub hsc).div_const _
    have := hc.tendsto
    rwa [Zc_zero] at this

/-! ## The forward map -/

/-- Woodford (2003), Ch. 4 (2.7)–(2.8): next period's `(σĉ′ + π′, G(x′))` from today's state,
`(φ_ππ + φ_yŷ + ν + σĉ, (G − H)/β)`. -/
noncomputable def Rf (p : Par) (ν : ℝ) (z : Fin 3 → ℝ) : ℝ × ℝ :=
  (p.φ * z 1 + p.φy * z 0 + ν + p.σ * z 2, (Gadj p z - Hmc p 0 z) / p.β)

/-- Woodford (2003), Prop. 4.3: the forward map in the exact coordinates,
`Tm q = Lmap(R(Zc q))`. -/
noncomputable def Tm (p : Par) (ν : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := Lmap p (Rf p ν (Zc p q))

/-- Woodford (2003), Prop. 4.3 (**the forward map is the exact planar recursion**):
`Tm q = (L + D(x) + ν, μV + E(x) + ψΘν)` at `x = Zc q`. -/
theorem Tm_eq (hp : p.Basic) (ν : ℝ) (q : ℝ × ℝ) :
    Tm p ν q = (Lf p (Zc p q) + Dfun p (Zc p q) + ν,
      mu p * Vf p (Zc p q) + Efun p (Zc p q) + p.ψ * Th p * ν) := by
  have hβ := hp.β_pos.ne'
  ext
  · simp only [Tm, Lmap, Rf, Lf, Dfun]; field_simp; ring
  · simp only [Tm, Lmap, Rf, Vf, Efun]; ring

/-- Woodford (2003), App. A.3: `R` is continuous. -/
theorem continuous_Rf (ν : ℝ) : Continuous (Rf p ν) := by
  unfold Rf Gadj Hmc; fun_prop

/-- Woodford (2003), App. A.3: The forward map is continuous on the chart's ball. -/
theorem continuousOn_Tm {ρ : ℝ} (hc : ContinuousOn (Zc p) (Metric.ball 0 ρ)) (ν : ℝ) :
    ContinuousOn (Tm p ν) (Metric.ball 0 ρ) := by
  have hL : Continuous (Lmap p) := by unfold Lmap; fun_prop
  exact hL.comp_continuousOn ((continuous_Rf ν).comp_continuousOn hc)

/-- Woodford (2003), Ch. 4 (2.7)–(2.8) (**orbits of the forward map are equilibria**): if every
`Tmᵗ q₀` is in the chart's domain, `x_t = Zc(Tmᵗ q₀)` is an exact perfect-foresight equilibrium
with the constant disturbance `ν`. -/
theorem orbit_pfeq (hp : p.Basic) (ν : ℝ) (q0 : ℝ × ℝ) (hdom : ∀ t, Dom p ((Tm p ν)^[t] q0)) :
    PFEq p ν (fun t => Zc p ((Tm p ν)^[t] q0)) := by
  have hβ := hp.β_pos.ne'
  refine pf_of_rec (fun t => (Zc_spec hp (hdom t)).1) (fun t => ?_) (fun t => ?_)
  · have hA := Za_spec hp (hdom (t + 1)).1 (hdom (t + 1)).2
    have e : Ainv p ((Tm p ν)^[t + 1] q0) = Rf p ν (Zc p ((Tm p ν)^[t] q0)) := by
      rw [Function.iterate_succ_apply', Tm, Ainv_Lmap hp]
    have h2 := hA.2.1
    rw [e] at h2
    simp only [Zc] at h2 ⊢
    rw [e]
    simp only [Rf] at h2
    exact h2
  · have hA := Za_spec hp (hdom (t + 1)).1 (hdom (t + 1)).2
    have e : Ainv p ((Tm p ν)^[t + 1] q0) = Rf p ν (Zc p ((Tm p ν)^[t] q0)) := by
      rw [Function.iterate_succ_apply', Tm, Ainv_Lmap hp]
    have h3 := hA.2.2
    simp only [Zc] at h3 ⊢
    rw [e] at h3 ⊢
    rw [h3]
    simp only [Rf, Zc]
    field_simp

end Woodford.StabilizationWelfare.NonlinearRotembergCentreChart
