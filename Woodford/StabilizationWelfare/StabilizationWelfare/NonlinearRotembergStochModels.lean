/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergStochWelfare

/-!
# Second-order welfare of the actual Rotemberg and Calvo perturbation equilibria

Woodford (2003), *Interest and Prices*, Chapter 6, §1–§2 (pp. 383–405), Appendix E.2 and
Chapter 3, footnote 44, with the Taylor principle (Proposition 4.3) and Appendix A.3.

On a finite Markov chain `(S, P)` both economies are hit by the same interest-rate disturbances
`εν(s)` and cost-push (markup) disturbances `εμ(s)` (neither enters preferences). Their perturbation
equilibria are the `C^∞` Rotemberg family of `NonlinearRotembergSmooth.markov_equilibrium_smooth`
and the `C²` Calvo family of `NonlinearNKMarkov.markov_equilibrium`. This module discharges every
hypothesis of `NonlinearRotembergStochWelfare.welfare_difference` for these actual equilibria:

* `rot_family`: the Rotemberg family is `C²` in `ε`, vanishes at `0`, is on the resource manifold
  and its derivative solves the linearised model;
* `calvo_pi`: the Calvo family is on the price-index curve;
* `models_families`: under the equivalence map the first-order output and inflation coincide
  (`NonlinearRotembergLinks.first_order_agree`);
* **`models_welfare_difference`**: for the actual perturbation equilibria, along every shock path,
  `W_R(ε) − W_C(ε) = (ε²/2)(1 − m)Σβᵗ(ŷ₂ᴿ(s_t) − ŷ₂ᶜ(s_t)) + o(ε²)` uniformly in the path, and the
  same for expected discounted welfare under every `ExpectationSystem`
  (**`models_expected_welfare_difference`**); at `m = 1` the two coincide to second order
  (**`models_coincide_efficient`**).
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergStochModels

open Filter Topology
open NonlinearRotembergStochWelfare
open NonlinearRotembergLinks (wedge)
open NonlinearNKMarkov (chainOp Stochastic IsMarkovEqm)

variable {S : Type} [Fintype S]

/-- Woodford (2003), Ch. 4 and Ch. 6: the Rotemberg disturbances `(ν, a, μ) = (ν(s), 0, μ(s))`. -/
def xiR (ν μ : S → ℝ) (s : S) : Fin 3 → ℝ := ![ν s, 0, μ s]

/-- Woodford (2003), §5: the Calvo disturbances `(ν, ĉ, τ̂, q, μ̂ʷ) = (ν(s), 0, 0, 0, μ(s))`. -/
def xiC (ν μ : S → ℝ) (s : S) : Fin 5 → ℝ := ![ν s, 0, 0, 0, μ s]

omit [Fintype S] in
/-- Woodford (2003), App. A.3: Components of a derivative of a family of policy functions. -/
theorem d1_eq {n : ℕ} {z : ℝ → S → Fin n → ℝ} {z1 : S → Fin n → ℝ} (h : HasDerivAt z z1 0)
    (s : S) (i : Fin n) : d1 z s i = z1 s i := by
  have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 h s) i
  exact h1.deriv

set_option maxHeartbeats 1000000 in
-- unpacking the implicit-function family
/-- Woodford (2003), App. A.3 and Ch. 3 fn. 44 (**the Rotemberg perturbation equilibrium**): under
the Taylor principle there is a family `ε ↦ z_ε` with `z₀ = 0`, of class `C²`, which is the Markov
equilibrium for `ε` near `0`, lies on the resource manifold `ĉ = ŷ + log(C/Y)`, and whose
derivative `z₁` solves the linearised model. -/
theorem rot_family (p : NonlinearRotemberg.Par) (hp : p.Std) {P : S → S → ℝ}
    (hP : Stochastic P) (ξ : S → Fin 3 → ℝ) :
    ∃ zR : ℝ → S → Fin 3 → ℝ, zR 0 = 0 ∧ ContDiffAt ℝ 2 zR 0 ∧
      (∀ᶠ ε in 𝓝 0, NonlinearRotembergSmooth.PhiJ P ξ (NonlinearRotembergSmooth.vecOf p, ε)
        (zR ε) = 0) ∧
      (∀ᶠ ε in 𝓝 0, ∀ s, zR ε s 2 = zR ε s 0 + Real.log (wedge p.ψ (zR ε s 1))) ∧
      NonlinearRotemberg.Lop p (chainOp P) (deriv zR 0) +
        (fun s => NonlinearRotemberg.DQe p (ξ s)) = 0 ∧
      ∃ r > 0, ∀ᶠ ε in 𝓝 0, ∀ w : S → Fin 3 → ℝ, ‖w‖ < r →
        NonlinearRotembergSmooth.PhiJ P ξ (NonlinearRotembergSmooth.vecOf p, ε) w = 0 →
          w = zR ε := by
  obtain ⟨r, hr, U, hU, g, hg0, hgC, hgE, hgU⟩ :=
    NonlinearRotembergSmooth.markov_equilibrium_smooth hp hP ξ
  set zR : ℝ → S → Fin 3 → ℝ := fun ε => g (NonlinearRotembergSmooth.vecOf p, ε) with hzR
  have hline : ContDiff ℝ 2 fun ε : ℝ => ((NonlinearRotembergSmooth.vecOf p, ε) :
      (Fin 8 → ℝ) × ℝ) := contDiff_const.prodMk contDiff_id
  have hC : ContDiffAt ℝ 2 zR 0 :=
    (NonlinearRotembergSmooth.smooth_Ck hgC 2).self_of_nhds.comp (0 : ℝ) hline.contDiffAt
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), (NonlinearRotembergSmooth.vecOf p, ε) ∈ U :=
    hline.continuous.continuousAt.preimage_mem_nhds hU
  have hE : ∀ᶠ ε in 𝓝 0, NonlinearRotembergSmooth.PhiJ P ξ
      (NonlinearRotembergSmooth.vecOf p, ε) (zR ε) = 0 :=
    hev.mono fun ε hε => (hgE _ hε).1
  refine ⟨zR, hg0, hC, hE, ?_, ?_, r, hr, hev.mono fun ε hε w hw hwE => hgU _ hε w hw hwE⟩
  · filter_upwards [hE] with ε hε s
    have h2 := congrFun (congrFun hε s) 2
    rw [NonlinearRotembergSmooth.PhiJ_apply] at h2
    have hN : ∀ s', NonlinearRotemberg.Nmap (NonlinearRotembergSmooth.parOf
        (NonlinearRotembergSmooth.vecOf p)) (ε • ξ s', zR ε s') 2 = 0 := fun s' => by
      simp [NonlinearRotemberg.Nmap]
    simp only [hN, mul_zero, Finset.sum_const_zero, add_zero, Pi.zero_apply] at h2
    have hres : NonlinearRotembergCentreLocal.Res p (zR ε s) := by
      simp only [NonlinearRotembergCentreLocal.Res, NonlinearRotemberg.Qmap,
        Matrix.cons_val] at h2 ⊢
      exact h2
    exact NonlinearRotembergCentreLocal.res_c hres
  · have hd : HasDerivAt zR (deriv zR 0) 0 :=
      (hC.differentiableAt (by norm_num)).hasDerivAt
    exact NonlinearRotembergSmooth.firstOrder P ξ hg0 hd hE

/-- Woodford (2003), §5 and App. A.3 (**the Calvo perturbation equilibrium is on the price-index
curve**): every Markov equilibrium satisfies
`α(e^{(θ−1)π} − 1) + (1 − α)(e^{−(θ−1)x̂} − 1) = 0`, `x̂ = (K̂ − F̂)/(1+ωθ)`, state by state. -/
theorem calvo_pi {c : NonlinearNKMarkov.Par} {P : S → S → ℝ} {ξ : S → Fin 5 → ℝ} {ε : ℝ}
    {z : S → Fin 4 → ℝ} (h : IsMarkovEqm c (chainOp P) ξ ε z) (s : S) :
    c.α * (Real.exp ((c.θ - 1) * z s 1) - 1) +
      (1 - c.α) * (Real.exp (-((c.θ - 1) * ((z s 3 - z s 2) / (1 + c.ω * c.θ)))) - 1) = 0 := by
  have h3 := congrFun (congrFun h s) 3
  simp only [NonlinearNKMarkov.Phi, NonlinearNKMarkov.Mv, Pi.add_apply, Pi.zero_apply] at h3
  have hN : (fun x' => NonlinearNKMarkov.Nmap c (ε • ξ x', z x') 3) = fun _ => 0 := by
    funext x'; simp [NonlinearNKMarkov.Nmap]
  have hz : chainOp P (fun _ => (0 : ℝ)) s = 0 := by simp [chainOp]
  simp only [hN, hz, add_zero] at h3
  simp only [NonlinearNKMarkov.Qmap, Matrix.cons_val, NonlinearNKMarkov.Par.c0] at h3
  rw [mul_div_assoc] at h3
  exact h3

set_option maxHeartbeats 1000000 in
-- assembling the two families and the first-order agreement
/-- Woodford (2003), App. A.3, Ch. 3 fn. 44 and Prop. 4.3 (**the two perturbation equilibria and
the hypotheses of the welfare comparison**): on a finite Markov chain with the same interest-rate
and cost-push disturbances, the same `β, σ, ω, θ, φ_π, φ_y`, the Taylor principle and the
equivalence map, there are the Rotemberg family `z^R` (`rot_family`) and the Calvo family `z^C`
(`NonlinearNKMarkov.markov_equilibrium`), both `C²` at `0` and vanishing there, equilibria for `ε`
near `0`, on the resource manifold resp. the price-index curve, with equal first-order output and
inflation; and they are the UNIQUE equilibria in fixed balls around the steady state. -/
theorem models_families (p : NonlinearRotemberg.Par) (c : NonlinearNKMarkov.Par)
    (hp : p.Std) (hc : c.Std) (hβ : p.β = c.β) (hσ : p.σ = c.σ) (hω : p.ω = c.ω)
    (hθ : p.θ = c.θ) (hφ : p.φ = c.φ) (hφy : p.φy = c.φy)
    (hψ : p.ψ = p.θ * p.m * c.α * (1 + p.ω * p.θ) / ((1 - c.α) * (1 - c.α * p.β)))
    {P : S → S → ℝ} (hP : Stochastic P) (ν μ : S → ℝ) :
    ∃ zR : ℝ → S → Fin 3 → ℝ, ∃ zC : ℝ → S → Fin 4 → ℝ,
      (∀ᶠ ε in 𝓝 0, NonlinearRotembergSmooth.PhiJ P (xiR ν μ)
        (NonlinearRotembergSmooth.vecOf p, ε) (zR ε) = 0) ∧
      (∀ᶠ ε in 𝓝 0, IsMarkovEqm c (chainOp P) (xiC ν μ) ε (zC ε)) ∧
      zR 0 = 0 ∧ zC 0 = 0 ∧ ContDiffAt ℝ 2 zR 0 ∧ ContDiffAt ℝ 2 zC 0 ∧
      (∀ᶠ ε in 𝓝 0, ∀ s, zR ε s 2 = zR ε s 0 + Real.log (wedge p.ψ (zR ε s 1))) ∧
      (∀ᶠ ε in 𝓝 0, ∀ s, c.α * (Real.exp ((p.θ - 1) * zC ε s 1) - 1) +
        (1 - c.α) * (Real.exp (-((p.θ - 1) * ((zC ε s 3 - zC ε s 2) / (1 + p.ω * p.θ)))) - 1) =
          0) ∧
      (∀ s, d1 zR s 0 = d1 zC s 0 ∧ d1 zR s 1 = d1 zC s 1) ∧
      (∃ r > 0, ∀ᶠ ε in 𝓝 0, ∀ w : S → Fin 3 → ℝ, ‖w‖ < r →
        NonlinearRotembergSmooth.PhiJ P (xiR ν μ) (NonlinearRotembergSmooth.vecOf p, ε) w = 0 →
          w = zR ε) ∧
      ∃ r > 0, ∀ᶠ ε in 𝓝 0, ∀ w : S → Fin 4 → ℝ, ‖w‖ < r →
        IsMarkovEqm c (chainOp P) (xiC ν μ) ε w → w = zC ε := by
  obtain ⟨zR, hR0, hRC, hRE, hres, hlin, hRU⟩ := rot_family p hp hP (xiR ν μ)
  obtain ⟨r, hr, δ, hδ, zC, hC0, hCC, hCE, hCU⟩ :=
    NonlinearNKMarkov.markov_equilibrium hc hP (xiC ν μ)
  have hCE' : ∀ᶠ ε in 𝓝 0, IsMarkovEqm c (chainOp P) (xiC ν μ) ε (zC ε) := by
    have := Metric.ball_mem_nhds (0 : ℝ) hδ
    filter_upwards [this] with ε hε
    exact (hCE ε (by simpa [Real.dist_eq] using hε)).1
  have hCd : HasDerivAt zC (deriv zC 0) 0 := (hCC.differentiableAt (by norm_num)).hasDerivAt
  have hRd : HasDerivAt zR (deriv zR 0) 0 := (hRC.differentiableAt (by norm_num)).hasDerivAt
  have hfo := fun s => NonlinearRotembergLinks.first_order_agree p c hp hc hβ hσ hω hθ hφ hφy hψ
    hP (xiC ν μ) (xiR ν μ) hC0 hCd hCE' hlin (fun s => by
      simp [xiR, xiC, chainOp]) (fun s => by simp [xiR, xiC, hσ, hω, add_comm]) s
  have h1 : ∀ s, d1 zR s 0 = d1 zC s 0 ∧ d1 zR s 1 = d1 zC s 1 := fun s => by
    rw [d1_eq hRd, d1_eq hRd, d1_eq hCd, d1_eq hCd]
    exact ⟨(hfo s).1.symm, (hfo s).2.symm⟩
  have hCpi : ∀ᶠ ε in 𝓝 0, ∀ s, c.α * (Real.exp ((p.θ - 1) * zC ε s 1) - 1) +
      (1 - c.α) * (Real.exp (-((p.θ - 1) * ((zC ε s 3 - zC ε s 2) / (1 + p.ω * p.θ)))) - 1) =
        0 := by
    filter_upwards [hCE'] with ε hε s
    rw [hθ, hω]; exact calvo_pi hε s
  have hCU' : ∀ᶠ ε in 𝓝 0, ∀ w : S → Fin 4 → ℝ, ‖w‖ < r →
      IsMarkovEqm c (chainOp P) (xiC ν μ) ε w → w = zC ε := by
    have := Metric.ball_mem_nhds (0 : ℝ) hδ
    filter_upwards [this] with ε hε w hw hwE
    exact hCU ε w (by simpa [Real.dist_eq] using hε) hw hwE
  exact ⟨zR, zC, hRE, hCE', hR0, hC0, hRC, hCC, hres, hCpi, h1, hRU, r, hr, hCU'⟩

/-- Woodford (2003), Ch. 6, §1–§2, App. E.2 and Ch. 3 fn. 44 (**the actual perturbation equilibria:
Rotemberg versus Calvo welfare to second order**): with the families of `models_families`, for
every `η > 0`, for `ε` near `0` and EVERY shock path,
`|W_R(ε) − W_C(ε) − (ε²/2)(1 − m)Σβᵗ(ŷ₂ᴿ(s_t) − ŷ₂ᶜ(s_t))| ≤ ηε²`. -/
theorem models_welfare_difference (p : NonlinearRotemberg.Par) (c : NonlinearNKMarkov.Par)
    (hp : p.Std) (hc : c.Std) (hβ : p.β = c.β) (hσ : p.σ = c.σ) (hω : p.ω = c.ω)
    (hθ : p.θ = c.θ) (hφ : p.φ = c.φ) (hφy : p.φy = c.φy)
    (hψ : p.ψ = p.θ * p.m * c.α * (1 + p.ω * p.θ) / ((1 - c.α) * (1 - c.α * p.β)))
    {P : S → S → ℝ} (hP : Stochastic P) (ν μ : S → ℝ) :
    ∃ zR : ℝ → S → Fin 3 → ℝ, ∃ zC : ℝ → S → Fin 4 → ℝ,
      (∀ᶠ ε in 𝓝 0, NonlinearRotembergSmooth.PhiJ P (xiR ν μ)
        (NonlinearRotembergSmooth.vecOf p, ε) (zR ε) = 0) ∧
      (∀ᶠ ε in 𝓝 0, IsMarkovEqm c (chainOp P) (xiC ν μ) ε (zC ε)) ∧
      ∀ η > 0, ∀ᶠ ε in 𝓝 0, ∀ sp : ℕ → S,
        |WRp p.β p.σ p.ω p.m zR ε sp - WCp p.β p.σ p.ω p.m c.α p.θ zC ε sp -
          ε ^ 2 / 2 * ((1 - p.m) * ∑' t, p.β ^ t * (d2 zR (sp t) 0 - d2 zC (sp t) 0))| ≤
          η * ε ^ 2 := by
  obtain ⟨zR, zC, hRE, hCE, hR0, hC0, hRC, hCC, hres, hCpi, h1, -, -⟩ :=
    models_families p c hp hc hβ hσ hω hθ hφ hφy hψ hP ν μ
  exact ⟨zR, zC, hRE, hCE, fun η hη => welfare_difference (σ := p.σ) hp.basic.β_pos
    hp.basic.β_lt_one hp.basic.ω_nonneg hc.α_pos.le hc.α_lt_one hp.basic.one_lt_θ hψ hR0 hRC
    hres hC0 hCC hCpi (fun s => (h1 s).1) (fun s => (h1 s).2) hη⟩

/-- Woodford (2003), Ch. 6, §1 (**expected discounted welfare of the actual equilibria**): for every
`ExpectationSystem` and every process `s_t(ω)` of the chain's state,
`|E₀W_R(ε) − E₀W_C(ε) − (ε²/2)(1 − m)E₀Σβᵗ(ŷ₂ᴿ − ŷ₂ᶜ)| ≤ ηε²` near `ε = 0`. -/
theorem models_expected_welfare_difference (p : NonlinearRotemberg.Par)
    (c : NonlinearNKMarkov.Par) (hp : p.Std) (hc : c.Std) (hβ : p.β = c.β) (hσ : p.σ = c.σ)
    (hω : p.ω = c.ω) (hθ : p.θ = c.θ) (hφ : p.φ = c.φ) (hφy : p.φy = c.φy)
    (hψ : p.ψ = p.θ * p.m * c.α * (1 + p.ω * p.θ) / ((1 - c.α) * (1 - c.α * p.β)))
    {P : S → S → ℝ} (hP : Stochastic P) (ν μ : S → ℝ) {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    (sh : ℕ → Ω → S) :
    ∃ zR : ℝ → S → Fin 3 → ℝ, ∃ zC : ℝ → S → Fin 4 → ℝ,
      (∀ᶠ ε in 𝓝 0, NonlinearRotembergSmooth.PhiJ P (xiR ν μ)
        (NonlinearRotembergSmooth.vecOf p, ε) (zR ε) = 0) ∧
      (∀ᶠ ε in 𝓝 0, IsMarkovEqm c (chainOp P) (xiC ν μ) ε (zC ε)) ∧
      ∀ η > 0, ∀ᶠ ε in 𝓝 0, ∀ ω0 : Ω,
        |𝔼.E 0 (fun ω' => WRp p.β p.σ p.ω p.m zR ε fun t => sh t ω') ω0 -
          𝔼.E 0 (fun ω' => WCp p.β p.σ p.ω p.m c.α p.θ zC ε fun t => sh t ω') ω0 -
          ε ^ 2 / 2 * ((1 - p.m) * 𝔼.E 0 (fun ω' => ∑' t, p.β ^ t *
            (d2 zR (sh t ω') 0 - d2 zC (sh t ω') 0)) ω0)| ≤ η * ε ^ 2 := by
  obtain ⟨zR, zC, hRE, hCE, hR0, hC0, hRC, hCC, hres, hCpi, h1, -, -⟩ :=
    models_families p c hp hc hβ hσ hω hθ hφ hφy hψ hP ν μ
  exact ⟨zR, zC, hRE, hCE, fun η hη => expected_welfare_difference 𝔼 sh (σ := p.σ)
    hp.basic.β_pos hp.basic.β_lt_one hp.basic.ω_nonneg hc.α_pos.le hc.α_lt_one
    hp.basic.one_lt_θ hψ hR0 hRC hres hC0 hCC hCpi (fun s => (h1 s).1) (fun s => (h1 s).2) hη⟩

/-- Woodford (2003), Ch. 6, §2 (**efficient steady state: the actual equilibria have the same
second-order welfare**): if moreover `m = 1`, then `W_R(ε) − W_C(ε) = o(ε²)` uniformly over shock
paths. -/
theorem models_coincide_efficient (p : NonlinearRotemberg.Par) (c : NonlinearNKMarkov.Par)
    (hp : p.Std) (hc : c.Std) (hβ : p.β = c.β) (hσ : p.σ = c.σ) (hω : p.ω = c.ω)
    (hθ : p.θ = c.θ) (hφ : p.φ = c.φ) (hφy : p.φy = c.φy) (hm : p.m = 1)
    (hψ : p.ψ = p.θ * p.m * c.α * (1 + p.ω * p.θ) / ((1 - c.α) * (1 - c.α * p.β)))
    {P : S → S → ℝ} (hP : Stochastic P) (ν μ : S → ℝ) :
    ∃ zR : ℝ → S → Fin 3 → ℝ, ∃ zC : ℝ → S → Fin 4 → ℝ,
      (∀ᶠ ε in 𝓝 0, NonlinearRotembergSmooth.PhiJ P (xiR ν μ)
        (NonlinearRotembergSmooth.vecOf p, ε) (zR ε) = 0) ∧
      (∀ᶠ ε in 𝓝 0, IsMarkovEqm c (chainOp P) (xiC ν μ) ε (zC ε)) ∧
      ∀ η > 0, ∀ᶠ ε in 𝓝 0, ∀ sp : ℕ → S,
        |WRp p.β p.σ p.ω p.m zR ε sp - WCp p.β p.σ p.ω p.m c.α p.θ zC ε sp| ≤ η * ε ^ 2 := by
  obtain ⟨zR, zC, hRE, hCE, h⟩ := models_welfare_difference p c hp hc hβ hσ hω hθ hφ hφy hψ hP ν μ
  refine ⟨zR, zC, hRE, hCE, fun η hη => ?_⟩
  filter_upwards [h η hη] with ε hε sp
  have := hε sp
  rw [show (1 : ℝ) - p.m = 0 by rw [hm]; ring, zero_mul, mul_zero, sub_zero] at this
  exact this

end Woodford.StabilizationWelfare.NonlinearRotembergStochModels
