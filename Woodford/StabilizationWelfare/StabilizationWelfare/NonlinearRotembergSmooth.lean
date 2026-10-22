/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergMarkov

/-!
# Smoothness of the Rotemberg Markov equilibrium in the shock scale and the parameters

Woodford (2003), *Interest and Prices*, Chapter 6, §1 (pp. 383–392: the welfare approximations
are taken along a one-parameter family of economies whose equilibria are smooth in the amplitude
of the disturbances), Appendix A.3 (the implicit function theorem), Chapter 3, fn. 44 (p. 188)
and Chapter 4, Proposition 4.3 (p. 254), for the exact Rotemberg model of `NonlinearRotemberg`.

## Main results

* **`markov_equilibrium_smooth`**: on a finite Markov chain, under the Taylor principle, the
  Markov equilibrium is a `C^∞` function `g(c, ε)` of the parameter vector
  `c = (β, σ, ω, θ, ψ, m, φ_π, φ_y)` (`vecOf`, `parOf`) and of the shock scale `ε`, near
  `(c₀, 0)`; `g(c₀, 0) = 0` (the steady state for every parameter vector), `g(c, ε)` is an
  equilibrium of the economy with parameters `c` and disturbances `εξ`, and it is the unique
  equilibrium in a fixed ball; `smooth_Ck` gives `Cᵏ` on a neighbourhood for every `k`.
* **`firstOrder`**, **`firstOrder_eqs`**, **`first_order_of_smooth`**: the first-order solution
  `∂g/∂ε` solves the linearised model: `ĉ₁ = ŷ₁`, the IS curve with the rule, and the NKPC
  `π₁ = κ(ŷ₁ − ŷⁿ) + βPπ₁` with the Rotemberg slope and `ŷⁿ = ((1+ω)a − μ)/(σ + ω)`.
* **`lop_injective_iff`**: the linearised operator is injective on every finite Markov chain iff
  the Taylor principle holds in the Rotemberg slope (necessity: an explicit two-state chain with a
  kernel).
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergSmooth

open Filter Topology
open NonlinearNKMarkov (Mv IsMarkov chainOp Stochastic chainOp_isMarkov)
open NonlinearNKMarkovGeneral (Mv_const)
open NonlinearRotemberg NonlinearRotembergNewton NonlinearRotembergMarkov

/-! ## Parameters as a vector -/

/-- The parameter vector `(β, σ, ω, θ, ψ, m, φ_π, φ_y)` as a structure. -/
def parOf (c : Fin 8 → ℝ) : Par := ⟨c 0, c 1, c 2, c 3, c 4, c 5, c 6, c 7⟩

/-- The structure as a parameter vector. -/
def vecOf (p : Par) : Fin 8 → ℝ := ![p.β, p.σ, p.ω, p.θ, p.ψ, p.m, p.φ, p.φy]

/-- `parOf ∘ vecOf = id`. -/
theorem parOf_vecOf (p : Par) : parOf (vecOf p) = p := rfl

/-- Woodford (2003), App. A.3: the current-date part is jointly `C^∞` in the parameters, the
disturbances and the endogenous variables. -/
theorem contDiff_Qj {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun w : (Fin 8 → ℝ) × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => Qmap (parOf w.1) w.2) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Qmap, Gadj, Hmc, parOf, Fin.zero_eta, Fin.isValue,
    Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    fun_prop

/-- Woodford (2003), App. A.3: the part inside `E_t` is jointly `C^∞`. -/
theorem contDiff_Nj {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun w : (Fin 8 → ℝ) × ((Fin 3 → ℝ) × (Fin 3 → ℝ)) => Nmap (parOf w.1) w.2) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Nmap, Gadj, parOf, Fin.zero_eta, Fin.isValue,
    Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    fun_prop

/-! ## The residual map on a finite chain, jointly in parameters, shock scale and policy -/

variable {S : Type*} [Fintype S]

/-- Woodford (2003), App. A.3: the residual of the Markov conditions on a finite chain with
parameters `q.1`, amplitude `q.2` and disturbance pattern `ξ`. -/
noncomputable def PhiJ (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) (q : (Fin 8 → ℝ) × ℝ)
    (z : S → Fin 3 → ℝ) : S → Fin 3 → ℝ :=
  PhiG (Qmap (parOf q.1)) (Nmap (parOf q.1)) (chainOp P) (fun s => q.2 • ξ s) z

/-- The residual on a finite chain, componentwise. -/
theorem PhiJ_apply (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) (q : (Fin 8 → ℝ) × ℝ)
    (z : S → Fin 3 → ℝ) (s : S) (i : Fin 3) :
    PhiJ P ξ q z s i = Qmap (parOf q.1) (q.2 • ξ s, z s) i +
      ∑ s', P s s' * Nmap (parOf q.1) (q.2 • ξ s', z s') i := rfl

/-- Woodford (2003), App. A.3: the residual is jointly `C^∞`. -/
theorem contDiff_PhiJ {n : WithTop ℕ∞} (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) :
    ContDiff ℝ n (fun w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) => PhiJ P ξ w.1 w.2) := by
  refine contDiff_pi.2 fun s => contDiff_pi.2 fun i => ?_
  have hQ : ContDiff ℝ n (fun w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) =>
      Qmap (parOf w.1.1) (w.1.2 • ξ s, w.2 s) i) := by
    have hg : ContDiff ℝ n (fun w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) =>
        (w.1.1, (w.1.2 • ξ s, w.2 s))) := by fun_prop
    exact (contDiff_apply ℝ ℝ i).comp (contDiff_Qj.comp hg)
  have hN : ∀ s', ContDiff ℝ n (fun w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) =>
      P s s' * Nmap (parOf w.1.1) (w.1.2 • ξ s', w.2 s') i) := fun s' => by
    have hg : ContDiff ℝ n (fun w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) =>
        (w.1.1, (w.1.2 • ξ s', w.2 s'))) := by fun_prop
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp (contDiff_Nj.comp hg))
  exact hQ.add (ContDiff.sum fun s' _ => hN s')

/-- Woodford (2003), App. A.3: the augmented map `(q, z) ↦ (q, Φ(q, z))`. -/
noncomputable def bigJ (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ)
    (w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ)) : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) :=
  (w.1, PhiJ P ξ w.1 w.2)

/-- The augmented map is `C^∞`. -/
theorem contDiff_bigJ {n : WithTop ℕ∞} (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) :
    ContDiff ℝ n (bigJ P ξ) :=
  contDiff_fst.prodMk (contDiff_PhiJ P ξ)

variable {p : Par}

/-- Woodford (2003), App. A.3: without disturbances the steady state solves the conditions for
EVERY parameter vector. -/
theorem PhiJ_zero {P : S → S → ℝ} (hP : Stochastic P) (ξ : S → Fin 3 → ℝ) (c : Fin 8 → ℝ) :
    PhiJ P ξ (c, 0) 0 = 0 := by
  funext s i
  have hc := congrFun (Mv_const (chainOp_isMarkov hP) (Nmap (parOf c) (0, 0)) s) i
  have h0 := congrFun (steadyState_zero (p := parOf c)) i
  simp only [PhiJ, PhiG, zero_smul, Pi.zero_apply, Pi.add_apply] at hc h0 ⊢
  rw [hc]; exact h0

/-- Woodford (2003), App. A.3: the derivative of the residual along `t ↦ (q₀, tv)` at the steady
state is the Rotemberg linearised operator. -/
theorem hasDerivAt_PhiJ_line (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) (v : S → Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => PhiJ P ξ (vecOf p, 0) (t • v)) (Lop p (chainOp P) v) 0 := by
  rw [hasDerivAt_pi]
  intro s
  rw [hasDerivAt_pi]
  intro i
  have hQ := hasDerivAt_Qmap_line (p := p) (v s) i
  have hN : ∀ s' ∈ (Finset.univ : Finset S), HasDerivAt
      (fun t : ℝ => P s s' * Nmap p (0, t • v s') i) (P s s' * DN0 p (v s') i) 0 :=
    fun s' _ => (hasDerivAt_Nmap_line (v s') i).const_mul (P s s')
  have h := hQ.add (HasDerivAt.sum hN)
  convert h using 1
  · funext t
    simp only [PhiJ_apply, parOf_vecOf, zero_smul, Pi.smul_apply, Pi.add_apply,
      Finset.sum_apply]
  · simp only [Lop, Mv, chainOp, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]

/-- The derivative of the residual along `t ↦ ((c₀, t), 0)`: `DQ_e ξ` (no lead term). -/
theorem hasDerivAt_PhiJ_eps (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => PhiJ P ξ (vecOf p, t) 0) (fun s => DQe p (ξ s)) 0 := by
  rw [hasDerivAt_pi]
  intro s
  rw [hasDerivAt_pi]
  intro i
  have hQ := hasDerivAt_Qmap_eps (p := p) (ξ s) i
  have hN : HasDerivAt (fun t : ℝ => ∑ s', P s s' * Nmap p (t • ξ s', 0) i) 0 0 := by
    have : (fun t : ℝ => ∑ s', P s s' * Nmap p (t • ξ s', 0) i) =
        fun _ => ∑ s', P s s' * Nmap p (0, 0) i := by
      funext t; simp [Nmap]
    rw [this]; exact hasDerivAt_const _ _
  have h := hQ.add hN
  convert h using 1
  · funext t
    simp only [PhiJ_apply, parOf_vecOf, Pi.zero_apply, Pi.add_apply]
  · simp

/-- Woodford (2003), App. A.3: the partial derivative of the residual in the policy at the steady
state is `L`. -/
theorem fderiv_PhiJ_inr (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) (v : S → Fin 3 → ℝ) :
    fderiv ℝ (fun w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) => PhiJ P ξ w.1 w.2)
      ((vecOf p, 0), 0) (0, v) = Lop p (chainOp P) v := by
  have hd := ((contDiff_PhiJ (n := 1) P ξ).differentiable one_ne_zero
    ((vecOf p, (0 : ℝ)), (0 : S → Fin 3 → ℝ))).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => (((vecOf p, (0 : ℝ))), t • v))
      ((0 : (Fin 8 → ℝ) × ℝ), v) 0 := by
    have := (hasDerivAt_const (0 : ℝ) ((vecOf p, (0 : ℝ)))).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_PhiJ_line P ξ v)

/-- Woodford (2003), App. A.3: the partial derivative of the residual in the amplitude at the
steady state is `DQ_e ξ`. -/
theorem fderiv_PhiJ_eps (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) :
    fderiv ℝ (fun w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) => PhiJ P ξ w.1 w.2)
      ((vecOf p, 0), 0) ((0, 1), 0) = fun s => DQe p (ξ s) := by
  have hd := ((contDiff_PhiJ (n := 1) P ξ).differentiable one_ne_zero
    ((vecOf p, (0 : ℝ)), (0 : S → Fin 3 → ℝ))).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((vecOf p, t), (0 : S → Fin 3 → ℝ)))
      (((0 : Fin 8 → ℝ), (1 : ℝ)), (0 : S → Fin 3 → ℝ)) 0 := by
    have := ((hasDerivAt_const (0 : ℝ) (vecOf p)).prodMk (hasDerivAt_id (0 : ℝ))).prodMk
      (hasDerivAt_const (0 : ℝ) (0 : S → Fin 3 → ℝ))
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_PhiJ_eps P ξ)

/-- Woodford (2003), App. A.3 and Proposition 4.3: under the Taylor principle the derivative of
the augmented map at the steady state is injective. -/
theorem fderiv_bigJ_injective (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 3 → ℝ) : Function.Injective (fderiv ℝ (bigJ P ξ) ((vecOf p, 0), 0)) := by
  have hd0 := ((contDiff_PhiJ (n := 1) P ξ).differentiable one_ne_zero
    ((vecOf p, (0 : ℝ)), (0 : S → Fin 3 → ℝ))).hasFDerivAt
  have hd : HasFDerivAt (bigJ P ξ)
      ((ContinuousLinearMap.fst ℝ ((Fin 8 → ℝ) × ℝ) (S → Fin 3 → ℝ)).prod
        (fderiv ℝ (fun w : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) => PhiJ P ξ w.1 w.2)
          ((vecOf p, 0), 0))) ((vecOf p, 0), 0) := hasFDerivAt_fst.prodMk hd0
  rw [hd.fderiv, injective_iff_map_eq_zero]
  rintro ⟨τ, v⟩ hq
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    Prod.mk_eq_zero] at hq
  obtain ⟨hτ, hv⟩ := hq
  subst hτ
  rw [fderiv_PhiJ_inr] at hv
  have := Lop_injective hp (chainOp_isMarkov hP) (V := ‖v‖) (fun s => norm_le_pi_norm v s) hv
  rw [this]
  rfl

/-- The derivative of the augmented map at the steady state as a linear equivalence. -/
noncomputable def derivEquivJ (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 3 → ℝ) :
    (((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ)) ≃L[ℝ] (((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ)) :=
  (LinearEquiv.ofInjectiveEndo (fderiv ℝ (bigJ P ξ) ((vecOf p, 0), 0) :
    (((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ)) →ₗ[ℝ] (((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ)))
    (fderiv_bigJ_injective hp hP ξ)).toContinuousLinearEquiv

/-- Woodford (2003), App. A.3: the augmented map has the invertible derivative `derivEquivJ`. -/
theorem hasFDerivAt_bigJ (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 3 → ℝ) :
    HasFDerivAt (bigJ P ξ) (derivEquivJ hp hP ξ :
      (((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ)) →L[ℝ] _) ((vecOf p, 0), 0) := by
  have hd : HasFDerivAt (bigJ P ξ) (fderiv ℝ (bigJ P ξ) ((vecOf p, 0), 0)) ((vecOf p, 0), 0) :=
    ((contDiff_bigJ (n := 1) P ξ).differentiable one_ne_zero _).hasFDerivAt
  convert hd using 1
  exact ContinuousLinearMap.ext fun q => rfl

/-- Woodford (2003), Ch. 6, §1 and App. A.3, Rotemberg pricing (**THE MARKOV EQUILIBRIUM IS
`C^∞` IN THE SHOCK SCALE AND THE PARAMETERS**). For a finite Markov chain `(S, P)`, a disturbance
pattern `ξ` and parameters `p` satisfying the Taylor principle, there are `r > 0`, a
neighbourhood `U` of `(c₀, 0)` (`c₀ = vecOf p`) and a map `g` with
* `g(c₀, 0) = 0` (the steady state is the base point);
* `g` is `C^∞` at `(c₀, 0)` (jointly in the eight parameters and the shock scale);
* for `(c, ε) ∈ U`, `g(c, ε)` is a Markov equilibrium of the economy with parameters `c` and
  disturbances `εξ`, with `‖g(c, ε)‖ < r`;
* it is the ONLY Markov equilibrium in the ball `‖z‖ < r`, for each `(c, ε) ∈ U`. -/
theorem markov_equilibrium_smooth (hp : p.Std) {P : S → S → ℝ} (hP : Stochastic P)
    (ξ : S → Fin 3 → ℝ) :
    ∃ r > 0, ∃ U ∈ 𝓝 (vecOf p, (0 : ℝ)), ∃ g : (Fin 8 → ℝ) × ℝ → S → Fin 3 → ℝ,
      g (vecOf p, 0) = 0 ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (vecOf p, 0) ∧
      (∀ q ∈ U, PhiJ P ξ q (g q) = 0 ∧ ‖g q‖ < r) ∧
      ∀ q ∈ U, ∀ w, ‖w‖ < r → PhiJ P ξ q w = 0 → w = g q := by
  set f := bigJ P ξ with hfdef
  set w0 : ((Fin 8 → ℝ) × ℝ) × (S → Fin 3 → ℝ) := ((vecOf p, 0), 0) with hw0
  have hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f w0 := (contDiff_bigJ P ξ).contDiffAt
  have hf' := hasFDerivAt_bigJ hp hP ξ
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
  set φh := hf.toOpenPartialHomeomorph f hf' hn with hφh
  have h00 : f w0 = w0 := by
    simp only [hfdef, bigJ, hw0]
    rw [PhiJ_zero hP ξ (vecOf p)]
  have hsrc : w0 ∈ φh.source := hf.mem_toOpenPartialHomeomorph_source hf' hn
  have htgt : w0 ∈ φh.target := by
    have := hf.image_mem_toOpenPartialHomeomorph_target hf' hn
    rwa [h00] at this
  have hcoe : (φh : _ → _) = f := rfl
  have hsymm0 : φh.symm w0 = w0 := by
    have := φh.left_inv hsrc
    rwa [hcoe, h00] at this
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 φh.open_source w0 hsrc
  have hline : Continuous fun q : (Fin 8 → ℝ) × ℝ => (q, (0 : S → Fin 3 → ℝ)) :=
    continuous_id.prodMk continuous_const
  have hev1 : ∀ᶠ q in 𝓝 (vecOf p, (0 : ℝ)), (q, (0 : S → Fin 3 → ℝ)) ∈ φh.target :=
    hline.continuousAt.preimage_mem_nhds (φh.open_target.mem_nhds htgt)
  have hcont : ContinuousAt (fun q : (Fin 8 → ℝ) × ℝ => φh.symm (q, 0)) (vecOf p, 0) := by
    have h1 : ContinuousAt φh.symm ((fun q : (Fin 8 → ℝ) × ℝ => (q, (0 : S → Fin 3 → ℝ)))
        (vecOf p, 0)) := φh.continuousAt_symm htgt
    exact ContinuousAt.comp (f := fun q : (Fin 8 → ℝ) × ℝ => (q, (0 : S → Fin 3 → ℝ))) h1
      hline.continuousAt
  have hev2 : ∀ᶠ q in 𝓝 (vecOf p, (0 : ℝ)), φh.symm (q, 0) ∈ Metric.ball w0 r := by
    have := hcont.tendsto
    rw [show ((vecOf p, (0 : ℝ)), (0 : S → Fin 3 → ℝ)) = w0 from rfl, hsymm0] at this
    exact this (Metric.ball_mem_nhds _ hr)
  have hev3 : ∀ᶠ q in 𝓝 (vecOf p, (0 : ℝ)), q ∈ Metric.ball (vecOf p, (0 : ℝ)) r :=
    Metric.ball_mem_nhds _ hr
  refine ⟨r, hr, {q | (q, (0 : S → Fin 3 → ℝ)) ∈ φh.target ∧ φh.symm (q, 0) ∈ Metric.ball w0 r ∧
    q ∈ Metric.ball (vecOf p, (0 : ℝ)) r}, hev1.and (hev2.and hev3),
    fun q => (φh.symm (q, 0)).2, ?_, ?_, ?_, ?_⟩
  · change (φh.symm w0).2 = 0
    rw [hsymm0]
  · have hloc := hf.to_localInverse hf' hn
    rw [h00] at hloc
    have hl2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (Fin 8 → ℝ) × ℝ => (q, (0 : S → Fin 3 → ℝ))) (vecOf p, 0) := by fun_prop
    have hcomp := hloc.comp (vecOf p, (0 : ℝ)) hl2
    exact contDiffAt_snd.comp _ hcomp
  · rintro q ⟨ht, hb, -⟩
    have hri := φh.right_inv ht
    rw [hcoe] at hri
    set qq := φh.symm (q, 0) with hqq
    have h1 : qq.1 = q := congrArg Prod.fst hri
    have h2 : PhiJ P ξ qq.1 qq.2 = 0 := congrArg Prod.snd hri
    refine ⟨?_, ?_⟩
    · change PhiJ P ξ q qq.2 = 0
      rw [← h1]; exact h2
    · rw [Metric.mem_ball, hw0] at hb
      have hb' : dist qq.2 0 < r := lt_of_le_of_lt (by
        rw [Prod.dist_eq]; exact le_max_right _ _) hb
      rwa [dist_zero_right] at hb'
  · rintro q ⟨ht, -, hq⟩ w hw heq
    have hin : (q, w) ∈ φh.source := hball (by
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, hw0]
      exact ⟨hq, by rwa [dist_zero_right]⟩)
    have hqt := φh.map_target ht
    have hfw : φh (q, w) = (q, 0) := by
      rw [hcoe]
      simp only [hfdef, bigJ]
      rw [heq]
    have hfq : φh (φh.symm (q, 0)) = (q, 0) := φh.right_inv ht
    have := φh.injOn hin hqt (hfw.trans hfq.symm)
    exact congrArg Prod.snd this

/-- Woodford (2003), Ch. 6, §1 (**`Cᵏ` on a neighbourhood, for every `k`**): a map `C^∞` at a
point is `Cᵏ` at every point of a neighbourhood, for each finite `k`. -/
theorem smooth_Ck {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → F} {q0 : E} (hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g q0)
    (k : ℕ) : ∀ᶠ q in 𝓝 q0, ContDiffAt ℝ k g q :=
  (hg.of_le (by exact_mod_cast le_top)).eventually (by simp)

/-! ## The first-order solution -/

/-- Woodford (2003), App. A.3 (**the first-order solution solves the linearised Markov model**):
if `ε ↦ z_ε` is a family of Markov equilibria at the parameters `p` with `z₀ = 0` and derivative
`z₁` at `0`, then `L z₁ + DQ_e ξ = 0`. -/
theorem firstOrder (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) {z : ℝ → S → Fin 3 → ℝ}
    {z1 : S → Fin 3 → ℝ} (hz0 : z 0 = 0) (hz : HasDerivAt z z1 0)
    (heq : ∀ᶠ ε in 𝓝 0, PhiJ P ξ (vecOf p, ε) (z ε) = 0) :
    Lop p (chainOp P) z1 + (fun s => DQe p (ξ s)) = 0 := by
  have hd := ((contDiff_PhiJ (n := 1) P ξ).differentiable one_ne_zero
    ((vecOf p, (0 : ℝ)), (0 : S → Fin 3 → ℝ))).hasFDerivAt
  have hl : HasDerivAt (fun ε : ℝ => ((vecOf p, ε), z ε)) (((0 : Fin 8 → ℝ), (1 : ℝ)), z1) 0 := by
    have := ((hasDerivAt_const (0 : ℝ) (vecOf p)).prodMk (hasDerivAt_id (0 : ℝ))).prodMk hz
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp [hz0])
  have h0 : HasDerivAt (fun ε => PhiJ P ξ (vecOf p, ε) (z ε)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : S → Fin 3 → ℝ)).congr_of_eventuallyEq
      (heq.mono fun ε hε => hε)
  have hu := hc.unique h0
  have hsplit : (((0 : Fin 8 → ℝ), (1 : ℝ)), z1) =
      (((0 : Fin 8 → ℝ), (1 : ℝ)), (0 : S → Fin 3 → ℝ)) + (((0 : Fin 8 → ℝ), (0 : ℝ)), z1) := by
    simp
  rw [hsplit, map_add, fderiv_PhiJ_eps] at hu
  have h00 : ((0 : Fin 8 → ℝ), (0 : ℝ)) = 0 := rfl
  rw [h00, fderiv_PhiJ_inr] at hu
  rw [add_comm]; exact hu

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) and Ch. 3, fn. 44 (**the first-order solution in
equations**): `(ŷ₁, π₁, ĉ₁)` satisfies, state by state, with `P` the transition operator,
* `ĉ₁ = ŷ₁`;
* the IS curve with the rule: `(σ + φ_y)ŷ₁ + φ_π π₁ − σPŷ₁ − Pπ₁ + ν = 0`;
* the NKPC with the Rotemberg slope: `π₁ = κ(ŷ₁ − ŷⁿ) + βPπ₁` with the natural rate
  `ŷⁿ = ((1+ω)a − μ)/(σ + ω)`. -/
theorem firstOrder_eqs (hp : p.Basic) (P : S → S → ℝ) (ξ : S → Fin 3 → ℝ) {z1 : S → Fin 3 → ℝ}
    (h : Lop p (chainOp P) z1 + (fun s => DQe p (ξ s)) = 0) (s : S) :
    z1 s 2 = z1 s 0 ∧
    (p.σ + p.φy) * z1 s 0 + p.φ * z1 s 1 - p.σ * chainOp P (fun s' => z1 s' 0) s -
        chainOp P (fun s' => z1 s' 1) s + ξ s 0 = 0 ∧
    z1 s 1 = p.κ * (z1 s 0 - ((1 + p.ω) * ξ s 1 - ξ s 2) / (p.σ + p.ω)) +
        p.β * chainOp P (fun s' => z1 s' 1) s := by
  have e : ∀ s i, Lop p (chainOp P) z1 s i + DQe p (ξ s) i = 0 := fun s i => by
    have := congrFun (congrFun h s) i
    simpa using this
  have e2 : ∀ s, z1 s 2 = z1 s 0 := fun s => by
    have h2 := e s 2
    rw [(Lop_apply (p := p) (chainOp P) z1 s).2.2] at h2
    simp [DQe] at h2
    linarith
  have hfun : (fun s' => z1 s' 2) = fun s' => z1 s' 0 := funext e2
  obtain ⟨l0, l1, -⟩ := Lop_apply (p := p) (chainOp P) z1 s
  have h0 := e s 0
  have h1 := e s 1
  rw [l0, hfun, e2 s] at h0
  rw [l1, e2 s] at h1
  simp only [DQe, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  refine ⟨e2 s, by linarith, ?_⟩
  have hψ := hp.ψ_pos
  have hωσ : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hk := hp.κ_mul
  have key : p.ψ * (z1 s 1 - p.κ * (z1 s 0 - ((1 + p.ω) * ξ s 1 - ξ s 2) / (p.σ + p.ω)) -
      p.β * chainOp P (fun s' => z1 s' 1) s) = 0 := by
    have e3 : p.ψ * p.κ * (((1 + p.ω) * ξ s 1 - ξ s 2) / (p.σ + p.ω)) =
        p.θ * p.m * ((1 + p.ω) * ξ s 1 - ξ s 2) := by
      rw [mul_comm p.ψ p.κ, hk]; field_simp
    linear_combination h1 - z1 s 0 * hk + e3
  have := (mul_eq_zero.1 key).resolve_left hψ.ne'
  linarith

/-- Woodford (2003), Ch. 6, §1 and App. A.3 (**the derivative of the smooth policy in the shock
scale solves the linearised model**): for `g` of `markov_equilibrium_smooth`,
`z₁ = ∂g/∂ε(c₀, 0)` satisfies `L z₁ + DQ_e ξ = 0`, i.e. `firstOrder_eqs`. -/
theorem first_order_of_smooth {P : S → S → ℝ} (ξ : S → Fin 3 → ℝ)
    {g : (Fin 8 → ℝ) × ℝ → S → Fin 3 → ℝ} {U : Set ((Fin 8 → ℝ) × ℝ)}
    (hU : U ∈ 𝓝 (vecOf p, (0 : ℝ))) (hg0 : g (vecOf p, 0) = 0)
    (hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (vecOf p, 0))
    (hgE : ∀ q ∈ U, PhiJ P ξ q (g q) = 0) :
    Lop p (chainOp P) (fderiv ℝ g (vecOf p, 0) (0, 1)) + (fun s => DQe p (ξ s)) = 0 := by
  have hdg := (hg.differentiableAt (by simp)).hasFDerivAt
  have hl : HasDerivAt (fun ε : ℝ => (vecOf p, ε)) ((0 : Fin 8 → ℝ), (1 : ℝ)) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (vecOf p)).prodMk (hasDerivAt_id (0 : ℝ))
    simpa using this
  have hc := hdg.comp_hasDerivAt_of_eq (0 : ℝ) hl rfl
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), (vecOf p, ε) ∈ U := by
    have hcont : Continuous fun ε : ℝ => (vecOf p, ε) := continuous_const.prodMk continuous_id
    exact hcont.continuousAt.preimage_mem_nhds hU
  exact firstOrder P ξ (z := fun ε => g (vecOf p, ε)) hg0 hc (hev.mono fun ε hε => hgE _ hε)

/-! ## The Taylor principle is necessary for invertibility on finite chains -/

/-- Woodford (2003), Proposition 4.3: the determinant of the IS–AS block, `σβ/(σ + φ_y + φ_πκ)`. -/
theorem det2_Arot : det2 (Arot p) = p.σ * p.β / p.dd := by
  have h : p.dd = p.σ + p.φy + p.φ * p.κ := rfl
  simp only [det2, Arot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  by_cases hd : p.dd = 0
  · simp [hd]
  · field_simp
    rw [h]
    ring

/-- Woodford (2003), Proposition 4.3: the trace of the IS–AS block. -/
theorem tr2_Arot : tr2 (Arot p) = (p.σ + p.κ + p.β * (p.σ + p.φy)) / p.dd := by
  simp only [tr2, Arot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  ring

/-- Woodford (2003), Proposition 4.3, Rotemberg slope (**an explicit root `μ ≥ 1` when the Taylor
principle fails**): if `κ(φ_π − 1) + (1 − β)φ_y ≤ 0`, then `A` has a real eigenvalue
`μ = (T + √(T² − 4D))/2 ≥ 1` with eigenvector `(μ − A₁₁, A₁₀)`, `A₁₀ = κσ/dd > 0`. -/
theorem big_root (hp : p.Basic) (hT : p.κ * (p.φ - 1) + (1 - p.β) * p.φy ≤ 0) :
    ∃ μ, 1 ≤ μ ∧ (Arot p).mulVec ![μ - Arot p 1 1, Arot p 1 0] =
      μ • ![μ - Arot p 1 1, Arot p 1 0] ∧ 0 < Arot p 1 0 := by
  have hd := hp.dd_pos
  set T := tr2 (Arot p) with hTdef
  set D := det2 (Arot p) with hDdef
  have hD0 : 0 < D := by rw [hDdef, det2_Arot]; exact div_pos (mul_pos hp.σ_pos hp.β_pos) hd
  have hTD : 1 + D ≤ T := by
    rw [hTdef, hDdef, tr2_Arot, det2_Arot, ← sub_nonneg]
    have : (p.σ + p.κ + p.β * (p.σ + p.φy)) / p.dd - (1 + p.σ * p.β / p.dd) =
        -(p.κ * (p.φ - 1) + (1 - p.β) * p.φy) / p.dd := by
      field_simp; unfold Par.dd; ring
    rw [this]; exact div_nonneg (by linarith) hd.le
  have hT0 : 0 ≤ T := by linarith
  have hdisc : 0 ≤ T ^ 2 - 4 * D := by
    nlinarith [mul_le_mul hTD hTD (by linarith) hT0, sq_nonneg (1 - D)]
  set sq := Real.sqrt (T ^ 2 - 4 * D) with hsq
  have hsq2 : sq ^ 2 = T ^ 2 - 4 * D := Real.sq_sqrt hdisc
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  set μ := (T + sq) / 2 with hμ
  have hchar : μ ^ 2 - T * μ + D = 0 := by rw [hμ]; nlinarith
  have hμ1 : 1 ≤ μ := by
    rw [hμ]
    by_cases h2 : 2 ≤ T
    · linarith
    · have h3 : (2 - T) ^ 2 ≤ sq ^ 2 := by rw [hsq2]; nlinarith
      have h4 : 2 - T ≤ sq := by nlinarith
      linarith
  have hA10 : 0 < Arot p 1 0 := by
    simp only [Arot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
    exact div_pos (mul_pos hp.κ_pos hp.σ_pos) hd
  refine ⟨μ, hμ1, ?_, hA10⟩
  have hT' : T = Arot p 0 0 + Arot p 1 1 := rfl
  have hD' : D = Arot p 0 0 * Arot p 1 1 - Arot p 0 1 * Arot p 1 0 := rfl
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.zero_eta, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    rw [hT', hD'] at hchar
    linear_combination -hchar
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    ring

/-- Woodford (2003), Proposition 4.3, Rotemberg slope (**the Taylor principle is EXACTLY the
condition for the linearised operator to be injective on every finite Markov chain**). If it
fails, the two-state chain with transition `[[(1+λ)/2, (1−λ)/2], [(1−λ)/2, (1+λ)/2]]`,
`λ = 1/μ` (`μ ≥ 1` of `big_root`), carries the nonzero kernel element
`v(s) = ±(μ − A₁₁, A₁₀, μ − A₁₁)`. -/
theorem lop_injective_iff (hp : p.Basic) :
    (∀ (S : Type) [Fintype S] (P : S → S → ℝ), Stochastic P → ∀ v : S → Fin 3 → ℝ,
      Lop p (chainOp P) v = 0 → v = 0) ↔ 0 < p.κ * (p.φ - 1) + (1 - p.β) * p.φy := by
  constructor
  · intro h
    by_contra hT
    push Not at hT
    obtain ⟨μ, hμ1, hAw, hA10⟩ := big_root hp hT
    set w : Fin 2 → ℝ := ![μ - Arot p 1 1, Arot p 1 0] with hw
    set l := 1 / μ with hl
    have hμ0 : 0 < μ := by linarith
    have hl0 : 0 < l := by positivity
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hμ0]; exact hμ1
    have hlμ : l * μ = 1 := by rw [hl]; field_simp
    set P : Fin 2 → Fin 2 → ℝ := fun s s' => if s = s' then (1 + l) / 2 else (1 - l) / 2
      with hP
    have hPs : Stochastic P := by
      refine ⟨fun s s' => ?_, fun s => ?_⟩
      · simp only [hP]; split_ifs <;> linarith
      · fin_cases s <;> simp [hP, Fin.sum_univ_two] <;> ring
    set hs : Fin 2 → ℝ := fun s => if s = 0 then 1 else -1 with hhs
    set u : Fin 2 → Fin 2 → ℝ := fun s => hs s • w with hu
    have hMu : ∀ s, Mv (chainOp P) u s = l • u s := fun s => by
      funext i
      simp only [Mv, chainOp, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_two, hu, hhs, hP,
        Pi.smul_apply, smul_eq_mul]
      fin_cases s <;> simp <;> ring
    have hrec : ∀ s, u s = (Arot p).mulVec (Mv (chainOp P) u s) +
        bR p (fun _ : Fin 2 => (0 : Fin 3 → ℝ)) s := fun s => by
      have hb0 : bR p (fun _ : Fin 2 => (0 : Fin 3 → ℝ)) s = 0 := by
        funext i; fin_cases i <;> simp [bR, gR0, gR1]
      rw [hb0, add_zero, hMu, Matrix.mulVec_smul, hu, Matrix.mulVec_smul, hAw, smul_smul,
        smul_smul]
      change hs s • w = (l * hs s * μ) • w
      rw [mul_comm l, mul_assoc, hlμ, mul_one]
    have hL := Lop_block hp (chainOp P) (fun _ => 0) u hrec
    have hv := h (Fin 2) P hPs _ hL
    have h0 : u 0 1 = 0 := congrFun (congrFun hv 0) 1
    have h1 : u 0 1 = Arot p 1 0 := by simp [hu, hhs, hw]
    rw [h1] at h0
    exact hA10.ne' h0
  · intro hT S _ P hP v hv
    exact Lop_injective ⟨hp, hT⟩ (chainOp_isMarkov hP) (V := ‖v‖)
      (fun s => norm_le_pi_norm v s) hv

end Woodford.StabilizationWelfare.NonlinearRotembergSmooth
