/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaSplit
import OptimalPolicyRules.InertiaProp810

/-!
# The general target criterion (1.23) of the inertia model is Rule I or Rule II

Woodford (2003), *Interest and Prices*, Chapter 8, §1.4 (pp. 553–556) and §3.2 (pp. 592–598),
App. G.7, pp. 727–730.

For the representation of Proposition 8.1 built from a deflating split of the inertia model
(`InertiaSplit.inSplit`, the real root `λₛ` of `λ² − Sλ + P₂₃` solved forward), the general target
criterion (1.23), `α(L)λᵢ(i_t − i*) + B₂'B(L)q_t = 0` with `q = Q(L⁻¹)T̃'W(τ − τ*)`, is computed
explicitly: it is Rule I (`λₛ = λ₃`) or Rule II (`λₛ = λ₂`).

## Main results

* `Bc_fin_two`, `in_Kinv`, `dot_two`: the coefficient matrices of `B(L) = adj(I − ΛL)`, `K⁻¹`.
* `Fw_rec`: the forward solution `F` of the split obeys `F_t = λₛ⁻¹E_tF_{t+1} + β[(μ − γ)q̂_t +
  (σμ²/(1 − μ))g_t]` (`q̂ = π − γZ`, `g = λₓ(x − x*)`, `μ = (βλₛ)⁻¹`).
* `Qop_eq`: `q_t = −(μ/γ)(q̂_t + a_t + d g_t, κ(q̂_t + a_t) + e g_t)`, `a_t = E_tF_{t+1}`.
* `crit_eq`: the criterion equals `λᵢα(L)(i_t − i*) − (σμ/γ)[κ(q̂_t + a_t) + e g_t − g_{t−1}]`.
* `W_eq_fwd`, `fplan_eq_fhat`: `(σ/λᵢ)[κ(q̂_t + a_t) + e g_t − g_{t−1}] = ∑_j λₛ^{−j}E_tf̂_{t+j}`
  (uniqueness of the bounded forward solution; the step is (1.15) at `μ`).
* `crit_rule`: **the criterion is `λᵢ[(1 − λ₁L)(1 − λ_bL)(i_t − i*) −
  (βγλₛ)⁻¹∑λₛ^{−j}E_tf̂_{t+j}]`** at every `t ≥ 1` along bounded adapted plans with
  `Z_{t+1} = π_t`.
* `crit_iff_ruleI`, `crit_iff_ruleII`: the general criterion holds from `T ≥ 2` on iff Rule I
  (3.22) (resp. Rule II (3.23)) does.
-/

namespace Woodford.OptimalPolicyRules.InertiaCriterion

open Matrix Polynomial GeneralSetup Adjugate PencilSplit
open IRuleBasic (Calib)
open CubicRoots
open GeneralLinksInertia (inSys inProblem in_det_ne in_xvec Zof)
open GeneralLinks (piOf xOf iOf)
open InertiaSplit (pR inJ inPsi quadQ inSplit mu_facts standing_of)
open InflationInertiaRepresentations (geomKer)
open TargetCriterion.Prop81 (xproc)
open GeneralFOC.LQ (Mpart)

variable (c : Calib) (γ : ℝ)

/-- Woodford (2003), p. 553 (tool): the coefficient matrices of `B(L) = adj(I − ΛL)` for a
`2 × 2` matrix: `B₀ = I`, `B₁ = [−Λ₁₁ Λ₀₁; Λ₁₀ −Λ₀₀]`, `B₂ = 0`. -/
theorem Bc_fin_two (Λ : Matrix (Fin 2) (Fin 2) ℝ) :
    TargetCriterion.Lag.Bc (Bpoly Λ) 0 = 1 ∧
      TargetCriterion.Lag.Bc (Bpoly Λ) 1 = !![-Λ 1 1, Λ 0 1; Λ 1 0, -Λ 0 0] ∧
      TargetCriterion.Lag.Bc (Bpoly Λ) 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [TargetCriterion.Lag.Bc, Bpoly, adjugate_fin_two, lagMat, coeff_one, coeff_X, coeff_C]

/-- Woodford (2003), (1.23), p. 554 (tool): `(0, σ)·(v + [a b; c d] w) = σ(v₁ + c w₀ + d w₁)`. -/
theorem dot_two (σ a b d e : ℝ) (v w : Fin 2 → ℝ) :
    ![0, σ] ⬝ᵥ (v + !![a, b; d, e] *ᵥ w) = σ * (v 1 + (d * w 0 + e * w 1)) := by
  simp [dotProduct, Fin.sum_univ_two]

/-- Woodford (2003), eq. (1.20), p. 553: `K⁻¹ = (μ/γ)[1 d; κ e]` for the inertia model, with
`d = σμ + σμ²/(1 − μ)` and `e = 1 + βγ − βμ`. -/
theorem in_Kinv (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) {μ : ℝ} (hp : pR c γ μ = 0)
    (h1 : 1 - μ ≠ 0) (h0 : μ ≠ 0) :
    (Kmat (inSys c γ hσ hd) (inJ c μ))⁻¹ = (μ / γ) •
      !![1, c.σ * μ + c.σ * μ ^ 2 / (1 - μ); c.κ, 1 + c.β * γ - c.β * μ] := by
  rw [inv_def, InertiaSplit.in_Kdet c γ hσ hd hp h1 h0, InertiaSplit.in_Kmat, adjugate_fin_two_of,
    Ring.inverse_eq_inv', inv_div, neg_neg, neg_neg]

/-- Woodford (2003), App. G.1 and (1.21), p. 553, for the inertia model: the forward solution
`F_t = ∑ (βμ)ᵏ E_t βJ'x_{t+k}` of the split solving `λₛ` forward (`βμ = λₛ⁻¹`) obeys
`F_t = βμ E_tF_{t+1} + β[(μ − γ)(π_t − γZ_t) + (σμ²/(1 − μ))λₓ(x_t − x*)]`. -/
theorem Fw_rec {Ω : Type*} (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) (𝔼 : ExpectationSystem Ω)
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} (hyb : BoundedV y) (hya : AdaptedV 𝔼 y)
    (t : ℕ) (ω : Ω) :
    Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq) (xproc (inProblem c γ hc hγ0.le) y) t ω () =
      c.β * (c.β * ls)⁻¹ * 𝔼.E t (fun ω' => Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
        (xproc (inProblem c γ hc hγ0.le) y) (t + 1) ω' ()) ω +
      c.β * (((c.β * ls)⁻¹ - γ) * (piOf y t ω - γ * Zof y t ω) +
        c.σ * (c.β * ls)⁻¹ ^ 2 / (1 - (c.β * ls)⁻¹) * (c.lx * (xOf y t ω - c.xstar))) := by
  have hxb : BoundedV (xproc (inProblem c γ hc hγ0.le) y) :=
    TargetCriterion.Prop81.boundedV_xproc (P := inProblem c γ hc hγ0.le) hyb
  obtain ⟨hrec, -, -⟩ := fwdSum_spec 𝔼 ((inSplit c γ hc hγ0 hγ1 hq).powDecay_G hc.1)
    (boundedV_mulVec (c.β • (inSplit c γ hc hγ0 hγ1 hq).Jᵀ) hxb)
  have hknown : KnownV 𝔼 t (fun ω' => (c.β • (inSplit c γ hc hγ0 hγ1 hq).Jᵀ) *ᵥ
      xproc (inProblem c γ hc hγ0.le) y t ω') :=
    PencilSplit.knownV_mulVec 𝔼 _ (Prop81General.adaptedV_xproc _ hya t)
  have hF : ∀ s ω', Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
      (xproc (inProblem c γ hc hγ0.le) y) s ω' = fwdSum 𝔼 (c.β • (inSplit c γ hc hγ0 hγ1 hq).Ψᵀ)
        (fun t ω => (c.β • (inSplit c γ hc hγ0 hγ1 hq).Jᵀ) *ᵥ
          xproc (inProblem c γ hc hγ0.le) y t ω) s ω' := fun _ _ => rfl
  simp only [hF]
  rw [congrFun (hrec t ω) (), EV_of_known 𝔼 hknown]
  have hx : xproc (inProblem c γ hc hγ0.le) y t ω = _ := in_xvec c γ hc hγ0.le (y t ω)
  beta_reduce
  rw [hx]
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, inSplit, inPsi, inJ, EV,
    Zof, piOf, xOf]
  ring

/-- Woodford (2003), eq. (1.20), p. 553, for the inertia model: the forcing of the multiplier
recursion is `q_t = −K⁻¹(E_t x^z_t + A₁₂'E_tF_{t+1}) = −(μ/γ)(q̂_t + a_t + d g_t,
κ(q̂_t + a_t) + e g_t)` with `q̂ = π − γZ`, `g = λₓ(x − x*)`, `a_t = E_tF_{t+1}`. -/
theorem Qop_eq {Ω : Type*} (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) (𝔼 : ExpectationSystem Ω)
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} (hya : AdaptedV 𝔼 y) (t : ℕ) (ω : Ω) :
    Prop81General.Qop 𝔼 (inSplit c γ hc hγ0 hγ1 hq) (xproc (inProblem c γ hc hγ0.le) y) t ω =
      -(((c.β * ls)⁻¹ / γ) • ![(piOf y t ω - γ * Zof y t ω) +
          𝔼.E t (fun ω' => Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
            (xproc (inProblem c γ hc hγ0.le) y) (t + 1) ω' ()) ω +
          (c.σ * (c.β * ls)⁻¹ + c.σ * (c.β * ls)⁻¹ ^ 2 / (1 - (c.β * ls)⁻¹)) *
            (c.lx * (xOf y t ω - c.xstar)),
        c.κ * ((piOf y t ω - γ * Zof y t ω) +
          𝔼.E t (fun ω' => Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
            (xproc (inProblem c γ hc hγ0.le) y) (t + 1) ω' ()) ω) +
          (1 + c.β * γ - c.β * (c.β * ls)⁻¹) * (c.lx * (xOf y t ω - c.xstar))]) := by
  obtain ⟨hp, h1, h0, -⟩ := mu_facts c γ (standing_of c γ hc hγ0 hγ1) hq
  have hxa := Prop81General.adaptedV_xproc (inProblem c γ hc hγ0.le) hya t
  have hknown : KnownV 𝔼 t (fun ω' => Mpart (xproc (inProblem c γ hc hγ0.le) y t ω')) :=
    fun r => hxa (Sum.inr r)
  have hKinv := in_Kinv c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hp h1 h0
  unfold Prop81General.Qop Prop81General.Rop
  rw [EV_of_known 𝔼 hknown]
  change -((Kmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) (inJ c (c.β * ls)⁻¹))⁻¹ *ᵥ
    _) = _
  rw [hKinv, show J1 (inSplit c γ hc hγ0 hγ1 hq).J = 1 from InertiaSplit.in_J1 c _,
    transpose_one, inv_one]
  have hx : xproc (inProblem c γ hc hγ0.le) y t ω = _ := in_xvec c γ hc hγ0.le (y t ω)
  beta_reduce
  rw [hx]
  funext r
  fin_cases r <;>
    simp [mulVec, dotProduct, Fin.sum_univ_two, Mpart, EV, inProblem, inSys, Zof, piOf, xOf] <;>
    ring

/-- **Woodford (2003), (1.23) and (1.28), pp. 554–556, for the inertia model.** For the
representation of Proposition 8.1 built from the split solving `λₛ` forward (`μ = (βλₛ)⁻¹`,
`λ_b = S − λₛ`), the general target criterion with `v = λᵢ(i − i*)` and `q = Q(L⁻¹)T̃'W(τ − τ*)` is
`λᵢ(1 − λ₁L)(1 − λ_bL)(i_t − i*) − (σμ/γ)[κ(q̂_t + a_t) + e g_t − g_{t−1}]`,
`q̂ = π − γZ`, `g = λₓ(x − x*)`, `a_t = E_tF_{t+1}`, `e = 1 + βγ − βμ`. -/
theorem crit_eq {Ω : Type*} (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} (hya : AdaptedV 𝔼 y) (t : ℕ) (ω : Ω) :
    TargetCriterion.Crit.crit
        (alpha (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Λ)
        (Bpoly (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Λ) 2
        (inProblem c γ hc hγ0.le).sys.B2 (fun s ω => c.li * (iOf y s ω - c.istar))
        ((Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Qop
          (xproc (inProblem c γ hc hγ0.le) y)) t ω =
      c.li * ((iOf y t ω - c.istar) - (lam1 c.β γ c.κ c.σ + (sumS c.β γ c.κ c.σ - ls)) *
          (iOf y (t - 1) ω - c.istar) + lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ - ls) *
          (iOf y (t - 2) ω - c.istar)) -
        c.σ * ((c.β * ls)⁻¹ / γ) * (c.κ * ((piOf y t ω - γ * Zof y t ω) +
          𝔼.E t (fun ω' => Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
            (xproc (inProblem c γ hc hγ0.le) y) (t + 1) ω' ()) ω) +
          (1 + c.β * γ - c.β * (c.β * ls)⁻¹) * (c.lx * (xOf y t ω - c.xstar)) -
          c.lx * (xOf y (t - 1) ω - c.xstar)) := by
  have h := standing_of c γ hc hγ0 hγ1
  obtain ⟨hp, h1, h0, -⟩ := mu_facts c γ h hq
  have hΛ : (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Λ =
      Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β (inJ c (c.β * ls)⁻¹) := rfl
  have hQ : (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Qop
      (xproc (inProblem c γ hc hγ0.le) y) =
      Prop81General.Qop 𝔼 (inSplit c γ hc hγ0 hγ1 hq) (xproc (inProblem c γ hc hγ0.le) y) := rfl
  have hα := InertiaSplit.alpha_inJ c γ h hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hq
  have hα' : (1 - C (lam1 c.β γ c.κ c.σ) * X) * (1 - C (sumS c.β γ c.κ c.σ - ls) * X) =
      (1 : ℝ[X]) - C (lam1 c.β γ c.κ c.σ + (sumS c.β γ c.κ c.σ - ls)) * X +
        C (lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ - ls)) * X ^ 2 := by
    simp only [C_add, C_mul]
    ring
  obtain ⟨hB0, hB1, hB2⟩ := Bc_fin_two (Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le))
    c.β (inJ c (c.β * ls)⁻¹))
  have hL := InertiaSplit.in_Λmat c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hc.1.ne' hγ0.ne' hp
    h1 h0
  have hK := InertiaSplit.in_Kdet c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hp h1 h0
  rw [InertiaSplit.in_Kmat, det_fin_two_of] at hK
  have e00 : Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β (inJ c (c.β * ls)⁻¹) 0 0 =
      (c.β * ls)⁻¹ / γ := by
    rw [hL]
    simp only [Matrix.smul_apply, of_apply, cons_val', cons_val_zero, empty_val',
      cons_val_fin_one, smul_eq_mul]
    field_simp
  have e10 : Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β (inJ c (c.β * ls)⁻¹) 1 0 =
      c.κ * ((c.β * ls)⁻¹ / γ) := by
    rw [hL]
    simp only [Matrix.smul_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, smul_eq_mul]
    field_simp
  unfold TargetCriterion.Crit.crit
  rw [hΛ, hQ, hα, hα', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hB0, hB1, hB2,
    Nat.sub_zero, one_mulVec, zero_mulVec, add_zero,
    show (inProblem c γ hc hγ0.le).sys.B2 = ![0, c.σ] from rfl, dot_two,
    Qop_eq c γ hc hγ0 hγ1 hq 𝔼 hya t, Qop_eq c γ hc hγ0 hγ1 hq 𝔼 hya (t - 1), e00, e10]
  simp only [coeff_add, coeff_sub, coeff_one, coeff_C_mul, coeff_X_pow, coeff_X, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
  generalize 𝔼.E (t - 1) (fun ω' => Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
    (xproc (inProblem c γ hc hγ0.le) y) (t - 1 + 1) ω' ()) ω = A1
  generalize 𝔼.E t (fun ω' => Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
    (xproc (inProblem c γ hc hγ0.le) y) (t + 1) ω' ()) ω = A0
  have hK2 : (c.β * ls)⁻¹ / γ * ((1 + c.β * γ - c.β * (c.β * ls)⁻¹) -
      c.κ * (c.σ * (c.β * ls)⁻¹ + c.σ * (c.β * ls)⁻¹ ^ 2 / (1 - (c.β * ls)⁻¹))) = 1 := by
    rw [show (1 + c.β * γ - c.β * (c.β * ls)⁻¹) - c.κ * (c.σ * (c.β * ls)⁻¹ + c.σ *
      (c.β * ls)⁻¹ ^ 2 / (1 - (c.β * ls)⁻¹)) = γ / (c.β * ls)⁻¹ by linear_combination hK]
    have hβls : c.β * ls ≠ 0 := fun e => h0 (by rw [e, _root_.inv_zero])
    field_simp
    exact div_self hβls
  norm_num
  linear_combination (c.σ * ((c.β * ls)⁻¹ / γ) * (c.lx * (xOf y (t - 1) ω - c.xstar))) * hK2

/-- Woodford (2003), p. 539 (tool): a linear combination of four quantities bounded by `M` is
bounded by `(|a₁| + |a₂| + |a₃| + |a₄|)M`. -/
theorem abs_lin4 {a1 a2 a3 a4 u1 u2 u3 u4 M : ℝ} (h1 : |u1| ≤ M) (h2 : |u2| ≤ M) (h3 : |u3| ≤ M)
    (h4 : |u4| ≤ M) :
    |a1 * u1 + a2 * u2 + a3 * u3 + a4 * u4| ≤ (|a1| + |a2| + |a3| + |a4|) * M := by
  calc |a1 * u1 + a2 * u2 + a3 * u3 + a4 * u4|
      ≤ |a1 * u1| + |a2 * u2| + |a3 * u3| + |a4 * u4| := by
        have e1 := abs_add_le (a1 * u1 + a2 * u2 + a3 * u3) (a4 * u4)
        have e2 := abs_add_le (a1 * u1 + a2 * u2) (a3 * u3)
        have e3 := abs_add_le (a1 * u1) (a2 * u2)
        linarith
    _ = |a1| * |u1| + |a2| * |u2| + |a3| * |u3| + |a4| * |u4| := by simp only [abs_mul]
    _ ≤ |a1| * M + |a2| * M + |a3| * M + |a4| * M := by gcongr
    _ = (|a1| + |a2| + |a3| + |a4|) * M := by ring

/-- Woodford (2003), (3.18)–(3.19), p. 593, along a plan: `q̃'_t = (σ/λᵢ)[κ(π_t − γZ_t) +
λₓ(x_t − x_{t−1})]` (with the plan's own predetermined `Z_t`), and `f̂'_t = q̃'_t − βγE_tq̃'_{t+1}`;
along a feasible plan (`Z_t = π_{t−1}`) these are `q̃` and `f̂` from date `1` on. -/
noncomputable def fplan {Ω : Type*} (𝔼 : ExpectationSystem Ω)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) (s : ℕ) : Ω → ℝ :=
  (c.σ / c.li) • (c.κ • (piOf y s - γ • Zof y s) + c.lx • (xOf y s - xOf y (s - 1))) -
    (c.β * γ) • 𝔼.E s ((c.σ / c.li) • (c.κ • (piOf y (s + 1) - γ • Zof y (s + 1)) +
      c.lx • (xOf y (s + 1) - xOf y s)))

/-- Woodford (2003), App. G.7, pp. 727–728, through the general representation: with
`a_t = E_tF_{t+1}` (`Fw_rec`), the process `W_t = (σ/λᵢ)[κ(q̂_t + a_t) + e g_t − g_{t−1}]` is the
forward sum `∑_j λₛ^{−j} E_t f̂'_{t+j}` (both are the unique bounded adapted solution of
`W_t − λₛ⁻¹E_tW_{t+1} = f̂'_t`; the step uses `κσμ²/(1 − μ) − μe = −γ`, i.e. (1.15) at `μ`). -/
theorem W_eq_fwd {Ω : Type*} (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) (𝔼 : ExpectationSystem Ω)
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} (hyb : BoundedV y) (hya : AdaptedV 𝔼 y) (t : ℕ)
    (ω : Ω) :
    c.σ / c.li * (c.κ * ((piOf y t ω - γ * Zof y t ω) +
        𝔼.E t (fun ω' => Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
          (xproc (inProblem c γ hc hγ0.le) y) (t + 1) ω' ()) ω) +
        (1 + c.β * γ - c.β * (c.β * ls)⁻¹) * (c.lx * (xOf y t ω - c.xstar)) -
        c.lx * (xOf y (t - 1) ω - c.xstar)) =
      InflationInertiaRepresentations.fwd 𝔼 (geomKer ls⁻¹) (fplan c γ 𝔼 y) t ω := by
  have h := standing_of c γ hc hγ0 hγ1
  obtain ⟨hp, h1, h0, -⟩ := mu_facts c γ h hq
  have hls1 : 1 < ls := InertiaSplit.one_lt_of_quadQ h hq
  have hβ0 := hc.1.ne'
  set μ := (c.β * ls)⁻¹ with hμ
  have hBμ : c.β * μ = ls⁻¹ := by
    rw [hμ]
    field_simp
  set e := 1 + c.β * γ - c.β * μ with he
  set j1 := c.σ * μ ^ 2 / (1 - μ) with hj1
  have hj : c.κ * j1 - μ * e = -γ := by
    unfold pR at hp
    rw [hj1, he]
    field_simp
    linear_combination hp
  set Fs : ℕ → Ω → ℝ := fun s ω' => Prop81General.Fw 𝔼 (inSplit c γ hc hγ0 hγ1 hq)
    (xproc (inProblem c γ hc hγ0.le) y) s ω' () with hFs
  set qh : ℕ → Ω → ℝ := fun s => piOf y s - γ • Zof y s with hqh
  set g : ℕ → Ω → ℝ := fun s => c.lx • (xOf y s - fun _ => c.xstar) with hg
  set a : ℕ → Ω → ℝ := fun s => 𝔼.E s (Fs (s + 1)) with ha
  set W : ℕ → Ω → ℝ := fun s => (c.σ / c.li) • (c.κ • (qh s + a s) + e • g s - g (s - 1)) with hW
  have hFrec : ∀ s, Fs s = (c.β * μ) • 𝔼.E s (Fs (s + 1)) + c.β • ((μ - γ) • qh s + j1 • g s) := by
    intro s
    funext ω'
    have := Fw_rec c γ hc hγ0 hγ1 hq 𝔼 hyb hya s ω'
    simp only [hFs, hqh, hg, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, piOf, Zof,
      xOf] at this ⊢
    rw [this]
  -- knownness
  have hpk : ∀ s, 𝔼.E s (piOf y s) = piOf y s := fun s => hya s (Sum.inl (Sum.inr 0))
  have hZk : ∀ s, 𝔼.E s (Zof y s) = Zof y s := fun s => hya s (Sum.inl (Sum.inl ()))
  have hxk : ∀ s, 𝔼.E s (xOf y s) = xOf y s := fun s => hya s (Sum.inl (Sum.inr 1))
  have hqhk : ∀ s, 𝔼.E s (qh s) = qh s := fun s => by
    simp only [hqh]
    rw [map_sub, map_smul, hpk, hZk]
  have hgk : ∀ s, 𝔼.E s (g s) = g s := fun s => by
    simp only [hg]
    rw [map_smul, map_sub, hxk, 𝔼.const]
  have hgk' : ∀ s, 𝔼.E s (g (s - 1)) = g (s - 1) := fun s =>
    ForwardSolution.E_of_known 𝔼 (Nat.sub_le s 1) (hgk (s - 1))
  have hak : ∀ s, 𝔼.E s (a s) = a s := fun s => by
    simp only [ha]
    rw [𝔼.tower le_rfl]
  -- boundedness
  obtain ⟨My, hMy⟩ := hyb
  have hxb : BoundedV (xproc (inProblem c γ hc hγ0.le) y) :=
    TargetCriterion.Prop81.boundedV_xproc (P := inProblem c γ hc hγ0.le) ⟨My, hMy⟩
  obtain ⟨-, -, ⟨MF, hMF⟩⟩ := fwdSum_spec 𝔼 ((inSplit c γ hc hγ0 hγ1 hq).powDecay_G hc.1)
    (boundedV_mulVec (c.β • (inSplit c γ hc hγ0 hγ1 hq).Jᵀ) hxb)
  have hFb : ∀ s ω', |Fs s ω'| ≤ MF := fun s ω' => hMF s ω' ()
  have hab : ∀ s ω', |a s ω'| ≤ MF := fun s ω' => 𝔼.abs_E_le (hFb (s + 1)) s ω'
  have hpb : ∀ s ω', |piOf y s ω'| ≤ My := fun s ω' => hMy s ω' _
  have hZb : ∀ s ω', |Zof y s ω'| ≤ My := fun s ω' => hMy s ω' _
  have hxb' : ∀ s ω', |xOf y s ω'| ≤ My := fun s ω' => hMy s ω' _
  set K := (1 + |γ|) * My + MF + |c.lx| * (My + |c.xstar|) + My with hK
  have hMy0 : 0 ≤ My := (abs_nonneg _).trans (hMy 0 ω (Sum.inr ()))
  have hMF0 : 0 ≤ MF := (abs_nonneg _).trans (hFb 0 ω)
  have hqhb : ∀ s ω', |qh s ω'| ≤ K := fun s ω' => by
    have e : qh s ω' = 1 * piOf y s ω' + (-γ) * Zof y s ω' + 0 * 0 + 0 * 0 := by
      simp [hqh]
      ring
    rw [e]
    refine (abs_lin4 (M := My) (hpb s ω') (hZb s ω') (by simpa using hMy0)
      (by simpa using hMy0)).trans ?_
    rw [hK]
    simp only [abs_one, abs_neg, abs_zero, add_zero]
    nlinarith [abs_nonneg c.lx, abs_nonneg c.xstar, abs_nonneg γ]
  have hgb : ∀ s ω', |g s ω'| ≤ K := fun s ω' => by
    have e : g s ω' = c.lx * (xOf y s ω' - c.xstar) := by simp [hg]
    rw [e, abs_mul]
    have h2 : |xOf y s ω' - c.xstar| ≤ My + |c.xstar| :=
      (abs_sub _ _).trans (by linarith [hxb' s ω'])
    have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg c.lx)
    rw [hK]
    nlinarith [abs_nonneg γ]
  have hab' : ∀ s ω', |a s ω'| ≤ K := fun s ω' => (hab s ω').trans (by
    rw [hK]
    nlinarith [abs_nonneg c.lx, abs_nonneg c.xstar, abs_nonneg γ])
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hqhb 0 ω)
  have hEE : ∀ s (z : Ω → ℝ), 𝔼.E s (𝔼.E s z) = 𝔼.E s z := fun s z => 𝔼.tower le_rfl z
  -- the forcing `f̂'` through `q̂` and `g`
  have hgd : ∀ s, c.lx • (xOf y s - xOf y (s - 1)) = g s - g (s - 1) := fun s => by
    funext ω'
    simp [hg]
    ring
  have hgd1 : ∀ s, c.lx • (xOf y (s + 1) - xOf y s) = g (s + 1) - g s := fun s => by
    funext ω'
    simp [hg]
    ring
  have hfp0 : ∀ s, fplan c γ 𝔼 y s = (c.σ / c.li) • (c.κ • qh s + (g s - g (s - 1))) -
      (c.β * γ) • 𝔼.E s ((c.σ / c.li) • (c.κ • qh (s + 1) + (g (s + 1) - g s))) := by
    intro s
    unfold fplan
    rw [hgd, hgd1]
  have hfp : ∀ s, fplan c γ 𝔼 y s = (c.σ / c.li) • (c.κ • qh s + (g s - g (s - 1))) -
      (c.β * γ) • ((c.σ / c.li) • (c.κ • 𝔼.E s (qh (s + 1)) + (𝔼.E s (g (s + 1)) - g s))) := by
    intro s
    rw [hfp0]
    simp only [map_smul, map_add, map_sub, hgk]
  -- `a_s` through `F_{s+2}`
  have has : ∀ s, a s = (c.β * μ) • 𝔼.E s (Fs (s + 1 + 1)) +
      c.β • ((μ - γ) • 𝔼.E s (qh (s + 1)) + j1 • 𝔼.E s (g (s + 1))) := by
    intro s
    simp only [ha]
    rw [hFrec (s + 1), map_add, map_smul, map_smul, map_add, map_smul, map_smul,
      𝔼.tower (Nat.le_succ s)]
  have hEW : ∀ s, 𝔼.E s (W (s + 1)) = (c.σ / c.li) • (c.κ • (𝔼.E s (qh (s + 1)) +
      𝔼.E s (Fs (s + 1 + 1))) + e • 𝔼.E s (g (s + 1)) - g s) := by
    intro s
    simp only [hW, ha]
    rw [map_smul, map_sub, map_add, map_smul, map_add, map_smul, 𝔼.tower (Nat.le_succ s),
      Nat.add_sub_cancel, hgk]
  -- `W` is a bounded adapted solution of `W_s − λₛ⁻¹E_sW_{s+1} = f̂'_s`
  have hWsol : (aeval (TargetCriterion.fwdOp 𝔼) (1 - C ls⁻¹ * X)) W = fplan c γ 𝔼 y := by
    funext s
    rw [InertiaProp810.aeval_one_sub, hEW, hfp]
    simp only [hW]
    rw [has]
    funext ω'
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (c.σ / c.li * c.β * 𝔼.E s (g (s + 1)) ω') * hj +
      (c.σ / c.li * (c.κ * (𝔼.E s (qh (s + 1)) ω' + 𝔼.E s (Fs (s + 1 + 1)) ω') +
        e * 𝔼.E s (g (s + 1)) ω' - g s ω')) * hBμ + (c.σ / c.li * g s ω') * he
  have hWa : 𝔼.Adapted W := fun s => by
    simp only [hW]
    rw [map_smul, map_sub, map_add, map_smul, map_add, map_smul, hqhk, hak, hgk, hgk']
  have hWb : BoundedProc W := by
    refine ⟨(|c.σ / c.li * c.κ| + |c.σ / c.li * c.κ| + |c.σ / c.li * e| + |-(c.σ / c.li)|) * K,
      fun s ω' => ?_⟩
    have ew : W s ω' = c.σ / c.li * c.κ * qh s ω' + c.σ / c.li * c.κ * a s ω' +
        c.σ / c.li * e * g s ω' + -(c.σ / c.li) * g (s - 1) ω' := by
      simp only [hW, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [ew]
    exact abs_lin4 (hqhb s ω') (hab' s ω') (hgb s ω') (hgb (s - 1) ω')
  -- `f̂'` is bounded and adapted
  set K2 := (|c.σ / c.li * c.κ| + |c.σ / c.li| + |-(c.σ / c.li)| + |(0 : ℝ)|) * K with hK2
  have hK20 : 0 ≤ K2 := mul_nonneg (by positivity) hK0
  have hinner : ∀ s ω', |((c.σ / c.li) • (c.κ • qh (s + 1) + (g (s + 1) - g s))) ω'| ≤ K2 :=
    fun s ω' => by
      have ew : ((c.σ / c.li) • (c.κ • qh (s + 1) + (g (s + 1) - g s))) ω' =
          c.σ / c.li * c.κ * qh (s + 1) ω' + c.σ / c.li * g (s + 1) ω' +
            -(c.σ / c.li) * g s ω' + 0 * 0 := by
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [ew]
      exact abs_lin4 (hqhb (s + 1) ω') (hgb (s + 1) ω') (hgb s ω') (by simpa using hK0)
  set Mf := (|c.σ / c.li * c.κ| + |c.σ / c.li| + |-(c.σ / c.li)| + |-(c.β * γ)|) * (K + K2)
    with hMf
  have hfb : ∀ s ω', |fplan c γ 𝔼 y s ω'| ≤ Mf := fun s ω' => by
    have ew : fplan c γ 𝔼 y s ω' = c.σ / c.li * c.κ * qh s ω' + c.σ / c.li * g s ω' +
        -(c.σ / c.li) * g (s - 1) ω' + -(c.β * γ) *
          𝔼.E s ((c.σ / c.li) • (c.κ • qh (s + 1) + (g (s + 1) - g s))) ω' := by
      rw [hfp0]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [ew]
    exact abs_lin4 ((hqhb s ω').trans (by linarith)) ((hgb s ω').trans (by linarith))
      ((hgb (s - 1) ω').trans (by linarith))
      ((𝔼.abs_E_le (hinner s) s ω').trans (by linarith))
  have hfa : 𝔼.Adapted (fplan c γ 𝔼 y) := fun s => by
    rw [hfp0]
    simp only [map_sub, map_smul, map_add, hEE, hqhk, hgk, hgk']
  -- the forward sum solves the same equation
  have hg0 : 0 ≤ ls⁻¹ := inv_nonneg.mpr (by linarith)
  have hg1 : ls⁻¹ < 1 := inv_lt_one_of_one_lt₀ hls1
  have hG := InflationInertiaRepresentations.summable_abs_geomKer hg0 hg1
  set Ψ := InflationInertiaRepresentations.fwd 𝔼 (geomKer ls⁻¹) (fplan c γ 𝔼 y) with hΨ
  have hΨb : BoundedProc Ψ := InflationInertiaRepresentations.fwd_bounded 𝔼 hG ⟨Mf, hfb⟩
  have hΨa : 𝔼.Adapted Ψ := fun s => InflationInertiaRepresentations.E_fwd_self 𝔼 hG hfb s
  have hΨsol : (aeval (TargetCriterion.fwdOp 𝔼) (1 - C ls⁻¹ * X)) Ψ = fplan c γ 𝔼 y := by
    funext s
    rw [InertiaProp810.aeval_one_sub]
    have hr := InflationInertiaRepresentations.fwd_rec 𝔼 hG (a := ls⁻¹) (b := 0)
      (by simp [geomKer]) (fun j => by simp [geomKer, pow_succ]; ring) hfb hfa s
    rw [← hΨ] at hr
    rw [hr]
    simp [geomKer]
  have hφ0 : (1 - C ls⁻¹ * X : ℝ[X]) ≠ 0 := by
    intro e0
    have := congrArg (fun p : ℝ[X] => p.coeff 0) e0
    simp at this
  have huniq := Prop84General.forward_inverse_existsUnique (𝔼 := 𝔼) hφ0
    (InertiaProp810.roots_one_sub_inv hls1) ⟨Mf, hfb⟩ hfa
  have hWΨ := huniq.unique ⟨hWb, hWa, hWsol⟩ ⟨hΨb, hΨa, hΨsol⟩
  have := congrFun (congrFun hWΨ t) ω
  rw [← this]
  simp only [hW, hqh, hg, ha, hFs, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), (3.18)–(3.19), p. 593: along a plan with `Z_{s+1} = π_s` (the first
structural equation), `f̂'_s = f̂_s` from date `1` on (`κ ≠ 0`). -/
theorem fplan_eq_fhat {Ω : Type*} (hc : c.Adm) (𝔼 : ExpectationSystem Ω)
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} (hZ : ∀ s, Zof y (s + 1) = piOf y s) {s : ℕ}
    (hs : 1 ≤ s) :
    fplan c γ 𝔼 y s =
      InflationInertiaRepresentations.fhat 𝔼 c.β γ c.κ c.σ c.lx c.li (piOf y) (xOf y) s := by
  have hκ := hc.2.2.2.1.ne'
  have hli := hc.2.2.2.2.2.ne'
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  have hq : ∀ m, (c.σ / c.li) • (c.κ • (piOf y (m + 1) - γ • Zof y (m + 1)) +
      c.lx • (xOf y (m + 1) - xOf y (m + 1 - 1))) =
      InflationInertiaRepresentations.qtilde γ c.κ c.σ c.lx c.li (piOf y) (xOf y) (m + 1) := by
    intro m
    unfold InflationInertiaRepresentations.qtilde
    rw [hZ m, Nat.add_sub_cancel]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  unfold fplan InflationInertiaRepresentations.fhat
  rw [hq n, ← hq (n + 1), Nat.add_sub_cancel]

/-- **Woodford (2003), (1.23)/(1.28) for the inertia model: the general target criterion is Rule
I or Rule II.** For the representation of Proposition 8.1 built from the split solving the real
root `λₛ` forward, along any bounded adapted plan with `Z_{t+1} = π_t`, at every date `t ≥ 1`,
the criterion (1.23) (with `v = λᵢ(i − i*)`, `q = Q(L⁻¹)T̃'W(τ − τ*)`) equals
`λᵢ[(1 − λ₁L)(1 − λ_bL)(i_t − i*) − (βγλₛ)⁻¹ ∑_j λₛ^{−j} E_t f̂_{t+j}]`, `λ_b = S − λₛ`:
the rule (3.22) (`λₛ = λ₃`) or (3.23) (`λₛ = λ₂`) for `ı̂ = i − i*` and `f̂` of (3.18). -/
theorem crit_rule {Ω : Type*} (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {ls : ℝ}
    (hq : quadQ c.β γ c.κ c.σ ls = 0) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} (hyb : BoundedV y) (hya : AdaptedV 𝔼 y)
    (hZ : ∀ s, Zof y (s + 1) = piOf y s) {t : ℕ} (ht : 1 ≤ t) (ω : Ω) :
    TargetCriterion.Crit.crit
        (alpha (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Λ)
        (Bpoly (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Λ) 2
        (inProblem c γ hc hγ0.le).sys.B2 (fun s ω => c.li * (iOf y s ω - c.istar))
        ((Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0).Qop
          (xproc (inProblem c γ hc hγ0.le) y)) t ω =
      c.li * ((iOf y t ω - c.istar) - (lam1 c.β γ c.κ c.σ + (sumS c.β γ c.κ c.σ - ls)) *
          (iOf y (t - 1) ω - c.istar) + lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ - ls) *
          (iOf y (t - 2) ω - c.istar) - (c.β * γ * ls)⁻¹ * ∑' j, (ls⁻¹) ^ j *
          𝔼.E t (InflationInertiaRepresentations.fhat 𝔼 c.β γ c.κ c.σ c.lx c.li (piOf y) (xOf y)
            (t + j)) ω) := by
  have hli := hc.2.2.2.2.2.ne'
  have hσ := hc.2.2.1.ne'
  have hβ := hc.1.ne'
  have hls : ls ≠ 0 := by
    linarith [InertiaSplit.one_lt_of_quadQ (standing_of c γ hc hγ0 hγ1) hq]
  have hfwd : InflationInertiaRepresentations.fwd 𝔼 (geomKer ls⁻¹) (fplan c γ 𝔼 y) t ω =
      ∑' j, (ls⁻¹) ^ j * 𝔼.E t (InflationInertiaRepresentations.fhat 𝔼 c.β γ c.κ c.σ c.lx c.li
        (piOf y) (xOf y) (t + j)) ω := by
    unfold InflationInertiaRepresentations.fwd
    refine tsum_congr fun j => ?_
    rw [fplan_eq_fhat c γ hc 𝔼 hZ (by omega)]
    rfl
  rw [crit_eq c γ hc hγ0 hγ1 hq 𝔼 t0 hya t ω, ← hfwd, ← W_eq_fwd c γ hc hγ0 hγ1 hq 𝔼 hyb hya t ω]
  field_simp

/-- Woodford (2003), (1.23) and (3.22)–(3.23) (tool): for `λᵢ ≠ 0`, the criterion value
`λᵢ[(1 − λ₁L)(1 − λ_bL)ı̂_t − (βγλₛ)⁻¹∑λₛ^{−j}E_tf̂_{t+j}]` vanishes at `t = n + 2` iff the real
rule with kept root `λ_b` and forward root `λₛ` holds at `n`. -/
theorem crit_zero_iff {Ω : Type*} (𝔼 : ExpectationSystem Ω) {li β γ l1 lb ls : ℝ} (hli : li ≠ 0)
    (ı f : ℕ → Ω → ℝ) (n : ℕ) :
    (∀ ω, li * (ı (n + 2) ω - (l1 + lb) * ı (n + 2 - 1) ω + l1 * lb * ı (n + 2 - 2) ω -
        (β * γ * ls)⁻¹ * ∑' j, (ls⁻¹) ^ j * 𝔼.E (n + 2) (f (n + 2 + j)) ω) = 0) ↔
      InflationInertiaRules.RuleIReal 𝔼 β γ l1 lb ls ı f n := by
  unfold InflationInertiaRules.RuleIReal
  refine forall_congr' fun ω => ?_
  rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hli
    · linarith
  · intro h
    right
    linarith

/-- **Woodford (2003), Rule I (3.22), p. 595, is the general target criterion (1.23)/(1.28).**
In the real case, for the representation of Proposition 8.1 whose split solves `λ₃` forward,
along any bounded adapted plan with `Z_{t+1} = π_t`, the general criterion holds at all dates
`t ≥ T` (`T ≥ 2`) iff Rule I holds there (for `ı̂ = i − i*` and `f̂` of (3.18)). -/
theorem crit_iff_ruleI {Ω : Type*} (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : 0 ≤ discQ c.β γ c.κ c.σ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} (hyb : BoundedV y) (hya : AdaptedV 𝔼 y)
    (hZ : ∀ s, Zof y (s + 1) = piOf y s) {T : ℕ} (hT : 2 ≤ T) :
    (∀ t, T ≤ t → ∀ ω, TargetCriterion.Crit.crit
        (alpha (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (InertiaSplit.quadQ_lam3r hD))
          𝔼 t0).Λ)
        (Bpoly (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (InertiaSplit.quadQ_lam3r hD))
          𝔼 t0).Λ) 2
        (inProblem c γ hc hγ0.le).sys.B2 (fun s ω => c.li * (iOf y s ω - c.istar))
        ((Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (InertiaSplit.quadQ_lam3r hD)) 𝔼 t0).Qop
          (xproc (inProblem c γ hc hγ0.le) y)) t ω = 0) ↔
      ∀ t, T ≤ t → InflationInertiaRules.RuleIReal 𝔼 c.β γ (lam1 c.β γ c.κ c.σ)
        (lam2r c.β γ c.κ c.σ) (lam3r c.β γ c.κ c.σ) (fun s ω => iOf y s ω - c.istar)
        (InflationInertiaRepresentations.fhat 𝔼 c.β γ c.κ c.σ c.lx c.li (piOf y) (xOf y))
        (t - 2) := by
  have hb : sumS c.β γ c.κ c.σ - lam3r c.β γ c.κ c.σ = lam2r c.β γ c.κ c.σ := by
    rw [← InertiaSplit.lam2r_add_lam3r]
    ring
  refine forall_congr' fun t => imp_congr_right fun ht => ?_
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
  rw [show n + 2 - 2 = n by omega, ← crit_zero_iff 𝔼 hc.2.2.2.2.2.ne']
  refine forall_congr' fun ω => ?_
  rw [crit_rule c γ hc hγ0 hγ1 _ 𝔼 t0 hyb hya hZ (by omega) ω, hb]

/-- **Woodford (2003), Rule II (3.23), p. 595, is the general target criterion (1.23)/(1.28)**
for the representation whose split solves `λ₂` forward (real case). -/
theorem crit_iff_ruleII {Ω : Type*} (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : 0 ≤ discQ c.β γ c.κ c.σ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    {y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ} (hyb : BoundedV y) (hya : AdaptedV 𝔼 y)
    (hZ : ∀ s, Zof y (s + 1) = piOf y s) {T : ℕ} (hT : 2 ≤ T) :
    (∀ t, T ≤ t → ∀ ω, TargetCriterion.Crit.crit
        (alpha (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (InertiaSplit.quadQ_lam2r hD))
          𝔼 t0).Λ)
        (Bpoly (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (InertiaSplit.quadQ_lam2r hD))
          𝔼 t0).Λ) 2
        (inProblem c γ hc hγ0.le).sys.B2 (fun s ω => c.li * (iOf y s ω - c.istar))
        ((Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 (InertiaSplit.quadQ_lam2r hD)) 𝔼 t0).Qop
          (xproc (inProblem c γ hc hγ0.le) y)) t ω = 0) ↔
      ∀ t, T ≤ t → InflationInertiaRules.RuleIIReal 𝔼 c.β γ (lam1 c.β γ c.κ c.σ)
        (lam2r c.β γ c.κ c.σ) (lam3r c.β γ c.κ c.σ) (fun s ω => iOf y s ω - c.istar)
        (InflationInertiaRepresentations.fhat 𝔼 c.β γ c.κ c.σ c.lx c.li (piOf y) (xOf y))
        (t - 2) := by
  have hb : sumS c.β γ c.κ c.σ - lam2r c.β γ c.κ c.σ = lam3r c.β γ c.κ c.σ := by
    rw [← InertiaSplit.lam2r_add_lam3r]
    ring
  refine forall_congr' fun t => imp_congr_right fun ht => ?_
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
  unfold InflationInertiaRules.RuleIIReal
  rw [show n + 2 - 2 = n by omega, ← crit_zero_iff 𝔼 hc.2.2.2.2.2.ne']
  refine forall_congr' fun ω => ?_
  rw [crit_rule c γ hc hγ0 hγ1 _ 𝔼 t0 hyb hya hZ (by omega) ω, hb]

end Woodford.OptimalPolicyRules.InertiaCriterion
