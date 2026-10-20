/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralLinks
import OptimalPolicyRules.InflationInertiaRules
import OptimalPolicyRules.InflationInertiaRepresentations
import OptimalPolicyRules.IRuleBasic
import Mathlib.Algebra.Order.Star.Real

/-!
# The general machinery specialised to the inflation-inertia model

Woodford (2003), *Interest and Prices*, Chapter 8: the general framework of §1 (pp. 536–559)
applied to the model with inflation inertia of §3.2 (pp. 592–604).

## Main results

* **The model as a general problem.** `inSys`, `inProblem`: the aggregate-supply relation with
  indexation (2.6) (in its corrected form, Chapter 3 (3.6)) and the IS relation (3.1) are the
  structural equations (1.1) with one predetermined variable `Z_t = π_{t−1}` (`n_Z = 1`),
  `z = (π, x)`, `A₂₂ = [1+βγ −κ; 0 1]` (invertible), `Ẽ = [β 0; σ 1]`, `B₂ = (0, σ)`; the loss
  (3.14) is (1.3) with `τ = (π − γZ, x, i)` and `W = diag(1, λₓ, λᵢ) ≻ 0`.
  `in_structural_iff`: (1.1) is exactly `Z_{t+1} = π_t`, (2.6) and (3.1).
  `in_foc_iff`: the general first-order conditions (1.9) are exactly the multiplier formula for
  the predetermined block, `ξ_t = −βγ(Ξ₂ₜ + π_t − γπ_{t−1})`, together with (3.15), (3.4) and
  (3.5) (`InflationInertiaRules.FOC315`, `FOC34`, `FOC35`).
* **Proposition 8.10 from the general lemma (1.30) ⟺ (1.31).** `prop_8_10_from_general`: the
  Euler equation (3.21) holds from a date `t₀ ≥ 2` on iff the pure targeting rule (3.26) does,
  obtained from `Prop84General.forward_eq_zero_from_iff` applied to the invertible
  `φ(L⁻¹) = 1 − (s/p)L⁻¹ + p⁻¹L⁻²` whose roots are `λ₂, λ₃` (real or a complex pair).
-/

namespace Woodford.OptimalPolicyRules.GeneralLinksInertia

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ
open TargetCriterion (fwdOp aeval_fwdOp_apply)
open InflationInertiaRepresentations (InertiaRoots sR pR Kker fwd Euler TargetRule)
open IRuleBasic (Calib)
open GeneralLinks (piOf xOf iOf piOf_eq xOf_eq cNK)

variable {Ω : Type*}

/-! ### Proposition 8.10 from the general lemma -/

/-- Woodford (2003), (3.26), p. 601: the invertible forward polynomial
`φ(L⁻¹) = 1 − (s/p)L⁻¹ + p⁻¹L⁻²`, `s = λ₂ + λ₃`, `p = λ₂λ₃`. -/
noncomputable def phi310 (s p : ℝ) : ℝ[X] := C 1 - C (s / p) * X + C p⁻¹ * X ^ 2

/-- Woodford (2003), App. G.9, p. 738: `φ(μ) = p⁻¹(μ − λ₂)(μ − λ₃)` over `ℂ`, so the roots of
`φ` are `λ₂` and `λ₃`, both outside the unit circle. -/
theorem phi310_roots {β γ κ σ l1 : ℝ} {l2 l3 : ℂ} (h : InertiaRoots β γ κ σ l1 l2 l3) :
    ∀ z ∈ ((phi310 (sR l2 l3) (pR l2 l3)).map Complex.ofRealHom).roots, 1 < ‖z‖ := by
  have hp0 : (pR l2 l3 : ℂ) ≠ 0 := by
    have := h.one_lt_p
    exact_mod_cast (show pR l2 l3 ≠ 0 by linarith)
  have hfac : (phi310 (sR l2 l3) (pR l2 l3)).map Complex.ofRealHom =
      C ((pR l2 l3 : ℂ)⁻¹) * ((X - C l2) * (X - C l3)) := by
    refine Polynomial.funext fun z => ?_
    have hs := h.coe_s
    have hp := h.coe_p
    have hl2 := h.l2_ne_zero
    have hl3 := h.l3_ne_zero
    simp only [phi310, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, map_C,
      map_X, Polynomial.map_pow, eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
      Complex.ofRealHom_eq_coe, Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_one]
    rw [hs, hp]
    field_simp
    ring
  intro z hz
  rw [hfac, roots_C_mul _ (inv_ne_zero hp0),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
    roots_X_sub_C] at hz
  rcases Multiset.mem_add.mp hz with hz | hz <;> rw [Multiset.mem_singleton] at hz <;>
    rw [hz]
  · exact h.one_lt_norm_l2
  · exact h.one_lt_norm_l3

/-- **Woodford (2003), Proposition 8.10, p. 601, from the general lemma behind Proposition 8.4.**
Under the assumptions of Proposition 8.7 (`InertiaRoots`), bounded adapted `ı̂, f̂` satisfy the
Euler equation (3.21) at all dates `t ≥ t₀` iff they satisfy the pure targeting rule (3.26) at all
those dates (`t₀ ≥ 2`). Here this is derived from `Prop84General.forward_eq_zero_from_iff`: with
`u_t = (1 − λ₁L)ı̂_{t−1} + (βγp)⁻¹ ∑ K_j E_t f̂_{t+j}`, (3.21) at `t` is `E_t φ(L⁻¹)u_t = 0` and
(3.26) at `t` is `u_t = 0`, and `φ` is invertible. -/
theorem prop_8_10_from_general (𝔼 : ExpectationSystem Ω) {β γ κ σ l1 : ℝ} {l2 l3 : ℂ}
    (hβ : 0 < β) (hγ : 0 < γ) (h : InertiaRoots β γ κ σ l1 l2 l3) {i f : ℕ → Ω → ℝ}
    (hib : BoundedProc i) (hia : 𝔼.Adapted i) (hfb : BoundedProc f) (hfa : 𝔼.Adapted f)
    {t0 : ℕ} (ht0 : 2 ≤ t0) :
    (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ i f t) ↔
      (∀ t, t0 ≤ t → TargetRule 𝔼 β γ l1 (sR l2 l3) (pR l2 l3) i f t) := by
  set s := sR l2 l3 with hs
  set p := pR l2 l3 with hp'
  have hp : p ≠ 0 := by linarith [h.one_lt_p]
  have hβγ : β * γ ≠ 0 := (mul_pos hβ hγ).ne'
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨Mi, hMi⟩ := hib
  set c := (β * γ * p)⁻¹ with hc
  set Φ := fwd 𝔼 (Kker s p) f with hΦ
  have hΦb : BoundedProc Φ := InflationInertiaRepresentations.fwd_bounded 𝔼 h.summable_abs_Kker
    ⟨Mf, hMf⟩
  have hΦa : 𝔼.Adapted Φ := fun t =>
    InflationInertiaRepresentations.E_fwd_self 𝔼 h.summable_abs_Kker hMf t
  have hrec : ∀ t, Φ t = f t + (s / p) • 𝔼.E t (Φ (t + 1)) + (-1 / p) • 𝔼.E t (Φ (t + 2)) :=
    fun t => h.fwd_Kker_rec 𝔼 hMf hfa t
  set u : ℕ → Ω → ℝ := fun t => (i (t - 1) - l1 • i (t - 2)) + c • Φ t with hu
  have hua : 𝔼.Adapted u := fun t => by
    simp only [hu]
    rw [map_add, map_sub, map_smul, map_smul, hΦa t,
      ForwardSolution.E_of_known 𝔼 (Nat.sub_le t 1) (hia _),
      ForwardSolution.E_of_known 𝔼 (Nat.sub_le t 2) (hia _)]
  have hub : BoundedProc u := by
    obtain ⟨MΦ, hMΦ⟩ := hΦb
    refine ⟨Mi + |l1| * Mi + |c| * MΦ, fun t ω => ?_⟩
    simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hMi (t - 1) ω
    have h2 := mul_le_mul_of_nonneg_left (hMi (t - 2) ω) (abs_nonneg l1)
    have h3 := mul_le_mul_of_nonneg_left (hMΦ t ω) (abs_nonneg c)
    have e1 := abs_add_le (i (t - 1) ω - l1 * i (t - 2) ω) (c * Φ t ω)
    have e2 := abs_sub (i (t - 1) ω) (l1 * i (t - 2) ω)
    rw [abs_mul] at e1 e2
    linarith
  have hφ0 : phi310 s p ≠ 0 := by
    intro h0
    have := congrArg (fun q => q.coeff 0) h0
    simp [phi310] at this
  have hdeg : (phi310 s p).natDegree = 2 := by
    unfold phi310
    compute_degree!
  have key := Prop84General.forward_eq_zero_from_iff hφ0 (phi310_roots h) hub hua t0
  -- (3.21) at `t` is `E_t φ(L⁻¹) u_t = 0`
  have hA : ∀ t, 2 ≤ t → (Euler 𝔼 β γ κ σ i f t ↔ (aeval (fwdOp 𝔼) (phi310 s p)) u t = 0) := by
    intro t ht
    have hEu1 : 𝔼.E t (u (t + 1)) =
        fun ω => (i t ω - l1 * i (t - 1) ω) + c * 𝔼.E t (Φ (t + 1)) ω := by
      simp only [hu, show t + 1 - 1 = t by omega, show t + 1 - 2 = t - 1 by omega]
      rw [map_add, map_sub, map_smul, map_smul, hia t,
        ForwardSolution.E_of_known 𝔼 (Nat.sub_le t 1) (hia _)]
      rfl
    have hEu2 : 𝔼.E t (u (t + 2)) =
        fun ω => (𝔼.E t (i (t + 1)) ω - l1 * i t ω) + c * 𝔼.E t (Φ (t + 2)) ω := by
      simp only [hu, show t + 2 - 1 = t + 1 by omega, show t + 2 - 2 = t by omega]
      rw [map_add, map_sub, map_smul, map_smul, hia t]
      rfl
    have hc0 : c ≠ 0 := inv_ne_zero (mul_ne_zero hβγ hp)
    have hcoef0 : (phi310 s p).coeff 0 = 1 := by simp [phi310]
    have hcoef1 : (phi310 s p).coeff 1 = -(s / p) := by simp [phi310, coeff_one]
    have hcoef2 : (phi310 s p).coeff 2 = p⁻¹ := by simp [phi310, coeff_one]
    have hval : (aeval (fwdOp 𝔼) (phi310 s p)) u t = fun ω => c * (β * γ * 𝔼.E t (i (t + 1)) ω -
        (1 + γ + β * γ) * i t ω + (1 + γ + (1 + κ * σ) / β) * i (t - 1) ω -
        β⁻¹ * i (t - 2) ω + f t ω) := by
      rw [aeval_fwdOp_apply 𝔼 hua, hdeg]
      funext ω
      have hr := congrFun (hrec t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hr
      have hfac := h.euler_lhs_factored (i (t - 2) ω) (i (t - 1) ω) (i t ω)
        (𝔼.E t (i (t + 1)) ω)
      rw [← hs, ← hp'] at hfac
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hcoef0, hcoef1,
        hcoef2, add_zero, hua t, hEu1, hEu2]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hu, Pi.sub_apply]
      rw [hfac, hr, hc]
      field_simp
      ring
    rw [hval]
    unfold Euler
    rw [funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply,
      smul_eq_mul]
    constructor
    · intro hE
      rw [hE]
      ring
    · intro hZ
      have := (mul_eq_zero.mp hZ).resolve_left hc0
      linarith
  -- (3.26) at `t` is `u_t = 0`
  have hB : ∀ t, 2 ≤ t → (TargetRule 𝔼 β γ l1 s p i f t ↔ u t = 0) := by
    intro t _
    unfold TargetRule
    rw [funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hΦ,
      hc, neg_mul]
    constructor <;> intro h0 <;> linarith
  calc (∀ t, t0 ≤ t → Euler 𝔼 β γ κ σ i f t) ↔
        (∀ t, t0 ≤ t → (aeval (fwdOp 𝔼) (phi310 s p)) u t = 0) :=
        forall_congr' fun t => imp_congr_right fun ht => hA t (by omega)
    _ ↔ (∀ t, t0 ≤ t → u t = 0) := key
    _ ↔ _ := forall_congr' fun t => imp_congr_right fun ht => (hB t (by omega)).symm

/-! ### The inflation-inertia model as a general linear-quadratic problem -/

variable (c : Calib) (γ : ℝ)

/-- Woodford (2003), (2.6), p. 562: `A₂₂ = [1+βγ −κ; 0 1]` is invertible, `det A₂₂ = 1 + βγ > 0`. -/
theorem in_det_ne (hc : c.Adm) (hγ : 0 ≤ γ) : 1 + c.β * γ ≠ 0 := by
  have := mul_nonneg hc.1.le hγ
  exact (by linarith : (0 : ℝ) < 1 + c.β * γ).ne'

/-- Woodford (2003), (2.6) (corrected) and (3.1) as (1.1), p. 537: `Z_t = π_{t−1}`,
`z = (π, x)`; `Z_{t+1} = π_t`, row `0`: `βE_tπ_{t+1} = −γZ_t + (1+βγ)π_t − κx_t − u_t`, row `1`:
`σE_tπ_{t+1} + E_tx_{t+1} = x_t + σi_t − σrⁿ_t`. -/
noncomputable def inSys (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0) : LinearRESystem Unit (Fin 2) where
  A11 := 0
  A12 := Matrix.of fun _ j => if j = 0 then 1 else 0
  A21 := Matrix.of fun j _ => if j = 0 then -γ else 0
  A22 := !![1 + c.β * γ, -c.κ; 0, 1]
  Et := !![c.β, 0; c.σ, 1]
  B2 := ![0, c.σ]
  A22_isUnit := by
    rw [isUnit_iff_ne_zero, det_fin_two_of]
    simpa using hd
  B2_ne_zero := by
    intro h
    have := congrFun h 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at this
    exact hσ this

/-- Woodford (2003), (3.14) as (1.4), p. 537: the targets `τ = (π − γZ, x, i)`. -/
def inTtil : Matrix (Fin 3) (Unit ⊕ Fin 2) ℝ :=
  Matrix.of fun a col => Sum.elim (fun _ => if a = 0 then -γ else 0)
    (fun j : Fin 2 => if (a : ℕ) = j then 1 else 0) col

/-- Woodford (2003), (3.14) as (1.2)–(1.4), p. 537: the inflation-inertia problem,
`W = diag(1, λₓ, λᵢ) ≻ 0`, `τ* = (0, x*, i*)`. -/
noncomputable def inProblem (hc : c.Adm) (hγ : 0 ≤ γ) : LQProblem Unit (Fin 2) (Fin 3) where
  sys := inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)
  β := c.β
  β_pos := hc.1
  β_lt_one := hc.2.1
  Ttil := inTtil γ
  Ti := ![0, 0, 1]
  W := diagonal ![1, c.lx, c.li]
  τstar := ![0, c.xstar, c.istar]
  W_posDef := PosDef.diagonal fun i => by
    fin_cases i
    · simp
    · simpa using hc.2.2.2.2.1
    · simpa using hc.2.2.2.2.2

/-- Woodford (2003), p. 538: the predetermined `Z_t = π_{t−1}` in a plan. -/
def Zof (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => y t ω (Sum.inl (Sum.inl ()))

/-- Woodford (2003), (2.6) (tool): `E_t[π_{t+1} − γπ_t] = E_tπ_{t+1} − γπ_t` for adapted `π`. -/
theorem E_quasi_diff (𝔼 : ExpectationSystem Ω) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (t : ℕ)
    (ω : Ω) : 𝔼.E t (fun ω' => π (t + 1) ω' - γ * π t ω') ω =
      𝔼.E t (π (t + 1)) ω - γ * π t ω := by
  rw [ExpectationTools.E_fun_sub, ExpectationTools.E_fun_mul, hπ t]

/-- **Woodford (2003), (1.1) for the inflation-inertia model, p. 537.** For an adapted plan
with `Z₁ = π₀`, the structural equations (1.1) of `inSys` from date `1` on are exactly
`Z_{t+1} = π_t`, the indexation Phillips curve (2.6) (corrected) and the IS relation (3.1). -/
theorem in_structural_iff (hc : c.Adm) (hγ : 0 ≤ γ) (𝔼 : ExpectationSystem Ω)
    (u rn : ℕ → Ω → ℝ) (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) (hya : AdaptedV 𝔼 y)
    (hZ1 : ∀ ω, Zof y 1 ω = piOf y 0 ω) :
    (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).Structural 𝔼 (cNK c u rn) 1 y ↔
      ∀ t, 1 ≤ t → (∀ ω, Zof y (t + 1) ω = piOf y t ω) ∧
        InflationInertiaRules.AS 𝔼 c.β γ c.κ u (piOf y) (xOf y) t ∧
        InflationInertiaRules.IS 𝔼 c.σ rn (piOf y) (xOf y) (iOf y) t := by
  have hπa : 𝔼.Adapted (piOf y) := fun t => hya t (Sum.inl (Sum.inr 0))
  have hZt : (∀ t, 1 ≤ t → ∀ ω, Zof y (t + 1) ω = piOf y t ω) →
      ∀ t, 1 ≤ t → ∀ ω, Zof y t ω = piOf y (t - 1) ω := by
    intro hz t ht ω
    rcases Nat.lt_or_ge t 2 with h2 | h2
    · obtain rfl : t = 1 := by omega
      exact hZ1 ω
    · have := hz (t - 1) (by omega) ω
      rwa [show t - 1 + 1 = t by omega] at this
  have key : ∀ t ω, (Zpart (y (t + 1) ω) =
      (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).A11 *ᵥ Zpart (y t ω) +
        (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).A12 *ᵥ zpart (y t ω) ∧
      (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).Et *ᵥ
          EV 𝔼 t (fun ω' => zpart (y (t + 1) ω')) ω =
        (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).A21 *ᵥ Zpart (y t ω) +
          (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).A22 *ᵥ zpart (y t ω) +
          ipart (y t ω) • (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)).B2 + cNK c u rn t ω) ↔
      (Zof y (t + 1) ω = piOf y t ω ∧
        piOf y t ω - γ * Zof y t ω = c.κ * xOf y t ω +
          c.β * (𝔼.E t (piOf y (t + 1)) ω - γ * piOf y t ω) + u t ω ∧
        xOf y t ω = 𝔼.E t (xOf y (t + 1)) ω -
          c.σ * (iOf y t ω - 𝔼.E t (piOf y (t + 1)) ω - rn t ω)) := by
    intro t ω
    rw [funext_iff, funext_iff, Fin.forall_fin_two]
    simp only [inSys, cNK, mulVec, dotProduct, Fin.sum_univ_two, EV, zpart, Zpart, ipart,
      piOf_eq, xOf_eq, Zof, piOf, xOf, iOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.zero_apply, Fintype.univ_punit,
      Finset.sum_singleton, Fin.isValue, ↓reduceIte, one_ne_zero]
    constructor
    · rintro ⟨h0, h1, h2⟩
      have h0' := h0 ()
      refine ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun _ => by linarith, by linarith, by linarith⟩
  constructor
  · intro H
    have hz : ∀ t, 1 ≤ t → ∀ ω, Zof y (t + 1) ω = piOf y t ω := fun t ht ω =>
      ((key t ω).mp ⟨(H t ht ω).1, (H t ht ω).2⟩).1
    have hZ := hZt hz
    intro t ht
    refine ⟨hz t ht, fun ω => ?_, fun ω => ?_⟩
    · have := ((key t ω).mp ⟨(H t ht ω).1, (H t ht ω).2⟩).2.1
      rw [hZ t ht ω] at this
      rw [E_quasi_diff γ 𝔼 hπa]
      exact this
    · exact ((key t ω).mp ⟨(H t ht ω).1, (H t ht ω).2⟩).2.2
  · intro H t ht ω
    have hz : ∀ t, 1 ≤ t → ∀ ω, Zof y (t + 1) ω = piOf y t ω := fun t ht ω => (H t ht).1 ω
    have hZ := hZt hz
    refine (key t ω).mpr ⟨hz t ht ω, ?_, (H t ht).2.2 ω⟩
    have := (H t ht).2.1 ω
    rw [E_quasi_diff γ 𝔼 hπa] at this
    rw [hZ t ht ω]
    exact this

/-! ### The first-order conditions (1.9) are (3.15), (3.4), (3.5) -/

/-- Woodford (2003), p. 552: `A'` for the inertia model, by blocks. -/
theorem in_Ahat_transpose_mulVec (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0)
    (v : Unit ⊕ Fin 2 → ℝ) :
    (inSys c γ hσ hd).Ahatᵀ *ᵥ v = Sum.elim (fun _ => -γ * v (Sum.inr 0))
      ![v (Sum.inl ()) + (1 + c.β * γ) * v (Sum.inr 0), -c.κ * v (Sum.inr 0) + v (Sum.inr 1)] := by
  funext r
  rcases r with r | j
  · simp [inSys, LinearRESystem.Ahat, mulVec, dotProduct]
  · fin_cases j <;> simp [inSys, LinearRESystem.Ahat, mulVec, dotProduct, Fin.sum_univ_two]

/-- Woodford (2003), p. 552: `Î'` for the inertia model, by blocks. -/
theorem in_Ihat_transpose_mulVec (hσ : c.σ ≠ 0) (hd : 1 + c.β * γ ≠ 0)
    (v : Unit ⊕ Fin 2 → ℝ) :
    (inSys c γ hσ hd).Ihatᵀ *ᵥ v = Sum.elim (fun _ => v (Sum.inl ()))
      ![c.β * v (Sum.inr 0) + c.σ * v (Sum.inr 1), v (Sum.inr 1)] := by
  funext r
  rcases r with r | j
  · simp [inSys, LinearRESystem.Ihat, mulVec, dotProduct]
  · fin_cases j <;> simp [inSys, LinearRESystem.Ihat, mulVec, dotProduct, Fin.sum_univ_two]

/-- Woodford (2003), p. 553: `T̃'W(τ − τ*) = (−γ(π − γZ), π − γZ, λₓ(x − x*))` for the inertia
model. -/
theorem in_xvec (hc : c.Adm) (hγ : 0 ≤ γ) (v : (Unit ⊕ Fin 2) ⊕ Unit → ℝ) :
    (inProblem c γ hc hγ).Ttilᵀ *ᵥ ((inProblem c γ hc hγ).W *ᵥ
      ((inProblem c γ hc hγ).T *ᵥ v - (inProblem c γ hc hγ).τstar)) =
      Sum.elim (fun _ => -γ * (v (Sum.inl (Sum.inr 0)) - γ * v (Sum.inl (Sum.inl ()))))
        ![v (Sum.inl (Sum.inr 0)) - γ * v (Sum.inl (Sum.inl ())),
          c.lx * (v (Sum.inl (Sum.inr 1)) - c.xstar)] := by
  have e : -(γ * v (Sum.inl (Sum.inl ()))) + v (Sum.inl (Sum.inr 0)) =
      v (Sum.inl (Sum.inr 0)) - γ * v (Sum.inl (Sum.inl ())) := by ring
  funext r
  rcases r with r | j
  · simp [inProblem, inTtil, LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type,
      diagonal_apply, e]
  · fin_cases j
    · simp [inProblem, inTtil, LQProblem.T, mulVec, dotProduct, Fintype.sum_sum_type,
        diagonal_apply, e]
    · simp [inProblem, inTtil, LQProblem.T, mulVec, dotProduct, Fin.sum_univ_three,
        Fintype.sum_sum_type, diagonal_apply]

/-- Woodford (2003), p. 553: `T_i'W(τ − τ*) = λᵢ(i − i*)` for the inertia model. -/
theorem in_vvec (hc : c.Adm) (hγ : 0 ≤ γ) (v : (Unit ⊕ Fin 2) ⊕ Unit → ℝ) :
    (inProblem c γ hc hγ).Ti ⬝ᵥ ((inProblem c γ hc hγ).W *ᵥ
      ((inProblem c γ hc hγ).T *ᵥ v - (inProblem c γ hc hγ).τstar)) =
      c.li * (v (Sum.inr ()) - c.istar) := by
  simp [inProblem, inTtil, LQProblem.T, mulVec, dotProduct, Fin.sum_univ_three,
    Fintype.sum_sum_type, diagonal_apply]

/-- Woodford (2003), p. 592: the multiplier `Ξ₁` on the IS relation, `M_t`'s second entry. -/
def Xi1 (φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ) : ℕ → Ω → ℝ := fun k ω => φ (k + 1) ω (Sum.inr 1)

/-- Woodford (2003), p. 592: the multiplier `Ξ₂` on the AS relation, `M_t`'s first entry. -/
def Xi2 (φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ) : ℕ → Ω → ℝ := fun k ω => φ (k + 1) ω (Sum.inr 0)

/-- Woodford (2003), (1.9) at one date for the inertia model, pp. 541, 552 and 592: with `M_t`
known at `t`, the general first-order conditions at `(t, ω)` are four scalar equations: the
row of the predetermined `Z` (the multiplier `ξ_t`), and the rows of `π`, `x` and `i`. -/
theorem in_foc_at_iff (hc : c.Adm) (hγ : 0 ≤ γ) (𝔼 : ExpectationSystem Ω)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) (t : ℕ) (ω : Ω) :
    ((inProblem c γ hc hγ).sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω +
      (inProblem c γ hc hγ).Tᵀ *ᵥ ((inProblem c γ hc hγ).W *ᵥ ((inProblem c γ hc hγ).T *ᵥ y t ω -
        (inProblem c γ hc hγ).τstar)) - (inProblem c γ hc hγ).β⁻¹ •
          ((inProblem c γ hc hγ).sys.Itilᵀ *ᵥ φ t ω) = 0) ↔
      (-γ * Xi2 φ t ω - γ * (piOf y t ω - γ * Zof y t ω) - c.β⁻¹ * φ t ω (Sum.inl ()) = 0 ∧
        𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω + (1 + c.β * γ) * Xi2 φ t ω +
          (piOf y t ω - γ * Zof y t ω) - c.β⁻¹ * (c.β * φ t ω (Sum.inr 0) +
            c.σ * φ t ω (Sum.inr 1)) = 0 ∧
        -c.κ * Xi2 φ t ω + Xi1 φ t ω + c.lx * (xOf y t ω - c.xstar) -
          c.β⁻¹ * φ t ω (Sum.inr 1) = 0 ∧
        c.σ * Xi1 φ t ω + c.li * (iOf y t ω - c.istar) = 0) := by
  have hE : ∀ j, 𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inr j)) ω = φ (t + 1) ω (Sum.inr j) :=
    fun j => congrFun (hmφ t j) ω
  rw [foc_iff_split _ hmφ y t ω, funext_iff, Sum.forall, Fin.forall_fin_two]
  have hA := in_Ahat_transpose_mulVec c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)
    (EV 𝔼 t (φ (t + 1)) ω)
  have hI := in_Ihat_transpose_mulVec c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ) (φ t ω)
  have hx := in_xvec c γ hc hγ (y t ω)
  have hv := in_vvec c γ hc hγ (y t ω)
  simp only [inProblem] at hA hI hx hv ⊢
  rw [hA, hI, hx, hv]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Sum.elim_inl, Sum.elim_inr,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, Xi1, Xi2, piOf, xOf, iOf, Zof,
    Mpart, inSys, dotProduct, Fin.sum_univ_two, Matrix.cons_val_fin_one, EV, hE]
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, h3⟩
    exact ⟨by linarith [h0 ()], by linarith, by linarith, by linarith⟩
  · rintro ⟨h0, h1, h2, h3⟩
    exact ⟨⟨fun _ => by linarith, by linarith, by linarith⟩, by linarith⟩

/-- **Woodford (2003), (1.9) for the inflation-inertia model, pp. 541 and 592.** For an adapted
plan with `Z_t = π_{t−1}` and multipliers with `M_t` known at `t`, the general first-order
conditions (1.9) of `inProblem` hold at every date `t ≥ 1` iff the multiplier on the
predetermined block is `ξ_t = −βγ(Ξ₂ₜ + π_t − γπ_{t−1})` and (3.15), (3.4), (3.5) hold at every
date `t ≥ 1` — the lead `E_tΞ₂,t+1` and `E_t[π_{t+1} − γπ_t]` of (3.15) come from `E_tξ_{t+1}`. -/
theorem in_foc_iff (hc : c.Adm) (hγ : 0 ≤ γ) (𝔼 : ExpectationSystem Ω)
    (y : ℕ → Ω → (Unit ⊕ Fin 2) ⊕ Unit → ℝ) {φ : ℕ → Ω → Unit ⊕ Fin 2 → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) (hZ : ∀ t, 1 ≤ t → ∀ ω, Zof y t ω = piOf y (t - 1) ω) :
    PFOC (inProblem c γ hc hγ) 𝔼 1 y φ ↔
      (∀ t, 1 ≤ t → ∀ ω, φ t ω (Sum.inl ()) =
        -(c.β * γ) * (Xi2 φ t ω + (piOf y t ω - γ * piOf y (t - 1) ω))) ∧
      ∀ t, 1 ≤ t → InflationInertiaRules.FOC315 𝔼 c.β γ c.σ (piOf y) (Xi1 φ) (Xi2 φ) t ∧
        InflationInertiaRules.FOC34 c.β c.κ c.lx c.xstar (xOf y) (Xi1 φ) (Xi2 φ) t ∧
        InflationInertiaRules.FOC35 c.σ c.li c.istar (iOf y) (Xi1 φ) t := by
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hXi : ∀ t, 1 ≤ t → ∀ ω, Xi1 φ (t - 1) ω = φ t ω (Sum.inr 1) ∧
      Xi2 φ (t - 1) ω = φ t ω (Sum.inr 0) := by
    intro t ht ω
    have e : t - 1 + 1 = t := by omega
    exact ⟨by simp only [Xi1, e], by simp only [Xi2, e]⟩
  have hEξ : ∀ t, (∀ ω, φ (t + 1) ω (Sum.inl ()) =
      -(c.β * γ) * (Xi2 φ (t + 1) ω + (piOf y (t + 1) ω - γ * piOf y t ω))) → ∀ ω,
      𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inl ())) ω = -(c.β * γ) * (𝔼.E t (Xi2 φ (t + 1)) ω +
        𝔼.E t (fun ω' => piOf y (t + 1) ω' - γ * piOf y t ω') ω) := by
    intro t hξ ω
    have e : (fun ω' => φ (t + 1) ω' (Sum.inl ())) = fun ω' =>
        -(c.β * γ) * (Xi2 φ (t + 1) ω' + (piOf y (t + 1) ω' - γ * piOf y t ω')) :=
      funext hξ
    rw [e, ExpectationTools.E_fun_mul, ExpectationTools.E_fun_add]
  have hb : ∀ a b : ℝ, c.β⁻¹ * (c.β * a + c.σ * b) = a + c.β⁻¹ * c.σ * b := by
    intro a b
    field_simp
  constructor
  · intro H
    have hk := fun t ht ω => (in_foc_at_iff c γ hc hγ 𝔼 y hmφ t ω).mp (H t ht ω)
    have hξ : ∀ t, 1 ≤ t → ∀ ω, φ t ω (Sum.inl ()) =
        -(c.β * γ) * (Xi2 φ t ω + (piOf y t ω - γ * piOf y (t - 1) ω)) := by
      intro t ht ω
      have h0 := (hk t ht ω).1
      rw [hZ t ht ω] at h0
      field_simp at h0
      linear_combination -h0
    refine ⟨hξ, fun t ht => ⟨fun ω => ?_, fun ω => ?_, fun ω => ?_⟩⟩
    · have h1 := (hk t ht ω).2.1
      rw [hEξ t (fun ω' => by
          have := hξ (t + 1) (by omega) ω'
          rwa [show t + 1 - 1 = t by omega] at this) ω, hZ t ht ω, hb] at h1
      rw [(hXi t ht ω).1, (hXi t ht ω).2]
      linear_combination h1
    · have h2 := (hk t ht ω).2.2.1
      rw [(hXi t ht ω).1]
      linear_combination h2
    · linarith [(hk t ht ω).2.2.2]
  · rintro ⟨hξ, hF⟩ t ht ω
    refine (in_foc_at_iff c γ hc hγ 𝔼 y hmφ t ω).mpr ⟨?_, ?_, ?_, ?_⟩
    · rw [hZ t ht ω, hξ t ht ω]
      field_simp
      ring
    · rw [hEξ t (fun ω' => by
          have := hξ (t + 1) (by omega) ω'
          rwa [show t + 1 - 1 = t by omega] at this) ω, hZ t ht ω, hb]
      have h1 := (hF t ht).1 ω
      rw [(hXi t ht ω).1, (hXi t ht ω).2] at h1
      linear_combination h1
    · have h2 := (hF t ht).2.1 ω
      rw [(hXi t ht ω).1] at h2
      linear_combination h2
    · linarith [(hF t ht).2.2 ω]

end Woodford.OptimalPolicyRules.GeneralLinksInertia
