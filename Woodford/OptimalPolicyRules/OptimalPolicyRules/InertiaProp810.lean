/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralLinks
import OptimalPolicyRules.Links

/-!
# Proposition 8.10 from the general Proposition 8.4

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.4 (p. 558) and Proposition 8.10
(p. 601; proof App. G.9, pp. 737–739).

Proposition 8.4 says that an instrument rule (1.28), `α(L)(i_t − i*) λᵢ + w_t = 0` with
`α(L) = α₁(L)α₂(L)` (`deg α₁ = m`, zeros of `α₁` inside the unit circle), is equivalent to the
target criterion (1.32), `g_t + λᵢ L^m α₂(L)(i_t − i*) = 0`, where `g = α̃₁(L⁻¹)⁻¹ w` is the
bounded forward inverse. For the inflation-inertia model in the real-root case, Rule I (3.22)
is (1.28) with `α(L) = (1 − λ₁L)(1 − λ₂L)` and `w_t = −(βγλ₃)⁻¹ ∑ λ₃^{−j} E_t f̂_{t+j}`; taking
`α₁ = L − λ₂⁻¹`, `α₂ = −λ₂(1 − λ₁L)` the general `Prop84General.prop84_from` turns it into the
pure targeting rule (3.26).

## Main results

* `fwd_Kker_sub`: the forward inverse of `1 − λ₂⁻¹L⁻¹` applied to `∑ λ₃^{−j} E_t f̂_{t+j}` is the
  double forward sum `∑ K_j E_t f̂_{t+j}` of (3.26): `Φ_t − λ₂⁻¹E_tΦ_{t+1} = ∑ λ₃^{−j}E_tf̂_{t+j}`
  (by uniqueness of bounded forward solutions, `Prop84General.forward_inverse_existsUnique`).
* `ruleI_iff_targetRule`: **Rule I (3.22) ⟺ the targeting rule (3.26), from the general
  Proposition 8.4** (`prop84_from`), for real roots `1 < λ₂, λ₃`, from any date `T ≥ 2`.
* `prop_8_10_via_prop84`: **Proposition 8.10 (real case) via Proposition 8.4**: the Euler
  equation (3.21) ⟺ Rule I (Proposition 8.8, `prop_8_8_real`) ⟺ (3.26) (Proposition 8.4).
-/

namespace Woodford.OptimalPolicyRules.InertiaProp810

open Polynomial GeneralSetup
open TargetCriterion (fwdOp lagOp)
open InflationInertiaRepresentations (InertiaRoots sR pR Kker fwd geomKer TargetRule)
open CubicRoots

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 558: `(1 − aL⁻¹)x_t = x_t − a E_t x_{t+1}`. -/
theorem aeval_one_sub (a : ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) :
    (aeval (fwdOp 𝔼) (1 - C a * X)) x t = x t - a • 𝔼.E t (x (t + 1)) := by
  simp only [map_sub, map_one, map_mul, aeval_C, aeval_X, LinearMap.sub_apply,
    Module.End.one_apply, Module.End.mul_apply, Module.algebraMap_end_apply]
  rfl

/-- Woodford (2003), p. 558: for `a > 1` the zero of `1 − a⁻¹L` (`L = a`) lies outside the unit
circle. -/
theorem roots_one_sub_inv {a : ℝ} (ha : 1 < a) :
    ∀ z ∈ ((1 - C a⁻¹ * X : ℝ[X]).map Complex.ofRealHom).roots, 1 < ‖z‖ := by
  have ha0 : a ≠ 0 := by linarith
  intro z hz
  rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C, map_X,
    Complex.ofRealHom_eq_coe, Prop83.roots_one_sub_C_mul_X] at hz
  have hne : ((a⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero ha0
  simp only [hne, ↓reduceIte, Multiset.mem_singleton] at hz
  rw [hz, ← Complex.ofReal_inv, inv_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  exact ha

/-- Woodford (2003), (3.22) and (G.49), App. G.9: for real roots `1 < λ₂, λ₃` of
`InertiaRoots`, the double forward sum `Φ_t = ∑ K_j E_t f̂_{t+j}` satisfies
`Φ_t − λ₂⁻¹E_tΦ_{t+1} = ∑_j λ₃^{−j} E_t f̂_{t+j}`: `(1 − λ₂⁻¹L⁻¹)⁻¹` applied to the forward sum
of Rule I is the forward sum of (3.26). -/
theorem fwd_Kker_sub {β γ κ σ l1 r2 r3 : ℝ} (h : InertiaRoots β γ κ σ l1 (r2 : ℂ) (r3 : ℂ))
    (hr2 : 1 < r2) (hr3 : 1 < r3) {f : ℕ → Ω → ℝ} (hfb : BoundedProc f) (hfa : 𝔼.Adapted f) :
    (fun t => fwd 𝔼 (Kker (r2 + r3) (r2 * r3)) f t -
        r2⁻¹ • 𝔼.E t (fwd 𝔼 (Kker (r2 + r3) (r2 * r3)) f (t + 1))) =
      fwd 𝔼 (geomKer r3⁻¹) f := by
  have hs : sR (r2 : ℂ) (r3 : ℂ) = r2 + r3 := by simp [sR]
  have hp : pR (r2 : ℂ) (r3 : ℂ) = r2 * r3 := by simp [pR]
  have h20 : r2 ≠ 0 := by linarith
  have h30 : r3 ≠ 0 := by linarith
  obtain ⟨Mf, hMf⟩ := hfb
  have hK := h.summable_abs_Kker
  rw [hs, hp] at hK
  have hrec := fun t => h.fwd_Kker_rec 𝔼 hMf hfa t
  simp only [hs, hp] at hrec
  set Φ := fwd 𝔼 (Kker (r2 + r3) (r2 * r3)) f with hΦ
  have hΦb : BoundedProc Φ := InflationInertiaRepresentations.fwd_bounded 𝔼 hK ⟨Mf, hMf⟩
  have hΦa : 𝔼.Adapted Φ := fun t => InflationInertiaRepresentations.E_fwd_self 𝔼 hK hMf t
  have hg0 : 0 ≤ r3⁻¹ := inv_nonneg.mpr (by linarith)
  have hg1 : r3⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr3
  have hG := InflationInertiaRepresentations.summable_abs_geomKer hg0 hg1
  set Ψ3 := fwd 𝔼 (geomKer r3⁻¹) f with hΨ3
  set D : ℕ → Ω → ℝ := fun t => Φ t - r2⁻¹ • 𝔼.E t (Φ (t + 1)) with hD
  have hφ0 : (1 - C r3⁻¹ * X : ℝ[X]) ≠ 0 := by
    intro e
    have := congrArg (fun p : ℝ[X] => p.coeff 0) e
    simp at this
  have huniq := Prop84General.forward_inverse_existsUnique (𝔼 := 𝔼) hφ0 (roots_one_sub_inv hr3)
    ⟨Mf, hMf⟩ hfa
  -- `D` solves `(1 − λ₃⁻¹L⁻¹)D = f̂`
  have hDb : BoundedProc D := by
    obtain ⟨MΦ, hMΦ⟩ := hΦb
    refine ⟨MΦ + |r2⁻¹| * MΦ, fun t ω => ?_⟩
    simp only [hD, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hMΦ t ω
    have h2 := mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hMΦ (t + 1)) t ω) (abs_nonneg r2⁻¹)
    have e := abs_sub (Φ t ω) (r2⁻¹ * 𝔼.E t (Φ (t + 1)) ω)
    rw [abs_mul] at e
    linarith
  have hDa : 𝔼.Adapted D := fun t => by
    simp only [hD]
    rw [map_sub, map_smul, hΦa t, 𝔼.tower le_rfl]
  have hDsol : (aeval (fwdOp 𝔼) (1 - C r3⁻¹ * X)) D = f := by
    funext t
    rw [aeval_one_sub]
    have hr := hrec t
    simp only [hD]
    rw [map_sub, map_smul, 𝔼.tower (Nat.le_succ t), hr]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  -- `Ψ3` solves `(1 − λ₃⁻¹L⁻¹)Ψ3 = f̂`
  have hΨb : BoundedProc Ψ3 := InflationInertiaRepresentations.fwd_bounded 𝔼 hG ⟨Mf, hMf⟩
  have hΨa : 𝔼.Adapted Ψ3 := fun t => InflationInertiaRepresentations.E_fwd_self 𝔼 hG hMf t
  have hΨsol : (aeval (fwdOp 𝔼) (1 - C r3⁻¹ * X)) Ψ3 = f := by
    funext t
    rw [aeval_one_sub]
    have hr := InflationInertiaRepresentations.fwd_rec 𝔼 hG (a := r3⁻¹) (b := 0)
      (by simp [geomKer]) (fun j => by simp [geomKer, pow_succ]; ring) hMf hfa t
    rw [← hΨ3] at hr
    rw [hr]
    simp [geomKer]
  exact huniq.unique ⟨hDb, hDa, hDsol⟩ ⟨hΨb, hΨa, hΨsol⟩

/-- **Woodford (2003), Rule I (3.22) ⟺ the pure targeting rule (3.26), from the general
Proposition 8.4** (real roots `1 < λ₂, λ₃`). Rule I is (1.28) with `λᵢ`-normalised
`α(L) = (1 − λ₁L)(1 − λ₂L)` and `w_t = −(βγλ₃)⁻¹ ∑ λ₃^{−j} E_t f̂_{t+j}` (written at date `t`;
`RuleIReal` at `t − 2` is stated at date `t`). With `α₁ = L − λ₂⁻¹` (zero inside the unit circle,
`m = 1`), `α₂ = −λ₂(1 − λ₁L)` and `g = −(βγλ₃)⁻¹ ∑ K_j E_t f̂_{t+j}` (which solves
`α̃₁(L⁻¹)g = w`, `fwd_Kker_sub`), `Prop84General.prop84_from` gives (1.32), which is (3.26). -/
theorem ruleI_iff_targetRule {β γ κ σ l1 r2 r3 : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (h : InertiaRoots β γ κ σ l1 (r2 : ℂ) (r3 : ℂ)) (hr2 : 1 < r2) (hr3 : 1 < r3)
    {i f : ℕ → Ω → ℝ} (hib : BoundedProc i) (hia : 𝔼.Adapted i) (hfb : BoundedProc f)
    (hfa : 𝔼.Adapted f) {T : ℕ} (hT : 2 ≤ T) :
    (∀ t, T ≤ t → InflationInertiaRules.RuleIReal 𝔼 β γ l1 r2 r3 i f (t - 2)) ↔
      (∀ t, T ≤ t → TargetRule 𝔼 β γ l1 (sR (r2 : ℂ) (r3 : ℂ)) (pR (r2 : ℂ) (r3 : ℂ)) i f t) := by
  have hs : sR (r2 : ℂ) (r3 : ℂ) = r2 + r3 := by simp [sR]
  have hp : pR (r2 : ℂ) (r3 : ℂ) = r2 * r3 := by simp [pR]
  rw [hs, hp]
  have h20 : r2 ≠ 0 := by linarith
  have h30 : r3 ≠ 0 := by linarith
  have hβγ : β * γ ≠ 0 := (mul_pos hβ hγ).ne'
  obtain ⟨Mf, hMf⟩ := hfb
  have hK := h.summable_abs_Kker
  rw [hs, hp] at hK
  set Φ := fwd 𝔼 (Kker (r2 + r3) (r2 * r3)) f with hΦ
  set Ψ3 := fwd 𝔼 (geomKer r3⁻¹) f with hΨ3
  set k := (β * γ * r3)⁻¹ with hk
  set α1 : ℝ[X] := X - C r2⁻¹ with hα1
  set α2 : ℝ[X] := C (-r2) * (1 - C l1 * X) with hα2
  have hm : α1.natDegree = 1 := natDegree_X_sub_C _
  have hα10 : α1 ≠ 0 := X_sub_C_ne_zero _
  have hroots : ∀ z ∈ (α1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖ := by
    rw [hα1, Prop83.reverse_X_sub_C]
    exact roots_one_sub_inv hr2
  set g : ℕ → Ω → ℝ := fun t => (-k) • Φ t with hg
  set w : ℕ → Ω → ℝ := fun t => (-k) • Ψ3 t with hw
  have hgb : BoundedProc g := by
    obtain ⟨MΦ, hMΦ⟩ := InflationInertiaRepresentations.fwd_bounded 𝔼 hK ⟨Mf, hMf⟩
    refine ⟨|k| * MΦ, fun t ω => ?_⟩
    simp only [hg, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hMΦ t ω) (abs_nonneg k)
  have hga : 𝔼.Adapted g := fun t => by
    simp only [hg]
    rw [map_smul, InflationInertiaRepresentations.E_fwd_self 𝔼 hK hMf t]
  have hgsol : (aeval (fwdOp 𝔼) α1.reverse) g = w := by
    rw [hα1, Prop83.reverse_X_sub_C]
    funext t
    rw [aeval_one_sub]
    have e := congrFun (fwd_Kker_sub 𝔼 h hr2 hr3 ⟨Mf, hMf⟩ hfa) t
    rw [← hΦ, ← hΨ3] at e
    simp only [hg, hw, map_smul]
    rw [← e, smul_sub, smul_comm r2⁻¹ (-k)]
  have key := Prop84General.prop84_from (α2 := α2) (lam := 1) (istar := 0) hm hα10 hroots hib
    hia hgb hga hgsol T
  have hprod : α1 * α2 = C 1 - C (l1 + r2) * X + C (l1 * r2) * X ^ 2 := by
    refine Polynomial.funext fun x => ?_
    simp only [hα1, hα2, eval_mul, eval_sub, eval_X, eval_C, eval_one, eval_add, eval_pow]
    field_simp
    ring
  rw [hprod] at key
  have hα2deg : α2.natDegree ≤ 1 := by
    rw [hα2]
    compute_degree!
  have hpdeg : (C 1 - C (l1 + r2) * X + C (l1 * r2) * X ^ 2 : ℝ[X]).natDegree ≤ 2 := by
    compute_degree!
  refine (forall_congr' fun t => imp_congr_right fun ht => ?_).trans
    (key.trans (forall_congr' fun t => imp_congr_right fun ht => ?_))
  · obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
    unfold InflationInertiaRules.RuleIReal
    rw [show n + 2 - 2 = n by omega, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.smul_apply, one_smul, smul_eq_mul, Pi.zero_apply, sub_zero, hw]
    rw [Prop84General.aeval_lagOp_apply_of_le _ hpdeg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, coeff_add, coeff_sub,
      coeff_C, coeff_C_mul, coeff_X, coeff_X_pow, Nat.sub_zero]
    norm_num
    have eΨ : Ψ3 (n + 2) ω = ∑' j, (r3 ^ j)⁻¹ * 𝔼.E (n + 2) (f (n + 2 + j)) ω := by
      simp [hΨ3, fwd, geomKer, inv_pow]
    have hk' : k = r3⁻¹ * (γ⁻¹ * β⁻¹) := by
      rw [hk]
      ring
    rw [eΨ, hk']
    constructor <;> intro h0 <;> linarith
  · unfold TargetRule
    rw [funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, one_smul, smul_eq_mul,
      Pi.zero_apply, sub_zero, hg]
    rw [Prop84General.lagOp_pow_apply (by omega),
      Prop84General.aeval_lagOp_apply_of_le _ hα2deg (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hα2, coeff_C_mul,
      coeff_sub, coeff_one, Nat.sub_zero, show t - 1 - 1 = t - 2 by omega]
    norm_num
    have e : r3⁻¹ * r2⁻¹ * (γ⁻¹ * β⁻¹) = r2⁻¹ * k := by
      rw [hk]
      ring
    rw [e, ← hΦ]
    have hinv : r2 * r2⁻¹ = 1 := mul_inv_cancel₀ h20
    constructor
    · intro h0
      linear_combination (-r2⁻¹) * h0 - (i (t - 1) ω - l1 * i (t - 2) ω) * hinv
    · intro h0
      linear_combination (-r2) * h0 + k * Φ t ω * hinv

/-- **Woodford (2003), Proposition 8.10, p. 601 (three real roots), via the general
Proposition 8.4.** Under Proposition 8.7's assumptions with `S² ≥ 4P₂₃`, bounded adapted
`ı̂, f̂` satisfy the Euler equation (3.21) at all dates `t ≥ t₀` (each stated at date `t + 2`) iff
they satisfy the pure targeting rule (3.26) at all dates `t ≥ t₀ + 2`. The chain is (3.21) ⟺
Rule I (Proposition 8.8, `InflationInertiaRules.prop_8_8_real`) ⟺ (3.26) (Proposition 8.4,
`ruleI_iff_targetRule`), so the equivalence of the targeting rule with the optimal plan is an
special case of the general Proposition 8.4. -/
theorem prop_8_10_via_prop84 {β γ κ σ : ℝ} (h : Assumptions.Standing β γ κ σ)
    (hD : 0 ≤ discQ β γ κ σ) {i f : ℕ → Ω → ℝ} (hib : BoundedProc i) (hia : 𝔼.Adapted i)
    (hfb : BoundedProc f) (hfa : 𝔼.Adapted f) (t0 : ℕ) :
    (∀ t, t0 ≤ t → InflationInertiaRules.Euler 𝔼 β γ κ σ i f t) ↔
      (∀ t, t0 + 2 ≤ t → TargetRule 𝔼 β γ (lam1 β γ κ σ) (sR (lam2r β γ κ σ : ℂ)
        (lam3r β γ κ σ : ℂ)) (pR (lam2r β γ κ σ : ℂ) (lam3r β γ κ σ : ℂ)) i f t) := by
  obtain ⟨Mi, hMi⟩ := hib
  obtain ⟨Mf, hMf⟩ := hfb
  have h88 := (InflationInertiaRules.prop_8_8_real 𝔼 h hD hia hfa hMi hMf t0).1
  have h84 := ruleI_iff_targetRule 𝔼 h.beta_pos h.gamma_pos (Links.inertiaRoots_real h hD)
    (one_lt_lam2r h) (one_lt_lam3r h) ⟨Mi, hMi⟩ hia ⟨Mf, hMf⟩ hfa (T := t0 + 2) (by omega)
  rw [← h88, ← h84]
  constructor
  · intro H t ht
    exact H (t - 2) (by omega)
  · intro H n hn
    have := H (n + 2) (by omega)
    rwa [show n + 2 - 2 = n by omega] at this

end Woodford.OptimalPolicyRules.InertiaProp810
