/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bFOCNecessity

/-!
# Necessity of the first-order conditions without faithful expectations

Woodford (2003), *Interest and Prices*, Chapter 8, §1.1 (pp. 538–543), the first-order conditions
(1.9).

`TidyR5bFOCNecessity.foc_necessary` proves that every optimal plan satisfies (1.9) state by
state, assuming faithful expectations (`E_t x = 0`, `x ≥ 0` ⇒ `x = 0`). Without faithfulness a
plan can be changed on "null" states without changing its expected loss, so only a
conditional-mean-square ("almost sure") statement can hold. This module proves it for the
general LQ problem, under Assumption 8.1 (existence half) and the pull-out property only:

* `exists_attaining`: the plan `y^{M₀}` of (1.1) + (1.9) with `Ẽ z_{t₀} = ē` (the variational part
  of `TidyR5bFOCNecessity.foc_necessary_explicit`, which does not use faithfulness);
* `targets_meanSq`: an optimal plan `y` and `y^{M₀}` have the same target path in conditional mean
  square, `E_{t₀} ½ (T(y_t − y^{M₀}_t))' W (T(y_t − y^{M₀}_t)) = 0` for `t ≥ t₀`;
* `sq_dot_W_le`: Cauchy–Schwarz for a positive semidefinite form;
* `foc_necessary_meanSq`: `y` with the multipliers of `y^{M₀}` satisfies every part of
  (1.1) + (1.9) exactly, except (1.9) itself, which holds in conditional mean square:
  `E_{t₀}[(residual of (1.9) at t)ᵢ²] = 0` for every component and `t ≥ t₀`;
* `foc_of_meanSq`: with faithful expectations this gives back the pointwise form.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bFOCMeanSq

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ TidyR5bFOCNecessity
open ExpectationTools (Faithful)

variable {Ω : Type*} {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), (1.10), p. 542 (**the attaining FOC plan**, no faithfulness): for a plan
optimal subject to `Ẽ z_{t₀} = ē`, there are bounded initial multipliers `M₀` known at `t₀` whose
solution `y⁰ + H M₀` of (1.1) + (1.9) has `Ẽ z_{t₀} = ē`. Assumption 8.1 (existence) and
pull-out. -/
theorem exists_attaining {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hsolv : FOCSolvable P 𝔼 t0) (hpull : 𝔼.PullOut)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    {ebar : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.OptimalSubjectTo 𝔼 c t0 Z0 ebar y) {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h0 : FOCSystem P 𝔼 c t0 Z0 0 y0 φ0)
    {H : ℕ → Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ} {Φ : ℕ → Matrix (ιZ ⊕ ιz) ιz ℝ}
    (hH : HomResp P t0 H Φ) :
    ∃ M0 : Ω → ιz → ℝ, KnownV 𝔼 t0 M0 ∧ (∃ K, ∀ ω r, |M0 ω r| ≤ K) ∧
      FOCSystem P 𝔼 c t0 Z0 M0 (comboF t0 y0 H M0) (comboF t0 φ0 Φ M0) ∧
      ∀ ω, P.sys.Et *ᵥ zpart (comboF t0 y0 H M0 t0 ω) = ebar ω := by
  have hWt : P.Wᵀ = P.W := by
    have := P.W_posDef.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨hfe, hey, hmin⟩ := hy
  have hZ0k := knownV_Z0 hfe
  set L := Lmat P t0 H with hL
  set e0 : Ω → ιz → ℝ := fun ω => P.sys.Et *ᵥ zpart (y0 t0 ω) with he0
  set d : Ω → ιz → ℝ := fun ω => ebar ω - e0 ω with hd
  -- `d` is known at `t₀` and bounded
  have hzk : ∀ (x : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ), AdaptedV 𝔼 x →
      KnownV 𝔼 t0 (fun ω => P.sys.Et *ᵥ zpart (x t0 ω)) :=
    fun x hx => knownV_mulVec P.sys.Et (fun r => hx t0 (Sum.inl (Sum.inr r)))
  have hebar : ebar = fun ω => P.sys.Et *ᵥ zpart (y t0 ω) := funext fun ω => (hey ω).symm
  have hdk : KnownV 𝔼 t0 d := by
    have := knownV_sub (hzk y hfe.2.2.2) (hzk y0 h0.1.2.2.2)
    rw [hd, hebar]
    exact this
  have hdb : ∃ K, ∀ ω r, |d ω r| ≤ K := by
    obtain ⟨Ky, hKy⟩ := hfe.2.2.1
    obtain ⟨K0, hK0⟩ := h0.1.2.2.1
    obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.sys.Et Ky
    obtain ⟨K2, hK2⟩ := exists_bound_mulVec P.sys.Et K0
    refine ⟨K1 + K2, fun ω r => ?_⟩
    simp only [hd, he0, hebar, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hK1 _ (fun i => hKy t0 ω _) r)
      (hK2 _ (fun i => hK0 t0 ω _) r))
  -- the variational inequality: `d ⟂ ker L'`
  have horth : ∀ ω w, Lᵀ *ᵥ w = 0 → w ⬝ᵥ d ω = 0 := by
    intro ω w hw
    have hwLw : w ⬝ᵥ (L *ᵥ w) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hw, zero_dotProduct]
    have key : ∀ s : ℝ, s * (w ⬝ᵥ d ω) ≤ P.β * Jfn 𝔼 P.β P.T P.W P.τstar t0 y ω := by
      intro s
      set Ms : Ω → ιz → ℝ := fun _ => s • w with hMs
      have hs := combo h0 hH (knownV_const 𝔼 t0 (s • w)) (knownV_const 𝔼 (t0 - 1) (s • w))
        ⟨∑ r, |(s • w) r|, fun _ r => Finset.single_le_sum (f := fun r => |(s • w) r|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ r)⟩
      obtain ⟨hfeM, hbφM, hmφM, hMM, hfM⟩ := hs
      have gap := lagrangian_gap_init hpull P.β_pos P.β_lt_one hWt
        ((structural_iff P.sys 𝔼 c t0 y).mp hfe.1) ((structural_iff P.sys 𝔼 c t0 _).mp hfeM.1)
        hfe.2.2.2 hfeM.2.2.2 hfe.2.2.1 hfeM.2.2.1 hbφM hmφM hfM ω
      have hinit : (fun ω' => comboF t0 φ0 Φ Ms t0 ω' ⬝ᵥ
          (P.sys.Itil *ᵥ (y t0 ω' - comboF t0 y0 H Ms t0 ω'))) = fun ω' => s * (w ⬝ᵥ d ω') := by
        funext ω'
        have hZ : Zpart (y t0 ω' - comboF t0 y0 H Ms t0 ω') = 0 := by
          have h1 := hfe.2.1 ω'
          have h2 := hfeM.2.1 ω'
          funext r
          have e1 := congrFun h1 r
          have e2 := congrFun h2 r
          simp only [Zpart, Pi.sub_apply, Pi.zero_apply] at e1 e2 ⊢
          rw [e1, e2, sub_self]
        have hz : P.sys.Et *ᵥ zpart (y t0 ω' - comboF t0 y0 H Ms t0 ω') =
            d ω' - s • (L *ᵥ w) := by
          have e1 : zpart (y t0 ω' - comboF t0 y0 H Ms t0 ω') =
              zpart (y t0 ω') - zpart (comboF t0 y0 H Ms t0 ω') := rfl
          rw [e1, mulVec_sub, eq110_combo, hey ω', ← hL, hMs, mulVec_smul]
          simp only [hd, he0]
          abel
        have hM := hMM ω'
        rw [P.sys.Itil_mulVec, hZ, hz]
        rw [dotProduct, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          zero_add]
        have e2 : ∀ r, comboF t0 φ0 Φ Ms t0 ω' (Sum.inr r) = s * w r := fun r => by
          have := congrFun hM r
          simpa [Mpart, hMs] using this
        simp only [e2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have e3 : ∑ x, s * w x * (d ω' x - s * (L *ᵥ w) x) =
            s * (w ⬝ᵥ d ω') - s * s * (w ⬝ᵥ (L *ᵥ w)) := by
          simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
        rw [e3, hwLw, mul_zero, sub_zero]
      have hEk : 𝔼.E t0 (fun ω' => s * (w ⬝ᵥ d ω')) = fun ω' => s * (w ⬝ᵥ d ω') := by
        have e : (fun ω' => s * (w ⬝ᵥ d ω')) = s • fun ω' => ∑ i, w i * d ω' i := rfl
        rw [e, map_smul, E_sum_mul]
        funext ω'
        simp only [Pi.smul_apply, smul_eq_mul]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdk i]
      rw [hinit, hEk] at gap
      have hnn := gap.nonneg fun k => mul_nonneg (pow_nonneg P.β_pos.le k)
        (by
          have := 𝔼.mono t0 (x := 0)
            (y := fun ω'' => quad P.W (P.T *ᵥ (y (t0 + k) ω'' - comboF t0 y0 H Ms (t0 + k) ω'')))
            (fun ω'' => quad_nonneg P.W_posDef.posSemidef _) ω
          simpa using this)
      have hJ0 := Jfn_nonneg 𝔼 P.β_pos.le P.W_posDef.posSemidef P.τstar t0
        (comboF t0 y0 H Ms) ω (Tm := P.T)
      have hβi : P.β * P.β⁻¹ = 1 := mul_inv_cancel₀ P.β_pos.ne'
      have h3 : P.β⁻¹ * (s * (w ⬝ᵥ d ω)) ≤ Jfn 𝔼 P.β P.T P.W P.τstar t0 y ω := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 P.β_pos.le
      rw [← mul_assoc, hβi, one_mul] at h4
      exact h4
    by_contra hne
    have := key ((P.β * Jfn 𝔼 P.β P.T P.W P.τstar t0 y ω + 1) / (w ⬝ᵥ d ω))
    rw [div_mul_cancel₀ _ hne] at this
    linarith
  -- `d` lies in the range of `L`
  have hdr : ∀ ω, d ω ∈ LinearMap.range L.mulVecLin := fun ω => mem_range_of_orth L (d ω)
    (horth ω)
  obtain ⟨R, hR⟩ := exists_rightInv L
  set M0 : Ω → ιz → ℝ := fun ω => R *ᵥ d ω with hM0
  have hM0k : KnownV 𝔼 t0 M0 := knownV_mulVec R hdk
  have hM0b : ∃ K, ∀ ω r, |M0 ω r| ≤ K := by
    obtain ⟨Kd, hKd⟩ := hdb
    obtain ⟨K, hK⟩ := exists_bound_mulVec R Kd
    exact ⟨K, fun ω r => hK _ (hKd ω) r⟩
  have hM0k' := knownV_pred_of_solvable hsolv hbc hac hZ0k hM0k
  have hs := combo h0 hH hM0k hM0k' hM0b
  have heb : ∀ ω, P.sys.Et *ᵥ zpart (comboF t0 y0 H M0 t0 ω) = ebar ω := by
    intro ω
    rw [eq110_combo, ← hL, hM0]
    beta_reduce
    rw [hR _ (hdr ω), hd]
    beta_reduce
    simp only [he0]
    abel
  exact ⟨M0, hM0k, hM0b, hs, heb⟩

/-- Woodford (2003), (1.3) (tool): **Cauchy–Schwarz for a positive semidefinite form**,
`(a'Wv)² ≤ (a'Wa)(v'Wv)`. -/
theorem sq_dot_W_le {ι : Type*} [Fintype ι] {W : Matrix ι ι ℝ} (hW : W.PosSemidef)
    (a v : ι → ℝ) : (a ⬝ᵥ (W *ᵥ v)) ^ 2 ≤ (a ⬝ᵥ (W *ᵥ a)) * (v ⬝ᵥ (W *ᵥ v)) := by
  have hWt : Wᵀ = W := by
    have := hW.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hsym : v ⬝ᵥ (W *ᵥ a) = a ⬝ᵥ (W *ᵥ v) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hWt, dotProduct_comm]
  set A := a ⬝ᵥ (W *ᵥ a)
  set B := a ⬝ᵥ (W *ᵥ v)
  set C := v ⬝ᵥ (W *ᵥ v)
  have hq : ∀ s : ℝ, 0 ≤ A + 2 * s * B + s ^ 2 * C := by
    intro s
    have h := hW.dotProduct_mulVec_nonneg (a + s • v)
    rw [star_trivial] at h
    have e : (a + s • v) ⬝ᵥ (W *ᵥ (a + s • v)) = A + 2 * s * B + s ^ 2 * C := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, hsym]
      ring
    rwa [e] at h
  have hC : 0 ≤ C := by
    have := hW.dotProduct_mulVec_nonneg v
    rwa [star_trivial] at this
  rcases hC.lt_or_eq with hC | hC
  · have := hq (-B / C)
    have e : A + 2 * (-B / C) * B + (-B / C) ^ 2 * C = A - B ^ 2 / C := by
      field_simp
      ring
    rw [e, sub_nonneg, div_le_iff₀ hC] at this
    linarith
  · have hB : B = 0 := by
      by_contra hB
      have h1 := hq (-(A + 1) / (2 * B))
      have e : 2 * (-(A + 1) / (2 * B)) * B = -(A + 1) := by field_simp
      rw [e, ← hC, mul_zero] at h1
      linarith
    rw [hB, ← hC]
    simp

/-- Woodford (2003), p. 541 and fn 7 (**targets agree in conditional mean square**, no
faithfulness): if `y` is optimal subject to `Ẽ z_{t₀} = ē` and `y*` solves (1.1) + (1.9) with
`Ẽ z*_{t₀} = ē`, then `E_{t₀} ½ (T(y_t − y*_t))' W (T(y_t − y*_t)) = 0` for every `t ≥ t₀`. -/
theorem targets_meanSq {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hpull : 𝔼.PullOut) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ} {ebar : Ω → ιz → ℝ}
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {M0 : Ω → ιz → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hy : P.OptimalSubjectTo 𝔼 c t0 Z0 ebar y) (hs : FOCSystem P 𝔼 c t0 Z0 M0 ys φ)
    (heb : ∀ ω, P.sys.Et *ᵥ zpart (ys t0 ω) = ebar ω) :
    ∀ t, t0 ≤ t → ∀ ω, 𝔼.E t0 (fun ω' => quad P.W (P.T *ᵥ (y t ω' - ys t ω'))) ω = 0 := by
  have hWt : P.Wᵀ = P.W := by
    have := P.W_posDef.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hopt := optimalSubjectTo_of_focSystem P hpull hs
  have e : (fun ω => P.sys.Et *ᵥ zpart (ys t0 ω)) = ebar := funext heb
  rw [e] at hopt
  obtain ⟨hfe, hbφ, hmφ, -, hfoc⟩ := hs
  intro t ht ω
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  have hJ : Jfn 𝔼 P.β P.T P.W P.τstar t0 y ω = Jfn 𝔼 P.β P.T P.W P.τstar t0 ys ω :=
    le_antisymm (hy.2.2 ys hfe heb ω) (hopt.2.2 y hy.1 hy.2.1 ω)
  have hg := lagrangian_gap hpull P.β_pos P.β_lt_one hWt
    ((structural_iff P.sys 𝔼 c t0 y).mp hy.1.1) ((structural_iff P.sys 𝔼 c t0 ys).mp hfe.1)
    hy.1.2.2.2 hfe.2.2.2 hy.1.2.2.1 hfe.2.2.1 hbφ hmφ hfoc (fun ω' => by
      rw [Itil_init_eq_zero P.sys ((hy.1.2.1 ω').trans (hfe.2.1 ω').symm)
        ((hy.2.1 ω').trans (heb ω').symm), dotProduct_zero]) ω
  rw [hJ, sub_self] at hg
  have hnn : ∀ j, 0 ≤ P.β ^ j *
      𝔼.E t0 (fun ω'' => quad P.W (P.T *ᵥ (y (t0 + j) ω'' - ys (t0 + j) ω''))) ω := by
    intro j
    refine mul_nonneg (pow_pos P.β_pos j).le ?_
    have := 𝔼.mono t0 (x := 0)
      (y := fun ω'' => quad P.W (P.T *ᵥ (y (t0 + j) ω'' - ys (t0 + j) ω'')))
      (fun ω'' => quad_nonneg P.W_posDef.posSemidef _) ω
    simpa using this
  have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hg) k
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', P.β_pos.ne', ne_eq, false_and,
    false_or] at hz
  exact hz

/-- Woodford (2003), eq. (1.9), p. 541: the residual of the first-order conditions at date `t`. -/
noncomputable def res (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) (t : ℕ) (ω : Ω) :
    (ιZ ⊕ ιz) ⊕ Unit → ℝ :=
  P.sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) -
    P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φ t ω)

/-- Woodford (2003), p. 541 (**necessity of the first-order conditions in conditional mean
square**, no faithfulness): under Assumption 8.1 (existence half) and the pull-out property,
for every bounded plan `y` that minimises (1.2) among bounded feasible plans subject to
`Ẽ z_{t₀} = ē` there are bounded initial multipliers `M₀` known at `t₀` and bounded multipliers
`φ` (`M_t` known at `t`, `M_{t₀−1} = M₀`) such that the residual of (1.9) has zero conditional
mean square at every date `t ≥ t₀` and in every component: (1.9) holds "almost surely". -/
theorem foc_necessary_meanSq {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hsolv : FOCSolvable P 𝔼 t0) (hpull : 𝔼.PullOut)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    {ebar : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.OptimalSubjectTo 𝔼 c t0 Z0 ebar y) :
    ∃ (M0 : Ω → ιz → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ), KnownV 𝔼 t0 M0 ∧
      (∃ K, ∀ ω r, |M0 ω r| ≤ K) ∧ P.Feasible 𝔼 c t0 Z0 y ∧ BoundedV φ ∧
      MultiplierMeas 𝔼 φ ∧ (∀ ω, Mpart (φ t0 ω) = M0 ω) ∧
      ∀ t, t0 ≤ t → ∀ ω i, 𝔼.E t0 (fun ω' => res P 𝔼 y φ t ω' i ^ 2) ω = 0 := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨0, 0, fun i => funext fun ω => isEmptyElim ω, ⟨0, fun ω => isEmptyElim ω⟩, hy.1,
      ⟨0, fun _ ω => isEmptyElim ω⟩, fun _ _ => funext fun ω => isEmptyElim ω,
      fun ω => isEmptyElim ω, fun _ _ ω => isEmptyElim ω⟩
  obtain ⟨y0, φ0, h0⟩ := hsolv c Z0 0 hbc hac (knownV_Z0 hy.1) (fun _ => 𝔼.const t0 0)
  obtain ⟨H, Φ, hH⟩ := exists_homResp hsolv
  obtain ⟨M0, hM0k, hM0b, hs, heb⟩ := exists_attaining hsolv hpull hbc hac hy h0 hH
  set ys := comboF t0 y0 H M0
  set φ := comboF t0 φ0 Φ M0
  have htq := targets_meanSq hpull hy hs heb
  refine ⟨M0, φ, hM0k, hM0b, hy.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, fun t ht ω i => ?_⟩
  have hres : ∀ ω', res P 𝔼 y φ t ω' i =
      (fun r => P.T r i) ⬝ᵥ (P.W *ᵥ (P.T *ᵥ (y t ω' - ys t ω'))) := by
    intro ω'
    have h0' := congrFun (hs.2.2.2.2 t ht ω') i
    simp only [Pi.zero_apply] at h0'
    have e : res P 𝔼 y φ t ω' = (P.sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω' +
        P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ ys t ω' - P.τstar)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φ t ω')) +
        P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ (y t ω' - ys t ω'))) := by
      simp only [res, mulVec_sub]
      abel
    rw [e, Pi.add_apply, h0', zero_add]
    simp [mulVec, dotProduct, transpose_apply]
  set Ki := (fun r => P.T r i) ⬝ᵥ (P.W *ᵥ fun r => P.T r i)
  have hbd : ∀ ω', res P 𝔼 y φ t ω' i ^ 2 ≤
      (2 * Ki) * quad P.W (P.T *ᵥ (y t ω' - ys t ω')) := by
    intro ω'
    rw [hres]
    have := sq_dot_W_le P.W_posDef.posSemidef (fun r => P.T r i) (P.T *ᵥ (y t ω' - ys t ω'))
    unfold quad
    linarith
  have hmono := 𝔼.mono t0 (x := fun ω' => res P 𝔼 y φ t ω' i ^ 2)
    (y := (2 * Ki) • fun ω' => quad P.W (P.T *ᵥ (y t ω' - ys t ω'))) (fun ω' => hbd ω') ω
  rw [map_smul, Pi.smul_apply, htq t ht ω, smul_zero] at hmono
  have hnn := 𝔼.mono t0 (x := 0) (y := fun ω' => res P 𝔼 y φ t ω' i ^ 2)
    (fun ω' => sq_nonneg _) ω
  rw [map_zero] at hnn
  exact le_antisymm hmono hnn

/-- Woodford (2003), p. 541: with faithful expectations the conditional-mean-square form gives
the first-order conditions (1.9) state by state (`TidyR5bFOCNecessity.foc_necessary`). -/
theorem foc_of_meanSq {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hfaith : Faithful 𝔼) {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : ∀ t, t0 ≤ t → ∀ ω i, 𝔼.E t0 (fun ω' => res P 𝔼 y φ t ω' i ^ 2) ω = 0) :
    PFOC P 𝔼 t0 y φ := by
  intro t ht ω
  funext i
  have := hfaith.eq_zero (fun ω' => sq_nonneg (res P 𝔼 y φ t ω' i))
    (funext fun ω' => h t ht ω' i) ω
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

end Woodford.OptimalPolicyRules.TidyR5bFOCMeanSq
