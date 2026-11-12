/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureGeneral
import OptimalPolicyRules.OptimalRulesMeasureStatic

/-!
# Stability of the endogenous state transition `H_n`

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541) and the state
transition `(Z_{t+1}, M_t) = h + H_n (Z_t, M_{t−1}) + …` of the optimal plan (p. 539).
`OptimalRulesMeasureMarkov.m_focSolvable_var` (existence on VAR economies) assumes that `H_n` is
**geometrically stable** (`PencilSplit.PowDecay`). Does this follow from the perfect-foresight
Assumption 8.1?

## Answer

* **No.** `H_n` is always **power-bounded** (`powBdd_Hn`, from
  `OptimalRulesMeasureGeneral.powBdd_Hgen`), but it can have an **eigenvalue of modulus one**:
  in the problem `urP` — the static problem `0 = z + i + c`, loss `½(z² + i²)`, plus a
  predetermined variable with `Z_{t+1} = Z_t` that affects nothing — the perfect-foresight
  Assumption 8.1 holds (`ur_pf`), but `H_n` has the eigenvalue `1` (`ur_eigenvalue_one`) and is
  not geometrically stable (`ur_not_powDecay`).
* **Geometric stability is not necessary either**: in the same problem the measure
  Assumption 8.1 holds on every filtered probability space for every bounded adapted disturbance
  (`ur_assumption81MB`).
* **The corrected statement** (`powDecay_Hn_iff`): under the perfect-foresight Assumption 8.1,
  `H_n` is geometrically stable **iff it has no eigenvalue on the unit circle** (the root
  condition), iff every homogeneous perfect-foresight state path converges
  (`powDecay_of_tendsto`); and `H_n` is the general `OptimalRulesMeasureGeneral.Hgen`
  (`Hn_eq_Hgen`), whatever VAR is used to define it.

The book's two models are verified in `OptimalRulesMeasureStabilityModels`.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureStability

open MeasureTheory Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov OptimalRulesMeasureForecast
  OptimalRulesMeasureKernel OptimalRulesMeasureGeneral

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### `H_n` of `OptimalRulesMeasureMarkov` is the general `H` -/

/-- Woodford (2003), p. 539: the perfect-foresight next state from `(n, s = 0)` of
`OptimalRulesMeasureMarkov` is the general zero-forcing next state. -/
theorem nextN_mkX_zero {ιs : Type*} [Fintype ιs] [DecidableEq ιs] {P : LQProblem ιZ ιz ιτ}
    (A : Matrix ιs ιs ℝ) (C2 : Matrix ιz ιs ℝ) (hA81 : Assumption81 P perfectForesight 0)
    (hA : PowBdd A) (n : ιZ ⊕ ιz → ℝ) :
    nextN P A C2 hA81 hA (mkX n 0) = nextS hA81 n 0 := by
  have hc : cpf A C2 (OptimalRulesMeasureMarkov.Xs (mkX n (0 : ιs → ℝ))) =
      fun k (_ : Unit) => (0 : ℕ → ιz → ℝ) k := by
    have hX : OptimalRulesMeasureMarkov.Xs (mkX n (0 : ιs → ℝ)) = 0 := rfl
    rw [hX]
    funext k u
    simp [cpf]
  have hs : PFSol P n 0 (pfY P A C2 hA81 hA (mkX n 0)) (pfΦ P A C2 hA81 hA (mkX n 0)) := by
    have := pf_spec P A C2 hA81 hA (mkX n 0)
    rw [hc] at this
    exact this
  have hu := sol_unique hA81 (bddSeq_zero (ι := ιz)) hs 1
  simp only [nextN, nextS, hu.1, hu.2]

/-- Woodford (2003), p. 539: **`H_n` (defined through a VAR) is the general `H`** — it does not
depend on the VAR used to define it. -/
theorem Hn_eq_Hgen {ιs : Type*} [Fintype ιs] [DecidableEq ιs] {P : LQProblem ιZ ιz ιτ}
    (A : Matrix ιs ιs ℝ) (C2 : Matrix ιz ιs ℝ) (hA81 : Assumption81 P perfectForesight 0)
    (hA : PowBdd A) : Hn P A C2 hA81 hA = Hgen hA81 := by
  funext i j
  rw [Hn_apply, nextN_mkX_zero, nextN_mkX_zero, hgen_spec, hgen_spec, mulVec_zero, add_zero,
    Pi.add_apply, add_sub_cancel_left, mulVec_single_one]
  rfl

/-- Woodford (2003), Assumption 8.1, p. 541: **the perfect-foresight Assumption 8.1 makes `H_n`
power-bounded.** -/
theorem powBdd_Hn {ιs : Type*} [Fintype ιs] [DecidableEq ιs] {P : LQProblem ιZ ιz ιτ}
    (A : Matrix ιs ιs ℝ) (C2 : Matrix ιz ιs ℝ) (hA81 : Assumption81 P perfectForesight 0)
    (hA : PowBdd A) : PowBdd (Hn P A C2 hA81 hA) := by
  rw [Hn_eq_Hgen]
  exact powBdd_Hgen hA81

/-! ### Geometric stability, the root condition and convergence -/

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1 (tool): a geometrically stable real matrix has no eigenvalue on the
unit circle. -/
theorem noUnit_of_powDecay {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℝ}
    (hd : PencilSplit.PowDecay H) :
    ∀ w : ℂ, ‖w‖ = 1 → (Matrix.scalar ι w - H.map Complex.ofReal).det ≠ 0 := by
  intro w hw hdet
  obtain ⟨C, r, hr0, hr1, hC⟩ := hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set Hc := H.map Complex.ofReal with hHc
  have hHv : Hc *ᵥ v = w • v := by
    rw [sub_mulVec] at hv
    have hs : Matrix.scalar ι w *ᵥ v = w • v := by
      rw [Matrix.scalar_apply]
      funext i
      rw [mulVec_diagonal]
      simp
    rw [hs] at hv
    exact (sub_eq_zero.mp hv).symm
  have hpow : ∀ k, Hc ^ k *ᵥ v = w ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hHv, smul_smul, pow_succ', mul_comm]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi
  set B := ∑ j, ‖v j‖ with hB
  have hbound : ∀ k, ‖v i‖ ≤ C * r ^ k * B := by
    intro k
    have e := congrFun (hpow k) i
    have hmap : Hc ^ k = (H ^ k).map Complex.ofReal := by
      rw [hHc]
      exact (Matrix.map_pow H Complex.ofRealHom k).symm
    rw [hmap] at e
    have h1 : ‖(w ^ k • v) i‖ = ‖v i‖ := by
      rw [Pi.smul_apply, norm_smul, norm_pow, hw, one_pow, one_mul]
    rw [← h1, ← e]
    calc ‖((H ^ k).map Complex.ofReal *ᵥ v) i‖
        = ‖∑ j, ((H ^ k) i j : ℂ) * v j‖ := rfl
      _ ≤ ∑ j, ‖((H ^ k) i j : ℂ) * v j‖ := norm_sum_le _ _
      _ ≤ ∑ j, C * r ^ k * ‖v j‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hC k i j) (norm_nonneg _)
      _ = C * r ^ k * B := by rw [hB, Finset.mul_sum]
  have hlim : Tendsto (fun k => C * r ^ k * B) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul C).mul_const B
    simpa using this
  have := ge_of_tendsto' hlim hbound
  linarith

/-- Woodford (2003), Assumption 8.1, p. 541, and p. 539 — **the corrected statement**: under the
perfect-foresight Assumption 8.1, `H_n` is geometrically stable **iff** it has no eigenvalue on
the unit circle (power-boundedness, `powBdd_Hn`, comes for free). -/
theorem powDecay_Hn_iff {ιs : Type*} [Fintype ιs] [DecidableEq ιs] {P : LQProblem ιZ ιz ιτ}
    (A : Matrix ιs ιs ℝ) (C2 : Matrix ιz ιs ℝ) (hA81 : Assumption81 P perfectForesight 0)
    (hA : PowBdd A) :
    PencilSplit.PowDecay (Hn P A C2 hA81 hA) ↔
      ∀ w : ℂ, ‖w‖ = 1 →
        (Matrix.scalar (ιZ ⊕ ιz) w - (Hn P A C2 hA81 hA).map Complex.ofReal).det ≠ 0 :=
  ⟨noUnit_of_powDecay, powDecay_of_powBdd_noUnit (powBdd_Hn A C2 hA81 hA)⟩

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1 (tool): **if every orbit of a real matrix converges to zero, its
powers decay geometrically** (an eigenvalue with `|μ| ≥ 1` would give a non-decaying complex orbit,
whose real and imaginary parts are real orbits). -/
theorem powDecay_of_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℝ}
    (h : ∀ n : ι → ℝ, Tendsto (fun k => H ^ k *ᵥ n) atTop (𝓝 0)) :
    PencilSplit.PowDecay H := by
  refine PencilSplit.powDecay_of_eig H fun w hw => ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hw
  set Hc := H.map Complex.ofReal with hHc
  have hHv : Hc *ᵥ v = w • v := by
    rw [sub_mulVec] at hv
    have hs : Matrix.scalar ι w *ᵥ v = w • v := by
      rw [Matrix.scalar_apply]
      funext i
      rw [mulVec_diagonal]
      simp
    rw [hs] at hv
    exact (sub_eq_zero.mp hv).symm
  have hpow : ∀ k, Hc ^ k *ᵥ v = w ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hHv, smul_smul, pow_succ', mul_comm]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi
  have hre := h (fun j => (v j).re)
  have him := h (fun j => (v j).im)
  have hti : Tendsto (fun k => |(H ^ k *ᵥ fun j => (v j).re) i| +
      |(H ^ k *ᵥ fun j => (v j).im) i|) atTop (𝓝 0) := by
    have h1 := ((continuous_abs.comp (continuous_apply i)).tendsto 0).comp hre
    have h2 := ((continuous_abs.comp (continuous_apply i)).tendsto 0).comp him
    simpa using h1.add h2
  have hge : ∀ k, ‖v i‖ ≤ |(H ^ k *ᵥ fun j => (v j).re) i| +
      |(H ^ k *ᵥ fun j => (v j).im) i| := by
    intro k
    have hmap : Hc ^ k = (H ^ k).map Complex.ofReal := by
      rw [hHc]
      exact (Matrix.map_pow H Complex.ofRealHom k).symm
    have e := congrFun (hpow k) i
    rw [hmap] at e
    have h1 : ‖v i‖ ≤ ‖(w ^ k • v) i‖ := by
      rw [Pi.smul_apply, norm_smul, norm_pow]
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hlt)
    rw [← e] at h1
    refine h1.trans ((Complex.norm_le_abs_re_add_abs_im _).trans_eq ?_)
    rw [BKInvariantSplit.re_mulVec, BKInvariantSplit.im_mulVec]
  have := ge_of_tendsto' hti hge
  linarith

/-! ### A counterexample: an eigenvalue of modulus one -/

/-- Woodford (2003), eq. (1.1), p. 537: the structure of the counterexample — a
predetermined `Z` with `Z_{t+1} = Z_t` (`A₁₁ = 1`, `A₁₂ = 0`) that enters nothing else, and
the static row `0 = z_t + i_t + c_t` (`A₂₁ = 0`, `A₂₂ = 1`, `B₂ = 1`, `Ẽ = 0`). -/
noncomputable def urSys : LinearRESystem Unit Unit where
  A11 := 1
  A12 := 0
  A21 := 0
  A22 := 1
  Et := 0
  B2 := fun _ => 1
  A22_isUnit := by simp
  B2_ne_zero := fun h => one_ne_zero (congrFun h ())

/-- Woodford (2003), eqs. (1.2)–(1.4), p. 537: the counterexample problem — targets `τ = (z, i)`,
`W = I`, `τ* = 0`, `β = 1/2`; the predetermined variable does not enter the loss. -/
noncomputable def urP : LQProblem Unit Unit (Fin 2) where
  sys := urSys
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := Matrix.of fun a b => if a = 0 then Sum.elim (fun _ => 0) (fun _ => 1) b else 0
  Ti := ![0, 1]
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), eq. (1.9), p. 541, for `urP`: `E_tξ_{t+1} − 2ξ_t = 0`, `M_t + z_t = 0`,
`M_t + i_t = 0` (`p` = `E_t φ_{t+1}`, `q` = `φ_t`, `v` = `y_t`). -/
theorem ur_foc_iff (p q : Unit ⊕ Unit → ℝ) (v : (Unit ⊕ Unit) ⊕ Unit → ℝ) :
    urP.sys.Atilᵀ *ᵥ p + urP.Tᵀ *ᵥ (urP.W *ᵥ (urP.T *ᵥ v - urP.τstar)) -
        urP.β⁻¹ • (urP.sys.Itilᵀ *ᵥ q) = 0 ↔
      p (Sum.inl ()) - 2 * q (Sum.inl ()) = 0 ∧ p (Sum.inr ()) + v (Sum.inl (Sum.inr ())) = 0 ∧
        p (Sum.inr ()) + v (Sum.inr ()) = 0 := by
  set F := urP.sys.Atilᵀ *ᵥ p + urP.Tᵀ *ᵥ (urP.W *ᵥ (urP.T *ᵥ v - urP.τstar)) -
    urP.β⁻¹ • (urP.sys.Itilᵀ *ᵥ q) with hF
  have h0 : F (Sum.inl (Sum.inl ())) = p (Sum.inl ()) - 2 * q (Sum.inl ()) := by
    simp [hF, LQProblem.T, urP, urSys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type]
  have h1 : F (Sum.inl (Sum.inr ())) = p (Sum.inr ()) + v (Sum.inl (Sum.inr ())) := by
    simp [hF, LQProblem.T, urP, urSys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type]
  have h2 : F (Sum.inr ()) = p (Sum.inr ()) + v (Sum.inr ()) := by
    simp [hF, LQProblem.T, urP, urSys, LinearRESystem.Atil, LinearRESystem.Itil,
      LinearRESystem.Ahat, LinearRESystem.Ihat, LinearRESystem.Bvec, mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two]
  constructor
  · intro h
    exact ⟨h0 ▸ congrFun h _, h1 ▸ congrFun h _, h2 ▸ congrFun h _⟩
  · rintro ⟨e0, e1, e2⟩
    funext idx
    rcases idx with (u | u) | u
    · rcases u
      rw [h0, e0]
      rfl
    · rcases u
      rw [h1, e1]
      rfl
    · rcases u
      rw [h2, e2]
      rfl

/-- Woodford (2003), eq. (1.1), p. 537, for `urP`: the expectational row is `0 = z + i + c`. -/
theorem ur_struct_iff (w : Unit → ℝ) (Z : Unit → ℝ) (z : Unit → ℝ) (i : ℝ) (cc : Unit → ℝ) :
    urP.sys.Et *ᵥ w = urP.sys.A21 *ᵥ Z + urP.sys.A22 *ᵥ z + i • urP.sys.B2 + cc ↔
      z () + i + cc () = 0 := by
  have h : ∀ u : Unit, (urP.sys.A21 *ᵥ Z + urP.sys.A22 *ᵥ z + i • urP.sys.B2 + cc) u =
      z () + i + cc () := by
    intro u
    rcases u
    simp [urP, urSys]
  have h0 : urP.sys.Et *ᵥ w = 0 := by simp [urP, urSys]
  rw [h0]
  constructor
  · intro e
    have := congrFun e ()
    rw [h] at this
    simp only [Pi.zero_apply] at this
    linarith
  · intro e
    funext u
    rw [h]
    simp only [Pi.zero_apply]
    linarith

/-- Woodford (2003), eq. (1.1), p. 537, for `urP`: the predetermined row is `Z_{t+1} = Z_t`. -/
theorem ur_Zrow (Z z : Unit → ℝ) : urP.sys.A11 *ᵥ Z + urP.sys.A12 *ᵥ z = Z := by
  simp [urP, urSys]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Woodford (2003), (1.5): the plan of `urP` — `Z_t = Z_{t₀}`, `z_t = i_t = −c_t/2` for
`t ≥ t₀`. -/
noncomputable def urY (c : ℕ → Ω → Unit → ℝ) (Z0 : Ω → Unit → ℝ) (t0 : ℕ) :
    ℕ → Ω → (Unit ⊕ Unit) ⊕ Unit → ℝ :=
  fun t ω => if t0 ≤ t then
    Sum.elim (Sum.elim (fun _ => Z0 ω ()) (fun _ => -(c t ω ()) / 2)) (fun _ => -(c t ω ()) / 2)
  else 0

/-- Woodford (2003), (1.9): the multipliers of `urP` — `ξ_t = 0`, `M_t = c_t/2` for `t ≥ t₀` and
the given `M_{t₀−1}`. -/
noncomputable def urΦ (c : ℕ → Ω → Unit → ℝ) (M0 : Ω → Unit → ℝ) (t0 : ℕ) :
    ℕ → Ω → Unit ⊕ Unit → ℝ :=
  fun t ω => Sum.elim (fun _ => 0)
    (fun _ => if t0 < t then c (t - 1) ω () / 2 else if t = t0 then M0 ω () else 0)

/-- Woodford (2003), Assumption 8.1 (existence), p. 541, for `urP`: on every probability space,
for every bounded adapted disturbance and all bounded initial conditions (`Z_{t₀}` known at
`t₀`, `M_{t₀−1}` known at `t₀ − 1`), `(urY, urΦ)` solves (1.1) + (1.9). -/
theorem ur_solvable (S : MeasExpectationSystem Ω) (t0 : ℕ) : MFOCSolvableMB S urP t0 := by
  intro c Z0 M0 hcb hca hZk hZb hMb hMk
  obtain ⟨Kc, hKc⟩ := hcb
  obtain ⟨KZ, hKZ⟩ := hZb
  obtain ⟨KM, hKM⟩ := hMb
  have hci : ∀ t, Integrable (fun ω => c t ω ()) S.μ := fun t =>
    integrable_of_bound ((hca t ()).mono (S.𝓕.le t)).aestronglyMeasurable
      ((hKc t).mono fun ω h => h ())
  refine ⟨urY c Z0 t0, urΦ c M0 t0, ⟨fun t ht => ⟨Eventually.of_forall fun ω => ?_,
    Eventually.of_forall fun ω => ?_⟩, Eventually.of_forall fun ω => ?_,
    ⟨max |KZ| |Kc|, fun t => ?_⟩, fun t i => ?_⟩,
    ⟨max |Kc| |KM|, fun t => ?_⟩, fun t i => ?_, fun t r => ?_,
    Eventually.of_forall fun ω => ?_, fun t ht => ?_⟩
  · funext u
    simp [urY, ht, show t0 ≤ t + 1 by omega, Zpart, urP, urSys]
  · refine (ur_struct_iff _ _ _ _ _).mpr ?_
    simp only [urY, ht, ↓reduceIte, zpart, ipart, Sum.elim_inl, Sum.elim_inr]
    ring
  · funext u
    simp [urY, Zpart]
  · filter_upwards [hKc t, hKZ] with ω h1 h2 i
    by_cases ht : t0 ≤ t
    · rcases i with (u | u) | u
      · simp only [urY, ht, ↓reduceIte, Sum.elim_inl]
        exact (h2 u).trans ((le_abs_self _).trans (le_max_left _ _))
      · simp only [urY, ht, ↓reduceIte, Sum.elim_inl, Sum.elim_inr]
        rw [abs_div, abs_neg, abs_two]
        have := h1 ()
        have := le_max_right |KZ| |Kc|
        linarith [abs_nonneg (c t ω ()), le_abs_self Kc]
      · simp only [urY, ht, ↓reduceIte, Sum.elim_inr]
        rw [abs_div, abs_neg, abs_two]
        have := h1 ()
        have := le_max_right |KZ| |Kc|
        linarith [abs_nonneg (c t ω ()), le_abs_self Kc]
    · simp only [urY, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact (abs_nonneg _).trans (le_max_left _ _)
  · by_cases ht : t0 ≤ t
    · rcases i with (u | u) | u
      · have : (fun ω => urY c Z0 t0 t ω (Sum.inl (Sum.inl u))) = fun ω => Z0 ω () := by
          funext ω
          simp only [urY, ht, ↓reduceIte, Sum.elim_inl]
        rw [this]
        exact (hZk ()).mono (S.𝓕.mono ht)
      · have : (fun ω => urY c Z0 t0 t ω (Sum.inl (Sum.inr u))) =
            fun ω => -(c t ω ()) / 2 := by
          funext ω
          simp only [urY, ht, ↓reduceIte, Sum.elim_inl, Sum.elim_inr]
        rw [this]
        exact ((hca t ()).measurable.neg.div_const 2).stronglyMeasurable
      · have : (fun ω => urY c Z0 t0 t ω (Sum.inr u)) = fun ω => -(c t ω ()) / 2 := by
          funext ω
          simp only [urY, ht, ↓reduceIte, Sum.elim_inr]
        rw [this]
        exact ((hca t ()).measurable.neg.div_const 2).stronglyMeasurable
    · have : (fun ω => urY c Z0 t0 t ω i) = fun _ => 0 := by
        funext ω
        simp only [urY, ht, ↓reduceIte, Pi.zero_apply]
      rw [this]
      exact stronglyMeasurable_const
  · filter_upwards [hKc (t - 1), hKM] with ω h1 h2 i
    rcases i with u | u
    · simp only [urΦ, Sum.elim_inl, abs_zero]
      exact (abs_nonneg _).trans (le_max_left _ _)
    · have e1 := h1 ()
      have e2 := h2 ()
      simp only [urΦ, Sum.elim_inr]
      split_ifs
      · rw [abs_div, abs_two]
        linarith [abs_nonneg (c (t - 1) ω ()), le_abs_self Kc, le_max_left |Kc| |KM|]
      · linarith [le_abs_self KM, le_max_right |Kc| |KM|]
      · simp
  · rcases i with u | u
    · simp only [urΦ, Sum.elim_inl]
      exact aestronglyMeasurable_const
    · by_cases h1 : t0 < t
      · have : (fun ω => urΦ c M0 t0 t ω (Sum.inr u)) = fun ω => c (t - 1) ω () / 2 := by
          funext ω
          simp only [urΦ, Sum.elim_inr, h1, ↓reduceIte]
        rw [this]
        exact (((hca (t - 1) ()).mono (S.𝓕.le _)).measurable.div_const 2).aestronglyMeasurable
      · by_cases h2 : t = t0
        · have : (fun ω => urΦ c M0 t0 t ω (Sum.inr u)) = fun ω => M0 ω () := by
            funext ω
            simp only [urΦ, Sum.elim_inr, h2, lt_irrefl, ↓reduceIte]
          rw [this]
          exact ((hMk ()).mono (S.𝓕.le _)).aestronglyMeasurable
        · have : (fun ω => urΦ c M0 t0 t ω (Sum.inr u)) = fun _ => 0 := by
            funext ω
            simp only [urΦ, Sum.elim_inr, h1, h2, ↓reduceIte]
          rw [this]
          exact aestronglyMeasurable_const
  · by_cases h1 : t0 < t + 1
    · have : (fun ω => urΦ c M0 t0 (t + 1) ω (Sum.inr r)) = fun ω => c t ω () / 2 := by
        funext ω
        simp only [urΦ, Sum.elim_inr, h1, ↓reduceIte, Nat.add_sub_cancel]
      rw [this]
      exact ((hca t ()).measurable.div_const 2).stronglyMeasurable
    · by_cases h2 : t + 1 = t0
      · have : (fun ω => urΦ c M0 t0 (t + 1) ω (Sum.inr r)) = fun ω => M0 ω () := by
          funext ω
          simp only [urΦ, Sum.elim_inr, h2, lt_irrefl, ↓reduceIte]
        rw [this]
        have := hMk ()
        rwa [show t0 - 1 = t by omega] at this
      · have : (fun ω => urΦ c M0 t0 (t + 1) ω (Sum.inr r)) = fun _ => 0 := by
          funext ω
          simp only [urΦ, Sum.elim_inr, h1, h2, ↓reduceIte]
        rw [this]
        exact stronglyMeasurable_const
  · funext r
    simp [urΦ, Mpart]
  · have hE : ∀ i, S.E t (fun ω => urΦ c M0 t0 (t + 1) ω i) = fun ω => urΦ c M0 t0 (t + 1) ω i := by
      intro i
      rcases i with u | u
      · simp only [urΦ, Sum.elim_inl]
        exact S.E_const t 0
      · have hfun : (fun ω => urΦ c M0 t0 (t + 1) ω (Sum.inr u)) = fun ω => c t ω () / 2 := by
          funext ω
          simp only [urΦ, Sum.elim_inr, show t0 < t + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
        rw [hfun]
        exact S.E_of_stronglyMeasurable ((hca t ()).measurable.div_const 2).stronglyMeasurable
          ((hci t).div_const 2)
    refine Eventually.of_forall fun ω => (ur_foc_iff _ _ _).mpr ?_
    have hp : EVm S t (urΦ c M0 t0 (t + 1)) ω = urΦ c M0 t0 (t + 1) ω := by
      funext i
      exact congrFun (hE i) ω
    rw [hp]
    simp only [urΦ, urY, ht, ↓reduceIte, Sum.elim_inl, Sum.elim_inr,
      show t0 < t + 1 by omega, Nat.add_sub_cancel]
    refine ⟨by ring, by ring, by ring⟩

omit [MeasurableSpace Ω] in
/-- Woodford (2003), App. G (tool): a bounded process with `x_t = ½ E_t x_{t+1}` a.s. from `t₀`
on vanishes a.s. from `t₀` on (iterate: `|x_t| ≤ 2^{−k} K` for every `k`). -/
theorem half_forward_zero [MeasurableSpace Ω] {S : MeasExpectationSystem Ω} {x : ℕ → Ω → ℝ}
    {K : ℝ} (hb : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ K) {t0 : ℕ}
    (h : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, x t ω = (1 / 2) * S.E t (x (t + 1)) ω) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, x t ω = 0 := by
  have hk : ∀ k t, t0 ≤ t → ∀ᵐ ω ∂S.μ, |x t ω| ≤ (1 / 2) ^ k * max K 0 := by
    intro k
    induction k with
    | zero =>
      intro t _
      filter_upwards [hb t] with ω h
      rw [pow_zero, one_mul]
      exact h.trans (le_max_left _ _)
    | succ k ih =>
      intro t ht
      filter_upwards [h t ht, S.abs_E_le (ih (t + 1) (by omega)) t] with ω e1 e2
      rw [e1, abs_mul, pow_succ]
      have : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [this]
      nlinarith [abs_nonneg (S.E t (x (t + 1)) ω)]
  intro t ht
  filter_upwards [ae_all_iff.2 fun k => hk k t ht] with ω h
  have hlim : Tendsto (fun k => (1 / 2 : ℝ) ^ k * max K 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).mul_const (max K 0)
  have := ge_of_tendsto' hlim h
  exact abs_nonpos_iff.mp this

/-- Woodford (2003), pp. 541–542, for `urP`: every bounded solution of (1.1) + (1.9) has, a.s. for
all `t ≥ t₀`, `Z_t = Z_{t₀}`, `z_t = i_t = −c_t/2`, `ξ_t = 0` and `M_t = c_t/2`. -/
theorem ur_sol {S : MeasExpectationSystem Ω} {c : ℕ → Ω → Unit → ℝ} {t0 : ℕ}
    {Z0 : Ω → Unit → ℝ} {M0 : Ω → Unit → ℝ} {y : ℕ → Ω → (Unit ⊕ Unit) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → Unit ⊕ Unit → ℝ} (h : MFOCSystem S urP c t0 Z0 M0 y φ) :
    ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, y t ω = urY c Z0 t0 t ω ∧ φ t ω (Sum.inl ()) = 0 ∧
      φ (t + 1) ω (Sum.inr ()) = c t ω () / 2 := by
  obtain ⟨Kφ, hKφ⟩ := h.2.1
  have hφi : ∀ t i, Integrable (fun ω => φ t ω i) S.μ := fun t i =>
    integrable_of_bound (h.2.2.1 t i) ((hKφ t).mono fun ω hh => hh i)
  have hfoc : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ,
      EVm S t (φ (t + 1)) ω (Sum.inl ()) - 2 * φ t ω (Sum.inl ()) = 0 ∧
      EVm S t (φ (t + 1)) ω (Sum.inr ()) + y t ω (Sum.inl (Sum.inr ())) = 0 ∧
      EVm S t (φ (t + 1)) ω (Sum.inr ()) + y t ω (Sum.inr ()) = 0 := fun t ht => by
    filter_upwards [h.2.2.2.2.2 t ht] with ω e
    exact (ur_foc_iff _ _ _).mp e
  -- `ξ = 0`
  have hξ := half_forward_zero (x := fun t ω => φ t ω (Sum.inl ())) (fun t => (hKφ t).mono
    fun ω hh => hh _) (t0 := t0) fun t ht => by
      filter_upwards [hfoc t ht] with ω e
      have := e.1
      change S.E t (fun ω => φ (t + 1) ω (Sum.inl ())) ω - 2 * φ t ω (Sum.inl ()) = 0 at this
      linarith
  -- `Z_t = Z_{t₀}`
  have hZ : ∀ t, t0 ≤ t → ∀ᵐ ω ∂S.μ, Zpart (y t ω) = Z0 ω := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact h.1.2.1
    | succ t ht ih =>
      filter_upwards [ih, (h.1.1 t ht).1] with ω e1 e2
      rw [e2, ur_Zrow, e1]
  have hMk : ∀ t ω, EVm S t (φ (t + 1)) ω (Sum.inr ()) = φ (t + 1) ω (Sum.inr ()) := fun t ω =>
    congrFun (S.E_of_stronglyMeasurable (h.2.2.2.1 t ()) (hφi _ _)) ω
  intro t ht
  filter_upwards [hfoc t ht, (h.1.1 t ht).2, hξ t ht, hZ t ht] with ω e es eξ eZ
  have hs := (ur_struct_iff _ _ _ _ _).mp es
  simp only [zpart, ipart] at hs
  rw [hMk] at e
  obtain ⟨-, e1, e2⟩ := e
  refine ⟨funext fun idx => ?_, eξ, by linarith⟩
  rcases idx with (u | u) | u
  · rcases u
    simp only [urY, ht, ↓reduceIte, Sum.elim_inl]
    exact congrFun eZ ()
  · rcases u
    simp only [urY, ht, ↓reduceIte, Sum.elim_inl, Sum.elim_inr]
    linarith
  · rcases u
    simp only [urY, ht, ↓reduceIte, Sum.elim_inr]
    linarith

/-- Woodford (2003), Assumption 8.1 (uniqueness), p. 541, for `urP`, on every probability space. -/
theorem ur_unique (S : MeasExpectationSystem Ω) (t0 : ℕ) : MFOCUnique S urP t0 := by
  intro c Z0 M0 y y' φ φ' h h' t ht
  refine ⟨?_, ?_⟩
  · filter_upwards [ur_sol h t ht, ur_sol h' t ht] with ω e1 e2
    rw [e1.1, e2.1]
  · have hM : ∀ᵐ ω ∂S.μ, φ t ω (Sum.inr ()) = φ' t ω (Sum.inr ()) := by
      rcases Nat.eq_or_lt_of_le ht with h0 | h0
      · subst h0
        filter_upwards [h.2.2.2.2.1, h'.2.2.2.2.1] with ω e1 e2
        exact (congrFun e1 ()).trans (congrFun e2 ()).symm
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        filter_upwards [ur_sol h s (by omega), ur_sol h' s (by omega)] with ω e1 e2
        exact e1.2.2.trans e2.2.2.symm
    filter_upwards [ur_sol h t ht, ur_sol h' t ht, hM] with ω e1 e2 e3
    funext idx
    rcases idx with u | u
    · rcases u
      exact e1.2.1.trans e2.2.1.symm
    · rcases u
      exact e3

/-- Woodford (2003), **Assumption 8.1**, p. 541, for `urP`: the corrected measure form holds on
every filtered probability space, for every bounded adapted disturbance, at every `t₀` — although
`H_n` is not geometrically stable (`ur_not_powDecay`). -/
theorem ur_assumption81MB (S : MeasExpectationSystem Ω) (t0 : ℕ) : MAssumption81MB S urP t0 :=
  ⟨ur_solvable S t0, ur_unique S t0⟩

/-- Woodford (2003), **Assumption 8.1 under perfect foresight**, p. 541, for `urP` (the core
statement, from the one-point probability space). -/
theorem ur_pf : Assumption81 urP perfectForesight 0 :=
  (Bridge.unit_assumption81_iff urP 0).mp (assumption81_iff.mpr
    ⟨ur_assumption81MB _ 0, Bridge.bddInfo_of_finite 0, OptimalRulesMeasureIID.predInfo_zero _⟩)

/-- Woodford (2003), p. 539, for `urP`: the zero-forcing next state is `(Z_1, M_0) = (Z_0, 0)`. -/
theorem ur_nextS (n : Unit ⊕ Unit → ℝ) :
    nextS ur_pf n 0 = Sum.elim (fun _ => n (Sum.inl ())) 0 := by
  obtain ⟨⟨hst, hZ0, -, -⟩, -, -, -, hfoc⟩ := sol_spec ur_pf n (bddSeq_zero (ι := Unit))
  have hrow := hst 0 le_rfl ()
  have hs := (ur_struct_iff _ _ _ _ _).mp hrow.2
  have hf := (ur_foc_iff _ _ _).mp (hfoc 0 le_rfl ())
  simp only [zpart, ipart] at hs
  funext a
  rcases a with u | u
  · rcases u
    simp only [nextS, Sum.elim_inl]
    have := congrFun hrow.1 ()
    rw [ur_Zrow] at this
    change Zpart (solY ur_pf n 0 1) () = _
    rw [this]
    exact congrFun (hZ0 ()) ()
  · rcases u
    simp only [nextS, Sum.elim_inr, Pi.zero_apply]
    change solΦ ur_pf n 0 1 (Sum.inr ()) = 0
    have h1 := hf.2.1
    have h2 := hf.2.2
    change solΦ ur_pf n 0 (0 + 1) (Sum.inr ()) + _ = 0 at h1
    change solΦ ur_pf n 0 (0 + 1) (Sum.inr ()) + _ = 0 at h2
    have h3 : (0 : ℕ → Unit → ℝ) 0 () = 0 := rfl
    change _ + _ + (0 : ℕ → Unit → ℝ) 0 () = 0 at hs
    rw [h3] at hs
    linarith

/-- Woodford (2003), p. 539, for `urP`: `H e_Z = e_Z` — the predetermined variable is a unit
root of the endogenous state transition. -/
theorem ur_Hgen_eZ : Hgen ur_pf *ᵥ (Pi.single (Sum.inl ()) 1 : Unit ⊕ Unit → ℝ) =
    (Pi.single (Sum.inl ()) 1 : Unit ⊕ Unit → ℝ) := by
  have h0 := hgen_spec ur_pf 0
  rw [mulVec_zero, add_zero, ur_nextS] at h0
  have h1 := hgen_spec ur_pf (Pi.single (Sum.inl ()) 1 : Unit ⊕ Unit → ℝ)
  rw [ur_nextS, ← h0] at h1
  have e : Hgen ur_pf *ᵥ (Pi.single (Sum.inl ()) 1 : Unit ⊕ Unit → ℝ) =
      Sum.elim (fun _ => (Pi.single (Sum.inl ()) 1 : Unit ⊕ Unit → ℝ) (Sum.inl ())) 0 -
        Sum.elim (fun _ => (0 : Unit ⊕ Unit → ℝ) (Sum.inl ())) 0 := by
    rw [h1]
    abel
  rw [e]
  funext a
  rcases a with u | u
  · rcases u
    simp
  · rcases u
    simp

/-- Woodford (2003), p. 539 — **the counterexample**: for `urP` (which satisfies the
perfect-foresight Assumption 8.1, `ur_pf`) the endogenous state transition `H` has the
**eigenvalue `1`**, on the unit circle. -/
theorem ur_eigenvalue_one :
    (Matrix.scalar (Unit ⊕ Unit) (1 : ℂ) - (Hgen ur_pf).map Complex.ofReal).det = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨fun i => (((Pi.single (Sum.inl ()) 1 : Unit ⊕ Unit → ℝ) i : ℝ) : ℂ), fun h => ?_, ?_⟩
  · have := congrFun h (Sum.inl ())
    simp at this
  · rw [sub_mulVec, GeneralBKCopy.map_ofReal_mulVec, ur_Hgen_eZ]
    funext i
    simp [Matrix.scalar_apply]

/-- Woodford (2003), p. 539 and `OptimalRulesMeasureMarkov.m_focSolvable_var` — **geometric
stability does not follow from the perfect-foresight Assumption 8.1**: for `urP` the matrix `H`
(and `H_n`, for every VAR used to define it) is not geometrically stable. -/
theorem ur_not_powDecay : ¬ PencilSplit.PowDecay (Hgen ur_pf) := fun hd =>
  noUnit_of_powDecay hd 1 (by simp) ur_eigenvalue_one

/-- Woodford (2003), p. 539: the same for `H_n` of `OptimalRulesMeasureMarkov`, whatever the VAR. -/
theorem ur_not_powDecay_Hn {ιs : Type*} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
    (C2 : Matrix Unit ιs ℝ) (hA : PowBdd A) : ¬ PencilSplit.PowDecay (Hn urP A C2 ur_pf hA) := by
  rw [Hn_eq_Hgen]
  exact ur_not_powDecay

end Woodford.OptimalPolicyRules.OptimalRulesMeasureStability
