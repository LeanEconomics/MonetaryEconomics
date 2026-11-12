/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigma

/-!
# Determinacy forces certainty equivalence; the illustration's risk correction in closed form

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 630–635 (determinacy of the
log-linearised system) and Chapter 6 / Appendix E.2, p. 695 (the second-order expansion in the
amplitude of the shocks). Additions to `SmoothInSigma`.

* **Lags with `A + B + C` singular cannot occur under determinacy**: if the linearised operator
  `L h = A E_t h_{t+1} + B h_t + C h_{t−1}` is invertible on `ℓ∞` of the event tree, then
  `A + B + C` is injective (`injective_ABC_of_isInvertible`; the date-only tent sequences
  `tentSeq` are approximate kernel vectors of a unit root). Hence certainty equivalence
  `g_σ(ȳ, 0, 0) = 0` holds under determinacy and mean-zero innovations alone, with or without
  lags (`certainty_equivalence_det`, `certainty_equivalence_det_local`): there is no
  counterexample.
* The second-order equation in the state direction at `σ = 0` (`second_order_state`).
* The illustration `π_t = β E_t π_{t+1} + γ E_t π²_{t+1} + κ x_t` in closed form
  (`exModel_closed_form`): `g_π₋ = 0`, `g_x = κ/(1 − βρ)`, `g_σ = 0`,
  `g_xx = 2γρ²κ²/((1 − βρ)²(1 − βρ²))` and the risk correction
  `g_σσ = 2γκ²/((1 − β)(1 − βρ)²(1 − βρ²))`; supporting lemmas `exModel_fderiv_at`,
  `exModel_fderiv2`, `exModel_partials`, `exModel_solves_iff`, `exModel_lag_indep`,
  `fderiv_policy_lag_indep`.
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaCE

open Filter Topology
open SmoothInSigma SmoothInSigma.Model

/-! ## Tent sequences -/

/-- Woodford (2003), App. A.3, p. 632 (an approximate eigenvector for a unit root): the tent
`φ_N(t) = max(0, min(t, 2N − t))/N`, equal to `1` at `t = N`, `0` at `t = 0`, with increments
at most `1/N`. -/
noncomputable def tent (N t : ℕ) : ℝ := max 0 (min (t : ℝ) (2 * N - t)) / N

/-- Woodford (2003), App. A.3: `φ_N(0) = 0`. -/
theorem tent_zero (N : ℕ) : tent N 0 = 0 := by
  simp [tent]

/-- Woodford (2003), App. A.3: `φ_N(N) = 1` for `N ≥ 1`. -/
theorem tent_self {N : ℕ} (hN : 0 < N) : tent N N = 1 := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  have : min (N : ℝ) (2 * N - N) = N := by rw [min_eq_left (by linarith)]
  rw [tent, this, max_eq_right h.le, div_self h.ne']

/-- Woodford (2003), App. A.3: `0 ≤ φ_N ≤ 1`. -/
theorem tent_mem {N : ℕ} (hN : 0 < N) (t : ℕ) : 0 ≤ tent N t ∧ tent N t ≤ 1 := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨div_nonneg (le_max_left _ _) h.le, ?_⟩
  rw [tent, div_le_one h]
  refine max_le h.le ?_
  rcases le_total (t : ℝ) N with ht | ht
  · exact (min_le_left _ _).trans ht
  · exact (min_le_right _ _).trans (by linarith)

/-- Woodford (2003), App. A.3: the increments of the tent are at most `1/N`. -/
theorem abs_tent_succ_sub (N t : ℕ) : |tent N (t + 1) - tent N t| ≤ 1 / N := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · simp [tent, h0]
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tent, tent, ← sub_div, abs_div, abs_of_pos h]
  refine div_le_div_of_nonneg_right ?_ h.le
  rw [max_comm (0 : ℝ), max_comm (0 : ℝ)]
  refine (abs_max_sub_max_le_abs _ _ (0 : ℝ)).trans ?_
  refine (abs_min_sub_min_le_max (((t + 1 : ℕ) : ℝ)) (2 * N - ((t + 1 : ℕ) : ℝ)) (t : ℝ)
    (2 * N - t)).trans ?_
  push_cast
  refine max_le ?_ ?_ <;> rw [abs_le] <;> constructor <;> linarith


/-- Woodford (2003), App. A.3: `|φ_N| ≤ 1` for every `N` (also `N = 0`, where `φ_0 = 0`). -/
theorem abs_tent_le (N t : ℕ) : |tent N t| ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · simp [tent, h0]
  obtain ⟨h1, h2⟩ := tent_mem hN t
  rw [abs_of_nonneg h1]
  exact h2

/-! ## Determinacy excludes a unit root: `A + B + C` is injective -/

variable {J Y Z X E : Type} [Fintype J] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Model J Y Z X E}

omit [Fintype J] [FiniteDimensional ℝ Y] in
/-- Woodford (2003), App. A.3, p. 632: the tent sequence `n ↦ φ_N(t(n)) v` on the event tree, a
bounded process of sup norm `‖v‖` depending only on the date. -/
noncomputable def tentSeq (N : ℕ) (v : Y) : Bd (List J) Y :=
  mkBd (fun n => tent N n.length • v) ⟨‖v‖, fun n => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_tent_le N _)⟩

omit [Fintype J] [FiniteDimensional ℝ Y] in
/-- Woodford (2003), App. A.3: members of the tent sequence. -/
@[simp] theorem tentSeq_apply (N : ℕ) (v : Y) (n : List J) :
    tentSeq N v n = tent N n.length • v :=
  rfl

/-- Woodford (2003), App. A.3, p. 632 (**the tent is an approximate kernel vector**): if
`(A + B + C) v = 0` then `‖L(φ_N v)‖ ≤ (‖Av‖ + ‖Cv‖)/N`. -/
theorem norm_linOp_tentSeq_le (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar : Y} {v : Y}
    (hv : (M.dA ybar + M.dB ybar + M.dC ybar) v = 0) (N : ℕ) :
    ‖M.linOp hM ybar (tentSeq N v)‖ ≤ (‖M.dA ybar v‖ + ‖M.dC ybar v‖) / N := by
  have hB : M.dB ybar v = -M.dA ybar v - M.dC ybar v := by
    simp only [add_apply] at hv
    rw [← sub_eq_zero, ← hv]
    abel
  have hN : (0 : ℝ) ≤ 1 / N := by positivity
  refine norm_le_of_forall (by positivity) fun n => ?_
  rw [linOp_apply hM hf]
  have hsum : ∑ j, M.prob j • M.dA ybar ((tentSeq N v : Bd (List J) Y) (j :: n)) =
      tent N (n.length + 1) • M.dA ybar v := by
    simp only [tentSeq_apply, List.length_cons, map_smul, ← Finset.sum_smul, hM.prob_sum,
      one_smul]
  rw [hsum]
  cases n with
  | nil =>
    simp only [List.length_nil, zero_add, tentSeq_apply, tent_zero, zero_smul, map_zero,
      lagAt_nil, add_zero]
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := abs_tent_succ_sub N 0
    rw [tent_zero, sub_zero, zero_add] at h1
    calc |tent N 1| * ‖M.dA ybar v‖ ≤ 1 / N * ‖M.dA ybar v‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ (‖M.dA ybar v‖ + ‖M.dC ybar v‖) / N := by
          rw [one_div_mul_eq_div]
          exact div_le_div_of_nonneg_right (by linarith [norm_nonneg (M.dC ybar v)])
            (by positivity)
  | cons i m =>
    simp only [List.length_cons, tentSeq_apply, lagAt_cons, map_smul]
    rw [hB]
    have e : tent N (m.length + 1 + 1) • M.dA ybar v +
        tent N (m.length + 1) • (-M.dA ybar v - M.dC ybar v) + tent N m.length • M.dC ybar v =
        (tent N (m.length + 1 + 1) - tent N (m.length + 1)) • M.dA ybar v +
          (tent N m.length - tent N (m.length + 1)) • M.dC ybar v := by
      simp only [sub_smul, smul_sub, smul_neg]
      abel
    rw [e]
    have h1 := abs_tent_succ_sub N (m.length + 1)
    have h2 := abs_tent_succ_sub N m.length
    rw [abs_sub_comm] at h2
    calc ‖(tent N (m.length + 1 + 1) - tent N (m.length + 1)) • M.dA ybar v +
          (tent N m.length - tent N (m.length + 1)) • M.dC ybar v‖
        ≤ 1 / N * ‖M.dA ybar v‖ + 1 / N * ‖M.dC ybar v‖ := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
          rw [norm_smul, Real.norm_eq_abs] <;>
          exact mul_le_mul_of_nonneg_right (by assumption) (norm_nonneg _)
      _ = (‖M.dA ybar v‖ + ‖M.dC ybar v‖) / N := by ring

/-- Woodford (2003), App. A.3, eq. (A.9) (**determinacy excludes a unit root**): if the
linearised operator `L h = A E_t h_{t+1} + B h_t + C h_{t−1}` is invertible on `ℓ∞` of the
event tree, then the steady-state Jacobian `A + B + C` is injective. (Otherwise the tent
sequences `φ_N(t) v` with `(A + B + C) v = 0` would have `‖L(φ_N v)‖ = O(1/N)` while
`‖φ_N v‖ = ‖v‖`.) -/
theorem injective_ABC_of_isInvertible (hM : M.Std) (hf : ContDiff ℝ 1 M.f) {ybar : Y}
    (hL : (M.linOp hM ybar).IsInvertible) :
    Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar) := by
  intro a b hab
  set v := a - b with hvdef
  have hv : (M.dA ybar + M.dB ybar + M.dC ybar) v = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨j0⟩ : Nonempty J := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := hM.prob_sum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  set K := ‖(M.linOp hM ybar).inverse‖ * (‖M.dA ybar v‖ + ‖M.dC ybar v‖) with hK
  have key : ∀ N : ℕ, 0 < N → ‖v‖ ≤ K / N := fun N hN => by
    have h1 : ‖v‖ = ‖(tentSeq N v : Bd (List J) Y) (List.replicate N j0)‖ := by
      rw [tentSeq_apply, List.length_replicate, tent_self hN, one_smul]
    rw [h1]
    refine (norm_apply_le _ _).trans ?_
    rw [← hL.inverse_apply_self (tentSeq N v)]
    refine ((M.linOp hM ybar).inverse.le_opNorm _).trans ?_
    calc ‖(M.linOp hM ybar).inverse‖ * ‖M.linOp hM ybar (tentSeq N v)‖
        ≤ ‖(M.linOp hM ybar).inverse‖ * ((‖M.dA ybar v‖ + ‖M.dC ybar v‖) / N) :=
          mul_le_mul_of_nonneg_left (norm_linOp_tentSeq_le hM hf hv N) (norm_nonneg _)
      _ = K / N := by rw [hK, mul_div_assoc]
  have hv0 : ‖v‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨N, hN⟩ := exists_nat_gt (K / ‖v‖)
    have hN0 : 0 < N := by
      have : 0 ≤ K / ‖v‖ := div_nonneg (by positivity) hpos.le
      exact_mod_cast lt_of_le_of_lt this hN
    have h2 := key N hN0
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [div_lt_iff₀ hpos] at hN
    rw [le_div_iff₀ hNr] at h2
    linarith
  rw [norm_eq_zero, hvdef, sub_eq_zero] at hv0
  exact hv0

/-- Woodford (2003), App. E.2 (**certainty equivalence from determinacy alone**): with
mean-zero innovations, `g_σ(ȳ, 0, 0) = 0` whenever the linearised operator is invertible — the
hypothesis on `A + B + C` of `certainty_equivalence` is automatic, so there is no
counterexample with lags. -/
theorem certainty_equivalence_det [FiniteDimensional ℝ Z] (hM : M.Std) (hf : ContDiff ℝ 1 M.f)
    {ybar : Y} (hL : (M.linOp hM ybar).IsInvertible) {ψ : Y × X × ℝ → Bd (List J) Y}
    (hψ : M.LocalSol ybar ψ) {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) {g' : Y × X × ℝ →L[ℝ] Y}
    (hg : HasFDerivAt (policy ψ) g' (pbar ybar)) (hmean : ∑ j, M.prob j • M.shock j = 0) :
    g' (0, 0, 1) = 0 :=
  certainty_equivalence hM hf hψ hψd hg hmean (injective_ABC_of_isInvertible hM hf hL)

/-- Woodford (2003), App. A.3 and E.2 (**certainty equivalence from determinacy alone, `f`
smooth only near the steady state**): as `certainty_equivalence_det`, assuming only that `f` is
`C¹` at `z̄`. -/
theorem certainty_equivalence_det_local [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E]
    (hM : M.Std) {ybar : Y} (hf : ContDiffAt ℝ 1 M.f (zbar ybar))
    (hL : (M.linOp hM ybar).IsInvertible) {ψ : Y × X × ℝ → Bd (List J) Y}
    (hψ : M.LocalSol ybar ψ) {ψ' : Y × X × ℝ →L[ℝ] Bd (List J) Y}
    (hψd : HasFDerivAt ψ ψ' (pbar ybar)) {g' : Y × X × ℝ →L[ℝ] Y}
    (hg : HasFDerivAt (policy ψ) g' (pbar ybar)) (hmean : ∑ j, M.prob j • M.shock j = 0) :
    g' (0, 0, 1) = 0 := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt (M := M) (ybar := ybar) (k := 1)
    (by exact_mod_cast hf)
  have hinj' := injective_ABC_of_isInvertible (std_cutoff hM hr)
    (by exact_mod_cast contDiff_cutoff (M := M) hr hball) (by rw [linOp_cutoff hM hr]; exact hL)
  have hD := (fderiv_cutoff (M := M) hr (ybar := ybar)).1
  have hinj : Function.Injective (M.dA ybar + M.dB ybar + M.dC ybar) := by
    simpa only [dA, dB, dC, hD] using hinj'
  exact certainty_equivalence_local hM hf hψ hψd hg hmean hinj

/-! ## Second order in the state at `σ = 0` -/

/-- Woodford (2003), App. E.2, and the second-order perturbation equations (**the coefficient
`g_xx` on the exogenous state**): at the steady state, with `a = g′(0, x, 0)` and
`b = g′(a, Λx, 0)`,
`A g″((a, Λx, 0), (a, Λx, 0)) + A G_y g″((0,x,0),(0,x,0)) + B g″((0,x,0),(0,x,0)) +
D²f(z̄)((b, a, 0, x, 0), (b, a, 0, x, 0)) = 0`. -/
theorem second_order_state [FiniteDimensional ℝ Z] (hM : M.Std) (hf : ContDiff ℝ 2 M.f)
    {ybar : Y} {ψ : Y × X × ℝ → Bd (List J) Y} (hψ : M.LocalSol ybar ψ)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) (x : X) :
    M.dA ybar (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar)
        (fderiv ℝ (policy ψ) (pbar ybar) (0, x, 0), M.Λ x, 0)
        (fderiv ℝ (policy ψ) (pbar ybar) (0, x, 0), M.Λ x, 0)) +
      M.dA ybar (fderiv ℝ (policy ψ) (pbar ybar)
        (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, x, 0) (0, x, 0), 0, 0)) +
      M.dB ybar (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) (0, x, 0) (0, x, 0)) +
      fderiv ℝ (fderiv ℝ M.f) (zbar ybar)
        (fderiv ℝ (policy ψ) (pbar ybar) (fderiv ℝ (policy ψ) (pbar ybar) (0, x, 0), M.Λ x, 0),
          fderiv ℝ (policy ψ) (pbar ybar) (0, x, 0), 0, x, 0)
        (fderiv ℝ (policy ψ) (pbar ybar) (fderiv ℝ (policy ψ) (pbar ybar) (0, x, 0), M.Λ x, 0),
          fderiv ℝ (policy ψ) (pbar ybar) (0, x, 0), 0, x, 0) = 0 := by
  obtain ⟨e3, he3⟩ : ∃ e3 : Y × X × ℝ, e3 = (0, x, 0) := ⟨_, rfl⟩
  rw [← he3]
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (pbar ybar)) (pbar ybar) :=
    (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hψev : ∀ᶠ p in 𝓝 (pbar ybar), HasFDerivAt ψ (fderiv ℝ ψ p) p :=
    (hψ2.eventually (by simp)).mono fun p hp => (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hψF1 : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (pbar ybar)) (pbar ybar) :=
    ((hψ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hg2 : ContDiffAt ℝ 2 (policy ψ) (pbar ybar) :=
    (evalL Y []).contDiff.contDiffAt.comp (pbar ybar) hψ2
  have hgd : HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) (pbar ybar)) (pbar ybar) :=
    (hg2.differentiableAt (by norm_num)).hasFDerivAt
  have hgev : ∀ᶠ p in 𝓝 (pbar ybar), HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) p) p :=
    (hg2.eventually (by simp)).mono fun p hp => (hp.differentiableAt (by norm_num)).hasFDerivAt
  have hgF1 : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar))
      (pbar ybar) :=
    ((hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hfd : ∀ z, HasFDerivAt M.f (fderiv ℝ M.f z) z := fun z =>
    (hf.differentiable (by norm_num) z).hasFDerivAt
  have hfF1 : HasFDerivAt (fderiv ℝ M.f) (fderiv ℝ (fderiv ℝ M.f) (zbar ybar)) (zbar ybar) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _).hasFDerivAt
  have hg'eq : fderiv ℝ (policy ψ) (pbar ybar) = (evalL Y []).comp (fderiv ℝ ψ (pbar ybar)) :=
    hgd.unique ((evalL Y []).hasFDerivAt.comp (pbar ybar) hψd)
  have hsm : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (v : V) (s : ℝ),
      HasDerivAt (fun s : ℝ => s • v) v s := fun v s => by
    simpa using (hasDerivAt_id s).smul_const v
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ → Y × X × ℝ, γ = fun s => (ybar, s • x, 0) := ⟨_, rfl⟩
  have hγd : ∀ s, HasDerivAt γ e3 s := fun s => by
    rw [hγ, he3]
    exact (hasDerivAt_const s ybar).prodMk ((hsm x s).prodMk (hasDerivAt_const s (0 : ℝ)))
  have hγ0 : γ 0 = pbar ybar := by rw [hγ]; simp [pbar]
  have hγt : Tendsto γ (𝓝 0) (𝓝 (pbar ybar)) := hγ0 ▸ (hγd 0).continuousAt.tendsto
  obtain ⟨u, hu⟩ : ∃ u : ℝ → Bd (List J) Y, u = fun s => ψ (γ s) := ⟨_, rfl⟩
  obtain ⟨u1, hu1⟩ : ∃ u1 : ℝ → Bd (List J) Y, u1 = fun s => fderiv ℝ ψ (γ s) e3 := ⟨_, rfl⟩
  obtain ⟨u2, hu2⟩ : ∃ u2 : Bd (List J) Y, u2 = fderiv ℝ (fderiv ℝ ψ) (pbar ybar) e3 e3 :=
    ⟨_, rfl⟩
  have hud : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt u (u1 s) s := by
    rw [hu, hu1]
    filter_upwards [hγt.eventually hψev] with s hs
    exact hs.comp_hasDerivAt s (hγd s)
  have hu1d : HasDerivAt u1 u2 0 := by
    have hF : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) (pbar ybar)) (γ 0) := by
      rw [hγ0]; exact hψF1
    have h1 := (ContinuousLinearMap.apply ℝ (Bd (List J) Y) e3).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (hF.comp_hasDerivAt (0 : ℝ) (hγd 0))
    rw [hu1, hu2]
    exact h1
  have hun : ∀ n, ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s => u s n) (u1 s n) s := fun n =>
    hud.mono fun s hs => (evalL Y n).hasFDerivAt.comp_hasDerivAt s hs
  have hun1 : ∀ n, HasDerivAt (fun s => u1 s n) (u2 n) 0 := fun n =>
    (evalL Y n).hasFDerivAt.comp_hasDerivAt 0 hu1d
  have hu0 : u 0 = constBd ybar := by rw [hu]; simp only [hγ0]; exact hψ.base
  have hu10 : u1 0 = fderiv ℝ ψ (pbar ybar) e3 := by rw [hu1]; simp only [hγ0]
  have hR0 : u2 [] = fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar) e3 e3 := by
    have hF : ∀ᶠ z in 𝓝 (γ 0), HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) z) z := by
      rw [hγ0]; exact hgev
    have hF1 : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar))
        (γ 0) := by rw [hγ0]; exact hgF1
    have := secondDeriv_comp (F := policy ψ) (a := γ) (a1 := fun _ => e3) (a2 := 0)
      (y := fun s => u s []) (y1 := fun s => u1 s []) hF hF1 (Eventually.of_forall hγd)
      (hasDerivAt_const 0 e3) (hun []) (hun1 [])
      (Eventually.of_forall fun s => by rw [hu]; rfl)
    rw [this, map_zero, add_zero]
  have h1root : u1 0 [] = fderiv ℝ (policy ψ) (pbar ybar) e3 := by
    rw [hu10, hg'eq]
    rfl
  have h1child : ∀ j, u1 0 [j] =
      fderiv ℝ (policy ψ) (pbar ybar) (fderiv ℝ (policy ψ) (pbar ybar) e3, M.Λ x, 0) :=
    fun j => by
      have h := markov_deriv hM hψ hψd e3 [j]
      rw [← hg'eq, ← hu10, he3] at h
      simp only [lagAt_cons, stateAt_cons, stateAt_nil, zero_smul, add_zero] at h
      rw [h1root, he3] at h
      rw [he3]
      exact h
  have hRj : ∀ j, u2 [j] = fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar)
      (fderiv ℝ (policy ψ) (pbar ybar) e3, M.Λ x, 0)
      (fderiv ℝ (policy ψ) (pbar ybar) e3, M.Λ x, 0) +
      fderiv ℝ (policy ψ) (pbar ybar) (u2 [], 0, 0) := fun j => by
    obtain ⟨b, hb⟩ : ∃ b : ℝ → Y × X × ℝ, b = fun s => (u s [], s • M.Λ x, 0) := ⟨_, rfl⟩
    have hb0 : b 0 = pbar ybar := by
      rw [hb]
      change (u 0 [], (0 : ℝ) • M.Λ x, (0 : ℝ)) = pbar ybar
      rw [hu0, zero_smul]
      rfl
    have hF : ∀ᶠ z in 𝓝 (b 0), HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) z) z := by
      rw [hb0]; exact hgev
    have hF1 : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar ybar))
        (b 0) := by rw [hb0]; exact hgF1
    have ha : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt b (u1 s [], M.Λ x, 0) s := by
      rw [hb]
      exact (hun []).mono fun s hs => hs.prodMk ((hsm _ s).prodMk (hasDerivAt_const s _))
    have ha1 : HasDerivAt (fun s => (u1 s [], M.Λ x, (0 : ℝ))) (u2 [], 0, 0) 0 :=
      (hun1 []).prodMk ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _))
    have heq : ∀ᶠ s in 𝓝 (0 : ℝ), u s [j] = policy ψ (b s) := by
      filter_upwards [hγt.eventually (markov hM hψ)] with s hs
      have h := hs [j]
      rw [hγ] at h
      simp only [lagAt_cons, stateAt_cons, stateAt_nil, zero_smul, add_zero, map_smul] at h
      rw [hb, hu, hγ]
      exact h
    have := secondDeriv_comp hF hF1 ha ha1 (hun [j]) (hun1 [j]) heq
    rw [this, hb0, hu10, hg'eq]
    rfl
  have hEq := secondDeriv_sum_comp (F := M.f) (F1 := fderiv ℝ M.f)
    (F2 := fun _ => fderiv ℝ (fderiv ℝ M.f) (zbar ybar)) (c := M.prob)
    (a := fun j s => (u s [j], u s [], ybar, s • x, (0 : ℝ) • M.shock j))
    (a1 := fun j s => (u1 s [j], u1 s [], (0 : Y), x, (0 : E)))
    (a2 := fun j => (u2 [j], u2 [], (0 : Y), (0 : X), (0 : E)))
    (fun _ => Eventually.of_forall hfd)
    (fun j => by
      rw [hu0, constBd_apply, constBd_apply, zero_smul, zero_smul]
      exact hfF1)
    (fun j => ((hun [j]).and (hun [])).mono fun s hs => hs.1.prodMk (hs.2.prodMk
      ((hasDerivAt_const s ybar).prodMk ((hsm x s).prodMk (hasDerivAt_const s _)))))
    (fun j => (hun1 [j]).prodMk ((hun1 []).prodMk ((hasDerivAt_const _ _).prodMk
      ((hasDerivAt_const _ _).prodMk (hasDerivAt_const _ _)))))
    (by
      filter_upwards [hγt.eventually hψ.solves] with s hs
      have h := hs []
      rw [hγ] at h
      simp only [bigF, ell_apply, point, lagAt_nil, stateAt_nil] at h
      rw [hu, hγ]
      exact h)
  simp only [hu0, constBd_apply, zero_smul] at hEq
  rw [show ((ybar, ybar, ybar, 0, 0) : Y × Y × Y × X × E) = zbar ybar from rfl] at hEq
  simp only [h1child, fderiv_f_apply, map_zero, add_zero, hRj, h1root, hR0] at hEq
  simp only [← Finset.sum_smul, hM.prob_sum, one_smul, map_add] at hEq
  rw [← hEq]
  abel

/-! ## The illustration: the risk correction in closed form -/

/-- Woodford (2003), the illustration `exModel`: the derivative of the period condition at any
point, `Df(z)(w) = w₂ − β w₁ − 2γ z₁ w₁ − κ w₄`. -/
theorem exModel_fderiv_at (β γ κ ρ : ℝ) (z w : ℝ × ℝ × ℝ × ℝ × ℝ) :
    fderiv ℝ (exModel β γ κ ρ).f z w = w.2.1 - β * w.1 - 2 * γ * z.1 * w.1 - κ * w.2.2.2.1 := by
  have hd : HasFDerivAt (exModel β γ κ ρ).f (fderiv ℝ (exModel β γ κ ρ).f z) z :=
    ((exModel_contDiff β γ κ ρ (k := 1)).differentiable one_ne_zero _).hasFDerivAt
  have hl : HasDerivAt (fun a : ℝ => z + a • w) w 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z).congr_deriv (one_smul ℝ w)
  have hd' : HasFDerivAt (exModel β γ κ ρ).f (fderiv ℝ (exModel β γ κ ρ).f z)
      ((fun a : ℝ => z + a • w) 0) := by
    simp only [zero_smul, add_zero]
    exact hd
  have h1 := hd'.comp_hasDerivAt (0 : ℝ) hl
  have e : ((exModel β γ κ ρ).f ∘ fun a : ℝ => z + a • w) = fun a =>
      (z.2.1 + a * w.2.1) - β * (z.1 + a * w.1) - γ * (z.1 + a * w.1) ^ 2 -
        κ * (z.2.2.2.1 + a * w.2.2.2.1) := by
    funext a
    simp only [Function.comp, exModel, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
  rw [e] at h1
  have h2 : HasDerivAt (fun a : ℝ => (z.2.1 + a * w.2.1) - β * (z.1 + a * w.1) -
      γ * (z.1 + a * w.1) ^ 2 - κ * (z.2.2.2.1 + a * w.2.2.2.1))
      (w.2.1 - β * w.1 - 2 * γ * z.1 * w.1 - κ * w.2.2.2.1) 0 := by
    have hlin : ∀ c d : ℝ, HasDerivAt (fun a : ℝ => c + a * d) d 0 := fun c d => by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c
    have := (((hlin z.2.1 w.2.1).sub ((hlin z.1 w.1).const_mul β)).sub
      (((hlin z.1 w.1).pow 2).const_mul γ)).sub ((hlin z.2.2.2.1 w.2.2.2.1).const_mul κ)
    convert this using 1
    simp
    ring
  exact h1.unique h2

/-- Woodford (2003), the illustration: the second derivative of the period condition at the
steady state, `D²f(z̄)(v, w) = −2γ v₁ w₁`. -/
theorem exModel_fderiv2 (β γ κ ρ : ℝ) (v w : ℝ × ℝ × ℝ × ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (exModel β γ κ ρ).f) (zbar 0) v w = -2 * γ * v.1 * w.1 := by
  have hD : HasFDerivAt (fderiv ℝ (exModel β γ κ ρ).f)
      (fderiv ℝ (fderiv ℝ (exModel β γ κ ρ).f) (zbar 0)) (zbar 0) :=
    (((exModel_contDiff β γ κ ρ (k := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) _).hasFDerivAt
  have hl : HasDerivAt (fun a : ℝ => zbar 0 + a • v) v 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (zbar 0)).congr_deriv (one_smul ℝ v)
  have hD' : HasFDerivAt (fderiv ℝ (exModel β γ κ ρ).f)
      (fderiv ℝ (fderiv ℝ (exModel β γ κ ρ).f) (zbar 0)) ((fun a : ℝ => zbar 0 + a • v) 0) := by
    simp only [zero_smul, add_zero]
    exact hD
  have h1 := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hD'.comp_hasDerivAt (0 : ℝ) hl)
  have e : (⇑(ContinuousLinearMap.apply ℝ ℝ w) ∘ (fderiv ℝ (exModel β γ κ ρ).f ∘
      fun a : ℝ => zbar 0 + a • v)) = fun a =>
      w.2.1 - β * w.1 - 2 * γ * (a * v.1) * w.1 - κ * w.2.2.2.1 := by
    funext a
    simp only [Function.comp, ContinuousLinearMap.apply_apply, exModel_fderiv_at, zbar,
      Prod.fst_add, Prod.smul_fst, smul_eq_mul, zero_add]
  rw [e] at h1
  have h2 : HasDerivAt (fun a : ℝ => w.2.1 - β * w.1 - 2 * γ * (a * v.1) * w.1 - κ * w.2.2.2.1)
      (-2 * γ * v.1 * w.1) 0 := by
    have := ((((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_mul (2 * γ)).mul_const w.1).const_sub
      (w.2.1 - β * w.1)
    have h3 := this.sub_const (κ * w.2.2.2.1)
    convert h3 using 1
    · funext a
      simp only [id]
    · ring
  have := h1.unique h2
  simpa using this

/-- Woodford (2003), the illustration: the equilibrium conditions do not involve the lagged
decision, so they are the same for every initial lag. -/
theorem exModel_solves_iff (β γ κ ρ : ℝ) (u : List Bool → ℝ) (a a' x σ : ℝ) :
    (exModel β γ κ ρ).Solves u (a, x, σ) ↔ (exModel β γ κ ρ).Solves u (a', x, σ) :=
  Iff.rfl

/-- Woodford (2003), the illustration: near the steady state the local equilibrium does not
depend on the initial lag. -/
theorem exModel_lag_indep {β γ κ ρ : ℝ} {ψ : ℝ × ℝ × ℝ → Bd (List Bool) ℝ}
    (hψ : (exModel β γ κ ρ).LocalSol 0 ψ) :
    ∀ᶠ p in 𝓝 (pbar (0 : ℝ) : ℝ × ℝ × ℝ), ψ p = ψ (0, p.2) := by
  obtain ⟨δ, hδ, huniq⟩ := hψ.unique
  have hball : ∀ᶠ p in 𝓝 (pbar (0 : ℝ) : ℝ × ℝ × ℝ), dist (ψ p) (constBd 0) < δ := by
    have := hψ.cont.tendsto
    rw [hψ.base] at this
    exact this (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hψ.solves, hball, Metric.ball_mem_nhds (pbar (0 : ℝ) : ℝ × ℝ × ℝ) hδ] with
    p hs hd hp
  have hp' : dist ((0 : ℝ), p.2) (pbar (0 : ℝ) : ℝ × ℝ × ℝ) < δ := by
    rw [Metric.mem_ball] at hp
    refine lt_of_le_of_lt ?_ hp
    have e1 : dist ((0 : ℝ), p.2) (pbar (0 : ℝ) : ℝ × ℝ × ℝ) =
        dist p.2 (pbar (0 : ℝ) : ℝ × ℝ × ℝ).2 := by simp [Prod.dist_eq, pbar]
    rw [e1, Prod.dist_eq (x := p)]
    exact le_max_right _ _
  exact (huniq _ _ hp' hd ((exModel_solves_iff β γ κ ρ _ p.1 0 p.2.1 p.2.2).1 hs)).symm

/-- Woodford (2003), the illustration: if a local equilibrium does not depend on the initial lag,
neither do the first and second derivatives of its policy function,
`g′(v) = g′(0, v_x, v_σ)` and `g″(v, w) = g″((0, v_x, v_σ), (0, w_x, w_σ))`. -/
theorem fderiv_policy_lag_indep {ψ : ℝ × ℝ × ℝ → Bd (List Bool) ℝ}
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar (0 : ℝ) : ℝ × ℝ × ℝ))
    (hind : ∀ᶠ p in 𝓝 (pbar (0 : ℝ) : ℝ × ℝ × ℝ), ψ p = ψ (0, p.2)) :
    (∀ v, fderiv ℝ (policy ψ) (pbar 0) v = fderiv ℝ (policy ψ) (pbar 0) (0, v.2)) ∧
      ∀ v w, fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0) v w =
        fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0) (0, v.2) (0, w.2) := by
  set P : ℝ × ℝ × ℝ →L[ℝ] ℝ × ℝ × ℝ :=
    (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) with hP
  have hPa : ∀ q, P q = (0, q.2) := fun q => rfl
  have hP0 : P (pbar 0) = pbar 0 := rfl
  have hg2 : ContDiffAt ℝ 2 (policy ψ) (pbar 0) :=
    (evalL ℝ []).contDiff.contDiffAt.comp (pbar 0) hψ2
  have hgev : ∀ᶠ q in 𝓝 (pbar (0 : ℝ) : ℝ × ℝ × ℝ),
      HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) q) q :=
    (hg2.eventually (by simp)).mono fun q hq => (hq.differentiableAt (by norm_num)).hasFDerivAt
  have hgF1 : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0))
      (pbar (0 : ℝ) : ℝ × ℝ × ℝ) :=
    ((hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hgP : policy ψ =ᶠ[𝓝 (pbar (0 : ℝ) : ℝ × ℝ × ℝ)] policy ψ ∘ P := by
    filter_upwards [hind] with p hp
    simp only [Function.comp, hPa, policy, hp]
  have hPt : Tendsto P (𝓝 (pbar (0 : ℝ) : ℝ × ℝ × ℝ)) (𝓝 (pbar 0)) := by
    have := P.continuous.tendsto (pbar (0 : ℝ) : ℝ × ℝ × ℝ)
    rwa [hP0] at this
  -- first derivative
  have h1 : fderiv ℝ (policy ψ) (pbar 0) = (fderiv ℝ (policy ψ) (pbar 0)).comp P := by
    conv_lhs => rw [hgP.fderiv_eq]
    have hd : HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) (pbar 0)) (P (pbar 0)) := by
      rw [hP0]; exact hgev.self_of_nhds
    exact (hd.comp (pbar 0) P.hasFDerivAt).fderiv
  -- second derivative
  have hev : fderiv ℝ (policy ψ) =ᶠ[𝓝 (pbar (0 : ℝ) : ℝ × ℝ × ℝ)]
      fun q => (fderiv ℝ (policy ψ) (P q)).comp P := by
    filter_upwards [hgP.eventually_nhds, hPt.eventually hgev] with q hq hdq
    rw [(show policy ψ =ᶠ[𝓝 q] policy ψ ∘ P from hq).fderiv_eq]
    exact (hdq.comp q P.hasFDerivAt).fderiv
  set R : (ℝ × ℝ × ℝ →L[ℝ] ℝ) →L[ℝ] (ℝ × ℝ × ℝ →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) ℝ).flip P with hR
  have hRa : ∀ L, R L = L.comp P := fun L => rfl
  have hF : HasFDerivAt (fderiv ℝ (policy ψ)) (fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0))
      (P (pbar 0)) := by rw [hP0]; exact hgF1
  have hd2 : HasFDerivAt (fun q => (fderiv ℝ (policy ψ) (P q)).comp P)
      (R.comp ((fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0)).comp P)) (pbar 0) :=
    R.hasFDerivAt.comp (pbar 0) (hF.comp (pbar 0) P.hasFDerivAt)
  have h2 : fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0) =
      R.comp ((fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0)).comp P) := by
    conv_lhs => rw [hev.fderiv_eq]
    exact hd2.fderiv
  refine ⟨fun v => ?_, fun v w => ?_⟩
  · conv_lhs => rw [h1]
    rfl
  · conv_lhs => rw [h2]
    rfl

/-- Woodford (2003), the illustration: the steady-state partial derivatives,
`A = −β`, `B = 1`, `C = 0`, `f_x = −κ`. -/
theorem exModel_partials (β γ κ ρ a : ℝ) :
    (exModel β γ κ ρ).dA 0 a = -(β * a) ∧ (exModel β γ κ ρ).dB 0 a = a ∧
      (exModel β γ κ ρ).dC 0 a = 0 ∧ (exModel β γ κ ρ).dX 0 a = -(κ * a) := by
  simp only [dA, dB, dC, dX, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, exModel_fderiv]
  refine ⟨by simp, by simp, by simp, by simp⟩

/-- Woodford (2003), the illustration (**the decision rule in closed form to second order**):
for `π_t = β E_t π_{t+1} + γ E_t π_{t+1}² + κ x_t`, `x_{t+1} = ρ x_t + σ ε_{t+1}`,
`ε = ±1` equally likely, `|β|, |ρ| < 1`, the local equilibrium policy `g(π_{−1}, x, σ)` has
`g_π₋ = 0`, `g_x = κ/(1 − βρ)`, `g_σ = 0`, `g_xx = 2γρ²κ²/((1 − βρ)²(1 − βρ²))` and the risk
correction `g_σσ = 2γκ²/((1 − β)(1 − βρ)²(1 − βρ²))`. -/
theorem exModel_closed_form {β γ κ ρ : ℝ} (hρ : |ρ| < 1) (hβ : |β| < 1)
    {ψ : ℝ × ℝ × ℝ → Bd (List Bool) ℝ} (hψ : (exModel β γ κ ρ).LocalSol 0 ψ)
    (hψ2 : ContDiffAt ℝ 2 ψ (pbar 0)) :
    fderiv ℝ (policy ψ) (pbar 0) (1, 0, 0) = 0 ∧
      fderiv ℝ (policy ψ) (pbar 0) (0, 1, 0) = κ / (1 - β * ρ) ∧
      fderiv ℝ (policy ψ) (pbar 0) (0, 0, 1) = 0 ∧
      fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0) (0, 1, 0) (0, 1, 0) =
        2 * γ * ρ ^ 2 * κ ^ 2 / ((1 - β * ρ) ^ 2 * (1 - β * ρ ^ 2)) ∧
      fderiv ℝ (fderiv ℝ (policy ψ)) (pbar 0) (0, 0, 1) (0, 0, 1) =
        2 * γ * κ ^ 2 / ((1 - β) * (1 - β * ρ) ^ 2 * (1 - β * ρ ^ 2)) := by
  have hM := exModel_std (β := β) (γ := γ) (κ := κ) hρ
  have hf := exModel_contDiff β γ κ ρ (k := 2)
  have hf1 := exModel_contDiff β γ κ ρ (k := 1)
  have hL := exModel_det (γ := γ) (κ := κ) hρ hβ
  obtain ⟨h1, h2⟩ := fderiv_policy_lag_indep hψ2 (exModel_lag_indep hψ)
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (pbar 0)) (pbar 0) :=
    (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hg2 : ContDiffAt ℝ 2 (policy ψ) (pbar 0) :=
    (evalL ℝ []).contDiff.contDiffAt.comp (pbar 0) hψ2
  have hgd : HasFDerivAt (policy ψ) (fderiv ℝ (policy ψ) (pbar 0)) (pbar 0) :=
    (hg2.differentiableAt (by norm_num)).hasFDerivAt
  set D1 := fderiv ℝ (policy ψ) (pbar (0 : ℝ) : ℝ × ℝ × ℝ) with hD1
  set D2 := fderiv ℝ (fderiv ℝ (policy ψ)) (pbar (0 : ℝ) : ℝ × ℝ × ℝ) with hD2
  set Gx := D1 (0, 1, 0) with hGx
  set gxx := D2 (0, 1, 0) (0, 1, 0) with hgxx
  set gss := D2 (0, 0, 1) (0, 0, 1) with hgss
  have hβρ : β * ρ < 1 := by
    have : |β * ρ| < 1 := by
      rw [abs_mul]
      nlinarith [abs_nonneg β, abs_nonneg ρ]
    linarith [le_abs_self (β * ρ)]
  have hβρ2 : β * ρ ^ 2 < 1 := by
    have : |ρ| ^ 2 < 1 := by nlinarith [abs_nonneg ρ]
    have h3 : |β * ρ ^ 2| < 1 := by
      rw [abs_mul, abs_pow]
      nlinarith [abs_nonneg β, abs_nonneg ρ, sq_nonneg |ρ|]
    linarith [le_abs_self (β * ρ ^ 2)]
  have hβ1 : β < 1 := (abs_lt.1 hβ).2
  -- linearity of `g′` and `g″` in the state direction
  have hD1x : ∀ x : ℝ, D1 (0, x, 0) = x * Gx := fun x => by
    rw [hGx, show ((0 : ℝ), x, (0 : ℝ)) = x • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) by simp, map_smul,
      smul_eq_mul]
  have hD2x : ∀ x : ℝ, D2 (0, x, 0) (0, x, 0) = x ^ 2 * gxx := fun x => by
    rw [hgxx, show ((0 : ℝ), x, (0 : ℝ)) = x • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) by simp, map_smul,
      map_smul]
    simp only [smul_apply, smul_eq_mul]
    ring
  -- `g_π₋ = 0`
  have hGy : ∀ a : ℝ, D1 (a, 0, 0) = 0 := fun a => by
    rw [h1, show (((0 : ℝ), ((a, (0 : ℝ), (0 : ℝ)) : ℝ × ℝ × ℝ).2) : ℝ × ℝ × ℝ) = 0 from rfl,
      map_zero]
  -- `g_x`
  have hfs := first_order_state hM hf1 hψ hψd hgd (1 : ℝ)
  have hΛ : ∀ x : ℝ, (exModel β γ κ ρ).Λ x = ρ * x := fun x => by simp [exModel]
  rw [hΛ, mul_one] at hfs
  have hρGx : D1 (D1 (0, 1, 0), ρ, 0) = ρ * Gx := by
    rw [h1, hD1x]
  simp only [← hGx] at hfs
  rw [hρGx] at hfs
  have hp := fun a => exModel_partials β γ κ ρ a
  rw [(hp _).1, (hp _).2.1, (hp _).2.2.2] at hfs
  have hGxv : Gx = κ / (1 - β * ρ) := by
    rw [eq_div_iff (by linarith)]
    linarith
  -- `g_σ = 0`
  have hce : D1 (0, 0, 1) = 0 := certainty_equivalence_det hM hf1 hL hψ hψd hgd
    (exModel_mean β γ κ ρ)
  -- `g_xx`
  have hss := second_order_state hM hf hψ hψ2 (1 : ℝ)
  simp only [← hD1, ← hD2, ← hGx, ← hgxx, hΛ, mul_one] at hss
  rw [hρGx, h2, h1] at hss
  simp only [hD2x, exModel_fderiv2, hD1x, (hp _).1, (hp _).2.1] at hss
  have hgxxv : gxx = 2 * γ * ρ ^ 2 * Gx ^ 2 / (1 - β * ρ ^ 2) := by
    rw [eq_div_iff (by linarith)]
    linear_combination hss
  -- `g_σσ`
  have hinj := injective_ABC_of_isInvertible hM hf1 hL
  have hso := second_order_sigma hM hf hψ hψ2 (exModel_mean β γ κ ρ) hinj
  simp only [← hD1, ← hD2, ← hgss, Fintype.sum_bool] at hso
  have hη : ∀ b : Bool, (exModel β γ κ ρ).η ((exModel β γ κ ρ).shock b) =
      if b then 1 else -1 := fun b => by simp [exModel]
  have hprob : ∀ b : Bool, (exModel β γ κ ρ).prob b = 1 / 2 := fun _ => rfl
  simp only [hη, Bool.false_eq_true, ↓reduceIte, hGy, hD2x, hD1x, exModel_fderiv2,
    (hp _).1, (hp _).2.1, hprob, smul_eq_mul] at hso
  have hgssv : gss = (β * gxx + 2 * γ * Gx ^ 2) / (1 - β) := by
    rw [eq_div_iff (by linarith)]
    linear_combination hso
  have hd1 : (1 - β * ρ) ≠ 0 := by linarith
  have hd2 : (1 - β * ρ ^ 2) ≠ 0 := by linarith
  have hd3 : (1 - β) ≠ 0 := by linarith
  refine ⟨?_, hGxv, hce, ?_, ?_⟩
  · rw [hGy]
  · rw [hgxxv, hGxv]
    field_simp
  · rw [hgssv, hgxxv, hGxv]
    field_simp
    ring

end Woodford.StabilizationWelfare.SmoothInSigmaCE
