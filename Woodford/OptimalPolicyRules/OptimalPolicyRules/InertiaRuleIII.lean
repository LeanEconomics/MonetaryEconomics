/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaSplit

/-!
# Rule III and the non-uniqueness of `Λ` in Proposition 8.1

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.1 (p. 553), Proposition 8.3
(pp. 556–557) and Rule III (3.24), p. 595.

`InertiaSplit.split_not_ruleIII` shows that no deflating split of the inertia model has Rule
III's lag polynomial `(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)`. This module shows that the homogeneous content
of Proposition 8.1 — the equivalence of the homogeneous (1.18) with the homogeneous
(1.20)–(1.21) on bounded sequences, which is all that Proposition 8.3 uses — does not pin `Λ`
down: the unstable eigenvalue may be moved to any `ν` with `|ν| > 1`.

## Main results

* `homEquiv_modify`: if `(Λ − λ_b)(Λ − λ₁) = 0`, `λ₁ ≠ λ_b`, `|λ_b| > 1` and `|ν| > 1`, then
  `Λ' = Λ + ((ν − λ_b)/(λ_b − λ₁))(Λ − λ₁I)` (which replaces the eigenvalue `λ_b` by `ν`) has the
  same bounded homogeneous solutions: `HomEquiv S β Λ Υ → HomEquiv S β Λ' Υ`.
* `alpha_modify`: for `2 × 2` `Λ` with eigenvalues `λ₁, λ_b`, `α'(L) = (1 − λ₁L)(1 − νL)`.
* `ruleIII_homEquiv`: **for the inertia model in the real case, Rule III's lag polynomial is
  `det(I − Λ'L)` for a matrix `Λ'` satisfying the homogeneous Proposition 8.1 equivalence**
  (built from the Rule I split with `ν = S/2`). So Rule III is excluded only for the `Λ` of a
  deflating split (`InertiaSplit.split_not_ruleIII`), not by Proposition 8.1's homogeneous
  equivalence or by Proposition 8.3.
-/

namespace Woodford.OptimalPolicyRules.InertiaRuleIII

open Matrix Polynomial GeneralSetup Adjugate PencilSplit
open IRuleBasic (Calib)
open CubicRoots
open GeneralLinksInertia (inSys inProblem in_det_ne)
open InertiaSplit (inJ quadQ inSplit standing_of)
open GeneralFOC.LQ (Mpart)

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 556 (tool): a bounded sequence `u_{t+1} = a u_t` with `|a| > 1`
vanishes. -/
theorem eq_zero_of_bdd_geom {a : ℝ} (ha : 1 < |a|) {u : ℕ → ιz → ℝ}
    (hb : ∃ C, ∀ t i, |u t i| ≤ C) (hu : ∀ t, u (t + 1) = a • u t) : ∀ t, u t = 0 := by
  obtain ⟨C, hC⟩ := hb
  have hpow : ∀ t, u t = a ^ t • u 0 := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hu n, ih, smul_smul, pow_succ, mul_comm]
  have h0 : u 0 = 0 := by
    funext i
    by_contra hne
    have hpos : 0 < |u 0 i| := abs_pos.mpr hne
    have htend : Filter.Tendsto (fun t : ℕ => |a| ^ t * |u 0 i|) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt ha).atTop_mul_const hpos
    obtain ⟨t, ht⟩ := (htend.eventually_gt_atTop C).exists
    have := hC t i
    rw [hpow t, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow] at this
    linarith
  intro t
  rw [hpow t, h0, smul_zero]

/-- **Woodford (2003), Proposition 8.1, p. 553: `Λ` is not determined by the homogeneous
equivalence.** If `(Λ − λ_bI)(Λ − λ₁I) = 0` with `λ₁ ≠ λ_b`, `|λ_b| > 1`, then for every `ν` with
`|ν| > 1` the matrix `Λ' = Λ + c(Λ − λ₁I)`, `c = (ν − λ_b)/(λ_b − λ₁)`, has the same bounded
homogeneous solutions of (1.20)–(1.21) as `Λ`. (On the range of `Λ − λ₁I`, `Λ` acts as `λ_b` and
`Λ'` as `ν`; bounded orbits never enter it.) -/
theorem homEquiv_modify {S : LinearRESystem ιZ ιz} {β : ℝ} {Λ : Matrix ιz ιz ℝ}
    {Υ : Matrix ιZ ιz ℝ} (hE : Prop83.HomEquiv S β Λ Υ) {l1 lb ν : ℝ}
    (hmin : (Λ - lb • (1 : Matrix ιz ιz ℝ)) * (Λ - l1 • (1 : Matrix ιz ιz ℝ)) = 0)
    (h1b : l1 ≠ lb) (hb : 1 < |lb|) (hν : 1 < |ν|) :
    Prop83.HomEquiv S β (Λ + ((ν - lb) / (lb - l1)) • (Λ - l1 • (1 : Matrix ιz ιz ℝ))) Υ := by
  set c := (ν - lb) / (lb - l1) with hc
  set N := Λ - l1 • (1 : Matrix ιz ιz ℝ) with hN
  have hsub : lb - l1 ≠ 0 := sub_ne_zero.mpr h1b.symm
  -- `Λ N = λ_b N`, and `N` commutes with `Λ`
  have hΛN : Λ * N = lb • N := by
    have := hmin
    rw [sub_mul, smul_mul_assoc, Matrix.one_mul, sub_eq_zero] at this
    exact this
  have hNΛ : N * Λ = Λ * N := by
    rw [hN, sub_mul, Matrix.mul_sub, smul_mul_assoc, Matrix.one_mul, mul_smul_comm,
      Matrix.mul_one]
  have hN2 : N * N = (lb - l1) • N := by
    rw [hN, Matrix.sub_mul, ← hN, hΛN, smul_mul_assoc, Matrix.one_mul, sub_smul]
  have hΛ'N : (Λ + c • N) * N = ν • N := by
    rw [Matrix.add_mul, hΛN, smul_mul_assoc, hN2, smul_smul, ← add_smul]
    congr 1
    rw [hc]
    field_simp
    ring
  intro h hbd
  rw [hE h hbd]
  -- bounded sequences `N M_t`
  obtain ⟨C, hC⟩ := hbd
  have hNb : ∃ C', ∀ t i, |(N *ᵥ Mpart (h t)) i| ≤ C' := by
    obtain ⟨K, hK⟩ := GeneralFOC.exists_bound_mulVec N C
    exact ⟨K, fun t i => hK (Mpart (h t)) (fun j => by
      have := hC t (Sum.inr j)
      rwa [Real.norm_eq_abs] at this) i⟩
  constructor
  · intro hR t
    obtain ⟨hM, hξ⟩ := hR t
    refine ⟨?_, hξ⟩
    have hz := eq_zero_of_bdd_geom hb hNb (fun s => by
      rw [(hR s).1, mulVec_mulVec, hNΛ, hΛN, Matrix.smul_mulVec])
    rw [hM, Matrix.add_mulVec, Matrix.smul_mulVec, hz t, smul_zero, add_zero]
  · intro hR t
    obtain ⟨hM, hξ⟩ := hR t
    refine ⟨?_, hξ⟩
    have hz := eq_zero_of_bdd_geom hν hNb (fun s => by
      rw [(hR s).1, mulVec_mulVec]
      have hcomm : N * (Λ + c • N) = (Λ + c • N) * N := by
        rw [Matrix.mul_add, Matrix.add_mul, hNΛ, mul_smul_comm, smul_mul_assoc]
      rw [hcomm, hΛ'N, Matrix.smul_mulVec])
    rw [hM, Matrix.add_mulVec, Matrix.smul_mulVec, hz t, smul_zero, add_zero]

/-- Woodford (2003), (1.22), p. 553: Cayley–Hamilton for a `2 × 2` matrix with
`tr Λ = λ₁ + λ_b`, `det Λ = λ₁λ_b`: `(Λ − λ_bI)(Λ − λ₁I) = 0`. -/
theorem cayley_two (Λ : Matrix (Fin 2) (Fin 2) ℝ) {l1 lb : ℝ} (htr : Λ.trace = l1 + lb)
    (hdet : Λ.det = l1 * lb) :
    (Λ - lb • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * (Λ - l1 • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = 0 := by
  rw [trace_fin_two] at htr
  rw [det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]
  · linear_combination (Λ 0 0) * htr - hdet
  · linear_combination (Λ 0 1) * htr
  · linear_combination (Λ 1 0) * htr
  · linear_combination (Λ 1 1) * htr - hdet

/-- Woodford (2003), (1.22): for `2 × 2` `Λ` with eigenvalues `λ₁ ≠ λ_b` (`tr Λ = λ₁ + λ_b`,
`det Λ = λ₁λ_b`), `Λ' = Λ + ((ν − λ_b)/(λ_b − λ₁))(Λ − λ₁I)` has
`α'(L) = det(I − Λ'L) = (1 − λ₁L)(1 − νL)`. -/
theorem alpha_modify (Λ : Matrix (Fin 2) (Fin 2) ℝ) {l1 lb ν : ℝ} (htr : Λ.trace = l1 + lb)
    (hdet : Λ.det = l1 * lb) (h1b : l1 ≠ lb) :
    alpha (Λ + ((ν - lb) / (lb - l1)) • (Λ - l1 • (1 : Matrix (Fin 2) (Fin 2) ℝ))) =
      (1 - C l1 * X) * (1 - C ν * X) := by
  have hsub : lb - l1 ≠ 0 := sub_ne_zero.mpr h1b.symm
  set c := (ν - lb) / (lb - l1) with hc
  have hcν : lb + c * (lb - l1) = ν := by
    rw [hc]
    field_simp
    ring
  rw [trace_fin_two] at htr
  rw [det_fin_two] at hdet
  have htr' : (Λ + c • (Λ - l1 • (1 : Matrix (Fin 2) (Fin 2) ℝ))).trace = l1 + ν := by
    rw [trace_fin_two]
    simp [Matrix.sub_apply]
    linear_combination (1 + c) * htr + hcν
  have hdet' : (Λ + c • (Λ - l1 • (1 : Matrix (Fin 2) (Fin 2) ℝ))).det = l1 * ν := by
    rw [det_fin_two]
    simp [Matrix.sub_apply]
    linear_combination (1 + c) ^ 2 * hdet - c * l1 * (1 + c) * htr + l1 * hcν
  rw [InertiaSplit.alpha_fin_two, htr', hdet', C_add, C_mul]
  ring

/-- **Woodford (2003), Rule III (3.24), p. 595, and Proposition 8.1: Rule III's lag polynomial is
`det(I − Λ'L)` for a `Λ'` satisfying the homogeneous Proposition 8.1 equivalence.** In the real
case (`S² ≥ 4P₂₃`), starting from the `Λ` of the Rule I split (`λₛ = λ₃`, eigenvalues `λ₁, λ₂`),
`Λ' = Λ + ((S/2 − λ₂)/(λ₂ − λ₁))(Λ − λ₁I)` has the same bounded homogeneous solutions as `Λ`
(`homEquiv_modify`, `ν = S/2 > 1`) and `α'(L) = (1 − λ₁L)(1 − ½(λ₂ + λ₃)L)`. Hence neither the
homogeneous equivalence nor Proposition 8.3 excludes Rule III's `α(L)`; only the deflating-split
construction of `Λ` does (`InertiaSplit.split_not_ruleIII`). -/
theorem ruleIII_homEquiv (c : Calib) (γ : ℝ) (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hD : 0 ≤ discQ c.β γ c.κ c.σ) :
    ∃ Λ' : Matrix (Fin 2) (Fin 2) ℝ,
      Prop83.HomEquiv (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β Λ'
        (Υmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le))
          (inJ c (c.β * lam3r c.β γ c.κ c.σ)⁻¹)) ∧
      alpha Λ' = (1 - C (lam1 c.β γ c.κ c.σ) * X) * (1 - C (sumS c.β γ c.κ c.σ / 2) * X) := by
  have h := standing_of c γ hc hγ0 hγ1
  have hq := InertiaSplit.quadQ_lam3r hD
  obtain ⟨hp, h1, h0, -⟩ := InertiaSplit.mu_facts c γ h hq
  have hls : lam3r c.β γ c.κ c.σ ≠ 0 := by linarith [one_lt_lam3r h]
  -- the homogeneous equivalence for the split's `Λ`, from Proposition 8.1 (perfect foresight)
  set H := Prop81General.prop81 (inProblem c γ hc hγ0.le) (inSplit c γ hc hγ0 hγ1 hq)
    perfectForesight 0 with hH
  obtain ⟨hyb, hya, hφb, hφm, h118⟩ := Prop83Links.const_base (inProblem c γ hc hγ0.le)
    perfectForesight 0 _ (InertiaSplit.in_xvec_base c γ hc hγ0.le)
  have hE := Prop83.homEquiv_of_perturbation h118
    (Prop83Links.hequiv_of_prop81M H hyb hya hφb hφm)
  change Prop83.HomEquiv (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β
    (Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le)) c.β
      (inJ c (c.β * lam3r c.β γ c.κ c.σ)⁻¹))
    (Υmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le))
      (inJ c (c.β * lam3r c.β γ c.κ c.σ)⁻¹)) at hE
  -- its trace and determinant
  have hb : sumS c.β γ c.κ c.σ - lam3r c.β γ c.κ c.σ = lam2r c.β γ c.κ c.σ := by
    rw [← InertiaSplit.lam2r_add_lam3r]
    ring
  have htr := InertiaSplit.in_Λ_trace c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hc.1.ne'
    hγ0.ne' hp h1 h0
  rw [InertiaSplit.tr_eq c γ h hls hp, hb] at htr
  have hdet := InertiaSplit.in_Λ_det c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le) hc.1.ne'
    hγ0.ne' hp h1 h0
  rw [InertiaSplit.det_eq c γ h hls hq, hb] at hdet
  have hl1 := lam1_spec h
  have h2 := one_lt_lam2r h
  have h1b : lam1 c.β γ c.κ c.σ ≠ lam2r c.β γ c.κ c.σ := by linarith
  have hS := two_lt_sumS h
  refine ⟨_, homEquiv_modify hE (cayley_two _ htr hdet) h1b
    (by rw [abs_of_pos (by linarith)]; exact h2)
    (ν := sumS c.β γ c.κ c.σ / 2) (by rw [abs_of_pos (by linarith)]; linarith),
    alpha_modify _ htr hdet h1b⟩

end Woodford.OptimalPolicyRules.InertiaRuleIII
