/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.MoneyGrowth
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Nonseparable utility: real-balance effects on the Fisher equation

Woodford (2003), *Interest and Prices*, Chapter 2, §3.4, pp. 111–117 ((3.10)–(3.22)), and
Appendix A, §§A.12–A.13, pp. 645–646.

* (3.10), p. 113: `chi_eq_sm_mul_upsilon`, `sm_eq`, `chi_pos_iff`, `chi_neg_iff` — `χ = s_m υ`,
  `s_m = Δ̄ m̄/Ȳ`, and `χ`, `υ` have the same sign.
* (3.11), p. 114: `hasFDerivAt_logMU` (the log marginal utility of consumption is, to first order,
  `−σ⁻¹ ŷ + χ m̂`, an exact derivative) and `fisher311_of_lambda` (the log-linear Euler
  equation in terms of `λ̂ = log u_c` gives (3.11) with `r̂` as in (1.33)).
* (3.12), p. 114: `fisher311_iff_312` — given (3.6), (3.11) is equivalent to (3.12).
* (3.13)–(3.15), pp. 114–115: `spread_const_iff` (a constant spread `Δ = Δ̄` is exactly
  `î = îᵐ`), `fisher312_constSpread` ((3.12) becomes (3.15)), `constSpread_existsUnique`
  (determinacy for every `φ_p > 0`).
* **Proposition 2.12** (A.12): `eq212_iff_scalar` is (A.32); `prop_2_12_iff` — for every
  bounded exogenous disturbance there is exactly one bounded solution iff
  `|1 + η_iχφ_p| < |1 + (1 + η_iχ)φ_p|`; `prop_2_12` — this holds for all `φ_p > 0` when
  `χ > −1/(2η_i)` (3.16); `prop_2_12_priceLevel` is the solution (3.17) with weights (3.18)–(3.19)
  (the target `log P*` may trend: the series converge by summation by parts);
  `phi212_pos`, `phiT212_pos` (positive if `χ > −1/(φ_p η_i)`), `hasSum_phi212`,
  `hasSum_phiT212` (both sum to one), `sol212_continuousOn` (the solution is continuous in `χ` on
  the whole region (3.16)), `weights212_at_zero` (reduction to (1.39) at `χ = 0`) and
  `phiT212_ne_phi212` (the two weight sequences differ for `χ ≠ 0`).
* **Proposition 2.13** (A.13): `eq213_iff` is (A.33); `det213_iff` — for `φ_π ≠ 0`
  determinacy holds iff `|γ₁| < |γ₀|`; `not_det213_zero` — never for `φ_π = 0`;
  `prop_2_13` — under (3.16), determinacy iff `φ_π > 0` and `φ_π + ρ > 1`;
  `gap213_formula` gives (3.20) with weights (3.21)–(3.22); `weights213_pos`,
  `weights213_at_zero` (reduction to (2.14) at `χ = 0`).
* Survey lemma L4 is used from `ForwardSolution` (`abs_lt_abs_of_sub_pos_add_pos`,
  `abs_lt_abs_iff_of_add_pos`).

Proposition 2.13 is stated in the book for `iᵐ_t = īᵐ_t`; its proof (and this module) takes the
interest on money constant, `îᵐ = 0` (survey E16).
-/

namespace Woodford.PriceLevelDetermination.NonSeparable

open Filter Topology
open Woodford.PriceLevelDetermination.MoneyGrowth
open Woodford.PriceLevelDetermination.ForwardSolution (ScalarEq scalarSol scalarSol_apply
  scalar_existsUnique scalar_homog scalar_determinate_iff summable_geom_mul)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (3.10): the elasticity `χ` -/

/-- Woodford (2003), eq. (3.10), p. 113: `χ = m̄ u_cm / u_c`. -/
noncomputable def chi (mbar uc ucm : ℝ) : ℝ := mbar * ucm / uc

/-- Woodford (2003), p. 113: `υ = Ȳ u_mc / u_m`. -/
noncomputable def upsilon (Ybar um ucm : ℝ) : ℝ := Ybar * ucm / um

/-- Woodford (2003), p. 113: `s_m = m̄ u_m / (Ȳ u_c)`. -/
noncomputable def sm (Ybar mbar uc um : ℝ) : ℝ := mbar * um / (Ybar * uc)

/-- Woodford (2003), p. 113: `χ = s_m υ` (with `u_cm = u_mc`). -/
theorem chi_eq_sm_mul_upsilon {Ybar mbar uc um ucm : ℝ} (hY : Ybar ≠ 0) (hc : uc ≠ 0)
    (hm : um ≠ 0) : chi mbar uc ucm = sm Ybar mbar uc um * upsilon Ybar um ucm := by
  unfold chi sm upsilon
  field_simp

/-- Woodford (2003), p. 113: with the first-order condition `u_m/u_c = Δ̄`, `s_m = Δ̄ m̄/Ȳ`. -/
theorem sm_eq {Ybar mbar uc um Δbar : ℝ} (hY : Ybar ≠ 0) (hc : uc ≠ 0)
    (hfoc : um / uc = Δbar) : sm Ybar mbar uc um = Δbar * (mbar / Ybar) := by
  unfold sm
  rw [← hfoc]
  field_simp

/-- Woodford (2003), p. 113: `χ > 0` iff `υ > 0` (since `s_m > 0`). -/
theorem chi_pos_iff {Ybar mbar uc um ucm : ℝ} (hY : 0 < Ybar) (hmb : 0 < mbar) (hc : 0 < uc)
    (hm : 0 < um) : 0 < chi mbar uc ucm ↔ 0 < upsilon Ybar um ucm := by
  rw [chi_eq_sm_mul_upsilon hY.ne' hc.ne' hm.ne']
  have hs : 0 < sm Ybar mbar uc um := by unfold sm; positivity
  exact ⟨fun h => pos_of_mul_pos_right h hs.le, fun h => mul_pos hs h⟩

/-- Woodford (2003), p. 113: `χ < 0` iff `υ < 0`. -/
theorem chi_neg_iff {Ybar mbar uc um ucm : ℝ} (hY : 0 < Ybar) (hmb : 0 < mbar) (hc : 0 < uc)
    (hm : 0 < um) : chi mbar uc ucm < 0 ↔ upsilon Ybar um ucm < 0 := by
  rw [chi_eq_sm_mul_upsilon hY.ne' hc.ne' hm.ne']
  have hs : 0 < sm Ybar mbar uc um := by unfold sm; positivity
  constructor
  · intro h
    by_contra h'
    push Not at h'
    have := mul_nonneg hs.le h'
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hs h

/-! ### (3.11): the log-linear Euler equation with real-balance effects -/

/-- Woodford (2003), (3.11), p. 114: the log marginal utility of consumption
`log u_c(Ȳ e^{ŷ}, m̄ e^{m̂}) − log u_c(Ȳ, m̄)` as a function of `(ŷ, m̂)`. -/
noncomputable def logMU (Uc : ℝ × ℝ → ℝ) (Ybar mbar : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.log (Uc (Ybar * Real.exp x.1, mbar * Real.exp x.2)) - Real.log (Uc (Ybar, mbar))

/-- Woodford (2003), (1.33) and (3.10)–(3.11), pp. 80, 113–114 (exact derivative): if `u_c` is
differentiable at the steady state with partials `u_cc = U'(1,0)`, `u_cm = U'(0,1)` and
`u_c > 0`, the derivative of `logMU` at zero is `(ŷ, m̂) ↦ −σ⁻¹ ŷ + χ m̂`, with
`σ⁻¹ = −u_cc Ȳ/u_c` and `χ = m̄ u_cm/u_c`. -/
theorem hasFDerivAt_logMU {Uc : ℝ × ℝ → ℝ} {U' : ℝ × ℝ →L[ℝ] ℝ} {Ybar mbar : ℝ}
    (hU : HasFDerivAt Uc U' (Ybar, mbar)) (hpos : 0 < Uc (Ybar, mbar)) :
    ∃ G' : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (logMU Uc Ybar mbar) G' 0 ∧
      ∀ v, G' v = -(-(U' (1, 0)) * Ybar / Uc (Ybar, mbar)) * v.1 +
        chi mbar (Uc (Ybar, mbar)) (U' (0, 1)) * v.2 := by
  let P1 : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let P2 : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hY := (P1.hasFDerivAt (x := 0)).exp.const_mul Ybar
  have hM := (P2.hasFDerivAt (x := 0)).exp.const_mul mbar
  have hg := hY.prodMk hM
  have hg0 : ((Ybar * Real.exp (P1 0), mbar * Real.exp (P2 0)) : ℝ × ℝ) = (Ybar, mbar) := by
    simp
  rw [← hg0] at hU
  have hc := hU.comp (0 : ℝ × ℝ) hg
  have hne : (Uc ∘ fun x => (Ybar * Real.exp (P1 x), mbar * Real.exp (P2 x))) 0 ≠ 0 := by
    simp only [Function.comp_apply]
    rw [hg0]
    exact hpos.ne'
  have hlog := (hc.log hne).sub_const (Real.log (Uc (Ybar, mbar)))
  refine ⟨_, hlog, fun v => ?_⟩
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    smul_eq_mul]
  rw [clm2_apply]
  simp [P1, P2, chi]
  field_simp

/-- Woodford (2003), eq. (1.33), p. 80: `r̂_t = σ⁻¹(E_t(Ŷ_{t+1} − g_{t+1}) − (Ŷ_t − g_t))`. -/
def rhat (σinv : ℝ) (Y g : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => σinv • (𝔼.E t (Y (t + 1) - g (t + 1)) - (Y t - g t))

/-- Woodford (2003), eq. (3.11), p. 114: `î_t = r̂_t + E_t π_{t+1} − χ E_t(m̂_{t+1} − m̂_t)`, with
`E_t π_{t+1} = E_t log P_{t+1} − log P_t`. -/
def Fisher311 (χ : ℝ) (r p i mh : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = r t + (𝔼.E t (p (t + 1)) - p t) - χ • (𝔼.E t (mh (t + 1)) - mh t)

/-- Woodford (2003), (1.21) log-linearised, pp. 79, 114: `î_t = λ̂_t − E_t λ̂_{t+1} + E_t π_{t+1}`
with `λ̂ = log u_c` (deviation). With `λ̂ = −σ⁻¹(Ŷ − g) + χ m̂` (`hasFDerivAt_logMU`) this is (3.11)
with `r̂` given by (1.33). -/
theorem fisher311_of_lambda {σinv χ : ℝ} {Y g mh lam p i : ℕ → Ω → ℝ}
    (hlam : ∀ t, lam t = -σinv • (Y t - g t) + χ • mh t)
    (heul : ∀ t, i t = lam t - 𝔼.E t (lam (t + 1)) + (𝔼.E t (p (t + 1)) - p t)) :
    Fisher311 𝔼 χ (rhat 𝔼 σinv Y g) p i mh := by
  intro t
  rw [heul t, hlam t, hlam (t + 1)]
  funext ω
  simp only [rhat, map_add, map_sub, map_smul, map_neg, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul, neg_smul]
  ring

/-! ### (3.12): substituting money demand -/

/-- Woodford (2003), eq. (3.6), p. 107, in terms of `îᵐ`:
`m̂_t = η_y Ŷ_t − η_i(î_t − îᵐ_t) + εᵐ_t`. -/
def LM36 (ηy ηi : ℝ) (Y e im mh i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, mh t = ηy • Y t - ηi • (i t - im t) + e t

/-- Woodford (2003), p. 114: the composite disturbance
`r̃_t = r̂_t − η_y χ E_t(Ŷ_{t+1} − Ŷ_t) − χ E_t(εᵐ_{t+1} − εᵐ_t)`. -/
def rtilde (ηy χ : ℝ) (r Y e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => r t - (ηy * χ) • (𝔼.E t (Y (t + 1)) - Y t) - χ • (𝔼.E t (e (t + 1)) - e t)

/-- Woodford (2003), p. 115 fn 49: with `χ = 0` the composite disturbance `r̃` is `r̂`. -/
theorem rtilde_zero (ηy : ℝ) (r Y e : ℕ → Ω → ℝ) : rtilde 𝔼 ηy 0 r Y e = r := by
  funext t
  simp [rtilde]

/-- Woodford (2003), eq. (3.12), p. 114:
`(1 + η_iχ) î_t = r̃_t + E_t π_{t+1} + η_iχ E_t î_{t+1} − η_iχ E_t(îᵐ_{t+1} − îᵐ_t)`, where
`Epi t` stands for `E_t π_{t+1}`. -/
def Fisher312 (ηi χ : ℝ) (rt Epi i im : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (1 + ηi * χ) • i t = rt t + Epi t + (ηi * χ) • 𝔼.E t (i (t + 1)) -
    (ηi * χ) • (𝔼.E t (im (t + 1)) - im t)

/-- Woodford (2003), (3.11)–(3.12), p. 114: given money demand (3.6), the Euler equation (3.11) is
equivalent to (3.12). -/
theorem fisher311_iff_312 {ηy ηi χ : ℝ} {r Y e im mh p i : ℕ → Ω → ℝ}
    (hLM : LM36 ηy ηi Y e im mh i) :
    Fisher311 𝔼 χ r p i mh ↔
      Fisher312 𝔼 ηi χ (rtilde 𝔼 ηy χ r Y e) (fun t => 𝔼.E t (p (t + 1)) - p t) i im := by
  unfold Fisher311 Fisher312
  refine forall_congr' fun t => ?_
  rw [hLM t, hLM (t + 1), funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [rtilde, map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  constructor
  · intro h; linear_combination (1 + ηi * χ) * h - ηi * χ * h
  · intro h; linear_combination h

/-! ### (3.13)–(3.15): a constant interest-rate spread -/

/-- Woodford (2003), (3.13)–(3.14), pp. 114–115: holding the spread at `Δ = Δ̄ < 1` is exactly
`î_t = îᵐ_t` (not only to first order). -/
theorem spread_const_iff {Δbar ih imh : ℝ} (hΔ : Δbar < 1) :
    spread Δbar ih imh = Δbar ↔ ih = imh := by
  unfold spread
  constructor
  · intro h
    have h1 : Real.exp (imh - ih) = 1 := by
      have : (1 - Δbar) * Real.exp (imh - ih) = (1 - Δbar) * 1 := by linarith
      exact mul_left_cancel₀ (by linarith) this
    rw [Real.exp_eq_one_iff] at h1
    linarith
  · rintro rfl
    simp

/-- Woodford (2003), eq. (3.15), p. 115: with `îᵐ = î`, (3.12) reduces to
`î_t = r̃_t + E_t π_{t+1}`. -/
theorem fisher312_constSpread {ηi χ : ℝ} {rt Epi i : ℕ → Ω → ℝ} :
    Fisher312 𝔼 ηi χ rt Epi i i ↔ ∀ t, i t = rt t + Epi t := by
  unfold Fisher312
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- Woodford (2003), p. 115: under a constant spread and a Wicksellian rule `î = φ_p P̂ + ν`,
(3.15) with (1.35) is (1.36) with `r̃` in place of `r̂`; for `φ_p > 0` and bounded adapted
disturbances (`r̃`, the target inflation forecast `Epistar`, `ν`) it has exactly one bounded
solution — Prop. 2.3 applies unchanged. -/
theorem constSpread_existsUnique {φp : ℝ} (hφ : 0 < φp) {rt Epistar ν : ℕ → Ω → ℝ}
    (hrt : BoundedProc rt) (hEp : BoundedProc Epistar) (hν : BoundedProc ν)
    (hart : 𝔼.Adapted rt) (haEp : 𝔼.Adapted Epistar) (haν : 𝔼.Adapted ν) :
    ∃! Ph : ℕ → Ω → ℝ, BoundedProc Ph ∧
      ∀ t, φp • Ph t + ν t = rt t + (𝔼.E t (Ph (t + 1)) - Ph t + Epistar t) := by
  obtain ⟨K1, h1⟩ := hrt
  obtain ⟨K2, h2⟩ := hEp
  obtain ⟨K3, h3⟩ := hν
  have hAB : |(1 : ℝ)| < |1 + φp| := by
    rw [abs_one, abs_of_pos (by linarith)]; linarith
  have hfb : ∀ t ω, |(fun t => rt t + Epistar t - ν t) t ω| ≤ K1 + K2 + K3 := fun t ω => by
    simp only [Pi.add_apply, Pi.sub_apply]
    have := abs_sub (rt t ω + Epistar t ω) (ν t ω)
    have := abs_add_le (rt t ω) (Epistar t ω)
    linarith [h1 t ω, h2 t ω, h3 t ω]
  have hfa : 𝔼.Adapted (fun t => rt t + Epistar t - ν t) := fun t => by
    simp only [map_add, map_sub, hart t, haEp t, haν t]
  obtain ⟨hs, hb, -, hu⟩ := scalar_existsUnique 𝔼 hAB hfb hfa
  have key : ∀ Ph : ℕ → Ω → ℝ, (∀ t, φp • Ph t + ν t = rt t + (𝔼.E t (Ph (t + 1)) - Ph t +
      Epistar t)) ↔ ScalarEq 𝔼 (1 + φp) 1 (fun t => rt t + Epistar t - ν t) Ph := fun Ph => by
    refine forall_congr' fun t => ?_
    rw [funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · intro h; linear_combination h
    · intro h; linear_combination h
  exact ⟨_, ⟨hb, (key _).mpr hs⟩, fun Ph h => hu Ph ((key Ph).mp h.2) h.1⟩

/-! ### Proposition 2.12: a Wicksellian rule with constant interest on money -/

/-- Woodford (2003), (A.32), p. 645: `A = 1 + (1 + η_iχ)φ_p`. -/
def A212 (ηi χ φp : ℝ) : ℝ := 1 + (1 + ηi * χ) * φp

/-- Woodford (2003), (A.32), p. 645: `B = 1 + η_iχφ_p`. -/
def B212 (ηi χ φp : ℝ) : ℝ := 1 + ηi * χ * φp

/-- Woodford (2003), (1.35), p. 81:
`E_t π_{t+1} = E_t P̂_{t+1} − P̂_t + E_t log P*_{t+1} − log P*_t` (`pstar = log P*`). -/
def EpiW (Ph pstar : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => 𝔼.E t (Ph (t + 1)) - Ph t + (𝔼.E t (pstar (t + 1)) - pstar t)

/-- Woodford (2003), Prop. 2.12, p. 115: (3.12) with `îᵐ = 0`, the Wicksellian rule
`î = φ_p P̂ + ν` (1.34) and (1.35). -/
def Eq212 (ηi χ φp : ℝ) (rt pstar ν Ph : ℕ → Ω → ℝ) : Prop :=
  Fisher312 𝔼 ηi χ rt (EpiW 𝔼 Ph pstar) (fun t => φp • Ph t + ν t) 0

/-- Woodford (2003), (A.32), p. 645: the forcing term
`E_t π*_{t+1} + (r̃_t − ν_t) + η_iχ(E_t ν_{t+1} − ν_t)`. -/
def f212 (ηi χ : ℝ) (rt pstar ν : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (𝔼.E t (pstar (t + 1)) - pstar t) + (rt t - ν t) +
    (ηi * χ) • (𝔼.E t (ν (t + 1)) - ν t)

/-- Woodford (2003), **(A.32)**, p. 645: the equilibrium conditions of Prop. 2.12 are the scalar
equation `(1 + (1 + η_iχ)φ_p) P̂_t = (1 + η_iχφ_p) E_t P̂_{t+1} + f_t`. -/
theorem eq212_iff_scalar {ηi χ φp : ℝ} {rt pstar ν Ph : ℕ → Ω → ℝ} :
    Eq212 𝔼 ηi χ φp rt pstar ν Ph ↔
      ScalarEq 𝔼 (A212 ηi χ φp) (B212 ηi χ φp) (f212 𝔼 ηi χ rt pstar ν) Ph := by
  unfold Eq212 Fisher312 ScalarEq
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [EpiW, f212, A212, B212, map_add, map_smul, map_zero, Pi.zero_apply, sub_zero,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- Woodford (2003), A.12: bounded increments of an adapted process give bounded expected
increments `E_t x_{t+1} − x_t`. -/
theorem expected_incr_bound {x : ℕ → Ω → ℝ} {K : ℝ} (hx : 𝔼.Adapted x)
    (hK : ∀ t ω, |x (t + 1) ω - x t ω| ≤ K) (t : ℕ) (ω : Ω) :
    |(𝔼.E t (x (t + 1)) - x t) ω| ≤ K := by
  have : 𝔼.E t (x (t + 1)) - x t = 𝔼.E t (x (t + 1) - x t) := by rw [map_sub, hx t]
  rw [this]
  exact 𝔼.abs_E_le (fun ω' => hK t ω') t ω

/-- Woodford (2003), A.12: the forcing term of (A.32) is bounded and adapted. -/
theorem f212_bounded_adapted {ηi χ K1 K2 K3 : ℝ} {rt pstar ν : ℕ → Ω → ℝ}
    (h1 : ∀ t ω, |rt t ω| ≤ K1) (h2 : ∀ t ω, |pstar (t + 1) ω - pstar t ω| ≤ K2)
    (h3 : ∀ t ω, |ν t ω| ≤ K3) (ha1 : 𝔼.Adapted rt) (ha2 : 𝔼.Adapted pstar)
    (ha3 : 𝔼.Adapted ν) :
    (∀ t ω, |f212 𝔼 ηi χ rt pstar ν t ω| ≤ K2 + (K1 + K3) + |ηi * χ| * (K3 + K3)) ∧
      𝔼.Adapted (f212 𝔼 ηi χ rt pstar ν) := by
  constructor
  · intro t ω
    have e2 := expected_incr_bound 𝔼 ha2 h2 t ω
    have e3 : |(𝔼.E t (ν (t + 1)) - ν t) ω| ≤ K3 + K3 := by
      simp only [Pi.sub_apply]
      have := abs_sub (𝔼.E t (ν (t + 1)) ω) (ν t ω)
      linarith [𝔼.abs_E_le (fun ω' => h3 (t + 1) ω') t ω, h3 t ω]
    simp only [f212, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 e3 ⊢
    have a1 := abs_add_le (𝔼.E t (pstar (t + 1)) ω - pstar t ω) (rt t ω - ν t ω)
    have a2 := abs_add_le (𝔼.E t (pstar (t + 1)) ω - pstar t ω + (rt t ω - ν t ω))
      (ηi * χ * (𝔼.E t (ν (t + 1)) ω - ν t ω))
    have a3 := abs_sub (rt t ω) (ν t ω)
    have a4 : |ηi * χ * (𝔼.E t (ν (t + 1)) ω - ν t ω)| ≤ |ηi * χ| * (K3 + K3) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left e3 (abs_nonneg _)
    linarith [h1 t ω, h3 t ω]
  · intro t
    simp only [f212, map_add, map_sub, map_smul, 𝔼.E_E_self, ha1 t, ha2 t, ha3 t]

/-- Woodford (2003), Prop. 2.12 and A.12, pp. 115, 645–646 (exact determinacy condition): for
every bounded adapted `r̃`, `ν` and every adapted target `log P*` with bounded growth, there is
exactly one bounded `P̂` solving the equilibrium conditions if and only if
`|1 + η_iχφ_p| < |1 + φ_p(1 + η_iχ)|`. -/
theorem prop_2_12_iff [Nonempty Ω] (ηi χ φp : ℝ) :
    (∀ rt pstar ν : ℕ → Ω → ℝ, BoundedProc rt → BoundedProc ν →
      (∃ K, ∀ t ω, |pstar (t + 1) ω - pstar t ω| ≤ K) →
      𝔼.Adapted rt → 𝔼.Adapted pstar → 𝔼.Adapted ν →
      ∃! Ph, BoundedProc Ph ∧ Eq212 𝔼 ηi χ φp rt pstar ν Ph) ↔
      |B212 ηi χ φp| < |A212 ηi χ φp| := by
  have hAB : A212 ηi χ φp ≠ 0 ∨ B212 ηi χ φp ≠ 0 := by
    by_contra h
    push Not at h
    unfold A212 B212 at h
    have : φp = 0 := by linarith [h.1, h.2]
    rw [this] at h
    linarith [h.1]
  rw [← scalar_determinate_iff 𝔼 hAB]
  constructor
  · intro h f hfb hfa
    have hz : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
    have hf : f212 𝔼 ηi χ f 0 0 = f := by
      funext t ω
      simp [f212]
    obtain ⟨Ph, hP, hu⟩ := h f 0 0 hfb ⟨0, fun _ _ => by simp⟩ ⟨0, fun _ _ => by simp⟩ hfa hz hz
    refine ⟨Ph, ⟨hP.1, ?_⟩, fun z hz' => hu z ⟨hz'.1, ?_⟩⟩
    · rw [← hf]; exact (eq212_iff_scalar 𝔼).mp hP.2
    · rw [eq212_iff_scalar, hf]; exact hz'.2
  · intro h rt pstar ν ⟨K1, h1⟩ ⟨K3, h3⟩ ⟨K2, h2⟩ ha1 ha2 ha3
    obtain ⟨hb, ha⟩ := f212_bounded_adapted 𝔼 (ηi := ηi) (χ := χ) h1 h2 h3 ha1 ha2 ha3
    obtain ⟨Ph, hP, hu⟩ := h _ ⟨_, hb⟩ ha
    refine ⟨Ph, ⟨hP.1, (eq212_iff_scalar 𝔼).mpr hP.2⟩, fun z hz => ?_⟩
    exact hu z ⟨hz.1, (eq212_iff_scalar 𝔼).mp hz.2⟩

/-- Woodford (2003), A.12, p. 646 (via survey L4): if `η_i > 0`, `χ > −1/(2η_i)` (3.16) and
`φ_p > 0`, then `|B| < |A|`; indeed `A − B = φ_p > 0` and `A + B = 2 + (1 + 2η_iχ)φ_p > 0`. -/
theorem abs_B_lt_A {ηi χ φp : ℝ} (hηi : 0 < ηi) (hχ : -1 / (2 * ηi) < χ) (hφ : 0 < φp) :
    |B212 ηi χ φp| < |A212 ηi χ φp| := by
  have h1 : 0 < 1 + 2 * ηi * χ := by
    rw [div_lt_iff₀ (by linarith)] at hχ; linarith
  apply ForwardSolution.abs_lt_abs_of_sub_pos_add_pos
  · unfold A212 B212; nlinarith
  · unfold A212 B212; nlinarith

/-- Woodford (2003), **Proposition 2.12**, pp. 115–116: with `η_i > 0` and `χ > −1/(2η_i)` (3.16),
equilibrium is determinate for every rule with `φ_p > 0`. -/
theorem prop_2_12 [Nonempty Ω] {ηi χ φp : ℝ} (hηi : 0 < ηi) (hχ : -1 / (2 * ηi) < χ)
    (hφ : 0 < φp) :
    ∀ rt pstar ν : ℕ → Ω → ℝ, BoundedProc rt → BoundedProc ν →
      (∃ K, ∀ t ω, |pstar (t + 1) ω - pstar t ω| ≤ K) →
      𝔼.Adapted rt → 𝔼.Adapted pstar → 𝔼.Adapted ν →
      ∃! Ph, BoundedProc Ph ∧ Eq212 𝔼 ηi χ φp rt pstar ν Ph :=
  (prop_2_12_iff 𝔼 ηi χ φp).mpr (abs_B_lt_A hηi hχ hφ)

/-- Woodford (2003), eq. (3.18), p. 116: `ϕ_j = (1 + η_iχφ_p)ʲ φ_p / [1 + (1 + η_iχ)φ_p]^{j+1}`. -/
noncomputable def phi212 (ηi χ φp : ℝ) (j : ℕ) : ℝ :=
  B212 ηi χ φp ^ j * φp / A212 ηi χ φp ^ (j + 1)

/-- Woodford (2003), eq. (3.19), p. 116: `ϕ̃_0 = (1 + η_iχ)φ_p / A`,
`ϕ̃_j = Bʲ⁻¹ φ_p / A^{j+1}` for `j ≥ 1`. -/
noncomputable def phiT212 (ηi χ φp : ℝ) : ℕ → ℝ
  | 0 => (1 + ηi * χ) * φp / A212 ηi χ φp
  | j + 1 => B212 ηi χ φp ^ j * φp / A212 ηi χ φp ^ (j + 2)

/-- Woodford (2003), A.12: summability of `Bʲ/A^{j+1} y_j` for bounded `y` when `|B| < |A|`. -/
theorem summable_c_bdd {A B K : ℝ} (h : |B| < |A|) {y : ℕ → ℝ} (hy : ∀ j, |y j| ≤ K) :
    Summable (fun j => B ^ j / A ^ (j + 1) * y j) := by
  have hA0 : 0 < |A| := lt_of_le_of_lt (abs_nonneg B) h
  have hq : |B / A| < 1 := by rw [abs_div, div_lt_one hA0]; exact h
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (abs_nonneg _) hq).mul_left (|A⁻¹| * K)) (fun j => ?_)
  have e : B ^ j / A ^ (j + 1) * y j = A⁻¹ * ((B / A) ^ j * y j) := by
    have : A ≠ 0 := abs_pos.mp hA0
    rw [div_pow]
    field_simp
    ring
  rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
  calc |A⁻¹| * (|B / A| ^ j * |y j|) ≤ |A⁻¹| * (|B / A| ^ j * K) := by
        gcongr; exact hy j
    _ = |A⁻¹| * K * |B / A| ^ j := by ring

/-- Woodford (2003), A.12: summability of `Bʲ/A^{j+1} x_j` when `x` has bounded increments. -/
theorem summable_c_incr {A B K : ℝ} (h : |B| < |A|) {x : ℕ → ℝ}
    (hx : ∀ j, |x (j + 1) - x j| ≤ K) : Summable (fun j => B ^ j / A ^ (j + 1) * x j) := by
  have hA0 : 0 < |A| := lt_of_le_of_lt (abs_nonneg B) h
  have hq : |B / A| < 1 := by rw [abs_div, div_lt_one hA0]; exact h
  refine ((summable_geom_mul hq hx).mul_left A⁻¹).congr fun j => ?_
  have : A ≠ 0 := abs_pos.mp hA0
  rw [div_pow]
  field_simp
  ring

/-- Woodford (2003), **(3.17)**, p. 116 (A.12, "rearranging terms", p. 646): for the unique
bounded solution `P̂` of Prop. 2.12, the log price level `log P = P̂ + log P*` is
`φ_p⁻¹ ∑ ϕ_j E_t r̃_{t+j} + ∑ ϕ̃_j E_t(log P*_{t+j} − φ_p⁻¹ ν_{t+j})`, both series converging
(although `log P*` may trend). -/
theorem prop_2_12_priceLevel {ηi χ φp K1 K2 K3 : ℝ} (hφ : φp ≠ 0)
    (hAB : |B212 ηi χ φp| < |A212 ηi χ φp|) {rt pstar ν : ℕ → Ω → ℝ}
    (h1 : ∀ t ω, |rt t ω| ≤ K1) (h2 : ∀ t ω, |pstar (t + 1) ω - pstar t ω| ≤ K2)
    (h3 : ∀ t ω, |ν t ω| ≤ K3) (ha2 : 𝔼.Adapted pstar) (t : ℕ) (ω : Ω) :
    Summable (fun j => phi212 ηi χ φp j * 𝔼.E t (rt (t + j)) ω) ∧
      Summable (fun j => phiT212 ηi χ φp j * 𝔼.E t (pstar (t + j) - φp⁻¹ • ν (t + j)) ω) ∧
      scalarSol 𝔼 (A212 ηi χ φp) (B212 ηi χ φp) (f212 𝔼 ηi χ rt pstar ν) t ω + pstar t ω =
        φp⁻¹ * ∑' j, phi212 ηi χ φp j * 𝔼.E t (rt (t + j)) ω +
          ∑' j, phiT212 ηi χ φp j * 𝔼.E t (pstar (t + j) - φp⁻¹ • ν (t + j)) ω := by
  set A := A212 ηi χ φp with hA
  set B := B212 ηi χ φp with hB
  set k := ηi * χ with hk
  have hA0 : A ≠ 0 := abs_pos.mp (lt_of_le_of_lt (abs_nonneg B) hAB)
  have hAm : A = 1 + (1 + k) * φp := rfl
  have hBm : B = 1 + k * φp := rfl
  clear_value A B k
  set x : ℕ → ℝ := fun j => 𝔼.E t (pstar (t + j)) ω with hx
  set R : ℕ → ℝ := fun j => 𝔼.E t (rt (t + j)) ω with hR
  set N : ℕ → ℝ := fun j => 𝔼.E t (ν (t + j)) ω with hN
  have hxi : ∀ j, |x (j + 1) - x j| ≤ K2 := fun j => by
    simp only [hx]
    rw [← Pi.sub_apply, ← map_sub]
    exact 𝔼.abs_E_le (fun ω' => h2 (t + j) ω') t ω
  have hRb : ∀ j, |R j| ≤ K1 := fun j => 𝔼.abs_E_le (fun ω' => h1 (t + j) ω') t ω
  have hNb : ∀ j, |N j| ≤ K3 := fun j => 𝔼.abs_E_le (fun ω' => h3 (t + j) ω') t ω
  have hxib : ∀ j, |(x (j + 1) - x j)| ≤ K2 := hxi
  have hNb1 : ∀ j, |N (j + 1)| ≤ K3 := fun j => hNb (j + 1)
  have hx1 : ∀ j, |x (j + 1 + 1) - x (j + 1)| ≤ K2 := fun j => hxi (j + 1)
  set c : ℕ → ℝ := fun j => B ^ j / A ^ (j + 1) with hc
  have hs1 : Summable (fun j => c j * (x (j + 1) - x j)) := summable_c_bdd hAB hxib
  have hs2 : Summable (fun j => c j * R j) := summable_c_bdd hAB hRb
  have hs3 : Summable (fun j => c j * N j) := summable_c_bdd hAB hNb
  have hs4 : Summable (fun j => c j * N (j + 1)) := summable_c_bdd hAB hNb1
  have hs5 : Summable (fun j => c j * x j) := summable_c_incr hAB hxi
  have hs6 : Summable (fun j => c j * x (j + 1)) := summable_c_incr hAB hx1
  have hcs : ∀ j, c (j + 1) = B / A * c j := fun j => by
    simp only [hc]; field_simp; ring
  -- expected forcing terms
  have hEf : ∀ j, 𝔼.E t (f212 𝔼 ηi χ rt pstar ν (t + j)) ω =
      (x (j + 1) - x j) + R j - (1 + k) * N j + k * N (j + 1) := fun j => by
    simp only [f212, hx, hR, hN, hk, map_add, map_sub, map_smul,
      𝔼.tower (Nat.le_add_right t j), Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show t + (j + 1) = t + j + 1 by omega]
    ring
  have hPh : scalarSol 𝔼 A B (f212 𝔼 ηi χ rt pstar ν) t ω =
      ∑' j, c j * (x (j + 1) - x j) + ∑' j, c j * R j - (1 + k) * ∑' j, c j * N j +
        k * ∑' j, c j * N (j + 1) := by
    rw [scalarSol_apply]
    have H := ((hs1.hasSum.add hs2.hasSum).sub (hs3.hasSum.mul_left (1 + k))).add
      (hs4.hasSum.mul_left k)
    refine (HasSum.tsum_eq ?_)
    convert H using 1
    funext j
    rw [hEf j]
    simp only [hc]
    ring
  -- the three pieces
  have hphi : ∀ j, phi212 ηi χ φp j * R j = φp * (c j * R j) := fun j => by
    simp only [phi212, ← hA, ← hB, hc]; ring
  have hP1 : ∑' j, phi212 ηi χ φp j * 𝔼.E t (rt (t + j)) ω = φp * ∑' j, c j * R j := by
    rw [← tsum_mul_left]; exact tsum_congr hphi
  have hsP1 : Summable (fun j => phi212 ηi χ φp j * 𝔼.E t (rt (t + j)) ω) :=
    (hs2.mul_left φp).congr fun j => (hphi j).symm
  have hT : ∀ j, phiT212 ηi χ φp (j + 1) = φp / A * c j := fun j => by
    simp only [phiT212, ← hA, ← hB, hc]; field_simp; ring
  have hEterm : ∀ j, 𝔼.E t (pstar (t + j) - φp⁻¹ • ν (t + j)) ω = x j - φp⁻¹ * N j :=
    fun j => by simp only [hx, hN, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hsT1 : Summable (fun j => phiT212 ηi χ φp (j + 1) *
      𝔼.E t (pstar (t + (j + 1)) - φp⁻¹ • ν (t + (j + 1))) ω) := by
    refine ((hs6.sub (hs4.mul_left φp⁻¹)).mul_left (φp / A)).congr fun j => ?_
    rw [hT j, hEterm (j + 1)]
    ring
  have hsT : Summable (fun j => phiT212 ηi χ φp j *
      𝔼.E t (pstar (t + j) - φp⁻¹ • ν (t + j)) ω) := (summable_nat_add_iff 1).mp hsT1
  refine ⟨hsP1, hsT, ?_⟩
  have hT0 : phiT212 ηi χ φp 0 = (1 + k) * φp / A := by simp only [phiT212, ← hA, hk]
  have hP2 : ∑' j, phiT212 ηi χ φp j * 𝔼.E t (pstar (t + j) - φp⁻¹ • ν (t + j)) ω =
      (1 + k) * φp / A * (x 0 - φp⁻¹ * N 0) +
        φp / A * (∑' j, c j * x (j + 1) - φp⁻¹ * ∑' j, c j * N (j + 1)) := by
    rw [hsT.tsum_eq_zero_add, hT0, hEterm 0]
    congr 1
    rw [← tsum_mul_left, ← hs6.tsum_sub (hs4.mul_left φp⁻¹), ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [hT j, hEterm (j + 1)]
    ring
  -- relations among the tsums
  have hS1 : ∑' j, c j * (x (j + 1) - x j) = ∑' j, c j * x (j + 1) - ∑' j, c j * x j := by
    rw [← hs6.tsum_sub hs5]; exact tsum_congr fun j => by ring
  have hS5 : ∑' j, c j * x j = x 0 / A + B / A * ∑' j, c j * x (j + 1) := by
    rw [hs5.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp only [hc]; ring
    · exact tsum_congr fun j => by rw [hcs j]; ring
  have hS3 : ∑' j, c j * N j = N 0 / A + B / A * ∑' j, c j * N (j + 1) := by
    rw [hs3.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp only [hc]; ring
    · exact tsum_congr fun j => by rw [hcs j]; ring
  have hx0 : x 0 = pstar t ω := by simp only [hx, add_zero, ha2 t]
  rw [hPh, hP1, hP2, hS1, hS5, hS3, ← hx0]
  rw [hAm, hBm]
  have hA' : 1 + (1 + k) * φp ≠ 0 := by rw [← hAm]; exact hA0
  field_simp
  ring

/-- Woodford (2003), p. 116: the weights `ϕ_j` (3.18) are positive when
`χ > −1/(φ_p η_i)`, `η_i, φ_p > 0`. -/
theorem phi212_pos {ηi χ φp : ℝ} (hηi : 0 < ηi) (hφ : 0 < φp) (hχ : -1 / (φp * ηi) < χ)
    (j : ℕ) : 0 < phi212 ηi χ φp j := by
  have hB : 0 < B212 ηi χ φp := by
    unfold B212
    rw [div_lt_iff₀ (by positivity)] at hχ
    nlinarith
  have hA : 0 < A212 ηi χ φp := by unfold A212; unfold B212 at hB; nlinarith
  unfold phi212
  positivity

/-- Woodford (2003), p. 116: the weights `ϕ̃_j` (3.19) are positive when
`χ > −1/(φ_p η_i)` and `χ > −1/(2η_i)`. -/
theorem phiT212_pos {ηi χ φp : ℝ} (hηi : 0 < ηi) (hφ : 0 < φp) (hχ : -1 / (φp * ηi) < χ)
    (hχ2 : -1 / (2 * ηi) < χ) (j : ℕ) : 0 < phiT212 ηi χ φp j := by
  have hB : 0 < B212 ηi χ φp := by
    unfold B212
    rw [div_lt_iff₀ (by positivity)] at hχ
    nlinarith
  have hA : 0 < A212 ηi χ φp := by unfold A212; unfold B212 at hB; nlinarith
  have hk : 0 < 1 + ηi * χ := by rw [div_lt_iff₀ (by positivity)] at hχ2; nlinarith
  cases j with
  | zero => simp only [phiT212]; positivity
  | succ j => simp only [phiT212]; positivity

/-- Woodford (2003), p. 116: the weights `ϕ_j` (3.18) sum to one (whenever `|B| < |A|`; an
instance of `ForwardSolution.hasSum_geometric_ratio`, since `A − B = φ_p`). -/
theorem hasSum_phi212 {ηi χ φp : ℝ} (hAB : |B212 ηi χ φp| < |A212 ηi χ φp|) :
    HasSum (phi212 ηi χ φp) 1 := by
  have hsub : A212 ηi χ φp - B212 ηi χ φp = φp := by unfold A212 B212; ring
  have hne : φp ≠ 0 := fun h0 => by
    have : A212 ηi χ φp = B212 ηi χ φp := by linarith
    rw [this] at hAB
    exact lt_irrefl _ hAB
  have h := ForwardSolution.hasSum_geometric_ratio φp hAB
  rw [hsub, div_self hne] at h
  refine h.congr_fun fun j => ?_
  simp only [phi212]
  ring

/-- Woodford (2003), p. 116: the weights `ϕ̃_j` (3.19) sum to one (whenever `|B| < |A|`). -/
theorem hasSum_phiT212 {ηi χ φp : ℝ} (hAB : |B212 ηi χ φp| < |A212 ηi χ φp|) :
    HasSum (phiT212 ηi χ φp) 1 := by
  have h := hasSum_phi212 hAB
  have hA : A212 ηi χ φp ≠ 0 := abs_pos.mp (lt_of_le_of_lt (abs_nonneg _) hAB)
  have h1 : HasSum (fun j => phiT212 ηi χ φp (j + 1)) (A212 ηi χ φp)⁻¹ := by
    have := h.mul_left (A212 ηi χ φp)⁻¹
    rw [mul_one] at this
    refine this.congr_fun fun j => ?_
    simp only [phiT212, phi212]
    field_simp
    ring
  have h0 : phiT212 ηi χ φp 0 + (A212 ηi χ φp)⁻¹ = 1 := by
    simp only [phiT212]
    field_simp
    unfold A212
    ring
  rw [← h0]
  exact h1.zero_add

/-- Woodford (2003), p. 116: at `χ = 0` both weight sequences reduce to the weights
`φ_p(1 + φ_p)^{−(j+1)}` of (1.39). -/
theorem weights212_at_zero (ηi φp : ℝ) (j : ℕ) :
    phi212 ηi 0 φp j = φp / (1 + φp) ^ (j + 1) ∧
      phiT212 ηi 0 φp j = φp / (1 + φp) ^ (j + 1) := by
  constructor
  · simp [phi212, A212, B212]
  · cases j with
    | zero => simp [phiT212, A212]
    | succ j => simp [phiT212, A212, B212]

/-- Woodford (2003), p. 116: for `χ ≠ 0` (and `η_i, φ_p ≠ 0`, `A ≠ 0`) the weight `ϕ̃_0` no
longer equals `ϕ_0`. -/
theorem phiT212_ne_phi212 {ηi χ φp : ℝ} (hηi : ηi ≠ 0) (hχ : χ ≠ 0) (hφ : φp ≠ 0)
    (hA : A212 ηi χ φp ≠ 0) : phiT212 ηi χ φp 0 ≠ phi212 ηi χ φp 0 := by
  simp only [phiT212, phi212, pow_zero, one_mul, zero_add, pow_one]
  intro h
  rw [div_left_inj' hA] at h
  have : ηi * χ * φp = 0 := by linarith
  rcases mul_eq_zero.mp this with h' | h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact hηi h''
    · exact hχ h''
  · exact hφ h'

/-- Woodford (2003), (3.17): the bounded solution as a function of `χ`, when the disturbance is
affine in `χ` (`r̃ = r̂ − χ z` makes the forcing term of (A.32) of the form `g₀ + χ g₁`). -/
noncomputable def sol212 (ηi φp : ℝ) (g0 g1 : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) (χ : ℝ) : ℝ :=
  ∑' j, B212 ηi χ φp ^ j / A212 ηi χ φp ^ (j + 1) * 𝔼.E t (g0 (t + j) + χ • g1 (t + j)) ω

/-- Woodford (2003), (3.17): `sol212` is the forward solution `scalarSol` of (A.32). -/
theorem sol212_eq (ηi φp χ : ℝ) (g0 g1 : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    sol212 𝔼 ηi φp g0 g1 t ω χ =
      scalarSol 𝔼 (A212 ηi χ φp) (B212 ηi χ φp) (fun s => g0 s + χ • g1 s) t ω := by
  rw [scalarSol_apply]
  rfl

/-- Woodford (2003), p. 116 ("the solution (3.17) is also observed to be continuous in `χ`"):
for bounded disturbances `g₀, g₁`, the unique bounded solution is a continuous function of `χ`
on the whole region `χ > −1/(2η_i)` of (3.16) (for fixed `η_i, φ_p > 0`). -/
theorem sol212_continuousOn {ηi φp K : ℝ} (hηi : 0 < ηi) (hφ : 0 < φp) {g0 g1 : ℕ → Ω → ℝ}
    (hg0 : ∀ t ω, |g0 t ω| ≤ K) (hg1 : ∀ t ω, |g1 t ω| ≤ K) (t : ℕ) (ω : Ω) :
    ContinuousOn (sol212 𝔼 ηi φp g0 g1 t ω) (Set.Ioi (-1 / (2 * ηi))) := by
  intro χ0 hχ0
  have hAB0 := abs_B_lt_A hηi hχ0 hφ
  have hpos : ∀ χ, -1 / (2 * ηi) < χ → 1 < A212 ηi χ φp := fun χ hχ => by
    rw [div_lt_iff₀ (by linarith)] at hχ
    unfold A212; nlinarith
  have hA0 : 0 < A212 ηi χ0 φp := by linarith [hpos χ0 hχ0]
  rw [abs_of_pos hA0] at hAB0
  set q := (1 + |B212 ηi χ0 φp| / A212 ηi χ0 φp) / 2 with hq
  have hq1 : q < 1 := by
    have : |B212 ηi χ0 φp| / A212 ηi χ0 φp < 1 := by rw [div_lt_one hA0]; exact hAB0
    rw [hq]; linarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  set U : Set ℝ := {χ | -1 / (2 * ηi) < χ} ∩ ({χ | |B212 ηi χ φp| < q * A212 ηi χ φp} ∩
    {χ | |χ - χ0| < 1}) with hU
  have hUo : IsOpen U := by
    refine (isOpen_lt continuous_const continuous_id).inter
      ((isOpen_lt ?_ ?_).inter (isOpen_lt ?_ continuous_const))
    · unfold B212; fun_prop
    · unfold A212; fun_prop
    · fun_prop
  have hχ0U : χ0 ∈ U := by
    refine ⟨hχ0, ?_, by simp⟩
    change |B212 ηi χ0 φp| < q * A212 ηi χ0 φp
    rw [hq]
    have : |B212 ηi χ0 φp| / A212 ηi χ0 φp * A212 ηi χ0 φp = |B212 ηi χ0 φp| := by
      field_simp
    nlinarith
  have hrw : ∀ χ, sol212 𝔼 ηi φp g0 g1 t ω χ = ∑' j, B212 ηi χ φp ^ j / A212 ηi χ φp ^ (j + 1) *
      (𝔼.E t (g0 (t + j)) ω + χ * 𝔼.E t (g1 (t + j)) ω) := fun χ => by
    unfold sol212
    refine tsum_congr fun j => ?_
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcont : ContinuousOn (fun χ => ∑' j, B212 ηi χ φp ^ j / A212 ηi χ φp ^ (j + 1) *
      (𝔼.E t (g0 (t + j)) ω + χ * 𝔼.E t (g1 (t + j)) ω)) U := by
    refine continuousOn_tsum (u := fun j => q ^ j * (K + (|χ0| + 1) * K)) (fun j => ?_)
      ((summable_geometric_of_lt_one hq0 hq1).mul_right _) (fun j χ hχ => ?_)
    · refine ContinuousOn.mul ?_ (Continuous.continuousOn (by fun_prop))
      refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
        (fun χ hχ => (pow_pos (by linarith [hpos χ hχ.1]) _).ne')
      · unfold B212; fun_prop
      · unfold A212; fun_prop
    · obtain ⟨h1, h2, h3⟩ := hχ
      simp only [Set.mem_ofPred_eq] at h1 h2 h3
      have hA1 := hpos χ h1
      have hK : 0 ≤ K := (abs_nonneg _).trans (hg0 0 ω)
      have hb : |𝔼.E t (g0 (t + j)) ω + χ * 𝔼.E t (g1 (t + j)) ω| ≤ K + (|χ0| + 1) * K := by
        have e0 := 𝔼.abs_E_le (fun ω' => hg0 (t + j) ω') t ω
        have e1 := 𝔼.abs_E_le (fun ω' => hg1 (t + j) ω') t ω
        have hχb : |χ| ≤ |χ0| + 1 := by
          have := abs_sub_abs_le_abs_sub χ χ0
          linarith
        calc _ ≤ |𝔼.E t (g0 (t + j)) ω| + |χ| * |𝔼.E t (g1 (t + j)) ω| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ K + (|χ0| + 1) * K := by
              gcongr
      have hc : |B212 ηi χ φp ^ j / A212 ηi χ φp ^ (j + 1)| ≤ q ^ j := by
        rw [abs_div, abs_pow, abs_pow, abs_of_pos (by linarith : 0 < A212 ηi χ φp),
          div_le_iff₀ (by positivity), pow_succ]
        have : |B212 ηi χ φp| ^ j ≤ (q * A212 ηi χ φp) ^ j :=
          pow_le_pow_left₀ (abs_nonneg _) h2.le j
        rw [mul_pow] at this
        have hqA : 0 ≤ q ^ j * A212 ηi χ φp ^ j :=
          mul_nonneg (pow_nonneg hq0 j) (pow_nonneg (by linarith) j)
        calc |B212 ηi χ φp| ^ j ≤ q ^ j * A212 ηi χ φp ^ j := this
          _ = q ^ j * A212 ηi χ φp ^ j * 1 := by ring
          _ ≤ q ^ j * A212 ηi χ φp ^ j * A212 ηi χ φp :=
              mul_le_mul_of_nonneg_left hA1.le hqA
          _ = q ^ j * (A212 ηi χ φp ^ j * A212 ηi χ φp) := by ring
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hc hb (abs_nonneg _) (pow_nonneg hq0 j)
  have hcont' : ContinuousOn (sol212 𝔼 ηi φp g0 g1 t ω) U := by
    rw [show sol212 𝔼 ηi φp g0 g1 t ω = _ from funext hrw]
    exact hcont
  exact (hcont'.continuousAt (hUo.mem_nhds hχ0U)).continuousWithinAt

/-! ### Proposition 2.13: the generalised Taylor rule (2.12) -/

/-- Woodford (2003), (A.33), p. 646: `γ₀ = (1 + η_iχ)φ_π + ρ`. -/
def gamma0 (ηi χ φπ ρ : ℝ) : ℝ := (1 + ηi * χ) * φπ + ρ

/-- Woodford (2003), (A.33), p. 646: `γ₁ = 1 + η_iχφ_π`. -/
def gamma1 (ηi χ φπ : ℝ) : ℝ := 1 + ηi * χ * φπ

/-- Woodford (2003), eq. (2.12), p. 96: `î_t = ī_t + ρ(î_{t−1} − ī_{t−1}) + φ_π π_t`, with given
initial lags `î_{−1} = ilag`, `ī_{−1} = ibarlag`. -/
def Rule212 (φπ ρ ilag ibarlag : ℝ) (ibar π i : ℕ → Ω → ℝ) : Prop :=
  (i 0 = ibar 0 + (fun (_ : Ω) => ρ * (ilag - ibarlag)) + φπ • π 0) ∧
    ∀ t, i (t + 1) = ibar (t + 1) + ρ • (i t - ibar t) + φπ • π (t + 1)

/-- Woodford (2003), Prop. 2.13, p. 116: the rule (2.12) and (3.12) with `îᵐ = 0`. -/
def Eq213 (ηi χ φπ ρ ilag ibarlag : ℝ) (rt ibar π i : ℕ → Ω → ℝ) : Prop :=
  Rule212 φπ ρ ilag ibarlag ibar π i ∧ Fisher312 𝔼 ηi χ rt (fun t => 𝔼.E t (π (t + 1))) i 0

/-- Woodford (2003), Prop. 2.13: determinacy — for all bounded adapted `r̃, ī` and initial lags
there is exactly one bounded adapted equilibrium `(π, î)`. -/
def Det213 (ηi χ φπ ρ : ℝ) : Prop :=
  ∀ rt ibar : ℕ → Ω → ℝ, BoundedProc rt → BoundedProc ibar → 𝔼.Adapted rt → 𝔼.Adapted ibar →
    ∀ ilag ibarlag : ℝ, ∃! πi : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      BoundedProc πi.1 ∧ BoundedProc πi.2 ∧ 𝔼.Adapted πi.1 ∧ 𝔼.Adapted πi.2 ∧
        Eq213 𝔼 ηi χ φπ ρ ilag ibarlag rt ibar πi.1 πi.2

/-- Woodford (2003), (A.33), p. 646: the forcing term `φ_π r̃_t + ρ ī_t − E_t ī_{t+1}`. -/
def f213 (φπ ρ : ℝ) (rt ibar : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => φπ • rt t + ρ • ibar t - 𝔼.E t (ibar (t + 1))

/-- Woodford (2003), p. 117 ("obtained by inverting (2.12)"): inflation implied by an
interest-rate path, `π_t = φ_π⁻¹(î_t − ī_t − ρ(î_{t−1} − ī_{t−1}))`. -/
noncomputable def piOf (φπ ρ ilag ibarlag : ℝ) (ibar i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => φπ⁻¹ • (i 0 - ibar 0 - fun (_ : Ω) => ρ * (ilag - ibarlag))
  | t + 1 => φπ⁻¹ • (i (t + 1) - ibar (t + 1) - ρ • (i t - ibar t))

/-- Woodford (2003), p. 117: for `φ_π ≠ 0` the rule (2.12) holds iff inflation is `piOf`. -/
theorem rule212_iff {φπ ρ ilag ibarlag : ℝ} (hφ : φπ ≠ 0) {ibar π i : ℕ → Ω → ℝ} :
    Rule212 φπ ρ ilag ibarlag ibar π i ↔ π = piOf φπ ρ ilag ibarlag ibar i := by
  have key : ∀ (a b : Ω → ℝ), a = b + φπ • π 0 ↔ π 0 = φπ⁻¹ • (a - b) := fun a b => by
    rw [funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h; rw [h]; field_simp; ring
  have key' : ∀ t (a b : Ω → ℝ), a = b + φπ • π (t + 1) ↔ π (t + 1) = φπ⁻¹ • (a - b) :=
    fun t a b => by
    rw [funext_iff, funext_iff]
    refine forall_congr' fun ω => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · intro h; rw [h]; field_simp; ring
    · intro h; rw [h]; field_simp; ring
  unfold Rule212
  constructor
  · rintro ⟨h0, hs⟩
    funext t
    cases t with
    | zero =>
      rw [(key _ _).mp h0]
      simp only [piOf]
      congr 1
      abel
    | succ t =>
      rw [(key' t _ _).mp (hs t)]
      simp only [piOf]
      congr 1
      abel
  · intro h
    subst h
    refine ⟨(key _ _).mpr ?_, fun t => (key' t _ _).mpr ?_⟩
    · simp only [piOf]
      congr 1
      abel
    · simp only [piOf]
      congr 1
      abel

/-- Woodford (2003), **(A.33)**, p. 646: for `φ_π ≠ 0` and adapted `î`, `ī`, the equilibrium
conditions of Prop. 2.13 hold iff inflation is `piOf î` and `î` solves
`γ₀ î_t = γ₁ E_t î_{t+1} + φ_π r̃_t + ρ ī_t − E_t ī_{t+1}`. -/
theorem eq213_iff {ηi χ φπ ρ ilag ibarlag : ℝ} (hφ : φπ ≠ 0) {rt ibar π i : ℕ → Ω → ℝ}
    (hai : 𝔼.Adapted i) (haib : 𝔼.Adapted ibar) :
    Eq213 𝔼 ηi χ φπ ρ ilag ibarlag rt ibar π i ↔
      ScalarEq 𝔼 (gamma0 ηi χ φπ ρ) (gamma1 ηi χ φπ) (f213 𝔼 φπ ρ rt ibar) i ∧
        π = piOf φπ ρ ilag ibarlag ibar i := by
  unfold Eq213
  rw [rule212_iff hφ, and_comm]
  refine and_congr_left fun hπ => ?_
  subst hπ
  unfold Fisher312 ScalarEq
  refine forall_congr' fun t => ?_
  have hE : 𝔼.E t (piOf φπ ρ ilag ibarlag ibar i (t + 1)) =
      φπ⁻¹ • (𝔼.E t (i (t + 1)) - 𝔼.E t (ibar (t + 1)) - ρ • (i t - ibar t)) := by
    simp only [piOf, map_smul, map_sub, hai t, haib t]
  beta_reduce
  rw [hE, funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [f213, gamma0, gamma1, map_zero, Pi.zero_apply, sub_zero, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    field_simp
    linear_combination h

/-- Woodford (2003), A.13: `piOf` of a bounded adapted interest-rate path is bounded and
adapted. -/
theorem piOf_bounded_adapted {φπ ρ ilag ibarlag : ℝ} {ibar i : ℕ → Ω → ℝ}
    (hi : BoundedProc i) (hib : BoundedProc ibar) (hai : 𝔼.Adapted i)
    (haib : 𝔼.Adapted ibar) :
    BoundedProc (piOf φπ ρ ilag ibarlag ibar i) ∧
      𝔼.Adapted (piOf φπ ρ ilag ibarlag ibar i) := by
  obtain ⟨K1, h1⟩ := hi
  obtain ⟨K2, h2⟩ := hib
  constructor
  · refine ⟨|φπ⁻¹| * (K1 + K2 + |ρ| * (K1 + K2) + |ρ * (ilag - ibarlag)|), fun t ω => ?_⟩
    cases t with
    | zero =>
      simp only [piOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := abs_sub (i 0 ω - ibar 0 ω) (ρ * (ilag - ibarlag))
      have := abs_sub (i 0 ω) (ibar 0 ω)
      have := mul_nonneg (abs_nonneg ρ) (add_nonneg ((abs_nonneg _).trans (h1 0 ω))
        ((abs_nonneg _).trans (h2 0 ω)))
      have := abs_mul ρ (ilag - ibarlag)
      linarith [h1 0 ω, h2 0 ω]
    | succ t =>
      simp only [piOf, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have a1 := abs_sub (i (t + 1) ω - ibar (t + 1) ω) (ρ * (i t ω - ibar t ω))
      have a2 := abs_sub (i (t + 1) ω) (ibar (t + 1) ω)
      have a3 : |ρ * (i t ω - ibar t ω)| ≤ |ρ| * (K1 + K2) := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          ((abs_sub _ _).trans (add_le_add (h1 t ω) (h2 t ω))) (abs_nonneg _)
      have := mul_nonneg (abs_nonneg ρ) (abs_nonneg (ilag - ibarlag))
      linarith [h1 (t + 1) ω, h2 (t + 1) ω]
  · intro t
    cases t with
    | zero => simp only [piOf, map_smul, map_sub, hai 0, haib 0, 𝔼.const]
    | succ t =>
      have k1 : 𝔼.E (t + 1) (i t) = i t := by
        conv_lhs => rw [← hai t]
        rw [𝔼.known (Nat.le_succ t), hai t]
      have k2 : 𝔼.E (t + 1) (ibar t) = ibar t := by
        conv_lhs => rw [← haib t]
        rw [𝔼.known (Nat.le_succ t), haib t]
      simp only [piOf, map_smul, map_sub, hai (t + 1), haib (t + 1), k1, k2]

/-- Woodford (2003), A.13: the forcing term of (A.33) is bounded and adapted. -/
theorem f213_bounded_adapted {φπ ρ : ℝ} {rt ibar : ℕ → Ω → ℝ} (hrt : BoundedProc rt)
    (hib : BoundedProc ibar) (hart : 𝔼.Adapted rt) (haib : 𝔼.Adapted ibar) :
    BoundedProc (f213 𝔼 φπ ρ rt ibar) ∧ 𝔼.Adapted (f213 𝔼 φπ ρ rt ibar) := by
  obtain ⟨K1, h1⟩ := hrt
  obtain ⟨K2, h2⟩ := hib
  constructor
  · refine ⟨|φπ| * K1 + |ρ| * K2 + K2, fun t ω => ?_⟩
    simp only [f213, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have e := 𝔼.abs_E_le (fun ω' => h2 (t + 1) ω') t ω
    have a1 : |φπ * rt t ω| ≤ |φπ| * K1 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h1 t ω) (abs_nonneg _)
    have a2 : |ρ * ibar t ω| ≤ |ρ| * K2 := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h2 t ω) (abs_nonneg _)
    have := abs_sub (φπ * rt t ω + ρ * ibar t ω) (𝔼.E t (ibar (t + 1)) ω)
    have := abs_add_le (φπ * rt t ω) (ρ * ibar t ω)
    linarith
  · intro t
    simp only [f213, map_add, map_sub, map_smul, hart t, haib t, 𝔼.E_E_self]

/-- Woodford (2003), A.13, p. 646 (exact determinacy condition, for any `φ_π ≠ 0`): the economy
of Prop. 2.13 is determinate iff `|γ₁| < |γ₀|`. -/
theorem det213_iff [Nonempty Ω] {ηi χ φπ ρ : ℝ} (hφ : φπ ≠ 0) :
    Det213 𝔼 ηi χ φπ ρ ↔ |gamma1 ηi χ φπ| < |gamma0 ηi χ φπ ρ| := by
  constructor
  · intro hdet
    by_contra hc
    push Not at hc
    have hz : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
    have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
    by_cases hg1 : gamma1 ηi χ φπ = 0
    · -- then `γ₀ = 0`: the forcing `φ_π` cannot be matched
      have hg0 : gamma0 ηi χ φπ ρ = 0 := by
        rw [hg1, abs_zero] at hc; exact abs_nonpos_iff.mp hc
      have h1a : 𝔼.Adapted (fun _ _ => (1 : ℝ)) := fun t => 𝔼.const t 1
      obtain ⟨⟨π, i⟩, ⟨-, -, -, hai, he⟩, -⟩ :=
        hdet (fun _ _ => 1) 0 ⟨1, fun _ _ => by simp⟩ hzb h1a hz 0 0
      have hs := ((eq213_iff 𝔼 hφ hai hz).mp he).1 0
      rw [hg0, hg1] at hs
      obtain ⟨ω⟩ := ‹Nonempty Ω›
      have := congrFun hs ω
      simp [f213] at this
      exact hφ this.symm
    · obtain ⟨hh, hhb⟩ := scalar_homog 𝔼 hc hg1
      have hha : 𝔼.Adapted (fun t (_ : Ω) => (gamma0 ηi χ φπ ρ / gamma1 ηi χ φπ) ^ t) :=
        fun t => 𝔼.const t _
      have hf0 : f213 𝔼 φπ ρ 0 0 = 0 := by funext t ω; simp [f213]
      obtain ⟨_, -, hu⟩ := hdet 0 0 hzb hzb hz hz 0 0
      have s1 : Eq213 𝔼 ηi χ φπ ρ 0 0 0 0 (piOf φπ ρ 0 0 0 0) 0 :=
        (eq213_iff 𝔼 hφ hz hz).mpr ⟨fun t => by simp [hf0], rfl⟩
      have s2 : Eq213 𝔼 ηi χ φπ ρ 0 0 0 0 (piOf φπ ρ 0 0 0 (fun t _ =>
          (gamma0 ηi χ φπ ρ / gamma1 ηi χ φπ) ^ t)) (fun t _ =>
          (gamma0 ηi χ φπ ρ / gamma1 ηi χ φπ) ^ t) :=
        (eq213_iff 𝔼 hφ hha hz).mpr ⟨by rw [hf0]; exact hh, rfl⟩
      obtain ⟨hb1, ha1⟩ := piOf_bounded_adapted 𝔼 (φπ := φπ) (ρ := ρ) (ilag := 0)
        (ibarlag := 0) hzb hzb hz hz
      obtain ⟨hb2, ha2⟩ := piOf_bounded_adapted 𝔼 (φπ := φπ) (ρ := ρ) (ilag := 0)
        (ibarlag := 0) hhb hzb hha hz
      have e1 := hu (piOf φπ ρ 0 0 0 0, 0) ⟨hb1, hzb, ha1, hz, s1⟩
      have e2 := hu (piOf φπ ρ 0 0 0 (fun t _ => (gamma0 ηi χ φπ ρ / gamma1 ηi χ φπ) ^ t),
        fun t _ => (gamma0 ηi χ φπ ρ / gamma1 ηi χ φπ) ^ t) ⟨hb2, hhb, ha2, hha, s2⟩
      have := congrArg Prod.snd (e2.trans e1.symm)
      obtain ⟨ω⟩ := ‹Nonempty Ω›
      have := congrFun (congrFun this 0) ω
      simp at this
  · intro h rt ibar hrt hib hart haib ilag ibarlag
    obtain ⟨hfb, hfa⟩ := f213_bounded_adapted 𝔼 (φπ := φπ) (ρ := ρ) hrt hib hart haib
    obtain ⟨Kf, hKf⟩ := hfb
    obtain ⟨hs, hb, ha, hu⟩ := scalar_existsUnique 𝔼 h hKf hfa
    obtain ⟨hpb, hpa⟩ := piOf_bounded_adapted 𝔼 (φπ := φπ) (ρ := ρ) (ilag := ilag)
      (ibarlag := ibarlag) hb hib ha haib
    refine ⟨(piOf φπ ρ ilag ibarlag ibar (scalarSol 𝔼 _ _ (f213 𝔼 φπ ρ rt ibar)),
      scalarSol 𝔼 _ _ (f213 𝔼 φπ ρ rt ibar)), ⟨hpb, hb, hpa, ha,
      (eq213_iff 𝔼 hφ ha haib).mpr ⟨hs, rfl⟩⟩, ?_⟩
    rintro ⟨π, i⟩ ⟨-, hbi, -, hai, he⟩
    obtain ⟨hsi, hπ⟩ := (eq213_iff 𝔼 hφ hai haib).mp he
    have hi := hu i hsi hbi
    simp only at hi hπ
    rw [hπ, hi]

/-- Woodford (2003), Prop. 2.13 and p. 97 ("determinacy requires `φ_π ≠ 0`"): with `φ_π = 0` the
equilibrium is never determinate — inflation at date 0 is left free. -/
theorem not_det213_zero [Nonempty Ω] (ηi χ ρ : ℝ) : ¬ Det213 𝔼 ηi χ 0 ρ := by
  intro hdet
  have hz : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => by simp
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  obtain ⟨_, -, hu⟩ := hdet 0 0 hzb hzb hz hz 0 0
  set δ : ℕ → Ω → ℝ := fun t _ => if t = 0 then 1 else 0 with hδ
  have hδa : 𝔼.Adapted δ := fun t => 𝔼.const t _
  have hδb : BoundedProc δ := ⟨1, fun t _ => by simp only [hδ]; split_ifs <;> simp⟩
  have hsol : ∀ π : ℕ → Ω → ℝ, (∀ t, π (t + 1) = 0) →
      Eq213 𝔼 ηi χ 0 ρ 0 0 0 0 π 0 := fun π hπ => by
    refine ⟨⟨?_, fun t => ?_⟩, fun t => ?_⟩
    · funext ω; simp
    · funext ω; simp
    · funext ω; simp [hπ t]
  have e1 := hu (0, 0) ⟨hzb, hzb, hz, hz, hsol 0 fun _ => rfl⟩
  have e2 := hu (δ, 0) ⟨hδb, hzb, hδa, hz, hsol δ fun t => by
    funext ω; simp [hδ]⟩
  have := congrArg Prod.fst (e2.trans e1.symm)
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun this 0) ω
  simp [hδ] at this

/-- Woodford (2003), A.13, p. 646: `γ₀ − γ₁ = φ_π + ρ − 1`. -/
theorem gamma_sub (ηi χ φπ ρ : ℝ) : gamma0 ηi χ φπ ρ - gamma1 ηi χ φπ = φπ + ρ - 1 := by
  unfold gamma0 gamma1; ring

/-- Woodford (2003), A.13, p. 646: under (3.16), `φ_π, ρ ≥ 0`, `γ₀ + γ₁ > 0`. -/
theorem gamma_add_pos {ηi χ φπ ρ : ℝ} (hηi : 0 < ηi) (hχ : -1 / (2 * ηi) < χ) (hφ : 0 ≤ φπ)
    (hρ : 0 ≤ ρ) : 0 < gamma0 ηi χ φπ ρ + gamma1 ηi χ φπ := by
  have h1 : 0 < 1 + 2 * ηi * χ := by
    rw [div_lt_iff₀ (by linarith)] at hχ; linarith
  unfold gamma0 gamma1
  nlinarith

/-- Woodford (2003), **Proposition 2.13**, pp. 116–117 and A.13: with `η_i > 0`, `φ_π, ρ ≥ 0` and
`χ > −1/(2η_i)` (3.16), equilibrium is determinate if and only if `φ_π > 0` and
`φ_π + ρ > 1` (2.13). -/
theorem prop_2_13 [Nonempty Ω] {ηi χ φπ ρ : ℝ} (hηi : 0 < ηi) (hχ : -1 / (2 * ηi) < χ)
    (hφ : 0 ≤ φπ) (hρ : 0 ≤ ρ) : Det213 𝔼 ηi χ φπ ρ ↔ 0 < φπ ∧ 1 < φπ + ρ := by
  rcases hφ.lt_or_eq with hφ' | hφ'
  · rw [det213_iff 𝔼 hφ'.ne',
      ForwardSolution.abs_lt_abs_iff_of_add_pos (gamma_add_pos hηi hχ hφ hρ)]
    have := gamma_sub ηi χ φπ ρ
    constructor
    · intro h; exact ⟨hφ', by linarith⟩
    · intro h; linarith [h.2]
  · subst hφ'
    simp only [lt_irrefl, false_and, iff_false]
    exact not_det213_zero 𝔼 ηi χ ρ

/-- Woodford (2003), eq. (3.21), p. 117: `ϕ_j = γ₁ʲ / γ₀^{j+1}`. -/
noncomputable def phi213 (ηi χ φπ ρ : ℝ) (j : ℕ) : ℝ :=
  gamma1 ηi χ φπ ^ j / gamma0 ηi χ φπ ρ ^ (j + 1)

/-- Woodford (2003), eq. (3.22), p. 117: `ϕ̃_0 = (1 + η_iχ)/γ₀`,
`ϕ̃_j = [1 + (1 − ρ)η_iχ] γ₁ʲ⁻¹/γ₀^{j+1}` for `j ≥ 1`. -/
noncomputable def phiT213 (ηi χ φπ ρ : ℝ) : ℕ → ℝ
  | 0 => (1 + ηi * χ) / gamma0 ηi χ φπ ρ
  | j + 1 => (1 + (1 - ρ) * ηi * χ) * gamma1 ηi χ φπ ^ j / gamma0 ηi χ φπ ρ ^ (j + 2)

/-- Woodford (2003), **(3.20)**, p. 117 (A.13, "applying (A.16) again"): for the unique bounded
solution `î` of (A.33) (with `φ_π ≠ 0`),
`φ_π⁻¹(î_t − ī_t) = ∑ ϕ_j E_t r̃_{t+j} − ∑ ϕ̃_j E_t ī_{t+j}`;
hence, by `piOf`, `π_t = −(ρ/φ_π)(î_{t−1} − ī_{t−1}) + ∑ ϕ_j E_t r̃_{t+j} − ∑ ϕ̃_j E_t ī_{t+j}`. -/
theorem gap213_formula {ηi χ φπ ρ K1 K2 : ℝ} (hφ : φπ ≠ 0)
    (hg : |gamma1 ηi χ φπ| < |gamma0 ηi χ φπ ρ|) {rt ibar : ℕ → Ω → ℝ}
    (h1 : ∀ t ω, |rt t ω| ≤ K1) (h2 : ∀ t ω, |ibar t ω| ≤ K2) (haib : 𝔼.Adapted ibar)
    (t : ℕ) (ω : Ω) :
    Summable (fun j => phi213 ηi χ φπ ρ j * 𝔼.E t (rt (t + j)) ω) ∧
      Summable (fun j => phiT213 ηi χ φπ ρ j * 𝔼.E t (ibar (t + j)) ω) ∧
      φπ⁻¹ * (scalarSol 𝔼 (gamma0 ηi χ φπ ρ) (gamma1 ηi χ φπ) (f213 𝔼 φπ ρ rt ibar) t ω -
        ibar t ω) =
        ∑' j, phi213 ηi χ φπ ρ j * 𝔼.E t (rt (t + j)) ω -
          ∑' j, phiT213 ηi χ φπ ρ j * 𝔼.E t (ibar (t + j)) ω := by
  set g0 := gamma0 ηi χ φπ ρ with hg0
  set g1 := gamma1 ηi χ φπ with hg1
  have hA0 : g0 ≠ 0 := abs_pos.mp (lt_of_le_of_lt (abs_nonneg _) hg)
  have hg0m : g0 = (1 + ηi * χ) * φπ + ρ := rfl
  have hg1m : g1 = 1 + ηi * χ * φπ := rfl
  clear_value g0 g1
  set R : ℕ → ℝ := fun j => 𝔼.E t (rt (t + j)) ω with hR
  set N : ℕ → ℝ := fun j => 𝔼.E t (ibar (t + j)) ω with hN
  have hRb : ∀ j, |R j| ≤ K1 := fun j => 𝔼.abs_E_le (fun ω' => h1 (t + j) ω') t ω
  have hNb : ∀ j, |N j| ≤ K2 := fun j => 𝔼.abs_E_le (fun ω' => h2 (t + j) ω') t ω
  have hNb1 : ∀ j, |N (j + 1)| ≤ K2 := fun j => hNb (j + 1)
  set c : ℕ → ℝ := fun j => g1 ^ j / g0 ^ (j + 1) with hc
  have hs2 : Summable (fun j => c j * R j) := summable_c_bdd hg hRb
  have hs3 : Summable (fun j => c j * N j) := summable_c_bdd hg hNb
  have hs4 : Summable (fun j => c j * N (j + 1)) := summable_c_bdd hg hNb1
  have hcs : ∀ j, c (j + 1) = g1 / g0 * c j := fun j => by
    simp only [hc]; field_simp; ring
  have hEf : ∀ j, 𝔼.E t (f213 𝔼 φπ ρ rt ibar (t + j)) ω = φπ * R j + ρ * N j - N (j + 1) :=
    fun j => by
    simp only [f213, hR, hN, map_add, map_sub, map_smul, 𝔼.tower (Nat.le_add_right t j),
      Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show t + (j + 1) = t + j + 1 by omega]
  have hI : scalarSol 𝔼 g0 g1 (f213 𝔼 φπ ρ rt ibar) t ω =
      φπ * ∑' j, c j * R j + ρ * ∑' j, c j * N j - ∑' j, c j * N (j + 1) := by
    rw [scalarSol_apply]
    have H := ((hs2.hasSum.mul_left φπ).add (hs3.hasSum.mul_left ρ)).sub hs4.hasSum
    refine HasSum.tsum_eq ?_
    convert H using 1
    funext j
    rw [hEf j]
    simp only [hc]
    ring
  have hphi : ∀ j, phi213 ηi χ φπ ρ j * R j = c j * R j := fun j => by
    simp only [phi213, ← hg0, ← hg1, hc]
  have hT : ∀ j, phiT213 ηi χ φπ ρ (j + 1) = (1 + (1 - ρ) * ηi * χ) / g0 * c j := fun j => by
    simp only [phiT213, ← hg0, ← hg1, hc]; field_simp; ring
  have hsT1 : Summable (fun j => phiT213 ηi χ φπ ρ (j + 1) * 𝔼.E t (ibar (t + (j + 1))) ω) :=
    (hs4.mul_left ((1 + (1 - ρ) * ηi * χ) / g0)).congr fun j => by rw [hT j]; ring
  have hsT : Summable (fun j => phiT213 ηi χ φπ ρ j * 𝔼.E t (ibar (t + j)) ω) :=
    (summable_nat_add_iff 1).mp hsT1
  refine ⟨hs2.congr fun j => (hphi j).symm, hsT, ?_⟩
  have hP2 : ∑' j, phiT213 ηi χ φπ ρ j * 𝔼.E t (ibar (t + j)) ω =
      (1 + ηi * χ) / g0 * N 0 + (1 + (1 - ρ) * ηi * χ) / g0 * ∑' j, c j * N (j + 1) := by
    rw [hsT.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp only [phiT213, ← hg0, hN]
    · exact tsum_congr fun j => by rw [hT j]; ring
  have hS3 : ∑' j, c j * N j = N 0 / g0 + g1 / g0 * ∑' j, c j * N (j + 1) := by
    rw [hs3.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp only [hc]; ring
    · exact tsum_congr fun j => by rw [hcs j]; ring
  have hN0 : N 0 = ibar t ω := by simp only [hN, add_zero, haib t]
  rw [hI, tsum_congr hphi, hP2, hS3, ← hN0, hg1m]
  have hρ : ρ = g0 - (1 + ηi * χ) * φπ := by linarith [hg0m]
  subst hρ
  field_simp
  ring

/-- Woodford (2003), p. 117: the weights (3.21)–(3.22) are all positive if `0 ≤ ρ ≤ 1`, `φ_π > 0`,
`χ > −1/(2η_i)` and `χ > −1/(φ_π η_i)` ("if `ρ ≤ 1` and `χ` is not too negative"). -/
theorem weights213_pos {ηi χ φπ ρ : ℝ} (hηi : 0 < ηi) (hφ : 0 < φπ) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (hχ2 : -1 / (2 * ηi) < χ) (hχ : -1 / (φπ * ηi) < χ) (j : ℕ) :
    0 < phi213 ηi χ φπ ρ j ∧ 0 < phiT213 ηi χ φπ ρ j := by
  have hk : 0 < 1 + 2 * ηi * χ := by rw [div_lt_iff₀ (by linarith)] at hχ2; linarith
  have hk1 : 0 < 1 + ηi * χ := by nlinarith
  have hB : 0 < gamma1 ηi χ φπ := by
    unfold gamma1
    rw [div_lt_iff₀ (by positivity)] at hχ
    nlinarith
  have hA : 0 < gamma0 ηi χ φπ ρ := by unfold gamma0; positivity
  have hκ : 0 < 1 + (1 - ρ) * ηi * χ := by
    rcases le_or_gt 0 χ with h | h
    · have : 0 ≤ (1 - ρ) * ηi * χ := by
        have := mul_nonneg (sub_nonneg.mpr hρ1) hηi.le
        exact mul_nonneg this h
      linarith
    · have h4 : 0 ≤ ρ * (ηi * -χ) := mul_nonneg hρ0 (mul_nonneg hηi.le (by linarith))
      have : ηi * χ ≤ (1 - ρ) * ηi * χ := by nlinarith
      linarith
  constructor
  · unfold phi213; positivity
  · cases j with
    | zero => simp only [phiT213]; positivity
    | succ j => simp only [phiT213]; positivity

/-- Woodford (2003), p. 117: at `χ = 0`, (3.20) reduces to (2.14): both weight sequences become
`(φ_π + ρ)^{−(j+1)}`. -/
theorem weights213_at_zero (ηi φπ ρ : ℝ) (j : ℕ) :
    phi213 ηi 0 φπ ρ j = 1 / (φπ + ρ) ^ (j + 1) ∧
      phiT213 ηi 0 φπ ρ j = 1 / (φπ + ρ) ^ (j + 1) := by
  constructor
  · simp [phi213, gamma0, gamma1]
  · cases j with
    | zero => simp [phiT213, gamma0]
    | succ j => simp [phiT213, gamma0, gamma1]

end Woodford.PriceLevelDetermination.NonSeparable
