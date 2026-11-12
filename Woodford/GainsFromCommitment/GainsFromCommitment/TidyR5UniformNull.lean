/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.NoninertialMeasureIID
import Mathlib.Analysis.Real.Cardinality

/-!
# One null set for all competing plans

Woodford (2003), *Interest and Prices*, Chapter 7, §3 (pp. 509–513: the stabilization loss
`L^stab`, (3.4), (3.7)–(3.8), Proposition 7.11) and Appendix F.4 (pp. 713–714).

NoninertialMeasure proves the variance results with Mathlib's conditional variance
`Var[· ; μ | 𝓕 t]`: for **each** competing plan the ranking holds off a null set that may depend on
the plan ("`∀ plan, ∀ᵐ ω`"). Whether one null set can serve all (uncountably many) plans at once
("`∀ᵐ ω, ∀ plan`") is decided here.

## The answer

* **Not as a property of `L^stab` itself.** A conditional variance is only defined up to a null
  set, so `L^stab` of a plan is an equivalence class of functions. On the fair-coin economy (every
  history null) there is a choice of versions — each one a.e. equal to the plan's `L^stab` — for
  which **no** null set works: at **every** state some feasible plan beats the optimal
  noninertial plan (`versions_no_uniform_null`). (The versions are built from an injection of the
  state space into `ℝ`, `stateToReal_injective`.)
* **Yes for the regular version.** Build every plan's conditional variance bilinearly from the
  three basis conditional covariances `E_{t₀}[(u_{t₀+k} − ρ_uᵏu_{t₀})(r_{t₀+k} − ρ_rᵏr_{t₀})]`
  (`bCov`, `regVar`, `regLstab`, `regLstab12`). These are versions (`regLstab_version`,
  `regLstab12_version`), and **one** null set — a countable union fixed before any plan is
  chosen — serves every plan: (3.4) (`regLstab12_uniform`), (3.7)–(3.8)
  (`regLstab_uniform`), Proposition 7.11 (`prop_7_11_uniform`) and F.4 (`f4_uniform`) hold for
  all plans simultaneously, including the equality case, pointwise off that set.
* **No null set at all for the expected loss.** As numbers,
  `∫ L^stab dμ` equals the closed forms (3.4), (3.7)–(3.8) for every plan (`lstab12_integral`,
  `lstab_integral`), and the rankings and equality cases of Prop. 7.11 and F.4 hold as
  inequalities between real numbers for all plans (`prop_7_11_integral`, `f4_integral`).
-/

namespace Woodford.GainsFromCommitment.TidyR5UniformNull

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID NoninertialMeasure
open VarianceFrontier (plan2 plan2_apply)
open Noninertial (plan1 fpiOni fxOni uncondVar objF4)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The regular version -/

/-- Woodford (2003), pp. 509, 512 (the basis conditional covariances): the conditional
covariance at `t₀` of the `k`-step forecast errors of two AR(1) disturbances,
`E_{t₀}[(X_{t₀+k} − ρ_Xᵏ X_{t₀})(Y_{t₀+k} − ρ_Yᵏ Y_{t₀})]`, one fixed function per `k`. -/
noncomputable def bCov (ρx ρy : ℝ) (X Y : ℕ → Ω → ℝ) (t₀ k : ℕ) : Ω → ℝ :=
  S.E t₀ ((X (t₀ + k) - ρx ^ k • X t₀) * (Y (t₀ + k) - ρy ^ k • Y t₀))

/-- Woodford (2003), p. 512 (the regular conditional variance of a plan (3.6)): for
`y = ȳ + f u + g r̂ⁿ`, `f² cov(u, u) + 2 f g cov(u, r) + g² cov(r, r)` built from `bCov`. -/
noncomputable def regVar (ρu ρr : ℝ) (u r : ℕ → Ω → ℝ) (t₀ k : ℕ) (f g : ℝ) (ω : Ω) : ℝ :=
  f ^ 2 * bCov S ρu ρu u u t₀ k ω + 2 * f * g * bCov S ρu ρr u r t₀ k ω +
    g ^ 2 * bCov S ρr ρr r r t₀ k ω

/-- Woodford (2003), p. 512 (the regular version of `L^stab` for the loss (2.24)) for the plan
(3.6) with responses `(f_π, f_x, f_i)` to `u` and `(g_π, g_x, g_i)` to `r̂ⁿ`. -/
noncomputable def regLstab (β lx li ρu ρr : ℝ) (u r : ℕ → Ω → ℝ) (t₀ : ℕ)
    (fπ fx fi gπ gx gi : ℝ) (ω : Ω) : ℝ :=
  ∑' k, β ^ k * (regVar S ρu ρr u r t₀ k fπ gπ ω + lx * regVar S ρu ρr u r t₀ k fx gx ω +
    li * regVar S ρu ρr u r t₀ k fi gi ω)

/-- Woodford (2003), p. 509 (the regular version of `L^stab` for the loss (1.2)) for the plan
(2.19) with responses `(f_π, f_x)` to `u`. -/
noncomputable def regLstab12 (β lam ρ : ℝ) (u : ℕ → Ω → ℝ) (t₀ : ℕ) (fπ fx : ℝ) (ω : Ω) : ℝ :=
  ∑' k, β ^ k * (fπ ^ 2 * bCov S ρ ρ u u t₀ k ω + lam * (fx ^ 2 * bCov S ρ ρ u u t₀ k ω))

/-- Woodford (2003), pp. 509, 512: **one** null set, fixed before any plan is chosen (a countable
union over `k`), off which all three basis covariances take their closed forms at every
horizon. -/
theorem bCov_good {ρu ρr su sr c : ℝ} {u εu r εr : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρu su u εu) (hr : MeasAR1Innov S ρr sr r εr)
    (hc : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => c) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ k,
      bCov S ρu ρu u u t₀ k ω = su * ∑ j ∈ Finset.range k, (ρu * ρu) ^ j ∧
      bCov S ρu ρr u r t₀ k ω = c * ∑ j ∈ Finset.range k, (ρu * ρr) ^ j ∧
      bCov S ρr ρr r r t₀ k ω = sr * ∑ j ∈ Finset.range k, (ρr * ρr) ^ j := by
  rw [ae_all_iff]
  intro k
  filter_upwards [E_cross_dev S hu hu hu.2.2.2.2 t₀ k, E_cross_dev S hu hr hc t₀ k,
    E_cross_dev S hr hr hr.2.2.2.2 t₀ k] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Equations (3.7)–(3.8), uniformly** (Woodford (2003), p. 513): with uncorrelated innovations,
off one null set, for **every** plan (3.6) simultaneously, the regular `L^stab` is the discounted
sum with value `L^{stab,r} + L^{stab,u}`. -/
theorem regLstab_uniform {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρu : |ρu| < 1) (hρr : |ρr| < 1) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ fπ fx fi gπ gx gi : ℝ,
      HasSum (fun k => β ^ k * (regVar S ρu ρr u r t₀ k fπ gπ ω +
        lx * regVar S ρu ρr u r t₀ k fx gx ω + li * regVar S ρu ρr u r t₀ k fi gi ω))
      (β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su) := by
  obtain ⟨hu0, hu1⟩ := sq_lt_one_of_abs hρu
  obtain ⟨hr0, hr1⟩ := sq_lt_one_of_abs hρr
  filter_upwards [bCov_good S hu hr hind t₀] with ω hω
  intro fπ fx fi gπ gx gi
  have hGu := (Noninertial.hasSum_disc_geomSum hβ0 hβ1 hu0 hu1).mul_left
    (su * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2))
  have hGr := (Noninertial.hasSum_disc_geomSum hβ0 hβ1 hr0 hr1).mul_left
    (sr * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2))
  convert hGr.add hGu using 1
  · funext k
    obtain ⟨h1, h2, h3⟩ := hω k
    simp only [regVar, h1, h2, h3, ← pow_two]
    ring
  · unfold uncondVar
    have : 1 - ρu ^ 2 ≠ 0 := by linarith
    have : 1 - ρr ^ 2 ≠ 0 := by linarith
    have : 1 - β ≠ 0 := by linarith
    have : 1 - β * ρu ^ 2 ≠ 0 := by nlinarith
    have : 1 - β * ρr ^ 2 ≠ 0 := by nlinarith
    field_simp

/-- Woodford (2003), (3.7)–(3.8), p. 513 (the uniform identity as a value). -/
theorem regLstab_eq_uniform {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρu : |ρu| < 1) (hρr : |ρr| < 1) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ fπ fx fi gπ gx gi : ℝ, regLstab S β lx li ρu ρr u r t₀ fπ fx fi gπ gx gi ω =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su := by
  filter_upwards [regLstab_uniform S hβ0 hβ1 hρu hρr hu hr hind t₀ (lx := lx) (li := li)]
    with ω h fπ fx fi gπ gx gi
  exact (h fπ fx fi gπ gx gi).tsum_eq

/-- Woodford (2003), p. 512: the regular `L^stab` is a version of Mathlib's `L^stab` of every plan
(3.6): the two agree almost surely, plan by plan. -/
theorem regLstab_version {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρu : |ρu| < 1) (hρr : |ρr| < 1) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) (t₀ : ℕ)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) :
    regLstab S β lx li ρu ρr u r t₀ fπ fx fi gπ gx gi =ᵐ[S.μ]
      mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r) := by
  filter_upwards [regLstab_eq_uniform S hβ0 hβ1 hρu hρr hu hr hind t₀ (lx := lx) (li := li),
    lstab_eq S hβ0 hβ1 hρu hρr hu hr hind πbar xbar ibar fπ fx fi gπ gx gi t₀ (lx := lx)
      (li := li)] with ω h1 h2
  rw [h1, h2]

/-- **Equation (3.4), uniformly** (Woodford (2003), p. 511): off one null set, for every plan
(2.19) simultaneously, the regular `L^stab` equals
`β/(1 − β) · (1 − ρ²)/(1 − βρ²) · (f_π² + λ f_x²) σ_u²`. -/
theorem regLstab12_uniform {β lam ρ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ fπ fx : ℝ, regLstab12 S β lam ρ u t₀ fπ fx ω =
      β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
        uncondVar ρ s := by
  obtain ⟨hq0, hq1⟩ := sq_lt_one_of_abs hρ
  filter_upwards [bCov_good S hu hu hu.2.2.2.2 t₀] with ω hω fπ fx
  have hG := (Noninertial.hasSum_disc_geomSum hβ0 hβ1 hq0 hq1).mul_left
    (s * (fπ ^ 2 + lam * fx ^ 2))
  refine HasSum.tsum_eq ?_
  convert hG using 1
  · funext k
    rw [(hω k).1, ← pow_two]
    ring
  · unfold uncondVar
    have : 1 - ρ ^ 2 ≠ 0 := by linarith
    have : 1 - β ≠ 0 := by linarith
    have : 1 - β * ρ ^ 2 ≠ 0 := by nlinarith
    field_simp

/-- Woodford (2003), p. 509: the regular `L^stab` is a version of Mathlib's `L^stab` of every plan
(2.19). -/
theorem regLstab12_version {β lam ρ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (t₀ : ℕ) (πbar xbar fπ fx : ℝ) :
    regLstab12 S β lam ρ u t₀ fπ fx =ᵐ[S.μ]
      mLstab12 S β lam t₀ (plan1 πbar fπ u) (plan1 xbar fx u) := by
  filter_upwards [regLstab12_uniform S hβ0 hβ1 hρ hu t₀ (lam := lam),
    lstab12_eq S hβ0 hβ1 hρ hu πbar xbar fπ fx t₀ (lam := lam)] with ω h1 h2
  rw [h1 fπ fx, h2]

/-! ### The rankings off one null set -/

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (3.5), p. 511 (the numerical core of Prop. 7.11): with `K > 0`, among
`(g_π, g_x)` satisfying (3.3), `K(g_π² + λ g_x²)` is minimised exactly at (3.5). -/
theorem oni_numeric {β κ lam ρ K : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (hK : 0 < K) {gπ gx : ℝ}
    (hg : (1 - β * ρ) * gπ = κ * gx + 1) :
    K * (fpiOni β κ lam ρ ^ 2 + lam * fxOni β κ lam ρ ^ 2) ≤ K * (gπ ^ 2 + lam * gx ^ 2) ∧
      (K * (gπ ^ 2 + lam * gx ^ 2) = K * (fpiOni β κ lam ρ ^ 2 + lam * fxOni β κ lam ρ ^ 2) ↔
        gπ = fpiOni β κ lam ρ ∧ gx = fxOni β κ lam ρ) := by
  have e := Noninertial.oni_objective_eq hκ hlam hg
  have hd : 0 ≤ (gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2 := by positivity
  refine ⟨by rw [e]; nlinarith, ⟨fun h => ?_, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩⟩
  rw [e] at h
  have hz : (gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2 = 0 := by
    have : K * ((gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2) = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hK.ne'
  have a2 : 0 ≤ lam * (gx - fxOni β κ lam ρ) ^ 2 := by positivity
  have e1 : (gπ - fpiOni β κ lam ρ) ^ 2 = 0 := by nlinarith [sq_nonneg (gπ - fpiOni β κ lam ρ)]
  have e2 : (gx - fxOni β κ lam ρ) ^ 2 = 0 := by
    have : lam * (gx - fxOni β κ lam ρ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (gπ - fpiOni β κ lam ρ)]
    exact (mul_eq_zero.mp this).resolve_left hlam.ne'
  exact ⟨by linarith [pow_eq_zero_iff two_ne_zero |>.mp e1],
    by linarith [pow_eq_zero_iff two_ne_zero |>.mp e2]⟩

omit [MeasurableSpace Ω] in
/-- Woodford (2003), App. F.4 (the numerical core): with `K_u, K_r > 0`, among responses
satisfying the four restrictions, `K_r obj(g) + K_u obj(f)` is minimised exactly at the F.4
responses. -/
theorem f4_numeric {β κ σ lx li ρu ρr Ku Kr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρu1 : ρu < 1)
    (hρr1 : ρr < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hKu : 0 < Ku)
    (hKr : 0 < Kr) {fπ fx fi gπ gx gi : ℝ} (hf : Noninertial.ConsU β κ σ ρu fπ fx fi)
    (hg : Noninertial.ConsR β κ σ ρr gπ gx gi) :
    Kr * objF4 lx li (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
        (Noninertial.iRF4 β κ σ lx li ρr) + Ku * objF4 lx li (Noninertial.piUF4 β κ σ lx li ρu)
        (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.iUF4 β κ σ lx li ρu) ≤
      Kr * objF4 lx li gπ gx gi + Ku * objF4 lx li fπ fx fi ∧
    (Kr * objF4 lx li gπ gx gi + Ku * objF4 lx li fπ fx fi =
        Kr * objF4 lx li (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
          (Noninertial.iRF4 β κ σ lx li ρr) + Ku * objF4 lx li
          (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.xUF4 β κ σ lx li ρu)
          (Noninertial.iUF4 β κ σ lx li ρu) ↔
      (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) := by
  have hfu := (Noninertial.f4_u_optimal hβ0 hβ1 hρu1 hκ hσ hlx hli
    (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.xUF4 β κ σ lx li ρu)
    (Noninertial.iUF4 β κ σ lx li ρu)).mpr ⟨rfl, rfl, rfl⟩
  have hgr := (Noninertial.f4_r_optimal hβ0 hβ1 hρr1 hκ hσ hlx hli
    (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
    (Noninertial.iRF4 β κ σ lx li ρr)).mpr ⟨rfl, rfl, rfl⟩
  have e1 := hfu.2 fπ fx fi hf
  have e2 := hgr.2 gπ gx gi hg
  refine ⟨?_, ⟨fun h => ?_, fun ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ => by rw [a1, a2, a3, b1, b2, b3]⟩⟩
  · have m1 := mul_le_mul_of_nonneg_left e1 hKu.le
    have m2 := mul_le_mul_of_nonneg_left e2 hKr.le
    linarith
  set Pu := objF4 lx li (Noninertial.piUF4 β κ σ lx li ρu) (Noninertial.xUF4 β κ σ lx li ρu)
    (Noninertial.iUF4 β κ σ lx li ρu)
  set Pr := objF4 lx li (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
    (Noninertial.iRF4 β κ σ lx li ρr)
  set Fu := objF4 lx li fπ fx fi
  set Fr := objF4 lx li gπ gx gi
  have m1 : 0 ≤ Ku * (Fu - Pu) := mul_nonneg hKu.le (by linarith)
  have m2 : 0 ≤ Kr * (Fr - Pr) := mul_nonneg hKr.le (by linarith)
  have z1 : Ku * (Fu - Pu) = 0 := by linarith
  have z2 : Kr * (Fr - Pr) = 0 := by linarith
  have hu0 : Fu = Pu := by linarith [(mul_eq_zero.mp z1).resolve_left hKu.ne']
  have hr0 : Fr = Pr := by linarith [(mul_eq_zero.mp z2).resolve_left hKr.ne']
  refine ⟨(Noninertial.f4_u_optimal hβ0 hβ1 hρu1 hκ hσ hlx hli fπ fx fi).mp
    ⟨hf, fun a b c h => ?_⟩,
    (Noninertial.f4_r_optimal hβ0 hβ1 hρr1 hκ hσ hlx hli gπ gx gi).mp
    ⟨hg, fun a b c h => ?_⟩⟩
  · change Fu ≤ _
    rw [hu0]
    exact hfu.2 a b c h
  · change Fr ≤ _
    rw [hr0]
    exact hgr.2 a b c h

omit [MeasurableSpace Ω] in
/-- Woodford (2003), (3.4) and (3.7)–(3.8) (tool): the weight
`β/(1 − β) · (1 − ρ²)/(1 − βρ²) · σ_u²` is positive. -/
theorem weight_pos {β ρ s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ : |ρ| < 1) (hs : 0 < s) :
    0 < β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s := by
  have hq1 : ρ ^ 2 < 1 := (sq_lt_one_of_abs hρ).2
  have : 0 < 1 - β := by linarith
  have : 0 < 1 - ρ ^ 2 := by linarith
  have : 0 < 1 - β * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
  unfold uncondVar
  positivity

/-- **Proposition 7.11, off one null set** (Woodford (2003), pp. 509–511): with an AR(1)
cost-push disturbance of innovation variance `s > 0`, there is one null set off which, for
**every** plan (2.19) satisfying (2.1) simultaneously, the regular `L^stab` of the optimal
noninertial plan is at most that of the plan, with equality iff the plan has the responses
(3.5). -/
theorem prop_7_11_uniform {β κ lam ρ s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| < 1) (hs : 0 < s) {u ε : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρ s u ε) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ πbar xbar gπ gx : ℝ, MAS S β κ (plan1 πbar gπ u) (plan1 xbar gx u) u →
      regLstab12 S β lam ρ u t₀ (fpiOni β κ lam ρ) (fxOni β κ lam ρ) ω ≤
        regLstab12 S β lam ρ u t₀ gπ gx ω ∧
      (regLstab12 S β lam ρ u t₀ gπ gx ω =
          regLstab12 S β lam ρ u t₀ (fpiOni β κ lam ρ) (fxOni β κ lam ρ) ω ↔
        gπ = fpiOni β κ lam ρ ∧ gx = fxOni β κ lam ρ) := by
  filter_upwards [regLstab12_uniform S hβ0.le hβ1 hρ hu t₀ (lam := lam)] with ω hω
  intro πbar xbar gπ gx hAS
  have hg := ((plan_AS_iff S hu hs.ne' πbar xbar gπ gx).mp hAS).2
  rw [hω, hω]
  have key := oni_numeric hκ hlam (weight_pos hβ0 hβ1 hρ hs) hg
  simp only [show ∀ X, β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * X * uncondVar ρ s =
    β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s * X from fun X => by ring]
  exact key

/-- **Appendix F.4, off one null set** (Woodford (2003), pp. 512–513, 713–714): with AR(1)
disturbances of positive innovation variances and uncorrelated innovations, there is one null set
off which, for **every** plan (3.6) satisfying (2.1) and (2.23) simultaneously, the regular
`L^stab` of the corrected optimal noninertial plan is at most that of the plan, with equality iff
the plan has the F.4 responses. -/
theorem f4_uniform {β κ σ rbar lx li ρu ρr su sr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1) (hρr : |ρr| < 1)
    (hsu : 0 < su) (hsr : 0 < sr) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ πbar xbar ibar fπ fx fi gπ gx gi : ℝ,
      MAS S β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u →
      MIS S σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
        (fun t ω => rbar + r t ω) →
      regLstab S β lx li ρu ρr u r t₀ (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.iUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
          (Noninertial.iRF4 β κ σ lx li ρr) ω ≤
        regLstab S β lx li ρu ρr u r t₀ fπ fx fi gπ gx gi ω ∧
      (regLstab S β lx li ρu ρr u r t₀ fπ fx fi gπ gx gi ω =
          regLstab S β lx li ρu ρr u r t₀ (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.iUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
            (Noninertial.iRF4 β κ σ lx li ρr) ω ↔
        (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) := by
  have hρu1 : ρu < 1 := (abs_lt.mp hρu).2
  have hρr1 : ρr < 1 := (abs_lt.mp hρr).2
  filter_upwards [regLstab_eq_uniform S hβ0.le hβ1 hρu hρr hu hr hind t₀ (lx := lx) (li := li)]
    with ω hω
  intro πbar xbar ibar fπ fx fi gπ gx gi hA hI
  obtain ⟨-, ⟨f1, f2⟩, ⟨g1, g2⟩⟩ :=
    (plan2_iff S hσ.ne' hu hr hsu.ne' hsr.ne' hind (rbar := rbar) (β := β) (κ := κ)
      πbar xbar ibar fπ fx fi gπ gx gi).mp ⟨hA, hI⟩
  have key := f4_numeric hβ0 hβ1 hρu1 hρr1 hκ hσ hlx hli (weight_pos hβ0 hβ1 hρu hsu)
    (weight_pos hβ0 hβ1 hρr hsr) ⟨f1, f2⟩ ⟨g1, g2⟩
  rw [hω, hω]
  unfold objF4 at key
  convert key using 3 <;> ring

/-! ### The expected loss: equalities of numbers, no null set -/

/-- Woodford (2003), eq. (3.4), p. 511, as an equality of numbers: for every plan (2.19), the
expected stabilization loss `∫ L^stab dμ` equals the closed form. -/
theorem lstab12_integral {β lam ρ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : |ρ| < 1)
    {u ε : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρ s u ε) (t₀ : ℕ) (πbar xbar fπ fx : ℝ) :
    ∫ ω, mLstab12 S β lam t₀ (plan1 πbar fπ u) (plan1 xbar fx u) ω ∂S.μ =
      β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
        uncondVar ρ s := by
  rw [integral_congr_ae (lstab12_eq S hβ0 hβ1 hρ hu πbar xbar fπ fx t₀ (lam := lam)),
    integral_const]
  simp

/-- Woodford (2003), eqs. (3.7)–(3.8), p. 513, as an equality of numbers: for every plan (3.6),
`∫ L^stab dμ = L^{stab,r} + L^{stab,u}`. -/
theorem lstab_integral {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρu : |ρu| < 1)
    (hρr : |ρr| < 1) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) (t₀ : ℕ) :
    ∫ ω, mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
      (plan2 ibar fi gi u r) ω ∂S.μ =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su := by
  rw [integral_congr_ae (lstab_eq S hβ0 hβ1 hρu hρr hu hr hind πbar xbar ibar fπ fx fi gπ gx gi
    t₀ (lx := lx) (li := li)), integral_const]
  simp

/-- **Proposition 7.11 for the expected loss** (Woodford (2003), pp. 509–511): for every plan
(2.19) satisfying (2.1), `∫ L^stab dμ` of the optimal noninertial plan is at most the plan's, with
equality iff the plan has the responses (3.5) — inequalities between numbers. -/
theorem prop_7_11_integral {β κ lam ρ s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| < 1) (hs : 0 < s) {u ε : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρ s u ε) (t₀ : ℕ) (πbar xbar gπ gx : ℝ)
    (hAS : MAS S β κ (plan1 πbar gπ u) (plan1 xbar gx u) u) :
    ∫ ω, mLstab12 S β lam t₀ (plan1 0 (fpiOni β κ lam ρ) u) (plan1 0 (fxOni β κ lam ρ) u) ω ∂S.μ ≤
      ∫ ω, mLstab12 S β lam t₀ (plan1 πbar gπ u) (plan1 xbar gx u) ω ∂S.μ ∧
    (∫ ω, mLstab12 S β lam t₀ (plan1 πbar gπ u) (plan1 xbar gx u) ω ∂S.μ =
        ∫ ω, mLstab12 S β lam t₀ (plan1 0 (fpiOni β κ lam ρ) u)
          (plan1 0 (fxOni β κ lam ρ) u) ω ∂S.μ ↔
      gπ = fpiOni β κ lam ρ ∧ gx = fxOni β κ lam ρ) := by
  have hg := ((plan_AS_iff S hu hs.ne' πbar xbar gπ gx).mp hAS).2
  rw [lstab12_integral S hβ0.le hβ1 hρ hu, lstab12_integral S hβ0.le hβ1 hρ hu]
  have key := oni_numeric hκ hlam (weight_pos hβ0 hβ1 hρ hs) hg
  simp only [show ∀ X, β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * X * uncondVar ρ s =
    β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s * X from fun X => by ring]
  exact key

/-- **Appendix F.4 for the expected loss** (Woodford (2003), pp. 512–513, 713–714): for every plan
(3.6) satisfying (2.1) and (2.23), `∫ L^stab dμ` of the corrected optimal noninertial plan is at
most the plan's, with equality iff the plan has the F.4 responses — inequalities between
numbers. -/
theorem f4_integral {β κ σ rbar lx li istar ρu ρr su sr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1) (hρr : |ρr| < 1)
    (hsu : 0 < su) (hsr : 0 < sr) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr)
    (hind : ∀ t, S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0) (t₀ : ℕ) {xs is : ℝ}
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ)
    (hA : MAS S β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u)
    (hI : MIS S σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
      (fun t ω => rbar + r t ω)) :
    ∫ ω, mLstab S β lx li t₀
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ω
        ∂S.μ ≤
      ∫ ω, mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
        (plan2 ibar fi gi u r) ω ∂S.μ ∧
    (∫ ω, mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
        (plan2 ibar fi gi u r) ω ∂S.μ =
      ∫ ω, mLstab S β lx li t₀
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ω
        ∂S.μ ↔
      (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) := by
  have hρu1 : ρu < 1 := (abs_lt.mp hρu).2
  have hρr1 : ρr < 1 := (abs_lt.mp hρr).2
  obtain ⟨-, ⟨f1, f2⟩, ⟨g1, g2⟩⟩ :=
    (plan2_iff S hσ.ne' hu hr hsu.ne' hsr.ne' hind (rbar := rbar) (β := β) (κ := κ)
      πbar xbar ibar fπ fx fi gπ gx gi).mp ⟨hA, hI⟩
  rw [lstab_integral S hβ0.le hβ1 hρu hρr hu hr hind, lstab_integral S hβ0.le hβ1 hρu hρr hu hr
    hind]
  have key := f4_numeric hβ0 hβ1 hρu1 hρr1 hκ hσ hlx hli (weight_pos hβ0 hβ1 hρu hsu)
    (weight_pos hβ0 hβ1 hρr hsr) ⟨f1, f2⟩ ⟨g1, g2⟩
  unfold objF4 at key
  convert key using 3 <;> ring


/-! ### No uniform null set for arbitrary versions -/

/-- Woodford (2003), p. 509 (tool): the state space `ℕ → ℝ` of the i.i.d. economy has the
cardinality of the continuum, so it injects into `ℝ`. -/
theorem exists_stateToReal_injective : ∃ e : (ℕ → ℝ) → ℝ, Function.Injective e := by
  have h : Cardinal.mk (ℕ → ℝ) ≤ Cardinal.mk ℝ := by
    rw [← Cardinal.power_def, Cardinal.mk_real, Cardinal.mk_nat, Cardinal.continuum_power_aleph0]
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp h
  exact ⟨f, f.injective⟩

/-- Woodford (2003), p. 509 (tool): a fixed injection of the states into `ℝ`. -/
noncomputable def stateToReal : (ℕ → ℝ) → ℝ := Classical.choose exists_stateToReal_injective

/-- Woodford (2003), p. 509 (tool): `stateToReal` is injective. -/
theorem stateToReal_injective : Function.Injective stateToReal :=
  Classical.choose_spec exists_stateToReal_injective

/-- Woodford (2003), (3.3) and (3.5), p. 511: the competing plan attached to the state `ω`: the
plan (2.19) with `π̄ = x̄ = 0`, `f_π = f_π^oni + exp(e(ω))` and `f_x` from (3.3). -/
noncomputable def badPlan (β κ lam ρ : ℝ) (ω : ℕ → ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (0, 0, fpiOni β κ lam ρ + Real.exp (stateToReal ω),
    ((1 - β * ρ) * (fpiOni β κ lam ρ + Real.exp (stateToReal ω)) - 1) / κ)

/-- Woodford (2003), p. 509: Mathlib's `L^stab` of the plan (2.19) with coefficients
`q = (π̄, x̄, f_π, f_x)` on the fair-coin economy. -/
noncomputable def coinL (β lam ρ : ℝ) (t₀ : ℕ) (q : ℝ × ℝ × ℝ × ℝ) (ω : ℕ → ℝ) : ℝ :=
  mLstab12 (iidSystem coin) β lam t₀ (plan1 q.1 q.2.2.1 (ar1 ρ)) (plan1 q.2.1 q.2.2.2 (ar1 ρ)) ω

/-- Woodford (2003), p. 509: a choice of versions of `L^stab` on the fair-coin economy: `L^stab`
itself, except that at the single state `ω` attached to a plan (`badPlan`) its value is set one
below that of the optimal noninertial plan. -/
noncomputable def badVersion (β κ lam ρ : ℝ) (t₀ : ℕ) (q : ℝ × ℝ × ℝ × ℝ) (ω : ℕ → ℝ) : ℝ :=
  if q = badPlan β κ lam ρ ω then
    coinL β lam ρ t₀ (0, 0, fpiOni β κ lam ρ, fxOni β κ lam ρ) ω - 1
  else coinL β lam ρ t₀ q ω

/-- **No uniform null set for `L^stab` as an a.s.-defined object** (Woodford (2003), pp. 509–511,
Proposition 7.11): on the fair-coin economy, `badVersion` is, plan by plan, a version of
`L^stab` (a.e. equal to it), yet at **every** state some plan satisfying (2.1) has a strictly
smaller value than the optimal noninertial plan; hence no null set `N` exists off which the
ranking of Prop. 7.11 holds for all plans at once. Uniformity is a property of the chosen versions,
not of `L^stab` (contrast `prop_7_11_uniform`). -/
theorem versions_no_uniform_null {β κ lam ρ : ℝ} (hκ : 0 < κ) (hρ : |ρ| < 1) (t₀ : ℕ) :
    (∀ q, badVersion β κ lam ρ t₀ q =ᵐ[(iidSystem coin).μ] coinL β lam ρ t₀ q) ∧
    (∀ ω, MAS (iidSystem coin) β κ (plan1 0 (badPlan β κ lam ρ ω).2.2.1 (ar1 ρ))
        (plan1 0 (badPlan β κ lam ρ ω).2.2.2 (ar1 ρ)) (ar1 ρ) ∧
      badVersion β κ lam ρ t₀ (badPlan β κ lam ρ ω) ω <
        badVersion β κ lam ρ t₀ (0, 0, fpiOni β κ lam ρ, fxOni β κ lam ρ) ω) ∧
    ¬ ∃ N : Set (ℕ → ℝ), (iidSystem coin).μ N = 0 ∧ ∀ ω ∉ N, ∀ q : ℝ × ℝ × ℝ × ℝ,
      MAS (iidSystem coin) β κ (plan1 q.1 q.2.2.1 (ar1 ρ)) (plan1 q.2.1 q.2.2.2 (ar1 ρ)) (ar1 ρ) →
      badVersion β κ lam ρ t₀ (0, 0, fpiOni β κ lam ρ, fxOni β κ lam ρ) ω ≤
        badVersion β κ lam ρ t₀ q ω := by
  have hu := NoninertialMeasureIID.iid_measAR1Innov (ρ := ρ) hρ coin_mean coin_var coin_bdd
  have hne : ∀ ω, (0, 0, fpiOni β κ lam ρ, fxOni β κ lam ρ) ≠ badPlan β κ lam ρ ω := by
    intro ω h
    have := congrArg (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1) h
    simp only [badPlan] at this
    linarith [Real.exp_pos (stateToReal ω)]
  have honi : ∀ ω, badVersion β κ lam ρ t₀ (0, 0, fpiOni β κ lam ρ, fxOni β κ lam ρ) ω =
      coinL β lam ρ t₀ (0, 0, fpiOni β κ lam ρ, fxOni β κ lam ρ) ω := by
    intro ω
    simp only [badVersion, hne ω, ↓reduceIte]
  have hbad : ∀ ω, badVersion β κ lam ρ t₀ (badPlan β κ lam ρ ω) ω <
      badVersion β κ lam ρ t₀ (0, 0, fpiOni β κ lam ρ, fxOni β κ lam ρ) ω := by
    intro ω
    rw [honi]
    simp only [badVersion, ↓reduceIte]
    linarith
  have hfeas : ∀ ω, MAS (iidSystem coin) β κ (plan1 0 (badPlan β κ lam ρ ω).2.2.1 (ar1 ρ))
      (plan1 0 (badPlan β κ lam ρ ω).2.2.2 (ar1 ρ)) (ar1 ρ) := by
    intro ω
    refine (plan_AS_iff _ hu one_ne_zero 0 0 _ _).mpr ⟨by ring, ?_⟩
    simp only [badPlan]
    field_simp
    ring
  refine ⟨fun q => ?_, fun ω => ⟨hfeas ω, hbad ω⟩, ?_⟩
  · have hsub : {ω | q = badPlan β κ lam ρ ω}.Subsingleton := by
      intro ω₁ h₁ ω₂ h₂
      have e := congrArg (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1) ((Set.mem_ofPred_eq ▸ h₁).symm.trans
        (Set.mem_ofPred_eq ▸ h₂))
      simp only [badPlan, add_right_inj, Real.exp_eq_exp] at e
      exact stateToReal_injective e
    have hnull : (iidSystem coin).μ {ω | q = badPlan β κ lam ρ ω} = 0 := by
      rcases hsub.eq_empty_or_singleton with h | ⟨ω₀, h⟩
      · rw [h, measure_empty]
      · rw [h]
        exact iid_singleton coin_mean coin_var one_pos ω₀
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with ω hω
    have hω' : ¬ q = badPlan β κ lam ρ ω := hω
    simp only [badVersion, hω', ↓reduceIte]
  · rintro ⟨N, hN, hall⟩
    have hNu : N ≠ Set.univ := by
      intro h
      rw [h, measure_univ] at hN
      exact one_ne_zero hN
    obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem N).mp hNu
    have := hall ω hω (badPlan β κ lam ρ ω) (hfeas ω)
    linarith [hbad ω]

end Woodford.GainsFromCommitment.TidyR5UniformNull
