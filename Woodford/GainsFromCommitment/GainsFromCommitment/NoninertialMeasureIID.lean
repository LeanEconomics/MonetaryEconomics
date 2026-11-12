/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.NoninertialMeasure
import GainsFromCommitment.ExpectationsMeasureIID

/-!
# The variance results on a genuine i.i.d. probability model

Woodford (2003), *Interest and Prices*, Chapter 7, §3, pp. 507–513 ((3.4), (3.7)–(3.8),
Proposition 7.11) and Appendix F.4, pp. 713–714, instantiated on the i.i.d. infinite-product
economy of `ExpectationsMeasureIID` (`Ω = ℕ → ℝ`, `μ = ν^ℕ`, natural filtration), which is not
finitely supported (every history is null). This shows that the hypotheses of
`NoninertialMeasure` (AR(1) disturbances with innovations of constant, positive conditional
variance, uncorrelated across the two disturbances) are satisfied by a genuine probability model
with infinitely many nondegenerate innovations.

## Main results

* One disturbance: `iid_measAR1Innov` (the AR(1) of the coordinate shocks), `iid_lstab12`
  ((3.4)), `iid_prop_7_11` (Proposition 7.11), and for fair `±1` coins `coin_prop_7_11`.
* Two disturbances driven by functions `f(ε_t)`, `g(ε_t)` of the shock: `ar1fn`,
  `iid_measAR1Innov_fn`, `E_fnShock_mul`, `iid2_lstab` ((3.7)–(3.8)), `iid2_f4_lstab`
  (Appendix F.4).
* A concrete law: `quad` (uniform on `{±1, ±3}`) with the two independent fair coins
  `coinA`, `coinB` it encodes; `twoCoin_economy` (all moment conditions, every history null) and
  `twoCoin_f4_lstab`.
-/

namespace Woodford.GainsFromCommitment.NoninertialMeasureIID

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID NoninertialMeasure
open VarianceFrontier (plan2)
open Noninertial (plan1 fpiOni fxOni uncondVar)

/-! ### One disturbance: the AR(1) of the coordinate shocks -/

/-- Woodford (2003), eq. (2.18), p. 496, on the i.i.d. economy: the AR(1) `u_{t+1} = ρu_t + ε_{t+1}`
of mean-zero shocks with variance `σ²` and bounded support (`|ρ| < 1`) satisfies `MeasAR1Innov`
with innovation variance `σ²`. -/
theorem iid_measAR1Innov {ν : ProbabilityMeasure ℝ} {ρ B σ2 : ℝ} (hρ : |ρ| < 1)
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) :
    MeasAR1Innov (iidSystem ν) ρ σ2 (ar1 ρ) shock := by
  refine ⟨ar1_adapted ν ρ, ⟨_, ar1_bdd hρ hbdd⟩, ar1_succ ρ, E_shock_zero hmean, fun t => ?_⟩
  have h : shock (t + 1) * shock (t + 1) = shock (t + 1) ^ 2 := (sq _).symm
  rw [h]
  exact E_shock_sq_eq hvar t

/-- **Equation (3.4)** (Woodford (2003), p. 511) on the i.i.d. economy: almost surely the
stabilization loss of a plan (2.19) is `β/(1 − β) · (1 − ρ²)/(1 − βρ²) · (f_π² + λ f_x²) σ_u²`
with `σ_u² = σ²/(1 − ρ²)`. -/
theorem iid_lstab12 {ν : ProbabilityMeasure ℝ} {β lam ρ B σ2 : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ : |ρ| < 1) (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B)
    (πbar xbar fπ fx : ℝ) (t₀ : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ,
      mLstab12 (iidSystem ν) β lam t₀ (plan1 πbar fπ (ar1 ρ)) (plan1 xbar fx (ar1 ρ)) ω =
        β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
          uncondVar ρ σ2 :=
  lstab12_eq _ hβ0 hβ1 hρ (iid_measAR1Innov hρ hmean hvar hbdd) πbar xbar fπ fx t₀

/-- **Proposition 7.11, stabilization form** (Woodford (2003), pp. 509–511) on the i.i.d.
economy with shock variance `σ² > 0`: the optimal noninertial plan satisfies (2.1), and every
plan (2.19) satisfying (2.1) has almost surely at least its stabilization loss, with almost-sure
equality iff it has the responses (3.5). -/
theorem iid_prop_7_11 {ν : ProbabilityMeasure ℝ} {β κ lam ρ B σ2 : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) (hρ : |ρ| < 1) (hσ : 0 < σ2)
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) (t₀ : ℕ) :
    MAS (iidSystem ν) β κ (plan1 0 (fpiOni β κ lam ρ) (ar1 ρ)) (plan1 0 (fxOni β κ lam ρ) (ar1 ρ))
      (ar1 ρ) ∧
    ∀ πbar xbar gπ gx, MAS (iidSystem ν) β κ (plan1 πbar gπ (ar1 ρ)) (plan1 xbar gx (ar1 ρ))
        (ar1 ρ) →
      (∀ᵐ ω ∂(iidSystem ν).μ,
        mLstab12 (iidSystem ν) β lam t₀ (plan1 0 (fpiOni β κ lam ρ) (ar1 ρ))
            (plan1 0 (fxOni β κ lam ρ) (ar1 ρ)) ω ≤
          mLstab12 (iidSystem ν) β lam t₀ (plan1 πbar gπ (ar1 ρ)) (plan1 xbar gx (ar1 ρ)) ω) ∧
      (mLstab12 (iidSystem ν) β lam t₀ (plan1 πbar gπ (ar1 ρ)) (plan1 xbar gx (ar1 ρ))
          =ᵐ[(iidSystem ν).μ]
          mLstab12 (iidSystem ν) β lam t₀ (plan1 0 (fpiOni β κ lam ρ) (ar1 ρ))
            (plan1 0 (fxOni β κ lam ρ) (ar1 ρ)) ↔
        gπ = fpiOni β κ lam ρ ∧ gx = fxOni β κ lam ρ) :=
  prop_7_11_lstab _ hβ0 hβ1 hκ hlam hρ hσ (iid_measAR1Innov hρ hmean hvar hbdd) t₀

/-- **Proposition 7.11** (Woodford (2003), pp. 509–511) on the fair-coin economy (`ε_t = ±1`
i.i.d., innovation variance `1`): every history is null (the model is not finitely supported),
and the optimal noninertial plan minimises the stabilization loss almost surely among all plans
(2.19) satisfying (2.1), uniquely up to almost-sure equality of losses. -/
theorem coin_prop_7_11 {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| < 1) (t₀ : ℕ) :
    (∀ ω, (iidSystem coin).μ {ω} = 0) ∧
    MAS (iidSystem coin) β κ (plan1 0 (fpiOni β κ lam ρ) (ar1 ρ))
      (plan1 0 (fxOni β κ lam ρ) (ar1 ρ)) (ar1 ρ) ∧
    ∀ πbar xbar gπ gx, MAS (iidSystem coin) β κ (plan1 πbar gπ (ar1 ρ)) (plan1 xbar gx (ar1 ρ))
        (ar1 ρ) →
      (∀ᵐ ω ∂(iidSystem coin).μ,
        mLstab12 (iidSystem coin) β lam t₀ (plan1 0 (fpiOni β κ lam ρ) (ar1 ρ))
            (plan1 0 (fxOni β κ lam ρ) (ar1 ρ)) ω ≤
          mLstab12 (iidSystem coin) β lam t₀ (plan1 πbar gπ (ar1 ρ)) (plan1 xbar gx (ar1 ρ)) ω) ∧
      (mLstab12 (iidSystem coin) β lam t₀ (plan1 πbar gπ (ar1 ρ)) (plan1 xbar gx (ar1 ρ))
          =ᵐ[(iidSystem coin).μ]
          mLstab12 (iidSystem coin) β lam t₀ (plan1 0 (fpiOni β κ lam ρ) (ar1 ρ))
            (plan1 0 (fxOni β κ lam ρ) (ar1 ρ)) ↔
        gπ = fpiOni β κ lam ρ ∧ gx = fxOni β κ lam ρ) :=
  ⟨iid_singleton coin_mean coin_var one_pos,
    iid_prop_7_11 hβ0 hβ1 hκ hlam hρ one_pos coin_mean coin_var coin_bdd t₀⟩

/-! ### Two disturbances driven by functions of the shock -/

/-- Woodford (2003), eq. (2.27), p. 504 (tool): the innovation `f(ε_t)`, a function of the date-`t`
shock. -/
def fnShock (f : ℝ → ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := f (ω t)

/-- Woodford (2003), eqs. (2.18) and (2.27): the AR(1) `u_0 = f(ε_0)`,
`u_{t+1} = ρ u_t + f(ε_{t+1})`. -/
def ar1fn (ρ : ℝ) (f : ℝ → ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fnShock f 0
  | t + 1 => fun ω => ρ * ar1fn ρ f t ω + fnShock f (t + 1) ω

/-- Woodford (2003), eq. (2.18): the AR(1) law of motion of `ar1fn`. -/
theorem ar1fn_succ (ρ : ℝ) (f : ℝ → ℝ) (t : ℕ) :
    ar1fn ρ f (t + 1) = ρ • ar1fn ρ f t + fnShock f (t + 1) := rfl

/-- Woodford (2003), eq. (2.18): a measurable function of the date-`s` shock is known at every
`t ≥ s`. -/
theorem measurable_fnShock (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} (hf : Measurable f) {s t : ℕ}
    (hst : s ≤ t) : Measurable[(iidSystem ν).𝓕 t] (fnShock f s) :=
  hf.comp (measurable_shock ν hst)

/-- Woodford (2003), eq. (2.18): `ar1fn` is adapted. -/
theorem ar1fn_adapted (ν : ProbabilityMeasure ℝ) (ρ : ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    StronglyAdapted (iidSystem ν).𝓕 (ar1fn ρ f) := by
  intro t
  induction t with
  | zero => exact (measurable_fnShock ν hf le_rfl).stronglyMeasurable
  | succ t ih =>
    rw [ar1fn_succ]
    exact ((ih.mono ((iidSystem ν).𝓕.mono (Nat.le_succ t))).const_smul ρ).add
      (measurable_fnShock ν hf le_rfl).stronglyMeasurable

/-- Woodford (2003), eq. (2.18): for `|ρ| < 1` and `|f| ≤ B`, `|u_t| ≤ B/(1 − |ρ|)` everywhere. -/
theorem ar1fn_bdd {ρ B : ℝ} (hρ : |ρ| < 1) {f : ℝ → ℝ} (hB : ∀ x, |f x| ≤ B) (t : ℕ)
    (ω : ℕ → ℝ) : |ar1fn ρ f t ω| ≤ B / (1 - |ρ|) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have h1 : 0 < 1 - |ρ| := by linarith
  induction t with
  | zero =>
    refine (hB (ω 0)).trans ?_
    rw [le_div_iff₀ h1]
    nlinarith [abs_nonneg ρ]
  | succ t ih =>
    change |ρ * ar1fn ρ f t ω + f (ω (t + 1))| ≤ _
    have key : |ρ| * (B / (1 - |ρ|)) + B = B / (1 - |ρ|) := by
      field_simp
      ring
    calc |ρ * ar1fn ρ f t ω + f (ω (t + 1))| ≤ |ρ| * |ar1fn ρ f t ω| + |f (ω (t + 1))| := by
          rw [← abs_mul]
          exact abs_add_le _ _
      _ ≤ |ρ| * (B / (1 - |ρ|)) + B :=
          add_le_add (mul_le_mul_of_nonneg_left ih (abs_nonneg ρ)) (hB _)
      _ = B / (1 - |ρ|) := key

/-- Woodford (2003), p. 512 (the conditional moments of the innovations): on the i.i.d. economy
`E_t[f(ε_{t+1}) g(ε_{t+1})] = ∫ f g dν` almost surely. -/
theorem E_fnShock_mul {ν : ProbabilityMeasure ℝ} {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) (t : ℕ) :
    (iidSystem ν).E t (fnShock f (t + 1) * fnShock g (t + 1)) =ᵐ[(iidSystem ν).μ]
      fun _ => ∫ x, f x * g x ∂(ν : Measure ℝ) :=
  E_shock_fun ν t (hf.mul hg)

/-- Woodford (2003), eqs. (2.18) and (2.27) on the i.i.d. economy: the AR(1) driven by `f(ε_t)`,
with `f` measurable, bounded, `∫ f dν = 0` and `∫ f² dν = s`, satisfies `MeasAR1Innov` with
innovation variance `s`. -/
theorem iid_measAR1Innov_fn {ν : ProbabilityMeasure ℝ} {ρ B s : ℝ} (hρ : |ρ| < 1) {f : ℝ → ℝ}
    (hf : Measurable f) (hB : ∀ x, |f x| ≤ B) (hmean : ∫ x, f x ∂(ν : Measure ℝ) = 0)
    (hvar : ∫ x, f x * f x ∂(ν : Measure ℝ) = s) :
    MeasAR1Innov (iidSystem ν) ρ s (ar1fn ρ f) (fnShock f) := by
  refine ⟨ar1fn_adapted ν ρ hf, ⟨_, fun t => Eventually.of_forall (ar1fn_bdd hρ hB t)⟩,
    ar1fn_succ ρ f, fun t => ?_, fun t => ?_⟩
  · filter_upwards [E_shock_fun ν t hf] with ω h
    change (iidSystem ν).E t (fun ω => f (ω (t + 1))) ω = 0
    rw [h, hmean]
  · filter_upwards [E_fnShock_mul (ν := ν) hf hf t] with ω h
    rw [h, hvar]

/-- **Equations (3.7)–(3.8)** (Woodford (2003), p. 513) on the i.i.d. economy: with disturbances
`u`, `r̂ⁿ` driven by `f(ε_t)`, `g(ε_t)` (measurable, bounded, mean zero, `∫ f² = s_u`,
`∫ g² = s_r`, `∫ f g = 0`), almost surely `L^stab = L^{stab,r} + L^{stab,u}` for every plan
(3.6). -/
theorem iid2_lstab {ν : ProbabilityMeasure ℝ} {β lx li ρu ρr Bu Br su sr : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hρu : |ρu| < 1) (hρr : |ρr| < 1) {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hBf : ∀ x, |f x| ≤ Bu) (hBg : ∀ x, |g x| ≤ Br)
    (hfm : ∫ x, f x ∂(ν : Measure ℝ) = 0) (hgm : ∫ x, g x ∂(ν : Measure ℝ) = 0)
    (hfv : ∫ x, f x * f x ∂(ν : Measure ℝ) = su) (hgv : ∫ x, g x * g x ∂(ν : Measure ℝ) = sr)
    (hfg : ∫ x, f x * g x ∂(ν : Measure ℝ) = 0) (πbar xbar ibar fπ fx fi gπ gx gi : ℝ)
    (t₀ : ℕ) :
    ∀ᵐ ω ∂(iidSystem ν).μ, mLstab (iidSystem ν) β lx li t₀
      (plan2 πbar fπ gπ (ar1fn ρu f) (ar1fn ρr g)) (plan2 xbar fx gx (ar1fn ρu f) (ar1fn ρr g))
      (plan2 ibar fi gi (ar1fn ρu f) (ar1fn ρr g)) ω =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su :=
  lstab_eq _ hβ0 hβ1 hρu hρr (iid_measAR1Innov_fn hρu hf hBf hfm hfv)
    (iid_measAR1Innov_fn hρr hg hBg hgm hgv)
    (fun t => (E_fnShock_mul hf hg t).trans (by rw [hfg])) πbar xbar ibar fπ fx fi gπ gx gi t₀

/-- **Appendix F.4, stabilization optimality** (Woodford (2003), pp. 512–513, 713–714) on the
i.i.d. economy with disturbances driven by `f(ε_t)`, `g(ε_t)` (measurable, bounded, mean zero,
`∫ f² = s_u > 0`, `∫ g² = s_r > 0`, `∫ f g = 0`): the conclusion of `NoninertialMeasure.f4_lstab`
holds. -/
theorem iid2_f4_lstab {ν : ProbabilityMeasure ℝ} {β κ σ rbar lx li istar ρu ρr Bu Br su sr : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li)
    (hρu : |ρu| < 1) (hρr : |ρr| < 1) (hsu : 0 < su) (hsr : 0 < sr) {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hBf : ∀ x, |f x| ≤ Bu) (hBg : ∀ x, |g x| ≤ Br)
    (hfm : ∫ x, f x ∂(ν : Measure ℝ) = 0) (hgm : ∫ x, g x ∂(ν : Measure ℝ) = 0)
    (hfv : ∫ x, f x * f x ∂(ν : Measure ℝ) = su) (hgv : ∫ x, g x * g x ∂(ν : Measure ℝ) = sr)
    (hfg : ∫ x, f x * g x ∂(ν : Measure ℝ) = 0) (t₀ : ℕ) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (MAS (iidSystem ν) β κ
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu f) (ar1fn ρr g))
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
          (ar1fn ρu f) (ar1fn ρr g)) (ar1fn ρu f) ∧
      MIS (iidSystem ν) σ
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu f) (ar1fn ρr g))
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
          (ar1fn ρu f) (ar1fn ρr g))
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr)
          (ar1fn ρu f) (ar1fn ρr g))
        (fun t ω => rbar + ar1fn ρr g t ω)) ∧
    ∀ πbar xbar ibar fπ fx fi gπ gx gi,
      MAS (iidSystem ν) β κ (plan2 πbar fπ gπ (ar1fn ρu f) (ar1fn ρr g))
        (plan2 xbar fx gx (ar1fn ρu f) (ar1fn ρr g)) (ar1fn ρu f) →
      MIS (iidSystem ν) σ (plan2 πbar fπ gπ (ar1fn ρu f) (ar1fn ρr g))
        (plan2 xbar fx gx (ar1fn ρu f) (ar1fn ρr g)) (plan2 ibar fi gi (ar1fn ρu f) (ar1fn ρr g))
        (fun t ω => rbar + ar1fn ρr g t ω) →
      (∀ᵐ ω ∂(iidSystem ν).μ, mLstab (iidSystem ν) β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu f) (ar1fn ρr g))
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
            (ar1fn ρu f) (ar1fn ρr g))
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr)
            (ar1fn ρu f) (ar1fn ρr g)) ω ≤
        mLstab (iidSystem ν) β lx li t₀ (plan2 πbar fπ gπ (ar1fn ρu f) (ar1fn ρr g))
          (plan2 xbar fx gx (ar1fn ρu f) (ar1fn ρr g))
          (plan2 ibar fi gi (ar1fn ρu f) (ar1fn ρr g)) ω) ∧
      (mLstab (iidSystem ν) β lx li t₀ (plan2 πbar fπ gπ (ar1fn ρu f) (ar1fn ρr g))
          (plan2 xbar fx gx (ar1fn ρu f) (ar1fn ρr g))
          (plan2 ibar fi gi (ar1fn ρu f) (ar1fn ρr g)) =ᵐ[(iidSystem ν).μ]
        mLstab (iidSystem ν) β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu f) (ar1fn ρr g))
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
            (ar1fn ρu f) (ar1fn ρr g))
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr)
            (ar1fn ρu f) (ar1fn ρr g)) ↔
        (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) :=
  f4_lstab _ hβ0 hβ1 hκ hσ hlx hli hρu hρr hsu hsr (iid_measAR1Innov_fn hρu hf hBf hfm hfv)
    (iid_measAR1Innov_fn hρr hg hBg hgm hgv)
    (fun t => (E_fnShock_mul hf hg t).trans (by rw [hfg])) t₀ hxs his

/-! ### A concrete law: two independent fair coins encoded in one shock -/

/-- Woodford (2003), p. 512 (two independent disturbances; concrete law): the uniform law on
`{3, 1, −1, −3}`, which encodes two independent fair coins, as a measure. -/
noncomputable def quadMeasure : Measure ℝ :=
  (4⁻¹ : ENNReal) • (Measure.dirac 3 + Measure.dirac 1 + Measure.dirac (-1) + Measure.dirac (-3))

/-- Woodford (2003), p. 512 (concrete law): the uniform law on `{±1, ±3}` has total mass one. -/
theorem quadMeasure_univ : quadMeasure Set.univ = 1 := by
  simp only [quadMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  have h4 : (1 + 1 + 1 + 1 : ENNReal) = 4 := by norm_num
  rw [h4, ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top]

/-- Woodford (2003), p. 512 (concrete law): the uniform law on `{±1, ±3}`. -/
noncomputable def quad : ProbabilityMeasure ℝ := ⟨quadMeasure, ⟨quadMeasure_univ⟩⟩

/-- Woodford (2003), p. 512 (concrete law): `∫ f d quad = (f 3 + f 1 + f(−1) + f(−3))/4`. -/
theorem integral_quad (f : ℝ → ℝ) :
    ∫ x, f x ∂(quad : Measure ℝ) = (f 3 + f 1 + f (-1) + f (-3)) / 4 := by
  change ∫ x, f x ∂quadMeasure = _
  have i : ∀ a : ℝ, Integrable f (Measure.dirac a) := fun _ => integrable_dirac enorm_lt_top
  rw [quadMeasure, integral_smul_measure,
    integral_add_measure (((i 3).add_measure (i 1)).add_measure (i (-1))) (i (-3)),
    integral_add_measure ((i 3).add_measure (i 1)) (i (-1)), integral_add_measure (i 3) (i 1),
    integral_dirac, integral_dirac, integral_dirac, integral_dirac, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- Woodford (2003), p. 512 (concrete law): the first coin, `+1` on `{3, 1}`, `−1` on
`{−1, −3}`. -/
noncomputable def coinA (x : ℝ) : ℝ := if 0 < x then 1 else -1

/-- Woodford (2003), p. 512 (concrete law): the second coin, `+1` on `{3, −1}`, `−1` on
`{1, −3}`. -/
noncomputable def coinB (x : ℝ) : ℝ := if 2 < x ∨ (-2 < x ∧ x < 0) then 1 else -1

/-- Woodford (2003), p. 512 (concrete law): the first coin is measurable. -/
theorem measurable_coinA : Measurable coinA :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

/-- Woodford (2003), p. 512 (concrete law): the second coin is measurable. -/
theorem measurable_coinB : Measurable coinB :=
  Measurable.ite (measurableSet_Ioi.union (measurableSet_Ioi.inter measurableSet_Iio))
    measurable_const measurable_const

/-- Woodford (2003), p. 512 (concrete law): the first coin is bounded by one. -/
theorem coinA_bdd (x : ℝ) : |coinA x| ≤ 1 := by
  unfold coinA
  split_ifs <;> norm_num

/-- Woodford (2003), p. 512 (concrete law): the second coin is bounded by one. -/
theorem coinB_bdd (x : ℝ) : |coinB x| ≤ 1 := by
  unfold coinB
  split_ifs <;> norm_num

/-- Woodford (2003), p. 512 (concrete law): the moments of the two coins under `quad`: both
have mean `0` and variance `1`, they are uncorrelated, and the underlying shock has mean `0` and
variance `5`. -/
theorem quad_moments :
    ∫ x, coinA x ∂(quad : Measure ℝ) = 0 ∧ ∫ x, coinB x ∂(quad : Measure ℝ) = 0 ∧
    ∫ x, coinA x * coinA x ∂(quad : Measure ℝ) = 1 ∧
    ∫ x, coinB x * coinB x ∂(quad : Measure ℝ) = 1 ∧
    ∫ x, coinA x * coinB x ∂(quad : Measure ℝ) = 0 ∧ ∫ x, x ∂(quad : Measure ℝ) = 0 ∧
    ∫ x, x ^ 2 ∂(quad : Measure ℝ) = 5 := by
  simp only [integral_quad]
  norm_num [coinA, coinB]

/-- Woodford (2003), pp. 512–513 (the two-disturbance economy is a genuine probability model):
with `ε_t` i.i.d. uniform on `{±1, ±3}`, `εᵘ_t = coinA(ε_t)`, `εʳ_t = coinB(ε_t)`, every history
is null, and the innovations are unforecastable with unit conditional variances and zero
conditional covariance. -/
theorem twoCoin_economy :
    (∀ ω, (iidSystem quad).μ {ω} = 0) ∧
    (∀ t, (iidSystem quad).E t (fnShock coinA (t + 1)) =ᵐ[(iidSystem quad).μ] 0) ∧
    (∀ t, (iidSystem quad).E t (fnShock coinB (t + 1)) =ᵐ[(iidSystem quad).μ] 0) ∧
    (∀ t, (iidSystem quad).E t (fnShock coinA (t + 1) * fnShock coinA (t + 1))
      =ᵐ[(iidSystem quad).μ] fun _ => 1) ∧
    (∀ t, (iidSystem quad).E t (fnShock coinB (t + 1) * fnShock coinB (t + 1))
      =ᵐ[(iidSystem quad).μ] fun _ => 1) ∧
    (∀ t, (iidSystem quad).E t (fnShock coinA (t + 1) * fnShock coinB (t + 1))
      =ᵐ[(iidSystem quad).μ] fun _ => 0) := by
  obtain ⟨hA, hB, hAA, hBB, hAB, hm, hv⟩ := quad_moments
  have uA := iid_measAR1Innov_fn (ν := quad) (ρ := 0) (by norm_num) measurable_coinA coinA_bdd
    hA hAA
  have uB := iid_measAR1Innov_fn (ν := quad) (ρ := 0) (by norm_num) measurable_coinB coinB_bdd
    hB hBB
  exact ⟨iid_singleton hm hv (by norm_num), uA.2.2.2.1, uB.2.2.2.1, uA.2.2.2.2, uB.2.2.2.2,
    fun t => (E_fnShock_mul measurable_coinA measurable_coinB t).trans (by rw [hAB])⟩

/-- **Appendix F.4, stabilization optimality** (Woodford (2003), pp. 512–513, 713–714) on the
two-coin economy (`twoCoin_economy`): with `u` and `r̂ⁿ` AR(1) disturbances driven by the two
independent fair coins (`|ρ_u|, |ρ_r| < 1`), the corrected optimal noninertial plan satisfies
(2.1) and (2.23), and every plan (3.6) satisfying them has almost surely at least its
stabilization loss, with almost-sure equality iff it has the F.4 responses. -/
theorem twoCoin_f4_lstab {β κ σ rbar lx li istar ρu ρr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1) (hρr : |ρr| < 1)
    (t₀ : ℕ) {xs is : ℝ} (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (MAS (iidSystem quad) β κ
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
          (ar1fn ρu coinA) (ar1fn ρr coinB)) (ar1fn ρu coinA) ∧
      MIS (iidSystem quad) σ
        (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
          (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr)
          (ar1fn ρu coinA) (ar1fn ρr coinB))
        (fun t ω => rbar + ar1fn ρr coinB t ω)) ∧
    ∀ πbar xbar ibar fπ fx fi gπ gx gi,
      MAS (iidSystem quad) β κ (plan2 πbar fπ gπ (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 xbar fx gx (ar1fn ρu coinA) (ar1fn ρr coinB)) (ar1fn ρu coinA) →
      MIS (iidSystem quad) σ (plan2 πbar fπ gπ (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 xbar fx gx (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 ibar fi gi (ar1fn ρu coinA) (ar1fn ρr coinB))
        (fun t ω => rbar + ar1fn ρr coinB t ω) →
      (∀ᵐ ω ∂(iidSystem quad).μ, mLstab (iidSystem quad) β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
            (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr)
            (ar1fn ρu coinA) (ar1fn ρr coinB)) ω ≤
        mLstab (iidSystem quad) β lx li t₀ (plan2 πbar fπ gπ (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 xbar fx gx (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 ibar fi gi (ar1fn ρu coinA) (ar1fn ρr coinB)) ω) ∧
      (mLstab (iidSystem quad) β lx li t₀ (plan2 πbar fπ gπ (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 xbar fx gx (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 ibar fi gi (ar1fn ρu coinA) (ar1fn ρr coinB)) =ᵐ[(iidSystem quad).μ]
        mLstab (iidSystem quad) β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
            (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr)
            (ar1fn ρu coinA) (ar1fn ρr coinB)) ↔
        (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) := by
  obtain ⟨hA, hB, hAA, hBB, hAB, -, -⟩ := quad_moments
  exact iid2_f4_lstab hβ0 hβ1 hκ hσ hlx hli hρu hρr one_pos one_pos measurable_coinA
    measurable_coinB coinA_bdd coinB_bdd hA hB hAA hBB hAB t₀ hxs his

/-- **Equations (3.7)–(3.8)** (Woodford (2003), p. 513) on the two-coin economy: almost surely
`L^stab = L^{stab,r} + L^{stab,u}` with unit innovation variances. -/
theorem twoCoin_lstab {β lx li ρu ρr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρu : |ρu| < 1)
    (hρr : |ρr| < 1) (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) (t₀ : ℕ) :
    ∀ᵐ ω ∂(iidSystem quad).μ, mLstab (iidSystem quad) β lx li t₀
      (plan2 πbar fπ gπ (ar1fn ρu coinA) (ar1fn ρr coinB))
      (plan2 xbar fx gx (ar1fn ρu coinA) (ar1fn ρr coinB))
      (plan2 ibar fi gi (ar1fn ρu coinA) (ar1fn ρr coinB)) ω =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr 1 +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu 1 := by
  obtain ⟨hA, hB, hAA, hBB, hAB, -, -⟩ := quad_moments
  exact iid2_lstab hβ0 hβ1 hρu hρr measurable_coinA measurable_coinB coinA_bdd coinB_bdd hA hB
    hAA hBB hAB πbar xbar ibar fπ fx fi gπ gx gi t₀

end Woodford.GainsFromCommitment.NoninertialMeasureIID
