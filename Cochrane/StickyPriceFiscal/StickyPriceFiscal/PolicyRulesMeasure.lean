/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.PolicyRules
import StickyPriceFiscal.ExpectationsMeasure

/-!
# Policy rules with measure-theoretic expectations: existence and uniqueness

Cochrane (2023), Chapter 5, §5.5 "Responses and rules", pp. 147–160, eqs. (5.61)–(5.73), and
Online Appendix A1 §1.9 (pp. 573–577) and §1.11 (pp. 578–579), restated for a genuine probability
model: a `MeasExpectationSystem` (Mathlib's `condExp` on a filtered probability space), with
every model equation an almost-everywhere equality, adapted meaning Mathlib's `StronglyAdapted`,
and bounded meaning a uniform essential bound. The algebra (`Params`, `iRule`, `sNext`,
`rnNext`, `xi`, `gV`, `backRec`, the roots `lamU`, `lamS`, the coefficients `qa`, `qb`, `cKp`,
`kapS`, …) is that of `PolicyRules`; only the expectations change.

No Blanchard–Kahn theorem is needed: for any real factorisation
`z² − tr z + det = (z − λ_U)(z − λ_S)` with `λ_U > 1` the combination `f = x − g(λ_S) π`
solves the scalar forward equation `f_t = λ_U⁻¹ E_t f_{t+1} − (σ/λ_U) u_{i,t}` and inflation
obeys `π_{t+1} = λ_S π_t − (κ/β) f_t + ξ_{t+1}` (`mblock_props`), which gives uniqueness
(`mblock_unique`) and, by reversing the algebra, existence (`mblock_of`).

## Main results

* `MShocks`, `MRedSys`, `MRedEquil`, `AESame` (agreement a.e. at every date),
  `MModelDeterminate`: the measure-theoretic versions of `PolicyRules.Shocks`, `RedSys`,
  `RedEquil`, `ModelDeterminate`.
* `munique_of_factor`: at most one equilibrium (up to a.e. equality) for every `α`, given a
  factorisation with `λ_U > 1`; `mpolicyRules_unique` (passive money) and `munitroot_unique`
  (the unit root `κ(θ_iπ − 1) + (1 − β)θ_ix = 0`).
* **`mpolicyRules_determinate`**: under the passive-money condition, `|ω| < 1`, `ρ > 0` and
  `|1 − α| < ρ` there is exactly one bounded equilibrium for every admissible shock process and
  every initial inflation and debt; `mmodelDeterminate_of`.
* `malpha_exists_iff`: for `|1 − α| ≥ ρ` an equilibrium exists iff the shock-driven part of debt
  `W_{t+1} = φ W_t + κ_s ε_{s,t+1} + κ_i ε_{i,t+1}` has a bounded adapted solution.
* `munitroot_exists_iff`: on the unit root an equilibrium exists iff the inflation martingale
  `W = π + k u_i` has a bounded adapted solution.
* `mnonexist_of_alpha`: `|1 − α| > ρ` leaves zero shocks, `π_0 = 0`, `v_0 = 1` without an
  equilibrium.
-/

namespace Cochrane.StickyPriceFiscal.PolicyRulesMeasure

open MeasureTheory Filter Topology
open ExpectationsMeasure PolicyRules

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The model with measure-theoretic expectations -/

/-- Cochrane (2023), eqs. (5.61)–(5.62), p. 147: the exogenous disturbances in a probability
model. The shocks `ε_i, ε_s` are bounded, adapted and unpredictable (`E_t ε_{t+1} = 0` a.e.); the
disturbances `u_i, u_s` are bounded adapted AR(1) processes driven by them. -/
def MShocks (P : Params) (ei es ui us : ℕ → Ω → ℝ) : Prop :=
  StronglyAdapted S.𝓕 ei ∧ StronglyAdapted S.𝓕 es ∧ StronglyAdapted S.𝓕 ui ∧
    StronglyAdapted S.𝓕 us ∧ S.BddProc ei ∧ S.BddProc es ∧ S.BddProc ui ∧ S.BddProc us ∧
    (∀ t, S.E t (ei (t + 1)) =ᵐ[S.μ] 0) ∧ (∀ t, S.E t (es (t + 1)) =ᵐ[S.μ] 0) ∧
    (∀ t, ui (t + 1) = P.etaI • ui t + ei (t + 1)) ∧
    (∀ t, us (t + 1) = P.etaS • us t + es (t + 1))

/-- Cochrane (2023), eqs. (5.64)–(5.73), pp. 148–149, a.e.: (5.64) IS curve, (5.65) Phillips
curve, (5.68) unexpected inflation, (5.71) debt flow, (5.72) expectations hypothesis. -/
def MRedSys (P : Params) (ei es ui us x p q v : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - S.E t (p (t + 1)))) ∧
  (∀ t, p t =ᵐ[S.μ] P.beta • S.E t (p (t + 1)) + P.kappa • x t) ∧
  (∀ t, S.innov t (p (t + 1)) =ᵐ[S.μ] -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1)) ∧
  (∀ t, P.rho • v (t + 1) =ᵐ[S.μ] v t + rnNext P q t - p (t + 1) - sNext P x p v us t) ∧
  (∀ t, S.E t (rnNext P q t) =ᵐ[S.μ] iRule P x p ui t)

/-- Cochrane (2023), pp. 148–149: an equilibrium of the reduced model in a probability model — a
bounded adapted a.e. solution with initial inflation `π_0` and initial value of debt `v_0`. -/
def MRedEquil (P : Params) (ei es ui us : ℕ → Ω → ℝ) (p0 v0 : ℝ) (x p q v : ℕ → Ω → ℝ) :
    Prop :=
  MRedSys S P ei es ui us x p q v ∧
  StronglyAdapted S.𝓕 x ∧ StronglyAdapted S.𝓕 p ∧ StronglyAdapted S.𝓕 q ∧
  StronglyAdapted S.𝓕 v ∧ S.BddProc x ∧ S.BddProc p ∧ S.BddProc q ∧ S.BddProc v ∧
  p 0 =ᵐ[S.μ] (fun _ => p0) ∧ v 0 =ᵐ[S.μ] (fun _ => v0)

/-- Cochrane (2023), p. 148 ("the unique equilibrium", in a probability model): two candidate
equilibria agree almost surely at every date. -/
def AESame (x p q v x' p' q' v' : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t =ᵐ[S.μ] x' t ∧ p t =ᵐ[S.μ] p' t ∧ q t =ᵐ[S.μ] q' t ∧ v t =ᵐ[S.μ] v' t

/-- Cochrane (2023), §5.5, p. 148 ("the unique stationary equilibrium"), at model level in a
probability model: for every admissible shock process and every initial inflation and debt an
equilibrium exists, and any two agree almost surely at every date. -/
def MModelDeterminate (P : Params) : Prop :=
  ∀ ei es ui us : ℕ → Ω → ℝ, MShocks S P ei es ui us → ∀ p0 v0 : ℝ,
    (∃ x p q v, MRedEquil S P ei es ui us p0 v0 x p q v) ∧
    ∀ x p q v x' p' q' v', MRedEquil S P ei es ui us p0 v0 x p q v →
      MRedEquil S P ei es ui us p0 v0 x' p' q' v' → AESame S x p q v x' p' q' v'

/-- Cochrane (2023), (5.64)–(5.68), pp. 148–149: the `(x, π)` block in a probability model — the
IS curve, the Phillips curve and unexpected inflation, with bounded adapted `x, π`. -/
def MBlock (P : Params) (ei es ui x p : ℕ → Ω → ℝ) : Prop :=
  (∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - P.sigma • (iRule P x p ui t - S.E t (p (t + 1)))) ∧
  (∀ t, p t =ᵐ[S.μ] P.beta • S.E t (p (t + 1)) + P.kappa • x t) ∧
  (∀ t, S.innov t (p (t + 1)) =ᵐ[S.μ] -(P.betaS • es (t + 1)) - P.betaI • ei (t + 1)) ∧
  StronglyAdapted S.𝓕 x ∧ StronglyAdapted S.𝓕 p ∧ S.BddProc x ∧ S.BddProc p

/-! ### Tools: integrability, linearity, boundedness -/

/-- Cochrane (2023), p. 148 (tool): a bounded adapted process is integrable at every date. -/
theorem int_of {x : ℕ → Ω → ℝ} (ha : StronglyAdapted S.𝓕 x) (hb : S.BddProc x) (t : ℕ) :
    Integrable (x t) S.μ := by
  obtain ⟨M, hM⟩ := hb
  exact (MeasExpectationSystem.BddRV.of_stronglyMeasurable (ha t) (hM t)).integrable

/-- Cochrane (2023), p. 148 (tool): a bounded adapted variable is its own forecast. -/
theorem E_self {x : ℕ → Ω → ℝ} (ha : StronglyAdapted S.𝓕 x) (hb : S.BddProc x) (t : ℕ) :
    S.E t (x t) = x t :=
  S.E_of_stronglyMeasurable (ha t) (int_of S ha hb t)

/-- Cochrane (2023), p. 148 (tool): `E_t (a y + b z) = a E_t y + b E_t z` a.e. -/
theorem E_comb {y z : Ω → ℝ} (hy : Integrable y S.μ) (hz : Integrable z S.μ) (a b : ℝ)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, S.E t (a • y + b • z) ω = a * S.E t y ω + b * S.E t z ω := by
  filter_upwards [S.E_add (hy.smul a) (hz.smul b) t, S.E_smul a y t, S.E_smul b z t]
    with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]

/-- Cochrane (2023), p. 148 (tool): `E_t (y − b z) = E_t y − b E_t z` a.e. -/
theorem E_sub_smul {y z : Ω → ℝ} (hy : Integrable y S.μ) (hz : Integrable z S.μ) (b : ℝ)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, S.E t (y - b • z) ω = S.E t y ω - b * S.E t z ω := by
  filter_upwards [S.E_sub hy (hz.smul b) t, S.E_smul b z t] with ω h1 h2
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), p. 148 (tool): `E_t (y + b z) = E_t y + b E_t z` a.e. -/
theorem E_add_smul {y z : Ω → ℝ} (hy : Integrable y S.μ) (hz : Integrable z S.μ) (b : ℝ)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, S.E t (y + b • z) ω = S.E t y ω + b * S.E t z ω := by
  filter_upwards [S.E_add hy (hz.smul b) t, S.E_smul b z t] with ω h1 h2
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul]

/-- Cochrane (2023), p. 148 (tool): adding a variable known at `t` commutes with `E_t`. -/
theorem E_known_add {t : ℕ} {z w : Ω → ℝ} (hz : StronglyMeasurable[S.𝓕 t] z)
    (hzi : Integrable z S.μ) (hw : Integrable w S.μ) :
    ∀ᵐ ω ∂S.μ, S.E t (z + w) ω = z ω + S.E t w ω := by
  filter_upwards [S.E_add hzi hw t] with ω h1
  rw [h1, Pi.add_apply, S.E_of_stronglyMeasurable hz hzi]

/-- Cochrane (2023), p. 148 (tool): sums of bounded processes are bounded. -/
theorem mbdd_add {a b : ℕ → Ω → ℝ} (ha : S.BddProc a) (hb : S.BddProc b) :
    S.BddProc (a + b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t => by
    filter_upwards [hA t, hB t] with ω h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)⟩

/-- Cochrane (2023), p. 148 (tool): differences of bounded processes are bounded. -/
theorem mbdd_sub {a b : ℕ → Ω → ℝ} (ha : S.BddProc a) (hb : S.BddProc b) :
    S.BddProc (a - b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun t => by
    filter_upwards [hA t, hB t] with ω h1 h2
    exact (abs_sub _ _).trans (add_le_add h1 h2)⟩

/-- Cochrane (2023), p. 148 (tool): multiples of bounded processes are bounded. -/
theorem mbdd_smul (c : ℝ) {a : ℕ → Ω → ℝ} (ha : S.BddProc a) : S.BddProc (c • a) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨|c| * A, fun t => by
    filter_upwards [hA t] with ω h1
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)⟩

/-- Cochrane (2023), p. 148 (tool): the one-period lead of a bounded process is bounded. -/
theorem mbdd_shift {a : ℕ → Ω → ℝ} (ha : S.BddProc a) : S.BddProc (fun t => a (t + 1)) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun t => hA (t + 1)⟩

/-- Cochrane (2023), p. 148 (tool): the zero process is bounded. -/
theorem mbdd_zero : S.BddProc (0 : ℕ → Ω → ℝ) :=
  ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩

/-- Cochrane (2023), (5.68), p. 149 (tool): `ξ` is adapted. -/
theorem xi_adaptedM {P : Params} {ei es : ℕ → Ω → ℝ} (hea : StronglyAdapted S.𝓕 ei)
    (hesa : StronglyAdapted S.𝓕 es) : StronglyAdapted S.𝓕 (xi P ei es) := by
  intro t
  cases t with
  | zero => exact stronglyMeasurable_zero
  | succ t =>
    rw [xi_succ]
    exact (((hesa (t + 1)).const_smul P.betaS).neg).sub ((hea (t + 1)).const_smul P.betaI)

/-- Cochrane (2023), (5.68), p. 149 (tool): `ξ` is bounded. -/
theorem xi_bddM {P : Params} {ei es : ℕ → Ω → ℝ} (heb : S.BddProc ei) (hesb : S.BddProc es) :
    S.BddProc (xi P ei es) := by
  obtain ⟨A, hA⟩ := heb
  obtain ⟨B, hB⟩ := hesb
  refine ⟨|P.betaS| * |B| + |P.betaI| * |A|, fun t => ?_⟩
  cases t with
  | zero =>
    exact Eventually.of_forall fun ω => by simp only [xi, Pi.zero_apply, abs_zero]; positivity
  | succ t =>
    filter_upwards [hA (t + 1), hB (t + 1)] with ω h1 h2
    simp only [xi_succ, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    calc |-(P.betaS * es (t + 1) ω) - P.betaI * ei (t + 1) ω|
        ≤ |P.betaS * es (t + 1) ω| + |P.betaI * ei (t + 1) ω| := by
          have := abs_sub (-(P.betaS * es (t + 1) ω)) (P.betaI * ei (t + 1) ω)
          rwa [abs_neg] at this
      _ ≤ |P.betaS| * |B| + |P.betaI| * |A| := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left (h2.trans (le_abs_self B)) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (h1.trans (le_abs_self A)) (abs_nonneg _))

/-- Cochrane (2023), (5.68), p. 149 (tool): `ξ` is unpredictable, `E_t ξ_{t+1} = 0` a.e. -/
theorem E_xiM {P : Params} {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us) (t : ℕ) :
    S.E t (xi P ei es (t + 1)) =ᵐ[S.μ] 0 := by
  obtain ⟨hea, hesa, -, -, heb, hesb, -, -, hei, hes, -, -⟩ := hsh
  have h1 := int_of S hea heb (t + 1)
  have h2 := int_of S hesa hesb (t + 1)
  rw [xi_succ, ← neg_smul]
  filter_upwards [S.E_sub (h2.smul (-P.betaS)) (h1.smul P.betaI) t,
    S.E_smul (-P.betaS) (es (t + 1)) t, S.E_smul P.betaI (ei (t + 1)) t, hei t, hes t]
    with ω e1 e3 e4 e5 e6
  rw [e1, Pi.sub_apply, e3, e4, Pi.smul_apply, Pi.smul_apply, e5, e6]
  simp

/-! ### The algebra of a real factorisation `z² − tr z + det = (z − λ_U)(z − λ_S)` -/

/-- Online Appendix A1 §1.9, p. 574 (tool): `1 + σθ_ix + σκ/β + g κ/β = λ_U`, with the output
gain `g = g(λ_S) = (1 − βλ_S)/κ`. -/
theorem alg_K1 {P : Params} (hβ : P.beta ≠ 0) (hκ : P.kappa ≠ 0) {lU lS : ℝ}
    (hsum : lU + lS = trB P) :
    1 + P.sigma * P.thIx + P.sigma * P.kappa / P.beta + gainOf P lS * P.kappa / P.beta = lU := by
  have hU' : lU = trB P - lS := by linarith
  rw [hU', trB_eq, gainOf]
  field_simp
  ring

/-- Online Appendix A1 §1.9, p. 574 (tool): `σθ_iπ − σ/β − g/β = −λ_U g`, since `λ_S` is a root. -/
theorem alg_K2 {P : Params} (hβ : P.beta ≠ 0) (hκ : P.kappa ≠ 0) {lU lS : ℝ}
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) :
    P.sigma * P.thIpi - P.sigma / P.beta - gainOf P lS / P.beta = -(lU * gainOf P lS) := by
  have hch : charB P lS = 0 := by rw [charB, ← hsum, ← hprod]; ring
  have hU' : lU = trB P - lS := by linarith
  have key : P.sigma * P.thIpi - P.sigma / P.beta - gainOf P lS / P.beta + lU * gainOf P lS =
      P.beta / P.kappa * charB P lS := by
    rw [hU', charB, trB_eq, detB_eq hβ, gainOf]
    field_simp
    ring
  rw [hch, mul_zero] at key
  linarith

/-- Online Appendix A1 §1.9, p. 574 (tool): `g λ_S − g − σθ_iπ − σθ_ix g + σλ_S = 0`. -/
theorem alg_K3 {P : Params} (hβ : P.beta ≠ 0) (hκ : P.kappa ≠ 0) {lU lS : ℝ}
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) :
    gainOf P lS * lS - gainOf P lS - P.sigma * P.thIpi - P.sigma * P.thIx * gainOf P lS +
      P.sigma * lS = 0 := by
  have hch : charB P lS = 0 := by rw [charB, ← hsum, ← hprod]; ring
  have key : gainOf P lS * lS - gainOf P lS - P.sigma * P.thIpi -
      P.sigma * P.thIx * gainOf P lS + P.sigma * lS = -(P.beta / P.kappa) * charB P lS := by
    rw [charB, trB_eq, detB_eq hβ, gainOf]
    field_simp
    ring
  rw [key, hch, mul_zero]

/-- Cochrane (2023), §5.5.2, p. 152 (tool): `κ g(λ) = 1 − βλ`. -/
theorem alg_K4 {P : Params} (hκ : P.kappa ≠ 0) (lS : ℝ) :
    P.kappa * gainOf P lS = 1 - P.beta * lS := by
  rw [gainOf]
  field_simp

/-- Online Appendix A1 §1.9, pp. 574–575 (pointwise): if the IS curve and the Phillips curve hold
at a state, then `E_t f_{t+1} = λ_U f_t + σ u_{i,t}` for `f = x − gπ`, and
`E_t π_{t+1} = λ_S π_t − (κ/β) f_t`. -/
theorem blk_pt {P : Params} (hβ : P.beta ≠ 0) (hκ : P.kappa ≠ 0) {lU lS : ℝ}
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) {X Pp U EX EP : ℝ}
    (e64 : X = EX - P.sigma * (P.thIpi * Pp + P.thIx * X + U - EP))
    (e65 : Pp = P.beta * EP + P.kappa * X) :
    EX - gainOf P lS * EP = lU * (X - gainOf P lS * Pp) + P.sigma * U ∧
      EP = lS * Pp - P.kappa / P.beta * (X - gainOf P lS * Pp) := by
  have k1 := alg_K1 hβ hκ hsum
  have k2 := alg_K2 hβ hκ hsum hprod
  have k4 := alg_K4 (P := P) hκ lS
  have hEP : EP = (Pp - P.kappa * X) / P.beta := by
    field_simp
    linarith
  have hEX : EX = X + P.sigma * (P.thIpi * Pp + P.thIx * X + U) - P.sigma * EP := by linarith
  constructor
  · rw [hEX, hEP]
    linear_combination X * k1 + Pp * k2
  · rw [hEP]
    field_simp
    linear_combination (-Pp) * k4

/-- Online Appendix A1 §1.9, pp. 574–575 (pointwise, the converse): if `E_t f_{t+1} = λ_U f_t +
σ u_{i,t}` and `E_t π_{t+1} = λ_S π_t − (κ/β) f_t`, then `x = f + gπ` satisfies the IS curve and
the Phillips curve at the state. -/
theorem blk_exist_pt {P : Params} (hβ : P.beta ≠ 0) (hκ : P.kappa ≠ 0) {lU lS : ℝ}
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) {F Pp U EF EP : ℝ}
    (eF : EF = lU * F + P.sigma * U) (eP : EP = lS * Pp - P.kappa / P.beta * F) :
    F + gainOf P lS * Pp = (EF + gainOf P lS * EP) -
        P.sigma * (P.thIpi * Pp + P.thIx * (F + gainOf P lS * Pp) + U - EP) ∧
      Pp = P.beta * EP + P.kappa * (F + gainOf P lS * Pp) := by
  have k1 := alg_K1 hβ hκ hsum
  have k3 := alg_K3 hβ hκ hsum hprod
  have k4 := alg_K4 (P := P) hκ lS
  have hb : P.beta * (P.kappa / P.beta) = P.kappa := mul_div_cancel₀ _ hβ
  rw [eF, eP]
  constructor
  · linear_combination F * k1 - Pp * k3
  · linear_combination (-Pp) * k4 + F * hb

/-! ### The `(x, π)` block without Blanchard–Kahn -/

/-- Online Appendix A1 §1.9, p. 574 (the forward-looking combination): `f_t = x_t − G π_t`. -/
def fwd (G : ℝ) (x p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => x t - G • p t

/-- Online Appendix A1 §1.9 (tool): `f` is adapted. -/
theorem fwd_adapted {G : ℝ} {x p : ℕ → Ω → ℝ} (hx : StronglyAdapted S.𝓕 x)
    (hp : StronglyAdapted S.𝓕 p) : StronglyAdapted S.𝓕 (fwd G x p) :=
  fun t => (hx t).sub ((hp t).const_smul G)

/-- Online Appendix A1 §1.9 (tool): `f` is bounded. -/
theorem fwd_bdd {G : ℝ} {x p : ℕ → Ω → ℝ} (hx : S.BddProc x) (hp : S.BddProc p) :
    S.BddProc (fwd G x p) :=
  mbdd_sub S hx (mbdd_smul S G hp)

/-- Online Appendix A1 §1.9, pp. 574–575, in a probability model: for any real factorisation
with `λ_U ≠ 0`, every bounded adapted solution of the block has `f = x − g(λ_S)π` solving
`f_t = λ_U⁻¹ E_t f_{t+1} − (σ/λ_U) u_{i,t}` and `π_{t+1} = λ_S π_t − (κ/β) f_t + ξ_{t+1}` a.e. -/
theorem mblock_props {P : Params} (hP : Standard P) {lU lS : ℝ} (hU0 : lU ≠ 0)
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) {ei es ui x p : ℕ → Ω → ℝ}
    (h : MBlock S P ei es ui x p) :
    S.Solves lU⁻¹ (fun t => (-(P.sigma / lU)) • ui t) (fwd (gainOf P lS) x p) ∧
    ∀ t, p (t + 1) =ᵐ[S.μ] lS • p t - (P.kappa / P.beta) • fwd (gainOf P lS) x p t +
      xi P ei es (t + 1) := by
  obtain ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩ := h
  have hβ := hP.2.2.1.ne'
  have hκ := hP.2.1.ne'
  constructor
  · intro t
    filter_upwards [h64 t, h65 t, E_sub_smul S (int_of S hxa hxb (t + 1))
      (int_of S hpa hpb (t + 1)) (gainOf P lS) t] with ω e64 e65 eE
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e64 e65
    obtain ⟨k1, -⟩ := blk_pt hβ hκ hsum hprod e64 e65
    simp only [fwd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [eE, k1]
    field_simp
    ring
  · intro t
    filter_upwards [h64 t, h65 t, h68 t] with ω e64 e65 e68
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e64 e65
    obtain ⟨-, k2⟩ := blk_pt hβ hκ hsum hprod e64 e65
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, E_self S hpa hpb (t + 1)] at e68
    simp only [fwd, xi_succ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul] at e68 ⊢
    linear_combination e68 + k2

/-- Online Appendix A1 §1.9, pp. 574–576, in a probability model: **uniqueness of the block**.
For any real factorisation with `λ_U > 1` (passive money, or the unit root), two bounded adapted
solutions of (5.64), (5.65), (5.68) with the same initial inflation agree a.e. at every date. -/
theorem mblock_unique {P : Params} (hP : Standard P) {lU lS : ℝ} (hU : 1 < lU)
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) {ei es ui x p x' p' : ℕ → Ω → ℝ}
    {p0 : ℝ} (h : MBlock S P ei es ui x p) (h' : MBlock S P ei es ui x' p')
    (hp0 : p 0 =ᵐ[S.μ] fun _ => p0) (hp0' : p' 0 =ᵐ[S.μ] fun _ => p0) :
    ∀ t, x t =ᵐ[S.μ] x' t ∧ p t =ᵐ[S.μ] p' t := by
  have hU0 : lU ≠ 0 := by linarith
  obtain ⟨hf, hps⟩ := mblock_props S hP hU0 hsum hprod h
  obtain ⟨hf', hps'⟩ := mblock_props S hP hU0 hsum hprod h'
  obtain ⟨-, -, -, hxa, hpa, hxb, hpb⟩ := h
  obtain ⟨-, -, -, hxa', hpa', hxb', hpb'⟩ := h'
  have hinv : |lU⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < lU)]
    exact inv_lt_one_of_one_lt₀ hU
  have hff := S.forward_unique hinv hf hf'
    (fun t => ((fwd_adapted S hxa hpa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => ((fwd_adapted S hxa' hpa' t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fwd_bdd S hxb hpb) (fwd_bdd S hxb' hpb')
  have hpp : ∀ t, p t =ᵐ[S.μ] p' t := by
    intro t
    induction t with
    | zero => exact hp0.trans hp0'.symm
    | succ t ih =>
      filter_upwards [hps t, hps' t, ih, hff t] with ω e e' e1 e2
      rw [e, e']
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e1, e2]
  intro t
  refine ⟨?_, hpp t⟩
  filter_upwards [hff t, hpp t] with ω e1 e2
  simp only [fwd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1
  rw [e2] at e1
  linarith

/-- Cochrane (2023), p. 148 (tool): a variable equal a.e. to something known at `t` plus
unpredictable news has that known part as its forecast. -/
theorem E_of_pred {t : ℕ} {y z w : Ω → ℝ} (hy : y =ᵐ[S.μ] z + w)
    (hz : StronglyMeasurable[S.𝓕 t] z) (hzi : Integrable z S.μ) (hwi : Integrable w S.μ)
    (hw : S.E t w =ᵐ[S.μ] 0) : S.E t y =ᵐ[S.μ] z := by
  filter_upwards [S.E_congr hy t, E_known_add S hz hzi hwi, hw] with ω h1 h2 h3
  rw [h1, h2, h3, Pi.zero_apply, add_zero]

/-- Online Appendix A1 §1.9, pp. 574–575, in a probability model: **the block from its forward
part**. If `f` is a bounded adapted solution of `f_t = λ_U⁻¹ E_t f_{t+1} − (σ/λ_U) u_{i,t}` and
`π` a bounded adapted process with `π_{t+1} = λ_S π_t − (κ/β) f_t + ξ_{t+1}` a.e., then
`(x, π) = (f + g(λ_S)π, π)` solves (5.64), (5.65), (5.68). -/
theorem mblock_of {P : Params} (hP : Standard P) {lU lS : ℝ} (hU0 : lU ≠ 0)
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) {ei es ui us : ℕ → Ω → ℝ}
    (hsh : MShocks S P ei es ui us) {f p : ℕ → Ω → ℝ}
    (hf : S.Solves lU⁻¹ (fun t => (-(P.sigma / lU)) • ui t) f) (hfa : StronglyAdapted S.𝓕 f)
    (hfb : S.BddProc f) (hpa : StronglyAdapted S.𝓕 p) (hpb : S.BddProc p)
    (hp : ∀ t, p (t + 1) =ᵐ[S.μ] lS • p t - (P.kappa / P.beta) • f t + xi P ei es (t + 1)) :
    MBlock S P ei es ui (fun t => f t + gainOf P lS • p t) p := by
  have hβ := hP.2.2.1.ne'
  have hκ := hP.2.1.ne'
  have hsh' := hsh
  obtain ⟨hea, hesa, hua, -, heb, hesb, hub, -, -, -, -, -⟩ := hsh'
  have hxia := xi_adaptedM S (P := P) hea hesa
  have hxib := xi_bddM S (P := P) heb hesb
  have hEp : ∀ t, S.E t (p (t + 1)) =ᵐ[S.μ] lS • p t - (P.kappa / P.beta) • f t := fun t =>
    E_of_pred S (hp t) (((hpa t).const_smul lS).sub ((hfa t).const_smul _))
      (((int_of S hpa hpb t).smul lS).sub ((int_of S hfa hfb t).smul _))
      (int_of S hxia hxib (t + 1)) (E_xiM S hsh t)
  have hEf : ∀ t, ∀ᵐ ω ∂S.μ, S.E t (f (t + 1)) ω = lU * f t ω + P.sigma * ui t ω := by
    intro t
    filter_upwards [hf t] with ω e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
    rw [e]
    field_simp
    ring
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => (hfa t).add ((hpa t).const_smul _),
    hpa, mbdd_add S hfb (mbdd_smul S _ hpb), hpb⟩
  · filter_upwards [hEp t, hEf t, E_add_smul S (int_of S hfa hfb (t + 1))
      (int_of S hpa hpb (t + 1)) (gainOf P lS) t] with ω e1 e2 e3
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e3, e2, e1]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact (blk_exist_pt hβ hκ hsum hprod rfl rfl).1
  · filter_upwards [hEp t] with ω e1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact (blk_exist_pt hβ hκ hsum hprod (U := ui t ω) rfl rfl).2
  · filter_upwards [hp t, hEp t] with ω e1 e2
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, E_self S hpa hpb (t + 1)]
    rw [e1, e2]
    simp only [xi_succ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring

/-! ### The bond price and the debt recursion -/

/-- Cochrane (2023), (5.73), p. 149 (tool): `E_t r^n_{t+1} = ω E_t q_{t+1} − q_t` a.e. -/
theorem E_rnNext {P : Params} {q : ℕ → Ω → ℝ} (hqa : StronglyAdapted S.𝓕 q) (hqb : S.BddProc q)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, S.E t (rnNext P q t) ω = P.omega * S.E t (q (t + 1)) ω - q t ω := by
  filter_upwards [S.E_sub ((int_of S hqa hqb (t + 1)).smul P.omega) (int_of S hqa hqb t) t,
    S.E_smul P.omega (q (t + 1)) t] with ω h1 h2
  rw [rnNext, h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul, E_self S hqa hqb t]

/-- Cochrane (2023), (5.72)–(5.73), p. 149, in a probability model: for a bounded adapted bond
price the expectations hypothesis is the forward equation `q_t = ω E_t q_{t+1} − i_t` (a.e.). -/
theorem meq572_iff {P : Params} {x p ui q : ℕ → Ω → ℝ} (hqa : StronglyAdapted S.𝓕 q)
    (hqb : S.BddProc q) :
    (∀ t, S.E t (rnNext P q t) =ᵐ[S.μ] iRule P x p ui t) ↔
      S.Solves P.omega (fun t => -iRule P x p ui t) q := by
  constructor
  · intro h t
    filter_upwards [h t, E_rnNext S hqa hqb t] with ω e1 e2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    rw [← e1, e2]
    ring
  · intro h t
    filter_upwards [h t, E_rnNext S hqa hqb t] with ω e1 e2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at e1
    rw [e2]
    linarith

/-- Cochrane (2023), (5.72)–(5.73), p. 149, in a probability model: for bounded adapted `x, π`,
`u_i` and `|ω| < 1` there is a bounded adapted bond price satisfying (5.72) (the forward solution
`q_t = −∑ ωᵏ E_t i_{t+k}`). -/
theorem mq_exists {P : Params} (hω : |P.omega| < 1) {x p ui : ℕ → Ω → ℝ}
    (hxa : StronglyAdapted S.𝓕 x) (hpa : StronglyAdapted S.𝓕 p) (hua : StronglyAdapted S.𝓕 ui)
    (hxb : S.BddProc x) (hpb : S.BddProc p) (hub : S.BddProc ui) :
    ∃ q, StronglyAdapted S.𝓕 q ∧ S.BddProc q ∧
      ∀ t, S.E t (rnNext P q t) =ᵐ[S.μ] iRule P x p ui t := by
  have hia : StronglyAdapted S.𝓕 (fun t => -iRule P x p ui t) := fun t =>
    ((((hpa t).const_smul P.thIpi).add ((hxa t).const_smul P.thIx)).add (hua t)).neg
  have hib : S.BddProc (fun t => -iRule P x p ui t) := by
    obtain ⟨M, hM⟩ := mbdd_add S (mbdd_add S (mbdd_smul S P.thIpi hpb)
      (mbdd_smul S P.thIx hxb)) hub
    refine ⟨M, fun t => ?_⟩
    filter_upwards [hM t] with ω h
    change |-(iRule P x p ui t ω)| ≤ M
    rw [abs_neg]
    exact h
  obtain ⟨⟨hs, ha, hb⟩, -⟩ := S.existsUnique_forward hω hia hib
  exact ⟨_, ha, hb, (meq572_iff S ha hb).mpr hs⟩

/-- Cochrane (2023), (5.69)–(5.71), p. 149, in a probability model: with `ρ ≠ 0` the debt flow
(5.71) holds a.e. at `t` iff `v_{t+1} = ((1 − α)/ρ) v_t + g_t` a.e. -/
theorem mdebt_iff {P : Params} (hρ : P.rho ≠ 0) {x p q v us : ℕ → Ω → ℝ} (t : ℕ) :
    (P.rho • v (t + 1) =ᵐ[S.μ] v t + rnNext P q t - p (t + 1) - sNext P x p v us t) ↔
      v (t + 1) =ᵐ[S.μ] debtRoot P • v t + gV P x p q us t := by
  constructor
  · intro h
    filter_upwards [h] with ω e
    simp only [gV, sNext, rnNext, debtRoot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    field_simp
    linear_combination e
  · intro h
    filter_upwards [h] with ω e
    simp only [gV, sNext, rnNext, debtRoot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] at e ⊢
    rw [e]
    field_simp
    ring

/-- Cochrane (2023), (5.71), p. 149 (tool): the forcing `g` of the debt recursion is bounded. -/
theorem mbdd_gV {P : Params} {x p q us : ℕ → Ω → ℝ} (hxb : S.BddProc x) (hpb : S.BddProc p)
    (hqb : S.BddProc q) (husb : S.BddProc us) : S.BddProc (gV P x p q us) :=
  mbdd_smul S P.rho⁻¹ (mbdd_sub S (mbdd_sub S (mbdd_sub S (mbdd_sub S
    (mbdd_smul S P.omega (mbdd_shift S hqb)) hqb) (mbdd_smul S (1 + P.thSpi)
    (mbdd_shift S hpb))) (mbdd_smul S P.thSx (mbdd_shift S hxb))) (mbdd_shift S husb))

/-- Cochrane (2023), (5.71), p. 149 (tool): `g_t` is known at `t + 1`. -/
theorem gV_meas {P : Params} {x p q us : ℕ → Ω → ℝ} (hxa : StronglyAdapted S.𝓕 x)
    (hpa : StronglyAdapted S.𝓕 p) (hqa : StronglyAdapted S.𝓕 q) (husa : StronglyAdapted S.𝓕 us)
    (t : ℕ) : StronglyMeasurable[S.𝓕 (t + 1)] (gV P x p q us t) :=
  ((((((hqa (t + 1)).const_smul P.omega).sub ((hqa t).mono (S.𝓕.mono (Nat.le_succ t)))).sub
    ((hpa (t + 1)).const_smul _)).sub ((hxa (t + 1)).const_smul _)).sub (husa (t + 1))).const_smul _

/-- Cochrane (2023), (5.71), p. 149 (tool): the backward recursion is adapted when `g_t` is known
at `t + 1`. -/
theorem backRec_adaptedM {φ : ℝ} {g : ℕ → Ω → ℝ}
    (hg : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (g t)) (v0 : ℝ) :
    StronglyAdapted S.𝓕 (backRec φ g v0) := by
  intro t
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih => exact ((ih.mono (S.𝓕.mono (Nat.le_succ t))).const_smul φ).add (hg t)

/-- Cochrane (2023), (5.71), p. 149 (tool): with `|φ| < 1` and an essentially bounded `g` the
backward recursion is essentially bounded. -/
theorem backRec_bddM {φ M : ℝ} (hφ : |φ| < 1) {g : ℕ → Ω → ℝ}
    (hg : ∀ t, ∀ᵐ ω ∂S.μ, |g t ω| ≤ M) (v0 : ℝ) : S.BddProc (backRec φ g v0) := by
  obtain ⟨ω0, hω0⟩ := (hg 0).exists
  have hM : 0 ≤ M := (abs_nonneg _).trans hω0
  refine ⟨|v0| + M / (1 - |φ|), fun t => ?_⟩
  filter_upwards [ae_all_iff.2 hg] with ω h
  refine SharedTools.bounded_of_rec (x := fun t => backRec φ g v0 t ω) (abs_nonneg φ) hφ hM
    (by simp only [backRec]; rfl) (fun t => ?_) t
  simp only [backRec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← abs_mul]
  exact (abs_add_le _ _).trans (add_le_add le_rfl (h t))

/-! ### Uniqueness for every `α`, and determinacy -/

/-- Cochrane (2023), pp. 148–149 and A1 §1.9, in a probability model: **at most one equilibrium**
for every `α`. For any real factorisation with `λ_U > 1`, `|ω| < 1` and `ρ ≠ 0`, two bounded
equilibria with the same initial inflation and debt agree a.e. at every date (the block by
`mblock_unique`, the bond price by the forward equation, the debt by its backward recursion). -/
theorem munique_of_factor {P : Params} (hP : Standard P) {lU lS : ℝ} (hU : 1 < lU)
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) (hω : |P.omega| < 1) (hρ : P.rho ≠ 0)
    {ei es ui us : ℕ → Ω → ℝ} {p0 v0 : ℝ} {x p q v x' p' q' v' : ℕ → Ω → ℝ}
    (h : MRedEquil S P ei es ui us p0 v0 x p q v)
    (h' : MRedEquil S P ei es ui us p0 v0 x' p' q' v') : AESame S x p q v x' p' q' v' := by
  obtain ⟨⟨h64, h65, h68, h71, h72⟩, hxa, hpa, hqa, -, hxb, hpb, hqb, -, hp0, hv0⟩ := h
  obtain ⟨⟨h64', h65', h68', h71', h72'⟩, hxa', hpa', hqa', -, hxb', hpb', hqb', -, hp0',
    hv0'⟩ := h'
  have hblk := mblock_unique S hP hU hsum hprod ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩
    ⟨h64', h65', h68', hxa', hpa', hxb', hpb'⟩ hp0 hp0'
  have hs := (meq572_iff S hqa hqb).mp h72
  have hs' := (meq572_iff S hqa' hqb').mp h72'
  have hs'' : S.Solves P.omega (fun t => -iRule P x p ui t) q' := by
    intro t
    filter_upwards [hs' t, (hblk t).1, (hblk t).2] with ω e e1 e2
    rw [e]
    simp only [iRule, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    rw [e1, e2]
  have hqq := S.forward_unique hω hs hs''
    (fun t => ((hqa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => ((hqa' t).mono (S.𝓕.le t)).aestronglyMeasurable) hqb hqb'
  have hr := fun t => (mdebt_iff S hρ t).mp (h71 t)
  have hr' := fun t => (mdebt_iff S hρ t).mp (h71' t)
  have hvv : ∀ t, v t =ᵐ[S.μ] v' t := by
    intro t
    induction t with
    | zero => exact hv0.trans hv0'.symm
    | succ t ih =>
      filter_upwards [hr t, hr' t, ih, (hblk (t + 1)).1, (hblk (t + 1)).2, hqq t, hqq (t + 1)]
        with ω e e' e1 e2 e3 e4 e5
      rw [e, e']
      simp only [gV, rnNext, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e1, e2, e3, e4, e5]
  exact fun t => ⟨(hblk t).1, (hblk t).2, hqq t, hvv t⟩

/-- Cochrane (2023), pp. 148–149 (uniqueness for every `α`), in a probability model: under the
sign restrictions, the passive-money condition, `|ω| < 1` and `ρ ≠ 0`, two bounded equilibria
agree a.e. at every date, whatever the debt response `α`. -/
theorem mpolicyRules_unique {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ : P.rho ≠ 0) {ei es ui us : ℕ → Ω → ℝ} {p0 v0 : ℝ}
    {x p q v x' p' q' v' : ℕ → Ω → ℝ} (h : MRedEquil S P ei es ui us p0 v0 x p q v)
    (h' : MRedEquil S P ei es ui us p0 v0 x' p' q' v') : AESame S x p q v x' p' q' v' := by
  obtain ⟨-, hU, -, -, hsum, hprod⟩ := roots_passive hP hpass
  exact munique_of_factor S hP hU hsum hprod hω hρ h h'

/-- Cochrane (2023), A1 §1.9, pp. 574–576 (E20), in a probability model: on the boundary
`κ(θ_iπ − 1) + (1 − β)θ_ix = 0` (roots `det > 1` and `1`), with `|ω| < 1` and `ρ ≠ 0`, two
bounded equilibria agree a.e. at every date. -/
theorem munitroot_unique {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hω : |P.omega| < 1)
    (hρ : P.rho ≠ 0) {ei es ui us : ℕ → Ω → ℝ} {p0 v0 : ℝ} {x p q v x' p' q' v' : ℕ → Ω → ℝ}
    (h : MRedEquil S P ei es ui us p0 v0 x p q v)
    (h' : MRedEquil S P ei es ui us p0 v0 x' p' q' v') : AESame S x p q v x' p' q' v' := by
  obtain ⟨hD, hsum, hprod⟩ := unitroot_roots hP hb
  exact munique_of_factor S hP hD hsum hprod hω hρ h h'

/-- Cochrane (2023), pp. 148–149 (existence of the `(x, π)` block), in a probability model:
under the sign restrictions and the passive-money condition, for every admissible shock process
and initial inflation the block has a bounded adapted solution: `f` is the forward solution of
`f_t = λ_u⁻¹ E_t f_{t+1} − (σ/λ_u) u_{i,t}` and `π_{t+1} = λ_s π_t − (κ/β) f_t + ξ_{t+1}`. -/
theorem mexists_block {P : Params} (hP : Standard P) (hpass : Passive P)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us) (p0 : ℝ) :
    ∃ x p, MBlock S P ei es ui x p ∧ p 0 = fun _ => p0 := by
  obtain ⟨-, hU, hl1, hl2, hsum, hprod⟩ := roots_passive hP hpass
  have hsh' := hsh
  obtain ⟨hea, hesa, hua, -, heb, hesb, hub, -, -, -, -, -⟩ := hsh'
  have hU0 : lamU P ≠ 0 := by linarith
  have hinv : |(lamU P)⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < lamU P)]
    exact inv_lt_one_of_one_lt₀ hU
  obtain ⟨⟨hf, hfa, hfb⟩, -⟩ := S.existsUnique_forward hinv
    (u := fun t => (-(P.sigma / lamU P)) • ui t) (fun t => (hua t).const_smul _)
    (mbdd_smul S _ hub)
  obtain ⟨f, hfd⟩ : ∃ f, f = S.forwardSol (lamU P)⁻¹ (fun t => (-(P.sigma / lamU P)) • ui t) :=
    ⟨_, rfl⟩
  rw [← hfd] at hf hfa hfb
  have hxia := xi_adaptedM S (P := P) hea hesa
  have hxib := xi_bddM S (P := P) heb hesb
  obtain ⟨M, hM⟩ := mbdd_add S (mbdd_smul S (-(P.kappa / P.beta)) hfb) (mbdd_shift S hxib)
  have hpa := backRec_adaptedM S (φ := lamS P)
    (g := fun t => (-(P.kappa / P.beta)) • f t + xi P ei es (t + 1))
    (fun t => (((hfa t).mono (S.𝓕.mono (Nat.le_succ t))).const_smul _).add (hxia (t + 1))) p0
  have hpb := backRec_bddM S (φ := lamS P)
    (g := fun t => (-(P.kappa / P.beta)) • f t + xi P ei es (t + 1)) (abs_lt.mpr ⟨hl1, hl2⟩)
    hM p0
  refine ⟨_, _, mblock_of S hP hU0 hsum hprod hsh hf hfa hfb hpa hpb
    (fun t => Eventually.of_forall fun ω => ?_), rfl⟩
  simp only [backRec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), (5.71)–(5.73), p. 149 (completing an equilibrium from the block), in a
probability model: with `|ω| < 1`, `ρ > 0` and `|1 − α| < ρ`, every bounded adapted solution of
the block extends to an equilibrium (`q` the forward solution, `v` the backward recursion). -/
theorem mexists_of_block {P : Params} (hω : |P.omega| < 1) (hρ0 : 0 < P.rho)
    (hα : |1 - P.alpha| < P.rho) {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us)
    {x p : ℕ → Ω → ℝ} (hb : MBlock S P ei es ui x p) {p0 : ℝ}
    (hp0 : p 0 =ᵐ[S.μ] fun _ => p0) (v0 : ℝ) : ∃ q v, MRedEquil S P ei es ui us p0 v0 x p q v := by
  obtain ⟨-, -, hua, husa, -, -, hub, husb, -, -, -, -⟩ := hsh
  obtain ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩ := hb
  obtain ⟨q, hqa, hqb, h72⟩ := mq_exists S hω hxa hpa hua hxb hpb hub
  have hφ : |debtRoot P| < 1 := by
    rw [debtRoot, abs_div, abs_of_pos hρ0, div_lt_one hρ0]
    exact hα
  obtain ⟨M, hM⟩ := mbdd_gV S (P := P) hxb hpb hqb husb
  exact ⟨q, backRec (debtRoot P) (gV P x p q us) v0, ⟨h64, h65, h68,
    fun t => (mdebt_iff S hρ0.ne' t).mpr (Eventually.of_forall fun _ => rfl), h72⟩,
    hxa, hpa, hqa, backRec_adaptedM S (gV_meas S hxa hpa hqa husa) v0, hxb, hpb, hqb,
    backRec_bddM S hφ hM v0, hp0, Eventually.of_forall fun _ => rfl⟩

/-- **Determinacy of the sticky-price fiscal model with policy rules in a probability model**
(Cochrane (2023), §5.5, pp. 148–149: "the unique stationary equilibrium"; A1 §1.11,
pp. 578–579). Under the sign restrictions, the passive-money condition
`κ(θ_iπ − 1) + (1 − β)θ_ix < 0`, `|ω| < 1`, `ρ > 0` and `|1 − α| < ρ`, for every
measure-theoretic expectation system, every admissible shock process and every initial inflation
and debt, the reduced model has a bounded adapted equilibrium, and any two agree a.e. at every
date. (No assumption on `η_i, η_s` is needed, as in `PolicyRules.policyRules_determinate`.) -/
theorem mpolicyRules_determinate {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us) (p0 v0 : ℝ) :
    (∃ x p q v, MRedEquil S P ei es ui us p0 v0 x p q v) ∧
    ∀ x p q v x' p' q' v', MRedEquil S P ei es ui us p0 v0 x p q v →
      MRedEquil S P ei es ui us p0 v0 x' p' q' v' → AESame S x p q v x' p' q' v' := by
  obtain ⟨x, p, hb, hp0⟩ := mexists_block S hP hpass hsh p0
  obtain ⟨q, v, h⟩ := mexists_of_block S hω hρ0 hα hsh hb (EventuallyEq.of_eq hp0) v0
  exact ⟨⟨x, p, q, v, h⟩, fun _ _ _ _ _ _ _ _ h1 h2 =>
    mpolicyRules_unique S hP hpass hω hρ0.ne' h1 h2⟩

/-- Cochrane (2023), §5.5, p. 148, at model level in a probability model: under the conditions of
`mpolicyRules_determinate` the model is determinate. -/
theorem mmodelDeterminate_of {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho) :
    MModelDeterminate S P := fun _ _ _ _ hsh p0 v0 =>
  mpolicyRules_determinate S hP hpass hω hρ0 hα hsh p0 v0

/-! ### Closed forms with AR(1) disturbances -/

/-- Cochrane (2023), (5.61)–(5.62), p. 147 (tool): `E_t u_{t+1} = η u_t` a.e. for an AR(1)
disturbance driven by unpredictable shocks. -/
theorem E_ar1M {u e : ℕ → Ω → ℝ} {η : ℝ} (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hea : StronglyAdapted S.𝓕 e) (heb : S.BddProc e) (he : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (hl : ∀ t, u (t + 1) = η • u t + e (t + 1)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, S.E t (u (t + 1)) ω = η * u t ω := by
  rw [hl t]
  filter_upwards [E_known_add S ((hua t).const_smul η) ((int_of S hua hub t).smul η)
    (int_of S hea heb (t + 1)), he t] with ω h1 h2
  rw [h1, h2]
  simp

/-- Cochrane (2023), §5.5 (the closed form of the forward part): `f = −σ/(λ_U − η_i) u_i` solves
`f_t = λ_U⁻¹ E_t f_{t+1} − (σ/λ_U) u_{i,t}` a.e. -/
theorem mfwd_cand {P : Params} {lU : ℝ} (hU0 : lU ≠ 0) (hηU : lU - P.etaI ≠ 0)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us) :
    S.Solves lU⁻¹ (fun t => (-(P.sigma / lU)) • ui t)
      (fun t => (-(P.sigma / (lU - P.etaI))) • ui t) := by
  obtain ⟨hea, -, hua, -, heb, -, hub, -, hei, -, hul, -⟩ := hsh
  intro t
  filter_upwards [S.E_smul (-(P.sigma / (lU - P.etaI))) (ui (t + 1)) t,
    E_ar1M S hua hub hea heb hei hul t] with ω e1 e2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1, Pi.smul_apply, smul_eq_mul, e2]
  field_simp
  ring

/-- Cochrane (2023), §5.5 (tool): with `|η_i| < 1` and `λ_U > 1` the bounded solution of the
forward equation is `f = −σ/(λ_U − η_i) u_i` a.e. -/
theorem mfwd_closed {P : Params} {lU : ℝ} (hU : 1 < lU) (hηi : |P.etaI| < 1)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us) {f : ℕ → Ω → ℝ}
    (hf : S.Solves lU⁻¹ (fun t => (-(P.sigma / lU)) • ui t) f)
    (hfm : ∀ t, AEStronglyMeasurable (f t) S.μ) (hfb : S.BddProc f) :
    ∀ t, f t =ᵐ[S.μ] (-(P.sigma / (lU - P.etaI))) • ui t := by
  have hU0 : lU ≠ 0 := by linarith
  have hηU : lU - P.etaI ≠ 0 := by
    have := (abs_lt.mp hηi).2
    linarith
  have hinv : |lU⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith : (0 : ℝ) < lU)]
    exact inv_lt_one_of_one_lt₀ hU
  have hsh' := hsh
  obtain ⟨-, -, hua, -, -, -, hub, -, -, -, -, -⟩ := hsh'
  exact S.forward_unique hinv hf (mfwd_cand S hU0 hηU hsh) hfm
    (fun t => ((hua t).mono (S.𝓕.le t)).aestronglyMeasurable.const_smul _) hfb
    (mbdd_smul S _ hub)

/-- **The closed form in a probability model** (Cochrane (2023), §5.5, pp. 150–158; A1 §1.9):
for any real factorisation with `λ_U > 1` and `|η_i| < 1`, every bounded adapted solution of the
block has `x_t = g(λ_S) π_t − σ/(λ_U − η_i) u_{i,t}` and
`π_{t+1} = λ_S π_t + κσ/(β(λ_U − η_i)) u_{i,t} + ξ_{t+1}` a.e. -/
theorem mclosed {P : Params} (hP : Standard P) {lU lS : ℝ} (hU : 1 < lU)
    (hsum : lU + lS = trB P) (hprod : lU * lS = detB P) (hηi : |P.etaI| < 1)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us) {x p : ℕ → Ω → ℝ}
    (h : MBlock S P ei es ui x p) :
    (∀ t, x t =ᵐ[S.μ] gainOf P lS • p t - (P.sigma / (lU - P.etaI)) • ui t) ∧
    ∀ t, p (t + 1) =ᵐ[S.μ] lS • p t +
      (P.kappa * P.sigma / (P.beta * (lU - P.etaI))) • ui t + xi P ei es (t + 1) := by
  have hU0 : lU ≠ 0 := by linarith
  have hβ := hP.2.2.1.ne'
  have hηU : lU - P.etaI ≠ 0 := by
    have := (abs_lt.mp hηi).2
    linarith
  obtain ⟨hf, hps⟩ := mblock_props S hP hU0 hsum hprod h
  obtain ⟨-, -, -, hxa, hpa, hxb, hpb⟩ := h
  have hfe := mfwd_closed S hU hηi hsh hf
    (fun t => ((fwd_adapted S hxa hpa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fwd_bdd S hxb hpb)
  constructor
  · intro t
    filter_upwards [hfe t] with ω e
    simp only [fwd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    linarith
  · intro t
    filter_upwards [hps t, hfe t] with ω e1 e2
    rw [e1]
    simp only [fwd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e2 ⊢
    rw [e2]
    field_simp
    ring

/-- Cochrane (2023), (5.72)–(5.73), p. 149, in a probability model: if `x = Gπ − d u_i` and
`π_{t+1} = λ_S π_t + c u_{i,t} + ξ_{t+1}` a.e., the bounded bond price is
`q_t = a π_t + b u_{i,t}` a.e. -/
theorem mq_closed {P : Params} {G d c lS : ℝ} (hω : |P.omega| < 1)
    (h1 : 1 - P.omega * lS ≠ 0) (h2 : 1 - P.omega * P.etaI ≠ 0)
    {ei es ui us x p q : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us)
    (hpa : StronglyAdapted S.𝓕 p) (hpb : S.BddProc p) (hqa : StronglyAdapted S.𝓕 q)
    (hqb : S.BddProc q) (hx : ∀ t, x t =ᵐ[S.μ] G • p t - d • ui t)
    (hp1 : ∀ t, p (t + 1) =ᵐ[S.μ] lS • p t + c • ui t + xi P ei es (t + 1))
    (h72 : ∀ t, S.E t (rnNext P q t) =ᵐ[S.μ] iRule P x p ui t) :
    ∀ t, q t =ᵐ[S.μ] qa P G lS • p t + qb P G d c lS • ui t := by
  have hsh' := hsh
  obtain ⟨hea, hesa, hua, -, heb, hesb, hub, -, hei, -, hul, -⟩ := hsh'
  have hxia := xi_adaptedM S (P := P) hea hesa
  have hxib := xi_bddM S (P := P) heb hesb
  have hqa' : qa P G lS * (1 - P.omega * lS) = -(P.thIpi + P.thIx * G) := by
    rw [qa]; field_simp
  have hqb' : qb P G d c lS * (1 - P.omega * P.etaI) =
      P.omega * qa P G lS * c - (1 - P.thIx * d) := by
    rw [qb]; field_simp
  have hEp : ∀ t, S.E t (p (t + 1)) =ᵐ[S.μ] lS • p t + c • ui t := fun t =>
    E_of_pred S (hp1 t) (((hpa t).const_smul lS).add ((hua t).const_smul c))
      (((int_of S hpa hpb t).smul lS).add ((int_of S hua hub t).smul c))
      (int_of S hxia hxib (t + 1)) (E_xiM S hsh t)
  have hs := (meq572_iff S hqa hqb).mp h72
  have hs2 : S.Solves P.omega (fun t => -iRule P x p ui t)
      (fun t => qa P G lS • p t + qb P G d c lS • ui t) := by
    intro t
    filter_upwards [E_comb S (int_of S hpa hpb (t + 1)) (int_of S hua hub (t + 1))
      (qa P G lS) (qb P G d c lS) t, hEp t, E_ar1M S hua hub hea heb hei hul t, hx t]
      with ω e1 e2 e3 e4
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
      smul_eq_mul] at e2 e4 ⊢
    rw [e1, e2, e3, e4]
    linear_combination p t ω * hqa' + ui t ω * hqb'
  exact S.forward_unique hω hs hs2 (fun t => ((hqa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => ((((hpa t).const_smul _).add ((hua t).const_smul _)).mono
      (S.𝓕.le t)).aestronglyMeasurable) hqb (mbdd_add S (mbdd_smul S _ hpb) (mbdd_smul S _ hub))

/-! ### The boundary `|1 − α| ≥ ρ`: the shock-driven part of debt -/

/-- Cochrane (2023), (5.71), p. 149 (the decomposition of `PolicyRules.gV_decomp`, at one
state): in the closed form the forcing `g_t` of `v_{t+1} = φ v_t + g_t` equals
`h_{t+1} − φ h_t + κ_s ε_{s,t+1} + κ_i ε_{i,t+1}`. -/
theorem gV_decomp_pt {P : Params} {C : DCoef} (hρ : P.rho ≠ 0) (h1 : C.lS ≠ C.phi)
    (h2 : P.etaI ≠ C.phi) (h3 : P.etaS ≠ C.phi) {X1 P0 P1 U0 U1 S0 S1 Q0 Q1 Ei Es : ℝ}
    (hx : X1 = C.G * P1 - C.d * U1)
    (hq0 : Q0 = qa P C.G C.lS * P0 + qb P C.G C.d C.c C.lS * U0)
    (hq1 : Q1 = qa P C.G C.lS * P1 + qb P C.G C.d C.c C.lS * U1)
    (hp1 : P1 = C.lS * P0 + C.c * U0 + (-(P.betaS * Es) - P.betaI * Ei))
    (hu1 : U1 = P.etaI * U0 + Ei) (hs1 : S1 = P.etaS * S0 + Es) :
    P.rho⁻¹ * (P.omega * Q1 - Q0 - (1 + P.thSpi) * P1 - P.thSx * X1 - S1) =
      cKp P C * P1 + cKu P C * U1 + cKs P C * S1 -
        C.phi * (cKp P C * P0 + cKu P C * U0 + cKs P C * S0) + kapS P C * Es +
        kapI P C * Ei := by
  have hK1 : cKp P C * (C.lS - C.phi) = cP1 P C * C.lS + cP0 P C := by
    rw [cKp]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr h1)
  have hK2 : cKu P C * (P.etaI - C.phi) =
      (cP1 P C - cKp P C) * C.c + cU1 P C * P.etaI + cU0 P C := by
    rw [cKu]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr h2)
  have hK3 : cKs P C * (P.etaS - C.phi) = cS1 P * P.etaS := by
    rw [cKs]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr h3)
  have hg : P.rho⁻¹ * (P.omega * Q1 - Q0 - (1 + P.thSpi) * P1 - P.thSx * X1 - S1) =
      cP1 P C * P1 + cU1 P C * U1 + cP0 P C * P0 + cU0 P C * U0 + cS1 P * S1 := by
    rw [hq0, hq1, hx]
    simp only [cP1, cU1, cP0, cU0, cS1]
    field_simp
    ring
  rw [hg]
  simp only [kapS, kapI]
  rw [hp1, hu1, hs1]
  linear_combination (-P0) * hK1 - U0 * hK2 - S0 * hK3

/-- Cochrane (2023), (5.71) (tool): the state part of debt is adapted. -/
theorem hProc_adaptedM {P : Params} {C : DCoef} {p ui us : ℕ → Ω → ℝ}
    (hpa : StronglyAdapted S.𝓕 p) (hua : StronglyAdapted S.𝓕 ui)
    (husa : StronglyAdapted S.𝓕 us) : StronglyAdapted S.𝓕 (hProc P C p ui us) := fun t =>
  (((hpa t).const_smul _).add ((hua t).const_smul _)).add ((husa t).const_smul _)

/-- Cochrane (2023), (5.71) (tool): the state part of debt is bounded. -/
theorem hProc_bddM {P : Params} {C : DCoef} {p ui us : ℕ → Ω → ℝ} (hpb : S.BddProc p)
    (hub : S.BddProc ui) (husb : S.BddProc us) : S.BddProc (hProc P C p ui us) := by
  rw [hProc_eq]
  exact mbdd_add S (mbdd_add S (mbdd_smul S _ hpb) (mbdd_smul S _ hub)) (mbdd_smul S _ husb)

/-- Cochrane (2023), (5.71), p. 149, in a probability model: under passive money, `|ω|, |η_i|,
|η_s| < 1`, `ρ > 0` and `|1 − α| ≥ ρ`, for a bounded adapted solution of the block with a bond
price satisfying (5.72), the debt forcing is
`g_t = h_{t+1} − φ h_t + κ_s ε_{s,t+1} + κ_i ε_{i,t+1}` a.e. -/
theorem mgV_decomp {P : Params} (hP : Standard P) (hpass : Passive P) (hω : |P.omega| < 1)
    (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1) (hφ : 1 ≤ |debtRoot P|)
    {ei es ui us x p q : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us)
    (hb : MBlock S P ei es ui x p) (hqa : StronglyAdapted S.𝓕 q) (hqb : S.BddProc q)
    (h72 : ∀ t, S.E t (rnNext P q t) =ᵐ[S.μ] iRule P x p ui t) (t : ℕ) :
    gV P x p q us t =ᵐ[S.μ] hProc P (alphaCoef P) p ui us (t + 1) -
      debtRoot P • hProc P (alphaCoef P) p ui us t + kapS P (alphaCoef P) • es (t + 1) +
      kapI P (alphaCoef P) • ei (t + 1) := by
  obtain ⟨-, hU, hl1, hl2, hsum, hprod⟩ := roots_passive hP hpass
  have hsh' := hsh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hul, husl⟩ := hsh'
  have hne1 : (alphaCoef P).lS ≠ (alphaCoef P).phi := by
    intro h
    change lamS P = debtRoot P at h
    have : |lamS P| < 1 := abs_lt.mpr ⟨hl1, hl2⟩
    rw [h] at this
    linarith
  have hne2 : P.etaI ≠ (alphaCoef P).phi := by
    intro h
    change P.etaI = debtRoot P at h
    rw [h] at hηi
    linarith
  have hne3 : P.etaS ≠ (alphaCoef P).phi := by
    intro h
    change P.etaS = debtRoot P at h
    rw [h] at hηs
    linarith
  have h1 : 1 - P.omega * lamS P ≠ 0 := by
    have : |P.omega * lamS P| < 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg P.omega, abs_lt.mpr ⟨hl1, hl2⟩, abs_nonneg (lamS P)]
    have := (abs_lt.mp this).2
    linarith
  have h2 : 1 - P.omega * P.etaI ≠ 0 := by
    have : |P.omega * P.etaI| < 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg P.omega, abs_nonneg P.etaI]
    have := (abs_lt.mp this).2
    linarith
  obtain ⟨hx, hp1⟩ := mclosed S hP hU hsum hprod hηi hsh hb
  have hb' := hb
  obtain ⟨-, -, -, -, hpa, -, hpb⟩ := hb'
  have hq := mq_closed S hω h1 h2 hsh hpa hpb hqa hqb hx hp1 h72
  filter_upwards [hx (t + 1), hq t, hq (t + 1), hp1 t] with ω e1 e2 e3 e4
  have e5 := congrFun (hul t) ω
  have e6 := congrFun (husl t) ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    xi_succ] at e1 e2 e3 e4 e5 e6
  simp only [gV, rnNext, hProc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact gV_decomp_pt (C := alphaCoef P) hρ0.ne' hne1 hne2 hne3 e1 e2 e3 e4 e5 e6

/-- **Existence at any `α` with `|1 − α| ≥ ρ`, in a probability model** (Cochrane (2023), (5.71),
p. 149; the boundary case of `α ∈ (1 − ρ, 1 + ρ)`): under the sign restrictions, passive money,
`|ω|, |η_i|, |η_s| < 1` and `ρ > 0`, a bounded equilibrium exists iff the shock-driven recursion
`W_{t+1} = φ W_t + κ_s ε_{s,t+1} + κ_i ε_{i,t+1}`, `W_0 = v_0 − h_0`, `φ = (1 − α)/ρ`, has a
bounded adapted solution (a.e.). The value of debt is `v = h + W`. -/
theorem malpha_exists_iff {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1)
    (hφ : 1 ≤ |debtRoot P|) {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us)
    (p0 v0 : ℝ) :
    (∃ x p q v, MRedEquil S P ei es ui us p0 v0 x p q v) ↔
      ∃ W : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 W ∧ S.BddProc W ∧
        W 0 =ᵐ[S.μ] (fun _ => v0) - (cKp P (alphaCoef P) • (fun _ => p0) +
          cKu P (alphaCoef P) • ui 0 + cKs P (alphaCoef P) • us 0) ∧
        ∀ t, W (t + 1) =ᵐ[S.μ] debtRoot P • W t + kapS P (alphaCoef P) • es (t + 1) +
          kapI P (alphaCoef P) • ei (t + 1) := by
  have hsh' := hsh
  obtain ⟨-, -, hua, husa, -, -, hub, husb, -, -, -, -⟩ := hsh'
  constructor
  · rintro ⟨x, p, q, v, ⟨⟨h64, h65, h68, h71, h72⟩, hxa, hpa, hqa, hva, hxb, hpb, hqb, hvb,
      hp0, hv0⟩⟩
    have hdec := mgV_decomp S hP hpass hω hρ0 hηi hηs hφ hsh
      ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩ hqa hqb h72
    refine ⟨fun t => v t - hProc P (alphaCoef P) p ui us t,
      fun t => (hva t).sub (hProc_adaptedM S hpa hua husa t),
      mbdd_sub S hvb (hProc_bddM S hpb hub husb), ?_, fun t => ?_⟩
    · filter_upwards [hv0, hp0] with ω e1 e2
      simp only [hProc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e1, e2]
    · filter_upwards [(mdebt_iff S hρ0.ne' t).mp (h71 t), hdec t] with ω e1 e2
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      rw [e1, e2]
      ring
  · rintro ⟨W, hWa, hWb, hW0, hWr⟩
    obtain ⟨x, p, hb, hp0⟩ := mexists_block S hP hpass hsh p0
    have hb' := hb
    obtain ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩ := hb'
    obtain ⟨q, hqa, hqb, h72⟩ := mq_exists S hω hxa hpa hua hxb hpb hub
    have hdec := mgV_decomp S hP hpass hω hρ0 hηi hηs hφ hsh hb hqa hqb h72
    refine ⟨x, p, q, fun t => W t + hProc P (alphaCoef P) p ui us t, ⟨h64, h65, h68,
      fun t => (mdebt_iff S hρ0.ne' (x := x) (p := p) (q := q)
        (v := fun t => W t + hProc P (alphaCoef P) p ui us t) (us := us) t).mpr ?_, h72⟩,
      hxa, hpa, hqa, fun t => (hWa t).add (hProc_adaptedM S hpa hua husa t), hxb, hpb, hqb,
      mbdd_add S hWb (hProc_bddM S hpb hub husb), EventuallyEq.of_eq hp0, ?_⟩
    · filter_upwards [hWr t, hdec t] with ω e1 e2
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      rw [e1, e2]
      ring
    · filter_upwards [hW0] with ω e1
      simp only [hProc, hp0, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [e1]
      ring

/-- **The unit-root case, existence, in a probability model** (Cochrane (2023), A1 §1.9,
pp. 574–576, E20): on the boundary `κ(θ_iπ − 1) + (1 − β)θ_ix = 0`, with `|η_i| < 1`,
`|ω| < 1`, `ρ > 0` and `|1 − α| < ρ`, a bounded equilibrium exists iff the inflation martingale
`W = π + k u_i` (`k = urK`), with `W_{t+1} = W_t − β_s ε_{s,t+1} + (k − β_i) ε_{i,t+1}` from
`W_0 = π_0 + k u_{i,0}`, has a bounded adapted solution (a.e.). -/
theorem munitroot_exists_iff {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho)
    {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us) (p0 v0 : ℝ) :
    (∃ x p q v, MRedEquil S P ei es ui us p0 v0 x p q v) ↔
      ∃ W : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 W ∧ S.BddProc W ∧
        W 0 =ᵐ[S.μ] (fun _ => p0) + urK P • ui 0 ∧
        ∀ t, W (t + 1) =ᵐ[S.μ] W t + (-P.betaS) • es (t + 1) +
          (urK P - P.betaI) • ei (t + 1) := by
  obtain ⟨hD, hsum, hprod⟩ := unitroot_roots hP hb
  have hβ := hP.2.2.1.ne'
  have hsh' := hsh
  obtain ⟨-, -, hua, -, -, -, hub, -, -, -, hul, -⟩ := hsh'
  have hη1 : 1 - P.etaI ≠ 0 := by
    have := (abs_lt.mp hηi).2; linarith
  have hηD : detB P - P.etaI ≠ 0 := by
    have := (abs_lt.mp hηi).2; linarith
  have hD0 : detB P ≠ 0 := by linarith
  have hk : urK P * (1 - P.etaI) = P.kappa * P.sigma / (P.beta * (detB P - P.etaI)) := by
    rw [urK]; field_simp
  have hk' : urK P * (1 - P.etaI) = P.kappa / P.beta * (P.sigma / (detB P - P.etaI)) := by
    rw [hk]; field_simp
  constructor
  · rintro ⟨x, p, q, v, ⟨⟨h64, h65, h68, -, -⟩, hxa, hpa, -, -, hxb, hpb, -, -, hp0, -⟩⟩
    obtain ⟨-, hp1⟩ := mclosed S hP hD hsum hprod hηi hsh ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩
    refine ⟨fun t => p t + urK P • ui t, fun t => (hpa t).add ((hua t).const_smul _),
      mbdd_add S hpb (mbdd_smul S _ hub), ?_, fun t => ?_⟩
    · filter_upwards [hp0] with ω e
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [e]
    · filter_upwards [hp1 t] with ω e
      have eu := congrFun (hul t) ω
      simp only [xi_succ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
        smul_eq_mul] at e eu ⊢
      rw [e, eu]
      linear_combination (-(ui t ω)) * hk
  · rintro ⟨W, hWa, hWb, hW0, hWr⟩
    have hf := mfwd_cand S hD0 hηD hsh
    have hpa : StronglyAdapted S.𝓕 (fun t => W t - urK P • ui t) := fun t =>
      (hWa t).sub ((hua t).const_smul _)
    have hpb : S.BddProc (fun t => W t - urK P • ui t) := mbdd_sub S hWb (mbdd_smul S _ hub)
    have hblk := mblock_of S hP hD0 hsum hprod hsh hf (fun t => (hua t).const_smul _)
      (mbdd_smul S _ hub) hpa hpb (fun t => by
        filter_upwards [hWr t] with ω e
        have eu := congrFun (hul t) ω
        simp only [xi_succ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply,
          smul_eq_mul] at e eu ⊢
        rw [e, eu]
        linear_combination (ui t ω) * hk')
    obtain ⟨q, v, h⟩ := mexists_of_block S hω hρ0 hα hsh hblk (p0 := p0) (by
      filter_upwards [hW0] with ω e
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      rw [e]
      ring) v0
    exact ⟨_, _, q, v, h⟩

/-- Cochrane (2023), §5.4, pp. 137–138 and §5.5 (the surplus response to debt must satisfy
`α ∈ (1 − ρ, 1 + ρ)`), in a probability model: if `|1 − α| > ρ`, then (with the other conditions
of `mpolicyRules_determinate`) the model with zero shocks, `π_0 = 0` and `v_0 = 1` has no
bounded equilibrium — the block is a.e. zero and debt follows `v_t = φᵗ` a.e. -/
theorem mnonexist_of_alpha {P : Params} (hP : Standard P) (hpass : Passive P)
    (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : P.rho < |1 - P.alpha|)
    (x p q v : ℕ → Ω → ℝ) : ¬ MRedEquil S P 0 0 0 0 0 1 x p q v := by
  rintro ⟨⟨h64, h65, h68, h71, h72⟩, hxa, hpa, hqa, -, hxb, hpb, hqb, hvb, hp0, hv0⟩
  obtain ⟨-, hU, -, -, hsum, hprod⟩ := roots_passive hP hpass
  have hz : MBlock S P 0 0 0 (0 : ℕ → Ω → ℝ) 0 := by
    refine ⟨fun t => Eventually.of_forall fun ω => ?_, fun t => Eventually.of_forall fun ω => ?_,
      fun t => Eventually.of_forall fun ω => ?_, fun _ => stronglyMeasurable_zero,
      fun _ => stronglyMeasurable_zero, mbdd_zero S, mbdd_zero S⟩
    · simp [iRule, S.E_zero]
    · simp [S.E_zero]
    · simp [MeasExpectationSystem.innov, S.E_zero]
  have hblk := mblock_unique S hP hU hsum hprod ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩ hz hp0
    (Eventually.of_forall fun _ => rfl)
  have hs := (meq572_iff S hqa hqb).mp h72
  have hs0 : S.Solves P.omega (fun t => -iRule P x p 0 t) 0 := by
    intro t
    filter_upwards [(hblk t).1, (hblk t).2] with ω e1 e2
    simp only [iRule, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul,
      S.E_zero]
    rw [e1, e2]
    simp
  have hq0 := S.forward_unique hω hs hs0 (fun t => ((hqa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun _ => aestronglyMeasurable_zero) hqb (mbdd_zero S)
  set φ := debtRoot P with hφdef
  have hφ : 1 < |φ| := by
    rw [hφdef, debtRoot, abs_div, abs_of_pos hρ0, one_lt_div hρ0]
    exact hα
  have hvt : ∀ t, v t =ᵐ[S.μ] fun _ => φ ^ t := by
    intro t
    induction t with
    | zero => simpa using hv0
    | succ t ih =>
      filter_upwards [(mdebt_iff S hρ0.ne' t).mp (h71 t), ih, (hblk (t + 1)).1, (hblk (t + 1)).2,
        hq0 t, hq0 (t + 1)] with ω e e1 e2 e3 e4 e5
      rw [e]
      simp only [gV, rnNext, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul]
      rw [e1, e2, e3, e4, e5, ← hφdef]
      simp only [Pi.zero_apply]
      ring
  obtain ⟨M, hM⟩ := hvb
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hφ).eventually_gt_atTop M).exists
  obtain ⟨ω, h1, h2⟩ := ((hM t).and (hvt t)).exists
  rw [h2, abs_pow] at h1
  linarith

end Cochrane.StickyPriceFiscal.PolicyRulesMeasure
