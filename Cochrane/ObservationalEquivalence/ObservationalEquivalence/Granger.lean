/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.SurplusRegression
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fin.VecNotation

/-!
# Granger causality, news, and information sets

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, p. 501 (footnote 1)
and pp. 501–502, and Online Appendix Chapter 2, introduction (p. 593) and §2.1.7, eqs.
(2.22)–(2.23), pp. 602–604.

## Granger causality in a VAR

For a VAR `z_{t+1} = A z_t + ε_{t+1}` with martingale-difference shocks (any
`ExpectationSystem`), `var_forecast` gives `E_t z_{t+h} = A^h z_t` and `var_innov` the impulse
response `ΔE_{t+1} z_{t+1+j} = A^j ε_{t+1}` (`ΔE_{t+1} = E_{t+1} − E_t`, `innov`); with
orthonormal shocks `cov_innov_shock` shows that the covariance of the revision
`ΔE_{t+1} y_{t+1+j}` with the `x`-shock is `(A^j)_{yx}`. Hence the book's footnote definition ("x
Granger-causes y if surprises to x forecast subsequent surprises to y") is the statement that
some `(A^j)_{yx} ≠ 0`, `j ≥ 1`: `IRFNonCausal`. The standard one-step definition is
`A_{yx} = 0` (`OneStepNonCausal`: the one-step forecast of `y` does not load on `x`).

* `irf_nonCausal_iff_forecast`: IRF non-causality ⇔ no `h`-step forecast of `y` loads on `x`.
* `irf_imp_oneStep`: IRF non-causality implies one-step non-causality.
* `bivariate_oneStep_iff_irf`: in a bivariate VAR the two definitions coincide (the footnote's
  "equivalently").
* `trivariate_counterexample` (survey **E17**): with three variables `x → w → y`
  (`A = [[0,0,0],[1,0,0],[0,1,0]]`), `x` does not Granger-cause `y` at one step but the impulse
  response of `y` to `x` shocks is nonzero at horizon 2; so "x does not Granger-cause y iff the
  IRF is zero" is false for the standard definition with three or more variables.

## News (pp. 501–502, Online Appendix p. 593)

In the news model `s_{t+1} = ε_t` (the surplus is learned one period ahead; exogenous, iid
shocks) the valuation equation gives `v_t = ε_t` (`news_value`): the value of debt forecasts the
surplus perfectly (`news_surplus_eq_value`, regression coefficient one, `news_regCoeff`), while
past surpluses do not forecast it at all (`news_past_surplus_uncorrelated`). In VAR form
(`news_isVAR`) debt Granger-causes surpluses and surpluses do not Granger-cause debt
(`news_debt_causes_surplus`, `news_surplus_not_cause_debt`), although surpluses are exogenous.

## Information sets ((2.22)–(2.23))

`Coarser 𝕀 𝔼`: our information is coarser than the agents' (`𝕀_t(𝔼_t x) = 𝕀_t x`, the tower
property across information sets). `pv_ours_of_agents`: (2.22) implies
`E(v_t | I_t) = E(PV | I_t)`; `pv_ours_iff`: the present-value relation with our forecasts (2.23)
holds iff `v_t` is in our information set; `pv_ours_of_same`: it holds when `I = Ω`;
`pv_ours_fails`: a concrete two-state example where agents know more and (2.23) fails.
-/

namespace Cochrane.ObservationalEquivalence.Granger

open Finset Cochrane.ObservationalEquivalence.MACovariance
open Cochrane.ObservationalEquivalence.SurplusRegression
open scoped Matrix
open Cochrane.ObservationalEquivalence.ExpectationTools (innov innov_apply fullInfo pvExPost)

variable {Ω κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### Innovations and VARs -/

/-- Cochrane (2023), p. 501, footnote 1: the VAR `z_{t+1} = A z_t + ε_{t+1}` of the variables
`z_t` (restated from the Cochrane `DebtDeficitsInflation` project). -/
def IsVAR (A : Matrix κ κ ℝ) (z ε : ℕ → κ → Ω → ℝ) : Prop :=
  ∀ t i, z (t + 1) i = ∑ j, A i j • z t j + ε (t + 1) i

/-- Cochrane (2023), p. 501, footnote 1: the VAR shocks are unforecastable, `E_t ε_{t+1} = 0`. -/
def ShockMDS (𝔼 : ExpectationSystem Ω) (ε : ℕ → κ → Ω → ℝ) : Prop :=
  ∀ t i, 𝔼.E t (ε (t + 1) i) = 0

/-- Cochrane (2023), p. 501, footnote 1: VAR forecasts, `E_t z_{t+k} = A^k z_t` (restated from the
Cochrane `DebtDeficitsInflation` project). -/
theorem var_forecast (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (t k : ℕ) (i : κ) : 𝔼.E t (z (t + k) i) = ∑ j, (A ^ k) i j • z t j := by
  induction k generalizing i with
  | zero =>
    simp [hz t i, Matrix.one_apply, ite_smul]
  | succ k ih =>
    have e : z (t + (k + 1)) i = ∑ j, A i j • z (t + k) j + ε (t + k + 1) i := hvar (t + k) i
    have hε : 𝔼.E t (ε (t + k + 1) i) = 0 := by
      rw [← 𝔼.tower (Nat.le_add_right t k), hmds (t + k) i, map_zero]
    rw [e, map_add, map_sum, hε, add_zero]
    simp only [map_smul, ih]
    rw [pow_succ']
    simp only [Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm

/-- Cochrane (2023), p. 501, footnote 1: the impulse response,
`ΔE_{t+1} z_{t+1+k} = A^k ε_{t+1}` (restated from the Cochrane `DebtDeficitsInflation`
project). -/
theorem var_innov (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    (t k : ℕ) (i : κ) : innov 𝔼 t (z (t + 1 + k) i) = ∑ j, (A ^ k) i j • ε (t + 1) j := by
  have h1 := var_forecast 𝔼 hvar hmds hz (t + 1) k i
  have h2 := var_forecast 𝔼 hvar hmds hz t (k + 1) i
  rw [show t + (k + 1) = t + 1 + k by omega] at h2
  rw [innov_apply, h1, h2]
  simp only [hvar t, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  rw [pow_succ]
  simp only [Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm (f := fun x y => ((A ^ k) i x * A x y) • z t y)]
  abel

/-- Cochrane (2023), p. 501, footnote 1 ("surprises to `x` forecast surprises to subsequent
`y`"): with orthonormal date-`t+1` shocks, the covariance of the revision
`ΔE_{t+1} y_{t+1+k}` with the `x`-shock `ε_{x,t+1}` is the impulse response `(A^k)_{yx}`. -/
theorem cov_innov_shock (𝔼 : ExpectationSystem Ω) {A : Matrix κ κ ℝ} {z ε : ℕ → κ → Ω → ℝ}
    (hvar : IsVAR A z ε) (hmds : ShockMDS 𝔼 ε) (hz : ∀ t i, 𝔼.E t (z t i) = z t i)
    {B : LinearMap.BilinForm ℝ (Ω → ℝ)} (t : ℕ)
    (hB : ∀ i j, B (ε (t + 1) i) (ε (t + 1) j) = if i = j then 1 else 0) (k : ℕ) (x y : κ) :
    B (innov 𝔼 t (z (t + 1 + k) y)) (ε (t + 1) x) = (A ^ k) y x := by
  rw [var_innov 𝔼 hvar hmds hz t k y]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hB, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-! ### Definitions of Granger non-causality -/

/-- Cochrane (2023), p. 501, footnote 1 (standard one-step definition): `x` does not
Granger-cause `y` when the one-step forecast of `y` does not load on `x`, `A_{yx} = 0`. -/
def OneStepNonCausal (A : Matrix κ κ ℝ) (x y : κ) : Prop := A y x = 0

/-- Cochrane (2023), p. 501, footnote 1 (the book's definition via surprises; the
"impulse-response" form): `x` does not Granger-cause `y` when the response of `y` to `x` shocks
is zero at every horizon `h ≥ 1`. -/
def IRFNonCausal (A : Matrix κ κ ℝ) (x y : κ) : Prop := ∀ h, 1 ≤ h → (A ^ h) y x = 0

/-- Cochrane (2023), p. 501, footnote 1: IRF non-causality is the same as "no `h`-step forecast
of `y` loads on `x`", `h ≥ 1` (the multi-horizon definition), since `E_t y_{t+h} = (A^h z_t)_y`
(`var_forecast`). -/
theorem irf_nonCausal_iff_forecast (A : Matrix κ κ ℝ) (x y : κ) :
    IRFNonCausal A x y ↔ ∀ h, 1 ≤ h → ∀ zz : κ → ℝ, (A ^ h *ᵥ zz) y = (A ^ h *ᵥ
      Function.update zz x 0) y := by
  constructor
  · intro hA h hh zz
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = x
    · subst hj; rw [hA h hh]; simp
    · rw [Function.update_of_ne hj]
  · intro hF h hh
    have e : Function.update (Pi.single (M := fun _ => ℝ) x 1) x 0 = 0 := by
      funext j
      by_cases hj : j = x
      · subst hj; simp
      · simp [hj]
    have := hF h hh (Pi.single (M := fun _ => ℝ) x 1)
    rw [e] at this
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- Cochrane (2023), p. 501, footnote 1: IRF non-causality implies one-step non-causality. -/
theorem irf_imp_oneStep {A : Matrix κ κ ℝ} {x y : κ} (h : IRFNonCausal A x y) :
    OneStepNonCausal A x y := by
  have := h 1 le_rfl
  simpa [OneStepNonCausal] using this

/-- Cochrane (2023), p. 501, footnote 1 ("Equivalently, `x_t` does not Granger-cause `y_t` if the
impulse-response function of `y` to `x` shocks is zero"): true in a bivariate VAR — the two
definitions coincide. -/
theorem bivariate_oneStep_iff_irf (A : Matrix (Fin 2) (Fin 2) ℝ) {x y : Fin 2} (hxy : x ≠ y) :
    OneStepNonCausal A x y ↔ IRFNonCausal A x y := by
  refine ⟨fun h => ?_, irf_imp_oneStep⟩
  unfold OneStepNonCausal at h
  have hpow : ∀ n, (A ^ n) y x = 0 := by
    intro n
    induction n with
    | zero => simp [Ne.symm hxy]
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases x <;> fin_cases y
      · exact absurd rfl hxy
      · simp_all
      · simp_all
      · exact absurd rfl hxy
  exact fun n _ => hpow n

/-- Cochrane (2023), p. 501, footnote 1 (survey E17): the three-variable chain `x → w → y`. -/
def chainA : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 1, 0, 0; 0, 1, 0]

/-- Cochrane (2023), p. 501, footnote 1 (survey E17): in the VAR with `A = chainA`
(`x = 0`, `w = 1`, `y = 2`), `x` does not Granger-cause `y` in the one-step sense
(`A_{yx} = 0`), yet the impulse response of `y` to an `x` shock is `(A²)_{yx} = 1 ≠ 0`. So the
footnote's "equivalently" fails for the standard definition with three or more variables. -/
theorem trivariate_counterexample :
    OneStepNonCausal chainA 0 2 ∧ (chainA ^ 2) 2 0 = 1 ∧ ¬ IRFNonCausal chainA 0 2 := by
  have h2 : (chainA ^ 2) 2 0 = 1 := by
    simp [sq, chainA, Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨by simp [OneStepNonCausal, chainA], h2, fun h => ?_⟩
  have := h 2 (by norm_num)
  rw [h2] at this
  exact one_ne_zero this

/-! ### The news model: debt Granger-causes an exogenous surplus -/

/-- Cochrane (2023), pp. 501–502 ("If people learn from reading the news that surpluses will be
poor…"): the news surplus `s_t = ε_{t−1}`, as the moving average with `a = (0, 1)`. -/
def newsCoeff (k : ℕ) : ℝ := if k = 1 then 1 else 0

/-- Cochrane (2023), pp. 501–502: the news surplus is `s_t = ε_{t−1}`. -/
theorem news_surplus (ε : ℤ → Ω → ℝ) (t : ℕ) :
    surplus newsCoeff 1 ε t = ε ((t : ℤ) - 1) := by
  simp [surplus, maProc, newsCoeff]

/-- Cochrane (2023), pp. 501–502: the news surplus coefficients vanish beyond lag one. -/
theorem newsCoeff_support : ∀ k, 1 < k → newsCoeff k = 0 := by
  intro k hk; simp [newsCoeff]; omega

/-- Cochrane (2023), pp. 501–502 and Online Appendix p. 593: in the news model the valuation
equation gives `v_t = E_t ∑ ρ^j s_{t+1+j} = ε_t` — debt reveals the news. -/
theorem news_value {𝔼 : ExpectationSystem Ω} {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    valueOfDebt 𝔼 ρ (surplus newsCoeff 1 ε) t = ε (t : ℤ) := by
  rw [value_eq_maProc hε hM hρ newsCoeff_support]
  simp [maProc, vCoeff, newsCoeff, Finset.sum_range_succ]

/-- Cochrane (2023), pp. 501–502: in the news model the value of debt forecasts next period's
surplus exactly, `s_{t+1} = v_t`. -/
theorem news_surplus_eq_value {𝔼 : ExpectationSystem Ω} {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε)
    {M : ℝ} (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    surplus newsCoeff 1 ε (t + 1) = valueOfDebt 𝔼 ρ (surplus newsCoeff 1 ε) t := by
  rw [news_value hε hM hρ, news_surplus]
  push_cast; ring_nf

/-- Cochrane (2023), pp. 501–502: in the news model the regression coefficient of `s_{t+1}` on
`v_t` is one (with unit-variance white-noise shocks). -/
theorem news_regCoeff {𝔼 : ExpectationSystem Ω} {B : LinearMap.BilinForm ℝ (Ω → ℝ)}
    {ε : ℤ → Ω → ℝ} (hw : WhiteNoise B ε) (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    regCoeff B (surplus newsCoeff 1 ε (t + 1)) (valueOfDebt 𝔼 ρ (surplus newsCoeff 1 ε) t) =
      1 := by
  rw [news_surplus_eq_value hε hM hρ, news_value hε hM hρ, regCoeff, hw]
  simp

/-- Cochrane (2023), pp. 501–502: in the news model past and current surpluses do not forecast
next period's surplus: `Cov(s_{t+1}, s_{t−k}) = 0` for every `k ≥ 0` (the surplus is serially
uncorrelated, hence exogenous white noise to an econometrician who sees only surpluses). -/
theorem news_past_surplus_uncorrelated {B : LinearMap.BilinForm ℝ (Ω → ℝ)} {ε : ℤ → Ω → ℝ}
    (hw : WhiteNoise B ε) (t k : ℕ) (hk : k ≤ t) :
    B (surplus newsCoeff 1 ε (t + 1)) (surplus newsCoeff 1 ε (t - k)) = 0 := by
  rw [news_surplus, news_surplus, hw]
  have : ¬ (((t + 1 : ℕ) : ℤ) - 1 = ((t - k : ℕ) : ℤ) - 1) := by omega
  simp only [this, ↓reduceIte]

/-- Cochrane (2023), pp. 501–502 (the news model is not vacuous): in the truncation model of
`SurplusRegression` (bounded white-noise shocks), `s_{t+1} = v_t` and the regression coefficient
of `s_{t+1}` on `v_t` is one. -/
theorem truncModel_news {ρ : ℝ} (hρ : |ρ| < 1) (t : ℕ) :
    surplus newsCoeff 1 clampShock (t + 1) =
        valueOfDebt truncSystem ρ (surplus newsCoeff 1 clampShock) t ∧
      regCoeff truncCov (surplus newsCoeff 1 clampShock (t + 1))
        (valueOfDebt truncSystem ρ (surplus newsCoeff 1 clampShock) t) = 1 :=
  ⟨news_surplus_eq_value clampShock_info clampShock_bounded hρ t,
    news_regCoeff clampShock_whiteNoise clampShock_info clampShock_bounded hρ t⟩

/-- Cochrane (2023), pp. 501–502: the news model as a VAR in `z = (s, v)`:
`s_{t+1} = v_t`, `v_{t+1} = ε_{t+1}`, i.e. `A = [[0, 1], [0, 0]]`. -/
def newsA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]

/-- Cochrane (2023), pp. 501–502: the VAR state of the news model, `z_t = (s_t, v_t)`. -/
noncomputable def newsZ (𝔼 : ExpectationSystem Ω) (ρ : ℝ) (ε : ℤ → Ω → ℝ) (t : ℕ) :
    Fin 2 → Ω → ℝ :=
  ![surplus newsCoeff 1 ε t, valueOfDebt 𝔼 ρ (surplus newsCoeff 1 ε) t]

/-- Cochrane (2023), pp. 501–502: the VAR shocks of the news model, `(0, ε_t)`. -/
def newsShock (ε : ℤ → Ω → ℝ) (t : ℕ) : Fin 2 → Ω → ℝ := ![0, ε (t : ℤ)]

/-- Cochrane (2023), pp. 501–502: the news model is the VAR `z_{t+1} = A z_t + (0, ε_{t+1})` with
`A = [[0, 1], [0, 0]]`. -/
theorem news_isVAR {𝔼 : ExpectationSystem Ω} {ε : ℤ → Ω → ℝ} (hε : ShockInfo 𝔼 ε) {M : ℝ}
    (hM : ∀ k ω, |ε k ω| ≤ M) {ρ : ℝ} (hρ : |ρ| < 1) :
    IsVAR newsA (newsZ 𝔼 ρ ε) (newsShock ε) := by
  intro t i
  fin_cases i
  · simp [newsZ, newsShock, newsA, Fin.sum_univ_two, news_surplus_eq_value hε hM hρ]
  · simp [newsZ, newsShock, newsA, Fin.sum_univ_two, news_value hε hM hρ]

/-- Cochrane (2023), pp. 501–502 and Online Appendix p. 593 ("debt [should] Granger-cause
surpluses"): in the news model debt Granger-causes surpluses in every sense — the one-step
forecast of `s` loads on `v` (`A_{sv} = 1`). -/
theorem news_debt_causes_surplus : ¬ OneStepNonCausal newsA 1 0 ∧ ¬ IRFNonCausal newsA 1 0 := by
  refine ⟨by simp [OneStepNonCausal, newsA], fun h => ?_⟩
  have := irf_imp_oneStep h
  simp [OneStepNonCausal, newsA] at this

/-- Cochrane (2023), pp. 501–502: in the news model surpluses do not Granger-cause debt at any
horizon, although debt is determined by the valuation equation and surpluses are exogenous. -/
theorem news_surplus_not_cause_debt : IRFNonCausal newsA 0 1 :=
  (bivariate_oneStep_iff_irf newsA (by decide)).mp (by simp [OneStepNonCausal, newsA])

/-! ### Information sets: (2.22) and (2.23) -/

/-- Cochrane (2023), Online Appendix p. 602 (`I_t ⊂ Ω_t`): our information `𝕀` is coarser than
the agents' information `𝔼` — the tower property across information sets. -/
def Coarser (𝕀 𝔼 : ExpectationSystem Ω) : Prop := ∀ t x, 𝕀.E t (𝔼.E t x) = 𝕀.E t x

/-- Cochrane (2023), Online Appendix eqs. (2.22)–(2.23), p. 602: if the value of debt is the
agents' present value (2.22), `v_t = E(PV | Ω_t)`, then with our coarser information
`E(v_t | I_t) = E(PV | I_t)` — "otherwise, we have `E(v_t | I_t)` on the left-hand side". -/
theorem pv_ours_of_agents {𝕀 𝔼 : ExpectationSystem Ω} (hc : Coarser 𝕀 𝔼) {t : ℕ}
    {v pv : Ω → ℝ} (h22 : v = 𝔼.E t pv) : 𝕀.E t v = 𝕀.E t pv := by
  rw [h22, hc]

/-- Cochrane (2023), Online Appendix eqs. (2.22)–(2.23), p. 602: given (2.22), the present-value
relation with our forecasts (2.23), `v_t = E(PV | I_t)`, holds if and only if the value of debt
is in our information set, `E(v_t | I_t) = v_t`. -/
theorem pv_ours_iff {𝕀 𝔼 : ExpectationSystem Ω} (hc : Coarser 𝕀 𝔼) {t : ℕ} {v pv : Ω → ℝ}
    (h22 : v = 𝔼.E t pv) : v = 𝕀.E t pv ↔ 𝕀.E t v = v := by
  rw [← pv_ours_of_agents hc h22]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-- Cochrane (2023), Online Appendix p. 602: if agents use no more information than we do
(`I_t = Ω_t`), (2.22) is (2.23). -/
theorem pv_ours_of_same (𝔼 : ExpectationSystem Ω) {t : ℕ} {v pv : Ω → ℝ}
    (h22 : v = 𝔼.E t pv) : v = 𝔼.E t pv := h22

/-- Cochrane (2023), Online Appendix p. 602 (example): averaging over the fair coin. -/
noncomputable def coinMean : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) where
  toFun x := fun _ => (x true + x false) / 2
  map_add' x y := by funext; simp only [Pi.add_apply]; ring
  map_smul' c x := by funext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Cochrane (2023), Online Appendix p. 602 (example): the econometrician learns the coin only
at date `1`. -/
noncomputable def oursInfo : ExpectationSystem Bool where
  E := fun t => if t = 0 then coinMean else LinearMap.id
  const := fun t c => by
    by_cases ht : t = 0
    · simp only [ht, ↓reduceIte]; funext; simp [coinMean]
    · simp [ht]
  mono := fun t x y h => by
    by_cases ht : t = 0
    · simp only [ht, ↓reduceIte]
      intro ω
      simp only [coinMean, LinearMap.coe_mk, AddHom.coe_mk]
      linarith [h true, h false]
    · simpa [ht] using h
  tower := fun {s t} hst x => by
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · subst hs; subst ht; simp only [↓reduceIte]; funext; simp [coinMean]
      · simp [hs, ht]
    · have ht : t ≠ 0 := by omega
      simp [hs, ht]
  known := fun {s t} hst x => by
    by_cases ht : t = 0
    · have hs : s = 0 := by omega
      subst hs; subst ht; simp only [↓reduceIte]; funext; simp [coinMean]
    · by_cases hs : s = 0
      · simp [hs, ht]
      · simp [hs, ht]

/-- Cochrane (2023), Online Appendix p. 602 (example): our information is coarser than the
agents'. -/
theorem ours_coarser : Coarser oursInfo (fullInfo Bool) := fun _ _ => rfl

/-- Cochrane (2023), Online Appendix p. 602 (example): the surplus `s_1 = ±1` according to the
coin, zero at all other dates. -/
def coinSurplus (t : ℕ) (ω : Bool) : ℝ := if t = 1 then (if ω then 1 else -1) else 0

/-- Cochrane (2023), Online Appendix p. 602 (example): the date-`0` present value of the coin
surplus is `∑_j ρ^j s_{1+j} = s_1`. -/
theorem coinSurplus_pv (ρ : ℝ) (ω : Bool) :
    ∑' j, ρ ^ j * coinSurplus (0 + 1 + j) ω = if ω then 1 else -1 := by
  rw [tsum_eq_single 0 fun j hj => by simp [coinSurplus, hj]]
  simp [coinSurplus]

/-- Cochrane (2023), Online Appendix eqs. (2.22)–(2.23), p. 602: when agents know more than we
do, (2.22) holds but (2.23) fails — the value of debt `v_0 = ±1` is the agents' present value,
while our forecast of the present value is `0`, and `v_0` is not in our information set. -/
theorem pv_ours_fails (ρ : ℝ) :
    valueOfDebt (fullInfo Bool) ρ coinSurplus 0 ≠
      oursInfo.E 0 (fun ω => ∑' j, ρ ^ j * coinSurplus (0 + 1 + j) ω) ∧
    oursInfo.E 0 (valueOfDebt (fullInfo Bool) ρ coinSurplus 0) ≠
      valueOfDebt (fullInfo Bool) ρ coinSurplus 0 := by
  have hv : valueOfDebt (fullInfo Bool) ρ coinSurplus 0 = fun ω => if ω then 1 else -1 := by
    funext ω
    simp only [valueOfDebt, fullInfo, pvExPost, LinearMap.id_apply]
    exact coinSurplus_pv ρ ω
  have hpv : (fun ω => ∑' j, ρ ^ j * coinSurplus (0 + 1 + j) ω) =
      fun ω => if ω then (1 : ℝ) else -1 := funext (coinSurplus_pv ρ)
  have hmean : oursInfo.E 0 (fun ω : Bool => if ω then (1 : ℝ) else -1) = 0 := by
    funext ω; simp [oursInfo, coinMean]
  refine ⟨?_, ?_⟩
  · rw [hv, hpv, hmean]
    intro h
    have := congrFun h true
    simp at this
  · rw [hv, hmean]
    intro h
    have := congrFun h true
    simp at this

end Cochrane.ObservationalEquivalence.Granger
