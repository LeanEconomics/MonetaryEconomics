/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DiscretionCommitment.Expectations
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The loss function and the NKPC with a cost-push shock

Galí (2015), Chapter 5, §5.2 introduction (pp. 127–129) and Appendix 5.1 (pp. 154–156).

## The loss (1) and the weight `ϑ = κ/ε`

* `vartheta_eq_weight_ratio`: the Chapter 4 welfare criterion
  `½ ∑ βᵗ [(σ + (φ+α)/(1−α)) x_t² + (ε/λ) π_t²]` has gap weight relative to inflation
  `(σ + (φ+α)/(1−α))/(ε/λ) = κ/ε = ϑ` (exact).
* `periodLoss_eq_scaled`, `hasSum_welfare_of_loss`, `expected_welfare_eq_scaled_loss`,
  `welfare_le_iff_loss_le`: the welfare loss is exactly `(ε/(2λ))` times
  `∑ βᵗ (π_t² + ϑ x_t²)`, the loss (1), path by path and in conditional expectation, so the
  two criteria rank policies identically.

## The NKPC (2) with a cost-push shock

* `nkpc_iff_costPush`: the Chapter 3 NKPC in `y − y^n` holds iff (2)
  `π_t = β E_t π_{t+1} + κ x_t + u_t` holds with `x = y − y^e`, `u = κ(y^e − y^n)`.
* `costPush_eq_zero_iff`, `zero_outcome_iff`: `π ≡ x ≡ 0` is an equilibrium outcome iff
  `u ≡ 0` iff `y^e = y^n` (the tradeoff of p. 128).

## Appendix 5.1: a small steady-state distortion

* `distortion_iff`: `−U_n/U_c = MPN (1 − Φ)` with `MPN = (1 − α) Y/N` is
  `U_n N = −(1 − Φ)(1 − α) U_c C`.
* `secondOrderUtility_eq_distorted` (**exact completing the square**): the second-order
  polynomial of period utility equals
  `U_c C [Φ x̂ − ½(Γ x̂² + (ε/Θ) var_i p(i))] + t.i.p. + (third-order terms) + U_c C Φ Q`
  with `x̂ = ŷ − ψ_ya a` and an explicit second-order `Q`.
* `small_distortion_polynomial`: along one-parameter families with `Φ = O(s)`, the book's
  approximation is correct to `O(s³)`.
* `period_utility_small_distortion` (**the analytic bridge**): for actual `C³` utility at a
  fixed distorted steady state, period utility equals the book's expression plus
  `U_c C Φ Q(s)` plus `O(s³)`, with `Q = O(s²)`: the neglected term is exactly
  "the product of `Φ` with a second-order term".
* `welfare_small_distortion`: summing with Lemma 2 (restated from the Chapter 4 project), the
  welfare loss is exactly `W = −∑ βᵗ [Φ x̂_t − ½((ε/λ) π_t² + (σ + (φ+α)/(1−α)) x̂_t²)]`;
  `welfareW_efficient`: for `Φ = 0` this is `(ε/(2λ)) ∑ βᵗ (π_t² + ϑ x_t²)`, the loss (1).

The Taylor-expansion machinery and Lemma 2 are restated from the Chapter 4 project
(`MonetaryPolicyDesign/Welfare.lean`).
-/

namespace Gali.DiscretionCommitment.LossAndCostPush

open Asymptotics Filter Topology

/-! ### Parameters (restated from the Chapter 4 project) -/

/-- Galí (2015), p. 111 and App. 5.1, p. 155: the output-gap coefficient of the loss,
`Γ = σ + (φ + α)/(1 − α)` (restated from the Chapter 4 project). -/
noncomputable def gapCoeff (σ φ α : ℝ) : ℝ := σ + (φ + α) / (1 - α)

/-- Galí (2015), App. 5.1, p. 155 (and ch. 3, p. 62): `ψ_ya = (1 + φ)/(σ(1 − α) + φ + α)`,
so that efficient output is `ŷ^e_t = ψ_ya a_t` (restated from the Chapter 4 project). -/
noncomputable def psiYA (σ φ α : ℝ) : ℝ := (1 + φ) / (σ * (1 - α) + φ + α)

/-- Galí (2015), ch. 3, p. 61: `Θ = (1 − α)/(1 − α + αε)` (restated from the Chapter 4
project). -/
noncomputable def bigTheta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- Galí (2015), ch. 3, p. 61: `λ = (1 − θ)(1 − βθ)Θ/θ` (restated from the Chapter 4
project). -/
noncomputable def lambdaNK (β θ α ε : ℝ) : ℝ := (1 - θ) * (1 - β * θ) / θ * bigTheta α ε

/-- Galí (2015), ch. 3, p. 63: `κ = λ(σ + (φ + α)/(1 − α))` (restated from the Chapter 4
project). -/
noncomputable def kappaNK (β θ σ φ α ε : ℝ) : ℝ := lambdaNK β θ α ε * gapCoeff σ φ α

/-- Galí (2015), p. 128: the relative weight of the welfare-relevant output gap in the loss
(1), `ϑ = κ/ε`. -/
noncomputable def vartheta (β θ σ φ α ε : ℝ) : ℝ := kappaNK β θ σ φ α ε / ε

/-- Galí (2015), ch. 3, p. 61: `Θ > 0` for `0 ≤ α < 1`, `ε > 0`. -/
theorem bigTheta_pos {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) :
    0 < bigTheta α ε := by
  unfold bigTheta
  have : 0 ≤ α * ε := mul_nonneg hα0 hε.le
  exact div_pos (by linarith) (by linarith)

/-- Galí (2015), ch. 3, p. 61: `λ > 0` for `0 < θ < 1`, `β < 1`, `0 ≤ α < 1`, `ε > 0`. -/
theorem lambdaNK_pos {β θ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) : 0 < lambdaNK β θ α ε := by
  unfold lambdaNK
  have h1 : 0 < 1 - β * θ := by nlinarith
  have h2 : 0 < 1 - θ := by linarith
  exact mul_pos (div_pos (mul_pos h2 h1) hθ0) (bigTheta_pos hα0 hα1 hε)

/-- Galí (2015), p. 111: `σ + (φ + α)/(1 − α) > 0` for `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem gapCoeff_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < gapCoeff σ φ α := by
  unfold gapCoeff
  have : 0 ≤ (φ + α) / (1 - α) := div_nonneg (by linarith) (by linarith)
  linarith

/-- Galí (2015), p. 128: under the standing assumptions (`0 < θ < 1`, `0 < β < 1`,
`σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`, `ε > 1`), `ϑ = κ/ε > 0`. -/
theorem vartheta_pos {β θ σ φ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ1 : β < 1)
    (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 1 < ε) :
    0 < vartheta β θ σ φ α ε := by
  unfold vartheta kappaNK
  exact div_pos (mul_pos (lambdaNK_pos hθ0 hθ1 hβ1 hα0 hα1 (by linarith))
    (gapCoeff_pos hσ hφ hα0 hα1)) (by linarith)

/-! ### The loss function (1) -/

/-- Galí (2015), p. 128 (**`ϑ = κ/ε` from the welfare criterion, exact**): in the Chapter 4
welfare loss `½[(σ + (φ+α)/(1−α)) x² + (ε/λ) π²]` the weight of the gap relative to inflation
is `(σ + (φ+α)/(1−α))/(ε/λ) = κ/ε = ϑ`. -/
theorem vartheta_eq_weight_ratio {β θ σ φ α ε : ℝ} (hlam : lambdaNK β θ α ε ≠ 0) (hε : ε ≠ 0) :
    gapCoeff σ φ α / (ε / lambdaNK β θ α ε) = vartheta β θ σ φ α ε := by
  unfold vartheta kappaNK
  field_simp

/-- Galí (2015), p. 128 and App. 5.1, p. 156 (the period loss, exact): the Chapter 4 period
welfare loss is `ε/(2λ)` times the period loss of (1):
`½[(σ + (φ+α)/(1−α)) x² + (ε/λ) π²] = (ε/(2λ)) (π² + ϑ x²)`. -/
theorem periodLoss_eq_scaled {β θ σ φ α ε : ℝ} (hlam : lambdaNK β θ α ε ≠ 0) (hε : ε ≠ 0)
    (x infl : ℝ) :
    (gapCoeff σ φ α * x ^ 2 + ε / lambdaNK β θ α ε * infl ^ 2) / 2
      = ε / (2 * lambdaNK β θ α ε) * (infl ^ 2 + vartheta β θ σ φ α ε * x ^ 2) := by
  unfold vartheta kappaNK
  field_simp
  ring

/-- Galí (2015), eq. (1), p. 128 (**the welfare loss is proportional to (1), exact**): if
`∑ βᵗ (π_t² + ϑ x_t²)` converges to `L`, then the welfare loss
`½ ∑ βᵗ [(σ + (φ+α)/(1−α)) x_t² + (ε/λ) π_t²]` converges to `(ε/(2λ)) L`. -/
theorem hasSum_welfare_of_loss {β θ σ φ α ε L : ℝ} (hlam : lambdaNK β θ α ε ≠ 0) (hε : ε ≠ 0)
    {x infl : ℕ → ℝ}
    (hL : HasSum (fun t => β ^ t * (infl t ^ 2 + vartheta β θ σ φ α ε * x t ^ 2)) L) :
    HasSum (fun t => β ^ t * ((gapCoeff σ φ α * x t ^ 2 +
      ε / lambdaNK β θ α ε * infl t ^ 2) / 2)) (ε / (2 * lambdaNK β θ α ε) * L) := by
  convert hL.mul_left (ε / (2 * lambdaNK β θ α ε)) using 1
  funext t
  rw [periodLoss_eq_scaled hlam hε]
  ring

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (1), p. 128 (**in expectation**): if, state by state, the welfare loss
converges to `W ω` and `∑ βᵗ (π_t² + ϑ x_t²)` converges to `L ω`, then
`E_0 W = (ε/(2λ)) E_0 L`: the expected welfare loss is proportional to (1). -/
theorem expected_welfare_eq_scaled_loss {β θ σ φ α ε : ℝ} (hlam : lambdaNK β θ α ε ≠ 0)
    (hε : ε ≠ 0) {x infl : ℕ → Ω → ℝ} {W L : Ω → ℝ}
    (hW : ∀ ω, HasSum (fun t => β ^ t * ((gapCoeff σ φ α * x t ω ^ 2 +
      ε / lambdaNK β θ α ε * infl t ω ^ 2) / 2)) (W ω))
    (hL : ∀ ω, HasSum (fun t => β ^ t * (infl t ω ^ 2 +
      vartheta β θ σ φ α ε * x t ω ^ 2)) (L ω)) :
    𝔼.E 0 W = (ε / (2 * lambdaNK β θ α ε)) • 𝔼.E 0 L := by
  have hWL : W = (ε / (2 * lambdaNK β θ α ε)) • L := funext fun ω =>
    (hW ω).unique (hasSum_welfare_of_loss hlam hε (hL ω))
  rw [hWL, map_smul]

/-- Galí (2015), p. 128: since `ε/(2λ) > 0`, the welfare loss and the loss (1) rank any two
policies identically. -/
theorem welfare_le_iff_loss_le {β θ α ε L₁ L₂ : ℝ} (hlam : 0 < lambdaNK β θ α ε) (hε : 0 < ε) :
    ε / (2 * lambdaNK β θ α ε) * L₁ ≤ ε / (2 * lambdaNK β θ α ε) * L₂ ↔ L₁ ≤ L₂ :=
  mul_le_mul_iff_of_pos_left (div_pos hε (by linarith))

/-! ### The NKPC with a cost-push shock (2) -/

/-- Galí (2015), eq. (2), p. 128: the cost-push shock `u_t = κ (y^e_t − y^n_t)`. -/
def costPush (κ : ℝ) (ye yn : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => κ • (ye t - yn t)

/-- Galí (2015), ch. 3 (eq. (22), p. 63), recalled on p. 128: the NKPC in the output gap
relative to natural output, `π_t = β E_t π_{t+1} + κ (y_t − y^n_t)`. -/
def NKPCNatural (β κ : ℝ) (y yn infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • (y t - yn t)

/-- Galí (2015), eq. (2), p. 128: `π_t = β E_t π_{t+1} + κ x_t + u_t`, with `x` the
welfare-relevant output gap. -/
def NKPC (β κ : ℝ) (x u infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • x t + u t

/-- Galí (2015), eq. (2), p. 128 (**exact**): substituting `y_t − y^n_t = (y_t − y^e_t) +
(y^e_t − y^n_t)`, the Chapter 3 NKPC holds iff (2) holds with the welfare-relevant gap
`x = y − y^e` and the cost-push shock `u = κ(y^e − y^n)`. -/
theorem nkpc_iff_costPush {β κ : ℝ} {y ye yn infl : ℕ → Ω → ℝ} :
    NKPCNatural 𝔼 β κ y yn infl ↔
      NKPC 𝔼 β κ (fun t => y t - ye t) (costPush κ ye yn) infl := by
  have key : ∀ t, κ • (y t - yn t) = κ • (y t - ye t) + costPush κ ye yn t := fun t => by
    funext ω
    simp only [costPush, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  constructor
  · intro h t
    rw [h t, key t, add_assoc]
  · intro h t
    rw [h t, key t, add_assoc]

/-- Galí (2015), p. 128: for `κ ≠ 0` the cost-push shock vanishes identically iff efficient
and natural output coincide (the Chapter 4 case). -/
theorem costPush_eq_zero_iff {κ : ℝ} (hκ : κ ≠ 0) {ye yn : ℕ → Ω → ℝ} :
    costPush κ ye yn = 0 ↔ ye = yn := by
  constructor
  · intro h
    funext t ω
    have := congrFun (congrFun h t) ω
    simp only [costPush, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply,
      mul_eq_zero, hκ, false_or] at this
    linarith
  · rintro rfl
    funext t ω
    simp [costPush]

/-- Galí (2015), p. 128 (**the tradeoff**): zero inflation together with an efficient level
of activity, `π ≡ 0` and `x ≡ 0`, satisfies (2) iff `u ≡ 0`. Hence any variation in `u`
makes the two goals jointly unattainable. -/
theorem zero_outcome_iff {β κ : ℝ} {u : ℕ → Ω → ℝ} : NKPC 𝔼 β κ 0 u 0 ↔ u = 0 := by
  constructor
  · intro h
    funext t
    have := h t
    simp only [Pi.zero_apply, map_zero, smul_zero, zero_add] at this
    exact this.symm
  · rintro rfl t
    simp

/-! ### Orders of magnitude and Taylor expansions (restated from the Chapter 4 project) -/

/-- Orders of magnitude multiply: `f = O(sᵃ)` and `g = O(sᵇ)` give `f g = O(sᵃ⁺ᵇ)`
(Galí 2015, App. 5.1, p. 155; restated from the Chapter 4 project). -/
theorem bigO_mul {f g : ℝ → ℝ} {a b : ℕ} (hf : f =O[𝓝 0] fun s => s ^ a)
    (hg : g =O[𝓝 0] fun s => s ^ b) :
    (fun s => f s * g s) =O[𝓝 0] fun s => s ^ (a + b) := by
  have := hf.mul hg
  simpa [pow_add] using this

/-- Higher orders are smaller near `0`: `O(sᵇ) ⊆ O(sᵃ)` for `a ≤ b` (Galí 2015, App. 5.1,
p. 155; restated from the Chapter 4 project). -/
theorem bigO_weaken {f : ℝ → ℝ} {a b : ℕ} (hab : a ≤ b) (hf : f =O[𝓝 0] fun s => s ^ b) :
    f =O[𝓝 0] fun s => s ^ a := by
  rcases hab.lt_or_eq with h | h
  · exact hf.trans (isLittleO_pow_pow h).isBigO
  · rw [h]
    exact hf

/-- A quantity that is `O(s)` tends to `0` (Galí 2015, App. 5.1; restated from the Chapter 4
project). -/
theorem tendsto_zero_of_bigO {f : ℝ → ℝ} (hf : f =O[𝓝 0] fun s => s ^ 1) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => s ^ 1) (𝓝 0) (𝓝 0) := by
    simp only [pow_one]
    exact tendsto_id
  exact hf.trans_tendsto h

/-- Galí (2015), App. 4.1, p. 117, used in App. 5.1, p. 154 (second-order Taylor expansion
with a cubic remainder; restated from the Chapter 4 project): if `f` is `C³` near `x₀`, then
`f x = f x₀ + f'(x₀)(x − x₀) + f''(x₀)/2 (x − x₀)² + O((x − x₀)³)`. -/
theorem taylor_two {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiffAt ℝ 3 f x₀) :
    (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) - iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      =O[𝓝 x₀] fun x => (x - x₀) ^ 3 := by
  obtain ⟨U, hU, hfU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  have hs : ContDiffOn ℝ 3 f (Metric.ball x₀ r) := hfU.mono hball
  have hT := taylor_isLittleO (convex_ball x₀ r) (Metric.mem_ball_self hr) hs
  rw [nhdsWithin_eq_nhds.2 (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))] at hT
  have hx0 := Metric.mem_ball_self hr (x := x₀)
  have e1 := iteratedDerivWithin_of_isOpen (n := 1) (f := f) Metric.isOpen_ball hx0
  have e2 := iteratedDerivWithin_of_isOpen (n := 2) (f := f) Metric.isOpen_ball hx0
  have e3 := iteratedDerivWithin_of_isOpen (n := 3) (f := f) Metric.isOpen_ball hx0
  have heq : (fun x => f x - f x₀ - deriv f x₀ * (x - x₀) -
      iteratedDeriv 2 f x₀ / 2 * (x - x₀) ^ 2)
      = fun x => (f x - taylorWithinEval f 3 (Metric.ball x₀ r) x₀ x) +
        iteratedDeriv 3 f x₀ / 6 * (x - x₀) ^ 3 := by
    funext x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_zero, e1, e2,
      e3, iteratedDeriv_one, smul_eq_mul]
    norm_num [Nat.factorial]
    ring
  rw [heq]
  exact hT.isBigO.add ((isBigO_refl _ _).const_mul_left _)

/-- Galí (2015), App. 4.1, p. 117: `e^x = 1 + x + x²/2 + O(x³)` (restated from the Chapter 4
project). -/
theorem exp_taylor_two :
    (fun x => Real.exp x - 1 - x - x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 3 := by
  have h := taylor_two (f := Real.exp) (x₀ := 0) Real.contDiff_exp.contDiffAt
  have h2 : iteratedDeriv 2 Real.exp 0 = 1 := by
    rw [iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.exp_zero]
  simp only [Real.deriv_exp, Real.exp_zero, h2, sub_zero] at h
  convert h using 2 with x
  ring

/-- Galí (2015), App. 4.1, p. 117: `e^x − 1 = O(x)` (restated from the Chapter 4 project). -/
theorem exp_sub_one_bigO : (fun x => Real.exp x - 1) =O[𝓝 0] fun x => x ^ 1 := by
  have h3 := bigO_weaken (by norm_num : 1 ≤ 3) exp_taylor_two
  have h1 : (fun x : ℝ => x) =O[𝓝 0] fun x => x ^ 1 := by simpa using isBigO_refl _ _
  have h2 : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 1 :=
    bigO_weaken (by norm_num : 1 ≤ 2) ((isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left
      (fun x => by ring))
  have := (h3.add h1).add h2
  refine this.congr_left fun x => ?_
  ring

/-- Galí (2015), App. 4.1, p. 117 (second-order expansion in log deviations; restated from
the Chapter 4 project): if `f` is `C³` near `X`, then with `X_t = X e^{x}`,
`f(X_t) − f(X) = f'(X) X (x + x²/2) + f''(X) X² x²/2 + O(x³)`. -/
theorem logdev_taylor {f : ℝ → ℝ} {X : ℝ} (hf : ContDiffAt ℝ 3 f X) :
    (fun x => f (X * Real.exp x) - f X - deriv f X * X * (x + x ^ 2 / 2) -
        iteratedDeriv 2 f X / 2 * X ^ 2 * x ^ 2) =O[𝓝 0] fun x => x ^ 3 := by
  have hT := taylor_two hf
  have hg : Tendsto (fun x => X * Real.exp x) (𝓝 0) (𝓝 X) := by
    have := ((Real.continuous_exp.tendsto 0).const_mul X)
    simpa using this
  have hE1 := exp_sub_one_bigO
  have h1 : (fun x => f (X * Real.exp x) - f X - deriv f X * (X * Real.exp x - X) -
      iteratedDeriv 2 f X / 2 * (X * Real.exp x - X) ^ 2) =O[𝓝 0] fun x => x ^ 3 := by
    refine (hT.comp_tendsto hg).trans ?_
    have hc : (fun x => (X * Real.exp x - X) ^ 3) =O[𝓝 0] fun x => x ^ 3 := by
      have : (fun x => (X * Real.exp x - X) ^ 3) = fun x => X ^ 3 * (Real.exp x - 1) ^ 3 := by
        funext x
        ring
      rw [this]
      have := hE1.pow 3
      simp only [← pow_mul] at this
      exact this.const_mul_left _
    exact hc
  have h2 : (fun x => deriv f X * X * (Real.exp x - 1 - x - x ^ 2 / 2)) =O[𝓝 0]
      fun x => x ^ 3 := exp_taylor_two.const_mul_left _
  have hA : (fun x => Real.exp x - 1 - x) =O[𝓝 0] fun x => x ^ 2 := by
    have : (fun x : ℝ => x ^ 2 / 2) =O[𝓝 0] fun x => x ^ 2 :=
      (isBigO_refl _ _).const_mul_left (1 / 2) |>.congr_left (fun x => by ring)
    refine ((bigO_weaken (by norm_num : 2 ≤ 3) exp_taylor_two).add this).congr_left
      fun x => ?_
    ring
  have hB : (fun x => Real.exp x - 1 + x) =O[𝓝 0] fun x => x ^ 1 :=
    hE1.add (by simpa using isBigO_refl (fun x : ℝ => x) (𝓝 0))
  have h3 : (fun x => iteratedDeriv 2 f X / 2 * X ^ 2 *
      ((Real.exp x - 1 - x) * (Real.exp x - 1 + x))) =O[𝓝 0] fun x => x ^ 3 :=
    (bigO_mul hA hB).const_mul_left _
  refine ((h1.add h2).add h3).congr_left fun x => ?_
  ring

/-! ### Appendix 5.1: exact algebra with a distorted steady state -/

/-- Galí (2015), App. 5.1, p. 154 (the second-order polynomial in log deviations, restated
from the Chapter 4 project): with `Ū = U(C, N)`, `K = U_c C`, `U_n N`, log deviations `y`
(output = consumption), `n` (hours) and `z` (preference shifter),
`Ū(z + z²/2) + K(y + (1−σ)/2 y²) + U_n N(n + (1+φ)/2 n²) + K y z + U_n N n z`. -/
noncomputable def secondOrderUtility (Ubar K UnN σ φ y n z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) + K * (y + (1 - σ) / 2 * y ^ 2) + UnN * (n + (1 + φ) / 2 * n ^ 2) +
    K * y * z + UnN * n * z

/-- Galí (2015), App. 5.1, p. 155 (terms independent of policy, restated from the Chapter 4
project): an explicit function of the shocks `a`, `z` only. -/
noncomputable def tip (Ubar K σ φ α a z : ℝ) : ℝ :=
  Ubar * (z + z ^ 2 / 2) +
    K * (a + a * z + (gapCoeff σ φ α * psiYA σ φ α ^ 2 - (1 + φ) / (1 - α)) / 2 * a ^ 2)

/-- Galí (2015), App. 5.1, p. 155: the quadratic part
`−(K/2)[(σ + (φ+α)/(1−α))(y − ψ_ya a)² + (ε/Θ) var_i p(i)]`. -/
noncomputable def welfareQuadratic (K σ φ α ε y a v : ℝ) : ℝ :=
  -K / 2 * (gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2 + ε / bigTheta α ε * v)

/-- Galí (2015), App. 5.1, p. 155: the welfare-relevant output gap in deviations,
`x̂ = ŷ − ŷ^e` with `ŷ^e = ψ_ya a`. -/
noncomputable def xhat (σ φ α y a : ℝ) : ℝ := y - psiYA σ φ α * a

/-- Galí (2015), App. 5.1, p. 155: the second-order term multiplying `Φ` that the
"small distortion" assumption neglects, `Q = d + (1 − α)((1+φ)/2 n² + n z)`. -/
noncomputable def distRemainder (φ α n z d : ℝ) : ℝ :=
  d + (1 - α) * ((1 + φ) / 2 * n ^ 2 + n * z)

/-- Galí (2015), App. 5.1, p. 155: a steady state with distortion `Φ`, `−U_n/U_c = MPN(1 − Φ)`
with `MPN = (1 − α) Y/N` and `Y = C`, is equivalent to `U_n N = −(1 − Φ)(1 − α) U_c C`. -/
theorem distortion_iff {α Φ Uc Un C N : ℝ} (hUc : Uc ≠ 0) (hN : N ≠ 0) :
    -Un / Uc = (1 - α) * C / N * (1 - Φ) ↔ Un * N = -(1 - Φ) * (1 - α) * (Uc * C) := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-- Galí (2015), App. 4.1, p. 119: `(σ + (φ+α)/(1−α)) ψ_ya = (1 + φ)/(1 − α)` (restated from
the Chapter 4 project). -/
theorem gapCoeff_mul_psiYA {σ φ α : ℝ} (hα : α ≠ 1) (hden : σ * (1 - α) + φ + α ≠ 0) :
    gapCoeff σ φ α * psiYA σ φ α = (1 + φ) / (1 - α) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  unfold gapCoeff psiYA
  field_simp
  ring

/-- Galí (2015), App. 4.1, pp. 117–119 (completing the square at an efficient steady state,
exact; restated from the Chapter 4 project): with `U_n N = −(1 − α) U_c C` and
`(1 − α) n = y − a + d`, the polynomial equals
`−(K/2)[Γ(y − ψ_ya a)² + (ε/Θ) v] + t.i.p. + K((ε/2Θ) v − d) − K((1+φ)/(2(1−α))(2(y−a)d + d²)
+ d z)`. -/
theorem secondOrderUtility_eq_efficient {Ubar K UnN σ φ α ε y n z a d v : ℝ} (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0) (hUn : UnN = -(1 - α) * K)
    (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = welfareQuadratic K σ φ α ε y a v + tip Ubar K σ φ α a z +
        K * (ε / (2 * bigTheta α ε) * v - d) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y - a) * d + d ^ 2) + d * z) := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  have hn' : n = (y - a + d) / (1 - α) := by
    field_simp
    linarith
  have hgp := gapCoeff_mul_psiYA (σ := σ) (φ := φ) hα hden
  have hgp2 : gapCoeff σ φ α * psiYA σ φ α ^ 2 = (1 + φ) / (1 - α) * psiYA σ φ α := by
    rw [← hgp]
    ring
  have hg : gapCoeff σ φ α = σ + (φ + α) / (1 - α) := rfl
  subst hUn hn'
  unfold secondOrderUtility welfareQuadratic tip
  rw [hgp2]
  have hexp : gapCoeff σ φ α * (y - psiYA σ φ α * a) ^ 2
      = gapCoeff σ φ α * y ^ 2 - 2 * (gapCoeff σ φ α * psiYA σ φ α) * a * y +
        (1 + φ) / (1 - α) * psiYA σ φ α * a ^ 2 := by
    rw [← hgp2]
    ring
  rw [hexp, hgp, hg]
  field_simp
  ring

/-- Galí (2015), App. 5.1, pp. 154–155 (**completing the square with a distorted steady state,
exact**). If `U_n N = −(1 − Φ)(1 − α) U_c C` and `(1 − α) n = y − a + d`, then the
second-order polynomial equals
`K Φ x̂ − (K/2)[Γ x̂² + (ε/Θ) v] + t.i.p. + K Φ (ψ_ya − 1) a`
`+ K((ε/2Θ) v − d) − K((1+φ)/(2(1−α))(2(y−a)d + d²) + d z) + K Φ Q`,
with `x̂ = y − ψ_ya a`, `Q = d + (1 − α)((1+φ)/2 n² + n z)`. The term `K Φ (ψ_ya − 1) a`
is independent of policy; the last three terms are third order when `d − (ε/2Θ)v = O(s³)`,
`d = O(s²)`, and (for the last) `Φ = O(s)`. -/
theorem secondOrderUtility_eq_distorted {Ubar K UnN σ φ α ε Φ y n z a d v : ℝ} (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0) (hUn : UnN = -(1 - Φ) * (1 - α) * K)
    (hn : (1 - α) * n = y - a + d) :
    secondOrderUtility Ubar K UnN σ φ y n z
      = K * Φ * xhat σ φ α y a + welfareQuadratic K σ φ α ε y a v + tip Ubar K σ φ α a z +
        K * Φ * (psiYA σ φ α - 1) * a + K * (ε / (2 * bigTheta α ε) * v - d) -
        K * ((1 + φ) / (2 * (1 - α)) * (2 * (y - a) * d + d ^ 2) + d * z) +
        K * Φ * distRemainder φ α n z d := by
  have hlin : secondOrderUtility Ubar K UnN σ φ y n z
      = secondOrderUtility Ubar K (-(1 - α) * K) σ φ y n z +
        Φ * (1 - α) * K * (n + (1 + φ) / 2 * n ^ 2 + n * z) := by
    rw [hUn]
    unfold secondOrderUtility
    ring
  rw [hlin, secondOrderUtility_eq_efficient (ε := ε) (v := v) hα hden rfl hn]
  unfold xhat distRemainder
  linear_combination (K * Φ) * hn

/-- Galí (2015), App. 5.1, p. 155 (**the small-distortion approximation, polynomial layer**).
Along a one-parameter family of size `s` with a small distortion `Φ(s) = O(s)`, log
deviations `y, a, z = O(s)`, `v = O(s²)`, `d − (ε/2Θ) v = O(s³)` (Lemma 1) and the exact
employment identity, the second-order polynomial at `U_n N = −(1 − Φ)(1 − α) U_c C`, divided
by `K = U_c C`, equals `Φ x̂ − ½[(σ + (φ+α)/(1−α)) x̂² + (ε/Θ) v] + t.i.p.` up to `O(s³)`. -/
theorem small_distortion_polynomial {Ubar K σ φ α ε : ℝ} {Φ y n z a d v : ℝ → ℝ} (hK : K ≠ 0)
    (hα : α ≠ 1) (hden : σ * (1 - α) + φ + α ≠ 0) (hΦ : Φ =O[𝓝 0] fun s => s ^ 1)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => secondOrderUtility Ubar K (-(1 - Φ s) * (1 - α) * K) σ φ (y s) (n s) (z s) / K
        - (Φ s * xhat σ φ α (y s) (a s) - (gapCoeff σ φ α * xhat σ φ α (y s) (a s) ^ 2 +
            ε / bigTheta α ε * v s) / 2 +
          (tip Ubar K σ φ α (a s) (z s) / K + Φ s * (psiYA σ φ α - 1) * a s)))
      =O[𝓝 0] fun s => s ^ 3 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  set c := ε / (2 * bigTheta α ε) with hc
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hv.const_mul_left c)).congr_left
      fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
  have T6 : (fun s => c * v s - d s) =O[𝓝 0] fun s => s ^ 3 :=
    hd.neg_left.congr_left fun s => by ring
  have T7 : (fun s => (1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) +
      d s * z s) =O[𝓝 0] fun s => s ^ 3 := by
    have e1 : (fun s => 2 * (y s - a s) * d s) =O[𝓝 0] fun s => s ^ (1 + 2) :=
      (bigO_mul ((hy.sub ha).const_mul_left 2) hd2).congr_left fun s => by ring
    have e2 : (fun s => d s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
      bigO_weaken (by norm_num : 3 ≤ 2 + 2) ((bigO_mul hd2 hd2).congr_left fun s => by ring)
    have e3 : (fun s => d s * z s) =O[𝓝 0] fun s => s ^ (2 + 1) := bigO_mul hd2 hz
    exact ((e1.add e2).const_mul_left ((1 + φ) / (2 * (1 - α)))).add e3
  have hQ : (fun s => distRemainder φ α (n s) (z s) (d s)) =O[𝓝 0] fun s => s ^ 2 := by
    have e1 : (fun s => n s ^ 2) =O[𝓝 0] fun s => s ^ (1 + 1) :=
      (bigO_mul hn1 hn1).congr_left fun s => by ring
    have e2 : (fun s => n s * z s) =O[𝓝 0] fun s => s ^ (1 + 1) := bigO_mul hn1 hz
    exact (hd2.add (((e1.const_mul_left ((1 + φ) / 2)).add e2).const_mul_left (1 - α)))
  have T8 : (fun s => Φ s * distRemainder φ α (n s) (z s) (d s)) =O[𝓝 0]
      fun s => s ^ (1 + 2) := bigO_mul hΦ hQ
  refine ((T6.sub T7).add T8).congr_left fun s => ?_
  rw [secondOrderUtility_eq_distorted (ε := ε) (v := v s) hα hden rfl (hn s)]
  unfold welfareQuadratic xhat
  field_simp
  ring

/-! ### Appendix 5.1: the analytic bridge -/

/-- Galí (2015), App. 4.1, p. 117 and App. 5.1, p. 154 (**period utility to second order,
any steady state**). Period utility is `U(C, N; Z) = (u(C) + w(N)) Z` (separable, `Z = e^z`),
`u`, `w` of class `C³` near the steady state `(C, N)`, `σ = −U_cc C/U_c`, `φ = U_nn N/U_n`.
Along a one-parameter family with log deviations `y, n, z = O(s)`, period utility minus its
steady-state value equals the second-order polynomial up to `O(s³)`. No efficiency of the
steady state is needed (this is the first display of App. 5.1). Adapted from the Chapter 4
project. -/
theorem period_utility_sub_polynomial {u w : ℝ → ℝ} {C N σ φ : ℝ} {y n z : ℝ → ℝ}
    (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (hn1 : n =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - secondOrderUtility (u C + w N) (deriv u C * C) (deriv w N * N) σ φ (y s) (n s) (z s))
      =O[𝓝 0] fun s => s ^ 3 := by
  set K := deriv u C * C with hK
  set UnN := deriv w N * N with hUnN
  set Ubar := u C + w N with hUbar
  have cube : ∀ {f : ℝ → ℝ}, f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => f s ^ 3) =O[𝓝 0] fun s => s ^ 3 := fun {f} hf => by
    have := hf.pow 3
    simpa [← pow_mul] using this
  have hRu : (fun s => u (C * Real.exp (y s)) - u C - K * (y s + (1 - σ) / 2 * y s ^ 2))
      =O[𝓝 0] fun s => s ^ 3 := by
    have h := ((logdev_taylor hu).comp_tendsto (tendsto_zero_of_bigO hy)).trans (cube hy)
    refine h.congr_left fun s => ?_
    simp only [Function.comp_apply]
    linear_combination (-(C / 2 * y s ^ 2)) * hσ
  have hRw : (fun s => w (N * Real.exp (n s)) - w N - UnN * (n s + (1 + φ) / 2 * n s ^ 2))
      =O[𝓝 0] fun s => s ^ 3 := by
    have h := ((logdev_taylor hw).comp_tendsto (tendsto_zero_of_bigO hn1)).trans (cube hn1)
    refine h.congr_left fun s => ?_
    simp only [Function.comp_apply]
    linear_combination (-(N / 2 * n s ^ 2)) * hφ
  have hRe : (fun s => Real.exp (z s) - 1 - z s - z s ^ 2 / 2) =O[𝓝 0] fun s => s ^ 3 :=
    (exp_taylor_two.comp_tendsto (tendsto_zero_of_bigO hz)).trans (cube hz)
  have hez : (fun s => Real.exp (z s)) =O[𝓝 0] fun s => s ^ 0 := by
    have ht : Tendsto (fun s => Real.exp (z s)) (𝓝 0) (𝓝 1) := by
      have := (Real.continuous_exp.tendsto 0).comp (tendsto_zero_of_bigO hz)
      rw [Real.exp_zero] at this
      exact this
    simpa using ht.isBigO_one ℝ
  have hsq : ∀ {f : ℝ → ℝ}, f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => f s ^ 2) =O[𝓝 0] fun s => s ^ 2 := fun {f} hf => by
    have := hf.pow 2
    simpa [← pow_mul] using this
  have hpoly : ∀ {f : ℝ → ℝ} (k₁ k₂ : ℝ), f =O[𝓝 0] (fun s => s ^ 1) →
      (fun s => k₁ * f s + k₂ * f s ^ 2) =O[𝓝 0] fun s => s ^ 1 := fun {f} k₁ k₂ hf =>
    (hf.const_mul_left k₁).add (bigO_weaken (by norm_num) ((hsq hf).const_mul_left k₂))
  have T1 := hRe.const_mul_left Ubar
  have T2 : (fun s => (K * (1 - σ) / 2 * y s ^ 2 + UnN * (1 + φ) / 2 * n s ^ 2) *
      (z s + z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ (2 + 1) :=
    bigO_mul (((hsq hy).const_mul_left _).add ((hsq hn1).const_mul_left _))
      ((hpoly 1 (1 / 2) hz).congr_left fun s => by ring)
  have T3 : (fun s => (K * y s + UnN * n s) * (z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ (1 + 2) :=
    bigO_mul ((hy.const_mul_left _).add (hn1.const_mul_left _))
      (((hsq hz).const_mul_left (1 / 2)).congr_left fun s => by ring)
  have T4 : (fun s => (K * (y s + (1 - σ) / 2 * y s ^ 2) + UnN * (n s + (1 + φ) / 2 * n s ^ 2)) *
      (Real.exp (z s) - 1 - z s - z s ^ 2 / 2)) =O[𝓝 0] fun s => s ^ 3 :=
    bigO_weaken (by norm_num : 3 ≤ 1 + 3) (bigO_mul
      ((((hpoly 1 ((1 - σ) / 2) hy).const_mul_left K).add
        ((hpoly 1 ((1 + φ) / 2) hn1).const_mul_left UnN)).congr_left fun s => by ring) hRe)
  have T5 : (fun s => ((u (C * Real.exp (y s)) - u C - K * (y s + (1 - σ) / 2 * y s ^ 2)) +
      (w (N * Real.exp (n s)) - w N - UnN * (n s + (1 + φ) / 2 * n s ^ 2))) *
      Real.exp (z s)) =O[𝓝 0] fun s => s ^ (3 + 0) := bigO_mul (hRu.add hRw) hez
  refine ((((T1.add T2).add T3).add T4).add T5).congr_left fun s => ?_
  unfold secondOrderUtility
  ring

/-- Galí (2015), App. 5.1, pp. 154–155 (**period utility with a small steady-state
distortion, rigorous form**). At a steady state with distortion `Φ`,
`U_n N = −(1 − Φ)(1 − α) U_c C`, along a one-parameter family with `y, a, z = O(s)`,
`v = O(s²)`, `d − (ε/2Θ) v = O(s³)` and `(1 − α) n = y − a + d`, period utility satisfies
`U_t − U = K[Φ x̂ − ½(Γ x̂² + (ε/Θ) v)] + t.i.p. + K Φ Q(s) + O(s³)` with `K = U_c C`,
`t.i.p. = tip + K Φ (ψ_ya − 1) a`, and the neglected term `Q(s) = O(s²)`: exactly the
"product of `Φ` with a second-order term" that the book drops. -/
theorem period_utility_small_distortion {u w : ℝ → ℝ} {C N σ φ α ε Φ : ℝ}
    {y n a z d v : ℝ → ℝ} (hu : ContDiffAt ℝ 3 u C) (hw : ContDiffAt ℝ 3 w N)
    (hσ : iteratedDeriv 2 u C * C = -σ * deriv u C)
    (hφ : iteratedDeriv 2 w N * N = φ * deriv w N)
    (hDist : deriv w N * N = -(1 - Φ) * (1 - α) * (deriv u C * C)) (hα : α ≠ 1)
    (hden : σ * (1 - α) + φ + α ≠ 0)
    (hy : y =O[𝓝 0] fun s => s ^ 1) (ha : a =O[𝓝 0] fun s => s ^ 1)
    (hz : z =O[𝓝 0] fun s => s ^ 1) (hv : v =O[𝓝 0] fun s => s ^ 2)
    (hd : (fun s => d s - ε / (2 * bigTheta α ε) * v s) =O[𝓝 0] fun s => s ^ 3)
    (hn : ∀ s, (1 - α) * n s = y s - a s + d s) :
    (fun s => (u (C * Real.exp (y s)) + w (N * Real.exp (n s))) * Real.exp (z s) - (u C + w N)
        - (deriv u C * C * Φ * xhat σ φ α (y s) (a s) +
          welfareQuadratic (deriv u C * C) σ φ α ε (y s) (a s) (v s) +
          tip (u C + w N) (deriv u C * C) σ φ α (a s) (z s) +
          deriv u C * C * Φ * (psiYA σ φ α - 1) * a s)
        - deriv u C * C * Φ * distRemainder φ α (n s) (z s) (d s))
      =O[𝓝 0] (fun s => s ^ 3) ∧
    (fun s => distRemainder φ α (n s) (z s) (d s)) =O[𝓝 0] fun s => s ^ 2 := by
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα)
  set K := deriv u C * C with hK
  set c := ε / (2 * bigTheta α ε) with hc
  have hd2 : d =O[𝓝 0] fun s => s ^ 2 :=
    ((bigO_weaken (by norm_num : 2 ≤ 3) hd).add (hv.const_mul_left c)).congr_left
      fun s => by ring
  have hd1 : d =O[𝓝 0] fun s => s ^ 1 := bigO_weaken (by norm_num) hd2
  have hn1 : n =O[𝓝 0] fun s => s ^ 1 :=
    (((hy.sub ha).add hd1).const_mul_left (1 - α)⁻¹).congr_left fun s => by
      rw [← hn s]
      field_simp
  have hB := period_utility_sub_polynomial hu hw hσ hφ hy hn1 hz
  have T6 : (fun s => K * (c * v s - d s)) =O[𝓝 0] fun s => s ^ 3 :=
    (hd.neg_left.const_mul_left K).congr_left fun s => by ring
  have T7 : (fun s => K * ((1 + φ) / (2 * (1 - α)) * (2 * (y s - a s) * d s + d s ^ 2) +
      d s * z s)) =O[𝓝 0] fun s => s ^ 3 := by
    have e1 : (fun s => 2 * (y s - a s) * d s) =O[𝓝 0] fun s => s ^ (1 + 2) :=
      (bigO_mul ((hy.sub ha).const_mul_left 2) hd2).congr_left fun s => by ring
    have e2 : (fun s => d s ^ 2) =O[𝓝 0] fun s => s ^ 3 :=
      bigO_weaken (by norm_num : 3 ≤ 2 + 2) ((bigO_mul hd2 hd2).congr_left fun s => by ring)
    have e3 : (fun s => d s * z s) =O[𝓝 0] fun s => s ^ (2 + 1) := bigO_mul hd2 hz
    exact ((((e1.add e2).const_mul_left ((1 + φ) / (2 * (1 - α)))).add e3).const_mul_left K)
  refine ⟨((hB.add T6).sub T7).congr_left fun s => ?_, ?_⟩
  · rw [secondOrderUtility_eq_distorted (ε := ε) (v := v s) hα hden hDist (hn s)]
    ring
  · have e1 : (fun s => n s ^ 2) =O[𝓝 0] fun s => s ^ (1 + 1) :=
      (bigO_mul hn1 hn1).congr_left fun s => by ring
    have e2 : (fun s => n s * z s) =O[𝓝 0] fun s => s ^ (1 + 1) := bigO_mul hn1 hz
    exact (hd2.add (((e1.const_mul_left ((1 + φ) / 2)).add e2).const_mul_left (1 - α)))

/-! ### Lemma 2 and the welfare loss `W` (restated from the Chapter 4 project) -/

/-- Galí (2015), App. 4.1, p. 119 (Lemma 2, partial sums; restated from the Chapter 4
project): if `V_{t+1} = θ V_t + c q_t`, then
`∑_{t ≤ N} βᵗ V_{t+1} = θ V_0 + θβ ∑_{t < N} βᵗ V_{t+1} + c ∑_{t ≤ N} βᵗ q_t`. -/
theorem lemma2_partial {θ β c : ℝ} {V q : ℕ → ℝ} (hrec : ∀ t, V (t + 1) = θ * V t + c * q t)
    (N : ℕ) :
    ∑ t ∈ Finset.range (N + 1), β ^ t * V (t + 1)
      = θ * V 0 + θ * β * ∑ t ∈ Finset.range N, β ^ t * V (t + 1) +
        c * ∑ t ∈ Finset.range (N + 1), β ^ t * q t := by
  have h : ∀ t, β ^ (t + 1) * V (t + 1 + 1) = θ * β * (β ^ t * V (t + 1)) +
      c * (β ^ (t + 1) * q (t + 1)) := fun t => by
    rw [hrec (t + 1)]
    ring
  rw [Finset.sum_range_succ' (fun t => β ^ t * V (t + 1)),
    Finset.sum_range_succ' (fun t => β ^ t * q t), Finset.sum_congr rfl (fun t _ => h t),
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrec 0]
  ring

/-- Galí (2015), App. 4.1, p. 119 (restated from the Chapter 4 project): a variance
recursion `V_{t+1} = θ V_t + c q_t` with nonnegative data stays nonnegative. -/
theorem lemma2_nonneg {θ c : ℝ} {V q : ℕ → ℝ} (hθ : 0 ≤ θ) (hc : 0 ≤ c) (hV0 : 0 ≤ V 0)
    (hq : ∀ t, 0 ≤ q t) (hrec : ∀ t, V (t + 1) = θ * V t + c * q t) : ∀ t, 0 ≤ V t := by
  intro t
  induction t with
  | zero => exact hV0
  | succ t ih =>
    rw [hrec t]
    have := mul_nonneg hc (hq t)
    have := mul_nonneg hθ ih
    linarith

/-- Galí (2015), App. 4.1, p. 119 (Lemma 2, general form, exact; restated from the Chapter 4
project): if `V_{t+1} = θ V_t + c q_t` with `θ, β, c ≥ 0`, `βθ < 1`, `V_0 ≥ 0`, `q ≥ 0` and
`∑ βᵗ q_t` summable, then `∑ βᵗ V_{t+1} = (θ V_0 + c ∑ βᵗ q_t)/(1 − βθ)`. -/
theorem lemma2_hasSum {θ β c : ℝ} {V q : ℕ → ℝ} (hθ : 0 ≤ θ) (hβ : 0 ≤ β) (hβθ : β * θ < 1)
    (hc : 0 ≤ c) (hV0 : 0 ≤ V 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + c * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      ((θ * V 0 + c * ∑' t, β ^ t * q t) / (1 - β * θ)) := by
  have hV := lemma2_nonneg hθ hc hV0 hq hrec
  have hf0 : ∀ t, 0 ≤ β ^ t * V (t + 1) := fun t => mul_nonneg (pow_nonneg hβ t) (hV _)
  have hq0 : ∀ t, 0 ≤ β ^ t * q t := fun t => mul_nonneg (pow_nonneg hβ t) (hq t)
  set Q := ∑' t, β ^ t * q t with hQdef
  have hQle : ∀ N, ∑ t ∈ Finset.range N, β ^ t * q t ≤ Q := fun N =>
    hQ.sum_le_tsum _ (fun i _ => hq0 i)
  have hpos : 0 < 1 - β * θ := by linarith
  have hQ0 : 0 ≤ Q := tsum_nonneg hq0
  have hbound : ∀ N, ∑ t ∈ Finset.range N, β ^ t * V (t + 1) ≤
      (θ * V 0 + c * Q) / (1 - β * θ) := by
    intro N
    cases N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact div_nonneg (add_nonneg (mul_nonneg hθ hV0) (mul_nonneg hc hQ0)) hpos.le
    | succ M =>
      rw [le_div_iff₀ hpos]
      have hp := lemma2_partial (β := β) hrec M
      have hmono : ∑ t ∈ Finset.range M, β ^ t * V (t + 1) ≤
          ∑ t ∈ Finset.range (M + 1), β ^ t * V (t + 1) := by
        rw [Finset.sum_range_succ]
        linarith [hf0 M]
      have h1 := mul_le_mul_of_nonneg_left hmono (mul_nonneg hθ hβ)
      have h2 := mul_le_mul_of_nonneg_left (hQle (M + 1)) hc
      nlinarith
  have hsum : Summable fun t => β ^ t * V (t + 1) := summable_of_sum_range_le hf0 hbound
  have hg : Summable fun t => β ^ t * V t := by
    refine (summable_nat_add_iff 1).1 ?_
    have : (fun t => β ^ (t + 1) * V (t + 1)) = fun t => β * (β ^ t * V (t + 1)) := by
      funext t
      ring
    rw [this]
    exact hsum.mul_left β
  have hg0 := hg.tsum_eq_zero_add
  have hshift : ∑' t, β ^ (t + 1) * V (t + 1) = β * ∑' t, β ^ t * V (t + 1) := by
    rw [← tsum_mul_left]
    congr 1
    funext t
    ring
  have hS : ∑' t, β ^ t * V (t + 1) = θ * ∑' t, β ^ t * V t + c * Q := by
    have : (fun t => β ^ t * V (t + 1)) = fun t => θ * (β ^ t * V t) + c * (β ^ t * q t) := by
      funext t
      rw [hrec t]
      ring
    rw [this, (hg.mul_left θ).tsum_add (hQ.mul_left c), tsum_mul_left, tsum_mul_left]
  rw [hg0, hshift] at hS
  simp only [pow_zero, one_mul] at hS
  have hval : ∑' t, β ^ t * V (t + 1) = (θ * V 0 + c * Q) / (1 - β * θ) := by
    rw [eq_div_iff hpos.ne']
    linarith
  rw [← hval]
  exact hsum.hasSum

/-- Galí (2015), App. 4.1, p. 119 (Lemma 2 as printed, exact; restated from the Chapter 4
project): with no inherited dispersion and `V_{t+1} = θ V_t + (θ/(1−θ)) q_t`,
`∑ βᵗ V_{t+1} = θ/((1 − βθ)(1 − θ)) ∑ βᵗ q_t`. -/
theorem lemma2 {θ β : ℝ} {V q : ℕ → ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hV0 : V 0 = 0) (hq : ∀ t, 0 ≤ q t)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * q t) (hQ : Summable fun t => β ^ t * q t) :
    HasSum (fun t => β ^ t * V (t + 1))
      (θ / ((1 - β * θ) * (1 - θ)) * ∑' t, β ^ t * q t) := by
  have hβθ : β * θ < 1 := by nlinarith
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h := lemma2_hasSum hθ0 hβ0 hβθ (div_nonneg hθ0 (by linarith)) hV0.ge hq hrec hQ
  rw [hV0] at h
  convert h using 1
  field_simp
  ring

/-- Galí (2015), App. 4.1, p. 119 and App. 5.1, p. 156: `(ε/Θ) · θ/((1 − βθ)(1 − θ)) = ε/λ`
(restated from the Chapter 4 project). -/
theorem inflWeight_of_dispersion {β θ α ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβθ : β * θ < 1)
    (hα : α < 1) :
    ε / bigTheta α ε * (θ / ((1 - β * θ) * (1 - θ))) = ε / lambdaNK β θ α ε := by
  have h1 : (1 : ℝ) - θ ≠ 0 := by linarith
  have h2 : 1 - β * θ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - α ≠ 0 := by linarith
  unfold lambdaNK bigTheta
  field_simp

/-- Galí (2015), App. 5.1, p. 156 (**the welfare loss with a small distortion**), for given
paths of the welfare-relevant gap `x̂` and inflation `π`:
`W = −∑ βᵗ [Φ x̂_t − ½((ε/λ) π_t² + (σ + (φ+α)/(1−α)) x̂_t²)]`. -/
noncomputable def welfareW (β θ σ φ α ε Φ : ℝ) (xh infl : ℕ → ℝ) : ℝ :=
  -∑' t, β ^ t * (Φ * xh t -
    (ε / lambdaNK β θ α ε * infl t ^ 2 + gapCoeff σ φ α * xh t ^ 2) / 2)

/-- Galí (2015), App. 5.1, pp. 155–156 (**from the cross-sectional variance to inflation,
exact**). If the cross-sectional variance follows the Calvo recursion
`V_{t+1} = θ V_t + (θ/(1−θ)) π_t²` with no inherited dispersion (Chapter 4, Lemma 2), and
`∑ βᵗ x̂_t`, `∑ βᵗ x̂_t²`, `∑ βᵗ π_t²` converge, then
`−∑ βᵗ [Φ x̂_t − ½(Γ x̂_t² + (ε/Θ) V_{t+1})]` converges to `W` of `welfareW`. -/
theorem welfare_small_distortion {β θ σ φ α ε Φ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hα : α < 1) {xh infl V : ℕ → ℝ} (hV0 : V 0 = 0)
    (hrec : ∀ t, V (t + 1) = θ * V t + θ / (1 - θ) * infl t ^ 2)
    (hX1 : Summable fun t => β ^ t * xh t) (hX2 : Summable fun t => β ^ t * xh t ^ 2)
    (hD : Summable fun t => β ^ t * infl t ^ 2) :
    HasSum (fun t => -(β ^ t * (Φ * xh t -
        (gapCoeff σ φ α * xh t ^ 2 + ε / bigTheta α ε * V (t + 1)) / 2)))
      (welfareW β θ σ φ α ε Φ xh infl) := by
  have hβθ : β * θ < 1 := by nlinarith
  have hL := lemma2 (q := fun t => infl t ^ 2) hθ0.le hθ1 hβ0 hβ1 hV0 (fun _ => sq_nonneg _)
    hrec hD
  have hB : HasSum (fun t => β ^ t * (Φ * xh t -
      (ε / lambdaNK β θ α ε * infl t ^ 2 + gapCoeff σ φ α * xh t ^ 2) / 2))
      (Φ * ∑' t, β ^ t * xh t - (ε / lambdaNK β θ α ε * ∑' t, β ^ t * infl t ^ 2 +
        gapCoeff σ φ α * ∑' t, β ^ t * xh t ^ 2) / 2) := by
    have := (hX1.hasSum.mul_left Φ).sub (((hD.hasSum.mul_left (ε / lambdaNK β θ α ε)).add
      (hX2.hasSum.mul_left (gapCoeff σ φ α))).div_const 2)
    convert this using 1
    funext t
    ring
  have hA := ((hX1.hasSum.mul_left Φ).sub (((hX2.hasSum.mul_left (gapCoeff σ φ α)).add
    (hL.mul_left (ε / bigTheta α ε))).div_const 2)).neg
  rw [welfareW, hB.tsum_eq, ← inflWeight_of_dispersion hθ0 hθ1 hβθ hα]
  convert hA using 1
  · funext t
    ring
  · ring

/-- Galí (2015), App. 5.1, p. 156, last paragraph, and eq. (1), p. 128 (**the efficient case,
exact**): with `Φ = 0` the welfare loss is `(ε/(2λ)) ∑ βᵗ (π_t² + ϑ x_t²)`, i.e. proportional
to the loss function (1) with `ϑ = κ/ε`. -/
theorem welfareW_efficient {β θ σ φ α ε : ℝ} (hlam : lambdaNK β θ α ε ≠ 0) (hε : ε ≠ 0)
    (x infl : ℕ → ℝ) :
    welfareW β θ σ φ α ε 0 x infl
      = ε / (2 * lambdaNK β θ α ε) * ∑' t, β ^ t * (infl t ^ 2 + vartheta β θ σ φ α ε * x t ^ 2)
    := by
  rw [welfareW, ← tsum_neg, ← tsum_mul_left]
  congr 1
  funext t
  have h := periodLoss_eq_scaled (σ := σ) (φ := φ) hlam hε (x t) (infl t)
  linear_combination (β ^ t) * h

end Gali.DiscretionCommitment.LossAndCostPush
