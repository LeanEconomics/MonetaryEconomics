/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Expectations
import GainsFromCommitment.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Monetary frictions and the optimal long-run inflation target

Woodford (2003), *Interest and Prices*, Chapter 7, §1.2, pp. 476–480.

With transactions frictions the welfare-theoretic loss acquires a term `λ_i(i_t − iᵐ)²`
((1.14)), and the plans compared must also satisfy the IS relation (1.15). Everything is stated
for a general linear model (`Model`) whose aggregate-supply relation carries the real-balance
shift `κϕ(i_t − r̄)` and whose IS relation carries the real-balance terms of Chapter 4 (3.10);
the basic model of (1.1), (1.14), (1.15) is `basic` (`ϕ = 0`, `a = 1`, `b = 0`) and the
real-balance model behind (1.20) is `rbModel`. The book's statements hold "up to an error of order
`O(‖Δ_{-1}^{1/2}, r̄ − iᵐ‖²)`"; that qualifier belongs to the Chapter 6 welfare approximation and
is recorded here only in docstrings — the exact linear-quadratic problem as posed is proved.

## Infrastructure
* Bounded sequences `Bdd` and the discounted sum `dsum β f = ∑' t, βᵗ f_t` (a genuine
  convergent series, `summable_dsum`), with linearity, `dsum_shift` (summation by parts),
  `dsum_eq_zero_iff`, `dsum_of_zero_from`.

## The Lagrangian (p. 478)
* `lagrangian` with the initial-constraint multipliers `φ_{1,−1}`, `φ_{2,−1}` (`initTerm`);
  `lagged` gives the pre-sample value of the multipliers.
* `constraint_by_parts`, `lagrangian_expand`: the exact expansion
  `𝓛(y + εd) = 𝓛(y) + ε∑βᵗF·d + (ε²/2)∑βᵗQ(d)`.
* (1.16)–(1.18) as exact derivatives: `hasDerivAt_lagrangian_pi`, `hasDerivAt_lagrangian_x`,
  `hasDerivAt_lagrangian_i`; book form for the basic model `basic_foc_116`, `basic_foc_117`,
  `basic_foc_118`.
* Lagrangian sufficiency (three constraints): `lagrangian_sufficiency` (exact loss identity),
  `loss_le_of_foc`, `eq_of_loss_le_of_foc` (uniqueness from strict convexity).

## Timeless optimality and Proposition 7.3
* `TimelesslyOptimal`: precise definition (p. 477) — for every date `t₀`, the constant plan
  minimises the loss from `t₀` on among bounded plans satisfying the constraints from `t₀` on with
  the initial constraints `π_{t₀} = π̄`, `a x_{t₀} + b i_{t₀} = a x̄ + b ı̄` (`x_{t₀} = x̄` in the
  basic model).
* Constant multipliers: `foc_const_iff` (general) and `basic_const_foc` (p. 478: constant `x, i`
  force constant multipliers and `λ_i(ı̄ − iᵐ) = −βπ̄`); `TimelessCond`, `basic_cond_iff`.
* Sufficiency `timelesslyOptimal_of_cond`, necessity `cond_of_timelesslyOptimal` (a feasible test
  deviation `pertPi`, `pertX`, `pertI`, `dsum_pert`, `eq_zero_of_forall_nonneg`),
  `timelesslyOptimal_iff`, `stationary_iff`, `timelesslyOptimal_iff_piBar`, uniqueness
  `timeless_unique`.
* (1.19): `eq_1_19`, `piBar_basic`; **Proposition 7.3**: `prop_7_3` (iff), `prop_7_3_unique`.
* p. 479: `piBar_119_neg`, `piBar_119_gt_friedman` (`ı̄ > iᵐ`), the flexible-price limit
  `tendsto_piBar_119_atTop` (`λ_i → ∞`) and the cashless limit `tendsto_piBar_119_zero`
  (`λ_i → 0`).

## Real-balance effects (1.20), pp. 479–480
* Chapter 4 relations restated: `AS314`, `IS310`, with `rb_AS_iff`, `rb_IS_iff`; `epsMC`, `phiRB`,
  `rbModel`, `rbModel_chi_zero` (reduces to the basic model).
* `rb_coef` (`b − aϕ = σϕω`), `denom_rb`, **(1.20)**: `eq_1_20` (iff).
* Sign claim (p. 480): `piBar_120_strictAnti`, `hasDerivAt_piBar_120`, `deriv_piBar_120_neg`.

## Under uncertainty
* `ASs`, `ISs`, `expLoss`; `dsum_grad_eq_zero`, `expLoss_eq` (exact decomposition of expected
  loss), `loss_le_expLoss`, `prop_7_3_uncertainty`: optimality for an arbitrary
  `ExpectationSystem` (no pull-out property needed, the multipliers being constant).
-/

namespace Woodford.GainsFromCommitment.MonetaryFrictions

open Filter Topology
open Sequences

/-! ### Bounded sequences and discounted sums -/

/-- Woodford (2003), (1.14), p. 476: the discounted sum `∑_{t ≥ 0} βᵗ f_t`. -/
noncomputable def dsum (β : ℝ) (f : ℕ → ℝ) : ℝ := ∑' t, β ^ t * f t

/-- Woodford (2003), (1.14), p. 476: for `0 ≤ β < 1` the discounted sum of a bounded sequence
is a genuine (absolutely) convergent series. -/
theorem summable_dsum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → ℝ} (hf : Bdd f) :
    Summable (fun t => β ^ t * f t) :=
  hf.elim fun _ hC => summable_disc hβ0 hβ1 hC

/-- Woodford (2003), (1.14), p. 476: the discounted sum is additive on bounded sequences. -/
theorem dsum_add {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → ℝ} (hf : Bdd f)
    (hg : Bdd g) : dsum β (fun t => f t + g t) = dsum β f + dsum β g := by
  unfold dsum
  simp_rw [mul_add]
  exact (summable_dsum hβ0 hβ1 hf).tsum_add (summable_dsum hβ0 hβ1 hg)

/-- Woodford (2003), (1.14), p. 476: the discounted sum commutes with differences. -/
theorem dsum_sub {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → ℝ} (hf : Bdd f)
    (hg : Bdd g) : dsum β (fun t => f t - g t) = dsum β f - dsum β g := by
  unfold dsum
  simp_rw [mul_sub]
  exact (summable_dsum hβ0 hβ1 hf).tsum_sub (summable_dsum hβ0 hβ1 hg)

/-- Woodford (2003), (1.14), p. 476: the discounted sum is homogeneous. -/
theorem dsum_mul_left (β c : ℝ) (f : ℕ → ℝ) : dsum β (fun t => c * f t) = c * dsum β f := by
  unfold dsum
  rw [← tsum_mul_left]
  congr 1
  funext t
  ring

/-- Woodford (2003), (1.14), p. 476: the discounted sum of a constant, `c/(1 − β)`. -/
theorem dsum_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (c : ℝ) :
    dsum β (fun _ => c) = c / (1 - β) := by
  unfold dsum
  rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1]
  ring

/-- Woodford (2003), p. 478 (summation by parts): if `g_{t+1} = h_t` then
`∑ βᵗ h_t = β⁻¹(∑ βᵗ g_t − g_0)`. This is the identity that turns the lead terms of the
constraints into the lagged multipliers of (1.16)–(1.17). -/
theorem dsum_shift {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {g h : ℕ → ℝ} (hg : Bdd g)
    (hgh : ∀ t, g (t + 1) = h t) : dsum β h = β⁻¹ * (dsum β g - g 0) := by
  have h1 := (summable_dsum hβ0.le hβ1 hg).tsum_eq_zero_add
  have h2 : ∑' t, β ^ (t + 1) * g (t + 1) = β * dsum β h := by
    unfold dsum
    rw [← tsum_mul_left]
    congr 1
    funext t
    rw [hgh t, pow_succ]
    ring
  have h3 : dsum β g = g 0 + β * dsum β h := by
    unfold dsum at h2 ⊢
    rw [h1, h2, pow_zero, one_mul]
  rw [h3]
  field_simp
  ring

/-- Woodford (2003), (1.14), p. 476: the discounted sum of a nonnegative sequence is
nonnegative. -/
theorem dsum_nonneg {β : ℝ} (hβ0 : 0 ≤ β) {f : ℕ → ℝ} (hf : ∀ t, 0 ≤ f t) : 0 ≤ dsum β f :=
  tsum_nonneg (fun t => mul_nonneg (pow_nonneg hβ0 t) (hf t))

/-- Woodford (2003), (1.14), p. 476: a bounded nonnegative sequence has zero discounted sum
(with `0 < β < 1`) only if it vanishes identically. -/
theorem dsum_eq_zero_iff {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {f : ℕ → ℝ} (hb : Bdd f)
    (hf : ∀ t, 0 ≤ f t) : dsum β f = 0 ↔ ∀ t, f t = 0 := by
  constructor
  · intro h0 t
    have hs := (summable_dsum hβ0.le hβ1 hb).hasSum
    unfold dsum at h0
    rw [h0, hasSum_zero_iff_of_nonneg (fun t => mul_nonneg (pow_nonneg hβ0.le t) (hf t))]
      at hs
    have := congrFun hs t
    simp only [Pi.zero_apply, mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h (pow_ne_zero t hβ0.ne')
    · exact h
  · intro h
    unfold dsum
    simp [h]

/-! ### The model -/

/-- Woodford (2003), §1.2, pp. 476–480: the parameters of the deterministic model with
transactions frictions. The aggregate-supply relation is
`π_t = κ x_t + κϕ(i_t − r̄) + β π_{t+1}` and the IS relation is
`a x_t = a x_{t+1} − σ(i_t − π_{t+1} − r̄) + b(i_{t+1} − i_t)`. With `ϕ = 0`, `a = 1`, `b = 0`
these are (1.1) and (1.15) (`basic`); with the Chapter 4 real-balance coefficients they are the
real-balance relations behind (1.20) (`rbModel`). The loss is (1.14),
`∑ βᵗ [π_t² + λ_x(x_t − x*)² + λ_i(i_t − iᵐ)²]`. -/
structure Model where
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The slope `κ` of the aggregate-supply relation. -/
  κ : ℝ
  /-- The intertemporal elasticity `σ` in the IS relation. -/
  σ : ℝ
  /-- The real-balance coefficient `ϕ` in the aggregate-supply relation. -/
  ϕ : ℝ
  /-- The coefficient `a = 1 − ση_yχ` on the output gap in the IS relation. -/
  a : ℝ
  /-- The coefficient `b = ση_iχ` on the interest-rate change in the IS relation. -/
  b : ℝ
  /-- The natural rate of interest `r̄`. -/
  rbar : ℝ
  /-- The weight `λ_x` on the output gap in the loss. -/
  lamx : ℝ
  /-- The weight `λ_i` on the interest differential in the loss. -/
  lami : ℝ
  /-- The efficient output gap `x*`. -/
  xstar : ℝ
  /-- The interest rate `iᵐ` paid on the monetary base. -/
  im : ℝ

/-- Woodford (2003), eq. (1.1) p. 469 (`ϕ = 0`) and Ch. 6 eq. (4.8) p. 421 (real-balance
effects): the aggregate-supply relation at date `t`,
`π_t = κ x_t + κϕ(i_t − r̄) + β π_{t+1}`. -/
def AS (M : Model) (π x i : ℕ → ℝ) (t : ℕ) : Prop :=
  π t = M.κ * x t + M.κ * M.ϕ * (i t - M.rbar) + M.β * π (t + 1)

/-- Woodford (2003), eq. (1.15) p. 477 (`a = 1`, `b = 0`) and Ch. 4 eq. (3.10) p. 302
(real-balance effects, constant `iᵐ`): the IS relation at date `t`,
`a x_t = a x_{t+1} − σ(i_t − π_{t+1} − r̄) + b(i_{t+1} − i_t)`. -/
def IS (M : Model) (π x i : ℕ → ℝ) (t : ℕ) : Prop :=
  M.a * x t = M.a * x (t + 1) - M.σ * (i t - π (t + 1) - M.rbar) + M.b * (i (t + 1) - i t)

/-- Woodford (2003), p. 477: a plan `{π_t, x_t, i_t}` is feasible when (1.1) and (1.15) hold
for every `t ≥ 0`. -/
def Feasible (M : Model) (π x i : ℕ → ℝ) : Prop := ∀ t, AS M π x i t ∧ IS M π x i t

/-- Woodford (2003), eq. (1.14), p. 476: the period loss
`π_t² + λ_x(x_t − x*)² + λ_i(i_t − iᵐ)²`. -/
def periodLoss (M : Model) (π x i : ℕ → ℝ) (t : ℕ) : ℝ :=
  π t ^ 2 + M.lamx * (x t - M.xstar) ^ 2 + M.lami * (i t - M.im) ^ 2

/-- Woodford (2003), eq. (1.14), p. 476: the discounted loss `∑_{t ≥ 0} βᵗ L_t`. -/
noncomputable def loss (M : Model) (π x i : ℕ → ℝ) : ℝ := dsum M.β (periodLoss M π x i)

/-- Woodford (2003), p. 478: the residual of the IS constraint in the Lagrangian,
`a x_t − a x_{t+1} + σ(i_t − π_{t+1} − r̄) − b(i_{t+1} − i_t)` (zero iff (1.15) holds). -/
def resIS (M : Model) (π x i : ℕ → ℝ) (t : ℕ) : ℝ :=
  M.a * x t - M.a * x (t + 1) + M.σ * (i t - π (t + 1) - M.rbar) - M.b * (i (t + 1) - i t)

/-- Woodford (2003), p. 478: the residual of the aggregate-supply constraint in the
Lagrangian, `π_t − κx_t − κϕ(i_t − r̄) − βπ_{t+1}` (zero iff (1.1) holds). -/
def resAS (M : Model) (π x i : ℕ → ℝ) (t : ℕ) : ℝ :=
  π t - M.κ * x t - M.κ * M.ϕ * (i t - M.rbar) - M.β * π (t + 1)

/-- Woodford (2003), p. 478: `β` times the initial-constraint terms of the Lagrangian,
`φ_{1,−1}(a x_0 + σπ_0 + b i_0) + βφ_{2,−1}π_0`; the Lagrangian subtracts `β⁻¹` times this
(for the basic model, `β⁻¹φ_{1,−1}[x_0 + σπ_0] + φ_{2,−1}π_0`). -/
def initTerm (M : Model) (φ1m φ2m : ℝ) (π x i : ℕ → ℝ) : ℝ :=
  φ1m * (M.a * x 0 + M.σ * π 0 + M.b * i 0) + M.β * φ2m * π 0

/-- Woodford (2003), p. 478: the Lagrangian
`∑ βᵗ {½L_t + φ_{1t}·[IS residual] + φ_{2t}·[AS residual]} − β⁻¹φ_{1,−1}[…] − φ_{2,−1}π_0`. -/
noncomputable def lagrangian (M : Model) (φ1 φ2 : ℕ → ℝ) (φ1m φ2m : ℝ) (π x i : ℕ → ℝ) : ℝ :=
  dsum M.β (fun t => periodLoss M π x i t / 2 + φ1 t * resIS M π x i t +
    φ2 t * resAS M π x i t) - M.β⁻¹ * initTerm M φ1m φ2m π x i

/-- Woodford (2003), (1.16), p. 478: the multiplier part of the inflation FOC,
`−β⁻¹σφ_{1,t−1} + φ_{2t} − φ_{2,t−1}`. -/
noncomputable def multPi (M : Model) (φ1 φ2 : ℕ → ℝ) (φ1m φ2m : ℝ) (t : ℕ) : ℝ :=
  -(M.β⁻¹ * M.σ * lagged φ1m φ1 t) + φ2 t - lagged φ2m φ2 t

/-- Woodford (2003), (1.17), p. 478: the multiplier part of the output-gap FOC,
`aφ_{1t} − β⁻¹aφ_{1,t−1} − κφ_{2t}`. -/
noncomputable def multX (M : Model) (φ1 φ2 : ℕ → ℝ) (φ1m : ℝ) (t : ℕ) : ℝ :=
  M.a * φ1 t - M.β⁻¹ * M.a * lagged φ1m φ1 t - M.κ * φ2 t

/-- Woodford (2003), (1.18), p. 478: the multiplier part of the interest-rate FOC,
`(σ + b)φ_{1t} − β⁻¹bφ_{1,t−1} − κϕφ_{2t}`. -/
noncomputable def multI (M : Model) (φ1 φ2 : ℕ → ℝ) (φ1m : ℝ) (t : ℕ) : ℝ :=
  (M.σ + M.b) * φ1 t - M.β⁻¹ * M.b * lagged φ1m φ1 t - M.κ * M.ϕ * φ2 t

/-- Woodford (2003), eq. (1.16), p. 478: the inflation first-order condition
`π_t − β⁻¹σφ_{1,t−1} + φ_{2t} − φ_{2,t−1}` (set to zero). -/
noncomputable def focPi (M : Model) (φ1 φ2 : ℕ → ℝ) (φ1m φ2m : ℝ) (π : ℕ → ℝ) (t : ℕ) : ℝ :=
  π t + multPi M φ1 φ2 φ1m φ2m t

/-- Woodford (2003), eq. (1.17), p. 478: the output-gap first-order condition
`λ_x(x_t − x*) + aφ_{1t} − β⁻¹aφ_{1,t−1} − κφ_{2t}` (set to zero). -/
noncomputable def focX (M : Model) (φ1 φ2 : ℕ → ℝ) (φ1m : ℝ) (x : ℕ → ℝ) (t : ℕ) : ℝ :=
  M.lamx * (x t - M.xstar) + multX M φ1 φ2 φ1m t

/-- Woodford (2003), eq. (1.18), p. 478: the interest-rate first-order condition
`λ_i(i_t − iᵐ) + (σ + b)φ_{1t} − β⁻¹bφ_{1,t−1} − κϕφ_{2t}` (set to zero). -/
noncomputable def focI (M : Model) (φ1 φ2 : ℕ → ℝ) (φ1m : ℝ) (i : ℕ → ℝ) (t : ℕ) : ℝ :=
  M.lami * (i t - M.im) + multI M φ1 φ2 φ1m t

/-- Woodford (2003), (1.14), p. 476: the quadratic form of a deviation,
`dπ_t² + λ_x dx_t² + λ_i di_t²`. -/
def quad (M : Model) (dπ dx di : ℕ → ℝ) (t : ℕ) : ℝ :=
  dπ t ^ 2 + M.lamx * dx t ^ 2 + M.lami * di t ^ 2

/-- Woodford (2003), p. 478: the homogeneous IS residual of a deviation `d`. -/
def homIS (M : Model) (dπ dx di : ℕ → ℝ) (t : ℕ) : ℝ :=
  M.a * dx t - M.a * dx (t + 1) + M.σ * (di t - dπ (t + 1)) - M.b * (di (t + 1) - di t)

/-- Woodford (2003), p. 478: the homogeneous aggregate-supply residual of a deviation `d`. -/
def homAS (M : Model) (dπ dx di : ℕ → ℝ) (t : ℕ) : ℝ :=
  dπ t - M.κ * dx t - M.κ * M.ϕ * di t - M.β * dπ (t + 1)

/-- Woodford (2003), p. 478 (summation by parts): for bounded multipliers and a bounded
deviation `d`, the constraint terms of the Lagrangian rearrange into the multiplier parts of
(1.16)–(1.18):
`∑βᵗ[φ_{1t}·IS_t(d) + φ_{2t}·AS_t(d)] − β⁻¹·init(d) = ∑βᵗ[m^π_t dπ_t + m^x_t dx_t + m^i_t di_t]`.
-/
theorem constraint_by_parts {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) {φ1 φ2 dπ dx di : ℕ → ℝ}
    (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hp : Bdd dπ) (hx : Bdd dx) (hi : Bdd di) :
    dsum M.β (fun t => φ1 t * homIS M dπ dx di t + φ2 t * homAS M dπ dx di t) -
        M.β⁻¹ * initTerm M φ1m φ2m dπ dx di =
      dsum M.β (fun t => multPi M φ1 φ2 φ1m φ2m t * dπ t + multX M φ1 φ2 φ1m t * dx t +
        multI M φ1 φ2 φ1m t * di t) := by
  set P : ℕ → ℝ := fun t => φ1 t * (M.a * dx t + M.σ * di t + M.b * di t) +
    φ2 t * (dπ t - M.κ * dx t - M.κ * M.ϕ * di t) with hP
  set H : ℕ → ℝ := fun t => φ1 t * (M.a * dx (t + 1) + M.σ * dπ (t + 1) + M.b * di (t + 1)) +
    M.β * φ2 t * dπ (t + 1) with hH
  set G : ℕ → ℝ := fun t => lagged φ1m φ1 t * (M.a * dx t + M.σ * dπ t + M.b * di t) +
    M.β * lagged φ2m φ2 t * dπ t with hG
  have hPb : Bdd P :=
    (h1.mul (((bdd_const _).mul hx).add ((bdd_const _).mul hi) |>.add
      ((bdd_const _).mul hi))).add
      (h2.mul ((hp.sub ((bdd_const _).mul hx)).sub ((bdd_const _).mul hi)))
  have hGb : Bdd G :=
    ((h1.lag φ1m).mul ((((bdd_const _).mul hx).add ((bdd_const _).mul hp)).add
      ((bdd_const _).mul hi))).add (((bdd_const _).mul (h2.lag φ2m)).mul hp)
  have hHb : Bdd H := by
    have := hGb.shift
    simpa [hG, hH] using this
  have hGH : ∀ t, G (t + 1) = H t := fun t => by simp [hG, hH]
  have hsplit : (fun t => φ1 t * homIS M dπ dx di t + φ2 t * homAS M dπ dx di t) =
      fun t => P t - H t := by
    funext t
    simp only [hP, hH, homIS, homAS]
    ring
  have hG0 : G 0 = initTerm M φ1m φ2m dπ dx di := by
    simp only [hG, lagged_zero, initTerm]
  have hfin : (fun t => multPi M φ1 φ2 φ1m φ2m t * dπ t + multX M φ1 φ2 φ1m t * dx t +
      multI M φ1 φ2 φ1m t * di t) = fun t => P t - M.β⁻¹ * G t := by
    funext t
    simp only [hP, hG, multPi, multX, multI]
    have hββ : M.β * M.β⁻¹ = 1 := mul_inv_cancel₀ hβ0.ne'
    linear_combination (lagged φ2m φ2 t * dπ t) * hββ
  rw [hsplit, dsum_sub hβ0.le hβ1 hPb hHb, dsum_shift hβ0 hβ1 hGb hGH, hfin,
    dsum_sub hβ0.le hβ1 hPb ((bdd_const _).mul hGb), dsum_mul_left, hG0]
  ring

/-- Woodford (2003), (1.16), p. 478: the multiplier part of the inflation FOC is bounded for
bounded multipliers. -/
theorem bdd_multPi (M : Model) {φ1 φ2 : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) :
    Bdd (multPi M φ1 φ2 φ1m φ2m) :=
  (((bdd_const _).mul (h1.lag φ1m)).neg.add h2).sub (h2.lag φ2m)

/-- Woodford (2003), (1.17), p. 478: the multiplier part of the output-gap FOC is bounded. -/
theorem bdd_multX (M : Model) {φ1 φ2 : ℕ → ℝ} (φ1m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) :
    Bdd (multX M φ1 φ2 φ1m) :=
  (((bdd_const _).mul h1).sub ((bdd_const _).mul (h1.lag φ1m))).sub ((bdd_const _).mul h2)

/-- Woodford (2003), (1.18), p. 478: the multiplier part of the interest-rate FOC is
bounded. -/
theorem bdd_multI (M : Model) {φ1 φ2 : ℕ → ℝ} (φ1m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) :
    Bdd (multI M φ1 φ2 φ1m) :=
  (((bdd_const _).mul h1).sub ((bdd_const _).mul (h1.lag φ1m))).sub ((bdd_const _).mul h2)

/-- Woodford (2003), (1.14), p. 476: the period loss of a bounded plan is bounded. -/
theorem bdd_periodLoss (M : Model) {π x i : ℕ → ℝ} (hπ : Bdd π) (hx : Bdd x) (hi : Bdd i) :
    Bdd (periodLoss M π x i) :=
  (hπ.sq.add ((bdd_const _).mul (hx.sub (bdd_const _)).sq)).add
    ((bdd_const _).mul (hi.sub (bdd_const _)).sq)

/-- Woodford (2003), (1.14), p. 476: the quadratic form of a bounded deviation is bounded. -/
theorem bdd_quad (M : Model) {dπ dx di : ℕ → ℝ} (hp : Bdd dπ) (hx : Bdd dx) (hi : Bdd di) :
    Bdd (quad M dπ dx di) :=
  (hp.sq.add ((bdd_const _).mul hx.sq)).add ((bdd_const _).mul hi.sq)

/-- Woodford (2003), (1.14), p. 476: with `λ_x, λ_i ≥ 0` the quadratic form is nonnegative. -/
theorem quad_nonneg {M : Model} (hlx : 0 ≤ M.lamx) (hli : 0 ≤ M.lami) (dπ dx di : ℕ → ℝ)
    (t : ℕ) : 0 ≤ quad M dπ dx di t := by
  unfold quad
  have := sq_nonneg (dπ t)
  have := mul_nonneg hlx (sq_nonneg (dx t))
  have := mul_nonneg hli (sq_nonneg (di t))
  linarith

/-- Woodford (2003), p. 478 (exact expansion of the Lagrangian): for bounded plans,
multipliers and deviations, `𝓛(y + εd) = 𝓛(y) + ε ∑βᵗ[F^π_t dπ_t + F^x_t dx_t + F^i_t di_t]
+ (ε²/2) ∑βᵗ[dπ_t² + λ_x dx_t² + λ_i di_t²]`, where `F^π, F^x, F^i` are the left sides of the
first-order conditions (1.16)–(1.18). This is the identity behind both the first-order
conditions and their sufficiency. -/
theorem lagrangian_expand {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i dπ dx di : ℕ → ℝ} (φ1m φ2m ε : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (hdp : Bdd dπ) (hdx : Bdd dx) (hdi : Bdd di) :
    lagrangian M φ1 φ2 φ1m φ2m (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
        (fun t => i t + ε * di t) =
      lagrangian M φ1 φ2 φ1m φ2m π x i +
        ε * dsum M.β (fun t => focPi M φ1 φ2 φ1m φ2m π t * dπ t + focX M φ1 φ2 φ1m x t * dx t +
          focI M φ1 φ2 φ1m i t * di t) +
        ε ^ 2 / 2 * dsum M.β (quad M dπ dx di) := by
  set S0 : ℕ → ℝ := fun t => periodLoss M π x i t / 2 + φ1 t * resIS M π x i t +
    φ2 t * resAS M π x i t with hS0
  set Gr : ℕ → ℝ := fun t => π t * dπ t + M.lamx * (x t - M.xstar) * dx t +
    M.lami * (i t - M.im) * di t with hGr
  set C : ℕ → ℝ := fun t => φ1 t * homIS M dπ dx di t + φ2 t * homAS M dπ dx di t with hC
  set Mu : ℕ → ℝ := fun t => multPi M φ1 φ2 φ1m φ2m t * dπ t + multX M φ1 φ2 φ1m t * dx t +
    multI M φ1 φ2 φ1m t * di t with hMu
  have hpt : (fun t => periodLoss M (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
      (fun t => i t + ε * di t) t / 2 +
      φ1 t * resIS M (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
        (fun t => i t + ε * di t) t +
      φ2 t * resAS M (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
        (fun t => i t + ε * di t) t) =
      fun t => S0 t + (ε * (Gr t + C t) + ε ^ 2 / 2 * quad M dπ dx di t) := by
    funext t
    simp only [hS0, hGr, hC, periodLoss, resIS, resAS, homIS, homAS, quad]
    ring
  have hinit : initTerm M φ1m φ2m (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
      (fun t => i t + ε * di t) =
      initTerm M φ1m φ2m π x i + ε * initTerm M φ1m φ2m dπ dx di := by
    simp only [initTerm]
    ring
  have hres : ∀ {u v w : ℕ → ℝ}, Bdd u → Bdd v → Bdd w →
      Bdd (resIS M u v w) ∧ Bdd (resAS M u v w) := by
    intro u v w hu hv hw
    exact ⟨((((bdd_const _).mul hv).sub ((bdd_const _).mul hv.shift)).add
      ((bdd_const _).mul ((hw.sub hu.shift).sub (bdd_const _)))).sub
      ((bdd_const _).mul (hw.shift.sub hw)),
      (((hu.sub ((bdd_const _).mul hv)).sub ((bdd_const _).mul (hw.sub (bdd_const _)))).sub
      ((bdd_const _).mul hu.shift))⟩
  have hS0b : Bdd S0 :=
    (((bdd_periodLoss M hπ hx hi).mul (bdd_const _)).add (h1.mul (hres hπ hx hi).1)).add
      (h2.mul (hres hπ hx hi).2)
  have hGrb : Bdd Gr :=
    ((hπ.mul hdp).add (((bdd_const _).mul (hx.sub (bdd_const _))).mul hdx)).add
      (((bdd_const _).mul (hi.sub (bdd_const _))).mul hdi)
  have hCb : Bdd C := by
    have hIS : Bdd (homIS M dπ dx di) :=
      ((((bdd_const _).mul hdx).sub ((bdd_const _).mul hdx.shift)).add
        ((bdd_const _).mul (hdi.sub hdp.shift))).sub ((bdd_const _).mul (hdi.shift.sub hdi))
    have hAS : Bdd (homAS M dπ dx di) :=
      ((hdp.sub ((bdd_const _).mul hdx)).sub ((bdd_const _).mul hdi)).sub
        ((bdd_const _).mul hdp.shift)
    exact (h1.mul hIS).add (h2.mul hAS)
  have hMub : Bdd Mu :=
    (((bdd_multPi M φ1m φ2m h1 h2).mul hdp).add ((bdd_multX M φ1m h1 h2).mul hdx)).add
      ((bdd_multI M φ1m h1 h2).mul hdi)
  have hQb : Bdd (quad M dπ dx di) := bdd_quad M hdp hdx hdi
  have key := constraint_by_parts hβ0 hβ1 φ1m φ2m h1 h2 hdp hdx hdi
  have hF : (fun t => focPi M φ1 φ2 φ1m φ2m π t * dπ t + focX M φ1 φ2 φ1m x t * dx t +
      focI M φ1 φ2 φ1m i t * di t) = fun t => Gr t + Mu t := by
    funext t
    simp only [hGr, hMu, focPi, focX, focI]
    ring
  unfold lagrangian
  rw [hpt, hinit, dsum_add hβ0.le hβ1 hS0b (((bdd_const _).mul (hGrb.add hCb)).add
      ((bdd_const _).mul hQb)), dsum_add hβ0.le hβ1 ((bdd_const _).mul (hGrb.add hCb))
      ((bdd_const _).mul hQb), dsum_mul_left, dsum_mul_left, dsum_add hβ0.le hβ1 hGrb hCb, hF,
    dsum_add hβ0.le hβ1 hGrb hMub, ← key]
  ring

/-- Woodford (2003), pp. 478–479: the unit sequence `e_s` (a perturbation of one date only). -/
def unitSeq (s : ℕ) : ℕ → ℝ := fun t => if t = s then 1 else 0

/-- Woodford (2003), pp. 478–479: the unit sequence is bounded. -/
theorem bdd_unitSeq (s : ℕ) : Bdd (unitSeq s) :=
  ⟨1, fun t => by unfold unitSeq; split_ifs <;> simp⟩

/-- Woodford (2003), pp. 478–479: `∑ βᵗ f_t (e_s)_t = βˢ f_s`. -/
theorem dsum_mul_unitSeq (β : ℝ) (f : ℕ → ℝ) (s : ℕ) :
    dsum β (fun t => f t * unitSeq s t) = β ^ s * f s := by
  unfold dsum unitSeq
  have h : (fun t => β ^ t * (f t * if t = s then (1 : ℝ) else 0)) =
      fun t => if t = s then β ^ s * f s else 0 := by
    funext t
    split_ifs with h
    · subst h; ring
    · ring
  rw [h, tsum_ite_eq]

/-- Woodford (2003), p. 478: the derivative at `ε = 0` of `L + εc + (ε²/2)Q` is `c`. -/
theorem hasDerivAt_quadratic (L c Q : ℝ) :
    HasDerivAt (fun ε : ℝ => L + ε * c + ε ^ 2 / 2 * Q) c 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).mul ((hasDerivAt_const (0 : ℝ) c).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (Q / 2)))).const_add L
  have hfun : (fun ε : ℝ => L + ε * c + ε ^ 2 / 2 * Q) =
      fun ε => L + id ε * ((fun _ => c) ε + id ε * (Q / 2)) := by
    funext ε
    simp only [id]
    ring
  rw [hfun]
  convert h using 1
  simp

/-- Woodford (2003), eq. (1.16), p. 478, as an exact derivative: for bounded plans and
multipliers, the derivative of the Lagrangian with respect to `π_s` is `βˢ` times the
left side of the inflation first-order condition (with `φ_{1,−1}`, `φ_{2,−1}` the
initial-constraint multipliers at `s = 0`). -/
theorem hasDerivAt_lagrangian_pi {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (s : ℕ) :
    HasDerivAt (fun ε => lagrangian M φ1 φ2 φ1m φ2m (fun t => π t + ε * unitSeq s t) x i)
      (M.β ^ s * focPi M φ1 φ2 φ1m φ2m π s) 0 := by
  have hfun : (fun ε => lagrangian M φ1 φ2 φ1m φ2m (fun t => π t + ε * unitSeq s t) x i) =
      fun ε => lagrangian M φ1 φ2 φ1m φ2m π x i + ε * (M.β ^ s * focPi M φ1 φ2 φ1m φ2m π s) +
        ε ^ 2 / 2 * dsum M.β (quad M (unitSeq s) (fun _ => 0) (fun _ => 0)) := by
    funext ε
    have h := lagrangian_expand hβ0 hβ1 φ1m φ2m ε h1 h2 hπ hx hi (bdd_unitSeq s) (bdd_const 0)
      (bdd_const 0)
    simp only [mul_zero, add_zero] at h
    rw [h, dsum_mul_unitSeq]
  rw [hfun]
  exact hasDerivAt_quadratic _ _ _

/-- Woodford (2003), eq. (1.17), p. 478, as an exact derivative: the derivative of the
Lagrangian with respect to `x_s` is `βˢ` times the left side of the output-gap FOC. -/
theorem hasDerivAt_lagrangian_x {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (s : ℕ) :
    HasDerivAt (fun ε => lagrangian M φ1 φ2 φ1m φ2m π (fun t => x t + ε * unitSeq s t) i)
      (M.β ^ s * focX M φ1 φ2 φ1m x s) 0 := by
  have hfun : (fun ε => lagrangian M φ1 φ2 φ1m φ2m π (fun t => x t + ε * unitSeq s t) i) =
      fun ε => lagrangian M φ1 φ2 φ1m φ2m π x i + ε * (M.β ^ s * focX M φ1 φ2 φ1m x s) +
        ε ^ 2 / 2 * dsum M.β (quad M (fun _ => 0) (unitSeq s) (fun _ => 0)) := by
    funext ε
    have h := lagrangian_expand hβ0 hβ1 φ1m φ2m ε h1 h2 hπ hx hi (bdd_const 0) (bdd_unitSeq s)
      (bdd_const 0)
    simp only [mul_zero, add_zero, zero_add] at h
    rw [h, dsum_mul_unitSeq]
  rw [hfun]
  exact hasDerivAt_quadratic _ _ _

/-- Woodford (2003), eq. (1.18), p. 478, as an exact derivative: the derivative of the
Lagrangian with respect to `i_s` is `βˢ` times the left side of the interest-rate FOC. -/
theorem hasDerivAt_lagrangian_i {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (s : ℕ) :
    HasDerivAt (fun ε => lagrangian M φ1 φ2 φ1m φ2m π x (fun t => i t + ε * unitSeq s t))
      (M.β ^ s * focI M φ1 φ2 φ1m i s) 0 := by
  have hfun : (fun ε => lagrangian M φ1 φ2 φ1m φ2m π x (fun t => i t + ε * unitSeq s t)) =
      fun ε => lagrangian M φ1 φ2 φ1m φ2m π x i + ε * (M.β ^ s * focI M φ1 φ2 φ1m i s) +
        ε ^ 2 / 2 * dsum M.β (quad M (fun _ => 0) (fun _ => 0) (unitSeq s)) := by
    funext ε
    have h := lagrangian_expand hβ0 hβ1 φ1m φ2m ε h1 h2 hπ hx hi (bdd_const 0) (bdd_const 0)
      (bdd_unitSeq s)
    simp only [mul_zero, add_zero, zero_add] at h
    rw [h, dsum_mul_unitSeq]
  rw [hfun]
  exact hasDerivAt_quadratic _ _ _

/-! ### Lagrangian sufficiency -/

/-- Woodford (2003), p. 478: for a feasible plan the constraint terms vanish, so the
Lagrangian is half the loss (1.14) minus the initial-constraint terms. -/
theorem lagrangian_of_feasible {M : Model} {φ1 φ2 π x i : ℕ → ℝ} (φ1m φ2m : ℝ)
    (hF : Feasible M π x i) :
    lagrangian M φ1 φ2 φ1m φ2m π x i =
      loss M π x i / 2 - M.β⁻¹ * initTerm M φ1m φ2m π x i := by
  have hz : (fun t => periodLoss M π x i t / 2 + φ1 t * resIS M π x i t +
      φ2 t * resAS M π x i t) = fun t => (1 / 2) * periodLoss M π x i t := by
    funext t
    have ha := (hF t).1
    have hb := (hF t).2
    unfold AS at ha
    unfold IS at hb
    have h1 : resIS M π x i t = 0 := by unfold resIS; linarith
    have h2 : resAS M π x i t = 0 := by unfold resAS; linarith
    rw [h1, h2]
    ring
  unfold lagrangian loss
  rw [hz, dsum_mul_left]
  ring

/-- Woodford (2003), §1.2, pp. 478–479 (Lagrangian sufficiency with three constraints): let
`(π, x, i)` be a bounded feasible plan and `φ₁, φ₂` bounded multipliers (with
initial-constraint multipliers `φ_{1,−1}, φ_{2,−1}`) such that the first-order conditions
(1.16)–(1.18) hold at every date. Then every bounded feasible plan `(π', x', i')` with the same
initial restrictions `π'_0 = π_0` and `a x'_0 + b i'_0 = a x_0 + b i_0` (in the basic model:
`x'_0 = x_0`) has loss
`loss(π', x', i') = loss(π, x, i) + ∑βᵗ[(π'−π)_t² + λ_x(x'−x)_t² + λ_i(i'−i)_t²]`. -/
theorem lagrangian_sufficiency {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i π' x' i' : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (hπ' : Bdd π') (hx' : Bdd x') (hi' : Bdd i')
    (hF : Feasible M π x i) (hF' : Feasible M π' x' i')
    (hfoc : ∀ t, focPi M φ1 φ2 φ1m φ2m π t = 0 ∧ focX M φ1 φ2 φ1m x t = 0 ∧
      focI M φ1 φ2 φ1m i t = 0)
    (h0 : π' 0 = π 0) (h0' : M.a * x' 0 + M.b * i' 0 = M.a * x 0 + M.b * i 0) :
    loss M π' x' i' = loss M π x i +
      dsum M.β (quad M (fun t => π' t - π t) (fun t => x' t - x t) (fun t => i' t - i t)) := by
  have h := lagrangian_expand hβ0 hβ1 φ1m φ2m 1 h1 h2 hπ hx hi (hπ'.sub hπ) (hx'.sub hx)
    (hi'.sub hi)
  have hy : ∀ u v : ℕ → ℝ, (fun t => v t + 1 * (u t - v t)) = u := fun u v => by
    funext t; ring
  rw [hy, hy, hy] at h
  have hz : (fun t => focPi M φ1 φ2 φ1m φ2m π t * (π' t - π t) +
      focX M φ1 φ2 φ1m x t * (x' t - x t) + focI M φ1 φ2 φ1m i t * (i' t - i t)) =
      fun _ => 0 := by
    funext t
    rw [(hfoc t).1, (hfoc t).2.1, (hfoc t).2.2]
    ring
  rw [hz, lagrangian_of_feasible φ1m φ2m hF', lagrangian_of_feasible φ1m φ2m hF] at h
  have hinit : initTerm M φ1m φ2m π' x' i' = initTerm M φ1m φ2m π x i := by
    unfold initTerm
    rw [h0]
    linear_combination φ1m * h0'
  have hd0 : dsum M.β (fun _ => (0 : ℝ)) = 0 := by simp [dsum]
  rw [hinit, hd0] at h
  linarith

/-- Woodford (2003), §1.2, pp. 478–479: under the hypotheses of `lagrangian_sufficiency`, with
`λ_x, λ_i ≥ 0` the plan satisfying the first-order conditions minimises the loss among bounded
feasible plans with the same initial restrictions. -/
theorem loss_le_of_foc {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) (hlx : 0 ≤ M.lamx)
    (hli : 0 ≤ M.lami) {φ1 φ2 π x i π' x' i' : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1)
    (h2 : Bdd φ2) (hπ : Bdd π) (hx : Bdd x) (hi : Bdd i) (hπ' : Bdd π') (hx' : Bdd x')
    (hi' : Bdd i') (hF : Feasible M π x i) (hF' : Feasible M π' x' i')
    (hfoc : ∀ t, focPi M φ1 φ2 φ1m φ2m π t = 0 ∧ focX M φ1 φ2 φ1m x t = 0 ∧
      focI M φ1 φ2 φ1m i t = 0)
    (h0 : π' 0 = π 0) (h0' : M.a * x' 0 + M.b * i' 0 = M.a * x 0 + M.b * i 0) :
    loss M π x i ≤ loss M π' x' i' := by
  rw [lagrangian_sufficiency hβ0 hβ1 φ1m φ2m h1 h2 hπ hx hi hπ' hx' hi' hF hF' hfoc h0 h0']
  linarith [dsum_nonneg hβ0.le (quad_nonneg hlx hli (fun t => π' t - π t)
    (fun t => x' t - x t) (fun t => i' t - i t))]

/-- Woodford (2003), §1.2, pp. 478–479 (uniqueness from strict convexity): with `λ_x, λ_i > 0`
a bounded feasible plan with the same initial restrictions and no larger loss than the plan
satisfying (1.16)–(1.18) coincides with it. -/
theorem eq_of_loss_le_of_foc {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) (hlx : 0 < M.lamx)
    (hli : 0 < M.lami) {φ1 φ2 π x i π' x' i' : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1)
    (h2 : Bdd φ2) (hπ : Bdd π) (hx : Bdd x) (hi : Bdd i) (hπ' : Bdd π') (hx' : Bdd x')
    (hi' : Bdd i') (hF : Feasible M π x i) (hF' : Feasible M π' x' i')
    (hfoc : ∀ t, focPi M φ1 φ2 φ1m φ2m π t = 0 ∧ focX M φ1 φ2 φ1m x t = 0 ∧
      focI M φ1 φ2 φ1m i t = 0)
    (h0 : π' 0 = π 0) (h0' : M.a * x' 0 + M.b * i' 0 = M.a * x 0 + M.b * i 0)
    (hle : loss M π' x' i' ≤ loss M π x i) : π' = π ∧ x' = x ∧ i' = i := by
  have h := lagrangian_sufficiency hβ0 hβ1 φ1m φ2m h1 h2 hπ hx hi hπ' hx' hi' hF hF' hfoc h0 h0'
  have hq := quad_nonneg hlx.le hli.le (fun t => π' t - π t) (fun t => x' t - x t)
    (fun t => i' t - i t)
  have hz : dsum M.β (quad M (fun t => π' t - π t) (fun t => x' t - x t)
      (fun t => i' t - i t)) = 0 := le_antisymm (by linarith) (dsum_nonneg hβ0.le hq)
  rw [dsum_eq_zero_iff hβ0 hβ1 (bdd_quad M (hπ'.sub hπ) (hx'.sub hx) (hi'.sub hi)) hq] at hz
  have hall : ∀ t, π' t - π t = 0 ∧ x' t - x t = 0 ∧ i' t - i t = 0 := by
    intro t
    have := hz t
    unfold quad at this
    have a1 := sq_nonneg (π' t - π t)
    have a2 := mul_nonneg hlx.le (sq_nonneg (x' t - x t))
    have a3 := mul_nonneg hli.le (sq_nonneg (i' t - i t))
    have e1 : (π' t - π t) ^ 2 = 0 := by linarith
    have e2 : M.lamx * (x' t - x t) ^ 2 = 0 := by linarith
    have e3 : M.lami * (i' t - i t) ^ 2 = 0 := by linarith
    refine ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1, ?_, ?_⟩
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp e2).resolve_left hlx.ne')
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
        ((mul_eq_zero.mp e3).resolve_left hli.ne')
  refine ⟨funext fun t => ?_, funext fun t => ?_, funext fun t => ?_⟩
  · linarith [(hall t).1]
  · linarith [(hall t).2.1]
  · linarith [(hall t).2.2]

/-! ### Constant plans and constant multipliers -/

/-- Woodford (2003), p. 477: a constant plan `(π̄, x̄, ı̄)` is feasible iff `ı̄ = r̄ + π̄` (the IS
relation (1.15)) and `κx̄ = (1 − β − κϕ)π̄` (the aggregate-supply relation; `x̄ = (1 − β)π̄/κ`
in the basic model). -/
theorem const_feasible_iff {M : Model} (hσ : M.σ ≠ 0) (πb xb ib : ℝ) :
    Feasible M (fun _ => πb) (fun _ => xb) (fun _ => ib) ↔
      ib = M.rbar + πb ∧ M.κ * xb = (1 - M.β - M.κ * M.ϕ) * πb := by
  constructor
  · intro h
    have ha := (h 0).1
    have hb := (h 0).2
    unfold AS at ha
    unfold IS at hb
    have hi : M.σ * (ib - πb - M.rbar) = 0 := by linarith
    have hi' : ib = M.rbar + πb := by
      have := (mul_eq_zero.mp hi).resolve_left hσ
      linarith
    refine ⟨hi', ?_⟩
    rw [hi'] at ha
    linarith
  · rintro ⟨hi, hx⟩ t
    refine ⟨?_, ?_⟩
    · unfold AS
      rw [hi]
      linarith
    · unfold IS
      rw [hi]
      ring

/-- Woodford (2003), p. 478: the condition on a stationary plan that the first-order
conditions (1.16)–(1.18) have constant multipliers,
`σ[λ_i(ı̄ − iᵐ) − ϕλ_x(x̄ − x*)] = π̄[(b − aϕ) − β(σ + b − aϕ)]`.
In the basic model (`ϕ = 0`, `a = 1`, `b = 0`) it reads `λ_i(ı̄ − iᵐ) = −βπ̄`. -/
def TimelessCond (M : Model) (πb xb ib : ℝ) : Prop :=
  M.σ * (M.lami * (ib - M.im) - M.ϕ * (M.lamx * (xb - M.xstar))) =
    πb * ((M.b - M.a * M.ϕ) - M.β * (M.σ + M.b - M.a * M.ϕ))

/-- Woodford (2003), p. 478: a stationary plan satisfies (1.16)–(1.18) at every date with
constant multipliers `φ_{1t} = φ_{1,−1} = c₁`, `φ_{2t} = φ_{2,−1} = c₂` if and only if
`TimelessCond` holds (`β, σ, κ ≠ 0`). The multipliers are then `c₁ = βπ̄/σ` and
`c₂ = (λ_x(x̄ − x*) + (1 − β⁻¹)a c₁)/κ`. -/
theorem foc_const_iff {M : Model} (hβ : M.β ≠ 0) (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0)
    (πb xb ib : ℝ) :
    (∃ c1 c2 : ℝ, ∀ t, focPi M (fun _ => c1) (fun _ => c2) c1 c2 (fun _ => πb) t = 0 ∧
      focX M (fun _ => c1) (fun _ => c2) c1 (fun _ => xb) t = 0 ∧
      focI M (fun _ => c1) (fun _ => c2) c1 (fun _ => ib) t = 0) ↔
      TimelessCond M πb xb ib := by
  constructor
  · rintro ⟨c1, c2, h⟩
    obtain ⟨hP, hX, hI⟩ := h 0
    simp only [focPi, focX, focI, multPi, multX, multI, lagged_const] at hP hX hI
    have hc1' : M.β⁻¹ * M.σ * c1 = πb := by linarith
    have hc : M.σ * c1 = M.β * πb := by
      rw [← hc1']
      field_simp
    unfold TimelessCond
    linear_combination M.σ * hI - M.σ * M.ϕ * hX - (M.σ + M.b - M.a * M.ϕ) * hc +
      (M.b - M.a * M.ϕ) * hc1'
  · intro hc
    refine ⟨M.β * πb / M.σ, (M.lamx * (xb - M.xstar) + (1 - M.β⁻¹) * M.a *
      (M.β * πb / M.σ)) / M.κ, fun t => ?_⟩
    simp only [focPi, focX, focI, multPi, multX, multI, lagged_const]
    unfold TimelessCond at hc
    refine ⟨?_, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring
    · field_simp
      linear_combination hc

/-- Woodford (2003), pp. 477–478 (precise definition): a stationary policy commitment with
constant inflation `π̄`, output gap `x̄` and interest rate `ı̄` is *optimal from a timeless
perspective* if the constant plan is feasible and, for every date `t₀`, it minimises the
discounted loss from `t₀` onward over all bounded plans satisfying (1.1) and (1.15) for every
`t ≥ t₀` subject to the initial constraints `π_{t₀} = π̄` and `a x_{t₀} + b i_{t₀} = a x̄ + b ı̄`
(in the basic model `x_{t₀} = x̄`, as on p. 477). -/
def TimelesslyOptimal (M : Model) (πb xb ib : ℝ) : Prop :=
  Feasible M (fun _ => πb) (fun _ => xb) (fun _ => ib) ∧
    ∀ (t0 : ℕ) (π x i : ℕ → ℝ), Bdd π → Bdd x → Bdd i →
      (∀ t, t0 ≤ t → AS M π x i t ∧ IS M π x i t) → π t0 = πb →
      M.a * x t0 + M.b * i t0 = M.a * xb + M.b * ib →
      loss M (fun _ => πb) (fun _ => xb) (fun _ => ib) ≤
        loss M (fun t => π (t0 + t)) (fun t => x (t0 + t)) (fun t => i (t0 + t))

/-- Woodford (2003), p. 477: a plan feasible from `t₀` on, shifted to start at date 0, is
feasible (the constraints are time-invariant). -/
theorem feasible_from {M : Model} {π x i : ℕ → ℝ} {t0 : ℕ}
    (h : ∀ t, t0 ≤ t → AS M π x i t ∧ IS M π x i t) :
    Feasible M (fun t => π (t0 + t)) (fun t => x (t0 + t)) (fun t => i (t0 + t)) :=
  fun t => h (t0 + t) (Nat.le_add_right t0 t)

/-- Woodford (2003), Proposition 7.3 (sufficiency half), pp. 478–479: a feasible stationary
plan satisfying `TimelessCond` is optimal from a timeless perspective (`0 < β < 1`,
`λ_x, λ_i ≥ 0`, `σ, κ ≠ 0`), by Lagrangian sufficiency with constant multipliers. -/
theorem timelesslyOptimal_of_cond {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hlx : 0 ≤ M.lamx) (hli : 0 ≤ M.lami) (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0) {πb xb ib : ℝ}
    (hF : Feasible M (fun _ => πb) (fun _ => xb) (fun _ => ib))
    (hc : TimelessCond M πb xb ib) : TimelesslyOptimal M πb xb ib := by
  obtain ⟨c1, c2, hfoc⟩ := (foc_const_iff hβ0.ne' hσ hκ πb xb ib).mpr hc
  refine ⟨hF, fun t0 π x i hπ hx hi hfeas h0 h0' => ?_⟩
  exact loss_le_of_foc hβ0 hβ1 hlx hli c1 c2 (bdd_const c1) (bdd_const c2) (bdd_const πb)
    (bdd_const xb) (bdd_const ib) (hπ.drop t0) (hx.drop t0) (hi.drop t0) hF
    (feasible_from hfeas) hfoc (by simpa using h0) (by simpa using h0')

/-- Woodford (2003), p. 478: with `λ_x, λ_i > 0` the timelessly optimal stationary plan is the
*unique* minimiser: a bounded plan feasible from `t₀` on with the same initial constraints and no
larger loss coincides with the constant plan from `t₀` on. -/
theorem timeless_unique {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hlx : 0 < M.lamx) (hli : 0 < M.lami) (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0) {πb xb ib : ℝ}
    (hF : Feasible M (fun _ => πb) (fun _ => xb) (fun _ => ib))
    (hc : TimelessCond M πb xb ib) (t0 : ℕ) {π x i : ℕ → ℝ} (hπ : Bdd π) (hx : Bdd x)
    (hi : Bdd i) (hfeas : ∀ t, t0 ≤ t → AS M π x i t ∧ IS M π x i t) (h0 : π t0 = πb)
    (h0' : M.a * x t0 + M.b * i t0 = M.a * xb + M.b * ib)
    (hle : loss M (fun t => π (t0 + t)) (fun t => x (t0 + t)) (fun t => i (t0 + t)) ≤
      loss M (fun _ => πb) (fun _ => xb) (fun _ => ib)) :
    ∀ t, t0 ≤ t → π t = πb ∧ x t = xb ∧ i t = ib := by
  obtain ⟨c1, c2, hfoc⟩ := (foc_const_iff hβ0.ne' hσ hκ πb xb ib).mpr hc
  have h := eq_of_loss_le_of_foc hβ0 hβ1 hlx hli c1 c2 (bdd_const c1) (bdd_const c2)
    (bdd_const πb) (bdd_const xb) (bdd_const ib) (hπ.drop t0) (hx.drop t0) (hi.drop t0) hF
    (feasible_from hfeas) hfoc (by simpa using h0) (by simpa using h0') hle
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact ⟨congrFun h.1 k, congrFun h.2.1 k, congrFun h.2.2 k⟩

/-! ### Necessity: a feasible perturbation -/

/-- Woodford (2003), (1.14), p. 476: the discounted sum of a sequence vanishing from date `N`
on is the finite sum `∑_{t < N} βᵗ f_t`. -/
theorem dsum_of_zero_from (β : ℝ) {f : ℕ → ℝ} (N : ℕ) (hf : ∀ t, N ≤ t → f t = 0) :
    dsum β f = ∑ t ∈ Finset.range N, β ^ t * f t := by
  unfold dsum
  refine tsum_eq_sum (fun t ht => ?_)
  rw [hf t (not_lt.mp (fun h => ht (Finset.mem_range.mpr h))), mul_zero]

/-- Woodford (2003), p. 478: the Lagrangian with zero multipliers is half the loss (1.14). -/
theorem lagrangian_zero (M : Model) (π x i : ℕ → ℝ) :
    lagrangian M (fun _ => 0) (fun _ => 0) 0 0 π x i = loss M π x i / 2 := by
  have h : (fun t => periodLoss M π x i t / 2 + (fun _ => (0 : ℝ)) t * resIS M π x i t +
      (fun _ => (0 : ℝ)) t * resAS M π x i t) = fun t => (1 / 2) * periodLoss M π x i t := by
    funext t
    ring
  unfold lagrangian loss initTerm
  rw [h, dsum_mul_left]
  ring

/-- Woodford (2003), (1.14), p. 476 (exact expansion of the loss): for bounded plans and
deviations, `loss(y + εd) = loss(y) + 2ε ∑βᵗ[π_t dπ_t + λ_x(x_t − x*)dx_t + λ_i(i_t − iᵐ)di_t]
+ ε² ∑βᵗ[dπ_t² + λ_x dx_t² + λ_i di_t²]`. -/
theorem loss_expand {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) {π x i dπ dx di : ℕ → ℝ}
    (ε : ℝ) (hπ : Bdd π) (hx : Bdd x) (hi : Bdd i) (hdp : Bdd dπ) (hdx : Bdd dx)
    (hdi : Bdd di) :
    loss M (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t) (fun t => i t + ε * di t) =
      loss M π x i + 2 * ε * dsum M.β (fun t => π t * dπ t +
        M.lamx * (x t - M.xstar) * dx t + M.lami * (i t - M.im) * di t) +
        ε ^ 2 * dsum M.β (quad M dπ dx di) := by
  have h := lagrangian_expand (φ1 := fun _ => 0) (φ2 := fun _ => 0) hβ0 hβ1 0 0 ε
    (bdd_const 0) (bdd_const 0) hπ hx hi hdp hdx hdi
  rw [lagrangian_zero, lagrangian_zero] at h
  have hF : (fun t => focPi M (fun _ => 0) (fun _ => 0) 0 0 π t * dπ t +
      focX M (fun _ => 0) (fun _ => 0) 0 x t * dx t +
      focI M (fun _ => 0) (fun _ => 0) 0 i t * di t) = fun t => π t * dπ t +
        M.lamx * (x t - M.xstar) * dx t + M.lami * (i t - M.im) * di t := by
    funext t
    simp only [focPi, focX, focI, multPi, multX, multI, lagged_const]
    ring
  rw [hF] at h
  linarith

/-- Woodford (2003), p. 478: a feasible plan plus any multiple of a deviation satisfying the
homogeneous constraints is feasible. -/
theorem feasible_add {M : Model} {π x i dπ dx di : ℕ → ℝ} (hF : Feasible M π x i)
    (hd : ∀ t, homAS M dπ dx di t = 0 ∧ homIS M dπ dx di t = 0) (ε : ℝ) :
    Feasible M (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
      (fun t => i t + ε * di t) := by
  intro t
  have ha := (hF t).1
  have hb := (hF t).2
  have hda := (hd t).1
  have hdb := (hd t).2
  unfold AS at ha ⊢
  unfold IS at hb ⊢
  unfold homAS at hda
  unfold homIS at hdb
  constructor
  · linear_combination ha + ε * hda
  · linear_combination hb + ε * hdb

/-- Woodford (2003), p. 478 (a feasible test deviation): the inflation component of a
deviation supported on dates 1–3 that satisfies the homogeneous constraints and the initial
constraints. With `p = b − aϕ`, `q = σ + b − aϕ`: `dπ_2 = κp`, `dπ_3 = −κq`. -/
def pertPi (M : Model) (t : ℕ) : ℝ :=
  if t = 2 then M.κ * (M.b - M.a * M.ϕ) else
    if t = 3 then -(M.κ * (M.σ + M.b - M.a * M.ϕ)) else 0

/-- Woodford (2003), p. 478: the output-gap component of the test deviation. -/
def pertX (M : Model) (t : ℕ) : ℝ :=
  if t = 1 then -(M.β * (M.b - M.a * M.ϕ)) - M.ϕ * M.a * M.β else
    if t = 2 then (M.b - M.a * M.ϕ) + M.β * (M.σ + M.b - M.a * M.ϕ) + M.ϕ * M.σ * M.κ +
      M.ϕ * M.a * (1 + M.β) else
      if t = 3 then -(M.σ + M.b - M.a * M.ϕ) - M.ϕ * M.a else 0

/-- Woodford (2003), p. 478: the interest-rate component of the test deviation. -/
def pertI (M : Model) (t : ℕ) : ℝ :=
  if t = 1 then M.a * M.β else
    if t = 2 then -(M.σ * M.κ) - M.a * (1 + M.β) else
      if t = 3 then M.a else 0

/-- Woodford (2003), p. 478: the test deviation satisfies the homogeneous aggregate-supply and
IS relations at every date. -/
theorem pert_hom (M : Model) (t : ℕ) :
    homAS M (pertPi M) (pertX M) (pertI M) t = 0 ∧
      homIS M (pertPi M) (pertX M) (pertI M) t = 0 := by
  rcases t with _ | _ | _ | _ | n
  · simp [homAS, homIS, pertPi, pertX, pertI]
    ring
  · simp [homAS, homIS, pertPi, pertX, pertI]
    constructor <;> ring
  · simp [homAS, homIS, pertPi, pertX, pertI]
    constructor <;> ring
  · simp [homAS, homIS, pertPi, pertX, pertI]
    constructor <;> ring
  · have h1 : n + 1 + 1 + 1 + 1 ≠ 1 := by omega
    have h2 : n + 1 + 1 + 1 + 1 ≠ 2 := by omega
    have h3 : n + 1 + 1 + 1 + 1 ≠ 3 := by omega
    have h1' : n + 1 + 1 + 1 + 1 + 1 ≠ 1 := by omega
    have h2' : n + 1 + 1 + 1 + 1 + 1 ≠ 2 := by omega
    have h3' : n + 1 + 1 + 1 + 1 + 1 ≠ 3 := by omega
    simp only [homAS, homIS, pertPi, pertX, pertI, h1, h2, h3, h1', h2', h3', ↓reduceIte]
    constructor <;> ring

/-- Woodford (2003), p. 478: the test deviation vanishes from date 4 on. -/
theorem pert_zero_from (M : Model) (t : ℕ) (ht : 4 ≤ t) :
    pertPi M t = 0 ∧ pertX M t = 0 ∧ pertI M t = 0 := by
  have h1 : t ≠ 1 := by omega
  have h2 : t ≠ 2 := by omega
  have h3 : t ≠ 3 := by omega
  simp [pertPi, pertX, pertI, h1, h2, h3]

/-- Woodford (2003), p. 478: the first-order change in the loss along the test deviation from a
constant plan, `∑βᵗ[π̄ dπ_t + λ_x(x̄ − x*)dx_t + λ_i(ı̄ − iᵐ)di_t]
= β²κ{π̄[(b − aϕ) − β(σ + b − aϕ)] − σ[λ_i(ı̄ − iᵐ) − ϕλ_x(x̄ − x*)]}`. -/
theorem dsum_pert (M : Model) (πb xb ib : ℝ) :
    dsum M.β (fun t => πb * pertPi M t + M.lamx * (xb - M.xstar) * pertX M t +
      M.lami * (ib - M.im) * pertI M t) =
      M.β ^ 2 * M.κ * (πb * ((M.b - M.a * M.ϕ) - M.β * (M.σ + M.b - M.a * M.ϕ)) -
        M.σ * (M.lami * (ib - M.im) - M.ϕ * (M.lamx * (xb - M.xstar)))) := by
  rw [dsum_of_zero_from M.β 4 (fun t ht => by
    obtain ⟨a, b, c⟩ := pert_zero_from M t ht
    rw [a, b, c]; ring)]
  simp [Finset.sum_range_succ, pertPi, pertX, pertI]
  ring

/-- Woodford (2003), p. 478: if `0 ≤ 2εG + ε²Q` for every real `ε`, then `G = 0` (a minimum
along a line has zero directional derivative). -/
theorem eq_zero_of_forall_nonneg {G Q : ℝ} (h : ∀ ε : ℝ, 0 ≤ 2 * ε * G + ε ^ 2 * Q) :
    G = 0 := by
  have hA : 0 < |Q| + 1 := by positivity
  have h1 := h (-G / (|Q| + 1))
  have hQ : Q ≤ |Q| := le_abs_self Q
  have h2 : 0 ≤ G ^ 2 * (Q - 2 * (|Q| + 1)) := by
    have e : 2 * (-G / (|Q| + 1)) * G + (-G / (|Q| + 1)) ^ 2 * Q =
        G ^ 2 * (Q - 2 * (|Q| + 1)) / (|Q| + 1) ^ 2 := by
      field_simp
      ring
    rw [e] at h1
    exact (div_nonneg_iff.mp h1).elim (fun h => h.1) (fun h => by
      nlinarith [h.2, sq_nonneg (|Q| + 1), h.1])
  have h3 : G ^ 2 ≤ 0 := by nlinarith [sq_nonneg G, abs_nonneg Q]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h3 (sq_nonneg G))

/-- Woodford (2003), Proposition 7.3 (necessity half), p. 478: if a stationary plan is optimal
from a timeless perspective then `TimelessCond` holds (`0 < β < 1`, `σ, κ ≠ 0`). The proof
perturbs the constant plan along the feasible test deviation `pertPi, pertX, pertI`. -/
theorem cond_of_timelesslyOptimal {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hκ : M.κ ≠ 0) {πb xb ib : ℝ} (h : TimelesslyOptimal M πb xb ib) :
    TimelessCond M πb xb ib := by
  have hb0 := pert_zero_from M
  have hbp : Bdd (pertPi M) := bdd_of_zero_from 4 (fun t ht => (hb0 t ht).1)
  have hbx : Bdd (pertX M) := bdd_of_zero_from 4 (fun t ht => (hb0 t ht).2.1)
  have hbi : Bdd (pertI M) := bdd_of_zero_from 4 (fun t ht => (hb0 t ht).2.2)
  have hall : ∀ ε : ℝ, 0 ≤ 2 * ε * dsum M.β (fun t => πb * pertPi M t +
      M.lamx * (xb - M.xstar) * pertX M t + M.lami * (ib - M.im) * pertI M t) +
      ε ^ 2 * dsum M.β (quad M (pertPi M) (pertX M) (pertI M)) := by
    intro ε
    have hfe := feasible_add h.1 (pert_hom M) ε
    have hle := h.2 0 (fun t => πb + ε * pertPi M t) (fun t => xb + ε * pertX M t)
      (fun t => ib + ε * pertI M t) ((bdd_const _).add ((bdd_const _).mul hbp))
      ((bdd_const _).add ((bdd_const _).mul hbx)) ((bdd_const _).add ((bdd_const _).mul hbi))
      (fun t _ => hfe t) (by simp [pertPi]) (by simp [pertX, pertI])
    simp only [zero_add] at hle
    rw [loss_expand hβ0 hβ1 ε (bdd_const πb) (bdd_const xb) (bdd_const ib) hbp hbx hbi] at hle
    linarith
  have hG := eq_zero_of_forall_nonneg hall
  rw [dsum_pert] at hG
  have hne : M.β ^ 2 * M.κ ≠ 0 := mul_ne_zero (pow_ne_zero 2 hβ0.ne') hκ
  have := (mul_eq_zero.mp hG).resolve_left hne
  unfold TimelessCond
  linarith

/-- Woodford (2003), Proposition 7.3 (general form, pp. 478–480): a stationary plan is optimal
from a timeless perspective if and only if it is feasible and satisfies `TimelessCond`
(`0 < β < 1`, `λ_x, λ_i ≥ 0`, `σ, κ ≠ 0`). -/
theorem timelesslyOptimal_iff {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hlx : 0 ≤ M.lamx) (hli : 0 ≤ M.lami) (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0) (πb xb ib : ℝ) :
    TimelesslyOptimal M πb xb ib ↔
      Feasible M (fun _ => πb) (fun _ => xb) (fun _ => ib) ∧ TimelessCond M πb xb ib :=
  ⟨fun h => ⟨h.1, cond_of_timelesslyOptimal hβ0 hβ1 hκ h⟩,
    fun h => timelesslyOptimal_of_cond hβ0 hβ1 hlx hli hσ hκ h.1 h.2⟩

/-! ### The optimal long-run inflation rate in closed form -/

/-- Woodford (2003), (1.19)–(1.20), pp. 478–479: the denominator
`λ_i + β − (1 − β)(b − aϕ)/σ − (1 − β)ϕλ_x/κ + ϕ²λ_x`. -/
noncomputable def denom (M : Model) : ℝ :=
  M.lami + M.β - (1 - M.β) * (M.b - M.a * M.ϕ) / M.σ - (1 - M.β) * M.ϕ * M.lamx / M.κ +
    M.ϕ ^ 2 * M.lamx

/-- Woodford (2003), (1.19)–(1.20), pp. 478–479: the timelessly optimal inflation rate
`π̄ = −[λ_i(r̄ − iᵐ) + ϕλ_x x*]/denom`. -/
noncomputable def piBar (M : Model) : ℝ :=
  -(M.lami * (M.rbar - M.im) + M.ϕ * M.lamx * M.xstar) / denom M

/-- Woodford (2003), pp. 478–479: a feasible stationary plan satisfies `TimelessCond` iff
`π̄ = piBar`, `ı̄ = r̄ + π̄` and `κx̄ = (1 − β − κϕ)π̄` (`σ, κ ≠ 0`, `denom ≠ 0`). -/
theorem stationary_iff {M : Model} (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0) (hD : denom M ≠ 0)
    (πb xb ib : ℝ) :
    (Feasible M (fun _ => πb) (fun _ => xb) (fun _ => ib) ∧ TimelessCond M πb xb ib) ↔
      πb = piBar M ∧ ib = M.rbar + πb ∧ M.κ * xb = (1 - M.β - M.κ * M.ϕ) * πb := by
  rw [const_feasible_iff hσ]
  have key : ∀ xb ib, ib = M.rbar + πb → M.κ * xb = (1 - M.β - M.κ * M.ϕ) * πb →
      (TimelessCond M πb xb ib ↔ πb = piBar M) := by
    intro xb ib hi hx
    have hxb : xb = (1 - M.β - M.κ * M.ϕ) * πb / M.κ := by
      field_simp
      linarith
    have hident : M.σ * (M.lami * (ib - M.im) - M.ϕ * (M.lamx * (xb - M.xstar))) -
        πb * ((M.b - M.a * M.ϕ) - M.β * (M.σ + M.b - M.a * M.ϕ)) =
        M.σ * ((M.lami * (M.rbar - M.im) + M.ϕ * M.lamx * M.xstar) + πb * denom M) := by
      rw [hi, hxb]
      unfold denom
      field_simp
      ring
    unfold TimelessCond piBar
    rw [eq_div_iff hD]
    constructor
    · intro h
      have h0 : M.σ * ((M.lami * (M.rbar - M.im) + M.ϕ * M.lamx * M.xstar) +
          πb * denom M) = 0 := by rw [← hident, h, sub_self]
      have := (mul_eq_zero.mp h0).resolve_left hσ
      linarith
    · intro h
      have h0 : M.σ * ((M.lami * (M.rbar - M.im) + M.ϕ * M.lamx * M.xstar) +
          πb * denom M) = 0 := by
        rw [show (M.lami * (M.rbar - M.im) + M.ϕ * M.lamx * M.xstar) + πb * denom M = 0 by
          linarith, mul_zero]
      linarith
  constructor
  · rintro ⟨⟨hi, hx⟩, hc⟩
    exact ⟨(key xb ib hi hx).mp hc, hi, hx⟩
  · rintro ⟨hp, hi, hx⟩
    exact ⟨⟨hi, hx⟩, (key xb ib hi hx).mpr hp⟩

/-- Woodford (2003), Proposition 7.3 in general form (pp. 478–480): the stationary plan
`(π̄, x̄, ı̄)` is optimal from a timeless perspective iff `π̄ = piBar`, `ı̄ = r̄ + π̄` and
`κx̄ = (1 − β − κϕ)π̄` (`0 < β < 1`, `λ_x, λ_i ≥ 0`, `σ, κ ≠ 0`, `denom ≠ 0`). -/
theorem timelesslyOptimal_iff_piBar {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hlx : 0 ≤ M.lamx) (hli : 0 ≤ M.lami) (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0)
    (hD : denom M ≠ 0) (πb xb ib : ℝ) :
    TimelesslyOptimal M πb xb ib ↔
      πb = piBar M ∧ ib = M.rbar + πb ∧ M.κ * xb = (1 - M.β - M.κ * M.ϕ) * πb := by
  rw [timelesslyOptimal_iff hβ0 hβ1 hlx hli hσ hκ, stationary_iff hσ hκ hD]

/-! ### The basic model with transactions frictions: (1.14)–(1.19) and Proposition 7.3 -/

/-- Woodford (2003), (1.1), (1.14), (1.15), pp. 469–477: the model with transactions frictions
but no real-balance effects (`ϕ = 0`, `a = 1`, `b = 0`). -/
def basic (β κ σ rbar lamx lami xstar im : ℝ) : Model :=
  { β := β, κ := κ, σ := σ, ϕ := 0, a := 1, b := 0, rbar := rbar, lamx := lamx, lami := lami,
    xstar := xstar, im := im }

/-- Woodford (2003), eq. (1.1), p. 469: in the basic model the aggregate-supply relation is
`π_t = κx_t + βπ_{t+1}`. -/
theorem basic_AS_iff (β κ σ rbar lamx lami xstar im : ℝ) (π x i : ℕ → ℝ) (t : ℕ) :
    AS (basic β κ σ rbar lamx lami xstar im) π x i t ↔ π t = κ * x t + β * π (t + 1) := by
  simp [AS, basic]

/-- Woodford (2003), eq. (1.15), p. 477: in the basic model the IS relation is
`x_t = x_{t+1} − σ(i_t − π_{t+1} − r̄)`. -/
theorem basic_IS_iff (β κ σ rbar lamx lami xstar im : ℝ) (π x i : ℕ → ℝ) (t : ℕ) :
    IS (basic β κ σ rbar lamx lami xstar im) π x i t ↔
      x t = x (t + 1) - σ * (i t - π (t + 1) - rbar) := by
  simp [IS, basic]

/-- Woodford (2003), eq. (1.16), p. 478: in the basic model the inflation FOC is
`π_t − β⁻¹σφ_{1,t−1} + φ_{2t} − φ_{2,t−1} = 0`. -/
theorem basic_foc_116 (β κ σ rbar lamx lami xstar im : ℝ) (φ1 φ2 : ℕ → ℝ) (φ1m φ2m : ℝ)
    (π : ℕ → ℝ) (t : ℕ) :
    focPi (basic β κ σ rbar lamx lami xstar im) φ1 φ2 φ1m φ2m π t =
      π t - β⁻¹ * σ * lagged φ1m φ1 t + φ2 t - lagged φ2m φ2 t := by
  simp only [focPi, multPi, basic]
  ring

/-- Woodford (2003), eq. (1.17), p. 478: in the basic model the output-gap FOC is
`λ_x(x_t − x*) + φ_{1t} − β⁻¹φ_{1,t−1} − κφ_{2t} = 0`. -/
theorem basic_foc_117 (β κ σ rbar lamx lami xstar im : ℝ) (φ1 φ2 : ℕ → ℝ) (φ1m : ℝ)
    (x : ℕ → ℝ) (t : ℕ) :
    focX (basic β κ σ rbar lamx lami xstar im) φ1 φ2 φ1m x t =
      lamx * (x t - xstar) + φ1 t - β⁻¹ * lagged φ1m φ1 t - κ * φ2 t := by
  simp only [focX, multX, basic]
  ring

/-- Woodford (2003), eq. (1.18), p. 478: in the basic model the interest-rate FOC is
`λ_i(i_t − iᵐ) + σφ_{1t} = 0`. -/
theorem basic_foc_118 (β κ σ rbar lamx lami xstar im : ℝ) (φ1 φ2 : ℕ → ℝ) (φ1m : ℝ)
    (i : ℕ → ℝ) (t : ℕ) :
    focI (basic β κ σ rbar lamx lami xstar im) φ1 φ2 φ1m i t =
      lami * (i t - im) + σ * φ1 t := by
  simp only [focI, multI, basic]
  ring

/-- Woodford (2003), p. 478: in the basic model `TimelessCond` is `λ_i(ı̄ − iᵐ) = −βπ̄`. -/
theorem basic_cond_iff {β κ σ rbar lamx lami xstar im : ℝ} (hσ : σ ≠ 0) (πb xb ib : ℝ) :
    TimelessCond (basic β κ σ rbar lamx lami xstar im) πb xb ib ↔
      lami * (ib - im) = -(β * πb) := by
  unfold TimelessCond basic
  simp only
  constructor
  · intro h
    have h' : σ * (lami * (ib - im) + β * πb) = 0 := by linarith
    have := (mul_eq_zero.mp h').resolve_left hσ
    linarith
  · intro h
    rw [h]
    ring

/-- Woodford (2003), p. 478: "(1.17) and (1.18) have a solution with the output gap and
interest rate constant only if both multipliers are constant; substituting constant values in
(1.16) and (1.18) … only if `λ_i(ı̄ − iᵐ) = −βπ̄`". Precisely: if the constant plan satisfies
(1.16)–(1.18) at every date for *some* multiplier sequences (and any initial multipliers), then
`φ_1` is constant, `φ_2` is constant from date 1 on, and `λ_i(ı̄ − iᵐ) = −βπ̄`. -/
theorem basic_const_foc {β κ σ rbar lamx lami xstar im : ℝ} (hβ : β ≠ 0) (hσ : σ ≠ 0)
    (hκ : κ ≠ 0) {φ1 φ2 : ℕ → ℝ} {φ1m φ2m πb xb ib : ℝ}
    (h : ∀ t, focPi (basic β κ σ rbar lamx lami xstar im) φ1 φ2 φ1m φ2m (fun _ => πb) t = 0 ∧
      focX (basic β κ σ rbar lamx lami xstar im) φ1 φ2 φ1m (fun _ => xb) t = 0 ∧
      focI (basic β κ σ rbar lamx lami xstar im) φ1 φ2 φ1m (fun _ => ib) t = 0) :
    (∀ t, φ1 t = φ1 0) ∧ (∀ t, φ2 (t + 1) = φ2 1) ∧ lami * (ib - im) = -(β * πb) := by
  have hI : ∀ t, lami * (ib - im) + σ * φ1 t = 0 := fun t => by
    have := (h t).2.2
    rwa [basic_foc_118] at this
  have h1 : ∀ t, φ1 t = φ1 0 := fun t => by
    have a := hI t
    have b := hI 0
    have : σ * (φ1 t - φ1 0) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hσ
    linarith
  have h2 : ∀ t, φ2 (t + 1) = φ2 1 := fun t => by
    have a := (h (t + 1)).2.1
    have b := (h 1).2.1
    rw [basic_foc_117] at a b
    simp only [lagged_succ] at a b
    rw [h1 (t + 1), h1 t] at a
    rw [h1 1, h1 0] at b
    have : κ * (φ2 (t + 1) - φ2 1) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hκ
    linarith
  refine ⟨h1, h2, ?_⟩
  have hP := (h 2).1
  rw [basic_foc_116] at hP
  simp only [lagged_succ] at hP
  rw [h2 1, h1 1] at hP
  have hπ : πb = β⁻¹ * σ * φ1 0 := by linarith
  have hb : β * πb = σ * φ1 0 := by rw [hπ]; field_simp
  linarith [hI 0]

/-- Woodford (2003), eq. (1.19), p. 478: `λ_i(ı̄ − iᵐ) = −βπ̄` and `ı̄ = r̄ + π̄` hold jointly iff
`π̄ = −λ_i/(λ_i + β)·(r̄ − iᵐ)` and `ı̄ = r̄ + π̄` (`λ_i ≥ 0`, `β > 0`). -/
theorem eq_1_19 {β lami rbar im : ℝ} (hβ : 0 < β) (hli : 0 ≤ lami) (πb ib : ℝ) :
    (lami * (ib - im) = -(β * πb) ∧ ib = rbar + πb) ↔
      (πb = -(lami / (lami + β)) * (rbar - im) ∧ ib = rbar + πb) := by
  have hd : lami + β ≠ 0 := by positivity
  constructor
  · rintro ⟨h, hi⟩
    refine ⟨?_, hi⟩
    rw [hi] at h
    field_simp
    linarith
  · rintro ⟨h, hi⟩
    refine ⟨?_, hi⟩
    rw [hi, h]
    field_simp
    ring

/-- Woodford (2003), (1.19): in the basic model `denom = λ_i + β`. -/
theorem denom_basic (β κ σ rbar lamx lami xstar im : ℝ) :
    denom (basic β κ σ rbar lamx lami xstar im) = lami + β := by
  simp [denom, basic]

/-- Woodford (2003), eq. (1.19), p. 478: in the basic model
`piBar = −λ_i/(λ_i + β)·(r̄ − iᵐ)`. -/
theorem piBar_basic (β κ σ rbar lamx lami xstar im : ℝ) :
    piBar (basic β κ σ rbar lamx lami xstar im) = -(lami / (lami + β)) * (rbar - im) := by
  rw [piBar, denom_basic]
  simp only [basic]
  ring

/-- Woodford (2003), **Proposition 7.3**, pp. 478–479 (exact LQ form): in the economy with
transactions frictions — loss (1.14), constraints (1.1) and (1.15) — the stationary plan
`(π̄, x̄, ı̄)` is optimal from a timeless perspective if and only if
`π̄ = −λ_i/(λ_i + β)·(r̄ − iᵐ)` (eq. (1.19)), `ı̄ = r̄ + π̄` and `x̄ = (1 − β)π̄/κ`
(`0 < β < 1`, `κ > 0`, `σ > 0`, `λ_x, λ_i ≥ 0`). -/
theorem prop_7_3 {β κ σ rbar lamx lami xstar im : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lamx) (hli : 0 ≤ lami) (πb xb ib : ℝ) :
    TimelesslyOptimal (basic β κ σ rbar lamx lami xstar im) πb xb ib ↔
      πb = -(lami / (lami + β)) * (rbar - im) ∧ ib = rbar + πb ∧
        xb = (1 - β) * πb / κ := by
  have hD : denom (basic β κ σ rbar lamx lami xstar im) ≠ 0 := by
    rw [denom_basic]; positivity
  rw [timelesslyOptimal_iff_piBar (M := basic β κ σ rbar lamx lami xstar im) hβ0 hβ1 hlx hli
    hσ.ne' hκ.ne' hD, piBar_basic]
  simp only [basic, mul_zero, sub_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by field_simp; linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [h3]; field_simp⟩

/-- Woodford (2003), Proposition 7.3 (uniqueness, p. 477 "are given by"): with `λ_x, λ_i > 0`
the timelessly optimal plan of (1.19) is the unique minimiser: any bounded plan satisfying
(1.1) and (1.15) from `t₀` on with `π_{t₀} = π̄`, `x_{t₀} = x̄` and no larger loss is the
constant plan from `t₀` on. -/
theorem prop_7_3_unique {β κ σ rbar lamx lami xstar im : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lamx) (hli : 0 < lami) {πb xb ib : ℝ}
    (hopt : TimelesslyOptimal (basic β κ σ rbar lamx lami xstar im) πb xb ib) (t0 : ℕ)
    {π x i : ℕ → ℝ} (hπ : Bdd π) (hx : Bdd x) (hi : Bdd i)
    (hfeas : ∀ t, t0 ≤ t → AS (basic β κ σ rbar lamx lami xstar im) π x i t ∧
      IS (basic β κ σ rbar lamx lami xstar im) π x i t)
    (h0 : π t0 = πb) (h0' : x t0 = xb)
    (hle : loss (basic β κ σ rbar lamx lami xstar im) (fun t => π (t0 + t))
      (fun t => x (t0 + t)) (fun t => i (t0 + t)) ≤
      loss (basic β κ σ rbar lamx lami xstar im) (fun _ => πb) (fun _ => xb) (fun _ => ib)) :
    ∀ t, t0 ≤ t → π t = πb ∧ x t = xb ∧ i t = ib :=
  timeless_unique (M := basic β κ σ rbar lamx lami xstar im) hβ0 hβ1 hlx hli hσ.ne' hκ.ne'
    hopt.1 (cond_of_timelesslyOptimal hβ0 hβ1 hκ.ne' hopt) t0 hπ hx hi hfeas h0
    (by simp [basic, h0']) hle

/-- Woodford (2003), p. 479: with `λ_i > 0` and `iᵐ < r̄` the optimal inflation target (1.19) is
negative. -/
theorem piBar_119_neg {β lami rbar im : ℝ} (hβ : 0 < β) (hli : 0 < lami) (him : im < rbar) :
    -(lami / (lami + β)) * (rbar - im) < 0 := by
  have : 0 < lami / (lami + β) * (rbar - im) := by
    apply mul_pos (div_pos hli (by linarith)) (by linarith)
  linarith

/-- Woodford (2003), p. 479: with sticky prices (`λ_i` finite) the deflation is more moderate
than the Friedman rate, `−(r̄ − iᵐ) < π̄`, so that `ı̄ = r̄ + π̄ > iᵐ`. -/
theorem piBar_119_gt_friedman {β lami rbar im : ℝ} (hβ : 0 < β) (hli : 0 ≤ lami)
    (him : im < rbar) :
    -(rbar - im) < -(lami / (lami + β)) * (rbar - im) ∧
      im < rbar + -(lami / (lami + β)) * (rbar - im) := by
  have hd : 0 < lami + β := by linarith
  have e : rbar + -(lami / (lami + β)) * (rbar - im) - im = β / (lami + β) * (rbar - im) := by
    field_simp
    ring
  have hp : 0 < β / (lami + β) * (rbar - im) := mul_pos (div_pos hβ hd) (by linarith)
  constructor <;> linarith

/-- Woodford (2003), p. 479 (flexible-price limit): as `λ_i → ∞` the optimal inflation rate
(1.19) tends to the Friedman rate `−(r̄ − iᵐ)`. -/
theorem tendsto_piBar_119_atTop {β : ℝ} (hβ : 0 < β) (rbar im : ℝ) :
    Tendsto (fun lami : ℝ => -(lami / (lami + β)) * (rbar - im)) atTop
      (𝓝 (-(rbar - im))) := by
  have h1 : Tendsto (fun lami : ℝ => β / (lami + β)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id)
  have h2 : Tendsto (fun lami : ℝ => -(1 - β / (lami + β)) * (rbar - im)) atTop
      (𝓝 (-(1 - 0) * (rbar - im))) :=
    ((tendsto_const_nhds.sub h1).neg).mul_const _
  rw [show -(1 - (0 : ℝ)) * (rbar - im) = -(rbar - im) by ring] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with l hl
  have : l + β ≠ 0 := by linarith
  field_simp
  ring

/-- Woodford (2003), p. 479 (cashless limit): as `λ_i → 0` the optimal inflation rate (1.19)
tends to zero, the result of §1.1. -/
theorem tendsto_piBar_119_zero {β : ℝ} (hβ : 0 < β) (rbar im : ℝ) :
    Tendsto (fun lami : ℝ => -(lami / (lami + β)) * (rbar - im)) (𝓝 0) (𝓝 0) := by
  have h : Tendsto (fun lami : ℝ => -(lami / (lami + β)) * (rbar - im)) (𝓝 0)
      (𝓝 (-((0 : ℝ) / (0 + β)) * (rbar - im))) :=
    ((tendsto_id.div (tendsto_id.add tendsto_const_nhds)
      (by simp only [zero_add]; exact hβ.ne')).neg).mul_const _
  simpa using h

/-! ### Real-balance effects: eq. (1.20) -/

/-- Woodford (2003), Ch. 6 eq. (4.3), p. 420 (= Ch. 4 `ε_mc`):
`ε_mc = σ⁻¹ + ω − χη_y`. -/
noncomputable def epsMC (σ ω χ ηy : ℝ) : ℝ := σ⁻¹ + ω - χ * ηy

/-- Woodford (2003), Ch. 6 eq. (4.4), p. 420: the real-balance coefficient
`ϕ = η_iχ/ε_mc`. -/
noncomputable def phiRB (σ ω χ ηy ηi : ℝ) : ℝ := ηi * χ / epsMC σ ω χ ηy

/-- Woodford (2003), p. 479 with Ch. 4 §3.2 and Ch. 6 §4.1: the model with real-balance effects,
`ϕ = η_iχ/ε_mc`, `a = 1 − ση_yχ`, `b = ση_iχ` (with constant interest `iᵐ` on money). -/
noncomputable def rbModel (β κ σ ω χ ηy ηi rbar lamx lami xstar im : ℝ) : Model :=
  { β := β, κ := κ, σ := σ, ϕ := phiRB σ ω χ ηy ηi, a := 1 - σ * ηy * χ, b := σ * ηi * χ,
    rbar := rbar, lamx := lamx, lami := lami, xstar := xstar, im := im }

/-- Woodford (2003), Ch. 4 eq. (3.14), p. 304 = Ch. 6 eq. (4.8), p. 421 (restated from the
Chapter 4 project, perfect foresight): `π_t = κ[x_t + ϕ(î_t − îᵐ_t)] + βπ_{t+1}`. -/
def AS314 (κ ϕ β : ℝ) (x π ih imh : ℕ → ℝ) (t : ℕ) : Prop :=
  π t = κ * (x t + ϕ * (ih t - imh t)) + β * π (t + 1)

/-- Woodford (2003), Ch. 4 eq. (3.10), p. 302 (restated from the Chapter 4 project, perfect
foresight): `(1 − ση_yχ)x_t = (1 − ση_yχ)x_{t+1} − σ(î_t − π_{t+1} − r̂ⁿ_t)
+ ση_iχ[(î_{t+1} − îᵐ_{t+1}) − (î_t − îᵐ_t)]`. -/
def IS310 (σ ηy ηi χ : ℝ) (x π ih imh rn : ℕ → ℝ) (t : ℕ) : Prop :=
  (1 - σ * ηy * χ) * x t = (1 - σ * ηy * χ) * x (t + 1) - σ * (ih t - π (t + 1) - rn t) +
    σ * ηi * χ * ((ih (t + 1) - imh (t + 1)) - (ih t - imh t))

/-- Woodford (2003), p. 477 fn 11 and Ch. 6 (4.8): in Chapter 7 notation the hatted differential
is `î_t − îᵐ_t = i_t − r̄` (deviation from the zero-inflation steady state with constant `iᵐ`), so
the aggregate-supply relation of `rbModel` is exactly (3.14)/(4.8). -/
theorem rb_AS_iff (β κ σ ω χ ηy ηi rbar lamx lami xstar im : ℝ) (π x i : ℕ → ℝ) (t : ℕ) :
    AS (rbModel β κ σ ω χ ηy ηi rbar lamx lami xstar im) π x i t ↔
      AS314 κ (phiRB σ ω χ ηy ηi) β x π (fun t => i t - rbar) (fun _ => 0) t := by
  unfold AS AS314 rbModel
  simp only [sub_zero]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 477 and Ch. 4 (3.10): with `î_t = i_t − r̄`, constant `iᵐ` (`îᵐ = 0`) and
no disturbances (`r̂ⁿ = 0`), the IS relation of `rbModel` is exactly (3.10). -/
theorem rb_IS_iff (β κ σ ω χ ηy ηi rbar lamx lami xstar im : ℝ) (π x i : ℕ → ℝ) (t : ℕ) :
    IS (rbModel β κ σ ω χ ηy ηi rbar lamx lami xstar im) π x i t ↔
      IS310 σ ηy ηi χ x π (fun t => i t - rbar) (fun _ => 0) (fun _ => 0) t := by
  unfold IS IS310 rbModel
  simp only [sub_zero]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), p. 479: with no real-balance effects (`χ = 0`) the real-balance model is the
basic model, so (1.20) reduces to (1.19). -/
theorem rbModel_chi_zero (β κ σ ω ηy ηi rbar lamx lami xstar im : ℝ) :
    rbModel β κ σ ω 0 ηy ηi rbar lamx lami xstar im = basic β κ σ rbar lamx lami xstar im := by
  simp [rbModel, basic, phiRB]

/-- Woodford (2003), (1.20), p. 479 (the key coefficient identity): `b − aϕ = σϕω`
(`σ ≠ 0`, `ε_mc ≠ 0`). -/
theorem rb_coef (β κ σ ω χ ηy ηi rbar lamx lami xstar im : ℝ) (hσ : σ ≠ 0)
    (hε : epsMC σ ω χ ηy ≠ 0) :
    (rbModel β κ σ ω χ ηy ηi rbar lamx lami xstar im).b -
        (rbModel β κ σ ω χ ηy ηi rbar lamx lami xstar im).a *
          (rbModel β κ σ ω χ ηy ηi rbar lamx lami xstar im).ϕ =
      σ * phiRB σ ω χ ηy ηi * ω := by
  simp only [rbModel, phiRB]
  set e := epsMC σ ω χ ηy with he_def
  have he : σ * e = 1 + σ * ω - σ * χ * ηy := by
    rw [he_def, epsMC]
    field_simp
  have hinv : e * e⁻¹ = 1 := mul_inv_cancel₀ hε
  rw [div_eq_mul_inv]
  linear_combination (ηi * χ * e⁻¹) * he - (σ * ηi * χ) * hinv

/-- Woodford (2003), (1.20), p. 479: the denominator of (1.20), with `λ_x = κ/θ`:
`denom = λ_i + ϕ²λ_x + β − (1 − β)ϕ(θ⁻¹ + ω)`. -/
theorem denom_rb (β κ σ ω χ ηy ηi rbar lamx lami xstar im θ : ℝ) (hσ : σ ≠ 0)
    (hε : epsMC σ ω χ ηy ≠ 0) (hκ : κ ≠ 0) (hθ : θ ≠ 0) (hlx : lamx = κ / θ) :
    denom (rbModel β κ σ ω χ ηy ηi rbar lamx lami xstar im) =
      lami + phiRB σ ω χ ηy ηi ^ 2 * lamx + β -
        (1 - β) * phiRB σ ω χ ηy ηi * (θ⁻¹ + ω) := by
  have hc := rb_coef β κ σ ω χ ηy ηi rbar lamx lami xstar im hσ hε
  unfold denom
  rw [hc]
  simp only [rbModel]
  rw [hlx]
  field_simp
  ring

/-- Woodford (2003), **eq. (1.20)**, p. 479 (exact LQ form): with real-balance effects the
stationary plan `(π̄, x̄, ı̄)` is optimal from a timeless perspective iff
`π̄ = −[λ_i(r̄ − iᵐ) + ϕλ_x x*]/[λ_i + ϕ²λ_x + β − (1 − β)ϕ(θ⁻¹ + ω)]`, `ı̄ = r̄ + π̄` and
`κx̄ = (1 − β − κϕ)π̄` (`0 < β < 1`, `σ, κ, θ, ε_mc ≠ 0`, `λ_x = κ/θ ≥ 0`, `λ_i ≥ 0`, nonzero
denominator). -/
theorem eq_1_20 {β κ σ ω χ ηy ηi rbar lamx lami xstar im θ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hσ : σ ≠ 0) (hκ : κ ≠ 0) (hθ : θ ≠ 0) (hε : epsMC σ ω χ ηy ≠ 0) (hlx : lamx = κ / θ)
    (hlx0 : 0 ≤ lamx) (hli : 0 ≤ lami)
    (hD : lami + phiRB σ ω χ ηy ηi ^ 2 * lamx + β -
      (1 - β) * phiRB σ ω χ ηy ηi * (θ⁻¹ + ω) ≠ 0) (πb xb ib : ℝ) :
    TimelesslyOptimal (rbModel β κ σ ω χ ηy ηi rbar lamx lami xstar im) πb xb ib ↔
      πb = -(lami * (rbar - im) + phiRB σ ω χ ηy ηi * lamx * xstar) /
          (lami + phiRB σ ω χ ηy ηi ^ 2 * lamx + β -
            (1 - β) * phiRB σ ω χ ηy ηi * (θ⁻¹ + ω)) ∧
        ib = rbar + πb ∧ κ * xb = (1 - β - κ * phiRB σ ω χ ηy ηi) * πb := by
  have hd := denom_rb β κ σ ω χ ηy ηi rbar lamx lami xstar im θ hσ hε hκ hθ hlx
  rw [timelesslyOptimal_iff_piBar (M := rbModel β κ σ ω χ ηy ηi rbar lamx lami xstar im) hβ0
    hβ1 hlx0 hli hσ hκ (by rw [hd]; exact hD), piBar, hd]
  simp only [rbModel]

/-- Woodford (2003), p. 480 (sign claim): if `ϕ > 0`, `λ_x > 0` and the denominator of (1.20)
is positive, a higher `x*` strictly *lowers* the optimal inflation target. -/
theorem piBar_120_strictAnti {lami rbar im ϕ lamx D : ℝ} (hϕ : 0 < ϕ) (hlx : 0 < lamx)
    (hD : 0 < D) : StrictAnti (fun xs : ℝ => -(lami * (rbar - im) + ϕ * lamx * xs) / D) := by
  intro u v huv
  simp only
  rw [div_lt_div_iff_of_pos_right hD]
  nlinarith [mul_pos hϕ hlx]

/-- Woodford (2003), p. 480 (sign claim, derivative form): `∂π̄/∂x* = −ϕλ_x/denom`, negative
when `ϕ > 0`, `λ_x > 0` and the denominator is positive. -/
theorem hasDerivAt_piBar_120 {lami rbar im ϕ lamx D : ℝ} (xs : ℝ) :
    HasDerivAt (fun xs : ℝ => -(lami * (rbar - im) + ϕ * lamx * xs) / D) (-(ϕ * lamx) / D)
      xs := by
  have h := (((hasDerivAt_id xs).const_mul (ϕ * lamx)).const_add
    (lami * (rbar - im))).neg.div_const D
  convert h using 1 <;> simp

/-- Woodford (2003), p. 480: the derivative `−ϕλ_x/denom` is negative when `ϕ > 0`, `λ_x > 0`
and the denominator of (1.20) is positive. -/
theorem deriv_piBar_120_neg {ϕ lamx D : ℝ} (hϕ : 0 < ϕ) (hlx : 0 < lamx) (hD : 0 < D) :
    -(ϕ * lamx) / D < 0 :=
  div_neg_of_neg_of_pos (neg_lt_zero.mpr (mul_pos hϕ hlx)) hD

/-! ### Optimality under uncertainty -/

/-- Woodford (2003), p. 478 (deterministic core of the stochastic argument): if the stationary
plan satisfies `TimelessCond`, the first-order change of the loss vanishes along every bounded
deviation satisfying the homogeneous constraints and the initial constraints:
`∑βᵗ[π̄ e^π_t + λ_x(x̄ − x*)e^x_t + λ_i(ı̄ − iᵐ)e^i_t] = 0`. -/
theorem dsum_grad_eq_zero {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) (hσ : M.σ ≠ 0)
    (hκ : M.κ ≠ 0) {πb xb ib : ℝ} (hc : TimelessCond M πb xb ib) {eπ ex ei : ℕ → ℝ}
    (hp : Bdd eπ) (hx : Bdd ex) (hi : Bdd ei)
    (hhom : ∀ t, homAS M eπ ex ei t = 0 ∧ homIS M eπ ex ei t = 0) (h0 : eπ 0 = 0)
    (h0' : M.a * ex 0 + M.b * ei 0 = 0) :
    dsum M.β (fun t => πb * eπ t + M.lamx * (xb - M.xstar) * ex t +
      M.lami * (ib - M.im) * ei t) = 0 := by
  obtain ⟨c1, c2, hfoc⟩ := (foc_const_iff hβ0.ne' hσ hκ πb xb ib).mpr hc
  have key := constraint_by_parts (φ1 := fun _ => c1) (φ2 := fun _ => c2) hβ0 hβ1 c1 c2
    (bdd_const c1) (bdd_const c2) hp hx hi
  have hl : (fun t => (fun _ => c1) t * homIS M eπ ex ei t +
      (fun _ => c2) t * homAS M eπ ex ei t) = fun _ => 0 := by
    funext t
    rw [(hhom t).1, (hhom t).2]
    ring
  have hinit : initTerm M c1 c2 eπ ex ei = 0 := by
    unfold initTerm
    rw [h0]
    linear_combination c1 * h0'
  have hr : (fun t => multPi M (fun _ => c1) (fun _ => c2) c1 c2 t * eπ t +
      multX M (fun _ => c1) (fun _ => c2) c1 t * ex t +
      multI M (fun _ => c1) (fun _ => c2) c1 t * ei t) =
      fun t => (-1) * (πb * eπ t + M.lamx * (xb - M.xstar) * ex t +
        M.lami * (ib - M.im) * ei t) := by
    funext t
    obtain ⟨a, b, c⟩ := hfoc t
    simp only [focPi, focX, focI] at a b c
    linear_combination eπ t * a + ex t * b + ei t * c
  rw [hl, hinit, hr, dsum_mul_left] at key
  have hd0 : dsum M.β (fun _ => (0 : ℝ)) = 0 := by simp [dsum]
  rw [hd0] at key
  linarith

variable {Ω : Type*}

/-- Woodford (2003), (1.1) under uncertainty (with real-balance shift):
`π_t = κx_t + κϕ(i_t − r̄) + βE_tπ_{t+1}` as an equality of random variables. -/
def ASs (𝔼 : ExpectationSystem Ω) (M : Model) (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  π t = M.κ • x t + (M.κ * M.ϕ) • (i t - fun _ => M.rbar) + M.β • 𝔼.E t (π (t + 1))

/-- Woodford (2003), (1.15) under uncertainty (with real-balance terms):
`a x_t = a E_t x_{t+1} − σ(i_t − E_tπ_{t+1} − r̄) + b(E_t i_{t+1} − i_t)`. -/
def ISs (𝔼 : ExpectationSystem Ω) (M : Model) (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  M.a • x t = M.a • 𝔼.E t (x (t + 1)) - M.σ • (i t - 𝔼.E t (π (t + 1)) - fun _ => M.rbar) +
    M.b • (𝔼.E t (i (t + 1)) - i t)

/-- Woodford (2003), (1.14) under uncertainty: the expected discounted loss
`E_0 ∑βᵗ L_t` of a random plan, as a random variable (a function of the date-0 state). -/
noncomputable def expLoss (𝔼 : ExpectationSystem Ω) (M : Model) (π x i : ℕ → Ω → ℝ) :
    Ω → ℝ :=
  𝔼.E 0 (fun ω => loss M (fun t => π t ω) (fun t => x t ω) (fun t => i t ω))

/-- Woodford (2003), (1.14): `|u(p − q)| ≤ |u|(C + |q|)` when `|p| ≤ C`. -/
theorem abs_mul_sub_le {u p q C : ℝ} (hp : |p| ≤ C) : |u * (p - q)| ≤ |u| * (C + |q|) := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (by linarith)) (abs_nonneg u)

/-- Woodford (2003), Proposition 7.3 under uncertainty (pp. 477–479, for an arbitrary
expectation system): let the stationary plan be feasible and satisfy `TimelessCond`. Then for
every bounded random plan satisfying the stochastic aggregate-supply and IS relations at every
date, with `π_0 = π̄` and `a x_0 + b i_0 = a x̄ + b ı̄`, the expected loss is the loss of the
stationary plan plus the expected discounted squared deviation:
`E_0 ∑βᵗL_t = ∑βᵗL̄ + E_0 ∑βᵗ[(π_t − π̄)² + λ_x(x_t − x̄)² + λ_i(i_t − ı̄)²]`. -/
theorem expLoss_eq {𝔼 : ExpectationSystem Ω} {M : Model} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0) {πb xb ib : ℝ}
    (hF : Feasible M (fun _ => πb) (fun _ => xb) (fun _ => ib)) (hc : TimelessCond M πb xb ib)
    {π x i : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) (hi : BoundedProc i)
    (hAS : ∀ t, ASs 𝔼 M π x i t) (hIS : ∀ t, ISs 𝔼 M π x i t) (h0 : π 0 = fun _ => πb)
    (h0' : M.a • x 0 + M.b • i 0 = fun _ => M.a * xb + M.b * ib) (ω : Ω) :
    expLoss 𝔼 M π x i ω = loss M (fun _ => πb) (fun _ => xb) (fun _ => ib) +
      𝔼.E 0 (fun ω' => dsum M.β (quad M (fun t => π t ω' - πb) (fun t => x t ω' - xb)
        (fun t => i t ω' - ib))) ω := by
  obtain ⟨C1, hC1⟩ := hπ
  obtain ⟨C2, hC2⟩ := hx
  obtain ⟨C3, hC3⟩ := hi
  have bp : ∀ ω', Bdd (fun t => π t ω') := fun ω' => ⟨C1, fun t => hC1 t ω'⟩
  have bx : ∀ ω', Bdd (fun t => x t ω') := fun ω' => ⟨C2, fun t => hC2 t ω'⟩
  have bi : ∀ ω', Bdd (fun t => i t ω') := fun ω' => ⟨C3, fun t => hC3 t ω'⟩
  set h : ℕ → Ω → ℝ := fun t ω' => πb * (π t ω' - πb) + M.lamx * (xb - M.xstar) * (x t ω' - xb) +
    M.lami * (ib - M.im) * (i t ω' - ib) with hh
  set D2 : Ω → ℝ := fun ω' => dsum M.β (quad M (fun t => π t ω' - πb) (fun t => x t ω' - xb)
    (fun t => i t ω' - ib)) with hD2
  have hpath : (fun ω' => loss M (fun t => π t ω') (fun t => x t ω') (fun t => i t ω')) =
      (fun _ => loss M (fun _ => πb) (fun _ => xb) (fun _ => ib)) +
        (2 : ℝ) • (fun ω' => ∑' t, M.β ^ t * h t ω') + D2 := by
    funext ω'
    have e := loss_expand (M := M) hβ0 hβ1 1 (bdd_const πb) (bdd_const xb) (bdd_const ib)
      ((bp ω').sub (bdd_const πb)) ((bx ω').sub (bdd_const xb)) ((bi ω').sub (bdd_const ib))
    have hy : ∀ (u : ℕ → ℝ) (c : ℝ), (fun t => c + 1 * (u t - c)) = u := fun u c => by
      funext t; ring
    rw [hy (fun t => π t ω'), hy (fun t => x t ω'), hy (fun t => i t ω')] at e
    rw [e]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hD2, hh, dsum]
    ring
  -- the expected first-order term vanishes
  set B : ℝ := |πb| * (C1 + |πb|) + |M.lamx * (xb - M.xstar)| * (C2 + |xb|) +
    |M.lami * (ib - M.im)| * (C3 + |ib|) with hB
  have hbound : ∀ k ω', |M.β ^ k * h k ω'| ≤ M.β ^ k * B := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_pos hβ0]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0.le k)
    simp only [hh, hB]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      (abs_mul_sub_le (hC1 k ω')) (abs_mul_sub_le (hC2 k ω')))) (abs_mul_sub_le (hC3 k ω')))
  have hE1 := 𝔼.E_tsum hβ0.le hβ1 hbound 0 ω
  have hEk : ∀ k, 𝔼.E 0 (fun ω' => M.β ^ k * h k ω') ω =
      M.β ^ k * (πb * (𝔼.E 0 (π k) ω - πb) + M.lamx * (xb - M.xstar) * (𝔼.E 0 (x k) ω - xb) +
        M.lami * (ib - M.im) * (𝔼.E 0 (i k) ω - ib)) := by
    intro k
    have hfun : (fun ω' => M.β ^ k * h k ω') = (M.β ^ k) • (πb • (π k - fun _ => πb) +
        (M.lamx * (xb - M.xstar)) • (x k - fun _ => xb) +
        (M.lami * (ib - M.im)) • (i k - fun _ => ib)) := by
      funext ω'
      simp [hh]
    rw [hfun]
    simp only [map_smul, map_add, map_sub, 𝔼.const, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
      smul_eq_mul]
  have hASe : ∀ t, 𝔼.E 0 (π t) ω = M.κ * 𝔼.E 0 (x t) ω +
      M.κ * M.ϕ * (𝔼.E 0 (i t) ω - M.rbar) + M.β * 𝔼.E 0 (π (t + 1)) ω := by
    intro t
    have e := congrArg (fun z => 𝔼.E 0 z ω) (hAS t)
    simp only [map_add, map_sub, map_smul, 𝔼.const, 𝔼.tower (Nat.zero_le t), Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    exact e
  have hISe : ∀ t, M.a * 𝔼.E 0 (x t) ω = M.a * 𝔼.E 0 (x (t + 1)) ω -
      M.σ * (𝔼.E 0 (i t) ω - 𝔼.E 0 (π (t + 1)) ω - M.rbar) +
      M.b * (𝔼.E 0 (i (t + 1)) ω - 𝔼.E 0 (i t) ω) := by
    intro t
    have e := congrArg (fun z => 𝔼.E 0 z ω) (hIS t)
    simp only [map_add, map_sub, map_smul, 𝔼.const, 𝔼.tower (Nat.zero_le t), Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    exact e
  have hzero : dsum M.β (fun t => πb * (𝔼.E 0 (π t) ω - πb) +
      M.lamx * (xb - M.xstar) * (𝔼.E 0 (x t) ω - xb) +
      M.lami * (ib - M.im) * (𝔼.E 0 (i t) ω - ib)) = 0 := by
    have be : ∀ (y : ℕ → Ω → ℝ) (C c : ℝ), (∀ t ω, |y t ω| ≤ C) →
        Bdd (fun t => 𝔼.E 0 (y t) ω - c) := fun y C c hy =>
      (show Bdd (fun t => 𝔼.E 0 (y t) ω) from ⟨C, fun t => 𝔼.abs_E_le (hy t) 0 ω⟩).sub
        (bdd_const c)
    refine dsum_grad_eq_zero hβ0 hβ1 hσ hκ hc (be π C1 πb hC1) (be x C2 xb hC2)
      (be i C3 ib hC3) (fun t => ?_) ?_ ?_
    · have ha := (hF t).1
      have hb := (hF t).2
      unfold AS at ha
      unfold IS at hb
      have e1 := hASe t
      have e2 := hISe t
      unfold homAS homIS
      constructor
      · linear_combination e1 - ha
      · linear_combination e2 - hb
    · rw [h0, 𝔼.const]
      ring
    · have e := congrArg (fun z => 𝔼.E 0 z ω) h0'
      simp only [map_add, map_smul, 𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
      linear_combination e
  have hD1 : 𝔼.E 0 (fun ω' => ∑' t, M.β ^ t * h t ω') ω = 0 := by
    rw [hE1]
    simp_rw [hEk]
    exact hzero
  unfold expLoss
  rw [hpath]
  simp only [map_add, map_smul, 𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hD1]
  ring

/-- Woodford (2003), Proposition 7.3 under uncertainty (optimality): in the setting of
`expLoss_eq` with `λ_x, λ_i ≥ 0`, no bounded random plan satisfying the constraints and the
initial constraints has lower expected loss than the stationary plan, in any date-0 state. -/
theorem loss_le_expLoss {𝔼 : ExpectationSystem Ω} {M : Model} (hβ0 : 0 < M.β)
    (hβ1 : M.β < 1) (hlx : 0 ≤ M.lamx) (hli : 0 ≤ M.lami) (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0)
    {πb xb ib : ℝ} (hF : Feasible M (fun _ => πb) (fun _ => xb) (fun _ => ib))
    (hc : TimelessCond M πb xb ib) {π x i : ℕ → Ω → ℝ} (hπ : BoundedProc π)
    (hx : BoundedProc x) (hi : BoundedProc i) (hAS : ∀ t, ASs 𝔼 M π x i t)
    (hIS : ∀ t, ISs 𝔼 M π x i t) (h0 : π 0 = fun _ => πb)
    (h0' : M.a • x 0 + M.b • i 0 = fun _ => M.a * xb + M.b * ib) (ω : Ω) :
    loss M (fun _ => πb) (fun _ => xb) (fun _ => ib) ≤ expLoss 𝔼 M π x i ω := by
  rw [expLoss_eq hβ0 hβ1 hσ hκ hF hc hπ hx hi hAS hIS h0 h0' ω]
  have hnn : (0 : Ω → ℝ) ≤ fun ω' => dsum M.β (quad M (fun t => π t ω' - πb)
      (fun t => x t ω' - xb) (fun t => i t ω' - ib)) := fun ω' =>
    dsum_nonneg hβ0.le (quad_nonneg hlx hli _ _ _)
  have := 𝔼.mono 0 hnn ω
  rw [map_zero, Pi.zero_apply] at this
  linarith [this]

/-- Woodford (2003), **Proposition 7.3 under uncertainty**: in the economy with transactions
frictions, with `π̄` given by (1.19), `ı̄ = r̄ + π̄` and `x̄ = (1 − β)π̄/κ`, no bounded random plan
satisfying the stochastic versions of (1.1) and (1.15) at every date, with `π_0 = π̄` and
`x_0 = x̄`, has lower expected loss (1.14) than the constant plan, for any expectation system. -/
theorem prop_7_3_uncertainty {𝔼 : ExpectationSystem Ω} {β κ σ rbar lamx lami xstar im : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lamx) (hli : 0 ≤ lami)
    {πb xb ib : ℝ} (hopt : πb = -(lami / (lami + β)) * (rbar - im) ∧ ib = rbar + πb ∧
      xb = (1 - β) * πb / κ)
    {π x i : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) (hi : BoundedProc i)
    (hAS : ∀ t, ASs 𝔼 (basic β κ σ rbar lamx lami xstar im) π x i t)
    (hIS : ∀ t, ISs 𝔼 (basic β κ σ rbar lamx lami xstar im) π x i t)
    (h0 : π 0 = fun _ => πb) (h0' : x 0 = fun _ => xb) (ω : Ω) :
    loss (basic β κ σ rbar lamx lami xstar im) (fun _ => πb) (fun _ => xb) (fun _ => ib) ≤
      expLoss 𝔼 (basic β κ σ rbar lamx lami xstar im) π x i ω := by
  have hT := (prop_7_3 (xstar := xstar) hβ0 hβ1 hκ hσ hlx hli πb xb ib).mpr hopt
  refine loss_le_expLoss (M := basic β κ σ rbar lamx lami xstar im) hβ0 hβ1 hlx hli hσ.ne'
    hκ.ne' hT.1 (cond_of_timelesslyOptimal hβ0 hβ1 hκ.ne' hT) hπ hx hi hAS hIS h0 ?_ ω
  funext ω'
  simp [basic, h0']

end Woodford.GainsFromCommitment.MonetaryFrictions
