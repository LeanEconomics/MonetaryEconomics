/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.ForwardSolution
import GainsFromCommitment.ExpectationsFiniteTree
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Deterministic and stabilisation losses, and the forward-looking variance frontier

Woodford (2003), *Interest and Prices*, Chapter 7, §2.1, pp. 496–497 (the decomposition of the
expected loss, eqs. (2.18)–(2.22)) and §3, pp. 508–513 (`L_det + L_stab`, (3.2)–(3.4),
(3.6)–(3.8)).

Conditional variances are defined from the expectation operator, `var_s X = E_s X² − (E_s X)²`
(`condVar`). Every result holds for an arbitrary `ExpectationSystem`; the results about AR(1)
disturbances use an explicit innovation structure (`AR1Innov`: `u_{t+1} = ρu_t + ε_{t+1}`,
`E_t ε_{t+1} = 0`, `E_t ε²_{t+1} = σ²_{t+1}`) and the pull-out property (`PullOut`), which hold
under genuine uncertainty (`coin_AR1Innov`, `ExpectationsFiniteTree.finiteTree_pullOut`).

## Main results

* `condVar_eq_E_dev`, `condVar_nonneg`, `condVar_affine`, `condVar_affine2` (conditional
  variance algebra).
* `loss_decomposition` (p. 509, and p. 496): `E_{t₀} ∑ β^{t−t₀}[π_t² + λ(x_t − x*)²] =
  L_det + L_stab` with genuine infinite sums; `loss_decomposition_V` (p. 496): the same with
  `V[y] = (1 − β)∑ βᵗ var(y_t)`; `decomposition_independent`: `L_det` depends only on the
  deterministic component and `L_stab` only on the responses to shocks.
* `fwd_AS_iff` ((2.19)–(2.21), (3.2)–(3.3)): a forward-looking linear plan is a
  rational-expectations equilibrium iff (2.20) and (2.21) hold (for a nondegenerate shock);
  `fwd_AS_degenerate` shows nondegeneracy is needed; `fwd_V` (p. 497):
  `V[π] + λV[x] = (f_π² + λf_x²)V[u]`.
* `opt_frontier` ((2.22)): the unique minimiser of `f_π² + λf_x²` subject to (2.21), with
  `f_π > 0 > f_x`.
* `ar1_condVar_closed` (p. 511): `var_{t₀}(u_{t₀+k}) = σ_u²(1 − ρ^{2k})`; `tsum_disc_one_sub`;
  `Lstab_ar1` ((3.4)).
* `condCov_zero`, `two_shock_RE_iff` ((3.6) and the four restrictions), `Lstab_two_shocks`
  ((3.7)–(3.8): `L_stab = L_stab,r + L_stab,u`).
-/

namespace Woodford.GainsFromCommitment.VarianceFrontier

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Conditional variances -/

/-- Woodford (2003), p. 509: the conditional variance `var_s X = E_s X² − (E_s X)²`. -/
def condVar (s : ℕ) (X : Ω → ℝ) : Ω → ℝ := 𝔼.E s (X * X) - 𝔼.E s X * 𝔼.E s X

/-- Woodford (2003), p. 512: the conditional covariance `cov_s(X, Y) = E_s XY − E_s X E_s Y`. -/
def condCov (s : ℕ) (X Y : Ω → ℝ) : Ω → ℝ := 𝔼.E s (X * Y) - 𝔼.E s X * 𝔼.E s Y

/-- Woodford (2003), p. 496: `E_s X² = (E_s X)² + var_s X`. -/
theorem E_sq_eq (s : ℕ) (X : Ω → ℝ) :
    𝔼.E s (X * X) = 𝔼.E s X * 𝔼.E s X + condVar 𝔼 s X := by
  unfold condVar; ring

/-- Woodford (2003), p. 509: with the pull-out property, `var_s X = E_s (X − E_s X)²`. -/
theorem condVar_eq_E_dev (hpo : 𝔼.PullOut) (s : ℕ) (X : Ω → ℝ) :
    condVar 𝔼 s X = 𝔼.E s ((X - 𝔼.E s X) * (X - 𝔼.E s X)) := by
  have hm : 𝔼.E s (𝔼.E s X) = 𝔼.E s X := 𝔼.E_E_self s X
  have h1 : 𝔼.E s (𝔼.E s X * X) = 𝔼.E s X * 𝔼.E s X := hpo s _ X hm
  have h2 : 𝔼.E s (𝔼.E s X * 𝔼.E s X) = 𝔼.E s X * 𝔼.E s X := by rw [hpo s _ _ hm, hm]
  have : (X - 𝔼.E s X) * (X - 𝔼.E s X) =
      X * X - 𝔼.E s X * X - 𝔼.E s X * X + 𝔼.E s X * 𝔼.E s X := by ring
  rw [this, map_add, map_sub, map_sub, h1, h2]
  unfold condVar
  ring

/-- Woodford (2003), p. 509: with the pull-out property conditional variances are nonnegative. -/
theorem condVar_nonneg (hpo : 𝔼.PullOut) (s : ℕ) (X : Ω → ℝ) (ω : Ω) :
    0 ≤ condVar 𝔼 s X ω := by
  rw [condVar_eq_E_dev 𝔼 hpo]
  have := 𝔼.mono s (x := 0) (y := (X - 𝔼.E s X) * (X - 𝔼.E s X))
    (fun ω' => mul_self_nonneg _)
  rw [map_zero] at this
  exact this ω

/-- Woodford (2003), p. 497: `var_s(a + bX) = b² var_s X` for constants `a`, `b`. -/
theorem condVar_affine (s : ℕ) (a b : ℝ) (X : Ω → ℝ) :
    condVar 𝔼 s ((fun _ => a) + b • X) = b ^ 2 • condVar 𝔼 s X := by
  have hsq : ((fun _ => a) + b • X) * ((fun _ => a) + b • X) =
      (fun _ => a * a) + (2 * a * b) • X + (b * b) • (X * X) := by
    funext ω; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold condVar
  rw [hsq]
  simp only [map_add, map_smul, 𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 512: `var_s(a + fX + gY) = f² var_s X + g² var_s Y + 2fg cov_s(X, Y)`. -/
theorem condVar_affine2 (s : ℕ) (a f g : ℝ) (X Y : Ω → ℝ) :
    condVar 𝔼 s ((fun _ => a) + f • X + g • Y) =
      f ^ 2 • condVar 𝔼 s X + g ^ 2 • condVar 𝔼 s Y + (2 * f * g) • condCov 𝔼 s X Y := by
  have hsq : ((fun _ => a) + f • X + g • Y) * ((fun _ => a) + f • X + g • Y) =
      (fun _ => a * a) + (2 * a * f) • X + (2 * a * g) • Y + (f * f) • (X * X) +
        (g * g) • (Y * Y) + (2 * f * g) • (X * Y) := by
    funext ω; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold condVar condCov
  rw [hsq]
  simp only [map_add, map_smul, 𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 509: a bounded variable has a bounded conditional variance,
`|var_s X| ≤ 2M²`. -/
theorem abs_condVar_le {M : ℝ} {X : Ω → ℝ} (hX : ∀ ω, |X ω| ≤ M) (s : ℕ) (ω : Ω) :
    |condVar 𝔼 s X ω| ≤ 2 * M ^ 2 := by
  have hsq : ∀ ω', |(X * X) ω'| ≤ M ^ 2 := fun ω' => by
    rw [Pi.mul_apply, abs_mul, sq]
    exact mul_le_mul (hX ω') (hX ω') (abs_nonneg _) ((abs_nonneg _).trans (hX ω'))
  have h1 := 𝔼.abs_E_le hsq s ω
  have h2 := 𝔼.abs_E_le hX s ω
  have h3 : |𝔼.E s X ω * 𝔼.E s X ω| ≤ M ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul h2 h2 (abs_nonneg _) ((abs_nonneg _).trans h2)
  unfold condVar
  rw [Pi.sub_apply, Pi.mul_apply]
  calc |𝔼.E s (X * X) ω - 𝔼.E s X ω * 𝔼.E s X ω|
      ≤ |𝔼.E s (X * X) ω| + |𝔼.E s X ω * 𝔼.E s X ω| := abs_sub _ _
    _ ≤ 2 * M ^ 2 := by linarith

/-! ### The decomposition `L = L_det + L_stab` (pp. 496, 509) -/

/-- **`L = L_det + L_stab`** (Woodford (2003), p. 509, and p. 496): for bounded inflation and
output-gap processes, the expected discounted loss conditional on date `s = t₀` splits into a
deterministic part (squared conditional means) and a stabilisation part (conditional
variances), all as genuine infinite sums:
`E_{t₀} ∑_k βᵏ[π_{t₀+k}² + λ(x_{t₀+k} − x*)²] =
∑_k βᵏ[(E_{t₀}π_{t₀+k})² + λ(E_{t₀}x_{t₀+k} − x*)²] +
∑_k βᵏ[var_{t₀}π_{t₀+k} + λ var_{t₀}x_{t₀+k}]`. -/
theorem loss_decomposition {β lam xs Mπ Mx : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {π x : ℕ → Ω → ℝ} (hπ : ∀ t ω, |π t ω| ≤ Mπ) (hx : ∀ t ω, |x t ω| ≤ Mx) (s : ℕ) (ω : Ω) :
    𝔼.E s (fun ω' => ∑' k, β ^ k * (π (s + k) ω' ^ 2 + lam * (x (s + k) ω' - xs) ^ 2)) ω =
      (∑' k, β ^ k * ((𝔼.E s (π (s + k)) ω) ^ 2 + lam * (𝔼.E s (x (s + k)) ω - xs) ^ 2)) +
        ∑' k, β ^ k * (condVar 𝔼 s (π (s + k)) ω + lam * condVar 𝔼 s (x (s + k)) ω) := by
  have hxc : ∀ t ω, |x t ω - xs| ≤ Mx + |xs| := fun t ω =>
    (abs_sub _ _).trans (add_le_add (hx t ω) le_rfl)
  set B := Mπ ^ 2 + |lam| * (Mx + |xs|) ^ 2 with hB
  have hsq : ∀ (M : ℝ) (y : Ω → ℝ), (∀ ω, |y ω| ≤ M) → ∀ ω, |y ω ^ 2| ≤ M ^ 2 := by
    intro M y hy ω
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hy ω) 2
  have hterm : ∀ k ω', |β ^ k * (π (s + k) ω' ^ 2 + lam * (x (s + k) ω' - xs) ^ 2)| ≤
      β ^ k * B := by
    intro k ω'
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 k)
    calc |π (s + k) ω' ^ 2 + lam * (x (s + k) ω' - xs) ^ 2|
        ≤ |π (s + k) ω' ^ 2| + |lam| * |(x (s + k) ω' - xs) ^ 2| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ B := by
          rw [hB]
          gcongr
          · exact hsq Mπ (π (s + k)) (hπ _) ω'
          · exact hsq (Mx + |xs|) (fun ω => x (s + k) ω - xs) (hxc _) ω'
  rw [𝔼.E_tsum hβ0 hβ1 (f := fun k ω' => β ^ k * (π (s + k) ω' ^ 2 +
    lam * (x (s + k) ω' - xs) ^ 2)) hterm s ω]
  -- termwise identity
  have hE : ∀ k, 𝔼.E s (fun ω' => β ^ k * (π (s + k) ω' ^ 2 + lam * (x (s + k) ω' - xs) ^ 2)) ω
      = β ^ k * ((𝔼.E s (π (s + k)) ω) ^ 2 + lam * (𝔼.E s (x (s + k)) ω - xs) ^ 2) +
        β ^ k * (condVar 𝔼 s (π (s + k)) ω + lam * condVar 𝔼 s (x (s + k)) ω) := by
    intro k
    have hf : (fun ω' => β ^ k * (π (s + k) ω' ^ 2 + lam * (x (s + k) ω' - xs) ^ 2)) =
        β ^ k • (π (s + k) * π (s + k) + lam • (((fun _ => -xs) + (1 : ℝ) • x (s + k)) *
          ((fun _ => -xs) + (1 : ℝ) • x (s + k)))) := by
      funext ω'
      simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hv := congrFun (condVar_affine 𝔼 s (-xs) 1 (x (s + k))) ω
    have hv2 := congrFun (E_sq_eq 𝔼 s ((fun _ => -xs) + (1 : ℝ) • x (s + k))) ω
    have hv3 := congrFun (E_sq_eq 𝔼 s (π (s + k))) ω
    rw [hf, map_smul, map_add, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at hv hv2 hv3 ⊢
    rw [hv2, hv3, hv]
    simp only [map_add, map_smul, 𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hE]
  have hs1 : Summable (fun k => β ^ k * ((𝔼.E s (π (s + k)) ω) ^ 2 +
      lam * (𝔼.E s (x (s + k)) ω - xs) ^ 2)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right B)
      (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 k)
    have h1 := 𝔼.abs_E_le (hπ (s + k)) s ω
    have h2 : |𝔼.E s (x (s + k)) ω - xs| ≤ Mx + |xs| :=
      (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le (hx (s + k)) s ω) le_rfl)
    calc |𝔼.E s (π (s + k)) ω ^ 2 + lam * (𝔼.E s (x (s + k)) ω - xs) ^ 2|
        ≤ |𝔼.E s (π (s + k)) ω ^ 2| + |lam| * |(𝔼.E s (x (s + k)) ω - xs) ^ 2| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ B := by
          rw [hB, abs_pow, abs_pow]
          gcongr
  have hs2 : Summable (fun k => β ^ k * (condVar 𝔼 s (π (s + k)) ω +
      lam * condVar 𝔼 s (x (s + k)) ω)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right
      (2 * Mπ ^ 2 + |lam| * (2 * Mx ^ 2))) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 k)
    calc |condVar 𝔼 s (π (s + k)) ω + lam * condVar 𝔼 s (x (s + k)) ω|
        ≤ |condVar 𝔼 s (π (s + k)) ω| + |lam| * |condVar 𝔼 s (x (s + k)) ω| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 * Mπ ^ 2 + |lam| * (2 * Mx ^ 2) := by
          gcongr
          · exact abs_condVar_le 𝔼 (hπ (s + k)) s ω
          · exact abs_condVar_le 𝔼 (hx (s + k)) s ω
  exact hs1.tsum_add hs2

/-- Woodford (2003), p. 496: the discounted measure of variability
`V[y] = (1 − β) ∑_k βᵏ var_{t₀}(y_{t₀+k})`. -/
noncomputable def discVar (β : ℝ) (s : ℕ) (y : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (1 - β) * ∑' k, β ^ k * condVar 𝔼 s (y (s + k)) ω

/-- **Woodford (2003), p. 496**: `E ∑ βᵗ[π_t² + λ(x_t − x*)²] = ∑ βᵗ[(Eπ_t)² + λ(Ex_t − x*)²]
+ (1 − β)⁻¹V[π] + (1 − β)⁻¹λV[x]`. -/
theorem loss_decomposition_V {β lam xs Mπ Mx : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {π x : ℕ → Ω → ℝ} (hπ : ∀ t ω, |π t ω| ≤ Mπ) (hx : ∀ t ω, |x t ω| ≤ Mx) (s : ℕ) (ω : Ω) :
    𝔼.E s (fun ω' => ∑' k, β ^ k * (π (s + k) ω' ^ 2 + lam * (x (s + k) ω' - xs) ^ 2)) ω =
      (∑' k, β ^ k * ((𝔼.E s (π (s + k)) ω) ^ 2 + lam * (𝔼.E s (x (s + k)) ω - xs) ^ 2)) +
        (1 - β)⁻¹ * discVar 𝔼 β s π ω + (1 - β)⁻¹ * lam * discVar 𝔼 β s x ω := by
  rw [loss_decomposition 𝔼 hβ0 hβ1 hπ hx s ω]
  have hs : ∀ (M : ℝ) (y : ℕ → Ω → ℝ), (∀ t ω, |y t ω| ≤ M) →
      Summable (fun k => β ^ k * condVar 𝔼 s (y (s + k)) ω) := fun M y hy =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right (2 * M ^ 2))
      (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
        exact mul_le_mul_of_nonneg_left (abs_condVar_le 𝔼 (hy (s + k)) s ω)
          (pow_nonneg hβ0 k))
  have h1 : (1 - β) ≠ 0 := by linarith
  have hsplit : ∑' k, β ^ k * (condVar 𝔼 s (π (s + k)) ω + lam * condVar 𝔼 s (x (s + k)) ω) =
      ∑' k, β ^ k * condVar 𝔼 s (π (s + k)) ω +
        lam * ∑' k, β ^ k * condVar 𝔼 s (x (s + k)) ω := by
    rw [← tsum_mul_left, ← (hs Mπ π hπ).tsum_add ((hs Mx x hx).mul_left lam)]
    exact tsum_congr fun k => by ring
  rw [hsplit, add_assoc]
  unfold discVar
  field_simp

/-- Woodford (2003), p. 496 ("the first term depends only on the deterministic component of
policy, the remaining two only on the prescribed responses to shocks"): with the pull-out
property, if `π_t = π^det_t + π^sh_t` with `π^det_t` known at `t₀` and `E_{t₀}π^sh_t = 0`, then
`E_{t₀}π_t = π^det_t` and `var_{t₀}π_t = var_{t₀}π^sh_t`. -/
theorem decomposition_independent (hpo : 𝔼.PullOut) {s : ℕ} {πd πs : Ω → ℝ}
    (hd : 𝔼.E s πd = πd) (hs : 𝔼.E s πs = 0) :
    𝔼.E s (πd + πs) = πd ∧ condVar 𝔼 s (πd + πs) = condVar 𝔼 s πs := by
  have hE : 𝔼.E s (πd + πs) = πd := by rw [map_add, hd, hs, add_zero]
  refine ⟨hE, ?_⟩
  have h1 : 𝔼.E s (πd * πd) = πd * πd := by rw [hpo s πd πd hd, hd]
  have h2 : 𝔼.E s (πd * πs) = 0 := by rw [hpo s πd πs hd, hs, mul_zero]
  have hsq : (πd + πs) * (πd + πs) = πd * πd + πd * πs + πd * πs + πs * πs := by ring
  unfold condVar
  rw [hE, hsq, map_add, map_add, map_add, h1, h2, hs]
  ring

/-! ### Forward-looking linear plans (2.18)–(2.21) and the frontier (2.22) -/

/-- Woodford (2003), eq. (2.19), p. 497: the forward-looking linear plan `y_t = ȳ + f u_t`. -/
def fwdPlan (ybar f : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => (fun _ => ybar) + f • u t

/-- Woodford (2003), eq. (2.1), p. 486: the aggregate-supply relation
`π_t = κx_t + βE_tπ_{t+1} + u_t` at every date. -/
def AS (β κ : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = κ • x t + β • 𝔼.E t (π (t + 1)) + u t

/-- **Woodford (2003), (2.20)–(2.21), p. 497 (and (3.2)–(3.3), p. 511)**: for an AR(1) cost-push
shock (2.18) that is not constant (two distinct values), the plan (2.19) is a
rational-expectations equilibrium iff `(1 − β)π̄ = κx̄` and `(1 − βρ)f_π = κf_x + 1`. -/
theorem fwd_AS_iff {β κ ρ pibar xbar fπ fx : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u)
    (hnd : ∃ t ω t' ω', u t ω ≠ u t' ω') :
    AS 𝔼 β κ u (fwdPlan pibar fπ u) (fwdPlan xbar fx u) ↔
      ((1 - β) * pibar = κ * xbar ∧ (1 - β * ρ) * fπ = κ * fx + 1) := by
  have hpt : ∀ t, (fwdPlan pibar fπ u t = κ • fwdPlan xbar fx u t +
      β • 𝔼.E t (fwdPlan pibar fπ u (t + 1)) + u t) ↔
      ∀ ω', ((1 - β) * pibar - κ * xbar) + ((1 - β * ρ) * fπ - κ * fx - 1) * u t ω' = 0 := by
    intro t
    have hE : 𝔼.E t (fwdPlan pibar fπ u (t + 1)) = (fun _ => pibar) + (fπ * ρ) • u t := by
      unfold fwdPlan
      rw [map_add, map_smul, 𝔼.const, hu.2 t, smul_smul]
    rw [hE, funext_iff]
    refine forall_congr' fun ω' => ?_
    unfold fwdPlan
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> intro h <;> linarith
  unfold AS
  constructor
  · intro h
    obtain ⟨t, ω, t', ω', hne⟩ := hnd
    have h1 := ((hpt t).mp (h t)) ω
    have h2 := ((hpt t').mp (h t')) ω'
    have hB : (1 - β * ρ) * fπ - κ * fx - 1 = 0 := by
      have : ((1 - β * ρ) * fπ - κ * fx - 1) * (u t ω - u t' ω') = 0 := by linarith
      rcases mul_eq_zero.mp this with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.mp h3) hne
    rw [hB, zero_mul, add_zero] at h1
    constructor <;> linarith
  · rintro ⟨h1, h2⟩ t
    exact (hpt t).mpr fun ω' => by
      rw [show (1 - β) * pibar - κ * xbar = 0 by linarith,
        show (1 - β * ρ) * fπ - κ * fx - 1 = 0 by linarith]
      ring

/-- Woodford (2003), (2.20)–(2.21), p. 497: nondegeneracy of `u` is needed for "only if": with
`u ≡ 0` (an AR(1) process for every `ρ`) the plan `π = x = 0` is an equilibrium although (2.21)
fails. -/
theorem fwd_AS_degenerate (β κ ρ : ℝ) :
    𝔼.IsAR1 ρ (fun _ => 0) ∧
      AS 𝔼 β κ (fun _ => 0) (fwdPlan 0 0 (fun _ => 0)) (fwdPlan 0 0 (fun _ => 0)) ∧
      ¬ ((1 - β * ρ) * 0 = κ * 0 + 1) := by
  refine ⟨⟨fun t => map_zero _, fun t => by simp⟩, fun t => ?_, by simp⟩
  unfold fwdPlan
  simp only [zero_smul, add_zero, 𝔼.const]
  funext ω
  simp

/-- Woodford (2003), p. 497: under a plan (2.19), `var_s(ȳ + f u_t) = f² var_s(u_t)`. -/
theorem fwd_condVar (s t : ℕ) (ybar f : ℝ) (u : ℕ → Ω → ℝ) :
    condVar 𝔼 s (fwdPlan ybar f u t) = f ^ 2 • condVar 𝔼 s (u t) :=
  condVar_affine 𝔼 s ybar f (u t)

/-- **Woodford (2003), p. 497**: for plans of the form (2.19),
`V[π] + λV[x] = (f_π² + λf_x²) V[u]`. -/
theorem fwd_V (β lam pibar xbar fπ fx : ℝ) (u : ℕ → Ω → ℝ) (s : ℕ) (ω : Ω) :
    discVar 𝔼 β s (fwdPlan pibar fπ u) ω + lam * discVar 𝔼 β s (fwdPlan xbar fx u) ω =
      (fπ ^ 2 + lam * fx ^ 2) * discVar 𝔼 β s u ω := by
  unfold discVar
  have h : ∀ ybar f k, β ^ k * condVar 𝔼 s (fwdPlan ybar f u (s + k)) ω =
      f ^ 2 * (β ^ k * condVar 𝔼 s (u (s + k)) ω) := fun ybar f k => by
    rw [fwd_condVar, Pi.smul_apply, smul_eq_mul]; ring
  simp only [h, tsum_mul_left]
  ring

/-- Woodford (2003), eq. (2.22), p. 497: the optimal inflation response
`f_π = (1 − βρ)/(κ²λ⁻¹ + (1 − βρ)²)`. -/
noncomputable def fpiOpt (β ρ κ lam : ℝ) : ℝ := (1 - β * ρ) / (κ ^ 2 / lam + (1 - β * ρ) ^ 2)

/-- Woodford (2003), eq. (2.22), p. 497: the optimal output-gap response
`f_x = −κλ⁻¹/(κ²λ⁻¹ + (1 − βρ)²)`. -/
noncomputable def fxOpt (β ρ κ lam : ℝ) : ℝ := -(κ / lam) / (κ ^ 2 / lam + (1 - β * ρ) ^ 2)

/-- **Woodford (2003), eq. (2.22), p. 497**: `(f_π, f_x)` of (2.22) satisfies (2.21),
`f_π > 0 > f_x`, and for every `(f, g)` satisfying (2.21),
`f² + λg² = f_π² + λf_x² + (f − f_π)² + λ(g − f_x)²`; hence (2.22) is the unique minimiser of
`f² + λg²` subject to (2.21). -/
theorem opt_frontier {β ρ κ lam : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (ha : 0 < 1 - β * ρ) :
    (1 - β * ρ) * fpiOpt β ρ κ lam = κ * fxOpt β ρ κ lam + 1 ∧ 0 < fpiOpt β ρ κ lam ∧
      fxOpt β ρ κ lam < 0 ∧
      ∀ f g, (1 - β * ρ) * f = κ * g + 1 →
        f ^ 2 + lam * g ^ 2 = fpiOpt β ρ κ lam ^ 2 + lam * fxOpt β ρ κ lam ^ 2 +
          ((f - fpiOpt β ρ κ lam) ^ 2 + lam * (g - fxOpt β ρ κ lam) ^ 2) := by
  have hD : 0 < κ ^ 2 / lam + (1 - β * ρ) ^ 2 := by positivity
  have hfeas : (1 - β * ρ) * fpiOpt β ρ κ lam = κ * fxOpt β ρ κ lam + 1 := by
    unfold fpiOpt fxOpt
    field_simp
    ring
  refine ⟨hfeas, div_pos ha hD, div_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hκ hlam)) hD,
    fun f g hfg => ?_⟩
  have key : fpiOpt β ρ κ lam * (f - fpiOpt β ρ κ lam) +
      lam * fxOpt β ρ κ lam * (g - fxOpt β ρ κ lam) =
      ((1 - β * ρ) * (f - fpiOpt β ρ κ lam) - κ * (g - fxOpt β ρ κ lam)) /
        (κ ^ 2 / lam + (1 - β * ρ) ^ 2) := by
    unfold fpiOpt fxOpt
    field_simp
    ring
  have hzero : (1 - β * ρ) * (f - fpiOpt β ρ κ lam) - κ * (g - fxOpt β ρ κ lam) = 0 := by
    linarith
  rw [hzero, zero_div] at key
  linear_combination 2 * key

/-- Woodford (2003), eq. (2.22), p. 497: the response coefficients (2.22) minimise `f² + λg²`
subject to (2.21), uniquely. -/
theorem opt_frontier_min {β ρ κ lam : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (ha : 0 < 1 - β * ρ)
    (f g : ℝ) (hfg : (1 - β * ρ) * f = κ * g + 1) :
    fpiOpt β ρ κ lam ^ 2 + lam * fxOpt β ρ κ lam ^ 2 ≤ f ^ 2 + lam * g ^ 2 ∧
      (f ^ 2 + lam * g ^ 2 = fpiOpt β ρ κ lam ^ 2 + lam * fxOpt β ρ κ lam ^ 2 →
        f = fpiOpt β ρ κ lam ∧ g = fxOpt β ρ κ lam) := by
  have h := (opt_frontier hκ hlam ha).2.2.2 f g hfg
  have h1 := sq_nonneg (f - fpiOpt β ρ κ lam)
  have h2 := mul_nonneg hlam.le (sq_nonneg (g - fxOpt β ρ κ lam))
  refine ⟨by linarith, fun heq => ?_⟩
  have h3 : (f - fpiOpt β ρ κ lam) ^ 2 = 0 := by linarith
  have h4 : lam * (g - fxOpt β ρ κ lam) ^ 2 = 0 := by linarith
  have h5 : (g - fxOpt β ρ κ lam) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · linarith
    · exact h
  exact ⟨by nlinarith [pow_eq_zero_iff (n := 2) (a := f - fpiOpt β ρ κ lam) two_ne_zero],
    by nlinarith [pow_eq_zero_iff (n := 2) (a := g - fxOpt β ρ κ lam) two_ne_zero]⟩

/-! ### AR(1) disturbances: `var_{t₀}(u_t) = σ_u²(1 − ρ^{2k})` and (3.4) -/

/-- Woodford (2003), eq. (2.18), p. 496 (and (2.27), p. 504): an AR(1) disturbance
`u_{t+1} = ρu_t + ε_{t+1}` with innovations satisfying `E_t ε_{t+1} = 0` and
`E_t ε²_{t+1} = σ²_{t+1}` (a deterministic sequence of innovation variances). -/
def AR1Innov (ρ : ℝ) (sig2 : ℕ → ℝ) (u ε : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted u ∧ 𝔼.Adapted ε ∧ (∀ t, u (t + 1) = ρ • u t + ε (t + 1)) ∧
    (∀ t, 𝔼.E t (ε (t + 1)) = 0) ∧ ∀ t, 𝔼.E t (ε (t + 1) * ε (t + 1)) = fun _ => sig2 (t + 1)

/-- Woodford (2003), eq. (2.18), p. 496: an AR(1) disturbance with mean-zero innovations is
`IsAR1`. -/
theorem ar1Innov_isAR1 {ρ : ℝ} {sig2 : ℕ → ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1Innov 𝔼 ρ sig2 u ε) :
    𝔼.IsAR1 ρ u :=
  ⟨h.1, fun t => by rw [h.2.2.1 t, map_add, map_smul, h.1 t, h.2.2.2.1 t, add_zero]⟩

/-- Woodford (2003), p. 512: a date-`(s+k)` variable times a later mean-zero innovation has zero
date-`s` forecast, `E_s(X_{s+k} ε_{s+k+1}) = 0` (pull-out, then iterated expectations). -/
theorem E_known_mul_innov (hpo : 𝔼.PullOut) {X ε : ℕ → Ω → ℝ} (hX : 𝔼.Adapted X)
    (hε : ∀ t, 𝔼.E t (ε (t + 1)) = 0) (s k : ℕ) : 𝔼.E s (X (s + k) * ε (s + k + 1)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right s k), hpo (s + k) _ _ (hX (s + k)), hε, mul_zero, map_zero]

/-- Woodford (2003), p. 511: future innovations are unforecastable,
`E_s(u_{s+k} ε_{s+k+1}) = 0` (pull-out at `s + k`, then iterated expectations). -/
theorem innov_E_u_eps (hpo : 𝔼.PullOut) {ρ : ℝ} {sig2 : ℕ → ℝ} {u ε : ℕ → Ω → ℝ}
    (h : AR1Innov 𝔼 ρ sig2 u ε) (s k : ℕ) : 𝔼.E s (u (s + k) * ε (s + k + 1)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right s k), hpo (s + k) _ _ (h.1 (s + k)), h.2.2.2.1, mul_zero,
    map_zero]

/-- Woodford (2003), p. 511: the variance of a future innovation,
`E_s ε²_{s+k+1} = σ²_{s+k+1}`. -/
theorem innov_E_eps_sq {ρ : ℝ} {sig2 : ℕ → ℝ} {u ε : ℕ → Ω → ℝ}
    (h : AR1Innov 𝔼 ρ sig2 u ε) (s k : ℕ) :
    𝔼.E s (ε (s + k + 1) * ε (s + k + 1)) = fun _ => sig2 (s + k + 1) := by
  rw [← 𝔼.tower (Nat.le_add_right s k), h.2.2.2.2, 𝔼.const]

/-- Woodford (2003), p. 511: future innovations have zero forecast, `E_s ε_{s+k+1} = 0`. -/
theorem innov_E_eps {ρ : ℝ} {sig2 : ℕ → ℝ} {u ε : ℕ → Ω → ℝ}
    (h : AR1Innov 𝔼 ρ sig2 u ε) (s k : ℕ) : 𝔼.E s (ε (s + k + 1)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right s k), h.2.2.2.1, map_zero]

/-- Woodford (2003), p. 511: the variance recursion
`var_s(u_{s+k+1}) = ρ² var_s(u_{s+k}) + σ²_{s+k+1}`. -/
theorem ar1_condVar_succ (hpo : 𝔼.PullOut) {ρ : ℝ} {sig2 : ℕ → ℝ} {u ε : ℕ → Ω → ℝ}
    (h : AR1Innov 𝔼 ρ sig2 u ε) (s k : ℕ) :
    condVar 𝔼 s (u (s + k + 1)) = ρ ^ 2 • condVar 𝔼 s (u (s + k)) + fun _ => sig2 (s + k + 1) := by
  have hsq : (ρ • u (s + k) + ε (s + k + 1)) * (ρ • u (s + k) + ε (s + k + 1)) =
      ρ ^ 2 • (u (s + k) * u (s + k)) + (2 * ρ) • (u (s + k) * ε (s + k + 1)) +
        ε (s + k + 1) * ε (s + k + 1) := by
    funext ω; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
  unfold condVar
  rw [h.2.2.1 (s + k), hsq, map_add, map_add, map_smul, map_smul, innov_E_u_eps 𝔼 hpo h,
    innov_E_eps_sq 𝔼 h, map_add, map_smul, innov_E_eps 𝔼 h]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply]
  ring

/-- Woodford (2003), p. 511: a variable known at `s` has zero conditional variance at `s`. -/
theorem condVar_known (hpo : 𝔼.PullOut) {s : ℕ} {X : Ω → ℝ} (hX : 𝔼.E s X = X) :
    condVar 𝔼 s X = 0 := by
  unfold condVar
  rw [hpo s X X hX, hX, sub_self]

/-- **Woodford (2003), p. 511** (the step behind (3.4)): for an AR(1) disturbance with constant
innovation variance `σ_ε²` and `ρ² ≠ 1`, `var_{t₀}(u_{t₀+k}) = σ_u²(1 − ρ^{2k})` with
`σ_u² = σ_ε²/(1 − ρ²)`. -/
theorem ar1_condVar_closed (hpo : 𝔼.PullOut) {ρ σε2 : ℝ} {sig2 : ℕ → ℝ} {u ε : ℕ → Ω → ℝ}
    (h : AR1Innov 𝔼 ρ sig2 u ε) (hsig : ∀ t, sig2 (t + 1) = σε2) (hρ : ρ ^ 2 ≠ 1) (s k : ℕ) :
    condVar 𝔼 s (u (s + k)) = fun _ => σε2 / (1 - ρ ^ 2) * (1 - ρ ^ (2 * k)) := by
  have h1 : 1 - ρ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  induction k with
  | zero =>
    rw [add_zero, condVar_known 𝔼 hpo (h.1 s)]
    funext ω
    simp
  | succ k ih =>
    rw [← add_assoc, ar1_condVar_succ 𝔼 hpo h, ih, hsig]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- Woodford (2003), p. 511: `σ_u² = σ_ε²/(1 − ρ²)` is the stationary (unconditional) variance:
`σ_u² = ρ²σ_u² + σ_ε²`. -/
theorem sigu2_fixed {ρ σε2 : ℝ} (hρ : ρ ^ 2 ≠ 1) :
    σε2 / (1 - ρ ^ 2) = ρ ^ 2 * (σε2 / (1 - ρ ^ 2)) + σε2 := by
  have h1 : 1 - ρ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  field_simp
  ring

/-- Woodford (2003), (3.4), p. 511: `∑_k βᵏ(1 − ρ^{2k}) = β(1 − ρ²)/((1 − β)(1 − βρ²))`. -/
theorem tsum_disc_one_sub {β ρ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : ρ ^ 2 < 1) :
    ∑' k : ℕ, β ^ k * (1 - ρ ^ (2 * k)) = β * (1 - ρ ^ 2) / ((1 - β) * (1 - β * ρ ^ 2)) := by
  have hb0 : 0 ≤ β * ρ ^ 2 := mul_nonneg hβ0 (sq_nonneg ρ)
  have hb1 : β * ρ ^ 2 < 1 := by
    calc β * ρ ^ 2 ≤ β * 1 := mul_le_mul_of_nonneg_left hρ.le hβ0
      _ < 1 := by linarith
  have h1 := summable_geometric_of_lt_one hβ0 hβ1
  have h2 := summable_geometric_of_lt_one hb0 hb1
  have heq : ∀ k : ℕ, β ^ k * (1 - ρ ^ (2 * k)) = β ^ k - (β * ρ ^ 2) ^ k := fun k => by
    rw [mul_pow, ← pow_mul, mul_comm 2 k]; ring
  simp only [heq]
  rw [h1.tsum_sub h2, tsum_geometric_of_lt_one hβ0 hβ1, tsum_geometric_of_lt_one hb0 hb1]
  have : (1 - β) ≠ 0 := by linarith
  have : (1 - β * ρ ^ 2) ≠ 0 := by linarith
  field_simp
  ring

/-- **Equation (3.4)** (Woodford (2003), p. 511): for a plan of the form (2.19) and an AR(1)
cost-push shock with constant innovation variance (`|ρ| < 1`), the stabilisation loss is
`L_stab = β/(1 − β) · (1 − ρ²)/(1 − βρ²) · (f_π² + λf_x²) σ_u²`, `σ_u² = σ_ε²/(1 − ρ²)`. -/
theorem Lstab_ar1 (hpo : 𝔼.PullOut) {β ρ σε2 lam pibar xbar fπ fx : ℝ} {sig2 : ℕ → ℝ}
    {u ε : ℕ → Ω → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ : ρ ^ 2 < 1)
    (h : AR1Innov 𝔼 ρ sig2 u ε) (hsig : ∀ t, sig2 (t + 1) = σε2) (s : ℕ) (ω : Ω) :
    ∑' k, β ^ k * (condVar 𝔼 s (fwdPlan pibar fπ u (s + k)) ω +
        lam * condVar 𝔼 s (fwdPlan xbar fx u (s + k)) ω) =
      β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
        (σε2 / (1 - ρ ^ 2)) := by
  have hρ1 : ρ ^ 2 ≠ 1 := hρ.ne
  have hterm : ∀ k, β ^ k * (condVar 𝔼 s (fwdPlan pibar fπ u (s + k)) ω +
      lam * condVar 𝔼 s (fwdPlan xbar fx u (s + k)) ω) =
      (fπ ^ 2 + lam * fx ^ 2) * (σε2 / (1 - ρ ^ 2)) * (β ^ k * (1 - ρ ^ (2 * k))) := by
    intro k
    rw [fwd_condVar, fwd_condVar, ar1_condVar_closed 𝔼 hpo h hsig hρ1]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hterm]
  rw [tsum_mul_left, tsum_disc_one_sub hβ0 hβ1 hρ]
  have : (1 - β) ≠ 0 := by linarith
  have : (1 - β * ρ ^ 2) ≠ 0 := by nlinarith [sq_nonneg ρ]
  field_simp

/-- Woodford (2003), (2.18) and (3.4): the innovation structure `AR1Innov` is satisfiable under
genuine uncertainty: in the coin-flip tree, `u_{t+1} = ρu_t + ε_{t+1}` with `ε = ±1` at dates 1
and 2 (innovation variances `1, 1, 0, 0, …`), and the tree has the pull-out property
(`ExpectationsFiniteTree.finiteTree_pullOut`). -/
theorem coin_AR1Innov (ρ : ℝ) :
    AR1Innov ExpectationsFiniteTree.coinSystem ρ (fun t => if t = 1 ∨ t = 2 then 1 else 0)
      (ExpectationsFiniteTree.coinAR1 ρ) ExpectationsFiniteTree.coinShock := by
  refine ⟨(ExpectationsFiniteTree.coinAR1_isAR1 ρ).1, fun t => ?_, fun t => ?_,
    ExpectationsFiniteTree.coinShock_mean_zero, fun t => ?_⟩
  · funext ω
    exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
      ExpectationsFiniteTree.coinShock_measurable t h
  · funext ω
    rfl
  · have hsq : ExpectationsFiniteTree.coinShock (t + 1) * ExpectationsFiniteTree.coinShock (t + 1)
        = fun _ => if t + 1 = 1 ∨ t + 1 = 2 then 1 else 0 := by
      funext ω
      simp only [Pi.mul_apply, ExpectationsFiniteTree.coinShock]
      rcases t with _ | _ | t
      · cases ω.1 <;> simp
      · cases ω.2 <;> simp
      · simp
    rw [hsq, ExpectationsFiniteTree.coinSystem.const]

/-! ### Two independent disturbances: (3.6)–(3.8) -/

/-- Woodford (2003), eq. (3.6), p. 512: the forward-looking plan `y_t = ȳ + f_y u_t + g_y r_t`
(with `r_t = rⁿ_t − r̄` the natural-rate deviation). -/
def plan2 (ybar f g : ℝ) (u r : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (fun _ => ybar) + f • u t + g • r t

/-- Woodford (2003), eq. (3.6), p. 512: the plan state by state,
`y_t(ω) = ȳ + f_y u_t(ω) + g_y r_t(ω)`. -/
@[simp] theorem plan2_apply (ybar f g : ℝ) (u r : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    plan2 ybar f g u r t ω = ybar + f * u t ω + g * r t ω := rfl

/-- Woodford (2003), p. 512: with independent innovations (`E_t ε^u_{t+1}ε^r_{t+1} = 0`), the
two AR(1) disturbances are conditionally uncorrelated: `cov_s(u_{s+k}, r_{s+k}) = 0`. -/
theorem condCov_zero (hpo : 𝔼.PullOut) {ρu ρr : ℝ} {su sr : ℕ → ℝ} {u εu r εr : ℕ → Ω → ℝ}
    (hu : AR1Innov 𝔼 ρu su u εu) (hr : AR1Innov 𝔼 ρr sr r εr)
    (hcross : ∀ t, 𝔼.E t (εu (t + 1) * εr (t + 1)) = 0) (s k : ℕ) :
    condCov 𝔼 s (u (s + k)) (r (s + k)) = 0 := by
  induction k with
  | zero =>
    unfold condCov
    rw [add_zero, hpo s _ _ (hu.1 s), hu.1 s, hr.1 s, sub_self]
  | succ k ih =>
    have hprod : (ρu • u (s + k) + εu (s + k + 1)) * (ρr • r (s + k) + εr (s + k + 1)) =
        (ρu * ρr) • (u (s + k) * r (s + k)) + ρu • (u (s + k) * εr (s + k + 1)) +
          ρr • (r (s + k) * εu (s + k + 1)) + εu (s + k + 1) * εr (s + k + 1) := by
      funext ω; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
    have hx : 𝔼.E s (εu (s + k + 1) * εr (s + k + 1)) = 0 := by
      rw [← 𝔼.tower (Nat.le_add_right s k), hcross, map_zero]
    unfold condCov at ih ⊢
    rw [← add_assoc, hu.2.2.1 (s + k), hr.2.2.1 (s + k), hprod, map_add, map_add, map_add,
      map_smul, map_smul, map_smul, hx, E_known_mul_innov 𝔼 hpo hu.1 hr.2.2.2.1,
      E_known_mul_innov 𝔼 hpo hr.1 hu.2.2.2.1,
      map_add, map_add, map_smul, map_smul, innov_E_eps 𝔼 hu, innov_E_eps 𝔼 hr]
    funext ω
    have h0 := congrFun ih ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at h0 ⊢
    linear_combination (ρu * ρr) * h0

/-- **Equations (3.7)–(3.8)** (Woodford (2003), pp. 512–513): for plans (3.6) and two AR(1)
disturbances with constant innovation variances and independent innovations, the stabilisation
loss with weights `1, λₓ, λᵢ` splits as `L_stab = L_stab,r + L_stab,u`, with
`L_stab,u = β/(1 − β)·(1 − ρᵤ²)/(1 − βρᵤ²)·(f_π² + λₓf_x² + λᵢf_i²)σ_u²` and
`L_stab,r = β/(1 − β)·(1 − ρᵣ²)/(1 − βρᵣ²)·(g_π² + λₓg_x² + λᵢg_i²)σ_r²`. -/
theorem Lstab_two_shocks (hpo : 𝔼.PullOut) {β ρu ρr σu2 σr2 lamx lami : ℝ} {su sr : ℕ → ℝ}
    {u εu r εr : ℕ → Ω → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρu : ρu ^ 2 < 1) (hρr : ρr ^ 2 < 1)
    (hu : AR1Innov 𝔼 ρu su u εu) (hr : AR1Innov 𝔼 ρr sr r εr)
    (hsu : ∀ t, su (t + 1) = σu2) (hsr : ∀ t, sr (t + 1) = σr2)
    (hcross : ∀ t, 𝔼.E t (εu (t + 1) * εr (t + 1)) = 0)
    (pibar xbar ibar fπ fx fi gπ gx gi : ℝ) (s : ℕ) (ω : Ω) :
    ∑' k, β ^ k * (condVar 𝔼 s (plan2 pibar fπ gπ u r (s + k)) ω +
        lamx * condVar 𝔼 s (plan2 xbar fx gx u r (s + k)) ω +
        lami * condVar 𝔼 s (plan2 ibar fi gi u r (s + k)) ω) =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lamx * gx ^ 2 + lami * gi ^ 2) *
          (σr2 / (1 - ρr ^ 2)) +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) *
          (fπ ^ 2 + lamx * fx ^ 2 + lami * fi ^ 2) * (σu2 / (1 - ρu ^ 2)) := by
  have hcv : ∀ ybar f g k, condVar 𝔼 s (plan2 ybar f g u r (s + k)) ω =
      f ^ 2 * (σu2 / (1 - ρu ^ 2) * (1 - ρu ^ (2 * k))) +
        g ^ 2 * (σr2 / (1 - ρr ^ 2) * (1 - ρr ^ (2 * k))) := by
    intro ybar f g k
    unfold plan2
    rw [condVar_affine2, condCov_zero 𝔼 hpo hu hr hcross, ar1_condVar_closed 𝔼 hpo hu hsu hρu.ne,
      ar1_condVar_closed 𝔼 hpo hr hsr hρr.ne]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, add_zero]
  have hsum : ∀ ρ : ℝ, ρ ^ 2 < 1 → Summable (fun k : ℕ => β ^ k * (1 - ρ ^ (2 * k))) := by
    intro ρ hρ
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hβ0 k) ?_) (fun k => ?_)
      (summable_geometric_of_lt_one hβ0 hβ1)
    · rw [pow_mul]; linarith [pow_le_one₀ (sq_nonneg ρ) hρ.le (n := k)]
    · rw [pow_mul]
      have := pow_nonneg (sq_nonneg ρ) k
      nlinarith [pow_nonneg hβ0 k]
  have hterm : ∀ k, β ^ k * (condVar 𝔼 s (plan2 pibar fπ gπ u r (s + k)) ω +
      lamx * condVar 𝔼 s (plan2 xbar fx gx u r (s + k)) ω +
      lami * condVar 𝔼 s (plan2 ibar fi gi u r (s + k)) ω) =
      (gπ ^ 2 + lamx * gx ^ 2 + lami * gi ^ 2) * (σr2 / (1 - ρr ^ 2)) *
          (β ^ k * (1 - ρr ^ (2 * k))) +
        (fπ ^ 2 + lamx * fx ^ 2 + lami * fi ^ 2) * (σu2 / (1 - ρu ^ 2)) *
          (β ^ k * (1 - ρu ^ (2 * k))) := by
    intro k
    rw [hcv, hcv, hcv]
    ring
  simp only [hterm]
  rw [((hsum ρr hρr).mul_left _).tsum_add ((hsum ρu hρu).mul_left _), tsum_mul_left,
    tsum_mul_left, tsum_disc_one_sub hβ0 hβ1 hρr, tsum_disc_one_sub hβ0 hβ1 hρu]
  have : (1 - β) ≠ 0 := by linarith
  have : (1 - β * ρu ^ 2) ≠ 0 := by nlinarith [sq_nonneg ρu]
  have : (1 - β * ρr ^ 2) ≠ 0 := by nlinarith [sq_nonneg ρr]
  field_simp

/-- Woodford (2003), eq. (2.23), p. 502: the intertemporal IS relation
`x_t = E_t x_{t+1} − σ(i_t − E_t π_{t+1} − rⁿ_t)`, with `rⁿ_t = r̄ + r_t`. -/
def IS (σ rbar : ℝ) (r π x i : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1)) - ((fun _ => rbar) + r t))

/-- Woodford (2003), p. 512: if `1`, `u_t`, `r_t` are linearly independent (as functions of
date and state), a vanishing linear combination has zero coefficients. -/
theorem lin3_iff {u r : ℕ → Ω → ℝ}
    (hind : ∀ a b c : ℝ, (∀ t ω, a + b * u t ω + c * r t ω = 0) → a = 0 ∧ b = 0 ∧ c = 0)
    (a b c : ℝ) : (∀ t ω, a + b * u t ω + c * r t ω = 0) ↔ (a = 0 ∧ b = 0 ∧ c = 0) :=
  ⟨hind a b c, fun ⟨ha, hb, hc⟩ t ω => by rw [ha, hb, hc]; ring⟩

/-- Woodford (2003), p. 512: the one-step forecast of a plan (3.6) under AR(1) disturbances. -/
theorem E_plan2 {ρu ρr : ℝ} {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r)
    (ybar f g : ℝ) (t : ℕ) :
    𝔼.E t (plan2 ybar f g u r (t + 1)) = (fun _ => ybar) + (f * ρu) • u t + (g * ρr) • r t := by
  unfold plan2
  rw [map_add, map_add, map_smul, map_smul, 𝔼.const, hu.2 t, hr.2 t, smul_smul, smul_smul]

/-- **Woodford (2003), (3.6), p. 512** ("the equilibrium relations (2.1) and (2.23) imply two
linear restrictions on the coefficients `f_y` and another two on the `g_y`"): for AR(1)
disturbances `u`, `r` with `1, u, r` linearly independent and `σ ≠ 0`, the plans (3.6) for
`π, x, i` satisfy (2.1) and (2.23) iff
`(1 − β)π̄ = κx̄`, `ī = π̄ + r̄`, `(1 − βρᵤ)f_π = κf_x + 1`, `(1 − ρᵤ)f_x = −σ(f_i − ρᵤf_π)`,
`(1 − βρᵣ)g_π = κg_x`, `(1 − ρᵣ)g_x = −σ(g_i − ρᵣg_π − 1)`. -/
theorem two_shock_RE_iff {β κ σ rbar ρu ρr pibar xbar ibar fπ fx fi gπ gx gi : ℝ}
    {u r : ℕ → Ω → ℝ} (hσ : σ ≠ 0) (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r)
    (hind : ∀ a b c : ℝ, (∀ t ω, a + b * u t ω + c * r t ω = 0) → a = 0 ∧ b = 0 ∧ c = 0) :
    (AS 𝔼 β κ u (plan2 pibar fπ gπ u r) (plan2 xbar fx gx u r) ∧
      IS 𝔼 σ rbar r (plan2 pibar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)) ↔
      ((1 - β) * pibar = κ * xbar ∧ ibar = pibar + rbar) ∧
        ((1 - β * ρu) * fπ = κ * fx + 1 ∧ (1 - ρu) * fx = -σ * (fi - ρu * fπ)) ∧
        ((1 - β * ρr) * gπ = κ * gx ∧ (1 - ρr) * gx = -σ * (gi - ρr * gπ - 1)) := by
  have hAS : AS 𝔼 β κ u (plan2 pibar fπ gπ u r) (plan2 xbar fx gx u r) ↔
      ∀ t ω, ((1 - β) * pibar - κ * xbar) + ((1 - β * ρu) * fπ - κ * fx - 1) * u t ω +
        ((1 - β * ρr) * gπ - κ * gx) * r t ω = 0 := by
    unfold AS
    refine forall_congr' fun t => ?_
    rw [E_plan2 𝔼 hu hr, funext_iff]
    refine forall_congr' fun ω => ?_
    unfold plan2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> intro h <;> linarith
  have hIS : IS 𝔼 σ rbar r (plan2 pibar fπ gπ u r) (plan2 xbar fx gx u r)
      (plan2 ibar fi gi u r) ↔
      ∀ t ω, (σ * (ibar - pibar - rbar)) + ((1 - ρu) * fx + σ * (fi - ρu * fπ)) * u t ω +
        ((1 - ρr) * gx + σ * (gi - ρr * gπ - 1)) * r t ω = 0 := by
    unfold IS
    refine forall_congr' fun t => ?_
    rw [E_plan2 𝔼 hu hr, E_plan2 𝔼 hu hr, funext_iff]
    refine forall_congr' fun ω => ?_
    unfold plan2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    constructor <;> intro h <;> linarith
  rw [hAS, hIS, lin3_iff hind, lin3_iff hind]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩
    have h4' : ibar - pibar - rbar = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h hσ
      · exact h
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    refine ⟨⟨by linarith, by linarith, by linarith⟩, ?_, by linarith, by linarith⟩
    rw [show ibar - pibar - rbar = 0 by linarith, mul_zero]

end Woodford.GainsFromCommitment.VarianceFrontier
