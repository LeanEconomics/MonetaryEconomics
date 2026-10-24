/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.MonetaryFrictions

/-!
# Inflation inertia: indexation to lagged inflation

Woodford (2003), *Interest and Prices*, Chapter 7, §1.2, pp. 480–484.

With prices indexed to lagged inflation, (1.1) becomes (1.21) and the loss becomes (1.22), both
in the quasi-difference `π^qd_t = π_t − γπ_{t−1}`. The book's statements hold up to an error of
order `O(‖Δ_{-1}^{1/2}, π_{−1}‖²)` (the Chapter 6 approximation); the exact linear-quadratic
problem is proved here.

## The change of variables (p. 481)
* `qd`, `unqd` (`π_t = γ^{t+1}π_{−1} + ∑_{s ≤ t} γ^{t−s}π^qd_s`), `qd_unqd`, `unqd_qd`, the
  bijection `qdEquiv`, `unqd_split` (`π_{−1}γ^{t+1}` plus a term independent of the initial
  condition), `unqd_add_smul`; boundedness `bdd_qd`, `bdd_unqd` (`γ < 1`), and
  `not_bdd_unqd_one` (fails at `γ = 1`).
* `ASind` (1.21), `lossInd` (1.22), `asInd_iff`, `lossInd_eq` (they are (1.1), (1.2) for
  `π^qd`; `cashless`), `transport_min` (optimality is transported both ways).

## Proposition 7.4 (pp. 482–483)
* `dsum_x_eq`, `cashless_loss_decomp` (the p. 473 identity with general `λ`),
  `cashless_timeless_min`, `cashless_timeless_unique` (Proposition 7.2, restated).
* **Proposition 7.4**: `prop_7_4` (from any date `t₀`, given the history), `prop_7_4_unique`,
  `prop_7_4_rule`; `rule_123_iff` (`π_t = γπ_{t−1}` iff `π_t = π_{−1}γ^{t+1}`),
  `tendsto_rule_path`, `rule_path_full_indexation`; the precise definition `TimelessInd` and
  `timelessInd_iff` (the rule `π_t − γπ_{t−1} = c` is timelessly optimal iff `c = 0`).
* Under uncertainty: `ASindS`, `prop_7_4_uncertainty`.

## Indexation with transactions frictions (pp. 483–484)
* `IModel`, `ASi`, `ISi`, `lossI`, `lagrI`, the exact expansion `lagrI_expand`, and the FOCs as
  exact derivatives `hasDerivAt_lagrI_pi` (the **corrected** generalised (1.16), `focPiI`),
  `hasDerivAt_lagrI_x`, `hasDerivAt_lagrI_i`.
* **Error E3** (p. 483): the printed FOC `focPiPrinted` omits `βγφ_{2t} − βγφ_{2,t+1}`:
  `focPiI_sub_printed`, counterexample `printed_foc_not_derivative`.
* The long-run rate (p. 484): `SSCondI`, `focI_const_iff`, `constI_feasible_iff`, `ss_ind_iff`
  (`π̄ = −λ_i(r̄ − iᵐ)/(λ_i + β(1 − γ)(1 − βγ))`), `piBar_ind_neg`, `piBar_ind_gamma_one`
  (`γ = 1` gives the Friedman rate, independent of `λ_i`), `ssCondI_cashless_iff` (with
  `λ_i = 0` determinate only when `γ ≠ 1`), and optimality `ss_ind_optimal`.
-/

namespace Woodford.GainsFromCommitment.Indexation

open Filter Topology Woodford.GainsFromCommitment.MonetaryFrictions
open Sequences

/-! ### The change of variables `π^qd_t = π_t − γπ_{t−1}` -/

/-- Woodford (2003), p. 481: quasi-differenced inflation `π^qd_t = π_t − γπ_{t−1}`, with the
pre-sample inflation rate `π_{−1}` given. -/
def qd (γ πm1 : ℝ) (π : ℕ → ℝ) : ℕ → ℝ := fun t => π t - γ * lagged πm1 π t

/-- Woodford (2003), p. 481: the inverse change of variables,
`π_t = γ^{t+1}π_{−1} + ∑_{s ≤ t} γ^{t−s} π^qd_s`. -/
def unqd (γ πm1 : ℝ) (q : ℕ → ℝ) : ℕ → ℝ :=
  fun t => γ ^ (t + 1) * πm1 + ∑ s ∈ Finset.range (t + 1), γ ^ (t - s) * q s

/-- Woodford (2003), p. 481: `π_0 = γπ_{−1} + π^qd_0`. -/
theorem unqd_zero (γ πm1 : ℝ) (q : ℕ → ℝ) : unqd γ πm1 q 0 = γ * πm1 + q 0 := by
  simp [unqd]

/-- Woodford (2003), p. 481: `π_{t+1} = γπ_t + π^qd_{t+1}`. -/
theorem unqd_succ (γ πm1 : ℝ) (q : ℕ → ℝ) (t : ℕ) :
    unqd γ πm1 q (t + 1) = γ * unqd γ πm1 q t + q (t + 1) := by
  unfold unqd
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
  have h : ∑ s ∈ Finset.range (t + 1), γ ^ (t + 1 - s) * q s =
      γ * ∑ s ∈ Finset.range (t + 1), γ ^ (t - s) * q s := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' : t + 1 - s = (t - s) + 1 := by
      have := Finset.mem_range.mp hs
      omega
    rw [hs', pow_succ]
    ring
  rw [h]
  ring

/-- Woodford (2003), p. 481: `qd ∘ unqd = id` (every path of `π^qd` comes from an inflation
path). -/
theorem qd_unqd (γ πm1 : ℝ) (q : ℕ → ℝ) : qd γ πm1 (unqd γ πm1 q) = q := by
  funext t
  cases t with
  | zero => simp [qd, unqd_zero]
  | succ n => simp [qd, unqd_succ]

/-- Woodford (2003), p. 481: `unqd ∘ qd = id` (an inflation path is recovered from its
quasi-differences and `π_{−1}`). -/
theorem unqd_qd (γ πm1 : ℝ) (π : ℕ → ℝ) : unqd γ πm1 (qd γ πm1 π) = π := by
  funext t
  induction t with
  | zero => simp [unqd_zero, qd]
  | succ n ih => rw [unqd_succ, ih]; simp [qd]

/-- Woodford (2003), p. 481: given `π_{−1}`, the change of variables `π ↦ π^qd` is a bijection
of paths. -/
def qdEquiv (γ πm1 : ℝ) : (ℕ → ℝ) ≃ (ℕ → ℝ) :=
  ⟨qd γ πm1, unqd γ πm1, unqd_qd γ πm1, qd_unqd γ πm1⟩

/-- Woodford (2003), p. 481: "the equilibrium value of `π_t` is given by `π_{−1}γ^{t+1}` plus a
term that is independent of the initial condition": for any path of `π^qd`,
`π_t = γ^{t+1}π_{−1} + (the path generated from π_{−1} = 0)`. -/
theorem unqd_split (γ πm1 : ℝ) (q : ℕ → ℝ) (t : ℕ) :
    unqd γ πm1 q t = γ ^ (t + 1) * πm1 + unqd γ 0 q t := by
  simp [unqd]

/-- Woodford (2003), p. 481: the inverse change of variables is linear in `(π_{−1}, π^qd)`. -/
theorem unqd_add_smul (γ πm1 πm1' ε : ℝ) (q q' : ℕ → ℝ) :
    unqd γ (πm1 + ε * πm1') (fun t => q t + ε * q' t) =
      fun t => unqd γ πm1 q t + ε * unqd γ πm1' q' t := by
  funext t
  simp only [unqd]
  have h : ∑ s ∈ Finset.range (t + 1), γ ^ (t - s) * (q s + ε * q' s) =
      ∑ s ∈ Finset.range (t + 1), γ ^ (t - s) * q s +
        ε * ∑ s ∈ Finset.range (t + 1), γ ^ (t - s) * q' s := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    ring
  rw [h]
  ring

/-- Woodford (2003), p. 481: a bounded inflation path has bounded quasi-differences. -/
theorem bdd_qd {γ πm1 : ℝ} {π : ℕ → ℝ} (h : Bdd π) : Bdd (qd γ πm1 π) :=
  h.sub ((bdd_const γ).mul (h.lag πm1))

/-- Woodford (2003), p. 481: for `0 ≤ γ < 1` bounded quasi-differences give a bounded inflation
path. -/
theorem bdd_unqd {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (πm1 : ℝ) {q : ℕ → ℝ} (h : Bdd q) :
    Bdd (unqd γ πm1 q) := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨|πm1| + C * (1 - γ)⁻¹, fun t => ?_⟩
  unfold unqd
  have h1 : |γ ^ (t + 1) * πm1| ≤ |πm1| := by
    rw [abs_mul, abs_pow, abs_of_nonneg hγ0]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hγ0 hγ1.le)
  have h2 : |∑ s ∈ Finset.range (t + 1), γ ^ (t - s) * q s| ≤ C * (1 - γ)⁻¹ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h3 : ∑ s ∈ Finset.range (t + 1), |γ ^ (t - s) * q s| ≤
        ∑ s ∈ Finset.range (t + 1), C * γ ^ (t - s) := by
      refine Finset.sum_le_sum (fun s _ => ?_)
      rw [abs_mul, abs_pow, abs_of_nonneg hγ0, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC s) (pow_nonneg hγ0 _)
    refine h3.trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    have hr := Finset.sum_range_reflect (fun k => γ ^ k) (t + 1)
    simp only [Nat.add_sub_cancel] at hr
    rw [hr, ← tsum_geometric_of_lt_one hγ0 hγ1]
    exact (summable_geometric_of_lt_one hγ0 hγ1).sum_le_tsum _
      (fun k _ => pow_nonneg hγ0 k)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Woodford (2003), p. 481 (why `γ = 1` is special): with full indexation bounded
quasi-differences need not give bounded inflation — `π^qd ≡ 1`, `π_{−1} = 0` gives
`π_t = t + 1`. -/
theorem not_bdd_unqd_one : ¬ Bdd (unqd 1 0 (fun _ => 1)) := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have h := hC n
  have e : unqd 1 0 (fun _ => 1) n = n + 1 := by simp [unqd]
  rw [e] at h
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_of_nonneg (by linarith)] at h
  linarith

/-- Woodford (2003), p. 481: for `0 ≤ γ ≤ 1` the path `π_t = γ^{t+1}π_{−1}` (zero
quasi-differences) is bounded. -/
theorem bdd_unqd_zero {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (πm1 : ℝ) :
    Bdd (unqd γ πm1 (fun _ => 0)) := by
  refine ⟨|πm1|, fun t => ?_⟩
  simp only [unqd, mul_zero, Finset.sum_const_zero, add_zero, abs_mul, abs_pow,
    abs_of_nonneg hγ0]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hγ0 hγ1)

/-- Woodford (2003), (1.23), p. 482 and p. 483: `π_t = γπ_{t−1}` for all `t ≥ 0` iff
`π_t = π_{−1}γ^{t+1}` for all `t`. -/
theorem rule_123_iff (γ πm1 : ℝ) (π : ℕ → ℝ) :
    (∀ t, π t = γ * lagged πm1 π t) ↔ ∀ t, π t = γ ^ (t + 1) * πm1 := by
  constructor
  · intro h t
    have hq : qd γ πm1 π = fun _ => 0 := by
      funext s; simp only [qd]; rw [h s]; ring
    have := congrFun (unqd_qd γ πm1 π) t
    rw [hq] at this
    rw [← this]
    simp [unqd]
  · intro h t
    cases t with
    | zero => rw [h 0, lagged_zero]; ring
    | succ n => rw [h (n + 1), lagged_succ, h n]; ring

/-! ### The indexation model (1.21)–(1.22) and its reduction to (1.1)–(1.2) -/

/-- Woodford (2003), §1.1–1.2: the cashless model (1.1)–(1.2) as an instance of
`MonetaryFrictions.Model` with no interest-rate term (`λ_i = 0`, `ϕ = 0`). -/
def cashless (β κ lam xstar : ℝ) : Model :=
  { β := β, κ := κ, σ := 1, ϕ := 0, a := 1, b := 0, rbar := 0, lamx := lam, lami := 0,
    xstar := xstar, im := 0 }

/-- Woodford (2003), eq. (1.1), p. 469: `q_t = κx_t + βq_{t+1}` is the aggregate-supply relation
of `cashless`. -/
theorem cashless_AS_iff (β κ lam xstar : ℝ) (q x i : ℕ → ℝ) (t : ℕ) :
    AS (cashless β κ lam xstar) q x i t ↔ q t = κ * x t + β * q (t + 1) := by
  simp [AS, cashless]

/-- Woodford (2003), eq. (1.2), p. 469: the loss of `cashless` is
`∑βᵗ[q_t² + λ(x_t − x*)²]` (independent of the unused interest-rate path). -/
theorem cashless_loss (β κ lam xstar : ℝ) (q x i : ℕ → ℝ) :
    loss (cashless β κ lam xstar) q x i =
      dsum β (fun t => q t ^ 2 + lam * (x t - xstar) ^ 2) := by
  unfold loss
  congr 1
  funext t
  simp [periodLoss, cashless]

/-- Woodford (2003), eq. (1.21), p. 481: the aggregate-supply relation with indexation,
`π_t − γπ_{t−1} = κx_t + β(π_{t+1} − γπ_t)`. -/
def ASind (β κ γ πm1 : ℝ) (π x : ℕ → ℝ) (t : ℕ) : Prop :=
  π t - γ * lagged πm1 π t = κ * x t + β * (π (t + 1) - γ * π t)

/-- Woodford (2003), eq. (1.22), p. 481: the loss with indexation,
`∑βᵗ[(π_t − γπ_{t−1})² + λ(x_t − x*)²]`. -/
noncomputable def lossInd (β γ lam xstar πm1 : ℝ) (π x : ℕ → ℝ) : ℝ :=
  dsum β (fun t => (π t - γ * lagged πm1 π t) ^ 2 + lam * (x t - xstar) ^ 2)

/-- Woodford (2003), p. 481: (1.21) for `π` is exactly (1.1) for `π^qd`. -/
theorem asInd_iff (β κ γ πm1 lam xstar : ℝ) (π x i : ℕ → ℝ) (t : ℕ) :
    ASind β κ γ πm1 π x t ↔ AS (cashless β κ lam xstar) (qd γ πm1 π) x i t := by
  rw [cashless_AS_iff]
  simp [ASind, qd]

/-- Woodford (2003), p. 481: (1.22) for `π` is exactly (1.2) for `π^qd`. -/
theorem lossInd_eq (β κ γ lam xstar πm1 : ℝ) (π x i : ℕ → ℝ) :
    lossInd β γ lam xstar πm1 π x = loss (cashless β κ lam xstar) (qd γ πm1 π) x i := by
  rw [cashless_loss]
  rfl

/-- Woodford (2003), p. 481 ("the same calculations as before may be used directly"): for
`0 ≤ γ < 1` and any restriction `R` on the quasi-differenced plan, an inflation path minimises
(1.22) subject to (1.21) and `R` among bounded paths iff its quasi-difference minimises (1.2)
subject to (1.1) and `R` among bounded paths. -/
theorem transport_min {β κ γ lam xstar πm1 : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (R : (ℕ → ℝ) → (ℕ → ℝ) → Prop) (π x : ℕ → ℝ) :
    (∀ π' x', Bdd π' → Bdd x' → (∀ t, ASind β κ γ πm1 π' x' t) → R (qd γ πm1 π') x' →
        lossInd β γ lam xstar πm1 π x ≤ lossInd β γ lam xstar πm1 π' x') ↔
      (∀ q' x', Bdd q' → Bdd x' → (∀ t, AS (cashless β κ lam xstar) q' x' 0 t) → R q' x' →
        loss (cashless β κ lam xstar) (qd γ πm1 π) x 0 ≤
          loss (cashless β κ lam xstar) q' x' 0) := by
  constructor
  · intro h q' x' hq hx hAS hR
    have e := h (unqd γ πm1 q') x' (bdd_unqd hγ0 hγ1 πm1 hq) hx
      (fun t => (asInd_iff β κ γ πm1 lam xstar _ x' 0 t).mpr (by rw [qd_unqd]; exact hAS t))
      (by rw [qd_unqd]; exact hR)
    rw [lossInd_eq β κ γ lam xstar πm1 _ _ 0, lossInd_eq β κ γ lam xstar πm1 _ _ 0,
      qd_unqd] at e
    exact e
  · intro h π' x' hπ hx hAS hR
    rw [lossInd_eq β κ γ lam xstar πm1 _ _ 0, lossInd_eq β κ γ lam xstar πm1 _ _ 0]
    exact h _ x' (bdd_qd hπ) hx (fun t => (asInd_iff β κ γ πm1 lam xstar π' x' 0 t).mp (hAS t))
      hR

/-! ### Optimality from a timeless perspective with inflation inertia: Proposition 7.4 -/

/-- Woodford (2003), p. 473 (summation of (1.1)): if `q_t = κx_t + βq_{t+1}` for bounded `q, x`,
then `∑βᵗx_t = q_0/κ`. -/
theorem dsum_x_eq {β κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) {q x : ℕ → ℝ}
    (hq : Bdd q) (hAS : ∀ t, q t = κ * x t + β * q (t + 1)) : dsum β x = q 0 / κ := by
  have hx : x = fun t => κ⁻¹ * (q t - β * q (t + 1)) := by
    funext t
    rw [hAS t]
    field_simp
    ring
  have hs := dsum_shift hβ0 hβ1 hq (h := fun t => q (t + 1)) (fun _ => rfl)
  rw [hx, dsum_mul_left, dsum_sub hβ0.le hβ1 hq ((bdd_const β).mul hq.shift), dsum_mul_left,
    hs]
  field_simp
  ring

/-- Woodford (2003), (1.14), p. 476: the discounted sum is monotone on bounded sequences. -/
theorem dsum_le_dsum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → ℝ} (hf : Bdd f)
    (hg : Bdd g) (h : ∀ t, f t ≤ g t) : dsum β f ≤ dsum β g :=
  Summable.tsum_le_tsum (fun t => mul_le_mul_of_nonneg_left (h t) (pow_nonneg hβ0 t))
    (summable_dsum hβ0 hβ1 hf) (summable_dsum hβ0 hβ1 hg)

/-- Woodford (2003), p. 473 (with `λ = κ/θ` replaced by a general weight, cf. survey E1): along
any bounded path satisfying (1.1), the loss (1.2) equals
`−2(λ/κ)x*q_0 + ∑βᵗ(q_t² + λx_t²) + λx*²/(1 − β)`. -/
theorem cashless_loss_decomp {β κ lam xstar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    {q x : ℕ → ℝ} (hq : Bdd q) (hx : Bdd x) (hAS : ∀ t, q t = κ * x t + β * q (t + 1)) :
    dsum β (fun t => q t ^ 2 + lam * (x t - xstar) ^ 2) =
      -2 * (lam / κ) * xstar * q 0 + dsum β (fun t => q t ^ 2 + lam * x t ^ 2) +
        lam * xstar ^ 2 / (1 - β) := by
  have h : (fun t => q t ^ 2 + lam * (x t - xstar) ^ 2) = fun t =>
      (q t ^ 2 + lam * x t ^ 2) + ((-2 * lam * xstar) * x t + lam * xstar ^ 2) := by
    funext t
    ring
  have hb : Bdd (fun t => q t ^ 2 + lam * x t ^ 2) := hq.sq.add ((bdd_const lam).mul hx.sq)
  rw [h, dsum_add hβ0.le hβ1 hb (((bdd_const _).mul hx).add (bdd_const _)),
    dsum_add hβ0.le hβ1 ((bdd_const _).mul hx) (bdd_const _), dsum_mul_left,
    dsum_x_eq hβ0 hβ1 hκ hq hAS, dsum_const hβ0.le hβ1]
  field_simp
  ring

/-- Woodford (2003), Proposition 7.2 (restated for the reduction, p. 475, exact LQ form): in the
cashless model every bounded plan satisfying (1.1) with `q_0 = 0` has loss (1.2) at least
`λx*²/(1 − β)`, the loss of the zero-inflation plan `q ≡ 0`, `x ≡ 0` (`λ ≥ 0`). -/
theorem cashless_timeless_min {β κ lam xstar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hlam : 0 ≤ lam) {q x : ℕ → ℝ} (hq : Bdd q) (hx : Bdd x)
    (hAS : ∀ t, q t = κ * x t + β * q (t + 1)) (h0 : q 0 = 0) :
    lam * xstar ^ 2 / (1 - β) ≤ dsum β (fun t => q t ^ 2 + lam * (x t - xstar) ^ 2) := by
  rw [cashless_loss_decomp hβ0 hβ1 hκ hq hx hAS, h0]
  have := dsum_nonneg hβ0.le (f := fun t => q t ^ 2 + lam * x t ^ 2)
    (fun t => add_nonneg (sq_nonneg _) (mul_nonneg hlam (sq_nonneg _)))
  linarith

/-- Woodford (2003), Proposition 7.2 (uniqueness, p. 475): with `λ > 0` the zero-inflation plan
is the unique minimiser: a bounded plan satisfying (1.1) with `q_0 = 0` and loss at most
`λx*²/(1 − β)` has `q ≡ 0` and `x ≡ 0`. -/
theorem cashless_timeless_unique {β κ lam xstar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : κ ≠ 0) (hlam : 0 < lam) {q x : ℕ → ℝ} (hq : Bdd q) (hx : Bdd x)
    (hAS : ∀ t, q t = κ * x t + β * q (t + 1)) (h0 : q 0 = 0)
    (hle : dsum β (fun t => q t ^ 2 + lam * (x t - xstar) ^ 2) ≤ lam * xstar ^ 2 / (1 - β)) :
    q = 0 ∧ x = 0 := by
  rw [cashless_loss_decomp hβ0 hβ1 hκ hq hx hAS, h0] at hle
  have hnn : ∀ t, 0 ≤ q t ^ 2 + lam * x t ^ 2 :=
    fun t => add_nonneg (sq_nonneg _) (mul_nonneg hlam.le (sq_nonneg _))
  have hz : dsum β (fun t => q t ^ 2 + lam * x t ^ 2) = 0 :=
    le_antisymm (by linarith) (dsum_nonneg hβ0.le hnn)
  rw [dsum_eq_zero_iff hβ0 hβ1 (hq.sq.add ((bdd_const lam).mul hx.sq)) hnn] at hz
  have hall : ∀ t, q t = 0 ∧ x t = 0 := by
    intro t
    have e := hz t
    have a1 := sq_nonneg (q t)
    have a2 := mul_nonneg hlam.le (sq_nonneg (x t))
    have e1 : q t ^ 2 = 0 := by linarith
    have e2 : lam * x t ^ 2 = 0 := by linarith
    exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1,
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp e2).resolve_left hlam.ne')⟩
  exact ⟨funext fun t => (hall t).1, funext fun t => (hall t).2⟩

/-- Woodford (2003), Proposition 7.4, pp. 482–483 (exact LQ form, from any date `t₀`): given the
inflation history (`π_{−1}` and the plan's values before `t₀`), every bounded plan satisfying
(1.21) from `t₀` on and the constraint that (1.23) hold in period `t₀`, `π_{t₀} = γπ_{t₀−1}`,
has discounted loss (1.22) from `t₀` on at least `λx*²/(1 − β)` (`0 < β < 1`, `κ ≠ 0`,
`λ ≥ 0`). -/
theorem prop_7_4 {β κ γ lam xstar πm1 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hlam : 0 ≤ lam) (t0 : ℕ) {π x : ℕ → ℝ} (hπ : Bdd π) (hx : Bdd x)
    (hfeas : ∀ t, t0 ≤ t → ASind β κ γ πm1 π x t) (h0 : π t0 = γ * lagged πm1 π t0) :
    lam * xstar ^ 2 / (1 - β) ≤ dsum β (fun t => (π (t0 + t) - γ * lagged πm1 π (t0 + t)) ^ 2 +
      lam * (x (t0 + t) - xstar) ^ 2) := by
  refine cashless_timeless_min (q := fun t => qd γ πm1 π (t0 + t)) hβ0 hβ1 hκ hlam
    ((bdd_qd hπ).drop t0) (hx.drop t0) (fun t => ?_) (by simp [qd, h0])
  have h := hfeas (t0 + t) (Nat.le_add_right t0 t)
  unfold ASind at h
  simp only [qd, ← add_assoc, lagged_succ]
  exact h

/-- Woodford (2003), Proposition 7.4 (uniqueness): with `λ > 0`, a plan as in `prop_7_4` whose
loss from `t₀` on is at most `λx*²/(1 − β)` satisfies the rule (1.23), `π_t = γπ_{t−1}`, and has
`x_t = 0`, at every date `t ≥ t₀`. -/
theorem prop_7_4_unique {β κ γ lam xstar πm1 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hlam : 0 < lam) (t0 : ℕ) {π x : ℕ → ℝ} (hπ : Bdd π) (hx : Bdd x)
    (hfeas : ∀ t, t0 ≤ t → ASind β κ γ πm1 π x t) (h0 : π t0 = γ * lagged πm1 π t0)
    (hle : dsum β (fun t => (π (t0 + t) - γ * lagged πm1 π (t0 + t)) ^ 2 +
      lam * (x (t0 + t) - xstar) ^ 2) ≤ lam * xstar ^ 2 / (1 - β)) :
    ∀ t, t0 ≤ t → π t = γ * lagged πm1 π t ∧ x t = 0 := by
  have h := cashless_timeless_unique (q := fun t => qd γ πm1 π (t0 + t)) hβ0 hβ1 hκ hlam
    ((bdd_qd hπ).drop t0) (hx.drop t0) (fun t => by
      have h := hfeas (t0 + t) (Nat.le_add_right t0 t)
      unfold ASind at h
      simp only [qd, ← add_assoc, lagged_succ]
      exact h) (by simp [qd, h0]) hle
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  have e1 := congrFun h.1 k
  have e2 := congrFun h.2 k
  simp only [qd, Pi.zero_apply] at e1 e2
  exact ⟨by linarith, e2⟩

/-- Woodford (2003), Proposition 7.4 (attainment): a plan following the rule (1.23) with `x_t = 0`
from `t₀` on satisfies (1.21) from `t₀` on and has loss exactly `λx*²/(1 − β)` from `t₀` on. -/
theorem prop_7_4_rule {β κ γ lam xstar πm1 : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (t0 : ℕ)
    {π x : ℕ → ℝ} (hrule : ∀ t, t0 ≤ t → π t = γ * lagged πm1 π t)
    (hx0 : ∀ t, t0 ≤ t → x t = 0) :
    (∀ t, t0 ≤ t → ASind β κ γ πm1 π x t) ∧
      dsum β (fun t => (π (t0 + t) - γ * lagged πm1 π (t0 + t)) ^ 2 +
        lam * (x (t0 + t) - xstar) ^ 2) = lam * xstar ^ 2 / (1 - β) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · unfold ASind
    rw [hx0 t ht]
    have h1 := hrule t ht
    have h2 := hrule (t + 1) (by omega)
    rw [lagged_succ] at h2
    rw [h2]
    linarith
  · have h : (fun t => (π (t0 + t) - γ * lagged πm1 π (t0 + t)) ^ 2 +
        lam * (x (t0 + t) - xstar) ^ 2) = fun _ => lam * xstar ^ 2 := by
      funext t
      rw [hrule (t0 + t) (Nat.le_add_right _ _), hx0 (t0 + t) (Nat.le_add_right _ _)]
      ring
    rw [h, dsum_const hβ0 hβ1]

/-- Woodford (2003), p. 483: for `0 ≤ γ < 1` the timelessly optimal inflation path
`π_t = π_{−1}γ^{t+1}` converges to zero ("the optimal long-run inflation rate is zero; but it is
now optimal to approach this inflation rate only over a period of time"). -/
theorem tendsto_rule_path {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (πm1 : ℝ) :
    Tendsto (fun t : ℕ => γ ^ (t + 1) * πm1) atTop (𝓝 0) := by
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).comp
    (tendsto_add_atTop_nat 1)).mul_const πm1
  simpa using h

/-- Woodford (2003), p. 483: with full indexation (`γ = 1`) the timelessly optimal path keeps
inflation at its initial level, `π_t = π_{−1}` ("it is not optimal ever to reduce inflation"). -/
theorem rule_path_full_indexation (πm1 : ℝ) (π : ℕ → ℝ)
    (h : ∀ t, π t = 1 * lagged πm1 π t) : ∀ t, π t = πm1 := by
  intro t
  rw [(rule_123_iff 1 πm1 π).mp h t, one_pow, one_mul]

/-- Woodford (2003), p. 482 (precise definition): the stationary rule `π_t − γπ_{t−1} = c`
(output gap `x̄ = (1 − β)c/κ`) is *optimal from a timeless perspective* if for every pre-sample
inflation rate `π_{−1}` the path it generates is bounded and minimises (1.22) among bounded
plans satisfying (1.21) with the initial constraint `π_0 = γπ_{−1} + c` that the rule hold at
date 0. (By time-invariance the date-`t₀` problem given the history is the date-0 problem with
`π_{−1} := π_{t₀−1}`; see `prop_7_4` for the explicit date-`t₀` statement.) -/
def TimelessInd (β κ γ lam xstar c : ℝ) : Prop :=
  ∀ πm1 : ℝ, Bdd (unqd γ πm1 (fun _ => c)) ∧
    ∀ π x : ℕ → ℝ, Bdd π → Bdd x → (∀ t, ASind β κ γ πm1 π x t) → π 0 = γ * πm1 + c →
      lossInd β γ lam xstar πm1 (unqd γ πm1 (fun _ => c)) (fun _ => (1 - β) * c / κ) ≤
        lossInd β γ lam xstar πm1 π x

/-- Woodford (2003), p. 482: the response of inflation to a unit change in `π^qd_1`,
`(unqd γ 0 e₁)_t = γ^{t−1}` for `t ≥ 1`, is bounded by 1 when `0 ≤ γ ≤ 1`. -/
theorem abs_unqd_unit_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (t : ℕ) :
    |unqd γ 0 (unitSeq 1) t| ≤ 1 := by
  induction t with
  | zero => simp [unqd_zero, unitSeq]
  | succ n ih =>
    rw [unqd_succ]
    by_cases hn : n = 0
    · subst hn
      simp [unqd_zero, unitSeq]
    · have hu : unitSeq 1 (n + 1) = 0 := by simp [unitSeq, hn]
      rw [hu, add_zero, abs_mul, abs_of_nonneg hγ0]
      exact (mul_le_mul hγ1 ih (abs_nonneg _) zero_le_one).trans (by norm_num)

/-- Woodford (2003), Proposition 7.4 (stationary rules, cf. Proposition 7.2 "if and only if",
p. 475): for `0 ≤ γ ≤ 1` the stationary rule `π_t − γπ_{t−1} = c` is optimal from a timeless
perspective iff `c = 0`, i.e. iff the rule is (1.23) `π_t = γπ_{t−1}` (`0 < β < 1`, `κ > 0`,
`λ ≥ 0`). -/
theorem timelessInd_iff {β κ γ lam xstar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (c : ℝ) :
    TimelessInd β κ γ lam xstar c ↔ c = 0 := by
  constructor
  · intro h
    obtain ⟨hB, hmin⟩ := h 0
    set X : ℝ := (1 - β) * c / κ with hX
    set dx : ℕ → ℝ := fun t => (unitSeq 1 t - β * unitSeq 1 (t + 1)) / κ with hdx
    have hbdx : Bdd dx := ⟨(1 + β) / κ, fun t => by
      simp only [hdx, unitSeq]
      rw [abs_div, abs_of_pos hκ]
      refine div_le_div_of_nonneg_right ((abs_sub _ _).trans ?_) hκ.le
      rw [abs_mul, abs_of_pos hβ0]
      split_ifs <;> simp <;> linarith⟩
    have hbu : Bdd (unqd γ 0 (unitSeq 1)) := ⟨1, abs_unqd_unit_le hγ0 hγ1⟩
    have hall : ∀ ε : ℝ, 0 ≤ 2 * ε * dsum β (fun t => (fun _ => c) t * unitSeq 1 t +
        (cashless β κ lam xstar).lamx * ((fun _ => X) t - (cashless β κ lam xstar).xstar) * dx t +
        (cashless β κ lam xstar).lami * ((fun _ => (0 : ℝ)) t - (cashless β κ lam xstar).im) *
          (fun _ => (0 : ℝ)) t) +
        ε ^ 2 * dsum β (quad (cashless β κ lam xstar) (unitSeq 1) dx (fun _ => 0)) := by
      intro ε
      have hpe := unqd_add_smul γ 0 0 ε (fun _ => c) (unitSeq 1)
      rw [mul_zero, add_zero] at hpe
      have hle := hmin (fun t => unqd γ 0 (fun _ => c) t + ε * unqd γ 0 (unitSeq 1) t)
        (fun t => X + ε * dx t) (hB.add ((bdd_const ε).mul hbu))
        ((bdd_const X).add ((bdd_const ε).mul hbdx)) (fun t => ?_) ?_
      · rw [lossInd_eq β κ γ lam xstar 0 _ _ (fun _ => 0),
          lossInd_eq β κ γ lam xstar 0 _ _ (fun t => 0 + ε * 0), ← hpe, qd_unqd, qd_unqd]
          at hle
        have e := loss_expand (M := cashless β κ lam xstar) hβ0 hβ1 ε (bdd_const c)
          (bdd_const X) (bdd_const 0) (bdd_unitSeq 1) hbdx (bdd_const 0)
        simp only [cashless] at e hle ⊢
        rw [e] at hle
        linarith
      · rw [asInd_iff β κ γ 0 lam xstar _ _ (fun _ => 0), ← hpe, qd_unqd, cashless_AS_iff]
        simp only [hX, hdx]
        field_simp
        ring
      · rw [unqd_zero, unqd_zero]
        simp [unitSeq]
    have hG := eq_zero_of_forall_nonneg hall
    rw [dsum_of_zero_from β 2 (fun t ht => by
      have h1 : t ≠ 1 := by omega
      have h2 : t + 1 ≠ 1 := by omega
      simp only [unitSeq, hdx, h1, h2, ↓reduceIte]
      ring)] at hG
    have hval : ∑ t ∈ Finset.range 2, β ^ t * ((fun _ => c) t * unitSeq 1 t +
        (cashless β κ lam xstar).lamx * ((fun _ => X) t - (cashless β κ lam xstar).xstar) * dx t +
        (cashless β κ lam xstar).lami * ((fun _ => (0 : ℝ)) t - (cashless β κ lam xstar).im) *
          (fun _ => (0 : ℝ)) t) = β * c := by
      simp [Finset.sum_range_succ, unitSeq, hdx, cashless]
      field_simp
      ring
    rw [hval] at hG
    exact (mul_eq_zero.mp hG).resolve_left hβ0.ne'
  · rintro rfl πm1
    refine ⟨bdd_unqd_zero hγ0 hγ1 πm1, fun π x hπ hx hAS h0 => ?_⟩
    have hval : lossInd β γ lam xstar πm1 (unqd γ πm1 (fun _ => 0))
        (fun _ => (1 - β) * 0 / κ) = lam * xstar ^ 2 / (1 - β) := by
      rw [lossInd_eq β κ γ lam xstar πm1 _ _ 0, qd_unqd, cashless_loss]
      have h : (fun t : ℕ => (fun _ : ℕ => (0 : ℝ)) t ^ 2 +
          lam * ((fun _ : ℕ => (1 - β) * 0 / κ) t - xstar) ^ 2) = fun _ => lam * xstar ^ 2 := by
        funext t
        ring
      rw [h, dsum_const hβ0.le hβ1]
    rw [hval]
    have h := prop_7_4 (xstar := xstar) hβ0 hβ1 hκ.ne' hlam 0 hπ hx (fun t _ => hAS t)
      (by rw [h0, lagged_zero]; ring)
    simpa [lossInd] using h

/-! ### Indexation with transactions frictions (pp. 483–484) -/

/-- Woodford (2003), pp. 483–484: parameters of the model with indexation (1.21), the IS relation
(1.15), the loss `∑βᵗ[(π_t − γπ_{t−1})² + λ(x_t − x*)² + λ_i(i_t − iᵐ)²]` and the pre-sample
inflation rate `π_{−1}`. -/
structure IModel where
  /-- The discount factor `β`. -/
  β : ℝ
  /-- The slope `κ` of (1.21). -/
  κ : ℝ
  /-- The intertemporal elasticity `σ` in (1.15). -/
  σ : ℝ
  /-- The degree of indexation `γ`. -/
  γ : ℝ
  /-- The natural rate of interest `r̄`. -/
  rbar : ℝ
  /-- The weight `λ` on the output gap. -/
  lam : ℝ
  /-- The weight `λ_i` on the interest differential. -/
  lami : ℝ
  /-- The efficient output gap `x*`. -/
  xstar : ℝ
  /-- The interest rate `iᵐ` on the monetary base. -/
  im : ℝ
  /-- The pre-sample inflation rate `π_{−1}`. -/
  πm1 : ℝ

/-- Woodford (2003), eq. (1.21), p. 481, in the model of pp. 483–484. -/
def ASi (M : IModel) (π x : ℕ → ℝ) (t : ℕ) : Prop :=
  π t - M.γ * lagged M.πm1 π t = M.κ * x t + M.β * (π (t + 1) - M.γ * π t)

/-- Woodford (2003), eq. (1.15), p. 477, in the model of pp. 483–484. -/
def ISi (M : IModel) (π x i : ℕ → ℝ) (t : ℕ) : Prop :=
  x t = x (t + 1) - M.σ * (i t - π (t + 1) - M.rbar)

/-- Woodford (2003), p. 483: the period loss
`(π_t − γπ_{t−1})² + λ(x_t − x*)² + λ_i(i_t − iᵐ)²`. -/
def periodLossI (M : IModel) (π x i : ℕ → ℝ) (t : ℕ) : ℝ :=
  (π t - M.γ * lagged M.πm1 π t) ^ 2 + M.lam * (x t - M.xstar) ^ 2 + M.lami * (i t - M.im) ^ 2

/-- Woodford (2003), p. 483: the discounted loss. -/
noncomputable def lossI (M : IModel) (π x i : ℕ → ℝ) : ℝ := dsum M.β (periodLossI M π x i)

/-- Woodford (2003), p. 483: the IS residual `x_t − x_{t+1} + σ(i_t − π_{t+1} − r̄)`. -/
def resISi (M : IModel) (π x i : ℕ → ℝ) (t : ℕ) : ℝ :=
  x t - x (t + 1) + M.σ * (i t - π (t + 1) - M.rbar)

/-- Woodford (2003), p. 483: the residual of (1.21),
`π_t − γπ_{t−1} − κx_t − β(π_{t+1} − γπ_t)`. -/
def resASi (M : IModel) (π x : ℕ → ℝ) (t : ℕ) : ℝ :=
  π t - M.γ * lagged M.πm1 π t - M.κ * x t - M.β * (π (t + 1) - M.γ * π t)

/-- Woodford (2003), p. 483: `β` times the initial-constraint terms,
`φ_{1,−1}(x_0 + σπ_0) + βφ_{2,−1}π_0`. -/
def initI (M : IModel) (φ1m φ2m : ℝ) (π x : ℕ → ℝ) : ℝ :=
  φ1m * (x 0 + M.σ * π 0) + M.β * φ2m * π 0

/-- Woodford (2003), p. 483: the Lagrangian of the indexation model with transactions
frictions. -/
noncomputable def lagrI (M : IModel) (φ1 φ2 : ℕ → ℝ) (φ1m φ2m : ℝ) (π x i : ℕ → ℝ) : ℝ :=
  dsum M.β (fun t => periodLossI M π x i t / 2 + φ1 t * resISi M π x i t +
    φ2 t * resASi M π x t) - M.β⁻¹ * initI M φ1m φ2m π x

/-- Woodford (2003), p. 483 (**corrected**, survey E3; cf. Ch. 8 (3.15)): the generalised
inflation FOC
`(π_t − γπ_{t−1}) − βγ(π_{t+1} − γπ_t) − β⁻¹σφ_{1,t−1} + (1 + βγ)φ_{2t} − φ_{2,t−1}
− βγφ_{2,t+1}`. -/
noncomputable def focPiI (M : IModel) (φ1 φ2 : ℕ → ℝ) (φ1m φ2m : ℝ) (π : ℕ → ℝ) (t : ℕ) :
    ℝ :=
  (π t - M.γ * lagged M.πm1 π t) - M.β * M.γ * (π (t + 1) - M.γ * π t) -
    M.β⁻¹ * M.σ * lagged φ1m φ1 t + (1 + M.β * M.γ) * φ2 t - lagged φ2m φ2 t -
      M.β * M.γ * φ2 (t + 1)

/-- Woodford (2003), p. 483, **as printed**:
`(π_t − γπ_{t−1}) − βγ(π_{t+1} − γπ_t) − β⁻¹σφ_{1,t−1} + φ_{2t} − φ_{2,t−1}`. -/
noncomputable def focPiPrinted (M : IModel) (φ1 φ2 : ℕ → ℝ) (φ1m φ2m : ℝ) (π : ℕ → ℝ)
    (t : ℕ) : ℝ :=
  (π t - M.γ * lagged M.πm1 π t) - M.β * M.γ * (π (t + 1) - M.γ * π t) -
    M.β⁻¹ * M.σ * lagged φ1m φ1 t + φ2 t - lagged φ2m φ2 t

/-- Woodford (2003), (1.17), p. 484 ("continue to apply"):
`λ(x_t − x*) + φ_{1t} − β⁻¹φ_{1,t−1} − κφ_{2t}`. -/
noncomputable def focXI (M : IModel) (φ1 φ2 : ℕ → ℝ) (φ1m : ℝ) (x : ℕ → ℝ) (t : ℕ) : ℝ :=
  M.lam * (x t - M.xstar) + φ1 t - M.β⁻¹ * lagged φ1m φ1 t - M.κ * φ2 t

/-- Woodford (2003), (1.18), p. 484 ("continue to apply"): `λ_i(i_t − iᵐ) + σφ_{1t}`. -/
def focII (M : IModel) (φ1 : ℕ → ℝ) (i : ℕ → ℝ) (t : ℕ) : ℝ :=
  M.lami * (i t - M.im) + M.σ * φ1 t

/-- Woodford (2003), p. 483: the quadratic form of a deviation (with `dπ_{−1} = 0`). -/
def quadI (M : IModel) (dπ dx di : ℕ → ℝ) (t : ℕ) : ℝ :=
  (dπ t - M.γ * lagged 0 dπ t) ^ 2 + M.lam * dx t ^ 2 + M.lami * di t ^ 2

/-- Woodford (2003), p. 483: the lag of a perturbed path,
`lagged m (f + εg) = lagged m f + ε lagged 0 g` (the pre-sample value is not perturbed). -/
theorem lag_pert (m ε : ℝ) (f g : ℕ → ℝ) (t : ℕ) :
    lagged m (fun t => f t + ε * g t) t = lagged m f t + ε * lagged 0 g t := by
  cases t <;> simp

/-- Woodford (2003), p. 483 (exact expansion of the Lagrangian of the indexation model with
frictions): `𝓛(y + εd) = 𝓛(y) + ε∑βᵗ[F^π_t dπ_t + F^x_t dx_t + F^i_t di_t] + (ε²/2)∑βᵗQ_t(d)`,
where `F^π` is the **corrected** generalised FOC `focPiI`. -/
theorem lagrI_expand {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i dπ dx di : ℕ → ℝ} (φ1m φ2m ε : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (hdp : Bdd dπ) (hdx : Bdd dx) (hdi : Bdd di) :
    lagrI M φ1 φ2 φ1m φ2m (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
        (fun t => i t + ε * di t) =
      lagrI M φ1 φ2 φ1m φ2m π x i +
        ε * dsum M.β (fun t => focPiI M φ1 φ2 φ1m φ2m π t * dπ t +
          focXI M φ1 φ2 φ1m x t * dx t + focII M φ1 i t * di t) +
        ε ^ 2 / 2 * dsum M.β (quadI M dπ dx di) := by
  set q : ℕ → ℝ := fun t => π t - M.γ * lagged M.πm1 π t with hq
  set S0 : ℕ → ℝ := fun t => periodLossI M π x i t / 2 + φ1 t * resISi M π x i t +
    φ2 t * resASi M π x t with hS0
  set A : ℕ → ℝ := fun t => q t * (dπ t - M.γ * lagged 0 dπ t) + M.lam * (x t - M.xstar) * dx t +
    M.lami * (i t - M.im) * di t + φ1 t * (dx t - dx (t + 1) + M.σ * (di t - dπ (t + 1))) +
    φ2 t * (dπ t - M.γ * lagged 0 dπ t - M.κ * dx t - M.β * (dπ (t + 1) - M.γ * dπ t)) with hA
  set P : ℕ → ℝ := fun t => q t * dπ t + M.lam * (x t - M.xstar) * dx t +
    M.lami * (i t - M.im) * di t + φ1 t * (dx t + M.σ * di t) +
    φ2 t * (dπ t - M.κ * dx t + M.β * M.γ * dπ t) with hP
  set H : ℕ → ℝ := fun t => φ1 t * (dx (t + 1) + M.σ * dπ (t + 1)) + M.β * φ2 t * dπ (t + 1)
    with hH
  set G : ℕ → ℝ := fun t => lagged φ1m φ1 t * (dx t + M.σ * dπ t) + M.β * lagged φ2m φ2 t * dπ t
    with hG
  set K : ℕ → ℝ := fun t => M.γ * (q t + φ2 t) * lagged 0 dπ t with hK
  set J : ℕ → ℝ := fun t => M.γ * (q (t + 1) + φ2 (t + 1)) * dπ t with hJ
  have hqb : Bdd q := hπ.sub ((bdd_const _).mul (hπ.lag _))
  have hpt : (fun t => periodLossI M (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
      (fun t => i t + ε * di t) t / 2 +
      φ1 t * resISi M (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t)
        (fun t => i t + ε * di t) t +
      φ2 t * resASi M (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t) t) =
      fun t => S0 t + (ε * A t + ε ^ 2 / 2 * quadI M dπ dx di t) := by
    funext t
    simp only [hS0, hA, hq, periodLossI, resISi, resASi, quadI, lag_pert]
    ring
  have hinit : initI M φ1m φ2m (fun t => π t + ε * dπ t) (fun t => x t + ε * dx t) =
      initI M φ1m φ2m π x + ε * initI M φ1m φ2m dπ dx := by
    simp only [initI]
    ring
  have hS0b : Bdd S0 := by
    have hl : Bdd (periodLossI M π x i) :=
      (hqb.sq.add ((bdd_const _).mul (hx.sub (bdd_const _)).sq)).add
        ((bdd_const _).mul (hi.sub (bdd_const _)).sq)
    have hr1 : Bdd (resISi M π x i) :=
      (hx.sub hx.shift).add ((bdd_const _).mul ((hi.sub hπ.shift).sub (bdd_const _)))
    have hr2 : Bdd (resASi M π x) :=
      ((hqb.sub ((bdd_const _).mul hx)).sub ((bdd_const _).mul
        (hπ.shift.sub ((bdd_const _).mul hπ))))
    exact ((hl.mul (bdd_const _)).add (h1.mul hr1)).add (h2.mul hr2)
  have hlag0 : Bdd (lagged 0 dπ) := hdp.lag 0
  have hPb : Bdd P :=
    ((((hqb.mul hdp).add (((bdd_const _).mul (hx.sub (bdd_const _))).mul hdx)).add
      (((bdd_const _).mul (hi.sub (bdd_const _))).mul hdi)).add
      (h1.mul (hdx.add ((bdd_const _).mul hdi)))).add
      (h2.mul ((hdp.sub ((bdd_const _).mul hdx)).add ((bdd_const _).mul hdp)))
  have hGb : Bdd G :=
    ((h1.lag φ1m).mul (hdx.add ((bdd_const _).mul hdp))).add
      (((bdd_const _).mul (h2.lag φ2m)).mul hdp)
  have hHb : Bdd H := by simpa [hG, hH] using hGb.shift
  have hKb : Bdd K := ((bdd_const _).mul (hqb.add h2)).mul hlag0
  have hJb : Bdd J := ((bdd_const _).mul (hqb.shift.add h2.shift)).mul hdp
  have hAb : Bdd A := by
    have e : A = fun t => (P t - H t) - K t := by
      funext t
      simp only [hA, hP, hH, hK]
      ring
    rw [e]
    exact (hPb.sub hHb).sub hKb
  have hQb : Bdd (quadI M dπ dx di) :=
    ((hdp.sub ((bdd_const _).mul hlag0)).sq.add ((bdd_const _).mul hdx.sq)).add
      ((bdd_const _).mul hdi.sq)
  have hGH : ∀ t, G (t + 1) = H t := fun t => by simp [hG, hH]
  have hKJ : ∀ t, K (t + 1) = J t := fun t => by simp [hK, hJ]
  have hG0 : G 0 = initI M φ1m φ2m dπ dx := by
    simp only [hG, lagged_zero, initI]
  have hK0 : K 0 = 0 := by simp [hK]
  have hsH := dsum_shift hβ0 hβ1 hGb hGH
  have hsJ := dsum_shift hβ0 hβ1 hKb hKJ
  rw [hK0, sub_zero] at hsJ
  have hsK : dsum M.β K = M.β * dsum M.β J := by
    rw [hsJ]
    field_simp
  have hAsplit : A = fun t => (P t - H t) - K t := by
    funext t
    simp only [hA, hP, hH, hK]
    ring
  have hF : (fun t => focPiI M φ1 φ2 φ1m φ2m π t * dπ t + focXI M φ1 φ2 φ1m x t * dx t +
      focII M φ1 i t * di t) = fun t => (P t - M.β⁻¹ * G t) - M.β * J t := by
    funext t
    simp only [hP, hG, hJ, hq, focPiI, focXI, focII, lagged_succ]
    have hββ : M.β * M.β⁻¹ = 1 := mul_inv_cancel₀ hβ0.ne'
    linear_combination (lagged φ2m φ2 t * dπ t) * hββ
  unfold lagrI
  rw [hpt, hinit, dsum_add hβ0.le hβ1 hS0b (((bdd_const _).mul hAb).add
      ((bdd_const _).mul hQb)), dsum_add hβ0.le hβ1 ((bdd_const _).mul hAb)
      ((bdd_const _).mul hQb), dsum_mul_left, dsum_mul_left, hAsplit,
    dsum_sub hβ0.le hβ1 (hPb.sub hHb) hKb, dsum_sub hβ0.le hβ1 hPb hHb, hsH, hsK, hF,
    dsum_sub hβ0.le hβ1 (hPb.sub ((bdd_const _).mul hGb)) ((bdd_const _).mul hJb),
    dsum_sub hβ0.le hβ1 hPb ((bdd_const _).mul hGb), dsum_mul_left, dsum_mul_left, hG0]
  ring

/-- Woodford (2003), p. 483, the generalised (1.16) as an exact derivative: the derivative of
the Lagrangian with respect to `π_s` is `βˢ` times the **corrected** FOC `focPiI`, which carries
the extra multiplier terms `βγφ_{2s} − βγφ_{2,s+1}` produced by (1.21). -/
theorem hasDerivAt_lagrI_pi {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (s : ℕ) :
    HasDerivAt (fun ε => lagrI M φ1 φ2 φ1m φ2m (fun t => π t + ε * unitSeq s t) x i)
      (M.β ^ s * focPiI M φ1 φ2 φ1m φ2m π s) 0 := by
  have hfun : (fun ε => lagrI M φ1 φ2 φ1m φ2m (fun t => π t + ε * unitSeq s t) x i) =
      fun ε => lagrI M φ1 φ2 φ1m φ2m π x i + ε * (M.β ^ s * focPiI M φ1 φ2 φ1m φ2m π s) +
        ε ^ 2 / 2 * dsum M.β (quadI M (unitSeq s) (fun _ => 0) (fun _ => 0)) := by
    funext ε
    have h := lagrI_expand hβ0 hβ1 φ1m φ2m ε h1 h2 hπ hx hi (bdd_unitSeq s) (bdd_const 0)
      (bdd_const 0)
    simp only [mul_zero, add_zero] at h
    rw [h, dsum_mul_unitSeq]
  rw [hfun]
  exact hasDerivAt_quadratic _ _ _

/-- Woodford (2003), (1.17) "continues to apply", p. 484, as an exact derivative. -/
theorem hasDerivAt_lagrI_x {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (s : ℕ) :
    HasDerivAt (fun ε => lagrI M φ1 φ2 φ1m φ2m π (fun t => x t + ε * unitSeq s t) i)
      (M.β ^ s * focXI M φ1 φ2 φ1m x s) 0 := by
  have hfun : (fun ε => lagrI M φ1 φ2 φ1m φ2m π (fun t => x t + ε * unitSeq s t) i) =
      fun ε => lagrI M φ1 φ2 φ1m φ2m π x i + ε * (M.β ^ s * focXI M φ1 φ2 φ1m x s) +
        ε ^ 2 / 2 * dsum M.β (quadI M (fun _ => 0) (unitSeq s) (fun _ => 0)) := by
    funext ε
    have h := lagrI_expand hβ0 hβ1 φ1m φ2m ε h1 h2 hπ hx hi (bdd_const 0) (bdd_unitSeq s)
      (bdd_const 0)
    simp only [mul_zero, add_zero, zero_add] at h
    rw [h, dsum_mul_unitSeq]
  rw [hfun]
  exact hasDerivAt_quadratic _ _ _

/-- Woodford (2003), (1.18) "continues to apply", p. 484, as an exact derivative. -/
theorem hasDerivAt_lagrI_i {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    {φ1 φ2 π x i : ℕ → ℝ} (φ1m φ2m : ℝ) (h1 : Bdd φ1) (h2 : Bdd φ2) (hπ : Bdd π)
    (hx : Bdd x) (hi : Bdd i) (s : ℕ) :
    HasDerivAt (fun ε => lagrI M φ1 φ2 φ1m φ2m π x (fun t => i t + ε * unitSeq s t))
      (M.β ^ s * focII M φ1 i s) 0 := by
  have hfun : (fun ε => lagrI M φ1 φ2 φ1m φ2m π x (fun t => i t + ε * unitSeq s t)) =
      fun ε => lagrI M φ1 φ2 φ1m φ2m π x i + ε * (M.β ^ s * focII M φ1 i s) +
        ε ^ 2 / 2 * dsum M.β (quadI M (fun _ => 0) (fun _ => 0) (unitSeq s)) := by
    funext ε
    have h := lagrI_expand hβ0 hβ1 φ1m φ2m ε h1 h2 hπ hx hi (bdd_const 0) (bdd_const 0)
      (bdd_unitSeq s)
    simp only [mul_zero, add_zero, zero_add] at h
    rw [h, dsum_mul_unitSeq]
  rw [hfun]
  exact hasDerivAt_quadratic _ _ _

/-- Woodford (2003), p. 483 (survey E3): the printed FOC differs from the correct one by
`βγ(φ_{2t} − φ_{2,t+1})`; the two agree when `φ₂` is constant from `t` to `t + 1`. -/
theorem focPiI_sub_printed (M : IModel) (φ1 φ2 : ℕ → ℝ) (φ1m φ2m : ℝ) (π : ℕ → ℝ) (t : ℕ) :
    focPiI M φ1 φ2 φ1m φ2m π t - focPiPrinted M φ1 φ2 φ1m φ2m π t =
      M.β * M.γ * (φ2 t - φ2 (t + 1)) := by
  simp only [focPiI, focPiPrinted]
  ring

/-- Woodford (2003), p. 483 (**counterexample to the printed FOC**, survey E3): with
`β = γ = 1/2`, `κ = σ = 1`, zero plan and multipliers `φ₁ = 0`, `φ₂ = e₁`, the printed expression
is *not* the derivative of the Lagrangian with respect to `π_0` (that derivative is the corrected
`focPiI`, which differs from the printed one by `βγ(φ_{20} − φ_{21}) = −1/4`). -/
theorem printed_foc_not_derivative :
    ∃ (M : IModel) (φ1 φ2 π x i : ℕ → ℝ) (φ1m φ2m : ℝ),
      ¬ HasDerivAt (fun ε => lagrI M φ1 φ2 φ1m φ2m (fun t => π t + ε * unitSeq 0 t) x i)
        (M.β ^ 0 * focPiPrinted M φ1 φ2 φ1m φ2m π 0) 0 := by
  set M : IModel :=
    { β := 1 / 2, κ := 1, σ := 1, γ := 1 / 2, rbar := 0, lam := 0, lami := 0,
      xstar := 0, im := 0, πm1 := 0 } with hM
  refine ⟨M, fun _ => 0, unitSeq 1, fun _ => 0, fun _ => 0, fun _ => 0, 0, 0, fun h => ?_⟩
  have hc := hasDerivAt_lagrI_pi (M := M) (by norm_num [hM]) (by norm_num [hM]) 0 0
    (bdd_const 0) (bdd_unitSeq 1) (bdd_const 0) (bdd_const 0) (bdd_const 0) 0
  have he := hc.unique h
  have hd := focPiI_sub_printed M (fun _ => 0) (unitSeq 1) 0 0 (fun _ => 0) 0
  rw [pow_zero, one_mul, one_mul] at he
  rw [he, sub_self] at hd
  simp [unitSeq, hM] at hd

/-- Woodford (2003), p. 484: the steady-state condition of the first-order conditions with
constant multipliers, `λ_i(ı̄ − iᵐ) = −β(1 − γ)(1 − βγ)π̄`. -/
def SSCondI (M : IModel) (πb ib : ℝ) : Prop :=
  M.lami * (ib - M.im) = -(M.β * (1 - M.γ) * (1 - M.β * M.γ) * πb)

/-- Woodford (2003), p. 484: with pre-sample inflation `π_{−1} = π̄`, the constant plan satisfies
the corrected FOCs (generalised (1.16), (1.17), (1.18)) at every date with constant multipliers
iff `SSCondI` holds (`β, σ, κ ≠ 0`). The printed FOC gives the same condition, because the
omitted terms cancel at constant `φ₂`. -/
theorem focI_const_iff {M : IModel} (hβ : M.β ≠ 0) (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0)
    {πb xb ib : ℝ} (hpm : M.πm1 = πb) :
    (∃ c1 c2 : ℝ, ∀ t, focPiI M (fun _ => c1) (fun _ => c2) c1 c2 (fun _ => πb) t = 0 ∧
      focXI M (fun _ => c1) (fun _ => c2) c1 (fun _ => xb) t = 0 ∧
      focII M (fun _ => c1) (fun _ => ib) t = 0) ↔ SSCondI M πb ib := by
  have hlag : ∀ t, lagged M.πm1 (fun _ => πb) t = πb := fun t => by
    rw [hpm]; exact lagged_const πb t
  constructor
  · rintro ⟨c1, c2, h⟩
    obtain ⟨hP, -, hI⟩ := h 0
    simp only [focPiI, focII, hlag, lagged_const] at hP hI
    unfold SSCondI
    have hc : M.β⁻¹ * M.σ * c1 = (1 - M.γ) * (1 - M.β * M.γ) * πb := by linarith
    have hc' : M.σ * c1 = M.β * ((1 - M.γ) * (1 - M.β * M.γ) * πb) := by
      rw [← hc]
      field_simp
    linear_combination hI - hc'
  · intro hc
    unfold SSCondI at hc
    refine ⟨M.β * (1 - M.γ) * (1 - M.β * M.γ) * πb / M.σ,
      (M.lam * (xb - M.xstar) + (1 - M.β⁻¹) * (M.β * (1 - M.γ) * (1 - M.β * M.γ) * πb / M.σ))
        / M.κ, fun t => ?_⟩
    simp only [focPiI, focXI, focII, hlag, lagged_const]
    refine ⟨?_, ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring
    · field_simp
      linear_combination hc

/-- Woodford (2003), p. 484: the constant plan is feasible iff `ı̄ = r̄ + π̄` and
`κx̄ = (1 − β)(1 − γ)π̄` (with `π_{−1} = π̄`, `σ ≠ 0`). -/
theorem constI_feasible_iff {M : IModel} (hσ : M.σ ≠ 0) {πb xb ib : ℝ} (hpm : M.πm1 = πb) :
    (∀ t, ASi M (fun _ => πb) (fun _ => xb) t ∧ ISi M (fun _ => πb) (fun _ => xb)
      (fun _ => ib) t) ↔ ib = M.rbar + πb ∧ M.κ * xb = (1 - M.β) * (1 - M.γ) * πb := by
  have hlag : ∀ t, lagged M.πm1 (fun _ => πb) t = πb := fun t => by
    rw [hpm]; exact lagged_const πb t
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := h 0
    unfold ASi at ha
    unfold ISi at hb
    rw [hlag] at ha
    have hi : M.σ * (ib - πb - M.rbar) = 0 := by linarith
    have := (mul_eq_zero.mp hi).resolve_left hσ
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hi, hx⟩ t
    refine ⟨?_, ?_⟩
    · unfold ASi
      rw [hlag]
      linarith
    · unfold ISi
      rw [hi]
      ring

/-- Woodford (2003), p. 484: the long-run inflation rate consistent with the first-order
conditions, `π̄ = −λ_i(r̄ − iᵐ)/(λ_i + β(1 − γ)(1 − βγ))`, generalising (1.19). The constant plan
with constant multipliers satisfies the FOCs and the constraints iff `π̄` is this value,
`ı̄ = r̄ + π̄` and `κx̄ = (1 − β)(1 − γ)π̄` (`β, σ, κ ≠ 0`, nonzero denominator). -/
theorem ss_ind_iff {M : IModel} (hβ : M.β ≠ 0) (hσ : M.σ ≠ 0) (hκ : M.κ ≠ 0)
    (hD : M.lami + M.β * (1 - M.γ) * (1 - M.β * M.γ) ≠ 0) {πb xb ib : ℝ} (hpm : M.πm1 = πb) :
    ((∃ c1 c2 : ℝ, ∀ t, focPiI M (fun _ => c1) (fun _ => c2) c1 c2 (fun _ => πb) t = 0 ∧
      focXI M (fun _ => c1) (fun _ => c2) c1 (fun _ => xb) t = 0 ∧
      focII M (fun _ => c1) (fun _ => ib) t = 0) ∧
      ∀ t, ASi M (fun _ => πb) (fun _ => xb) t ∧ ISi M (fun _ => πb) (fun _ => xb)
        (fun _ => ib) t) ↔
      πb = -(M.lami * (M.rbar - M.im)) / (M.lami + M.β * (1 - M.γ) * (1 - M.β * M.γ)) ∧
        ib = M.rbar + πb ∧ M.κ * xb = (1 - M.β) * (1 - M.γ) * πb := by
  rw [focI_const_iff hβ hσ hκ hpm, constI_feasible_iff hσ hpm]
  unfold SSCondI
  constructor
  · rintro ⟨hc, hi, hx⟩
    refine ⟨?_, hi, hx⟩
    rw [eq_div_iff hD]
    rw [hi] at hc
    linarith
  · rintro ⟨hp, hi, hx⟩
    refine ⟨?_, hi, hx⟩
    rw [eq_div_iff hD] at hp
    rw [hi]
    linarith

/-- Woodford (2003), p. 484: the long-run inflation rate is negative,
`−λ_i(r̄ − iᵐ)/(λ_i + β(1 − γ)(1 − βγ)) < 0`, when `λ_i > 0`, `iᵐ < r̄`, `0 < β < 1`,
`γ ≤ 1` (in particular for `0 ≤ γ ≤ 1`). -/
theorem piBar_ind_neg {β γ lami rbar im : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ1 : γ ≤ 1)
    (hli : 0 < lami) (him : im < rbar) :
    -(lami * (rbar - im)) / (lami + β * (1 - γ) * (1 - β * γ)) < 0 := by
  have h1 : 0 ≤ β * (1 - γ) * (1 - β * γ) := by
    have : β * γ ≤ 1 := by nlinarith
    have := mul_nonneg (mul_nonneg hβ0.le (by linarith : (0 : ℝ) ≤ 1 - γ))
      (by linarith : (0 : ℝ) ≤ 1 - β * γ)
    exact this
  exact div_neg_of_neg_of_pos (by nlinarith) (by linarith)

/-- Woodford (2003), p. 484: with full indexation (`γ = 1`) and `λ_i > 0` the long-run inflation
rate is the Friedman rate `−(r̄ − iᵐ)`, independent of `λ_i`. -/
theorem piBar_ind_gamma_one {β lami rbar im : ℝ} (hli : lami ≠ 0) :
    -(lami * (rbar - im)) / (lami + β * (1 - 1) * (1 - β * 1)) = -(rbar - im) := by
  have h : lami + β * (1 - 1) * (1 - β * 1) = lami := by ring
  rw [h, neg_div, mul_div_cancel_left₀ _ hli]

/-- Woodford (2003), p. 484: in the cashless case `λ_i = 0` the steady-state condition
`SSCondI` determines `π̄` (as `π̄ = 0`) only when `γ ≠ 1`: it holds iff `γ = 1` or `π̄ = 0`
(`0 < β < 1`, `γ ≤ 1`). -/
theorem ssCondI_cashless_iff {M : IModel} (hli : M.lami = 0) (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hγ1 : M.γ ≤ 1) (πb ib : ℝ) :
    SSCondI M πb ib ↔ M.γ = 1 ∨ πb = 0 := by
  unfold SSCondI
  rw [hli, zero_mul]
  have hbg : 1 - M.β * M.γ ≠ 0 := by nlinarith
  constructor
  · intro h
    have h' : M.β * ((1 - M.γ) * ((1 - M.β * M.γ) * πb)) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h | h
    · exact absurd h hβ0.ne'
    rcases mul_eq_zero.mp h with h | h
    · left; linarith
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hbg
    · right; exact h
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

/-- Woodford (2003), p. 484 (sufficiency): if `π_{−1} = π̄` and the constant plan with constant
multipliers satisfies the FOCs and the constraints, then it minimises the loss among bounded
plans satisfying (1.21) and (1.15) with `π_0 = π̄`, `x_0 = x̄` (`0 < β < 1`, `λ, λ_i ≥ 0`): the
FOC steady state is optimal from a timeless perspective. -/
theorem ss_ind_optimal {M : IModel} (hβ0 : 0 < M.β) (hβ1 : M.β < 1) (hlam : 0 ≤ M.lam)
    (hli : 0 ≤ M.lami) {πb xb ib c1 c2 : ℝ}
    (hfoc : ∀ t, focPiI M (fun _ => c1) (fun _ => c2) c1 c2 (fun _ => πb) t = 0 ∧
      focXI M (fun _ => c1) (fun _ => c2) c1 (fun _ => xb) t = 0 ∧
      focII M (fun _ => c1) (fun _ => ib) t = 0)
    (hF : ∀ t, ASi M (fun _ => πb) (fun _ => xb) t ∧
      ISi M (fun _ => πb) (fun _ => xb) (fun _ => ib) t)
    {π x i : ℕ → ℝ} (hπ : Bdd π) (hx : Bdd x) (hi : Bdd i)
    (hF' : ∀ t, ASi M π x t ∧ ISi M π x i t) (h0 : π 0 = πb) (h0' : x 0 = xb) :
    lossI M (fun _ => πb) (fun _ => xb) (fun _ => ib) ≤ lossI M π x i := by
  have hfeas : ∀ {u v w : ℕ → ℝ}, (∀ t, ASi M u v t ∧ ISi M u v w t) →
      lagrI M (fun _ => c1) (fun _ => c2) c1 c2 u v w =
        lossI M u v w / 2 - M.β⁻¹ * initI M c1 c2 u v := by
    intro u v w h
    have hz : (fun t => periodLossI M u v w t / 2 + (fun _ => c1) t * resISi M u v w t +
        (fun _ => c2) t * resASi M u v t) = fun t => (1 / 2) * periodLossI M u v w t := by
      funext t
      have ha := (h t).1
      have hb := (h t).2
      unfold ASi at ha
      unfold ISi at hb
      have e1 : resISi M u v w t = 0 := by unfold resISi; linarith
      have e2 : resASi M u v t = 0 := by unfold resASi; linarith
      rw [e1, e2]
      ring
    unfold lagrI lossI
    rw [hz, dsum_mul_left]
    ring
  have he := lagrI_expand (M := M) hβ0 hβ1 c1 c2 1 (bdd_const c1) (bdd_const c2)
    (bdd_const πb) (bdd_const xb) (bdd_const ib) (hπ.sub (bdd_const πb))
    (hx.sub (bdd_const xb)) (hi.sub (bdd_const ib))
  have hy : ∀ (u : ℕ → ℝ) (c : ℝ), (fun t => c + 1 * (u t - c)) = u := fun u c => by
    funext t; ring
  rw [hy, hy, hy, hfeas hF', hfeas hF] at he
  have hz : (fun t => focPiI M (fun _ => c1) (fun _ => c2) c1 c2 (fun _ => πb) t * (π t - πb) +
      focXI M (fun _ => c1) (fun _ => c2) c1 (fun _ => xb) t * (x t - xb) +
      focII M (fun _ => c1) (fun _ => ib) t * (i t - ib)) = fun _ => 0 := by
    funext t
    rw [(hfoc t).1, (hfoc t).2.1, (hfoc t).2.2]
    ring
  have hinit : initI M c1 c2 π x = initI M c1 c2 (fun _ => πb) (fun _ => xb) := by
    simp only [initI, h0, h0']
  have hd0 : dsum M.β (fun _ => (0 : ℝ)) = 0 := by simp [dsum]
  rw [hz, hinit, hd0] at he
  have hq : 0 ≤ dsum M.β (quadI M (fun t => π t - πb) (fun t => x t - xb)
      (fun t => i t - ib)) := dsum_nonneg hβ0.le (fun t => by
    unfold quadI
    have := sq_nonneg ((fun t => π t - πb) t - M.γ * lagged 0 (fun t => π t - πb) t)
    have := mul_nonneg hlam (sq_nonneg (x t - xb))
    have := mul_nonneg hli (sq_nonneg (i t - ib))
    linarith)
  linarith

/-! ### Proposition 7.4 under uncertainty -/

variable {Ω : Type*}

/-- Woodford (2003), (1.21) under uncertainty:
`π_t − γπ_{t−1} = κx_t + βE_t[π_{t+1} − γπ_t]`. -/
def ASindS (𝔼 : ExpectationSystem Ω) (β κ γ πm1 : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  π t - γ • lagged (fun _ => πm1) π t = κ • x t + β • 𝔼.E t (π (t + 1) - γ • π t)

/-- Woodford (2003), Proposition 7.4 under uncertainty (for an arbitrary expectation system):
every bounded random plan satisfying (1.21) at every date with the rule (1.23) holding at date 0,
`π_0 = γπ_{−1}`, has expected discounted loss (1.22) at least `λx*²/(1 − β)`, the loss of the
deterministic path `π_t = γ^{t+1}π_{−1}`, `x_t = 0` (`prop_7_4_rule`), in every date-0 state. -/
theorem prop_7_4_uncertainty {𝔼 : ExpectationSystem Ω} {β κ γ lam xstar πm1 : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : κ ≠ 0) (hlam : 0 ≤ lam) {π x : ℕ → Ω → ℝ}
    (hπ : BoundedProc π) (hx : BoundedProc x) (hAS : ∀ t, ASindS 𝔼 β κ γ πm1 π x t)
    (h0 : π 0 = fun _ => γ * πm1) (ω : Ω) :
    lam * xstar ^ 2 / (1 - β) ≤ 𝔼.E 0 (fun ω' => dsum β (fun t =>
      (π t ω' - γ * lagged (fun _ => πm1) π t ω') ^ 2 + lam * (x t ω' - xstar) ^ 2)) ω := by
  obtain ⟨C1, hC1⟩ := hπ
  obtain ⟨C2, hC2⟩ := hx
  have hC1' : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0 ω)
  set q : ℕ → Ω → ℝ := fun t => π t - γ • lagged (fun _ => πm1) π t with hq
  have hlagb : ∀ t ω', |lagged (fun _ => πm1) π t ω'| ≤ C1 + |πm1| := by
    intro t ω'
    cases t with
    | zero => simp only [lagged_zero]; linarith [abs_nonneg πm1]
    | succ n => simp only [lagged_succ]; linarith [hC1 n ω', abs_nonneg πm1]
  have hqb : ∀ t ω', |q t ω'| ≤ C1 + |γ| * (C1 + |πm1|) := by
    intro t ω'
    simp only [hq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hC1 t ω') ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hlagb t ω') (abs_nonneg γ)
  -- the pointwise lower bound
  set Sx : Ω → ℝ := fun ω' => ∑' t, β ^ t * x t ω' with hSx
  have hlow : (fun ω' => lam * xstar ^ 2 / (1 - β) - (2 * lam * xstar) * Sx ω') ≤
      fun ω' => dsum β (fun t => (π t ω' - γ * lagged (fun _ => πm1) π t ω') ^ 2 +
        lam * (x t ω' - xstar) ^ 2) := by
    intro ω'
    have bx : Bdd (fun t => x t ω') := ⟨C2, fun t => hC2 t ω'⟩
    have bp : Bdd (fun t => π t ω') := ⟨C1, fun t => hC1 t ω'⟩
    have bl : Bdd (fun t => lagged (fun _ => πm1) π t ω') := ⟨C1 + |πm1|, fun t => hlagb t ω'⟩
    have hpt : ∀ t, lam * xstar ^ 2 - (2 * lam * xstar) * x t ω' ≤
        (π t ω' - γ * lagged (fun _ => πm1) π t ω') ^ 2 + lam * (x t ω' - xstar) ^ 2 := by
      intro t
      have a1 := sq_nonneg (π t ω' - γ * lagged (fun _ => πm1) π t ω')
      have a2 := mul_nonneg hlam (sq_nonneg (x t ω'))
      nlinarith
    have hle := dsum_le_dsum hβ0.le hβ1 ((bdd_const _).sub ((bdd_const _).mul bx))
      ((bp.sub ((bdd_const γ).mul bl)).sq.add ((bdd_const lam).mul (bx.sub (bdd_const _)).sq))
      hpt
    rw [dsum_sub hβ0.le hβ1 (bdd_const _) ((bdd_const _).mul bx), dsum_const hβ0.le hβ1,
      dsum_mul_left] at hle
    exact hle
  have hmono := 𝔼.mono 0 hlow ω
  have hfun : (fun ω' => lam * xstar ^ 2 / (1 - β) - (2 * lam * xstar) * Sx ω') =
      (fun _ => lam * xstar ^ 2 / (1 - β)) - (2 * lam * xstar) • Sx := by
    funext ω'
    simp
  rw [hfun, map_sub, map_smul, 𝔼.const] at hmono
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hmono
  -- E_0 ∑βᵗx_t = 0
  have hE := 𝔼.E_tsum hβ0.le hβ1 (f := fun k ω' => β ^ k * x k ω') (M := C2) (fun k ω' => by
    rw [abs_mul, abs_pow, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left (hC2 k ω') (pow_nonneg hβ0.le k)) 0 ω
  have hEk : ∀ k, 𝔼.E 0 (fun ω' => β ^ k * x k ω') ω = β ^ k * 𝔼.E 0 (x k) ω := by
    intro k
    have : (fun ω' => β ^ k * x k ω') = (β ^ k) • x k := by funext; simp
    rw [this, map_smul]
    rfl
  have hrec : ∀ t, 𝔼.E 0 (q t) ω = κ * 𝔼.E 0 (x t) ω + β * 𝔼.E 0 (q (t + 1)) ω := by
    intro t
    have e := congrArg (fun z => 𝔼.E 0 z ω) (hAS t)
    have hq1 : π (t + 1) - γ • π t = q (t + 1) := rfl
    simp only [hq1] at e
    simp only [map_add, map_smul, 𝔼.tower (Nat.zero_le t), Pi.add_apply, Pi.smul_apply,
      smul_eq_mul] at e
    exact e
  have hq0 : 𝔼.E 0 (q 0) ω = 0 := by
    have : q 0 = fun _ => 0 := by
      funext ω'
      simp only [hq, h0, lagged_zero, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, 𝔼.const]
  have hsum : dsum β (fun t => 𝔼.E 0 (x t) ω) = 0 := by
    rw [dsum_x_eq hβ0 hβ1 hκ (q := fun t => 𝔼.E 0 (q t) ω)
      ⟨C1 + |γ| * (C1 + |πm1|), fun t => 𝔼.abs_E_le (hqb t) 0 ω⟩ hrec, hq0, zero_div]
  have hS : 𝔼.E 0 Sx ω = 0 := by
    rw [hSx, hE]
    simp_rw [hEk]
    exact hsum
  rw [hS] at hmono
  linarith

end Woodford.GainsFromCommitment.Indexation
