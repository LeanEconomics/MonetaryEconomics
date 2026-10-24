/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.Expectations
import GainsFromCommitment.Sequences
import GainsFromCommitment.VarianceFrontier

/-!
# The optimal noninertial plan

Woodford (2003), *Interest and Prices*, Chapter 7, §3 (pp. 507–513) and Appendix F.4
(pp. 713–714).

## Main results

* (3.1): the Taylor-rule family `taylorRule`.
* p. 508: along a constant-inflation path the loss (1.2) equals `constLoss`
  (`hasSum_constLoss`); its unique minimiser `constLossArgmin` is strictly positive when `x* > 0`,
  so the constant-path criterion is not minimised at zero inflation (`constLoss_not_min_at_zero`).
* Timeless optimality of constant plans, proved by Lagrangian sufficiency with an explicit
  perturbation for the converse: for the loss (1.2) the constant path is timelessly optimal iff
  `π̄ = 0` (`timelessOpt12_iff`, Prop 7.2 restated); for the loss (1.14) with the IS relation
  (1.15) iff `π̄ = λᵢ(i* − r̄)/(λᵢ + β)`, i.e. (1.19) = (3.11) (`timelessOpt114_iff`, Prop 7.3
  restated).
* (3.2)–(3.3): a plan `π = π̄ + f_π u`, `x = x̄ + f_x u` satisfies (2.1) iff (3.2) and (3.3)
  (`plan_AS_iff`).
* Conditional variances of AR(1) processes with innovations (`condCov_ar1`), and the stabilization
  loss (3.4), (3.7), (3.8) as genuine discounted sums of conditional variances (`lstab12_hasSum`,
  `lstab_hasSum`).
* (3.5) and **Proposition 7.11** (`oni_objective_eq`, `oni_unique_min`, `prop_7_11`,
  `prop_7_11_lstab`).
* Discretion (pp. 511–512): the unique bounded solution of (2.2) under AR(1) shocks
  (`discretion_iff`), `f_π^disc ≥ f_π^oni` with equality iff `ρ = 0` (`fpiDisc_ge_fpiOni`), the
  output-gap response (`fxDisc_ge_fxOni`), and discretion is the noninertial optimum iff
  `x* = 0 ∧ ρ = 0` (`discretion_eq_oni_iff`).
* (3.6)–(3.8) and Appendix F.4: the six restrictions (`plan2_iff`), the F.4 response
  coefficients are the unique minimisers of `L^{stab,u}`, `L^{stab,r}` (`f4_u_optimal`,
  `f4_r_optimal`, and stochastically `f4_lstab`), `iᵣ, iᵤ > 0` (`iRF4_iUF4_pos`).
* Survey E11 (confirmed): the F.4 long-run values minimise the steady-state period loss
  (`f4_zbar_minimises_steady_loss`), they differ from the timelessly optimal (3.11) values
  (`f4_zbar_ne_timeless`, `f4_zbar_ne_timeless_xstar`, `f4_zbar_not_timeless`), and the latter
  are proved timelessly optimal (`timelessOpt114_iff`); the corrected F.4 is `f4_corrected`.
  The text's "Section F.3" (pp. 513, 514) means F.4.

All stochastic statements hold for an arbitrary `ExpectationSystem`; the variance results use the
pull-out property `PullOut` (true for perfect foresight and finite event trees).
-/

namespace Woodford.GainsFromCommitment.Noninertial

open Filter Topology
open Sequences
open VarianceFrontier (condCov plan2 plan2_apply)

/-! ### The Taylor rule (3.1) -/

/-- Woodford (2003), eq. (3.1), p. 507: the contemporaneous Taylor rule
`i_t = ī + φ_π (π_t − π̄) + φ_x (x_t − x̄)/4`, state by state. -/
noncomputable def taylorRule {Ω : Type*} (ibar φπ φx πbar xbar : ℝ) (π x : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t ω => ibar + φπ * (π t ω - πbar) + φx * (x t ω - xbar) / 4

/-! The discounted-sum and boundedness tools (`summable_disc`, `hasSum_telescope`,
`hasSum_disc_const`, `Bdd`, `bdd_sub_const`, `bdd_lin`) are the shared `Sequences` lemmas and
the conditional covariance `condCov` is the shared `VarianceFrontier.condCov`. -/

/-! ### p. 508: the constant-inflation criterion -/

/-- Woodford (2003), p. 508: the value of (1.2) along the path with constant inflation `π̄` and
the constant output gap `(1 − β) π̄ / κ` that (1.1) then requires,
`(1 − β)⁻¹ [π̄² + λ((1 − β)π̄/κ − x*)²]`. -/
noncomputable def constLoss (β κ lam xstar πbar : ℝ) : ℝ :=
  (1 - β)⁻¹ * (πbar ^ 2 + lam * ((1 - β) / κ * πbar - xstar) ^ 2)

/-- Woodford (2003), p. 508: if inflation is constant at `π̄` and (1.1) `π_t = κ x_t + β π_{t+1}`
holds every period, then the output gap is `(1 − β) π̄ / κ` and the loss (1.2) is `constLoss`. -/
theorem hasSum_constLoss {β κ lam xstar πbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    {π x : ℕ → ℝ} (hπ : ∀ t, π t = πbar) (hAS : ∀ t, π t = κ * x t + β * π (t + 1)) :
    HasSum (fun t => β ^ t * (π t ^ 2 + lam * (x t - xstar) ^ 2))
      (constLoss β κ lam xstar πbar) := by
  have hx : ∀ t, x t = (1 - β) / κ * πbar := by
    intro t
    have h := hAS t
    rw [hπ t, hπ (t + 1)] at h
    field_simp
    linarith
  have e : (fun t => β ^ t * (π t ^ 2 + lam * (x t - xstar) ^ 2)) =
      fun t => β ^ t * (πbar ^ 2 + lam * ((1 - β) / κ * πbar - xstar) ^ 2) := by
    funext t
    rw [hπ t, hx t]
  rw [e]
  exact hasSum_disc_const hβ0 hβ1 _

/-- Woodford (2003), p. 508: the minimiser of the constant-inflation criterion,
`π̄ = λ κ (1 − β) x* / (κ² + λ (1 − β)²)`. -/
noncomputable def constLossArgmin (β κ lam xstar : ℝ) : ℝ :=
  lam * κ * (1 - β) * xstar / (κ ^ 2 + lam * (1 - β) ^ 2)

/-- Woodford (2003), p. 508: completing the square,
`constLoss π̄ = constLoss π̄* + (1 − β)⁻¹ (1 + λ(1 − β)²/κ²)(π̄ − π̄*)²`. -/
theorem constLoss_eq {β κ lam xstar : ℝ} (hκ : κ ≠ 0) (hlam : 0 ≤ lam) (πbar : ℝ) :
    constLoss β κ lam xstar πbar = constLoss β κ lam xstar (constLossArgmin β κ lam xstar)
      + (1 - β)⁻¹ * (1 + lam * (1 - β) ^ 2 / κ ^ 2) *
        (πbar - constLossArgmin β κ lam xstar) ^ 2 := by
  have hden : κ ^ 2 + lam * (1 - β) ^ 2 ≠ 0 := by positivity
  unfold constLoss constLossArgmin
  field_simp
  ring

/-- Woodford (2003), p. 508: `constLossArgmin` is the unique minimiser of the constant-inflation
criterion (for `0 < β < 1`, `κ ≠ 0`, `λ ≥ 0`). -/
theorem constLoss_min_iff {β κ lam xstar : ℝ} (hβ1 : β < 1) (hκ : κ ≠ 0) (hlam : 0 ≤ lam)
    (πbar : ℝ) :
    (∀ p, constLoss β κ lam xstar πbar ≤ constLoss β κ lam xstar p) ↔
      πbar = constLossArgmin β κ lam xstar := by
  have hc : 0 < (1 - β)⁻¹ * (1 + lam * (1 - β) ^ 2 / κ ^ 2) := by
    have : 0 ≤ lam * (1 - β) ^ 2 / κ ^ 2 := by positivity
    have : 0 < (1 - β)⁻¹ := inv_pos.mpr (by linarith)
    positivity
  constructor
  · intro h
    have h1 := h (constLossArgmin β κ lam xstar)
    rw [constLoss_eq hκ hlam πbar] at h1
    have h2 : (πbar - constLossArgmin β κ lam xstar) ^ 2 ≤ 0 := by
      by_contra hn
      push Not at hn
      nlinarith [mul_pos hc hn]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h2 (sq_nonneg _))
    linarith
  · rintro rfl p
    rw [constLoss_eq hκ hlam p]
    nlinarith [sq_nonneg (p - constLossArgmin β κ lam xstar)]

/-- Woodford (2003), p. 508: with `x* > 0` the constant-inflation criterion is minimised at a
strictly positive inflation rate. -/
theorem constLossArgmin_pos {β κ lam xstar : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam)
    (hx : 0 < xstar) : 0 < constLossArgmin β κ lam xstar := by
  unfold constLossArgmin
  have : 0 < 1 - β := by linarith
  positivity

/-- Woodford (2003), p. 508: the constant-inflation criterion "is not minimized at `π̄ = 0` in
the case that `x* > 0`": some constant inflation rate does strictly better than zero. -/
theorem constLoss_not_min_at_zero {β κ lam xstar : ℝ} (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hx : 0 < xstar) :
    constLoss β κ lam xstar (constLossArgmin β κ lam xstar) < constLoss β κ lam xstar 0 := by
  have hpos := constLossArgmin_pos hβ1 hκ hlam hx
  rw [constLoss_eq (xstar := xstar) hκ.ne' hlam.le 0]
  have hc : 0 < (1 - β)⁻¹ * (1 + lam * (1 - β) ^ 2 / κ ^ 2) := by
    have : 0 < (1 - β)⁻¹ := inv_pos.mpr (by linarith)
    positivity
  have : 0 < (0 - constLossArgmin β κ lam xstar) ^ 2 := by
    have : 0 - constLossArgmin β κ lam xstar ≠ 0 := by linarith
    positivity
  nlinarith [mul_pos hc this]


/-! ### Timeless optimality of constant plans (Propositions 7.2 and 7.3 restated)

The deterministic problems of §1 (pp. 469–479). A constant plan is *optimal from a timeless
perspective* (p. 474 for (1.2); p. 477 for (1.14)) if the constant path is the unique minimiser of
the loss among bounded paths satisfying the structural equations and the initial constraints
(`π₀ = π̄`, and `x₀ = x̄` when the IS relation (1.15) is a constraint). The proofs are Lagrangian
sufficiency with constant multipliers (the telescoping identity `hasSum_telescope`) and, for the
converse, an explicit three-period feasible perturbation (`pertPi`, `pertX`). -/

/-- Woodford (2003), eq. (1.1), p. 469: the deterministic aggregate-supply relation
`π_t = κ x_t + β π_{t+1}` for every `t ≥ 0`. -/
def AS11 (β κ : ℝ) (π x : ℕ → ℝ) : Prop := ∀ t, π t = κ * x t + β * π (t + 1)

/-- Woodford (2003), eq. (1.2), p. 469: the discounted loss `∑ βᵗ [π_t² + λ (x_t − x*)²]`. -/
noncomputable def loss12 (β lam xstar : ℝ) (π x : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * (π t ^ 2 + lam * (x t - xstar) ^ 2)

/-- Woodford (2003), p. 474 (optimality from a timeless perspective, loss (1.2)): the constant
plan `π_t = π̄`, `x_t = (1 − β) π̄ / κ` minimises (1.2) among bounded paths satisfying (1.1) and
the initial constraint `π₀ = π̄`, and it is the only minimiser. -/
def TimelessOpt12 (β κ lam xstar πbar : ℝ) : Prop :=
  ∀ π x : ℕ → ℝ, AS11 β κ π x → Bdd π → Bdd x → π 0 = πbar →
    loss12 β lam xstar (fun _ => πbar) (fun _ => (1 - β) / κ * πbar) ≤ loss12 β lam xstar π x ∧
    (loss12 β lam xstar π x = loss12 β lam xstar (fun _ => πbar) (fun _ => (1 - β) / κ * πbar) →
      π = (fun _ => πbar) ∧ x = fun _ => (1 - β) / κ * πbar)

/-- Woodford (2003), p. 474 (Lagrangian sufficiency for (1.2), the expansion): for a bounded path
satisfying (1.1) with `π₀ = π̄`, the loss exceeds that of the constant plan by
`2 π̄ ∑ βᵗ (π_t − π̄) + ∑ βᵗ [(π_t − π̄)² + λ (x_t − x̄)²]`; the multiplier term
`λ(x̄ − x*)(x_t − x̄) = (λ(x̄ − x*)/κ)(Δπ_t − β Δπ_{t+1})` telescopes to zero. -/
theorem loss12_sub {β κ lam xstar πbar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : κ ≠ 0)
    {π x : ℕ → ℝ} (hAS : AS11 β κ π x) (hπb : Bdd π) (hxb : Bdd x) (h0 : π 0 = πbar) :
    loss12 β lam xstar π x = loss12 β lam xstar (fun _ => πbar) (fun _ => (1 - β) / κ * πbar) +
      (2 * πbar * (∑' t, β ^ t * (π t - πbar)) +
        ∑' t, β ^ t * (1 * (π t - πbar) ^ 2 + lam * (x t - (1 - β) / κ * πbar) ^ 2)) := by
  set xb := (1 - β) / κ * πbar with hxb_def
  have hsteady : πbar = κ * xb + β * πbar := by rw [hxb_def]; field_simp; ring
  obtain ⟨Mp, hMp⟩ := bdd_sub_const hπb πbar
  obtain ⟨Mq, hMq⟩ := bdd_lin (Bdd.sq (bdd_sub_const hπb πbar)) (Bdd.sq (bdd_sub_const hxb xb))
    1 lam
  have hS := (summable_disc hβ0 hβ1 hMp).hasSum
  have hQ := (summable_disc hβ0 hβ1 hMq).hasSum
  have hT := hasSum_telescope hβ0 hβ1 hMp
  have hC := hasSum_disc_const hβ0 hβ1 (πbar ^ 2 + lam * (xb - xstar) ^ 2)
  set p2 := lam * (xb - xstar) / κ with hp2
  have e2 : lam * (xb - xstar) = κ * p2 := by rw [hp2]; field_simp
  have hD := (((hS.mul_left (2 * πbar)).add (hT.mul_left (2 * p2))).add hQ).add hC
  have hL : loss12 β lam xstar (fun _ => πbar) (fun _ => xb) =
      (1 - β)⁻¹ * (πbar ^ 2 + lam * (xb - xstar) ^ 2) := by
    unfold loss12
    exact hC.tsum_eq
  rw [h0, sub_self, mul_zero, add_zero] at hD
  rw [hL]
  have hfg : (∑' t, β ^ t * (π t ^ 2 + lam * (x t - xstar) ^ 2)) =
      ∑' t, (((2 * πbar * (β ^ t * (π t - πbar)) +
        2 * p2 * (β ^ t * ((π t - πbar) - β * (π (t + 1) - πbar)))) +
        β ^ t * (1 * (π t - πbar) ^ 2 + lam * (x t - xb) ^ 2)) +
        β ^ t * (πbar ^ 2 + lam * (xb - xstar) ^ 2)) := by
    refine tsum_congr fun t => ?_
    have e1 := hAS t
    linear_combination (β ^ t) * 2 * (x t - xb) * e2 - (β ^ t) * 2 * p2 * e1 +
      (β ^ t) * 2 * p2 * hsteady
  change (∑' t, β ^ t * (π t ^ 2 + lam * (x t - xstar) ^ 2)) = _
  rw [hfg, hD.tsum_eq]
  ring


/-- Woodford (2003), pp. 474–478 (the converse direction of Props 7.2 and 7.3): the inflation
component `Δπ = (0, 0, 1, 0, 0, …)` of a three-period perturbation of a constant plan. -/
noncomputable def pertPi (t : ℕ) : ℝ := if t = 2 then 1 else 0

/-- Woodford (2003), pp. 474–478: the output-gap component `Δx = (0, −β/κ, 1/κ, 0, …)` of the
perturbation, chosen so that `Δπ_t = κ Δx_t + β Δπ_{t+1}` for every `t` and `Δπ₀ = Δx₀ = 0`. -/
noncomputable def pertX (β κ : ℝ) (t : ℕ) : ℝ :=
  if t = 1 then -β / κ else if t = 2 then 1 / κ else 0

/-- Woodford (2003), eq. (1.1), p. 469: the perturbation satisfies the homogeneous
aggregate-supply relation. -/
theorem pert_AS {β κ : ℝ} (hκ : κ ≠ 0) (t : ℕ) :
    pertPi t = κ * pertX β κ t + β * pertPi (t + 1) := by
  match t with
  | 0 => simp [pertPi, pertX]
  | 1 => simp [pertPi, pertX]; field_simp; ring
  | 2 => simp [pertPi, pertX]; field_simp
  | n + 3 => simp [pertPi, pertX]

/-- Woodford (2003), pp. 474–478 (tool): the perturbation is bounded. -/
theorem pert_bdd (β κ : ℝ) : Bdd pertPi ∧ Bdd (pertX β κ) := by
  refine ⟨⟨1, fun t => ?_⟩, ⟨|β / κ| + |1 / κ|, fun t => ?_⟩⟩
  · unfold pertPi; split_ifs <;> simp
  · have h1 := abs_nonneg (β / κ)
    have h2 := abs_nonneg (1 / κ)
    unfold pertX
    split_ifs
    · rw [neg_div, abs_neg]; linarith
    · linarith
    · simp only [abs_zero]; linarith

/-- Woodford (2003), pp. 474–478: the discounted sum of the inflation perturbation is `β²`. -/
theorem hasSum_pertPi (β : ℝ) : HasSum (fun t => β ^ t * pertPi t) (β ^ 2) := by
  have e : (fun t => β ^ t * pertPi t) = fun t => if t = 2 then β ^ 2 else 0 := by
    funext t
    unfold pertPi
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero]
  rw [e]
  exact hasSum_ite_eq 2 _

/-- Woodford (2003), pp. 474–478: a weighted discounted sum of squares of the perturbation that
is at least `β²` (the period-2 term). -/
theorem pert_sq_pos {β κ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {lam : ℝ} (hlam : 0 ≤ lam)
    {k : ℕ → ℝ} (hk : Bdd k) {w : ℝ} (hw : 0 ≤ w) :
    0 < ∑' t, β ^ t * (1 * pertPi t ^ 2 + lam * pertX β κ t ^ 2 + w * k t ^ 2) := by
  obtain ⟨hp, hx⟩ := pert_bdd β κ
  obtain ⟨M, hM⟩ := bdd_lin (bdd_lin (Bdd.sq hp) (Bdd.sq hx) 1 lam) (Bdd.sq hk) 1 w
  have hs := (summable_disc hβ0.le hβ1 (a := fun t => 1 * (1 * pertPi t ^ 2 +
    lam * pertX β κ t ^ 2) + w * k t ^ 2) hM).hasSum
  have hnn : ∀ t, 0 ≤ β ^ t * (1 * (1 * pertPi t ^ 2 + lam * pertX β κ t ^ 2) + w * k t ^ 2) :=
    fun t => by positivity
  have h2 := le_hasSum hs 2 (fun j _ => hnn j)
  have hv : β ^ 2 * (1 * (1 * pertPi 2 ^ 2 + lam * pertX β κ 2 ^ 2) + w * k 2 ^ 2) ≥ β ^ 2 := by
    have : pertPi 2 = 1 := by simp [pertPi]
    rw [this]
    have : 0 ≤ lam * pertX β κ 2 ^ 2 + w * k 2 ^ 2 := by positivity
    nlinarith [pow_pos hβ0 2]
  have hpos : 0 < β ^ 2 := by positivity
  rw [← hs.tsum_eq] at h2
  have e : (∑' t, β ^ t * (1 * pertPi t ^ 2 + lam * pertX β κ t ^ 2 + w * k t ^ 2)) =
      ∑' t, β ^ t * (1 * (1 * pertPi t ^ 2 + lam * pertX β κ t ^ 2) + w * k t ^ 2) :=
    tsum_congr fun t => by ring
  rw [e]
  linarith

/-- **Proposition 7.2** restated (Woodford (2003), p. 475; deterministic, loss (1.2)): with
`0 < β < 1`, `κ > 0`, `λ > 0` and any `x*`, the constant plan with inflation `π̄` is optimal from
a timeless perspective iff `π̄ = 0`. Sufficiency is Lagrangian sufficiency (`loss12_sub`), with
uniqueness from strict convexity; necessity is the three-period perturbation of size
`ε = −π̄β²/q`, which lowers the loss by `π̄²β⁴/q`. -/
theorem timelessOpt12_iff {β κ lam xstar πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) : TimelessOpt12 β κ lam xstar πbar ↔ πbar = 0 := by
  constructor
  · intro hopt
    by_contra hne
    set q := ∑' t, β ^ t * (1 * pertPi t ^ 2 + lam * pertX β κ t ^ 2 + 0 * (0 : ℕ → ℝ) t ^ 2)
      with hq
    have hqpos : 0 < q := pert_sq_pos hβ0 hβ1 hlam.le ⟨0, fun _ => by simp⟩ le_rfl
    set ε := -πbar * β ^ 2 / q with hε
    set xb := (1 - β) / κ * πbar with hxb
    have hsteady : πbar = κ * xb + β * πbar := by rw [hxb]; field_simp; ring
    obtain ⟨hpb, hxpb⟩ := pert_bdd β κ
    have hAS : AS11 β κ (fun t => πbar + ε * pertPi t) (fun t => xb + ε * pertX β κ t) := by
      intro t
      have := pert_AS (β := β) hκ.ne' t
      simp only
      linear_combination hsteady + ε * this
    have hb1 : Bdd (fun t => πbar + ε * pertPi t) := by
      obtain ⟨M, hM⟩ := bdd_lin (y := fun _ => 1) ⟨1, fun _ => by simp⟩ hpb πbar ε
      exact ⟨M, fun t => by simpa only [mul_one] using hM t⟩
    have hb2 : Bdd (fun t => xb + ε * pertX β κ t) := by
      obtain ⟨M, hM⟩ := bdd_lin (y := fun _ => 1) ⟨1, fun _ => by simp⟩ hxpb xb ε
      exact ⟨M, fun t => by simpa only [mul_one] using hM t⟩
    have h0 : (fun t => πbar + ε * pertPi t) 0 = πbar := by simp [pertPi]
    have hle := (hopt _ _ hAS hb1 hb2 h0).1
    rw [loss12_sub hβ0.le hβ1 hκ.ne' hAS hb1 hb2 h0] at hle
    have hS : (∑' t, β ^ t * ((πbar + ε * pertPi t) - πbar)) = ε * β ^ 2 := by
      rw [← (hasSum_pertPi β).tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun t => by ring
    have hQ : (∑' t, β ^ t * (1 * ((πbar + ε * pertPi t) - πbar) ^ 2 +
        lam * ((xb + ε * pertX β κ t) - (1 - β) / κ * πbar) ^ 2)) = ε ^ 2 * q := by
      rw [hq, ← tsum_mul_left]
      exact tsum_congr fun t => by rw [hxb]; ring
    rw [hS, hQ] at hle
    have hkey : 2 * πbar * (ε * β ^ 2) + ε ^ 2 * q = -(πbar ^ 2 * β ^ 4 / q) := by
      rw [hε]; field_simp; ring
    have : 0 < πbar ^ 2 * β ^ 4 / q := by positivity
    linarith
  · rintro rfl π x hAS hπb hxb h0
    have e := loss12_sub (lam := lam) (xstar := xstar) hβ0.le hβ1 hκ.ne' hAS hπb hxb h0
    simp only [mul_zero, zero_mul, sub_zero, zero_add] at e ⊢
    obtain ⟨M, hM⟩ := bdd_lin (Bdd.sq hπb) (Bdd.sq hxb) 1 lam
    have hQs := (summable_disc hβ0.le hβ1 hM).hasSum
    have hnn : ∀ t, 0 ≤ β ^ t * (1 * π t ^ 2 + lam * x t ^ 2) := fun t => by positivity
    have hQ0 := hQs.nonneg hnn
    refine ⟨by rw [e]; linarith, fun heq => ?_⟩
    rw [e, add_eq_left] at heq
    have hz := (hasSum_zero_iff_of_nonneg hnn).mp (heq ▸ hQs)
    have hpt : ∀ t, π t = 0 ∧ x t = 0 := by
      intro t
      have h := congrFun hz t
      simp only [Pi.zero_apply] at h
      have hb : 0 < β ^ t := pow_pos hβ0 t
      have h' : 1 * π t ^ 2 + lam * x t ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h hb.ne'
        · exact h
      have hx2 : x t ^ 2 = 0 := by nlinarith [sq_nonneg (π t), sq_nonneg (x t)]
      have hp2 : π t ^ 2 = 0 := by nlinarith [sq_nonneg (π t), sq_nonneg (x t)]
      exact ⟨pow_eq_zero_iff (two_ne_zero) |>.mp hp2, pow_eq_zero_iff (two_ne_zero) |>.mp hx2⟩
    exact ⟨funext fun t => (hpt t).1, funext fun t => (hpt t).2⟩


/-- Woodford (2003), eqs. (1.1) and (1.15), pp. 469 and 477: the deterministic AS relation
`π_t = κ x_t + β π_{t+1}` and IS relation `x_t = x_{t+1} − σ (i_t − π_{t+1} − r̄)`, for every
`t ≥ 0`. -/
def Feas115 (β κ σ rbar : ℝ) (π x i : ℕ → ℝ) : Prop :=
  ∀ t, π t = κ * x t + β * π (t + 1) ∧ x t = x (t + 1) - σ * (i t - π (t + 1) - rbar)

/-- Woodford (2003), eq. (1.14), p. 476 (and the deterministic part of (2.24), p. 503): the loss
`∑ βᵗ [π_t² + λₓ (x_t − x*)² + λᵢ (i_t − i*)²]`. -/
noncomputable def loss114 (β lx li xstar istar : ℝ) (π x i : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * (π t ^ 2 + lx * (x t - xstar) ^ 2 + li * (i t - istar) ^ 2)

/-- Woodford (2003), p. 477 (optimality from a timeless perspective, loss (1.14)): the constant
plan `π_t = π̄`, `x_t = x̄ = (1 − β) π̄ / κ`, `i_t = ī = r̄ + π̄` minimises (1.14) among bounded
paths satisfying (1.1), (1.15) and the initial constraints `π₀ = π̄`, `x₀ = x̄`, and it is the
only minimiser. -/
def TimelessOpt114 (β κ σ rbar lx li xstar istar πbar : ℝ) : Prop :=
  ∀ π x i : ℕ → ℝ, Feas115 β κ σ rbar π x i → Bdd π → Bdd x → Bdd i → π 0 = πbar →
    x 0 = (1 - β) / κ * πbar →
    loss114 β lx li xstar istar (fun _ => πbar) (fun _ => (1 - β) / κ * πbar)
        (fun _ => rbar + πbar) ≤ loss114 β lx li xstar istar π x i ∧
    (loss114 β lx li xstar istar π x i = loss114 β lx li xstar istar (fun _ => πbar)
        (fun _ => (1 - β) / κ * πbar) (fun _ => rbar + πbar) →
      π = (fun _ => πbar) ∧ x = (fun _ => (1 - β) / κ * πbar) ∧ i = fun _ => rbar + πbar)

/-- Woodford (2003), (1.19), p. 478: the timelessly optimal inflation target
`π̄ = −λᵢ (r̄ − i*)/(λᵢ + β) = λᵢ (i* − r̄)/(λᵢ + β)`, which is (3.11), p. 514. -/
noncomputable def piBar119 (β li rbar istar : ℝ) : ℝ := li * (istar - rbar) / (li + β)

/-- Woodford (2003), pp. 477–478 (Lagrangian sufficiency for (1.14), the expansion): for a bounded
path satisfying (1.1) and (1.15) with `π₀ = π̄`, `x₀ = x̄`, the loss exceeds that of the constant
plan by `2 c ∑ βᵗ (π_t − π̄) + ∑ βᵗ [(π_t − π̄)² + λₓ(x_t − x̄)² + λᵢ(i_t − ī)²]`, where
`c = π̄ + λᵢ (ī − i*)/β`. The constant multipliers `φ₁ = −λᵢ(ī − i*)/σ` (from (1.18)) and `φ₂`
(from (1.17)) make every other term telescope. -/
theorem loss114_sub {β κ σ rbar lx li xstar istar πbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : κ ≠ 0) (hσ : σ ≠ 0) {π x i : ℕ → ℝ} (hF : Feas115 β κ σ rbar π x i) (hπb : Bdd π)
    (hxb : Bdd x) (hib : Bdd i) (h0 : π 0 = πbar) (hx0 : x 0 = (1 - β) / κ * πbar) :
    loss114 β lx li xstar istar π x i = loss114 β lx li xstar istar (fun _ => πbar)
        (fun _ => (1 - β) / κ * πbar) (fun _ => rbar + πbar) +
      (2 * (πbar + li * (rbar + πbar - istar) / β) * (∑' t, β ^ t * (π t - πbar)) +
        ∑' t, β ^ t * (1 * (π t - πbar) ^ 2 + lx * (x t - (1 - β) / κ * πbar) ^ 2 +
          li * (i t - (rbar + πbar)) ^ 2)) := by
  set xb := (1 - β) / κ * πbar with hxb_def
  set ib := rbar + πbar with hib_def
  have hs1 : πbar = κ * xb + β * πbar := by rw [hxb_def]; field_simp; ring
  have hs2 : xb = xb - σ * (ib - πbar - rbar) := by rw [hib_def]; ring
  obtain ⟨Mp, hMp⟩ := bdd_sub_const hπb πbar
  obtain ⟨Mx, hMx⟩ := bdd_sub_const hxb xb
  obtain ⟨Mq, hMq⟩ := bdd_lin (bdd_lin (Bdd.sq (bdd_sub_const hπb πbar))
    (Bdd.sq (bdd_sub_const hxb xb)) 1 lx) (Bdd.sq (bdd_sub_const hib ib)) 1 li
  have hS := (summable_disc hβ0.le hβ1 hMp).hasSum
  have hQ := (summable_disc hβ0.le hβ1 hMq).hasSum
  have hT1 := hasSum_telescope hβ0.le hβ1 hMp
  have hT2 := hasSum_telescope hβ0.le hβ1 hMx
  have hC := hasSum_disc_const hβ0.le hβ1
    (πbar ^ 2 + lx * (xb - xstar) ^ 2 + li * (ib - istar) ^ 2)
  set b := -(li * (ib - istar)) / (σ * β) with hb
  set p2 := (lx * (xb - xstar) + β * b - b) / κ with hp2
  have hN : li * (ib - istar) = -(σ * β * b) := by rw [hb]; field_simp
  have hL : lx * (xb - xstar) = κ * p2 - β * b + b := by rw [hp2]; field_simp; ring
  have hc : πbar + li * (rbar + πbar - istar) / β = πbar - σ * b := by
    rw [hb, hib_def]; field_simp; ring
  have hD := ((((hS.mul_left (2 * (πbar - σ * b))).add (hT1.mul_left (2 * (p2 + σ * b)))).add
    (hT2.mul_left (2 * b))).add hQ).add hC
  rw [h0, hx0, sub_self, sub_self, mul_zero, mul_zero, add_zero, add_zero] at hD
  have hLc : loss114 β lx li xstar istar (fun _ => πbar) (fun _ => xb) (fun _ => ib) =
      (1 - β)⁻¹ * (πbar ^ 2 + lx * (xb - xstar) ^ 2 + li * (ib - istar) ^ 2) := by
    unfold loss114
    exact hC.tsum_eq
  rw [hLc, hc]
  have hfg : (∑' t, β ^ t * (π t ^ 2 + lx * (x t - xstar) ^ 2 + li * (i t - istar) ^ 2)) =
      ∑' t, ((((2 * (πbar - σ * b) * (β ^ t * (π t - πbar)) +
        2 * (p2 + σ * b) * (β ^ t * ((π t - πbar) - β * (π (t + 1) - πbar)))) +
        2 * b * (β ^ t * ((x t - xb) - β * (x (t + 1) - xb)))) +
        β ^ t * (1 * (1 * (π t - πbar) ^ 2 + lx * (x t - xb) ^ 2) + li * (i t - ib) ^ 2)) +
        β ^ t * (πbar ^ 2 + lx * (xb - xstar) ^ 2 + li * (ib - istar) ^ 2)) := by
    refine tsum_congr fun t => ?_
    obtain ⟨e1, e3⟩ := hF t
    linear_combination (β ^ t) * (2 * (x t - xb) * hL + 2 * (i t - ib) * hN - 2 * p2 * e1 +
      2 * p2 * hs1 - 2 * β * b * e3 + 2 * β * b * hs2)
  change (∑' t, β ^ t * (π t ^ 2 + lx * (x t - xstar) ^ 2 + li * (i t - istar) ^ 2)) = _
  rw [hfg, hD.tsum_eq, tsum_congr (fun t => (by ring : β ^ t * (1 * (1 * (π t - πbar) ^ 2 +
    lx * (x t - xb) ^ 2) + li * (i t - ib) ^ 2) = β ^ t * (1 * (π t - πbar) ^ 2 +
    lx * (x t - xb) ^ 2 + li * (i t - ib) ^ 2)))]
  ring

/-- Woodford (2003), p. 477 (the perturbation for (1.15)): the interest-rate component
`Δi_t = (Δx_{t+1} − Δx_t)/σ + Δπ_{t+1}`, which makes the perturbation satisfy the homogeneous IS
relation. -/
noncomputable def pertI (β κ σ : ℝ) (t : ℕ) : ℝ :=
  (pertX β κ (t + 1) - pertX β κ t) / σ + pertPi (t + 1)

/-- **Proposition 7.3** restated (Woodford (2003), p. 478; deterministic, loss (1.14), constraints
(1.1) and (1.15)): with `0 < β < 1`, `κ, σ, λₓ > 0`, `λᵢ ≥ 0`, the constant plan with inflation
`π̄` (and `x̄ = (1 − β)π̄/κ`, `ī = r̄ + π̄`) is optimal from a timeless perspective iff
`π̄ = λᵢ (i* − r̄)/(λᵢ + β)`, eq. (1.19) = (3.11). Sufficiency is Lagrangian sufficiency
(`loss114_sub`) with uniqueness; necessity is the three-period perturbation. -/
theorem timelessOpt114_iff {β κ σ rbar lx li xstar istar πbar : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) :
    TimelessOpt114 β κ σ rbar lx li xstar istar πbar ↔ πbar = piBar119 β li rbar istar := by
  have hc_iff : πbar + li * (rbar + πbar - istar) / β = 0 ↔ πbar = piBar119 β li rbar istar := by
    unfold piBar119
    have : li + β ≠ 0 := by linarith
    constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h; rw [h]; field_simp; ring
  rw [← hc_iff]
  set c := πbar + li * (rbar + πbar - istar) / β with hc
  constructor
  · intro hopt
    by_contra hne
    obtain ⟨hpb, hxpb⟩ := pert_bdd β κ
    have hkb : Bdd (pertI β κ σ) := by
      obtain ⟨M, hM⟩ := bdd_lin (bdd_lin (y := fun t => pertX β κ (t + 1)) (z := pertX β κ)
        ⟨hxpb.choose, fun t => hxpb.choose_spec (t + 1)⟩ hxpb (1 / σ) (-(1 / σ)))
        (z := fun t => pertPi (t + 1)) ⟨hpb.choose, fun t => hpb.choose_spec (t + 1)⟩ 1 1
      exact ⟨M, fun t => by
        have := hM t; unfold pertI; convert this using 2; ring⟩
    set q := ∑' t, β ^ t * (1 * pertPi t ^ 2 + lx * pertX β κ t ^ 2 + li * pertI β κ σ t ^ 2)
      with hq
    have hqpos : 0 < q := pert_sq_pos hβ0 hβ1 hlx.le hkb hli
    set ε := -c * β ^ 2 / q with hε
    set xb := (1 - β) / κ * πbar with hxb
    have hs1 : πbar = κ * xb + β * πbar := by rw [hxb]; field_simp; ring
    have hF : Feas115 β κ σ rbar (fun t => πbar + ε * pertPi t) (fun t => xb + ε * pertX β κ t)
        (fun t => rbar + πbar + ε * pertI β κ σ t) := by
      intro t
      have h1 := pert_AS (β := β) hκ.ne' t
      have h2 : σ * pertI β κ σ t = pertX β κ (t + 1) - pertX β κ t + σ * pertPi (t + 1) := by
        unfold pertI; field_simp
      refine ⟨by simp only; linear_combination hs1 + ε * h1, ?_⟩
      simp only
      linear_combination ε * h2
    have hbd : ∀ (a e : ℝ) (k : ℕ → ℝ), Bdd k → Bdd (fun t => a + e * k t) := by
      intro a e k hk
      obtain ⟨M, hM⟩ := bdd_lin (y := fun _ => 1) ⟨1, fun _ => by simp⟩ hk a e
      exact ⟨M, fun t => by simpa only [mul_one] using hM t⟩
    have hb3 : Bdd (fun t => rbar + πbar + ε * pertI β κ σ t) := hbd _ _ _ hkb
    have h0 : (fun t => πbar + ε * pertPi t) 0 = πbar := by simp [pertPi]
    have hx0 : (fun t => xb + ε * pertX β κ t) 0 = (1 - β) / κ * πbar := by simp [pertX, hxb]
    have hle := (hopt _ _ _ hF (hbd _ _ _ hpb) (hbd _ _ _ hxpb) hb3 h0 hx0).1
    rw [loss114_sub hβ0 hβ1 hκ.ne' hσ.ne' hF (hbd _ _ _ hpb) (hbd _ _ _ hxpb) hb3 h0 hx0] at hle
    have hS : (∑' t, β ^ t * ((πbar + ε * pertPi t) - πbar)) = ε * β ^ 2 := by
      rw [← (hasSum_pertPi β).tsum_eq, ← tsum_mul_left]
      exact tsum_congr fun t => by ring
    have hQ : (∑' t, β ^ t * (1 * ((πbar + ε * pertPi t) - πbar) ^ 2 +
        lx * ((xb + ε * pertX β κ t) - (1 - β) / κ * πbar) ^ 2 +
        li * ((rbar + πbar + ε * pertI β κ σ t) - (rbar + πbar)) ^ 2)) = ε ^ 2 * q := by
      rw [hq, ← tsum_mul_left]
      exact tsum_congr fun t => by rw [hxb]; ring
    rw [← hc, hS, hQ] at hle
    have hkey : 2 * c * (ε * β ^ 2) + ε ^ 2 * q = -(c ^ 2 * β ^ 4 / q) := by
      rw [hε]; field_simp; ring
    have : 0 < c ^ 2 * β ^ 4 / q := by positivity
    linarith
  · intro hc0 π x i hF hπb hxb hib h0 hx0
    have e := loss114_sub (lx := lx) (li := li) (xstar := xstar) (istar := istar) hβ0 hβ1
      hκ.ne' hσ.ne' hF hπb hxb hib h0 hx0
    rw [← hc, hc0, mul_zero, zero_mul, zero_add] at e
    set xb := (1 - β) / κ * πbar with hxb_def
    set ib := rbar + πbar with hib_def
    obtain ⟨M, hM⟩ := bdd_lin (bdd_lin (Bdd.sq (bdd_sub_const hπb πbar))
      (Bdd.sq (bdd_sub_const hxb xb)) 1 lx) (Bdd.sq (bdd_sub_const hib ib)) 1 li
    have hQs := (summable_disc hβ0.le hβ1 hM).hasSum
    have hnn : ∀ t, 0 ≤ β ^ t * (1 * (1 * (π t - πbar) ^ 2 + lx * (x t - xb) ^ 2) +
        li * (i t - ib) ^ 2) := fun t => by positivity
    have hQ0 := hQs.nonneg hnn
    have e' : (∑' t, β ^ t * (1 * (π t - πbar) ^ 2 + lx * (x t - xb) ^ 2 +
        li * (i t - ib) ^ 2)) = ∑' t, β ^ t * (1 * (1 * (π t - πbar) ^ 2 +
        lx * (x t - xb) ^ 2) + li * (i t - ib) ^ 2) := tsum_congr fun t => by ring
    rw [e'] at e
    refine ⟨by rw [e]; linarith, fun heq => ?_⟩
    rw [e, add_eq_left] at heq
    have hz := (hasSum_zero_iff_of_nonneg hnn).mp (heq ▸ hQs)
    have hpt : ∀ t, π t = πbar ∧ x t = xb := by
      intro t
      have h := congrFun hz t
      simp only [Pi.zero_apply] at h
      have hb : 0 < β ^ t := pow_pos hβ0 t
      have h' : 1 * (1 * (π t - πbar) ^ 2 + lx * (x t - xb) ^ 2) + li * (i t - ib) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h hb.ne'
        · exact h
      have h3 : 0 ≤ li * (i t - ib) ^ 2 := by positivity
      have hx2 : (x t - xb) ^ 2 = 0 := by
        nlinarith [sq_nonneg (π t - πbar), sq_nonneg (x t - xb)]
      have hp2 : (π t - πbar) ^ 2 = 0 := by
        nlinarith [sq_nonneg (π t - πbar), sq_nonneg (x t - xb)]
      exact ⟨by linarith [pow_eq_zero_iff (two_ne_zero) |>.mp hp2],
        by linarith [pow_eq_zero_iff (two_ne_zero) |>.mp hx2]⟩
    refine ⟨funext fun t => (hpt t).1, funext fun t => (hpt t).2, funext fun t => ?_⟩
    obtain ⟨-, e3⟩ := hF t
    rw [(hpt t).2, (hpt (t + 1)).2, (hpt (t + 1)).1] at e3
    have : σ * (i t - ib) = 0 := by rw [hib_def]; linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hσ.ne'
    · linarith


/-! ### The stochastic model and purely forward-looking plans -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eq. (2.1), p. 486: the aggregate-supply relation with cost-push shocks,
`π_t = κ x_t + β E_t π_{t+1} + u_t`, for every date. -/
def AS (β κ : ℝ) (π x u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = κ • x t + β • 𝔼.E t (π (t + 1)) + u t

/-- Woodford (2003), eq. (2.23), p. 502: the intertemporal IS relation
`x_t = E_t x_{t+1} − σ (i_t − E_t π_{t+1} − r^n_t)`, for every date. -/
def IS (σ : ℝ) (π x i rn : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • (i t - 𝔼.E t (π (t + 1)) - rn t)

omit 𝔼 in
/-- Woodford (2003), eq. (2.19), p. 497: a purely forward-looking plan `y_t = ȳ + f u_t`. -/
def plan1 (ybar f : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => ybar + f * u t ω

/-- Woodford (2003), eq. (2.18), p. 496: under an AR(1) disturbance `E_t u_{t+1} = ρ u_t`, so
`E_t (ȳ + f u_{t+1}) = ȳ + f ρ u_t`. -/
theorem E_plan1 {ρ : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (ybar f : ℝ) (t : ℕ) :
    𝔼.E t (plan1 ybar f u (t + 1)) = plan1 ybar (f * ρ) u t := by
  have e : plan1 ybar f u (t + 1) = (fun _ => ybar) + f • u (t + 1) := by
    funext ω; simp [plan1]
  rw [e, map_add, map_smul, 𝔼.const, hu.2 t]
  funext ω
  simp [plan1]
  ring

/-- Woodford (2003), eqs. (2.18) and (2.27), pp. 496 and 504: under AR(1) disturbances,
`E_t (ȳ + f u_{t+1} + g r̂_{t+1}) = ȳ + f ρ_u u_t + g ρ_r r̂_t`. -/
theorem E_plan2 {ρu ρr : ℝ} {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u) (hr : 𝔼.IsAR1 ρr r)
    (ybar f g : ℝ) (t : ℕ) :
    𝔼.E t (plan2 ybar f g u r (t + 1)) = plan2 ybar (f * ρu) (g * ρr) u r t := by
  have e : plan2 ybar f g u r (t + 1) = (fun _ => ybar) + f • u (t + 1) + g • r (t + 1) := by
    funext ω; simp [plan2_apply]
  rw [e, map_add, map_add, map_smul, map_smul, 𝔼.const, hu.2 t, hr.2 t]
  funext ω
  simp [plan2_apply]
  ring

omit 𝔼 in
/-- Woodford (2003), p. 511 (non-degenerate disturbance): the disturbance is not constant, i.e. it
takes two different values. This is what "the coefficients must satisfy" (3.2)–(3.3) uses. -/
def Nondeg1 (u : ℕ → Ω → ℝ) : Prop := ∃ t₁ ω₁ t₂ ω₂, u t₁ ω₁ ≠ u t₂ ω₂

omit 𝔼 in
/-- Woodford (2003), p. 512 (non-degenerate pair of disturbances): three realised values
`(u, r̂)` that are not collinear, so that an affine function of `(u_t, r̂_t)` vanishing at every
date and state has zero coefficients. -/
def Nondeg2 (u r : ℕ → Ω → ℝ) : Prop :=
  ∃ t₁ ω₁ t₂ ω₂ t₃ ω₃, (u t₂ ω₂ - u t₁ ω₁) * (r t₃ ω₃ - r t₁ ω₁) -
    (u t₃ ω₃ - u t₁ ω₁) * (r t₂ ω₂ - r t₁ ω₁) ≠ 0

omit 𝔼 in
/-- Woodford (2003), p. 511 (tool): an affine function `a + b u_t` vanishing at every date and
state of a non-degenerate disturbance has `a = b = 0`. -/
theorem affine_zero1 {u : ℕ → Ω → ℝ} (hu : Nondeg1 u) {a b : ℝ}
    (h : ∀ t ω, a + b * u t ω = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨t₁, ω₁, t₂, ω₂, hne⟩ := hu
  have h1 := h t₁ ω₁
  have h2 := h t₂ ω₂
  have hb : b * (u t₁ ω₁ - u t₂ ω₂) = 0 := by linear_combination h1 - h2
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right (sub_ne_zero.mpr hne)
  refine ⟨?_, hb0⟩
  rw [hb0] at h1
  linarith

omit 𝔼 in
/-- Woodford (2003), p. 512 (tool): an affine function `a + b u_t + c r̂_t` vanishing at every
date and state of a non-degenerate pair of disturbances has `a = b = c = 0`. -/
theorem affine_zero2 {u r : ℕ → Ω → ℝ} (hur : Nondeg2 u r) {a b c : ℝ}
    (h : ∀ t ω, a + b * u t ω + c * r t ω = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨t₁, ω₁, t₂, ω₂, t₃, ω₃, hdet⟩ := hur
  have h1 := h t₁ ω₁
  have h2 := h t₂ ω₂
  have h3 := h t₃ ω₃
  set D := (u t₂ ω₂ - u t₁ ω₁) * (r t₃ ω₃ - r t₁ ω₁) - (u t₃ ω₃ - u t₁ ω₁) * (r t₂ ω₂ - r t₁ ω₁)
  have hb : b * D = 0 := by
    linear_combination (r t₃ ω₃ - r t₁ ω₁) * (h2 - h1) - (r t₂ ω₂ - r t₁ ω₁) * (h3 - h1)
  have hc : c * D = 0 := by
    linear_combination (u t₂ ω₂ - u t₁ ω₁) * (h3 - h1) - (u t₃ ω₃ - u t₁ ω₁) * (h2 - h1)
  have hb0 := (mul_eq_zero.mp hb).resolve_right hdet
  have hc0 := (mul_eq_zero.mp hc).resolve_right hdet
  refine ⟨?_, hb0, hc0⟩
  rw [hb0, hc0] at h1
  linarith

/-- Woodford (2003), eqs. (3.2)–(3.3), p. 511 (= (2.20)–(2.21), p. 497): with an AR(1) cost-push
disturbance (2.18) that is not degenerate, a plan `π_t = π̄ + f_π u_t`, `x_t = x̄ + f_x u_t`
satisfies the aggregate-supply relation (2.1) at every date iff `(1 − β) π̄ = κ x̄` and
`(1 − β ρ) f_π = κ f_x + 1`. -/
theorem plan_AS_iff {β κ ρ : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hnd : Nondeg1 u)
    (πbar xbar fπ fx : ℝ) :
    AS 𝔼 β κ (plan1 πbar fπ u) (plan1 xbar fx u) u ↔
      (1 - β) * πbar = κ * xbar ∧ (1 - β * ρ) * fπ = κ * fx + 1 := by
  have key : ∀ t ω, (plan1 πbar fπ u t = κ • plan1 xbar fx u t +
      β • 𝔼.E t (plan1 πbar fπ u (t + 1)) + u t) →
      ((1 - β) * πbar - κ * xbar) + ((1 - β * ρ) * fπ - κ * fx - 1) * u t ω = 0 := by
    intro t ω h
    rw [E_plan1 𝔼 hu] at h
    have := congrFun h ω
    simp only [plan1, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  constructor
  · intro h
    have := affine_zero1 hnd (fun t ω => key t ω (h t))
    constructor <;> linarith [this.1, this.2]
  · rintro ⟨h1, h2⟩ t
    rw [E_plan1 𝔼 hu]
    funext ω
    simp only [plan1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h1 + u t ω * h2

/-- Woodford (2003), eq. (3.6), p. 512 and the "two linear restrictions on the coefficients
`f_y` and another set of two linear restrictions on the coefficients `g_y`" (p. 512; App. F.4):
with AR(1) disturbances `u` (2.18) and `r̂ⁿ` (2.27), `r^n_t = r̄ + r̂ⁿ_t`, non-degenerate as a pair,
a plan (3.6) for `(π, x, i)` satisfies (2.1) and (2.23) at every date iff the long-run values
satisfy `(1 − β) π̄ = κ x̄`, `ī = r̄ + π̄`, and the responses satisfy
`(1 − β ρ_u) f_π = κ f_x + 1`, `(1 − ρ_u) f_x = −σ (f_i − ρ_u f_π)`,
`(1 − β ρ_r) g_π = κ g_x`, `(1 − ρ_r) g_x = −σ (g_i − ρ_r g_π − 1)`. -/
theorem plan2_iff {β κ σ ρu ρr rbar : ℝ} (hσ : σ ≠ 0) {u r : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρu u)
    (hr : 𝔼.IsAR1 ρr r) (hnd : Nondeg2 u r) (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) :
    (AS 𝔼 β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u ∧
      IS 𝔼 σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
        (fun t ω => rbar + r t ω)) ↔
      ((1 - β) * πbar = κ * xbar ∧ ibar = rbar + πbar) ∧
      ((1 - β * ρu) * fπ = κ * fx + 1 ∧ (1 - ρu) * fx = -σ * (fi - ρu * fπ)) ∧
      ((1 - β * ρr) * gπ = κ * gx ∧ (1 - ρr) * gx = -σ * (gi - ρr * gπ - 1)) := by
  have kAS : ∀ t ω, (plan2 πbar fπ gπ u r t = κ • plan2 xbar fx gx u r t +
      β • 𝔼.E t (plan2 πbar fπ gπ u r (t + 1)) + u t) ↔
      ((1 - β) * πbar - κ * xbar) + ((1 - β * ρu) * fπ - κ * fx - 1) * u t ω +
        ((1 - β * ρr) * gπ - κ * gx) * r t ω = 0 ∧
      (plan2 πbar fπ gπ u r t = κ • plan2 xbar fx gx u r t +
      β • 𝔼.E t (plan2 πbar fπ gπ u r (t + 1)) + u t) := by
    intro t ω
    refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
    have h' := h
    rw [E_plan2 𝔼 hu hr] at h'
    have := congrFun h' ω
    simp only [plan2_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  have kIS : ∀ t ω, (plan2 xbar fx gx u r t = 𝔼.E t (plan2 xbar fx gx u r (t + 1)) -
      σ • (plan2 ibar fi gi u r t - 𝔼.E t (plan2 πbar fπ gπ u r (t + 1)) -
        fun ω => rbar + r t ω)) →
      σ * (ibar - πbar - rbar) + ((1 - ρu) * fx + σ * (fi - ρu * fπ)) * u t ω +
        ((1 - ρr) * gx + σ * (gi - ρr * gπ - 1)) * r t ω = 0 := by
    intro t ω h
    rw [E_plan2 𝔼 hu hr, E_plan2 𝔼 hu hr] at h
    have := congrFun h ω
    simp only [plan2_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  constructor
  · rintro ⟨hA, hI⟩
    obtain ⟨a1, a2, a3⟩ := affine_zero2 hnd (fun t ω => ((kAS t ω).mp (hA t)).1)
    obtain ⟨i1, i2, i3⟩ := affine_zero2 hnd (fun t ω => kIS t ω (hI t))
    have hi : ibar - πbar - rbar = 0 := (mul_eq_zero.mp i1).resolve_left hσ
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [E_plan2 𝔼 hu hr]
      funext ω
      simp only [plan2_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination h1 + u t ω * h3 + r t ω * h5
    · rw [E_plan2 𝔼 hu hr, E_plan2 𝔼 hu hr]
      funext ω
      simp only [plan2_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination σ * h2 + u t ω * h4 + r t ω * h6


/-- Woodford (2003), eqs. (3.2)–(3.3), p. 511 (sufficiency, no non-degeneracy needed): a plan
whose coefficients satisfy (3.2) and (3.3) satisfies (2.1) at every date. -/
theorem plan_AS_of {β κ ρ : ℝ} {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) {πbar xbar fπ fx : ℝ}
    (h1 : (1 - β) * πbar = κ * xbar) (h2 : (1 - β * ρ) * fπ = κ * fx + 1) :
    AS 𝔼 β κ (plan1 πbar fπ u) (plan1 xbar fx u) u := by
  intro t
  rw [E_plan1 𝔼 hu]
  funext ω
  simp only [plan1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination h1 + u t ω * h2

/-! ### (3.5): the optimal noninertial responses to cost-push shocks -/

/-- Woodford (2003), eq. (3.5), p. 511 (= (2.22), p. 497): the optimal noninertial inflation
response `f_π^oni = (1 − βρ)/(κ²λ⁻¹ + (1 − βρ)²)`. -/
noncomputable def fpiOni (β κ lam ρ : ℝ) : ℝ := (1 - β * ρ) / (κ ^ 2 * lam⁻¹ + (1 - β * ρ) ^ 2)

/-- Woodford (2003), eq. (3.5), p. 511: the optimal noninertial output-gap response
`f_x^oni = −κλ⁻¹/(κ²λ⁻¹ + (1 − βρ)²)`. -/
noncomputable def fxOni (β κ lam ρ : ℝ) : ℝ := -(κ * lam⁻¹) / (κ ^ 2 * lam⁻¹ + (1 - β * ρ) ^ 2)

/-- Woodford (2003), eq. (3.5), p. 511: the coefficients (3.5) satisfy the constraint (3.3). -/
theorem oni_constraint {β κ lam ρ : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) :
    (1 - β * ρ) * fpiOni β κ lam ρ = κ * fxOni β κ lam ρ + 1 := by
  have hN : 0 < κ ^ 2 * lam⁻¹ + (1 - β * ρ) ^ 2 := by positivity
  unfold fpiOni fxOni
  field_simp
  ring

/-- Woodford (2003), eq. (3.5), p. 511 (the constrained minimisation): for every `(f_π, f_x)`
satisfying (3.3), `f_π² + λ f_x² = (value at (3.5)) + (f_π − f_π^oni)² + λ (f_x − f_x^oni)²`. -/
theorem oni_objective_eq {β κ lam ρ : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) {fπ fx : ℝ}
    (h : (1 - β * ρ) * fπ = κ * fx + 1) :
    fπ ^ 2 + lam * fx ^ 2 = fpiOni β κ lam ρ ^ 2 + lam * fxOni β κ lam ρ ^ 2 +
      ((fπ - fpiOni β κ lam ρ) ^ 2 + lam * (fx - fxOni β κ lam ρ) ^ 2) := by
  set N := κ ^ 2 * lam⁻¹ + (1 - β * ρ) ^ 2 with hNdef
  have hN : 0 < N := by positivity
  set p := fpiOni β κ lam ρ with hpdef
  set q := fxOni β κ lam ρ with hqdef
  have hp : p * N = 1 - β * ρ := by rw [hpdef, hNdef]; unfold fpiOni; field_simp
  have hq : lam * q * N = -κ := by rw [hqdef, hNdef]; unfold fxOni; field_simp
  have hc : (1 - β * ρ) * p = κ * q + 1 := oni_constraint hκ hlam
  have horth : N * (p * (fπ - p) + lam * q * (fx - q)) = 0 := by
    linear_combination (fπ - p) * hp + (fx - q) * hq + h - hc
  have h0 : p * (fπ - p) + lam * q * (fx - q) = 0 :=
    (mul_eq_zero.mp horth).resolve_left hN.ne'
  linear_combination 2 * h0

/-- Woodford (2003), eq. (3.5), p. 511: among coefficients satisfying (3.3), `f_π² + λ f_x²` has
the unique minimiser (3.5). -/
theorem oni_unique_min {β κ lam ρ : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (fπ fx : ℝ) :
    ((1 - β * ρ) * fπ = κ * fx + 1 ∧ ∀ gπ gx, (1 - β * ρ) * gπ = κ * gx + 1 →
      fπ ^ 2 + lam * fx ^ 2 ≤ gπ ^ 2 + lam * gx ^ 2) ↔
      fπ = fpiOni β κ lam ρ ∧ fx = fxOni β κ lam ρ := by
  constructor
  · rintro ⟨hf, hmin⟩
    have h1 := hmin _ _ (oni_constraint hκ hlam)
    rw [oni_objective_eq hκ hlam hf] at h1
    have hs : (fπ - fpiOni β κ lam ρ) ^ 2 + lam * (fx - fxOni β κ lam ρ) ^ 2 ≤ 0 := by linarith
    have a1 := sq_nonneg (fπ - fpiOni β κ lam ρ)
    have a2 : 0 ≤ lam * (fx - fxOni β κ lam ρ) ^ 2 := by positivity
    have e1 : (fπ - fpiOni β κ lam ρ) ^ 2 = 0 := by linarith
    have e2 : (fx - fxOni β κ lam ρ) ^ 2 = 0 := by
      have : lam * (fx - fxOni β κ lam ρ) ^ 2 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hlam.ne'
    exact ⟨by linarith [pow_eq_zero_iff two_ne_zero |>.mp e1],
      by linarith [pow_eq_zero_iff two_ne_zero |>.mp e2]⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨oni_constraint hκ hlam, fun gπ gx hg => ?_⟩
    rw [oni_objective_eq hκ hlam hg]
    have : 0 ≤ lam * (gx - fxOni β κ lam ρ) ^ 2 := by positivity
    nlinarith [sq_nonneg (gπ - fpiOni β κ lam ρ)]

/-! ### Discretion under AR(1) cost-push shocks (pp. 511–512) -/

/-- Woodford (2003), eq. (2.2), p. 487: the discretionary equilibrium condition
`π_t = (1 + κ²/λ)⁻¹ (κ x* + u_t + β E_t π_{t+1})` (period-by-period optimisation (1.4) combined
with (2.1)). -/
def Discretion (β κ lam xstar : ℝ) (π u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = (1 + κ ^ 2 / lam)⁻¹ • ((fun _ => κ * xstar) + u t + β • 𝔼.E t (π (t + 1)))

/-- Woodford (2003), p. 511: the average discretionary inflation rate
`π̄^disc = κλ x*/((1 − β)λ + κ²)` (= (1.6)). -/
noncomputable def piDisc (β κ lam xstar : ℝ) : ℝ := κ * lam / ((1 - β) * lam + κ ^ 2) * xstar

/-- Woodford (2003), p. 512: the discretionary inflation response to a cost-push shock,
`f_π^disc = λ/(κ² + (1 − βρ)λ)`. -/
noncomputable def fpiDisc (β κ lam ρ : ℝ) : ℝ := lam / (κ ^ 2 + (1 - β * ρ) * lam)

/-- Woodford (2003), eq. (1.4), p. 471 applied to (2.19): under discretion
`x_t = x* − (κ/λ) π_t`, so the output-gap response is `f_x^disc = −(κ/λ) f_π^disc`. -/
noncomputable def fxDisc (β κ lam ρ : ℝ) : ℝ := -(κ / lam) * fpiDisc β κ lam ρ

/-- Woodford (2003), eq. (1.4), p. 471: the average discretionary output gap
`x* − (κ/λ) π̄^disc`. -/
noncomputable def xDisc (β κ lam xstar : ℝ) : ℝ := xstar - κ / lam * piDisc β κ lam xstar

/-- Woodford (2003), pp. 511–512 (applying (2.3) to the AR(1) process (2.18)): with
`0 < β < 1`, `κ, λ > 0`, `|ρ| ≤ 1` and a bounded AR(1) disturbance, a bounded process solves the
discretionary condition (2.2) iff it is `π_t = π̄^disc + f_π^disc u_t`. -/
theorem discretion_iff {β κ lam xstar ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ : |ρ| ≤ 1) {u : ℕ → Ω → ℝ} (hu : 𝔼.IsAR1 ρ u) (hub : BoundedProc u)
    {π : ℕ → Ω → ℝ} (hπb : BoundedProc π) :
    Discretion 𝔼 β κ lam xstar π u ↔
      π = plan1 (piDisc β κ lam xstar) (fpiDisc β κ lam ρ) u := by
  have hβρ : β * ρ ≤ β := by
    have := abs_le.mp hρ
    nlinarith [this.1, this.2]
  have hβρ' : -β ≤ β * ρ := by
    have := abs_le.mp hρ
    nlinarith [this.1, this.2]
  have hD1 : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith
  have hD2 : 0 < κ ^ 2 + (1 - β * ρ) * lam := by nlinarith
  have hD3 : 0 < 1 + κ ^ 2 / lam := by positivity
  set a := (1 + κ ^ 2 / lam)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.mpr hD3
  have hk2 : 0 ≤ κ ^ 2 / lam := by positivity
  have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hsol : Discretion 𝔼 β κ lam xstar (plan1 (piDisc β κ lam xstar) (fpiDisc β κ lam ρ) u) u
      := by
    intro t
    rw [E_plan1 𝔼 hu]
    funext ω
    simp only [plan1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    set A := piDisc β κ lam xstar with hAdef
    set F := fpiDisc β κ lam ρ with hFdef
    have hA : A * ((1 - β) * lam + κ ^ 2) = κ * lam * xstar := by
      rw [hAdef]; unfold piDisc
      rw [mul_comm (κ * lam / _) xstar, mul_assoc, div_mul_cancel₀ _ hD1.ne']
      ring
    have hF : F * (κ ^ 2 + (1 - β * ρ) * lam) = lam := by
      rw [hFdef]; unfold fpiDisc; exact div_mul_cancel₀ _ hD2.ne'
    have ha' : (1 + κ ^ 2 / lam)⁻¹ = lam / (lam + κ ^ 2) := by field_simp
    have key : (A + F * u t ω) * (lam + κ ^ 2) =
        lam * (κ * xstar + u t ω + β * (A + F * ρ * u t ω)) := by
      linear_combination hA + u t ω * hF
    rw [ha']
    field_simp
    linear_combination key
  have hform : ∀ z : ℕ → Ω → ℝ, Discretion 𝔼 β κ lam xstar z u ↔
      ∀ t, z t = (a * β) • 𝔼.E t (z (t + 1)) + a • ((fun _ => κ * xstar) + u t) := by
    intro z
    refine forall_congr' fun t => ?_
    rw [smul_add a _ (β • _), smul_smul, add_comm (a • _)]
  constructor
  · intro h
    have hab : |a * β| < 1 := by
      rw [abs_of_pos (mul_pos ha0 hβ0)]
      nlinarith
    obtain ⟨M, hM⟩ := hub
    have hpb : BoundedProc (plan1 (piDisc β κ lam xstar) (fpiDisc β κ lam ρ) u) := by
      refine ⟨|piDisc β κ lam xstar| + |fpiDisc β κ lam ρ| * M, fun t ω => ?_⟩
      simp only [plan1]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)
    exact 𝔼.forward_unique hab ((hform π).mp h) ((hform _).mp hsol) hπb hpb
  · rintro rfl
    exact hsol

/-- Woodford (2003), pp. 511–512: the discretionary plan satisfies (2.1) with the output gap given
by (1.4), i.e. its coefficients satisfy (3.2) and (3.3). -/
theorem discretion_coeffs {β κ lam xstar ρ : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam)
    (hβρ : 0 < 1 - β * ρ) :
    (1 - β) * piDisc β κ lam xstar = κ * xDisc β κ lam xstar ∧
      (1 - β * ρ) * fpiDisc β κ lam ρ = κ * fxDisc β κ lam ρ + 1 := by
  have hD1 : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith
  have hD2 : 0 < κ ^ 2 + (1 - β * ρ) * lam := by positivity
  unfold xDisc fxDisc piDisc fpiDisc
  constructor <;> field_simp <;> ring

/-- Woodford (2003), p. 511: `π̄^disc > 0` when `x* > 0`. -/
theorem piDisc_pos {β κ lam xstar : ℝ} (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam)
    (hx : 0 < xstar) : 0 < piDisc β κ lam xstar := by
  have : 0 < 1 - β := by linarith
  unfold piDisc
  positivity

/-- Woodford (2003), p. 512: `f_π^disc ≥ f_π^oni` (for `0 ≤ ρ`, `0 < β`, `βρ < 1`). The
difference is `λ κ² (βρ) / ((κ² + (1 − βρ)λ)(κ² + λ(1 − βρ)²))`. -/
theorem fpiDisc_sub_fpiOni {β κ lam ρ : ℝ} (hκ : 0 < κ) (hlam : 0 < lam) (hβρ : 0 < 1 - β * ρ) :
    fpiDisc β κ lam ρ - fpiOni β κ lam ρ =
      lam * κ ^ 2 * (β * ρ) / ((κ ^ 2 + (1 - β * ρ) * lam) * (κ ^ 2 + lam * (1 - β * ρ) ^ 2)) := by
  have hD2 : 0 < κ ^ 2 + (1 - β * ρ) * lam := by positivity
  have hD3 : 0 < κ ^ 2 + lam * (1 - β * ρ) ^ 2 := by positivity
  unfold fpiDisc fpiOni
  field_simp
  ring

/-- Woodford (2003), p. 512: `f_π^disc ≥ f_π^oni`, "where the last inequality is strict if
`ρ_u > 0`" — and it is an equality iff `ρ_u = 0` (for `0 ≤ ρ < 1`, `0 < β < 1`). -/
theorem fpiDisc_ge_fpiOni {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    fpiOni β κ lam ρ ≤ fpiDisc β κ lam ρ ∧
      (fpiOni β κ lam ρ = fpiDisc β κ lam ρ ↔ ρ = 0) := by
  have hβρ : 0 < 1 - β * ρ := by nlinarith
  have hD2 : 0 < κ ^ 2 + (1 - β * ρ) * lam := by positivity
  have hD3 : 0 < κ ^ 2 + lam * (1 - β * ρ) ^ 2 := by positivity
  have e := fpiDisc_sub_fpiOni hκ hlam hβρ
  refine ⟨?_, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have : 0 ≤ lam * κ ^ 2 * (β * ρ) / ((κ ^ 2 + (1 - β * ρ) * lam) *
      (κ ^ 2 + lam * (1 - β * ρ) ^ 2)) := by positivity
    linarith
  · rw [h, sub_self] at e
    have hnum : lam * κ ^ 2 * (β * ρ) = 0 := by
      rcases div_eq_zero_iff.mp e.symm with h | h
      · exact h
      · exact absurd h (by positivity)
    have : lam * κ ^ 2 * β ≠ 0 := by positivity
    have h2 : lam * κ ^ 2 * β * ρ = 0 := by linear_combination hnum
    exact (mul_eq_zero.mp h2).resolve_left this
  · have e0 : fpiDisc β κ lam ρ - fpiOni β κ lam ρ = 0 := by rw [e, h]; simp
    linarith

/-- Woodford (2003), p. 512: "too large a positive inflation response `f_π` also means too small a
negative output-gap response `f_x`": `f_x^oni ≤ f_x^disc` (equality iff `ρ_u = 0`). -/
theorem fxDisc_ge_fxOni {β κ lam ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    fxOni β κ lam ρ ≤ fxDisc β κ lam ρ ∧ (fxOni β κ lam ρ = fxDisc β κ lam ρ ↔ ρ = 0) := by
  have hβρ : 0 < 1 - β * ρ := by nlinarith
  obtain ⟨hle, hiff⟩ := fpiDisc_ge_fpiOni hβ0 hβ1 hκ hlam hρ0 hρ1
  have c1 := oni_constraint (β := β) (ρ := ρ) hκ hlam
  have c2 := (discretion_coeffs (xstar := 0) hβ1 hκ hlam hβρ).2
  have key : κ * (fxDisc β κ lam ρ - fxOni β κ lam ρ) =
      (1 - β * ρ) * (fpiDisc β κ lam ρ - fpiOni β κ lam ρ) := by linear_combination c1 - c2
  refine ⟨?_, ⟨fun h => hiff.mp ?_, fun h => ?_⟩⟩
  · have : 0 ≤ κ * (fxDisc β κ lam ρ - fxOni β κ lam ρ) := by
      rw [key]; exact mul_nonneg hβρ.le (by linarith)
    have := (mul_nonneg_iff_of_pos_left hκ).mp this
    linarith
  · rw [h, sub_self, mul_zero] at key
    have := (mul_eq_zero.mp key.symm).resolve_left hβρ.ne'
    linarith
  · have e := hiff.mpr h
    rw [e, sub_self, mul_zero] at key
    have := (mul_eq_zero.mp key).resolve_left hκ.ne'
    linarith

/-- Woodford (2003), p. 512: "discretionary policy is suboptimal, even within the class of purely
forward-looking policies, except in the special case that `x* = 0` and the cost-push shocks are
serially uncorrelated": the discretionary plan has the optimal noninertial long-run inflation `0`
and response `f_π^oni` iff `x* = 0` and `ρ = 0`. -/
theorem discretion_eq_oni_iff {β κ lam xstar ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (piDisc β κ lam xstar = 0 ∧ fpiDisc β κ lam ρ = fpiOni β κ lam ρ) ↔ (xstar = 0 ∧ ρ = 0) := by
  have hD1 : 0 < (1 - β) * lam + κ ^ 2 := by nlinarith
  have hpd : piDisc β κ lam xstar = 0 ↔ xstar = 0 := by
    unfold piDisc
    have : κ * lam / ((1 - β) * lam + κ ^ 2) ≠ 0 := by positivity
    exact ⟨fun h => (mul_eq_zero.mp h).resolve_left this, fun h => by rw [h, mul_zero]⟩
  rw [hpd, eq_comm (a := fpiDisc β κ lam ρ), (fpiDisc_ge_fpiOni hβ0 hβ1 hκ hlam hρ0 hρ1).2]


/-! ### Conditional variances and the stabilization loss (3.4), (3.7), (3.8)

`L^stab = ∑_{t ≥ t₀} β^{t−t₀} [var_{t₀}(π_t) + λ var_{t₀}(x_t)]` (p. 509) is computed exactly
for AR(1) disturbances driven by innovations with constant conditional variance. This uses the
pull-out property (`PullOut`), which holds for perfect foresight and every finite event tree. -/

/-- Woodford (2003), eqs. (2.18) and (2.27), pp. 496 and 504: `u` is an adapted AR(1) process
`u_{t+1} = ρ u_t + ε_{t+1}` whose innovation is unforecastable, `E_t ε_{t+1} = 0`, with constant
conditional variance `E_t ε_{t+1}² = s`. -/
def AR1Innov (ρ s : ℝ) (u ε : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted u ∧ (∀ t, u (t + 1) = ρ • u t + ε (t + 1)) ∧ (∀ t, 𝔼.E t (ε (t + 1)) = 0) ∧
    ∀ t, 𝔼.E t (ε (t + 1) * ε (t + 1)) = fun _ => s

/-- Woodford (2003), eq. (2.18), p. 496: an AR(1) process with innovations satisfies
`E_t u_{t+1} = ρ u_t`. -/
theorem AR1Innov.isAR1 {ρ s : ℝ} {u ε : ℕ → Ω → ℝ} (h : AR1Innov 𝔼 ρ s u ε) : 𝔼.IsAR1 ρ u := by
  refine ⟨h.1, fun t => ?_⟩
  rw [h.2.1 t, map_add, map_smul, h.1 t, h.2.2.1 t, add_zero]

/-- Woodford (2003), p. 509 (tool): `E_{t₀}` of a product of a variable known at `t₀ + k` and a
next-period innovation is zero (tower and pull-out). -/
theorem E_mul_innov (hpo : 𝔼.PullOut) {ρ s : ℝ} {v ε : ℕ → Ω → ℝ} (hv : AR1Innov 𝔼 ρ s v ε)
    {X : Ω → ℝ} (t₀ k : ℕ) (hX : 𝔼.E (t₀ + k) X = X) :
    𝔼.E t₀ (X * ε (t₀ + k + 1)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t₀ k), hpo _ _ _ hX, hv.2.2.1, mul_zero, map_zero]

/-- Woodford (2003), p. 509 (tool): `E_{t₀}` of a later innovation is zero. -/
theorem E_innov (s0 : ℝ) {ρ : ℝ} {v ε : ℕ → Ω → ℝ} (hv : AR1Innov 𝔼 ρ s0 v ε) (t₀ k : ℕ) :
    𝔼.E t₀ (ε (t₀ + k + 1)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t₀ k), hv.2.2.1, map_zero]

/-- Woodford (2003), pp. 509, 512 (the covariance of two AR(1) disturbances): if the innovations
have constant conditional covariance `E_t(εᵘ_{t+1} εʳ_{t+1}) = c`, then
`cov_{t₀}(u_{t₀+k}, r_{t₀+k}) = c ∑_{j<k} (ρ_u ρ_r)ʲ`. With `u = r` this is the conditional
variance `var_{t₀}(u_{t₀+k}) = s ∑_{j<k} ρ^{2j}`. -/
theorem condCov_ar1 (hpo : 𝔼.PullOut) {ρu ρr su sr c : ℝ} {u εu r εr : ℕ → Ω → ℝ}
    (hu : AR1Innov 𝔼 ρu su u εu) (hr : AR1Innov 𝔼 ρr sr r εr)
    (hc : ∀ t, 𝔼.E t (εu (t + 1) * εr (t + 1)) = fun _ => c) (t₀ k : ℕ) :
    condCov 𝔼 t₀ (u (t₀ + k)) (r (t₀ + k)) =
      fun _ => c * ∑ j ∈ Finset.range k, (ρu * ρr) ^ j := by
  induction k with
  | zero =>
    simp only [add_zero, Finset.range_zero, Finset.sum_empty, mul_zero]
    unfold condCov
    rw [hpo _ _ _ (hu.1 t₀), hu.1 t₀, hr.1 t₀, sub_self]
    rfl
  | succ k ih =>
    have hEu := 𝔼.ar1_iterate (hu.isAR1 𝔼) t₀
    have hEr := 𝔼.ar1_iterate (hr.isAR1 𝔼) t₀
    have hprod : u (t₀ + (k + 1)) * r (t₀ + (k + 1)) =
        (ρu * ρr) • (u (t₀ + k) * r (t₀ + k)) + ρu • (u (t₀ + k) * εr (t₀ + k + 1)) +
          ρr • (r (t₀ + k) * εu (t₀ + k + 1)) + εu (t₀ + k + 1) * εr (t₀ + k + 1) := by
      rw [← add_assoc t₀ k 1, hu.2.1, hr.2.1]
      funext ω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hcross : 𝔼.E t₀ (εu (t₀ + k + 1) * εr (t₀ + k + 1)) = fun _ => c := by
      rw [← 𝔼.tower (Nat.le_add_right t₀ k), hc, 𝔼.const]
    unfold condCov at ih ⊢
    rw [hprod, map_add, map_add, map_add, map_smul, map_smul, map_smul,
      E_mul_innov 𝔼 hpo hr t₀ k (hu.1 (t₀ + k)), E_mul_innov 𝔼 hpo hu t₀ k (hr.1 (t₀ + k)),
      hcross, hEu (k + 1), hEr (k + 1)]
    have e1 : 𝔼.E t₀ (u (t₀ + k) * r (t₀ + k)) = (fun _ => c * ∑ j ∈ Finset.range k,
        (ρu * ρr) ^ j) + 𝔼.E t₀ (u (t₀ + k)) * 𝔼.E t₀ (r (t₀ + k)) := by
      rw [← ih]; abel
    rw [e1, hEu k, hEr k]
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      smul_zero, add_zero, Finset.sum_range_succ', pow_zero, pow_succ]
    rw [← Finset.sum_mul]
    ring

/-- Woodford (2003), p. 509 (tool): the conditional variance of a plan (3.6),
`var_t(ȳ + f X + g Y) = f² var_t X + 2 f g cov_t(X, Y) + g² var_t Y`. -/
theorem condCov_affine2 (t : ℕ) (a f g : ℝ) (X Y : Ω → ℝ) :
    condCov 𝔼 t ((fun _ => a) + f • X + g • Y) ((fun _ => a) + f • X + g • Y) =
      f ^ 2 • condCov 𝔼 t X X + (2 * f * g) • condCov 𝔼 t X Y + g ^ 2 • condCov 𝔼 t Y Y := by
  have hp : ((fun _ => a) + f • X + g • Y) * ((fun _ => a) + f • X + g • Y) =
      (fun _ => a ^ 2) + (2 * a * f) • X + (2 * a * g) • Y + f ^ 2 • (X * X) +
        (2 * f * g) • (X * Y) + g ^ 2 • (Y * Y) := by
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hYX : Y * X = X * Y := mul_comm Y X
  unfold condCov
  rw [hp]
  simp only [map_add, map_smul, 𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  ring

/-- Woodford (2003), p. 509 (tool): a plan (3.6) at date `t` as a sum of functions. -/
theorem plan2_eq {u r : ℕ → Ω → ℝ} (ybar f g : ℝ) (t : ℕ) :
    plan2 ybar f g u r t = (fun _ => ybar) + f • u t + g • r t := by
  funext ω; simp [plan2_apply]

/-- Woodford (2003), (3.4), p. 511 (the geometric sum): for `0 ≤ β < 1`, `0 ≤ q < 1`,
`∑_k βᵏ ∑_{j<k} qʲ = β / ((1 − β)(1 − βq))`. -/
theorem hasSum_disc_geomSum {β q : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k => β ^ k * ∑ j ∈ Finset.range k, q ^ j) (β / ((1 - β) * (1 - β * q))) := by
  have hβq0 : 0 ≤ β * q := mul_nonneg hβ0 hq0
  have hβq1 : β * q < 1 := by nlinarith
  have h1 := hasSum_geometric_of_lt_one hβ0 hβ1
  have h2 := hasSum_geometric_of_lt_one hβq0 hβq1
  have h3 := (h1.sub h2).div_const (1 - q)
  have hq : 1 - q ≠ 0 := by linarith
  have hq' : q - 1 ≠ 0 := by linarith
  convert h3 using 1
  · funext k
    rw [geom_sum_eq (by linarith : q ≠ 1), mul_pow]
    field_simp
    ring
  · have : 1 - β ≠ 0 := by linarith
    have : 1 - β * q ≠ 0 := by linarith
    field_simp
    ring

/-- Woodford (2003), p. 509 (definition of `L^stab` for the loss (1.2)): the stabilization loss
`∑_k βᵏ [var_{t₀}(π_{t₀+k}) + λ var_{t₀}(x_{t₀+k})]` in state `ω` at date `t₀`. -/
noncomputable def Lstab12 (β lam : ℝ) (t₀ : ℕ) (π x : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' k, β ^ k * (condCov 𝔼 t₀ (π (t₀ + k)) (π (t₀ + k)) ω +
    lam * condCov 𝔼 t₀ (x (t₀ + k)) (x (t₀ + k)) ω)

/-- Woodford (2003), p. 512 (definition of `L^stab` for the loss (2.24)): the stabilization loss
`∑_k βᵏ [var_{t₀}(π) + λₓ var_{t₀}(x) + λᵢ var_{t₀}(i)]` in state `ω` at date `t₀`. -/
noncomputable def Lstab (β lx li : ℝ) (t₀ : ℕ) (π x i : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∑' k, β ^ k * (condCov 𝔼 t₀ (π (t₀ + k)) (π (t₀ + k)) ω +
    lx * condCov 𝔼 t₀ (x (t₀ + k)) (x (t₀ + k)) ω + li * condCov 𝔼 t₀ (i (t₀ + k)) (i (t₀ + k)) ω)

/-- Woodford (2003), p. 511: the unconditional variance `σ_u² = s/(1 − ρ²)` of an AR(1) process
with innovation variance `s`. -/
noncomputable def uncondVar (ρ s : ℝ) : ℝ := s / (1 - ρ ^ 2)

/-- Woodford (2003), eq. (3.4), p. 511: for a plan (2.19) and an AR(1) disturbance with
innovation variance `s` (`|ρ| < 1`), the stabilization loss is
`β/(1 − β) · (1 − ρ²)/(1 − βρ²) · (f_π² + λ f_x²) σ_u²`, in every state and at every date. -/
theorem lstab12_hasSum (hpo : 𝔼.PullOut) {β lam ρ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρ : |ρ| < 1) {u ε : ℕ → Ω → ℝ} (hu : AR1Innov 𝔼 ρ s u ε) (πbar xbar fπ fx : ℝ)
    (t₀ : ℕ) (ω : Ω) :
    HasSum (fun k => β ^ k * (condCov 𝔼 t₀ (plan1 πbar fπ u (t₀ + k)) (plan1 πbar fπ u (t₀ + k)) ω
      + lam * condCov 𝔼 t₀ (plan1 xbar fx u (t₀ + k)) (plan1 xbar fx u (t₀ + k)) ω))
      (β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * (fπ ^ 2 + lam * fx ^ 2) *
        uncondVar ρ s) := by
  have hq0 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  have hq1 : ρ ^ 2 < 1 := by
    have := sq_abs ρ ▸ (pow_lt_one₀ (abs_nonneg ρ) hρ (two_ne_zero))
    exact this
  have hV := condCov_ar1 𝔼 hpo hu hu (hu.2.2.2) t₀
  have hpl : ∀ y f k, plan1 y f u (t₀ + k) = (fun _ => y) + f • u (t₀ + k) + (0 : ℝ) • u (t₀ + k)
      := by
    intro y f k; funext ω; simp [plan1]
  have hG := (hasSum_disc_geomSum hβ0 hβ1 hq0 hq1).mul_left (s * (fπ ^ 2 + lam * fx ^ 2))
  convert hG using 1
  · funext k
    rw [hpl, hpl, condCov_affine2, condCov_affine2, hV k]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← pow_two]
    ring
  · unfold uncondVar
    have : 1 - ρ ^ 2 ≠ 0 := by linarith
    have : 1 - β ≠ 0 := by linarith
    have : 1 - β * ρ ^ 2 ≠ 0 := by nlinarith
    field_simp

/-- Woodford (2003), eqs. (3.7)–(3.8), p. 513: for a plan (3.6) and independent AR(1)
disturbances (`E_t(εᵘ_{t+1} εʳ_{t+1}) = 0`) with innovation variances `s_u`, `s_r`, the
stabilization loss splits as `L^stab = L^{stab,r} + L^{stab,u}` with
`L^{stab,j} = β/(1 − β) · (1 − ρ_j²)/(1 − βρ_j²) · (π_j² + λₓ x_j² + λᵢ i_j²) σ_j²`. -/
theorem lstab_hasSum (hpo : 𝔼.PullOut) {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hρu : |ρu| < 1) (hρr : |ρr| < 1) {u εu r εr : ℕ → Ω → ℝ} (hu : AR1Innov 𝔼 ρu su u εu)
    (hr : AR1Innov 𝔼 ρr sr r εr) (hind : ∀ t, 𝔼.E t (εu (t + 1) * εr (t + 1)) = fun _ => 0)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) (t₀ : ℕ) (ω : Ω) :
    HasSum (fun k => β ^ k *
      (condCov 𝔼 t₀ (plan2 πbar fπ gπ u r (t₀ + k)) (plan2 πbar fπ gπ u r (t₀ + k)) ω +
      lx * condCov 𝔼 t₀ (plan2 xbar fx gx u r (t₀ + k)) (plan2 xbar fx gx u r (t₀ + k)) ω +
      li * condCov 𝔼 t₀ (plan2 ibar fi gi u r (t₀ + k)) (plan2 ibar fi gi u r (t₀ + k)) ω))
      (β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su) := by
  have hsq : ∀ ρ : ℝ, |ρ| < 1 → 0 ≤ ρ ^ 2 ∧ ρ ^ 2 < 1 := fun ρ h =>
    ⟨sq_nonneg ρ, sq_abs ρ ▸ (pow_lt_one₀ (abs_nonneg ρ) h (two_ne_zero))⟩
  obtain ⟨hu0, hu1⟩ := hsq ρu hρu
  obtain ⟨hr0, hr1⟩ := hsq ρr hρr
  have hVu := condCov_ar1 𝔼 hpo hu hu (hu.2.2.2) t₀
  have hVr := condCov_ar1 𝔼 hpo hr hr (hr.2.2.2) t₀
  have hC := condCov_ar1 𝔼 hpo hu hr hind t₀
  have hGu := (hasSum_disc_geomSum hβ0 hβ1 hu0 hu1).mul_left
    (su * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2))
  have hGr := (hasSum_disc_geomSum hβ0 hβ1 hr0 hr1).mul_left
    (sr * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2))
  convert hGr.add hGu using 1
  · funext k
    rw [plan2_eq, plan2_eq, plan2_eq, condCov_affine2, condCov_affine2, condCov_affine2, hVu k,
      hVr k, hC k]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← pow_two]
    ring
  · unfold uncondVar
    have : 1 - ρu ^ 2 ≠ 0 := by linarith
    have : 1 - ρr ^ 2 ≠ 0 := by linarith
    have : 1 - β ≠ 0 := by linarith
    have : 1 - β * ρu ^ 2 ≠ 0 := by nlinarith
    have : 1 - β * ρr ^ 2 ≠ 0 := by nlinarith
    field_simp


/-! ### Proposition 7.11 -/

/-- Woodford (2003), p. 510 and Prop. 7.11, p. 511 (the optimal noninertial plan for the loss (1.2)
with one AR(1) cost-push disturbance): a plan (2.19) whose (i) long-run values are those of a
policy that is optimal from a timeless perspective, and (ii) responses minimise `L^stab` — by
(3.4) equivalently `f_π² + λ f_x²` — among responses consistent with (2.1), i.e. with (3.3). -/
def IsOptimalNoninertial12 (β κ lam xstar ρ πbar xbar fπ fx : ℝ) : Prop :=
  (TimelessOpt12 β κ lam xstar πbar ∧ xbar = (1 - β) / κ * πbar) ∧
    ((1 - β * ρ) * fπ = κ * fx + 1 ∧ ∀ gπ gx, (1 - β * ρ) * gπ = κ * gx + 1 →
      fπ ^ 2 + lam * fx ^ 2 ≤ gπ ^ 2 + lam * gx ^ 2)

/-- **Proposition 7.11** (Woodford (2003), p. 511): with `0 < β < 1`, `κ, λ > 0`, the optimal
noninertial plan is the plan (2.19) with `π̄ = x̄ = 0` and the coefficients (3.5). -/
theorem prop_7_11 {β κ lam xstar ρ πbar xbar fπ fx : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) :
    IsOptimalNoninertial12 β κ lam xstar ρ πbar xbar fπ fx ↔
      (πbar = 0 ∧ xbar = 0) ∧ fπ = fpiOni β κ lam ρ ∧ fx = fxOni β κ lam ρ := by
  unfold IsOptimalNoninertial12
  rw [timelessOpt12_iff hβ0 hβ1 hκ hlam, oni_unique_min hκ hlam]
  constructor
  · rintro ⟨⟨rfl, rfl⟩, h⟩
    exact ⟨⟨rfl, by ring⟩, h⟩
  · rintro ⟨⟨rfl, rfl⟩, h⟩
    exact ⟨⟨rfl, by ring⟩, h⟩

/-- **Proposition 7.11, stochastic form** (Woodford (2003), pp. 509–511): let the cost-push
disturbance be AR(1) with innovations of conditional variance `s > 0` (`|ρ| < 1`), not
degenerate, and let `E` have the pull-out property. The plan `π = f_π^oni u`, `x = f_x^oni u`
satisfies (2.1), and for every plan (2.19) that satisfies (2.1), its stabilization loss
`L^stab` (a genuine discounted sum of conditional variances, in any state and at any date) is at
least that of the optimal noninertial plan, with equality iff it has the responses (3.5). -/
theorem prop_7_11_lstab (hpo : 𝔼.PullOut) {β κ lam ρ s : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hlam : 0 < lam) (hρ : |ρ| < 1) (hs : 0 < s) {u ε : ℕ → Ω → ℝ}
    (hu : AR1Innov 𝔼 ρ s u ε) (hnd : Nondeg1 u) (t₀ : ℕ) (ω : Ω) :
    AS 𝔼 β κ (plan1 0 (fpiOni β κ lam ρ) u) (plan1 0 (fxOni β κ lam ρ) u) u ∧
    ∀ πbar xbar gπ gx, AS 𝔼 β κ (plan1 πbar gπ u) (plan1 xbar gx u) u →
      Lstab12 𝔼 β lam t₀ (plan1 0 (fpiOni β κ lam ρ) u) (plan1 0 (fxOni β κ lam ρ) u) ω ≤
        Lstab12 𝔼 β lam t₀ (plan1 πbar gπ u) (plan1 xbar gx u) ω ∧
      (Lstab12 𝔼 β lam t₀ (plan1 πbar gπ u) (plan1 xbar gx u) ω =
        Lstab12 𝔼 β lam t₀ (plan1 0 (fpiOni β κ lam ρ) u) (plan1 0 (fxOni β κ lam ρ) u) ω ↔
        gπ = fpiOni β κ lam ρ ∧ gx = fxOni β κ lam ρ) := by
  have hq1 : ρ ^ 2 < 1 := sq_abs ρ ▸ (pow_lt_one₀ (abs_nonneg ρ) hρ (two_ne_zero))
  have hK : 0 < β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s := by
    have : 0 < 1 - β := by linarith
    have : 0 < 1 - ρ ^ 2 := by linarith
    have : 0 < 1 - β * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
    unfold uncondVar
    positivity
  set K := β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s
  have hL : ∀ πbar xbar fπ fx, Lstab12 𝔼 β lam t₀ (plan1 πbar fπ u) (plan1 xbar fx u) ω =
      K * (fπ ^ 2 + lam * fx ^ 2) := by
    intro πbar xbar fπ fx
    unfold Lstab12
    rw [(lstab12_hasSum 𝔼 hpo hβ0.le hβ1 hρ hu πbar xbar fπ fx t₀ ω).tsum_eq]
    ring
  refine ⟨plan_AS_of 𝔼 hu.isAR1 (by ring) (oni_constraint hκ hlam), ?_⟩
  intro πbar xbar gπ gx hAS
  have hg := ((plan_AS_iff 𝔼 hu.isAR1 hnd πbar xbar gπ gx).mp hAS).2
  have e := oni_objective_eq hκ hlam hg
  rw [hL, hL]
  have hd : 0 ≤ (gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2 := by positivity
  refine ⟨by rw [e]; nlinarith, ⟨fun heq => ?_, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩⟩
  rw [e] at heq
  have hz : (gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2 = 0 := by
    have : K * ((gπ - fpiOni β κ lam ρ) ^ 2 + lam * (gx - fxOni β κ lam ρ) ^ 2) = 0 := by
      linarith
    exact (mul_eq_zero.mp this).resolve_left hK.ne'
  have a2 : 0 ≤ lam * (gx - fxOni β κ lam ρ) ^ 2 := by positivity
  have e1 : (gπ - fpiOni β κ lam ρ) ^ 2 = 0 := by nlinarith [sq_nonneg (gπ - fpiOni β κ lam ρ)]
  have e2 : (gx - fxOni β κ lam ρ) ^ 2 = 0 := by
    have : lam * (gx - fxOni β κ lam ρ) ^ 2 = 0 := by nlinarith [sq_nonneg (gπ - fpiOni β κ lam ρ)]
    exact (mul_eq_zero.mp this).resolve_left hlam.ne'
  exact ⟨by linarith [pow_eq_zero_iff two_ne_zero |>.mp e1],
    by linarith [pow_eq_zero_iff two_ne_zero |>.mp e2]⟩

/-! ### Appendix F.4: the optimal noninertial plan with two disturbances -/

/-- Woodford (2003), App. F.4, p. 713: `γ_j = (1 − ρ_j)(1 − βρ_j)`. -/
noncomputable def gamF4 (β ρ : ℝ) : ℝ := (1 - ρ) * (1 - β * ρ)

/-- Woodford (2003), App. F.4, p. 714: `ξ_j = λₓ (1 − βρ_j)`. -/
noncomputable def xiF4 (β lx ρ : ℝ) : ℝ := lx * (1 - β * ρ)

/-- Woodford (2003), App. F.4, p. 714:
`h_j = λᵢ σ⁻² (γ_j − ρ_j κσ)² + λₓ (1 − βρ_j)² + κ²`. -/
noncomputable def hF4 (β κ σ lx li ρ : ℝ) : ℝ :=
  li * σ⁻¹ ^ 2 * (gamF4 β ρ - ρ * κ * σ) ^ 2 + lx * (1 - β * ρ) ^ 2 + κ ^ 2

/-- Woodford (2003), App. F.4, p. 713: `π_r = λᵢ σ⁻¹ (γ_r − ρ_r κσ) κ / h_r`. -/
noncomputable def piRF4 (β κ σ lx li ρ : ℝ) : ℝ :=
  li * σ⁻¹ * (gamF4 β ρ - ρ * κ * σ) * κ / hF4 β κ σ lx li ρ

/-- Woodford (2003), App. F.4, p. 713: `x_r = λᵢ σ⁻¹ (γ_r − ρ_r κσ)(1 − βρ_r) / h_r`. -/
noncomputable def xRF4 (β κ σ lx li ρ : ℝ) : ℝ :=
  li * σ⁻¹ * (gamF4 β ρ - ρ * κ * σ) * (1 - β * ρ) / hF4 β κ σ lx li ρ

/-- Woodford (2003), App. F.4, p. 713: `i_r = (ξ_r (1 − βρ_r) + κ²) / h_r`. -/
noncomputable def iRF4 (β κ σ lx li ρ : ℝ) : ℝ :=
  (xiF4 β lx ρ * (1 - β * ρ) + κ ^ 2) / hF4 β κ σ lx li ρ

/-- Woodford (2003), App. F.4, p. 713: `π_u = (λᵢ σ⁻² (γ_u − ρ_u κσ)(1 − ρ_u) + ξ_u) / h_u`. -/
noncomputable def piUF4 (β κ σ lx li ρ : ℝ) : ℝ :=
  (li * σ⁻¹ ^ 2 * (gamF4 β ρ - ρ * κ * σ) * (1 - ρ) + xiF4 β lx ρ) / hF4 β κ σ lx li ρ

/-- Woodford (2003), App. F.4, p. 713: `x_u = (ρ_u λᵢ σ⁻¹ (γ_u − ρ_u κσ) − κ) / h_u`. -/
noncomputable def xUF4 (β κ σ lx li ρ : ℝ) : ℝ :=
  (ρ * li * σ⁻¹ * (gamF4 β ρ - ρ * κ * σ) - κ) / hF4 β κ σ lx li ρ

/-- Woodford (2003), App. F.4, p. 713: `i_u = (σ⁻¹ κ (1 − ρ_u) + ξ_u ρ_u) / h_u`. -/
noncomputable def iUF4 (β κ σ lx li ρ : ℝ) : ℝ :=
  (σ⁻¹ * κ * (1 - ρ) + xiF4 β lx ρ * ρ) / hF4 β κ σ lx li ρ

/-- Woodford (2003), App. F.4, p. 714: `h_j > 0` (needs only `κ ≠ 0`, `λₓ, λᵢ ≥ 0`). -/
theorem hF4_pos {β κ σ lx li ρ : ℝ} (hκ : κ ≠ 0) (hlx : 0 ≤ lx) (hli : 0 ≤ li) :
    0 < hF4 β κ σ lx li ρ := by
  unfold hF4
  have : 0 < κ ^ 2 := by positivity
  have : 0 ≤ li * σ⁻¹ ^ 2 * (gamF4 β ρ - ρ * κ * σ) ^ 2 := by positivity
  have : 0 ≤ lx * (1 - β * ρ) ^ 2 := by positivity
  linarith

/-- Woodford (2003), App. F.4, pp. 713–714: `γ_j > 0` and `ξ_j > 0` for `0 ≤ ρ_j < 1`,
`0 < β < 1`, `λₓ > 0` (the bounds hold for every `ρ < 1`). -/
theorem gamF4_xiF4_pos {β lx ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1)
    (hlx : 0 < lx) : 0 < gamF4 β ρ ∧ 0 < xiF4 β lx ρ := by
  have : 0 < 1 - β * ρ := by nlinarith
  exact ⟨mul_pos (by linarith) this, mul_pos hlx this⟩

/-- Woodford (2003), App. F.4, p. 713: `i_r > 0` and `i_u > 0` (for `0 ≤ ρ < 1`, `κ, σ, λₓ > 0`,
`λᵢ ≥ 0`). -/
theorem iRF4_iUF4_pos {β κ σ lx li ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < iRF4 β κ σ lx li ρ ∧ 0 < iUF4 β κ σ lx li ρ := by
  have hh := hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx.le hli
  obtain ⟨-, hξ⟩ := gamF4_xiF4_pos hβ0 hβ1 hρ1 hlx
  have ha : 0 < 1 - β * ρ := by nlinarith
  have h1 : 0 < 1 - ρ := by linarith
  unfold iRF4 iUF4
  constructor <;> positivity

/-- Woodford (2003), App. F.4 (the two restrictions on the responses to `u`, from (2.1) and
(2.23)): `(1 − βρ) f_π = κ f_x + 1` and `(1 − ρ) f_x = −σ (f_i − ρ f_π)`. -/
def ConsU (β κ σ ρ fπ fx fi : ℝ) : Prop :=
  (1 - β * ρ) * fπ = κ * fx + 1 ∧ (1 - ρ) * fx = -σ * (fi - ρ * fπ)

/-- Woodford (2003), App. F.4 (the two restrictions on the responses to `r̂ⁿ`):
`(1 − βρ) g_π = κ g_x` and `(1 − ρ) g_x = −σ (g_i − ρ g_π − 1)`. -/
def ConsR (β κ σ ρ gπ gx gi : ℝ) : Prop :=
  (1 - β * ρ) * gπ = κ * gx ∧ (1 - ρ) * gx = -σ * (gi - ρ * gπ - 1)

/-- Woodford (2003), eq. (3.8), p. 513 (the objective of `L^{stab,j}`):
`f_π² + λₓ f_x² + λᵢ f_i²`. -/
def objF4 (lx li fπ fx fi : ℝ) : ℝ := fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2

/-- Woodford (2003), App. F.4 (tool): the feasible directions of either response problem are the
multiples of `v = (κ, 1 − βρ, −(γ − ρκσ)/σ)`: a direction satisfying the two homogeneous
restrictions has `d_π = κ s`, `d_x = (1 − βρ) s`, `d_i = −s (γ − ρκσ)/σ` with
`s = d_x/(1 − βρ)`. -/
theorem null_dir {β κ σ ρ : ℝ} (hσ : σ ≠ 0) (ha : 1 - β * ρ ≠ 0) {dπ dx di : ℝ}
    (h1 : (1 - β * ρ) * dπ = κ * dx) (h2 : (1 - ρ) * dx = -σ * (di - ρ * dπ)) :
    dπ = κ * (dx / (1 - β * ρ)) ∧ dx = (1 - β * ρ) * (dx / (1 - β * ρ)) ∧
      di = -(dx / (1 - β * ρ)) * (gamF4 β ρ - ρ * κ * σ) / σ := by
  refine ⟨by field_simp; linarith, by field_simp, ?_⟩
  have key : di * ((1 - β * ρ) * σ) = -dx * ((1 - ρ) * (1 - β * ρ) - ρ * κ * σ) := by
    linear_combination (1 - β * ρ) * h2 + σ * ρ * h1
  rw [eq_div_iff hσ, show -(dx / (1 - β * ρ)) * (gamF4 β ρ - ρ * κ * σ) =
    -dx * (gamF4 β ρ - ρ * κ * σ) / (1 - β * ρ) by ring, eq_div_iff ha]
  unfold gamF4
  linear_combination key

/-- Woodford (2003), App. F.4, p. 713 (the responses to `u` are feasible): `(π_u, x_u, i_u)`
satisfies the two restrictions implied by (2.1) and (2.23). -/
theorem f4_u_feasible {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx)
    (hli : 0 ≤ li) :
    ConsU β κ σ ρ (piUF4 β κ σ lx li ρ) (xUF4 β κ σ lx li ρ) (iUF4 β κ σ lx li ρ) := by
  have hh := hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx hli
  unfold ConsU piUF4 xUF4 iUF4
  have hσ' := hσ.ne'
  have hh' := hh.ne'
  constructor
  · field_simp
    unfold hF4 xiF4 gamF4
    field_simp
    ring
  · field_simp
    unfold xiF4 gamF4
    ring

/-- Woodford (2003), App. F.4, p. 713 (the responses to `r̂ⁿ` are feasible): `(π_r, x_r, i_r)`
satisfies the two restrictions implied by (2.1) and (2.23). -/
theorem f4_r_feasible {β κ σ lx li ρ : ℝ} (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 ≤ lx)
    (hli : 0 ≤ li) :
    ConsR β κ σ ρ (piRF4 β κ σ lx li ρ) (xRF4 β κ σ lx li ρ) (iRF4 β κ σ lx li ρ) := by
  have hh := hF4_pos (β := β) (σ := σ) (ρ := ρ) hκ.ne' hlx hli
  unfold ConsR piRF4 xRF4 iRF4
  have hσ' := hσ.ne'
  have hh' := hh.ne'
  constructor
  · field_simp
  · field_simp
    unfold hF4 xiF4 gamF4
    field_simp
    ring

/-- Woodford (2003), App. F.4 (orthogonality, `u` block): the F.4 point is `W`-orthogonal to the
feasible direction `v = (κ, 1 − βρ, −(γ − ρκσ)/σ)`, `W = diag(1, λₓ, λᵢ)`. -/
theorem f4_u_orth (β κ σ lx li ρ : ℝ) :
    κ * piUF4 β κ σ lx li ρ + lx * (1 - β * ρ) * xUF4 β κ σ lx li ρ -
      li * ((gamF4 β ρ - ρ * κ * σ) / σ) * iUF4 β κ σ lx li ρ = 0 := by
  unfold piUF4 xUF4 iUF4 xiF4
  simp only [div_eq_mul_inv]
  ring

/-- Woodford (2003), App. F.4 (orthogonality, `r̂ⁿ` block). -/
theorem f4_r_orth (β κ σ lx li ρ : ℝ) :
    κ * piRF4 β κ σ lx li ρ + lx * (1 - β * ρ) * xRF4 β κ σ lx li ρ -
      li * ((gamF4 β ρ - ρ * κ * σ) / σ) * iRF4 β κ σ lx li ρ = 0 := by
  unfold piRF4 xRF4 iRF4 xiF4
  simp only [div_eq_mul_inv]
  ring

/-- Woodford (2003), App. F.4 (tool): if `p` is `W`-orthogonal to `v` and `d` satisfies the
homogeneous restrictions, then `objF4 (p + d) = objF4 p + objF4 d`. -/
theorem objF4_add_of_orth {β κ σ lx li ρ : ℝ} (hσ : σ ≠ 0) (ha : 1 - β * ρ ≠ 0)
    {pπ px pi fπ fx fi : ℝ}
    (horth : κ * pπ + lx * (1 - β * ρ) * px - li * ((gamF4 β ρ - ρ * κ * σ) / σ) * pi = 0)
    (h1 : (1 - β * ρ) * (fπ - pπ) = κ * (fx - px))
    (h2 : (1 - ρ) * (fx - px) = -σ * ((fi - pi) - ρ * (fπ - pπ))) :
    objF4 lx li fπ fx fi = objF4 lx li pπ px pi + objF4 lx li (fπ - pπ) (fx - px) (fi - pi) := by
  obtain ⟨e1, e2, e3⟩ := null_dir hσ ha h1 h2
  set s := (fx - px) / (1 - β * ρ)
  unfold objF4
  linear_combination 2 * pπ * e1 + 2 * lx * px * e2 + 2 * li * pi * e3 + 2 * s * horth

/-- Woodford (2003), App. F.4 (tool): a direction with zero weighted norm that satisfies the
homogeneous restrictions is zero (`λₓ > 0`, `λᵢ ≥ 0`, `σ ≠ 0`). -/
theorem dir_eq_zero {σ lx li ρ : ℝ} (hσ : σ ≠ 0) (hlx : 0 < lx) (hli : 0 ≤ li)
    {dπ dx di : ℝ} (h2 : (1 - ρ) * dx = -σ * (di - ρ * dπ)) (h0 : objF4 lx li dπ dx di = 0) :
    dπ = 0 ∧ dx = 0 ∧ di = 0 := by
  unfold objF4 at h0
  have a1 := sq_nonneg dπ
  have a2 : 0 ≤ lx * dx ^ 2 := by positivity
  have a3 : 0 ≤ li * di ^ 2 := by positivity
  have hp : dπ ^ 2 = 0 := by linarith
  have hx : dx ^ 2 = 0 := by
    have : lx * dx ^ 2 = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hlx.ne'
  have hp0 := pow_eq_zero_iff two_ne_zero |>.mp hp
  have hx0 := pow_eq_zero_iff two_ne_zero |>.mp hx
  rw [hp0, hx0] at h2
  have : σ * di = 0 := by linarith
  exact ⟨hp0, hx0, (mul_eq_zero.mp this).resolve_left hσ⟩

/-- Woodford (2003), App. F.4 (the `u` block, confirmed): among responses `(f_π, f_x, f_i)` to the
cost-push disturbance consistent with (2.1) and (2.23), `f_π² + λₓ f_x² + λᵢ f_i²` — hence
`L^{stab,u}` by (3.8) — has the unique minimiser `(π_u, x_u, i_u)` of Appendix F.4. -/
theorem f4_u_optimal {β κ σ lx li ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (fπ fx fi : ℝ) :
    (ConsU β κ σ ρ fπ fx fi ∧ ∀ gπ gx gi, ConsU β κ σ ρ gπ gx gi →
      objF4 lx li fπ fx fi ≤ objF4 lx li gπ gx gi) ↔
      fπ = piUF4 β κ σ lx li ρ ∧ fx = xUF4 β κ σ lx li ρ ∧ fi = iUF4 β κ σ lx li ρ := by
  have ha : 1 - β * ρ ≠ 0 := by
    have : 0 < 1 - β * ρ := by nlinarith
    exact this.ne'
  obtain ⟨c1, c2⟩ := f4_u_feasible (β := β) (ρ := ρ) hκ hσ hlx.le hli
  have hsplit : ∀ gπ gx gi, ConsU β κ σ ρ gπ gx gi → objF4 lx li gπ gx gi =
      objF4 lx li (piUF4 β κ σ lx li ρ) (xUF4 β κ σ lx li ρ) (iUF4 β κ σ lx li ρ) +
      objF4 lx li (gπ - piUF4 β κ σ lx li ρ) (gx - xUF4 β κ σ lx li ρ)
        (gi - iUF4 β κ σ lx li ρ) := by
    rintro gπ gx gi ⟨g1, g2⟩
    exact objF4_add_of_orth hσ.ne' ha (f4_u_orth β κ σ lx li ρ)
      (by linear_combination g1 - c1) (by linear_combination g2 - c2)
  have hnn : ∀ a b c, 0 ≤ objF4 lx li a b c := fun a b c => by unfold objF4; positivity
  constructor
  · rintro ⟨hf, hmin⟩
    have h1 := hmin _ _ _ ⟨c1, c2⟩
    rw [hsplit _ _ _ hf] at h1
    have h0 : objF4 lx li (fπ - piUF4 β κ σ lx li ρ) (fx - xUF4 β κ σ lx li ρ)
        (fi - iUF4 β κ σ lx li ρ) = 0 := le_antisymm (by linarith) (hnn _ _ _)
    obtain ⟨g1, g2⟩ := hf
    have h2' : (1 - ρ) * (fx - xUF4 β κ σ lx li ρ) =
        -σ * ((fi - iUF4 β κ σ lx li ρ) - ρ * (fπ - piUF4 β κ σ lx li ρ)) := by
      linear_combination g2 - c2
    obtain ⟨d1, d2, d3⟩ := dir_eq_zero hσ.ne' hlx hli h2' h0
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨⟨c1, c2⟩, fun gπ gx gi hg => ?_⟩
    rw [hsplit _ _ _ hg]
    linarith [hnn (gπ - piUF4 β κ σ lx li ρ) (gx - xUF4 β κ σ lx li ρ) (gi - iUF4 β κ σ lx li ρ)]

/-- Woodford (2003), App. F.4 (the `r̂ⁿ` block, confirmed): among responses `(g_π, g_x, g_i)` to
the natural-rate disturbance consistent with (2.1) and (2.23), `g_π² + λₓ g_x² + λᵢ g_i²` — hence
`L^{stab,r}` by (3.7) — has the unique minimiser `(π_r, x_r, i_r)` of Appendix F.4. -/
theorem f4_r_optimal {β κ σ lx li ρ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hρ1 : ρ < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (gπ gx gi : ℝ) :
    (ConsR β κ σ ρ gπ gx gi ∧ ∀ hπ hx hi, ConsR β κ σ ρ hπ hx hi →
      objF4 lx li gπ gx gi ≤ objF4 lx li hπ hx hi) ↔
      gπ = piRF4 β κ σ lx li ρ ∧ gx = xRF4 β κ σ lx li ρ ∧ gi = iRF4 β κ σ lx li ρ := by
  have ha : 1 - β * ρ ≠ 0 := by
    have : 0 < 1 - β * ρ := by nlinarith
    exact this.ne'
  obtain ⟨c1, c2⟩ := f4_r_feasible (β := β) (ρ := ρ) hκ hσ hlx.le hli
  have hsplit : ∀ hπ hx hi, ConsR β κ σ ρ hπ hx hi → objF4 lx li hπ hx hi =
      objF4 lx li (piRF4 β κ σ lx li ρ) (xRF4 β κ σ lx li ρ) (iRF4 β κ σ lx li ρ) +
      objF4 lx li (hπ - piRF4 β κ σ lx li ρ) (hx - xRF4 β κ σ lx li ρ)
        (hi - iRF4 β κ σ lx li ρ) := by
    rintro hπ hx hi ⟨g1, g2⟩
    exact objF4_add_of_orth hσ.ne' ha (f4_r_orth β κ σ lx li ρ)
      (by linear_combination g1 - c1) (by linear_combination g2 - c2)
  have hnn : ∀ a b c, 0 ≤ objF4 lx li a b c := fun a b c => by unfold objF4; positivity
  constructor
  · rintro ⟨hf, hmin⟩
    have h1 := hmin _ _ _ ⟨c1, c2⟩
    rw [hsplit _ _ _ hf] at h1
    have h0 : objF4 lx li (gπ - piRF4 β κ σ lx li ρ) (gx - xRF4 β κ σ lx li ρ)
        (gi - iRF4 β κ σ lx li ρ) = 0 := le_antisymm (by linarith) (hnn _ _ _)
    obtain ⟨g1, g2⟩ := hf
    have h2' : (1 - ρ) * (gx - xRF4 β κ σ lx li ρ) =
        -σ * ((gi - iRF4 β κ σ lx li ρ) - ρ * (gπ - piRF4 β κ σ lx li ρ)) := by
      linear_combination g2 - c2
    obtain ⟨d1, d2, d3⟩ := dir_eq_zero hσ.ne' hlx hli h2' h0
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨⟨c1, c2⟩, fun hπ hx hi hg => ?_⟩
    rw [hsplit _ _ _ hg]
    linarith [hnn (hπ - piRF4 β κ σ lx li ρ) (hx - xRF4 β κ σ lx li ρ) (hi - iRF4 β κ σ lx li ρ)]

/-! ### Survey E11: the long-run values printed in Appendix F.4 -/

/-- Woodford (2003), App. F.4, p. 713 (as printed): the long-run inflation rate
`π̄ = ((1 − β)κ⁻¹λₓ x* + λᵢ(i* − r̄)) / (1 + (1 − β)²κ⁻²λₓ + λᵢ)` (with `x̄ = (1 − β)π̄/κ`,
`ī = π̄ + r̄`). -/
noncomputable def piBarF4 (β κ lx li xstar istar rbar : ℝ) : ℝ :=
  ((1 - β) * κ⁻¹ * lx * xstar + li * (istar - rbar)) / (1 + (1 - β) ^ 2 * κ⁻¹ ^ 2 * lx + li)

/-- Woodford (2003), (2.24), p. 503 at a steady state (the "L^det" criterion that §3 rejects,
p. 509): the period loss `π² + λₓ(x − x*)² + λᵢ(i − i*)²` along the steady state with inflation
`π`, `x = (1 − β)π/κ`, `i = r̄ + π`. -/
noncomputable def steadyLoss (β κ lx li xstar istar rbar p : ℝ) : ℝ :=
  p ^ 2 + lx * ((1 - β) / κ * p - xstar) ^ 2 + li * (rbar + p - istar) ^ 2

/-- Survey E11 (Woodford (2003), App. F.4, p. 713, confirmed): the printed long-run value `π̄` of
F.4 is the unique minimiser of the steady-state period loss, by completing the square:
`steadyLoss p = steadyLoss π̄_F4 + (1 + (1 − β)²λₓ/κ² + λᵢ)(p − π̄_F4)²`. -/
theorem f4_zbar_minimises_steady_loss {β κ lx li xstar istar rbar : ℝ} (hκ : κ ≠ 0)
    (hlx : 0 ≤ lx) (hli : 0 ≤ li) (q : ℝ) :
    (∀ p, steadyLoss β κ lx li xstar istar rbar q ≤ steadyLoss β κ lx li xstar istar rbar p) ↔
      q = piBarF4 β κ lx li xstar istar rbar := by
  set D := 1 + (1 - β) ^ 2 * κ⁻¹ ^ 2 * lx + li with hD
  have hDpos : 0 < D := by
    have : 0 ≤ (1 - β) ^ 2 * κ⁻¹ ^ 2 * lx := by positivity
    linarith
  have hP : piBarF4 β κ lx li xstar istar rbar * D =
      (1 - β) * κ⁻¹ * lx * xstar + li * (istar - rbar) := by
    unfold piBarF4; exact div_mul_cancel₀ _ hDpos.ne'
  have key : ∀ p, steadyLoss β κ lx li xstar istar rbar p =
      steadyLoss β κ lx li xstar istar rbar (piBarF4 β κ lx li xstar istar rbar) +
        D * (p - piBarF4 β κ lx li xstar istar rbar) ^ 2 := by
    intro p
    unfold steadyLoss
    rw [hD] at hP ⊢
    simp only [div_eq_mul_inv]
    linear_combination 2 * (p - piBarF4 β κ lx li xstar istar rbar) * hP
  constructor
  · intro h
    have h1 := h (piBarF4 β κ lx li xstar istar rbar)
    rw [key q] at h1
    have : D * (q - piBarF4 β κ lx li xstar istar rbar) ^ 2 = 0 :=
      le_antisymm (by linarith) (by positivity)
    have := (mul_eq_zero.mp this).resolve_left hDpos.ne'
    linarith [pow_eq_zero_iff two_ne_zero |>.mp this]
  · rintro rfl p
    rw [key p]
    have : 0 ≤ D * (p - piBarF4 β κ lx li xstar istar rbar) ^ 2 := by positivity
    linarith

/-- Survey E11 (confirmed), the interest-rate channel: with `x* = 0`, `λᵢ > 0` and `i* ≠ r̄`, the
F.4 long-run inflation rate differs from the timelessly optimal (1.19) = (3.11). -/
theorem f4_zbar_ne_timeless {β κ lx li istar rbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : κ ≠ 0) (hlx : 0 ≤ lx) (hli : 0 < li) (hi : istar ≠ rbar) :
    piBarF4 β κ lx li 0 istar rbar ≠ piBar119 β li rbar istar := by
  intro h
  unfold piBarF4 piBar119 at h
  simp only [mul_zero, zero_add] at h
  have h0 : 0 ≤ (1 - β) ^ 2 * κ⁻¹ ^ 2 * lx := by positivity
  have hD : 0 < 1 + (1 - β) ^ 2 * κ⁻¹ ^ 2 * lx + li := by linarith
  have hlb : 0 < li + β := by linarith
  have hN : li * (istar - rbar) ≠ 0 := mul_ne_zero hli.ne' (sub_ne_zero.mpr hi)
  rw [div_eq_div_iff hD.ne' hlb.ne'] at h
  have := mul_left_cancel₀ hN h
  linarith

/-- Survey E11 (confirmed), the output-gap channel: with `λᵢ = 0` the timelessly optimal
long-run inflation (1.19) is `0` for every `x*`, while the F.4 value is nonzero whenever
`x* ≠ 0` (`λₓ > 0`, `β < 1`). -/
theorem f4_zbar_ne_timeless_xstar {β κ lx xstar istar rbar : ℝ} (hβ1 : β < 1) (hκ : κ ≠ 0)
    (hlx : 0 < lx) (hx : xstar ≠ 0) :
    piBarF4 β κ lx 0 xstar istar rbar ≠ piBar119 β 0 rbar istar := by
  unfold piBarF4 piBar119
  simp only [zero_mul, zero_div, add_zero]
  have hD : 0 < 1 + (1 - β) ^ 2 * κ⁻¹ ^ 2 * lx := by
    have : 0 ≤ (1 - β) ^ 2 * κ⁻¹ ^ 2 * lx := by positivity
    linarith
  refine div_ne_zero ?_ hD.ne'
  have : (1 - β) ≠ 0 := by linarith
  have : κ⁻¹ ≠ 0 := inv_ne_zero hκ
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero ‹1 - β ≠ 0› this) hlx.ne') hx

/-- Survey E11 (confirmed): whenever the F.4 long-run inflation rate differs from (1.19), the
constant plan at the F.4 values is not optimal from a timeless perspective, so it is not the
long-run part of the optimal noninertial plan (p. 510 (i), p. 513 (i)). -/
theorem f4_zbar_not_timeless {β κ σ rbar lx li xstar istar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li)
    (hne : piBarF4 β κ lx li xstar istar rbar ≠ piBar119 β li rbar istar) :
    ¬ TimelessOpt114 β κ σ rbar lx li xstar istar (piBarF4 β κ lx li xstar istar rbar) := by
  rw [timelessOpt114_iff hβ0 hβ1 hκ hσ hlx hli]
  exact hne

/-! ### The optimal noninertial plan with two disturbances (corrected F.4) -/

/-- Woodford (2003), p. 513 (definition of the optimal noninertial plan for the loss (2.24)): a
plan (3.6) whose (i) long-run values are those of a timelessly optimal policy (Prop. 7.3), and
whose responses (ii) to `u` minimise `L^{stab,u}` and (iii) to `r̂ⁿ` minimise `L^{stab,r}`, each
subject to the two restrictions implied by (2.1) and (2.23) (by (3.7)–(3.8) equivalently the
weighted sums of squares `objF4`). -/
def IsOptimalNoninertial2 (β κ σ rbar lx li xstar istar ρu ρr : ℝ)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) : Prop :=
  (TimelessOpt114 β κ σ rbar lx li xstar istar πbar ∧ xbar = (1 - β) / κ * πbar ∧
      ibar = rbar + πbar) ∧
    (ConsU β κ σ ρu fπ fx fi ∧ ∀ a b c, ConsU β κ σ ρu a b c →
      objF4 lx li fπ fx fi ≤ objF4 lx li a b c) ∧
    (ConsR β κ σ ρr gπ gx gi ∧ ∀ a b c, ConsR β κ σ ρr a b c →
      objF4 lx li gπ gx gi ≤ objF4 lx li a b c)

/-- **Appendix F.4, corrected** (Woodford (2003), pp. 713–714; survey E11): the optimal
noninertial plan has the F.4 response coefficients, but the long-run values (3.11) =
(1.19): `π̄ = λᵢ(i* − r̄)/(λᵢ + β)`, `x̄ = (1 − β)π̄/κ`, `ī = r̄ + π̄` — not the printed F.4 values
(`f4_zbar_ne_timeless`, `f4_zbar_ne_timeless_xstar`). -/
theorem f4_corrected {β κ σ rbar lx li xstar istar ρu ρr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : ρu < 1) (hρr : ρr < 1)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) :
    IsOptimalNoninertial2 β κ σ rbar lx li xstar istar ρu ρr πbar xbar ibar fπ fx fi gπ gx gi ↔
      (πbar = piBar119 β li rbar istar ∧ xbar = (1 - β) / κ * piBar119 β li rbar istar ∧
        ibar = rbar + piBar119 β li rbar istar) ∧
      (fπ = piUF4 β κ σ lx li ρu ∧ fx = xUF4 β κ σ lx li ρu ∧ fi = iUF4 β κ σ lx li ρu) ∧
      (gπ = piRF4 β κ σ lx li ρr ∧ gx = xRF4 β κ σ lx li ρr ∧ gi = iRF4 β κ σ lx li ρr) := by
  unfold IsOptimalNoninertial2
  rw [timelessOpt114_iff hβ0 hβ1 hκ hσ hlx hli,
    f4_u_optimal hβ0 hβ1 hρu hκ hσ hlx hli, f4_r_optimal hβ0 hβ1 hρr hκ hσ hlx hli]
  constructor
  · rintro ⟨⟨rfl, h2, h3⟩, hf, hg⟩
    exact ⟨⟨rfl, h2, h3⟩, hf, hg⟩
  · rintro ⟨⟨rfl, h2, h3⟩, hf, hg⟩
    exact ⟨⟨rfl, h2, h3⟩, hf, hg⟩

/-- Woodford (2003), pp. 512–513 and App. F.4, stochastic form: with independent AR(1)
disturbances `u`, `r̂ⁿ` (innovation variances `s_u, s_r > 0`, `|ρ_j| < 1`, non-degenerate as a
pair) and the pull-out property, the corrected optimal noninertial plan satisfies (2.1) and
(2.23), and every plan (3.6) satisfying (2.1) and (2.23) has a stabilization loss `L^stab` at least
as large, with equality iff it has the F.4 response coefficients. -/
theorem f4_lstab (hpo : 𝔼.PullOut) {β κ σ rbar lx li istar ρu ρr su sr : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1)
    (hρr : |ρr| < 1) (hsu : 0 < su) (hsr : 0 < sr) {u εu r εr : ℕ → Ω → ℝ}
    (hu : AR1Innov 𝔼 ρu su u εu) (hr : AR1Innov 𝔼 ρr sr r εr)
    (hind : ∀ t, 𝔼.E t (εu (t + 1) * εr (t + 1)) = fun _ => 0) (hnd : Nondeg2 u r) (t₀ : ℕ)
    (ω : Ω) {xs is : ℝ} (hxs : xs = (1 - β) / κ * piBar119 β li rbar istar)
    (his : is = rbar + piBar119 β li rbar istar) :
    (AS 𝔼 β κ (plan2 (piBar119 β li rbar istar) (piUF4 β κ σ lx li ρu) (piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (xUF4 β κ σ lx li ρu) (xRF4 β κ σ lx li ρr) u r) u ∧
      IS 𝔼 σ (plan2 (piBar119 β li rbar istar) (piUF4 β κ σ lx li ρu) (piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (xUF4 β κ σ lx li ρu) (xRF4 β κ σ lx li ρr) u r)
        (plan2 is (iUF4 β κ σ lx li ρu) (iRF4 β κ σ lx li ρr) u r)
        (fun t ω => rbar + r t ω)) ∧
    ∀ πbar xbar ibar fπ fx fi gπ gx gi,
      AS 𝔼 β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u →
      IS 𝔼 σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
        (fun t ω => rbar + r t ω) →
      Lstab 𝔼 β lx li t₀
          (plan2 (piBar119 β li rbar istar) (piUF4 β κ σ lx li ρu) (piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (xUF4 β κ σ lx li ρu) (xRF4 β κ σ lx li ρr) u r)
          (plan2 is (iUF4 β κ σ lx li ρu) (iRF4 β κ σ lx li ρr) u r) ω ≤
        Lstab 𝔼 β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
          (plan2 ibar fi gi u r) ω ∧
      (Lstab 𝔼 β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
          (plan2 ibar fi gi u r) ω =
        Lstab 𝔼 β lx li t₀
          (plan2 (piBar119 β li rbar istar) (piUF4 β κ σ lx li ρu) (piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (xUF4 β κ σ lx li ρu) (xRF4 β κ σ lx li ρr) u r)
          (plan2 is (iUF4 β κ σ lx li ρu) (iRF4 β κ σ lx li ρr) u r) ω ↔
        (fπ = piUF4 β κ σ lx li ρu ∧ fx = xUF4 β κ σ lx li ρu ∧ fi = iUF4 β κ σ lx li ρu) ∧
        (gπ = piRF4 β κ σ lx li ρr ∧ gx = xRF4 β κ σ lx li ρr ∧ gi = iRF4 β κ σ lx li ρr)) := by
  have hρu1 : ρu < 1 := (abs_lt.mp hρu).2
  have hρr1 : ρr < 1 := (abs_lt.mp hρr).2
  have hK : ∀ ρ s : ℝ, |ρ| < 1 → 0 < s →
      0 < β / (1 - β) * ((1 - ρ ^ 2) / (1 - β * ρ ^ 2)) * uncondVar ρ s := by
    intro ρ s hρ hs
    have hq1 : ρ ^ 2 < 1 := sq_abs ρ ▸ (pow_lt_one₀ (abs_nonneg ρ) hρ (two_ne_zero))
    have : 0 < 1 - β := by linarith
    have : 0 < 1 - ρ ^ 2 := by linarith
    have : 0 < 1 - β * ρ ^ 2 := by nlinarith [sq_nonneg ρ]
    unfold uncondVar
    positivity
  have hKu := hK ρu su hρu hsu
  have hKr := hK ρr sr hρr hsr
  set Ku := β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * uncondVar ρu su
  set Kr := β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * uncondVar ρr sr
  have hL : ∀ πbar xbar ibar fπ fx fi gπ gx gi, Lstab 𝔼 β lx li t₀ (plan2 πbar fπ gπ u r)
      (plan2 xbar fx gx u r) (plan2 ibar fi gi u r) ω =
      Kr * objF4 lx li gπ gx gi + Ku * objF4 lx li fπ fx fi := by
    intro πbar xbar ibar fπ fx fi gπ gx gi
    unfold Lstab objF4
    rw [(lstab_hasSum 𝔼 hpo hβ0.le hβ1 hρu hρr hu hr hind πbar xbar ibar fπ fx fi gπ gx gi t₀
      ω).tsum_eq]
    ring
  obtain ⟨cu1, cu2⟩ := f4_u_feasible (β := β) (ρ := ρu) hκ hσ hlx.le hli
  obtain ⟨cr1, cr2⟩ := f4_r_feasible (β := β) (ρ := ρr) hκ hσ hlx.le hli
  have hx2 : (1 - β) * piBar119 β li rbar istar = κ * xs := by rw [hxs]; field_simp
  have hiff := plan2_iff 𝔼 hσ.ne' hu.isAR1 hr.isAR1 hnd (rbar := rbar) (β := β) (κ := κ)
  refine ⟨(hiff (piBar119 β li rbar istar) xs is _ _ _ _ _ _).mpr
    ⟨⟨hx2, his⟩, ⟨cu1, cu2⟩, ⟨cr1, cr2⟩⟩, ?_⟩
  intro πbar xbar ibar fπ fx fi gπ gx gi hA hI
  obtain ⟨-, ⟨f1, f2⟩, ⟨g1, g2⟩⟩ := (hiff πbar xbar ibar fπ fx fi gπ gx gi).mp ⟨hA, hI⟩
  have hfu := (f4_u_optimal hβ0 hβ1 hρu1 hκ hσ hlx hli (piUF4 β κ σ lx li ρu)
    (xUF4 β κ σ lx li ρu) (iUF4 β κ σ lx li ρu)).mpr ⟨rfl, rfl, rfl⟩
  have hgr := (f4_r_optimal hβ0 hβ1 hρr1 hκ hσ hlx hli (piRF4 β κ σ lx li ρr)
    (xRF4 β κ σ lx li ρr) (iRF4 β κ σ lx li ρr)).mpr ⟨rfl, rfl, rfl⟩
  have e1 := hfu.2 fπ fx fi ⟨f1, f2⟩
  have e2 := hgr.2 gπ gx gi ⟨g1, g2⟩
  rw [hL, hL]
  set Pu := objF4 lx li (piUF4 β κ σ lx li ρu) (xUF4 β κ σ lx li ρu) (iUF4 β κ σ lx li ρu)
  set Pr := objF4 lx li (piRF4 β κ σ lx li ρr) (xRF4 β κ σ lx li ρr) (iRF4 β κ σ lx li ρr)
  set Fu := objF4 lx li fπ fx fi
  set Fr := objF4 lx li gπ gx gi
  have m1 : 0 ≤ Ku * (Fu - Pu) := mul_nonneg hKu.le (by linarith)
  have m2 : 0 ≤ Kr * (Fr - Pr) := mul_nonneg hKr.le (by linarith)
  refine ⟨by linarith, ⟨fun heq => ?_, fun ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ => ?_⟩⟩
  swap
  · have q1 : Fu = Pu := by simp only [Fu, Pu]; rw [a1, a2, a3]
    have q2 : Fr = Pr := by simp only [Fr, Pr]; rw [b1, b2, b3]
    rw [q1, q2]
  have z1 : Ku * (Fu - Pu) = 0 := by linarith
  have z2 : Kr * (Fr - Pr) = 0 := by linarith
  have hu0 : Fu = Pu := by linarith [(mul_eq_zero.mp z1).resolve_left hKu.ne']
  have hr0 : Fr = Pr := by linarith [(mul_eq_zero.mp z2).resolve_left hKr.ne']
  refine ⟨(f4_u_optimal hβ0 hβ1 hρu1 hκ hσ hlx hli fπ fx fi).mp ⟨⟨f1, f2⟩, fun a b c h => ?_⟩,
    (f4_r_optimal hβ0 hβ1 hρr1 hκ hσ hlx hli gπ gx gi).mp ⟨⟨g1, g2⟩, fun a b c h => ?_⟩⟩
  · change Fu ≤ _
    rw [hu0]; exact hfu.2 a b c h
  · change Fr ≤ _
    rw [hr0]; exact hgr.2 a b c h

end Woodford.GainsFromCommitment.Noninertial
