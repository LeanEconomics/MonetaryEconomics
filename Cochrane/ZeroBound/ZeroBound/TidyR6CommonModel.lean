/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.LiftoffStructure
import ZeroBound.TidyR6WoodfordZLB

/-!
# A common model for the zero bound of Chapter 20 and Woodford's Proposition 6.9

Cochrane (2023), Chapter 20, §§20.1–20.2.4, pp. 465–480 (the new-Keynesian model at the bound,
the natural-rate trap, forward guidance and lift-off), linked with Woodford (2003), Chapter 6,
§4.2, Proposition 6.9, p. 428 (proof App. E.5, pp. 700–703), which replaces the bound
`i_t ≥ 0` by the moment constraints `Ê[i] ≥ 0`, `Ê[i²] ≤ K Ê[i]²` (`TidyR6WoodfordZLB`).

`LinksGaliWoodford.Moments` compares the two constraints only on abstract interest-rate paths.
Here both problems are special cases of one model, the discrete model of `LinksGaliWoodford`
(Galí's and Cochrane's: `π_t = βπ_{t+1} + κx_t`, the IS curve with natural rate `rⁿ`, which for
`rⁿ = natRate ρ η t_Z` is the trap of §20.2.2) with Galí's loss `∑βᵗ(π_t² + ϑx_t²)`:
* policies are `(x, π, c)` (`Pol`), the structural set is `Cset` (`c = 1`, the Phillips curve at
  every date, finite loss), the interest rate `i = rateLin p`,
  `i_t = c rⁿ_t + π_{t+1} + σ(x_{t+1} − x_t)`, is LINEAR in the policy, and the moments are
  `m₁ = (1 − β)∑βᵗi_t`, `m₂ = (1 − β)∑βᵗi_t²` (`mom1`, `mom2`; for bounded rates they are
  Woodford's `TidyR6WoodfordZLB.dAvg` under perfect foresight, `mom1_eq_dAvg`, `mom2_eq_dAvg`);
* **the zero bound of Chapter 20 is the special case `i ≥ 0` at every date**: the pathwise
  optimum of the common model is exactly Galí's commitment optimum `LinksGaliWoodford.Optimal`
  (`pathOpt_iff`), which exists and is unique (`pathOpt_existsUnique`, from
  `LiftoffStructure.optimal_exists_unique`);
* **Woodford's constraint is the other special case**: Proposition 6.9 holds in the common model
  (`prop_6_9_common`), from the restated abstract steps of the Woodford project; the structural
  hypotheses — `Cset` convex, the loss convex, `m₁` affine, `m₂` convex — are proved here
  (`cset_convex`, `loss_convexOn`, `mom1_affine`, `mom2_convexOn`), and the moment-constrained
  optimum is unique (`momOpt_unique`).

The two problems are compared inside the model: every pathwise-feasible policy has
`Ê[i] ≥ 0` (`pathwise_mom1_nonneg`); at Woodford's calibration (`β = 0.99`, `K = 1 + 2.26⁻²`)
and the trap `rⁿ = natRate 1 1 0`, neither feasible set contains the other, with model-feasible
witnesses (`neither_in_model`); and the optimal losses compare as the constraint sets do, with
equality and the same optimum when each optimum satisfies the other constraint
(`values_compare`).
-/

namespace Cochrane.ZeroBound.TidyR6CommonModel

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford Cochrane.ZeroBound.TidyR6WoodfordZLB

/-! ## The common model -/

/-- Cochrane (2023), §20.2.4, p. 479, and Woodford (2003), §6.4.2, p. 428: a policy is an
output-gap path, an inflation path and the coefficient `c` of the natural rate (`c = 1` on the
structural set), so that the interest rate is linear in the policy. -/
abbrev Pol : Type := (ℕ → ℝ) × (ℕ → ℝ) × ℝ

/-- Cochrane (2023), eq. (5.1), p. 118, and Galí (2015), eq. (30): the interest rate implied by
the IS curve, `i_t = c rⁿ_t + π_{t+1} + σ(x_{t+1} − x_t)`, a linear map of the policy. -/
def rateLin (σ : ℝ) (rn : ℕ → ℝ) : Pol →ₗ[ℝ] (ℕ → ℝ) where
  toFun p := fun t => p.2.2 * rn t + p.2.1 (t + 1) + σ * (p.1 (t + 1) - p.1 t)
  map_add' p q := by
    funext t
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    ring
  map_smul' a p := by
    funext t
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Cochrane (2023), eq. (5.2), p. 118, and Woodford (2003), p. 428 (the structural equations):
the policies of the common model: `c = 1`, the Phillips curve at every date and finite loss. -/
def Cset (β κ ϑ : ℝ) : Set Pol :=
  {p | p.2.2 = 1 ∧ (∀ t, NKPC β κ p.1 p.2.1 t) ∧ Summable (lossTerm β ϑ p.1 p.2.1)}

/-- Cochrane (2023), p. 485, and Galí (2015), p. 148: the loss `∑βᵗ(π_t² + ϑx_t²)`. -/
noncomputable def Lfun (β ϑ : ℝ) (p : Pol) : ℝ := loss β ϑ p.1 p.2.1

/-- Woodford (2003), (4.18), p. 428: the discounted mean `Ê[i] = (1 − β)∑βᵗi_t`. -/
noncomputable def mom1 (β σ : ℝ) (rn : ℕ → ℝ) (p : Pol) : ℝ :=
  (1 - β) * ∑' t, β ^ t * rateLin σ rn p t

/-- Woodford (2003), (4.19), p. 428: the discounted second moment `Ê[i²] = (1 − β)∑βᵗi_t²`. -/
noncomputable def mom2 (β σ : ℝ) (rn : ℕ → ℝ) (p : Pol) : ℝ :=
  (1 - β) * ∑' t, β ^ t * rateLin σ rn p t ^ 2

/-- Cochrane (2023), eq. (5.1): on the structural set the linear rate is the implied rate of
`LinksGaliWoodford`. -/
theorem rateLin_eq {β κ ϑ σ : ℝ} {rn : ℕ → ℝ} {p : Pol} (hp : p ∈ Cset β κ ϑ) (t : ℕ) :
    rateLin σ rn p t = impliedRate σ rn p.1 p.2.1 t := by
  simp only [rateLin, LinearMap.coe_mk, AddHom.coe_mk, impliedRate, hp.1, one_mul]

/-! ## Summability and the structure of the problem -/

/-- Galí (2015), p. 148: `(a + b)² ≤ 2a² + 2b²`. -/
theorem sq_add_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Galí (2015), p. 148: convexity of squares, `(au + bv)² ≤ au² + bv²` for `a, b ≥ 0`,
`a + b = 1`. -/
theorem sq_convex {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a * u + b * v) ^ 2 ≤ a * u ^ 2 + b * v ^ 2 := by
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg (u - v), mul_nonneg ha hb]

/-- Woodford (2003), App. E.3, p. 697: on the structural set, with a bounded natural rate,
`βᵗi_t²` is summable. -/
theorem summable_rate_sq {β κ ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) {p : Pol} (hp : p ∈ Cset β κ ϑ) :
    Summable fun t => β ^ t * rateLin σ rn p t ^ 2 := by
  obtain ⟨M, hM⟩ := hrn
  obtain ⟨hpc, -, hs⟩ := hp
  have hs1 : Summable fun t => lossTerm β ϑ p.1 p.2.1 (t + 1) := hs.comp_injective
    (add_left_injective 1)
  have hg : Summable fun t : ℕ => β ^ t := summable_geometric_of_lt_one hβ.le hβ1
  have hbound : ∀ t, β ^ t * rateLin σ rn p t ^ 2 ≤
      4 * M ^ 2 * β ^ t + (4 / β + 4 * σ ^ 2 / (β * ϑ)) * lossTerm β ϑ p.1 p.2.1 (t + 1) +
        4 * σ ^ 2 / ϑ * lossTerm β ϑ p.1 p.2.1 t := by
    intro t
    have hbt : 0 < β ^ t := pow_pos hβ t
    have hr : rateLin σ rn p t = p.2.2 * rn t + p.2.1 (t + 1) + σ * (p.1 (t + 1) - p.1 t) := rfl
    rw [hr, hpc, one_mul]
    have h4 : (rn t + p.2.1 (t + 1) + σ * (p.1 (t + 1) - p.1 t)) ^ 2 ≤
        4 * rn t ^ 2 + 4 * p.2.1 (t + 1) ^ 2 + 4 * σ ^ 2 * p.1 (t + 1) ^ 2 +
          4 * σ ^ 2 * p.1 t ^ 2 := by
      nlinarith [sq_nonneg (rn t - p.2.1 (t + 1)), sq_nonneg (rn t + p.2.1 (t + 1) -
        σ * p.1 (t + 1) - σ * p.1 t), sq_nonneg (σ * p.1 (t + 1) + σ * p.1 t),
        sq_nonneg (rn t + p.2.1 (t + 1) - σ * (p.1 (t + 1) - p.1 t)),
        sq_nonneg (σ * p.1 (t + 1) - σ * p.1 t - rn t + p.2.1 (t + 1)),
        sq_nonneg (rn t - p.2.1 (t + 1) + σ * p.1 (t + 1) + σ * p.1 t)]
    have hrn2 : rn t ^ 2 ≤ M ^ 2 := by
      have := hM t
      nlinarith [abs_nonneg (rn t), sq_abs (rn t)]
    have hL1 : lossTerm β ϑ p.1 p.2.1 (t + 1) =
        β * β ^ t * (p.2.1 (t + 1) ^ 2 + ϑ * p.1 (t + 1) ^ 2) := by
      unfold lossTerm; rw [pow_succ]; ring
    have hL0 : lossTerm β ϑ p.1 p.2.1 t = β ^ t * (p.2.1 t ^ 2 + ϑ * p.1 t ^ 2) := rfl
    rw [hL1, hL0]
    have e1 : (4 / β + 4 * σ ^ 2 / (β * ϑ)) * (β * β ^ t * (p.2.1 (t + 1) ^ 2 +
        ϑ * p.1 (t + 1) ^ 2)) = β ^ t * (4 * p.2.1 (t + 1) ^ 2 + 4 * σ ^ 2 * p.1 (t + 1) ^ 2) +
        β ^ t * (4 * ϑ / 1 * p.1 (t + 1) ^ 2 + 4 * σ ^ 2 / ϑ * p.2.1 (t + 1) ^ 2) := by
      field_simp
      ring
    have e2 : 4 * σ ^ 2 / ϑ * (β ^ t * (p.2.1 t ^ 2 + ϑ * p.1 t ^ 2)) =
        β ^ t * (4 * σ ^ 2 * p.1 t ^ 2) + β ^ t * (4 * σ ^ 2 / ϑ * p.2.1 t ^ 2) := by
      field_simp
      ring
    rw [e1, e2]
    have n1 : 0 ≤ β ^ t * (4 * ϑ / 1 * p.1 (t + 1) ^ 2 + 4 * σ ^ 2 / ϑ * p.2.1 (t + 1) ^ 2) := by
      positivity
    have n2 : 0 ≤ β ^ t * (4 * σ ^ 2 / ϑ * p.2.1 t ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left h4 hbt.le
    nlinarith [mul_le_mul_of_nonneg_left hrn2 hbt.le]
  refine Summable.of_nonneg_of_le (fun t => by positivity) hbound ?_
  exact ((hg.mul_left _).add (hs1.mul_left _)).add (hs.mul_left _)

/-- Woodford (2003), App. E.3, p. 697: on the structural set, `βᵗ|i_t|` is summable
(`|i| ≤ (1 + i²)/2`), so `Ê[i]` is a genuine sum. -/
theorem summable_rate {β κ ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) {p : Pol} (hp : p ∈ Cset β κ ϑ) :
    Summable fun t => β ^ t * rateLin σ rn p t := by
  have h2 := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn hp
  have hg : Summable fun t : ℕ => β ^ t := summable_geometric_of_lt_one hβ.le hβ1
  refine Summable.of_norm_bounded ((hg.add h2).div_const 2) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ t)]
  have : |rateLin σ rn p t| ≤ (1 + rateLin σ rn p t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|rateLin σ rn p t| - 1), sq_abs (rateLin σ rn p t)]
  have hb := mul_le_mul_of_nonneg_left this (pow_pos hβ t).le
  linarith

/-- Galí (2015), p. 149, and Woodford (2003), p. 428: the structural set is convex, and the loss
of a convex combination is at most the combination of the losses (termwise). -/
theorem lossTerm_convex {β ϑ a b : ℝ} (hβ : 0 ≤ β) (hϑ : 0 ≤ ϑ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (x π y q : ℕ → ℝ) (t : ℕ) :
    lossTerm β ϑ (fun s => a * x s + b * y s) (fun s => a * π s + b * q s) t ≤
      a * lossTerm β ϑ x π t + b * lossTerm β ϑ y q t := by
  unfold lossTerm
  have h1 := sq_convex (u := π t) (v := q t) ha hb hab
  have h2 := sq_convex (u := x t) (v := y t) ha hb hab
  have hbt : 0 ≤ β ^ t := pow_nonneg hβ t
  nlinarith [mul_le_mul_of_nonneg_left h1 hbt, mul_le_mul_of_nonneg_left h2 hbt,
    mul_le_mul_of_nonneg_left h2 (mul_nonneg hbt hϑ)]

/-- Woodford (2003), App. E.5, p. 701 (the policy set `C` is convex): `Cset` is convex. -/
theorem cset_convex {β κ ϑ : ℝ} (hβ : 0 ≤ β) (hϑ : 0 ≤ ϑ) : Convex ℝ (Cset β κ ϑ) := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, fun t => ?_, ?_⟩
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, hp.1, hq.1]; linarith
  · have h1 := hp.2.1 t
    have h2 := hq.2.1 t
    unfold NKPC at h1 h2 ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [h1, h2]
    ring
  · have e1 : (a • p + b • q).1 = fun s => a * p.1 s + b * q.1 s := by
      funext s; simp
    have e2 : (a • p + b • q).2.1 = fun s => a * p.2.1 s + b * q.2.1 s := by
      funext s; simp
    rw [e1, e2]
    refine Summable.of_nonneg_of_le (fun t => ?_) (lossTerm_convex hβ hϑ ha hb hab _ _ _ _)
      ((hp.2.2.mul_left a).add (hq.2.2.mul_left b))
    unfold lossTerm; positivity

/-- Woodford (2003), (4.20), p. 428: the loss is convex on the structural set. -/
theorem loss_convexOn {β κ ϑ : ℝ} (hβ : 0 ≤ β) (hϑ : 0 ≤ ϑ) :
    ConvexOn ℝ (Cset β κ ϑ) (Lfun β ϑ) := by
  refine ⟨cset_convex hβ hϑ, fun p hp q hq a b ha hb hab => ?_⟩
  have e1 : (a • p + b • q).1 = fun s => a * p.1 s + b * q.1 s := by
    funext s; simp
  have e2 : (a • p + b • q).2.1 = fun s => a * p.2.1 s + b * q.2.1 s := by
    funext s; simp
  have hS := (cset_convex (κ := κ) hβ hϑ hp hq ha hb hab).2.2
  rw [e1, e2] at hS
  simp only [Lfun, smul_eq_mul, e1, e2, loss]
  rw [← tsum_mul_left, ← tsum_mul_left, ← (hp.2.2.mul_left a).tsum_add (hq.2.2.mul_left b)]
  exact hS.tsum_le_tsum (lossTerm_convex hβ hϑ ha hb hab _ _ _ _)
    ((hp.2.2.mul_left a).add (hq.2.2.mul_left b))

/-- Woodford (2003), App. E.5, p. 701 (`m₁` linear in the policy): on the structural set,
`Ê[i]` of a combination is the combination of the `Ê[i]`. -/
theorem mom1_comb {β κ ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) {p q : Pol} (hp : p ∈ Cset β κ ϑ) (hq : q ∈ Cset β κ ϑ)
    (a b : ℝ) : mom1 β σ rn (a • p + b • q) = a * mom1 β σ rn p + b * mom1 β σ rn q := by
  have h1 := summable_rate (σ := σ) hβ hβ1 hϑ hrn hp
  have h2 := summable_rate (σ := σ) hβ hβ1 hϑ hrn hq
  unfold mom1
  have e : (fun t => β ^ t * rateLin σ rn (a • p + b • q) t) =
      fun t => a * (β ^ t * rateLin σ rn p t) + b * (β ^ t * rateLin σ rn q t) := by
    funext t
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, (h1.mul_left a).tsum_add (h2.mul_left b), tsum_mul_left, tsum_mul_left]
  ring

/-- Woodford (2003), App. E.5, p. 701 (`m₁` linear in the policy): on the structural set
`Ê[i]` is affine. -/
theorem mom1_affine {β κ ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) :
    ConvexOn ℝ (Cset β κ ϑ) (mom1 β σ rn) ∧ ConcaveOn ℝ (Cset β κ ϑ) (mom1 β σ rn) := by
  have hC := cset_convex (κ := κ) hβ.le hϑ.le
  exact ⟨⟨hC, fun p hp q hq a b _ _ _ => by rw [mom1_comb hβ hβ1 hϑ hrn hp hq a b]; simp⟩,
    ⟨hC, fun p hp q hq a b _ _ _ => by rw [mom1_comb hβ hβ1 hϑ hrn hp hq a b]; simp⟩⟩

/-- Woodford (2003), App. E.5, p. 701 (`m₂` convex in the policy): on the structural set
`Ê[i²]` is convex. -/
theorem mom2_convexOn {β κ ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) : ConvexOn ℝ (Cset β κ ϑ) (mom2 β σ rn) := by
  have hC := cset_convex (κ := κ) hβ.le hϑ.le
  refine ⟨hC, fun p hp q hq a b ha hb hab => ?_⟩
  have h1 := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn hp
  have h2 := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn hq
  have h3 := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn (hC hp hq ha hb hab)
  unfold mom2
  simp only [smul_eq_mul]
  have hle : ∑' t, β ^ t * rateLin σ rn (a • p + b • q) t ^ 2 ≤
      a * ∑' t, β ^ t * rateLin σ rn p t ^ 2 + b * ∑' t, β ^ t * rateLin σ rn q t ^ 2 := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (h1.mul_left a).tsum_add (h2.mul_left b)]
    refine h3.tsum_le_tsum (fun t => ?_) ((h1.mul_left a).add (h2.mul_left b))
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := sq_convex (u := rateLin σ rn p t) (v := rateLin σ rn q t) ha hb hab
    have hbt : 0 ≤ β ^ t := pow_nonneg hβ.le t
    nlinarith [mul_le_mul_of_nonneg_left this hbt]
  have : 0 ≤ 1 - β := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hle this]

/-! ## Woodford's Proposition 6.9 in the common model -/

/-- Woodford (2003), (E.25), p. 703: completing the square,
`(1 − β)∑βᵗ(i_t − c)² = Ê[i²] − 2cÊ[i] + c²`. -/
theorem avg_sq_dev {β κ ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) {p : Pol} (hp : p ∈ Cset β κ ϑ) (c : ℝ) :
    (1 - β) * ∑' t, β ^ t * (rateLin σ rn p t - c) ^ 2 =
      mom2 β σ rn p - 2 * c * mom1 β σ rn p + c ^ 2 := by
  have h1 := summable_rate (σ := σ) hβ hβ1 hϑ hrn hp
  have h2 := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn hp
  have hg : Summable fun t : ℕ => β ^ t := summable_geometric_of_lt_one hβ.le hβ1
  have e : (fun t => β ^ t * (rateLin σ rn p t - c) ^ 2) = fun t =>
      β ^ t * rateLin σ rn p t ^ 2 + (-(2 * c)) * (β ^ t * rateLin σ rn p t) +
        c ^ 2 * β ^ t := by
    funext t; ring
  rw [e, (h2.add (h1.mul_left _)).tsum_add (hg.mul_left _), h2.tsum_add (h1.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hβ.le hβ1]
  unfold mom1 mom2
  have : 1 - β ≠ 0 := by linarith
  field_simp
  ring

/-- Woodford (2003), Proposition 6.9, eq. (4.21), p. 428, **in the common model** (Cochrane's
zero-bound model of Chapter 20 with Galí's loss): let `p` minimise the loss over the structural
set subject to `Ê[i] ≥ 0`, `Ê[i²] ≤ KÊ[i]²` with `K > 1`. Under Woodford's remaining hypotheses
(`Ê[i] ≥ ī > 0` at the optimum, a Slater point, no unconstrained minimiser satisfies the
constraints, the value function differentiable at the optimum's moments) there are multipliers
`μ₁ ≥ 0`, `μ₂ > 0`, `μ₁ = 2KÊ[i]μ₂`, with `i** = KÊ[i] − ī > 0`, such that `p` minimises, over
the structural set alone, `L + μ₂Ê[(i − ī − i**)²]`. -/
theorem prop_6_9_common {β κ ϑ σ K ib : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {rn : ℕ → ℝ} (hrn : ∃ M, ∀ t, |rn t| ≤ M) (hK : 1 < K) (hib : 0 < ib) {p p0 : Pol}
    (hopt : IsConstrOpt (Cset β κ ϑ) (Lfun β ϑ) (mom1 β σ rn) (mom2 β σ rn) K p)
    (hm1 : ib ≤ mom1 β σ rn p) (hp0 : p0 ∈ Cset β κ ϑ)
    (h01 : mom1 β σ rn p < mom1 β σ rn p0) (h02 : mom2 β σ rn p0 < mom2 β σ rn p)
    (hno : ∀ q ∈ Cset β κ ϑ, (∀ r ∈ Cset β κ ϑ, Lfun β ϑ q ≤ Lfun β ϑ r) →
      ¬ Feasible (Cset β κ ϑ) (mom1 β σ rn) (mom2 β σ rn) K q)
    {V' : ℝ × ℝ →L[ℝ] ℝ}
    (hV : HasFDerivAt (valueFn (Cset β κ ϑ) (Lfun β ϑ) (mom1 β σ rn) (mom2 β σ rn)) V'
      (mom1 β σ rn p, mom2 β σ rn p)) :
    ∃ μ1 μ2 : ℝ, 0 ≤ μ1 ∧ 0 < μ2 ∧ μ1 = 2 * K * mom1 β σ rn p * μ2 ∧
      0 < K * mom1 β σ rn p - ib ∧
      ∀ q ∈ Cset β κ ϑ, Lfun β ϑ p + μ2 * ((1 - β) * ∑' t, β ^ t *
          (rateLin σ rn p t - ib - (K * mom1 β σ rn p - ib)) ^ 2) ≤
        Lfun β ϑ q + μ2 * ((1 - β) * ∑' t, β ^ t *
          (rateLin σ rn q t - ib - (K * mom1 β σ rn p - ib)) ^ 2) := by
  have hC := cset_convex (κ := κ) hβ.le hϑ.le
  have hL := loss_convexOn (κ := κ) hβ.le hϑ.le
  obtain ⟨hm1c, hm1c'⟩ := mom1_affine (κ := κ) (σ := σ) hβ hβ1 hϑ hrn
  have hm2c := mom2_convexOn (κ := κ) (σ := σ) hβ hβ1 hϑ hrn
  have hK0 : 0 ≤ K := by linarith
  have hpos : 0 < mom1 β σ rn p := lt_of_lt_of_le hib hm1
  obtain ⟨μ1, μ2, hμ1, hμ2, hlag⟩ :=
    prop_6_9_multipliers hC hL hm1c' hm2c hK0 hopt hp0 h01 h02
  have hμ2pos := mu2_pos hK0 hL hm1c hm1c' hm2c hopt hpos hno hp0 h01 h02 hμ1 hμ2 hlag hV
  have hbind := binds_of_unconstrained_infeasible hL hm1c hm1c' hm2c hopt hpos hno
  have henv := envelope hK0 hopt hbind hpos hp0 h01 h02 hμ1 hμ2 hlag hV
  refine ⟨μ1, μ2, hμ1, hμ2pos, henv, iStarStar_pos hK hm1 hib, fun q hq => ?_⟩
  have hsq : ∀ r ∈ Cset β κ ϑ, μ2 * ((1 - β) * ∑' t, β ^ t *
      (rateLin σ rn r t - ib - (K * mom1 β σ rn p - ib)) ^ 2) =
      -μ1 * mom1 β σ rn r + μ2 * mom2 β σ rn r + μ2 * (K * mom1 β σ rn p) ^ 2 := by
    intro r hr
    have e : (fun t => β ^ t * (rateLin σ rn r t - ib - (K * mom1 β σ rn p - ib)) ^ 2) =
        fun t => β ^ t * (rateLin σ rn r t - K * mom1 β σ rn p) ^ 2 := by
      funext t; ring
    rw [e, avg_sq_dev hβ hβ1 hϑ hrn hr, henv]
    ring
  rw [hsq p hopt.1.1, hsq q hq]
  have := hlag q hq
  linarith

/-- Woodford (2003), (4.18)–(4.19), p. 428: for bounded rate paths the common model's moments
are Woodford's discounted averages under perfect foresight. -/
theorem mom1_eq_dAvg (β σ : ℝ) (rn : ℕ → ℝ) (p : Pol) :
    mom1 β σ rn p = dAvg perfectForesight β (fun t _ => rateLin σ rn p t) () := rfl

/-- Woodford (2003), (4.19), p. 428: the second moment as a discounted average. -/
theorem mom2_eq_dAvg (β σ : ℝ) (rn : ℕ → ℝ) (p : Pol) :
    mom2 β σ rn p = dAvg perfectForesight β (fun t _ => rateLin σ rn p t ^ 2) () := rfl

/-! ## The zero bound of Chapter 20 as the other special case -/

/-- Cochrane (2023), §20.2.4, p. 479, and Galí (2015), p. 148: the pathwise-optimal policy of
the common model: on the structural set, `i_t ≥ 0` at every date, and minimal loss among such
policies. -/
def PathOpt (β κ σ ϑ : ℝ) (rn : ℕ → ℝ) (p : Pol) : Prop :=
  p ∈ Cset β κ ϑ ∧ (∀ t, 0 ≤ rateLin σ rn p t) ∧
    ∀ q ∈ Cset β κ ϑ, (∀ t, 0 ≤ rateLin σ rn q t) → Lfun β ϑ p ≤ Lfun β ϑ q

/-- Cochrane (2023), §20.1, p. 465 (the bound `i ≥ 0`), Galí (2015), p. 149: the Phillips
curve and `i ≥ 0` at every date is exactly Galí's feasibility (`σ > 0`). -/
theorem feasible_iff {β κ σ : ℝ} (hσ : 0 < σ) (rn x π : ℕ → ℝ) :
    Feasible β κ σ rn x π ↔ (∀ t, NKPC β κ x π t) ∧ ∀ t, 0 ≤ impliedRate σ rn x π t := by
  constructor
  · intro h
    refine ⟨fun t => (h t).1, fun t => ?_⟩
    rw [impliedRate_eq hσ.ne']
    exact mul_nonneg hσ.le (by linarith [(h t).2])
  · rintro ⟨h1, h2⟩ t
    refine ⟨h1 t, ?_⟩
    have := h2 t
    rw [impliedRate_eq hσ.ne'] at this
    have := (mul_nonneg_iff_of_pos_left hσ).mp this
    linarith

/-- Cochrane (2023), §20.2.4, p. 479: **the zero bound of Chapter 20 is a special case of the
common model** — its pathwise optimum is exactly Galí's commitment optimum. -/
theorem pathOpt_iff {β κ σ ϑ : ℝ} (hσ : 0 < σ) {rn x π : ℕ → ℝ} :
    PathOpt β κ σ ϑ rn (x, π, 1) ↔ Optimal β κ σ ϑ rn x π := by
  have hrate : ∀ (y q : ℕ → ℝ) t, rateLin σ rn (y, q, 1) t = impliedRate σ rn y q t :=
    fun y q t => by simp [rateLin, impliedRate]
  constructor
  · rintro ⟨⟨-, hN, hS⟩, hpos, hmin⟩
    refine ⟨(feasible_iff hσ rn x π).mpr ⟨hN, fun t => by rw [← hrate]; exact hpos t⟩, hS,
      fun y q hF hSq => ?_⟩
    obtain ⟨hN', hpos'⟩ := (feasible_iff hσ rn y q).mp hF
    exact hmin (y, q, 1) ⟨rfl, hN', hSq⟩ fun t => by rw [hrate]; exact hpos' t
  · rintro ⟨hF, hS, hmin⟩
    obtain ⟨hN, hpos⟩ := (feasible_iff hσ rn x π).mp hF
    refine ⟨⟨rfl, hN, hS⟩, fun t => by rw [hrate]; exact hpos t, fun q hq hqpos => ?_⟩
    obtain ⟨hc, hN', hSq⟩ := hq
    have hq' : q = (q.1, q.2.1, 1) := by rw [← hc]
    have hF' : Feasible β κ σ rn q.1 q.2.1 := (feasible_iff hσ rn _ _).mpr ⟨hN', fun t => by
      have := hqpos t
      rwa [hq', hrate] at this⟩
    exact hmin _ _ hF' hSq

/-- Cochrane (2023), §20.2.4 and Galí (2015), §5.4.2: in the common model with the trap
`rⁿ = natRate ρ η t_Z`, the pathwise optimum exists and is unique (it is Galí's commitment
optimum, `LiftoffStructure.optimal_exists_unique`). -/
theorem pathOpt_existsUnique {β κ σ ϑ ρ η : ℝ} (hβ : 0 < β) (hσ : 0 < σ) (hϑ : 0 < ϑ)
    (hρ : 0 ≤ ρ) (tZ : ℕ) :
    ∃! p : Pol, PathOpt β κ σ ϑ (natRate ρ η tZ) p := by
  obtain ⟨x, π, hopt, huniq⟩ := LiftoffStructure.optimal_exists_unique (κ := κ) (η := η) hβ hσ
    hϑ hρ tZ
  refine ⟨(x, π, 1), (pathOpt_iff hσ).mpr hopt, fun p hp => ?_⟩
  have hc : p.2.2 = 1 := hp.1.1
  have hp' : p = (p.1, p.2.1, 1) := by rw [← hc]
  rw [hp'] at hp ⊢
  obtain ⟨h1, h2⟩ := huniq _ _ ((pathOpt_iff hσ).mp hp)
  rw [h1, h2]

/-! ## Comparing the two problems inside the model -/

/-- Woodford (2003), p. 428, and Cochrane (2023), §20.1: every pathwise-feasible policy of the
common model has `Ê[i] ≥ 0`. -/
theorem pathwise_mom1_nonneg {β σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {rn : ℕ → ℝ} {p : Pol}
    (hpos : ∀ t, 0 ≤ rateLin σ rn p t) : 0 ≤ mom1 β σ rn p := by
  unfold mom1
  exact mul_nonneg (by linarith) (tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ.le t) (hpos t))

/-- Woodford (2003), p. 428, and Cochrane (2023), §20.2.4: **the optimal losses compare as the
constraint sets do.** If `p` is the pathwise optimum and `w` a moment-constrained optimum: when
`p` satisfies Woodford's constraint, `L(w) ≤ L(p)`; when `w` satisfies the pathwise bound,
`L(p) ≤ L(w)`; when both hold the losses are equal and `w` is itself a pathwise optimum. -/
theorem values_compare {β κ ϑ σ K : ℝ} (hβ : 0 < β) (hβ1 : β < 1) {rn : ℕ → ℝ}
    {p w : Pol} (hp : PathOpt β κ σ ϑ rn p)
    (hw : IsConstrOpt (Cset β κ ϑ) (Lfun β ϑ) (mom1 β σ rn) (mom2 β σ rn) K w) :
    (mom2 β σ rn p ≤ K * mom1 β σ rn p ^ 2 → Lfun β ϑ w ≤ Lfun β ϑ p) ∧
      ((∀ t, 0 ≤ rateLin σ rn w t) → Lfun β ϑ p ≤ Lfun β ϑ w) ∧
      (mom2 β σ rn p ≤ K * mom1 β σ rn p ^ 2 → (∀ t, 0 ≤ rateLin σ rn w t) →
        Lfun β ϑ p = Lfun β ϑ w ∧ PathOpt β κ σ ϑ rn w) := by
  have h1 : mom2 β σ rn p ≤ K * mom1 β σ rn p ^ 2 → Lfun β ϑ w ≤ Lfun β ϑ p := fun h =>
    hw.2 p ⟨hp.1, pathwise_mom1_nonneg hβ hβ1 hp.2.1, h⟩
  have h2 : (∀ t, 0 ≤ rateLin σ rn w t) → Lfun β ϑ p ≤ Lfun β ϑ w := fun h =>
    hp.2.2 w hw.1.1 h
  refine ⟨h1, h2, fun ha hb => ⟨le_antisymm (h2 hb) (h1 ha), hw.1.1, hb, fun q hq hqpos => ?_⟩⟩
  exact le_trans (h1 ha) (hp.2.2 q hq hqpos)

/-- Cochrane (2023), §20.2.2 (the trap, `t_Z = 0`): the model-feasible policy whose rate is `c`
at date 0 and the natural rate `ρ` afterwards: `x₀ = −(η + c)/σ`, `π₀ = κx₀`, zero after. -/
noncomputable def spikePol (κ σ η c : ℝ) : Pol :=
  (fun t => if t = 0 then -(η + c) / σ else 0, fun t => if t = 0 then κ * (-(η + c) / σ) else 0,
    1)

/-- Cochrane (2023), §20.2.2: the spike policy is in the structural set and its rate is `c` at
date 0 and `ρ` afterwards. -/
theorem spikePol_spec {β κ ϑ σ ρ η c : ℝ} (hσ : σ ≠ 0) :
    spikePol κ σ η c ∈ Cset β κ ϑ ∧
      ∀ t, rateLin σ (natRate ρ η 0) (spikePol κ σ η c) t = if t = 0 then c else ρ := by
  refine ⟨⟨rfl, fun t => ?_, ?_⟩, fun t => ?_⟩
  · unfold NKPC spikePol
    rcases t with _ | t <;> simp
  · refine summable_of_ne_finset_zero (s := {0}) fun t ht => ?_
    have : t ≠ 0 := by simpa using ht
    simp [lossTerm, spikePol, this]
  · simp only [rateLin, LinearMap.coe_mk, AddHom.coe_mk, spikePol, natRate]
    rcases t with _ | t
    · simp
      field_simp
      ring
    · simp

/-- Woodford (2003), p. 428: the discounted moments of a path equal to `c` at date 0 and `ρ`
afterwards: `Ê[i] = (1 − β)c + βρ`, `Ê[i²] = (1 − β)c² + βρ²`. -/
theorem spike_moments {β κ σ ρ η c : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1) (hσ : σ ≠ 0) :
    mom1 β σ (natRate ρ η 0) (spikePol κ σ η c) = (1 - β) * c + β * ρ ∧
      mom2 β σ (natRate ρ η 0) (spikePol κ σ η c) = (1 - β) * c ^ 2 + β * ρ ^ 2 := by
  have hr := (spikePol_spec (β := β) (κ := κ) (ϑ := 1) (ρ := ρ) (η := η) (c := c) hσ).2
  have hg := hasSum_geometric_of_lt_one hβ hβ1
  have key : ∀ a b : ℝ, HasSum (fun t : ℕ => β ^ t * (if t = 0 then a else b))
      (a + b * (β / (1 - β))) := by
    intro a b
    have h1 := (hg.mul_left b).add (hasSum_ite_eq 0 (a - b))
    convert h1 using 1
    · funext t
      by_cases ht : t = 0
      · subst ht; simp
      · simp [ht, mul_comm]
    · have hne : 1 - β ≠ 0 := by linarith
      field_simp
      ring
  have hne : 1 - β ≠ 0 := by linarith
  constructor
  · unfold mom1
    have e : (fun t => β ^ t * rateLin σ (natRate ρ η 0) (spikePol κ σ η c) t) =
        fun t : ℕ => β ^ t * (if t = 0 then c else ρ) := by
      funext t; rw [hr t]
    rw [e, (key c ρ).tsum_eq]
    field_simp
  · unfold mom2
    have e : (fun t => β ^ t * rateLin σ (natRate ρ η 0) (spikePol κ σ η c) t ^ 2) =
        fun t : ℕ => β ^ t * (if t = 0 then c ^ 2 else ρ ^ 2) := by
      funext t
      rw [hr t]
      by_cases ht : t = 0 <;> simp [ht]
    rw [e, (key _ _).tsum_eq]
    field_simp

/-- Woodford (2003), Table 6.1, p. 434 (`K = 1 + 2.26⁻²`, `β = 0.99`), in the common model with
the trap `rⁿ = natRate 1 1 0` (`σ = κ = ϑ = 1`): **neither constraint implies the other for
model-feasible policies.** A spike rate `i₀ = 1000`, then `1`, is pathwise feasible but violates
Woodford's constraint; a rate `i₀ = −1/100`, then `1`, satisfies Woodford's constraint but
violates the bound. -/
theorem neither_in_model :
    (spikePol 1 1 1 1000 ∈ Cset (99 / 100) 1 1 ∧
      (∀ t, 0 ≤ rateLin 1 (natRate 1 1 0) (spikePol 1 1 1 1000) t) ∧
      ¬ (mom2 (99 / 100) 1 (natRate 1 1 0) (spikePol 1 1 1 1000) ≤
        bigK 2.26 * mom1 (99 / 100) 1 (natRate 1 1 0) (spikePol 1 1 1 1000) ^ 2)) ∧
    (spikePol 1 1 1 (-1 / 100) ∈ Cset (99 / 100) 1 1 ∧
      ¬ (∀ t, 0 ≤ rateLin 1 (natRate 1 1 0) (spikePol 1 1 1 (-1 / 100)) t) ∧
      0 ≤ mom1 (99 / 100) 1 (natRate 1 1 0) (spikePol 1 1 1 (-1 / 100)) ∧
      mom2 (99 / 100) 1 (natRate 1 1 0) (spikePol 1 1 1 (-1 / 100)) ≤
        bigK 2.26 * mom1 (99 / 100) 1 (natRate 1 1 0) (spikePol 1 1 1 (-1 / 100)) ^ 2) := by
  obtain ⟨hA, hrA⟩ := spikePol_spec (β := 99 / 100) (κ := 1) (ϑ := 1) (ρ := 1) (η := 1)
    (c := 1000) one_ne_zero
  obtain ⟨hB, hrB⟩ := spikePol_spec (β := 99 / 100) (κ := 1) (ϑ := 1) (ρ := 1) (η := 1)
    (c := -1 / 100) one_ne_zero
  obtain ⟨mA1, mA2⟩ := spike_moments (κ := 1) (ρ := 1) (η := 1) (c := 1000)
    (by norm_num : (0 : ℝ) ≤ 99 / 100) (by norm_num) one_ne_zero
  obtain ⟨mB1, mB2⟩ := spike_moments (κ := 1) (ρ := 1) (η := 1) (c := -1 / 100)
    (by norm_num : (0 : ℝ) ≤ 99 / 100) (by norm_num) one_ne_zero
  have hK : bigK 2.26 = 15269 / 12769 := by unfold bigK; norm_num
  refine ⟨⟨hA, fun t => ?_, ?_⟩, ⟨hB, fun h => ?_, ?_, ?_⟩⟩
  · rw [hrA t]; split_ifs <;> norm_num
  · rw [mA1, mA2, hK]; norm_num
  · have := h 0
    rw [hrB 0] at this
    norm_num at this
  · rw [mB1]; norm_num
  · rw [mB1, mB2, hK]; norm_num

/-! ## Uniqueness of the moment-constrained optimum -/

/-- Woodford (2003), (4.19), p. 428 (the constraint set is convex: `√Ê[i²] ≤ √K Ê[i]` is a
second-order cone): if `∑βᵗu_t² ≤ K a²` and `∑βᵗv_t² ≤ K b²` with `a, b ≥ 0`, then
`∑βᵗ((u_t + v_t)/2)² ≤ K((a + b)/2)²`. -/
theorem soc_mid {β K a b : ℝ} (hβ : 0 < β) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {u v : ℕ → ℝ} (hu : Summable fun t => β ^ t * u t ^ 2)
    (hv : Summable fun t => β ^ t * v t ^ 2) (hA : ∑' t, β ^ t * u t ^ 2 ≤ K * a ^ 2)
    (hB : ∑' t, β ^ t * v t ^ 2 ≤ K * b ^ 2) :
    ∑' t, β ^ t * ((u t + v t) / 2) ^ 2 ≤ K * ((a + b) / 2) ^ 2 := by
  have hA0 : 0 ≤ ∑' t, β ^ t * u t ^ 2 := tsum_nonneg fun t => by positivity
  have hB0 : 0 ≤ ∑' t, β ^ t * v t ^ 2 := tsum_nonneg fun t => by positivity
  have hzero : ∀ {w : ℕ → ℝ}, Summable (fun t => β ^ t * w t ^ 2) →
      ∑' t, β ^ t * w t ^ 2 ≤ 0 → ∀ t, w t = 0 := fun {w} hw h t => by
    have := eq_zero_of_tsum_nonpos (fun t => by positivity) hw h t
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (pow_pos hβ t).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · -- both positive: weights `λ = b/a`
      have hpt : ∀ t, β ^ t * ((u t + v t) / 2) ^ 2 ≤
          ((1 + b / a) * (β ^ t * u t ^ 2) + (1 + a / b) * (β ^ t * v t ^ 2)) / 4 := by
        intro t
        have hbt : 0 ≤ β ^ t := pow_nonneg hβ.le t
        have key : 2 * (u t * v t) ≤ b / a * u t ^ 2 + a / b * v t ^ 2 := by
          have : 0 ≤ (b / a) * (u t - a / b * v t) ^ 2 := by positivity
          have e : (b / a) * (u t - a / b * v t) ^ 2 =
              b / a * u t ^ 2 + a / b * v t ^ 2 - 2 * (u t * v t) := by
            field_simp; ring
          linarith
        have : ((u t + v t) / 2) ^ 2 ≤
            ((1 + b / a) * u t ^ 2 + (1 + a / b) * v t ^ 2) / 4 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this hbt]
      have hs : Summable fun t => β ^ t * ((u t + v t) / 2) ^ 2 :=
        Summable.of_nonneg_of_le (fun t => by positivity) hpt
          (((hu.mul_left _).add (hv.mul_left _)).div_const 4)
      calc ∑' t, β ^ t * ((u t + v t) / 2) ^ 2
          ≤ ∑' t, ((1 + b / a) * (β ^ t * u t ^ 2) + (1 + a / b) * (β ^ t * v t ^ 2)) / 4 :=
            hs.tsum_le_tsum hpt (((hu.mul_left _).add (hv.mul_left _)).div_const 4)
        _ = ((1 + b / a) * ∑' t, β ^ t * u t ^ 2 + (1 + a / b) * ∑' t, β ^ t * v t ^ 2) / 4 := by
            rw [tsum_div_const, (hu.mul_left _).tsum_add (hv.mul_left _), tsum_mul_left,
              tsum_mul_left]
        _ ≤ ((1 + b / a) * (K * a ^ 2) + (1 + a / b) * (K * b ^ 2)) / 4 := by
            have h1 : 0 ≤ 1 + b / a := by positivity
            have h2 : 0 ≤ 1 + a / b := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hA h1, mul_le_mul_of_nonneg_left hB h2]
        _ = K * ((a + b) / 2) ^ 2 := by field_simp; ring
    · -- `b = 0`
      subst hb'
      have hv0 := hzero hv (by nlinarith)
      have e : (fun t => β ^ t * ((u t + v t) / 2) ^ 2) = fun t => (β ^ t * u t ^ 2) / 4 := by
        funext t; rw [hv0 t]; ring
      rw [e, tsum_div_const]
      nlinarith
  · -- `a = 0`
    subst ha'
    have hu0 := hzero hu (by nlinarith)
    have e : (fun t => β ^ t * ((u t + v t) / 2) ^ 2) = fun t => (β ^ t * v t ^ 2) / 4 := by
      funext t; rw [hu0 t]; ring
    rw [e, tsum_div_const]
    nlinarith

/-- Woodford (2003), Proposition 6.9, p. 428 (the optimal policy is well defined): in the common
model the moment-constrained optimum is unique (any `K`, `0 < β < 1`, `ϑ > 0`, bounded natural
rate): the constraint set is convex (`soc_mid`) and the loss strictly convex. -/
theorem momOpt_unique {β κ ϑ σ K : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {rn : ℕ → ℝ} (hrn : ∃ M, ∀ t, |rn t| ≤ M) {w1 w2 : Pol}
    (h1 : IsConstrOpt (Cset β κ ϑ) (Lfun β ϑ) (mom1 β σ rn) (mom2 β σ rn) K w1)
    (h2 : IsConstrOpt (Cset β κ ϑ) (Lfun β ϑ) (mom1 β σ rn) (mom2 β σ rn) K w2) :
    w1 = w2 := by
  obtain ⟨⟨hw1, a1, b1⟩, o1⟩ := h1
  obtain ⟨⟨hw2, a2, b2⟩, o2⟩ := h2
  have hC := cset_convex (κ := κ) hβ.le hϑ.le
  set w : Pol := (1 / 2 : ℝ) • w1 + (1 / 2 : ℝ) • w2 with hwd
  have hw : w ∈ Cset β κ ϑ := hC hw1 hw2 (by norm_num) (by norm_num) (by norm_num)
  have hm1 : mom1 β σ rn w = (mom1 β σ rn w1 + mom1 β σ rn w2) / 2 := by
    rw [hwd, mom1_comb hβ hβ1 hϑ hrn hw1 hw2]; ring
  have hβ1' : 0 < 1 - β := by linarith
  -- feasibility of the midpoint
  have hm2 : mom2 β σ rn w ≤ K * mom1 β σ rn w ^ 2 := by
    have hu := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn hw1
    have hv := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn hw2
    have hA : ∑' t, β ^ t * rateLin σ rn w1 t ^ 2 ≤ K / (1 - β) * mom1 β σ rn w1 ^ 2 := by
      unfold mom2 at b1
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ1']
      linarith
    have hB : ∑' t, β ^ t * rateLin σ rn w2 t ^ 2 ≤ K / (1 - β) * mom1 β σ rn w2 ^ 2 := by
      unfold mom2 at b2
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ1']
      linarith
    have := soc_mid hβ a1 a2 hu hv hA hB
    have e : ∀ t, rateLin σ rn w t = (rateLin σ rn w1 t + rateLin σ rn w2 t) / 2 := fun t => by
      simp only [hwd, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    unfold mom2
    simp only [e]
    rw [hm1]
    have := mul_le_mul_of_nonneg_left this hβ1'.le
    rw [show (1 - β) * (K / (1 - β) * ((mom1 β σ rn w1 + mom1 β σ rn w2) / 2) ^ 2) =
      K * ((mom1 β σ rn w1 + mom1 β σ rn w2) / 2) ^ 2 by field_simp] at this
    exact this
  have hfw : Feasible (Cset β κ ϑ) (mom1 β σ rn) (mom2 β σ rn) K w :=
    ⟨hw, by rw [hm1]; linarith, hm2⟩
  -- strict convexity of the loss
  have c1 := hw1.1
  have hs1 := hw1.2.2
  have c2 := hw2.1
  have hs2 := hw2.2.2
  set D : ℕ → ℝ := fun t => β ^ t * ((w1.2.1 t - w2.2.1 t) ^ 2 + ϑ * (w1.1 t - w2.1 t) ^ 2)
    with hDdef
  have hD0 : ∀ t, 0 ≤ D t := fun t => by simp only [hDdef]; positivity
  have hDs : Summable D := by
    refine Summable.of_nonneg_of_le hD0 (fun t => ?_) ((hs1.add hs2).mul_left 2)
    simp only [hDdef, lossTerm]
    have hp : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have : (w1.2.1 t - w2.2.1 t) ^ 2 + ϑ * (w1.1 t - w2.1 t) ^ 2 ≤
        2 * ((w1.2.1 t ^ 2 + ϑ * w1.1 t ^ 2) + (w2.2.1 t ^ 2 + ϑ * w2.1 t ^ 2)) := by
      nlinarith [sq_nonneg (w1.2.1 t + w2.2.1 t), sq_nonneg (w1.1 t + w2.1 t)]
    nlinarith
  have hterm : ∀ t, lossTerm β ϑ w.1 w.2.1 t =
      (lossTerm β ϑ w1.1 w1.2.1 t + lossTerm β ϑ w2.1 w2.2.1 t) / 2 - D t / 4 := by
    intro t
    simp only [hwd, lossTerm, hDdef, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hlm : Lfun β ϑ w = (Lfun β ϑ w1 + Lfun β ϑ w2) / 2 - (∑' t, D t) / 4 := by
    unfold Lfun loss
    rw [show lossTerm β ϑ w.1 w.2.1 = fun t =>
      (lossTerm β ϑ w1.1 w1.2.1 t + lossTerm β ϑ w2.1 w2.2.1 t) / 2 - D t / 4 from funext hterm]
    rw [((hs1.add hs2).div_const 2).tsum_sub (hDs.div_const 4), tsum_div_const,
      tsum_div_const, hs1.tsum_add hs2]
  have l12 := o1 w2 ⟨hw2, a2, b2⟩
  have l21 := o2 w1 ⟨hw1, a1, b1⟩
  have l1m := o1 w hfw
  have hz := eq_zero_of_tsum_nonpos hD0 hDs (by linarith)
  have hx : w1.1 = w2.1 := funext fun t => by
    have := (sq_terms_zero hβ hϑ t (hz t)).2; linarith
  have hπ : w1.2.1 = w2.2.1 := funext fun t => by
    have := (sq_terms_zero hβ hϑ t (hz t)).1; linarith
  exact Prod.ext hx (Prod.ext hπ (c1.trans c2.symm))

end Cochrane.ZeroBound.TidyR6CommonModel
