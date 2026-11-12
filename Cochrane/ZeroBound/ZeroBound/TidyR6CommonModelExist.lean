/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.TidyR6CommonModel

/-!
# Existence of Woodford's moment-constrained optimum in the common model

Cochrane (2023), Chapter 20, §20.2.4, p. 479, with Woodford (2003), Chapter 6, §4.2,
Proposition 6.9, p. 428. Woodford's proposition takes the constrained optimum as given; in the
common model of `TidyR6CommonModel` it exists whenever the moment constraints can be met, and it
is unique (`TidyR6CommonModel.momOpt_unique`).

The proof codes paths in the Hilbert space `ℓ²(ℕ ⊕ ℕ)` of `LiftoffStructure` (the loss is the
squared norm, `LiftoffStructure.loss_dec`). The scaled interest rate `√βᵗ i_t` of a coded path is
an affine, Lipschitz map into `ℓ²(ℕ)` (`scaledRate`, `scaledRate_lipschitz`), so
`Ê[i²] = (1 − β)‖√βᵗi‖²` and `Ê[i] = (1 − β)⟪√βᵗ, √βᵗi⟫` are continuous (`mom2_code`,
`mom1_code`); the constraint `√Ê[i²] ≤ √K Ê[i]` is a second-order cone, so the feasible codes
form a closed convex set (`soc_comb`, `wset_closed`, `wset_convex`); the minimal-norm element is
the optimum (`momOpt_exists`, `momOpt_exists_iff`). At Woodford's calibration in the trap of
§20.2.2 (`t_Z = 0`) a feasible policy exists as soon as `Kβ ≥ 1`, so the optimum exists and is
unique (`momOpt_existsUnique_trap`).
-/

namespace Cochrane.ZeroBound.TidyR6CommonModelExist

open Filter Topology
open Cochrane.ZeroBound Cochrane.ZeroBound.LinksGaliWoodford Cochrane.ZeroBound.TidyR6WoodfordZLB
open Cochrane.ZeroBound.TidyR6CommonModel
open Cochrane.ZeroBound.LiftoffStructure (PathSpace decX decP enc decX_enc decP_enc loss_dec
  memℓp_enc coord_continuous sqrt_pow_sq)

/-! ## The second-order cone -/

/-- Woodford (2003), (4.19), p. 428: the moment constraint is a second-order cone. If
`∑βᵗu_t² ≤ K a²` and `∑βᵗv_t² ≤ K b²` with `a, b ≥ 0`, then for `α, γ ≥ 0`
`∑βᵗ(αu_t + γv_t)² ≤ K(αa + γb)²`. -/
theorem soc_comb {β K a b α γ : ℝ} (hβ : 0 < β) (ha : 0 ≤ a) (hb : 0 ≤ b) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) {u v : ℕ → ℝ} (hu : Summable fun t => β ^ t * u t ^ 2)
    (hv : Summable fun t => β ^ t * v t ^ 2) (hA : ∑' t, β ^ t * u t ^ 2 ≤ K * a ^ 2)
    (hB : ∑' t, β ^ t * v t ^ 2 ≤ K * b ^ 2) :
    ∑' t, β ^ t * (α * u t + γ * v t) ^ 2 ≤ K * (α * a + γ * b) ^ 2 := by
  have hzero : ∀ {w : ℕ → ℝ}, Summable (fun t => β ^ t * w t ^ 2) →
      ∑' t, β ^ t * w t ^ 2 ≤ 0 → ∀ t, w t = 0 := fun {w} hw h t => by
    have := eq_zero_of_tsum_nonpos (fun t => by positivity) hw h t
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (pow_pos hβ t).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  have hA0 : 0 ≤ ∑' t, β ^ t * u t ^ 2 := tsum_nonneg fun t => by positivity
  have hB0 : 0 ≤ ∑' t, β ^ t * v t ^ 2 := tsum_nonneg fun t => by positivity
  -- the degenerate cases: one of the two terms vanishes identically
  have hone : ∀ {w : ℕ → ℝ} {c d : ℝ}, Summable (fun t => β ^ t * w t ^ 2) →
      ∑' t, β ^ t * w t ^ 2 ≤ K * d ^ 2 →
      ∑' t, β ^ t * (c * w t) ^ 2 ≤ K * (c * d) ^ 2 := fun {w c d} hw h => by
    have e : (fun t => β ^ t * (c * w t) ^ 2) = fun t => c ^ 2 * (β ^ t * w t ^ 2) := by
      funext t; ring
    rw [e, tsum_mul_left]
    nlinarith [sq_nonneg c]
  by_cases h1 : α * a = 0
  · have hu0 : ∀ t, α * u t = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · intro t; rw [h, zero_mul]
      · subst h
        have := hzero hu (by nlinarith)
        intro t; rw [this t, mul_zero]
    have e : (fun t => β ^ t * (α * u t + γ * v t) ^ 2) = fun t => β ^ t * (γ * v t) ^ 2 := by
      funext t; rw [hu0 t, zero_add]
    rw [e, h1, zero_add]
    exact hone hv hB
  by_cases h2 : γ * b = 0
  · have hv0 : ∀ t, γ * v t = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · intro t; rw [h, zero_mul]
      · subst h
        have := hzero hv (by nlinarith)
        intro t; rw [this t, mul_zero]
    have e : (fun t => β ^ t * (α * u t + γ * v t) ^ 2) = fun t => β ^ t * (α * u t) ^ 2 := by
      funext t; rw [hv0 t, add_zero]
    rw [e, h2, add_zero]
    exact hone hu hA
  have hP : 0 < α * a := lt_of_le_of_ne (mul_nonneg hα ha) (Ne.symm h1)
  have hQ : 0 < γ * b := lt_of_le_of_ne (mul_nonneg hγ hb) (Ne.symm h2)
  set l := γ * b / (α * a) with hl
  have hl0 : 0 < l := div_pos hQ hP
  have hpt : ∀ t, β ^ t * (α * u t + γ * v t) ^ 2 ≤
      (1 + l) * α ^ 2 * (β ^ t * u t ^ 2) + (1 + 1 / l) * γ ^ 2 * (β ^ t * v t ^ 2) := by
    intro t
    have hbt : 0 ≤ β ^ t := pow_nonneg hβ.le t
    have key : 2 * (α * u t) * (γ * v t) ≤ l * (α * u t) ^ 2 + 1 / l * (γ * v t) ^ 2 := by
      have : 0 ≤ l * (α * u t - 1 / l * (γ * v t)) ^ 2 := by positivity
      have e : l * (α * u t - 1 / l * (γ * v t)) ^ 2 =
          l * (α * u t) ^ 2 + 1 / l * (γ * v t) ^ 2 - 2 * (α * u t) * (γ * v t) := by
        field_simp; ring
      linarith
    have : (α * u t + γ * v t) ^ 2 ≤ (1 + l) * α ^ 2 * u t ^ 2 + (1 + 1 / l) * γ ^ 2 * v t ^ 2 := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hbt]
  have hsR : Summable fun t =>
      (1 + l) * α ^ 2 * (β ^ t * u t ^ 2) + (1 + 1 / l) * γ ^ 2 * (β ^ t * v t ^ 2) :=
    (hu.mul_left _).add (hv.mul_left _)
  have hs : Summable fun t => β ^ t * (α * u t + γ * v t) ^ 2 :=
    Summable.of_nonneg_of_le (fun t => by positivity) hpt hsR
  calc ∑' t, β ^ t * (α * u t + γ * v t) ^ 2
      ≤ ∑' t, ((1 + l) * α ^ 2 * (β ^ t * u t ^ 2) + (1 + 1 / l) * γ ^ 2 * (β ^ t * v t ^ 2)) :=
        hs.tsum_le_tsum hpt hsR
    _ = (1 + l) * α ^ 2 * ∑' t, β ^ t * u t ^ 2 + (1 + 1 / l) * γ ^ 2 * ∑' t, β ^ t * v t ^ 2 := by
        rw [(hu.mul_left _).tsum_add (hv.mul_left _), tsum_mul_left, tsum_mul_left]
    _ ≤ (1 + l) * α ^ 2 * (K * a ^ 2) + (1 + 1 / l) * γ ^ 2 * (K * b ^ 2) := by
        have c1 : 0 ≤ (1 + l) * α ^ 2 := by positivity
        have c2 : 0 ≤ (1 + 1 / l) * γ ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hA c1, mul_le_mul_of_nonneg_left hB c2]
    _ = K * (α * a + γ * b) ^ 2 := by
        have hαn : α ≠ 0 := by rintro rfl; simp at hP
        have han : a ≠ 0 := by rintro rfl; simp at hP
        have hγn : γ ≠ 0 := by rintro rfl; simp at hQ
        have hbn : b ≠ 0 := by rintro rfl; simp at hQ
        rw [hl]
        field_simp
        ring

/-! ## Coded paths and their interest rates -/

/-- Galí (2015), p. 148, with Cochrane (2023), §20.2.4: the policy decoded from `z ∈ ℓ²(ℕ ⊕ ℕ)`,
`(decX z, decP z, 1)`. -/
noncomputable def decPol (β ϑ : ℝ) (z : ℕ ⊕ ℕ → ℝ) : Pol := (decX β ϑ z, decP β z, 1)

/-- Woodford (2003), (4.19), p. 428: the scaled interest rate `√βᵗ i_t` of a coded path. -/
noncomputable def srate (β ϑ σ : ℝ) (rn : ℕ → ℝ) (z : ℕ ⊕ ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.sqrt β ^ t * rateLin σ rn (decPol β ϑ z) t

/-- Woodford (2003), (4.19): the scaled rate in code coordinates,
`√βᵗi_t = √βᵗ rⁿ_t + z(inl(t+1))/√β + σ z(inr(t+1))/(√β√ϑ) − σ z(inr t)/√ϑ`. -/
theorem srate_eq {β ϑ σ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (rn : ℕ → ℝ) (z : ℕ ⊕ ℕ → ℝ) (t : ℕ) :
    srate β ϑ σ rn z t = Real.sqrt β ^ t * rn t + z (Sum.inl (t + 1)) / Real.sqrt β +
      σ * z (Sum.inr (t + 1)) / (Real.sqrt β * Real.sqrt ϑ) - σ * z (Sum.inr t) / Real.sqrt ϑ := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hs2 : 0 < Real.sqrt ϑ := Real.sqrt_pos.mpr hϑ
  have hp : Real.sqrt β ^ t ≠ 0 := pow_ne_zero _ hs.ne'
  simp only [srate, rateLin, LinearMap.coe_mk, AddHom.coe_mk, decPol, decX, decP, one_mul,
    pow_succ]
  field_simp
  ring

/-- Woodford (2003), (4.19): differences of scaled rates are bounded by the code distance,
`(√βᵗ(i_t − i'_t))² ≤ C(d(inl(t+1))² + d(inr(t+1))² + d(inr t)²)`, `d = z − z'`. -/
theorem srate_sub_sq {β ϑ σ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (rn : ℕ → ℝ) (z z' : ℕ ⊕ ℕ → ℝ)
    (t : ℕ) :
    (srate β ϑ σ rn z t - srate β ϑ σ rn z' t) ^ 2 ≤
      3 * (1 / β + σ ^ 2 / (β * ϑ) + σ ^ 2 / ϑ) *
        ((z (Sum.inl (t + 1)) - z' (Sum.inl (t + 1))) ^ 2 +
          (z (Sum.inr (t + 1)) - z' (Sum.inr (t + 1))) ^ 2 +
          (z (Sum.inr t) - z' (Sum.inr t)) ^ 2) := by
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hs2 : 0 < Real.sqrt ϑ := Real.sqrt_pos.mpr hϑ
  set A := z (Sum.inl (t + 1)) - z' (Sum.inl (t + 1))
  set B := z (Sum.inr (t + 1)) - z' (Sum.inr (t + 1))
  set C := z (Sum.inr t) - z' (Sum.inr t)
  have e : srate β ϑ σ rn z t - srate β ϑ σ rn z' t =
      A / Real.sqrt β + σ * B / (Real.sqrt β * Real.sqrt ϑ) - σ * C / Real.sqrt ϑ := by
    rw [srate_eq hβ hϑ, srate_eq hβ hϑ]
    simp only [A, B, C]
    field_simp
    ring
  rw [e]
  set a := A / Real.sqrt β
  set b := σ * B / (Real.sqrt β * Real.sqrt ϑ)
  set c := σ * C / Real.sqrt ϑ
  have h3 : (a + b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + c), sq_nonneg (b + c)]
  have ea : a ^ 2 = 1 / β * A ^ 2 := by
    simp only [a]; rw [div_pow, Real.sq_sqrt hβ.le]; ring
  have eb : b ^ 2 = σ ^ 2 / (β * ϑ) * B ^ 2 := by
    simp only [b]; rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hβ.le, Real.sq_sqrt hϑ.le]; ring
  have ec : c ^ 2 = σ ^ 2 / ϑ * C ^ 2 := by
    simp only [c]; rw [div_pow, mul_pow, Real.sq_sqrt hϑ.le]; ring
  have k1 : 0 ≤ 1 / β := by positivity
  have k2 : 0 ≤ σ ^ 2 / (β * ϑ) := by positivity
  have k3 : 0 ≤ σ ^ 2 / ϑ := by positivity
  rw [ea, eb, ec] at h3
  nlinarith [mul_nonneg k1 (sq_nonneg B), mul_nonneg k1 (sq_nonneg C),
    mul_nonneg k2 (sq_nonneg A), mul_nonneg k2 (sq_nonneg C), mul_nonneg k3 (sq_nonneg A),
    mul_nonneg k3 (sq_nonneg B)]

/-- Galí (2015), p. 148: the squares of an `ℓ²(ℕ ⊕ ℕ)` element, read along the shifted and
unshifted coordinates, have total at most `2‖z‖²`. -/
theorem sum_three_le (z : PathSpace) :
    Summable (fun t => z (Sum.inl (t + 1)) ^ 2 + z (Sum.inr (t + 1)) ^ 2 + z (Sum.inr t) ^ 2) ∧
      ∑' t, (z (Sum.inl (t + 1)) ^ 2 + z (Sum.inr (t + 1)) ^ 2 + z (Sum.inr t) ^ 2) ≤
        2 * ‖z‖ ^ 2 := by
  set f : ℕ ⊕ ℕ → ℝ := fun i => z i ^ 2 with hf
  have hs : Summable f := LiftoffStructure.summable_sq z
  have hl : Summable (f ∘ Sum.inl) := hs.comp_injective Sum.inl_injective
  have hr : Summable (f ∘ Sum.inr) := hs.comp_injective Sum.inr_injective
  have hl1 : Summable fun t => (f ∘ Sum.inl) (t + 1) := hl.comp_injective (add_left_injective 1)
  have hr1 : Summable fun t => (f ∘ Sum.inr) (t + 1) := hr.comp_injective (add_left_injective 1)
  have e : (fun t => z (Sum.inl (t + 1)) ^ 2 + z (Sum.inr (t + 1)) ^ 2 + z (Sum.inr t) ^ 2) =
      fun t => (f ∘ Sum.inl) (t + 1) + (f ∘ Sum.inr) (t + 1) + (f ∘ Sum.inr) t := rfl
  rw [e]
  refine ⟨(hl1.add hr1).add hr, ?_⟩
  have h3 : ∑' i, f i = ∑' t, (f ∘ Sum.inl) t + ∑' t, (f ∘ Sum.inr) t := Summable.tsum_sum hl hr
  have hn : ‖z‖ ^ 2 = ∑' i, f i := LiftoffStructure.norm_sq_eq z
  rw [(hl1.add hr1).tsum_add hr, hl1.tsum_add hr1, hn, h3]
  have a1 : ∑' t, (f ∘ Sum.inl) (t + 1) ≤ ∑' t, (f ∘ Sum.inl) t := by
    rw [hl.tsum_eq_zero_add]
    have : 0 ≤ (f ∘ Sum.inl) 0 := sq_nonneg _
    linarith
  have a2 : ∑' t, (f ∘ Sum.inr) (t + 1) ≤ ∑' t, (f ∘ Sum.inr) t := by
    rw [hr.tsum_eq_zero_add]
    have : 0 ≤ (f ∘ Sum.inr) 0 := sq_nonneg _
    linarith
  have a3 : 0 ≤ ∑' t, (f ∘ Sum.inl) t := tsum_nonneg fun t => sq_nonneg _
  linarith

/-- Woodford (2003), (4.19): `ℓ²(ℕ)`, the space of scaled interest-rate paths. -/
abbrev Seq2 : Type := lp (fun _ : ℕ => ℝ) 2

/-- Galí (2015), p. 148: `‖f‖² = ∑ f_t²` in `ℓ²(ℕ)`. -/
theorem seq_norm_sq (f : Seq2) : ‖f‖ ^ 2 = ∑' t, f t ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) f
  rw [show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two] at h
  rw [h]
  congr 1
  funext i
  rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-- Galí (2015), p. 148: a real sequence with summable squares is in `ℓ²(ℕ)`. -/
theorem memℓp_of_sq {f : ℕ → ℝ} (h : Summable fun t => f t ^ 2) :
    Memℓp (fun t => f t) 2 := by
  refine (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).2 ?_
  refine h.congr fun i => ?_
  rw [Real.norm_eq_abs, show (2 : ENNReal).toReal = (2 : ℝ) by norm_num, Real.rpow_two, sq_abs]

/-- Woodford (2003), (4.19): the scaled rate of a coded path has summable squares (bounded
natural rate). -/
theorem srate_sq_summable {β ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) (z : PathSpace) :
    Summable fun t => srate β ϑ σ rn z t ^ 2 := by
  obtain ⟨M, hM⟩ := hrn
  have h3 := (sum_three_le z).1
  have hg : Summable fun t : ℕ => β ^ t := summable_geometric_of_lt_one hβ.le hβ1
  have hpt : ∀ t, srate β ϑ σ rn z t ^ 2 ≤ 2 * (M ^ 2 * β ^ t) +
      2 * (3 * (1 / β + σ ^ 2 / (β * ϑ) + σ ^ 2 / ϑ) *
        (z (Sum.inl (t + 1)) ^ 2 + z (Sum.inr (t + 1)) ^ 2 + z (Sum.inr t) ^ 2)) := by
    intro t
    have h0 := srate_sub_sq (σ := σ) hβ hϑ rn z 0 t
    simp only [Pi.zero_apply, sub_zero] at h0
    have hz0 : srate β ϑ σ rn 0 t = Real.sqrt β ^ t * rn t := by
      rw [srate_eq hβ hϑ]; simp
    have hr2 : (Real.sqrt β ^ t * rn t) ^ 2 ≤ M ^ 2 * β ^ t := by
      rw [mul_pow, sqrt_pow_sq hβ.le]
      have : rn t ^ 2 ≤ M ^ 2 := by
        have := hM t
        nlinarith [abs_nonneg (rn t), sq_abs (rn t)]
      nlinarith [pow_pos hβ t]
    rw [hz0] at h0
    have := sq_add_le (srate β ϑ σ rn z t - Real.sqrt β ^ t * rn t) (Real.sqrt β ^ t * rn t)
    rw [sub_add_cancel] at this
    linarith
  exact Summable.of_nonneg_of_le (fun t => sq_nonneg _) hpt
    ((hg.mul_left _).mul_left 2 |>.add ((h3.mul_left _).mul_left 2))

/-- Woodford (2003), (4.19): the scaled interest-rate path of a code, as an element of
`ℓ²(ℕ)`. -/
noncomputable def scaledRate {β ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) (z : PathSpace) : Seq2 :=
  ⟨fun t => srate β ϑ σ rn z t, memℓp_of_sq (srate_sq_summable hβ hβ1 hϑ hrn z)⟩

/-- Woodford (2003), (4.19): the scaled interest rate is Lipschitz in the code. -/
theorem scaledRate_lipschitz {β ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) :
    LipschitzWith (Real.toNNReal (Real.sqrt (6 * (1 / β + σ ^ 2 / (β * ϑ) + σ ^ 2 / ϑ))))
      (scaledRate (σ := σ) hβ hβ1 hϑ hrn) := by
  set C := 3 * (1 / β + σ ^ 2 / (β * ϑ) + σ ^ 2 / ϑ) with hC
  have hC0 : 0 ≤ C := by positivity
  refine LipschitzWith.of_dist_le_mul fun z z' => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  have hsq : ‖scaledRate (σ := σ) hβ hβ1 hϑ hrn z - scaledRate (σ := σ) hβ hβ1 hϑ hrn z'‖ ^ 2 ≤
      2 * C * ‖z - z'‖ ^ 2 := by
    rw [seq_norm_sq]
    obtain ⟨h3s, h3⟩ := sum_three_le (z - z')
    have hpt : ∀ t, (scaledRate (σ := σ) hβ hβ1 hϑ hrn z -
        scaledRate (σ := σ) hβ hβ1 hϑ hrn z') t ^ 2 ≤
        C * ((z - z') (Sum.inl (t + 1)) ^ 2 + (z - z') (Sum.inr (t + 1)) ^ 2 +
          (z - z') (Sum.inr t) ^ 2) := by
      intro t
      simp only [lp.coeFn_sub, Pi.sub_apply, scaledRate]
      exact srate_sub_sq hβ hϑ rn z z' t
    have hsum : Summable fun t =>
        (scaledRate (σ := σ) hβ hβ1 hϑ hrn z - scaledRate (σ := σ) hβ hβ1 hϑ hrn z') t ^ 2 :=
      Summable.of_nonneg_of_le (fun t => sq_nonneg _) hpt (h3s.mul_left C)
    calc ∑' t, (scaledRate (σ := σ) hβ hβ1 hϑ hrn z - scaledRate (σ := σ) hβ hβ1 hϑ hrn z') t ^ 2
        ≤ ∑' t, C * ((z - z') (Sum.inl (t + 1)) ^ 2 + (z - z') (Sum.inr (t + 1)) ^ 2 +
          (z - z') (Sum.inr t) ^ 2) := hsum.tsum_le_tsum hpt (h3s.mul_left C)
      _ ≤ C * (2 * ‖z - z'‖ ^ 2) := by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left h3 hC0
      _ = 2 * C * ‖z - z'‖ ^ 2 := by ring
  have h6 : 6 * (1 / β + σ ^ 2 / (β * ϑ) + σ ^ 2 / ϑ) = 2 * C := by rw [hC]; ring
  rw [h6]
  calc ‖scaledRate (σ := σ) hβ hβ1 hϑ hrn z - scaledRate (σ := σ) hβ hβ1 hϑ hrn z'‖
      = Real.sqrt (‖scaledRate (σ := σ) hβ hβ1 hϑ hrn z -
          scaledRate (σ := σ) hβ hβ1 hϑ hrn z'‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * C * ‖z - z'‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (2 * C) * ‖z - z'‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- Woodford (2003), (4.19), p. 428: `Ê[i²] = (1 − β)‖√βᵗ i‖²` for a coded path. -/
theorem mom2_code {β ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) (z : PathSpace) :
    mom2 β σ rn (decPol β ϑ z) = (1 - β) * ‖scaledRate (σ := σ) hβ hβ1 hϑ hrn z‖ ^ 2 := by
  rw [seq_norm_sq]
  unfold mom2
  congr 1
  refine tsum_congr fun t => ?_
  simp only [scaledRate, srate]
  rw [mul_pow, sqrt_pow_sq hβ.le]

/-- Woodford (2003), (4.18): the weights `√βᵗ`, an element of `ℓ²(ℕ)`. -/
noncomputable def sqrtWeights {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) : Seq2 :=
  ⟨fun t => Real.sqrt β ^ t, memℓp_of_sq (by
    simp only [sqrt_pow_sq hβ.le]; exact summable_geometric_of_lt_one hβ.le hβ1)⟩

/-- Woodford (2003), (4.18), p. 428: `Ê[i] = (1 − β)⟪√βᵗ, √βᵗ i⟫` for a coded path. -/
theorem mom1_code {β ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) (z : PathSpace) :
    mom1 β σ rn (decPol β ϑ z) =
      (1 - β) * inner ℝ (sqrtWeights hβ hβ1) (scaledRate (σ := σ) hβ hβ1 hϑ hrn z) := by
  rw [lp.inner_eq_tsum]
  unfold mom1
  congr 1
  refine tsum_congr fun t => ?_
  simp only [scaledRate, srate, sqrtWeights, Real.inner_apply]
  rw [← mul_assoc, ← mul_pow, Real.mul_self_sqrt hβ.le]

/-- Woodford (2003), (4.18)–(4.19): both moments are continuous functions of the code. -/
theorem moms_continuous {β ϑ σ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) :
    Continuous (fun z : PathSpace => mom1 β σ rn (decPol β ϑ z)) ∧
      Continuous (fun z : PathSpace => mom2 β σ rn (decPol β ϑ z)) := by
  have hV := (scaledRate_lipschitz (σ := σ) hβ hβ1 hϑ hrn).continuous
  refine ⟨?_, ?_⟩
  · simp only [mom1_code hβ hβ1 hϑ hrn]
    exact continuous_const.mul (continuous_const.inner hV)
  · simp only [mom2_code hβ hβ1 hϑ hrn]
    exact continuous_const.mul (hV.norm.pow 2)

/-! ## The feasible codes -/

/-- Woodford (2003), (4.18)–(4.19), p. 428: the codes of policies satisfying the structural
equations and Woodford's moment constraints. -/
def Wset (β κ ϑ σ K : ℝ) (rn : ℕ → ℝ) : Set PathSpace :=
  {z | (∀ t, NKPC β κ (decX β ϑ z) (decP β z) t) ∧ 0 ≤ mom1 β σ rn (decPol β ϑ z) ∧
    mom2 β σ rn (decPol β ϑ z) ≤ K * mom1 β σ rn (decPol β ϑ z) ^ 2}

/-- Galí (2015), p. 148: a decoded path with the Phillips curve is in the structural set. -/
theorem decPol_mem {β κ ϑ : ℝ} (hβ : 0 < β) (hϑ : 0 < ϑ) (z : PathSpace)
    (h : ∀ t, NKPC β κ (decX β ϑ z) (decP β z) t) : decPol β ϑ z ∈ Cset β κ ϑ :=
  ⟨rfl, h, (loss_dec hβ hϑ z).1⟩

/-- Woodford (2003), (4.18)–(4.19): the feasible codes are closed. -/
theorem wset_closed {β κ ϑ σ K : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ) {rn : ℕ → ℝ}
    (hrn : ∃ M, ∀ t, |rn t| ≤ M) : IsClosed (Wset β κ ϑ σ K rn) := by
  obtain ⟨h1, h2⟩ := moms_continuous (σ := σ) hβ hβ1 hϑ hrn
  have hP : ∀ t, Continuous fun z : PathSpace => decP β z t := fun t => by
    simp only [decP]; exact (coord_continuous _).div_const _
  have hX : ∀ t, Continuous fun z : PathSpace => decX β ϑ z t := fun t => by
    simp only [decX]; exact (coord_continuous _).div_const _
  have e : Wset β κ ϑ σ K rn = (⋂ t, {z : PathSpace |
      decP β z t = β * decP β z (t + 1) + κ * decX β ϑ z t}) ∩
      ({z | 0 ≤ mom1 β σ rn (decPol β ϑ z)} ∩
        {z | mom2 β σ rn (decPol β ϑ z) ≤ K * mom1 β σ rn (decPol β ϑ z) ^ 2}) := by
    ext z
    simp only [Wset, NKPC, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
  rw [e]
  exact (isClosed_iInter fun t => isClosed_eq (hP t)
    (((hP _).const_mul β).add ((hX t).const_mul κ))).inter
    ((isClosed_le continuous_const h1).inter (isClosed_le h2 (continuous_const.mul (h1.pow 2))))

/-- Galí (2015), p. 149: decoding commutes with convex combinations. -/
theorem decPol_comb {β ϑ a b : ℝ} (hab : a + b = 1) (z w : PathSpace) :
    decPol β ϑ ⇑(a • z + b • w) = a • decPol β ϑ z + b • decPol β ϑ w := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext t
    simp only [decPol, decX, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Prod.fst_add, Prod.smul_fst]
    ring
  · funext t
    simp only [decPol, decP, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst]
    ring
  · simp only [decPol, Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, hab]

/-- Woodford (2003), (4.18)–(4.19): the feasible codes are convex (the second-order cone
`soc_comb`). -/
theorem wset_convex {β κ ϑ σ K : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {rn : ℕ → ℝ} (hrn : ∃ M, ∀ t, |rn t| ≤ M) : Convex ℝ (Wset β κ ϑ σ K rn) := by
  intro z hz w hw a b ha hb hab
  have hzC := decPol_mem (κ := κ) hβ hϑ z hz.1
  have hwC := decPol_mem (κ := κ) hβ hϑ w hw.1
  have hcomb := decPol_comb (β := β) (ϑ := ϑ) hab z w
  have hmemC : a • decPol β ϑ z + b • decPol β ϑ w ∈ Cset β κ ϑ :=
    cset_convex hβ.le hϑ.le hzC hwC ha hb hab
  have hm1 := mom1_comb (σ := σ) hβ hβ1 hϑ hrn hzC hwC a b
  refine ⟨?_, ?_, ?_⟩
  · intro t
    have := hmemC.2.1 t
    rw [← hcomb] at this
    exact this
  · rw [hcomb, hm1]
    exact add_nonneg (mul_nonneg ha hz.2.1) (mul_nonneg hb hw.2.1)
  · rw [hcomb, hm1]
    have hβ1' : 0 < 1 - β := by linarith
    have hu := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn hzC
    have hv := summable_rate_sq (σ := σ) hβ hβ1 hϑ hrn hwC
    have hA : ∑' t, β ^ t * rateLin σ rn (decPol β ϑ z) t ^ 2 ≤
        K / (1 - β) * mom1 β σ rn (decPol β ϑ z) ^ 2 := by
      have := hz.2.2
      unfold mom2 at this
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ1']
      linarith
    have hB : ∑' t, β ^ t * rateLin σ rn (decPol β ϑ w) t ^ 2 ≤
        K / (1 - β) * mom1 β σ rn (decPol β ϑ w) ^ 2 := by
      have := hw.2.2
      unfold mom2 at this
      rw [div_mul_eq_mul_div, le_div_iff₀ hβ1']
      linarith
    have hS := soc_comb hβ hz.2.1 hw.2.1 ha hb hu hv hA hB
    have e : ∀ t, rateLin σ rn (a • decPol β ϑ z + b • decPol β ϑ w) t =
        a * rateLin σ rn (decPol β ϑ z) t + b * rateLin σ rn (decPol β ϑ w) t := fun t => by
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    unfold mom2
    simp only [e]
    have := mul_le_mul_of_nonneg_left hS hβ1'.le
    rw [show (1 - β) * (K / (1 - β) * (a * mom1 β σ rn (decPol β ϑ z) +
      b * mom1 β σ rn (decPol β ϑ w)) ^ 2) = K * (a * mom1 β σ rn (decPol β ϑ z) +
      b * mom1 β σ rn (decPol β ϑ w)) ^ 2 by field_simp] at this
    exact this

/-! ## Existence -/

/-- Woodford (2003), Proposition 6.9, p. 428, in the common model: **the moment-constrained
optimum exists** whenever some policy of the structural set satisfies Woodford's constraints
(`0 < β < 1`, `ϑ > 0`, bounded natural rate). -/
theorem momOpt_exists {β κ ϑ σ K : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {rn : ℕ → ℝ} (hrn : ∃ M, ∀ t, |rn t| ≤ M)
    (hne : ∃ q, Feasible (Cset β κ ϑ) (mom1 β σ rn) (mom2 β σ rn) K q) :
    ∃ w, IsConstrOpt (Cset β κ ϑ) (Lfun β ϑ) (mom1 β σ rn) (mom2 β σ rn) K w := by
  -- the code of a feasible policy is a feasible code
  have hcode : ∀ q, Feasible (Cset β κ ϑ) (mom1 β σ rn) (mom2 β σ rn) K q →
      ∃ zq : PathSpace, zq ∈ Wset β κ ϑ σ K rn ∧ decPol β ϑ zq = q ∧ ‖zq‖ ^ 2 = Lfun β ϑ q := by
    intro q ⟨⟨hc, hN, hS⟩, h1, h2⟩
    refine ⟨⟨enc β ϑ q.1 q.2.1, memℓp_enc hβ hϑ hS⟩, ?_⟩
    have hdec : decPol β ϑ (enc β ϑ q.1 q.2.1) = q := by
      refine Prod.ext (decX_enc hβ hϑ _ _) (Prod.ext (decP_enc hβ ϑ _ _) hc.symm)
    have hdec' : decPol β ϑ ⇑(⟨enc β ϑ q.1 q.2.1, memℓp_enc hβ hϑ hS⟩ : PathSpace) = q := hdec
    refine ⟨⟨?_, ?_, ?_⟩, hdec', ?_⟩
    · intro t
      change NKPC β κ (decX β ϑ (enc β ϑ q.1 q.2.1)) (decP β (enc β ϑ q.1 q.2.1)) t
      rw [decX_enc hβ hϑ, decP_enc hβ]; exact hN t
    · rw [hdec']; exact h1
    · rw [hdec']; exact h2
    · have := (loss_dec hβ hϑ ⟨enc β ϑ q.1 q.2.1, memℓp_enc hβ hϑ hS⟩).2
      rw [← this]
      change loss β ϑ (decX β ϑ (enc β ϑ q.1 q.2.1)) (decP β (enc β ϑ q.1 q.2.1)) = Lfun β ϑ q
      rw [decX_enc hβ hϑ, decP_enc hβ]
      rfl
  obtain ⟨q0, hq0⟩ := hne
  obtain ⟨z0, hz0, -, -⟩ := hcode q0 hq0
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex ⟨z0, hz0⟩
    (wset_closed (κ := κ) (σ := σ) (K := K) hβ hβ1 hϑ hrn).isComplete
    (wset_convex (κ := κ) hβ hβ1 hϑ hrn) 0
  refine ⟨decPol β ϑ v, ⟨decPol_mem hβ hϑ v hvK.1, hvK.2.1, hvK.2.2⟩, fun q hq => ?_⟩
  obtain ⟨zq, hzq, -, hLq⟩ := hcode q hq
  have hle : ‖v‖ ≤ ‖zq‖ := by
    have h1 : ‖(0 : PathSpace) - v‖ ≤ ‖(0 : PathSpace) - zq‖ := by
      rw [hv]
      exact ciInf_le ⟨0, by rintro _ ⟨u, rfl⟩; exact norm_nonneg _⟩
        (⟨zq, hzq⟩ : Wset β κ ϑ σ K rn)
    simpa only [zero_sub, norm_neg] using h1
  have hLv : Lfun β ϑ (decPol β ϑ v) = ‖v‖ ^ 2 := (loss_dec hβ hϑ v).2
  rw [hLv, ← hLq]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- Woodford (2003), Proposition 6.9 in the common model: the moment-constrained optimum exists
**iff** the constraints can be met by some policy of the structural set, and it is then unique
(`TidyR6CommonModel.momOpt_unique`). -/
theorem momOpt_exists_iff {β κ ϑ σ K : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    {rn : ℕ → ℝ} (hrn : ∃ M, ∀ t, |rn t| ≤ M) :
    (∃! w, IsConstrOpt (Cset β κ ϑ) (Lfun β ϑ) (mom1 β σ rn) (mom2 β σ rn) K w) ↔
      ∃ q, Feasible (Cset β κ ϑ) (mom1 β σ rn) (mom2 β σ rn) K q := by
  constructor
  · rintro ⟨w, hw, -⟩
    exact ⟨w, hw.1⟩
  · intro hne
    obtain ⟨w, hw⟩ := momOpt_exists hβ hβ1 hϑ hrn hne
    exact ⟨w, hw, fun w' hw' => momOpt_unique hβ hβ1 hϑ hrn hw' hw⟩

/-- Cochrane (2023), §20.2.2 (the trap `rⁿ = natRate ρ η 0`), with Woodford's constraint: if
`ρ ≥ 0` and `Kβ ≥ 1`, the moment-constrained optimum of the common model exists and is unique
(the policy with rate `0` at date 0 and `ρ` afterwards is feasible). At Woodford's calibration
`β = 0.99`, `K = 1 + 2.26⁻²` the condition `Kβ ≥ 1` holds (`woodford_calibration_ok`). -/
theorem momOpt_existsUnique_trap {β κ ϑ σ K ρ η : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hϑ : 0 < ϑ)
    (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hKβ : 1 ≤ K * β) :
    ∃! w, IsConstrOpt (Cset β κ ϑ) (Lfun β ϑ) (mom1 β σ (natRate ρ η 0))
      (mom2 β σ (natRate ρ η 0)) K w := by
  have hrn : ∃ M, ∀ t, |natRate ρ η 0 t| ≤ M := ⟨|η| + |ρ|, fun t => by
    unfold natRate
    split_ifs
    · rw [abs_neg]; linarith [abs_nonneg ρ]
    · linarith [abs_nonneg η]⟩
  refine (momOpt_exists_iff hβ hβ1 hϑ hrn).mpr ⟨spikePol κ σ η 0, ?_⟩
  obtain ⟨hC, -⟩ := spikePol_spec (β := β) (κ := κ) (ϑ := ϑ) (ρ := ρ) (η := η) (c := 0) hσ.ne'
  obtain ⟨m1, m2⟩ := spike_moments (κ := κ) (ρ := ρ) (η := η) (c := 0) hβ.le hβ1 hσ.ne'
  refine ⟨hC, ?_, ?_⟩
  · rw [m1]; positivity
  · rw [m1, m2]
    have : β * ρ ^ 2 ≤ K * β * (β * ρ ^ 2) := by
      have h0 : 0 ≤ β * ρ ^ 2 := by positivity
      nlinarith
    nlinarith

/-- Woodford (2003), Table 6.1, p. 434: at `β = 0.99` and `K = 1 + 2.26⁻²`, `Kβ ≥ 1`. -/
theorem woodford_calibration_ok : (1 : ℝ) ≤ bigK 2.26 * (99 / 100) := by
  unfold bigK; norm_num

end Cochrane.ZeroBound.TidyR6CommonModelExist
