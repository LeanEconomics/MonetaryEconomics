/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyGenIFT
import StabilizationWelfare.NonlinearRotembergBoundary
import StabilizationWelfare.NonlinearRotembergRamseyMarkov

/-!
# Non-existence of the exact Rotemberg Ramsey equilibrium when `G < 0` and `−2(1+β) < κθ_R`

Woodford (2003), *Interest and Prices*, Chapter 7, (1.20), pp. 475–476, and Appendix A.3. When
`G < 0` and `−2(1 + β) < κθ_R < 0` both roots of the commitment polynomial lie outside the unit
circle (`NonlinearRotembergRamseyDegenerate.ramsey_G_neg_nonexist` for the linearisation). Here
the EXACT perfect-foresight Ramsey conditions are treated.

* **`rec_apriori`**: for `0 < β < 1` and `|s| < 1 + β`, every bounded solution of the FORCED
  recursion `βℓ_{t+2} − sℓ_{t+1} + ℓ_t = g_t` satisfies `|ℓ_t| ≤ K sup|g|` at every date,
  including `t = 0` (factorisation over `ℂ` with both roots of modulus `> 1`, `geom_apriori`).
* **`pf_forced`**: the linearised conditions with any residual `w` reduce to that recursion for
  `ℓ_t = λ̂_{t−1}`, with the other variables explicit in `(ℓ, w)`.
* **`ramsey_nonexist`**: there is `r > 0` such that every exact perfect-foresight solution with
  `‖u_t‖ ≤ r` and `|λ̂_{−1}| ≤ r` has `λ̂_{−1} = 0` and is the steady state. Hence for every
  inherited multiplier `0 < |λ̂_{−1}| ≤ r` there is NO exact equilibrium within `r` of the steady
  state.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyNonexist

open Filter Topology
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyTree (cR4 cR)
open NonlinearRotembergRamseyAE (gamb_pos)
open NonlinearRotembergRamseyDegenerate (cG cG_neg abs_root_gt lagP)
open NonlinearRotembergRamseyMarkov (Qd_congr proj norm_proj_le)
open NonlinearRotembergBoundary (small_remainder)

variable {p : Par}

/-! ## A priori bounds for recursions without a stable root -/

/-- Woodford (2003), App. A.3 (tool): if `|v_{t+1} − z v_t| ≤ G` and `|v_t| ≤ V` at every date
with `‖z‖ > 1`, then `‖v_t‖ ≤ G/(‖z‖ − 1)`. -/
theorem geom_apriori {z : ℂ} (hz : 1 < ‖z‖) {v : ℕ → ℂ} {V G : ℝ} (hV : ∀ t, ‖v t‖ ≤ V)
    (hG : ∀ t, ‖v (t + 1) - z * v t‖ ≤ G) (t : ℕ) : ‖v t‖ ≤ G / (‖z‖ - 1) := by
  have hz0 : 0 < ‖z‖ := by linarith
  have hz1 : 0 < ‖z‖ - 1 := by linarith
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
  have hn : ∀ n : ℕ, ∀ t, ‖v t‖ ≤ G / (‖z‖ - 1) + V / ‖z‖ ^ n := by
    intro n
    induction n with
    | zero => intro t; have : 0 ≤ G / (‖z‖ - 1) := by positivity
              simp only [pow_zero, div_one]; linarith [hV t]
    | succ n ih =>
      intro t
      have h1 : ‖z‖ * ‖v t‖ ≤ ‖v (t + 1)‖ + G := by
        rw [← norm_mul]
        calc ‖z * v t‖ = ‖v (t + 1) - (v (t + 1) - z * v t)‖ := by ring_nf
          _ ≤ ‖v (t + 1)‖ + ‖v (t + 1) - z * v t‖ := norm_sub_le _ _
          _ ≤ _ := by linarith [hG t]
      have h2 := ih (t + 1)
      have h1' : ‖v t‖ ≤ (‖v (t + 1)‖ + G) / ‖z‖ := by rw [le_div_iff₀ hz0]; linarith
      calc ‖v t‖ ≤ (‖v (t + 1)‖ + G) / ‖z‖ := h1'
        _ ≤ (G / (‖z‖ - 1) + V / ‖z‖ ^ n + G) / ‖z‖ := by gcongr
        _ = G / (‖z‖ - 1) + V / ‖z‖ ^ (n + 1) := by field_simp; ring
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV 0)
  have ht : Tendsto (fun n : ℕ => G / (‖z‖ - 1) + V / ‖z‖ ^ n) atTop
      (𝓝 (G / (‖z‖ - 1) + 0)) := by
    refine tendsto_const_nhds.add ?_
    simpa using (tendsto_const_nhds (x := V)).div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt hz)
  rw [add_zero] at ht
  exact ge_of_tendsto' ht fun n => hn n t

/-- Woodford (2003), Ch. 7, (1.20) (**both roots outside the unit circle**): if `0 < β < 1` and
`|s| < 1 + β`, there are `z₁, z₂ ∈ ℂ` with `βz₁z₂ = 1`, `β(z₁ + z₂) = s`, `‖z₁‖, ‖z₂‖ > 1`. -/
theorem roots_out {β s : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hs : |s| < 1 + β) :
    ∃ z1 z2 : ℂ, (β : ℂ) * z1 * z2 = 1 ∧ (β : ℂ) * (z1 + z2) = s ∧ 1 < ‖z1‖ ∧ 1 < ‖z2‖ := by
  rcases le_or_gt (4 * β) (s ^ 2) with hD | hD
  · set D := Real.sqrt (s ^ 2 - 4 * β)
    have hD2 : D ^ 2 = s ^ 2 - 4 * β := Real.sq_sqrt (by linarith)
    set a := (s - D) / (2 * β)
    set b := (s + D) / (2 * β)
    have h1 : β * a * b = 1 := by simp only [a, b]; field_simp; linear_combination -hD2
    have h2 : β * (a + b) = s := by simp only [a, b]; field_simp; ring
    have ra : β * a ^ 2 - s * a + 1 = 0 := by simp only [a]; field_simp; linear_combination hD2
    have rb : β * b ^ 2 - s * b + 1 = 0 := by simp only [b]; field_simp; linear_combination hD2
    refine ⟨a, b, by exact_mod_cast h1, by exact_mod_cast h2, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_root_gt hβ hβ1.le hs ra
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_root_gt hβ hβ1.le hs rb
  · set E := Real.sqrt (4 * β - s ^ 2)
    have hE2 : E ^ 2 = 4 * β - s ^ 2 := Real.sq_sqrt (by linarith)
    set a : ℂ := ⟨s / (2 * β), E / (2 * β)⟩
    set b : ℂ := ⟨s / (2 * β), -(E / (2 * β))⟩
    have hnorm : ∀ y : ℝ, y = E / (2 * β) ∨ y = -(E / (2 * β)) →
        1 < ‖(⟨s / (2 * β), y⟩ : ℂ)‖ := by
      intro y hy
      have hy2 : y ^ 2 = E ^ 2 / (4 * β ^ 2) := by
        rcases hy with rfl | rfl <;> field_simp <;> ring
      have hsq : ‖(⟨s / (2 * β), y⟩ : ℂ)‖ ^ 2 = 1 / β := by
        rw [Complex.sq_norm, Complex.normSq_mk, ← sq, ← sq, hy2, hE2]
        field_simp; ring
      have : 1 < ‖(⟨s / (2 * β), y⟩ : ℂ)‖ ^ 2 := by
        rw [hsq, lt_div_iff₀ hβ]; linarith
      nlinarith [norm_nonneg (⟨s / (2 * β), y⟩ : ℂ)]
    refine ⟨a, b, ?_, ?_, hnorm _ (Or.inl rfl), hnorm _ (Or.inr rfl)⟩
    · apply Complex.ext <;> simp [a, b] <;> field_simp <;> first | ring1 | linear_combination hE2
    · apply Complex.ext
      · simp [a, b]; field_simp; ring
      · simp [a, b]

/-- Woodford (2003), Ch. 7, (1.20) and App. A.3 (**the a priori bound without a stable root**):
if `0 < β < 1` and `|s| < 1 + β`, there is `K ≥ 0` such that every bounded real solution of
`βℓ_{t+2} − sℓ_{t+1} + ℓ_t = g_t` with `|g_t| ≤ G` has `|ℓ_t| ≤ K G` at every date. -/
theorem rec_apriori {β s : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hs : |s| < 1 + β) :
    ∃ K, 0 ≤ K ∧ ∀ (ℓ g : ℕ → ℝ) (L G : ℝ), (∀ t, |ℓ t| ≤ L) → (∀ t, |g t| ≤ G) →
      (∀ t, β * ℓ (t + 2) - s * ℓ (t + 1) + ℓ t = g t) → ∀ t, |ℓ t| ≤ K * G := by
  obtain ⟨z1, z2, h1, h2, hz1, hz2⟩ := roots_out hβ hβ1 hs
  have hz1' : 0 < ‖z1‖ - 1 := by linarith
  have hz2' : 0 < ‖z2‖ - 1 := by linarith
  refine ⟨1 / (β * (‖z2‖ - 1)) / (‖z1‖ - 1), by positivity, fun ℓ g L G hL hg hrec t => ?_⟩
  have hβc : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  set w : ℕ → ℂ := fun t => (ℓ t : ℂ)
  set v : ℕ → ℂ := fun t => w (t + 1) - z1 * w t
  have hvrec : ∀ t, v (t + 1) - z2 * v t = (g t : ℂ) / β := fun t => by
    have h := hrec t
    have hc : (β : ℂ) * w (t + 2) - s * w (t + 1) + w t = g t := by
      simp only [w]; exact_mod_cast h
    simp only [v]
    rw [eq_div_iff hβc]
    rw [← h2] at hc
    linear_combination hc + (w t) * h1
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hvb : ∀ t, ‖v t‖ ≤ L + ‖z1‖ * L := fun t => by
    simp only [v, w]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_real, Real.norm_eq_abs]; exact hL _
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hL _) (norm_nonneg _)
  have hgb : ∀ t, ‖v (t + 1) - z2 * v t‖ ≤ G / β := fun t => by
    rw [hvrec, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hβ]
    exact div_le_div_of_nonneg_right (hg t) hβ.le
  have hv := geom_apriori hz2 hvb hgb
  have hwb : ∀ t, ‖w t‖ ≤ L := fun t => by
    simp only [w]; rw [Complex.norm_real, Real.norm_eq_abs]; exact hL t
  have hw := geom_apriori hz1 hwb (G := G / β / (‖z2‖ - 1)) fun t => hv t
  have := hw t
  simp only [w] at this
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  calc |ℓ t| ≤ G / β / (‖z2‖ - 1) / (‖z1‖ - 1) := this
    _ = 1 / (β * (‖z2‖ - 1)) / (‖z1‖ - 1) * G := by field_simp


/-! ## The forced reduction -/

/-- Woodford (2003), Ch. 7: the current variables in terms of `(λ̂_{t−1}, λ̂_t, w_t)` when the
linearised conditions equal `w_t` (with `G ≠ 0`). -/
noncomputable def compMap (p : Par) : (ℝ × ℝ × (Fin 5 → ℝ)) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun q :=
    ![-(p.θ * p.m * (p.σ + p.ω) * q.2.1 + q.2.2 0 + q.2.2 2 - cR4 p * q.2.2 4) / Gw p +
        q.2.2 4,
      (q.2.1 - q.1) / gamb p - q.2.2 1 / (gamb p * p.ψ),
      -(p.θ * p.m * (p.σ + p.ω) * q.2.1 + q.2.2 0 + q.2.2 2 - cR4 p * q.2.2 4) / Gw p,
      q.2.1,
      (1 - p.σ) * (-(p.θ * p.m * (p.σ + p.ω) * q.2.1 + q.2.2 0 + q.2.2 2 - cR4 p * q.2.2 4) /
          Gw p) - q.2.1 * (p.θ * p.m * p.σ) -
        lamb p * (p.θ * p.m * p.σ * (q.2.2 4 + (1 - p.σ) *
          (-(p.θ * p.m * (p.σ + p.ω) * q.2.1 + q.2.2 0 + q.2.2 2 - cR4 p * q.2.2 4) / Gw p))) -
        gamb p * (-(p.θ * p.m * (p.σ + p.ω) * q.2.1 + q.2.2 0 + q.2.2 2 - cR4 p * q.2.2 4) /
          Gw p) - q.2.2 2]
  map_add' q q' := by
    funext i; fin_cases i <;> simp <;> ring
  map_smul' c q := by
    funext i; fin_cases i <;> simp <;> ring

/-- Woodford (2003), Ch. 7: the forcing of the multiplier recursion from two consecutive
residuals. -/
noncomputable def hMap (p : Par) : ((Fin 5 → ℝ) × (Fin 5 → ℝ)) →ₗ[ℝ] ℝ where
  toFun q := (gamb p * (p.θ * p.m * (p.σ + p.ω)) * (q.1 0 + q.1 2 - cR4 p * q.1 4) / Gw p -
    q.1 1 + p.β * q.2 1 - gamb p * q.1 3 - gamb p * (p.θ * p.m * p.ω) * q.1 4) / p.ψ
  map_add' q q' := by simp; ring
  map_smul' c q := by simp; ring

/-- Woodford (2003), Ch. 7 (**the forced reduction**): if `G ≠ 0`, the linearised conditions at
two consecutive dates with residuals `w`, `w′` give the current variables as
`compMap (λ̂_{t−1}, λ̂_t, w)` and the multiplier recursion
`βλ̂_{t+1} − (1 + β + c_G)λ̂_t + λ̂_{t−1} = hMap(w, w′)`. -/
theorem pf_forced (hp : p.Basic) (hG : Gw p ≠ 0) (um u n nn w w' : Fin 5 → ℝ)
    (h : DQr p um u + DNr p n = w) (h' : DQr p u n + DNr p nn = w') :
    u = compMap p (um 3, u 3, w) ∧
      p.β * n 3 - (1 + p.β + cG p) * u 3 + um 3 = hMap p (w, w') := by
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have c : ∀ i, (DQr p um u + DNr p n) i = w i := fun i => by rw [h]
  have c' : ∀ i, (DQr p u n + DNr p nn) i = w' i := fun i => by rw [h']
  have c0 := c 0; have c1 := c 1; have c2 := c 2; have c3 := c 3; have c4 := c 4
  have d1 := c' 1
  have h02 := red_lam hp um u
  simp only [Pi.add_apply, DNr, Matrix.cons_val_zero, Matrix.cons_val, add_zero] at c0 c2 c4
  rw [c0, c2] at h02
  simp only [DQr, Matrix.cons_val] at c4
  simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val_one, Matrix.cons_val_zero, add_zero] at c1 d1
  simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val] at c3
  have e4 : u 0 = u 2 + w 4 := by linarith
  have e2 : u 2 = -(p.θ * p.m * (p.σ + p.ω) * u 3 + w 0 + w 2 - cR4 p * w 4) / Gw p := by
    rw [eq_div_iff hG]
    have : u 0 - u 2 = w 4 := by linarith
    rw [this] at h02
    unfold cR4; linear_combination h02
  have e1 : u 1 = (u 3 - um 3) / gamb p - w 1 / (gamb p * p.ψ) := by
    field_simp; linear_combination -c1
  have en1 : n 1 = (n 3 - u 3) / gamb p - w' 1 / (gamb p * p.ψ) := by
    field_simp; linear_combination -d1
  have c2' := c 2
  simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val, add_zero] at c2'
  refine ⟨?_, ?_⟩
  · funext i
    fin_cases i
    · simp only [compMap, LinearMap.coe_mk, AddHom.coe_mk, Fin.zero_eta, Matrix.cons_val_zero]
      rw [e4, e2]
    · simp only [compMap, LinearMap.coe_mk, AddHom.coe_mk, Fin.mk_one, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      exact e1
    · simp only [compMap, LinearMap.coe_mk, AddHom.coe_mk, Fin.reduceFinMk, Matrix.cons_val]
      exact e2
    · simp only [compMap, LinearMap.coe_mk, AddHom.coe_mk, Fin.reduceFinMk, Matrix.cons_val]
    · simp only [compMap, LinearMap.coe_mk, AddHom.coe_mk, Fin.reduceFinMk, Matrix.cons_val]
      rw [← e2]
      have : u 0 - p.σ * u 2 = w 4 + (1 - p.σ) * u 2 := by rw [e4]; ring
      rw [← this]
      linarith
  · simp only [hMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [e1, en1, e4, e2] at c3
    unfold cG
    have hgb' := hgb.ne'
    have hψ' := hψ.ne'
    linear_combination (norm := (field_simp; ring)) (-(gamb p / p.ψ)) * c3

/-! ## Non-existence near the steady state -/

/-- Woodford (2003), Ch. 7, (1.20) and App. A.3 (**NON-EXISTENCE FOR THE EXACT RAMSEY CONDITIONS
WHEN `G < 0` AND `−2(1+β) < κθ_R`**): there is `r > 0` such that every exact perfect-foresight
solution of the Rotemberg Ramsey conditions (no disturbances) with `‖u_t‖ ≤ r` at every date and
`|λ̂_{−1}| ≤ r` has `λ̂_{−1} = 0` and is the steady state. In particular, for an inherited
multiplier `0 < |λ̂_{−1}| ≤ r` no exact equilibrium stays within `r` of the steady state. -/
theorem ramsey_nonexist (hp : p.Basic) (hG : Gw p < 0) (hc : -(2 * (1 + p.β)) < cG p) :
    ∃ r > 0, ∀ (d : Fin 5 → ℝ) (u : ℕ → Fin 5 → ℝ), |d 3| ≤ r → (∀ t, ‖u t‖ ≤ r) →
      (∀ t, Qd p (0, lagP d u t, u t) + Nd p (u (t + 1)) = 0) → d 3 = 0 ∧ ∀ t, u t = 0 := by
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hc0 := cG_neg hp hG
  have hs : |1 + p.β + cG p| < 1 + p.β := by rw [abs_lt]; constructor <;> linarith
  obtain ⟨K, hK0, hK⟩ := rec_apriori hβ hβ1 hs
  set CU := ‖LinearMap.toContinuousLinearMap (compMap p)‖
  set CH := ‖LinearMap.toContinuousLinearMap (hMap p)‖
  have hCU : 0 ≤ CU := norm_nonneg _
  have hCH : 0 ≤ CH := norm_nonneg _
  set η := 1 / (8 * (1 + K * CH) * (1 + CU)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := small_remainder
    ((contDiff_Qd (n := 1) p).differentiable one_ne_zero 0) hη0
  obtain ⟨ρN, hρN, hN⟩ := small_remainder
    ((contDiff_Nd (n := 1) p).differentiable one_ne_zero 0) hη0
  set r := min ρQ ρN / 2
  have hr0 : 0 < r := by positivity
  have hrQ : r < ρQ := by
    have := min_le_left ρQ ρN; have := lt_min hρQ hρN; simp only [r]; linarith
  have hrN : r < ρN := by
    have := min_le_right ρQ ρN; have := lt_min hρQ hρN; simp only [r]; linarith
  refine ⟨r, hr0, fun d u hd hu heq => ?_⟩
  have hss := Qd_Nd_zero hp
  -- one halving step
  have half : ∀ B, 0 ≤ B → B ≤ r → |d 3| ≤ B → (∀ t, ‖u t‖ ≤ B) →
      |d 3| ≤ B / 2 ∧ ∀ t, ‖u t‖ ≤ B / 2 := by
    intro B hB0 hBr hdB huB
    set ℓ : ℕ → ℝ := fun t => lagP d u t 3 with hℓ
    have hℓB : ∀ t, |ℓ t| ≤ B := fun t => by
      cases t with
      | zero => exact hdB
      | succ t =>
        have := (norm_le_pi_norm (u t) 3).trans (huB t); rwa [Real.norm_eq_abs] at this
    set a : ℕ → Fin 5 → ℝ := fun t => proj (lagP d u t)
    have ha3 : ∀ t, a t 3 = ℓ t := fun t => rfl
    have haB : ∀ t, ‖a t‖ ≤ B := fun t => by
      refine (pi_norm_le_iff_of_nonneg hB0).2 fun i => ?_
      fin_cases i
      · simp [a, proj, hB0]
      · simp [a, proj, hB0]
      · simp [a, proj, hB0]
      · have h3 : a t 3 = ℓ t := rfl
        simp only [Fin.reduceFinMk, Real.norm_eq_abs]
        rw [h3]; exact hℓB t
      · simp [a, proj, hB0]
    set w : ℕ → Fin 5 → ℝ := fun t => DQr p (a t) (u t) + DNr p (u (t + 1))
    have hw : ∀ t, ‖w t‖ ≤ 2 * η * B := fun t => by
      have hq : ‖((0 : Fin 3 → ℝ), a t, u t)‖ ≤ B := by
        rw [Prod.norm_def, Prod.norm_def, norm_zero]
        exact max_le hB0 (max_le (haB t) (huB t))
      have h1 := hQ ((0 : Fin 3 → ℝ), a t, u t) (by linarith)
      have h2 := hN (u (t + 1)) (by linarith [huB (t + 1)])
      rw [NonlinearRotembergRamseyLin.fderiv_Qd] at h1
      rw [fderiv_Nd] at h2
      have hex : Qd p (0, a t, u t) + Nd p (u (t + 1)) = 0 := by
        rw [Qd_congr _ _ (ha3 t)]; exact heq t
      have e : w t = -((Qd p (0, a t, u t) - Qd p 0 - DQr p (a t) (u t)) +
          (Nd p (u (t + 1)) - Nd p 0 - DNr p (u (t + 1)))) := by
        have h0 : Qd p 0 + Nd p 0 = 0 := hss
        have e1 := eq_neg_of_add_eq_zero_left hex
        have e2 := eq_neg_of_add_eq_zero_left h0
        simp only [w]
        rw [e1, e2]; abel
      rw [e, norm_neg]
      calc _ ≤ ‖Qd p (0, a t, u t) - Qd p 0 - DQr p (a t) (u t)‖ +
            ‖Nd p (u (t + 1)) - Nd p 0 - DNr p (u (t + 1))‖ := norm_add_le _ _
        _ ≤ η * B + η * B := add_le_add (h1.trans (mul_le_mul_of_nonneg_left hq hη0.le))
            (h2.trans (mul_le_mul_of_nonneg_left (huB _) hη0.le))
        _ = 2 * η * B := by ring
    have hred : ∀ t, u t = compMap p (ℓ t, ℓ (t + 1), w t) ∧
        p.β * ℓ (t + 2) - (1 + p.β + cG p) * ℓ (t + 1) + ℓ t = hMap p (w t, w (t + 1)) :=
      fun t => by
        have := pf_forced hp hG.ne (a t) (u t) (u (t + 1)) (u (t + 2)) (w t) (w (t + 1)) rfl
          (by
            have e : DQr p (u t) (u (t + 1)) = DQr p (a (t + 1)) (u (t + 1)) := by
              simp [DQr, a, proj, lagP]
            simp only [w, e])
        exact ⟨this.1, this.2⟩
    have hg : ∀ t, |hMap p (w t, w (t + 1))| ≤ CH * (2 * η * B) := fun t => by
      have := (LinearMap.toContinuousLinearMap (hMap p)).le_opNorm (w t, w (t + 1))
      rw [Real.norm_eq_abs] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hCH)
      rw [Prod.norm_def]; exact max_le (hw t) (hw (t + 1))
    have hℓK : ∀ t, |ℓ t| ≤ K * (CH * (2 * η * B)) :=
      hK ℓ _ B _ hℓB hg fun t => (hred t).2
    have hkey : K * (CH * (2 * η * B)) ≤ B / (4 * (1 + CU)) := by
      have h1 : 0 ≤ K * CH := by positivity
      have : K * CH * η ≤ 1 / (8 * (1 + CU)) := by
        rw [hη, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg h1 hCU]
      have e : K * (CH * (2 * η * B)) = 2 * B * (K * CH * η) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * B)
      calc _ ≤ 2 * B * (1 / (8 * (1 + CU))) := this
        _ = B / (4 * (1 + CU)) := by field_simp; ring
    have hq4 : B / (4 * (1 + CU)) ≤ B / 4 := by
      apply div_le_div_of_nonneg_left hB0 (by norm_num); nlinarith
    refine ⟨(by have := (hℓK 0).trans (hkey.trans hq4); simp only [ℓ, lagP] at this; linarith),
      fun t => ?_⟩
    rw [(hred t).1]
    have := (LinearMap.toContinuousLinearMap (compMap p)).le_opNorm (ℓ t, ℓ (t + 1), w t)
    refine this.trans ?_
    have hmx : ‖((ℓ t, ℓ (t + 1), w t) : ℝ × ℝ × (Fin 5 → ℝ))‖ ≤
        B / (4 * (1 + CU)) + 2 * η * B := by
      rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := (hℓK t).trans hkey
      have h2 := (hℓK (t + 1)).trans hkey
      have h3 := hw t
      have : 0 ≤ 2 * η * B := by positivity
      have : 0 ≤ B / (4 * (1 + CU)) := by positivity
      exact max_le (by linarith) (max_le (by linarith) (by linarith))
    have hcu : CU * (2 * η) ≤ 1 / 4 := by
      rw [hη]
      have h1 : 0 ≤ K * CH := by positivity
      rw [show CU * (2 * (1 / (8 * (1 + K * CH) * (1 + CU)))) =
        CU / (4 * (1 + K * CH) * (1 + CU)) by field_simp; ring]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg h1 hCU]
    have hc1 : CU * (B / (4 * (1 + CU))) ≤ B / 4 := by
      rw [show CU * (B / (4 * (1 + CU))) = B / 4 * (CU / (1 + CU)) by field_simp]
      have : CU / (1 + CU) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
      nlinarith
    calc CU * ‖((ℓ t, ℓ (t + 1), w t) : ℝ × ℝ × (Fin 5 → ℝ))‖ ≤
          CU * (B / (4 * (1 + CU)) + 2 * η * B) := mul_le_mul_of_nonneg_left hmx hCU
      _ ≤ B / 2 := by
          have := mul_le_mul_of_nonneg_right hcu hB0
          have e : CU * (B / (4 * (1 + CU)) + 2 * η * B) =
              CU * (B / (4 * (1 + CU))) + CU * (2 * η) * B := by ring
          rw [e]; linarith
  -- iterate the halving
  have hit : ∀ n : ℕ, |d 3| ≤ r / 2 ^ n ∧ ∀ t, ‖u t‖ ≤ r / 2 ^ n := by
    intro n
    induction n with
    | zero => simpa using ⟨hd, hu⟩
    | succ n ih =>
      have h := half (r / 2 ^ n) (by positivity)
        (div_le_self hr0.le (one_le_pow₀ (by norm_num))) ih.1 ih.2
      rw [pow_succ, ← div_div]
      exact h
  have ht : Tendsto (fun n : ℕ => r / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow]; field_simp
  refine ⟨?_, fun t => ?_⟩
  · have := ge_of_tendsto' ht fun n => (hit n).1
    exact abs_nonpos_iff.1 this
  · have := ge_of_tendsto' ht fun n => (hit n).2 t
    exact norm_le_zero_iff.1 this

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyNonexist
