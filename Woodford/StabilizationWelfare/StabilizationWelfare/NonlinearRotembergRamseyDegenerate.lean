/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyAE

/-!
# The Rotemberg timeless Ramsey problem when `G = 1 + ω − m(1 − σ) ≤ 0`

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 ((1.20), pp. 475–476: the root condition
of the optimal commitment system), with Rotemberg pricing. The Ramsey results of
`NonlinearRotembergRamseyIFT`, `NonlinearRotembergRamseyAEIFT` and
`NonlinearRotembergNonAdapted` assume `G > 0`, which holds for every nonnegative distortion
(`NonlinearRotembergRamseyLin.Gw_pos`). Here the remaining cases are characterised for the
linearised commitment system under perfect foresight (`PF`), with inherited multiplier `λ̂_{−1}`.

## Main results

* **`Gw_nonpos`**: `G ≤ 0` only if `σ < 1` and `m ≥ (1+ω)/(1−σ) > 1`, i.e. an output subsidy
  overshooting the efficient level (`Φ < 0`); both `G = 0` and `G < 0` occur (`Gw_cases_occur`).
* **`pf_reduce`**, **`pf_build`**: for `G ≠ 0` the system is equivalent to the multiplier
  recursion `βλ̂_{t+1} − (1 + β + c_G)λ̂_t + λ̂_{t−1} = 0`, `c_G = γ̄(θm(σ+ω))²/(Gψ) = κθ_R`
  (`cG_eq`), with `ŷ = ĉ = −θm(σ+ω)λ̂/G` and `π = Δλ̂/γ̄`.
* **`ramsey_G_zero`** (`G = 0`): for every `λ̂_{−1}` there is exactly one solution (bounded or not):
  `λ̂_t = 0`, `π_0 = −λ̂_{−1}/γ̄`, `π_t = 0` for `t ≥ 1` — strict price stability after one period.
* **`ramsey_G_neg_nonexist`** (`G < 0`, `−2(1+β) < κθ_R < 0`): every bounded solution has
  `λ̂_{−1} = 0` and is zero; for `λ̂_{−1} ≠ 0` NO bounded solution exists (both roots outside the
  unit circle, `rec_bounded_zero`).
* **`ramsey_G_neg_det`** (`G < 0`, `κθ_R < −2(1+β)`): for every `λ̂_{−1}` exactly one bounded
  solution, `λ̂_t = z₁^{t+1}λ̂_{−1}` with an OSCILLATING stable root `z₁ ∈ (−1, 0)`.
* **`ramsey_G_neg_unit`** (`κθ_R = −2(1+β)`): exactly one bounded solution, `λ̂_t =
  (−1)^{t+1}λ̂_{−1}`, which does not converge when `λ̂_{−1} ≠ 0`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyDegenerate

open Filter Topology
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyAE (gamb_pos)

variable {p : Par}

/-! ## When can `G` be nonpositive? -/

/-- Woodford (2003), Ch. 7 (**`G ≤ 0` requires an overshooting subsidy**): if `G ≤ 0` then
`σ < 1` and `(1 + ω) ≤ m(1 − σ)`, so `m > 1` (`Φ < 0`). -/
theorem Gw_nonpos (hp : p.Basic) (hG : Gw p ≤ 0) :
    p.σ < 1 ∧ 1 + p.ω ≤ p.m * (1 - p.σ) ∧ 1 < p.m := by
  unfold Gw at hG
  have := hp.ω_nonneg; have := hp.σ_pos; have := hp.m_pos
  have hs : p.σ < 1 := by
    by_contra h; push Not at h; nlinarith
  refine ⟨hs, by linarith, ?_⟩
  by_contra h; push Not at h; nlinarith

/-- Woodford (2003), Ch. 7: both cases occur — with `σ = 1/2`, `ω = 0`, `G = 0` at `m = 2` and
`G = −1/2` at `m = 3`. -/
theorem Gw_cases_occur (β θ ψ φ φy : ℝ) :
    Gw ⟨β, 1 / 2, 0, θ, ψ, 2, φ, φy⟩ = 0 ∧ Gw ⟨β, 1 / 2, 0, θ, ψ, 3, φ, φy⟩ = -1 / 2 := by
  constructor <;> (unfold Gw; norm_num)

/-! ## Second-order recursions -/

/-- Woodford (2003), Ch. 7, (1.20) (tool): if `βz₁z₂ = 1` and `β(z₁ + z₂) = s`, a solution of
`βℓ_{t+2} − sℓ_{t+1} + ℓ_t = 0` has `v_t = ℓ_{t+1} − z₁ℓ_t` with `v_{t+1} = z₂v_t`. -/
theorem rec_factor {β s z1 z2 : ℝ} (hβ : 0 < β) (h1 : β * z1 * z2 = 1) (h2 : β * (z1 + z2) = s)
    {ℓ : ℕ → ℝ} (hℓ : ∀ t, β * ℓ (t + 2) - s * ℓ (t + 1) + ℓ t = 0) (t : ℕ) :
    ℓ (t + 2) - z1 * ℓ (t + 1) = z2 * (ℓ (t + 1) - z1 * ℓ t) := by
  have h := hℓ t
  have : β * (ℓ (t + 2) - z1 * ℓ (t + 1) - z2 * (ℓ (t + 1) - z1 * ℓ t)) = 0 := by
    linear_combination h - ℓ (t + 1) * h2 + ℓ t * h1
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hβ.ne')

/-- Woodford (2003), App. A.3 (tool): a geometric sequence with ratio `|r| > 1` is bounded only if
it is zero. -/
theorem geom_bounded_zero {r a C : ℝ} (hr : 1 < |r|) (h : ∀ t : ℕ, |r ^ t * a| ≤ C) : a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.2 ha
  have ht := tendsto_pow_atTop_atTop_of_one_lt hr
  obtain ⟨t, htt⟩ := (ht.eventually_gt_atTop (C / |a|)).exists
  have h1 := h t
  rw [abs_mul, abs_pow] at h1
  rw [div_lt_iff₀ hpos] at htt
  linarith

/-- Woodford (2003), App. A.3 (tool): a solution with `ℓ_{t+1} − zℓ_t` geometric of ratio `|r| > 1`
and bounded is the geometric sequence `ℓ_t = zᵗℓ_0`. -/
theorem rec_pin {β s z1 z2 B : ℝ} (hβ : 0 < β) (h1 : β * z1 * z2 = 1) (h2 : β * (z1 + z2) = s)
    (hz2 : 1 < |z2|) {ℓ : ℕ → ℝ} (hℓ : ∀ t, β * ℓ (t + 2) - s * ℓ (t + 1) + ℓ t = 0)
    (hB : ∀ t, |ℓ t| ≤ B) (t : ℕ) : ℓ t = z1 ^ t * ℓ 0 := by
  set v : ℕ → ℝ := fun t => ℓ (t + 1) - z1 * ℓ t with hv
  have hgeo : ∀ t, v t = z2 ^ t * v 0 := fun t => by
    induction t with
    | zero => simp
    | succ t ih =>
      have := rec_factor hβ h1 h2 hℓ t
      simp only [hv] at this ih ⊢
      rw [this, ih, pow_succ]; ring
  have hv0 : v 0 = 0 := geom_bounded_zero hz2 (C := B + |z1| * B) fun t => by
    rw [← hgeo t]
    simp only [hv]
    calc |ℓ (t + 1) - z1 * ℓ t| ≤ |ℓ (t + 1)| + |z1 * ℓ t| := abs_sub _ _
      _ ≤ B + |z1| * B := by
          rw [abs_mul]
          exact add_le_add (hB _) (mul_le_mul_of_nonneg_left (hB t) (abs_nonneg _))
  induction t with
  | zero => simp
  | succ t ih =>
    have := hgeo t
    rw [hv0, mul_zero] at this
    simp only [hv] at this
    rw [pow_succ]; linear_combination this + z1 * ih

/-- Woodford (2003), Ch. 7, (1.20) (tool): if `0 < β ≤ 1` and `|s| < 1 + β`, every real root of
`βz² − sz + 1` has `|z| > 1`. -/
theorem abs_root_gt {β s z : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hs : |s| < 1 + β)
    (hz : β * z ^ 2 - s * z + 1 = 0) : 1 < |z| := by
  by_contra h
  push Not at h
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hx : 0 < |z| := abs_pos.2 hz0
  have e : |s| * |z| = β * |z| ^ 2 + 1 := by
    rw [← abs_mul, sq_abs]
    have : s * z = β * z ^ 2 + 1 := by linarith
    rw [this, abs_of_pos (by positivity)]
  have h2 : (1 - |z|) * (1 - β * |z|) ≥ 0 :=
    mul_nonneg (by linarith) (by nlinarith)
  nlinarith

/-- Woodford (2003), Ch. 7, (1.20) and App. A.3 (**no stable root**): if `0 < β < 1` and
`|s| < 1 + β`, every bounded solution of `βℓ_{t+2} − sℓ_{t+1} + ℓ_t = 0` is zero. (Real roots:
both outside the unit circle; complex roots: the form
`Q_t = ℓ_{t+1}² − (s/β)ℓ_{t+1}ℓ_t + ℓ_t²/β` is positive definite and `Q_{t+1} = Q_t/β`.) -/
theorem rec_bounded_zero {β s B : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hs : |s| < 1 + β)
    {ℓ : ℕ → ℝ} (hℓ : ∀ t, β * ℓ (t + 2) - s * ℓ (t + 1) + ℓ t = 0) (hB : ∀ t, |ℓ t| ≤ B)
    (t : ℕ) : ℓ t = 0 := by
  rcases le_or_gt (4 * β) (s ^ 2) with hD | hD
  · -- real roots, both outside the unit circle
    set D := Real.sqrt (s ^ 2 - 4 * β) with hDdef
    have hD2 : D ^ 2 = s ^ 2 - 4 * β := Real.sq_sqrt (by linarith)
    set z1 := (s - D) / (2 * β)
    set z2 := (s + D) / (2 * β)
    have h1 : β * z1 * z2 = 1 := by
      simp only [z1, z2]; field_simp; linear_combination -hD2
    have h2 : β * (z1 + z2) = s := by simp only [z1, z2]; field_simp; ring
    have hr2 : β * z2 ^ 2 - s * z2 + 1 = 0 := by
      simp only [z2]; field_simp; linear_combination hD2
    have hr1 : β * z1 ^ 2 - s * z1 + 1 = 0 := by
      simp only [z1]; field_simp; linear_combination hD2
    have hz2 := abs_root_gt hβ hβ1.le hs hr2
    have hz1 := abs_root_gt hβ hβ1.le hs hr1
    have hgeo := rec_pin hβ h1 h2 hz2 hℓ hB
    have h0 : ℓ 0 = 0 := geom_bounded_zero hz1 (C := B) fun t => by rw [← hgeo t]; exact hB t
    rw [hgeo t, h0, mul_zero]
  · -- complex roots: a positive definite form growing like `β^{−t}`
    set Q : ℕ → ℝ := fun t => ℓ (t + 1) ^ 2 - s / β * ℓ (t + 1) * ℓ t + ℓ t ^ 2 / β with hQ
    have hQs : ∀ t, Q (t + 1) = Q t / β := fun t => by
      have h := hℓ t
      have e : ℓ (t + 2) = (s * ℓ (t + 1) - ℓ t) / β := by
        rw [eq_div_iff hβ.ne']; linarith
      simp only [hQ, e]
      field_simp; ring
    have hQt : ∀ t, Q 0 = Q t * β ^ t := fun t => by
      induction t with
      | zero => simp
      | succ t ih => rw [ih, hQs, pow_succ]; field_simp
    have hQb : ∀ t, Q t ≤ B ^ 2 + |s| / β * B ^ 2 + B ^ 2 / β := fun t => by
      have hb1 := hB t; have hb2 := hB (t + 1)
      have hB0 : 0 ≤ B := (abs_nonneg _).trans hb1
      have a1 : ℓ (t + 1) ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb2 2
      have a2 : ℓ t ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
      have a3 : -(s / β * ℓ (t + 1) * ℓ t) ≤ |s| / β * B ^ 2 := by
        have : |s / β * ℓ (t + 1) * ℓ t| ≤ |s| / β * B ^ 2 := by
          rw [abs_mul, abs_mul, abs_div, abs_of_pos hβ, sq]
          have := mul_le_mul hb2 hb1 (abs_nonneg _) hB0
          have hsb : 0 ≤ |s| / β := by positivity
          calc |s| / β * |ℓ (t + 1)| * |ℓ t| = |s| / β * (|ℓ (t + 1)| * |ℓ t|) := by ring
            _ ≤ |s| / β * (B * B) := mul_le_mul_of_nonneg_left this hsb
        exact (neg_le_abs _).trans this
      have a4 : ℓ t ^ 2 / β ≤ B ^ 2 / β := div_le_div_of_nonneg_right a2 hβ.le
      simp only [hQ]; linarith
    set C := B ^ 2 + |s| / β * B ^ 2 + B ^ 2 / β
    have hQ0 : Q 0 ≤ 0 := by
      have ht : Tendsto (fun t : ℕ => C * β ^ t) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).const_mul C
      refine ge_of_tendsto' ht fun t => ?_
      rw [hQt t]
      exact mul_le_mul_of_nonneg_right (hQb t) (pow_nonneg hβ.le t)
    -- positive definiteness
    have hpd : β * Q 0 = (ℓ 0 - s / 2 * ℓ 1) ^ 2 + (β - s ^ 2 / 4) * ℓ 1 ^ 2 := by
      simp only [hQ]; field_simp; ring
    have hβQ : β * Q 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ.le hQ0
    have h4 : 0 < β - s ^ 2 / 4 := by linarith
    have hl1 : ℓ 1 = 0 := by
      have hsq : (β - s ^ 2 / 4) * ℓ 1 ^ 2 ≤ 0 := by
        have := sq_nonneg (ℓ 0 - s / 2 * ℓ 1); linarith
      have h5 : ℓ 1 ^ 2 ≤ 0 := by
        by_contra hh; push Not at hh; have := mul_pos h4 hh; linarith
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h5 (sq_nonneg _))
    have hl0 : ℓ 0 = 0 := by
      rw [hl1, mul_zero, sub_zero, zero_pow two_ne_zero, mul_zero, add_zero] at hpd
      have h5 : ℓ 0 ^ 2 ≤ 0 := by linarith
      exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h5 (sq_nonneg _))
    have hall : ∀ t, ℓ t = 0 ∧ ℓ (t + 1) = 0 := fun t => by
      induction t with
      | zero => exact ⟨hl0, hl1⟩
      | succ t ih =>
        refine ⟨ih.2, ?_⟩
        have h := hℓ t
        rw [ih.1, ih.2] at h
        have : β * ℓ (t + 2) = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hβ.ne'
    exact (hall t).1

/-! ## The linearised commitment system under perfect foresight -/

/-- Woodford (2003), Ch. 7: the lagged variables with the inherited initial value `d`. -/
def lagP (d : Fin 5 → ℝ) (u : ℕ → Fin 5 → ℝ) : ℕ → Fin 5 → ℝ
  | 0 => d
  | t + 1 => u t

/-- Woodford (2003), Ch. 7 and (1.20) (**the linearised commitment system under perfect
foresight**): `DQ(λ̂_{t−1}; u_t) + DN(u_{t+1}) = 0` at every date, `λ̂_{−1} = d 3`. -/
def PF (p : Par) (d : Fin 5 → ℝ) (u : ℕ → Fin 5 → ℝ) : Prop :=
  ∀ t, DQr p (lagP d u t) (u t) + DNr p (u (t + 1)) = 0

/-- Woodford (2003), Ch. 7: the coefficient of the multiplier recursion,
`c_G = γ̄(θm(σ+ω))²/(Gψ)`. -/
noncomputable def cG (p : Par) : ℝ :=
  gamb p * (p.θ * p.m * (p.σ + p.ω)) ^ 2 / (Gw p * p.ψ)

/-- Woodford (2003), Ch. 7: `c_G = κθ_R`. -/
theorem cG_eq (hp : p.Basic) (hG : Gw p ≠ 0) : cG p = p.κ * thR p := by
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hψ := hp.ψ_pos.ne'
  unfold cG thR gamb Par.κ
  field_simp

/-- The components of the system at one date. -/
theorem pf_comp (d : Fin 5 → ℝ) (u : ℕ → Fin 5 → ℝ) (h : PF p d u) (t : ℕ) :
    (∀ i, (DQr p (lagP d u t) (u t) + DNr p (u (t + 1))) i = 0) := fun i => by
  rw [h t]; rfl

/-- Woodford (2003), Ch. 7 (**reduction to the multiplier recursion**): if `G ≠ 0`, every
perfect-foresight solution has `ĉ = ŷ = −θm(σ+ω)λ̂/G`, `π_t = (λ̂_t − λ̂_{t−1})/γ̄`, and
`ℓ_t = λ̂_{t−1}` (with `ℓ_0 = d 3`) solves `βℓ_{t+2} − (1 + β + c_G)ℓ_{t+1} + ℓ_t = 0`. -/
theorem pf_reduce (hp : p.Basic) (hG : Gw p ≠ 0) (d : Fin 5 → ℝ) (u : ℕ → Fin 5 → ℝ)
    (h : PF p d u) :
    (∀ t, u t 0 = -(p.θ * p.m * (p.σ + p.ω)) * u t 3 / Gw p ∧ u t 2 = u t 0 ∧
      u t 1 = (u t 3 - lagP d u t 3) / gamb p) ∧
    ∀ t, p.β * lagP d u (t + 2) 3 - (1 + p.β + cG p) * lagP d u (t + 1) 3 + lagP d u t 3 = 0 := by
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hc : ∀ t, u t 2 = u t 0 ∧ u t 0 = -(p.θ * p.m * (p.σ + p.ω)) * u t 3 / Gw p ∧
      u t 1 = (u t 3 - lagP d u t 3) / gamb p := fun t => by
    have e := pf_comp d u h t
    have e4 := e 4
    have e1 := e 1
    have e0 := e 0
    have e2 := e 2
    simp only [Pi.add_apply, DNr, Matrix.cons_val, add_zero] at e4 e0 e2
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val_one, Matrix.cons_val_zero, add_zero] at e1
    have h02 := red_lam hp (lagP d u t) (u t)
    rw [e0, e2] at h02
    simp only [DQr, Matrix.cons_val] at e4
    have h42 : u t 2 = u t 0 := by linarith
    refine ⟨h42, ?_, ?_⟩
    · rw [h42, sub_self, mul_zero, add_zero] at h02
      field_simp
      linear_combination h02
    · field_simp
      have : p.ψ * (u t 1 * gamb p - (u t 3 - lagP d u t 3)) = 0 := by linear_combination -e1
      have := (mul_eq_zero.1 this).resolve_left hψ.ne'
      linarith
  refine ⟨fun t => ⟨(hc t).2.1, (hc t).1, (hc t).2.2⟩, fun t => ?_⟩
  have e3 := pf_comp d u h t 3
  simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val] at e3
  obtain ⟨h2, h0, h1⟩ := hc t
  obtain ⟨-, -, h1'⟩ := hc (t + 1)
  have l1 : lagP d u (t + 1) 3 = u t 3 := rfl
  have l2 : lagP d u (t + 2) 3 = u (t + 1) 3 := rfl
  rw [h1', l1, h2, h0, h1] at e3
  rw [l1, l2]
  unfold cG
  have hgb' := hgb.ne'
  have hψ' := hψ.ne'
  linear_combination (norm := (field_simp; ring)) (-(gamb p) / p.ψ) * e3

/-- Woodford (2003), Ch. 7: the date-`t` vector built from a multiplier path `ℓ` (`ℓ_t = λ̂_{t−1}`):
`ŷ = ĉ = −θm(σ+ω)ℓ_{t+1}/G`, `π = (ℓ_{t+1} − ℓ_t)/γ̄`, `λ̂ = ℓ_{t+1}` and `γ̂` from the
consumption condition. -/
noncomputable def buildU (p : Par) (ℓ : ℕ → ℝ) (t : ℕ) : Fin 5 → ℝ :=
  ![-(p.θ * p.m * (p.σ + p.ω)) * ℓ (t + 1) / Gw p, (ℓ (t + 1) - ℓ t) / gamb p,
    -(p.θ * p.m * (p.σ + p.ω)) * ℓ (t + 1) / Gw p, ℓ (t + 1),
    (1 - p.σ) * (-(p.θ * p.m * (p.σ + p.ω)) * ℓ (t + 1) / Gw p) - (ℓ (t + 1) * (p.θ * p.m * p.σ) +
      lamb p * (p.θ * p.m * p.σ * ((-(p.θ * p.m * (p.σ + p.ω)) * ℓ (t + 1) / Gw p) -
        p.σ * (-(p.θ * p.m * (p.σ + p.ω)) * ℓ (t + 1) / Gw p)))) -
      gamb p * (-(p.θ * p.m * (p.σ + p.ω)) * ℓ (t + 1) / Gw p)]

/-- Woodford (2003), Ch. 7 (**the converse**): if `G ≠ 0` and `ℓ` solves the multiplier recursion
with `ℓ_0 = d 3`, then `buildU ℓ` solves the perfect-foresight system. -/
theorem pf_build (hp : p.Basic) (hG : Gw p ≠ 0) (d : Fin 5 → ℝ) (ℓ : ℕ → ℝ) (h0 : ℓ 0 = d 3)
    (hℓ : ∀ t, p.β * ℓ (t + 2) - (1 + p.β + cG p) * ℓ (t + 1) + ℓ t = 0) :
    PF p d (buildU p ℓ) := by
  have hψ := hp.ψ_pos.ne'
  have hgb := (gamb_pos hp).ne'
  have hlag : ∀ t, lagP d (buildU p ℓ) t 3 = ℓ t := fun t => by
    cases t with
    | zero => exact h0.symm
    | succ t => rfl
  intro t
  have hl := hlag t
  funext i
  have h02 := red_lam hp (lagP d (buildU p ℓ) t) (buildU p ℓ t)
  have c2 : DQr p (lagP d (buildU p ℓ) t) (buildU p ℓ t) 2 = 0 := by
    simp only [DQr, buildU, Matrix.cons_val]; ring
  fin_cases i
  · simp only [Fin.zero_eta, Pi.add_apply, DNr, Matrix.cons_val_zero, add_zero, Pi.zero_apply]
    rw [c2] at h02
    have e : buildU p ℓ t 0 - buildU p ℓ t 2 = 0 := by simp [buildU]
    rw [e, mul_zero, add_zero] at h02
    have e2 : -(Gw p * buildU p ℓ t 2) - p.θ * p.m * (p.σ + p.ω) * buildU p ℓ t 3 = 0 := by
      simp only [buildU, Matrix.cons_val]; field_simp; ring
    linarith
  · simp only [Fin.mk_one, Pi.add_apply, DNr, DQr, Matrix.cons_val_one, Matrix.cons_val_zero,
      add_zero, Pi.zero_apply]
    rw [hl]
    simp only [buildU, Matrix.cons_val]
    field_simp; ring
  · simp only [Fin.reduceFinMk, Pi.add_apply, DNr, Matrix.cons_val, add_zero, Pi.zero_apply]
    exact c2
  · simp only [Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, Pi.zero_apply]
    simp only [buildU, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero]
    have hr := hℓ t
    unfold cG at hr
    linear_combination (norm := (field_simp; ring)) (-(p.ψ) / gamb p) * hr
  · simp only [Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, Pi.zero_apply,
      add_zero]
    simp [buildU]

/-- The multiplier path of a solution: `ℓ_0 = d 3`, `ℓ_{t+1} = λ̂_t`. -/
theorem lagP_bound (d : Fin 5 → ℝ) (u : ℕ → Fin 5 → ℝ) {B : ℝ} (hB : ∀ t k, |u t k| ≤ B) :
    ∀ t, |lagP d u t 3| ≤ max |d 3| B := fun t => by
  cases t with
  | zero => exact le_max_left _ _
  | succ t => exact (hB t 3).trans (le_max_right _ _)

/-- A solution with `G ≠ 0` is pinned by its multiplier path. -/
theorem pf_eq_build (hp : p.Basic) (hG : Gw p ≠ 0) (d : Fin 5 → ℝ) (u : ℕ → Fin 5 → ℝ)
    (h : PF p d u) (t : ℕ) : u t = buildU p (fun s => lagP d u s 3) t := by
  obtain ⟨hc, -⟩ := pf_reduce hp hG d u h
  obtain ⟨h0, h2, h1⟩ := hc t
  have e2 := pf_comp d u h t 2
  simp only [Pi.add_apply, DNr, DQr, Matrix.cons_val, add_zero] at e2
  have l1 : lagP d u (t + 1) 3 = u t 3 := rfl
  funext k
  fin_cases k
  · simp only [Fin.zero_eta, buildU, Matrix.cons_val_zero, l1]; exact h0
  · simp only [Fin.mk_one, buildU, Matrix.cons_val_one, Matrix.cons_val_zero, l1]; exact h1
  · simp only [Fin.reduceFinMk, buildU, Matrix.cons_val, l1]; rw [h2]; exact h0
  · simp only [Fin.reduceFinMk, buildU, Matrix.cons_val, l1]
  · simp only [Fin.reduceFinMk, buildU, Matrix.cons_val, l1]
    rw [← h0]
    rw [h2] at e2
    linarith

/-! ## The case `G = 0`: strict price stability after one period -/

/-- Woodford (2003), Ch. 7: the date-0 vector of the `G = 0` solution: `π_0 = −λ̂_{−1}/γ̄`,
`ŷ_0 = ĉ_0 = ψπ_0/(θm(σ+ω))`, `λ̂_0 = 0` and `γ̂_0` from the consumption condition. -/
noncomputable def zeroU0 (p : Par) (d : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![p.ψ * (-d 3 / gamb p) / (p.θ * p.m * (p.σ + p.ω)), -d 3 / gamb p,
    p.ψ * (-d 3 / gamb p) / (p.θ * p.m * (p.σ + p.ω)), 0,
    (1 - p.σ) * (p.ψ * (-d 3 / gamb p) / (p.θ * p.m * (p.σ + p.ω))) -
      lamb p * (p.θ * p.m * p.σ * (p.ψ * (-d 3 / gamb p) / (p.θ * p.m * (p.σ + p.ω)) -
        p.σ * (p.ψ * (-d 3 / gamb p) / (p.θ * p.m * (p.σ + p.ω))))) -
      gamb p * (p.ψ * (-d 3 / gamb p) / (p.θ * p.m * (p.σ + p.ω)))]

/-- Woodford (2003), Ch. 7: the `G = 0` solution, `zeroU0` at date `0` and zero afterwards. -/
noncomputable def zeroU (p : Par) (d : Fin 5 → ℝ) (t : ℕ) : Fin 5 → ℝ :=
  if t = 0 then zeroU0 p d else 0

/-- Woodford (2003), Ch. 7 (**`G = 0`**): every perfect-foresight solution of the linearised
commitment system (bounded or not) has `λ̂_t = 0` for all `t`, `π_0 = −λ̂_{−1}/γ̄` and `π_t = 0`
for `t ≥ 1`; and a solution exists for every inherited multiplier (`zeroU`): the system is
determinate with no inertia beyond one period. -/
theorem ramsey_G_zero (hp : p.Basic) (hG : Gw p = 0) (d : Fin 5 → ℝ) :
    PF p d (zeroU p d) ∧ ∀ u, PF p d u →
      (∀ t, u t 3 = 0) ∧ u 0 1 = -d 3 / gamb p ∧ ∀ t, u (t + 1) 1 = 0 := by
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hlam : ∀ u, PF p d u → ∀ t, u t 3 = 0 := fun u h t => by
    have e := pf_comp d u h t
    have e4 := e 4; have e0 := e 0; have e2 := e 2
    simp only [Pi.add_apply, DNr, Matrix.cons_val, add_zero] at e4 e0 e2
    simp only [DQr, Matrix.cons_val] at e4
    have h02 := red_lam hp (lagP d u t) (u t)
    rw [e0, e2, hG, show u t 0 - u t 2 = 0 by linarith] at h02
    have : p.θ * p.m * (p.σ + p.ω) * u t 3 = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left (by positivity)
  have hpi : ∀ u, PF p d u → ∀ t, u t 1 = -lagP d u t 3 / gamb p := fun u h t => by
    have e1 := pf_comp d u h t 1
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val_one, Matrix.cons_val_zero, add_zero] at e1
    rw [hlam u h t] at e1
    field_simp
    have : p.ψ * (u t 1 * gamb p + lagP d u t 3) = 0 := by linear_combination -e1
    have := (mul_eq_zero.1 this).resolve_left hψ.ne'
    linarith
  refine ⟨?_, fun u h => ⟨hlam u h, by rw [hpi u h 0]; rfl, fun t => ?_⟩⟩
  · intro t
    have hθm' := hθm.ne'
    have hs' := hs.ne'
    have hgb' := hgb.ne'
    cases t with
    | zero =>
      have hl : lagP d (zeroU p d) 0 = d := rfl
      have h0 : zeroU p d 0 = zeroU0 p d := by simp [zeroU]
      have h1 : zeroU p d (0 + 1) = 0 := by simp [zeroU]
      rw [hl, h0, h1]
      have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
      have hm : p.m ≠ 0 := hp.m_pos.ne'
      have c2 : DQr p d (zeroU0 p d) 2 = 0 := by simp only [DQr, zeroU0, Matrix.cons_val]; ring
      have c0 : DQr p d (zeroU0 p d) 0 = 0 := by
        have h02 := red_lam hp d (zeroU0 p d)
        have e3 : zeroU0 p d 3 = 0 := rfl
        have e02 : zeroU0 p d 0 - zeroU0 p d 2 = 0 := by simp [zeroU0]
        rw [c2, hG, e3, e02] at h02
        linarith
      funext i
      fin_cases i
      · simp only [Fin.zero_eta, Pi.add_apply, DNr, Matrix.cons_val_zero, add_zero, Pi.zero_apply]
        exact c0
      · simp only [Fin.mk_one, Pi.add_apply, DNr, DQr, zeroU0, Matrix.cons_val_one,
          Matrix.cons_val_zero, Matrix.cons_val, add_zero, Pi.zero_apply]
        field_simp; ring
      · simp only [Fin.reduceFinMk, Pi.add_apply, DNr, Matrix.cons_val, add_zero, Pi.zero_apply]
        exact c2
      · simp only [Fin.reduceFinMk, Pi.add_apply, DNr, DQr, zeroU0, Matrix.cons_val,
          Pi.zero_apply]
        field_simp; ring
      · simp only [Fin.reduceFinMk, Pi.add_apply, DNr, DQr, zeroU0, Matrix.cons_val,
          Pi.zero_apply, add_zero]
        ring
    | succ t =>
      have hl3 : lagP d (zeroU p d) (t + 1) 3 = 0 := by
        change zeroU p d t 3 = 0
        by_cases ht : t = 0
        · simp [zeroU, ht, zeroU0]
        · simp [zeroU, ht]
      have h0 : zeroU p d (t + 1) = 0 := by simp [zeroU]
      have h1 : zeroU p d (t + 1 + 1) = 0 := by simp [zeroU]
      rw [h0, h1]
      funext i
      fin_cases i <;> simp [DQr, DNr, hl3]
  · rw [hpi u h (t + 1)]
    have : lagP d u (t + 1) 3 = u t 3 := rfl
    rw [this, hlam u h t]; simp

/-! ## The case `G < 0` -/

/-- Woodford (2003), Ch. 7: `G < 0` makes the targeting coefficient and `c_G = κθ_R` negative. -/
theorem cG_neg (hp : p.Basic) (hG : Gw p < 0) : cG p < 0 := by
  unfold cG
  have hgb := gamb_pos hp
  have hψ := hp.ψ_pos
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  apply div_neg_of_pos_of_neg (by positivity)
  exact mul_neg_of_neg_of_pos hG hψ

/-- Woodford (2003), Ch. 7, (1.20) with `G < 0` (**NONEXISTENCE**): if `−2(1 + β) < κθ_R`, both
roots of the multiplier recursion lie outside the unit circle; every bounded perfect-foresight
solution then has `λ̂_{−1} = 0` and is zero. In particular for every inherited multiplier
`λ̂_{−1} ≠ 0` the linearised commitment system has NO bounded solution. -/
theorem ramsey_G_neg_nonexist (hp : p.Basic) (hG : Gw p < 0) (hc : -(2 * (1 + p.β)) < cG p)
    (d : Fin 5 → ℝ) (u : ℕ → Fin 5 → ℝ) (h : PF p d u) {B : ℝ} (hB : ∀ t k, |u t k| ≤ B) :
    d 3 = 0 ∧ ∀ t, u t = 0 := by
  have hc0 := cG_neg hp hG
  obtain ⟨-, hrec⟩ := pf_reduce hp hG.ne d u h
  have hs : |1 + p.β + cG p| < 1 + p.β := by
    rw [abs_lt]; constructor <;> linarith
  have hz := rec_bounded_zero hp.β_pos hp.β_lt_one hs hrec (lagP_bound d u hB)
  refine ⟨hz 0, fun t => ?_⟩
  rw [pf_eq_build hp hG.ne d u h t]
  have hl : (fun s => lagP d u s 3) = fun _ => 0 := funext hz
  rw [hl]
  funext k; fin_cases k <;> simp [buildU]

/-- `buildU` is linear in `(ℓ_{t+1}, ℓ_t)` with fixed coefficients. -/
theorem buildU_lin (p : Par) : ∃ a b : Fin 5 → ℝ, ∀ (ℓ : ℕ → ℝ) t k,
    buildU p ℓ t k = a k * ℓ (t + 1) + b k * ℓ t := by
  set y := -(p.θ * p.m * (p.σ + p.ω)) / Gw p
  refine ⟨![y, 1 / gamb p, y, 1, (1 - p.σ) * y - p.θ * p.m * p.σ -
    lamb p * (p.θ * p.m * p.σ * (y - p.σ * y)) - gamb p * y], ![0, -(1 / gamb p), 0, 0, 0],
    fun ℓ t k => ?_⟩
  fin_cases k <;> simp only [buildU, y, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- `buildU` of a bounded path is bounded. -/
theorem buildU_bounded (p : Par) {ℓ : ℕ → ℝ} {L : ℝ} (hL : ∀ t, |ℓ t| ≤ L) :
    ∃ B, ∀ t k, |buildU p ℓ t k| ≤ B := by
  obtain ⟨a, b, h⟩ := buildU_lin p
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  refine ⟨(∑ k, (|a k| + |b k|)) * L, fun t k => ?_⟩
  rw [h]
  calc |a k * ℓ (t + 1) + b k * ℓ t| ≤ |a k| * L + |b k| * L := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hL _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hL _) (abs_nonneg _))
    _ = (|a k| + |b k|) * L := by ring
    _ ≤ (∑ k, (|a k| + |b k|)) * L := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun k => |a k| + |b k|) (fun _ _ => by positivity)
          (Finset.mem_univ k)) hL0

/-- Woodford (2003), App. A.3 (tool): existence and uniqueness of the bounded solution once the
multiplier recursion has roots `z₁, z₂` with `|z₁| ≤ 1 < |z₂|`: for every `λ̂_{−1}` exactly one
bounded solution, with `λ̂_t = z₁^{t+1}λ̂_{−1}`. -/
theorem pf_exists_unique (hp : p.Basic) (hG : Gw p ≠ 0) {z1 z2 : ℝ}
    (h1 : p.β * z1 * z2 = 1) (h2 : p.β * (z1 + z2) = 1 + p.β + cG p) (hz1 : |z1| ≤ 1)
    (hz2 : 1 < |z2|) (d : Fin 5 → ℝ) :
    (∃ u, PF p d u ∧ (∃ B, ∀ t k, |u t k| ≤ B) ∧ ∀ t, u t 3 = z1 ^ (t + 1) * d 3) ∧
      ∀ u v, PF p d u → PF p d v → (∃ B, ∀ t k, |u t k| ≤ B) → (∃ B, ∀ t k, |v t k| ≤ B) →
        u = v := by
  have hβ := hp.β_pos
  have hr1 : p.β * z1 ^ 2 - (1 + p.β + cG p) * z1 + 1 = 0 := by
    rw [← h2]; linear_combination -h1
  refine ⟨?_, ?_⟩
  · set ℓ : ℕ → ℝ := fun t => z1 ^ t * d 3
    have hℓ : ∀ t, p.β * ℓ (t + 2) - (1 + p.β + cG p) * ℓ (t + 1) + ℓ t = 0 := fun t => by
      simp only [ℓ]
      rw [pow_succ, pow_succ]
      linear_combination (z1 ^ t * d 3) * hr1
    have hb : ∀ t, |ℓ t| ≤ |d 3| := fun t => by
      simp only [ℓ, abs_mul, abs_pow]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hz1)
    exact ⟨buildU p ℓ, pf_build hp hG d ℓ (by simp [ℓ]) hℓ, buildU_bounded p hb,
      fun t => by simp [buildU, ℓ]⟩
  · intro u v hu hv ⟨Bu, hBu⟩ ⟨Bv, hBv⟩
    obtain ⟨-, ru⟩ := pf_reduce hp hG d u hu
    obtain ⟨-, rv⟩ := pf_reduce hp hG d v hv
    have pu := rec_pin hβ h1 h2 hz2 ru (lagP_bound d u hBu)
    have pv := rec_pin hβ h1 h2 hz2 rv (lagP_bound d v hBv)
    have hl : (fun s => lagP d u s 3) = fun s => lagP d v s 3 := by
      funext s; rw [pu s, pv s]; rfl
    funext t
    rw [pf_eq_build hp hG d u hu t, pf_eq_build hp hG d v hv t, hl]

/-- Woodford (2003), Ch. 7, (1.20) with `G < 0` and `κθ_R < −2(1 + β)` (**determinacy with an
oscillating stable root**): there is `z₁ ∈ (−1, 0)` such that for every inherited multiplier
there is exactly one bounded perfect-foresight solution, and its multiplier is
`λ̂_t = z₁^{t+1}λ̂_{−1}`. -/
theorem ramsey_G_neg_det (hp : p.Basic) (hG : Gw p < 0) (hc : cG p < -(2 * (1 + p.β))) :
    ∃ z1 : ℝ, -1 < z1 ∧ z1 < 0 ∧ ∀ d : Fin 5 → ℝ,
      (∃ u, PF p d u ∧ (∃ B, ∀ t k, |u t k| ≤ B) ∧ ∀ t, u t 3 = z1 ^ (t + 1) * d 3) ∧
      ∀ u v, PF p d u → PF p d v → (∃ B, ∀ t k, |u t k| ≤ B) → (∃ B, ∀ t k, |v t k| ≤ B) →
        u = v := by
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  obtain ⟨s, hsdef⟩ : ∃ s, s = 1 + p.β + cG p := ⟨_, rfl⟩
  have hs : s < -(1 + p.β) := by linarith
  have hD0 : 4 * p.β ≤ s ^ 2 := by nlinarith
  obtain ⟨D, hDdef⟩ : ∃ D, D = Real.sqrt (s ^ 2 - 4 * p.β) := ⟨_, rfl⟩
  have hD2 : D ^ 2 = s ^ 2 - 4 * p.β := by rw [hDdef]; exact Real.sq_sqrt (by linarith)
  have hDnn : 0 ≤ D := by rw [hDdef]; exact Real.sqrt_nonneg _
  obtain ⟨z1, hz1d⟩ : ∃ z, z = (s + D) / (2 * p.β) := ⟨_, rfl⟩
  obtain ⟨z2, hz2d⟩ : ∃ z, z = (s - D) / (2 * p.β) := ⟨_, rfl⟩
  have h1 : p.β * z1 * z2 = 1 := by rw [hz1d, hz2d]; field_simp; linear_combination -hD2
  have h2 : p.β * (z1 + z2) = s := by rw [hz1d, hz2d]; field_simp; ring
  have hle : z2 ≤ z1 := by
    rw [hz1d, hz2d]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hprod : (z1 + 1) * (z2 + 1) < 0 := by
    have e : p.β * ((z1 + 1) * (z2 + 1)) = 1 + p.β + s := by linear_combination h1 + h2
    have hneg : 1 + p.β + s < 0 := by linarith
    by_contra hh; push Not at hh
    nlinarith
  have hz1 : -1 < z1 := by by_contra hh; push Not at hh; nlinarith
  have hz2 : z2 < -1 := by by_contra hh; push Not at hh; nlinarith
  have hz10 : z1 < 0 := by
    by_contra hh; push Not at hh
    have : z1 * z2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh (by linarith)
    nlinarith
  refine ⟨z1, hz1, hz10, fun d => pf_exists_unique hp hG.ne h1 (by rw [h2, hsdef])
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_of_neg (by linarith)]; linarith) d⟩

/-- Woodford (2003), Ch. 7, (1.20) with `G < 0` at the boundary `κθ_R = −2(1 + β)` (**a unit
root at `−1`**): for every inherited multiplier exactly one bounded solution, with
`λ̂_t = (−1)^{t+1}λ̂_{−1}`, which does NOT converge to the steady state when `λ̂_{−1} ≠ 0`. -/
theorem ramsey_G_neg_unit (hp : p.Basic) (hG : Gw p < 0) (hc : cG p = -(2 * (1 + p.β)))
    (d : Fin 5 → ℝ) :
    (∃ u, PF p d u ∧ (∃ B, ∀ t k, |u t k| ≤ B) ∧ ∀ t, u t 3 = (-1) ^ (t + 1) * d 3) ∧
      ∀ u v, PF p d u → PF p d v → (∃ B, ∀ t k, |u t k| ≤ B) → (∃ B, ∀ t k, |v t k| ≤ B) →
        u = v := by
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  refine pf_exists_unique hp hG.ne (z2 := -(1 / p.β)) (by field_simp)
    (by rw [hc]; field_simp; ring) (by simp) ?_ d
  rw [abs_neg, abs_of_pos (by positivity), lt_div_iff₀ hβ]; linarith

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyDegenerate
