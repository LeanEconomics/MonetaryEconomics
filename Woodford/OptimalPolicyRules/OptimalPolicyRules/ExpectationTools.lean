/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.ForwardSolution
import Mathlib.Analysis.Complex.Basic

/-!
# Expectation tools shared by Chapter 8: faithfulness and complexified expectations

Woodford (2003), *Interest and Prices*, Chapter 8: §1.2, p. 541 (uniqueness of the optimum by
strict convexity), p. 557 (forward operators with complex roots), §2.2 (the determinacy analysis
of (2.20)), §3.1 (p. 585) and App. G.7–G.9, pp. 727–739 (forward inverses with a complex pair of
roots).

This module collects the expectation-system tools that several parts of the chapter use, so that
there is one copy of each.

* `Faithful`, `perfectForesight_faithful`: an expectation system is faithful when a nonnegative
  random variable with zero conditional expectation is zero (the pointwise stand-in for "almost
  surely"); perfect foresight is faithful.
* The complexified conditional expectation `EC` (applied to real and imaginary parts) with its
  algebra (`EC_add`, `EC_smul`, `EC_sub`, `EC_zero`, the pointwise forms `EC_add_fun`,
  `EC_const_mul`, `EC_sub_fun`, `EC_zero_fun`), `EC_ofReal`, `EC_conj`, the law of iterated
  expectations `EC_tower`, `EC_known`, `EC_of_known`, the bound `norm_EC_le` and the series
  interchange `EC_tsum`, `EC_tsum_geom`.
* Complex processes `AdaptedC`, `BoundedC` and the forward-inverse lemma over `ℂ`: the forward
  series `fwdC a u t = ∑ₖ aᵏ E_t u_{t+k}` solves `z_t = a E_t z_{t+1} + u_t` (`fwdC_solves`),
  is bounded and adapted (`fwdC_bounded`, `fwdC_adapted`), and is the only bounded solution
  (`forwardC_unique`, `fwdC_unique`).
-/

namespace Woodford.OptimalPolicyRules.ExpectationTools

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Faithful expectation systems -/

/-- Woodford (2003), p. 541 and §3.1, p. 585 (uniqueness of the optimum by strict convexity): an
expectation system is *faithful* when `E_t x = 0` for `x ≥ 0` forces `x = 0` (true under perfect
foresight; for genuine conditional expectations it is the "almost surely" qualifier). -/
def Faithful : Prop := ∀ t (x : Ω → ℝ), 0 ≤ x → 𝔼.E t x = 0 → x = 0

/-- Woodford (2003), p. 541: perfect foresight is faithful. -/
theorem perfectForesight_faithful : Faithful perfectForesight := fun _ _ _ h => h

/-- Woodford (2003), p. 593: the pointwise form of faithfulness. -/
theorem Faithful.eq_zero {𝔼 : ExpectationSystem Ω} (h : Faithful 𝔼) {t : ℕ} {y : Ω → ℝ}
    (hy : ∀ ω, 0 ≤ y ω) (hE : 𝔼.E t y = 0) (ω : Ω) : y ω = 0 :=
  congrFun (h t y hy hE) ω

/-! ### Linearity of `E_t` on functions -/

/-- `E_t` of a sum, as functions (Woodford (2003), App. G.7: linearity of `E_t`). -/
theorem E_fun_add (t : ℕ) (f g : Ω → ℝ) :
    𝔼.E t (fun ω => f ω + g ω) = fun ω => 𝔼.E t f ω + 𝔼.E t g ω :=
  map_add (𝔼.E t) f g

/-- `E_t` of a difference, as functions (Woodford (2003), App. G.7). -/
theorem E_fun_sub (t : ℕ) (f g : Ω → ℝ) :
    𝔼.E t (fun ω => f ω - g ω) = fun ω => 𝔼.E t f ω - 𝔼.E t g ω :=
  map_sub (𝔼.E t) f g

/-- `E_t` of a constant multiple, as functions (Woodford (2003), App. G.7). -/
theorem E_fun_mul (t : ℕ) (c : ℝ) (f : Ω → ℝ) :
    𝔼.E t (fun ω => c * f ω) = fun ω => c * 𝔼.E t f ω :=
  map_smul (𝔼.E t) c f

/-- `E_t` of the zero random variable (Woodford (2003), App. G.7). -/
theorem E_fun_zero (t : ℕ) : 𝔼.E t (fun _ => (0 : ℝ)) = fun _ => 0 := 𝔼.const t 0

/-! ### The complexified conditional expectation -/

/-- Woodford (2003), p. 557, §2.2 and App. G.7, pp. 727–730: the conditional expectation
extended `ℂ`-linearly to complex random variables, applied to the real and imaginary parts. -/
def EC (t : ℕ) (z : Ω → ℂ) : Ω → ℂ :=
  fun ω => ⟨𝔼.E t (fun ω' => (z ω').re) ω, 𝔼.E t (fun ω' => (z ω').im) ω⟩

/-- The real part of `EC_t z` is `E_t Re z` (Woodford (2003), App. G.7). -/
@[simp] theorem EC_re (t : ℕ) (z : Ω → ℂ) (ω : Ω) :
    (EC 𝔼 t z ω).re = 𝔼.E t (fun ω' => (z ω').re) ω := rfl

/-- The imaginary part of `EC_t z` is `E_t Im z` (Woodford (2003), App. G.7). -/
@[simp] theorem EC_im (t : ℕ) (z : Ω → ℂ) (ω : Ω) :
    (EC 𝔼 t z ω).im = 𝔼.E t (fun ω' => (z ω').im) ω := rfl

/-- A real random variable viewed as complex: `EC_t x = E_t x` (Woodford (2003), App. G.7). -/
theorem EC_ofReal (t : ℕ) (x : Ω → ℝ) :
    EC 𝔼 t (fun ω => (x ω : ℂ)) = fun ω => (𝔼.E t x ω : ℂ) := by
  funext ω
  apply Complex.ext
  · rfl
  · simp only [EC_im, Complex.ofReal_im, E_fun_zero]

/-- `EC_t` is additive (Woodford (2003), App. G.7). -/
theorem EC_add (t : ℕ) (z w : Ω → ℂ) : EC 𝔼 t (z + w) = EC 𝔼 t z + EC 𝔼 t w := by
  funext ω
  apply Complex.ext
  · exact congrFun (map_add (𝔼.E t) (fun ω' => (z ω').re) (fun ω' => (w ω').re)) ω
  · exact congrFun (map_add (𝔼.E t) (fun ω' => (z ω').im) (fun ω' => (w ω').im)) ω

/-- `EC_t` is additive, pointwise form (Woodford (2003), App. G.7). -/
theorem EC_add_fun (t : ℕ) (z w : Ω → ℂ) :
    EC 𝔼 t (fun ω => z ω + w ω) = fun ω => EC 𝔼 t z ω + EC 𝔼 t w ω :=
  EC_add 𝔼 t z w

/-- `EC_t` is `ℂ`-homogeneous (Woodford (2003), App. G.7). -/
theorem EC_smul (t : ℕ) (c : ℂ) (z : Ω → ℂ) : EC 𝔼 t (c • z) = c • EC 𝔼 t z := by
  funext ω
  apply Complex.ext
  · change 𝔼.E t (c.re • (fun ω' => (z ω').re) - c.im • fun ω' => (z ω').im) ω =
      c.re * 𝔼.E t (fun ω' => (z ω').re) ω - c.im * 𝔼.E t (fun ω' => (z ω').im) ω
    rw [map_sub, map_smul, map_smul]
    rfl
  · change 𝔼.E t (c.re • (fun ω' => (z ω').im) + c.im • fun ω' => (z ω').re) ω =
      c.re * 𝔼.E t (fun ω' => (z ω').im) ω + c.im * 𝔼.E t (fun ω' => (z ω').re) ω
    rw [map_add, map_smul, map_smul]
    rfl

/-- `EC_t` commutes with multiplication by a complex constant, pointwise form (Woodford (2003),
App. G.7). -/
theorem EC_const_mul (t : ℕ) (c : ℂ) (z : Ω → ℂ) :
    EC 𝔼 t (fun ω => c * z ω) = fun ω => c * EC 𝔼 t z ω :=
  EC_smul 𝔼 t c z

/-- `EC_t` of a difference (Woodford (2003), App. G.7). -/
theorem EC_sub (t : ℕ) (z w : Ω → ℂ) : EC 𝔼 t (z - w) = EC 𝔼 t z - EC 𝔼 t w := by
  rw [sub_eq_add_neg, EC_add, show -w = (-1 : ℂ) • w by simp, EC_smul]
  simp [sub_eq_add_neg]

/-- `EC_t` of a difference, pointwise form (Woodford (2003), App. G.7). -/
theorem EC_sub_fun (t : ℕ) (z w : Ω → ℂ) :
    EC 𝔼 t (fun ω => z ω - w ω) = fun ω => EC 𝔼 t z ω - EC 𝔼 t w ω :=
  EC_sub 𝔼 t z w

/-- `EC_t 0 = 0` (Woodford (2003), App. G.7). -/
theorem EC_zero (t : ℕ) : EC 𝔼 t (0 : Ω → ℂ) = 0 := by
  have := EC_smul 𝔼 t 0 (0 : Ω → ℂ)
  simpa using this

/-- `EC_t 0 = 0`, pointwise form (Woodford (2003), App. G.7). -/
theorem EC_zero_fun (t : ℕ) : EC 𝔼 t (fun _ => (0 : ℂ)) = fun _ => 0 :=
  EC_zero 𝔼 t

/-- `EC_t` commutes with complex conjugation (Woodford (2003), (2.20) and App. G.7). -/
theorem EC_conj (t : ℕ) (z : Ω → ℂ) :
    EC 𝔼 t (fun ω => (starRingEnd ℂ) (z ω)) = fun ω => (starRingEnd ℂ) (EC 𝔼 t z ω) := by
  funext ω
  apply Complex.ext
  · simp
  · simp only [EC_im, Complex.conj_im]
    rw [show (fun ω => -(z ω).im) = -(fun ω => (z ω).im) from rfl, map_neg]
    rfl

/-- The law of iterated expectations for `EC` (Woodford (2003), App. G.7). -/
theorem EC_tower {s t : ℕ} (hst : s ≤ t) (z : Ω → ℂ) : EC 𝔼 s (EC 𝔼 t z) = EC 𝔼 s z := by
  funext ω
  apply Complex.ext
  · exact congrFun (𝔼.tower hst (fun ω' => (z ω').re)) ω
  · exact congrFun (𝔼.tower hst (fun ω' => (z ω').im)) ω

/-- Information known at `s` is known at `t ≥ s`, for `EC` (Woodford (2003), App. G.7). -/
theorem EC_known {s t : ℕ} (hst : s ≤ t) (z : Ω → ℂ) : EC 𝔼 t (EC 𝔼 s z) = EC 𝔼 s z := by
  funext ω
  apply Complex.ext
  · exact congrFun (𝔼.known hst (fun ω' => (z ω').re)) ω
  · exact congrFun (𝔼.known hst (fun ω' => (z ω').im)) ω

/-- Woodford (2003), (2.20): a complex random variable known at `s` is known at `t ≥ s`. -/
theorem EC_of_known {s t : ℕ} (h : s ≤ t) {z : Ω → ℂ} (hz : EC 𝔼 s z = z) : EC 𝔼 t z = z := by
  rw [← hz, EC_known 𝔼 h]

/-- `EC_t` of a bounded complex random variable is bounded: `‖z‖ ≤ M ⇒ ‖EC_t z‖ ≤ 2M`
(Woodford (2003), p. 557 and App. G.7). -/
theorem norm_EC_le {M : ℝ} {z : Ω → ℂ} (hz : ∀ ω, ‖z ω‖ ≤ M) (t : ℕ) (ω : Ω) :
    ‖EC 𝔼 t z ω‖ ≤ 2 * M := by
  have h1 : |(EC 𝔼 t z ω).re| ≤ M :=
    𝔼.abs_E_le (fun ω' => (Complex.abs_re_le_norm _).trans (hz ω')) t ω
  have h2 : |(EC 𝔼 t z ω).im| ≤ M :=
    𝔼.abs_E_le (fun ω' => (Complex.abs_im_le_norm _).trans (hz ω')) t ω
  linarith [Complex.norm_le_abs_re_add_abs_im (EC 𝔼 t z ω)]

/-- `EC_t` commutes with a series of complex random variables dominated by a summable sequence
(Woodford (2003), App. G.7; the complex version of `ForwardSolution.E_tsum_dom`). -/
theorem EC_tsum {u : ℕ → ℝ} (hu : Summable u) {f : ℕ → Ω → ℂ} (hf : ∀ k ω, ‖f k ω‖ ≤ u k)
    (t : ℕ) (ω : Ω) :
    EC 𝔼 t (fun ω' => ∑' k, f k ω') ω = ∑' k, EC 𝔼 t (f k) ω := by
  have hs : ∀ ω', Summable (fun k => f k ω') := fun ω' => Summable.of_norm_bounded hu
    (fun k => hf k ω')
  have hsE : Summable (fun k => EC 𝔼 t (f k) ω) := Summable.of_norm_bounded (hu.mul_left 2)
    (fun k => norm_EC_le 𝔼 (hf k) t ω)
  apply Complex.ext
  · rw [EC_re, Complex.re_tsum hsE]
    have e : (fun ω' => (∑' k, f k ω').re) = fun ω' => ∑' k, (f k ω').re :=
      funext fun ω' => Complex.re_tsum (hs ω')
    rw [e, ForwardSolution.E_tsum_dom 𝔼 hu
      (fun k ω' => (Complex.abs_re_le_norm _).trans (hf k ω')) t ω]
    rfl
  · rw [EC_im, Complex.im_tsum hsE]
    have e : (fun ω' => (∑' k, f k ω').im) = fun ω' => ∑' k, (f k ω').im :=
      funext fun ω' => Complex.im_tsum (hs ω')
    rw [e, ForwardSolution.E_tsum_dom 𝔼 hu
      (fun k ω' => (Complex.abs_im_le_norm _).trans (hf k ω')) t ω]
    rfl

/-- Woodford (2003), (2.20): `E^ℂ_t` commutes with a geometrically dominated series. -/
theorem EC_tsum_geom {r M : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {f : ℕ → Ω → ℂ}
    (hf : ∀ k ω, ‖f k ω‖ ≤ r ^ k * M) (t : ℕ) (ω : Ω) :
    EC 𝔼 t (fun ω' => ∑' k, f k ω') ω = ∑' k, EC 𝔼 t (f k) ω :=
  EC_tsum 𝔼 ((summable_geometric_of_lt_one hr0 hr1).mul_right M) hf t ω

/-! ### Complex processes and the forward-inverse lemma over `ℂ` -/

/-- Woodford (2003), (2.20) and App. G.7: an adapted complex process. -/
def AdaptedC (z : ℕ → Ω → ℂ) : Prop := ∀ t, EC 𝔼 t (z t) = z t

/-- Woodford (2003), p. 557, (2.20) and App. G.7: a uniformly bounded complex process. -/
def BoundedC (z : ℕ → Ω → ℂ) : Prop := ∃ M, ∀ t ω, ‖z t ω‖ ≤ M

/-- Woodford (2003), (2.20): iterating a homogeneous complex forward equation
`d_t = a E_t d_{t+1}` gives `d_t = aᵏ E_t d_{t+k}`. -/
theorem forwardC_iterate {a : ℂ} {d : ℕ → Ω → ℂ} (hd : ∀ t, d t = a • EC 𝔼 t (d (t + 1)))
    (t k : ℕ) : d t = a ^ k • EC 𝔼 t (d (t + k)) := by
  induction k with
  | zero =>
    rw [pow_zero, one_smul, add_zero]
    calc d t = a • EC 𝔼 t (d (t + 1)) := hd t
      _ = EC 𝔼 t (a • EC 𝔼 t (d (t + 1))) := by rw [EC_smul, EC_tower 𝔼 le_rfl]
      _ = EC 𝔼 t (d t) := by rw [← hd t]
  | succ k ih =>
    rw [ih, hd (t + k), EC_smul, EC_tower 𝔼 (Nat.le_add_right t k), smul_smul, ← pow_succ,
      add_assoc]

/-- Woodford (2003), (2.20) and App. G.7–G.9 (forward uniqueness over `ℂ`): a complex forward
equation `z_t = a E_t z_{t+1} + u_t` with `‖a‖ < 1` has at most one bounded solution. -/
theorem forwardC_unique {a : ℂ} (ha : ‖a‖ < 1) {u z₁ z₂ : ℕ → Ω → ℂ}
    (h₁ : ∀ t, z₁ t = a • EC 𝔼 t (z₁ (t + 1)) + u t)
    (h₂ : ∀ t, z₂ t = a • EC 𝔼 t (z₂ (t + 1)) + u t)
    (hb₁ : BoundedC z₁) (hb₂ : BoundedC z₂) : z₁ = z₂ := by
  obtain ⟨M₁, hM₁⟩ := hb₁
  obtain ⟨M₂, hM₂⟩ := hb₂
  set d : ℕ → Ω → ℂ := fun t => z₁ t - z₂ t with hd_def
  have hd : ∀ t, d t = a • EC 𝔼 t (d (t + 1)) := by
    intro t
    simp only [hd_def, EC_sub, smul_sub]
    rw [h₁ t, h₂ t]; abel
  have hdb : ∀ t ω, ‖d t ω‖ ≤ M₁ + M₂ := fun t ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (norm_sub_le _ _).trans (add_le_add (hM₁ t ω) (hM₂ t ω))
  funext t ω
  have hle : ∀ k, ‖d t ω‖ ≤ ‖a‖ ^ k * (2 * (M₁ + M₂)) := by
    intro k
    rw [forwardC_iterate 𝔼 hd t k]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, norm_pow]
    gcongr
    exact norm_EC_le 𝔼 (hdb (t + k)) t ω
  have hlim : Tendsto (fun k : ℕ => ‖a‖ ^ k * (2 * (M₁ + M₂))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg a) ha).mul_const
      (2 * (M₁ + M₂))
  have h0 : ‖d t ω‖ ≤ 0 := ge_of_tendsto' hlim hle
  have : d t ω = 0 := norm_le_zero_iff.mp h0
  simpa [hd_def, sub_eq_zero] using this

/-- **Complex forward-inverse lemma, uniqueness** (Woodford (2003), App. G.7–G.9): for
`|a| < 1`, two bounded complex processes solving `z_t = a E_t z_{t+1} + u_t` at every date
coincide (the form with a common bound). -/
theorem fwdC_unique {a : ℂ} (ha : ‖a‖ < 1) {u z1 z2 : ℕ → Ω → ℂ}
    (h1 : ∀ t, z1 t = a • EC 𝔼 t (z1 (t + 1)) + u t)
    (h2 : ∀ t, z2 t = a • EC 𝔼 t (z2 (t + 1)) + u t)
    {M : ℝ} (hb1 : ∀ t ω, ‖z1 t ω‖ ≤ M) (hb2 : ∀ t ω, ‖z2 t ω‖ ≤ M) : z1 = z2 :=
  forwardC_unique 𝔼 ha h1 h2 ⟨M, hb1⟩ ⟨M, hb2⟩

/-- Woodford (2003), (2.20) and App. G.7–G.9: the complex forward inverse
`((1 − aL⁻¹)⁻¹ u)_t = ∑_k aᵏ E_t u_{t+k}` for complex `a`, `|a| < 1`. -/
noncomputable def fwdC (a : ℂ) (u : ℕ → Ω → ℂ) (t : ℕ) : Ω → ℂ :=
  fun ω => ∑' k, a ^ k * EC 𝔼 t (u (t + k)) ω

/-- Woodford (2003), (2.20): the terms of the complex forward series are geometrically
dominated. -/
theorem fwdC_term_le {a : ℂ} {M : ℝ} {u : ℕ → Ω → ℂ} (hu : ∀ t ω, ‖u t ω‖ ≤ M) (t k : ℕ)
    (ω : Ω) : ‖a ^ k * EC 𝔼 t (u (t + k)) ω‖ ≤ ‖a‖ ^ k * (2 * M) := by
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (norm_EC_le 𝔼 (hu (t + k)) t ω) (pow_nonneg (norm_nonneg _) _)

/-- Woodford (2003), App. G.7–G.9: `E_s ∑_k aᵏ E_t u_{t+k} = ∑_k aᵏ E_s u_{t+k}` for `s ≤ t`. -/
theorem EC_fwdC {a : ℂ} (ha : ‖a‖ < 1) {u : ℕ → Ω → ℂ} {M : ℝ} (hu : ∀ t ω, ‖u t ω‖ ≤ M)
    {s t : ℕ} (hst : s ≤ t) (ω : Ω) :
    EC 𝔼 s (fwdC 𝔼 a u t) ω = ∑' k, a ^ k * EC 𝔼 s (u (t + k)) ω := by
  have hsum : Summable (fun k : ℕ => ‖a‖ ^ k * (2 * M)) :=
    (summable_geometric_of_lt_one (norm_nonneg _) ha).mul_right _
  rw [show fwdC 𝔼 a u t = fun ω' => ∑' k, a ^ k * EC 𝔼 t (u (t + k)) ω' from rfl,
    EC_tsum 𝔼 hsum (fun k ω' => fwdC_term_le 𝔼 hu t k ω') s ω]
  refine tsum_congr fun k => ?_
  change EC 𝔼 s (a ^ k • EC 𝔼 t (u (t + k))) ω = _
  rw [EC_smul, EC_tower 𝔼 hst]
  rfl

/-- **Complex forward-inverse lemma, existence** (Woodford (2003), (2.20) and App. G.7–G.9): for
`|a| < 1` and a bounded adapted complex process `u`, `z_t = ∑_k aᵏ E_t u_{t+k}` solves
`z_t = a E_t z_{t+1} + u_t`. -/
theorem fwdC_solves {a : ℂ} {M : ℝ} (ha : ‖a‖ < 1) {u : ℕ → Ω → ℂ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) (hua : AdaptedC 𝔼 u) (t : ℕ) :
    fwdC 𝔼 a u t = a • EC 𝔼 t (fwdC 𝔼 a u (t + 1)) + u t := by
  funext ω
  have hs : Summable (fun k => a ^ k * EC 𝔼 t (u (t + k)) ω) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) ha).mul_right _)
      (fun k => fwdC_term_le 𝔼 hu t k ω)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [EC_fwdC 𝔼 ha hu (Nat.le_succ t)]
  change ∑' k, a ^ k * EC 𝔼 t (u (t + k)) ω = _
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, hua t, ← tsum_mul_left, add_comm]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Woodford (2003), (2.20): the complex forward series is bounded. -/
theorem fwdC_bounded {a : ℂ} {M : ℝ} (ha : ‖a‖ < 1) {u : ℕ → Ω → ℂ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) : ∀ t ω, ‖fwdC 𝔼 a u t ω‖ ≤ 2 * M / (1 - ‖a‖) := by
  intro t ω
  have hr0 := norm_nonneg a
  have hg : Summable (fun k : ℕ => ‖a‖ ^ k * (2 * M)) :=
    (summable_geometric_of_lt_one hr0 ha).mul_right _
  have hn : Summable (fun k => ‖a ^ k * EC 𝔼 t (u (t + k)) ω‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => fwdC_term_le 𝔼 hu t k ω) hg
  calc ‖fwdC 𝔼 a u t ω‖ ≤ ∑' k, ‖a ^ k * EC 𝔼 t (u (t + k)) ω‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k : ℕ, ‖a‖ ^ k * (2 * M) :=
        Summable.tsum_le_tsum (fun k => fwdC_term_le 𝔼 hu t k ω) hn hg
    _ = 2 * M / (1 - ‖a‖) := by
        rw [tsum_mul_right, tsum_geometric_of_lt_one hr0 ha]; ring

/-- Woodford (2003), (2.20): the complex forward series is adapted. -/
theorem fwdC_adapted {a : ℂ} {M : ℝ} (ha : ‖a‖ < 1) {u : ℕ → Ω → ℂ}
    (hu : ∀ t ω, ‖u t ω‖ ≤ M) : AdaptedC 𝔼 (fwdC 𝔼 a u) := by
  intro t
  funext ω
  rw [EC_fwdC 𝔼 ha hu le_rfl]
  rfl

end Woodford.OptimalPolicyRules.ExpectationTools
