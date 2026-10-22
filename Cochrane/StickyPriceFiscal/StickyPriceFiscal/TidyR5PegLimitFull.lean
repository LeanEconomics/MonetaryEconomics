/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR5PegLimit

/-!
# The peg path converges uniformly on all of `[0, ∞)`, output included

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5: Figs. 5.1–5.3, pp. 122–125
(`FiscalNK.piDet`, `FiscalNK.xDet`, `FiscalNK.vDet`) and §5.7.1, (5.96), p. 166
(`CTSimple.ct_step_solution`, `CTSimple.ct_step_family`, `CTSimple.ct_step_debt`).

`TidyR5PegLimit` proves uniform convergence on compact intervals. Here both sides decay
exponentially, so the convergence is uniform on the whole half-line `[0, ∞)`:

* `abs_exp_neg_sub_le_exp`, `mul_exp_neg_le`: `|e^{−x} − e^{−y}| ≤ e^{−m}|x − y|` for
  `x, y ≥ m`, and `t e^{−at} ≤ 1/a`.
* `decay_bound_global`, `tendsto_bGlob`: for small `h` and **every** `t ≥ 0`,
  `|λ₁^{−⌊t/h⌋} − e^{−λ₂t}| ≤ e^{λ₂h/2}(2|k̂(h) − λ₂|/λ₂ + λ₂h) → 0`.
* `coef_path_uniform_global`: `a + c(h) λ₁^{−⌊t/h⌋} → a + c₀ e^{−λ₂t}` uniformly on `[0, ∞)` when
  `c(h) → c₀`.
* `peg_path_uniform_global`, `peg_debt_uniform_global`: inflation per unit of time and debt.

**Output.** With IS slope `σh` and Phillips-curve slope `κh`, discrete output equals
`(p_j − (1 − ρh)p_{j+1})/κ` where `p = π/h` is inflation per unit of time, and this is `O(h)`:
the discrete output at date `⌊t/h⌋` **divided by `h`** is the continuous-time output.
`xDet_scaled` gives the closed form, `peg_output_uniform` the uniform convergence of `x/h` on
`[0, ∞)` to `x(t) = (λ₁(π₀ − i₀)e^{−λ₂t} + ρi₀)/κ`, and `peg_output_level_vanishes` shows that
unscaled discrete output tends to `0` uniformly, so `h¹` is the right power.
-/

namespace Cochrane.StickyPriceFiscal.TidyR5PegLimitFull

open Filter Topology TidyR5PegLimit

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §5.7.1, p. 166 (tool): for `x, y ≥ m`, `|e^{−x} − e^{−y}| ≤ e^{−m}|x − y|`. -/
theorem abs_exp_neg_sub_le_exp {x y m : ℝ} (hx : m ≤ x) (hy : m ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ Real.exp (-m) * |x - y| := by
  have key : ∀ a b : ℝ, m ≤ a → a ≤ b →
      Real.exp (-a) - Real.exp (-b) ≤ Real.exp (-m) * (b - a) := by
    intro a b ha hab
    have h1 := Real.add_one_le_exp (-(b - a))
    have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-a) ≤ Real.exp (-m) := Real.exp_le_exp.mpr (by linarith)
    rw [h2]
    have h4 : Real.exp (-a) - Real.exp (-a) * Real.exp (-(b - a)) ≤ Real.exp (-a) * (b - a) := by
      nlinarith [Real.exp_pos (-a)]
    exact h4.trans (mul_le_mul_of_nonneg_right h3 (by linarith))
  rcases le_total x y with hxy | hxy
  · have := key x y hx hxy
    have hm : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have := key y x hy hxy
    have hm : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- Cochrane (2023), §5.7.1, p. 166 (tool): `t e^{−at} ≤ 1/a` for `a > 0`. -/
theorem mul_exp_neg_le {a t : ℝ} (ha : 0 < a) : t * Real.exp (-(a * t)) ≤ 1 / a := by
  have h := Real.add_one_le_exp (a * t)
  have hp := Real.exp_pos (a * t)
  have hi : Real.exp (-(a * t)) = (Real.exp (a * t))⁻¹ := Real.exp_neg _
  rw [hi, le_div_iff₀ ha, mul_comm, ← mul_assoc, ← div_eq_mul_inv, div_le_one hp]
  linarith

/-- Cochrane (2023), §5.7.1, p. 166 (tool): the global decay bound
`e^{λ₂h/2}(2|k̂(h) − λ₂|/λ₂ + λ₂h)`. -/
noncomputable def bGlob (ρ σ κ h : ℝ) : ℝ :=
  Real.exp (CTSimple.lam2 ρ κ σ * h / 2) *
    (2 * |khat ρ σ κ h - CTSimple.lam2 ρ κ σ| / CTSimple.lam2 ρ κ σ + CTSimple.lam2 ρ κ σ * h)

/-- Cochrane (2023), Fig. 5.1 → (5.96): **the decay bound on all of `[0, ∞)`**: if `h > 0` and
`k̂(h) ≥ λ₂/2`, then for every `t ≥ 0`, `|λ₁^{−⌊t/h⌋} − e^{−λ₂t}| ≤ bGlob h`. -/
theorem decay_bound_global {ρ σ κ h t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hh : 0 < h)
    (hk : CTSimple.lam2 ρ κ σ / 2 ≤ khat ρ σ κ h) (ht : 0 ≤ t) :
    |qh ρ σ κ h ^ ⌊t / h⌋₊ - Real.exp (-(CTSimple.lam2 ρ κ σ * t))| ≤ bGlob ρ σ κ h := by
  have ha := mul_pos hσ hκ
  set l := CTSimple.lam2 ρ κ σ with hl
  have hl2 : 0 < l := CTSimple.lam2_pos hκ hσ
  obtain ⟨hn1, hn2⟩ := floor_bounds hh ht
  set n := ⌊t / h⌋₊
  have hnh0 : 0 ≤ (n : ℝ) * h := by positivity
  rw [qh_pow_eq ha hh n]
  have hx : l / 2 * (t - h) ≤ khat ρ σ κ h * (n * h) := by
    have : l / 2 * (t - h) ≤ l / 2 * (n * h) := mul_le_mul_of_nonneg_left (by linarith)
      (by linarith)
    exact this.trans (mul_le_mul_of_nonneg_right hk hnh0)
  have hy : l / 2 * (t - h) ≤ l * t := by nlinarith
  refine (abs_exp_neg_sub_le_exp hx hy).trans ?_
  have hd : |khat ρ σ κ h * (n * h) - l * t| ≤ |khat ρ σ κ h - l| * t + l * h := by
    have e : khat ρ σ κ h * (n * h) - l * t =
        (khat ρ σ κ h - l) * (n * h) + l * ((n * h) - t) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hnh0]
      exact mul_le_mul_of_nonneg_left hn1 (abs_nonneg _)
    · rw [abs_mul, abs_of_pos hl2]
      refine mul_le_mul_of_nonneg_left ?_ hl2.le
      rw [abs_le]
      constructor <;> linarith
  have hsplit : Real.exp (-(l / 2 * (t - h))) =
      Real.exp (l * h / 2) * Real.exp (-(l / 2 * t)) := by
    rw [← Real.exp_add]; ring_nf
  have hte := mul_exp_neg_le (a := l / 2) (t := t) (by linarith)
  have he1 : Real.exp (-(l / 2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hE := Real.exp_pos (l * h / 2)
  have hE2 := Real.exp_pos (-(l / 2 * t))
  calc Real.exp (-(l / 2 * (t - h))) * |khat ρ σ κ h * (n * h) - l * t|
      ≤ Real.exp (-(l / 2 * (t - h))) * (|khat ρ σ κ h - l| * t + l * h) :=
        mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
    _ = Real.exp (l * h / 2) * (|khat ρ σ κ h - l| * (t * Real.exp (-(l / 2 * t))) +
          l * h * Real.exp (-(l / 2 * t))) := by rw [hsplit]; ring
    _ ≤ Real.exp (l * h / 2) * (|khat ρ σ κ h - l| * (1 / (l / 2)) + l * h * 1) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hE.le
        · exact mul_le_mul_of_nonneg_left hte (abs_nonneg _)
        · exact mul_le_mul_of_nonneg_left he1 (by positivity)
    _ = bGlob ρ σ κ h := by
        rw [bGlob, ← hl]
        field_simp

/-- Cochrane (2023), §5.7.1, p. 165: `bGlob h → 0` as `h → 0⁺`. -/
theorem tendsto_bGlob {ρ σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (bGlob ρ σ κ) (𝓝[>] 0) (𝓝 0) := by
  have ha := mul_pos hσ hκ
  set l := CTSimple.lam2 ρ κ σ
  have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun h => |khat ρ σ κ h - l|) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_khat (ρ := ρ) ha).sub_const l).abs
    rwa [sub_self, abs_zero] at this
  have hE : Tendsto (fun h => Real.exp (l * h / 2)) (𝓝[>] 0) (𝓝 (Real.exp (l * 0 / 2))) :=
    (Real.continuous_exp.tendsto _).comp (((hid.const_mul l)).div_const 2)
  have h2 := ((h1.const_mul 2).div_const l).add (hid.const_mul l)
  have := hE.mul h2
  simp only [mul_zero, zero_div, add_zero] at this
  exact this

/-- Cochrane (2023), §5.7.1, p. 165: eventually as `h → 0⁺`, `k̂(h) ≥ λ₂/2`. -/
theorem eventually_khat_ge {ρ σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), CTSimple.lam2 ρ κ σ / 2 ≤ khat ρ σ κ h := by
  have hl2 : 0 < CTSimple.lam2 ρ κ σ := CTSimple.lam2_pos hκ hσ
  exact ((tendsto_khat (ρ := ρ) (mul_pos hσ hκ)).eventually
    (lt_mem_nhds (by linarith : CTSimple.lam2 ρ κ σ / 2 < CTSimple.lam2 ρ κ σ))).mono
    fun _ h => h.le

/-- Cochrane (2023), Figs. 5.1–5.3 → (5.96): **uniform convergence on `[0, ∞)` of every path of
the form `a + c(h) λ₁^{−⌊t/h⌋}`** to `a + c₀ e^{−λ₂t}` when `c(h) → c₀`. -/
theorem coef_path_uniform_global {ρ σ κ a c0 : ℝ} {c : ℝ → ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hc : Tendsto c (𝓝[>] 0) (𝓝 c0)) :
    TendstoUniformlyOn (fun h t => a + c h * qh ρ σ κ h ^ ⌊t / h⌋₊)
      (fun t => a + c0 * Real.exp (-(CTSimple.lam2 ρ κ σ * t))) (𝓝[>] 0) (Set.Ici 0) := by
  refine tendstoUniformlyOn_of_abs_le (B := fun h => |c h - c0| + |c0| * bGlob ρ σ κ h) ?_ ?_
  · have h1 : Tendsto (fun h => |c h - c0|) (𝓝[>] 0) (𝓝 0) := by
      have := (hc.sub_const c0).abs
      rwa [sub_self, abs_zero] at this
    have := h1.add ((tendsto_bGlob (ρ := ρ) hσ hκ).const_mul |c0|)
    rwa [mul_zero, add_zero] at this
  · filter_upwards [eventually_small (ρ := ρ) (r := 1) one_pos, eventually_khat_ge (ρ := ρ) hσ hκ]
      with h ⟨hh, hb, _, _⟩ hk t ht
    obtain ⟨q0, q1⟩ := qh_mem (ρ := ρ) hσ hκ hh hb
    rw [show a + c h * qh ρ σ κ h ^ ⌊t / h⌋₊ -
        (a + c0 * Real.exp (-(CTSimple.lam2 ρ κ σ * t))) =
        c h * qh ρ σ κ h ^ ⌊t / h⌋₊ - c0 * Real.exp (-(CTSimple.lam2 ρ κ σ * t)) by ring]
    refine (abs_prod_sub_le (pow_nonneg q0.le _) (pow_le_one₀ q0.le q1.le)).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (decay_bound_global hσ hκ hh hk (Set.mem_Ici.mp ht)) (abs_nonneg _))

/-- Cochrane (2023), Figs. 5.1–5.3 → (5.96), p. 166: **inflation converges uniformly on all of
`[0, ∞)`**: along any family of bounded discrete equilibria, inflation per unit of time at date
`⌊t/h⌋` converges to `π(t)` uniformly in `t ≥ 0`. -/
theorem peg_path_uniform_global {r σ κ ρ v0 i0 s0 : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hκ : 0 < κ)
    {x π v : ℝ → ℝ}
    (hct : CTSimple.IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (X P V : ℝ → ℕ → Ω → ℝ)
    (hd : ∀ᶠ h in 𝓝[>] (0 : ℝ), FiscalNK.FTPLNK 𝔼 (σ * h) (1 - ρ * h) (κ * h) (1 - r * h)
      (fun _ _ => i0 * h) (fun _ _ => s0 * h) (fun _ => v0) (X h) (P h) (V h) ∧
      BoundedProc (P h) ∧ BoundedProc (V h))
    (ω : Ω) :
    TendstoUniformlyOn (fun h t => P h ⌊t / h⌋₊ ω / h) π (𝓝[>] 0) (Set.Ici 0) := by
  have ha := mul_pos hσ hκ
  set c := fun h => (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h *
    (v0 - i0 * h - s0 / r) with hc
  have hcl : Tendsto c (𝓝[>] 0) (𝓝 ((r + CTSimple.lam2 ρ κ σ) * (v0 - s0 / r))) := by
    have h1 := Links.tendsto_peg_impact (ρ := ρ) r ha
    have h2 : Tendsto (fun h : ℝ => v0 - i0 * h - s0 / r) (𝓝[>] 0) (𝓝 (v0 - i0 * 0 - s0 / r)) :=
      ((tendsto_const_nhds.sub ((tendsto_id.const_mul i0))).sub tendsto_const_nhds).mono_left
        nhdsWithin_le_nhds
    rw [mul_zero, sub_zero] at h2
    exact h1.mul h2
  refine ((coef_path_uniform_global (ρ := ρ) (a := i0) hσ hκ hcl).congr ?_).congr_right ?_
  · filter_upwards [eventually_small (ρ := ρ) hr, hd] with h ⟨hh, hb, hrh0, hrh1⟩
      ⟨hF, hπb, hvb⟩ t _
    have hπ := (FiscalNK.det_unique 𝔼 (mul_pos hσ hh) (mul_pos hκ hh) hb (by linarith)
      (by linarith) (i0 * h) v0 (s := fun _ => s0 * h) (Ms := |s0 * h|) (fun _ => le_rfl)
      hF hπb hvb).2.1
    simp only [hπ, hc]
    rw [piDet_scaled hh hrh0 hrh1]
  · intro t ht
    simp only
    rw [CTSimple.ct_step_solution hr hκ hσ hct t (Set.mem_Ici.mp ht)]
    ring

/-- Cochrane (2023), Figs. 5.1–5.3 → p. 166 (`CTSimple.ct_step_debt`): **debt converges uniformly
on all of `[0, ∞)`** to `v(t) = s̃₀/r + (v₀ − s̃₀/r)e^{−λ₂t}`. -/
theorem peg_debt_uniform_global {r σ κ ρ v0 i0 s0 : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hκ : 0 < κ)
    {x π v : ℝ → ℝ}
    (hct : CTSimple.IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (X P V : ℝ → ℕ → Ω → ℝ)
    (hd : ∀ᶠ h in 𝓝[>] (0 : ℝ), FiscalNK.FTPLNK 𝔼 (σ * h) (1 - ρ * h) (κ * h) (1 - r * h)
      (fun _ _ => i0 * h) (fun _ _ => s0 * h) (fun _ => v0) (X h) (P h) (V h) ∧
      BoundedProc (P h) ∧ BoundedProc (V h))
    (ω : Ω) :
    TendstoUniformlyOn (fun h t => V h ⌊t / h⌋₊ ω) v (𝓝[>] 0) (Set.Ici 0) := by
  set c := fun h => (v0 - i0 * h - s0 / r) * qh ρ σ κ h with hc
  have hq : Tendsto (qh ρ σ κ) (𝓝[>] 0) (𝓝 1) := by
    have h1 := Links.tendsto_lam1_scaled ρ σ κ
    have h2 : Tendsto (fun h => NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) (𝓝[>] 0) (𝓝 1) := by
      have hid : Tendsto (fun h : ℝ => h) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left
        nhdsWithin_le_nhds
      have := (h1.mul hid).const_add 1
      rw [mul_zero, add_zero] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh' : (h : ℝ) ≠ 0 := (Set.mem_Ioi.mp hh).ne'
      field_simp
      ring
    have := h2.inv₀ one_ne_zero
    rw [inv_one] at this
    exact this
  have hcl : Tendsto c (𝓝[>] 0) (𝓝 (v0 - s0 / r)) := by
    have h2 : Tendsto (fun h : ℝ => v0 - i0 * h - s0 / r) (𝓝[>] 0) (𝓝 (v0 - i0 * 0 - s0 / r)) :=
      ((tendsto_const_nhds.sub ((tendsto_id.const_mul i0))).sub tendsto_const_nhds).mono_left
        nhdsWithin_le_nhds
    rw [mul_zero, sub_zero] at h2
    have := h2.mul hq
    rwa [mul_one] at this
  refine ((coef_path_uniform_global (ρ := ρ) (a := s0 / r) hσ hκ hcl).congr ?_).congr_right ?_
  · filter_upwards [eventually_small (ρ := ρ) hr, hd] with h ⟨hh, hb, hrh0, hrh1⟩
      ⟨hF, hπb, hvb⟩ t _
    have hV := (FiscalNK.det_unique 𝔼 (mul_pos hσ hh) (mul_pos hκ hh) hb (by linarith)
      (by linarith) (i0 * h) v0 (s := fun _ => s0 * h) (Ms := |s0 * h|) (fun _ => le_rfl)
      hF hπb hvb).2.2
    have hsum : ∑' j, (1 - r * h) ^ j * (s0 * h) = s0 / r := pvS_const hrh0 hrh1 hh
    simp only [hV, hc, FiscalNK.vDet]
    rw [pvS_const hrh0 hrh1 hh, hsum, qh]
    ring
  · intro t ht
    have hvt := (CTSimple.ct_step_debt hr hκ hσ hct t (Set.mem_Ici.mp ht)).2
    simp only
    linarith

/-- Cochrane (2023), (5.2), p. 118 and Figs. 5.1–5.3 (tool): discrete output per period length,
`xDet/h = ρi₀/κ + [c(h)(v₀ − i₀h − s̃₀/r) e(h)/κ] λ₁^{−n}` with
`c(h) = (1 − (1 − rh)/λ₁)/h` and `e(h) = (1 − (1 − ρh)/λ₁)/h`. -/
theorem xDet_scaled {r σ κ ρ v0 i0 s0 h : ℝ} (hκ : 0 < κ) (hh : 0 < h) (hrh0 : 0 < r * h)
    (hrh1 : r * h < 1) (n : ℕ) :
    FiscalNK.xDet (σ * h) (1 - ρ * h) (κ * h) (1 - r * h) (i0 * h) v0 (fun _ => s0 * h) n / h =
      ρ * i0 / κ + (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h *
        (v0 - i0 * h - s0 / r) *
        ((1 - (1 - ρ * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h) / κ *
        qh ρ σ κ h ^ n := by
  have hp : ∀ m : ℕ, FiscalNK.piDet (σ * h) (1 - ρ * h) (κ * h) (1 - r * h) (i0 * h) v0
      (fun _ => s0 * h) m = h * (i0 + (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h)
        (κ * h)) / h * (v0 - i0 * h - s0 / r) * qh ρ σ κ h ^ m) := fun m => by
    rw [← piDet_scaled (σ := σ) (ρ := ρ) hh hrh0 hrh1 m]
    field_simp
  rw [FiscalNK.xDet, hp, hp, pow_succ]
  generalize (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h *
    (v0 - i0 * h - s0 / r) = C
  have hq : qh ρ σ κ h = (NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h))⁻¹ := rfl
  rw [hq]
  generalize NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h) = L
  generalize (L⁻¹) ^ n = Q
  rw [div_eq_mul_inv (1 - ρ * h) L]
  field_simp
  ring

/-- Cochrane (2023), Figs. 5.1–5.3 → (5.92) and p. 166 (`CTSimple.ct_step_family`): **output
converges uniformly on `[0, ∞)` once divided by the period length**: along any family of bounded
discrete equilibria, `x^h_{⌊t/h⌋}/h → x(t) = (λ₁(π₀ − i₀)e^{−λ₂t} + ρi₀)/κ` uniformly in
`t ≥ 0` (IS slope `σh` and Phillips-curve slope `κh` make discrete output `h` times the
continuous-time output). -/
theorem peg_output_uniform {r σ κ ρ v0 i0 s0 : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hκ : 0 < κ)
    {x π v : ℝ → ℝ}
    (hct : CTSimple.IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (X P V : ℝ → ℕ → Ω → ℝ)
    (hd : ∀ᶠ h in 𝓝[>] (0 : ℝ), FiscalNK.FTPLNK 𝔼 (σ * h) (1 - ρ * h) (κ * h) (1 - r * h)
      (fun _ _ => i0 * h) (fun _ _ => s0 * h) (fun _ => v0) (X h) (P h) (V h) ∧
      BoundedProc (P h) ∧ BoundedProc (V h))
    (ω : Ω) :
    TendstoUniformlyOn (fun h t => X h ⌊t / h⌋₊ ω / h) x (𝓝[>] 0) (Set.Ici 0) := by
  have ha := mul_pos hσ hκ
  set c := fun h => (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h *
    (v0 - i0 * h - s0 / r) *
    ((1 - (1 - ρ * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h) / κ with hc
  set c0 := (r + CTSimple.lam2 ρ κ σ) * (v0 - s0 / r) * CTSimple.lam1 ρ κ σ / κ with hc0
  have hcl : Tendsto c (𝓝[>] 0) (𝓝 c0) := by
    have h1 := Links.tendsto_peg_impact (ρ := ρ) r ha
    have h3 := Links.tendsto_peg_impact (ρ := ρ) ρ ha
    rw [show ρ + CTSimple.lam2 ρ κ σ = CTSimple.lam1 ρ κ σ by
      linarith [CTSimple.lam_sub ρ κ σ]] at h3
    have h2 : Tendsto (fun h : ℝ => v0 - i0 * h - s0 / r) (𝓝[>] 0) (𝓝 (v0 - i0 * 0 - s0 / r)) :=
      ((tendsto_const_nhds.sub ((tendsto_id.const_mul i0))).sub tendsto_const_nhds).mono_left
        nhdsWithin_le_nhds
    rw [mul_zero, sub_zero] at h2
    exact ((h1.mul h2).mul h3).div_const κ
  refine ((coef_path_uniform_global (ρ := ρ) (a := ρ * i0 / κ) hσ hκ hcl).congr ?_).congr_right
    ?_
  · filter_upwards [eventually_small (ρ := ρ) hr, hd] with h ⟨hh, hb, hrh0, hrh1⟩
      ⟨hF, hπb, hvb⟩ t _
    have hx := (FiscalNK.det_unique 𝔼 (mul_pos hσ hh) (mul_pos hκ hh) hb (by linarith)
      (by linarith) (i0 * h) v0 (s := fun _ => s0 * h) (Ms := |s0 * h|) (fun _ => le_rfl)
      hF hπb hvb).1
    simp only [hx, hc]
    rw [xDet_scaled hκ hh hrh0 hrh1]
  · intro t ht
    have hπ0 := CTSimple.ct_step_solution hr hκ hσ hct 0 le_rfl
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hπ0
    have hxt := (CTSimple.ct_step_family hκ hσ hct.1 t (Set.mem_Ici.mp ht)).2
    simp only [hc0]
    rw [hxt, hπ0]
    field_simp
    ring

/-- Cochrane (2023), Figs. 5.1–5.3 → p. 166: **the unscaled discrete output vanishes**: along
any family of bounded discrete equilibria, `x^h_{⌊t/h⌋} → 0` uniformly on `[0, ∞)`; so `h¹` is
the scaling that matches the continuous-time output (`peg_output_uniform`). -/
theorem peg_output_level_vanishes {r σ κ ρ v0 i0 s0 : ℝ} (hr : 0 < r) (hσ : 0 < σ)
    (hκ : 0 < κ) {x π v : ℝ → ℝ}
    (hct : CTSimple.IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (X P V : ℝ → ℕ → Ω → ℝ)
    (hd : ∀ᶠ h in 𝓝[>] (0 : ℝ), FiscalNK.FTPLNK 𝔼 (σ * h) (1 - ρ * h) (κ * h) (1 - r * h)
      (fun _ _ => i0 * h) (fun _ _ => s0 * h) (fun _ => v0) (X h) (P h) (V h) ∧
      BoundedProc (P h) ∧ BoundedProc (V h))
    (ω : Ω) :
    TendstoUniformlyOn (fun h t => X h ⌊t / h⌋₊ ω) (fun _ => 0) (𝓝[>] 0) (Set.Ici 0) := by
  obtain ⟨K, hK⟩ := hct.1.2.1
  have hu := peg_output_uniform 𝔼 hr hσ hκ hct X P V hd ω
  rw [Metric.tendstoUniformlyOn_iff] at hu
  have hid : Tendsto (fun h : ℝ => h * (K + 1)) (𝓝[>] 0) (𝓝 0) := by
    have := ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (K + 1)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    rwa [zero_mul] at this
  refine tendstoUniformlyOn_of_abs_le (B := fun h => h * (K + 1)) hid ?_
  filter_upwards [hu 1 one_pos, self_mem_nhdsWithin] with h hh hpos t ht
  have hh0 : 0 < h := hpos
  have h1 := hh t ht
  rw [Real.dist_eq] at h1
  have h2 := hK t (Set.mem_Ici.mp ht)
  have h3 : |X h ⌊t / h⌋₊ ω / h| ≤ K + 1 := by
    have := abs_sub_abs_le_abs_sub (X h ⌊t / h⌋₊ ω / h) (x t)
    rw [abs_sub_comm (X h ⌊t / h⌋₊ ω / h)] at this
    linarith
  rw [sub_zero, show X h ⌊t / h⌋₊ ω = h * (X h ⌊t / h⌋₊ ω / h) by field_simp, abs_mul,
    abs_of_pos hh0]
  exact mul_le_mul_of_nonneg_left h3 hh0.le

end Cochrane.StickyPriceFiscal.TidyR5PegLimitFull
