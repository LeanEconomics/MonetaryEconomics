/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.Links

/-!
# The discrete-to-continuous limit of the whole peg path

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5: Figs. 5.1–5.3, pp. 122–125
(the discrete-time peg, `FiscalNK.piDet`) and §5.7.1, (5.96), p. 166 (the step example in
continuous time, `CTSimple.ct_step_solution`, `CTSimple.ct_step_debt`).

`Links` shows that the roots, the impact coefficient and the decay factor of the discrete peg
response converge to their continuous-time counterparts. This module proves the convergence of
the **whole path**, uniformly on every compact time interval `[0, T]`, as the period length
`h → 0⁺`.

With period length `h`, the discrete model has IS slope `σh`, Phillips-curve slope `κh`,
discount `β = 1 − ρh`, debt discount `1 − rh`, a peg at `i₀h` per period, surpluses `s̃₀h` per
period and initial debt `v₀`; continuous time `t` is date `⌊t/h⌋` and per-period inflation is
divided by `h` to give a rate.

## Main results

* `qh_pow_eq`, `tendsto_khat`: `λ₁^{−n} = e^{−k̂(h)·nh}` with `k̂(h) → λ₂`.
* `decay_bound`, `tendsto_decay_uniform`: `λ₁^{−⌊t/h⌋} → e^{−λ₂ t}` uniformly on `[0, T]`.
* `peg_response_uniform`: the peg response of `Links` (`FiscalNK`'s `(1 − ρ/λ₁)λ₁^{−t}`, per unit
  of time) converges uniformly on `[0, T]` to `CTSimple`'s `(r + λ₂)e^{−λ₂ t}`.
* `peg_disc_exists`: for small `h` the discrete equilibrium exists.
* `peg_path_uniform`: **every family of bounded discrete equilibria has inflation (per unit of
  time) converging uniformly on `[0, T]` to the continuous-time equilibrium inflation**
  `(r + λ₂)(v₀ − s̃₀/r)e^{−λ₂ t} + i₀`; `peg_debt_uniform`: so does the real value of debt.
-/

namespace Cochrane.StickyPriceFiscal.TidyR5PegLimit

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), Fig. 5.1, p. 122, with period length `h`: the per-period decay factor
`λ₁^{−1}` of the discrete peg response. -/
noncomputable def qh (ρ σ κ h : ℝ) : ℝ := (NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h))⁻¹

/-- Cochrane (2023), §5.7.1, p. 165, with period length `h`: the implied continuous decay rate
`k̂(h) = log(1 + h·g(h))/h`, `g = Links.scaledRoot`. -/
noncomputable def khat (ρ σ κ h : ℝ) : ℝ := Real.log (1 + h * Links.scaledRoot ρ σ κ h) / h

/-- Cochrane (2023), §5.7.1, p. 165 (tool): uniform convergence on a set from an eventual
uniform bound `|F_i − G| ≤ B_i` with `B_i → 0`. -/
theorem tendstoUniformlyOn_of_abs_le {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ} {G : ℝ → ℝ}
    {S : Set ℝ} {B : ι → ℝ} (hB : Tendsto B l (𝓝 0))
    (h : ∀ᶠ i in l, ∀ t ∈ S, |F i t - G t| ≤ B i) : TendstoUniformlyOn F G l S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h, hB.eventually (gt_mem_nhds hε)] with i hi hBi t ht
  rw [Real.dist_eq, abs_sub_comm]
  exact (hi t ht).trans_lt hBi

/-- Cochrane (2023), §5.7.1, p. 166 (tool): `e^{−x}` is 1-Lipschitz on `[0, ∞)`. -/
theorem abs_exp_neg_sub_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    intro a b ha hab
    have h1 := Real.add_one_le_exp (-(b - a))
    have h2 : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h4 : 0 ≤ 1 - Real.exp (-(b - a)) := by
      have : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    rw [h2]
    nlinarith [Real.exp_pos (-a)]
  rcases le_total x y with hxy | hxy
  · have := key x y hx hxy
    have hm : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith
  · have := key y x hy hxy
    have hm : Real.exp (-x) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith

/-- Cochrane (2023), Fig. 5.1 → (5.96) (tool): for `h > 0` and `σκ > 0`,
`λ₁^{−n} = e^{−k̂(h)·(nh)}`. -/
theorem qh_pow_eq {ρ σ κ h : ℝ} (ha : 0 < σ * κ) (hh : 0 < h) (n : ℕ) :
    qh ρ σ κ h ^ n = Real.exp (-(khat ρ σ κ h * (n * h))) := by
  have hpos : 0 < 1 + h * Links.scaledRoot ρ σ κ h := by
    have := mul_pos hh (Links.scaledRoot_pos (ρ := ρ) ha h)
    linarith
  rw [qh, Links.lam1_scaled_eq hh, inv_pow, khat,
    show Real.log (1 + h * Links.scaledRoot ρ σ κ h) / h * (n * h) =
      n * Real.log (1 + h * Links.scaledRoot ρ σ κ h) by field_simp,
    ← Real.log_pow, Real.exp_neg, Real.exp_log (pow_pos hpos n)]

/-- Cochrane (2023), §5.7.1, p. 165 (tool): `k̂(h) ≥ 0` for `h > 0`. -/
theorem khat_nonneg {ρ σ κ h : ℝ} (ha : 0 < σ * κ) (hh : 0 < h) : 0 ≤ khat ρ σ κ h := by
  have := mul_pos hh (Links.scaledRoot_pos (ρ := ρ) ha h)
  exact div_nonneg (Real.log_nonneg (by linarith)) hh.le

/-- Cochrane (2023), (5.6), p. 119 → §5.7.1, p. 165: as `h → 0⁺`, the implied decay rate
`k̂(h) = log λ₁/h` converges to the continuous-time root `λ₂`. -/
theorem tendsto_khat {ρ σ κ : ℝ} (ha : 0 < σ * κ) :
    Tendsto (khat ρ σ κ) (𝓝[>] 0) (𝓝 (CTSimple.lam2 ρ κ σ)) := by
  have hg : Tendsto (Links.scaledRoot ρ σ κ) (𝓝[>] 0) (𝓝 (CTSimple.lam2 ρ κ σ)) := by
    rw [← Links.scaledRoot_zero]
    exact ((Links.continuous_scaledRoot ρ σ κ).tendsto 0).mono_left nhdsWithin_le_nhds
  have hhg : Tendsto (fun h => 1 + h * Links.scaledRoot ρ σ κ h) (𝓝[>] 0)
      (𝓝 (1 + 0 * CTSimple.lam2 ρ κ σ)) :=
    tendsto_const_nhds.add ((tendsto_id.mono_left nhdsWithin_le_nhds).mul hg)
  rw [zero_mul, add_zero] at hhg
  have hlo : Tendsto (fun h => Links.scaledRoot ρ σ κ h / (1 + h * Links.scaledRoot ρ σ κ h))
      (𝓝[>] 0) (𝓝 (CTSimple.lam2 ρ κ σ)) := by
    have := hg.div hhg one_ne_zero
    rwa [div_one] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hg ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hy := mul_pos hh' (Links.scaledRoot_pos (ρ := ρ) ha h)
    have hl := Real.one_sub_inv_le_log_of_pos (by linarith :
      (0 : ℝ) < 1 + h * Links.scaledRoot ρ σ κ h)
    rw [khat, le_div_iff₀ hh']
    have hne : 1 + h * Links.scaledRoot ρ σ κ h ≠ 0 := by linarith
    have e : Links.scaledRoot ρ σ κ h / (1 + h * Links.scaledRoot ρ σ κ h) * h =
        1 - (1 + h * Links.scaledRoot ρ σ κ h)⁻¹ := by
      have e1 : (1 + h * Links.scaledRoot ρ σ κ h) * (1 + h * Links.scaledRoot ρ σ κ h)⁻¹ = 1 :=
        mul_inv_cancel₀ hne
      rw [div_eq_mul_inv]
      linear_combination e1
    rw [e]
    exact hl
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : 0 < h := hh
    have hy := mul_pos hh' (Links.scaledRoot_pos (ρ := ρ) ha h)
    have hl := Real.log_le_sub_one_of_pos (by linarith :
      (0 : ℝ) < 1 + h * Links.scaledRoot ρ σ κ h)
    rw [khat, div_le_iff₀ hh']
    linarith

/-- Cochrane (2023), §5.7.1, p. 166 (tool): for `h > 0` and `0 ≤ t`, `n = ⌊t/h⌋` satisfies
`nh ≤ t < nh + h`. -/
theorem floor_bounds {t h : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    (⌊t / h⌋₊ : ℝ) * h ≤ t ∧ t < (⌊t / h⌋₊ : ℝ) * h + h := by
  have h0 : 0 ≤ t / h := div_nonneg ht hh.le
  constructor
  · have := Nat.floor_le h0
    rwa [le_div_iff₀ hh] at this
  · have := Nat.lt_floor_add_one (t / h)
    rw [div_lt_iff₀ hh] at this
    linarith

/-- Cochrane (2023), Fig. 5.1 → (5.96): **the decay bound**: for `h > 0` and `t ∈ [0, T]`,
`|λ₁^{−⌊t/h⌋} − e^{−λ₂ t}| ≤ |k̂(h) − λ₂| T + λ₂ h`. -/
theorem decay_bound {ρ σ κ h T t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hh : 0 < h)
    (ht : t ∈ Set.Icc 0 T) :
    |qh ρ σ κ h ^ ⌊t / h⌋₊ - Real.exp (-(CTSimple.lam2 ρ κ σ * t))| ≤
      |khat ρ σ κ h - CTSimple.lam2 ρ κ σ| * T + CTSimple.lam2 ρ κ σ * h := by
  have ha := mul_pos hσ hκ
  have hl2 := CTSimple.lam2_pos (ρ := ρ) hκ hσ
  obtain ⟨hn1, hn2⟩ := floor_bounds hh ht.1
  set n := ⌊t / h⌋₊
  have hnh0 : 0 ≤ (n : ℝ) * h := by positivity
  rw [qh_pow_eq ha hh n]
  refine (abs_exp_neg_sub_le (mul_nonneg (khat_nonneg ha hh) hnh0)
    (mul_nonneg hl2.le ht.1)).trans ?_
  have e : khat ρ σ κ h * (n * h) - CTSimple.lam2 ρ κ σ * t =
      (khat ρ σ κ h - CTSimple.lam2 ρ κ σ) * (n * h) +
        CTSimple.lam2 ρ κ σ * ((n * h) - t) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg hnh0]
    exact mul_le_mul_of_nonneg_left (hn1.trans ht.2) (abs_nonneg _)
  · rw [abs_mul, abs_of_pos hl2]
    refine mul_le_mul_of_nonneg_left ?_ hl2.le
    rw [abs_le]
    constructor <;> linarith

/-- Cochrane (2023), Fig. 5.1 → (5.96): **the discrete decay `λ₁^{−⌊t/h⌋}` converges to
`e^{−λ₂ t}` uniformly on `[0, T]`** as the period length `h → 0⁺`. -/
theorem tendsto_decay_uniform {ρ σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (T : ℝ) :
    TendstoUniformlyOn (fun h t => qh ρ σ κ h ^ ⌊t / h⌋₊)
      (fun t => Real.exp (-(CTSimple.lam2 ρ κ σ * t))) (𝓝[>] 0) (Set.Icc 0 T) := by
  have ha := mul_pos hσ hκ
  refine tendstoUniformlyOn_of_abs_le
    (B := fun h => |khat ρ σ κ h - CTSimple.lam2 ρ κ σ| * T + CTSimple.lam2 ρ κ σ * h) ?_ ?_
  · have h1 : Tendsto (fun h => |khat ρ σ κ h - CTSimple.lam2 ρ κ σ|) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_khat (ρ := ρ) ha).sub_const (CTSimple.lam2 ρ κ σ)).abs
      rwa [sub_self, abs_zero] at this
    have h2 : Tendsto (fun h : ℝ => CTSimple.lam2 ρ κ σ * h) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (CTSimple.lam2 ρ κ σ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [mul_zero] at this
    have := (h1.mul_const T).add h2
    rwa [zero_mul, zero_add] at this
  · filter_upwards [self_mem_nhdsWithin] with h hh t ht
    exact decay_bound hσ hκ hh ht

/-- Cochrane (2023), §5.7.1, p. 166 (tool): `|c_h q_h(t) − c₀ e(t)|` is at most
`|c_h − c₀| + |c₀| |q_h(t) − e(t)|` when `0 ≤ q_h(t) ≤ 1`. -/
theorem abs_prod_sub_le {c c0 q e : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    |c * q - c0 * e| ≤ |c - c0| + |c0| * |q - e| := by
  have e1 : c * q - c0 * e = (c - c0) * q + c0 * (q - e) := by ring
  rw [e1]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg hq0]
    exact mul_le_of_le_one_right (abs_nonneg _) hq1
  · rw [abs_mul]

/-- Cochrane (2023), Fig. 5.1 (tool): for `h > 0`, `0 < λ₁^{−1} < 1`. -/
theorem qh_mem {ρ σ κ h : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hh : 0 < h) (hβ : 0 < 1 - ρ * h) :
    0 < qh ρ σ κ h ∧ qh ρ σ κ h < 1 := by
  have ha : 0 < σ * h * (κ * h) := by positivity
  have h1 := NKModel.one_lt_lam1 ha hβ
  exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ h1⟩

/-- Cochrane (2023), Figs. 5.1–5.3, pp. 122–125 → (5.96), p. 166, **the whole peg response**:
`FiscalNK`'s response `(1 − ρ/λ₁)λ₁^{−⌊t/h⌋}` per unit of time (`ρ = 1 − rh`) converges to
`CTSimple`'s `(r + λ₂)e^{−λ₂ t}` uniformly on `[0, T]` as `h → 0⁺`. -/
theorem peg_response_uniform {ρ σ κ : ℝ} (r : ℝ) (hσ : 0 < σ) (hκ : 0 < κ) (T : ℝ) :
    TendstoUniformlyOn
      (fun h t => (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h *
        qh ρ σ κ h ^ ⌊t / h⌋₊)
      (fun t => (r + CTSimple.lam2 ρ κ σ) * Real.exp (-(CTSimple.lam2 ρ κ σ * t)))
      (𝓝[>] 0) (Set.Icc 0 T) := by
  have ha := mul_pos hσ hκ
  set c := fun h => (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h with hc
  set c0 := r + CTSimple.lam2 ρ κ σ
  have hcl : Tendsto c (𝓝[>] 0) (𝓝 c0) := Links.tendsto_peg_impact r ha
  set Bd := fun h => |khat ρ σ κ h - CTSimple.lam2 ρ κ σ| * T + CTSimple.lam2 ρ κ σ * h
  have hBd : Tendsto Bd (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun h => |khat ρ σ κ h - CTSimple.lam2 ρ κ σ|) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_khat (ρ := ρ) ha).sub_const (CTSimple.lam2 ρ κ σ)).abs
      rwa [sub_self, abs_zero] at this
    have h2 : Tendsto (fun h : ℝ => CTSimple.lam2 ρ κ σ * h) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (CTSimple.lam2 ρ κ σ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [mul_zero] at this
    have := (h1.mul_const T).add h2
    rwa [zero_mul, zero_add] at this
  refine tendstoUniformlyOn_of_abs_le (B := fun h => |c h - c0| + |c0| * Bd h) ?_ ?_
  · have h1 : Tendsto (fun h => |c h - c0|) (𝓝[>] 0) (𝓝 0) := by
      have := (hcl.sub_const c0).abs
      rwa [sub_self, abs_zero] at this
    have := h1.add (hBd.const_mul |c0|)
    rwa [mul_zero, add_zero] at this
  · have hβ : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < 1 - ρ * h := by
      have hc1 : Tendsto (fun h : ℝ => 1 - ρ * h) (𝓝 0) (𝓝 (1 - ρ * 0)) :=
        tendsto_const_nhds.sub (tendsto_id.const_mul ρ)
      rw [mul_zero, sub_zero] at hc1
      exact nhdsWithin_le_nhds (hc1.eventually (lt_mem_nhds one_pos))
    filter_upwards [self_mem_nhdsWithin, hβ] with h hh hb t ht
    obtain ⟨q0, q1⟩ := qh_mem (ρ := ρ) hσ hκ hh hb
    refine (abs_prod_sub_le (pow_nonneg q0.le _) (pow_le_one₀ q0.le q1.le)).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (decay_bound hσ hκ hh ht)
      (abs_nonneg _))

/-- Cochrane (2023), p. 122 (tool): the present value of constant per-period surpluses `s̃₀h`
discounted at `1 − rh` is `s̃₀/r`. -/
theorem pvS_const {r s0 h : ℝ} (hrh0 : 0 < r * h) (hrh1 : r * h < 1) (hh : 0 < h) :
    FiscalNK.pvS (1 - r * h) (fun _ => s0 * h) = s0 / r := by
  have hr : 0 < r := pos_of_mul_pos_left hrh0 hh.le
  unfold FiscalNK.pvS
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by linarith) (by linarith)]
  field_simp
  ring

/-- Cochrane (2023), §5.7.1, p. 166 (tool): eventually as `h → 0⁺`, `h > 0`, `0 < 1 − ρh`,
`0 < rh < 1`. -/
theorem eventually_small {ρ r : ℝ} (hr : 0 < r) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ 0 < 1 - ρ * h ∧ 0 < r * h ∧ r * h < 1 := by
  have hc : ∀ c : ℝ, ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < 1 - c * h := fun c => by
    have hc1 : Tendsto (fun h : ℝ => 1 - c * h) (𝓝 0) (𝓝 (1 - c * 0)) :=
      tendsto_const_nhds.sub (tendsto_id.const_mul c)
    rw [mul_zero, sub_zero] at hc1
    exact nhdsWithin_le_nhds (hc1.eventually (lt_mem_nhds one_pos))
  filter_upwards [self_mem_nhdsWithin, hc ρ, hc r] with h hh h1 h2
  exact ⟨hh, h1, mul_pos hr hh, by linarith⟩

/-- Cochrane (2023), Figs. 5.1–5.3, pp. 122–125: **for small period length the discrete peg
equilibrium exists**: with `h` small there is an equilibrium of (5.15)–(5.16) with bounded
inflation and debt for the peg `i₀h`, surpluses `s̃₀h` and initial debt `v₀`. -/
theorem peg_disc_exists {r σ κ ρ v0 i0 s0 : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hκ : 0 < κ) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ x π v, FiscalNK.FTPLNK 𝔼 (σ * h) (1 - ρ * h) (κ * h) (1 - r * h)
      (fun _ _ => i0 * h) (fun _ _ => s0 * h) (fun _ => v0) x π v ∧ BoundedProc π ∧
      BoundedProc v := by
  filter_upwards [eventually_small (ρ := ρ) hr] with h ⟨hh, hb, hrh0, hrh1⟩
  obtain ⟨hd, -, hdπ, hdv⟩ := FiscalNK.det_eqm 𝔼 (ρ := 1 - r * h) (mul_pos hσ hh)
    (mul_pos hκ hh) hb (by linarith) (by linarith) (i0 * h) v0 (s := fun _ => s0 * h)
    (Ms := |s0 * h|) (fun _ => le_rfl)
  exact ⟨_, _, _, hd, hdπ, hdv⟩

/-- Cochrane (2023), Figs. 5.1–5.3 (tool): the discrete peg inflation per unit of time,
`piDet/h = i₀ + c(h)(v₀ − i₀h − s̃₀/r) λ₁^{−n}` with `c(h) = (1 − (1 − rh)/λ₁)/h`. -/
theorem piDet_scaled {r σ κ ρ v0 i0 s0 h : ℝ} (hh : 0 < h) (hrh0 : 0 < r * h)
    (hrh1 : r * h < 1) (n : ℕ) :
    FiscalNK.piDet (σ * h) (1 - ρ * h) (κ * h) (1 - r * h) (i0 * h) v0 (fun _ => s0 * h) n / h =
      i0 + (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h *
        (v0 - i0 * h - s0 / r) * qh ρ σ κ h ^ n := by
  rw [FiscalNK.piDet, pvS_const hrh0 hrh1 hh, qh, div_eq_mul_inv (1 - r * h)]
  field_simp

/-- Cochrane (2023), Figs. 5.1–5.3, pp. 122–125 → §5.7.1, (5.96), p. 166, **the full
discrete-to-continuous limit of the peg path**: take any family of bounded equilibria of the
discrete model with period length `h` (eventually as `h → 0⁺`) and any equilibrium `(x, π, v)` of
the continuous-time step example. Discrete inflation per unit of time at date `⌊t/h⌋` converges
to `π(t) = (r + λ₂)(v₀ − s̃₀/r)e^{−λ₂ t} + i₀` uniformly on `[0, T]`. -/
theorem peg_path_uniform {r σ κ ρ v0 i0 s0 : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hκ : 0 < κ)
    {x π v : ℝ → ℝ}
    (hct : CTSimple.IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (X P V : ℝ → ℕ → Ω → ℝ)
    (hd : ∀ᶠ h in 𝓝[>] (0 : ℝ), FiscalNK.FTPLNK 𝔼 (σ * h) (1 - ρ * h) (κ * h) (1 - r * h)
      (fun _ _ => i0 * h) (fun _ _ => s0 * h) (fun _ => v0) (X h) (P h) (V h) ∧
      BoundedProc (P h) ∧ BoundedProc (V h))
    (ω : Ω) (T : ℝ) :
    TendstoUniformlyOn (fun h t => P h ⌊t / h⌋₊ ω / h) π (𝓝[>] 0) (Set.Icc 0 T) := by
  have ha := mul_pos hσ hκ
  set c := fun h => (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h *
    (v0 - i0 * h - s0 / r) with hc
  set c0 := (r + CTSimple.lam2 ρ κ σ) * (v0 - s0 / r) with hc0
  have hcl : Tendsto c (𝓝[>] 0) (𝓝 c0) := by
    have h1 := Links.tendsto_peg_impact (ρ := ρ) r ha
    have h2 : Tendsto (fun h : ℝ => v0 - i0 * h - s0 / r) (𝓝[>] 0) (𝓝 (v0 - i0 * 0 - s0 / r)) :=
      ((tendsto_const_nhds.sub ((tendsto_id.const_mul i0))).sub tendsto_const_nhds).mono_left
        nhdsWithin_le_nhds
    rw [mul_zero, sub_zero] at h2
    exact h1.mul h2
  set Bd := fun h => |khat ρ σ κ h - CTSimple.lam2 ρ κ σ| * T + CTSimple.lam2 ρ κ σ * h
  have hBd : Tendsto Bd (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun h => |khat ρ σ κ h - CTSimple.lam2 ρ κ σ|) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_khat (ρ := ρ) ha).sub_const (CTSimple.lam2 ρ κ σ)).abs
      rwa [sub_self, abs_zero] at this
    have h2 : Tendsto (fun h : ℝ => CTSimple.lam2 ρ κ σ * h) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (CTSimple.lam2 ρ κ σ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [mul_zero] at this
    have := (h1.mul_const T).add h2
    rwa [zero_mul, zero_add] at this
  refine tendstoUniformlyOn_of_abs_le (B := fun h => |c h - c0| + |c0| * Bd h) ?_ ?_
  · have h1 : Tendsto (fun h => |c h - c0|) (𝓝[>] 0) (𝓝 0) := by
      have := (hcl.sub_const c0).abs
      rwa [sub_self, abs_zero] at this
    have := h1.add (hBd.const_mul |c0|)
    rwa [mul_zero, add_zero] at this
  · filter_upwards [eventually_small (ρ := ρ) hr, hd] with h ⟨hh, hb, hrh0, hrh1⟩
      ⟨hF, hπb, hvb⟩ t ht
    obtain ⟨q0, q1⟩ := qh_mem (ρ := ρ) hσ hκ hh hb
    have hπ := (FiscalNK.det_unique 𝔼 (mul_pos hσ hh) (mul_pos hκ hh) hb (by linarith)
      (by linarith) (i0 * h) v0 (s := fun _ => s0 * h) (Ms := |s0 * h|) (fun _ => le_rfl)
      hF hπb hvb).2.1
    rw [hπ]
    simp only
    rw [piDet_scaled hh hrh0 hrh1, CTSimple.ct_step_solution hr hκ hσ hct t ht.1]
    have e : i0 + (1 - (1 - r * h) / NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h)) / h *
        (v0 - i0 * h - s0 / r) * qh ρ σ κ h ^ ⌊t / h⌋₊ -
        ((r + CTSimple.lam2 ρ κ σ) * (v0 - s0 / r) *
          Real.exp (-(CTSimple.lam2 ρ κ σ * t)) + i0) =
        c h * qh ρ σ κ h ^ ⌊t / h⌋₊ - c0 * Real.exp (-(CTSimple.lam2 ρ κ σ * t)) := by
      simp only [hc, hc0]
      ring
    rw [e]
    refine (abs_prod_sub_le (pow_nonneg q0.le _) (pow_le_one₀ q0.le q1.le)).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (decay_bound hσ hκ hh ht)
      (abs_nonneg _))

/-- Cochrane (2023), Figs. 5.1–5.3, p. 122 → §5.7.1, p. 166 (`CTSimple.ct_step_debt`): **the real
value of debt converges too**: along any family of bounded discrete equilibria, debt at date
`⌊t/h⌋` converges to `v(t) = s̃₀/r + (v₀ − s̃₀/r)e^{−λ₂ t}` uniformly on `[0, T]`. -/
theorem peg_debt_uniform {r σ κ ρ v0 i0 s0 : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hκ : 0 < κ)
    {x π v : ℝ → ℝ}
    (hct : CTSimple.IsCTEquilibrium r σ κ ρ v0 (fun _ => i0) (fun _ => s0) x π v)
    (X P V : ℝ → ℕ → Ω → ℝ)
    (hd : ∀ᶠ h in 𝓝[>] (0 : ℝ), FiscalNK.FTPLNK 𝔼 (σ * h) (1 - ρ * h) (κ * h) (1 - r * h)
      (fun _ _ => i0 * h) (fun _ _ => s0 * h) (fun _ => v0) (X h) (P h) (V h) ∧
      BoundedProc (P h) ∧ BoundedProc (V h))
    (ω : Ω) (T : ℝ) :
    TendstoUniformlyOn (fun h t => V h ⌊t / h⌋₊ ω) v (𝓝[>] 0) (Set.Icc 0 T) := by
  have ha := mul_pos hσ hκ
  set c := fun h => (v0 - i0 * h - s0 / r) * qh ρ σ κ h with hc
  set c0 := v0 - s0 / r with hc0
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
  have hcl : Tendsto c (𝓝[>] 0) (𝓝 c0) := by
    have h2 : Tendsto (fun h : ℝ => v0 - i0 * h - s0 / r) (𝓝[>] 0) (𝓝 (v0 - i0 * 0 - s0 / r)) :=
      ((tendsto_const_nhds.sub ((tendsto_id.const_mul i0))).sub tendsto_const_nhds).mono_left
        nhdsWithin_le_nhds
    rw [mul_zero, sub_zero] at h2
    have := h2.mul hq
    rwa [mul_one] at this
  set Bd := fun h => |khat ρ σ κ h - CTSimple.lam2 ρ κ σ| * T + CTSimple.lam2 ρ κ σ * h
  have hBd : Tendsto Bd (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun h => |khat ρ σ κ h - CTSimple.lam2 ρ κ σ|) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_khat (ρ := ρ) ha).sub_const (CTSimple.lam2 ρ κ σ)).abs
      rwa [sub_self, abs_zero] at this
    have h2 : Tendsto (fun h : ℝ => CTSimple.lam2 ρ κ σ * h) (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (CTSimple.lam2 ρ κ σ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [mul_zero] at this
    have := (h1.mul_const T).add h2
    rwa [zero_mul, zero_add] at this
  refine tendstoUniformlyOn_of_abs_le (B := fun h => |c h - c0| + |c0| * Bd h) ?_ ?_
  · have h1 : Tendsto (fun h => |c h - c0|) (𝓝[>] 0) (𝓝 0) := by
      have := (hcl.sub_const c0).abs
      rwa [sub_self, abs_zero] at this
    have := h1.add (hBd.const_mul |c0|)
    rwa [mul_zero, add_zero] at this
  · filter_upwards [eventually_small (ρ := ρ) hr, hd] with h ⟨hh, hb, hrh0, hrh1⟩
      ⟨hF, hπb, hvb⟩ t ht
    obtain ⟨q0, q1⟩ := qh_mem (ρ := ρ) hσ hκ hh hb
    have hV := (FiscalNK.det_unique 𝔼 (mul_pos hσ hh) (mul_pos hκ hh) hb (by linarith)
      (by linarith) (i0 * h) v0 (s := fun _ => s0 * h) (Ms := |s0 * h|) (fun _ => le_rfl)
      hF hπb hvb).2.2
    have hvt := (CTSimple.ct_step_debt hr hκ hσ hct t ht.1).2
    have hsum : ∑' j, (1 - r * h) ^ j * (s0 * h) = s0 / r := pvS_const hrh0 hrh1 hh
    rw [hV]
    simp only [FiscalNK.vDet]
    rw [pvS_const hrh0 hrh1 hh, hsum]
    have hvv : v t = c0 * Real.exp (-(CTSimple.lam2 ρ κ σ * t)) + s0 / r := by
      rw [hc0]; linarith
    rw [hvv]
    have e : (v0 - i0 * h - s0 / r) * (NKModel.lam1 (σ * h) (1 - ρ * h) (κ * h))⁻¹ ^
        (⌊t / h⌋₊ + 1) + s0 / r - (c0 * Real.exp (-(CTSimple.lam2 ρ κ σ * t)) + s0 / r) =
        c h * qh ρ σ κ h ^ ⌊t / h⌋₊ - c0 * Real.exp (-(CTSimple.lam2 ρ κ σ * t)) := by
      simp only [hc, qh]
      ring
    rw [e]
    refine (abs_prod_sub_le (pow_nonneg q0.le _) (pow_le_one₀ q0.le q1.le)).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (decay_bound hσ hκ hh ht)
      (abs_nonneg _))

end Cochrane.StickyPriceFiscal.TidyR5PegLimit
