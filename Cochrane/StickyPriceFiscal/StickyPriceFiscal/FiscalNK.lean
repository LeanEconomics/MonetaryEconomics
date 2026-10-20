/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TwoSidedMA
import StickyPriceFiscal.SharedTools

/-!
# Fiscal theory in the simple new-Keynesian model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1.2, eqs. (5.11)–(5.16),
pp. 120–125, with Figs. 5.1 and 5.3.

The model (5.15)–(5.16) adds the linearised flow condition for the real value of debt,
`ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`, to the new-Keynesian model. The key modelling
device is the **predetermined real value of nominal debt** `b_{t+1} = v_t + i_t` (known at `t`):
the flow is `ρ v_{t+1} = b_{t+1} − π_{t+1} − s̃_{t+1}` (`predetermined_b`), and the model starts
from a given `b_0`. Everything is proved for an arbitrary expectation system, in the general form
`ρ v_{t+1} = v_t − π_{t+1} − e_{t+1}` (`Flow`, `Eqm`), which the long-term-debt model of §5.2
reuses with a different forcing `e`.

## Main results

* Determinacy for `0 < ρ < 1` ("ρ ≤ 1 provides the additional forward-looking root", p. 121):
  `eqm_unique_tvc` (uniqueness under the transversality condition `ρᵏ E_t v_{t+k} → 0`, any
  `0 < ρ ≤ 1`), `eqm_unique` (bounded `v`, `ρ < 1`), the explicit construction `recSeq`,
  `rec_bounded`, `gForce`, `Gser`, `piRec`, `vRec`, `xRec` with `eqm_exists`, and
  `eqm_determinate` (exactly one bounded equilibrium for every bounded adapted `i`, `e` and
  date-0 `b_0`); for (5.15)–(5.16): `fiscalNK_determinate`. Supporting facts: `flowShort_iff`,
  `ftplnk_iff`, `predetermined_b`, `eShort_adapted`, `eShort_bounded`, `nk_pi_adapted`,
  `flow_v_adapted`, `eqm_add` (linearity).
* `ρ = 1` (survey errors E20/E32): `dPert`, `wPert`, `xPert`, `pert_eqm`,
  `rho_one_not_determinate` — boundedness does not select, every bounded equilibrium has a
  one-parameter family of bounded companions — `rho_one_pert_violates_tvc` and
  `rho_one_tvc_unique` — the transversality condition selects at most one.
* (5.11)–(5.13): `valuation` (bounded `v` is the present value), `eq_5_13`, `eq_5_11_5_12`.
* Closed forms under a peg (deterministic `i ≡ a`, deterministic surpluses `s` with present
  value `S = pvS ρ s`): `pv_split`, `piDet`, `vDet`, `xDet`, `det_eqm`, `det_unique` —
  `π_t = a + (1 − ρ/λ₁)(b₀ − a − S) λ₁^{−t}` — and `pv_only` (the path depends on surpluses only
  through `S`, p. 125).
* Fig. 5.1 (unexpected permanent rise): `perm_rise` — `π_{1+j} = 1 − (1 − ρ/λ₁) λ₁^{−j}`,
  `κ x_{1+j} = (1 − β) − (1 − ρ/λ₁)(1 − β/λ₁) λ₁^{−j}`, `v_{1+j} = −λ₁^{−(j+1)}`;
  `perm_rise_pi0_pos` (`π₁ = ρ/λ₁ > 0`), `perm_rise_tendsto_one`, `perm_rise_pi0_strictAnti`
  (stickier prices, larger `π₁`), `perm_rise_kappa_zero` and `e27_not_exact` (κ → 0:
  `π_{1+j} → ρ`, not `1`: survey error E27), `perm_rise_kappa_atTop`; output
  `perm_rise_x0_neg_iff`, `perm_rise_x_tendsto`, `perm_rise_x0_pos_small_kappa` (output rises
  on impact for small κ: "higher interest rates do lead to lower output" is conditional).
* Fig. 5.3 (fiscal shock): `fiscal_shock` — `π_{1+j} = (1 − ρ/λ₁) λ₁^{−j}`,
  `fiscal_shock_pv_one` (`∑ ρʲ π_{1+j} = 1`), `fiscal_shock_sum` (`∑ π_{1+j} =
  (λ₁ − ρ)/(λ₁ − 1) > 1`: survey error E28), `fiscal_shock_x_pos`, `fiscal_shock_pi0`.
* General deterministic rate paths: `det_path`. Fig. 5.2 (anticipated rise, closed form):
  `hasSum_step`, `antB`, `antH`, `antC`, `antPi`, `anticipated_rise`, `anticipated_rise_tendsto`.
* The calibration of Figs. 5.3–5.4 (`r = 0.01`, `σ = 1`, `κ = 0.25`): `lam1_calib`,
  `fig53_impact` (impact response in `(0.394, 0.395)`: "0.4%"), `fig53_cumulative`
  (`∑ π_{1+j} ∈ (1.015, 1.016)`, E28).
-/

namespace Cochrane.StickyPriceFiscal.FiscalNK

open Filter Topology NKModel TwoSidedMA

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model -/

/-- Cochrane (2023), eq. (5.16), p. 121, general form: `ρ v_{t+1} = v_t − π_{t+1} − e_{t+1}`
(for one-period debt `e_{t+1} = s̃_{t+1} − i_t`, `eShort`). -/
def Flow (ρ : ℝ) (e v π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ρ • v (t + 1) = v t - π (t + 1) - e (t + 1)

/-- Cochrane (2023), eqs. (5.15)–(5.16), p. 121, general form: the new-Keynesian model, the flow
condition, and the date-0 flow `ρ v_0 = b_0 − π_0 − e_0` from the predetermined `b_0`. -/
def Eqm (σ β κ ρ : ℝ) (i e : ℕ → Ω → ℝ) (b0 : Ω → ℝ) (x π v : ℕ → Ω → ℝ) : Prop :=
  NK 𝔼 σ β κ i x π ∧ Flow ρ e v π ∧ ρ • v 0 = b0 - π 0 - e 0

/-- Cochrane (2023), eq. (5.16), p. 121: `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`. -/
def FlowShort (ρ : ℝ) (i s v π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ρ • v (t + 1) = v t + i t - π (t + 1) - s (t + 1)

/-- Cochrane (2023), eq. (5.16), p. 121: the forcing of the flow with one-period debt,
`e_0 = s̃_0`, `e_{t+1} = s̃_{t+1} − i_t`. -/
def eShort (i s : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => s 0
  | t + 1 => s (t + 1) - i t

/-- Cochrane (2023), eqs. (5.15)–(5.16), p. 121: the sticky-price fiscal-theory model with
one-period debt, started from the predetermined `b_0 = v_{−1} + i_{−1}`. -/
def FTPLNK (σ β κ ρ : ℝ) (i s : ℕ → Ω → ℝ) (b0 : Ω → ℝ) (x π v : ℕ → Ω → ℝ) : Prop :=
  NK 𝔼 σ β κ i x π ∧ FlowShort ρ i s v π ∧ ρ • v 0 = b0 - π 0 - s 0

/-- Cochrane (2023), eq. (5.16), p. 121: the one-period-debt flow is the general flow with
forcing `eShort`. -/
theorem flowShort_iff {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} :
    FlowShort ρ i s v π ↔ Flow ρ (eShort i s) v π := by
  refine forall_congr' fun t => ?_
  rw [show eShort i s (t + 1) = s (t + 1) - i t from rfl]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), eqs. (5.15)–(5.16), p. 121: the model in the general form. -/
theorem ftplnk_iff {σ β κ ρ : ℝ} {i s : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x π v : ℕ → Ω → ℝ} :
    FTPLNK 𝔼 σ β κ ρ i s b0 x π v ↔ Eqm 𝔼 σ β κ ρ i (eShort i s) b0 x π v := by
  unfold FTPLNK Eqm
  rw [flowShort_iff]
  rfl

/-- Cochrane (2023), p. 121: with adapted `v` and `i`, the real value of nominal debt
`b_{t+1} = v_t + i_t` is known at date `t` (predetermined), and the flow reads
`ρ v_{t+1} = b_{t+1} − π_{t+1} − s̃_{t+1}`. -/
theorem predetermined_b {ρ : ℝ} {i s v π : ℕ → Ω → ℝ} (hv : 𝔼.Adapted v) (hi : 𝔼.Adapted i)
    (h : FlowShort ρ i s v π) (t : ℕ) :
    𝔼.E t (v t + i t) = v t + i t ∧ ρ • v (t + 1) = (v t + i t) - π (t + 1) - s (t + 1) := by
  refine ⟨by rw [map_add, hv t, hi t], ?_⟩
  rw [h t]

/-- Cochrane (2023), eq. (5.16): `eShort` is adapted when `i` and `s` are. -/
theorem eShort_adapted {i s : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i) (hs : 𝔼.Adapted s) :
    𝔼.Adapted (eShort i s) := by
  intro t
  cases t with
  | zero => exact hs 0
  | succ t =>
    change 𝔼.E (t + 1) (s (t + 1) - i t) = s (t + 1) - i t
    rw [map_sub, hs, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hi t)]

/-- Cochrane (2023), eq. (5.16): `eShort` is bounded when `i` and `s` are. -/
theorem eShort_bounded {Mi Ms : ℝ} {i s : ℕ → Ω → ℝ} (hib : ∀ t ω, |i t ω| ≤ Mi)
    (hsb : ∀ t ω, |s t ω| ≤ Ms) : ∀ t ω, |eShort i s t ω| ≤ Ms + Mi := by
  intro t ω
  have hMi : 0 ≤ Mi := (abs_nonneg _).trans (hib 0 ω)
  cases t with
  | zero => exact (hsb 0 ω).trans (by linarith)
  | succ t =>
    change |s (t + 1) ω - i t ω| ≤ Ms + Mi
    exact (abs_sub _ _).trans (add_le_add (hsb _ ω) (hib t ω))

/-- Cochrane (2023), eq. (5.2), p. 118: in an equilibrium of (5.1)–(5.2) with adapted `i`,
inflation is adapted. -/
theorem nk_pi_adapted {σ β κ : ℝ} {i x π : ℕ → Ω → ℝ} (hi : 𝔼.Adapted i)
    (h : NK 𝔼 σ β κ i x π) : 𝔼.Adapted π := by
  have hxa := is_adapted 𝔼 hi h.1
  intro t
  conv_lhs => rw [h.2 t]
  rw [map_add, map_smul, map_smul, 𝔼.E_E_self, hxa t, ← h.2 t]

/-- Cochrane (2023), eq. (5.16), p. 121: with `ρ ≠ 0`, adapted `π`, `e` and a date-0 `b_0`,
the value of debt is adapted. -/
theorem flow_v_adapted {ρ : ℝ} (hρ : ρ ≠ 0) {e v π : ℕ → Ω → ℝ} {b0 : Ω → ℝ}
    (hπ : 𝔼.Adapted π) (he : 𝔼.Adapted e) (hb0 : 𝔼.E 0 b0 = b0) (hf : Flow ρ e v π)
    (h0 : ρ • v 0 = b0 - π 0 - e 0) : 𝔼.Adapted v := by
  intro t
  induction t with
  | zero =>
    have : v 0 = ρ⁻¹ • (b0 - π 0 - e 0) := by rw [← h0, smul_smul, inv_mul_cancel₀ hρ, one_smul]
    rw [this, map_smul, map_sub, map_sub, hb0, hπ 0, he 0]
  | succ t ih =>
    have : v (t + 1) = ρ⁻¹ • (v t - π (t + 1) - e (t + 1)) := by
      rw [← hf t, smul_smul, inv_mul_cancel₀ hρ, one_smul]
    rw [this, map_smul, map_sub, map_sub, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      hπ, he]

/-! ### Uniqueness -/

/-- Cochrane (2023), pp. 121–122 (selection by the transversality condition): for
`0 < ρ ≤ 1`, two equilibria with bounded inflation, the same `i`, `e`, `b_0`, and values of debt
satisfying `ρᵏ E_t v_{t+k} → 0`, coincide. The proof: the inflation difference `d` solves
`d_t = λ₁ E_t d_{t+1}`; the debt difference is then forced to be `d_t/(λ₁ − ρ)`; the flow makes
`d_{t+1} = d_t/λ₁` pathwise and the date-0 flow makes `d_0 = 0`. -/
theorem eqm_unique_tvc {σ β κ ρ Mi : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hi : 𝔼.Adapted i)
    (hib : ∀ t ω, |i t ω| ≤ Mi) (he : 𝔼.Adapted e) (hb0 : 𝔼.E 0 b0 = b0)
    {x π v x' π' v' : ℕ → Ω → ℝ} (h : Eqm 𝔼 σ β κ ρ i e b0 x π v)
    (h' : Eqm 𝔼 σ β κ ρ i e b0 x' π' v') (hπb : BoundedProc π) (hπb' : BoundedProc π')
    (htvc : SharedTools.TVC 𝔼 ρ v) (htvc' : SharedTools.TVC 𝔼 ρ v') :
    x = x' ∧ π = π' ∧ v = v' := by
  have ha := mul_pos hσ hκ
  set l1 := lam1 σ β κ with hl1
  have h1 : 1 < l1 := one_lt_lam1 ha hβ
  have hl0 : l1 ≠ 0 := by linarith
  have hlr : l1 - ρ ≠ 0 := by linarith
  obtain ⟨hx, hf⟩ := (nk_iff_factor 𝔼 hσ hκ hβ hi hib hπb).mp h.1
  obtain ⟨hx', hf'⟩ := (nk_iff_factor 𝔼 hσ hκ hβ hi hib hπb').mp h'.1
  have hπa := nk_pi_adapted 𝔼 hi h.1
  have hπa' := nk_pi_adapted 𝔼 hi h'.1
  have hva := flow_v_adapted 𝔼 hρ0.ne' hπa he hb0 h.2.1 h.2.2
  have hva' := flow_v_adapted 𝔼 hρ0.ne' hπa' he hb0 h'.2.1 h'.2.2
  obtain ⟨d, hd⟩ : ∃ d : ℕ → Ω → ℝ, d = fun t => π t - π' t := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℕ → Ω → ℝ, w = fun t => v t - v' t := ⟨_, rfl⟩
  -- d_t = λ₁ E_t d_{t+1}
  have hdd : ∀ t, d t = l1 • 𝔼.E t (d (t + 1)) := by
    intro t
    have e1 := hf t
    have e2 := hf' t
    simp only [hd]
    rw [map_sub, smul_sub]
    have : π t - π' t = (π t - l1 • 𝔼.E t (π (t + 1))) - (π' t - l1 • 𝔼.E t (π' (t + 1))) +
        (l1 • 𝔼.E t (π (t + 1)) - l1 • 𝔼.E t (π' (t + 1))) := by abel
    rw [this, e1, e2, sub_self, zero_add]
  have hEd : ∀ t k, 𝔼.E t (d (t + k)) = (l1⁻¹ ^ k) • d t := by
    intro t k
    have := 𝔼.forward_iterate hdd t k
    rw [this, smul_smul, ← mul_pow, inv_mul_cancel₀ hl0, one_pow, one_smul]
  -- the flow of the differences
  have hwf : ∀ t, ρ • w (t + 1) = w t - d (t + 1) := by
    intro t
    simp only [hw, hd]
    rw [smul_sub, h.2.1 t, h'.2.1 t]
    abel
  have hw0 : ρ • w 0 = -d 0 := by
    simp only [hw, hd]
    rw [smul_sub, h.2.2, h'.2.2]
    abel
  have hwa : 𝔼.Adapted w := fun t => by simp only [hw]; rw [map_sub, hva t, hva' t]
  -- y_t = w_t − d_t/(λ₁ − ρ) solves y_t = ρ E_t y_{t+1}
  obtain ⟨y, hy⟩ : ∃ y : ℕ → Ω → ℝ, y = fun t => w t - (l1 - ρ)⁻¹ • d t := ⟨_, rfl⟩
  have hyy : ∀ t, y t = ρ • 𝔼.E t (y (t + 1)) := by
    intro t
    have hE := congrArg (𝔼.E t) (hwf t)
    rw [map_smul, map_sub, hwa t] at hE
    have hE1 := hEd t 1
    simp only [hy]
    rw [map_sub, map_smul, smul_sub, smul_smul, hE, hE1]
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_one]
    field_simp
    ring
  have hy0 : y = 0 := by
    funext t ω
    have hit : ∀ k, y t ω = ρ ^ k * 𝔼.E t (y (t + k)) ω := fun k => by
      have := congrFun (𝔼.forward_iterate hyy t k) ω
      simpa using this
    have hlim : Tendsto (fun k => ρ ^ k * 𝔼.E t (y (t + k)) ω) atTop (𝓝 0) := by
      have hq0 : 0 ≤ ρ * l1⁻¹ := mul_nonneg hρ0.le (inv_nonneg.mpr (by linarith))
      have hq1 : ρ * l1⁻¹ < 1 := by
        rw [← div_eq_mul_inv, div_lt_one (by linarith)]; linarith
      have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
        ((l1 - ρ)⁻¹ * d t ω)
      rw [zero_mul] at hg
      have := (htvc t ω).sub ((htvc' t ω).add hg)
      rw [show (0 : ℝ) - (0 + 0) = 0 by norm_num] at this
      refine this.congr fun k => ?_
      simp only [hy, hw, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hEd t k]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_pow]
      ring
    have hconst : Tendsto (fun _ : ℕ => y t ω) atTop (𝓝 (y t ω)) := tendsto_const_nhds
    have := tendsto_nhds_unique (hconst.congr fun k => hit k) hlim
    simpa using this
  have hwd : ∀ t, w t = (l1 - ρ)⁻¹ • d t := fun t => by
    have := congrFun hy0 t
    simp only [hy, Pi.zero_apply] at this
    exact sub_eq_zero.mp this
  have hdz : ∀ t, d t = 0 := by
    intro t
    induction t with
    | zero =>
      funext ω
      have := congrFun hw0 ω
      rw [hwd 0] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.zero_apply] at this ⊢
      field_simp at this
      have : l1 * d 0 ω = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hl0
      · exact h
    | succ t ih =>
      funext ω
      have := congrFun (hwf t) ω
      rw [hwd, hwd, ih] at this
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply, mul_zero,
        zero_sub] at this
      field_simp at this
      have : l1 * d (t + 1) ω = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hl0
      · exact h
  have hππ : π = π' := funext fun t => by
    have := hdz t
    rw [hd] at this
    exact sub_eq_zero.mp this
  have hvv : v = v' := funext fun t => by
    have := hwd t
    rw [hdz t, smul_zero, hw] at this
    exact sub_eq_zero.mp this
  refine ⟨funext fun t => ?_, hππ, hvv⟩
  rw [hx t, hx' t, hππ]

/-- Cochrane (2023), p. 121: for `0 < ρ < 1`, bounded equilibria (bounded `π` and `v`) with the
same `i`, `e`, `b_0` coincide (boundedness implies the transversality condition). -/
theorem eqm_unique {σ β κ ρ Mi : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hi : 𝔼.Adapted i)
    (hib : ∀ t ω, |i t ω| ≤ Mi) (he : 𝔼.Adapted e) (hb0 : 𝔼.E 0 b0 = b0)
    {x π v x' π' v' : ℕ → Ω → ℝ} (h : Eqm 𝔼 σ β κ ρ i e b0 x π v)
    (h' : Eqm 𝔼 σ β κ ρ i e b0 x' π' v') (hπb : BoundedProc π) (hπb' : BoundedProc π')
    (hvb : BoundedProc v) (hvb' : BoundedProc v') : x = x' ∧ π = π' ∧ v = v' := by
  have tvc : ∀ {u : ℕ → Ω → ℝ}, BoundedProc u →
      ∀ t ω, Tendsto (fun k => ρ ^ k * 𝔼.E t (u (t + k)) ω) atTop (𝓝 0) := by
    intro u ⟨M, hM⟩ t ω
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).mul_const M
    rw [zero_mul] at hg
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun _ => abs_nonneg _) (fun k => ?_) hg
    rw [Function.comp_apply, abs_mul, abs_of_nonneg (pow_nonneg hρ0.le k)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM _) t ω) (pow_nonneg hρ0.le k)
  exact eqm_unique_tvc 𝔼 hσ hκ hβ hρ0 hρ1.le hi hib he hb0 h h' hπb hπb' (tvc hvb) (tvc hvb')

/-! ### Existence: the solution, constructed -/

/-- Cochrane (2023), p. 121 (construction of the unique solution): the backward recursion
`y_0 = k(b_0 − e_0 − ρ G_0)`, `y_{t+1} = a y_t + k(G_t − ρ G_{t+1} − e_{t+1})`. -/
def recSeq (a k ρ : ℝ) (G e : ℕ → Ω → ℝ) (b0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => k • (b0 - e 0 - ρ • G 0)
  | t + 1 => a • recSeq a k ρ G e b0 t + k • (G t - ρ • G (t + 1) - e (t + 1))

/-- Cochrane (2023), p. 121: a stable backward recursion `y_{t+1} = a y_t + h_{t+1}` with
`0 ≤ a < 1` and bounded `h` has bounded solutions, `|y_t| ≤ Y + H/(1 − a)`. -/
theorem rec_bounded {a Y H : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {y : ℕ → Ω → ℝ}
    (h0 : ∀ ω, |y 0 ω| ≤ Y) (hs : ∀ t ω, |y (t + 1) ω - a * y t ω| ≤ H) :
    ∀ t ω, |y t ω| ≤ Y + H / (1 - a) := by
  intro t ω
  refine SharedTools.bounded_of_rec (x := fun t => y t ω) ha0 ha1
    ((abs_nonneg _).trans (hs 0 ω)) (h0 ω) (fun t => ?_) t
  have e : y (t + 1) ω = (y (t + 1) ω - a * y t ω) + a * y t ω := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg ha0]
  linarith [hs t ω]

/-- Cochrane (2023), p. 121: the forcing of the debt-valuation part of the solution,
`g_t = E_t e_{t+1} + σκ/(λ₁ − ρ) F_t`. -/
noncomputable def gForce (σ β κ ρ : ℝ) (i e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t =>
  𝔼.E t (e (t + 1)) + (σ * κ / (lam1 σ β κ - ρ)) • 𝔼.forwardSeries (lam2 σ β κ) i t

/-- Cochrane (2023), p. 121: `G_t = ∑_{k≥0} ρᵏ E_t g_{t+k}`, the forward-solved debt root. -/
noncomputable def Gser (σ β κ ρ : ℝ) (i e : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries ρ (gForce 𝔼 σ β κ ρ i e)

/-- Cochrane (2023), p. 121: equilibrium inflation, solved backward with the stable root
`λ₁⁻¹` once the debt root `ρ⁻¹` has been solved forward. -/
noncomputable def piRec (σ β κ ρ : ℝ) (i e : ℕ → Ω → ℝ) (b0 : Ω → ℝ) : ℕ → Ω → ℝ :=
  recSeq (lam1 σ β κ)⁻¹ ((lam1 σ β κ - ρ) / lam1 σ β κ) ρ (Gser 𝔼 σ β κ ρ i e) e b0

/-- Cochrane (2023), p. 121: the equilibrium value of debt, `v_t = π_t/(λ₁ − ρ) + G_t`. -/
noncomputable def vRec (σ β κ ρ : ℝ) (i e : ℕ → Ω → ℝ) (b0 : Ω → ℝ) : ℕ → Ω → ℝ := fun t =>
  (lam1 σ β κ - ρ)⁻¹ • piRec 𝔼 σ β κ ρ i e b0 t + Gser 𝔼 σ β κ ρ i e t

/-- Cochrane (2023), eq. (5.2): equilibrium output, `x_t = κ⁻¹(π_t − β E_t π_{t+1})`. -/
noncomputable def xRec (σ β κ ρ : ℝ) (i e : ℕ → Ω → ℝ) (b0 : Ω → ℝ) : ℕ → Ω → ℝ := fun t =>
  κ⁻¹ • (piRec 𝔼 σ β κ ρ i e b0 t - β • 𝔼.E t (piRec 𝔼 σ β κ ρ i e b0 (t + 1)))

/-- Cochrane (2023), pp. 121–122 — **existence**: for `σ, κ > 0`, `0 < β`, `0 < ρ < 1`, bounded
adapted `i`, `e` and a bounded date-0 `b_0`, `(xRec, piRec, vRec)` is a bounded equilibrium. -/
theorem eqm_exists {σ β κ ρ Mi Me Mb : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hi : 𝔼.Adapted i)
    (hib : ∀ t ω, |i t ω| ≤ Mi) (he : 𝔼.Adapted e) (heb : ∀ t ω, |e t ω| ≤ Me)
    (hb0 : 𝔼.E 0 b0 = b0) (hbb : ∀ ω, |b0 ω| ≤ Mb) :
    Eqm 𝔼 σ β κ ρ i e b0 (xRec 𝔼 σ β κ ρ i e b0) (piRec 𝔼 σ β κ ρ i e b0)
        (vRec 𝔼 σ β κ ρ i e b0) ∧
      BoundedProc (xRec 𝔼 σ β κ ρ i e b0) ∧ BoundedProc (piRec 𝔼 σ β κ ρ i e b0) ∧
      BoundedProc (vRec 𝔼 σ β κ ρ i e b0) := by
  have ha := mul_pos hσ hκ
  have h1 : 1 < lam1 σ β κ := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have hlr : 0 < lam1 σ β κ - ρ := by linarith
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  set F := 𝔼.forwardSeries (lam2 σ β κ) i with hFdef
  have hFa : 𝔼.Adapted F := 𝔼.forwardSeries_adapted (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib
  obtain ⟨MF, hMF⟩ := 𝔼.forwardSeries_bounded (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib
  set g := gForce 𝔼 σ β κ ρ i e with hgdef
  have hga : 𝔼.Adapted g := fun t => by
    simp only [hgdef, gForce]
    rw [map_add, 𝔼.E_E_self, map_smul, hFa t]
  have hgb : ∀ t ω, |g t ω| ≤ Me + |σ * κ / (lam1 σ β κ - ρ)| * MF := by
    intro t ω
    simp only [hgdef, gForce, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (𝔼.abs_E_le (heb _) t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMF t ω) (abs_nonneg _)
  set G := Gser 𝔼 σ β κ ρ i e with hGdef
  have hGs : ∀ t, G t = ρ • 𝔼.E t (G (t + 1)) + g t :=
    𝔼.forwardSeries_solves hρ0.le hρ1 hgb hga
  have hGa : 𝔼.Adapted G := 𝔼.forwardSeries_adapted hρ0.le hρ1 hgb
  obtain ⟨MG, hMG⟩ := 𝔼.forwardSeries_bounded hρ0.le hρ1 hgb
  set k := (lam1 σ β κ - ρ) / lam1 σ β κ with hk
  set π := piRec 𝔼 σ β κ ρ i e b0 with hπdef
  have hπ0 : π 0 = k • (b0 - e 0 - ρ • G 0) := rfl
  have hπs : ∀ t, π (t + 1) = (lam1 σ β κ)⁻¹ • π t + k • (G t - ρ • G (t + 1) - e (t + 1)) :=
    fun t => rfl
  have hπa : 𝔼.Adapted π := by
    intro t
    induction t with
    | zero => rw [hπ0, map_smul, map_sub, map_sub, map_smul, hb0, he 0, hGa 0]
    | succ t ih =>
      rw [hπs, map_add, map_smul, map_smul, map_sub, map_sub, map_smul,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hGa t), hGa, he]
  have hπb : BoundedProc π := by
    refine ⟨|k| * (Mb + Me + ρ * MG) + |k| * (MG + ρ * MG + Me) / (1 - (lam1 σ β κ)⁻¹),
      rec_bounded hq0 hq1 (fun ω => ?_) (fun t ω => ?_)⟩
    · rw [hπ0]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (hbb ω) (heb 0 ω))) ?_)
      rw [abs_mul, abs_of_pos hρ0]
      exact mul_le_mul_of_nonneg_left (hMG 0 ω) hρ0.le
    · rw [hπs]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_sub_cancel_left,
        abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
        (add_le_add (hMG t ω) ?_)) (heb _ ω))
      rw [abs_mul, abs_of_pos hρ0]
      exact mul_le_mul_of_nonneg_left (hMG _ ω) hρ0.le
  have hfac : ∀ t, π t - lam1 σ β κ • 𝔼.E t (π (t + 1)) = -(σ * κ) • F t := by
    intro t
    funext ω
    have e1 : 𝔼.E t (π (t + 1)) = (lam1 σ β κ)⁻¹ • π t +
        k • (G t - ρ • 𝔼.E t (G (t + 1)) - 𝔼.E t (e (t + 1))) := by
      rw [hπs, map_add, map_smul, map_smul, map_sub, map_sub, map_smul, hπa t, hGa t]
    have e2 := congrFun (hGs t) ω
    have e1ω := congrFun e1 ω
    simp only [hgdef, gForce, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e1ω e2
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
    rw [e1ω]
    have e3 : G t ω - ρ * 𝔼.E t (G (t + 1)) ω - 𝔼.E t (e (t + 1)) ω =
        σ * κ / (lam1 σ β κ - ρ) * F t ω := by linarith
    rw [e3, hk]
    field_simp
    ring
  refine ⟨⟨(nk_iff_factor 𝔼 hσ hκ hβ hi hib hπb).mpr ⟨fun t => rfl, hfac⟩, fun t => ?_, ?_⟩,
    ?_, hπb, ?_⟩
  · funext ω
    have e := congrFun (hπs t) ω
    simp only [vRec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e ⊢
    rw [← hπdef, ← hGdef, e, hk]
    field_simp
    ring
  · funext ω
    have e := congrFun hπ0 ω
    simp only [vRec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at e ⊢
    rw [← hπdef, ← hGdef, e, hk]
    field_simp
    ring
  · obtain ⟨M, hM⟩ := hπb
    refine ⟨κ⁻¹ * (M + β * M), fun t ω => ?_⟩
    simp only [xRec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [← hπdef, abs_mul, abs_of_pos (inv_pos.mpr hκ)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hκ).le
    refine (abs_sub _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM (t + 1)) t ω) hβ.le
  · obtain ⟨M, hM⟩ := hπb
    refine ⟨(lam1 σ β κ - ρ)⁻¹ * M + MG, fun t ω => ?_⟩
    simp only [vRec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hπdef, ← hGdef]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hMG t ω))
    rw [abs_mul, abs_of_pos (inv_pos.mpr hlr)]
    exact mul_le_mul_of_nonneg_left (hM t ω) (inv_pos.mpr hlr).le

/-- Cochrane (2023), p. 121 — **determinacy** ("ρ ≤ 1 provides the additional forward-looking
root … and give a unique solution", for `0 < ρ < 1`): there is exactly one equilibrium with
bounded output, inflation and value of debt, for every bounded adapted `i`, `e` and every
bounded date-0 `b_0`. -/
theorem eqm_determinate {σ β κ ρ Mi Me Mb : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hi : 𝔼.Adapted i)
    (hib : ∀ t ω, |i t ω| ≤ Mi) (he : 𝔼.Adapted e) (heb : ∀ t ω, |e t ω| ≤ Me)
    (hb0 : 𝔼.E 0 b0 = b0) (hbb : ∀ ω, |b0 ω| ≤ Mb) :
    ∃ x π v, (Eqm 𝔼 σ β κ ρ i e b0 x π v ∧ BoundedProc x ∧ BoundedProc π ∧ BoundedProc v) ∧
      ∀ x' π' v', Eqm 𝔼 σ β κ ρ i e b0 x' π' v' → BoundedProc π' → BoundedProc v' →
        x' = x ∧ π' = π ∧ v' = v := by
  obtain ⟨h, hx, hπ, hv⟩ := eqm_exists 𝔼 hσ hκ hβ hρ0 hρ1 hi hib he heb hb0 hbb
  exact ⟨_, _, _, ⟨h, hx, hπ, hv⟩, fun x' π' v' h' hπ' hv' =>
    eqm_unique 𝔼 hσ hκ hβ hρ0 hρ1 hi hib he hb0 h' h hπ' hπ hv' hv⟩

/-- Cochrane (2023), eqs. (5.15)–(5.16), p. 121: the sticky-price fiscal-theory model with
one-period debt is determinate for `0 < ρ < 1`, under any bounded adapted interest-rate path
(a peg) and bounded adapted surpluses, from any bounded date-0 debt `b_0 = v_{−1} + i_{−1}`. -/
theorem fiscalNK_determinate {σ β κ ρ Mi Ms Mb : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {i s : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hi : 𝔼.Adapted i)
    (hib : ∀ t ω, |i t ω| ≤ Mi) (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ Ms)
    (hb0 : 𝔼.E 0 b0 = b0) (hbb : ∀ ω, |b0 ω| ≤ Mb) :
    ∃ x π v, (FTPLNK 𝔼 σ β κ ρ i s b0 x π v ∧ BoundedProc x ∧ BoundedProc π ∧
      BoundedProc v) ∧ ∀ x' π' v', FTPLNK 𝔼 σ β κ ρ i s b0 x' π' v' → BoundedProc π' →
        BoundedProc v' → x' = x ∧ π' = π ∧ v' = v := by
  simp only [ftplnk_iff]
  exact eqm_determinate 𝔼 hσ hκ hβ hρ0 hρ1 hi hib (eShort_adapted 𝔼 hi hs)
    (eShort_bounded hib hsb) hb0 hbb

/-! ### ρ = 1: boundedness does not select, the transversality condition does -/

/-- Cochrane (2023), p. 121 (ρ = 1): the deterministic inflation perturbation
`d_t = c λ₁^{−t}`, which solves the homogeneous model. -/
noncomputable def dPert (σ β κ c : ℝ) : ℕ → Ω → ℝ := fun t _ => c * (lam1 σ β κ)⁻¹ ^ t

/-- Cochrane (2023), p. 121 (ρ = 1): the matching debt perturbation
`w_t = −c ∑_{k ≤ t} λ₁^{−k}`. -/
noncomputable def wPert (σ β κ c : ℝ) : ℕ → Ω → ℝ := fun t _ =>
  -c * ∑ k ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ k

/-- Cochrane (2023), p. 121 (ρ = 1): the matching output perturbation from (5.2). -/
noncomputable def xPert (σ β κ c : ℝ) : ℕ → Ω → ℝ := fun t _ =>
  κ⁻¹ * (c * (lam1 σ β κ)⁻¹ ^ t - β * (c * (lam1 σ β κ)⁻¹ ^ (t + 1)))

/-- Cochrane (2023), eqs. (5.15)–(5.16): the model is linear — adding a solution of the
homogeneous model (`i = e = b_0 = 0`) to an equilibrium gives an equilibrium. -/
theorem eqm_add {σ β κ ρ : ℝ} {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x π v x' π' v' : ℕ → Ω → ℝ}
    (h : Eqm 𝔼 σ β κ ρ i e b0 x π v) (h' : Eqm 𝔼 σ β κ ρ 0 0 0 x' π' v') :
    Eqm 𝔼 σ β κ ρ i e b0 (x + x') (π + π') (v + v') := by
  obtain ⟨⟨his, hpc⟩, hf, h0⟩ := h
  obtain ⟨⟨his', hpc'⟩, hf', h0'⟩ := h'
  refine ⟨⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, ?_⟩
  · funext ω
    have a := congrFun (his t) ω
    have b := congrFun (his' t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add,
      Pi.zero_apply] at a b ⊢
    linarith
  · funext ω
    have a := congrFun (hpc t) ω
    have b := congrFun (hpc' t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add] at a b ⊢
    linarith
  · funext ω
    have a := congrFun (hf t) ω
    have b := congrFun (hf' t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a b ⊢
    linarith
  · funext ω
    have a := congrFun h0 ω
    have b := congrFun h0' ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at a b ⊢
    linarith

/-- Cochrane (2023), p. 121 (ρ = 1): `(xPert, dPert, wPert)` solves the homogeneous model with
`ρ = 1` for every `c`. -/
theorem pert_eqm {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (c : ℝ) :
    Eqm 𝔼 σ β κ 1 0 0 0 (xPert σ β κ c) (dPert σ β κ c) (wPert σ β κ c) := by
  have ha := mul_pos hσ hκ
  have hl0 : lam1 σ β κ ≠ 0 := (lam1_pos ha hβ).ne'
  have hq : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hroot := lam1_root ha hβ
  have hc : ∀ t (r : ℝ), 𝔼.E t (fun _ => r) = fun _ => r := fun t r => 𝔼.const t r
  have hd : ∀ s, dPert (Ω := Ω) σ β κ c s = fun _ => c * (lam1 σ β κ)⁻¹ ^ s := fun s => rfl
  refine ⟨(nk_iff_second 𝔼 hκ.ne').mpr ⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, ?_⟩
  · funext ω
    simp only [xPert, hd, hc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  · funext ω
    simp only [hd, hc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, mul_zero]
    linear_combination (c * (lam1 σ β κ)⁻¹ ^ (t + 2)) * hroot -
      c * (lam1 σ β κ)⁻¹ ^ t * (lam1 σ β κ * (lam1 σ β κ)⁻¹ + 1) * hq +
      (1 + β + σ * κ) * c * (lam1 σ β κ)⁻¹ ^ (t + 1) * hq
  · funext ω
    simp only [wPert, dPert, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply, one_mul,
      Finset.sum_range_succ _ (t + 1)]
    ring
  · funext ω
    simp only [wPert, dPert, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply, one_mul]
    simp

/-- Cochrane (2023), pp. 121, 136–137, survey errors E20/E32: with `ρ = 1` boundedness does
**not** determine the equilibrium. Every bounded equilibrium has bounded companions: for each
`c ≠ 0`, adding `(xPert, dPert, wPert)` gives another bounded equilibrium with different
inflation. -/
theorem rho_one_not_determinate [Nonempty Ω] {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} {x π v : ℕ → Ω → ℝ} (h : Eqm 𝔼 σ β κ 1 i e b0 x π v)
    (hxb : BoundedProc x) (hπb : BoundedProc π) (hvb : BoundedProc v) {c : ℝ} (hc : c ≠ 0) :
    Eqm 𝔼 σ β κ 1 i e b0 (x + xPert σ β κ c) (π + dPert σ β κ c) (v + wPert σ β κ c) ∧
      BoundedProc (x + xPert σ β κ c) ∧ BoundedProc (π + dPert σ β κ c) ∧
      BoundedProc (v + wPert σ β κ c) ∧ π + dPert σ β κ c ≠ π := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have hqt : ∀ t, (lam1 σ β κ)⁻¹ ^ t ≤ 1 := fun t => pow_le_one₀ hq0 hq1.le
  refine ⟨eqm_add 𝔼 h (pert_eqm 𝔼 hσ hκ hβ c), ?_, ?_, ?_, ?_⟩
  · obtain ⟨M, hM⟩ := hxb
    refine ⟨M + κ⁻¹ * (|c| + β * |c|), fun t ω => ?_⟩
    simp only [Pi.add_apply, xPert]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul, abs_of_pos (inv_pos.mpr hκ)]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ?_ ?_))
      (inv_pos.mpr hκ).le
    · rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 t)]
      exact mul_le_of_le_one_right (abs_nonneg c) (hqt t)
    · rw [abs_mul, abs_of_pos hβ, abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg c) (hqt _)) hβ.le
  · obtain ⟨M, hM⟩ := hπb
    refine ⟨M + |c|, fun t ω => ?_⟩
    simp only [Pi.add_apply, dPert]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 t)]
    exact mul_le_of_le_one_right (abs_nonneg c) (hqt t)
  · obtain ⟨M, hM⟩ := hvb
    refine ⟨M + |c| * (1 - (lam1 σ β κ)⁻¹)⁻¹, fun t ω => ?_⟩
    simp only [Pi.add_apply, wPert]
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul, abs_neg, abs_of_nonneg (Finset.sum_nonneg fun k _ => pow_nonneg hq0 k)]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    exact (hasSum_geometric_of_lt_one hq0 hq1).summable.sum_le_tsum _
      (fun k _ => pow_nonneg hq0 k) |>.trans (tsum_geometric_of_lt_one hq0 hq1).le
  · intro heq
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun heq 0) ω
    simp only [Pi.add_apply, dPert, pow_zero, mul_one, add_eq_left] at this
    exact hc this

/-- Cochrane (2023), pp. 121, 137 (ρ = 1, survey error E32): the transversality condition
`E_t v_{t+k} → 0` rules the companions out: if `v` satisfies it, `v + wPert c` does not
(`c ≠ 0`). -/
theorem rho_one_pert_violates_tvc {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {v : ℕ → Ω → ℝ} (htvc : ∀ t ω, Tendsto (fun k => (1 : ℝ) ^ k * 𝔼.E t (v (t + k)) ω) atTop
      (𝓝 0)) {c : ℝ} (hc : c ≠ 0) (t : ℕ) (ω : Ω) :
    ¬ Tendsto (fun k => (1 : ℝ) ^ k * 𝔼.E t ((v + wPert σ β κ c : ℕ → Ω → ℝ) (t + k)) ω)
      atTop (𝓝 0) := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  intro hcon
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).tendsto_sum_nat
  have hw : Tendsto (fun k => wPert σ β κ c (t + k) ω) atTop
      (𝓝 (-c * (1 - (lam1 σ β κ)⁻¹)⁻¹)) := by
    simp only [wPert]
    exact (hgeo.comp ((tendsto_add_atTop_nat (t + 1)).congr fun k => by omega)).const_mul (-c)
  have hsum := (htvc t ω).add hw
  rw [zero_add] at hsum
  have heq : (fun k => (1 : ℝ) ^ k * 𝔼.E t ((v + wPert σ β κ c : ℕ → Ω → ℝ) (t + k)) ω) =
      fun k => (1 : ℝ) ^ k * 𝔼.E t (v (t + k)) ω + wPert σ β κ c (t + k) ω := by
    funext k
    rw [Pi.add_apply, map_add, show 𝔼.E t (wPert σ β κ c (t + k)) = wPert σ β κ c (t + k) from
      𝔼.const t _]
    simp
  rw [heq] at hcon
  have := tendsto_nhds_unique hcon hsum
  have hne : (1 - (lam1 σ β κ)⁻¹)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have : c * (1 - (lam1 σ β κ)⁻¹)⁻¹ = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact hc h
  · exact hne h

/-- Cochrane (2023), pp. 121, 137 (ρ = 1): under the transversality condition
`E_t v_{t+k} → 0` there is at most one equilibrium with bounded inflation. -/
theorem rho_one_tvc_unique {σ β κ Mi : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {i e : ℕ → Ω → ℝ} {b0 : Ω → ℝ} (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi)
    (he : 𝔼.Adapted e) (hb0 : 𝔼.E 0 b0 = b0) {x π v x' π' v' : ℕ → Ω → ℝ}
    (h : Eqm 𝔼 σ β κ 1 i e b0 x π v) (h' : Eqm 𝔼 σ β κ 1 i e b0 x' π' v')
    (hπb : BoundedProc π) (hπb' : BoundedProc π')
    (htvc : ∀ t ω, Tendsto (fun k => 𝔼.E t (v (t + k)) ω) atTop (𝓝 0))
    (htvc' : ∀ t ω, Tendsto (fun k => 𝔼.E t (v' (t + k)) ω) atTop (𝓝 0)) :
    x = x' ∧ π = π' ∧ v = v' :=
  eqm_unique_tvc 𝔼 hσ hκ hβ one_pos le_rfl hi hib he hb0 h h' hπb hπb'
    (fun t ω => by simpa using htvc t ω) (fun t ω => by simpa using htvc' t ω)

/-! ### (5.11)–(5.13): unexpected inflation -/

/-- Cochrane (2023), p. 121 (valuation equation): with `0 ≤ ρ < 1`, a bounded adapted value of
debt satisfying (5.16) is the present value
`v_t = ∑_{k≥0} ρᵏ E_t[π_{t+k+1} + s̃_{t+k+1} − i_{t+k}]`. -/
theorem valuation {ρ Mi Ms Mπ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {i s v π : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hsb : ∀ t ω, |s t ω| ≤ Ms)
    (hπb : ∀ t ω, |π t ω| ≤ Mπ) (hva : 𝔼.Adapted v) (hvb : BoundedProc v)
    (h : FlowShort ρ i s v π) :
    v = 𝔼.forwardSeries ρ (fun t => 𝔼.E t (π (t + 1) + s (t + 1)) - i t) := by
  refine 𝔼.eq_forwardSeries hρ0 hρ1 (M := Mπ + Ms + Mi) (fun t ω => ?_) (fun t => ?_)
    (fun t => ?_) hvb
  · simp only [Pi.sub_apply]
    refine (abs_sub _ _).trans (add_le_add ?_ (hib t ω))
    rw [map_add, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (𝔼.abs_E_le (hπb _) t ω) (𝔼.abs_E_le (hsb _) t ω))
  · rw [map_sub, 𝔼.E_E_self, hi t]
  · have hE := congrArg (𝔼.E t) (h t)
    rw [map_smul, map_sub, map_sub, map_add, hva t, hi t] at hE
    funext ω
    have hω := congrFun hE ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add] at hω ⊢
    linarith

/-- Cochrane (2023), eq. (5.13), p. 121: with one-period debt and `0 < ρ < 1`, in any bounded
equilibrium of the flow (5.16) (sticky or flexible prices),
`ΔE_{t+1} π_{t+1} = ∑_{j≥1} ρʲ ΔE_{t+1}(i_{t+j} − π_{t+1+j}) − ∑_{j≥0} ρʲ ΔE_{t+1} s̃_{t+1+j}`,
both series converging. -/
theorem eq_5_13 {ρ Mi Ms Mπ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {i s v π : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hsb : ∀ t ω, |s t ω| ≤ Ms)
    (hπb : ∀ t ω, |π t ω| ≤ Mπ) (hva : 𝔼.Adapted v) (hvb : BoundedProc v)
    (h : FlowShort ρ i s v π) (t : ℕ) (ω : Ω) :
    Summable (fun j : ℕ => ρ ^ (j + 1) * (𝔼.E (t + 1) (i (t + 1 + j) - π (t + 1 + j + 1)) ω -
      𝔼.E t (i (t + 1 + j) - π (t + 1 + j + 1)) ω)) ∧
    Summable (fun j : ℕ => ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω)) ∧
    𝔼.E (t + 1) (π (t + 1)) ω - 𝔼.E t (π (t + 1)) ω =
      ∑' j : ℕ, ρ ^ (j + 1) * (𝔼.E (t + 1) (i (t + 1 + j) - π (t + 1 + j + 1)) ω -
        𝔼.E t (i (t + 1 + j) - π (t + 1 + j + 1)) ω) -
      ∑' j : ℕ, ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω) := by
  set u : ℕ → Ω → ℝ := fun t => 𝔼.E t (π (t + 1) + s (t + 1)) - i t with hu
  have hv := valuation 𝔼 hρ0 hρ1 hi hib hsb hπb hva hvb h
  have hub : ∀ t ω, |u t ω| ≤ Mπ + Ms + Mi := fun t ω => by
    simp only [hu, Pi.sub_apply]
    refine (abs_sub _ _).trans (add_le_add ?_ (hib t ω))
    rw [map_add, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (𝔼.abs_E_le (hπb _) t ω) (𝔼.abs_E_le (hsb _) t ω))
  -- X_k = π_{t+1+k+1} + s_{t+1+k+1} − i_{t+1+k}
  set X : ℕ → Ω → ℝ := fun k => π (t + 1 + k + 1) + s (t + 1 + k + 1) - i (t + 1 + k) with hX
  have hEu : ∀ r k, r ≤ t + 1 + k → 𝔼.E r (u (t + 1 + k)) = 𝔼.E r (X k) := by
    intro r k hr
    simp only [hu, hX]
    rw [map_sub, 𝔼.tower hr, map_sub]
  have hXk : ∀ k ω', |X k ω'| ≤ Mπ + Ms + Mi := fun k ω' => by
    simp only [hX, Pi.sub_apply, Pi.add_apply]
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (hπb _ ω') (hsb _ ω'))) (hib _ ω'))
  have hXb : ∀ r k ω', |𝔼.E r (X k) ω'| ≤ Mπ + Ms + Mi := fun r k ω' =>
    𝔼.abs_E_le (hXk k) r ω'
  have hgeo := summable_geometric_of_lt_one hρ0 hρ1
  have hsumE : ∀ r, Summable (fun k => ρ ^ k * 𝔼.E r (X k) ω) := fun r =>
    Summable.of_norm_bounded (hgeo.mul_right (Mπ + Ms + Mi)) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
      exact mul_le_mul_of_nonneg_left (hXb r k ω) (pow_nonneg hρ0 k))
  -- v_{t+1} and its date-t forecast as series
  have hv1 : v (t + 1) ω = ∑' k, ρ ^ k * 𝔼.E (t + 1) (X k) ω := by
    rw [hv]
    unfold ExpectationSystem.forwardSeries
    exact tsum_congr fun k => by rw [hEu (t + 1) k (by omega)]
  have hEv1 : 𝔼.E t (v (t + 1)) ω = ∑' k, ρ ^ k * 𝔼.E t (X k) ω := by
    rw [hv]
    have hb : ∀ k ω', |ρ ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω'| ≤ ρ ^ k * (Mπ + Ms + Mi) :=
      fun k ω' => by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hub _) _ ω') (pow_nonneg hρ0 k)
    unfold ExpectationSystem.forwardSeries
    rw [𝔼.E_tsum hρ0 hρ1 hb t ω]
    refine tsum_congr fun k => ?_
    have : (fun ω' => ρ ^ k * 𝔼.E (t + 1) (u (t + 1 + k)) ω') =
        ρ ^ k • 𝔼.E (t + 1) (u (t + 1 + k)) := rfl
    rw [this, map_smul, 𝔼.tower (Nat.le_succ t), hEu t k (by omega)]
    rfl
  -- the innovation of the flow
  have hinn : ρ * (v (t + 1) ω - 𝔼.E t (v (t + 1)) ω) =
      -(𝔼.E (t + 1) (π (t + 1)) ω - 𝔼.E t (π (t + 1)) ω) -
        (𝔼.E (t + 1) (s (t + 1)) ω - 𝔼.E t (s (t + 1)) ω) := by
    have h1 := congrFun (h t) ω
    have hE := congrFun (congrArg (𝔼.E t) (h t)) ω
    have hE1 := congrFun (congrArg (𝔼.E (t + 1)) (h t)) ω
    rw [map_smul, map_sub, map_sub, map_add, hva t, hi t] at hE
    rw [map_smul, map_sub, map_sub, map_add, hva (t + 1),
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hva t),
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hi t)] at hE1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 hE hE1
    linarith
  -- the two book series
  have hDb : ∀ (Y : ℕ → Ω → ℝ) (M : ℝ), (∀ k ω', |Y k ω'| ≤ M) → Summable (fun k : ℕ =>
      ρ ^ k * (𝔼.E (t + 1) (Y k) ω - 𝔼.E t (Y k) ω)) := fun Y M hY =>
    Summable.of_norm_bounded (hgeo.mul_right (M + M)) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans
        (add_le_add (𝔼.abs_E_le (hY k) _ ω) (𝔼.abs_E_le (hY k) _ ω))) (pow_nonneg hρ0 k))
  have hA0 := hDb (fun k => i (t + 1 + k) - π (t + 1 + k + 1)) (Mi + Mπ) (fun k ω' =>
    (abs_sub _ _).trans (add_le_add (hib _ ω') (hπb _ ω')))
  have hB0 := hDb (fun k => s (t + 1 + k)) Ms (fun k ω' => hsb _ ω')
  have hA : Summable (fun j : ℕ => ρ ^ (j + 1) * (𝔼.E (t + 1) (i (t + 1 + j) -
      π (t + 1 + j + 1)) ω - 𝔼.E t (i (t + 1 + j) - π (t + 1 + j + 1)) ω)) :=
    (hA0.mul_left ρ).congr fun j => by ring
  refine ⟨hA, hB0, ?_⟩
  have hB1 : Summable (fun k : ℕ => ρ ^ (k + 1) * (𝔼.E (t + 1) (s (t + 1 + (k + 1))) ω -
      𝔼.E t (s (t + 1 + (k + 1))) ω)) := (summable_nat_add_iff 1).mpr hB0
  rw [hB0.tsum_eq_zero_add]
  have hsplit : ρ * (v (t + 1) ω - 𝔼.E t (v (t + 1)) ω) =
      -(∑' j : ℕ, ρ ^ (j + 1) * (𝔼.E (t + 1) (i (t + 1 + j) - π (t + 1 + j + 1)) ω -
        𝔼.E t (i (t + 1 + j) - π (t + 1 + j + 1)) ω)) +
      ∑' k : ℕ, ρ ^ (k + 1) * (𝔼.E (t + 1) (s (t + 1 + (k + 1))) ω -
        𝔼.E t (s (t + 1 + (k + 1))) ω) := by
    rw [hv1, hEv1, ← (hsumE (t + 1)).tsum_sub (hsumE t), ← tsum_mul_left, ← tsum_neg,
      ← hA.neg.tsum_add hB1]
    refine tsum_congr fun k => ?_
    simp only [hX, map_sub, map_add, Pi.sub_apply, Pi.add_apply]
    ring_nf
  simp only [pow_zero, one_mul, add_zero] at hinn ⊢
  linarith

/-- Cochrane (2023), eqs. (5.11)–(5.12), p. 120 (flexible prices, `i_t = E_t π_{t+1}`, one-period
debt): `ΔE_{t+1} π_{t+1} = −ε_{Σs,t+1}` and `π_{t+1} = i_t − ε_{Σs,t+1}` with
`ε_{Σs,t+1} = ∑_{j≥0} ρʲ ΔE_{t+1} s̃_{t+1+j}`. -/
theorem eq_5_11_5_12 {ρ Mi Ms Mπ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {i s v π : ℕ → Ω → ℝ}
    (hi : 𝔼.Adapted i) (hib : ∀ t ω, |i t ω| ≤ Mi) (hsb : ∀ t ω, |s t ω| ≤ Ms)
    (hπ : 𝔼.Adapted π) (hπb : ∀ t ω, |π t ω| ≤ Mπ) (hva : 𝔼.Adapted v) (hvb : BoundedProc v)
    (hflex : ∀ t, i t = 𝔼.E t (π (t + 1))) (h : FlowShort ρ i s v π) (t : ℕ) (ω : Ω) :
    π (t + 1) ω - 𝔼.E t (π (t + 1)) ω =
      -∑' j : ℕ, ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω) ∧
    π (t + 1) ω = i t ω -
      ∑' j : ℕ, ρ ^ j * (𝔼.E (t + 1) (s (t + 1 + j)) ω - 𝔼.E t (s (t + 1 + j)) ω) := by
  obtain ⟨_, _, h13⟩ := eq_5_13 𝔼 hρ0 hρ1 hi hib hsb hπb hva hvb h t ω
  have hz : ∀ r j, r ≤ t + 1 + j → 𝔼.E r (i (t + 1 + j) - π (t + 1 + j + 1)) = 0 := by
    intro r j hr
    rw [map_sub, hflex, 𝔼.tower hr, sub_self]
  have h0 : ∑' j : ℕ, ρ ^ (j + 1) * (𝔼.E (t + 1) (i (t + 1 + j) - π (t + 1 + j + 1)) ω -
      𝔼.E t (i (t + 1 + j) - π (t + 1 + j + 1)) ω) = 0 := by
    have : ∀ j : ℕ, ρ ^ (j + 1) * (𝔼.E (t + 1) (i (t + 1 + j) - π (t + 1 + j + 1)) ω -
        𝔼.E t (i (t + 1 + j) - π (t + 1 + j + 1)) ω) = 0 := fun j => by
      rw [hz (t + 1) j (by omega), hz t j (by omega)]; simp
    exact (tsum_congr this).trans tsum_zero
  rw [h0, zero_sub, hπ (t + 1)] at h13
  have hE : 𝔼.E t (π (t + 1)) ω = i t ω := by rw [hflex t]
  refine ⟨h13, ?_⟩
  rw [← hE]
  linarith

/-! ### Closed forms under an interest-rate peg (Figs. 5.1 and 5.3) -/

/-- Cochrane (2023), p. 125: the present value `S = ∑_{j≥0} ρʲ s̃_j` of a deterministic surplus
path (from the shock date). -/
noncomputable def pvS (ρ : ℝ) (s : ℕ → ℝ) : ℝ := ∑' j, ρ ^ j * s j

/-- Cochrane (2023), pp. 122–125: equilibrium inflation under the peg `i ≡ a` with deterministic
surpluses and initial debt `b_0`: `π_t = a + (1 − ρ/λ₁)(b_0 − a − S) λ₁^{−t}`. -/
noncomputable def piDet (σ β κ ρ a b0 : ℝ) (s : ℕ → ℝ) (t : ℕ) : ℝ :=
  a + (1 - ρ * (lam1 σ β κ)⁻¹) * (b0 - a - pvS ρ s) * (lam1 σ β κ)⁻¹ ^ t

/-- Cochrane (2023), pp. 122–125: the equilibrium value of debt,
`v_t = (b_0 − a − S) λ₁^{−(t+1)} + ∑_{j≥0} ρʲ s̃_{t+1+j}`. -/
noncomputable def vDet (σ β κ ρ a b0 : ℝ) (s : ℕ → ℝ) (t : ℕ) : ℝ :=
  (b0 - a - pvS ρ s) * (lam1 σ β κ)⁻¹ ^ (t + 1) + ∑' j, ρ ^ j * s (t + 1 + j)

/-- Cochrane (2023), eq. (5.2): equilibrium output `x_t = κ⁻¹(π_t − β π_{t+1})`. -/
noncomputable def xDet (σ β κ ρ a b0 : ℝ) (s : ℕ → ℝ) (t : ℕ) : ℝ :=
  κ⁻¹ * (piDet σ β κ ρ a b0 s t - β * piDet σ β κ ρ a b0 s (t + 1))

/-- Cochrane (2023), p. 125: splitting a present value,
`∑ ρʲ s_{m+j} = s_m + ρ ∑ ρʲ s_{m+1+j}` (bounded `s`, `0 ≤ ρ < 1`). -/
theorem pv_split {ρ Ms : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {s : ℕ → ℝ} (hsb : ∀ j, |s j| ≤ Ms)
    (m : ℕ) : Summable (fun j => ρ ^ j * s (m + j)) ∧
      ∑' j, ρ ^ j * s (m + j) = s m + ρ * ∑' j, ρ ^ j * s (m + 1 + j) := by
  have hsum : ∀ m, Summable (fun j => ρ ^ j * s (m + j)) := fun m =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Ms) (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 j)]
      exact mul_le_mul_of_nonneg_left (hsb _) (pow_nonneg hρ0 j))
  refine ⟨hsum m, ?_⟩
  rw [(hsum m).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show m + (j + 1) = m + 1 + j by omega, pow_succ]
  ring

/-- Cochrane (2023), Figs. 5.1–5.3, pp. 122–125: under the peg `i ≡ a`, with deterministic
bounded surpluses `s̃` and initial debt `b_0`, `(xDet, piDet, vDet)` is a bounded equilibrium of
(5.15)–(5.16), for any expectation system. -/
theorem det_eqm {σ β κ ρ Ms : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (a b0 : ℝ) {s : ℕ → ℝ} (hsb : ∀ j, |s j| ≤ Ms) :
    FTPLNK 𝔼 σ β κ ρ (fun _ _ => a) (fun t _ => s t) (fun _ => b0)
        (fun t _ => xDet σ β κ ρ a b0 s t) (fun t _ => piDet σ β κ ρ a b0 s t)
        (fun t _ => vDet σ β κ ρ a b0 s t) ∧
      BoundedProc (fun t (_ : Ω) => xDet σ β κ ρ a b0 s t) ∧
      BoundedProc (fun t (_ : Ω) => piDet σ β κ ρ a b0 s t) ∧
      BoundedProc (fun t (_ : Ω) => vDet σ β κ ρ a b0 s t) := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have hq : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have hqt : ∀ t, (lam1 σ β κ)⁻¹ ^ t ≤ 1 := fun t => pow_le_one₀ hq0 hq1.le
  have hroot := lam1_root ha hβ
  have hc : ∀ t (r : ℝ), 𝔼.E t (fun _ => r) = fun _ => r := fun t r => 𝔼.const t r
  set q := (lam1 σ β κ)⁻¹ with hqdef
  set A := (1 - ρ * q) * (b0 - a - pvS ρ s) with hA
  have hpi : ∀ t, piDet σ β κ ρ a b0 s t = a + A * q ^ t := fun t => by
    simp only [piDet, hA, hqdef]
  have hsplit := pv_split hρ0.le hρ1 hsb
  refine ⟨⟨(nk_iff_second 𝔼 hκ.ne').mpr ⟨fun t => ?_, fun t => ?_⟩, fun t => ?_, ?_⟩, ?_, ?_, ?_⟩
  · funext ω
    simp only [hc, xDet, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  · funext ω
    simp only [hc, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hpi]
    linear_combination (A * q ^ (t + 2)) * hroot - A * q ^ t * (lam1 σ β κ * q + 1) * hq +
      (1 + β + σ * κ) * A * q ^ (t + 1) * hq
  · funext ω
    have e := (hsplit (t + 1)).2
    simp only [vDet, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hpi]
    rw [e]
    simp only [hA, ← hqdef]
    ring
  · funext ω
    have e := (hsplit 0).2
    simp only [zero_add] at e
    have hS : pvS ρ s = s 0 + ρ * ∑' j, ρ ^ j * s (1 + j) := e
    simp only [vDet, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hpi, zero_add, pow_zero, mul_one]
    simp only [hA, ← hqdef]
    linear_combination -hS
  · refine ⟨κ⁻¹ * ((|a| + |A|) + β * (|a| + |A|)), fun t _ => ?_⟩
    have hb : ∀ t, |piDet σ β κ ρ a b0 s t| ≤ |a| + |A| := fun t => by
      rw [hpi]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 t)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hqt t)
    simp only [xDet]
    rw [abs_mul, abs_of_pos (inv_pos.mpr hκ)]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hb t) ?_))
      (inv_pos.mpr hκ).le
    rw [abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hb _) hβ.le
  · refine ⟨|a| + |A|, fun t _ => ?_⟩
    change |piDet σ β κ ρ a b0 s t| ≤ |a| + |A|
    rw [hpi]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 t)]
    exact mul_le_of_le_one_right (abs_nonneg _) (hqt t)
  · refine ⟨|b0 - a - pvS ρ s| + Ms * (1 - ρ)⁻¹, fun t _ => ?_⟩
    simp only [vDet]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hqt _)
    · have hs := (hsplit (t + 1)).1
      calc |∑' j, ρ ^ j * s (t + 1 + j)| = ‖∑' j, ρ ^ j * s (t + 1 + j)‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ∑' j, ‖ρ ^ j * s (t + 1 + j)‖ := norm_tsum_le_tsum_norm hs.abs
        _ ≤ ∑' j : ℕ, ρ ^ j * Ms := by
            refine hs.abs.tsum_le_tsum (fun j => ?_)
              ((summable_geometric_of_lt_one hρ0.le hρ1).mul_right Ms)
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0.le j)]
            exact mul_le_mul_of_nonneg_left (hsb _) (pow_nonneg hρ0.le j)
        _ = Ms * (1 - ρ)⁻¹ := by
            rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0.le hρ1, mul_comm]

/-- Cochrane (2023), Figs. 5.1–5.3 and p. 125: under the peg `i ≡ a`, with deterministic bounded
surpluses and initial debt `b_0`, **every** equilibrium with bounded inflation and debt is
`(xDet, piDet, vDet)`; in particular inflation and output depend on the surpluses only through
their present value `S` ("the present value of future surpluses matters, not the current
deficit"). -/
theorem det_unique {σ β κ ρ Ms : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (a b0 : ℝ) {s : ℕ → ℝ} (hsb : ∀ j, |s j| ≤ Ms) {x π v : ℕ → Ω → ℝ}
    (h : FTPLNK 𝔼 σ β κ ρ (fun _ _ => a) (fun t _ => s t) (fun _ => b0) x π v)
    (hπb : BoundedProc π) (hvb : BoundedProc v) :
    x = (fun t _ => xDet σ β κ ρ a b0 s t) ∧ π = (fun t _ => piDet σ β κ ρ a b0 s t) ∧
      v = (fun t _ => vDet σ β κ ρ a b0 s t) := by
  obtain ⟨hd, _, hdπ, hdv⟩ := det_eqm 𝔼 hσ hκ hβ hρ0 hρ1 a b0 hsb
  have hi : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => a) := fun t => 𝔼.const t a
  have hs : 𝔼.Adapted (fun (t : ℕ) (_ : Ω) => s t) := fun t => 𝔼.const t (s t)
  rw [ftplnk_iff] at h hd
  exact eqm_unique 𝔼 hσ hκ hβ hρ0 hρ1 hi (Mi := |a|) (fun _ _ => le_rfl)
    (eShort_adapted 𝔼 hi hs) (𝔼.const 0 b0) h hd hπb hdπ hvb hdv

/-- Cochrane (2023), p. 125 ("the present value of future surpluses matters, not the current
deficit"): two deterministic surplus paths with the same present value give the same equilibrium
inflation and output. -/
theorem pv_only {σ β κ ρ Ms Ms' : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (a b0 : ℝ) {s s' : ℕ → ℝ} (hsb : ∀ j, |s j| ≤ Ms) (hsb' : ∀ j, |s' j| ≤ Ms')
    (hpv : pvS ρ s = pvS ρ s') {x π v x' π' v' : ℕ → Ω → ℝ}
    (h : FTPLNK 𝔼 σ β κ ρ (fun _ _ => a) (fun t _ => s t) (fun _ => b0) x π v)
    (h' : FTPLNK 𝔼 σ β κ ρ (fun _ _ => a) (fun t _ => s' t) (fun _ => b0) x' π' v')
    (hπb : BoundedProc π) (hvb : BoundedProc v) (hπb' : BoundedProc π')
    (hvb' : BoundedProc v') : x = x' ∧ π = π' := by
  obtain ⟨hx, hπ, _⟩ := det_unique 𝔼 hσ hκ hβ hρ0 hρ1 a b0 hsb h hπb hvb
  obtain ⟨hx', hπ', _⟩ := det_unique 𝔼 hσ hκ hβ hρ0 hρ1 a b0 hsb' h' hπb' hvb'
  have hp : ∀ t, piDet σ β κ ρ a b0 s t = piDet σ β κ ρ a b0 s' t := fun t => by
    simp only [piDet, hpv]
  refine ⟨?_, ?_⟩
  · rw [hx, hx']
    funext t _
    simp only [xDet, hp]
  · rw [hπ, hπ']
    funext t _
    rw [hp]

/-! ### Fig. 5.1: an unexpected permanent interest-rate rise -/

/-- Cochrane (2023), Fig. 5.1, pp. 122–123: an unexpected permanent rate rise (`i ≡ 1` from the
shock date, unchanged surpluses, `b_0 = 0`). The equilibrium exists, and every equilibrium with
bounded inflation and debt is `π_{1+j} = 1 − (1 − ρ/λ₁) λ₁^{−j}`,
`κ x_{1+j} = (1 − β) − (1 − ρ/λ₁)(1 − β/λ₁) λ₁^{−j}`, `v_{1+j} = −λ₁^{−(j+1)}` (book date `1 + j`
is date `j` here). -/
theorem perm_rise {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    (∃ x π v, FTPLNK 𝔼 σ β κ ρ (fun _ _ => 1) (fun _ _ => 0) (fun _ => 0) x π v ∧
      BoundedProc π ∧ BoundedProc v) ∧
    ∀ x π v, FTPLNK 𝔼 σ β κ ρ (fun _ _ => 1) (fun _ _ => 0) (fun _ => 0) x π v →
      BoundedProc π → BoundedProc v → ∀ t ω,
        π t ω = 1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t ∧
        κ * x t ω = (1 - β) - (1 - ρ * (lam1 σ β κ)⁻¹) * (1 - β * (lam1 σ β κ)⁻¹) *
          (lam1 σ β κ)⁻¹ ^ t ∧
        v t ω = -(lam1 σ β κ)⁻¹ ^ (t + 1) := by
  have hs0 : ∀ j, |(fun _ : ℕ => (0 : ℝ)) j| ≤ 0 := fun j => by simp
  have hpv : pvS ρ (fun _ => 0) = 0 := by simp [pvS]
  obtain ⟨hd, _, hdπ, hdv⟩ := det_eqm 𝔼 hσ hκ hβ hρ0 hρ1 1 0 hs0
  refine ⟨⟨_, _, _, hd, hdπ, hdv⟩, fun x π v h hπb hvb t ω => ?_⟩
  obtain ⟨hx, hπ, hv⟩ := det_unique 𝔼 hσ hκ hβ hρ0 hρ1 1 0 hs0 h hπb hvb
  rw [hx, hπ, hv]
  simp only [xDet, piDet, vDet, hpv, mul_zero, tsum_zero, add_zero]
  have hκ0 : κ ≠ 0 := hκ.ne'
  refine ⟨by ring, ?_, by ring⟩
  field_simp
  ring

/-- Cochrane (2023), p. 122: on impact `π_1 = 1 − (1 − ρ/λ₁) = ρ/λ₁ > 0` — "an immediate positive
inflation response". -/
theorem perm_rise_pi0_pos {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ) :
    1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ 0 = ρ * (lam1 σ β κ)⁻¹ ∧
      0 < ρ * (lam1 σ β κ)⁻¹ := by
  refine ⟨by ring, mul_pos hρ0 (inv_pos.mpr (lam1_pos (mul_pos hσ hκ) hβ))⟩

/-- Cochrane (2023), p. 120 (Fisherian long run): after a permanent rise inflation converges to
the new rate, `π_{1+j} → 1`. -/
theorem perm_rise_tendsto_one {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t) atTop (𝓝 1) := by
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (by linarith))
    (inv_lt_one_of_one_lt₀ h1)).const_mul (1 - ρ * (lam1 σ β κ)⁻¹)
  rw [mul_zero] at this
  simpa using this.const_sub 1

/-- Cochrane (2023), p. 123 ("stickier prices lead to more positive time-1 inflation"): the
impact response `π_1 = ρ/λ₁` is strictly decreasing in `κ`. -/
theorem perm_rise_pi0_strictAnti {σ β ρ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hρ0 : 0 < ρ) :
    StrictAntiOn (fun κ => ρ * (lam1 σ β κ)⁻¹) (Set.Ioi 0) := by
  intro κ₁ hκ₁ κ₂ hκ₂ hlt
  have hm := lam1_strictMonoOn hσ hβ hκ₁ hκ₂ hlt
  have hp := lam1_pos (mul_pos hσ hκ₁) hβ
  simp only
  exact mul_lt_mul_of_pos_left ((inv_lt_inv₀ (hp.trans hm) hp).mpr hm) hρ0

/-- Cochrane (2023), p. 123, survey error E27: as `κ → 0` the inflation path tends to
`π_{1+j} → ρ` for every `j` — a jump to `ρ` times the rate rise, not "exactly by the amount of
the nominal interest rate". -/
theorem perm_rise_kappa_zero {σ β ρ : ℝ} (hβ1 : β < 1) (t : ℕ) :
    Tendsto (fun κ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t) (𝓝[>] 0) (𝓝 ρ) := by
  have hq : Tendsto (fun κ => (lam1 σ β κ)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_lam1_zero (σ := σ) hβ1).inv₀ one_ne_zero
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (hq.const_mul ρ)).mul (hq.pow t))
  simpa using this

/-- Cochrane (2023), p. 123, survey error E27 (the printed claim fails at every κ): for every
`κ > 0` the impact response is `ρ/λ₁ < ρ`, and the κ → 0 limit `ρ` is below the rate rise `1`
when `ρ < 1`. -/
theorem e27_not_exact {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) : ρ * (lam1 σ β κ)⁻¹ < ρ ∧ ρ < 1 := by
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  exact ⟨mul_lt_of_lt_one_right hρ0 (inv_lt_one_of_one_lt₀ h1), hρ1⟩

/-- Cochrane (2023), p. 123 and Fig. 3.1 (flexible-price limit κ → ∞): the impact response
`π_1 → 0` and, for `j ≥ 1`, `π_{1+j} → 1`. -/
theorem perm_rise_kappa_atTop {σ β ρ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) :
    Tendsto (fun κ => ρ * (lam1 σ β κ)⁻¹) atTop (𝓝 0) ∧
    ∀ t, 1 ≤ t → Tendsto (fun κ => 1 - (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t) atTop
      (𝓝 1) := by
  have hq := (tendsto_lam1_atTop hσ hβ).inv_tendsto_atTop
  refine ⟨by simpa using hq.const_mul ρ, fun t ht => ?_⟩
  have hqt : Tendsto (fun κ => (lam1 σ β κ)⁻¹ ^ t) atTop (𝓝 0) := by
    have := hq.pow t
    rwa [zero_pow (by omega)] at this
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (hq.const_mul ρ)).mul hqt)
  simpa using this

/-- Cochrane (2023), p. 123 ("Higher interest rates do lead to lower output"): output falls on
impact iff `(1 − ρ/λ₁)(1 − β/λ₁) > 1 − β`. -/
theorem perm_rise_x0_neg_iff {β κ ρ q x0 : ℝ} (hκ : 0 < κ)
    (hx : κ * x0 = (1 - β) - (1 - ρ * q) * (1 - β * q) * q ^ 0) :
    x0 < 0 ↔ 1 - β < (1 - ρ * q) * (1 - β * q) := by
  rw [pow_zero, mul_one] at hx
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hc
    push Not at hc
    nlinarith

/-- Cochrane (2023), p. 123 (the permanent tradeoff): after a permanent rise output converges
to `(1 − β)/κ`. -/
theorem perm_rise_x_tendsto {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) :
    Tendsto (fun t : ℕ => κ⁻¹ * ((1 - β) - (1 - ρ * (lam1 σ β κ)⁻¹) * (1 - β * (lam1 σ β κ)⁻¹) *
      (lam1 σ β κ)⁻¹ ^ t)) atTop (𝓝 ((1 - β) / κ)) := by
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (by linarith))
    (inv_lt_one_of_one_lt₀ h1)).const_mul
      ((1 - ρ * (lam1 σ β κ)⁻¹) * (1 - β * (lam1 σ β κ)⁻¹))
  rw [mul_zero] at hp
  have := (hp.const_sub (1 - β)).const_mul κ⁻¹
  rw [sub_zero] at this
  rw [div_eq_inv_mul]
  exact this.congr fun t => by ring

/-- Cochrane (2023), p. 123: "higher interest rates do lead to lower output" is conditional —
for `0 < ρ`, `β < 1`, if prices are sticky enough (κ near 0) output **rises** on impact:
`κ x_1 = (1 − β) − (1 − ρ/λ₁)(1 − β/λ₁) > 0`. -/
theorem perm_rise_x0_pos_small_kappa {σ β ρ : ℝ} (hβ1 : β < 1) (hρ0 : 0 < ρ) :
    ∀ᶠ κ in 𝓝[>] 0, 0 < (1 - β) - (1 - ρ * (lam1 σ β κ)⁻¹) * (1 - β * (lam1 σ β κ)⁻¹) := by
  have hq : Tendsto (fun κ => (lam1 σ β κ)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_lam1_zero (σ := σ) hβ1).inv₀ one_ne_zero
  have hlim := (tendsto_const_nhds (x := 1 - β)).sub
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (hq.const_mul ρ)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (hq.const_mul β)))
  have hpos : 0 < (1 - β) - (1 - ρ * 1) * (1 - β * 1) := by nlinarith
  exact hlim.eventually (lt_mem_nhds hpos)

/-! ### Fig. 5.3: a fiscal shock -/

/-- Cochrane (2023), Fig. 5.3, pp. 124–125: a deficit shock (surpluses with present value
`∑ ρʲ s̃_j = −1`, no rate change, `b_0 = 0`): every equilibrium with bounded inflation and debt
has `π_{1+j} = (1 − ρ/λ₁) λ₁^{−j}` and `κ x_{1+j} = (1 − ρ/λ₁)(1 − β/λ₁) λ₁^{−j}`, whatever the
timing of the deficits. -/
theorem fiscal_shock {σ β κ ρ Ms : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) {s : ℕ → ℝ} (hsb : ∀ j, |s j| ≤ Ms) (hpv : pvS ρ s = -1)
    {x π v : ℕ → Ω → ℝ}
    (h : FTPLNK 𝔼 σ β κ ρ (fun _ _ => 0) (fun t _ => s t) (fun _ => 0) x π v)
    (hπb : BoundedProc π) (hvb : BoundedProc v) (t : ℕ) (ω : Ω) :
    π t ω = (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t ∧
      κ * x t ω = (1 - ρ * (lam1 σ β κ)⁻¹) * (1 - β * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t := by
  obtain ⟨hx, hπ, _⟩ := det_unique 𝔼 hσ hκ hβ hρ0 hρ1 0 0 hsb h hπb hvb
  rw [hx, hπ]
  simp only [xDet, piDet, hpv]
  refine ⟨by ring, ?_⟩
  field_simp
  ring

/-- Cochrane (2023), p. 124 ("cumulative inflation is still 1%", exact form): the
`ρ`-discounted cumulative inflation after the fiscal shock is exactly one,
`∑ ρʲ π_{1+j} = 1`. -/
theorem fiscal_shock_pv_one {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) : HasSum (fun j : ℕ => ρ ^ j * ((1 - ρ * (lam1 σ β κ)⁻¹) *
      (lam1 σ β κ)⁻¹ ^ j)) 1 := by
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have hq0 : 0 ≤ ρ * (lam1 σ β κ)⁻¹ := mul_nonneg hρ0.le (inv_nonneg.mpr (by linarith))
  have hq1 : ρ * (lam1 σ β κ)⁻¹ < 1 := by
    have := inv_lt_one_of_one_lt₀ h1
    nlinarith
  have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 - ρ * (lam1 σ β κ)⁻¹)
  rw [mul_inv_cancel₀ (by linarith)] at this
  exact this.congr_fun fun j => by rw [mul_pow]; ring

/-- Cochrane (2023), p. 124, survey error E28: the undiscounted cumulative inflation is
`∑ π_{1+j} = (λ₁ − ρ)/(λ₁ − 1)`, strictly greater than one for `ρ < 1` — "cumulative inflation
is still 1%" holds only for the `ρ`-weighted sum (`fiscal_shock_pv_one`). -/
theorem fiscal_shock_sum {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ1 : ρ < 1) :
    HasSum (fun j : ℕ => (1 - ρ * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ j)
      ((lam1 σ β κ - ρ) / (lam1 σ β κ - 1)) ∧ 1 < (lam1 σ β κ - ρ) / (lam1 σ β κ - 1) := by
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 := inv_lt_one_of_one_lt₀ h1
  refine ⟨?_, (one_lt_div (by linarith)).mpr (by linarith)⟩
  have := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (1 - ρ * (lam1 σ β κ)⁻¹)
  convert this using 1
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have hl1 : lam1 σ β κ - 1 ≠ 0 := by linarith
  field_simp

/-- Cochrane (2023), p. 125 ("an output expansion in response to the deficit shock"): for
`0 < β < 1`, `κ x_{1+j} = (1 − ρ/λ₁)(1 − β/λ₁) λ₁^{−j} > 0`. -/
theorem fiscal_shock_x_pos {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hβ1 : β < 1)
    (hρ1 : ρ < 1) (t : ℕ) :
    0 < (1 - ρ * (lam1 σ β κ)⁻¹) * (1 - β * (lam1 σ β κ)⁻¹) * (lam1 σ β κ)⁻¹ ^ t := by
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have hq0 : 0 < (lam1 σ β κ)⁻¹ := inv_pos.mpr (by linarith)
  have hq1 := inv_lt_one_of_one_lt₀ h1
  have hρq : ρ * (lam1 σ β κ)⁻¹ < 1 := by
    rcases le_or_gt ρ 0 with h | h
    · nlinarith
    · nlinarith
  have hβq : β * (lam1 σ β κ)⁻¹ < 1 := by nlinarith
  exact mul_pos (mul_pos (by linarith) (by linarith)) (pow_pos hq0 t)

/-- Cochrane (2023), p. 124 ("the 1% fiscal shock now only produces a 0.4% immediate rise"):
the impact response `1 − ρ/λ₁` lies in `(0, 1)` and is strictly increasing in `κ` (stickier
prices spread the inflation out). -/
theorem fiscal_shock_pi0 {σ β ρ : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    StrictMonoOn (fun κ => 1 - ρ * (lam1 σ β κ)⁻¹) (Set.Ioi 0) ∧
      ∀ κ, 0 < κ → 0 < 1 - ρ * (lam1 σ β κ)⁻¹ ∧ 1 - ρ * (lam1 σ β κ)⁻¹ < 1 := by
  refine ⟨fun κ₁ h₁ κ₂ h₂ hlt => ?_, fun κ hκ => ?_⟩
  · have := perm_rise_pi0_strictAnti hσ hβ hρ0 h₁ h₂ hlt
    simp only at this ⊢
    linarith
  · have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
    have hq1 := inv_lt_one_of_one_lt₀ h1
    have hq0 : 0 < (lam1 σ β κ)⁻¹ := inv_pos.mpr (by linarith)
    constructor <;> nlinarith

/-! ### The calibration of Figs. 5.3–5.4 (r = 0.01, σ = 1, κ = 0.25) -/

/-- Cochrane (2023), Figs. 5.3–5.4, pp. 125, 128 (calibration `β = ρ = 1/(1 + r)` with
`r = 0.01`, `σ = 1`, `κ = 0.25`): `1.63425 < λ₁ < 1.634275`. -/
theorem lam1_calib :
    (163425 / 100000 : ℝ) < lam1 1 (100 / 101) (1 / 4) ∧
      lam1 1 (100 / 101) (1 / 4) < (1634275 / 1000000 : ℝ) := by
  unfold lam1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt ((1 + 100 / 101 + 1 * (1 / 4)) ^ 2 - 4 * (100 / 101)) :=
    ⟨_, rfl⟩
  rw [← hr]
  have ha : (102841 / 100000 : ℝ) < r := by
    rw [hr, Real.lt_sqrt (by norm_num)]; norm_num
  have hb : r < (102845 / 100000 : ℝ) := by
    rw [hr, Real.sqrt_lt' (by norm_num)]; norm_num
  constructor <;> linarith

/-- Cochrane (2023), Fig. 5.3, p. 124 ("the 1% fiscal shock now only produces a 0.4% immediate
rise in inflation"): at the calibration, the impact response `1 − ρ/λ₁` lies in
`(0.394, 0.395)`. -/
theorem fig53_impact :
    (394 / 1000 : ℝ) < 1 - 100 / 101 * (lam1 1 (100 / 101) (1 / 4))⁻¹ ∧
      1 - 100 / 101 * (lam1 1 (100 / 101) (1 / 4))⁻¹ < (395 / 1000 : ℝ) := by
  obtain ⟨h1, h2⟩ := lam1_calib
  have hL : 0 < lam1 1 (100 / 101) (1 / 4) := by linarith
  have hu1 : (1000000 / 1634275 : ℝ) < (lam1 1 (100 / 101) (1 / 4))⁻¹ := by
    rw [← one_div, div_lt_div_iff₀ (by norm_num) hL]; linarith
  have hu2 : (lam1 1 (100 / 101) (1 / 4))⁻¹ < (100000 / 163425 : ℝ) := by
    rw [← one_div, div_lt_div_iff₀ hL (by norm_num)]; linarith
  constructor <;> linarith

/-- Cochrane (2023), Fig. 5.3, p. 124, survey error E28 (numerically): at the calibration the
undiscounted cumulative inflation `(λ₁ − ρ)/(λ₁ − 1)` lies in `(1.015, 1.016)`, not `1`. -/
theorem fig53_cumulative :
    (1015 / 1000 : ℝ) < (lam1 1 (100 / 101) (1 / 4) - 100 / 101) /
        (lam1 1 (100 / 101) (1 / 4) - 1) ∧
      (lam1 1 (100 / 101) (1 / 4) - 100 / 101) / (lam1 1 (100 / 101) (1 / 4) - 1) <
        (1016 / 1000 : ℝ) := by
  obtain ⟨h1, h2⟩ := lam1_calib
  have hL : 0 < lam1 1 (100 / 101) (1 / 4) - 1 := by linarith
  constructor
  · rw [lt_div_iff₀ hL]; linarith
  · rw [div_lt_iff₀ hL]; linarith

/-! ### General deterministic rate paths under the peg -/

/-- Cochrane (2023), pp. 122–125: a deterministic bounded rate path `c`, surpluses `s̃` and
debt `b_0`. If a bounded sequence `p` solves the factored model
`p_t − λ₁ p_{t+1} = −σκ ∑_{k≥0} λ₂ᵏ c_{t+k}` and the date-0 valuation
`∑ ρʲ(p_j + s̃_j) − ρ ∑ ρʲ c_j = b_0`, then `p` is equilibrium inflation: an equilibrium with
inflation `p` exists, and every equilibrium with bounded inflation and debt has inflation `p` and
output `κ⁻¹(p_t − β p_{t+1})`. -/
theorem det_path {σ β κ ρ Mc Ms Mp : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (b0 : ℝ) {c sv p : ℕ → ℝ} (hcb : ∀ t, |c t| ≤ Mc) (hsb : ∀ t, |sv t| ≤ Ms)
    (hpb : ∀ t, |p t| ≤ Mp)
    (hfac : ∀ t, p t - lam1 σ β κ * p (t + 1) =
      -(σ * κ) * ∑' k, lam2 σ β κ ^ k * c (t + k))
    (hfis : ∑' j, ρ ^ j * (p j + sv j) - ρ * ∑' j, ρ ^ j * c j = b0) :
    (∃ x v, FTPLNK 𝔼 σ β κ ρ (fun t _ => c t) (fun t _ => sv t) (fun _ => b0) x
        (fun t _ => p t) v ∧ BoundedProc v) ∧
    ∀ x π v, FTPLNK 𝔼 σ β κ ρ (fun t _ => c t) (fun t _ => sv t) (fun _ => b0) x π v →
      BoundedProc π → BoundedProc v →
        π = (fun t _ => p t) ∧ x = (fun t _ => κ⁻¹ * (p t - β * p (t + 1))) := by
  have ha := mul_pos hσ hκ
  have hc : ∀ t (r : ℝ), 𝔼.E t (fun _ => r) = fun _ => r := fun t r => 𝔼.const t r
  have hi : 𝔼.Adapted (fun t (_ : Ω) => c t) := fun t => 𝔼.const t _
  have hib : ∀ t (ω : Ω), |(fun t (_ : Ω) => c t) t ω| ≤ Mc := fun t _ => hcb t
  obtain ⟨w, hw⟩ : ∃ w : ℕ → ℝ, w = fun m => p (m + 1) + sv (m + 1) - c m := ⟨_, rfl⟩
  have hwb : ∀ m, |w m| ≤ Mp + Ms + Mc := fun m => by
    rw [hw]
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (hpb _) (hsb _))) (hcb _))
  have hsplit := pv_split hρ0.le hρ1 hwb
  have hF : ∀ t, 𝔼.forwardSeries (lam2 σ β κ) (fun t (_ : Ω) => c t) t =
      fun _ => ∑' k, lam2 σ β κ ^ k * c (t + k) := by
    intro t
    funext ω
    unfold ExpectationSystem.forwardSeries
    exact tsum_congr fun k => by rw [hc]
  have hEq : FTPLNK 𝔼 σ β κ ρ (fun t _ => c t) (fun t _ => sv t) (fun _ => b0)
      (fun t _ => κ⁻¹ * (p t - β * p (t + 1))) (fun t _ => p t)
      (fun t _ => ∑' j, ρ ^ j * w (t + j)) := by
    refine ⟨(nk_iff_second 𝔼 hκ.ne').mpr ⟨fun t => ?_, second_of_factor 𝔼 ha hβ hi hib
      (fun t => ?_)⟩, fun t => ?_, ?_⟩
    · funext ω
      simp only [hc, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    · rw [hF t, hc]
      funext ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact hfac t
    · funext ω
      have e := (hsplit t).2
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e, hw]
      ring
    · funext ω
      have hs1 := (hsplit 0).1
      have hpsb : ∀ j, |p j + sv j| ≤ Mp + Ms := fun j =>
        (abs_add_le _ _).trans (add_le_add (hpb j) (hsb j))
      have e2 := (pv_split hρ0.le hρ1 hpsb 0).2
      have hs2 := (pv_split hρ0.le hρ1 hpsb 1).1
      have hs3 := (pv_split hρ0.le hρ1 hcb 0).1
      simp only [zero_add] at e2 hs3 hs1
      have hs2' : Summable (fun j => ρ ^ j * (p (j + 1) + sv (j + 1))) :=
        hs2.congr fun j => by rw [add_comm 1 j]
      have e3 : ∑' j, ρ ^ j * w j = ∑' j, ρ ^ j * (p (j + 1) + sv (j + 1)) -
          ∑' j, ρ ^ j * c j := by
        rw [← hs2'.tsum_sub hs3]
        exact tsum_congr fun j => by rw [hw]; ring
      have e2' : ∑' j, ρ ^ j * (p j + sv j) = p 0 + sv 0 +
          ρ * ∑' j, ρ ^ j * (p (j + 1) + sv (j + 1)) := by
        rw [e2]
        congr 2
        exact tsum_congr fun j => by rw [add_comm 1 j]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_add]
      rw [e3]
      linarith
  have hvb : BoundedProc (fun t (_ : Ω) => ∑' j, ρ ^ j * w (t + j)) := by
    refine ⟨(Mp + Ms + Mc) * (1 - ρ)⁻¹, fun t _ => ?_⟩
    have hs := (hsplit t).1
    calc |∑' j, ρ ^ j * w (t + j)| = ‖∑' j, ρ ^ j * w (t + j)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' j, ‖ρ ^ j * w (t + j)‖ := norm_tsum_le_tsum_norm hs.abs
      _ ≤ ∑' j : ℕ, ρ ^ j * (Mp + Ms + Mc) := by
          refine hs.abs.tsum_le_tsum (fun j => ?_)
            ((summable_geometric_of_lt_one hρ0.le hρ1).mul_right _)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0.le j)]
          exact mul_le_mul_of_nonneg_left (hwb _) (pow_nonneg hρ0.le j)
      _ = (Mp + Ms + Mc) * (1 - ρ)⁻¹ := by
          rw [tsum_mul_right, tsum_geometric_of_lt_one hρ0.le hρ1, mul_comm]
  have hpbd : BoundedProc (fun t (_ : Ω) => p t) := ⟨Mp, fun t _ => hpb t⟩
  refine ⟨⟨_, _, hEq, hvb⟩, fun x π v h hπb hvb' => ?_⟩
  have hs : 𝔼.Adapted (fun (t : ℕ) (_ : Ω) => sv t) := fun t => 𝔼.const t (sv t)
  rw [ftplnk_iff] at h hEq
  obtain ⟨hx, hπ, _⟩ := eqm_unique 𝔼 hσ hκ hβ hρ0 hρ1 hi hib (eShort_adapted 𝔼 hi hs)
    (𝔼.const 0 b0) h hEq hπb hpbd hvb' hvb
  exact ⟨hπ, hx⟩

/-- Cochrane (2023), Fig. 5.2: `∑_{k≥0} rᵏ 1{S ≤ t + k} = r^{S−t}/(1 − r)` (`0 ≤ r < 1`), the
forward sum of an announced step. -/
theorem hasSum_step {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S t : ℕ) :
    HasSum (fun k : ℕ => r ^ k * (if S ≤ t + k then (1 : ℝ) else 0)) (r ^ (S - t) / (1 - r)) := by
  rw [← hasSum_nat_add_iff' (S - t)]
  have hfin : ∑ i ∈ Finset.range (S - t), r ^ i * (if S ≤ t + i then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), mul_zero]
  rw [hfin, sub_zero]
  have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (r ^ (S - t))
  convert this using 1
  · funext n
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), mul_one, pow_add]
    ring
  · rw [div_eq_mul_inv]

/-- Cochrane (2023), Fig. 5.2: the coefficient `B = (λ₁ − 1)λ₂/(λ₁ − λ₂) = σκλ₂/((1−λ₂)(λ₁−λ₂))`
on the announced rate in the two-sided moving average. -/
noncomputable def antB (σ β κ : ℝ) : ℝ :=
  (lam1 σ β κ - 1) * lam2 σ β κ / (lam1 σ β κ - lam2 σ β κ)

/-- Cochrane (2023), Fig. 5.2: `H = ∑_{j<S} ρʲ λ₂^{S−j}`. -/
noncomputable def antH (σ β κ ρ : ℝ) (S : ℕ) : ℝ :=
  ∑ j ∈ Finset.range S, ρ ^ j * lam2 σ β κ ^ (S - j)

/-- Cochrane (2023), Fig. 5.2: the coefficient on `λ₁^{−t}`, pinned by the valuation equation,
`C = (1 − ρ/λ₁)(−ρ^S − B H) − ρ^S(B − 1)`. -/
noncomputable def antC (σ β κ ρ : ℝ) (S : ℕ) : ℝ :=
  (1 - ρ * (lam1 σ β κ)⁻¹) * (-ρ ^ S - antB σ β κ * antH σ β κ ρ S) - ρ ^ S * (antB σ β κ - 1)

/-- Cochrane (2023), Fig. 5.2: the inflation path after the date-0 announcement of a permanent
rise to `i = 1` from date `S` on: `π_t = B λ₂^{S−t} + C λ₁^{−t}` before the rise (`t < S`) and
`π_t = 1 + (B − 1) λ₁^{−(t−S)} + C λ₁^{−t}` from the rise on. -/
noncomputable def antPi (σ β κ ρ : ℝ) (S t : ℕ) : ℝ :=
  (if t < S then antB σ β κ * lam2 σ β κ ^ (S - t)
    else 1 + (antB σ β κ - 1) * (lam1 σ β κ)⁻¹ ^ (t - S)) + antC σ β κ ρ S * (lam1 σ β κ)⁻¹ ^ t

/-- Cochrane (2023), Fig. 5.2, p. 124 — **the anticipated rise in closed form**: a permanent rate
rise to `1` from date `S`, announced at date 0 (one-period debt, unchanged surpluses, `b_0 = 0`).
An equilibrium exists, and every equilibrium with bounded inflation and debt has `π_t = antPi t`:
before the rise inflation is the two-sided moving average `B λ₂^{S−t}` of the announced rate plus
`C λ₁^{−t}`; from the rise on it is `1 + (B − 1)λ₁^{−(t−S)} + C λ₁^{−t}`. With `S = 0` this is
`perm_rise`. -/
theorem anticipated_rise {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (S : ℕ) :
    (∃ x π v, FTPLNK 𝔼 σ β κ ρ (fun t _ => if S ≤ t then 1 else 0) (fun _ _ => 0) (fun _ => 0)
      x π v ∧ BoundedProc π ∧ BoundedProc v) ∧
    ∀ x π v, FTPLNK 𝔼 σ β κ ρ (fun t _ => if S ≤ t then 1 else 0) (fun _ _ => 0) (fun _ => 0)
      x π v → BoundedProc π → BoundedProc v → ∀ t ω, π t ω = antPi σ β κ ρ S t := by
  have ha := mul_pos hσ hκ
  have h1 := one_lt_lam1 ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := by linarith
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have h12 := lam2_lt_lam1 ha hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have hq : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hρq0 : 0 ≤ ρ * (lam1 σ β κ)⁻¹ := mul_nonneg hρ0.le hq0
  have hρq1 : ρ * (lam1 σ β κ)⁻¹ < 1 := by nlinarith
  have hσκ := sigma_kappa_eq ha hβ
  have hB : antB σ β κ * (lam1 σ β κ - lam2 σ β κ) = (lam1 σ β κ - 1) * lam2 σ β κ := by
    unfold antB; field_simp [sub_ne_zero.mpr h12.ne']
  set B := antB σ β κ with hBdef
  set C := antC σ β κ ρ S with hCdef
  set H := antH σ β κ ρ S with hHdef
  set l1 := lam1 σ β κ with hl1
  set l2 := lam2 σ β κ with hl2
  set q := l1⁻¹ with hqdef
  -- the factored model
  have hFd : ∀ t, ∑' k, l2 ^ k * (if S ≤ t + k then (1 : ℝ) else 0) = l2 ^ (S - t) / (1 - l2) :=
    fun t => (hasSum_step h2.le h21 S t).tsum_eq
  have hfac : ∀ t, antPi σ β κ ρ S t - l1 * antPi σ β κ ρ S (t + 1) =
      -(σ * κ) * ∑' k, l2 ^ k * (if S ≤ t + k then (1 : ℝ) else 0) := by
    intro t
    rw [hFd t, hσκ]
    have hc : (l1 - 1) * (1 - l2) * (l2 ^ (S - t) / (1 - l2)) = (l1 - 1) * l2 ^ (S - t) := by
      field_simp [(by linarith : (1 : ℝ) - l2 ≠ 0)]
    rw [neg_mul, hc]
    unfold antPi
    rw [← hBdef, ← hCdef, ← hl1, ← hl2, ← hqdef]
    by_cases ht : t < S
    · have hg1 : (if t + 1 < S then B * l2 ^ (S - (t + 1)) else 1 + (B - 1) * q ^ (t + 1 - S)) =
          B * l2 ^ (S - (t + 1)) := by
        split_ifs with h
        · rfl
        · rw [show t + 1 - S = 0 by omega, show S - (t + 1) = 0 by omega]; ring
      rw [ite_eq_left_of_eq_true _ _ (eq_true ht), hg1, show S - t = S - (t + 1) + 1 by omega,
        pow_succ, pow_succ]
      linear_combination (-l2 ^ (S - (t + 1))) * hB - (C * q ^ t) * hq
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ht),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)), show S - t = 0 by omega,
        show t + 1 - S = t - S + 1 by omega, pow_succ, pow_succ, pow_zero]
      linear_combination (-(B - 1) * q ^ (t - S) - C * q ^ t) * hq
  -- the valuation equation
  have hg : HasSum (fun j : ℕ => ρ ^ j * (if j < S then B * l2 ^ (S - j)
      else 1 + (B - 1) * q ^ (j - S)))
      (ρ ^ S * (1 - ρ)⁻¹ + ρ ^ S * (B - 1) * (1 - ρ * q)⁻¹ + B * H) := by
    rw [← hasSum_nat_add_iff' S]
    have hfin : ∑ i ∈ Finset.range S, ρ ^ i * (if i < S then B * l2 ^ (S - i)
        else 1 + (B - 1) * q ^ (i - S)) = B * H := by
      rw [hHdef, antH, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [ite_eq_left_of_eq_true _ _ (eq_true hi), ← hl2]
      ring
    rw [hfin, add_sub_cancel_right]
    have := ((hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left (ρ ^ S)).add
      ((hasSum_geometric_of_lt_one hρq0 hρq1).mul_left (ρ ^ S * (B - 1)))
    convert this using 1
    funext n
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Nat.add_sub_cancel, mul_pow, pow_add]
    ring
  have hpS : HasSum (fun j : ℕ => ρ ^ j * (antPi σ β κ ρ S j + 0))
      (ρ ^ S * (1 - ρ)⁻¹ + ρ ^ S * (B - 1) * (1 - ρ * q)⁻¹ + B * H + C * (1 - ρ * q)⁻¹) := by
    have := hg.add ((hasSum_geometric_of_lt_one hρq0 hρq1).mul_left C)
    convert this using 1
    funext j
    unfold antPi
    rw [← hBdef, ← hCdef, ← hl1, ← hl2, ← hqdef, mul_pow]
    ring
  have hcS : ∑' j, ρ ^ j * (if S ≤ j then (1 : ℝ) else 0) = ρ ^ S / (1 - ρ) := by
    have := (hasSum_step hρ0.le hρ1 S 0).tsum_eq
    simpa using this
  have hfis : ∑' j, ρ ^ j * (antPi σ β κ ρ S j + 0) -
      ρ * ∑' j, ρ ^ j * (if S ≤ j then (1 : ℝ) else 0) = 0 := by
    rw [hpS.tsum_eq, hcS, hCdef, antC, ← hBdef, ← hHdef, ← hl1]
    have e1 : (1 : ℝ) - ρ ≠ 0 := by linarith
    have e2 : (1 : ℝ) - ρ * q ≠ 0 := by linarith
    have hq' : q * l1 = 1 := by rw [mul_comm]; exact hq
    field_simp
    linear_combination (-(ρ * ρ ^ S + ρ * B * H - ρ ^ 2 * ρ ^ S - ρ ^ 2 * B * H)) * hq'
  -- boundedness
  have hpb : ∀ t, |antPi σ β κ ρ S t| ≤ |B| + (1 + |B - 1|) + |C| := by
    intro t
    unfold antPi
    rw [← hBdef, ← hCdef, ← hl1, ← hl2, ← hqdef]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs
      · rw [abs_mul, abs_of_nonneg (pow_nonneg h2.le _)]
        have := pow_le_one₀ h2.le h21.le (n := S - t)
        nlinarith [abs_nonneg B, abs_nonneg (B - 1)]
      · refine (abs_add_le _ _).trans ?_
        rw [abs_one, abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
        have := pow_le_one₀ hq0 hq1.le (n := t - S)
        nlinarith [abs_nonneg B, abs_nonneg (B - 1)]
    · rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hq0 hq1.le)
  have hcb : ∀ t, |(if S ≤ t then (1 : ℝ) else 0)| ≤ 1 := fun t => by split_ifs <;> simp
  have hdp := det_path 𝔼 hσ hκ hβ hρ0 hρ1 0 (sv := fun _ => 0) (Ms := 0) hcb (fun _ => by simp) hpb
    (fun t => hfac t) hfis
  refine ⟨?_, fun x π v h hπb hvb t ω => ?_⟩
  · obtain ⟨x, v, hE, hvb⟩ := hdp.1
    exact ⟨x, _, v, hE, ⟨_, fun t _ => hpb t⟩, hvb⟩
  · rw [(hdp.2 x π v h hπb hvb).1]

/-- Cochrane (2023), Fig. 5.2: after an anticipated permanent rise inflation converges to the new
rate. -/
theorem anticipated_rise_tendsto {σ β κ ρ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) (S : ℕ) :
    Tendsto (fun t => antPi σ β κ ρ S t) atTop (𝓝 1) := by
  have h1 := one_lt_lam1 (mul_pos hσ hκ) hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hlim := ((hp.comp (tendsto_sub_atTop_nat S)).const_mul (antB σ β κ - 1)).const_add 1 |>.add
    (hp.const_mul (antC σ β κ ρ S))
  simp only [mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop S] with t ht
  unfold antPi
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  rfl

end Cochrane.StickyPriceFiscal.FiscalNK
