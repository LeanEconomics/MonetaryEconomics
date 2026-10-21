/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.WerningModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Equilibrium selection at the zero bound: the deflation jump and the frictionless limit

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 20, §20.2.2–20.2.3,
pp. 474–478.

In the Werning experiment (`WerningModel`) the bounded equilibria form a one-parameter family.
The new-Keynesian selection picks `π_T = 0`; the fiscal selection picks no inflation jump,
`π_0 = 0`. Throughout `u < 0` is the natural rate during the trap (the book: `−2%`), `g = 0`.

## Main results

* Properties of `h(s) = (λ^f e^{λ^b s} + λ^b e^{−λ^f s})/(λ^f+λ^b)`: `hh_strictMonoOn`,
  `one_lt_hh`, `hh_ge`, `kk_pos`; and `hh_strictMono_kappa` (via the `cosh`/`sinh` form
  `hh_eq_cosh`): `h` increases as prices become more flexible (`ρ ≥ 0`).
* The `π_T = 0` equilibrium (p. 475–476): `pi0NK_eq` (`π_0 = −u(1 − h(T))`), `pi0NK_book` (the
  closed form with `(1 − e^{−λ^f T})/λ^f − (e^{λ^b T} − 1)/λ^b`); deflation throughout the trap
  (`nk_pi_neg`), steadily improving (`nk_pi_strictMonoOn`), no inflation after (`nk_after`);
  output gap negative and rising (`nk_x_neg`, `nk_x_strictMonoOn`).
* "Backward explosion" and the frictionless limit: `pi0NK_tendsto_T`, `pi0NK_tendsto_kappa`,
  `nk_tendsto_kappa` (every date of the trap), `pi0NK_strictAnti_kappa` (deflation larger as
  `κ` rises), `x0NK_tendsto_kappa` (and the output gap); `nk_x_eq_HH`
  (`x_t = σu∫_0^{T−t} h`), `nk_x_strictAnti_kappa`, `x0NK_strictAnti_kappa` (the output gap is
  strictly decreasing in `κ` at every date of the trap).
* The frictionless model (p. 477): `frictionless_iff` (`x = −g`, `π = i − u_r`, a unique path).
* The discontinuity (p. 478): `nk_discontinuity`.
* The `π_0 = 0` equilibrium (pp. 476, 478): `nj_pi0`, `nj_formula`, `nj_pos`, `nj_lt`
  (`0 < π_t < −u`), `nj_tendsto_time`, the smooth square-wave limit `nj_limit_trap`,
  `nj_limit_after`, uniformly on compacts (`nj_uniform_trap`, `nj_uniform_after`).
* The fiscal reading (p. 476): `jump_eq_fiscal` — across equilibria
  `π_0 − π_0' = −(r + λ^b)(PV(s̃) − PV(s̃'))`; `nk_fiscal_contraction` — the `π_T = 0`
  equilibrium needs a fiscal contraction, unboundedly large as `κ → ∞`.
* `gap_neg_iff` (p. 476): with `g = 0`, `x_t < 0` iff `dπ/dt > ρπ_t`.
-/

namespace Cochrane.ZeroBound.ZLBSelection

open Filter Topology MeasureTheory
open Cochrane.ZeroBound.ContinuousTimeNK Cochrane.ZeroBound.WerningModel

/-! ## The function `h` -/

/-- Cochrane (2023), §20.2.5, p. 481: `k(s) > 0` for `s > 0`. -/
theorem kk_pos {lf lb s : ℝ} (hf : 0 < lf) (hb : 0 < lb) (hs : 0 < s) : 0 < kk lf lb s := by
  unfold kk
  refine div_pos (sub_pos.2 (Real.exp_lt_exp.2 ?_)) (by linarith)
  nlinarith

/-- Cochrane (2023), §20.2.5, p. 481: `k` is strictly increasing. -/
theorem kk_strictMono {lf lb : ℝ} (hf : 0 < lf) (hb : 0 < lb) : StrictMono (kk lf lb) :=
  strictMono_of_deriv_pos fun s => by
    rw [(kk_hasDerivAt lf lb s).deriv]
    have := Real.exp_pos (lb * s)
    have := Real.exp_pos (-(lf * s))
    positivity

/-- Cochrane (2023), §20.2.2, p. 475: `h` is strictly increasing on `[0, ∞)`. -/
theorem hh_strictMonoOn {lf lb : ℝ} (hf : 0 < lf) (hb : 0 < lb) :
    StrictMonoOn (hh lf lb) (Set.Ici 0) := by
  have hne : lf + lb ≠ 0 := by linarith
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (fun s _ => (hh_hasDerivAt hne s).continuousAt.continuousWithinAt) fun s hs => ?_
  rw [interior_Ici] at hs
  rw [(hh_hasDerivAt hne s).deriv]
  have := kk_pos hf hb hs
  positivity

/-- Cochrane (2023), §20.2.2, p. 475: `h(s) > 1` for `s > 0`. -/
theorem one_lt_hh {lf lb s : ℝ} (hf : 0 < lf) (hb : 0 < lb) (hs : 0 < s) : 1 < hh lf lb s := by
  have h := hh_strictMonoOn hf hb (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs.le) hs
  rwa [hh_zero (by linarith)] at h

/-- Cochrane (2023), §20.2.2, p. 475: the exponential lower bound
`h(s) ≥ λ^f e^{λ^b s}/(λ^f + λ^b)`. -/
theorem hh_ge {lf lb : ℝ} (hf : 0 < lf) (hb : 0 < lb) (s : ℝ) :
    lf * Real.exp (lb * s) / (lf + lb) ≤ hh lf lb s := by
  unfold hh
  have := Real.exp_pos (-(lf * s))
  exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)

/-- Cochrane (2023), §20.2.3, p. 477: `sinh v / v` is strictly increasing on `(0, ∞)`. -/
theorem sinhc_strictMonoOn : StrictMonoOn (fun v => Real.sinh v / v) (Set.Ioi 0) := by
  -- `v cosh v − sinh v > 0` for `v > 0`
  have hg : StrictMonoOn (fun v => v * Real.cosh v - Real.sinh v) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop) fun v hv => ?_
    rw [interior_Ici] at hv
    have hd : HasDerivAt (fun v => v * Real.cosh v - Real.sinh v) (v * Real.sinh v) v := by
      have := ((hasDerivAt_id v).mul (Real.hasDerivAt_cosh v)).sub (Real.hasDerivAt_sinh v)
      refine this.congr_deriv ?_
      simp only [id]
      ring
    rw [hd.deriv]
    exact mul_pos hv (Real.sinh_pos_iff.2 hv)
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
    (fun v hv => ((Real.continuous_sinh.continuousAt.div continuousAt_id
      (ne_of_gt hv)).continuousWithinAt)) fun v hv => ?_
  rw [interior_Ioi] at hv
  have hv0 : (v : ℝ) ≠ 0 := ne_of_gt hv
  have hd : HasDerivAt (fun v => Real.sinh v / v)
      ((v * Real.cosh v - Real.sinh v) / v ^ 2) v := by
    have := (Real.hasDerivAt_sinh v).div (hasDerivAt_id v) hv0
    refine this.congr_deriv ?_
    simp only [id]
    ring
  rw [hd.deriv]
  have h0 := hg (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hv.le) hv
  simp only [Real.sinh_zero, zero_mul, sub_zero] at h0
  positivity

/-- Cochrane (2023), §20.2.3, p. 477: the hyperbolic form of `h`. With `S = λ^f + λ^b`,
`ρ = λ^f − λ^b` and `v = Ss/2 > 0`: `h(s) = e^{−ρs/2}(cosh v + (ρs/2) sinh v / v)`. -/
theorem hh_eq_cosh {lf lb s : ℝ} (hS : 0 < lf + lb) (hs : 0 < s) :
    hh lf lb s = Real.exp (-((lf - lb) * s / 2)) *
      (Real.cosh ((lf + lb) * s / 2) + (lf - lb) * s / 2 *
        (Real.sinh ((lf + lb) * s / 2) / ((lf + lb) * s / 2))) := by
  have hv : (lf + lb) * s / 2 ≠ 0 := by positivity
  rw [Real.cosh_eq, Real.sinh_eq]
  unfold hh
  have e1 : Real.exp (lb * s) =
      Real.exp (-((lf - lb) * s / 2)) * Real.exp ((lf + lb) * s / 2) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(lf * s)) =
      Real.exp (-((lf - lb) * s / 2)) * Real.exp (-((lf + lb) * s / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, e2]
  field_simp
  ring

/-- Cochrane (2023), §20.2.3, p. 477 ("deflation … larger as price stickiness is reduced"):
for `ρ ≥ 0` and `s > 0`, `h(s)` is strictly increasing in `κ`. -/
theorem hh_strictMono_kappa {ρ σ κ κ' s : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 < σ) (hκ : 0 < κ)
    (hlt : κ < κ') (hs : 0 < s) :
    hh (lamf ρ κ σ) (lamb ρ κ σ) s < hh (lamf ρ κ' σ) (lamb ρ κ' σ) s := by
  have hκ' : 0 < κ' := by linarith
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have hS' := lamf_add_lamb_pos (ρ := ρ) hκ' hσ
  rw [hh_eq_cosh hS hs, hh_eq_cosh hS' hs, lamf_sub_lamb, lamf_sub_lamb]
  have hSlt : lamf ρ κ σ + lamb ρ κ σ < lamf ρ κ' σ + lamb ρ κ' σ := by
    have := lamb_strictMono (ρ := ρ) hσ hκ hlt
    have := lamf_strictMono (ρ := ρ) hσ hκ hlt
    linarith
  have hv : 0 < (lamf ρ κ σ + lamb ρ κ σ) * s / 2 := by positivity
  have hvlt : (lamf ρ κ σ + lamb ρ κ σ) * s / 2 < (lamf ρ κ' σ + lamb ρ κ' σ) * s / 2 := by
    have := mul_lt_mul_of_pos_right hSlt hs
    linarith
  have hc : Real.cosh ((lamf ρ κ σ + lamb ρ κ σ) * s / 2) <
      Real.cosh ((lamf ρ κ' σ + lamb ρ κ' σ) * s / 2) := by
    rw [Real.cosh_lt_cosh, abs_of_pos hv, abs_of_pos (by linarith)]
    exact hvlt
  have hsh := sinhc_strictMonoOn (Set.mem_Ioi.2 hv) (Set.mem_Ioi.2 (by linarith)) hvlt
  simp only at hsh
  have hρs : 0 ≤ ρ * s / 2 := by positivity
  refine mul_lt_mul_of_pos_left ?_ (Real.exp_pos _)
  nlinarith

/-! ## The `π_T = 0` (new-Keynesian) equilibrium -/

/-- Cochrane (2023), §20.2.2, p. 475: initial inflation `π_0` in the new-Keynesian `π_T = 0`
equilibrium (`g = 0`). -/
noncomputable def pi0NK (σ κ ρ T u : ℝ) : ℝ := wPi σ κ ρ T u 0 0 0

/-- Cochrane (2023), §20.2.2, p. 475: the `π_T = 0` path during the trap,
`π_t = −u(1 − h(T − t))` for `t ≤ T`. -/
theorem nk_pi_eq {σ κ ρ T u t : ℝ} (htT : t ≤ T) :
    wPi σ κ ρ T u 0 0 t = -u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t)) := by
  simp [wPi, htT, trapPi]

/-- Cochrane (2023), §20.2.2, p. 475: `π_0 = −u(1 − h(T))` in the `π_T = 0` equilibrium. -/
theorem pi0NK_eq {σ κ ρ T u : ℝ} (hT : 0 ≤ T) :
    pi0NK σ κ ρ T u = -u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T) := by
  rw [pi0NK, nk_pi_eq hT, sub_zero]

/-- Cochrane (2023), §20.2.2, pp. 475–476 (cf. Figure 20.5, survey closed form):
`π_0 = −u (κσ/(λ^f+λ^b)) [(1 − e^{−λ^f T})/λ^f − (e^{λ^b T} − 1)/λ^b]`. -/
theorem pi0NK_book {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hT : 0 ≤ T) :
    pi0NK σ κ ρ T u = -u * (κ * σ / (lamf ρ κ σ + lamb ρ κ σ)) *
      ((1 - Real.exp (-(lamf ρ κ σ * T))) / lamf ρ κ σ -
        (Real.exp (lamb ρ κ σ * T) - 1) / lamb ρ κ σ) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  rw [pi0NK_eq hT, hh, ← lamf_mul_lamb hκ hσ]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 476: in the `π_T = 0` equilibrium there is deflation
throughout the trap: `π_t < 0` for `0 ≤ t < T` (when `u < 0`). -/
theorem nk_pi_neg {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (htT : t < T) :
    wPi σ κ ρ T u 0 0 t < 0 := by
  rw [nk_pi_eq htT.le]
  have := one_lt_hh (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) (sub_pos.2 htT)
  nlinarith

/-- Cochrane (2023), §20.2.2, p. 476: in the `π_T = 0` equilibrium inflation and the output gap
are zero from `T` on. -/
theorem nk_after {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : T ≤ t) :
    wPi σ κ ρ T u 0 0 t = 0 ∧ wX σ κ ρ T u 0 0 t = 0 := by
  have hne := (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne'
  rcases eq_or_lt_of_le htT with h | h
  · subst h
    refine ⟨by simp [wPi, trapPi_zero hne], ?_⟩
    simp [wX, trapPi_zero hne, trapY_zero]
  · exact ⟨by simp [wPi, not_le.2 h], by simp [wX, not_le.2 h]⟩

/-- Cochrane (2023), §20.2.2, p. 476 ("deflation steadily improves … no deflation spiral"): the
`π_T = 0` inflation path is strictly increasing on `[0, T]` (when `u < 0`). -/
theorem nk_pi_strictMonoOn {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) :
    StrictMonoOn (wPi σ κ ρ T u 0 0) (Set.Icc 0 T) := by
  intro t1 h1 t2 h2 hlt
  rw [nk_pi_eq h1.2, nk_pi_eq h2.2]
  have := hh_strictMonoOn (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ)
    (Set.mem_Ici.2 (sub_nonneg.2 h2.2)) (Set.mem_Ici.2 (sub_nonneg.2 h1.2))
    (by linarith : T - t2 < T - t1)
  nlinarith

/-- Cochrane (2023), (20.10), p. 475: the `π_T = 0` output gap during the trap,
`κ x_t = λ^f(−u)(1 − h(s)) − λ^b(−u)(1 − e^{−λ^f s})`, `s = T − t`. -/
theorem nk_x_eq {σ κ ρ T u t : ℝ} (hκ : 0 < κ) (htT : t ≤ T) :
    κ * wX σ κ ρ T u 0 0 t = lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t))) -
      lamb ρ κ σ * (-u) * (1 - Real.exp (-(lamf ρ κ σ * (T - t)))) := by
  simp only [wX, htT, ↓reduceIte, trapPi, trapY, zero_mul, mul_zero, add_zero, sub_zero,
    zero_add]
  field_simp

/-- Cochrane (2023), §20.2.2, p. 476 ("a large output gap"): in the `π_T = 0` equilibrium the
output gap is negative throughout the trap (when `u < 0`). -/
theorem nk_x_neg {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (htT : t < T) :
    wX σ κ ρ T u 0 0 t < 0 := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have h1 := one_lt_hh hf hb (sub_pos.2 htT)
  have h2 : Real.exp (-(lamf ρ κ σ * (T - t))) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  have h := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ htT.le
  have : κ * wX σ κ ρ T u 0 0 t < 0 := by
    rw [h]
    have a : lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t))) < 0 := by
      apply mul_neg_of_pos_of_neg hf; nlinarith
    have b : 0 ≤ lamb ρ κ σ * (-u) * (1 - Real.exp (-(lamf ρ κ σ * (T - t)))) := by
      apply mul_nonneg (mul_nonneg hb.le (by linarith)); linarith
    linarith
  nlinarith

/-- Cochrane (2023), §20.2.2, p. 476 ("expected output growth is strong"): the `π_T = 0` output
gap rises strictly over `[0, T]` (when `u < 0`). -/
theorem nk_x_strictMonoOn {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) :
    StrictMonoOn (wX σ κ ρ T u 0 0) (Set.Icc 0 T) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  intro t1 h1 t2 h2 hlt
  have e1 := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ h1.2
  have e2 := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ h2.2
  have hh12 := hh_strictMonoOn hf hb (Set.mem_Ici.2 (sub_nonneg.2 h2.2))
    (Set.mem_Ici.2 (sub_nonneg.2 h1.2)) (by linarith : T - t2 < T - t1)
  have hex : Real.exp (-(lamf ρ κ σ * (T - t1))) < Real.exp (-(lamf ρ κ σ * (T - t2))) := by
    rw [Real.exp_lt_exp]; nlinarith
  have : κ * wX σ κ ρ T u 0 0 t1 < κ * wX σ κ ρ T u 0 0 t2 := by
    rw [e1, e2]
    have a : lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t1))) <
        lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t2))) := by
      apply mul_lt_mul_of_pos_left _ hf; nlinarith
    have b : lamb ρ κ σ * (-u) * (1 - Real.exp (-(lamf ρ κ σ * (T - t2)))) ≤
        lamb ρ κ σ * (-u) * (1 - Real.exp (-(lamf ρ κ σ * (T - t1)))) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb.le (by linarith)); linarith
    linarith
  exact lt_of_mul_lt_mul_left this hκ.le

/-- Cochrane (2023), §20.2.2, p. 477: a lower bound on the deflation jump,
`π_0 ≤ −u(1 − λ^f e^{λ^b T}/(λ^f + λ^b))`. -/
theorem pi0NK_le {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 ≤ T) :
    pi0NK σ κ ρ T u ≤
      -u * (1 - lamf ρ κ σ * Real.exp (lamb ρ κ σ * T) / (lamf ρ κ σ + lamb ρ κ σ)) := by
  rw [pi0NK_eq hT]
  have := hh_ge (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) T
  nlinarith

/-- Cochrane (2023), §20.2.2, p. 477 ("as we move the length of the zero bound episode `T` to
the right, the new-Keynesian deflation blows up"): `π_0 → −∞` as `T → ∞`. -/
theorem pi0NK_tendsto_T {σ κ ρ u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) :
    Tendsto (fun T => pi0NK σ κ ρ T u) atTop atBot := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  set c := -u * lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ)
  have hu' : 0 < -u := by linarith
  have hc : 0 < c := by simp only [c]; positivity
  have h1 : Tendsto (fun T => -u - c * Real.exp (lamb ρ κ σ * T)) atTop atBot := by
    have := ((tendsto_expPos hb).const_mul_atTop hc)
    exact tendsto_atBot_add_const_left _ (-u) (tendsto_neg_atTop_atBot.comp this) |>.congr
      fun T => by simp [sub_eq_add_neg]
  refine tendsto_atBot_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop 0] with T hT
  have := pi0NK_le (ρ := ρ) hσ hκ hu hT
  simp only [c]
  calc pi0NK σ κ ρ T u ≤ -u * (1 - lamf ρ κ σ * Real.exp (lamb ρ κ σ * T) /
      (lamf ρ κ σ + lamb ρ κ σ)) := this
    _ = _ := by ring

/-- Cochrane (2023), §20.2.3, p. 477: for `ρ ≥ 0`, `λ^f/(λ^f + λ^b) ≥ 1/2`. -/
theorem half_le_weight {ρ κ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 < σ) (hκ : 0 < κ) :
    1 / 2 ≤ lamf ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  rw [div_le_div_iff₀ (by norm_num) hS]
  have := lamb_le_lamf (κ := κ) (σ := σ) hρ
  linarith

/-- Cochrane (2023), §20.2.3, p. 477: `e^{λ^b T} → ∞` as `κ → ∞` (`T > 0`). -/
theorem expLamb_tendsto_kappa {ρ σ T : ℝ} (hσ : 0 < σ) (hT : 0 < T) :
    Tendsto (fun κ => Real.exp (lamb ρ κ σ * T)) atTop atTop :=
  Real.tendsto_exp_atTop.comp ((lamb_tendsto_atTop ρ hσ).atTop_mul_const hT)

/-- Cochrane (2023), §20.2.3, p. 477 ("deflation gets worse without limit as prices become
less sticky"): in the `π_T = 0` equilibrium, every date `t ∈ [0, T)` of the trap has
`π_t → −∞` as `κ → ∞` (`ρ ≥ 0`, `u < 0`). -/
theorem nk_tendsto_kappa {σ ρ T u t : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0) (htT : t < T) :
    Tendsto (fun κ => wPi σ κ ρ T u 0 0 t) atTop atBot := by
  have hE := expLamb_tendsto_kappa (ρ := ρ) hσ (sub_pos.2 htT)
  have h1 : Tendsto (fun κ => -u - (-u / 2) * Real.exp (lamb ρ κ σ * (T - t))) atTop atBot := by
    have := hE.const_mul_atTop (by linarith : 0 < -u / 2)
    exact tendsto_atBot_add_const_left _ (-u) (tendsto_neg_atTop_atBot.comp this) |>.congr
      fun κ => by simp [sub_eq_add_neg]
  refine tendsto_atBot_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  rw [nk_pi_eq htT.le]
  have hh1 := hh_ge (lamf_pos (ρ := ρ) hκ hσ) (lamb_pos (ρ := ρ) hκ hσ) (T - t)
  have hw := half_le_weight hρ hσ hκ
  have hE0 := Real.exp_pos (lamb ρ κ σ * (T - t))
  have : Real.exp (lamb ρ κ σ * (T - t)) / 2 ≤ hh (lamf ρ κ σ) (lamb ρ κ σ) (T - t) := by
    refine le_trans ?_ hh1
    have := mul_le_mul_of_nonneg_right hw hE0.le
    rw [mul_div_right_comm]
    linarith
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 477: `π_0 → −∞` as `κ → ∞` in the `π_T = 0` equilibrium. -/
theorem pi0NK_tendsto_kappa {σ ρ T u : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0) (hT : 0 < T) :
    Tendsto (fun κ => pi0NK σ κ ρ T u) atTop atBot :=
  nk_tendsto_kappa hσ hρ hu hT

/-- Cochrane (2023), §20.2.3, p. 477 ("deflation … become[s] larger as price stickiness is
reduced"): for `ρ ≥ 0`, `u < 0`, and every date `t ∈ [0, T)`, `π_t` in the `π_T = 0`
equilibrium is strictly decreasing in `κ`. -/
theorem nk_strictAnti_kappa {σ ρ T u t κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (htT : t < T) (hκ : 0 < κ) (hlt : κ < κ') :
    wPi σ κ' ρ T u 0 0 t < wPi σ κ ρ T u 0 0 t := by
  rw [nk_pi_eq htT.le, nk_pi_eq htT.le]
  have := hh_strictMono_kappa hρ hσ hκ hlt (sub_pos.2 htT) (ρ := ρ)
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 477: `π_0` in the `π_T = 0` equilibrium is strictly decreasing
in `κ`. -/
theorem pi0NK_strictAnti_kappa {σ ρ T u κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (hT : 0 < T) (hκ : 0 < κ) (hlt : κ < κ') : pi0NK σ κ' ρ T u < pi0NK σ κ ρ T u :=
  nk_strictAnti_kappa hσ hρ hu hT hκ hlt

/-- Cochrane (2023), §20.2.3, p. 477 ("(not shown) output gaps become larger"): the time-0 output
gap of the `π_T = 0` equilibrium tends to `−∞` as `κ → ∞` (`ρ ≥ 0`, `u < 0`, `T > 0`). -/
theorem x0NK_tendsto_kappa {σ ρ T u : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0) (hT : 0 < T) :
    Tendsto (fun κ => wX σ κ ρ T u 0 0 0) atTop atBot := by
  -- `x_0 ≤ σ(−u)(1 − e^{λ^b T}/2)/λ^b ≤ −u σ T/2 … `: use `e^{y}/y → ∞`
  have hy : Tendsto (fun κ => lamb ρ κ σ * T) atTop atTop :=
    (lamb_tendsto_atTop ρ hσ).atTop_mul_const hT
  have hq : Tendsto (fun κ => Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) atTop atTop := by
    exact ((Real.tendsto_exp_div_pow_atTop 1).comp hy).congr fun κ => by simp
  have h1 : Tendsto (fun κ => σ * (-u) * T * ((1 : ℝ) - Real.exp (lamb ρ κ σ * T) /
      (lamb ρ κ σ * T) / 2)) atTop atBot := by
    have h2 : Tendsto (fun κ => (1 : ℝ) - Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T) / 2)
        atTop atBot := by
      have := (hq.atTop_div_const (by norm_num : (0 : ℝ) < 2))
      exact tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp this) |>.congr
        fun κ => by simp [sub_eq_add_neg]
    have hu' : 0 < -u := by linarith
    exact h2.const_mul_atBot (by positivity)
  refine tendsto_atBot_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0, hy.eventually_ge_atTop 1] with κ hκ hy1
  have hu' : 0 < -u := by linarith
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have e := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ hT.le
  rw [sub_zero] at e
  have hh1 := hh_ge hf hb T
  have hw := half_le_weight hρ hσ hκ
  have hE0 := Real.exp_pos (lamb ρ κ σ * T)
  have hF : 0 ≤ 1 - Real.exp (-(lamf ρ κ σ * T)) := by
    rw [sub_nonneg, Real.exp_le_one_iff]; nlinarith
  have hhalf : Real.exp (lamb ρ κ σ * T) / 2 ≤ hh (lamf ρ κ σ) (lamb ρ κ σ) T := by
    refine le_trans ?_ hh1
    have := mul_le_mul_of_nonneg_right hw hE0.le
    rw [mul_div_right_comm]
    linarith
  -- `κ x_0 ≤ λ^f (−u)(1 − e^{λ^b T}/2)` and `λ^f/κ = σ/λ^b`
  have hx : κ * wX σ κ ρ T u 0 0 0 ≤ lamf ρ κ σ * (-u * (1 - Real.exp (lamb ρ κ σ * T) / 2)) := by
    rw [e]
    have : 0 ≤ lamb ρ κ σ * -u * (1 - Real.exp (-(lamf ρ κ σ * T))) :=
      mul_nonneg (mul_nonneg hb.le (by linarith)) hF
    have : lamf ρ κ σ * (-u * (1 - hh (lamf ρ κ σ) (lamb ρ κ σ) T)) ≤
        lamf ρ κ σ * (-u * (1 - Real.exp (lamb ρ κ σ * T) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hf.le; nlinarith
    linarith
  have hσl : lamf ρ κ σ / κ = σ / lamb ρ κ σ := by
    field_simp; linarith
  have hx' : wX σ κ ρ T u 0 0 0 ≤ σ / lamb ρ κ σ * (-u * (1 - Real.exp (lamb ρ κ σ * T) / 2)) := by
    rw [← hσl, div_mul_eq_mul_div, le_div_iff₀ hκ]
    linarith
  refine hx'.trans ?_
  have key : σ * -u * T * (1 - Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T) / 2) *
      lamb ρ κ σ = σ * -u * (lamb ρ κ σ * T - Real.exp (lamb ρ κ σ * T) / 2) := by
    field_simp
  rw [div_mul_eq_mul_div, div_le_iff₀ hb, key]
  have := mul_pos hσ hu'
  nlinarith

/-! ## The frictionless model (p. 477) -/

/-- Cochrane (2023), §20.2.3, p. 477: the frictionless (`κ = ∞`) model: the Phillips curve
divided by `κ` gives `x + g = 0` on `[0, ∞)`, and the IS curve (20.5) holds off `S`. -/
def IsFrictionless (σ : ℝ) (i u g : ℝ → ℝ) (S : Set ℝ) (x π : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → x t + g t = 0) ∧
    ∀ t, 0 < t → t ∉ S → HasDerivAt x (σ * (i t - π t - u t)) t

/-- Cochrane (2023), §20.2.3, p. 477: **the frictionless solution is unique**: with `σ ≠ 0`,
`(x, π)` solves the frictionless model of the experiment iff `x = −g` and `π = i − u_r = −u` on
`(0, T)`, `0` after `T` ("inflation simply jumps up to 2% … returning to 0 the minute the shock
ends"; no output gap when `g = 0`). -/
theorem frictionless_iff {σ T u g : ℝ} (hσ : σ ≠ 0) {x π : ℝ → ℝ} :
    IsFrictionless σ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ↔
      (∀ t, 0 ≤ t → x t = -trapStep g T t) ∧ ∀ t, 0 < t → t ≠ T → π t = -trapStep u T t := by
  have hloc : ∀ t, 0 < t → t ≠ T → ∀ x : ℝ → ℝ, (∀ s, 0 ≤ s → x s = -trapStep g T s) →
      HasDerivAt x 0 t := by
    intro t ht htT x hx
    rcases lt_or_gt_of_ne htT with h | h
    · have ev : (fun _ => -g) =ᶠ[𝓝 t] x := by
        filter_upwards [Ioo_mem_nhds ht h] with s hs
        rw [hx s hs.1.le]; simp [trapStep, hs.2]
      exact (hasDerivAt_const t (-g)).congr_of_eventuallyEq ev.symm
    · have ev : (fun _ => (0 : ℝ)) =ᶠ[𝓝 t] x := by
        filter_upwards [Ioi_mem_nhds h, Ioi_mem_nhds ht] with s (hs : T < s) (hs0 : 0 < s)
        rw [hx s hs0.le]; simp [trapStep, not_lt.2 hs.le]
      exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ev.symm
  constructor
  · rintro ⟨h1, h2⟩
    have hx : ∀ t, 0 ≤ t → x t = -trapStep g T t := fun t ht => by linarith [h1 t ht]
    refine ⟨hx, fun t ht htT => ?_⟩
    have := (h2 t ht htT).unique (hloc t ht htT x hx)
    have h0 : 0 - π t - trapStep u T t = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hσ
      · exact h
    linarith
  · rintro ⟨hx, hπ⟩
    refine ⟨fun t ht => by rw [hx t ht]; ring, fun t ht htT => ?_⟩
    refine (hloc t ht htT x hx).congr_deriv ?_
    rw [hπ t ht htT]
    ring

/-- Cochrane (2023), §20.2.3, p. 478 (**the puzzling discontinuity**): with `ρ ≥ 0`, `u < 0`, at
every date `t ∈ (0, T)` the `π_T = 0` inflation `π_t(κ)` does not converge, as `κ → ∞`, to the
frictionless value `−u` (it diverges to `−∞`), although the frictionless model is well behaved
(`frictionless_iff`). -/
theorem nk_discontinuity {σ ρ T u t : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0) (htT : t < T) :
    ¬ Tendsto (fun κ => wPi σ κ ρ T u 0 0 t) atTop (𝓝 (-u)) := fun h =>
  not_tendsto_nhds_of_tendsto_atBot (nk_tendsto_kappa hσ hρ hu htT) (-u) h

/-! ## The `π_0 = 0` (no-jump) equilibrium -/

/-- Cochrane (2023), §20.2.2, p. 476: the end-of-trap inflation of the no-jump equilibrium,
`π_T = −u(h(T) − 1)e^{−λ^b T}`. -/
noncomputable def piTnj (σ κ ρ T u : ℝ) : ℝ :=
  -u * (hh (lamf ρ κ σ) (lamb ρ κ σ) T - 1) * Real.exp (-(lamb ρ κ σ * T))

/-- Cochrane (2023), §20.2.2, p. 476: the no-jump equilibrium has `π_0 = 0`. -/
theorem nj_pi0 {σ κ ρ T u : ℝ} (hT : 0 ≤ T) : wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) 0 = 0 := by
  simp only [wPi, hT, ↓reduceIte, trapPi, piTnj, sub_zero, zero_mul, mul_zero, add_zero]
  have : Real.exp (-(lamb ρ κ σ * T)) * Real.exp (lamb ρ κ σ * T) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (-u * (hh (lamf ρ κ σ) (lamb ρ κ σ) T - 1)) * this

/-- Cochrane (2023), §20.2.2, p. 476: the no-jump path during the trap, for `0 ≤ t ≤ T`:
`π_t = −u[1 − e^{−λ^b t} − (λ^b/(λ^f+λ^b))(e^{−λ^f(T−t)} − e^{−λ^f T}e^{−λ^b t})]`. -/
theorem nj_formula {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : t ≤ T) :
    wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t = -u * (1 - Real.exp (-(lamb ρ κ σ * t)) -
      lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (Real.exp (-(lamf ρ κ σ * (T - t))) -
        Real.exp (-(lamf ρ κ σ * T)) * Real.exp (-(lamb ρ κ σ * t)))) := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  simp only [wPi, htT, ↓reduceIte, trapPi, piTnj, hh, zero_mul, mul_zero, add_zero]
  have e4 : Real.exp (lamb ρ κ σ * (T - t)) = Real.exp (lamb ρ κ σ * T) *
      Real.exp (-(lamb ρ κ σ * t)) := by rw [← Real.exp_add]; ring_nf
  rw [e4, Real.exp_neg (lamb ρ κ σ * T)]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 476: the key inequality behind `0 < π_t` in the no-jump
equilibrium, `λ^f(1 − e^{−λ^b t}) > λ^b e^{−λ^b t}(1 − e^{−λ^f t})` for `t > 0`. -/
theorem nj_key {lf lb t : ℝ} (hf : 0 < lf) (hb : 0 < lb) (ht : 0 < t) :
    lb * Real.exp (-(lb * t)) * (1 - Real.exp (-(lf * t))) <
      lf * (1 - Real.exp (-(lb * t))) := by
  have hE : lb * t + 1 < Real.exp (lb * t) := Real.add_one_lt_exp (by positivity)
  have hG : -(lf * t) + 1 ≤ Real.exp (-(lf * t)) := Real.add_one_le_exp _
  have hinv : Real.exp (-(lb * t)) * Real.exp (lb * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (lb * t)
  have ha := Real.exp_pos (-(lb * t))
  -- multiply through by `e^{λ^b t}`
  have h1 : lb * (1 - Real.exp (-(lf * t))) < lf * (Real.exp (lb * t) - 1) := by
    have : lb * (1 - Real.exp (-(lf * t))) ≤ lb * (lf * t) :=
      mul_le_mul_of_nonneg_left (by linarith) hb.le
    have : lf * (lb * t) < lf * (Real.exp (lb * t) - 1) :=
      mul_lt_mul_of_pos_left (by linarith) hf
    nlinarith
  have h2 := mul_lt_mul_of_pos_left h1 ha
  nlinarith

/-- Cochrane (2023), §20.2.2, p. 476 ("the declining natural rate is met by a slight inflation
rise"): in the no-jump equilibrium inflation is positive at every `t > 0` (`u < 0`, `T > 0`). -/
theorem nj_pos {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 < T)
    (ht : 0 < t) : 0 < wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  -- the value on the trap
  have htrap : ∀ s, 0 < s → s ≤ T → 0 < wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) s := by
    intro s hs hsT
    rw [nj_formula hσ hκ hsT]
    have hkey := nj_key hf hb hs
    set a := Real.exp (-(lamb ρ κ σ * s))
    set c := Real.exp (-(lamf ρ κ σ * s))
    set b := Real.exp (-(lamf ρ κ σ * (T - s)))
    have hH : Real.exp (-(lamf ρ κ σ * T)) = b * c := by
      simp only [b, c]; rw [← Real.exp_add]; ring_nf
    have hb1 : b ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    have hb0 : 0 < b := Real.exp_pos _
    have ha0 : 0 < a := Real.exp_pos _
    have hc1 : c ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    have hc0 : 0 < c := Real.exp_pos _
    have ha1 : a < 1 := by rw [Real.exp_lt_one_iff]; nlinarith
    rw [hH]
    have hac : 0 ≤ 1 - c * a := by nlinarith
    have : lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) ≤
        lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (1 - c * a) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
    have hfrac : 0 < 1 - a - lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (1 - c * a) := by
      rw [div_mul_eq_mul_div, sub_pos, div_lt_iff₀ hS]
      nlinarith
    have : 0 < 1 - a - lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) := by linarith
    have hu' : 0 < -u := by linarith
    positivity
  rcases le_or_gt t T with h | h
  · exact htrap t ht h
  · have hT' := htrap T hT le_rfl
    rw [wPi_T hκ hσ] at hT'
    simp only [wPi, not_le.2 h, ↓reduceIte]
    positivity

/-- Cochrane (2023), §20.2.2, p. 476: in the no-jump equilibrium inflation stays below the
frictionless value `−u` (`= 2%` in the book) at every `t ≥ 0`. -/
theorem nj_lt {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 ≤ T)
    (ht : 0 ≤ t) : wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t < -u := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have htrap : ∀ s, 0 ≤ s → s ≤ T → wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) s < -u := by
    intro s hs hsT
    rw [nj_formula hσ hκ hsT]
    set a := Real.exp (-(lamb ρ κ σ * s))
    set c := Real.exp (-(lamf ρ κ σ * s))
    set b := Real.exp (-(lamf ρ κ σ * (T - s)))
    have hH : Real.exp (-(lamf ρ κ σ * T)) = b * c := by
      simp only [b, c]; rw [← Real.exp_add]; ring_nf
    have hb0 : 0 < b := Real.exp_pos _
    have ha0 : 0 < a := Real.exp_pos _
    have hc1 : c ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    have hc0 : 0 < c := Real.exp_pos _
    have ha1 : a ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
    rw [hH]
    have : 0 ≤ lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) := by
      apply mul_nonneg (by positivity)
      have : c * a ≤ 1 := by nlinarith
      nlinarith
    have hu' : 0 < -u := by linarith
    nlinarith
  rcases le_or_gt t T with h | h
  · exact htrap t ht h
  · have hT' := htrap T hT le_rfl
    rw [wPi_T hκ hσ] at hT'
    simp only [wPi, not_le.2 h, ↓reduceIte]
    have hle : Real.exp (-(lamb ρ κ σ * (t - T))) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h0 : 0 ≤ piTnj σ κ ρ T u := by
      rcases eq_or_lt_of_le hT with h0 | h0
      · subst h0
        simp [piTnj, hh_zero (lamf_add_lamb_pos (ρ := ρ) hκ hσ).ne']
      · have := nj_pos (ρ := ρ) hσ hκ hu h0 h0
        rw [wPi_T hκ hσ] at this
        exact this.le
    nlinarith [Real.exp_pos (-(lamb ρ κ σ * (t - T)))]

/-- Cochrane (2023), §20.2.2, p. 476: the no-jump end-of-trap inflation satisfies
`0 < π_T < −u` (it is "only slightly higher" than in the `π_T = 0` equilibrium). -/
theorem piTnj_bounds {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (hT : 0 < T) :
    0 < piTnj σ κ ρ T u ∧ piTnj σ κ ρ T u < -u := by
  have h1 := nj_pos (ρ := ρ) hσ hκ hu hT hT
  have h2 := nj_lt (ρ := ρ) hσ hκ hu hT.le hT.le
  rw [wPi_T hκ hσ] at h1 h2
  exact ⟨h1, h2⟩

/-- Cochrane (2023), §20.2.2, p. 476: after the trap the no-jump inflation decays to zero. -/
theorem nj_tendsto_time {σ κ ρ T u : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) :
    Tendsto (fun t => wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t) atTop (𝓝 0) := by
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have h : Tendsto (fun t => piTnj σ κ ρ T u * Real.exp (-(lamb ρ κ σ * (t - T)))) atTop
      (𝓝 0) := by
    have := ((tendsto_expNeg hb).comp (tendsto_atTop_add_const_right atTop (-T) tendsto_id))
    have := this.const_mul (piTnj σ κ ρ T u)
    rw [mul_zero] at this
    refine this.congr fun t => ?_
    simp [Function.comp, sub_eq_add_neg]
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop T] with t ht
  simp [wPi, not_le.2 ht]

/-- Cochrane (2023), §20.2.3, p. 478: `e^{−λ^b c} → 0` and `e^{−λ^f c} → 0` as `κ → ∞`
(`c > 0`). -/
theorem expNeg_lam_tendsto {ρ σ c : ℝ} (hσ : 0 < σ) (hc : 0 < c) :
    Tendsto (fun κ => Real.exp (-(lamb ρ κ σ * c))) atTop (𝓝 0) ∧
      Tendsto (fun κ => Real.exp (-(lamf ρ κ σ * c))) atTop (𝓝 0) :=
  ⟨Real.tendsto_exp_neg_atTop_nhds_zero.comp ((lamb_tendsto_atTop ρ hσ).atTop_mul_const hc),
    Real.tendsto_exp_neg_atTop_nhds_zero.comp ((lamf_tendsto_atTop ρ hσ).atTop_mul_const hc)⟩

/-- Cochrane (2023), §20.2.3, p. 478: during the trap, the no-jump inflation is within
`−u(e^{−λ^b t} + e^{−λ^f(T−t)})` of the frictionless value `−u`. -/
theorem nj_dist_trap {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hu : u < 0) (ht : 0 ≤ t)
    (htT : t ≤ T) :
    |wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t - -u| ≤
      -u * (Real.exp (-(lamb ρ κ σ * t)) + Real.exp (-(lamf ρ κ σ * (T - t)))) := by
  have hS := lamf_add_lamb_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hf := lamf_pos (ρ := ρ) hκ hσ
  rw [nj_formula hσ hκ htT]
  set a := Real.exp (-(lamb ρ κ σ * t))
  set c := Real.exp (-(lamf ρ κ σ * t))
  set b := Real.exp (-(lamf ρ κ σ * (T - t)))
  have hH : Real.exp (-(lamf ρ κ σ * T)) = b * c := by
    simp only [b, c]; rw [← Real.exp_add]; ring_nf
  have hb0 : 0 < b := Real.exp_pos _
  have ha0 : 0 < a := Real.exp_pos _
  have hc1 : c ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  have hc0 : 0 < c := Real.exp_pos _
  have ha1 : a ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith
  rw [hH]
  have hα0 : 0 ≤ lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) := by positivity
  have hα1 : lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) ≤ 1 := by
    rw [div_le_one hS]; linarith
  have hca : 0 ≤ 1 - c * a := by nlinarith
  have hm : 0 ≤ lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) := by
    apply mul_nonneg hα0; nlinarith
  have hM : lamb ρ κ σ / (lamf ρ κ σ + lamb ρ κ σ) * (b - b * c * a) ≤ b := by
    have : 0 ≤ b * c * a := by positivity
    have : b - b * c * a ≤ b := by linarith
    calc _ ≤ 1 * (b - b * c * a) := by
          apply mul_le_mul_of_nonneg_right hα1; nlinarith
      _ ≤ b := by linarith
  have hu' : 0 < -u := by linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- Cochrane (2023), §20.2.3, p. 478 ("inflation smoothly rises to fill out a square function,
2% inflation from `t = 0` to `t = T`"): at every `t ∈ (0, T)`, the no-jump inflation converges to
the frictionless value `−u` as `κ → ∞`. -/
theorem nj_limit_trap {σ ρ T u t : ℝ} (hσ : 0 < σ) (hu : u < 0) (ht : 0 < t) (htT : t < T) :
    Tendsto (fun κ => wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t) atTop (𝓝 (-u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (expNeg_lam_tendsto (ρ := ρ) hσ ht).1
  have h2 := (expNeg_lam_tendsto (ρ := ρ) hσ (sub_pos.2 htT)).2
  have h3 := (h1.add h2).const_mul (-u)
  rw [add_zero, mul_zero] at h3
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h3
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  exact nj_dist_trap hσ hκ hu ht.le htT.le

/-- Cochrane (2023), §20.2.3, p. 478 ("ε price stickiness implies δ deviation"): the
convergence to the frictionless square wave is uniform on every compact `[t₁, t₂] ⊂ (0, T)`. -/
theorem nj_uniform_trap {σ ρ T u t1 t2 : ℝ} (hσ : 0 < σ) (hu : u < 0) (h1 : 0 < t1)
    (h2 : t2 < T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ κ in atTop, ∀ t ∈ Set.Icc t1 t2,
      |wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t - -u| < ε := by
  have ha := (expNeg_lam_tendsto (ρ := ρ) hσ h1).1
  have hb := (expNeg_lam_tendsto (ρ := ρ) hσ (sub_pos.2 h2)).2
  have h3 := (ha.add hb).const_mul (-u)
  rw [add_zero, mul_zero] at h3
  filter_upwards [eventually_gt_atTop 0, h3.eventually (gt_mem_nhds hε)] with κ hκ hlt t ht
  refine lt_of_le_of_lt (nj_dist_trap hσ hκ hu (by linarith [ht.1]) (by linarith [ht.2])) ?_
  have hb0 := lamb_pos (ρ := ρ) hκ hσ
  have hf0 := lamf_pos (ρ := ρ) hκ hσ
  have e1 : Real.exp (-(lamb ρ κ σ * t)) ≤ Real.exp (-(lamb ρ κ σ * t1)) :=
    Real.exp_le_exp.2 (by nlinarith [ht.1])
  have e2 : Real.exp (-(lamf ρ κ σ * (T - t))) ≤ Real.exp (-(lamf ρ κ σ * (T - t2))) :=
    Real.exp_le_exp.2 (by nlinarith [ht.2])
  have hu' : 0 < -u := by linarith
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 478: after the trap (`t > T`) the no-jump inflation converges to
the frictionless value `0` as `κ → ∞`, uniformly on `[t₃, ∞)` for every `t₃ > T`. -/
theorem nj_uniform_after {σ ρ T u t3 : ℝ} (hσ : 0 < σ) (hu : u < 0) (hT : 0 < T) (h3 : T < t3)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ κ in atTop, ∀ t, t3 ≤ t → |wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t| < ε := by
  have ha := ((expNeg_lam_tendsto (ρ := ρ) hσ (sub_pos.2 h3)).1).const_mul (-u)
  rw [mul_zero] at ha
  filter_upwards [eventually_gt_atTop 0, ha.eventually (gt_mem_nhds hε)] with κ hκ hlt t ht
  have hb0 := lamb_pos (ρ := ρ) hκ hσ
  obtain ⟨p0, p1⟩ := piTnj_bounds (ρ := ρ) hσ hκ hu hT
  have htT : T < t := by linarith
  simp only [wPi, not_le.2 htT, ↓reduceIte]
  rw [abs_of_pos (by positivity)]
  have e1 : Real.exp (-(lamb ρ κ σ * (t - T))) ≤ Real.exp (-(lamb ρ κ σ * (t3 - T))) :=
    Real.exp_le_exp.2 (by nlinarith)
  have := Real.exp_pos (-(lamb ρ κ σ * (t - T)))
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 478: pointwise after the trap, the no-jump inflation converges
to the frictionless value `0` as `κ → ∞`. -/
theorem nj_limit_after {σ ρ T u t : ℝ} (hσ : 0 < σ) (hu : u < 0) (hT : 0 < T) (ht : T < t) :
    Tendsto (fun κ => wPi σ κ ρ T u 0 (piTnj σ κ ρ T u) t) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [nj_uniform_after (ρ := ρ) hσ hu hT ht hε] with κ hκ
  rw [Real.dist_eq, sub_zero]
  exact hκ t le_rfl

/-! ## The fiscal reading of the time-0 jump (p. 476) -/

/-- Cochrane (2023), §20.2.2, p. 476 (and §5.7, (5.93)): the government debt valuation along a
path with `i = 0`: `v` continuous on `[0, ∞)`, `dv/dt = rv + (i − π) − s̃` on `(0, ∞)`, and the
transversality condition `e^{−rT}v_T → 0`. -/
def IsValuation (r : ℝ) (π s v : ℝ → ℝ) : Prop :=
  ContinuousOn v (Set.Ici 0) ∧ (∀ t, 0 < t → HasDerivAt v (r * v t + (0 - π t) - s t) t) ∧
    Tendsto (fun T => Real.exp (-(r * T)) * v T) atTop (𝓝 0)

/-- Cochrane (2023), §20.2.2, p. 476 ("a fiscal theorist picks the equilibrium by the fiscal
innovation at time 0"): **the inflation jump is the fiscal innovation.** For two bounded
equilibria of the experiment with the same predetermined debt `v_0` (and integrable discounted
surpluses), `π_0 − π_0' = −(r + λ^b)(∫_0^∞ e^{−rτ}s̃_τ dτ − ∫_0^∞ e^{−rτ}s̃'_τ dτ)`. -/
theorem jump_eq_fiscal {σ κ ρ T u g r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hr : 0 < r)
    {x π x' π' s s' v v' : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π)
    (h' : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep g T) {T} x' π' ∧ BddOnIci x' ∧
      BddOnIci π')
    (hv : IsValuation r π s v) (hv' : IsValuation r π' s' v') (h0 : v 0 = v' 0)
    (hs : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0))
    (hs' : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s' τ) (Set.Ioi 0)) :
    π 0 - π' 0 = -(r + lamb ρ κ σ) * ((∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s' τ) := by
  have hb := lamb_pos (ρ := ρ) hκ hσ
  -- the two inflation paths differ by `(π_0 − π_0') e^{−λ^b t}`
  have hdiff := homog_bdd hσ hκ ((Set.countable_singleton T).union (Set.countable_singleton T))
    (h.1.sub h'.1)
    (by obtain ⟨K1, h1⟩ := h.2.1; obtain ⟨K2, h2⟩ := h'.2.1
        exact ⟨K1 + K2, fun t ht => (abs_sub _ _).trans (add_le_add (h1 t ht) (h2 t ht))⟩)
    (by obtain ⟨K1, h1⟩ := h.2.2; obtain ⟨K2, h2⟩ := h'.2.2
        exact ⟨K1 + K2, fun t ht => (abs_sub _ _).trans (add_le_add (h1 t ht) (h2 t ht))⟩)
  -- integrability of the discounted inflation paths
  have hint : ∀ (p : ℝ → ℝ), ContinuousOn p (Set.Ici 0) → BddOnIci p →
      IntegrableOn (fun τ => Real.exp (-(r * τ)) * p τ) (Set.Ioi 0) := by
    intro p hp ⟨K, hK⟩
    exact integrableOn_exp_mul_of_bdd hr
      ((hp.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
      fun τ hτ => hK τ hτ.le
  have iπ := hint π h.1.2.1 h.2.2
  have iπ' := hint π' h'.1.2.1 h'.2.2
  -- the valuation equation at `0`
  have val : ∀ (p q w : ℝ → ℝ), IsValuation r p q w →
      IntegrableOn (fun τ => Real.exp (-(r * τ)) * q τ) (Set.Ioi 0) →
      IntegrableOn (fun τ => Real.exp (-(r * τ)) * p τ) (Set.Ioi 0) →
      w 0 = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * q τ) +
        ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * p τ := by
    intro p q w ⟨hc, hd, htvc⟩ iq ip
    have hI : IntegrableOn (fun τ => Real.exp (-(r * τ)) * (q τ + p τ)) (Set.Ioi 0) :=
      (iq.add ip).congr_fun (fun τ _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
    have := (tvc_iff_forward (f := fun τ => q τ + p τ) (t := 0) hc
      (fun τ hτ => (hd τ hτ).congr_deriv (by ring)) hI).1 htvc
    rw [this, ← integral_add iq ip]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
    simp only [zero_add]
    ring
  have e1 := val π s v hv hs iπ
  have e2 := val π' s' v' hv' hs' iπ'
  -- `∫ e^{−rτ}(π − π') = (π_0 − π_0')/(r + λ^b)`
  have hpi : ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * π τ =
      (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * π' τ) + (π 0 - π' 0) / (r + lamb ρ κ σ) := by
    have hEq : Set.EqOn (fun τ => Real.exp (-(r * τ)) * π τ)
        (fun τ => Real.exp (-(r * τ)) * π' τ +
          (π 0 - π' 0) * Real.exp (-((r + lamb ρ κ σ) * τ))) (Set.Ioi 0) := by
      intro τ hτ
      have := (hdiff τ (le_of_lt hτ)).1
      simp only at this ⊢
      have he : Real.exp (-((r + lamb ρ κ σ) * τ)) =
          Real.exp (-(r * τ)) * Real.exp (-(lamb ρ κ σ * τ)) := by
        rw [← Real.exp_add]; ring_nf
      rw [he]
      linear_combination Real.exp (-(r * τ)) * this
    rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_add iπ'
      ((integrableOn_exp_Ioi (by linarith : 0 < r + lamb ρ κ σ)).const_mul _),
      integral_const_mul, integral_exp_Ioi (by linarith)]
    ring
  have hrb : 0 < r + lamb ρ κ σ := by linarith
  rw [h0] at e1
  rw [e1, hpi] at e2
  have hq : (π 0 - π' 0) / (r + lamb ρ κ σ) = (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s' τ) -
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ := by linarith
  rw [div_eq_iff hrb.ne'] at hq
  rw [hq]
  ring

/-- Cochrane (2023), §20.2.2, p. 476 ("the deflation jump must correspond to a large fiscal
contraction"): the extra present value of surpluses required by the `π_T = 0` equilibrium
relative to the no-jump equilibrium, `−π_0^{NK}/(r + λ^b)`. -/
noncomputable def fiscalContraction (σ κ ρ T u r : ℝ) : ℝ :=
  -pi0NK σ κ ρ T u / (r + lamb ρ κ σ)

/-- Cochrane (2023), §20.2.2, p. 476: **the `π_T = 0` equilibrium requires a fiscal
contraction**: with the same predetermined debt, the present value of surpluses in any
`π_T = 0` equilibrium exceeds that of any no-jump (`π_0 = 0`) equilibrium by
`fiscalContraction > 0` (`u < 0`, `T > 0`). -/
theorem nk_fiscal_contraction {σ κ ρ T u r : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hr : 0 < r)
    (hu : u < 0) (hT : 0 < T) {x π x' π' s s' v v' : ℝ → ℝ}
    (h : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep 0 T) {T} x π ∧ BddOnIci x ∧
      BddOnIci π) (hNK : π T = 0)
    (h' : IsPath σ ρ κ (fun _ => 0) (trapStep u T) (trapStep 0 T) {T} x' π' ∧ BddOnIci x' ∧
      BddOnIci π') (hNJ : π' 0 = 0)
    (hv : IsValuation r π s v) (hv' : IsValuation r π' s' v') (h0 : v 0 = v' 0)
    (hs : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s τ) (Set.Ioi 0))
    (hs' : IntegrableOn (fun τ => Real.exp (-(r * τ)) * s' τ) (Set.Ioi 0)) :
    (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s τ) -
        (∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * s' τ) = fiscalContraction σ κ ρ T u r ∧
      0 < fiscalContraction σ κ ρ T u r := by
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hrb : 0 < r + lamb ρ κ σ := by linarith
  have hj := jump_eq_fiscal hσ hκ hr h h' hv hv' h0 hs hs'
  obtain ⟨πT, hπT⟩ := (bdd_path_iff hκ hσ).1 h
  have hπT0 : πT = 0 := by rw [← wPi_T hκ hσ T u 0 πT, ← (hπT T hT.le).1, hNK]
  have hπ0 : π 0 = pi0NK σ κ ρ T u := by rw [(hπT 0 le_rfl).1, hπT0, pi0NK]
  rw [hπ0, hNJ, sub_zero] at hj
  have hneg : pi0NK σ κ ρ T u < 0 := nk_pi_neg hσ hκ hu hT
  refine ⟨?_, div_pos (by linarith) hrb⟩
  rw [fiscalContraction, hj]
  field_simp

/-- Cochrane (2023), §20.2.2–20.2.3, pp. 476–477: the required fiscal contraction grows without
bound as prices become flexible (`ρ ≥ 0`, `u < 0`, `T > 0`). -/
theorem fiscalContraction_tendsto {σ ρ T u r : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (hT : 0 < T) (hr : 0 < r) :
    Tendsto (fun κ => fiscalContraction σ κ ρ T u r) atTop atTop := by
  have hy : Tendsto (fun κ => lamb ρ κ σ * T) atTop atTop :=
    (lamb_tendsto_atTop ρ hσ).atTop_mul_const hT
  have hq : Tendsto (fun κ => Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) atTop atTop :=
    ((Real.tendsto_exp_div_pow_atTop 1).comp hy).congr fun κ => by simp
  have hu' : 0 < -u := by linarith
  -- `fiscalContraction ≥ (−u)(T/4) e^{λ^b T}/(λ^b T) − (−u)/r` once `λ^b ≥ r`
  have h1 : Tendsto (fun κ => -u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) -
      -u / r) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (hq.const_mul_atTop (by positivity))
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_gt_atTop 0, (lamb_tendsto_atTop ρ hσ).eventually_ge_atTop r]
    with κ hκ hbr
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hrb : 0 < r + lamb ρ κ σ := by linarith
  have hE0 := Real.exp_pos (lamb ρ κ σ * T)
  have hle := pi0NK_le (ρ := ρ) hσ hκ hu hT.le
  have hw := half_le_weight hρ hσ hκ
  have hhalf : Real.exp (lamb ρ κ σ * T) / 2 ≤
      lamf ρ κ σ * Real.exp (lamb ρ κ σ * T) / (lamf ρ κ σ + lamb ρ κ σ) := by
    have := mul_le_mul_of_nonneg_right hw hE0.le
    rw [mul_div_right_comm]
    linarith
  -- `−π_0 ≥ (−u)(e^{λ^b T}/2 − 1)`
  have hpi : -u * (Real.exp (lamb ρ κ σ * T) / 2 - 1) ≤ -pi0NK σ κ ρ T u := by nlinarith
  unfold fiscalContraction
  rw [le_div_iff₀ hrb]
  -- `(r + λ^b) ≤ 2λ^b`
  have key : (-u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) - -u / r) *
      (r + lamb ρ κ σ) ≤ -u * (Real.exp (lamb ρ κ σ * T) / 2 - 1) := by
    have e1 : -u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) * lamb ρ κ σ =
        -u * Real.exp (lamb ρ κ σ * T) / 4 := by field_simp
    have e2 : -u / r * r = -u := by field_simp
    have hA : 0 ≤ -u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) := by positivity
    have e3 : -u * (T / 4) * (Real.exp (lamb ρ κ σ * T) / (lamb ρ κ σ * T)) * r ≤
        -u * Real.exp (lamb ρ κ σ * T) / 4 := by
      rw [← e1]; exact mul_le_mul_of_nonneg_left hbr hA
    have hB : 0 ≤ -u / r * lamb ρ κ σ := by positivity
    nlinarith
  linarith

/-- Cochrane (2023), §20.2.2, p. 476 ("the forward-looking Phillips curve (20.6) only produces a
large output gap when inflation is lower today than in the future"): along a path, at a date
where (20.6) holds and `g_t = 0`, `x_t < 0` iff `dπ/dt > ρπ_t`. -/
theorem gap_neg_iff {σ ρ κ t : ℝ} (hκ : 0 < κ) {i u g x π : ℝ → ℝ} {S : Set ℝ}
    (h : IsPath σ ρ κ i u g S x π) (ht : 0 < t) (hS : t ∉ S) (hg : g t = 0) :
    x t < 0 ↔ ρ * π t < deriv π t := by
  rw [((h.2.2 t ht hS).2).deriv, hg, add_zero]
  constructor
  · intro hx; nlinarith
  · intro hx; nlinarith

/-! ## The output gap of the `π_T = 0` equilibrium is strictly decreasing in `κ` (p. 477) -/

/-- Cochrane (2023), §20.2.3, p. 477: the antiderivative of `h`,
`H(s) = [(λ^f/λ^b)(e^{λ^b s} − 1) + (λ^b/λ^f)(1 − e^{−λ^f s})]/(λ^f + λ^b) = ∫_0^s h`. -/
noncomputable def HH (lf lb s : ℝ) : ℝ :=
  (lf / lb * (Real.exp (lb * s) - 1) + lb / lf * (1 - Real.exp (-(lf * s)))) / (lf + lb)

/-- Cochrane (2023), §20.2.3, p. 477: `H(0) = 0`. -/
theorem HH_zero (lf lb : ℝ) : HH lf lb 0 = 0 := by
  simp [HH]

/-- Cochrane (2023), §20.2.3, p. 477: `H' = h`. -/
theorem HH_hasDerivAt {lf lb : ℝ} (hf : 0 < lf) (hb : 0 < lb) (s : ℝ) :
    HasDerivAt (HH lf lb) (hh lf lb s) s := by
  have := ((((hasDerivAt_expPos lb s).sub_const 1).const_mul (lf / lb)).add
    (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_expNeg lf s)).const_mul (lb / lf))).div_const
    (lf + lb)
  refine this.congr_deriv ?_
  simp only [hh]
  field_simp
  ring

/-- Cochrane (2023), §20.2.2, p. 475 (the IS curve integrated back from `x_T = 0`): during the
trap the `π_T = 0` output gap is `x_t = σ u H(T − t)`, i.e. `x_t = −σ(−u)∫_0^{T−t} h`. -/
theorem nk_x_eq_HH {σ κ ρ T u t : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (htT : t ≤ T) :
    wX σ κ ρ T u 0 0 t = σ * u * HH (lamf ρ κ σ) (lamb ρ κ σ) (T - t) := by
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hmul := lamf_mul_lamb (ρ := ρ) hκ hσ
  have e := nk_x_eq (σ := σ) (ρ := ρ) (u := u) hκ htT
  apply mul_left_cancel₀ hκ.ne'
  rw [e]
  have key : κ * (σ * u * HH (lamf ρ κ σ) (lamb ρ κ σ) (T - t)) =
      lamf ρ κ σ * lamb ρ κ σ * u * HH (lamf ρ κ σ) (lamb ρ κ σ) (T - t) := by
    rw [hmul]; ring
  rw [key]
  simp only [HH, hh]
  field_simp
  ring

/-- Cochrane (2023), §20.2.3, p. 477: for `ρ ≥ 0` and `s > 0`, `H(s)` is strictly increasing in
`κ` (because `h` is, at every date). -/
theorem HH_strictMono_kappa {ρ σ κ κ' s : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 < σ) (hκ : 0 < κ)
    (hlt : κ < κ') (hs : 0 < s) :
    HH (lamf ρ κ σ) (lamb ρ κ σ) s < HH (lamf ρ κ' σ) (lamb ρ κ' σ) s := by
  have hκ' : 0 < κ' := by linarith
  have hf := lamf_pos (ρ := ρ) hκ hσ
  have hb := lamb_pos (ρ := ρ) hκ hσ
  have hf' := lamf_pos (ρ := ρ) hκ' hσ
  have hb' := lamb_pos (ρ := ρ) hκ' hσ
  have hd : ∀ r, HasDerivAt (fun r => HH (lamf ρ κ' σ) (lamb ρ κ' σ) r -
      HH (lamf ρ κ σ) (lamb ρ κ σ) r)
      (hh (lamf ρ κ' σ) (lamb ρ κ' σ) r - hh (lamf ρ κ σ) (lamb ρ κ σ) r) r := fun r =>
    (HH_hasDerivAt hf' hb' r).sub (HH_hasDerivAt hf hb r)
  have hmono : StrictMonoOn (fun r => HH (lamf ρ κ' σ) (lamb ρ κ' σ) r -
      HH (lamf ρ κ σ) (lamb ρ κ σ) r) (Set.Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun r _ => (hd r).continuousAt.continuousWithinAt) fun r hr => ?_
    rw [interior_Ici] at hr
    rw [(hd r).deriv]
    linarith [hh_strictMono_kappa hρ hσ hκ hlt hr (ρ := ρ)]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hs.le) hs
  simp only [HH_zero, sub_zero] at this
  linarith

/-- Cochrane (2023), §20.2.3, p. 477 ("deflation and (not shown) output gaps become larger as
price stickiness is reduced"): **at every date `t ∈ [0, T)` of the trap, the output gap of the
`π_T = 0` equilibrium is strictly decreasing in `κ`** (`ρ ≥ 0`, `σ > 0`, `u < 0`). From `T` on it
is `0` for every `κ` (`nk_after`), so strictness holds exactly on the trap. -/
theorem nk_x_strictAnti_kappa {σ ρ T u t κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (htT : t < T) (hκ : 0 < κ) (hlt : κ < κ') :
    wX σ κ' ρ T u 0 0 t < wX σ κ ρ T u 0 0 t := by
  rw [nk_x_eq_HH hσ (by linarith) htT.le, nk_x_eq_HH hσ hκ htT.le]
  have h := HH_strictMono_kappa hρ hσ hκ hlt (sub_pos.2 htT) (ρ := ρ)
  have hσu : σ * u < 0 := mul_neg_of_pos_of_neg hσ hu
  nlinarith

/-- Cochrane (2023), §20.2.3, p. 477: in particular the time-0 output gap of the `π_T = 0`
equilibrium is strictly decreasing in `κ` (`T > 0`). -/
theorem x0NK_strictAnti_kappa {σ ρ T u κ κ' : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) (hu : u < 0)
    (hT : 0 < T) (hκ : 0 < κ) (hlt : κ < κ') :
    wX σ κ' ρ T u 0 0 0 < wX σ κ ρ T u 0 0 0 :=
  nk_x_strictAnti_kappa hσ hρ hu hT hκ hlt

end Cochrane.ZeroBound.ZLBSelection
