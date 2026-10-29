/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.LowerBound
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The linearisation of (16.25) as a Fréchet derivative

Cochrane (2023), Chapter 16, §16.8, pp. 377–378: the nonlinear Fisher equation (16.25)
`1/(1 + i_t) = (1 + r)⁻¹E_t(1/Π_{t+1})` linearises to (16.1) `i_t = r + E_tπ_{t+1}`.

`LowerBound.gateaux_log_bondPricing` proves the Gateaux derivative along every bounded direction.
Here the topology is the sup norm on bounded processes: the space `ℓ^∞(ℕ × Ω)` of bounded
processes `x_t(ω)` (Mathlib's `lp` with exponent `∞`). For an arbitrary expectation system, the
map that sends a bounded log-inflation process `x` (`x_{t+1} = log Π_{t+1}`) to the log interest
rate process `log(1 + i_t) = log(1 + r) − log E_t[e^{−x_{t+1}}]` (`fisherMap`) is Fréchet
differentiable at **every** bounded process `x⁰`, with derivative the weighted expectation
`h ↦ E_t[w_{t+1}h_{t+1}]/E_t[w_{t+1}]`, `w = e^{−x⁰}` (`weightedE`, `hasFDerivAt_fisherMap`).
At a steady state `x⁰ ≡ π*` the weights are constant and the derivative is `h ↦ E_th_{t+1}`
(`weightedE_const`, `hasFDerivAt_fisherMap_steady`): the linearised Fisher equation (16.1) is a
genuine Fréchet derivative, uniformly over dates and states.

## Main results

* `E_abs_le_of_weight`, `E_exp_neg_ge`: bounds for `E_t` from monotonicity and linearity.
* `fisherMap` (`ℓ^∞ → ℓ^∞`), `weightedE` (a continuous linear map of norm at most one).
* `fisher_remainder`: `|F(x⁰ + h) − F(x⁰) − Dh| ≤ 9‖h‖²` for `‖h‖ ≤ 1/4`.
* `hasFDerivAt_fisherMap`, `hasFDerivAt_fisherMap_steady`, `fisherMap_steady` (the steady state
  value `log(1 + r) + π*`).
-/

namespace Cochrane.NewKeynesianSelection.TidyR6FrechetBondPricing

open Filter Topology
open scoped ENNReal

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), (16.25), pp. 377–378: bounded processes indexed by `(t, ω)`, with the sup
norm. -/
abbrev BProc (Ω : Type*) := lp (fun _ : ℕ × Ω => ℝ) ∞

/-- Cochrane (2023), (16.25), p. 377: `E_t` is bounded by a weight: if `|g| ≤ Mw`
pointwise, then `|E_t g| ≤ M E_t w`. -/
theorem E_abs_le_of_weight {g w : Ω → ℝ} {M : ℝ}
    (hg : ∀ ω, |g ω| ≤ M * w ω) (t : ℕ) (ω : Ω) : |𝔼.E t g ω| ≤ M * 𝔼.E t w ω := by
  have h1 : g ≤ M • w := fun ω' => by
    simp only [Pi.smul_apply, smul_eq_mul]; exact (le_abs_self _).trans (hg ω')
  have h2 : -(M • w) ≤ g := fun ω' => by
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    linarith [neg_abs_le (g ω'), hg ω']
  have e1 := 𝔼.mono t h1 ω
  have e2 := 𝔼.mono t h2 ω
  rw [map_smul] at e1
  rw [map_neg, map_smul] at e2
  simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at e1 e2
  exact abs_le.mpr ⟨by linarith, e1⟩

/-- Cochrane (2023), (16.25), p. 377: `E_t[e^{−x}] ≥ e^{−M}` when `|x| ≤ M`. -/
theorem E_exp_neg_ge {x : Ω → ℝ} {M : ℝ} (hx : ∀ ω, |x ω| ≤ M) (t : ℕ) (ω : Ω) :
    Real.exp (-M) ≤ 𝔼.E t (fun ω' => Real.exp (-x ω')) ω := by
  have h : (fun _ : Ω => Real.exp (-M)) ≤ fun ω' => Real.exp (-x ω') := fun ω' =>
    Real.exp_le_exp.mpr (by linarith [le_abs_self (x ω'), hx ω'])
  have := 𝔼.mono t h ω
  rwa [𝔼.const] at this

/-- Cochrane (2023), (16.25), p. 377: the pointwise bound `|x(i)| ≤ ‖x‖` in `ℓ^∞`. -/
theorem abs_le_norm (x : BProc Ω) (p : ℕ × Ω) : |x p| ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (E := fun _ : ℕ × Ω => ℝ) ENNReal.top_ne_zero x p
  rwa [Real.norm_eq_abs] at this

/-- Cochrane (2023), (16.25), p. 377: the log interest rate `log(1 + i_t) = log(1 + r) −
log E_t[e^{−x_{t+1}}]` as a function of the log-inflation process `x`, pointwise. -/
noncomputable def fisherFun (r : ℝ) (x : ℕ × Ω → ℝ) (p : ℕ × Ω) : ℝ :=
  Real.log (1 + r) - Real.log (𝔼.E p.1 (fun ω' => Real.exp (-x (p.1 + 1, ω'))) p.2)

/-- Cochrane (2023), (16.25), p. 377: `fisherFun` of a bounded process is bounded,
`|log(1 + i_t)| ≤ |log(1 + r)| + ‖x‖`. -/
theorem fisherFun_bdd (r : ℝ) (x : BProc Ω) (p : ℕ × Ω) :
    |fisherFun 𝔼 r x p| ≤ |Real.log (1 + r)| + ‖x‖ := by
  set M := ‖x‖
  have hx : ∀ ω', |x (p.1 + 1, ω')| ≤ M := fun ω' => abs_le_norm x _
  have hlo := E_exp_neg_ge 𝔼 hx p.1 p.2
  have hhi : 𝔼.E p.1 (fun ω' => Real.exp (-x (p.1 + 1, ω'))) p.2 ≤ Real.exp M := by
    have h : (fun ω' => Real.exp (-x (p.1 + 1, ω'))) ≤ fun _ => Real.exp M := fun ω' =>
      Real.exp_le_exp.mpr (by linarith [neg_abs_le (x (p.1 + 1, ω')), hx ω'])
    have := 𝔼.mono p.1 h p.2
    rwa [𝔼.const] at this
  have hpos : 0 < 𝔼.E p.1 (fun ω' => Real.exp (-x (p.1 + 1, ω'))) p.2 :=
    lt_of_lt_of_le (Real.exp_pos _) hlo
  have h1 := Real.log_le_log (Real.exp_pos _) hlo
  have h2 := Real.log_le_log hpos hhi
  rw [Real.log_exp] at h1 h2
  unfold fisherFun
  have := abs_sub (Real.log (1 + r))
    (Real.log (𝔼.E p.1 (fun ω' => Real.exp (-x (p.1 + 1, ω'))) p.2))
  have h3 : |Real.log (𝔼.E p.1 (fun ω' => Real.exp (-x (p.1 + 1, ω'))) p.2)| ≤ M :=
    abs_le.mpr ⟨h1, h2⟩
  linarith

/-- Cochrane (2023), (16.25), pp. 377–378: the map `x ↦ log(1 + i)` on bounded processes,
`ℓ^∞ → ℓ^∞`. -/
noncomputable def fisherMap (r : ℝ) (x : BProc Ω) : BProc Ω :=
  ⟨fisherFun 𝔼 r x, memℓp_infty_iff.mpr ⟨|Real.log (1 + r)| + ‖x‖, by
    rintro _ ⟨p, rfl⟩
    simpa [Real.norm_eq_abs] using fisherFun_bdd 𝔼 r x p⟩⟩

/-- Cochrane (2023), (16.1), p. 364: the weight `w_{t+1} = e^{−x⁰_{t+1}}`. -/
noncomputable def wt (x0 : BProc Ω) (t : ℕ) (ω : Ω) : ℝ := Real.exp (-x0 (t + 1, ω))

/-- Cochrane (2023), (16.1), p. 364: the weighted conditional expectation
`(Dh)_t = E_t[w_{t+1}h_{t+1}]/E_t[w_{t+1}]`, pointwise. -/
noncomputable def weightedFun (x0 : BProc Ω) (h : ℕ × Ω → ℝ) (p : ℕ × Ω) : ℝ :=
  𝔼.E p.1 (fun ω' => wt x0 p.1 ω' * h (p.1 + 1, ω')) p.2 / 𝔼.E p.1 (wt x0 p.1) p.2

/-- Cochrane (2023), (16.1), p. 364: `E_t[w_{t+1}] ≥ e^{−‖x⁰‖} > 0`. -/
theorem E_wt_pos (x0 : BProc Ω) (t : ℕ) (ω : Ω) : 0 < 𝔼.E t (wt x0 t) ω :=
  lt_of_lt_of_le (Real.exp_pos _) (E_exp_neg_ge 𝔼 (M := ‖x0‖) (x := fun ω' => x0 (t + 1, ω'))
    (fun _ => abs_le_norm x0 _) t ω)

/-- Cochrane (2023), (16.1), p. 364: `|(Dh)_t| ≤ ‖h‖`. -/
theorem weightedFun_bdd (x0 h : BProc Ω) (p : ℕ × Ω) : |weightedFun 𝔼 x0 h p| ≤ ‖h‖ := by
  have hpos := E_wt_pos 𝔼 x0 p.1 p.2
  have hb := E_abs_le_of_weight 𝔼 (g := fun ω' => wt x0 p.1 ω' * h (p.1 + 1, ω'))
    (w := wt x0 p.1) (M := ‖h‖) (fun ω' => by
      rw [abs_mul, abs_of_pos (show 0 < wt x0 p.1 ω' from Real.exp_pos _), mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_le_norm h _) (Real.exp_pos _).le) p.1 p.2
  unfold weightedFun
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  exact hb

/-- Cochrane (2023), (16.1), p. 364: the weighted conditional expectation as a linear map on
bounded processes. -/
noncomputable def weightedLin (x0 : BProc Ω) : BProc Ω →ₗ[ℝ] BProc Ω where
  toFun h := ⟨weightedFun 𝔼 x0 h, memℓp_infty_iff.mpr ⟨‖h‖, by
    rintro _ ⟨p, rfl⟩
    simpa [Real.norm_eq_abs] using weightedFun_bdd 𝔼 x0 h p⟩⟩
  map_add' h k := by
    apply lp.ext
    funext p
    simp only [lp.coeFn_add, Pi.add_apply]
    change weightedFun 𝔼 x0 (⇑(h + k)) p = weightedFun 𝔼 x0 h p + weightedFun 𝔼 x0 k p
    unfold weightedFun
    have e : (fun ω' => wt x0 p.1 ω' * (⇑(h + k)) (p.1 + 1, ω')) =
        (fun ω' => wt x0 p.1 ω' * h (p.1 + 1, ω')) +
          fun ω' => wt x0 p.1 ω' * k (p.1 + 1, ω') := by
      funext ω'
      simp only [lp.coeFn_add, Pi.add_apply]
      ring
    rw [e, map_add, Pi.add_apply, add_div]
  map_smul' c h := by
    apply lp.ext
    funext p
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    change weightedFun 𝔼 x0 (⇑(c • h)) p = c * weightedFun 𝔼 x0 h p
    unfold weightedFun
    have e : (fun ω' => wt x0 p.1 ω' * (⇑(c • h)) (p.1 + 1, ω')) =
        c • fun ω' => wt x0 p.1 ω' * h (p.1 + 1, ω') := by
      funext ω'
      simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

/-- Cochrane (2023), (16.1), p. 364: the weighted conditional expectation as a continuous linear
map of norm at most one. -/
noncomputable def weightedE (x0 : BProc Ω) : BProc Ω →L[ℝ] BProc Ω :=
  (weightedLin 𝔼 x0).mkContinuous 1 fun h => by
    rw [one_mul]
    refine lp.norm_le_of_forall_le (norm_nonneg h) fun p => ?_
    rw [Real.norm_eq_abs]
    exact weightedFun_bdd 𝔼 x0 h p

/-- Cochrane (2023), (16.1), p. 364: `weightedE` evaluates to the pointwise weighted
expectation. -/
theorem weightedE_apply (x0 h : BProc Ω) (p : ℕ × Ω) :
    weightedE 𝔼 x0 h p = weightedFun 𝔼 x0 h p := rfl

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, the second-order bound: for bounded `x⁰`
and `‖h‖ ≤ 1/4`, `|F(x⁰ + h)_t − F(x⁰)_t − (Dh)_t| ≤ 9‖h‖²` at every date and state. -/
theorem fisher_remainder (r : ℝ) (x0 h : BProc Ω) (hh : ‖h‖ ≤ 1 / 4) (p : ℕ × Ω) :
    |fisherFun 𝔼 r (⇑(x0 + h)) p - fisherFun 𝔼 r x0 p - weightedFun 𝔼 x0 h p| ≤ 9 * ‖h‖ ^ 2 := by
  obtain ⟨t, ω⟩ := p
  set H := ‖h‖ with hH
  have hH0 : 0 ≤ H := norm_nonneg h
  set w := wt x0 t with hwdef
  have hw : ∀ ω', 0 < w ω' := fun ω' => Real.exp_pos _
  set Ew := 𝔼.E t w ω with hEw
  have hEw0 : 0 < Ew := E_wt_pos 𝔼 x0 t ω
  set hn : Ω → ℝ := fun ω' => h (t + 1, ω') with hhn
  have hhb : ∀ ω', |hn ω'| ≤ H := fun ω' => abs_le_norm h _
  -- `w e^{−h} = w − w h + R` with `|R| ≤ H² w`
  set R : Ω → ℝ := fun ω' => w ω' * (Real.exp (-hn ω') - 1 + hn ω') with hR
  have hRb : ∀ ω', |R ω'| ≤ H ^ 2 * w ω' := by
    intro ω'
    have hz : |-hn ω'| ≤ 1 := by rw [abs_neg]; linarith [hhb ω']
    have e := Real.abs_exp_sub_one_sub_id_le hz
    have : Real.exp (-hn ω') - 1 + hn ω' = Real.exp (-hn ω') - 1 - -hn ω' := by ring
    rw [hR]
    simp only
    rw [abs_mul, abs_of_pos (hw ω'), this, mul_comm]
    refine mul_le_mul_of_nonneg_right (e.trans ?_) (hw ω').le
    rw [neg_sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hhb ω') 2
  have hsplit : (fun ω' => Real.exp (-(⇑(x0 + h)) (t + 1, ω'))) =
      w - (fun ω' => w ω' * hn ω') + R := by
    funext ω'
    simp only [lp.coeFn_add, Pi.add_apply, Pi.sub_apply, hR, hwdef, wt, hhn, neg_add,
      Real.exp_add]
    ring
  set Eh := 𝔼.E t (fun ω' => w ω' * hn ω') ω with hEh
  set ER := 𝔼.E t R ω with hER
  have hEhb : |Eh| ≤ H * Ew := E_abs_le_of_weight 𝔼
    (fun ω' => by rw [abs_mul, abs_of_pos (hw ω'), mul_comm]
                  exact mul_le_mul_of_nonneg_right (hhb ω') (hw ω').le) t ω
  have hERb : |ER| ≤ H ^ 2 * Ew := E_abs_le_of_weight 𝔼 hRb t ω
  have hEnew : 𝔼.E t (fun ω' => Real.exp (-(⇑(x0 + h)) (t + 1, ω'))) ω = Ew - Eh + ER := by
    rw [hsplit, map_add, map_sub]
    rfl
  -- the relative change `z`
  set z := (-Eh + ER) / Ew with hz
  have hzb : |z| ≤ H + H ^ 2 := by
    rw [hz, abs_div, abs_of_pos hEw0, div_le_iff₀ hEw0]
    calc |-Eh + ER| ≤ |Eh| + |ER| := by
          have := abs_add_le (-Eh) ER; rwa [abs_neg] at this
      _ ≤ H * Ew + H ^ 2 * Ew := add_le_add hEhb hERb
      _ = (H + H ^ 2) * Ew := by ring
  have hz2 : |z| ≤ 1 / 2 := by nlinarith
  have hnew : Ew - Eh + ER = Ew * (1 + z) := by rw [hz]; field_simp; ring
  have h1z : 0 < 1 + z := by linarith [neg_abs_le z]
  have hlog : |Real.log (1 + z) - z| ≤ 2 * z ^ 2 := by
    have hz1 : |-z| < 1 := by rw [abs_neg]; linarith
    have e := Real.abs_log_sub_add_sum_range_le hz1 1
    simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one, sub_neg_eq_add,
      abs_neg] at e
    have hd : |z| ^ 2 / (1 - |z|) ≤ 2 * z ^ 2 := by
      rw [div_le_iff₀ (by linarith), sq_abs]
      nlinarith [sq_nonneg z]
    have : |Real.log (1 + z) - z| = |-z + Real.log (1 + z)| := by
      rw [show Real.log (1 + z) - z = -z + Real.log (1 + z) by ring]
    rw [this]
    exact e.trans hd
  -- assemble
  have hF : fisherFun 𝔼 r (⇑(x0 + h)) (t, ω) - fisherFun 𝔼 r x0 (t, ω) = -Real.log (1 + z) := by
    unfold fisherFun
    simp only
    rw [hEnew, hnew, Real.log_mul hEw0.ne' h1z.ne']
    change _ - _ - (Real.log (1 + r) - Real.log (𝔼.E t w ω)) = _
    ring
  have hD : weightedFun 𝔼 x0 h (t, ω) = Eh / Ew := rfl
  rw [hF, hD]
  have hDz : Eh / Ew = -z + ER / Ew := by rw [hz]; field_simp; ring
  rw [hDz]
  have hERw : |ER / Ew| ≤ H ^ 2 := by
    rw [abs_div, abs_of_pos hEw0, div_le_iff₀ hEw0]; exact hERb
  have hz2' : z ^ 2 ≤ (H + H ^ 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hzb 2
  calc |-Real.log (1 + z) - (-z + ER / Ew)| = |-(Real.log (1 + z) - z) - ER / Ew| := by ring_nf
    _ ≤ |Real.log (1 + z) - z| + |ER / Ew| := by
        have := abs_sub (-(Real.log (1 + z) - z)) (ER / Ew)
        rwa [abs_neg] at this
    _ ≤ 2 * (H + H ^ 2) ^ 2 + H ^ 2 := by nlinarith
    _ ≤ 9 * H ^ 2 := by
        have : (H + H ^ 2) ^ 2 ≤ 4 * H ^ 2 := by
          have h2 : H + H ^ 2 ≤ 2 * H := by nlinarith
          have h3 : 0 ≤ H + H ^ 2 := by positivity
          nlinarith
        linarith

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378, **the Fréchet derivative**: for an arbitrary
expectation system and every bounded log-inflation process `x⁰`, the map `fisherMap` from bounded
processes to bounded processes (sup norm) is Fréchet differentiable at `x⁰`, with derivative the
weighted conditional expectation `h ↦ E_t[e^{−x⁰_{t+1}}h_{t+1}]/E_t[e^{−x⁰_{t+1}}]`. -/
theorem hasFDerivAt_fisherMap (r : ℝ) (x0 : BProc Ω) :
    HasFDerivAt (fisherMap 𝔼 r) (weightedE 𝔼 x0) x0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  have hball : ∀ᶠ h in 𝓝 (0 : BProc Ω), ‖h‖ < min (1 / 4) (c / 9) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : BProc Ω)
      (show (0 : ℝ) < min (1 / 4) (c / 9) from lt_min (by norm_num) (by positivity)))
      fun h hh => by rwa [Metric.mem_ball, dist_zero_right] at hh
  filter_upwards [hball] with h hh
  have h1 : ‖h‖ ≤ 1 / 4 := (lt_min_iff.mp hh).1.le
  have h2 : ‖h‖ ≤ c / 9 := (lt_min_iff.mp hh).2.le
  refine lp.norm_le_of_forall_le (by positivity) fun p => ?_
  rw [Real.norm_eq_abs]
  have := fisher_remainder 𝔼 r x0 h h1 p
  change |fisherFun 𝔼 r (⇑(x0 + h)) p - fisherFun 𝔼 r x0 p - weightedFun 𝔼 x0 h p| ≤ _
  calc _ ≤ 9 * ‖h‖ ^ 2 := this
    _ = (9 * ‖h‖) * ‖h‖ := by ring
    _ ≤ c * ‖h‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg h)

/-- Cochrane (2023), (16.1), p. 364: the constant process `π*`. -/
noncomputable def constProc (pis : ℝ) : BProc Ω :=
  ⟨fun _ => pis, memℓp_infty_iff.mpr ⟨|pis|, by rintro _ ⟨p, rfl⟩; simp⟩⟩

/-- Cochrane (2023), (16.1), p. 364: at a steady state the weights are constant, so the
derivative is the plain conditional expectation `(Dh)_t = E_th_{t+1}`. -/
theorem weightedE_const (pis : ℝ) (h : BProc Ω) (p : ℕ × Ω) :
    weightedE 𝔼 (constProc pis) h p = 𝔼.E p.1 (fun ω' => h (p.1 + 1, ω')) p.2 := by
  rw [weightedE_apply]
  unfold weightedFun wt constProc
  have e1 : (fun ω' => Real.exp (-pis) * h (p.1 + 1, ω')) =
      Real.exp (-pis) • fun ω' => h (p.1 + 1, ω') := rfl
  have e2 : (fun _ : Ω => Real.exp (-pis)) = fun _ => Real.exp (-pis) := rfl
  change 𝔼.E p.1 (fun ω' => Real.exp (-pis) * h (p.1 + 1, ω')) p.2 /
    𝔼.E p.1 (fun _ => Real.exp (-pis)) p.2 = _
  rw [e1, map_smul, 𝔼.const]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- Cochrane (2023), (16.25), p. 377: at the steady state `π*` the log interest rate is
`log(1 + r) + π*` (the exact Fisher relation `1 + i = (1 + r)Π*`). -/
theorem fisherMap_steady (r pis : ℝ) (p : ℕ × Ω) :
    fisherMap 𝔼 r (constProc pis) p = Real.log (1 + r) + pis := by
  change fisherFun 𝔼 r (fun _ => pis) p = _
  unfold fisherFun
  rw [𝔼.const, Real.log_exp]
  ring

/-- Cochrane (2023), (16.25) ⇒ (16.1), pp. 377–378: at a steady state `π*` the linearisation of
(16.25) is the Fréchet derivative `h ↦ (E_th_{t+1})_t` on bounded processes: the linearised
Fisher equation `i_t = r + E_tπ_{t+1}` (16.1), uniformly over dates and states. -/
theorem hasFDerivAt_fisherMap_steady (r pis : ℝ) :
    HasFDerivAt (fisherMap 𝔼 r) (weightedE 𝔼 (constProc pis)) (constProc pis) ∧
      ∀ h p, weightedE 𝔼 (constProc pis) h p = 𝔼.E p.1 (fun ω' => h (p.1 + 1, ω')) p.2 :=
  ⟨hasFDerivAt_fisherMap 𝔼 r _, weightedE_const 𝔼 pis⟩

end Cochrane.NewKeynesianSelection.TidyR6FrechetBondPricing
