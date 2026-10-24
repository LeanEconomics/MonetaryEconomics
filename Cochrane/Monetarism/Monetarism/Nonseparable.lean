/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.ObstfeldRogoff
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Nonseparable utility and more indeterminacy

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix, Chapter 3, §3.2.4
"Nonseparable utility and more indeterminacy", eqs. (3.7)–(3.8) and pp. 629–632 (with the remark
on p. 445 of §19.3). Perfect foresight.

## Main results

* (3.7)–(3.8): `foc38_iff`; the "usual approximation, precise in continuous time": the exact
  derivative of the log discount factor `log(βu_c(ce^a, me^b)/u_c(c, m))` at `(0, 0)` is
  `−γa − ηb` with `γ = −cu_cc/u_c`, `η = −mu_cm/u_c` (`sdf_log_hasFDerivAt`), so
  `log(1 + r^f)` has derivative `γa + ηb` and value `log(1+δ)` (`rf_log_hasFDerivAt`). With
  log money growth the coefficient is `−mu_cm/u_c`; the printed `η = −u_cm/u_c` is the
  coefficient of a level change `Δm` (`sdf_level_hasDerivAt`). The continuous-time footnote:
  `ct_footnote`.
* Obstfeld (1984), `u = −c^{−a}m^{−b}`: exact partials `obs_uc`, `obs_um` (the printed
  `u_c = ac^{−a−1}m^{b}`, `u_m = bc^{a}m^{−b−1}` have sign typos: `obs_printed_typo`),
  `obs_mrs`, the first-order condition `obs_foc`, the equilibrium map `obs_map_iff`, the steady
  state `obs_steady_iff`, its relative form `obs_relative`.
* Linearisation, survey error **E19**: the exact derivative of `m_{t+1}/m_t` at `m̄` is
  `i/((1−b)m̄) = (b/a)(1+i)/((1−b)m̄²)` (`obs_ratio_hasDerivAt`), missing the factor
  `(1+δ)(1+µ) = 1+i` in print (`e19_printed_coefficient`); the map `m ↦ m_{t+1}` has slope
  `1 − i/(b−1)` (`obs_map_hasDerivAt`). The phase diagram cuts from above iff `b > 1`
  (`obs_cuts_from_above_iff`), but local stability holds iff `b > 1 + i/2`
  (`obs_stable_iff`); counterexample `b = 1.04`, `i = 0.1025` (`e19_counterexample`).
  General local dynamics: `local_contraction`, `local_repulsion` (corollaries of the orbit
  lemmas of `MoneyTargetingDynamics`); consequences:
  `obs_multiple_stable` (a continuum of convergent equilibria satisfying the TVC) and
  `obs_locally_unique` (`1 < b < 1 + i/2`: only the steady state stays nearby).
* CES money in utility (p. 632): `ces_uc`, `ces_um`, `ces_uc_form`, `ces_sdf`,
  `ces_sdf_const`, `ces_mrs`, `ces_money_demand_iff`, `ces_income_elasticity`,
  `ces_interest_elasticity`.
-/

namespace Cochrane.Monetarism.Nonseparable

open Filter Topology

/-! ## (3.7)–(3.8) and the discount factor -/

/-- Cochrane (2023), eq. (3.8), p. 630: `u_m/u_c = i/(1+i) = 1 − Q` with `Q = 1/(1+i)`. -/
theorem foc38_iff {i : ℝ} (hi : 1 + i ≠ 0) : i / (1 + i) = 1 - 1 / (1 + i) := by
  field_simp; ring

/-- Cochrane (2023), p. 630, "The usual approximation, precise in continuous time": with
`u_c` differentiable at `(c, m)` (derivative `L`, so `u_cc = L(1,0)`, `u_cm = L(0,1)`) and
positive there, the log discount factor `log(βu_c(ce^a, me^b)/u_c(c, m))` as a function of log
consumption growth `a` and log money growth `b` has exact derivative `−γa − ηb` at `(0, 0)`,
`γ = −cu_cc/u_c`, `η = −mu_cm/u_c`, and value `log β`. -/
theorem sdf_log_hasFDerivAt {β c m : ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} (hβ : 0 < β)
    (hpos : 0 < Uc (c, m)) (hU : HasFDerivAt Uc L (c, m)) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ =>
        Real.log (β * Uc (c * Real.exp p.1, m * Real.exp p.2) / Uc (c, m))) D (0, 0) ∧
      (∀ a b, D (a, b) = -(-(c * L (1, 0)) / Uc (c, m) * a) - -(m * L (0, 1)) / Uc (c, m) * b) ∧
      Real.log (β * Uc (c * Real.exp (0 : ℝ × ℝ).1, m * Real.exp (0 : ℝ × ℝ).2) / Uc (c, m)) =
        Real.log β := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => c * Real.exp p.1)
      (c • (Real.exp (0 : ℝ × ℝ).1 • ContinuousLinearMap.fst ℝ ℝ ℝ)) (0 : ℝ × ℝ) :=
    (hasFDerivAt_fst.exp).const_mul c
  have h2 : HasFDerivAt (fun p : ℝ × ℝ => m * Real.exp p.2)
      (m • (Real.exp (0 : ℝ × ℝ).2 • ContinuousLinearMap.snd ℝ ℝ ℝ)) (0 : ℝ × ℝ) :=
    (hasFDerivAt_snd.exp).const_mul m
  have hg := h1.prodMk h2
  have hU' : HasFDerivAt Uc L (c * Real.exp (0 : ℝ × ℝ).1, m * Real.exp (0 : ℝ × ℝ).2) := by
    simpa using hU
  have hcomp := hU'.comp (0 : ℝ × ℝ) hg
  have hf := hcomp.const_mul (β / Uc (c, m))
  have hval :
      β / Uc (c, m) * (Uc ∘ fun x : ℝ × ℝ => (c * Real.exp x.1, m * Real.exp x.2)) 0 = β := by
    simp only [Function.comp_apply, Prod.fst_zero, Prod.snd_zero, Real.exp_zero, mul_one]
    field_simp
  have hlog := hf.log (by rw [hval]; exact hβ.ne')
  have hfun : (fun p : ℝ × ℝ =>
      Real.log (β * Uc (c * Real.exp p.1, m * Real.exp p.2) / Uc (c, m))) =
      fun p => Real.log (β / Uc (c, m) *
        (Uc ∘ fun x : ℝ × ℝ => (c * Real.exp x.1, m * Real.exp x.2)) p) := by
    funext p; simp only [Function.comp_apply]; ring_nf
  rw [hfun]
  refine ⟨_, hlog, fun a b => ?_, ?_⟩
  · rw [hval]
    have hL : L (c * a, m * b) = c * a * L (1, 0) + m * b * L (0, 1) := by
      have : ((c * a, m * b) : ℝ × ℝ) =
          (c * a) • ((1 : ℝ), (0 : ℝ)) + (m * b) • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    simp only [Prod.fst_zero, Real.exp_zero, one_smul, Prod.snd_zero,
      smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
      ContinuousLinearMap.coe_snd']
    rw [hL]
    field_simp
    ring
  · simp only [Prod.fst_zero, Prod.snd_zero, Real.exp_zero, mul_one]
    congr 1
    field_simp

/-- Cochrane (2023), p. 630, `r^f ≈ δ + γE_t(Δc_{t+1}) + ηE_t(Δm_{t+1})`, exact form under
perfect foresight: `log(1 + r^f) = −log(βu_c(ce^a, me^b)/u_c(c, m))` has value `log(1+δ)` at
`(0, 0)` when `β = 1/(1+δ)`, and derivative `γa + ηb`. -/
theorem rf_log_hasFDerivAt {β δ c m : ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} (hδ : 0 < 1 + δ)
    (hβ : β = 1 / (1 + δ)) (hpos : 0 < Uc (c, m)) (hU : HasFDerivAt Uc L (c, m)) :
    ∃ D : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ =>
        -Real.log (β * Uc (c * Real.exp p.1, m * Real.exp p.2) / Uc (c, m))) D (0, 0) ∧
      (∀ a b, D (a, b) = -(c * L (1, 0)) / Uc (c, m) * a + -(m * L (0, 1)) / Uc (c, m) * b) ∧
      -Real.log (β * Uc (c * Real.exp (0 : ℝ × ℝ).1, m * Real.exp (0 : ℝ × ℝ).2) / Uc (c, m)) =
        Real.log (1 + δ) := by
  have hβ0 : 0 < β := by rw [hβ]; positivity
  obtain ⟨D, hD, hDab, hval⟩ := sdf_log_hasFDerivAt hβ0 hpos hU
  refine ⟨-D, hD.neg, fun a b => ?_, ?_⟩
  · change -(D (a, b)) = _
    rw [hDab]; ring
  · rw [hval, hβ, one_div, Real.log_inv, neg_neg]

/-- Cochrane (2023), p. 630 (survey note on the printed `η = −u_cm/u_c`): for a level change
`m' = m + b` the log discount factor has derivative `u_cm/u_c = −(−u_cm/u_c)` — the printed `η`
is the coefficient of a level change, while for log money growth (as in the footnote,
`m u_cm/u_c · dm/m`) it is `−m u_cm/u_c` (`sdf_log_hasFDerivAt`). -/
theorem sdf_level_hasDerivAt {β c m : ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ} (hβ : 0 < β)
    (hpos : 0 < Uc (c, m)) (hU : HasFDerivAt Uc L (c, m)) :
    HasDerivAt (fun b => Real.log (β * Uc (c, m + b) / Uc (c, m))) (L (0, 1) / Uc (c, m)) 0 := by
  have hpath : HasDerivAt (fun b : ℝ => (c, m + b)) ((0 : ℝ), (1 : ℝ)) 0 :=
    (hasDerivAt_const 0 c).prodMk ((hasDerivAt_id 0).const_add m)
  have hU' : HasFDerivAt Uc L (c, m + 0) := by simpa using hU
  have hcomp := HasFDerivAt.comp_hasDerivAt (l := Uc) (l' := L) (f := fun b : ℝ => (c, m + b))
    (0 : ℝ) hU' hpath
  have hf := (hcomp.const_mul (β / Uc (c, m))).log (by
    simp only [Function.comp_apply, add_zero]; field_simp; exact hβ.ne')
  have hfun : (fun b => Real.log (β * Uc (c, m + b) / Uc (c, m))) =
      fun b => Real.log (β / Uc (c, m) * (Uc ∘ fun b : ℝ => (c, m + b)) b) := by
    funext b; simp only [Function.comp_apply]; ring_nf
  rw [hfun]
  convert hf using 1
  simp only [Function.comp_apply, add_zero]
  field_simp

/-- Cochrane (2023), p. 630, footnote 1: along differentiable paths `c(t), m(t) > 0`,
`d log(e^{−δt}u_c(c_t, m_t))/dt = −δ + (c u_cc/u_c)(ċ/c) + (m u_cm/u_c)(ṁ/m)`. -/
theorem ct_footnote {δ t c' m' : ℝ} {c m : ℝ → ℝ} {Uc : ℝ × ℝ → ℝ} {L : ℝ × ℝ →L[ℝ] ℝ}
    (hc : HasDerivAt c c' t) (hm : HasDerivAt m m' t) (hcpos : 0 < c t) (hmpos : 0 < m t)
    (hpos : 0 < Uc (c t, m t)) (hU : HasFDerivAt Uc L (c t, m t)) :
    HasDerivAt (fun s => Real.log (Real.exp (-δ * s) * Uc (c s, m s)))
      (-δ + c t * L (1, 0) / Uc (c t, m t) * (c' / c t) +
        m t * L (0, 1) / Uc (c t, m t) * (m' / m t)) t := by
  have hpath : HasDerivAt (fun s => (c s, m s)) (c', m') t := hc.prodMk hm
  have hcomp := HasFDerivAt.comp_hasDerivAt (l := Uc) (l' := L) (f := fun s => (c s, m s)) t
    hU hpath
  have he : HasDerivAt (fun s => Real.exp (-δ * s)) (Real.exp (-δ * t) * (-δ * 1)) t :=
    ((hasDerivAt_id t).const_mul (-δ)).exp
  have hprod := he.mul hcomp
  have hne : Real.exp (-δ * t) * (Uc ∘ fun s => (c s, m s)) t ≠ 0 := by
    change Real.exp (-δ * t) * Uc (c t, m t) ≠ 0
    positivity
  have hlog := hprod.log hne
  have hL : L (c', m') = c' * L (1, 0) + m' * L (0, 1) := by
    have : ((c', m') : ℝ × ℝ) = c' • ((1 : ℝ), (0 : ℝ)) + m' • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  convert hlog using 1
  · rfl
  · change _ = (Real.exp (-δ * t) * (-δ * 1) * Uc (c t, m t) + Real.exp (-δ * t) * L (c', m')) /
      (Real.exp (-δ * t) * Uc (c t, m t))
    rw [hL]
    field_simp
    ring

/-! ## Obstfeld (1984): `u(c, m) = −c^{−a}m^{−b}` -/

/-- Cochrane (2023), p. 631: `u_c = a c^{−a−1}m^{−b}` for `u(c, m) = −c^{−a}m^{−b}`, `c > 0`. -/
theorem obs_uc {a b c m : ℝ} (hc : 0 < c) :
    HasDerivAt (fun c => -(c ^ (-a) * m ^ (-b))) (a * c ^ (-a - 1) * m ^ (-b)) c := by
  have h := ((Real.hasDerivAt_rpow_const (p := -a) (Or.inl hc.ne')).mul_const (m ^ (-b))).neg
  convert h using 1
  ring

/-- Cochrane (2023), p. 631: `u_m = b c^{−a}m^{−b−1}`, `m > 0`. -/
theorem obs_um {a b c m : ℝ} (hm : 0 < m) :
    HasDerivAt (fun m => -(c ^ (-a) * m ^ (-b))) (b * c ^ (-a) * m ^ (-b - 1)) m := by
  have h := ((Real.hasDerivAt_rpow_const (p := -b) (Or.inl hm.ne')).const_mul (c ^ (-a))).neg
  convert h using 1
  ring

/-- Cochrane (2023), p. 631 (typo): the printed partials `u_c = ac^{−a−1}m^{b}` and
`u_m = bc^{a}m^{−b−1}` disagree with the exact ones: at `a = b = 1`, `c = m = 2` the printed
`u_c` is `1/2` against `1/8`, and the printed `u_m` is `1/2` against `1/8`. -/
theorem obs_printed_typo :
    (1 : ℝ) * (2 : ℝ) ^ (-(1 : ℝ) - 1) * (2 : ℝ) ^ (1 : ℝ) ≠
        1 * (2 : ℝ) ^ (-(1 : ℝ) - 1) * (2 : ℝ) ^ (-(1 : ℝ)) ∧
      (1 : ℝ) * (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 : ℝ) - 1) ≠
        1 * (2 : ℝ) ^ (-(1 : ℝ)) * (2 : ℝ) ^ (-(1 : ℝ) - 1) := by
  have h1 : (2 : ℝ) ^ (-(1 : ℝ) - 1) = 1 / 4 := by
    rw [show -(1 : ℝ) - 1 = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num
  have h2 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  rw [h1, h2, Real.rpow_one]
  norm_num

/-- Cochrane (2023), p. 631: the marginal rate of substitution `u_m/u_c = (b/a)(c/m)`. -/
theorem obs_mrs {a b c m : ℝ} (ha : 0 < a) (hc : 0 < c) (hm : 0 < m) :
    b * c ^ (-a) * m ^ (-b - 1) / (a * c ^ (-a - 1) * m ^ (-b)) = b / a * (c / m) := by
  rw [Real.rpow_sub_one hc.ne', Real.rpow_sub_one hm.ne']
  have : 0 < c ^ (-a) := Real.rpow_pos_of_pos hc _
  have : 0 < m ^ (-b) := Real.rpow_pos_of_pos hm _
  field_simp

/-- Cochrane (2023), p. 631: the ratio of marginal utilities of consumption across dates,
`u_c(c', m')/u_c(c, m) = (c'/c)^{−a−1}(m'/m)^{−b}`. -/
theorem obs_uc_ratio {a b c m c' m' : ℝ} (ha : 0 < a) (hc : 0 < c) (hm : 0 < m) (hc' : 0 < c')
    (hm' : 0 < m') :
    a * c' ^ (-a - 1) * m' ^ (-b) / (a * c ^ (-a - 1) * m ^ (-b)) =
      (c' / c) ^ (-a - 1) * (m' / m) ^ (-b) := by
  rw [Real.div_rpow hc'.le hc.le, Real.div_rpow hm'.le hm.le]
  have : 0 < c ^ (-a - 1) := Real.rpow_pos_of_pos hc _
  have : 0 < m ^ (-b) := Real.rpow_pos_of_pos hm _
  field_simp

/-- Cochrane (2023), p. 631, "the first-order conditions give
`c_tb/(m_ta) = 1 − β(c_{t+1}/c_t)^{−a−1}(m_{t+1}/m_t)^{−b}P_t/P_{t+1}`": (3.8) with (3.7) under
perfect foresight, `u_m/u_c = 1 − βu_c(t+1)/u_c(t)·P_t/P_{t+1}`, for this utility. -/
theorem obs_foc {a b c m c' m' β Pr : ℝ} (ha : 0 < a) (hc : 0 < c) (hm : 0 < m) (hc' : 0 < c')
    (hm' : 0 < m') :
    b * c ^ (-a) * m ^ (-b - 1) / (a * c ^ (-a - 1) * m ^ (-b)) =
        1 - β * (a * c' ^ (-a - 1) * m' ^ (-b) / (a * c ^ (-a - 1) * m ^ (-b))) * Pr ↔
      c * b / (m * a) = 1 - β * (c' / c) ^ (-a - 1) * (m' / m) ^ (-b) * Pr := by
  rw [obs_mrs ha hc hm, obs_uc_ratio ha hc hm hc' hm',
    show b / a * (c / m) = c * b / (m * a) by field_simp,
    show β * ((c' / c) ^ (-a - 1) * (m' / m) ^ (-b)) * Pr =
      β * (c' / c) ^ (-a - 1) * (m' / m) ^ (-b) * Pr by ring]

/-- Cochrane (2023), p. 631: with `y = c = 1` and money growth `µ`
(`P_t/P_{t+1} = (m_{t+1}/m_t)/(1+µ)`), the first-order condition reads
`(b/a)(1/m_t) = 1 − (β/(1+µ))(m_{t+1}/m_t)^{1−b}`, and for `b ≠ 1` this is equivalent to
`m_{t+1}/m_t = [(1+µ)/β · (1 − b/(am_t))]^{1/(1−b)}`. -/
theorem obs_map_iff {a b β μ m m' : ℝ} (ha : 0 < a) (hb : b ≠ 1) (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hm : 0 < m) (hm' : 0 < m') (hmb : b / a < m) :
    (b / (m * a) = 1 - β * (m' / m) ^ (-b) * ((m' / m) / (1 + μ)) ↔
      b / a * (1 / m) = 1 - β / (1 + μ) * (m' / m) ^ (1 - b)) ∧
    (b / a * (1 / m) = 1 - β / (1 + μ) * (m' / m) ^ (1 - b) ↔
      m' / m = ((1 + μ) / β * (1 - b / a * (1 / m))) ^ (1 / (1 - b))) := by
  have hr : 0 < m' / m := div_pos hm' hm
  have h1b : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hpow : (m' / m) ^ (-b) * (m' / m) = (m' / m) ^ (1 - b) := by
    rw [show 1 - b = -b + 1 by ring, Real.rpow_add hr, Real.rpow_one]
  constructor
  · rw [← hpow]
    constructor <;> intro h
    · field_simp at h ⊢; linarith
    · field_simp at h ⊢; linarith
  · constructor
    · intro h
      have h2 : (m' / m) ^ (1 - b) = (1 + μ) / β * (1 - b / a * (1 / m)) := by
        field_simp at h ⊢; linarith
      rw [← h2, show 1 / (1 - b) = (1 - b)⁻¹ by ring, Real.rpow_rpow_inv hr.le h1b]
    · intro h
      have hbase : 0 < (1 + μ) / β * (1 - b / a * (1 / m)) := by
        have : b / a * (1 / m) < 1 := by
          rw [mul_one_div, div_lt_one hm]; exact hmb
        have := div_pos hμ hβ
        nlinarith
      have h2 : (m' / m) ^ (1 - b) = (1 + μ) / β * (1 - b / a * (1 / m)) := by
        rw [h, show 1 / (1 - b) = (1 - b)⁻¹ by ring, Real.rpow_inv_rpow hbase.le h1b]
      rw [h2]
      field_simp
      ring

/-- Cochrane (2023), p. 631: the gross growth of real balances
`[(1+δ)(1+µ)(1 − b/(am))]^{1/(1−b)}`, with `A = (1+δ)(1+µ) = 1 + i`. -/
noncomputable def obsRatio (a b A m : ℝ) : ℝ := (A * (1 - b / a * (1 / m))) ^ (1 / (1 - b))

/-- Cochrane (2023), p. 631: the equilibrium map `m_t ↦ m_{t+1} = m_t·obsRatio(m_t)`. -/
noncomputable def obsMap (a b A m : ℝ) : ℝ := m * obsRatio a b A m

/-- Cochrane (2023), p. 631, "The steady state is `1 = (1+δ)(1+µ)(1 − (b/a)(1/m̄))`": for
`A > 1`, this holds iff `m̄ = (b/a)·A/(A − 1)`, and then `m̄` is a fixed point of the map. -/
theorem obs_steady_iff {a b A ms : ℝ} (ha : 0 < a) (hA : 1 < A) (hms : 0 < ms) :
    (A * (1 - b / a * (1 / ms)) = 1 ↔ ms = b / a * A / (A - 1)) ∧
      (A * (1 - b / a * (1 / ms)) = 1 → obsMap a b A ms = ms) := by
  have hA1 : A - 1 ≠ 0 := by linarith
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · field_simp at h ⊢; linarith
  · rw [h]
    have hb : b ≠ 0 := by
      intro hb; rw [hb] at h; simp at h; linarith
    field_simp
    ring
  · unfold obsMap obsRatio; rw [h, Real.one_rpow, mul_one]

/-- Cochrane (2023), p. 631, "In terms of the steady state": if `A(1 − b/(am̄)) = 1` then
`A(1 − b/(am)) = (1 − b/(am))/(1 − b/(am̄))`. -/
theorem obs_relative {a b A ms m : ℝ} (hss : A * (1 - b / a * (1 / ms)) = 1) :
    A * (1 - b / a * (1 / m)) = (1 - b / a * (1 / m)) / (1 - b / a * (1 / ms)) := by
  have h : 1 - b / a * (1 / ms) ≠ 0 := by intro h0; rw [h0, mul_zero] at hss; norm_num at hss
  have hA : A = 1 / (1 - b / a * (1 / ms)) := by rw [eq_div_iff h]; exact hss
  rw [hA]; field_simp

/-- Cochrane (2023), p. 631, linearisation (survey **E19**, corrected): with
`A(1 − b/(am̄)) = 1`, `b ≠ 1`, the exact derivative of `m_{t+1}/m_t` at `m̄` is
`(b/a)·A/((1−b)m̄²) = (A − 1)/((1−b)m̄) = i/((1−b)m̄)`. -/
theorem obs_ratio_hasDerivAt {a b A ms : ℝ} (ha : 0 < a) (hb : b ≠ 1) (hms : 0 < ms)
    (hss : A * (1 - b / a * (1 / ms)) = 1) :
    HasDerivAt (obsRatio a b A) ((A - 1) / ((1 - b) * ms)) ms ∧
      (A - 1) / ((1 - b) * ms) = b / a * A / ((1 - b) * ms ^ 2) := by
  have h1b : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hinv : HasDerivAt (fun m : ℝ => 1 / m) (-(1 / ms ^ 2)) ms := by
    have := hasDerivAt_inv hms.ne'
    simpa [one_div] using this
  have hbase : HasDerivAt (fun m => A * (1 - b / a * (1 / m))) (A * -(b / a * -(1 / ms ^ 2)))
      ms := ((hinv.const_mul (b / a)).const_sub 1).const_mul A
  have hpow := hbase.rpow_const (p := 1 / (1 - b)) (Or.inl (by rw [hss]; norm_num))
  have hkey : A * (b / a) = (A - 1) * ms := by
    field_simp at hss ⊢; linarith
  constructor
  · unfold obsRatio
    convert hpow using 1
    rw [hss, Real.one_rpow, mul_one,
      show A * -(b / a * -(1 / ms ^ 2)) = A * (b / a) / ms ^ 2 by ring, hkey]
    field_simp
  · rw [show b / a * A = A * (b / a) by ring, hkey]
    field_simp

/-- Cochrane (2023), p. 631 (survey **E19**): the printed coefficient `(b/a)(1/(1−b))/m̄²` omits
the factor `A = (1+δ)(1+µ)`: the exact one is `A` times it, so they differ whenever `A ≠ 1`
(and `b ≠ 0`). -/
theorem e19_printed_coefficient {a b A ms : ℝ} (ha : 0 < a) (hb0 : b ≠ 0) (hb : b ≠ 1)
    (hms : 0 < ms) (hA : A ≠ 1) :
    b / a * A / ((1 - b) * ms ^ 2) = A * (b / a * (1 / (1 - b)) / ms ^ 2) ∧
      b / a * A / ((1 - b) * ms ^ 2) ≠ b / a * (1 / (1 - b)) / ms ^ 2 := by
  have h1b : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have e : b / a * A / ((1 - b) * ms ^ 2) = A * (b / a * (1 / (1 - b)) / ms ^ 2) := by
    field_simp
  refine ⟨e, fun h => hA ?_⟩
  have hne : b / a * (1 / (1 - b)) / ms ^ 2 ≠ 0 := by
    have : b / a ≠ 0 := div_ne_zero hb0 ha.ne'
    positivity
  rw [e] at h
  have h2 : (A - 1) * (b / a * (1 / (1 - b)) / ms ^ 2) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact absurd h3 hne

/-- Cochrane (2023), p. 631–632: the map `m_t ↦ m_{t+1}` has exact slope
`1 + (A−1)/(1−b) = 1 − i/(b − 1)` at the steady state. -/
theorem obs_map_hasDerivAt {a b A ms : ℝ} (ha : 0 < a) (hb : b ≠ 1) (hms : 0 < ms)
    (hss : A * (1 - b / a * (1 / ms)) = 1) :
    HasDerivAt (obsMap a b A) (1 - (A - 1) / (b - 1)) ms := by
  obtain ⟨hR, -⟩ := obs_ratio_hasDerivAt ha hb hms hss
  have hR1 : obsRatio a b A ms = 1 := by unfold obsRatio; rw [hss, Real.one_rpow]
  have h := (hasDerivAt_id' ms).mul hR
  have hfun : obsMap a b A = fun m => m * obsRatio a b A m := rfl
  rw [hfun]
  convert h using 1
  have h1b : (1 - b) ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hb1 : (b - 1) ≠ 0 := sub_ne_zero.mpr hb
  rw [hR1]
  field_simp
  ring

/-- Cochrane (2023), p. 631, "The phase diagram … can cut from above rather than below": with
`i = A − 1 > 0`, the slope `1 − i/(b−1)` at the steady state is below one iff `b > 1`. -/
theorem obs_cuts_from_above_iff {b i : ℝ} (hi : 0 < i) (hb : b ≠ 1) :
    1 - i / (b - 1) < 1 ↔ 1 < b := by
  constructor
  · intro h
    by_contra hcon; push Not at hcon
    have hlt : b - 1 < 0 := by rcases hcon.lt_or_eq with h' | h' <;> [linarith; exact absurd h' hb]
    have : i / (b - 1) < 0 := div_neg_of_pos_of_neg hi hlt
    linarith
  · intro h
    have : 0 < i / (b - 1) := div_pos hi (by linarith)
    linarith

/-- Cochrane (2023), pp. 631–632, survey error **E19** (corrected): with `i > 0`, `b ≠ 1`, the
steady state is locally stable (`|slope| < 1`) iff `b > 1 + i/2` — not merely `b > 1`. -/
theorem obs_stable_iff {b i : ℝ} (hi : 0 < i) (hb : b ≠ 1) :
    |1 - i / (b - 1)| < 1 ↔ 1 + i / 2 < b := by
  rw [abs_lt]
  rcases lt_or_gt_of_ne hb with hlt | hgt
  · have : i / (b - 1) < 0 := div_neg_of_pos_of_neg hi (by linarith)
    constructor
    · rintro ⟨-, h⟩; linarith
    · intro h; linarith
  · have hb1 : 0 < b - 1 := by linarith
    constructor
    · rintro ⟨h, -⟩
      have : i / (b - 1) < 2 := by linarith
      rw [div_lt_iff₀ hb1] at this
      linarith
    · intro h
      refine ⟨?_, by have := div_pos hi hb1; linarith⟩
      have : i / (b - 1) < 2 := by rw [div_lt_iff₀ hb1]; linarith
      linarith

/-- Cochrane (2023), p. 632, "negative for `b > 1`. In that case, dynamics are stable"
(survey **E19**, counterexample): `δ = µ = 0.05` gives `i = 1.05² − 1 = 0.1025`; with `b = 1.04`
the slope is `1 − i/(b−1) = −1.5625`, of modulus above one: unstable although `b > 1`. -/
theorem e19_counterexample :
    (1.05 : ℝ) * 1.05 - 1 = 0.1025 ∧ (1 : ℝ) < 1.04 ∧
      1 - (0.1025 : ℝ) / (1.04 - 1) = -1.5625 ∧ 1 < |1 - (0.1025 : ℝ) / (1.04 - 1)| := by
  have h : 1 - (0.1025 : ℝ) / (1.04 - 1) = -1.5625 := by norm_num
  refine ⟨by norm_num, by norm_num, h, ?_⟩
  rw [h]; norm_num [abs_of_neg]

/-! ## Local dynamics of one-dimensional maps -/

/-- A general lemma (not in the book; the orbit form is
`MoneyTargetingDynamics.attracting_of_abs_deriv_lt_one`, of which this is the iterate form): a
fixed point `x` of a map differentiable there with `|f'(x)| < 1` is locally attracting: for `y`
in some ball around `x`, the orbit never gets farther from `x` than `y` is, and converges to
`x`. -/
theorem local_contraction {f : ℝ → ℝ} {x d : ℝ} (hf : HasDerivAt f d x) (hfix : f x = x)
    (hd : |d| < 1) :
    ∃ r, 0 < r ∧ ∀ y, |y - x| < r →
      (∀ t, |f^[t] y - x| ≤ |y - x|) ∧ Tendsto (fun t => f^[t] y) atTop (𝓝 x) := by
  obtain ⟨r, hr, h⟩ := MoneyTargetingDynamics.attracting_of_abs_deriv_lt_one hfix hf hd
  refine ⟨r, hr, fun y hy => ?_⟩
  have h' := h (fun t => f^[t] y) (fun t => Function.iterate_succ_apply' f t y) (by simpa)
  exact ⟨fun t => by simpa using h'.2.1 t, h'.2.2⟩

/-- A general lemma (not in the book; a corollary of
`MoneyTargetingDynamics.repelling_of_one_lt_abs_deriv`): a fixed point `x` with `|f'(x)| > 1` is
locally repelling: in some ball around `x`, the only orbit that stays in the ball forever is the
constant orbit at `x`. -/
theorem local_repulsion {f : ℝ → ℝ} {x d : ℝ} (hf : HasDerivAt f d x) (hfix : f x = x)
    (hd : 1 < |d|) :
    ∃ r, 0 < r ∧ ∀ y : ℕ → ℝ, (∀ t, y (t + 1) = f (y t)) → (∀ t, |y t - x| < r) →
      ∀ t, y t = x := by
  obtain ⟨r, hr, h⟩ := MoneyTargetingDynamics.repelling_of_one_lt_abs_deriv hfix hf hd
  refine ⟨r, hr, fun y hy hin t => ?_⟩
  have h0 : y 0 = x := by
    by_contra hne
    obtain ⟨k, hk⟩ := h y hy hne
    linarith [hin k]
  induction t with
  | zero => exact h0
  | succ n ih => rw [hy n, ih, hfix]

/-- Cochrane (2023), pp. 631–632, "multiple stable equilibria that unquestionably satisfy the
transversality condition" (under the corrected condition `b > 1 + i/2`, E19): with `a > 0`,
`A = 1 + i`, `i > 0`, `A(1 − b/(am̄)) = 1`, there is `r > 0` such that every `m₀` within `r` of
`m̄` starts an orbit of the map that stays in `(b/a, ∞)` (so the first-order condition holds at
every date, `obs_map_iff`), converges to `m̄`, and satisfies the transversality condition
`βᵀ u_c m_T = βᵀ a m_T^{−b} m_T → 0`; distinct `m₀` give distinct equilibria. -/
theorem obs_multiple_stable {a b i β ms : ℝ} (ha : 0 < a) (hi : 0 < i) (hβ : 0 ≤ β)
    (hβ1 : β < 1) (hb : 1 + i / 2 < b) (hms : 0 < ms) (hss : (1 + i) * (1 - b / a * (1 / ms)) = 1) :
    ∃ r, 0 < r ∧ ∀ m0, |m0 - ms| < r →
      (∀ t, b / a < (obsMap a b (1 + i))^[t] m0) ∧
      Tendsto (fun t => (obsMap a b (1 + i))^[t] m0) atTop (𝓝 ms) ∧
      Tendsto (fun T => β ^ T * (a * ((obsMap a b (1 + i))^[T] m0) ^ (-b)) *
        (obsMap a b (1 + i))^[T] m0) atTop (𝓝 0) := by
  have hb1 : b ≠ 1 := by intro h; rw [h] at hb; linarith
  have hderiv := obs_map_hasDerivAt ha hb1 hms hss
  have hfix := (obs_steady_iff ha (by linarith : (1 : ℝ) < 1 + i) hms).2 hss
  have hstab : |1 - (1 + i - 1) / (b - 1)| < 1 := by
    rw [show 1 + i - 1 = i by ring]; exact (obs_stable_iff hi hb1).mpr hb
  obtain ⟨r, hr, hcon⟩ := local_contraction hderiv hfix hstab
  have hbams : b / a < ms := by
    have h1 : b / a * (1 / ms) < 1 := by
      have : 1 - b / a * (1 / ms) = 1 / (1 + i) := by
        rw [eq_div_iff (by positivity), mul_comm]; exact hss
      have : 0 < 1 / (1 + i) := by positivity
      linarith
    rw [mul_one_div, div_lt_one hms] at h1
    exact h1
  refine ⟨min r (ms - b / a), lt_min hr (by linarith), fun m0 hm0 => ?_⟩
  have hm0r : |m0 - ms| < r := lt_of_lt_of_le hm0 (min_le_left _ _)
  obtain ⟨hin, hlim⟩ := hcon m0 hm0r
  refine ⟨fun t => ?_, hlim, ?_⟩
  · have h1 := hin t
    have h2 : |m0 - ms| < ms - b / a := lt_of_lt_of_le hm0 (min_le_right _ _)
    have h3 := neg_abs_le ((obsMap a b (1 + i))^[t] m0 - ms)
    linarith
  · have hc : ContinuousAt (fun m : ℝ => a * m ^ (-b) * m) ms :=
      (continuousAt_const.mul (Real.continuousAt_rpow_const ms (-b) (Or.inl hms.ne'))).mul
        continuousAt_id
    have h1 := hc.tendsto.comp hlim
    have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul h1
    rw [zero_mul] at h2
    refine h2.congr fun T => ?_
    simp only [Function.comp_apply]
    ring

/-- Cochrane (2023), pp. 631–632 (E19): for `1 < b < 1 + i/2` (and for `b < 1`) the steady state
is locally unique: some neighbourhood of `m̄` contains no orbit other than the steady state. -/
theorem obs_locally_unique {a b i ms : ℝ} (ha : 0 < a) (hi : 0 < i) (hb1 : b ≠ 1)
    (hb : b < 1 + i / 2) (hms : 0 < ms) (hss : (1 + i) * (1 - b / a * (1 / ms)) = 1) :
    ∃ r, 0 < r ∧ ∀ m : ℕ → ℝ, (∀ t, m (t + 1) = obsMap a b (1 + i) (m t)) →
      (∀ t, |m t - ms| < r) → ∀ t, m t = ms := by
  have hderiv := obs_map_hasDerivAt ha hb1 hms hss
  have hfix := (obs_steady_iff ha (by linarith : (1 : ℝ) < 1 + i) hms).2 hss
  have hunst : 1 < |1 - (1 + i - 1) / (b - 1)| := by
    rw [show 1 + i - 1 = i by ring]
    have hne : 1 ≠ |1 - i / (b - 1)| := by
      intro h
      rcases lt_or_gt_of_ne hb1 with hlt | hgt
      · have : i / (b - 1) < 0 := div_neg_of_pos_of_neg hi (by linarith)
        rw [abs_of_pos (by linarith)] at h; linarith
      · have hb0 : 0 < b - 1 := by linarith
        have h2 : 2 < i / (b - 1) := by rw [lt_div_iff₀ hb0]; linarith
        rw [abs_of_neg (by linarith)] at h; linarith
    rcases (not_lt.mp (mt (obs_stable_iff hi hb1).mp (not_lt.mpr hb.le))).lt_or_eq with h | h
    · exact h
    · exact absurd h hne
  exact local_repulsion hderiv hfix hunst

/-! ## CES money in utility (p. 632) -/

/-- Cochrane (2023), p. 632: the CES utility
`u(c, m) = ([c^ρ + θm^ρ]^{(1−γ)/ρ} − 1)/(1 − γ)`, `m = M/P`. -/
noncomputable def cesU (ρ θ γ c m : ℝ) : ℝ := ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ) / ρ) - 1) / (1 - γ)

/-- Cochrane (2023), p. 632: `u_c = [c^ρ + θm^ρ]^{(1−γ−ρ)/ρ}c^{ρ−1}` (exact derivative,
`c, m > 0`, `θ > 0`, `ρ ≠ 0`, `γ ≠ 1`). -/
theorem ces_uc {ρ θ γ c m : ℝ} (hρ : ρ ≠ 0) (hγ : γ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) :
    HasDerivAt (fun c => cesU ρ θ γ c m)
      ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * c ^ (ρ - 1)) c := by
  have hg : HasDerivAt (fun c => c ^ ρ + θ * m ^ ρ) (ρ * c ^ (ρ - 1)) c :=
    (Real.hasDerivAt_rpow_const (Or.inl hc.ne')).add_const _
  have hpos : 0 < c ^ ρ + θ * m ^ ρ := by
    have := Real.rpow_pos_of_pos hc ρ; have := Real.rpow_pos_of_pos hm ρ; positivity
  have h := ((hg.rpow_const (p := (1 - γ) / ρ) (Or.inl hpos.ne')).sub_const 1).div_const
    (1 - γ)
  have h1γ : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  change HasDerivAt (fun c => ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ) / ρ) - 1) / (1 - γ)) _ c
  convert h using 1
  rw [show (1 - γ) / ρ - 1 = (1 - γ - ρ) / ρ by field_simp]
  field_simp

/-- Cochrane (2023), p. 632: `u_m = [c^ρ + θm^ρ]^{(1−γ−ρ)/ρ}θm^{ρ−1}`. -/
theorem ces_um {ρ θ γ c m : ℝ} (hρ : ρ ≠ 0) (hγ : γ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) :
    HasDerivAt (fun m => cesU ρ θ γ c m)
      ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * (θ * m ^ (ρ - 1))) m := by
  have hg : HasDerivAt (fun m => c ^ ρ + θ * m ^ ρ) (θ * (ρ * m ^ (ρ - 1))) m :=
    ((Real.hasDerivAt_rpow_const (Or.inl hm.ne')).const_mul θ).const_add _
  have hpos : 0 < c ^ ρ + θ * m ^ ρ := by
    have := Real.rpow_pos_of_pos hc ρ; have := Real.rpow_pos_of_pos hm ρ; positivity
  have h := ((hg.rpow_const (p := (1 - γ) / ρ) (Or.inl hpos.ne')).sub_const 1).div_const
    (1 - γ)
  have h1γ : (1 - γ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hγ)
  change HasDerivAt (fun m => ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ) / ρ) - 1) / (1 - γ)) _ m
  convert h using 1
  rw [show (1 - γ) / ρ - 1 = (1 - γ - ρ) / ρ by field_simp]
  field_simp

/-- Cochrane (2023), p. 632, second line: `u_c(y, m) = [1 + θ(m/y)^ρ]^{(1−γ−ρ)/ρ} y^{−γ}`. -/
theorem ces_uc_form {ρ θ γ y m : ℝ} (hρ : ρ ≠ 0) (hθ : 0 < θ) (hy : 0 < y) (hm : 0 < m) :
    (y ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * y ^ (ρ - 1) =
      (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) * y ^ (-γ) := by
  have hyρ : 0 < y ^ ρ := Real.rpow_pos_of_pos hy ρ
  have h1 : y ^ ρ + θ * m ^ ρ = y ^ ρ * (1 + θ * (m / y) ^ ρ) := by
    rw [Real.div_rpow hm.le hy.le]; field_simp
  have hpos : 0 ≤ 1 + θ * (m / y) ^ ρ := by
    have := Real.rpow_pos_of_pos (div_pos hm hy) ρ; positivity
  rw [h1, Real.mul_rpow hyρ.le hpos, ← Real.rpow_mul hy.le,
    show ρ * ((1 - γ - ρ) / ρ) = 1 - γ - ρ by field_simp]
  rw [mul_comm ((y ^ (1 - γ - ρ))), mul_assoc, ← Real.rpow_add hy,
    show 1 - γ - ρ + (ρ - 1) = -γ by ring]

/-- Cochrane (2023), p. 632, "so asset prices are driven by": the discount factor
`βu_c(t+1)/u_c(t) = β([1 + θ(m'/y')^ρ]/[1 + θ(m/y)^ρ])^{(1−γ−ρ)/ρ}(y'/y)^{−γ}`. -/
theorem ces_sdf {ρ θ γ β y m y' m' : ℝ} (hθ : 0 < θ) (hy : 0 < y) (hm : 0 < m) (hy' : 0 < y')
    (hm' : 0 < m') :
    β * ((1 + θ * (m' / y') ^ ρ) ^ ((1 - γ - ρ) / ρ) * y' ^ (-γ)) /
        ((1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) * y ^ (-γ)) =
      β * (1 + θ * (m' / y') ^ ρ) ^ ((1 - γ - ρ) / ρ) /
        (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) * (y' / y) ^ (-γ) := by
  have h1 : 0 < (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) := by
    have := Real.rpow_pos_of_pos (div_pos hm hy) ρ
    exact Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < y ^ (-γ) := Real.rpow_pos_of_pos hy _
  have := hm'; have := hy'
  rw [Real.div_rpow hy'.le hy.le]
  field_simp

/-- Cochrane (2023), p. 632, "With constant real money `M/(Py)`, we have the usual power utility
formula": if `m'/y' = m/y` the discount factor is `β(y'/y)^{−γ}`. -/
theorem ces_sdf_const {ρ θ γ β y m y' m' : ℝ} (hθ : 0 < θ) (hy : 0 < y) (hm : 0 < m)
    (hconst : m' / y' = m / y) :
    β * (1 + θ * (m' / y') ^ ρ) ^ ((1 - γ - ρ) / ρ) /
        (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) * (y' / y) ^ (-γ) = β * (y' / y) ^ (-γ) := by
  have h1 : 0 < (1 + θ * (m / y) ^ ρ) ^ ((1 - γ - ρ) / ρ) := by
    have := Real.rpow_pos_of_pos (div_pos hm hy) ρ
    exact Real.rpow_pos_of_pos (by positivity) _
  rw [hconst]
  field_simp

/-- Cochrane (2023), p. 632: the CES marginal rate of substitution `u_m/u_c = θ(m/c)^{ρ−1}`. -/
theorem ces_mrs {ρ θ γ c m : ℝ} (hθ : 0 < θ) (hc : 0 < c) (hm : 0 < m) :
    (c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * (θ * m ^ (ρ - 1)) /
        ((c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) * c ^ (ρ - 1)) = θ * (m / c) ^ (ρ - 1) := by
  have hpos : 0 < (c ^ ρ + θ * m ^ ρ) ^ ((1 - γ - ρ) / ρ) := by
    have := Real.rpow_pos_of_pos hc ρ; have := Real.rpow_pos_of_pos hm ρ
    exact Real.rpow_pos_of_pos (by positivity) _
  have := Real.rpow_pos_of_pos hc (ρ - 1)
  rw [Real.div_rpow hm.le hc.le]
  field_simp

/-- Cochrane (2023), p. 632, "the money demand function (19.16) becomes
`M_t = P_ty_t((1/θ)i_t/(1+i_t))^{1/(ρ−1)}`": for `ρ ≠ 1`, `k = i/(1+i) > 0`,
`θ(m/c)^{ρ−1} = k` iff `m = c(k/θ)^{1/(ρ−1)}`. -/
theorem ces_money_demand_iff {ρ θ c m k : ℝ} (hρ : ρ ≠ 1) (hθ : 0 < θ) (hc : 0 < c)
    (hm : 0 < m) (hk : 0 < k) :
    θ * (m / c) ^ (ρ - 1) = k ↔ m = c * (1 / θ * k) ^ (1 / (ρ - 1)) := by
  have hρ1 : (ρ - 1) ≠ 0 := sub_ne_zero.mpr hρ
  have hmc : 0 < m / c := div_pos hm hc
  constructor
  · intro h
    have h1 : (m / c) ^ (ρ - 1) = 1 / θ * k := by rw [← h]; field_simp
    rw [← h1, show 1 / (ρ - 1) = (ρ - 1)⁻¹ by ring, Real.rpow_rpow_inv hmc.le hρ1]
    field_simp
  · intro h
    have h1 : m / c = (1 / θ * k) ^ (1 / (ρ - 1)) := by rw [h]; field_simp
    rw [h1, show 1 / (ρ - 1) = (ρ - 1)⁻¹ by ring, Real.rpow_inv_rpow (by positivity) hρ1]
    field_simp

/-- Cochrane (2023), p. 632, "Here too we have a unit income elasticity": with `m = y·K` the
exact elasticity `d log m/d log y` equals one. -/
theorem ces_income_elasticity {K ly : ℝ} (hK : 0 < K) :
    HasDerivAt (fun l => Real.log (Real.exp l * K)) 1 ly := by
  have h : (fun l => Real.log (Real.exp l * K)) = fun l => l + Real.log K := by
    funext l; rw [Real.log_mul (Real.exp_pos l).ne' hK.ne', Real.log_exp]
  rw [h]
  simpa using (hasDerivAt_id ly).add_const (Real.log K)

/-- Cochrane (2023), p. 632, "and an interest elasticity governed by the separate parameter ρ":
with `m = c(k/θ)^{1/(ρ−1)}`, the exact elasticity `d log m/d log k` (`k = i/(1+i)`) is
`1/(ρ − 1)`. -/
theorem ces_interest_elasticity {ρ θ c lk : ℝ} (hθ : 0 < θ) (hc : 0 < c) :
    HasDerivAt (fun l => Real.log (c * (1 / θ * Real.exp l) ^ (1 / (ρ - 1)))) (1 / (ρ - 1)) lk := by
  have h : (fun l => Real.log (c * (1 / θ * Real.exp l) ^ (1 / (ρ - 1)))) =
      fun l => Real.log c + 1 / (ρ - 1) * (Real.log (1 / θ) + l) := by
    funext l
    have h1 : 0 < 1 / θ * Real.exp l := by positivity
    rw [Real.log_mul hc.ne' (Real.rpow_pos_of_pos h1 _).ne', Real.log_rpow h1,
      Real.log_mul (by positivity) (Real.exp_pos l).ne', Real.log_exp]
  rw [h]
  simpa using (((hasDerivAt_id lk).const_add (Real.log (1 / θ))).const_mul (1 / (ρ - 1))).const_add
    (Real.log c)

end Cochrane.Monetarism.Nonseparable
