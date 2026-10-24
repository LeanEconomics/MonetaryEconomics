/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Unemployment.Expectations
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exercise 7.3: taming the wealth effect on labour supply

Galí (2015), Chapter 7, Exercise 7.3, pp. 221–222. Member `(j, s)` has utility
`log C_t(j, s) − 1_t(j, s) χ_t Θ_t s^φ`, with `Θ_t = Z_t/C̄_t`, `C̄_t` aggregate consumption and
`Z_t = Z_{t−1}^{1−υ} C̄_t^υ`, `υ ∈ [0, 1]`; consumption is fully shared within the household.

## (a) Household utility

* `integral_disutility`: `∫₀¹ 1{s ≤ N} K s^φ ds = K N^{1+φ}/(1 + φ)` (a genuine interval
  integral; members `s ∈ [0, N]`, those with the lowest disutility, are employed).
* `member_integral`, `household_utility`: with full risk sharing `C_t(j, s) = C_t`,
  `∫₀¹∫₀¹ U(j, s) ds dj = log C_t − χ_tΘ_t ∫₀¹ N_t(j)^{1+φ}/(1 + φ) dj`.

## (b) Participation and the wealth effect

* `works_iff`: member `(j, s)` works iff `(W/P)/C ≥ χΘs^φ`; `participants_iff`: the participants
  of a type are exactly `s ≤ L = ((W/P)/(CχΘ))^{1/φ}`.
* `participation_log`: at the marginal participant, with `C = C̄`,
  `w − p = ξ_t + z_t + φ l` (exact in logs); `z_log`: `z_t = (1 − υ) z_{t−1} + υ c_t`.
* `zPath`, `zPath_one` (`υ = 1 ⇒ z = c`, the log-utility wealth effect of (6) with `σ = 1`,
  `participation_upsilon_one`), `zPath_zero` (`υ = 0 ⇒ z` constant: no wealth effect).
* `zPath_add`: the response of `z` to a consumption perturbation does not depend on the baseline;
  `zPath_permanent`: to a permanent change `Δ`, `z` responds by `(1 − (1 − υ)^{t+1}) Δ`;
  `labourForce_response`: the labour force responds by `−(1 − (1 − υ)^{t+1}) Δ/φ`.
* **Dampening** (`dampening_strictMonoOn`, `labourForce_dampening`): the size of that response is
  strictly increasing in `υ ∈ [0, 1]`, from `0` (`υ = 0`) to the full `|Δ|/φ` (`υ = 1`); the impact
  response to any consumption change is `υ` times the full one (`zPath_pulse`).
* Precision note (`lagged_pulse_not_monotone`): the response at lag `k ≥ 1` to a *one-period*
  consumption change, `υ(1 − υ)ᵏ`, is not monotone in `υ`; the dampening claim holds for impact and
  for persistent changes.
-/

namespace Gali.Unemployment.Ex7_3

/-! ### (a) Household utility -/

/-- Galí (2015), Exercise 7.3, p. 221: the period utility of member `s` of a labour type with
employment rate `N`: `log C − 1{s ≤ N} χΘ s^φ` (members `s ∈ [0, N]` work; `K = χΘ`). -/
noncomputable def memberU (C K φ N s : ℝ) : ℝ :=
  Real.log C - (Set.Iic N).indicator (fun s => K * s ^ φ) s

/-- Galí (2015), Exercise 7.3(a), p. 222: `s ↦ 1{s ≤ N} K s^φ` is interval integrable on
`[0, 1]` (for `φ ≥ 0`). -/
theorem disutility_intervalIntegrable {K φ N : ℝ} (hφ : 0 ≤ φ) :
    IntervalIntegrable ((Set.Iic N).indicator (fun s => K * s ^ φ)) MeasureTheory.volume 0 1 := by
  have hc : Continuous (fun s : ℝ => K * s ^ φ) :=
    continuous_const.mul (Real.continuous_rpow_const hφ)
  refine (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr ?_
  exact (hc.intervalIntegrable 0 1).1.indicator measurableSet_Iic

/-- Galí (2015), Exercise 7.3(a), p. 222 (**the disutility integral**): for `φ ≥ 0` and
`0 ≤ N ≤ 1`, `∫₀¹ 1{s ≤ N} K s^φ ds = K N^{1+φ}/(1 + φ)`. -/
theorem integral_disutility {K φ N : ℝ} (hφ : 0 ≤ φ) (hN0 : 0 ≤ N) (hN1 : N ≤ 1) :
    ∫ s in (0 : ℝ)..1, (Set.Iic N).indicator (fun s => K * s ^ φ) s =
      K * N ^ (1 + φ) / (1 + φ) := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.setIntegral_indicator measurableSet_Iic]
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iic N = Set.Ioc 0 N := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
    constructor
    · rintro ⟨⟨h0, -⟩, h2⟩
      exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩
      exact ⟨⟨h0, h2.trans hN1⟩, h2⟩
  rw [hset, ← intervalIntegral.integral_of_le hN0, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
  rw [add_comm φ 1]
  ring

/-- Galí (2015), Exercise 7.3(a), p. 222 (**one labour type**): with full risk sharing
(`C(j, s) = C` for every member) the integral of members' utilities over `s ∈ [0, 1]` is
`log C − K N^{1+φ}/(1 + φ)`. -/
theorem member_integral {C K φ N : ℝ} (hφ : 0 ≤ φ) (hN0 : 0 ≤ N) (hN1 : N ≤ 1)
    {Cm : ℝ → ℝ} (hrs : ∀ s, Cm s = C) :
    ∫ s in (0 : ℝ)..1, memberU (Cm s) K φ N s = Real.log C - K * N ^ (1 + φ) / (1 + φ) := by
  simp only [memberU, hrs]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (disutility_intervalIntegrable hφ), intervalIntegral.integral_const,
    integral_disutility hφ hN0 hN1]
  simp

/-- Galí (2015), Exercise 7.3(a), p. 222: `Θ_t = Z_t/C̄_t`. -/
noncomputable def theta (Z Cbar : ℝ) : ℝ := Z / Cbar

/-- **Galí (2015), Exercise 7.3(a), p. 222 (the household's period utility)**: with full risk
sharing (`C(j, s) = C_t`), employment rates `N(j) ∈ [0, 1]` with `j ↦ N(j)^{1+φ}` integrable, and
`Θ_t = Z_t/C̄_t`, the integral over the household's members `(j, s) ∈ [0, 1]²` of
`log C(j, s) − 1(j, s) χ_t Θ_t s^φ` equals `log C_t − χ_tΘ_t ∫₀¹ N(j)^{1+φ}/(1 + φ) dj`. -/
theorem household_utility {C χ Z Cbar φ : ℝ} (hφ : 0 ≤ φ) {N : ℝ → ℝ}
    (hN0 : ∀ j, 0 ≤ N j) (hN1 : ∀ j, N j ≤ 1)
    (hint : IntervalIntegrable (fun j => N j ^ (1 + φ) / (1 + φ)) MeasureTheory.volume 0 1)
    {Cm : ℝ → ℝ → ℝ} (hrs : ∀ j s, Cm j s = C) :
    ∫ j in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, memberU (Cm j s) (χ * theta Z Cbar) φ (N j) s =
      Real.log C - χ * theta Z Cbar * ∫ j in (0 : ℝ)..1, N j ^ (1 + φ) / (1 + φ) := by
  have h1 : ∀ j, ∫ s in (0 : ℝ)..1, memberU (Cm j s) (χ * theta Z Cbar) φ (N j) s =
      Real.log C - χ * theta Z Cbar * (N j ^ (1 + φ) / (1 + φ)) := fun j => by
    rw [member_integral hφ (hN0 j) (hN1 j) (hrs j)]
    ring
  simp_rw [h1]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hint.const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  simp

/-! ### (b) Participation -/

/-- Galí (2015), Exercise 7.3(b), p. 222 (**the participation condition**): measured in utility
(marginal utility of consumption `1/C` under log utility and full risk sharing), member `(j, s)`
gains from working iff `(1/C)(W/P) − χΘs^φ ≥ 0`, i.e. iff `(W/P)/C ≥ χΘ s^φ`. -/
theorem works_iff {WP C K φ s : ℝ} : 0 ≤ (1 / C) * WP - K * s ^ φ ↔ K * s ^ φ ≤ WP / C := by
  rw [one_div_mul_eq_div]
  constructor <;> intro h <;> linarith

/-- Galí (2015), Exercise 7.3(b), p. 222 (**the participants are an interval**): for `φ > 0`,
`K = χΘ > 0`, `R = (W/P)/C ≥ 0` and `s ≥ 0`, `K s^φ ≤ R` iff `s ≤ L` with
`L = (R/K)^{1/φ}`, the marginal participant (`K L^φ = R`). -/
theorem participants_iff {R K φ s : ℝ} (hφ : 0 < φ) (hK : 0 < K) (hR : 0 ≤ R) (hs : 0 ≤ s) :
    (K * s ^ φ ≤ R ↔ s ≤ (R / K) ^ (1 / φ)) ∧ K * ((R / K) ^ (1 / φ)) ^ φ = R := by
  have hRK : 0 ≤ R / K := div_nonneg hR hK.le
  have hinv : 0 < 1 / φ := by positivity
  refine ⟨?_, ?_⟩
  · rw [← le_div_iff₀' hK, ← Real.rpow_le_rpow_iff (Real.rpow_nonneg hs φ) hRK hinv,
      ← Real.rpow_mul hs, mul_one_div_cancel hφ.ne', Real.rpow_one]
  · rw [← Real.rpow_mul hRK, one_div_mul_cancel hφ.ne', Real.rpow_one]
    field_simp

/-- Galí (2015), Exercise 7.3(b), p. 222 (**the participation equation, exact in logs**): at the
marginal participant `(W/P)/C = χΘL^φ` with `Θ = Z/C̄` and, in equilibrium, `C = C̄`:
`log(W/P) = ξ + z + φ l` with `ξ = log χ`, `z = log Z`, `l = log L`. -/
theorem participation_log {WP C Cbar χ Z L φ : ℝ} (hC : 0 < C) (hχ : 0 < χ)
    (hZ : 0 < Z) (hL : 0 < L) (hm : WP / C = χ * theta Z Cbar * L ^ φ) (heq : C = Cbar) :
    Real.log WP = Real.log χ + Real.log Z + φ * Real.log L := by
  subst heq
  have hWP' : WP = χ * Z * L ^ φ := by
    unfold theta at hm
    field_simp at hm
    linarith
  rw [hWP', Real.log_mul (by positivity) (by positivity), Real.log_mul hχ.ne' hZ.ne',
    Real.log_rpow hL]

/-- Galí (2015), Exercise 7.3, p. 221 (**the law of motion of `z`, exact in logs**): from
`Z_t = Z_{t−1}^{1−υ} C̄_t^υ`, `z_t = (1 − υ) z_{t−1} + υ c_t`. -/
theorem z_log {Zprev Cbar υ : ℝ} (hZ : 0 < Zprev) (hC : 0 < Cbar) :
    Real.log (Zprev ^ (1 - υ) * Cbar ^ υ) = (1 - υ) * Real.log Zprev + υ * Real.log Cbar := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hZ, Real.log_rpow hC]

/-- Galí (2015), Exercise 7.3, p. 221: the path of `z_t` given `z_{−1} = z₀` and a consumption
path `c`, `z_t = (1 − υ) z_{t−1} + υ c_t`. -/
def zPath (υ z0 : ℝ) (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => (1 - υ) * z0 + υ * c 0
  | t + 1 => (1 - υ) * zPath υ z0 c t + υ * c (t + 1)

/-- Galí (2015), Exercise 7.3(b), p. 222 (**`υ = 1`: the standard wealth effect**): `z = c`. -/
theorem zPath_one (z0 : ℝ) (c : ℕ → ℝ) : zPath 1 z0 c = c := by
  funext t
  cases t <;> simp [zPath]

/-- Galí (2015), Exercise 7.3(b), p. 222 (**`υ = 0`: no wealth effect**): `z_t = z_{−1}`. -/
theorem zPath_zero (z0 : ℝ) (c : ℕ → ℝ) (t : ℕ) : zPath 0 z0 c t = z0 := by
  induction t with
  | zero => simp [zPath]
  | succ t ih => simp [zPath, ih]

/-- Galí (2015), Exercise 7.3(b), p. 222: with `υ = 1` the participation equation
`w − p = ξ + z + φl` is the baseline (6) `w − p = σc + φl + ξ` with `σ = 1` (log utility). -/
theorem participation_upsilon_one {φ z0 : ℝ} {c wr ξ l : ℕ → ℝ} :
    (∀ t, wr t = ξ t + zPath 1 z0 c t + φ * l t) ↔ ∀ t, wr t = 1 * c t + φ * l t + ξ t := by
  rw [zPath_one]
  refine forall_congr' fun t => ?_
  constructor <;> intro h <;> linarith

/-- Galí (2015), Exercise 7.3(b), p. 222 (**linearity**): `z` along `c + Δc` is `z` along `c`
plus the response `zPath υ 0 Δc`, which depends neither on `z_{−1}` nor on the baseline `c`. -/
theorem zPath_add (υ z0 : ℝ) (c dc : ℕ → ℝ) (t : ℕ) :
    zPath υ z0 (fun s => c s + dc s) t = zPath υ z0 c t + zPath υ 0 dc t := by
  induction t with
  | zero => simp [zPath]; ring
  | succ t ih => simp only [zPath, ih]; ring

/-- Galí (2015), Exercise 7.3(b), p. 222 (**response to a permanent consumption change**): a
permanent change `Δ` in consumption from date `0` on moves `z_t` by `(1 − (1 − υ)^{t+1}) Δ`. -/
theorem zPath_permanent (υ Δ : ℝ) (t : ℕ) :
    zPath υ 0 (fun _ => Δ) t = (1 - (1 - υ) ^ (t + 1)) * Δ := by
  induction t with
  | zero => simp [zPath]
  | succ t ih => simp only [zPath, ih, pow_succ]; ring

/-- Galí (2015), Exercise 7.3(b), p. 222 (**impact and lagged responses to a one-period
consumption change** at date `t₀`): `z` is unaffected before `t₀`, moves by `υ` on impact and by
`υ(1 − υ)ᵏ` after `k` periods. -/
theorem zPath_pulse (υ : ℝ) (t0 k : ℕ) :
    (∀ t < t0, zPath υ 0 (fun s => if s = t0 then 1 else 0) t = 0) ∧
      zPath υ 0 (fun s => if s = t0 then 1 else 0) (t0 + k) = υ * (1 - υ) ^ k := by
  have hbefore : ∀ t < t0, zPath υ 0 (fun s => if s = t0 then 1 else 0) t = 0 := by
    intro t ht
    induction t with
    | zero =>
      have : (0 : ℕ) ≠ t0 := by omega
      simp [zPath, this]
    | succ t ih =>
      have : t + 1 ≠ t0 := by omega
      simp [zPath, ih (by omega), this]
  refine ⟨hbefore, ?_⟩
  induction k with
  | zero =>
    cases t0 with
    | zero => simp [zPath]
    | succ t0 =>
      simp only [zPath, ↓reduceIte, pow_zero, mul_one]
      rw [hbefore t0 (by omega)]
      ring
  | succ k ih =>
    have : t0 + k + 1 ≠ t0 := by omega
    rw [← add_assoc]
    simp only [zPath, ih, this, ↓reduceIte, pow_succ]
    ring

/-- Galí (2015), Exercise 7.3(b), p. 222: the labour force implied by the participation equation,
`l_t = (ω_t − ξ_t − z_t)/φ`. -/
noncomputable def labourForce (φ : ℝ) (wr ξ z : ℕ → ℝ) (t : ℕ) : ℝ := (wr t - ξ t - z t) / φ

/-- Galí (2015), Exercise 7.3(b), p. 222: for `φ ≠ 0`, `l = labourForce` is the unique solution
of the participation equation `ω_t = ξ_t + z_t + φ l_t`. -/
theorem labourForce_iff {φ : ℝ} (hφ : φ ≠ 0) {wr ξ z l : ℕ → ℝ} :
    (∀ t, wr t = ξ t + z t + φ * l t) ↔ l = labourForce φ wr ξ z := by
  constructor
  · intro h
    funext t
    rw [labourForce, eq_div_iff hφ, h t]
    ring
  · rintro rfl t
    rw [labourForce]
    field_simp
    ring

/-- **Galí (2015), Exercise 7.3(b), p. 222 (the labour-force response to a permanent consumption
change)**: holding the real wage and `ξ` fixed, a permanent consumption change `Δ` changes the
labour force at date `t` by `−(1 − (1 − υ)^{t+1}) Δ/φ` (for any `z_{−1}` and baseline `c`). -/
theorem labourForce_response (φ υ z0 Δ : ℝ) (wr ξ c : ℕ → ℝ) (t : ℕ) :
    labourForce φ wr ξ (zPath υ z0 fun s => c s + Δ) t - labourForce φ wr ξ (zPath υ z0 c) t =
      -((1 - (1 - υ) ^ (t + 1)) * Δ / φ) := by
  have h := zPath_add υ z0 c (fun _ => Δ) t
  rw [zPath_permanent] at h
  simp only [labourForce, h]
  ring

/-- Galí (2015), Exercise 7.3(b), p. 222 (**dampening**): for every horizon `t`, the share
`1 − (1 − υ)^{t+1}` of the full response is strictly increasing in `υ ∈ [0, 1]`, equals `0` at
`υ = 0` and `1` at `υ = 1`, and lies in `[0, 1]`. -/
theorem dampening_strictMonoOn (t : ℕ) :
    StrictMonoOn (fun υ : ℝ => 1 - (1 - υ) ^ (t + 1)) (Set.Icc 0 1) ∧
      (1 - (1 - (0 : ℝ)) ^ (t + 1) = 0) ∧ (1 - (1 - (1 : ℝ)) ^ (t + 1) = 1) ∧
      ∀ υ ∈ Set.Icc (0 : ℝ) 1, 0 ≤ 1 - (1 - υ) ^ (t + 1) ∧ 1 - (1 - υ) ^ (t + 1) ≤ 1 := by
  refine ⟨fun a ha b hb hab => ?_, by simp, by simp, fun υ hυ => ?_⟩
  · simp only
    have h1 : 0 ≤ 1 - b := by linarith [hb.2]
    have h2 : 1 - b < 1 - a := by linarith
    have := pow_lt_pow_left₀ h2 h1 (by omega : t + 1 ≠ 0)
    linarith
  · have h0 : 0 ≤ 1 - υ := by linarith [hυ.2]
    have h1 : 1 - υ ≤ 1 := by linarith [hυ.1]
    have hp0 : 0 ≤ (1 - υ) ^ (t + 1) := pow_nonneg h0 _
    have hp1 : (1 - υ) ^ (t + 1) ≤ 1 := pow_le_one₀ h0 h1
    constructor <;> linarith

/-- **Galí (2015), Exercise 7.3(b), p. 222 (an intermediate `υ` dampens the labour-force
response)**: for `φ > 0` and `Δ ≠ 0`, the absolute labour-force response at every date `t` to a
permanent consumption change `Δ` is strictly increasing in `υ ∈ [0, 1]`; it is `0` for `υ = 0`
and the full log-utility response `|Δ|/φ` for `υ = 1`. -/
theorem labourForce_dampening {φ Δ : ℝ} (hφ : 0 < φ) (hΔ : Δ ≠ 0) (z0 : ℝ) (wr ξ c : ℕ → ℝ)
    (t : ℕ) :
    StrictMonoOn (fun υ => |labourForce φ wr ξ (zPath υ z0 fun s => c s + Δ) t -
        labourForce φ wr ξ (zPath υ z0 c) t|) (Set.Icc 0 1) ∧
      |labourForce φ wr ξ (zPath 0 z0 fun s => c s + Δ) t -
        labourForce φ wr ξ (zPath 0 z0 c) t| = 0 ∧
      |labourForce φ wr ξ (zPath 1 z0 fun s => c s + Δ) t -
        labourForce φ wr ξ (zPath 1 z0 c) t| = |Δ| / φ := by
  have he : ∀ υ, |labourForce φ wr ξ (zPath υ z0 fun s => c s + Δ) t -
      labourForce φ wr ξ (zPath υ z0 c) t| = (1 - (1 - υ) ^ (t + 1)) * (|Δ| / φ) ∨
      (1 - (1 - υ) ^ (t + 1)) < 0 := by
    intro υ
    rw [labourForce_response]
    by_cases h : 0 ≤ 1 - (1 - υ) ^ (t + 1)
    · left
      rw [abs_neg, mul_div_assoc, abs_mul, abs_of_nonneg h, abs_div, abs_of_pos hφ]
    · right
      linarith
  obtain ⟨hmono, h0, h1, hrange⟩ := dampening_strictMonoOn t
  have hpos : 0 < |Δ| / φ := div_pos (abs_pos.mpr hΔ) hφ
  have key : ∀ υ ∈ Set.Icc (0 : ℝ) 1, |labourForce φ wr ξ (zPath υ z0 fun s => c s + Δ) t -
      labourForce φ wr ξ (zPath υ z0 c) t| = (1 - (1 - υ) ^ (t + 1)) * (|Δ| / φ) := by
    intro υ hυ
    rcases he υ with h | h
    · exact h
    · exact absurd (hrange υ hυ).1 (not_le.mpr h)
  refine ⟨fun a ha b hb hab => ?_, ?_, ?_⟩
  · simp only
    rw [key a ha, key b hb]
    exact mul_lt_mul_of_pos_right (hmono ha hb hab) hpos
  · rw [key 0 ⟨le_rfl, zero_le_one⟩, h0, zero_mul]
  · rw [key 1 ⟨zero_le_one, le_rfl⟩, h1, one_mul]

/-- Galí (2015), Exercise 7.3(b), p. 222 (**precision note**): the response at lag `k = 1` to a
one-period consumption change, `υ(1 − υ)`, is not monotone in `υ`: it is `1/4` at `υ = 1/2` but
`0` at `υ = 1`. The dampening claim concerns impact responses (`υ`, increasing) and persistent
changes (`labourForce_dampening`). -/
theorem lagged_pulse_not_monotone :
    ¬ MonotoneOn (fun υ : ℝ => zPath υ 0 (fun s => if s = 0 then 1 else 0) (0 + 1))
      (Set.Icc 0 1) := by
  intro h
  have hle := h ⟨by norm_num, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num : (1 / 2 : ℝ) ≤ 1)
  simp only [(zPath_pulse _ 0 1).2] at hle
  norm_num at hle

end Gali.Unemployment.Ex7_3
