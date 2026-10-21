/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.IRulePredetermined

/-!
# Optimal policy under imperfect information

Woodford (2003), *Interest and Prices*, Chapter 8, §3.4, pp. 606–610: eqs. (3.32)–(3.35).

The private sector forms expectations with an `ExpectationSystem` `𝔼`; the central bank, which
knows less, with a second system `𝔹` (`z_{t|t} = 𝔹.E t z_t`). "Less information" is the tower
relation `Nested 𝔼 𝔹`: `𝔹_t 𝔼_t = 𝔹_t` and `𝔼_t 𝔹_t = 𝔹_t`.

## Main results

* `eq334`: the ideal instrument setting `ī_t = i* − (σ/λᵢ)φ_{1t}` (3.33) obeys (3.34) — the law of
  motion (3.7) with the coefficients (3.8)–(3.9) — whenever (3.3)–(3.4) hold (the algebra is that
  of (3.7)); no condition links it to the actual interest rate.
* `eq335_iff`: (3.32) holds iff `i_t = ī_{t|t}` (3.35).
* `eq332_optimal`: (3.32) is the genuine optimality condition for an instrument setting the bank
  can condition only on its own information — among all settings known to the bank at `t`, the
  one satisfying (3.32) minimises the bank's expected value of the `i_t`-terms of the Lagrangian,
  with excess `(λᵢ/2) 𝔹_s(i' − i)²`.
* `eq335_expanded`: `i_t = (1 − ρ₁)i* + ρ₁ ī_{t−1|t} + ρ₂(ī_{t−1|t} − ī_{t−2|t}) + φπ π_{t|t}
  + (φx/4)(x_{t|t} − x_{t−1|t})` (p. 608).
* `naive_rule_not_optimal` (p. 608): the "certainty-equivalent" rule that replaces each term of
  (3.7) by its estimate, keeping the actual lagged rates `i_{t−1}, i_{t−2}`, does not reproduce the
  optimal setting — a two-state example in which the bank learns the state with a lag.

Kalman filtering (computing `ī_{t|t}` recursively), the fixed point between the filter and the
equilibrium, and the general certainty-equivalence results of Svensson and Woodford (2002b) are
outside the scope of this module.
-/

namespace Woodford.OptimalPolicyRules.ImperfectInfo

open Filter Topology
open IRuleBasic (rho1 rho2 phiPi phiX)

variable {Ω : Type*}

/-- Woodford (2003), p. 607: the central bank (expectations `𝔹`) has less information than
the private sector (expectations `𝔼`) each period: `𝔹_t 𝔼_t = 𝔹_t` and `𝔼_t 𝔹_t = 𝔹_t`. -/
def Nested (𝔼 𝔹 : ExpectationSystem Ω) : Prop :=
  ∀ t (x : Ω → ℝ), 𝔹.E t (𝔼.E t x) = 𝔹.E t x ∧ 𝔼.E t (𝔹.E t x) = 𝔹.E t x

/-- Woodford (2003), p. 607: a setting chosen by the bank at `t` (`𝔹_t i = i`) is known to
the private sector at `t`. -/
theorem known_private {𝔼 𝔹 : ExpectationSystem Ω} (h : Nested 𝔼 𝔹) {t : ℕ} {i : Ω → ℝ}
    (hi : 𝔹.E t i = i) : 𝔼.E t i = i := by
  rw [← hi, (h t i).2]

/-- Woodford (2003), eq. (3.3), p. 584: `π_t − β⁻¹σ φ_{1,t−1} + φ_{2t} − φ_{2,t−1} = 0`. -/
def FOC33 (β σ : ℝ) (π φ1 φ2 : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, π t ω - β⁻¹ * σ * φ1 (t - 1) ω + φ2 t ω - φ2 (t - 1) ω = 0

/-- Woodford (2003), eq. (3.4), p. 584: `λx(x_t − x*) + φ_{1t} − β⁻¹φ_{1,t−1} − κφ_{2t} = 0`. -/
def FOC34 (β κ lamx xs : ℝ) (x φ1 φ2 : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, lamx * (x t ω - xs) + φ1 t ω - β⁻¹ * φ1 (t - 1) ω - κ * φ2 t ω = 0

/-- Woodford (2003), eq. (3.32), p. 607: `λᵢ(i_t − i*) + σ φ_{1t|t} = 0`. -/
def FOC332 (𝔹 : ExpectationSystem Ω) (σ lami istar : ℝ) (i φ1 : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, lami * (i t ω - istar) + σ * 𝔹.E t (φ1 t) ω = 0

/-- Woodford (2003), eq. (3.33), p. 607: the ideal instrument setting `ī_t = i* − (σ/λᵢ)φ_{1t}`
(the book writes `Ξ_{1t}` for the multiplier `φ_{1t}`). -/
noncomputable def ibar (σ lami istar : ℝ) (φ1 : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => istar - σ / lami * φ1 t ω

/-- Woodford (2003), eq. (3.34), p. 608 (**the ideal setting follows (3.7)**): if (3.3) holds at
`t` and (3.4) at `t` and `t − 1` (`t ≥ 2`), then
`ī_t = (1 − ρ₁)i* + ρ₁ī_{t−1} + ρ₂Δī_{t−1} + φπ π_t + φx Δx_t/4` with (3.8)–(3.9). -/
theorem eq334 {β κ σ lamx xs lami istar : ℝ} {π x φ1 φ2 : ℕ → Ω → ℝ} {t : ℕ} (ht : 2 ≤ t)
    (h3 : FOC33 β σ π φ1 φ2 t) (h4 : FOC34 β κ lamx xs x φ1 φ2 t)
    (h4m : FOC34 β κ lamx xs x φ1 φ2 (t - 1)) (ω : Ω) :
    ibar σ lami istar φ1 t ω = (1 - rho1 β σ κ) * istar
      + rho1 β σ κ * ibar σ lami istar φ1 (t - 1) ω
      + rho2 β * (ibar σ lami istar φ1 (t - 1) ω - ibar σ lami istar φ1 (t - 2) ω)
      + phiPi σ κ lami * π t ω + phiX σ lamx lami * (x t ω - x (t - 1) ω) / 4 := by
  have f3 := h3 ω
  have f4 := h4 ω
  have f4m := h4m ω
  rw [show t - 1 - 1 = t - 2 by omega] at f4m
  simp only [ibar, rho1, rho2, phiPi, phiX]
  linear_combination lami⁻¹ * (-(κ * σ) * f3 - σ * f4 + σ * f4m)

/-- Woodford (2003), eq. (3.35), p. 608: (3.32) holds iff `i_t = ī_{t|t}` (`λᵢ ≠ 0`). -/
theorem eq335_iff (𝔹 : ExpectationSystem Ω) {σ lami istar : ℝ} (hlami : lami ≠ 0)
    {i φ1 : ℕ → Ω → ℝ} (t : ℕ) :
    FOC332 𝔹 σ lami istar i φ1 t ↔ i t = 𝔹.E t (ibar σ lami istar φ1 t) := by
  have e : ibar σ lami istar φ1 t = (fun _ => istar) - (σ / lami) • φ1 t := by
    funext ω; simp [ibar]
  rw [e, map_sub, map_smul, 𝔹.const]
  constructor
  · intro h
    funext ω
    have := h ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  · intro h ω
    rw [h]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- Woodford (2003), p. 607 (**(3.32) is the optimality condition under the bank's information**):
the interest rate enters the Lagrangian through `(λᵢ/2)(i_t − i*)² + σφ_{1t} i_t`. If `i_t` is
known to the bank (`𝔹_t i_t = i_t`) and satisfies (3.32), then for every other setting `i'` known to
the bank at `t` and every `s ≤ t`, with pull-out for `𝔹`,
`𝔹_s[(λᵢ/2)(i' − i*)² + σφ₁i'] = 𝔹_s[(λᵢ/2)(i_t − i*)² + σφ₁i_t] + (λᵢ/2)𝔹_s(i' − i_t)²`;
so `i_t` minimises the bank's expected loss term, uniquely in mean square for `λᵢ > 0`. -/
theorem eq332_optimal (𝔹 : ExpectationSystem Ω) (hPO : 𝔹.PullOut) {σ lami istar : ℝ}
    {i φ1 : ℕ → Ω → ℝ} {t s : ℕ} (hst : s ≤ t) (h : FOC332 𝔹 σ lami istar i φ1 t)
    (hi : 𝔹.E t (i t) = i t) {i' : Ω → ℝ} (hi' : 𝔹.E t i' = i') :
    𝔹.E s (fun ω => lami / 2 * (i' ω - istar) ^ 2 + σ * φ1 t ω * i' ω) =
      𝔹.E s (fun ω => lami / 2 * (i t ω - istar) ^ 2 + σ * φ1 t ω * i t ω) +
        (lami / 2) • 𝔹.E s (fun ω => (i' ω - i t ω) ^ 2) := by
  set D : Ω → ℝ := i' - i t with hD
  set Y : Ω → ℝ := fun ω => lami * (i t ω - istar) + σ * φ1 t ω with hY
  have hDk : 𝔹.E t D = D := by rw [hD, map_sub, hi, hi']
  have hEY : 𝔹.E t Y = 0 := by
    have e : Y = lami • (i t - fun _ => istar) + σ • φ1 t := by funext ω; simp [hY]
    rw [e, map_add, map_smul, map_smul, map_sub, hi, 𝔹.const]
    funext ω
    have := h ω
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
    linarith
  have hcross : 𝔹.E s (D * Y) = 0 := by
    rw [← 𝔹.tower hst, hPO t D Y hDk, hEY, mul_zero, map_zero]
  have hfun : (fun ω => lami / 2 * (i' ω - istar) ^ 2 + σ * φ1 t ω * i' ω) =
      (fun ω => lami / 2 * (i t ω - istar) ^ 2 + σ * φ1 t ω * i t ω) +
        (lami / 2) • (fun ω => (i' ω - i t ω) ^ 2) + D * Y := by
    funext ω
    simp only [hD, hY, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hfun, map_add, map_add, map_smul, hcross, add_zero]

/-- Woodford (2003), p. 608: under (3.34) and (3.35) the operating target is
`i_t = (1 − ρ₁)i* + ρ₁ ī_{t−1|t} + ρ₂(ī_{t−1|t} − ī_{t−2|t}) + φπ π_{t|t}
  + (φx/4)(x_{t|t} − x_{t−1|t})` — the lagged *ideal* settings, re-estimated with date-`t`
information, not the lagged actual rates. -/
theorem eq335_expanded (𝔹 : ExpectationSystem Ω) {β κ σ lamx xs lami istar : ℝ}
    (hlami : lami ≠ 0) {π x i φ1 φ2 : ℕ → Ω → ℝ} {t : ℕ} (ht : 2 ≤ t)
    (h3 : FOC33 β σ π φ1 φ2 t) (h4 : FOC34 β κ lamx xs x φ1 φ2 t)
    (h4m : FOC34 β κ lamx xs x φ1 φ2 (t - 1)) (h32 : FOC332 𝔹 σ lami istar i φ1 t) :
    i t = (fun _ => (1 - rho1 β σ κ) * istar) + rho1 β σ κ • 𝔹.E t (ibar σ lami istar φ1 (t - 1))
      + rho2 β • (𝔹.E t (ibar σ lami istar φ1 (t - 1)) - 𝔹.E t (ibar σ lami istar φ1 (t - 2)))
      + phiPi σ κ lami • 𝔹.E t (π t)
      + (phiX σ lamx lami / 4) • (𝔹.E t (x t) - 𝔹.E t (x (t - 1))) := by
  rw [(eq335_iff 𝔹 hlami t).mp h32]
  have e : ibar σ lami istar φ1 t = (fun _ => (1 - rho1 β σ κ) * istar)
      + rho1 β σ κ • ibar σ lami istar φ1 (t - 1)
      + rho2 β • (ibar σ lami istar φ1 (t - 1) - ibar σ lami istar φ1 (t - 2))
      + phiPi σ κ lami • π t + (phiX σ lamx lami / 4) • (x t - x (t - 1)) := by
    funext ω
    rw [eq334 ht h3 h4 h4m ω]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [e]
  simp only [map_add, map_sub, map_smul, 𝔹.const]

/-! ### Naive certainty equivalence is not optimal (p. 608) -/

/-- Woodford (2003), p. 608 (example): full information for the private sector on two states. -/
def fullInfo : ExpectationSystem Bool where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

/-- Woodford (2003), p. 608 (example): the uninformed average `(x(true) + x(false))/2`. -/
noncomputable def avg : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) where
  toFun := fun x _ => (x true + x false) / 2
  map_add' := fun x y => by funext; simp only [Pi.add_apply]; ring
  map_smul' := fun c x => by funext; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Woodford (2003), p. 608 (example): `avg x ω = (x(true) + x(false))/2`. -/
theorem avg_apply (x : Bool → ℝ) (ω : Bool) : avg x ω = (x true + x false) / 2 := rfl

/-- Woodford (2003), p. 608 (example): averaging twice is averaging once. -/
theorem avg_avg (x : Bool → ℝ) : avg (avg x) = avg x := by
  funext ω; simp only [avg_apply]; ring

/-- Woodford (2003), p. 608 (example): a central bank that learns the state only at date `k`:
`𝔹_t` is the uninformed average for `t < k` and full information from `k` on. -/
noncomputable def lateBank (k : ℕ) : ExpectationSystem Bool where
  E := fun t => if t < k then avg else LinearMap.id
  const := fun t c => by
    by_cases h : t < k
    · simp only [h, ↓reduceIte]; funext ω; rw [avg_apply]; ring
    · simp only [h, ↓reduceIte]; rfl
  mono := fun t x y hxy => by
    by_cases h : t < k
    · simp only [h, ↓reduceIte]
      intro ω
      simp only [avg_apply]
      linarith [hxy true, hxy false]
    · simp only [h, ↓reduceIte]; exact hxy
  tower := fun {s t} hst x => by
    by_cases hs : s < k
    · by_cases ht : t < k
      · simp only [hs, ht, ↓reduceIte, avg_avg]
      · simp only [hs, ht, ↓reduceIte]; rfl
    · have ht : ¬ t < k := by omega
      simp only [hs, ht, ↓reduceIte]; rfl
  known := fun {s t} hst x => by
    by_cases ht : t < k
    · have hs : s < k := by omega
      simp only [hs, ht, ↓reduceIte, avg_avg]
    · simp only [ht, ↓reduceIte]; rfl

/-- Woodford (2003), p. 608 (example): the late-learning bank knows less than a fully
informed private sector. -/
theorem lateBank_nested (k : ℕ) : Nested fullInfo (lateBank k) := fun _ _ => ⟨rfl, rfl⟩

/-- Woodford (2003), p. 608 (**naive certainty equivalence fails**): for any coefficients with
`ρ₁ + ρ₂ ≠ 0` there is an economy (two states; the private sector fully informed; the bank learning
the state only at date 2) and an ideal-setting process `ī` obeying (3.34) at `t = 2` such that,
with the optimal settings `i_s = ī_{s|s}` (3.35), the naive rule
`(1 − ρ₁)i* + ρ₁i_{1} + ρ₂(i_{1} − i_{0}) + φπ π_{2|2} + (φx/4)(x_{2|2} − x_{1|2})` prescribes a
different date-2 setting from the optimal one. -/
theorem naive_rule_not_optimal (ρ1 ρ2 φπ φx : ℝ) (hρ : ρ1 + ρ2 ≠ 0) :
    ∃ (ib π x : ℕ → Bool → ℝ) (ω : Bool),
      (∀ ω', ib 2 ω' = (1 - ρ1) * 0 + ρ1 * ib 1 ω' + ρ2 * (ib 1 ω' - ib 0 ω') + φπ * π 2 ω'
        + φx * (x 2 ω' - x 1 ω') / 4) ∧
      (1 - ρ1) * 0 + ρ1 * (lateBank 2).E 1 (ib 1) ω
          + ρ2 * ((lateBank 2).E 1 (ib 1) ω - (lateBank 2).E 0 (ib 0) ω)
          + φπ * (lateBank 2).E 2 (π 2) ω
          + φx / 4 * ((lateBank 2).E 2 (x 2) ω - (lateBank 2).E 2 (x 1) ω) ≠
        (lateBank 2).E 2 (ib 2) ω := by
  refine ⟨fun s ω => if s = 1 then (if ω then 1 else 0)
      else if s = 2 then (ρ1 + ρ2) * (if ω then 1 else 0) else 0, 0, 0, false, ?_, ?_⟩
  · intro ω'
    simp only [Pi.zero_apply]
    split_ifs <;> simp_all
  · change (1 - ρ1) * 0 + ρ1 * avg _ false + ρ2 * (avg _ false - avg _ false) + φπ * 0
        + φx / 4 * (0 - 0) ≠ _
    simp only [avg_apply]
    change _ ≠ (ρ1 + ρ2) * (if false = true then 1 else 0)
    norm_num
    intro h
    apply hρ
    linarith

end Woodford.OptimalPolicyRules.ImperfectInfo
