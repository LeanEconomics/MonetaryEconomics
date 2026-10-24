/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflTargetPredetermined
import OptimalPolicyRules.IRuleBasic
import OptimalPolicyRules.CubicRoots

/-!
# Optimal interest-rate rules with predetermined spending and pricing decisions

Woodford (2003), *Interest and Prices*, Chapter 8, §3.3, pp. 604–606: eqs. (3.28)–(3.31), and
the `γ = 0` case on p. 606.

Spending and pricing decisions are predetermined `d` periods in advance and the loss includes the
interest-rate term of (3.14). The first-order conditions are (3.28) together with (3.4)–(3.5) with
`φ_{i,t−d}` in place of `φ_{it}`.

The key device is the **delayed expectation system** `delay 𝔼 d`, with `E'_t = E_{t−d}`. It
satisfies all the axioms of an `ExpectationSystem` (`delay`), so every theorem of §3.2 proved for an
arbitrary expectation system applies to it; this module shows that the predetermined problem is
exactly the §3.2 problem for `delay 𝔼 d` ("identical to (3.16) except for the conditioning
information set", p. 605).

## Main results

* `eq329_cleared`, `eq329`: eliminating the multipliers from (3.28), (3.4'), (3.5') gives the
  Euler equation (3.29), `A₁(L)î_t + βγ E_{t−d} î_{t+1} = −E_{t−d} f_t`, with `A(L) = βγ + L A₁(L)`
  the cubic (3.17) and `f`, `q̃` from (3.18)–(3.19).
* `i_predetermined` (from (3.5')) and `i_predetermined_of_eq329` (by induction from (3.29), as the
  book argues): under a timelessly optimal policy `i_t` depends only on date-`(t−d)` information,
  i.e. (2.34) holds.
* `eq316_delay`: taking `E_{t−d}` of (3.29) gives `E_{t−d}[A(L) î_{t+1}] = −E_{t−d} f_t`, which is
  literally (3.16) for the expectation system `delay 𝔼 d`.
* `Fw_delay`, `rule330_iff`, `target331_iff`: the rules (3.25)/(3.27) for `delay 𝔼 d` are exactly
  the book's (3.30)/(3.31) (`E_{t−d}` applied to the forecasts `F_t`, by the law of iterated
  expectations).
* p. 606: `rule37_of_foc_gamma0` (with `γ = 0` the delayed FOCs give the rule (3.7) with the
  coefficients (3.8)–(3.9) unchanged) and `rule330_gamma0_iff` (with weights only on the current
  period, (3.30) is (3.7) because `π_t`, `x_t` are known at `t − d`).

The equivalence of (3.16) with the rules (3.25)/(3.27) for an arbitrary expectation system is
Propositions 8.8–8.11 (§3.2, App. G.7–G.10), which belong to another module; applied to
`delay 𝔼 d` they give the equivalence of (3.29) (projected) with (3.30)/(3.31).
-/

namespace Woodford.OptimalPolicyRules.IRulePredetermined

open Filter Topology
open InflTargetPredetermined (qd qd_apply Predet)
open CubicRoots (coefA1 coefA2 coefA3)
open IRuleBasic (rho1 rho2 phiPi phiX)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The delayed expectation system -/

/-- Woodford (2003), p. 605: the expectation system `E'_t = E_{t−d}` of an economy in which
decisions are predetermined `d` periods in advance (with `E'_t = E_0` for `t < d`). It is a genuine
`ExpectationSystem` because `t ↦ t − d` is monotone. -/
def delay (d : ℕ) : ExpectationSystem Ω where
  E := fun t => 𝔼.E (t - d)
  const := fun t c => 𝔼.const (t - d) c
  mono := fun t _ _ h => 𝔼.mono (t - d) h
  tower := fun h x => 𝔼.tower (Nat.sub_le_sub_right h d) x
  known := fun h x => 𝔼.known (Nat.sub_le_sub_right h d) x

/-- Woodford (2003), p. 605: `E'_t = E_{t−d}` for the delayed system. -/
@[simp] theorem delay_E (d t : ℕ) (x : Ω → ℝ) : (delay 𝔼 d).E t x = 𝔼.E (t - d) x := rfl

/-! ### First-order conditions (3.28), (3.4'), (3.5') -/

/-- Woodford (2003), eq. (3.28), p. 605:
`π^{qd}_t − βγ E_{t−d} π^{qd}_{t+1} − β⁻¹σ φ_{1,t−d−1} − βγ E_{t−d} φ_{2,t−d+1}
  + (1 + βγ) φ_{2,t−d} − φ_{2,t−d−1} = 0`. -/
def FOC328 (β γ σ : ℝ) (d : ℕ) (π φ1 φ2 : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, qd γ π t ω - β * γ * 𝔼.E (t - d) (qd γ π (t + 1)) ω - β⁻¹ * σ * φ1 (t - d - 1) ω
    - β * γ * 𝔼.E (t - d) (φ2 (t - d + 1)) ω + (1 + β * γ) * φ2 (t - d) ω - φ2 (t - d - 1) ω = 0

/-- Woodford (2003), eq. (3.4) with `φ_{i,t−d}` (p. 605):
`λx(x_t − x*) + φ_{1,t−d} − β⁻¹ φ_{1,t−d−1} − κ φ_{2,t−d} = 0`. -/
def FOC34 (β κ lamx xs : ℝ) (d : ℕ) (x φ1 φ2 : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, lamx * (x t ω - xs) + φ1 (t - d) ω - β⁻¹ * φ1 (t - d - 1) ω - κ * φ2 (t - d) ω = 0

/-- Woodford (2003), eq. (3.5) with `φ_{1,t−d}` (p. 605): `λᵢ(i_t − i*) + σ φ_{1,t−d} = 0`. -/
def FOC35 (σ lami istar : ℝ) (d : ℕ) (i φ1 : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, lami * (i t ω - istar) + σ * φ1 (t - d) ω = 0

/-- Woodford (2003), eq. (3.19), p. 593: `q̃_t = (κσ/λᵢ)[π^{qd}_t + (λx/κ)Δx_t]`. -/
noncomputable def qtil (κ σ lami lamx γ : ℝ) (π x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => κ * σ / lami * (qd γ π t ω + lamx / κ * (x t ω - x (t - 1) ω))

/-- Woodford (2003), (3.28)–(3.29), p. 605 (**elimination of the multipliers, cleared of
denominators**): if (3.5') holds at `t − 2, …, t + 1`, (3.4') at `t − 1, t, t + 1` and (3.28) at `t`
(with `t ≥ d + 2`, the multiplier `φ₁` known at its date and `x` predetermined), then
`λᵢ[a₁î_t + a₂î_{t−1} + a₃î_{t−2} + βγ E_{t−d} î_{t+1}]
  + σ[κπ^{qd}_t + λxΔx_t − βγ(κ E_{t−d}π^{qd}_{t+1} + λx(E_{t−d}x_{t+1} − x_t))] = 0`. -/
theorem eq329_cleared {β γ κ σ lamx xs lami istar : ℝ} (hβ : β ≠ 0) {d t : ℕ} (ht : d + 2 ≤ t)
    {π x i φ1 φ2 : ℕ → Ω → ℝ}
    (h28 : FOC328 𝔼 β γ σ d π φ1 φ2 t)
    (h4m : FOC34 β κ lamx xs d x φ1 φ2 (t - 1)) (h4 : FOC34 β κ lamx xs d x φ1 φ2 t)
    (h4p : FOC34 β κ lamx xs d x φ1 φ2 (t + 1))
    (h5mm : FOC35 σ lami istar d i φ1 (t - 2)) (h5m : FOC35 σ lami istar d i φ1 (t - 1))
    (h5 : FOC35 σ lami istar d i φ1 t) (h5p : FOC35 σ lami istar d i φ1 (t + 1))
    (hφ1 : 𝔼.E (t - d) (φ1 (t - d)) = φ1 (t - d)) (ω : Ω) :
    lami * (coefA1 β γ * (i t ω - istar) + coefA2 β γ κ σ * (i (t - 1) ω - istar)
      + coefA3 β * (i (t - 2) ω - istar) + β * γ * (𝔼.E (t - d) (i (t + 1)) ω - istar))
    + σ * (κ * qd γ π t ω + lamx * (x t ω - x (t - 1) ω)
      - β * γ * (κ * 𝔼.E (t - d) (qd γ π (t + 1)) ω + lamx * (𝔼.E (t - d) (x (t + 1)) ω
        - x t ω))) = 0 := by
  have i1 : t - 1 - d = t - d - 1 := by omega
  have i2 : t - 1 - d - 1 = t - d - 2 := by omega
  have i3 : t - 2 - d = t - d - 2 := by omega
  have i4 : t + 1 - d = t - d + 1 := by omega
  have i5 : t + 1 - d - 1 = t - d := by omega
  -- the date-(t+1) conditions hold as equalities of random variables; take `E_{t−d}`
  have e4p : (fun ω' => lamx * (x (t + 1) ω' - xs) + φ1 (t - d + 1) ω' - β⁻¹ * φ1 (t - d) ω'
      - κ * φ2 (t - d + 1) ω') = 0 := by
    funext ω'; have := h4p ω'; rw [i5, i4] at this; simpa using this
  have e5p : (fun ω' => lami * (i (t + 1) ω' - istar) + σ * φ1 (t - d + 1) ω') = 0 := by
    funext ω'; have := h5p ω'; rw [i4] at this; simpa using this
  have E4 : lamx * (𝔼.E (t - d) (x (t + 1)) ω - xs) + 𝔼.E (t - d) (φ1 (t - d + 1)) ω
      - β⁻¹ * φ1 (t - d) ω - κ * 𝔼.E (t - d) (φ2 (t - d + 1)) ω = 0 := by
    have hfun : (fun ω' => lamx * (x (t + 1) ω' - xs) + φ1 (t - d + 1) ω' - β⁻¹ * φ1 (t - d) ω'
        - κ * φ2 (t - d + 1) ω') = lamx • (x (t + 1) - fun _ => xs) + φ1 (t - d + 1)
          - β⁻¹ • φ1 (t - d) - κ • φ2 (t - d + 1) := by
      funext ω'; simp
    have := congrFun (congrArg (𝔼.E (t - d)) e4p) ω
    rw [hfun, map_zero] at this
    simp only [map_sub, map_add, map_smul, 𝔼.const, hφ1, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this
  have E5 : lami * (𝔼.E (t - d) (i (t + 1)) ω - istar) + σ * 𝔼.E (t - d) (φ1 (t - d + 1)) ω
      = 0 := by
    have hfun : (fun ω' => lami * (i (t + 1) ω' - istar) + σ * φ1 (t - d + 1) ω') =
        lami • (i (t + 1) - fun _ => istar) + σ • φ1 (t - d + 1) := by
      funext ω'; simp
    have := congrFun (congrArg (𝔼.E (t - d)) e5p) ω
    rw [hfun, map_zero] at this
    simp only [map_sub, map_add, map_smul, 𝔼.const, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    exact this
  have f28 := h28 ω
  have f4m := h4m ω
  rw [i2, i1] at f4m
  have f4 := h4 ω
  have f5mm := h5mm ω
  rw [i3] at f5mm
  have f5m := h5m ω
  rw [i1] at f5m
  have f5 := h5 ω
  have hb : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  simp only [coefA1, coefA2, coefA3]
  linear_combination σ * κ * f28 + σ * (1 + β * γ) * f4 - σ * f4m - σ * β * γ * E4
    - (1 + β * γ + γ) * f5 + (σ * κ * β⁻¹ + β⁻¹ + γ + 1) * f5m - β⁻¹ * f5mm + β * γ * E5
    + σ * γ * (φ1 (t - d - 1) ω - φ1 (t - d) ω) * hb

/-- Woodford (2003), eq. (3.29), p. 605: in the book's normalisation (`λᵢ, κ, σ ≠ 0`),
`A₁(L)(i_t − i*) + βγ E_{t−d}(i_{t+1} − i*) = −E_{t−d} f_t`, where `A₁(L) = a₁ + a₂L + a₃L²` and
`E_{t−d} f_t = q̃_t − βγ E_{t−d} q̃_{t+1}` ((3.18)–(3.19); `q̃_t` is known at `t − d`). -/
theorem eq329 {β γ κ σ lamx xs lami istar : ℝ} (hβ : β ≠ 0) (hκ : κ ≠ 0) (hlami : lami ≠ 0)
    {d t : ℕ} (ht : d + 2 ≤ t) {π x i φ1 φ2 : ℕ → Ω → ℝ}
    (h28 : FOC328 𝔼 β γ σ d π φ1 φ2 t)
    (h4m : FOC34 β κ lamx xs d x φ1 φ2 (t - 1)) (h4 : FOC34 β κ lamx xs d x φ1 φ2 t)
    (h4p : FOC34 β κ lamx xs d x φ1 φ2 (t + 1))
    (h5mm : FOC35 σ lami istar d i φ1 (t - 2)) (h5m : FOC35 σ lami istar d i φ1 (t - 1))
    (h5 : FOC35 σ lami istar d i φ1 t) (h5p : FOC35 σ lami istar d i φ1 (t + 1))
    (hφ1 : 𝔼.E (t - d) (φ1 (t - d)) = φ1 (t - d)) (hx : 𝔼.E (t - d) (x t) = x t) (ω : Ω) :
    coefA1 β γ * (i t ω - istar) + coefA2 β γ κ σ * (i (t - 1) ω - istar)
      + coefA3 β * (i (t - 2) ω - istar)
      + β * γ * (𝔼.E (t - d) (i (t + 1)) ω - istar) =
    -(qtil κ σ lami lamx γ π x t ω - β * γ * 𝔼.E (t - d) (qtil κ σ lami lamx γ π x (t + 1)) ω) := by
  have hc := eq329_cleared 𝔼 hβ ht h28 h4m h4 h4p h5mm h5m h5 h5p hφ1 ω
  have hq : qtil κ σ lami lamx γ π x (t + 1) =
      (κ * σ / lami) • (qd γ π (t + 1) + (lamx / κ) • (x (t + 1) - x t)) := by
    funext ω'; simp [qtil]
  rw [hq, map_smul, map_add, map_smul, map_sub, hx]
  simp only [qtil, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  linear_combination hc

/-- Woodford (2003), p. 605 (with (2.34)): under (3.5') with `λᵢ ≠ 0` and a multiplier known at its
date, the interest rate `i_t` depends only on information at date `t − d`. -/
theorem i_predetermined {σ lami istar : ℝ} (hlami : lami ≠ 0) {d t : ℕ} {i φ1 : ℕ → Ω → ℝ}
    (h5 : FOC35 σ lami istar d i φ1 t) (hφ1 : 𝔼.E (t - d) (φ1 (t - d)) = φ1 (t - d)) :
    𝔼.E (t - d) (i t) = i t := by
  have e : i t = (fun _ => istar) - (σ / lami) • φ1 (t - d) := by
    funext ω
    have := h5 ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    linarith
  rw [e, map_sub, map_smul, 𝔼.const, hφ1]

/-- Woodford (2003), p. 605 ("it follows from this [(3.29)]"): if (3.29) holds at every date
`t ≥ T` (`T ≥ d + 2`), `a₁ ≠ 0`, and the two initial rates `i_{T−1}, i_{T−2}` are known at dates
`T − 1 − d`, `T − 2 − d`, then every `i_t` (`t ≥ T − 2`) is known at date `t − d`. -/
theorem i_predetermined_of_eq329 {β γ κ σ lami lamx istar : ℝ} (ha1 : coefA1 β γ ≠ 0) {d T : ℕ}
    (hT : d + 2 ≤ T) {π x i : ℕ → Ω → ℝ}
    (h329 : ∀ t, T ≤ t → ∀ ω, coefA1 β γ * (i t ω - istar) + coefA2 β γ κ σ * (i (t - 1) ω - istar)
      + coefA3 β * (i (t - 2) ω - istar) + β * γ * (𝔼.E (t - d) (i (t + 1)) ω - istar) =
      -(qtil κ σ lami lamx γ π x t ω - β * γ * 𝔼.E (t - d) (qtil κ σ lami lamx γ π x (t + 1)) ω))
    (hq : ∀ t, T ≤ t → 𝔼.E (t - d) (qtil κ σ lami lamx γ π x t) = qtil κ σ lami lamx γ π x t)
    (h1 : 𝔼.E (T - 1 - d) (i (T - 1)) = i (T - 1)) (h2 : 𝔼.E (T - 2 - d) (i (T - 2)) = i (T - 2))
    (n : ℕ) : 𝔼.E (T - 2 + n - d) (i (T - 2 + n)) = i (T - 2 + n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using h2
    | 1 => rw [show T - 2 + 1 = T - 1 by omega]; exact h1
    | k + 2 =>
      set t := T - 2 + (k + 2) with htdef
      have ht : T ≤ t := by omega
      have hk1 := ih (k + 1) (by omega)
      have hk0 := ih k (by omega)
      rw [show T - 2 + (k + 1) = t - 1 by omega] at hk1
      rw [show T - 2 + k = t - 2 by omega] at hk0
      have k1 : 𝔼.E (t - d) (i (t - 1)) = i (t - 1) :=
        ForwardSolution.E_of_known 𝔼 (by omega : t - 1 - d ≤ t - d) hk1
      have k0 : 𝔼.E (t - d) (i (t - 2)) = i (t - 2) :=
        ForwardSolution.E_of_known 𝔼 (by omega : t - 2 - d ≤ t - d) hk0
      -- solve (3.29) for `i_t`
      have e : i t = (coefA1 β γ)⁻¹ • (-(qtil κ σ lami lamx γ π x t
          - (β * γ) • 𝔼.E (t - d) (qtil κ σ lami lamx γ π x (t + 1)))
          - coefA2 β γ κ σ • (i (t - 1) - fun _ => istar) - coefA3 β • (i (t - 2) - fun _ => istar)
          - (β * γ) • (𝔼.E (t - d) (i (t + 1)) - fun _ => istar)) + fun _ => istar := by
        funext ω
        have := h329 t ht ω
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        field_simp
        linarith
      rw [e]
      simp only [map_add, map_sub, map_neg, map_smul, 𝔼.const, hq t ht, k1, k0, 𝔼.E_E_self]

/-! ### Taking `E_{t−d}`: the Euler equation (3.16) for the delayed system -/

/-- Woodford (2003), eq. (3.16), p. 592, for an arbitrary expectation system `𝔼'`:
`E'_t[A(L)(i_{t+1} − i*)] = −f_t` with `f_t = q̃_t − βγ E'_t q̃_{t+1}` (3.18). -/
def Euler316 (𝔼' : ExpectationSystem Ω) (β γ κ σ lami lamx istar : ℝ) (π x i : ℕ → Ω → ℝ)
    (t : ℕ) : Prop :=
  𝔼'.E t ((β * γ) • (i (t + 1) - fun _ => istar) + coefA1 β γ • (i t - fun _ => istar)
      + coefA2 β γ κ σ • (i (t - 1) - fun _ => istar) + coefA3 β • (i (t - 2) - fun _ => istar)) =
    -(qtil κ σ lami lamx γ π x t - (β * γ) • 𝔼'.E t (qtil κ σ lami lamx γ π x (t + 1)))

/-- Woodford (2003), p. 605 (**(3.29) is (3.16) with the delayed information set**): if (3.29)
holds at `t`, `i_t, i_{t−1}, i_{t−2}` are known at `t − d` and `q̃_t` is known at `t − d`, then
`E_{t−d}[A(L) î_{t+1}] = −E_{t−d} f_t`, which is (3.16) for the expectation system `delay 𝔼 d`. -/
theorem eq316_delay {β γ κ σ lami lamx istar : ℝ} {d t : ℕ} {π x i : ℕ → Ω → ℝ}
    (h329 : ∀ ω, coefA1 β γ * (i t ω - istar) + coefA2 β γ κ σ * (i (t - 1) ω - istar)
      + coefA3 β * (i (t - 2) ω - istar) + β * γ * (𝔼.E (t - d) (i (t + 1)) ω - istar) =
      -(qtil κ σ lami lamx γ π x t ω - β * γ * 𝔼.E (t - d) (qtil κ σ lami lamx γ π x (t + 1)) ω))
    (k0 : 𝔼.E (t - d) (i t) = i t) (k1 : 𝔼.E (t - d) (i (t - 1)) = i (t - 1))
    (k2 : 𝔼.E (t - d) (i (t - 2)) = i (t - 2)) :
    Euler316 (delay 𝔼 d) β γ κ σ lami lamx istar π x i t := by
  unfold Euler316
  simp only [delay_E, map_add, map_sub, map_smul, 𝔼.const, k0, k1, k2]
  funext ω
  have := h329 ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  linarith

/-! ### The rules (3.30)–(3.31) are (3.25)/(3.27) for the delayed system -/

/-- Woodford (2003), (3.25), p. 597: the forecast combination `F_t(z) = ∑_{j ≥ 0} α_j E_t z_{t+j}`
for an expectation system `𝔼'`. -/
noncomputable def Fw (𝔼' : ExpectationSystem Ω) (α : ℕ → ℝ) (z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, α j * 𝔼'.E t (z (t + j)) ω

/-- Woodford (2003), p. 606 (**law of iterated expectations for the forecasts**): for the delayed
system, `F'_t(z) = E_{t−d} F_t(z)` (absolutely summable weights, bounded `z`). -/
theorem Fw_delay {α : ℕ → ℝ} (hα : Summable (fun j => |α j|)) {z : ℕ → Ω → ℝ}
    (hz : BoundedProc z) (d t : ℕ) : Fw (delay 𝔼 d) α z t = 𝔼.E (t - d) (Fw 𝔼 α z t) := by
  obtain ⟨M, hM⟩ := hz
  funext ω
  have hf : ∀ j ω', |α j * 𝔼.E t (z (t + j)) ω'| ≤ |α j| * M := fun j ω' => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hM _) t ω') (abs_nonneg _)
  have h := ForwardSolution.E_tsum_dom 𝔼 (hα.mul_right M) hf (t - d) ω
  unfold Fw
  rw [h]
  refine tsum_congr fun j => ?_
  change α j * 𝔼.E (t - d) (z (t + j)) ω = 𝔼.E (t - d) (α j • 𝔼.E t (z (t + j))) ω
  rw [map_smul, 𝔼.tower (by omega : t - d ≤ t)]
  rfl

/-- Woodford (2003), eq. (3.25), p. 597, for an expectation system `𝔼'`:
`i_t = (1 − ρ₁)i* + ρ₁i_{t−1} + ρ₂Δi_{t−1} + φπ F_t(π) + (φx/4)F_t(x)
  − θπ π_{t−1} − (θx/4)x_{t−1}`. -/
def Rule325 (𝔼' : ExpectationSystem Ω) (ρ1 ρ2 φπ φx θπ θx istar : ℝ) (απ αx : ℕ → ℝ)
    (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t = (fun _ => (1 - ρ1) * istar) + ρ1 • i (t - 1) + ρ2 • (i (t - 1) - i (t - 2)) +
    φπ • Fw 𝔼' απ π t + (φx / 4) • Fw 𝔼' αx x t - θπ • π (t - 1) - (θx / 4) • x (t - 1)

/-- Woodford (2003), eq. (3.30), p. 606: the rule (3.25) with the projections conditioned on
date-`(t − d)` information, `… + φπ E_{t−d}F_t(π) + (φx/4) E_{t−d}F_t(x) − …`. -/
def Rule330 (ρ1 ρ2 φπ φx θπ θx istar : ℝ) (απ αx : ℕ → ℝ) (d : ℕ) (π x i : ℕ → Ω → ℝ)
    (t : ℕ) : Prop :=
  i t = (fun _ => (1 - ρ1) * istar) + ρ1 • i (t - 1) + ρ2 • (i (t - 1) - i (t - 2)) +
    φπ • 𝔼.E (t - d) (Fw 𝔼 απ π t) + (φx / 4) • 𝔼.E (t - d) (Fw 𝔼 αx x t) - θπ • π (t - 1)
      - (θx / 4) • x (t - 1)

/-- Woodford (2003), p. 606: (3.25) for the delayed expectation system is exactly (3.30). -/
theorem rule330_iff {ρ1 ρ2 φπ φx θπ θx istar : ℝ} {απ αx : ℕ → ℝ}
    (hαπ : Summable (fun j => |απ j|)) (hαx : Summable (fun j => |αx j|)) {d : ℕ}
    {π x i : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) (t : ℕ) :
    Rule325 (delay 𝔼 d) ρ1 ρ2 φπ φx θπ θx istar απ αx π x i t ↔
      Rule330 𝔼 ρ1 ρ2 φπ φx θπ θx istar απ αx d π x i t := by
  unfold Rule325 Rule330
  rw [Fw_delay 𝔼 hαπ hπ, Fw_delay 𝔼 hαx hx]

/-- Woodford (2003), eq. (3.27), p. 601, for an expectation system `𝔼'`:
`F_t(π) + (φx/4)F_t(x) = θπ π_{t−1} + (θx/4)x_{t−1} − θᵢ(i_{t−1} − i*) − θ_Δ Δi_{t−1}`. -/
def Target327 (𝔼' : ExpectationSystem Ω) (φx θπ θx θi θΔ istar : ℝ) (απ αx : ℕ → ℝ)
    (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  Fw 𝔼' απ π t + (φx / 4) • Fw 𝔼' αx x t = θπ • π (t - 1) + (θx / 4) • x (t - 1)
    - θi • (i (t - 1) - fun _ => istar) - θΔ • (i (t - 1) - i (t - 2))

/-- Woodford (2003), eq. (3.31), p. 606: `E_{t−d}F_t(π) + (φx/4)E_{t−d}F_t(x) = …` (the right side
as in (3.27)). -/
def Target331 (φx θπ θx θi θΔ istar : ℝ) (απ αx : ℕ → ℝ) (d : ℕ) (π x i : ℕ → Ω → ℝ)
    (t : ℕ) : Prop :=
  𝔼.E (t - d) (Fw 𝔼 απ π t) + (φx / 4) • 𝔼.E (t - d) (Fw 𝔼 αx x t) =
    θπ • π (t - 1) + (θx / 4) • x (t - 1) - θi • (i (t - 1) - fun _ => istar)
      - θΔ • (i (t - 1) - i (t - 2))

/-- Woodford (2003), p. 606: the target criterion (3.27) for the delayed expectation system is
exactly (3.31). -/
theorem target331_iff {φx θπ θx θi θΔ istar : ℝ} {απ αx : ℕ → ℝ}
    (hαπ : Summable (fun j => |απ j|)) (hαx : Summable (fun j => |αx j|)) {d : ℕ}
    {π x i : ℕ → Ω → ℝ} (hπ : BoundedProc π) (hx : BoundedProc x) (t : ℕ) :
    Target327 (delay 𝔼 d) φx θπ θx θi θΔ istar απ αx π x i t ↔
      Target331 𝔼 φx θπ θx θi θΔ istar απ αx d π x i t := by
  unfold Target327 Target331
  rw [Fw_delay 𝔼 hαπ hπ, Fw_delay 𝔼 hαx hx]

/-! ### The case `γ = 0` (p. 606) -/

/-- Woodford (2003), eq. (3.7), p. 584:
`i_t = (1 − ρ₁)i* + ρ₁i_{t−1} + ρ₂Δi_{t−1} + φπ π_t + φx Δx_t/4`. -/
def Rule37 (ρ1 ρ2 φπ φx istar : ℝ) (π x i : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, i t ω = (1 - ρ1) * istar + ρ1 * i (t - 1) ω + ρ2 * (i (t - 1) ω - i (t - 2) ω)
    + φπ * π t ω + φx * (x t ω - x (t - 1) ω) / 4

/-- Woodford (2003), p. 606 (**`γ = 0` with delays: no change in the optimal rule**): with
`γ = 0` the delayed first-order conditions imply the instrument rule (3.7) with exactly the
coefficients (3.8)–(3.9) at every date `t ≥ d + 2`. -/
theorem rule37_of_foc_gamma0 {β κ σ lamx xs lami istar : ℝ} (hβ : β ≠ 0) (hlami : lami ≠ 0)
    {d t : ℕ} (ht : d + 2 ≤ t) {π x i φ1 φ2 : ℕ → Ω → ℝ}
    (h28 : FOC328 𝔼 β 0 σ d π φ1 φ2 t)
    (h4m : FOC34 β κ lamx xs d x φ1 φ2 (t - 1)) (h4 : FOC34 β κ lamx xs d x φ1 φ2 t)
    (h4p : FOC34 β κ lamx xs d x φ1 φ2 (t + 1))
    (h5mm : FOC35 σ lami istar d i φ1 (t - 2)) (h5m : FOC35 σ lami istar d i φ1 (t - 1))
    (h5 : FOC35 σ lami istar d i φ1 t) (h5p : FOC35 σ lami istar d i φ1 (t + 1))
    (hφ1 : 𝔼.E (t - d) (φ1 (t - d)) = φ1 (t - d)) :
    Rule37 (rho1 β σ κ) (rho2 β) (phiPi σ κ lami) (phiX σ lamx lami) istar π x i t := by
  intro ω
  have hc := eq329_cleared 𝔼 hβ ht h28 h4m h4 h4p h5mm h5m h5 h5p hφ1 ω
  simp only [coefA1, coefA2, coefA3, qd_apply, mul_zero, zero_mul, sub_zero, add_zero] at hc
  have hb : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ
  simp only [rho1, rho2, phiPi, phiX]
  field_simp
  linear_combination (-β) * hc
    + lami * (κ * σ * (i (t - 1) ω - istar) + i (t - 1) ω - i (t - 2) ω) * hb

/-- Woodford (2003), p. 606: with forecast weights only on the current period
(`α₀ = 1`, `α_j = 0` for `j > 0`) and `θπ = 0`, rule (3.30) is rule (3.7) — because `π_t` and `x_t`
are known at date `t − d`. -/
theorem rule330_gamma0_iff {ρ1 ρ2 φπ φx θx istar : ℝ} {d t : ℕ} {π x i : ℕ → Ω → ℝ}
    (hπt : 𝔼.E (t - d) (π t) = π t) (hxt : 𝔼.E (t - d) (x t) = x t) (hθx : θx = φx) :
    Rule330 𝔼 ρ1 ρ2 φπ φx 0 θx istar (fun j => if j = 0 then 1 else 0)
        (fun j => if j = 0 then 1 else 0) d π x i t ↔
      Rule37 ρ1 ρ2 φπ φx istar π x i t := by
  have hF : ∀ z : ℕ → Ω → ℝ, Fw 𝔼 (fun j => if j = 0 then 1 else 0) z t = 𝔼.E t (z t) := by
    intro z
    funext ω
    unfold Fw
    rw [tsum_eq_single 0 (fun j hj => by simp [hj])]
    simp
  have hEπ : 𝔼.E (t - d) (𝔼.E t (π t)) = π t := by rw [𝔼.tower (by omega), hπt]
  have hEx : 𝔼.E (t - d) (𝔼.E t (x t)) = x t := by rw [𝔼.tower (by omega), hxt]
  unfold Rule330 Rule37
  rw [hF, hF, hEπ, hEx, hθx]
  constructor
  · intro h ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_mul, sub_zero] at this
    rw [this]
    ring
  · intro h
    funext ω
    rw [h ω]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_mul, sub_zero]
    ring

end Woodford.OptimalPolicyRules.IRulePredetermined
