/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6RotembergGlobal
import KeynesianStickyPrices.TidyR6CalvoReset

/-!
# Near the steady state the Rotemberg first-order condition is globally sufficient

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.1, p. 118 ("The Phillips
curve (5.2) comes from the first-order condition for monopolistically-competitive price setters,
facing costs of changing prices"), and eq. (17.17), p. 407.

TidyR6RotembergGlobal shows that the first-order condition is not sufficient in general (a deep
deflation). This module decides the local question **positively**: for data close enough to the
zero-inflation steady state, charging the aggregate price is optimal among **all** plans as soon
as it satisfies the first-order condition.

## The argument

With `f(a) = Ae^{(1−ε)a} − Be^{−ηa}` (the static payoff, `TidyR6CalvoReset.gRes`) and the price
change cost `C(d) = (φ/2)(e^{d+π} − 1)²` (`cC`), the period payoff is `f(a) − C(a − b)`
(`rot_eq`). Add the bounded potential `h_t s(q_t) − g_t s(q_{t−1})` with the clamp
`s = max(−R, min(·, R))` (`clampR`), `g_t = C_t′(0)` and `h_t = βE_tg_{t+1}`; it telescopes, so it
does not change values (up to a vanishing terminal term). The first-order condition is
`h_t = g_t − f_t′(0)`, and then the modified payoff has a **global** maximum at `(0, 0)`
(`pot_le`) under explicit conditions: strong concavity of `f` on `[−R, R]` (`cS > 0`,
`static_strong`), strong convexity of `C` on `[−2R, 2R]` (`cP > 0`, `cost_strong`), static loss
outside `[−R, R]` (`static_outside`), cost growth outside `[−2R, 2R]` (`cost_outside`), and the
smallness of `f′(0)` and `g`.

## Main results

* `pot_le`: the pointwise global inequality.
* `optimal_of_pot` (**verification theorem**): if the first-order condition holds and the
  conditions hold at every date almost surely, charging the aggregate price is optimal among all
  plans (`TidyR6PriceSetting.Plan`).
* `near_ss`: at the steady state (`(1 − ε)Ā + ηB̄ = 0`, `π = 0`) the conditions hold strictly for
  some `R > 0` (chosen by continuity at `R = 0`), hence on a neighbourhood: there is `ρ > 0` such
  that data within `ρ` of `(Ā, B̄, 0)` satisfy them.
* `optimal_near_ss`: **local global sufficiency**: there is `ρ > 0` such that, whenever the data
  stay within `ρ` of the steady state at every date almost surely and charging the aggregate
  price satisfies the first-order condition, it is optimal among all plans.
* `optimal_near_ss_yeo`: the same for the symmetric equilibrium of (17.15)–(17.17): output gap and
  inflation in `(−ρ, ρ)` plus the exact nonlinear Phillips curve give optimality among all plans.

The radius `ρ` is existential (continuity), not explicit. Far from the steady state the answer
is negative (`TidyR6RotembergGlobal.cex_not_optimal`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6RotembergLocal

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6PriceSetting TidyR6Rotemberg TidyR6CalvoReset
open TidyR6RotembergPC

/-! ### One-variable estimates -/

/-- Cochrane (2023), p. 118: the cost of changing the price, `C(d) = (φ/2)(e^{d+π} − 1)²`. -/
noncomputable def cC (φ π d : ℝ) : ℝ := φ / 2 * (Real.exp (d + π) - 1) ^ 2

/-- Cochrane (2023), p. 118: the marginal cost of a price change at zero,
`g = C′(0) = φ(e^π − 1)e^π`. -/
noncomputable def gC (φ π : ℝ) : ℝ := φ * (Real.exp π - 1) * Real.exp π

/-- Cochrane (2023), p. 118: the marginal static payoff at zero, `f′(0) = (1 − ε)A + ηB`. -/
def f1 (ε η A B : ℝ) : ℝ := (1 - ε) * A + η * B

/-- Cochrane (2023), p. 118: the curvature bound of the static payoff on `[−R, R]`,
`η²Be^{−ηR} − (ε − 1)²Ae^{(ε−1)R}`. -/
noncomputable def cS (ε η A B R : ℝ) : ℝ :=
  η ^ 2 * B * Real.exp (-(η * R)) - (ε - 1) ^ 2 * A * Real.exp ((ε - 1) * R)

/-- Cochrane (2023), p. 118: the curvature bound of the cost on `[−2R, 2R]`,
`φe^{π−2R}(2e^{π−2R} − 1)`. -/
noncomputable def cP (φ π R : ℝ) : ℝ :=
  φ * Real.exp (π - 2 * R) * (2 * Real.exp (π - 2 * R) - 1)

/-- Cochrane (2023), p. 118: the clamp `s(b) = max(−R, min(b, R))`. -/
def clampR (R b : ℝ) : ℝ := max (-R) (min b R)

/-- Cochrane (2023), p. 118: the Rotemberg payoff is `f(a) − C(a − b)`. -/
theorem rot_eq (ε η φ a b : ℝ) (v : ℝ × ℝ × ℝ) :
    rotPay ε η φ a b v = gRes ε η v.1 v.2.1 a - cC φ v.2.2 (a - b) := by
  simp only [rotPay, gRes, cC]

/-- Cochrane (2023), p. 118: a function with nonnegative derivative on an order-connected set
is monotone there. -/
theorem monotoneOn_of_deriv_nonneg' {g g' : ℝ → ℝ} {D : Set ℝ} (hD : D.OrdConnected)
    (hg : ∀ x, HasDerivAt g (g' x) x) (h : ∀ x ∈ D, 0 ≤ g' x) : MonotoneOn g D := by
  have := antitoneOn_of_deriv_nonpos' (g := fun x => -g x) (g' := fun x => -g' x) hD
    (fun x => (hg x).neg) fun x hx => by linarith [h x hx]
  intro x hx y hy hxy
  have := this hx hy hxy
  simp only at this
  linarith

/-- Cochrane (2023), p. 118: the derivative of the cost, `C′(d) = φ(e^{d+π} − 1)e^{d+π}`. -/
theorem hasDerivAt_cC (φ π d : ℝ) :
    HasDerivAt (cC φ π) (φ * (Real.exp (d + π) - 1) * Real.exp (d + π)) d := by
  have h := ((((hasDerivAt_id d).add_const π).exp.sub_const 1).pow 2).const_mul (φ / 2)
  refine h.congr_deriv ?_
  simp only [id, Nat.cast_ofNat]
  ring

/-- Cochrane (2023), p. 118: the second derivative of the cost. -/
theorem hasDerivAt_cC' (φ π d : ℝ) :
    HasDerivAt (fun d => φ * (Real.exp (d + π) - 1) * Real.exp (d + π))
      (φ * Real.exp (d + π) * (2 * Real.exp (d + π) - 1)) d := by
  have he : HasDerivAt (fun d => Real.exp (d + π)) (Real.exp (d + π)) d := by
    simpa using ((hasDerivAt_id d).add_const π).exp
  have h := ((he.sub_const 1).const_mul φ).mul he
  refine h.congr_deriv ?_
  ring

/-- Cochrane (2023), p. 118: the second derivative of the static payoff. -/
theorem hasDerivAt_gRes' (ε η A B a : ℝ) :
    HasDerivAt (fun a => A * (1 - ε) * Real.exp ((1 - ε) * a) + B * η * Real.exp (-(η * a)))
      (A * (1 - ε) ^ 2 * Real.exp ((1 - ε) * a) - B * η ^ 2 * Real.exp (-(η * a))) a := by
  have h1 : HasDerivAt (fun a => Real.exp ((1 - ε) * a)) (Real.exp ((1 - ε) * a) * (1 - ε)) a :=
    ((hasDerivAt_id a).const_mul (1 - ε)).exp.congr_deriv (by simp)
  have h2 : HasDerivAt (fun a => Real.exp (-(η * a))) (Real.exp (-(η * a)) * (-η)) a :=
    (((hasDerivAt_id a).const_mul η).neg).exp.congr_deriv (by simp)
  exact ((h1.const_mul (A * (1 - ε))).add (h2.const_mul (B * η))).congr_deriv (by ring)

/-- Cochrane (2023), p. 118, **strong concavity of the static payoff**: for `A, B ≥ 0`, `ε > 1`,
`η > 0` and `a ∈ [−R, R]`, `f(a) ≤ f(0) + f′(0)a − (cS/2)a²`, and `f′(R) + cS·R ≤ f′(0) ≤
f′(−R) − cS·R`. -/
theorem static_strong {ε η A B R : ℝ} (hε : 1 < ε) (hη : 0 < η) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∀ a, -R ≤ a → a ≤ R →
      gRes ε η A B a ≤ gRes ε η A B 0 + f1 ε η A B * a - cS ε η A B R / 2 * a ^ 2) ∧
    (0 ≤ R → A * (1 - ε) * Real.exp ((1 - ε) * R) + B * η * Real.exp (-(η * R)) +
        cS ε η A B R * R ≤ f1 ε η A B) ∧
    (0 ≤ R → f1 ε η A B ≤ A * (1 - ε) * Real.exp ((1 - ε) * -R) +
        B * η * Real.exp (-(η * -R)) - cS ε η A B R * R) := by
  set c := cS ε η A B R
  set k : ℝ → ℝ := fun a => gRes ε η A B a + c / 2 * a ^ 2
  set k' : ℝ → ℝ := fun a =>
    A * (1 - ε) * Real.exp ((1 - ε) * a) + B * η * Real.exp (-(η * a)) + c * a
  set k'' : ℝ → ℝ := fun a =>
    A * (1 - ε) ^ 2 * Real.exp ((1 - ε) * a) - B * η ^ 2 * Real.exp (-(η * a)) + c
  have hk : ∀ x, HasDerivAt k (k' x) x := fun x => by
    have := (hasDerivAt_gRes ε η A B x).add (((hasDerivAt_id x).pow 2).const_mul (c / 2))
    refine this.congr_deriv ?_
    simp only [k', id, Nat.cast_ofNat]
    ring
  have hk' : ∀ x, HasDerivAt k' (k'' x) x := fun x => by
    have := (hasDerivAt_gRes' ε η A B x).add ((hasDerivAt_id x).const_mul c)
    exact this.congr_deriv (by simp only [k'']; ring)
  have hD : (Set.Icc (-R) R).OrdConnected := Set.ordConnected_Icc
  have hneg : ∀ x ∈ Set.Icc (-R) R, k'' x ≤ 0 := by
    intro x hx
    have e1 : Real.exp ((1 - ε) * x) ≤ Real.exp ((ε - 1) * R) :=
      Real.exp_le_exp.2 (by nlinarith [hx.1])
    have e2 : Real.exp (-(η * R)) ≤ Real.exp (-(η * x)) :=
      Real.exp_le_exp.2 (by nlinarith [hx.2])
    have h1 : A * (1 - ε) ^ 2 * Real.exp ((1 - ε) * x) ≤
        (ε - 1) ^ 2 * A * Real.exp ((ε - 1) * R) := by
      have : 0 ≤ A * (1 - ε) ^ 2 := mul_nonneg hA (sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left e1 this]
    have h2 : η ^ 2 * B * Real.exp (-(η * R)) ≤ B * η ^ 2 * Real.exp (-(η * x)) := by
      have : 0 ≤ B * η ^ 2 := mul_nonneg hB (sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_left e2 this]
    simp only [k'', c, cS]
    linarith
  have hanti := antitoneOn_of_deriv_nonpos' hD hk' hneg
  have hk'0 : k' 0 = f1 ε η A B := by simp [k', f1]; ring
  have hk'R : ∀ x, k' x = A * (1 - ε) * Real.exp ((1 - ε) * x) +
      B * η * Real.exp (-(η * x)) + c * x := fun x => rfl
  refine ⟨fun a ha1 ha2 => ?_, fun hR => ?_, fun hR => ?_⟩
  · have h0 : (0 : ℝ) ∈ Set.Icc (-R) R := ⟨by linarith, by linarith⟩
    have := tangent_of_antitoneOn hD hk hanti h0 ⟨ha1, ha2⟩
    rw [hk'0] at this
    simp only [k] at this
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      sub_zero] at this
    linarith
  · have := hanti (a := 0) (b := R) ⟨by linarith, hR⟩ ⟨by linarith, le_rfl⟩ hR
    rw [hk'0, hk'R] at this
    linarith
  · have := hanti (a := -R) (b := 0) ⟨le_rfl, by linarith⟩ ⟨by linarith, hR⟩ (by linarith)
    rw [hk'0, hk'R] at this
    linarith

/-- Cochrane (2023), p. 118, **strong convexity of the cost**: if `cP > 0` (prices are not cut
by half or more), for `d ∈ [−2R, 2R]`, `C(d) ≥ C(0) + gd + (cP/2)d²`. -/
theorem cost_strong {φ π R : ℝ} (hφ : 0 < φ) (hc : 0 < cP φ π R) (d : ℝ) (hd1 : -(2 * R) ≤ d)
    (hd2 : d ≤ 2 * R) : cC φ π 0 + gC φ π * d + cP φ π R / 2 * d ^ 2 ≤ cC φ π d := by
  set c := cP φ π R
  set m : ℝ → ℝ := fun d => -cC φ π d + c / 2 * d ^ 2
  set m' : ℝ → ℝ := fun d => -(φ * (Real.exp (d + π) - 1) * Real.exp (d + π)) + c * d
  set m'' : ℝ → ℝ := fun d => -(φ * Real.exp (d + π) * (2 * Real.exp (d + π) - 1)) + c
  have hm : ∀ x, HasDerivAt m (m' x) x := fun x => by
    have := (hasDerivAt_cC φ π x).neg.add (((hasDerivAt_id x).pow 2).const_mul (c / 2))
    refine this.congr_deriv ?_
    simp only [m', id, Nat.cast_ofNat]
    ring
  have hm' : ∀ x, HasDerivAt m' (m'' x) x := fun x => by
    have := (hasDerivAt_cC' φ π x).neg.add ((hasDerivAt_id x).const_mul c)
    exact this.congr_deriv (by simp only [m'']; ring)
  have hD : (Set.Icc (-(2 * R)) (2 * R)).OrdConnected := Set.ordConnected_Icc
  have hE0 : 0 < 2 * Real.exp (π - 2 * R) - 1 := by
    have h1 := Real.exp_pos (π - 2 * R)
    by_contra hcon
    push Not at hcon
    have : c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
    linarith
  have hneg : ∀ x ∈ Set.Icc (-(2 * R)) (2 * R), m'' x ≤ 0 := by
    intro x hx
    have hy : Real.exp (π - 2 * R) ≤ Real.exp (x + π) := Real.exp_le_exp.2 (by linarith [hx.1])
    have : c ≤ φ * Real.exp (x + π) * (2 * Real.exp (x + π) - 1) := by
      simp only [c, cP]
      have h0 := Real.exp_pos (π - 2 * R)
      have key : Real.exp (π - 2 * R) * (2 * Real.exp (π - 2 * R) - 1) ≤
          Real.exp (x + π) * (2 * Real.exp (x + π) - 1) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left key hφ.le]
    simp only [m'']
    linarith
  have h0 : (0 : ℝ) ∈ Set.Icc (-(2 * R)) (2 * R) := ⟨by
    have := hE0; nlinarith [Real.exp_le_exp (x := π - 2 * R) (y := π), Real.exp_pos π],
    by nlinarith [Real.exp_le_exp (x := π - 2 * R) (y := π), Real.exp_pos π]⟩
  have := tangent_of_antitoneOn hD hm (antitoneOn_of_deriv_nonpos' hD hm' hneg) h0 ⟨hd1, hd2⟩
  simp only [m, m', zero_add, mul_zero, add_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at this
  simp only [gC]
  linarith

/-- Cochrane (2023), p. 118, **static loss away from the aggregate price**: if `|f′(0)| ≤ cS·R`
(`ε > 1`, `η > ε − 1`, `A, B ≥ 0`, `R ≥ 0`), then for `|a| ≥ R`,
`f(a) ≤ f(0) + |f′(0)|R − (cS/2)R²`. -/
theorem static_outside {ε η A B R : ℝ} (hε : 1 < ε) (hη : ε - 1 < η) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hf : |f1 ε η A B| ≤ cS ε η A B R * R) (a : ℝ) (ha : R ≤ |a|) :
    gRes ε η A B a ≤ gRes ε η A B 0 + |f1 ε η A B| * R - cS ε η A B R / 2 * R ^ 2 := by
  have hη0 : 0 < η := by linarith
  obtain ⟨hs, hR1, hR2⟩ := static_strong (R := R) hε hη0 hA hB
  have hc0 : 0 < 1 - ε + η := by linarith
  have hd : ∀ x, HasDerivAt (gRes ε η A B)
      (Real.exp (-(η * x)) * (η * B - (ε - 1) * A * Real.exp ((1 - ε + η) * x))) x :=
    fun x => (hasDerivAt_gRes ε η A B x).congr_deriv (deriv_gRes_eq ε η A B x)
  have hk : 0 ≤ (ε - 1) * A := mul_nonneg (by linarith) hA
  have hD1 := hR1 hR
  have hD2 := hR2 hR
  rw [deriv_gRes_eq] at hD1 hD2
  have hf1 := neg_abs_le (f1 ε η A B)
  have hf2 := le_abs_self (f1 ε η A B)
  rcases le_abs'.1 ha with h | h
  · -- `a ≤ −R`: the payoff is increasing up to `−R`
    have hpos : 0 ≤ η * B - (ε - 1) * A * Real.exp ((1 - ε + η) * -R) := by
      by_contra hcon
      push Not at hcon
      have := mul_neg_of_pos_of_neg (Real.exp_pos (-(η * -R))) hcon
      linarith
    have hmono : MonotoneOn (gRes ε η A B) (Set.Iic (-R)) :=
      monotoneOn_of_deriv_nonneg' Set.ordConnected_Iic hd fun x hx => by
        refine mul_nonneg (Real.exp_pos _).le ?_
        have : Real.exp ((1 - ε + η) * x) ≤ Real.exp ((1 - ε + η) * -R) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx hc0.le)
        nlinarith [mul_le_mul_of_nonneg_left this hk]
    have h1 := hmono (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h
    have h2 := hs (-R) le_rfl (by linarith)
    nlinarith
  · -- `a ≥ R`: the payoff is decreasing from `R`
    have hneg : η * B - (ε - 1) * A * Real.exp ((1 - ε + η) * R) ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have := mul_pos (Real.exp_pos (-(η * R))) hcon
      linarith
    have hanti : AntitoneOn (gRes ε η A B) (Set.Ici R) :=
      antitoneOn_of_deriv_nonpos' Set.ordConnected_Ici hd fun x hx => by
        refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
        have : Real.exp ((1 - ε + η) * R) ≤ Real.exp ((1 - ε + η) * x) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx hc0.le)
        nlinarith [mul_le_mul_of_nonneg_left this hk]
    have h1 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h
    have h2 := hs R (by linarith) le_rfl
    nlinarith

/-- Cochrane (2023), p. 118, **the cost away from small price changes**: if `|π| ≤ 2R` and
`φ ≥ 0`, then for `|d| ≥ 2R`, `C(d) ≥ min(C(2R), C(−2R))`. -/
theorem cost_outside {φ π R : ℝ} (hφ : 0 ≤ φ) (hπ : |π| ≤ 2 * R) (d : ℝ) (hd : 2 * R ≤ |d|) :
    min (cC φ π (2 * R)) (cC φ π (-(2 * R))) ≤ cC φ π d := by
  rcases le_abs'.1 hd with h | h
  · have hanti : AntitoneOn (cC φ π) (Set.Iic (-(2 * R))) :=
      antitoneOn_of_deriv_nonpos' Set.ordConnected_Iic (hasDerivAt_cC φ π) fun x hx => by
        have hx' : x + π ≤ 0 := by
          have := (abs_le.1 hπ).2; rw [Set.mem_Iic] at hx; linarith
        have h1 : Real.exp (x + π) ≤ 1 := Real.exp_le_one_iff.2 hx'
        have := Real.exp_pos (x + π)
        have : φ * (Real.exp (x + π) - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hφ (by linarith)
        nlinarith
    exact (min_le_right _ _).trans (hanti (Set.mem_Iic.2 h) (Set.mem_Iic.2 le_rfl) h)
  · have hmono : MonotoneOn (cC φ π) (Set.Ici (2 * R)) :=
      monotoneOn_of_deriv_nonneg' Set.ordConnected_Ici (hasDerivAt_cC φ π) fun x hx => by
        have hx' : 0 ≤ x + π := by
          have := (abs_le.1 hπ).1; rw [Set.mem_Ici] at hx; linarith
        have h1 : 1 ≤ Real.exp (x + π) := Real.one_le_exp_iff.2 hx'
        exact mul_nonneg (mul_nonneg hφ (by linarith)) (Real.exp_pos _).le
    exact (min_le_left _ _).trans (hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h) h)

/-! ### The global inequality for the payoff with the potential -/

/-- Cochrane (2023), p. 118: the clamp is bounded by `R`. -/
theorem abs_clampR_le {R : ℝ} (hR : 0 ≤ R) (b : ℝ) : |clampR R b| ≤ R := by
  simp only [clampR, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_right _ _)

/-- Cochrane (2023), p. 118: the clamp is the identity on `[−R, R]`. -/
theorem clampR_of_abs_le {R b : ℝ} (h : |b| ≤ R) : clampR R b = b := by
  have := abs_le.1 h
  simp only [clampR]
  rw [min_eq_left this.2, max_eq_right this.1]

/-- Cochrane (2023), p. 118: the clamp is `1`-Lipschitz. -/
theorem abs_clampR_sub {R : ℝ} (a b : ℝ) : |clampR R a - clampR R b| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b)
  have h2 := neg_abs_le (a - b)
  simp only [clampR, max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Cochrane (2023), p. 118: outside `[−R, R]` the clamp moves `b` by `|b| − R`. -/
theorem abs_sub_clampR {R b : ℝ} (hR : 0 ≤ R) (h : R < |b|) : |b - clampR R b| = |b| - R := by
  rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg hb] at h ⊢
    simp only [clampR]
    rw [min_eq_right h.le, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
  · rw [abs_of_neg hb] at h ⊢
    simp only [clampR]
    rw [min_eq_left (by linarith), max_eq_left (by linarith),
      show b - -R = b + R by ring, abs_of_nonpos (by linarith)]
    ring

/-- Cochrane (2023), p. 118: the explicit conditions on the data `(A, B, π)` under which the
payoff with the potential has a global maximum at the aggregate price: nonnegative weights,
positive curvature bounds, small inflation, cost growth outside `[−2R, 2R]`, and smallness of
`f′(0)` and `g`. -/
def PotCond (ε η φ A B π R : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧ 0 < cS ε η A B R ∧ 0 < cP φ π R ∧ |π| ≤ 2 * R ∧
    cC φ π 0 + 2 * R * |gC φ π| ≤ cC φ π (2 * R) ∧
    cC φ π 0 + 2 * R * |gC φ π| ≤ cC φ π (-(2 * R)) ∧
    2 * |f1 ε η A B| * R * cP φ π R + 2 * gC φ π ^ 2 ≤ cS ε η A B R / 2 * R ^ 2 * cP φ π R ∧
    |gC φ π| ≤ cS ε η A B R * R / 16 ∧ |gC φ π| ≤ cP φ π R * R / 4

/-- Cochrane (2023), p. 118: the inequality when both prices are in `[−R, R]`. -/
theorem case_in {fa f0 C0 Cd F1 g c c' a b d : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (hd : d = a - b)
    (hfa : fa ≤ f0 + F1 * a - c / 2 * a ^ 2) (hcd : C0 + g * d + c' / 2 * d ^ 2 ≤ Cd) :
    fa - Cd + (g - F1) * a - g * b ≤ f0 - C0 := by
  have h1 := mul_nonneg hc (sq_nonneg a)
  have h2 := mul_nonneg hc' (sq_nonneg d)
  have e : g * d = g * a - g * b := by rw [hd]; ring
  nlinarith

/-- Cochrane (2023), p. 118: the key estimate when `|a| ≤ R < |b|` and `|a − b| ≤ 2R`. -/
theorem key3 {c c' R g a b d : ℝ} (hc : 0 < c) (hc' : 0 < c') (hR : 0 < R) (ha : |a| ≤ R)
    (hb : R < |b|)
    (hbd : |b| ≤ |a| + |d|) (hdd : |d| ≤ 2 * R) (hg1 : |g| ≤ c * R / 16)
    (hg2 : |g| ≤ c' * R / 4) : -(c / 2) * a ^ 2 + |g| * (|b| - R) - c' / 2 * d ^ 2 ≤ 0 := by
  have hg0 := abs_nonneg g
  by_cases ha2 : R / 2 ≤ |a|
  · have h1 : (R / 2) ^ 2 ≤ a ^ 2 := by
      rw [← sq_abs a]; exact pow_le_pow_left₀ (by linarith) ha2 2
    have h2 : |g| * (|b| - R) ≤ |g| * (2 * R) :=
      mul_le_mul_of_nonneg_left (by linarith [abs_nonneg a]) hg0
    have h3 : |g| * (2 * R) ≤ c * R / 16 * (2 * R) := mul_le_mul_of_nonneg_right hg1 (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h1 hc.le
    have h5 := mul_nonneg hc'.le (sq_nonneg d)
    nlinarith
  · push Not at ha2
    have hdR : R / 2 ≤ |d| := by linarith
    have h1 : |g| * (|b| - R) ≤ |g| * |d| := mul_le_mul_of_nonneg_left (by linarith) hg0
    have h2 : |g| * |d| ≤ c' * R / 4 * |d| := mul_le_mul_of_nonneg_right hg2 (abs_nonneg d)
    have h3 : c' * R / 4 * |d| ≤ c' / 2 * d ^ 2 := by
      rw [← sq_abs d]
      have := mul_le_mul_of_nonneg_left hdR (mul_nonneg hc'.le (abs_nonneg d))
      nlinarith
    have h4 := mul_nonneg hc.le (sq_nonneg a)
    linarith

/-- Cochrane (2023), p. 118: the inequality when `|a| ≤ R < |b|` and `|a − b| ≤ 2R`. -/
theorem case_mix_near {fa f0 C0 Cd F1 g c c' a sb d e : ℝ}
    (hfa : fa ≤ f0 + F1 * a - c / 2 * a ^ 2) (hcd : C0 + g * d + c' / 2 * d ^ 2 ≤ Cd)
    (hde : a - sb = d + e) (hge : g * e ≤ |g| * (|e|))
    (hkey : -(c / 2) * a ^ 2 + |g| * |e| - c' / 2 * d ^ 2 ≤ 0) :
    fa - Cd + (g - F1) * a - g * sb ≤ f0 - C0 := by
  have e1 : g * sb = g * a - g * d - g * e := by
    have : sb = a - d - e := by linarith
    rw [this]; ring
  nlinarith

/-- Cochrane (2023), p. 118: the inequality when `|a| ≤ R < |b|` and `|a − b| > 2R`. -/
theorem case_mix_far {fa f0 C0 Cd F1 g c a sb R : ℝ} (hc : 0 ≤ c)
    (hfa : fa ≤ f0 + F1 * a - c / 2 * a ^ 2) (hcd : C0 + 2 * R * |g| ≤ Cd)
    (hab : g * (a - sb) ≤ 2 * R * |g|) :
    fa - Cd + (g - F1) * a - g * sb ≤ f0 - C0 := by
  have := mul_nonneg hc (sq_nonneg a)
  nlinarith

/-- Cochrane (2023), p. 118: the inequality when `|a| > R` and `|a − b| ≤ 2R`. -/
theorem case_out_near {fa f0 C0 Cd F1 g c c' R sa sb d : ℝ} (hc' : 0 < c')
    (hfa : fa ≤ f0 + |F1| * R - c / 2 * R ^ 2) (hF1a : -(F1 * sa) ≤ |F1| * R)
    (hcd : C0 + g * d + c' / 2 * d ^ 2 ≤ Cd)
    (hgs : g * (sa - sb) - g * d ≤ 2 * |g| * |d|)
    (amgm : c' * (2 * |g| * |d|) - c' * (c' / 2 * d ^ 2) ≤ 2 * g ^ 2)
    (hK6 : 2 * |F1| * R * c' + 2 * g ^ 2 ≤ c / 2 * R ^ 2 * c') :
    fa - Cd + (g - F1) * sa - g * sb ≤ f0 - C0 := by
  have hQ : c' * (2 * |F1| * R - c / 2 * R ^ 2 + 2 * |g| * |d| - c' / 2 * d ^ 2) ≤ 0 := by
    nlinarith
  have hQ' : 2 * |F1| * R - c / 2 * R ^ 2 + 2 * |g| * |d| - c' / 2 * d ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hc' hcon]
  nlinarith

/-- Cochrane (2023), p. 118: the inequality when `|a| > R` and `|a − b| > 2R`. -/
theorem case_out_far {fa f0 C0 Cd F1 g c R sa sb : ℝ}
    (hfa : fa ≤ f0 + |F1| * R - c / 2 * R ^ 2) (hF1a : -(F1 * sa) ≤ |F1| * R)
    (hcd : C0 + 2 * R * |g| ≤ Cd) (hab : g * (sa - sb) ≤ 2 * R * |g|)
    (hK : 2 * |F1| * R ≤ c / 2 * R ^ 2) :
    fa - Cd + (g - F1) * sa - g * sb ≤ f0 - C0 := by
  nlinarith

/-- Cochrane (2023), p. 118, **the global inequality**: under `PotCond`, with the potential
coefficient `h = g − f′(0)` (the first-order condition), for all `a`, `b`,
`f(a) − C(a − b) + h s(a) − g s(b) ≤ f(0) − C(0)`. -/
theorem pot_le {ε η φ A B π R : ℝ} (hε : 1 < ε) (hη : ε - 1 < η) (hφ : 0 < φ) (hR : 0 < R)
    (hc : PotCond ε η φ A B π R) {h : ℝ} (hh : h = gC φ π - f1 ε η A B) (a b : ℝ) :
    gRes ε η A B a - cC φ π (a - b) + h * clampR R a - gC φ π * clampR R b ≤
      gRes ε η A B 0 - cC φ π 0 := by
  obtain ⟨hA, hB, hcS, hcP, hπ, hC1, hC2, hK6, hK7a, hK7b⟩ := hc
  have hη0 : 0 < η := by linarith
  have hK : 2 * |f1 ε η A B| * R ≤ cS ε η A B R / 2 * R ^ 2 := by
    have h1 : 2 * |f1 ε η A B| * R * cP φ π R ≤ cS ε η A B R / 2 * R ^ 2 * cP φ π R := by
      nlinarith [sq_nonneg (gC φ π)]
    exact le_of_mul_le_mul_right h1 hcP
  have hF1 : |f1 ε η A B| ≤ cS ε η A B R * R := by nlinarith [abs_nonneg (f1 ε η A B)]
  have hCO : ∀ x, 2 * R ≤ |x| → cC φ π 0 + 2 * R * |gC φ π| ≤ cC φ π x := fun x hx =>
    le_trans (le_min hC1 hC2) (cost_outside hφ.le hπ x hx)
  have hCS : ∀ x, |x| ≤ 2 * R →
      cC φ π 0 + gC φ π * x + cP φ π R / 2 * x ^ 2 ≤ cC φ π x := fun x hx =>
    cost_strong hφ hcP x (abs_le.1 hx).1 (abs_le.1 hx).2
  have hsa := abs_clampR_le hR.le a
  have hsb := abs_clampR_le hR.le b
  have hbd : |b| ≤ |a| + |a - b| := by
    have := abs_sub_abs_le_abs_sub b a; rw [abs_sub_comm a b]; linarith
  rw [hh]
  by_cases ha : |a| ≤ R
  · have hfa := (static_strong (R := R) hε hη0 hA hB).1 a (abs_le.1 ha).1 (abs_le.1 ha).2
    rw [clampR_of_abs_le ha]
    by_cases hb : |b| ≤ R
    · rw [clampR_of_abs_le hb]
      have hdd : |a - b| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
      exact case_in hcS.le hcP.le rfl hfa (hCS _ hdd)
    · push Not at hb
      by_cases hdd : |a - b| ≤ 2 * R
      · have he := abs_sub_clampR hR.le hb
        refine case_mix_near hfa (hCS _ hdd) (by ring) ?_ ?_ (e := b - clampR R b)
        · rw [← abs_mul]; exact le_abs_self _
        · rw [he]
          exact key3 hcS hcP hR ha hb hbd hdd hK7a hK7b
      · push Not at hdd
        refine case_mix_far hcS.le hfa (hCO _ hdd.le) ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        have : |a - clampR R b| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
        nlinarith [abs_nonneg (gC φ π)]
  · push Not at ha
    have hfa := static_outside (R := R) hε hη hA hB hR.le hF1 a ha.le
    have hF1a : -(f1 ε η A B * clampR R a) ≤ |f1 ε η A B| * R := by
      have h1 := neg_abs_le (f1 ε η A B * clampR R a)
      rw [abs_mul] at h1
      nlinarith [mul_le_mul_of_nonneg_left hsa (abs_nonneg (f1 ε η A B))]
    by_cases hdd : |a - b| ≤ 2 * R
    · refine case_out_near hcP hfa hF1a (hCS _ hdd) ?_ ?_ hK6
      · have hlip := abs_clampR_sub (R := R) a b
        have h1 := le_abs_self (gC φ π * (clampR R a - clampR R b))
        have h2 := neg_abs_le (gC φ π * (a - b))
        rw [abs_mul] at h1 h2
        nlinarith [mul_le_mul_of_nonneg_left hlip (abs_nonneg (gC φ π))]
      · rw [← sq_abs (a - b), ← sq_abs (gC φ π)]
        nlinarith [sq_nonneg (cP φ π R * |a - b| - 2 * |gC φ π|)]
    · push Not at hdd
      refine case_out_far hfa hF1a (hCO _ hdd.le) ?_ hK
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      have : |clampR R a - clampR R b| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
      nlinarith [abs_nonneg (gC φ π)]

/-! ### The verification theorem -/

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: at the aggregate price, the derivatives of the Rotemberg payoff are
`Φ₁ = f′(0) − g` and `Φ₂ = g`. -/
theorem rotD_zero (ε η φ : ℝ) (v : ℝ × ℝ × ℝ) :
    rotD1 ε η φ 0 0 v = f1 ε η v.1 v.2.1 - gC φ v.2.2 ∧ rotD2 φ 0 0 v = gC φ v.2.2 := by
  constructor
  · simp only [rotD1, f1, gC, mul_zero, Real.exp_zero, mul_one, neg_zero, sub_zero, zero_add]
    ring
  · simp only [rotD2, gC, sub_zero, zero_add]

/-- Cochrane (2023), p. 118: `|g| ≤ φ(e^K + 1)e^K` when `|π| ≤ K` (`φ ≥ 0`). -/
theorem abs_gC_le {φ π K : ℝ} (hφ : 0 ≤ φ) (h : |π| ≤ K) :
    |gC φ π| ≤ φ * (Real.exp K + 1) * Real.exp K := by
  have h1 : Real.exp π ≤ Real.exp K := Real.exp_le_exp.2 (le_abs_self π |>.trans h)
  have h2 := Real.exp_pos π
  simp only [gC]
  rw [abs_mul, abs_mul, abs_of_nonneg hφ, abs_of_pos h2]
  have h3 : |Real.exp π - 1| ≤ Real.exp K + 1 := by
    rw [abs_le]; constructor <;> linarith [Real.exp_pos K]
  have := mul_le_mul h3 h1 h2.le (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left this hφ]

/-- Cochrane (2023), p. 118, **the verification theorem**: let `0 < β < 1`, `ε > 1`, `η > ε − 1`,
`φ > 0`, `R > 0`, the data adapted and uniformly bounded, charging the aggregate price satisfy the
first-order condition at every date, and `PotCond` hold at every date almost surely. Then
charging the aggregate price is optimal among **all** plans. -/
theorem optimal_of_pot {β ε η φ R : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hε : 1 < ε)
    (hη : ε - 1 < η) (hφ : 0 < φ) (hR : 0 < R) {θ : ℕ → Ω → ℝ × ℝ × ℝ} (hθ : DataReg S θ)
    (hθu : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ K)
    (hfoc : ∀ t, FOC S β (rotD1 ε η φ) (rotD2 φ) θ (fun _ => 0) zeroPlan t)
    (hcond : ∀ t, ∀ᵐ ω ∂S.μ, PotCond ε η φ (θ t ω).1 (θ t ω).2.1 (θ t ω).2.2 R) :
    OptimalIn S (Plan S) β (rotPay ε η φ) θ (fun _ => 0) zeroPlan := by
  have hadm0 := TidyR6RotembergPC.admissible_zero (ε := ε) (η := η) (φ := φ) hβ.le hβ1 hθ hθu
  refine ⟨TidyR6RotembergPC.uplan_zero.1, hadm0, fun q' hq' hadm' => ?_⟩
  obtain ⟨K, hK⟩ := hθu
  set G := φ * (Real.exp K + 1) * Real.exp K
  set g : ℕ → Ω → ℝ := fun t ω => gC φ (θ t ω).2.2 with hgdef
  have hgm : ∀ t, StronglyMeasurable[S.𝓕 t] (g t) := fun t => by
    have : Measurable[S.𝓕 t] fun ω => (θ t ω).2.2 := (hθ.1 t).measurable.snd.snd
    exact ((((Real.continuous_exp.measurable.comp this).sub_const 1).const_mul φ).mul
      (Real.continuous_exp.measurable.comp this)).stronglyMeasurable
  have hgb : ∀ t, ∀ᵐ ω ∂S.μ, |g t ω| ≤ G := fun t => by
    filter_upwards [hK t] with ω h
    refine abs_gC_le hφ.le ?_
    have h1 := norm_snd_le (θ t ω)
    have h2 := norm_snd_le (θ t ω).2
    rw [Real.norm_eq_abs] at h2
    linarith
  set s : ℝ → ℝ := clampR R with hsdef
  set l' := lag (fun _ : Ω => (0 : ℝ)) q' with hl'
  have hsm : ∀ t (r : Ω → ℝ), StronglyMeasurable[S.𝓕 t] r →
      StronglyMeasurable[S.𝓕 t] (fun ω => s (r ω)) := fun t r hr =>
    (measurable_const.max (hr.measurable.min measurable_const)).stronglyMeasurable
  have hsb : ∀ x, |s x| ≤ R := abs_clampR_le hR.le
  have hs0 : s 0 = 0 := clampR_of_abs_le (by simp [hR.le])
  have hgi : ∀ t, Integrable (g t) S.μ := fun t =>
    Integrable.of_bound ((hgm t).mono (S.𝓕.le t)).aestronglyMeasurable G
      ((hgb t).mono fun ω h => by rwa [Real.norm_eq_abs])
  -- the products with the potential are integrable and bounded
  have hprod : ∀ t (r : Ω → ℝ) (X : Ω → ℝ), StronglyMeasurable[S.𝓕 t] r →
      AEStronglyMeasurable X S.μ → (∀ᵐ ω ∂S.μ, |X ω| ≤ G) →
      Integrable (fun ω => X ω * s (r ω)) S.μ := fun t r X hr hX hXb =>
    Integrable.of_bound (hX.mul ((hsm t r hr).mono (S.𝓕.le t)).aestronglyMeasurable) (G * R)
      (hXb.mono fun ω h => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul h (hsb _) (abs_nonneg _) ((abs_nonneg _).trans h))
  set u : ℕ → ℝ := fun t => β ^ t * ∫ ω, g t ω * s (l' t ω) ∂S.μ with hudef
  have hu0 : u 0 = 0 := by simp [hudef, hl', lag, hs0]
  have hub : ∀ t, |u t| ≤ β ^ t * (G * R) := fun t => by
    simp only [hudef]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hβ.le t)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ.le t)
    rw [← Real.norm_eq_abs]
    have hb : ∀ᵐ ω ∂S.μ, ‖g t ω * s (l' t ω)‖ ≤ G * R := (hgb t).mono fun ω h => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul h (hsb _) (abs_nonneg _) ((abs_nonneg _).trans h)
    simpa using norm_integral_le_of_norm_le_const hb
  -- the date-`t` comparison
  have hstep : ∀ t, β ^ t * (∫ ω, pay (rotPay ε η φ) θ (fun _ => 0) q' t ω ∂S.μ -
      ∫ ω, pay (rotPay ε η φ) θ (fun _ => 0) zeroPlan t ω ∂S.μ) ≤ u t - u (t + 1) := by
    intro t
    have hE : (fun ω => rotD2 φ (zeroPlan (t + 1) ω) (zeroPlan t ω) (θ (t + 1) ω)) =
        g (t + 1) := funext fun ω => (rotD_zero ε η φ (θ (t + 1) ω)).2
    have hpt : ∀ᵐ ω ∂S.μ, pay (rotPay ε η φ) θ (fun _ => 0) q' t ω +
        β * S.E t (g (t + 1)) ω * s (q' t ω) - g t ω * s (l' t ω) ≤
          pay (rotPay ε η φ) θ (fun _ => 0) zeroPlan t ω := by
      filter_upwards [hfoc t, hcond t] with ω h1 h2
      rw [hE, lag_zeroPlan] at h1
      simp only [zeroPlan] at h1
      rw [(rotD_zero ε η φ (θ t ω)).1] at h1
      have hh : β * S.E t (g (t + 1)) ω = gC φ (θ t ω).2.2 - f1 ε η (θ t ω).1 (θ t ω).2.1 := by
        linarith
      have := pot_le hε hη hφ hR h2 hh (q' t ω) (l' t ω)
      simp only [pay, rot_eq, zeroPlan, lag_zeroPlan, sub_self]
      exact this
    have hl'm : StronglyMeasurable[S.𝓕 t] (l' t) := lag_sm stronglyMeasurable_const hq'.1 t
    have hEi : Integrable (fun ω => S.E t (g (t + 1)) ω * s (q' t ω)) S.μ :=
      hprod t (q' t) _ (hq'.1 t) (S.integrable_E t _).aestronglyMeasurable
        (S.abs_E_le (hgb (t + 1)) t)
    have hgl : Integrable (fun ω => g t ω * s (l' t ω)) S.μ :=
      hprod t (l' t) _ hl'm (hgi t).aestronglyMeasurable (hgb t)
    have hA : Integrable (fun ω => pay (rotPay ε η φ) θ (fun _ => 0) q' t ω +
        β * (S.E t (g (t + 1)) ω * s (q' t ω))) S.μ := (hadm'.1 t).add (hEi.const_mul β)
    have hB : Integrable (fun ω => pay (rotPay ε η φ) θ (fun _ => 0) q' t ω +
        β * (S.E t (g (t + 1)) ω * s (q' t ω)) - g t ω * s (l' t ω)) S.μ := hA.sub hgl
    have hint := integral_mono_ae hB (hadm0.1 t) (hpt.mono fun ω h => by linarith)
    rw [integral_sub hA hgl, integral_add (hadm'.1 t) (hEi.const_mul β),
      integral_const_mul] at hint
    have hlie : ∫ ω, S.E t (g (t + 1)) ω * s (q' t ω) ∂S.μ =
        ∫ ω, g (t + 1) ω * s (l' (t + 1) ω) ∂S.μ := by
      have := integral_mul_E (S := S) (hsm t (q' t) (hq'.1 t))
        (Eventually.of_forall fun _ => hsb _)
        (hgi (t + 1))
      simp only [hl', lag]
      rw [integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _), ← this]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hlie] at hint
    simp only [hudef, pow_succ]
    have hbt := pow_nonneg hβ.le t
    nlinarith [mul_le_mul_of_nonneg_left hint hbt]
  -- telescoping and the limit
  have hulim : Tendsto u atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun t => β ^ t * (G * R))
      (fun t => by rw [Real.norm_eq_abs]; exact hub t) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le hβ1).mul_const (G * R)
  have hsum := ((hadm'.summable hβ.le).sub (hadm0.summable hβ.le)).hasSum
  have hle := le_of_tendsto_of_tendsto' hsum.tendsto_sum_nat hulim.neg fun T => by
    have := Finset.sum_le_sum fun t (_ : t ∈ Finset.range T) => hstep t
    rw [Finset.sum_range_sub', hu0, zero_sub] at this
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [(hadm'.summable hβ.le).tsum_sub (hadm0.summable hβ.le), neg_zero] at hle
  unfold value
  linarith

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: at the zero-inflation steady state (`Ā, B̄ > 0`,
`(1 − ε)Ā + ηB̄ = 0`, `π = 0`) the conditions of `pot_le` hold, for some `R > 0`, on a whole
neighbourhood: there is `ρ > 0` such that every `v` within `ρ` of `(Ā, B̄, 0)` satisfies them. -/
theorem near_ss {ε η φ A B : ℝ} (hε : 1 < ε) (hη : ε - 1 < η) (hφ : 0 < φ) (hA : 0 < A)
    (hB : 0 < B) (hf : f1 ε η A B = 0) :
    ∃ R, 0 < R ∧ ∃ ρ, 0 < ρ ∧ ∀ v : ℝ × ℝ × ℝ, dist v (A, B, 0) < ρ →
      PotCond ε η φ v.1 v.2.1 v.2.2 R := by
  -- the choice of `R`
  have hS0 : 0 < cS ε η A B 0 := by
    have hηB : η * B = (ε - 1) * A := by simp only [f1] at hf; linarith
    have h1 : 0 < (ε - 1) * A * (η - (ε - 1)) :=
      mul_pos (mul_pos (by linarith) hA) (by linarith)
    simp only [cS, mul_zero, neg_zero, Real.exp_zero, mul_one]
    nlinarith [congrArg (η * ·) hηB]
  have hP0 : 0 < cP φ 0 0 := by
    simp only [cP, mul_zero, sub_zero, Real.exp_zero, mul_one]
    linarith
  have hcS : Continuous fun R => cS ε η A B R := by unfold cS; fun_prop
  have hcP : Continuous fun R => cP φ 0 R := by unfold cP; fun_prop
  obtain ⟨δ, hδ, hδR⟩ := Metric.eventually_nhds_iff.1
    ((hcS.continuousAt.eventually (Ioi_mem_nhds hS0)).and
      (hcP.continuousAt.eventually (Ioi_mem_nhds hP0)))
  set R := δ / 2 with hRdef
  have hR : 0 < R := by positivity
  obtain ⟨hSR, hPR⟩ := hδR (y := R) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hR]; linarith)
  refine ⟨R, hR, ?_⟩
  -- the strict conditions at the steady state, and continuity
  set v0 : ℝ × ℝ × ℝ := (A, B, 0)
  have ev : ∀ F : ℝ × ℝ × ℝ → ℝ, Continuous F → 0 < F v0 → ∀ᶠ v in 𝓝 v0, 0 < F v :=
    fun F hF h => hF.continuousAt.eventually (Ioi_mem_nhds h)
  have hg0 : gC φ 0 = 0 := by simp [gC]
  have hC0 : cC φ 0 0 = 0 := by simp [cC]
  have hC2 : ∀ d, d ≠ 0 → 0 < cC φ 0 d := fun d hd => by
    simp only [cC, add_zero]
    have : Real.exp d - 1 ≠ 0 := by
      rw [sub_ne_zero, Ne, Real.exp_eq_one_iff]; exact hd
    positivity
  have e1 := ev (fun v => v.1) (by fun_prop) hA
  have e2 := ev (fun v => v.2.1) (by fun_prop) hB
  have e3 := ev (fun v => cS ε η v.1 v.2.1 R) (by unfold cS; fun_prop) hSR
  have e4 := ev (fun v => cP φ v.2.2 R) (by unfold cP; fun_prop) hPR
  have e5 := ev (fun v => 2 * R - |v.2.2|) (by fun_prop) (by simp [v0]; linarith)
  have e6 := ev (fun v => cC φ v.2.2 (2 * R) - (cC φ v.2.2 0 + 2 * R * |gC φ v.2.2|))
    (by unfold cC gC; fun_prop) (by
      simp only [v0, hg0, hC0, abs_zero, mul_zero, add_zero, sub_zero]
      exact hC2 _ (by positivity))
  have e7 := ev (fun v => cC φ v.2.2 (-(2 * R)) - (cC φ v.2.2 0 + 2 * R * |gC φ v.2.2|))
    (by unfold cC gC; fun_prop) (by
      simp only [v0, hg0, hC0, abs_zero, mul_zero, add_zero, sub_zero]
      exact hC2 _ (by linarith))
  have e8 := ev (fun v => cS ε η v.1 v.2.1 R / 2 * R ^ 2 * cP φ v.2.2 R -
      (2 * |f1 ε η v.1 v.2.1| * R * cP φ v.2.2 R + 2 * gC φ v.2.2 ^ 2))
    (by unfold cS cP f1 gC; fun_prop) (by
      simp only [v0, hg0, hf, abs_zero, mul_zero, zero_mul]
      norm_num
      positivity)
  have e9 := ev (fun v => cS ε η v.1 v.2.1 R * R / 16 - |gC φ v.2.2|)
    (by unfold cS gC; fun_prop) (by simp only [v0, hg0, abs_zero, sub_zero]; positivity)
  have e10 := ev (fun v => cP φ v.2.2 R * R / 4 - |gC φ v.2.2|)
    (by unfold cP gC; fun_prop) (by simp only [v0, hg0, abs_zero, sub_zero]; positivity)
  obtain ⟨ρ, hρ, hρv⟩ := Metric.eventually_nhds_iff.1
    (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (e7.and (e8.and (e9.and e10)))))))))
  refine ⟨ρ, hρ, fun v hv => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hρv hv
  exact ⟨h1.le, h2.le, h3, h4, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-- Cochrane (2023), p. 118 and eq. (17.17), p. 407, **local global sufficiency**: let
`0 < β < 1`, `ε > 1`, `η > ε − 1`, `φ > 0`, and `(Ā, B̄, 0)` a zero-inflation steady state
(`Ā, B̄ > 0`, `(1 − ε)Ā + ηB̄ = 0`). There is `ρ > 0` such that, for adapted data staying within
`ρ` of the steady state at every date almost surely, charging the aggregate price is optimal
among **all** plans as soon as it satisfies the first-order condition. -/
theorem optimal_near_ss {β ε η φ A B : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hε : 1 < ε)
    (hη : ε - 1 < η) (hφ : 0 < φ) (hA : 0 < A) (hB : 0 < B) (hf : f1 ε η A B = 0) :
    ∃ ρ, 0 < ρ ∧ ∀ θ : ℕ → Ω → ℝ × ℝ × ℝ, StronglyAdapted S.𝓕 θ →
      (∀ t, ∀ᵐ ω ∂S.μ, dist (θ t ω) (A, B, 0) < ρ) →
      (∀ t, FOC S β (rotD1 ε η φ) (rotD2 φ) θ (fun _ => 0) zeroPlan t) →
      OptimalIn S (Plan S) β (rotPay ε η φ) θ (fun _ => 0) zeroPlan := by
  obtain ⟨R, hR, ρ, hρ, hcond⟩ := near_ss (φ := φ) hε hη hφ hA hB hf
  refine ⟨ρ, hρ, fun θ hθa hθρ hfoc => ?_⟩
  have hK : ∀ t, ∀ᵐ ω ∂S.μ, ‖θ t ω‖ ≤ ‖((A, B, 0) : ℝ × ℝ × ℝ)‖ + ρ := fun t => by
    filter_upwards [hθρ t] with ω h
    rw [dist_eq_norm] at h
    have := norm_le_insert' (θ t ω) ((A, B, 0) : ℝ × ℝ × ℝ)
    linarith
  exact optimal_of_pot hβ hβ1 hε hη hφ hR ⟨hθa, fun t => ⟨_, hK t⟩⟩ ⟨_, hK⟩ hfoc
    fun t => (hθρ t).mono fun ω h => hcond _ h

/-- Cochrane (2023), p. 118 and eq. (17.17), p. 407, **local global sufficiency for the
symmetric equilibrium**: with `0 < β < 1`, `ε > 1`, `ϕ ≥ 0`, `φ > 0`, `η = ε(1 + ϕ)` and `Ȳ > 0`
the steady state, there is `ρ > 0` such that whenever output gap and inflation are adapted, stay
in `(−ρ, ρ)` at every date almost surely, and satisfy the exact nonlinear Phillips curve, charging
the aggregate price is optimal among **all** plans. -/
theorem optimal_near_ss_yeo {β ε φ γ ϕ Ybar : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hε : 1 < ε)
    (hϕ : 0 ≤ ϕ) (hφ : 0 < φ) (hY : 0 < Ybar)
    (hss : ε * Ybar ^ (1 + ϕ) = (ε - 1) * Ybar ^ (1 - γ)) :
    ∃ ρ, 0 < ρ ∧ ∀ x π : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 x → StronglyAdapted S.𝓕 π →
      (∀ t, ∀ᵐ ω ∂S.μ, |x t ω| < ρ ∧ |π t ω| < ρ) →
      (∀ t, NonlinPC S β (kappaT ε φ γ Ybar) γ ϕ x π t) →
      OptimalIn S (Plan S) β (rotPay ε (ε * (1 + ϕ)) φ) (yeoData γ ϕ Ybar x π) (fun _ => 0)
        zeroPlan := by
  have h1ϕ : 0 < 1 + ϕ := by linarith
  have hA : 0 < Ybar ^ (1 - γ) := Real.rpow_pos_of_pos hY _
  have hB : 0 < Ybar ^ (1 + ϕ) / (1 + ϕ) := div_pos (Real.rpow_pos_of_pos hY _) h1ϕ
  have hf : f1 ε (ε * (1 + ϕ)) (Ybar ^ (1 - γ)) (Ybar ^ (1 + ϕ) / (1 + ϕ)) = 0 := by
    simp only [f1]
    field_simp
    linarith
  obtain ⟨ρ0, hρ0, hopt⟩ := optimal_near_ss (S := S) hβ hβ1 hε (by nlinarith) hφ hA hB hf
  set m : ℝ × ℝ → ℝ × ℝ × ℝ := fun p => (Ybar ^ (1 - γ) * Real.exp ((1 - γ) * p.1),
    Ybar ^ (1 + ϕ) * Real.exp ((1 + ϕ) * p.1) / (1 + ϕ), p.2) with hm
  have hm0 : m (0, 0) = (Ybar ^ (1 - γ), Ybar ^ (1 + ϕ) / (1 + ϕ), 0) := by
    simp [hm]
  have hmc : Continuous m := by rw [hm]; fun_prop
  obtain ⟨ρ, hρ, hρm⟩ := Metric.continuousAt_iff.1 hmc.continuousAt ρ0 hρ0
  rw [hm0] at hρm
  refine ⟨ρ, hρ, fun x π hx hπ hxπ hpc => ?_⟩
  refine hopt _ ?_ (fun t => (hxπ t).mono fun ω h => ?_) fun t =>
    (symFOC_iff_nonlinPC hφ.ne' h1ϕ.ne' hss).2 (hpc t)
  · exact (yeoData_reg hx hπ (fun t => ⟨ρ, (hxπ t).mono fun _ h => h.1.le⟩)
      fun t => ⟨ρ, (hxπ t).mono fun _ h => h.2.le⟩).1
  · have := hρm (x := (x t ω, π t ω)) (by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
      exact max_lt h.1 h.2)
    exact this

end Cochrane.KeynesianStickyPrices.TidyR6RotembergLocal
