/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.Links

/-!
# E13 as the limit of one economy

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.4, p. 57 ((3.9)–(3.11),
"these equivalent expressions"), and §3.6.4 with Online Appendix A1.6, p. 79 and pp. 567–568
((3.52)–(3.54)); survey error E13.

`Links.e13_discrete_and_continuous` put a discrete counterexample (`Money.money_bubble`) next to a
continuous one (`ContinuousMoney.printing_without_interest_example`). Here the two are one
economy. The continuous economy `C` has `P ≡ 1`, nominal rate `ι`, nominal discount factor
`N(τ) = e^{−ιτ}`, no bonds, money `M(τ) = e^{ιτ}` and money-financed deficits
`s(τ) = −ιe^{ιτ}`; in it (3.53) holds and (3.54) fails at every date. For every period length
`h > 0` its discretisation `D_h` samples `C` on the grid `nh`:

`Λ_n = N(nh)`, `P_n = 1`, `1 + i_h = e^{ιh}`, `B ≡ 0`, `M_n = M(nh)`, `s_n = M_n − M_{n+1}`.

We prove (`e13_one_economy`): every `D_h` satisfies the standing assumptions of `Money` and the
flow (3.9); in every `D_h`, (3.11) holds at every date, (3.10) fails at every date and the money
transversality condition fails (`discrete_e13`); the discrete objects are exact samples of the
continuous ones and the gap between `(B + M)/P` and the present value in (3.10) equals the
continuous (3.54) gap `M(nh)` (`sample_eq`, `gap_eq`); and as `h → 0⁺` the per-unit-time
discrete flows converge to the continuous ones at every date `τ ≥ 0` (grid date `⌊τ/h⌋h`):
the nominal rate `i_h/h → ι`, the surplus `s_n/h → s(τ)`, seigniorage
`(M_{n+1} − M_n)/(hP_n) → M'(τ)` and interest saving `i_h/(1 + i_h)·M_{n+1}/(hP_n) → ιM(τ)`
(`limits`).
-/

namespace Cochrane.Generality.TidyR6E13Limit

open Filter Topology MeasureTheory

/-! ### The discretised economy -/

/-- Cochrane (2023), p. 55 and A1.6: the real discount factor of `D_h`, `Λ_n = e^{−ι nh}`. -/
noncomputable def lamD (ι h : ℝ) : ℕ → Unit → ℝ := fun n _ => Real.exp (-(ι * (n * h)))

/-- Cochrane (2023), §3.4: the price level of `D_h`, `P ≡ 1`. -/
def priceD : ℕ → Unit → ℝ := fun _ _ => 1

/-- Cochrane (2023), §3.4 and A1.6: the per-period nominal rate of `D_h`, `1 + i_h = e^{ιh}`. -/
noncomputable def rateD (ι h : ℝ) : ℕ → Unit → ℝ := fun _ _ => Real.exp (ι * h) - 1

/-- Cochrane (2023), §3.4 and A1.6: money in `D_h`, `M_n = e^{ι nh}` (held overnight from
`n − 1`). -/
noncomputable def moneyD (ι h : ℝ) : ℕ → Unit → ℝ := fun n _ => Real.exp (ι * (n * h))

/-- Cochrane (2023), §3.4: no bonds, `B ≡ 0`. -/
def bondsD : ℕ → Unit → ℝ := fun _ _ => 0

/-- Cochrane (2023), (3.9), p. 57: money-financed deficits `s_n = M_n − M_{n+1}`. -/
noncomputable def surplusD (ι h : ℝ) : ℕ → Unit → ℝ :=
  fun n ω => moneyD ι h n ω - moneyD ι h (n + 1) ω

/-- Cochrane (2023), §3.4: `M_{n+1} = e^{ιh} M_n`. -/
theorem moneyD_succ (ι h : ℝ) (n : ℕ) (ω : Unit) :
    moneyD ι h (n + 1) ω = Real.exp (ι * h) * moneyD ι h n ω := by
  simp only [moneyD, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Cochrane (2023), (3.10), p. 58: in `D_h` the (3.10) integrand vanishes. -/
theorem term10_zero (ι h : ℝ) (n : ℕ) (ω : Unit) :
    Money.term10 priceD (surplusD ι h) (rateD ι h) (moneyD ι h) n ω = 0 := by
  simp only [Money.term10, surplusD, priceD, rateD, moneyD_succ, div_one]
  have he : Real.exp (ι * h) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

/-- Cochrane (2023), (3.11), p. 58: in `D_h` the (3.11) integrand vanishes. -/
theorem term11_zero (ι h : ℝ) (n : ℕ) (ω : Unit) :
    Money.term11 priceD (surplusD ι h) (moneyD ι h) n ω = 0 := by
  simp only [Money.term11, surplusD, priceD, div_one]
  ring

/-- Cochrane (2023), §3.3–3.4, pp. 55–59: every discretisation `D_h` satisfies the standing
assumptions of the money chain (`Money.Standing`) under perfect foresight. -/
theorem standing (ι h : ℝ) :
    Money.Standing perfectForesight (lamD ι h) priceD (rateD ι h) (moneyD ι h) bondsD where
  pullOut := perfectForesight_pullOut
  disc_pos := fun _ _ => Real.exp_pos _
  price_pos := fun _ _ => one_pos
  nominal_adapted := fun _ => rfl
  disc_inv_adapted := fun _ => rfl
  bonds_adapted := fun _ => rfl
  money_adapted := fun _ => rfl
  bonds_pre := fun _ => rfl
  money_pre := fun _ => rfl
  rate_gt := fun _ _ => by
    simp only [rateD]
    linarith [Real.exp_pos (ι * h)]
  euler := fun t => by
    funext ω
    change 1 / (1 + (Real.exp (ι * h) - 1)) =
      Real.exp (-(ι * ((t + 1 : ℕ) * h))) / Real.exp (-(ι * (t * h))) * (1 / 1)
    rw [div_one, mul_one, ← Real.exp_sub, add_sub_cancel, one_div, ← Real.exp_neg]
    congr 1
    push_cast
    ring

/-- Cochrane (2023), (3.9), p. 57: every `D_h` satisfies the flow condition. -/
theorem flow (ι h : ℝ) : Money.Flow39 priceD (surplusD ι h) (rateD ι h) (moneyD ι h) bondsD := by
  intro t ω
  simp only [priceD, surplusD, bondsD]
  ring

/-- Cochrane (2023), p. 57 (survey E13), in every discretisation `D_h`: (3.11) holds at every
date, (3.10) fails at every date, and the money transversality condition fails at every date
(the discount-weighted real money stock is `1` at every horizon). -/
theorem discrete_e13 (ι h : ℝ) :
    (∀ t, Money.PVRel perfectForesight (lamD ι h) priceD bondsD
        (Money.term11 priceD (surplusD ι h) (moneyD ι h)) t ()) ∧
      (∀ t, ¬ Money.PVRel perfectForesight (lamD ι h) priceD (bondsD + moneyD ι h)
        (Money.term10 priceD (surplusD ι h) (rateD ι h) (moneyD ι h)) t ()) ∧
      (∀ t, ¬ Money.TVC perfectForesight (lamD ι h) priceD (moneyD ι h) t ()) := by
  refine ⟨fun t => ?_, fun t h10 => ?_, fun t hT => ?_⟩
  · unfold Money.PVRel
    change bondsD t () / priceD t () = ∑' j, lamD ι h (t + j) () / lamD ι h t () *
      Money.term11 priceD (surplusD ι h) (moneyD ι h) (t + j) ()
    simp only [term11_zero, mul_zero, tsum_zero, bondsD, priceD, div_one]
  · unfold Money.PVRel at h10
    change (bondsD t () + moneyD ι h t ()) / priceD t () = ∑' j, lamD ι h (t + j) () /
      lamD ι h t () * Money.term10 priceD (surplusD ι h) (rateD ι h) (moneyD ι h) (t + j) ()
      at h10
    simp only [term10_zero, mul_zero, tsum_zero, bondsD, priceD, div_one, zero_add] at h10
    exact (Real.exp_pos _).ne' h10
  · unfold Money.TVC at hT
    have h1 : ∀ T, perfectForesight.E t (fun ω' => lamD ι h (t + T) ω' *
        (moneyD ι h (t + T) ω' / priceD (t + T) ω')) () = 1 := by
      intro T
      change lamD ι h (t + T) () * (moneyD ι h (t + T) () / priceD (t + T) ()) = 1
      simp only [lamD, moneyD, priceD, div_one, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    simp only [h1] at hT
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hT)

/-! ### Samples and limits -/

/-- Cochrane (2023), A1.6: the continuous economy's paths (`ContinuousMoney`'s example):
`N(τ) = e^{−ιτ}`, `M(τ) = e^{ιτ}`, `s(τ) = −ιe^{ιτ}`, `P ≡ 1`. -/
noncomputable def contN (ι τ : ℝ) : ℝ := Real.exp (-(ι * τ))

/-- Cochrane (2023), A1.6: continuous money `M(τ) = e^{ιτ}`. -/
noncomputable def contM (ι τ : ℝ) : ℝ := Real.exp (ι * τ)

/-- Cochrane (2023), A1.6: continuous surpluses `s(τ) = −ιe^{ιτ}`. -/
noncomputable def contS (ι τ : ℝ) : ℝ := -(ι * Real.exp (ι * τ))

/-- Cochrane (2023), A1.6: `D_h` samples `C` exactly on the grid: `Λ_n = N(nh)P(nh)`,
`M_n = M(nh)`, `P_n = P(nh) = 1`, and `s_n = M(nh) − M((n+1)h)`. -/
theorem sample_eq (ι h : ℝ) (n : ℕ) :
    lamD ι h n () = contN ι (n * h) * 1 ∧ moneyD ι h n () = contM ι (n * h) ∧
      priceD n () = 1 ∧
      surplusD ι h n () = contM ι (n * h) - contM ι ((n + 1 : ℕ) * h) := by
  refine ⟨by simp [lamD, contN], rfl, rfl, rfl⟩

/-- Cochrane (2023), p. 57 and A1.6 (E13): the failure of (3.10) in `D_h` at date `n` is exactly
the failure of (3.54) in `C` at date `nh`: `(B_n + M_n)/P_n − ∑_j (Λ_{n+j}/Λ_n)·term10 =
M(nh) = (M(nh) + 0)/1 − ∫_{nh}^∞ (N_τ/N_{nh})(s_τ + ιM_τ)dτ`. -/
theorem gap_eq (ι h : ℝ) (n : ℕ) :
    (bondsD n () + moneyD ι h n ()) / priceD n () - ∑' j, lamD ι h (n + j) () / lamD ι h n () *
        Money.term10 priceD (surplusD ι h) (rateD ι h) (moneyD ι h) (n + j) () =
      (contM ι (n * h) + 0) / 1 - ∫ τ in Set.Ioi ((n : ℝ) * h), contN ι τ * 1 /
        (contN ι (n * h) * 1) * (contS ι τ + (ι - 0) * contM ι τ / 1) := by
  have hz : ∀ τ, contS ι τ + (ι - 0) * contM ι τ / 1 = 0 := fun τ => by
    simp only [contS, contM]
    ring
  simp only [hz, mul_zero, integral_zero]
  simp only [term10_zero, mul_zero, tsum_zero, bondsD, priceD, moneyD, contM, sub_zero, div_one,
    zero_add, add_zero]

/-- Cochrane (2023), A1.6 (auxiliary): the grid date `⌊τ/h⌋h` tends to `τ ≥ 0` as `h → 0⁺`. -/
theorem tendsto_grid {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun h : ℝ => (⌊τ / h⌋₊ : ℝ) * h) (𝓝[>] 0) (𝓝 τ) := by
  have hlo : Tendsto (fun h : ℝ => τ - h) (𝓝[>] 0) (𝓝 τ) := by
    have h1 : Tendsto (fun h : ℝ => τ - h) (𝓝 0) (𝓝 (τ - 0)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (0 : ℝ) < h := hh
    have h1 := Nat.lt_floor_add_one (τ / h)
    have h2 := mul_lt_mul_of_pos_right h1 hh'
    rw [add_mul, div_mul_cancel₀ _ hh'.ne', one_mul] at h2
    linarith
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh' : (0 : ℝ) < h := hh
    have h1 := Nat.floor_le (div_nonneg hτ hh'.le)
    exact (le_div_iff₀ hh').mp h1

/-- Cochrane (2023), A1.6 (auxiliary): `(e^{ah} − 1)/h → a` as `h → 0⁺`. -/
theorem tendsto_expm1_div (a : ℝ) :
    Tendsto (fun h : ℝ => (Real.exp (a * h) - 1) / h) (𝓝[>] 0) (𝓝 a) := by
  have h1 := (Links.tendsto_slope_exp_sub a 0).mono_left
    (nhdsWithin_mono _ fun x hx => (Set.mem_Ioi.mp hx).ne')
  simpa using h1

/-- Cochrane (2023), (3.9)–(3.11), (3.52)–(3.54), A1.6: **the discrete flows converge to the
continuous ones.** At every date `τ ≥ 0`, with grid index `n = ⌊τ/h⌋`, as `h → 0⁺`: the nominal
rate per unit of time `i_h/h → ι`; the surplus per unit of time `s_n/h → s(τ) = −ιe^{ιτ}`;
seigniorage per unit of time `(M_{n+1} − M_n)/(hP_n) → M'(τ) = ιe^{ιτ}`; and interest saving per
unit of time `(i_h/(1 + i_h))M_{n+1}/(hP_n) → ιM(τ)`; the discount factor and money stock at the
grid date tend to `N(τ)` and `M(τ)`. -/
theorem limits (ι : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun h => rateD ι h 0 () / h) (𝓝[>] 0) (𝓝 ι) ∧
      Tendsto (fun h => surplusD ι h ⌊τ / h⌋₊ () / h) (𝓝[>] 0) (𝓝 (contS ι τ)) ∧
      Tendsto (fun h => (moneyD ι h (⌊τ / h⌋₊ + 1) () - moneyD ι h ⌊τ / h⌋₊ ()) /
        (h * priceD ⌊τ / h⌋₊ ())) (𝓝[>] 0) (𝓝 (ι * contM ι τ)) ∧
      Tendsto (fun h => rateD ι h ⌊τ / h⌋₊ () / (1 + rateD ι h ⌊τ / h⌋₊ ()) *
        moneyD ι h (⌊τ / h⌋₊ + 1) () / (h * priceD ⌊τ / h⌋₊ ())) (𝓝[>] 0)
        (𝓝 (ι * contM ι τ)) ∧
      Tendsto (fun h => lamD ι h ⌊τ / h⌋₊ ()) (𝓝[>] 0) (𝓝 (contN ι τ)) ∧
      Tendsto (fun h => moneyD ι h ⌊τ / h⌋₊ ()) (𝓝[>] 0) (𝓝 (contM ι τ)) := by
  have hg := tendsto_grid hτ
  have hM : Tendsto (fun h : ℝ => Real.exp (ι * ((⌊τ / h⌋₊ : ℝ) * h))) (𝓝[>] 0)
      (𝓝 (contM ι τ)) :=
    (Real.continuous_exp.tendsto _).comp (hg.const_mul ι)
  have hN : Tendsto (fun h : ℝ => Real.exp (-(ι * ((⌊τ / h⌋₊ : ℝ) * h)))) (𝓝[>] 0)
      (𝓝 (contN ι τ)) :=
    (Real.continuous_exp.tendsto _).comp (hg.const_mul ι).neg
  have hr := tendsto_expm1_div ι
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  refine ⟨hr, ?_, ?_, ?_, hN, hM⟩
  · have h1 := hM.mul hr.neg
    refine (h1.congr' ?_).trans (by rw [contS, contM]; ring_nf; exact le_rfl)
    filter_upwards [hpos] with h hh
    simp only [surplusD]
    rw [moneyD_succ]
    simp only [moneyD]
    field_simp
    ring
  · have h1 := hr.mul hM
    refine h1.congr' ?_
    filter_upwards [hpos] with h hh
    rw [moneyD_succ]
    simp only [moneyD, priceD, mul_one]
    field_simp
  · have h1 := hr.mul hM
    refine h1.congr' ?_
    filter_upwards [hpos] with h hh
    have he : Real.exp (ι * h) ≠ 0 := (Real.exp_pos _).ne'
    rw [moneyD_succ]
    simp only [moneyD, priceD, rateD, mul_one, add_sub_cancel]
    field_simp

/-- Cochrane (2023), p. 57, §3.6.4 and A1.6 (survey E13), **one economy**: the continuous economy
`C` violates the equivalence of (3.53) and (3.54) at every date
(`ContinuousMoney.printing_without_interest_example`), every discretisation `D_h` of `C` is a
discrete economy satisfying `Money.Standing` and (3.9) in which (3.11) holds and (3.10) fails at
every date with the money transversality condition failing (`discrete_e13`), `D_h` samples `C`
exactly with the same (3.10)/(3.54) gap (`sample_eq`, `gap_eq`), and the per-unit-time discrete
flows converge to the continuous ones as `h → 0⁺` (`limits`). -/
theorem e13_one_economy (ι : ℝ) :
    (∀ τ, (0 : ℝ) / 1 = ∫ u in Set.Ioi τ, contN ι u * 1 / (contN ι τ * 1) *
        (contS ι u + ι * contM ι u / 1) ∧
      (contM ι τ + 0) / 1 ≠ ∫ u in Set.Ioi τ, contN ι u * 1 / (contN ι τ * 1) *
        (contS ι u + (ι - 0) * contM ι u / 1)) ∧
    (∀ h, Money.Standing perfectForesight (lamD ι h) priceD (rateD ι h) (moneyD ι h) bondsD ∧
      Money.Flow39 priceD (surplusD ι h) (rateD ι h) (moneyD ι h) bondsD ∧
      (∀ t, Money.PVRel perfectForesight (lamD ι h) priceD bondsD
        (Money.term11 priceD (surplusD ι h) (moneyD ι h)) t ()) ∧
      (∀ t, ¬ Money.PVRel perfectForesight (lamD ι h) priceD (bondsD + moneyD ι h)
        (Money.term10 priceD (surplusD ι h) (rateD ι h) (moneyD ι h)) t ()) ∧
      (∀ t, ¬ Money.TVC perfectForesight (lamD ι h) priceD (moneyD ι h) t ())) ∧
    (∀ τ, 0 ≤ τ →
      Tendsto (fun h => surplusD ι h ⌊τ / h⌋₊ () / h) (𝓝[>] 0) (𝓝 (contS ι τ)) ∧
      Tendsto (fun h => (moneyD ι h (⌊τ / h⌋₊ + 1) () - moneyD ι h ⌊τ / h⌋₊ ()) /
        (h * priceD ⌊τ / h⌋₊ ())) (𝓝[>] 0) (𝓝 (ι * contM ι τ)) ∧
      Tendsto (fun h => rateD ι h ⌊τ / h⌋₊ () / (1 + rateD ι h ⌊τ / h⌋₊ ()) *
        moneyD ι h (⌊τ / h⌋₊ + 1) () / (h * priceD ⌊τ / h⌋₊ ())) (𝓝[>] 0)
        (𝓝 (ι * contM ι τ))) := by
  refine ⟨fun τ => ?_, fun h => ⟨standing ι h, flow ι h, discrete_e13 ι h⟩, fun τ hτ => ?_⟩
  · have hc := ContinuousMoney.printing_without_interest_example ι τ
    exact ⟨hc.2.2.2.1, hc.2.2.2.2⟩
  · obtain ⟨-, h2, h3, h4, -, -⟩ := limits ι hτ
    exact ⟨h2, h3, h4⟩

end Cochrane.Generality.TidyR6E13Limit
