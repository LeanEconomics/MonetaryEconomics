/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR5ExpectationsMeasure

/-!
# Expectations indexed by the integers: an infinite past under uncertainty

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.2, eq. (17.8), p. 400
(the infinite past), §17.4.1, pp. 408–409 (the rise anticipated from the infinite past), with
the expectations and news of Ch. 2, §2.3–2.4, pp. 29–30, eq. (2.13).

The core `ExpectationSystem` and TidyR5ExpectationsMeasure's `MeasExpectationSystem` are indexed
by `ℕ`, so the infinite-past statements of §17.2 and §17.4 were pathwise (perfect foresight).
This module indexes information by `ℤ`.

## The abstract system

`ZExpectationSystem Ω`: operators `E_t`, `t ∈ ℤ`, with linearity, constants, monotonicity, the
law of iterated expectations and `known`, as in the core. `zPerfectForesight` is the identity.
`ZExpectationSystem.restrict s` is the core `ExpectationSystem` `n ↦ E_{s+n}` of dates `t ≥ s`
(`restrict_E`; perfect foresight restricts to `perfectForesight`, `restrict_zPerfectForesight`),
so every core theorem applies from any date `s` on. News `innov` is a martingale difference
(`E_innov`), revisions telescope (`E_sub_E_eq_sum_innov`), `E_t` passes through dominated
geometric series (`E_tsum`).

## The probability space

`ZMeasExpectationSystem Ω`: a probability measure and a filtration `𝓕 : Filtration ℤ _`
(Mathlib), `E_t x = μ[x | 𝓕 t]`. Proved: linearity, constants, monotonicity, tower
(`E_tower`), `E_known`, `E_of_stronglyMeasurable`, **pull-out** (`E_pullOut`), `abs_E_le`, the
mean (`integral_E`); news (`innov`, `E_innov`, `E_mul_innov`, `E_sub_E_eq_sum_innov`,
`eq_E_add_innov`); `E_hasSum`. The **remote past** `remote = ⨅ₜ 𝓕 t`: what is known at every date,
however early (`remote_le`, `E_of_remote`).

`ZMeasExpectationSystem.restrict s` is the `MeasExpectationSystem` with filtration
`n ↦ 𝓕 (s + n)` (`restrict_E`, `restrict_adapted`), the link through which the ℕ-indexed results
of TidyR5ExpectationsMeasure apply to the dates `t ≥ s`.

## Forward sums on ℤ

`FZ q u t = E_t ∑_{k≥0} qᵏ u_{t+k}` (`FZ_eq_restrict`: it is the ℕ forward solution of the
system restricted at any `s ≤ t`). For `|q| < 1` and bounded adapted `u`: adapted (`FZ_adapted`),
bounded by `M/(1 − |q|)` (`FZ_bdd`), it is the genuine sum `∑ qᵏ E_t u_{t+k}` (`FZ_hasSum`), solves
`z_t = q E_t z_{t+1} + u_t` (`FZ_solves`), and is the only bounded solution on ℤ
(`forwardZ_unique`, `eq_FZ`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6ZExpectations

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure

/-! ### The abstract ℤ-indexed system -/

/-- Cochrane (2023), Ch. 2, pp. 29–30, with an infinite past (§17.2, p. 400): conditional
expectations `E_t`, `t ∈ ℤ`, linear, preserving constants and order, with the law of iterated
expectations.
ℤ-indexed version of `ExpectationSystem`. -/
structure ZExpectationSystem (Ω : Type*) where
  /-- The expectation conditional on date-`t` information, `t ∈ ℤ`. -/
  E : ℤ → (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ)
  /-- Constants are known at every date. -/
  const : ∀ t (c : ℝ), E t (fun _ => c) = fun _ => c
  /-- Expectations preserve the pointwise order. -/
  mono : ∀ t {x y : Ω → ℝ}, x ≤ y → E t x ≤ E t y
  /-- The law of iterated expectations: `E_s E_t = E_s` for `s ≤ t`. -/
  tower : ∀ {s t : ℤ}, s ≤ t → ∀ x, E s (E t x) = E s x
  /-- Earlier information is known later: `E_t E_s = E_s` for `s ≤ t`. -/
  known : ∀ {s t : ℤ}, s ≤ t → ∀ x, E t (E s x) = E s x

/-- Cochrane (2023), §17.2, p. 400 and §17.4.1, p. 409 (perfect foresight with an infinite past):
a single state, `E_t` the identity at every date `t ∈ ℤ`.
ℤ-indexed version of `perfectForesight`. -/
def zPerfectForesight : ZExpectationSystem Unit where
  E := fun _ => LinearMap.id
  const := fun _ _ => rfl
  mono := fun _ _ _ h => h
  tower := fun _ _ => rfl
  known := fun _ _ => rfl

namespace ZExpectationSystem

variable {Ω : Type*} (𝔼 : ZExpectationSystem Ω)

/-- Cochrane (2023), Ch. 2, pp. 29–30: the dates `t ≥ s` of a ℤ-indexed system form a core
(ℕ-indexed) `ExpectationSystem`, `n ↦ E_{s+n}`. -/
def restrict (s : ℤ) : ExpectationSystem Ω where
  E := fun n => 𝔼.E (s + n)
  const := fun _ c => 𝔼.const _ c
  mono := fun _ _ _ h => 𝔼.mono _ h
  tower := fun h x => 𝔼.tower (add_le_add_right (Nat.cast_le.mpr h) s) x
  known := fun h x => 𝔼.known (add_le_add_right (Nat.cast_le.mpr h) s) x

/-- Cochrane (2023), Ch. 2: the restricted system at horizon `n` is `E_{s+n}`. -/
theorem restrict_E (s : ℤ) (n : ℕ) (x : Ω → ℝ) : (𝔼.restrict s).E n x = 𝔼.E (s + n) x := rfl

/-- Cochrane (2023), §17.4.1: perfect foresight on ℤ restricts to perfect foresight on ℕ. -/
theorem restrict_zPerfectForesight (s : ℤ) : zPerfectForesight.restrict s = perfectForesight :=
  rfl

/-- Cochrane (2023), Ch. 2, p. 29: a ℤ-indexed process is adapted when `E_t x_t = x_t`.
ℤ-indexed version of `ExpectationSystem.Adapted`. -/
def Adapted (x : ℤ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (x t) = x t

/-- Cochrane (2023), Ch. 2: an adapted process restricts to an adapted process from any date. -/
theorem restrict_adapted {x : ℤ → Ω → ℝ} (h : 𝔼.Adapted x) (s : ℤ) :
    (𝔼.restrict s).Adapted (fun n => x (s + n)) := fun n => h (s + n)

/-- Cochrane (2023), Ch. 2, p. 29: `|E_t x| ≤ M` whenever `|x| ≤ M`.
ℤ-indexed version of `ExpectationSystem.abs_E_le`. -/
theorem abs_E_le {M : ℝ} {x : Ω → ℝ} (hx : ∀ ω, |x ω| ≤ M) (t : ℤ) (ω : Ω) :
    |𝔼.E t x ω| ≤ M := by
  have h := (𝔼.restrict t).abs_E_le hx 0 ω
  rwa [restrict_E, Nat.cast_zero, add_zero] at h

/-- Cochrane (2023), eq. (2.13), p. 30: the news `ΔE_{t+1} x = E_{t+1} x − E_t x`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.innov`. -/
def innov (t : ℤ) (x : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) x - 𝔼.E t x

/-- Cochrane (2023), eq. (2.13), p. 30: news is a martingale difference, `E_s ΔE_{t+1} x = 0`
for `s ≤ t`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_innov`. -/
theorem E_innov {s t : ℤ} (hst : s ≤ t) (x : Ω → ℝ) : 𝔼.E s (𝔼.innov t x) = 0 := by
  rw [innov, map_sub, 𝔼.tower (hst.trans (Int.le_add_one le_rfl)), 𝔼.tower hst, sub_self]

/-- Cochrane (2023), eq. (2.13), p. 30: forecast revisions telescope into news,
`E_{t+n} x − E_t x = ∑_{i<n} ΔE_{t+i+1} x`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_sub_E_eq_sum_innov`. -/
theorem E_sub_E_eq_sum_innov (t : ℤ) (n : ℕ) (x : Ω → ℝ) :
    𝔼.E (t + n) x - 𝔼.E t x = ∑ i ∈ Finset.range n, 𝔼.innov (t + i) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, innov, Nat.cast_succ, ← add_assoc]
    abel

/-- Cochrane (2023), eq. (2.17), p. 35: a variable known at `t + 1` is its forecast plus its
news.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.eq_E_add_innov`. -/
theorem eq_E_add_innov {t : ℤ} {x : Ω → ℝ} (hx : 𝔼.E (t + 1) x = x) :
    x = 𝔼.E t x + 𝔼.innov t x := by
  rw [innov, hx]
  abel

/-- Cochrane (2023), Ch. 2, p. 29: the pull-out property on ℤ (not implied by the axioms; a
hypothesis where needed, as in the core `ExpectationSystem.PullOut`). -/
def PullOut : Prop := ∀ t (a y : Ω → ℝ), 𝔼.E t a = a → 𝔼.E t (a * y) = a * 𝔼.E t y

/-- Cochrane (2023), §17.4.1: perfect foresight on ℤ has the pull-out property.
ℤ-indexed version of `perfectForesight_pullOut`. -/
theorem zPerfectForesight_pullOut : zPerfectForesight.PullOut := fun _ _ _ _ => rfl

/-- Cochrane (2023), Ch. 2, p. 29 (present values): `E_t` commutes with a series dominated by
`aᵏ M`, `0 ≤ a < 1`, at every date `t ∈ ℤ`.
ℤ-indexed version of `ExpectationSystem.E_tsum`. -/
theorem E_tsum {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → Ω → ℝ}
    (hf : ∀ k ω, |f k ω| ≤ a ^ k * M) (t : ℤ) (ω : Ω) :
    𝔼.E t (fun ω' => ∑' k, f k ω') ω = ∑' k, 𝔼.E t (f k) ω := by
  have h := (𝔼.restrict t).E_tsum ha0 ha1 hf 0 ω
  simpa only [restrict_E, Nat.cast_zero, add_zero] using h

end ZExpectationSystem

/-! ### The probability space with a ℤ-indexed filtration -/

variable (Ω : Type*) [mΩ : MeasurableSpace Ω]

/-- Cochrane (2023), Ch. 2, pp. 29–30, with an infinite past (§17.2, p. 400): a probability space
with a filtration `𝓕 : ℤ → MeasurableSpace Ω` indexed by all dates; `E_t x := P[x | 𝓕 t]`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem`. -/
structure ZMeasExpectationSystem where
  /-- The probability measure. -/
  P : ProbabilityMeasure Ω
  /-- The information available at each date `t ∈ ℤ`. -/
  𝓕 : Filtration ℤ mΩ

namespace ZMeasExpectationSystem

variable {Ω} (S : ZMeasExpectationSystem Ω)

/-- Cochrane (2023), Ch. 2, p. 29: the probability measure as a measure.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.μ`. -/
abbrev μ : Measure Ω := S.P

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x = μ[x | 𝓕 t]`, `t ∈ ℤ`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E`. -/
noncomputable abbrev E (t : ℤ) (x : Ω → ℝ) : Ω → ℝ := S.μ[x | S.𝓕 t]

/-- Cochrane (2023), Ch. 2, pp. 29–30: the filtration `n ↦ 𝓕 (s + n)` of the dates `t ≥ s`. -/
def restrictF (s : ℤ) : Filtration ℕ mΩ where
  seq := fun n => S.𝓕 (s + n)
  mono' := fun _ _ h => S.𝓕.mono (add_le_add_right (Nat.cast_le.mpr h) s)
  le' := fun _ => S.𝓕.le _

/-- Cochrane (2023), Ch. 2, pp. 29–30: the dates `t ≥ s` as an ℕ-indexed
`TidyR5ExpectationsMeasure.MeasExpectationSystem`. -/
def restrict (s : ℤ) : MeasExpectationSystem Ω := ⟨S.P, S.restrictF s⟩

/-- Cochrane (2023), Ch. 2: the restricted system has the same measure. -/
theorem restrict_μ (s : ℤ) : (S.restrict s).μ = S.μ := rfl

/-- Cochrane (2023), Ch. 2: the restricted information at horizon `n` is `𝓕 (s + n)`. -/
theorem restrict_𝓕 (s : ℤ) (n : ℕ) : (S.restrict s).𝓕 n = S.𝓕 (s + n) := rfl

/-- Cochrane (2023), Ch. 2: the restricted expectation at horizon `n` is `E_{s+n}`. -/
theorem restrict_E (s : ℤ) (n : ℕ) (x : Ω → ℝ) : (S.restrict s).E n x = S.E (s + n) x := rfl

/-- Cochrane (2023), Ch. 2: an adapted ℤ-indexed process restricts to an adapted process. -/
theorem restrict_adapted {x : ℤ → Ω → ℝ} (h : StronglyAdapted S.𝓕 x) (s : ℤ) :
    StronglyAdapted (S.restrict s).𝓕 (fun n => x (s + n)) := fun n => h (s + n)

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is additive (a.e.).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_add`. -/
theorem E_add {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℤ) :
    S.E t (x + y) =ᵐ[S.μ] S.E t x + S.E t y := condExp_add hx hy _

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` commutes with differences (a.e.).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_sub`. -/
theorem E_sub {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℤ) :
    S.E t (x - y) =ᵐ[S.μ] S.E t x - S.E t y := condExp_sub hx hy _

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is homogeneous (a.e.).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_smul`. -/
theorem E_smul (c : ℝ) (x : Ω → ℝ) (t : ℤ) : S.E t (c • x) =ᵐ[S.μ] c • S.E t x :=
  condExp_smul c x _

/-- Cochrane (2023), Ch. 2, pp. 29–30: constants are known (exactly).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_const`. -/
theorem E_const (t : ℤ) (c : ℝ) : S.E t (fun _ => c) = fun _ => c :=
  condExp_const (S.𝓕.le t) c

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is monotone (a.e.).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_mono`. -/
theorem E_mono {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ)
    (hxy : x ≤ᵐ[S.μ] y) (t : ℤ) : S.E t x ≤ᵐ[S.μ] S.E t y := condExp_mono hx hy hxy

/-- Cochrane (2023), Ch. 2, pp. 29–30: the law of iterated expectations, `E_s E_t = E_s` for
`s ≤ t` in `ℤ` (a.e.).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_tower`. -/
theorem E_tower {s t : ℤ} (hst : s ≤ t) (x : Ω → ℝ) : S.E s (S.E t x) =ᵐ[S.μ] S.E s x :=
  condExp_condExp_of_le (S.𝓕.mono hst) (S.𝓕.le t)

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x` is `𝓕 t`-strongly measurable.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_E`. -/
theorem stronglyMeasurable_E (t : ℤ) (x : Ω → ℝ) : StronglyMeasurable[S.𝓕 t] (S.E t x) :=
  stronglyMeasurable_condExp

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x` is integrable.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.integrable_E`. -/
theorem integrable_E (t : ℤ) (x : Ω → ℝ) : Integrable (S.E t x) S.μ := integrable_condExp

/-- Cochrane (2023), Ch. 2, pp. 29–30: what is known at `t` is its own forecast (exactly).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_of_stronglyMeasurable`. -/
theorem E_of_stronglyMeasurable {t : ℤ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    (hi : Integrable x S.μ) : S.E t x = x :=
  condExp_of_stronglyMeasurable (S.𝓕.le t) hx hi

/-- Cochrane (2023), Ch. 2, pp. 29–30: earlier forecasts are known later, `E_t E_s = E_s`,
`s ≤ t` (exactly).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_known`. -/
theorem E_known {s t : ℤ} (hst : s ≤ t) (x : Ω → ℝ) : S.E t (S.E s x) = S.E s x :=
  S.E_of_stronglyMeasurable ((S.stronglyMeasurable_E s x).mono (S.𝓕.mono hst))
    (S.integrable_E s x)

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is idempotent (exactly).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_E_self`. -/
theorem E_E_self (t : ℤ) (x : Ω → ℝ) : S.E t (S.E t x) = S.E t x := S.E_known le_rfl x

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` respects a.e. equality.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_congr`. -/
theorem E_congr {x y : Ω → ℝ} (h : x =ᵐ[S.μ] y) (t : ℤ) : S.E t x =ᵐ[S.μ] S.E t y :=
  condExp_congr_ae h

/-- Cochrane (2023), Ch. 2, pp. 29–30: the unconditional mean of a forecast is the mean.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.integral_E`. -/
theorem integral_E (t : ℤ) (x : Ω → ℝ) : ∫ ω, S.E t x ω ∂S.μ = ∫ ω, x ω ∂S.μ :=
  integral_condExp (S.𝓕.le t)

/-- Cochrane (2023), Ch. 2, pp. 29–30: **pull-out** — a bounded factor known at `t` comes out of
`E_t` (a.e.).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_pullOut`. -/
theorem E_pullOut {t : ℤ} {f y : Ω → ℝ} (hf : StronglyMeasurable[S.𝓕 t] f) {C : ℝ}
    (hfC : ∀ᵐ ω ∂S.μ, |f ω| ≤ C) (hy : Integrable y S.μ) :
    S.E t (f * y) =ᵐ[S.μ] f * S.E t y := by
  have hint : Integrable (f * y) S.μ :=
    hy.bdd_mul (hf.mono (S.𝓕.le t)).aestronglyMeasurable
      (hfC.mono fun ω h => by rwa [Real.norm_eq_abs])
  exact condExp_mul_of_stronglyMeasurable_left hf hint hy

/-- Cochrane (2023), Ch. 2, pp. 29–30: `|E_t x| ≤ M` a.e. whenever `|x| ≤ M` a.e.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.abs_E_le`. -/
theorem abs_E_le {x : Ω → ℝ} {M : ℝ} (hx : ∀ᵐ ω ∂S.μ, |x ω| ≤ M) (t : ℤ) :
    ∀ᵐ ω ∂S.μ, |S.E t x ω| ≤ M :=
  ae_bdd_abs_condExp_of_ae_bdd_abs hx

/-- Cochrane (2023), Ch. 2, p. 29: a variable known at `t` with an a.e. bound is integrable. -/
theorem integrable_of_bdd {t : ℤ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x) {M : ℝ}
    (hM : ∀ᵐ ω ∂S.μ, |x ω| ≤ M) : Integrable x S.μ :=
  Integrable.of_bound (hx.mono (S.𝓕.le t)).aestronglyMeasurable M
    (hM.mono fun ω h => by rwa [Real.norm_eq_abs])

/-! ### The remote past -/

/-- Cochrane (2023), §17.2, p. 400 (the infinite past): the **remote past** `⨅ₜ 𝓕 t`, the
information available at every date, however early. -/
abbrev remote : MeasurableSpace Ω := ⨅ t, S.𝓕 t

/-- Cochrane (2023), §17.2: the remote past is known at every date. -/
theorem remote_le (t : ℤ) : S.remote ≤ S.𝓕 t := iInf_le _ t

/-- Cochrane (2023), §17.2: a variable measurable for the remote past is its own forecast at every
date. -/
theorem E_of_remote {c : Ω → ℝ} (hc : StronglyMeasurable[S.remote] c) (hi : Integrable c S.μ)
    (t : ℤ) : S.E t c = c :=
  S.E_of_stronglyMeasurable (hc.mono (S.remote_le t)) hi

/-! ### News -/

/-- Cochrane (2023), eq. (2.13), p. 30: the innovation `ΔE_{t+1} x = E_{t+1} x − E_t x`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.innov`. -/
noncomputable def innov (t : ℤ) (x : Ω → ℝ) : Ω → ℝ := S.E (t + 1) x - S.E t x

/-- Cochrane (2023), eq. (2.13), p. 30: the innovation is known at `t + 1`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.stronglyMeasurable_innov`. -/
theorem stronglyMeasurable_innov (t : ℤ) (x : Ω → ℝ) :
    StronglyMeasurable[S.𝓕 (t + 1)] (S.innov t x) :=
  (S.stronglyMeasurable_E (t + 1) x).sub
    ((S.stronglyMeasurable_E t x).mono (S.𝓕.mono (Int.le_add_one le_rfl)))

/-- Cochrane (2023), eq. (2.13), p. 30: **innovations are martingale differences**,
`E_s ΔE_{t+1} x = 0` a.e. for `s ≤ t` in `ℤ`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_innov`. -/
theorem E_innov {s t : ℤ} (hst : s ≤ t) (x : Ω → ℝ) : S.E s (S.innov t x) =ᵐ[S.μ] 0 := by
  filter_upwards [S.E_sub (S.integrable_E (t + 1) x) (S.integrable_E t x) s,
    S.E_tower (hst.trans (Int.le_add_one le_rfl)) x, S.E_tower hst x] with ω h1 h2 h3
  rw [innov, h1, Pi.sub_apply, h2, h3, sub_self, Pi.zero_apply]

/-- Cochrane (2023), eq. (2.13), p. 30: news is uncorrelated with anything known before it,
`E_t (w ΔE_{t+1} x) = 0` for bounded `w` known at `t`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_mul_innov`. -/
theorem E_mul_innov {t : ℤ} {w : Ω → ℝ} (hw : StronglyMeasurable[S.𝓕 t] w) {C : ℝ}
    (hwC : ∀ᵐ ω ∂S.μ, |w ω| ≤ C) (x : Ω → ℝ) :
    S.E t (w * S.innov t x) =ᵐ[S.μ] 0 := by
  have hi : Integrable (S.innov t x) S.μ := (S.integrable_E _ x).sub (S.integrable_E _ x)
  filter_upwards [S.E_pullOut hw hwC hi, S.E_innov le_rfl x] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]
  simp

/-- Cochrane (2023), eq. (2.13), p. 30: forecast revisions telescope into news,
`E_{t+n} x − E_t x = ∑_{i<n} ΔE_{t+i+1} x` (exactly).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_sub_E_eq_sum_innov`. -/
theorem E_sub_E_eq_sum_innov (t : ℤ) (n : ℕ) (x : Ω → ℝ) :
    S.E (t + n) x - S.E t x = ∑ i ∈ Finset.range n, S.innov (t + i) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, innov, Nat.cast_succ, ← add_assoc]
    abel

/-- Cochrane (2023), eq. (2.17), p. 35: a variable known at `t + 1` is its forecast plus its
news (exactly).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.eq_E_add_innov`. -/
theorem eq_E_add_innov {t : ℤ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 (t + 1)] x)
    (hi : Integrable x S.μ) : x = S.E t x + S.innov t x := by
  rw [innov, S.E_of_stronglyMeasurable hx hi]
  abel

/-- Cochrane (2023), Ch. 2, p. 29 (present values): `E_t` passes through a dominated series at
every date `t ∈ ℤ` (a.e., as a genuine `HasSum`).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.E_hasSum`. -/
theorem E_hasSum {f : ℕ → Ω → ℝ} {c : ℕ → ℝ} (hc : Summable c)
    (hm : ∀ k, AEStronglyMeasurable (f k) S.μ) (hf : ∀ k, ∀ᵐ ω ∂S.μ, |f k ω| ≤ c k) (t : ℤ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => S.E t (f k) ω) (S.E t (fun ω' => ∑' k, f k ω') ω) := by
  have h := (S.restrict t).E_hasSum hc hm hf 0
  simpa only [restrict_E, restrict_μ, Nat.cast_zero, add_zero] using h

/-! ### Forward sums on ℤ -/

/-- Cochrane (2023), Ch. 2, p. 29 and eq. (5.5), p. 119: the forward sum on ℤ,
`F_t = E_t ∑_{k≥0} qᵏ u_{t+k}`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.forwardSol`. -/
noncomputable def FZ (q : ℝ) (u : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  S.E t (fun ω => ∑' k : ℕ, q ^ k * u (t + k) ω)

/-- Cochrane (2023), eq. (5.5): the forward sum on ℤ at `s + n` is the ℕ forward solution of the
system restricted at `s`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.forwardSol`. -/
theorem FZ_eq_restrict (q : ℝ) (u : ℤ → Ω → ℝ) (s : ℤ) (n : ℕ) :
    S.FZ q u (s + n) = (S.restrict s).forwardSol q (fun m => u (s + m)) n := by
  unfold FZ MeasExpectationSystem.forwardSol MeasExpectationSystem.discSum
  rw [restrict_E]
  congr 1
  funext ω
  refine tsum_congr fun k => ?_
  simp only [Nat.cast_add, add_assoc]

/-- Cochrane (2023), eq. (5.5): the forward sum is adapted.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.forwardSol_adapted`. -/
theorem FZ_adapted (q : ℝ) (u : ℤ → Ω → ℝ) : StronglyAdapted S.𝓕 (S.FZ q u) :=
  fun t => S.stronglyMeasurable_E t _

/-- Cochrane (2023), eq. (5.5): for `|q| < 1` the forward sum of a process bounded by `M` is
bounded by `M/(1 − |q|)` a.e.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.forwardSol_bdd`. -/
theorem FZ_bdd {q M : ℝ} (hq : |q| < 1) {u : ℤ → Ω → ℝ} (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M)
    (t : ℤ) : ∀ᵐ ω ∂S.μ, |S.FZ q u t ω| ≤ M / (1 - |q|) := by
  have h := (S.restrict t).forwardSol_bdd hq (u := fun m => u (t + m)) (fun m => hb (t + m))
  obtain ⟨K, hK⟩ := h
  have e := S.FZ_eq_restrict q u t 0
  rw [Nat.cast_zero, add_zero] at e
  rw [e]
  unfold MeasExpectationSystem.forwardSol
  exact (S.restrict t).abs_E_le ((S.restrict t).discSum_bdd hq (fun m => hb (t + m)) 0) 0

/-- Cochrane (2023), eq. (5.5), p. 119: for `|q| < 1` and bounded `u`, the forward sum is the
genuine sum `∑ qᵏ E_t u_{t+k}` (a.e.).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.forwardSol_hasSum`. -/
theorem FZ_hasSum {q M : ℝ} (hq : |q| < 1) {u : ℤ → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) S.μ) (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℤ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k : ℕ => q ^ k * S.E t (u (t + k)) ω) (S.FZ q u t ω) := by
  have h := (S.restrict t).forwardSol_hasSum hq (u := fun m => u (t + m)) (fun m => hm (t + m))
    (fun m => hb (t + m)) 0
  have e := S.FZ_eq_restrict q u t 0
  rw [Nat.cast_zero, add_zero] at e
  rw [e]
  simpa only [restrict_E, restrict_μ, Nat.cast_zero, add_zero, zero_add] using h

/-- Cochrane (2023), Ch. 2, p. 29: `z` solves `z_t = q E_t z_{t+1} + u_t` on ℤ (a.e. at every
date).
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.Solves`. -/
def SolvesZ (q : ℝ) (u z : ℤ → Ω → ℝ) : Prop :=
  ∀ t, z t =ᵐ[S.μ] q • S.E t (z (t + 1)) + u t

/-- Cochrane (2023), Ch. 2: a solution on ℤ restricts to a solution of the ℕ-indexed system at
every date `s`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.Solves`. -/
theorem solvesZ_restrict {q : ℝ} {u z : ℤ → Ω → ℝ} (h : S.SolvesZ q u z) (s : ℤ) :
    (S.restrict s).Solves q (fun n => u (s + n)) (fun n => z (s + n)) := by
  intro n
  have e : s + ((n + 1 : ℕ) : ℤ) = s + n + 1 := by push_cast; ring
  change z (s + n) =ᵐ[S.μ] q • S.E (s + n) (z (s + ((n + 1 : ℕ) : ℤ))) + u (s + n)
  rw [e]
  exact h (s + n)

/-- Cochrane (2023), eq. (5.5), p. 119, on ℤ (**existence**): for `|q| < 1` and bounded adapted
`u`, the forward sum solves `z_t = q E_t z_{t+1} + u_t` at every date `t ∈ ℤ`.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.forwardSol_solves`. -/
theorem FZ_solves {q M : ℝ} (hq : |q| < 1) {u : ℤ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) : S.SolvesZ q u (S.FZ q u) := by
  intro t
  have h := (S.restrict t).forwardSol_solves hq (S.restrict_adapted hua t)
    (fun m => hb (t + m)) 0
  have e0 := S.FZ_eq_restrict q u t 0
  have e1 := S.FZ_eq_restrict q u t 1
  rw [Nat.cast_zero, add_zero] at e0
  rw [Nat.cast_one] at e1
  rw [e0, e1]
  simpa only [restrict_E, restrict_μ, Nat.cast_zero, add_zero, zero_add] using h

/-- Cochrane (2023), Ch. 2, p. 29, on ℤ (**uniqueness**): for `|q| < 1` the equation
`z_t = q E_t z_{t+1} + u_t` has at most one bounded a.e.-measurable solution on ℤ.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.forward_unique`. -/
theorem forwardZ_unique {q : ℝ} (hq : |q| < 1) {u z₁ z₂ : ℤ → Ω → ℝ} (h₁ : S.SolvesZ q u z₁)
    (h₂ : S.SolvesZ q u z₂) (hm₁ : ∀ t, AEStronglyMeasurable (z₁ t) S.μ)
    (hm₂ : ∀ t, AEStronglyMeasurable (z₂ t) S.μ) {M₁ M₂ : ℝ}
    (hb₁ : ∀ t, ∀ᵐ ω ∂S.μ, |z₁ t ω| ≤ M₁) (hb₂ : ∀ t, ∀ᵐ ω ∂S.μ, |z₂ t ω| ≤ M₂) (t : ℤ) :
    z₁ t =ᵐ[S.μ] z₂ t := by
  have h := (S.restrict t).forward_unique hq (S.solvesZ_restrict h₁ t) (S.solvesZ_restrict h₂ t)
    (fun n => hm₁ (t + n)) (fun n => hm₂ (t + n)) ⟨M₁, fun n => hb₁ (t + n)⟩
    ⟨M₂, fun n => hb₂ (t + n)⟩ 0
  simpa only [restrict_μ, Nat.cast_zero, add_zero] using h

/-- Cochrane (2023), eq. (5.5), p. 119, on ℤ: every bounded a.e.-measurable solution of
`z_t = q E_t z_{t+1} + u_t` (`|q| < 1`, bounded adapted `u`) is the forward sum a.e.
ℤ-indexed version of `TidyR5ExpectationsMeasure.MeasExpectationSystem.existsUnique_forward`. -/
theorem eq_FZ {q M Mz : ℝ} (hq : |q| < 1) {u z : ℤ → Ω → ℝ} (hua : StronglyAdapted S.𝓕 u)
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (hz : S.SolvesZ q u z)
    (hzm : ∀ t, AEStronglyMeasurable (z t) S.μ) (hzb : ∀ t, ∀ᵐ ω ∂S.μ, |z t ω| ≤ Mz) (t : ℤ) :
    z t =ᵐ[S.μ] S.FZ q u t :=
  S.forwardZ_unique hq hz (S.FZ_solves hq hua hb) hzm
    (fun s => ((S.FZ_adapted q u s).mono (S.𝓕.le s)).aestronglyMeasurable) hzb
    (S.FZ_bdd hq hb) t

end ZMeasExpectationSystem

end Cochrane.KeynesianStickyPrices.TidyR6ZExpectations
