/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import DebtDeficitsInflation.ExpectationsFiniteTree
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.CondVar

/-!
# Measure-theoretic conditional expectations

Cochrane (2023), Ch. 2, §2.3–2.4, pp. 29–30 (expectations `E_t`, the news operator
`ΔE_{t+1} = E_{t+1} − E_t` of eq. (2.13), forward-looking present values) and §2.7, p. 42 (AR(1)
surpluses). The core `ExpectationSystem` defines `E_t` on **all** functions `Ω → ℝ` with exact
equalities; on a countable `Ω` this forces finitely supported forecasts (proved in the Woodford
Chapter 2 project, `SGUStochasticMeasure.expectationSystem_finite_support`), so no genuine
infinite-horizon model with nondegenerate shocks fits it. This module is an **additive bridge**:
a probability space with a filtration and Mathlib's `condExp`, with every property stated in its
almost-everywhere form. Existing core theorems are untouched.

## How to use (API)

* `MeasExpectationSystem Ω` (fields `P : ProbabilityMeasure Ω`, `𝓕 : Filtration ℕ _`);
  `S.μ` the measure, `S.E t x = S.μ[x | S.𝓕 t]`.
* Carriers: plain functions `Ω → ℝ` and processes `ℕ → Ω → ℝ`; `S.BddRV x` (a.e. measurable,
  essentially bounded; closed under `add`, `sub`, `smul`, `mul`, `sq`, `E`; `.integrable`),
  `S.BddProc x` (uniform essential bound), Mathlib's `StronglyAdapted S.𝓕 x` (adapted).
* Axioms (a.e.): `E_add`, `E_sub`, `E_smul`, `E_const` (exact), `E_zero`, `E_mono`, `E_tower`,
  `E_known` (exact), `E_E_self`, `E_of_stronglyMeasurable` (exact), `E_of_aestronglyMeasurable`,
  `E_congr`, `E_pullOut`, `abs_E_le`, `integral_E`, `stronglyMeasurable_E`, `integrable_E`.
* News: `innov t x = ΔE_{t+1} x`, `E_innov` (martingale difference), `E_mul_innov`,
  `E_sub_E_eq_sum_innov`, `eq_E_add_innov`.
* Series: `E_hasSum` (`E_t` through a dominated `tsum`).
* Forward equation `z_t = a E_t z_{t+1} + u_t` (`Solves`): `forwardSol` (with `forwardSol_hasSum`:
  it is `∑ aᵏ E_t u_{t+k}`), `forwardSol_solves`, `forward_unique`, `existsUnique_forward`;
  for `|a| ≥ 1`: `sunspot`, `sunspot_solves`, `not_unique_of_one_le`, `sunspot_not_predictable`;
  criteria `unique_iff`, `existsUnique_iff`.
* AR(1) with martingale-difference shocks: `ar1_E`, `ar1_E_sq_dev`, `ar1_condVar`,
  `ar1_condVar_closed`.
* Bridges: `toExpectationSystem` (finite discrete full-support `Ω` → core system, with
  `toExpectationSystem_E`, `toExpectationSystem_pullOut`) and `TreeBridge.treeSystem` (core
  `FiniteTree` → measure system, `TreeBridge.treeSystem_E`: `E_t` equals the cell average at every
  state, `TreeBridge.treeSystem_toExpectationSystem_E`: round trip).

The genuine infinite-horizon instance (i.i.d. shocks on `ℕ → ℝ`) is `ExpectationsMeasureIID`.
To copy into another project: rename the namespace prefix and the `import` of
`ExpectationsFiniteTree`; the module uses the core only through `ExpectationSystem`,
`ExpectationSystem.PullOut`, `ExpectationsFiniteTree.FiniteTree` and its `condE`,
`condE_of_trivial`, `condE_tower`, `condE_congr`, `condE_of_const_on_cell`,
`toExpectationSystem_E`, `finiteTree_pullOut`.
-/

namespace Cochrane.DebtDeficitsInflation.ExpectationsMeasure

open MeasureTheory ProbabilityTheory Filter Topology

variable (Ω : Type*) [mΩ : MeasurableSpace Ω]

/-- Cochrane (2023), Ch. 2, pp. 29–30 (the conditional expectations `E_t`): a probability space
`(Ω, P)` with a filtration `𝓕 : ℕ → MeasurableSpace Ω`; `E_t x := P[x | 𝓕 t]`. -/
structure MeasExpectationSystem where
  /-- The probability measure. -/
  P : ProbabilityMeasure Ω
  /-- The information available at each date. -/
  𝓕 : Filtration ℕ mΩ

namespace MeasExpectationSystem

variable {Ω} (S : MeasExpectationSystem Ω)

/-- Cochrane (2023), Ch. 2, p. 29: the probability measure as a measure. -/
abbrev μ : Measure Ω := S.P

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x = μ[x | 𝓕 t]`, Mathlib's conditional expectation. -/
noncomputable abbrev E (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := S.μ[x | S.𝓕 t]

/-- Cochrane (2023), Ch. 2, p. 29: a bounded random variable (a.e. strongly measurable and
essentially bounded). -/
def BddRV (x : Ω → ℝ) : Prop := AEStronglyMeasurable x S.μ ∧ ∃ M, ∀ᵐ ω ∂S.μ, |x ω| ≤ M

/-- Cochrane (2023), Ch. 2, p. 29: a uniformly (essentially) bounded process. -/
def BddProc (x : ℕ → Ω → ℝ) : Prop := ∃ M, ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ M

/-- Cochrane (2023), Ch. 2, p. 29: a bounded random variable is integrable. -/
theorem BddRV.integrable {S : MeasExpectationSystem Ω}
    {x : Ω → ℝ} (hx : S.BddRV x) : Integrable x S.μ := by
  obtain ⟨hm, M, hM⟩ := hx
  exact Integrable.of_bound hm M (hM.mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is additive (a.e.). -/
theorem E_add {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.E t (x + y) =ᵐ[S.μ] S.E t x + S.E t y := condExp_add hx hy _

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` commutes with differences (a.e.). -/
theorem E_sub {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.E t (x - y) =ᵐ[S.μ] S.E t x - S.E t y := condExp_sub hx hy _

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is homogeneous (a.e.). -/
theorem E_smul (c : ℝ) (x : Ω → ℝ) (t : ℕ) : S.E t (c • x) =ᵐ[S.μ] c • S.E t x :=
  condExp_smul c x _

/-- Cochrane (2023), Ch. 2, pp. 29–30: constants are known (exactly). -/
theorem E_const (t : ℕ) (c : ℝ) : S.E t (fun _ => c) = fun _ => c :=
  condExp_const (S.𝓕.le t) c

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t 0 = 0`. -/
theorem E_zero (t : ℕ) : S.E t 0 = 0 := condExp_zero

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is monotone (a.e.). -/
theorem E_mono {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ)
    (hxy : x ≤ᵐ[S.μ] y) (t : ℕ) : S.E t x ≤ᵐ[S.μ] S.E t y := condExp_mono hx hy hxy

/-- Cochrane (2023), Ch. 2, pp. 29–30: the law of iterated expectations `E_s E_t = E_s`, `s ≤ t`
(a.e.). -/
theorem E_tower {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : S.E s (S.E t x) =ᵐ[S.μ] S.E s x :=
  condExp_condExp_of_le (S.𝓕.mono hst) (S.𝓕.le t)

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x` is `𝓕 t`-strongly measurable. -/
theorem stronglyMeasurable_E (t : ℕ) (x : Ω → ℝ) : StronglyMeasurable[S.𝓕 t] (S.E t x) :=
  stronglyMeasurable_condExp

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t x` is integrable. -/
theorem integrable_E (t : ℕ) (x : Ω → ℝ) : Integrable (S.E t x) S.μ := integrable_condExp

/-- Cochrane (2023), Ch. 2, pp. 29–30: what is known at `t` is its own forecast (exactly). -/
theorem E_of_stronglyMeasurable {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    (hi : Integrable x S.μ) : S.E t x = x :=
  condExp_of_stronglyMeasurable (S.𝓕.le t) hx hi

/-- Cochrane (2023), Ch. 2, pp. 29–30: what is a.e. known at `t` is a.e. its own forecast. -/
theorem E_of_aestronglyMeasurable {t : ℕ} {x : Ω → ℝ} (hx : AEStronglyMeasurable[S.𝓕 t] x S.μ)
    (hi : Integrable x S.μ) : S.E t x =ᵐ[S.μ] x :=
  condExp_of_aestronglyMeasurable' (S.𝓕.le t) hx hi

/-- Cochrane (2023), Ch. 2, pp. 29–30: earlier forecasts are known later, `E_t E_s = E_s` for
`s ≤ t` (exactly). -/
theorem E_known {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : S.E t (S.E s x) = S.E s x :=
  S.E_of_stronglyMeasurable ((S.stronglyMeasurable_E s x).mono (S.𝓕.mono hst))
    (S.integrable_E s x)

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` is idempotent (exactly). -/
theorem E_E_self (t : ℕ) (x : Ω → ℝ) : S.E t (S.E t x) = S.E t x := S.E_known le_rfl x

/-- Cochrane (2023), Ch. 2, pp. 29–30: `E_t` respects a.e. equality. -/
theorem E_congr {x y : Ω → ℝ} (h : x =ᵐ[S.μ] y) (t : ℕ) : S.E t x =ᵐ[S.μ] S.E t y :=
  condExp_congr_ae h

/-- Cochrane (2023), Ch. 2, pp. 29–30: the unconditional mean of a forecast is the mean. -/
theorem integral_E (t : ℕ) (x : Ω → ℝ) : ∫ ω, S.E t x ω ∂S.μ = ∫ ω, x ω ∂S.μ :=
  integral_condExp (S.𝓕.le t)

/-- Cochrane (2023), Ch. 2, pp. 29–30: **pull-out** — a bounded factor known at `t` comes out of
`E_t` (a.e.). -/
theorem E_pullOut {t : ℕ} {f y : Ω → ℝ} (hf : StronglyMeasurable[S.𝓕 t] f) {C : ℝ}
    (hfC : ∀ᵐ ω ∂S.μ, |f ω| ≤ C) (hy : Integrable y S.μ) :
    S.E t (f * y) =ᵐ[S.μ] f * S.E t y := by
  have hint : Integrable (f * y) S.μ :=
    hy.bdd_mul (hf.mono (S.𝓕.le t)).aestronglyMeasurable
      (hfC.mono fun ω h => by rwa [Real.norm_eq_abs])
  exact condExp_mul_of_stronglyMeasurable_left hf hint hy

/-- Cochrane (2023), Ch. 2, pp. 29–30: `|E_t x| ≤ M` a.e. whenever `|x| ≤ M` a.e. -/
theorem abs_E_le {x : Ω → ℝ} {M : ℝ} (hx : ∀ᵐ ω ∂S.μ, |x ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |S.E t x ω| ≤ M :=
  ae_bdd_abs_condExp_of_ae_bdd_abs hx

/-! ### Bounded random variables -/

/-- Cochrane (2023), Ch. 2, p. 29: a variable known at `t` with an a.e. bound is bounded. -/
theorem BddRV.of_stronglyMeasurable {S : MeasExpectationSystem Ω}
    {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    {M : ℝ} (hM : ∀ᵐ ω ∂S.μ, |x ω| ≤ M) : S.BddRV x :=
  ⟨(hx.mono (S.𝓕.le t)).aestronglyMeasurable, M, hM⟩

/-- Cochrane (2023), Ch. 2, p. 29: constants are bounded. -/
theorem BddRV.const {S : MeasExpectationSystem Ω} (c : ℝ) : S.BddRV (fun _ => c) :=
  ⟨aestronglyMeasurable_const, |c|, Eventually.of_forall fun _ => le_rfl⟩

/-- Cochrane (2023), Ch. 2, p. 29: sums of bounded variables are bounded. -/
theorem BddRV.add {S : MeasExpectationSystem Ω}
    {x y : Ω → ℝ} (hx : S.BddRV x) (hy : S.BddRV y) : S.BddRV (x + y) := by
  obtain ⟨hxm, M, hM⟩ := hx
  obtain ⟨hym, N, hN⟩ := hy
  refine ⟨hxm.add hym, M + N, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- Cochrane (2023), Ch. 2, p. 29: multiples of bounded variables are bounded. -/
theorem BddRV.smul {S : MeasExpectationSystem Ω}
    {x : Ω → ℝ} (hx : S.BddRV x) (c : ℝ) : S.BddRV (c • x) := by
  obtain ⟨hxm, M, hM⟩ := hx
  refine ⟨hxm.const_smul c, |c| * M, ?_⟩
  filter_upwards [hM] with ω h1
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)

/-- Cochrane (2023), Ch. 2, p. 29: differences of bounded variables are bounded. -/
theorem BddRV.sub {S : MeasExpectationSystem Ω}
    {x y : Ω → ℝ} (hx : S.BddRV x) (hy : S.BddRV y) : S.BddRV (x - y) := by
  have h := hx.add (hy.smul (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at h

/-- Cochrane (2023), Ch. 2, p. 29: products of bounded variables are bounded. -/
theorem BddRV.mul {S : MeasExpectationSystem Ω}
    {x y : Ω → ℝ} (hx : S.BddRV x) (hy : S.BddRV y) : S.BddRV (x * y) := by
  obtain ⟨hxm, M, hM⟩ := hx
  obtain ⟨hym, N, hN⟩ := hy
  refine ⟨hxm.mul hym, M * N, ?_⟩
  filter_upwards [hM, hN] with ω h1 h2
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

/-- Cochrane (2023), Ch. 2, p. 29: forecasts of bounded variables are bounded. -/
theorem BddRV.E {S : MeasExpectationSystem Ω}
    {x : Ω → ℝ} (hx : S.BddRV x) (t : ℕ) : S.BddRV (S.E t x) := by
  obtain ⟨-, M, hM⟩ := hx
  exact ⟨(S.integrable_E t x).aestronglyMeasurable, M, S.abs_E_le hM t⟩

/-! ### Innovations (news) -/

/-- Cochrane (2023), eq. (2.13), p. 30: the innovation `ΔE_{t+1} x = E_{t+1} x − E_t x`. -/
noncomputable def innov (t : ℕ) (x : Ω → ℝ) : Ω → ℝ := S.E (t + 1) x - S.E t x

/-- Cochrane (2023), eq. (2.13), p. 30: the innovation is known at `t + 1`. -/
theorem stronglyMeasurable_innov (t : ℕ) (x : Ω → ℝ) :
    StronglyMeasurable[S.𝓕 (t + 1)] (S.innov t x) :=
  (S.stronglyMeasurable_E (t + 1) x).sub
    ((S.stronglyMeasurable_E t x).mono (S.𝓕.mono (Nat.le_succ t)))

/-- Cochrane (2023), eq. (2.13), p. 30: **innovations are martingale differences**,
`E_s ΔE_{t+1} x = 0` a.e. for every `s ≤ t`. -/
theorem E_innov {s t : ℕ} (hst : s ≤ t) (x : Ω → ℝ) : S.E s (S.innov t x) =ᵐ[S.μ] 0 := by
  filter_upwards [S.E_sub (S.integrable_E (t + 1) x) (S.integrable_E t x) s,
    S.E_tower (hst.trans (Nat.le_succ t)) x, S.E_tower hst x] with ω h1 h2 h3
  rw [innov, h1, Pi.sub_apply, h2, h3, sub_self, Pi.zero_apply]

/-- Cochrane (2023), eq. (2.13), p. 30: news is uncorrelated with anything known before it,
`E_t (w ΔE_{t+1} x) = 0` for bounded `w` known at `t` and bounded `x`. -/
theorem E_mul_innov {t : ℕ} {w : Ω → ℝ} (hw : StronglyMeasurable[S.𝓕 t] w) {C : ℝ}
    (hwC : ∀ᵐ ω ∂S.μ, |w ω| ≤ C) (x : Ω → ℝ) :
    S.E t (w * S.innov t x) =ᵐ[S.μ] 0 := by
  have hi : Integrable (S.innov t x) S.μ := (S.integrable_E _ x).sub (S.integrable_E _ x)
  filter_upwards [S.E_pullOut hw hwC hi, S.E_innov le_rfl x] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]
  simp

/-- Cochrane (2023), eq. (2.13), p. 30: forecast revisions telescope into news,
`E_{t+n} x − E_t x = ∑_{i<n} ΔE_{t+i+1} x` (exactly). -/
theorem E_sub_E_eq_sum_innov (t n : ℕ) (x : Ω → ℝ) :
    S.E (t + n) x - S.E t x = ∑ i ∈ Finset.range n, S.innov (t + i) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, innov, ← add_assoc]
    abel

/-- Cochrane (2023), eq. (2.17), p. 35: a variable known at `t + 1` is its forecast plus its
news, `x = E_t x + ΔE_{t+1} x` (exactly). -/
theorem eq_E_add_innov {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 (t + 1)] x)
    (hi : Integrable x S.μ) : x = S.E t x + S.innov t x := by
  rw [innov, S.E_of_stronglyMeasurable hx hi]
  abel

/-! ### `E_t` and dominated infinite sums -/

/-- Cochrane (2023), Ch. 2, p. 29 (present values as infinite sums): **`E_t` passes through a
dominated series** — if `|f_k| ≤ c_k` a.e. with `∑ c_k < ∞`, then a.e.
`∑_k E_t f_k = E_t ∑_k f_k` (as a genuine `HasSum`). -/
theorem E_hasSum {f : ℕ → Ω → ℝ} {c : ℕ → ℝ} (hc : Summable c)
    (hm : ∀ k, AEStronglyMeasurable (f k) S.μ) (hf : ∀ k, ∀ᵐ ω ∂S.μ, |f k ω| ≤ c k) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => S.E t (f k) ω) (S.E t (fun ω' => ∑' k, f k ω') ω) := by
  set F : Ω → ℝ := fun ω' => ∑' k, f k ω' with hF
  have hall : ∀ᵐ ω ∂S.μ, ∀ k, |f k ω| ≤ c k := ae_all_iff.2 hf
  have hsum : ∀ᵐ ω ∂S.μ, Summable (fun k => f k ω) := hall.mono fun ω h =>
    Summable.of_norm_bounded hc (fun k => by rw [Real.norm_eq_abs]; exact h k)
  have hFm : AEStronglyMeasurable F S.μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, f k ω)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hm k) ?_
    filter_upwards [hsum] with ω h
    exact h.hasSum.tendsto_sum_nat
  -- the tail bound
  have htail : ∀ N, ∀ᵐ ω ∂S.μ,
      |F ω - ∑ k ∈ Finset.range N, f k ω| ≤ ∑' k, c (k + N) := by
    intro N
    filter_upwards [hall, hsum] with ω h hs
    change |∑' k, f k ω - ∑ k ∈ Finset.range N, f k ω| ≤ _
    rw [← hs.sum_add_tsum_nat_add N, add_sub_cancel_left, ← Real.norm_eq_abs]
    exact tsum_of_norm_bounded ((summable_nat_add_iff N).2 hc).hasSum
      (fun k => by rw [Real.norm_eq_abs]; exact h (k + N))
  have hbF : ∀ᵐ ω ∂S.μ, |F ω| ≤ ∑' k, c k := by
    filter_upwards [htail 0] with ω h
    simpa using h
  have hint : ∀ k, Integrable (f k) S.μ := fun k => BddRV.integrable (S := S) ⟨hm k, c k, hf k⟩
  have hFi : Integrable F S.μ := BddRV.integrable (S := S) ⟨hFm, _, hbF⟩
  have hdiff : ∀ N, ∀ᵐ ω ∂S.μ,
      |S.E t F ω - ∑ k ∈ Finset.range N, S.E t (f k) ω| ≤ ∑' k, c (k + N) := by
    intro N
    have hpi : Integrable (∑ k ∈ Finset.range N, f k) S.μ :=
      integrable_finsetSum' _ fun k _ => hint k
    have hEs : S.E t (∑ k ∈ Finset.range N, f k) =ᵐ[S.μ] ∑ k ∈ Finset.range N, S.E t (f k) :=
      condExp_finsetSum (fun k _ => hint k) (S.𝓕 t)
    filter_upwards [S.E_sub hFi hpi t, hEs,
      S.abs_E_le (x := F - ∑ k ∈ Finset.range N, f k) (by
        filter_upwards [htail N] with ω h
        simpa [Finset.sum_apply] using h) t] with ω h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Finset.sum_apply] at h3
    exact h3
  have hEb : ∀ᵐ ω ∂S.μ, ∀ k, |S.E t (f k) ω| ≤ c k :=
    ae_all_iff.2 fun k => S.abs_E_le (hf k) t
  filter_upwards [ae_all_iff.2 hdiff, hEb] with ω hd hb
  have hs : Summable fun k => ‖S.E t (f k) ω‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact hb k) hc
  rw [hasSum_iff_tendsto_nat_of_summable_norm hs, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun N => ?_) (tendsto_sum_nat_add c)
  rw [norm_norm, Real.norm_eq_abs, abs_sub_comm]
  exact hd N

/-! ### Forward solutions: existence and uniqueness for `|a| < 1` -/

/-- Cochrane (2023), Ch. 2, p. 29 (present values): the realised discounted sum
`∑_k aᵏ u_{t+k}`. -/
noncomputable def discSum (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' k, a ^ k * u (t + k) ω

/-- Cochrane (2023), Ch. 2, p. 29: a geometric series with bounded terms is summable. -/
theorem summable_geom_mul {a M : ℝ} (ha : |a| < 1) {x : ℕ → ℝ} (hx : ∀ k, |x k| ≤ M) :
    Summable (fun k => a ^ k * x k) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hx k) (pow_nonneg (abs_nonneg a) k))

/-- Cochrane (2023), Ch. 2, p. 29: the bound `|∑ aᵏ x_k| ≤ M / (1 − |a|)`. -/
theorem abs_tsum_geom_mul_le {a M : ℝ} (ha : |a| < 1) {x : ℕ → ℝ} (hx : ∀ k, |x k| ≤ M) :
    |∑' k, a ^ k * x k| ≤ M / (1 - |a|) := by
  rw [← Real.norm_eq_abs, div_eq_inv_mul]
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hx k) (pow_nonneg (abs_nonneg a) k)

omit mΩ in
/-- Cochrane (2023), Ch. 2, p. 29: the discounted sum satisfies `U_t = u_t + a U_{t+1}` wherever
it converges. -/
theorem discSum_succ {a : ℝ} {u : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (hs : Summable (fun k => a ^ k * u (t + k) ω)) :
    discSum a u t ω = u t ω + a * discSum a u (t + 1) ω := by
  unfold discSum
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun k => ?_
  rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
  ring

/-- Cochrane (2023), Ch. 2, p. 29: the discounted sum of a bounded process is bounded a.e. -/
theorem discSum_bdd {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |discSum a u t ω| ≤ M / (1 - |a|) := by
  filter_upwards [ae_all_iff.2 hb] with ω h
  exact abs_tsum_geom_mul_le ha fun k => h (t + k)

/-- Cochrane (2023), Ch. 2, p. 29: `U_t = u_t + a U_{t+1}` a.e. -/
theorem discSum_rec {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℕ) :
    discSum a u t =ᵐ[S.μ] u t + a • discSum a u (t + 1) := by
  filter_upwards [ae_all_iff.2 hb] with ω h
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact discSum_succ (summable_geom_mul ha fun k => h (t + k))

/-- Cochrane (2023), Ch. 2, p. 29: the discounted sum is a.e. strongly measurable. -/
theorem aestronglyMeasurable_discSum {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) S.μ) (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℕ) :
    AEStronglyMeasurable (discSum a u t) S.μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun N ω => ∑ k ∈ Finset.range N, a ^ k * u (t + k) ω)
    (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => (hm (t + k)).const_mul _) ?_
  filter_upwards [ae_all_iff.2 hb] with ω h
  exact (summable_geom_mul ha fun k => h (t + k)).hasSum.tendsto_sum_nat

/-- Cochrane (2023), Ch. 2, p. 29: `z` solves `z_t = a E_t z_{t+1} + u_t` (a.e. at every
date). -/
def Solves (a : ℝ) (u z : ℕ → Ω → ℝ) : Prop :=
  ∀ t, z t =ᵐ[S.μ] a • S.E t (z (t + 1)) + u t

/-- Cochrane (2023), Ch. 2, p. 29: the forward solution `z_t = E_t ∑_k aᵏ u_{t+k}`. -/
noncomputable def forwardSol (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := S.E t (discSum a u t)

/-- Cochrane (2023), Ch. 2, p. 29: the forward solution is adapted. -/
theorem forwardSol_adapted (a : ℝ) (u : ℕ → Ω → ℝ) : StronglyAdapted S.𝓕 (S.forwardSol a u) :=
  fun t => S.stronglyMeasurable_E t _

/-- Cochrane (2023), Ch. 2, p. 29: the forward solution is bounded by `M / (1 − |a|)`. -/
theorem forwardSol_bdd {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) : S.BddProc (S.forwardSol a u) :=
  ⟨M / (1 - |a|), fun t => S.abs_E_le (S.discSum_bdd ha hb t) t⟩

/-- Cochrane (2023), Ch. 2, p. 29: **existence** — for `|a| < 1` and bounded adapted `u`, the
forward solution solves `z_t = a E_t z_{t+1} + u_t`. -/
theorem forwardSol_solves {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hua : StronglyAdapted S.𝓕 u) (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) :
    S.Solves a u (S.forwardSol a u) := by
  intro t
  have hm : ∀ t, AEStronglyMeasurable (u t) S.μ :=
    fun t => ((hua t).mono (S.𝓕.le t)).aestronglyMeasurable
  have hDi : ∀ s, Integrable (discSum a u s) S.μ := fun s =>
    BddRV.integrable ⟨S.aestronglyMeasurable_discSum ha hm hb s, _, S.discSum_bdd ha hb s⟩
  have hui : Integrable (u t) S.μ := BddRV.integrable ⟨hm t, M, hb t⟩
  have hEu : S.E t (u t) = u t := S.E_of_stronglyMeasurable (hua t) hui
  filter_upwards [S.E_congr (S.discSum_rec ha hb t) t, S.E_add hui ((hDi (t + 1)).smul a) t,
    S.E_smul a (discSum a u (t + 1)) t, S.E_tower (Nat.le_succ t) (discSum a u (t + 1))]
    with ω h1 h2 h3 h4
  change S.E t (discSum a u t) ω = (a • S.E t (S.E (t + 1) (discSum a u (t + 1))) + u t) ω
  rw [h1, h2, Pi.add_apply, hEu, h3, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, h4,
    add_comm]

/-- Cochrane (2023), Ch. 2, p. 29: the forward solution is the genuine forward sum
`z_t = ∑_k aᵏ E_t u_{t+k}` (a.e., as a convergent series). -/
theorem forwardSol_hasSum {a M : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hm : ∀ t, AEStronglyMeasurable (u t) S.μ) (hb : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, HasSum (fun k => a ^ k * S.E t (u (t + k)) ω) (S.forwardSol a u t ω) := by
  have hsm : ∀ k, S.E t (fun ω => a ^ k * u (t + k) ω) =ᵐ[S.μ] a ^ k • S.E t (u (t + k)) :=
    fun k => S.E_smul (a ^ k) (u (t + k)) t
  filter_upwards [S.E_hasSum (f := fun k ω => a ^ k * u (t + k) ω)
    ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right M)
    (fun k => (hm (t + k)).const_mul _) (fun k => by
      filter_upwards [hb (t + k)] with ω h
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left h (pow_nonneg (abs_nonneg a) k)) t,
    ae_all_iff.2 hsm] with ω h1 h2
  have e : (fun k => a ^ k * S.E t (u (t + k)) ω) =
      fun k => S.E t (fun ω => a ^ k * u (t + k) ω) ω := by
    funext k
    rw [h2 k, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact h1

/-- Cochrane (2023), Ch. 2, p. 29: iterating a homogeneous forward equation,
`d_t = a^{k+1} E_t d_{t+k+1}` a.e. -/
theorem iterate_homog {a : ℝ} {d : ℕ → Ω → ℝ} (hd : ∀ t, d t =ᵐ[S.μ] a • S.E t (d (t + 1)))
    (t k : ℕ) : d t =ᵐ[S.μ] a ^ (k + 1) • S.E t (d (t + (k + 1))) := by
  induction k with
  | zero => simpa using hd t
  | succ k ih =>
    have h2 := hd (t + (k + 1))
    have e : t + (k + 1) + 1 = t + (k + 1 + 1) := rfl
    rw [e] at h2
    filter_upwards [ih, S.E_congr h2 t, S.E_smul a (S.E (t + (k + 1)) (d (t + (k + 1 + 1)))) t,
      S.E_tower (Nat.le_add_right t (k + 1)) (d (t + (k + 1 + 1)))] with ω e1 e2 e3 e4
    rw [e1, Pi.smul_apply, e2, e3, Pi.smul_apply, e4, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, pow_succ]
    ring

/-- Cochrane (2023), Ch. 2, p. 29: **uniqueness** — for `|a| < 1` the equation
`z_t = a E_t z_{t+1} + u_t` has at most one bounded (a.e. measurable) solution, up to a.e.
equality at every date. -/
theorem forward_unique {a : ℝ} (ha : |a| < 1) {u z₁ z₂ : ℕ → Ω → ℝ} (h₁ : S.Solves a u z₁)
    (h₂ : S.Solves a u z₂) (hm₁ : ∀ t, AEStronglyMeasurable (z₁ t) S.μ)
    (hm₂ : ∀ t, AEStronglyMeasurable (z₂ t) S.μ) (hb₁ : S.BddProc z₁) (hb₂ : S.BddProc z₂) :
    ∀ t, z₁ t =ᵐ[S.μ] z₂ t := by
  obtain ⟨M₁, hM₁⟩ := hb₁
  obtain ⟨M₂, hM₂⟩ := hb₂
  have hi₁ : ∀ t, Integrable (z₁ t) S.μ := fun t => BddRV.integrable ⟨hm₁ t, M₁, hM₁ t⟩
  have hi₂ : ∀ t, Integrable (z₂ t) S.μ := fun t => BddRV.integrable ⟨hm₂ t, M₂, hM₂ t⟩
  set d : ℕ → Ω → ℝ := fun t => z₁ t - z₂ t with hd_def
  have hd : ∀ t, d t =ᵐ[S.μ] a • S.E t (d (t + 1)) := by
    intro t
    filter_upwards [h₁ t, h₂ t, S.E_sub (hi₁ (t + 1)) (hi₂ (t + 1)) t] with ω e1 e2 e3
    simp only [hd_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, e3]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hdb : ∀ s, ∀ᵐ ω ∂S.μ, |d s ω| ≤ M₁ + M₂ := fun s => by
    filter_upwards [hM₁ s, hM₂ s] with ω e1 e2
    exact (abs_sub _ _).trans (add_le_add e1 e2)
  intro t
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂S.μ, |d t ω| ≤ |a| ^ (k + 1) * (M₁ + M₂) := by
    intro k
    filter_upwards [S.iterate_homog hd t k, S.abs_E_le (hdb (t + (k + 1))) t] with ω e1 e2
    rw [e1, Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left e2 (pow_nonneg (abs_nonneg a) _)
  filter_upwards [ae_all_iff.2 hk] with ω h
  have hlim : Tendsto (fun k : ℕ => |a| ^ (k + 1) * (M₁ + M₂)) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).comp
      (tendsto_add_atTop_nat 1)).mul_const (M₁ + M₂)
    simpa using this
  have h0 : d t ω = 0 := abs_nonpos_iff.mp (ge_of_tendsto' hlim h)
  simpa [hd_def, sub_eq_zero] using h0

/-- Cochrane (2023), Ch. 2, p. 29: **existence and uniqueness** of the bounded adapted solution
of `z_t = a E_t z_{t+1} + u_t` for `|a| < 1` and bounded adapted `u`: it is the forward solution
`∑ aᵏ E_t u_{t+k}` (`forwardSol_hasSum`), and every bounded a.e.-measurable solution equals it
a.e. at every date. -/
theorem existsUnique_forward {a : ℝ} (ha : |a| < 1) {u : ℕ → Ω → ℝ}
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u) :
    (S.Solves a u (S.forwardSol a u) ∧ StronglyAdapted S.𝓕 (S.forwardSol a u) ∧
      S.BddProc (S.forwardSol a u)) ∧
    ∀ z, S.Solves a u z → (∀ t, AEStronglyMeasurable (z t) S.μ) → S.BddProc z →
      ∀ t, z t =ᵐ[S.μ] S.forwardSol a u t := by
  obtain ⟨M, hb⟩ := hub
  refine ⟨⟨S.forwardSol_solves ha hua hb, S.forwardSol_adapted a u, S.forwardSol_bdd ha hb⟩,
    fun z hz hzm hzb => S.forward_unique ha hz (S.forwardSol_solves ha hua hb) hzm
      (fun t => ((S.forwardSol_adapted a u t).mono (S.𝓕.le t)).aestronglyMeasurable) hzb
      (S.forwardSol_bdd ha hb)⟩

/-! ### Nonuniqueness for `|a| ≥ 1`: genuinely random sunspots -/

/-- Cochrane (2023), Ch. 2, p. 29 (multiple equilibria when the root is not stable): the sunspot
started by a date-`s+1` shock `η`: `d_t = 0` for `t ≤ s` and `d_t = a^{-(t-s-1)} (η − E_s η)`
for `t > s`. -/
noncomputable def sunspot (a : ℝ) (s : ℕ) (η : Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  if t ≤ s then 0 else a⁻¹ ^ (t - (s + 1)) • (η - S.E s η)

/-- Cochrane (2023), Ch. 2, p. 29: at date `s + 1` the sunspot is the news `η − E_s η`. -/
theorem sunspot_succ (a : ℝ) (s : ℕ) (η : Ω → ℝ) : S.sunspot a s η (s + 1) = η - S.E s η := by
  simp [sunspot]

/-- Cochrane (2023), Ch. 2, p. 29: the sunspot is adapted. -/
theorem sunspot_adapted (a : ℝ) {s : ℕ} {η : Ω → ℝ} (hη : StronglyMeasurable[S.𝓕 (s + 1)] η) :
    StronglyAdapted S.𝓕 (S.sunspot a s η) := by
  intro t
  unfold sunspot
  by_cases h : t ≤ s
  · simp only [h, ↓reduceIte]
    exact stronglyMeasurable_zero
  · simp only [h, ↓reduceIte]
    have h1 : s + 1 ≤ t := by omega
    exact ((hη.mono (S.𝓕.mono h1)).sub
      ((S.stronglyMeasurable_E s η).mono (S.𝓕.mono (by omega)))).const_smul _

/-- Cochrane (2023), Ch. 2, p. 29: for `|a| ≥ 1` the sunspot of a bounded shock is bounded. -/
theorem sunspot_bdd {a B : ℝ} (ha : 1 ≤ |a|) {s : ℕ} {η : Ω → ℝ}
    (hηb : ∀ᵐ ω ∂S.μ, |η ω| ≤ B) : S.BddProc (S.sunspot a s η) := by
  obtain ⟨ω₀, hω₀⟩ := hηb.exists
  have hB : 0 ≤ B := (abs_nonneg _).trans hω₀
  refine ⟨B + B, fun t => ?_⟩
  unfold sunspot
  by_cases h : t ≤ s
  · simp only [h, ↓reduceIte]
    exact Eventually.of_forall fun ω => by simp; linarith
  · simp only [h, ↓reduceIte]
    filter_upwards [hηb, S.abs_E_le hηb s] with ω h1 h2
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, Pi.sub_apply]
    have hp : |a⁻¹| ^ (t - (s + 1)) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (by rw [abs_inv]; exact inv_le_one_of_one_le₀ ha)
    have hs : |η ω - S.E s η ω| ≤ B + B := (abs_sub _ _).trans (add_le_add h1 h2)
    calc |a⁻¹| ^ (t - (s + 1)) * |η ω - S.E s η ω| ≤ 1 * (B + B) :=
          mul_le_mul hp hs (abs_nonneg _) zero_le_one
      _ = B + B := one_mul _

/-- Cochrane (2023), Ch. 2, p. 29: the sunspot solves the homogeneous equation
`d_t = a E_t d_{t+1}` (a.e.) for every `a ≠ 0`. -/
theorem sunspot_solves {a : ℝ} (ha : a ≠ 0) {s : ℕ} {η : Ω → ℝ}
    (hη : StronglyMeasurable[S.𝓕 (s + 1)] η) (hηi : Integrable η S.μ) (t : ℕ) :
    S.sunspot a s η t =ᵐ[S.μ] a • S.E t (S.sunspot a s η (t + 1)) := by
  rcases lt_trichotomy t s with h | rfl | h
  · have h1 : t ≤ s := h.le
    have h2 : t + 1 ≤ s := h
    unfold sunspot
    simp only [h1, h2, ↓reduceIte, S.E_zero, smul_zero]
    rfl
  · rw [S.sunspot_succ]
    unfold sunspot
    simp only [le_refl, ↓reduceIte]
    filter_upwards [S.E_sub hηi (S.integrable_E t η) t] with ω h1
    rw [Pi.smul_apply, h1, Pi.sub_apply, S.E_E_self, sub_self, smul_zero, Pi.zero_apply]
  · have h1 : ¬ t ≤ s := by omega
    have h2 : ¬ t + 1 ≤ s := by omega
    have hν : StronglyMeasurable[S.𝓕 t] (a⁻¹ ^ (t + 1 - (s + 1)) • (η - S.E s η)) :=
      ((hη.mono (S.𝓕.mono h)).sub
        ((S.stronglyMeasurable_E s η).mono (S.𝓕.mono h.le))).const_smul _
    have hνi : Integrable (a⁻¹ ^ (t + 1 - (s + 1)) • (η - S.E s η)) S.μ :=
      (hηi.sub (S.integrable_E s η)).smul _
    unfold sunspot
    simp only [h1, h2, ↓reduceIte]
    rw [S.E_of_stronglyMeasurable hν hνi, smul_smul]
    have e : t + 1 - (s + 1) = t - (s + 1) + 1 := by omega
    rw [e, pow_succ, ← mul_assoc, mul_comm a, mul_assoc, mul_inv_cancel₀ ha, mul_one]

/-- Cochrane (2023), Ch. 2, p. 29: adding a solution of the homogeneous equation to a solution
gives a solution. -/
theorem solves_add {a : ℝ} {u z d : ℕ → Ω → ℝ} (hz : S.Solves a u z)
    (hd : ∀ t, d t =ᵐ[S.μ] a • S.E t (d (t + 1))) (hzi : ∀ t, Integrable (z t) S.μ)
    (hdi : ∀ t, Integrable (d t) S.μ) : S.Solves a u (fun t => z t + d t) := by
  intro t
  filter_upwards [hz t, hd t, S.E_add (hzi (t + 1)) (hdi (t + 1)) t] with ω e1 e2 e3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
  rw [e1, e2, e3]
  ring

/-- Cochrane (2023), Ch. 2, p. 29: the sunspot shock is genuinely random — `η − E_s η` is not
a.e. equal to any variable known at date `s` — unless `η` is a.e. its own date-`s` forecast. -/
theorem sunspot_not_predictable {s : ℕ} {η : Ω → ℝ} (hηi : Integrable η S.μ)
    (hηr : ¬ η =ᵐ[S.μ] S.E s η) {g : Ω → ℝ} (hg : StronglyMeasurable[S.𝓕 s] g) :
    ¬ (η - S.E s η) =ᵐ[S.μ] g := by
  intro h
  have hνi : Integrable (η - S.E s η) S.μ := hηi.sub (S.integrable_E s η)
  have hgi : Integrable g S.μ := hνi.congr h
  have h0 : S.E s (η - S.E s η) =ᵐ[S.μ] 0 := by
    filter_upwards [S.E_sub hηi (S.integrable_E s η) s] with ω h1
    rw [h1, Pi.sub_apply, S.E_E_self, sub_self, Pi.zero_apply]
  have hg0 : g =ᵐ[S.μ] 0 := by
    have := (S.E_congr h s).symm.trans h0
    rwa [S.E_of_stronglyMeasurable hg hgi] at this
  apply hηr
  filter_upwards [h.trans hg0] with ω h1
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h1
  exact h1

/-- Cochrane (2023), Ch. 2, p. 29: **nonuniqueness for `|a| ≥ 1`** — next to every bounded
adapted solution of `z_t = a E_t z_{t+1} + u_t` there is another one, `z + d` with the sunspot
`d` driven by any bounded date-`s+1` shock `η` that is not a.e. its own date-`s` forecast; the
two differ with positive probability at date `s + 1`. -/
theorem not_unique_of_one_le {a B : ℝ} (ha : 1 ≤ |a|) {s : ℕ} {η : Ω → ℝ}
    (hη : StronglyMeasurable[S.𝓕 (s + 1)] η) (hηb : ∀ᵐ ω ∂S.μ, |η ω| ≤ B)
    (hηr : ¬ η =ᵐ[S.μ] S.E s η) {u z : ℕ → Ω → ℝ} (hz : S.Solves a u z)
    (hza : StronglyAdapted S.𝓕 z) (hzb : S.BddProc z) :
    ∃ z', S.Solves a u z' ∧ StronglyAdapted S.𝓕 z' ∧ S.BddProc z' ∧
      ¬ z' (s + 1) =ᵐ[S.μ] z (s + 1) := by
  have ha0 : a ≠ 0 := fun h => by rw [h, abs_zero] at ha; linarith
  have hηi : Integrable η S.μ := BddRV.integrable (BddRV.of_stronglyMeasurable hη hηb)
  obtain ⟨M, hM⟩ := hzb
  obtain ⟨M', hM'⟩ := S.sunspot_bdd (s := s) ha hηb
  have hzi : ∀ t, Integrable (z t) S.μ := fun t =>
    BddRV.integrable (BddRV.of_stronglyMeasurable (hza t) (hM t))
  have hdi : ∀ t, Integrable (S.sunspot a s η t) S.μ := fun t =>
    BddRV.integrable (BddRV.of_stronglyMeasurable (S.sunspot_adapted a hη t) (hM' t))
  refine ⟨fun t => z t + S.sunspot a s η t,
    S.solves_add hz (S.sunspot_solves ha0 hη hηi) hzi hdi,
    fun t => (hza t).add (S.sunspot_adapted a hη t), ⟨M + M', fun t => ?_⟩, ?_⟩
  · filter_upwards [hM t, hM' t] with ω h1 h2
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  · intro h
    apply hηr
    filter_upwards [h] with ω h1
    rw [S.sunspot_succ, Pi.add_apply, Pi.sub_apply, add_eq_left, sub_eq_zero] at h1
    exact h1

/-- Cochrane (2023), Ch. 2, p. 29: the zero process solves `z_t = a E_t z_{t+1}`. -/
theorem solves_zero (a : ℝ) : S.Solves a 0 0 := fun t => by
  rw [Pi.zero_apply, Pi.zero_apply, S.E_zero, smul_zero, add_zero]

/-- Cochrane (2023), Ch. 2, p. 29: **determinacy criterion** — on a filtration carrying some
genuinely random bounded news (a bounded date-`s+1` variable that is not a.e. its own date-`s`
forecast), bounded adapted solutions of `z_t = a E_t z_{t+1} + u_t` are unique (for every
bounded adapted `u`) if and only if `|a| < 1`. -/
theorem unique_iff (hnd : ∃ s η B, StronglyMeasurable[S.𝓕 (s + 1)] η ∧
      (∀ᵐ ω ∂S.μ, |η ω| ≤ B) ∧ ¬ η =ᵐ[S.μ] S.E s η) (a : ℝ) :
    (∀ u z₁ z₂ : ℕ → Ω → ℝ, S.Solves a u z₁ → S.Solves a u z₂ → StronglyAdapted S.𝓕 z₁ →
      StronglyAdapted S.𝓕 z₂ → S.BddProc z₁ → S.BddProc z₂ → ∀ t, z₁ t =ᵐ[S.μ] z₂ t) ↔
      |a| < 1 := by
  constructor
  · intro h
    by_contra ha
    push Not at ha
    obtain ⟨s, η, B, hη, hηb, hηr⟩ := hnd
    obtain ⟨z', hz', hza', hzb', hne⟩ := S.not_unique_of_one_le ha hη hηb hηr (S.solves_zero a)
      (fun _ => stronglyMeasurable_zero) ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩
    exact hne (h 0 z' 0 hz' (S.solves_zero a) hza' (fun _ => stronglyMeasurable_zero) hzb'
      ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩ (s + 1))
  · intro ha u z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂
    exact S.forward_unique ha h₁ h₂ (fun t => ((ha₁ t).mono (S.𝓕.le t)).aestronglyMeasurable)
      (fun t => ((ha₂ t).mono (S.𝓕.le t)).aestronglyMeasurable) hb₁ hb₂

/-- Cochrane (2023), Ch. 2, p. 29: **existence and uniqueness iff `|a| < 1`** — under genuinely
random news, every bounded adapted `u` has a bounded adapted solution, unique up to a.e.
equality, exactly when `|a| < 1`. -/
theorem existsUnique_iff (hnd : ∃ s η B, StronglyMeasurable[S.𝓕 (s + 1)] η ∧
      (∀ᵐ ω ∂S.μ, |η ω| ≤ B) ∧ ¬ η =ᵐ[S.μ] S.E s η) (a : ℝ) :
    (∀ u : ℕ → Ω → ℝ, StronglyAdapted S.𝓕 u → S.BddProc u →
      (∃ z, S.Solves a u z ∧ StronglyAdapted S.𝓕 z ∧ S.BddProc z) ∧
      ∀ z₁ z₂ : ℕ → Ω → ℝ, S.Solves a u z₁ → S.Solves a u z₂ → StronglyAdapted S.𝓕 z₁ →
        StronglyAdapted S.𝓕 z₂ → S.BddProc z₁ → S.BddProc z₂ → ∀ t, z₁ t =ᵐ[S.μ] z₂ t) ↔
      |a| < 1 := by
  constructor
  · intro h
    by_contra ha
    push Not at ha
    obtain ⟨s, η, B, hη, hηb, hηr⟩ := hnd
    have h0 := (h 0 (fun _ => stronglyMeasurable_zero)
      ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩).2
    obtain ⟨z', hz', hza', hzb', hne⟩ := S.not_unique_of_one_le ha hη hηb hηr (S.solves_zero a)
      (fun _ => stronglyMeasurable_zero) ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩
    exact hne (h0 z' 0 hz' (S.solves_zero a) hza' (fun _ => stronglyMeasurable_zero) hzb'
      ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩ (s + 1))
  · intro ha u hua hub
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := S.existsUnique_forward ha hua hub
    exact ⟨⟨_, h1, h2, h3⟩, fun z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂ =>
      (S.unique_iff hnd a).2 ha u z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂⟩

/-! ### AR(1) processes driven by martingale-difference shocks -/

/-- Cochrane (2023), Ch. 2, p. 29: the square of a bounded variable is bounded. -/
theorem BddRV.sq {S : MeasExpectationSystem Ω} {x : Ω → ℝ} (hx : S.BddRV x) : S.BddRV (x ^ 2) := by
  rw [pow_two]
  exact hx.mul hx

/-- Cochrane (2023), p. 42 (AR(1) surpluses `s_t = η s_{t−1} + ε_t`): for
`u_{t+1} = ρ u_t + ε_{t+1}` with bounded adapted `u` and martingale-difference shocks
(`E_t ε_{t+1} = 0`), `E_t u_{t+j} = ρʲ u_t` a.e. -/
theorem ar1_E {ρ : ℝ} {u ε : ℕ → Ω → ℝ} (hrec : ∀ t, u (t + 1) = ρ • u t + ε (t + 1))
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0) (t j : ℕ) :
    S.E t (u (t + j)) =ᵐ[S.μ] ρ ^ j • u t := by
  obtain ⟨M, hM⟩ := hub
  have hui : ∀ s, Integrable (u s) S.μ := fun s =>
    BddRV.integrable (BddRV.of_stronglyMeasurable (hua s) (hM s))
  have hεe : ∀ s, ε (s + 1) = u (s + 1) - ρ • u s := fun s => by
    rw [hrec s, add_sub_cancel_left]
  have hεi : ∀ s, Integrable (ε (s + 1)) S.μ := fun s => by
    rw [hεe]
    exact (hui _).sub ((hui s).smul ρ)
  induction j with
  | zero =>
    rw [add_zero, pow_zero, one_smul, S.E_of_stronglyMeasurable (hua t) (hui t)]
  | succ j ih =>
    have e : u (t + (j + 1)) = ρ • u (t + j) + ε (t + j + 1) := hrec (t + j)
    have hz : S.E t (ε (t + j + 1)) =ᵐ[S.μ] 0 := by
      filter_upwards [(S.E_tower (Nat.le_add_right t j) (ε (t + j + 1))).symm,
        S.E_congr (hmd (t + j)) t] with ω h1 h2
      rw [h1, h2, S.E_zero]
    rw [e]
    filter_upwards [S.E_add ((hui _).smul ρ) (hεi (t + j)) t, S.E_smul ρ (u (t + j)) t, ih, hz]
      with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h4, Pi.smul_apply, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, Pi.zero_apply, add_zero, pow_succ]
    ring

/-- Cochrane (2023), p. 42: with conditionally homoskedastic shocks (`E_t ε_{t+1}² = σ²`), the
squared forecast error of an AR(1) has conditional mean `σ² ∑_{i<j} ρ^{2i}`. -/
theorem ar1_E_sq_dev {ρ σ2 : ℝ} {u ε : ℕ → Ω → ℝ} (hrec : ∀ t, u (t + 1) = ρ • u t + ε (t + 1))
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hvar : ∀ t, S.E t (ε (t + 1) ^ 2) =ᵐ[S.μ] fun _ => σ2) (t j : ℕ) :
    S.E t ((u (t + j) - ρ ^ j • u t) ^ 2) =ᵐ[S.μ]
      fun _ => σ2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) := by
  obtain ⟨M, hM⟩ := hub
  have hB : ∀ s, S.BddRV (u s) := fun s => BddRV.of_stronglyMeasurable (hua s) (hM s)
  have hεe : ∀ s, ε (s + 1) = u (s + 1) - ρ • u s := fun s => by
    rw [hrec s, add_sub_cancel_left]
  have hεB : ∀ s, S.BddRV (ε (s + 1)) := fun s => by
    rw [hεe]
    exact (hB _).sub ((hB s).smul ρ)
  induction j with
  | zero =>
    have h0 : (u (t + 0) - ρ ^ 0 • u t) ^ 2 = 0 := by
      funext ω
      simp
    rw [h0, S.E_zero]
    exact Eventually.of_forall fun ω => by simp
  | succ j ih =>
    set w := u (t + j) - ρ ^ j • u t with hw
    set e' := ε (t + j + 1) with he'
    have hwB : S.BddRV w := (hB _).sub ((hB t).smul _)
    have hwm : StronglyMeasurable[S.𝓕 (t + j)] w :=
      (hua (t + j)).sub (((hua t).mono (S.𝓕.mono (Nat.le_add_right t j))).const_smul _)
    have hsplit : (u (t + (j + 1)) - ρ ^ (j + 1) • u t) ^ 2 =
        ρ ^ 2 • w ^ 2 + (2 * ρ) • (w * e') + e' ^ 2 := by
      have e : u (t + (j + 1)) = ρ • u (t + j) + ε (t + j + 1) := hrec (t + j)
      rw [e]
      funext ω
      simp only [hw, he', Pi.add_apply, Pi.smul_apply, Pi.pow_apply, Pi.sub_apply, Pi.mul_apply,
        smul_eq_mul]
      ring
    have hcross : S.E t (w * e') =ᵐ[S.μ] 0 := by
      obtain ⟨-, C, hC⟩ := hwB
      have hz : w * S.E (t + j) e' =ᵐ[S.μ] 0 := by
        filter_upwards [hmd (t + j)] with ω h
        rw [Pi.mul_apply, he', h, Pi.zero_apply, mul_zero]
      filter_upwards [(S.E_tower (Nat.le_add_right t j) (w * e')).symm,
        S.E_congr (S.E_pullOut hwm hC (hεB (t + j)).integrable) t, S.E_congr hz t]
        with ω h1 h2 h3
      rw [h1, h2, h3, S.E_zero]
    have hsq : S.E t (e' ^ 2) =ᵐ[S.μ] fun _ => σ2 := by
      filter_upwards [(S.E_tower (Nat.le_add_right t j) (e' ^ 2)).symm,
        S.E_congr (hvar (t + j)) t] with ω h1 h2
      rw [h1, h2, S.E_const]
    have I1 : Integrable (ρ ^ 2 • w ^ 2) S.μ := hwB.sq.integrable.smul _
    have I2 : Integrable ((2 * ρ) • (w * e')) S.μ := (hwB.mul (hεB (t + j))).integrable.smul _
    have I3 : Integrable (e' ^ 2) S.μ := (hεB (t + j)).sq.integrable
    have hs : ∑ i ∈ Finset.range (j + 1), ρ ^ (2 * i) =
        ρ ^ 2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    filter_upwards [S.E_add (I1.add I2) I3 t, S.E_add I1 I2 t, S.E_smul (ρ ^ 2) (w ^ 2) t,
      S.E_smul (2 * ρ) (w * e') t, ih, hcross, hsq] with ω h1 h2 h3 h4 h5 h6 h7
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, h5, h6, h7, hs,
      Pi.zero_apply, smul_eq_mul, smul_eq_mul]
    ring

/-- Cochrane (2023), p. 42: **conditional variance of an AR(1)** —
`Var_t(u_{t+j}) = σ² ∑_{i<j} ρ^{2i}` a.e. (Mathlib's `condVar`). -/
theorem ar1_condVar {ρ σ2 : ℝ} {u ε : ℕ → Ω → ℝ} (hrec : ∀ t, u (t + 1) = ρ • u t + ε (t + 1))
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hvar : ∀ t, S.E t (ε (t + 1) ^ 2) =ᵐ[S.μ] fun _ => σ2) (t j : ℕ) :
    Var[u (t + j); S.μ | S.𝓕 t] =ᵐ[S.μ] fun _ => σ2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) := by
  change S.E t ((u (t + j) - S.E t (u (t + j))) ^ 2) =ᵐ[S.μ] _
  refine (S.E_congr ?_ t).trans (S.ar1_E_sq_dev hrec hua hub hmd hvar t j)
  filter_upwards [S.ar1_E hrec hua hub hmd t j] with ω h
  rw [Pi.pow_apply, Pi.pow_apply, Pi.sub_apply, Pi.sub_apply, h]

/-- Cochrane (2023), p. 42: the closed form `Var_t(u_{t+j}) = σ² (1 − ρ^{2j}) / (1 − ρ²)` for
`ρ² ≠ 1`. -/
theorem ar1_condVar_closed {ρ σ2 : ℝ} (hρ : ρ ^ 2 ≠ 1) {u ε : ℕ → Ω → ℝ}
    (hrec : ∀ t, u (t + 1) = ρ • u t + ε (t + 1))
    (hua : StronglyAdapted S.𝓕 u) (hub : S.BddProc u)
    (hmd : ∀ t, S.E t (ε (t + 1)) =ᵐ[S.μ] 0)
    (hvar : ∀ t, S.E t (ε (t + 1) ^ 2) =ᵐ[S.μ] fun _ => σ2) (t j : ℕ) :
    Var[u (t + j); S.μ | S.𝓕 t] =ᵐ[S.μ] fun _ => σ2 * (1 - ρ ^ (2 * j)) / (1 - ρ ^ 2) := by
  refine (S.ar1_condVar hrec hua hub hmd hvar t j).trans (Eventually.of_forall fun _ => ?_)
  have h1 : 1 - ρ ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have hs : ∑ i ∈ Finset.range j, ρ ^ (2 * i) = (1 - ρ ^ (2 * j)) / (1 - ρ ^ 2) := by
    simp_rw [pow_mul]
    rw [geom_sum_eq hρ, eq_div_iff h1, div_mul_eq_mul_div, div_eq_iff (sub_ne_zero.mpr hρ)]
    ring
  change σ2 * ∑ i ∈ Finset.range j, ρ ^ (2 * i) = σ2 * (1 - ρ ^ (2 * j)) / (1 - ρ ^ 2)
  rw [hs, mul_div_assoc]

/-! ### Bridge to the core `ExpectationSystem` on a finite, fully supported state space -/

/-- Cochrane (2023), Ch. 2, p. 29: when every state has positive probability, a.e. equality is
equality. -/
theorem eq_of_ae_eq (hfull : ∀ ω, S.μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f =ᵐ[S.μ] g) : f = g := by
  funext ω
  by_contra hne
  have h0 : S.μ {ω' | f ω' ≠ g ω'} = 0 := ae_iff.mp h
  refine hfull ω (measure_mono_null (fun ω' hω' => ?_) h0)
  rw [Set.mem_singleton_iff.mp hω']
  exact hne

/-- Cochrane (2023), Ch. 2, p. 29: when every state has positive probability, a.e. inequality is
inequality. -/
theorem le_of_ae_le (hfull : ∀ ω, S.μ {ω} ≠ 0) {f g : Ω → ℝ} (h : f ≤ᵐ[S.μ] g) : f ≤ g := by
  intro ω
  by_contra hne
  have h0 : S.μ {ω' | ¬ f ω' ≤ g ω'} = 0 := ae_iff.mp h
  refine hfull ω (measure_mono_null (fun ω' hω' => ?_) h0)
  rw [Set.mem_singleton_iff.mp hω']
  exact hne

/-- Cochrane (2023), Ch. 2, p. 29: `E_t` as a linear map on all of `Ω → ℝ`, for a finite discrete
state space with full support. -/
noncomputable def ELin [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (t : ℕ) : (Ω → ℝ) →ₗ[ℝ] (Ω → ℝ) where
  toFun := S.E t
  map_add' _ _ := S.eq_of_ae_eq hfull (S.E_add Integrable.of_finite Integrable.of_finite t)
  map_smul' c x := S.eq_of_ae_eq hfull (S.E_smul c x t)

/-- Cochrane (2023), Ch. 2, p. 29: **bridge (b)** — on a finite discrete state space with full
support, a measure-theoretic expectation system is a core `ExpectationSystem`, with the same
`E_t` at every state, so every core theorem applies to it. -/
noncomputable def toExpectationSystem [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) : ExpectationSystem Ω where
  E := S.ELin hfull
  const := S.E_const
  mono t _ _ h := S.le_of_ae_le hfull
    (S.E_mono Integrable.of_finite Integrable.of_finite (Eventually.of_forall h) t)
  tower hst x := S.eq_of_ae_eq hfull (S.E_tower hst x)
  known hst x := S.E_known hst x

/-- Cochrane (2023), Ch. 2, p. 29: the core system's `E_t` is Mathlib's conditional
expectation, exactly. -/
theorem toExpectationSystem_E [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) (t : ℕ) (x : Ω → ℝ) :
    (S.toExpectationSystem hfull).E t x = S.E t x := rfl

/-- Cochrane (2023), Ch. 2, p. 29: the core system obtained from a measure-theoretic one has the
pull-out property, so `PullOut`-hypothesis theorems of the core apply too. -/
theorem toExpectationSystem_pullOut [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) : (S.toExpectationSystem hfull).PullOut := by
  have := Fintype.ofFinite Ω
  intro t a y ha
  rw [toExpectationSystem_E] at ha ⊢
  rw [toExpectationSystem_E]
  have hm : StronglyMeasurable[S.𝓕 t] a := ha ▸ S.stronglyMeasurable_E t a
  refine S.eq_of_ae_eq hfull (S.E_pullOut hm (C := ∑ ω, |a ω|)
    (Eventually.of_forall fun ω => ?_) Integrable.of_finite)
  exact Finset.single_le_sum (f := fun ω => |a ω|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ ω)

end MeasExpectationSystem

/-! ### Bridge (a): every finite event tree is a measure-theoretic expectation system -/

namespace TreeBridge

open ExpectationsFiniteTree

variable {Ω} [Fintype Ω] (T : FiniteTree Ω)

/-- Cochrane (2023), Ch. 2, p. 29: the tree with an uninformative date prepended (date `0`
knows nothing, date `t + 1` knows what the original tree knows at `t`). -/
def trivialFirst : FiniteTree Ω where
  prob := T.prob
  prob_pos := T.prob_pos
  prob_sum := T.prob_sum
  info n := match n with
    | 0 => Setoid.ker (fun _ : Ω => ())
    | n + 1 => T.info n
  refines := by
    intro s t hst a b h
    cases s with
    | zero => exact Setoid.ker_def.2 rfl
    | succ s =>
      cases t with
      | zero => omega
      | succ t => exact T.refines (by omega) a b h

omit mΩ in
/-- Cochrane (2023), Ch. 2, p. 29: **the law of total expectation on a finite tree**,
`∑ p(ω) E_t x(ω) = ∑ p(ω) x(ω)`. -/
theorem sum_prob_condE (t : ℕ) (x : Ω → ℝ) :
    ∑ ω, T.prob ω * T.condE t x ω = ∑ ω, T.prob ω * x ω := by
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := T.prob_sum
    simp at this
  have htriv : ∀ a b, (trivialFirst T).info 0 a b := fun _ _ => Setoid.ker_def.2 rfl
  have h1 := (trivialFirst T).condE_of_trivial htriv ((trivialFirst T).condE (t + 1) x) ω₀
  have h2 := (trivialFirst T).condE_of_trivial htriv x ω₀
  rw [(trivialFirst T).condE_tower (Nat.zero_le (t + 1)) x] at h1
  exact h1.symm.trans h2

/-- Cochrane (2023), Ch. 2, p. 29: the tree's probabilities as a measure,
`μ = ∑_ω p(ω) δ_ω`. -/
noncomputable def treeMeasure : Measure Ω := ∑ ω, ENNReal.ofReal (T.prob ω) • Measure.dirac ω

/-- Cochrane (2023), Ch. 2, p. 29: `μ{ω} = p(ω)`. -/
theorem treeMeasure_singleton [DiscreteMeasurableSpace Ω] (ω : Ω) :
    treeMeasure T {ω} = ENNReal.ofReal (T.prob ω) := by
  classical
  rw [treeMeasure, Measure.finsetSum_apply, Finset.sum_eq_single ω]
  · rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton ω), smul_eq_mul,
      mul_one]
  · intro b _ hb
    rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem (by simpa using hb),
      smul_eq_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ ω) h

/-- Cochrane (2023), Ch. 2, p. 29: the tree measure is a probability measure. -/
theorem treeMeasure_univ : treeMeasure T Set.univ = 1 := by
  rw [treeMeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => (T.prob_pos ω).le), T.prob_sum,
    ENNReal.ofReal_one]

/-- Cochrane (2023), Ch. 2, p. 29: the tree's probability measure. -/
noncomputable def treeProb : ProbabilityMeasure Ω := ⟨treeMeasure T, ⟨treeMeasure_univ T⟩⟩

/-- Cochrane (2023), Ch. 2, p. 29: integrals against the tree measure are weighted sums. -/
theorem integral_treeProb [DiscreteMeasurableSpace Ω] (f : Ω → ℝ) :
    ∫ ω, f ω ∂(treeProb T : Measure Ω) = ∑ ω, T.prob ω * f ω := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have h : (treeProb T : Measure Ω) {ω} = ENNReal.ofReal (T.prob ω) := treeMeasure_singleton T ω
  rw [measureReal_def, h, ENNReal.toReal_ofReal (T.prob_pos ω).le, smul_eq_mul]

/-- Cochrane (2023), Ch. 2, p. 29: the tree's information as a filtration, `𝓕_t = σ(cell_t)`. -/
def treeFiltration [DiscreteMeasurableSpace Ω] : Filtration ℕ mΩ where
  seq t := MeasurableSpace.comap (Quotient.mk (T.info t)) ⊤
  mono' s t hst := by
    intro A hA
    obtain ⟨B, -, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
    exact MeasurableSpace.measurableSet_comap.2
      ⟨Quotient.lift (Quotient.mk (T.info s)) (fun a b h => Quotient.sound (T.refines hst a b h))
        ⁻¹' B, MeasurableSpace.measurableSet_top, rfl⟩
  le' _ _ _ := MeasurableSet.of_discrete

/-- Cochrane (2023), Ch. 2, p. 29: the cell average `E_t x` is `𝓕_t`-measurable. -/
theorem stronglyMeasurable_condE [DiscreteMeasurableSpace Ω] (t : ℕ) (x : Ω → ℝ) :
    StronglyMeasurable[treeFiltration T t] (T.condE t x) := by
  have hm : Measurable[treeFiltration T t] (T.condE t x) := fun U _ =>
    MeasurableSpace.measurableSet_comap.2
      ⟨Quotient.lift (T.condE t x) (fun _ _ h => T.condE_congr x h) ⁻¹' U,
        MeasurableSpace.measurableSet_top, rfl⟩
  exact hm.stronglyMeasurable

/-- Cochrane (2023), Ch. 2, p. 29: the finite tree as a measure-theoretic expectation system. -/
noncomputable def treeSystem [DiscreteMeasurableSpace Ω] : MeasExpectationSystem Ω :=
  ⟨treeProb T, treeFiltration T⟩

/-- Cochrane (2023), Ch. 2, p. 29: every state of the tree has positive probability. -/
theorem treeSystem_fullSupport [DiscreteMeasurableSpace Ω] (ω : Ω) :
    (treeSystem T).μ {ω} ≠ 0 := by
  change treeMeasure T {ω} ≠ 0
  rw [treeMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact T.prob_pos ω

/-- Cochrane (2023), Ch. 2, p. 29: **bridge (a)** — the tree's cell average is Mathlib's
conditional expectation `μ[x | 𝓕_t]`, at every state and for every `x`. -/
theorem treeSystem_E [DiscreteMeasurableSpace Ω] (t : ℕ) (x : Ω → ℝ) :
    (treeSystem T).E t x = T.condE t x := by
  classical
  set S := treeSystem T
  refine (S.eq_of_ae_eq (treeSystem_fullSupport T)
    (ae_eq_condExp_of_forall_setIntegral_eq (S.𝓕.le t) Integrable.of_finite
      (fun _ _ _ => Integrable.of_finite.integrableOn) (fun A hA _ => ?_)
      (stronglyMeasurable_condE T t x).aestronglyMeasurable)).symm
  obtain ⟨B, -, hB⟩ := MeasurableSpace.measurableSet_comap.1 hA
  set a : Ω → ℝ := A.indicator fun _ => 1 with ha
  have hcell : ∀ ω ω', T.info t ω' ω → (ω' ∈ A ↔ ω ∈ A) := fun ω ω' h => by
    rw [← hB, Set.mem_preimage, Set.mem_preimage, Quotient.sound h]
  have hacell : T.condE t a = a := by
    funext ω
    refine T.condE_of_const_on_cell fun ω' h => ?_
    simp only [ha, Set.indicator, hcell ω ω' h]
  have hind : ∀ y : Ω → ℝ, A.indicator y = a * y := fun y => by
    funext ω
    by_cases h : ω ∈ A <;> simp [ha, Set.indicator, h]
  have hpo := finiteTree_pullOut T t a x hacell
  rw [FiniteTree.toExpectationSystem_E, FiniteTree.toExpectationSystem_E] at hpo
  rw [← integral_indicator MeasurableSet.of_discrete,
    ← integral_indicator MeasurableSet.of_discrete]
  change ∫ ω, A.indicator (T.condE t x) ω ∂(treeProb T : Measure Ω) =
    ∫ ω, A.indicator x ω ∂(treeProb T : Measure Ω)
  rw [integral_treeProb, integral_treeProb, hind, hind, ← hpo, sum_prob_condE]

/-- Cochrane (2023), Ch. 2, p. 29: the round trip — the core system obtained from the tree's
measure-theoretic system (bridge (b)) is the tree's own core system. -/
theorem treeSystem_toExpectationSystem_E [DiscreteMeasurableSpace Ω] (t : ℕ) (x : Ω → ℝ) :
    ((treeSystem T).toExpectationSystem (treeSystem_fullSupport T)).E t x =
      T.toExpectationSystem.E t x := by
  rw [MeasExpectationSystem.toExpectationSystem_E, treeSystem_E,
    FiniteTree.toExpectationSystem_E]

end TreeBridge

end Cochrane.DebtDeficitsInflation.ExpectationsMeasure
