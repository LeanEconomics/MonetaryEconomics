/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6HouseholdMoney
import NewKeynesianSelection.TidyR6ExpectationsMeasureIID

/-!
# Money in the utility function on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 439–441,
eqs. (19.9)–(19.16) and footnote 1, in the measure-theoretic setting of
TidyR6ExpectationsMeasure and TidyR6HouseholdMoney: the household maximises expected discounted
utility `E ∑ βᵗu(c_t, M_t/P_t)`, a genuine integral, subject to the period budget constraint
(19.10) with complete contingent claims holding almost surely, on a probability space whose
information may grow forever (the i.i.d. economy of TidyR6ExpectationsMeasureIID is not finitely
supported).

Restated from the Cochrane Monetarism project (its module MoneyInUtilityMeasure, without the links
to that project's finite-tree module MoneyInUtility) with the namespace renamed, for the household
problem behind Cochrane (2023), eq. (16.31), p. 393 (module TidyR6Household16_31).

## Main results

* **Necessity of (19.13)–(19.14)**, by bounded `𝓕_t`-measurable budget-neutral deviations
  (`TidyR6HouseholdMoney.pair_foc`): at an optimal plan with consumption and real balances
  essentially bounded at every date and regular prices,
  - `euler_step`: `β^{t+1}u_c(t+1) = (βᵗu_c(t)/Λ_t) Λ_{t+1}` almost surely;
  - `foc_1913`: `βᵗu_c(t) = λΛ_t` almost surely at every date, with the single multiplier
    `λ = u_c(0)/Λ_0` known at date `0` (footnote 1's `λ = u_c(c_0, M_0/P_0)` when `Λ_0 = 1`);
  - `money_foc`: `u_m(t) = u_c(t)ι_t` almost surely;
  - `foc_1914`: `βᵗu_m(t) = λΛ_tι_t = λΛ_t i_t/(1 + i_t)` almost surely;
  - `foc_normalised`: with the normalisation `Λ_0 = u_c(0)`, (19.13)–(19.14) as printed.
* **(19.15)–(19.16) and the value of money**, derived from optimality:
  - `bond_1915`: `u_c(t)Q_t = βP_tE_t[u_c(t+1)/P_{t+1}]` almost surely, and `bond_1915_ratio`:
    `Q_t = E_t[βu_c(t+1)/u_c(t) · P_t/P_{t+1}]` when `u_c(t) ≠ 0` with `1/u_c(t)` bounded;
  - `money_demand_1916`: `u_m/u_c = i_t/(1 + i_t)` with `1 + i_t = 1/Q_t`;
  - `value_recursion`: `u_c(t)/P_t = u_m(t)/P_t + βE_t[u_c(t+1)/P_{t+1}]` (a measure
    `Solves`), and `convenience_identity` (p. 441).
* **Sufficiency under concavity and the transversality condition** (`optimal_of_foc`): a
  feasible admissible plan with `βᵗu_c = λΛ_t`, `βᵗu_m = λΛ_tι_t` almost surely (`λ ≥ 0` a
  constant), jointly concave utility and `E[pk_T(a_T + M_{T−1})] → 0` is optimal;
  `optimal_iff_foc`: with `Λ_0 = u_c(0)` the conditions are necessary and sufficient.
* **The i.i.d. economy** (`IID.iid_optimal`, `IID.iid_necessity`, `IID.coin_economy`): with
  quadratic utility and an i.i.d. endowment on `TidyR6ExpectationsMeasureIID.iidSystem` (every
  history null for coin shocks), consuming the endowment with the money balances of (19.16) is
  optimal, and the derived (19.15)–(19.16) and the value-of-money recursion hold there.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6MoneyInUtility

open MeasureTheory ProbabilityTheory Filter Topology TidyR6ExpectationsMeasure
open TidyR6HouseholdMoney

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

variable (S) in
/-- Cochrane (2023), (19.9)–(19.10), p. 439: an optimal plan of the money-in-utility household
(no constraint beyond the budget and no-Ponzi conditions). -/
abbrev MIUOptimal (β : ℝ) (u : ℝ → ℝ → ℝ) (Λ P y s : ℕ → Ω → ℝ) (N0 a0 : Ω → ℝ)
    (c m a : ℕ → Ω → ℝ) : Prop :=
  Optimal S β u (fun _ _ => True) Λ P y s N0 a0 c m a

/-- Cochrane (2023), (19.13), p. 440: with no money in the bundle (`θ = 0`) the bundle cost is
one. -/
theorem wedge_zero (Λ P : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : wedge S 0 Λ P t ω = 1 := by
  simp [wedge]

/-! ### Necessity of the first-order conditions -/

/-- Cochrane (2023), (19.13), p. 440 and footnote 1, on a probability space: **the consumption
Euler equation.** At an optimal plan (smooth utility, regular prices, consumption and real
balances essentially bounded at every date),
`β^{t+1}u_c(t+1) = (βᵗu_c(t)/Λ_t) Λ_{t+1}` almost surely. -/
theorem euler_step {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, β ^ (t + 1) * uc (c (t + 1) ω) (m (t + 1) ω) =
      β ^ t * uc (c t ω) (m t ω) / Λ t ω * Λ (t + 1) ω := by
  have h := bundle_euler hβ hu hopt hp 0 (hcb t) (hcb (t + 1)) (hmb t) (hmb (t + 1))
    (Eventually.of_forall fun ω => by simp [wedge_zero])
    ⟨1, Eventually.of_forall fun ω => by simp [wedge_zero]⟩
    (fun _ _ _ _ => ⟨1, one_pos, fun _ _ => trivial⟩)
  filter_upwards [h] with ω hω
  simpa [wedge_zero] using hω

/-- Cochrane (2023), eq. (19.13), p. 440 and footnote 1 (`βᵗpr(xᵗ)u_c = pr(xᵗ)(Λ_t/Λ_0)λ`), on a
probability space: at an optimal plan, almost surely at every date
`βᵗu_c(c_t, M_t/P_t) = λΛ_t` with the single multiplier `λ = u_c(c_0, M_0/P_0)/Λ_0`, known at
date `0`. -/
theorem foc_1913 {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, β ^ t * uc (c t ω) (m t ω) = uc (c 0 ω) (m 0 ω) / Λ 0 ω * Λ t ω := by
  have h := bundle_multiplier_const hβ hu hopt hp 0 hcb hmb
    (fun _ => Eventually.of_forall fun ω => by simp [wedge_zero])
    (fun _ => ⟨1, Eventually.of_forall fun ω => by simp [wedge_zero]⟩)
    (fun _ _ _ _ _ => ⟨1, one_pos, fun _ _ => trivial⟩) t
  filter_upwards [h] with ω hω
  simp only [wedge_zero, zero_mul, add_zero, mul_one] at hω
  have := (hp.2.2.1 t ω).ne'
  rw [← hω]
  field_simp

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440 (dividing them, (19.16)), on a probability
space: **the money first-order condition.** At an optimal plan, `u_m(t) = u_c(t)ι_t` almost
surely, where `ι_t = 1 − Q_t = i_t/(1 + i_t)`. The deviation holds `εζ` more real balances at `t`
(`ζ` bounded, known at `t`), paid for by consuming less at `t + 1` the amount
`ζι_tΛ_t/Λ_{t+1}`. -/
theorem money_foc {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, um (c t ω) (m t ω) = uc (c t ω) (m t ω) * iota S Λ P t ω := by
  have hfeas := hopt.1
  have hca := hfeas.2.1
  have hma := hfeas.2.2.1
  have hle : S.𝓕 t ≤ S.𝓕 (t + 1) := S.𝓕.mono (Nat.le_succ t)
  have ae : ∀ {k : ℕ} {f : Ω → ℝ}, StronglyMeasurable[S.𝓕 k] f → AEStronglyMeasurable f S.μ :=
    fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  have hucm : ∀ n, StronglyMeasurable[S.𝓕 n] (fun ω => uc (c n ω) (m n ω)) := fun n =>
    (hu.2.1.measurable.comp ((hca n).measurable.prodMk (hma n).measurable)).stronglyMeasurable
  have humm : ∀ n, StronglyMeasurable[S.𝓕 n] (fun ω => um (c n ω) (m n ω)) := fun n =>
    (hu.2.2.measurable.comp ((hca n).measurable.prodMk (hma n).measurable)).stronglyMeasurable
  have hucb : ∀ n, BddAt S (fun ω => uc (c n ω) (m n ω)) := fun n =>
    BddAt.comp₂ hu.2.1 (hcb n) (hmb n)
  have humb : ∀ n, BddAt S (fun ω => um (c n ω) (m n ω)) := fun n =>
    BddAt.comp₂ hu.2.2 (hcb n) (hmb n)
  -- the test variable
  set G : Ω → ℝ := fun ω => um (c t ω) (m t ω) - uc (c t ω) (m t ω) * iota S Λ P t ω with hG
  have hGm : StronglyMeasurable[S.𝓕 t] G :=
    (humm t).sub ((hucm t).mul (hp.stronglyMeasurable_iota t))
  have hGb : BddAt S G := (humb t).sub ((hucb t).mul (hp.iota_bdd t))
  set z₂ : Ω → ℝ := fun ω => -(G ω * iota S Λ P t ω * Λ t ω / Λ (t + 1) ω) with hz₂
  have hz₂m : StronglyMeasurable[S.𝓕 (t + 1)] z₂ :=
    ((((hGm.mul (hp.stronglyMeasurable_iota t)).mul (hp.1 t)).mono hle).measurable.div
      (hp.1 (t + 1)).measurable).neg.stronglyMeasurable
  have hz₂b : BddAt S z₂ := by
    have := (((hGb.mul (hp.iota_bdd t)).mul (hp.2.2.2.2 t).1).mul
      (hp.2.2.2.2 (t + 1)).2.1).neg
    simpa [hz₂, div_eq_mul_inv] using this
  have h0m : ∀ k, StronglyMeasurable[S.𝓕 k] (fun _ : Ω => (0 : ℝ)) :=
    fun _ => stronglyMeasurable_const
  have hfin : ∀ᵐ ω ∂S.μ, Λ t ω * (0 + iota S Λ P t ω * G ω) +
      S.E t (fun ω => Λ (t + 1) ω * (z₂ ω + iota S Λ P (t + 1) ω * 0)) ω = 0 := by
    have e : (fun ω => Λ (t + 1) ω * (z₂ ω + iota S Λ P (t + 1) ω * 0)) =
        fun ω => -(G ω * iota S Λ P t ω * Λ t ω) := by
      funext ω
      have := (hp.2.2.1 (t + 1) ω).ne'
      simp only [hz₂]
      field_simp
      ring
    have hXm : StronglyMeasurable[S.𝓕 t] (fun ω => -(G ω * iota S Λ P t ω * Λ t ω)) :=
      ((hGm.mul (hp.stronglyMeasurable_iota t)).mul (hp.1 t)).neg
    have hXi : Integrable (fun ω => -(G ω * iota S Λ P t ω * Λ t ω)) S.μ :=
      (((hGb.mul (hp.iota_bdd t)).mul (hp.2.2.2.2 t).1).neg).integrable (ae hXm)
    rw [e, S.E_of_stronglyMeasurable hXm hXi]
    exact Eventually.of_forall fun ω => by ring
  have key := pair_foc hβ hu hopt hp (hcb t) (hcb (t + 1)) (hmb t) (hmb (t + 1)) (h0m t) hGm
    hz₂m (h0m (t + 1)) (BddAt.const 0) hGb hz₂b (BddAt.const 0) hfin
    ⟨1, one_pos, fun _ _ => trivial⟩
  -- rewrite with the Euler equation
  have i1 : Integrable (fun ω => um (c t ω) (m t ω) * G ω) S.μ :=
    ((humb t).mul hGb).integrable ((ae (humm t)).mul (ae hGm))
  have i2 : Integrable (fun ω => uc (c t ω) (m t ω) * iota S Λ P t ω * G ω) S.μ :=
    (((hucb t).mul (hp.iota_bdd t)).mul hGb).integrable
      (((ae (hucm t)).mul (ae (hp.stronglyMeasurable_iota t))).mul (ae hGm))
  have e1 : ∫ ω, (uc (c t ω) (m t ω) * 0 + um (c t ω) (m t ω) * G ω) ∂S.μ =
      ∫ ω, um (c t ω) (m t ω) * G ω ∂S.μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have e2 : β ^ (t + 1) * ∫ ω, (uc (c (t + 1) ω) (m (t + 1) ω) * z₂ ω +
      um (c (t + 1) ω) (m (t + 1) ω) * 0) ∂S.μ =
      -(β ^ t * ∫ ω, uc (c t ω) (m t ω) * iota S Λ P t ω * G ω ∂S.μ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [euler_step hβ hu hopt hp hcb hmb t] with ω h
    have := (hp.2.2.1 (t + 1) ω).ne'
    have := (hp.2.2.1 t ω).ne'
    have e : β ^ (t + 1) * (uc (c (t + 1) ω) (m (t + 1) ω) * z₂ ω +
        um (c (t + 1) ω) (m (t + 1) ω) * 0) =
        -(β ^ (t + 1) * uc (c (t + 1) ω) (m (t + 1) ω) * (G ω * iota S Λ P t ω * Λ t ω /
          Λ (t + 1) ω)) := by
      simp only [hz₂]
      ring
    rw [e, h]
    field_simp
  rw [e1, e2] at key
  have hGG : ∫ ω, G ω * G ω ∂S.μ = 0 := by
    have e3 : ∫ ω, G ω * G ω ∂S.μ = ∫ ω, um (c t ω) (m t ω) * G ω ∂S.μ -
        ∫ ω, uc (c t ω) (m t ω) * iota S Λ P t ω * G ω ∂S.μ := by
      rw [← integral_sub i1 i2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by simp only [hG]; ring)
    rw [e3]
    have hb : 0 < β ^ t := pow_pos hβ t
    have : β ^ t * (∫ ω, um (c t ω) (m t ω) * G ω ∂S.μ -
        ∫ ω, uc (c t ω) (m t ω) * iota S Λ P t ω * G ω ∂S.μ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb.ne'
    · exact h
  have hG0 := ae_eq_zero_of_integral_mul_self ((hGb.mul hGb).integrable
    ((ae hGm).mul (ae hGm))) hGG
  filter_upwards [hG0] with ω hω
  simp only [hG, Pi.zero_apply] at hω
  linarith

/-- Cochrane (2023), eq. (19.14), p. 440 and footnote 1, on a probability space: at an optimal
plan, almost surely at every date `βᵗu_m(c_t, M_t/P_t) = λΛ_tι_t = λΛ_t i_t/(1 + i_t)` with the
multiplier `λ = u_c(c_0, M_0/P_0)/Λ_0` of `foc_1913`. -/
theorem foc_1914 {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, β ^ t * um (c t ω) (m t ω) =
      uc (c 0 ω) (m 0 ω) / Λ 0 ω * Λ t ω * iota S Λ P t ω := by
  filter_upwards [foc_1913 hβ hu hopt hp hcb hmb t, money_foc hβ hu hopt hp hcb hmb t]
    with ω h1 h2
  rw [h2, ← mul_assoc, h1]

/-- Cochrane (2023), eqs. (19.13)–(19.14), p. 440, **as printed**: with the state prices
normalised so that `Λ_0 = u_c(c_0, M_0/P_0)` (state prices are defined up to a positive factor
known at date `0`), an optimal plan has `βᵗu_c(c_t, M_t/P_t) = Λ_t` and
`βᵗu_m(c_t, M_t/P_t) = Λ_t i_t/(1 + i_t)` almost surely, with `i_t/(1 + i_t) = ι_t = 1 − Q_t`. -/
theorem foc_normalised {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n))
    (hnorm : ∀ ω, Λ 0 ω = uc (c 0 ω) (m 0 ω)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, β ^ t * uc (c t ω) (m t ω) = Λ t ω ∧
      β ^ t * um (c t ω) (m t ω) = Λ t ω * iota S Λ P t ω := by
  filter_upwards [foc_1913 hβ hu hopt hp hcb hmb t, foc_1914 hβ hu hopt hp hcb hmb t]
    with ω h1 h2
  have := (hp.2.2.1 0 ω).ne'
  rw [← hnorm ω, div_self this, one_mul] at h1 h2
  exact ⟨h1, h2⟩


/-! ### (19.15)–(19.16) and the value of money -/

/-- Cochrane (2023), eq. (19.15), p. 441, on a probability space, derived from optimality: the
bond price satisfies `u_c(t)Q_t = βP_tE_t[u_c(t+1)/P_{t+1}]` almost surely, where
`Q_t = E_t[pk_{t+1}]/pk_t = 1/(1 + i_t)` is the price of a one-period nominal bond. -/
theorem bond_1915 {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, uc (c t ω) (m t ω) * bondPrice S Λ P t ω =
      β * P t ω * S.E t (fun ω => uc (c (t + 1) ω) (m (t + 1) ω) / P (t + 1) ω) ω := by
  have hca := hopt.1.2.1
  have hma := hopt.1.2.2.1
  set f : Ω → ℝ := fun ω => β ^ t * uc (c t ω) (m t ω) / Λ t ω / β ^ (t + 1) with hf
  have hfm : StronglyMeasurable[S.𝓕 t] f :=
    ((((hu.2.1.measurable.comp ((hca t).measurable.prodMk (hma t).measurable)).const_mul
      (β ^ t)).div (hp.1 t).measurable).div_const _).stronglyMeasurable
  have hfb : BddAt S f := by
    have := (((BddAt.const (β ^ t)).mul (BddAt.comp₂ hu.2.1 (hcb t) (hmb t))).mul
      (hp.2.2.2.2 t).2.1).mul (BddAt.const (β ^ (t + 1))⁻¹)
    simpa [hf, div_eq_mul_inv] using this
  obtain ⟨K, hK⟩ := hfb
  have hae : (fun ω => uc (c (t + 1) ω) (m (t + 1) ω) / P (t + 1) ω) =ᵐ[S.μ]
      f * pk Λ P (t + 1) := by
    filter_upwards [euler_step hβ hu hopt hp hcb hmb t] with ω h
    have hb := (pow_pos hβ (t + 1)).ne'
    have := (hp.2.2.2.1 (t + 1) ω).ne'
    have key : uc (c (t + 1) ω) (m (t + 1) ω) =
        β ^ t * uc (c t ω) (m t ω) / Λ t ω * Λ (t + 1) ω / β ^ (t + 1) := by
      rw [← h]
      field_simp
    simp only [Pi.mul_apply, hf, pk]
    rw [key]
    ring
  filter_upwards [S.E_congr hae t, S.E_pullOut hfm hK (hp.integrable_pk (t + 1))] with ω h1 h2
  rw [h1, h2, Pi.mul_apply, hp.E_pk_eq t ω]
  have := (hp.2.2.1 t ω).ne'
  have := (hp.2.2.2.1 t ω).ne'
  have hb := (pow_pos hβ t).ne'
  simp only [hf, pk, pow_succ]
  field_simp

/-- Cochrane (2023), eq. (19.15), p. 441, **as printed**: if marginal utility `u_c(c_t, m_t)` is
nonzero with essentially bounded reciprocal (e.g. `u_c > 0` continuous), an optimal plan has
`Q_t = 1/(1 + i_t) = E_t[β u_c(t+1)/u_c(t) · P_t/P_{t+1}]` almost surely. -/
theorem bond_1915_ratio {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n))
    (hucne : ∀ t ω, uc (c t ω) (m t ω) ≠ 0)
    (hucinv : ∀ t, BddAt S fun ω => (uc (c t ω) (m t ω))⁻¹) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, bondPrice S Λ P t ω = S.E t (fun ω => β * (uc (c (t + 1) ω) (m (t + 1) ω) /
      uc (c t ω) (m t ω)) * (P t ω / P (t + 1) ω)) ω := by
  have hca := hopt.1.2.1
  have hma := hopt.1.2.2.1
  set f : Ω → ℝ := fun ω => P t ω / uc (c t ω) (m t ω) with hf
  have hfm : StronglyMeasurable[S.𝓕 t] f :=
    ((hp.2.1 t).measurable.div (hu.2.1.measurable.comp
      ((hca t).measurable.prodMk (hma t).measurable))).stronglyMeasurable
  have hfb : BddAt S f := by
    have := (hp.2.2.2.2 t).2.2.1.mul (hucinv t)
    simpa [hf, div_eq_mul_inv] using this
  obtain ⟨K, hK⟩ := hfb
  set X : Ω → ℝ := fun ω => uc (c (t + 1) ω) (m (t + 1) ω) / P (t + 1) ω with hX
  have hXi : Integrable X S.μ := by
    have hb := (BddAt.comp₂ hu.2.1 (hcb (t + 1)) (hmb (t + 1))).mul
      (hp.2.2.2.2 (t + 1)).2.2.2
    refine (hb.integrable ?_).congr (Eventually.of_forall fun ω => by
      simp only [hX, div_eq_mul_inv])
    exact (((hu.2.1.measurable.comp ((hca (t + 1)).measurable.prodMk
      (hma (t + 1)).measurable)).mul (hp.2.1 (t + 1)).measurable.inv).stronglyMeasurable.mono
      (S.𝓕.le (t + 1))).aestronglyMeasurable
  have e : (fun ω => β * (uc (c (t + 1) ω) (m (t + 1) ω) / uc (c t ω) (m t ω)) *
      (P t ω / P (t + 1) ω)) = f * (β • X) := by
    funext ω
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hf, hX]
    ring
  rw [e]
  filter_upwards [S.E_pullOut hfm hK (hXi.smul β), S.E_smul β X t,
    bond_1915 hβ hu hopt hp hcb hmb t] with ω h1 h2 h3
  rw [h1, Pi.mul_apply, h2, Pi.smul_apply, smul_eq_mul]
  have := hucne t ω
  simp only [hf]
  rw [div_mul_eq_mul_div, eq_div_iff this, mul_comm, h3]
  ring

/-- Cochrane (2023), eq. (19.16), p. 441, on a probability space, derived from optimality:
**money demand.** With `1 + i_t = 1/Q_t`, an optimal plan with `u_c ≠ 0` has
`u_m(t)/u_c(t) = i_t/(1 + i_t)` almost surely (and `i_t/(1 + i_t) = ι_t = 1 − Q_t`). -/
theorem money_demand_1916 {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n))
    (hucne : ∀ t ω, uc (c t ω) (m t ω) ≠ 0) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, um (c t ω) (m t ω) / uc (c t ω) (m t ω) =
        (1 / bondPrice S Λ P t ω - 1) / (1 + (1 / bondPrice S Λ P t ω - 1)) ∧
      (1 / bondPrice S Λ P t ω - 1) / (1 + (1 / bondPrice S Λ P t ω - 1)) =
        iota S Λ P t ω := by
  filter_upwards [money_foc hβ hu hopt hp hcb hmb t, hp.bondPrice_pos t] with ω h hQ
  have hQ0 := hQ.ne'
  have hu0 := hucne t ω
  have e : (1 / bondPrice S Λ P t ω - 1) / (1 + (1 / bondPrice S Λ P t ω - 1)) =
      iota S Λ P t ω := by
    simp only [iota]
    field_simp
    ring
  refine ⟨?_, e⟩
  rw [e, h]
  field_simp

/-- Cochrane (2023), (19.15)–(19.16), p. 441, on a probability space, derived from optimality:
**the value of money.** The value of a dollar `v_t = u_c(t)/P_t` solves
`v_t = u_m(t)/P_t + βE_tv_{t+1}` almost surely at every date (the measure-theoretic `Solves`;
the Monetarism project's finite-state version assumes (19.15)–(19.16)). -/
theorem value_recursion {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) :
    S.Solves β (fun t ω => um (c t ω) (m t ω) / P t ω)
      (fun t ω => uc (c t ω) (m t ω) / P t ω) := by
  intro t
  filter_upwards [bond_1915 hβ hu hopt hp hcb hmb t, money_foc hβ hu hopt hp hcb hmb t]
    with ω h1 h2
  have := (hp.2.2.2.1 t ω).ne'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [h2]
  simp only [iota]
  field_simp
  linear_combination h1

/-- Cochrane (2023), p. 441 ("We can also write from the first-order conditions"), on a
probability space: if `u_c(c_t, m_t)` is nonzero with essentially bounded reciprocal, an optimal
plan has
`1 = u_m(t)/u_c(t) + E_t[βu_c(t+1)/u_c(t) · P_t/P_{t+1}]` almost surely (the convenience yield of
money plus its pecuniary return). -/
theorem convenience_identity {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ}
    (hu : Smooth₂ u uc um) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n))
    (hucne : ∀ t ω, uc (c t ω) (m t ω) ≠ 0)
    (hucinv : ∀ t, BddAt S fun ω => (uc (c t ω) (m t ω))⁻¹) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, 1 = um (c t ω) (m t ω) / uc (c t ω) (m t ω) +
      S.E t (fun ω => β * (uc (c (t + 1) ω) (m (t + 1) ω) / uc (c t ω) (m t ω)) *
        (P t ω / P (t + 1) ω)) ω := by
  filter_upwards [money_foc hβ hu hopt hp hcb hmb t,
    bond_1915_ratio hβ hu hopt hp hcb hmb hucne hucinv t] with ω h1 h2
  rw [← h2, h1]
  have := hucne t ω
  simp only [iota]
  field_simp
  ring

/-! ### Sufficiency -/

/-- Cochrane (2023), eqs. (19.13)–(19.14) and footnote 1, p. 440, on a probability space,
**sufficiency under concavity and the transversality condition**: if `u` is jointly concave in the
supergradient form `u(c', m') ≤ u(c, m) + u_c(c' − c) + u_m(m' − m)`, and a feasible admissible
plan satisfies `βᵗu_c(t) = λΛ_t` and `βᵗu_m(t) = λΛ_tι_t` almost surely at every date (`λ ≥ 0` a
constant) and the transversality condition `E[pk_T(a_T + M_{T−1})] → 0`, then it is optimal. -/
theorem optimal_of_foc {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ}
    (hsup : ∀ x y x' y', u x' y' ≤ u x y + uc x y * (x' - x) + um x y * (y' - y))
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} (hp : PriceRegular S Λ P)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hf : Feasible S Λ P y s N0 a0 c m a)
    (hadm : UAdmissible S β (fun n ω => u (c n ω) (m n ω)))
    (hfoc : ∀ t, ∀ᵐ ω ∂S.μ, β ^ t * uc (c t ω) (m t ω) = lam * Λ t ω ∧
      β ^ t * um (c t ω) (m t ω) = lam * Λ t ω * iota S Λ P t ω)
    (htvc : Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0)) :
    MIUOptimal S β u Λ P y s N0 a0 c m a := by
  refine optimal_of_supergradient hβ hp hy hs hlam hf trivial hadm htvc
    fun c' m' a' _ _ t => ?_
  filter_upwards [hfoc t] with ω h
  have h3 := mul_le_mul_of_nonneg_left
    (show u (c' t ω) (m' t ω) - u (c t ω) (m t ω) ≤ uc (c t ω) (m t ω) * (c' t ω - c t ω) +
      um (c t ω) (m t ω) * (m' t ω - m t ω) by
        linarith [hsup (c t ω) (m t ω) (c' t ω) (m' t ω)]) (pow_nonneg hβ.le t)
  have e : β ^ t * (uc (c t ω) (m t ω) * (c' t ω - c t ω) +
      um (c t ω) (m t ω) * (m' t ω - m t ω)) =
      lam * (Λ t ω * ((c' t ω - c t ω) + iota S Λ P t ω * (m' t ω - m t ω))) := by
    linear_combination (c' t ω - c t ω) * h.1 + (m' t ω - m t ω) * h.2
  rw [e] at h3
  exact h3

/-- Cochrane (2023), eqs. (19.13)–(19.14) and footnote 1, p. 440, on a probability space,
**necessary and sufficient conditions**: for jointly concave smooth utility, regular prices,
consumption and real balances essentially bounded at every date, and state prices normalised by
`Λ_0 = u_c(c_0, M_0/P_0)`, a feasible admissible plan satisfying the transversality condition is
optimal if and only if `βᵗu_c(t) = Λ_t` and `βᵗu_m(t) = Λ_t i_t/(1 + i_t)` almost surely at
every date. -/
theorem optimal_iff_foc {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    (hsup : ∀ x y x' y', u x' y' ≤ u x y + uc x y * (x' - x) + um x y * (y' - y))
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} (hp : PriceRegular S Λ P)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a)
    (hadm : UAdmissible S β (fun n ω => u (c n ω) (m n ω)))
    (htvc : Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0))
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n))
    (hnorm : ∀ ω, Λ 0 ω = uc (c 0 ω) (m 0 ω)) :
    MIUOptimal S β u Λ P y s N0 a0 c m a ↔ ∀ t, ∀ᵐ ω ∂S.μ,
      β ^ t * uc (c t ω) (m t ω) = Λ t ω ∧
        β ^ t * um (c t ω) (m t ω) = Λ t ω * iota S Λ P t ω := by
  refine ⟨fun hopt t => foc_normalised hβ hu hopt hp hcb hmb hnorm t, fun hfoc => ?_⟩
  exact optimal_of_foc hβ hsup hp hy hs zero_le_one hf hadm
    (fun t => (hfoc t).mono fun ω h => ⟨by rw [one_mul]; exact h.1,
      by rw [one_mul]; exact h.2⟩) htvc




/-! ### The i.i.d. economy: a genuine infinite state space -/

namespace IID

open TidyR6ExpectationsMeasureIID

variable (ν : ProbabilityMeasure ℝ)

/-- Cochrane (2023), §19.3, p. 439 (an endowment shock): the shock clipped to `[−1, 1]`. -/
def clamp (x : ℝ) : ℝ := max (-1) (min 1 x)

/-- Cochrane (2023), §19.3, p. 439: the clipped shock lies in `[−1, 1]`. -/
theorem abs_clamp_le (x : ℝ) : |clamp x| ≤ 1 :=
  abs_le.2 ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Cochrane (2023), §19.3, p. 439: clipping is continuous. -/
theorem continuous_clamp : Continuous clamp :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Cochrane (2023), §19.3, p. 439: the i.i.d. endowment `y_t = 2 + clamp(ε_t)/2 ∈ [3/2, 5/2]`. -/
noncomputable def endow (t : ℕ) (ω : ℕ → ℝ) : ℝ := 2 + clamp (ω t) / 2

/-- Cochrane (2023), §19.3, p. 439: `3/2 ≤ y_t ≤ 5/2`. -/
theorem endow_bounds (t : ℕ) (ω : ℕ → ℝ) : 3 / 2 ≤ endow t ω ∧ endow t ω ≤ 5 / 2 := by
  have := abs_le.1 (abs_clamp_le (ω t))
  simp only [endow]
  constructor <;> linarith [this.1, this.2]

/-- Cochrane (2023), §19.3, p. 439: the endowment is known at its date. -/
theorem measurable_endow (t : ℕ) : StronglyMeasurable[(iidSystem ν).𝓕 t] (endow t) :=
  (((continuous_clamp.measurable.comp (measurable_shock ν (le_refl t))).div_const 2).const_add
    2).stronglyMeasurable

/-- Cochrane (2023), §19.3, p. 439: the mean endowment `ȳ = 2 + E[clamp ε]/2`. -/
noncomputable def ybar : ℝ := 2 + (∫ x, clamp x ∂(ν : Measure ℝ)) / 2

/-- Cochrane (2023), §19.3, p. 439: `3/2 ≤ ȳ ≤ 5/2`. -/
theorem ybar_bounds : 3 / 2 ≤ ybar ν ∧ ybar ν ≤ 5 / 2 := by
  have h : ‖∫ x, clamp x ∂(ν : Measure ℝ)‖ ≤ 1 * (ν : Measure ℝ).real Set.univ :=
    norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_clamp_le x)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  have := abs_le.1 h
  simp only [ybar]
  constructor <;> linarith [this.1, this.2]

/-- Cochrane (2023), (19.9), p. 439: the quadratic period utility
`u(c, m) = 4c − c²/2 + 4m − m²/2`. -/
noncomputable def qU (c m : ℝ) : ℝ := (4 * c - c ^ 2 / 2) + (4 * m - m ^ 2 / 2)

/-- Cochrane (2023), (19.9), p. 439: the quadratic utility is smooth with `u_c = 4 − c`,
`u_m = 4 − m`. -/
theorem smooth_qU : Smooth₂ qU (fun c _ => 4 - c) (fun _ m => 4 - m) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => 4 * x - x ^ 2 / 2) (4 - x) x := fun x =>
    (((hasDerivAt_id' x).const_mul 4).sub ((hasDerivAt_pow 2 x).div_const 2)).congr_deriv
      (by simp)
  exact smooth₂_sep hd (continuous_const.sub continuous_id) hd
    (continuous_const.sub continuous_id)

/-- Cochrane (2023), (19.9), p. 439: the quadratic utility is jointly concave (supergradient
form). -/
theorem qU_sup (x y x' y' : ℝ) :
    qU x' y' ≤ qU x y + (4 - x) * (x' - x) + (4 - y) * (y' - y) := by
  simp only [qU]
  nlinarith [sq_nonneg (x' - x), sq_nonneg (y' - y)]

/-- Cochrane (2023), (19.13), p. 440: the equilibrium state prices `Λ_t = βᵗu_c(y_t) =
βᵗ(4 − y_t)`. -/
noncomputable def lam (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := β ^ t * (4 - endow t ω)

/-- Cochrane (2023), (19.16), p. 441: the money balances `m_t = y_t + β(4 − ȳ)` that satisfy
`u_m = u_c i/(1 + i)`. -/
noncomputable def money (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ := endow t ω + β * (4 - ybar ν)

/-- Cochrane (2023), (19.10), p. 439: the transfers `s_t = M_{t−1} − M_t` (with `P = 1`,
`M_{−1} = 0`, no bonds) that make the endowment plan satisfy the flow constraint. -/
noncomputable def taxes (β : ℝ) (t : ℕ) (ω : ℕ → ℝ) : ℝ :=
  moneyIn (fun _ => 0) (fun _ _ => 1) (money ν β) t ω - money ν β t ω

/-- Cochrane (2023), (19.15), p. 441: in the i.i.d. economy `E_t pk_{t+1} = β^{t+1}(4 − ȳ)`. -/
theorem E_pk_iid (β : ℝ) (t : ℕ) :
    (iidSystem ν).E t (pk (lam β) (fun _ _ => 1) (t + 1)) =ᵐ[(iidSystem ν).μ]
      fun _ => β ^ (t + 1) * (4 - ybar ν) := by
  set f : ℝ → ℝ := fun x => β ^ (t + 1) * (4 - (2 + clamp x / 2)) / 1 with hf
  have hfm : Measurable f :=
    ((((continuous_clamp.measurable.div_const 2).const_add 2).const_sub 4).const_mul _).div_const _
  have e : pk (lam β) (fun _ _ => 1) (t + 1) = fun ω => f (ω (t + 1)) := rfl
  rw [e]
  filter_upwards [E_shock_fun ν t hfm] with ω h
  rw [h]
  have hi : Integrable clamp (ν : Measure ℝ) :=
    Integrable.of_bound continuous_clamp.measurable.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_clamp_le x)
  have e2 : (fun x => f x) = fun x => (β ^ (t + 1) * 2) - (β ^ (t + 1) / 2) * clamp x := by
    funext x
    simp only [hf]
    ring
  simp only [e2]
  rw [integral_sub (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul,
    probReal_univ, one_smul, ybar]
  ring

variable {ν}

/-- Cochrane (2023), (19.13), p. 440: the i.i.d. state prices are positive. -/
theorem lam_pos {β : ℝ} (hβ0 : 0 < β) (t : ℕ) (ω : ℕ → ℝ) : 0 < lam β t ω := by
  have := (endow_bounds t ω).2
  exact mul_pos (pow_pos hβ0 t) (by linarith)

/-- Cochrane (2023), p. 439: the i.i.d. state prices and the constant price level `P = 1` are
regular. -/
theorem iid_priceRegular {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    PriceRegular (iidSystem ν) (lam β) (fun _ _ => 1) := by
  have hlm : ∀ t, StronglyMeasurable[(iidSystem ν).𝓕 t] (lam β t) := fun t =>
    (stronglyMeasurable_const.sub (measurable_endow ν t)).const_mul _
  refine ⟨hlm, fun _ => stronglyMeasurable_const, fun t ω => lam_pos hβ0 t ω,
    fun _ _ => one_pos, fun t => ⟨⟨5 / 2, Eventually.of_forall fun ω => ?_⟩,
      ⟨2 / (3 * β ^ t), Eventually.of_forall fun ω => ?_⟩, BddAt.const 1,
      ⟨1, Eventually.of_forall fun _ => by norm_num⟩⟩⟩
  · have h1 := endow_bounds t ω
    have hb : β ^ t ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    rw [abs_of_pos (lam_pos hβ0 t ω)]
    simp only [lam]
    nlinarith [pow_pos hβ0 t]
  · have h1 := (endow_bounds t ω).2
    have hb := pow_pos hβ0 t
    rw [abs_of_pos (inv_pos.2 (lam_pos hβ0 t ω)), inv_le_comm₀ (lam_pos hβ0 t ω)
      (by positivity)]
    simp only [lam]
    rw [inv_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith

/-- Cochrane (2023), §19.3, pp. 439–441, **the i.i.d. money-in-utility economy**: on
`TidyR6ExpectationsMeasureIID.iidSystem` `ν` (any shock law `ν`; every history null when `ν` is
nondegenerate), with `0 < β < 1`, quadratic utility, `P = 1`, state prices
`Λ_t = βᵗ(4 − y_t)` and transfers `s_t = M_{t−1} − M_t`, consuming the endowment and holding
`m_t = y_t + β(4 − ȳ)` with no bonds is optimal (`optimal_of_foc`: concavity, the first-order
conditions and the transversality condition). -/
theorem iid_optimal {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    MIUOptimal (iidSystem ν) β qU (lam β) (fun _ _ => 1) endow (taxes ν β) (fun _ => 0)
      (fun _ => 0) endow (money ν β) (fun _ _ => 0) := by
  set S := iidSystem ν with hS
  have hyb := ybar_bounds ν
  have hlpos : ∀ t ω, 0 < lam β t ω := fun t ω => by
    have := (endow_bounds t ω).2
    exact mul_pos (pow_pos hβ0 t) (by linarith)
  have hmm : ∀ t, StronglyMeasurable[S.𝓕 t] (money ν β t) := fun t =>
    (measurable_endow ν t).add stronglyMeasurable_const
  have hlm : ∀ t, StronglyMeasurable[S.𝓕 t] (lam β t) := fun t =>
    (stronglyMeasurable_const.sub (measurable_endow ν t)).const_mul _
  have ae : ∀ {k : ℕ} {f : (ℕ → ℝ) → ℝ}, StronglyMeasurable[S.𝓕 k] f →
      AEStronglyMeasurable f S.μ := fun {k} _ h => (h.mono (S.𝓕.le k)).aestronglyMeasurable
  -- bounds
  have hlb : ∀ t ω, |lam β t ω| ≤ 5 / 2 := fun t ω => by
    have h1 := endow_bounds t ω
    have hb : β ^ t ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    rw [abs_of_pos (hlpos t ω)]
    simp only [lam]
    nlinarith [pow_pos hβ0 t]
  have hmb : ∀ t ω, |money ν β t ω| ≤ 5 := fun t ω => by
    have h1 := endow_bounds t ω
    simp only [money]
    rw [abs_le]
    constructor <;> nlinarith
  have hyb' : ∀ t ω, |endow t ω| ≤ 5 / 2 := fun t ω => by
    have h1 := endow_bounds t ω
    rw [abs_le]
    constructor <;> linarith
  have hmIn : ∀ t ω, |moneyIn (fun _ => 0) (fun _ _ => (1 : ℝ)) (money ν β) t ω| ≤ 5 := by
    intro t ω
    cases t with
    | zero => simp [moneyIn]
    | succ k => simpa [moneyIn] using hmb k ω
  have hmInm : ∀ t, StronglyMeasurable[S.𝓕 t]
      (moneyIn (fun _ => 0) (fun _ _ => (1 : ℝ)) (money ν β) t) := by
    intro t
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ k =>
      have : moneyIn (fun _ => 0) (fun _ _ => (1 : ℝ)) (money ν β) (k + 1) =
          fun ω => 1 * money ν β k ω := rfl
      rw [this]
      exact ((hmm k).const_mul 1).mono (S.𝓕.mono (Nat.le_succ k))
  have hbdd : ∀ {f : (ℕ → ℝ) → ℝ} {K : ℝ}, (∀ ω, |f ω| ≤ K) → BddAt S f :=
    fun {f} {K} h => ⟨K, Eventually.of_forall h⟩
  have hint : ∀ {k : ℕ} {f : (ℕ → ℝ) → ℝ} {K : ℝ}, StronglyMeasurable[S.𝓕 k] f →
      (∀ ω, |f ω| ≤ K) → Integrable f S.μ :=
    fun {k} {f} {K} hm h => (hbdd h).integrable (ae hm)
  have hp : PriceRegular S (lam β) (fun _ _ => 1) := iid_priceRegular hβ0 hβ1
  have hpk : ∀ t ω, pk (lam β) (fun _ _ => (1 : ℝ)) t ω = lam β t ω := fun t ω => by
    simp [pk]
  -- feasibility
  have hflow : Flow S (lam β) (fun _ _ => 1) endow (taxes ν β) (fun _ => 0) endow (money ν β)
      (fun _ _ => 0) := by
    intro t
    refine Eventually.of_forall fun ω => ?_
    have e0 : S.E t (fun _ => (0 : ℝ)) = 0 := S.E_zero t
    simp only [claimCost, mul_zero, e0, taxes, Pi.zero_apply, zero_div, sub_self, one_mul,
      zero_add, add_zero]
    ring
  have hfeas : Feasible S (lam β) (fun _ _ => 1) endow (taxes ν β) (fun _ => 0) (fun _ => 0)
      endow (money ν β) (fun _ _ => 0) := by
    refine ⟨rfl, fun t => measurable_endow ν t, hmm, fun _ => stronglyMeasurable_const, hflow,
      fun t => by simp, fun t => ?_, fun t => ?_, fun t => ?_, fun δ hδ => ?_⟩
    · refine hint (k := t) (K := 5 / 2 * 5) ((hp.stronglyMeasurable_pk t).mul (hmInm t))
        fun ω => ?_
      rw [abs_mul, hpk]
      exact mul_le_mul (hlb t ω) (hmIn t ω) (abs_nonneg _) (by norm_num)
    · refine hint (k := t) (K := 5 / 2 * 5) ((hlm t).mul (hmm t)) fun ω => ?_
      rw [abs_mul]
      exact mul_le_mul (hlb t ω) (hmb t ω) (abs_nonneg _) (by norm_num)
    · refine hint (k := t) (K := 5 / 2 * (5 / 2)) ((hlm t).mul (measurable_endow ν t))
        fun ω => ?_
      rw [abs_mul]
      exact mul_le_mul (hlb t ω) (hyb' t ω) (abs_nonneg _) (by norm_num)
    · refine Eventually.of_forall fun T => ?_
      refine le_trans (by linarith) (integral_nonneg fun ω => ?_)
      rw [hpk, zero_add]
      refine mul_nonneg (hlpos T ω).le ?_
      cases T with
      | zero => simp [moneyIn]
      | succ k =>
        have := (endow_bounds k ω).1
        simp only [moneyIn, one_mul, money]
        nlinarith
  -- admissibility
  have hadm : UAdmissible S β (fun n ω => qU (endow n ω) (money ν β n ω)) := by
    refine UAdmissible.of_bdd hβ0.le hβ1 (fun n => ae (k := n)
      ((smooth_qU.continuous.measurable.comp ((measurable_endow ν n).measurable.prodMk
        (hmm n).measurable)).stronglyMeasurable)) (K := 60) fun n ω => ?_
    have h1 := abs_le.1 (hyb' n ω)
    have h2 := abs_le.1 (hmb n ω)
    simp only [qU]
    rw [abs_le]
    constructor <;> nlinarith
  -- the transversality condition
  have htvc : Tendsto (wealthPV S (lam β) (fun _ _ => 1) (fun _ => 0) (money ν β)
      (fun _ _ => 0)) atTop (𝓝 0) := by
    have hb : ∀ T, ‖wealthPV S (lam β) (fun _ _ => 1) (fun _ => 0) (money ν β)
        (fun _ _ => 0) T‖ ≤ 13 * β ^ T := by
      intro T
      have h := norm_integral_le_of_norm_le_const (μ := S.μ) (C := 13 * β ^ T)
        (f := fun ω => pk (lam β) (fun _ _ => 1) T ω *
          ((fun _ _ => (0 : ℝ)) T ω + moneyIn (fun _ => 0) (fun _ _ => 1) (money ν β) T ω))
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, hpk, zero_add, abs_mul]
          have h1 := endow_bounds T ω
          have h2 := hmIn T ω
          have h3 : |lam β T ω| ≤ 5 / 2 * β ^ T := by
            rw [abs_of_pos (hlpos T ω)]
            simp only [lam]
            nlinarith [pow_pos hβ0 T]
          nlinarith [abs_nonneg (lam β T ω), abs_nonneg (moneyIn (fun _ => (0 : ℝ))
            (fun _ _ => (1 : ℝ)) (money ν β) T ω), pow_pos hβ0 T])
      rw [probReal_univ, mul_one] at h
      exact h
    have hlim : Tendsto (fun T : ℕ => 13 * β ^ T) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul 13
    exact squeeze_zero_norm hb hlim
  -- the first-order conditions
  refine optimal_of_foc hβ0 qU_sup hp (fun t => ?_) (fun t => ?_) zero_le_one hfeas hadm
    (fun t => ?_) htvc
  · refine hint (k := t) (K := 5 / 2 * (5 / 2)) ((hlm t).mul (measurable_endow ν t))
      fun ω => ?_
    rw [abs_mul]
    exact mul_le_mul (hlb t ω) (hyb' t ω) (abs_nonneg _) (by norm_num)
  · have hsm : StronglyMeasurable[S.𝓕 t] (taxes ν β t) := (hmInm t).sub (hmm t)
    refine hint (k := t) (K := 5 / 2 * 10) ((hlm t).mul hsm) fun ω => ?_
    rw [abs_mul]
    refine mul_le_mul (hlb t ω) ?_ (abs_nonneg _) (by norm_num)
    simp only [taxes]
    exact (abs_sub _ _).trans (by linarith [hmIn t ω, hmb t ω])
  · filter_upwards [E_pk_iid ν β t] with ω h
    rw [← hS] at h
    refine ⟨by simp [lam], ?_⟩
    have hl := (hlpos t ω).ne'
    simp only [iota, bondPrice, h, hpk, lam, money, one_mul]
    have h4 : 4 - endow t ω ≠ 0 := by
      have := (endow_bounds t ω).2
      linarith
    have hb := (pow_pos hβ0 t).ne'
    field_simp
    ring

/-- Cochrane (2023), (19.15)–(19.16), p. 441, **derived on the i.i.d. economy**: the necessity
theorems apply to the optimal plan of `IID.iid_optimal` (information growing forever, every history
null for a nondegenerate `ν`): the value of money `u_c/P = 4 − y_t` solves
`v_t = u_m(t)/P_t + βE_tv_{t+1}`, the bond price is
`Q_t = E_t[β u_c(t+1)/u_c(t) · P_t/P_{t+1}]` (19.15) and money demand is
`u_m/u_c = i_t/(1 + i_t)` (19.16), all almost surely. -/
theorem iid_necessity {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (iidSystem ν).Solves β (fun t ω => (4 - money ν β t ω) / 1) (fun t ω => (4 - endow t ω) / 1) ∧
      (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, bondPrice (iidSystem ν) (lam β) (fun _ _ => 1) t ω =
        (iidSystem ν).E t (fun ω => β * ((4 - endow (t + 1) ω) / (4 - endow t ω)) * (1 / 1)) ω) ∧
      ∀ t, ∀ᵐ ω ∂(iidSystem ν).μ, (4 - money ν β t ω) / (4 - endow t ω) =
        (1 / bondPrice (iidSystem ν) (lam β) (fun _ _ => 1) t ω - 1) /
          (1 + (1 / bondPrice (iidSystem ν) (lam β) (fun _ _ => 1) t ω - 1)) := by
  have hopt := iid_optimal (ν := ν) hβ0 hβ1
  have hp := iid_priceRegular (ν := ν) hβ0 hβ1
  have hcb : ∀ n, BddAt (iidSystem ν) (endow n) := fun n => ⟨5 / 2, Eventually.of_forall
    fun ω => by have h1 := endow_bounds n ω; rw [abs_le]; constructor <;> linarith⟩
  have hmb : ∀ n, BddAt (iidSystem ν) (money ν β n) := fun n => ⟨5, Eventually.of_forall
    fun ω => by
      have h1 := endow_bounds n ω
      have h2 := ybar_bounds ν
      simp only [money]
      rw [abs_le]
      constructor <;> nlinarith⟩
  have hne : ∀ t ω, (4 : ℝ) - endow t ω ≠ 0 := fun t ω => by
    have := (endow_bounds t ω).2
    linarith
  have hinv : ∀ t, BddAt (iidSystem ν) fun ω => (4 - endow t ω)⁻¹ := fun t =>
    ⟨2 / 3, Eventually.of_forall fun ω => by
      have h1 := (endow_bounds t ω).2
      have h2 : 0 < 4 - endow t ω := by linarith
      rw [abs_of_pos (inv_pos.2 h2), inv_le_comm₀ h2 (by norm_num)]
      norm_num
      linarith⟩
  exact ⟨value_recursion hβ0 smooth_qU hopt hp hcb hmb,
    fun t => bond_1915_ratio hβ0 smooth_qU hopt hp hcb hmb hne hinv t,
    fun t => (money_demand_1916 hβ0 smooth_qU hopt hp hcb hmb hne t).mono fun _ h => h.1⟩

/-- Cochrane (2023), §19.3, pp. 439–441, **the coin economy**: with fair `±1` coin shocks
(`TidyR6ExpectationsMeasureIID.coin`), every single history has probability zero (the state
space is not a finite event tree), and still consuming the endowment is optimal and
(19.15)–(19.16) and the value-of-money recursion hold. -/
theorem coin_economy {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ ω, (iidSystem coin).μ {ω} = 0) ∧
      MIUOptimal (iidSystem coin) β qU (lam β) (fun _ _ => 1) endow (taxes coin β)
        (fun _ => 0) (fun _ => 0) endow (money coin β) (fun _ _ => 0) ∧
      (iidSystem coin).Solves β (fun t ω => (4 - money coin β t ω) / 1)
        (fun t ω => (4 - endow t ω) / 1) :=
  ⟨iid_singleton coin_mean coin_var one_pos, iid_optimal hβ0 hβ1,
    (iid_necessity hβ0 hβ1).1⟩

end IID

end Cochrane.NewKeynesianSelection.TidyR6MoneyInUtility
