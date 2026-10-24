/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Field

/-!
# Observational equivalence in asset pricing and the finite-state discount-factor theorem

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.2.4, pp. 498–499.

"Marginal utility and probability always enter together in asset pricing formulas,
`p = ∑_s π_s u'(c_s) x_s` … 'Rational' (`u'`) and 'behavioral' (misperceived probabilities `π`)
finance are observationally equivalent", formalised in the Harrison–Kreps martingale-measure and
Hansen–Richard discount-factor existence theorems.

## Main results

* `price π m x = ∑_s π_s m_s x_s`. `rational_behavioral_equiv`: for any full-support beliefs
  `π'`, the marginal utilities `m' = πm/π'` give identical prices for every payoff;
  `same_prices_iff`: two (belief, marginal-utility) pairs give the same prices for all payoffs
  iff `π_s m_s = π'_s m'_s` in every state — only the product is identified;
  `behavioral_pos`: positivity of marginal utility is preserved.
* `riskNeutral`: the risk-neutral (martingale) measure `q = πm/∑πm`, `p = (∑πm) E^q[x]`.
* Finite-state fundamental theorem of asset pricing (one period, finitely many assets
  `X : J → S → ℝ` with prices `p`): `NoArbitrage X p ↔ ∃ m, IsSDF X p m` (`ftap`), the
  discount-factor existence theorem behind "absent arbitrage, there is a discount factor"
  (p. 499). The hard direction is proved with the Hahn–Banach separation theorem
  (`exists_sdf_of_noArbitrage`); the easy one is `noArbitrage_of_sdf`.
  `sdf_expectation_form`: given any full-support probabilities, the price is the expectation
  `p_j = E^π[(m/π) X_j]`.
-/

namespace Cochrane.ObservationalEquivalence.AssetPricingOE

open Finset

variable {S : Type*} [Fintype S]

/-! ### Probabilities and marginal utility enter only as a product -/

/-- Cochrane (2023), p. 498: the asset-pricing formula `p = ∑_s π_s u'(c_s) x_s`, with
probabilities `π`, marginal utilities `m = u'(c)` and payoff `x`. -/
def price (π m x : S → ℝ) : ℝ := ∑ s, π s * m s * x s

/-- Cochrane (2023), p. 498 ("'Rational' and 'behavioral' finance are observationally
equivalent"): for any full-support beliefs `π'`, the marginal utilities `m' = πm/π'` price every
payoff exactly as `(π, m)` does. -/
theorem rational_behavioral_equiv (π m π' : S → ℝ) (hπ' : ∀ s, 0 < π' s) (x : S → ℝ) :
    price π m x = price π' (fun s => π s * m s / π' s) x := by
  unfold price
  refine Finset.sum_congr rfl fun s _ => ?_
  have := (hπ' s).ne'
  field_simp

omit [Fintype S] in
/-- Cochrane (2023), p. 498: if `π, m, π'` are strictly positive, so is `m' = πm/π'`. -/
theorem behavioral_pos {π m π' : S → ℝ} (hπ : ∀ s, 0 < π s) (hm : ∀ s, 0 < m s)
    (hπ' : ∀ s, 0 < π' s) (s : S) : 0 < π s * m s / π' s :=
  div_pos (mul_pos (hπ s) (hm s)) (hπ' s)

/-- Cochrane (2023), p. 498 ("probability and marginal utility always enter together"): two
pairs `(π, m)` and `(π', m')` give the same price to every payoff iff `π_s m_s = π'_s m'_s` in
every state — prices identify only the product. -/
theorem same_prices_iff (π m π' m' : S → ℝ) :
    (∀ x, price π m x = price π' m' x) ↔ ∀ s, π s * m s = π' s * m' s := by
  classical
  constructor
  · intro h s
    have := h (Pi.single s 1)
    simpa [price, Pi.single_apply] using this
  · intro h x
    unfold price
    exact Finset.sum_congr rfl fun s _ => by rw [h s]

/-- Cochrane (2023), pp. 498–499 (Harrison–Kreps martingale measure): with `π, m > 0` (and `S`
nonempty), `q = πm/∑πm` is a full-support probability and `p = (∑ πm) ∑_s q_s x_s`. -/
theorem riskNeutral [Nonempty S] {π m : S → ℝ} (hπ : ∀ s, 0 < π s) (hm : ∀ s, 0 < m s)
    (x : S → ℝ) :
    let Z := ∑ s, π s * m s
    (∀ s, 0 < π s * m s / Z) ∧ ∑ s, π s * m s / Z = 1 ∧
      price π m x = Z * ∑ s, (π s * m s / Z) * x s := by
  intro Z
  have hZ : 0 < Z := Finset.sum_pos (fun s _ => mul_pos (hπ s) (hm s)) Finset.univ_nonempty
  refine ⟨fun s => div_pos (mul_pos (hπ s) (hm s)) hZ, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hZ.ne']
  · unfold price
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by field_simp

/-! ### The finite-state discount-factor theorem -/

variable {J : Type*} [Fintype J]

/-- Cochrane (2023), p. 499: the cost `∑_j θ_j p_j` of a portfolio `θ`. -/
def cost (p : J → ℝ) (θ : J → ℝ) : ℝ := ∑ j, θ j * p j

/-- Cochrane (2023), p. 499: the payoff `∑_j θ_j X_j(s)` of a portfolio `θ` in state `s`. -/
def payoff (X : J → S → ℝ) (θ : J → ℝ) (s : S) : ℝ := ∑ j, θ j * X j s

/-- Cochrane (2023), p. 499: an arbitrage — a portfolio with nonnegative payoff in every state
and nonpositive cost that either costs strictly less than zero or pays strictly positive in
some state. -/
def IsArbitrage (X : J → S → ℝ) (p : J → ℝ) (θ : J → ℝ) : Prop :=
  (∀ s, 0 ≤ payoff X θ s) ∧ cost p θ ≤ 0 ∧ (cost p θ < 0 ∨ ∃ s, 0 < payoff X θ s)

/-- Cochrane (2023), p. 499 ("absent arbitrage"): no portfolio is an arbitrage. -/
def NoArbitrage (X : J → S → ℝ) (p : J → ℝ) : Prop := ∀ θ, ¬ IsArbitrage X p θ

/-- Cochrane (2023), p. 499: a strictly positive (state-price) discount factor `m` that prices
every asset, `p_j = ∑_s m_s X_j(s)`. -/
def IsSDF (X : J → S → ℝ) (p : J → ℝ) (m : S → ℝ) : Prop :=
  (∀ s, 0 < m s) ∧ ∀ j, p j = ∑ s, m s * X j s

/-- Cochrane (2023), p. 499: with a discount factor, the cost of any portfolio is the
discounted value of its payoff. -/
theorem cost_eq_of_sdf {X : J → S → ℝ} {p : J → ℝ} {m : S → ℝ} (hm : IsSDF X p m)
    (θ : J → ℝ) : cost p θ = ∑ s, m s * payoff X θ s := by
  simp only [cost, payoff, hm.2, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

/-- Cochrane (2023), p. 499 (easy direction of the discount-factor theorem): a strictly
positive discount factor rules out arbitrage. -/
theorem noArbitrage_of_sdf {X : J → S → ℝ} {p : J → ℝ} {m : S → ℝ} (hm : IsSDF X p m) :
    NoArbitrage X p := by
  rintro θ ⟨hpay, hcost, hstrict⟩
  have hc := cost_eq_of_sdf hm θ
  have hnn : ∀ s ∈ (Finset.univ : Finset S), 0 ≤ m s * payoff X θ s :=
    fun s _ => mul_nonneg (hm.1 s).le (hpay s)
  have h0 : 0 ≤ cost p θ := hc ▸ Finset.sum_nonneg hnn
  have hz : cost p θ = 0 := le_antisymm hcost h0
  rcases hstrict with hlt | ⟨s, hs⟩
  · linarith
  · have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (hc ▸ hz)
    have := hall s (Finset.mem_univ s)
    rcases mul_eq_zero.mp this with h | h
    · exact (hm.1 s).ne' h
    · exact hs.ne' h

/-- Cochrane (2023), p. 499 (tool): the gains map `θ ↦ (−cost θ, payoff θ)` into
`ℝ^{1+S}`, the `none` coordinate holding minus the cost. -/
def gains (X : J → S → ℝ) (p : J → ℝ) : (J → ℝ) →ₗ[ℝ] (Option S → ℝ) where
  toFun θ := fun o => Option.elim o (-cost p θ) (payoff X θ)
  map_add' θ θ' := by
    funext o
    cases o <;> simp [cost, payoff, add_mul, Finset.sum_add_distrib]; ring
  map_smul' c θ := by
    funext o
    cases o <;> simp [cost, payoff, Finset.mul_sum, mul_assoc]

/-- Cochrane (2023), p. 499 (tool): the simplex of `ℝ^{1+S}`, nonnegative vectors summing to
one. -/
def simplexSet (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {f | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}

/-- Cochrane (2023), p. 499 (tool): the simplex is convex. -/
theorem convex_simplexSet (ι : Type*) [Fintype ι] : Convex ℝ (simplexSet ι) := by
  rintro f ⟨hf0, hf1⟩ g ⟨hg0, hg1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hf0 i)) (mul_nonneg hb (hg0 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hf1, hg1, mul_one, hab]

/-- Cochrane (2023), p. 499 (tool): a linear functional on `ℝ^ι` is determined by its values on
the unit vectors. -/
theorem functional_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) →ₗ[ℝ] ℝ)
    (z : ι → ℝ) : f z = ∑ i, z i * f (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Pi.single i (z i) = z i • Pi.single (M := fun _ => ℝ) i 1 := by
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [this, map_smul, smul_eq_mul]

/-- Cochrane (2023), p. 499 (the discount-factor existence theorem, Harrison–Kreps /
Hansen–Richard, finite states): absent arbitrage there is a strictly positive discount factor
pricing every asset. Proof by strict separation (Hahn–Banach) of the simplex of `ℝ^{1+S}` from
the subspace of attainable (−cost, payoff) vectors. -/
theorem exists_sdf_of_noArbitrage {X : J → S → ℝ} {p : J → ℝ}
    (hna : NoArbitrage X p) : ∃ m, IsSDF X p m := by
  classical
  set L : Submodule ℝ (Option S → ℝ) := LinearMap.range (gains X p) with hL
  set K : Set (Option S → ℝ) :=
    convexHull ℝ (Set.range fun o : Option S => Pi.single (M := fun _ => ℝ) o 1) with hK
  have hKsub : K ⊆ simplexSet (Option S) := by
    refine convexHull_min ?_ (convex_simplexSet _)
    rintro _ ⟨o, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h : i = o
      · subst h; simp
      · simp [h]
    · simp
  have hKc : IsCompact K := by
    rw [hK]; exact (Set.finite_range _).isCompact_convexHull ℝ
  have hdisj : Disjoint K (L : Set (Option S → ℝ)) := by
    rw [Set.disjoint_left]
    intro y hyK hyL
    obtain ⟨θ, rfl⟩ := hyL
    obtain ⟨hnn, hsum⟩ := hKsub hyK
    have hcost : cost p θ ≤ 0 := by
      have := hnn none; simp [gains] at this; linarith
    have hpay : ∀ s, 0 ≤ payoff X θ s := fun s => by simpa [gains] using hnn (some s)
    refine hna θ ⟨hpay, hcost, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hc0, hp0⟩ := hcon
    have hzero : ∀ o, gains X p θ o = 0 := by
      intro o
      cases o with
      | none => simp [gains]; linarith
      | some s => simp only [gains, LinearMap.coe_mk, AddHom.coe_mk, Option.elim_some]
                  exact le_antisymm (hp0 s) (hpay s)
    simp [hzero] at hsum
  obtain ⟨f, u, v, hfK, huv, hfL⟩ :=
    geometric_hahn_banach_compact_closed (convex_convexHull ℝ _) hKc L.convex
      L.closed_of_finiteDimensional hdisj
  have hfL0 : ∀ b ∈ (L : Set (Option S → ℝ)), f b = 0 := by
    intro b hb
    by_contra hne
    have hcb : ((v - 1) / f b) • b ∈ (L : Set (Option S → ℝ)) := L.smul_mem _ hb
    have := hfL _ hcb
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  have hv : v < 0 := by
    have := hfL 0 L.zero_mem
    simpa using this
  have hneg : ∀ o, f (Pi.single o 1) < 0 := fun o =>
    (hfK _ (subset_convexHull ℝ _ ⟨o, rfl⟩)).trans (huv.trans hv)
  refine ⟨fun s => f (Pi.single (some s) 1) / f (Pi.single none 1), fun s => ?_, fun j => ?_⟩
  · exact div_pos_of_neg_of_neg (hneg (some s)) (hneg none)
  · have h0 := hfL0 (gains X p (Pi.single j 1)) ⟨Pi.single j 1, rfl⟩
    have hrep := functional_eq_sum (f : (Option S → ℝ) →ₗ[ℝ] ℝ) (gains X p (Pi.single j 1))
    simp only [ContinuousLinearMap.coe_coe] at hrep
    rw [hrep, Fintype.sum_option] at h0
    have hc : cost p (Pi.single j 1) = p j := by simp [cost, Pi.single_apply]
    have hpj : ∀ s, payoff X (Pi.single j 1) s = X j s := by
      intro s; simp [payoff, Pi.single_apply]
    simp only [gains, LinearMap.coe_mk, AddHom.coe_mk, Option.elim_none, Option.elim_some,
      hc, hpj] at h0
    have hn := (hneg none).ne
    rw [Finset.sum_congr rfl fun s _ => (div_mul_eq_mul_div _ _ _).trans
      (by ring : f (Pi.single (some s) 1) * X j s / f (Pi.single none 1) =
        X j s * f (Pi.single (some s) 1) / f (Pi.single none 1)), ← Finset.sum_div]
    field_simp
    linarith

/-- Cochrane (2023), pp. 498–499 (finite-state fundamental theorem of asset pricing): there is
no arbitrage iff there is a strictly positive discount factor pricing every asset. -/
theorem ftap (X : J → S → ℝ) (p : J → ℝ) :
    NoArbitrage X p ↔ ∃ m, IsSDF X p m :=
  ⟨exists_sdf_of_noArbitrage, fun ⟨_, hm⟩ => noArbitrage_of_sdf hm⟩

omit [Fintype J] in
/-- Cochrane (2023), pp. 498–499: a discount factor in expectation form — for any full-support
probabilities `π`, `p_j = ∑_s π_s (m_s/π_s) X_j(s) = price π (m/π) X_j`, so the same prices are
"explained" by every belief `π` with a suitable positive marginal utility `m/π`. -/
theorem sdf_expectation_form {X : J → S → ℝ} {p : J → ℝ} {m : S → ℝ} (hm : IsSDF X p m)
    {π : S → ℝ} (hπ : ∀ s, 0 < π s) (j : J) :
    p j = price π (fun s => m s / π s) (X j) ∧ ∀ s, 0 < m s / π s := by
  refine ⟨?_, fun s => div_pos (hm.1 s) (hπ s)⟩
  rw [hm.2 j]
  unfold price
  refine Finset.sum_congr rfl fun s _ => ?_
  have := (hπ s).ne'
  field_simp

end Cochrane.ObservationalEquivalence.AssetPricingOE
