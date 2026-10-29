/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6HouseholdBondTVC
import NewKeynesianSelection.LowerBound

/-!
# The household problem behind (16.25)

Cochrane (2023), Chapter 16, §16.8, p. 377: "The setup is the same as the complete frictionless
model of Section 2. The interest rate and inflation conform to the nonlinear Fisher relation
(16.25) `1/(1 + i_t) = βE_t(P_t/P_{t+1}) = (1 + r)⁻¹E_t(1/Π_{t+1})`", and p. 378, "the
consumer's first-order condition (16.25)".

Here (16.25) is derived from the household's optimisation problem of Section 2 (the endowment
economy with one-period nominal bonds, restated in TidyR6HouseholdBond and
TidyR6HouseholdBondTVC) on a genuine probability space, whose information may grow forever:
the household maximises `E ∑ βᵗu(c_t)` subject to `B_{t−1} + P_ty = P_tc_t + P_ts_t + Q_tB_t`,
`B_t ≥ 0`, and in equilibrium `c_t = y`. With `β = 1/(1 + r)`, `Q_t = 1/(1 + i_t)` and
`Π_{t+1} = P_{t+1}/P_t`:

* `bondPricingM_iff`: (16.25) in measure form (`BondPricingM`) is `Q_t = βE_t(P_t/P_{t+1})`.
* `bondPricing_of_optimal` (**necessity**): if consuming the endowment is optimal and the
  household holds bonds (`B_t > 0`), (16.25) holds almost surely.
* `optimal_of_bondPricing` (**sufficiency**): if prices satisfy (16.25) at every date and the
  transversality condition `βᴺE[B_{N−1}/P_N] → 0` holds, consuming the endowment is optimal
  (concave increasing utility, `r > 0`).
* `optimal_iff_bondPricing`: the two together.
* Finite trees: `Tree.tree_bondPricing_of_optimal` gives `LowerBound.BondPricing` for the tree's
  core
  `ExpectationSystem` exactly, in every state; `Tree.unitTree`, `Tree.unitTree_E`,
  `Tree.pf_of_optimal`: on the one-state tree (perfect foresight) optimisation gives (16.28)
  `Π_{t+1} = β(1 + i_t)`.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6Household16_25

open MeasureTheory ProbabilityTheory Filter Topology TidyR6ExpectationsMeasure
open TidyR6HouseholdBond TidyR6HouseholdBondTVC

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-- Cochrane (2023), eq. (16.27), p. 378: gross inflation `Π_{t+1} = P_{t+1}/P_t` (with the
irrelevant value `1` at date `0`). -/
noncomputable def grossInfl (P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun ω => P (t + 1) ω / P t ω

/-- Cochrane (2023), p. 21 and eq. (16.25), p. 377: the nominal rate implied by the bond price,
`i_t = 1/Q_t − 1`. -/
noncomputable def rateOf (Q : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := (Q t ω)⁻¹ - 1

variable (S) in
/-- Cochrane (2023), eq. (16.25), p. 377, on a probability space: almost surely
`1/(1 + i_t) = (1 + r)⁻¹E_t(1/Π_{t+1})`. -/
def BondPricingM (r : ℝ) (i infl : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  (fun ω => 1 / (1 + i t ω)) =ᵐ[S.μ] (1 + r)⁻¹ • S.E t (fun ω => 1 / infl (t + 1) ω)

/-- Cochrane (2023), eq. (16.25), p. 377: with `i_t = 1/Q_t − 1` and `Π_{t+1} = P_{t+1}/P_t`,
(16.25) is `Q_t = (1 + r)⁻¹E_t(P_t/P_{t+1})`. -/
theorem bondPricingM_iff (r : ℝ) (Q P : ℕ → Ω → ℝ) (t : ℕ) :
    BondPricingM S r (rateOf Q) (grossInfl P) t ↔
      Q t =ᵐ[S.μ] (1 + r)⁻¹ • S.E t (fun ω => P t ω / P (t + 1) ω) := by
  have e1 : (fun ω => 1 / (1 + rateOf Q t ω)) = Q t := by
    funext ω
    simp only [rateOf, add_sub_cancel, one_div, inv_inv]
  have e2 : (fun ω => 1 / grossInfl P (t + 1) ω) = fun ω => P t ω / P (t + 1) ω := by
    funext ω
    simp only [grossInfl, one_div_div]
  rw [BondPricingM, e1, e2]

/-- Cochrane (2023), eq. (16.25), p. 377, **necessity**: if consuming the endowment `c = y` is
optimal for a household with differentiable utility (`u′` continuous and positive), at prices
that are adapted and positive with `TidyR6HouseholdBond.EulerRegular` regularity, and the household
holds bonds
`B_t > 0` almost surely, then (16.25) holds almost surely at date `t`, with `β = 1/(1 + r)`. -/
theorem bondPricing_of_optimal {r y : ℝ} (hr : 0 < 1 + r) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hu'pos : ∀ x, 0 < u' x)
    {P s Q b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ}
    (hopt : Optimal S (1 + r)⁻¹ y u P s Q b₀ (fun _ _ => y) b) (hPad : StronglyAdapted S.𝓕 P)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) {t : ℕ} (hQt : StronglyMeasurable[S.𝓕 t] (Q t))
    (hreg : EulerRegular S P Q (fun _ _ => y) t)
    (hint : Integrable (fun ω => P t ω / P (t + 1) ω) S.μ)
    (hb : ∀ᵐ ω ∂S.μ, 0 < b (t + 1) ω) : BondPricingM S r (rateOf Q) (grossInfl P) t := by
  have hy : u' y / u' y = 1 := div_self (hu'pos y).ne'
  have hW : Integrable (fun ω => u' ((fun _ _ => y : ℕ → Ω → ℝ) (t + 1) ω) /
      u' ((fun _ _ => y : ℕ → Ω → ℝ) t ω) * (P t ω / P (t + 1) ω)) S.μ := by
    simpa only [hy, one_mul] using hint
  have h := bondPrice_formula (inv_pos.mpr hr) hu hu' hu'pos hopt hPad hP hQt hreg hW
  simp only [hy, one_mul] at h
  rw [bondPricingM_iff]
  filter_upwards [h, hb] with ω h1 h2
  rw [(h1 h2).1]
  rfl

/-- Cochrane (2023), eq. (16.25), p. 377, **sufficiency**: let `r > 0`, `u` concave, increasing
and differentiable, and let the endowment plan `c = y` with bonds `B` be feasible. If prices are
adapted, positive, with `1/P_t` essentially bounded, `P_t/P_{t+1}` and real debt `B_{t−1}/P_t`
integrable, (16.25) holds at every date and the transversality condition
`βᴺE[B_{N−1}/P_N] → 0` holds, then consuming the endowment is optimal. -/
theorem optimal_of_bondPricing {r y : ℝ} (hr : 0 < r) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    {P s Q b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ} (hfeas : Feasible S y P s Q b₀ (fun _ _ => y) b)
    (hPad : StronglyAdapted S.𝓕 P) (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω)
    (hPinv : ∀ n, BddAt S (fun ω => (P n ω)⁻¹))
    (hPP : ∀ n, Integrable (fun ω => P n ω / P (n + 1) ω) S.μ)
    (hbP : ∀ n, Integrable (fun ω => b n ω / P n ω) S.μ)
    (hbp : ∀ n, BondPricingM S r (rateOf Q) (grossInfl P) n)
    (htvc : Tendsto (fun N => ((1 + r)⁻¹) ^ N * ∫ ω, b N ω / P N ω ∂S.μ) atTop (𝓝 0)) :
    Optimal S (1 + r)⁻¹ y u P s Q b₀ (fun _ _ => y) b := by
  have hr1 : 0 < 1 + r := by linarith
  have hβ : 0 < (1 + r)⁻¹ := inv_pos.mpr hr1
  have hβ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have huc : Continuous u := continuous_iff_continuousAt.2 fun x => (hu x).continuousAt
  have hadm : Admissible S (1 + r)⁻¹ u (fun _ _ => y) :=
    admissible_of_bdd hβ.le hβ1 huc (fun _ => aestronglyMeasurable_const) (M := |y|)
      fun _ => Eventually.of_forall fun _ => le_rfl
  have hPm : ∀ n, AEStronglyMeasurable (fun ω => u' y / P n ω) S.μ := fun n =>
    (((hPad n).measurable.const_div (u' y)).stronglyMeasurable.mono (S.𝓕.le n)).aestronglyMeasurable
  have hbdd : ∀ n, BddAt S (fun ω => u' y / P n ω) := fun n => by
    have := (BddAt.const (S := S) (u' y)).mul (hPinv n)
    simpa [div_eq_mul_inv] using this
  refine optimal_of_euler_tvc hβ hu hconc hmono hfeas hadm hP (fun n => (hbdd n).integrable (hPm n))
    (fun n => ((hbP n).const_mul (u' y)).congr (Eventually.of_forall fun ω => by
      simp only; ring)) (fun n => ?_) ?_
  · -- the Euler equation from (16.25), by pulling `u'(y)/P_n` into `E_n`
    have h1 := (bondPricingM_iff r Q P n).mp (hbp n)
    obtain ⟨C, hC⟩ := hbdd n
    have hfm : StronglyMeasurable[S.𝓕 n] (fun ω => u' y / P n ω) :=
      ((hPad n).measurable.const_div (u' y)).stronglyMeasurable
    have hpo := S.E_pullOut hfm hC (hPP n)
    have hcong : ((fun ω => u' y / P n ω) * fun ω => P n ω / P (n + 1) ω) =ᵐ[S.μ]
        fun ω => u' y / P (n + 1) ω := by
      filter_upwards [hP n] with ω hω
      simp only [Pi.mul_apply]
      field_simp
    have hE := S.E_congr hcong n
    filter_upwards [h1, hpo, hE] with ω e1 e2 e3
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] at e1 e2
    rw [← e3, e2, e1]
    ring
  · have e : (fun N => ((1 + r)⁻¹) ^ N * ∫ ω, u' ((fun _ _ => y : ℕ → Ω → ℝ) N ω) * b N ω /
        P N ω ∂S.μ) = fun N => u' y * (((1 + r)⁻¹) ^ N * ∫ ω, b N ω / P N ω ∂S.μ) := by
      funext N
      have : (fun ω => u' y * b N ω / P N ω) = fun ω => u' y * (b N ω / P N ω) := by
        funext ω; ring
      simp only [this, integral_const_mul]
      ring
    rw [e]
    simpa using htvc.const_mul (u' y)

/-- Cochrane (2023), eq. (16.25), p. 377 and p. 378 ("the consumer's first-order condition
(16.25)"): under the hypotheses of both directions (`r > 0`; `u` concave, increasing,
differentiable with continuous positive `u′`; the endowment plan feasible with `B_t > 0`;
regular prices; the transversality condition), consuming the endowment is optimal iff (16.25)
holds at every date. -/
theorem optimal_iff_bondPricing {r y : ℝ} (hr : 0 < r) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hu'pos : ∀ x, 0 < u' x)
    (hconc : ConcaveOn ℝ Set.univ u) (hmono : Monotone u)
    {P s Q b : ℕ → Ω → ℝ} {b₀ : Ω → ℝ} (hfeas : Feasible S y P s Q b₀ (fun _ _ => y) b)
    (hPad : StronglyAdapted S.𝓕 P) (hQad : StronglyAdapted S.𝓕 Q)
    (hP : ∀ n, ∀ᵐ ω ∂S.μ, 0 < P n ω) (hPinv : ∀ n, BddAt S (fun ω => (P n ω)⁻¹))
    (hreg : ∀ n, EulerRegular S P Q (fun _ _ => y) n)
    (hPP : ∀ n, Integrable (fun ω => P n ω / P (n + 1) ω) S.μ)
    (hbP : ∀ n, Integrable (fun ω => b n ω / P n ω) S.μ) (hb : ∀ n, ∀ᵐ ω ∂S.μ, 0 < b (n + 1) ω)
    (htvc : Tendsto (fun N => ((1 + r)⁻¹) ^ N * ∫ ω, b N ω / P N ω ∂S.μ) atTop (𝓝 0)) :
    Optimal S (1 + r)⁻¹ y u P s Q b₀ (fun _ _ => y) b ↔
      ∀ n, BondPricingM S r (rateOf Q) (grossInfl P) n :=
  ⟨fun hopt n => bondPricing_of_optimal (by linarith) hu hu' hu'pos hopt hPad hP (hQad n)
      (hreg n) (hPP n) (hb n),
    fun hbp => optimal_of_bondPricing hr hu hconc hmono hfeas hPad hP hPinv hPP hbP hbp htvc⟩

/-! ## Finite event trees and perfect foresight -/

namespace Tree

open ExpectationsFiniteTree TreeBridge Link

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), eq. (16.25), p. 377, on a finite event tree: if consuming the endowment is
optimal (the household problem posed on the tree as a probability space), the bond price is
adapted and the household holds bonds in every state, then (16.25) holds **exactly in every
state** for the tree's core expectation system: `LowerBound.BondPricing`. -/
theorem tree_bondPricing_of_optimal {r y : ℝ} (hr : 0 < 1 + r) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hu'pos : ∀ x, 0 < u' x)
    {P s Q b : ℕ → Ω' → ℝ} {b₀ : Ω' → ℝ}
    (hopt : Optimal (treeSystem T) (1 + r)⁻¹ y u P s Q b₀ (fun _ _ => y) b)
    (hPad : StronglyAdapted (treeSystem T).𝓕 P) (hQad : StronglyAdapted (treeSystem T).𝓕 Q)
    (hP : ∀ n ω, 0 < P n ω) (hb : ∀ n ω, 0 < b (n + 1) ω) :
    LowerBound.BondPricing T.toExpectationSystem r (rateOf Q) (grossInfl P) := by
  intro t
  have h := bondPricing_of_optimal hr hu hu' hu'pos hopt hPad
    (fun n => Eventually.of_forall (hP n)) (hQad t) (eulerRegular_tree T _ _ _ t)
    Integrable.of_finite (Eventually.of_forall (hb t))
  funext ω
  have := forall_of_ae T h ω
  rw [treeE] at this
  exact this

/-- Cochrane (2023), eq. (16.28), p. 378: the one-state tree (perfect foresight). -/
def unitTree : FiniteTree Unit where
  prob := fun _ => 1
  prob_pos := fun _ => one_pos
  prob_sum := by simp
  info := fun _ => ⊤
  refines := fun _ _ _ _ => trivial

/-- Cochrane (2023), eq. (16.28), p. 378: on the one-state tree `E_t` is the identity. -/
theorem unitTree_E (t : ℕ) (x : Unit → ℝ) : unitTree.toExpectationSystem.E t x = x := by
  funext ω
  rw [FiniteTree.toExpectationSystem_E]
  exact unitTree.condE_of_const_on_cell fun ω' _ => by rw [Subsingleton.elim ω' ω]

/-- Cochrane (2023), eqs. (16.25) and (16.28), p. 378, "With perfect foresight, the consumer's
first-order condition (16.25) reduces to `Π_{t+1} = β(1 + i_t)`", derived from optimisation: on
the one-state tree, if consuming the endowment is optimal, prices and the bond price are positive
and the household holds bonds, then `Π_{t+1} = (1 + r)⁻¹(1 + i_t)` at every date. -/
theorem pf_of_optimal {r y : ℝ} (hr : 0 < 1 + r) {u u' : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : Continuous u') (hu'pos : ∀ x, 0 < u' x)
    {P s Q b : ℕ → Unit → ℝ} {b₀ : Unit → ℝ}
    (hopt : Optimal (treeSystem unitTree) (1 + r)⁻¹ y u P s Q b₀ (fun _ _ => y) b)
    (hPad : StronglyAdapted (treeSystem unitTree).𝓕 P)
    (hQad : StronglyAdapted (treeSystem unitTree).𝓕 Q) (hP : ∀ n ω, 0 < P n ω)
    (hQ : ∀ n ω, 0 < Q n ω) (hb : ∀ n ω, 0 < b (n + 1) ω) (t : ℕ) :
    grossInfl P (t + 1) () = (1 + r)⁻¹ * (1 + rateOf Q t ()) := by
  have h := congrFun (tree_bondPricing_of_optimal unitTree hr hu hu' hu'pos hopt hPad hQad hP hb
    t) ()
  rw [unitTree_E] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have h1 : 0 < 1 + rateOf Q t () := by simp only [rateOf]; linarith [inv_pos.mpr (hQ t ())]
  have h2 : 0 < grossInfl P (t + 1) () := div_pos (hP _ _) (hP _ _)
  field_simp at h
  rw [eq_inv_mul_iff_mul_eq₀ hr.ne']
  linarith

end Tree

end Cochrane.NewKeynesianSelection.TidyR6Household16_25
