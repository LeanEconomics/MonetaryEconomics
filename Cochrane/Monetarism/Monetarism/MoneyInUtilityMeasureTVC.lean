/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.MoneyInUtilityMeasure
import Monetarism.HouseholdMeasureTVC

/-!
# Money in the utility function: transversality and the value of money

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, §19.3, pp. 439–441, on a
genuine probability space (`MoneyInUtilityMeasure`, `HouseholdMeasureTVC`).

## Main results

* `tvc_necessary`: at an optimal plan of the money-in-utility household (utility concave and
  increasing in consumption, everything bounded at each date, the reference plan
  `(y − s − ιm, m)` admissible, `Λ_0 = u_c(0)`), **the transversality condition holds**:
  `E[Λ_T(a_T + M_{T−1})/P_T] → 0`, equivalently `βᵀE[u_c(T)(a_T + M_{T−1})/P_T] → 0`
  (`tvc_necessary_mu`). With `optimal_iff_foc`, the first-order conditions and the transversality
  condition are necessary and sufficient (`optimal_iff_foc_tvc`).
* `solves_iterate`, `value_of_money_iterated`: the iterated value of money of p. 441,
  `u_c(t)/P_t = ∑_{j<J} βʲE_t[u_m(t+j)/P_{t+j}] + βᴶE_t[u_c(t+J)/P_{t+J}]` almost surely;
  `value_of_money_limit_iff`: the value of a dollar is the present value of its liquidity
  dividends iff `βᴶE_t[u_c(t+J)/P_{t+J}] → 0`, almost surely.
-/

namespace Cochrane.Monetarism.MoneyInUtilityMeasureTVC

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  HouseholdMeasureTVC MoneyInUtilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Necessity of the transversality condition -/

/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions") and
(19.11)–(19.12), **the transversality condition is necessary in the money-in-utility problem, on a
probability space**: at an optimal plan with smooth utility that is concave and increasing in
consumption, regular prices, consumption, real balances, claims, endowment and taxes bounded at
each date (endowment and taxes adapted), the reference plan `(y − s − ιm, m)` admissible, and the
normalisation `Λ_0 = u_c(c_0, M_0/P_0)`, `E[Λ_T(a_T + M_{T−1})/P_T] → 0`. -/
theorem tvc_necessary {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    (hconc : ∀ x z, ConcaveOn ℝ Set.univ (fun e => u (x + e) z))
    (hmono : ∀ x z, Monotone (fun e => u (x + e) z))
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (hab : ∀ n, BddAt S (a n))
    (hyb : ∀ n, BddAt S (y n)) (hsb : ∀ n, BddAt S (s n)) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s)
    (href : UAdmissible S β
      (fun n ω => u (cRef S 0 Λ P y s c m n ω) (mRef S 0 Λ P y s c m n ω)))
    (hnorm : ∀ ω, Λ 0 ω = uc (c 0 ω) (m 0 ω)) :
    Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0) := by
  have e : ∀ x z, (fun e => u (x + e) (z + 0 * e)) = fun e => u (x + e) z := fun x z =>
    funext fun e => by simp
  refine tvc_of_optimal hβ hu (ϑ := 0) (fun x z => by rw [e]; exact hconc x z)
    (fun x z => by rw [e]; exact hmono x z) hopt hp hcb hmb hab hyb hsb hya hsa
    (fun n => Eventually.of_forall fun ω => by simp [wedge_zero])
    (fun n => ⟨1, Eventually.of_forall fun ω => by simp [wedge_zero]⟩) href
    (fun T => ⟨1, one_pos, le_rfl, fun _ _ _ => trivial⟩) (fun T => ?_)
  filter_upwards [foc_normalised hβ hu hopt hp hcb hmb hnorm T] with ω h
  simp only [zero_mul, add_zero, wedge_zero, mul_one]
  exact h.1

/-- Cochrane (2023), p. 439, the transversality condition in marginal-utility form: under the
hypotheses of `tvc_necessary`, `βᵀE[u_c(c_T, M_T/P_T)(a_T + M_{T−1})/P_T] → 0`. -/
theorem tvc_necessary_mu {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    (hconc : ∀ x z, ConcaveOn ℝ Set.univ (fun e => u (x + e) z))
    (hmono : ∀ x z, Monotone (fun e => u (x + e) z))
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (hab : ∀ n, BddAt S (a n))
    (hyb : ∀ n, BddAt S (y n)) (hsb : ∀ n, BddAt S (s n)) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s)
    (href : UAdmissible S β
      (fun n ω => u (cRef S 0 Λ P y s c m n ω) (mRef S 0 Λ P y s c m n ω)))
    (hnorm : ∀ ω, Λ 0 ω = uc (c 0 ω) (m 0 ω)) :
    Tendsto (fun T => β ^ T * ∫ ω, uc (c T ω) (m T ω) *
      ((a T ω + moneyIn N0 P m T ω) / P T ω) ∂S.μ) atTop (𝓝 0) := by
  refine (tvc_necessary hβ hu hconc hmono hopt hp hcb hmb hab hyb hsb hya hsa href
    hnorm).congr fun T => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [foc_normalised hβ hu hopt hp hcb hmb hnorm T] with ω h
  rw [← mul_assoc, h.1]
  simp only [pk]
  ring

/-- Cochrane (2023), eqs. (19.13)–(19.14) and footnote 1, p. 440, and p. 439 ("their optimal
choices include transversality conditions"), **necessary and sufficient conditions including the
transversality condition**: under the hypotheses of `tvc_necessary` (and joint concavity in the
supergradient form), a feasible admissible plan is optimal iff `βᵗu_c = Λ_t`,
`βᵗu_m = Λ_tι_t` almost surely at every date and `E[pk_T(a_T + M_{T−1})] → 0`. -/
theorem optimal_iff_foc_tvc {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ} (hu : Smooth₂ u uc um)
    (hsup : ∀ x y x' y', u x' y' ≤ u x y + uc x y * (x' - x) + um x y * (y' - y))
    (hconc : ∀ x z, ConcaveOn ℝ Set.univ (fun e => u (x + e) z))
    (hmono : ∀ x z, Monotone (fun e => u (x + e) z))
    {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ} (hp : PriceRegular S Λ P)
    (hy : ∀ t, Integrable (fun ω => Λ t ω * y t ω) S.μ)
    (hs : ∀ t, Integrable (fun ω => Λ t ω * s t ω) S.μ)
    (hf : Feasible S Λ P y s N0 a0 c m a)
    (hadm : UAdmissible S β (fun n ω => u (c n ω) (m n ω)))
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (hab : ∀ n, BddAt S (a n))
    (hyb : ∀ n, BddAt S (y n)) (hsb : ∀ n, BddAt S (s n)) (hya : StronglyAdapted S.𝓕 y)
    (hsa : StronglyAdapted S.𝓕 s)
    (href : UAdmissible S β
      (fun n ω => u (cRef S 0 Λ P y s c m n ω) (mRef S 0 Λ P y s c m n ω)))
    (hnorm : ∀ ω, Λ 0 ω = uc (c 0 ω) (m 0 ω)) :
    MIUOptimal S β u Λ P y s N0 a0 c m a ↔ (∀ t, ∀ᵐ ω ∂S.μ,
      β ^ t * uc (c t ω) (m t ω) = Λ t ω ∧
        β ^ t * um (c t ω) (m t ω) = Λ t ω * iota S Λ P t ω) ∧
      Tendsto (wealthPV S Λ P N0 m a) atTop (𝓝 0) := by
  refine ⟨fun hopt => ⟨fun t => foc_normalised hβ hu hopt hp hcb hmb hnorm t,
    tvc_necessary hβ hu hconc hmono hopt hp hcb hmb hab hyb hsb hya hsa href hnorm⟩,
    fun ⟨hfoc, htvc⟩ => ?_⟩
  exact optimal_of_foc hβ hsup hp hy hs zero_le_one hf hadm
    (fun t => (hfoc t).mono fun ω h => ⟨by rw [one_mul]; exact h.1,
      by rw [one_mul]; exact h.2⟩) htvc

/-! ### The iterated value of money -/

/-- Cochrane (2023), p. 441 ("Iterating"): if `v_t = aE_tv_{t+1} + w_t` almost surely with `v`,
`w` integrable and `w` adapted, then almost surely
`v_t = ∑_{j<J} aʲE_tw_{t+j} + aᴶE_tv_{t+J}` for every horizon `J`. -/
theorem solves_iterate {a : ℝ} {w v : ℕ → Ω → ℝ} (hv : ∀ t, Integrable (v t) S.μ)
    (hw : ∀ t, Integrable (w t) S.μ) (hwm : ∀ t, StronglyMeasurable[S.𝓕 t] (w t))
    (hs : S.Solves a w v) (t J : ℕ) :
    ∀ᵐ ω ∂S.μ, v t ω = ∑ j ∈ Finset.range J, a ^ j * S.E t (w (t + j)) ω +
      a ^ J * S.E t (v (t + J)) ω := by
  induction J with
  | zero =>
    have hm : AEStronglyMeasurable[S.𝓕 t] (v t) S.μ :=
      (((S.stronglyMeasurable_E t _).const_smul a).add (hwm t)).aestronglyMeasurable.congr
        (hs t).symm
    filter_upwards [S.E_of_aestronglyMeasurable hm (hv t)] with ω h
    simp [h]
  | succ J ih =>
    have h1 := S.E_congr (hs (t + J)) t
    have h2 := S.E_add ((S.integrable_E (t + J) (v (t + J + 1))).smul a) (hw (t + J)) t
    have h3 := S.E_smul a (S.E (t + J) (v (t + J + 1))) t
    have h4 := S.E_tower (Nat.le_add_right t J) (v (t + J + 1))
    filter_upwards [ih, h1, h2, h3, h4] with ω e0 e1 e2 e3 e4
    rw [e0, e1, e2, Pi.add_apply, e3, Pi.smul_apply, e4, smul_eq_mul,
      Finset.sum_range_succ, show t + (J + 1) = t + J + 1 by ring]
    ring

/-- Cochrane (2023), p. 441 ("Iterating, we can state an asset-pricing view of the value of
money"), on a probability space, **derived from optimality**: at an optimal plan (hypotheses of
`MoneyInUtilityMeasure.value_recursion`), almost surely
`u_c(t)/P_t = ∑_{j<J} βʲE_t[u_m(t+j)/P_{t+j}] + βᴶE_t[u_c(t+J)/P_{t+J}]`. -/
theorem value_of_money_iterated {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ}
    (hu : Smooth₂ u uc um) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (t J : ℕ) :
    ∀ᵐ ω ∂S.μ, uc (c t ω) (m t ω) / P t ω = ∑ j ∈ Finset.range J,
      β ^ j * S.E t (fun ω => um (c (t + j) ω) (m (t + j) ω) / P (t + j) ω) ω +
        β ^ J * S.E t (fun ω => uc (c (t + J) ω) (m (t + J) ω) / P (t + J) ω) ω := by
  have hca := hopt.1.2.1
  have hma := hopt.1.2.2.1
  have hreg : ∀ (v : ℝ → ℝ → ℝ), Continuous (fun p : ℝ × ℝ => v p.1 p.2) → ∀ n,
      StronglyMeasurable[S.𝓕 n] (fun ω => v (c n ω) (m n ω) / P n ω) ∧
        Integrable (fun ω => v (c n ω) (m n ω) / P n ω) S.μ := by
    intro v hv n
    have hm : StronglyMeasurable[S.𝓕 n] (fun ω => v (c n ω) (m n ω) / P n ω) :=
      ((hv.measurable.comp ((hca n).measurable.prodMk (hma n).measurable)).div
        (hp.2.1 n).measurable).stronglyMeasurable
    refine ⟨hm, ((BddAt.comp₂ hv (hcb n) (hmb n)).mul (hp.2.2.2.2 n).2.2.2 |>.congr
      (Eventually.of_forall fun ω => by simp [div_eq_mul_inv])).integrable
        ((hm.mono (S.𝓕.le n)).aestronglyMeasurable)⟩
  exact solves_iterate (fun n => (hreg uc hu.2.1 n).2) (fun n => (hreg um hu.2.2 n).2)
    (fun n => (hreg um hu.2.2 n).1) (value_recursion hβ hu hopt hp hcb hmb) t J

/-- Cochrane (2023), p. 441 ("An additional dollar, held forever, costs `1/P_t`. It generates a
stream of benefits"), on a probability space, derived from optimality: almost surely, the value
of a dollar is the present value of its liquidity dividends,
`u_c(t)/P_t = lim_J ∑_{j<J} βʲE_t[u_m(t+j)/P_{t+j}]`, iff `βᴶE_t[u_c(t+J)/P_{t+J}] → 0`. -/
theorem value_of_money_limit_iff {β : ℝ} (hβ : 0 < β) {u uc um : ℝ → ℝ → ℝ}
    (hu : Smooth₂ u uc um) {Λ P y s : ℕ → Ω → ℝ} {N0 a0 : Ω → ℝ} {c m a : ℕ → Ω → ℝ}
    (hopt : MIUOptimal S β u Λ P y s N0 a0 c m a) (hp : PriceRegular S Λ P)
    (hcb : ∀ n, BddAt S (c n)) (hmb : ∀ n, BddAt S (m n)) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, (Tendsto (fun J => ∑ j ∈ Finset.range J,
        β ^ j * S.E t (fun ω => um (c (t + j) ω) (m (t + j) ω) / P (t + j) ω) ω) atTop
        (𝓝 (uc (c t ω) (m t ω) / P t ω)) ↔
      Tendsto (fun J => β ^ J * S.E t (fun ω => uc (c (t + J) ω) (m (t + J) ω) /
        P (t + J) ω) ω) atTop (𝓝 0)) := by
  filter_upwards [ae_all_iff.2 fun J => value_of_money_iterated hβ hu hopt hp hcb hmb t J]
    with ω h
  have e : ∀ J, ∑ j ∈ Finset.range J,
      β ^ j * S.E t (fun ω => um (c (t + j) ω) (m (t + j) ω) / P (t + j) ω) ω =
      uc (c t ω) (m t ω) / P t ω - β ^ J * S.E t (fun ω => uc (c (t + J) ω) (m (t + J) ω) /
        P (t + J) ω) ω := fun J => by linarith [h J]
  simp_rw [e]
  constructor
  · intro hl
    have := (tendsto_const_nhds (x := uc (c t ω) (m t ω) / P t ω)).sub hl
    simpa using this
  · intro hl
    have := (tendsto_const_nhds (x := uc (c t ω) (m t ω) / P t ω)).sub hl
    simpa using this

end Cochrane.Monetarism.MoneyInUtilityMeasureTVC
