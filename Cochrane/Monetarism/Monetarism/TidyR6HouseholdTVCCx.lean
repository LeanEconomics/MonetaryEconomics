/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Monetarism.TidyR6HouseholdSuff
import Monetarism.HouseholdMeasureTVC
import Monetarism.CashInAdvanceMeasure

/-!
# Two hypotheses of the transversality theorem cannot be dropped

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 19, p. 439 ("their optimal
choices include transversality conditions") and (19.28), p. 449, for the necessity theorem
`HouseholdMeasureTVC.tvc_of_optimal`. Two counterexamples, each on an arbitrary probability space
(the economies are deterministic), satisfy every hypothesis of that theorem but one, and the
transversality condition `E[pk_T(a_T + M_{T−1})] → 0` fails at an optimum.

* `tvc_needs_reference`: **the admissible reference plan is needed.** With linear utility
  `u(c, m) = c`, `Λ_t = βᵗ`, `P_t = 1` and the endowment `y_t = (−1)ᵗ/βᵗ` (whose present value
  oscillates), consuming nothing is optimal (`TidyR6HouseholdSuff.optimal_of_supergradient_liminf`)
  while the date-0 value of wealth alternates between `0` and `1`. Every hypothesis of
  `tvc_of_optimal` holds — including all the per-date bounds, concavity and monotonicity, and the
  normalised first-order condition — except that the reference plan (consume `y − s`) is not
  admissible. The liminf form (`TidyR6HouseholdFOC.miu_liminf_tvc`) does hold.
* `tvc_needs_nonsatiation`: **nonsatiation (`λ > 0`) is needed.** With constant utility every
  feasible plan is optimal, including one that keeps a unit of wealth for ever. Every hypothesis
  of `tvc_of_optimal` holds except the normalised first-order condition; the first-order
  condition holds with multiplier `λ = 0`. `cia_needs_nonsatiation`: a cash-in-advance version
  satisfies every hypothesis of `CashInAdvanceMeasureTVC.tvc_necessary` except `u' > 0` and the
  normalisation `Λ_0w_0 = u'(c_0)` (which nonsatiation makes possible), and the transversality
  condition fails.
-/

namespace Cochrane.Monetarism.TidyR6HouseholdTVCCx

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure HouseholdMeasure
  HouseholdMeasureTVC TidyR6HouseholdRoll TidyR6HouseholdSuff

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Deterministic helpers -/

/-- Cochrane (2023), Ch. 2, p. 29: the conditional expectation of a constant is the constant
(stated for a function that ignores the state). -/
theorem E_fun_const (t : ℕ) (f : Ω → ℝ) (k : ℝ) (hf : f = fun _ => k) (ω : Ω) :
    S.E t f ω = k := by
  rw [hf, S.E_const]

/-- Cochrane (2023), Ch. 2, p. 29: on a probability space the integral of a function that
ignores the state is that constant. -/
theorem integral_fun_const (f : Ω → ℝ) (k : ℝ) (hf : ∀ ω, f ω = k) : ∫ ω, f ω ∂S.μ = k := by
  rw [integral_congr_ae (Eventually.of_forall hf), integral_const, probReal_univ, one_smul]

/-- Cochrane (2023), Ch. 2, p. 29: a function that ignores the state is integrable on a
probability space. -/
theorem integrable_fun_const (f : Ω → ℝ) (k : ℝ) (hf : ∀ ω, f ω = k) : Integrable f S.μ :=
  (integrable_const k).congr (Eventually.of_forall fun ω => (hf ω).symm)

/-- Cochrane (2023), (19.9), p. 439: a function that ignores the state is essentially
bounded. -/
theorem bddAt_fun_const (f : Ω → ℝ) (k : ℝ) (hf : ∀ ω, f ω = k) : BddAt S f :=
  ⟨|k|, Eventually.of_forall fun ω => by rw [hf]⟩

/-- Cochrane (2023), p. 439: a sequence that is not summable because its terms do not go to
zero: `∑ 1` diverges. -/
theorem not_summable_one : ¬ Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  have := h.tendsto_atTop_zero
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique h1 this)

/-! ### The reference plan is needed -/

namespace RefCx

/-- Cochrane (2023), p. 439 (counterexample): the parity indicator `e_t = 1` for odd `t`. -/
def par (t : ℕ) : ℝ := if t % 2 = 1 then 1 else 0

/-- Cochrane (2023), p. 439 (counterexample): `e_t + (−1)ᵗ = e_{t+1}`. -/
theorem par_succ (t : ℕ) : par t + (-1) ^ t = par (t + 1) := by
  rcases Nat.even_or_odd t with h | h
  · have h1 : t % 2 = 0 := Nat.even_iff.1 h
    have h2 : (t + 1) % 2 = 1 := by omega
    simp [par, h1, h2, h.neg_one_pow]
  · have h1 : t % 2 = 1 := Nat.odd_iff.1 h
    have h2 : (t + 1) % 2 = 0 := by omega
    simp [par, h1, h2, h.neg_one_pow]

/-- Cochrane (2023), p. 439 (counterexample): state prices `Λ_t = βᵗ`. -/
noncomputable def lam (β : ℝ) (t : ℕ) (_ : Ω) : ℝ := β ^ t

/-- Cochrane (2023), p. 439 (counterexample): a constant price level `P_t = 1`. -/
def pr (_ : ℕ) (_ : Ω) : ℝ := 1

/-- Cochrane (2023), p. 439 (counterexample): the endowment `y_t = (−1)ᵗ/βᵗ`, whose present value
`∑ βᵗy_t = 1 − 1 + 1 − ⋯` oscillates. -/
noncomputable def endow (β : ℝ) (t : ℕ) (_ : Ω) : ℝ := (-1) ^ t / β ^ t

/-- Cochrane (2023), p. 439 (counterexample): the claims `a_t = e_t/βᵗ`. -/
noncomputable def claims (β : ℝ) (t : ℕ) (_ : Ω) : ℝ := par t / β ^ t

/-- Cochrane (2023), p. 439 (counterexample): the zero process. -/
def zp (_ : ℕ) (_ : Ω) : ℝ := 0

/-- Cochrane (2023), p. 439 (counterexample): the constraint `m_t ≥ 0` (no money issue). -/
def NonnegMoney (S : MeasExpectationSystem Ω) (_ m : ℕ → Ω → ℝ) : Prop :=
  ∀ t, ∀ᵐ ω ∂S.μ, 0 ≤ m t ω

/-- Cochrane (2023), p. 439: the counterexample prices are regular. -/
theorem priceRegular_cx {β : ℝ} (hβ0 : 0 < β) : PriceRegular S (lam (Ω := Ω) β) pr :=
  ⟨fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    fun t _ => pow_pos hβ0 t, fun _ _ => one_pos, fun t => ⟨bddAt_fun_const _ (β ^ t)
      fun _ => rfl, bddAt_fun_const _ (β ^ t)⁻¹ fun _ => rfl, bddAt_fun_const _ 1 fun _ => rfl,
      bddAt_fun_const _ 1⁻¹ fun _ => rfl⟩⟩

/-- Cochrane (2023), (19.15), p. 441: in the counterexample economy `Q_t = β`. -/
theorem bondPrice_cx {β : ℝ} (hβ0 : 0 < β) (t : ℕ) (ω : Ω) :
    bondPrice S (lam β) pr t ω = β := by
  simp only [bondPrice]
  rw [E_fun_const t (pk (lam β) pr (t + 1)) (β ^ (t + 1) / 1) rfl]
  simp only [pk, lam, pr]
  have := pow_pos hβ0 t
  field_simp
  ring

/-- Cochrane (2023), (19.10), p. 439: consuming nothing, holding no money and the claims
`a_t = e_t/βᵗ` is feasible from zero initial wealth. -/
theorem feasible_cx {β : ℝ} (hβ0 : 0 < β) :
    Feasible S (lam β) pr (endow β) zp 0 0 zp zp (claims β) := by
  refine ⟨by funext ω; simp [claims, par], fun _ => stronglyMeasurable_const,
    fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    fun t => Eventually.of_forall fun ω => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_, fun δ hδ => Eventually.of_forall fun T => ?_⟩
  · simp only [claimCost]
    rw [E_fun_const t (fun ω => pk (lam β) pr (t + 1) ω * claims β (t + 1) ω) (par (t + 1)) (by
      funext ω
      simp only [pk, lam, pr, claims]
      have := pow_pos hβ0 (t + 1)
      field_simp)]
    have hb := pow_pos hβ0 t
    have hm : moneyIn 0 pr zp t ω = 0 := by
      cases t with
      | zero => rfl
      | succ k => simp [moneyIn, zp]
    simp only [hm, claims, endow, pk, lam, pr, zp]
    rw [← par_succ t]
    field_simp
    ring
  · exact integrable_fun_const _ (par t) fun ω => by
      have := pow_pos hβ0 t
      simp only [pk, lam, pr, claims]
      field_simp
  · refine (integrable_zero Ω ℝ S.μ).congr (Eventually.of_forall fun ω => ?_)
    cases t with
    | zero => simp [moneyIn]
    | succ k => simp [moneyIn, zp]
  · simp [zp]
  · simp [zp]
  · have hW : wealthPV S (lam β) pr 0 zp (claims β) T = par T := by
      simp only [wealthPV]
      refine integral_fun_const _ _ fun ω => ?_
      have hm : moneyIn 0 pr zp T ω = 0 := by
        cases T with
        | zero => rfl
        | succ k => simp [moneyIn, zp]
      simp only [hm, add_zero, pk, lam, pr, claims]
      have := pow_pos hβ0 T
      field_simp
    rw [hW]
    have : 0 ≤ par T := by unfold par; split_ifs <;> norm_num
    linarith

/-- Cochrane (2023), (19.28), p. 449: in the counterexample the date-0 value of wealth is
`e_T`, alternating between `0` and `1`. -/
theorem wealthPV_cx {β : ℝ} (hβ0 : 0 < β) (T : ℕ) :
    wealthPV S (lam β) pr 0 zp (claims β) T = par T := by
  simp only [wealthPV]
  refine integral_fun_const _ _ fun ω => ?_
  have hm : moneyIn 0 pr zp T ω = 0 := by
    cases T with
    | zero => rfl
    | succ k => simp [moneyIn, zp]
  simp only [hm, add_zero, pk, lam, pr, claims]
  have := pow_pos hβ0 T
  field_simp

end RefCx

open RefCx in
/-- Cochrane (2023), p. 439 ("their optimal choices include transversality conditions") and
(19.28), p. 449, **the admissible reference plan cannot be dropped from
`HouseholdMeasureTVC.tvc_of_optimal`.** For `0 < β < 1`, utility `u(c, m) = c`, state prices
`Λ_t = βᵗ`, price level `1`, endowment `y_t = (−1)ᵗ/βᵗ`, no taxes, no initial wealth and the
constraint `m ≥ 0`: consuming nothing with the claims `a_t = e_t/βᵗ` is optimal; the prices are
regular; consumption, money, claims, endowment and taxes are bounded at each date and adapted;
utility is concave and increasing along the bundle `ϑ = 0`; the bundle cost is `1`; the
constraint allows every Kamihigashi deviation; the normalised first-order condition
`βᵀu_c = Λ_Tw_T` holds; and yet the reference plan is not admissible and the transversality
condition fails: `E[pk_T(a_T + M_{T−1})] = e_T` does not tend to `0`. -/
theorem tvc_needs_reference {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Optimal S β (fun x _ => x) (NonnegMoney S) (lam β) pr (endow β) zp 0 0 zp zp (claims β) ∧
      PriceRegular S (lam β) pr ∧
      (∀ n, BddAt S (zp (Ω := Ω) n)) ∧ (∀ n, BddAt S (claims (Ω := Ω) β n)) ∧
      (∀ n, BddAt S (endow (Ω := Ω) β n)) ∧ StronglyAdapted S.𝓕 (endow (Ω := Ω) β) ∧
      StronglyAdapted S.𝓕 (zp (Ω := Ω)) ∧
      (∀ x z : ℝ, ConcaveOn ℝ Set.univ (fun e => (fun x _ => x : ℝ → ℝ → ℝ) (x + e) (z + 0 * e)))
      ∧ (∀ x z : ℝ, Monotone (fun e => (fun x _ => x : ℝ → ℝ → ℝ) (x + e) (z + 0 * e))) ∧
      (∀ n ω, wedge S 0 (lam β) pr n ω = 1) ∧
      (∀ T, ∃ θ₀, 0 < θ₀ ∧ θ₀ ≤ 1 ∧ ∀ θ, 0 < θ → θ < θ₀ →
        NonnegMoney S (kamC S 0 (lam β) pr (endow β) zp (claims β) zp zp T θ)
          (kamM S 0 (lam β) pr (endow β) zp (claims β) zp zp T θ)) ∧
      (∀ T, ∀ᵐ ω ∂S.μ, β ^ T * ((1 : ℝ) + 0 * 0) = lam β T ω * wedge S 0 (lam β) pr T ω) ∧
      ¬ UAdmissible S β (fun n ω => (fun x _ => x : ℝ → ℝ → ℝ)
        (cRef S 0 (lam β) pr (endow β) zp zp zp n ω) (mRef S 0 (lam β) pr (endow β) zp zp zp n ω))
      ∧ (∀ L, 0 < L → ∃ᶠ T in atTop, wealthPV S (lam β) pr 0 zp (claims β) T < L) ∧
      ¬ Tendsto (wealthPV S (lam β) pr 0 zp (claims β)) atTop (𝓝 0) := by
  have hp := priceRegular_cx (S := S) hβ0
  have hw : ∀ n ω, wedge S 0 (lam β) pr n ω = 1 := fun n ω => by simp [wedge]
  have hlim : ∀ L, 0 < L → ∃ᶠ T in atTop, wealthPV S (lam β) pr 0 zp (claims β) T < L := by
    intro L hL
    refine frequently_atTop.2 fun N => ⟨2 * N, by omega, ?_⟩
    rw [wealthPV_cx hβ0]
    simp [par, hL]
  refine ⟨?_, hp, fun _ => BddAt.const _, fun _ => BddAt.const _, fun _ => BddAt.const _,
    fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    fun x _ => ⟨convex_univ, fun a _ b _ p q _ _ hpq => le_of_eq (by
      simp only [smul_eq_mul]
      linear_combination x * hpq)⟩,
    fun x _ a b hab => by simp only; linarith, hw, fun T => ⟨1, one_pos, le_rfl,
      fun θ _ _ n => Eventually.of_forall fun ω => ?_⟩, fun T => Eventually.of_forall fun ω => ?_,
    ?_, hlim, ?_⟩
  · refine optimal_of_supergradient_liminf (lam := 1) hβ0 (priceWeak_of_priceRegular hp)
      (fun t => integrable_fun_const _ ((-1) ^ t) fun ω => by
        have := pow_pos hβ0 t
        simp only [lam, endow]
        field_simp)
      (fun t => integrable_fun_const _ 0 fun ω => by simp [zp]) zero_le_one (feasible_cx hβ0)
      (fun t => Eventually.of_forall fun ω => le_rfl)
      (UAdmissible.of_bdd hβ0.le hβ1 (fun _ => aestronglyMeasurable_const) (K := 0)
        fun _ _ => by simp [zp]) hlim fun c' m' a' _ hm' t => ?_
    filter_upwards [hm' t] with ω hω
    have hι : iota S (lam β) pr t ω = 1 - β := by simp [iota, bondPrice_cx hβ0]
    rw [hι]
    have hb := pow_pos hβ0 t
    simp only [lam, zp, one_mul]
    nlinarith [mul_nonneg (mul_nonneg hb.le (sub_nonneg.2 hβ1.le)) hω]
  · simp [kamM, mRef, zp]
  · simp [lam, wedge]
  · intro hU
    obtain ⟨ω, hω⟩ := hU.2.1.exists
    apply not_summable_one
    refine hω.congr fun n => ?_
    simp only [cRef, wedge, zp, endow, mul_zero, add_zero, sub_zero, zero_add,
      zero_mul, div_one]
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (pow_pos hβ0 n)]
    have := pow_pos hβ0 n
    field_simp
  · intro h
    have := (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))
    obtain ⟨N, hN⟩ := eventually_atTop.1 this
    have := hN (2 * N + 1) (by omega)
    rw [wealthPV_cx hβ0] at this
    have hp1 : (2 * N + 1) % 2 = 1 := by omega
    simp [par, hp1] at this
    linarith

/-! ### Nonsatiation is needed -/

namespace SatCx

/-- Cochrane (2023), p. 439 (counterexample): the claims `a_t = 1/βᵗ` (one unit of date-0 wealth
kept for ever). -/
noncomputable def claims (β : ℝ) (t : ℕ) (_ : Ω) : ℝ := 1 / β ^ t

/-- Cochrane (2023), p. 439 (counterexample): initial claims `1`. -/
def one (_ : Ω) : ℝ := 1

/-- Cochrane (2023), (19.10), p. 439: consuming nothing and keeping one unit of wealth for ever is
feasible. -/
theorem feasible_sat {β : ℝ} (hβ0 : 0 < β) :
    Feasible S (RefCx.lam β) RefCx.pr RefCx.zp RefCx.zp 0 one RefCx.zp RefCx.zp (claims β) := by
  refine ⟨by funext ω; simp [claims, one], fun _ => stronglyMeasurable_const,
    fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    fun t => Eventually.of_forall fun ω => ?_, fun t => ?_, fun t => ?_, fun t => ?_,
    fun t => ?_, fun δ hδ => Eventually.of_forall fun T => ?_⟩
  · simp only [claimCost]
    rw [E_fun_const t (fun ω => pk (RefCx.lam β) RefCx.pr (t + 1) ω * claims β (t + 1) ω) 1 (by
      funext ω
      simp only [pk, RefCx.lam, RefCx.pr, claims]
      have := pow_pos hβ0 (t + 1)
      field_simp)]
    have hm : moneyIn 0 RefCx.pr RefCx.zp t ω = 0 := by
      cases t with
      | zero => rfl
      | succ k => simp [moneyIn, RefCx.zp]
    simp only [hm, claims, pk, RefCx.lam, RefCx.pr, RefCx.zp]
    have := pow_pos hβ0 t
    field_simp
    ring
  · exact integrable_fun_const _ 1 fun ω => by
      have := pow_pos hβ0 t
      simp only [pk, RefCx.lam, RefCx.pr, claims]
      field_simp
  · refine (integrable_zero Ω ℝ S.μ).congr (Eventually.of_forall fun ω => ?_)
    cases t with
    | zero => simp [moneyIn]
    | succ k => simp [moneyIn, RefCx.zp]
  · simp [RefCx.zp]
  · simp [RefCx.zp]
  · have hW : wealthPV S (RefCx.lam β) RefCx.pr 0 RefCx.zp (claims β) T = 1 := by
      simp only [wealthPV]
      refine integral_fun_const _ _ fun ω => ?_
      have hm : moneyIn 0 RefCx.pr RefCx.zp T ω = 0 := by
        cases T with
        | zero => rfl
        | succ k => simp [moneyIn, RefCx.zp]
      simp only [hm, add_zero, pk, RefCx.lam, RefCx.pr, claims]
      have := pow_pos hβ0 T
      field_simp
    rw [hW]
    linarith

/-- Cochrane (2023), (19.28), p. 449: in the satiation counterexample the date-0 value of wealth
is `1` at every date. -/
theorem wealthPV_sat {β : ℝ} (hβ0 : 0 < β) (T : ℕ) :
    wealthPV S (RefCx.lam β) RefCx.pr 0 RefCx.zp (claims β) T = 1 := by
  simp only [wealthPV]
  refine integral_fun_const _ _ fun ω => ?_
  have hm : moneyIn 0 RefCx.pr RefCx.zp T ω = 0 := by
    cases T with
    | zero => rfl
    | succ k => simp [moneyIn, RefCx.zp]
  simp only [hm, add_zero, pk, RefCx.lam, RefCx.pr, claims]
  have := pow_pos hβ0 T
  field_simp

end SatCx

open RefCx in
/-- Cochrane (2023), p. 439 and (19.28), p. 449, **nonsatiation cannot be dropped from the
transversality theorem.** With constant utility `u ≡ 0`, `Λ_t = βᵗ`, `P_t = 1`, no endowment or
taxes and initial claims `1`, keeping the unit of wealth for ever (`a_t = 1/βᵗ`) is optimal; every
hypothesis of `HouseholdMeasureTVC.tvc_of_optimal` other than the normalised first-order condition
holds (regular prices, all bounds, concavity and monotonicity along the bundle, an admissible
reference plan, `Con` trivially allowing every deviation), the first-order condition holds with
the multiplier `λ = 0`, and the transversality condition fails: `E[pk_T(a_T + M_{T−1})] = 1`. -/
theorem tvc_needs_nonsatiation {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Optimal S β (fun _ _ => 0) (fun _ _ => True) (lam β) pr zp zp 0 SatCx.one zp zp
        (SatCx.claims β) ∧
      PriceRegular S (lam β) pr ∧ (∀ n, BddAt S (SatCx.claims (Ω := Ω) β n)) ∧
      (∀ x z : ℝ, ConcaveOn ℝ Set.univ (fun e => (fun _ _ => 0 : ℝ → ℝ → ℝ) (x + e) (z + 0 * e)))
      ∧ (∀ x z : ℝ, Monotone (fun e => (fun _ _ => 0 : ℝ → ℝ → ℝ) (x + e) (z + 0 * e))) ∧
      UAdmissible S β (fun n ω => (fun _ _ => 0 : ℝ → ℝ → ℝ)
        (cRef S 0 (lam β) pr zp zp zp zp n ω) (mRef S 0 (lam β) pr zp zp zp zp n ω)) ∧
      (∀ T, ∀ᵐ ω ∂S.μ, β ^ T * ((0 : ℝ) + 0 * 0) = 0 * (lam β T ω * wedge S 0 (lam β) pr T ω)) ∧
      ¬ Tendsto (wealthPV S (lam β) pr 0 zp (SatCx.claims β)) atTop (𝓝 0) := by
  have hadm0 : ∀ f : ℕ → Ω → ℝ, (∀ n ω, f n ω = 0) → UAdmissible S β f := fun f hf =>
    UAdmissible.of_bdd hβ0.le hβ1 (fun n => by
      rw [show f n = fun _ => 0 from funext (hf n)]
      exact aestronglyMeasurable_const) (K := 0) fun n ω => by rw [hf]; simp
  refine ⟨⟨SatCx.feasible_sat hβ0, trivial, hadm0 _ fun _ _ => rfl, fun c' m' a' _ _ _ =>
      le_of_eq rfl⟩,
    priceRegular_cx hβ0, fun n => bddAt_fun_const _ (1 / β ^ n) fun _ => rfl,
    fun _ _ => concaveOn_const _ convex_univ,
    fun _ _ _ _ _ => le_rfl, hadm0 _ fun _ _ => rfl,
    fun T => Eventually.of_forall fun ω => by ring, fun h => ?_⟩
  have h1 : Tendsto (wealthPV S (lam β) pr 0 zp (SatCx.claims β)) atTop (𝓝 1) := by
    have e : wealthPV S (lam β) pr 0 zp (SatCx.claims β) = fun _ => 1 :=
      funext (SatCx.wealthPV_sat hβ0)
    rw [e]
    exact tendsto_const_nhds
  have := tendsto_nhds_unique h h1
  norm_num at this

namespace SatCIA

/-- Cochrane (2023), (19.24)–(19.26), p. 448 (counterexample): the constant process `1`
(consumption, endowment and overnight money). -/
def onep (_ : ℕ) (_ : Ω) : ℝ := 1

/-- Cochrane (2023), (19.27), p. 449: in the cash-in-advance satiation economy (`V = 1`,
endowment, consumption and money `1`, initial money and claims `1`), keeping the unit of claims
for ever is feasible and the date-0 value of wealth is `1 + βᵀ`. -/
theorem feasible_cia {β : ℝ} (hβ0 : 0 < β) :
    Feasible S (RefCx.lam β) RefCx.pr onep RefCx.zp SatCx.one SatCx.one onep onep
      (SatCx.claims β) ∧ ∀ T, wealthPV S (RefCx.lam β) RefCx.pr SatCx.one onep (SatCx.claims β) T
        = 1 + β ^ T := by
  have hW : ∀ T, wealthPV S (RefCx.lam β) RefCx.pr SatCx.one onep (SatCx.claims β) T =
      1 + β ^ T := by
    intro T
    simp only [wealthPV]
    refine integral_fun_const _ _ fun ω => ?_
    have hm : moneyIn SatCx.one RefCx.pr onep T ω = 1 := by
      cases T with
      | zero => rfl
      | succ k => simp [moneyIn, onep, RefCx.pr]
    simp only [hm, pk, RefCx.lam, RefCx.pr, SatCx.claims]
    have := pow_pos hβ0 T
    field_simp
  refine ⟨⟨by funext ω; simp [SatCx.claims, SatCx.one], fun _ => stronglyMeasurable_const,
    fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
    fun t => Eventually.of_forall fun ω => ?_, fun t => ?_, fun t => ?_,
    fun t => integrable_fun_const _ (β ^ t) fun ω => by simp [RefCx.lam, onep],
    fun t => integrable_fun_const _ (β ^ t) fun ω => by simp [RefCx.lam, onep],
    fun δ hδ => Eventually.of_forall fun T => ?_⟩, hW⟩
  · simp only [claimCost]
    rw [E_fun_const t (fun ω => pk (RefCx.lam β) RefCx.pr (t + 1) ω * SatCx.claims β (t + 1) ω)
      1 (by
        funext ω
        simp only [pk, RefCx.lam, RefCx.pr, SatCx.claims]
        have := pow_pos hβ0 (t + 1)
        field_simp)]
    have hm : moneyIn SatCx.one RefCx.pr onep t ω = 1 := by
      cases t with
      | zero => rfl
      | succ k => simp [moneyIn, onep, RefCx.pr]
    simp only [hm, SatCx.claims, pk, RefCx.lam, RefCx.pr, RefCx.zp, onep]
    have := pow_pos hβ0 t
    field_simp
    ring
  · exact integrable_fun_const _ 1 fun ω => by
      have := pow_pos hβ0 t
      simp only [pk, RefCx.lam, RefCx.pr, SatCx.claims]
      field_simp
  · refine integrable_fun_const _ (β ^ t) fun ω => ?_
    cases t with
    | zero => simp [moneyIn, pk, RefCx.lam, RefCx.pr, SatCx.one]
    | succ k => simp [moneyIn, pk, RefCx.lam, RefCx.pr, onep]
  · rw [hW]
    have := pow_pos hβ0 T
    linarith

end SatCIA

open RefCx SatCx SatCIA in
/-- Cochrane (2023), (19.28), p. 449, **`u' > 0` cannot be dropped from the cash-in-advance
transversality theorem.** For `0 < β < 1`, velocity `V = 1`, utility `u ≡ 0`, state prices
`Λ_t = βᵗ`, price level `1`, endowment, consumption and overnight money `1`, no taxes, initial
money and claims `1` and claims `a_t = 1/βᵗ`: the plan is optimal in the cash-in-advance problem
(`CashInAdvanceMeasure.CIAOptimal`), and every hypothesis of
`CashInAdvanceMeasureTVC.tvc_necessary` holds — regular prices, all per-date bounds, overnight
money at least `1`, `Q_t = β ≤ 1`, an admissible reference plan with nonnegative money, `u`
concave and increasing with continuous derivative `0` — except `u' > 0` and the normalisation
`Λ_0w_0 = u'(c_0)`; and the transversality condition fails: `E[pk_T(a_T + M_{T−1})] = 1 + βᵀ`. -/
theorem cia_needs_nonsatiation {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    CashInAdvanceMeasure.CIAOptimal S β (fun _ => 0) 1 (lam β) pr onep zp SatCx.one SatCx.one
        onep onep (SatCx.claims β) ∧
      (∀ x : ℝ, HasDerivAt (fun _ => (0 : ℝ)) 0 x) ∧ ConcaveOn ℝ Set.univ (fun _ : ℝ => (0 : ℝ))
      ∧ Monotone (fun _ : ℝ => (0 : ℝ)) ∧ PriceRegular S (lam β) pr ∧
      (∀ n, BddAt S (onep (Ω := Ω) n)) ∧ (∀ n, BddAt S (SatCx.claims (Ω := Ω) β n)) ∧
      (∀ n, BddAt S (zp (Ω := Ω) n)) ∧ (∀ t, ∀ᵐ ω ∂S.μ, (1 : ℝ) ≤ onep t ω) ∧
      (∀ t, ∀ᵐ ω ∂S.μ, bondPrice S (lam β) pr t ω ≤ 1) ∧
      UAdmissible S β (fun n ω => (fun _ : ℝ => (0 : ℝ)) (cRef S (1 / 1 - 1) (lam β) pr onep zp
        onep onep n ω)) ∧
      (∀ n, ∀ᵐ ω ∂S.μ, 0 ≤ mRef S (1 / 1 - 1) (lam β) pr onep zp onep onep n ω) ∧
      ¬ Tendsto (wealthPV S (lam β) pr SatCx.one onep (SatCx.claims β)) atTop (𝓝 0) := by
  obtain ⟨hF, hW⟩ := feasible_cia (S := S) hβ0
  have hadm0 : ∀ f : ℕ → Ω → ℝ, (∀ n ω, f n ω = 0) → UAdmissible S β f := fun f hf =>
    UAdmissible.of_bdd hβ0.le hβ1 (fun n => by
      rw [show f n = fun _ => 0 from funext (hf n)]
      exact aestronglyMeasurable_const) (K := 0) fun n ω => by rw [hf]; simp
  refine ⟨⟨hF, fun t => Eventually.of_forall fun ω => ⟨by simp [onep], by simp [onep]⟩,
      hadm0 _ fun _ _ => rfl, fun c' m' a' _ _ _ => le_of_eq rfl⟩,
    fun x => hasDerivAt_const x 0, concaveOn_const _ convex_univ, fun _ _ _ => le_rfl,
    priceRegular_cx hβ0, fun _ => BddAt.const _, fun n => bddAt_fun_const _ (1 / β ^ n)
      fun _ => rfl, fun _ => BddAt.const _, fun t => Eventually.of_forall fun ω => le_rfl,
    fun t => Eventually.of_forall fun ω => by rw [bondPrice_cx hβ0]; exact hβ1.le,
    hadm0 _ fun _ _ => rfl, fun n => Eventually.of_forall fun ω => by simp [mRef, onep], ?_⟩
  intro h
  have h1 : Tendsto (wealthPV S (lam β) pr SatCx.one onep (SatCx.claims β)) atTop (𝓝 1) := by
    have e : wealthPV S (lam β) pr SatCx.one onep (SatCx.claims β) = fun T => 1 + β ^ T :=
      funext hW
    rw [e]
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_add 1
  have := tendsto_nhds_unique h h1
  norm_num at this

end Cochrane.Monetarism.TidyR6HouseholdTVCCx
