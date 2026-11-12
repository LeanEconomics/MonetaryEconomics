/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalModel.TidyR6MeasFamilyVersion
import IntertemporalModel.TidyR6MeasFiscal
import IntertemporalModel.Links

/-!
# The Woodford contrasts on a genuine probability space

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 2, §2.4 (p. 33: "inflation is
stable and determinate under a peg"), §2.6 (pp. 39–40: no Taylor principle) and p. 39 (passive
fiscal policy), set against Woodford (2003), *Interest and Prices*, Propositions 2.5 and 2.6 and
eq. (4.2), restated from `Links` on a probability space (`MeasExpectationSystem`). The
counterexamples live in the i.i.d. `±1` coin economy of `ExpectationsMeasureIID`, a genuine
infinite-horizon probability space in which every history is null; "uncountably many solutions"
is proved **up to null sets** (no countable family of paths matches every solution almost
surely at date `1`).

## Main results

* Proposition 2.5: `sunP` (the sunspot price paths `P_{t+1} = P_t/(1 − σ c(ε_{t+1}))`),
  `sunP_mem`, `sunP_distinct`, `prop_2_5_meas` (uncountably many solutions of the Fisher
  equation with `P_0 = 1`, up to null sets); `peg_contrast_meas` (with the valuation equation
  there is exactly one equilibrium, `P ≡ 1` almost surely, and it is one of Woodford's paths).
* Proposition 2.6: `Eq26M`, `eq26M_iff_solves`, `DetCrit`, `prop_2_6_meas` (bounded solutions of
  Woodford's (2.6) exist and are unique almost surely for every bounded adapted `r̂`, `ī` iff
  `|φ_π| > 1`, on the coin economy); `taylor_contrast_meas` (for `|θ| ≤ 1` the criterion fails,
  yet the fiscal-theory rule model has a solution unique almost surely for every disturbance and
  shock); `taylor_contrast_coin_meas` (uncountably many bounded solutions of (2.6) with `π_0 = 0`
  versus exactly one equilibrium `π ≡ 0`).
* Woodford's (4.2): `mDiscount`, `mRicardian_tvc` (the transversality condition holds along every
  path and in conditional expectation); `passivePath`, `mPassive_any_price` (under the passive
  rule the valuation equation holds for every initial real debt, so it does not determine the
  price level); `mActive_unique_value` (with exogenous bounded surpluses flow plus transversality
  pin real debt to the present value).
* Links back to the core: `Link.tree_eq26M_iff` (finite trees), `mDiscount_eq_discount`.
-/

namespace Cochrane.IntertemporalModel.TidyR6MeasLinks

open MeasureTheory ProbabilityTheory Filter Topology ExpectationsMeasure TidyR5Meas
  TidyR5MeasLinear ExpectationsMeasureIID

/-! ### The coin economy and the clamped coin -/

/-- Cochrane (2023), Ch. 2, p. 29: the clamped coin `c(x) = max(−1, min(1, x))`, equal to the
coin almost surely and bounded by `1` in every state. -/
noncomputable def cc (x : ℝ) : ℝ := TidyR6MeasFamilyVersion.clamp 1 x

/-- Cochrane (2023), Ch. 2, p. 29: the clamped coin is bounded by `1`. -/
theorem abs_cc_le (x : ℝ) : |cc x| ≤ 1 := TidyR6MeasFamilyVersion.abs_clamp_le zero_le_one x

/-- Cochrane (2023), Ch. 2, p. 29: the clamped coin is measurable. -/
theorem measurable_cc : Measurable cc := TidyR6MeasFamilyVersion.measurable_clamp 1

/-- Cochrane (2023), Ch. 2, p. 29: `c(1) = 1` and `c(−1) = −1`. -/
theorem cc_one_neg : cc 1 = 1 ∧ cc (-1) = -1 :=
  ⟨TidyR6MeasFamilyVersion.clamp_eq (by norm_num), TidyR6MeasFamilyVersion.clamp_eq (by norm_num)⟩

/-- Cochrane (2023), Ch. 2, p. 29: `E_t[a + b c(ε_{t+1})] = a` almost surely in the coin
economy. -/
theorem E_cc (t : ℕ) (a b : ℝ) :
    (iidSystem coin).E t (fun ω => a + b * cc (ω (t + 1))) =ᵐ[(iidSystem coin).μ]
      fun _ => a := by
  have h := E_shock_fun coin t (f := fun x => a + b * cc x)
    (measurable_const.add (measurable_const.mul measurable_cc))
  have hI : ∫ x, (fun x => a + b * cc x) x ∂(coin : Measure ℝ) = a := by
    rw [integral_coin, cc_one_neg.1, cc_one_neg.2]
    ring
  rw [hI] at h
  exact h

/-- Cochrane (2023), Ch. 2, p. 29: the date-`1` clamped coin is not almost surely zero
(`E c(ε_1)² = 1`). -/
theorem cc_not_ae_zero : ¬ (fun ω : ℕ → ℝ => cc (ω 1)) =ᵐ[(iidSystem coin).μ] 0 := by
  intro h
  have h1 : ∫ ω, (fun x => x ^ 2) (cc (ω 1)) ∂(iidSystem coin).μ = 1 := by
    rw [integral_shock_fun coin 1 (f := fun x => cc x ^ 2) (measurable_cc.pow_const 2),
      integral_coin, cc_one_neg.1, cc_one_neg.2]
    norm_num
  have h2 : ∫ ω, (fun x => x ^ 2) (cc (ω 1)) ∂(iidSystem coin).μ = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) (h.mono fun ω hω => by
      simp only [Pi.zero_apply] at hω
      simp [hω])]
    simp
  rw [h1] at h2
  exact one_ne_zero h2

/-- Cochrane (2023), Ch. 2, p. 29: distinct multiples of the date-`1` clamped coin differ with
positive probability. -/
theorem cc_mul_ne {σ σ' : ℝ} (h : σ ≠ σ') :
    ¬ (fun ω : ℕ → ℝ => σ * cc (ω 1)) =ᵐ[(iidSystem coin).μ] fun ω => σ' * cc (ω 1) := by
  intro he
  apply cc_not_ae_zero
  filter_upwards [he] with ω hω
  have : (σ - σ') * cc (ω 1) = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h)

/-- Cochrane (2023), Ch. 2, p. 29: the clamped coin of date `s ≤ t` is known at `t`. -/
theorem measurable_cc_shock {s t : ℕ} (hst : s ≤ t) :
    Measurable[(iidSystem coin).𝓕 t] (fun ω : ℕ → ℝ => cc (ω s)) :=
  measurable_cc.comp (measurable_shock coin hst)

/-! ### Woodford's Proposition 2.5 and the peg -/

/-- Woodford (2003), §A.6, p. 639 (restated, `u_c ≡ 1`), used for Cochrane (2023), p. 33: the
sunspot price paths `P_0 = 1`, `P_{t+1} = P_t/(1 − σ c(ε_{t+1}))`.
Restates `Links.sunspotPrice` on a genuine probability space. -/
noncomputable def sunP (σ : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun ω => sunP σ t ω / (1 - σ * cc (ω (t + 1)))

/-- Woodford (2003), p. 87 (restated), used for Cochrane (2023), p. 33: the set of price paths
solving the exact Fisher equation (2.3) under the peg `i ≡ β⁻¹ − 1` on the coin economy, almost
surely, with positive adapted prices, integrable `P_t/P_{t+1}` and `P_0 = 1` almost surely.
Restates `Links.FisherExactW` on a genuine probability space. -/
def WFisher (β : ℝ) : Set (ℕ → (ℕ → ℝ) → ℝ) :=
  {P | (∀ t, ∀ᵐ ω ∂(iidSystem coin).μ, 0 < P t ω) ∧ StronglyAdapted (iidSystem coin).𝓕 P ∧
    (∀ t, Integrable (fun ω => P t ω / P (t + 1) ω) (iidSystem coin).μ) ∧
    MBondPricing (iidSystem coin) β P (fun _ _ => β⁻¹ - 1) ∧
    P 0 =ᵐ[(iidSystem coin).μ] fun _ => 1}

/-- Woodford (2003), §A.6 (restated): for `|σ| < 1` the sunspot path is positive in every
state.
Restates `Links.sunspotPrice_pos` on a genuine probability space. -/
theorem sunP_pos {σ : ℝ} (hσ : |σ| < 1) (t : ℕ) (ω : ℕ → ℝ) : 0 < sunP σ t ω := by
  have hd : ∀ x, 0 < 1 - σ * cc x := fun x => by
    have h1 : |σ * cc x| < 1 := by
      rw [abs_mul]
      nlinarith [abs_cc_le x, abs_nonneg σ, abs_nonneg (cc x)]
    linarith [le_abs_self (σ * cc x)]
  induction t with
  | zero => exact one_pos
  | succ t ih => exact div_pos ih (hd _)

/-- Woodford (2003), §A.6 (restated): `P_t/P_{t+1} = 1 − σ c(ε_{t+1})` along the sunspot path. -/
theorem sunP_ratio {σ : ℝ} (hσ : |σ| < 1) (t : ℕ) (ω : ℕ → ℝ) :
    sunP σ t ω / sunP σ (t + 1) ω = 1 - σ * cc (ω (t + 1)) := by
  change sunP σ t ω / (sunP σ t ω / (1 - σ * cc (ω (t + 1)))) = _
  rw [div_div_cancel₀ (sunP_pos hσ t ω).ne']

/-- Woodford (2003), §A.6 (restated): the sunspot path is adapted. -/
theorem sunP_adapted (σ : ℝ) : StronglyAdapted (iidSystem coin).𝓕 (sunP σ) := by
  intro t
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih =>
    exact ((ih.mono ((iidSystem coin).𝓕.mono (Nat.le_succ t))).measurable.div
      (measurable_const.sub (measurable_const.mul (measurable_cc_shock le_rfl)))
      ).stronglyMeasurable

/-- Woodford (2003), Proposition 2.5 (restated), on the coin economy: for `|σ| < 1` the sunspot
path solves the Fisher equation under the peg almost surely.
Restates `Links.sunspot_fisher` on a genuine probability space. -/
theorem sunP_mem {β σ : ℝ} (hσ : |σ| < 1) : sunP σ ∈ WFisher β := by
  refine ⟨fun t => Eventually.of_forall fun ω => sunP_pos hσ t ω, sunP_adapted σ, fun t => ?_,
    fun t => ?_, Eventually.of_forall fun _ => rfl⟩
  · refine (Integrable.of_bound (C := 1 + |σ|) ?_ (Eventually.of_forall fun ω => ?_))
    · exact (((sunP_adapted σ t).mono ((iidSystem coin).𝓕.le t)).measurable.div
        ((sunP_adapted σ (t + 1)).mono ((iidSystem coin).𝓕.le (t + 1))).measurable
        ).aestronglyMeasurable
    · rw [Real.norm_eq_abs, sunP_ratio hσ]
      refine (abs_sub _ _).trans ?_
      rw [abs_one, abs_mul]
      nlinarith [abs_cc_le (ω (t + 1)), abs_nonneg σ]
  · have hr : (fun ω => sunP σ t ω / sunP σ (t + 1) ω) = fun ω => 1 + (-σ) * cc (ω (t + 1)) := by
      funext ω
      rw [sunP_ratio hσ]
      ring
    rw [hr]
    filter_upwards [E_cc t 1 (-σ)] with ω h
    rw [Pi.smul_apply, h, smul_eq_mul]
    simp only [add_sub_cancel, mul_one]
    rw [inv_inv]

/-- Woodford (2003), §A.6 (restated), on the coin economy: distinct `σ` give sunspot paths that
differ with positive probability at date `1`.
Restates `Links.sunspotPrice_injective` on a genuine probability space. -/
theorem sunP_distinct {σ σ' : ℝ} (hσ : |σ| < 1) (hσ' : |σ'| < 1) (h : σ ≠ σ') :
    ¬ sunP σ 1 =ᵐ[(iidSystem coin).μ] sunP σ' 1 := by
  intro he
  apply cc_mul_ne h
  filter_upwards [he] with ω hω
  have e1 := sunP_ratio hσ 0 ω
  have e2 := sunP_ratio hσ' 0 ω
  have h0 : sunP σ 0 ω = sunP σ' 0 ω := rfl
  have hω' : sunP σ (0 + 1) ω = sunP σ' (0 + 1) ω := hω
  rw [hω', h0] at e1
  rw [e1] at e2
  linarith

/-- Woodford (2003), Proposition 2.5, p. 87 (restated) **on a genuine probability space**: in the
i.i.d. coin economy with the peg `i ≡ β⁻¹ − 1` (any `β`) the exact Fisher equation has
uncountably many solutions with `P_0 = 1`, even up to null sets: the sunspot paths `sunP σ`,
`|σ| < 1`, are solutions, pairwise different with positive probability, and no countable family
of paths matches every solution almost surely at date `1`.
Restates `Links.prop_2_5_uncountable` on a genuine probability space. -/
theorem prop_2_5_meas (β : ℝ) :
    (∀ σ ∈ Set.Ioo (-1 : ℝ) 1, sunP σ ∈ WFisher β) ∧
      (∀ σ ∈ Set.Ioo (-1 : ℝ) 1, ∀ σ' ∈ Set.Ioo (-1 : ℝ) 1, σ ≠ σ' →
        ¬ sunP σ 1 =ᵐ[(iidSystem coin).μ] sunP σ' 1) ∧
      ¬ ∃ C : Set (ℕ → (ℕ → ℝ) → ℝ), C.Countable ∧
        ∀ P ∈ WFisher β, ∃ Q ∈ C, P 1 =ᵐ[(iidSystem coin).μ] Q 1 := by
  have habs : ∀ σ ∈ Set.Ioo (-1 : ℝ) 1, |σ| < 1 := fun σ hσ => abs_lt.mpr hσ
  refine ⟨fun σ hσ => sunP_mem (habs σ hσ),
    fun σ hσ σ' hσ' h => sunP_distinct (habs σ hσ) (habs σ' hσ') h, ?_⟩
  rintro ⟨C, hC, hcov⟩
  have hg : ∀ σ : Set.Ioo (-1 : ℝ) 1, ∃ Q : C, sunP σ 1 =ᵐ[(iidSystem coin).μ] Q.1 1 :=
    fun σ => by
      obtain ⟨Q, hQ, h⟩ := hcov _ (sunP_mem (habs σ σ.2))
      exact ⟨⟨Q, hQ⟩, h⟩
  choose g hgs using hg
  have hinj : Function.Injective g := by
    intro σ σ' he
    by_contra hne
    have hne' : (σ : ℝ) ≠ σ' := fun h => hne (Subtype.ext h)
    exact sunP_distinct (habs σ σ.2) (habs σ' σ'.2) hne'
      ((hgs σ).trans ((congrArg (fun Q : C => Q.1 1) he) ▸ (hgs σ').symm))
  have : Countable C := hC.to_subtype
  have hc : (Set.Ioo (-1 : ℝ) 1).Countable := Set.countable_coe_iff.mp hinj.countable
  rw [Cardinal.Real.Ioo_countable_iff] at hc
  norm_num at hc

/-- Cochrane (2023), eq. (2.7), p. 22: with constant surpluses `1 − β` (`0 ≤ β < 1`) the present
value is `1` at every date (any probability space).
Generalises `TidyR6MeasHyp.Uniform.pv_half`. -/
theorem pv_one {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (t : ℕ) :
    S.forwardSol β (fun _ _ => 1 - β) t = fun _ => 1 := by
  have e : MeasExpectationSystem.discSum (Ω := Ω) β (fun _ _ => 1 - β) t = fun _ => 1 := by
    funext ω
    simp only [MeasExpectationSystem.discSum]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0 hβ1, inv_mul_cancel₀ (by linarith)]
  change S.E t _ = _
  rw [e, S.E_const]

/-- Cochrane (2023), p. 33 against Woodford (2003), Proposition 2.5, **on a genuine probability
space** ("the fiscal theory overturns" the indeterminacy of pegs): in the i.i.d. coin economy
with the peg `i ≡ β⁻¹ − 1` (`0 < β < 1`), surpluses `s ≡ 1 − β` and `B_{−1} = 1`:
(a) the Fisher equation alone has uncountably many solutions with `P_0 = 1`, up to null sets;
(b) `P ≡ 1`, `B ≡ 1` is an equilibrium; (c) every equilibrium has `P_t = 1` almost surely at
every date; (d) every equilibrium price path is one of the Fisher solutions of (a).
Restates `Links.peg_contrast` on a genuine probability space. -/
theorem peg_contrast_meas {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    (¬ ∃ C : Set (ℕ → (ℕ → ℝ) → ℝ), C.Countable ∧
        ∀ P ∈ WFisher β, ∃ Q ∈ C, P 1 =ᵐ[(iidSystem coin).μ] Q 1) ∧
      MEquilibrium (iidSystem coin) β (fun _ => 1) (fun _ _ => 1 - β) (fun _ _ => 1)
        (fun _ _ => 1) (fun _ _ => β⁻¹ - 1) ∧
      (∀ B P : ℕ → (ℕ → ℝ) → ℝ, MEquilibrium (iidSystem coin) β (fun _ => 1)
        (fun _ _ => 1 - β) B P (fun _ _ => β⁻¹ - 1) → ∀ t, P t =ᵐ[(iidSystem coin).μ] 1) ∧
      ∀ B P : ℕ → (ℕ → ℝ) → ℝ, MEquilibrium (iidSystem coin) β (fun _ => 1)
        (fun _ _ => 1 - β) B P (fun _ _ => β⁻¹ - 1) → P ∈ WFisher β := by
  set CS := iidSystem coin
  have hpv := pv_one CS hβ.le hβ1
  have hpvp : ∀ t, ∀ᵐ ω ∂CS.μ, 0 < CS.forwardSol β (fun _ _ => 1 - β) t ω := fun t => by
    rw [hpv t]
    exact Eventually.of_forall fun _ => one_pos
  have hone : MEquilibrium CS β (fun _ => 1) (fun _ _ => 1 - β) (fun _ _ => 1) (fun _ _ => 1)
      (fun _ _ => β⁻¹ - 1) := by
    refine ⟨fun _ => stronglyMeasurable_const, fun _ => Eventually.of_forall fun _ => one_pos,
      fun _ => stronglyMeasurable_const, fun _ => stronglyMeasurable_const,
      fun _ => (integrable_const (1 : ℝ)).congr (Eventually.of_forall fun _ => by simp),
      ⟨?_, fun t => ?_⟩, fun t => ?_⟩
    · rw [hpv 0]
      exact Eventually.of_forall fun _ => by simp
    · rw [hpv (t + 1)]
      exact Eventually.of_forall fun _ => by simp
    · have e : (fun ω => (fun (_ : ℕ) (_ : ℕ → ℝ) => (1 : ℝ)) t ω /
          (fun (_ : ℕ) (_ : ℕ → ℝ) => (1 : ℝ)) (t + 1) ω) = fun _ => 1 := by
        funext ω
        simp
      rw [e, CS.E_const]
      refine Eventually.of_forall fun ω => ?_
      simp only [Pi.smul_apply, smul_eq_mul, mul_one, add_sub_cancel, inv_inv]
  have huniq : ∀ B P : ℕ → (ℕ → ℝ) → ℝ, MEquilibrium CS β (fun _ => 1) (fun _ _ => 1 - β) B P
      (fun _ _ => β⁻¹ - 1) → ∀ t, P t =ᵐ[CS.μ] 1 := fun B P h t =>
    (TidyR6MeasHyp.mPeg_unique_pos CS hβ hpvp h t).1.trans
      (TidyR6MeasHyp.mPeg_unique_pos CS hβ hpvp hone t).1.symm
  refine ⟨(prop_2_5_meas β).2.2, hone, huniq, fun B P h => ⟨h.2.1, h.1, h.2.2.2.2.1,
    h.2.2.2.2.2.2, huniq B P h 0⟩⟩

/-! ### Woodford's Proposition 2.6 and the rule -/

/-- Woodford (2003), eq. (2.6), p. 91 (restated from `Links.Eq26`) on a probability space, used
for Cochrane (2023), §2.6: `φ_π π_t = E_t π_{t+1} + (r̂_t − ī_t)` almost surely at every date. -/
def Eq26M {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω) (φπ : ℝ)
    (r ib π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φπ • π t =ᵐ[S.μ] S.E t (π (t + 1)) + (r t - ib t)

/-- Woodford (2003), App. A, p. 636 (restated) on a probability space, used for Cochrane (2023),
§2.6: for `φ_π ≠ 0`, (2.6) is the forward equation `π_t = φ_π⁻¹ E_t π_{t+1} + u_t` with
`u_t = φ_π⁻¹(r̂_t − ī_t)`, almost surely.
Restates `Links.eq26_iff_solves` on a genuine probability space. -/
theorem eq26M_iff_solves {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)
    {φπ : ℝ} (hφ : φπ ≠ 0) {r ib π : ℕ → Ω → ℝ} :
    Eq26M S φπ r ib π ↔ S.Solves φπ⁻¹ (fun t => φπ⁻¹ • (r t - ib t)) π := by
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · filter_upwards [h] with ω hω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hω ⊢
    field_simp
    linarith
  · filter_upwards [h] with ω hω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hω ⊢
    rw [hω]
    field_simp

/-- Woodford (2003), Proposition 2.6, p. 91 (restated) on the coin economy, used for Cochrane
(2023), §2.6: the determinacy criterion "for every bounded adapted `r̂`, `ī`, (2.6) has a bounded
adapted solution, unique almost surely among bounded adapted solutions".
Restates `Links.prop_2_6_iff` on a genuine probability space. -/
def DetCrit (φπ : ℝ) : Prop :=
  ∀ r ib : ℕ → (ℕ → ℝ) → ℝ, StronglyAdapted (iidSystem coin).𝓕 r → (iidSystem coin).BddProc r →
    StronglyAdapted (iidSystem coin).𝓕 ib → (iidSystem coin).BddProc ib →
    (∃ π, Eq26M (iidSystem coin) φπ r ib π ∧ StronglyAdapted (iidSystem coin).𝓕 π ∧
      (iidSystem coin).BddProc π) ∧
    ∀ π₁ π₂, Eq26M (iidSystem coin) φπ r ib π₁ → Eq26M (iidSystem coin) φπ r ib π₂ →
      StronglyAdapted (iidSystem coin).𝓕 π₁ → StronglyAdapted (iidSystem coin).𝓕 π₂ →
      (iidSystem coin).BddProc π₁ → (iidSystem coin).BddProc π₂ →
      ∀ t, π₁ t =ᵐ[(iidSystem coin).μ] π₂ t

/-- Woodford (2003), Proposition 2.6, p. 91 (restated) **on a genuine probability space**: in the
i.i.d. coin economy, bounded solutions of (2.6) exist and are unique almost surely for every
bounded adapted `r̂`, `ī` iff `|φ_π| > 1`.
Restates `Links.prop_2_6_iff` on a genuine probability space. -/
theorem prop_2_6_meas (φπ : ℝ) : DetCrit φπ ↔ 1 < |φπ| := by
  set CS := iidSystem coin
  by_cases hφ : φπ = 0
  · subst hφ
    simp only [abs_zero]
    refine ⟨fun h => ?_, fun h => by norm_num at h⟩
    exfalso
    have hz : StronglyAdapted CS.𝓕 (0 : ℕ → (ℕ → ℝ) → ℝ) := fun _ => stronglyMeasurable_zero
    have hzb : CS.BddProc (0 : ℕ → (ℕ → ℝ) → ℝ) := ⟨0, fun _ => Eventually.of_forall fun _ => by
      simp⟩
    have hsol0 : Eq26M CS 0 0 0 (0 : ℕ → (ℕ → ℝ) → ℝ) := fun t => by
      simp only [zero_smul, Pi.zero_apply, sub_zero, add_zero]
      rw [CS.E_zero]
    set π₂ : ℕ → (ℕ → ℝ) → ℝ := fun t ω => cc (ω t) with hπ₂
    have hsol2 : Eq26M CS 0 0 0 π₂ := fun t => by
      have h := E_cc t 0 1
      simp only [zero_add, one_mul] at h
      filter_upwards [h] with ω hω
      simp only [zero_smul, Pi.zero_apply, sub_zero, add_zero, hπ₂]
      exact hω.symm
    have ha2 : StronglyAdapted CS.𝓕 π₂ := fun t =>
      (measurable_cc_shock (t := t) le_rfl).stronglyMeasurable
    have hb2 : CS.BddProc π₂ := ⟨1, fun t => Eventually.of_forall fun ω => abs_cc_le _⟩
    have := (h 0 0 hz hzb hz hzb).2 0 π₂ hsol0 hsol2 hz ha2 hzb hb2 1
    exact cc_not_ae_zero (this.symm.trans (Eventually.of_forall fun _ => rfl))
  · have hiid := iid_existsUnique_iff coin_mean coin_var one_pos coin_bdd φπ⁻¹
    have habs : |φπ⁻¹| < 1 ↔ 1 < |φπ| := by
      rw [abs_inv]
      exact inv_lt_one₀ (abs_pos.mpr hφ)
    rw [← habs, ← hiid]
    constructor
    · intro h u hua hub
      have hra : StronglyAdapted CS.𝓕 (fun t => φπ • u t) := fun t => (hua t).const_smul φπ
      obtain ⟨M, hM⟩ := hub
      have hrb : CS.BddProc (fun t => φπ • u t) := ⟨|φπ| * M, fun t => by
        filter_upwards [hM t] with ω hω
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left hω (abs_nonneg _)⟩
      have hz : StronglyAdapted CS.𝓕 (0 : ℕ → (ℕ → ℝ) → ℝ) := fun _ => stronglyMeasurable_zero
      have hzb : CS.BddProc (0 : ℕ → (ℕ → ℝ) → ℝ) := ⟨0, fun _ => Eventually.of_forall
        fun _ => by simp⟩
      have hu : (fun t => φπ⁻¹ • ((fun t => φπ • u t) t - (0 : ℕ → (ℕ → ℝ) → ℝ) t)) = u := by
        funext t ω
        simp only [Pi.zero_apply, sub_zero, Pi.smul_apply, smul_eq_mul]
        field_simp
      obtain ⟨⟨π, hπ, hπa, hπb⟩, hun⟩ := h _ 0 hra hrb hz hzb
      refine ⟨⟨π, ?_, hπa, hπb⟩, fun z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂ => ?_⟩
      · have := (eq26M_iff_solves CS hφ).mp hπ
        rwa [hu] at this
      · refine hun z₁ z₂ ?_ ?_ ha₁ ha₂ hb₁ hb₂
        · rw [eq26M_iff_solves CS hφ, hu]
          exact h₁
        · rw [eq26M_iff_solves CS hφ, hu]
          exact h₂
    · intro h r ib hra hrb hia hib
      have hua : StronglyAdapted CS.𝓕 (fun t => φπ⁻¹ • (r t - ib t)) := fun t =>
        ((hra t).sub (hia t)).const_smul _
      obtain ⟨Mr, hMr⟩ := hrb
      obtain ⟨Mi, hMi⟩ := hib
      have hub : CS.BddProc (fun t => φπ⁻¹ • (r t - ib t)) := ⟨|φπ⁻¹| * (Mr + Mi), fun t => by
        filter_upwards [hMr t, hMi t] with ω h1 h2
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2))
          (abs_nonneg _)⟩
      obtain ⟨⟨π, hπ, hπa, hπb⟩, hun⟩ := h _ hua hub
      refine ⟨⟨π, (eq26M_iff_solves CS hφ).mpr hπ, hπa, hπb⟩,
        fun z₁ z₂ h₁ h₂ ha₁ ha₂ hb₁ hb₂ => hun z₁ z₂ ((eq26M_iff_solves CS hφ).mp h₁)
          ((eq26M_iff_solves CS hφ).mp h₂) ha₁ ha₂ hb₁ hb₂⟩

/-- Cochrane (2023), §2.6, pp. 39–40 ("no Taylor principle needed"), against Woodford (2003),
Proposition 2.6, **on a genuine probability space**: for `|θ| ≤ 1` the rule fails Woodford's
determinacy criterion in the coin economy, yet the fiscal-theory model (2.20)–(2.22) has, for
every adapted integrable disturbance, every shock and every integrable `π_0` known at `0`, a
solution that is unique almost surely (`TidyR5MeasLinear.mRule_linear_existsUnique`).
Restates `Links.taylor_contrast` on a genuine probability space. -/
theorem taylor_contrast_meas {θ : ℝ} (hθ : |θ| ≤ 1) :
    ¬ DetCrit θ ∧
      ∀ (u ε : ℕ → (ℕ → ℝ) → ℝ) (π0 : (ℕ → ℝ) → ℝ),
        StronglyAdapted (iidSystem coin).𝓕 u → (∀ t, Integrable (u t) (iidSystem coin).μ) →
        MIsShock (iidSystem coin) ε → StronglyMeasurable[(iidSystem coin).𝓕 0] π0 →
        Integrable π0 (iidSystem coin).μ →
        ∀ q : (ℕ → (ℕ → ℝ) → ℝ) × (ℕ → (ℕ → ℝ) → ℝ),
          StronglyAdapted (iidSystem coin).𝓕 q.1 →
          (∀ t, Integrable (q.1 t) (iidSystem coin).μ) → q.1 0 =ᵐ[(iidSystem coin).μ] π0 →
          MRuleModel (iidSystem coin) θ q.2 u ε q.1 →
          ∀ t, q.1 t =ᵐ[(iidSystem coin).μ] LinearFTMP.ruleSol θ u ε π0 t :=
  ⟨fun h => absurd ((prop_2_6_meas θ).mp h) (not_lt.mpr hθ),
    fun _ _ _ hu hui hε h0 h0i q hπ hπi hπ0 hm t =>
      ((mRule_linear_existsUnique (iidSystem coin) θ hu hui hε h0 h0i).2 q hπ hπi hπ0 hm t).1⟩

/-- Woodford (2003), App. A, p. 637 (restated), used for Cochrane (2023), §2.6: the sunspot
inflation paths `π_0 = 0`, `π_{t+1} = θπ_t + σ c(ε_{t+1})` on the coin economy.
Restates `Links.sunspotInfl` on a genuine probability space. -/
noncomputable def sunπ (θ σ : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => θ * sunπ θ σ t ω + σ * cc (ω (t + 1))

/-- Woodford (2003), Proposition 2.6 (restated), used for Cochrane (2023), §2.6: the set of
bounded adapted solutions of (2.6) with `r̂ = ī = 0` and `π_0 = 0`, on the coin economy. -/
def WTaylor (θ : ℝ) : Set (ℕ → (ℕ → ℝ) → ℝ) :=
  {π | StronglyAdapted (iidSystem coin).𝓕 π ∧ (iidSystem coin).BddProc π ∧
    Eq26M (iidSystem coin) θ 0 0 π ∧ π 0 = 0}

/-- Woodford (2003), App. A (restated): the sunspot inflation paths are adapted. -/
theorem sunπ_adapted (θ σ : ℝ) : StronglyAdapted (iidSystem coin).𝓕 (sunπ θ σ) := by
  intro t
  induction t with
  | zero => exact stronglyMeasurable_const
  | succ t ih =>
    exact (((ih.mono ((iidSystem coin).𝓕.mono (Nat.le_succ t))).measurable.const_mul θ).add
      (measurable_const.mul (measurable_cc_shock le_rfl))).stronglyMeasurable

/-- Woodford (2003), App. A (restated): for `|θ| < 1` the sunspot paths are bounded by
`|σ|/(1 − |θ|)` in every state.
Restates `Links.sunspotInfl_bounded` on a genuine probability space. -/
theorem sunπ_bdd {θ σ : ℝ} (hθ : |θ| < 1) (t : ℕ) (ω : ℕ → ℝ) :
    |sunπ θ σ t ω| ≤ |σ| / (1 - |θ|) := by
  have h1 : 0 < 1 - |θ| := by linarith
  have hK : 0 ≤ |σ| / (1 - |θ|) := div_nonneg (abs_nonneg σ) h1.le
  induction t with
  | zero => simpa [sunπ] using hK
  | succ t ih =>
    change |θ * sunπ θ σ t ω + σ * cc (ω (t + 1))| ≤ _
    have hKe : |σ| / (1 - |θ|) * (1 - |θ|) = |σ| := div_mul_cancel₀ _ h1.ne'
    calc |θ * sunπ θ σ t ω + σ * cc (ω (t + 1))|
        ≤ |θ| * |sunπ θ σ t ω| + |σ| * |cc (ω (t + 1))| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ |θ| * (|σ| / (1 - |θ|)) + |σ| * 1 := by
          gcongr
          exact abs_cc_le _
      _ = |σ| / (1 - |θ|) := by nlinarith

/-- Woodford (2003), Proposition 2.6 (restated) on the coin economy: for `|θ| < 1` every sunspot
path is a bounded adapted solution of (2.6) with `π_0 = 0`.
Restates `Links.sunspotInfl_solves` on a genuine probability space. -/
theorem sunπ_mem {θ : ℝ} (hθ : |θ| < 1) (σ : ℝ) : sunπ θ σ ∈ WTaylor θ := by
  refine ⟨sunπ_adapted θ σ, ⟨_, fun t => Eventually.of_forall (sunπ_bdd hθ t)⟩, fun t => ?_, rfl⟩
  have hi : Integrable (sunπ θ σ t) (iidSystem coin).μ :=
    MeasExpectationSystem.BddRV.integrable (MeasExpectationSystem.BddRV.of_stronglyMeasurable
      (sunπ_adapted θ σ t) (Eventually.of_forall (sunπ_bdd hθ t)))
  have hci : Integrable (fun ω : ℕ → ℝ => σ * cc (ω (t + 1))) (iidSystem coin).μ :=
    Integrable.of_bound (C := |σ|) ((measurable_const.mul (measurable_cc.comp
      (measurable_pi_apply (t + 1)))).aestronglyMeasurable) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [abs_cc_le (ω (t + 1)), abs_nonneg σ])
  have e : sunπ θ σ (t + 1) = θ • sunπ θ σ t + fun ω => σ * cc (ω (t + 1)) := rfl
  have hc := E_cc t 0 σ
  simp only [zero_add] at hc
  filter_upwards [(iidSystem coin).E_add (hi.smul θ) hci t, hc] with ω h1 h2
  rw [e]
  simp only [Pi.add_apply, Pi.zero_apply, sub_zero, add_zero]
  rw [h1, Pi.add_apply, h2,
    (iidSystem coin).E_of_stronglyMeasurable ((sunπ_adapted θ σ t).const_smul θ) (hi.smul θ)]
  simp

/-- Cochrane (2023), §2.6, against Woodford (2003), Proposition 2.6, **on a genuine probability
space**: in the i.i.d. coin economy with no disturbances, `|θ| < 1` and `π_0 = 0`, Woodford's
(2.6) has uncountably many bounded solutions even up to null sets (the sunspots `sunπ θ σ`,
pairwise different with positive probability, and no countable family matches all of them almost
surely at date `1`), while the fiscal-theory rule model with no fiscal shock has exactly one
solution, `π = 0` almost surely, which is one of Woodford's.
Restates `Links.taylor_contrast_coin` on a genuine probability space. -/
theorem taylor_contrast_coin_meas {θ : ℝ} (hθ : |θ| < 1) :
    (∀ σ, sunπ θ σ ∈ WTaylor θ) ∧
      (∀ σ σ', σ ≠ σ' → ¬ sunπ θ σ 1 =ᵐ[(iidSystem coin).μ] sunπ θ σ' 1) ∧
      (¬ ∃ C : Set (ℕ → (ℕ → ℝ) → ℝ), C.Countable ∧
        ∀ π ∈ WTaylor θ, ∃ Q ∈ C, π 1 =ᵐ[(iidSystem coin).μ] Q 1) ∧
      (∀ π i : ℕ → (ℕ → ℝ) → ℝ, StronglyAdapted (iidSystem coin).𝓕 π →
        (∀ t, Integrable (π t) (iidSystem coin).μ) → π 0 =ᵐ[(iidSystem coin).μ] 0 →
        MRuleModel (iidSystem coin) θ i 0 0 π → ∀ t, π t =ᵐ[(iidSystem coin).μ] 0) ∧
      (0 : ℕ → (ℕ → ℝ) → ℝ) ∈ WTaylor θ := by
  set CS := iidSystem coin
  have hdist : ∀ σ σ', σ ≠ σ' → ¬ sunπ θ σ 1 =ᵐ[CS.μ] sunπ θ σ' 1 := fun σ σ' h he => by
    apply cc_mul_ne h
    filter_upwards [he] with ω hω
    have e1 : sunπ θ σ 1 ω = σ * cc (ω 1) := by simp [sunπ]
    have e2 : sunπ θ σ' 1 ω = σ' * cc (ω 1) := by simp [sunπ]
    rw [← e1, ← e2]
    exact hω
  have hzS : MIsShock CS (0 : ℕ → (ℕ → ℝ) → ℝ) :=
    ⟨fun _ => stronglyMeasurable_zero, fun _ => integrable_zero _ _ _,
      fun t => by simp only [Pi.zero_apply]; rw [CS.E_zero]⟩
  have hz : StronglyAdapted CS.𝓕 (0 : ℕ → (ℕ → ℝ) → ℝ) := fun _ => stronglyMeasurable_zero
  have hrs0 : ∀ t, LinearFTMP.ruleSol θ (0 : ℕ → (ℕ → ℝ) → ℝ) 0 0 t = 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change θ • LinearFTMP.ruleSol θ (0 : ℕ → (ℕ → ℝ) → ℝ) 0 0 t +
        (0 : ℕ → (ℕ → ℝ) → ℝ) t - (0 : ℕ → (ℕ → ℝ) → ℝ) (t + 1) = 0
      rw [ih]
      simp
  refine ⟨fun σ => sunπ_mem hθ σ, hdist, ?_, fun π i hπ hπi hπ0 hm t => ?_, ?_⟩
  · rintro ⟨C, hC, hcov⟩
    have hg : ∀ σ : ℝ, ∃ Q : C, sunπ θ σ 1 =ᵐ[CS.μ] Q.1 1 := fun σ => by
      obtain ⟨Q, hQ, h⟩ := hcov _ (sunπ_mem hθ σ)
      exact ⟨⟨Q, hQ⟩, h⟩
    choose g hgs using hg
    have hinj : Function.Injective g := by
      intro σ σ' he
      by_contra hne
      exact hdist σ σ' hne ((hgs σ).trans ((congrArg (fun Q : C => Q.1 1) he) ▸ (hgs σ').symm))
    have : Countable C := hC.to_subtype
    have : Countable ℝ := hinj.countable
    exact Cardinal.not_countable_real Set.countable_univ
  · have h := ((mRule_linear_existsUnique CS θ hz (fun _ => integrable_zero _ _ _) hzS
      stronglyMeasurable_zero (integrable_zero _ _ _)).2 (π, i) hπ hπi hπ0 hm t).1
    rw [hrs0] at h
    exact h
  · refine ⟨hz, ⟨0, fun _ => Eventually.of_forall fun _ => by simp⟩, fun t => ?_, rfl⟩
    simp only [smul_zero, Pi.zero_apply, sub_zero, add_zero]
    rw [CS.E_zero]

/-! ### Woodford's (4.2) and passive fiscal policy -/

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-- Woodford (2003), §1, p. 66 (restated from `Links.discount`) state by state, used for
Cochrane (2023), p. 39: the stochastic discount factor `Q_{t,T} = ∏_{s=t}^{T−1} q_s`. -/
def mDiscount (q : ℕ → Ω → ℝ) (t T : ℕ) (ω : Ω) : ℝ := ∏ s ∈ Finset.Ico t T, q s ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 39, against Woodford (2003), §1: state by state the discount factor
`mDiscount` is the core `Links.discount` of the path. -/
theorem mDiscount_eq_discount (q : ℕ → Ω → ℝ) (t T' : ℕ) (ω : Ω) :
    mDiscount q t T' ω = Links.discount (fun s => q s ω) t T' := rfl

/-- Woodford (2003), (4.2), p. 124 (restated) **on a probability space**, used for Cochrane
(2023), p. 39: under the Ricardian rule `T_t = αW_t − Δ_tM_t` (`0 < α ≤ 1`) and the government
budget in every state, the transversality condition `Q_{t,T}W_T → 0` holds along every path, and,
for wealth `W_t` known at `t` and integrable, in conditional expectation:
`E_t[Q_{t,T}W_T] → 0` almost surely.
Restates `Links.ricardian_tvc` on a genuine probability space. -/
theorem mRicardian_tvc {q W Tx Δ M : ℕ → Ω → ℝ} {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hgov : ∀ s ω, q s ω * W (s + 1) ω = W s ω - Tx s ω - Δ s ω * M s ω)
    (hrule : ∀ s ω, Tx s ω = α * W s ω - Δ s ω * M s ω) (t : ℕ)
    (hW : StronglyMeasurable[S.𝓕 t] (W t)) (hWi : Integrable (W t) S.μ) :
    (∀ ω, Tendsto (fun T => mDiscount q t T ω * W T ω) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂S.μ, Tendsto (fun T => S.E t (fun ω => mDiscount q t T ω * W T ω) ω) atTop (𝓝 0) := by
  have hpath : ∀ ω n, mDiscount q t (t + n) ω * W (t + n) ω = (1 - α) ^ n * W t ω :=
    fun ω n => Links.ricardian_discounted (q := fun s => q s ω) (W := fun s => W s ω)
      (Tx := fun s => Tx s ω) (Δ := fun s => Δ s ω) (M := fun s => M s ω)
      (fun s => hgov s ω) (fun s => hrule s ω) t n
  refine ⟨fun ω => Links.ricardian_tvc (q := fun s => q s ω) (W := fun s => W s ω)
    (Tx := fun s => Tx s ω) (Δ := fun s => Δ s ω) (M := fun s => M s ω) hα0 hα1
    (fun s => hgov s ω) (fun s => hrule s ω) t, ?_⟩
  have hE : ∀ n, S.E t (fun ω => mDiscount q t (t + n) ω * W (t + n) ω) =ᵐ[S.μ]
      fun ω => (1 - α) ^ n * W t ω := fun n => by
    have e : (fun ω => mDiscount q t (t + n) ω * W (t + n) ω) = (1 - α) ^ n • W t := by
      funext ω
      rw [hpath ω n, Pi.smul_apply, smul_eq_mul]
    rw [e]
    filter_upwards [S.E_smul ((1 - α) ^ n) (W t) t] with ω h
    rw [h, Pi.smul_apply, S.E_of_stronglyMeasurable hW hWi, smul_eq_mul]
  filter_upwards [ae_all_iff.2 hE] with ω h
  refine (tendsto_add_atTop_iff_nat t).mp ?_
  have hlim : Tendsto (fun n : ℕ => (1 - α) ^ n * W t ω) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - α)
      (by linarith)).mul_const (W t ω)
  refine hlim.congr fun n => ?_
  rw [show n + t = t + n by ring, h n]

/-- Cochrane (2023), p. 39: the real-debt path `x_t = ((1 − α)/β)ᵗ x_0` of passive fiscal
policy. -/
noncomputable def passivePath (α β : ℝ) (x0 : Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ((1 - α) / β) ^ t * x0 ω

/-- Cochrane (2023), p. 39 (passive fiscal policy) via Woodford (2003), (4.2), **on a probability
space**: under the passive rule `s_t = α x_t` (`0 < α ≤ 1`, `β > 0`), for **every** initial real
debt `x_0` known at `0` and integrable, the path `passivePath` satisfies the flow condition
`x_t = s_t + β E_t x_{t+1}` and the valuation equation `x_t = PV_t` at every date: the valuation
equation no longer determines the price level `P_0 = B_{−1}/x_0`.
Restates `Links.passive_any_price` on a genuine probability space. -/
theorem mPassive_any_price {α β : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) {x0 : Ω → ℝ}
    (hx0 : StronglyMeasurable[S.𝓕 0] x0) (hx0i : Integrable x0 S.μ) (t : ℕ) :
    passivePath α β x0 t = (fun ω => α * passivePath α β x0 t ω +
        β * S.E t (passivePath α β x0 (t + 1)) ω) ∧
      passivePath α β x0 t = S.forwardSol β (fun k ω => α * passivePath α β x0 k ω) t := by
  have hsm : ∀ n, StronglyMeasurable[S.𝓕 n] (passivePath α β x0 t) ∧
      StronglyMeasurable[S.𝓕 n] (passivePath α β x0 (t + 1)) := fun n =>
    ⟨((hx0.mono (S.𝓕.mono (Nat.zero_le n))).const_mul _),
      ((hx0.mono (S.𝓕.mono (Nat.zero_le n))).const_mul _)⟩
  have hint : ∀ k, Integrable (passivePath α β x0 k) S.μ := fun k => hx0i.const_mul _
  have hg : β * ((1 - α) / β) = 1 - α := by field_simp
  refine ⟨?_, ?_⟩
  · rw [S.E_of_stronglyMeasurable (hsm t).2 (hint (t + 1))]
    funext ω
    simp only [passivePath, pow_succ]
    rw [show β * (((1 - α) / β) ^ t * ((1 - α) / β) * x0 ω) =
      (β * ((1 - α) / β)) * (((1 - α) / β) ^ t * x0 ω) by ring, hg]
    ring
  · have hd : MeasExpectationSystem.discSum β (fun k ω => α * passivePath α β x0 k ω) t =
        passivePath α β x0 t := by
      funext ω
      simp only [MeasExpectationSystem.discSum, passivePath]
      have e : ∀ k, β ^ k * (α * (((1 - α) / β) ^ (t + k) * x0 ω)) =
          (α * (((1 - α) / β) ^ t * x0 ω)) * (1 - α) ^ k := fun k => by
        rw [pow_add, show (1 - α) ^ k = (β * ((1 - α) / β)) ^ k by rw [hg], mul_pow]
        ring
      simp only [e]
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by linarith) (by linarith), sub_sub_cancel]
      have := hα0.ne'
      field_simp
    change _ = S.E t _
    rw [hd, S.E_of_stronglyMeasurable (hsm t).1 (hint t)]

/-- Cochrane (2023), eqs. (2.5)–(2.7), p. 22, the active case on a probability space,
contrasting `mPassive_any_price`: with exogenous bounded adapted surpluses and `0 < β < 1`, a
real-debt process satisfying the flow condition `x_t = s_t + β E_t x_{t+1}` and the
transversality condition `β^N E_t x_{t+N} → 0` almost surely equals the present value almost
surely at every date, so the valuation equation pins the price level.
Restates `Links.active_unique_value` on a genuine probability space. -/
theorem mActive_unique_value {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {s x : ℕ → Ω → ℝ}
    (hsad : StronglyAdapted S.𝓕 s) (hsM : ∀ t, ∀ᵐ ω ∂S.μ, |s t ω| ≤ M)
    (hflow : ∀ t, x t =ᵐ[S.μ] s t + β • S.E t (x (t + 1)))
    (htvc : ∀ t, ∀ᵐ ω ∂S.μ, Tendsto (fun N => β ^ N * S.E t (x (t + N)) ω) atTop (𝓝 0))
    (t : ℕ) : x t =ᵐ[S.μ] S.forwardSol β s t := by
  have ha : |β| < 1 := by rwa [abs_of_pos hβ0]
  have hsm : ∀ n, AEStronglyMeasurable (s n) S.μ := fun n =>
    ((hsad n).mono (S.𝓕.le n)).aestronglyMeasurable
  have hsi : ∀ n, Integrable (s n) S.μ := fun n =>
    MeasExpectationSystem.BddRV.integrable ⟨hsm n, M, hsM n⟩
  have htel := ae_all_iff.2 (HouseholdMeasureTVC.telescope_ae hflow hsad hsi t)
  filter_upwards [htel, htvc t, S.forwardSol_hasSum ha hsm hsM t] with ω h1 h2 h3
  have hlim1 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω)
      atTop (𝓝 (S.forwardSol β s t ω)) :=
    h3.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2' : Tendsto (fun N => β ^ (N + 1) * S.E t (x (t + N + 1)) ω) atTop (𝓝 0) :=
    h2.comp (tendsto_add_atTop_nat 1)
  have hlim2 : Tendsto (fun N => ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω)
      atTop (𝓝 (x t ω)) := by
    have e : ∀ N, ∑ j ∈ Finset.range (N + 1), β ^ j * S.E t (s (t + j)) ω =
        x t ω - β ^ (N + 1) * S.E t (x (t + N + 1)) ω := fun N => by
      rw [h1 N]
      ring
    simp_rw [e]
    simpa using (tendsto_const_nhds (x := x t ω)).sub h2'
  exact tendsto_nhds_unique hlim2 hlim1

/-! ### Links to the core versions on finite trees -/

namespace Link

open ExpectationsFiniteTree TreeBridge HouseholdMeasureTVC.Link TidyR5MeasLinear.Link

variable {Ω' : Type*} [Fintype Ω'] [MeasurableSpace Ω'] [DiscreteMeasurableSpace Ω']
  (T : FiniteTree Ω')

/-- Cochrane (2023), §2.6, against Woodford (2003), eq. (2.6): on a finite tree the almost-sure
(2.6) is the core `Links.Eq26`. -/
theorem tree_eq26M_iff (φπ : ℝ) (r ib π : ℕ → Ω' → ℝ) :
    Eq26M (treeSystem T) φπ r ib π ↔ Links.Eq26 T.toExpectationSystem φπ r ib π := by
  refine forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · have e := eq_of_ae T h
    rwa [treeE] at e
  · rw [h, treeE]

end Link

end Cochrane.IntertemporalModel.TidyR6MeasLinks
