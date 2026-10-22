/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR5UniformNull

/-!
# Genuinely independent disturbances

Woodford (2003), *Interest and Prices*, Chapter 7, §3.1, p. 512 ("other (independent)
disturbances"), eqs. (3.7)–(3.8), and Appendix F.4 (pp. 713–714).

NoninertialMeasure formalises the two disturbances of p. 512 through uncorrelated innovations,
`E_t(εᵘ_{t+1} εʳ_{t+1}) = 0`. Here independence itself is used.

## Main results

* `IndepInnov`: each date's innovation pair is independent of the information `𝓕_t`, and the two
  innovations are independent of each other (genuine independence, not a moment condition);
  `IndepDisturbances`: the processes `u` and `r̂ⁿ` are independent random elements of `ℝ^ℕ`.
* Independence implies the moment condition used in (3.7)–(3.8) (`condCov_zero_of_indep`,
  `indepInnov_uncorrelated`), so (3.7)–(3.8) and F.4 hold for independent disturbances
  (`lstab_eq_indep`, `f4_lstab_indep`, `f4_uniform_indep`).
* The two-coin economy of NoninertialMeasureIID (`ε_t` i.i.d. uniform on `{±1, ±3}`,
  `εᵘ_t = coinA(ε_t)`, `εʳ_t = coinB(ε_t)`) has genuinely independent disturbances: the
  coins are mutually independent over all dates and both coin families (`twoCoin_iIndepFun`),
  the innovations satisfy `IndepInnov` (`twoCoin_indepInnov`), and the disturbance processes are
  independent (`twoCoin_indepDisturbances`); F.4 follows from independence alone
  (`twoCoin_f4_indep`).
-/

namespace Woodford.GainsFromCommitment.TidyR5Independence

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID NoninertialMeasure NoninertialMeasureIID
open VarianceFrontier (plan2)
open Noninertial (uncondVar)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Independence implies the moment condition -/

/-- Woodford (2003), p. 512 ("independent disturbances"), with genuine independence: at every
date the innovation pair `(εᵘ_{t+1}, εʳ_{t+1})` is independent of the date-`t` information, and
`εᵘ_{t+1}` and `εʳ_{t+1}` are independent of each other. -/
def IndepInnov (εu εr : ℕ → Ω → ℝ) : Prop :=
  ∀ t, Indep (MeasurableSpace.comap (fun ω => (εu (t + 1) ω, εr (t + 1) ω)) inferInstance)
    (S.𝓕 t) S.μ ∧ IndepFun (εu (t + 1)) (εr (t + 1)) S.μ

/-- Woodford (2003), p. 512 ("independent disturbances"): the disturbance processes `u` and
`r̂ⁿ`, as random elements of `ℝ^ℕ`, are independent. -/
def IndepDisturbances (u r : ℕ → Ω → ℝ) : Prop :=
  IndepFun (fun ω t => u t ω) (fun ω t => r t ω) S.μ

/-- Woodford (2003), p. 512 (independence gives the conditional moment): if the pair `(X, Y)` is
independent of `𝓕_t`, `X` and `Y` are independent, `X` has mean zero and both are bounded and
measurable, then `E_t(X Y) = 0` almost surely. -/
theorem condCov_zero_of_indep (t : ℕ) {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXb : S.BddRV X) (hYb : S.BddRV Y)
    (hpast : Indep (MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance) (S.𝓕 t) S.μ)
    (hXY : IndepFun X Y S.μ) (hmean : ∫ ω, X ω ∂S.μ = 0) :
    S.E t (X * Y) =ᵐ[S.μ] fun _ => 0 := by
  have hle₁ : MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance ≤ mΩ :=
    (hX.prodMk hY).comap_le
  have hm : StronglyMeasurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (X * Y) := by
    have : Measurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
        ((fun p : ℝ × ℝ => p.1 * p.2) ∘ fun ω => (X ω, Y ω)) :=
      (measurable_fst.mul measurable_snd).comp (comap_measurable _)
    exact this.stronglyMeasurable
  have h := condExp_indep_eq hle₁ (S.𝓕.le t) hm hpast
  have hint : ∫ ω, (X * Y) ω ∂S.μ = 0 := by
    have := hXY.integral_mul_eq_mul_integral hXb.1 hYb.1
    simp only [Pi.mul_apply] at this ⊢
    rw [this, hmean, zero_mul]
  filter_upwards [h] with ω hω
  change S.μ[X * Y | S.𝓕 t] ω = 0
  rw [hω, hint]

/-- Woodford (2003), p. 512: for AR(1) disturbances with independent innovations (`IndepInnov`),
the innovations are conditionally uncorrelated, `E_t(εᵘ_{t+1} εʳ_{t+1}) = 0` — the hypothesis of
(3.7)–(3.8) and F.4 in NoninertialMeasure. -/
theorem indepInnov_uncorrelated {ρu ρr su sr : ℝ} {u εu r εr : ℕ → Ω → ℝ}
    (hu : MeasAR1Innov S ρu su u εu) (hr : MeasAR1Innov S ρr sr r εr)
    (hind : IndepInnov S εu εr) (t : ℕ) :
    S.E t (εu (t + 1) * εr (t + 1)) =ᵐ[S.μ] fun _ => 0 := by
  have mu : Measurable (εu (t + 1)) :=
    ((hu.innov_meas t).mono (S.𝓕.le (t + 1))).measurable
  have mr : Measurable (εr (t + 1)) :=
    ((hr.innov_meas t).mono (S.𝓕.le (t + 1))).measurable
  have hmean : ∫ ω, εu (t + 1) ω ∂S.μ = 0 := by
    rw [← S.integral_E t, integral_congr_ae (hu.2.2.2.1 t)]
    simp
  exact condCov_zero_of_indep S t mu mr (hu.innov_bddRV t) (hr.innov_bddRV t) (hind t).1
    (hind t).2 hmean

/-- **Equations (3.7)–(3.8) for independent disturbances** (Woodford (2003), p. 513): with
genuinely independent innovations, almost surely `L^stab = L^{stab,r} + L^{stab,u}`. -/
theorem lstab_eq_indep {β lx li ρu ρr su sr : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρu : |ρu| < 1)
    (hρr : |ρr| < 1) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr) (hind : IndepInnov S εu εr)
    (πbar xbar ibar fπ fx fi gπ gx gi : ℝ) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
      (plan2 ibar fi gi u r) ω =
      β / (1 - β) * ((1 - ρr ^ 2) / (1 - β * ρr ^ 2)) * (gπ ^ 2 + lx * gx ^ 2 + li * gi ^ 2) *
          uncondVar ρr sr +
        β / (1 - β) * ((1 - ρu ^ 2) / (1 - β * ρu ^ 2)) * (fπ ^ 2 + lx * fx ^ 2 + li * fi ^ 2) *
          uncondVar ρu su :=
  lstab_eq S hβ0 hβ1 hρu hρr hu hr (indepInnov_uncorrelated S hu hr hind) πbar xbar ibar fπ fx
    fi gπ gx gi t₀

/-- **Appendix F.4 for independent disturbances** (Woodford (2003), pp. 512–513, 713–714): with
genuinely independent innovations (`IndepInnov`), the corrected optimal noninertial plan satisfies
(2.1) and (2.23), and every plan (3.6) satisfying them has almost surely a stabilization loss at
least as large, with almost-sure equality iff it has the F.4 responses. -/
theorem f4_lstab_indep {β κ σ rbar lx li istar ρu ρr su sr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1) (hρr : |ρr| < 1)
    (hsu : 0 < su) (hsr : 0 < sr) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr) (hind : IndepInnov S εu εr) (t₀ : ℕ) {xs is : ℝ}
    (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    (MAS S β κ (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
        (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r) u ∧
      MIS S σ (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
        (Noninertial.piRF4 β κ σ lx li ρr) u r)
        (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
        (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r)
        (fun t ω => rbar + r t ω)) ∧
    ∀ πbar xbar ibar fπ fx fi gπ gx gi,
      MAS S β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u →
      MIS S σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
        (fun t ω => rbar + r t ω) →
      (∀ᵐ ω ∂S.μ, mLstab S β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ω ≤
        mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
          (plan2 ibar fi gi u r) ω) ∧
      (mLstab S β lx li t₀ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r)
          (plan2 ibar fi gi u r) =ᵐ[S.μ]
        mLstab S β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) u r)
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr) u r)
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr) u r) ↔
        (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) :=
  f4_lstab S hβ0 hβ1 hκ hσ hlx hli hρu hρr hsu hsr hu hr
    (indepInnov_uncorrelated S hu hr hind) t₀ hxs his

/-- **Appendix F.4 for independent disturbances, off one null set** (Woodford (2003),
pp. 512–513, 713–714; `TidyR5UniformNull.f4_uniform`): with genuinely independent innovations,
one null set serves every plan (3.6) satisfying (2.1) and (2.23). -/
theorem f4_uniform_indep {β κ σ rbar lx li ρu ρr su sr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1) (hρr : |ρr| < 1)
    (hsu : 0 < su) (hsr : 0 < sr) {u εu r εr : ℕ → Ω → ℝ} (hu : MeasAR1Innov S ρu su u εu)
    (hr : MeasAR1Innov S ρr sr r εr) (hind : IndepInnov S εu εr) (t₀ : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ πbar xbar ibar fπ fx fi gπ gx gi : ℝ,
      MAS S β κ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) u →
      MIS S σ (plan2 πbar fπ gπ u r) (plan2 xbar fx gx u r) (plan2 ibar fi gi u r)
        (fun t ω => rbar + r t ω) →
      TidyR5UniformNull.regLstab S β lx li ρu ρr u r t₀ (Noninertial.piUF4 β κ σ lx li ρu)
          (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.iUF4 β κ σ lx li ρu)
          (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
          (Noninertial.iRF4 β κ σ lx li ρr) ω ≤
        TidyR5UniformNull.regLstab S β lx li ρu ρr u r t₀ fπ fx fi gπ gx gi ω ∧
      (TidyR5UniformNull.regLstab S β lx li ρu ρr u r t₀ fπ fx fi gπ gx gi ω =
          TidyR5UniformNull.regLstab S β lx li ρu ρr u r t₀ (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.iUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) (Noninertial.xRF4 β κ σ lx li ρr)
            (Noninertial.iRF4 β κ σ lx li ρr) ω ↔
        (fπ = Noninertial.piUF4 β κ σ lx li ρu ∧ fx = Noninertial.xUF4 β κ σ lx li ρu ∧
          fi = Noninertial.iUF4 β κ σ lx li ρu) ∧
        (gπ = Noninertial.piRF4 β κ σ lx li ρr ∧ gx = Noninertial.xRF4 β κ σ lx li ρr ∧
          gi = Noninertial.iRF4 β κ σ lx li ρr)) :=
  TidyR5UniformNull.f4_uniform S hβ0 hβ1 hκ hσ hlx hli hρu hρr hsu hsr hu hr
    (indepInnov_uncorrelated S hu hr hind) t₀


/-! ### The two-coin economy has genuinely independent disturbances -/

/-- Woodford (2003), p. 512 (concrete law): the coins indexed by date and type,
`coinFam (t, true) = coinA(ε_t)` (the cost-push innovation) and `coinFam (t, false) =
coinB(ε_t)` (the natural-rate innovation). -/
noncomputable def coinFam (p : ℕ × Bool) (ω : ℕ → ℝ) : ℝ :=
  cond p.2 (coinA (ω p.1)) (coinB (ω p.1))

/-- Woodford (2003), p. 512 (concrete law): each coin is measurable. -/
theorem measurable_coinFam (p : ℕ × Bool) : Measurable (coinFam p) := by
  obtain ⟨t, b⟩ := p
  cases b
  · exact measurable_coinB.comp (measurable_pi_apply t)
  · exact measurable_coinA.comp (measurable_pi_apply t)

/-- Woodford (2003), p. 512 (concrete law): the date-`t` shock has law `NoninertialMeasureIID.quad`.
-/
theorem twoCoin_eval (t : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    (iidSystem quad).μ ((fun ω : ℕ → ℝ => ω t) ⁻¹' A) = (quad : Measure ℝ) A := by
  change (Measure.infinitePi (fun _ => (quad : Measure ℝ))) _ = _
  rw [← Measure.map_apply (by fun_prop) hA, Measure.infinitePi_map_eval]

/-- Woodford (2003), p. 512 (concrete law): `quad(A) = (1_A(3) + 1_A(1) + 1_A(−1) + 1_A(−3))/4`. -/
theorem quad_apply {A : Set ℝ} (hA : MeasurableSet A) :
    (quad : Measure ℝ) A =
      4⁻¹ * (A.indicator 1 3 + A.indicator 1 1 + A.indicator 1 (-1) + A.indicator 1 (-3)) := by
  change quadMeasure A = _
  simp only [quadMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply' _ hA,
    smul_eq_mul]

/-- Woodford (2003), p. 512 (concrete law): under `NoninertialMeasureIID.quad` the two coins are
independent: `quad(coinA ∈ s, coinB ∈ s') = quad(coinA ∈ s) quad(coinB ∈ s')`. -/
theorem quad_coins_indep {s s' : Set ℝ} (hs : MeasurableSet s) (hs' : MeasurableSet s') :
    (quad : Measure ℝ) (coinA ⁻¹' s ∩ coinB ⁻¹' s') =
      (quad : Measure ℝ) (coinA ⁻¹' s) * (quad : Measure ℝ) (coinB ⁻¹' s') := by
  rw [quad_apply ((measurable_coinA hs).inter (measurable_coinB hs')),
    quad_apply (measurable_coinA hs), quad_apply (measurable_coinB hs')]
  have a3 : coinA 3 = 1 := by norm_num [coinA]
  have a1 : coinA 1 = 1 := by norm_num [coinA]
  have am1 : coinA (-1) = -1 := by norm_num [coinA]
  have am3 : coinA (-3) = -1 := by norm_num [coinA]
  have b3 : coinB 3 = 1 := by norm_num [coinB]
  have b1 : coinB 1 = -1 := by norm_num [coinB]
  have bm1 : coinB (-1) = 1 := by norm_num [coinB]
  have bm3 : coinB (-3) = -1 := by norm_num [coinB]
  classical
  simp only [Set.indicator, Set.mem_inter_iff, Set.mem_preimage, a3, a1, am1, am3, b3, b1, bm1,
    bm3, Pi.one_apply]
  by_cases h1 : (1 : ℝ) ∈ s <;> by_cases h2 : (-1 : ℝ) ∈ s <;> by_cases h3 : (1 : ℝ) ∈ s' <;>
    by_cases h4 : (-1 : ℝ) ∈ s' <;>
    simp only [h1, h2, h3, h4, and_self, and_true, and_false, ite_true, ite_false] <;>
    rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)] <;>
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] <;>
    norm_num

/-- Woodford (2003), p. 512 (concrete law): finsets of `Bool` (tool). -/
theorem finset_bool_cases (T : Finset Bool) :
    T = ∅ ∨ T = {true} ∨ T = {false} ∨ T = {true, false} := by
  by_cases ht : true ∈ T <;> by_cases hf : false ∈ T
  · right; right; right; ext b; cases b <;> simp [ht, hf]
  · right; left; ext b; cases b <;> simp [ht, hf]
  · right; right; left; ext b; cases b <;> simp [ht, hf]
  · left; ext b; cases b <;> simp [ht, hf]

/-- **The two coins are genuinely independent** (Woodford (2003), p. 512): on the two-coin economy
the whole family `coinFam` — both coins at every date — is mutually independent. -/
theorem twoCoin_iIndepFun : iIndepFun coinFam (iidSystem quad).μ := by
  have h1 : iIndepFun (fun t (ω : ℕ → ℝ) => fun j : Bool => cond j (coinA (ω t)) (coinB (ω t)))
      (iidSystem quad).μ :=
    iIndepFun_infinitePi (P := fun _ => (quad : Measure ℝ))
      (X := fun _ (x : ℝ) (j : Bool) => cond j (coinA x) (coinB x))
      (fun _ => measurable_pi_iff.mpr fun j => by
        cases j
        · exact measurable_coinB
        · exact measurable_coinA)
  have h2 : ∀ t, iIndepFun (fun (j : Bool) (ω : ℕ → ℝ) => cond j (coinA (ω t)) (coinB (ω t)))
      (iidSystem quad).μ := by
    intro t
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro T sets H
    rcases finset_bool_cases T with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp
    · have ht := H true (by simp)
      have hf := H false (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton, Set.iInter_iInter_eq_or_left,
        Set.iInter_iInter_eq_left, Finset.prod_insert (by decide : true ∉ ({false} : Finset Bool)),
        Finset.prod_singleton, Bool.cond_true, Bool.cond_false]
      have e1 : (fun ω : ℕ → ℝ => coinA (ω t)) ⁻¹' sets true ∩
          (fun ω : ℕ → ℝ => coinB (ω t)) ⁻¹' sets false =
          (fun ω : ℕ → ℝ => ω t) ⁻¹' (coinA ⁻¹' sets true ∩ coinB ⁻¹' sets false) := rfl
      have e2 : (fun ω : ℕ → ℝ => coinA (ω t)) ⁻¹' sets true =
          (fun ω : ℕ → ℝ => ω t) ⁻¹' (coinA ⁻¹' sets true) := rfl
      have e3 : (fun ω : ℕ → ℝ => coinB (ω t)) ⁻¹' sets false =
          (fun ω : ℕ → ℝ => ω t) ⁻¹' (coinB ⁻¹' sets false) := rfl
      rw [e1, e2, e3, twoCoin_eval t ((measurable_coinA ht).inter (measurable_coinB hf)),
        twoCoin_eval t (measurable_coinA ht), twoCoin_eval t (measurable_coinB hf)]
      exact quad_coins_indep ht hf
  exact iIndepFun_uncurry' (X := fun t j (ω : ℕ → ℝ) => cond j (coinA (ω t)) (coinB (ω t)))
    (fun t j => measurable_coinFam (t, j)) h1 h2

/-- Woodford (2003), p. 512: the innovations of the two-coin economy satisfy `IndepInnov`: each
date's pair of coins is independent of the past, and the two coins are independent. -/
theorem twoCoin_indepInnov : IndepInnov (iidSystem quad) (fnShock coinA) (fnShock coinB) := by
  intro t
  refine ⟨indep_of_indep_of_le_left (indep_future quad t) ?_, ?_⟩
  · have hm : Measurable[coordSigma (t + 1)]
        (fun ω : ℕ → ℝ => (fnShock coinA (t + 1) ω, fnShock coinB (t + 1) ω)) :=
      (measurable_coinA.prodMk measurable_coinB).comp
        (comap_measurable (fun ω : ℕ → ℝ => ω (t + 1)))
    exact hm.comap_le.trans (le_iSup₂ (f := fun j (_ : j ∈ Set.Ioi t) => coordSigma j) (t + 1)
      (Set.mem_Ioi.mpr (Nat.lt_succ_self t)))
  · exact twoCoin_iIndepFun.indepFun (i := (t + 1, true)) (j := (t + 1, false)) (by simp)

/-- Woodford (2003), p. 512 (concrete law): the σ-algebra generated by all the coins of one type
(`true`: the cost-push coins `coinA(ε_t)`; `false`: the natural-rate coins `coinB(ε_t)`). -/
noncomputable abbrev coinSigma (b : Bool) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ p ∈ {p : ℕ × Bool | p.2 = b}, MeasurableSpace.comap (coinFam p) inferInstance

/-- **Genuinely independent disturbances** (Woodford (2003), p. 512): on the two-coin economy the
cost-push process `u = ar1fn ρ_u coinA` and the natural-rate process `r̂ⁿ = ar1fn ρ_r coinB` are
independent random elements of `ℝ^ℕ` (for all persistences). -/
theorem twoCoin_indepDisturbances (ρu ρr : ℝ) :
    IndepDisturbances (iidSystem quad) (ar1fn ρu coinA) (ar1fn ρr coinB) := by
  have hle : ∀ p, MeasurableSpace.comap (coinFam p) inferInstance ≤ MeasurableSpace.pi :=
    fun p => (measurable_coinFam p).comap_le
  have hD := indep_iSup_of_disjoint hle twoCoin_iIndepFun.iIndep
    (S := {p : ℕ × Bool | p.2 = true}) (T := {p : ℕ × Bool | p.2 = false})
    (Set.disjoint_left.2 fun p h1 h2 => by simp_all)
  have cA : ∀ t, Measurable[coinSigma true] (fnShock coinA t) := fun t =>
    (comap_measurable (coinFam (t, true))).mono
      (le_iSup₂ (f := fun p (_ : p ∈ {p : ℕ × Bool | p.2 = true}) =>
        MeasurableSpace.comap (coinFam p) (inferInstance : MeasurableSpace ℝ)) (t, true) rfl)
      le_rfl
  have cB : ∀ t, Measurable[coinSigma false] (fnShock coinB t) := fun t =>
    (comap_measurable (coinFam (t, false))).mono
      (le_iSup₂ (f := fun p (_ : p ∈ {p : ℕ × Bool | p.2 = false}) =>
        MeasurableSpace.comap (coinFam p) (inferInstance : MeasurableSpace ℝ)) (t, false) rfl)
      le_rfl
  have hA : ∀ t, Measurable[coinSigma true] (ar1fn ρu coinA t) := by
    intro t
    induction t with
    | zero => exact cA 0
    | succ t ih => rw [ar1fn_succ]; exact (ih.const_smul ρu).add (cA (t + 1))
  have hB : ∀ t, Measurable[coinSigma false] (ar1fn ρr coinB t) := by
    intro t
    induction t with
    | zero => exact cB 0
    | succ t ih => rw [ar1fn_succ]; exact (ih.const_smul ρr).add (cB (t + 1))
  have pA : MeasurableSpace.comap (fun ω t => ar1fn ρu coinA t ω) MeasurableSpace.pi ≤
      coinSigma true := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    exact iSup_le fun t => (hA t).comap_le
  have pB : MeasurableSpace.comap (fun ω t => ar1fn ρr coinB t ω) MeasurableSpace.pi ≤
      coinSigma false := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    exact iSup_le fun t => (hB t).comap_le
  unfold IndepDisturbances
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hD pA) pB

/-- **Appendix F.4 with genuinely independent disturbances** (Woodford (2003), pp. 512–513,
713–714) on the two-coin economy: derived from independence (`twoCoin_indepInnov`) rather than
from moments; the disturbances are independent processes (`twoCoin_indepDisturbances`). Every plan
(3.6) satisfying (2.1) and (2.23) has almost surely a stabilization loss at least that of the
corrected optimal noninertial plan, with almost-sure equality iff it has the F.4 responses. -/
theorem twoCoin_f4_indep {β κ σ rbar lx li istar ρu ρr : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hκ : 0 < κ) (hσ : 0 < σ) (hlx : 0 < lx) (hli : 0 ≤ li) (hρu : |ρu| < 1) (hρr : |ρr| < 1)
    (t₀ : ℕ) {xs is : ℝ} (hxs : xs = (1 - β) / κ * Noninertial.piBar119 β li rbar istar)
    (his : is = rbar + Noninertial.piBar119 β li rbar istar) :
    IndepDisturbances (iidSystem quad) (ar1fn ρu coinA) (ar1fn ρr coinB) ∧
    ∀ πbar xbar ibar fπ fx fi gπ gx gi,
      MAS (iidSystem quad) β κ (plan2 πbar fπ gπ (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 xbar fx gx (ar1fn ρu coinA) (ar1fn ρr coinB)) (ar1fn ρu coinA) →
      MIS (iidSystem quad) σ (plan2 πbar fπ gπ (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 xbar fx gx (ar1fn ρu coinA) (ar1fn ρr coinB))
        (plan2 ibar fi gi (ar1fn ρu coinA) (ar1fn ρr coinB))
        (fun t ω => rbar + ar1fn ρr coinB t ω) →
      ∀ᵐ ω ∂(iidSystem quad).μ, mLstab (iidSystem quad) β lx li t₀
          (plan2 (Noninertial.piBar119 β li rbar istar) (Noninertial.piUF4 β κ σ lx li ρu)
            (Noninertial.piRF4 β κ σ lx li ρr) (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 xs (Noninertial.xUF4 β κ σ lx li ρu) (Noninertial.xRF4 β κ σ lx li ρr)
            (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 is (Noninertial.iUF4 β κ σ lx li ρu) (Noninertial.iRF4 β κ σ lx li ρr)
            (ar1fn ρu coinA) (ar1fn ρr coinB)) ω ≤
        mLstab (iidSystem quad) β lx li t₀ (plan2 πbar fπ gπ (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 xbar fx gx (ar1fn ρu coinA) (ar1fn ρr coinB))
          (plan2 ibar fi gi (ar1fn ρu coinA) (ar1fn ρr coinB)) ω := by
  obtain ⟨hA, hB, hAA, hBB, -, -, -⟩ := quad_moments
  have hu := iid_measAR1Innov_fn (ν := quad) hρu measurable_coinA coinA_bdd hA hAA
  have hr := iid_measAR1Innov_fn (ν := quad) hρr measurable_coinB coinB_bdd hB hBB
  refine ⟨twoCoin_indepDisturbances ρu ρr, fun πbar xbar ibar fπ fx fi gπ gx gi hM hI => ?_⟩
  exact ((f4_lstab_indep (iidSystem quad) hβ0 hβ1 hκ hσ hlx hli hρu hρr one_pos one_pos hu hr
    twoCoin_indepInnov t₀ hxs his).2 πbar xbar ibar fπ fx fi gπ gx gi hM hI).1

end Woodford.GainsFromCommitment.TidyR5Independence
