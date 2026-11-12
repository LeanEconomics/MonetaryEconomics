/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.PolicyRulesMeasure
import StickyPriceFiscal.ExpectationsMeasureIID

/-!
# Policy rules with recurring news: exact determinacy in a full-support probability model

Cochrane (2023), Chapter 5, §5.5, pp. 147–160 (the model (5.64)–(5.73) and "the unique stationary
equilibrium", p. 148), the condition `α ∈ (1 − ρ, 1 + ρ)` of §5.4 (pp. 137–138), and Online
Appendix A1 §1.9 (pp. 573–577, the unit root, E20). The boundary results of `PolicyRules`
(`alpha_iff_trunc`, `unitroot_iff_trunc`) were proved for the point-mass truncation system
`PolicyRules.truncSystem`, under which the non-existence happens on a single path of probability
zero. Here the same verdicts are proved for **every** measure-theoretic expectation system that
carries recurring nondegenerate news (`RecurringNews`: a bounded adapted martingale difference
with conditional second moment bounded away from zero at every date), in particular for the
genuine i.i.d. infinite-product system `ExpectationsMeasureIID.iidSystem` (every history is null)
and the fair-coin economy.

The non-existence mechanism is second moments, not a single path: if
`W_{t+1} = φ W_t + η_{t+1}` with `|φ| ≥ 1` and news `η` with `E η_{t+1}² ≥ c > 0`, then
`E W_t² ≥ t c` (the news is orthogonal to `W_t`), which no essentially bounded `W` allows
(`not_bdd_of_news`).

## Main results

* `mean_shocks`, `mean_equil`: the unconditional mean of a measure-theoretic equilibrium is a
  perfect-foresight equilibrium (a link to the core). `mnonexist_of_active`: active money leaves
  some initial inflation without an equilibrium, in every probability model.
* `RecurringNews`, `integral_sq_step`, `not_bdd_of_news`, `news_shocks`.
* **`alpha_iff_news`**: with recurring news, the model is determinate iff `|1 − α| < ρ`, or
  `|1 − α| = ρ` with `κ_s = κ_i = 0`. **`unitroot_iff_news`**: on the unit root, determinate iff
  `β_s = 0` and `β_i = k`.
* `iid_recurringNews`, `alpha_iff_iid`, `unitroot_iff_iid`, `alpha_iff_coin`,
  `unitroot_iff_coin`; the links `alpha_iid_iff_trunc`, `unitroot_iid_iff_trunc` (the full-support
  i.i.d. verdict equals the `truncSystem` verdict) and `alpha_boundary_pf_vs_iid` (on the
  boundary perfect foresight and recurring news disagree).
* `mredEquil_iff_core`, `mmodelDeterminate_iff_core`: on a finite fully supported state space a
  measure-theoretic equilibrium is exactly a core equilibrium of
  `MeasExpectationSystem.toExpectationSystem`.
-/

namespace Cochrane.StickyPriceFiscal.PolicyRulesMeasureNews

open MeasureTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID PolicyRules PolicyRulesMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### The mean of an equilibrium is a perfect-foresight equilibrium -/

/-- Cochrane (2023), §5.5, p. 148 (unconditional means): the deterministic path of means
`t ↦ E x_t`, as a perfect-foresight process. -/
noncomputable def mean (x : ℕ → Ω → ℝ) : ℕ → Unit → ℝ := fun t _ => ∫ ω, x t ω ∂S.μ

/-- Cochrane (2023), p. 148 (tool): the mean of the zero process is zero. -/
theorem mean_zero : mean S (0 : ℕ → Ω → ℝ) = 0 := by
  funext t u
  simp [mean]

/-- Cochrane (2023), p. 148 (tool): an essentially bounded process has bounded means. -/
theorem mean_bdd {x : ℕ → Ω → ℝ} (hb : S.BddProc x) : BoundedProc (mean S x) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨M, fun t _ => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := S.μ) (f := x t) (C := M)
    ((hM t).mono fun ω h => by rwa [Real.norm_eq_abs])
  simpa [mean] using h

/-- Cochrane (2023), (5.61)–(5.62), p. 147: the means of admissible shocks are admissible
perfect-foresight shocks (mean-zero news, AR(1) means). -/
theorem mean_shocks {P : Params} {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us) :
    Shocks perfectForesight P (mean S ei) (mean S es) (mean S ui) (mean S us) := by
  obtain ⟨hea, hesa, hua, husa, heb, hesb, hub, husb, hei, hes, hul, husl⟩ := hsh
  have hz : ∀ {e : ℕ → Ω → ℝ}, (∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) →
      ∀ t, perfectForesight.E t (mean S e (t + 1)) = 0 := fun he t => by
    funext u
    change ∫ ω, _ ∂S.μ = 0
    rw [← S.integral_E t, integral_congr_ae (he t)]
    simp
  have har : ∀ {u e : ℕ → Ω → ℝ} {η : ℝ}, StronglyAdapted S.𝓕 u → S.BddProc u →
      StronglyAdapted S.𝓕 e → S.BddProc e → (∀ t, u (t + 1) = η • u t + e (t + 1)) →
      ∀ t, mean S u (t + 1) = η • mean S u t + mean S e (t + 1) := fun hua hub hea heb hl t => by
    funext _
    simp only [mean, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hl t, integral_add' ((int_of S hua hub t).smul _) (int_of S hea heb (t + 1))]
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul]
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, mean_bdd S heb, mean_bdd S hesb,
    mean_bdd S hub, mean_bdd S husb, hz hei, hz hes, har hua hub hea heb hul,
    har husa husb hesa hesb husl⟩

/-- **The mean of an equilibrium** (Cochrane (2023), §5.5, pp. 148–149; a link to the core
`PolicyRules.RedEquil`): taking unconditional expectations of every equation, the means of a
bounded equilibrium in a probability model form a perfect-foresight equilibrium of the same
model with the means of the shocks and the same initial inflation and debt. -/
theorem mean_equil {P : Params} {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us)
    {p0 v0 : ℝ} {x p q v : ℕ → Ω → ℝ} (h : MRedEquil S P ei es ui us p0 v0 x p q v) :
    RedEquil perfectForesight P (mean S ei) (mean S es) (mean S ui) (mean S us) p0 v0
      (mean S x) (mean S p) (mean S q) (mean S v) := by
  obtain ⟨hea, hesa, hua, husa, heb, hesb, hub, husb, hei, hes, -, -⟩ := hsh
  obtain ⟨⟨h64, h65, h68, h71, h72⟩, hxa, hpa, hqa, hva, hxb, hpb, hqb, hvb, hp0, hv0⟩ := h
  have ix := int_of S hxa hxb
  have ip := int_of S hpa hpb
  have iq := int_of S hqa hqb
  have iv := int_of S hva hvb
  have iu := int_of S hua hub
  have ius := int_of S husa husb
  have ie := int_of S hea heb
  have ies := int_of S hesa hesb
  have iE : ∀ t (y : Ω → ℝ), Integrable (S.E t y) S.μ := fun t y => S.integrable_E t y
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, mean_bdd S hxb, mean_bdd S hpb, mean_bdd S hqb,
    mean_bdd S hvb, ?_, ?_⟩
  · funext u
    change ∫ ω, x t ω ∂S.μ = ∫ ω, x (t + 1) ω ∂S.μ - P.sigma * (P.thIpi * ∫ ω, p t ω ∂S.μ +
      P.thIx * ∫ ω, x t ω ∂S.μ + ∫ ω, ui t ω ∂S.μ - ∫ ω, p (t + 1) ω ∂S.μ)
    have e := integral_congr_ae (h64 t)
    have a1 := iE t (x (t + 1))
    have a2 := iE t (p (t + 1))
    have a3 := ix t
    have a4 := ip t
    have a5 := iu t
    simp only [iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp (disch := fun_prop) only [integral_sub, integral_add, integral_const_mul,
      S.integral_E] at e
    linear_combination e
  · funext u
    change ∫ ω, p t ω ∂S.μ = P.beta * ∫ ω, p (t + 1) ω ∂S.μ + P.kappa * ∫ ω, x t ω ∂S.μ
    have e := integral_congr_ae (h65 t)
    have a2 := iE t (p (t + 1))
    have a3 := ix t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
    simp (disch := fun_prop) only [integral_add, integral_const_mul, S.integral_E] at e
    exact e
  · funext u
    change ∫ ω, p (t + 1) ω ∂S.μ - ∫ ω, p (t + 1) ω ∂S.μ =
      -(P.betaS * ∫ ω, es (t + 1) ω ∂S.μ) - P.betaI * ∫ ω, ei (t + 1) ω ∂S.μ
    have z1 : ∫ ω, es (t + 1) ω ∂S.μ = 0 := by
      rw [← S.integral_E t, integral_congr_ae (hes t)]
      simp
    have z2 : ∫ ω, ei (t + 1) ω ∂S.μ = 0 := by
      rw [← S.integral_E t, integral_congr_ae (hei t)]
      simp
    rw [z1, z2]
    ring
  · funext u
    change P.rho * ∫ ω, v (t + 1) ω ∂S.μ = ∫ ω, v t ω ∂S.μ + (P.omega * ∫ ω, q (t + 1) ω ∂S.μ -
      ∫ ω, q t ω ∂S.μ) - ∫ ω, p (t + 1) ω ∂S.μ - (P.thSpi * ∫ ω, p (t + 1) ω ∂S.μ +
      P.thSx * ∫ ω, x (t + 1) ω ∂S.μ + P.alpha * ∫ ω, v t ω ∂S.μ + ∫ ω, us (t + 1) ω ∂S.μ)
    have e := integral_congr_ae (h71 t)
    have a1 := iv t
    have a2 := iv (t + 1)
    have a3 := iq t
    have a4 := iq (t + 1)
    have a5 := ip (t + 1)
    have a6 := ix (t + 1)
    have a7 := ius (t + 1)
    simp only [rnNext, sNext, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp (disch := fun_prop) only [integral_sub, integral_add, integral_const_mul] at e
    linear_combination e
  · funext u
    change P.omega * ∫ ω, q (t + 1) ω ∂S.μ - ∫ ω, q t ω ∂S.μ = P.thIpi * ∫ ω, p t ω ∂S.μ +
      P.thIx * ∫ ω, x t ω ∂S.μ + ∫ ω, ui t ω ∂S.μ
    have e := integral_congr_ae (h72 t)
    have a3 := iq t
    have a4 := iq (t + 1)
    have a5 := ip t
    have a6 := ix t
    have a7 := iu t
    rw [S.integral_E] at e
    simp only [rnNext, iRule, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
    simp (disch := fun_prop) only [integral_sub, integral_add, integral_const_mul] at e
    linear_combination e
  · funext u
    change ∫ ω, p 0 ω ∂S.μ = p0
    rw [integral_congr_ae hp0]
    simp
  · funext u
    change ∫ ω, v 0 ω ∂S.μ = v0
    rw [integral_congr_ae hv0]
    simp

/-- Cochrane (2023), p. 147 (tool): zero disturbances are admissible in every probability
model. -/
theorem mshocks_zero (P : Params) : MShocks S P 0 0 0 0 := by
  refine ⟨fun _ => stronglyMeasurable_zero, fun _ => stronglyMeasurable_zero,
    fun _ => stronglyMeasurable_zero, fun _ => stronglyMeasurable_zero, mbdd_zero S, mbdd_zero S,
    mbdd_zero S, mbdd_zero S, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · simp [S.E_zero]
  · simp [S.E_zero]
  · simp
  · simp

/-- Cochrane (2023), §5.5, p. 148 and §5.5.3, p. 154 (active money and active fiscal policy
over-determine inflation), in every probability model: if `κ(θ_iπ − 1) + (1 − β)θ_ix > 0`, then
even with zero shocks some initial inflation `π_0` admits no bounded equilibrium. (Its mean would
be a perfect-foresight equilibrium, which `PolicyRules.nonexist_of_active` rules out.) -/
theorem mnonexist_of_active {P : Params} (hP : Standard P)
    (hact : 0 < P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx) :
    ∃ p0 : ℝ, ∀ (v0 : ℝ) (x p q v : ℕ → Ω → ℝ), ¬ MRedEquil S P 0 0 0 0 p0 v0 x p q v := by
  obtain ⟨p0, hp0⟩ := nonexist_of_active perfectForesight hP hact
  refine ⟨p0, fun v0 x p q v h => hp0 v0 (mean S x) (mean S p) (mean S q) (mean S v) ?_⟩
  have := mean_equil S (mshocks_zero S P) h
  rwa [mean_zero] at this

/-! ### Recurring news and the growth of second moments -/

/-- Cochrane (2023), §5.5, pp. 147–149 ("shocks" `ε_{t+1}` at every date): an expectation
system carries **recurring nondegenerate news** if some bounded adapted martingale difference
`e` (`E_t e_{t+1} = 0`) has `E e_{t+1}² ≥ c > 0` at every date. -/
def RecurringNews : Prop :=
  ∃ (e : ℕ → Ω → ℝ) (c : ℝ), 0 < c ∧ StronglyAdapted S.𝓕 e ∧ S.BddProc e ∧
    (∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) ∧ ∀ t, c ≤ ∫ ω, e (t + 1) ω ^ 2 ∂S.μ

/-- Cochrane (2023), eq. (2.13), p. 30 (news is orthogonal to what is known), as used in §5.5:
for `W` known at `t` and bounded news `η` with `E_t η = 0`,
`E (φ W + η)² = φ² E W² + E η²`. -/
theorem integral_sq_step {t : ℕ} {W η : Ω → ℝ} (φ : ℝ) (hW : StronglyMeasurable[S.𝓕 t] W)
    {M : ℝ} (hWM : ∀ᵐ ω ∂S.μ, |W ω| ≤ M) (hη : S.BddRV η) (hE : S.E t η =ᵐ[S.μ] 0) :
    ∫ ω, (φ * W ω + η ω) ^ 2 ∂S.μ = φ ^ 2 * ∫ ω, W ω ^ 2 ∂S.μ + ∫ ω, η ω ^ 2 ∂S.μ := by
  have hWB : S.BddRV W := MeasExpectationSystem.BddRV.of_stronglyMeasurable hW hWM
  have hcross : ∫ ω, W ω * η ω ∂S.μ = 0 := by
    have h1 := S.E_pullOut hW hWM hη.integrable
    have h2 : ∫ ω, W ω * η ω ∂S.μ = ∫ ω, S.E t (W * η) ω ∂S.μ := (S.integral_E t (W * η)).symm
    rw [h2, integral_congr_ae h1]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hE] with ω h
    simp [Pi.mul_apply, h]
  have i1 : Integrable (fun ω => W ω ^ 2) S.μ := hWB.sq.integrable
  have i2 : Integrable (fun ω => W ω * η ω) S.μ := (hWB.mul hη).integrable
  have i3 : Integrable (fun ω => η ω ^ 2) S.μ := hη.sq.integrable
  have expand : (fun ω => (φ * W ω + η ω) ^ 2) =
      fun ω => φ ^ 2 * W ω ^ 2 + (2 * φ * (W ω * η ω) + η ω ^ 2) := by
    funext ω
    ring
  have i23 : Integrable (fun ω => 2 * φ * (W ω * η ω) + η ω ^ 2) S.μ := (i2.const_mul _).add i3
  rw [expand, integral_add (i1.const_mul _) i23, integral_add (i2.const_mul _) i3,
    integral_const_mul, integral_const_mul, hcross]
  ring

/-- **Recurring news makes a non-stable recursion unbounded** (Cochrane (2023), §5.5 and A1 §1.9,
the mechanism behind "debt cannot explode" at the boundary): if `W_{t+1} = φ W_t + η_{t+1}` a.e.
with `|φ| ≥ 1`, `W` adapted, and bounded news `η` with `E_t η_{t+1} = 0` and
`E η_{t+1}² ≥ c > 0`, then `E W_t² ≥ t c`, so `W` is not essentially bounded. -/
theorem not_bdd_of_news {φ c : ℝ} (hφ : 1 ≤ |φ|) (hc : 0 < c) {W η : ℕ → Ω → ℝ}
    (hWa : StronglyAdapted S.𝓕 W) (hηa : StronglyAdapted S.𝓕 η) (hηb : S.BddProc η)
    (hE : ∀ t, S.E t (η (t + 1)) =ᵐ[S.μ] 0) (hηc : ∀ t, c ≤ ∫ ω, η (t + 1) ω ^ 2 ∂S.μ)
    (hr : ∀ t, W (t + 1) =ᵐ[S.μ] φ • W t + η (t + 1)) : ¬ S.BddProc W := by
  rintro ⟨M, hM⟩
  obtain ⟨B, hB⟩ := hηb
  have hφ2 : 1 ≤ φ ^ 2 := by nlinarith [sq_abs φ, abs_nonneg φ]
  have hgrow : ∀ t : ℕ, (t : ℝ) * c ≤ ∫ ω, W t ω ^ 2 ∂S.μ := by
    intro t
    induction t with
    | zero => simpa using integral_nonneg (fun ω => sq_nonneg (W 0 ω))
    | succ t ih =>
      have e : ∫ ω, W (t + 1) ω ^ 2 ∂S.μ = ∫ ω, (φ * W t ω + η (t + 1) ω) ^ 2 ∂S.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hr t] with ω h
        rw [h]
        rfl
      rw [e, integral_sq_step S φ (hWa t) (hM t)
        (MeasExpectationSystem.BddRV.of_stronglyMeasurable (hηa (t + 1)) (hB (t + 1))) (hE t)]
      have h0 : 0 ≤ ∫ ω, W t ω ^ 2 ∂S.μ := integral_nonneg (fun ω => sq_nonneg _)
      push_cast
      nlinarith [hηc t]
  have hup : ∀ t, ∫ ω, W t ω ^ 2 ∂S.μ ≤ M ^ 2 := by
    intro t
    have hW2 : Integrable (fun ω => W t ω ^ 2) S.μ :=
      (MeasExpectationSystem.BddRV.of_stronglyMeasurable (hWa t) (hM t)).sq.integrable
    calc ∫ ω, W t ω ^ 2 ∂S.μ ≤ ∫ _ω, M ^ 2 ∂S.μ := by
          refine integral_mono_ae hW2 (integrable_const _) ?_
          filter_upwards [hM t] with ω h
          calc W t ω ^ 2 = |W t ω| ^ 2 := (sq_abs _).symm
            _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = M ^ 2 := by simp
  obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 2 / c)
  have := (hgrow n).trans (hup n)
  rw [div_lt_iff₀ hc] at hn
  linarith

/-- Cochrane (2023), (5.61)–(5.62), p. 147 (shocks built from news): `ε_i = k_i e`,
`ε_s = k_s e`, and AR(1) disturbances driven by them from zero are admissible. -/
theorem news_shocks {P : Params} (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1) {e : ℕ → Ω → ℝ}
    (hea : StronglyAdapted S.𝓕 e) (heb : S.BddProc e) (he : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0)
    (ki ks : ℝ) :
    MShocks S P (ki • e) (ks • e) (backRec P.etaI (fun t => (ki • e) (t + 1)) 0)
      (backRec P.etaS (fun t => (ks • e) (t + 1)) 0) := by
  obtain ⟨Mi, hMi⟩ := mbdd_shift S (mbdd_smul S ki heb)
  obtain ⟨Ms, hMs⟩ := mbdd_shift S (mbdd_smul S ks heb)
  have hE : ∀ k : ℝ, ∀ t, S.E t ((k • e) (t + 1)) =ᵐ[S.μ] 0 := fun k t => by
    filter_upwards [S.E_smul k (e (t + 1)) t, he t] with ω h1 h2
    change S.E t (k • e (t + 1)) ω = 0
    rw [h1, Pi.smul_apply, h2]
    simp
  exact ⟨fun t => (hea t).const_smul ki, fun t => (hea t).const_smul ks,
    backRec_adaptedM S (fun t => (hea (t + 1)).const_smul ki) 0,
    backRec_adaptedM S (fun t => (hea (t + 1)).const_smul ks) 0,
    mbdd_smul S ki heb, mbdd_smul S ks heb, backRec_bddM S hηi hMi 0, backRec_bddM S hηs hMs 0,
    hE ki, hE ks, fun _ => rfl, fun _ => rfl⟩

/-- Cochrane (2023), §5.5 (tool): scaled news is news, with second moment scaled by `K²`. -/
theorem news_scale {e : ℕ → Ω → ℝ} {c : ℝ} (hea : StronglyAdapted S.𝓕 e) (heb : S.BddProc e)
    (he : ∀ t, S.E t (e (t + 1)) =ᵐ[S.μ] 0) (hec : ∀ t, c ≤ ∫ ω, e (t + 1) ω ^ 2 ∂S.μ)
    (K : ℝ) :
    StronglyAdapted S.𝓕 (K • e) ∧ S.BddProc (K • e) ∧
      (∀ t, S.E t ((K • e) (t + 1)) =ᵐ[S.μ] 0) ∧
      ∀ t, K ^ 2 * c ≤ ∫ ω, (K • e) (t + 1) ω ^ 2 ∂S.μ := by
  refine ⟨fun t => (hea t).const_smul K, mbdd_smul S K heb, fun t => ?_, fun t => ?_⟩
  · filter_upwards [S.E_smul K (e (t + 1)) t, he t] with ω h1 h2
    change S.E t (K • e (t + 1)) ω = 0
    rw [h1, Pi.smul_apply, h2]
    simp
  · have e1 : (fun ω => (K • e) (t + 1) ω ^ 2) = fun ω => K ^ 2 * e (t + 1) ω ^ 2 := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hec t) (sq_nonneg K)

/-! ### Exact determinacy with recurring news -/

/-- **Exact determinacy in `α` with recurring news** (Cochrane (2023), §5.5, p. 148, and the
condition `α ∈ (1 − ρ, 1 + ρ)` of §5.4, pp. 137–138), in every measure-theoretic expectation
system with recurring nondegenerate news: under the sign restrictions, the passive-money
condition, `|ω|, |η_i|, |η_s| < 1` and `ρ > 0`, the model is determinate iff `|1 − α| < ρ`, or
`|1 − α| = ρ` and both shock loadings of the debt recursion vanish (`κ_s = κ_i = 0`). On the
boundary with a nonzero loading, debt shocks `ε_s = κ_s e`, `ε_i = κ_i e` accumulate along the
unit root: `E W_t² ≥ t (κ_s² + κ_i²)² c`, so no bounded equilibrium exists. -/
theorem alpha_iff_news (hS : RecurringNews S) {P : Params} (hP : Standard P)
    (hpass : Passive P) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) :
    MModelDeterminate S P ↔ |1 - P.alpha| < P.rho ∨
      (|1 - P.alpha| = P.rho ∧ kapS P (alphaCoef P) = 0 ∧ kapI P (alphaCoef P) = 0) := by
  have hroot : ∀ h : |1 - P.alpha| = P.rho, |debtRoot P| = 1 := fun h => by
    rw [debtRoot, abs_div, abs_of_pos hρ0, h, div_self hρ0.ne']
  constructor
  · intro hd
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    rcases h1.lt_or_eq with h | h
    · obtain ⟨⟨x, p, q, v, hy⟩, -⟩ := hd 0 0 0 0 (mshocks_zero S P) 0 1
      exact mnonexist_of_alpha S hP hpass hω hρ0 h x p q v hy
    · have hk : kapS P (alphaCoef P) ≠ 0 ∨ kapI P (alphaCoef P) ≠ 0 := by
        by_contra hk
        push Not at hk
        exact h2 h.symm hk.1 hk.2
      obtain ⟨e, c, hc, hea, heb, he, hec⟩ := hS
      have hsh := news_shocks S (P := P) hηi hηs hea heb he (kapI P (alphaCoef P))
        (kapS P (alphaCoef P))
      obtain ⟨⟨x, p, q, v, hy⟩, -⟩ := hd _ _ _ _ hsh 0 0
      obtain ⟨W, hWa, hWb, -, hWr⟩ := (malpha_exists_iff S hP hpass hω hρ0 hηi hηs
        (hroot h.symm).ge hsh 0 0).mp ⟨x, p, q, v, hy⟩
      have hK : 0 < kapS P (alphaCoef P) ^ 2 + kapI P (alphaCoef P) ^ 2 := by
        rcases hk with h | h
        · have := sq_pos_of_ne_zero h
          linarith [sq_nonneg (kapI P (alphaCoef P))]
        · have := sq_pos_of_ne_zero h
          linarith [sq_nonneg (kapS P (alphaCoef P))]
      obtain ⟨hηa, hηb, hηE, hηc⟩ := news_scale S hea heb he hec
        (kapS P (alphaCoef P) ^ 2 + kapI P (alphaCoef P) ^ 2)
      refine not_bdd_of_news S (hroot h.symm).ge (mul_pos (pow_pos hK 2) hc) hWa hηa hηb hηE
        hηc (fun t => ?_) hWb
      filter_upwards [hWr t] with ω e1
      rw [e1]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  · rintro (h | ⟨h, hks, hki⟩)
    · exact mmodelDeterminate_of S hP hpass hω hρ0 h
    · intro ei es ui us hsh p0 v0
      refine ⟨?_, fun _ _ _ _ _ _ _ _ h1 h2 => mpolicyRules_unique S hP hpass hω hρ0.ne' h1 h2⟩
      have hsh' := hsh
      obtain ⟨-, -, hua, husa, -, -, ⟨Mu, hMu⟩, ⟨Ms, hMs⟩, -, -, -, -⟩ := hsh'
      obtain ⟨W0, hW0⟩ : ∃ W0 : Ω → ℝ, W0 = (fun _ => v0) - (cKp P (alphaCoef P) • (fun _ => p0) +
          cKu P (alphaCoef P) • ui 0 + cKs P (alphaCoef P) • us 0) := ⟨_, rfl⟩
      have hW0m : StronglyMeasurable[S.𝓕 0] W0 := by
        rw [hW0]
        exact stronglyMeasurable_const.sub (((stronglyMeasurable_const.const_smul _).add
          ((hua 0).const_smul _)).add ((husa 0).const_smul _))
      refine (malpha_exists_iff S hP hpass hω hρ0 hηi hηs (hroot h).ge hsh p0 v0).mpr
        ⟨fun t => debtRoot P ^ t • W0,
          fun t => (hW0m.mono (S.𝓕.mono (Nat.zero_le t))).const_smul _,
          ⟨|v0| + |cKp P (alphaCoef P)| * |p0| + |cKu P (alphaCoef P)| * |Mu| +
            |cKs P (alphaCoef P)| * |Ms|, fun t => ?_⟩,
          Eventually.of_forall fun ω => by simp [hW0], fun t => Eventually.of_forall fun ω => ?_⟩
      · filter_upwards [hMu 0, hMs 0] with ω a1 a2
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, hroot h, one_pow, one_mul, hW0,
          Pi.sub_apply, Pi.add_apply]
        have a1' := a1.trans (le_abs_self Mu)
        have a2' := a2.trans (le_abs_self Ms)
        calc |v0 - (cKp P (alphaCoef P) * p0 + cKu P (alphaCoef P) * ui 0 ω +
              cKs P (alphaCoef P) * us 0 ω)|
            ≤ |v0| + (|cKp P (alphaCoef P) * p0| + |cKu P (alphaCoef P) * ui 0 ω| +
              |cKs P (alphaCoef P) * us 0 ω|) :=
              (abs_sub _ _).trans (add_le_add le_rfl ((abs_add_le _ _).trans
                (add_le_add (abs_add_le _ _) le_rfl)))
          _ ≤ _ := by
              rw [abs_mul, abs_mul, abs_mul]
              have b1 := mul_le_mul_of_nonneg_left a1' (abs_nonneg (cKu P (alphaCoef P)))
              have b2 := mul_le_mul_of_nonneg_left a2' (abs_nonneg (cKs P (alphaCoef P)))
              linarith
      · simp only [hks, hki, zero_smul, add_zero, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
          Pi.zero_apply, pow_succ]
        ring

/-- **The unit-root case with recurring news** (Cochrane (2023), A1 §1.9, pp. 574–576; E20), in
every measure-theoretic expectation system with recurring nondegenerate news: on the boundary
`κ(θ_iπ − 1) + (1 − β)θ_ix = 0`, with `|η_i|, |η_s|, |ω| < 1`, `ρ > 0` and `|1 − α| < ρ`, the
model is determinate iff `β_s = 0` and `β_i = k` — iff no shock moves the inflation martingale;
otherwise inflation inherits a random walk with `E W_t² ≥ t (β_s² + (k − β_i)²)² c`. -/
theorem unitroot_iff_news (hS : RecurringNews S) {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho) :
    MModelDeterminate S P ↔ P.betaS = 0 ∧ P.betaI = urK P := by
  constructor
  · intro hd
    by_contra hc
    have hk : -P.betaS ≠ 0 ∨ urK P - P.betaI ≠ 0 := by
      by_contra hk
      push Not at hk
      exact hc ⟨by linarith [hk.1], by linarith [hk.2]⟩
    obtain ⟨e, c, hc, hea, heb, he, hec⟩ := hS
    have hsh := news_shocks S (P := P) hηi hηs hea heb he (urK P - P.betaI) (-P.betaS)
    obtain ⟨⟨x, p, q, v, hy⟩, -⟩ := hd _ _ _ _ hsh 0 0
    obtain ⟨W, hWa, hWb, -, hWr⟩ := (munitroot_exists_iff S hP hb hηi hω hρ0 hα hsh 0 0).mp
      ⟨x, p, q, v, hy⟩
    have hK : 0 < (-P.betaS) ^ 2 + (urK P - P.betaI) ^ 2 := by
      rcases hk with h | h
      · have := sq_pos_of_ne_zero h
        linarith [sq_nonneg (urK P - P.betaI)]
      · have := sq_pos_of_ne_zero h
        linarith [sq_nonneg (-P.betaS)]
    obtain ⟨hηa, hηb, hηE, hηc⟩ := news_scale S hea heb he hec
      ((-P.betaS) ^ 2 + (urK P - P.betaI) ^ 2)
    refine not_bdd_of_news S (φ := 1) (by simp) (mul_pos (pow_pos hK 2) hc) hWa hηa hηb hηE
      hηc (fun t => ?_) hWb
    filter_upwards [hWr t] with ω e1
    rw [e1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rintro ⟨hs, hi⟩ ei es ui us hsh p0 v0
    refine ⟨?_, fun _ _ _ _ _ _ _ _ h1 h2 => munitroot_unique S hP hb hω hρ0.ne' h1 h2⟩
    have hsh' := hsh
    obtain ⟨-, -, hua, -, -, -, ⟨Mu, hMu⟩, -, -, -, -, -⟩ := hsh'
    refine (munitroot_exists_iff S hP hb hηi hω hρ0 hα hsh p0 v0).mpr
      ⟨fun _ => (fun _ => p0) + urK P • ui 0,
        fun t => ((stronglyMeasurable_const.add ((hua 0).const_smul _)).mono
          (S.𝓕.mono (Nat.zero_le t))),
        ⟨|p0| + |urK P| * |Mu|, fun t => ?_⟩, Eventually.of_forall fun _ => rfl,
        fun t => Eventually.of_forall fun ω => ?_⟩
    · filter_upwards [hMu 0] with ω a1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (a1.trans (le_abs_self Mu)) (abs_nonneg _)
    · simp only [hs, hi, neg_zero, sub_self, zero_smul, add_zero, Pi.add_apply, Pi.zero_apply]

/-! ### The genuine i.i.d. system, and the links to `truncSystem` and perfect foresight -/

/-- Cochrane (2023), §5.5, pp. 147–149 (shocks at every date), in the i.i.d. infinite-product
system: mean-zero, bounded i.i.d. shocks with variance `σ² > 0` are recurring nondegenerate news
(with `c = σ²`). -/
theorem iid_recurringNews {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) : RecurringNews (iidSystem ν) :=
  ⟨shock, σ2, hσ, fun _ => (measurable_shock ν le_rfl).stronglyMeasurable,
    ⟨B, shock_ae_bdd ν hbdd⟩, E_shock_zero hmean, fun t => le_of_eq (by
      rw [← hvar]
      exact (integral_shock_fun ν (t + 1) (measurable_id.pow_const 2)).symm)⟩

/-- **Exact determinacy in `α` in the genuine i.i.d. economy** (Cochrane (2023), §5.5, p. 148;
§5.4, pp. 137–138): with mean-zero bounded i.i.d. shocks of variance `σ² > 0` (a full-support
infinite-horizon system in which every history is null), under the sign restrictions, passive
money, `|ω|, |η_i|, |η_s| < 1` and `ρ > 0`, the model is determinate iff `|1 − α| < ρ`, or
`|1 − α| = ρ` with `κ_s = κ_i = 0`. -/
theorem alpha_iff_iid {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {P : Params} (hP : Standard P)
    (hpass : Passive P) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) :
    MModelDeterminate (iidSystem ν) P ↔ |1 - P.alpha| < P.rho ∨
      (|1 - P.alpha| = P.rho ∧ kapS P (alphaCoef P) = 0 ∧ kapI P (alphaCoef P) = 0) :=
  alpha_iff_news (iidSystem ν) (iid_recurringNews hmean hvar hσ hbdd) hP hpass hω hρ0 hηi hηs

/-- **The unit root in the genuine i.i.d. economy** (Cochrane (2023), A1 §1.9, pp. 574–576;
E20): with mean-zero bounded i.i.d. shocks of variance `σ² > 0`, on the boundary
`κ(θ_iπ − 1) + (1 − β)θ_ix = 0`, with `|η_i|, |η_s|, |ω| < 1`, `ρ > 0` and `|1 − α| < ρ`, the
model is determinate iff `β_s = 0` and `β_i = k`. -/
theorem unitroot_iff_iid {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho) :
    MModelDeterminate (iidSystem ν) P ↔ P.betaS = 0 ∧ P.betaI = urK P :=
  unitroot_iff_news (iidSystem ν) (iid_recurringNews hmean hvar hσ hbdd) hP hb hηi hηs hω hρ0
    hα

/-- **Link to the point-mass system** (Cochrane (2023), §5.5, p. 148): the full-support i.i.d.
verdict on determinacy in `α` is exactly the `PolicyRules.truncSystem` verdict
(`PolicyRules.alpha_iff_trunc`). -/
theorem alpha_iid_iff_trunc {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {P : Params} (hP : Standard P)
    (hpass : Passive P) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) :
    MModelDeterminate (iidSystem ν) P ↔ ModelDeterminate truncSystem P :=
  (alpha_iff_iid hmean hvar hσ hbdd hP hpass hω hρ0 hηi hηs).trans
    (alpha_iff_trunc hP hpass hω hρ0 hηi hηs).symm

/-- **Link to the point-mass system at the unit root** (Cochrane (2023), A1 §1.9, E20): the
full-support i.i.d. verdict equals the `PolicyRules.truncSystem` verdict
(`PolicyRules.unitroot_iff_trunc`). -/
theorem unitroot_iid_iff_trunc {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho) :
    MModelDeterminate (iidSystem ν) P ↔ ModelDeterminate truncSystem P :=
  (unitroot_iff_iid hmean hvar hσ hbdd hP hb hηi hηs hω hρ0 hα).trans
    (unitroot_iff_trunc hP hb hηi hηs hω hρ0 hα).symm

/-- Cochrane (2023), §5.5, p. 148, in the fair-coin economy (`ε_t = ±1` i.i.d.): determinacy in
`α` holds iff `|1 − α| < ρ`, or `|1 − α| = ρ` with `κ_s = κ_i = 0`. -/
theorem alpha_iff_coin {P : Params} (hP : Standard P) (hpass : Passive P) (hω : |P.omega| < 1)
    (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1) (hηs : |P.etaS| < 1) :
    MModelDeterminate (iidSystem coin) P ↔ |1 - P.alpha| < P.rho ∨
      (|1 - P.alpha| = P.rho ∧ kapS P (alphaCoef P) = 0 ∧ kapI P (alphaCoef P) = 0) :=
  alpha_iff_iid coin_mean coin_var one_pos coin_bdd hP hpass hω hρ0 hηi hηs

/-- Cochrane (2023), A1 §1.9 (E20), in the fair-coin economy: on the unit root the model is
determinate iff `β_s = 0` and `β_i = k`. -/
theorem unitroot_iff_coin {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho) :
    MModelDeterminate (iidSystem coin) P ↔ P.betaS = 0 ∧ P.betaI = urK P :=
  unitroot_iff_iid coin_mean coin_var one_pos coin_bdd hP hb hηi hηs hω hρ0 hα

/-- Cochrane (2023), §5.5, p. 148 (the boundary `|1 − α| = ρ` separates perfect foresight from
genuine uncertainty): with a nonzero shock loading of the debt recursion, the model is
determinate under perfect foresight (`PolicyRules.alpha_iff_pf`) but not in the i.i.d. economy. -/
theorem alpha_boundary_pf_vs_iid {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {P : Params} (hP : Standard P)
    (hpass : Passive P) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) (h : |1 - P.alpha| = P.rho)
    (hk : kapS P (alphaCoef P) ≠ 0 ∨ kapI P (alphaCoef P) ≠ 0) :
    ModelDeterminate perfectForesight P ∧ ¬ MModelDeterminate (iidSystem ν) P := by
  refine ⟨(alpha_iff_pf hP hpass hω hρ0 hηi hηs).mpr h.le, fun hd => ?_⟩
  rcases (alpha_iff_iid hmean hvar hσ hbdd hP hpass hω hρ0 hηi hηs).mp hd with h1 | ⟨-, h2, h3⟩
  · linarith
  · rcases hk with hk | hk
    · exact hk h2
    · exact hk h3

/-- Cochrane (2023), A1 §1.9 (E20 refined): on the unit root with `β_s ≠ 0` or `β_i ≠ k` the
model is determinate under perfect foresight (`PolicyRules.unitroot_pf`) but not in the i.i.d.
economy. -/
theorem unitroot_pf_vs_iid {ν : ProbabilityMeasure ℝ} {σ2 B : ℝ}
    (hmean : ∫ x, x ∂(ν : Measure ℝ) = 0) (hvar : ∫ x, x ^ 2 ∂(ν : Measure ℝ) = σ2)
    (hσ : 0 < σ2) (hbdd : ∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) {P : Params} (hP : Standard P)
    (hb : P.kappa * (P.thIpi - 1) + (1 - P.beta) * P.thIx = 0) (hηi : |P.etaI| < 1)
    (hηs : |P.etaS| < 1) (hω : |P.omega| < 1) (hρ0 : 0 < P.rho) (hα : |1 - P.alpha| < P.rho)
    (hk : ¬ (P.betaS = 0 ∧ P.betaI = urK P)) :
    ModelDeterminate perfectForesight P ∧ ¬ MModelDeterminate (iidSystem ν) P :=
  ⟨unitroot_pf hP hb hηi hω hρ0 hα,
    fun hd => hk ((unitroot_iff_iid hmean hvar hσ hbdd hP hb hηi hηs hω hρ0 hα).mp hd)⟩

/-! ### Bridge: finite fully supported systems are core systems -/

/-- Cochrane (2023), Ch. 2, p. 29 (tool for the bridge): on a finite fully supported space,
a.e. equality is equality. -/
theorem ae_iff_eq [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (f g : Ω → ℝ) : f =ᵐ[S.μ] g ↔ f = g :=
  ⟨S.eq_of_ae_eq hfull, EventuallyEq.of_eq⟩

/-- Cochrane (2023), Ch. 2, p. 29 (tool for the bridge): on a finite fully supported space,
measurable adaptedness is the core `Adapted`. -/
theorem adapted_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (y : ℕ → Ω → ℝ) : StronglyAdapted S.𝓕 y ↔ (S.toExpectationSystem hfull).Adapted y := by
  constructor
  · intro h t
    rw [MeasExpectationSystem.toExpectationSystem_E]
    exact S.E_of_stronglyMeasurable (h t) Integrable.of_finite
  · intro h t
    have e := h t
    rw [MeasExpectationSystem.toExpectationSystem_E] at e
    exact e ▸ S.stronglyMeasurable_E t (y t)

/-- Cochrane (2023), Ch. 2, p. 29 (tool for the bridge): on a finite fully supported space an
essential bound is a bound. -/
theorem bdd_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    (y : ℕ → Ω → ℝ) : S.BddProc y ↔ BoundedProc y := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun t ω => S.le_of_ae_le hfull (f := fun ω => |y t ω|) (g := fun _ => M) (hM t) ω⟩
  · rintro ⟨M, hM⟩
    exact ⟨M, fun t => Eventually.of_forall (hM t)⟩

/-- **Bridge for the shocks** (Cochrane (2023), (5.61)–(5.62), p. 147): on a finite fully
supported state space, admissible shocks in the measure-theoretic sense are exactly admissible
shocks of the core system `toExpectationSystem`. -/
theorem mshocks_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {P : Params} {ei es ui us : ℕ → Ω → ℝ} :
    MShocks S P ei es ui us ↔ Shocks (S.toExpectationSystem hfull) P ei es ui us := by
  simp only [MShocks, Shocks, ae_iff_eq S hfull, adapted_iff_core S hfull, bdd_iff_core S hfull,
    MeasExpectationSystem.toExpectationSystem_E]

/-- **Bridge for equilibria** (Cochrane (2023), pp. 148–149): on a finite fully supported state
space, a measure-theoretic equilibrium is exactly a core equilibrium (`PolicyRules.RedEquil`) of
the core system `toExpectationSystem`. -/
theorem mredEquil_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω] (hfull : ∀ ω, S.μ {ω} ≠ 0)
    {P : Params} {ei es ui us : ℕ → Ω → ℝ} {p0 v0 : ℝ} {x p q v : ℕ → Ω → ℝ} :
    MRedEquil S P ei es ui us p0 v0 x p q v ↔
      RedEquil (S.toExpectationSystem hfull) P ei es ui us p0 v0 x p q v := by
  simp only [MRedEquil, RedEquil, MRedSys, RedSys, ae_iff_eq S hfull, adapted_iff_core S hfull,
    bdd_iff_core S hfull, SharedTools.innov, MeasExpectationSystem.innov,
    MeasExpectationSystem.toExpectationSystem_E]

/-- **Bridge for determinacy** (Cochrane (2023), §5.5, p. 148): on a finite fully supported
state space, measure-theoretic determinacy (existence, uniqueness a.e.) is exactly core
determinacy (`PolicyRules.ModelDeterminate`) of `toExpectationSystem`. -/
theorem mmodelDeterminate_iff_core [Finite Ω] [DiscreteMeasurableSpace Ω]
    (hfull : ∀ ω, S.μ {ω} ≠ 0) (P : Params) :
    MModelDeterminate S P ↔ ModelDeterminate (S.toExpectationSystem hfull) P := by
  constructor
  · intro hd ei es ui us hsh p0 v0
    obtain ⟨⟨x, p, q, v, h⟩, hu⟩ := hd ei es ui us ((mshocks_iff_core S hfull).mpr hsh) p0 v0
    refine ⟨(x, p, q, v), (mredEquil_iff_core S hfull).mp h, fun y hy => ?_⟩
    have e := hu _ _ _ _ _ _ _ _ ((mredEquil_iff_core S hfull).mpr hy) h
    refine Prod.ext (funext fun t => S.eq_of_ae_eq hfull (e t).1)
      (Prod.ext (funext fun t => S.eq_of_ae_eq hfull (e t).2.1)
      (Prod.ext (funext fun t => S.eq_of_ae_eq hfull (e t).2.2.1)
      (funext fun t => S.eq_of_ae_eq hfull (e t).2.2.2)))
  · intro hd ei es ui us hsh p0 v0
    obtain ⟨y, hy, hu⟩ := hd ei es ui us ((mshocks_iff_core S hfull).mp hsh) p0 v0
    refine ⟨⟨y.1, y.2.1, y.2.2.1, y.2.2.2, (mredEquil_iff_core S hfull).mpr hy⟩,
      fun x p q v x' p' q' v' h h' => ?_⟩
    have e1 := hu (x, p, q, v) ((mredEquil_iff_core S hfull).mp h)
    have e2 := hu (x', p', q', v') ((mredEquil_iff_core S hfull).mp h')
    have e := e1.trans e2.symm
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl⟩ := e
    exact fun t => ⟨EventuallyEq.rfl, EventuallyEq.rfl, EventuallyEq.rfl, EventuallyEq.rfl⟩

end Cochrane.StickyPriceFiscal.PolicyRulesMeasureNews
