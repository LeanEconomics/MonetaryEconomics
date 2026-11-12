/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.TidyR6StochasticMeasure

/-!
# The patches of §16.10 and the deflations of §16.8 almost surely

Cochrane (2023), §16.8, pp. 379–380 and §§16.10.2–16.10.6, pp. 386–394, on a general filtered
probability space (TidyR6ExpectationsMeasure: `E_t = μ[·|𝓕_t]`, every equation almost surely;
the i.i.d. economy with infinitely many genuine shocks is an instance). The abstract-system
versions in TidyR6StochasticPatches take the pull-out property and "this function of known
variables is known" as hypotheses. Here neither is assumed: adaptedness is
`MeasureTheory.StronglyAdapted`, measurable functions of adapted processes are adapted, and the
pull-out property of `condExp` for bounded known factors
(`TidyR6ExpectationsMeasure.MeasExpectationSystem.E_pullOut`) is used directly. Only
boundedness (for integrability) is assumed.

## Main results

* `firstSet`, `measurableSet_firstSet`, `MeasACK`, `meas_ack_bounded` (no ACK equilibrium
  exceeds `Π_U`, almost surely at every date), `le_of_gapAbove_ae`,
  `meas_ack_prunes_inflation` (no equilibrium has `Π_t > Π*`, a.s.).
* `meas_bsgu_tvc_violated` (BSGU, §16.10.3): `βᵗE_0b_t → ∞` almost surely where `E_0b_T > 0`.
* `meas_mubar_tvc_violated` (Woodford's `μ̄`, §16.10.3) and `meas_sims_tvc_violated` (Sims
  1994, §16.10.6): the transversality term does not tend to zero.
* `meas_stochEq1632_of_bond`, `boundedRule_rhs_lt`, `meas_bounded_rule_explosion`
  ((16.31)–(16.32), §16.10.6): in the bounded-rule model the event `Π_t ∈ (1, 3/2)` has
  probability zero in every equilibrium.
* `meas_deflation_mean` (pp. 379–380): `E[1/Π_t]` nondecreasing and convergent,
  `∑ E[1/Φ(Π_t) − 1/Π_t] < ∞`.
* Online Appendix A3: `meas_a3_helicopter_tvc_violated` (helicopter money violates the
  transversality condition), `meas_a3_omo_tvc` (under open-market operations real total debt is a
  martingale and the transversality condition holds).
-/

namespace Cochrane.NewKeynesianSelection.TidyR6StochasticMeasurePatches

open MeasureTheory ProbabilityTheory Filter Topology TidyR6ExpectationsMeasure
open TidyR6StochasticPatches TidyR6StochasticMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ## Tools -/

/-- Cochrane (2023), p. 389: a variable that is measurable and bounded is integrable. -/
theorem integrable_of_bdd {x : Ω → ℝ} (hx : Measurable x) {C : ℝ} (hC : ∀ ω, |x ω| ≤ C) :
    Integrable x S.μ :=
  Integrable.of_bound hx.aestronglyMeasurable C (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hC ω)

/-- Cochrane (2023), (16.25)–(16.27), p. 378, in one state: where (16.25) holds and the rule
holds, `E_t(1/Π_{t+1}) = 1/Φ(Π_t)`. -/
theorem E_inv_pt {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {it Et x : ℝ}
    (hω : 1 / (1 + it) = (1 + r)⁻¹ * Et) (hrule : 1 + it = (1 + r) * Φ x) : Et = 1 / Φ x := by
  rw [hrule, one_div, mul_inv] at hω
  rw [one_div]
  exact (mul_left_cancel₀ (inv_ne_zero hr.ne') hω).symm

/-- Cochrane (2023), §16.1, p. 364: if `aₙ ≥ c` and `a_{n+1} ≥ q aₙ` from `T` on with `q > 1`
and `a_T > 0`, then `aₙ → ∞`. -/
theorem tendsto_of_growth {a : ℕ → ℝ} {q : ℝ} (hq : 1 < q) {T : ℕ} (hT : 0 < a T)
    (h : ∀ t, T ≤ t → q * a t ≤ a (t + 1)) : Tendsto a atTop atTop := by
  have hg : ∀ n, q ^ n * a T ≤ a (T + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc q ^ (n + 1) * a T = q * (q ^ n * a T) := by ring
        _ ≤ q * a (T + n) := mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ a (T + n + 1) := h _ (Nat.le_add_right T n)
  have hlim : Tendsto (fun n => q ^ n * a T) atTop atTop :=
    Tendsto.atTop_mul_const hT (tendsto_pow_atTop_atTop_of_one_lt hq)
  rw [← tendsto_add_atTop_iff_nat T]
  exact (tendsto_atTop_mono hg hlim).congr fun n => by rw [Nat.add_comm T n]

/-- Cochrane (2023), §16.10.3, p. 390: if `a_{n+1} ≥ aₙ` from `T` on and `a_T > 0`, then `aₙ`
does not tend to zero. -/
theorem not_tendsto_zero_of_mono {a : ℕ → ℝ} {T : ℕ} (hT : 0 < a T)
    (h : ∀ t, T ≤ t → a t ≤ a (t + 1)) : ¬ Tendsto a atTop (𝓝 0) := by
  intro hlim
  have hg : ∀ n, a T ≤ a (T + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => exact ih.trans (h _ (Nat.le_add_right T n))
  have h2 := (tendsto_add_atTop_iff_nat T).mpr hlim
  have := ge_of_tendsto h2 (Eventually.of_forall fun n => by
    simpa only [Nat.add_comm n T] using hg n)
  linarith

/-! ## Atkeson–Chari–Kehoe almost surely -/

/-- Cochrane (2023), §16.10.2, p. 389: the event "`t` is the first date with `Π_t > Π_U`". -/
def firstSet (infl : ℕ → Ω → ℝ) (PiU : ℝ) (t : ℕ) : Set Ω :=
  {ω | PiU < infl t ω ∧ ∀ s < t, infl s ω ≤ PiU}

/-- Cochrane (2023), §16.10.2, p. 389: the first-exceedance event is known at its date when
inflation is adapted. -/
theorem measurableSet_firstSet {infl : ℕ → Ω → ℝ} (had : StronglyAdapted S.𝓕 infl) (PiU : ℝ)
    (t : ℕ) : MeasurableSet[S.𝓕 t] (firstSet infl PiU t) := by
  have h1 : MeasurableSet[S.𝓕 t] {ω | PiU < infl t ω} :=
    measurableSet_lt measurable_const (had t).measurable
  have h2 : MeasurableSet[S.𝓕 t] {ω | ∀ s < t, infl s ω ≤ PiU} := by
    have e : {ω | ∀ s < t, infl s ω ≤ PiU} = ⋂ s : Fin t, {ω | infl s ω ≤ PiU} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h s => h s s.isLt, fun h s hs => h ⟨s, hs⟩⟩
    rw [e]
    exact MeasurableSet.iInter fun s =>
      measurableSet_le ((had s).mono (S.𝓕.mono s.isLt.le)).measurable measurable_const
  exact h1.inter h2

/-- Cochrane (2023), §16.10.2, p. 389, on a probability space: the ACK regime with constant
velocity — positive adapted inflation, (16.25) almost surely, the zero bound, the Taylor rule
until and including the first exceedance of `Π_U`, the money rule `Π_{t+1} = μ` from then on
(state by state). -/
def MeasACK (r : ℝ) (Φ : ℝ → ℝ) (PiU μ : ℝ) (infl i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < infl t ω) ∧ StronglyAdapted S.𝓕 infl ∧
    (∀ t, (fun ω => 1 / (1 + i t ω)) =ᵐ[S.μ] (1 + r)⁻¹ • S.E t (fun ω => 1 / infl (t + 1) ω)) ∧
    (∀ t ω, 0 ≤ i t ω) ∧
    (∀ t ω, (∀ s < t, infl s ω ≤ PiU) → 1 + i t ω = (1 + r) * Φ (infl t ω)) ∧
    ∀ t ω, (∃ s ≤ t, PiU < infl s ω) → infl (t + 1) ω = μ

/-- Cochrane (2023), §16.10.2, p. 389, "an equilibrium cannot form at period `T`", almost
surely and with no pull-out or information hypothesis: if `Φ(Π) ≠ μ` above `Π_U` and inflation
is bounded below by `lo > 0`, almost surely no date ever has `Π_t > Π_U`. -/
theorem meas_ack_bounded {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {PiU μ lo : ℝ} (hlo : 0 < lo)
    (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) {infl i : ℕ → Ω → ℝ} (h : MeasACK S r Φ PiU μ infl i)
    (hlow : ∀ t ω, lo ≤ infl t ω) : ∀ᵐ ω ∂S.μ, ∀ t, infl t ω ≤ PiU := by
  obtain ⟨hpos, had, hbp, -, htay, hmon⟩ := h
  have hnot : ∀ t, ∀ᵐ ω ∂S.μ, ω ∉ firstSet infl PiU t := by
    intro t
    have hA := measurableSet_firstSet S had PiU t
    set a : Ω → ℝ := (firstSet infl PiU t).indicator (fun _ => 1) with ha
    have ham : StronglyMeasurable[S.𝓕 t] a := stronglyMeasurable_const.indicator hA
    have habs : ∀ ω, |a ω| ≤ 1 := fun ω => by
      simp only [ha, Set.indicator]; split_ifs <;> simp
    set g : Ω → ℝ := fun ω => 1 / infl (t + 1) ω with hg
    have hgm : Measurable g := ((had (t + 1)).mono (S.𝓕.le _)).measurable.const_div 1
    have hgi : Integrable g S.μ := integrable_of_bdd S hgm (C := 1 / lo) fun ω => by
      rw [abs_of_pos (one_div_pos.mpr (hpos _ _))]
      exact one_div_le_one_div_of_le hlo (hlow _ _)
    have hai : Integrable a S.μ :=
      integrable_of_bdd S ((ham.mono (S.𝓕.le t)).measurable) habs
    have hpo := S.E_pullOut ham (Eventually.of_forall habs) hgi
    have hprod : a * g = (1 / μ) • a := by
      funext ω
      simp only [ha, hg, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, Set.indicator]
      split_ifs with hc
      · rw [hmon t ω ⟨t, le_rfl, hc.1⟩]; ring
      · ring
    have hk := S.E_smul (1 / μ) a t
    have hknown : S.E t a = a := S.E_of_stronglyMeasurable ham hai
    filter_upwards [hpo, hk, hbp t] with ω e1 e2 e3 hω
    rw [hprod, e2, hknown] at e1
    have haω : a ω = 1 := by simp only [ha, Set.indicator_of_mem hω]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, haω, mul_one, one_mul] at e1
    simp only [Pi.smul_apply, smul_eq_mul] at e3
    have hE := E_inv_pt hr e3 (htay t ω hω.2)
    rw [← hg] at hE
    rw [hE, one_div, one_div, inv_inj] at e1
    exact hΦμ _ hω.1 e1.symm
  filter_upwards [ae_all_iff.mpr hnot] with ω hω t
  by_contra hcon
  push Not at hcon
  classical
  have hex : ∃ T, PiU < infl T ω := ⟨t, hcon⟩
  exact hω (Nat.find hex) ⟨Nat.find_spec hex, fun s hs => not_lt.mp (Nat.find_min hex hs)⟩

/-- Cochrane (2023), §16.10.2, p. 389 and §16.10.5, almost surely: if
`E_t(1/Π_{t+1}) = 1/Φ(Π_t)` a.s., inflation is measurable, bounded below by `lo > 0` and almost
surely below `Π_U` at every date, and the rule satisfies `TidyR6StochasticPatches.GapAbove`
with `c > 1`, then `Π_t ≤ Π*` almost surely at every date. -/
theorem le_of_gapAbove_ae {Φ : ℝ → ℝ} {Pis PiU c lo : ℝ} (hPis : 0 < Pis) (hlo : 0 < lo)
    (hc : 1 < c) (hgap : GapAbove Φ Pis PiU c) {infl : ℕ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (infl t)) (hlow : ∀ t ω, lo ≤ infl t ω)
    (hbd : ∀ᵐ ω ∂S.μ, ∀ t, infl t ω ≤ PiU)
    (hdyn : ∀ t, S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun ω => 1 / Φ (infl t ω)) :
    ∀ t, ∀ᵐ ω ∂S.μ, infl t ω ≤ Pis := by
  have hpos : ∀ t ω, 0 < infl t ω := fun t ω => lt_of_lt_of_le hlo (hlow t ω)
  set D : ℕ → Ω → ℝ := fun t ω => max (1 / Pis - 1 / infl t ω) 0 with hD
  have hDB : ∀ t ω, D t ω ≤ 1 / Pis := fun t ω => by
    have := one_div_pos.mpr (hpos t ω)
    exact max_le (by linarith) (one_div_pos.mpr hPis).le
  have hfm : ∀ t, Measurable (fun ω => 1 / infl t ω) := fun t => (hmeas t).const_div 1
  have hDm : ∀ t, AEStronglyMeasurable (D t) S.μ := fun t =>
    ((measurable_const.sub (hfm t)).max measurable_const).aestronglyMeasurable
  have hDi : ∀ t, Integrable (D t) S.μ := fun t =>
    Integrable.of_bound (hDm t) (1 / Pis) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]; exact hDB t ω)
  have hgi : ∀ t, Integrable (fun ω => 1 / infl t ω) S.μ := fun t =>
    integrable_of_bdd S (hfm t) (C := 1 / lo) fun ω => by
      rw [abs_of_pos (one_div_pos.mpr (hpos t ω))]
      exact one_div_le_one_div_of_le hlo (hlow t ω)
  have hg : ∀ t, ∀ᵐ ω ∂S.μ, c * D t ω ≤ S.E t (D (t + 1)) ω := by
    intro t
    have hnn := S.E_mono (integrable_const 0) (hDi (t + 1))
      (Eventually.of_forall fun ω => le_max_right _ _) t
    have hm := S.E_mono ((integrable_const (1 / Pis)).sub (hgi (t + 1))) (hDi (t + 1))
      (Eventually.of_forall fun ω => le_max_left _ _) t
    have hsub := S.E_sub (integrable_const (1 / Pis)) (hgi (t + 1)) t
    filter_upwards [hdyn t, hnn, hm, hsub, hbd] with ω e1 e2 e3 e4 hb
    rw [S.E_const] at e2
    by_cases hx : infl t ω ≤ Pis
    · have : D t ω = 0 := by
        simp only [hD]
        apply max_eq_right
        rw [sub_nonpos]
        exact one_div_le_one_div_of_le (hpos t ω) hx
      rw [this, mul_zero]
      exact e2
    · push Not at hx
      have hgp := hgap _ hx.le (hb t)
      have hDt : D t ω = 1 / Pis - 1 / infl t ω := by
        simp only [hD]
        apply max_eq_left
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hPis hx.le
      have e5 : S.E t ((fun _ => 1 / Pis) - fun ω => 1 / infl (t + 1) ω) ω =
          1 / Pis - 1 / Φ (infl t ω) := by rw [e4, Pi.sub_apply, e1, S.E_const]
      rw [e5] at e3
      rw [hDt]
      linarith
  have hz := growth_zero_ae S hc hDm (fun t => Eventually.of_forall fun ω => le_max_right _ _)
    (fun t => Eventually.of_forall fun ω => hDB t ω) hg
  intro t
  filter_upwards [hz t] with ω h0
  have h0' : max (1 / Pis - 1 / infl t ω) 0 = 0 := h0
  have h1 : 1 / Pis - 1 / infl t ω ≤ 0 := by rw [← h0']; exact le_max_left _ _
  have := hpos t ω
  by_contra hcon
  push Not at hcon
  have : 1 / infl t ω < 1 / Pis := one_div_lt_one_div_of_lt hPis hcon
  linarith

/-- Cochrane (2023), §16.10.2, p. 389, "the ACK regime prunes the inflationary equilibria", on a
probability space with no pull-out or information hypothesis: with `Φ(Π) ≠ μ` above `Π_U`, a
rule satisfying `TidyR6StochasticPatches.GapAbove` with `c > 1` and inflation bounded below by
`lo > 0`, every equilibrium — sunspot equilibria with infinitely many shocks included — has
`Π_t ≤ Π*` almost surely at every date. -/
theorem meas_ack_prunes_inflation {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {Pis PiU μ c lo : ℝ}
    (hPis : 0 < Pis) (hlo : 0 < lo) (hc : 1 < c) (hgap : GapAbove Φ Pis PiU c)
    (hΦμ : ∀ x, PiU < x → Φ x ≠ μ) {infl i : ℕ → Ω → ℝ} (h : MeasACK S r Φ PiU μ infl i)
    (hlow : ∀ t ω, lo ≤ infl t ω) : ∀ t, ∀ᵐ ω ∂S.μ, infl t ω ≤ Pis := by
  have hall := meas_ack_bounded S hr hlo hΦμ h hlow
  obtain ⟨-, had, hbp, -, htay, -⟩ := h
  refine le_of_gapAbove_ae S hPis hlo hc hgap (fun t => ((had t).mono (S.𝓕.le t)).measurable)
    hlow hall fun t => ?_
  filter_upwards [hall, hbp t] with ω h1 h2
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  exact E_inv_pt hr h2 (htay t ω fun s _ => h1 s)

/-! ## Fiscal trimming almost surely -/

/-- Cochrane (2023), §16.10.3, p. 390 (Benhabib, Schmitt-Grohé and Uribe), on a probability space
with no pull-out or information hypothesis: let real debt follow
`b_{t+1} = (1 + i_t)(1 − θ(Π_t))b_t/Π_{t+1}` with `θ` measurable, inflation, rates and debt
adapted, `Π ≥ lo > 0`, `i ≥ 0`, (16.25) almost surely, `0 ≤ b_t` bounded and
`(1 + i_t)(1 − θ(Π_t))b_t` bounded at each date. If `θ(Π_t) ≤ θ̄ < 0` in every state from date
`T` on, then almost surely, wherever `E_0b_T > 0`, the discounted expected debt `βᵗE_0b_t`
diverges: the transversality condition fails. -/
theorem meas_bsgu_tvc_violated {r : ℝ} (hr : 0 < 1 + r) {θ : ℝ → ℝ} (hθm : Measurable θ)
    {θbar lo : ℝ} (hθbar : θbar < 0) (hlo : 0 < lo) {T : ℕ} {infl i b : ℕ → Ω → ℝ}
    (hπad : StronglyAdapted S.𝓕 infl) (hiad : StronglyAdapted S.𝓕 i)
    (hbad : StronglyAdapted S.𝓕 b) (hlow : ∀ t ω, lo ≤ infl t ω)
    (hbp : ∀ t, (fun ω => 1 / (1 + i t ω)) =ᵐ[S.μ]
      (1 + r)⁻¹ • S.E t (fun ω => 1 / infl (t + 1) ω))
    (hi : ∀ t ω, 0 ≤ i t ω)
    (hflow : ∀ t ω, b (t + 1) ω = (1 + i t ω) * (1 - θ (infl t ω)) * b t ω / infl (t + 1) ω)
    (hkb : ∀ t, ∃ C, ∀ ω, |(1 + i t ω) * (1 - θ (infl t ω)) * b t ω| ≤ C)
    (hb : ∀ t ω, 0 ≤ b t ω) (hbB : ∀ t, ∃ C, ∀ ω, b t ω ≤ C)
    (hθ : ∀ t, T ≤ t → ∀ ω, θ (infl t ω) ≤ θbar) :
    ∀ᵐ ω ∂S.μ, 0 < S.E 0 (b T) ω →
      Tendsto (fun t => ((1 + r)⁻¹) ^ t * S.E 0 (b t) ω) atTop atTop := by
  have hpos : ∀ t ω, 0 < infl t ω := fun t ω => lt_of_lt_of_le hlo (hlow t ω)
  have hbi : ∀ t, Integrable (b t) S.μ := fun t => by
    obtain ⟨C, hC⟩ := hbB t
    exact integrable_of_bdd S ((hbad t).mono (S.𝓕.le t)).measurable (C := C) fun ω => by
      rw [abs_of_nonneg (hb t ω)]; exact hC ω
  -- `(1 − θ(Π_t))b_t` is measurable and bounded
  have hmi : ∀ t, Integrable (fun ω => (1 - θ (infl t ω)) * b t ω) S.μ := fun t => by
    obtain ⟨C, hC⟩ := hkb t
    refine integrable_of_bdd S ((measurable_const.sub (hθm.comp
      ((hπad t).mono (S.𝓕.le t)).measurable)).mul ((hbad t).mono (S.𝓕.le t)).measurable)
      (C := C) fun ω => ?_
    have h1 : 1 ≤ 1 + i t ω := by linarith [hi t ω]
    have := hC ω
    rw [mul_assoc, abs_mul, abs_of_pos (by linarith)] at this
    nlinarith [abs_nonneg ((1 - θ (infl t ω)) * b t ω)]
  have hstep : ∀ t, T ≤ t → ∀ᵐ ω ∂S.μ,
      (1 + r) * (1 - θbar) * S.E 0 (b t) ω ≤ S.E 0 (b (t + 1)) ω := by
    intro t ht
    set k : Ω → ℝ := fun ω => (1 + i t ω) * (1 - θ (infl t ω)) * b t ω with hkdef
    have hkm : StronglyMeasurable[S.𝓕 t] k :=
      (((measurable_const.add (hiad t).measurable).mul (measurable_const.sub
        (hθm.comp (hπad t).measurable))).mul (hbad t).measurable).stronglyMeasurable
    obtain ⟨C, hC⟩ := hkb t
    have hgi : Integrable (fun ω => 1 / infl (t + 1) ω) S.μ :=
      integrable_of_bdd S (((hπad (t + 1)).mono (S.𝓕.le _)).measurable.const_div 1)
        (C := 1 / lo) fun ω => by
          rw [abs_of_pos (one_div_pos.mpr (hpos _ _))]
          exact one_div_le_one_div_of_le hlo (hlow _ _)
    have hpo := S.E_pullOut hkm (Eventually.of_forall hC) hgi
    have he : b (t + 1) = k * fun ω => 1 / infl (t + 1) ω := by
      funext ω; rw [hflow]; simp only [hkdef, Pi.mul_apply]; ring
    -- `E_t b_{t+1} = (1 + r)(1 − θ(Π_t))b_t` almost surely
    have hEt : S.E t (b (t + 1)) =ᵐ[S.μ] fun ω => (1 + r) * ((1 - θ (infl t ω)) * b t ω) := by
      rw [he]
      filter_upwards [hpo, hbp t] with ω e1 e2
      rw [e1]
      simp only [Pi.smul_apply, smul_eq_mul] at e2
      have h1 : 0 < 1 + i t ω := by linarith [hi t ω]
      have hE : S.E t (fun ω => 1 / infl (t + 1) ω) ω = (1 + r) / (1 + i t ω) := by
        field_simp at e2 ⊢
        linarith
      simp only [Pi.mul_apply, hE, hkdef]
      field_simp
    have h0 := S.E_tower (Nat.zero_le t) (b (t + 1))
    have h1 := S.E_congr hEt 0
    have hle : (fun ω => (1 + r) * (1 - θbar) * b t ω) ≤ᵐ[S.μ]
        fun ω => (1 + r) * ((1 - θ (infl t ω)) * b t ω) :=
      Eventually.of_forall fun ω => by
        have := mul_le_mul_of_nonneg_right (by linarith [hθ t ht ω] :
          1 - θbar ≤ 1 - θ (infl t ω)) (hb t ω)
        nlinarith
    have h2 := S.E_mono ((hbi t).const_mul ((1 + r) * (1 - θbar)))
      ((hmi t).const_mul (1 + r)) hle 0
    have h3 := S.E_smul ((1 + r) * (1 - θbar)) (b t) 0
    filter_upwards [h0, h1, h2, h3] with ω e0 e1 e2 e3
    have e4 : S.E 0 (fun ω => (1 + r) * (1 - θbar) * b t ω) ω =
        (1 + r) * (1 - θbar) * S.E 0 (b t) ω := by
      have : (fun ω => (1 + r) * (1 - θbar) * b t ω) = ((1 + r) * (1 - θbar)) • b t := rfl
      rw [this, e3]; rfl
    rw [← e0, e1]
    rw [e4] at e2
    exact e2
  have hall : ∀ᵐ ω ∂S.μ, ∀ t, T ≤ t →
      (1 + r) * (1 - θbar) * S.E 0 (b t) ω ≤ S.E 0 (b (t + 1)) ω := by
    rw [ae_all_iff]
    intro t
    by_cases ht : T ≤ t
    · filter_upwards [hstep t ht] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h ht
  filter_upwards [hall] with ω hω hT
  have hβ : ∀ t, 0 < ((1 + r)⁻¹) ^ t := fun t => pow_pos (inv_pos.mpr hr) t
  refine tendsto_of_growth (q := 1 - θbar) (by linarith) (mul_pos (hβ T) hT) fun t ht => ?_
  have := hω t ht
  rw [pow_succ]
  have e : ((1 + r)⁻¹) ^ t * (1 + r)⁻¹ * ((1 + r) * (1 - θbar) * S.E 0 (b t) ω) =
      (1 - θbar) * (((1 + r)⁻¹) ^ t * S.E 0 (b t) ω) := by field_simp
  rw [← e]
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- Cochrane (2023), §16.10.3, p. 390, Woodford's `μ̄` rule on a probability space with no
pull-out or information hypothesis: with nominal liabilities `D_{t+1} = μ̄D_t`, prices
`P_{t+1} = Π_{t+1}P_t > 0`, adapted `Π`, `P`, `D`, `D ≥ 0`, real liabilities `v_t = D_t/P_t`
bounded at each date, `Π ≥ lo > 0`, and `E_t(1/Π_{t+1}) = 1/Φ(Π_t)` almost surely: if
`0 < Φ(Π_t) ≤ βμ̄` in every state from date `T` on, then almost surely, wherever
`E_0v_T > 0`, `βᵗE_0v_t` does not tend to zero. -/
theorem meas_mubar_tvc_violated {r μ lo : ℝ} (hr : 0 < 1 + r) (hlo : 0 < lo) {Φ : ℝ → ℝ}
    {T : ℕ} {infl P D : ℕ → Ω → ℝ} (hπad : StronglyAdapted S.𝓕 infl)
    (hPad : StronglyAdapted S.𝓕 P) (hDad : StronglyAdapted S.𝓕 D)
    (hlow : ∀ t ω, lo ≤ infl t ω) (hP : ∀ t ω, 0 < P t ω)
    (hPs : ∀ t ω, P (t + 1) ω = infl (t + 1) ω * P t ω) (hD : ∀ t ω, D (t + 1) ω = μ * D t ω)
    (hv : ∀ t ω, 0 ≤ D t ω) (hvB : ∀ t, ∃ C, ∀ ω, D t ω / P t ω ≤ C)
    (hdyn : ∀ t, S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun ω => 1 / Φ (infl t ω))
    (hle : ∀ t, T ≤ t → ∀ ω, 0 < Φ (infl t ω) ∧ Φ (infl t ω) ≤ (1 + r)⁻¹ * μ) :
    ∀ᵐ ω ∂S.μ, 0 < S.E 0 (fun ω => D T ω / P T ω) ω →
      ¬ Tendsto (fun t => ((1 + r)⁻¹) ^ t * S.E 0 (fun ω => D t ω / P t ω) ω) atTop (𝓝 0) := by
  have hpos : ∀ t ω, 0 < infl t ω := fun t ω => lt_of_lt_of_le hlo (hlow t ω)
  have hvm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => D t ω / P t ω) := fun t =>
    ((hDad t).measurable.div (hPad t).measurable).stronglyMeasurable
  have hvi : ∀ t, Integrable (fun ω => D t ω / P t ω) S.μ := fun t => by
    obtain ⟨C, hC⟩ := hvB t
    exact integrable_of_bdd S ((hvm t).mono (S.𝓕.le t)).measurable (C := C) fun ω => by
      rw [abs_of_nonneg (div_nonneg (hv t ω) (hP t ω).le)]; exact hC ω
  have hstep : ∀ t, T ≤ t → ∀ᵐ ω ∂S.μ,
      (1 + r) * S.E 0 (fun ω => D t ω / P t ω) ω ≤ S.E 0 (fun ω => D (t + 1) ω / P (t + 1) ω) ω :=
      by
    intro t ht
    obtain ⟨C, hC⟩ := hvB t
    have hkm : StronglyMeasurable[S.𝓕 t] (fun ω => μ * (D t ω / P t ω)) :=
      ((hvm t).measurable.const_mul μ).stronglyMeasurable
    have hkb : ∀ ω, |μ * (D t ω / P t ω)| ≤ |μ| * C := fun ω => by
      rw [abs_mul, abs_of_nonneg (div_nonneg (hv t ω) (hP t ω).le)]
      exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg μ)
    have hgi : Integrable (fun ω => 1 / infl (t + 1) ω) S.μ :=
      integrable_of_bdd S (((hπad (t + 1)).mono (S.𝓕.le _)).measurable.const_div 1)
        (C := 1 / lo) fun ω => by
          rw [abs_of_pos (one_div_pos.mpr (hpos _ _))]
          exact one_div_le_one_div_of_le hlo (hlow _ _)
    have hpo := S.E_pullOut hkm (Eventually.of_forall hkb) hgi
    have he : (fun ω => D (t + 1) ω / P (t + 1) ω) =
        (fun ω => μ * (D t ω / P t ω)) * fun ω => 1 / infl (t + 1) ω := by
      funext ω
      rw [hD, hPs]
      simp only [Pi.mul_apply]
      have := (hP t ω).ne'
      have := (hpos (t + 1) ω).ne'
      field_simp
    have hEt : (fun ω => (1 + r) * (D t ω / P t ω)) ≤ᵐ[S.μ]
        S.E t (fun ω => D (t + 1) ω / P (t + 1) ω) := by
      rw [he]
      filter_upwards [hpo, hdyn t] with ω e1 e2
      rw [e1]
      simp only [Pi.mul_apply, e2]
      obtain ⟨h1, h2⟩ := hle t ht ω
      have hvv : 0 ≤ D t ω / P t ω := div_nonneg (hv t ω) (hP t ω).le
      have : 1 + r ≤ μ * (1 / Φ (infl t ω)) := by
        rw [mul_one_div, le_div_iff₀ h1]
        have := mul_le_mul_of_nonneg_left h2 hr.le
        rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
        exact this
      nlinarith
    have h2 := S.E_mono ((hvi t).const_mul (1 + r)) (S.integrable_E _ _) hEt 0
    have h0 := S.E_tower (Nat.zero_le t) (fun ω => D (t + 1) ω / P (t + 1) ω)
    have h3 := S.E_smul (1 + r) (fun ω => D t ω / P t ω) 0
    filter_upwards [h0, h2, h3] with ω e0 e2 e3
    rw [e0] at e2
    have e4 : S.E 0 (fun ω => (1 + r) * (D t ω / P t ω)) ω =
        (1 + r) * S.E 0 (fun ω => D t ω / P t ω) ω := by
      have : (fun ω => (1 + r) * (D t ω / P t ω)) = (1 + r) • fun ω => D t ω / P t ω := rfl
      rw [this, e3]; rfl
    rw [e4] at e2
    exact e2
  have hall : ∀ᵐ ω ∂S.μ, ∀ t, T ≤ t → (1 + r) * S.E 0 (fun ω => D t ω / P t ω) ω ≤
      S.E 0 (fun ω => D (t + 1) ω / P (t + 1) ω) ω := by
    rw [ae_all_iff]
    intro t
    by_cases ht : T ≤ t
    · filter_upwards [hstep t ht] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h ht
  filter_upwards [hall] with ω hω hT
  refine not_tendsto_zero_of_mono (mul_pos (pow_pos (inv_pos.mpr hr) T) hT) fun t ht => ?_
  rw [pow_succ]
  have hβ : 0 < ((1 + r)⁻¹) ^ t := pow_pos (inv_pos.mpr hr) t
  calc ((1 + r)⁻¹) ^ t * S.E 0 (fun ω => D t ω / P t ω) ω
      = ((1 + r)⁻¹) ^ t * (1 + r)⁻¹ * ((1 + r) * S.E 0 (fun ω => D t ω / P t ω) ω) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (hω t ht) (by positivity)

/-- Cochrane (2023), §16.10.6, p. 394 (Sims 1994), on a probability space with no pull-out or
information hypothesis: with nominal money `M_t ≥ M̲ > 0`, prices `P_{t+1} = Π_{t+1}P_t > 0`,
adapted `Π`, `P`, `M`, `1/P_t` and `M_t/P_t` bounded at each date, `Π ≥ lo > 0`, and the zero
bound reached from date `T` on (`E_t(1/Π_{t+1}) = 1 + r` almost surely), then almost surely,
wherever `E_0(1/P_T) > 0`, `βᵗE_0[M_t/P_t]` does not tend to zero. -/
theorem meas_sims_tvc_violated {r Mlow lo : ℝ} (hr : 0 < 1 + r) (hM0 : 0 < Mlow) (hlo : 0 < lo)
    {T : ℕ} {infl P M : ℕ → Ω → ℝ} (hπad : StronglyAdapted S.𝓕 infl)
    (hPad : StronglyAdapted S.𝓕 P) (hMad : StronglyAdapted S.𝓕 M)
    (hlow : ∀ t ω, lo ≤ infl t ω) (hP : ∀ t ω, 0 < P t ω)
    (hPs : ∀ t ω, P (t + 1) ω = infl (t + 1) ω * P t ω) (hM : ∀ t ω, Mlow ≤ M t ω)
    (hwB : ∀ t, ∃ C, ∀ ω, 1 / P t ω ≤ C) (hmB : ∀ t, ∃ C, ∀ ω, M t ω / P t ω ≤ C)
    (hzb : ∀ t, T ≤ t → S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun _ => 1 + r) :
    ∀ᵐ ω ∂S.μ, 0 < S.E 0 (fun ω => 1 / P T ω) ω →
      ¬ Tendsto (fun t => ((1 + r)⁻¹) ^ t * S.E 0 (fun ω => M t ω / P t ω) ω) atTop (𝓝 0) := by
  have hpos : ∀ t ω, 0 < infl t ω := fun t ω => lt_of_lt_of_le hlo (hlow t ω)
  have hwm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => 1 / P t ω) := fun t =>
    ((hPad t).measurable.const_div 1).stronglyMeasurable
  have hwi : ∀ t, Integrable (fun ω => 1 / P t ω) S.μ := fun t => by
    obtain ⟨C, hC⟩ := hwB t
    exact integrable_of_bdd S ((hwm t).mono (S.𝓕.le t)).measurable (C := C) fun ω => by
      rw [abs_of_pos (one_div_pos.mpr (hP t ω))]; exact hC ω
  have hmi : ∀ t, Integrable (fun ω => M t ω / P t ω) S.μ := fun t => by
    obtain ⟨C, hC⟩ := hmB t
    exact integrable_of_bdd S (((hMad t).mono (S.𝓕.le t)).measurable.div
      ((hPad t).mono (S.𝓕.le t)).measurable) (C := C) fun ω => by
        rw [abs_of_pos (div_pos (lt_of_lt_of_le hM0 (hM t ω)) (hP t ω))]; exact hC ω
  -- the discounted mean of `1/P_t` is constant from `T` on
  have hstep : ∀ t, T ≤ t → ∀ᵐ ω ∂S.μ,
      S.E 0 (fun ω => 1 / P (t + 1) ω) ω = (1 + r) * S.E 0 (fun ω => 1 / P t ω) ω := by
    intro t ht
    obtain ⟨C, hC⟩ := hwB t
    have hgi : Integrable (fun ω => 1 / infl (t + 1) ω) S.μ :=
      integrable_of_bdd S (((hπad (t + 1)).mono (S.𝓕.le _)).measurable.const_div 1)
        (C := 1 / lo) fun ω => by
          rw [abs_of_pos (one_div_pos.mpr (hpos _ _))]
          exact one_div_le_one_div_of_le hlo (hlow _ _)
    have hpo := S.E_pullOut (hwm t) (C := C) (Eventually.of_forall fun ω => by
      rw [abs_of_pos (one_div_pos.mpr (hP t ω))]; exact hC ω) hgi
    have he : (fun ω => 1 / P (t + 1) ω) =
        (fun ω => 1 / P t ω) * fun ω => 1 / infl (t + 1) ω := by
      funext ω
      rw [hPs]
      simp only [Pi.mul_apply]
      rw [one_div_mul_one_div, mul_comm]
    have hEt : S.E t (fun ω => 1 / P (t + 1) ω) =ᵐ[S.μ] (1 + r) • fun ω => 1 / P t ω := by
      rw [he]
      filter_upwards [hpo, hzb t ht] with ω e1 e2
      rw [e1]
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, e2]
      ring
    have h0 := S.E_tower (Nat.zero_le t) (fun ω => 1 / P (t + 1) ω)
    have h1 := S.E_congr hEt 0
    have h3 := S.E_smul (1 + r) (fun ω => 1 / P t ω) 0
    filter_upwards [h0, h1, h3] with ω e0 e1 e3
    rw [← e0, e1, e3]
    rfl
  have hlowE : ∀ t, ∀ᵐ ω ∂S.μ,
      Mlow * S.E 0 (fun ω => 1 / P t ω) ω ≤ S.E 0 (fun ω => M t ω / P t ω) ω := by
    intro t
    have hle : Mlow • (fun ω => 1 / P t ω) ≤ᵐ[S.μ] fun ω => M t ω / P t ω :=
      Eventually.of_forall fun ω => by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (hM t ω) (hP t ω).le
    have h2 := S.E_mono ((hwi t).smul Mlow) (hmi t) hle 0
    have h3 := S.E_smul Mlow (fun ω => 1 / P t ω) 0
    filter_upwards [h2, h3] with ω e2 e3
    rw [e3] at e2
    exact e2
  have hall : ∀ᵐ ω ∂S.μ, (∀ t, T ≤ t →
      S.E 0 (fun ω => 1 / P (t + 1) ω) ω = (1 + r) * S.E 0 (fun ω => 1 / P t ω) ω) ∧
      ∀ t, Mlow * S.E 0 (fun ω => 1 / P t ω) ω ≤ S.E 0 (fun ω => M t ω / P t ω) ω := by
    refine (ae_all_iff.mpr fun t => ?_).and (ae_all_iff.mpr hlowE)
    by_cases ht : T ≤ t
    · filter_upwards [hstep t ht] with ω h _ using h
    · exact Eventually.of_forall fun ω h => absurd h ht
  filter_upwards [hall] with ω ⟨hω, hω2⟩ hT
  have hconst : ∀ n, ((1 + r)⁻¹) ^ (T + n) * S.E 0 (fun ω => 1 / P (T + n) ω) ω =
      ((1 + r)⁻¹) ^ T * S.E 0 (fun ω => 1 / P T ω) ω := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [← add_assoc, hω _ (Nat.le_add_right T n), pow_succ, ← ih]
      field_simp
  intro hlim
  have hpos0 : 0 < Mlow * (((1 + r)⁻¹) ^ T * S.E 0 (fun ω => 1 / P T ω) ω) :=
    mul_pos hM0 (mul_pos (pow_pos (inv_pos.mpr hr) T) hT)
  have h2 := (tendsto_add_atTop_iff_nat T).mpr hlim
  have := ge_of_tendsto h2 (Eventually.of_forall fun n => by
    have h3 := mul_le_mul_of_nonneg_left (hω2 (T + n))
      (pow_pos (inv_pos.mpr hr) (T + n)).le
    rw [show ((1 + r)⁻¹) ^ (T + n) * (Mlow * S.E 0 (fun ω => 1 / P (T + n) ω) ω) =
      Mlow * (((1 + r)⁻¹) ^ (T + n) * S.E 0 (fun ω => 1 / P (T + n) ω) ω) by ring,
      hconst n] at h3
    simpa only [Nat.add_comm n T] using h3)
  linarith

/-! ## (16.31)–(16.32) almost surely -/

/-- Cochrane (2023), eqs. (16.31)–(16.32), p. 393, on a probability space with no pull-out or
information hypothesis: if inflation is adapted and positive, `k` measurable with
`k(Π_t) > 0` and `1/k(Π_t)` bounded at each date, `k(Π_{t+1})/Π_{t+1}` integrable,
`Φ(Π_t) > 0`, the rule `1 + i_t = Φ(Π_t)/β` and the stochastic (16.31)
`1/(1 + i_t) = βE_t[(k(Π_{t+1})/k(Π_t))/Π_{t+1}]` almost surely, then the stochastic (16.32)
`E_t[k(Π_{t+1})/Π_{t+1}] = k(Π_t)/Φ(Π_t)` holds almost surely. -/
theorem meas_stochEq1632_of_bond {β : ℝ} (hβ : 0 < β) {Φ k : ℝ → ℝ} (hkm : Measurable k)
    {infl i : ℕ → Ω → ℝ} (hπad : StronglyAdapted S.𝓕 infl)
    (hk0 : ∀ t ω, 0 < k (infl t ω)) (hΦ0 : ∀ t ω, 0 < Φ (infl t ω))
    (hkB : ∀ t, ∃ C, ∀ ω, 1 / k (infl t ω) ≤ C)
    (hhi : ∀ t, Integrable (fun ω => k (infl (t + 1) ω) / infl (t + 1) ω) S.μ)
    (hrule : ∀ t ω, 1 + i t ω = Φ (infl t ω) / β)
    (hbond : ∀ t, (fun ω => 1 / (1 + i t ω)) =ᵐ[S.μ]
      β • S.E t (fun ω => k (infl (t + 1) ω) / k (infl t ω) / infl (t + 1) ω)) :
    ∀ t, S.E t (fun ω => k (infl (t + 1) ω) / infl (t + 1) ω) =ᵐ[S.μ]
      fun ω => k (infl t ω) / Φ (infl t ω) := by
  intro t
  obtain ⟨C, hC⟩ := hkB t
  have hfm : StronglyMeasurable[S.𝓕 t] (fun ω => 1 / k (infl t ω)) :=
    ((hkm.comp (hπad t).measurable).const_div 1).stronglyMeasurable
  have hpo := S.E_pullOut hfm (C := C) (Eventually.of_forall fun ω => by
    rw [abs_of_pos (one_div_pos.mpr (hk0 t ω))]; exact hC ω) (hhi t)
  have e : (fun ω => k (infl (t + 1) ω) / k (infl t ω) / infl (t + 1) ω) =
      (fun ω => 1 / k (infl t ω)) * fun ω => k (infl (t + 1) ω) / infl (t + 1) ω := by
    funext ω; simp only [Pi.mul_apply]; ring
  filter_upwards [hbond t, hpo] with ω e1 e2
  have e3 : S.E t (fun ω => k (infl (t + 1) ω) / k (infl t ω) / infl (t + 1) ω) ω =
      ((fun ω => 1 / k (infl t ω)) * S.E t (fun ω => k (infl (t + 1) ω) / infl (t + 1) ω)) ω := by
    rw [e]; exact e2
  simp only [Pi.smul_apply, smul_eq_mul] at e1
  rw [e3] at e1
  simp only [Pi.mul_apply, hrule] at e1
  have hk := (hk0 t ω).ne'
  have hΦ := (hΦ0 t ω).ne'
  field_simp at e1
  field_simp
  linarith

/-- Cochrane (2023), (16.32), p. 393: in the bounded-rule model, for `Π ∈ (1, 3/2)`,
`k(Π)/Φ(Π) < 1/4`. -/
theorem boundedRule_rhs_lt {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) (3 / 2)) :
    SelectionPatches.ucMoney (SelectionPatches.moneyDemand (SelectionPatches.boundedRate x)) /
      SelectionPatches.boundedRule x < 1 / 4 := by
  obtain ⟨hx1, hx2⟩ := hx
  have hrule : SelectionPatches.boundedRule x = 2 * x - 1 := by
    unfold SelectionPatches.boundedRule
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  simp only [SelectionPatches.ucMoney, SelectionPatches.moneyDemand,
    SelectionPatches.boundedRate]
  rw [hrule, div_div, div_lt_div_iff₀ (by nlinarith) (by norm_num), one_mul]
  nlinarith

/-- Cochrane (2023), (16.32), p. 393, "may rise to require `Π_{t+1} = ∞`", on a probability
space: in the bounded-rule model, if `Π_{t+1}` is positive with positive money demand in every
state, `k(Π_{t+1})/Π_{t+1}` is integrable and the stochastic (16.32) holds almost surely at `t`,
then `Π_t ∉ (1, 3/2)` almost surely: no equilibrium, sunspots with infinitely many shocks
included, ever reaches that region with positive probability. -/
theorem meas_bounded_rule_explosion {infl : ℕ → Ω → ℝ} {t : ℕ}
    (hpos : ∀ ω, 0 < infl (t + 1) ω ∧
      0 < SelectionPatches.moneyDemand (SelectionPatches.boundedRate (infl (t + 1) ω)))
    (hhi : Integrable (fun ω => SelectionPatches.ucMoney (SelectionPatches.moneyDemand
      (SelectionPatches.boundedRate (infl (t + 1) ω))) / infl (t + 1) ω) S.μ)
    (heq : S.E t (fun ω => SelectionPatches.ucMoney (SelectionPatches.moneyDemand
      (SelectionPatches.boundedRate (infl (t + 1) ω))) / infl (t + 1) ω) =ᵐ[S.μ]
      fun ω => SelectionPatches.ucMoney (SelectionPatches.moneyDemand
        (SelectionPatches.boundedRate (infl t ω))) / SelectionPatches.boundedRule (infl t ω)) :
    ∀ᵐ ω ∂S.μ, infl t ω ∉ Set.Ioo (1 : ℝ) (3 / 2) := by
  have hm := S.E_mono (integrable_const (1 / 4 : ℝ)) hhi
    (Eventually.of_forall fun ω => boundedRule_h_ge (hpos ω).1 (hpos ω).2) t
  rw [S.E_const] at hm
  filter_upwards [hm, heq] with ω e1 e2 hx
  rw [e2] at e1
  linarith [boundedRule_rhs_lt hx]

/-! ## Deflations in mean -/

/-- Cochrane (2023), pp. 379–380, "trundle down gently to the zero bound", on a probability
space: if `E_t(1/Π_{t+1}) = 1/Φ(Π_t)` almost surely, inflation is measurable and stays in
`[Π_L, Π*]` (`Π_L > 0`) where `0 < Φ(Π) ≤ Π`, then `E[1/Π_t]` is nondecreasing and converges, and
the expected one-step gaps `E[1/Φ(Π_t) − 1/Π_t]` are nonnegative and summable. -/
theorem meas_deflation_mean {Φ : ℝ → ℝ} {PL Pis : ℝ} (hPL : 0 < PL)
    (hbelow : ∀ x, PL ≤ x → x ≤ Pis → Φ x ≤ x) (hΦpos : ∀ x, PL ≤ x → x ≤ Pis → 0 < Φ x)
    {infl : ℕ → Ω → ℝ} (hmeas : ∀ t, Measurable (infl t))
    (hdyn : ∀ t, S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun ω => 1 / Φ (infl t ω))
    (hmem : ∀ t ω, PL ≤ infl t ω ∧ infl t ω ≤ Pis) :
    Monotone (fun t => ∫ ω, 1 / infl t ω ∂S.μ) ∧
      (∃ L, Tendsto (fun t => ∫ ω, 1 / infl t ω ∂S.μ) atTop (𝓝 L)) ∧
      (∀ t, 0 ≤ ∫ ω, (1 / Φ (infl t ω) - 1 / infl t ω) ∂S.μ) ∧
      Summable (fun t => ∫ ω, (1 / Φ (infl t ω) - 1 / infl t ω) ∂S.μ) := by
  have hpos : ∀ t ω, 0 < infl t ω := fun t ω => lt_of_lt_of_le hPL (hmem t ω).1
  have hgi : ∀ t, Integrable (fun ω => 1 / infl t ω) S.μ := fun t =>
    integrable_of_bdd S ((hmeas t).const_div 1) (C := 1 / PL) fun ω => by
      rw [abs_of_pos (one_div_pos.mpr (hpos t ω))]
      exact one_div_le_one_div_of_le hPL (hmem t ω).1
  have hΦi : ∀ t, Integrable (fun ω => 1 / Φ (infl t ω)) S.μ := fun t =>
    (S.integrable_E t _).congr (hdyn t)
  have hstep : ∀ t, ∫ ω, 1 / infl (t + 1) ω ∂S.μ = ∫ ω, 1 / Φ (infl t ω) ∂S.μ := fun t => by
    rw [← S.integral_E t, integral_congr_ae (hdyn t)]
  have hgapnn : ∀ t ω, 0 ≤ 1 / Φ (infl t ω) - 1 / infl t ω := fun t ω => by
    obtain ⟨h1, h2⟩ := hmem t ω
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (hΦpos _ h1 h2) (hbelow _ h1 h2)
  have hgap : ∀ t, 0 ≤ ∫ ω, (1 / Φ (infl t ω) - 1 / infl t ω) ∂S.μ := fun t =>
    integral_nonneg (hgapnn t)
  have hdiff : ∀ t, ∫ ω, 1 / infl (t + 1) ω ∂S.μ - ∫ ω, 1 / infl t ω ∂S.μ =
      ∫ ω, (1 / Φ (infl t ω) - 1 / infl t ω) ∂S.μ := fun t => by
    rw [hstep t, integral_sub (hΦi t) (hgi t)]
  have hmono : Monotone (fun t => ∫ ω, 1 / infl t ω ∂S.μ) :=
    monotone_nat_of_le_succ fun t => by linarith [hdiff t, hgap t]
  have hbdd : ∀ t, ∫ ω, 1 / infl t ω ∂S.μ ≤ 1 / PL := fun t => by
    have := integral_mono (hgi t) (integrable_const (1 / PL)) fun ω =>
      one_div_le_one_div_of_le hPL (hmem t ω).1
    simpa using this
  refine ⟨hmono, ⟨_, tendsto_atTop_ciSup hmono ⟨1 / PL, by rintro _ ⟨t, rfl⟩; exact hbdd t⟩⟩,
    hgap, ?_⟩
  refine summable_of_sum_range_le hgap (c := 1 / PL - ∫ ω, 1 / infl 0 ω ∂S.μ) fun n => ?_
  have htel : ∑ t ∈ Finset.range n, ∫ ω, (1 / Φ (infl t ω) - 1 / infl t ω) ∂S.μ =
      ∫ ω, 1 / infl n ω ∂S.μ - ∫ ω, 1 / infl 0 ω ∂S.μ := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, ← hdiff n]; ring
  rw [htel]
  linarith [hbdd n]

/-! ## Online Appendix A3 under uncertainty -/

/-- Cochrane (2023), Online Appendix A3, §3.1.1, p. 614 (helicopter money, "the final,
transversality condition is violated"), on a probability space: with money growing at
`M_{t+1} = (1 + μ)M_t`, `μ > 0`, prices `P_{t+1} = Π_{t+1}P_t > 0`, adapted `Π`, `P`, `M`,
real money `M_t/P_t ≥ 0` bounded at each date, `Π ≥ lo > 0` and the zero bound
(`E_t(1/Π_{t+1}) = 1 + r` almost surely), almost surely, wherever `E_0[M_0/P_0] > 0`, the
discounted expected real money `βᵗE_0[M_t/P_t]` diverges. -/
theorem meas_a3_helicopter_tvc_violated {r μ lo : ℝ} (hr : 0 < 1 + r) (hμ : 0 < μ)
    (hlo : 0 < lo) {infl P M : ℕ → Ω → ℝ} (hπad : StronglyAdapted S.𝓕 infl)
    (hPad : StronglyAdapted S.𝓕 P) (hMad : StronglyAdapted S.𝓕 M)
    (hlow : ∀ t ω, lo ≤ infl t ω) (hP : ∀ t ω, 0 < P t ω)
    (hPs : ∀ t ω, P (t + 1) ω = infl (t + 1) ω * P t ω)
    (hMs : ∀ t ω, M (t + 1) ω = (1 + μ) * M t ω) (hM : ∀ t ω, 0 ≤ M t ω)
    (hmB : ∀ t, ∃ C, ∀ ω, M t ω / P t ω ≤ C)
    (hzb : ∀ t, S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun _ => 1 + r) :
    ∀ᵐ ω ∂S.μ, 0 < S.E 0 (fun ω => M 0 ω / P 0 ω) ω →
      Tendsto (fun t => ((1 + r)⁻¹) ^ t * S.E 0 (fun ω => M t ω / P t ω) ω) atTop atTop := by
  have hpos : ∀ t ω, 0 < infl t ω := fun t ω => lt_of_lt_of_le hlo (hlow t ω)
  have hmm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => M t ω / P t ω) := fun t =>
    ((hMad t).measurable.div (hPad t).measurable).stronglyMeasurable
  have hstep : ∀ t, ∀ᵐ ω ∂S.μ, S.E 0 (fun ω => M (t + 1) ω / P (t + 1) ω) ω =
      (1 + μ) * (1 + r) * S.E 0 (fun ω => M t ω / P t ω) ω := by
    intro t
    obtain ⟨C, hC⟩ := hmB t
    have hgi : Integrable (fun ω => 1 / infl (t + 1) ω) S.μ :=
      integrable_of_bdd S (((hπad (t + 1)).mono (S.𝓕.le _)).measurable.const_div 1)
        (C := 1 / lo) fun ω => by
          rw [abs_of_pos (one_div_pos.mpr (hpos _ _))]
          exact one_div_le_one_div_of_le hlo (hlow _ _)
    have hkm : StronglyMeasurable[S.𝓕 t] (fun ω => (1 + μ) * (M t ω / P t ω)) :=
      ((hmm t).measurable.const_mul _).stronglyMeasurable
    have hpo := S.E_pullOut hkm (C := (1 + μ) * C) (Eventually.of_forall fun ω => by
      rw [abs_mul, abs_of_pos (by linarith), abs_of_nonneg (div_nonneg (hM t ω) (hP t ω).le)]
      exact mul_le_mul_of_nonneg_left (hC ω) (by linarith)) hgi
    have he : (fun ω => M (t + 1) ω / P (t + 1) ω) =
        (fun ω => (1 + μ) * (M t ω / P t ω)) * fun ω => 1 / infl (t + 1) ω := by
      funext ω
      rw [hMs, hPs]
      simp only [Pi.mul_apply]
      have := (hP t ω).ne'
      have := (hpos (t + 1) ω).ne'
      field_simp
    have hEt : S.E t (fun ω => M (t + 1) ω / P (t + 1) ω) =ᵐ[S.μ]
        ((1 + μ) * (1 + r)) • fun ω => M t ω / P t ω := by
      rw [he]
      filter_upwards [hpo, hzb t] with ω e1 e2
      rw [e1]
      simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, e2]
      ring
    have h0 := S.E_tower (Nat.zero_le t) (fun ω => M (t + 1) ω / P (t + 1) ω)
    have h1 := S.E_congr hEt 0
    have h3 := S.E_smul ((1 + μ) * (1 + r)) (fun ω => M t ω / P t ω) 0
    filter_upwards [h0, h1, h3] with ω e0 e1 e3
    rw [← e0, e1, e3]
    rfl
  filter_upwards [ae_all_iff.mpr hstep] with ω hω h0
  refine tendsto_of_growth (q := 1 + μ) (by linarith) (T := 0) (by simpa using h0)
    fun t _ => ?_
  rw [hω t, pow_succ]
  have : ((1 + r)⁻¹) ^ t * (1 + r)⁻¹ * ((1 + μ) * (1 + r) * S.E 0 (fun ω => M t ω / P t ω) ω) =
      (1 + μ) * (((1 + r)⁻¹) ^ t * S.E 0 (fun ω => M t ω / P t ω) ω) := by field_simp
  rw [this]

/-- Cochrane (2023), Online Appendix A3, §3.1.2, p. 615 ("despite ever increasing money, the
total value of government debt is the same, and the transversality condition holds"), on a
probability space: with total liabilities `W_{t+1} = βW_t` (the surplus `s_t = (1 − β)W_t/P_t`
at a zero rate, `β = 1/(1 + r) < 1`), prices `P_{t+1} = Π_{t+1}P_t > 0`, adapted `Π`, `P`, `W`,
real liabilities bounded at each date, `Π ≥ lo > 0` and `E_t(1/Π_{t+1}) = 1 + r` almost surely,
real total debt is a martingale, `E_t[W_{t+1}/P_{t+1}] = W_t/P_t`, and the transversality
condition `βᵗE_0[W_t/P_t] → 0` holds almost surely. -/
theorem meas_a3_omo_tvc {r lo : ℝ} (hr : 0 < r) (hlo : 0 < lo) {infl P W : ℕ → Ω → ℝ}
    (hπad : StronglyAdapted S.𝓕 infl) (hPad : StronglyAdapted S.𝓕 P)
    (hWad : StronglyAdapted S.𝓕 W) (hlow : ∀ t ω, lo ≤ infl t ω) (hP : ∀ t ω, 0 < P t ω)
    (hPs : ∀ t ω, P (t + 1) ω = infl (t + 1) ω * P t ω)
    (hWs : ∀ t ω, W (t + 1) ω = (1 + r)⁻¹ * W t ω)
    (hwB : ∀ t, ∃ C, ∀ ω, |W t ω / P t ω| ≤ C)
    (hzb : ∀ t, S.E t (fun ω => 1 / infl (t + 1) ω) =ᵐ[S.μ] fun _ => 1 + r) :
    (∀ t, S.E t (fun ω => W (t + 1) ω / P (t + 1) ω) =ᵐ[S.μ] fun ω => W t ω / P t ω) ∧
      ∀ᵐ ω ∂S.μ, Tendsto (fun t => ((1 + r)⁻¹) ^ t * S.E 0 (fun ω => W t ω / P t ω) ω)
        atTop (𝓝 0) := by
  have hr1 : 0 < 1 + r := by linarith
  have hpos : ∀ t ω, 0 < infl t ω := fun t ω => lt_of_lt_of_le hlo (hlow t ω)
  have hwm : ∀ t, StronglyMeasurable[S.𝓕 t] (fun ω => W t ω / P t ω) := fun t =>
    ((hWad t).measurable.div (hPad t).measurable).stronglyMeasurable
  have hwi : ∀ t, Integrable (fun ω => W t ω / P t ω) S.μ := fun t => by
    obtain ⟨C, hC⟩ := hwB t
    exact integrable_of_bdd S ((hwm t).mono (S.𝓕.le t)).measurable hC
  have hmart : ∀ t, S.E t (fun ω => W (t + 1) ω / P (t + 1) ω) =ᵐ[S.μ]
      fun ω => W t ω / P t ω := by
    intro t
    obtain ⟨C, hC⟩ := hwB t
    have hgi : Integrable (fun ω => 1 / infl (t + 1) ω) S.μ :=
      integrable_of_bdd S (((hπad (t + 1)).mono (S.𝓕.le _)).measurable.const_div 1)
        (C := 1 / lo) fun ω => by
          rw [abs_of_pos (one_div_pos.mpr (hpos _ _))]
          exact one_div_le_one_div_of_le hlo (hlow _ _)
    have hkm : StronglyMeasurable[S.𝓕 t] (fun ω => (1 + r)⁻¹ * (W t ω / P t ω)) :=
      ((hwm t).measurable.const_mul _).stronglyMeasurable
    have hpo := S.E_pullOut hkm (C := (1 + r)⁻¹ * C) (Eventually.of_forall fun ω => by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hr1)]
      exact mul_le_mul_of_nonneg_left (hC ω) (inv_pos.mpr hr1).le) hgi
    have he : (fun ω => W (t + 1) ω / P (t + 1) ω) =
        (fun ω => (1 + r)⁻¹ * (W t ω / P t ω)) * fun ω => 1 / infl (t + 1) ω := by
      funext ω
      rw [hWs, hPs]
      simp only [Pi.mul_apply]
      have := (hP t ω).ne'
      have := (hpos (t + 1) ω).ne'
      field_simp
    rw [he]
    filter_upwards [hpo, hzb t] with ω e1 e2
    rw [e1]
    simp only [Pi.mul_apply, e2]
    field_simp
  refine ⟨hmart, ?_⟩
  have hstep : ∀ t, ∀ᵐ ω ∂S.μ, S.E 0 (fun ω => W (t + 1) ω / P (t + 1) ω) ω =
      S.E 0 (fun ω => W t ω / P t ω) ω := by
    intro t
    filter_upwards [S.E_tower (Nat.zero_le t) (fun ω => W (t + 1) ω / P (t + 1) ω),
      S.E_congr (hmart t) 0] with ω e0 e1
    rw [← e0, e1]
  filter_upwards [ae_all_iff.mpr hstep] with ω hω
  have hconst : ∀ t, S.E 0 (fun ω => W t ω / P t ω) ω = S.E 0 (fun ω => W 0 ω / P 0 ω) ω := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih => rw [hω n, ih]
  simp only [hconst]
  have hq : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr hr1).le hq).mul_const
    (S.E 0 (fun ω => W 0 ω / P 0 ω) ω)

end Cochrane.NewKeynesianSelection.TidyR6StochasticMeasurePatches
