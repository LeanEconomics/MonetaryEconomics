/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureForecast

/-!
# Determinacy under the target criterion (1.23) with genuine conditional expectations

Woodford (2003), *Interest and Prices*, Chapter 8, Section 1.4, Propositions 8.1 and 8.2
(pp. 552–555, (1.18)–(1.27)), with Appendix G.1–G.2 (pp. 716–719), on a filtered probability
space with Mathlib's conditional expectation and an **arbitrary** bounded disturbance.

Proposition 8.2 says that commitment to the target criterion (1.23) brings about the optimal
equilibrium and that this equilibrium is determinate. `OptimalRulesMeasureForecast.m_criterion`
shows the first half (the solution of (1.1) + (1.9) satisfies (1.23) a.s.). Here the converse
is rebuilt with `condExp`: **a bounded feasible plan that satisfies (1.23) a.s. is the solution of
(1.1) + (1.9)**, so it is unique a.s. (the core template is `Prop82General.Prop82M`).

## The construction (the reverse direction of Proposition 8.1)

With a deflating split (`PencilSplit.DeflatingSplit`, `G = βΨ'`, `f_t = βJ'x_t`,
`x_t = T̃'W(τ_t − τ*)`):

* `Rsum`: the realised forward sum `R_t = ∑_k Gᵏ f_{t+k}` (absolutely convergent a.s.,
  `rsum_spec`), `R_t = f_t + G R_{t+1}`;
* `Fm`: `F_t = E_t R_t`, so `F_t = f_t + G E_t F_{t+1}` a.s. (`Fm_rec`, the law of iterated
  expectations — no interchange of `E_t` and the series is needed);
* `rm`, `qm`: `r_t = (J₁')⁻¹F_t` and `q_t = −K⁻¹(x^z_t + A₁₂'E_t r_{t+1})`, the operators
  `E_t R(L⁻¹)`, `E_t Q(L⁻¹)` of Proposition 8.1; `qm_eq_qM`: `q_t` is a.s. the forecast-based
  `OptimalRulesMeasureMarkov.qM` used in the criterion (here `E_t` is passed through the series,
  `ExpectationsMeasure.MeasExpectationSystem.E_hasSum`);
* `Mc`, `φc`: `M_t` from (1.20) with the history before `t₀`, `ξ_t = ΥM_{t−1} + r_t` (1.21).

Then (1.19) follows from (1.23) (`TargetCriterion.Crit.eq119_of_criterion`), `M` is bounded by
Assumption 8.5 (`Prop82General.KrylovBound.boundedV_of_krylov`, made uniform over `ω` by
`krylov_ae`), (1.18) holds a.s. (`eq118_pt`: the algebra of `Prop81General.prop81_equiv`, with
`E_t F_{t+1}`), and (1.18) + (1.19) is (1.9) (`foc_split_pt`).

## Main results

* `m_focSystem_of_criterion`: a bounded feasible plan satisfying (1.23) a.s. from `t₀` on, with a
  consistent history, solves (1.1) + (1.9) with `M_{t₀−1}` from the history.
* `m_criterion_iff`: for a feasible plan, (1.23) a.s. ⟺ it is (the plan of) a solution of
  (1.1) + (1.9) with that initial multiplier — the measure-theoretic Proposition 8.2.
* `m_prop82_unique`, `m_prop82_unique_pf`, `m_criterion_eq_foc`: **determinacy**: two bounded
  feasible plans satisfying (1.23) a.s. agree a.s., and each equals the optimal (FOC) plan a.s.
  — under the measure Assumption 8.1 (uniqueness half), which holds on every probability space
  as soon as it holds under perfect foresight (`OptimalRulesMeasureForecast.m_focUnique_of_pf`).
* `m_prop82_var`: on every VAR economy with the perfect-foresight Assumption 8.1 and stable
  `H_n` the criterion has exactly one bounded equilibrium, and it is optimal from a timeless
  perspective.
* `mCriterion_unit_iff`: on the one-point probability space the criterion is the core
  `Prop82General.Prop82M.CriterionM` for `Prop81General.prop81 … perfectForesight`.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureConverse

open MeasureTheory Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov OptimalRulesMeasureForecast
open TargetCriterion.Prop81 TargetCriterion.Recursion

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### Geometric vector series -/

omit [MeasurableSpace Ω] in
/-- Woodford (2003), App. G.1, p. 717 (tool): if the powers of `G` decay geometrically, the
series `∑_k Gᵏ w_k` converges absolutely for every bounded sequence `w`, with a bound depending
only on the bound of `w`. -/
theorem geom_vec {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℝ}
    (hG : PencilSplit.PowDecay G) (M : ℝ) :
    ∃ K, ∀ w : ℕ → ι → ℝ, (∀ k j, |w k j| ≤ M) → ∀ i,
      Summable (fun k => (G ^ k *ᵥ w k) i) ∧ |∑' k, (G ^ k *ᵥ w k) i| ≤ K := by
  obtain ⟨C, r, hr0, hr1, hC⟩ := hG
  set g : ℕ → ℝ := fun k => Fintype.card ι * (C * r ^ k * M) with hg
  have hgs : HasSum g (Fintype.card ι * (C * M) * (1 - r)⁻¹) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (Fintype.card ι * (C * M))
    convert this using 1
    funext k
    simp only [hg]
    ring
  refine ⟨Fintype.card ι * (C * M) * (1 - r)⁻¹, fun w hw i => ?_⟩
  have hb : ∀ k, ‖(G ^ k *ᵥ w k) i‖ ≤ g k := fun k => by
    rw [Real.norm_eq_abs]
    exact PencilSplit.abs_mulVec_pow_le hC k (hw k) i
  exact ⟨Summable.of_norm_bounded hgs.summable hb, by
    rw [← Real.norm_eq_abs]
    exact tsum_of_norm_bounded hgs hb⟩

omit [MeasurableSpace Ω] in
/-- Woodford (2003), App. G.1 (tool): one step of a convergent vector series,
`∑_k Gᵏ w_k = w_0 + G ∑_k Gᵏ w_{k+1}`. -/
theorem geom_shift {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (w : ℕ → ι → ℝ)
    (hs : ∀ i, Summable (fun k => (G ^ k *ᵥ w k) i))
    (hs1 : ∀ i, Summable (fun k => (G ^ k *ᵥ w (k + 1)) i)) :
    (fun i => ∑' k, (G ^ k *ᵥ w k) i) =
      w 0 + G *ᵥ fun i => ∑' k, (G ^ k *ᵥ w (k + 1)) i := by
  funext i
  rw [(hs i).tsum_eq_zero_add, pow_zero, one_mulVec, Pi.add_apply]
  congr 1
  have h1 : ∀ k, (G ^ (k + 1) *ᵥ w (k + 1)) i = ∑ j, G i j * (G ^ k *ᵥ w (k + 1)) j := by
    intro k
    rw [pow_succ', ← mulVec_mulVec]
    rfl
  simp_rw [h1]
  rw [Summable.tsum_finsetSum (fun j _ => (hs1 j).mul_left (G i j))]
  rw [Finset.sum_congr rfl fun j _ => (hs1 j).tsum_mul_left (G i j)]
  rfl

/-! ### Bounds for the target terms -/

omit [DecidableEq ιZ] in
/-- Woodford (2003), p. 553 (tool): `T̃'W(Tv − τ*)` is bounded for bounded `v`. -/
theorem xv_bound (P : LQProblem ιZ ιz ιτ) (M : ℝ) :
    ∃ K, ∀ v : (ιZ ⊕ ιz) ⊕ Unit → ℝ, (∀ i, |v i| ≤ M) →
      ∀ j, |(P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))) j| ≤ K := by
  obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.T M
  obtain ⟨K2, hK2⟩ := exists_bound_mulVec P.W (K1 + ∑ b, |P.τstar b|)
  obtain ⟨K3, hK3⟩ := exists_bound_mulVec P.Ttilᵀ K2
  refine ⟨K3, fun v hv j => hK3 _ (fun a => hK2 _ (fun b => ?_) a) j⟩
  have h2 : |P.τstar b| ≤ ∑ b, |P.τstar b| :=
    Finset.single_le_sum (f := fun b => |P.τstar b|) (fun b _ => abs_nonneg _)
      (Finset.mem_univ b)
  simp only [Pi.sub_apply]
  exact (abs_sub _ _).trans (add_le_add (hK1 _ hv b) h2)

omit [DecidableEq ιZ] in
/-- Woodford (2003), eq. (1.26), p. 554 (tool): `v = T_i'W(Tv − τ*)` is bounded for bounded `v`. -/
theorem vv_bound (P : LQProblem ιZ ιz ιτ) (M : ℝ) :
    ∃ K, ∀ v : (ιZ ⊕ ιz) ⊕ Unit → ℝ, (∀ i, |v i| ≤ M) →
      |P.Ti ⬝ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))| ≤ K := by
  obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.T M
  obtain ⟨K2, hK2⟩ := exists_bound_mulVec (Matrix.of fun (_ : Unit) a => (P.Ti ᵥ* P.W) a)
    (K1 + ∑ b, |P.τstar b|)
  refine ⟨K2, fun v hv => ?_⟩
  have hb : ∀ b, |(P.T *ᵥ v - P.τstar) b| ≤ K1 + ∑ b, |P.τstar b| := fun b => by
    have h2 : |P.τstar b| ≤ ∑ b, |P.τstar b| :=
      Finset.single_le_sum (f := fun b => |P.τstar b|) (fun b _ => abs_nonneg _)
        (Finset.mem_univ b)
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hK1 _ hv b) h2)
  have := hK2 _ hb ()
  rw [dotProduct_mulVec]
  exact this

omit [DecidableEq ιZ] in
/-- Woodford (2003), p. 553 (tool): `T̃'W(Ty − τ*)` is affine in `y`. -/
theorem xv_affine (P : LQProblem ιZ ιz ιτ) (v : (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) =
      (P.Ttilᵀ * P.W * P.T) *ᵥ v + -(P.Ttilᵀ *ᵥ (P.W *ᵥ P.τstar)) := by
  rw [mulVec_sub, mulVec_sub, ← mulVec_mulVec, ← mulVec_mulVec, sub_eq_add_neg]

/-! ### The operators `E_t R(L⁻¹)` and `E_t Q(L⁻¹)` with conditional expectations -/

variable (P : LQProblem ιZ ιz ιτ) (Dsp : PencilSplit.DeflatingSplit P.sys P.β)

/-- Woodford (2003), App. G.1, p. 717: the realised forward sum
`R_t = ∑_{k ≥ 0} (βΨ')ᵏ βJ' T̃'W(τ_{t+k} − τ*)` along a plan. -/
noncomputable def Rsum (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω) : ιZ → ℝ :=
  fun i => ∑' k, ((P.β • Dsp.Ψᵀ) ^ k *ᵥ ((P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + k) ω)) i

/-- Woodford (2003), App. G.1 and eq. (1.21), p. 553: `F_t = E_t R_t`, the forward solution of
`w_t = βΨ' E_t w_{t+1} + βJ' x_t` with genuine conditional expectations. -/
noncomputable def Fm (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) :
    Ω → ιZ → ℝ :=
  EVm S t (Rsum P Dsp y t)

/-- Woodford (2003), eq. (1.21), p. 553: `r_t = E_t R(L⁻¹) T̃'W(τ_t − τ*) = (J₁')⁻¹ F_t`. -/
noncomputable def rm (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ)
    (ω : Ω) : ιZ → ℝ :=
  ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ Fm P Dsp S y t ω

/-- Woodford (2003), eqs. (1.20) and (1.25), p. 553: `q_t = E_t Q(L⁻¹) T̃'W(τ_t − τ*)
= −K⁻¹(x^z_t + A₁₂' E_t r_{t+1})`. -/
noncomputable def qm (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ)
    (ω : Ω) : ιz → ℝ :=
  -((PencilSplit.Kmat P.sys Dsp.J)⁻¹ *ᵥ
    (Mpart (xproc P y t ω) + P.sys.A12ᵀ *ᵥ EVm S t (rm P Dsp S y (t + 1)) ω))

variable {P Dsp}


/-- Woodford (2003), App. G.1 (the forward sum): along an essentially bounded plan, a.s. at every
date the series `R_t` converges absolutely, is bounded by a constant, and satisfies
`R_t = βJ'x_t + βΨ' R_{t+1}`. -/
theorem rsum_spec {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) :
    ∃ KR, ∀ᵐ ω ∂S.μ, ∀ t, (∀ i, HasSum (fun k => ((P.β • Dsp.Ψᵀ) ^ k *ᵥ
        ((P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + k) ω)) i) (Rsum P Dsp y t ω i)) ∧
      (∀ i, |Rsum P Dsp y t ω i| ≤ KR) ∧
      Rsum P Dsp y t ω = (P.β • Dsp.Jᵀ) *ᵥ xproc P y t ω +
        (P.β • Dsp.Ψᵀ) *ᵥ Rsum P Dsp y (t + 1) ω := by
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨KX, hKX⟩ := xv_bound P Ky
  obtain ⟨Mw, hMw⟩ := exists_bound_mulVec (P.β • Dsp.Jᵀ) KX
  obtain ⟨K, hK⟩ := geom_vec (Dsp.powDecay_G P.β_pos) Mw
  refine ⟨K, ?_⟩
  filter_upwards [ae_all_iff.2 hKy] with ω hω t
  have hw : ∀ s, ∀ k j, |((P.β • Dsp.Jᵀ) *ᵥ xproc P y (s + k) ω) j| ≤ Mw := fun s k j =>
    hMw _ (fun j' => hKX _ (hω (s + k)) j') j
  have h0 := fun i => hK _ (hw t) i
  have h1 := fun i => hK _ (hw (t + 1)) i
  refine ⟨fun i => (h0 i).1.hasSum, fun i => (h0 i).2, ?_⟩
  have hs1 : ∀ i, Summable (fun k => ((P.β • Dsp.Ψᵀ) ^ k *ᵥ
      ((P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + (k + 1)) ω)) i) := by
    intro i
    refine (h1 i).1.congr fun k => ?_
    rw [show t + (k + 1) = t + 1 + k by omega]
  have := geom_shift (P.β • Dsp.Ψᵀ) (fun k => (P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + k) ω)
    (fun i => (h0 i).1) hs1
  have e1 : Rsum P Dsp y t ω = fun i => ∑' k, ((P.β • Dsp.Ψᵀ) ^ k *ᵥ
      ((fun k => (P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + k) ω) k)) i := rfl
  rw [e1, this]
  refine congrArg₂ (· + ·) rfl (congrArg _ (funext fun i => tsum_congr fun k => ?_))
  show ((P.β • Dsp.Ψᵀ) ^ k *ᵥ ((P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + (k + 1)) ω)) i =
    ((P.β • Dsp.Ψᵀ) ^ k *ᵥ ((P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + 1 + k) ω)) i
  rw [show t + (k + 1) = t + 1 + k by omega]

omit [DecidableEq ιZ] in
/-- Woodford (2003), p. 553 (tool): the components of `T̃'W(τ_t − τ*)` along a bounded adapted
plan are integrable and known at `t`. -/
theorem xproc_int_known {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) (t : ℕ) :
    (∀ j, Integrable (fun ω => xproc P y t ω j) S.μ) ∧ MKnownV S t (xproc P y t) := by
  have hyi := integrable_of_adapted hyb hya
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have : (fun ω => xproc P y t ω j) = fun ω => ((P.Ttilᵀ * P.W * P.T) *ᵥ y t ω +
        -(P.Ttilᵀ *ᵥ (P.W *ᵥ P.τstar))) j := by
      funext ω
      rw [xproc, xv_affine]
    rw [this]
    exact (integrable_mulVec _ (hyi t) j).add (integrable_const _)
  · exact sm_comp (hya t) (g := fun v => (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))) j)
      (by fun_prop)


/-- Woodford (2003), App. G.1 (tool): the realised forward sum is a.e. strongly measurable
(the a.e. limit of its partial sums) and integrable. -/
theorem rsum_integrable {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) (t : ℕ) (i : ιZ) :
    Integrable (fun ω => Rsum P Dsp y t ω i) S.μ := by
  obtain ⟨KR, hKR⟩ := rsum_spec (P := P) (Dsp := Dsp) hyb
  have hterm : ∀ k, AEStronglyMeasurable (fun ω => ((P.β • Dsp.Ψᵀ) ^ k *ᵥ
      ((P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + k) ω)) i) S.μ := fun k =>
    aesm_comp (fun j => (((xproc_int_known (P := P) hyb hya (t + k)).2 j).mono
      (S.𝓕.le _)).aestronglyMeasurable)
      (g := fun v => ((P.β • Dsp.Ψᵀ) ^ k *ᵥ ((P.β • Dsp.Jᵀ) *ᵥ v)) i) (by fun_prop)
  have hm : AEStronglyMeasurable (fun ω => Rsum P Dsp y t ω i) S.μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, ((P.β • Dsp.Ψᵀ) ^ k *ᵥ
        ((P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + k) ω)) i)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hterm k) ?_
    filter_upwards [hKR] with ω h
    exact ((h t).1 i).tendsto_sum_nat
  exact integrable_of_bound hm (hKR.mono fun ω h => (h t).2.1 i)


/-- Woodford (2003), App. G.1, (G.5) with genuine conditional expectations: **the forward
recursion** `F_t = βJ'x_t + βΨ' E_t F_{t+1}` a.s. (law of iterated expectations). -/
theorem Fm_rec {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, Fm P Dsp S y t ω = (P.β • Dsp.Jᵀ) *ᵥ xproc P y t ω +
      (P.β • Dsp.Ψᵀ) *ᵥ EVm S t (Fm P Dsp S y (t + 1)) ω := by
  obtain ⟨KR, hKR⟩ := rsum_spec (P := P) (Dsp := Dsp) hyb
  obtain ⟨hxi, hxk⟩ := xproc_int_known (P := P) hyb hya t
  have hRi := rsum_integrable (P := P) (Dsp := Dsp) hyb hya (t + 1)
  have hrec : ∀ᵐ ω ∂S.μ, Rsum P Dsp y t ω = (P.β • Dsp.Jᵀ) *ᵥ xproc P y t ω +
      (P.β • Dsp.Ψᵀ) *ᵥ Rsum P Dsp y (t + 1) ω + (0 : Matrix ιZ ιZ ℝ) *ᵥ Rsum P Dsp y t ω +
        0 := by
    filter_upwards [hKR] with ω h
    rw [zero_mulVec, add_zero, add_zero]
    exact (h t).2.2
  filter_upwards [EVm_congr S t hrec, EVm_affine3 S t (P.β • Dsp.Jᵀ) (P.β • Dsp.Ψᵀ)
    (0 : Matrix ιZ ιZ ℝ) 0 hxi hRi (rsum_integrable (P := P) (Dsp := Dsp) hyb hya t),
    EVm_tower S (Nat.le_succ t) (Rsum P Dsp y (t + 1))] with ω e1 e2 e3
  unfold Fm
  rw [e1, e2, zero_mulVec, add_zero, add_zero, EVm_of_known S hxk hxi, e3]


/-- Woodford (2003), (1.21) (tool): `F_t` and `r_t` are essentially bounded, uniformly in `t`. -/
theorem Fm_bdd {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) :
    ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, (∀ i, |Fm P Dsp S y t ω i| ≤ K) ∧ ∀ i, |rm P Dsp S y t ω i| ≤ K := by
  obtain ⟨KR, hKR⟩ := rsum_spec (P := P) (Dsp := Dsp) hyb
  obtain ⟨Kr, hKr⟩ := exists_bound_mulVec ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ KR
  refine ⟨max KR Kr, fun t => ?_⟩
  have hF : ∀ᵐ ω ∂S.μ, ∀ i, |Fm P Dsp S y t ω i| ≤ KR :=
    ae_all_iff.2 fun i => S.abs_E_le (hKR.mono fun ω h => (h t).2.1 i) t
  filter_upwards [hF] with ω h
  exact ⟨fun i => (h i).trans (le_max_left _ _),
    fun i => (hKr _ h i).trans (le_max_right _ _)⟩


/-- Woodford (2003), p. 553: `F_t` and `r_t` are known at `t`. -/
theorem rm_known (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) :
    MKnownV S t (Fm P Dsp S y t) ∧ MKnownV S t (rm P Dsp S y t) := by
  have hF : MKnownV S t (Fm P Dsp S y t) := fun i => S.stronglyMeasurable_E t _
  exact ⟨hF, fun i => sm_comp hF (g := fun v => (((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ v) i)
    (by fun_prop)⟩


/-- Woodford (2003), eq. (1.25), p. 554: `q_t` is known at `t` and essentially bounded. -/
theorem qm_known_bdd {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) :
    (∀ t, MKnownV S t (qm P Dsp S y t)) ∧ ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, ∀ r, |qm P Dsp S y t ω r| ≤ K := by
  refine ⟨fun t r => ?_, ?_⟩
  · have h1 := (xproc_int_known (P := P) hyb hya t).2
    have h2 : MKnownV S t (EVm S t (rm P Dsp S y (t + 1))) := fun i =>
      S.stronglyMeasurable_E t _
    exact sm_comp₂ h1 h2 (g := fun p => (-((PencilSplit.Kmat P.sys Dsp.J)⁻¹ *ᵥ
      (Mpart p.1 + P.sys.A12ᵀ *ᵥ p.2))) r) (by unfold Mpart; fun_prop)
  · obtain ⟨Ky, hKy⟩ := hyb
    obtain ⟨KX, hKX⟩ := xv_bound P Ky
    obtain ⟨KF, hKF⟩ := Fm_bdd (P := P) (Dsp := Dsp) ⟨Ky, hKy⟩
    obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.sys.A12ᵀ KF
    obtain ⟨K2, hK2⟩ := exists_bound_mulVec (PencilSplit.Kmat P.sys Dsp.J)⁻¹ (KX + K1)
    refine ⟨K2, fun t => ?_⟩
    have hE : ∀ᵐ ω ∂S.μ, ∀ i, |EVm S t (rm P Dsp S y (t + 1)) ω i| ≤ KF :=
      ae_all_iff.2 fun i => S.abs_E_le ((hKF (t + 1)).mono fun ω h => h.2 i) t
    filter_upwards [hKy t, hE] with ω h1 h2 r
    change |(-((PencilSplit.Kmat P.sys Dsp.J)⁻¹ *ᵥ _)) r| ≤ K2
    rw [Pi.neg_apply, abs_neg]
    refine hK2 _ (fun j => ?_) r
    exact (abs_add_le _ _).trans (add_le_add (hKX _ h1 (Sum.inr j)) (hK1 _ h2 j))

omit [MeasurableSpace Ω] in
/-- Woodford (2003), App. G.1, p. 717 (tool): an explicit summable bound for the terms of
`∑_k Gᵏ w_k` over all `w` bounded by `M`. -/
theorem geom_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℝ}
    (hG : PencilSplit.PowDecay G) (M : ℝ) :
    ∃ g : ℕ → ℝ, Summable g ∧ ∀ k (w : ι → ℝ), (∀ j, |w j| ≤ M) → ∀ i, |(G ^ k *ᵥ w) i| ≤ g k := by
  obtain ⟨C, r, hr0, hr1, hC⟩ := hG
  refine ⟨fun k => Fintype.card ι * (C * r ^ k * M), ?_, fun k w hw i =>
    PencilSplit.abs_mulVec_pow_le hC k hw i⟩
  have := (summable_geometric_of_lt_one hr0 hr1).mul_left (Fintype.card ι * (C * M))
  refine this.congr fun k => ?_
  ring

/-- Woodford (2003), eq. (1.25), p. 554: the forecast-based `q_t` of
`OptimalRulesMeasureMarkov.qM` written out — `−K⁻¹(x̂^z_0 + A₁₂'(J₁')⁻¹ ∑_k (βΨ')ᵏ βJ' x̂_{1+k})`
for the conditional forecast path `x̂_k = T̃'W(T E_t y_{t+k} − τ*)`. -/
theorem qM_eq (S : MeasExpectationSystem Ω) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ)
    (ω : Ω) : qM P Dsp S y t ω = -((PencilSplit.Kmat P.sys Dsp.J)⁻¹ *ᵥ
      (Mpart (xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω) 0 ()) + P.sys.A12ᵀ *ᵥ
        (((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ fun i => ∑' k, ((P.β • Dsp.Ψᵀ) ^ k *ᵥ
          ((P.β • Dsp.Jᵀ) *ᵥ xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω)
            (0 + 1 + k) ())) i))) := rfl

/-- Woodford (2003), eq. (1.25), p. 554 (link): the operator `q_t` built with conditional
expectations equals a.s. the forecast-based `OptimalRulesMeasureMarkov.qM` (the operator
`Q(L⁻¹)` of `Prop81General` applied to the conditional forecast path) used in the criterion
(1.23); here `E_t` is passed through the forward series (dominated convergence,
`ExpectationsMeasure.MeasExpectationSystem.E_hasSum`). -/
theorem qm_eq_qM {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) (t : ℕ) :
    qm P Dsp S y t =ᵐ[S.μ] qM P Dsp S y t := by
  have hyi := integrable_of_adapted hyb hya
  set G := P.β • Dsp.Ψᵀ with hG
  set BJ := P.β • Dsp.Jᵀ with hBJ
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨KX, hKX⟩ := xv_bound P Ky
  obtain ⟨Mw, hMw⟩ := exists_bound_mulVec BJ KX
  obtain ⟨g, hgs, hg⟩ := geom_bound (Dsp.powDecay_G P.β_pos) Mw
  -- the series for `E_t R_{t+1}`
  have hser : ∀ i, ∀ᵐ ω ∂S.μ, EVm S t (Rsum P Dsp y (t + 1)) ω i =
      ∑' k, (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 1 + k)) ω -
        P.τstar))))) i := by
    intro i
    set a : ℕ → Ω → ℝ := fun k ω => (G ^ k *ᵥ (BJ *ᵥ xproc P y (t + 1 + k) ω)) i with ha
    have ham : ∀ k, AEStronglyMeasurable (a k) S.μ := fun k =>
      aesm_comp (fun j => ((hya (t + 1 + k) j).mono (S.𝓕.le _)).aestronglyMeasurable)
        (g := fun v => (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))))) i)
        (by fun_prop)
    have hab : ∀ k, ∀ᵐ ω ∂S.μ, |a k ω| ≤ g k := fun k => by
      filter_upwards [hKy (t + 1 + k)] with ω h
      exact hg k _ (fun j => hMw _ (fun j' => hKX _ h j') j) i
    have hEk : ∀ k, ∀ᵐ ω ∂S.μ, S.E t (a k) ω = (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ
        (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 1 + k)) ω - P.τstar))))) i := by
      intro k
      set B := G ^ k * BJ * (P.Ttilᵀ * P.W * P.T) with hB
      set b := G ^ k *ᵥ (BJ *ᵥ -(P.Ttilᵀ *ᵥ (P.W *ᵥ P.τstar))) with hb
      have haff : ∀ v : (ιZ ⊕ ιz) ⊕ Unit → ℝ, G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ
          (P.W *ᵥ (P.T *ᵥ v - P.τstar)))) = B *ᵥ v + (0 : Matrix ιZ ((ιZ ⊕ ιz) ⊕ Unit) ℝ) *ᵥ v +
            (0 : Matrix ιZ ((ιZ ⊕ ιz) ⊕ Unit) ℝ) *ᵥ v + b := by
        intro v
        rw [xv_affine, zero_mulVec, add_zero, add_zero, mulVec_add, mulVec_add, hB, hb]
        simp only [mulVec_mulVec, Matrix.mul_assoc]
      have hfun : a k = fun ω => (B *ᵥ y (t + 1 + k) ω +
          (0 : Matrix ιZ ((ιZ ⊕ ιz) ⊕ Unit) ℝ) *ᵥ y (t + 1 + k) ω +
          (0 : Matrix ιZ ((ιZ ⊕ ιz) ⊕ Unit) ℝ) *ᵥ y (t + 1 + k) ω + b) i := by
        funext ω
        simp only [ha]
        rw [← haff]
        rfl
      filter_upwards [EVm_affine3 S t B 0 0 b (hyi (t + 1 + k)) (hyi (t + 1 + k))
        (hyi (t + 1 + k))] with ω e
      have := congrFun e i
      simp only [EVm] at this
      rw [hfun, this, haff]
    filter_upwards [S.E_hasSum hgs ham hab t, ae_all_iff.2 hEk] with ω h1 h2
    change S.E t (fun ω' => Rsum P Dsp y (t + 1) ω' i) ω = _
    have hR : (fun ω' => Rsum P Dsp y (t + 1) ω' i) = fun ω' => ∑' k, a k ω' := rfl
    rw [hR, ← h1.tsum_eq]
    exact tsum_congr h2
  -- assemble
  have hFi : ∀ i, Integrable (fun ω => Fm P Dsp S y (t + 1) ω i) S.μ := fun i =>
    S.integrable_E _ _
  filter_upwards [EVm_mulVec S t ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ hFi,
    EVm_tower S (Nat.le_succ t) (Rsum P Dsp y (t + 1)), ae_all_iff.2 hser] with ω e1 e2 e3
  have hy0 : EVm S t (y (t + 0)) ω = y t ω := by
    rw [Nat.add_zero, EVm_of_known S (hya t) (hyi t)]
  have hrm : EVm S t (rm P Dsp S y (t + 1)) ω = ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ
      fun i => ∑' k, (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 1 + k)) ω -
        P.τstar))))) i := by
    have : EVm S t (rm P Dsp S y (t + 1)) ω = EVm S t
        (fun ω => ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ Fm P Dsp S y (t + 1) ω) ω := rfl
    rw [this, e1]
    congr 1
    funext i
    rw [← e3 i]
    exact congrFun e2 i
  have h1 : xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω) 0 () = xproc P y t ω := by
    change P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 0)) ω - P.τstar)) = _
    rw [hy0]
    rfl
  have h2 : (fun i => ∑' k, (G ^ k *ᵥ (BJ *ᵥ
      xproc P (fun k (_ : Unit) => EVm S t (y (t + k)) ω) (0 + 1 + k) ())) i) =
      fun i => ∑' k, (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + 1 + k)) ω -
        P.τstar))))) i := by
    funext i
    refine tsum_congr fun k => ?_
    change (G ^ k *ᵥ (BJ *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm S t (y (t + (0 + 1 + k))) ω -
      P.τstar))))) i = _
    rw [show t + (0 + 1 + k) = t + 1 + k by omega]
  rw [qM_eq, h1, h2]
  unfold qm
  rw [hrm]

omit [MeasurableSpace Ω] in
/-- Woodford (2003), eq. (1.23) (tool): the criterion at `(t, ω)` depends on `q` only through
its values at `ω`. -/
theorem crit_congr {ι : Type*} [Fintype ι] (α : Polynomial ℝ)
    (B : Matrix ι ι (Polynomial ℝ)) (D : ℕ) (B2 : ι → ℝ) (v : ℕ → Ω → ℝ)
    {q q' : ℕ → Ω → ι → ℝ} (t : ℕ) (ω : Ω) (h : ∀ u, q u ω = q' u ω) :
    TargetCriterion.Crit.crit α B D B2 v q t ω = TargetCriterion.Crit.crit α B D B2 v q' t ω := by
  unfold TargetCriterion.Crit.crit
  simp only [h]

/-- Woodford (2003), App. G.2 and Assumption 8.5 (tool):
`Prop82General.KrylovBound.boundedV_of_krylov` with almost-sure hypotheses gives an essential
bound that is uniform over dates (the processes are replaced by zero off the full-measure set
where the hypotheses hold). -/
theorem krylov_ae {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ}
    (h85 : TargetCriterion.Krylov.Assumption85b Λ B2) {μ : Measure Ω}
    {M q : ℕ → Ω → ι → ℝ} {v : ℕ → Ω → ℝ} {s0 : ℕ} {Kq Kv K0 : ℝ}
    (h : ∀ᵐ ω ∂μ, (∀ s i, |q s ω i| ≤ Kq) ∧ (∀ s, |v s ω| ≤ Kv) ∧
      (∀ s, s ≤ s0 → ∀ i, |M s ω i| ≤ K0) ∧
      (∀ s, s0 < s → M s ω = Λ *ᵥ M (s - 1) ω + q s ω) ∧
      (∀ s, s0 < s → B2 ⬝ᵥ M s ω + v s ω = 0)) :
    ∃ K, ∀ s, ∀ᵐ ω ∂μ, ∀ i, |M s ω i| ≤ K := by
  classical
  set Q : Ω → Prop := fun ω => (∀ s i, |q s ω i| ≤ Kq) ∧ (∀ s, |v s ω| ≤ Kv) ∧
      (∀ s, s ≤ s0 → ∀ i, |M s ω i| ≤ K0) ∧
      (∀ s, s0 < s → M s ω = Λ *ᵥ M (s - 1) ω + q s ω) ∧
      (∀ s, s0 < s → B2 ⬝ᵥ M s ω + v s ω = 0) with hQ
  set M' : ℕ → Ω → ι → ℝ := fun s ω => if Q ω then M s ω else 0 with hM'
  set q' : ℕ → Ω → ι → ℝ := fun s ω => if Q ω then q s ω else 0 with hq'
  set v' : ℕ → Ω → ℝ := fun s ω => if Q ω then v s ω else 0 with hv'
  obtain ⟨K, hK⟩ := Prop82General.KrylovBound.boundedV_of_krylov h85 (M := M') (q := q')
    (v := v') (s0 := s0)
    ⟨max Kq 0, fun s ω i => by
      simp only [hq']
      split_ifs with hω
      · exact (hω.1 s i).trans (le_max_left _ _)
      · simp⟩
    ⟨max Kv 0, fun s ω => by
      simp only [hv']
      split_ifs with hω
      · exact (hω.2.1 s).trans (le_max_left _ _)
      · simp⟩
    (fun s hs ω => by
      simp only [hM', hq']
      split_ifs with hω
      · exact hω.2.2.2.1 s hs
      · simp)
    (fun s hs ω => by
      simp only [hM', hv']
      split_ifs with hω
      · exact hω.2.2.2.2 s hs
      · simp)
    ⟨max K0 0, fun s hs ω i => by
      simp only [hM']
      split_ifs with hω
      · exact (hω.2.2.1 s hs i).trans (le_max_left _ _)
      · simp⟩
  refine ⟨K, fun s => ?_⟩
  filter_upwards [h] with ω hω i
  have := hK s ω i
  simp only [hM', hω, ↓reduceIte] at this
  exact this

omit [Fintype ιτ] in
/-- Woodford (2003), eqs. (1.18)–(1.19), p. 552 (pointwise): when `M_t`, the `z`-block of
`p = E_t φ_{t+1}`, is given, (1.9) at a date splits into (1.18) and (1.19). -/
theorem foc_split_pt [Fintype ιτ] {p q : ιZ ⊕ ιz → ℝ} {v : (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {M : ιz → ℝ} (hM : Mpart p = M) :
    P.sys.Atilᵀ *ᵥ p + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ q) = 0 ↔
      (P.sys.Ahatᵀ *ᵥ p + P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) -
        P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ q) = 0) ∧
      P.sys.B2 ⬝ᵥ M + P.Ti ⬝ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) = 0 := by
  rw [Atil_transpose_mulVec, Itil_transpose_mulVec, T_transpose_mulVec, hM]
  constructor
  · intro h
    refine ⟨funext fun r => ?_, ?_⟩
    · have := congrFun h (Sum.inl r)
      simpa using this
    · have := congrFun h (Sum.inr ())
      simpa using this
  · rintro ⟨h1, h2⟩
    funext x
    rcases x with x | x
    · have := congrFun h1 x
      simpa using this
    · simpa using h2

/-- Woodford (2003), (1.18), p. 552, from (1.20), (1.21) and the forward recursion (the reverse
direction of Proposition 8.1, pointwise; the algebra of `Prop81General.prop81_equiv`): with
`E_tφ_{t+1} = (ΥM_t + (J₁')⁻¹F', M_t)`, `φ_t = (ΥM_{t−1} + (J₁')⁻¹F, M_{t−1})`,
`M_t = ΛM_{t−1} − K⁻¹(x^z_t + A₁₂'(J₁')⁻¹F')` and `F = βJ'x_t + βΨ'F'`, (1.18) holds. -/
theorem eq118_pt {Mm M : ιz → ℝ} {F Fn : ιZ → ℝ} {v : (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hM : M = PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ Mm +
      -((PencilSplit.Kmat P.sys Dsp.J)⁻¹ *ᵥ (Mpart (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))) +
        P.sys.A12ᵀ *ᵥ (((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ Fn))))
    (hF : F = (P.β • Dsp.Jᵀ) *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar))) +
      (P.β • Dsp.Ψᵀ) *ᵥ Fn) :
    P.sys.Ahatᵀ *ᵥ Sum.elim (PencilSplit.Υmat P.sys Dsp.J *ᵥ M +
        ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ Fn) M + P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) -
      P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ Sum.elim (PencilSplit.Υmat P.sys Dsp.J *ᵥ Mm +
        ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ F) Mm) = 0 := by
  set x := P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ v - P.τstar)) with hx
  set Υ := PencilSplit.Υmat P.sys Dsp.J with hΥ
  set Ji := ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ with hJi
  set pp : ιZ ⊕ ιz → ℝ := Sum.elim (Υ *ᵥ M + Ji *ᵥ Fn) M with hpp
  set qq : ιZ ⊕ ιz → ℝ := Sum.elim (Υ *ᵥ Mm + Ji *ᵥ F) Mm with hqq
  set L := P.sys.Ahatᵀ *ᵥ pp + x - P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ qq) with hL
  have hβ : P.β ≠ 0 := P.β_pos.ne'
  have hw : ∀ (ξ G : ιZ → ℝ) (m : ιz → ℝ), ξ = Υ *ᵥ m + Ji *ᵥ G →
      (Dsp.Jᵀ * P.sys.Ihatᵀ) *ᵥ Sum.elim ξ m = G := fun ξ G m h => by
    rw [Prop81General.w_split]
    exact (Prop81General.eq121_iff P.sys Dsp.J1_det ξ G m).mp h
  -- the `z`-rows vanish
  have hz : Mpart L = 0 := by
    have h120 := (Prop81General.eq120_iff P.sys P.β Dsp.K_det M Mm (Mpart x) (Ji *ᵥ Fn)).mp hM
    have hML : Mpart L = PencilSplit.Kmat P.sys Dsp.J *ᵥ M + P.sys.A12ᵀ *ᵥ (Ji *ᵥ Fn) +
        Mpart x - P.β⁻¹ • (P.sys.Etᵀ *ᵥ Mm) := by
      have e1 : Mpart (P.sys.Ahatᵀ *ᵥ pp) = P.sys.A12ᵀ *ᵥ (Υ *ᵥ M + Ji *ᵥ Fn) +
          P.sys.A22ᵀ *ᵥ M := by
        rw [PencilSplit.Ahat_transpose_mulVec]
        rfl
      have e2 : Mpart (P.sys.Ihatᵀ *ᵥ qq) = P.sys.Etᵀ *ᵥ Mm := by
        rw [PencilSplit.Ihat_transpose_mulVec]
        rfl
      have e3 : Mpart L = Mpart (P.sys.Ahatᵀ *ᵥ pp) + Mpart x -
          P.β⁻¹ • Mpart (P.sys.Ihatᵀ *ᵥ qq) := rfl
      rw [e3, e1, e2, PencilSplit.Kmat, add_mulVec, mulVec_add, ← mulVec_mulVec]
      abel
    rw [hML]
    exact h120
  -- `J'` times (1.18) vanishes
  have hJ : Dsp.Jᵀ *ᵥ L = 0 := by
    have e1 : Dsp.Jᵀ *ᵥ (P.sys.Ahatᵀ *ᵥ pp) = Dsp.Ψᵀ *ᵥ Fn := by
      rw [PencilSplit.deflate_transpose Dsp.deflate, mulVec_mulVec pp Dsp.Jᵀ, hw _ Fn M rfl]
    have e2 : Dsp.Jᵀ *ᵥ (P.sys.Ihatᵀ *ᵥ qq) = F := by
      rw [mulVec_mulVec qq Dsp.Jᵀ, hw _ F Mm rfl]
    rw [hL, mulVec_sub, mulVec_add, mulVec_smul, e1, e2, hF]
    simp only [smul_mulVec, smul_add, smul_smul, inv_mul_cancel₀ hβ, one_smul]
    abel
  rw [PencilSplit.J_transpose_mulVec] at hJ
  have hz' : L ∘ Sum.inr = 0 := hz
  rw [hz', mulVec_zero, add_zero] at hJ
  have hdet : ((PencilSplit.J1 Dsp.J)ᵀ).det ≠ 0 := by
    rw [det_transpose]
    exact Dsp.J1_det
  have hZ := eq_zero_of_mulVec_eq_zero hdet hJ
  funext a
  rcases a with i | r
  · exact congrFun hZ i
  · exact congrFun hz r

/-! ### The multipliers implied by a plan under the criterion -/

variable (P Dsp)

/-- Woodford (2003), p. 555: the multipliers `M_t` implied by a plan under the criterion: the
history `M_s = Mh_s` before `t₀`, then (1.20) `M_t = ΛM_{t−1} + q_t` with `q_t = qm`. -/
noncomputable def Mc (S : MeasExpectationSystem Ω) (Mh : ℕ → Ω → ιz → ℝ) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℕ → Ω → ιz → ℝ :=
  Mseq (PencilSplit.Λmat P.sys P.β Dsp.J) Mh t0 (qm P Dsp S y)

/-- Woodford (2003), p. 555 and (1.21): the full multiplier vector `φ_t = (ξ_t, M_{t−1})` with
`ξ_t = ΥM_{t−1} + r_t` from `t₀` on. -/
noncomputable def φc (S : MeasExpectationSystem Ω) (Mh : ℕ → Ω → ιz → ℝ) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun s ω => Sum.elim (if t0 ≤ s then PencilSplit.Υmat P.sys Dsp.J *ᵥ Mc P Dsp S Mh t0 y (s - 1) ω +
    rm P Dsp S y s ω else 0) (Mc P Dsp S Mh t0 y (s - 1) ω)

variable {P Dsp}

/-- Woodford (2003), p. 540: the implied `M_t` is known at `t` (history adapted, `q_t` known at
`t`). -/
theorem Mc_known {S : MeasExpectationSystem Ω} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hyb : MBoundedV S y) (hya : MAdaptedV S y) {Mh : ℕ → Ω → ιz → ℝ} (hMhk : MAdaptedV S Mh)
    {t0 : ℕ} (ht0 : 1 ≤ t0) : ∀ s, MKnownV S s (Mc P Dsp S Mh t0 y s) := by
  intro s
  induction s with
  | zero =>
    have : Mc P Dsp S Mh t0 y 0 = Mh 0 := by
      simp only [Mc, Mseq, show 0 < t0 by omega, ↓reduceIte]
    rw [this]
    exact hMhk 0
  | succ s ih =>
    by_cases hs : s + 1 < t0
    · have : Mc P Dsp S Mh t0 y (s + 1) = Mh (s + 1) := by
        simp only [Mc, Mseq, hs, ↓reduceIte]
      rw [this]
      exact hMhk _
    · have hrec : Mc P Dsp S Mh t0 y (s + 1) = fun ω => PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ
          Mc P Dsp S Mh t0 y s ω + qm P Dsp S y (s + 1) ω := funext fun ω => by
        have := Mseq_rec (Λ := PencilSplit.Λmat P.sys P.β Dsp.J) (Mh := Mh)
          (q := qm P Dsp S y) ht0 (s + 1) (by omega) ω
        rw [Nat.add_sub_cancel] at this
        exact this
      rw [hrec]
      intro i
      exact sm_comp₂ (fun j => (ih j).mono (S.𝓕.mono (Nat.le_succ s)))
        ((qm_known_bdd (P := P) (Dsp := Dsp) hyb hya).1 (s + 1))
        (g := fun p => (PencilSplit.Λmat P.sys P.β Dsp.J *ᵥ p.1 + p.2) i) (by fun_prop)

/-- Woodford (2003), **Proposition 8.2 (the converse direction), p. 555, with genuine conditional
expectations**: a bounded feasible plan that satisfies the target criterion (1.23) a.s. at all
`t ≥ t₀` (with a consistent, bounded, adapted history and Assumption 8.5) **solves
(1.1) + (1.9)**, with the multipliers `φc` and the initial multiplier `M_{t₀−1}` from the
history. Any disturbance; no stability of `Λ`. -/
theorem m_focSystem_of_criterion {S : MeasExpectationSystem Ω}
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D t0 : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y)
    (hcrit : MCriterion P Dsp S D t0 qh vh y) :
    MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y (φc P Dsp S Mh t0 y) := by
  classical
  have hyb := hy.2.2.1
  have hya := hy.2.2.2
  set Λ := PencilSplit.Λmat P.sys P.β Dsp.J with hΛ
  set Υ := PencilSplit.Υmat P.sys Dsp.J with hΥ
  set Ji := ((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ with hJi
  set Ms := Mc P Dsp S Mh t0 y with hMs
  set qs := splice t0 qh (qm P Dsp S y) with hqs
  set vs := splice t0 vh (vproc P y) with hvs
  have ht0 : 1 ≤ t0 := by omega
  -- the criterion with `qm`
  have hc' : ∀ᵐ ω ∂S.μ, ∀ t, t0 ≤ t → TargetCriterion.Crit.crit (Adjugate.alpha Λ)
      (Adjugate.Bpoly Λ) D P.sys.B2 vs qs t ω = 0 := by
    have hq : ∀ᵐ ω ∂S.μ, ∀ u, qm P Dsp S y u ω = qM P Dsp S y u ω :=
      ae_all_iff.2 fun u => qm_eq_qM (P := P) (Dsp := Dsp) hyb hya u
    refine ae_all_iff.2 fun t => ?_
    by_cases ht : t0 ≤ t
    · filter_upwards [hcrit t ht, hq] with ω e hω _
      have hqq : ∀ u, qs u ω = splice t0 qh (qM P Dsp S y) u ω := fun u => by
        simp only [hqs, splice]
        split_ifs
        · rfl
        · exact hω u
      rw [crit_congr _ _ _ _ _ t ω hqq]
      exact e
    · exact Eventually.of_forall fun _ h => absurd h ht
  -- (1.20) for the spliced processes
  have h120 : ∀ᵐ ω ∂S.μ, ∀ s, t0 - D ≤ s → Ms s ω = Λ *ᵥ Ms (s - 1) ω + qs s ω := by
    have hh : ∀ s, ∀ᵐ ω ∂S.μ, t0 - D ≤ s → s < t0 → Mh s ω = Λ *ᵥ Mh (s - 1) ω + qh s ω := by
      intro s
      by_cases hs : t0 - D ≤ s ∧ s < t0
      · filter_upwards [hhist.1 s hs.1 hs.2] with ω e _ _
        exact e
      · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hs
    filter_upwards [ae_all_iff.2 hh] with ω e s hs
    by_cases hlt : s < t0
    · simp only [hMs, Mc, Mseq, hqs, splice, hlt, ↓reduceIte, show s - 1 < t0 by omega]
      exact e s hs hlt
    · simp only [hqs, splice, hlt, ↓reduceIte]
      exact Mseq_rec ht0 s (by omega) ω
  -- (1.19) from the criterion (Proposition 8.2's key step)
  have h119 : ∀ᵐ ω ∂S.μ, ∀ s, t0 - D ≤ s → P.sys.B2 ⬝ᵥ Ms s ω + vs s ω = 0 := by
    have hh : ∀ s, ∀ᵐ ω ∂S.μ, t0 - D ≤ s → s < t0 → P.sys.B2 ⬝ᵥ Mh s ω + vh s ω = 0 := by
      intro s
      by_cases hs : t0 - D ≤ s ∧ s < t0
      · filter_upwards [hhist.2 s hs.1 hs.2] with ω e _ _
        exact e
      · exact Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hs
    filter_upwards [hc', h120, ae_all_iff.2 hh] with ω e1 e2 e3
    have := TargetCriterion.Crit.eq119_of_criterion (Adjugate.eq122 Λ)
      (Adjugate.alpha_coeff_zero Λ) hB hα P.sys.B2 (M := fun u (_ : Unit) => Ms u ω)
      (q := fun u (_ : Unit) => qs u ω) (v := fun u (_ : Unit) => vs u ω) (t1 := t0 - D)
      (t0 := t0) (by omega) (fun u hu _ => e2 u hu)
      (fun u hu hlt _ => by
        simp only [hMs, Mc, Mseq, hvs, splice, hlt, ↓reduceIte]
        exact e3 u hu hlt)
      (fun u hu _ => e1 u hu)
    exact fun s hs => this s hs ()
  -- the multipliers are bounded (Assumption 8.5)
  obtain ⟨KMh, hKMh⟩ := hMhb
  obtain ⟨Kqh, hKqh⟩ := hqhb
  obtain ⟨Kvh, hKvh⟩ := hvhb
  obtain ⟨Kqm, hKqm⟩ := (qm_known_bdd (P := P) (Dsp := Dsp) hyb hya).2
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨Kv, hKv⟩ := vv_bound P Ky
  obtain ⟨KM, hKM⟩ : ∃ KM, ∀ s, ∀ᵐ ω ∂S.μ, ∀ i, |Ms s ω i| ≤ KM := by
    refine krylov_ae h85 (q := qs) (v := vs) (s0 := t0 - D - 1) (Kq := max Kqh Kqm)
      (Kv := max Kvh Kv) (K0 := KMh) ?_
    filter_upwards [h120, h119, ae_all_iff.2 hKMh, ae_all_iff.2 hKqh, ae_all_iff.2 hKvh,
      ae_all_iff.2 hKqm, ae_all_iff.2 hKy] with ω e1 e2 b1 b2 b3 b4 b5
    refine ⟨fun s i => ?_, fun s => ?_, fun s hs i => ?_, fun s hs => e1 s (by omega),
      fun s hs => e2 s (by omega)⟩
    · simp only [hqs, splice]
      split_ifs
      · exact (b2 s i).trans (le_max_left _ _)
      · exact (b4 s i).trans (le_max_right _ _)
    · simp only [hvs, splice]
      split_ifs
      · exact (b3 s).trans (le_max_left _ _)
      · exact (hKv _ (b5 s)).trans (le_max_right _ _)
    · simp only [hMs, Mc, Mseq, show s < t0 by omega, ↓reduceIte]
      exact b1 s i
  have hyb : MBoundedV S y := ⟨Ky, hKy⟩
  obtain ⟨KF, hKF⟩ := Fm_bdd (P := P) (Dsp := Dsp) hyb
  have hMk := Mc_known (P := P) (Dsp := Dsp) hyb hya hMhk ht0
  have hMi : ∀ s i, Integrable (fun ω => Ms s ω i) S.μ := fun s i =>
    integrable_of_bound ((hMk s i).mono (S.𝓕.le s)).aestronglyMeasurable
      ((hKM s).mono fun ω h => h i)
  have hri : ∀ s i, Integrable (fun ω => rm P Dsp S y s ω i) S.μ := fun s i =>
    integrable_of_bound (((rm_known (P := P) (Dsp := Dsp) S y s).2 i).mono
      (S.𝓕.le s)).aestronglyMeasurable ((hKF s).mono fun ω h => h.2 i)
  obtain ⟨KΥ, hKΥ⟩ := exists_bound_mulVec Υ KM
  refine ⟨hy, ⟨max (max (KΥ + KF) KM) 0, fun s => ?_⟩, fun s i => ?_, fun t r => ?_,
    Eventually.of_forall fun ω => ?_, fun t ht => ?_⟩
  · -- bounded multipliers
    filter_upwards [hKM (s - 1), hKF s] with ω h1 h2 i
    rcases i with j | r
    · simp only [φc, Sum.elim_inl]
      split_ifs
      · exact ((abs_add_le _ _).trans (add_le_add (hKΥ _ h1 j) (h2.2 j))).trans
          ((le_max_left _ _).trans (le_max_left _ _))
      · simp only [Pi.zero_apply, abs_zero]
        exact le_max_right _ _
    · exact (h1 r).trans ((le_max_right _ _).trans (le_max_left _ _))
  · -- measurable multipliers
    rcases i with j | r
    · by_cases hs : t0 ≤ s
      · have : (fun ω => φc P Dsp S Mh t0 y s ω (Sum.inl j)) =
            fun ω => (Υ *ᵥ Ms (s - 1) ω + rm P Dsp S y s ω) j := by
          funext ω
          simp only [φc, hs, ↓reduceIte, Sum.elim_inl]
          rfl
        rw [this]
        exact ((integrable_mulVec _ (hMi (s - 1)) j).add (hri s j)).aestronglyMeasurable
      · have : (fun ω => φc P Dsp S Mh t0 y s ω (Sum.inl j)) = fun _ => 0 := by
          funext ω
          simp only [φc, hs, ↓reduceIte, Sum.elim_inl, Pi.zero_apply]
        rw [this]
        exact aestronglyMeasurable_const
    · exact ((hMk (s - 1) r).mono (S.𝓕.le _)).aestronglyMeasurable
  · -- `M_t` known at `t`
    exact hMk t r
  · -- the initial multiplier
    funext r
    simp only [φc, Mpart, Sum.elim_inr, Mc, Mseq, show t0 - 1 < t0 by omega, ↓reduceIte]
  · -- (1.9)
    have hφ1 : ∀ ω, φc P Dsp S Mh t0 y (t + 1) ω =
        Sum.elim (Υ *ᵥ Ms t ω + rm P Dsp S y (t + 1) ω) (Ms t ω) := fun ω => by
      simp only [φc, show t0 ≤ t + 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
      rfl
    have hφ0 : ∀ ω, φc P Dsp S Mh t0 y t ω =
        Sum.elim (Υ *ᵥ Ms (t - 1) ω + Ji *ᵥ Fm P Dsp S y t ω) (Ms (t - 1) ω) := fun ω => by
      simp only [φc, ht, ↓reduceIte]
      rfl
    have hFi : ∀ i, Integrable (fun ω => Fm P Dsp S y (t + 1) ω i) S.μ := fun i =>
      S.integrable_E _ _
    have hErm : ∀ᵐ ω ∂S.μ, EVm S t (rm P Dsp S y (t + 1)) ω =
        Ji *ᵥ EVm S t (Fm P Dsp S y (t + 1)) ω := by
      filter_upwards [EVm_mulVec S t Ji hFi] with ω e
      exact e
    have hE : ∀ᵐ ω ∂S.μ, EVm S t (φc P Dsp S Mh t0 y (t + 1)) ω =
        Sum.elim (Υ *ᵥ Ms t ω + Ji *ᵥ EVm S t (Fm P Dsp S y (t + 1)) ω) (Ms t ω) := by
      filter_upwards [EVm_add S t (x := fun ω => Υ *ᵥ Ms t ω) (x' := rm P Dsp S y (t + 1))
        (integrable_mulVec _ (hMi t)) (hri (t + 1)), EVm_mulVec S t Υ (hMi t), hErm]
        with ω e1 e2 e3
      funext idx
      rcases idx with j | r
      · have hfun : (fun ω' => φc P Dsp S Mh t0 y (t + 1) ω' (Sum.inl j)) =
            fun ω' => (Υ *ᵥ Ms t ω' + rm P Dsp S y (t + 1) ω') j := funext fun ω' => by
          rw [hφ1]
          rfl
        change S.E t (fun ω' => φc P Dsp S Mh t0 y (t + 1) ω' (Sum.inl j)) ω = _
        rw [hfun]
        have := congrFun e1 j
        simp only [EVm] at this
        rw [this, Pi.add_apply, e2, e3, EVm_of_known S (hMk t) (hMi t)]
        rfl
      · change S.E t (fun ω' => φc P Dsp S Mh t0 y (t + 1) ω' (Sum.inr r)) ω = _
        exact congrFun (S.E_of_stronglyMeasurable (hMk t r) (hMi t r)) ω
    filter_upwards [hE, Fm_rec (P := P) (Dsp := Dsp) hyb hya t, h119, hErm] with ω e f g h
    rw [e]
    refine (foc_split_pt (P := P) (M := Ms t ω) rfl).mpr ⟨?_, ?_⟩
    · rw [hφ0 ω]
      have hM : Ms t ω = Λ *ᵥ Ms (t - 1) ω + -((PencilSplit.Kmat P.sys Dsp.J)⁻¹ *ᵥ
          (Mpart (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar))) +
            P.sys.A12ᵀ *ᵥ (Ji *ᵥ EVm S t (Fm P Dsp S y (t + 1)) ω))) := by
        have := Mseq_rec (Λ := Λ) (Mh := Mh) (q := qm P Dsp S y) ht0 t ht ω
        refine this.trans ?_
        unfold qm
        rw [h]
        rfl
      exact eq118_pt (P := P) (Dsp := Dsp) hM f
    · have := g t (by omega)
      simp only [hvs, splice, show ¬ t < t0 by omega, ↓reduceIte] at this
      exact this

/-! ### Determinacy -/

/-- Woodford (2003), **Proposition 8.2 (determinacy, uniqueness)**, p. 555, with genuine
conditional expectations: under the measure Assumption 8.1 (uniqueness half) and Assumption 8.5,
two bounded feasible plans that satisfy the target criterion (1.23) a.s. from `t₀` on (same
history, same disturbance and `Z_{t₀}`) agree a.s. at every `t ≥ t₀`. -/
theorem m_prop82_unique {S : MeasExpectationSystem Ω} {t0 : ℕ} (hU : MFOCUnique S P t0)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y)
    (hy' : MFeasible S P c t0 Z0 y') (hcrit : MCriterion P Dsp S D t0 qh vh y)
    (hcrit' : MCriterion P Dsp S D t0 qh vh y') : ∀ t, t0 ≤ t → y t =ᵐ[S.μ] y' t := fun t ht =>
  (hU c Z0 (Mh (t0 - 1)) y y' _ _
    (m_focSystem_of_criterion h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy hcrit)
    (m_focSystem_of_criterion h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy' hcrit') t ht).1

/-- Woodford (2003), **Proposition 8.2 (determinacy)**, p. 555, **on every probability space from
the perfect-foresight Assumption 8.1**: if bounded solutions of (1.1) + (1.9) are unique under
perfect foresight, two bounded feasible plans satisfying (1.23) a.s. agree a.s. (any filtered
probability space, any disturbance; `OptimalRulesMeasureForecast.m_focUnique_of_pf`). -/
theorem m_prop82_unique_pf {S : MeasExpectationSystem Ω} {t0 : ℕ}
    (hU : FOCUnique P perfectForesight 0)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y)
    (hy' : MFeasible S P c t0 Z0 y') (hcrit : MCriterion P Dsp S D t0 qh vh y)
    (hcrit' : MCriterion P Dsp S D t0 qh vh y') : ∀ t, t0 ≤ t → y t =ᵐ[S.μ] y' t :=
  m_prop82_unique (m_focUnique_of_pf hU S t0) h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy hy'
    hcrit hcrit'

/-- Woodford (2003), **Proposition 8.2**, p. 555: **the plan determined by commitment to (1.23) is
the optimal plan** — a bounded feasible plan satisfying (1.23) a.s. equals a.s., from `t₀` on,
the solution of (1.1) + (1.9) with `M_{t₀−1}` from the history (under the measure Assumption 8.1,
uniqueness half). -/
theorem m_criterion_eq_foc {S : MeasExpectationSystem Ω} {t0 : ℕ} (hU : MFOCUnique S P t0)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φs : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) ys φs) {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : MFeasible S P c t0 Z0 y) (hcrit : MCriterion P Dsp S D t0 qh vh y) :
    ∀ t, t0 ≤ t → y t =ᵐ[S.μ] ys t := fun t ht =>
  (hU c Z0 (Mh (t0 - 1)) y ys _ φs
    (m_focSystem_of_criterion h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy hcrit) hs t ht).1

/-- Woodford (2003), **Propositions 8.1–8.2 (the equivalence)**, p. 555, with genuine conditional
expectations: for a bounded feasible plan and a consistent history, the target criterion (1.23)
holds a.s. from `t₀` on **iff** the plan solves (1.1) + (1.9) with `M_{t₀−1}` from the history.
Any disturbance. -/
theorem m_criterion_iff {S : MeasExpectationSystem Ω}
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D t0 : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : MFeasible S P c t0 Z0 y) :
    MCriterion P Dsp S D t0 qh vh y ↔ ∃ φ, MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ := by
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ := fun r =>
    ((hMhk (t0 - 1) r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  exact ⟨fun h => ⟨_, m_focSystem_of_criterion h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy h⟩,
    fun ⟨_, h⟩ => m_criterion P Dsp hD hB hα hhist h hM0⟩

/-- Woodford (2003), **Proposition 8.2 on every VAR economy**, p. 555: under the perfect-foresight
Assumption 8.1, geometric stability of `H_n` and Assumption 8.5, for every VAR(1) exogenous state,
every bounded `Z_{t₀}` known at `t₀` and every consistent bounded adapted history, **commitment to
(1.23) determines exactly one bounded equilibrium a.s., and it is optimal from a timeless
perspective** (with `X̄_t = (Z_t, M_{t−1}, s_t)`). -/
theorem m_prop82_var {ιs : Type*} [Fintype ιs] [DecidableEq ιs] (A : Matrix ιs ιs ℝ)
    (C2 : Matrix ιz ιs ℝ) (hA81 : Assumption81 P perfectForesight 0) (hA : PowBdd A)
    (hstab : PencilSplit.PowDecay (Hn P A C2 hA81 hA)) {S : MeasExpectationSystem Ω}
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D t0 : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) {s : ℕ → Ω → ιs → ℝ} (hs : IsVAR S A s)
    {Z0 : Ω → ιZ → ℝ} (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 y ∧ MCriterion P Dsp S D t0 qh vh y ∧
      (∀ y', MFeasible S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 y' → MCriterion P Dsp S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MTimelesslyOptimalPlan S P (fun t ω => C2 *ᵥ s t ω) t0 Z0 (stateX y φ s)
        (zpart (fY P A C2 hA81 hA)) ((FY P A C2 hA81 hA).submatrix (Sum.inl ∘ Sum.inr) id) y := by
  have hMb : MBoundedRV S (Mh (t0 - 1)) := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, hK (t0 - 1)⟩
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ := fun r =>
    ((hMhk (t0 - 1) r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  obtain ⟨y, φ, hsol, -, hopt⟩ :=
    m_existsUnique_var P A C2 hA81 hA hstab hs hZk hZb hMb (hMhk (t0 - 1))
  refine ⟨y, hsol.1, m_criterion P Dsp hD hB hα hhist hsol hM0, fun y' hy' hc' t ht => ?_,
    φ, hopt⟩
  exact m_criterion_eq_foc (m_focUnique_of_pf hA81.unique S t0) h85 hD hB hα hhist hMhb hMhk
    hqhb hvhb hsol hy' hc' t ht

/-! ### Link with the core (perfect foresight) -/

omit [Fintype ιτ] in
/-- Woodford (2003), eq. (1.25) under perfect foresight: `Prop81General.Qop` written out. -/
theorem Qop_pf_eq (x : ℕ → Unit → ιZ ⊕ ιz → ℝ) (t : ℕ) :
    Prop81General.Qop perfectForesight Dsp x t () = -((PencilSplit.Kmat P.sys Dsp.J)⁻¹ *ᵥ
      (Mpart (x t ()) + P.sys.A12ᵀ *ᵥ (((PencilSplit.J1 Dsp.J)ᵀ)⁻¹ *ᵥ
        fun i => ∑' k, ((P.β • Dsp.Ψᵀ) ^ k *ᵥ ((P.β • Dsp.Jᵀ) *ᵥ x (t + 1 + k) ())) i))) := rfl

/-- Woodford (2003), eq. (1.25) (link): on the one-point probability space (perfect foresight) the
forecast-based `q_t` is the core operator `Prop81General.Qop perfectForesight` applied to the
plan. -/
theorem qM_unit (y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) :
    qM P Dsp Bridge.unitSystem y t () =
      Prop81General.Qop perfectForesight Dsp (xproc P y) t () := by
  rw [qM_eq, Qop_pf_eq]
  have hfc : ∀ k, EVm Bridge.unitSystem t (y (t + k)) () = y (t + k) () := fun k =>
    fc_unitSystem y t k ()
  have h0 : xproc P (fun k (_ : Unit) => EVm Bridge.unitSystem t (y (t + k)) ()) 0 () =
      xproc P y t () := by
    change P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ EVm Bridge.unitSystem t (y (t + 0)) () - P.τstar)) = _
    rw [hfc 0]
    rfl
  have h1 : (fun i => ∑' k, ((P.β • Dsp.Ψᵀ) ^ k *ᵥ ((P.β • Dsp.Jᵀ) *ᵥ
      xproc P (fun k (_ : Unit) => EVm Bridge.unitSystem t (y (t + k)) ()) (0 + 1 + k) ())) i) =
      fun i => ∑' k, ((P.β • Dsp.Ψᵀ) ^ k *ᵥ ((P.β • Dsp.Jᵀ) *ᵥ xproc P y (t + 1 + k) ())) i := by
    funext i
    refine tsum_congr fun k => ?_
    change ((P.β • Dsp.Ψᵀ) ^ k *ᵥ ((P.β • Dsp.Jᵀ) *ᵥ (P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ
      EVm Bridge.unitSystem t (y (t + (0 + 1 + k))) () - P.τstar))))) i = _
    rw [hfc, show t + (0 + 1 + k) = t + 1 + k by omega]
    rfl
  rw [h0, h1]

/-- Woodford (2003), **(1.23) (link with the core)**: on the one-point probability space the
measure-theoretic criterion `MCriterion` is exactly the core criterion
`Prop82General.Prop82M.CriterionM` for the matrices of `Prop81General.prop81` under perfect
foresight. -/
theorem mCriterion_unit_iff {D t0 : ℕ} (qh : ℕ → Unit → ιz → ℝ) (vh : ℕ → Unit → ℝ)
    (y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    MCriterion P Dsp Bridge.unitSystem D t0 qh vh y ↔
      Prop82General.Prop82M.CriterionM (Prop81General.prop81 P Dsp perfectForesight t0) D qh vh
        y := by
  have hq : ∀ u, splice t0 qh (qM P Dsp Bridge.unitSystem y) u () =
      splice t0 qh (Prop81General.Qop perfectForesight Dsp (xproc P y)) u () := fun u => by
    simp only [splice]
    split_ifs
    · rfl
    · exact qM_unit y u
  constructor
  · intro h t ht ω
    rcases ω
    have := (Bridge.ae_iff_forall Bridge.unitSystem_full).mp (h t ht) ()
    rw [crit_congr _ _ _ _ _ t () hq] at this
    exact this
  · intro h t ht
    refine (Bridge.ae_iff_forall Bridge.unitSystem_full).mpr fun ω => ?_
    rcases ω
    rw [crit_congr _ _ _ _ _ t () hq]
    exact h t ht ()

end Woodford.OptimalPolicyRules.OptimalRulesMeasureConverse
