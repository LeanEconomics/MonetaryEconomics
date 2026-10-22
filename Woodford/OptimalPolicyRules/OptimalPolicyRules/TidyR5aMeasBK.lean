/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureQuasiSplit
import OptimalPolicyRules.TidyR5aExogenousInstrument

/-!
# The Blanchard–Kahn theorem with conditional expectations

Woodford (2003), *Interest and Prices*, Appendix C.1, pp. 670–672 (Blanchard and Kahn 1980), on a
filtered probability space with Mathlib's conditional expectation (`MeasExpectationSystem`).

The system is `E_t y_{t+1} = A y_t + w_t` a.s. with `y = (z, x)`, `x` predetermined (`x_{t+1}`
known at `t`), `x_0` given, and solutions essentially bounded and adapted (`MEquil`). The
perfect-foresight Blanchard–Kahn split of `BKInvariantSplit` (no unit eigenvalue, the
bounded-orbit subspace of dimension `|X|`, genericity) supplies the graph `z = Gx` of the stable
subspace, `Λ` stable and `C` unstable. Then:

* `m_bk_exists`: an equilibrium exists for every essentially bounded adapted forcing and every
  essentially bounded `x₀` known at `0`: `ẑ_t = E_t ∑_k (C⁻¹)ᵏ⁺¹(…)` (`fwdM`, the forward sum with
  conditional expectations, `fwdM_rec`, `fwdM_bdd`, `fwdM_adapted`) and
  `x_{t+1} = Λx_t + A_xz ẑ_t + w_{x,t}` (`xrecM`);
* `m_bk_unique`: two equilibria with the same forcing and `x₀` agree a.s. at every date
  (`ẑ` of the difference is a bounded solution of `ẑ_t = C⁻¹E_tẑ_{t+1}`, hence `0` by
  `OptimalRulesMeasureQuasiSplit.m_fwd_zero`).

These are the measure-theoretic tools used by `TidyR5aLambdaXZeroMeasure` (existence of the rule
system's solution) and `TidyR5aRuleIIIMeasure` (the forward sums of the modification).
-/

namespace Woodford.OptimalPolicyRules.TidyR5aMeasBK

open MeasureTheory Filter Topology Matrix GeneralSetup
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov
open BKInvariantSplit

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The forward solution with conditional expectations -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), App. C.1, p. 670: the realised forward sum `R_t = ∑_k Kᵏ f_{t+k}`. -/
noncomputable def Rf (K : Matrix ι ι ℝ) (f : ℕ → Ω → ι → ℝ) (t : ℕ) (ω : Ω) : ι → ℝ :=
  fun i => ∑' k, (K ^ k *ᵥ f (t + k) ω) i

/-- Woodford (2003), App. C.1, p. 670: the forward solution `s_t = E_t ∑_k Kᵏ f_{t+k}` of
`s_t = K E_t s_{t+1} + f_t`, with Mathlib's conditional expectation. -/
noncomputable def fwdM (S : MeasExpectationSystem Ω) (K : Matrix ι ι ℝ) (f : ℕ → Ω → ι → ℝ)
    (t : ℕ) : Ω → ι → ℝ :=
  EVm S t (Rf K f t)

/-- Woodford (2003), App. C.1 (tool): along an essentially bounded forcing, a.s. at every date
the realised forward sum converges, is bounded by a constant and satisfies
`R_t = f_t + K R_{t+1}`. -/
theorem rf_spec {S : MeasExpectationSystem Ω} {K : Matrix ι ι ℝ} (hK : PencilSplit.PowDecay K)
    {f : ℕ → Ω → ι → ℝ} (hfb : MBoundedV S f) :
    ∃ KR, ∀ᵐ ω ∂S.μ, ∀ t, (∀ i, HasSum (fun k => (K ^ k *ᵥ f (t + k) ω) i) (Rf K f t ω i)) ∧
      (∀ i, |Rf K f t ω i| ≤ KR) ∧ Rf K f t ω = f t ω + K *ᵥ Rf K f (t + 1) ω := by
  obtain ⟨M, hM⟩ := hfb
  obtain ⟨KR, hKR⟩ := OptimalRulesMeasureConverse.geom_vec hK M
  refine ⟨KR, ?_⟩
  filter_upwards [ae_all_iff.2 hM] with ω hω
  intro t
  have h0 := fun i => hKR (fun k => f (t + k) ω) (fun k j => hω (t + k) j) i
  have h1 := fun i => hKR (fun k => f (t + 1 + k) ω) (fun k j => hω (t + 1 + k) j) i
  refine ⟨fun i => (h0 i).1.hasSum, fun i => (h0 i).2, ?_⟩
  have hs1 : ∀ i, Summable (fun k => (K ^ k *ᵥ f (t + (k + 1)) ω) i) := by
    intro i
    refine (h1 i).1.congr fun k => ?_
    rw [show t + (k + 1) = t + 1 + k by omega]
  have := OptimalRulesMeasureConverse.geom_shift K (fun k => f (t + k) ω) (fun i => (h0 i).1)
    hs1
  have e1 : Rf K f t ω = fun i => ∑' k, (K ^ k *ᵥ (fun k => f (t + k) ω) k) i := rfl
  rw [e1, this]
  simp only [add_zero]
  refine congrArg₂ (· + ·) rfl (congrArg _ (funext fun i => tsum_congr fun k => ?_))
  show (K ^ k *ᵥ f (t + (k + 1)) ω) i = (K ^ k *ᵥ f (t + 1 + k) ω) i
  rw [show t + (k + 1) = t + 1 + k by omega]

/-- Woodford (2003), App. C.1 (tool): the realised forward sum of a bounded adapted forcing is
integrable (the a.e. limit of its partial sums). -/
theorem rf_integrable {S : MeasExpectationSystem Ω} {K : Matrix ι ι ℝ}
    (hK : PencilSplit.PowDecay K) {f : ℕ → Ω → ι → ℝ} (hfb : MBoundedV S f)
    (hfa : MAdaptedV S f) (t : ℕ) (i : ι) : Integrable (fun ω => Rf K f t ω i) S.μ := by
  obtain ⟨KR, hKR⟩ := rf_spec hK hfb
  have hterm : ∀ k, AEStronglyMeasurable (fun ω => (K ^ k *ᵥ f (t + k) ω) i) S.μ := fun k =>
    aesm_comp (fun j => ((hfa (t + k) j).mono (S.𝓕.le _)).aestronglyMeasurable)
      (g := fun v => (K ^ k *ᵥ v) i) (by fun_prop)
  have hm : AEStronglyMeasurable (fun ω => Rf K f t ω i) S.μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, (K ^ k *ᵥ f (t + k) ω) i)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hterm k) ?_
    filter_upwards [hKR] with ω h
    exact ((h t).1 i).tendsto_sum_nat
  exact integrable_of_bound hm (hKR.mono fun ω h => (h t).2.1 i)

/-- **Woodford (2003), App. C.1, p. 670, with conditional expectations: the forward recursion**
`s_t = f_t + K E_t s_{t+1}` a.s. (law of iterated expectations). -/
theorem fwdM_rec {S : MeasExpectationSystem Ω} {K : Matrix ι ι ℝ}
    (hK : PencilSplit.PowDecay K) {f : ℕ → Ω → ι → ℝ} (hfb : MBoundedV S f)
    (hfa : MAdaptedV S f) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, fwdM S K f t ω = f t ω + K *ᵥ EVm S t (fwdM S K f (t + 1)) ω := by
  obtain ⟨KR, hKR⟩ := rf_spec hK hfb
  have hfi : ∀ i, Integrable (fun ω => f t ω i) S.μ := integrable_of_adapted hfb hfa t
  have hRi := rf_integrable hK hfb hfa (t + 1)
  have hrec : ∀ᵐ ω ∂S.μ, Rf K f t ω = (1 : Matrix ι ι ℝ) *ᵥ f t ω + K *ᵥ Rf K f (t + 1) ω +
      (0 : Matrix ι ι ℝ) *ᵥ Rf K f t ω + 0 := by
    filter_upwards [hKR] with ω h
    rw [zero_mulVec, add_zero, add_zero, one_mulVec]
    exact (h t).2.2
  filter_upwards [EVm_congr S t hrec, EVm_affine3 S t (1 : Matrix ι ι ℝ) K (0 : Matrix ι ι ℝ) 0
    hfi hRi (rf_integrable hK hfb hfa t), EVm_tower S (Nat.le_succ t) (Rf K f (t + 1))]
    with ω e1 e2 e3
  unfold fwdM
  rw [e1, e2, zero_mulVec, add_zero, add_zero, one_mulVec, EVm_of_known S (hfa t) hfi, e3]

/-- Woodford (2003), App. C.1: the forward solution is adapted. -/
theorem fwdM_adapted (S : MeasExpectationSystem Ω) (K : Matrix ι ι ℝ) (f : ℕ → Ω → ι → ℝ) :
    MAdaptedV S (fwdM S K f) :=
  fun t _ => S.stronglyMeasurable_E t _

/-- Woodford (2003), App. C.1: the forward solution of a bounded forcing is essentially
bounded. -/
theorem fwdM_bdd {S : MeasExpectationSystem Ω} {K : Matrix ι ι ℝ} (hK : PencilSplit.PowDecay K)
    {f : ℕ → Ω → ι → ℝ} (hfb : MBoundedV S f) : MBoundedV S (fwdM S K f) := by
  obtain ⟨KR, hKR⟩ := rf_spec hK hfb
  exact ⟨KR, fun t => ae_all_iff.2 fun i =>
    S.abs_E_le (hKR.mono fun ω h => (h t).2.1 i) t⟩

/-! ### The Blanchard–Kahn equilibrium with conditional expectations -/

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, p. 670, with Mathlib's conditional expectation: `y` is an
equilibrium of `E_t y_{t+1} = A y_t + w_t` (a.s. at every date) with predetermined block `x`
(`x_{t+1}` known at `t`) and `x_0 = x₀` a.s.; essentially bounded and adapted. -/
def MEquil (S : MeasExpectationSystem Ω) (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ)
    (w : ℕ → Ω → Z ⊕ X → ℝ) (x0 : Ω → X → ℝ) (y : ℕ → Ω → Z ⊕ X → ℝ) : Prop :=
  (∀ t, ∀ᵐ ω ∂S.μ, EVm S t (y (t + 1)) ω = A *ᵥ y t ω + w t ω) ∧ MAdaptedV S y ∧
    (∀ t, MKnownV S t (fun ω j => y (t + 1) ω (Sum.inr j))) ∧
    (∀ᵐ ω ∂S.μ, ∀ j, y 0 ω (Sum.inr j) = x0 ω j) ∧ MBoundedV S y

/-- Woodford (2003), App. C.1, p. 672 (tool): **the algebra of the Blanchard–Kahn solution**. If
`ẑ` obeys `E ẑ' = Cẑ + w_z − G w_x` and `x' = Λx + A_xz ẑ + w_x`, then `(ẑ + Gx, x)` obeys
`E y' = Ay + w` (graph invariance `A_zz G + A_zx = GΛ`). -/
theorem bk_alg {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G)
    (zh zE wz : Z → ℝ) (x xn wx : X → ℝ) (hzE : zE = cmat A G *ᵥ zh + (wz - G *ᵥ wx))
    (hxn : xn = lam A G *ᵥ x + A.toBlocks₂₁ *ᵥ zh + wx) :
    Sum.elim (zE + G *ᵥ xn) xn = A *ᵥ Sum.elim (zh + G *ᵥ x) x + Sum.elim wz wx := by
  have hinv := graph_invariant hG
  have e : G *ᵥ (lam A G *ᵥ x) = A.toBlocks₁₁ *ᵥ (G *ᵥ x) + A.toBlocks₁₂ *ᵥ x := by
    rw [mulVec_mulVec, ← hinv, add_mulVec, mulVec_mulVec]
  have h1 : zE + G *ᵥ xn = A.toBlocks₁₁ *ᵥ (zh + G *ᵥ x) + A.toBlocks₁₂ *ᵥ x + wz := by
    rw [hzE, hxn, cmat, sub_mulVec, mulVec_add, mulVec_add, e, mulVec_add, ← mulVec_mulVec]
    abel
  have h2 : xn = A.toBlocks₂₁ *ᵥ (zh + G *ᵥ x) + A.toBlocks₂₂ *ᵥ x + wx := by
    rw [hxn, lam, add_mulVec, mulVec_add, ← mulVec_mulVec]
    abel
  rw [mulVec_sumElim, h1, h2]
  funext k
  rcases k with i | j <;> rfl

/-- Woodford (2003), App. C.1, p. 670 (tool): the backward recursion
`x_{t+1} = L x_t + g_t`, `x_0 = x₀`, on random vectors. -/
def xrecM (L : Matrix X X ℝ) (g : ℕ → Ω → X → ℝ) (x0 : Ω → X → ℝ) : ℕ → Ω → X → ℝ
  | 0 => x0
  | t + 1 => fun ω => L *ᵥ xrecM L g x0 t ω + g t ω

/-- **Woodford (2003), App. C.1, p. 670 (Blanchard–Kahn, sufficiency), on a filtered probability
space with Mathlib's conditional expectation.** If no eigenvalue of `A` lies on the unit circle,
the bounded-orbit subspace has dimension `|X|` and the genericity condition holds, then for every
essentially bounded adapted forcing and every essentially bounded `x₀` known at date `0` there is
an equilibrium (`ẑ_t = E_t ∑_k Kᵏ f_{t+k}`, `x_{t+1} = Λx_t + A_xz ẑ_t + w_{x,t}`). -/
theorem m_bk_exists {S : MeasExpectationSystem Ω} {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hnu : NoUnit A) (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X)
    (hg : GenericX A) {w : ℕ → Ω → Z ⊕ X → ℝ} (hwb : MBoundedV S w) (hwa : MAdaptedV S w)
    {x0 : Ω → X → ℝ} (hx0k : MKnownV S 0 x0) (hx0b : MBoundedRV S x0) :
    ∃ y, MEquil S A w x0 y := by
  classical
  obtain ⟨G, hG⟩ := exists_graph hd hg
  have hΛ := lam_stable hG hnu
  have hC := cmat_unstable hG hg hΛ
  have hdet : IsUnit (cmat A G).det :=
    isUnit_iff_ne_zero.mpr (GeneralBKCopy.det_ne_zero_of_unstable hC)
  set K := (cmat A G)⁻¹ with hKdef
  have hCK : cmat A G * K = 1 := Matrix.mul_nonsing_inv _ hdet
  obtain ⟨CbK, ρK, -, hρK0, hρK1, hKpow⟩ := pow_entry_bound K (GeneralBKCopy.inv_stable hC)
  have hKd : PencilSplit.PowDecay K := ⟨CbK, ρK, hρK0.le, hρK1, hKpow⟩
  obtain ⟨CbL, ρL, hCbL, hρL0, hρL1, hLpow⟩ := pow_entry_bound (lam A G) hΛ
  set wz : ℕ → Ω → Z → ℝ := fun t ω i => w t ω (Sum.inl i) with hwz
  set wx : ℕ → Ω → X → ℝ := fun t ω j => w t ω (Sum.inr j) with hwx
  set f : ℕ → Ω → Z → ℝ := fun t ω => -(K *ᵥ (wz t ω - G *ᵥ wx t ω)) with hf
  obtain ⟨Mw, hMw⟩ := hwb
  have hfb : MBoundedV S f := by
    obtain ⟨K1, hK1⟩ := GeneralFOC.exists_bound_mulVec G Mw
    obtain ⟨K2, hK2⟩ := GeneralFOC.exists_bound_mulVec K (Mw + K1)
    refine ⟨K2, fun t => ?_⟩
    filter_upwards [hMw t] with ω h i
    have hv : ∀ i, |(wz t ω - G *ᵥ wx t ω) i| ≤ Mw + K1 := fun i =>
      (abs_sub _ _).trans (add_le_add (h _) (hK1 _ (fun j => h _) i))
    simp only [hf, Pi.neg_apply, abs_neg]
    exact hK2 _ hv i
  have hfa : MAdaptedV S f := fun t i => sm_comp (hwa t)
    (g := fun v => (-(K *ᵥ ((fun i => v (Sum.inl i)) - G *ᵥ (fun j => v (Sum.inr j))))) i)
    (by fun_prop)
  set zh := fwdM S K f with hzh
  have hzb := fwdM_bdd hKd hfb
  have hza := fwdM_adapted S K f
  set g : ℕ → Ω → X → ℝ := fun t ω => A.toBlocks₂₁ *ᵥ zh t ω + wx t ω with hgdef
  set x := xrecM (lam A G) g x0 with hx
  have hgk : ∀ t, MKnownV S t (g t) := fun t j =>
    sm_comp₂ (hza t) (fun j => hwa t (Sum.inr j))
      (g := fun p => (A.toBlocks₂₁ *ᵥ p.1 + p.2) j) (by fun_prop)
  have hxk : ∀ t, MKnownV S t (x t) := by
    intro t
    induction t with
    | zero => exact hx0k
    | succ t ih =>
      intro j
      have h1 : MKnownV S t (x (t + 1)) := fun j =>
        sm_comp₂ ih (hgk t) (g := fun p => (lam A G *ᵥ p.1 + p.2) j) (by fun_prop)
      exact (h1 j).mono (S.𝓕.mono (Nat.le_succ t))
  have hxk1 : ∀ t, MKnownV S t (x (t + 1)) := fun t j =>
    sm_comp₂ (hxk t) (hgk t) (g := fun p => (lam A G *ᵥ p.1 + p.2) j) (by fun_prop)
  obtain ⟨Mz, hMz⟩ := hzb
  obtain ⟨M0, hM0⟩ := hx0b
  obtain ⟨Kg, hKg⟩ := GeneralFOC.exists_bound_mulVec A.toBlocks₂₁ Mz
  have hxb : MBoundedV S x := by
    refine ⟨Fintype.card X * CbL * (max M0 0 + max (Kg + Mw) 0 / (1 - ρL)), fun t => ?_⟩
    filter_upwards [hM0, ae_all_iff.2 hMz, ae_all_iff.2 hMw] with ω h0 hz hw
    intro j
    refine rec_bounded hCbL hρL0.le hρL1 hLpow (x := fun t => x t ω) (f := fun t => g t ω)
      (fun t => rfl) (le_max_right _ _) (le_max_right _ _) (fun s j => ?_)
      (fun j => (h0 j).trans (le_max_left _ _)) t j
    refine le_trans ?_ (le_max_left _ _)
    exact (abs_add_le _ _).trans (add_le_add (hKg _ (hz s) j) (hw s (Sum.inr j)))
  set y : ℕ → Ω → Z ⊕ X → ℝ := fun t ω => Sum.elim (zh t ω + G *ᵥ x t ω) (x t ω) with hy
  have hzi : ∀ t i, Integrable (fun ω => zh t ω i) S.μ := integrable_of_adapted ⟨Mz, hMz⟩ hza
  have hxi : ∀ t j, Integrable (fun ω => x t ω j) S.μ := integrable_of_adapted hxb hxk
  refine ⟨y, fun t => ?_, fun t k => ?_, fun t j => hxk1 t j, ae_of_all _ fun ω j => rfl, ?_⟩
  · have hz : ∀ᵐ ω ∂S.μ, EVm S t (zh (t + 1)) ω =
        cmat A G *ᵥ zh t ω + (wz t ω - G *ᵥ wx t ω) := by
      filter_upwards [fwdM_rec hKd hfb hfa t] with ω e
      have e2 := congrArg (fun v => cmat A G *ᵥ v) e
      simp only [hf, mulVec_add, mulVec_neg, mulVec_mulVec, hCK, one_mulVec] at e2
      rw [e2]
      abel
    have hE : ∀ᵐ ω ∂S.μ, EVm S t (y (t + 1)) ω =
        Sum.elim (EVm S t (zh (t + 1)) ω + G *ᵥ x (t + 1) ω) (x (t + 1) ω) := by
      have hGx : MKnownV S t (fun ω => G *ᵥ x (t + 1) ω) := fun i =>
        sm_comp (hxk1 t) (g := fun v => (G *ᵥ v) i) (by fun_prop)
      have hGxi : ∀ i, Integrable (fun ω => (G *ᵥ x (t + 1) ω) i) S.μ := fun i =>
        integrable_mulVec G (hxi (t + 1)) i
      filter_upwards [EVm_add S t (hzi (t + 1)) hGxi] with ω e
      funext k
      rcases k with i | j
      · refine (congrFun e i).trans ?_
        rw [EVm_of_known S hGx hGxi]
        rfl
      · change S.E t (fun ω' => x (t + 1) ω' j) ω = x (t + 1) ω j
        exact congrFun (S.E_of_stronglyMeasurable (hxk1 t j) (hxi (t + 1) j)) ω
    filter_upwards [hz, hE] with ω e1 e2
    rw [e2, e1]
    have hw : w t ω = Sum.elim (wz t ω) (wx t ω) := by
      funext k
      rcases k with i | j <;> rfl
    rw [hw]
    refine bk_alg hG _ _ _ _ _ _ rfl ?_
    change xrecM (lam A G) g x0 (t + 1) ω = _
    simp only [xrecM, hgdef]
    abel
  · rcases k with i | j
    · exact sm_comp₂ (hza t) (hxk t) (g := fun p => (p.1 + G *ᵥ p.2) i) (by fun_prop)
    · exact hxk t j
  · obtain ⟨Mx, hMx⟩ := hxb
    obtain ⟨KG, hKG⟩ := GeneralFOC.exists_bound_mulVec G Mx
    refine ⟨max (Mz + KG) Mx, fun t => ?_⟩
    filter_upwards [hMz t, hMx t] with ω h1 h2 k
    rcases k with i | j
    · exact ((abs_add_le _ _).trans (add_le_add (h1 i) (hKG _ h2 i))).trans (le_max_left _ _)
    · exact (h2 j).trans (le_max_right _ _)

/-- Woodford (2003), p. 540 (tool): `E_t (x − x') = E_t x − E_t x'` for integrable random
vectors (a.s.). -/
theorem EVm_sub' (S : MeasExpectationSystem Ω) {κ : Type*} [Countable κ] (t : ℕ)
    {x x' : Ω → κ → ℝ} (hx : ∀ i, Integrable (fun ω => x ω i) S.μ)
    (hx' : ∀ i, Integrable (fun ω => x' ω i) S.μ) :
    ∀ᵐ ω ∂S.μ, EVm S t (fun ω => x ω - x' ω) ω = EVm S t x ω - EVm S t x' ω := by
  have hc : ∀ i, ∀ᵐ ω ∂S.μ, EVm S t (fun ω => x ω - x' ω) ω i =
      EVm S t x ω i - EVm S t x' ω i := fun i => S.E_sub (hx i) (hx' i) t
  filter_upwards [ae_all_iff.2 hc] with ω h
  funext i
  exact h i

/-- Woodford (2003), App. C.1, p. 672 (tool): along `y' = Ay`, `ẑ = z − Gx` is mapped by `C`:
`(Ay)_z − G(Ay)_x = C(y_z − Gy_x)` (graph invariance). -/
theorem bk_alg2 {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {G : Matrix Z X ℝ} (hG : IsGraph A G)
    (v : Z ⊕ X → ℝ) :
    (fun i => (A *ᵥ v) (Sum.inl i)) - G *ᵥ (fun j => (A *ᵥ v) (Sum.inr j)) =
      cmat A G *ᵥ ((fun i => v (Sum.inl i)) - G *ᵥ (fun j => v (Sum.inr j))) := by
  have hinv := graph_invariant hG
  have hz : (fun i => (A *ᵥ v) (Sum.inl i)) = A.toBlocks₁₁ *ᵥ (fun i => v (Sum.inl i)) +
      A.toBlocks₁₂ *ᵥ (fun j => v (Sum.inr j)) := by
    funext i
    simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂]
  have hx : (fun j => (A *ᵥ v) (Sum.inr j)) = A.toBlocks₂₁ *ᵥ (fun i => v (Sum.inl i)) +
      A.toBlocks₂₂ *ᵥ (fun j => v (Sum.inr j)) := by
    funext j
    simp [mulVec, dotProduct, Fintype.sum_sum_type, toBlocks₂₁, toBlocks₂₂]
  have h12 : A.toBlocks₁₂ = G * A.toBlocks₂₁ * G + G * A.toBlocks₂₂ - A.toBlocks₁₁ * G := by
    rw [lam, Matrix.mul_add, ← Matrix.mul_assoc] at hinv
    rw [← hinv]
    abel
  rw [hz, hx, cmat, h12]
  simp only [add_mulVec, sub_mulVec, mulVec_add, mulVec_sub, ← mulVec_mulVec]
  abel

/-- **Woodford (2003), App. C.1, p. 670 (Blanchard–Kahn, uniqueness), with conditional
expectations.** Under the conditions of `m_bk_exists`, two equilibria with the same forcing and
initial condition agree a.s. at every date: `ẑ = z − Gx` of their difference obeys
`ẑ_t = C⁻¹E_tẑ_{t+1}` and is bounded, hence `0` (`OptimalRulesMeasureQuasiSplit.m_fwd_zero`),
and then the predetermined block vanishes by induction. -/
theorem m_bk_unique {S : MeasExpectationSystem Ω} {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hnu : NoUnit A) (hd : Module.finrank ℝ (boundedOrbits A) = Fintype.card X)
    (hg : GenericX A) {w : ℕ → Ω → Z ⊕ X → ℝ} {x0 : Ω → X → ℝ} {y1 y2 : ℕ → Ω → Z ⊕ X → ℝ}
    (h1 : MEquil S A w x0 y1) (h2 : MEquil S A w x0 y2) :
    ∀ t, ∀ᵐ ω ∂S.μ, y1 t ω = y2 t ω := by
  classical
  obtain ⟨G, hG⟩ := exists_graph hd hg
  have hΛ := lam_stable hG hnu
  have hC := cmat_unstable hG hg hΛ
  have hdet : IsUnit (cmat A G).det :=
    isUnit_iff_ne_zero.mpr (GeneralBKCopy.det_ne_zero_of_unstable hC)
  set K := (cmat A G)⁻¹ with hKdef
  have hKC : K * cmat A G = 1 := Matrix.nonsing_inv_mul _ hdet
  obtain ⟨CbK, ρK, -, hρK0, hρK1, hKpow⟩ := pow_entry_bound K (GeneralBKCopy.inv_stable hC)
  have hKd : PencilSplit.PowDecay K := ⟨CbK, ρK, hρK0.le, hρK1, hKpow⟩
  obtain ⟨hS1, ha1, hk1, h01, hb1⟩ := h1
  obtain ⟨hS2, ha2, hk2, h02, hb2⟩ := h2
  have hi1 := integrable_of_adapted hb1 ha1
  have hi2 := integrable_of_adapted hb2 ha2
  set d : ℕ → Ω → Z ⊕ X → ℝ := fun t ω => y1 t ω - y2 t ω with hd'
  have hdi : ∀ t i, Integrable (fun ω => d t ω i) S.μ := fun t i => (hi1 t i).sub (hi2 t i)
  have hdE : ∀ t, ∀ᵐ ω ∂S.μ, EVm S t (d (t + 1)) ω = A *ᵥ d t ω := by
    intro t
    filter_upwards [EVm_sub' S t (hi1 (t + 1)) (hi2 (t + 1)), hS1 t, hS2 t] with ω e e1 e2
    rw [e, e1, e2, hd', mulVec_sub]
    abel
  set xd : ℕ → Ω → X → ℝ := fun t ω j => d t ω (Sum.inr j) with hxd
  set zh : ℕ → Ω → Z → ℝ :=
    fun t ω => (fun i => d t ω (Sum.inl i)) - G *ᵥ xd t ω with hzh
  have hxdk : ∀ t, MKnownV S t (xd (t + 1)) := fun t j =>
    (hk1 t j).sub (hk2 t j)
  have hxdE : ∀ t, ∀ᵐ ω ∂S.μ, xd (t + 1) ω = fun j => (A *ᵥ d t ω) (Sum.inr j) := by
    intro t
    filter_upwards [hdE t] with ω e
    funext j
    rw [← congrFun e (Sum.inr j)]
    exact (congrFun (S.E_of_stronglyMeasurable (hxdk t j) (hdi (t + 1) (Sum.inr j))) ω).symm
  have hzb : MBoundedV S zh := by
    obtain ⟨M1, hM1⟩ := hb1
    obtain ⟨M2, hM2⟩ := hb2
    obtain ⟨KG, hKG⟩ := GeneralFOC.exists_bound_mulVec G (M1 + M2)
    refine ⟨M1 + M2 + KG, fun t => ?_⟩
    filter_upwards [hM1 t, hM2 t] with ω e1 e2 i
    have hdb : ∀ k, |d t ω k| ≤ M1 + M2 := fun k =>
      (abs_sub _ _).trans (add_le_add (e1 k) (e2 k))
    exact (abs_sub _ _).trans (add_le_add (hdb _) (hKG _ (fun j => hdb _) i))
  have hzE : ∀ t, 0 ≤ t → ∀ᵐ ω ∂S.μ, zh t ω = K *ᵥ EVm S t (zh (t + 1)) ω := by
    intro t _
    have hzi : ∀ i, Integrable (fun ω => d (t + 1) ω (Sum.inl i)) S.μ := fun i => hdi _ _
    have hGi : ∀ i, Integrable (fun ω => (G *ᵥ xd (t + 1) ω) i) S.μ := fun i =>
      integrable_mulVec G (fun j => hdi (t + 1) (Sum.inr j)) i
    have hGk : MKnownV S t (fun ω => G *ᵥ xd (t + 1) ω) := fun i =>
      sm_comp (hxdk t) (g := fun v => (G *ᵥ v) i) (by fun_prop)
    filter_upwards [EVm_sub' S t hzi hGi, hdE t, hxdE t] with ω e e1 e2
    have e3 : EVm S t (fun ω => fun i => d (t + 1) ω (Sum.inl i)) ω =
        fun i => (A *ᵥ d t ω) (Sum.inl i) := by
      funext i
      exact congrFun e1 (Sum.inl i)
    change zh t ω = K *ᵥ EVm S t (fun ω => (fun i => d (t + 1) ω (Sum.inl i)) -
      G *ᵥ xd (t + 1) ω) ω
    rw [e, e3, EVm_of_known S hGk hGi]
    dsimp only
    rw [e2, bk_alg2 hG, mulVec_mulVec, hKC, one_mulVec]
  have hz0 := OptimalRulesMeasureQuasiSplit.m_fwd_zero hKd hzb hzE
  have hx0 : ∀ t, ∀ᵐ ω ∂S.μ, xd t ω = 0 := by
    intro t
    induction t with
    | zero =>
      filter_upwards [h01, h02] with ω e1 e2
      funext j
      simp only [hxd, hd', Pi.sub_apply, e1 j, e2 j, sub_self, Pi.zero_apply]
    | succ t ih =>
      filter_upwards [ih, hz0 t (Nat.zero_le t), hxdE t] with ω e1 e2 e3
      rw [e3]
      have hdt : d t ω = Sum.elim (zh t ω + G *ᵥ xd t ω) (xd t ω) := by
        funext k
        rcases k with i | j
        · simp only [hzh, Sum.elim_inl, sub_add_cancel]
        · rfl
      rw [hdt, e1, e2]
      funext j
      simp
  intro t
  filter_upwards [hx0 t, hz0 t (Nat.zero_le t)] with ω e1 e2
  have hdt : d t ω = 0 := by
    funext k
    rcases k with i | j
    · have := congrFun e2 i
      simp only [hzh, Pi.sub_apply, Pi.zero_apply, e1, mulVec_zero, sub_zero] at this
      exact this
    · exact congrFun e1 j
  funext k
  have := congrFun hdt k
  simp only [hd', Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

end Woodford.OptimalPolicyRules.TidyR5aMeasBK
