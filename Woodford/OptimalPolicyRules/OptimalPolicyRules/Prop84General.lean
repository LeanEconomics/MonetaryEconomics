/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.Prop83

/-!
# Proposition 8.4 in general

Woodford (2003), *Interest and Prices*, Chapter 8, §1.5, pp. 557–559: the lemma (1.30)–(1.31),
the factorisation `α(L) = α₁(L) α₂(L)` and Proposition 8.4 ((1.28) ⟺ (1.32)).

`TargetCriterion.prop84_conditional` proved the equivalence (1.28) ⟺ (1.32) *given* the
factorisation and *given* the bounded forward inverse `g = α̃₁(L⁻¹)⁻¹ w`. Both are proved here.

## Main results

* **The forward inverse.** `forward_inverse_existsUnique`: for a nonzero real polynomial `φ`
  all of whose complex roots satisfy `|μ| > 1`, and every bounded adapted `w`, there is exactly
  one bounded adapted `g` with `E_t φ(L⁻¹) g_t = w_t` for all `t` (existence by factoring `φ`
  over `ℂ` and solving one first-order forward equation per root, `exists_aeval_fwdC_eq`; the
  real solution is the real part). `forward_inverse_iff`: this is **exactly** the right root
  condition — if some root has `|μ| ≤ 1`, uniqueness fails (`not_unique_of_root_in_disc`).
* **The factorisation.** `exists_inside_factorization`: every nonzero real polynomial is
  `p = p₁ p₂` with `p₁` real and monic, the complex roots of `p₁` exactly the roots of `p` inside
  the unit circle (with multiplicity, `deg p₁ = zerosInside p`), and every root of `p₂` of
  modulus `≥ 1` (`> 1` when `p` has no zero on the circle). The real coefficients come from the
  conjugation-invariance of the roots of a real polynomial (`insideRoots_conj`).
* **Proposition 8.4.** `prop84`: under the hypotheses of `Prop83.prop83` (Assumptions 8.1, 8.3,
  8.7, no root of (1.15) on `|λ| = β⁻¹`) the `α(L) = det(I − ΛL)` of every representation of
  Proposition 8.1 factors as `α₁ α₂` with `deg α₁ = m`, all zeros of `α₁` inside and all zeros
  of `α₂` outside the unit circle; for every bounded adapted `w` the bounded forward inverse `g`
  exists and is unique, and for every bounded adapted instrument path (1.28) ⟺ (1.32).
  `prop84_from`: the same equivalence for rules imposed from any date `T` on; `prop84_criterion`:
  the version stated with the target criterion (1.23) itself (`TargetCriterion.Crit.crit`) and
  `v_t = λ_i (i_t − i*)` (Assumption 8.6), for all `t ≥ T ≥ D`.
-/

namespace Woodford.OptimalPolicyRules.Prop84General

open Matrix Polynomial GeneralSetup GeneralFOC GeneralFOC.LQ Adjugate
open TargetCriterion (zerosInside fwdOp lagOp eq_zero_of_aeval_fwdOp_eq_zero prop84_conditional
  roots_reverse_outside map_reverse_ofReal aeval_fwdOp_apply p558_identity
  boundedProc_aeval_lagOp aeval_lagOp_adapted lagOp_adapted)
open TargetCriterion.Prop81
open ExpectationTools (EC EC_smul EC_add norm_EC_le BoundedC AdaptedC EC_ofReal)
open Prop83 (zerosOnCircle)
open PencilEigen (Assumption83)

variable {Ω : Type*}

/-! ### The bounded forward inverse of a polynomial in `L⁻¹` -/

/-- Woodford (2003), p. 558: a first-order forward equation `E_t v_{t+1} − z v_t = w_t` with
`|z| > 1` has a bounded adapted solution, the forward series
`v_t = −∑_k z^{−k−1} E_t w_{t+k}`. -/
theorem exists_fwdC_sub_eq (𝔼 : ExpectationSystem Ω) {z : ℂ} (hz : 1 < ‖z‖)
    {w : ℕ → Ω → ℂ} (hwb : BoundedC w) (hwa : AdaptedC 𝔼 w) :
    ∃ v, BoundedC v ∧ AdaptedC 𝔼 v ∧ TargetCriterion.fwdC 𝔼 v - z • v = w := by
  obtain ⟨M, hM⟩ := hwb
  have hz0 : z ≠ 0 := fun h => by rw [h, norm_zero] at hz; linarith
  have ha : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hz
  set u : ℕ → Ω → ℂ := fun t => (-z⁻¹) • w t with hu
  have huM : ∀ t ω, ‖u t ω‖ ≤ ‖z⁻¹‖ * M := fun t ω => by
    simp only [hu, Pi.smul_apply, smul_eq_mul, norm_mul, norm_neg]
    exact mul_le_mul_of_nonneg_left (hM t ω) (norm_nonneg _)
  have hua : AdaptedC 𝔼 u := fun t => by
    simp only [hu]
    rw [EC_smul, hwa t]
  refine ⟨ExpectationTools.fwdC 𝔼 z⁻¹ u, ⟨_, ExpectationTools.fwdC_bounded 𝔼 ha huM⟩,
    ExpectationTools.fwdC_adapted 𝔼 ha huM, ?_⟩
  funext t
  have hs := ExpectationTools.fwdC_solves 𝔼 ha huM hua t
  change EC 𝔼 t (ExpectationTools.fwdC 𝔼 z⁻¹ u (t + 1)) - z • ExpectationTools.fwdC 𝔼 z⁻¹ u t =
    w t
  have hzu : z • u t = -w t := by
    simp only [hu]
    rw [smul_smul, mul_neg, mul_inv_cancel₀ hz0, neg_one_smul]
  rw [hs, smul_add, smul_smul, mul_inv_cancel₀ hz0, one_smul, hzu]
  abel

/-- Woodford (2003), p. 558: **existence of the forward inverse over `ℂ`.** If every root of the
nonzero complex polynomial `p` satisfies `|μ| > 1`, then `p(F) u = w` (`F u_t = E_t u_{t+1}`)
has a bounded adapted solution for every bounded adapted `w`. -/
theorem exists_aeval_fwdC_eq (𝔼 : ExpectationSystem Ω) :
    ∀ (n : ℕ) (p : ℂ[X]), p.natDegree = n → p ≠ 0 → (∀ z ∈ p.roots, 1 < ‖z‖) →
      ∀ w, BoundedC w → AdaptedC 𝔼 w →
        ∃ u, BoundedC u ∧ AdaptedC 𝔼 u ∧ (aeval (TargetCriterion.fwdC 𝔼) p) u = w := by
  intro n
  induction n with
  | zero =>
    intro p hn hp _ w hwb hwa
    have hc : p.coeff 0 ≠ 0 := fun h0 =>
      hp (by rw [eq_C_of_natDegree_eq_zero hn, h0, map_zero])
    refine ⟨(p.coeff 0)⁻¹ • w, ?_, fun t => ?_, ?_⟩
    · obtain ⟨M, hM⟩ := hwb
      refine ⟨‖(p.coeff 0)⁻¹‖ * M, fun t ω => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (norm_nonneg _)
    · change EC 𝔼 t ((p.coeff 0)⁻¹ • w t) = (p.coeff 0)⁻¹ • w t
      rw [EC_smul, hwa t]
    · nth_rewrite 1 [eq_C_of_natDegree_eq_zero hn]
      rw [aeval_C, Module.algebraMap_end_apply, smul_smul, mul_inv_cancel₀ hc, one_smul]
  | succ n ih =>
    intro p hn hp hroots w hwb hwa
    obtain ⟨z, hz⟩ := Complex.exists_root (f := p) (by
      rw [degree_eq_natDegree hp, hn]
      exact_mod_cast Nat.succ_pos n)
    set q := p /ₘ (X - C z) with hq
    have hfac : (X - C z) * q = p := mul_divByMonic_eq_iff_isRoot.mpr hz
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfac
      exact hp hfac.symm
    have hqdeg : q.natDegree = n := by
      have := congrArg natDegree hfac
      rw [natDegree_mul (X_sub_C_ne_zero z) hq0, natDegree_X_sub_C, hn] at this
      omega
    have hqroots : ∀ y ∈ q.roots, 1 < ‖y‖ := by
      intro y hy
      apply hroots
      rw [← hfac, roots_mul (by rw [hfac]; exact hp), roots_X_sub_C]
      exact Multiset.mem_add.mpr (Or.inr hy)
    have hzroot : 1 < ‖z‖ := hroots z ((mem_roots hp).mpr hz)
    obtain ⟨v, hvb, hva, hv⟩ := exists_fwdC_sub_eq 𝔼 hzroot hwb hwa
    obtain ⟨u, hub, hua, hu⟩ := ih q hqdeg hq0 hqroots v hvb hva
    refine ⟨u, hub, hua, ?_⟩
    rw [← hfac, map_mul, Module.End.mul_apply, hu, map_sub, aeval_X, aeval_C,
      LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact hv

/-- Woodford (2003), p. 557 (tool): the real part commutes with the forward operator. -/
theorem fwdOp_re (𝔼 : ExpectationSystem Ω) (u : ℕ → Ω → ℂ) :
    fwdOp 𝔼 (fun t ω => (u t ω).re) = fun t ω => ((TargetCriterion.fwdC 𝔼 u) t ω).re := rfl

/-- Woodford (2003), p. 557 (tool): the real part commutes with real forward lag polynomials. -/
theorem aeval_fwdOp_re (𝔼 : ExpectationSystem Ω) (φ : ℝ[X]) (u : ℕ → Ω → ℂ) :
    (aeval (fwdOp 𝔼) φ) (fun t ω => (u t ω).re) =
      fun t ω => ((aeval (TargetCriterion.fwdC 𝔼) (φ.map Complex.ofRealHom)) u t ω).re := by
  have hpow : ∀ j (u : ℕ → Ω → ℂ), ((fwdOp 𝔼) ^ j) (fun t ω => (u t ω).re) =
      fun t ω => ((((TargetCriterion.fwdC 𝔼) ^ j) u) t ω).re := by
    intro j
    induction j with
    | zero => intro u; rfl
    | succ j ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, fwdOp_re, ih, pow_succ, Module.End.mul_apply]
  rw [aeval_eq_sum_range, aeval_eq_sum_range,
    natDegree_map_eq_of_injective Complex.ofRealHom.injective]
  funext t ω
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, hpow,
    Pi.smul_apply, coeff_map, smul_eq_mul, Complex.ofRealHom_eq_coe, Complex.re_sum,
    Complex.re_ofReal_mul]

/-- **Woodford (2003), p. 558: the bounded forward inverse `φ(L⁻¹)⁻¹`, existence and
uniqueness.** If `φ ≠ 0` is a real polynomial all of whose complex roots satisfy `|μ| > 1`, then
for every bounded adapted `w` there is exactly one bounded adapted `g` with
`E_t φ(L⁻¹) g_t = w_t` for all `t`. -/
theorem forward_inverse_existsUnique {𝔼 : ExpectationSystem Ω} {φ : ℝ[X]} (hφ : φ ≠ 0)
    (hroots : ∀ z ∈ (φ.map Complex.ofRealHom).roots, 1 < ‖z‖) {w : ℕ → Ω → ℝ}
    (hwb : BoundedProc w) (hwa : 𝔼.Adapted w) :
    ∃! g, BoundedProc g ∧ 𝔼.Adapted g ∧ (aeval (fwdOp 𝔼) φ) g = w := by
  have hφc : φ.map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hφ
  obtain ⟨M, hM⟩ := hwb
  have hwcb : BoundedC (fun t ω => (w t ω : ℂ)) :=
    ⟨M, fun t ω => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hM t ω⟩
  have hwca : AdaptedC 𝔼 (fun t ω => (w t ω : ℂ)) := fun t => by
    change EC 𝔼 t (fun ω => (w t ω : ℂ)) = fun ω => (w t ω : ℂ)
    rw [EC_ofReal, hwa t]
  obtain ⟨u, hub, hua, hu⟩ := exists_aeval_fwdC_eq 𝔼 _ _ rfl hφc hroots _ hwcb hwca
  have hreb : BoundedProc (fun t ω => (u t ω).re) := by
    obtain ⟨K, hK⟩ := hub
    exact ⟨K, fun t ω => (Complex.abs_re_le_norm _).trans (hK t ω)⟩
  have hsol : (aeval (fwdOp 𝔼) φ) (fun t ω => (u t ω).re) = w := by
    rw [aeval_fwdOp_re, hu]
    rfl
  refine ⟨fun t ω => (u t ω).re, ⟨hreb, fun t => ?_, hsol⟩, ?_⟩
  · funext ω
    exact congrArg Complex.re (congrFun (hua t) ω)
  · rintro g ⟨hgb, -, hg⟩
    have hdiff : (aeval (fwdOp 𝔼) φ) (g - fun t ω => (u t ω).re) = 0 := by
      rw [map_sub, hg, hsol, sub_self]
    have hb : BoundedProc (g - fun t ω => (u t ω).re) := by
      obtain ⟨M1, h1⟩ := hgb
      obtain ⟨M2, h2⟩ := hreb
      exact ⟨M1 + M2, fun t ω => (abs_sub _ _).trans (add_le_add (h1 t ω) (h2 t ω))⟩
    exact sub_eq_zero.mp (eq_zero_of_aeval_fwdOp_eq_zero hφ hroots hb hdiff)

/-- Woodford (2003), p. 558: **the root condition cannot be weakened.** If the real polynomial
`φ` has a complex root `r` with `|r| ≤ 1`, the deterministic bounded process `g_t = Re(rᵗ)`
(`g_0 = 1`) solves `E_t φ(L⁻¹) g_t = 0`, so bounded solutions of `E_t φ(L⁻¹) g_t = w_t` are never
unique. -/
theorem not_unique_of_root_in_disc [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {φ : ℝ[X]} {r : ℂ}
    (hr : r ∈ (φ.map Complex.ofRealHom).roots) (hr1 : ‖r‖ ≤ 1) :
    ∃ g : ℕ → Ω → ℝ, g ≠ 0 ∧ BoundedProc g ∧ 𝔼.Adapted g ∧ (aeval (fwdOp 𝔼) φ) g = 0 := by
  obtain ⟨ω0⟩ := ‹Nonempty Ω›
  have hφc : φ.map Complex.ofRealHom ≠ 0 := ne_zero_of_mem_roots hr
  have heval : (φ.map Complex.ofRealHom).eval r = 0 := (mem_roots hφc).mp hr
  set g : ℕ → Ω → ℝ := fun t _ => (r ^ t).re with hg
  have hga : 𝔼.Adapted g := fun t => 𝔼.const t _
  refine ⟨g, fun h => ?_, ⟨1, fun t ω => ?_⟩, hga, ?_⟩
  · have := congrFun (congrFun h 0) ω0
    simp [hg] at this
  · simp only [hg]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg r) hr1
  · funext t ω
    rw [aeval_fwdOp_apply 𝔼 hga]
    simp only [hg, 𝔼.const, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [eval_eq_sum_range, natDegree_map_eq_of_injective Complex.ofRealHom.injective] at heval
    have h1 : ∑ j ∈ Finset.range (φ.natDegree + 1), φ.coeff j * (r ^ (t + j)).re =
        (r ^ t * ∑ j ∈ Finset.range (φ.natDegree + 1),
          (φ.map Complex.ofRealHom).coeff j * r ^ j).re := by
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coeff_map, Complex.ofRealHom_eq_coe, pow_add]
      rw [show r ^ t * (↑(φ.coeff j) * r ^ j) = ↑(φ.coeff j) * (r ^ t * r ^ j) by ring,
        Complex.re_ofReal_mul]
    rw [h1, heval, mul_zero, Complex.zero_re]

/-- **Woodford (2003), p. 558: the correct root condition.** For a nonzero real polynomial `φ`
(and a nonempty sample space), `E_t φ(L⁻¹) g_t = w_t` has a unique bounded adapted solution for
every bounded adapted `w` iff every complex root of `φ` satisfies `|μ| > 1`. -/
theorem forward_inverse_iff [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {φ : ℝ[X]} (hφ : φ ≠ 0) :
    (∀ w, BoundedProc w → 𝔼.Adapted w →
      ∃! g, BoundedProc g ∧ 𝔼.Adapted g ∧ (aeval (fwdOp 𝔼) φ) g = w) ↔
    ∀ z ∈ (φ.map Complex.ofRealHom).roots, 1 < ‖z‖ := by
  constructor
  · intro H z hz
    by_contra hz1
    obtain ⟨g, hg0, hgb, hga, hg⟩ := not_unique_of_root_in_disc 𝔼 hz (not_lt.mp hz1)
    have h0b : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun t ω => by simp⟩
    have h0a : 𝔼.Adapted (0 : ℕ → Ω → ℝ) := fun t => map_zero _
    obtain ⟨g', -, hu⟩ := H 0 h0b h0a
    have e1 := hu g ⟨hgb, hga, hg⟩
    have e2 := hu 0 ⟨h0b, h0a, map_zero _⟩
    exact hg0 (e1.trans e2.symm)
  · intro hroots w hwb hwa
    exact forward_inverse_existsUnique hφ hroots hwb hwa

/-! ### The factorisation `α = α₁ α₂` -/

/-- Woodford (2003), p. 558: the zeros of a real lag polynomial inside the unit circle, with
multiplicity. -/
noncomputable def insideRoots (p : ℝ[X]) : Multiset ℂ :=
  (p.map Complex.ofRealHom).roots.filter (fun z => ‖z‖ < 1)

/-- Woodford (2003), p. 552 and p. 558: the complex roots of a real polynomial come in conjugate
pairs (with multiplicity); in particular the zeros inside the unit circle do. -/
theorem insideRoots_conj (p : ℝ[X]) :
    (insideRoots p).map (starRingEnd ℂ) = insideRoots p := by
  unfold insideRoots
  set P := p.map Complex.ofRealHom with hP
  have hcard : Multiset.card P.roots = P.natDegree :=
    (splits_iff_card_roots).mp (IsAlgClosed.splits P)
  have hconj : P.map (starRingEnd ℂ) = P := by
    rw [hP, Polynomial.map_map]
    congr 1
    ext x
    simp
  have hroots : P.roots.map (starRingEnd ℂ) = P.roots := by
    rw [roots_map_of_injective_of_card_eq_natDegree (starRingEnd ℂ).injective hcard, hconj]
  calc (P.roots.filter (fun z => ‖z‖ < 1)).map (starRingEnd ℂ) =
        (P.roots.filter ((fun z => ‖z‖ < 1) ∘ starRingEnd ℂ)).map (starRingEnd ℂ) := by
        congr 1
        exact Multiset.filter_congr fun z _ => by simp
    _ = (P.roots.map (starRingEnd ℂ)).filter (fun z => ‖z‖ < 1) :=
        (Multiset.filter_map _ _ _).symm
    _ = P.roots.filter (fun z => ‖z‖ < 1) := by rw [hroots]

/-- **Woodford (2003), p. 558: the factorisation `α(L) = α₁(L) α₂(L)`.** Every nonzero real
polynomial `p` factors as `p = p₁ p₂` with `p₁` real and monic, the complex roots of `p₁` exactly
the roots of `p` inside the unit circle (with multiplicity), `deg p₁ = zerosInside p`, and every
complex root of `p₂` of modulus at least `1`. -/
theorem exists_inside_factorization (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ p1 p2 : ℝ[X], p = p1 * p2 ∧ p1.Monic ∧ (p1.map Complex.ofRealHom).roots = insideRoots p ∧
      p1.natDegree = zerosInside p ∧ ∀ z ∈ (p2.map Complex.ofRealHom).roots, 1 ≤ ‖z‖ := by
  set P := p.map Complex.ofRealHom with hP
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp
  set QC : ℂ[X] := ((insideRoots p).map fun a => X - C a).prod with hQC
  have hQmonic : QC.Monic := monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
  have hQconj : QC.map (starRingEnd ℂ) = QC := by
    rw [hQC, Polynomial.map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [← insideRoots_conj p, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp
  have hlift : QC ∈ lifts Complex.ofRealHom := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have h1 := congrArg (fun q => q.coeff n) hQconj
    simp only [coeff_map] at h1
    exact ⟨(QC.coeff n).re, Complex.conj_eq_iff_re.mp h1⟩
  obtain ⟨p1, hp1map, hp1deg, hp1monic⟩ := lifts_and_natDegree_eq_and_monic hlift hQmonic
  have hcard : Multiset.card P.roots = P.natDegree :=
    (splits_iff_card_roots).mp (IsAlgClosed.splits P)
  have hdvdC : QC ∣ P := by
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C hcard]
    refine Dvd.dvd.mul_left (Multiset.prod_dvd_prod_of_le
      (Multiset.map_le_map (Multiset.filter_le _ _))) _
  have hdvd : p1 ∣ p :=
    (map_dvd_map Complex.ofRealHom Complex.ofRealHom.injective hp1monic).mp
      (by rw [hp1map]; exact hdvdC)
  obtain ⟨p2, hp2⟩ := hdvd
  have hroots1 : (p1.map Complex.ofRealHom).roots = insideRoots p := by
    rw [hp1map, hQC, roots_multiset_prod_X_sub_C]
  refine ⟨p1, p2, hp2, hp1monic, hroots1, ?_, ?_⟩
  · rw [hp1deg, hQC, natDegree_multiset_prod_X_sub_C_eq_card]
    rfl
  · intro z hz
    by_contra hlt
    push Not at hlt
    have hPfac : P = p1.map Complex.ofRealHom * p2.map Complex.ofRealHom := by
      rw [hP, hp2, Polynomial.map_mul]
    have hsum : P.roots = insideRoots p + (p2.map Complex.ofRealHom).roots := by
      rw [hPfac, roots_mul (by rw [← hPfac]; exact hP0), hroots1]
    have hc := congrArg (Multiset.count z) hsum
    rw [Multiset.count_add] at hc
    have hin : Multiset.count z (insideRoots p) = Multiset.count z P.roots := by
      unfold insideRoots
      rw [← hP]
      exact Multiset.count_filter_of_pos hlt
    have hpos := Multiset.count_pos.mpr hz
    omega

/-- Woodford (2003), p. 558: when `p` has no zero on the unit circle, the cofactor `p₂` of the
factorisation has all its zeros strictly outside the unit circle. -/
theorem roots_cofactor_outside {p p1 p2 : ℝ[X]} (hp : p ≠ 0) (hfac : p = p1 * p2)
    (h1 : ∀ z ∈ (p2.map Complex.ofRealHom).roots, 1 ≤ ‖z‖) (hcirc : zerosOnCircle p = 0) :
    ∀ z ∈ (p2.map Complex.ofRealHom).roots, 1 < ‖z‖ := by
  intro z hz
  refine lt_of_le_of_ne (h1 z hz) fun h => ?_
  have hP0 : p.map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hp
  have hzp : z ∈ (p.map Complex.ofRealHom).roots := by
    rw [hfac, Polynomial.map_mul, roots_mul (by rw [← Polynomial.map_mul, ← hfac]; exact hP0)]
    exact Multiset.mem_add.mpr (Or.inr hz)
  unfold zerosOnCircle at hcirc
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil] at hcirc
  exact hcirc z hzp h.symm

/-! ### Proposition 8.4 -/

/-- Woodford (2003), p. 558 (tool): the expectation system seen from date `T` on,
`E'_s = E_{s+T}`. -/
def shiftES (𝔼 : ExpectationSystem Ω) (T : ℕ) : ExpectationSystem Ω where
  E s := 𝔼.E (s + T)
  const s c := 𝔼.const (s + T) c
  mono s _ _ h := 𝔼.mono (s + T) h
  tower h x := 𝔼.tower (Nat.add_le_add_right h T) x
  known h x := 𝔼.known (Nat.add_le_add_right h T) x

/-- Woodford (2003), p. 558 (tool): forward lag polynomials commute with the shift of dates. -/
theorem aeval_fwdOp_shift (𝔼 : ExpectationSystem Ω) (T : ℕ) (φ : ℝ[X]) {x : ℕ → Ω → ℝ}
    (hx : 𝔼.Adapted x) (s : ℕ) :
    (aeval (fwdOp (shiftES 𝔼 T)) φ) (fun s => x (s + T)) s = (aeval (fwdOp 𝔼) φ) x (s + T) := by
  have hx' : (shiftES 𝔼 T).Adapted (fun s => x (s + T)) := fun s => hx (s + T)
  rw [aeval_fwdOp_apply _ hx', aeval_fwdOp_apply _ hx]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show s + j + T = s + T + j by omega]
  rfl

/-- **Woodford (2003), pp. 557–558: the lemma (1.30) ⟺ (1.31) from a date `T` on.** If `φ ≠ 0`
has all its complex roots outside the unit circle and `u` is bounded and adapted, then
`E_t φ(L⁻¹) u_t = 0` for all `t ≥ T` iff `u_t = 0` for all `t ≥ T`. -/
theorem forward_eq_zero_from_iff {𝔼 : ExpectationSystem Ω} {φ : ℝ[X]} (hφ : φ ≠ 0)
    (hroots : ∀ z ∈ (φ.map Complex.ofRealHom).roots, 1 < ‖z‖) {u : ℕ → Ω → ℝ}
    (hub : BoundedProc u) (hua : 𝔼.Adapted u) (T : ℕ) :
    (∀ t, T ≤ t → (aeval (fwdOp 𝔼) φ) u t = 0) ↔ (∀ t, T ≤ t → u t = 0) := by
  constructor
  · intro he
    set u' : ℕ → Ω → ℝ := fun s => u (s + T) with hu'
    have hu'b : BoundedProc u' := by
      obtain ⟨M, hM⟩ := hub
      exact ⟨M, fun s ω => hM (s + T) ω⟩
    have hz : (aeval (fwdOp (shiftES 𝔼 T)) φ) u' = 0 := by
      funext s
      rw [hu', aeval_fwdOp_shift 𝔼 T _ hua]
      exact he (s + T) (by omega)
    have h0 := eq_zero_of_aeval_fwdOp_eq_zero hφ hroots hu'b hz
    intro t ht
    have := congrFun h0 (t - T)
    simp only [hu', Pi.zero_apply] at this
    rwa [show t - T + T = t by omega] at this
  · intro hu0 t ht
    rw [aeval_fwdOp_apply 𝔼 hua]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hu0 (t + j) (by omega), map_zero, smul_zero]

/-- Woodford (2003), p. 558: `x_t − i*` is bounded and adapted when `i` is. -/
theorem gap_bounded_adapted {𝔼 : ExpectationSystem Ω} {i : ℕ → Ω → ℝ} (istar : ℝ)
    (hib : BoundedProc i) (hia : 𝔼.Adapted i) :
    BoundedProc (fun t ω => i t ω - istar) ∧ 𝔼.Adapted (fun t ω => i t ω - istar) := by
  refine ⟨?_, fun t => ?_⟩
  · obtain ⟨M, hM⟩ := hib
    exact ⟨M + |istar|, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)⟩
  · have e : (fun ω => i t ω - istar) = i t - fun _ => istar := rfl
    change 𝔼.E t (fun ω => i t ω - istar) = fun ω => i t ω - istar
    rw [e, map_sub, hia t, 𝔼.const]

/-- **Woodford (2003), Proposition 8.4, p. 558, for rules imposed from date `T` on.** With
`α = α₁ α₂`, `deg α₁ = m`, `α̃₁(L⁻¹) = α₁(L) L^{-m}` invertible, and `g` a bounded adapted solution
of `E_t α̃₁(L⁻¹) g_t = w_t`: for a bounded adapted instrument path, the instrument rule (1.28)
`λ_i α(L)(i_t − i*) + w_t = 0` holds for all `t ≥ T` iff the targeting rule (1.32)
`g_t + λ_i α₂(L)(i_{t−m} − i*) = 0` holds for all `t ≥ T`. -/
theorem prop84_from {𝔼 : ExpectationSystem Ω} {α1 α2 : ℝ[X]} {m : ℕ} (hm : α1.natDegree = m)
    (hα1 : α1 ≠ 0) (hroots : ∀ z ∈ (α1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖)
    {lam istar : ℝ} {i w g : ℕ → Ω → ℝ} (hib : BoundedProc i) (hia : 𝔼.Adapted i)
    (hgb : BoundedProc g) (hga : 𝔼.Adapted g) (hg : (aeval (fwdOp 𝔼) α1.reverse) g = w)
    (T : ℕ) :
    (∀ t, T ≤ t → (lam • (aeval (lagOp (Ω := Ω)) (α1 * α2)) (fun t ω => i t ω - istar) + w) t =
      0) ↔
    (∀ t, T ≤ t → (g + lam • ((lagOp (Ω := Ω)) ^ m)
      ((aeval (lagOp (Ω := Ω)) α2) (fun t ω => i t ω - istar))) t = 0) := by
  have hrev : α1.reverse ≠ 0 := fun h => hα1 (reverse_eq_zero.mp h)
  obtain ⟨hxb, hxa⟩ := gap_bounded_adapted istar hib hia
  set x : ℕ → Ω → ℝ := fun t ω => i t ω - istar with hx
  set u := g + lam • ((lagOp (Ω := Ω)) ^ m) ((aeval (lagOp (Ω := Ω)) α2) x) with hu
  have hlagA : 𝔼.Adapted (((lagOp (Ω := Ω)) ^ m) ((aeval (lagOp (Ω := Ω)) α2) x)) := by
    have := aeval_lagOp_adapted (X ^ m) (aeval_lagOp_adapted α2 hxa)
    rwa [map_pow, aeval_X] at this
  have hua : 𝔼.Adapted u := fun t => by
    simp only [hu, Pi.add_apply, Pi.smul_apply]
    rw [map_add, map_smul, hga t, hlagA t]
  have hub : BoundedProc u := by
    have := boundedProc_aeval_lagOp (X ^ m) _ (boundedProc_aeval_lagOp α2 _ hxb)
    rw [map_pow, aeval_X] at this
    obtain ⟨M, hM⟩ := this
    obtain ⟨Mg, hMg⟩ := hgb
    refine ⟨Mg + |lam| * M, fun t ω => ?_⟩
    simp only [hu, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add (hMg t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg lam)
  have key : (aeval (fwdOp 𝔼) α1.reverse) u =
      lam • (aeval (lagOp (Ω := Ω)) (α1 * α2)) x + w := by
    rw [hu, map_add, hg, map_smul, p558_identity hm hxa, add_comm]
  rw [← forward_eq_zero_from_iff hrev hroots hub hua T, key]

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- **Woodford (2003), Propositions 8.3–8.4, p. 558: the factorisation of `α(L)`.** Under the
hypotheses of Proposition 8.3, the `α(L) = det(I − ΛL)` of every representation of Proposition
8.1 factors as `α₁(L) α₂(L)` with `α₁` monic of degree `m`, all zeros of `α₁` inside and all
zeros of `α₂` outside the unit circle; `α̃₁(L⁻¹) = α₁(L) L^{-m}` then has all its zeros outside
the unit circle (so it is invertible on bounded processes). -/
theorem alpha_factorization [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81Conclusion P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (h83 : Assumption83 P.sys) {m : ℕ} (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    ∃ α1 α2 : ℝ[X], alpha H.Λ = α1 * α2 ∧ α1.Monic ∧ α1.natDegree = m ∧
      (∀ z ∈ (α1.map Complex.ofRealHom).roots, ‖z‖ < 1) ∧
      (∀ z ∈ (α2.map Complex.ofRealHom).roots, 1 < ‖z‖) ∧
      (∀ z ∈ (α1.reverse.map Complex.ofRealHom).roots, 1 < ‖z‖) := by
  obtain ⟨α1, α2, hfac, hmon, hroots1, hdeg, hroots2⟩ :=
    exists_inside_factorization (alpha H.Λ) (alpha_ne_zero _)
  have hm := Prop83.prop83 H hA h83 h87 hcirc
  have hc := Prop83.prop83_noCircle H hA h83.regular hcirc
  have hin : ∀ z ∈ (α1.map Complex.ofRealHom).roots, ‖z‖ < 1 := by
    intro z hz
    rw [hroots1] at hz
    exact (Multiset.mem_filter.mp hz).2
  refine ⟨α1, α2, hfac, hmon, hdeg.trans hm, hin,
    roots_cofactor_outside (alpha_ne_zero _) hfac hroots2 hc, ?_⟩
  rw [map_reverse_ofReal]
  exact roots_reverse_outside hin

/-- **Woodford (2003), Proposition 8.4, p. 558.** For a linear-quadratic problem satisfying
Assumptions 8.1, 8.3 and 8.7 (`n_Z + m` roots of (1.15) with `|μ| < β⁻¹`), with no root of (1.15)
on `|μ| = β⁻¹`, and for every matrix `Λ` delivered by Proposition 8.1: `α(L) = α₁(L) α₂(L)` with
`deg α₁ = m`, all zeros of `α₁` inside and of `α₂` outside the unit circle; for every bounded
adapted `w_t` (Woodford's `B₂'B(L)E_tQ(L⁻¹)T̂'Ŵ(τ̂_t − τ̂*)`) the bounded process
`g = α̃₁(L⁻¹)⁻¹ w` exists and is unique; and for every bounded adapted instrument path the
implicit instrument rule (1.28), `λ_i α(L)(i_t − i*) + w_t = 0` for all `t`, holds iff the pure
targeting rule (1.32), `g_t + λ_i α₂(L)(i_{t−m} − i*) = 0` for all `t`, holds. -/
theorem prop84 [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81Conclusion P 𝔼 t0) (hA : Assumption81 P 𝔼 t0) (h83 : Assumption83 P.sys)
    {m : ℕ} (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) :
    ∃ α1 α2 : ℝ[X], alpha H.Λ = α1 * α2 ∧ α1.natDegree = m ∧
      (∀ z ∈ (α1.map Complex.ofRealHom).roots, ‖z‖ < 1) ∧
      (∀ z ∈ (α2.map Complex.ofRealHom).roots, 1 < ‖z‖) ∧
      ∀ (lam istar : ℝ) (i w : ℕ → Ω → ℝ), BoundedProc i → 𝔼.Adapted i → BoundedProc w →
        𝔼.Adapted w →
        (∃! g, BoundedProc g ∧ 𝔼.Adapted g ∧ (aeval (fwdOp 𝔼) α1.reverse) g = w) ∧
        ∀ g, BoundedProc g → (aeval (fwdOp 𝔼) α1.reverse) g = w →
          (lam • (aeval (lagOp (Ω := Ω)) (alpha H.Λ)) (fun t ω => i t ω - istar) + w = 0 ↔
            g + lam • ((lagOp (Ω := Ω)) ^ m)
              ((aeval (lagOp (Ω := Ω)) α2) (fun t ω => i t ω - istar)) = 0) := by
  obtain ⟨α1, α2, hfac, hmon, hdeg, hin, hout, hrev⟩ := alpha_factorization H hA h83 h87 hcirc
  have hrev0 : α1.reverse ≠ 0 := fun h => hmon.ne_zero (reverse_eq_zero.mp h)
  refine ⟨α1, α2, hfac, hdeg, hin, hout, fun lam istar i w hib hia hwb hwa => ⟨?_, ?_⟩⟩
  · exact forward_inverse_existsUnique hrev0 hrev hwb hwa
  · intro g hgb hg
    rw [hfac]
    exact prop84_conditional hdeg hmon.ne_zero hrev hib hia hgb hg

/-! ### Proposition 8.4 stated with the target criterion (1.23) -/

/-- Woodford (2003), p. 558 (tool): `(Lʲ x)_t = x_{t−j}` for `j ≤ t`. -/
theorem lagOp_pow_apply {j t : ℕ} (hj : j ≤ t) (x : ℕ → Ω → ℝ) :
    ((lagOp (Ω := Ω)) ^ j) x t = x (t - j) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [pow_succ', Module.End.mul_apply]
    change (((lagOp (Ω := Ω)) ^ j) x) s = x (s + 1 - (j + 1))
    rw [ih (by omega), show s + 1 - (j + 1) = s - j by omega]

/-- Woodford (2003), p. 556 (tool): for `t ≥ D ≥ deg p`, `(p(L) x)_t = ∑_{j ≤ D} p_j x_{t−j}`
(no pre-sample value is involved). -/
theorem aeval_lagOp_apply_of_le (p : ℝ[X]) {D t : ℕ} (hD : p.natDegree ≤ D) (ht : D ≤ t)
    (x : ℕ → Ω → ℝ) (ω : Ω) :
    (aeval (lagOp (Ω := Ω)) p) x t ω = ∑ j ∈ Finset.range (D + 1), p.coeff j * x (t - j) ω := by
  rw [aeval_eq_sum_range' (n := D + 1) (by omega)]
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.mp hj
  rw [lagOp_pow_apply (by omega)]

/-- Woodford (2003), eq. (1.28), p. 556: the forward-looking part of the criterion,
`w_t = B₂' B(L) q_t = B₂' ∑_{j ≤ D} B_j q_{t−j}`. -/
noncomputable def wproc {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ[X]) (D : ℕ) (B2 : ι → ℝ)
    (q : ℕ → Ω → ι → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => B2 ⬝ᵥ ∑ j ∈ Finset.range (D + 1), TargetCriterion.Lag.Bc B j *ᵥ q (t - j) ω

/-- Woodford (2003), eqs. (1.23) and (1.28), p. 556: with `v_t = λ_i (i_t − i*)`, the target
criterion (1.23) at a date `t ≥ D` is `λ_i α(L)(i_t − i*) + w_t`. -/
theorem crit_eq_rule {ι : Type*} [Fintype ι] (α : ℝ[X]) (B : Matrix ι ι ℝ[X])
    {D : ℕ} (hα : α.natDegree ≤ D) (B2 : ι → ℝ) (lam istar : ℝ) (i : ℕ → Ω → ℝ)
    (q : ℕ → Ω → ι → ℝ) {t : ℕ} (ht : D ≤ t) (ω : Ω) :
    TargetCriterion.Crit.crit α B D B2 (fun s ω => lam * (i s ω - istar)) q t ω =
      (lam • (aeval (lagOp (Ω := Ω)) α) (fun s ω => i s ω - istar) + wproc B D B2 q) t ω := by
  unfold TargetCriterion.Crit.crit wproc
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [aeval_lagOp_apply_of_le α hα ht, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Woodford (2003), eq. (1.28), p. 556: `w_t = B₂'B(L)q_t` is bounded and adapted when `q` is. -/
theorem wproc_bounded_adapted {𝔼 : ExpectationSystem Ω} {ι : Type*} [Fintype ι]
    (B : Matrix ι ι ℝ[X]) (D : ℕ) (B2 : ι → ℝ) {q : ℕ → Ω → ι → ℝ} (hqb : BoundedV q)
    (hqa : AdaptedV 𝔼 q) : BoundedProc (wproc B D B2 q) ∧ 𝔼.Adapted (wproc B D B2 q) := by
  refine ⟨?_, fun t => ?_⟩
  · obtain ⟨M, hM⟩ := hqb
    choose K hK using fun j => exists_bound_mulVec (TargetCriterion.Lag.Bc B j) M
    refine ⟨Fintype.card ι * ((∑ r, |B2 r|) * ∑ j ∈ Finset.range (D + 1), K j),
      fun t ω => ?_⟩
    refine abs_dotProduct_le (fun r => Finset.single_le_sum (f := fun r => |B2 r|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ r)) fun r => ?_
    rw [Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    exact hK j _ (fun c => hM _ ω c) r
  · have hk := PencilSplit.knownV_sum_mulVec 𝔼 (TargetCriterion.Lag.Bc B) hqa t (D + 1)
    unfold wproc
    have := E_sum_mul 𝔼 t B2 (fun r ω =>
      (∑ j ∈ Finset.range (D + 1), TargetCriterion.Lag.Bc B j *ᵥ q (t - j) ω) r)
    simp only [dotProduct]
    rw [this]
    funext ω
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hk r]

/-- **Woodford (2003), Proposition 8.4, p. 558, stated with the target criterion (1.23).**
Under the hypotheses of Proposition 8.3, let `Λ` be delivered by Proposition 8.1, `α`, `B` its
`det(I − ΛL)` and `adj(I − ΛL)`, `D ≥ deg α` (e.g. `D = rank Λ`), `q` the bounded
adapted forcing (1.25) and `v_t = λ_i(i_t − i*)` (Assumption 8.6). Then `α = α₁α₂` as in
`alpha_factorization`, the bounded forward inverse `g = α̃₁(L⁻¹)⁻¹ B₂'B(L)q` exists and is unique,
and for every `T ≥ D` and every bounded adapted instrument path the criterion (1.23) — which is
the implicit instrument rule (1.28), `TargetCriterion.Rule128.eq128_iff` — holds at all dates
`t ≥ T` iff the targeting rule (1.32) `g_t + λ_i α₂(L)(i_{t−m} − i*) = 0` holds at all `t ≥ T`. -/
theorem prop84_criterion [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81Conclusion P 𝔼 t0) (hA : Assumption81 P 𝔼 t0)
    (h83 : Assumption83 P.sys) {m : ℕ} (h87 : P.sys.stableCount P.β⁻¹ = Fintype.card ιZ + m)
    (hcirc : ∀ l ∈ P.sys.pencilPoly.roots, ‖l‖ ≠ P.β⁻¹) {D : ℕ}
    (hD : (alpha H.Λ).natDegree ≤ D) :
    ∃ α1 α2 : ℝ[X], alpha H.Λ = α1 * α2 ∧ α1.natDegree = m ∧
      (∀ z ∈ (α1.map Complex.ofRealHom).roots, ‖z‖ < 1) ∧
      (∀ z ∈ (α2.map Complex.ofRealHom).roots, 1 < ‖z‖) ∧
      ∀ (lam istar : ℝ) (i : ℕ → Ω → ℝ) (q : ℕ → Ω → ιz → ℝ), BoundedProc i → 𝔼.Adapted i →
        BoundedV q → AdaptedV 𝔼 q →
        (∃! g, BoundedProc g ∧ 𝔼.Adapted g ∧
          (aeval (fwdOp 𝔼) α1.reverse) g = wproc (Bpoly H.Λ) D P.sys.B2 q) ∧
        ∀ g, BoundedProc g → 𝔼.Adapted g →
          (aeval (fwdOp 𝔼) α1.reverse) g = wproc (Bpoly H.Λ) D P.sys.B2 q → ∀ T, D ≤ T →
          ((∀ t, T ≤ t → ∀ ω, TargetCriterion.Crit.crit (alpha H.Λ) (Bpoly H.Λ) D P.sys.B2
              (fun s ω => lam * (i s ω - istar)) q t ω = 0) ↔
            (∀ t, T ≤ t → (g + lam • ((lagOp (Ω := Ω)) ^ m)
              ((aeval (lagOp (Ω := Ω)) α2) (fun t ω => i t ω - istar))) t = 0)) := by
  obtain ⟨α1, α2, hfac, hmon, hdeg, hin, hout, hrev⟩ := alpha_factorization H hA h83 h87 hcirc
  have hrev0 : α1.reverse ≠ 0 := fun h => hmon.ne_zero (reverse_eq_zero.mp h)
  refine ⟨α1, α2, hfac, hdeg, hin, hout, fun lam istar i q hib hia hqb hqa => ⟨?_, ?_⟩⟩
  · obtain ⟨hwb, hwa⟩ := wproc_bounded_adapted (Bpoly H.Λ) D P.sys.B2 hqb hqa (𝔼 := 𝔼)
    exact forward_inverse_existsUnique hrev0 hrev hwb hwa
  · intro g hgb hga hg T hT
    rw [← prop84_from (α2 := α2) (lam := lam) (istar := istar) hdeg hmon.ne_zero hrev hib hia
      hgb hga hg T]
    refine forall_congr' fun t => imp_congr_right fun ht => ?_
    rw [← hfac, funext_iff]
    exact forall_congr' fun ω => by rw [crit_eq_rule _ _ hD _ _ _ _ _ (hT.trans ht)]; rfl

end Woodford.OptimalPolicyRules.Prop84General
