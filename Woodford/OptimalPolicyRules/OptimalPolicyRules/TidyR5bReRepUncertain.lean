/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bReRepConverse
import OptimalPolicyRules.TidyR5bFOCNecessity

/-!
# The exact criterion for uniqueness of `Λ` under uncertainty (p. 553 remark)

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.1 and the remark after it
(p. 553), that `Λ` and `Υ` are "uniquely defined".

The module TidyR5bReRepConverse proves, under perfect foresight, that `Λ` is unique iff it is
power-bounded. This module extends the converse to **every expectation system**.

## Re-representation under uncertainty

`reRepM` replaces `Λ` by any `Λ'` with the same bounded homogeneous solutions (path by path),
keeping `Υ` and `R`. The new `Q'` must be adapted, so on a plan with a solution `N` of
`M_{t+1} = Λ M_t + q_t` (bounded, `N_{t+1}` known at `t`) the value `N_{t₀}` is first replaced
by `E_{t₀} N_{t₀}` (`normalize`), which is again a solution and known at `t₀`; then
`q'_t = N_{t+1} − Λ' N_t`. On a plan with no such solution, `Q'` is an adapted forcing for which
the `Λ'` recursion has none either.

## The converse (`not_unique_of_not_powBdd_any`)

* `Λ` not scalar: `Λ' = G Λ G⁻¹` with `G` fixing the bounded orbits, forcing `G q`
  (`conj_repM`).
* `Λ = c I` with `|c| > 1`: `Λ' = −c I`, forcing `(−1)^{t+1} q_t`; `(−1)ᵗ` maps the solutions of
  one recursion to the other and preserves boundedness and information (`neg_repM`). Unlike the
  perfect-foresight construction (`TidyR5bReRepConverse.scal_rep`), this does not need every
  forcing to have a solution, which fails under uncertainty (the forward solution
  `−∑ c^{−k−1} q_{t+k}` need not be known at `t − 1`).

`unique_iff_powBdd_any`, `unique_iff_powBdd_any_of_assumption81`: under any expectation system
(on a nonempty sample space), given one bounded solution of (1.18), `Λ` and `Υ` are the same in
every representation iff `Λ` is power-bounded.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bReRepUncertain

open Matrix GeneralSetup PencilSplit PencilEigen Prop81General
open TargetCriterion.Prop81 GeneralFOC GeneralFOC.LQ TidyR5bReRep TidyR5bReRepConverse
open TidyR5bFOCNecessity

variable {Ω : Type*} {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### Solutions of the multiplier recursion under uncertainty -/

omit [DecidableEq ιz] in
/-- Woodford (2003), (1.20): `M` is a bounded solution of `M_{t+1} = Λ M_t + q_t` from `t₀`,
path by path, with `M_{t+1}` known at `t`. -/
def RecSolM (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (Λ : Matrix ιz ιz ℝ) (q : ℕ → Ω → ιz → ℝ)
    (M : ℕ → Ω → ιz → ℝ) : Prop :=
  BoundedV M ∧ (∀ t, t0 ≤ t → KnownV 𝔼 t (M (t + 1))) ∧
    ∀ t, t0 ≤ t → ∀ ω, M (t + 1) ω = Λ *ᵥ M t ω + q t ω

omit [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): information known at `s` is known at every `t ≥ s`. -/
theorem knownV_mono {𝔼 : ExpectationSystem Ω} {ι : Type*} {s t : ℕ} (hst : s ≤ t)
    {x : Ω → ι → ℝ} (hx : KnownV 𝔼 s x) : KnownV 𝔼 t x := fun i => by
  rw [← hx i, 𝔼.known hst]

omit [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): `E_t x` is known at `t`. -/
theorem knownV_EV (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (x : Ω → ι → ℝ) :
    KnownV 𝔼 t (EV 𝔼 t x) := fun _ => 𝔼.known le_rfl _

omit [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): a known vector equals its conditional expectation. -/
theorem EV_of_known {𝔼 : ExpectationSystem Ω} {ι : Type*} {t : ℕ} {x : Ω → ι → ℝ}
    (hx : KnownV 𝔼 t x) : EV 𝔼 t x = x := by
  funext ω i
  exact congrFun (hx i) ω

omit [DecidableEq ιz] in
/-- Woodford (2003), (1.20) (**normalisation**): a solution can be chosen with `M_{t₀}` known at
`t₀`: replace `M_{t₀}` by `E_{t₀} M_{t₀}` (when `q_{t₀}` is known at `t₀`). -/
theorem normalize {𝔼 : ExpectationSystem Ω} {t0 : ℕ} {Λ : Matrix ιz ιz ℝ}
    {q : ℕ → Ω → ιz → ℝ} (hq : KnownV 𝔼 t0 (q t0)) {M : ℕ → Ω → ιz → ℝ}
    (hM : RecSolM 𝔼 t0 Λ q M) :
    ∃ N, RecSolM 𝔼 t0 Λ q N ∧ KnownV 𝔼 t0 (N t0) := by
  classical
  obtain ⟨⟨K, hK⟩, hk, hr⟩ := hM
  set N : ℕ → Ω → ιz → ℝ := fun t => if t = t0 then EV 𝔼 t0 (M t0) else M t with hN
  have hNs : ∀ t, t ≠ t0 → N t = M t := fun t h => by rw [hN]; simp [h]
  have hN0 : N t0 = EV 𝔼 t0 (M t0) := by rw [hN]; simp
  refine ⟨N, ⟨⟨K, fun t ω i => ?_⟩, fun t ht => ?_, fun t ht ω => ?_⟩, ?_⟩
  · by_cases h : t = t0
    · rw [h, hN0]
      exact 𝔼.abs_E_le (fun ω => hK t0 ω i) t0 ω
    · rw [hNs t h]
      exact hK t ω i
  · rw [hNs (t + 1) (by omega)]
    exact hk t ht
  · rw [hNs (t + 1) (by omega)]
    by_cases h : t = t0
    · subst h
      rw [hN0]
      have e1 : EV 𝔼 t (M (t + 1)) = M (t + 1) := EV_of_known (hk t le_rfl)
      have hfun : M (t + 1) = fun ω => Λ *ᵥ M t ω + q t ω := funext (hr t le_rfl)
      calc M (t + 1) ω = EV 𝔼 t (M (t + 1)) ω := (congrFun e1 ω).symm
        _ = EV 𝔼 t (fun ω => Λ *ᵥ M t ω + q t ω) ω := by rw [hfun]
        _ = Λ *ᵥ EV 𝔼 t (M t) ω + q t ω := by
          rw [TidyR5bFOCNecessity.EV_add 𝔼 t (fun ω => Λ *ᵥ M t ω) (q t), EV_mulVec,
            EV_of_known hq]
    · rw [hNs t h]
      exact hr t ht ω
  · rw [hN0]
    exact knownV_EV 𝔼 t0 _

/-! ### Re-representation under uncertainty -/

open Classical in
omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.20) (the modified operator `Q'` under uncertainty): on a plan whose
recursion has a solution `N` (chosen with `N_{t₀}` known at `t₀`), `q'_t = N_{t+1} − Λ' N_t`
from `t₀` on; on a plan with none, the forcing `b x`. -/
noncomputable def reQM (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (Λ Λ' : Matrix ιz ιz ℝ)
    (Q : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (b : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ) :
    (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ :=
  fun x => if h : ∃ N, RecSolM 𝔼 t0 Λ (Q x) N ∧ KnownV 𝔼 t0 (N t0) then
    fun t ω => if t0 ≤ t then Classical.choose h (t + 1) ω - Λ' *ᵥ Classical.choose h t ω
      else Q x t ω
    else b x

/-- Woodford (2003), Proposition 8.1, p. 553 (**re-representation under uncertainty**): if
`Λ'` has the same bounded homogeneous solutions as `H.Λ` (path by path) and, on every bounded
plan without a solution of the `H.Λ` recursion, the `Λ'` recursion with forcing `b x` has none
either, then `(Λ', H.Υ, reQM, H.Rop)` represents the bounded solutions of (1.18). Any expectation
system. -/
theorem reRepM_equiv {𝔼 : ExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) {Λ' : Matrix ιz ιz ℝ} (hsame : HomSame t0 H.Λ Λ')
    (b : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (hb : ∀ x, ¬ (∃ M, RecSolM 𝔼 t0 H.Λ (H.Qop x) M) → ∀ D, ¬ RecSolM 𝔼 t0 Λ' (b x) D) :
    Prop81EquivM P 𝔼 t0 Λ' H.Υ (reQM 𝔼 t0 H.Λ Λ' H.Qop b) H.Rop := by
  intro y φ hyb hya hφb hφk
  set x := xproc P y with hx
  set m : ℕ → Ω → ιz → ℝ := fun t ω => Mpart (φ t ω) with hm
  have hmb : BoundedV m := by
    obtain ⟨K, hK⟩ := hφb
    exact ⟨K, fun t ω i => hK t ω (Sum.inr i)⟩
  have hmk : ∀ t, t0 ≤ t → KnownV 𝔼 t (m (t + 1)) := fun t ht => hφk t ht
  have hE120 : ∀ (L : Matrix ιz ιz ℝ) (q' : ℕ → Ω → ιz → ℝ), Eq120 t0 L q' φ ↔
      ∀ t, t0 ≤ t → ∀ ω, m (t + 1) ω = L *ᵥ m t ω + q' t ω := fun _ _ => Iff.rfl
  rw [H.equiv y φ hyb hya hφb hφk, hE120, hE120]
  by_cases hs : ∃ N, RecSolM 𝔼 t0 H.Λ (H.Qop x) N ∧ KnownV 𝔼 t0 (N t0)
  · have hQ : ∀ t, t0 ≤ t → ∀ ω, reQM 𝔼 t0 H.Λ Λ' H.Qop b x t ω =
        Classical.choose hs (t + 1) ω - Λ' *ᵥ Classical.choose hs t ω := by
      intro t ht ω
      simp only [reQM]
      rw [dite_eq_left hs]
      simp [ht]
    obtain ⟨⟨⟨KN, hKN⟩, -, hNr⟩, -⟩ := Classical.choose_spec hs
    set N := Classical.choose hs
    have hDb : ∀ ω, BddS (fun t => m t ω - N t ω) := by
      intro ω
      obtain ⟨K1, hK1⟩ := hmb
      exact ⟨K1 + KN, fun t i => (abs_sub _ _).trans (add_le_add (hK1 t ω i) (hKN t ω i))⟩
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ht ω => ?_, h2⟩
      have hD := ((hsame _ (hDb ω)).mp fun t ht => by
        rw [h1 t ht ω, hNr t ht ω, mulVec_sub]; abel) t ht
      rw [hQ t ht ω]
      have : m (t + 1) ω = N (t + 1) ω + Λ' *ᵥ (m t ω - N t ω) := by rw [← hD]; abel
      rw [this, mulVec_sub]
      abel
    · rintro ⟨h1, h2⟩
      refine ⟨fun t ht ω => ?_, h2⟩
      have hD := ((hsame _ (hDb ω)).mpr fun t ht => by
        rw [h1 t ht ω, hQ t ht ω, mulVec_sub]; abel) t ht
      have : m (t + 1) ω = N (t + 1) ω + H.Λ *ᵥ (m t ω - N t ω) := by rw [← hD]; abel
      rw [this, hNr t ht ω, mulVec_sub]
      abel
  · have hQ : reQM 𝔼 t0 H.Λ Λ' H.Qop b x = b x := by
      simp only [reQM]
      rw [dite_eq_right hs]
    have hno : ¬ ∃ M, RecSolM 𝔼 t0 H.Λ (H.Qop x) M := fun ⟨M, hM⟩ =>
      hs (normalize (fun i => H.Qadapted x t0 i) hM)
    rw [hQ]
    constructor
    · rintro ⟨h1, -⟩
      exact absurd ⟨m, hmb, hmk, h1⟩ hno
    · rintro ⟨h1, -⟩
      exact absurd ⟨hmb, hmk, h1⟩ (hb x hno m)

/-- Woodford (2003), Proposition 8.1 (**re-representation under uncertainty**): the
representation `(Λ', H.Υ, reQM, H.Rop)` of `reRepM_equiv` as a `Prop81ConclusionM`. The forcing
`b` must be adapted, and bounded on bounded plans. -/
noncomputable def reRepM {𝔼 : ExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) (Λ' : Matrix ιz ιz ℝ) (hsame : HomSame t0 H.Λ Λ')
    (b : (ℕ → Ω → ιZ ⊕ ιz → ℝ) → ℕ → Ω → ιz → ℝ)
    (hba : ∀ x, AdaptedV 𝔼 (b x)) (hbb : ∀ x, BoundedV x → BoundedV (b x))
    (hb : ∀ x, ¬ (∃ M, RecSolM 𝔼 t0 H.Λ (H.Qop x) M) → ∀ D, ¬ RecSolM 𝔼 t0 Λ' (b x) D) :
    Prop81ConclusionM P 𝔼 t0 where
  Λ := Λ'
  Υ := H.Υ
  Qop := reQM 𝔼 t0 H.Λ Λ' H.Qop b
  Rop := H.Rop
  equiv := reRepM_equiv H hsame b hb
  Qbounded := fun x hx => by
    by_cases hs : ∃ N, RecSolM 𝔼 t0 H.Λ (H.Qop x) N ∧ KnownV 𝔼 t0 (N t0)
    · obtain ⟨⟨⟨K, hK⟩, -, -⟩, -⟩ := Classical.choose_spec hs
      obtain ⟨K', hK'⟩ := exists_bound_mulVec Λ' K
      obtain ⟨KQ, hKQ⟩ := H.Qbounded x hx
      refine ⟨K + K' + |KQ|, fun t ω i => ?_⟩
      simp only [reQM]
      rw [dite_eq_left hs]
      split_ifs
      · exact ((abs_sub _ _).trans (add_le_add (hK _ ω i) (hK' _ (hK t ω) i))).trans
          (le_add_of_nonneg_right (abs_nonneg _))
      · have h1 := hKQ t ω i
        have h2 := (abs_nonneg _).trans (hK t ω i)
        have h3 := (abs_nonneg _).trans (hK' _ (hK t ω) i)
        linarith [le_abs_self KQ]
    · obtain ⟨K, hK⟩ := hbb x hx
      refine ⟨K, fun t ω i => ?_⟩
      simp only [reQM]
      rw [dite_eq_right hs]
      exact hK t ω i
  Rbounded := H.Rbounded
  Qadapted := fun x t => by
    by_cases hs : ∃ N, RecSolM 𝔼 t0 H.Λ (H.Qop x) N ∧ KnownV 𝔼 t0 (N t0)
    · obtain ⟨⟨-, hk, -⟩, h0⟩ := Classical.choose_spec hs
      by_cases ht : t0 ≤ t
      · have e : reQM 𝔼 t0 H.Λ Λ' H.Qop b x t = fun ω =>
            Classical.choose hs (t + 1) ω - Λ' *ᵥ Classical.choose hs t ω := by
          funext ω
          simp only [reQM]
          rw [dite_eq_left hs]
          simp [ht]
        rw [e]
        have hNt : KnownV 𝔼 t (Classical.choose hs t) := by
          rcases ht.lt_or_eq with hlt | heq
          · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
            exact knownV_mono (Nat.le_succ s) (hk s (by omega))
          · rw [← heq]
            exact h0
        exact knownV_sub (hk t ht) (knownV_mulVec Λ' hNt)
      · have e : reQM 𝔼 t0 H.Λ Λ' H.Qop b x t = H.Qop x t := by
          funext ω
          simp only [reQM]
          rw [dite_eq_left hs]
          simp [ht]
        rw [e]
        exact H.Qadapted x t
    · have e : reQM 𝔼 t0 H.Λ Λ' H.Qop b x = b x := by
        simp only [reQM]
        rw [dite_eq_right hs]
      rw [e]
      exact hba x t
  Radapted := H.Radapted

/-! ### The two constructions -/

/-- Woodford (2003), Proposition 8.1, p. 553 (**conjugated representation under
uncertainty**): if `G` (inverse `Gi`) fixes the bounded orbits of `H.Λ`, there is a
representation with `Λ' = G Λ Gi` and the same `Υ`, under any expectation system. -/
theorem conj_repM {𝔼 : ExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) {G Gi : Matrix ιz ιz ℝ} (hGGi : G * Gi = 1)
    (hGiG : Gi * G = 1) (hfix : ∀ v ∈ bddOrb H.Λ, G *ᵥ v = v) :
    ∃ H' : Prop81ConclusionM P 𝔼 t0, H'.Λ = G * H.Λ * Gi ∧ H'.Υ = H.Υ := by
  refine ⟨reRepM H (G * H.Λ * Gi) (conj_homSame t0 hGGi hGiG hfix)
    (fun x t ω => G *ᵥ H.Qop x t ω) (fun x t => knownV_mulVec G (H.Qadapted x t))
    (fun x hx => ?_) (fun x hs D hD => ?_), rfl, rfl⟩
  · obtain ⟨K, hK⟩ := H.Qbounded x hx
    obtain ⟨K', hK'⟩ := exists_bound_mulVec G K
    exact ⟨K', fun t ω i => hK' _ (hK t ω) i⟩
  · obtain ⟨⟨K, hK⟩, hk, hr⟩ := hD
    refine hs ⟨fun t ω => Gi *ᵥ D t ω, ?_, fun t ht => knownV_mulVec Gi (hk t ht),
      fun t ht ω => ?_⟩
    · obtain ⟨K', hK'⟩ := exists_bound_mulVec Gi K
      exact ⟨K', fun t ω i => hK' _ (hK t ω) i⟩
    · change Gi *ᵥ D (t + 1) ω = H.Λ *ᵥ (Gi *ᵥ D t ω) + H.Qop x t ω
      rw [hr t ht ω, mulVec_add, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul, one_mulVec]

/-- Woodford (2003), Proposition 8.1, p. 553 (**sign-flipped representation under
uncertainty**): if `Λ = c I` with `|c| > 1`, then `Λ' = −c I` (same `Υ`) is also a
representation, under any expectation system; the forcing is `(−1)^{t+1} q_t`. -/
theorem neg_repM {𝔼 : ExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) {c : ℝ} (hΛ : H.Λ = c • 1) (hc : 1 < |c|) :
    ∃ H' : Prop81ConclusionM P 𝔼 t0, H'.Λ = (-c) • 1 ∧ H'.Υ = H.Υ := by
  have hc2 : 1 < |-c| := by rwa [abs_neg]
  have hsame : HomSame t0 H.Λ ((-c) • 1) := by
    intro D hD
    rw [hΛ]
    have key : ∀ (d : ℝ), 1 < |d| →
        (∀ t, t0 ≤ t → D (t + 1) = (d • (1 : Matrix ιz ιz ℝ)) *ᵥ D t) →
        ∀ (e : ℝ), ∀ t, t0 ≤ t → D (t + 1) = (e • (1 : Matrix ιz ιz ℝ)) *ᵥ D t := by
      intro d hd h e t ht
      rw [zero_of_scalar hd hD h t ht, zero_of_scalar hd hD h (t + 1) (by omega), mulVec_zero]
    exact ⟨fun h => key c hc h (-c), fun h => key (-c) hc2 h c⟩
  have hsgn : ∀ t : ℕ, ((-1 : ℝ) ^ t) * (-1) ^ t = 1 := fun t => by
    rw [← mul_pow]; norm_num
  refine ⟨reRepM H ((-c) • 1) hsame (fun x t ω => ((-1 : ℝ) ^ (t + 1)) • H.Qop x t ω)
    (fun x t i => ?_) (fun x hx => ?_) (fun x hs D hD => ?_), rfl, rfl⟩
  · have h := H.Qadapted x t i
    change 𝔼.E t (((-1 : ℝ) ^ (t + 1)) • fun ω => H.Qop x t ω i) =
      ((-1 : ℝ) ^ (t + 1)) • fun ω => H.Qop x t ω i
    rw [map_smul, h]
  · obtain ⟨K, hK⟩ := H.Qbounded x hx
    refine ⟨K, fun t ω i => ?_⟩
    change |(((-1 : ℝ) ^ (t + 1)) • H.Qop x t ω) i| ≤ K
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hK t ω i
  · obtain ⟨⟨K, hK⟩, hk, hr⟩ := hD
    refine hs ⟨fun t ω => ((-1 : ℝ) ^ t) • D t ω, ⟨K, fun t ω i => ?_⟩, fun t ht i => ?_,
      fun t ht ω => ?_⟩
    · change |(((-1 : ℝ) ^ t) • D t ω) i| ≤ K
      rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact hK t ω i
    · have h := hk t ht i
      change 𝔼.E t (((-1 : ℝ) ^ (t + 1)) • fun ω => D (t + 1) ω i) =
        ((-1 : ℝ) ^ (t + 1)) • fun ω => D (t + 1) ω i
      rw [map_smul, h]
    · change ((-1 : ℝ) ^ (t + 1)) • D (t + 1) ω =
        H.Λ *ᵥ (((-1 : ℝ) ^ t) • D t ω) + H.Qop x t ω
      rw [hr t ht ω, hΛ]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_mulVec, one_mulVec, mulVec_smul]
      linear_combination (H.Qop x t ω i) * hsgn (t + 1)

/-! ### The general converse and the exact criterion -/

/-- Woodford (2003), p. 553, the remark after Proposition 8.1 (**general converse under
uncertainty**): under any expectation system, if `Λ` is not power-bounded, some other
representation of Proposition 8.1 has a different `Λ'` (and the same `Υ`). -/
theorem not_unique_of_not_powBdd_any {𝔼 : ExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {t0 : ℕ} (H : Prop81ConclusionM P 𝔼 t0) (hnp : ¬ PowBdd H.Λ) :
    ∃ H' : Prop81ConclusionM P 𝔼 t0, H'.Λ ≠ H.Λ ∧ H'.Υ = H.Υ := by
  have hne : Nonempty ιz := by
    by_contra h0
    exact hnp ⟨0, fun _ i => absurd ⟨i⟩ h0⟩
  obtain ⟨i0⟩ := hne
  by_cases hsc : ∃ c : ℝ, H.Λ = c • 1
  · obtain ⟨c, hc⟩ := hsc
    have hc1 : 1 < |c| := by
      by_contra hle
      push Not at hle
      refine hnp ⟨1, fun k i j => ?_⟩
      rw [hc, smul_pow, one_pow, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, abs_mul,
        abs_pow]
      have h1 : |c| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg c) hle
      split_ifs <;> simp [h1]
    obtain ⟨H', h1, h2⟩ := neg_repM H hc hc1
    refine ⟨H', fun h => ?_, h2⟩
    have e := congrFun (congrFun (h1.symm.trans (h.trans hc)) i0) i0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e
    have hc0 : c ≠ 0 := fun h0 => by rw [h0, abs_zero] at hc1; linarith
    exact hc0 (by linarith)
  · have hlt : bddOrb H.Λ < ⊤ := lt_top_iff_ne_top.mpr fun h => hnp (powBdd_of_top h)
    obtain ⟨f, hf0, hfV⟩ := (bddOrb H.Λ).exists_le_ker_of_lt_top hlt
    set w : ιz → ℝ := fun i => f (Pi.single i 1) with hw
    have hwf : ∀ v, w ⬝ᵥ v = f v := by
      intro v
      conv_rhs => rw [pi_eq_sum_univ v]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dotProduct, hw]
      exact Finset.sum_congr rfl fun i _ => by
        rw [mul_comm]
        congr 2
        funext j
        simp only [Pi.single_apply, eq_comm]
    have hw0 : ∃ b, w b ≠ 0 := by
      by_contra hall
      push Not at hall
      refine hf0 (LinearMap.ext fun v => ?_)
      rw [← hwf, LinearMap.zero_apply, dotProduct]
      exact Finset.sum_eq_zero fun i _ => by rw [hall i, zero_mul]
    obtain ⟨b, hb⟩ := hw0
    have hnc : ∃ i, ∀ s : ℝ, s ≠ 0 →
        vecMulVec (Pi.single i s) (w ᵥ* H.Λ) ≠ vecMulVec (H.Λ *ᵥ Pi.single i s) w := by
      by_contra hall
      push Not at hall
      exact hsc ⟨_, scalar_of_comm hb hall⟩
    obtain ⟨i, hi⟩ := hnc
    obtain ⟨s, hs0, hsdet⟩ : ∃ s : ℝ, s ≠ 0 ∧ 1 + w i * s ≠ 0 := by
      by_cases h1 : 1 + w i * 1 = 0
      · refine ⟨2, two_ne_zero, ?_⟩
        intro h2
        linarith
      · exact ⟨1, one_ne_zero, h1⟩
    set u : ιz → ℝ := Pi.single i s with hu
    set G : Matrix ιz ιz ℝ := 1 + vecMulVec u w with hG
    have hdet : IsUnit G.det := by
      rw [hG, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, hu,
        dotProduct_single]
      exact isUnit_iff_ne_zero.mpr hsdet
    have hfix : ∀ v ∈ bddOrb H.Λ, G *ᵥ v = v := by
      intro v hv
      have h0 : w ⬝ᵥ v = 0 := by rw [hwf]; exact hfV hv
      rw [hG, add_mulVec, one_mulVec]
      conv_rhs => rw [← add_zero v]
      congr 1
      funext a
      simp only [mulVec, dotProduct, vecMulVec_apply, Pi.zero_apply, mul_assoc,
        ← Finset.mul_sum]
      rw [show (∑ x, w x * v x) = w ⬝ᵥ v from rfl, h0, mul_zero]
    obtain ⟨H', h1, h2⟩ := conj_repM H (mul_nonsing_inv G hdet) (nonsing_inv_mul G hdet) hfix
    refine ⟨H', fun h => hi s hs0 ?_, h2⟩
    have hcomm : G * H.Λ = H.Λ * G := by
      calc G * H.Λ = G * H.Λ * G⁻¹ * G := by
            rw [Matrix.mul_assoc _ G⁻¹, nonsing_inv_mul G hdet, Matrix.mul_one]
        _ = H.Λ * G := by rw [← h1, h]
    rw [hG, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, vecMulVec_mul,
      mul_vecMulVec] at hcomm
    exact add_left_cancel hcomm

/-- Woodford (2003), p. 553, the remark after Proposition 8.1 (**exact criterion under
uncertainty**): under any expectation system on a nonempty sample space, if (1.18) has one
bounded solution, `Λ` and `Υ` are the same in every representation iff `Λ` is power-bounded
(`TidyR5bReRep.unique_of_powBdd`, `not_unique_of_not_powBdd_any`). -/
theorem unique_iff_powBdd_any [Nonempty Ω] {𝔼 : ExpectationSystem Ω} {P : LQProblem ιZ ιz ιτ}
    {t0 : ℕ} (H : Prop81ConclusionM P 𝔼 t0) {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hy0b : BoundedV y0) (hy0a : AdaptedV 𝔼 y0)
    (hφ0b : BoundedV φ0) (hφ0k : MultKnown 𝔼 t0 φ0) (h118 : Eq118 P 𝔼 t0 y0 φ0) :
    (∀ H' : Prop81ConclusionM P 𝔼 t0, H'.Λ = H.Λ ∧ H'.Υ = H.Υ) ↔ PowBdd H.Λ := by
  constructor
  · intro hall
    by_contra hnp
    obtain ⟨H', h1, -⟩ := not_unique_of_not_powBdd_any H hnp
    exact h1 (hall H').1
  · intro hpb H'
    obtain ⟨h1, h2⟩ := unique_of_powBdd H H' hy0b hy0a hφ0b hφ0k h118 hpb
    exact ⟨h1.symm, h2.symm⟩

/-- Woodford (2003), p. 553 (**exact criterion under Assumption 8.1, any expectation system**):
`Λ` and `Υ` are the same in every representation of Proposition 8.1 iff `Λ` is power-bounded. -/
theorem unique_iff_powBdd_any_of_assumption81 [Nonempty Ω] {𝔼 : ExpectationSystem Ω}
    {P : LQProblem ιZ ιz ιτ} {t0 : ℕ} (hA : Assumption81 P 𝔼 t0)
    (H : Prop81ConclusionM P 𝔼 t0) :
    (∀ H' : Prop81ConclusionM P 𝔼 t0, H'.Λ = H.Λ ∧ H'.Υ = H.Υ) ↔ PowBdd H.Λ := by
  obtain ⟨y, φ, hy, hya, hφ, hφk, h118⟩ := Prop83.exists_base_of_assumption81 hA
  exact unique_iff_powBdd_any H hy hya hφ hφk h118

end Woodford.OptimalPolicyRules.TidyR5bReRepUncertain
