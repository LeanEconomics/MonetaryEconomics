/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilAssumptions

/-!
# Uniqueness in Proposition 8.1 and the remark on p. 553

Woodford (2003), *Interest and Prices*, Chapter 8, p. 553 (the paragraph after Proposition 8.1):
"In the case that there are exactly `n_Z` roots of (1.15) such that `|μᵢ| < β⁻¹`, the matrices
`Λ, Υ, Q`, and `R` are uniquely defined, and there is a unique solution to (1.18) for the
evolution of the multipliers given a process for the target variables and an initial condition
`M_{t₀−1}`."

* `boundedV_mrec_of_powDecay`: a stable `Λ` keeps the recursion (1.20) bounded.
* `prop81M_solution`: for stable `Λ`, given a bounded adapted plan and a bounded `M_{t₀−1}` known
  at `t₀`, (1.18) has exactly one bounded multiplier solution with `M_t` known at `t`.
* `prop81M_unique`: for stable `Λ`, any two representations of Proposition 8.1 have the same
  `Λ`, `Υ`, and the same `Q(L⁻¹)`, `R(L⁻¹)` on bounded adapted plans.
* `powDecay_Λ_of_outside`: under Assumptions 8.2 (i)–8.4, if every unselected nonzero root has
  `|μ| > β⁻¹` (exactly `n_Z` roots inside and **none on** `|μ| = β⁻¹`), `Λ` is stable; so the
  remark holds with that proviso (`remark_p553`).
* `circle_counterexample`: the proviso is needed. With one root exactly on `|μ| = β⁻¹` (and
  `n_Z = 0` roots inside, so "exactly `n_Z`" holds), (1.18) has **no** bounded solution for a
  bounded plan.
* `eig_conj`, `realSelection_misses_unpaired`: in case (ii) of Assumption 8.2 no real deflating
  pair can carry the unpaired complex root (a real `Ψ` has a spectrum closed under conjugation),
  which is why the invariant-subspace construction covers case (i) only.
-/

namespace Woodford.OptimalPolicyRules.Prop81Unique

open Matrix GeneralSetup PencilSplit PencilEigen PencilAssumptions Prop81General
open TargetCriterion.Prop81 TargetCriterion.Recursion GeneralFOC.LQ GeneralFOC.Selection

variable {Ω : Type*}

/-! ### Stable recursions -/

/-- Woodford (2003), eq. (1.20): `m_k = Λ^{k+1} m₀ + ∑_{j ≤ k} Λ^{k−j} u_j`. -/
theorem mrec_formula {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι ℝ)
    (m0 : Ω → ι → ℝ) (u : ℕ → Ω → ι → ℝ) (k : ℕ) (ω : Ω) :
    mrec Λ m0 u k ω =
      Λ ^ (k + 1) *ᵥ m0 ω + ∑ j ∈ Finset.range (k + 1), Λ ^ (k - j) *ᵥ u j ω := by
  induction k with
  | zero => simp [mrec]
  | succ k ih =>
    change Λ *ᵥ mrec Λ m0 u k ω + u (k + 1) ω = _
    rw [ih, mulVec_add, mulVec_mulVec, ← pow_succ', mulVec_sum, Finset.sum_range_succ _ (k + 1),
      Nat.sub_self, pow_zero, one_mulVec, add_assoc]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [mulVec_mulVec, ← pow_succ', show k - j + 1 = k + 1 - j by omega]

/-- Woodford (2003), eq. (1.20), p. 553: if the powers of `Λ` decay geometrically, bounded
forcing and a bounded start give a bounded multiplier path (`MultStable`). -/
theorem boundedV_mrec_of_powDecay {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ : Matrix ι ι ℝ}
    (hΛ : PowDecay Λ) {m0 : Ω → ι → ℝ} (hm0 : ∃ K, ∀ ω i, |m0 ω i| ≤ K)
    {u : ℕ → Ω → ι → ℝ} (hu : BoundedV u) : BoundedV (mrec Λ m0 u) := by
  obtain ⟨C, r, hr0, hr1, hG⟩ := hΛ
  obtain ⟨K0, hK0⟩ := hm0
  obtain ⟨Ku, hKu⟩ := hu
  have hpowle : ∀ k : ℕ, C * r ^ k ≤ |C| := fun k =>
    calc C * r ^ k ≤ |C| * r ^ k := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hr0 k)
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1.le) (abs_nonneg C)
      _ = |C| := mul_one _
  have hgeo : ∀ k : ℕ, ∑ j ∈ Finset.range (k + 1), r ^ (k - j) ≤ (1 - r)⁻¹ := by
    intro k
    have hre : ∑ j ∈ Finset.range (k + 1), r ^ (k - j) = ∑ j ∈ Finset.range (k + 1), r ^ j := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.mp hj
      congr 1
      omega
    rw [hre, ← tsum_geometric_of_lt_one hr0 hr1]
    exact Summable.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
      (summable_geometric_of_lt_one hr0 hr1)
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  refine ⟨(Fintype.card ι : ℝ) * (|C| * |K0|) +
    (Fintype.card ι : ℝ) * (|C| * |Ku|) * (1 - r)⁻¹, fun k ω i => ?_⟩
  rw [mrec_formula, Pi.add_apply, Finset.sum_apply]
  have h1 : |(Λ ^ (k + 1) *ᵥ m0 ω) i| ≤ (Fintype.card ι : ℝ) * (|C| * |K0|) := by
    refine (abs_mulVec_pow_le hG (k + 1) (fun j => (hK0 ω j).trans (le_abs_self K0)) i).trans ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hpowle (k + 1)) (abs_nonneg K0)) hn
  have h2 : |∑ j ∈ Finset.range (k + 1), (Λ ^ (k - j) *ᵥ u j ω) i| ≤
      (Fintype.card ι : ℝ) * (|C| * |Ku|) * (1 - r)⁻¹ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range (k + 1), |(Λ ^ (k - j) *ᵥ u j ω) i| ≤
        (Fintype.card ι : ℝ) * (|C| * |Ku|) * r ^ (k - j) := by
      intro j _
      refine (abs_mulVec_pow_le hG (k - j) (fun l => (hKu j ω l).trans (le_abs_self Ku)) i).trans
        ?_
      have hc : C * r ^ (k - j) * |Ku| ≤ |C| * |Ku| * r ^ (k - j) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hr0 (k - j))) (abs_nonneg Ku)
        linarith [this]
      calc (Fintype.card ι : ℝ) * (C * r ^ (k - j) * |Ku|)
          ≤ (Fintype.card ι : ℝ) * (|C| * |Ku| * r ^ (k - j)) := mul_le_mul_of_nonneg_left hc hn
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hgeo k) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ### The multiplier solution given `M_{t₀−1}`, and uniqueness of the representation -/

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), eq. (1.20): the multipliers `M_{s−1}` generated by (1.20) from `M_{t₀−1} = m₀`
(the value at `s` is `M_{s−1}`). -/
noncomputable def Mrep (Λ : Matrix ιz ιz ℝ) (m0 : Ω → ιz → ℝ) (q : ℕ → Ω → ιz → ℝ) (t0 s : ℕ) :
    Ω → ιz → ℝ :=
  if s ≤ t0 then m0 else mrec Λ m0 (fun k => q (t0 + k)) (s - t0 - 1)

/-- Woodford (2003), eqs. (1.20)–(1.21): the multipliers `φ_s = (ξ_s, M_{s−1})` generated from
`M_{t₀−1} = m₀` by a representation `H` of Proposition 8.1 and a plan `y`. -/
noncomputable def φrep {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) (m0 : Ω → ιz → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun s ω => Sum.elim
    (if t0 ≤ s then H.Υ *ᵥ Mrep H.Λ m0 (H.Qop (xproc P y)) t0 s ω + H.Rop (xproc P y) s ω
      else 0)
    (Mrep H.Λ m0 (H.Qop (xproc P y)) t0 s ω)

omit [DecidableEq ιz] in
/-- Woodford (2003), eq. (1.20): `Mrep` satisfies `M_t = Λ M_{t−1} + q_t` for `t ≥ t₀`. -/
theorem Mrep_rec (Λ : Matrix ιz ιz ℝ) (m0 : Ω → ιz → ℝ) (q : ℕ → Ω → ιz → ℝ) {t0 t : ℕ}
    (ht : t0 ≤ t) (ω : Ω) : Mrep Λ m0 q t0 (t + 1) ω = Λ *ᵥ Mrep Λ m0 q t0 t ω + q t ω := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  cases k with
  | zero =>
    simp [Mrep, mrec]
  | succ k =>
    simp only [Mrep, show ¬ t0 + (k + 1) + 1 ≤ t0 by omega, ↓reduceIte,
      show ¬ t0 + (k + 1) ≤ t0 by omega, show t0 + (k + 1) + 1 - t0 - 1 = k + 1 by omega,
      show t0 + (k + 1) - t0 - 1 = k by omega]
    rfl

omit [DecidableEq ιz] in
/-- Woodford (2003), p. 540: `Mrep` at `t + 1` (that is, `M_t`) is known at `t` (`m₀` known at
`t₀`, `q` adapted). -/
theorem Mrep_known {𝔼 : ExpectationSystem Ω}
    (Λ : Matrix ιz ιz ℝ) {m0 : Ω → ιz → ℝ} {q : ℕ → Ω → ιz → ℝ} {t0 : ℕ}
    (hm0 : KnownV 𝔼 t0 m0) (hq : AdaptedV 𝔼 q) :
    ∀ t, t0 ≤ t → KnownV 𝔼 t (Mrep Λ m0 q t0 (t + 1)) := by
  intro t ht
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  simp only [Mrep, show ¬ t0 + k + 1 ≤ t0 by omega, ↓reduceIte,
    show t0 + k + 1 - t0 - 1 = k by omega]
  induction k with
  | zero =>
    exact knownV_mulVec_add 𝔼 Λ hm0 (hq (t0 + 0))
  | succ k ih =>
    exact knownV_mulVec_add 𝔼 Λ (KnownV.mono 𝔼 (by omega) (ih (by omega))) (hq (t0 + (k + 1)))

/-- Woodford (2003), p. 553: with a stable `Λ`, `Mrep` is bounded for a bounded start and
bounded forcing. -/
theorem Mrep_bounded {Λ : Matrix ιz ιz ℝ} (hΛ : PowDecay Λ) {m0 : Ω → ιz → ℝ}
    (hm0 : ∃ K, ∀ ω i, |m0 ω i| ≤ K) {q : ℕ → Ω → ιz → ℝ} (hq : BoundedV q) (t0 : ℕ) :
    BoundedV (Mrep Λ m0 q t0) := by
  obtain ⟨K1, hK1⟩ := hm0
  obtain ⟨K2, hK2⟩ := boundedV_mrec_of_powDecay hΛ ⟨K1, hK1⟩
    (u := fun k => q (t0 + k)) (by obtain ⟨Kq, hKq⟩ := hq; exact ⟨Kq, fun k => hKq (t0 + k)⟩)
  refine ⟨max K1 K2, fun s ω i => ?_⟩
  unfold Mrep
  split_ifs
  · exact (hK1 ω i).trans (le_max_left _ _)
  · exact (hK2 _ ω i).trans (le_max_right _ _)

/-- Woodford (2003), p. 553: the generated multipliers satisfy (1.20)–(1.21) for `H`, have
`M_{t₀−1} = m₀`, `M_t` known at `t`, and (for stable `Λ`) are bounded. -/
theorem φrep_spec {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) (hΛ : PowDecay H.Λ) {m0 : Ω → ιz → ℝ}
    (hm0b : ∃ K, ∀ ω i, |m0 ω i| ≤ K) (hm0k : KnownV 𝔼 t0 m0)
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hyb : BoundedV y) :
    Eq120 t0 H.Λ (H.Qop (xproc P y)) (φrep H m0 y) ∧
      Eq121 t0 H.Υ (H.Rop (xproc P y)) (φrep H m0 y) ∧ BoundedV (φrep H m0 y) ∧
      MultKnown 𝔼 t0 (φrep H m0 y) ∧ (∀ ω, Mpart (φrep H m0 y t0 ω) = m0 ω) := by
  have hxb := boundedV_xproc (P := P) hyb
  have hMb := Mrep_bounded hΛ hm0b (H.Qbounded _ hxb) t0
  refine ⟨fun t ht ω => Mrep_rec _ _ _ ht ω, fun t ht ω => ?_, ?_,
    fun t ht => Mrep_known H.Λ hm0k (H.Qadapted _) t ht, fun ω => ?_⟩
  · simp only [φrep, ht, ↓reduceIte]
    rfl
  · obtain ⟨K1, hK1⟩ := hMb
    obtain ⟨KR, hKR⟩ := H.Rbounded _ hxb
    obtain ⟨KΥ, hKΥ⟩ := GeneralFOC.exists_bound_mulVec H.Υ K1
    refine ⟨max (max (KΥ + KR) K1) 0, fun s ω a => ?_⟩
    rcases a with i | r
    · by_cases hs : t0 ≤ s
      · simp only [φrep, hs, ↓reduceIte, Sum.elim_inl, Pi.add_apply]
        exact (abs_add_le _ _).trans ((add_le_add (hKΥ _ (hK1 s ω) i) (hKR s ω i)).trans
          ((le_max_left _ _).trans (le_max_left _ _)))
      · simp only [φrep, hs, ↓reduceIte, Sum.elim_inl, Pi.zero_apply, abs_zero]
        exact le_max_right _ _
    · exact (hK1 s ω r).trans ((le_max_right _ _).trans (le_max_left _ _))
  · change Mrep H.Λ m0 (H.Qop (xproc P y)) t0 t0 ω = m0 ω
    simp [Mrep]

/-- Woodford (2003), p. 553 (the remark after Proposition 8.1, existence and uniqueness of the
multiplier path): for a representation `H` with stable `Λ`, a bounded adapted plan and a bounded
initial `M_{t₀−1} = m₀` known at `t₀`, (1.18) has a bounded solution `φ` (with `M_t` known at
`t`) with that initial condition, and any two such solutions agree from `t₀` on. -/
theorem prop81M_solution {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) (hΛ : PowDecay H.Λ) {m0 : Ω → ιz → ℝ}
    (hm0b : ∃ K, ∀ ω i, |m0 ω i| ≤ K) (hm0k : KnownV 𝔼 t0 m0)
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hyb : BoundedV y) (hya : AdaptedV 𝔼 y) :
    (∃ φ, BoundedV φ ∧ MultKnown 𝔼 t0 φ ∧ (∀ ω, Mpart (φ t0 ω) = m0 ω) ∧ Eq118 P 𝔼 t0 y φ) ∧
      ∀ φ φ', BoundedV φ → MultKnown 𝔼 t0 φ → (∀ ω, Mpart (φ t0 ω) = m0 ω) →
        Eq118 P 𝔼 t0 y φ → BoundedV φ' → MultKnown 𝔼 t0 φ' →
        (∀ ω, Mpart (φ' t0 ω) = m0 ω) → Eq118 P 𝔼 t0 y φ' → ∀ t, t0 ≤ t → φ t = φ' t := by
  obtain ⟨h120, h121, hb, hk, hinit⟩ := φrep_spec H hΛ hm0b hm0k hyb
  refine ⟨⟨φrep H m0 y, hb, hk, hinit, (H.equiv y _ hyb hya hb hk).mpr ⟨h120, h121⟩⟩, ?_⟩
  intro φ φ' hφb hφk hφ0 hφ hφ'b hφ'k hφ'0 hφ'
  obtain ⟨e120, e121⟩ := (H.equiv y φ hyb hya hφb hφk).mp hφ
  obtain ⟨e120', e121'⟩ := (H.equiv y φ' hyb hya hφ'b hφ'k).mp hφ'
  have hM : ∀ t, t0 ≤ t → Mpart ∘ φ t = Mpart ∘ φ' t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact funext fun ω => (hφ0 ω).trans (hφ'0 ω).symm
    | succ t ht ih =>
      funext ω
      have h1 := e120 t ht ω
      have h2 := e120' t ht ω
      have h3 := congrFun ih ω
      simp only [Function.comp] at h3 ⊢
      rw [h1, h2, h3]
  intro t ht
  funext ω a
  have hMt := congrFun (hM t ht) ω
  simp only [Function.comp] at hMt
  rcases a with i | r
  · have hξ : ξpart (φ t ω) = ξpart (φ' t ω) := by rw [e121 t ht ω, e121' t ht ω, hMt]
    exact congrFun hξ i
  · exact congrFun hMt r

/-- Woodford (2003), p. 553 (the remark after Proposition 8.1, uniqueness of `Λ, Υ, Q, R`): any
two representations `H`, `H'` of Proposition 8.1 (corrected form), the first with stable `Λ`,
have the same `Λ` and `Υ`, and the same operators `E_t Q(L⁻¹)`, `E_t R(L⁻¹)` on (the
`T̃'W(τ − τ*)` of) every bounded adapted plan, from `t₀` on. -/
theorem prop81M_unique [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H H' : Prop81ConclusionM P 𝔼 t0) (hΛ : PowDecay H.Λ) :
    H.Λ = H'.Λ ∧ H.Υ = H'.Υ ∧ ∀ y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ, BoundedV y → AdaptedV 𝔼 y →
      ∀ t, t0 ≤ t → H.Qop (xproc P y) t = H'.Qop (xproc P y) t ∧
        H.Rop (xproc P y) t = H'.Rop (xproc P y) t := by
  -- the generated multipliers satisfy the primed representation too
  have hboth : ∀ (m : ιz → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ), BoundedV y → AdaptedV 𝔼 y →
      Eq120 t0 H'.Λ (H'.Qop (xproc P y)) (φrep H (fun _ => m) y) ∧
        Eq121 t0 H'.Υ (H'.Rop (xproc P y)) (φrep H (fun _ => m) y) := by
    intro m y hyb hya
    have hm0k : KnownV 𝔼 t0 (fun _ : Ω => m) := fun i => 𝔼.const t0 (m i)
    obtain ⟨h120, h121, hb, hk, -⟩ :=
      φrep_spec H hΛ ⟨∑ i, |m i|, fun _ i => Finset.single_le_sum (f := fun i => |m i|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)⟩ hm0k hyb
    have h118 := (H.equiv y _ hyb hya hb hk).mpr ⟨h120, h121⟩
    exact (H'.equiv y _ hyb hya hb hk).mp h118
  have hy0b : BoundedV (0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) := ⟨0, by simp⟩
  have hy0a : AdaptedV 𝔼 (0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) := fun t i => 𝔼.const t 0
  obtain ω0 : Ω := Classical.arbitrary Ω
  have hMt0 : ∀ m : ιz → ℝ, ∀ y, Mrep H.Λ (fun _ => m) (H.Qop (xproc P y)) t0 t0 ω0 = m :=
    fun m y => by simp [Mrep]
  -- the comparison at `t₀`
  have key : ∀ (m : ιz → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ), BoundedV y → AdaptedV 𝔼 y →
      H.Λ *ᵥ m + H.Qop (xproc P y) t0 ω0 = H'.Λ *ᵥ m + H'.Qop (xproc P y) t0 ω0 ∧
      H.Υ *ᵥ m + H.Rop (xproc P y) t0 ω0 = H'.Υ *ᵥ m + H'.Rop (xproc P y) t0 ω0 := by
    intro m y hyb hya
    obtain ⟨h2, h3⟩ := hboth m y hyb hya
    have hA : Mrep H.Λ (fun _ => m) (H.Qop (xproc P y)) t0 (t0 + 1) ω0 =
        H'.Λ *ᵥ Mrep H.Λ (fun _ => m) (H.Qop (xproc P y)) t0 t0 ω0 +
          H'.Qop (xproc P y) t0 ω0 := h2 t0 le_rfl ω0
    rw [Mrep_rec _ _ _ (le_refl t0), hMt0] at hA
    have hB := h3 t0 le_rfl ω0
    simp only [φrep, le_refl, ↓reduceIte] at hB
    change H.Υ *ᵥ Mrep H.Λ (fun _ => m) (H.Qop (xproc P y)) t0 t0 ω0 +
        H.Rop (xproc P y) t0 ω0 =
      H'.Υ *ᵥ Mrep H.Λ (fun _ => m) (H.Qop (xproc P y)) t0 t0 ω0 +
        H'.Rop (xproc P y) t0 ω0 at hB
    rw [hMt0] at hB
    exact ⟨hA, hB⟩
  have hmat : ∀ (A A' : Matrix ιz ιz ℝ) (c c' : ιz → ℝ), (∀ m, A *ᵥ m + c = A' *ᵥ m + c') →
      A = A' := by
    intro A A' c c' h
    have k0 := h 0
    simp only [mulVec_zero, zero_add] at k0
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [Pi.add_apply, Pi.add_apply, k0, add_left_inj, mulVec_single_one, mulVec_single_one]
      at this
    exact this
  have hmat' : ∀ (A A' : Matrix ιZ ιz ℝ) (c c' : ιZ → ℝ), (∀ m, A *ᵥ m + c = A' *ᵥ m + c') →
      A = A' := by
    intro A A' c c' h
    have k0 := h 0
    simp only [mulVec_zero, zero_add] at k0
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [Pi.add_apply, Pi.add_apply, k0, add_left_inj, mulVec_single_one, mulVec_single_one]
      at this
    exact this
  have hΛeq : H.Λ = H'.Λ := hmat _ _ _ _ fun m => (key m 0 hy0b hy0a).1
  have hΥeq : H.Υ = H'.Υ := hmat' _ _ _ _ fun m => (key m 0 hy0b hy0a).2
  refine ⟨hΛeq, hΥeq, fun y hyb hya t ht => ⟨?_, ?_⟩⟩
  · funext ω
    obtain ⟨h2, -⟩ := hboth 0 y hyb hya
    have hA : Mrep H.Λ (fun _ => 0) (H.Qop (xproc P y)) t0 (t + 1) ω =
        H'.Λ *ᵥ Mrep H.Λ (fun _ => 0) (H.Qop (xproc P y)) t0 t ω + H'.Qop (xproc P y) t ω :=
      h2 t ht ω
    rw [Mrep_rec _ _ _ ht, hΛeq, add_right_inj] at hA
    exact hA
  · funext ω
    obtain ⟨-, h3⟩ := hboth 0 y hyb hya
    have hB := h3 t ht ω
    simp only [φrep, ht, ↓reduceIte] at hB
    change H.Υ *ᵥ Mrep H.Λ (fun _ => 0) (H.Qop (xproc P y)) t0 t ω + H.Rop (xproc P y) t ω =
      H'.Υ *ᵥ Mrep H.Λ (fun _ => 0) (H.Qop (xproc P y)) t0 t ω + H'.Rop (xproc P y) t ω at hB
    rw [hΥeq, add_right_inj] at hB
    exact hB

/-! ### When is `Λ` stable? -/

/-- Woodford (2003), p. 553: under Assumptions 8.2 (i)–8.4, if every unselected nonzero root of
(1.15) has `|μ| > β⁻¹` — exactly `n_Z` roots with `|μ| < β⁻¹` and none on `|μ| = β⁻¹` — then
`Λ` is stable: its nonzero eigenvalues are the `(βμ)⁻¹` (`nonzero_eig_eq`), of modulus `< 1`. -/
theorem powDecay_Λ_of_outside {S : LinearRESystem ιZ ιz} {β : ℝ} (hβ : 0 < β)
    (h82 : Assumption82 S β) (R : RealSelection S h82.sel) (h83 : Assumption83 S)
    (h84 : Assumption84 S h82.sel) (hout : ∀ μ ∈ unselected S h82.sel, β⁻¹ < ‖μ‖) :
    PowDecay (Λmat S β (splitOfSel hβ h82 R h83 h84).J) := by
  refine powDecay_of_eig _ fun w hw => ?_
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]
    exact one_pos
  have hroot : w ∈ ((Λmat S β (splitOfSel hβ h82 R h83 h84).J).map
      Complex.ofReal).charpoly.roots.filter (fun x => x ≠ 0) := by
    rw [Multiset.mem_filter, Polynomial.mem_roots (charpoly_monic _).ne_zero, Polynomial.IsRoot,
      eval_charpoly]
    exact ⟨hw, hw0⟩
  rw [← nonzero_eig_eq hβ h82 R h83 h84] at hroot
  obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hroot
  have hμ' := hout μ hμ
  have hpos : 0 < ‖μ‖ := lt_trans (inv_pos.mpr hβ) hμ'
  rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
  have h1 : 1 < β * ‖μ‖ := by
    have := mul_lt_mul_of_pos_left hμ' hβ
    rwa [mul_inv_cancel₀ hβ.ne'] at this
  exact inv_lt_one_of_one_lt₀ h1

/-- Woodford (2003), p. 553, **the remark after Proposition 8.1, corrected**: under Assumptions
8.2 (i)–8.4, if exactly `n_Z` roots of (1.15) satisfy `|μ| < β⁻¹` **and no root lies on
`|μ| = β⁻¹`** (every unselected nonzero root has `|μ| > β⁻¹`), then `Λ` is stable, the matrices
`Λ`, `Υ` and the operators `Q(L⁻¹)`, `R(L⁻¹)` (on bounded adapted plans) are uniquely
determined, and for every bounded adapted plan and bounded `M_{t₀−1}` known at `t₀` there is
exactly one bounded multiplier solution of (1.18). -/
theorem remark_p553 [Nonempty Ω] (P : LQProblem ιZ ιz ιτ) (h82 : Assumption82 P.sys P.β)
    (hi : ConjClosed h82.sel) (h83 : Assumption83 P.sys) (h84 : Assumption84 P.sys h82.sel)
    (hout : ∀ μ ∈ unselected P.sys h82.sel, P.β⁻¹ < ‖μ‖) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    PowDecay (prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0).Λ ∧
      ∀ H' : Prop81ConclusionM P 𝔼 t0, (prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0).Λ = H'.Λ ∧
        (prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0).Υ = H'.Υ ∧
        ∀ y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ, BoundedV y → AdaptedV 𝔼 y → ∀ t, t0 ≤ t →
          (prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0).Qop (xproc P y) t = H'.Qop (xproc P y) t ∧
          (prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0).Rop (xproc P y) t = H'.Rop (xproc P y) t := by
  have hst : PowDecay (prop81 P (splitOf P h82 hi h83 h84) 𝔼 t0).Λ :=
    powDecay_Λ_of_outside P.β_pos h82 _ h83 h84 hout
  exact ⟨hst, fun H' => prop81M_unique _ H' hst⟩

/-! ### A root on `|μ| = β⁻¹`: the remark fails without the proviso -/

/-- Woodford (2003), (1.1)–(1.4) (the counterexample to the remark on p. 553): the system
`Prop81General.coinSys`, `E_t z_{t+1} = 2 z_t + i_t + c_t` (no predetermined variable; (1.15) is
`2 − μ`, its only root on `|μ| = β⁻¹`), with `β = 1/2`, target `τ = z`, `τ* = 1`, `W = 1`. -/
noncomputable def circleProblem : LQProblem Empty Unit Unit where
  sys := coinSys
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := Matrix.of fun _ _ => 1
  Ti := fun _ => 0
  W := 1
  τstar := fun _ => 1
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), (1.15) for the counterexample: `det(A − μÎ) = 2 − μ`. -/
theorem circle_pencil (μ : ℂ) : coinSys.pencilPoly.eval μ = 2 - μ := by
  rw [pencilPoly_eval]
  have he : coinSys.Ahat.map Complex.ofReal - μ • coinSys.Ihat.map Complex.ofReal =
      fromBlocks (-(μ • (1 : Matrix Empty Empty ℂ))) 0 0 (Matrix.of fun _ _ => 2 - μ) := by
    ext a b
    rcases a with e | u
    · exact e.elim
    · rcases b with e | v
      · exact e.elim
      · simp [coinSys, LinearRESystem.Ahat, LinearRESystem.Ihat]
  rw [he, det_fromBlocks_zero₂₁, Matrix.det_isEmpty, one_mul, Matrix.det_unique]
  rfl

/-- Woodford (2003), p. 553 (the counterexample): (1.15) has the single root `μ = 2 = β⁻¹`, so
it has exactly `n_Z = 0` roots with `|μ| < β⁻¹` (`stableCount β⁻¹ = 0`), and one root on
`|μ| = β⁻¹`. -/
theorem circle_roots : (∀ μ, coinSys.pencilPoly.eval μ = 0 ↔ μ = 2) ∧
    coinSys.stableCount (1 / 2 : ℝ)⁻¹ = 0 := by
  have hroot : ∀ μ, coinSys.pencilPoly.eval μ = 0 ↔ μ = 2 := fun μ => by
    rw [circle_pencil, sub_eq_zero, eq_comm]
  refine ⟨hroot, ?_⟩
  have hne : coinSys.pencilPoly ≠ 0 := fun h => by
    have := hroot 0
    rw [h, Polynomial.eval_zero] at this
    norm_num at this
  have hrank : coinSys.Ahat.rank = Fintype.card (Empty ⊕ Unit) := by
    refine rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr ?_)
    have hd : coinSys.Ahat = fromBlocks 0 0 0 (Matrix.of fun _ _ => (2 : ℝ)) := by
      ext a b
      rcases a with e | u
      · exact e.elim
      · rcases b with e | v
        · exact e.elim
        · rfl
    rw [hd, det_fromBlocks_zero₂₁, Matrix.det_isEmpty, one_mul, Matrix.det_unique]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  unfold LinearRESystem.stableCount
  rw [hrank, Nat.sub_self, zero_add, Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro μ hμ hμ'
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot, hroot] at hμ
  rw [hμ] at hμ'
  norm_num at hμ'

/-- Woodford (2003), (1.18) for the counterexample with the plan `y = 0` (bounded, adapted):
`2 M_t − 1 − 2 M_{t−1} = 0` (perfect foresight). -/
theorem circle_lhs118 (φ : ℕ → Unit → Empty ⊕ Unit → ℝ) (t : ℕ) :
    lhs118 circleProblem perfectForesight 0 φ t () (Sum.inr ()) =
      2 * φ (t + 1) () (Sum.inr ()) - 1 - 2 * φ t () (Sum.inr ()) := by
  simp [lhs118, circleProblem, coinSys, xproc, LinearRESystem.Ahat, LinearRESystem.Ihat, EV,
    mulVec, dotProduct, fromBlocks, perfectForesight, LQProblem.T]
  ring

/-- Woodford (2003), p. 553 (**the remark fails when a root lies on `|μ| = β⁻¹`**): in
`circleProblem` there are exactly `n_Z = 0` roots with `|μ| < β⁻¹` (`circle_roots`), yet for
the bounded plan `y = 0` **no** bounded multiplier process satisfies (1.18) (deterministic
case): (1.18) forces `M_t = M_{t−1} + 1/2`. -/
theorem circle_counterexample (φ : ℕ → Unit → Empty ⊕ Unit → ℝ)
    (h : Eq118 circleProblem perfectForesight 0 0 φ) : ¬ BoundedV φ := by
  have hstep : ∀ t, φ (t + 1) () (Sum.inr ()) = φ t () (Sum.inr ()) + 1 / 2 := by
    intro t
    have := congrFun (h t (Nat.zero_le t) ()) (Sum.inr ())
    change lhs118 circleProblem perfectForesight 0 φ t () (Sum.inr ()) = 0 at this
    rw [circle_lhs118] at this
    linarith
  have hlin : ∀ t : ℕ, φ t () (Sum.inr ()) = φ 0 () (Sum.inr ()) + t / 2 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hstep, ih]
      push_cast
      ring
  rintro ⟨K, hK⟩
  obtain ⟨t, ht⟩ := exists_nat_gt (2 * (K + |φ 0 () (Sum.inr ())|))
  have h1 := hK t () (Sum.inr ())
  rw [hlin] at h1
  have h2 := le_abs_self (φ 0 () (Sum.inr ()) + t / 2)
  have h3 := neg_abs_le (φ 0 () (Sum.inr ()))
  linarith

/-! ### Case (ii) of Assumption 8.2 -/

/-- Woodford (2003), App. G.1 (complex roots come in conjugate pairs, p. 716): the eigenvalues
of a real matrix are closed under conjugation. -/
theorem eig_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (Ψ : Matrix ι ι ℝ) {μ : ℂ}
    (h : (Matrix.scalar ι μ - Ψ.map Complex.ofReal).det = 0) :
    (Matrix.scalar ι (starRingEnd ℂ μ) - Ψ.map Complex.ofReal).det = 0 := by
  have e := (starRingEnd ℂ).map_det (Matrix.scalar ι μ - Ψ.map Complex.ofReal)
  rw [h, map_zero, RingHom.mapMatrix_apply] at e
  have hm : (Matrix.scalar ι μ - Ψ.map Complex.ofReal).map (starRingEnd ℂ) =
      Matrix.scalar ι (starRingEnd ℂ μ) - Ψ.map Complex.ofReal := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, hij]
  rw [hm] at e
  exact e.symm

/-- Woodford (2003), Assumption 8.2 (ii), p. 552: in case (ii) — a selected complex root `μ` whose
conjugate is not selected — `μ` is never an eigenvalue of the `Ψ` of a real deflating pair whose
eigenvalues are selected roots or zero (`RealSelection`). So no real invariant subspace carries
the unpaired root: the construction of `PencilEigen`/`Prop81General` covers case (i) only, and
case (ii) needs the different (real-part) construction of Giannoni–Woodford (2002a). -/
theorem realSelection_misses_unpaired {S : LinearRESystem ιZ ιz} {sel : Multiset ℂ}
    (R : RealSelection S sel) {μ : ℂ} (hμ0 : μ ≠ 0) (hconj : starRingEnd ℂ μ ∉ sel) :
    (Matrix.scalar ιZ μ - R.Ψ.map Complex.ofReal).det ≠ 0 := by
  intro h
  rcases R.eig _ (eig_conj R.Ψ h) with h0 | hm
  · exact hμ0 (by simpa using h0)
  · exact hconj hm

/-- Woodford (2003), Assumption 8.4 (ii), App. G.1, p. 718 (**not invariant for complex `Γ`**):
rescaling a complex left eigenvector by `c ≠ 0` preserves (G.6) and (i), but `det[Re Γ₂]` can be
made zero: for a nonzero `1 × 1` block `Γ₂ = γ`, `c = i γ̄` gives `Re(cγ) = 0`. In case (ii) of
Assumption 8.2, where `Γ` is necessarily complex, the condition is therefore not well-posed
without the (unstated) normalisation of Giannoni–Woodford (2002a). -/
theorem re_det_rescale_zero {ι : Type*} [Unique ι] (γ : Matrix ι ι ℂ) (hγ : γ.det ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ((c • γ).map Complex.re).det = 0 ∧
      ((starRingEnd ℂ (γ default default) • γ).map Complex.re).det ≠ 0 := by
  rw [Matrix.det_unique] at hγ
  refine ⟨Complex.I * starRingEnd ℂ (γ default default),
    mul_ne_zero Complex.I_ne_zero ((map_ne_zero _).mpr hγ), ?_, ?_⟩
  · rw [Matrix.det_unique]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  · rw [Matrix.det_unique]
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    have : (γ default default).re * (γ default default).re +
        (γ default default).im * (γ default default).im ≠ 0 := by
      intro h0
      apply hγ
      apply Complex.ext <;> simp <;> nlinarith [sq_nonneg (γ default default).re,
        sq_nonneg (γ default default).im]
    intro h
    apply this
    linarith

end Woodford.OptimalPolicyRules.Prop81Unique
