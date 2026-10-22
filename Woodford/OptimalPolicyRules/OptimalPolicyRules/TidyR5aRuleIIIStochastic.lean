/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InertiaRuleIII
import OptimalPolicyRules.InertiaProp82Complex
import OptimalPolicyRules.Prop83Links

/-!
# Rule III and the full stochastic Proposition 8.1

Woodford (2003), *Interest and Prices*, Chapter 8, Proposition 8.1 (p. 553), Proposition 8.2
(p. 555), and Rule III (3.24), p. 595, of the inflation-inertia model (§3.2).

`InertiaRuleIII.ruleIII_homEquiv` shows that Rule III's lag polynomial
`(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)` is `det(I − Λ'L)` for a matrix `Λ'` with the homogeneous content of
Proposition 8.1 (`Prop83.HomEquiv`). Here the same is proved at the **full stochastic level**:
there is a complete representation of the corrected Proposition 8.1 (`Prop81ConclusionM`: the
equivalence of (1.18) with (1.20)–(1.21) for all bounded adapted plans and bounded multipliers
with `M_t` known at `t`, under any expectation system) whose `Λ'` has Rule III's lag polynomial,
and commitment to its target criterion (1.23) is robustly optimal (Proposition 8.2).

## The modification, in general

If `(Λ − λ_bI)(Λ − λ₁I) = 0`, `λ₁ ≠ λ_b`, `|λ_b| > 1`, and `|ν| > 1`, put `N = Λ − λ₁I`,
`c = (ν − λ_b)/(λ_b − λ₁)`, `Λ' = Λ + cN`. Along a bounded solution of (1.20), `U_t = N M_{t−1}`
obeys `U_{t+1} = λ_bU_t + Nq_t`, so it is the bounded forward solution
`F_t = −∑_k λ_b^{−k−1} E_t N q_{t+k}` (`fwdN`); hence (1.20) with `Λ` is (1.20) with `Λ'` and
`q'_t = q_t − cE_tF_t` (`qMod`). Conversely, along (1.20) with `Λ'`, `w_t = U_t − F_t` satisfies
`E_tw_{t+1} = νw_t`, so `w = 0` because `|ν| > 1`.

* `Modify.eq120_modify`: (1.20) with `(Λ, q)` ⟺ (1.20) with `(Λ', q')`, for bounded adapted `q`
  and bounded multipliers with `M_t` known at `t`.
* `Modify.modify`, `Modify.modify_Λ`: **any** representation `H` of the corrected Proposition 8.1
  with such a `Λ` gives a representation with `Λ'` (same `Υ` and `R(L⁻¹)`, modified `Q(L⁻¹)`).

## Rule III

* `Inertia.in_Λ_struct`: for every representation of Proposition 8.1 of the inertia model (any
  `0 < γ ≤ 1` away from `S² = 4P₂₃`), `tr Λ = λ₁ + λ_b`, `det Λ = λ₁λ_b` with `|λ_b| > 1` (from
  Proposition 8.3, `InertiaSplit.in_prop83`, and the root `μ₁ = (βλ₁)⁻¹` of (1.15)).
* `Inertia.ruleIII_prop81M`: **for every `0 < γ ≤ 1` (real or complex roots) and every expectation
  system there is a representation of the corrected Proposition 8.1 with
  `α(L) = (1 − λ₁L)(1 − ½(λ₂ + λ₃)L)`, Rule III's lag polynomial.**
* `Inertia.ruleIII_assumption85`, `Inertia.ruleIII_prop82_B`: Assumption 8.5 holds for it and
  commitment to its target criterion (1.23) is robustly optimal (bounded initial conditions,
  pull-out).

So Rule III is excluded only by the requirement that `Λ` come from a deflating split
(`InertiaSplit.split_not_ruleIII`), not by Proposition 8.1 or 8.2.
-/

namespace Woodford.OptimalPolicyRules.TidyR5aRuleIIIStochastic

open Matrix Polynomial GeneralSetup GeneralFOC.LQ PencilSplit Prop81General Adjugate
open TargetCriterion.Prop81 (Eq118 Eq120 Eq121 xproc boundedV_xproc)

variable {Ω : Type*}

/-! ### Tools -/

namespace Modify

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), App. G.1 (tool): a scalar matrix `a I` with `|a| < 1` has geometrically
decaying powers. -/
theorem powDecay_smul_one {a : ℝ} (ha : |a| < 1) :
    PowDecay (a • (1 : Matrix ιz ιz ℝ)) := by
  refine ⟨1, |a|, abs_nonneg a, ha, fun k i j => ?_⟩
  rw [smul_pow, one_pow, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, abs_mul, abs_pow,
    one_mul]
  split_ifs
  · simp
  · simp [pow_nonneg (abs_nonneg a)]

/-- Woodford (2003), App. G.1 (tool): `(aI) v = a v`. -/
theorem smul_one_mulVec (a : ℝ) (v : ιz → ℝ) : (a • (1 : Matrix ιz ιz ℝ)) *ᵥ v = a • v := by
  rw [Matrix.smul_mulVec, one_mulVec]

/-- Woodford (2003), p. 553 (tool): the forward series of the zero process vanishes. -/
theorem fwdSum_zero (𝔼 : ExpectationSystem Ω) (G : Matrix ιz ιz ℝ) (t : ℕ) :
    fwdSum 𝔼 G (fun _ _ _ => 0) t = 0 := by
  funext ω i
  have e : ∀ s, EV 𝔼 s (fun (_ : Ω) (_ : ιz) => (0 : ℝ)) = fun _ _ => 0 :=
    fun s => PencilSplit.EV_const 𝔼 s (fun _ => 0)
  have h0 : ∀ k : ℕ, (G ^ k *ᵥ fun (_ : ιz) => (0 : ℝ)) i = 0 := fun k => by
    simp [mulVec, dotProduct]
  simp only [fwdSum, e, h0]
  exact tsum_zero

omit [Fintype ιz] [DecidableEq ιz] in
/-- Woodford (2003), p. 553 (tool): a known random vector is its own expectation. -/
theorem EV_known {𝔼 : ExpectationSystem Ω} {t : ℕ} {x : Ω → ιz → ℝ} (h : KnownV 𝔼 t x)
    (ω : Ω) : EV 𝔼 t x ω = x ω := by
  funext i
  exact congrFun (h i) ω

/-- Woodford (2003), App. G.1: the forward solution `F_t = ∑_k (λ_b⁻¹)^k E_t f_{t+k}` with
`f_t = −λ_b⁻¹ N q_t`, i.e. `F_t = −∑_k λ_b^{−k−1} E_t N q_{t+k}`: the bounded solution of
`U_t = λ_b⁻¹ E_tU_{t+1} − λ_b⁻¹ N q_t`. -/
noncomputable def fwdN (𝔼 : ExpectationSystem Ω) (N : Matrix ιz ιz ℝ) (lb : ℝ)
    (q : ℕ → Ω → ιz → ℝ) : ℕ → Ω → ιz → ℝ :=
  fwdSum 𝔼 (lb⁻¹ • (1 : Matrix ιz ιz ℝ)) (fun t ω => (-lb⁻¹) • (N *ᵥ q t ω))

/-- Woodford (2003), (1.20), p. 553: the modified forcing `q'_t = q_t − c E_t F_t`,
`c = (ν − λ_b)/(λ_b − λ₁)`. -/
noncomputable def qMod (𝔼 : ExpectationSystem Ω) (N : Matrix ιz ιz ℝ) (l1 lb ν : ℝ)
    (q : ℕ → Ω → ιz → ℝ) : ℕ → Ω → ιz → ℝ :=
  fun t ω => q t ω - ((ν - lb) / (lb - l1)) • EV 𝔼 t (fwdN 𝔼 N lb q t) ω

omit [DecidableEq ιz] in
/-- Woodford (2003), p. 553 (tool): the forcing `−λ_b⁻¹ N q_t` is bounded for bounded `q`. -/
theorem boundedV_fN (N : Matrix ιz ιz ℝ) (lb : ℝ) {q : ℕ → Ω → ιz → ℝ} (hq : BoundedV q) :
    BoundedV (fun t ω => (-lb⁻¹) • (N *ᵥ q t ω)) := by
  have h := PencilSplit.boundedV_mulVec ((-lb⁻¹) • N) hq
  convert h using 3 with t ω
  rw [Matrix.smul_mulVec]

/-- Woodford (2003), App. G.1: the properties of `F` (`fwdSum_spec`): the recursion
`F_t = λ_b⁻¹E_tF_{t+1} − λ_b⁻¹Nq_t`, adaptedness and boundedness. -/
theorem fwdN_spec (𝔼 : ExpectationSystem Ω) (N : Matrix ιz ιz ℝ) {lb : ℝ} (hb : 1 < |lb|)
    {q : ℕ → Ω → ιz → ℝ} (hqb : BoundedV q) (hqa : AdaptedV 𝔼 q) :
    (∀ t ω, fwdN 𝔼 N lb q t ω = lb⁻¹ • EV 𝔼 t (fwdN 𝔼 N lb q (t + 1)) ω -
        lb⁻¹ • (N *ᵥ q t ω)) ∧
      AdaptedV 𝔼 (fwdN 𝔼 N lb q) ∧ BoundedV (fwdN 𝔼 N lb q) := by
  have hG : PowDecay (lb⁻¹ • (1 : Matrix ιz ιz ℝ)) := by
    refine powDecay_smul_one ?_
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hb
  obtain ⟨hrec, ha, hbd⟩ := fwdSum_spec 𝔼 hG (boundedV_fN N lb hqb)
  refine ⟨fun t ω => ?_, ha, hbd⟩
  have hk : KnownV 𝔼 t (fun ω => (-lb⁻¹) • (N *ᵥ q t ω)) := by
    have := PencilSplit.knownV_mulVec 𝔼 ((-lb⁻¹) • N) (hqa t)
    convert this using 2 with ω
    rw [Matrix.smul_mulVec]
  have := hrec t ω
  rw [EV_known hk, smul_one_mulVec] at this
  change fwdN 𝔼 N lb q t ω = _ at this
  rw [this, neg_smul]
  rfl

/-- Woodford (2003), App. G.1 (tool): `N F_t = (λ_b − λ₁) F_t` when `N² = (λ_b − λ₁)N`: both are
bounded solutions of the same forward equation (`eq_fwdSum`). -/
theorem N_fwdN (𝔼 : ExpectationSystem Ω) {N : Matrix ιz ιz ℝ} {l1 lb : ℝ} (hb : 1 < |lb|)
    (hNN : N * N = (lb - l1) • N) {q : ℕ → Ω → ιz → ℝ} (hqb : BoundedV q)
    (hqa : AdaptedV 𝔼 q) (t : ℕ) (ω : Ω) :
    N *ᵥ fwdN 𝔼 N lb q t ω = (lb - l1) • fwdN 𝔼 N lb q t ω := by
  have hG : PowDecay (lb⁻¹ • (1 : Matrix ιz ιz ℝ)) := by
    refine powDecay_smul_one ?_
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hb
  obtain ⟨hrec, ha, hbd⟩ := fwdN_spec 𝔼 N hb hqb hqa
  set F := fwdN 𝔼 N lb q with hF
  set g : ℕ → Ω → ιz → ℝ := fun s ω => ((-lb⁻¹) * (lb - l1)) • (N *ᵥ q s ω) with hg
  have hgb : BoundedV g := by
    have h := PencilSplit.boundedV_mulVec ((-lb⁻¹ * (lb - l1)) • N) hqb
    convert h using 3 with s ω
    rw [Matrix.smul_mulVec]
  have hgk : ∀ s, 0 ≤ s → KnownV 𝔼 s (g s) := by
    intro s _
    have := PencilSplit.knownV_mulVec 𝔼 ((-lb⁻¹ * (lb - l1)) • N) (hqa s)
    convert this using 2 with ω
    rw [Matrix.smul_mulVec]
  have hNNq : ∀ v : ιz → ℝ, N *ᵥ (N *ᵥ v) = (lb - l1) • (N *ᵥ v) := by
    intro v
    rw [mulVec_mulVec, hNN, Matrix.smul_mulVec]
  have hA : ∀ s, 0 ≤ s → ∀ ω, N *ᵥ F s ω =
      (lb⁻¹ • (1 : Matrix ιz ιz ℝ)) *ᵥ EV 𝔼 s (fun ω => N *ᵥ F (s + 1) ω) ω + g s ω := by
    intro s _ ω
    rw [hrec s ω, EV_mulVec, smul_one_mulVec, mulVec_sub, mulVec_smul, mulVec_smul, hNNq]
    funext i
    simp only [hg, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hB : ∀ s, 0 ≤ s → ∀ ω, (lb - l1) • F s ω =
      (lb⁻¹ • (1 : Matrix ιz ιz ℝ)) *ᵥ EV 𝔼 s (fun ω => (lb - l1) • F (s + 1) ω) ω + g s ω := by
    intro s _ ω
    rw [hrec s ω, PencilSplit.EV_smul, smul_one_mulVec]
    funext i
    simp only [hg, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hAb : BoundedV (fun s ω => N *ᵥ F s ω) := PencilSplit.boundedV_mulVec N hbd
  have hBb : BoundedV (fun s ω => (lb - l1) • F s ω) := by
    have h := PencilSplit.boundedV_mulVec ((lb - l1) • (1 : Matrix ιz ιz ℝ)) hbd
    convert h using 3 with s ω
    rw [smul_one_mulVec]
  have e1 := eq_fwdSum 𝔼 hG hgb hAb hgk hA t (Nat.zero_le t)
  have e2 := eq_fwdSum 𝔼 hG hgb hBb hgk hB t (Nat.zero_le t)
  exact congrFun (e1.trans e2.symm) ω

/-! ### The modification of (1.20) -/

omit [Fintype ιZ] [DecidableEq ιZ] in
/-- **Woodford (2003), (1.20), p. 553: changing the unstable eigenvalue of `Λ`.** If
`(Λ − λ_bI)(Λ − λ₁I) = 0`, `λ₁ ≠ λ_b`, `|λ_b| > 1` and `|ν| > 1`, then for bounded adapted `q` and
bounded multipliers with `M_t` known at `t` (from `t₀` on), `M_t = ΛM_{t−1} + q_t` (`t ≥ t₀`) holds
iff `M_t = Λ'M_{t−1} + q'_t` does, with `Λ' = Λ + c(Λ − λ₁I)`, `c = (ν − λ_b)/(λ_b − λ₁)` and
`q' = qMod`. -/
theorem eq120_modify (𝔼 : ExpectationSystem Ω) (t0 : ℕ) {Λ : Matrix ιz ιz ℝ} {l1 lb ν : ℝ}
    (hmin : (Λ - lb • (1 : Matrix ιz ιz ℝ)) * (Λ - l1 • (1 : Matrix ιz ιz ℝ)) = 0)
    (h1b : l1 ≠ lb) (hb : 1 < |lb|) (hν : 1 < |ν|) {q : ℕ → Ω → ιz → ℝ} (hqb : BoundedV q)
    (hqa : AdaptedV 𝔼 q) {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hφb : BoundedV φ)
    (hφm : MultKnown 𝔼 t0 φ) :
    Eq120 t0 Λ q φ ↔
      Eq120 t0 (Λ + ((ν - lb) / (lb - l1)) • (Λ - l1 • (1 : Matrix ιz ιz ℝ)))
        (qMod 𝔼 (Λ - l1 • (1 : Matrix ιz ιz ℝ)) l1 lb ν q) φ := by
  set N := Λ - l1 • (1 : Matrix ιz ιz ℝ) with hN
  set cc := (ν - lb) / (lb - l1) with hcc
  have hsub : lb - l1 ≠ 0 := sub_ne_zero.mpr h1b.symm
  have hlb0 : lb ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hb
    linarith
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hν
    linarith
  have hΛN : Λ * N = lb • N := by
    have h := hmin
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, sub_eq_zero] at h
    exact h
  have hNΛ : N * Λ = lb • N := by
    have : N * Λ = Λ * N := by
      rw [hN, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
    rw [this, hΛN]
  have hNN : N * N = (lb - l1) • N := by
    calc N * N = Λ * N - l1 • N := by
          rw [hN, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = (lb - l1) • N := by rw [hΛN, sub_smul]
  have hcν : lb + cc * (lb - l1) = ν := by
    rw [hcc]
    field_simp
    ring
  obtain ⟨hrec, hFa, hFb⟩ := fwdN_spec 𝔼 N hb hqb hqa
  set F := fwdN 𝔼 N lb q with hF
  have hFk : ∀ t ω, EV 𝔼 t (F t) ω = F t ω := fun t ω => EV_known (hFa t) ω
  have hqM : ∀ t ω, qMod 𝔼 N l1 lb ν q t ω = q t ω - cc • F t ω := by
    intro t ω
    simp only [qMod, ← hF, hFk]
    rfl
  set U : ℕ → Ω → ιz → ℝ := fun t ω => N *ᵥ Mpart (φ t ω) with hU
  have hUk : ∀ t, t0 ≤ t → ∀ ω, EV 𝔼 t (U (t + 1)) ω = U (t + 1) ω := by
    intro t ht ω
    refine EV_known ?_ ω
    exact PencilSplit.knownV_mulVec 𝔼 N (hφm t ht)
  have hUb : BoundedV U := by
    have hM : BoundedV (fun t ω => Mpart (φ t ω)) := by
      obtain ⟨K, hK⟩ := hφb
      exact ⟨K, fun t ω r => hK t ω _⟩
    exact PencilSplit.boundedV_mulVec N hM
  have hG : PowDecay (lb⁻¹ • (1 : Matrix ιz ιz ℝ)) := by
    refine powDecay_smul_one ?_
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hb
  have hfk : ∀ t, t0 ≤ t → KnownV 𝔼 t (fun ω => (-lb⁻¹) • (N *ᵥ q t ω)) := by
    intro t _
    have := PencilSplit.knownV_mulVec 𝔼 ((-lb⁻¹) • N) (hqa t)
    convert this using 2 with ω
    rw [Matrix.smul_mulVec]
  constructor
  · intro h t ht ω
    -- `U` solves `U_t = λ_b⁻¹ E_tU_{t+1} − λ_b⁻¹ N q_t`, so `U = F`
    have hUrec : ∀ s, t0 ≤ s → ∀ ω, U s ω = (lb⁻¹ • (1 : Matrix ιz ιz ℝ)) *ᵥ
        EV 𝔼 s (U (s + 1)) ω + (-lb⁻¹) • (N *ᵥ q s ω) := by
      intro s hs ω
      rw [hUk s hs ω, smul_one_mulVec]
      have e : U (s + 1) ω = lb • U s ω + N *ᵥ q s ω := by
        simp only [hU]
        rw [h s hs ω, mulVec_add, mulVec_mulVec, hNΛ, Matrix.smul_mulVec]
      rw [e, smul_add, smul_smul, inv_mul_cancel₀ hlb0, one_smul, neg_smul]
      abel
    have hUF := eq_fwdSum 𝔼 hG (boundedV_fN N lb hqb) hUb hfk hUrec
    rw [h t ht ω, hqM, Matrix.add_mulVec, Matrix.smul_mulVec]
    have e2 : N *ᵥ Mpart (φ t ω) = F t ω := congrFun (hUF t ht) ω
    rw [e2]
    abel
  · intro h t ht ω
    have hNF : ∀ s ω, N *ᵥ F s ω = (lb - l1) • F s ω :=
      fun s ω => N_fwdN 𝔼 hb hNN hqb hqa s ω
    -- `w = U − F` satisfies `w_t = ν⁻¹ E_t w_{t+1}`, so `w = 0`
    set w : ℕ → Ω → ιz → ℝ := fun s ω => U s ω - F s ω with hw
    have hwrec : ∀ s, t0 ≤ s → ∀ ω, w s ω = (ν⁻¹ • (1 : Matrix ιz ιz ℝ)) *ᵥ
        EV 𝔼 s (w (s + 1)) ω + (fun _ _ _ => (0 : ℝ)) s ω := by
      intro s hs ω
      have eU : U (s + 1) ω = ν • U s ω + N *ᵥ q s ω - (cc * (lb - l1)) • F s ω := by
        simp only [hU]
        rw [h s hs ω, hqM, mulVec_add, mulVec_sub, mulVec_mulVec, Matrix.mul_add,
          Matrix.mul_smul, hNΛ, hNN, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
          mulVec_smul, hNF, ← hcν]
        funext i
        simp only [Matrix.smul_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      have eEF : EV 𝔼 s (F (s + 1)) ω = lb • F s ω + N *ᵥ q s ω := by
        rw [hrec s ω]
        funext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      have eEw : EV 𝔼 s (w (s + 1)) ω = ν • w s ω := by
        have e := PencilSplit.EV_sub 𝔼 s (U (s + 1)) (F (s + 1))
        have e' : EV 𝔼 s (w (s + 1)) ω = EV 𝔼 s (U (s + 1)) ω - EV 𝔼 s (F (s + 1)) ω :=
          congrFun e ω
        rw [e', hUk s hs ω, eU, eEF]
        have hc' : cc * (lb - l1) = ν - lb := by rw [← hcν]; ring
        rw [hc']
        funext i
        simp only [hw, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [eEw, smul_one_mulVec, smul_smul, inv_mul_cancel₀ hν0, one_smul]
      exact (add_zero (w s ω)).symm
    have hwb : BoundedV w := by
      obtain ⟨K1, hK1⟩ := hUb
      obtain ⟨K2, hK2⟩ := hFb
      refine ⟨K1 + K2, fun s ω i => ?_⟩
      simp only [hw, Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hK1 s ω i) (hK2 s ω i))
    have hGν : PowDecay (ν⁻¹ • (1 : Matrix ιz ιz ℝ)) := by
      refine powDecay_smul_one ?_
      rw [abs_inv]
      exact inv_lt_one_of_one_lt₀ hν
    have hw0 := eq_fwdSum 𝔼 hGν (f := fun _ _ _ => (0 : ℝ)) ⟨0, fun _ _ _ => by simp⟩ hwb
      (fun s _ i => 𝔼.const s 0) hwrec t ht
    rw [fwdSum_zero] at hw0
    have hUF : N *ᵥ Mpart (φ t ω) = F t ω := by
      have := congrFun hw0 ω
      simp only [hw, Pi.zero_apply] at this
      exact sub_eq_zero.mp this
    rw [h t ht ω, hqM, Matrix.add_mulVec, Matrix.smul_mulVec, hUF]
    abel

/-- **Woodford (2003), Proposition 8.1, p. 553: the modified representation.** Any
representation `H` of the corrected Proposition 8.1 whose `Λ` satisfies
`(Λ − λ_bI)(Λ − λ₁I) = 0` with `λ₁ ≠ λ_b`, `|λ_b| > 1` gives, for every `|ν| > 1`, a representation
with `Λ' = Λ + ((ν − λ_b)/(λ_b − λ₁))(Λ − λ₁I)`, the same `Υ` and `R(L⁻¹)`, and
`Q'(L⁻¹)x = qMod (Q(L⁻¹)x)`. -/
noncomputable def modify {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) {l1 lb ν : ℝ}
    (hmin : (H.Λ - lb • (1 : Matrix ιz ιz ℝ)) * (H.Λ - l1 • (1 : Matrix ιz ιz ℝ)) = 0)
    (h1b : l1 ≠ lb) (hb : 1 < |lb|) (hν : 1 < |ν|) : Prop81ConclusionM P 𝔼 t0 where
  Λ := H.Λ + ((ν - lb) / (lb - l1)) • (H.Λ - l1 • (1 : Matrix ιz ιz ℝ))
  Υ := H.Υ
  Qop := fun x => qMod 𝔼 (H.Λ - l1 • (1 : Matrix ιz ιz ℝ)) l1 lb ν (H.Qop x)
  Rop := H.Rop
  equiv := by
    intro y φ hyb hya hφb hφm
    rw [H.equiv y φ hyb hya hφb hφm,
      eq120_modify 𝔼 t0 hmin h1b hb hν (H.Qbounded _ (boundedV_xproc hyb)) (H.Qadapted _)
        hφb hφm]
  Qbounded := by
    intro x hx
    obtain ⟨-, -, hFb⟩ := fwdN_spec 𝔼 (H.Λ - l1 • (1 : Matrix ιz ιz ℝ)) hb (H.Qbounded x hx)
      (H.Qadapted x)
    obtain ⟨K1, hK1⟩ := H.Qbounded x hx
    obtain ⟨K2, hK2⟩ := hFb
    refine ⟨K1 + |(ν - lb) / (lb - l1)| * K2, fun t ω i => ?_⟩
    simp only [qMod, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h2 : |EV 𝔼 t (fwdN 𝔼 (H.Λ - l1 • (1 : Matrix ιz ιz ℝ)) lb (H.Qop x) t) ω i| ≤ K2 :=
      PencilSplit.abs_EV_le 𝔼 (fun ω' i' => hK2 t ω' i') t ω i
    refine (abs_sub _ _).trans (add_le_add (hK1 t ω i) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  Rbounded := H.Rbounded
  Qadapted := by
    intro x t i
    have h1 := H.Qadapted x t i
    have h2 := PencilSplit.knownV_EV 𝔼 t
      (fwdN 𝔼 (H.Λ - l1 • (1 : Matrix ιz ιz ℝ)) lb (H.Qop x) t) i
    change 𝔼.E t ((fun ω => H.Qop x t ω i) - ((ν - lb) / (lb - l1)) • fun ω =>
      EV 𝔼 t (fwdN 𝔼 (H.Λ - l1 • (1 : Matrix ιz ιz ℝ)) lb (H.Qop x) t) ω i) = _
    rw [map_sub, map_smul, h1, h2]
    rfl
  Radapted := H.Radapted

/-- Woodford (2003), Proposition 8.1, p. 553: the `Λ` of the modified representation. -/
theorem modify_Λ {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (H : Prop81ConclusionM P 𝔼 t0) {l1 lb ν : ℝ}
    (hmin : (H.Λ - lb • (1 : Matrix ιz ιz ℝ)) * (H.Λ - l1 • (1 : Matrix ιz ιz ℝ)) = 0)
    (h1b : l1 ≠ lb) (hb : 1 < |lb|) (hν : 1 < |ν|) :
    (modify H hmin h1b hb hν).Λ =
      H.Λ + ((ν - lb) / (lb - l1)) • (H.Λ - l1 • (1 : Matrix ιz ιz ℝ)) := rfl

end Modify

/-! ### Rule III for the inflation-inertia model -/

namespace Inertia

open IRuleBasic (Calib)
open CubicRoots
open GeneralLinksInertia (inSys inProblem in_det_ne)
open InertiaSplit (inJ inSplit standing_of muj)

variable (c : Calib) (γ : ℝ)

/-- Woodford (2003), Rule III (3.24), p. 595: its lag polynomial
`(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)` (`½(λ₂ + λ₃) = S/2`). -/
noncomputable def ruleIIIpoly : ℝ[X] :=
  (1 - Polynomial.C (lam1 c.β γ c.κ c.σ) * X) *
    (1 - Polynomial.C (sumS c.β γ c.κ c.σ / 2) * X)

/-- Woodford (2003), (1.20) for the inertia model: for every `J` with `K` invertible,
`Λ₁₀ ≠ 0` (`Λ = β⁻¹K⁻¹Ẽ'`, the second row of `K` is `(−κ, 1)`). -/
theorem in_Λ10_ne_zero (hc : c.Adm) (hγ : 0 ≤ γ) (J : Matrix (Unit ⊕ Fin 2) Unit ℝ)
    (hK : (Kmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)) J).det ≠ 0) :
    Λmat (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ)) c.β J 1 0 ≠ 0 := by
  set S := inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ) with hS
  set K := Kmat S J with hKdef
  have hβ : c.β ≠ 0 := hc.1.ne'
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.mpr hK
  set L := K⁻¹ * S.Etᵀ with hL
  have hKL : K * L = S.Etᵀ := by rw [hL, mul_nonsing_inv_cancel_left _ _ hKu]
  have hK10 : K 1 0 = -c.κ := by
    simp [hKdef, Kmat, hS, inSys, Matrix.add_apply, Matrix.mul_apply]
  have hK11 : K 1 1 = 1 := by
    simp [hKdef, Kmat, hS, inSys, Matrix.add_apply, Matrix.mul_apply]
  have e10 : -c.κ * L 0 0 + L 1 0 = 0 := by
    have := congrFun (congrFun hKL 1) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, hK10, hK11] at this
    simpa [hS, inSys] using this
  have e00 : K 0 0 * L 0 0 + K 0 1 * L 1 0 = c.β := by
    have := congrFun (congrFun hKL 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two] at this
    simpa [hS, inSys] using this
  have hdetK : K.det = K 0 0 + c.κ * K 0 1 := by
    rw [det_fin_two, hK10, hK11]
    ring
  have hL00 : L 0 0 ≠ 0 := by
    intro h0
    have : K.det * L 0 0 = c.β := by rw [hdetK]; linear_combination e00 - K 0 1 * e10
    rw [h0, mul_zero] at this
    exact hβ this.symm
  rw [Λmat, ← hL, Matrix.smul_apply, smul_eq_mul]
  refine mul_ne_zero (inv_ne_zero hβ) ?_
  have : L 1 0 = c.κ * L 0 0 := by linarith
  rw [this]
  exact mul_ne_zero hc.2.2.2.1.ne' hL00

/-- **Woodford (2003), Propositions 8.1 and 8.3 for the inertia model: the eigenvalues of every
`Λ`.** For every representation of the corrected Proposition 8.1 (here under perfect foresight;
`Λ` does not depend on the expectation system in the constructions used below), away from
`S² = 4P₂₃`, `tr Λ = λ₁ + λ_b` and `det Λ = λ₁λ_b` with `|λ_b| > 1`: `λ₁` is an eigenvalue because
`(βλ₁)⁻¹` is a root of (1.15) outside `|μ| = β⁻¹` (`Prop83.charpoly_root_of_pencil_root`), and
`α(L)` has exactly one zero inside the unit circle (`InertiaSplit.in_prop83`). -/
theorem in_Λ_struct (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hD : discQ c.β γ c.κ c.σ ≠ 0)
    (H : Prop81ConclusionM (inProblem c γ hc hγ0.le) perfectForesight 0) :
    ∃ lb : ℝ, H.Λ.trace = lam1 c.β γ c.κ c.σ + lb ∧ H.Λ.det = lam1 c.β γ c.κ c.σ * lb ∧
      1 < |lb| := by
  have h := standing_of c γ hc hγ0 hγ1
  obtain ⟨hl1p, hl1lt, -⟩ := lam1_spec h
  set l1 := lam1 c.β γ c.κ c.σ with hl1
  obtain ⟨hyb, hya, hφb, hφm, h118⟩ := Prop83Links.const_base (inProblem c γ hc hγ0.le)
    perfectForesight 0 _ (InertiaSplit.in_xvec_base c γ hc hγ0.le)
  have hE := Prop83.homEquiv_of_perturbation h118
    (Prop83Links.hequiv_of_prop81M H hyb hya hφb hφm)
  -- `λ₁` is an eigenvalue of `Λ`
  have hl0 : muj c (l1 : ℂ) ≠ 0 :=
    InertiaSplit.muj_ne_zero c γ h (by exact_mod_cast hl1p.ne')
  have hdet : (Prop83.cmat (inProblem c γ hc hγ0.le).sys.Ahat -
      muj c (l1 : ℂ) • Prop83.cmat (inProblem c γ hc hγ0.le).sys.Ihat).det = 0 := by
    have e := PencilSplit.pencilPoly_eval (inSys c γ hc.2.2.1.ne' (in_det_ne c γ hc hγ0.le))
      (muj c (l1 : ℂ))
    rw [InertiaSplit.in_pencilPoly c γ h] at e
    simp only [eval_mul, eval_sub, eval_X, eval_C, ← hl1, sub_self, mul_zero, zero_mul] at e
    exact e.symm
  have hnorm : (inProblem c γ hc hγ0.le).β⁻¹ ≤ ‖muj c (l1 : ℂ)‖ :=
    (InertiaSplit.in_root_norms c γ h).1.le
  have hroot := Prop83.charpoly_root_of_pencil_root hE hc.1 hl0 hdet hnorm
  have hinv : (((inProblem c γ hc hγ0.le).β : ℂ) * muj c (l1 : ℂ))⁻¹ = (l1 : ℂ) := by
    change ((c.β : ℂ) * ((c.β : ℂ) * (l1 : ℂ))⁻¹)⁻¹ = (l1 : ℂ)
    have hβc : (c.β : ℂ) ≠ 0 := by exact_mod_cast hc.1.ne'
    have hlc : (l1 : ℂ) ≠ 0 := by exact_mod_cast hl1p.ne'
    field_simp
  rw [hinv] at hroot
  have htrC : (Prop83.cmat H.Λ).trace = (H.Λ.trace : ℂ) := by
    simp [trace_fin_two, Prop83.cmat]
  have hdetC : (Prop83.cmat H.Λ).det = (H.Λ.det : ℂ) := by
    simp [det_fin_two, Prop83.cmat]
  rw [charpoly_fin_two, htrC, hdetC] at hroot
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hroot
  have hq : l1 ^ 2 - H.Λ.trace * l1 + H.Λ.det = 0 := by exact_mod_cast hroot
  set lb := H.Λ.trace - l1 with hlb
  have htr : H.Λ.trace = l1 + lb := by rw [hlb]; ring
  have hdt : H.Λ.det = l1 * lb := by rw [hlb]; linear_combination hq
  refine ⟨lb, htr, hdt, ?_⟩
  -- `|λ_b| > 1` from Proposition 8.3
  obtain ⟨hin, -⟩ := InertiaSplit.in_prop83 c γ hc hγ0 hγ1 hD perfectForesight 0 H
  rw [Prop83.zerosInside_alpha] at hin
  have hcp : (Prop83.cmat H.Λ).charpoly =
      (X - Polynomial.C (l1 : ℂ)) * (X - Polynomial.C (lb : ℂ)) := by
    rw [charpoly_fin_two, htrC, hdetC, htr, hdt]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Polynomial.C_add, Polynomial.C_mul]
    ring
  rw [hcp, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
    roots_X_sub_C] at hin
  have hl1n : ¬ 1 < ‖(l1 : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hl1p.le]
    exact not_lt.mpr hl1lt.le
  by_contra hlb1
  have hlbn : ¬ 1 < ‖(lb : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hlb1
  rw [Multiset.filter_add, Multiset.filter_singleton, Multiset.filter_singleton] at hin
  simp only [hl1n, hlbn, ↓reduceIte] at hin
  exact absurd hin (by norm_num)

/-- Woodford (2003), Rule III (3.24) and Proposition 8.1 (tool): a representation whose `Λ` has
`tr Λ = λ₁ + λ_b`, `det Λ = λ₁λ_b`, `|λ_b| > 1`, `Λ₁₀ ≠ 0` gives one with Rule III's lag
polynomial, `Λ'₁₀ ≠ 0` and `det Λ' = λ₁S/2`. -/
theorem ruleIII_of_rep (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (H : Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0) {lb : ℝ}
    (htr : H.Λ.trace = lam1 c.β γ c.κ c.σ + lb) (hdet : H.Λ.det = lam1 c.β γ c.κ c.σ * lb)
    (hb : 1 < |lb|) (h10 : H.Λ 1 0 ≠ 0) :
    ∃ H' : Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0, H'.Υ = H.Υ ∧ H'.Rop = H.Rop ∧
      alpha H'.Λ = ruleIIIpoly c γ ∧ H'.Λ 1 0 ≠ 0 ∧
      H'.Λ.det = lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ / 2) := by
  have h := standing_of c γ hc hγ0 hγ1
  obtain ⟨hl1p, hl1lt, -⟩ := lam1_spec h
  set l1 := lam1 c.β γ c.κ c.σ with hl1
  set ν := sumS c.β γ c.κ c.σ / 2 with hνdef
  have hS := two_lt_sumS h
  have hν : 1 < |ν| := by rw [abs_of_pos (by linarith)]; linarith
  have h1b : l1 ≠ lb := by
    intro e
    rw [← e, abs_of_pos hl1p] at hb
    linarith
  have hmin := InertiaRuleIII.cayley_two H.Λ htr hdet
  refine ⟨Modify.modify H hmin h1b hb hν, rfl, rfl, ?_, ?_, ?_⟩
  · rw [Modify.modify_Λ]
    exact InertiaRuleIII.alpha_modify H.Λ htr hdet h1b
  · rw [Modify.modify_Λ]
    have hsub : lb - l1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h1b)
    have h1c : 1 + (ν - lb) / (lb - l1) ≠ 0 := by
      rw [show 1 + (ν - lb) / (lb - l1) = (ν - l1) / (lb - l1) by field_simp; ring]
      exact div_ne_zero (by linarith) hsub
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply_ne
      (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul, mul_zero, sub_zero]
    rw [show H.Λ 1 0 + (ν - lb) / (lb - l1) * H.Λ 1 0 = (1 + (ν - lb) / (lb - l1)) * H.Λ 1 0 by
      ring]
    exact mul_ne_zero h1c h10
  · have hα := InertiaRuleIII.alpha_modify (ν := ν) H.Λ htr hdet h1b
    rw [← Modify.modify_Λ H hmin h1b hb hν, InertiaSplit.alpha_fin_two] at hα
    have e : (1 - Polynomial.C l1 * X) * (1 - Polynomial.C ν * X) =
        1 - Polynomial.C (l1 + ν) * X + Polynomial.C (l1 * ν) * X ^ 2 := by
      simp only [Polynomial.C_add, Polynomial.C_mul]
      ring
    rw [e] at hα
    have := congrArg (fun p : ℝ[X] => p.coeff 2) hα
    simp only [coeff_add, coeff_sub, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow] at this
    norm_num at this
    linear_combination this

/-- **Woodford (2003), Rule III (3.24), p. 595, and Proposition 8.1, p. 553, at the full
stochastic level.** For every `0 < γ ≤ 1` (three real roots, the double root, or a complex pair)
and every expectation system, there is a representation of the corrected Proposition 8.1 for the
inflation-inertia model (`Prop81ConclusionM`: (1.18) ⟺ (1.20)–(1.21) for all bounded adapted
plans and bounded multipliers with `M_t` known at `t`) whose lag polynomial
`α(L) = det(I − ΛL)` is Rule III's `(1 − λ₁L)(1 − ½(λ₂ + λ₃)L)`. It is the modification
(`Modify.modify`) of the Rule I split (real case) or of the case-(ii) construction (complex
case). -/
theorem ruleIII_prop81M (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) :
    ∃ H : Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0,
      alpha H.Λ = ruleIIIpoly c γ ∧ H.Λ 1 0 ≠ 0 ∧
        H.Λ.det = lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ / 2) := by
  have h := standing_of c γ hc hγ0 hγ1
  have hσ : c.σ ≠ 0 := hc.2.2.1.ne'
  have hd := in_det_ne c γ hc hγ0.le
  rcases le_or_gt 0 (discQ c.β γ c.κ c.σ) with hD | hD
  · -- the Rule I split solving `λ₃` forward: eigenvalues `λ₁, λ₂`
    have hq := InertiaSplit.quadQ_lam3r hD
    obtain ⟨hp, h1, h0, -⟩ := InertiaSplit.mu_facts c γ h hq
    have hls : lam3r c.β γ c.κ c.σ ≠ 0 := by linarith [one_lt_lam3r h]
    have hb : sumS c.β γ c.κ c.σ - lam3r c.β γ c.κ c.σ = lam2r c.β γ c.κ c.σ := by
      rw [← InertiaSplit.lam2r_add_lam3r]
      ring
    have htr := InertiaSplit.in_Λ_trace c γ hσ hd hc.1.ne' hγ0.ne' hp h1 h0
    rw [InertiaSplit.tr_eq c γ h hls hp, hb] at htr
    have hdet := InertiaSplit.in_Λ_det c γ hσ hd hc.1.ne' hγ0.ne' hp h1 h0
    rw [InertiaSplit.det_eq c γ h hls hq, hb] at hdet
    have h2 := one_lt_lam2r h
    have hK := (inSplit c γ hc hγ0 hγ1 hq).K_det
    obtain ⟨H', -, -, hα, h10, hdt⟩ := ruleIII_of_rep c γ hc hγ0 hγ1
      (Prop81General.prop81 _ (inSplit c γ hc hγ0 hγ1 hq) 𝔼 t0) htr hdet
      (by rw [abs_of_pos (by linarith)]; exact h2) (in_Λ10_ne_zero c γ hc hγ0.le _ hK)
    exact ⟨H', hα, h10, hdt⟩
  · -- the case-(ii) construction
    set Q := InertiaProp82Complex.inQ c γ hc hγ0 hγ1 hD with hQ
    obtain ⟨lb, htr, hdet, hb⟩ := in_Λ_struct c γ hc hγ0 hγ1 hD.ne
      (Prop81CaseII.prop81II _ Q perfectForesight 0)
    obtain ⟨H', -, -, hα, h10, hdt⟩ := ruleIII_of_rep c γ hc hγ0 hγ1
      (Prop81CaseII.prop81II _ Q 𝔼 t0) htr hdet hb
      (in_Λ10_ne_zero c γ hc hγ0.le _ Q.K_det)
    exact ⟨H', hα, h10, hdt⟩

/-- **Woodford (2003), Assumption 8.5, App. G.2, p. 719, for a representation with Rule III's
lag polynomial** (`InertiaProp8182.assumption85_two`: `B₂ = (0, σ)`, `Λ₁₀ ≠ 0`, `det Λ ≠ 0`). -/
theorem ruleIII_assumption85 (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {Λ : Matrix (Fin 2) (Fin 2) ℝ}
    (h10 : Λ 1 0 ≠ 0) (hdet : Λ.det = lam1 c.β γ c.κ c.σ * (sumS c.β γ c.κ c.σ / 2)) :
    PencilAssumptions.Assumption85 Λ (inProblem c γ hc hγ0.le).sys.B2 := by
  have h := standing_of c γ hc hγ0 hγ1
  have hS := two_lt_sumS h
  refine InertiaProp8182.assumption85_two hc.2.2.1.ne' h10 ?_
  rw [hdet]
  exact mul_ne_zero (lam1_spec h).1.ne' (by linarith)

/-- **Woodford (2003), Proposition 8.2, p. 555, for Rule III, at the full stochastic level, with
bounded initial conditions.** For every `0 < γ ≤ 1` and every expectation system with pull-out
there is a representation of the corrected Proposition 8.1 with Rule III's lag polynomial such
that, for every window `D ≥ 2` and every consistent bounded history, commitment to its target
criterion (1.23) determines a unique bounded equilibrium, optimal from a timeless perspective,
for every bounded adapted disturbance and every bounded initial condition (Assumption 8.1:
`InertiaAssumption81.in_assumption81MB`; Assumption 8.5: `Inertia.ruleIII_assumption85`). -/
theorem ruleIII_prop82_B (hc : c.Adm) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (hpull : 𝔼.PullOut) :
    ∃ H : Prop81ConclusionM (inProblem c γ hc hγ0.le) 𝔼 t0, alpha H.Λ = ruleIIIpoly c γ ∧
      ∀ D, D + 1 ≤ t0 → 2 ≤ D → ∀ (Mh qh : ℕ → Ω → Fin 2 → ℝ) (vh : ℕ → Ω → ℝ),
        TargetCriterion.Prop82.HistoryOK H.Λ (inProblem c γ hc hγ0.le).sys.B2 t0 D Mh qh vh →
        BoundedV Mh → AdaptedV 𝔼 Mh → BoundedV qh → (∃ K, ∀ t ω, |vh t ω| ≤ K) →
        InertiaAssumption81.RobustlyOptimalB (κ := Fin 2) (inProblem c γ hc hγ0.le) 𝔼 t0
          (fun _ y => Prop82General.Prop82M.CriterionM H D qh vh y)
          (fun _ y t ω => zpart (y t ω)) := by
  obtain ⟨H, hα, h10, hdet⟩ := ruleIII_prop81M c γ hc hγ0 hγ1 𝔼 t0
  refine ⟨H, hα, fun D hD1 hD2 Mh qh vh hhist hMhb hMhk hqhb hvhb => ?_⟩
  have hrk : H.Λ.rank ≤ D := (rank_le_width H.Λ).trans hD2
  exact InertiaAssumption81.prop82M_robustlyOptimalB hpull
    (InertiaAssumption81.in_assumption81MB c γ hc hγ0 hγ1 𝔼 t0) H
    (ruleIII_assumption85 c γ hc hγ0 hγ1 h10 hdet).2 hD1
    (fun i j => (Adjugate.natDegree_Bpoly_le_rank _ i j).trans hrk)
    ((Adjugate.natDegree_alpha_le_rank _).trans hrk) hhist hMhb hMhk hqhb hvhb

end Inertia

end Woodford.OptimalPolicyRules.TidyR5aRuleIIIStochastic
