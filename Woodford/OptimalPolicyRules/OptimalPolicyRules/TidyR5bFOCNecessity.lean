/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralFOC
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection

/-!
# Necessity of the first-order conditions in the general LQ problem

Woodford (2003), *Interest and Prices*, Chapter 8, §1.1 (pp. 538–543): the first-order
conditions (1.9), the initial-multiplier restatement (1.10)–(1.12) of optimality from a timeless
perspective.

The book asserts without proof that every optimal plan satisfies the first-order conditions (1.9)
for some initial multipliers `M_{t₀−1}`; `GeneralFOC.LQ.timeless_restated` proves the direction
"original ⇒ restated" only under an attainability hypothesis. This module proves necessity under
the project's hypotheses — Assumption 8.1 (existence half, `FOCSolvable`), the pull-out property
and faithful expectations — for an arbitrary expectation system.

## The argument (a variational argument with deterministic perturbations)

* **Deterministic responses** (`HomResp`, `exists_homResp`): from the solutions of (1.1) + (1.9)
  with data `(0, 0, e_j)` and `(0, 0, 0)` the date-`t₀` forecast path of their difference is a
  bounded *deterministic* solution of the homogeneous system with `M_{t₀−1} = e_j`. Collected as
  the columns of matrices `H_t`, `Φ_t`.
* **Affine family** (`combo`): for any bounded `M` known at `t₀`, `y⁰ + H M`, `φ⁰ + Φ M` solves
  (1.1) + (1.9) with initial multipliers `M`, and its `Ẽ z_{t₀}` is `e⁰ + L M` with the constant
  matrix `L = Ẽ (H_{t₀})_z` (Woodford's `e_M` of (1.10)).
* **The variational inequality** (`lagrangian_gap_init`): the Lagrangian identity with a nonzero
  initial multiplier term, `J(y) − J(y^M) = ∑ βᵏ E ½(T d)'W(T d) + β⁻¹ M'(ē − e(M))`. For `M = s w`
  with `L'w = 0` this gives `β⁻¹ s w'(ē − e⁰) ≤ J(y)` for every real `s`, so `w'(ē − e⁰) = 0`:
  the constraint value `ē` of an optimal plan lies in `e⁰ + range L` (`mem_range_of_orth`).
* **Necessity** (`foc_necessary`): with a fixed right inverse `R` of `L` on its range
  (`exists_rightInv`), `M₀ = R(ē − e⁰)` is bounded and known at `t₀`, the FOC plan `y^{M₀}` has
  `Ẽ z_{t₀} = ē`, and strict convexity (`GeneralFOC.LQ.targets_eq_of_optimal`) gives
  `T y = T y^{M₀}`; the FOC involve the plan only through `T y`, so `y` itself satisfies (1.9)
  with the multipliers of `y^{M₀}`.

## Main results

* `foc_necessary`: every plan optimal subject to `Ẽ z_{t₀} = ē` satisfies (1.1) + (1.9) with some
  bounded initial multipliers known at `t₀`.
* `t0Optimal_foc_necessary`: every `t₀`-optimal plan satisfies (1.9) with `M_{t₀−1} = 0`.
* `timeless_restated_unconditional`: the direction "original ⇒ restated" of (1.11)–(1.12) without
  the attainability hypothesis of `GeneralFOC.LQ.timeless_restated`.
* `restated_of_affine`, `affine_of_restated`: the initial multipliers can be taken of the form
  (1.11) `g⁰ + G X̄_{t₀}` exactly when the zero-multiplier value `e(c, Z, 0)` of (1.10) is affine
  in `X̄_{t₀}`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bFOCNecessity

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationTools (Faithful)

variable {Ω : Type*}

/-! ### Conditional expectations of random vectors -/

/-- Woodford (2003), p. 540: `E_t` of a sum of random vectors. -/
theorem EV_add (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (a b : Ω → ι → ℝ) :
    EV 𝔼 t (fun ω => a ω + b ω) = fun ω => EV 𝔼 t a ω + EV 𝔼 t b ω := by
  funext ω i
  exact congrFun (map_add (𝔼.E t) (fun ω' => a ω' i) (fun ω' => b ω' i)) ω

/-- Woodford (2003), p. 540: a sum of random vectors known at `t` is known at `t`. -/
theorem knownV_add {𝔼 : ExpectationSystem Ω} {ι : Type*} {t : ℕ} {a b : Ω → ι → ℝ}
    (ha : KnownV 𝔼 t a) (hb : KnownV 𝔼 t b) : KnownV 𝔼 t (fun ω => a ω + b ω) := fun i => by
  have h : (fun ω => (a ω + b ω) i) = (fun ω => a ω i) + fun ω => b ω i := rfl
  rw [h, map_add, ha i, hb i]

/-- Woodford (2003), p. 540: a difference of random vectors known at `t` is known at `t`. -/
theorem knownV_sub {𝔼 : ExpectationSystem Ω} {ι : Type*} {t : ℕ} {a b : Ω → ι → ℝ}
    (ha : KnownV 𝔼 t a) (hb : KnownV 𝔼 t b) : KnownV 𝔼 t (fun ω => a ω - b ω) := fun i => by
  have h : (fun ω => (a ω - b ω) i) = (fun ω => a ω i) - fun ω => b ω i := rfl
  rw [h, map_sub, ha i, hb i]

/-- Woodford (2003), p. 540: a constant matrix times a random vector known at `t` is known at
`t`. -/
theorem knownV_mulVec {𝔼 : ExpectationSystem Ω} {ι κ : Type*} [Fintype ι] {t : ℕ}
    (A : Matrix κ ι ℝ) {a : Ω → ι → ℝ} (ha : KnownV 𝔼 t a) :
    KnownV 𝔼 t (fun ω => A *ᵥ a ω) := by
  intro k
  have h := EV_mulVec 𝔼 t A a
  rw [EV_of_known 𝔼 ha] at h
  funext ω
  have := congrFun (congrFun h ω) k
  simpa [EV] using this

/-- Woodford (2003), p. 540: a constant random vector is known at every date. -/
theorem knownV_const (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (v : ι → ℝ) :
    KnownV 𝔼 t (fun _ => v) := fun i => 𝔼.const t (v i)

/-- Woodford (2003), fn 6, p. 539: a matrix with bounded entries maps bounded vectors to bounded
vectors. -/
theorem abs_mulVec_le {ι κ : Type*} [Fintype ι] {A : Matrix κ ι ℝ} {KA Kv : ℝ}
    (hA : ∀ k i, |A k i| ≤ KA) {v : ι → ℝ} (hv : ∀ i, |v i| ≤ Kv) (k : κ) :
    |(A *ᵥ v) k| ≤ Fintype.card ι * (KA * Kv) :=
  abs_dotProduct_le (hA k) hv

/-! ### Linear algebra: the range of a matrix and a right inverse on it -/

/-- Woodford (2003), (1.10), p. 542 (linear algebra): a vector orthogonal to `ker L'` lies in the
range of `L`. -/
theorem mem_range_of_orth {n : Type*} [Fintype n] (L : Matrix n n ℝ)
    (d : n → ℝ) (h : ∀ w, Lᵀ *ᵥ w = 0 → w ⬝ᵥ d = 0) : d ∈ LinearMap.range L.mulVecLin := by
  classical
  by_contra hd
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hd inferInstance
  set w : n → ℝ := fun i => f (fun j => if i = j then 1 else 0) with hw
  have hfv : ∀ v, f v = w ⬝ᵥ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hzero : ∀ v ∈ LinearMap.range L.mulVecLin, f v = 0 := by
    intro v hv
    have : f v ∈ (LinearMap.range L.mulVecLin).map f := Submodule.mem_map_of_mem hv
    rw [hmap] at this
    exact this
  have hLw : Lᵀ *ᵥ w = 0 := by
    funext j
    have h1 := hzero (L *ᵥ Pi.single j 1) ⟨Pi.single j 1, rfl⟩
    rw [hfv, mulVec_single_one] at h1
    rw [Pi.zero_apply, ← h1]
    simp [mulVec, dotProduct, Matrix.col, mul_comm]
  exact hf (by rw [hfv]; exact h w hLw)

/-- Woodford (2003), (1.10), p. 542 (linear algebra): a fixed matrix `R` with `L R v = v` for
every `v` in the range of `L`. -/
theorem exists_rightInv {n : Type*} [Fintype n] (L : Matrix n n ℝ) :
    ∃ R : Matrix n n ℝ, ∀ v ∈ LinearMap.range L.mulVecLin, L *ᵥ (R *ᵥ v) = v := by
  classical
  set g := L.mulVecLin with hg
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (LinearMap.range g)
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  refine ⟨LinearMap.toMatrix' (s ∘ₗ Submodule.projectionOnto _ q hq), fun v hv => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, LinearMap.comp_apply,
    Submodule.projectionOnto_apply_of_mem_left hq hv]
  have := congrArg Subtype.val (LinearMap.congr_fun hs ⟨v, hv⟩)
  simpa [hg] using this

/-! ### The Lagrangian identity with an initial multiplier term -/

/-- Woodford (2003), p. 541 and survey §4.4: **the Lagrangian identity with a nonzero initial
term.** Under the hypotheses of `GeneralFOC.lagrangian_gap` but without `φ_{t₀}'Ĩ(y_{t₀} −
y*_{t₀}) = 0`, `J(y) − J(y*) − β⁻¹ E_{t₀}[φ_{t₀}'Ĩ(y_{t₀} − y*_{t₀})]` is the genuine infinite sum
`∑_k βᵏ E_{t₀} ½ (T d)'W(T d)`, `d = y − y*`. -/
theorem lagrangian_gap_init {ρ₁ ρ₂ ν ιτ : Type*} [Fintype ιτ] [Fintype ν] [Fintype ρ₁]
    [Fintype ρ₂] {𝔼 : ExpectationSystem Ω} (hpull : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) {Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ} {Tm : Matrix ιτ ν ℝ}
    {W : Matrix ιτ ιτ ℝ} (hW : Wᵀ = W) {τs : ιτ → ℝ} {cf : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ} {t0 : ℕ}
    {y ys : ℕ → Ω → ν → ℝ} {φ : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ}
    (hy : ConstraintsHold 𝔼 Atil Itil cf t0 y) (hys : ConstraintsHold 𝔼 Atil Itil cf t0 ys)
    (hay : AdaptedV 𝔼 y) (hays : AdaptedV 𝔼 ys) (hby : BoundedV y) (hbys : BoundedV ys)
    (hbφ : BoundedV φ) (hmφ : MultiplierMeas 𝔼 φ) (hfoc : FOC 𝔼 Atil Itil Tm W τs β t0 ys φ)
    (ω : Ω) :
    HasSum (fun k => β ^ k *
        𝔼.E t0 (fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω)
      (Jfn 𝔼 β Tm W τs t0 y ω - Jfn 𝔼 β Tm W τs t0 ys ω -
        β⁻¹ * 𝔼.E t0 (fun ω' => φ t0 ω' ⬝ᵥ (Itil *ᵥ (y t0 ω' - ys t0 ω'))) ω) := by
  obtain ⟨My, hMy⟩ := hby
  obtain ⟨Mys, hMys⟩ := hbys
  obtain ⟨Mφ, hMφ⟩ := hbφ
  obtain ⟨Ky, hKy⟩ := exists_bound_lossFn Tm W τs My
  obtain ⟨Kys, hKys⟩ := exists_bound_lossFn Tm W τs Mys
  have hJ : ∀ (z : ℕ → Ω → ν → ℝ) (K : ℝ), (∀ t ω, |lossFn Tm W τs (z t ω)| ≤ K) →
      HasSum (fun k => β ^ k * 𝔼.E t0 (fun ω' => lossFn Tm W τs (z (t0 + k) ω')) ω)
        (Jfn 𝔼 β Tm W τs t0 z ω) := by
    intro z K hK
    have hb : ∀ k ω, |β ^ k * lossFn Tm W τs (z (t0 + k) ω)| ≤ β ^ k * K := fun k ω => by
      rw [abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (hK _ _) (pow_pos hβ0 k).le
    have hEt := 𝔼.E_tsum hβ0.le hβ1 hb t0 ω
    have hterm : ∀ k, 𝔼.E t0 (fun ω' => β ^ k * lossFn Tm W τs (z (t0 + k) ω')) ω =
        β ^ k * 𝔼.E t0 (fun ω' => lossFn Tm W τs (z (t0 + k) ω')) ω := by
      intro k
      have : (fun ω' => β ^ k * lossFn Tm W τs (z (t0 + k) ω')) =
          β ^ k • fun ω' => lossFn Tm W τs (z (t0 + k) ω') := rfl
      rw [this, map_smul]
      rfl
    have hsumm : Summable (fun k => β ^ k *
        𝔼.E t0 (fun ω' => lossFn Tm W τs (z (t0 + k) ω')) ω) := by
      refine Summable.of_norm_bounded
        ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K) (fun k => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => hK _ ω') t0 ω) (pow_pos hβ0 k).le
    unfold Jfn
    rw [hEt]
    simp_rw [hterm]
    exact hsumm.hasSum
  have hJy := hJ y Ky (fun t ω' => hKy _ (hMy t ω'))
  have hJys := hJ ys Kys (fun t ω' => hKys _ (hMys t ω'))
  set a : ℕ → Ω → ℝ := fun s ω' => φ s ω' ⬝ᵥ (Itil *ᵥ (y s ω' - ys s ω')) with ha
  set e : ℕ → ℝ := fun s => 𝔼.E t0 (a s) ω with he
  obtain ⟨KI, hKI⟩ := exists_bound_mulVec Itil (My + Mys)
  have hab : ∀ s ω', |a s ω'| ≤ Fintype.card (ρ₁ ⊕ ρ₂) * (Mφ * KI) := by
    intro s ω'
    have hd : ∀ i, |(y s ω' - ys s ω') i| ≤ My + Mys := fun i =>
      (abs_sub _ _).trans (add_le_add (hMy s ω' i) (hMys s ω' i))
    exact abs_dotProduct_le (hMφ s ω') (hKI _ hd)
  have heb : ∀ k, |e (t0 + k)| ≤ Fintype.card (ρ₁ ⊕ ρ₂) * (Mφ * KI) := fun k =>
    𝔼.abs_E_le (hab (t0 + k)) t0 ω
  have hkey : ∀ k, β ^ k * 𝔼.E t0 (fun ω' => lossFn Tm W τs (y (t0 + k) ω')) ω -
      β ^ k * 𝔼.E t0 (fun ω' => lossFn Tm W τs (ys (t0 + k) ω')) ω -
      β ^ k * (β⁻¹ * e (t0 + k) - e (t0 + (k + 1))) =
      β ^ k * 𝔼.E t0 (fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω := by
    intro k
    have ht : t0 ≤ t0 + k := Nat.le_add_right _ _
    have hpt : (fun ω' => lossFn Tm W τs (y (t0 + k) ω')) =
        (fun ω' => lossFn Tm W τs (ys (t0 + k) ω')) +
          (fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) + β⁻¹ • a (t0 + k) -
          fun ω' => EV 𝔼 (t0 + k) (φ (t0 + k + 1)) ω' ⬝ᵥ
            (Atil *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω')) := by
      funext ω'
      have := lossFn_sub_of_foc hW (hfoc (t0 + k) ht ω') (y (t0 + k) ω')
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
      linarith
    have hnext := E_next_multiplier_term hpull hy hys hay hays hmφ ht
    have hE : 𝔼.E t0 (fun ω' => EV 𝔼 (t0 + k) (φ (t0 + k + 1)) ω' ⬝ᵥ
        (Atil *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) = 𝔼.E t0 (a (t0 + (k + 1))) := by
      rw [← hnext, 𝔼.tower ht]
      rfl
    have h1 := congrFun (congrArg (𝔼.E t0) hpt) ω
    rw [map_sub, map_add, map_add, map_smul, hE] at h1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [he]
    rw [h1]
    ring
  have htel := hasSum_telescope hβ0 hβ1 (e := fun k => e (t0 + k)) heb
  simp only [Nat.add_zero] at htel
  have hfin := (hJy.sub hJys).sub htel
  refine hfin.congr_fun ?_
  intro k
  exact (hkey k).symm

/-- Woodford (2003), (1.2)–(1.3): the discounted expected loss is nonnegative (`W ⪰ 0`). -/
theorem Jfn_nonneg {ν ιτ : Type*} [Fintype ιτ] [Fintype ν] (𝔼 : ExpectationSystem Ω) {β : ℝ}
    (hβ0 : 0 ≤ β) {Tm : Matrix ιτ ν ℝ} {W : Matrix ιτ ιτ ℝ} (hW : W.PosSemidef) (τs : ιτ → ℝ)
    (t0 : ℕ) (y : ℕ → Ω → ν → ℝ) (ω : Ω) : 0 ≤ Jfn 𝔼 β Tm W τs t0 y ω := by
  have hnn : (0 : Ω → ℝ) ≤ fun ω' => ∑' k, β ^ k * lossFn Tm W τs (y (t0 + k) ω') :=
    fun ω' => tsum_nonneg fun k => mul_nonneg (pow_nonneg hβ0 k) (quad_nonneg hW _)
  have := 𝔼.mono t0 hnn ω
  rw [map_zero] at this
  exact this

/-! ### Deterministic responses to the initial multipliers -/

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), (1.10), p. 542: **deterministic responses to the initial multipliers.**
The columns `j` of `H_t` (plan) and `Φ_t` (multipliers) form a bounded deterministic solution of
the homogeneous (1.1) + (1.9) — no disturbance, no `τ*` — from `t₀`, with `Z_{t₀} = 0` and
`M_{t₀−1} = e_j`. -/
def HomResp (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) (H : ℕ → Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ)
    (Φ : ℕ → Matrix (ιZ ⊕ ιz) ιz ℝ) : Prop :=
  (∀ t, t0 ≤ t → P.sys.Itil * H (t + 1) = P.sys.Atil * H t) ∧
    (∀ t, t0 ≤ t → P.sys.Atilᵀ * Φ (t + 1) + P.Tᵀ * (P.W * (P.T * H t)) -
      P.β⁻¹ • (P.sys.Itilᵀ * Φ t) = 0) ∧
    (∀ r j, H t0 (Sum.inl (Sum.inl r)) j = 0) ∧
    (∀ r j, Φ t0 (Sum.inr r) j = (1 : Matrix ιz ιz ℝ) r j) ∧
    (∃ K, ∀ t v j, |H t v j| ≤ K) ∧ (∃ K, ∀ t r j, |Φ t r j| ≤ K)

/-- Woodford (2003), (1.10): the forecast at `ω₀` of a random vector. -/
noncomputable def fcV (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (ω0 : Ω) {ι : Type*}
    (x : Ω → ι → ℝ) : ι → ℝ :=
  EV 𝔼 t0 x ω0

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): the forecast commutes with a constant matrix. -/
theorem fcV_mulVec (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (ω0 : Ω) {ι κ : Type*} [Fintype ι]
    (A : Matrix κ ι ℝ) (x : Ω → ι → ℝ) : fcV 𝔼 t0 ω0 (fun ω => A *ᵥ x ω) = A *ᵥ fcV 𝔼 t0 ω0 x :=
  congrFun (EV_mulVec 𝔼 t0 A x) ω0

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): the forecast of a sum. -/
theorem fcV_add (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (ω0 : Ω) {ι : Type*} (a b : Ω → ι → ℝ) :
    fcV 𝔼 t0 ω0 (fun ω => a ω + b ω) = fcV 𝔼 t0 ω0 a + fcV 𝔼 t0 ω0 b :=
  congrFun (EV_add 𝔼 t0 a b) ω0

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): the forecast of a difference. -/
theorem fcV_sub (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (ω0 : Ω) {ι : Type*} (a b : Ω → ι → ℝ) :
    fcV 𝔼 t0 ω0 (fun ω => a ω - b ω) = fcV 𝔼 t0 ω0 a - fcV 𝔼 t0 ω0 b := by
  funext i
  simp only [fcV, EV, Pi.sub_apply]
  have h : (fun ω' => a ω' i - b ω' i) = (fun ω' => a ω' i) - fun ω' => b ω' i := rfl
  rw [h, map_sub]
  rfl

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): the forecast of a constant vector is the vector. -/
theorem fcV_const (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (ω0 : Ω) {ι : Type*} (v : ι → ℝ) :
    fcV 𝔼 t0 ω0 (fun _ => v) = v := by
  funext i
  simp only [fcV, EV, 𝔼.const]

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10) (law of iterated expectations): `E_{t₀}(E_t x) = E_{t₀} x` for
`t ≥ t₀`. -/
theorem fcV_EV (𝔼 : ExpectationSystem Ω) {t0 t : ℕ} (ht : t0 ≤ t) (ω0 : Ω) {ι : Type*}
    (x : Ω → ι → ℝ) : fcV 𝔼 t0 ω0 (EV 𝔼 t x) = fcV 𝔼 t0 ω0 x := by
  funext i
  simp only [fcV, EV]
  exact congrFun (𝔼.tower ht (fun ω => x ω i)) ω0

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): the forecast of a bounded random vector is bounded. -/
theorem abs_fcV_le (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (ω0 : Ω) {ι : Type*} {x : Ω → ι → ℝ}
    {K : ℝ} (hx : ∀ ω i, |x ω i| ≤ K) (i : ι) : |fcV 𝔼 t0 ω0 x i| ≤ K :=
  𝔼.abs_E_le (fun ω => hx ω i) t0 ω0

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): the forecast of a scalar multiple. -/
theorem fcV_smul (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (ω0 : Ω) {ι : Type*} (a : ℝ)
    (x : Ω → ι → ℝ) : fcV 𝔼 t0 ω0 (fun ω => a • x ω) = a • fcV 𝔼 t0 ω0 x := by
  funext i
  simp only [fcV, EV, Pi.smul_apply, smul_eq_mul]
  have h : (fun ω' => a * x ω' i) = a • fun ω' => x ω' i := rfl
  rw [h, map_smul]
  rfl

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540: `E_t` of a difference of random vectors. -/
theorem EV_sub (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (a b : Ω → ι → ℝ) :
    EV 𝔼 t (fun ω => a ω - b ω) = fun ω => EV 𝔼 t a ω - EV 𝔼 t b ω := by
  funext ω i
  exact congrFun (map_sub (𝔼.E t) (fun ω' => a ω' i) (fun ω' => b ω' i)) ω

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): a matrix whose columns are given vectors, multiplied on the left. -/
theorem mul_of_cols {a b c : Type*} [Fintype b] (A : Matrix a b ℝ) (h : c → b → ℝ) :
    A * Matrix.of (fun v j => h j v) = Matrix.of fun i j => (A *ᵥ h j) i := by
  ext i j
  simp [Matrix.mul_apply, mulVec, dotProduct]

/-- Woodford (2003), (1.10), p. 542: **deterministic responses exist** (Assumption 8.1, existence
half, on a nonempty sample space): the date-`t₀` forecast path of the difference of the solutions
with data `(0, 0, e_j)` and `(0, 0, 0)` is a bounded deterministic homogeneous solution with
`M_{t₀−1} = e_j`. -/
theorem exists_homResp [Nonempty Ω] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (hsolv : FOCSolvable P 𝔼 t0) : ∃ H Φ, HomResp P t0 H Φ := by
  set ω0 : Ω := Classical.arbitrary Ω
  have hc0b : BoundedV (fun (_ : ℕ) (_ : Ω) (_ : ιz) => (0 : ℝ)) := ⟨0, fun _ _ _ => by simp⟩
  have hc0a : AdaptedV 𝔼 (fun (_ : ℕ) (_ : Ω) (_ : ιz) => (0 : ℝ)) := fun t i => 𝔼.const t 0
  have hZk : KnownV 𝔼 t0 (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) := fun i => 𝔼.const t0 0
  have hMk : ∀ v : ιz → ℝ, KnownV 𝔼 t0 (fun (_ : Ω) => v) := fun v i => 𝔼.const t0 (v i)
  choose yj φj hj using fun j : ιz =>
    hsolv _ _ (fun _ => (1 : Matrix ιz ιz ℝ) j) hc0b hc0a hZk (hMk _)
  obtain ⟨y0, φ0, h0⟩ := hsolv _ _ (fun _ => (0 : ιz → ℝ)) hc0b hc0a hZk (hMk 0)
  set hv : ℕ → ιz → (ιZ ⊕ ιz) ⊕ Unit → ℝ :=
    fun t j => fcV 𝔼 t0 ω0 (fun ω => yj j t ω - y0 t ω) with hhv
  set pv : ℕ → ιz → ιZ ⊕ ιz → ℝ :=
    fun t j => fcV 𝔼 t0 ω0 (fun ω => φj j t ω - φ0 t ω) with hpv
  -- the constraints, column by column
  have hcon : ∀ t, t0 ≤ t → ∀ j, P.sys.Itil *ᵥ hv (t + 1) j = P.sys.Atil *ᵥ hv t j := by
    intro t ht j
    have hsj := (structural_iff P.sys 𝔼 _ t0 (yj j)).mp (hj j).1.1 t ht
    have hs0 := (structural_iff P.sys 𝔼 _ t0 y0).mp h0.1.1 t ht
    simp only [hhv]
    rw [← fcV_mulVec, ← fcV_mulVec]
    funext a
    simp only [fcV, EV]
    rcases a with r | r
    · refine congrArg (fun f => 𝔼.E t0 f ω0) (funext fun ω => ?_)
      have a1 := (hsj ω).1 r
      have a2 := (hs0 ω).1 r
      simp only [mulVec_sub, Pi.sub_apply, liftDist, Sum.elim_inl, Pi.zero_apply] at a1 a2 ⊢
      linarith
    · rw [← congrFun (𝔼.tower ht (fun ω => (P.sys.Itil *ᵥ (yj j (t + 1) ω - y0 (t + 1) ω))
        (Sum.inr r))) ω0]
      refine congrArg (fun f => 𝔼.E t0 f ω0) (funext fun ω => ?_)
      have a1 := (hsj ω).2 r
      have a2 := (hs0 ω).2 r
      simp only [EV, liftDist, Sum.elim_inr] at a1 a2
      have e : (fun ω' => (P.sys.Itil *ᵥ (yj j (t + 1) ω' - y0 (t + 1) ω')) (Sum.inr r)) =
          (fun ω' => (P.sys.Itil *ᵥ yj j (t + 1) ω') (Sum.inr r)) -
            fun ω' => (P.sys.Itil *ᵥ y0 (t + 1) ω') (Sum.inr r) := by
        funext ω'
        simp [mulVec_sub]
      rw [e, map_sub, Pi.sub_apply, a1, a2, mulVec_sub, Pi.sub_apply]
      ring
  -- the first-order conditions, column by column
  have hfoc : ∀ t, t0 ≤ t → ∀ j, P.sys.Atilᵀ *ᵥ pv (t + 1) j +
      P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ hv t j)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ pv t j) = 0 := by
    intro t ht j
    have hG : (fun ω => P.sys.Atilᵀ *ᵥ EV 𝔼 t (fun ω' => φj j (t + 1) ω' - φ0 (t + 1) ω') ω +
        P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ (yj j t ω - y0 t ω))) -
        P.β⁻¹ • (P.sys.Itilᵀ *ᵥ (φj j t ω - φ0 t ω))) = fun _ => 0 := by
      funext ω
      have f1 := (hj j).2.2.2.2 t ht ω
      have f0 := h0.2.2.2.2 t ht ω
      rw [EV_sub]
      simp only [mulVec_sub, smul_sub]
      rw [← sub_eq_zero.mpr (f1.trans f0.symm)]
      simp only [mulVec_sub]
      abel
    have e := congrArg (fcV 𝔼 t0 ω0) hG
    rw [fcV_const, fcV_sub, fcV_add, fcV_mulVec, fcV_mulVec, fcV_EV 𝔼 ht, fcV_mulVec,
      fcV_mulVec, fcV_smul, fcV_mulVec] at e
    exact e
  -- bounds
  choose Kj hKj using fun j => (hj j).1.2.2.1
  choose Lj hLj using fun j => (hj j).2.1
  obtain ⟨K0, hK0⟩ := h0.1.2.2.1
  obtain ⟨L0, hL0⟩ := h0.2.1
  refine ⟨fun t => Matrix.of fun v j => hv t j v, fun t => Matrix.of fun r j => pv t j r,
    ⟨fun t ht => ?_, fun t ht => ?_, fun r j => ?_, fun r j => ?_,
      ⟨∑ j, |Kj j| + |K0|, fun t v j => ?_⟩, ⟨∑ j, |Lj j| + |L0|, fun t r j => ?_⟩⟩⟩
  · change P.sys.Itil * Matrix.of (fun v j => hv (t + 1) j v) =
      P.sys.Atil * Matrix.of (fun v j => hv t j v)
    rw [mul_of_cols, mul_of_cols]
    ext a j
    simp only [of_apply]
    rw [hcon t ht j]
  · change P.sys.Atilᵀ * Matrix.of (fun r j => pv (t + 1) j r) +
      P.Tᵀ * (P.W * (P.T * Matrix.of (fun v j => hv t j v))) -
      P.β⁻¹ • (P.sys.Itilᵀ * Matrix.of (fun r j => pv t j r)) = 0
    simp only [mul_of_cols]
    ext a j
    have := congrFun (hfoc t ht j) a
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply] at this
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
      of_apply]
    exact this
  · simp only [of_apply, hhv, fcV, EV]
    have e : (fun ω => (yj j t0 ω - y0 t0 ω) (Sum.inl (Sum.inl r))) = fun _ => (0 : ℝ) := by
      funext ω
      have a1 := congrFun ((hj j).1.2.1 ω) r
      have a2 := congrFun (h0.1.2.1 ω) r
      simp only [Zpart] at a1 a2
      simp [a1, a2]
    rw [e, 𝔼.const]
  · simp only [of_apply, hpv, fcV, EV]
    have e : (fun ω => (φj j t0 ω - φ0 t0 ω) (Sum.inr r)) =
        fun _ => (1 : Matrix ιz ιz ℝ) r j := by
      funext ω
      have a1 := congrFun ((hj j).2.2.2.1 ω) r
      have a2 := congrFun (h0.2.2.2.1 ω) r
      simp only [Mpart] at a1 a2
      simp only [Pi.sub_apply, a1, a2, Pi.zero_apply, sub_zero]
      by_cases hrj : r = j
      · subst hrj; simp
      · simp [Matrix.one_apply_ne hrj, Matrix.one_apply_ne (Ne.symm hrj)]
    rw [e, 𝔼.const]
  · simp only [of_apply]
    refine (abs_fcV_le 𝔼 t0 ω0 (K := |Kj j| + |K0|) (fun ω i => ?_) v).trans ?_
    · exact (abs_sub _ _).trans (add_le_add ((hKj j t ω i).trans (le_abs_self _))
        ((hK0 t ω i).trans (le_abs_self _)))
    · have : |Kj j| ≤ ∑ j, |Kj j| :=
        Finset.single_le_sum (f := fun j => |Kj j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
      linarith
  · simp only [of_apply]
    refine (abs_fcV_le 𝔼 t0 ω0 (K := |Lj j| + |L0|) (fun ω i => ?_) r).trans ?_
    · exact (abs_sub _ _).trans (add_le_add ((hLj j t ω i).trans (le_abs_self _))
        ((hL0 t ω i).trans (le_abs_self _)))
    · have : |Lj j| ≤ ∑ j, |Lj j| :=
        Finset.single_le_sum (f := fun j => |Lj j|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)
      linarith

/-! ### The affine family of first-order-condition plans -/

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): the plan (or multipliers) `x⁰_t + H_t M` from `t₀` on (and `x⁰_t`
before `t₀`). -/
noncomputable def comboF (t0 : ℕ) {ι : Type*} (x0 : ℕ → Ω → ι → ℝ) (H : ℕ → Matrix ι ιz ℝ)
    (M : Ω → ιz → ℝ) : ℕ → Ω → ι → ℝ :=
  fun t ω => x0 t ω + if t0 ≤ t then H t *ᵥ M ω else 0

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): `comboF` from `t₀` on. -/
theorem comboF_of_le {t0 t : ℕ} (ht : t0 ≤ t) {ι : Type*} (x0 : ℕ → Ω → ι → ℝ)
    (H : ℕ → Matrix ι ιz ℝ) (M : Ω → ιz → ℝ) (ω : Ω) :
    comboF t0 x0 H M t ω = x0 t ω + H t *ᵥ M ω := by
  simp only [comboF, ht, ↓reduceIte]

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): `comboF` before `t₀`. -/
theorem comboF_of_lt {t0 t : ℕ} (ht : t < t0) {ι : Type*} (x0 : ℕ → Ω → ι → ℝ)
    (H : ℕ → Matrix ι ιz ℝ) (M : Ω → ιz → ℝ) (ω : Ω) : comboF t0 x0 H M t ω = x0 t ω := by
  simp only [comboF, show ¬ t0 ≤ t by omega, ↓reduceIte, add_zero]

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 6: `comboF` of bounded data is bounded. -/
theorem comboF_bounded (t0 : ℕ) {ι : Type*} {x0 : ℕ → Ω → ι → ℝ} (hx : BoundedV x0)
    {H : ℕ → Matrix ι ιz ℝ} (hH : ∃ K, ∀ t v j, |H t v j| ≤ K) {M : Ω → ιz → ℝ}
    (hM : ∃ K, ∀ ω r, |M ω r| ≤ K) : BoundedV (comboF t0 x0 H M) := by
  obtain ⟨Kx, hKx⟩ := hx
  obtain ⟨KH, hKH⟩ := hH
  obtain ⟨KM, hKM⟩ := hM
  have hb : ∀ t ω v, |(H t *ᵥ M ω) v| ≤ Fintype.card ιz * (|KH| * |KM|) := fun t ω v =>
    abs_mulVec_le (fun k i => (hKH t k i).trans (le_abs_self _))
      (fun i => (hKM ω i).trans (le_abs_self _)) v
  have h0 : (0 : ℝ) ≤ Fintype.card ιz * (|KH| * |KM|) := by positivity
  refine ⟨Kx + Fintype.card ιz * (|KH| * |KM|), fun t ω v => ?_⟩
  by_cases ht : t0 ≤ t
  · rw [comboF_of_le ht, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hKx t ω v) (hb t ω v))
  · rw [comboF_of_lt (by omega)]
    linarith [hKx t ω v]

/-- Woodford (2003), (1.10), p. 542: **the affine family.** If `(y⁰, φ⁰)` solves (1.1) + (1.9)
with `M_{t₀−1} = 0` and `(H, Φ)` are deterministic responses, then for every bounded `M` known
at `t₀` (and at `t₀ − 1`, where the multiplier `M_{t₀−1}` is required to be known), the plan
`y⁰ + H M` with multipliers `φ⁰ + Φ M` solves (1.1) + (1.9) with `M_{t₀−1} = M`. -/
theorem combo {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ}
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h0 : FOCSystem P 𝔼 c t0 Z0 0 y0 φ0)
    {H : ℕ → Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ} {Φ : ℕ → Matrix (ιZ ⊕ ιz) ιz ℝ}
    (hH : HomResp P t0 H Φ) {M : Ω → ιz → ℝ} (hMk : KnownV 𝔼 t0 M)
    (hMk' : KnownV 𝔼 (t0 - 1) M) (hMb : ∃ K, ∀ ω r, |M ω r| ≤ K) :
    FOCSystem P 𝔼 c t0 Z0 M (comboF t0 y0 H M) (comboF t0 φ0 Φ M) := by
  obtain ⟨⟨hs0, hZ0, hb0, ha0⟩, hbφ0, hm0, hM0, hf0⟩ := h0
  obtain ⟨hHc, hHf, hHZ, hHM, hHb, hΦb⟩ := hH
  have hMt : ∀ t, t0 ≤ t → KnownV 𝔼 t M := fun t ht => KnownV.mono 𝔼 ht hMk
  refine ⟨⟨?_, fun ω => ?_, comboF_bounded t0 hb0 hHb hMb, fun t => ?_⟩,
    comboF_bounded t0 hbφ0 hΦb hMb, fun t r => ?_, fun ω => ?_, fun t ht ω => ?_⟩
  · -- the constraints
    rw [structural_iff]
    have hs := (structural_iff P.sys 𝔼 c t0 y0).mp hs0
    intro t ht ω
    obtain ⟨a1, a2⟩ := hs t ht ω
    have hItH : ∀ ω', P.sys.Itil *ᵥ (H (t + 1) *ᵥ M ω') = P.sys.Atil *ᵥ (H t *ᵥ M ω') := by
      intro ω'
      rw [mulVec_mulVec, mulVec_mulVec, hHc t ht]
    refine ⟨fun r => ?_, fun r => ?_⟩
    · rw [comboF_of_le (by omega), comboF_of_le ht, mulVec_add, mulVec_add, hItH, Pi.add_apply,
        Pi.add_apply, a1 r]
      ring
    · have hk : KnownV 𝔼 t (fun ω' => P.sys.Itil *ᵥ (H (t + 1) *ᵥ M ω')) := by
        have e : (fun ω' => P.sys.Itil *ᵥ (H (t + 1) *ᵥ M ω')) =
            fun ω' => (P.sys.Itil * H (t + 1)) *ᵥ M ω' := funext fun _ => mulVec_mulVec _ _ _
        rw [e]
        exact knownV_mulVec _ (hMt t ht)
      have e : (fun ω' => P.sys.Itil *ᵥ comboF t0 y0 H M (t + 1) ω') =
          fun ω' => P.sys.Itil *ᵥ y0 (t + 1) ω' + P.sys.Itil *ᵥ (H (t + 1) *ᵥ M ω') := by
        funext ω'
        rw [comboF_of_le (by omega), mulVec_add]
      rw [e, EV_add, EV_of_known 𝔼 hk]
      beta_reduce
      rw [Pi.add_apply, a2 r, comboF_of_le ht, mulVec_add, hItH, Pi.add_apply]
      ring
  · -- the initial predetermined variables
    rw [comboF_of_le le_rfl, ← hZ0 ω]
    funext r
    simp only [Zpart, Pi.add_apply, add_eq_left]
    simp [mulVec, dotProduct, hHZ]
  · -- adaptedness of the plan
    by_cases ht : t0 ≤ t
    · have e : comboF t0 y0 H M t = fun ω => y0 t ω + H t *ᵥ M ω :=
        funext fun ω => comboF_of_le ht _ _ _ _
      rw [e]
      exact knownV_add (ha0 t) (knownV_mulVec _ (hMt t ht))
    · have e : comboF t0 y0 H M t = y0 t := funext fun ω => comboF_of_lt (by omega) _ _ _ _
      rw [e]
      exact ha0 t
  · -- the multipliers `M_t` are known at `t`
    by_cases ht : t0 ≤ t + 1
    · have hk : KnownV 𝔼 t M := by
        by_cases ht' : t0 ≤ t
        · exact hMt t ht'
        · have : t = t0 - 1 := by omega
          rw [this]
          exact hMk'
      have e : (fun ω => comboF t0 φ0 Φ M (t + 1) ω (Sum.inr r)) =
          (fun ω => φ0 (t + 1) ω (Sum.inr r)) + fun ω => (Φ (t + 1) *ᵥ M ω) (Sum.inr r) := by
        funext ω
        rw [comboF_of_le ht]
        rfl
      rw [e, map_add, hm0 t r, knownV_mulVec (Φ (t + 1)) hk (Sum.inr r)]
    · have e : (fun ω => comboF t0 φ0 Φ M (t + 1) ω (Sum.inr r)) =
          fun ω => φ0 (t + 1) ω (Sum.inr r) := by
        funext ω
        rw [comboF_of_lt (by omega)]
      rw [e, hm0 t r]
  · -- the initial multipliers
    rw [comboF_of_le le_rfl]
    funext r
    have h1 := congrFun (hM0 ω) r
    simp only [Mpart, Pi.add_apply] at h1 ⊢
    rw [h1]
    simp only [Pi.zero_apply, zero_add]
    simp only [mulVec, dotProduct, hHM]
    simp [Matrix.one_apply]
  · -- the first-order conditions
    have hk : KnownV 𝔼 t (fun ω' => Φ (t + 1) *ᵥ M ω') := knownV_mulVec _ (hMt t ht)
    have e : comboF t0 φ0 Φ M (t + 1) = fun ω' => φ0 (t + 1) ω' + Φ (t + 1) *ᵥ M ω' :=
      funext fun ω' => comboF_of_le (by omega) _ _ _ _
    have hEV : EV 𝔼 t (comboF t0 φ0 Φ M (t + 1)) ω = EV 𝔼 t (φ0 (t + 1)) ω +
        Φ (t + 1) *ᵥ M ω := by
      rw [e, EV_add, EV_of_known 𝔼 hk]
    have hf := hf0 t ht ω
    have hhom := congrArg (· *ᵥ M ω) (hHf t ht)
    simp only [add_mulVec, sub_mulVec, smul_mulVec, zero_mulVec, ← mulVec_mulVec] at hhom
    change P.sys.Atilᵀ *ᵥ EV 𝔼 t (comboF t0 φ0 Φ M (t + 1)) ω +
      P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ comboF t0 y0 H M t ω - P.τstar)) -
      P.β⁻¹ • (P.sys.Itilᵀ *ᵥ comboF t0 φ0 Φ M t ω) = 0
    change P.sys.Atilᵀ *ᵥ EV 𝔼 t (φ0 (t + 1)) ω +
      P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y0 t ω - P.τstar)) - P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φ0 t ω) = 0 at hf
    rw [hEV, comboF_of_le ht, comboF_of_le ht]
    simp only [mulVec_add, mulVec_sub, smul_add] at hf hhom ⊢
    linear_combination (norm := module) hf + hhom

/-! ### The response matrix `L = e_M` of (1.10) -/

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), (1.10): the forward-looking rows of a response matrix. -/
def zrows (H0 : Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ) : Matrix ιz ιz ℝ :=
  Matrix.of fun r j => H0 (Sum.inl (Sum.inr r)) j

/-- Woodford (2003), (1.10), p. 542: the matrix `e_M = Ẽ (H_{t₀})_z` of the response of `Ẽ z_{t₀}`
to the initial multipliers. -/
def Lmat (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) (H : ℕ → Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ) :
    Matrix ιz ιz ℝ :=
  P.sys.Et * zrows (H t0)

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), (1.10), p. 542: along the affine family,
`Ẽ z_{t₀} = Ẽ z⁰_{t₀} + e_M M`. -/
theorem eq110_combo (P : LQProblem ιZ ιz ιτ) (t0 : ℕ) (y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ)
    (H : ℕ → Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ) (M : Ω → ιz → ℝ) (ω : Ω) :
    P.sys.Et *ᵥ zpart (comboF t0 y0 H M t0 ω) =
      P.sys.Et *ᵥ zpart (y0 t0 ω) + Lmat P t0 H *ᵥ M ω := by
  rw [comboF_of_le le_rfl, Lmat, ← mulVec_mulVec]
  have e : zpart (y0 t0 ω + H t0 *ᵥ M ω) = zpart (y0 t0 ω) + zrows (H t0) *ᵥ M ω := by
    funext r
    simp [zpart, zrows, mulVec, dotProduct]
  rw [e, mulVec_add]

/-! ### Necessity of the first-order conditions -/

omit [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), p. 539: the predetermined initial condition of a feasible plan is known at
`t₀`. -/
theorem knownV_Z0 {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ}
    {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.Feasible 𝔼 c t0 Z0 y) : KnownV 𝔼 t0 Z0 := by
  intro i
  have h := hy.2.2.2 t0 (Sum.inl (Sum.inl i))
  have hz : (fun ω => Z0 ω i) = fun ω => y t0 ω (Sum.inl (Sum.inl i)) := by
    funext ω
    rw [← hy.2.1 ω]
    rfl
  rw [hz]
  exact h

/-- Woodford (2003), p. 540 and Assumption 8.1: under Assumption 8.1 (existence half) an initial
multiplier known at `t₀` is known at `t₀ − 1` (the solution with that initial multiplier has
`M_{t₀−1}` known at `t₀ − 1`, `GeneralFOC.MultiplierMeas`). -/
theorem knownV_pred_of_solvable {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hsolv : FOCSolvable P 𝔼 t0) {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c)
    {Z0 : Ω → ιZ → ℝ} (hZ0 : KnownV 𝔼 t0 Z0) {M : Ω → ιz → ℝ} (hM : KnownV 𝔼 t0 M) :
    KnownV 𝔼 (t0 - 1) M := by
  rcases Nat.eq_zero_or_pos t0 with h | h
  · subst h
    exact hM
  · obtain ⟨y', φ', hs'⟩ := hsolv c Z0 M hbc hac hZ0 hM
    intro r
    have h1 := hs'.2.2.1 (t0 - 1) r
    rw [Nat.sub_add_cancel h] at h1
    have e : (fun ω => φ' t0 ω (Sum.inr r)) = fun ω => M ω r :=
      funext fun ω => congrFun (hs'.2.2.2.1 ω) r
    rw [e] at h1
    exact h1

/-- Woodford (2003), p. 541 and fn 8 (**necessity of the first-order conditions, explicit
form**). Let `y` minimise (1.2) among bounded feasible plans subject to `Ẽ z_{t₀} = ē`. Given a
solution `(y⁰, φ⁰)` of (1.1) + (1.9) with `M_{t₀−1} = 0` and deterministic responses `(H, Φ)`,
there is a fixed matrix `R` such that, with `M₀ = R(ē − Ẽ z⁰_{t₀})` (bounded and known at `t₀`),
`y` itself satisfies (1.1) + (1.9) with initial multipliers `M₀`. Assumption 8.1 (existence),
pull-out and faithful expectations; any expectation system. -/
theorem foc_necessary_explicit {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hsolv : FOCSolvable P 𝔼 t0) (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    {ebar : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.OptimalSubjectTo 𝔼 c t0 Z0 ebar y) {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h0 : FOCSystem P 𝔼 c t0 Z0 0 y0 φ0)
    {H : ℕ → Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ} {Φ : ℕ → Matrix (ιZ ⊕ ιz) ιz ℝ}
    (hH : HomResp P t0 H Φ) :
    ∃ R : Matrix ιz ιz ℝ,
      KnownV 𝔼 t0 (fun ω => R *ᵥ (ebar ω - P.sys.Et *ᵥ zpart (y0 t0 ω))) ∧
      (∃ K, ∀ ω r, |(R *ᵥ (ebar ω - P.sys.Et *ᵥ zpart (y0 t0 ω))) r| ≤ K) ∧
      ∃ φ, FOCSystem P 𝔼 c t0 Z0 (fun ω => R *ᵥ (ebar ω - P.sys.Et *ᵥ zpart (y0 t0 ω))) y φ := by
  have hWt : P.Wᵀ = P.W := by
    have := P.W_posDef.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  obtain ⟨hfe, hey, hmin⟩ := hy
  have hZ0k := knownV_Z0 hfe
  set L := Lmat P t0 H with hL
  set e0 : Ω → ιz → ℝ := fun ω => P.sys.Et *ᵥ zpart (y0 t0 ω) with he0
  set d : Ω → ιz → ℝ := fun ω => ebar ω - e0 ω with hd
  -- `d` is known at `t₀` and bounded
  have hzk : ∀ (x : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ), AdaptedV 𝔼 x →
      KnownV 𝔼 t0 (fun ω => P.sys.Et *ᵥ zpart (x t0 ω)) :=
    fun x hx => knownV_mulVec P.sys.Et (fun r => hx t0 (Sum.inl (Sum.inr r)))
  have hebar : ebar = fun ω => P.sys.Et *ᵥ zpart (y t0 ω) := funext fun ω => (hey ω).symm
  have hdk : KnownV 𝔼 t0 d := by
    have := knownV_sub (hzk y hfe.2.2.2) (hzk y0 h0.1.2.2.2)
    rw [hd, hebar]
    exact this
  have hdb : ∃ K, ∀ ω r, |d ω r| ≤ K := by
    obtain ⟨Ky, hKy⟩ := hfe.2.2.1
    obtain ⟨K0, hK0⟩ := h0.1.2.2.1
    obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.sys.Et Ky
    obtain ⟨K2, hK2⟩ := exists_bound_mulVec P.sys.Et K0
    refine ⟨K1 + K2, fun ω r => ?_⟩
    simp only [hd, he0, hebar, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hK1 _ (fun i => hKy t0 ω _) r)
      (hK2 _ (fun i => hK0 t0 ω _) r))
  -- the variational inequality: `d ⟂ ker L'`
  have horth : ∀ ω w, Lᵀ *ᵥ w = 0 → w ⬝ᵥ d ω = 0 := by
    intro ω w hw
    have hwLw : w ⬝ᵥ (L *ᵥ w) = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hw, zero_dotProduct]
    have key : ∀ s : ℝ, s * (w ⬝ᵥ d ω) ≤ P.β * Jfn 𝔼 P.β P.T P.W P.τstar t0 y ω := by
      intro s
      set Ms : Ω → ιz → ℝ := fun _ => s • w with hMs
      have hs := combo h0 hH (knownV_const 𝔼 t0 (s • w)) (knownV_const 𝔼 (t0 - 1) (s • w))
        ⟨∑ r, |(s • w) r|, fun _ r => Finset.single_le_sum (f := fun r => |(s • w) r|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ r)⟩
      obtain ⟨hfeM, hbφM, hmφM, hMM, hfM⟩ := hs
      have gap := lagrangian_gap_init hpull P.β_pos P.β_lt_one hWt
        ((structural_iff P.sys 𝔼 c t0 y).mp hfe.1) ((structural_iff P.sys 𝔼 c t0 _).mp hfeM.1)
        hfe.2.2.2 hfeM.2.2.2 hfe.2.2.1 hfeM.2.2.1 hbφM hmφM hfM ω
      have hinit : (fun ω' => comboF t0 φ0 Φ Ms t0 ω' ⬝ᵥ
          (P.sys.Itil *ᵥ (y t0 ω' - comboF t0 y0 H Ms t0 ω'))) = fun ω' => s * (w ⬝ᵥ d ω') := by
        funext ω'
        have hZ : Zpart (y t0 ω' - comboF t0 y0 H Ms t0 ω') = 0 := by
          have h1 := hfe.2.1 ω'
          have h2 := hfeM.2.1 ω'
          funext r
          have e1 := congrFun h1 r
          have e2 := congrFun h2 r
          simp only [Zpart, Pi.sub_apply, Pi.zero_apply] at e1 e2 ⊢
          rw [e1, e2, sub_self]
        have hz : P.sys.Et *ᵥ zpart (y t0 ω' - comboF t0 y0 H Ms t0 ω') =
            d ω' - s • (L *ᵥ w) := by
          have e1 : zpart (y t0 ω' - comboF t0 y0 H Ms t0 ω') =
              zpart (y t0 ω') - zpart (comboF t0 y0 H Ms t0 ω') := rfl
          rw [e1, mulVec_sub, eq110_combo, hey ω', ← hL, hMs, mulVec_smul]
          simp only [hd, he0]
          abel
        have hM := hMM ω'
        rw [P.sys.Itil_mulVec, hZ, hz]
        rw [dotProduct, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          zero_add]
        have e2 : ∀ r, comboF t0 φ0 Φ Ms t0 ω' (Sum.inr r) = s * w r := fun r => by
          have := congrFun hM r
          simpa [Mpart, hMs] using this
        simp only [e2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have e3 : ∑ x, s * w x * (d ω' x - s * (L *ᵥ w) x) =
            s * (w ⬝ᵥ d ω') - s * s * (w ⬝ᵥ (L *ᵥ w)) := by
          simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          ring
        rw [e3, hwLw, mul_zero, sub_zero]
      have hEk : 𝔼.E t0 (fun ω' => s * (w ⬝ᵥ d ω')) = fun ω' => s * (w ⬝ᵥ d ω') := by
        have e : (fun ω' => s * (w ⬝ᵥ d ω')) = s • fun ω' => ∑ i, w i * d ω' i := rfl
        rw [e, map_smul, E_sum_mul]
        funext ω'
        simp only [Pi.smul_apply, smul_eq_mul]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdk i]
      rw [hinit, hEk] at gap
      have hnn := gap.nonneg fun k => mul_nonneg (pow_nonneg P.β_pos.le k)
        (by
          have := 𝔼.mono t0 (x := 0)
            (y := fun ω'' => quad P.W (P.T *ᵥ (y (t0 + k) ω'' - comboF t0 y0 H Ms (t0 + k) ω'')))
            (fun ω'' => quad_nonneg P.W_posDef.posSemidef _) ω
          simpa using this)
      have hJ0 := Jfn_nonneg 𝔼 P.β_pos.le P.W_posDef.posSemidef P.τstar t0
        (comboF t0 y0 H Ms) ω (Tm := P.T)
      have hβi : P.β * P.β⁻¹ = 1 := mul_inv_cancel₀ P.β_pos.ne'
      have h3 : P.β⁻¹ * (s * (w ⬝ᵥ d ω)) ≤ Jfn 𝔼 P.β P.T P.W P.τstar t0 y ω := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 P.β_pos.le
      rw [← mul_assoc, hβi, one_mul] at h4
      exact h4
    by_contra hne
    have := key ((P.β * Jfn 𝔼 P.β P.T P.W P.τstar t0 y ω + 1) / (w ⬝ᵥ d ω))
    rw [div_mul_cancel₀ _ hne] at this
    linarith
  -- `d` lies in the range of `L`
  have hdr : ∀ ω, d ω ∈ LinearMap.range L.mulVecLin := fun ω => mem_range_of_orth L (d ω)
    (horth ω)
  obtain ⟨R, hR⟩ := exists_rightInv L
  set M0 : Ω → ιz → ℝ := fun ω => R *ᵥ d ω with hM0
  have hM0k : KnownV 𝔼 t0 M0 := knownV_mulVec R hdk
  have hM0b : ∃ K, ∀ ω r, |M0 ω r| ≤ K := by
    obtain ⟨Kd, hKd⟩ := hdb
    obtain ⟨K, hK⟩ := exists_bound_mulVec R Kd
    exact ⟨K, fun ω r => hK _ (hKd ω) r⟩
  have hM0k' := knownV_pred_of_solvable hsolv hbc hac hZ0k hM0k
  have hs := combo h0 hH hM0k hM0k' hM0b
  have heb : ∀ ω, P.sys.Et *ᵥ zpart (comboF t0 y0 H M0 t0 ω) = ebar ω := by
    intro ω
    rw [eq110_combo, ← hL, hM0]
    beta_reduce
    rw [hR _ (hdr ω), hd]
    beta_reduce
    simp only [he0]
    abel
  have hopt : P.OptimalSubjectTo 𝔼 c t0 Z0
      (fun ω => P.sys.Et *ᵥ zpart (comboF t0 y0 H M0 t0 ω)) y := by
    have e : (fun ω => P.sys.Et *ᵥ zpart (comboF t0 y0 H M0 t0 ω)) = ebar := funext heb
    rw [e]
    exact ⟨hfe, hey, hmin⟩
  have htar := targets_eq_of_optimal P hpull hfaith hs hopt
  refine ⟨R, hM0k, hM0b, comboF t0 φ0 Φ M0, hfe, hs.2.1, hs.2.2.1, hs.2.2.2.1, fun t ht ω => ?_⟩
  have := hs.2.2.2.2 t ht ω
  rw [← htar t ht ω] at this
  exact this

/-- Woodford (2003), p. 541 (**necessity of the first-order conditions**, asserted in the book
without proof): under Assumption 8.1 (existence half), the pull-out property and faithful
expectations, every bounded plan that minimises (1.2) among bounded feasible plans subject to
`Ẽ z_{t₀} = ē` satisfies (1.1) + (1.9) with some bounded initial multipliers `M_{t₀−1}` known at
`t₀`. Any expectation system. -/
theorem foc_necessary {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hsolv : FOCSolvable P 𝔼 t0) (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    {ebar : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.OptimalSubjectTo 𝔼 c t0 Z0 ebar y) :
    ∃ M0 : Ω → ιz → ℝ, KnownV 𝔼 t0 M0 ∧ (∃ K, ∀ ω r, |M0 ω r| ≤ K) ∧
      ∃ φ, FOCSystem P 𝔼 c t0 Z0 M0 y φ := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · refine ⟨0, fun i => funext fun ω => isEmptyElim ω, ⟨0, fun ω => isEmptyElim ω⟩, 0, hy.1,
      ⟨0, fun _ ω => isEmptyElim ω⟩, fun _ _ => funext fun ω => isEmptyElim ω,
      fun ω => isEmptyElim ω, fun _ _ ω => isEmptyElim ω⟩
  · obtain ⟨y0, φ0, h0⟩ := hsolv c Z0 0 hbc hac (knownV_Z0 hy.1) (fun _ => 𝔼.const t0 0)
    obtain ⟨H, Φ, hH⟩ := exists_homResp hsolv
    obtain ⟨R, hk, hb, φ, hφ⟩ := foc_necessary_explicit hsolv hpull hfaith hbc hac hy h0 hH
    exact ⟨_, hk, hb, φ, hφ⟩

/-- Woodford (2003), p. 541, (1.8) (**necessity for the `t₀`-optimal plan**): under Assumption
8.1 (existence half), pull-out and faithful expectations, every `t₀`-optimal plan satisfies
(1.1) + (1.9) with `M_{t₀−1} = 0`. -/
theorem t0Optimal_foc_necessary {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hsolv : FOCSolvable P 𝔼 t0) (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.T0Optimal 𝔼 c t0 Z0 y) :
    ∃ φ, FOCSystem P 𝔼 c t0 Z0 0 y φ := by
  obtain ⟨y0, φ0, h0⟩ := hsolv c Z0 0 hbc hac (knownV_Z0 hy.1) (fun _ => 𝔼.const t0 0)
  have hopt0 := t0Optimal_of_focSystem P hpull h0
  obtain ⟨hfe0, hbφ0, hmφ0, hM0, hf0⟩ := h0
  have hinit : ∀ ω, φ0 t0 ω ⬝ᵥ (P.sys.Itil *ᵥ (y t0 ω - y0 t0 ω)) = 0 := by
    intro ω
    have hZ : Zpart (y t0 ω) - Zpart (y0 t0 ω) = 0 := by
      rw [hy.1.2.1 ω, hfe0.2.1 ω, sub_self]
    have hM : ∀ r, φ0 t0 ω (Sum.inr r) = 0 := fun r => congrFun (hM0 ω) r
    rw [mulVec_sub, P.sys.Itil_mulVec, P.sys.Itil_mulVec]
    simp only [dotProduct, Fintype.sum_sum_type, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, hM,
      zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_eq_zero fun r _ => ?_
    have := congrFun hZ r
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    rw [this, mul_zero]
  have htar := targets_eq_of_J_eq hpull hfaith P.β_pos P.β_lt_one P.W_posDef
    ((structural_iff P.sys 𝔼 c t0 y).mp hy.1.1) ((structural_iff P.sys 𝔼 c t0 y0).mp hfe0.1)
    hy.1.2.2.2 hfe0.2.2.2 hy.1.2.2.1 hfe0.2.2.1 hbφ0 hmφ0 hf0 hinit
    (fun ω => le_antisymm (hy.2 y0 hfe0 ω) (hopt0.2 y hy.1 ω))
  refine ⟨φ0, hy.1, hbφ0, hmφ0, hM0, fun t ht ω => ?_⟩
  have := hf0 t ht ω
  rw [← htar t ht ω] at this
  exact this

/-! ### The restatement (1.11)–(1.12) -/

/-- Woodford (2003), pp. 542–543 (**original ⇒ restated, unconditionally**): under Assumption 8.1
(existence half), pull-out and faithful expectations, a plan that is optimal from a timeless
perspective (1.5)–(1.6) solves (1.1) + (1.9) for some bounded initial multipliers `M_{t₀−1}`
known at `t₀`. This removes the attainability hypothesis of
`GeneralFOC.LQ.timeless_restated`. -/
theorem timeless_restated_unconditional {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (hsolv : FOCSolvable P 𝔼 t0) (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    {κ : Type*} [Fintype κ] {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c)
    {Z0 : Ω → ιZ → ℝ} {Xbar : ℕ → Ω → κ → ℝ} {f0 : ιz → ℝ} {F : Matrix ιz κ ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.TimelesslyOptimalPlan 𝔼 c t0 Z0 Xbar f0 F y) :
    ∃ M0 : Ω → ιz → ℝ, KnownV 𝔼 t0 M0 ∧ (∃ K, ∀ ω r, |M0 ω r| ≤ K) ∧
      ∃ φ, FOCSystem P 𝔼 c t0 Z0 M0 y φ :=
  foc_necessary hsolv hpull hfaith hbc hac hy.2

/-- Woodford (2003), (1.10)–(1.11), pp. 542–543 (**the restated definition, with initial
multipliers of the form (1.11)**): if, in addition, the value `Ẽ z_{t₀}` of the zero-multiplier
solution (Woodford's `e(c, Z, 0)` of (1.10)) is an affine function `h⁰ + H_X X̄_{t₀}` of the state
`X̄_{t₀}`, then a timelessly optimal plan satisfies the restated definition (1.11)–(1.12) with
`M_{t₀−1} = g⁰ + G X̄_{t₀}`. -/
theorem restated_of_affine {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hsolv : FOCSolvable P 𝔼 t0) (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    {κ : Type*} [Fintype κ] {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c)
    {Z0 : Ω → ιZ → ℝ} {Xbar : ℕ → Ω → κ → ℝ} {f0 : ιz → ℝ} {F : Matrix ιz κ ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.TimelesslyOptimalPlan 𝔼 c t0 Z0 Xbar f0 F y)
    {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h0 : FOCSystem P 𝔼 c t0 Z0 0 y0 φ0) {h0' : ιz → ℝ} {Hx : Matrix ιz κ ℝ}
    (haff : ∀ ω, P.sys.Et *ᵥ zpart (y0 t0 ω) = h0' + Hx *ᵥ Xbar t0 ω) :
    ∃ (g0 : ιz → ℝ) (G : Matrix ιz κ ℝ),
      RestatedTimeless (P := P) (𝔼 := 𝔼) (t0 := t0) c Z0 Xbar f0 F g0 G y := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨0, 0, fun _ _ ω => isEmptyElim ω, 0, hy.2.1, ⟨0, fun _ ω => isEmptyElim ω⟩,
      fun _ _ => funext fun ω => isEmptyElim ω, fun ω => isEmptyElim ω,
      fun _ _ ω => isEmptyElim ω⟩
  · obtain ⟨H, Φ, hH⟩ := exists_homResp hsolv
    obtain ⟨R, -, -, φ, hφ⟩ := foc_necessary_explicit hsolv hpull hfaith hbc hac hy.2 h0 hH
    refine ⟨R *ᵥ (P.sys.Et *ᵥ f0 - h0'), R * (P.sys.Et * F - Hx), hy.1, φ, ?_⟩
    have e : (fun ω => R *ᵥ (P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t0 ω) -
        P.sys.Et *ᵥ zpart (y0 t0 ω))) =
        fun ω => R *ᵥ (P.sys.Et *ᵥ f0 - h0') + (R * (P.sys.Et * F - Hx)) *ᵥ Xbar t0 ω := by
      funext ω
      rw [haff ω, ← mulVec_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_add]
      congr 1
      rw [mulVec_add]
      abel
    rw [← e]
    exact hφ

/-- Woodford (2003), (1.10)–(1.11), pp. 542–543 (**the affine form (1.11) is also necessary**):
under Assumption 8.1, if a plan satisfies the restated definition with `M_{t₀−1} = g⁰ + G X̄_{t₀}`
and the state `X̄_{t₀}` is known at `t₀`, then the value `Ẽ z_{t₀}` of every zero-multiplier
solution is affine in `X̄_{t₀}`. -/
theorem affine_of_restated {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hA : Assumption81 P 𝔼 t0) {κ : Type*} [Fintype κ] {c : ℕ → Ω → ιz → ℝ}
    (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ} {Xbar : ℕ → Ω → κ → ℝ}
    (hXk : KnownV 𝔼 t0 (Xbar t0)) {f0 : ιz → ℝ} {F : Matrix ιz κ ℝ} {g0 : ιz → ℝ}
    {G : Matrix ιz κ ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (h : RestatedTimeless (P := P) (𝔼 := 𝔼) (t0 := t0) c Z0 Xbar f0 F g0 G y)
    {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h0 : FOCSystem P 𝔼 c t0 Z0 0 y0 φ0) :
    ∃ (h0' : ιz → ℝ) (Hx : Matrix ιz κ ℝ),
      ∀ ω, P.sys.Et *ᵥ zpart (y0 t0 ω) = h0' + Hx *ᵥ Xbar t0 ω := by
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact ⟨0, 0, fun ω => isEmptyElim ω⟩
  obtain ⟨H, Φ, hH⟩ := exists_homResp hA.solvable
  obtain ⟨h1, φ, hφ⟩ := h
  set M : Ω → ιz → ℝ := fun ω => g0 + G *ᵥ Xbar t0 ω with hM
  have hZ0k := knownV_Z0 hφ.1
  have hMk : KnownV 𝔼 t0 M := knownV_add (knownV_const 𝔼 t0 g0) (knownV_mulVec G hXk)
  have hMk' := knownV_pred_of_solvable hA.solvable hbc hac hZ0k hMk
  have hMb : ∃ K, ∀ ω r, |M ω r| ≤ K := by
    obtain ⟨K, hK⟩ := hφ.2.1
    refine ⟨K, fun ω r => ?_⟩
    have := hK t0 ω (Sum.inr r)
    have e := congrFun (hφ.2.2.2.1 ω) r
    simp only [Mpart] at e
    rw [e] at this
    exact this
  have hs := combo h0 hH hMk hMk' hMb
  obtain ⟨hyeq, -⟩ := hA.unique c Z0 M y _ φ _ hφ hs t0 le_rfl
  refine ⟨P.sys.Et *ᵥ f0 - Lmat P t0 H *ᵥ g0, P.sys.Et * F - Lmat P t0 H * G, fun ω => ?_⟩
  have e1 := eq110_combo P t0 y0 H M ω
  rw [← hyeq, h1 t0 le_rfl ω] at e1
  rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  have e2 : P.sys.Et *ᵥ zpart (y0 t0 ω) = P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t0 ω) -
      Lmat P t0 H *ᵥ M ω := by rw [e1]; abel
  rw [e2, hM]
  simp only [mulVec_add]
  abel

/-- Woodford (2003), (1.10)–(1.12), pp. 542–543 (**exact form of "original ⇔ restated"**): under
Assumption 8.1, pull-out and faithful expectations, with `X̄_{t₀}` known at `t₀`, a plan that is
optimal from a timeless perspective satisfies the restated definition (1.11)–(1.12) for some
`g⁰, G` if and only if the zero-multiplier value `e(c, Z, 0)` of (1.10) is affine in `X̄_{t₀}`. -/
theorem restated_iff_affine {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}
    (hA : Assumption81 P 𝔼 t0) (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    {κ : Type*} [Fintype κ] {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c)
    {Z0 : Ω → ιZ → ℝ} {Xbar : ℕ → Ω → κ → ℝ} (hXk : KnownV 𝔼 t0 (Xbar t0)) {f0 : ιz → ℝ}
    {F : Matrix ιz κ ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.TimelesslyOptimalPlan 𝔼 c t0 Z0 Xbar f0 F y)
    {y0 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ0 : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h0 : FOCSystem P 𝔼 c t0 Z0 0 y0 φ0) :
    (∃ (g0 : ιz → ℝ) (G : Matrix ιz κ ℝ),
      RestatedTimeless (P := P) (𝔼 := 𝔼) (t0 := t0) c Z0 Xbar f0 F g0 G y) ↔
    ∃ (h0' : ιz → ℝ) (Hx : Matrix ιz κ ℝ),
      ∀ ω, P.sys.Et *ᵥ zpart (y0 t0 ω) = h0' + Hx *ᵥ Xbar t0 ω :=
  ⟨fun ⟨_, _, h⟩ => affine_of_restated hA hbc hac hXk h h0,
    fun ⟨_, _, haff⟩ => restated_of_affine hA.solvable hpull hfaith hbc hac hy h0 haff⟩

end Woodford.OptimalPolicyRules.TidyR5bFOCNecessity
