/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.GeneralBKPencil

/-!
# The Blanchard–Kahn theorem for singular pencils (Klein; King–Watson)

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670 (models first written as
`A₀ E_t y_{t+1} = A₁ y_t + w_t`, where `A₀` may be singular because some equations are static);
Blanchard and Kahn (1980); the singular case is that of King and Watson (1998) and Klein (2000).

No invertibility of `A₀` is assumed. With `pencilPoly A₀ A₁ = det(λA₀ − A₁)`:

* `nonexist_of_not_regular`: if the pencil is singular (`det(λA₀ − A₁) ≡ 0`), a polynomial left
  null vector `q(λ)` gives a linear restriction `∑ q_k · w_k = 0` on the forcing of every
  solution, so for a bounded deterministic forcing `w_t = ρᵗ q(ρ)` no solution exists at all.
* For a regular pencil choose `c` with `det(cA₀ − A₁) ≠ 0` (`exists_regular_point`) and put
  `N = (cA₀ − A₁)⁻¹A₀`. The Fitting decomposition of `N` (`exists_fitting`, `Fitting`) splits the
  state space into the range of `P`, where `N` is invertible with inverse `Ni` (the finite
  generalised eigenvalues), and the range of `Q`, where `N` is nilpotent (the infinite ones).
* `determinatePencil_iff_ahat`: the pencil system is determinate iff the standard-form system
  `E_t y_{t+1} = Â y_t + w_t` is, `Â = cP − Ni + 2Q` (`ahat`). The `Q` block of the pencil is
  purely forward-looking with a nilpotent forward matrix (`pencilV_existsUnique`, `kmat_pow`);
  the `Q` block of `Â` is the unstable `E_t q_{t+1} = 2q_t + g_t` (`twoBlock_existsUnique`);
  equilibria correspond (`pencil_iff_ahat`).
* `poly_relations`: `det(λA₀ − A₁) = κ f(λ)` with `κ ≠ 0` and `det(λ − Â) = f(λ) g(λ)`, where all
  roots of `g` equal `2` (`gpoly_roots`); hence `eigs_ahat`, `noUnit_ahat_iff`,
  `stableCount_ahat`: the eigenvalues of `Â` in or on the unit circle are exactly the roots of
  `det(λA₀ − A₁)` there, with multiplicity.
* `mem_boundedOrbits_ahat`: the bounded orbits of `Â` are the initial values of bounded
  deterministic solutions of `A₀ y_{t+1} = A₁ y_t` (`PencilBounded`).
* `determinatePencil_iff_general` (**Blanchard–Kahn for arbitrary pencils**): for any expectation
  system on a nonempty state space, `A₀ E_t y_{t+1} = A₁ y_t + w_t` is determinate iff the pencil
  is regular, no root of `det(λA₀ − A₁)` lies on the unit circle, exactly `|X|` roots (with
  multiplicity) lie in the open unit disc, and no nonzero bounded deterministic solution starts
  with `x_0 = 0` (`GenericPencil`).
* `unstable_add_infinite`: the infinite generalised eigenvalues (`n − deg det(λA₀ − A₁)` of them)
  count as unstable — with the roots outside the unit circle they number `|Z|`.
-/

namespace Woodford.NeoWicksellianFramework.GeneralBKSingular

open Polynomial Filter Topology InvariantSplit GeneralBKForward GeneralBK GeneralBKPencil
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The Fitting decomposition of `N` -/

/-- Woodford (2003), App. C.1, p. 670 (tool): powers of a matrix act as powers of its linear
map. -/
theorem pow_mulVec_eq (N : Matrix ι ι ℝ) (k : ℕ) (x : ι → ℝ) :
    N ^ k *ᵥ x = (Matrix.toLin' N ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, pow_succ', Module.End.mul_apply,
      Matrix.toLin'_apply]

/-- **The Fitting decomposition** (Woodford (2003), App. C.1, p. 670, the tool for singular
pencils): for a square matrix `N` there are complementary idempotents `P`, `Q` commuting with `N`
and a matrix `Ni` with `N Ni = Ni N = P` (`N` is invertible on the range of `P`), `Q Ni = Ni Q = 0`,
and `Nᵐ Q = 0` (`N` is nilpotent on the range of `Q`). -/
theorem exists_fitting (N : Matrix ι ι ℝ) :
    ∃ (m : ℕ) (P Q Ni : Matrix ι ι ℝ), P + Q = 1 ∧ P * Q = 0 ∧ Q * P = 0 ∧
      N * P = P * N ∧ N * Q = Q * N ∧ N * Ni = P ∧ Ni * N = P ∧ Q * Ni = 0 ∧ Ni * Q = 0 ∧
      N ^ m * Q = 0 := by
  set φ := Matrix.toLin' N with hφ
  obtain ⟨m0, hm0⟩ := Filter.eventually_atTop.mp (φ.eventually_isCompl_ker_pow_range_pow)
  set m := m0 + 1 with hm
  have hc : IsCompl (LinearMap.ker (φ ^ m)) (LinearMap.range (φ ^ m)) := hm0 m (by omega)
  set V := LinearMap.ker (φ ^ m) with hV
  set U := LinearMap.range (φ ^ m) with hU
  set Pl := U.projection V hc.symm with hPl
  set Ql := V.projection U hc with hQl
  have hPQ : ∀ x, Pl x + Ql x = x := fun x => by
    rw [add_comm]; exact Submodule.projection_add_projection_eq_self hc x
  have hφU : ∀ u ∈ U, φ u ∈ U := by
    rintro _ ⟨y, rfl⟩
    exact ⟨φ y, by rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]⟩
  have hφV : ∀ v ∈ V, φ v ∈ V := by
    intro v hv
    rw [hV, LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hv, map_zero]
  have hPU : ∀ x, Pl x ∈ U := fun x => Submodule.projection_apply_mem _ x
  have hQV : ∀ x, Ql x ∈ V := fun x => Submodule.projection_apply_mem _ x
  have hPleft : ∀ u ∈ U, Pl u = u := fun u hu => Submodule.projection_apply_of_mem_left _ hu
  have hPright : ∀ v ∈ V, Pl v = 0 := fun v hv => Submodule.projection_apply_of_mem_right _ hv
  have hQleft : ∀ v ∈ V, Ql v = v := fun v hv => Submodule.projection_apply_of_mem_left _ hv
  have hQright : ∀ u ∈ U, Ql u = 0 := fun u hu => Submodule.projection_apply_of_mem_right _ hu
  have hφP : ∀ x, φ (Pl x) = Pl (φ x) := by
    intro x
    conv_rhs => rw [← hPQ x, map_add, map_add, hPleft _ (hφU _ (hPU x)),
      hPright _ (hφV _ (hQV x)), add_zero]
  have hφQ : ∀ x, φ (Ql x) = Ql (φ x) := by
    intro x
    conv_rhs => rw [← hPQ x, map_add, map_add, hQright _ (hφU _ (hPU x)),
      hQleft _ (hφV _ (hQV x)), zero_add]
  set ψ : U →ₗ[ℝ] U := φ.restrict hφU with hψ
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h0 : φ u = 0 := by
      have := congrArg Subtype.val hu
      simpa [hψ, LinearMap.restrict_apply] using this
    have huV : (u : ι → ℝ) ∈ V := by
      rw [hV, LinearMap.mem_ker, hm, pow_succ, Module.End.mul_apply, h0, map_zero]
    have := hc.disjoint.le_bot ⟨huV, u.2⟩
    exact Subtype.ext ((Submodule.mem_bot ℝ).mp this)
  have hψsurj : Function.Surjective ψ := LinearMap.injective_iff_surjective.mp hψinj
  set eψ := LinearEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩ with heψ
  set pU := U.projectionOnto V hc.symm with hpU
  have hpUval : ∀ x, ((pU x : U) : ι → ℝ) = Pl x := fun x => rfl
  set Nl : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := U.subtype ∘ₗ eψ.symm.toLinearMap ∘ₗ pU with hNl
  have hNlU : ∀ x, Nl x ∈ U := fun x => (eψ.symm (pU x)).2
  have hφNl : ∀ x, φ (Nl x) = Pl x := by
    intro x
    have := congrArg Subtype.val (eψ.apply_symm_apply (pU x))
    rw [hpUval] at this
    rw [← this]
    rfl
  have hpUφ : ∀ x, pU (φ x) = ψ (pU x) := by
    intro x
    apply Subtype.ext
    rw [hpUval]
    change Pl (φ x) = φ (Pl x)
    exact (hφP x).symm
  have hNlφ : ∀ x, Nl (φ x) = Pl x := by
    intro x
    change ((eψ.symm (pU (φ x)) : U) : ι → ℝ) = Pl x
    rw [hpUφ]
    have : eψ.symm (ψ (pU x)) = pU x := eψ.symm_apply_apply (pU x)
    rw [this, hpUval]
  have hNlQ : ∀ x, Nl (Ql x) = 0 := by
    intro x
    have : pU (Ql x) = 0 := (Submodule.projectionOnto_apply_eq_zero_iff _).mpr (hQV x)
    change ((eψ.symm (pU (Ql x)) : U) : ι → ℝ) = 0
    rw [this, map_zero]
    rfl
  refine ⟨m, LinearMap.toMatrix' Pl, LinearMap.toMatrix' Ql, LinearMap.toMatrix' Nl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> refine matrix_eq_of_mulVec fun x => ?_ <;>
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec,
      Matrix.one_mulVec, Matrix.zero_mulVec]
  · exact hPQ x
  · exact hPright _ (hQV x)
  · exact hQright _ (hPU x)
  · have := hφP x; simpa [hφ, Matrix.toLin'_apply] using this
  · have := hφQ x; simpa [hφ, Matrix.toLin'_apply] using this
  · have := hφNl x; simpa [hφ, Matrix.toLin'_apply] using this
  · have := hNlφ x; simpa [hφ, Matrix.toLin'_apply] using this
  · exact hQright _ (hNlU x)
  · exact hNlQ x
  · rw [pow_mulVec_eq, ← hφ]
    exact hQV x

/-- Woodford (2003), App. C.1, p. 670 (tool): the data of a Fitting decomposition of `N`
(the conclusion of `exists_fitting`). -/
def Fitting (N : Matrix ι ι ℝ) (m : ℕ) (P Q Ni : Matrix ι ι ℝ) : Prop :=
  P + Q = 1 ∧ P * Q = 0 ∧ Q * P = 0 ∧ N * P = P * N ∧ N * Q = Q * N ∧ N * Ni = P ∧
    Ni * N = P ∧ Q * Ni = 0 ∧ Ni * Q = 0 ∧ N ^ m * Q = 0

/-- Woodford (2003), App. C.1, p. 670 (tool): consequences of a Fitting decomposition:
idempotents, `P Ni = Ni`, and `Q N P = 0`. -/
theorem Fitting.basic {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ}
    (hF : Fitting N m P Q Ni) :
    P * P = P ∧ Q * Q = Q ∧ P * Ni = Ni ∧ Q * N * P = 0 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := hF
  have hP : P = 1 - Q := eq_sub_of_add_eq h1
  have hQ : Q = 1 - P := eq_sub_of_add_eq' h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc P * P = P * (1 - Q) := by rw [← hP]
      _ = P := by rw [Matrix.mul_sub, h2, Matrix.mul_one, sub_zero]
  · calc Q * Q = Q * (1 - P) := by rw [← hQ]
      _ = Q := by rw [Matrix.mul_sub, h3, Matrix.mul_one, sub_zero]
  · calc P * Ni = (1 - Q) * Ni := by rw [← hP]
      _ = Ni := by rw [Matrix.sub_mul, h8, Matrix.one_mul, sub_zero]
  · rw [← h5, Matrix.mul_assoc, h3, Matrix.mul_zero]

/-- Woodford (2003), App. C.1, p. 670 (tool): a nilpotent matrix has geometrically bounded
powers (they vanish from `n` on). -/
theorem pow_bound_of_pow_eq_zero {K : Matrix ι ι ℝ} {n : ℕ} (h : K ^ n = 0) :
    ∃ Cb ρ : ℝ, 0 ≤ Cb ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k := by
  set Cb : ℝ := ∑ k ∈ Finset.range n, 2 ^ k * ∑ i, ∑ j, |(K ^ k) i j| with hCb
  have hterm : ∀ k, 0 ≤ 2 ^ k * ∑ i, ∑ j, |(K ^ k) i j| := fun k =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      abs_nonneg _)
  refine ⟨Cb, 1 / 2, Finset.sum_nonneg fun k _ => hterm k, by norm_num, by norm_num,
    fun k i j => ?_⟩
  by_cases hk : k < n
  · have h1 : |(K ^ k) i j| * 2 ^ k ≤ Cb := by
      calc |(K ^ k) i j| * 2 ^ k ≤ 2 ^ k * ∑ i, ∑ j, |(K ^ k) i j| := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left (abs_entry_le_sum _ i j) (by positivity)
        _ ≤ Cb := Finset.single_le_sum (f := fun k => 2 ^ k * ∑ i, ∑ j, |(K ^ k) i j|)
            (fun k _ => hterm k) (Finset.mem_range.mpr hk)
    have h2 : (0 : ℝ) < 2 ^ k := by positivity
    rw [div_pow, one_pow, ← div_eq_mul_one_div, le_div_iff₀ h2]
    exact h1
  · have : K ^ k = 0 := by
      rw [show k = n + (k - n) by omega, pow_add, h, Matrix.zero_mul]
    rw [this, Matrix.zero_apply, abs_zero]
    exact mul_nonneg (Finset.sum_nonneg fun k _ => hterm k) (by positivity)

/-! ### The standard-form matrix `Â` -/

/-- Woodford (2003), App. C.1, p. 670: the standard-form matrix `Â = cP − Ni + 2Q` of a regular
pencil — the finite generalised eigenvalues on the range of `P`, and the (unstable) value `2` in
place of the infinite ones on the range of `Q`. -/
def ahat (c : ℝ) (P Q Ni : Matrix ι ι ℝ) : Matrix ι ι ℝ := c • P - Ni + (2 : ℝ) • Q

/-- Woodford (2003), App. C.1, p. 670 (tool): `P Â = cP − Ni` and `Q Â = 2Q`. -/
theorem ahat_proj {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ} (hF : Fitting N m P Q Ni)
    (c : ℝ) : P * ahat c P Q Ni = c • P - Ni ∧ Q * ahat c P Q Ni = (2 : ℝ) • Q := by
  obtain ⟨hPP, hQQ, hPN, -⟩ := hF.basic
  obtain ⟨-, h2, h3, -, -, -, -, h8, -, -⟩ := hF
  constructor
  · rw [ahat, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hPP, hPN, h2,
      smul_zero, add_zero]
  · rw [ahat, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, h3, h8, hQQ,
      smul_zero, zero_sub, neg_zero, zero_add]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), App. C.1, p. 670: the standard-form system `E_t y_{t+1} = Â y_t + ŵ_t`
splits into its `P` and `Q` parts, `P E_t y_{t+1} = (cP − Ni) y_t + P ŵ_t` and
`Q E_t y_{t+1} = 2 Q y_t + Q ŵ_t`. -/
theorem split_ahat {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ}
    (hF : Fitting N m P Q Ni) (c : ℝ) (e y g : ι → Ω → ℝ) :
    e = mv (ahat c P Q Ni) y + g ↔
      mv P e = mv (c • P - Ni) y + mv P g ∧ mv Q e = mv ((2 : ℝ) • Q) y + mv Q g := by
  obtain ⟨hPA, hQA⟩ := ahat_proj hF c
  obtain ⟨h1, -⟩ := hF
  have hsplit : ∀ a : ι → Ω → ℝ, a = mv P a + mv Q a := fun a => by
    rw [← add_mv, h1, mv_one]
  constructor
  · intro h
    rw [h, mv_add, mv_add, mv_mv, mv_mv, hPA, hQA]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hp, hq⟩
    calc e = mv P e + mv Q e := hsplit e
      _ = (mv (c • P - Ni) y + mv P g) + (mv ((2 : ℝ) • Q) y + mv Q g) := by rw [hp, hq]
      _ = (mv (P * ahat c P Q Ni) y + mv (Q * ahat c P Q Ni) y) + (mv P g + mv Q g) := by
          rw [hPA, hQA]; abel
      _ = mv (ahat c P Q Ni) y + g := by rw [← mv_mv, ← mv_mv, ← hsplit, ← hsplit]

/-- Woodford (2003), App. C.1, p. 670: the reduced pencil equation
`N E_t y_{t+1} = (cN − 1) y_t + g_t` splits into its `P` part, solved for `P E_t y_{t+1}` by
`Ni`, and its `Q` part. -/
theorem split_pencil {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ}
    (hF : Fitting N m P Q Ni) (c : ℝ) (e y g : ι → Ω → ℝ) :
    mv N e = mv (c • N - 1) y + g ↔
      mv P e = mv (c • P - Ni) y + mv Ni g ∧
        mv N (mv Q e) = mv (c • N - 1) (mv Q y) + mv Q g := by
  obtain ⟨h1, -, -, h4, h5, h6, h7, -, -, -⟩ := hF
  have hNiA : Ni * (c • N - 1) = c • P - Ni := by
    rw [Matrix.mul_sub, Matrix.mul_smul, h7, Matrix.mul_one]
  have hQA : Q * (c • N - 1) = (c • N - 1) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h5, Matrix.mul_one,
      Matrix.one_mul]
  constructor
  · intro h
    constructor
    · have := congrArg (mv Ni) h
      rwa [mv_mv, h7, mv_add, mv_mv, hNiA] at this
    · calc mv N (mv Q e) = mv Q (mv N e) := by rw [mv_mv, mv_mv, h5]
        _ = mv Q (mv (c • N - 1) y + g) := by rw [h]
        _ = _ := by rw [mv_add, mv_mv, mv_mv, hQA]
  · rintro ⟨hp, hq⟩
    have hsplit : ∀ a : ι → Ω → ℝ, a = mv P a + mv Q a := fun a => by
      rw [← add_mv, h1, mv_one]
    have hNP : mv N (mv P e) = mv (c • (N * P) - P) y + mv P g := by
      rw [hp, mv_add, mv_mv, mv_mv, Matrix.mul_sub, Matrix.mul_smul, h6]
    calc mv N e = mv N (mv P e) + mv N (mv Q e) := by rw [← mv_add, ← hsplit]
      _ = mv (c • (N * P) - P) y + mv P g + (mv (c • N - 1) (mv Q y) + mv Q g) := by
          rw [hNP, hq]
      _ = mv (c • (N * P) - P + (c • N - 1) * Q) y + (mv P g + mv Q g) := by
          rw [add_mv, ← mv_mv]; abel
      _ = mv (c • N - 1) y + g := by
          rw [← hsplit g]
          congr 2
          rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
          have : c • (N * P) - P + (c • (N * Q) - Q) = c • (N * (P + Q)) - (P + Q) := by
            rw [Matrix.mul_add, smul_add]; abel
          rw [this, h1, Matrix.mul_one]

/-! ### The two forward blocks -/

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): the one-step-ahead expectations of any process
form an adapted process. -/
theorem adaptedV_Enext (q : ℕ → ι → Ω → ℝ) :
    AdaptedV 𝔼 (fun t i => 𝔼.E t (q (t + 1) i)) := fun t _ => 𝔼.E_E_self t _

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): one-step-ahead expectations of a bounded process
are bounded. -/
theorem boundedV_Enext {q : ℕ → ι → Ω → ℝ} (hq : BoundedV q) :
    BoundedV (fun t i => 𝔼.E t (q (t + 1) i)) := by
  obtain ⟨M, hM⟩ := hq
  exact ⟨M, fun t i ω => 𝔼.abs_E_le (hM (t + 1) i) t ω⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): scalar multiples of bounded vector processes are
bounded. -/
theorem boundedV_smul (r : ℝ) {q : ℕ → ι → Ω → ℝ} (hq : BoundedV q) :
    BoundedV (fun t => r • q t) := by
  obtain ⟨M, hM⟩ := hq
  exact ⟨|r| * M, fun t i ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t i ω) (abs_nonneg r)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): scalar multiples of adapted vector processes are
adapted. -/
theorem adaptedV_smul (r : ℝ) {q : ℕ → ι → Ω → ℝ} (hq : AdaptedV 𝔼 q) :
    AdaptedV 𝔼 (fun t => r • q t) := fun t i => by
  simp only [Pi.smul_apply, map_smul, hq t i]

omit [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): `E_t` commutes with a constant matrix acting on the
next-period vector. -/
theorem Enext_mv (M : Matrix ι ι ℝ) (q : ℕ → ι → Ω → ℝ) (t : ℕ) :
    (fun i => 𝔼.E t (mv M (q (t + 1)) i)) = mv M (fun i => 𝔼.E t (q (t + 1) i)) := by
  funext i
  exact E_mv 𝔼 t M _ i

omit [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): a scalar multiple of a matrix acts by scaling. -/
theorem smul_mv (r : ℝ) (M : Matrix ι ι ℝ) (a : ι → Ω → ℝ) : mv (r • M) a = r • mv M a := by
  funext i
  simp only [mv, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.smul_sum, smul_smul]

omit [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): a matrix acting on a scaled vector. -/
theorem mv_smul (M : Matrix ι ι ℝ) (r : ℝ) (a : ι → Ω → ℝ) : mv M (r • a) = r • mv M a := by
  funext i
  simp only [mv, Pi.smul_apply, smul_smul, Finset.smul_sum, mul_comm]

/-- Woodford (2003), App. C.1, p. 670 (tool): a multiple of the identity acts by scaling. -/
theorem mv_smul_one (r : ℝ) (a : ι → Ω → ℝ) : mv (r • (1 : Matrix ι ι ℝ)) a = r • a := by
  rw [smul_mv, mv_one]

/-- Woodford (2003), App. C.1, p. 670: the standard-form `Q` block `E_t q_{t+1} = 2 q_t + g_t` is
the forward system `q_t = ½ E_t q_{t+1} − ½ g_t`. -/
theorem twoBlock_iff (q g : ℕ → ι → Ω → ℝ) :
    (∀ t, (fun i => 𝔼.E t (q (t + 1) i)) = (2 : ℝ) • q t + g t) ↔
      FSolves 𝔼 ((2⁻¹ : ℝ) • (1 : Matrix ι ι ℝ)) (fun t => -((2⁻¹ : ℝ) • g t)) q := by
  unfold FSolves
  simp only [mv_smul_one]
  constructor
  · intro h t
    rw [h t, smul_add, smul_smul]
    norm_num
  · intro h t
    have := h t
    have e : (fun i => 𝔼.E t (q (t + 1) i)) = (2 : ℝ) • (q t + (2⁻¹ : ℝ) • g t) := by
      rw [this, add_assoc]
      simp [smul_smul]
    rw [e, smul_add, smul_smul]
    norm_num

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670: `E_t q_{t+1} = 2 q_t + g_t` has exactly one bounded
adapted solution for every bounded adapted `g` (its forward solution). -/
theorem twoBlock_existsUnique [Finite ι] {g : ℕ → ι → Ω → ℝ} (hgb : BoundedV g)
    (hga : AdaptedV 𝔼 g) :
    ∃! q, (∀ t, (fun i => 𝔼.E t (q (t + 1) i)) = (2 : ℝ) • q t + g t) ∧ AdaptedV 𝔼 q ∧
      BoundedV q := by
  have := Fintype.ofFinite ι
  classical
  have hK : ∀ k i j, |(((2⁻¹ : ℝ) • (1 : Matrix ι ι ℝ)) ^ k) i j| ≤ 1 * (1 / 2) ^ k := by
    intro k i j
    rw [smul_pow, one_pow, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, abs_mul]
    split_ifs <;> norm_num
  obtain ⟨Mf, hMf⟩ := boundedV_neg (boundedV_smul (2⁻¹ : ℝ) hgb)
  obtain ⟨q, hq, hqa, hqb⟩ := fsolves_exists 𝔼 (by norm_num) (by norm_num) hK hMf
    (adaptedV_neg 𝔼 (adaptedV_smul 𝔼 _ hga))
  refine ⟨q, ⟨(twoBlock_iff 𝔼 q g).mpr hq, hqa, hqb⟩, fun q' ⟨hq', hqa', hqb'⟩ => ?_⟩
  exact fsolves_unique 𝔼 (by norm_num) (by norm_num) hK ((twoBlock_iff 𝔼 q' g).mp hq') hq
    hqa' hqa hqb' hqb

/-- Woodford (2003), App. C.1, p. 670: `R = ∑_{k<m} (cN)ᵏ`, the inverse of `1 − cN` on the
nilpotent block. -/
noncomputable def rmat (c : ℝ) (N : Matrix ι ι ℝ) (m : ℕ) : Matrix ι ι ℝ :=
  ∑ k ∈ Finset.range m, (c • N) ^ k

/-- Woodford (2003), App. C.1, p. 670: the forward matrix `K = −R N Q` of the nilpotent block. -/
noncomputable def kmat (c : ℝ) (N Q : Matrix ι ι ℝ) (m : ℕ) : Matrix ι ι ℝ :=
  -(rmat c N m * N * Q)

/-- Woodford (2003), App. C.1, p. 670 (tool): matrices commuting with `N` commute with `R`. -/
theorem commute_rmat {c : ℝ} {N M : Matrix ι ι ℝ} (h : Commute M N) (m : ℕ) :
    Commute M (rmat c N m) :=
  Commute.sum_right _ _ _ fun k _ => (h.smul_right c).pow_right k

/-- Woodford (2003), App. C.1, p. 670: the forward matrix of the nilpotent block is nilpotent,
`K^{m+1} = 0`. -/
theorem kmat_pow {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ} (hF : Fitting N m P Q Ni)
    (c : ℝ) : kmat c N Q m ^ (m + 1) = 0 := by
  obtain ⟨-, -, -, -, h5, -, -, -, -, h10⟩ := hF
  have hRN : Commute (rmat c N m) N := (commute_rmat (Commute.refl N) m).symm
  have hRQ : Commute (rmat c N m) Q := (commute_rmat (Commute.symm h5) m).symm
  have hNQ : Commute N Q := h5
  have hRNQ : Commute (rmat c N m * N) Q := Commute.mul_left hRQ hNQ
  have h0 : N ^ (m + 1) * Q ^ (m + 1) = 0 := by
    rw [pow_succ', pow_succ', Matrix.mul_assoc, ← Matrix.mul_assoc (N ^ m), h10, Matrix.zero_mul,
      Matrix.mul_zero]
  rw [kmat, neg_pow, hRNQ.mul_pow, hRN.mul_pow, Matrix.mul_assoc (rmat c N m ^ (m + 1)), h0,
    Matrix.mul_zero, mul_zero]

omit [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): the zero matrix acts as zero. -/
theorem zero_mv (a : ι → Ω → ℝ) : mv (0 : Matrix ι ι ℝ) a = 0 := by
  funext i
  simp [mv]

omit [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): the action of a negated matrix. -/
theorem neg_mv (M : Matrix ι ι ℝ) (a : ι → Ω → ℝ) : mv (-M) a = -mv M a := by
  funext i
  simp [mv, Finset.sum_neg_distrib]

/-- Woodford (2003), App. C.1, p. 670 (tool): matrix facts for the nilpotent block:
`R(1 − cN) = (1 − cN)R = 1 − (cN)ᵐ`, `(cN)ᵐ Q = 0`, `(1 − cN)K = −NQ`, `QK = KQ = K`,
`QR = RQ`. -/
theorem nil_facts {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ} (hF : Fitting N m P Q Ni)
    (c : ℝ) :
    rmat c N m * (1 - c • N) = 1 - (c • N) ^ m ∧ (1 - c • N) * rmat c N m = 1 - (c • N) ^ m ∧
      (c • N) ^ m * Q = 0 ∧ (1 - c • N) * kmat c N Q m = -(N * Q) ∧
      Q * kmat c N Q m = kmat c N Q m ∧ kmat c N Q m * Q = kmat c N Q m ∧
      Q * rmat c N m = rmat c N m * Q := by
  obtain ⟨-, hQQ, -, -⟩ := hF.basic
  obtain ⟨-, -, -, -, h5, -, -, -, -, h10⟩ := hF
  have hRm : rmat c N m * (1 - c • N) = 1 - (c • N) ^ m := geom_sum_mul_neg _ _
  have hmR : (1 - c • N) * rmat c N m = 1 - (c • N) ^ m := mul_neg_geom_sum _ _
  have hz : (c • N) ^ m * Q = 0 := by rw [smul_pow, Matrix.smul_mul, h10, smul_zero]
  have hQR : Q * rmat c N m = rmat c N m * Q := commute_rmat (Commute.symm h5) m
  refine ⟨hRm, hmR, hz, ?_, ?_, ?_, hQR⟩
  · rw [kmat, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hmR, Matrix.sub_mul,
      Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc ((c • N) ^ m), h5, ← Matrix.mul_assoc,
      hz, Matrix.zero_mul, sub_zero]
  · rw [kmat, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR, Matrix.mul_assoc _ Q,
      ← h5, ← Matrix.mul_assoc, Matrix.mul_assoc _ N Q, Matrix.mul_assoc, Matrix.mul_assoc,
      hQQ]
  · rw [kmat, Matrix.neg_mul, Matrix.mul_assoc _ Q Q, hQQ]

/-- Woodford (2003), App. C.1, p. 670: on the nilpotent block (`Q`-invariant vectors), the
pencil equation `N e = (cN − 1) a + b` is the forward relation `a = K e + R b`. -/
theorem pencilV_step {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ}
    (hF : Fitting N m P Q Ni) (c : ℝ) {e a b : ι → Ω → ℝ} (ha : mv Q a = a) (hb : mv Q b = b)
    (he : mv Q e = e) :
    mv N e = mv (c • N - 1) a + b ↔ a = mv (kmat c N Q m) e + mv (rmat c N m) b := by
  obtain ⟨hRm, hmR, hz, hK, -, -, -⟩ := nil_facts hF c
  have hfix : ∀ v : ι → Ω → ℝ, mv Q v = v → mv (1 - (c • N) ^ m) v = v := by
    intro v hv
    have h0 : mv ((c • N) ^ m) v = 0 :=
      calc mv ((c • N) ^ m) v = mv ((c • N) ^ m) (mv Q v) := by rw [hv]
        _ = 0 := by rw [mv_mv, hz, zero_mv]
    rw [sub_mv, mv_one, h0, sub_zero]
  constructor
  · intro h
    have h1 : mv (1 - c • N) a = b - mv N e := by
      rw [h, sub_mv, sub_mv, mv_one]
      abel
    calc a = mv (1 - (c • N) ^ m) a := (hfix a ha).symm
      _ = mv (rmat c N m) (mv (1 - c • N) a) := by rw [mv_mv, hRm]
      _ = mv (kmat c N Q m) e + mv (rmat c N m) b := by
          rw [h1, mv_sub, kmat, neg_mv, ← mv_mv, ← mv_mv, he, mv_mv]
          abel
  · intro h
    have h1 : mv (1 - c • N) a = b - mv N e := by
      rw [h, mv_add, mv_mv, mv_mv, hmR, hfix b hb, hK, neg_mv, ← mv_mv, he]
      abel
    have h2 : mv (c • N - 1) a = -mv (1 - c • N) a := by
      rw [← neg_mv, neg_sub]
    rw [h2, h1]
    abel

/-- Woodford (2003), App. C.1, p. 670: the nilpotent block `N E_t q_{t+1} = (cN − 1) q_t + g_t`
(`g` in the range of `Q`) has exactly one bounded adapted solution in the range of `Q` — its
forward solution with the nilpotent matrix `K` (finitely many terms). -/
theorem pencilV_existsUnique {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ}
    (hF : Fitting N m P Q Ni) (c : ℝ) {g : ℕ → ι → Ω → ℝ} (hgQ : ∀ t, mv Q (g t) = g t)
    (hgb : BoundedV g) (hga : AdaptedV 𝔼 g) :
    (∃ q : ℕ → ι → Ω → ℝ, (∀ t, mv Q (q t) = q t) ∧
      (∀ t, mv N (fun i => 𝔼.E t (q (t + 1) i)) = mv (c • N - 1) (q t) + g t) ∧
      AdaptedV 𝔼 q ∧ BoundedV q) ∧
    ∀ q₁ q₂ : ℕ → ι → Ω → ℝ, (∀ t, mv Q (q₁ t) = q₁ t) →
      (∀ t, mv N (fun i => 𝔼.E t (q₁ (t + 1) i)) = mv (c • N - 1) (q₁ t) + g t) →
      AdaptedV 𝔼 q₁ → BoundedV q₁ → (∀ t, mv Q (q₂ t) = q₂ t) →
      (∀ t, mv N (fun i => 𝔼.E t (q₂ (t + 1) i)) = mv (c • N - 1) (q₂ t) + g t) →
      AdaptedV 𝔼 q₂ → BoundedV q₂ → q₁ = q₂ := by
  obtain ⟨-, -, -, -, hQK, hKQ, hQR⟩ := nil_facts hF c
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hK⟩ := pow_bound_of_pow_eq_zero (kmat_pow hF c)
  have hfb : BoundedV (fun t => mv (rmat c N m) (g t)) := boundedV_mv _ hgb
  have hfa : AdaptedV 𝔼 (fun t => mv (rmat c N m) (g t)) := adaptedV_mv 𝔼 _ hga
  -- the pencil equation for `Q`-invariant processes is the forward system
  have hiff : ∀ q : ℕ → ι → Ω → ℝ, (∀ t, mv Q (q t) = q t) →
      ((∀ t, mv N (fun i => 𝔼.E t (q (t + 1) i)) = mv (c • N - 1) (q t) + g t) ↔
        FSolves 𝔼 (kmat c N Q m) (fun t => mv (rmat c N m) (g t)) q) := by
    intro q hq
    have hEq : ∀ t, mv Q (fun i => 𝔼.E t (q (t + 1) i)) = fun i => 𝔼.E t (q (t + 1) i) := by
      intro t
      rw [← Enext_mv, hq]
    unfold FSolves
    exact forall_congr' fun t => pencilV_step hF c (hq t) (hgQ t) (hEq t)
  obtain ⟨Mf, hMf⟩ := hfb
  obtain ⟨s, hs, hsa, hsb⟩ := fsolves_exists 𝔼 hρ0.le hρ1 hK hMf hfa
  have hsQ : ∀ t, mv Q (s t) = s t := by
    have hs' : FSolves 𝔼 (kmat c N Q m) (fun t => mv (rmat c N m) (g t))
        (fun t => mv Q (s t)) := by
      intro t
      have e := congrArg (mv Q) (hs t)
      rw [mv_add, mv_mv, hQK, mv_mv, hQR, ← mv_mv, hgQ] at e
      change mv Q (s t) = mv (kmat c N Q m) (fun j => 𝔼.E t (mv Q (s (t + 1)) j)) +
        mv (rmat c N m) (g t)
      rw [e, Enext_mv, mv_mv, hKQ]
    have := fsolves_unique 𝔼 hρ0.le hρ1 hK hs' hs (adaptedV_mv 𝔼 Q hsa) hsa
      (boundedV_mv Q hsb) hsb
    exact fun t => congrFun this t
  refine ⟨⟨s, hsQ, (hiff s hsQ).mpr hs, hsa, hsb⟩, ?_⟩
  intro q₁ q₂ h1Q h1 h1a h1b h2Q h2 h2a h2b
  exact fsolves_unique 𝔼 hρ0.le hρ1 hK ((hiff q₁ h1Q).mp h1) ((hiff q₂ h2Q).mp h2) h1a h2a h1b h2b

/-! ### Pencil equilibria are standard-form equilibria -/

/-- Woodford (2003), App. C.1, p. 670: with `B = cA₀ − A₁` invertible and `N = B⁻¹A₀`, the pencil
equation `A₀ E_t y_{t+1} = A₁ y_t + w_t` is `N E_t y_{t+1} = (cN − 1) y_t + B⁻¹ w_t`. -/
theorem pencil_reduce {A0 A1 : Matrix ι ι ℝ} {c : ℝ} (hB : IsUnit (c • A0 - A1).det)
    (e y w : ι → Ω → ℝ) :
    mv A0 e = mv A1 y + w ↔
      mv ((c • A0 - A1)⁻¹ * A0) e = mv (c • ((c • A0 - A1)⁻¹ * A0) - 1) y +
        mv (c • A0 - A1)⁻¹ w := by
  set B := c • A0 - A1 with hBdef
  have hA1 : A1 = c • A0 - B := by rw [hBdef]; abel
  have h1 : B⁻¹ * A1 = c • (B⁻¹ * A0) - 1 := by
    rw [hA1, Matrix.mul_sub, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hB]
  have h2 : B * (c • (B⁻¹ * A0) - 1) = A1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_nonsing_inv_cancel_left _ _ hB,
      Matrix.mul_one, hA1]
  constructor
  · intro h
    have := congrArg (mv B⁻¹) h
    rwa [mv_mv, mv_add, mv_mv, h1] at this
  · intro h
    have := congrArg (mv B) h
    rwa [mv_mv, Matrix.mul_nonsing_inv_cancel_left _ _ hB, mv_add, mv_mv, h2, mv_mv,
      Matrix.mul_nonsing_inv _ hB, mv_one] at this

/-- Woodford (2003), App. C.1, p. 670: when the `Q` block of `y` is a process `q` solving both the
pencil's nilpotent block and the standard form's `2`-block, and the `P` parts of the forcings
agree, `y` solves the pencil system iff it solves `E_t y_{t+1} = Â y_t + ŵ_t`. -/
theorem pencil_iff_ahat {A0 A1 : Matrix ι ι ℝ} {c : ℝ} (hB : IsUnit (c • A0 - A1).det) {m : ℕ}
    {P Q Ni : Matrix ι ι ℝ} (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni)
    {w wh y q : ℕ → ι → Ω → ℝ}
    (hPw : ∀ t, mv P (wh t) = mv Ni (mv (c • A0 - A1)⁻¹ (w t)))
    (hq2 : ∀ t, (fun i => 𝔼.E t (q (t + 1) i)) = (2 : ℝ) • q t + mv Q (wh t))
    (hqN : ∀ t, mv ((c • A0 - A1)⁻¹ * A0) (fun i => 𝔼.E t (q (t + 1) i)) =
      mv (c • ((c • A0 - A1)⁻¹ * A0) - 1) (q t) + mv Q (mv (c • A0 - A1)⁻¹ (w t)))
    (hyq : ∀ t, mv Q (y t) = q t) :
    SolvesPencil 𝔼 A0 A1 w y ↔ Solves 𝔼 (ahat c P Q Ni) wh y := by
  have hEyq : ∀ t, mv Q (fun i => 𝔼.E t (y (t + 1) i)) = fun i => 𝔼.E t (q (t + 1) i) := by
    intro t
    rw [← Enext_mv, hyq]
  have hS : Solves 𝔼 (ahat c P Q Ni) wh y ↔
      ∀ t, (fun i => 𝔼.E t (y (t + 1) i)) = mv (ahat c P Q Ni) (y t) + wh t := by
    constructor
    · intro h t; funext i; exact h t i
    · intro h t i; exact congrFun (h t) i
  rw [hS]
  unfold SolvesPencil
  refine forall_congr' fun t => ?_
  rw [pencil_reduce hB, split_pencil hF, split_ahat hF, hPw, hEyq, hyq, hqN t, hq2 t, smul_mv,
    hyq]
  simp only [and_true]

/-- Woodford (2003), App. C.1, p. 670 (tool): a `Q`-image process is `Q`-invariant. -/
theorem mvQ_idem {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ} (hF : Fitting N m P Q Ni)
    (a : ι → Ω → ℝ) : mv Q (mv Q a) = mv Q a := by
  rw [mv_mv, hF.basic.2.1]

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, p. 670 (tool): the nilpotent-block part of a pencil solution. -/
theorem pencil_Vpart {A0 A1 : Matrix ι ι ℝ} {c : ℝ} (hB : IsUnit (c • A0 - A1).det) {m : ℕ}
    {P Q Ni : Matrix ι ι ℝ} (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni)
    {w y : ℕ → ι → Ω → ℝ} (hy : SolvesPencil 𝔼 A0 A1 w y) (t : ℕ) :
    mv ((c • A0 - A1)⁻¹ * A0) (fun i => 𝔼.E t (mv Q (y (t + 1)) i)) =
      mv (c • ((c • A0 - A1)⁻¹ * A0) - 1) (mv Q (y t)) + mv Q (mv (c • A0 - A1)⁻¹ (w t)) := by
  have h := ((split_pencil hF c _ _ _).mp ((pencil_reduce hB _ _ _).mp (hy t))).2
  rw [Enext_mv]
  exact h

/-- Woodford (2003), App. C.1, p. 670 (tool): the `2`-block part of a standard-form solution. -/
theorem ahat_Vpart {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ} (hF : Fitting N m P Q Ni)
    (c : ℝ) {wh y : ℕ → ι → Ω → ℝ} (hy : Solves 𝔼 (ahat c P Q Ni) wh y) (t : ℕ) :
    (fun i => 𝔼.E t (mv Q (y (t + 1)) i)) = (2 : ℝ) • mv Q (y t) + mv Q (wh t) := by
  have e : (fun i => 𝔼.E t (y (t + 1) i)) = mv (ahat c P Q Ni) (y t) + wh t := by
    funext i; exact hy t i
  have h := ((split_ahat hF c _ _ _).mp e).2
  rw [Enext_mv, h, smul_mv]

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- **Singular pencils reduce to standard form** (Woodford (2003), App. C.1, p. 670; King and
Watson (1998), Klein (2000)): if `det(cA₀ − A₁) ≠ 0` and `(P, Q, Ni)` is a Fitting decomposition
of `N = (cA₀ − A₁)⁻¹A₀`, the pencil system `A₀ E_t y_{t+1} = A₁ y_t + w_t` (with `A₀` possibly
singular) is determinate iff the standard-form system `E_t y_{t+1} = Â y_t + w_t` is,
`Â = cP − Ni + 2Q`. -/
theorem determinatePencil_iff_ahat {A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} {c : ℝ}
    (hB : IsUnit (c • A0 - A1).det) {m : ℕ} {P Q Ni : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni) :
    DeterminatePencil 𝔼 A0 A1 ↔ Determinate 𝔼 (ahat c P Q Ni) := by
  set B := c • A0 - A1 with hBdef
  set N := B⁻¹ * A0 with hN
  obtain ⟨hPP, hQQ, hPNi, hQNP⟩ := hF.basic
  have hFc := hF
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩ := hFc
  have hNiA : Ni * (c • N - 1) = c • P - Ni := by
    rw [Matrix.mul_sub, Matrix.mul_smul, h7, Matrix.mul_one]
  have hQA : Q * (c • N - 1) = (c • N - 1) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h5, Matrix.mul_one,
      Matrix.one_mul]
  have hPq : ∀ a : Z ⊕ X → Ω → ℝ, mv Q a = a → mv P a = 0 := fun a ha => by
    rw [← ha, mv_mv, h2, zero_mv]
  have hNiq : ∀ a : Z ⊕ X → Ω → ℝ, mv Q a = a → mv Ni a = 0 := fun a ha => by
    rw [← ha, mv_mv, h9, zero_mv]
  have hQidem : ∀ a : Z ⊕ X → Ω → ℝ, mv Q (mv Q a) = mv Q a := fun a => by rw [mv_mv, hQQ]
  have hEQ : ∀ (q : ℕ → Z ⊕ X → Ω → ℝ) t, (∀ t, mv Q (q t) = q t) →
      mv Q (fun i => 𝔼.E t (q (t + 1) i)) = fun i => 𝔼.E t (q (t + 1) i) := by
    intro q t hq
    rw [← Enext_mv, hq]
  constructor
  · -- pencil determinacy gives standard-form determinacy
    intro hd wh hwb hwa x0
    obtain ⟨q, ⟨hq2, hqa, hqb⟩, hqu⟩ :=
      twoBlock_existsUnique 𝔼 (boundedV_mv Q hwb) (adaptedV_mv 𝔼 Q hwa)
    have hqQ : ∀ t, mv Q (q t) = q t := by
      have h' : (fun t => mv Q (q t)) = q := by
        refine hqu _ ⟨fun t => ?_, adaptedV_mv 𝔼 Q hqa, boundedV_mv Q hqb⟩
        change (fun i => 𝔼.E t (mv Q (q (t + 1)) i)) = (2 : ℝ) • mv Q (q t) + mv Q (wh t)
        rw [Enext_mv, hq2 t, mv_add, mv_smul, hQidem]
      exact fun t => congrFun h' t
    set wt : ℕ → Z ⊕ X → Ω → ℝ := fun t => mv N (mv P (wh t)) +
      (mv N (fun i => 𝔼.E t (q (t + 1) i)) - mv (c • N - 1) (q t)) with hwt
    have hwtb : BoundedV wt := boundedV_add (boundedV_mv N (boundedV_mv P hwb))
      (boundedV_sub (boundedV_mv N (boundedV_Enext 𝔼 hqb)) (boundedV_mv _ hqb))
    have hwta : AdaptedV 𝔼 wt := adaptedV_add 𝔼 (adaptedV_mv 𝔼 N (adaptedV_mv 𝔼 P hwa))
      (adaptedV_sub 𝔼 (adaptedV_mv 𝔼 N (adaptedV_Enext 𝔼 q)) (adaptedV_mv 𝔼 _ hqa))
    have hBw : ∀ t, mv B⁻¹ (mv B (wt t)) = wt t := fun t => by
      rw [mv_mv, Matrix.nonsing_inv_mul _ hB, mv_one]
    have hPw : ∀ t, mv P (wh t) = mv Ni (mv B⁻¹ (mv B (wt t))) := by
      intro t
      rw [hBw, hwt]
      simp only
      rw [mv_add, mv_sub, mv_mv N P, mv_mv Ni (N * P), ← Matrix.mul_assoc Ni N P, h7, hPP,
        mv_mv Ni N, h7, hPq _ (hEQ q t hqQ), mv_mv Ni (c • N - 1), hNiA, sub_mv, smul_mv,
        hPq _ (hqQ t), hNiq _ (hqQ t), smul_zero, sub_zero, sub_zero, add_zero]
    have hqN : ∀ t, mv N (fun i => 𝔼.E t (q (t + 1) i)) =
        mv (c • N - 1) (q t) + mv Q (mv B⁻¹ (mv B (wt t))) := by
      intro t
      rw [hBw, hwt]
      simp only
      have e1 : mv Q (mv N (mv P (wh t))) = 0 := by
        rw [mv_mv N P, mv_mv Q (N * P), ← Matrix.mul_assoc Q N P, hQNP, zero_mv]
      have e2 : mv Q (mv N (fun i => 𝔼.E t (q (t + 1) i))) =
          mv N (fun i => 𝔼.E t (q (t + 1) i)) := by
        rw [mv_mv Q N, ← h5, ← mv_mv N Q, hEQ q t hqQ]
      have e3 : mv Q (mv (c • N - 1) (q t)) = mv (c • N - 1) (q t) := by
        rw [mv_mv Q (c • N - 1), hQA, ← mv_mv (c • N - 1) Q, hqQ t]
      rw [mv_add, mv_sub, e1, e2, e3, zero_add]
      abel
    obtain ⟨y, hy, hyu⟩ := hd (fun t => mv B (wt t)) (boundedV_mv B hwtb)
      (adaptedV_mv 𝔼 B hwta) x0
    have hgb : BoundedV (fun t => mv Q (mv B⁻¹ (mv B (wt t)))) :=
      boundedV_mv Q (boundedV_mv _ (boundedV_mv B hwtb))
    have hga : AdaptedV 𝔼 (fun t => mv Q (mv B⁻¹ (mv B (wt t)))) :=
      adaptedV_mv 𝔼 Q (adaptedV_mv 𝔼 _ (adaptedV_mv 𝔼 B hwta))
    have hVu := (pencilV_existsUnique 𝔼 hF c (g := fun t => mv Q (mv B⁻¹ (mv B (wt t))))
      (fun t => hQidem _) hgb hga).2
    have hyq : ∀ t, mv Q (y t) = q t := by
      have := hVu (fun t => mv Q (y t)) q (fun t => hQidem _)
        (fun t => pencil_Vpart 𝔼 hB hF hy.1 t) (adaptedV_mv 𝔼 Q hy.2.1)
        (boundedV_mv Q hy.2.2.2.2) hqQ hqN hqa hqb
      exact fun t => congrFun this t
    refine ⟨y, ⟨(pencil_iff_ahat 𝔼 hB hF (w := fun t => mv B (wt t)) hPw hq2 hqN hyq).mp hy.1,
      hy.2⟩, fun y'' hy'' => ?_⟩
    have hyq'' : ∀ t, mv Q (y'' t) = q t := by
      have := hqu (fun t => mv Q (y'' t)) ⟨fun t => ahat_Vpart 𝔼 hF c hy''.1 t,
        adaptedV_mv 𝔼 Q hy''.2.1, boundedV_mv Q hy''.2.2.2.2⟩
      exact fun t => congrFun this t
    exact hyu y'' ⟨(pencil_iff_ahat 𝔼 hB hF (w := fun t => mv B (wt t)) hPw hq2 hqN
      hyq'').mpr hy''.1, hy''.2⟩
  · -- standard-form determinacy gives pencil determinacy
    intro hd w hwb hwa x0
    have hgQ : ∀ t, mv Q (mv Q (mv B⁻¹ (w t))) = mv Q (mv B⁻¹ (w t)) := fun t => hQidem _
    have hgb : BoundedV (fun t => mv Q (mv B⁻¹ (w t))) := boundedV_mv Q (boundedV_mv _ hwb)
    have hga : AdaptedV 𝔼 (fun t => mv Q (mv B⁻¹ (w t))) :=
      adaptedV_mv 𝔼 Q (adaptedV_mv 𝔼 _ hwa)
    obtain ⟨⟨s, hsQ, hs, hsa, hsb⟩, hsu⟩ := pencilV_existsUnique 𝔼 hF c hgQ hgb hga
    set wh : ℕ → Z ⊕ X → Ω → ℝ := fun t => mv Ni (mv B⁻¹ (w t)) +
      ((fun i => 𝔼.E t (s (t + 1) i)) - (2 : ℝ) • s t) with hwh
    have hwhb : BoundedV wh := boundedV_add (boundedV_mv Ni (boundedV_mv _ hwb))
      (boundedV_sub (boundedV_Enext 𝔼 hsb) (boundedV_smul 2 hsb))
    have hwha : AdaptedV 𝔼 wh := adaptedV_add 𝔼 (adaptedV_mv 𝔼 Ni (adaptedV_mv 𝔼 _ hwa))
      (adaptedV_sub 𝔼 (adaptedV_Enext 𝔼 s) (adaptedV_smul 𝔼 2 hsa))
    have hPw : ∀ t, mv P (wh t) = mv Ni (mv B⁻¹ (w t)) := by
      intro t
      simp only [hwh]
      rw [mv_add, mv_sub, mv_mv P Ni, hPNi, hPq _ (hEQ s t hsQ), mv_smul, hPq _ (hsQ t),
        smul_zero, sub_zero, add_zero]
    have hq2 : ∀ t, (fun i => 𝔼.E t (s (t + 1) i)) = (2 : ℝ) • s t + mv Q (wh t) := by
      intro t
      simp only [hwh]
      rw [mv_add, mv_sub, mv_mv Q Ni, h8, zero_mv, hEQ s t hsQ, mv_smul, hsQ t]
      abel
    obtain ⟨y, hy, hyu⟩ := hd wh hwhb hwha x0
    have h2u := twoBlock_existsUnique 𝔼 (boundedV_mv Q hwhb) (adaptedV_mv 𝔼 Q hwha)
    have hyq : ∀ t, mv Q (y t) = s t := by
      have := h2u.unique ⟨fun t => ahat_Vpart 𝔼 hF c hy.1 t, adaptedV_mv 𝔼 Q hy.2.1,
        boundedV_mv Q hy.2.2.2.2⟩ ⟨hq2, hsa, hsb⟩
      exact fun t => congrFun this t
    refine ⟨y, ⟨(pencil_iff_ahat 𝔼 hB hF hPw hq2 hs hyq).mpr hy.1, hy.2⟩, fun y'' hy'' => ?_⟩
    have hyq'' : ∀ t, mv Q (y'' t) = s t := by
      have := hsu (fun t => mv Q (y'' t)) s (fun t => hQidem _)
        (fun t => pencil_Vpart 𝔼 hB hF hy''.1 t) (adaptedV_mv 𝔼 Q hy''.2.1)
        (boundedV_mv Q hy''.2.2.2.2) hsQ hs hsa hsb
      exact fun t => congrFun this t
    exact hyu y'' ⟨(pencil_iff_ahat 𝔼 hB hF hPw hq2 hs hyq'').mp hy''.1, hy''.2⟩

/-! ### The generalised eigenvalues -/

/-- Woodford (2003), App. C.1, p. 670 (tool): an element commuting with complementary
idempotents `p`, `q` factors as `x = (xp + q)(p + xq)`. -/
theorem factor_idem {R : Type*} [Ring R] {x p q : R} (h1 : p + q = 1) (hpq : p * q = 0)
    (hqp : q * p = 0) (hpp : p * p = p) (hqq : q * q = q) (hxp : x * p = p * x)
    (hxq : x * q = q * x) : x = (x * p + q) * (p + x * q) := by
  have e1 : x * p * p = x * p := by rw [mul_assoc, hpp]
  have e2 : x * p * (x * q) = 0 := by
    rw [mul_assoc, ← mul_assoc p x q, ← hxp, mul_assoc x p q, hpq, mul_zero, mul_zero]
  have e3 : q * (x * q) = x * q := by rw [← mul_assoc, ← hxq, mul_assoc, hqq]
  rw [add_mul, mul_add, mul_add, e1, e2, hqp, e3, add_zero, zero_add, ← mul_add, h1, mul_one]

/-- Woodford (2003), App. C.1, p. 670 (tool): `det(1 + sM) = 1` for nilpotent `M`. -/
theorem det_one_add_smul_nilpotent {M : Matrix ι ι ℝ} (hM : IsNilpotent M) (s : ℝ) :
    (1 + s • M).det = 1 := by
  obtain ⟨r, hr, hrp⟩ := Polynomial.isUnit_iff.mp (Matrix.isUnit_charpolyRev_of_isNilpotent hM)
  have h0 := Matrix.eval_charpolyRev (M := M)
  rw [← hrp, eval_C] at h0
  have hcr : M.charpolyRev = 1 := by rw [← hrp, h0, C_1]
  have e : (1 + s • M).det = M.charpolyRev.eval (-s) := by
    rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst hij; simp [mul_comm s]
    · simp [Matrix.one_apply_ne hij, mul_comm s]
  rw [e, hcr, eval_one]

/-- Woodford (2003), App. C.1, p. 670: the factor `det((λ − Â)P + Q)` of the characteristic
polynomial of `Â` — the finite generalised eigenvalues. -/
noncomputable def fpoly (A P Q : Matrix ι ι ℝ) : ℝ[X] :=
  (A.charmatrix * (C : ℝ →+* ℝ[X]).mapMatrix P + (C : ℝ →+* ℝ[X]).mapMatrix Q).det

/-- Woodford (2003), App. C.1, p. 670: the factor `det(P + (λ − 2)Q)` of the characteristic
polynomial of `Â` — the placeholder value `2` for the infinite generalised eigenvalues. -/
noncomputable def gpoly (P Q : Matrix ι ι ℝ) : ℝ[X] :=
  ((C : ℝ →+* ℝ[X]).mapMatrix P +
    Matrix.scalar ι (Polynomial.X - C 2 : ℝ[X]) * (C : ℝ →+* ℝ[X]).mapMatrix Q).det

/-- Woodford (2003), App. C.1, p. 670 (tool): evaluating the determinant of a polynomial matrix. -/
theorem eval_det_mapMatrix (M : Matrix ι ι ℝ[X]) (r : ℝ) :
    M.det.eval r = ((evalRingHom r).mapMatrix M).det := by
  rw [← coe_evalRingHom, RingHom.map_det]

/-- Woodford (2003), App. C.1, p. 670 (tool): `f(r) = det((r − Â)P + Q)`. -/
theorem eval_fpoly (A P Q : Matrix ι ι ℝ) (r : ℝ) :
    (fpoly A P Q).eval r = ((r • 1 - A) * P + Q).det := by
  rw [fpoly, eval_det_mapMatrix]
  congr 1
  rw [map_add, map_mul]
  congr 2
  · ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Matrix.one_apply_ne hij]
  · ext i j; simp
  · ext i j; simp

/-- Woodford (2003), App. C.1, p. 670 (tool): `g(r) = det(P + (r − 2)Q)`. -/
theorem eval_gpoly (P Q : Matrix ι ι ℝ) (r : ℝ) :
    (gpoly P Q).eval r = (P + (r - 2) • Q).det := by
  rw [gpoly, eval_det_mapMatrix]
  congr 1
  rw [map_add, map_mul]
  congr 1
  · ext i j; simp
  · ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): `det(rA₀ − A₁)` as the value of `pencilPoly`. -/
theorem eval_pencilPoly (A0 A1 : Matrix ι ι ℝ) (r : ℝ) :
    (pencilPoly A0 A1).eval r = (r • A0 - A1).det := by
  rw [pencilPoly, eval_det_mapMatrix]
  congr 1
  rw [map_sub, map_mul]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): `Â` commutes with `P` and `Q`: `ÂP = PÂ = cP − Ni`,
`ÂQ = QÂ = 2Q`. -/
theorem ahat_comm {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ} (hF : Fitting N m P Q Ni)
    (c : ℝ) : ahat c P Q Ni * P = c • P - Ni ∧ ahat c P Q Ni * Q = (2 : ℝ) • Q ∧
      P * ahat c P Q Ni = c • P - Ni ∧ Q * ahat c P Q Ni = (2 : ℝ) • Q := by
  obtain ⟨hPP, hQQ, -, -⟩ := hF.basic
  obtain ⟨hPA, hQA⟩ := ahat_proj hF c
  obtain ⟨h1, h2, h3, -, -, -, -, -, h9, -⟩ := hF
  have hNiP : Ni * P = Ni := by
    calc Ni * P = Ni * (P + Q) := by rw [Matrix.mul_add, h9, add_zero]
      _ = Ni := by rw [h1, Matrix.mul_one]
  refine ⟨?_, ?_, hPA, hQA⟩
  · rw [ahat, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hPP, hNiP, h3,
      smul_zero, add_zero]
  · rw [ahat, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, h2, h9, hQQ,
      smul_zero, zero_sub, neg_zero, zero_add]

/-- Woodford (2003), App. C.1, p. 670 (tool): `scalar r = r • 1`. -/
theorem scalar_eq_smul_one (r : ℝ) : Matrix.scalar ι r = r • (1 : Matrix ι ι ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Matrix.one_apply_ne hij]

/-- **The characteristic polynomials** (Woodford (2003), App. C.1, p. 670; King and Watson (1998),
Klein (2000)): `det(λA₀ − A₁) = κ f(λ)` with `κ = det(cA₀ − A₁) det(NP + Q) ≠ 0`, and
`det(λ − Â) = f(λ) g(λ)`. -/
theorem poly_relations {A0 A1 : Matrix ι ι ℝ} {c : ℝ} (hB : IsUnit (c • A0 - A1).det) {m : ℕ}
    {P Q Ni : Matrix ι ι ℝ} (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni) :
    pencilPoly A0 A1 = C ((c • A0 - A1).det * ((c • A0 - A1)⁻¹ * A0 * P + Q).det) *
        fpoly (ahat c P Q Ni) P Q ∧
      (ahat c P Q Ni).charpoly = fpoly (ahat c P Q Ni) P Q * gpoly P Q := by
  set B := c • A0 - A1 with hBdef
  set N := B⁻¹ * A0 with hN
  set Ah := ahat c P Q Ni with hAh
  obtain ⟨hPP, hQQ, hPNi, hQNP⟩ := hF.basic
  obtain ⟨hAP, hAQ, hPA, hQA⟩ := ahat_comm hF c
  have hFc := hF
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hFc
  -- the factor `det((r − Â)P + Q) · det(P + (r − 2)Q)` of `det(r − Â)`
  have hfac1 : ∀ r : ℝ, (r • 1 - Ah).det =
      ((r • 1 - Ah) * P + Q).det * (P + (r - 2) • Q).det := by
    intro r
    have hxp : (r • 1 - Ah) * P = P * (r • 1 - Ah) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hAP, hPA]
    have hxq : (r • 1 - Ah) * Q = Q * (r • 1 - Ah) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hAQ, hQA]
    have hq2 : (r • 1 - Ah) * Q = (r - 2) • Q := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hAQ, sub_smul]
    conv_lhs => rw [factor_idem h1 h2 h3 hPP hQQ hxp hxq]
    rw [Matrix.det_mul, hq2]
  -- `NQ` is nilpotent
  have hNQ : IsNilpotent (N * Q) := by
    refine ⟨m + 1, ?_⟩
    rw [(show Commute N Q from h5).mul_pow, pow_succ', pow_succ', Matrix.mul_assoc,
      ← Matrix.mul_assoc (N ^ m), h10, Matrix.zero_mul, Matrix.mul_zero]
  -- the factor of `det(rA₀ − A₁)`
  have hfac2 : ∀ r : ℝ, (r • A0 - A1).det =
      B.det * (N * P + Q).det * ((r • 1 - Ah) * P + Q).det := by
    intro r
    set Y := (r - c) • N + 1 with hY
    have hBY : r • A0 - A1 = B * Y := by
      rw [hY, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, hN,
        Matrix.mul_nonsing_inv_cancel_left _ _ hB, hBdef, sub_smul]
      abel
    have hyp : Y * P = P * Y := by
      rw [hY, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, h4,
        Matrix.one_mul, Matrix.mul_one]
    have hyq : Y * Q = Q * Y := by
      rw [hY, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, h5,
        Matrix.one_mul, Matrix.mul_one]
    have hdet1 : (P + Y * Q).det = 1 := by
      have : P + Y * Q = 1 + (r - c) • (N * Q) := by
        rw [hY, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, ← h1]
        abel
      rw [this, det_one_add_smul_nilpotent hNQ]
    have hD : Y * P + Q = (N * P + Q) * ((r • 1 - Ah) * P + Q) := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hAP, hY]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, Matrix.one_mul, hPP, hPNi, h6, h2, h3,
        h8, hQQ, Matrix.mul_zero, add_zero, zero_add, sub_smul]
      abel
    rw [hBY, Matrix.det_mul, factor_idem h1 h2 h3 hPP hQQ hyp hyq, Matrix.det_mul, hdet1,
      mul_one, hD, Matrix.det_mul, ← mul_assoc]
  constructor
  · refine Polynomial.funext fun r => ?_
    rw [eval_pencilPoly, eval_mul, eval_C, eval_fpoly, hfac2]
  · refine Polynomial.funext fun r => ?_
    rw [Matrix.eval_charpoly, eval_mul, eval_fpoly, eval_gpoly, scalar_eq_smul_one, hfac1]

/-- Woodford (2003), App. C.1, p. 670 (tool): `NP + Q` is invertible, with inverse `Ni + Q`. -/
theorem det_NPQ_ne_zero {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ}
    (hF : Fitting N m P Q Ni) : (N * P + Q).det ≠ 0 := by
  obtain ⟨-, hQQ, hPNi, -⟩ := hF.basic
  obtain ⟨h1, h2, -, -, -, h6, -, h8, -, -⟩ := hF
  have h : (N * P + Q) * (Ni + Q) = 1 := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_assoc, hPNi, h6,
      Matrix.mul_assoc, h2, Matrix.mul_zero, h8, hQQ, add_zero, zero_add, h1]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- Woodford (2003), App. C.1, p. 670 (tool): every complex root of `g(λ) = det(P + (λ − 2)Q)` is
`2`. -/
theorem gpoly_roots {N : Matrix ι ι ℝ} {m : ℕ} {P Q Ni : Matrix ι ι ℝ}
    (hF : Fitting N m P Q Ni) : ∀ μ ∈ ((gpoly P Q).map Complex.ofRealHom).roots, μ = 2 := by
  obtain ⟨hPP, hQQ, -, -⟩ := hF.basic
  obtain ⟨h1, h2, h3, -⟩ := hF
  intro μ hμ
  have hne : (gpoly P Q).map Complex.ofRealHom ≠ 0 := fun h0 => by simp [h0] at hμ
  rw [mem_roots hne, IsRoot, eval_map, ← coe_eval₂RingHom, gpoly, RingHom.map_det] at hμ
  set Pc := P.map Complex.ofReal with hPc
  set Qc := Q.map Complex.ofReal with hQc
  have hmap : (eval₂RingHom Complex.ofRealHom μ).mapMatrix
      ((C : ℝ →+* ℝ[X]).mapMatrix P +
        Matrix.scalar ι (Polynomial.X - C 2 : ℝ[X]) * (C : ℝ →+* ℝ[X]).mapMatrix Q) =
      Pc + (μ - 2) • Qc := by
    ext i j
    simp [hPc, hQc, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.smul_apply]
  rw [hmap] at hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  have hm : ∀ M M' : Matrix ι ι ℝ, (M * M').map Complex.ofReal =
      M.map Complex.ofReal * M'.map Complex.ofReal := fun M M' =>
    Matrix.map_mul (f := Complex.ofRealHom)
  have hPPc : Pc * Pc = Pc := by rw [hPc, ← hm, hPP]
  have hQQc : Qc * Qc = Qc := by rw [hQc, ← hm, hQQ]
  have hPQc : Pc * Qc = 0 := by rw [hPc, hQc, ← hm, h2, Matrix.map_zero _ (by simp)]
  have hQPc : Qc * Pc = 0 := by rw [hPc, hQc, ← hm, h3, Matrix.map_zero _ (by simp)]
  have h1c : Pc + Qc = 1 := by
    rw [hPc, hQc, ← Matrix.map_add _ (by simp), h1]
    exact Matrix.map_one _ (by simp) (by simp)
  have hPv : Pc *ᵥ v = 0 := by
    have := congrArg (Pc *ᵥ ·) hv
    simp only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.mul_add, Matrix.mul_smul,
      hPPc, hPQc, smul_zero, add_zero] at this
    exact this
  have hQv : (μ - 2) • (Qc *ᵥ v) = 0 := by
    have := congrArg (Qc *ᵥ ·) hv
    simp only [Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.mul_add, Matrix.mul_smul,
      hQPc, hQQc, zero_add, Matrix.smul_mulVec] at this
    exact this
  by_contra h2'
  have hQv' : Qc *ᵥ v = 0 := (smul_eq_zero.mp hQv).resolve_left (sub_ne_zero.mpr h2')
  apply hv0
  rw [← Matrix.one_mulVec v, ← h1c, Matrix.add_mulVec, hPv, hQv', add_zero]

/-- Woodford (2003), App. C.1, p. 670: the eigenvalues of `Â`, with multiplicity, are the roots of
`det(λA₀ − A₁)` together with copies of the placeholder `2`. -/
theorem eigs_ahat {A0 A1 : Matrix ι ι ℝ} {c : ℝ} (hB : IsUnit (c • A0 - A1).det) {m : ℕ}
    {P Q Ni : Matrix ι ι ℝ} (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni) :
    eigs (ahat c P Q Ni) = ((pencilPoly A0 A1).map Complex.ofRealHom).roots +
      ((gpoly P Q).map Complex.ofRealHom).roots := by
  obtain ⟨hp, hc⟩ := poly_relations hB hF
  have hκ : (Complex.ofRealHom ((c • A0 - A1).det * ((c • A0 - A1)⁻¹ * A0 * P + Q).det)) ≠ 0 := by
    simpa using mul_ne_zero hB.ne_zero (det_NPQ_ne_zero hF)
  have hne : (fpoly (ahat c P Q Ni) P Q).map Complex.ofRealHom *
      (gpoly P Q).map Complex.ofRealHom ≠ 0 := by
    rw [← Polynomial.map_mul, ← hc]
    exact ((Matrix.charpoly_monic _).map _).ne_zero
  rw [eigs, charpoly_map_ofReal, hc, Polynomial.map_mul, roots_mul hne, hp, Polynomial.map_mul,
    Polynomial.map_C, roots_C_mul _ hκ]

/-- Woodford (2003), App. C.1, p. 670: no eigenvalue of `Â` on the unit circle iff no root of
`det(λA₀ − A₁)` on it. -/
theorem noUnit_ahat_iff {A0 A1 : Matrix ι ι ℝ} {c : ℝ} (hB : IsUnit (c • A0 - A1).det) {m : ℕ}
    {P Q Ni : Matrix ι ι ℝ} (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni) :
    NoUnit (ahat c P Q Ni) ↔ ∀ μ ∈ ((pencilPoly A0 A1).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1 := by
  rw [NoUnit, eigs_ahat hB hF]
  constructor
  · intro h μ hμ
    exact h μ (Multiset.mem_add.mpr (Or.inl hμ))
  · intro h μ hμ
    rcases Multiset.mem_add.mp hμ with h1 | h2
    · exact h μ h1
    · rw [gpoly_roots hF μ h2]
      norm_num

/-- Woodford (2003), App. C.1, p. 670: the eigenvalues of `Â` in the open unit disc are the roots
of `det(λA₀ − A₁)` there, with multiplicity. -/
theorem stableCount_ahat {A0 A1 : Matrix ι ι ℝ} {c : ℝ} (hB : IsUnit (c • A0 - A1).det)
    {m : ℕ} {P Q Ni : Matrix ι ι ℝ} (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni) :
    stableCount (ahat c P Q Ni) =
      Multiset.card (((pencilPoly A0 A1).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) := by
  have hg0 : ((gpoly P Q).map Complex.ofRealHom).roots.filter (fun μ => ‖μ‖ < 1) = 0 :=
    Multiset.filter_eq_nil.mpr (fun μ hμ => by rw [gpoly_roots hF μ hμ]; norm_num)
  rw [stableCount, eigs_ahat hB hF, Multiset.filter_add, hg0, add_zero]

/-- Woodford (2003), App. C.1, p. 670: `v` starts a bounded deterministic solution of
`A₀ y_{t+1} = A₁ y_t`. -/
def PencilBounded (A0 A1 : Matrix ι ι ℝ) (v : ι → ℝ) : Prop :=
  ∃ y : ℕ → ι → ℝ, y 0 = v ∧ (∃ C, ∀ t i, |y t i| ≤ C) ∧ ∀ t, A0 *ᵥ y (t + 1) = A1 *ᵥ y t

/-- Woodford (2003), App. C.1, p. 670: the bounded orbits of `Â` are exactly the initial values of
bounded deterministic solutions of the pencil system `A₀ y_{t+1} = A₁ y_t` — the stable deflating
subspace of the pencil. -/
theorem mem_boundedOrbits_ahat {A0 A1 : Matrix ι ι ℝ} {c : ℝ} (hB : IsUnit (c • A0 - A1).det)
    {m : ℕ} {P Q Ni : Matrix ι ι ℝ} (hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni)
    (v : ι → ℝ) : v ∈ boundedOrbits (ahat c P Q Ni) ↔ PencilBounded A0 A1 v := by
  set B := c • A0 - A1 with hBdef
  set N := B⁻¹ * A0 with hN
  set Ah := ahat c P Q Ni with hAh
  obtain ⟨hPP, hQQ, hPNi, -⟩ := hF.basic
  obtain ⟨hAP, hAQ, -, hQA⟩ := ahat_comm hF c
  obtain ⟨hRm, -, hz, -, -, hKQ, hQR⟩ := nil_facts hF c
  have hKpow := kmat_pow hF c
  have hFc := hF
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hFc
  have hBN : B * N = A0 := Matrix.mul_nonsing_inv_cancel_left _ _ hB
  have hBA : B * (c • N - 1) = A1 := by
    rw [Matrix.mul_sub, Matrix.mul_smul, hBN, Matrix.mul_one, hBdef]; abel
  have hred : ∀ a b : ι → ℝ, A0 *ᵥ a = A1 *ᵥ b ↔ N *ᵥ a = (c • N - 1) *ᵥ b := by
    intro a b
    constructor
    · intro h
      have := congrArg (B⁻¹ *ᵥ ·) h
      simp only [Matrix.mulVec_mulVec] at this
      rw [← hBA, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul] at this
      exact this
    · intro h
      rw [← hBN, ← hBA, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_mulVec]
  constructor
  · rintro ⟨C, hC⟩
    -- the `Q` component of a bounded orbit vanishes
    have hQpow : ∀ t, Q * Ah ^ t = (2 : ℝ) ^ t • Q := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, hQA, smul_smul, pow_succ]
    have hQv : Q *ᵥ v = 0 := by
      funext i
      by_contra hi
      have hb : ∀ t : ℕ, ‖(2 : ℂ) ^ t * ((Q *ᵥ v) i : ℂ)‖ ≤
          Fintype.card ι * ((∑ i, ∑ j, |Q i j|) * C) := by
        intro t
        have e : (Q *ᵥ (Ah ^ t *ᵥ v)) i = 2 ^ t * (Q *ᵥ v) i := by
          rw [Matrix.mulVec_mulVec, hQpow, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
        rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.norm_real,
          Real.norm_eq_abs, ← e]
        exact InvariantSplit.abs_mulVec_le Q _ (InvariantSplit.abs_entry_le_sum Q) (hC t) i
      have := norm_le_one_of_bounded_pow_mul (by exact_mod_cast hi) hb
      norm_num at this
    have hQy : ∀ t, Q *ᵥ (Ah ^ t *ᵥ v) = 0 := by
      intro t
      rw [Matrix.mulVec_mulVec, hQpow, Matrix.smul_mulVec, hQv, smul_zero]
    refine ⟨fun t => Ah ^ t *ᵥ v, by simp, ⟨C, hC⟩, fun t => (hred _ _).mpr ?_⟩
    change N *ᵥ (Ah ^ (t + 1) *ᵥ v) = (c • N - 1) *ᵥ (Ah ^ t *ᵥ v)
    rw [pow_succ', ← Matrix.mulVec_mulVec v Ah (Ah ^ t),
      Matrix.mulVec_mulVec (Ah ^ t *ᵥ v) N Ah]
    set u := Ah ^ t *ᵥ v with hu
    have hPu : P *ᵥ u = u := by
      conv_rhs => rw [← Matrix.one_mulVec u, ← h1, Matrix.add_mulVec, hQy t, add_zero]
    have hNA : N * Ah = c • (N * P) - P + (2 : ℝ) • (N * Q) := by
      rw [hAh, ahat, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, h6]
    rw [hNA, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec u N P, ← Matrix.mulVec_mulVec u N Q, hQy t, Matrix.mulVec_zero,
      smul_zero, add_zero, hPu, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  · rintro ⟨y, hy0, ⟨C, hC⟩, hy⟩
    have hNy : ∀ t, N *ᵥ y (t + 1) = (c • N - 1) *ᵥ y t := fun t => (hred _ _).mp (hy t)
    -- the `Q` component: `Q y_t = K Q y_{t+1}`, and `K` is nilpotent
    have hRQN : rmat c N m * Q * N = -kmat c N Q m := by
      rw [kmat, neg_neg, Matrix.mul_assoc, ← h5, ← Matrix.mul_assoc]
    have hQc : Q * (c • N - 1) = (c • N - 1) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h5, Matrix.mul_one,
        Matrix.one_mul]
    have hRQA : rmat c N m * Q * (c • N - 1) = -Q := by
      calc rmat c N m * Q * (c • N - 1) = rmat c N m * ((c • N - 1) * Q) := by
            rw [Matrix.mul_assoc, hQc]
        _ = -(rmat c N m * (1 - c • N) * Q) := by
            rw [← neg_sub (1 : Matrix ι ι ℝ) (c • N), Matrix.neg_mul, Matrix.mul_neg,
              Matrix.mul_assoc]
        _ = -Q := by rw [hRm, Matrix.sub_mul, Matrix.one_mul, hz, sub_zero]
    have hKP : kmat c N Q m * P = 0 := by
      rw [kmat, Matrix.neg_mul, Matrix.mul_assoc, h3, Matrix.mul_zero, neg_zero]
    have hQstep : ∀ t, Q *ᵥ y t = kmat c N Q m *ᵥ (Q *ᵥ y (t + 1)) := by
      intro t
      have e := congrArg ((rmat c N m * Q) *ᵥ ·) (hNy t)
      simp only [Matrix.mulVec_mulVec] at e
      rw [hRQN, hRQA, Matrix.neg_mulVec, Matrix.neg_mulVec, neg_inj] at e
      rw [← e, Matrix.mulVec_mulVec, hKQ]
    have hQiter : ∀ k t, Q *ᵥ y t = kmat c N Q m ^ k *ᵥ (Q *ᵥ y (t + k)) := by
      intro k
      induction k with
      | zero => intro t; simp
      | succ k ih =>
        intro t
        rw [ih t, hQstep (t + k), Matrix.mulVec_mulVec, ← pow_succ, show t + k + 1 = t + (k + 1)
          by omega]
    have hQ0 : ∀ t, Q *ᵥ y t = 0 := fun t => by
      rw [hQiter (m + 1) t, hKpow, Matrix.zero_mulVec]
    -- the `P` component: `P y_{t+1} = (cP − Ni) y_t`, so `y_{t+1} = Â y_t`
    have hstep : ∀ t, y (t + 1) = Ah *ᵥ y t := by
      intro t
      have hP : P *ᵥ y (t + 1) = (c • P - Ni) *ᵥ y t := by
        have e := congrArg (Ni *ᵥ ·) (hNy t)
        simp only [Matrix.mulVec_mulVec] at e
        rw [h7, Matrix.mul_sub, Matrix.mul_smul, h7, Matrix.mul_one] at e
        exact e
      calc y (t + 1) = P *ᵥ y (t + 1) + Q *ᵥ y (t + 1) := by
            rw [← Matrix.add_mulVec, h1, Matrix.one_mulVec]
        _ = (c • P - Ni) *ᵥ y t + (2 : ℝ) • (Q *ᵥ y t) := by
            rw [hP, hQ0, hQ0, smul_zero]
        _ = Ah *ᵥ y t := by
            rw [hAh, ahat, Matrix.add_mulVec, Matrix.smul_mulVec]
    rw [← hy0]
    exact mem_boundedOrbits_of_orbit hstep hC

/-! ### Singular pencils: non-existence -/

/-- **A singular pencil admits no solution for some forcing** (Woodford (2003), App. C.1, p. 670;
King and Watson (1998)): if `det(λA₀ − A₁) ≡ 0`, a polynomial left null vector
`q(λ) = ∑ q_k λᵏ` of `λA₀ − A₁` makes `∑_k q_k · w_{t+k}` vanish along every solution, so the
bounded deterministic forcing `w_t = ρᵗ q(ρ)` (some `ρ ∈ [0, 1]` with `q(ρ) ≠ 0`) has no
solution at all. -/
theorem nonexist_of_not_regular [Nonempty Ω] {A0 A1 : Matrix ι ι ℝ}
    (h : pencilPoly A0 A1 = 0) :
    ∃ w : ℕ → ι → Ω → ℝ, BoundedV w ∧ AdaptedV 𝔼 w ∧
      ∀ y, SolvesPencil 𝔼 A0 A1 w y → False := by
  obtain ⟨q, hq0, hq⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  set cK : ℕ → ι → ℝ := fun k i => (q i).coeff k with hcK
  -- the coefficient identities `q_{k+1} A₁ = q_k A₀`, `q_0 A₁ = 0`
  have hrow : ∀ j, ∑ i, (q i * Polynomial.X * C (A0 i j) - q i * C (A1 i j)) = 0 := by
    intro j
    have := congrFun hq j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.diagonal_mul, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hsucc : ∀ k, cK (k + 1) ᵥ* A1 = cK k ᵥ* A0 := by
    intro k
    funext j
    have := congrArg (fun p => p.coeff (k + 1)) (hrow j)
    simp only [Polynomial.finsetSum_coeff, coeff_sub, coeff_mul_C, coeff_mul_X,
      coeff_zero, Finset.sum_sub_distrib] at this
    simp only [Matrix.vecMul, dotProduct, hcK]
    linarith
  have hzero : cK 0 ᵥ* A1 = 0 := by
    funext j
    have := congrArg (fun p => p.coeff 0) (hrow j)
    simp only [Polynomial.finsetSum_coeff, coeff_sub, coeff_mul_C, coeff_mul_X_zero, zero_mul,
      zero_sub, coeff_zero, Finset.sum_neg_distrib, neg_eq_zero] at this
    simp only [Matrix.vecMul, dotProduct, hcK, Pi.zero_apply]
    exact this
  -- a bound on the degrees
  set K : ℕ := Finset.univ.sup (fun i => (q i).natDegree) with hK
  have hdeg : ∀ i, (q i).natDegree < K + 1 := fun i =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (q i).natDegree) (Finset.mem_univ i))
  have hcK0 : cK (K + 1) = 0 := by
    funext i
    exact coeff_eq_zero_of_natDegree_lt (hdeg i)
  -- a point `ρ ∈ [0, 1]` with `q(ρ) ≠ 0`
  obtain ⟨i0, hi0⟩ : ∃ i, q i ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hq0 (funext hne)
  obtain ⟨ρ, ⟨hρ0, hρ1⟩, hρ⟩ := (Set.Icc_infinite (zero_lt_one' ℝ)).exists_notMem_finset
    (q i0).roots.toFinset
  have hρq : (q i0).eval ρ ≠ 0 := by
    intro h0
    exact hρ (Multiset.mem_toFinset.mpr ((mem_roots hi0).mpr h0))
  set qρ : ι → ℝ := fun i => (q i).eval ρ with hqρ
  have hqρsum : ∀ i, qρ i = ∑ k ∈ Finset.range (K + 1), cK k i * ρ ^ k := fun i =>
    eval_eq_sum_range' (hdeg i) ρ
  refine ⟨fun t i _ => ρ ^ t * qρ i, ⟨∑ i, |qρ i|, fun t i _ => ?_⟩, fun t i => 𝔼.const t _, ?_⟩
  · rw [abs_mul, abs_pow, abs_of_nonneg hρ0]
    calc ρ ^ t * |qρ i| ≤ 1 * |qρ i| :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hρ0 hρ1) (abs_nonneg _)
      _ ≤ ∑ i, |qρ i| := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun i => |qρ i|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)
  · intro y hy
    obtain ⟨ω₀⟩ := ‹Nonempty Ω›
    set e : ℕ → ι → ℝ := fun s i => 𝔼.E 0 (y s i) ω₀ with he
    have hstep : ∀ s, A0 *ᵥ e (s + 1) = A1 *ᵥ e s + fun i => ρ ^ s * qρ i := by
      intro s
      funext i
      have h1 := congrArg (fun f => 𝔼.E 0 (f i) ω₀) (hy s)
      simp only [E_mv 𝔼, Pi.add_apply, map_add, 𝔼.const] at h1
      have h2 : (fun j => 𝔼.E 0 (𝔼.E s (y (s + 1) j))) = fun j => 𝔼.E 0 (y (s + 1) j) := by
        funext j; exact 𝔼.tower (Nat.zero_le s) _
      rw [h2] at h1
      rw [mv_apply, mv_apply] at h1
      simpa [he, Pi.add_apply] using h1
    -- telescoping
    set c : ℕ → ℝ := fun k => (cK k ᵥ* A1) ⬝ᵥ e k with hc
    have hinc : ∀ k, cK k ⬝ᵥ (fun i => ρ ^ k * qρ i) = c (k + 1) - c k := by
      intro k
      have e1 : (fun i => ρ ^ k * qρ i) = A0 *ᵥ e (k + 1) - A1 *ᵥ e k := by
        rw [hstep k]; abel
      rw [e1, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, hc]
      simp only
      rw [hsucc]
    have hsum : ∑ k ∈ Finset.range (K + 1), cK k ⬝ᵥ (fun i => ρ ^ k * qρ i) = 0 := by
      rw [Finset.sum_congr rfl fun k _ => hinc k, Finset.sum_range_sub, hc]
      simp only
      rw [hcK0, hzero, Matrix.zero_vecMul, zero_dotProduct, zero_dotProduct, sub_zero]
    have hpos : 0 < ∑ k ∈ Finset.range (K + 1), cK k ⬝ᵥ (fun i => ρ ^ k * qρ i) := by
      have e2 : ∑ k ∈ Finset.range (K + 1), cK k ⬝ᵥ (fun i => ρ ^ k * qρ i) =
          ∑ i, qρ i * qρ i := by
        simp only [dotProduct]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        calc ∑ k ∈ Finset.range (K + 1), cK k i * (ρ ^ k * qρ i) =
            (∑ k ∈ Finset.range (K + 1), cK k i * ρ ^ k) * qρ i := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun k _ => by ring
          _ = qρ i * qρ i := by rw [← hqρsum i]
      rw [e2]
      exact Finset.sum_pos' (fun i _ => mul_self_nonneg _)
        ⟨i0, Finset.mem_univ _, mul_self_pos.mpr hρq⟩
    linarith

/-! ### The Blanchard–Kahn theorem for arbitrary pencils -/

/-- Woodford (2003), App. C.1, p. 672, fn. 2 (genericity for pencils): no nonzero bounded
deterministic solution of `A₀ y_{t+1} = A₁ y_t` starts with `x_0 = 0`. -/
def GenericPencil (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : Prop :=
  ∀ v, PencilBounded A0 A1 v → (∀ j, v (Sum.inr j) = 0) → v = 0

/-- Woodford (2003), App. C.1, p. 670 (tool): a nonzero pencil polynomial has a point where
`det(cA₀ − A₁) ≠ 0`. -/
theorem exists_regular_point {A0 A1 : Matrix ι ι ℝ} (h : pencilPoly A0 A1 ≠ 0) :
    ∃ c : ℝ, IsUnit (c • A0 - A1).det := by
  by_contra hne
  push Not at hne
  apply h
  refine Polynomial.funext fun r => ?_
  rw [eval_pencilPoly, eval_zero]
  by_contra h0
  exact hne r (isUnit_iff_ne_zero.mpr h0)

/-- **The Blanchard–Kahn theorem for arbitrary pencils** (Woodford (2003), App. C.1, p. 670 and
fn. 1–2; Blanchard and Kahn (1980), King and Watson (1998), Klein (2000)): for any expectation
system on a nonempty state space, `A₀ E_t y_{t+1} = A₁ y_t + w_t` (with `A₀` possibly singular,
`x` predetermined) is determinate iff the pencil is regular (`det(λA₀ − A₁) ≢ 0`), no root of
`det(λA₀ − A₁)` lies on the unit circle, exactly `|X|` roots (with multiplicity) lie in the open
unit disc, and genericity holds for the bounded deterministic solutions. -/
theorem determinatePencil_iff_general [Nonempty Ω] (A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    DeterminatePencil 𝔼 A0 A1 ↔ pencilPoly A0 A1 ≠ 0 ∧
      (∀ μ ∈ ((pencilPoly A0 A1).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1) ∧
      Multiset.card (((pencilPoly A0 A1).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card X ∧ GenericPencil A0 A1 := by
  by_cases hreg : pencilPoly A0 A1 = 0
  · constructor
    · intro hd
      exfalso
      obtain ⟨w, hwb, hwa, hno⟩ := nonexist_of_not_regular 𝔼 hreg
      obtain ⟨y, hy, -⟩ := hd w hwb hwa 0
      exact hno y hy.1
    · rintro ⟨h, -⟩
      exact absurd hreg h
  · obtain ⟨c, hB⟩ := exists_regular_point hreg
    obtain ⟨m, P, Q, Ni, hFit⟩ := exists_fitting ((c • A0 - A1)⁻¹ * A0)
    have hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni := hFit
    have hgen : GenericX (ahat c P Q Ni) ↔ GenericPencil A0 A1 := by
      unfold GenericX GenericPencil
      exact forall_congr' fun v => by rw [mem_boundedOrbits_ahat hB hF]
    rw [determinatePencil_iff_ahat 𝔼 hB hF, determinate_iff_count, noUnit_ahat_iff hB hF,
      stableCount_ahat hB hF, hgen]
    simp only [hreg, ne_eq, not_false_eq_true, true_and]

/-- Woodford (2003), App. C.1, p. 670 (the infinite generalised eigenvalues are unstable): under
the conditions of `determinatePencil_iff_general`, the roots of `det(λA₀ − A₁)` outside the
closed unit disc together with the `n − deg det(λA₀ − A₁)` infinite generalised eigenvalues
number exactly `|Z|`, the non-predetermined variables. -/
theorem unstable_add_infinite {A0 A1 : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hreg : pencilPoly A0 A1 ≠ 0)
    (hnu : ∀ μ ∈ ((pencilPoly A0 A1).map Complex.ofRealHom).roots, ‖μ‖ ≠ 1)
    (hc : Multiset.card (((pencilPoly A0 A1).map Complex.ofRealHom).roots.filter
        (fun μ => ‖μ‖ < 1)) = Fintype.card X) :
    Multiset.card (((pencilPoly A0 A1).map Complex.ofRealHom).roots.filter (fun μ => 1 < ‖μ‖)) +
        (Fintype.card (Z ⊕ X) - (pencilPoly A0 A1).natDegree) = Fintype.card Z := by
  obtain ⟨c, hB⟩ := exists_regular_point hreg
  obtain ⟨m, P, Q, Ni, hFit⟩ := exists_fitting ((c • A0 - A1)⁻¹ * A0)
  have hF : Fitting ((c • A0 - A1)⁻¹ * A0) m P Q Ni := hFit
  obtain ⟨hp, hcp⟩ := poly_relations hB hF
  set p := pencilPoly A0 A1 with hpdef
  set rts := (p.map Complex.ofRealHom).roots with hrts
  have hcard : Multiset.card rts = p.natDegree := by
    rw [hrts, IsAlgClosed.card_roots_eq_natDegree, natDegree_map]
  have hdeg : p.natDegree ≤ Fintype.card (Z ⊕ X) := by
    have hκ : (c • A0 - A1).det * ((c • A0 - A1)⁻¹ * A0 * P + Q).det ≠ 0 :=
      mul_ne_zero hB.ne_zero (det_NPQ_ne_zero hF)
    have h1 : p.natDegree = (fpoly (ahat c P Q Ni) P Q).natDegree := by
      rw [hp, natDegree_C_mul hκ]
    have h2 : (fpoly (ahat c P Q Ni) P Q).natDegree ≤ (ahat c P Q Ni).charpoly.natDegree :=
      natDegree_le_of_dvd ⟨gpoly P Q, hcp⟩ (Matrix.charpoly_monic _).ne_zero
    rw [h1, ← Matrix.charpoly_natDegree_eq_dim (ahat c P Q Ni)]
    exact h2
  have hsplit : Multiset.card (rts.filter (fun μ => ‖μ‖ < 1)) +
      Multiset.card (rts.filter (fun μ => 1 < ‖μ‖)) = Multiset.card rts := by
    rw [← Multiset.card_add]
    congr 1
    conv_rhs => rw [← Multiset.filter_add_not (fun μ : ℂ => ‖μ‖ < 1) rts]
    congr 1
    refine Multiset.filter_congr fun μ hμ => ?_
    have := hnu μ hμ
    constructor
    · intro h1; exact not_lt.mpr h1.le
    · intro h1; exact lt_of_le_of_ne (not_lt.mp h1) (Ne.symm this)
  rw [Fintype.card_sum] at hdeg ⊢
  rw [hc, hcard] at hsplit
  omega

end Woodford.NeoWicksellianFramework.GeneralBKSingular
