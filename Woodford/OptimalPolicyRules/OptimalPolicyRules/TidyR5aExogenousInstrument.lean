/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralBKCopy
import OptimalPolicyRules.Prop84General
import OptimalPolicyRules.GeneralLinks

/-!
# Determinacy under an exogenous instrument (p. 546)

Woodford (2003), *Interest and Prices*, Chapter 8, §1.2, p. 546: when the instrument is a
specified function of the exogenous disturbances, the equilibrium conditions are (1.1) alone,
and "standard results then imply that the determinacy of equilibrium depends, in the generic
case, on the roots of the characteristic equation (1.15), `det[A − μÎ] = 0`: equilibrium is
(generically) determinate if the number of roots with `|μ| < 1` is exactly `n_Z`"; hence the
Sargent–Wallace property (more than `n_Z` such roots, p. 547) means indeterminacy.

## The Blanchard–Kahn theorem, both directions

`GeneralBKCopy.determinate_of` gives sufficiency. Here (`BK` namespace):

* `BK.orbit_equil`: a bounded deterministic orbit `Aᵗv` is an equilibrium with no forcing;
* `BK.not_determinate_of_not_generic`: if the genericity condition `GenericX` fails, uniqueness
  fails;
* `BK.mem_proj_of_equil`, `BK.not_determinate_of_finrank_lt`: an equilibrium with no forcing and a
  deterministic `x₀` has `E₀y₀` on a bounded orbit, so fewer bounded-orbit dimensions than
  predetermined variables means non-existence for some `x₀`;
* `BK.finrank_le_of_generic`; **`BK.determinate_iff`**: with no eigenvalue on the unit circle,
  determinacy holds **iff** exactly `|X|` eigenvalues lie inside the unit circle and `GenericX`
  holds; `BK.not_determinate_of_card_lt_stableCount`: more stable eigenvalues than predetermined
  variables means indeterminacy, with or without unit-circle eigenvalues.

## (1.1) with an exogenous instrument (`Ẽ` invertible)

* `exoA`: (1.1) as `E_t(z_{t+1}, Z_{t+1}) = A(z_t, Z_t) + w_t`,
  `A = [[Ẽ⁻¹A₂₂, Ẽ⁻¹A₂₁], [A₁₂, A₁₁]]`; `Exo.eigs_exoA`: its eigenvalues (with multiplicity) are the
  roots of (1.15); `Exo.stableCount_le_exoA`: the count of p. 547 (zero root counted `n − rank A`
  times) never exceeds the multiplicity count.
* `Exo.ExoSol`, `Exo.ExoDeterminate`: bounded solutions of (1.1) with a given bounded exogenous
  instrument path, and the Definition of p. 546 (a unique bounded solution from `t₀` on, for
  every bounded disturbance and instrument path and every bounded initial `Z_{t₀}`).
* **`Exo.exoDeterminate_iff`** (p. 546): if no root of (1.15) lies on the unit circle, the
  equilibrium is determinate **iff** exactly `n_Z` roots of (1.15) lie inside the unit circle
  and the genericity condition holds — the book's "generically".
* **`Exo.sargentWallace_not_exoDeterminate`** (pp. 546–547): under the Sargent–Wallace property no
  exogenous instrument rule gives a determinate equilibrium.
-/

namespace Woodford.OptimalPolicyRules.TidyR5aExogenousInstrument

open Matrix Polynomial

variable {Ω : Type*}

/-! ### The Blanchard–Kahn theorem: necessity -/

namespace BK

open BKInvariantSplit BKForward

variable {Z X : Type*} [Fintype Z] [Fintype X] [DecidableEq Z] [DecidableEq X]

/-- Woodford (2003), App. C.1, p. 670 (tool): a bounded deterministic orbit `y_t = Aᵗv` is a
bounded equilibrium of `E_ty_{t+1} = Ay_t` with `x₀ = v_x`. -/
theorem orbit_equil (𝔼 : ExpectationSystem Ω) {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    {v : Z ⊕ X → ℝ} (hv : v ∈ boundedOrbits A) :
    GeneralBKCopy.Equil 𝔼 A (fun _ _ _ => 0) (fun j _ => v (Sum.inr j))
      (fun t k _ => (A ^ t *ᵥ v) k) := by
  obtain ⟨C, hC⟩ := hv
  refine ⟨fun t i => ?_, fun t i => 𝔼.const t _, fun t j => 𝔼.const t _, fun j => by simp,
    ⟨C, fun t i _ => hC t i⟩⟩
  rw [𝔼.const]
  funext ω
  rw [Pi.add_apply, mv_apply, pow_succ', ← mulVec_mulVec, add_zero]

omit [DecidableEq Z] [DecidableEq X] in
/-- Woodford (2003), App. C.1, p. 670 (tool): the zero process is the equilibrium with no
forcing and `x₀ = 0`. -/
theorem zero_equil (𝔼 : ExpectationSystem Ω) (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) :
    GeneralBKCopy.Equil 𝔼 A (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) := by
  refine ⟨fun t i => ?_, fun t i => 𝔼.const t _, fun t j => 𝔼.const t _, fun j => rfl,
    ⟨0, fun _ _ _ => by simp⟩⟩
  rw [𝔼.const]
  funext ω
  rw [Pi.add_apply, mv_apply]
  simp [mulVec, dotProduct]

/-- **Woodford (2003), App. C.1, p. 672, fn 2: the genericity condition is necessary.** If a
nonzero bounded orbit starts with `x = 0`, the equilibrium with no forcing and `x₀ = 0` is not
unique (nonempty sample space). -/
theorem not_determinate_of_not_generic [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (h : ¬ GenericX A) : ¬ GeneralBKCopy.Determinate 𝔼 A := by
  intro hD
  simp only [GenericX, not_forall] at h
  obtain ⟨v, hv, hx, hne⟩ := h
  obtain ⟨y, -, huniq⟩ := hD (fun _ _ _ => 0) ⟨0, fun _ _ _ => by simp⟩
    (fun t i => 𝔼.const t 0) (fun _ _ => 0) (fun j => 𝔼.const 0 0) ⟨0, fun _ _ => by simp⟩
  have h1 := orbit_equil 𝔼 hv
  have hx0 : (fun j (_ : Ω) => v (Sum.inr j)) = fun _ _ => 0 := by
    funext j ω
    exact hx j
  rw [hx0] at h1
  have e0 := huniq _ (zero_equil 𝔼 A)
  have e1 := huniq _ h1
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  apply hne
  funext k
  have := congrFun (congrFun (congrFun (e1.trans e0.symm) 0) k) ω
  simpa using this

/-- Woodford (2003), App. C.1, p. 670: **an equilibrium with no forcing and a deterministic `x₀`
lies on a bounded orbit**: `m_t = E₀y_t` (at any outcome) satisfies `m_{t+1} = Am_t` by the law
of iterated expectations, is bounded, and starts at `y₀`, whose predetermined block is `x₀`. -/
theorem mem_proj_of_equil [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    {c : X → ℝ} {y : ℕ → Z ⊕ X → Ω → ℝ}
    (hy : GeneralBKCopy.Equil 𝔼 A (fun _ _ _ => 0) (fun j _ => c j) y) :
    ∃ v ∈ boundedOrbits A, ∀ j, v (Sum.inr j) = c j := by
  obtain ⟨ω0⟩ := ‹Nonempty Ω›
  obtain ⟨hS, ha, -, h0, ⟨M, hM⟩⟩ := hy
  set m : ℕ → Z ⊕ X → ℝ := fun t k => 𝔼.E 0 (y t k) ω0 with hm
  have hrec : ∀ t, m (t + 1) = A *ᵥ m t := by
    intro t
    funext i
    have e1 : 𝔼.E 0 (y (t + 1) i) = 𝔼.E 0 (𝔼.E t (y (t + 1) i)) :=
      (𝔼.tower (Nat.zero_le t) _).symm
    have e2 : mv A (y t) i + (fun _ _ _ => (0 : ℝ)) t i = ∑ j, A i j • y t j := by
      funext ω
      simp [mv, Finset.sum_apply]
    rw [hS t i, e2, map_sum] at e1
    simp only [hm]
    rw [e1, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
  have hb : ∀ t k, |m t k| ≤ M := fun t k => 𝔼.abs_E_le (fun ω => hM t k ω) 0 ω0
  refine ⟨m 0, mem_boundedOrbits_of_orbit hrec hb, fun j => ?_⟩
  simp only [hm]
  rw [ha 0 (Sum.inr j), h0 j]

/-- Woodford (2003), App. C.1, p. 672 (tool): the projection onto the predetermined block,
restricted to the bounded-orbit subspace. -/
noncomputable def projB (A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ) : boundedOrbits A →ₗ[ℝ] (X → ℝ) :=
  (projX (Z := Z) (X := X)).comp (boundedOrbits A).subtype

/-- **Woodford (2003), App. C.1, p. 670: the stable subspace must be large enough.** If the
bounded-orbit subspace has dimension below the number of predetermined variables, some
deterministic `x₀` admits no bounded equilibrium (nonempty sample space). -/
theorem not_determinate_of_finrank_lt [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (h : Module.finrank ℝ (boundedOrbits A) < Fintype.card X) :
    ¬ GeneralBKCopy.Determinate 𝔼 A := by
  intro hD
  have hr : Module.finrank ℝ (LinearMap.range (projB A)) < Module.finrank ℝ (X → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact (LinearMap.finrank_range_le _).trans_lt h
  have hne : LinearMap.range (projB A) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hr
    exact lt_irrefl _ hr
  obtain ⟨c, hc⟩ : ∃ c, c ∉ LinearMap.range (projB A) := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.mpr fun c _ => hcon c)
  obtain ⟨y, hy, -⟩ := hD (fun _ _ _ => 0) ⟨0, fun _ _ _ => by simp⟩
    (fun t i => 𝔼.const t 0) (fun j _ => c j) (fun j => 𝔼.const 0 (c j))
    ⟨∑ j, |c j|, fun j _ => Finset.single_le_sum (f := fun j => |c j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)⟩
  obtain ⟨v, hv, hvx⟩ := mem_proj_of_equil 𝔼 hy
  exact hc ⟨⟨v, hv⟩, funext fun j => hvx j⟩

/-- Woodford (2003), App. C.1, p. 672: under the genericity condition the bounded-orbit subspace
has dimension at most the number of predetermined variables (the projection onto `x` is
injective on it). -/
theorem finrank_le_of_generic {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (hg : GenericX A) :
    Module.finrank ℝ (boundedOrbits A) ≤ Fintype.card X := by
  have hinj : Function.Injective (projB A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (hg v v.2 fun j => congrFun hv j)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card] at this

/-- **Woodford (2003), App. C.1, p. 670 (Blanchard and Kahn 1980), both directions.** With no
eigenvalue on the unit circle and a nonempty sample space, `E_ty_{t+1} = Ay_t + w_t` is
determinate iff exactly `|X|` eigenvalues (with multiplicity) lie inside the unit circle and the
genericity condition holds. -/
theorem determinate_iff [Nonempty Ω] (𝔼 : ExpectationSystem Ω) {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ}
    (hnu : NoUnit A) :
    GeneralBKCopy.Determinate 𝔼 A ↔ stableCount A = Fintype.card X ∧ GenericX A := by
  rw [← finrank_eq_stableCount hnu]
  constructor
  · intro hD
    have hg : GenericX A := by
      by_contra h
      exact not_determinate_of_not_generic 𝔼 h hD
    refine ⟨le_antisymm (finrank_le_of_generic hg) ?_, hg⟩
    by_contra h
    exact not_determinate_of_finrank_lt 𝔼 (lt_of_not_ge h) hD
  · rintro ⟨hd, hg⟩
    exact GeneralBKCopy.determinate_of 𝔼 hnu hd hg

/-- **Woodford (2003), App. C.1, p. 670: more stable eigenvalues than predetermined variables
means indeterminacy** (no condition on unit-circle eigenvalues): the bounded-orbit subspace is
then too large for the genericity condition. -/
theorem not_determinate_of_card_lt_stableCount [Nonempty Ω] (𝔼 : ExpectationSystem Ω)
    {A : Matrix (Z ⊕ X) (Z ⊕ X) ℝ} (h : Fintype.card X < stableCount A) :
    ¬ GeneralBKCopy.Determinate 𝔼 A := by
  have hg : ¬ GenericX A := fun hg =>
    absurd ((stableCount_le_finrank A).trans (finrank_le_of_generic hg)) (not_le.mpr h)
  exact not_determinate_of_not_generic 𝔼 hg

end BK

/-! ### (1.1) with an exogenous instrument -/

namespace Exo

open GeneralSetup
open BKInvariantSplit (eigs stableCount NoUnit GenericX boundedOrbits)

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]
variable (S : LinearRESystem ιZ ιz)

/-- Woodford (2003), (1.1), p. 537, with `Ẽ` invertible, as a Blanchard–Kahn system in the state
`(z_t, Z_t)` (`z` non-predetermined, `Z` predetermined): `E_tz_{t+1} = Ẽ⁻¹(A₂₂z_t + A₂₁Z_t) + …`,
`Z_{t+1} = A₁₂z_t + A₁₁Z_t`. -/
noncomputable def exoA : Matrix (ιz ⊕ ιZ) (ιz ⊕ ιZ) ℝ :=
  fromBlocks (S.Et⁻¹ * S.A22) (S.Et⁻¹ * S.A21) S.A12 S.A11

/-- Woodford (2003), p. 537 (tool): `Î⁻¹ = diag(I, Ẽ⁻¹)` for invertible `Ẽ`. -/
theorem Ihat_inv (hE : IsUnit S.Et.det) : S.Ihat⁻¹ = fromBlocks 1 0 0 S.Et⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [LinearRESystem.Ihat, fromBlocks_multiply]
  simp [Matrix.nonsing_inv_mul _ hE, fromBlocks_one]

/-- Woodford (2003), (1.1) and (1.15): `exoA` is `Î⁻¹A` with the blocks reordered. -/
theorem exoA_reindex (hE : IsUnit S.Et.det) :
    exoA S = (S.Ihat⁻¹ * S.Ahat).reindex (Equiv.sumComm ιZ ιz) (Equiv.sumComm ιZ ιz) := by
  rw [Ihat_inv S hE, LinearRESystem.Ahat, fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [exoA]

/-- Woodford (2003), (1.15), p. 546: the characteristic polynomial of `Î⁻¹A` is a nonzero
multiple of `det[A − μÎ]`. -/
theorem charpoly_eq (hE : IsUnit S.Et.det) :
    ((S.Ihat⁻¹ * S.Ahat).map Complex.ofReal).charpoly =
      Polynomial.C (((S.Et.det : ℂ))⁻¹ * (-1) ^ Fintype.card (ιZ ⊕ ιz)) * S.pencilPoly := by
  have hI : IsUnit S.Ihat.det := by
    rw [LinearRESystem.Ihat, det_fromBlocks_zero₂₁, det_one, one_mul]
    exact hE
  have hdetI : (S.Ihat.map Complex.ofReal).det = (S.Et.det : ℂ) := by
    change (Complex.ofRealHom.mapMatrix S.Ihat).det = _
    rw [← RingHom.map_det, LinearRESystem.Ihat, det_fromBlocks_zero₂₁, det_one, one_mul]
    rfl
  have hEc : (S.Et.det : ℂ) ≠ 0 := by exact_mod_cast hE.ne_zero
  have hIM : S.Ihat.map Complex.ofReal * (S.Ihat⁻¹ * S.Ahat).map Complex.ofReal =
      S.Ahat.map Complex.ofReal := by
    change Complex.ofRealHom.mapMatrix S.Ihat * Complex.ofRealHom.mapMatrix (S.Ihat⁻¹ * S.Ahat) =
      Complex.ofRealHom.mapMatrix S.Ahat
    rw [← map_mul, ← Matrix.mul_assoc, mul_nonsing_inv _ hI, Matrix.one_mul]
  refine Polynomial.funext fun μ => ?_
  rw [eval_charpoly, eval_mul, eval_C, PencilSplit.pencilPoly_eval]
  have key : (S.Ihat.map Complex.ofReal).det *
      (Matrix.scalar (ιZ ⊕ ιz) μ - (S.Ihat⁻¹ * S.Ahat).map Complex.ofReal).det =
      (-1) ^ Fintype.card (ιZ ⊕ ιz) *
        (S.Ahat.map Complex.ofReal - μ • S.Ihat.map Complex.ofReal).det := by
    rw [← det_mul, Matrix.mul_sub, hIM, ← det_neg]
    congr 1
    have hs : S.Ihat.map Complex.ofReal * Matrix.scalar (ιZ ⊕ ιz) μ =
        μ • S.Ihat.map Complex.ofReal := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
    rw [hs]
    abel
  rw [hdetI] at key
  field_simp
  linear_combination key

/-- **Woodford (2003), (1.15), p. 546: the eigenvalues of the Blanchard–Kahn matrix of (1.1)
(with multiplicity) are the roots of `det[A − μÎ] = 0`**, for invertible `Ẽ`. -/
theorem eigs_exoA (hE : IsUnit S.Et.det) : eigs (exoA S) = S.pencilPoly.roots := by
  have hEc : (S.Et.det : ℂ) ≠ 0 := by exact_mod_cast hE.ne_zero
  have hc : ((S.Et.det : ℂ))⁻¹ * (-1) ^ Fintype.card (ιZ ⊕ ιz) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hEc) (pow_ne_zero _ (by norm_num))
  unfold eigs
  rw [exoA_reindex S hE]
  have e : ((S.Ihat⁻¹ * S.Ahat).reindex (Equiv.sumComm ιZ ιz) (Equiv.sumComm ιZ ιz)).map
      Complex.ofReal = ((S.Ihat⁻¹ * S.Ahat).map Complex.ofReal).reindex (Equiv.sumComm ιZ ιz)
        (Equiv.sumComm ιZ ιz) := rfl
  rw [e, charpoly_reindex, charpoly_eq S hE, roots_C_mul _ hc]

/-- Woodford (2003), (1.15), p. 546: the number of eigenvalues of `exoA` in the open unit disc is
the number of roots of (1.15) there, with multiplicity. -/
theorem stableCount_exoA (hE : IsUnit S.Et.det) :
    stableCount (exoA S) = Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1) := by
  unfold stableCount
  rw [eigs_exoA S hE]

/-- Woodford (2003), (1.15): no eigenvalue of `exoA` on the unit circle iff no root of (1.15)
on it. -/
theorem noUnit_exoA_iff (hE : IsUnit S.Et.det) :
    NoUnit (exoA S) ↔ ∀ μ ∈ S.pencilPoly.roots, ‖μ‖ ≠ 1 := by
  unfold NoUnit
  rw [eigs_exoA S hE]

/-- Woodford (2003), p. 547: the zero root of (1.15) has multiplicity at least `n − rank A` (the
kernel of `A` is an eigenspace of `Î⁻¹A` for `0`). -/
theorem card_sub_rank_le_count_zero (hE : IsUnit S.Et.det) :
    Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank ≤ S.pencilPoly.roots.count 0 := by
  have hI : IsUnit S.Ihat.det := by
    rw [LinearRESystem.Ihat, det_fromBlocks_zero₂₁, det_one, one_mul]
    exact hE
  set M := (S.Ihat⁻¹ * S.Ahat).map Complex.ofReal with hM
  have hEc : (S.Et.det : ℂ) ≠ 0 := by exact_mod_cast hE.ne_zero
  have hc : ((S.Et.det : ℂ))⁻¹ * (-1) ^ Fintype.card (ιZ ⊕ ιz) ≠ 0 :=
    mul_ne_zero (inv_ne_zero hEc) (pow_ne_zero _ (by norm_num))
  have hroots : M.charpoly.roots = S.pencilPoly.roots := by
    rw [hM, charpoly_eq S hE, roots_C_mul _ hc]
  rw [← hroots, count_roots]
  have hK : Module.finrank ℝ (LinearMap.ker S.Ahat.mulVecLin) =
      Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank := by
    have h1 := LinearMap.finrank_range_add_finrank_ker S.Ahat.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at h1
    have h2 : Module.finrank ℝ (LinearMap.range S.Ahat.mulVecLin) = S.Ahat.rank := rfl
    omega
  let K := LinearMap.ker S.Ahat.mulVecLin
  let b := Module.finBasis ℝ K
  let v : Fin (Module.finrank ℝ K) → ιZ ⊕ ιz → ℝ := fun i => (b i : ιZ ⊕ ιz → ℝ)
  have hv : LinearIndependent ℝ v :=
    b.linearIndependent.map' K.subtype (Submodule.ker_subtype K)
  have hvc : LinearIndependent ℂ (fun i => (algebraMap ℝ ℂ) ∘ v i) :=
    linearIndependent_algebraMap_comp_iff.mpr hv
  have hmem : ∀ i, (algebraMap ℝ ℂ) ∘ v i ∈ Module.End.eigenspace (toLin' M) 0 := by
    intro i
    rw [Module.End.mem_eigenspace_iff, zero_smul, toLin'_apply]
    have hker : S.Ahat *ᵥ v i = 0 := LinearMap.mem_ker.mp (b i).2
    have h0 : (S.Ihat⁻¹ * S.Ahat) *ᵥ v i = 0 := by rw [← mulVec_mulVec, hker, mulVec_zero]
    have e : (algebraMap ℝ ℂ ∘ v i) = fun j => (v i j : ℂ) := rfl
    rw [e, hM, PencilEigen.map_mulVec_ofReal, h0]
    funext j
    simp
  have hle := Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem))
  rw [finrank_span_eq_card hvc, Fintype.card_fin] at hle
  calc _ = Module.finrank ℝ K := hK.symm
    _ ≤ _ := hle
    _ ≤ _ := LinearMap.finrank_eigenspace_le _ _
    _ = _ := by rw [charpoly_toLin']

/-- Woodford (2003), p. 547: the count of roots inside the unit circle with the zero root counted
`n − rank A` times (`GeneralSetup.LinearRESystem.stableCount`) never exceeds the number of
eigenvalues of `exoA` inside the unit circle (with multiplicity). -/
theorem stableCount_le_exoA (hE : IsUnit S.Et.det) :
    S.stableCount 1 ≤ stableCount (exoA S) := by
  rw [stableCount_exoA S hE, LinearRESystem.stableCount]
  have hsplit := Multiset.filter_add_not (fun r : ℂ => r = 0)
    (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1)
  rw [← hsplit, Multiset.card_add, Multiset.filter_filter, Multiset.filter_filter]
  have h0 : Multiset.card (S.pencilPoly.roots.filter fun μ => μ = 0 ∧ ‖μ‖ < 1) =
      S.pencilPoly.roots.count 0 := by
    rw [Multiset.count_eq_card_filter_eq]
    congr 1
    refine Multiset.filter_congr fun r _ => ?_
    constructor
    · rintro ⟨rfl, -⟩
      rfl
    · rintro rfl
      exact ⟨rfl, by simp⟩
  have h1 : (S.pencilPoly.roots.filter fun μ => ¬ μ = 0 ∧ ‖μ‖ < 1) =
      S.pencilPoly.roots.filter fun μ => μ ≠ 0 ∧ ‖μ‖ < 1 := rfl
  rw [h0, h1]
  have := card_sub_rank_le_count_zero S hE
  omega

/-! ### Solutions of (1.1) with an exogenous instrument and the Blanchard–Kahn equilibria -/

/-- Woodford (2003), p. 546: a bounded adapted solution of (1.1) from `t₀` on with the instrument
set to the given exogenous path `i_t = ie_t` and `Z_{t₀} = Z₀`. -/
def ExoSol (𝔼 : ExpectationSystem Ω) (c : ℕ → Ω → ιz → ℝ) (ie : ℕ → Ω → ℝ) (t0 : ℕ)
    (Z0 : Ω → ιZ → ℝ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  S.Structural 𝔼 c t0 y ∧ (∀ ω, Zpart (y t0 ω) = Z0 ω) ∧
    (∀ t, t0 ≤ t → ∀ ω, ipart (y t ω) = ie t ω) ∧ BoundedV y ∧ AdaptedV 𝔼 y

/-- **Woodford (2003), Definition, p. 546, for an exogenous instrument**: for every bounded
adapted disturbance, every bounded adapted instrument path and every bounded `Z_{t₀}` known at
`t₀`, (1.1) has a bounded solution, unique from `t₀` on. -/
def ExoDeterminate (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (ie : ℕ → Ω → ℝ) (Z0 : Ω → ιZ → ℝ), BoundedV c → AdaptedV 𝔼 c →
    (∃ K, ∀ t ω, |ie t ω| ≤ K) → 𝔼.Adapted ie → KnownV 𝔼 t0 Z0 →
    (∃ K, ∀ ω j, |Z0 ω j| ≤ K) →
    ∃ y, ExoSol S 𝔼 c ie t0 Z0 y ∧ ∀ y', ExoSol S 𝔼 c ie t0 Z0 y' → ∀ t, t0 ≤ t → y' t = y t

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 538 (tool): the predetermined block of an assembled plan. -/
theorem Zpart_elim (f : ιZ → ℝ) (g : ιz → ℝ) (h : Unit → ℝ) :
    Zpart (Sum.elim (Sum.elim f g) h) = f := rfl

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 538 (tool): the forward-looking block of an assembled plan. -/
theorem zpart_elim (f : ιZ → ℝ) (g : ιz → ℝ) (h : Unit → ℝ) :
    zpart (Sum.elim (Sum.elim f g) h) = g := rfl

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 538 (tool): the instrument of an assembled plan. -/
theorem ipart_elim (f : ιZ → ℝ) (g : ιz → ℝ) (h : Unit → ℝ) :
    ipart (Sum.elim (Sum.elim f g) h) = h () := rfl

/-- Woodford (2003), App. C.1 (tool): the Blanchard–Kahn state `(z_{s+t₀}, Z_{s+t₀})` of a
plan. -/
def toBK (t0 : ℕ) (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℕ → ιz ⊕ ιZ → Ω → ℝ :=
  fun s k ω => Sum.elim (fun i => zpart (y (s + t0) ω) i) (fun j => Zpart (y (s + t0) ω) j) k

/-- Woodford (2003), (1.1) (tool): the forcing `(Ẽ⁻¹(B₂ie_t + c_t), 0)` of the Blanchard–Kahn
form. -/
noncomputable def wExo (c : ℕ → Ω → ιz → ℝ) (ie : ℕ → Ω → ℝ) (t0 : ℕ) :
    ℕ → ιz ⊕ ιZ → Ω → ℝ :=
  fun s k ω => Sum.elim (fun i => (S.Et⁻¹ *ᵥ (ie (s + t0) ω • S.B2 + c (s + t0) ω)) i)
    (fun _ => 0) k

/-- Woodford (2003), App. C.1 (tool): the plan of a Blanchard–Kahn path (dates from `t₀`; zero
before `t₀`), with the instrument `ie`. -/
def ofBK (t0 : ℕ) (Y : ℕ → ιz ⊕ ιZ → Ω → ℝ) (ie : ℕ → Ω → ℝ) :
    ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ :=
  fun t ω => if t0 ≤ t then Sum.elim (Sum.elim (fun j => Y (t - t0) (Sum.inr j) ω)
    (fun i => Y (t - t0) (Sum.inl i) ω)) (fun _ => ie t ω) else 0

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. C.1 (tool): the state of the plan of a path is the path. -/
theorem toBK_ofBK (t0 : ℕ) (Y : ℕ → ιz ⊕ ιZ → Ω → ℝ) (ie : ℕ → Ω → ℝ) :
    toBK t0 (ofBK t0 Y ie) = Y := by
  funext s k ω
  rcases k with i | j
  · simp [toBK, ofBK, zpart]
  · simp [toBK, ofBK, Zpart]

omit [DecidableEq ιZ] in
/-- Woodford (2003), App. C.1 (tool): a solution of (1.1) with the instrument `ie` is the plan of
its state from `t₀` on. -/
theorem ofBK_toBK {𝔼 : ExpectationSystem Ω} {c : ℕ → Ω → ιz → ℝ} {ie : ℕ → Ω → ℝ} {t0 : ℕ}
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : ExoSol S 𝔼 c ie t0 Z0 y)
    (t : ℕ) (ht : t0 ≤ t) : y t = ofBK t0 (toBK t0 y) ie t := by
  funext ω v
  have e : t - t0 + t0 = t := by omega
  rcases v with (j | i) | u
  · simp [ofBK, toBK, Zpart, ht, e]
  · simp [ofBK, toBK, zpart, ht, e]
  · simp only [ofBK, ht, ↓reduceIte, Sum.elim_inr]
    exact hy.2.2.1 t ht ω

variable {S}

omit [DecidableEq ιZ] in
/-- Woodford (2003), (1.1) (tool): `exoA` applied to a state, by blocks. -/
theorem exoA_mulVec (v : ιz ⊕ ιZ → ℝ) :
    exoA S *ᵥ v = Sum.elim
      (S.Et⁻¹ *ᵥ (S.A22 *ᵥ (fun i => v (Sum.inl i)) + S.A21 *ᵥ (fun j => v (Sum.inr j))))
      (S.A12 *ᵥ (fun i => v (Sum.inl i)) + S.A11 *ᵥ (fun j => v (Sum.inr j))) := by
  have hv : v = Sum.elim (fun i => v (Sum.inl i)) (fun j => v (Sum.inr j)) := by
    funext k
    rcases k with i | j <;> rfl
  conv_lhs => rw [hv]
  simp only [exoA, fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_add,
    mulVec_mulVec]

omit [DecidableEq ιZ] in
/-- **Woodford (2003), (1.1) and App. C.1: a solution of (1.1) with an exogenous instrument gives
a Blanchard–Kahn equilibrium** of `exoA` (dates from `t₀`, `Prop84General.shiftES`). -/
theorem exoSol_to_equil (hE : IsUnit S.Et.det) {𝔼 : ExpectationSystem Ω}
    {c : ℕ → Ω → ιz → ℝ} {ie : ℕ → Ω → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : ExoSol S 𝔼 c ie t0 Z0 y) :
    GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) (exoA S) (wExo S c ie t0)
      (fun j ω => Z0 ω j) (toBK t0 y) := by
  obtain ⟨hS, hZ0, hi, ⟨K, hK⟩, ha⟩ := hy
  -- the predetermined block at `t + 1` is known at `t`
  have hZk : ∀ t, t0 ≤ t → KnownV 𝔼 t (fun ω => Zpart (y (t + 1) ω)) := by
    intro t ht
    have e : (fun ω => Zpart (y (t + 1) ω)) =
        fun ω => S.A11 *ᵥ Zpart (y t ω) + S.A12 *ᵥ zpart (y t ω) :=
      funext fun ω => (hS t ht ω).1
    rw [e]
    have hZ : KnownV 𝔼 t (fun ω => Zpart (y t ω)) := fun j => ha t _
    have hz : KnownV 𝔼 t (fun ω => zpart (y t ω)) := fun i => ha t _
    exact PencilSplit.knownV_mulVec_add 𝔼 S.A11 hZ (PencilSplit.knownV_mulVec 𝔼 S.A12 hz)
  refine ⟨fun s k => ?_, fun s k => ?_, fun s j => ?_, fun j => ?_, ⟨K, fun s k ω => ?_⟩⟩
  · change 𝔼.E (s + t0) (toBK t0 y (s + 1) k) = _
    funext ω
    rw [Pi.add_apply, BKForward.mv_apply, exoA_mulVec]
    have est : s + 1 + t0 = s + t0 + 1 := by omega
    rcases k with i | j
    · obtain ⟨-, h2⟩ := hS (s + t0) (by omega) ω
      have hEV := congrArg (fun v => (S.Et⁻¹ *ᵥ v) i) h2
      simp only [mulVec_mulVec, Matrix.nonsing_inv_mul _ hE, one_mulVec] at hEV
      change 𝔼.E (s + t0) (fun ω' => zpart (y (s + 1 + t0) ω') i) ω = _
      rw [est]
      change EV 𝔼 (s + t0) (fun ω' => zpart (y (s + t0 + 1) ω')) ω i = _
      rw [hEV, hi (s + t0) (by omega) ω]
      simp only [toBK, wExo, Sum.elim_inl, Sum.elim_inr, mulVec_add, Pi.add_apply]
      ring
    · change 𝔼.E (s + t0) (fun ω' => Zpart (y (s + 1 + t0) ω') j) ω = _
      rw [est]
      have h1 : 𝔼.E (s + t0) (fun ω' => Zpart (y (s + t0 + 1) ω') j) ω =
          Zpart (y (s + t0 + 1) ω) j := congrFun (hZk (s + t0) (by omega) j) ω
      rw [h1, (hS (s + t0) (by omega) ω).1]
      simp only [toBK, wExo, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, add_zero]
      ring
  · change 𝔼.E (s + t0) (toBK t0 y s k) = toBK t0 y s k
    rcases k with i | j
    · exact ha (s + t0) (Sum.inl (Sum.inr i))
    · exact ha (s + t0) (Sum.inl (Sum.inl j))
  · change 𝔼.E (s + t0) (fun ω => Zpart (y (s + 1 + t0) ω) j) =
      fun ω => Zpart (y (s + 1 + t0) ω) j
    rw [show s + 1 + t0 = s + t0 + 1 by omega]
    exact hZk (s + t0) (by omega) j
  · funext ω
    simp only [toBK, zero_add, Sum.elim_inr]
    exact congrFun (hZ0 ω) j
  · rcases k with i | j
    · exact hK _ ω _
    · exact hK _ ω _

omit [DecidableEq ιZ] in
/-- **Woodford (2003), App. C.1 and (1.1): a Blanchard–Kahn equilibrium of `exoA` gives a
solution of (1.1) with the exogenous instrument** (the plan `ofBK`). -/
theorem equil_to_exoSol (hE : IsUnit S.Et.det) {𝔼 : ExpectationSystem Ω}
    {c : ℕ → Ω → ιz → ℝ} {ie : ℕ → Ω → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ}
    (hib : ∃ K, ∀ t ω, |ie t ω| ≤ K) (hia : 𝔼.Adapted ie) {Y : ℕ → ιz ⊕ ιZ → Ω → ℝ}
    (hY : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) (exoA S) (wExo S c ie t0)
      (fun j ω => Z0 ω j) Y) :
    ExoSol S 𝔼 c ie t0 Z0 (ofBK t0 Y ie) := by
  obtain ⟨hSol, ha, hpk, h0, ⟨K, hK⟩⟩ := hY
  obtain ⟨Ki, hKi⟩ := hib
  refine ⟨fun t ht ω => ⟨funext fun j => ?_, funext fun i => ?_⟩, fun ω => funext fun j => ?_,
    fun t ht ω => ?_, ⟨max (max K Ki) 0, fun t ω v => ?_⟩, fun t v => ?_⟩
  · -- `Z_{t+1} = A₁₁Z_t + A₁₂z_t`
    have e1 : t + 1 - t0 = t - t0 + 1 := by omega
    have hk := congrFun (hSol (t - t0) (Sum.inr j)) ω
    have hp := congrFun (hpk (t - t0) j) ω
    change 𝔼.E (t - t0 + t0) _ ω = _ at hk hp
    rw [hp, Pi.add_apply, BKForward.mv_apply, exoA_mulVec] at hk
    simp only [Sum.elim_inr, wExo, add_zero] at hk
    simp only [ofBK, show t0 ≤ t + 1 by omega, ht, ↓reduceIte, e1, Zpart_elim, zpart_elim,
      Pi.add_apply]
    rw [hk, Pi.add_apply]
    ring
  · -- `Ẽ E_tz_{t+1} = A₂₁Z_t + A₂₂z_t + B₂i_t + c_t`
    have e1 : t + 1 - t0 = t - t0 + 1 := by omega
    have e2 : t - t0 + t0 = t := by omega
    have hEV : EV 𝔼 t (fun ω' => zpart (ofBK t0 Y ie (t + 1) ω')) ω =
        S.Et⁻¹ *ᵥ (S.A22 *ᵥ (fun i => Y (t - t0) (Sum.inl i) ω) +
          S.A21 *ᵥ (fun j => Y (t - t0) (Sum.inr j) ω)) +
          S.Et⁻¹ *ᵥ (ie t ω • S.B2 + c t ω) := by
      funext i
      have hk := congrFun (hSol (t - t0) (Sum.inl i)) ω
      change 𝔼.E (t - t0 + t0) _ ω = _ at hk
      rw [Pi.add_apply, BKForward.mv_apply, exoA_mulVec, e2] at hk
      simp only [Sum.elim_inl, wExo, e2] at hk
      simp only [EV, zpart, ofBK, show t0 ≤ t + 1 by omega, ↓reduceIte, Sum.elim_inl,
        Sum.elim_inr, e1, Pi.add_apply]
      exact hk
    rw [hEV, ← mulVec_add, mulVec_mulVec, Matrix.mul_nonsing_inv _ hE, one_mulVec]
    simp only [ofBK, ht, ↓reduceIte, Zpart_elim, zpart_elim, ipart_elim, Pi.add_apply]
    ring
  · simp only [Zpart, ofBK, le_rfl, ↓reduceIte, Sum.elim_inl, Nat.sub_self]
    exact congrFun (h0 j) ω
  · simp [ipart, ofBK, ht]
  · simp only [ofBK]
    split_ifs
    · rcases v with (j | i) | u
      · exact (hK _ _ ω).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hK _ _ ω).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hKi t ω).trans ((le_max_right _ _).trans (le_max_left _ _))
    · simp only [Pi.zero_apply, abs_zero]
      exact le_max_right _ _
  · by_cases ht : t0 ≤ t
    · have e2 : t - t0 + t0 = t := by omega
      rcases v with (j | i) | u
      · have := ha (t - t0) (Sum.inr j)
        change 𝔼.E (t - t0 + t0) _ = _ at this
        rw [e2] at this
        simp only [ofBK, ht, ↓reduceIte, Sum.elim_inl]
        exact this
      · have := ha (t - t0) (Sum.inl i)
        change 𝔼.E (t - t0 + t0) _ = _ at this
        rw [e2] at this
        simp only [ofBK, ht, ↓reduceIte, Sum.elim_inl, Sum.elim_inr]
        exact this
      · simp only [ofBK, ht, ↓reduceIte, Sum.elim_inr]
        exact hia t
    · simp only [ofBK, ht, ↓reduceIte, Pi.zero_apply]
      exact 𝔼.const t 0


/-! ### Determinacy under an exogenous instrument -/

variable (S)

omit [Fintype ιZ] [DecidableEq ιZ] in
/-- Woodford (2003), (1.1) (tool): with no disturbance and a zero instrument path the forcing of
the Blanchard–Kahn form vanishes. -/
theorem wExo_zero (t0 : ℕ) :
    wExo S (fun _ _ _ => 0) (fun (_ : ℕ) (_ : Ω) => 0) t0 = fun _ _ _ => (0 : ℝ) := by
  funext s k ω
  rcases k with i | j <;> simp [wExo, mulVec, dotProduct]

/-- **Woodford (2003), p. 546: without the genericity condition an exogenous instrument rule is
indeterminate.** A nonzero bounded orbit of `exoA` with `Z = 0` gives a second bounded solution of
(1.1) (no disturbance, zero instrument, `Z_{t₀} = 0`) besides the zero solution. -/
theorem not_exoDeterminate_of_not_generic [Nonempty Ω] (hE : IsUnit S.Et.det)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (h : ¬ GenericX (exoA S)) :
    ¬ ExoDeterminate S 𝔼 t0 := by
  intro hD
  simp only [GenericX, not_forall] at h
  obtain ⟨v, hv, hx, hne⟩ := h
  have h1 : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) (exoA S)
      (wExo S (fun _ _ _ => 0) (fun _ _ => 0) t0) (fun j ω => (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) ω j)
      (fun t k _ => ((exoA S) ^ t *ᵥ v) k) := by
    rw [wExo_zero S t0]
    have hx0 : (fun j (ω : Ω) => (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) ω j) =
        fun j _ => v (Sum.inr j) := by
      funext j ω
      exact (hx j).symm
    rw [hx0]
    exact BK.orbit_equil _ hv
  have h0 : GeneralBKCopy.Equil (Prop84General.shiftES 𝔼 t0) (exoA S)
      (wExo S (fun _ _ _ => 0) (fun _ _ => 0) t0) (fun j ω => (fun (_ : Ω) (_ : ιZ) => (0 : ℝ)) ω j)
      (fun _ _ _ => 0) := by
    rw [wExo_zero S t0]
    exact BK.zero_equil _ _
  have hib : ∃ K, ∀ (t : ℕ) (ω : Ω), |(fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) t ω| ≤ K :=
    ⟨0, fun _ _ => by simp⟩
  have hia : 𝔼.Adapted (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) := fun t => 𝔼.const t 0
  obtain ⟨y, -, huniq⟩ := hD (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    ⟨0, fun _ _ _ => by simp⟩ (fun t i => 𝔼.const t 0) hib hia (fun j => 𝔼.const t0 0)
    ⟨0, fun _ _ => by simp⟩
  have e1 := huniq _ (equil_to_exoSol hE hib hia h1) t0 le_rfl
  have e0 := huniq _ (equil_to_exoSol hE hib hia h0) t0 le_rfl
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  apply hne
  funext k
  rcases k with i | j
  · have := congrFun (congrFun (e1.trans e0.symm) ω) (Sum.inl (Sum.inr i))
    simpa [ofBK] using this
  · exact hx j

/-- **Woodford (2003), p. 546: too few bounded directions means non-existence.** If the bounded-
orbit subspace of `exoA` has dimension below `n_Z`, some deterministic `Z_{t₀}` admits no bounded
solution of (1.1) with no disturbance and a zero instrument. -/
theorem not_exoDeterminate_of_finrank_lt [Nonempty Ω] (hE : IsUnit S.Et.det)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (h : Module.finrank ℝ (boundedOrbits (exoA S)) < Fintype.card ιZ) :
    ¬ ExoDeterminate S 𝔼 t0 := by
  intro hD
  have hr : Module.finrank ℝ (LinearMap.range (BK.projB (exoA S))) <
      Module.finrank ℝ (ιZ → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact (LinearMap.finrank_range_le _).trans_lt h
  have hne : LinearMap.range (BK.projB (exoA S)) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hr
    exact lt_irrefl _ hr
  obtain ⟨c, hc⟩ : ∃ c, c ∉ LinearMap.range (BK.projB (exoA S)) := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.mpr fun c _ => hcon c)
  obtain ⟨y, hy, -⟩ := hD (fun _ _ _ => 0) (fun _ _ => 0) (fun _ j => c j)
    ⟨0, fun _ _ _ => by simp⟩ (fun t i => 𝔼.const t 0) ⟨0, fun _ _ => by simp⟩
    (fun t => 𝔼.const t 0) (fun j => 𝔼.const t0 (c j))
    ⟨∑ j, |c j|, fun _ j => Finset.single_le_sum (f := fun j => |c j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)⟩
  have hY := exoSol_to_equil hE hy
  rw [wExo_zero S t0] at hY
  obtain ⟨v, hv, hvx⟩ := BK.mem_proj_of_equil _ hY
  exact hc ⟨⟨v, hv⟩, funext fun j => hvx j⟩

/-- **Woodford (2003), p. 546, with the Blanchard–Kahn matrix.** For invertible `Ẽ`, a nonempty
sample space and no eigenvalue of `exoA` on the unit circle, an exogenous instrument rule gives a
determinate equilibrium (Definition, p. 546) iff `exoA` has exactly `n_Z` eigenvalues in the open
unit disc and the genericity condition holds. -/
theorem exoDeterminate_iff_bk [Nonempty Ω] (hE : IsUnit S.Et.det) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (hnu : NoUnit (exoA S)) :
    ExoDeterminate S 𝔼 t0 ↔ stableCount (exoA S) = Fintype.card ιZ ∧ GenericX (exoA S) := by
  constructor
  · intro hD
    have hg : GenericX (exoA S) := by
      by_contra h
      exact not_exoDeterminate_of_not_generic S hE 𝔼 t0 h hD
    refine ⟨?_, hg⟩
    rw [← BKInvariantSplit.finrank_eq_stableCount hnu]
    refine le_antisymm (BK.finrank_le_of_generic hg) ?_
    by_contra h
    exact not_exoDeterminate_of_finrank_lt S hE 𝔼 t0 (lt_of_not_ge h) hD
  · rintro ⟨hd, hg⟩
    have hDet := (BK.determinate_iff (Prop84General.shiftES 𝔼 t0) hnu).mpr ⟨hd, hg⟩
    intro c ie Z0 hcb hca hib hia hZk hZb
    have hwb : BKForward.BoundedV (wExo S c ie t0) := by
      obtain ⟨Mc, hMc⟩ := hcb
      obtain ⟨Ki, hKi⟩ := hib
      obtain ⟨K, hK⟩ := GeneralFOC.exists_bound_mulVec S.Et⁻¹ (Ki * ∑ i, |S.B2 i| + Mc)
      refine ⟨max K 0, fun s k ω => ?_⟩
      rcases k with i | j
      · refine (hK _ (fun i' => ?_) i).trans (le_max_left _ _)
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have h1 : |S.B2 i'| ≤ ∑ i, |S.B2 i| :=
          Finset.single_le_sum (f := fun i => |S.B2 i|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ i')
        have h2 : |ie (s + t0) ω| * |S.B2 i'| ≤ Ki * ∑ i, |S.B2 i| :=
          mul_le_mul (hKi (s + t0) ω) h1 (abs_nonneg _) ((abs_nonneg _).trans (hKi (s + t0) ω))
        calc |ie (s + t0) ω * S.B2 i' + c (s + t0) ω i'|
            ≤ |ie (s + t0) ω * S.B2 i'| + |c (s + t0) ω i'| := abs_add_le _ _
          _ ≤ Ki * ∑ i, |S.B2 i| + Mc := by rw [abs_mul]; linarith [hMc (s + t0) ω i']
      · simp [wExo]
    have hwa : BKForward.AdaptedV (Prop84General.shiftES 𝔼 t0) (wExo S c ie t0) := by
      intro s k
      change 𝔼.E (s + t0) _ = _
      rcases k with i | j
      · have hk : KnownV 𝔼 (s + t0) (fun ω => ie (s + t0) ω • S.B2 + c (s + t0) ω) := by
          intro i'
          have e : (fun ω => (ie (s + t0) ω • S.B2 + c (s + t0) ω) i') =
              (S.B2 i') • ie (s + t0) + fun ω => c (s + t0) ω i' := by
            funext ω
            simp [mul_comm]
          change 𝔼.E (s + t0) (fun ω => (ie (s + t0) ω • S.B2 + c (s + t0) ω) i') =
            fun ω => (ie (s + t0) ω • S.B2 + c (s + t0) ω) i'
          rw [e, map_add, map_smul, hia (s + t0), hca (s + t0) i']
        exact PencilSplit.knownV_mulVec 𝔼 S.Et⁻¹ hk i
      · exact 𝔼.const _ 0
    obtain ⟨Y, hY, huniq⟩ := hDet _ hwb hwa (fun j ω => Z0 ω j)
      (fun j => by change 𝔼.E (0 + t0) _ = _; rw [zero_add]; exact hZk j)
      (by obtain ⟨K, hK⟩ := hZb; exact ⟨K, fun j ω => hK ω j⟩)
    refine ⟨ofBK t0 Y ie, equil_to_exoSol hE hib hia hY, fun y' hy' t ht => ?_⟩
    rw [ofBK_toBK S hy' t ht, huniq _ (exoSol_to_equil hE hy')]

/-- **Woodford (2003), p. 546: "rational-expectations equilibrium is (generically) determinate if
the number of roots `μᵢ` such that `|μᵢ| < 1` is exactly equal to `n_Z`".** For invertible `Ẽ`, a
nonempty sample space and no root of (1.15) on the unit circle, an exogenous instrument rule
gives a determinate equilibrium iff (1.15) has exactly `n_Z` roots (with multiplicity) in the open
unit disc and the genericity condition holds. -/
theorem exoDeterminate_iff [Nonempty Ω] (hE : IsUnit S.Et.det) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) (hcirc : ∀ μ ∈ S.pencilPoly.roots, ‖μ‖ ≠ 1) :
    ExoDeterminate S 𝔼 t0 ↔
      Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1) = Fintype.card ιZ ∧
        GenericX (exoA S) := by
  rw [exoDeterminate_iff_bk S hE 𝔼 t0 ((noUnit_exoA_iff S hE).mpr hcirc), stableCount_exoA S hE]

/-- **Woodford (2003), p. 546: more than `n_Z` roots of (1.15) inside the unit circle means an
exogenous instrument rule is indeterminate** (counting with multiplicity; no condition on the unit
circle). -/
theorem not_exoDeterminate_of_card_lt [Nonempty Ω] (hE : IsUnit S.Et.det)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (h : Fintype.card ιZ < Multiset.card (S.pencilPoly.roots.filter fun μ => ‖μ‖ < 1)) :
    ¬ ExoDeterminate S 𝔼 t0 := by
  rw [← stableCount_exoA S hE] at h
  have hg : ¬ GenericX (exoA S) := fun hg => absurd
    ((BKInvariantSplit.stableCount_le_finrank _).trans (BK.finrank_le_of_generic hg))
    (not_le.mpr h)
  exact not_exoDeterminate_of_not_generic S hE 𝔼 t0 hg

/-- **Woodford (2003), pp. 546–547: the Sargent–Wallace property rules out every exogenous
instrument rule** (for invertible `Ẽ`; the count of p. 547 is at most the multiplicity count,
`Exo.stableCount_le_exoA`). -/
theorem sargentWallace_not_exoDeterminate [Nonempty Ω] (hE : IsUnit S.Et.det)
    (𝔼 : ExpectationSystem Ω) (t0 : ℕ) (h : S.SargentWallace) : ¬ ExoDeterminate S 𝔼 t0 := by
  refine not_exoDeterminate_of_card_lt S hE 𝔼 t0 ?_
  rw [← stableCount_exoA S hE]
  exact lt_of_lt_of_le h (stableCount_le_exoA S hE)

end Exo

/-! ### The basic model (p. 546, fn 11) -/

open IRuleBasic (Calib) in
/-- **Woodford (2003), p. 546 and fn 11 (Proposition 4.1): in the basic neo-Wicksellian model an
exogenous interest-rate path gives an indeterminate equilibrium.** (1.15) has the root
`λ₁ ∈ (0, 1)` while `n_Z = 0`. -/
theorem nk_not_exoDeterminate [Nonempty Ω] (c : Calib) (hc : c.Adm) (𝔼 : ExpectationSystem Ω)
    (t0 : ℕ) : ¬ Exo.ExoDeterminate (GeneralLinks.nkSys c hc.2.2.1.ne') 𝔼 t0 := by
  have hβ := hc.1
  have hκσ : 0 < c.κ * c.σ := mul_pos hc.2.2.2.1 hc.2.2.1
  have hE : IsUnit (GeneralLinks.nkSys c hc.2.2.1.ne').Et.det := by
    rw [isUnit_iff_ne_zero]
    simp [GeneralLinks.nkSys, det_fin_two, hβ.ne']
  refine Exo.not_exoDeterminate_of_card_lt _ hE 𝔼 t0 ?_
  rw [GeneralLinks.nk_pencilPoly c hc, mul_assoc, roots_C_mul _ (by exact_mod_cast hβ.ne'),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
    roots_X_sub_C, Multiset.filter_add, Multiset.filter_singleton]
  have h1 : ‖((QuadraticRoots.lam1 c.β (c.κ * c.σ) : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (QuadraticRoots.lam1_pos hβ hκσ).le]
    exact QuadraticRoots.lam1_lt_one hβ hκσ
  simp only [h1, ↓reduceIte, Multiset.card_add, Multiset.card_singleton, Fintype.card_empty]
  omega

end Woodford.OptimalPolicyRules.TidyR5aExogenousInstrument
