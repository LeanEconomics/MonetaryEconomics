/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.PrestonLearning
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# When do Preston's forecast sums converge? The exact condition

Woodford (2003), *Interest and Prices*, Chapter 4, §2.3, pp. 273–274 ((2.29)–(2.30) with the
forecasts of the estimated model `(Φ̂, Ĉ)`, Preston (2005), App. 4). The module PrestonLearning
proves that the discounted forecast sums `∑ aᵏ Ê_t z_{t+k+1} = ∑ aᵏ (Φ̂₀ + Φ̂ₛ Ĉᵏ s_t)`
(`a = β` or `αβ`) and `∑ βᵏ Ê_t r̂ⁿ_{t+k} = ∑ βᵏ f_r′ Ĉᵏ s_t` converge when every eigenvalue
of `βĈ` lies inside the unit circle. That condition is **not necessary** for a given belief and
state, and it **is necessary** for convergence at every belief and every state. The exact
condition:

* `IsGenEig M ℓ v` (`(M − ℓI)ᵐ v = 0` for some `m`), `krylov M x` (the span of `Mʲ x`, the
  spectral components "excited" by `x`); `isGenEig_iff_mem` (Mathlib's
  `Module.End.maxGenEigenspace`).
* `summable_of_isGenEig_lt` (stable components decay: binomial expansion and
  `∑ C(k + j, j) ℓᵏ`), `dot_eq_zero_of_summable` (a convergent series `φ′ Mᵏ x` on an invariant
  subspace forces `φ′ v = 0` on every generalised eigenvector with `|ℓ| ≥ 1`, including
  `|ℓ| = 1`, no diagonalisability), **`summable_iff_of_invariant`** (both directions, through the
  decomposition into generalised eigenspaces, `Submodule.inf_iSup_genEigenspace`).
* For real data: **`summable_iff_krylov`**: `∑ₖ φ′ Mᵏ s` converges **iff** `φ` annihilates every
  generalised eigenvector of `M` with eigenvalue of modulus `≥ 1` lying in the Krylov space of
  `s`; **`summable_all_iff`**: it converges for every state `s` iff `φ` annihilates every such
  generalised eigenvector; **`summable_all_all_iff`**: it converges for every `φ` and every `s`
  iff every eigenvalue of `M` lies inside the unit circle; `hasSum_of_summable_all`: under the
  exact condition and `det(I − M) ≠ 0` the sum is still `φ′ (I − M)⁻¹ s`.
* The model: `summable_fcast_iff`, `fcast_summable_iff`, `rnfc_summable_iff` (each forecast sum,
  per belief and state, exact); `isTerm`, `asTerm` (the summands of (2.29), (2.30)),
  `summable_isTerm_iff`, `summable_asTerm_iff` (the literal series of (2.29)–(2.30) converge iff
  `χ′(βĈ)ᵏ s_t`, `χ′_AS (αβĈ)ᵏ s_t` do, with explicit rows `isRow`, `asRow`);
  **`forecast_sums_all_iff`**, **`IS229_sums_all_iff`**: the spectral-radius condition on `βĈ`
  is **necessary and sufficient** for the forecast sums (resp. the literal series in (2.29)) to
  converge at every belief and every state.
* `decisionRules_iff_of_hasSum`, **`decisionRules_iff_exact`**: the actual law of motion
  `z_t = tempSol(s_t)` (`PrestonLearning.decisionRules_iff`) holds under the exact condition
  (the rows of `Φ̂ₛ` and `f_r` annihilate the generalised eigenvectors of `βĈ` and `αβĈ` with
  eigenvalues of modulus `≥ 1`, and `I − βĈ`, `I − αβĈ` invertible).
* **`forecast_sums_converge_without_spectral`**, `decisionRules_without_spectral`: the
  counterexample. With `Ĉ = diag(1/2, 2)` and `1/2 < β < 1` (so `βĈ` has the eigenvalue
  `2β > 1`) and beliefs and `f_r` that put no weight on the second state, every forecast sum and
  both series (2.29)–(2.30) converge, and (for `2αβ ≠ 1`) the decision rules are
  `z_t = tempSol(s_t)`; `cexCh_pow_mulVec`, `cexCh_isEig`, `cexCh_hasSum`, `cexCh_summable`,
  `cexCh_vecMul`.
-/

namespace Woodford.NeoWicksellianFramework.TidyR5ForecastSums

open Matrix Filter Topology Determinacy2 PrestonLearning

variable {n : ℕ}

/-! ### Generalised eigenvectors and Krylov subspaces -/

/-- Woodford (2003), p. 274: `v` is a generalised eigenvector of `M` for `ℓ` (or zero):
`(M − ℓI)ᵐ v = 0` for some `m`. -/
def IsGenEig (M : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) (v : Fin n → ℂ) : Prop :=
  ∃ m : ℕ, (M - l • 1) ^ m *ᵥ v = 0

/-- Woodford (2003), p. 274: the Krylov space `span{Mʲ x : j ≥ 0}` — the smallest
`M`-invariant subspace containing `x`; its generalised eigenvectors are the spectral components
of `M` that the state `x` excites. -/
def krylov (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (Set.range fun j : ℕ => M ^ j *ᵥ x)

/-- Woodford (2003), p. 274: `M` commutes with `M − ℓI`. -/
theorem commute_sub_smul (M : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) : Commute M (M - l • 1) :=
  (Commute.refl M).sub_right ((Commute.one_right M).smul_right l)

/-- Woodford (2003), p. 274: `IsGenEig` is membership of Mathlib's maximal generalised
eigenspace. -/
theorem isGenEig_iff_mem (M : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) (v : Fin n → ℂ) :
    IsGenEig M l v ↔ v ∈ Module.End.maxGenEigenspace (Matrix.toLin' M) l := by
  rw [Module.End.mem_maxGenEigenspace]
  have h : Matrix.toLin' M - l • (1 : Module.End ℂ (Fin n → ℂ)) = Matrix.toLin' (M - l • 1) := by
    rw [map_sub, map_smul, Matrix.toLin'_one]
    rfl
  refine exists_congr fun m => ?_
  rw [h, ← Matrix.toLin'_pow, Matrix.toLin'_apply]

/-- Woodford (2003), p. 274: generalised eigenspaces are invariant under `M`. -/
theorem isGenEig_pow_mulVec {M : Matrix (Fin n) (Fin n) ℂ} {l : ℂ} {v : Fin n → ℂ}
    (hv : IsGenEig M l v) (k : ℕ) : IsGenEig M l (M ^ k *ᵥ v) := by
  obtain ⟨m, hm⟩ := hv
  refine ⟨m, ?_⟩
  rw [mulVec_mulVec, ← ((commute_sub_smul M l).pow_pow k m).eq, ← mulVec_mulVec, hm, mulVec_zero]

/-- Woodford (2003), p. 274: an `M`-invariant subspace is invariant under `Mᵏ`. -/
theorem pow_mulVec_mem {M : Matrix (Fin n) (Fin n) ℂ} {Z : Submodule ℂ (Fin n → ℂ)}
    (hZ : ∀ x ∈ Z, M *ᵥ x ∈ Z) (k : ℕ) {x : Fin n → ℂ} (hx : x ∈ Z) : M ^ k *ᵥ x ∈ Z := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec]
    exact hZ _ ih

/-- Woodford (2003), p. 274: the Krylov space of `x` is `M`-invariant. -/
theorem krylov_invariant (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    ∀ y ∈ krylov M x, M *ᵥ y ∈ krylov M x := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, rfl⟩ := hz
    exact Submodule.subset_span ⟨j + 1, by simp only; rw [mulVec_mulVec, pow_succ']⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [mulVec_add]
    exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [mulVec_smul]
    exact Submodule.smul_mem _ c ha

/-- Woodford (2003), p. 274: `x` lies in its own Krylov space. -/
theorem self_mem_krylov (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : x ∈ krylov M x :=
  Submodule.subset_span ⟨0, by simp⟩

/-! ### Stable components: convergence -/

/-- Woodford (2003), p. 274: **stable spectral components contribute convergent sums**: if
`(M − ℓI)ᵐ v = 0` and `|ℓ| < 1`, then `∑ₖ φ′ Mᵏ v` converges (`Mᵏ v = ∑_{j<m} C(k, j) ℓ^{k−j}
(M − ℓI)ʲ v` and `∑ₖ C(k, j) ℓ^{k−j}` converges). -/
theorem summable_of_isGenEig_lt (M : Matrix (Fin n) (Fin n) ℂ) {l : ℂ} (hl : ‖l‖ < 1)
    {v : Fin n → ℂ} (hv : IsGenEig M l v) (φ : Fin n → ℂ) :
    Summable (fun k => φ ⬝ᵥ (M ^ k *ᵥ v)) := by
  obtain ⟨m, hm⟩ := hv
  set N := M - l • 1 with hN
  have hNv : ∀ j, m ≤ j → N ^ j *ᵥ v = 0 := fun j hj => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [add_comm, pow_add, ← mulVec_mulVec, hm, mulVec_zero]
  have hM : M = N + l • 1 := by rw [hN, sub_add_cancel]
  have hexp : ∀ k, M ^ k *ᵥ v =
      ∑ j ∈ Finset.range m, ((k.choose j : ℂ) * l ^ (k - j)) • (N ^ j *ᵥ v) := by
    intro k
    have h1 : M ^ k *ᵥ v =
        ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℂ) * l ^ (k - j)) • (N ^ j *ᵥ v) := by
      rw [hM, ((Commute.one_right N).smul_right l).add_pow, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_pow, one_pow, Matrix.mul_smul, Matrix.mul_one, ← Nat.cast_comm, ← nsmul_eq_mul,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Matrix.smul_mulVec]
    rw [h1]
    have e1 : ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℂ) * l ^ (k - j)) • (N ^ j *ᵥ v) =
        ∑ j ∈ Finset.range (k + 1 + m), ((k.choose j : ℂ) * l ^ (k - j)) • (N ^ j *ᵥ v) :=
      Finset.sum_subset (Finset.range_mono (Nat.le_add_right _ _)) fun j _ hj' => by
        have : k < j := by simp at hj'; omega
        simp [Nat.choose_eq_zero_of_lt this]
    have e2 : ∑ j ∈ Finset.range m, ((k.choose j : ℂ) * l ^ (k - j)) • (N ^ j *ᵥ v) =
        ∑ j ∈ Finset.range (k + 1 + m), ((k.choose j : ℂ) * l ^ (k - j)) • (N ^ j *ᵥ v) :=
      Finset.sum_subset (Finset.range_mono (Nat.le_add_left _ _)) fun j _ hj' => by
        have : m ≤ j := by simp at hj'; omega
        simp [hNv j this]
    rw [e1, e2]
  have hsum : ∀ j, Summable (fun k : ℕ => (k.choose j : ℂ) * l ^ (k - j)) := by
    intro j
    rw [← summable_nat_add_iff j]
    refine (hasSum_choose_mul_geometric_of_norm_lt_one j hl).summable.congr fun k => ?_
    simp
  have he : (fun k => φ ⬝ᵥ (M ^ k *ᵥ v)) = fun k =>
      ∑ j ∈ Finset.range m, ((k.choose j : ℂ) * l ^ (k - j)) * (φ ⬝ᵥ (N ^ j *ᵥ v)) := by
    funext k
    rw [hexp, dotProduct_sum]
    simp [dotProduct_smul, smul_eq_mul]
  rw [he]
  exact summable_sum fun j _ => (hsum j).mul_right _

/-! ### Unstable components: necessity -/

/-- Woodford (2003), p. 274: **convergence forces the unstable components to be invisible**: on
an `M`-invariant subspace `Z` on which every series `∑ₖ φ′ Mᵏ x` converges, `φ′ v = 0` for every
`v ∈ Z` with `(M − ℓI)ᵐ v = 0`, `|ℓ| ≥ 1`. By induction on `m`: `φ′ Mᵏ v = ℓᵏ φ′ v` because
`Mᵏ v − ℓᵏ v ∈ Z ∩ ker (M − ℓI)ᵐ`, and the terms of a convergent series tend to `0` while
`|ℓᵏ| ≥ 1`. -/
theorem dot_eq_zero_of_summable {M : Matrix (Fin n) (Fin n) ℂ} {φ : Fin n → ℂ}
    {Z : Submodule ℂ (Fin n → ℂ)} (hZ : ∀ x ∈ Z, M *ᵥ x ∈ Z)
    (hs : ∀ x ∈ Z, Summable (fun k => φ ⬝ᵥ (M ^ k *ᵥ x))) {l : ℂ} (hl : 1 ≤ ‖l‖) :
    ∀ m : ℕ, ∀ v ∈ Z, (M - l • 1) ^ m *ᵥ v = 0 → φ ⬝ᵥ v = 0 := by
  intro m
  induction m with
  | zero =>
    intro v _ hv
    rw [pow_zero, one_mulVec] at hv
    rw [hv, dotProduct_zero]
  | succ m ih =>
    intro v hvZ hv
    set N := M - l • 1 with hN
    have hNv : N *ᵥ v ∈ Z := by
      rw [hN, sub_mulVec, smul_mulVec, one_mulVec]
      exact Z.sub_mem (hZ v hvZ) (Z.smul_mem l hvZ)
    have hMs : Commute M (l • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
      (Commute.one_right M).smul_right l
    have hNM : Commute N M := (commute_sub_smul M l).symm
    have hNs : Commute N (l • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
      (Commute.one_right N).smul_right l
    have hkey : ∀ k : ℕ, φ ⬝ᵥ (M ^ k *ᵥ v) = l ^ k * (φ ⬝ᵥ v) := by
      intro k
      set S := ∑ i ∈ Finset.range k, M ^ i * (l • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (k - 1 - i)
        with hS
      have hgeom : S * N = M ^ k - (l • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ k :=
        hMs.geom_sum₂_mul k
      have hSmem : S *ᵥ (N *ᵥ v) ∈ Z := by
        rw [hS, Matrix.sum_mulVec]
        refine Z.sum_mem fun i _ => ?_
        rw [smul_pow, one_pow, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mulVec]
        exact Z.smul_mem _ (pow_mulVec_mem hZ i hNv)
      have hc : Commute (N ^ m) S := by
        rw [hS]
        exact Commute.sum_right _ _ _ fun i _ =>
          ((hNM.pow_pow m i).mul_right (hNs.pow_pow m (k - 1 - i)))
      have hSker : N ^ m *ᵥ (S *ᵥ (N *ᵥ v)) = 0 := by
        rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, mulVec_mulVec v (N ^ m) N, ← pow_succ, hv,
          mulVec_zero]
      have h0 := ih _ hSmem hSker
      have hdec : M ^ k *ᵥ v = S *ᵥ (N *ᵥ v) + l ^ k • v := by
        rw [mulVec_mulVec, hgeom, sub_mulVec, smul_pow, one_pow, smul_mulVec, one_mulVec,
          sub_add_cancel]
      rw [hdec, dotProduct_add, h0, zero_add, dotProduct_smul, smul_eq_mul]
    have ht := (hs v hvZ).tendsto_atTop_zero
    simp only [hkey] at ht
    have hle : ∀ k : ℕ, ‖φ ⬝ᵥ v‖ ≤ ‖l ^ k * (φ ⬝ᵥ v)‖ := fun k => by
      rw [norm_mul, norm_pow]
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hl)
    have h0 : ‖φ ⬝ᵥ v‖ ≤ 0 := by
      have := ht.norm
      rw [norm_zero] at this
      exact ge_of_tendsto' this hle
    exact norm_le_zero_iff.mp h0

/-- Woodford (2003), p. 274: **the exact convergence condition on an invariant subspace**: for an
`M`-invariant `Z`, every series `∑ₖ φ′ Mᵏ x`, `x ∈ Z`, converges **iff** `φ′ v = 0` for every
generalised eigenvector `v ∈ Z` of `M` whose eigenvalue has modulus `≥ 1`. -/
theorem summable_iff_of_invariant (M : Matrix (Fin n) (Fin n) ℂ) (φ : Fin n → ℂ)
    (Z : Submodule ℂ (Fin n → ℂ)) (hZ : ∀ x ∈ Z, M *ᵥ x ∈ Z) :
    (∀ x ∈ Z, Summable (fun k => φ ⬝ᵥ (M ^ k *ᵥ x))) ↔
      ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v ∈ Z, IsGenEig M l v → φ ⬝ᵥ v = 0 := by
  constructor
  · rintro hs l hl v hvZ ⟨m, hm⟩
    exact dot_eq_zero_of_summable hZ hs hl m v hvZ hm
  · intro h y hy
    have hZ' : ∀ x ∈ Z, Matrix.toLin' M x ∈ Z := fun x hx => by
      rw [Matrix.toLin'_apply]
      exact hZ x hx
    have hy' : y ∈ ⨆ μ, Z ⊓ Module.End.genEigenspace (Matrix.toLin' M) μ ⊤ := by
      rw [← Submodule.inf_iSup_genEigenspace hZ']
      refine ⟨hy, ?_⟩
      have htop := Module.End.iSup_maxGenEigenspace_eq_top (Matrix.toLin' M)
      exact htop ▸ Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun y => Summable fun k => φ ⬝ᵥ (M ^ k *ᵥ y))
      hy' ?_ ?_ ?_
    · intro μ x hx
      obtain ⟨hxZ, hxg⟩ := Submodule.mem_inf.mp hx
      have hgen : IsGenEig M μ x := (isGenEig_iff_mem M μ x).mpr hxg
      by_cases hμ : ‖μ‖ < 1
      · exact summable_of_isGenEig_lt M hμ hgen φ
      · push Not at hμ
        have hz : (fun k => φ ⬝ᵥ (M ^ k *ᵥ x)) = 0 := funext fun k =>
          h μ hμ _ (pow_mulVec_mem hZ k hxZ) (isGenEig_pow_mulVec hgen k)
        rw [hz]
        exact summable_zero
    · simp only [mulVec_zero, dotProduct_zero]
      exact summable_zero
    · intro a b ha hb
      simp only [mulVec_add, dotProduct_add]
      exact ha.add hb

/-! ### Real data -/

/-- Woodford (2003), p. 274: complexification commutes with `φ′ Mᵏ x`. -/
theorem ofReal_dot_pow (M : Matrix (Fin n) (Fin n) ℝ) (φ x : Fin n → ℝ) (k : ℕ) :
    (fun i => (φ i : ℂ)) ⬝ᵥ ((M.map Complex.ofReal) ^ k *ᵥ fun i => (x i : ℂ)) =
      ((φ ⬝ᵥ (M ^ k *ᵥ x) : ℝ) : ℂ) := by
  have hp : (M.map Complex.ofReal) ^ k = (M ^ k).map Complex.ofReal :=
    (Complex.ofRealHom.mapMatrix.map_pow M k).symm
  rw [hp]
  simp [dotProduct, mulVec, Complex.ofReal_sum, Complex.ofReal_mul]

/-- Woodford (2003), p. 274: **the exact condition, state by state**: for real `M`, `φ`, `s`,
`∑ₖ φ′ Mᵏ s` converges **iff** `φ` annihilates every generalised eigenvector of `M` (complex)
with eigenvalue of modulus `≥ 1` that lies in the Krylov space of `s` (the spectral components
`s` excites). -/
theorem summable_iff_krylov (M : Matrix (Fin n) (Fin n) ℝ) (φ s : Fin n → ℝ) :
    Summable (fun k => φ ⬝ᵥ (M ^ k *ᵥ s)) ↔
      ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v ∈ krylov (M.map Complex.ofReal) (fun i => (s i : ℂ)),
        IsGenEig (M.map Complex.ofReal) l v → (fun i => (φ i : ℂ)) ⬝ᵥ v = 0 := by
  set Mc := M.map Complex.ofReal with hMc
  set sc : Fin n → ℂ := fun i => (s i : ℂ) with hsc
  set φc : Fin n → ℂ := fun i => (φ i : ℂ) with hφc
  have h1 : Summable (fun k => φ ⬝ᵥ (M ^ k *ᵥ s)) ↔
      Summable (fun k => φc ⬝ᵥ (Mc ^ k *ᵥ sc)) := by
    rw [← Complex.summable_ofReal]
    simp only [hφc, hMc, hsc, ofReal_dot_pow]
  rw [h1, ← summable_iff_of_invariant Mc φc _ (krylov_invariant Mc sc)]
  constructor
  · intro hs y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      refine ((summable_nat_add_iff j).mpr hs).congr fun k => ?_
      simp only
      rw [mulVec_mulVec, ← pow_add]
    | zero => simp
    | add a b _ _ ha hb => simpa [mulVec_add, dotProduct_add] using ha.add hb
    | smul c a _ ha => simpa [mulVec_smul, dotProduct_smul] using ha.mul_left c
  · intro h
    exact h sc (self_mem_krylov Mc sc)

/-- Woodford (2003), p. 274: **the exact condition for every state**: `∑ₖ φ′ Mᵏ s` converges for
every `s` iff `φ` annihilates every generalised eigenvector of `M` with eigenvalue of modulus
`≥ 1`. -/
theorem summable_all_iff (M : Matrix (Fin n) (Fin n) ℝ) (φ : Fin n → ℝ) :
    (∀ s, Summable (fun k => φ ⬝ᵥ (M ^ k *ᵥ s))) ↔
      ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v, IsGenEig (M.map Complex.ofReal) l v →
        (fun i => (φ i : ℂ)) ⬝ᵥ v = 0 := by
  constructor
  · intro h
    set Mc := M.map Complex.ofReal with hMc
    set φc : Fin n → ℂ := fun i => (φ i : ℂ) with hφc
    have hall : ∀ y ∈ (⊤ : Submodule ℂ (Fin n → ℂ)),
        Summable (fun k => φc ⬝ᵥ (Mc ^ k *ᵥ y)) := by
      intro y _
      have hy : y = (fun i => ((y i).re : ℂ)) + Complex.I • (fun i => ((y i).im : ℂ)) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [mul_comm]
        exact (Complex.re_add_im (y i)).symm
      have hr := Complex.summable_ofReal.mpr (h fun i => (y i).re)
      have hi := (Complex.summable_ofReal.mpr (h fun i => (y i).im)).mul_left Complex.I
      rw [hy]
      refine (hr.add hi).congr fun k => ?_
      simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul, hφc,
        hMc, ofReal_dot_pow]
    intro l hl v hv
    exact (summable_iff_of_invariant Mc φc ⊤ (fun _ _ => Submodule.mem_top)).mp hall l hl v
      Submodule.mem_top hv
  · intro h s
    exact (summable_iff_krylov M φ s).mpr fun l hl v _ hv => h l hl v hv

/-- Woodford (2003), p. 274: a nonzero generalised eigenvector for `ℓ` makes `ℓ` an
eigenvalue. -/
theorem isEig_of_isGenEig {M : Matrix (Fin n) (Fin n) ℂ} {l : ℂ} {v : Fin n → ℂ}
    (hv : IsGenEig M l v) (hv0 : v ≠ 0) : KroneckerSpectrum.IsEig M l := by
  obtain ⟨m, hm⟩ := hv
  induction m generalizing v with
  | zero => exact absurd (by simpa using hm) hv0
  | succ m ih =>
    by_cases hN : (M - l • 1) *ᵥ v = 0
    · refine ⟨v, hv0, ?_⟩
      rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hN
      exact hN
    · exact ih hN (by rw [mulVec_mulVec, ← pow_succ, hm])

/-- Woodford (2003), p. 274: **the spectral-radius condition is necessary and sufficient for
convergence at every row and every state**: `∑ₖ φ′ Mᵏ s` converges for all `φ, s` iff every
(complex) eigenvalue of `M` lies inside the unit circle. -/
theorem summable_all_all_iff (M : Matrix (Fin n) (Fin n) ℝ) :
    (∀ φ s : Fin n → ℝ, Summable (fun k => φ ⬝ᵥ (M ^ k *ᵥ s))) ↔
      ∀ w, KroneckerSpectrum.IsEig (M.map Complex.ofReal) w → ‖w‖ < 1 := by
  constructor
  · intro h w hw
    by_contra hge
    push Not at hge
    obtain ⟨v, hv0, hv⟩ := hw
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have := (summable_all_iff M (Pi.single i 1)).mp (h _) w hge v
      ⟨1, by rw [pow_one, sub_mulVec, hv, smul_mulVec, one_mulVec, sub_self]⟩
    apply hi
    have e : (fun j => (((Pi.single i 1 : Fin n → ℝ) j : ℝ) : ℂ)) = Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [e, single_one_dotProduct] at this
    simpa using this
  · intro h φ s
    have hS := hasSum_smul_pow M h (a := 1) (by norm_num)
    simp only [one_smul] at hS
    exact (hasSum_dotProduct_mulVec hS φ s).summable

/-- Woodford (2003), p. 274 (Preston (2005), App. 4, `∑ βᵏ Ĉᵏ = (I − βĈ)⁻¹`, sharpened): if the
series converges for every state (the exact condition `summable_all_iff`) and `I − M` is
invertible, its sum is `φ′ (I − M)⁻¹ s` — no spectral-radius condition. -/
theorem hasSum_of_summable_all {M : Matrix (Fin n) (Fin n) ℝ} {φ : Fin n → ℝ}
    (hdet : (1 - M).det ≠ 0) (h : ∀ s, Summable (fun k => φ ⬝ᵥ (M ^ k *ᵥ s)))
    (s : Fin n → ℝ) : HasSum (fun k => φ ⬝ᵥ (M ^ k *ᵥ s)) (φ ⬝ᵥ ((1 - M)⁻¹ *ᵥ s)) := by
  set u := (1 - M)⁻¹ *ᵥ s with hu
  have hsu : s = (1 - M) *ᵥ u := by
    rw [hu, mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  rw [(h s).hasSum_iff_tendsto_nat]
  have hpart : ∀ N : ℕ, ∑ k ∈ Finset.range N, φ ⬝ᵥ (M ^ k *ᵥ s) = φ ⬝ᵥ u - φ ⬝ᵥ (M ^ N *ᵥ u) := by
    intro N
    rw [← dotProduct_sum, ← Matrix.sum_mulVec, hsu, mulVec_mulVec, geom_sum_mul_neg, sub_mulVec,
      one_mulVec, dotProduct_sub]
  simp only [hpart]
  have ht := (h u).tendsto_atTop_zero
  simpa using (tendsto_const_nhds (x := φ ⬝ᵥ u)).sub ht

/-! ### Preston's forecast sums -/

variable {Ω : Type*}

/-- Woodford (2003), p. 274: `aᵏ Ê_t z_{t+k+1} = aᵏ Φ̂₀ + Φ̂ₛ (aĈ)ᵏ s_t` (component `j`). -/
theorem fcast_term (a : ℝ) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → Ω → ℝ) (t k : ℕ) (j : Fin 3) (ω : Ω) :
    a ^ k * fcast Φ Ch s t k j ω = a ^ k * Φ.1 j + Φ.2 j ⬝ᵥ ((a • Ch) ^ k *ᵥ sv s t ω) := by
  simp only [fcast, smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-- Woodford (2003), p. 274: for `|a| < 1` the forecast sum `∑ aᵏ Ê_t z_{t+k+1}` (component `j`)
converges iff `∑ Φ̂ₛⱼ′ (aĈ)ᵏ s_t` does (the intercepts give a geometric series). -/
theorem summable_fcast_iff {a : ℝ} (ha : |a| < 1) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → Ω → ℝ) (t : ℕ) (j : Fin 3) (ω : Ω) :
    Summable (fun k => a ^ k * fcast Φ Ch s t k j ω) ↔
      Summable (fun k => Φ.2 j ⬝ᵥ ((a • Ch) ^ k *ᵥ sv s t ω)) := by
  have hg : Summable (fun k : ℕ => a ^ k * Φ.1 j) :=
    (summable_geometric_of_abs_lt_one ha).mul_right _
  simp only [fcast_term]
  exact ⟨fun h => (h.sub hg).congr fun k => by ring, fun h => hg.add h⟩

/-- Woodford (2003), p. 274: **the exact condition for a forecast sum**: for `|a| < 1`,
`∑ aᵏ Ê_t z_{t+k+1}` (component `j`) converges iff the row `Φ̂ₛⱼ` annihilates every generalised
eigenvector of `aĈ` with eigenvalue of modulus `≥ 1` that the state `s_t` excites. -/
theorem fcast_summable_iff {a : ℝ} (ha : |a| < 1) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → Ω → ℝ) (t : ℕ) (j : Fin 3) (ω : Ω) :
    Summable (fun k => a ^ k * fcast Φ Ch s t k j ω) ↔
      ∀ l : ℂ, 1 ≤ ‖l‖ →
        ∀ v ∈ krylov ((a • Ch).map Complex.ofReal) (fun i => (sv s t ω i : ℂ)),
          IsGenEig ((a • Ch).map Complex.ofReal) l v → (fun i => (Φ.2 j i : ℂ)) ⬝ᵥ v = 0 :=
  (summable_fcast_iff ha Φ Ch s t j ω).trans (summable_iff_krylov _ _ _)

/-- Woodford (2003), p. 274: **the exact condition for the natural-rate forecast sum**:
`∑ aᵏ Ê_t r̂ⁿ_{t+k} = ∑ f_r′ (aĈ)ᵏ s_t` converges iff `f_r` annihilates every generalised
eigenvector of `aĈ` with eigenvalue of modulus `≥ 1` that `s_t` excites. -/
theorem rnfc_summable_iff (a : ℝ) (gr : Fin n → ℝ) (Ch : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ → Fin n → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Summable (fun k => a ^ k * rnfc gr Ch s t k ω) ↔
      ∀ l : ℂ, 1 ≤ ‖l‖ →
        ∀ v ∈ krylov ((a • Ch).map Complex.ofReal) (fun i => (sv s t ω i : ℂ)),
          IsGenEig ((a • Ch).map Complex.ofReal) l v → (fun i => (gr i : ℂ)) ⬝ᵥ v = 0 := by
  rw [← summable_iff_krylov]
  refine Eq.to_iff (congrArg Summable (funext fun k => ?_))
  simp only [rnfc, smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- Woodford (2003), p. 274: **the spectral-radius condition is necessary and sufficient for the
forecast sums to converge at every belief and every state**: for `|a| < 1` (`a = β` in (2.29)),
`∑ aᵏ Ê_t z_{t+k+1}` converges for every belief `Φ̂`, state history, date, component and
outcome iff every eigenvalue of `aĈ` lies inside the unit circle. -/
theorem forecast_sums_all_iff [Nonempty Ω] {a : ℝ} (ha : |a| < 1)
    (Ch : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (Φ : Learning.Regression.Belief (Fin 3) (Fin n)) (s : ℕ → Fin n → Ω → ℝ) (t : ℕ)
        (j : Fin 3) (ω : Ω), Summable (fun k => a ^ k * fcast Φ Ch s t k j ω)) ↔
      ∀ w, KroneckerSpectrum.IsEig ((a • Ch).map Complex.ofReal) w → ‖w‖ < 1 := by
  rw [← summable_all_all_iff]
  constructor
  · intro h φ v
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := (summable_fcast_iff ha (0, fun _ => φ) Ch (fun _ l _ => v l) 0 0 ω).mp
      (h _ _ 0 0 ω)
    exact this
  · intro h Φ s t j ω
    exact (summable_fcast_iff ha Φ Ch s t j ω).mpr (h _ _)

/-! ### The literal series of (2.29) and (2.30) -/

/-- Woodford (2003), (2.29) p. 273: the `k`-th summand of the right side of (2.29). -/
def isTerm (β σ : ℝ) (gr : Fin n → ℝ) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ)
    (t : ℕ) (ω : Ω) (k : ℕ) : ℝ :=
  β ^ k * ((1 - β) * subj z Φ Ch s t (k + 1) 1 ω -
    σ * (subj z Φ Ch s t k 2 ω - subj z Φ Ch s t (k + 1) 0 ω - rnfc gr Ch s t k ω))

/-- Woodford (2003), (2.30) p. 273: the `k`-th summand of the right side of (2.30). -/
def asTerm (α β κ : ℝ) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ)
    (t : ℕ) (ω : Ω) (k : ℕ) : ℝ :=
  (α * β) ^ k * (κ * subj z Φ Ch s t k 1 ω + (1 - α) * β * subj z Φ Ch s t (k + 1) 0 ω)

/-- Woodford (2003), (2.29): the row `χ = ((1 − β)Φ̂ₓ + σΦ̂_π + σ f_r)′(βĈ) − σβ Φ̂_î` through which
the series (2.29) loads on `(βĈ)ᵏ s_t`. -/
def isRow (β σ : ℝ) (gr : Fin n → ℝ) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  ((1 - β) • Φ.2 1 + σ • Φ.2 0 + σ • gr) ᵥ* (β • Ch) - (σ * β) • Φ.2 2

/-- Woodford (2003), (2.30): the row `χ = καβ Φ̂ₓ + (1 − α)β Φ̂_π′(αβĈ)` through which the
series (2.30) loads on `(αβĈ)ᵏ s_t`. -/
def asRow (α β κ : ℝ) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  (κ * (α * β)) • Φ.2 1 + ((1 - α) * β) • (Φ.2 0 ᵥ* ((α * β) • Ch))

/-- Woodford (2003), (2.29): from `k = 1` on, the summand of (2.29) is a geometric term plus
`χ′(βĈ)ᵏ s_t`. -/
theorem isTerm_succ (β σ : ℝ) (gr : Fin n → ℝ) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ)
    (t : ℕ) (ω : Ω) (k : ℕ) :
    isTerm β σ gr Φ Ch s z t ω (k + 1) =
      β ^ (k + 1) * ((1 - β) * Φ.1 1 - σ * (Φ.1 2 - Φ.1 0)) +
        isRow β σ gr Φ Ch ⬝ᵥ ((β • Ch) ^ k *ᵥ sv s t ω) := by
  simp only [isTerm, isRow, subj, fcast, rnfc, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel, sub_dotProduct, ← dotProduct_mulVec, smul_pow,
    Matrix.smul_mulVec, add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    mulVec_mulVec, Matrix.smul_mul, ← pow_succ']
  ring

/-- Woodford (2003), (2.30): from `k = 1` on, the summand of (2.30) is a geometric term plus
`χ′(αβĈ)ᵏ s_t`. -/
theorem asTerm_succ (α β κ : ℝ) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (Ch : Matrix (Fin n) (Fin n) ℝ) (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ)
    (t : ℕ) (ω : Ω) (k : ℕ) :
    asTerm α β κ Φ Ch s z t ω (k + 1) =
      (α * β) ^ (k + 1) * (κ * Φ.1 1 + (1 - α) * β * Φ.1 0) +
        asRow α β κ Φ Ch ⬝ᵥ (((α * β) • Ch) ^ k *ᵥ sv s t ω) := by
  simp only [asTerm, asRow, subj, fcast, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceIte, Nat.add_sub_cancel, ← dotProduct_mulVec, smul_pow, Matrix.smul_mulVec,
    add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul, mulVec_mulVec, ← pow_succ',
    Matrix.smul_mul]
  ring

/-- Woodford (2003), (2.29): for `|β| < 1` the series on the right of (2.29) converges iff
`∑ χ′(βĈ)ᵏ s_t` does. -/
theorem summable_isTerm_iff {β : ℝ} (hβ : |β| < 1) (σ : ℝ) (gr : Fin n → ℝ)
    (Φ : Learning.Regression.Belief (Fin 3) (Fin n)) (Ch : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Summable (isTerm β σ gr Φ Ch s z t ω) ↔
      Summable (fun k => isRow β σ gr Φ Ch ⬝ᵥ ((β • Ch) ^ k *ᵥ sv s t ω)) := by
  have hg : Summable (fun k : ℕ => β ^ (k + 1) * ((1 - β) * Φ.1 1 - σ * (Φ.1 2 - Φ.1 0))) :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one hβ)).mul_right _
  rw [← summable_nat_add_iff 1]
  simp only [isTerm_succ]
  exact ⟨fun h => (h.sub hg).congr fun k => by ring, fun h => hg.add h⟩

/-- Woodford (2003), (2.30): for `|αβ| < 1` the series on the right of (2.30) converges iff
`∑ χ′(αβĈ)ᵏ s_t` does. -/
theorem summable_asTerm_iff {α β : ℝ} (hab : |α * β| < 1) (κ : ℝ)
    (Φ : Learning.Regression.Belief (Fin 3) (Fin n)) (Ch : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Summable (asTerm α β κ Φ Ch s z t ω) ↔
      Summable (fun k => asRow α β κ Φ Ch ⬝ᵥ (((α * β) • Ch) ^ k *ᵥ sv s t ω)) := by
  have hg : Summable (fun k : ℕ => (α * β) ^ (k + 1) * (κ * Φ.1 1 + (1 - α) * β * Φ.1 0)) :=
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_abs_lt_one hab)).mul_right _
  rw [← summable_nat_add_iff 1]
  simp only [asTerm_succ]
  exact ⟨fun h => (h.sub hg).congr fun k => by ring, fun h => hg.add h⟩

/-- Woodford (2003), (2.29): **the exact convergence condition for the series in (2.29)**: it
converges iff the row `χ` (`isRow`) annihilates every generalised eigenvector of `βĈ` with
eigenvalue of modulus `≥ 1` that the state `s_t` excites. -/
theorem isTerm_summable_iff {β : ℝ} (hβ : |β| < 1) (σ : ℝ) (gr : Fin n → ℝ)
    (Φ : Learning.Regression.Belief (Fin 3) (Fin n)) (Ch : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Summable (isTerm β σ gr Φ Ch s z t ω) ↔
      ∀ l : ℂ, 1 ≤ ‖l‖ →
        ∀ v ∈ krylov ((β • Ch).map Complex.ofReal) (fun i => (sv s t ω i : ℂ)),
          IsGenEig ((β • Ch).map Complex.ofReal) l v →
            (fun i => (isRow β σ gr Φ Ch i : ℂ)) ⬝ᵥ v = 0 :=
  (summable_isTerm_iff hβ σ gr Φ Ch s z t ω).trans (summable_iff_krylov _ _ _)

/-- Woodford (2003), (2.30): **the exact convergence condition for the series in (2.30)**. -/
theorem asTerm_summable_iff {α β : ℝ} (hab : |α * β| < 1) (κ : ℝ)
    (Φ : Learning.Regression.Belief (Fin 3) (Fin n)) (Ch : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ) (ω : Ω) :
    Summable (asTerm α β κ Φ Ch s z t ω) ↔
      ∀ l : ℂ, 1 ≤ ‖l‖ →
        ∀ v ∈ krylov (((α * β) • Ch).map Complex.ofReal) (fun i => (sv s t ω i : ℂ)),
          IsGenEig (((α * β) • Ch).map Complex.ofReal) l v →
            (fun i => (asRow α β κ Φ Ch i : ℂ)) ⬝ᵥ v = 0 :=
  (summable_asTerm_iff hab κ Φ Ch s z t ω).trans (summable_iff_krylov _ _ _)

/-- Woodford (2003), (2.29): **the spectral-radius condition on `βĈ` is necessary and sufficient
for the series in (2.29) to converge at every belief and every state** (`0 < β < 1`, `σ ≠ 0`,
any `f_r`). Necessity: the belief `Φ̂ₓ = Φ̂_π = 0`, `Φ̂_î = f_r′Ĉ − φ/(σβ)` makes the row `χ`
equal to an arbitrary `φ`. -/
theorem IS229_sums_all_iff [Nonempty Ω] {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hσ : σ ≠ 0)
    (gr : Fin n → ℝ) (Ch : Matrix (Fin n) (Fin n) ℝ) :
    (∀ (Φ : Learning.Regression.Belief (Fin 3) (Fin n)) (s : ℕ → Fin n → Ω → ℝ)
        (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ) (ω : Ω), Summable (isTerm β σ gr Φ Ch s z t ω)) ↔
      ∀ w, KroneckerSpectrum.IsEig ((β • Ch).map Complex.ofReal) w → ‖w‖ < 1 := by
  have hβ : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [← summable_all_all_iff]
  constructor
  · intro h φ v
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    set Φ : Learning.Regression.Belief (Fin 3) (Fin n) :=
      (0, Matrix.of ![0, 0, gr ᵥ* Ch - (σ * β)⁻¹ • φ]) with hΦ
    have hrow : isRow β σ gr Φ Ch = φ := by
      have hσβ : σ * β ≠ 0 := mul_ne_zero hσ hβ0.ne'
      have e0 : Φ.2 0 = 0 := rfl
      have e1 : Φ.2 1 = 0 := rfl
      have e2 : Φ.2 2 = gr ᵥ* Ch - (σ * β)⁻¹ • φ := rfl
      simp only [isRow, e0, e1, e2, smul_zero, zero_add, Matrix.vecMul_smul, Matrix.smul_vecMul,
        smul_smul, smul_sub, mul_inv_cancel₀ hσβ, one_smul]
      rw [mul_comm β σ]
      abel
    have := (summable_isTerm_iff hβ σ gr Φ Ch (fun _ l _ => v l) (fun _ _ _ => 0) 0 ω).mp
      (h _ _ _ 0 ω)
    rw [hrow] at this
    exact this
  · intro h Φ s z t ω
    exact (summable_isTerm_iff hβ σ gr Φ Ch s z t ω).mpr (h _ _)

/-! ### The decision rules under the exact condition -/

/-- Woodford (2003), p. 274: the forecast sum with a per-state hypothesis: if
`∑ Φ̂ₛⱼ′(aĈ)ᵏ v = Φ̂ₛⱼ′ S v`, then `∑ aᵏ Ê_t z_{t+k+1} = Φ̂₀ⱼ/(1 − a) + Φ̂ₛⱼ′ S s_t`. -/
theorem hasSum_fcast_vec {a : ℝ} (ha : |a| < 1) {Ch S : Matrix (Fin n) (Fin n) ℝ}
    (Φ : Learning.Regression.Belief (Fin 3) (Fin n)) (s : ℕ → Fin n → Ω → ℝ) (t : ℕ)
    (j : Fin 3) (ω : Ω)
    (hS : HasSum (fun k => Φ.2 j ⬝ᵥ ((a • Ch) ^ k *ᵥ sv s t ω)) (Φ.2 j ⬝ᵥ (S *ᵥ sv s t ω))) :
    HasSum (fun k => a ^ k * fcast Φ Ch s t k j ω)
      (Φ.1 j / (1 - a) + Φ.2 j ⬝ᵥ (S *ᵥ sv s t ω)) := by
  have h1 : HasSum (fun k => a ^ k * Φ.1 j) (Φ.1 j / (1 - a)) := by
    rw [div_eq_inv_mul]
    exact (hasSum_geometric_of_abs_lt_one ha).mul_right (Φ.1 j)
  convert h1.add hS using 1
  funext k
  exact fcast_term a Φ Ch s t k j ω

/-- Woodford (2003), p. 273: `∑ aᵐ Ê_t z_{t+m} = z_t + a ∑ aᵏ Ê_t z_{t+k+1}` under the per-state
hypothesis. -/
theorem hasSum_subj_vec {a : ℝ} (ha : |a| < 1) {Ch S : Matrix (Fin n) (Fin n) ℝ}
    (z : ℕ → Fin 3 → Ω → ℝ) (Φ : Learning.Regression.Belief (Fin 3) (Fin n))
    (s : ℕ → Fin n → Ω → ℝ) (t : ℕ) (j : Fin 3) (ω : Ω)
    (hS : HasSum (fun k => Φ.2 j ⬝ᵥ ((a • Ch) ^ k *ᵥ sv s t ω)) (Φ.2 j ⬝ᵥ (S *ᵥ sv s t ω))) :
    HasSum (fun m => a ^ m * subj z Φ Ch s t m j ω)
      (z t j ω + a * (Φ.1 j / (1 - a) + Φ.2 j ⬝ᵥ (S *ᵥ sv s t ω))) := by
  refine (hasSum_nat_add_iff' 1).mp ?_
  convert (hasSum_fcast_vec ha Φ s t j ω hS).mul_left a using 1
  · funext k
    simp only [subj, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, pow_succ]
    ring
  · simp [subj]

/-- Woodford (2003), pp. 273–274: **the actual law of motion under per-state convergence**:
`PrestonLearning.decisionRules_iff` with the spectral-radius hypothesis replaced by the
convergence of the forecast sums at the states that occur, to the closed forms with
`(I − βĈ)⁻¹`, `(I − αβĈ)⁻¹`. -/
theorem decisionRules_iff_of_hasSum {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin n → ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {Φ : Learning.Regression.Belief (Fin 3) (Fin n)}
    {Ch : Matrix (Fin n) (Fin n) ℝ} (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ)
    (hD : ∀ ω j, HasSum (fun k => Φ.2 j ⬝ᵥ ((β • Ch) ^ k *ᵥ sv s t ω))
      (Φ.2 j ⬝ᵥ ((1 - β • Ch)⁻¹ *ᵥ sv s t ω)))
    (hSu : ∀ ω j, HasSum (fun k => Φ.2 j ⬝ᵥ (((α * β) • Ch) ^ k *ᵥ sv s t ω))
      (Φ.2 j ⬝ᵥ ((1 - (α * β) • Ch)⁻¹ *ᵥ sv s t ω)))
    (hR : ∀ ω, HasSum (fun k => gr ⬝ᵥ ((β • Ch) ^ k *ᵥ sv s t ω))
      (gr ⬝ᵥ ((1 - β • Ch)⁻¹ *ᵥ sv s t ω))) :
    (IS229 β σ gr Φ Ch s z t ∧ AS230 α β κ Φ Ch s z t ∧
        TaylorRule φπ φx πbar xbar ci gi s z t) ↔
      ∀ ω, (fun j => z t j ω) =
        tempSol α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi Φ Ch (sv s t ω) := by
  have hβa : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hαβa : |α * β| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have hIS : ∀ ω, HasSum (fun k => β ^ k * ((1 - β) * subj z Φ Ch s t (k + 1) 1 ω -
      σ * (subj z Φ Ch s t k 2 ω - subj z Φ Ch s t (k + 1) 0 ω - rnfc gr Ch s t k ω)))
      (-(σ * z t 2 ω) + (demandW β σ ⬝ᵥ sumD β Φ Ch (sv s t ω) +
        σ * sumR β gr Ch (sv s t ω))) := by
    intro ω
    have h1 := hasSum_fcast_vec hβa Φ s t 1 ω (hD ω 1)
    have h0 := hasSum_fcast_vec hβa Φ s t 0 ω (hD ω 0)
    have hr : HasSum (fun k => β ^ k * rnfc gr Ch s t k ω)
        (gr ⬝ᵥ ((1 - β • Ch)⁻¹ *ᵥ sv s t ω)) := by
      convert hR ω using 1
      funext k
      simp only [rnfc, smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hi := hasSum_subj_vec hβa z Φ s t 2 ω (hD ω 2)
    convert (((h1.mul_left (1 - β)).add (h0.mul_left σ)).add (hr.mul_left σ)).sub
      (hi.mul_left σ) using 1
    · funext k
      simp only [subj, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      ring
    · simp only [demandW, sumD, sumR, dotProduct, Fin.sum_univ_three, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Nat.succ_eq_add_one,
        Nat.reduceAdd, Matrix.tail_cons, Matrix.head_cons]
      have : (1 - β) ≠ 0 := by linarith
      field_simp
      ring
  have hAS : ∀ ω, HasSum (fun k => (α * β) ^ k *
      (κ * subj z Φ Ch s t k 1 ω + (1 - α) * β * subj z Φ Ch s t (k + 1) 0 ω))
      (κ * z t 1 ω + supplyW α β κ ⬝ᵥ sumS α β Φ Ch (sv s t ω)) := by
    intro ω
    have hx := hasSum_subj_vec hαβa z Φ s t 1 ω (hSu ω 1)
    have hp := hasSum_fcast_vec hαβa Φ s t 0 ω (hSu ω 0)
    convert (hx.mul_left κ).add (hp.mul_left ((1 - α) * β)) using 1
    · funext k
      simp only [subj, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      ring
    · simp only [supplyW, sumS, dotProduct, Fin.sum_univ_three, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Nat.succ_eq_add_one,
        Nat.reduceAdd, Matrix.tail_cons, Matrix.head_cons]
      ring
  have hIS' : IS229 β σ gr Φ Ch s z t ↔ ∀ ω, z t 1 ω = -(σ * z t 2 ω) +
      (demandW β σ ⬝ᵥ sumD β Φ Ch (sv s t ω) + σ * sumR β gr Ch (sv s t ω)) :=
    forall_congr' fun ω => by rw [(hIS ω).tsum_eq]
  have hAS' : AS230 α β κ Φ Ch s z t ↔ ∀ ω, z t 0 ω = κ * z t 1 ω +
      supplyW α β κ ⬝ᵥ sumS α β Φ Ch (sv s t ω) :=
    forall_congr' fun ω => by rw [(hAS ω).tsum_eq]
  have hTR : TaylorRule φπ φx πbar xbar ci gi s z t ↔ ∀ ω, z t 2 ω =
      (taylorConst φπ φx πbar xbar ci + gi ⬝ᵥ sv s t ω) + φπ * z t 0 ω + φx / 4 * z t 1 ω :=
    forall_congr' fun ω => by
      unfold taylorConst
      constructor <;> intro h <;> linarith
  rw [hIS', hAS', hTR, ← forall_and, ← forall_and]
  exact forall_congr' fun ω => tempEqm_iff hΔ (fun j => z t j ω) _ _ _ _

/-- Woodford (2003), pp. 273–274: **the actual law of motion under the exact condition**: if the
rows of `Φ̂ₛ` and `f_r` annihilate every generalised eigenvector of `βĈ` with eigenvalue of
modulus `≥ 1`, the rows of `Φ̂ₛ` annihilate those of `αβĈ`, and `I − βĈ`, `I − αβĈ` are
invertible, then (2.29), (2.30) and (1.14) hold at `t` iff `z_t = tempSol(s_t)` — whatever the
spectral radius of `βĈ`. -/
theorem decisionRules_iff_exact {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin n → ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) {Φ : Learning.Regression.Belief (Fin 3) (Fin n)}
    {Ch : Matrix (Fin n) (Fin n) ℝ} (hd1 : (1 - β • Ch).det ≠ 0)
    (hd2 : (1 - (α * β) • Ch).det ≠ 0)
    (hΦ1 : ∀ j, ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v, IsGenEig ((β • Ch).map Complex.ofReal) l v →
      (fun i => (Φ.2 j i : ℂ)) ⬝ᵥ v = 0)
    (hΦ2 : ∀ j, ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v, IsGenEig (((α * β) • Ch).map Complex.ofReal) l v →
      (fun i => (Φ.2 j i : ℂ)) ⬝ᵥ v = 0)
    (hgr : ∀ l : ℂ, 1 ≤ ‖l‖ → ∀ v, IsGenEig ((β • Ch).map Complex.ofReal) l v →
      (fun i => (gr i : ℂ)) ⬝ᵥ v = 0)
    (s : ℕ → Fin n → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ) :
    (IS229 β σ gr Φ Ch s z t ∧ AS230 α β κ Φ Ch s z t ∧
        TaylorRule φπ φx πbar xbar ci gi s z t) ↔
      ∀ ω, (fun j => z t j ω) =
        tempSol α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi Φ Ch (sv s t ω) := by
  refine decisionRules_iff_of_hasSum hβ0 hβ1 hα0 hα1 hΔ s z t (fun ω j => ?_) (fun ω j => ?_)
    (fun ω => ?_)
  · have hd : (1 - β • Ch).det ≠ 0 := hd1
    exact hasSum_of_summable_all hd ((summable_all_iff _ _).mpr (hΦ1 j)) _
  · exact hasSum_of_summable_all hd2 ((summable_all_iff _ _).mpr (hΦ2 j)) _
  · exact hasSum_of_summable_all hd1 ((summable_all_iff _ _).mpr hgr) _

/-! ### The counterexample -/

/-- Woodford (2003), (2.24): an estimated state matrix `Ĉ = diag(1/2, 2)`, with an explosive
second state. -/
noncomputable def cexCh : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1 / 2, 2]

/-- Woodford (2003), (2.24): `(aĈ)ᵏ s` for `Ĉ = diag(1/2, 2)`: componentwise
`((a/2)ᵏ s₀, (2a)ᵏ s₁)`. -/
theorem cexCh_pow_mulVec (a : ℝ) (k : ℕ) (v : Fin 2 → ℝ) :
    (a • cexCh) ^ k *ᵥ v = ![(a / 2) ^ k * v 0, (2 * a) ^ k * v 1] := by
  have h : a • cexCh = Matrix.diagonal ![a / 2, 2 * a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cexCh, Matrix.diagonal] <;> ring
  rw [h, Matrix.diagonal_pow]
  funext i
  rw [Matrix.mulVec_diagonal]
  fin_cases i <;> simp

/-- Woodford (2003), (2.24): `2a` is an eigenvalue of `aĈ`, `Ĉ = diag(1/2, 2)`. -/
theorem cexCh_isEig (a : ℝ) :
    KroneckerSpectrum.IsEig ((a • cexCh).map Complex.ofReal) ((2 * a : ℝ) : ℂ) := by
  refine ⟨![0, 1], by simp, ?_⟩
  funext i
  fin_cases i
  · simp [cexCh, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.diagonal]
  · simp [cexCh, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.diagonal]
    ring

/-- Woodford (2003), (2.24): a row with no weight on the second state sums against `(aĈ)ᵏ` to
`φ′ (I − aĈ)⁻¹ s`. -/
theorem cexCh_hasSum {a : ℝ} (ha : |a| < 1) (ha2 : 2 * a ≠ 1) (φ : Fin 2 → ℝ) (hφ : φ 1 = 0)
    (v : Fin 2 → ℝ) :
    HasSum (fun k => φ ⬝ᵥ ((a • cexCh) ^ k *ᵥ v)) (φ ⬝ᵥ ((1 - a • cexCh)⁻¹ *ᵥ v)) := by
  have ha' : |a / 2| < 1 := by rw [abs_div]; norm_num; linarith [abs_nonneg a]
  have hinv : (1 - a • cexCh)⁻¹ = Matrix.diagonal ![(1 - a / 2)⁻¹, (1 - 2 * a)⁻¹] := by
    have h : 1 - a • cexCh = Matrix.diagonal ![1 - a / 2, 1 - 2 * a] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cexCh, Matrix.diagonal] <;> ring
    have h1 : (1 : ℝ) - a / 2 ≠ 0 := by
      intro h0
      have : a = 2 := by linarith
      rw [this] at ha
      norm_num at ha
    have h2 : (1 : ℝ) - 2 * a ≠ 0 := fun h0 => ha2 (by linarith)
    rw [h]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, h1, h2]
  rw [hinv]
  have hg := (hasSum_geometric_of_abs_lt_one ha').mul_right (φ 0 * v 0)
  convert hg using 1
  · funext k
    rw [cexCh_pow_mulVec]
    simp [dotProduct, Fin.sum_univ_two, hφ]
    ring
  · simp [dotProduct, Fin.sum_univ_two, hφ, Matrix.mulVec_diagonal]
    ring

/-- Woodford (2003), (2.24): a row with no weight on the second state gives a convergent series
against `(aĈ)ᵏ`, `|a| < 1`, whatever `2a`. -/
theorem cexCh_summable {a : ℝ} (ha : |a| < 1) (φ : Fin 2 → ℝ) (hφ : φ 1 = 0) (v : Fin 2 → ℝ) :
    Summable (fun k => φ ⬝ᵥ ((a • cexCh) ^ k *ᵥ v)) := by
  have ha' : |a / 2| < 1 := by rw [abs_div]; norm_num; linarith [abs_nonneg a]
  refine ((summable_geometric_of_abs_lt_one ha').mul_right (φ 0 * v 0)).congr fun k => ?_
  rw [cexCh_pow_mulVec]
  simp [dotProduct, Fin.sum_univ_two, hφ]
  ring

/-- Woodford (2003), (2.24): the row of a vector with no weight on the second state, times
`aĈ`, has no weight on the second state. -/
theorem cexCh_vecMul (a : ℝ) (φ : Fin 2 → ℝ) (h : φ 1 = 0) : (φ ᵥ* (a • cexCh)) 1 = 0 := by
  simp [cexCh, Matrix.vecMul, dotProduct, Matrix.diagonal, h]

/-- Woodford (2003), pp. 273–274: **the spectral-radius condition is not necessary**. Let
`Ĉ = diag(1/2, 2)` and `1/2 < β < 1`, `0 ≤ α < 1`, so that `βĈ` has the eigenvalue `2β > 1`, and
let the beliefs `Φ̂ₛ` and the loading `f_r` put no weight on the second (explosive) state. Then,
for every state history, every forecast sum and the series in (2.29) and (2.30) converge. -/
theorem forecast_sums_converge_without_spectral {α β κ σ : ℝ} {gr : Fin 2 → ℝ}
    (hβ0 : 1 / 2 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (Φ : Learning.Regression.Belief (Fin 3) (Fin 2)) (hΦ : ∀ j, Φ.2 j 1 = 0) (hgr : gr 1 = 0)
    (s : ℕ → Fin 2 → Ω → ℝ) (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ) :
    (∃ w, KroneckerSpectrum.IsEig ((β • cexCh).map Complex.ofReal) w ∧ 1 < ‖w‖) ∧
      (∀ j ω, Summable (fun k => β ^ k * fcast Φ cexCh s t k j ω) ∧
        Summable (fun k => (α * β) ^ k * fcast Φ cexCh s t k j ω) ∧
        Summable (fun k => β ^ k * rnfc gr cexCh s t k ω)) ∧
      ∀ ω, Summable (isTerm β σ gr Φ cexCh s z t ω) ∧
        Summable (asTerm α β κ Φ cexCh s z t ω) := by
  have hβa : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hαβa : |α * β| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  refine ⟨⟨_, cexCh_isEig β, ?_⟩, fun j ω => ⟨?_, ?_, ?_⟩, fun ω => ⟨?_, ?_⟩⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · exact (summable_fcast_iff hβa Φ cexCh s t j ω).mpr (cexCh_summable hβa _ (hΦ j) _)
  · exact (summable_fcast_iff hαβa Φ cexCh s t j ω).mpr (cexCh_summable hαβa _ (hΦ j) _)
  · refine (cexCh_summable hβa _ hgr (sv s t ω)).congr fun k => ?_
    simp only [rnfc, smul_pow, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  · refine (summable_isTerm_iff hβa σ gr Φ cexCh s z t ω).mpr (cexCh_summable hβa _ ?_ _)
    simp only [isRow, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hΦ, mul_zero, sub_zero]
    exact cexCh_vecMul β _ (by simp [hΦ, hgr])
  · refine (summable_asTerm_iff hαβa κ Φ cexCh s z t ω).mpr (cexCh_summable hαβa _ ?_ _)
    simp only [asRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hΦ, mul_zero, zero_add]
    rw [cexCh_vecMul _ _ (hΦ 0), mul_zero]

/-- Woodford (2003), pp. 273–274: **in the counterexample the actual law of motion is still
`z_t = tempSol(s_t)`**: with `Ĉ = diag(1/2, 2)`, `1/2 < β < 1`, `0 ≤ α < 1`, `2αβ ≠ 1` (so that
`I − αβĈ` is invertible; `I − βĈ` is, as `2β > 1`), and beliefs and `f_r` with no weight on the
second state, (2.29), (2.30) and (1.14) hold at `t` iff `z_t = tempSol(s_t)`, although `βĈ` has
the eigenvalue `2β > 1`. -/
theorem decisionRules_without_spectral {α β κ σ φπ φx πbar xbar ci : ℝ} {gr gi : Fin 2 → ℝ}
    (hβ0 : 1 / 2 < β) (hβ1 : β < 1) (hα0 : 0 ≤ α) (hα1 : α < 1) (h2αβ : 2 * (α * β) ≠ 1)
    (hΔ : taylorDelta σ κ φπ φx ≠ 0) (Φ : Learning.Regression.Belief (Fin 3) (Fin 2))
    (hΦ : ∀ j, Φ.2 j 1 = 0) (hgr : gr 1 = 0) (s : ℕ → Fin 2 → Ω → ℝ)
    (z : ℕ → Fin 3 → Ω → ℝ) (t : ℕ) :
    (IS229 β σ gr Φ cexCh s z t ∧ AS230 α β κ Φ cexCh s z t ∧
        TaylorRule φπ φx πbar xbar ci gi s z t) ↔
      ∀ ω, (fun j => z t j ω) =
        tempSol α β κ σ φπ φx (taylorConst φπ φx πbar xbar ci) gr gi Φ cexCh (sv s t ω) := by
  have hβa : |β| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hαβa : |α * β| < 1 := by rw [abs_lt]; constructor <;> nlinarith
  have h2β : 2 * β ≠ 1 := by intro h; linarith
  exact decisionRules_iff_of_hasSum (by linarith) hβ1 hα0 hα1 hΔ s z t
    (fun ω j => cexCh_hasSum hβa h2β _ (hΦ j) _) (fun ω j => cexCh_hasSum hαβa h2αβ _ (hΦ j) _)
    (fun ω => cexCh_hasSum hβa h2β _ hgr _)

end Woodford.NeoWicksellianFramework.TidyR5ForecastSums
