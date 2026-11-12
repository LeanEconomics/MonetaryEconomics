/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.PencilRepeated

/-!
# Proposition 8.1 when the selection takes only part of a repeated root

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (p. 552), Appendix G.1
(pp. 716–718), Propositions 8.1 and 8.2.

`PencilRepeated.exists_realSelection_general` builds the real deflating pair `A J = Î J Ψ` when
the selection takes whole root classes (`PencilRepeated.SelWhole`). This module removes that
hypothesis and says exactly what survives.

## Existence survives

* `exists_inv_sub` (linear algebra): if `f − ν` is nilpotent on an `f`-invariant subspace `X`,
  then `X` contains an `f`-invariant subspace of every dimension `k ≤ dim X` (add one vector at a
  time: a vector `x ∉ U` with `(f − ν)x ∈ U`).
* The selected subspace `Wp`: for each selected value `ν = (μ − s)⁻¹` of `N = (A − sÎ)⁻¹Î`, an
  `N`-invariant subspace of the generalised eigenspace of dimension `sel.count μ` (complexified
  from a real one when `μ` is real; for a conjugate pair, one is chosen for `Im ν > 0` and the
  other is its conjugate), plus `ker A`. It is conjugation-stable, `N`-invariant and has dimension
  `(n − rank A) + #sel` (`finrank_Wp`).
* `exists_deflating_cols_partial`, `exists_realSelection_partial`: a real deflating pair exists for
  EVERY conjugation-closed selection of nonzero roots (each with at most its multiplicity), so
  `prop81_of_assumptions_partial`, `prop82_of_assumptions_partial`: Propositions 8.1 and 8.2 hold
  without `SelWhole`.

## Uniqueness fails

* `partial_nonunique`: for `rSys` (`n_Z = n_z = 1`, `A = ½ I`, `Î = I`: the double root `½`,
  semisimple) the selection `{½}` takes one copy of the double root; every line is an invariant
  subspace, and two of them give deflating splits with `Υ = 0` and `Υ = −1`. So the
  representation of Proposition 8.1 (`Υ`, and with it `R(L⁻¹)` and the target criterion) depends
  on a choice that the selection does not determine.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bPartialSel

open Matrix Polynomial GeneralSetup PencilSplit PencilEigen PencilAssumptions PencilRepeated
  GeneralFOC.Selection

/-! ### Invariant subspaces of every dimension -/

/-- Woodford (2003), App. G.1 (linear algebra): if `f` maps `X` into itself and `f − ν` is
nilpotent on `X`, then for every `k ≤ dim X` there is an `f`-invariant subspace `U ≤ X` of
dimension `k`. -/
theorem exists_inv_sub {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : V →ₗ[K] V) (ν : K) (X : Submodule K V)
    (hX : ∀ x ∈ X, f x ∈ X) (hnil : ∀ x ∈ X, ∃ n : ℕ, ((f - ν • 1) ^ n) x = 0) :
    ∀ k ≤ Module.finrank K X, ∃ U : Submodule K V, U ≤ X ∧ (∀ x ∈ U, f x ∈ U) ∧
      Module.finrank K U = k := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨⊥, bot_le, fun x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero],
      finrank_bot K V⟩
  | succ k ih =>
    intro hk
    obtain ⟨U, hUX, hUf, hUk⟩ := ih (by omega)
    set g := f - ν • (1 : V →ₗ[K] V) with hg
    have hgX : ∀ x ∈ X, g x ∈ X := fun x hx => by
      rw [hg, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact X.sub_mem (hX x hx) (X.smul_mem ν hx)
    have hgnX : ∀ n, ∀ x ∈ X, (g ^ n) x ∈ X := by
      intro n
      induction n with
      | zero => intro x hx; simpa using hx
      | succ n ihn =>
        intro x hx
        rw [pow_succ', Module.End.mul_apply]
        exact hgX _ (ihn x hx)
    have hlt : U < X := by
      refine lt_of_le_of_ne hUX fun h => ?_
      rw [h] at hUk
      omega
    obtain ⟨y, hyX, hyU⟩ := SetLike.exists_of_lt hlt
    obtain ⟨n, hn⟩ := hnil y hyX
    have hex : ∃ j, (g ^ j) y ∈ U := ⟨n, by rw [hn]; exact U.zero_mem⟩
    set j := Nat.find hex with hj
    have hjU : (g ^ j) y ∈ U := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero, Module.End.one_apply] at hjU
      exact hyU hjU
    set x := (g ^ (j - 1)) y with hx
    have hxU : x ∉ U := Nat.find_min hex (by omega)
    have hgx : g x ∈ U := by
      rw [hx, ← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
      exact hjU
    have hxX : x ∈ X := hgnX _ _ hyX
    refine ⟨U ⊔ K ∙ x, sup_le hUX ((Submodule.span_singleton_le_iff_mem _ _).mpr hxX),
      fun v hv => ?_, ?_⟩
    · obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have hfx : f x = g x + ν • x := by
        rw [hg, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        abel
      rw [map_add, map_smul, hfx]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (hUf u hu)) ?_
      rw [smul_add, smul_smul]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (U.smul_mem _ hgx))
        (Submodule.mem_sup_right (Submodule.mem_span_singleton.mpr ⟨a * ν, rfl⟩))
    · have hx0 : x ≠ 0 := fun h => hxU (by rw [h]; exact U.zero_mem)
      have hinf : U ⊓ K ∙ x = ⊥ := by
        rw [eq_bot_iff]
        intro v hv
        obtain ⟨hvU, hvx⟩ := Submodule.mem_inf.mp hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvx
        rw [Submodule.mem_bot]
        by_contra ha
        have ha0 : a ≠ 0 := fun h => ha (by rw [h, zero_smul])
        apply hxU
        have := U.smul_mem a⁻¹ hvU
        rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq U (K ∙ x)
      rw [hinf, finrank_bot, add_zero, finrank_span_singleton hx0, hUk] at h
      exact h

/-! ### Complexification and conjugation of subspaces -/

/-- Woodford (2003), App. G.1, fn 2: the complexification `span_ℂ U` of a real subspace. -/
noncomputable def cplx {κ : Type*} (U : Submodule ℝ (κ → ℝ)) : Submodule ℂ (κ → ℂ) :=
  Submodule.span ℂ {w | ∃ v ∈ U, w = fun i => (v i : ℂ)}

/-- Woodford (2003), App. G.1: a real vector of `U` lies in its complexification. -/
theorem ofReal_mem_cplx {κ : Type*} {U : Submodule ℝ (κ → ℝ)} {v : κ → ℝ} (hv : v ∈ U) :
    (fun i => (v i : ℂ)) ∈ cplx U :=
  Submodule.subset_span ⟨v, hv, rfl⟩

/-- Woodford (2003), App. G.1: the complexification is the smallest complex subspace containing
the real vectors of `U`. -/
theorem cplx_le {κ : Type*} {U : Submodule ℝ (κ → ℝ)} {W : Submodule ℂ (κ → ℂ)}
    (h : ∀ v ∈ U, (fun i => (v i : ℂ)) ∈ W) : cplx U ≤ W :=
  Submodule.span_le.mpr (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)

/-- Woodford (2003), App. G.1: a complexification is closed under conjugation. -/
theorem cplx_conjStable {κ : Type*} (U : Submodule ℝ (κ → ℝ)) : ConjStable (cplx U) := by
  intro w hw
  have h : cplx U ≤ conjPre (cplx U) := cplx_le fun v hv => by
    change (fun i => starRingEnd ℂ ((v i : ℂ))) ∈ cplx U
    simp only [Complex.conj_ofReal]
    exact ofReal_mem_cplx hv
  exact h hw

/-- Woodford (2003), App. G.1: the complexification of a subspace invariant under a real matrix
is invariant. -/
theorem cplx_inv {κ : Type*} [Fintype κ] (N : Matrix κ κ ℝ)
    {U : Submodule ℝ (κ → ℝ)} (hU : ∀ v ∈ U, N *ᵥ v ∈ U) :
    ∀ w ∈ cplx U, N.map Complex.ofReal *ᵥ w ∈ cplx U := by
  classical
  have h : cplx U ≤ (cplx U).comap (Matrix.toLin' (N.map Complex.ofReal)) :=
    cplx_le fun v hv => by
      rw [Submodule.mem_comap, Matrix.toLin'_apply, map_mulVec_ofReal]
      exact ofReal_mem_cplx (hU v hv)
  intro w hw
  have := h hw
  rwa [Submodule.mem_comap, Matrix.toLin'_apply] at this

/-- Woodford (2003), App. G.1, fn 2: `dim_ℂ (span_ℂ U) = dim_ℝ U`. -/
theorem finrank_cplx {κ : Type*} [Finite κ] (U : Submodule ℝ (κ → ℝ)) :
    Module.finrank ℂ (cplx U) = Module.finrank ℝ U := by
  set b := Module.finBasis ℝ U with hb
  set f : Fin (Module.finrank ℝ U) → (κ → ℂ) := fun k i => (((b k : U) : κ → ℝ) i : ℂ) with hf
  have hind : LinearIndependent ℂ f :=
    linearIndependent_ofReal (b.linearIndependent.map' U.subtype (Submodule.ker_subtype _))
  have hspan : cplx U = Submodule.span ℂ (Set.range f) := by
    refine le_antisymm (cplx_le fun v hv => ?_) (Submodule.span_le.mpr ?_)
    · have e : (fun i => (v i : ℂ)) = ∑ k, ((b.repr ⟨v, hv⟩ k : ℝ) : ℂ) • f k := by
        funext i
        have := congrArg (fun z : U => (z : κ → ℝ) i) (b.sum_repr ⟨v, hv⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hf, ← this, Complex.ofReal_sum,
          Complex.ofReal_mul]
      rw [e]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
    · rintro _ ⟨k, rfl⟩
      exact ofReal_mem_cplx (b k).2
  rw [hspan, finrank_span_eq_card hind, Fintype.card_fin]

/-- Woodford (2003), App. G.1: conjugating twice. -/
theorem conjPre_conjPre {κ : Type*} (U : Submodule ℂ (κ → ℂ)) : conjPre (conjPre U) = U := by
  ext w
  change (fun i => starRingEnd ℂ (starRingEnd ℂ (w i))) ∈ U ↔ w ∈ U
  simp

/-- Woodford (2003), App. G.1: conjugation does not decrease dimension. -/
theorem finrank_le_conjPre {κ : Type*} [Finite κ] (U : Submodule ℂ (κ → ℂ)) :
    Module.finrank ℂ U ≤ Module.finrank ℂ (conjPre U) := by
  set b := Module.finBasis ℂ U with hb
  set g : Fin (Module.finrank ℂ U) → (κ → ℂ) :=
    fun k i => starRingEnd ℂ (((b k : U) : κ → ℂ) i) with hg
  have hind : LinearIndependent ℂ g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 : ∑ k, starRingEnd ℂ (c k) • ((b k : U) : κ → ℂ) = 0 := by
      funext i
      have := congrFun hc i
      have h2 := congrArg (starRingEnd ℂ) this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        Complex.conj_conj, Pi.zero_apply, map_zero, hg] at h2
      simpa [Finset.sum_apply] using h2
    have h3 : ∑ k, starRingEnd ℂ (c k) • b k = 0 := by
      apply Subtype.ext
      simpa using h1
    have := Fintype.linearIndependent_iff.mp b.linearIndependent _ h3 k
    simpa using this
  have hle : Submodule.span ℂ (Set.range g) ≤ conjPre U := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change (fun i => starRingEnd ℂ (starRingEnd ℂ (((b k : U) : κ → ℂ) i))) ∈ U
    simp only [Complex.conj_conj]
    exact (b k).2
  calc Module.finrank ℂ U = Module.finrank ℂ (Submodule.span ℂ (Set.range g)) := by
        rw [finrank_span_eq_card hind, Fintype.card_fin]
    _ ≤ _ := Submodule.finrank_mono hle

/-- Woodford (2003), App. G.1: conjugation preserves dimension. -/
theorem finrank_conjPre {κ : Type*} [Finite κ] (U : Submodule ℂ (κ → ℂ)) :
    Module.finrank ℂ (conjPre U) = Module.finrank ℂ U := by
  refine le_antisymm ?_ (finrank_le_conjPre U)
  have := finrank_le_conjPre (conjPre U)
  rwa [conjPre_conjPre] at this

/-! ### Invariant blocks inside the generalised eigenspaces of `N` -/

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-- Woodford (2003), App. G.1: `N` maps its generalised eigenspace into itself. -/
theorem maxGen_mapsTo (S : LinearRESystem ιZ ιz) (s : ℝ) (ν : ℂ) :
    ∀ x ∈ (φN S s).maxGenEigenspace ν, φN S s x ∈ (φN S s).maxGenEigenspace ν :=
  fun _ hx => Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) ν hx

/-- Woodford (2003), App. G.1: `N − ν` is nilpotent on the generalised eigenspace of `ν`. -/
theorem maxGen_nil (S : LinearRESystem ιZ ιz) (s : ℝ) (ν : ℂ) :
    ∀ x ∈ (φN S s).maxGenEigenspace ν, ∃ n : ℕ, ((φN S s - ν • 1) ^ n) x = 0 :=
  fun _ hx => by
    rw [Module.End.mem_maxGenEigenspace] at hx
    exact hx

/-- Woodford (2003), App. G.1: an `N`-invariant subspace of dimension `min k m` of the
generalised eigenspace (dimension `m`) of `ν`. -/
noncomputable def cBlock (S : LinearRESystem ιZ ιz) (s : ℝ) (ν : ℂ) (k : ℕ) :
    Submodule ℂ (ιZ ⊕ ιz → ℂ) :=
  Classical.choose (exists_inv_sub (φN S s) ν _ (maxGen_mapsTo S s ν) (maxGen_nil S s ν)
    (min k (Module.finrank ℂ ((φN S s).maxGenEigenspace ν))) (min_le_right _ _))

/-- Woodford (2003), App. G.1: the defining properties of `cBlock`. -/
theorem cBlock_spec (S : LinearRESystem ιZ ιz) (s : ℝ) (ν : ℂ) (k : ℕ) :
    cBlock S s ν k ≤ (φN S s).maxGenEigenspace ν ∧
      (∀ x ∈ cBlock S s ν k, φN S s x ∈ cBlock S s ν k) ∧
      Module.finrank ℂ (cBlock S s ν k) =
        min k (Module.finrank ℂ ((φN S s).maxGenEigenspace ν)) :=
  Classical.choose_spec (exists_inv_sub (φN S s) ν _ (maxGen_mapsTo S s ν) (maxGen_nil S s ν)
    (min k (Module.finrank ℂ ((φN S s).maxGenEigenspace ν))) (min_le_right _ _))

/-- Woodford (2003), App. G.1: for real `r`, `(N − r)ⁿ` commutes with complexification. -/
theorem ofReal_pow_apply (S : LinearRESystem ιZ ιz) (s r : ℝ) (n : ℕ) (v : ιZ ⊕ ιz → ℝ) :
    (fun i => ((((Nr S s).mulVecLin - r • (1 : Module.End ℝ (ιZ ⊕ ιz → ℝ))) ^ n) v i : ℂ)) =
      ((φN S s - (r : ℂ) • 1) ^ n) (fun i => (v i : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
    funext i
    simp [φN, Matrix.toLin'_apply, map_mulVec_ofReal]

/-- Woodford (2003), App. G.1: the real part of the generalised eigenspace of a real `r` is
`N`-invariant. -/
theorem realMaxGen_mapsTo (S : LinearRESystem ιZ ιz) (s r : ℝ) :
    ∀ v ∈ realPart ((φN S s).maxGenEigenspace (r : ℂ)),
      (Nr S s).mulVecLin v ∈ realPart ((φN S s).maxGenEigenspace (r : ℂ)) := by
  intro v hv
  change (fun i => ((Nr S s *ᵥ v) i : ℂ)) ∈ (φN S s).maxGenEigenspace (r : ℂ)
  rw [← map_mulVec_ofReal]
  have := maxGen_mapsTo S s r _ hv
  rwa [φN, Matrix.toLin'_apply] at this

/-- Woodford (2003), App. G.1: `N − r` is nilpotent on the real part of the generalised
eigenspace of a real `r`. -/
theorem realMaxGen_nil (S : LinearRESystem ιZ ιz) (s r : ℝ) :
    ∀ v ∈ realPart ((φN S s).maxGenEigenspace (r : ℂ)),
      ∃ n : ℕ, (((Nr S s).mulVecLin - r • (1 : Module.End ℝ (ιZ ⊕ ιz → ℝ))) ^ n) v = 0 := by
  intro v hv
  obtain ⟨n, hn⟩ := maxGen_nil S s r _ hv
  refine ⟨n, funext fun i => ?_⟩
  have := congrFun (ofReal_pow_apply S s r n v) i
  rw [hn, Pi.zero_apply] at this
  simp only [Pi.zero_apply]
  exact_mod_cast this

/-- Woodford (2003), App. G.1, fn 2: for real `r`, the real part of the generalised eigenspace
has the complex dimension. -/
theorem finrank_realMaxGen (S : LinearRESystem ιZ ιz) (s r : ℝ) :
    Module.finrank ℝ (realPart ((φN S s).maxGenEigenspace (r : ℂ))) =
      Module.finrank ℂ ((φN S s).maxGenEigenspace (r : ℂ)) := by
  refine finrank_realPart _ fun w hw => ?_
  have := conj_mem_maxGen (Nr S s) hw
  rwa [Complex.conj_ofReal] at this

/-- Woodford (2003), App. G.1, fn 2: a real `N`-invariant subspace of dimension `min k m` of the
real generalised eigenspace (dimension `m`) of a real `r`. -/
noncomputable def rBlock (S : LinearRESystem ιZ ιz) (s r : ℝ) (k : ℕ) :
    Submodule ℝ (ιZ ⊕ ιz → ℝ) :=
  Classical.choose (exists_inv_sub (Nr S s).mulVecLin r _ (realMaxGen_mapsTo S s r)
    (realMaxGen_nil S s r)
    (min k (Module.finrank ℝ (realPart ((φN S s).maxGenEigenspace (r : ℂ))))) (min_le_right _ _))

/-- Woodford (2003), App. G.1: the defining properties of `rBlock`. -/
theorem rBlock_spec (S : LinearRESystem ιZ ιz) (s r : ℝ) (k : ℕ) :
    rBlock S s r k ≤ realPart ((φN S s).maxGenEigenspace (r : ℂ)) ∧
      (∀ x ∈ rBlock S s r k, (Nr S s).mulVecLin x ∈ rBlock S s r k) ∧
      Module.finrank ℝ (rBlock S s r k) =
        min k (Module.finrank ℝ (realPart ((φN S s).maxGenEigenspace (r : ℂ)))) :=
  Classical.choose_spec (exists_inv_sub (Nr S s).mulVecLin r _ (realMaxGen_mapsTo S s r)
    (realMaxGen_nil S s r)
    (min k (Module.finrank ℝ (realPart ((φN S s).maxGenEigenspace (r : ℂ))))) (min_le_right _ _))

/-! ### The selected subspace for a partial selection -/

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), Assumption 8.2: the number of selected copies of the root `μ = s + ν⁻¹`
belonging to the eigenvalue `ν` of `N`. -/
noncomputable def kc (sel : Multiset ℂ) (s : ℝ) (ν : ℂ) : ℕ := sel.count ((s : ℂ) + ν⁻¹)

/-- Woodford (2003), App. G.1, (G.4) (**partial selections**): the block of the selected subspace
belonging to the eigenvalue `ν` of `N`: `ker A` for `ν₀`; for a real `ν`, the complexification
of a real invariant subspace of dimension `kc ν`; for `Im ν > 0`, an invariant subspace of
dimension `kc ν`; for `Im ν < 0`, the conjugate of the block of `ν̄`. -/
noncomputable def Ublk (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) (ν : ℂ) :
    Submodule ℂ (ιZ ⊕ ιz → ℂ) :=
  if ν = ν0 s then (φN S s).eigenspace ν
  else if ν.im = 0 then cplx (rBlock S s ν.re (kc sel s ν))
  else if 0 < ν.im then cBlock S s ν (kc sel s ν)
  else conjPre (cBlock S s (starRingEnd ℂ ν) (kc sel s (starRingEnd ℂ ν)))

/-- Woodford (2003), App. G.1, (G.4): the selected subspace for a partial selection. -/
noncomputable def Wp (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) :
    Submodule ℂ (ιZ ⊕ ιz → ℂ) :=
  (Tset sel s).sup (Ublk S sel s)

/-- Woodford (2003), App. G.1: the block of `ν₀` is `ker A` (the eigenspace of `ν₀`). -/
theorem Ublk_ν0 (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) :
    Ublk S sel s (ν0 s) = (φN S s).eigenspace (ν0 s) := by
  simp [Ublk]

/-- Woodford (2003), App. G.1: the block of a real eigenvalue `ν ≠ ν₀`. -/
theorem Ublk_real (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) {ν : ℂ}
    (h0 : ν ≠ ν0 s) (hre : ν.im = 0) :
    Ublk S sel s ν = cplx (rBlock S s ν.re (kc sel s ν)) := by
  simp [Ublk, h0, hre]

/-- Woodford (2003), App. G.1: the block of an eigenvalue with `Im ν > 0`. -/
theorem Ublk_pos (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) {ν : ℂ}
    (h0 : ν ≠ ν0 s) (hpos : 0 < ν.im) : Ublk S sel s ν = cBlock S s ν (kc sel s ν) := by
  simp [Ublk, h0, hpos, hpos.ne']

/-- Woodford (2003), App. G.1: the block of an eigenvalue with `Im ν < 0`. -/
theorem Ublk_neg (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) {ν : ℂ}
    (h0 : ν ≠ ν0 s) (hre : ν.im ≠ 0) (hpos : ¬ 0 < ν.im) :
    Ublk S sel s ν = conjPre (cBlock S s (starRingEnd ℂ ν) (kc sel s (starRingEnd ℂ ν))) := by
  simp [Ublk, h0, hre, hpos]

/-- Woodford (2003), App. G.1: a block lies in the generalised eigenspace of its eigenvalue
(`Wfam`). -/
theorem Ublk_le_Wfam (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) (ν : ℂ) :
    Ublk S sel s ν ≤ Wfam S s ν := by
  unfold Ublk
  split_ifs with h0 hre hpos
  · rw [h0, Wfam_ν0]
  · rw [Wfam_ne S s h0]
    refine cplx_le fun v hv => ?_
    have h1 := (rBlock_spec S s ν.re (kc sel s ν)).1 hv
    have hν : ((ν.re : ℝ) : ℂ) = ν := Complex.ext (by simp) (by simp [hre])
    change (fun i => (v i : ℂ)) ∈ (φN S s).maxGenEigenspace ((ν.re : ℝ) : ℂ) at h1
    rwa [hν] at h1
  · rw [Wfam_ne S s h0]
    exact (cBlock_spec S s ν _).1
  · rw [Wfam_ne S s h0]
    intro w hw
    have h1 := (cBlock_spec S s _ _).1 hw
    have h2 := conj_mem_maxGen (Nr S s) h1
    simp only [Complex.conj_conj] at h2
    exact h2

/-- Woodford (2003), App. G.1: every block is `N`-invariant. -/
theorem Ublk_inv (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) (ν : ℂ) :
    ∀ w ∈ Ublk S sel s ν, φN S s w ∈ Ublk S sel s ν := by
  unfold Ublk
  split_ifs with h0 hre hpos
  · intro w hw
    rw [Module.End.mem_eigenspace_iff] at hw ⊢
    rw [hw, map_smul, hw]
  · intro w hw
    rw [φN, Matrix.toLin'_apply]
    exact cplx_inv (Nr S s) (fun v hv => (rBlock_spec S s ν.re _).2.1 v hv) w hw
  · exact (cBlock_spec S s ν _).2.1
  · intro w hw
    change (fun i => starRingEnd ℂ (φN S s w i)) ∈
      cBlock S s (starRingEnd ℂ ν) (kc sel s (starRingEnd ℂ ν))
    have h1 := (cBlock_spec S s (starRingEnd ℂ ν) _).2.1 _ hw
    rw [φN, Matrix.toLin'_apply] at h1 ⊢
    rw [← map_mulVec_conj]
    exact h1

/-- Woodford (2003), App. G.1, p. 716: conjugation maps the block of `ν` into the block of `ν̄`
(the selection is closed under conjugation). -/
theorem Ublk_conj (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) (ν : ℂ) :
    ∀ w ∈ Ublk S sel s ν, (fun i => starRingEnd ℂ (w i)) ∈ Ublk S sel s (starRingEnd ℂ ν) := by
  have hν0r : starRingEnd ℂ (ν0 s) = ν0 s := by rw [ν0_eq, Complex.conj_ofReal]
  by_cases h0 : ν = ν0 s
  · subst h0
    intro w hw
    simp only [Ublk, ↓reduceIte, hν0r] at hw ⊢
    have := conj_mem_eigenspace (Nr S s) (-s⁻¹) (by rw [← ν0_eq]; exact hw)
    rwa [← ν0_eq] at this
  have h0' : starRingEnd ℂ ν ≠ ν0 s := by
    intro h
    apply h0
    rw [← hν0r, ← h, Complex.conj_conj]
  by_cases hre : ν.im = 0
  · have hc : starRingEnd ℂ ν = ν := Complex.ext (by simp) (by simp [hre])
    rw [hc]
    intro w hw
    simp only [Ublk, h0, ↓reduceIte, hre] at hw ⊢
    exact cplx_conjStable _ w hw
  · have hre' : (starRingEnd ℂ ν).im ≠ 0 := by simpa using hre
    by_cases hpos : 0 < ν.im
    · have hneg : ¬ 0 < (starRingEnd ℂ ν).im := by simp; linarith
      intro w hw
      simp only [Ublk, h0, h0', ↓reduceIte, hre, hre', hpos, hneg, Complex.conj_conj] at hw ⊢
      change (fun i => starRingEnd ℂ (starRingEnd ℂ (w i))) ∈ cBlock S s ν (kc sel s ν)
      simpa using hw
    · have hpos' : 0 < (starRingEnd ℂ ν).im := by
        simp only [Complex.conj_im, Left.neg_pos_iff]
        exact lt_of_le_of_ne (not_lt.mp hpos) hre
      intro w hw
      simp only [Ublk, h0, h0', ↓reduceIte, hre, hre', hpos, hpos'] at hw ⊢
      exact hw

/-- Woodford (2003), Assumption 8.2: the eigenvalues used are closed under conjugation. -/
theorem Tset_conj {sel : Multiset ℂ} (hc : ConjClosed sel) (s : ℝ) {ν : ℂ}
    (hν : ν ∈ Tset sel s) : starRingEnd ℂ ν ∈ Tset sel s := by
  rw [Tset, Finset.mem_insert] at hν ⊢
  rcases hν with h | h
  · left
    rw [h, ν0_eq, Complex.conj_ofReal]
  · right
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp h
    refine Finset.mem_image.mpr ⟨starRingEnd ℂ μ, Multiset.mem_toFinset.mpr
      (hc.conj_mem (Multiset.mem_toFinset.mp hμ)), ?_⟩
    simp [map_inv₀, map_sub]

/-- Woodford (2003), App. G.1, p. 716: the selected subspace is closed under conjugation. -/
theorem Wp_conj (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} (hc : ConjClosed sel) (s : ℝ) :
    ConjStable (Wp S sel s) := by
  intro w hw
  have hle : Wp S sel s ≤ conjPre (Wp S sel s) := by
    refine Finset.sup_le fun ν hν v hv => ?_
    change (fun i => starRingEnd ℂ (v i)) ∈ Wp S sel s
    exact (Finset.le_sup (f := Ublk S sel s) (Tset_conj hc s hν)) (Ublk_conj S sel s ν v hv)
  exact hle hw

/-- Woodford (2003), App. G.1: the selected subspace is `N`-invariant. -/
theorem Wp_inv (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) {w : ιZ ⊕ ιz → ℂ}
    (hw : w ∈ Wp S sel s) : φN S s w ∈ Wp S sel s := by
  have hle : Wp S sel s ≤ (Wp S sel s).comap (φN S s) := by
    refine Finset.sup_le fun ν hν v hv => ?_
    rw [Submodule.mem_comap]
    exact (Finset.le_sup (f := Ublk S sel s) hν) (Ublk_inv S sel s ν v hv)
  exact hle hw

/-- Woodford (2003), App. G.1: the selected subspace lies in `PencilRepeated.Wsub`. -/
theorem Wp_le (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) :
    Wp S sel s ≤ Wsub S sel s :=
  Finset.sup_mono_fun fun ν _ => Ublk_le_Wfam S sel s ν

/-- Woodford (2003), App. G.1: the generalised eigenspace of `(μ − s)⁻¹` has the multiplicity of
`μ` as a root of (1.15) as its dimension. -/
theorem finrank_maxGen (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    {μ : ℂ} (hμs : μ ≠ (s : ℂ)) :
    Module.finrank ℂ ((φN S s).maxGenEigenspace (μ - s)⁻¹) = S.pencilPoly.roots.count μ := by
  rw [LinearMap.finrank_maxGenEigenspace_eq, φN, Matrix.charpoly_toLin', ← count_roots]
  exact (count_pencil_roots S hs hμs).symm

/-- Woodford (2003), Assumption 8.2: a selected root differs from the shift `s`. -/
theorem sel_ne_shift (S : LinearRESystem ιZ ιz) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    {μ : ℂ} (hμ : S.pencilPoly.eval μ = 0) : μ ≠ (s : ℂ) := by
  intro h
  apply hs
  rw [h, pencilPoly_eval, det_pencil_ofReal] at hμ
  exact_mod_cast hμ

/-- Woodford (2003), Assumption 8.2 and App. G.1: **the block of a selected root `μ` has
dimension `sel.count μ`** (each selected root taken at most with its multiplicity). -/
theorem finrank_Ublk (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} (hc : ConjClosed sel)
    {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ) {μ : ℂ} (hμ : μ ∈ sel) :
    Module.finrank ℂ (Ublk S sel s (μ - s)⁻¹) = sel.count μ := by
  have hne := inv_sub_ne_ν0 (s := s) (hsel μ hμ).1
  have hkc : ∀ μ' : ℂ, kc sel s (μ' - s)⁻¹ = sel.count μ' := fun μ' => by
    simp [kc]
  have hdim := finrank_maxGen S hs (sel_ne_shift S hs (hsel μ hμ).2)
  have hk := hcnt μ hμ
  by_cases hre : ((μ - s)⁻¹).im = 0
  · rw [Ublk_real S sel s hne hre, finrank_cplx, (rBlock_spec S s _ _).2.2, finrank_realMaxGen]
    have hν : (((μ - s)⁻¹).re : ℂ) = (μ - s)⁻¹ := Complex.ext (by simp) (by simp [hre])
    rw [hν, hdim, hkc]
    exact min_eq_left hk
  by_cases hpos : 0 < ((μ - s)⁻¹).im
  · rw [Ublk_pos S sel s hne hpos, (cBlock_spec S s _ _).2.2, hdim, hkc]
    exact min_eq_left hk
  · rw [Ublk_neg S sel s hne hre hpos, finrank_conjPre, (cBlock_spec S s _ _).2.2]
    have hconj : starRingEnd ℂ ((μ - s)⁻¹) = (starRingEnd ℂ μ - s)⁻¹ := by
      simp [map_inv₀, map_sub]
    have hcμ : starRingEnd ℂ μ ∈ sel := hc.conj_mem hμ
    have hcount : sel.count (starRingEnd ℂ μ) = sel.count μ := by
      conv_lhs => rw [← hc]
      exact Multiset.count_map_eq_count' _ _ (starRingEnd ℂ).injective _
    rw [hconj, finrank_maxGen S hs (sel_ne_shift S hs (hsel _ hcμ).2), hkc, hcount]
    exact min_eq_left (hcount ▸ hcnt _ hcμ)

/-- Woodford (2003), Assumption 8.2 and App. G.1: **`dim Wp = (n − rank A) + #sel`** for a
partial selection. -/
theorem finrank_Wp (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} (hc : ConjClosed sel)
    {s : ℝ} (hs0 : s ≠ 0) (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ) :
    Module.finrank ℂ (Wp S sel s) =
      (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) + Multiset.card sel := by
  have hnot : ν0 s ∉ sel.toFinset.image fun μ : ℂ => (μ - s)⁻¹ := by
    intro h
    obtain ⟨μ, hμ, he⟩ := Finset.mem_image.mp h
    exact inv_sub_ne_ν0 (hsel μ (Multiset.mem_toFinset.mp hμ)).1 he
  have hinj : Set.InjOn (fun μ : ℂ => (μ - s)⁻¹) (sel.toFinset : Set ℂ) :=
    fun a _ b _ h => sub_left_injective (inv_injective h)
  have hind : iSupIndep (Ublk S sel s) := (Wfam_indep S s).mono (Ublk_le_Wfam S sel s)
  rw [Wp, finrank_finset_sup hind, Tset, Finset.sum_insert hnot, Finset.sum_image hinj]
  congr 1
  · rw [Ublk_ν0]
    exact finrank_eigenspace_ν0 S hs0 hs
  · rw [← Multiset.toFinset_sum_count_eq]
    exact Finset.sum_congr rfl fun μ hμ =>
      finrank_Ublk S hc hs hsel hcnt (Multiset.mem_toFinset.mp hμ)

/-! ### The real deflating pair for a partial selection -/

/-- Woodford (2003), App. G.1, (G.4) and fn 2 (**partial selections allowed**), for any number of
columns: a conjugation-closed multiset `sel` of nonzero roots of a nonzero (1.15), each taken
**at most** with its multiplicity, gives a real `n × κ` matrix `J` with independent columns,
`#κ = (n − rank A) + #sel`, and `Ψ` with `A J = Î J Ψ`, every eigenvalue of `Ψ` zero or in
`sel`. -/
theorem exists_deflating_cols_partial (S : LinearRESystem ιZ ιz) {κ : Type*} [Fintype κ]
    [DecidableEq κ] {sel : Multiset ℂ} (hi : ConjClosed sel)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0) (hreg : S.pencilPoly ≠ 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ)
    (hcard : (Fintype.card (ιZ ⊕ ιz) - S.Ahat.rank) + Multiset.card sel = Fintype.card κ) :
    ∃ (J : Matrix (ιZ ⊕ ιz) κ ℝ) (Ψ : Matrix κ κ ℝ), S.Ahat * J = S.Ihat * J * Ψ ∧
      LinearIndependent ℝ Jᵀ ∧
      ∀ μ : ℂ, (Matrix.scalar κ μ - Ψ.map Complex.ofReal).det = 0 → μ = 0 ∨ μ ∈ sel := by
  obtain ⟨s, hs0, hsev⟩ := PencilEigen.Construction.exists_shift hreg
  have hs : (S.Ahat - s • S.Ihat).det ≠ 0 := by
    intro h
    apply hsev
    rw [pencilPoly_eval, det_pencil_ofReal, h, Complex.ofReal_zero]
  set U := realPart (Wp S sel s) with hU
  have hdim : Module.finrank ℝ U = Fintype.card κ := by
    rw [hU, finrank_realPart _ (Wp_conj S hi s), finrank_Wp S hi hs0 hs hsel hcnt, hcard]
  have hUle : ∀ v ∈ U, v ∈ Ureal S sel s := fun v hv => Wp_le S sel s hv
  have hNU : ∀ v ∈ U, Nr S s *ᵥ v ∈ U := by
    intro v hv
    change (fun i => ((Nr S s *ᵥ v) i : ℂ)) ∈ Wp S sel s
    rw [← map_mulVec_ofReal]
    have := Wp_inv S sel s (w := fun i => (v i : ℂ)) hv
    rwa [φN, Matrix.toLin'_apply] at this
  let b := Module.finBasisOfFinrankEq ℝ U hdim
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let col : κ → ιZ ⊕ ιz → ℝ := fun c => (b (e c) : ιZ ⊕ ιz → ℝ)
  have hcolU : ∀ c, col c ∈ U := fun c => (b (e c)).2
  let T : U →ₗ[ℝ] U := (Nr S s).mulVecLin.restrict (fun v hv => hNU v hv)
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have h0 : Nr S s *ᵥ (x : ιZ ⊕ ιz → ℝ) = 0 := by
      have := congrArg Subtype.val hx
      exact this
    exact Subtype.ext (Nr_inj_Ureal S hs0 hs hsel (hUle _ x.2) h0)
  have hTsurj := LinearMap.injective_iff_surjective.mp hTinj
  choose pre hpre using fun c => hTsurj ⟨col c, hcolU c⟩
  let x : κ → U := fun c => pre c + s • ⟨col c, hcolU c⟩
  let Ψ : Matrix κ κ ℝ := Matrix.of fun c' c => b.repr (x c) (e c')
  have hsum : ∀ c, ∑ c', Ψ c' c • col c' = (x c : ιZ ⊕ ιz → ℝ) := by
    intro c
    have h1 := b.sum_repr (x c)
    have h2 : ∑ c', Ψ c' c • col c' = ∑ i, b.repr (x c) i • (b i : ιZ ⊕ ιz → ℝ) :=
      Equiv.sum_comp e (fun i => b.repr (x c) i • (b i : ιZ ⊕ ιz → ℝ))
    rw [h2]
    have := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at this
    simpa using this
  have hcolA : ∀ c, S.Ahat *ᵥ col c = S.Ihat *ᵥ (x c : ιZ ⊕ ιz → ℝ) := by
    intro c
    have hp : Nr S s *ᵥ (pre c : ιZ ⊕ ιz → ℝ) = col c := by
      have := congrArg Subtype.val (hpre c)
      exact this
    have h1 : (S.Ahat - s • S.Ihat) *ᵥ col c = S.Ihat *ᵥ (pre c : ιZ ⊕ ιz → ℝ) := by
      rw [← hp, mulVec_mulVec, shift_mul_Nr S hs]
    rw [sub_mulVec, smul_mulVec] at h1
    change S.Ahat *ᵥ col c = S.Ihat *ᵥ ((pre c : ιZ ⊕ ιz → ℝ) + s • col c)
    rw [mulVec_add, mulVec_smul, ← h1]
    abel
  have hdefl : S.Ahat * Matrix.of (fun a c => col c a) =
      S.Ihat * Matrix.of (fun a c => col c a) * Ψ :=
    deflate_of_cols _ _ _ _ fun c => by rw [hsum c]; exact hcolA c
  have hind : LinearIndependent ℝ col :=
    (b.linearIndependent.comp e e.injective).map' U.subtype (Submodule.ker_subtype _)
  refine ⟨Matrix.of fun a c => col c a, Ψ, hdefl, hind, fun μ hμ => ?_⟩
  obtain ⟨z, hz0, hz⟩ := exists_eigvec hμ
  set Jc : Matrix (ιZ ⊕ ιz) κ ℂ := (Matrix.of fun a c => col c a).map Complex.ofReal with hJc
  set u := Jc *ᵥ z with hu
  have hcolC : LinearIndependent ℂ (fun c i => (col c i : ℂ)) := linearIndependent_ofReal hind
  have hJsum : u = ∑ c, z c • fun i => (col c i : ℂ) := by
    funext i
    simp [hu, hJc, mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hu0 : u ≠ 0 := by
    intro h0
    rw [hJsum] at h0
    exact hz0 (funext fun c => Fintype.linearIndependent_iff.mp hcolC z h0 c)
  have huW : u ∈ Wsub S sel s := by
    rw [hJsum]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hUle _ (hcolU c))
  have hAu : S.Ahat.map Complex.ofReal *ᵥ u = μ • (S.Ihat.map Complex.ofReal *ᵥ u) := by
    have hdc : S.Ahat.map Complex.ofReal * Jc = S.Ihat.map Complex.ofReal * Jc *
        Ψ.map Complex.ofReal := by
      rw [hJc, ← map_ofReal_mul, ← map_ofReal_mul, ← map_ofReal_mul, hdefl]
    rw [hu, mulVec_mulVec, hdc, ← mulVec_mulVec, hz, mulVec_smul, mulVec_mulVec]
  have hμs : μ ≠ s := by
    intro h
    apply det_shift_C S hs
    refine exists_mulVec_eq_zero_iff.mp ⟨u, hu0, ?_⟩
    rw [sub_mulVec, hAu, smul_mulVec, h, sub_self]
  have hN := eig_to_N S hs hμs hAu
  have hT := mem_Tset_of_eig S sel s hu0 huW (by rw [φN, Matrix.toLin'_apply]; exact hN)
  rw [Tset, Finset.mem_insert] at hT
  rcases hT with h | h
  · left
    have h' : μ - s = 0 - s := inv_injective h
    simpa using h'
  · right
    obtain ⟨μ', hμ', he⟩ := Finset.mem_image.mp h
    have : μ' = μ := sub_left_injective (inv_injective he)
    rw [← this]
    exact Multiset.mem_toFinset.mp hμ'

/-- Woodford (2003), Assumption 8.2 and App. G.1, (G.4) and fn 2 (**partial selections**): under
Assumption 8.2 with a conjugation-closed selection and a nonzero (1.15), a real deflating pair
exists — whether or not the selection takes whole root classes (`PencilRepeated.SelWhole` is not
needed). -/
theorem exists_realSelection_partial {S : LinearRESystem ιZ ιz} {β : ℝ}
    (h82 : Assumption82 S β) (hi : ConjClosed h82.sel) (hreg : S.pencilPoly ≠ 0) :
    Nonempty (RealSelection S h82.sel) := by
  have hsel : ∀ μ ∈ h82.sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0 := by
    intro μ hμ
    have := Multiset.mem_of_le h82.sel_le hμ
    rw [Multiset.mem_filter, Polynomial.mem_roots hreg] at this
    exact ⟨this.2.1, this.1⟩
  have hcnt : ∀ μ ∈ h82.sel, h82.sel.count μ ≤ S.pencilPoly.roots.count μ := fun μ _ =>
    (Multiset.count_le_of_le μ h82.sel_le).trans (Multiset.count_le_of_le μ
      (Multiset.filter_le _ _))
  obtain ⟨J, Ψ, hd, hind, heig⟩ := exists_deflating_cols_partial S (κ := ιZ) hi hsel hreg hcnt
    (by rw [add_comm]; exact h82.sel_card)
  exact ⟨⟨J, Ψ, hd, hind, heig⟩⟩

/-- Woodford (2003), App. G.1: the deflating pair chosen from Assumptions 8.2 (i) and 8.4 with
(1.15) nonzero, for a selection that may take only part of a root class. -/
noncomputable def splitOfPartial {ιτ : Type*} [Fintype ιτ] (P : LQProblem ιZ ιz ιτ)
    (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel) (hreg : P.sys.pencilPoly ≠ 0)
    (h84 : Assumption84 P.sys h82.sel) : DeflatingSplit P.sys P.β :=
  splitGen P.β_pos h82 (exists_realSelection_partial h82 hi hreg).some hreg h84

/-- Woodford (2003), **Proposition 8.1**, p. 553, **for any selection, including one that takes
only part of a repeated root**: under Assumption 8.2 (case (i)), Assumption 8.4 and a nonzero
(1.15) the corrected Proposition 8.1 holds for any expectation system. -/
theorem prop81_of_assumptions_partial {Ω ιτ : Type*} [Fintype ιτ] (P : LQProblem ιZ ιz ιτ)
    (h82 : Assumption82 P.sys P.β) (hi : ConjClosed h82.sel) (hreg : P.sys.pencilPoly ≠ 0)
    (h84 : Assumption84 P.sys h82.sel) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Nonempty (Prop81General.Prop81ConclusionM P 𝔼 t0) :=
  ⟨Prop81General.prop81 P (splitOfPartial P h82 hi hreg h84) 𝔼 t0⟩

/-- Woodford (2003), **Proposition 8.2**, p. 555, **for any selection, including one that takes
only part of a repeated root**: under Assumptions 8.1, 8.2 (case (i)), 8.4, 8.5 and a nonzero
(1.15), commitment to (1.23) is robustly optimal. -/
theorem prop82_of_assumptions_partial {Ω ιτ : Type*} [Fintype ιτ] {P : LQProblem ιZ ιz ιτ}
    {𝔼 : ExpectationSystem Ω} {t0 : ℕ} (hpull : 𝔼.PullOut)
    (hA : Prop82General.Assumption81M P 𝔼 t0) (h82 : Assumption82 P.sys P.β)
    (hi : ConjClosed h82.sel) (hreg : P.sys.pencilPoly ≠ 0) (h84 : Assumption84 P.sys h82.sel)
    (h85 : Assumption85 (Λmat P.sys P.β (splitOfPartial P h82 hi hreg h84).J) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0) (hDk : P.sys.Et.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ}
    {vh : ℕ → Ω → ℝ}
    (hhist : TargetCriterion.Prop82.HistoryOK
      (Λmat P.sys P.β (splitOfPartial P h82 hi hreg h84).J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := ιz) P 𝔼 t0
      (fun _ y => Prop82General.Prop82M.CriterionM
        (Prop81General.prop81 P (splitOfPartial P h82 hi hreg h84) 𝔼 t0) D qh vh y)
      (fun _ y t ω => zpart (y t ω)) :=
  Prop82General.prop82_of_split hpull hA _ h85.2 hD hDk hhist hMhb hMhk hqhb hvhb

/-! ### Non-uniqueness: a semisimple double root, one copy selected -/

/-- Woodford (2003), eq. (1.1), p. 537 (the illustration): `n_Z = n_z = 1`, `A = ½ I`, `Î = I`,
`B₂ = 1`; (1.15) has the double, semisimple root `½`. -/
noncomputable def rSys : LinearRESystem Unit Unit where
  A11 := Matrix.of fun _ _ => 1 / 2
  A12 := 0
  A21 := 0
  A22 := Matrix.of fun _ _ => 1 / 2
  Et := 1
  B2 := fun _ => 1
  A22_isUnit := by
    rw [Matrix.det_unique]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  B2_ne_zero := fun h => by simpa using congrFun h ()

/-- Woodford (2003), (1.1)–(1.4) (the illustration): `β = 1/2`, loss `½ i_t²`. -/
noncomputable def rProblem : LQProblem Unit Unit Unit where
  sys := rSys
  β := 1 / 2
  β_pos := by norm_num
  β_lt_one := by norm_num
  Ttil := 0
  Ti := fun _ => 1
  W := 1
  τstar := 0
  W_posDef := Matrix.PosDef.one

/-- Woodford (2003), eq. (1.15) (the illustration): `det(A − μÎ) = (μ − ½)²`. -/
theorem rSys_pencilPoly : rSys.pencilPoly = (X - C (1 / 2)) ^ 2 := by
  refine Polynomial.funext fun μ => ?_
  rw [pencilPoly_eval]
  have e : rSys.Ahat.map Complex.ofReal - μ • rSys.Ihat.map Complex.ofReal =
      fromBlocks (Matrix.of fun _ _ => (1 / 2 : ℂ) - μ) 0 0 (Matrix.of fun _ _ => 1 / 2 - μ) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [rSys, LinearRESystem.Ahat, LinearRESystem.Ihat]
  rw [e, det_fromBlocks_zero₂₁]
  simp [Matrix.det_unique]
  ring

/-- Woodford (2003), (1.15) (the illustration): the roots are `{½, ½}`; `A` is invertible. -/
theorem rSys_roots : rSys.pencilPoly.roots = {1 / 2, 1 / 2} ∧ rSys.Ahat.rank = 2 := by
  refine ⟨?_, ?_⟩
  · rw [rSys_pencilPoly, roots_pow, roots_X_sub_C]
    rfl
  · have h : IsUnit rSys.Ahat.det := by
      change IsUnit (fromBlocks (Matrix.of fun _ _ => (1 / 2 : ℝ)) 0 0
        (Matrix.of fun _ _ => (1 / 2 : ℝ)) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ).det
      rw [det_fromBlocks_zero₂₁]
      exact isUnit_iff_ne_zero.mpr (by simp [Matrix.det_unique])
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr h)]
    simp

/-- Woodford (2003), Assumption 8.2 (i) (the illustration, `β = 1/2`): the selection `{½}` takes ONE
copy of the double root `½` (both copies lie in `|μ| < β⁻¹ = 2`). -/
noncomputable def r82 : Assumption82 rSys (1 / 2) where
  count := by
    unfold LinearRESystem.Assumption82Count LinearRESystem.stableCount
    rw [rSys_roots.1, rSys_roots.2]
    norm_num [Multiset.filter_cons]
  sel := {1 / 2}
  sel_le := by
    rw [rSys_roots.1]
    norm_num [Multiset.filter_cons]
  sel_card := by
    rw [rSys_roots.2]
    simp
  cases := by
    left
    unfold ConjClosed
    simp [map_ofNat]

/-- Woodford (2003), Assumption 8.2: **the selection does not take the whole root class** —
`½` is selected once but is a double root. -/
theorem r_not_selWhole : ¬ SelWhole rSys r82.sel := by
  intro h
  have := h (1 / 2) (Multiset.mem_singleton_self _)
  change Multiset.count (1 / 2 : ℂ) {1 / 2} = _ at this
  rw [rSys_roots.1] at this
  simp at this

/-- Woodford (2003), App. G.1 (the illustration): the line spanned by `(1, a)` is invariant (every
vector is an eigenvector of `A = ½ I`); `J = (1, a)'`, `Ψ = ½`. -/
noncomputable def rJ (a : ℝ) : Matrix (Unit ⊕ Unit) Unit ℝ := Matrix.of fun r _ => Sum.elim
  (fun _ => 1) (fun _ => a) r

/-- Woodford (2003), App. G.1 (the illustration): `Ψ = ½`. -/
noncomputable def rΨ : Matrix Unit Unit ℝ := Matrix.of fun _ _ => 1 / 2

/-- Woodford (2003), App. G.1, (G.4) (the illustration): `A J = Î J Ψ` for every `a`. -/
theorem r_deflate (a : ℝ) : rSys.Ahat * rJ a = rSys.Ihat * rJ a * rΨ := by
  ext r c
  rcases r with r | r <;>
    simp [Matrix.mul_apply, rSys, rJ, rΨ, LinearRESystem.Ahat, LinearRESystem.Ihat,
      Fintype.sum_sum_type, mul_comm]

/-- Woodford (2003), App. G.1 (the illustration): `Ψ = ½` has the single eigenvalue `½`. -/
theorem r_eig {μ : ℂ} (h : (Matrix.scalar Unit μ - rΨ.map Complex.ofReal).det = 0) :
    μ = 1 / 2 := by
  rw [Matrix.det_unique] at h
  simp [rΨ, Matrix.scalar_apply] at h
  linear_combination h

/-- Woodford (2003), App. G.1, (G.4) (the illustration): for every `a`, `(1, a)` with `Ψ = ½` is
a real selection for `{½}`. -/
noncomputable def rSel (a : ℝ) : RealSelection rSys r82.sel where
  J := rJ a
  Ψ := rΨ
  deflate := r_deflate a
  indep := by
    refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
    have := congrFun hg (Sum.inl ())
    simpa [rJ] using this
  eig := fun μ h => Or.inr (by rw [r_eig h]; exact Multiset.mem_singleton_self _)

/-- Woodford (2003), App. G.1 (the illustration): for every `a`, `J = (1, a)'` gives a deflating
split (`J₁ = 1`, `K = ½`, the eigenvalue `½ < β⁻¹`). -/
noncomputable def rSplit (a : ℝ) : DeflatingSplit rSys (1 / 2) where
  J := rJ a
  Ψ := rΨ
  deflate := r_deflate a
  eig_lt := fun μ h => by
    rw [r_eig h]
    norm_num
  J1_det := by
    rw [Matrix.det_unique]
    simp [J1, rJ]
  K_det := by
    rw [Matrix.det_unique]
    simp [Kmat, rSys]

/-- Woodford (2003), (1.21) (the illustration): `Υ = −(J₁')⁻¹ J₂' Ẽ' = −a`. -/
theorem r_Υ (a : ℝ) : Υmat rSys (rJ a) = Matrix.of fun _ _ => -a := by
  ext i j
  simp [Υmat, J1, J2, rJ, rSys]

/-- **Woodford (2003), Proposition 8.1 and App. G.1 with a partially selected repeated root
(non-uniqueness)**: for `rProblem` the selection `{½}` takes one copy of the semisimple double
root `½` (`¬ SelWhole`), and the invariant lines spanned by `(1, 0)` and `(1, 1)` both give real
selections and deflating splits; the resulting representations of the corrected Proposition 8.1
(any expectation system) have different `Υ` (`0` and `−1`). So with a partial selection the
existence of the representation survives (`prop81_of_assumptions_partial`), but `Υ` (and with it
`R(L⁻¹)` and the target criterion) is not determined by the selection. -/
theorem partial_nonunique {Ω : Type*} (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    ¬ SelWhole rSys r82.sel ∧ (rSel 0).J ≠ (rSel 1).J ∧
      (Prop81General.prop81 rProblem (rSplit 0) 𝔼 t0).Υ ≠
        (Prop81General.prop81 rProblem (rSplit 1) 𝔼 t0).Υ := by
  refine ⟨r_not_selWhole, fun h => ?_, ?_⟩
  · have := congrFun (congrFun h (Sum.inr ())) ()
    simp [rSel, rJ] at this
  · change Υmat rSys (rJ 0) ≠ Υmat rSys (rJ 1)
    rw [r_Υ, r_Υ]
    intro h
    have := congrFun (congrFun h ()) ()
    simp at this

end Woodford.OptimalPolicyRules.TidyR5bPartialSel
