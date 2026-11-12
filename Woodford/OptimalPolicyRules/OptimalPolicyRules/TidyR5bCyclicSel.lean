/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.TidyR5bPartialSel
import OptimalPolicyRules.InertiaSplit

/-!
# Partial selections: the selected subspace is unique iff the partial blocks are cyclic

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.2 (p. 552), Appendix G.1
(pp. 716–718), Propositions 8.1 and 8.2.

The module TidyR5bPartialSel shows that a selection taking only part of a repeated root still
gives a deflating pair, and (`TidyR5bPartialSel.partial_nonunique`) that the resulting `Υ` can
then depend on a choice. This module gives the exact criterion.

## Linear algebra (`g` nilpotent on an invariant `X`)

* `unique_of_cyclic`: if `dim (X ∩ ker g) ≤ 1` (one Jordan chain), every `g`-invariant `U ≤ X`
  of dimension `k` equals `X ∩ ker gᵏ`.
* `two_of_not_cyclic`: if `dim (X ∩ ker g) ≥ 2` and `0 < k < dim X`, there are two different
  `g`-invariant `k`-dimensional subspaces of `X`.
* `block_unique_iff`: so for `0 < k < dim X` the invariant `k`-dimensional subspace of `X` is
  unique **iff** `dim (X ∩ ker g) ≤ 1`.

## The selected subspace

A selected subspace (`SelSpace`) is `⊕_ν B_ν` over the eigenvalues `ν` of
`N = (A − sÎ)⁻¹Î` used by the selection (`PencilRepeated.Tset`): `B_{ν₀} = ker A`, and for
`ν = (μ − s)⁻¹` an `N`-invariant subspace of the generalised eigenspace of dimension
`sel.count μ` (`AdmBlocks`). `TidyR5bPartialSel.Wp` is one (`selSpace_Wp`).

* `selSpace_unique_iff`: the selected subspace is unique **iff** every partially selected
  eigenvalue (`0 < count < multiplicity`) has geometric multiplicity `≤ 1` (`CyclicPartial`).
* `selSpace_conj_unique_iff`: the same among conjugation-closed selected subspaces (the
  complexifications of the real ones that a real `J` spans).
* `Υ_eq_iff_mul`: `Υ` (eq. (1.21)) is a function of the column space of `J`
  (`InertiaSplit.Υmat_mul`), and when `Ẽ` is invertible the column space is a function of `Υ`.
-/

namespace Woodford.OptimalPolicyRules.TidyR5bCyclicSel

open Matrix Polynomial GeneralSetup PencilSplit PencilEigen PencilAssumptions PencilRepeated
  GeneralFOC.Selection TidyR5bPartialSel

/-! ### Linear algebra: invariant subspaces of a nilpotent block -/

/-- Woodford (2003), App. G.1 (linear algebra): extension — if `g` maps `X` into itself and is
nilpotent on `X`, every `g`-invariant `Z ≤ X` lies in a `g`-invariant `W ≤ X` of every
dimension between `dim Z` and `dim X`. -/
theorem exists_ext {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : V →ₗ[K] V) (X : Submodule K V)
    (hX : ∀ x ∈ X, g x ∈ X) (hnil : ∀ x ∈ X, ∃ n : ℕ, (g ^ n) x = 0) (Z : Submodule K V)
    (hZX : Z ≤ X) (hZ : ∀ x ∈ Z, g x ∈ Z) :
    ∀ d, Module.finrank K Z + d ≤ Module.finrank K X → ∃ W : Submodule K V, Z ≤ W ∧ W ≤ X ∧
      (∀ x ∈ W, g x ∈ W) ∧ Module.finrank K W = Module.finrank K Z + d := by
  classical
  intro d
  induction d with
  | zero =>
    intro _
    exact ⟨Z, le_rfl, hZX, hZ, rfl⟩
  | succ d ih =>
    intro hd
    obtain ⟨U, hZU, hUX, hUf, hUk⟩ := ih (by omega)
    have hgnX : ∀ n, ∀ x ∈ X, (g ^ n) x ∈ X := fun n x hx =>
      Module.End.pow_apply_mem_of_forall_mem n hX x hx
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
    refine ⟨U ⊔ K ∙ x, hZU.trans le_sup_left,
      sup_le hUX ((Submodule.span_singleton_le_iff_mem _ _).mpr hxX), fun v hv => ?_, ?_⟩
    · obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_add, map_smul]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hUf u hu))
        (Submodule.mem_sup_left (U.smul_mem _ hgx))
    · rw [Submodule.finrank_sup_span_singleton hxU, hUk]
      omega

/-- Woodford (2003), App. G.1 (linear algebra, rank–nullity on a subspace):
`dim g(Y) + dim (Y ∩ ker g) = dim Y`. -/
theorem finrank_map_add_inf_ker {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ[K] V) (Y : Submodule K V) :
    Module.finrank K (Y.map h) + Module.finrank K (Y ⊓ LinearMap.ker h : Submodule K V) =
      Module.finrank K Y := by
  have := (h.domRestrict Y).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq Y ((LinearMap.ker h).comap Y.subtype),
    Submodule.map_comap_subtype] at this
  exact this

/-- Woodford (2003), App. G.1 (linear algebra): if `g` is nilpotent on a `g`-invariant `Y`, then
`g^{dim Y}` kills `Y`. -/
theorem pow_finrank_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : V →ₗ[K] V) (Y : Submodule K V) (hY : ∀ y ∈ Y, g y ∈ Y)
    (hnil : ∀ y ∈ Y, ∃ n : ℕ, (g ^ n) y = 0) :
    ∀ y ∈ Y, (g ^ Module.finrank K Y) y = 0 := by
  intro y hy
  obtain ⟨n, hn⟩ := hnil y hy
  have hmem : (⟨y, hy⟩ : Y) ∈ LinearMap.ker ((g.restrict hY) ^ n) := by
    rw [LinearMap.mem_ker, Module.End.pow_restrict]
    exact Subtype.ext (by simp [LinearMap.restrict_apply, hn])
  have h2 := Module.End.ker_pow_le_ker_pow_finrank (g.restrict hY) n hmem
  rw [LinearMap.mem_ker, Module.End.pow_restrict] at h2
  have := congrArg Subtype.val h2
  simpa [LinearMap.restrict_apply] using this

/-- Woodford (2003), App. G.1 (linear algebra): the kernel chain grows by at most
`dim (X ∩ ker g)` per step: `dim (X ∩ ker g^{j+1}) ≤ dim (X ∩ ker gʲ) + dim (X ∩ ker g)`. -/
theorem finrank_ker_succ_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : V →ₗ[K] V) (X : Submodule K V) (hX : ∀ x ∈ X, g x ∈ X)
    (j : ℕ) :
    Module.finrank K (X ⊓ LinearMap.ker (g ^ (j + 1)) : Submodule K V) ≤
      Module.finrank K (X ⊓ LinearMap.ker (g ^ j) : Submodule K V) +
        Module.finrank K (X ⊓ LinearMap.ker g : Submodule K V) := by
  set Y : Submodule K V := X ⊓ LinearMap.ker (g ^ (j + 1)) with hY
  have h := finrank_map_add_inf_ker (g ^ j) Y
  have h1 : Y.map (g ^ j) ≤ X ⊓ LinearMap.ker g := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyX, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨Module.End.pow_apply_mem_of_forall_mem j hX y hyX, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, ← pow_succ']
    exact hyk
  have h2 : Y ⊓ LinearMap.ker (g ^ j) ≤ X ⊓ LinearMap.ker (g ^ j) :=
    inf_le_inf_right _ inf_le_left
  have := Submodule.finrank_mono h1
  have := Submodule.finrank_mono h2
  omega

/-- Woodford (2003), App. G.1 (linear algebra): with one Jordan chain (`dim (X ∩ ker g) ≤ 1`),
`dim (X ∩ ker gʲ) ≤ j`. -/
theorem finrank_ker_pow_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : V →ₗ[K] V) (X : Submodule K V) (hX : ∀ x ∈ X, g x ∈ X)
    (h1 : Module.finrank K (X ⊓ LinearMap.ker g : Submodule K V) ≤ 1) (j : ℕ) :
    Module.finrank K (X ⊓ LinearMap.ker (g ^ j) : Submodule K V) ≤ j := by
  induction j with
  | zero =>
    have : X ⊓ LinearMap.ker (g ^ 0) = ⊥ := by
      rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id, inf_bot_eq]
    rw [this, finrank_bot]
  | succ j ih =>
    have := finrank_ker_succ_le g X hX j
    omega

/-- Woodford (2003), App. G.1 (**one Jordan chain ⇒ uniqueness**): if `dim (X ∩ ker g) ≤ 1`,
every `g`-invariant `k`-dimensional `U ≤ X` is `X ∩ ker gᵏ`. -/
theorem unique_of_cyclic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : V →ₗ[K] V) (X : Submodule K V) (hX : ∀ x ∈ X, g x ∈ X)
    (hnil : ∀ x ∈ X, ∃ n : ℕ, (g ^ n) x = 0)
    (h1 : Module.finrank K (X ⊓ LinearMap.ker g : Submodule K V) ≤ 1) {k : ℕ}
    {U : Submodule K V} (hUX : U ≤ X) (hU : ∀ x ∈ U, g x ∈ U) (hUk : Module.finrank K U = k) :
    U = X ⊓ LinearMap.ker (g ^ k) := by
  have hle : U ≤ X ⊓ LinearMap.ker (g ^ k) := by
    intro y hy
    refine Submodule.mem_inf.mpr ⟨hUX hy, ?_⟩
    rw [LinearMap.mem_ker, ← hUk]
    exact pow_finrank_eq_zero g U hU (fun y hy => hnil y (hUX hy)) y hy
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [hUk]; exact finrank_ker_pow_le g X hX h1 k)

/-- Woodford (2003), App. G.1 (**two Jordan chains ⇒ non-uniqueness**): if
`dim (X ∩ ker g) ≥ 2` and `0 < k < dim X`, there are two different `g`-invariant
`k`-dimensional subspaces of `X`. -/
theorem two_of_not_cyclic {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : V →ₗ[K] V) (X : Submodule K V) (hX : ∀ x ∈ X, g x ∈ X)
    (hnil : ∀ x ∈ X, ∃ n : ℕ, (g ^ n) x = 0)
    (h2 : 2 ≤ Module.finrank K (X ⊓ LinearMap.ker g : Submodule K V)) {k : ℕ} (hk0 : 0 < k)
    (hkX : k < Module.finrank K X) :
    ∃ U₁ U₂ : Submodule K V, U₁ ≤ X ∧ (∀ x ∈ U₁, g x ∈ U₁) ∧ Module.finrank K U₁ = k ∧
      U₂ ≤ X ∧ (∀ x ∈ U₂, g x ∈ U₂) ∧ Module.finrank K U₂ = k ∧ U₁ ≠ U₂ := by
  set L : Submodule K V := X ⊓ LinearMap.ker g with hL
  have hLg : ∀ x ∈ L, g x ∈ L := fun x hx => by
    have := (Submodule.mem_inf.mp hx).2
    rw [LinearMap.mem_ker] at this
    rw [this]
    exact L.zero_mem
  have hLnil : ∀ x ∈ L, ∃ n : ℕ, (g ^ n) x = 0 := fun x hx =>
    ⟨1, by rw [pow_one]; exact (Submodule.mem_inf.mp hx).2⟩
  obtain ⟨L2, -, hL2L, hL2g, hL2d⟩ := exists_ext g L hLg hLnil ⊥ bot_le
    (fun x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]) 2
    (by rw [finrank_bot]; omega)
  rw [finrank_bot, zero_add] at hL2d
  obtain ⟨W, hL2W, hWX, hWg, hWd⟩ := exists_ext g X hX hnil L2 (hL2L.trans inf_le_left) hL2g
    (k - 1) (by omega)
  rw [hL2d, show 2 + (k - 1) = k + 1 by omega] at hWd
  have hWnil : ∀ x ∈ W, ∃ n : ℕ, (g ^ n) x = 0 := fun x hx => hnil x (hWX hx)
  set R : Submodule K V := W.map g with hR
  have hRW : R ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact hWg w hw
  have hRg : ∀ x ∈ R, g x ∈ R := fun x hx => Submodule.mem_map_of_mem (hRW hx)
  have hRd : Module.finrank K R + 1 ≤ k := by
    have h : Module.finrank K R + Module.finrank K (W ⊓ LinearMap.ker g : Submodule K V) =
        Module.finrank K W := finrank_map_add_inf_ker g W
    have h' : L2 ≤ W ⊓ LinearMap.ker g :=
      le_inf hL2W (hL2L.trans inf_le_right)
    have := Submodule.finrank_mono h'
    rw [hL2d] at this
    omega
  obtain ⟨T, hRT, hTW, -, hTd⟩ := exists_ext g W hWg hWnil R hRW hRg
    (k - 1 - Module.finrank K R) (by omega)
  rw [show Module.finrank K R + (k - 1 - Module.finrank K R) = k - 1 by omega] at hTd
  have hTlt : T < W := lt_of_le_of_ne hTW fun h => by rw [h] at hTd; omega
  obtain ⟨y1, hy1W, hy1T⟩ := SetLike.exists_of_lt hTlt
  set T1 : Submodule K V := T ⊔ K ∙ y1 with hT1
  have hT1d : Module.finrank K T1 = k := by
    rw [hT1, Submodule.finrank_sup_span_singleton hy1T, hTd]
    omega
  have hT1W : T1 ≤ W := sup_le hTW ((Submodule.span_singleton_le_iff_mem _ _).mpr hy1W)
  have hT1lt : T1 < W := lt_of_le_of_ne hT1W fun h => by rw [h] at hT1d; omega
  obtain ⟨y2, hy2W, hy2T1⟩ := SetLike.exists_of_lt hT1lt
  have hy2T : y2 ∉ T := fun h => hy2T1 (Submodule.mem_sup_left h)
  set T2 : Submodule K V := T ⊔ K ∙ y2 with hT2
  have hT2d : Module.finrank K T2 = k := by
    rw [hT2, Submodule.finrank_sup_span_singleton hy2T, hTd]
    omega
  have hT2W : T2 ≤ W := sup_le hTW ((Submodule.span_singleton_le_iff_mem _ _).mpr hy2W)
  have hinv : ∀ T' : Submodule K V, T ≤ T' → T' ≤ W → ∀ x ∈ T', g x ∈ T' := fun T' h1 h2 x hx =>
    h1 (hRT (Submodule.mem_map_of_mem (h2 hx)))
  refine ⟨T1, T2, hT1W.trans hWX, hinv T1 le_sup_left hT1W, hT1d, hT2W.trans hWX,
    hinv T2 le_sup_left hT2W, hT2d, fun h => hy2T1 ?_⟩
  rw [h]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y2)

/-- Woodford (2003), App. G.1 (**the block criterion**): for `0 < k < dim X`, the `g`-invariant
`k`-dimensional subspace of `X` (with `g` nilpotent on `X`) is unique iff
`dim (X ∩ ker g) ≤ 1`, i.e. iff `g` has a single Jordan chain on `X`. -/
theorem block_unique_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : V →ₗ[K] V) (X : Submodule K V) (hX : ∀ x ∈ X, g x ∈ X)
    (hnil : ∀ x ∈ X, ∃ n : ℕ, (g ^ n) x = 0) {k : ℕ} (hk0 : 0 < k)
    (hkX : k < Module.finrank K X) :
    (∀ U₁ U₂ : Submodule K V, U₁ ≤ X → (∀ x ∈ U₁, g x ∈ U₁) → Module.finrank K U₁ = k →
      U₂ ≤ X → (∀ x ∈ U₂, g x ∈ U₂) → Module.finrank K U₂ = k → U₁ = U₂) ↔
      Module.finrank K (X ⊓ LinearMap.ker g : Submodule K V) ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨U₁, U₂, a1, a2, a3, b1, b2, b3, hne⟩ :=
      two_of_not_cyclic g X hX hnil (by omega) hk0 hkX
    exact hne (h U₁ U₂ a1 a2 a3 b1 b2 b3)
  · intro h1 U₁ U₂ a1 a2 a3 b1 b2 b3
    rw [unique_of_cyclic g X hX hnil h1 a1 a2 a3, unique_of_cyclic g X hX hnil h1 b1 b2 b3]

/-- Woodford (2003), App. G.1 (linear algebra): a subspace is `f`-invariant iff it is
`(f − ν)`-invariant. -/
theorem inv_sub_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (f : V →ₗ[K] V)
    (ν : K) (U : Submodule K V) :
    (∀ x ∈ U, f x ∈ U) ↔ ∀ x ∈ U, (f - ν • (1 : V →ₗ[K] V)) x ∈ U := by
  constructor
  · intro h x hx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact U.sub_mem (h x hx) (U.smul_mem ν hx)
  · intro h x hx
    have := U.add_mem (h x hx) (U.smul_mem ν hx)
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_add_cancel] at this

/-- Woodford (2003), App. G.1 (linear algebra): inside the generalised eigenspace,
`ker (f − ν)` is the eigenspace, so `dim (X ∩ ker g)` is the geometric multiplicity. -/
theorem maxGen_inf_ker {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (ν : K) :
    Module.End.maxGenEigenspace f ν ⊓ LinearMap.ker (f - ν • (1 : Module.End K V)) =
      Module.End.eigenspace f ν := by
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
  rw [Module.End.mem_eigenspace_iff]
  exact ⟨fun h => h.2, fun h =>
    ⟨Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr h), h⟩⟩

/-! ### Selected subspaces -/

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-- Woodford (2003), App. G.1, (G.4): `U` is an admissible block for the eigenvalue `ν` of `N`:
an `N`-invariant subspace of the generalised eigenspace with dimension the number of selected
copies of the root `μ = s + ν⁻¹`. -/
def BlockOK (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) (ν : ℂ)
    (U : Submodule ℂ (ιZ ⊕ ιz → ℂ)) : Prop :=
  U ≤ Wfam S s ν ∧ (∀ w ∈ U, φN S s w ∈ U) ∧ Module.finrank ℂ U = kc sel s ν

/-- Woodford (2003), App. G.1, (G.4): a family of admissible blocks: `ker A` for `ν₀`, and an
admissible block (`BlockOK`) for every other eigenvalue used by the selection. -/
def AdmBlocks (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ)
    (B : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ)) : Prop :=
  B (ν0 s) = Wfam S s (ν0 s) ∧ ∀ ν ∈ Tset sel s, ν ≠ ν0 s → BlockOK S sel s ν (B ν)

/-- Woodford (2003), App. G.1, (G.4) (**a selected subspace**): `⊕_ν B_ν` for an admissible
family of blocks. -/
def SelSpace (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ)
    (W : Submodule ℂ (ιZ ⊕ ιz → ℂ)) : Prop :=
  ∃ B, AdmBlocks S sel s B ∧ W = (Tset sel s).sup B

/-- Woodford (2003), Assumption 8.2 (**the cyclic condition**): every partially selected
eigenvalue `ν` (`0 < kc ν < dim` of its generalised eigenspace) has geometric multiplicity
`≤ 1` (a single Jordan chain). -/
def CyclicPartial (S : LinearRESystem ιZ ιz) (sel : Multiset ℂ) (s : ℝ) : Prop :=
  ∀ ν ∈ Tset sel s, ν ≠ ν0 s → 0 < kc sel s ν → kc sel s ν < Module.finrank ℂ (Wfam S s ν) →
    Module.finrank ℂ ((φN S s).eigenspace ν) ≤ 1

/-- Woodford (2003), App. G.1: the blocks of `TidyR5bPartialSel.Wp` are admissible. -/
theorem Ublk_ok (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} (hc : ConjClosed sel)
    {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ) :
    ∀ ν ∈ Tset sel s, ν ≠ ν0 s → BlockOK S sel s ν (Ublk S sel s ν) := by
  intro ν hν h0
  refine ⟨Ublk_le_Wfam S sel s ν, Ublk_inv S sel s ν, ?_⟩
  rw [Tset, Finset.mem_insert] at hν
  rcases hν with h | h
  · exact absurd h h0
  obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp h
  rw [finrank_Ublk S hc hs hsel hcnt (Multiset.mem_toFinset.mp hμ)]
  simp [kc]

/-- Woodford (2003), App. G.1: `TidyR5bPartialSel.Wp` is a selected subspace. -/
theorem selSpace_Wp (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} (hc : ConjClosed sel)
    {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ) :
    SelSpace S sel s (Wp S sel s) :=
  ⟨Ublk S sel s, ⟨by rw [Ublk_ν0, Wfam_ν0], Ublk_ok S hc hs hsel hcnt⟩, rfl⟩

/-- Woodford (2003), App. G.1: a selected subspace meets the generalised eigenspace of a used
`ν` exactly in its block (the generalised eigenspaces are independent). -/
theorem sup_inf_Wfam (S : LinearRESystem ιZ ιz) {T : Finset ℂ} {s : ℝ}
    {B : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ)} (hB : ∀ μ ∈ T, B μ ≤ Wfam S s μ) {ν : ℂ}
    (hν : ν ∈ T) : T.sup B ⊓ Wfam S s ν = B ν := by
  classical
  rw [← Finset.insert_erase hν, Finset.sup_insert, sup_inf_assoc_of_le _ (hB ν hν)]
  have hR : (T.erase ν).sup B ≤ ⨆ j, ⨆ (_ : j ≠ ν), Wfam S s j :=
    Finset.sup_le fun μ hμ => (hB μ (Finset.mem_of_mem_erase hμ)).trans
      (le_iSup₂_of_le μ (Finset.ne_of_mem_erase hμ) le_rfl)
  have hd : Disjoint ((T.erase ν).sup B) (Wfam S s ν) := ((Wfam_indep S s ν).symm).mono_left hR
  rw [disjoint_iff.mp hd, sup_bot_eq]

/-- Woodford (2003), App. G.1: two admissible families whose blocks differ at a used `ν` give
different selected subspaces. -/
theorem sup_ne_of_block_ne (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ}
    {B₁ B₂ : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ)} (h₁ : AdmBlocks S sel s B₁)
    (h₂ : AdmBlocks S sel s B₂) {ν : ℂ} (hν : ν ∈ Tset sel s) (hne : B₁ ν ≠ B₂ ν) :
    (Tset sel s).sup B₁ ≠ (Tset sel s).sup B₂ := by
  have hle : ∀ B : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ), AdmBlocks S sel s B →
      ∀ μ ∈ Tset sel s, B μ ≤ Wfam S s μ := fun B hB μ hμ => by
    by_cases h0 : μ = ν0 s
    · rw [h0, hB.1]
    · exact (hB.2 μ hμ h0).1
  intro h
  apply hne
  rw [← sup_inf_Wfam S (hle B₁ h₁) hν, ← sup_inf_Wfam S (hle B₂ h₂) hν, h]

/-- Woodford (2003), App. G.1 (**cyclic ⇒ the blocks are forced**): under `CyclicPartial`, any
two admissible families have the same blocks. -/
theorem blocks_eq (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ}
    (hcyc : CyclicPartial S sel s) {B B' : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ)}
    (hB : AdmBlocks S sel s B) (hB' : AdmBlocks S sel s B') :
    ∀ ν ∈ Tset sel s, B ν = B' ν := by
  intro ν hν
  by_cases h0 : ν = ν0 s
  · rw [h0, hB.1, hB'.1]
  obtain ⟨a1, a2, a3⟩ := hB.2 ν hν h0
  obtain ⟨b1, b2, b3⟩ := hB'.2 ν hν h0
  rcases Nat.eq_zero_or_pos (kc sel s ν) with hk | hk
  · rw [hk] at a3 b3
    rw [Submodule.finrank_eq_zero.mp a3, Submodule.finrank_eq_zero.mp b3]
  have hle : kc sel s ν ≤ Module.finrank ℂ (Wfam S s ν) := a3 ▸ Submodule.finrank_mono a1
  rcases hle.lt_or_eq with hlt | heq
  · have h1 := hcyc ν hν h0 hk hlt
    rw [← maxGen_inf_ker] at h1
    rw [Wfam_ne S s h0] at a1 b1
    have hX := (inv_sub_iff _ ν _).mp (maxGen_mapsTo S s ν)
    rw [unique_of_cyclic _ _ hX (maxGen_nil S s ν) h1 a1 ((inv_sub_iff _ ν _).mp a2) a3,
      unique_of_cyclic _ _ hX (maxGen_nil S s ν) h1 b1 ((inv_sub_iff _ ν _).mp b2) b3]
  · rw [Submodule.eq_of_le_of_finrank_le a1 (by rw [a3]; exact heq.ge),
      Submodule.eq_of_le_of_finrank_le b1 (by rw [b3]; exact heq.ge)]

/-- Woodford (2003), App. G.1 (**cyclic ⇒ unique**): under `CyclicPartial` there is at most one
selected subspace. -/
theorem selSpace_unique_of_cyclic (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} {s : ℝ}
    (hcyc : CyclicPartial S sel s) {W W' : Submodule ℂ (ιZ ⊕ ιz → ℂ)}
    (hW : SelSpace S sel s W) (hW' : SelSpace S sel s W') : W = W' := by
  obtain ⟨B, hB, rfl⟩ := hW
  obtain ⟨B', hB', rfl⟩ := hW'
  exact Finset.sup_congr rfl (blocks_eq S hcyc hB hB')

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1, p. 716: a sum of blocks that conjugation maps into each other is
closed under conjugation. -/
theorem conjStable_sup {sel : Multiset ℂ} (hc : ConjClosed sel)
    {s : ℝ} {B : ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ)}
    (hB : ∀ μ ∈ Tset sel s, ∀ w ∈ B μ, (fun i => starRingEnd ℂ (w i)) ∈ B (starRingEnd ℂ μ)) :
    ConjStable ((Tset sel s).sup B) := by
  intro w hw
  have hle : (Tset sel s).sup B ≤ conjPre ((Tset sel s).sup B) := by
    refine Finset.sup_le fun ν hν v hv => ?_
    change (fun i => starRingEnd ℂ (v i)) ∈ (Tset sel s).sup B
    exact (Finset.le_sup (f := B) (Tset_conj hc s hν)) (hB ν hν v hv)
  exact hle hw

/-- Woodford (2003), App. G.1, fn 2: the real part of a complexification is the subspace itself. -/
theorem realPart_cplx {κ : Type*} [Finite κ] (U : Submodule ℝ (κ → ℝ)) :
    realPart (cplx U) = U := by
  refine (Submodule.eq_of_le_of_finrank_le (fun v hv => ofReal_mem_cplx hv) ?_).symm
  rw [finrank_realPart _ (cplx_conjStable U), finrank_cplx]

/-- Woodford (2003), App. G.1 (**not cyclic ⇒ two conjugation-closed selected subspaces**): if
some partially selected eigenvalue has geometric multiplicity `≥ 2`, there are two different
conjugation-closed selected subspaces. For a real eigenvalue the two blocks are complexified real
invariant subspaces; for a complex one they come with their conjugates. -/
theorem exists_two_of_not_cyclic (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ}
    (hc : ConjClosed sel) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ)
    (hnc : ¬ CyclicPartial S sel s) :
    ∃ W W' : Submodule ℂ (ιZ ⊕ ιz → ℂ), SelSpace S sel s W ∧ ConjStable W ∧
      SelSpace S sel s W' ∧ ConjStable W' ∧ W ≠ W' := by
  classical
  unfold CyclicPartial at hnc
  push Not at hnc
  obtain ⟨ν, hν, h0, hk, hlt, h2⟩ := hnc
  have hok := Ublk_ok S hc hs hsel hcnt
  have hν0r : starRingEnd ℂ (ν0 s) = ν0 s := by rw [ν0_eq, Complex.conj_ofReal]
  -- an admissible family that agrees with `Ublk` off `ν`
  have adm1 : ∀ U, BlockOK S sel s ν U →
      AdmBlocks S sel s (Function.update (Ublk S sel s) ν U) := fun U hU =>
    ⟨by rw [Function.update_of_ne (Ne.symm h0), Ublk_ν0, Wfam_ν0], fun μ hμ hμ0 => by
      by_cases hμν : μ = ν
      · subst hμν
        rw [Function.update_self]
        exact hU
      · rw [Function.update_of_ne hμν]
        exact hok μ hμ hμ0⟩
  by_cases hre : ν.im = 0
  · -- a real eigenvalue: complexified real blocks
    set r : ℝ := ν.re with hr
    have hνr : (r : ℂ) = ν := Complex.ext (by simp [hr]) (by simp [hre])
    have hcν : starRingEnd ℂ ν = ν := by rw [← hνr, Complex.conj_ofReal]
    set XR := realPart ((φN S s).maxGenEigenspace (r : ℂ)) with hXR
    set gR := (Nr S s).mulVecLin - r • (1 : Module.End ℝ (ιZ ⊕ ιz → ℝ)) with hgR
    have hXg : ∀ v ∈ XR, gR v ∈ XR := (inv_sub_iff _ r _).mp (realMaxGen_mapsTo S s r)
    have hdimX : Module.finrank ℝ XR = Module.finrank ℂ (Wfam S s ν) := by
      rw [hXR, finrank_realMaxGen, hνr, Wfam_ne S s h0]
    have hE : realPart ((φN S s).eigenspace (r : ℂ)) ≤ XR ⊓ LinearMap.ker gR := by
      intro v hv
      refine Submodule.mem_inf.mpr ⟨Module.End.eigenspace_le_maxGenEigenspace hv, ?_⟩
      change (fun i => (v i : ℂ)) ∈ (φN S s).eigenspace (r : ℂ) at hv
      rw [Module.End.mem_eigenspace_iff, φN, Matrix.toLin'_apply, map_mulVec_ofReal] at hv
      rw [LinearMap.mem_ker, hgR, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, Matrix.mulVecLin_apply, sub_eq_zero]
      funext i
      have := congrFun hv i
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      exact_mod_cast this
    have hEd : Module.finrank ℝ (realPart ((φN S s).eigenspace (r : ℂ))) =
        Module.finrank ℂ ((φN S s).eigenspace ν) := by
      have hcs : ConjStable ((φN S s).eigenspace (r : ℂ)) := fun w hw =>
        conj_mem_eigenspace (Nr S s) r hw
      rw [finrank_realPart _ hcs, hνr]
    have hd2 : 2 ≤ Module.finrank ℝ (XR ⊓ LinearMap.ker gR : Submodule ℝ _) := by
      have := Submodule.finrank_mono hE
      omega
    obtain ⟨U₁, U₂, a1, a2, a3, b1, b2, b3, hne⟩ :=
      two_of_not_cyclic gR XR hXg (realMaxGen_nil S s r) hd2 hk (by rw [hdimX]; exact hlt)
    have okC : ∀ U : Submodule ℝ (ιZ ⊕ ιz → ℝ), U ≤ XR → (∀ x ∈ U, gR x ∈ U) →
        Module.finrank ℝ U = kc sel s ν → BlockOK S sel s ν (cplx U) := by
      intro U hUX hUg hUk
      refine ⟨?_, fun w hw => ?_, by rw [finrank_cplx, hUk]⟩
      · rw [Wfam_ne S s h0, ← hνr]
        exact cplx_le fun v hv => hUX hv
      · rw [φN, Matrix.toLin'_apply]
        refine cplx_inv (Nr S s) (fun v hv => ?_) w hw
        have := ((inv_sub_iff _ r U).mpr hUg) v hv
        rwa [Matrix.mulVecLin_apply] at this
    have conjC : ∀ U : Submodule ℝ (ιZ ⊕ ιz → ℝ), ∀ μ ∈ Tset sel s,
        ∀ w ∈ Function.update (Ublk S sel s) ν (cplx U) μ, (fun i => starRingEnd ℂ (w i)) ∈
          Function.update (Ublk S sel s) ν (cplx U) (starRingEnd ℂ μ) := by
      intro U μ _ w hw
      by_cases hμν : μ = ν
      · subst hμν
        rw [Function.update_self] at hw
        rw [hcν, Function.update_self]
        exact cplx_conjStable U w hw
      · have hcμ : starRingEnd ℂ μ ≠ ν := fun h => hμν (by rw [← hcν, ← h, Complex.conj_conj])
        rw [Function.update_of_ne hμν] at hw
        rw [Function.update_of_ne hcμ]
        exact Ublk_conj S sel s μ w hw
    refine ⟨_, _, ⟨_, adm1 _ (okC U₁ a1 a2 a3), rfl⟩, conjStable_sup hc (conjC U₁),
      ⟨_, adm1 _ (okC U₂ b1 b2 b3), rfl⟩, conjStable_sup hc (conjC U₂),
      sup_ne_of_block_ne S (adm1 _ (okC U₁ a1 a2 a3)) (adm1 _ (okC U₂ b1 b2 b3)) hν ?_⟩
    rw [Function.update_self, Function.update_self]
    intro h
    apply hne
    rw [← realPart_cplx U₁, h, realPart_cplx]
  · -- a non-real eigenvalue: blocks at `ν` and conjugate blocks at `ν̄`
    set νc := starRingEnd ℂ ν with hνc
    have hνcν : ν ≠ νc := by
      intro h
      apply hre
      have := congrArg Complex.im h
      rw [hνc, Complex.conj_im] at this
      linarith
    have hνc0 : νc ≠ ν0 s := by
      intro h
      apply h0
      rw [← hν0r, ← h, hνc, Complex.conj_conj]
    have hνcT : νc ∈ Tset sel s := Tset_conj hc s hν
    have hkc : kc sel s νc = kc sel s ν := by
      have e : (s : ℂ) + νc⁻¹ = starRingEnd ℂ ((s : ℂ) + ν⁻¹) := by
        simp [hνc, map_add, map_inv₀, Complex.conj_ofReal]
      unfold kc
      rw [e]
      conv_lhs => rw [← hc]
      exact Multiset.count_map_eq_count' _ _ (starRingEnd ℂ).injective _
    set g := φN S s - ν • (1 : Module.End ℂ (ιZ ⊕ ιz → ℂ)) with hg
    have hXg := (inv_sub_iff _ ν _).mp (maxGen_mapsTo S s ν)
    have hd2 : 2 ≤ Module.finrank ℂ ((φN S s).maxGenEigenspace ν ⊓ LinearMap.ker g :
        Submodule ℂ _) := by
      rw [hg, maxGen_inf_ker]
      omega
    obtain ⟨U₁, U₂, a1, a2, a3, b1, b2, b3, hne⟩ :=
      two_of_not_cyclic g _ hXg (maxGen_nil S s ν) hd2 hk (by rw [← Wfam_ne S s h0]; exact hlt)
    set F : Submodule ℂ (ιZ ⊕ ιz → ℂ) → ℂ → Submodule ℂ (ιZ ⊕ ιz → ℂ) := fun U =>
      Function.update (Function.update (Ublk S sel s) ν U) νc (conjPre U) with hF
    have Fν : ∀ U, F U ν = U := fun U => by
      rw [hF]
      dsimp only
      rw [Function.update_of_ne hνcν, Function.update_self]
    have Fνc : ∀ U, F U νc = conjPre U := fun U => by
      rw [hF]
      dsimp only
      rw [Function.update_self]
    have Foth : ∀ U μ, μ ≠ ν → μ ≠ νc → F U μ = Ublk S sel s μ := fun U μ h1 h2 => by
      rw [hF]
      dsimp only
      rw [Function.update_of_ne h2, Function.update_of_ne h1]
    have admF : ∀ U, U ≤ (φN S s).maxGenEigenspace ν → (∀ x ∈ U, g x ∈ U) →
        Module.finrank ℂ U = kc sel s ν → AdmBlocks S sel s (F U) := by
      intro U hUX hUg hUk
      have hUf := (inv_sub_iff _ ν U).mpr hUg
      refine ⟨by rw [Foth U _ (Ne.symm h0) (Ne.symm hνc0), Ublk_ν0, Wfam_ν0],
        fun μ hμ hμ0 => ?_⟩
      by_cases h1 : μ = ν
      · rw [h1, Fν]
        exact ⟨by rw [Wfam_ne S s h0]; exact hUX, hUf, hUk⟩
      by_cases h2 : μ = νc
      · rw [h2, Fνc]
        refine ⟨?_, fun w hw => ?_, by rw [finrank_conjPre, hUk, hkc]⟩
        · rw [Wfam_ne S s hνc0]
          intro w hw
          have h3 := conj_mem_maxGen (Nr S s) (hUX hw)
          simp only [Complex.conj_conj] at h3
          exact h3
        · change (fun i => starRingEnd ℂ (φN S s w i)) ∈ U
          have h3 := hUf _ hw
          rw [φN, Matrix.toLin'_apply] at h3 ⊢
          rw [← map_mulVec_conj]
          exact h3
      · rw [Foth U μ h1 h2]
        exact hok μ hμ hμ0
    have conjF : ∀ U, ∀ μ ∈ Tset sel s, ∀ w ∈ F U μ,
        (fun i => starRingEnd ℂ (w i)) ∈ F U (starRingEnd ℂ μ) := by
      intro U μ _ w hw
      by_cases h1 : μ = ν
      · have e : starRingEnd ℂ μ = νc := by rw [h1, hνc]
        rw [h1, Fν] at hw
        rw [e, Fνc]
        change (fun i => starRingEnd ℂ (starRingEnd ℂ (w i))) ∈ U
        simpa using hw
      by_cases h2 : μ = νc
      · have e : starRingEnd ℂ μ = ν := by rw [h2, hνc, Complex.conj_conj]
        rw [h2, Fνc] at hw
        rw [e, Fν]
        exact hw
      · have h1' : starRingEnd ℂ μ ≠ ν := fun h => h2 (by rw [hνc, ← h, Complex.conj_conj])
        have h2' : starRingEnd ℂ μ ≠ νc := fun h => h1 (by
          have := congrArg (starRingEnd ℂ) h
          rwa [Complex.conj_conj, hνc, Complex.conj_conj] at this)
        rw [Foth U μ h1 h2] at hw
        rw [Foth U _ h1' h2']
        exact Ublk_conj S sel s μ w hw
    refine ⟨_, _, ⟨_, admF U₁ a1 a2 a3, rfl⟩, conjStable_sup hc (conjF U₁),
      ⟨_, admF U₂ b1 b2 b3, rfl⟩, conjStable_sup hc (conjF U₂),
      sup_ne_of_block_ne S (admF U₁ a1 a2 a3) (admF U₂ b1 b2 b3) hν ?_⟩
    rw [Fν, Fν]
    exact hne

/-- Woodford (2003), App. G.1 and Proposition 8.1 (**the exact criterion, complex form**): for a
conjugation-closed selection of nonzero roots, each taken at most with its multiplicity, the
selected subspace is unique **iff** every partially selected eigenvalue has a single Jordan chain
(`CyclicPartial`). -/
theorem selSpace_unique_iff (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ}
    (hc : ConjClosed sel) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ) :
    (∀ W W' : Submodule ℂ (ιZ ⊕ ιz → ℂ), SelSpace S sel s W → SelSpace S sel s W' → W = W') ↔
      CyclicPartial S sel s := by
  constructor
  · intro h
    by_contra hnc
    obtain ⟨W, W', h1, -, h2, -, hne⟩ := exists_two_of_not_cyclic S hc hs hsel hcnt hnc
    exact hne (h W W' h1 h2)
  · intro hcyc W W' hW hW'
    exact selSpace_unique_of_cyclic S hcyc hW hW'

/-- Woodford (2003), App. G.1, fn 2 and Proposition 8.1 (**the exact criterion, real form**):
among conjugation-closed selected subspaces (the complexifications of the real column spaces
of `J`), the selected subspace is unique **iff** `CyclicPartial` holds. -/
theorem selSpace_conj_unique_iff (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ}
    (hc : ConjClosed sel) {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ) :
    (∀ W W' : Submodule ℂ (ιZ ⊕ ιz → ℂ), SelSpace S sel s W → ConjStable W →
      SelSpace S sel s W' → ConjStable W' → W = W') ↔ CyclicPartial S sel s := by
  constructor
  · intro h
    by_contra hnc
    obtain ⟨W, W', h1, c1, h2, c2, hne⟩ := exists_two_of_not_cyclic S hc hs hsel hcnt hnc
    exact hne (h W W' h1 c1 h2 c2)
  · intro hcyc W W' hW _ hW' _
    exact selSpace_unique_of_cyclic S hcyc hW hW'

/-- Woodford (2003), App. G.1 (**cyclic case**): under `CyclicPartial` every selected subspace
is the one built in `TidyR5bPartialSel.Wp`. -/
theorem selSpace_eq_Wp (S : LinearRESystem ιZ ιz) {sel : Multiset ℂ} (hc : ConjClosed sel)
    {s : ℝ} (hs : (S.Ahat - s • S.Ihat).det ≠ 0)
    (hsel : ∀ μ ∈ sel, μ ≠ 0 ∧ S.pencilPoly.eval μ = 0)
    (hcnt : ∀ μ ∈ sel, sel.count μ ≤ S.pencilPoly.roots.count μ)
    (hcyc : CyclicPartial S sel s) {W : Submodule ℂ (ιZ ⊕ ιz → ℂ)} (hW : SelSpace S sel s W) :
    W = Wp S sel s :=
  selSpace_unique_of_cyclic S hcyc hW (selSpace_Wp S hc hs hsel hcnt)

/-! ### `Υ` and the column space of `J` -/

/-- Woodford (2003), eq. (1.21), p. 553 (**`Υ` determines the column space**): if `Ẽ` is
invertible and `J₁`, `J₁'` are invertible, equal `Υ` forces `J' = J T` with
`T = J₁⁻¹ J₁'` invertible. -/
theorem mul_of_Υ_eq (S : LinearRESystem ιZ ιz) (hE : IsUnit S.Et.det)
    {J J' : Matrix (ιZ ⊕ ιz) ιZ ℝ} (h1 : IsUnit (J1 J).det) (h1' : IsUnit (J1 J').det)
    (hΥ : Υmat S J = Υmat S J') :
    IsUnit ((J1 J)⁻¹ * J1 J').det ∧ J' = J * ((J1 J)⁻¹ * J1 J') := by
  have hEt : IsUnit S.Etᵀ.det := by rwa [det_transpose]
  refine ⟨?_, ?_⟩
  · rw [det_mul, det_nonsing_inv]
    exact (h1.ringInverse).mul h1'
  have e1 : ((J1 J)ᵀ)⁻¹ * (J2 J)ᵀ = ((J1 J')ᵀ)⁻¹ * (J2 J')ᵀ := by
    have h := neg_inj.mp hΥ
    have := congrArg (· * (S.Etᵀ)⁻¹) h
    simp only [Matrix.mul_assoc, mul_nonsing_inv _ hEt, Matrix.mul_one] at this
    exact this
  have e2 : J2 J * (J1 J)⁻¹ = J2 J' * (J1 J')⁻¹ := by
    have := congrArg Matrix.transpose e1
    rwa [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose,
      ← transpose_nonsing_inv, ← transpose_nonsing_inv, transpose_transpose,
      transpose_transpose] at this
  have f1 : J1 (J * ((J1 J)⁻¹ * J1 J')) = J1 J' := by
    rw [J1_mul, ← Matrix.mul_assoc, mul_nonsing_inv _ h1, Matrix.one_mul]
  have f2 : J2 (J * ((J1 J)⁻¹ * J1 J')) = J2 J' := by
    rw [J2_mul, ← Matrix.mul_assoc, e2, Matrix.mul_assoc, nonsing_inv_mul _ h1',
      Matrix.mul_one]
  ext r b
  rcases r with a | a
  · exact (congrFun (congrFun f1 a) b).symm
  · exact (congrFun (congrFun f2 a) b).symm

/-- Woodford (2003), eq. (1.21), p. 553 (**`Υ` is a function of the column space, and
conversely**): with `Ẽ`, `J₁`, `J₁'` invertible, `Υ(J) = Υ(J')` iff `J' = J T` for an invertible
`T`. So a unique selected column space gives a unique `Υ`, and two column spaces give two `Υ`
(`InertiaSplit.Υmat_mul`, `mul_of_Υ_eq`). -/
theorem Υ_eq_iff_mul (S : LinearRESystem ιZ ιz) (hE : IsUnit S.Et.det)
    {J J' : Matrix (ιZ ⊕ ιz) ιZ ℝ} (h1 : IsUnit (J1 J).det) (h1' : IsUnit (J1 J').det) :
    Υmat S J = Υmat S J' ↔ ∃ T : Matrix ιZ ιZ ℝ, IsUnit T.det ∧ J' = J * T := by
  constructor
  · intro hΥ
    obtain ⟨hT, hJ⟩ := mul_of_Υ_eq S hE h1 h1' hΥ
    exact ⟨_, hT, hJ⟩
  · rintro ⟨T, hT, rfl⟩
    exact (InertiaSplit.Υmat_mul S J hT).symm

end Woodford.OptimalPolicyRules.TidyR5bCyclicSel
