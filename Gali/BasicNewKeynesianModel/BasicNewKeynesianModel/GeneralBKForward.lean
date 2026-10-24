/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.MoneyRule
import BasicNewKeynesianModel.InvariantSplit

/-!
# Forward systems over an arbitrary finite index type

Woodford (2003), *Interest and Prices*, Appendix C.1, p. 670, fn. 1 (Blanchard and Kahn 1980).
Vector processes of random variables indexed by any finite type, and the forward system
`s_t = K E_t s_{t+1} + w_t`: if the powers of `K` decay geometrically it has exactly one bounded
adapted solution for every bounded adapted forcing, the forward series
`s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` (`fsolves_exists`, `fsolves_unique`).

Restated from `BlanchardKahn` (`rvMul`, `FSolves`, `fsolves_iterate`, `fsolves_unique`,
`fsolves_exists`, which restated them from the Galí Chapter 6 project), generalised from `Fin n`
to any finite index type.

Restated from the Woodford Chapter 4 project (`NeoWicksellianFramework.GeneralBKForward`,
namespace renamed; this project does not import across projects); the interchange of `E_t` and a
geometrically dominated series is `MoneyRule.E_tsum`. Used here for Galí (2015), Ch. 3, §3.4.2,
p. 75 and fn. 14 (`MoneyRuleDeterminacy`).
-/

namespace Gali.BasicNewKeynesianModel.GeneralBKForward

open Filter Topology
open scoped Matrix

/-- Woodford (2003), App. C.1, p. 670 (tool): a matrix acting on a vector of random variables,
`(M a)_i = ∑_j M_{ij} a_j`. -/
def mv {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) : m → Ω → ℝ :=
  fun i => ∑ j, M i j • a j

/-- Woodford (2003), App. C.1, p. 670 (tool): the action, pointwise. -/
theorem mv_apply {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m)
    (ω : Ω) : mv M a i ω = (M *ᵥ fun j => a j ω) i := by
  simp [mv, Finset.sum_apply, Matrix.mulVec, dotProduct]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action, pointwise, as a sum. -/
theorem mv_apply_sum {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m)
    (ω : Ω) : mv M a i ω = ∑ j, M i j * a j ω := by
  simp [mv, Finset.sum_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): compatibility with matrix multiplication. -/
theorem mv_mv {Ω m n l : Type*} [Fintype n] [Fintype l] (M : Matrix m n ℝ) (N : Matrix n l ℝ)
    (a : l → Ω → ℝ) : mv M (mv N a) = mv (M * N) a := by
  funext i
  simp only [mv, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

/-- Woodford (2003), App. C.1, p. 670 (tool): additivity of the action. -/
theorem mv_add {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a b : n → Ω → ℝ) :
    mv M (a + b) = mv M a + mv M b := by
  funext i
  simp only [mv, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action respects subtraction. -/
theorem mv_sub {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a b : n → Ω → ℝ) :
    mv M (a - b) = mv M a - mv M b := by
  funext i
  simp only [mv, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action of a sum of matrices. -/
theorem add_mv {Ω m n : Type*} [Fintype n] (M N : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv (M + N) a = mv M a + mv N a := by
  funext i
  simp only [mv, Matrix.add_apply, add_smul, Finset.sum_add_distrib, Pi.add_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action of a difference of matrices. -/
theorem sub_mv {Ω m n : Type*} [Fintype n] (M N : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv (M - N) a = mv M a - mv N a := by
  funext i
  simp only [mv, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib, Pi.sub_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the identity matrix acts trivially. -/
theorem mv_one {Ω n : Type*} [Fintype n] [DecidableEq n] (a : n → Ω → ℝ) :
    mv (1 : Matrix n n ℝ) a = a := by
  funext i
  simp [mv, Matrix.one_apply]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action on the zero vector. -/
theorem mv_zero {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) :
    mv M (0 : n → Ω → ℝ) = 0 := by
  funext i
  simp [mv]

/-- Woodford (2003), App. C.1, p. 670 (tool): the action respects negation. -/
theorem mv_neg {Ω m n : Type*} [Fintype n] (M : Matrix m n ℝ) (a : n → Ω → ℝ) :
    mv M (-a) = -mv M a := by
  funext i
  simp [mv, Finset.sum_neg_distrib]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), App. C.1, p. 670 (tool): `E_t` commutes with constant matrices. -/
theorem E_mv {m n : Type*} [Fintype n] (t : ℕ) (M : Matrix m n ℝ) (a : n → Ω → ℝ) (i : m) :
    𝔼.E t (mv M a i) = mv M (fun j => 𝔼.E t (a j)) i := by
  simp only [mv, map_sum, map_smul]

/-- Woodford (2003), App. C.1, p. 670: a vector process is adapted. -/
def AdaptedV {ι : Type*} (s : ℕ → ι → Ω → ℝ) : Prop := ∀ t i, 𝔼.E t (s t i) = s t i

/-- Woodford (2003), App. C.1, p. 670: a vector process is bounded. -/
def BoundedV {ι : Type*} (s : ℕ → ι → Ω → ℝ) : Prop := ∃ M, ∀ t i ω, |s t i ω| ≤ M

/-- Woodford (2003), App. C.1, p. 670: `s` solves the forward system
`s_t = K E_t s_{t+1} + w_t`. -/
def FSolves {ι : Type*} [Fintype ι] (K : Matrix ι ι ℝ) (w s : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ t, s t = mv K (fun j => 𝔼.E t (s (t + 1) j)) + w t

/-- Woodford (2003), App. C.1, p. 670 (tool): a constant matrix maps a bounded vector process to
a bounded one. -/
theorem boundedV_mv {m n : Type*} [Finite m] [Fintype n] (M : Matrix m n ℝ)
    {a : ℕ → n → Ω → ℝ} (ha : BoundedV a) : BoundedV (fun t => mv M (a t)) := by
  have := Fintype.ofFinite m
  obtain ⟨B, hB⟩ := ha
  refine ⟨Fintype.card n * ((∑ i, ∑ j, |M i j|) * max B 0), fun t i ω => ?_⟩
  change |mv M (a t) i ω| ≤ _
  rw [mv_apply]
  exact InvariantSplit.abs_mulVec_le M _ (InvariantSplit.abs_entry_le_sum M)
    (fun j => (hB t j ω).trans (le_max_left _ _)) i |>.trans (le_of_eq (by ring))

/-- Woodford (2003), App. C.1, p. 670 (tool): a constant matrix maps an adapted vector process
to an adapted one. -/
theorem adaptedV_mv {m n : Type*} [Fintype n] (M : Matrix m n ℝ) {a : ℕ → n → Ω → ℝ}
    (ha : AdaptedV 𝔼 a) : AdaptedV 𝔼 (fun t => mv M (a t)) := by
  intro t i
  change 𝔼.E t (mv M (a t) i) = mv M (a t) i
  rw [E_mv 𝔼]
  congr 1
  funext j
  exact ha t j

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), App. C.1, p. 670: iterating a homogeneous forward system,
`d_t = Kᵏ E_t d_{t+k}`. -/
theorem fsolves_iterate {K : Matrix ι ι ℝ} {d : ℕ → ι → Ω → ℝ} (hd : FSolves 𝔼 K 0 d)
    (had : AdaptedV 𝔼 d) (t k : ℕ) : d t = mv (K ^ k) (fun j => 𝔼.E t (d (t + k) j)) := by
  induction k with
  | zero =>
    funext i
    simp only [pow_zero, add_zero, mv_one, had t i]
  | succ k ih =>
    rw [ih]
    have h := hd (t + k)
    simp only [Pi.zero_apply, add_zero] at h
    have : (fun j => 𝔼.E t (d (t + k) j)) = mv K (fun j => 𝔼.E t (d (t + (k + 1)) j)) := by
      funext j
      rw [h, E_mv 𝔼]
      congr 1
      funext l
      rw [𝔼.tower (Nat.le_add_right t k), ← add_assoc]
    rw [this, mv_mv, ← pow_succ]

omit [DecidableEq ι] in
/-- Woodford (2003), App. C.1, p. 670 (tool): bound for `Kᵏ` acting on a bounded vector. -/
theorem abs_mv_le {M : Matrix ι ι ℝ} {c : ℝ} (hM : ∀ i j, |M i j| ≤ c) {a : ι → Ω → ℝ}
    {B : ℝ} (ha : ∀ j ω, |a j ω| ≤ B) (i : ι) (ω : Ω) :
    |mv M a i ω| ≤ Fintype.card ι * (c * B) := by
  rw [mv_apply]
  exact InvariantSplit.abs_mulVec_le M _ hM (fun j => ha j ω) i

/-- Woodford (2003), App. C.1, p. 670, fn. 1 (Blanchard–Kahn): if the powers of `K` decay
geometrically, `s_t = K E_t s_{t+1} + w_t` has at most one bounded adapted solution. -/
theorem fsolves_unique {K : Matrix ι ι ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w x y : ℕ → ι → Ω → ℝ}
    (hx : FSolves 𝔼 K w x) (hy : FSolves 𝔼 K w y) (hax : AdaptedV 𝔼 x) (hay : AdaptedV 𝔼 y)
    (hbx : BoundedV x) (hby : BoundedV y) : x = y := by
  obtain ⟨M₁, hM₁⟩ := hbx
  obtain ⟨M₂, hM₂⟩ := hby
  set d : ℕ → ι → Ω → ℝ := fun t => x t - y t with hd_def
  have hd : FSolves 𝔼 K 0 d := by
    intro t
    simp only [hd_def, Pi.zero_apply, add_zero, Pi.sub_apply, map_sub]
    rw [hx t, hy t]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, mv, smul_sub, Finset.sum_sub_distrib]
    abel
  have had : AdaptedV 𝔼 d := by
    intro t i
    simp only [hd_def, Pi.sub_apply, map_sub, hax t i, hay t i]
  have hdb : ∀ t i ω, |d t i ω| ≤ M₁ + M₂ := fun t i ω => by
    simp only [hd_def, Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hM₁ t i ω) (hM₂ t i ω))
  have hzero : d = 0 := by
    funext t i ω
    have hle : ∀ k, |d t i ω| ≤ Fintype.card ι * (Cb * ρ ^ k * (M₁ + M₂)) := by
      intro k
      rw [fsolves_iterate 𝔼 hd had t k]
      exact abs_mv_le (hK k) (fun j ω => 𝔼.abs_E_le (hdb (t + k) j) t ω) i ω
    have hlim : Tendsto (fun k : ℕ => (Fintype.card ι : ℝ) * (Cb * ρ ^ k * (M₁ + M₂))) atTop
        (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul Cb).mul_const
        (M₁ + M₂)
      simpa using this.const_mul (Fintype.card ι : ℝ)
    have h0 : |d t i ω| ≤ 0 := ge_of_tendsto' hlim hle
    simpa using h0
  funext t i ω
  have := congrFun (congrFun (congrFun hzero t) i) ω
  simpa [hd_def, sub_eq_zero] using this

/-- Woodford (2003), App. C.1, p. 670, fn. 1 (Blanchard–Kahn): if the powers of `K` decay
geometrically, the forward series `s_t = ∑_{k ≥ 0} Kᵏ E_t w_{t+k}` is a bounded adapted solution
of `s_t = K E_t s_{t+1} + w_t` for bounded adapted forcing `w`. -/
theorem fsolves_exists {K : Matrix ι ι ℝ} {Cb ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : ∀ k i j, |(K ^ k) i j| ≤ Cb * ρ ^ k) {w : ℕ → ι → Ω → ℝ} {Mw : ℝ}
    (hw : ∀ t i ω, |w t i ω| ≤ Mw) (haw : AdaptedV 𝔼 w) :
    ∃ s, FSolves 𝔼 K w s ∧ AdaptedV 𝔼 s ∧ BoundedV s := by
  set Mb : ℝ := Fintype.card ι * Cb * Mw with hMb
  set B : ℕ → ℕ → ι → Ω → ℝ := fun k t => mv (K ^ k) (fun j => 𝔼.E t (w (t + k) j)) with hB
  have hT : ∀ k t t' i ω, |mv (K ^ k) (fun j => 𝔼.E t (w t' j)) i ω| ≤ ρ ^ k * Mb := by
    intro k t t' i ω
    have := abs_mv_le (hK k) (fun j ω => 𝔼.abs_E_le (hw t' j) t ω) i ω
    calc _ ≤ Fintype.card ι * (Cb * ρ ^ k * Mw) := this
      _ = ρ ^ k * Mb := by rw [hMb]; ring
  have hTs : ∀ t t' : ℕ → ℕ, ∀ i ω,
      Summable fun k => mv (K ^ k) (fun j => 𝔼.E (t k) (w (t' k) j)) i ω := fun t t' i ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right Mb)
      (fun k => by rw [Real.norm_eq_abs]; exact hT k (t k) (t' k) i ω)
  have hBb : ∀ k t i ω, |B k t i ω| ≤ ρ ^ k * Mb := fun k t i ω => hT k t (t + k) i ω
  have hsum : ∀ t i ω, Summable fun k => B k t i ω := fun t i ω =>
    hTs (fun _ => t) (fun k => t + k) i ω
  set s : ℕ → ι → Ω → ℝ := fun t i ω => ∑' k, B k t i ω with hs
  have hEB : ∀ k t i, 𝔼.E t (B k (t + 1) i) =
      mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i := by
    intro k t i
    simp only [hB, E_mv 𝔼, 𝔼.tower (Nat.le_succ t)]
  have hEs : ∀ t i ω, 𝔼.E t (s (t + 1) i) ω =
      ∑' k, mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) i ω := by
    intro t i ω
    have := MoneyRule.E_tsum 𝔼 hρ0 hρ1 (f := fun k => B k (t + 1) i)
      (fun k ω => hBb k (t + 1) i ω) t ω
    rw [show s (t + 1) i = fun ω' => ∑' k, B k (t + 1) i ω' from rfl, this]
    exact tsum_congr fun k => by rw [hEB]
  refine ⟨s, ?_, ?_, ?_⟩
  · intro t
    funext i ω
    have hB0 : B 0 t i ω = w t i ω := by
      simp only [hB, pow_zero, add_zero, mv_one, haw t i]
    have hshift : ∀ k, B (k + 1) t i ω =
        ∑ l, K i l * mv (K ^ k) (fun j => 𝔼.E t (w (t + 1 + k) j)) l ω := by
      intro k
      simp only [hB]
      rw [← mv_apply_sum, mv_mv, ← pow_succ', show t + (k + 1) = t + 1 + k by omega]
    have hR : (mv K (fun j => 𝔼.E t (s (t + 1) j)) + w t) i ω =
        (∑' k, B (k + 1) t i ω) + w t i ω := by
      rw [Pi.add_apply, Pi.add_apply, mv_apply_sum]
      congr 1
      simp only [hEs, ← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun l _ =>
        (hTs (fun _ => t) (fun k => t + 1 + k) l ω).mul_left (K i l))]
      exact tsum_congr fun k => (hshift k).symm
    rw [hR, show s t i ω = ∑' k, B k t i ω from rfl, (hsum t i ω).tsum_eq_zero_add, hB0]
    ring
  · intro t i
    funext ω
    have := MoneyRule.E_tsum 𝔼 hρ0 hρ1 (f := fun k => B k t i)
      (fun k ω => hBb k t i ω) t ω
    rw [show s t i = fun ω' => ∑' k, B k t i ω' from rfl, this]
    refine tsum_congr fun k => ?_
    simp only [hB, E_mv 𝔼, 𝔼.E_E_self]
  · refine ⟨Mb / (1 - ρ), fun t i ω => ?_⟩
    have hg : HasSum (fun k : ℕ => ρ ^ k * Mb) (Mb / (1 - ρ)) := by
      have := (hasSum_geometric_of_lt_one hρ0 hρ1).mul_right Mb
      rwa [← div_eq_inv_mul] at this
    have := tsum_of_norm_bounded hg (f := fun k => B k t i ω)
      (fun k => by rw [Real.norm_eq_abs]; exact hBb k t i ω)
    rw [Real.norm_eq_abs] at this
    exact this

end Gali.BasicNewKeynesianModel.GeneralBKForward
