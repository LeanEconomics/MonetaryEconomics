/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureConverse
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Sequences

/-!
# The perfect-foresight solution map of (1.1) + (1.9) has a summable kernel

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541) under perfect
foresight, for an **arbitrary** bounded forcing path (not only the VAR paths `C₂Aᵏs` of
`OptimalRulesMeasureMarkov`).

Under the perfect-foresight Assumption 8.1 (`GeneralFOC.LQ.Assumption81 P perfectForesight 0`)
the bounded solution of (1.1) + (1.9) from the state `n = (Z, M)` with a bounded forcing path
`g = (g_k)` is unique (`solY`, `solΦ`, `sol_spec`, `sol_unique`). This module shows that this
solution map is as regular as a linear rational-expectations solution can be: at every date `d`

`y_d(n, g) = y_d(n, 0) + ∑_k K^d_k g_k`, with `∑_k |K^d_k| < ∞`,

and the same for the multipliers (`kernel_hasSum`, `kernel_summable`). This is what makes the
solution map commute with conditional expectations (the measure-theoretic existence theory of
`OptimalRulesMeasureGeneral`).

## The argument (no root counting)

* The map is affine (`sol_comb`, from `GeneralFOC.LQ.affine_comb_focSystem` and uniqueness) and
  time invariant (`sol_shift`).
* **Closed graph** (`Tlin`, `Tlin_continuous`): as a linear map from
  `ℝ^{n_Z+n_z} × ℓ^∞` (bounded continuous functions on `ℕ`) to `ℓ^∞`, its graph is closed —
  uniform limits of solutions solve the equations (`pfsol_limit`) and are bounded, so uniqueness
  identifies them — hence it is continuous (Mathlib's closed graph theorem): solutions are
  bounded uniformly in the size of the data (`sol_bound`).
* **Sequential compactness** (`sol_tendsto`): with uniformly bounded data converging pointwise,
  the solutions converge pointwise — every subsequence has a pointwise convergent
  subsequence (Tychonoff), whose limit solves the equations and is bounded, hence is the solution.
* Truncating the forcing path (`truncSeq`) and passing to the limit gives the series; the uniform
  bound applied to sign patterns gives absolute summability.
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureKernel

open Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open scoped BoundedContinuousFunction

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### The deterministic system from a state with a forcing path -/

/-- Woodford (2003), (1.1) + (1.9), pp. 537–541, under perfect foresight: `(y, φ)` solves the
system with forcing path `g` (`c_k = g_k`) from the state `n = (Z_0, M_{−1})`. -/
def PFSol (P : LQProblem ιZ ιz ιτ) (n : ιZ ⊕ ιz → ℝ) (g : ℕ → ιz → ℝ)
    (y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Unit → ιZ ⊕ ιz → ℝ) : Prop :=
  FOCSystem P perfectForesight (fun k _ => g k) 0 (fun _ j => n (Sum.inl j))
    (fun _ r => n (Sum.inr r)) y φ

/-- Woodford (2003), fn 6, p. 539: a bounded forcing path. -/
def BddSeq {ι : Type*} (g : ℕ → ι → ℝ) : Prop := ∃ K, ∀ k i, |g k i| ≤ K

variable {P : LQProblem ιZ ιz ιτ}

/-- Woodford (2003), Assumption 8.1 (existence), p. 541, under perfect foresight: a bounded
solution from every state for every bounded forcing path. -/
theorem pfsol_exists (hA81 : Assumption81 P perfectForesight 0) (n : ιZ ⊕ ιz → ℝ)
    {g : ℕ → ιz → ℝ} (hg : BddSeq g) : ∃ y φ, PFSol P n g y φ := by
  obtain ⟨K, hK⟩ := hg
  exact hA81.solvable _ _ _ ⟨K, fun k _ i => hK k i⟩ (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => rfl)

/-- Woodford (2003), Assumption 8.1, p. 541: the plan of the bounded perfect-foresight solution
from the state `n` with forcing path `g` (`0` for an unbounded path). -/
noncomputable def solY (hA81 : Assumption81 P perfectForesight 0) (n : ιZ ⊕ ιz → ℝ)
    (g : ℕ → ιz → ℝ) : ℕ → (ιZ ⊕ ιz) ⊕ Unit → ℝ := by
  classical
  exact if h : BddSeq g then fun k => Classical.choose (pfsol_exists hA81 n h) k () else 0

/-- Woodford (2003), Assumption 8.1, p. 541: the multipliers of the bounded perfect-foresight
solution from `n` with forcing path `g`. -/
noncomputable def solΦ (hA81 : Assumption81 P perfectForesight 0) (n : ιZ ⊕ ιz → ℝ)
    (g : ℕ → ιz → ℝ) : ℕ → ιZ ⊕ ιz → ℝ := by
  classical
  exact if h : BddSeq g then
    fun k => Classical.choose (Classical.choose_spec (pfsol_exists hA81 n h)) k ()
  else 0

variable (hA81 : Assumption81 P perfectForesight 0)

/-- Woodford (2003), Assumption 8.1, p. 541: `(solY, solΦ)` solves the system. -/
theorem sol_spec (n : ιZ ⊕ ιz → ℝ) {g : ℕ → ιz → ℝ} (hg : BddSeq g) :
    PFSol P n g (fun k _ => solY hA81 n g k) (fun k _ => solΦ hA81 n g k) := by
  simp only [solY, solΦ, hg, ↓reduceDIte]
  exact Classical.choose_spec (Classical.choose_spec (pfsol_exists hA81 n hg))

/-- Woodford (2003), Assumption 8.1 (uniqueness), p. 541: every bounded solution is
`(solY, solΦ)`. -/
theorem sol_unique {n : ιZ ⊕ ιz → ℝ} {g : ℕ → ιz → ℝ} (hg : BddSeq g)
    {y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Unit → ιZ ⊕ ιz → ℝ}
    (h : PFSol P n g y φ) : ∀ k, y k () = solY hA81 n g k ∧ φ k () = solΦ hA81 n g k := by
  intro k
  have := hA81.unique _ _ _ _ _ _ _ h (sol_spec hA81 n hg) k (Nat.zero_le k)
  exact ⟨congrFun this.1 (), congrFun this.2 ()⟩

/-- Woodford (2003), fn 6, p. 539: the solution is bounded. -/
theorem sol_bdd (n : ιZ ⊕ ιz → ℝ) {g : ℕ → ιz → ℝ} (hg : BddSeq g) :
    ∃ M, ∀ k, (∀ i, |solY hA81 n g k i| ≤ M) ∧ ∀ i, |solΦ hA81 n g k i| ≤ M := by
  obtain ⟨⟨-, -, ⟨M1, hM1⟩, -⟩, ⟨M2, hM2⟩, -⟩ := sol_spec hA81 n hg
  exact ⟨max M1 M2, fun k => ⟨fun i => (hM1 k () i).trans (le_max_left _ _),
    fun i => (hM2 k () i).trans (le_max_right _ _)⟩⟩

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 6 (tool): affine combinations of bounded paths are bounded. -/
theorem bddSeq_comb {ι : Type*} (w1 w2 w3 : ℝ) {g1 g2 g3 : ℕ → ι → ℝ} (h1 : BddSeq g1)
    (h2 : BddSeq g2) (h3 : BddSeq g3) : BddSeq (w1 • g1 + w2 • g2 + w3 • g3) := by
  obtain ⟨K1, hK1⟩ := h1
  obtain ⟨K2, hK2⟩ := h2
  obtain ⟨K3, hK3⟩ := h3
  refine ⟨|w1| * K1 + |w2| * K2 + |w3| * K3, fun k i => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |w1 * g1 k i + w2 * g2 k i + w3 * g3 k i|
      ≤ |w1 * g1 k i| + |w2 * g2 k i| + |w3 * g3 k i| := abs_add_three _ _ _
    _ ≤ |w1| * K1 + |w2| * K2 + |w3| * K3 := by
      rw [abs_mul, abs_mul, abs_mul]
      gcongr
      · exact hK1 k i
      · exact hK2 k i
      · exact hK3 k i

/-- Woodford (2003), (1.10), p. 542: **the solution map is affine** — an affine combination of
data gives the affine combination of solutions (`GeneralFOC.LQ.affine_comb_focSystem` and
uniqueness). -/
theorem sol_comb {w1 w2 w3 : ℝ} (hw : w1 + w2 + w3 = 1) (n1 n2 n3 : ιZ ⊕ ιz → ℝ)
    {g1 g2 g3 : ℕ → ιz → ℝ} (h1 : BddSeq g1) (h2 : BddSeq g2) (h3 : BddSeq g3) (k : ℕ) :
    solY hA81 (w1 • n1 + w2 • n2 + w3 • n3) (w1 • g1 + w2 • g2 + w3 • g3) k =
        w1 • solY hA81 n1 g1 k + w2 • solY hA81 n2 g2 k + w3 • solY hA81 n3 g3 k ∧
      solΦ hA81 (w1 • n1 + w2 • n2 + w3 • n3) (w1 • g1 + w2 • g2 + w3 • g3) k =
        w1 • solΦ hA81 n1 g1 k + w2 • solΦ hA81 n2 g2 k + w3 • solΦ hA81 n3 g3 k := by
  have hc := affine_comb_focSystem hw (sol_spec hA81 n1 h1) (sol_spec hA81 n2 h2)
    (sol_spec hA81 n3 h3)
  have hs : PFSol P (w1 • n1 + w2 • n2 + w3 • n3) (w1 • g1 + w2 • g2 + w3 • g3)
      (comb3 w1 w2 w3 (fun k _ => solY hA81 n1 g1 k) (fun k _ => solY hA81 n2 g2 k)
        (fun k _ => solY hA81 n3 g3 k))
      (comb3 w1 w2 w3 (fun k _ => solΦ hA81 n1 g1 k) (fun k _ => solΦ hA81 n2 g2 k)
        (fun k _ => solΦ hA81 n3 g3 k)) := hc
  have := sol_unique hA81 (bddSeq_comb w1 w2 w3 h1 h2 h3) hs k
  exact ⟨this.1.symm, this.2.symm⟩

/-- Woodford (2003), p. 539: the next state `(Z_1, M_0)` of the solution from `n` with forcing
`g`. -/
noncomputable def nextS (n : ιZ ⊕ ιz → ℝ) (g : ℕ → ιz → ℝ) : ιZ ⊕ ιz → ℝ :=
  Sum.elim (Zpart (solY hA81 n g 1)) (Mpart (solΦ hA81 n g 1))

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 6 (tool): a shifted bounded path is bounded. -/
theorem bddSeq_shift {ι : Type*} {g : ℕ → ι → ℝ} (hg : BddSeq g) : BddSeq (fun j => g (j + 1)) := by
  obtain ⟨K, hK⟩ := hg
  exact ⟨K, fun k i => hK (k + 1) i⟩

/-- Woodford (2003), p. 539: **time invariance** — the solution from `n` continued one period
later is the solution from the state it reaches with the shifted forcing path. -/
theorem sol_shift (n : ιZ ⊕ ιz → ℝ) {g : ℕ → ιz → ℝ} (hg : BddSeq g) (k : ℕ) :
    solY hA81 n g (k + 1) = solY hA81 (nextS hA81 n g) (fun j => g (j + 1)) k ∧
      solΦ hA81 n g (k + 1) = solΦ hA81 (nextS hA81 n g) (fun j => g (j + 1)) k := by
  obtain ⟨⟨hst, -, ⟨Ky, hKy⟩, -⟩, ⟨Kφ, hKφ⟩, -, -, hfoc⟩ := sol_spec hA81 n hg
  refine sol_unique hA81 (bddSeq_shift hg)
    (y := fun j _ => solY hA81 n g (j + 1)) (φ := fun j _ => solΦ hA81 n g (j + 1))
    ⟨⟨fun t _ ω => ?_, fun ω => ?_, ⟨Ky, fun t ω => hKy _ ω⟩, fun _ _ => rfl⟩,
      ⟨Kφ, fun t ω => hKφ _ ω⟩, fun _ _ => rfl, fun ω => ?_, fun t _ ω => ?_⟩ k
  · exact hst (t + 1) (Nat.zero_le _) ω
  · rfl
  · rfl
  · exact hfoc (t + 1) (Nat.zero_le _) ω

/-! ### Limits of solutions -/

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 541 (tool): an equation between continuous functions passes to the limit
along a convergent sequence. -/
theorem lim_eq {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [T2Space β]
    {f g : α → β} (hf : Continuous f) (hg : Continuous g) {a : ℕ → α} {a0 : α}
    (ha : Tendsto a atTop (𝓝 a0)) (h : ∀ j, f (a j) = g (a j)) : f a0 = g a0 := by
  have h1 : Tendsto (fun j => f (a j)) atTop (𝓝 (f a0)) := (hf.tendsto a0).comp ha
  have h2 : Tendsto (fun j => f (a j)) atTop (𝓝 (g a0)) := by
    simp only [h]
    exact (hg.tendsto a0).comp ha
  exact tendsto_nhds_unique h1 h2

/-- Woodford (2003), (1.1) + (1.9) (tool): **pointwise limits of solutions are solutions** — if
`(y^j, φ^j)` solve the perfect-foresight system from `n^j` with forcing `g^j`, the data converge
and the solutions converge at every date to bounded limits, the limits solve the system with the
limit data. -/
theorem pfsol_limit {nj : ℕ → ιZ ⊕ ιz → ℝ} {gj : ℕ → ℕ → ιz → ℝ}
    {yj : ℕ → ℕ → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φj : ℕ → ℕ → ιZ ⊕ ιz → ℝ} {n : ιZ ⊕ ιz → ℝ}
    {g : ℕ → ιz → ℝ} {y : ℕ → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → ιZ ⊕ ιz → ℝ}
    (h : ∀ j, PFSol P (nj j) (gj j) (fun k _ => yj j k) (fun k _ => φj j k))
    (hn : Tendsto nj atTop (𝓝 n)) (hg : ∀ k, Tendsto (fun j => gj j k) atTop (𝓝 (g k)))
    (hy : ∀ k, Tendsto (fun j => yj j k) atTop (𝓝 (y k)))
    (hφ : ∀ k, Tendsto (fun j => φj j k) atTop (𝓝 (φ k)))
    (hyb : ∃ K, ∀ k i, |y k i| ≤ K) (hφb : ∃ K, ∀ k i, |φ k i| ≤ K) :
    PFSol P n g (fun k _ => y k) (fun k _ => φ k) := by
  obtain ⟨Ky, hKy⟩ := hyb
  obtain ⟨Kφ, hKφ⟩ := hφb
  refine ⟨⟨fun t _ ω => ⟨?_, ?_⟩, fun ω => ?_, ⟨Ky, fun k _ i => hKy k i⟩, fun _ _ => rfl⟩,
    ⟨Kφ, fun k _ i => hKφ k i⟩, fun _ _ => rfl, fun ω => ?_, fun t _ ω => ?_⟩
  · -- predetermined rows
    refine lim_eq (f := fun p : ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × ((ιZ ⊕ ιz) ⊕ Unit → ℝ) => Zpart p.1)
      (g := fun p => P.sys.A11 *ᵥ Zpart p.2 + P.sys.A12 *ᵥ zpart p.2)
      (by unfold Zpart; fun_prop) (by unfold Zpart zpart; fun_prop)
      ((hy (t + 1)).prodMk_nhds (hy t)) (fun j => ?_)
    exact ((h j).1.1 t (Nat.zero_le t) ()).1
  · -- expectational rows
    refine lim_eq (f := fun p : ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιz → ℝ) =>
        P.sys.Et *ᵥ zpart p.1)
      (g := fun p => P.sys.A21 *ᵥ Zpart p.2.1 + P.sys.A22 *ᵥ zpart p.2.1 +
        ipart p.2.1 • P.sys.B2 + p.2.2)
      (by unfold zpart; fun_prop) (by unfold Zpart zpart ipart; fun_prop)
      ((hy (t + 1)).prodMk_nhds ((hy t).prodMk_nhds (hg t))) (fun j => ?_)
    exact ((h j).1.1 t (Nat.zero_le t) ()).2
  · -- initial predetermined variables
    refine lim_eq (f := fun p : ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ) => Zpart p.1)
      (g := fun p => fun j => p.2 (Sum.inl j)) (by unfold Zpart; fun_prop) (by fun_prop)
      ((hy 0).prodMk_nhds hn) (fun j => ?_)
    exact (h j).1.2.1 ()
  · -- initial multipliers
    refine lim_eq (f := fun p : (ιZ ⊕ ιz → ℝ) × (ιZ ⊕ ιz → ℝ) => Mpart p.1)
      (g := fun p => fun r => p.2 (Sum.inr r)) (by unfold Mpart; fun_prop) (by fun_prop)
      ((hφ 0).prodMk_nhds hn) (fun j => ?_)
    exact (h j).2.2.2.1 ()
  · -- (1.9)
    refine lim_eq (f := fun p : (ιZ ⊕ ιz → ℝ) × ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ) =>
        P.sys.Atilᵀ *ᵥ p.1 + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ p.2.1 - P.τstar)) -
          P.β⁻¹ • (P.sys.Itilᵀ *ᵥ p.2.2))
      (g := fun _ => 0) (by fun_prop) (by fun_prop)
      ((hφ (t + 1)).prodMk_nhds ((hy t).prodMk_nhds (hφ t))) (fun j => ?_)
    exact (h j).2.2.2.2 t (Nat.zero_le t) ()

/-! ### The closed graph theorem: solutions are bounded uniformly in the data -/

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 6, p. 539 (tool): a bounded continuous function on `ℕ` is a bounded
path. -/
theorem bddSeq_bcf (x : ℕ →ᵇ (ιz → ℝ)) : BddSeq ⇑x :=
  ⟨‖x‖, fun k i => by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (x k) i).trans (x.norm_coe_le_norm k)⟩

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 6 (tool): the zero path is bounded. -/
theorem bddSeq_zero {ι : Type*} : BddSeq (0 : ℕ → ι → ℝ) := ⟨0, fun k i => by simp⟩

/-- Woodford (2003), (1.10) (tool): the solution from `(n, g)` minus the solution from
`(0, 0)`, at date `k`. -/
noncomputable def dvec (n : ιZ ⊕ ιz → ℝ) (g : ℕ → ιz → ℝ) (k : ℕ) :
    ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ) :=
  (solY hA81 n g k - solY hA81 0 0 k, solΦ hA81 n g k - solΦ hA81 0 0 k)

/-- Woodford (2003), fn 6 (tool): `dvec` is bounded over dates. -/
theorem dvec_bound (n : ιZ ⊕ ιz → ℝ) {g : ℕ → ιz → ℝ} (hg : BddSeq g) :
    ∃ C, 0 ≤ C ∧ ∀ k, ‖dvec hA81 n g k‖ ≤ C := by
  obtain ⟨M1, hM1⟩ := sol_bdd hA81 n hg
  obtain ⟨M0, hM0⟩ := sol_bdd hA81 0 (bddSeq_zero (ι := ιz))
  refine ⟨max (M1 + M0) 0, le_max_right _ _, fun k => ?_⟩
  refine norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => ?_,
    (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => ?_⟩
  · rw [Real.norm_eq_abs]
    exact ((abs_sub _ _).trans (add_le_add ((hM1 k).1 i) ((hM0 k).1 i))).trans
      (le_max_left _ _)
  · rw [Real.norm_eq_abs]
    exact ((abs_sub _ _).trans (add_le_add ((hM1 k).2 i) ((hM0 k).2 i))).trans
      (le_max_left _ _)

/-- Woodford (2003), (1.10) (tool): `dvec` as a bounded continuous function on `ℕ`. -/
noncomputable def dbcf (x : (ιZ ⊕ ιz → ℝ) × (ℕ →ᵇ (ιz → ℝ))) :
    ℕ →ᵇ (((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ)) :=
  BoundedContinuousFunction.mkOfDiscrete (dvec hA81 x.1 x.2)
    (2 * Classical.choose (dvec_bound hA81 x.1 (bddSeq_bcf x.2))) fun a b => by
      obtain ⟨-, h⟩ := Classical.choose_spec (dvec_bound hA81 x.1 (bddSeq_bcf x.2))
      rw [dist_eq_norm]
      linarith [norm_sub_le (dvec hA81 x.1 x.2 a) (dvec hA81 x.1 x.2 b), h a, h b]

/-- Woodford (2003), (1.10), p. 542: **the solution map as a linear map** from
`ℝ^{n_Z+n_z} × ℓ^∞` to `ℓ^∞` (bounded continuous functions on `ℕ`), measured from the solution
with zero data. -/
noncomputable def Tlin : ((ιZ ⊕ ιz → ℝ) × (ℕ →ᵇ (ιz → ℝ))) →ₗ[ℝ]
    (ℕ →ᵇ (((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ))) where
  toFun := dbcf hA81
  map_add' x y := by
    refine BoundedContinuousFunction.ext fun k => ?_
    change dvec hA81 (x.1 + y.1) (⇑x.2 + ⇑y.2) k = dvec hA81 x.1 x.2 k + dvec hA81 y.1 y.2 k
    have hc := sol_comb hA81 (w1 := 1) (w2 := 1) (w3 := -1) (by norm_num) x.1 y.1 0
      (bddSeq_bcf x.2) (bddSeq_bcf y.2) (bddSeq_zero (ι := ιz)) k
    simp only [one_smul, smul_zero, add_zero] at hc
    simp only [dvec, hc.1, hc.2, Prod.mk_add_mk]
    congr 1 <;> module
  map_smul' a x := by
    refine BoundedContinuousFunction.ext fun k => ?_
    change dvec hA81 (a • x.1) (a • ⇑x.2) k = a • dvec hA81 x.1 x.2 k
    have hc := sol_comb hA81 (w1 := a) (w2 := 1 - a) (w3 := 0) (by ring) x.1 0 0
      (bddSeq_bcf x.2) (bddSeq_zero (ι := ιz)) (bddSeq_zero (ι := ιz)) k
    simp only [smul_zero, add_zero, zero_smul] at hc
    simp only [dvec, hc.1, hc.2, Prod.smul_mk]
    congr 1 <;> module

/-- Woodford (2003), Assumption 8.1, p. 541, with **the closed graph theorem**: the solution map
`Tlin` is continuous — its graph is closed because uniform limits of solutions solve the system
(`pfsol_limit`) and are bounded, so uniqueness identifies them. -/
theorem Tlin_continuous : Continuous (Tlin hA81) := by
  refine (Tlin hA81).continuous_of_seq_closed_graph fun u x w hu hw => ?_
  refine BoundedContinuousFunction.ext fun k => ?_
  obtain ⟨M0, hM0⟩ := sol_bdd hA81 0 (bddSeq_zero (ι := ιz))
  have hev : ∀ m, Tendsto (fun j => (Tlin hA81 (u j)) m) atTop (𝓝 (w m)) := fun m =>
    ((BoundedContinuousFunction.lipschitz_eval_const m).continuous.tendsto w).comp hw
  have hsol : PFSol P x.1 ⇑x.2 (fun m _ => (w m).1 + solY hA81 0 0 m)
      (fun m _ => (w m).2 + solΦ hA81 0 0 m) := by
    refine pfsol_limit (nj := fun j => (u j).1) (gj := fun j => ⇑(u j).2)
      (yj := fun j m => solY hA81 (u j).1 (u j).2 m) (φj := fun j m => solΦ hA81 (u j).1 (u j).2 m)
      (fun j => sol_spec hA81 _ (bddSeq_bcf _)) ((continuous_fst.tendsto x).comp hu)
      (fun m => ((BoundedContinuousFunction.lipschitz_eval_const m).continuous.tendsto _).comp
        ((continuous_snd.tendsto x).comp hu)) (fun m => ?_) (fun m => ?_)
      ⟨‖w‖ + M0, fun m i => ?_⟩ ⟨‖w‖ + M0, fun m i => ?_⟩
    · have h2 := ((continuous_fst.tendsto _).comp (hev m)).add_const (solY hA81 0 0 m)
      refine h2.congr fun j => ?_
      change (solY hA81 (u j).1 (u j).2 m - solY hA81 0 0 m) + solY hA81 0 0 m = _
      abel
    · have h2 := ((continuous_snd.tendsto _).comp (hev m)).add_const (solΦ hA81 0 0 m)
      refine h2.congr fun j => ?_
      change (solΦ hA81 (u j).1 (u j).2 m - solΦ hA81 0 0 m) + solΦ hA81 0 0 m = _
      abel
    · have h1 : |(w m).1 i| ≤ ‖w‖ := by
        rw [← Real.norm_eq_abs]
        exact (norm_le_pi_norm _ i).trans ((norm_fst_le _).trans (w.norm_coe_le_norm m))
      exact (abs_add_le _ _).trans (add_le_add h1 ((hM0 m).1 i))
    · have h1 : |(w m).2 i| ≤ ‖w‖ := by
        rw [← Real.norm_eq_abs]
        exact (norm_le_pi_norm _ i).trans ((norm_snd_le _).trans (w.norm_coe_le_norm m))
      exact (abs_add_le _ _).trans (add_le_add h1 ((hM0 m).2 i))
  have := sol_unique hA81 (bddSeq_bcf x.2) hsol k
  change w k = dvec hA81 x.1 x.2 k
  refine Prod.ext ?_ ?_
  · change (w k).1 = solY hA81 x.1 x.2 k - solY hA81 0 0 k
    rw [← this.1]
    abel
  · change (w k).2 = solΦ hA81 x.1 x.2 k - solΦ hA81 0 0 k
    rw [← this.2]
    abel

/-- Woodford (2003), Assumption 8.1, p. 541: **the bounded solution is bounded uniformly in the
size of the data** — for every bound `B` on the state and the forcing path there is a bound `C`
on the solution at every date (consequence of the closed graph theorem). -/
theorem sol_bound (B : ℝ) : ∃ C, ∀ (n : ιZ ⊕ ιz → ℝ) (g : ℕ → ιz → ℝ), (∀ i, |n i| ≤ B) →
    (∀ k i, |g k i| ≤ B) → ∀ k, (∀ i, |solY hA81 n g k i| ≤ C) ∧
      ∀ i, |solΦ hA81 n g k i| ≤ C := by
  set T : ((ιZ ⊕ ιz → ℝ) × (ℕ →ᵇ (ιz → ℝ))) →L[ℝ]
      (ℕ →ᵇ (((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ))) := ⟨Tlin hA81, Tlin_continuous hA81⟩
  obtain ⟨M0, hM0⟩ := sol_bdd hA81 0 (bddSeq_zero (ι := ιz))
  set B' := max B 0 with hB'
  refine ⟨‖T‖ * B' + M0, fun n g hn hg k => ?_⟩
  have hgn : ∀ m, ‖g m‖ ≤ B' := fun m =>
    (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => by
      rw [Real.norm_eq_abs]
      exact (hg m i).trans (le_max_left _ _)
  set gb : ℕ →ᵇ (ιz → ℝ) := BoundedContinuousFunction.mkOfDiscrete g (2 * B') fun a b => by
    rw [dist_eq_norm]
    linarith [norm_sub_le (g a) (g b), hgn a, hgn b] with hgb
  have hx : ‖((n, gb) : (ιZ ⊕ ιz → ℝ) × (ℕ →ᵇ (ιz → ℝ)))‖ ≤ B' := by
    refine norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => ?_,
      (BoundedContinuousFunction.norm_le (le_max_right _ _)).mpr hgn⟩
    rw [Real.norm_eq_abs]
    exact (hn i).trans (le_max_left _ _)
  have hT : ‖T (n, gb)‖ ≤ ‖T‖ * B' :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hk : ‖dvec hA81 n g k‖ ≤ ‖T‖ * B' := ((T (n, gb)).norm_coe_le_norm k).trans hT
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 : |solY hA81 n g k i - solY hA81 0 0 k i| ≤ ‖T‖ * B' := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (dvec hA81 n g k).1 i).trans ((norm_fst_le _).trans hk)
    have := abs_add_le (solY hA81 n g k i - solY hA81 0 0 k i) (solY hA81 0 0 k i)
    rw [sub_add_cancel] at this
    linarith [(hM0 k).1 i]
  · have h1 : |solΦ hA81 n g k i - solΦ hA81 0 0 k i| ≤ ‖T‖ * B' := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (dvec hA81 n g k).2 i).trans ((norm_snd_le _).trans hk)
    have := abs_add_le (solΦ hA81 n g k i - solΦ hA81 0 0 k i) (solΦ hA81 0 0 k i)
    rw [sub_add_cancel] at this
    linarith [(hM0 k).2 i]

/-! ### Sequential compactness: continuity in the product topology on bounded sets -/

/-- Woodford (2003), Assumption 8.1, p. 541: **the solution map is continuous for pointwise
convergence of uniformly bounded data** — if the states converge and the forcing paths converge at
every date, with a common bound, the solutions converge at every date. (Every subsequence has a
pointwise convergent subsequence — Tychonoff — whose limit solves the system and is bounded,
hence is the solution.) -/
theorem sol_tendsto {B : ℝ} {nj : ℕ → ιZ ⊕ ιz → ℝ} {gj : ℕ → ℕ → ιz → ℝ} {n : ιZ ⊕ ιz → ℝ}
    {g : ℕ → ιz → ℝ} (hnb : ∀ j i, |nj j i| ≤ B) (hgb : ∀ j k i, |gj j k i| ≤ B)
    (hn : Tendsto nj atTop (𝓝 n)) (hg : ∀ k, Tendsto (fun j => gj j k) atTop (𝓝 (g k))) :
    ∀ k, Tendsto (fun j => solY hA81 (nj j) (gj j) k) atTop (𝓝 (solY hA81 n g k)) ∧
      Tendsto (fun j => solΦ hA81 (nj j) (gj j) k) atTop (𝓝 (solΦ hA81 n g k)) := by
  obtain ⟨C, hC⟩ := sol_bound hA81 B
  have hgB : BddSeq g := ⟨B, fun k i => by
    have h1 : Tendsto (fun j => |gj j k i|) atTop (𝓝 |g k i|) :=
      ((continuous_abs.comp (continuous_apply i)).tendsto _).comp (hg k)
    exact le_of_tendsto' h1 fun j => hgb j k i⟩
  set W : ℕ → ℕ → ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ) :=
    fun j k => (solY hA81 (nj j) (gj j) k, solΦ hA81 (nj j) (gj j) k) with hW
  set W0 : ℕ → ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ) :=
    fun k => (solY hA81 n g k, solΦ hA81 n g k) with hW0
  set K : Set (ℕ → ((ιZ ⊕ ιz) ⊕ Unit → ℝ) × (ιZ ⊕ ιz → ℝ)) :=
    Set.pi Set.univ (fun _ => Metric.closedBall 0 (max C 0)) with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hWK : ∀ j, W j ∈ K := fun j k _ => by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine norm_prod_le_iff.mpr ⟨(pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => ?_,
      (pi_norm_le_iff_of_nonneg (le_max_right _ _)).mpr fun i => ?_⟩
    · rw [Real.norm_eq_abs]
      exact ((hC (nj j) (gj j) (hnb j) (hgb j) k).1 i).trans (le_max_left _ _)
    · rw [Real.norm_eq_abs]
      exact ((hC (nj j) (gj j) (hnb j) (hgb j) k).2 i).trans (le_max_left _ _)
  have hT : Tendsto W atTop (𝓝 W0) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨a, ha, φ, hφ, hlim⟩ := hKc.isSeqCompact (fun i => hWK (ns i))
    refine ⟨φ, ?_⟩
    have hsub : Tendsto (fun i => ns (φ i)) atTop atTop := hns.comp hφ.tendsto_atTop
    have hak : ∀ k, Tendsto (fun i => W (ns (φ i)) k) atTop (𝓝 (a k)) := fun k =>
      ((continuous_apply k).tendsto a).comp hlim
    have hab : ∀ k, ‖a k‖ ≤ max C 0 := fun k => by
      have := ha k (Set.mem_univ k)
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hsol : PFSol P n g (fun k _ => (a k).1) (fun k _ => (a k).2) := by
      refine pfsol_limit (nj := fun i => nj (ns (φ i))) (gj := fun i => gj (ns (φ i)))
        (yj := fun i k => solY hA81 (nj (ns (φ i))) (gj (ns (φ i))) k)
        (φj := fun i k => solΦ hA81 (nj (ns (φ i))) (gj (ns (φ i))) k)
        (fun i => sol_spec hA81 _ ⟨B, hgb _⟩) (hn.comp hsub) (fun k => (hg k).comp hsub)
        (fun k => (continuous_fst.tendsto _).comp (hak k))
        (fun k => (continuous_snd.tendsto _).comp (hak k))
        ⟨max C 0, fun k i => ?_⟩ ⟨max C 0, fun k i => ?_⟩
      · rw [← Real.norm_eq_abs]
        exact (norm_le_pi_norm _ i).trans ((norm_fst_le _).trans (hab k))
      · rw [← Real.norm_eq_abs]
        exact (norm_le_pi_norm _ i).trans ((norm_snd_le _).trans (hab k))
    have hk : a = W0 := funext fun k =>
      Prod.ext (sol_unique hA81 hgB hsol k).1 (sol_unique hA81 hgB hsol k).2
    rw [← hk]
    exact hlim
  intro k
  have hk := ((continuous_apply k).tendsto W0).comp hT
  exact ⟨(continuous_fst.tendsto _).comp hk, (continuous_snd.tendsto _).comp hk⟩

/-! ### The kernel -/

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), p. 537 (tool): the forcing path that is the unit vector `e_i` at date `k`
and zero otherwise. -/
def imp (k : ℕ) (i : ιz) : ℕ → ιz → ℝ := Pi.single k (Pi.single i 1)

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 537 (tool): the forcing path truncated after `N` periods. -/
def truncSeq {ι : Type*} (N : ℕ) (g : ℕ → ι → ℝ) : ℕ → ι → ℝ :=
  fun k => if k < N then g k else 0

/-- Woodford (2003), (1.10) and p. 541: the **kernel** of the plan at date `d`: column `i` of
`K^d_k` is the response of `y_d` to a unit forcing `e_i` at date `k` (from the zero state). -/
noncomputable def KY (d k : ℕ) : Matrix ((ιZ ⊕ ιz) ⊕ Unit) ιz ℝ :=
  Matrix.of fun a i => solY hA81 0 (imp k i) d a - solY hA81 0 0 d a

/-- Woodford (2003), (1.10) and p. 541: the kernel of the multipliers at date `d`. -/
noncomputable def KΦ (d k : ℕ) : Matrix (ιZ ⊕ ιz) ιz ℝ :=
  Matrix.of fun a i => solΦ hA81 0 (imp k i) d a - solΦ hA81 0 0 d a

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), fn 6 (tool): the unit impulse is bounded. -/
theorem bddSeq_imp (k : ℕ) (i : ιz) : BddSeq (imp k i) := ⟨1, fun m j => by
  by_cases hm : m = k <;> by_cases hj : j = i <;> simp [imp, hm, hj]⟩

/-- Woodford (2003), (1.10) (tool): the response to the forcing path, measured from the zero
forcing, is additive and homogeneous in the forcing (from the zero state). -/
theorem dsol_lin {g1 g2 : ℕ → ιz → ℝ} (h1 : BddSeq g1) (h2 : BddSeq g2) (a b : ℝ) (d : ℕ) :
    solY hA81 0 (a • g1 + b • g2) d - solY hA81 0 0 d =
        a • (solY hA81 0 g1 d - solY hA81 0 0 d) + b • (solY hA81 0 g2 d - solY hA81 0 0 d) ∧
      solΦ hA81 0 (a • g1 + b • g2) d - solΦ hA81 0 0 d =
        a • (solΦ hA81 0 g1 d - solΦ hA81 0 0 d) + b • (solΦ hA81 0 g2 d - solΦ hA81 0 0 d) := by
  have hc := sol_comb hA81 (w1 := a) (w2 := b) (w3 := 1 - a - b) (by ring) 0 0 0 h1 h2
    (bddSeq_zero (ι := ιz)) d
  simp only [smul_zero, add_zero] at hc
  rw [hc.1, hc.2]
  constructor <;> module

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] in
/-- Woodford (2003), p. 537 (tool): the truncated path grows by one date at a time,
`g^{(N+1)} = g^{(N)} + ∑_i g_{N,i} e_i δ_N`. -/
theorem truncSeq_succ (N : ℕ) (g : ℕ → ιz → ℝ) :
    truncSeq (N + 1) g = truncSeq N g + ∑ i, g N i • imp N i := by
  have himp : ∀ k, (∑ i, g N i • imp N i) k = if k = N then g N else 0 := by
    intro k
    funext j
    by_cases hk : k = N
    · subst hk
      simp [imp, Pi.single_apply]
    · simp [imp, hk]
  funext k
  rw [Pi.add_apply, himp]
  by_cases hk : k = N
  · subst hk
    simp [truncSeq]
  · by_cases hlt : k < N
    · simp [truncSeq, hk, hlt, show k < N + 1 by omega]
    · simp [truncSeq, hk, hlt, show ¬ k < N + 1 by omega]

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 6 (tool): truncation preserves a bound. -/
theorem truncSeq_bdd {ι : Type*} {g : ℕ → ι → ℝ} {B : ℝ} (hB : 0 ≤ B) (hg : ∀ k i, |g k i| ≤ B)
    (N : ℕ) : ∀ k i, |truncSeq N g k i| ≤ B := fun k i => by
  simp only [truncSeq]
  split_ifs
  · exact hg k i
  · simpa using hB

/-- Woodford (2003), (1.10) (tool): for a finite sum of impulses the response is the finite sum
of the impulse responses. -/
theorem dsol_finsum (d N : ℕ) (c : ιz → ℝ) (g0 : ℕ → ιz → ℝ) (h0 : BddSeq g0)
    (s : Finset ιz) :
    solY hA81 0 (g0 + ∑ i ∈ s, c i • imp N i) d - solY hA81 0 0 d =
        (solY hA81 0 g0 d - solY hA81 0 0 d) +
          ∑ i ∈ s, c i • (solY hA81 0 (imp N i) d - solY hA81 0 0 d) ∧
      solΦ hA81 0 (g0 + ∑ i ∈ s, c i • imp N i) d - solΦ hA81 0 0 d =
        (solΦ hA81 0 g0 d - solΦ hA81 0 0 d) +
          ∑ i ∈ s, c i • (solΦ hA81 0 (imp N i) d - solΦ hA81 0 0 d) := by
  classical
  induction s using Finset.induction_on generalizing g0 with
  | empty => simp
  | insert i s hi ih =>
    have hb : BddSeq (g0 + c i • imp N i) := by
      have := bddSeq_comb 1 (c i) 0 h0 (bddSeq_imp N i) (bddSeq_zero (ι := ιz))
      simpa using this
    have e : g0 + ∑ x ∈ insert i s, c x • imp N x = (g0 + c i • imp N i) +
        ∑ x ∈ s, c x • imp N x := by
      rw [Finset.sum_insert hi]
      abel
    have hl := dsol_lin hA81 h0 (bddSeq_imp N i) 1 (c i) d
    simp only [one_smul] at hl
    rw [e, Finset.sum_insert hi, Finset.sum_insert hi, (ih _ hb).1, (ih _ hb).2, hl.1, hl.2]
    constructor <;> abel

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 6 (tool): a truncated path is bounded (whatever the path). -/
theorem bddSeq_trunc [Finite ιz] (N : ℕ) (g : ℕ → ιz → ℝ) : BddSeq (truncSeq N g) := by
  have := Fintype.ofFinite ιz
  refine ⟨∑ m ∈ Finset.range N, ∑ i, |g m i|, fun k i => ?_⟩
  simp only [truncSeq]
  split_ifs with hk
  · calc |g k i| ≤ ∑ i, |g k i| :=
          Finset.single_le_sum (f := fun i => |g k i|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ i)
      _ ≤ ∑ m ∈ Finset.range N, ∑ i, |g m i| :=
          Finset.single_le_sum (f := fun m => ∑ i, |g m i|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hk)
  · simp only [Pi.zero_apply, abs_zero]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Woodford (2003), (1.10): **the response to a truncated forcing path is the finite kernel
sum**, `y_d(0, g^{(N)}) − y_d(0, 0) = ∑_{k<N} K^d_k g_k`. -/
theorem dsol_trunc (d : ℕ) (g : ℕ → ιz → ℝ) (N : ℕ) :
    solY hA81 0 (truncSeq N g) d - solY hA81 0 0 d =
        ∑ k ∈ Finset.range N, KY hA81 d k *ᵥ g k ∧
      solΦ hA81 0 (truncSeq N g) d - solΦ hA81 0 0 d =
        ∑ k ∈ Finset.range N, KΦ hA81 d k *ᵥ g k := by
  classical
  induction N with
  | zero =>
    have : truncSeq 0 g = 0 := by
      funext k
      simp [truncSeq]
    simp [this]
  | succ N ih =>
    have hf := dsol_finsum hA81 d N (g N) (truncSeq N g) (bddSeq_trunc N g) Finset.univ
    rw [← truncSeq_succ] at hf
    rw [hf.1, hf.2, ih.1, ih.2, Finset.sum_range_succ, Finset.sum_range_succ]
    constructor
    · congr 1
      funext a
      simp only [KY, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.sub_apply, of_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · congr 1
      funext a
      simp only [KΦ, mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.sub_apply, of_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G (tool): a real number times its sign pattern is its absolute
value. -/
theorem mul_sgn (x : ℝ) : x * (if 0 ≤ x then (1 : ℝ) else -1) = |x| := by
  split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · rw [mul_neg_one, abs_of_neg (not_le.mp h)]

/-- Woodford (2003), Assumption 8.1, p. 541: **the kernel is absolutely summable**,
`∑_k |K^d_k| < ∞` entrywise (the uniform bound `sol_bound` applied to sign patterns). -/
theorem kernel_summable (d : ℕ) :
    (∀ a i, Summable fun k => |KY hA81 d k a i|) ∧ ∀ a i, Summable fun k => |KΦ hA81 d k a i| := by
  obtain ⟨C, hC⟩ := sol_bound hA81 1
  obtain ⟨M0, hM0⟩ := sol_bdd hA81 0 (bddSeq_zero (ι := ιz))
  have hsg : ∀ (s : ℕ → ℝ) (i : ιz), (∀ k, |s k| ≤ 1) →
      ∀ k j, |(fun k => s k • (Pi.single i 1 : ιz → ℝ)) k j| ≤ 1 := by
    intro s i hs k j
    by_cases hj : j = i
    · subst hj
      simpa using hs k
    · simp [hj]
  have hs1 : ∀ x : ℝ, |(if 0 ≤ x then (1 : ℝ) else -1)| ≤ 1 := fun x => by
    split_ifs <;> simp
  have h0 : ∀ i, |(0 : ιZ ⊕ ιz → ℝ) i| ≤ 1 := fun i => by simp
  constructor
  · intro a i
    set sg : ℕ → ιz → ℝ := fun k =>
      (if 0 ≤ KY hA81 d k a i then (1 : ℝ) else -1) • (Pi.single i 1 : ιz → ℝ) with hsgdef
    refine summable_of_sum_range_le (c := C + M0) (fun k => abs_nonneg _) fun N => ?_
    have hb : ∀ k j, |truncSeq N sg k j| ≤ 1 := truncSeq_bdd zero_le_one
      (hsg (fun k => if 0 ≤ KY hA81 d k a i then (1 : ℝ) else -1) i fun k => hs1 _) N
    have h1 := (hC 0 (truncSeq N sg) h0 hb d).1 a
    have heq : ∑ k ∈ Finset.range N, |KY hA81 d k a i| =
        (solY hA81 0 (truncSeq N sg) d - solY hA81 0 0 d) a := by
      rw [(dsol_trunc hA81 d sg N).1, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_sgn, hsgdef]
      simp only
      rw [mulVec_smul, mulVec_single_one, Pi.smul_apply, smul_eq_mul, mul_comm]
      rfl
    rw [heq, Pi.sub_apply]
    exact (le_abs_self _).trans ((abs_sub _ _).trans (add_le_add h1 ((hM0 d).1 a)))
  · intro a i
    set sg : ℕ → ιz → ℝ := fun k =>
      (if 0 ≤ KΦ hA81 d k a i then (1 : ℝ) else -1) • (Pi.single i 1 : ιz → ℝ) with hsgdef
    refine summable_of_sum_range_le (c := C + M0) (fun k => abs_nonneg _) fun N => ?_
    have hb : ∀ k j, |truncSeq N sg k j| ≤ 1 := truncSeq_bdd zero_le_one
      (hsg (fun k => if 0 ≤ KΦ hA81 d k a i then (1 : ℝ) else -1) i fun k => hs1 _) N
    have h1 := (hC 0 (truncSeq N sg) h0 hb d).2 a
    have heq : ∑ k ∈ Finset.range N, |KΦ hA81 d k a i| =
        (solΦ hA81 0 (truncSeq N sg) d - solΦ hA81 0 0 d) a := by
      rw [(dsol_trunc hA81 d sg N).2, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_sgn, hsgdef]
      simp only
      rw [mulVec_smul, mulVec_single_one, Pi.smul_apply, smul_eq_mul, mul_comm]
      rfl
    rw [heq, Pi.sub_apply]
    exact (le_abs_self _).trans ((abs_sub _ _).trans (add_le_add h1 ((hM0 d).2 a)))

omit [Fintype ιZ] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G (tool): a matrix row applied to a bounded vector, entrywise bound. -/
theorem abs_mulVec_le {κ : Type*} (L : Matrix κ ιz ℝ) {v : ιz → ℝ} {B : ℝ}
    (hv : ∀ j, |v j| ≤ B) (a : κ) : |(L *ᵥ v) a| ≤ ∑ j, |L a j| * B := by
  calc |(L *ᵥ v) a| = |∑ j, L a j * v j| := rfl
    _ ≤ ∑ j, |L a j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |L a j| * B := Finset.sum_le_sum fun j _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)

/-- Woodford (2003), (1.10), Assumption 8.1: the response measured from the zero forcing does
not depend on the state. -/
theorem sol_sub_indep (n : ιZ ⊕ ιz → ℝ) {g : ℕ → ιz → ℝ} (hg : BddSeq g) (d : ℕ) :
    solY hA81 n g d - solY hA81 n 0 d = solY hA81 0 g d - solY hA81 0 0 d ∧
      solΦ hA81 n g d - solΦ hA81 n 0 d = solΦ hA81 0 g d - solΦ hA81 0 0 d := by
  have hc := sol_comb hA81 (w1 := 1) (w2 := 1) (w3 := -1) (by norm_num) n 0 0
    (bddSeq_zero (ι := ιz)) hg (bddSeq_zero (ι := ιz)) d
  simp only [one_smul, smul_zero, add_zero, zero_add] at hc
  rw [hc.1, hc.2]
  constructor <;> module

/-- Woodford (2003), (1.10) and Assumption 8.1, p. 541: **the kernel representation** — for every
state `n` and every bounded forcing path `g`, at every date `d`,
`y_d(n, g) = y_d(n, 0) + ∑_k K^d_k g_k` and `φ_d(n, g) = φ_d(n, 0) + ∑_k K^{φ,d}_k g_k`
(convergent series; the kernels are absolutely summable, `kernel_summable`). -/
theorem kernel_hasSum (d : ℕ) (n : ιZ ⊕ ιz → ℝ) {g : ℕ → ιz → ℝ} (hg : BddSeq g) :
    HasSum (fun k => KY hA81 d k *ᵥ g k) (solY hA81 n g d - solY hA81 n 0 d) ∧
      HasSum (fun k => KΦ hA81 d k *ᵥ g k) (solΦ hA81 n g d - solΦ hA81 n 0 d) := by
  obtain ⟨B0, hB0⟩ := hg
  set B := max B0 0 with hBdef
  have hB : ∀ k i, |g k i| ≤ B := fun k i => (hB0 k i).trans (le_max_left _ _)
  have ht := sol_tendsto hA81 (B := B) (nj := fun _ => 0) (gj := fun N => truncSeq N g) (n := 0)
    (g := g) (fun _ i => by simp only [Pi.zero_apply, abs_zero]; exact le_max_right B0 0)
    (fun N => truncSeq_bdd (le_max_right _ _) hB N)
    tendsto_const_nhds (fun k => tendsto_atTop_of_eventually_const (i₀ := k + 1) fun N hN => by
      simp [truncSeq, show k < N by omega]) d
  rw [(sol_sub_indep hA81 n ⟨B0, hB0⟩ d).1, (sol_sub_indep hA81 n ⟨B0, hB0⟩ d).2]
  obtain ⟨hsY, hsΦ⟩ := kernel_summable hA81 d
  constructor
  · rw [Pi.hasSum]
    intro a
    have hs : Summable (fun k => (KY hA81 d k *ᵥ g k) a) := by
      refine Summable.of_norm_bounded (g := fun k => ∑ j, |KY hA81 d k a j| * B)
        (summable_sum fun j _ => (hsY a j).mul_right _) fun k => ?_
      rw [Real.norm_eq_abs]
      exact abs_mulVec_le _ (hB k) a
    have hlim : Tendsto (fun N => ∑ k ∈ Finset.range N, (KY hA81 d k *ᵥ g k) a) atTop
        (𝓝 ((solY hA81 0 g d - solY hA81 0 0 d) a)) := by
      have := ((continuous_apply a).tendsto _).comp (ht.1.sub_const (solY hA81 0 0 d))
      refine this.congr fun N => ?_
      simp only [Function.comp_apply]
      rw [(dsol_trunc hA81 d g N).1, Finset.sum_apply]
    have := hs.hasSum
    rwa [tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim] at this
  · rw [Pi.hasSum]
    intro a
    have hs : Summable (fun k => (KΦ hA81 d k *ᵥ g k) a) := by
      refine Summable.of_norm_bounded (g := fun k => ∑ j, |KΦ hA81 d k a j| * B)
        (summable_sum fun j _ => (hsΦ a j).mul_right _) fun k => ?_
      rw [Real.norm_eq_abs]
      exact abs_mulVec_le _ (hB k) a
    have hlim : Tendsto (fun N => ∑ k ∈ Finset.range N, (KΦ hA81 d k *ᵥ g k) a) atTop
        (𝓝 ((solΦ hA81 0 g d - solΦ hA81 0 0 d) a)) := by
      have := ((continuous_apply a).tendsto _).comp (ht.2.sub_const (solΦ hA81 0 0 d))
      refine this.congr fun N => ?_
      simp only [Function.comp_apply]
      rw [(dsol_trunc hA81 d g N).2, Finset.sum_apply]
    have := hs.hasSum
    rwa [tendsto_nhds_unique hs.hasSum.tendsto_sum_nat hlim] at this

/-- Woodford (2003), (1.5) and (1.10): with zero forcing the solution is an affine function of the
state at every date: `y_d(n, 0) = y⁰_d + B_d n`, `φ_d(n, 0) = φ⁰_d + G_d n`. -/
theorem sol0_affine (d : ℕ) :
    ∃ (y0 : (ιZ ⊕ ιz) ⊕ Unit → ℝ) (By : Matrix ((ιZ ⊕ ιz) ⊕ Unit) (ιZ ⊕ ιz) ℝ)
      (p0 : ιZ ⊕ ιz → ℝ) (Bp : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ),
      ∀ n, solY hA81 n 0 d = y0 + By *ᵥ n ∧ solΦ hA81 n 0 d = p0 + Bp *ᵥ n := by
  obtain ⟨y0, By, hy⟩ := OptimalRulesMeasureMarkov.exists_affine_matrix
    (fun n => solY hA81 n 0 d) fun w1 w2 w3 x1 x2 x3 hw => by
      have := (sol_comb hA81 hw x1 x2 x3 (bddSeq_zero (ι := ιz)) (bddSeq_zero (ι := ιz))
        (bddSeq_zero (ι := ιz)) d).1
      simp only [smul_zero, add_zero] at this
      exact this
  obtain ⟨p0, Bp, hp⟩ := OptimalRulesMeasureMarkov.exists_affine_matrix
    (fun n => solΦ hA81 n 0 d) fun w1 w2 w3 x1 x2 x3 hw => by
      have := (sol_comb hA81 hw x1 x2 x3 (bddSeq_zero (ι := ιz)) (bddSeq_zero (ι := ιz))
        (bddSeq_zero (ι := ιz)) d).2
      simp only [smul_zero, add_zero] at this
      exact this
  exact ⟨y0, By, p0, Bp, fun n => ⟨hy n, hp n⟩⟩

end Woodford.OptimalPolicyRules.OptimalRulesMeasureKernel
