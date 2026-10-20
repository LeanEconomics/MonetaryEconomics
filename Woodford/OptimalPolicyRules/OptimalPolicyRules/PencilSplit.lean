/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralFOC
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Stable/unstable splitting of the multiplier system

Woodford (2003), *Interest and Prices*, Chapter 8, Section 1.4 (pp. 552–553) and Appendix G.1
(pp. 716–718, (G.1)–(G.9)).

Proposition 8.1 rewrites the first-order conditions (1.18) for the multipliers
`φ_t = (ξ_t, M_{t-1})` in the recursive form (1.20)–(1.21). This module supplies the two tools:

* **Vector forward solutions.** For a square matrix `G` whose powers decay geometrically
  (`PowDecay`; by Gelfand's formula this holds when every complex eigenvalue lies in the open
  unit disc, `powDecay_of_eig`), the equation `w_t = G E_t w_{t+1} + f_t` has, for bounded
  `f`, the bounded solution `fwdSum` `= ∑_k G^k E_t f_{t+k}` (`fwdSum_spec`), and it is the only
  bounded solution from any date `t₀` on (`eq_fwdSum`). Everything holds for an arbitrary
  `ExpectationSystem`.
* **The deflating (invariant) subspace.** A real `n × n_Z` matrix `J` and an `n_Z × n_Z`
  matrix `Ψ` with `A J = Î J Ψ` (Woodford's (G.4)) span the right deflating subspace of the
  pencil `(A, Î)` belonging to `n_Z` roots of (1.15). The structure `DeflatingSplit` records
  such a pair with all eigenvalues of `Ψ` in `|μ| < β⁻¹`, the top block `J₁` invertible and the
  matrix `K = A₂₂' + A₁₂' Υ` invertible. No diagonalisability is assumed: this is the
  invariant-subspace route, which avoids the eigenvector basis of Assumption 8.3.
  `eig_isRoot` shows that the eigenvalues of `Ψ` are roots of (1.15) (so `J` really selects
  `n_Z` roots with `|μ| < β⁻¹`), and `powDecay_G` gives the decay of `(β Ψ')^k`.

The vector forward solution is restated from the Woodford Chapter 5 project
(`ForwardSystems.pow_entry_bound`, `fwdVec_spec`, `fsolves_unique`), generalised from `Fin n` to
any finite index type and to equations holding only from a date `t₀` on.
-/

namespace Woodford.OptimalPolicyRules.PencilSplit

open Matrix Filter Topology GeneralSetup

variable {Ω : Type*}

/-! ### Componentwise expectations of random vectors -/

/-- Woodford (2003), p. 540: `E_t` of a sum of random vectors. -/
theorem EV_add (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (x y : Ω → ι → ℝ) :
    EV 𝔼 t (fun ω => x ω + y ω) = fun ω => EV 𝔼 t x ω + EV 𝔼 t y ω := by
  funext ω i
  change 𝔼.E t (fun ω' => x ω' i + y ω' i) ω =
    𝔼.E t (fun ω' => x ω' i) ω + 𝔼.E t (fun ω' => y ω' i) ω
  rw [show (fun ω' => x ω' i + y ω' i) = (fun ω' => x ω' i) + fun ω' => y ω' i from rfl,
    map_add]
  rfl

/-- Woodford (2003), p. 540: `E_t` of a difference of random vectors. -/
theorem EV_sub (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (x y : Ω → ι → ℝ) :
    EV 𝔼 t (fun ω => x ω - y ω) = fun ω => EV 𝔼 t x ω - EV 𝔼 t y ω := by
  funext ω i
  change 𝔼.E t (fun ω' => x ω' i - y ω' i) ω =
    𝔼.E t (fun ω' => x ω' i) ω - 𝔼.E t (fun ω' => y ω' i) ω
  rw [show (fun ω' => x ω' i - y ω' i) = (fun ω' => x ω' i) - fun ω' => y ω' i from rfl,
    map_sub]
  rfl

/-- Woodford (2003), p. 540: `E_t` of a scalar multiple of a random vector. -/
theorem EV_smul (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (c : ℝ) (x : Ω → ι → ℝ) :
    EV 𝔼 t (fun ω => c • x ω) = fun ω => c • EV 𝔼 t x ω := by
  funext ω i
  change 𝔼.E t (fun ω' => c * x ω' i) ω = c * 𝔼.E t (fun ω' => x ω' i) ω
  rw [show (fun ω' => c * x ω' i) = c • fun ω' => x ω' i from rfl, map_smul]
  rfl

/-- Woodford (2003), p. 540: a constant vector is its own conditional expectation. -/
theorem EV_const (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (v : ι → ℝ) :
    EV 𝔼 t (fun _ => v) = fun _ => v := by
  funext ω i
  exact congrFun (𝔼.const t (v i)) ω

/-- Woodford (2003), p. 540: the law of iterated expectations for random vectors,
`E_s E_t x = E_s x` for `s ≤ t`. -/
theorem EV_tower (𝔼 : ExpectationSystem Ω) {ι : Type*} {s t : ℕ} (h : s ≤ t)
    (x : Ω → ι → ℝ) : EV 𝔼 s (EV 𝔼 t x) = EV 𝔼 s x := by
  funext ω i
  exact congrFun (𝔼.tower h (fun ω' => x ω' i)) ω

/-- Woodford (2003), p. 540: `E_t x` is known at `t`. -/
theorem knownV_EV (𝔼 : ExpectationSystem Ω) {ι : Type*} (t : ℕ) (x : Ω → ι → ℝ) :
    KnownV 𝔼 t (EV 𝔼 t x) := fun i => 𝔼.tower le_rfl (fun ω' => x ω' i)

/-- Woodford (2003), p. 540: a constant matrix applied to a known vector, plus a known vector,
is known. -/
theorem knownV_mulVec_add (𝔼 : ExpectationSystem Ω) {ι κ : Type*} [Fintype ι] {t : ℕ}
    (A : Matrix κ ι ℝ) {a : Ω → ι → ℝ} {b : Ω → κ → ℝ} (ha : KnownV 𝔼 t a)
    (hb : KnownV 𝔼 t b) : KnownV 𝔼 t (fun ω => A *ᵥ a ω + b ω) := by
  intro i
  have hA := EV_mulVec 𝔼 t A a
  rw [EV_of_known 𝔼 ha] at hA
  have h := EV_add 𝔼 t (fun ω => A *ᵥ a ω) b
  rw [hA, EV_of_known 𝔼 hb] at h
  funext ω
  exact congrFun (congrFun h ω) i

/-- Woodford (2003), p. 540: a constant matrix applied to a known vector is known. -/
theorem knownV_mulVec (𝔼 : ExpectationSystem Ω) {ι κ : Type*} [Fintype ι] {t : ℕ}
    (A : Matrix κ ι ℝ) {a : Ω → ι → ℝ} (ha : KnownV 𝔼 t a) :
    KnownV 𝔼 t (fun ω => A *ᵥ a ω) := by
  intro i
  have hA := EV_mulVec 𝔼 t A a
  rw [EV_of_known 𝔼 ha] at hA
  funext ω
  exact congrFun (congrFun hA ω) i

/-- Woodford (2003), p. 540: `E_t (x + c) = E_t x + c` for a constant vector `c`. -/
theorem EV_add_const (𝔼 : ExpectationSystem Ω) {κ : Type*} (t : ℕ) (x : Ω → κ → ℝ)
    (c : κ → ℝ) : EV 𝔼 t (fun ω => x ω + c) = fun ω => EV 𝔼 t x ω + c := by
  rw [EV_add 𝔼 t x (fun _ => c), EV_const]

/-- Woodford (2003), p. 540: the sum of two known random vectors is known. -/
theorem knownV_add (𝔼 : ExpectationSystem Ω) {ι : Type*} {t : ℕ} {a b : Ω → ι → ℝ}
    (ha : KnownV 𝔼 t a) (hb : KnownV 𝔼 t b) : KnownV 𝔼 t (fun ω => a ω + b ω) := by
  intro i
  have h := EV_add 𝔼 t a b
  rw [EV_of_known 𝔼 ha, EV_of_known 𝔼 hb] at h
  funext ω
  exact congrFun (congrFun h ω) i

/-- Woodford (2003), p. 556: `∑_{j < n} B_j q_{t−j}` is known at `t` for adapted `q`. -/
theorem knownV_sum_mulVec (𝔼 : ExpectationSystem Ω) {ι : Type*} [Fintype ι]
    (B : ℕ → Matrix ι ι ℝ) {q : ℕ → Ω → ι → ℝ} (hq : AdaptedV 𝔼 q) (t : ℕ) :
    ∀ n, KnownV 𝔼 t (fun ω => ∑ j ∈ Finset.range n, B j *ᵥ q (t - j) ω) := by
  intro n
  induction n with
  | zero =>
    intro r
    simpa using 𝔼.const t 0
  | succ n ih =>
    have e : (fun ω => ∑ j ∈ Finset.range (n + 1), B j *ᵥ q (t - j) ω) =
        fun ω => B n *ᵥ q (t - n) ω + ∑ j ∈ Finset.range n, B j *ᵥ q (t - j) ω := by
      funext ω
      rw [Finset.sum_range_succ, add_comm]
    rw [e]
    exact knownV_mulVec_add 𝔼 (B n) (KnownV.mono 𝔼 (Nat.sub_le t n) (hq (t - n))) ih

/-- Woodford (2003), fn 6, p. 539: a constant matrix maps bounded vector processes to bounded
vector processes. -/
theorem boundedV_mulVec {ι κ : Type*} [Fintype ι] [Finite κ] (A : Matrix κ ι ℝ)
    {x : ℕ → Ω → ι → ℝ} (hx : BoundedV x) : BoundedV (fun t ω => A *ᵥ x t ω) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨K, hK⟩ := GeneralFOC.exists_bound_mulVec A M
  exact ⟨K, fun t ω i => hK _ (hM t ω) i⟩

/-- Woodford (2003), fn 6, p. 539: sums of bounded vector processes are bounded. -/
theorem boundedV_add {ι : Type*} {x y : ℕ → Ω → ι → ℝ} (hx : BoundedV x) (hy : BoundedV y) :
    BoundedV (fun t ω => x t ω + y t ω) := by
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hy
  exact ⟨M + N, fun t ω i => (abs_add_le _ _).trans (add_le_add (hM t ω i) (hN t ω i))⟩

/-- Woodford (2003), fn 6, p. 539: the conditional expectation of a bounded vector process is
bounded by the same bound. -/
theorem abs_EV_le (𝔼 : ExpectationSystem Ω) {ι : Type*} {x : Ω → ι → ℝ} {M : ℝ}
    (hx : ∀ ω i, |x ω i| ≤ M) (t : ℕ) (ω : Ω) (i : ι) : |EV 𝔼 t x ω i| ≤ M :=
  𝔼.abs_E_le (fun ω' => hx ω' i) t ω

/-! ### Geometric decay of matrix powers -/

/-- Woodford (2003), App. G.1, p. 717 (`|μᵢ| < β⁻¹` for the eigenvalues of `Ψ`, (G.4)–(G.5)):
the powers of `G` decay geometrically, `|(Gᵏ)ᵢⱼ| ≤ C rᵏ` with `0 ≤ r < 1`. -/
def PowDecay {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) : Prop :=
  ∃ C r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ k i j, |(G ^ k) i j| ≤ C * r ^ k

/-- Woodford (2003), App. G.1, p. 717 (restated from the Woodford Chapter 5 project,
`ForwardSystems.pow_entry_bound`, for any finite index type): if every complex eigenvalue of a
real square matrix lies in the open unit disc, its powers decay geometrically (Gelfand's
spectral radius formula). -/
theorem powDecay_of_eig {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Matrix ι ι ℝ)
    (h : ∀ w : ℂ, (Matrix.scalar ι w - K.map Complex.ofReal).det = 0 → ‖w‖ < 1) :
    PowDecay K := by
  have hpow : ∀ k, ((K ^ k).map Complex.ofReal) = (K.map Complex.ofReal) ^ k := fun k =>
    (Complex.ofRealHom.mapMatrix.map_pow K k)
  let _ : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  set A : Matrix ι ι ℂ := K.map Complex.ofReal with hA
  have hspec : ∀ w ∈ spectrum ℂ A, w ∈ A.charpoly.roots.toFinset ∧ ‖w‖ < 1 := by
    intro w hw
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hw
    refine ⟨?_, h w ?_⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero]
      exact hw
    · rw [← Matrix.eval_charpoly]; exact hw
  set ρ0 : NNReal := A.charpoly.roots.toFinset.sup (fun w => ‖w‖₊) with hρ0
  have hρ0lt : ρ0 < 1 := by
    rw [hρ0, Finset.sup_lt_iff (by norm_num)]
    intro w hw
    have hw' : w ∈ spectrum ℂ A := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero] at hw
      exact hw
    have := (hspec w hw').2
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    simpa using this
  have hsr : spectralRadius ℂ A ≤ (ρ0 : ENNReal) := by
    refine iSup₂_le fun w hw => ?_
    rw [quasispectrum_eq_spectrum_union_zero] at hw
    rcases hw with hw | hw
    · exact ENNReal.coe_le_coe.mpr (Finset.le_sup (f := fun w => ‖w‖₊) (hspec w hw).1)
    · rw [Set.mem_singleton_iff] at hw
      subst hw
      simp
  set r : ℝ := ((ρ0 : ℝ) + 1) / 2 with hr
  have hρ0r : (ρ0 : ℝ) < r := by
    have : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
    rw [hr]; linarith
  have hr1 : r < 1 := by
    have : (ρ0 : ℝ) < 1 := by exact_mod_cast hρ0lt
    rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt ρ0.coe_nonneg hρ0r
  have hlt : spectralRadius ℂ A < ENNReal.ofReal r := by
    refine lt_of_le_of_lt hsr ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).mpr hρ0r
  have hev := (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius A).eventually_lt_const
    hlt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hbig : ∀ k ≥ N + 1, ‖A ^ k‖ ≤ r ^ k := by
    intro k hk
    have h1 := hN k (by omega)
    rw [ENNReal.ofReal_lt_ofReal_iff hr0] at h1
    have hk0 : k ≠ 0 := by omega
    have h2 : (‖A ^ k‖ ^ (1 / k : ℝ)) ^ k = ‖A ^ k‖ := by
      rw [one_div]; exact Real.rpow_inv_natCast_pow (norm_nonneg _) hk0
    rw [← h2]
    exact (pow_lt_pow_left₀ h1 (Real.rpow_nonneg (norm_nonneg _) _) hk0).le
  set Cb : ℝ := 1 + ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k with hCb
  have hall : ∀ k, ‖A ^ k‖ ≤ Cb * r ^ k := by
    intro k
    by_cases hk : k ≤ N
    · have hmem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
      have hle : ‖A ^ k‖ / r ^ k ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
        Finset.single_le_sum (f := fun k => ‖A ^ k‖ / r ^ k)
          (fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)) hmem
      have hrk : 0 < r ^ k := pow_pos hr0 k
      have : ‖A ^ k‖ = ‖A ^ k‖ / r ^ k * r ^ k := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hrk.le
    · have := hbig k (by omega)
      have hrk : 0 ≤ r ^ k := pow_nonneg hr0.le k
      have hs : 0 ≤ ∑ k ∈ Finset.range (N + 1), ‖A ^ k‖ / r ^ k :=
        Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
      nlinarith
  refine ⟨Cb, r, hr0.le, hr1, fun k i j => ?_⟩
  have hentry : |(K ^ k) i j| = ‖(A ^ k) i j‖ := by
    have e : (A ^ k) i j = ((K ^ k) i j : ℂ) := by
      have := congrFun (congrFun (hpow k) i) j
      exact this.symm
    rw [e, Complex.norm_real, Real.norm_eq_abs]
  rw [hentry]
  refine le_trans ?_ (hall k)
  rw [Matrix.linfty_opNorm_def]
  have h1 : ‖(A ^ k) i j‖₊ ≤ ∑ j, ‖(A ^ k) i j‖₊ :=
    Finset.single_le_sum (f := fun j => ‖(A ^ k) i j‖₊) (fun _ _ => by positivity)
      (Finset.mem_univ j)
  have h2 : ∑ j, ‖(A ^ k) i j‖₊ ≤ Finset.univ.sup fun i => ∑ j, ‖(A ^ k) i j‖₊ :=
    Finset.le_sup (f := fun i => ∑ j, ‖(A ^ k) i j‖₊) (Finset.mem_univ i)
  have := h1.trans h2
  rw [← coe_nnnorm]
  exact_mod_cast this

/-- Woodford (2003), App. G.1, p. 717: the bound for `Gᵏ` acting on a bounded vector,
`|(Gᵏ v)ᵢ| ≤ n C rᵏ M`. -/
theorem abs_mulVec_pow_le {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℝ}
    {C r : ℝ} (hG : ∀ k i j, |(G ^ k) i j| ≤ C * r ^ k) (k : ℕ) {v : ι → ℝ} {M : ℝ}
    (hv : ∀ j, |v j| ≤ M) (i : ι) : |(G ^ k *ᵥ v) i| ≤ Fintype.card ι * (C * r ^ k * M) := by
  calc |(G ^ k *ᵥ v) i| = |∑ j, (G ^ k) i j * v j| := rfl
    _ ≤ ∑ j, |(G ^ k) i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : ι, C * r ^ k * M := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hG k i j) (hv j) (abs_nonneg _) ((abs_nonneg _).trans (hG k i j))
    _ = Fintype.card ι * (C * r ^ k * M) := by simp

/-! ### Vector forward solutions `w_t = G E_t w_{t+1} + f_t` -/

/-- Woodford (2003), p. 553 (the operators `E_t Q(L⁻¹)`, `E_t R(L⁻¹)` of Proposition 8.1) and
App. G.1: the forward series `∑_{k ≥ 0} Gᵏ E_t f_{t+k}`. -/
noncomputable def fwdSum (𝔼 : ExpectationSystem Ω) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (f : ℕ → Ω → ι → ℝ) (t : ℕ) : Ω → ι → ℝ :=
  fun ω i => ∑' k, (G ^ k *ᵥ EV 𝔼 t (f (t + k)) ω) i

/-- Woodford (2003), p. 553 and App. G.1 (restated from the Woodford Chapter 5 project,
`ForwardSystems.fwdVec_spec`): if the powers of `G` decay geometrically and `f` is bounded,
the forward series is a bounded adapted solution of `w_t = G E_t w_{t+1} + E_t f_t`. -/
theorem fwdSum_spec (𝔼 : ExpectationSystem Ω) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : PowDecay G) {f : ℕ → Ω → ι → ℝ} (hf : BoundedV f) :
    (∀ t ω, fwdSum 𝔼 G f t ω = G *ᵥ EV 𝔼 t (fwdSum 𝔼 G f (t + 1)) ω + EV 𝔼 t (f t) ω) ∧
      AdaptedV 𝔼 (fwdSum 𝔼 G f) ∧ BoundedV (fwdSum 𝔼 G f) := by
  obtain ⟨C, r, hr0, hr1, hGb⟩ := hG
  obtain ⟨Mf, hMf⟩ := hf
  set Mb : ℝ := Fintype.card ι * C * Mf with hMb
  set B : ℕ → ℕ → ι → Ω → ℝ := fun k t i ω => (G ^ k *ᵥ EV 𝔼 t (f (t + k)) ω) i with hB
  have hT : ∀ k t t' i ω, |(G ^ k *ᵥ EV 𝔼 t (f t') ω) i| ≤ r ^ k * Mb := by
    intro k t t' i ω
    have := abs_mulVec_pow_le hGb k (fun j => abs_EV_le 𝔼 (hMf t') t ω j) i
    calc _ ≤ Fintype.card ι * (C * r ^ k * Mf) := this
      _ = r ^ k * Mb := by rw [hMb]; ring
  have hTs : ∀ (t t' : ℕ → ℕ) i ω,
      Summable fun k => (G ^ k *ᵥ EV 𝔼 (t k) (f (t' k)) ω) i := fun t t' i ω =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_right Mb)
      (fun k => by rw [Real.norm_eq_abs]; exact hT k (t k) (t' k) i ω)
  have hBb : ∀ k t i ω, |B k t i ω| ≤ r ^ k * Mb := fun k t i ω => hT k t (t + k) i ω
  have hsum : ∀ t i ω, Summable fun k => B k t i ω := fun t i ω =>
    hTs (fun _ => t) (fun k => t + k) i ω
  have hEB : ∀ k t i, 𝔼.E t (B k (t + 1) i) =
      fun ω => (G ^ k *ᵥ EV 𝔼 t (f (t + 1 + k)) ω) i := by
    intro k t i
    funext ω
    change EV 𝔼 t (fun ω' => G ^ k *ᵥ EV 𝔼 (t + 1) (f (t + 1 + k)) ω') ω i = _
    rw [EV_mulVec, EV_tower 𝔼 (Nat.le_succ t)]
  have hEs : ∀ t i ω, EV 𝔼 t (fwdSum 𝔼 G f (t + 1)) ω i =
      ∑' k, (G ^ k *ᵥ EV 𝔼 t (f (t + 1 + k)) ω) i := by
    intro t i ω
    have := 𝔼.E_tsum hr0 hr1 (f := fun k => B k (t + 1) i) (fun k ω => hBb k (t + 1) i ω) t ω
    change 𝔼.E t (fun ω' => ∑' k, B k (t + 1) i ω') ω = _
    rw [this]
    exact tsum_congr fun k => by rw [hEB]
  refine ⟨?_, ?_, ?_⟩
  · intro t ω
    funext i
    have hB0 : B 0 t i ω = EV 𝔼 t (f t) ω i := by
      simp only [hB, pow_zero, add_zero, one_mulVec]
    have hshift : ∀ k, B (k + 1) t i ω =
        ∑ l, G i l * (G ^ k *ᵥ EV 𝔼 t (f (t + 1 + k)) ω) l := by
      intro k
      simp only [hB]
      rw [pow_succ', ← mulVec_mulVec, show t + (k + 1) = t + 1 + k by omega]
      rfl
    have hR : (G *ᵥ EV 𝔼 t (fwdSum 𝔼 G f (t + 1)) ω + EV 𝔼 t (f t) ω) i =
        (∑' k, B (k + 1) t i ω) + EV 𝔼 t (f t) ω i := by
      rw [Pi.add_apply]
      congr 1
      change ∑ l, G i l * EV 𝔼 t (fwdSum 𝔼 G f (t + 1)) ω l = _
      simp only [hEs, ← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (fun l _ =>
        (hTs (fun _ => t) (fun k => t + 1 + k) l ω).mul_left (G i l))]
      exact tsum_congr fun k => (hshift k).symm
    rw [hR, show fwdSum 𝔼 G f t ω i = ∑' k, B k t i ω from rfl, (hsum t i ω).tsum_eq_zero_add,
      hB0]
    ring
  · intro t i
    funext ω
    have := 𝔼.E_tsum hr0 hr1 (f := fun k => B k t i) (fun k ω => hBb k t i ω) t ω
    change 𝔼.E t (fun ω' => ∑' k, B k t i ω') ω = ∑' k, B k t i ω
    rw [this]
    refine tsum_congr fun k => ?_
    change EV 𝔼 t (fun ω' => G ^ k *ᵥ EV 𝔼 t (f (t + k)) ω') ω i = _
    rw [EV_mulVec, EV_tower 𝔼 le_rfl]
  · refine ⟨Mb / (1 - r), fun t ω i => ?_⟩
    have hg : HasSum (fun k : ℕ => r ^ k * Mb) (Mb / (1 - r)) := by
      have := (hasSum_geometric_of_lt_one hr0 hr1).mul_right Mb
      rwa [← div_eq_inv_mul] at this
    have := tsum_of_norm_bounded hg (f := fun k => B k t i ω)
      (fun k => by rw [Real.norm_eq_abs]; exact hBb k t i ω)
    rw [Real.norm_eq_abs] at this
    exact this

/-- Woodford (2003), p. 553 and App. G.1 (restated from the Woodford Chapter 5 project,
`ForwardSystems.fsolves_unique`, from a date `t₀` on): if the powers of `G` decay
geometrically, `f` is bounded and known at each date, and the bounded process `w` satisfies
`w_t = G E_t w_{t+1} + f_t` for all `t ≥ t₀`, then `w_t` is the forward series for every
`t ≥ t₀`. (`w` itself need not be adapted.) -/
theorem eq_fwdSum (𝔼 : ExpectationSystem Ω) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {G : Matrix ι ι ℝ} (hG : PowDecay G) {f w : ℕ → Ω → ι → ℝ} (hf : BoundedV f)
    (hw : BoundedV w) {t0 : ℕ} (hfk : ∀ t, t0 ≤ t → KnownV 𝔼 t (f t))
    (heq : ∀ t, t0 ≤ t → ∀ ω, w t ω = G *ᵥ EV 𝔼 t (w (t + 1)) ω + f t ω) :
    ∀ t, t0 ≤ t → w t = fwdSum 𝔼 G f t := by
  obtain ⟨hF, -, hFb⟩ := fwdSum_spec 𝔼 hG hf
  obtain ⟨C, r, hr0, hr1, hGb⟩ := hG
  set F := fwdSum 𝔼 G f with hFdef
  set d : ℕ → Ω → ι → ℝ := fun t ω => w t ω - F t ω with hd
  have hdrec : ∀ t, t0 ≤ t → ∀ ω, d t ω = G *ᵥ EV 𝔼 t (d (t + 1)) ω := by
    intro t ht ω
    simp only [hd]
    rw [EV_sub, heq t ht ω, hF t ω, EV_of_known 𝔼 (hfk t ht), mulVec_sub]
    abel
  have hiter : ∀ k t, t0 ≤ t → ∀ ω, d t ω = G ^ (k + 1) *ᵥ EV 𝔼 t (d (t + k + 1)) ω := by
    intro k
    induction k with
    | zero =>
      intro t ht ω
      rw [zero_add, pow_one, add_zero]
      exact hdrec t ht ω
    | succ k ih =>
      intro t ht ω
      rw [ih t ht ω]
      have hfun : d (t + k + 1) = fun ω' => G *ᵥ EV 𝔼 (t + k + 1) (d (t + k + 1 + 1)) ω' :=
        funext fun ω' => hdrec (t + k + 1) (by omega) ω'
      rw [hfun, EV_mulVec, EV_tower 𝔼 (by omega), mulVec_mulVec, ← pow_succ,
        show t + k + 1 + 1 = t + (k + 1) + 1 by omega]
  obtain ⟨Mw, hMw⟩ := hw
  obtain ⟨MF, hMF⟩ := hFb
  have hdb : ∀ t ω i, |d t ω i| ≤ Mw + MF := fun t ω i =>
    (abs_sub _ _).trans (add_le_add (hMw t ω i) (hMF t ω i))
  intro t ht
  funext ω i
  have hle : ∀ k, |d t ω i| ≤ Fintype.card ι * (C * r ^ (k + 1) * (Mw + MF)) := by
    intro k
    rw [hiter k t ht ω]
    exact abs_mulVec_pow_le hGb (k + 1) (fun j => abs_EV_le 𝔼 (hdb (t + k + 1)) t ω j) i
  have hlim : Tendsto (fun k : ℕ => (Fintype.card ι : ℝ) * (C * r ^ (k + 1) * (Mw + MF)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => r ^ (k + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp (tendsto_add_atTop_nat 1)
    have := ((h1.const_mul C).mul_const (Mw + MF)).const_mul (Fintype.card ι : ℝ)
    simpa using this
  have h0 : |d t ω i| ≤ 0 := ge_of_tendsto' hlim hle
  have : d t ω i = 0 := abs_nonpos_iff.mp h0
  simp only [hd, Pi.sub_apply] at this
  linarith

/-! ### The deflating subspace (G.4) and the matrices of Proposition 8.1 -/

variable {ιZ ιz : Type*} [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz]

/-- Woodford (2003), App. G.1, p. 718 (Assumption 8.4 (ii)): the top block `J₁` of `J` (the rows
belonging to the predetermined variables `Z`); `n_Z × n_Z` for the `J` of (G.4), and for any
column type (the `J⁺` of case (ii)). -/
def J1 {ιc : Type*} (J : Matrix (ιZ ⊕ ιz) ιc ℝ) : Matrix ιZ ιc ℝ := J.submatrix Sum.inl id

/-- Woodford (2003), App. G.1, p. 718: the bottom block `J₂` of `J` (the rows belonging to the
forward-looking variables `z`), for any column type. -/
def J2 {ιc : Type*} (J : Matrix (ιZ ⊕ ιz) ιc ℝ) : Matrix ιz ιc ℝ := J.submatrix Sum.inr id

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1, p. 718: `J₁(JP) = J₁(J)P` (a change of basis acts on the blocks). -/
theorem J1_mul {ιc κ : Type*} [Fintype ιc] (J : Matrix (ιZ ⊕ ιz) ιc ℝ) (P : Matrix ιc κ ℝ) :
    J1 (J * P) = J1 J * P := by
  ext a b
  simp [J1, mul_apply]

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1, p. 718: `J₂(JP) = J₂(J)P`. -/
theorem J2_mul {ιc κ : Type*} [Fintype ιc] (J : Matrix (ιZ ⊕ ιz) ιc ℝ) (P : Matrix ιc κ ℝ) :
    J2 (J * P) = J2 J * P := by
  ext a b
  simp [J2, mul_apply]

/-- Woodford (2003), eq. (1.21), p. 553: the matrix `Υ = −(J₁')⁻¹ J₂' Ẽ'`, so that
`J' Î' φ_t = J₁' ξ_t + J₂' Ẽ' M_{t-1}` determines `ξ_t = Υ M_{t-1} + r_t`. -/
noncomputable def Υmat (S : LinearRESystem ιZ ιz) (J : Matrix (ιZ ⊕ ιz) ιZ ℝ) :
    Matrix ιZ ιz ℝ :=
  -(((J1 J)ᵀ)⁻¹ * (J2 J)ᵀ * S.Etᵀ)

/-- Woodford (2003), eq. (1.20), p. 553: the matrix `K = A₂₂' + A₁₂' Υ` multiplying `M_t` in the
`z`-rows of (1.18) once `ξ_{t+1}` is replaced by (1.21). -/
noncomputable def Kmat (S : LinearRESystem ιZ ιz) (J : Matrix (ιZ ⊕ ιz) ιZ ℝ) :
    Matrix ιz ιz ℝ :=
  S.A22ᵀ + S.A12ᵀ * Υmat S J

/-- Woodford (2003), eq. (1.20), p. 553: the matrix `Λ = β⁻¹ K⁻¹ Ẽ'` of the multiplier recursion
`M_t = Λ M_{t-1} + q_t`. -/
noncomputable def Λmat (S : LinearRESystem ιZ ιz) (β : ℝ) (J : Matrix (ιZ ⊕ ιz) ιZ ℝ) :
    Matrix ιz ιz ℝ :=
  β⁻¹ • ((Kmat S J)⁻¹ * S.Etᵀ)

/-- Woodford (2003), App. G.1, pp. 717–718, (G.4) with Assumptions 8.2 and 8.4: a real
right deflating subspace for `n_Z` roots of (1.15) inside `|μ| < β⁻¹`. The columns of the
`n × n_Z` matrix `J` span a subspace with `A J = Î J Ψ`; every eigenvalue of `Ψ` satisfies
`|μ| < β⁻¹`; the block `J₁` is invertible (the role of Assumption 8.4 (ii)); and
`K = A₂₂' + A₁₂' Υ` is invertible (the role of Assumption 8.4 (i)). No diagonalisability is
required. -/
structure DeflatingSplit (S : LinearRESystem ιZ ιz) (β : ℝ) where
  J : Matrix (ιZ ⊕ ιz) ιZ ℝ
  Ψ : Matrix ιZ ιZ ℝ
  deflate : S.Ahat * J = S.Ihat * J * Ψ
  eig_lt : ∀ μ : ℂ, (Matrix.scalar ιZ μ - Ψ.map Complex.ofReal).det = 0 → ‖μ‖ < β⁻¹
  J1_det : (J1 J).det ≠ 0
  K_det : (Kmat S J).det ≠ 0

omit [DecidableEq ιZ] in
/-- Woodford (2003), (1.18), p. 552: block form of `A' v`. -/
theorem Ahat_transpose_mulVec (S : LinearRESystem ιZ ιz) (v : ιZ ⊕ ιz → ℝ) :
    S.Ahatᵀ *ᵥ v = Sum.elim (S.A11ᵀ *ᵥ (v ∘ Sum.inl) + S.A21ᵀ *ᵥ (v ∘ Sum.inr))
      (S.A12ᵀ *ᵥ (v ∘ Sum.inl) + S.A22ᵀ *ᵥ (v ∘ Sum.inr)) := by
  rw [LinearRESystem.Ahat, fromBlocks_transpose, fromBlocks_mulVec]

/-- Woodford (2003), (1.18), p. 552: block form of `Î' v`. -/
theorem Ihat_transpose_mulVec (S : LinearRESystem ιZ ιz) (v : ιZ ⊕ ιz → ℝ) :
    S.Ihatᵀ *ᵥ v = Sum.elim (v ∘ Sum.inl) (S.Etᵀ *ᵥ (v ∘ Sum.inr)) := by
  rw [LinearRESystem.Ihat, fromBlocks_transpose, fromBlocks_mulVec]
  simp

omit [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1: block form of `J' v = J₁' v_Z + J₂' v_z` (any column type). -/
theorem J_transpose_mulVec {ιc : Type*} (J : Matrix (ιZ ⊕ ιz) ιc ℝ) [Fintype ιz]
    (v : ιZ ⊕ ιz → ℝ) :
    Jᵀ *ᵥ v = (J1 J)ᵀ *ᵥ (v ∘ Sum.inl) + (J2 J)ᵀ *ᵥ (v ∘ Sum.inr) := by
  funext j
  simp [mulVec, dotProduct, Fintype.sum_sum_type, J1, J2]

/-- Woodford (2003), (G.4) transposed: `J' A' v = Ψ' J' Î' v`. -/
theorem deflate_transpose {S : LinearRESystem ιZ ιz} {J : Matrix (ιZ ⊕ ιz) ιZ ℝ}
    {Ψ : Matrix ιZ ιZ ℝ} (h : S.Ahat * J = S.Ihat * J * Ψ) (v : ιZ ⊕ ιz → ℝ) :
    Jᵀ *ᵥ (S.Ahatᵀ *ᵥ v) = Ψᵀ *ᵥ (Jᵀ *ᵥ (S.Ihatᵀ *ᵥ v)) := by
  have ht : Jᵀ * S.Ahatᵀ = Ψᵀ * (Jᵀ * S.Ihatᵀ) := by
    rw [← transpose_mul, h, transpose_mul, transpose_mul]
  rw [mulVec_mulVec, ht, ← mulVec_mulVec, ← mulVec_mulVec]

/-- Woodford (2003), eq. (1.15), p. 546: the characteristic polynomial evaluated at `μ` is
`det (A − μ Î)` (over `ℂ`). -/
theorem pencilPoly_eval (S : LinearRESystem ιZ ιz) (μ : ℂ) :
    S.pencilPoly.eval μ =
      (S.Ahat.map Complex.ofReal - μ • S.Ihat.map Complex.ofReal).det := by
  rw [LinearRESystem.pencilPoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    Polynomial.coe_evalRingHom, Polynomial.eval_sub, Polynomial.eval_C, smul_eq_mul,
    Polynomial.eval_mul, Polynomial.eval_X]

/-- Woodford (2003), App. G.1, p. 717 ((G.4): "the eigenvalues of `Ψ` are the associated
eigenvalues"): every eigenvalue of `Ψ` is a root of the characteristic polynomial (1.15), so a
`DeflatingSplit` selects `n_Z` roots of (1.15), all with `|μ| < β⁻¹`. -/
theorem DeflatingSplit.eig_isRoot {S : LinearRESystem ιZ ιz} {β : ℝ}
    (D : DeflatingSplit S β) {μ : ℂ}
    (h : (Matrix.scalar ιZ μ - D.Ψ.map Complex.ofReal).det = 0) : S.pencilPoly.eval μ = 0 := by
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr h
  set X := D.Ψ.map Complex.ofReal with hX
  set Jc := D.J.map Complex.ofReal with hJc
  have hXv : X *ᵥ v = μ • v := by
    rw [sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    funext i
    simp [Matrix.scalar_apply, mulVec_diagonal]
  have hAJ : S.Ahat.map Complex.ofReal * Jc = S.Ihat.map Complex.ofReal * Jc * X := by
    ext i j
    have e := congrArg (fun M : Matrix (ιZ ⊕ ιz) ιZ ℝ => ((M i j : ℝ) : ℂ)) D.deflate
    simp only [Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul] at e
    simp only [hJc, hX, Matrix.mul_apply, Matrix.map_apply]
    exact e
  rw [pencilPoly_eval]
  refine exists_mulVec_eq_zero_iff.mp ⟨Jc *ᵥ v, fun h0 => hv0 ?_, ?_⟩
  · have hJ1 : (J1 D.J).map Complex.ofReal *ᵥ v = 0 := by
      funext i
      have := congrFun h0 (Sum.inl i)
      simpa [mulVec, dotProduct, J1, hJc] using this
    have hdet : ((J1 D.J).map Complex.ofReal).det ≠ 0 := by
      have e := Complex.ofRealHom.map_det (J1 D.J)
      rw [RingHom.mapMatrix_apply] at e
      change ((J1 D.J).det : ℂ) = ((J1 D.J).map Complex.ofReal).det at e
      rw [← e]
      exact_mod_cast D.J1_det
    exact eq_zero_of_mulVec_eq_zero hdet hJ1
  · rw [sub_mulVec, mulVec_mulVec, hAJ, ← mulVec_mulVec, hXv, smul_mulVec, mulVec_smul,
      mulVec_mulVec, sub_self]

/-- Woodford (2003), App. G.1, p. 717 and (1.20)–(1.21): the powers of `β Ψ'` decay
geometrically, since every eigenvalue of `Ψ` has `|μ| < β⁻¹` (`β > 0`). -/
theorem DeflatingSplit.powDecay_G {S : LinearRESystem ιZ ιz} {β : ℝ} (D : DeflatingSplit S β)
    (hβ : 0 < β) : PowDecay (β • D.Ψᵀ) := by
  refine powDecay_of_eig _ fun w hw => ?_
  set X := D.Ψ.map Complex.ofReal with hX
  have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
  have hmap : (β • D.Ψᵀ).map Complex.ofReal = (β : ℂ) • Xᵀ := by
    ext i j
    simp [hX]
  have hsc : Matrix.scalar ιZ w - (β : ℂ) • Xᵀ =
      ((β : ℂ) • (Matrix.scalar ιZ (w / β) - X))ᵀ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply]
      field_simp
    · simp [Matrix.scalar_apply, hij, Ne.symm hij]
  rw [hmap, hsc, det_transpose, det_smul] at hw
  have hd : (Matrix.scalar ιZ (w / β) - X).det = 0 := by
    rcases mul_eq_zero.mp hw with h | h
    · exact absurd h (pow_ne_zero _ hβc)
    · exact h
  have hlt := D.eig_lt (w / β) hd
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ] at hlt
  rw [div_lt_iff₀ hβ, inv_mul_cancel₀ hβ.ne'] at hlt
  exact hlt

end Woodford.OptimalPolicyRules.PencilSplit
