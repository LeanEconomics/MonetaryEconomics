/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.Prop81General

/-!
# Proposition 8.2 without the stability hypothesis

Woodford (2003), *Interest and Prices*, Chapter 8, Section 1.4, Proposition 8.2 (pp. 554–555,
(1.23)–(1.27)), with Assumption 8.5 (App. G.2, p. 719).

`TargetCriterion.Prop82` proved Proposition 8.2 conditional on Proposition 8.1 *and* on an
extra hypothesis `MultStable` (the multiplier recursion (1.20) maps bounded forcing to bounded
paths), which fails in the book's own examples: when (1.15) has more than `n_Z` roots with
`|μ| < β⁻¹` (Assumption 8.7, implied by the Sargent–Wallace property) `Λ` has an eigenvalue
outside the unit circle (`PencilAssumptions.not_multStable_of_unselected`). This module removes
it. The multiplier path built from
(1.20) also satisfies (1.19), `B₂' M_t = −v_t`, and Assumption 8.5 (the vectors `B₂'Λʲ`,
`j = 1, …, k`, are independent, so they span the row space of `Λ`) makes `Λ M_t` a fixed linear
function of `B₂' M_{t+1}, …, B₂' M_{t+k}` and the `q`'s, all bounded (`boundedV_of_krylov`). So
Assumption 8.5 — which Proposition 8.2 assumes anyway — is what keeps the multipliers bounded.

## Main results

* `krylov_factor`, `boundedV_of_krylov`: observability of `(Λ, B₂')` under Assumption 8.5.
* `focSystem_of_criterionM`: a bounded feasible plan satisfying (1.23) from `t₀` on solves
  (1.1) + (1.9) with the initial multipliers recovered from the history.
* `FOCSolvableM`, `Assumption81M`, `Assumption81M.of_assumption81`: Assumption 8.1 with the
  initial multiplier `M_{t₀−1}` bounded and known at `t₀ − 1` (implied by
  `GeneralFOC.LQ.Assumption81`, which can fail under uncertainty for every problem,
  `NKAssumption81.not_assumption81_coin`).
* `prop82M_exists`, `prop82M_unique`, `prop82M_determinate`, `prop82M_optimal`: Proposition 8.2
  from the corrected Proposition 8.1 (`Prop81General.Prop81ConclusionM`) and Assumptions 8.1
  (corrected, `Assumption81M`) and 8.5 only.
* `gRule`, `multiplier_rule`, `prop82M_multiplier_rule`: the initial-multiplier rule (1.17) is
  an explicit time-invariant linear function `g` of the predetermined state (1.24)
  (`q_{t-1}, …, q_{t-D}, v_{t-1}, …, v_{t-D}`), and in the equilibrium `M_{t-1} = g(Z̄_t)` holds at
  every date `t ≥ t₀`, not only at `t₀`: the self-consistency that makes the plan optimal from a
  timeless perspective.
* `prop82M_robustlyOptimal`: commitment to (1.23) is robustly optimal in the sense of
  `GeneralSetup.RobustlyOptimal` (every bounded adapted disturbance process and every initial
  condition).
* `prop82_of_split`: everything for the explicit `Λ` of `Prop81General.prop81`.
-/

namespace Woodford.OptimalPolicyRules.Prop82General

open Matrix GeneralSetup GeneralFOC GeneralFOC.LQ PencilSplit Prop81General Adjugate
open TargetCriterion.Lag TargetCriterion.Crit TargetCriterion.Krylov TargetCriterion.Recursion
  TargetCriterion.Prop81 TargetCriterion.Prop82

variable {Ω : Type*}

/-! ### Observability of `(Λ, B₂')` under Assumption 8.5 -/

namespace KrylovBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Woodford (2003), Assumption 8.5 (App. G.2, p. 719): the vectors `B₂'Λʲ`, `j = 1, …, k`,
span the row space of `Λ` (`k = rank Λ`), so `Λ w = C (B₂'Λ w, …, B₂'Λᵏ w)` for a fixed
matrix `C`. -/
theorem krylov_factor {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ} (h85 : Assumption85b Λ B2) :
    ∃ C : Matrix ι (Fin Λ.rank) ℝ,
      ∀ w, Λ *ᵥ w = C *ᵥ fun j => (B2 ᵥ* Λ ^ (j.val + 1)) ⬝ᵥ w := by
  set R := LinearMap.range Λᵀ.mulVecLin with hR
  set S := Submodule.span ℝ (Set.range (fun j : Fin Λ.rank => B2 ᵥ* Λ ^ (j.val + 1))) with hS
  have hSR : S ≤ R := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨B2 ᵥ* Λ ^ j.val, ?_⟩
    rw [mulVecLin_apply, mulVec_transpose, vecMul_vecMul, ← pow_succ]
  have hrank : Module.finrank ℝ R = Λ.rank := by
    rw [hR]
    exact rank_transpose Λ
  have hSfin : Module.finrank ℝ S = Λ.rank := by
    rw [hS, finrank_span_eq_card h85, Fintype.card_fin]
  have hSeq : S = R := Submodule.eq_of_le_of_finrank_eq hSR (by rw [hSfin, hrank])
  have hrow : ∀ i, Λ i ∈ S := by
    intro i
    rw [hSeq]
    refine ⟨Pi.single i 1, ?_⟩
    rw [mulVecLin_apply, mulVec_single_one]
    rfl
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hrow i)
  refine ⟨Matrix.of fun i j => c i j, fun w => ?_⟩
  funext i
  change Λ i ⬝ᵥ w = ∑ j, c i j * ((B2 ᵥ* Λ ^ (j.val + 1)) ⬝ᵥ w)
  rw [← hc i, dotProduct_comm, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm]

/-- Woodford (2003), eq. (1.20): iterating `m_s = Λ m_{s-1} + q_s` over `t + 1, …, t + n`,
`m_{t+n} = Λⁿ m_t + ∑_{i<n} Λ^{n-1-i} q_{t+1+i}`. -/
theorem iterate_rec {Λ : Matrix ι ι ℝ} {m q : ℕ → ι → ℝ} {t n : ℕ}
    (h : ∀ j, 1 ≤ j → j ≤ n → m (t + j) = Λ *ᵥ m (t + j - 1) + q (t + j)) :
    m (t + n) = Λ ^ n *ᵥ m t + ∑ i ∈ Finset.range n, Λ ^ (n - 1 - i) *ᵥ q (t + 1 + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [h (n + 1) (by omega) le_rfl, show t + (n + 1) - 1 = t + n by omega,
      ih fun j hj1 hjn => h j hj1 (by omega), Finset.sum_range_succ, mulVec_add, mulVec_sum,
      mulVec_mulVec, ← pow_succ']
    have hs : ∑ i ∈ Finset.range n, Λ *ᵥ (Λ ^ (n - 1 - i) *ᵥ q (t + 1 + i)) =
        ∑ i ∈ Finset.range n, Λ ^ (n + 1 - 1 - i) *ᵥ q (t + 1 + i) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      rw [mulVec_mulVec, ← pow_succ', show n - 1 - i + 1 = n + 1 - 1 - i by omega]
    rw [hs, show n + 1 - 1 - n = 0 by omega, pow_zero, one_mulVec,
      show t + (n + 1) = t + 1 + n by omega]
    abel

/-- Woodford (2003), App. G.2: a uniform bound for `B₂' Λᵐ u`, `m ≤ N`, over bounded `u`. -/
theorem exists_bound_dot_pow (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ) (N : ℕ) (K : ℝ) :
    ∃ c, 0 ≤ c ∧ ∀ m ≤ N, ∀ u : ι → ℝ, (∀ i, |u i| ≤ K) → |B2 ⬝ᵥ (Λ ^ m *ᵥ u)| ≤ c := by
  have hm : ∀ m, ∃ Km, ∀ u : ι → ℝ, (∀ i, |u i| ≤ K) → |B2 ⬝ᵥ (Λ ^ m *ᵥ u)| ≤ Km := by
    intro m
    obtain ⟨Km, hKm⟩ := exists_bound_mulVec (Matrix.of fun (_ : Unit) l => (B2 ᵥ* Λ ^ m) l) K
    exact ⟨Km, fun u hu => by rw [dotProduct_mulVec]; exact hKm u hu ()⟩
  choose Km hKm using hm
  refine ⟨∑ m ∈ Finset.range (N + 1), |Km m|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun m hm u hu => ?_⟩
  refine (hKm m u hu).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun m => |Km m|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))

/-- Woodford (2003), p. 555 and Assumption 8.5 (App. G.2): **observability makes the multipliers
bounded.** If `M_s = Λ M_{s-1} + q_s` and `B₂' M_s + v_s = 0` for all `s > s₀`, with `q`, `v`
bounded and `M` bounded up to `s₀`, then `M` is bounded — whatever the eigenvalues of `Λ`. -/
theorem boundedV_of_krylov {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ} (h85 : Assumption85b Λ B2)
    {M q : ℕ → Ω → ι → ℝ} {v : ℕ → Ω → ℝ} {s0 : ℕ} (hq : BoundedV q)
    (hv : ∃ K, ∀ t ω, |v t ω| ≤ K)
    (h120 : ∀ s, s0 < s → ∀ ω, M s ω = Λ *ᵥ M (s - 1) ω + q s ω)
    (h119 : ∀ s, s0 < s → ∀ ω, B2 ⬝ᵥ M s ω + v s ω = 0)
    (hM0 : ∃ K, ∀ s, s ≤ s0 → ∀ ω i, |M s ω i| ≤ K) : BoundedV M := by
  obtain ⟨C, hC⟩ := krylov_factor h85
  obtain ⟨Kq, hKq⟩ := hq
  obtain ⟨Kv, hKv⟩ := hv
  obtain ⟨K0, hK0⟩ := hM0
  obtain ⟨c, hc0, hc⟩ := exists_bound_dot_pow Λ B2 Λ.rank Kq
  have hb : ∀ t, s0 ≤ t → ∀ ω (j : Fin Λ.rank),
      |(B2 ᵥ* Λ ^ (j.val + 1)) ⬝ᵥ M t ω| ≤ Kv + (Λ.rank + 1) * c := by
    intro t ht ω j
    have hit := iterate_rec (Λ := Λ) (m := fun s => M s ω) (q := fun s => q s ω) (t := t)
      (n := j.val + 1) (fun i hi1 _ => h120 (t + i) (by omega) ω)
    have h19 := h119 (t + (j.val + 1)) (by omega) ω
    rw [hit, dotProduct_add, dotProduct_sum] at h19
    rw [← dotProduct_mulVec]
    have heq : B2 ⬝ᵥ (Λ ^ (j.val + 1) *ᵥ M t ω) = -v (t + (j.val + 1)) ω -
        ∑ i ∈ Finset.range (j.val + 1), B2 ⬝ᵥ (Λ ^ (j.val + 1 - 1 - i) *ᵥ q (t + 1 + i) ω) := by
      linarith
    rw [heq]
    have hsum : |∑ i ∈ Finset.range (j.val + 1), B2 ⬝ᵥ (Λ ^ (j.val + 1 - 1 - i) *ᵥ
        q (t + 1 + i) ω)| ≤ (j.val + 1) * c := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_card_nsmul (Finset.range (j.val + 1))
        (fun i => |B2 ⬝ᵥ (Λ ^ (j.val + 1 - 1 - i) *ᵥ q (t + 1 + i) ω)|) c
        (fun i _ => hc _ (by omega) _ (hKq _ ω))
      simpa using this
    have hj : ((j.val : ℝ) + 1) * c ≤ (Λ.rank + 1) * c := by
      have : (j.val : ℝ) ≤ Λ.rank := by exact_mod_cast j.isLt.le
      nlinarith
    calc |-v (t + (j.val + 1)) ω - ∑ i ∈ Finset.range (j.val + 1),
          B2 ⬝ᵥ (Λ ^ (j.val + 1 - 1 - i) *ᵥ q (t + 1 + i) ω)|
        ≤ |v (t + (j.val + 1)) ω| + |∑ i ∈ Finset.range (j.val + 1),
          B2 ⬝ᵥ (Λ ^ (j.val + 1 - 1 - i) *ᵥ q (t + 1 + i) ω)| := by
          rw [sub_eq_add_neg, ← neg_add]
          rw [abs_neg]
          exact abs_add_le _ _
      _ ≤ Kv + (Λ.rank + 1) * c := add_le_add (hKv _ _) (hsum.trans hj)
  obtain ⟨KC, hKC⟩ := exists_bound_mulVec C (Kv + (Λ.rank + 1) * c)
  refine ⟨max K0 (KC + Kq), fun s ω i => ?_⟩
  by_cases hs : s ≤ s0
  · exact (hK0 s hs ω i).trans (le_max_left _ _)
  · rw [h120 s (by omega) ω, hC]
    refine (abs_add_le _ _).trans ((add_le_add (hKC _ (fun j => hb (s - 1) (by omega) ω j) i)
      (hKq s ω i)).trans (le_max_right _ _))

/-- Woodford (2003), eq. (1.17), p. 551 with (1.24), p. 554: the time-invariant initial-multiplier
rule. From a window of `K` periods of `q` and `v` (`qs i = q_{s₀+1+i}`, `vs i = v_{s₀+1+i}`) it
returns `Λ^{K-1} C b + ∑_{i<K} Λ^{K-1-i} q_{s₀+1+i}`, where
`b_j = −v_{s₀+1+j} − ∑_{i ≤ j} B₂' Λ^{j-i} q_{s₀+1+i}` recovers `B₂' Λ^{j+1} M_{s₀}`. -/
noncomputable def gRule (Λ : Matrix ι ι ℝ) (B2 : ι → ℝ) (C : Matrix ι (Fin Λ.rank) ℝ) (K : ℕ)
    (qs : ℕ → ι → ℝ) (vs : ℕ → ℝ) : ι → ℝ :=
  Λ ^ (K - 1) *ᵥ (C *ᵥ fun j => -vs j.val -
      ∑ i ∈ Finset.range (j.val + 1), B2 ⬝ᵥ (Λ ^ (j.val - i) *ᵥ qs i)) +
    ∑ i ∈ Finset.range K, Λ ^ (K - 1 - i) *ᵥ qs i

/-- Woodford (2003), (1.17) and Assumption 8.5 (App. G.2): if (1.20) and (1.19) hold on a window
of `K ≥ max(1, rank Λ)` periods `s₀ + 1, …, s₀ + K`, the multiplier at its end is given by the
time-invariant linear rule `gRule` of the window's `q` and `v` (an explicit form of
`TargetCriterion.Krylov.initial_multiplier_unique`). -/
theorem multiplier_rule {Λ : Matrix ι ι ℝ} {B2 : ι → ℝ} {C : Matrix ι (Fin Λ.rank) ℝ}
    (hC : ∀ w, Λ *ᵥ w = C *ᵥ fun j => (B2 ᵥ* Λ ^ (j.val + 1)) ⬝ᵥ w) {K s0 : ℕ} (hK1 : 1 ≤ K)
    (hKk : Λ.rank ≤ K) {m q : ℕ → ι → ℝ} {v : ℕ → ℝ}
    (h120 : ∀ j, 1 ≤ j → j ≤ K → m (s0 + j) = Λ *ᵥ m (s0 + j - 1) + q (s0 + j))
    (h119 : ∀ j, 1 ≤ j → j ≤ K → B2 ⬝ᵥ m (s0 + j) + v (s0 + j) = 0) :
    m (s0 + K) = gRule Λ B2 C K (fun i => q (s0 + 1 + i)) (fun i => v (s0 + 1 + i)) := by
  rw [iterate_rec h120, gRule]
  congr 1
  obtain ⟨K', rfl⟩ := Nat.exists_eq_add_of_le hK1
  rw [show 1 + K' - 1 = K' by omega, add_comm 1 K', pow_succ, ← mulVec_mulVec, hC]
  congr 2
  funext j
  have hit := iterate_rec (Λ := Λ) (m := m) (q := q) (t := s0) (n := j.val + 1)
    (fun i hi1 hi2 => h120 i hi1 (by have := j.isLt; omega))
  have h19 := h119 (j.val + 1) (by omega) (by have := j.isLt; omega)
  rw [hit, dotProduct_add, dotProduct_sum] at h19
  rw [← dotProduct_mulVec]
  have hs : ∑ i ∈ Finset.range (j.val + 1), B2 ⬝ᵥ (Λ ^ (j.val + 1 - 1 - i) *ᵥ q (s0 + 1 + i)) =
      ∑ i ∈ Finset.range (j.val + 1), B2 ⬝ᵥ (Λ ^ (j.val - i) *ᵥ q (s0 + 1 + i)) :=
    Finset.sum_congr rfl fun i _ => by rw [show j.val + 1 - 1 - i = j.val - i by omega]
  rw [hs, show s0 + (j.val + 1) = s0 + 1 + j.val by omega] at h19
  linarith

end KrylovBound

open KrylovBound

/-! ### Assumption 8.1 with measurable, bounded initial conditions -/

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), Assumption 8.1, p. 541 (existence half), **corrected**: (1.1) + (1.9) has a
bounded solution for every bounded adapted disturbance, every `Z_{t₀}` known at `t₀` and every
**bounded** initial multiplier `M_{t₀−1}` **known at `t₀ − 1`**. (`GeneralFOC.LQ.FOCSolvable`
asks for every `M_{t₀−1}` known at `t₀`; since a solution has `M_t` known at `t` and bounded,
that version can fail for every problem, `NKAssumption81.not_assumption81_coin`.) -/
def FOCSolvableM (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) : Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ), BoundedV c → AdaptedV 𝔼 c →
    KnownV 𝔼 t0 Z0 → (∃ K, ∀ ω r, |M0 ω r| ≤ K) → KnownV 𝔼 (t0 - 1) M0 →
      ∃ y φ, FOCSystem P 𝔼 c t0 Z0 M0 y φ

variable (P : LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)

/-- Woodford (2003), Assumption 8.1, p. 541, **corrected**: existence for bounded initial
multipliers known at `t₀ − 1` (`FOCSolvableM`) and uniqueness (`GeneralFOC.LQ.FOCUnique`). -/
structure Assumption81M where
  solvable : FOCSolvableM P 𝔼 t0
  unique : FOCUnique P 𝔼 t0

variable {P 𝔼 t0}

/-- Woodford (2003), Assumption 8.1, p. 541: the formalisation `GeneralFOC.LQ.Assumption81`
implies the corrected one. -/
theorem Assumption81M.of_assumption81 (hA : Assumption81 P 𝔼 t0) : Assumption81M P 𝔼 t0 :=
  ⟨fun c Z0 M0 hbc hac hZ0 _ hM0 =>
    hA.solvable c Z0 M0 hbc hac hZ0 (KnownV.mono 𝔼 (Nat.sub_le t0 1) hM0), hA.unique⟩

/-! ### Proposition 8.2 from the corrected Proposition 8.1 -/

namespace Prop82M

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω} {t0 : ℕ}

/-- Woodford (2003), eq. (1.23), p. 554: commitment to the target criterion at all `t ≥ t₀`
(`α = det(I − ΛL)`, `B = adj(I − ΛL)`, historical `q`, `v` before `t₀`), for the matrices of the
corrected Proposition 8.1. -/
def CriterionM (H : Prop81ConclusionM P 𝔼 t0) (D : ℕ) (qh : ℕ → Ω → ιz → ℝ) (vh : ℕ → Ω → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ ω, crit (alpha H.Λ) (Bpoly H.Λ) D P.sys.B2 (splice t0 vh (vproc P y))
    (splice t0 qh (H.Qop (xproc P y))) t ω = 0

/-- Woodford (2003), p. 555: the multipliers implied by a plan under the criterion: `M_t` from
(1.20) with the history before `t₀`, `ξ_t` from (1.21), `φ_t = (ξ_t, M_{t-1})`. -/
def φconM (H : Prop81ConclusionM P 𝔼 t0) (Mh : ℕ → Ω → ιz → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun s ω => Sum.elim
    (if t0 ≤ s then H.Υ *ᵥ Mseq H.Λ Mh t0 (H.Qop (xproc P y)) (s - 1) ω +
      H.Rop (xproc P y) s ω else 0)
    (Mseq H.Λ Mh t0 (H.Qop (xproc P y)) (s - 1) ω)

/-- Woodford (2003), p. 540: the constructed `M_t` is known at `t` (restated from
`TargetCriterion.Prop82.known_Mseq` for the corrected Proposition 8.1). -/
theorem known_MseqM (H : Prop81ConclusionM P 𝔼 t0) (ht0 : 1 ≤ t0) {Mh : ℕ → Ω → ιz → ℝ}
    (hMhk : AdaptedV 𝔼 Mh) (x : ℕ → Ω → ιZ ⊕ ιz → ℝ) :
    ∀ s, KnownV 𝔼 s (Mseq H.Λ Mh t0 (H.Qop x) s) := by
  intro s
  by_cases hs : s < t0
  · simp only [Mseq, hs, ↓reduceIte]
    exact hMhk s
  · push Not at hs
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    simp only [Mseq, show ¬ t0 + k < t0 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    induction k with
    | zero =>
      exact KnownV.mulVec_add H.Λ (KnownV.mono 𝔼 (by omega) (hMhk (t0 - 1)))
        (H.Qadapted x (t0 + 0))
    | succ k ih =>
      exact KnownV.mulVec_add H.Λ (KnownV.mono 𝔼 (by omega) (ih (by omega)))
        (H.Qadapted x (t0 + (k + 1)))

omit [DecidableEq ιZ] in
/-- Woodford (2003), eq. (1.26), p. 554: `v_t = T_i'W(τ_t − τ*)` is bounded for bounded plans. -/
theorem bounded_vproc {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : BoundedV y) :
    ∃ K, ∀ t ω, |vproc P y t ω| ≤ K := by
  obtain ⟨M, hM⟩ := hy
  obtain ⟨K1, hK1⟩ := exists_bound_mulVec P.T M
  obtain ⟨K2, hK2⟩ := exists_bound_mulVec (Matrix.of fun (_ : Unit) a => (P.Ti ᵥ* P.W) a)
    (K1 + ∑ b, |P.τstar b|)
  refine ⟨K2, fun t ω => ?_⟩
  have hb : ∀ b, |(P.T *ᵥ y t ω - P.τstar) b| ≤ K1 + ∑ b, |P.τstar b| := fun b => by
    have h2 : |P.τstar b| ≤ ∑ b, |P.τstar b| :=
      Finset.single_le_sum (f := fun b => |P.τstar b|) (fun b _ => abs_nonneg _)
        (Finset.mem_univ b)
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hK1 _ (hM t ω) b) h2)
  have := hK2 _ hb ()
  rw [vproc, dotProduct_mulVec]
  exact this

/-- Woodford (2003), p. 555: splicing two bounded processes gives a bounded process. -/
theorem boundedV_splice {ι : Type*} {h x : ℕ → Ω → ι → ℝ} (hh : BoundedV h) (hx : BoundedV x)
    : BoundedV (splice t0 h x) := by
  obtain ⟨K1, hK1⟩ := hh
  obtain ⟨K2, hK2⟩ := hx
  refine ⟨max K1 K2, fun s ω i => ?_⟩
  unfold splice
  split_ifs
  · exact (hK1 s ω i).trans (le_max_left _ _)
  · exact (hK2 s ω i).trans (le_max_right _ _)

/-- Woodford (2003), p. 555 (Proposition 8.2, the key step): a bounded feasible plan satisfying
the target criterion (1.23) at all `t ≥ t₀`, given a consistent bounded history, solves
(1.1) + (1.9) with initial multipliers `M_{t₀-1} = Mh_{t₀-1}`. Unlike
`TargetCriterion.Prop82.focSystem_of_criterion`, no stability of `Λ` is assumed: the multipliers
are bounded by Assumption 8.5 (`boundedV_of_krylov`). -/
theorem focSystem_of_criterionM (H : Prop81ConclusionM P 𝔼 t0)
    (h85 : Assumption85b H.Λ P.sys.B2) {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D) (hα : (alpha H.Λ).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ} (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.Feasible 𝔼 c t0 Z0 y)
    (hcrit : CriterionM H D qh vh y) :
    FOCSystem P 𝔼 c t0 Z0 (Mh (t0 - 1)) y (φconM H Mh y) := by
  set x := xproc P y with hx
  set Ms := Mseq H.Λ Mh t0 (H.Qop x) with hMs
  have hxb : BoundedV x := boundedV_xproc hy.2.2.1
  have hMpart : ∀ s ω, Mpart (φconM H Mh y s ω) = Ms (s - 1) ω := fun _ _ => rfl
  have hξ : ∀ s, t0 ≤ s → ∀ ω, ξpart (φconM H Mh y s ω) = H.Υ *ᵥ Ms (s - 1) ω + H.Rop x s ω := by
    intro s hs ω
    funext r
    simp [φconM, ξpart, hs, hMs, hx]
  -- (1.20) and (1.19) for the spliced processes, from `t₀ − D` on
  have h120' : ∀ s, t0 - D ≤ s → ∀ ω,
      Ms s ω = H.Λ *ᵥ Ms (s - 1) ω + splice t0 qh (H.Qop x) s ω := by
    intro s hs ω
    by_cases hlt : s < t0
    · simp only [hMs, Mseq, splice, hlt, ↓reduceIte, show s - 1 < t0 by omega]
      exact hhist.1 s hs hlt ω
    · simp only [splice, hlt, ↓reduceIte]
      exact Mseq_rec (by omega) s (by omega) ω
  have h119' : ∀ s, t0 - D ≤ s → s < t0 → ∀ ω,
      P.sys.B2 ⬝ᵥ Ms s ω + splice t0 vh (vproc P y) s ω = 0 := by
    intro s hs hlt ω
    simp only [hMs, Mseq, splice, hlt, ↓reduceIte]
    exact hhist.2 s hs hlt ω
  have h119 := eq119_of_criterion (eq122 H.Λ) (alpha_coeff_zero H.Λ) hB hα P.sys.B2
    (show t0 - D + D ≤ t0 by omega) h120' h119' hcrit
  -- the multipliers are bounded (Assumption 8.5)
  have hMsb : BoundedV Ms := by
    obtain ⟨K1, hK1⟩ := hMhb
    refine boundedV_of_krylov h85 (s0 := t0 - D - 1)
      (boundedV_splice hqhb (H.Qbounded x hxb)) ?_
      (fun s hs ω => h120' s (by omega) ω) (fun s hs ω => h119 s (by omega) ω)
      ⟨K1, fun s hs ω i => ?_⟩
    · obtain ⟨Kv1, hKv1⟩ := hvhb
      obtain ⟨Kv2, hKv2⟩ := bounded_vproc (P := P) hy.2.2.1
      refine ⟨max Kv1 Kv2, fun s ω => ?_⟩
      unfold splice
      split_ifs
      · exact (hKv1 s ω).trans (le_max_left _ _)
      · exact (hKv2 s ω).trans (le_max_right _ _)
    · simp only [hMs, Mseq, show s < t0 by omega, ↓reduceIte]
      exact hK1 s ω i
  have hφb : BoundedV (φconM H Mh y) := by
    obtain ⟨K1, hK1⟩ := hMsb
    obtain ⟨KR, hKR⟩ := H.Rbounded x hxb
    obtain ⟨KΥ, hKΥ⟩ := exists_bound_mulVec H.Υ K1
    refine ⟨max (max (KΥ + KR) K1) 0, fun s ω i => ?_⟩
    rcases i with r | r
    · by_cases hs : t0 ≤ s
      · have := congrFun (hξ s hs ω) r
        simp only [ξpart, Pi.add_apply] at this
        rw [this]
        exact (abs_add_le _ _).trans ((add_le_add (hKΥ _ (hK1 _ ω) r) (hKR s ω r)).trans
          ((le_max_left _ _).trans (le_max_left _ _)))
      · simp only [φconM, hs, ↓reduceIte, Sum.elim_inl, Pi.zero_apply, abs_zero]
        exact le_max_right _ _
    · exact (hK1 _ ω r).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hmeas : MultiplierMeas 𝔼 (φconM H Mh y) := by
    intro t r
    have := known_MseqM H (by omega) hMhk x t r
    simpa [φconM, hMs] using this
  have h120 : Eq120 t0 H.Λ (H.Qop x) (φconM H Mh y) := by
    intro t ht ω
    rw [hMpart, hMpart, Nat.add_sub_cancel]
    exact Mseq_rec (by omega) t ht ω
  have h121 : Eq121 t0 H.Υ (H.Rop x) (φconM H Mh y) := by
    intro t ht ω
    rw [hξ t ht ω, hMpart]
  have h118 := (H.equiv y (φconM H Mh y) hy.2.2.1 hy.2.2.2 hφb
    (fun t _ r => hmeas t r)).mpr ⟨h120, h121⟩
  refine ⟨hy, hφb, hmeas, fun ω => ?_, fun t ht ω => ?_⟩
  · rw [hMpart]
    simp only [hMs, Mseq, show t0 - 1 < t0 by omega, ↓reduceIte]
  · refine (foc_iff_split P hmeas y t ω).mpr ⟨h118 t ht ω, ?_⟩
    have := h119 t (by omega) ω
    simp only [splice, show ¬ t < t0 by omega, ↓reduceIte] at this
    rw [hMpart, Nat.add_sub_cancel]
    exact this

/-- Woodford (2003), **Proposition 8.2** (second part), p. 555: the plan determined by
commitment to (1.23) minimises (1.2) among bounded feasible plans subject to the initial
constraint (1.27) `Ẽ z_{t₀} = ē` (any expectation system with pull-out; no stability
hypothesis on `Λ`). -/
theorem prop82M_optimal (hpull : 𝔼.PullOut) (H : Prop81ConclusionM P 𝔼 t0)
    (h85 : Assumption85b H.Λ P.sys.B2) {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D) (hα : (alpha H.Λ).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ} (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.Feasible 𝔼 c t0 Z0 y)
    (hcrit : CriterionM H D qh vh y) :
    P.OptimalSubjectTo 𝔼 c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y :=
  optimalSubjectTo_of_focSystem P hpull
    (focSystem_of_criterionM H h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy hcrit)

/-- Woodford (2003), **Proposition 8.2** (determinacy, uniqueness), p. 555: under Assumptions
8.1 and 8.5 two bounded feasible plans satisfying (1.23) at all `t ≥ t₀` (same history)
coincide from `t₀` on. -/
theorem prop82M_unique (hA : Assumption81M P 𝔼 t0) (H : Prop81ConclusionM P 𝔼 t0)
    (h85 : Assumption85b H.Λ P.sys.B2) {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D) (hα : (alpha H.Λ).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ} (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} (hy : P.Feasible 𝔼 c t0 Z0 y)
    (hy' : P.Feasible 𝔼 c t0 Z0 y') (hcrit : CriterionM H D qh vh y)
    (hcrit' : CriterionM H D qh vh y') : ∀ t, t0 ≤ t → y t = y' t := fun t ht =>
  (hA.unique c Z0 (Mh (t0 - 1)) y y' _ _
    (focSystem_of_criterionM H h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy hcrit)
    (focSystem_of_criterionM H h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy' hcrit') t ht).1

/-- Woodford (2003), the Mseq-type history used by `prop82M_exists` and
`prop82M_multiplier_rule`: the history `Mh` before `t₀`, then the multipliers `M_s` of a FOC
solution (`φ_{s+1} = (ξ_{s+1}, M_s)`). -/
def histThen (t0 : ℕ) (Mh : ℕ → Ω → ιz → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : ℕ → Ω → ιz → ℝ :=
  fun s => if s < t0 then Mh s else fun ω => Mpart (φ (s + 1) ω)

/-- Woodford (2003), p. 555 and fn 14: along a FOC solution with `M_{t₀-1} = Mh_{t₀-1}` and a
consistent history, the spliced multipliers satisfy (1.20) and (1.19) from `t₀ − D` on. -/
theorem histThen_rec (H : Prop81ConclusionM P 𝔼 t0) {D : ℕ} (hD : D + 1 ≤ t0)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ} (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh)
    {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hs : FOCSystem P 𝔼 c t0 Z0 (Mh (t0 - 1)) y φ) :
    (∀ s, t0 - D ≤ s → ∀ ω, histThen t0 Mh φ s ω =
      H.Λ *ᵥ histThen t0 Mh φ (s - 1) ω + splice t0 qh (H.Qop (xproc P y)) s ω) ∧
    ∀ s, t0 - D ≤ s → ∀ ω,
      P.sys.B2 ⬝ᵥ histThen t0 Mh φ s ω + splice t0 vh (vproc P y) s ω = 0 := by
  obtain ⟨hfe, hbφ, hmφ, hM, hfoc⟩ := hs
  have hsplit := fun t (ht : t0 ≤ t) ω => (foc_iff_split P hmφ y t ω).mp (hfoc t ht ω)
  have h120 := ((H.equiv y φ hfe.2.2.1 hfe.2.2.2 hbφ (fun t _ r => hmφ t r)).mp
    fun t ht ω => (hsplit t ht ω).1).1
  refine ⟨fun s hs ω => ?_, fun s hs ω => ?_⟩
  · by_cases hlt : s < t0
    · simp only [histThen, splice, hlt, ↓reduceIte, show s - 1 < t0 by omega]
      exact hhist.1 s hs hlt ω
    · simp only [histThen, splice, hlt, ↓reduceIte]
      rw [h120 s (by omega) ω]
      congr 2
      by_cases heq : s = t0
      · subst heq
        simp only [show s - 1 < s by omega, ↓reduceIte]
        exact hM ω
      · simp only [show ¬ s - 1 < t0 by omega, ↓reduceIte, show s - 1 + 1 = s by omega]
  · by_cases hlt : s < t0
    · simp only [histThen, splice, hlt, ↓reduceIte]
      exact hhist.2 s hs hlt ω
    · simp only [histThen, splice, hlt, ↓reduceIte, vproc]
      exact (hsplit s (by omega) ω).2

/-- Woodford (2003), **Proposition 8.2** (determinacy, existence), p. 555: under Assumption 8.1
the bounded solution of (1.1) + (1.9) with initial multipliers `M_{t₀-1} = Mh_{t₀-1}` satisfies
the criterion (1.23) at every `t ≥ t₀` (fn 14). -/
theorem prop82M_exists (hA : Assumption81M P 𝔼 t0) (H : Prop81ConclusionM P 𝔼 t0) {D : ℕ}
    (hD : D + 1 ≤ t0) (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D)
    (hα : (alpha H.Λ).natDegree ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh) (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    (hZ0 : KnownV 𝔼 t0 Z0) :
    ∃ y, P.Feasible 𝔼 c t0 Z0 y ∧ CriterionM H D qh vh y := by
  have hMb : ∃ K, ∀ ω r, |Mh (t0 - 1) ω r| ≤ K := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, fun ω r => hK (t0 - 1) ω r⟩
  obtain ⟨y, φ, hs⟩ := hA.solvable c Z0 (Mh (t0 - 1)) hbc hac hZ0 hMb (hMhk (t0 - 1))
  refine ⟨y, hs.1, ?_⟩
  obtain ⟨h120', h119'⟩ := histThen_rec H hD hhist hs
  have hc := eq123_of_eq119_eq120 (eq122 H.Λ) hB hα P.sys.B2 h119' h120'
  intro t ht ω
  exact hc t (by omega) ω

/-- Woodford (2003), **Proposition 8.2**, p. 555: commitment to (1.23) at all `t ≥ t₀` results
in a determinate equilibrium: there is exactly one bounded feasible plan (from `t₀` on) that
satisfies the criterion, for every bounded adapted disturbance process and every initial
condition known at `t₀`. -/
theorem prop82M_determinate (hA : Assumption81M P 𝔼 t0) (H : Prop81ConclusionM P 𝔼 t0)
    (h85 : Assumption85b H.Λ P.sys.B2) {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D) (hα : (alpha H.Λ).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ} (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh)
    (hMhb : BoundedV Mh) (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh)
    (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c)
    (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ} (hZ0 : KnownV 𝔼 t0 Z0) :
    ∃ y, (P.Feasible 𝔼 c t0 Z0 y ∧ CriterionM H D qh vh y) ∧
      ∀ y', P.Feasible 𝔼 c t0 Z0 y' → CriterionM H D qh vh y' → ∀ t, t0 ≤ t → y' t = y t := by
  obtain ⟨y, hy, hcrit⟩ := prop82M_exists hA H hD hB hα hhist hMhb hMhk hbc hac hZ0
  exact ⟨y, ⟨hy, hcrit⟩, fun y' hy' hcrit' t ht =>
    prop82M_unique hA H h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy' hy hcrit' hcrit t ht⟩

/-- Woodford (2003), eqs. (1.17) and (1.24), pp. 551–554 (the self-consistency behind
Proposition 8.2): along a solution of (1.1) + (1.9) with initial multipliers
`M_{t₀-1} = Mh_{t₀-1}` and a consistent history, there is one fixed matrix `C` such that at every
date `t ≥ t₀` the multipliers are the same time-invariant linear function `gRule` of the
predetermined state `Z̄_t = (q_{t-1}, …, q_{t-D}, v_{t-1}, …, v_{t-D})` (1.24): `M_{t-1} = g(Z̄_t)`.
At `t = t₀` this is the initial-multiplier rule (1.11); at later dates it is (1.17), which is
what makes the equilibrium optimal from a timeless perspective. -/
theorem prop82M_multiplier_rule (H : Prop81ConclusionM P 𝔼 t0)
    (h85 : Assumption85b H.Λ P.sys.B2) {D : ℕ} (hD : D + 1 ≤ t0) (hD1 : 1 ≤ D)
    (hDk : H.Λ.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh) {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : FOCSystem P 𝔼 c t0 Z0 (Mh (t0 - 1)) y φ) :
    ∃ C : Matrix ιz (Fin H.Λ.rank) ℝ, ∀ t, t0 ≤ t → ∀ ω,
      Mpart (φ t ω) = gRule H.Λ P.sys.B2 C D
        (fun i => splice t0 qh (H.Qop (xproc P y)) (t - D + i) ω)
        (fun i => splice t0 vh (vproc P y) (t - D + i) ω) := by
  obtain ⟨C, hC⟩ := krylov_factor h85
  obtain ⟨h120, h119⟩ := histThen_rec H hD hhist hs
  refine ⟨C, fun t ht ω => ?_⟩
  have hrule := multiplier_rule hC hD1 hDk (s0 := t - 1 - D)
    (m := fun s => histThen t0 Mh φ s ω) (q := fun s => splice t0 qh (H.Qop (xproc P y)) s ω)
    (v := fun s => splice t0 vh (vproc P y) s ω)
    (fun j hj1 hjK => h120 (t - 1 - D + j) (by omega) ω)
    (fun j hj1 hjK => h119 (t - 1 - D + j) (by omega) ω)
  rw [show t - 1 - D + D = t - 1 by omega] at hrule
  have hidx : ∀ i, t - 1 - D + 1 + i = t - D + i := fun i => by omega
  simp only [hidx] at hrule
  rw [← hrule]
  by_cases hlt : t - 1 < t0
  · have ht0 : t = t0 := by omega
    subst ht0
    simp only [histThen, hlt, ↓reduceIte]
    exact hs.2.2.2.1 ω
  · simp only [histThen, hlt, ↓reduceIte, show t - 1 + 1 = t by omega]

/-- Woodford (2003), Definition, pp. 549–550 and Proposition 8.2, p. 555: **commitment to the
target criterion (1.23) is robustly optimal** — for every bounded adapted disturbance process
and every initial condition it determines a unique bounded equilibrium, and that equilibrium is
optimal from a timeless perspective (`GeneralSetup.RobustlyOptimal`). The rule's coefficients
depend only on the first-order conditions, not on the disturbance process. (The definition
`TimelesslyOptimalPlan` allows `X̄_t = z_t`, which is the instance used; the substantive
time-invariance of the initial-multiplier rule is `prop82M_multiplier_rule`.) -/
theorem prop82M_robustlyOptimal (hpull : 𝔼.PullOut) (hA : Assumption81M P 𝔼 t0)
    (H : Prop81ConclusionM P 𝔼 t0) (h85 : Assumption85b H.Λ P.sys.B2) {D : ℕ}
    (hD : D + 1 ≤ t0) (hB : ∀ i c, (Bpoly H.Λ i c).natDegree ≤ D)
    (hα : (alpha H.Λ).natDegree ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK H.Λ P.sys.B2 t0 D Mh qh vh) (hMhb : BoundedV Mh)
    (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh) (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := ιz) P 𝔼 t0 (fun _ y => CriterionM H D qh vh y)
      (fun _ y t ω => zpart (y t ω)) := by
  intro c Z0 hbc hac hZ0
  obtain ⟨y, ⟨hy, hcrit⟩, huniq⟩ :=
    prop82M_determinate hA H h85 hD hB hα hhist hMhb hMhk hqhb hvhb hbc hac hZ0
  refine ⟨y, hy, hcrit, huniq, 0, 1, fun t _ ω => by simp, ?_⟩
  have hopt := prop82M_optimal hpull H h85 hD hB hα hhist hMhb hMhk hqhb hvhb hy hcrit
  have he : (fun ω => P.sys.Et *ᵥ ((0 : ιz → ℝ) + (1 : Matrix ιz ιz ℝ) *ᵥ zpart (y t0 ω))) =
      fun ω => P.sys.Et *ᵥ zpart (y t0 ω) := by
    funext ω
    simp
  rw [he]
  exact hopt

end Prop82M

open Prop82M

/-! ### Proposition 8.2 for the explicit `Λ` of Proposition 8.1 -/

/-- Woodford (2003), **Proposition 8.2**, p. 555, for the matrices of Proposition 8.1 built from
a deflating pair (`Prop81General.prop81`, `Λ = β⁻¹ K⁻¹ Ẽ'`): under Assumption 8.1, Assumption 8.5
for this `Λ`, a lag length `D ≥ max(1, rank Ẽ)` and a consistent bounded history, commitment to
(1.23) determines a unique bounded equilibrium for every bounded adapted disturbance process,
optimal subject to its initial constraint (1.27) and hence robustly optimal. -/
theorem prop82_of_split {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ]
    [DecidableEq ιZ] [DecidableEq ιz] {P : LQProblem ιZ ιz ιτ} {𝔼 : ExpectationSystem Ω}
    {t0 : ℕ} (hpull : 𝔼.PullOut) (hA : Assumption81M P 𝔼 t0) (Dsp : DeflatingSplit P.sys P.β)
    (h85 : Assumption85b (Λmat P.sys P.β Dsp.J) P.sys.B2) {D : ℕ} (hD : D + 1 ≤ t0)
    (hDk : P.sys.Et.rank ≤ D) {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOK (Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh) (hMhb : BoundedV Mh)
    (hMhk : AdaptedV 𝔼 Mh) (hqhb : BoundedV qh) (hvhb : ∃ K, ∀ t ω, |vh t ω| ≤ K) :
    RobustlyOptimal (κ := ιz) P 𝔼 t0
      (fun _ y => CriterionM (prop81 P Dsp 𝔼 t0) D qh vh y) (fun _ y t ω => zpart (y t ω)) := by
  have hrk : (Λmat P.sys P.β Dsp.J).rank ≤ D := by
    rw [rank_Λmat P.sys P.β_pos.ne' Dsp.K_det]
    exact hDk
  exact prop82M_robustlyOptimal hpull hA (prop81 P Dsp 𝔼 t0) h85 hD
    (fun i c => (natDegree_Bpoly_le_rank _ i c).trans hrk)
    ((natDegree_alpha_le_rank _).trans hrk) hhist hMhb hMhk hqhb hvhb

end Woodford.OptimalPolicyRules.Prop82General
