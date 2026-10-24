/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.FutureSales
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Antidiag.Prod
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# A general formula, and when the present-value system determines the price level

Cochrane (2023), §7.4, pp. 224–226, equations (7.14)–(7.17).

Write `y_t = B_{t−1}^{(t)}/P_t` for the real value of maturing debt and
`A_t^{(m)} = (B_t^{(m)} − B_{t−1}^{(m)})/B_{m−1}^{(m)}` for the fraction of the debt due at `m`
that is
sold at `t`. The flow conditions (7.1) are the infinite upper-triangular linear system
`y_t = s_t + ∑_{j≥1} β^j E_t(A_t^{(t+j)} y_{t+j})` (`realFlow_iff_maturingSystem`).
Cochrane's weights are `W_t^{(0)} = 1`, `W_t^{(j)} = ∑_{k<j} A_{t+k}^{(t+j)} W_t^{(k)}` (`weight`),
and
(7.17) reads `y_t = E_t ∑_j β^j W_t^{(j)} s_{t+j}`.

## Main results

* `weight_first_step`: Cochrane's (last-step) recursion for `W` coincides with the first-step
  recursion `W_t^{(k+1)} = ∑_{j≤k} A_t^{(t+j+1)} W_{t+j+1}^{(k−j)}` produced by substitution.
* `comps`, `mem_comps`, `chainProd`, `chainProd_eq`, `chainSum`, `weight_eq_chainSum`: **Theorem W
  (ii)**: the weights are sums over strictly increasing chains `t = k₀ < … < k_n = t + m` of
  `∏ A_{k_i}^{(k_{i+1})}`.
* `theoremW_finite`: **Theorem W, finite horizon.** In an economy whose debt all matures by `T`,
  (7.17) holds exactly at every `t ≤ T`, under uncertainty.
* `abs_weight_le`, `sum_domWeight_le`: under the row condition `∑_j β^j a_j ≤ ρ < 1` on
  (deterministic bounds `a_j` for) the sale fractions, the weights are absolutely summable.
* `formulaW_solves`, `theoremW`: **Theorem W, infinite horizon.** Under the row condition and
bounded
  surpluses, (7.17) is a genuine convergent series, it solves the system, and every bounded
  solution equals it.
* `unique_of_row`, `unique_of_noBuyback`: **when the present-value system pins down the price
  level.** Bounded solutions are unique under the row condition, and also whenever the government
  never buys back debt (`B_t^{(m)} ≥ B_{t−1}^{(m)}`, nonnegative inherited debt).
* `bounded_of_presentValue`, `price_unique_noBuyback`: with nonnegative debt and positive prices
  the present-value relations force boundedness, so with no buy-backs the present-value relations
  determine the price level uniquely.
* `cx_*`: **the non-uniqueness counterexample** (E7.4): `B_{t−1}^{(t)} = 1`, `B_{t−1}^{(t+1)} =
2/β`,
  constant surplus. A one-parameter family of positive bounded price paths satisfies every flow and
  every present-value relation; the weights obey `W^{(k+2)} = (1 − 2/β) W^{(k+1)} + (2/β) W^{(k)}`,
  `β^k W^{(k)}` does not tend to zero, and (7.17) diverges. The policy buys back debt and violates
  the row condition, so both sufficient conditions are sharp in this sense.
* `unique_iff_homogeneous`: given one bounded solution, uniqueness of bounded solutions is
  equivalent to the homogeneous system having no nonzero bounded solution.
* `printed_715_fails`: the printed (7.15) without `β^j` is false (E7.2); `pvMatrix_row`: the
  corrected matrix display (7.16) (E7.3); `special_noSales`, `special_onePeriod`,
  `fracSold_onePeriod`: the special cases of §7.4.
* Labels (E7.1): on p. 225, (7.14) is the *flow* relation and (7.15) the *present-value*
  relation; the text swaps the two labels.
-/

namespace Cochrane.LongTermDebtDynamics.GeneralFormula

open Filter Topology MaturityStructure

/-! ### The weights and their two recursions -/

/-- Cochrane (2023), §7.4, p. 225–226: the weights `W_t^{(0)} = 1`,
`W_t^{(k+1)} = ∑_{n ≤ k} A_{t+n}^{(t+k+1)} W_t^{(n)}` (Cochrane's recursion, last step). -/
noncomputable def weight {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (t : ℕ) : ℕ → R
  | 0 => 1
  | k + 1 => ∑ n : Fin (k + 1), A (t + n) (t + (k + 1)) * weight A t n
decreasing_by exact n.isLt

/-- Cochrane (2023), §7.4, p. 225: `W_t^{(0)} = 1`. -/
theorem weight_zero {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (t : ℕ) : weight A t 0 = 1 := by
  rw [weight]

/-- Cochrane (2023), §7.4, p. 226: `W_t^{(k+1)} = ∑_{n<k+1} A_{t+n}^{(t+k+1)} W_t^{(n)}`. -/
theorem weight_succ {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (t k : ℕ) :
    weight A t (k + 1) = ∑ n ∈ Finset.range (k + 1), A (t + n) (t + (k + 1)) * weight A t n := by
  rw [weight, Fin.sum_univ_eq_sum_range (fun n => A (t + n) (t + (k + 1)) * weight A t n)]

/-- Cochrane (2023), §7.4, p. 226: reindexing a triangular double sum,
`∑_{j<N} ∑_{m<N−j} f j m = ∑_{k<N} ∑_{j≤k} f j (k − j)`. -/
theorem sum_triangle {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    ∑ j ∈ Finset.range N, ∑ m ∈ Finset.range (N - j), f j m =
      ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range (k + 1), f j (k - j) := by
  symm
  rw [Finset.sum_comm' (t' := Finset.range N) (s' := fun j => Finset.Ico j N)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Nat.add_sub_cancel_left]
  · intro k j
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega

/-- Cochrane (2023), §7.4, p. 226: **the two recursions agree.** Cochrane's last-step recursion
for `W` equals the first-step recursion obtained by substituting the flow condition forward,
`W_t^{(k+1)} = ∑_{j ≤ k} A_t^{(t+j+1)} W_{t+j+1}^{(k−j)}`. -/
theorem weight_first_step {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (k : ℕ) :
    ∀ t, weight A t (k + 1) =
      ∑ j ∈ Finset.range (k + 1), A t (t + (j + 1)) * weight A (t + (j + 1)) (k - j) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t
    rw [weight_succ, Finset.sum_range_succ' _ k, Finset.sum_range_succ _ k]
    simp only [add_zero, weight_zero, mul_one, Nat.sub_self]
    congr 1
    have hR : ∀ j ∈ Finset.range k, A t (t + (j + 1)) * weight A (t + (j + 1)) (k - j) =
        ∑ m ∈ Finset.range (k - j), A t (t + (j + 1)) *
          (A (t + (j + 1) + m) (t + (k + 1)) * weight A (t + (j + 1)) m) := by
      intro j hj
      have hjk := Finset.mem_range.mp hj
      obtain ⟨i, hi⟩ : ∃ i, k - j = i + 1 := ⟨k - j - 1, by omega⟩
      rw [hi, weight_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [show t + (j + 1) + (i + 1) = t + (k + 1) by omega]
    rw [Finset.sum_congr rfl hR, sum_triangle k (fun j m => A t (t + (j + 1)) *
      (A (t + (j + 1) + m) (t + (k + 1)) * weight A (t + (j + 1)) m))]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [ih n (Finset.mem_range.mp hn) t, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show t + (j + 1) + (n - j) = t + (n + 1) by omega]
    ring

/-! ### Theorem W (ii): the weights as a sum over chains -/

/-- Cochrane (2023), §7.4, p. 226: the compositions of `m`, i.e. the lists of positive gaps
`(k₁ − k₀, k₂ − k₁, …, k_n − k_{n−1})` of the strictly increasing chains
`0 = k₀ < k₁ < … < k_n = m`. -/
def comps : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | m + 1 => (Finset.range (m + 1)).biUnion fun g =>
      (comps (m - g)).map ⟨List.cons (g + 1), List.cons_injective⟩
decreasing_by omega

/-- Cochrane (2023), §7.4, p. 226: a list is a composition of `m` iff its entries are positive and
sum to `m` (so `comps m` is exactly the set of strictly increasing chains from `0` to `m`). -/
theorem mem_comps (m : ℕ) : ∀ l : List ℕ, l ∈ comps m ↔ (∀ x ∈ l, 0 < x) ∧ l.sum = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro l
    rcases m with _ | m
    · rw [comps]
      rcases l with _ | ⟨g, l⟩
      · simp
      · simp only [Finset.mem_singleton, reduceCtorEq, false_iff, not_and, List.mem_cons,
          List.sum_cons]
        intro h
        have := h g (Or.inl rfl)
        omega
    · rw [comps, Finset.mem_biUnion]
      constructor
      · rintro ⟨g, hg, hl⟩
        rw [Finset.mem_map] at hl
        obtain ⟨c, hc, rfl⟩ := hl
        have hg' := Finset.mem_range.mp hg
        obtain ⟨h1, h2⟩ := (ih (m - g) (by omega) c).mp hc
        refine ⟨fun x hx => ?_, ?_⟩
        · simp only [Function.Embedding.coeFn_mk, List.mem_cons] at hx
          rcases hx with rfl | hx
          · omega
          · exact h1 x hx
        · simp only [Function.Embedding.coeFn_mk, List.sum_cons, h2]
          omega
      · rintro ⟨hpos, hsum⟩
        rcases l with _ | ⟨g, c⟩
        · simp at hsum
        · have hg : 0 < g := hpos g (List.mem_cons_self ..)
          simp only [List.sum_cons] at hsum
          refine ⟨g - 1, Finset.mem_range.mpr (by omega), ?_⟩
          rw [Finset.mem_map]
          refine ⟨c, (ih (m - (g - 1)) (by omega) c).mpr ⟨fun x hx => hpos x
            (List.mem_cons_of_mem _ hx), by omega⟩, ?_⟩
          simp only [Function.Embedding.coeFn_mk]
          congr 1
          omega

/-- Cochrane (2023), §7.4, p. 226: the product of sale fractions along a chain starting at `t` with
gaps `l`: `chainProd A t [g₁, …, g_n] = A_t^{(t+g₁)} A_{t+g₁}^{(t+g₁+g₂)} ⋯`. -/
def chainProd {R : Type*} [CommRing R] (A : ℕ → ℕ → R) : ℕ → List ℕ → R
  | _, [] => 1
  | t, g :: l => A t (t + g) * chainProd A (t + g) l

/-- Cochrane (2023), §7.4, p. 226: the chain product written explicitly with the chain points
`k_i = t + g₁ + ⋯ + g_i`: `∏_{i<n} A_{k_i}^{(k_{i+1})}`. -/
theorem chainProd_eq {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (l : List ℕ) :
    ∀ t, chainProd A t l = ∏ i ∈ Finset.range l.length,
      A (t + (l.take i).sum) (t + (l.take (i + 1)).sum) := by
  induction l with
  | nil => intro t; simp [chainProd]
  | cons g l ih =>
    intro t
    rw [chainProd, ih, List.length_cons, Finset.prod_range_succ', mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [List.take_succ_cons, List.take_succ_cons]
      simp only [List.sum_cons, add_assoc]

/-- Cochrane (2023), §7.4, p. 226: the explicit weight, the sum over all chains
`t = k₀ < k₁ < … < k_n = t + m` of `∏ A_{k_i}^{(k_{i+1})}`. -/
noncomputable def chainSum {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (t m : ℕ) : R :=
  ∑ c ∈ comps m, chainProd A t c

/-- Cochrane (2023), §7.4, p. 226: **Theorem W (ii).** Cochrane's recursively defined weights are
the sums over chains, `W_t^{(m)} = ∑_{t = k₀ < … < k_n = t + m} ∏_i A_{k_i}^{(k_{i+1})}`. -/
theorem weight_eq_chainSum {R : Type*} [CommRing R] (A : ℕ → ℕ → R) (m : ℕ) :
    ∀ t, weight A t m = chainSum A t m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t
    rcases m with _ | k
    · simp [chainSum, comps, chainProd, weight_zero]
    · rw [weight_first_step, chainSum, comps, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun g hg => ?_
        rw [Finset.sum_map, ih (k - g) (by omega), chainSum, Finset.mul_sum]
        rfl
      · intro g _ g' _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx hx'
        rw [Finset.mem_map] at hx hx'
        obtain ⟨c, -, rfl⟩ := hx
        obtain ⟨c', -, h⟩ := hx'
        simp only [Function.Embedding.coeFn_mk, List.cons.injEq] at h
        exact hne (by omega)

/-! ### The maturing-debt system -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.4, p. 225: the fraction of the debt due at `m` sold at `t`,
`A_t^{(m)} = (B_t^{(m)} − B_{t−1}^{(m)})/B_{m−1}^{(m)}`. -/
noncomputable def fracSold (D : ℕ → ℕ → Ω → ℝ) (t m : ℕ) : Ω → ℝ :=
  (D (t + 1) m - D t m) / D m m

/-- Cochrane (2023), eq. (7.14), p. 225, in maturing-value form: with `y_t = B_{t−1}^{(t)}/P_t`, the
flow conditions are `y_t = s_t + ∑_{j≥0} β^{j+1} E_t(A_t^{(t+j+1)} y_{t+j+1})`. -/
def MaturingSystem (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (y s : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω, HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) ω)
    (y t ω - s t ω)

/-- Cochrane (2023), eqs. (7.1)/(7.14), p. 225: the flow condition (7.1) at `t` is the maturing-debt
system at `t` for `y_t = B_{t−1}^{(t)}/P_t` and `A = fracSold`, when the debt coming due is never
zero. -/
theorem realFlow_iff_maturingSystem (hpo : 𝔼.PullOut) {β : ℝ} {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hDmm : ∀ m ω, D m m ω ≠ 0) (t : ℕ) :
    RealFlow 𝔼 β D x s t ↔ MaturingSystem 𝔼 β (fracSold D) (fun u => D u u * x u) s t := by
  have hterm : ∀ m, sales D t m * 𝔼.E t (x m) = 𝔼.E t (fracSold D t m * (D m m * x m)) := by
    intro m
    have hk : 𝔼.E t (sales D t m) = sales D t m := by
      rw [sales, map_sub, hD.2 t m, Predetermined.known 𝔼 hD le_rfl m]
    have : fracSold D t m * (D m m * x m) = sales D t m * x m := by
      funext ω
      simp only [fracSold, sales, Pi.mul_apply, Pi.div_apply, Pi.sub_apply]
      field_simp [hDmm m ω]
    rw [this, hpo t _ _ hk]
  unfold RealFlow MaturingSystem
  refine forall_congr' fun ω => ?_
  have hf : (fun j : ℕ => β ^ (j + 1) * (sales D t (t + (j + 1)) ω *
      𝔼.E t (x (t + (j + 1))) ω)) = fun j : ℕ => β ^ (j + 1) *
        𝔼.E t (fracSold D t (t + (j + 1)) *
          (D (t + (j + 1)) (t + (j + 1)) * x (t + (j + 1)))) ω := by
    funext j
    rw [← hterm]
    rfl
  rw [hf]
  exact Iff.rfl

/-- Cochrane (2023), §7.4, p. 226: if each sale fraction `A_t^{(t+j+1)}` is known at `t + j` (when
the last sale before maturity takes place), the weight `W_t^{(m+1)}` is known at `t + m`. -/
theorem weight_known (hpo : 𝔼.PullOut) {A : ℕ → ℕ → Ω → ℝ}
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1))) (t m : ℕ) :
    𝔼.E (t + m) (weight A t (m + 1)) = weight A t (m + 1) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [weight_succ, map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hAk : 𝔼.E (t + m) (A (t + n) (t + (m + 1))) = A (t + n) (t + (m + 1)) := by
      have := hA (t + n) (m - n)
      rwa [show t + n + (m - n) = t + m by omega, show t + n + (m - n + 1) = t + (m + 1) by omega]
        at this
    rw [hpo _ _ _ hAk]
    congr 1
    rcases n with _ | n
    · rw [weight_zero]; exact 𝔼.const _ 1
    · exact ForwardSolution.E_of_known 𝔼 (by omega) (ih n (by omega))

/-- Cochrane (2023), eq. (7.17), p. 225: **Theorem W, finite horizon.** Suppose no debt matures
after `T` (`A_t^{(m)} = 0` for `m > T`), each `A_t^{(t+j+1)}` is known at `t + j`, surpluses are
adapted and `y` solves the maturing-debt system. Then at every `t ≤ T`,
`y_t = ∑_{m ≤ T−t} β^m E_t(W_t^{(m)} s_{t+m})`, an exact identity under uncertainty. -/
theorem theoremW_finite (hpo : 𝔼.PullOut) {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {y s : ℕ → Ω → ℝ}
    {T : ℕ} (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    (hT : ∀ t m, T < m → A t m = 0) (hs : 𝔼.Adapted s)
    (hsys : ∀ t, MaturingSystem 𝔼 β A y s t) {t : ℕ} (ht : t ≤ T) :
    y t = ∑ m ∈ Finset.range (T - t + 1), β ^ m • 𝔼.E t (weight A t m * s (t + m)) := by
  suffices key : ∀ N t, T - t = N → t ≤ T →
      y t = ∑ m ∈ Finset.range (N + 1), β ^ m • 𝔼.E t (weight A t m * s (t + m)) from
    key _ t rfl ht
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro t hN ht
    -- the flow sum is finite
    have hfin : y t - s t = ∑ j ∈ Finset.range N,
        β ^ (j + 1) • 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) := by
      funext ω
      have hz : ∀ j ∉ Finset.range N,
          β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) ω = 0 := by
        intro j hj
        rw [Finset.mem_range, not_lt] at hj
        rw [hT t _ (by omega), zero_mul, map_zero, Pi.zero_apply, mul_zero]
      have := (hsys t ω).unique (hasSum_sum_of_ne_finset_zero hz)
      rw [Pi.sub_apply, this, Finset.sum_apply]
      rfl
    -- expand each later maturing value by the induction hypothesis
    have hexp : ∀ j ∈ Finset.range N, β ^ (j + 1) • 𝔼.E t (A t (t + (j + 1)) * y (t + (j + 1))) =
        ∑ m ∈ Finset.range (N - j), β ^ (j + 1 + m) • 𝔼.E t (A t (t + (j + 1)) *
          weight A (t + (j + 1)) m * s (t + (j + 1) + m)) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [ih (N - (j + 1)) (by omega) (t + (j + 1)) (by omega) (by omega),
        show N - (j + 1) + 1 = N - j by omega, Finset.mul_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hAk : 𝔼.E (t + (j + 1)) (A t (t + (j + 1))) = A t (t + (j + 1)) :=
        ForwardSolution.E_of_known 𝔼 (by omega) (hA t j)
      rw [mul_smul_comm, map_smul, ← hpo _ _ _ hAk, 𝔼.tower (by omega), smul_smul, ← pow_add,
        mul_assoc]
    rw [Finset.sum_range_succ', weight_zero, one_mul, pow_zero, one_smul, add_zero, hs t]
    rw [eq_add_of_sub_eq hfin, Finset.sum_congr rfl hexp, sum_triangle N
      (fun j m => β ^ (j + 1 + m) • 𝔼.E t (A t (t + (j + 1)) * weight A (t + (j + 1)) m *
        s (t + (j + 1) + m)))]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [weight_first_step, Finset.sum_mul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [show j + 1 + (k - j) = k + 1 by omega, show t + (j + 1) + (k - j) = t + (k + 1) by omega]

/-! ### Infinite horizon: the row condition -/

/-- Cochrane (2023), eq. (7.17), p. 225: the **row condition**: the sale fractions are bounded by a
deterministic sequence, `|A_t^{(t+j+1)}| ≤ a_j`, with `∑_j β^{j+1} a_j ≤ ρ` (convergent). With
`ρ < 1` this is a contraction condition on the system (7.14). -/
def RowBound (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (a : ℕ → ℝ) (ρ : ℝ) : Prop :=
  (∀ j, 0 ≤ a j) ∧ (∀ t j ω, |A t (t + (j + 1)) ω| ≤ a j) ∧
    Summable (fun j => β ^ (j + 1) * a j) ∧ ∑' j, β ^ (j + 1) * a j ≤ ρ

/-- Cochrane (2023), eq. (7.17), p. 226: the stationary dominating fractions
`(u, v) ↦ a_{v−u−1}`. -/
def domA (a : ℕ → ℝ) : ℕ → ℕ → ℝ := fun u v => a (v - u - 1)

/-- Cochrane (2023), eq. (7.17), p. 226: the dominating weights, the weights of the stationary
fractions `a`. -/
noncomputable def domWeight (a : ℕ → ℝ) : ℕ → ℝ := weight (domA a) 0

/-- Cochrane (2023), eq. (7.17), p. 226: the dominating weights do not depend on the start date. -/
theorem weight_domA (a : ℕ → ℝ) (m : ℕ) : ∀ u, weight (domA a) u m = domWeight a m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro u
    rcases m with _ | k
    · rw [domWeight, weight_zero, weight_zero]
    · rw [domWeight, weight_succ, weight_succ]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn' := Finset.mem_range.mp hn
      rw [ih n hn' u, ih n hn' 0]
      simp only [domA]
      congr 2
      omega

/-- Cochrane (2023), eq. (7.17), p. 226: the dominating weights are nonnegative. -/
theorem domWeight_nonneg {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (m : ℕ) : 0 ≤ domWeight a m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | k
    · rw [domWeight, weight_zero]; exact zero_le_one
    · rw [domWeight, weight_succ]
      refine Finset.sum_nonneg fun n hn => mul_nonneg (ha _) ?_
      exact ih n (Finset.mem_range.mp hn)

/-- Cochrane (2023), eq. (7.17), p. 226: first-step recursion for the dominating weights,
`w_{k+1} = ∑_{j ≤ k} a_j w_{k−j}`. -/
theorem domWeight_succ (a : ℕ → ℝ) (k : ℕ) :
    domWeight a (k + 1) = ∑ j ∈ Finset.range (k + 1), a j * domWeight a (k - j) := by
  rw [domWeight, weight_first_step]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weight_domA]
  simp only [domA]
  congr 2
  omega

/-- Cochrane (2023), eq. (7.17), p. 226: under the row condition, `|W_t^{(m)}| ≤ w_m`. -/
theorem abs_weight_le {β ρ : ℝ} {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} (hrow : RowBound β A a ρ)
    (m : ℕ) : ∀ t ω, |weight A t m ω| ≤ domWeight a m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro t ω
    rcases m with _ | k
    · rw [weight_zero, domWeight, weight_zero]; simp
    · rw [weight_succ, domWeight, weight_succ, Finset.sum_apply]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hn' : n ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [Pi.mul_apply, abs_mul]
      have hA := hrow.2.1 (t + n) (k - n) ω
      rw [show t + n + (k - n + 1) = t + (k + 1) by omega] at hA
      have hdA : domA a (0 + n) (0 + (k + 1)) = a (k - n) := by
        simp only [domA]; congr 1; omega
      rw [hdA]
      exact mul_le_mul hA (ih n (by omega) t ω) (abs_nonneg _) ((hrow.1 _))

/-- Cochrane (2023), eq. (7.17), p. 226: under the row condition the finite sums of
`β^m w_m` are bounded by `∑_{n<N} ρ^n`. -/
theorem sum_domWeight_le {β ρ : ℝ} (hβ0 : 0 ≤ β) (hρ0 : 0 ≤ ρ) {a : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ (j + 1) * a j ≤ ρ) (N : ℕ) :
    ∑ m ∈ Finset.range N, β ^ m * domWeight a m ≤ ∑ n ∈ Finset.range N, ρ ^ n := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | N
    · simp
    · rw [Finset.sum_range_succ', Finset.sum_range_succ', pow_zero, domWeight, weight_zero,
        mul_one, pow_zero]
      have hexp : ∑ k ∈ Finset.range N, β ^ (k + 1) * weight (domA a) 0 (k + 1) =
          ∑ j ∈ Finset.range N, β ^ (j + 1) * a j *
            ∑ m ∈ Finset.range (N - j), β ^ m * domWeight a m := by
        have : ∀ k, β ^ (k + 1) * weight (domA a) 0 (k + 1) =
            ∑ j ∈ Finset.range (k + 1),
              β ^ (j + 1) * a j * (β ^ (k - j) * domWeight a (k - j)) := by
          intro k
          rw [← domWeight, domWeight_succ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [show β ^ (k + 1) = β ^ (j + 1) * β ^ (k - j) by rw [← pow_add]; congr 1; omega]
          ring
        simp only [this]
        rw [← sum_triangle N (fun j m => β ^ (j + 1) * a j * (β ^ m * domWeight a m))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
      rw [hexp]
      have hstep : ∑ j ∈ Finset.range N, β ^ (j + 1) * a j *
          ∑ m ∈ Finset.range (N - j), β ^ m * domWeight a m ≤
          ∑ j ∈ Finset.range N, β ^ (j + 1) * a j * ∑ n ∈ Finset.range N, ρ ^ n := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (pow_nonneg hβ0 _) (ha j))
        refine (ih (N - j) (by omega)).trans ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le N j))
          fun n _ _ => pow_nonneg hρ0 n
      have hgeo : 0 ≤ ∑ n ∈ Finset.range N, ρ ^ n := Finset.sum_nonneg fun n _ => pow_nonneg hρ0 n
      rw [← Finset.sum_mul] at hstep
      have h2 := mul_le_mul_of_nonneg_right (hpart N) hgeo
      have h3 : ∑ i ∈ Finset.range N, ρ ^ (i + 1) = ρ * ∑ n ∈ Finset.range N, ρ ^ n := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_succ' ρ i
      rw [h3]
      linarith

/-- Cochrane (2023), eq. (7.17), p. 226: under the row condition with `ρ < 1`, `∑_m β^m w_m`
converges, with sum at most `1/(1−ρ)`. -/
theorem summable_domWeight {β ρ : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (hrow : RowBound β A a ρ) :
    Summable (fun m => β ^ m * domWeight a m) ∧ ∑' m, β ^ m * domWeight a m ≤ 1 / (1 - ρ) := by
  have hnn : ∀ j, 0 ≤ β ^ (j + 1) * a j := fun j => mul_nonneg (pow_nonneg hβ0 _) (hrow.1 j)
  have hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ (j + 1) * a j ≤ ρ := fun N =>
    (hrow.2.2.1.sum_le_tsum _ fun j _ => hnn j).trans hrow.2.2.2
  have hρ0 : 0 ≤ ρ := (tsum_nonneg hnn).trans hrow.2.2.2
  have hbound : ∀ N, ∑ m ∈ Finset.range N, β ^ m * domWeight a m ≤ 1 / (1 - ρ) := by
    intro N
    refine (sum_domWeight_le hβ0 hρ0 hrow.1 hpart N).trans ?_
    have hg := summable_geometric_of_lt_one hρ0 hρ1
    refine (hg.sum_le_tsum _ fun n _ => pow_nonneg hρ0 n).trans ?_
    rw [tsum_geometric_of_lt_one hρ0 hρ1, one_div]
  have hnn' : ∀ m, 0 ≤ β ^ m * domWeight a m := fun m =>
    mul_nonneg (pow_nonneg hβ0 m) (domWeight_nonneg hrow.1 m)
  exact ⟨summable_of_sum_range_le hnn' hbound, Real.tsum_le_of_sum_range_le hnn' hbound⟩

/-- Cochrane (2023), eq. (7.17), p. 225: the terms `β^m E_t(W_t^{(m)} s_{t+m})` of the weighted
present value. -/
noncomputable def formulaTerm (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) (t m : ℕ) (ω : Ω) :
    ℝ :=
  β ^ m * 𝔼.E t (weight A t m * s (t + m)) ω

/-- Cochrane (2023), eq. (7.17), p. 225: the weighted present value
`E_t ∑_m β^m W_t^{(m)} s_{t+m}`. -/
noncomputable def formulaW (β : ℝ) (A : ℕ → ℕ → Ω → ℝ) (s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' m, formulaTerm 𝔼 β A s t m ω

/-- Cochrane (2023), eq. (7.17), p. 225: under the row condition and `|s| ≤ M`, the terms of (7.17)
are dominated by `β^m w_m M`. -/
theorem abs_formulaTerm_le {β ρ M : ℝ} (hβ0 : 0 ≤ β) {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (hrow : RowBound β A a ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M) (t m : ℕ) (ω : Ω) :
    |formulaTerm 𝔼 β A s t m ω| ≤ β ^ m * domWeight a m * M := by
  rw [formulaTerm, abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
  refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => ?_) t ω) (pow_nonneg hβ0 m)
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (abs_weight_le hrow m t ω') (hsb _ ω') (abs_nonneg _)
    (domWeight_nonneg hrow.1 m)

/-- Cochrane (2023), eq. (7.17), p. 225: under the row condition (`ρ < 1`) and bounded surpluses,
the series (7.17) converges absolutely and `|E_t ∑ β^m W s| ≤ M/(1−ρ)`. -/
theorem formulaW_summable {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (hrow : RowBound β A a ρ) {s : ℕ → Ω → ℝ} (hsb : ∀ t ω, |s t ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    Summable (fun m => formulaTerm 𝔼 β A s t m ω) ∧ |formulaW 𝔼 β A s t ω| ≤ M / (1 - ρ) := by
  obtain ⟨hsum, hle⟩ := summable_domWeight hβ0 hρ1 hrow
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb t ω)
  have hdom : Summable (fun m => β ^ m * domWeight a m * M) := hsum.mul_right M
  have hs : Summable (fun m => formulaTerm 𝔼 β A s t m ω) :=
    Summable.of_norm_bounded hdom (fun m => by
      rw [Real.norm_eq_abs]; exact abs_formulaTerm_le 𝔼 hβ0 hrow hsb t m ω)
  refine ⟨hs, ?_⟩
  have h1 : |formulaW 𝔼 β A s t ω| ≤ ∑' m, β ^ m * domWeight a m * M := by
    rw [formulaW]
    have h0 := norm_tsum_le_tsum_norm (f := fun m => formulaTerm 𝔼 β A s t m ω)
      (by simpa only [Real.norm_eq_abs] using hs.abs)
    simp only [Real.norm_eq_abs] at h0
    refine h0.trans ?_
    exact Summable.tsum_le_tsum (fun m => abs_formulaTerm_le 𝔼 hβ0 hrow hsb t m ω) hs.abs hdom
  refine h1.trans ?_
  rw [tsum_mul_right, div_eq_mul_inv, mul_comm M]
  exact mul_le_mul_of_nonneg_right (by simpa using hle) hM

/-- Cochrane (2023), eq. (7.17), p. 225: **the weighted present value solves the system.** Under
the row condition (`ρ < 1`), with each `A_t^{(t+j+1)}` known at `t + j` and bounded adapted
surpluses, `y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}` satisfies the flow conditions (7.14) at every date.
The proof substitutes and regroups an absolutely convergent double series by antidiagonals,
using `weight_first_step`. -/
theorem formulaW_solves (hpo : 𝔼.PullOut) {β ρ M : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} (hrow : RowBound β A a ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (t : ℕ) :
    MaturingSystem 𝔼 β A (formulaW 𝔼 β A s) s t := by
  intro ω
  obtain ⟨hsumw, -⟩ := summable_domWeight hβ0 hρ1 hrow
  have hM : 0 ≤ M := (abs_nonneg _).trans (hsb t ω)
  set Gf : ℕ × ℕ → ℝ := fun p => β ^ (p.1 + 1) * (β ^ p.2 *
    𝔼.E t (A t (t + (p.1 + 1)) * (weight A (t + (p.1 + 1)) p.2 * s (t + (p.1 + 1) + p.2))) ω)
    with hGf
  have hEb : ∀ (j m : ℕ) (u : ℕ) (ω₀ : Ω), |𝔼.E u (A t (t + (j + 1)) *
      (weight A (t + (j + 1)) m * s (t + (j + 1) + m))) ω₀| ≤ a j * (domWeight a m * M) := by
    intro j m u ω₀
    refine 𝔼.abs_E_le (fun ω' => ?_) u ω₀
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hrow.2.1 t j ω') (mul_le_mul (abs_weight_le hrow _ _ ω') (hsb _ ω')
      (abs_nonneg _) (domWeight_nonneg hrow.1 _)) (by positivity) (hrow.1 _)
  have hGb : ∀ p : ℕ × ℕ, ‖Gf p‖ ≤ (β ^ (p.1 + 1) * a p.1) * (β ^ p.2 * domWeight a p.2 * M) := by
    intro p
    rw [Real.norm_eq_abs, hGf]
    simp only [abs_mul, abs_pow, abs_of_nonneg hβ0]
    have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hEb p.1 p.2 t ω)
      (pow_nonneg hβ0 p.2)) (pow_nonneg hβ0 (p.1 + 1))
    refine h1.trans (le_of_eq ?_)
    ring
  have hprod : Summable (fun p : ℕ × ℕ => (β ^ (p.1 + 1) * a p.1) *
      (β ^ p.2 * domWeight a p.2 * M)) :=
    summable_mul_of_summable_norm (f := fun j => β ^ (j + 1) * a j)
      (g := fun m => β ^ m * domWeight a m * M)
      (by simpa only [Real.norm_eq_abs] using hrow.2.2.1.abs)
      (by simpa only [Real.norm_eq_abs] using (hsumw.mul_right M).abs)
  have hGsum : Summable Gf := Summable.of_norm_bounded hprod hGb
  -- (i) the fibres in `j`
  have hfib : ∀ j, HasSum (fun m => Gf (j, m))
      (β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * formulaW 𝔼 β A s (t + (j + 1))) ω) := by
    intro j
    have hAk : 𝔼.E (t + (j + 1)) (A t (t + (j + 1))) = A t (t + (j + 1)) :=
      ForwardSolution.E_of_known 𝔼 (by omega) (hA t j)
    have hfun : A t (t + (j + 1)) * formulaW 𝔼 β A s (t + (j + 1)) = fun ω' =>
        ∑' m, A t (t + (j + 1)) ω' * formulaTerm 𝔼 β A s (t + (j + 1)) m ω' := by
      funext ω'
      rw [Pi.mul_apply, formulaW, tsum_mul_left]
    have hu : Summable (fun m => a j * (β ^ m * domWeight a m * M)) :=
      (hsumw.mul_right M).mul_left (a j)
    have hf : ∀ m ω', |A t (t + (j + 1)) ω' * formulaTerm 𝔼 β A s (t + (j + 1)) m ω'| ≤
        a j * (β ^ m * domWeight a m * M) := by
      intro m ω'
      rw [abs_mul]
      exact mul_le_mul (hrow.2.1 t j ω') (abs_formulaTerm_le 𝔼 hβ0 hrow hsb _ m ω')
        (abs_nonneg _) (hrow.1 j)
    have hterm : ∀ m, 𝔼.E t (fun ω' => A t (t + (j + 1)) ω' *
        formulaTerm 𝔼 β A s (t + (j + 1)) m ω') ω = β ^ m * 𝔼.E t (A t (t + (j + 1)) *
          (weight A (t + (j + 1)) m * s (t + (j + 1) + m))) ω := by
      intro m
      have hfm : (fun ω' => A t (t + (j + 1)) ω' * formulaTerm 𝔼 β A s (t + (j + 1)) m ω') =
          β ^ m • 𝔼.E (t + (j + 1)) (A t (t + (j + 1)) *
            (weight A (t + (j + 1)) m * s (t + (j + 1) + m))) := by
        rw [hpo _ _ _ hAk]
        funext ω'
        simp only [formulaTerm, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
        ring
      rw [hfm, map_smul, 𝔼.tower (by omega)]
      rfl
    rw [hfun, ForwardSolution.E_tsum_dom 𝔼 hu hf t ω]
    simp only [hterm]
    have hinner : Summable (fun m => β ^ m * 𝔼.E t (A t (t + (j + 1)) *
        (weight A (t + (j + 1)) m * s (t + (j + 1) + m))) ω) :=
      Summable.of_norm_bounded ((hsumw.mul_right M).mul_left (a j)) (fun m => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
        have := mul_le_mul_of_nonneg_left (hEb j m t ω) (pow_nonneg hβ0 m)
        refine this.trans (le_of_eq ?_)
        ring)
    exact hinner.hasSum.mul_left (β ^ (j + 1))
  -- (ii) summing the fibres
  have hrowsum := hGsum.hasSum.prod_fiberwise hfib
  -- (iii) summing by antidiagonals
  have hdiag : HasSum (fun k => formulaTerm 𝔼 β A s t (k + 1) ω) (∑' p, Gf p) := by
    have h1 := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff (f := Gf)).mpr
      hGsum.hasSum
    have h2 := h1.sigma (fun k => hasSum_fintype _)
    convert h2 using 1
    funext k
    simp only [Function.comp_apply, Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd_apply]
    rw [Finset.sum_coe_sort (Finset.antidiagonal k) Gf,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, formulaTerm, weight_first_step,
      Finset.sum_mul, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [hGf]
    rw [show t + (j + 1) + (k - j) = t + (k + 1) by omega, mul_assoc,
      show β ^ (k + 1) = β ^ (j + 1) * β ^ (k - j) by rw [← pow_add]; congr 1; omega]
    ring
  -- (iv) the value at `t`
  obtain ⟨hzs, -⟩ := formulaW_summable 𝔼 hβ0 hρ1 hrow hsb t ω
  have hz : formulaW 𝔼 β A s t ω = s t ω + ∑' p, Gf p := by
    rw [formulaW, hzs.tsum_eq_zero_add, hdiag.tsum_eq]
    simp [formulaTerm, weight_zero, hs t]
  rw [hz, add_sub_cancel_left]
  exact hrowsum

/-- Cochrane (2023), §7.4, p. 225: **uniqueness under the row condition.** If `ρ < 1`, the only
bounded solution of the homogeneous system `d_t = ∑_j β^{j+1} E_t(A_t^{(t+j+1)} d_{t+j+1})` is
zero. -/
theorem unique_of_row {β ρ K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1) {A : ℕ → ℕ → Ω → ℝ}
    {a : ℕ → ℝ} (hrow : RowBound β A a ρ) {d : ℕ → Ω → ℝ}
    (hd : ∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω)
      (d t ω)) (hK : ∀ t ω, |d t ω| ≤ K) : d = 0 := by
  have hnn : ∀ j, 0 ≤ β ^ (j + 1) * a j := fun j => mul_nonneg (pow_nonneg hβ0 _) (hrow.1 j)
  have hρ0 : 0 ≤ ρ := (tsum_nonneg hnn).trans hrow.2.2.2
  have hstep : ∀ n t ω, |d t ω| ≤ ρ ^ n * K := by
    intro n
    induction n with
    | zero => intro t ω; simpa using hK t ω
    | succ n ih =>
      intro t ω
      have hK0 : 0 ≤ ρ ^ n * K := (abs_nonneg _).trans (ih t ω)
      have hb : ∀ j, |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω| ≤
          β ^ (j + 1) * a j * (ρ ^ n * K) := by
        intro j
        rw [abs_mul, abs_pow, abs_of_nonneg hβ0, mul_assoc]
        refine mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => ?_) t ω) (pow_nonneg hβ0 _)
        rw [Pi.mul_apply, abs_mul]
        exact mul_le_mul (hrow.2.1 t j ω') (ih _ ω') (abs_nonneg _) (hrow.1 j)
      have hH : HasSum (fun j => β ^ (j + 1) * a j * (ρ ^ n * K))
          ((∑' j, β ^ (j + 1) * a j) * (ρ ^ n * K)) := hrow.2.2.1.hasSum.mul_right _
      have h1 := hasSum_le (fun j => (le_abs_self _).trans (hb j)) (hd t ω) hH
      have h2 := hasSum_le (fun j => (neg_le_abs _).trans (hb j)) (hd t ω).neg hH
      have h3 : (∑' j, β ^ (j + 1) * a j) * (ρ ^ n * K) ≤ ρ ^ (n + 1) * K := by
        rw [pow_succ, mul_comm (ρ ^ n) ρ, mul_assoc]
        exact mul_le_mul_of_nonneg_right hrow.2.2.2 hK0
      rw [abs_le]
      constructor <;> linarith
  funext t ω
  have hlim : Tendsto (fun n : ℕ => ρ ^ n * K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const K
  have := ge_of_tendsto' hlim (fun n => hstep n t ω)
  simpa using abs_nonpos_iff.mp this

/-- Cochrane (2023), eq. (7.17), p. 225: **Theorem W, infinite horizon.** Under the row condition
(`ρ < 1`), with each `A_t^{(t+j+1)}` known at `t + j` and bounded adapted surpluses, every bounded
solution of the flow conditions (7.14) is given by the weighted present value (7.17):
`y_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}`, an absolutely convergent series. -/
theorem theoremW (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {A : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} (hrow : RowBound β A a ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (A t (t + (j + 1))) = A t (t + (j + 1)))
    {s y : ℕ → Ω → ℝ} (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hyb : ∀ t ω, |y t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β A s t m ω) (y t ω) := by
  have hz := formulaW_solves 𝔼 hpo hβ0 hρ1 hrow hA hs hsb
  have hd : y - formulaW 𝔼 β A s = 0 := by
    refine unique_of_row 𝔼 hβ0 hρ1 hrow (K := K + M / (1 - ρ)) (fun u ω' => ?_) (fun u ω' => ?_)
    · have := (hy u ω').sub (hz u ω')
      convert this using 1
      · funext j
        simp only [Pi.sub_apply, mul_sub, map_sub]
      · simp only [Pi.sub_apply]; ring
    · rw [Pi.sub_apply]
      exact (abs_sub _ _).trans
        (add_le_add (hyb u ω') (formulaW_summable 𝔼 hβ0 hρ1 hrow hsb u ω').2)
  have hyz : y t ω = formulaW 𝔼 β A s t ω := by
    have := congrFun (congrFun hd t) ω
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    linarith
  rw [hyz]
  exact (formulaW_summable 𝔼 hβ0 hρ1 hrow hsb t ω).1.hasSum

/-! ### Uniqueness without buy-backs (the column condition) -/

/-- Cochrane (2023), §7.4, p. 225 (the "column" lemma behind uniqueness without buy-backs): let
`u ≥ 0` be summable and `G ≥ 0` with `G t m = 0` for `m ≤ t`. If `u_t ≤ ∑_m G t m` for every
`t ≥ τ` and every column satisfies `∑_{t<m} G t m ≤ u_m`, then `u_τ ≤ 0`. -/
theorem col_lemma {u : ℕ → ℝ} {G : ℕ → ℕ → ℝ} (hu0 : ∀ t, 0 ≤ u t) (hus : Summable u)
    (hG0 : ∀ t m, 0 ≤ G t m) (hGz : ∀ t m, m ≤ t → G t m = 0) {τ : ℕ}
    (hGs : ∀ t, τ ≤ t → Summable (G t)) (hH1 : ∀ t, τ ≤ t → u t ≤ ∑' m, G t m)
    (hcol : ∀ m, ∑ t ∈ Finset.range m, G t m ≤ u m) : u τ ≤ 0 := by
  classical
  set F : ℕ → ℕ → ℝ := fun k m => G (τ + k) m with hF
  set v : ℕ → ℝ := fun m => if τ < m then u m else 0 with hv
  have hFz : ∀ k m, m ≤ k → F k m = 0 := fun k m h => hGz _ _ (by omega)
  have hslm : ∀ m, Summable (fun k => F k m) := fun m =>
    summable_of_ne_finset_zero (s := Finset.range m) fun k hk =>
      hFz k m (by simpa using hk)
  have hFm : ∀ m, ∑' k, F k m ≤ v m := by
    intro m
    rw [tsum_eq_sum (s := Finset.range m) fun k hk => hFz k m (by simpa using hk)]
    by_cases hτm : τ < m
    · simp only [hv, hτm, ↓reduceIte, hF]
      have hre : ∑ x ∈ Finset.range m, G (τ + x) m = ∑ t ∈ Finset.Ico τ (τ + m), G t m := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      rw [hre]
      refine le_trans ?_ (hcol m)
      rw [← Finset.sum_filter_of_ne (p := fun t => t < m) (fun t _ h => by
        by_contra hc; exact h (hGz t m (by omega)))]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun t ht => by simp only [Finset.mem_filter] at ht; exact Finset.mem_range.mpr ht.2)
        fun t _ _ => hG0 t m
    · simp only [hv, hτm, ↓reduceIte]
      exact le_of_eq (Finset.sum_eq_zero fun k _ => hGz _ _ (by omega))
  have hv0 : ∀ m, 0 ≤ v m := fun m => by
    simp only [hv]; split_ifs <;> simp [hu0 m]
  have hvs : Summable v := Summable.of_nonneg_of_le hv0
    (fun m => by simp only [hv]; split_ifs <;> simp [hu0 m]) hus
  have hH : Summable (fun p : ℕ × ℕ => F p.2 p.1) := by
    rw [summable_prod_of_nonneg (fun p => hG0 _ _)]
    exact ⟨fun m => hslm m, Summable.of_nonneg_of_le (fun m => tsum_nonneg fun k => hG0 _ _)
      hFm hvs⟩
  have hFsum : Summable (Function.uncurry F) := hH.prod_symm
  have hslk : ∀ k, Summable (F k) := fun k => hGs (τ + k) (by omega)
  have hcomm : ∑' m, ∑' k, F k m = ∑' k, ∑' m, F k m := hFsum.tsum_comm' hslk hslm
  have hus' : Summable (fun k => u (τ + k)) := by
    simpa [add_comm] using (summable_nat_add_iff τ).mpr hus
  have h1 : ∑' k, u (τ + k) ≤ ∑' k, ∑' m, F k m :=
    Summable.tsum_le_tsum (fun k => hH1 (τ + k) (by omega)) hus' hFsum.prod
  have h2 : ∑' m, ∑' k, F k m ≤ ∑' m, v m :=
    Summable.tsum_le_tsum hFm (Summable.of_nonneg_of_le (fun m => tsum_nonneg fun k => hG0 _ _)
      hFm hvs) hvs
  have h3 : ∑' m, v m = ∑' k, u (τ + (k + 1)) := by
    have hfin : ∑ i ∈ Finset.range (τ + 1), v i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [hv, show ¬ τ < i by have := Finset.mem_range.mp hi; omega, ↓reduceIte]
    have := (hasSum_nat_add_iff' (τ + 1)).mpr hvs.hasSum
    rw [hfin, sub_zero] at this
    rw [← this.tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [hv, show τ < k + (τ + 1) by omega, ↓reduceIte]
    congr 1
    omega
  have h4 : ∑' k, u (τ + k) = u τ + ∑' k, u (τ + (k + 1)) := by
    rw [hus'.tsum_eq_zero_add, add_zero]
  linarith

/-- Cochrane (2023), §7.4: `|E_t f| ≤ E_t |f|`. -/
theorem abs_E_le_E_abs (t : ℕ) (f : Ω → ℝ) (ω : Ω) :
    |𝔼.E t f ω| ≤ 𝔼.E t (fun ω' => |f ω'|) ω := by
  have h1 := 𝔼.mono t (fun ω' => le_abs_self (f ω')) ω
  have h2 := 𝔼.mono t (fun ω' => neg_abs_le (f ω')) ω
  have h3 : 𝔼.E t (fun ω' => -|f ω'|) ω = -𝔼.E t (fun ω' => |f ω'|) ω := by
    rw [show (fun ω' => -|f ω'|) = -(fun ω' => |f ω'|) from rfl, map_neg, Pi.neg_apply]
  rw [abs_le]
  constructor <;> linarith

/-- Cochrane (2023), §7.4, p. 225: **uniqueness without buy-backs.** Suppose the sale fractions are
nonnegative and each column sums to at most one, `∑_{t<m} A_t^{(m)} ≤ 1` (true when the government
never buys back debt and inherited positions are nonnegative), and `0 < β < 1`. Then the only
bounded solution of the homogeneous system `d_t = ∑_j β^{j+1} E_t(A_t^{(t+j+1)} d_{t+j+1})` is
zero, under uncertainty. -/
theorem unique_of_noBuyback {β K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {A : ℕ → ℕ → Ω → ℝ}
    (hA0 : ∀ t m ω, t < m → 0 ≤ A t m ω)
    (hcolA : ∀ m ω, ∑ t ∈ Finset.range m, A t m ω ≤ 1) {d : ℕ → Ω → ℝ}
    (hd : ∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω)
      (d t ω)) (hK : ∀ t ω, |d t ω| ≤ K) : d = 0 := by
  classical
  have hA1 : ∀ t m ω, t < m → A t m ω ≤ 1 := fun t m ω h =>
    (Finset.single_le_sum (fun i hi => hA0 i m ω (Finset.mem_range.mp hi))
      (Finset.mem_range.mpr h)).trans (hcolA m ω)
  set e : ℕ → Ω → ℝ := fun t ω => |d t ω| with he
  have he0 : ∀ t ω, 0 ≤ e t ω := fun t ω => abs_nonneg _
  have heK : ∀ t ω, e t ω ≤ K := hK
  have hsumβ : Summable (fun j : ℕ => β ^ (j + 1) * K) :=
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left β).mul_right K |>.congr fun j => by ring
  -- bounds on the terms
  have hAe : ∀ (t j : ℕ) (u : ℕ) (ω : Ω), 0 ≤ 𝔼.E u (A t (t + (j + 1)) * e (t + (j + 1))) ω ∧
      𝔼.E u (A t (t + (j + 1)) * e (t + (j + 1))) ω ≤ K := by
    intro t j u ω
    have hlo : (fun _ => (0 : ℝ)) ≤ A t (t + (j + 1)) * e (t + (j + 1)) := fun ω' =>
      mul_nonneg (hA0 _ _ ω' (by omega)) (he0 _ ω')
    have hhi : A t (t + (j + 1)) * e (t + (j + 1)) ≤ fun _ => K := fun ω' =>
      (mul_le_of_le_one_left (he0 _ ω') (hA1 _ _ ω' (by omega))).trans (heK _ ω')
    have h1 := 𝔼.mono u hlo ω
    have h2 := 𝔼.mono u hhi ω
    rw [𝔼.const] at h1 h2
    exact ⟨h1, h2⟩
  -- `d` is adapted
  have hdad : ∀ t, 𝔼.E t (d t) = d t := by
    intro t
    funext ω
    have hfun : d t = fun ω' => ∑' j, β ^ (j + 1) *
        𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω' := by
      funext ω'; exact (hd t ω').tsum_eq.symm
    have hb : ∀ j ω', |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω'| ≤
        β ^ (j + 1) * K := by
      intro j ω'
      rw [abs_mul, abs_pow, abs_of_pos hβ0]
      refine mul_le_mul_of_nonneg_left ((abs_E_le_E_abs 𝔼 _ _ ω').trans ?_) (pow_nonneg hβ0.le _)
      have : (fun ω'' => |(A t (t + (j + 1)) * d (t + (j + 1))) ω''|) =
          A t (t + (j + 1)) * e (t + (j + 1)) := by
        funext ω''
        simp only [Pi.mul_apply, abs_mul, he,
          abs_of_nonneg (hA0 _ _ ω'' (by omega : t < t + (j + 1)))]
      rw [this]
      exact (hAe t j t ω').2
    conv_lhs => rw [hfun]
    rw [ForwardSolution.E_tsum_dom 𝔼 hsumβ hb t ω]
    rw [← (hd t ω).tsum_eq]
    refine tsum_congr fun j => ?_
    rw [show (fun ω' => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω') =
      β ^ (j + 1) • 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) from rfl, map_smul, 𝔼.E_E_self]
    rfl
  -- the pointwise inequality `e_t ≤ ∑ β^{j+1} E_t(A e)`
  have hR : ∀ t ω, e t ω ≤ ∑' j, β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω := by
    intro t ω
    have hsR : Summable (fun j => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω) :=
      Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hβ0.le _) (hAe t j t ω).1)
        (fun j => mul_le_mul_of_nonneg_left (hAe t j t ω).2 (pow_nonneg hβ0.le _)) hsumβ
    have hle : ∀ j, |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω| ≤
        β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω := by
      intro j
      rw [abs_mul, abs_pow, abs_of_pos hβ0]
      have hfe : (fun ω'' => |(A t (t + (j + 1)) * d (t + (j + 1))) ω''|) =
          A t (t + (j + 1)) * e (t + (j + 1)) := by
        funext ω''
        simp only [Pi.mul_apply, abs_mul, he,
          abs_of_nonneg (hA0 _ _ ω'' (by omega : t < t + (j + 1)))]
      have := abs_E_le_E_abs 𝔼 t (A t (t + (j + 1)) * d (t + (j + 1))) ω
      rw [hfe] at this
      exact mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le _)
    have h1 := hasSum_le (fun j => (le_abs_self _).trans (hle j)) (hd t ω) hsR.hasSum
    have h2 := hasSum_le (fun j => (neg_le_abs _).trans (hle j)) (hd t ω).neg hsR.hasSum
    simp only [he]
    rw [abs_le]
    constructor <;> linarith
  -- apply the column lemma at each date `τ` and state `ω`
  funext τ ω
  set u : ℕ → ℝ := fun t => β ^ t * 𝔼.E τ (e t) ω with hu
  set G : ℕ → ℕ → ℝ := fun t m => if t < m then β ^ m * 𝔼.E τ (A t m * e m) ω else 0 with hG
  have hEe : ∀ t, 0 ≤ 𝔼.E τ (e t) ω ∧ 𝔼.E τ (e t) ω ≤ K := by
    intro t
    have h1 := 𝔼.mono τ (show (fun _ => (0 : ℝ)) ≤ e t from fun ω' => he0 t ω') ω
    have h2 := 𝔼.mono τ (show e t ≤ fun _ => K from fun ω' => heK t ω') ω
    rw [𝔼.const] at h1 h2
    exact ⟨h1, h2⟩
  have hu0 : ∀ t, 0 ≤ u t := fun t => mul_nonneg (pow_nonneg hβ0.le t) (hEe t).1
  have hus : Summable u := Summable.of_nonneg_of_le hu0
    (fun t => mul_le_mul_of_nonneg_left (hEe t).2 (pow_nonneg hβ0.le t))
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K)
  have hGnn : ∀ t m, t < m → 0 ≤ 𝔼.E τ (A t m * e m) ω ∧ 𝔼.E τ (A t m * e m) ω ≤ K := by
    intro t m htm
    obtain ⟨j, rfl⟩ : ∃ j, m = t + (j + 1) := ⟨m - t - 1, by omega⟩
    exact hAe t j τ ω
  have hG0 : ∀ t m, 0 ≤ G t m := fun t m => by
    simp only [hG]; split_ifs with h
    · exact mul_nonneg (pow_nonneg hβ0.le _) (hGnn t m h).1
    · exact le_rfl
  have hGz : ∀ t m, m ≤ t → G t m = 0 := fun t m h => by
    simp only [hG, show ¬ t < m by omega, ↓reduceIte]
  have hGs : ∀ t, Summable (G t) := fun t =>
    Summable.of_nonneg_of_le (hG0 t) (fun m => by
      simp only [hG]; split_ifs with h
      · exact mul_le_mul_of_nonneg_left (hGnn t m h).2 (pow_nonneg hβ0.le _)
      · exact mul_nonneg (pow_nonneg hβ0.le _) ((abs_nonneg _).trans (hK 0 ω)))
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K)
  have hH1 : ∀ t, τ ≤ t → u t ≤ ∑' m, G t m := by
    intro t ht
    -- `E_τ e_t ≤ ∑ β^{j+1} E_τ(A e)`
    have hb : ∀ j ω', |β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω'| ≤
        β ^ (j + 1) * K := by
      intro j ω'
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg hβ0.le _) (hAe t j t ω').1)]
      exact mul_le_mul_of_nonneg_left (hAe t j t ω').2 (pow_nonneg hβ0.le _)
    have hmono := 𝔼.mono τ (show e t ≤ fun ω' => ∑' j, β ^ (j + 1) *
        𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω' from fun ω' => hR t ω') ω
    rw [ForwardSolution.E_tsum_dom 𝔼 hsumβ hb τ ω] at hmono
    have hterm : ∀ j, 𝔼.E τ (fun ω' => β ^ (j + 1) *
        𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω') ω =
        β ^ (j + 1) * 𝔼.E τ (A t (t + (j + 1)) * e (t + (j + 1))) ω := by
      intro j
      rw [show (fun ω' => β ^ (j + 1) * 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) ω') =
        β ^ (j + 1) • 𝔼.E t (A t (t + (j + 1)) * e (t + (j + 1))) from rfl, map_smul,
        𝔼.tower ht]
      rfl
    simp only [hterm] at hmono
    have hshift : ∑' m, G t m = ∑' j, β ^ t * (β ^ (j + 1) *
        𝔼.E τ (A t (t + (j + 1)) * e (t + (j + 1))) ω) := by
      have hfin : ∑ i ∈ Finset.range (t + 1), G t i = 0 :=
        Finset.sum_eq_zero fun i hi => hGz t i (by have := Finset.mem_range.mp hi; omega)
      have := (hasSum_nat_add_iff' (t + 1)).mpr (hGs t).hasSum
      rw [hfin, sub_zero] at this
      rw [← this.tsum_eq]
      refine tsum_congr fun j => ?_
      rw [show j + (t + 1) = t + (j + 1) by omega]
      simp only [hG, show t < t + (j + 1) by omega, ↓reduceIte]
      ring
    rw [hshift, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hmono (pow_nonneg hβ0.le t)
  have hcol : ∀ m, ∑ t ∈ Finset.range m, G t m ≤ u m := by
    intro m
    have hsum : ∑ t ∈ Finset.range m, G t m =
        β ^ m * 𝔼.E τ ((∑ t ∈ Finset.range m, A t m) * e m) ω := by
      rw [Finset.sum_mul, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [hG, Finset.mem_range.mp ht, ↓reduceIte]
    rw [hsum]
    refine mul_le_mul_of_nonneg_left (𝔼.mono τ (fun ω' => ?_) ω) (pow_nonneg hβ0.le m)
    simp only [Pi.mul_apply, Finset.sum_apply]
    exact mul_le_of_le_one_left (he0 m ω') (hcolA m ω')
  have hfin := col_lemma hu0 hus hG0 hGz (fun t _ => hGs t) hH1 hcol
  have hEτ : 𝔼.E τ (e τ) ω ≤ 0 := by
    have hp : 0 < β ^ τ := pow_pos hβ0 τ
    simp only [hu] at hfin
    nlinarith [(hEe τ).1]
  have habs : |d τ ω| ≤ 0 := by
    have := abs_E_le_E_abs 𝔼 τ (d τ) ω
    rw [hdad τ] at this
    exact this.trans hEτ
  simpa using abs_nonpos_iff.mp habs

/-! ### When the present-value relations determine the price level -/

/-- Cochrane (2023), §7.4, p. 225: the difference of two solutions of the maturing-debt system with
the same surpluses solves the homogeneous system. -/
theorem homogeneous_of_two {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {y y' s : ℕ → Ω → ℝ}
    (hy : ∀ t, MaturingSystem 𝔼 β A y s t) (hy' : ∀ t, MaturingSystem 𝔼 β A y' s t) (t : ℕ)
    (ω : Ω) : HasSum (fun j : ℕ => β ^ (j + 1) *
      𝔼.E t (A t (t + (j + 1)) * (y - y') (t + (j + 1))) ω) ((y - y') t ω) := by
  have := (hy t ω).sub (hy' t ω)
  convert this using 1
  · funext j
    simp only [Pi.sub_apply, mul_sub, map_sub]
  · simp only [Pi.sub_apply]; ring

/-- Cochrane (2023), §7.4, pp. 225–226: given one bounded solution, bounded solutions of the
maturing-debt system are unique if and only if the homogeneous system has no nonzero bounded
solution. -/
theorem unique_iff_homogeneous {β : ℝ} {A : ℕ → ℕ → Ω → ℝ} {y₀ s : ℕ → Ω → ℝ}
    (hy₀ : ∀ t, MaturingSystem 𝔼 β A y₀ s t) (hb₀ : ∃ K, ∀ t ω, |y₀ t ω| ≤ K) :
    (∀ y, (∀ t, MaturingSystem 𝔼 β A y s t) → (∃ K, ∀ t ω, |y t ω| ≤ K) → y = y₀) ↔
      ∀ d : ℕ → Ω → ℝ, (∀ t ω, HasSum (fun j : ℕ => β ^ (j + 1) *
        𝔼.E t (A t (t + (j + 1)) * d (t + (j + 1))) ω) (d t ω)) →
        (∃ K, ∀ t ω, |d t ω| ≤ K) → d = 0 := by
  constructor
  · intro hu d hd hdb
    have hsol : ∀ t, MaturingSystem 𝔼 β A (y₀ + d) s t := by
      intro t ω
      have := (hy₀ t ω).add (hd t ω)
      convert this using 1
      · funext j
        simp only [Pi.add_apply, mul_add, map_add]
      · simp only [Pi.add_apply]; ring
    obtain ⟨K₀, hK₀⟩ := hb₀
    obtain ⟨K, hK⟩ := hdb
    have := hu (y₀ + d) hsol ⟨K₀ + K, fun t ω => (abs_add_le _ _).trans
      (add_le_add (hK₀ t ω) (hK t ω))⟩
    funext t ω
    have h := congrFun (congrFun this t) ω
    simp only [Pi.add_apply] at h
    simp only [Pi.zero_apply]
    linarith
  · intro hh y hy hyb
    have := hh (y - y₀) (homogeneous_of_two 𝔼 hy hy₀) (by
      obtain ⟨K, hK⟩ := hyb
      obtain ⟨K₀, hK₀⟩ := hb₀
      exact ⟨K + K₀, fun t ω => (abs_sub _ _).trans (add_le_add (hK t ω) (hK₀ t ω))⟩)
    exact sub_eq_zero.mp this

/-- Cochrane (2023), §7.4, p. 225: the government never buys back debt (`B_t^{(m)} ≥ B_{t−1}^{(m)}`
for `t < m`), inherited positions are nonnegative and the debt coming due is positive. -/
def NoBuyback (D : ℕ → ℕ → Ω → ℝ) : Prop :=
  (∀ m ω, 0 ≤ D 0 m ω) ∧ (∀ t m ω, t < m → D t m ω ≤ D (t + 1) m ω) ∧ ∀ m ω, 0 < D m m ω

/-- Cochrane (2023), §7.4: without buy-backs, debt outstanding is nonnegative up to maturity. -/
theorem NoBuyback.nonneg {D : ℕ → ℕ → Ω → ℝ} (h : NoBuyback D) (t m : ℕ) (htm : t ≤ m)
    (ω : Ω) : 0 ≤ D t m ω := by
  induction t with
  | zero => exact h.1 m ω
  | succ t ih => exact (ih (by omega)).trans (h.2.1 t m ω (by omega))

/-- Cochrane (2023), §7.4: without buy-backs the sale fractions are nonnegative. -/
theorem NoBuyback.frac_nonneg {D : ℕ → ℕ → Ω → ℝ} (h : NoBuyback D) (t m : ℕ) (ω : Ω)
    (htm : t < m) : 0 ≤ fracSold D t m ω := by
  simp only [fracSold, Pi.div_apply, Pi.sub_apply]
  exact div_nonneg (sub_nonneg.mpr (h.2.1 t m ω htm)) (h.2.2 m ω).le

/-- Cochrane (2023), §7.4: without buy-backs each column of sale fractions sums to
`(B_{m−1}^{(m)} − B_{−1}^{(m)})/B_{m−1}^{(m)} ≤ 1`. -/
theorem NoBuyback.col_le_one {D : ℕ → ℕ → Ω → ℝ} (h : NoBuyback D) (m : ℕ) (ω : Ω) :
    ∑ t ∈ Finset.range m, fracSold D t m ω ≤ 1 := by
  simp only [fracSold, Pi.div_apply, Pi.sub_apply]
  rw [← Finset.sum_div, Finset.sum_range_sub (fun t => D t m ω), div_le_one (h.2.2 m ω)]
  linarith [h.1 m ω]

/-- Cochrane (2023), eq. (7.5), p. 216: with nonnegative debt and price levels, the present-value
relation bounds the real value of maturing debt: `0 ≤ B_{t−1}^{(t)}/P_t ≤ M/(1−β)`. -/
theorem bounded_of_presentValue {β M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {D : ℕ → ℕ → Ω → ℝ}
    {x s : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hx0 : ∀ t ω, 0 ≤ x t ω)
    (hD0 : ∀ t j ω, 0 ≤ D t (t + j) ω) (hsb : ∀ t ω, |s t ω| ≤ M) {t : ℕ}
    (hpv : PresentValue 𝔼 β D x s t) (ω : Ω) :
    0 ≤ D t t ω * x t ω ∧ D t t ω * x t ω ≤ M / (1 - β) := by
  have hEx : ∀ u v ω', 0 ≤ 𝔼.E u (x v) ω' := by
    intro u v ω'
    have := 𝔼.mono u (show (fun _ => (0 : ℝ)) ≤ x v from fun ω'' => hx0 v ω'') ω'
    rwa [𝔼.const] at this
  have hterm : ∀ j, 0 ≤ debtTerm 𝔼 β D x t j ω := fun j =>
    mul_nonneg (pow_nonneg hβ0 j) (mul_nonneg (hD0 t j ω) (hEx _ _ ω))
  have h0 : debtTerm 𝔼 β D x t 0 ω = D t t ω * x t ω := by
    simp [debtTerm, hx t]
  refine ⟨h0 ▸ hterm 0, ?_⟩
  have h1 := le_hasSum (hpv ω).2 0 (fun j _ => hterm j)
  rw [h0] at h1
  refine h1.trans ?_
  have hg : HasSum (fun k : ℕ => β ^ k * M) (M / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right M
    simpa [div_eq_mul_inv, mul_comm] using this
  refine hasSum_le (fun k => ?_) (hpv ω).1.hasSum hg
  rw [surplusTerm]
  exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (𝔼.abs_E_le (hsb _) _ ω))
    (pow_nonneg hβ0 k)

/-- Cochrane (2023), §7.4, pp. 225–226: **the present-value relations determine the price level
when the government never buys back debt.** Two adapted, positive price-level paths `1/P`, `1/P'`
that both satisfy every flow condition (7.1) and every present-value relation (7.5), for the same
predetermined debt without buy-backs and the same bounded surpluses (`0 < β < 1`), coincide. -/
theorem price_unique_noBuyback (hpo : 𝔼.PullOut) {β M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {D : ℕ → ℕ → Ω → ℝ} {x x' s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D) (hnb : NoBuyback D)
    (hx : 𝔼.Adapted x) (hx' : 𝔼.Adapted x') (hx0 : ∀ t ω, 0 ≤ x t ω)
    (hx0' : ∀ t ω, 0 ≤ x' t ω) (hsb : ∀ t ω, |s t ω| ≤ M)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D x' s t)
    (hpv : ∀ t, PresentValue 𝔼 β D x s t) (hpv' : ∀ t, PresentValue 𝔼 β D x' s t) :
    x = x' := by
  have hDmm : ∀ m ω, D m m ω ≠ 0 := fun m ω => (hnb.2.2 m ω).ne'
  have hD0 : ∀ t j ω, 0 ≤ D t (t + j) ω := fun t j ω => hnb.nonneg t (t + j) (by omega) ω
  have hy := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow t)
  have hy' := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow' t)
  have hb : ∀ t ω, |D t t ω * x t ω| ≤ M / (1 - β) := fun t ω => by
    obtain ⟨h1, h2⟩ := bounded_of_presentValue 𝔼 hβ0.le hβ1 hx hx0 hD0 hsb (hpv t) ω
    rw [abs_of_nonneg h1]; exact h2
  have hb' : ∀ t ω, |D t t ω * x' t ω| ≤ M / (1 - β) := fun t ω => by
    obtain ⟨h1, h2⟩ := bounded_of_presentValue 𝔼 hβ0.le hβ1 hx' hx0' hD0 hsb (hpv' t) ω
    rw [abs_of_nonneg h1]; exact h2
  have hzero := unique_of_noBuyback 𝔼 hβ0 hβ1 (A := fracSold D)
    (fun t m ω h => hnb.frac_nonneg t m ω h) (fun m ω => hnb.col_le_one m ω)
    (homogeneous_of_two 𝔼 hy hy') (K := M / (1 - β) + M / (1 - β))
    (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hb t ω) (hb' t ω)))
  funext t ω
  have := congrFun (congrFun hzero t) ω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact mul_left_cancel₀ (hDmm t ω) this

/-- Cochrane (2023), §7.4, p. 225: **the present-value relations determine the price level under
the row condition.** If the sale fractions satisfy the row condition with `ρ < 1`, two adapted price
paths satisfying every flow condition with bounded real values of maturing debt coincide. -/
theorem price_unique_row (hpo : 𝔼.PullOut) {β ρ K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {D : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} {x x' s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) (hrow : RowBound β (fracSold D) a ρ)
    (hflow : ∀ t, RealFlow 𝔼 β D x s t) (hflow' : ∀ t, RealFlow 𝔼 β D x' s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (hb' : ∀ t ω, |D t t ω * x' t ω| ≤ K) : x = x' := by
  have hy := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow t)
  have hy' := fun t => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm t).mp (hflow' t)
  have hzero := unique_of_row 𝔼 hβ0 hρ1 hrow (homogeneous_of_two 𝔼 hy hy') (K := K + K)
    (fun t ω => by
      simp only [Pi.sub_apply]
      exact (abs_sub _ _).trans (add_le_add (hb t ω) (hb' t ω)))
  funext t ω
  have := congrFun (congrFun hzero t) ω
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact mul_left_cancel₀ (hDmm t ω) this

/-- Cochrane (2023), eq. (7.17), p. 225: **(7.17) for the price level.** In an equilibrium with
bounded real maturing debt, under the row condition and with each sale fraction known at the last
sale date, `B_{t−1}^{(t)}/P_t = E_t ∑_m β^m W_t^{(m)} s_{t+m}`. -/
theorem price_formula (hpo : 𝔼.PullOut) {β ρ M K : ℝ} (hβ0 : 0 ≤ β) (hρ1 : ρ < 1)
    {D : ℕ → ℕ → Ω → ℝ} {a : ℕ → ℝ} {x s : ℕ → Ω → ℝ} (hD : Predetermined 𝔼 D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) (hrow : RowBound β (fracSold D) a ρ)
    (hA : ∀ t j, 𝔼.E (t + j) (fracSold D t (t + (j + 1))) = fracSold D t (t + (j + 1)))
    (hs : 𝔼.Adapted s) (hsb : ∀ t ω, |s t ω| ≤ M) (hflow : ∀ t, RealFlow 𝔼 β D x s t)
    (hb : ∀ t ω, |D t t ω * x t ω| ≤ K) (t : ℕ) (ω : Ω) :
    HasSum (fun m => formulaTerm 𝔼 β (fracSold D) s t m ω) (D t t ω * x t ω) :=
  theoremW 𝔼 hpo hβ0 hρ1 hrow hA hs hsb
    (fun u => (realFlow_iff_maturingSystem 𝔼 hpo hD hDmm u).mp (hflow u)) hb t ω

/-! ### Special cases (§7.4, p. 225) -/

/-- Cochrane (2023), §7.4, p. 225 (special case): with no sales after date 0 (`A_t^{(m)} = 0` for
`t ≥ 1`), `W_t^{(k)} = 0` for `k ≥ 1` and `t ≥ 1`, so (7.17) reduces to (7.6). -/
theorem special_noSales {R : Type*} [CommRing R] {A : ℕ → ℕ → R}
    (hA : ∀ t m, 1 ≤ t → A t m = 0) {t : ℕ} (ht : 1 ≤ t) (k : ℕ) : weight A t (k + 1) = 0 := by
  rw [weight_succ]
  exact Finset.sum_eq_zero fun n _ => by rw [hA _ _ (by omega), zero_mul]

/-- Cochrane (2023), §7.4, p. 225 (special case): pure one-period roll-over (`A_t^{(t+1)} = 1`, no
other sales) gives `W ≡ 1`, so (7.17) is the standard present value `E_t ∑ β^j s_{t+j}`. -/
theorem special_onePeriod {R : Type*} [CommRing R] {A : ℕ → ℕ → R}
    (h1 : ∀ t, A t (t + 1) = 1) (h0 : ∀ t j, A t (t + (j + 2)) = 0) (k : ℕ) :
    ∀ t, weight A t k = 1 := by
  induction k with
  | zero => exact fun t => weight_zero A t
  | succ k ih =>
    intro t
    rw [weight_succ, Finset.sum_range_succ, ih t, mul_one,
      show t + (k + 1) = t + k + 1 by omega, h1 (t + k)]
    rw [Finset.sum_eq_zero fun n hn => ?_, zero_add]
    have hn' := Finset.mem_range.mp hn
    rw [show t + k + 1 = t + n + (k - n - 1 + 2) by omega, h0, zero_mul]

/-- Cochrane (2023), §7.4, p. 225: with one-period debt only, the sale fractions are
`A_t^{(t+1)} = 1` and `A_t^{(t+j+2)} = 0`, so the one-period special case applies. -/
theorem fracSold_onePeriod {Ω : Type*} {D : ℕ → ℕ → Ω → ℝ} (h : MaturingDebt.OnePeriod D)
    (hDmm : ∀ m ω, D m m ω ≠ 0) :
    (∀ t, fracSold D t (t + 1) = 1) ∧ ∀ t j, fracSold D t (t + (j + 2)) = 0 := by
  constructor
  · intro t
    funext ω
    have := h t 0
    simp only [zero_add] at this
    simp only [fracSold, Pi.div_apply, this, sub_zero, Pi.one_apply]
    exact div_self (hDmm _ ω)
  · intro t j
    funext ω
    have h1 := h (t + 1) j
    have h2 := h t (j + 1)
    rw [show t + 1 + (j + 1) = t + (j + 2) by omega] at h1
    rw [show t + (j + 1 + 1) = t + (j + 2) by omega] at h2
    simp only [fracSold, Pi.div_apply, Pi.zero_apply, h1, h2, sub_zero, zero_div]

/-! ### The printed (7.15) omits `β^j` (E7.2) -/

/-- Cochrane (2023), eq. (7.15), p. 225: the illustrative debt: one unit due at dates 0 and 1,
nothing
later, no sales. -/
noncomputable def exD : ℕ → ℕ → Unit → ℝ := fun _ m _ => if m ≤ 1 then 1 else 0

/-- Cochrane (2023), eq. (7.15), p. 225: the illustrative surpluses `s_0 = s_1 = 1`, zero
afterwards. -/
noncomputable def exS : ℕ → Unit → ℝ := fun t _ => if t ≤ 1 then 1 else 0

/-- Cochrane (2023), eq. (7.15), p. 225 (E7.2): **the printed (7.15) is false.** In the illustration
(perfect foresight, `β < 1`, price level `1/P_t = 1`) every flow condition and the corrected
present-value relation (with `β^j`, as in (7.5)) hold at date 0, but the printed version without
`β^j` would require `∑_j B_{−1}^{(j)}/P_j = 2` to equal `∑_j β^j s_j = 1 + β`. -/
theorem printed_715_fails {β : ℝ} (hβ1 : β < 1) :
    (∀ t, RealFlow perfectForesight β exD (fun _ _ => 1) exS t) ∧
      PresentValue perfectForesight β exD (fun _ _ => 1) exS 0 ∧
      HasSum (fun j => exD 0 j () * 1) 2 ∧ HasSum (fun j => β ^ j * exS j ()) (1 + β) ∧
      (2 : ℝ) ≠ 1 + β := by
  have hS : HasSum (fun j => β ^ j * exS j ()) (1 + β) := by
    have : HasSum (fun j => β ^ j * exS j ())
        (∑ j ∈ Finset.range 2, β ^ j * exS j ()) := hasSum_sum_of_ne_finset_zero fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj
        simp [exS, show ¬ j ≤ 1 by omega]
    simpa [Finset.sum_range_succ, exS] using this
  refine ⟨fun t ω => ?_, fun ω => ?_, ?_, hS, by linarith⟩
  · have hz : (fun j : ℕ => β ^ (j + 1) * (sales exD t (t + (j + 1)) ω *
        perfectForesight.E t (fun _ => (1 : ℝ)) ω)) = fun _ => 0 := by
      funext j; simp [sales, exD]
    rw [hz]
    convert hasSum_zero using 1
    by_cases ht : t ≤ 1 <;> simp [exD, exS, ht]
  · have hsum : ∀ k, surplusTerm perfectForesight β exS 0 k ω = β ^ k * exS k () := by
      intro k; simp [surplusTerm, perfectForesight, zero_add]
    have hsumm : Summable (fun k => surplusTerm perfectForesight β exS 0 k ω) := by
      simp only [hsum]; exact hS.summable
    refine ⟨hsumm, ?_⟩
    have hpv : pvSurplus perfectForesight β exS 0 ω = 1 + β := by
      rw [pvSurplus]; simp only [hsum]; exact hS.tsum_eq
    rw [hpv]
    have : HasSum (fun j => debtTerm perfectForesight β exD (fun _ _ => 1) 0 j ω)
        (∑ j ∈ Finset.range 2, debtTerm perfectForesight β exD (fun _ _ => 1) 0 j ω) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj
        simp [debtTerm, exD, show ¬ j ≤ 1 by omega]
    simpa [Finset.sum_range_succ, debtTerm, exD, perfectForesight, add_comm] using this
  · have : HasSum (fun j => exD 0 j () * 1) (∑ j ∈ Finset.range 2, exD 0 j () * 1) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        simp only [Finset.mem_range, not_lt] at hj
        simp [exD, show ¬ j ≤ 1 by omega]
    have h2 : (∑ j ∈ Finset.range 2, exD 0 j () * 1) = 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [exD]
    rwa [h2] at this

/-! ### The matrix display (7.16), corrected (E7.3) -/

/-- Cochrane (2023), eq. (7.16), p. 225, corrected: row `t` of the upper-triangular matrix has entry
`β^{m−t} B_{t−1}^{(m)}` in column `m ≥ t` (the printed display starts row `t` with `B_t^{(t+1)}`,
one index too late, and omits `β^{m−t}`). -/
noncomputable def pvMatrix (β : ℝ) (D : ℕ → ℕ → ℝ) (t m : ℕ) : ℝ :=
  if t ≤ m then β ^ (m - t) * D t m else 0

/-- Cochrane (2023), eqs. (7.15)–(7.16), p. 225 (perfect foresight): row `t` of the corrected matrix
applied to `p = (1/P_m)_m` is the real value of debt `∑_j β^j B_{t−1}^{(t+j)}/P_{t+j}`. -/
theorem pvMatrix_row (β : ℝ) (D : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (t : ℕ) (v : ℝ) :
    HasSum (fun m => pvMatrix β D t m * x m) v ↔
      HasSum (fun j => β ^ j * D t (t + j) * x (t + j)) v := by
  have hfin : ∑ m ∈ Finset.range t, pvMatrix β D t m * x m = 0 :=
    Finset.sum_eq_zero fun m hm => by
      simp [pvMatrix, show ¬ t ≤ m by have := Finset.mem_range.mp hm; omega]
  rw [← hasSum_nat_add_iff' t, hfin, sub_zero]
  have : (fun j => pvMatrix β D t (j + t) * x (j + t)) =
      fun j => β ^ j * D t (t + j) * x (t + j) := by
    funext j
    rw [add_comm j t]
    simp only [pvMatrix, show t ≤ t + j by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  rw [this]

/-! ### The non-uniqueness counterexample (E7.4) -/

/-- Cochrane (2023), §7.4, p. 225 (counterexample to uniqueness): at every date one unit of debt
matures and `2/β` units are due the following date, `B_{t−1}^{(t)} = 1`, `B_{t−1}^{(t+1)} = 2/β`. -/
noncomputable def cxD (β : ℝ) : ℕ → ℕ → Unit → ℝ :=
  fun t m _ => if m = t then 1 else if m = t + 1 then 2 / β else 0

/-- Cochrane (2023), §7.4: the constant surplus `s`. -/
def cxS (s0 : ℝ) : ℕ → Unit → ℝ := fun _ _ => s0

/-- Cochrane (2023), §7.4: the fundamental level `x* = s/(3(1−β))`. -/
noncomputable def cxStar (β s0 : ℝ) : ℝ := s0 / (3 * (1 - β))

/-- Cochrane (2023), §7.4: the family of price paths `1/P_t = x* + ε (−1/2)^t`. -/
noncomputable def cxX (β s0 ε : ℝ) : ℕ → Unit → ℝ := fun t _ => cxStar β s0 + ε * (-1 / 2) ^ t

/-- Cochrane (2023), §7.4: `B_{t−1}^{(t)} = 1` in the counterexample. -/
theorem cxD_self (β : ℝ) (t : ℕ) (u : Unit) : cxD β t t u = 1 := by simp [cxD]

/-- Cochrane (2023), §7.4: `B_{t−1}^{(t+1)} = 2/β` in the counterexample. -/
theorem cxD_succ (β : ℝ) (t : ℕ) (u : Unit) : cxD β t (t + 1) u = 2 / β := by simp [cxD]

/-- Cochrane (2023), §7.4: no debt due after `t + 1` in the counterexample. -/
theorem cxD_far (β : ℝ) (t k : ℕ) (u : Unit) : cxD β t (t + (k + 2)) u = 0 := by
  simp only [cxD, show ¬ (t + (k + 2) = t) by omega, show ¬ (t + (k + 2) = t + 1) by omega,
    ↓reduceIte]

/-- Cochrane (2023), §7.4: the policy buys back debt: the sale at `t` of maturity-`t+1` debt is
`1 − 2/β < 0` (for `0 < β < 2`). -/
theorem cx_buyback {β : ℝ} (hβ0 : 0 < β) (hβ2 : β < 2) (t : ℕ) (u : Unit) :
    sales (cxD β) t (t + 1) u < 0 := by
  simp only [sales, Pi.sub_apply, cxD_self, cxD_succ]
  rw [sub_neg, lt_div_iff₀ hβ0]
  linarith

/-- Cochrane (2023), §7.4 (E7.4): **every member of the family satisfies every flow condition**
(7.1)/(7.14), for any `ε`, under perfect foresight with `0 < β < 1`. -/
theorem cx_flow {β s0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ε : ℝ) (t : ℕ) :
    RealFlow perfectForesight β (cxD β) (cxX β s0 ε) (cxS s0) t := by
  intro u
  have hz : ∀ j ∉ Finset.range 2, β ^ (j + 1) * (sales (cxD β) t (t + (j + 1)) u *
      perfectForesight.E t (cxX β s0 ε (t + (j + 1))) u) = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have h1 : cxD β (t + 1) (t + (k + 2 + 1)) u = 0 := by
      rw [show t + (k + 2 + 1) = t + 1 + (k + 2) by omega, cxD_far]
    have h2 : cxD β t (t + (k + 2 + 1)) u = 0 := by
      rw [show t + (k + 2 + 1) = t + (k + 1 + 2) by omega, cxD_far]
    simp [sales, h1, h2]
  have hs : HasSum (fun j => β ^ (j + 1) * (sales (cxD β) t (t + (j + 1)) u *
      perfectForesight.E t (cxX β s0 ε (t + (j + 1))) u))
      (∑ j ∈ Finset.range 2, β ^ (j + 1) * (sales (cxD β) t (t + (j + 1)) u *
        perfectForesight.E t (cxX β s0 ε (t + (j + 1))) u)) :=
    hasSum_sum_of_ne_finset_zero hz
  convert hs using 1
  have e1 : cxD β (t + 1) (t + (0 + 1)) u = 1 := by rw [zero_add, cxD_self]
  have e2 : cxD β t (t + (0 + 1)) u = 2 / β := by rw [zero_add, cxD_succ]
  have e3 : cxD β (t + 1) (t + (1 + 1)) u = 2 / β := by
    rw [show t + (1 + 1) = t + 1 + 1 by omega, cxD_succ]
  have e4 : cxD β t (t + (1 + 1)) u = 0 := by
    rw [show t + (1 + 1) = t + (0 + 2) by omega, cxD_far]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sales, Pi.sub_apply]
  rw [show t + (0 + 1) = t + 1 by omega] at e1 e2
  simp only [show t + (1 + 1) = t + 2 by omega] at e3 e4
  simp only [e1, e2, e3, e4, cxD_self, cxX, cxS, cxStar, perfectForesight, LinearMap.id_apply]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hb : β ≠ 0 := hβ0.ne'
  rw [pow_succ (-1 / 2 : ℝ) (t + 1), pow_succ (-1 / 2 : ℝ) t]
  field_simp
  ring

/-- Cochrane (2023), §7.4 (E7.4): **every member of the family satisfies every present-value
relation** (7.5)/(7.15): `x_t + 2 x_{t+1} = s/(1−β)`. -/
theorem cx_presentValue {β s0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (ε : ℝ) (t : ℕ) :
    PresentValue perfectForesight β (cxD β) (cxX β s0 ε) (cxS s0) t := by
  intro u
  have hsT : ∀ k, surplusTerm perfectForesight β (cxS s0) t k u = β ^ k * s0 := by
    intro k; simp [surplusTerm, perfectForesight, cxS]
  have hgeo : HasSum (fun k => β ^ k * s0) (s0 / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_right s0
    simpa [div_eq_mul_inv, mul_comm] using this
  have hsumm : Summable (fun k => surplusTerm perfectForesight β (cxS s0) t k u) := by
    simp only [hsT]; exact hgeo.summable
  refine ⟨hsumm, ?_⟩
  have hpv : pvSurplus perfectForesight β (cxS s0) t u = s0 / (1 - β) := by
    rw [pvSurplus]; simp only [hsT]; exact hgeo.tsum_eq
  rw [hpv]
  have hz : ∀ j ∉ Finset.range 2, debtTerm perfectForesight β (cxD β) (cxX β s0 ε) t j u = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    simp [debtTerm, cxD_far]
  have hs : HasSum (fun j => debtTerm perfectForesight β (cxD β) (cxX β s0 ε) t j u)
      (∑ j ∈ Finset.range 2, debtTerm perfectForesight β (cxD β) (cxX β s0 ε) t j u) :=
    hasSum_sum_of_ne_finset_zero hz
  convert hs using 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, debtTerm, add_zero,
    cxD_self, cxD_succ, cxX, cxStar, perfectForesight, LinearMap.id_apply, pow_zero, pow_one]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hb : β ≠ 0 := hβ0.ne'
  rw [pow_succ (-1 / 2 : ℝ) t]
  field_simp
  ring

/-- Cochrane (2023), §7.4 (E7.4): for `|ε| < x*` (possible when `s > 0`, `β < 1`), every price
level in the family is positive. -/
theorem cx_pos {β s0 ε : ℝ} (hε : |ε| < cxStar β s0) (t : ℕ) (u : Unit) :
    0 < cxX β s0 ε t u := by
  simp only [cxX]
  have hq : |(-1 / 2 : ℝ) ^ t| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (by norm_num [abs_div])
  have : |ε * (-1 / 2) ^ t| ≤ |ε| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hq
  have := neg_abs_le (ε * (-1 / 2) ^ t)
  linarith

/-- Cochrane (2023), §7.4 (E7.4): the family is bounded, `|1/P_t| ≤ x* + |ε|`. -/
theorem cx_bounded (β s0 ε : ℝ) (t : ℕ) (u : Unit) :
    |cxX β s0 ε t u| ≤ |cxStar β s0| + |ε| := by
  simp only [cxX]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _)
    (by norm_num [abs_div]))

/-- Cochrane (2023), §7.4 (E7.4): **non-uniqueness**: different `ε` give different price paths, so
the flow and present-value relations (7.14)–(7.16) do not determine the price level. -/
theorem cx_ne {β s0 ε ε' : ℝ} (h : ε ≠ ε') : cxX β s0 ε ≠ cxX β s0 ε' := by
  intro hx
  have := congrFun (congrFun hx 0) ()
  simp only [cxX, pow_zero, mul_one] at this
  exact h (by linarith)

/-- Cochrane (2023), §7.4 (E7.4): the sale fractions of the counterexample:
`A_t^{(t+1)} = 1 − 2/β`, `A_t^{(t+2)} = 2/β`, `A_t^{(t+k+3)} = 0`. -/
theorem cx_frac (β : ℝ) (t : ℕ) :
    fracSold (cxD β) t (t + 1) = (fun _ => 1 - 2 / β) ∧
      fracSold (cxD β) t (t + 2) = (fun _ => 2 / β) ∧
      ∀ k, fracSold (cxD β) t (t + (k + 3)) = fun _ => 0 := by
  refine ⟨?_, ?_, fun k => ?_⟩
  · funext u
    simp only [fracSold, Pi.div_apply, Pi.sub_apply, cxD_self, cxD_succ, div_one]
  · funext u
    have e1 : cxD β (t + 1) (t + 2) u = 2 / β := by
      rw [show t + 2 = t + 1 + 1 by omega, cxD_succ]
    have e2 : cxD β t (t + 2) u = 0 := by rw [show t + 2 = t + (0 + 2) by omega, cxD_far]
    simp only [fracSold, Pi.div_apply, Pi.sub_apply, e1, e2, cxD_self, sub_zero, div_one]
  · funext u
    have e1 : cxD β (t + 1) (t + (k + 3)) u = 0 := by
      rw [show t + (k + 3) = t + 1 + (k + 2) by omega, cxD_far]
    have e2 : cxD β t (t + (k + 3)) u = 0 := by
      rw [show t + (k + 3) = t + (k + 1 + 2) by omega, cxD_far]
    simp only [fracSold, Pi.div_apply, Pi.sub_apply, e1, e2, sub_zero, zero_div]

/-- Cochrane (2023), §7.4 (E7.4): the weights obey
`W^{(k+2)} = (1 − 2/β) W^{(k+1)} + (2/β) W^{(k)}`. -/
theorem cx_weight_rec (β : ℝ) (t k : ℕ) :
    weight (fracSold (cxD β)) t (k + 2) = (fun _ => 1 - 2 / β) * weight (fracSold (cxD β)) t (k + 1)
      + (fun _ => 2 / β) * weight (fracSold (cxD β)) t k := by
  have h1 := fun t => (cx_frac β t).1
  have h2 := fun t => (cx_frac β t).2.1
  have h3 := fun t => (cx_frac β t).2.2
  rw [weight_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_eq_zero fun n hn => ?_, zero_add]
  · rw [show t + (k + 1 + 1) = t + (k + 1) + 1 by omega, h1,
      show t + (k + 1) + 1 = t + k + 2 by omega, h2]
    ring
  · have hn' := Finset.mem_range.mp hn
    rw [show t + (k + 1 + 1) = t + n + (k - n - 1 + 3) by omega, h3]
    funext u
    simp

/-- Cochrane (2023), §7.4 (E7.4): the weights in closed form,
`W^{(k)} = (β + 2(−2/β)^k)/(β + 2)`. -/
theorem cx_weight {β : ℝ} (hβ0 : 0 < β) (t k : ℕ) :
    weight (fracSold (cxD β)) t k = fun _ => (β + 2 * (-2 / β) ^ k) / (β + 2) := by
  have hb : β ≠ 0 := hβ0.ne'
  have hb2 : β + 2 ≠ 0 := by linarith
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k
    · rw [weight_zero]
      funext u
      simp only [Pi.one_apply, pow_zero, mul_one]
      field_simp
    · rw [weight_succ, Finset.sum_range_one, weight_zero, add_zero, (cx_frac β t).1]
      funext u
      simp only [Pi.mul_apply, Pi.one_apply, mul_one, zero_add, pow_one]
      field_simp
      ring
    · rw [cx_weight_rec, ih (k + 1) (by omega), ih k (by omega)]
      funext u
      simp only [Pi.add_apply, Pi.mul_apply]
      rw [pow_succ (-2 / β) (k + 1), pow_succ (-2 / β) k]
      generalize (-2 / β) ^ k = q
      field_simp
      ring

/-- Cochrane (2023), §7.4 (E7.4): **(7.17) diverges**: `β^k W^{(k)} = (β^{k+1} + 2(−2)^k)/(β+2)`
does not tend to zero, so with `s ≠ 0` the series `∑_k β^k W^{(k)} s` is not summable. -/
theorem cx_formula_diverges {β s0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hs0 : s0 ≠ 0) (t : ℕ) :
    ¬ Summable (fun k => formulaTerm perfectForesight β (fracSold (cxD β)) (cxS s0) t k ()) := by
  intro hsum
  have hterm : ∀ k, formulaTerm perfectForesight β (fracSold (cxD β)) (cxS s0) t k () =
      (β ^ (k + 1) + 2 * (-2) ^ k) / (β + 2) * s0 := by
    intro k
    simp only [formulaTerm, cx_weight hβ0, perfectForesight, LinearMap.id_apply, Pi.mul_apply,
      cxS]
    have hb : β ≠ 0 := hβ0.ne'
    have hb2 : β + 2 ≠ 0 := by linarith
    rw [div_pow, pow_succ]
    field_simp
  have hlim := hsum.tendsto_atTop_zero
  simp only [hterm] at hlim
  have hlow : ∀ k : ℕ, |s0| / 3 ≤ |(β ^ (k + 1) + 2 * (-2) ^ k) / (β + 2) * s0| := by
    intro k
    rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < β + 2)]
    have hpow : β ^ (k + 1) ≤ 1 := pow_le_one₀ hβ0.le hβ1.le
    have hpow0 : 0 ≤ β ^ (k + 1) := pow_nonneg hβ0.le _
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hnum : 1 ≤ |β ^ (k + 1) + 2 * (-2 : ℝ) ^ k| := by
      have habs : |2 * (-2 : ℝ) ^ k| = 2 * 2 ^ k := by
        rw [abs_mul, abs_pow]; norm_num
      have := abs_sub_abs_le_abs_sub (2 * (-2 : ℝ) ^ k) (-(β ^ (k + 1)))
      rw [abs_neg, abs_of_nonneg hpow0, habs, sub_neg_eq_add] at this
      rw [add_comm]
      linarith
    have hs : 0 ≤ |s0| := abs_nonneg _
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 < |s0| / 3 := by positivity
  have hlim' : Tendsto (fun k : ℕ => |(β ^ (k + 1) + 2 * (-2) ^ k) / (β + 2) * s0|) atTop
      (𝓝 0) := by simpa using hlim.abs
  obtain ⟨k, hk⟩ := (hlim'.eventually (gt_mem_nhds hpos)).exists
  exact absurd (hlow k) (not_le.mpr hk)

/-- Cochrane (2023), §7.4 (E7.4): the counterexample violates the row condition: for any bound
`a` the sum `∑_j β^{j+1} a_j` is at least `2 + β > 1`. -/
theorem cx_not_row {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ¬ ∃ a ρ, ρ < 1 ∧ RowBound β (fracSold (cxD β)) a ρ := by
  rintro ⟨a, ρ, hρ, hrow⟩
  obtain ⟨h1, h2, -⟩ := cx_frac β 0
  have ha0 : 2 / β - 1 ≤ a 0 := by
    have := hrow.2.1 0 0 ()
    rw [h1] at this
    simp only at this
    rw [abs_sub_comm, abs_of_nonneg (by rw [sub_nonneg, le_div_iff₀ hβ0]; linarith)] at this
    exact this
  have ha1 : 2 / β ≤ a 1 := by
    have := hrow.2.1 0 1 ()
    rw [show 0 + (1 + 1) = 0 + 2 by rfl, h2] at this
    simp only at this
    rwa [abs_of_pos (by positivity)] at this
  have hnn : ∀ j, 0 ≤ β ^ (j + 1) * a j := fun j => mul_nonneg (pow_nonneg hβ0.le _) (hrow.1 j)
  have hpart := hrow.2.2.1.sum_le_tsum (Finset.range 2) fun j _ => hnn j
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one,
    show 1 + 1 = 2 from rfl] at hpart
  have h3 : β * (2 / β - 1) + β ^ 2 * (2 / β) = 2 + β := by field_simp; ring
  have h4 : β * (2 / β - 1) + β ^ 2 * (2 / β) ≤ β * a 0 + β ^ 2 * a 1 :=
    add_le_add (mul_le_mul_of_nonneg_left ha0 hβ0.le)
      (mul_le_mul_of_nonneg_left ha1 (by positivity))
  linarith [hrow.2.2.2]

end Cochrane.LongTermDebtDynamics.GeneralFormula
