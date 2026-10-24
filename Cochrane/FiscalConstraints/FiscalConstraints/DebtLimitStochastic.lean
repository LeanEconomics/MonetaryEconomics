/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import FiscalConstraints.RvsG
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A debt limit with stochastic surpluses (Theorem S)

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 6, §6.4.1, pp. 196–197.

With permanent `r < g` the debt-to-GDP ratio follows `x_{t+1} = γ x_t − σ_t` with
`γ = (1 + r)/(1 + g) ∈ [0, 1)`, where `σ_t` is the surplus-to-GDP ratio. The book argues
that with an upper limit on the debt-to-GDP ratio and a stationary (unmanaged) surplus
process, "you eventually flip 100 heads in a row": the debt ratio eventually exceeds the
bound, so no initial value of debt is sustainable (p. 197).

## Main results

* `frequently_exceeds` (**Theorem S**): independent surpluses, bounded above, with a
  probability of a deficit of size at least `c` bounded away from zero, push the debt ratio
  above every level `M < c/(1 − γ)` infinitely often, almost surely, from every initial
  debt. The proof is the second Borel–Cantelli lemma applied to independent blocks of
  `k` consecutive bad draws.
* `not_sustainable`: hence the event "debt stays below the limit forever" has probability 0.
* `unbounded_of_unbounded_deficits`, `iid_unbounded`, `gaussian_iid_unbounded`: if large
  deficits have positive probability at every size (e.g. i.i.d. Gaussian surpluses), the debt
  ratio is almost surely unbounded above.
* `debtPath_le_of_bounded_deficits` (correction): if deficits are bounded, `σ_t ≥ −c`, the
  debt ratio never exceeds `max x₀ (c/(1 − γ))`. So "even if we limit the support of the
  surplus distribution ... the integral of the surplus eventually exceeds any bound" (p. 197)
  is false for bounds above `c/(1 − γ)`; it holds for bounds below `c/(1 − γ)` (Theorem S).
* `managedPath_le`: a managed surplus that rises just enough to avoid the boundary keeps debt
  below the limit from date 1 on (p. 197, "we must already imagine a managed surplus
  process").
-/

namespace Cochrane.FiscalConstraints.DebtLimitStochastic

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*}

/-- Cochrane (2023), (6.4) p. 196 in discrete time: the debt-to-GDP ratio
`x_{t+1} = γ x_t − σ_t`, `x_0 = x₀`, with `γ = (1 + r)/(1 + g)` and surplus ratio `σ_t`: on each
path `ω` it is the deterministic backward solution `RvsG.iterD` driven by `σ_t(ω)`. -/
noncomputable def debtPath (γ x₀ : ℝ) (σ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  RvsG.iterD γ (fun s => σ s ω) x₀ t

/-- Cochrane (2023), (6.4) p. 196: the recursion of `debtPath`. -/
theorem debtPath_succ (γ x₀ : ℝ) (σ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    debtPath γ x₀ σ (t + 1) ω = γ * debtPath γ x₀ σ t ω - σ t ω := rfl

/-- Cochrane (2023), p. 197: with surpluses bounded above by `K` and `0 ≤ γ < 1`, the debt
ratio is bounded below by `−(|x₀| + |K|/(1 − γ))`. -/
theorem debtPath_lower {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) {σ : ℕ → Ω → ℝ} {ω : Ω}
    (hK : ∀ t, σ t ω ≤ K) (t : ℕ) :
    -(|x₀| + |K| / (1 - γ)) ≤ debtPath γ x₀ σ t ω := by
  have h1 : 0 < 1 - γ := by linarith
  have hKd : 0 ≤ |K| / (1 - γ) := div_nonneg (abs_nonneg K) h1.le
  have hKe : |K| / (1 - γ) * (1 - γ) = |K| := div_mul_cancel₀ _ h1.ne'
  induction t with
  | zero =>
    change -(|x₀| + |K| / (1 - γ)) ≤ x₀
    linarith [neg_abs_le x₀]
  | succ t ih =>
    rw [debtPath_succ]
    have hσ := (hK t).trans (le_abs_self K)
    have h2 : γ * -(|x₀| + |K| / (1 - γ)) ≤ γ * debtPath γ x₀ σ t ω :=
      mul_le_mul_of_nonneg_left ih hγ0
    nlinarith [abs_nonneg x₀]

/-- Cochrane (2023), p. 197 ("flip 100 heads in a row"): after `k` consecutive deficits of
size at least `c`, `x_{t+k} ≥ γᵏ x_t + c (1 + γ + ⋯ + γᵏ⁻¹)`. -/
theorem debtPath_run {γ x₀ c : ℝ} (hγ0 : 0 ≤ γ) {σ : ℕ → Ω → ℝ} {ω : Ω} (t : ℕ) :
    ∀ k, (∀ j < k, σ (t + j) ω ≤ -c) →
      γ ^ k * debtPath γ x₀ σ t ω + c * ∑ i ∈ Finset.range k, γ ^ i ≤
        debtPath γ x₀ σ (t + k) ω := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hrun
    have hk := ih (fun j hj => hrun j (Nat.lt_succ_of_lt hj))
    have hlast := hrun k (Nat.lt_succ_self k)
    rw [← add_assoc, debtPath_succ, Finset.sum_range_succ', pow_succ]
    have hsum : ∑ i ∈ Finset.range k, γ ^ (i + 1) = γ * ∑ i ∈ Finset.range k, γ ^ i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    have := mul_le_mul_of_nonneg_left hk hγ0
    nlinarith

/-- Cochrane (2023), p. 197: for any floor `−B` and any level `M < c/(1 − γ)` there is a run
length `k ≥ 1` such that `k` consecutive deficits of size `c` lift every debt ratio above the
floor to above `M`. -/
theorem exists_run_length {γ c M B : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) :
    ∃ k, 1 ≤ k ∧ ∀ x, -B ≤ x → M < γ ^ k * x + c * ∑ i ∈ Finset.range k, γ ^ i := by
  have h1 : 0 < 1 - γ := by linarith
  set D := c / (1 - γ) with hD
  have hlim : Tendsto (fun k : ℕ => γ ^ k * (D + B)) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (D + B)
  have hev : ∀ᶠ k : ℕ in atTop, γ ^ k * (D + B) < D - M ∧ 1 ≤ k :=
    (hlim.eventually (gt_mem_nhds (by linarith))).and (eventually_ge_atTop 1)
  obtain ⟨k, hk, hk1⟩ := hev.exists
  refine ⟨k, hk1, fun x hx => ?_⟩
  have hgeo : c * ∑ i ∈ Finset.range k, γ ^ i = D * (1 - γ ^ k) := by
    have hne : γ - 1 ≠ 0 := by linarith
    rw [geom_sum_eq (by linarith : γ ≠ 1), hD]
    field_simp
    ring
  rw [hgeo]
  have hpk : 0 ≤ γ ^ k := pow_nonneg hγ0 k
  nlinarith [mul_le_mul_of_nonneg_left hx hpk]

/-- Cochrane (2023), p. 197: the event that the surpluses of block `n`, dates
`n k, …, n k + k − 1`, are all deficits of size at least `c`. -/
def badBlock (σ : ℕ → Ω → ℝ) (c : ℝ) (k n : ℕ) : Set Ω :=
  ⋂ j ∈ Finset.range k, σ (n * k + j) ⁻¹' Set.Iic (-c)

/-- Cochrane (2023), p. 197: block events are measurable. -/
theorem measurableSet_badBlock [MeasurableSpace Ω] {σ : ℕ → Ω → ℝ}
    (hσ : ∀ t, Measurable (σ t)) (c : ℝ) (k n : ℕ) : MeasurableSet (badBlock σ c k n) :=
  Finset.measurableSet_biInter _ fun _ _ => measurableSet_Iic.preimage (hσ _)

/-- Cochrane (2023), p. 197: the index map `(n, j) ↦ n k + j` is injective on `j < k`, so
different blocks use different dates. -/
theorem block_index_injOn (S : Finset ℕ) (k : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * k + p.2) ↑(S ×ˢ Finset.range k) := by
  intro p hp q hq h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp hq
  have hk : 0 < k := by omega
  have h' : p.2 + k * p.1 = q.2 + k * q.1 := by
    simp only at h
    rw [mul_comm k p.1, mul_comm k q.1, add_comm p.2, add_comm q.2]
    exact h
  have hdiv := congrArg (· / k) h'
  have hmod := congrArg (· % k) h'
  simp only [Nat.add_mul_div_left _ _ hk, Nat.add_mul_mod_self_left,
    Nat.div_eq_of_lt hp.2, Nat.div_eq_of_lt hq.2, Nat.mod_eq_of_lt hp.2,
    Nat.mod_eq_of_lt hq.2, zero_add] at hdiv hmod
  exact Prod.ext hdiv hmod

/-- Cochrane (2023), p. 197: a union of blocks is an intersection of single-date events over
the image of the block indices. -/
theorem biInter_badBlock (σ : ℕ → Ω → ℝ) (c : ℝ) (k : ℕ) (S : Finset ℕ) :
    (⋂ n ∈ S, badBlock σ c k n) =
      ⋂ i ∈ (S ×ˢ Finset.range k).image (fun p : ℕ × ℕ => p.1 * k + p.2),
        σ i ⁻¹' Set.Iic (-c) := by
  ext ω
  simp only [badBlock, Set.mem_iInter, Finset.mem_image, Finset.mem_product,
    Finset.mem_range, Prod.exists, forall_exists_index, and_imp]
  constructor
  · rintro h i n j hn hj rfl
    exact h n hn j hj
  · intro h n hn j hj
    exact h _ n j hn hj rfl

/-- Cochrane (2023), p. 197: the probability of a union of blocks is the product of the
single-date probabilities (independence of the surpluses). -/
theorem measure_biInter_badBlock [MeasurableSpace Ω] {μ : Measure Ω} {σ : ℕ → Ω → ℝ}
    (hind : iIndepFun σ μ) (c : ℝ) (k : ℕ) (S : Finset ℕ) :
    μ (⋂ n ∈ S, badBlock σ c k n) =
      ∏ n ∈ S, ∏ j ∈ Finset.range k, μ (σ (n * k + j) ⁻¹' Set.Iic (-c)) := by
  rw [biInter_badBlock, hind.measure_inter_preimage_eq_mul _ (fun _ _ => measurableSet_Iic),
    Finset.prod_image (block_index_injOn S k), Finset.prod_product]

/-- Cochrane (2023), p. 197: the block events are mutually independent. -/
theorem iIndepSet_badBlock [MeasurableSpace Ω] {μ : Measure Ω} {σ : ℕ → Ω → ℝ}
    (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ μ) (c : ℝ) (k : ℕ) :
    iIndepSet (badBlock σ c k) μ := by
  rw [iIndepSet_iff_meas_biInter (measurableSet_badBlock hσ c k)]
  intro S
  rw [measure_biInter_badBlock hind]
  refine Finset.prod_congr rfl fun n _ => ?_
  have h := measure_biInter_badBlock hind c k {n}
  simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, Finset.prod_singleton] at h
  exact h.symm

/-- Cochrane (2023), p. 197: with probability at least `p` of a bad draw at every date, each
block has probability at least `pᵏ`, so the block probabilities have an infinite sum. -/
theorem tsum_badBlock_eq_top [MeasurableSpace Ω] {μ : Measure Ω} {σ : ℕ → Ω → ℝ}
    (hind : iIndepFun σ μ) {c : ℝ} {p : ENNReal} (hp0 : p ≠ 0)
    (hp : ∀ t, p ≤ μ (σ t ⁻¹' Set.Iic (-c))) (k : ℕ) :
    ∑' n, μ (badBlock σ c k n) = ⊤ := by
  have hle : ∀ n, p ^ k ≤ μ (badBlock σ c k n) := fun n => by
    have h := measure_biInter_badBlock hind c k {n}
    simp only [Finset.mem_singleton, Set.iInter_iInter_eq_left, Finset.prod_singleton] at h
    rw [h]
    calc p ^ k = ∏ _j ∈ Finset.range k, p := by simp
      _ ≤ _ := Finset.prod_le_prod fun j _ => hp _
  refine top_unique ?_
  rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) (pow_ne_zero k hp0)]
  exact ENNReal.tsum_le_tsum hle

/-- **Theorem S** (Cochrane (2023), §6.4.1, p. 197, "you eventually flip 100 heads in a
row"). Let `0 ≤ γ < 1` (permanent `r < g`), let the surplus ratios `σ_t` be independent,
measurable, almost surely bounded above by `K`, and let every date carry probability at least
`p > 0` of a deficit of size at least `c`. Then from every initial debt ratio `x₀`, almost
surely the debt ratio exceeds every level `M < c/(1 − γ)` infinitely often. -/
theorem frequently_exceeds [MeasureSpace Ω] {γ x₀ c K M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t))
    (hind : iIndepFun σ volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K) {p : ENNReal} (hp0 : p ≠ 0)
    (hp : ∀ t, p ≤ volume (σ t ⁻¹' Set.Iic (-c))) :
    ∀ᵐ ω, ∃ᶠ t in atTop, M < debtPath γ x₀ σ t ω := by
  have : IsProbabilityMeasure (volume : Measure Ω) := hind.isProbabilityMeasure
  obtain ⟨k, hk1, hk⟩ := exists_run_length (B := |x₀| + |K| / (1 - γ)) hγ0 hγ1 hM
  have hL : volume (limsup (badBlock σ c k) atTop) = 1 :=
    measure_limsup_eq_one (measurableSet_badBlock hσ c k) (iIndepSet_badBlock hσ hind c k)
      (tsum_badBlock_eq_top hind hp0 hp k)
  have hae : ∀ᵐ ω, ω ∈ limsup (badBlock σ c k) atTop := by
    rw [ae_iff]
    have hm := MeasurableSet.measurableSet_limsup (measurableSet_badBlock hσ c k)
    have := (prob_compl_eq_zero_iff hm).mpr hL
    simpa [Set.compl_def] using this
  filter_upwards [ae_all_iff.2 hK, hae] with ω hKω hω
  rw [Filter.mem_limsup_iff_frequently_mem] at hω
  rw [Filter.frequently_atTop] at hω ⊢
  intro N
  obtain ⟨n, hnN, hn⟩ := hω N
  refine ⟨n * k + k, ?_, ?_⟩
  · nlinarith
  · have hrun : ∀ j < k, σ (n * k + j) ω ≤ -c := fun j hj => by
      have := Set.mem_iInter₂.mp hn j (Finset.mem_range.mpr hj)
      simpa using this
    have h1 := debtPath_run (x₀ := x₀) hγ0 (n * k) k hrun
    have h2 := hk _ (debtPath_lower hγ0 hγ1 hKω (n * k))
    linarith

/-- Cochrane (2023), p. 197 ("no value of debt `b₀/y₀` is sustainable"): under Theorem S's
hypotheses the event that the debt ratio stays below the limit `M` forever has probability
zero, whatever the initial debt `x₀`. -/
theorem not_sustainable [MeasureSpace Ω] {γ x₀ c K M : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hM : M < c / (1 - γ)) {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t))
    (hind : iIndepFun σ volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K) {p : ENNReal} (hp0 : p ≠ 0)
    (hp : ∀ t, p ≤ volume (σ t ⁻¹' Set.Iic (-c))) :
    volume {ω | ∀ t, debtPath γ x₀ σ t ω ≤ M} = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [frequently_exceeds hγ0 hγ1 hM hσ hind hK hp0 hp] with ω hω hall
  obtain ⟨t, ht⟩ := hω.exists
  exact absurd (hall t) (not_le.mpr ht)

/-- Cochrane (2023), p. 197 (an AR(1) "ranges over the entire real line"): if deficits of
every size have probability bounded away from zero at every date, the debt ratio is almost
surely unbounded above: it exceeds every level infinitely often. -/
theorem unbounded_of_unbounded_deficits [MeasureSpace Ω] {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ volume)
    (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K)
    (hdef : ∀ c : ℝ, ∃ p : ENNReal, p ≠ 0 ∧ ∀ t, p ≤ volume (σ t ⁻¹' Set.Iic (-c))) :
    ∀ᵐ ω, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ σ t ω := by
  have h1 : 0 < 1 - γ := by linarith
  have hn : ∀ n : ℕ, ∀ᵐ ω, ∃ᶠ t in atTop, (n : ℝ) < debtPath γ x₀ σ t ω := by
    intro n
    obtain ⟨p, hp0, hp⟩ := hdef ((n + 1) * (1 - γ))
    refine frequently_exceeds hγ0 hγ1 ?_ hσ hind hK hp0 hp
    rw [mul_div_assoc, div_self h1.ne', mul_one]
    linarith
  filter_upwards [ae_all_iff.2 hn] with ω hω M
  obtain ⟨n, hnM⟩ := exists_nat_gt M
  exact (hω n).mono fun t ht => hnM.trans ht

/-- Cochrane (2023), p. 197: i.i.d. surpluses (identically distributed and independent)
whose deficits are unbounded below in distribution make the debt ratio almost surely
unbounded above. -/
theorem iid_unbounded [MeasureSpace Ω] {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ volume)
    (hident : ∀ t, IdentDistrib (σ t) (σ 0) volume volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K)
    (hdef : ∀ c : ℝ, volume (σ 0 ⁻¹' Set.Iic (-c)) ≠ 0) :
    ∀ᵐ ω, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ σ t ω := by
  refine unbounded_of_unbounded_deficits hγ0 hγ1 hσ hind hK fun c => ⟨_, hdef c, fun t => ?_⟩
  rw [(hident t).measure_mem_eq measurableSet_Iic]

/-- Cochrane (2023), p. 197: a Gaussian surplus (non-degenerate) puts positive probability on
deficits of every size. -/
theorem gaussian_deficit_pos [MeasureSpace Ω] {X : Ω → ℝ} (hX : Measurable X) {m : ℝ}
    {v : NNReal} (hv : v ≠ 0) (hlaw : Measure.map X volume = gaussianReal m v) (c : ℝ) :
    volume (X ⁻¹' Set.Iic (-c)) ≠ 0 := by
  rw [← Measure.map_apply hX measurableSet_Iic, hlaw]
  intro h
  have h2 := gaussianReal_absolutelyContinuous' m hv h
  rw [Real.volume_Iic] at h2
  exact ENNReal.top_ne_zero h2

/-- Cochrane (2023), p. 197: i.i.d. Gaussian surplus shocks, truncated above at `K` almost
surely, make the debt ratio almost surely unbounded above (the discrete analogue of the
book's AR(1) argument). -/
theorem gaussian_iid_unbounded [MeasureSpace Ω] {γ x₀ K : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {σ : ℕ → Ω → ℝ} (hσ : ∀ t, Measurable (σ t)) (hind : iIndepFun σ volume)
    (hident : ∀ t, IdentDistrib (σ t) (σ 0) volume volume) (hK : ∀ t, ∀ᵐ ω, σ t ω ≤ K)
    {m : ℝ} {v : NNReal} (hv : v ≠ 0) (hlaw : Measure.map (σ 0) volume = gaussianReal m v) :
    ∀ᵐ ω, ∀ M : ℝ, ∃ᶠ t in atTop, M < debtPath γ x₀ σ t ω :=
  iid_unbounded hγ0 hγ1 hσ hind hident hK fun c => gaussian_deficit_pos (hσ 0) hv hlaw c

/-- Cochrane (2023), p. 197 (correction): with deficits bounded by `c` (`σ_t ≥ −c`), the debt
ratio never exceeds `max x₀ (c/(1 − γ))`, on every path. So bounded surplus support does NOT
make debt eventually exceed *any* bound; Theorem S needs the limit below `c/(1 − γ)`. -/
theorem debtPath_le_of_bounded_deficits {γ x₀ c : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {σ : ℕ → Ω → ℝ} {ω : Ω} (hc : ∀ t, -c ≤ σ t ω) (t : ℕ) :
    debtPath γ x₀ σ t ω ≤ max x₀ (c / (1 - γ)) := by
  have h1 : 0 < 1 - γ := by linarith
  have hce : c / (1 - γ) * (1 - γ) = c := div_mul_cancel₀ _ h1.ne'
  induction t with
  | zero => exact le_max_left _ _
  | succ t ih =>
    rw [debtPath_succ]
    have hm2 := le_max_right x₀ (c / (1 - γ))
    have h2 := mul_le_mul_of_nonneg_left ih hγ0
    have h3 := hc t
    rcases le_total (c / (1 - γ)) x₀ with h | h
    · rw [max_eq_left h] at h2 ⊢
      have hc' : c ≤ x₀ * (1 - γ) := by nlinarith
      nlinarith
    · rw [max_eq_right h] at h2 ⊢
      nlinarith

/-- Cochrane (2023), p. 197 (correction, counterexample to the printed claim): constant
deficits `σ_t = −c` with `c > 0` (a degenerate, bounded, stationary surplus) never push debt
above `max x₀ (c/(1 − γ))`; the level `max x₀ (c/(1 − γ)) + 1` is never reached. -/
theorem bounded_support_counterexample {γ x₀ c : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (t : ℕ)
    (ω : Ω) :
    debtPath γ x₀ (fun _ _ => -c) t ω < max x₀ (c / (1 - γ)) + 1 :=
  (debtPath_le_of_bounded_deficits (σ := fun _ _ => -c) (ω := ω) hγ0 hγ1 (fun _ => le_rfl)
    t).trans_lt (lt_add_one _)

/-- Cochrane (2023), p. 197 ("as debt starts to grow, the government increases surpluses so
as to avoid the boundary"): the managed path `x_{t+1} = min (γ x_t − ε_t) x̄`, generated by
the surplus `σ_t = ε_t + max 0 (γ x_t − ε_t − x̄)`. -/
noncomputable def managedPath (γ x₀ xbar : ℝ) (ε : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | t + 1 => fun ω => γ * managedPath γ x₀ xbar ε t ω -
      (ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar))

/-- Cochrane (2023), p. 197: the managed surplus keeps the debt ratio at or below the limit
`x̄` from date 1 on, for every shock path and every initial debt. -/
theorem managedPath_le (γ x₀ xbar : ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    managedPath γ x₀ xbar ε (t + 1) ω ≤ xbar := by
  change γ * managedPath γ x₀ xbar ε t ω -
      (ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar)) ≤ xbar
  have := le_max_right 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar)
  linarith

/-- Cochrane (2023), p. 197: the managed surplus departs from the unmanaged one only when the
boundary would otherwise be crossed: the extra surplus is zero whenever `γ x_t − ε_t ≤ x̄`. -/
theorem managedPath_eq_of_le {γ x₀ xbar : ℝ} {ε : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω}
    (h : γ * managedPath γ x₀ xbar ε t ω - ε t ω ≤ xbar) :
    managedPath γ x₀ xbar ε (t + 1) ω = γ * managedPath γ x₀ xbar ε t ω - ε t ω := by
  change γ * managedPath γ x₀ xbar ε t ω -
      (ε t ω + max 0 (γ * managedPath γ x₀ xbar ε t ω - ε t ω - xbar)) = _
  rw [max_eq_left (by linarith)]
  ring

end Cochrane.FiscalConstraints.DebtLimitStochastic
