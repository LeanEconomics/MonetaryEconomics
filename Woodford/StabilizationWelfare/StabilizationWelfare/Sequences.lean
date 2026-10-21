/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.ForwardSolution
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Bounded sequences, discounted sums and the dispersion recursion

Woodford (2003), *Interest and Prices*, Chapter 6: the discounted sums of bounded sequences that
every welfare criterion of the chapter uses (§2, (2.21)–(2.22), p. 400; App. E.2–E.3,
pp. 695–697; App. E.7, p. 706; (4.18)–(4.20), p. 428; (5.2), p. 456), collected in one place.

* Bounded families (`Bdd`) and their algebra; the lag `lagS`; bounded processes
  (`BoundedProc`) and their algebra (`bdd_mul`, `bdd_sq`, `bdd_shift`, `bdd_congr`,
  `boundedProc_lincomb`, `bdd_of_continuous`).
* Discounted sums: `summable_geom_bdd`, `Bdd.summable`, `abs_tsum_le`, `tsum_geom_shift`,
  `tsum_telescope`, `tsum_telescope_add`, `tsum_add3`; bounded solutions of
  `v_t = d_t + βv_{t+1}` are discounted sums (`forward_real`); the expected discounted sum
  `dsum` of a bounded process (`hasSum_dsum`, `abs_E0_le`); the lagged process `lagP`
  (`lagP_apply`, `lagP_known`).
* The dispersion recursion `Δ_t = αΔ_{t−1} + c q_t` of Proposition 6.3 (p. 400): integrated
  (`disp_integrated`), discounted (`dispersion_tsum` for bounded sequences, any `α`, `|β| < 1`;
  `disp_discounted_hasSum`, a Cauchy product needing only `∑ βᵗ|q_t| < ∞`), and in the Calvo
  form with an initial dispersion `Δ_{−1}` (`disp_bdd`, `disp_discounted`).
-/

namespace Woodford.StabilizationWelfare.Sequences

open Filter Topology

/-! ### Bounded families -/

/-- Woodford (2003), App. E.3, p. 697 (discounted sums of bounded sequences): a real family is
bounded. -/
def Bdd {ι : Type*} (a : ι → ℝ) : Prop := ∃ M, ∀ i, |a i| ≤ M

namespace Bdd

variable {ι κ : Type*}

/-- Woodford (2003), App. E.3, p. 697: constants are bounded. -/
theorem const (c : ℝ) : Bdd (fun _ : ι => c) := ⟨|c|, fun _ => le_rfl⟩

/-- Woodford (2003), App. E.3, p. 697: the bound may be taken nonnegative. -/
theorem nonneg_bound {a : ι → ℝ} (ha : Bdd a) : ∃ M, 0 ≤ M ∧ ∀ i, |a i| ≤ M := by
  obtain ⟨M, hM⟩ := ha
  exact ⟨max M 0, le_max_right _ _, fun i => le_max_of_le_left (hM i)⟩

/-- Woodford (2003), App. E.3, p. 697: sums of bounded families are bounded. -/
theorem add {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun i => a i + b i) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A + B, fun i => (abs_add_le _ _).trans (add_le_add (hA i) (hB i))⟩

/-- Woodford (2003), App. E.3, p. 697: negatives of bounded families are bounded. -/
theorem neg {a : ι → ℝ} (ha : Bdd a) : Bdd (fun i => -a i) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun i => by rw [abs_neg]; exact hA i⟩

/-- Woodford (2003), App. E.3, p. 697: differences of bounded families are bounded. -/
theorem sub {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun i => a i - b i) := by
  simpa [sub_eq_add_neg] using ha.add hb.neg

/-- Woodford (2003), App. E.3, p. 697: products of bounded families are bounded. -/
theorem mul {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) : Bdd (fun i => a i * b i) := by
  obtain ⟨A, hA0, hA⟩ := ha.nonneg_bound
  obtain ⟨B, -, hB⟩ := hb.nonneg_bound
  exact ⟨A * B, fun i => by
    rw [abs_mul]; exact mul_le_mul (hA i) (hB i) (abs_nonneg _) hA0⟩

/-- Woodford (2003), App. E.3, p. 697: quotients by a constant are bounded. -/
theorem div_const {a : ι → ℝ} (ha : Bdd a) (c : ℝ) : Bdd (fun i => a i / c) := by
  simpa [div_eq_mul_inv] using ha.mul (const c⁻¹)

/-- Woodford (2003), App. E.3, p. 697: powers of bounded families are bounded. -/
theorem pow {a : ι → ℝ} (ha : Bdd a) (n : ℕ) : Bdd (fun i => a i ^ n) := by
  induction n with
  | zero => simpa using const (ι := ι) 1
  | succ n ih => simpa [pow_succ] using ih.mul ha

/-- Woodford (2003), (2.21): linear combinations of bounded families are bounded. -/
theorem lin {a b : ι → ℝ} (ha : Bdd a) (hb : Bdd b) (c d : ℝ) :
    Bdd fun i => c * a i + d * b i :=
  ((const c).mul ha).add ((const d).mul hb)

/-- Woodford (2003), App. E.3, p. 697: reindexing a bounded family keeps it bounded. -/
theorem comp {a : ι → ℝ} (ha : Bdd a) (f : κ → ι) : Bdd (fun j => a (f j)) := by
  obtain ⟨A, hA⟩ := ha
  exact ⟨A, fun j => hA (f j)⟩

/-- Woodford (2003), App. E.3, p. 697: the one-period-ahead shift of a bounded sequence is
bounded. -/
theorem shift {a : ℕ → ℝ} (ha : Bdd a) : Bdd (fun t => a (t + 1)) := ha.comp _

end Bdd

/-- Woodford (2003), App. E.3, p. 696: the lagged sequence `a_{t−1}` with initial value
`a_{−1}`. -/
def lagS (am1 : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => am1
  | t + 1 => a t

/-- Woodford (2003), p. 696: the lag at `t + 1` is the value at `t`. -/
@[simp] theorem lagS_succ (am1 : ℝ) (a : ℕ → ℝ) (t : ℕ) : lagS am1 a (t + 1) = a t := rfl

/-- Woodford (2003), p. 696: the lag at date `0` is the initial value. -/
@[simp] theorem lagS_zero (am1 : ℝ) (a : ℕ → ℝ) : lagS am1 a 0 = am1 := rfl

/-- Woodford (2003), p. 696: the lag of a bounded sequence is bounded. -/
theorem Bdd.lagS {a : ℕ → ℝ} (ha : Bdd a) (am1 : ℝ) : Bdd (lagS am1 a) := by
  obtain ⟨A, hA⟩ := ha
  refine ⟨max |am1| A, fun t => ?_⟩
  cases t with
  | zero => exact le_max_left _ _
  | succ t => exact le_max_of_le_right (hA t)

/-- Woodford (2003), p. 696: the lag of the zero sequence with zero initial value is zero. -/
@[simp] theorem lagS_zero_seq (t : ℕ) : lagS 0 (fun _ => 0) t = 0 := by
  cases t <;> rfl

/-- Woodford (2003), p. 697: the lag of a difference is the difference of the lags. -/
theorem lagS_sub (am1 bm1 : ℝ) (a b : ℕ → ℝ) (t : ℕ) :
    lagS (am1 - bm1) (fun s => a s - b s) t = lagS am1 a t - lagS bm1 b t := by
  cases t <;> rfl

/-! ### Discounted sums -/

/-- Woodford (2003), (2.21), p. 400: geometrically weighted bounded sequences are summable
(`|β| < 1`). -/
theorem summable_geom_bdd {β M : ℝ} (hβ : |β| < 1) {a : ℕ → ℝ} (ha : ∀ t, |a t| ≤ M) :
    Summable (fun t => β ^ t * a t) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg β) hβ).mul_right M)
    (fun t => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (ha t) (pow_nonneg (abs_nonneg β) t))

/-- Woodford (2003), (2.21), p. 400: absolute summability of `βᵗ a_t` for a bounded sequence
(`|β| < 1`). -/
theorem summable_norm_geom_bdd {β M : ℝ} (hβ : |β| < 1) {a : ℕ → ℝ} (ha : ∀ t, |a t| ≤ M) :
    Summable (fun t => ‖β ^ t * a t‖) := by
  have h := summable_geom_bdd (β := |β|) (a := fun t => |a t|) (by rwa [abs_abs]) (fun t => by
    rw [abs_abs]; exact ha t)
  refine h.congr fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]

/-- Woodford (2003), App. E.3, p. 697: a bounded sequence is summable against `βᵗ`,
`0 ≤ β < 1`. -/
theorem Bdd.summable {a : ℕ → ℝ} (ha : Bdd a) {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) :
    Summable (fun t => β ^ t * a t) := by
  obtain ⟨A, hA⟩ := ha
  exact summable_geom_bdd (by rwa [abs_of_nonneg h0]) hA

/-- Woodford (2003), (2.21): `|∑ βᵗ f_t| ≤ B/(1 − β)` when `|f_t| ≤ B` (`0 ≤ β < 1`; survey
error 25: a uniform bound `B = O(ε³)` gives an `O(ε³)` discounted remainder). -/
theorem abs_tsum_le {f : ℕ → ℝ} {B β : ℝ} (hf : ∀ t, |f t| ≤ B) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    |∑' t, β ^ t * f t| ≤ B / (1 - β) := by
  have hs := Bdd.summable (a := f) ⟨B, hf⟩ hβ0 hβ1
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left B
  have h1 : |∑' t, β ^ t * f t| ≤ ∑' t, |β ^ t * f t| := by
    have := norm_tsum_le_tsum_norm (f := fun t => β ^ t * f t)
      (by simpa only [Real.norm_eq_abs] using hs.abs)
    simpa only [Real.norm_eq_abs] using this
  have h2 : ∑' t, |β ^ t * f t| ≤ ∑' t, B * β ^ t := by
    refine hs.abs.tsum_le_tsum (fun t => ?_) hg.summable
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hf t) (pow_nonneg hβ0 t)
  rw [hg.tsum_eq] at h2
  calc _ ≤ _ := h1.trans h2
    _ = B / (1 - β) := by rw [div_eq_mul_inv]

/-- Woodford (2003), p. 458: shifting a discounted sum by one period,
`∑ βᵗ a_t = a_0 + β ∑ βᵗ a_{t+1}`. -/
theorem tsum_geom_shift {β : ℝ} {a : ℕ → ℝ} (hs : Summable (fun t => β ^ t * a t)) :
    ∑' t, β ^ t * a t = a 0 + β * ∑' t, β ^ t * a (t + 1) := by
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul]
  congr 1
  exact tsum_congr fun t => by ring

/-- **Woodford (2003), App. E.3, p. 697 (the discounted shift).** For a bounded sequence `K`
and `0 ≤ β < 1`, `∑ βᵗ (K_t − β K_{t+1}) = K_0`: every "lagged" term of a period loss can be
moved one period forward at the cost of an initial-condition term. -/
theorem tsum_telescope {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {K : ℕ → ℝ} (hK : Bdd K) :
    ∑' t, β ^ t * (K t - β * K (t + 1)) = K 0 := by
  have hs := hK.summable h0 h1
  have hs1 := hK.shift.summable h0 h1
  have hfun : (fun t => β ^ t * (K t - β * K (t + 1))) =
      fun t => β ^ t * K t - β * (β ^ t * K (t + 1)) := by
    funext t; ring
  rw [hfun, hs.tsum_sub (hs1.mul_left β), tsum_mul_left, tsum_geom_shift hs]
  ring

/-- **Woodford (2003), App. E.3, p. 697.** If `F_t = G_t + (K_t − β K_{t+1})` with `G`, `K`
bounded, then `∑ βᵗ F_t = ∑ βᵗ G_t + K_0`. -/
theorem tsum_telescope_add {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {F G K : ℕ → ℝ} (hG : Bdd G)
    (hK : Bdd K) (h : ∀ t, F t = G t + (K t - β * K (t + 1))) :
    ∑' t, β ^ t * F t = ∑' t, β ^ t * G t + K 0 := by
  have hK' : Bdd (fun t => K t - β * K (t + 1)) := hK.sub ((Bdd.const β).mul hK.shift)
  have hfun : (fun t => β ^ t * F t) =
      fun t => β ^ t * G t + β ^ t * (K t - β * K (t + 1)) := by
    funext t; rw [h t]; ring
  rw [hfun, (hG.summable h0 h1).tsum_add (hK'.summable h0 h1), tsum_telescope h0 h1 hK]

/-- Woodford (2003), App. E.3, p. 697: discounted sums are linear on bounded sequences,
`∑ βᵗ(k a_t + b_t + c_t) = k ∑ βᵗ a_t + ∑ βᵗ b_t + ∑ βᵗ c_t`. -/
theorem tsum_add3 {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (k : ℝ) {a b c : ℕ → ℝ} (ha : Bdd a)
    (hb : Bdd b) (hc : Bdd c) :
    ∑' t, β ^ t * (k * a t + b t + c t) =
      k * ∑' t, β ^ t * a t + ∑' t, β ^ t * b t + ∑' t, β ^ t * c t := by
  have hfun : (fun t => β ^ t * (k * a t + b t + c t)) =
      fun t => (k * (β ^ t * a t) + β ^ t * b t) + β ^ t * c t := by
    funext t; ring
  rw [hfun, (((ha.summable h0 h1).mul_left k).add (hb.summable h0 h1)).tsum_add
    (hc.summable h0 h1), ((ha.summable h0 h1).mul_left k).tsum_add (hb.summable h0 h1),
    tsum_mul_left]

/-- Woodford (2003), §3.2 and p. 458 ("forward integrated"): a bounded solution of
`v_t = d_t + β v_{t+1}` (`|β| < 1`) is the discounted sum `v_0 = ∑ βᵗ d_t`. -/
theorem forward_real {β M : ℝ} (hβ : |β| < 1) {v d : ℕ → ℝ} (hv : ∀ t, |v t| ≤ M)
    (h : ∀ t, v t = d t + β * v (t + 1)) : v 0 = ∑' t, β ^ t * d t := by
  have hs : Summable (fun t => β ^ t * v t) := summable_geom_bdd hβ hv
  have hs1 : Summable (fun t => β ^ t * v (t + 1)) := summable_geom_bdd hβ (fun t => hv (t + 1))
  have hd : ∀ t, β ^ t * d t = β ^ t * v t - β * (β ^ t * v (t + 1)) := fun t => by
    linear_combination (-(β ^ t)) * h t
  rw [tsum_congr hd, hs.tsum_sub (hs1.mul_left β), tsum_mul_left, tsum_geom_shift hs]
  ring

/-! ### The dispersion recursion of Proposition 6.3 -/

/-- Woodford (2003), p. 400 (integrating (2.20) forward, exact): if
`V_{t+1} = α V_t + c q_t` then `V_{t+1} = α^{t+1} V_0 + ∑_{s ≤ t} α^{t−s} c q_s`
(with `V_0 = Δ_{−1}` the inherited dispersion). -/
theorem disp_integrated {α c : ℝ} {V q : ℕ → ℝ} (hrec : ∀ t, V (t + 1) = α * V t + c * q t)
    (t : ℕ) :
    V (t + 1) = α ^ (t + 1) * V 0 + ∑ s ∈ Finset.range (t + 1), α ^ (t - s) * (c * q s) := by
  induction t with
  | zero => simp [hrec 0]
  | succ t ih =>
    rw [hrec (t + 1), ih, Finset.sum_range_succ _ (t + 1), Nat.sub_self, pow_zero, one_mul,
      mul_add, Finset.mul_sum]
    have : ∀ s ∈ Finset.range (t + 1), α * (α ^ (t - s) * (c * q s)) =
        α ^ (t + 1 - s) * (c * q s) := by
      intro s hs
      rw [Finset.mem_range] at hs
      rw [Nat.sub_add_comm (Nat.lt_succ_iff.mp hs), pow_succ]
      ring
    rw [Finset.sum_congr rfl this]
    ring

/-- Woodford (2003), proof of Propositions 6.3/6.4 (App. E.2, p. 695, integrated): if
`Δ_t = α Δ_{t−1} + k p_t` (here `d t = Δ_{t−1}`) with `Δ`, `p` bounded and `|β| < 1`, then
`(1 − αβ) ∑ βᵗ Δ_t = α Δ_{−1} + k ∑ βᵗ p_t`. -/
theorem dispersion_tsum {α β k M N : ℝ} (hβ : |β| < 1) {d p : ℕ → ℝ} (hd : ∀ t, |d t| ≤ M)
    (hp : ∀ t, |p t| ≤ N) (hrec : ∀ t, d (t + 1) = α * d t + k * p t) :
    (1 - α * β) * ∑' t, β ^ t * d (t + 1) = α * d 0 + k * ∑' t, β ^ t * p t := by
  have hs : Summable (fun t => β ^ t * d t) := summable_geom_bdd hβ hd
  have hsp : Summable (fun t => β ^ t * p t) := summable_geom_bdd hβ hp
  have e1 : ∑' t, β ^ t * d (t + 1) = α * ∑' t, β ^ t * d t + k * ∑' t, β ^ t * p t := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hs.mul_left α).tsum_add (hsp.mul_left k)]
    exact tsum_congr fun t => by rw [hrec t]; ring
  have e2 := tsum_geom_shift hs
  rw [e2] at e1
  linear_combination e1

/-- Woodford (2003), p. 400 (**the discounted sum, exact, genuine `tsum`s**): if
`V_{t+1} = α V_t + c q_t`, `0 ≤ α`, `0 ≤ β`, `αβ < 1` and `∑ βᵗ q_t` converges absolutely,
then `∑ βᵗ V_{t+1}` converges and equals `(α V_0 + c ∑ βᵗ q_t)/(1 − αβ)` (a Cauchy product
of `∑ (αβ)ᵏ` with `∑ βˢ q_s`; no bound on `V` is needed). -/
theorem disp_discounted_hasSum {α β c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α * β < 1)
    {V q : ℕ → ℝ} (hrec : ∀ t, V (t + 1) = α * V t + c * q t)
    (hq : Summable fun t => ‖β ^ t * q t‖) :
    HasSum (fun t => β ^ t * V (t + 1)) ((α * V 0 + c * ∑' t, β ^ t * q t) / (1 - α * β)) := by
  set f : ℕ → ℝ := fun k => (α * β) ^ k with hfdef
  set g : ℕ → ℝ := fun s => β ^ s * q s with hgdef
  have hab0 : 0 ≤ α * β := mul_nonneg hα hβ
  have hf : Summable fun k => ‖f k‖ := by
    simpa [hfdef, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hab0 _)] using
      summable_geometric_of_lt_one hab0 hαβ
  have hcp := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf hq
  have hcs := (summable_norm_sum_mul_range_of_summable_norm hf hq).of_norm
  have hterm : ∀ t, β ^ t * V (t + 1) = (α * V 0) * f t +
      c * ∑ k ∈ Finset.range (t + 1), f k * g (t - k) := by
    intro t
    rw [disp_integrated hrec t]
    have hr := Finset.sum_range_reflect (fun k => f k * g (t - k)) (t + 1)
    simp only [Nat.add_sub_cancel] at hr
    rw [← hr, mul_add, Finset.mul_sum, Finset.mul_sum]
    have : ∀ s ∈ Finset.range (t + 1), β ^ t * (α ^ (t - s) * (c * q s)) =
        c * (f (t - s) * g (t - (t - s))) := by
      intro s hs
      rw [Finset.mem_range] at hs
      have hst : s ≤ t := Nat.lt_succ_iff.mp hs
      rw [Nat.sub_sub_self hst]
      simp only [hfdef, hgdef]
      have : β ^ t = β ^ (t - s) * β ^ s := by rw [← pow_add, Nat.sub_add_cancel hst]
      rw [this, mul_pow]
      ring
    rw [Finset.sum_congr rfl this, pow_succ]
    simp only [hfdef]
    ring
  have hgeo : HasSum f (1 - α * β)⁻¹ := hasSum_geometric_of_lt_one hab0 hαβ
  have hA : HasSum (fun t => (α * V 0) * f t) ((α * V 0) * (1 - α * β)⁻¹) := hgeo.mul_left _
  have hB : HasSum (fun t => c * ∑ k ∈ Finset.range (t + 1), f k * g (t - k))
      (c * ((∑' k, f k) * ∑' s, g s)) := by
    rw [hcp]
    exact hcs.hasSum.mul_left c
  have h := hA.add hB
  rw [hgeo.tsum_eq] at h
  have hpos : (1 : ℝ) - α * β ≠ 0 := by linarith
  convert h using 1
  · funext t
    exact hterm t
  · field_simp

/-- Woodford (2003), (2.20) and (2.24), pp. 399, 402 (the exact second-order law of motion,
Proposition 6.3): `Δ_t = αΔ_{t−1} + α/(1 − α) p_t²`, with `p_t = π_t` (Calvo) or
`p_t = π_t − γπ_{t−1}` (indexation). A bounded `p` gives a bounded `Δ`. -/
theorem disp_bdd {α Δm1 : ℝ} {Δ p : ℕ → ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hp : Bdd p)
    (hrec : ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2) : Bdd Δ := by
  obtain ⟨M, hM0, hM⟩ := hp.nonneg_bound
  have h1α : 0 < 1 - α := by linarith
  set B := max |Δm1| (α * M ^ 2 / (1 - α) ^ 2) with hB
  have hB1 : α * M ^ 2 / (1 - α) ^ 2 ≤ B := le_max_right _ _
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (le_max_left _ _)
  have hstep : ∀ t, |lagS Δm1 Δ t| ≤ B → |Δ t| ≤ B := by
    intro t ht
    rw [hrec t]
    have hp2 : p t ^ 2 ≤ M ^ 2 := by
      have := hM t
      have h' : |p t| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      simpa [sq_abs] using h'
    have hc : α / (1 - α) * p t ^ 2 ≤ (1 - α) * B := by
      have h2 : α * M ^ 2 ≤ (1 - α) ^ 2 * B := by
        rw [div_le_iff₀ (by positivity)] at hB1; linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ h1α]
      nlinarith
    have hc0 : 0 ≤ α / (1 - α) * p t ^ 2 := by positivity
    calc |α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2|
        ≤ |α * lagS Δm1 Δ t| + |α / (1 - α) * p t ^ 2| := abs_add_le _ _
      _ = α * |lagS Δm1 Δ t| + α / (1 - α) * p t ^ 2 := by
          rw [abs_mul, abs_of_nonneg hα0, abs_of_nonneg hc0]
      _ ≤ α * B + (1 - α) * B := add_le_add (mul_le_mul_of_nonneg_left ht hα0) hc
      _ = B := by ring
  refine ⟨B, fun t => ?_⟩
  induction t with
  | zero => exact hstep 0 (le_max_left _ _)
  | succ t ih => exact hstep (t + 1) ih

/-- **Woodford (2003), p. 400 (the discounted dispersion, exact Layer-A form).** Under (2.20),
`∑ βᵗ Δ_t = [αΔ_{−1} + α/(1 − α) ∑ βᵗ p_t²]/(1 − αβ)`; the `Δ_{−1}` term is t.i.p. -/
theorem disp_discounted {α β Δm1 : ℝ} {Δ p : ℕ → ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hp : Bdd p)
    (hrec : ∀ t, Δ t = α * lagS Δm1 Δ t + α / (1 - α) * p t ^ 2) :
    ∑' t, β ^ t * Δ t = (α * Δm1 + α / (1 - α) * ∑' t, β ^ t * p t ^ 2) / (1 - α * β) := by
  obtain ⟨M, hM⟩ := (disp_bdd hα0 hα1 hp hrec).lagS Δm1
  obtain ⟨N, hN⟩ := hp.pow 2
  have hab : 0 < 1 - α * β := by nlinarith
  have h := dispersion_tsum (β := β) (by rw [abs_of_nonneg h0]; exact h1) hM hN
    (fun t => by simp only [lagS_succ]; exact hrec t)
  simp only [lagS_succ, lagS_zero] at h
  rw [eq_div_iff hab.ne']
  linarith

/-! ### Bounded processes and their expected discounted sums -/

variable {Ω : Type*}

/-- Woodford (2003), (5.2): products of bounded processes are bounded. -/
theorem bdd_mul {X Y : ℕ → Ω → ℝ} (hX : BoundedProc X) (hY : BoundedProc Y) :
    BoundedProc (fun t => X t * Y t) := by
  obtain ⟨M, hM⟩ := hX
  obtain ⟨N, hN⟩ := hY
  refine ⟨M * N, fun t w => ?_⟩
  dsimp only
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (hM t w) (hN t w) (abs_nonneg _) ((abs_nonneg _).trans (hM t w))

/-- Woodford (2003), (5.2): squares of bounded processes are bounded. -/
theorem bdd_sq {X : ℕ → Ω → ℝ} (hX : BoundedProc X) : BoundedProc (fun t => X t ^ 2) := by
  obtain ⟨M, hM⟩ := bdd_mul hX hX
  refine ⟨M, fun t w => ?_⟩
  have h := hM t w
  dsimp only at h ⊢
  rw [Pi.mul_apply] at h
  rw [Pi.pow_apply, sq]
  exact h

/-- Woodford (2003), (5.2): shifts of bounded processes are bounded. -/
theorem bdd_shift {X : ℕ → Ω → ℝ} (hX : BoundedProc X) : BoundedProc (fun t => X (t + 1)) := by
  obtain ⟨M, hM⟩ := hX
  exact ⟨M, fun t w => hM (t + 1) w⟩

/-- Woodford (2003), (5.2): boundedness transfers along pointwise equality. -/
theorem bdd_congr {X Y : ℕ → Ω → ℝ} (hX : BoundedProc X) (h : ∀ t w, Y t w = X t w) :
    BoundedProc Y := by
  obtain ⟨M, hM⟩ := hX
  exact ⟨M, fun t w => by rw [h]; exact hM t w⟩

/-- Woodford (2003), (4.18)–(4.20), p. 428: bounded processes are closed under affine
combinations. -/
theorem boundedProc_lincomb {f g : ℕ → Ω → ℝ} (hf : BoundedProc f) (hg : BoundedProc g)
    (a b c : ℝ) : BoundedProc (fun t ω => a * f t ω + b * g t ω + c) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨|a| * M + |b| * N + |c|, fun t ω => ?_⟩
  calc |a * f t ω + b * g t ω + c| ≤ |a * f t ω| + |b * g t ω| + |c| := abs_add_three _ _ _
    _ = |a| * |f t ω| + |b| * |g t ω| + |c| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * M + |b| * N + |c| := by
      gcongr
      · exact hM t ω
      · exact hN t ω

/-- Woodford (2003), (5.2)–(5.4): a continuous function of finitely many bounded processes is a
bounded process. -/
theorem bdd_of_continuous {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ)
    (X : Fin n → ℕ → Ω → ℝ) (hX : ∀ i, BoundedProc (X i)) :
    BoundedProc (fun t w => φ (fun i => X i t w)) := by
  choose M hM using hX
  set B : ℝ := ∑ i, |M i| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => abs_nonneg _
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin n → ℝ) B).exists_bound_of_continuousOn
    hφ.continuousOn
  refine ⟨C, fun t w => ?_⟩
  have hmem : (fun i => X i t w) ∈ Metric.closedBall (0 : Fin n → ℝ) B := by
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hB0]
    intro i
    rw [Real.norm_eq_abs]
    calc |X i t w| ≤ M i := hM i t w
      _ ≤ |M i| := le_abs_self _
      _ ≤ B := Finset.single_le_sum (f := fun i => |M i|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ i)
  have := hC _ hmem
  rwa [Real.norm_eq_abs] at this

variable (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (5.2): the expected discounted sum `E_0 ∑ βᵗ X_t`, evaluated in state `w`
as `∑ βᵗ E_0 X_t` (equal to `E_0` of the pathwise sum for bounded `X`, `E_tsum_dom`). -/
noncomputable def dsum (β : ℝ) (X : ℕ → Ω → ℝ) (w : Ω) : ℝ :=
  ∑' t, β ^ t * 𝔼.E 0 (X t) w

/-- Woodford (2003), (5.2): `E_0` of a bounded process is a bounded real sequence. -/
theorem abs_E0_le {X : ℕ → Ω → ℝ} {M : ℝ} (hM : ∀ t w, |X t w| ≤ M) (w : Ω) (t : ℕ) :
    |𝔼.E 0 (X t) w| ≤ M := 𝔼.abs_E_le (hM t) 0 w

/-- Woodford (2003), (5.2): the discounted expected sum of a bounded process converges. -/
theorem hasSum_dsum {β : ℝ} (hβ : |β| < 1) {X : ℕ → Ω → ℝ} (hX : BoundedProc X) (w : Ω) :
    HasSum (fun t => β ^ t * 𝔼.E 0 (X t) w) (dsum 𝔼 β X w) := by
  obtain ⟨M, hM⟩ := hX
  exact (summable_geom_bdd hβ (fun t => abs_E0_le 𝔼 hM w t)).hasSum

/-- Woodford (2003), Ch. 5 §1.2, p. 333 and (2.28) of Ch. 3 (restated): the lagged process
`x_{t−1}` with initial value `x_{−1}`. -/
def lagP (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => xm1
  | t + 1 => x t

/-- Woodford (2003), p. 333: the lag of a process, state by state, is the lag of the path. -/
theorem lagP_apply (xm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) (t : ℕ) (w : Ω) :
    lagP xm1 x t w = lagS (xm1 w) (fun s => x s w) t := by
  cases t <;> rfl

/-- Woodford (2003), p. 333: the lag of an adapted process with `x_{−1}` known at date 0 is known
at date `t`. -/
theorem lagP_known {xm1 : Ω → ℝ} (hm : 𝔼.E 0 xm1 = xm1) {x : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (t : ℕ) : 𝔼.E t (lagP xm1 x t) = lagP xm1 x t := by
  cases t with
  | zero => exact hm
  | succ t => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hx t)

end Woodford.StabilizationWelfare.Sequences
