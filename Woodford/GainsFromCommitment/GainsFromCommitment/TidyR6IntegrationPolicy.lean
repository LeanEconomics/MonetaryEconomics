/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.TidyR6IntegrationOrder

/-!
# The price level is `I(0)`, `I(1)` or `I(2)`: page 501 as statements about processes

Woodford (2003), *Interest and Prices*, Chapter 7, §2.1, p. 501 and footnote 22: with cost-push
shocks, the price level is stationary under optimal policy without indexation (`γ = 0`); with
full indexation (`γ = 1`), "under optimal policy, the price is an integrated process of order
one, while under discretion it is an integrated process of order two, since there is a unit root
in the inflation rate"; and under discretion with `γ = 0` the price level has a unit root.

The economy is the genuine i.i.d. one (`ExpectationsMeasureIID.iidSystem` with fair coins, every
history null): the cost-push shock is white noise `u_t = ε_t` (mean `0`, variance `1`), and
E_t is Mathlib's conditional expectation. The policies are given by their laws of motion
(restated for this measure-theoretic system from `ImpulseResponses.Plan`, (1.7) and (2.7), and
from (2.3) for discretion), with the forward sums `∑ⱼ aʲE_tu_{t+j}` computed as
`ExpectationsMeasure.MeasExpectationSystem.forwardSol`; `forwardSol_shock` shows that with
white noise they are the current shock.

## Main results

* `forwardSol_shock`: `∑ⱼ aʲE_tε_{t+j} = ε_t` a.s.
* `optimal_gamma0_I0`: optimal policy, `γ = 0`, stationary initial multiplier: `p` is `I(0)`.
* `optimal_gamma1_I1`: optimal policy, `γ = 1`: `p` is `I(1)` (a unit-root process).
* `discretion_gamma0_I1`: discretion, `γ = 0`: `p` is `I(1)`.
* `discretion_gamma1_I2`: discretion, `γ = 1`: `p` is `I(2)`.
-/

namespace Woodford.GainsFromCommitment.TidyR6IntegrationPolicy

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasure ExpectationsMeasureIID TidyR6IntegrationOrder

/-- Woodford (2003), p. 501: the i.i.d. fair-coin expectation system. -/
noncomputable abbrev Sc : MeasExpectationSystem (ℕ → ℝ) := iidSystem coin

/-! ### White-noise news -/

/-- Woodford (2003), (2.3) and (2.7): with i.i.d. mean-zero shocks the discounted forecast sum is
the current shock, `∑ⱼ aʲ E_t ε_{t+j} = ε_t` a.s. (`|a| < 1`). -/
theorem forwardSol_shock {a : ℝ} (ha : |a| < 1) (t : ℕ) :
    Sc.forwardSol a shock t =ᵐ[Pc] shock t := by
  have hc : Summable (fun k : ℕ => |a| ^ k) := summable_geometric_of_lt_one (abs_nonneg a) ha
  have hm : ∀ k, AEStronglyMeasurable (fun ω : ℕ → ℝ => a ^ k * shock (t + k) ω) Pc :=
    fun k => ((measurable_pi_apply (t + k)).const_mul _).aestronglyMeasurable
  have hf : ∀ k, ∀ᵐ ω ∂Pc, |a ^ k * shock (t + k) ω| ≤ |a| ^ k := fun k =>
    (coord_bdd (t + k)).mono fun ω h => by
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (by positivity) h
  have hs := Sc.E_hasSum hc hm hf t
  have hk : ∀ k, Sc.E t (fun ω => a ^ k * shock (t + k) ω) =ᵐ[Pc]
      fun ω => if k = 0 then shock t ω else 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have e : (fun ω : ℕ → ℝ => a ^ 0 * shock (t + 0) ω) = shock t := by
        funext ω; simp
      rw [e, Sc.E_of_stronglyMeasurable (measurable_shock coin le_rfl).stronglyMeasurable
        (coord_integrable t)]
      exact Eventually.of_forall fun ω => by simp
    · have hmeas : StronglyMeasurable[futureSigma t] (shock (t + k)) :=
        (Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ Set.Ioi t) => coordSigma i)
          (t + k) (by simp only [Set.mem_Ioi]; omega))).stronglyMeasurable
      have e : (fun ω : ℕ → ℝ => a ^ k * shock (t + k) ω) = a ^ k • shock (t + k) := rfl
      rw [e]
      filter_upwards [Sc.E_smul (a ^ k) (shock (t + k)) t, E_future coin t hmeas] with ω h1 h2
      rw [h1, Pi.smul_apply, h2]
      have : ∫ ω', shock (t + k) ω' ∂(iidSystem coin).μ = 0 := integral_coord (t + k)
      simp [this, hk.ne']
  filter_upwards [hs, ae_all_iff.2 hk] with ω h1 h2
  have h3 : (fun k => Sc.E t (fun ω => a ^ k * shock (t + k) ω) ω) =
      fun k => if k = 0 then shock t ω else 0 := funext h2
  rw [h3] at h1
  exact (h1.unique (hasSum_ite_eq 0 (shock t ω))).symm ▸ rfl

/-! ### Small moment facts -/

/-- Woodford (2003), p. 501: a constant has zero variance (probability measure). -/
theorem cov_const (c : ℝ) : cov Pc (fun _ => c) (fun _ => c) = 0 := by
  unfold cov
  simp

/-- Woodford (2003), p. 501: the variance depends only on the a.e. class. -/
theorem cov_congr {X Y : (ℕ → ℝ) → ℝ} (h : X =ᵐ[Pc] Y) : cov Pc X X = cov Pc Y Y := by
  unfold cov
  rw [integral_congr_ae h]
  exact integral_congr_ae (h.mono fun ω hω => by simp only [hω])

/-- Woodford (2003), p. 501: a single coin with weight `a` placed at `t + c`,
`∑_{j < t+c+1} 1[j = t+c] a ε_j = a ε_{t+c}`. -/
theorem sum_single (a : ℝ) (c t : ℕ) (ω : ℕ → ℝ) :
    ∑ j ∈ Finset.range (t + c + 1), (if j = t + c then a else 0) * ω j = a * ω (t + c) := by
  rw [Finset.sum_eq_single (t + c)]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; simp at h

/-- Woodford (2003), p. 501: white noise with a constant mean, `y_t = π̄ + a ε_{t+c}`, is
covariance stationary. -/
theorem covStationary_single (pbar a : ℝ) (c : ℕ) :
    CovStationary Pc (lin (fun _ => pbar) (fun t j => if j = t + c then a else 0)
      (fun t => t + c + 1)) := by
  rw [covStationary_lin_iff]
  refine ⟨fun _ => rfl, fun t h => ?_⟩
  have key : ∀ s, ∑ j ∈ Finset.range (min (s + c + 1) (s + h + c + 1)),
      (if j = s + c then a else 0) * (if j = s + h + c then a else 0) =
        if h = 0 then a * a else 0 := by
    intro s
    rw [min_eq_left (by omega), Finset.sum_eq_single (s + c)]
    · by_cases hh : h = 0
      · subst hh; simp
      · have : s + c ≠ s + h + c := by omega
        simp [hh]
    · intro j _ hj; simp [hj]
    · intro hm; simp at hm
  have e1 := key t
  have e2 := key 0
  simp only [zero_add] at e2
  convert e1.trans e2.symm using 3 <;> ring_nf

/-! ### The multiplier under optimal policy: a stationary AR(1) -/

/-- Woodford (2003), (2.7) with white noise: the coefficients of the multiplier process
`φ_t = m + c₀μ^t ε_0 − k∑_{1≤j≤t} μ^{t−j} ε_j`. -/
noncomputable def phiB (μ c0 k : ℝ) (t j : ℕ) : ℝ :=
  if j = 0 then c0 * μ ^ t else -(k * μ ^ (t - j))

/-- Woodford (2003), (2.7): the coefficients scale by `μ` each period. -/
theorem phiB_succ (μ c0 k : ℝ) {t j : ℕ} (hj : j ≤ t) :
    phiB μ c0 k (t + 1) j = μ * phiB μ c0 k t j := by
  unfold phiB
  split_ifs with h
  · ring
  · rw [show t + 1 - j = (t - j) + 1 by omega, pow_succ]; ring

/-- Woodford (2003), (2.7): after `h` periods the coefficients scale by `μʰ`. -/
theorem phiB_add (μ c0 k : ℝ) {t j : ℕ} (hj : j ≤ t) (h : ℕ) :
    phiB μ c0 k (t + h) j = μ ^ h * phiB μ c0 k t j := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [← add_assoc, phiB_succ μ c0 k (by omega), ih, pow_succ]
    ring

/-- Woodford (2003), (2.7): with `c₀²(1 − μ²) = k²` the variance of the multiplier is
`∑_{j ≤ t} b_{t,j}² = c₀²` at every date (stationary initial condition). -/
theorem phiB_sq_sum {μ c0 k : ℝ} (hc : c0 ^ 2 * (1 - μ ^ 2) = k ^ 2) (t : ℕ) :
    ∑ j ∈ Finset.range (t + 1), phiB μ c0 k t j * phiB μ c0 k t j = c0 ^ 2 := by
  induction t with
  | zero => simp [phiB]; ring
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hlast : phiB μ c0 k (t + 1) (t + 1) = -k := by simp [phiB]
    have hrest : ∑ j ∈ Finset.range (t + 1), phiB μ c0 k (t + 1) j * phiB μ c0 k (t + 1) j =
        μ ^ 2 * ∑ j ∈ Finset.range (t + 1), phiB μ c0 k t j * phiB μ c0 k t j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [phiB_succ μ c0 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
      ring
    rw [hrest, ih, hlast]
    linear_combination -hc

/-- Woodford (2003), (2.7): `Cov(φ_t, φ_{t+h}) = μʰc₀²` for every `t`. -/
theorem phiB_cov {μ c0 k : ℝ} (hc : c0 ^ 2 * (1 - μ ^ 2) = k ^ 2) (t h : ℕ) :
    ∑ j ∈ Finset.range (min (t + 1) (t + h + 1)), phiB μ c0 k t j * phiB μ c0 k (t + h) j =
      μ ^ h * c0 ^ 2 := by
  rw [min_eq_left (by omega), ← phiB_sq_sum hc t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [phiB_add μ c0 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  ring

/-- Woodford (2003), (2.7): the linear coin process of the multiplier. -/
noncomputable def phiL (m μ c0 k : ℝ) : ℕ → (ℕ → ℝ) → ℝ :=
  lin (fun _ => m) (phiB μ c0 k) (fun t => t + 1)

/-- Woodford (2003), (2.7): the multiplier process satisfies
`φ_{t+1} = μφ_t + (1 − μ)m − kε_{t+1}`. -/
theorem phiL_succ (m μ c0 k : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    phiL m μ c0 k (t + 1) ω = μ * phiL m μ c0 k t ω + (1 - μ) * m - k * ω (t + 1) := by
  unfold phiL lin
  rw [Finset.sum_range_succ]
  have hlast : phiB μ c0 k (t + 1) (t + 1) = -k := by simp [phiB]
  have hrest : ∑ j ∈ Finset.range (t + 1), phiB μ c0 k (t + 1) j * ω j =
      μ * ∑ j ∈ Finset.range (t + 1), phiB μ c0 k t j * ω j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [phiB_succ μ c0 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    ring
  rw [hrest, hlast]
  ring

/-- Woodford (2003), (2.7): the multiplier process at date `0` is `m + c₀ε_0`. -/
theorem phiL_zero (m μ c0 k : ℝ) (ω : ℕ → ℝ) : phiL m μ c0 k 0 ω = m + c0 * ω 0 := by
  simp [phiL, lin, phiB]

/-! ### The policy laws in the i.i.d. economy -/

/-- Woodford (2003), (1.7) and (2.7), p. 489 (restated from `ImpulseResponses.Plan` for the
measure-theoretic system; `x` is not needed): under optimal commitment with indexation `γ`,
`π_{t+1} − γπ_t = φ_t − φ_{t+1}` and
`φ_{t+1} = μ₁φ_t − C − k∑ⱼ μ₂^{−j}E_{t+1}u_{t+1+j}` with `C = (1 − μ₁)(λ/κ)x*`,
`k = β⁻¹μ₂⁻¹`, here with white-noise cost-push shocks `u = ε`. -/
def OptLaw (μ1 μ2 C k γ : ℝ) (π φ : ℕ → (ℕ → ℝ) → ℝ) : Prop :=
  (∀ t, π (t + 1) - γ • π t = φ t - φ (t + 1)) ∧
    ∀ t, φ (t + 1) =ᵐ[Pc] μ1 • φ t - (fun _ => C) - k • Sc.forwardSol μ2⁻¹ shock (t + 1)

/-- Woodford (2003), (2.3), p. 487 (with indexation, footnote 22): under discretion,
quasi-differenced inflation is `π̄ + a∑ⱼ (βa)ʲE_tu_{t+j}`, `a = λ/(λ + κ²)`, here with
white-noise cost-push shocks. -/
def DiscLaw (pbar a β γ : ℝ) (π : ℕ → (ℕ → ℝ) → ℝ) : Prop :=
  ∀ t, π (t + 1) - γ • π t =ᵐ[Pc] (fun _ => pbar) + a • Sc.forwardSol (β * a) shock (t + 1)

/-- Woodford (2003), p. 491: the price level, `p_{t+1} = p_t + π_{t+1}`. -/
def PriceLaw (p π : ℕ → (ℕ → ℝ) → ℝ) : Prop := ∀ t, p (t + 1) = p t + π (t + 1)

/-- Woodford (2003), (2.7) in the i.i.d. economy: the multiplier is a.s. the linear coin
process `phiL` with `m = −C/(1 − μ₁)`, given its initial value `m + c₀ε_0`. -/
theorem phi_ae {μ1 μ2 C k γ c0 : ℝ} (hμ1 : μ1 ≠ 1) (hμ2 : |μ2⁻¹| < 1)
    {π φ : ℕ → (ℕ → ℝ) → ℝ} (hL : OptLaw μ1 μ2 C k γ π φ)
    (h0 : φ 0 = fun ω => -C / (1 - μ1) + c0 * ω 0) (t : ℕ) :
    φ t =ᵐ[Pc] phiL (-C / (1 - μ1)) μ1 c0 k t := by
  induction t with
  | zero => exact Eventually.of_forall fun ω => by rw [h0, phiL_zero]
  | succ t ih =>
    filter_upwards [hL.2 t, ih, forwardSol_shock hμ2 (t + 1)] with ω h1 h2 h3
    rw [h1, phiL_succ]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h2, h3, shock]
    have h1μ : 1 - μ1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hμ1)
    field_simp
    ring

/-- Woodford (2003), p. 501: the variance of `π̄ + aε_{t+c}` is `a²`. -/
theorem cov_single (q a : ℝ) (c t : ℕ) :
    cov Pc (lin (fun _ => q) (fun t j => if j = t + c then a else 0) (fun t => t + c + 1) t)
      (lin (fun _ => q) (fun t j => if j = t + c then a else 0) (fun t => t + c + 1) t) =
      a * a := by
  rw [cov_lin, min_self, Finset.sum_eq_single (t + c)]
  · simp
  · intro j _ hj; simp [hj]
  · intro hm; simp at hm

/-- Woodford (2003), p. 501: the random walk `y_t = q_t + a∑_{1≤j≤t} ε_j` has variance `t a²`. -/
theorem cov_walk (q : ℕ → ℝ) (a : ℝ) (t : ℕ) :
    cov Pc (lin q (fun _ j => if j = 0 then 0 else a) (fun t => t + 1) t)
      (lin q (fun _ j => if j = 0 then 0 else a) (fun t => t + 1) t) = t * (a * a) := by
  rw [cov_lin, min_self]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    push_cast
    ring

/-- Woodford (2003), p. 501: the random walk's law of motion. -/
theorem walk_succ (q : ℕ → ℝ) (a : ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    lin q (fun _ j => if j = 0 then 0 else a) (fun t => t + 1) (t + 1) ω =
      lin q (fun _ j => if j = 0 then 0 else a) (fun t => t + 1) t ω + (q (t + 1) - q t) +
        a * ω (t + 1) := by
  unfold lin
  rw [Finset.sum_range_succ (n := t + 1)]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
  ring

/-! ### Page 501 -/

/-- **Woodford (2003), p. 501 (optimal policy, `γ = 0`: "the price level is stationary").** In
the i.i.d. economy with white-noise cost-push shocks, let `(π, φ)` follow the optimal plan
(`OptLaw`, `|μ₁| < 1`, `|μ₂⁻¹| < 1`), with the stationary initial multiplier
`φ_0 = m + c₀ε_0`, `m = −C/(1 − μ₁)`, `c₀²(1 − μ₁²) = k²` (the policy has been followed forever:
the timeless perspective), and let `p_{t₀−1} + φ_{t₀−1} = K` be the price-level target. Then the
price level is covariance stationary: `p` is `I(0)`. -/
theorem optimal_gamma0_I0 {μ1 μ2 C k c0 K : ℝ} (hμ1 : |μ1| < 1) (hμ2 : |μ2⁻¹| < 1)
    (hc : c0 ^ 2 * (1 - μ1 ^ 2) = k ^ 2) {π φ p : ℕ → (ℕ → ℝ) → ℝ}
    (hL : OptLaw μ1 μ2 C k 0 π φ) (hP : PriceLaw p π)
    (h0 : φ 0 = fun ω => -C / (1 - μ1) + c0 * ω 0) (hK : p 0 + φ 0 = fun _ => K) :
    IntegratedOfOrder Pc 0 p := by
  have hμ1' : μ1 ≠ 1 := fun h => by rw [h, abs_one] at hμ1; exact lt_irrefl _ hμ1
  have hpφ : ∀ t, p t + φ t = fun _ => K := by
    intro t
    induction t with
    | zero => exact hK
    | succ t ih =>
      rw [hP t, ← ih]
      have := hL.1 t
      simp only [zero_smul, sub_zero] at this
      rw [this]
      abel
  set m := -C / (1 - μ1)
  have hae : ∀ t, p t =ᵐ[Pc] lin (fun _ => K - m) (fun t j => -phiB μ1 c0 k t j)
      (fun t => t + 1) t := by
    intro t
    filter_upwards [phi_ae hμ1' hμ2 hL h0 t] with ω h
    have e := congrFun (hpφ t) ω
    simp only [Pi.add_apply] at e
    have e2 : p t ω = K - φ t ω := by linarith
    rw [e2, h]
    simp only [phiL, lin, neg_mul, Finset.sum_neg_distrib]
    ring
  refine ⟨?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  rw [show diffN 0 p = p from rfl, covStationary_congr_ae hae, covStationary_lin_iff]
  refine ⟨fun _ => rfl, fun t h => ?_⟩
  simp only [neg_mul_neg]
  rw [phiB_cov hc t h]
  have := phiB_cov hc 0 h
  simp only [zero_add] at this
  rw [this]

/-- **Woodford (2003), p. 501 (optimal policy, `γ = 1`: "the price is an integrated process of
order one").** With full indexation the optimal plan has `π_{t+1} − π_t = φ_t − φ_{t+1}`; with the
stationary initial multiplier and the initial condition of the stationary regime
(`π_{t₀−1} + φ_{t₀−1} = K`, `p_{t₀−1} = P₀` known), and a nonzero response `k` of the multiplier
to cost-push news, the price level is `I(1)`: its first difference (inflation) is covariance
stationary and the price level itself is not. -/
theorem optimal_gamma1_I1 {μ1 μ2 C k c0 K P0 : ℝ} (hμ1 : |μ1| < 1) (hμ2 : |μ2⁻¹| < 1)
    (hk : k ≠ 0) (hc : c0 ^ 2 * (1 - μ1 ^ 2) = k ^ 2) {π φ p : ℕ → (ℕ → ℝ) → ℝ}
    (hL : OptLaw μ1 μ2 C k 1 π φ) (hP : PriceLaw p π)
    (h0 : φ 0 = fun ω => -C / (1 - μ1) + c0 * ω 0) (hK : π 0 + φ 0 = fun _ => K)
    (hp0 : p 0 = fun _ => P0) : IntegratedOfOrder Pc 1 p := by
  have hμ1' : μ1 ≠ 1 := fun h => by rw [h, abs_one] at hμ1; exact lt_irrefl _ hμ1
  have hπφ : ∀ t, π t + φ t = fun _ => K := by
    intro t
    induction t with
    | zero => exact hK
    | succ t ih =>
      rw [← ih]
      have := hL.1 t
      simp only [one_smul] at this
      funext ω
      have := congrFun this ω
      simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
      linarith
  set m := -C / (1 - μ1)
  have hπ : ∀ t, π (t + 1) =ᵐ[Pc] lin (fun _ => K - m) (fun t j => -phiB μ1 c0 k (t + 1) j)
      (fun t => t + 2) t := by
    intro t
    filter_upwards [phi_ae hμ1' hμ2 hL h0 (t + 1)] with ω h
    have e := congrFun (hπφ (t + 1)) ω
    simp only [Pi.add_apply] at e
    have e2 : π (t + 1) ω = K - φ (t + 1) ω := by linarith
    rw [e2, h]
    simp only [phiL, lin, neg_mul, Finset.sum_neg_distrib]
    ring
  have hc0 : c0 ^ 2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    exact hk (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc.symm)
  refine ⟨?_, fun j hj => ?_⟩
  · have hd : ∀ t, diffN 1 p t =ᵐ[Pc] lin (fun _ => K - m) (fun t j => -phiB μ1 c0 k (t + 1) j)
        (fun t => t + 2) t := fun t => by
      filter_upwards [hπ t] with ω h
      simp only [diffN, diff, hP t, Pi.add_apply]
      rw [← h]
      ring
    rw [covStationary_congr_ae hd, covStationary_lin_iff]
    refine ⟨fun _ => rfl, fun t h => ?_⟩
    simp only [neg_mul_neg]
    have A : ∀ s : ℕ, ∑ x ∈ Finset.range (min (s + 2) (s + h + 2)),
        phiB μ1 c0 k (s + 1) x * phiB μ1 c0 k (s + h + 1) x = μ1 ^ h * c0 ^ 2 := fun s => by
      have := phiB_cov hc (s + 1) h
      rwa [show s + 1 + 1 = s + 2 by ring, show s + 1 + h + 1 = s + h + 2 by ring,
        show s + 1 + h = s + h + 1 by ring] at this
    rw [A t]
    have := A 0
    simp only [zero_add] at this ⊢
    rw [this]
  · have hj0 : j = 0 := by omega
    subst hj0
    refine not_covStationary_of_var_ne (t := 1) ?_
    have hp1 : p 1 =ᵐ[Pc] lin (fun _ => P0 + K - m) (fun _ j => -phiB μ1 c0 k 1 j)
        (fun _ => 2) 1 := by
      filter_upwards [hπ 0] with ω h
      rw [hP 0, Pi.add_apply, hp0, h]
      simp only [lin]
      ring
    rw [show diffN 0 p = p from rfl, cov_congr hp1, hp0, cov_const, cov_lin, min_self]
    simp only [neg_mul_neg]
    rw [phiB_sq_sum hc 1]
    exact hc0

/-- **Woodford (2003), p. 501 (discretion, `γ = 0`: a unit root in the price level).** Under
discretion, with white-noise cost-push shocks, `a ≠ 0`, `|βa| < 1` and `p_{t₀−1} = P₀` known,
inflation is `π̄ + aε_t` (stationary) and the price level is `I(1)`. -/
theorem discretion_gamma0_I1 {pbar a β P0 : ℝ} (ha : a ≠ 0) (hβa : |β * a| < 1)
    {π p : ℕ → (ℕ → ℝ) → ℝ} (hL : DiscLaw pbar a β 0 π) (hP : PriceLaw p π)
    (hp0 : p 0 = fun _ => P0) : IntegratedOfOrder Pc 1 p := by
  have hπ : ∀ t, π (t + 1) =ᵐ[Pc] lin (fun _ => pbar) (fun t j => if j = t + 1 then a else 0)
      (fun t => t + 1 + 1) t := by
    intro t
    filter_upwards [hL t, forwardSol_shock hβa (t + 1)] with ω h1 h2
    simp only [zero_smul, sub_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, h2]
    simp only [lin, sum_single, shock]
  refine ⟨?_, fun j hj => ?_⟩
  · have hd : ∀ t, diffN 1 p t =ᵐ[Pc] lin (fun _ => pbar)
        (fun t j => if j = t + 1 then a else 0) (fun t => t + 1 + 1) t := fun t => by
      filter_upwards [hπ t] with ω h
      simp only [diffN, diff, hP t, Pi.add_apply]
      rw [← h]
      ring
    rw [covStationary_congr_ae hd]
    exact covStationary_single pbar a 1
  · have hj0 : j = 0 := by omega
    subst hj0
    refine not_covStationary_of_var_ne (t := 1) ?_
    have hp1 : p 1 =ᵐ[Pc] lin (fun _ => P0 + pbar) (fun t j => if j = t + 0 then a else 0)
        (fun t => t + 0 + 1) 1 := by
      filter_upwards [hπ 0] with ω h
      rw [hP 0, Pi.add_apply, hp0, h]
      simp only [lin]
      ring
    rw [show diffN 0 p = p from rfl, cov_congr hp1, hp0, cov_const, cov_single]
    exact mul_ne_zero ha ha

/-- **Woodford (2003), p. 501 (discretion, `γ = 1`: "an integrated process of order two, since
there is a unit root in the inflation rate").** With full indexation, under discretion the change
in inflation is `π̄ + aε_t`; with `π_{t₀−1} = Pπ` and `p_{t₀−1} = P₀` known, `a ≠ 0`,
`|βa| < 1`, the price level is `I(2)`: its second difference is covariance stationary, while
inflation (a random walk with variance `t a²`) and the price level are not. -/
theorem discretion_gamma1_I2 {pbar a β P0 Pπ : ℝ} (ha : a ≠ 0) (hβa : |β * a| < 1)
    {π p : ℕ → (ℕ → ℝ) → ℝ} (hL : DiscLaw pbar a β 1 π) (hP : PriceLaw p π)
    (hπ0 : π 0 = fun _ => Pπ) (hp0 : p 0 = fun _ => P0) : IntegratedOfOrder Pc 2 p := by
  have hstep : ∀ t, π (t + 1) =ᵐ[Pc] fun ω => π t ω + pbar + a * ω (t + 1) := by
    intro t
    filter_upwards [hL t, forwardSol_shock hβa (t + 1)] with ω h1 h2
    simp only [one_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h2] at h1
    simp only [shock] at h1
    linarith
  set W := lin (fun t : ℕ => Pπ + (t : ℝ) * pbar) (fun _ j => if j = 0 then 0 else a)
    (fun t => t + 1) with hW
  have hπW : ∀ t, π t =ᵐ[Pc] W t := by
    intro t
    induction t with
    | zero =>
      refine Eventually.of_forall fun ω => ?_
      rw [hπ0, hW]
      simp [lin]
    | succ t ih =>
      filter_upwards [hstep t, ih] with ω h1 h2
      rw [h1, h2, hW, walk_succ]
      push_cast
      ring
  refine ⟨?_, fun j hj => ?_⟩
  · have hd : ∀ t, diffN 2 p t =ᵐ[Pc] lin (fun _ => pbar)
        (fun t j => if j = t + 2 then a else 0) (fun t => t + 2 + 1) t := fun t => by
      filter_upwards [hstep (t + 1)] with ω h
      have e1 : p (t + 2) ω = p (t + 1) ω + π (t + 2) ω := by rw [hP (t + 1)]; rfl
      have e2 : p (t + 1) ω = p t ω + π (t + 1) ω := by rw [hP t]; rfl
      simp only [diffN, diff, lin, sum_single]
      rw [show t + 1 + 1 = t + 2 by ring] at h ⊢
      rw [e1, e2, h]
      ring
    rw [covStationary_congr_ae hd]
    exact covStationary_single pbar a 2
  · interval_cases j
    · refine not_covStationary_of_var_ne (t := 1) ?_
      set Wp := lin (fun t : ℕ => P0 + Pπ + (t : ℝ) * pbar) (fun _ j => if j = 0 then 0 else a)
        (fun t => t + 1) with hWp
      have hp1 : p 1 =ᵐ[Pc] Wp 1 := by
        filter_upwards [hπW 1] with ω h
        rw [hP 0, Pi.add_apply, hp0, h, hW, hWp]
        simp only [lin]
        ring
      rw [show diffN 0 p = p from rfl, cov_congr hp1, hp0, cov_const, hWp, cov_walk]
      simp only [Nat.cast_one, one_mul]
      exact mul_ne_zero ha ha
    · refine not_covStationary_of_var_ne (t := 1) ?_
      have hd : ∀ t, diffN 1 p t = π (t + 1) := fun t => by
        funext ω
        simp only [diffN, diff, hP t, Pi.add_apply]
        ring
      rw [hd, hd, cov_congr (hπW 2), cov_congr (hπW 1), hW, cov_walk, cov_walk]
      intro h
      have : a * a = 0 := by push_cast at h; linarith
      exact mul_ne_zero ha ha this

end Woodford.GainsFromCommitment.TidyR6IntegrationPolicy
