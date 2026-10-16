/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.Sequences
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Sqrt

/-!
# The zero interest-rate lower bound (Woodford 2003, §6.4.2, App. E.5)

Woodford (2003), *Interest and Prices*, Chapter 6, §4.2 "The Zero Interest-Rate Lower Bound",
pp. 427–435, with the proof of Proposition 6.9 in Appendix E.5, pp. 700–703.

## Main results

* `mean_ge_k_sd_iff`: "the mean is at least `k` standard deviations above zero" is equivalent
  to `E i² ≤ (1 + k⁻²)(E i)²` and `E i ≥ 0` (p. 428); `K_value` (`K = 1.196` at `k = 2.26`);
  `one_lt_K`.
* `dAvg`: the discounted average `Ê[f] = (1−β) Σ βᵗ E₀ f_t` (a genuine `tsum`), with
  linearity (`dAvg_lincomb`), monotonicity, `dAvg_const`, Jensen `dAvg_sq_ge`, and the
  completing-the-square step (E.25) `dAvg_complete_square`.
* `lagrangian_sufficiency`: Lagrangian sufficiency on an arbitrary set of policies.
* `kkt_exists`: Kuhn–Tucker multipliers for two convex constraints on a convex set of policies in
  any real vector space, under a Slater point, via finite-dimensional separation
  (`geometric_hahn_banach_open` in `ℝ × ℝ × ℝ`).
* `optimal_reformulated`, `prop_6_9_multipliers`: the book's reformulation with the linear
  constraints `m₁ ≥ m̄₁`, `m₂ ≤ m̄₂` and the multipliers of (E.23).
* `det_component_mean`: the decomposition argument that (E.20) never binds, made precise.
* `valueFn`, `envelope`: the envelope step `μ₁ = 2K m̄₁ μ₂` (E.24), under differentiability of
  the value function at `(m̄₁, m̄₂)`.
* `binds_of_unconstrained_infeasible`, `mu2_pos`, `zero_multiplier_of_feasible_min`,
  `binding_zero_multiplier_case`: "`λ̃_i > 0` iff (E.21) binds", made precise.
* `iStarStar_pos`, `iStarStar_K_one` (survey error 22: `K > 1` is needed; at `K = 1` only
  `i** ≥ 0`), `one_le_K_of_feasible`.
* `prop_6_9`: Proposition 6.9 (4.21) assembled; `prop_6_9_slack`.
* `loss_4_22`, `iHat_between`, `iHat_either_sign`: (4.22), `λ̂_i = λ_i + μ₂`.
-/

namespace Woodford.StabilizationWelfare.ZLB

open Filter Topology
open Sequences (bdd_sq boundedProc_lincomb dsum hasSum_dsum)

/-! ### The moment form of the lower-bound constraint -/

/-- Woodford (2003), p. 428: for `k > 0`, the requirement that
the mean be at least `k` standard deviations, `k √(E i² − (E i)²) ≤ E i`, is equivalent to
`E i² ≤ (1 + k⁻²)(E i)²` together with `E i ≥ 0`. -/
theorem mean_ge_k_sd_iff {k m1 m2 : ℝ} (hk : 0 < k) :
    k * Real.sqrt (m2 - m1 ^ 2) ≤ m1 ↔ m2 ≤ (1 + k⁻¹ ^ 2) * m1 ^ 2 ∧ 0 ≤ m1 := by
  have hk' := hk.ne'
  constructor
  · intro h
    have hm1 : 0 ≤ m1 := le_trans (by positivity) h
    have h2 : Real.sqrt (m2 - m1 ^ 2) ≤ m1 / k := by
      rw [le_div_iff₀ hk]; linarith
    rw [Real.sqrt_le_left (by positivity)] at h2
    refine ⟨?_, hm1⟩
    have : m2 - m1 ^ 2 ≤ k⁻¹ ^ 2 * m1 ^ 2 := by
      calc m2 - m1 ^ 2 ≤ (m1 / k) ^ 2 := h2
        _ = k⁻¹ ^ 2 * m1 ^ 2 := by field_simp
    linarith
  · rintro ⟨h, hm1⟩
    have h2 : m2 - m1 ^ 2 ≤ (m1 / k) ^ 2 := by
      calc m2 - m1 ^ 2 ≤ k⁻¹ ^ 2 * m1 ^ 2 := by linarith
        _ = (m1 / k) ^ 2 := by field_simp
    have h3 := (Real.sqrt_le_left (by positivity)).mpr h2
    rw [le_div_iff₀ hk] at h3
    linarith

/-- Woodford (2003), p. 428: `K ≡ 1 + k⁻²`. -/
noncomputable def bigK (k : ℝ) : ℝ := 1 + k⁻¹ ^ 2

/-- Woodford (2003), Table 6.1 and p. 434: at `k = 2.26`, `K = 1.1958… ≈ 1.196`. -/
theorem K_value : |bigK 2.26 - 1.196| < 0.0005 := by
  unfold bigK; rw [abs_lt]; constructor <;> norm_num

/-- Woodford (2003), p. 428: for every finite `k ≠ 0`, `K = 1 + k⁻² > 1`. -/
theorem one_lt_K {k : ℝ} (hk : k ≠ 0) : 1 < bigK k := by
  unfold bigK
  have : 0 < k⁻¹ ^ 2 := by positivity
  linarith

/-- Woodford (2003), p. 428 (Jensen): with `(E i)² ≤ E i²`, the constraint
`E i² ≤ K (E i)²` with `K < 1` forces `E i = 0`; a meaningful bound needs `K ≥ 1`. -/
theorem one_le_K_of_feasible {K m1 m2 : ℝ} (hK : K < 1) (hJ : m1 ^ 2 ≤ m2)
    (hc : m2 ≤ K * m1 ^ 2) : m1 = 0 := by
  have : (1 - K) * m1 ^ 2 ≤ 0 := by nlinarith
  have h2 : m1 ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h2 (sq_nonneg m1))

/-! ### Discounted averages `Ê` -/

variable {S : Type*} (𝔼 : ExpectationSystem S)

/-- Woodford (2003), (4.18)–(4.20), p. 428 and (4.23), p. 430: the discounted average
`Ê[f] = E₀ (1−β) Σ βᵗ f_t`, evaluated in the date-0 state `ω₀`: `(1 − β)` times the expected
discounted sum `Sequences.dsum` (convergent for bounded processes, `Sequences.hasSum_dsum`). -/
noncomputable def dAvg (β : ℝ) (f : ℕ → S → ℝ) (ω0 : S) : ℝ :=
  (1 - β) * dsum 𝔼 β f ω0

/-- Woodford (2003), (4.18)–(4.20): `Ê` is linear on bounded processes and `Ê[c] = c`:
`Ê[a f + b g + c] = a Ê[f] + b Ê[g] + c`. -/
theorem dAvg_lincomb {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → S → ℝ}
    (hf : BoundedProc f) (hg : BoundedProc g) (a b c : ℝ) (ω0 : S) :
    dAvg 𝔼 β (fun t ω => a * f t ω + b * g t ω + c) ω0 =
      a * dAvg 𝔼 β f ω0 + b * dAvg 𝔼 β g ω0 + c := by
  have hE : ∀ t, 𝔼.E 0 (fun ω => a * f t ω + b * g t ω + c) ω0 =
      a * 𝔼.E 0 (f t) ω0 + b * 𝔼.E 0 (g t) ω0 + c := by
    intro t
    have : (fun ω => a * f t ω + b * g t ω + c) = a • f t + b • g t + (fun _ => c) := by
      funext ω; simp [smul_eq_mul]
    rw [this, map_add, map_add, map_smul, map_smul, 𝔼.const]
    rfl
  have hsf := (hasSum_dsum 𝔼 (abs_lt.2 ⟨by linarith, hβ1⟩) hf ω0).summable
  have hsg := (hasSum_dsum 𝔼 (abs_lt.2 ⟨by linarith, hβ1⟩) hg ω0).summable
  have hgeo : HasSum (fun t => β ^ t * c) (c / (1 - β)) := by
    have := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right c
    rwa [div_eq_inv_mul]
  have htot := ((hsf.hasSum.mul_left a).add (hsg.hasSum.mul_left b)).add hgeo
  unfold dAvg dsum
  rw [show (fun t => β ^ t * 𝔼.E 0 (fun ω => a * f t ω + b * g t ω + c) ω0) =
      fun t => a * (β ^ t * 𝔼.E 0 (f t) ω0) + b * (β ^ t * 𝔼.E 0 (g t) ω0) + β ^ t * c from
      funext fun t => by rw [hE t]; ring, htot.tsum_eq]
  have h1 : 1 - β ≠ 0 := by linarith
  field_simp

/-- Woodford (2003), (4.18): `Ê[c] = c`. -/
theorem dAvg_const {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (c : ℝ) (ω0 : S) :
    dAvg 𝔼 β (fun _ _ => c) ω0 = c := by
  have h0 : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → S → ℝ) := ⟨0, fun _ _ => by simp⟩
  have := dAvg_lincomb 𝔼 hβ0 hβ1 h0 h0 0 0 c ω0
  simpa using this

/-- `Ê` is monotone on bounded processes. -/
theorem dAvg_mono {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f g : ℕ → S → ℝ}
    (hf : BoundedProc f) (hg : BoundedProc g) (hfg : ∀ t ω, f t ω ≤ g t ω) (ω0 : S) :
    dAvg 𝔼 β f ω0 ≤ dAvg 𝔼 β g ω0 := by
  unfold dAvg dsum
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  have hβ : |β| < 1 := abs_lt.2 ⟨by linarith, hβ1⟩
  refine Summable.tsum_le_tsum (fun t => ?_) (hasSum_dsum 𝔼 hβ hf ω0).summable
    (hasSum_dsum 𝔼 hβ hg ω0).summable
  exact mul_le_mul_of_nonneg_left (𝔼.mono 0 (fun ω => hfg t ω) ω0) (pow_nonneg hβ0 t)

/-- Woodford (2003), p. 428 (Jensen): `(Ê i)² ≤ Ê[i²]`, so `K ≥ 1` in (4.19) is forced. -/
theorem dAvg_sq_ge {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : ℕ → S → ℝ}
    (hf : BoundedProc f) (ω0 : S) :
    dAvg 𝔼 β f ω0 ^ 2 ≤ dAvg 𝔼 β (fun t ω => f t ω ^ 2) ω0 := by
  set c := dAvg 𝔼 β f ω0
  have hsq : BoundedProc (fun t ω => f t ω ^ 2) := bdd_sq hf
  have hb := boundedProc_lincomb hsq hf 1 (-2 * c) (c ^ 2)
  have h0 : BoundedProc (fun _ _ => (0 : ℝ) : ℕ → S → ℝ) := ⟨0, fun _ _ => by simp⟩
  have hmono := dAvg_mono 𝔼 hβ0 hβ1 h0 hb (fun t ω => by
    show (0 : ℝ) ≤ 1 * f t ω ^ 2 + -2 * c * f t ω + c ^ 2
    nlinarith [sq_nonneg (f t ω - c)]) ω0
  rw [dAvg_const 𝔼 hβ0 hβ1, dAvg_lincomb 𝔼 hβ0 hβ1 hsq hf] at hmono
  nlinarith

/-- Woodford (2003), eq. (E.25), p. 702: completing the square,
`−μ₁ Ê[i] + μ₂ Ê[i²] = μ₂ Ê[(i − μ₁/(2μ₂))²] − μ₁²/(4μ₂)` for `μ₂ ≠ 0`. -/
theorem dAvg_complete_square {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {i : ℕ → S → ℝ}
    (hi : BoundedProc i) {μ1 μ2 : ℝ} (hμ2 : μ2 ≠ 0) (ω0 : S) :
    -μ1 * dAvg 𝔼 β i ω0 + μ2 * dAvg 𝔼 β (fun t ω => i t ω ^ 2) ω0 =
      μ2 * dAvg 𝔼 β (fun t ω => (i t ω - μ1 / (2 * μ2)) ^ 2) ω0 - μ1 ^ 2 / (4 * μ2) := by
  have hsq : BoundedProc (fun t ω => i t ω ^ 2) := bdd_sq hi
  have hfun : (fun t ω => (i t ω - μ1 / (2 * μ2)) ^ 2) =
      fun t ω => 1 * i t ω ^ 2 + (-(μ1 / μ2)) * i t ω + (μ1 / (2 * μ2)) ^ 2 := by
    funext t ω; field_simp; ring
  rw [hfun, dAvg_lincomb 𝔼 hβ0 hβ1 hsq hi]
  field_simp
  ring

/-! ### Lagrangian sufficiency and Kuhn–Tucker existence -/

/-- Woodford (2003), App. E.5, p. 702 (Lagrangian sufficiency): if `p` is feasible
(`g₁ p, g₂ p ≤ 0`), the multipliers are non-negative and complementary-slack, and `p` minimises
the Lagrangian `L + μ₁g₁ + μ₂g₂` over `C`, then `p` solves the constrained problem. No structure
on the set of policies is needed. -/
theorem lagrangian_sufficiency {X : Type*} {C : Set X} {L g1 g2 : X → ℝ} {p : X}
    {μ1 μ2 : ℝ} (hμ1 : 0 ≤ μ1) (hμ2 : 0 ≤ μ2) (hs1 : μ1 * g1 p = 0) (hs2 : μ2 * g2 p = 0)
    (hmin : ∀ q ∈ C, L p + μ1 * g1 p + μ2 * g2 p ≤ L q + μ1 * g1 q + μ2 * g2 q) :
    ∀ q ∈ C, g1 q ≤ 0 → g2 q ≤ 0 → L p ≤ L q := by
  intro q hq h1 h2
  have := hmin q hq
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hμ1 h1, mul_nonpos_of_nonneg_of_nonpos hμ2 h2]

/-- A continuous linear functional on `ℝ × ℝ × ℝ` in coordinates. -/
theorem clm_triple (f : StrongDual ℝ (ℝ × ℝ × ℝ)) (z : ℝ × ℝ × ℝ) :
    f z = z.1 * f (1, 0, 0) + z.2.1 * f (0, 1, 0) + z.2.2 * f (0, 0, 1) := by
  have hz : z = z.1 • ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + z.2.1 • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
      z.2.2 • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  simp [smul_eq_mul]

/-- An elementary step of the separation argument: if `u ≤ v + c a` for every `c ≥ 0`, then
`a ≥ 0`. -/
theorem nonneg_of_forall_le_add_mul {u v a : ℝ} (h : ∀ c : ℝ, 0 ≤ c → u ≤ v + c * a) :
    0 ≤ a := by
  by_contra ha
  push Not at ha
  have hc : 0 ≤ (|v - u| + 1) / (-a) := div_nonneg (by positivity) (by linarith)
  have h1 := h _ hc
  have h2 : (|v - u| + 1) / (-a) * a = -(|v - u| + 1) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_neg, div_self ha.ne, mul_neg_one]
  rw [h2] at h1
  linarith [le_abs_self (v - u)]

/-- Woodford (2003), App. E.5, p. 702 ("by the Kuhn–Tucker theorem"), with the hypotheses the
book leaves implicit: `C` a convex set of policies in a real vector space, `L`, `g₁`, `g₂` convex
on `C`, a Slater point `p₀ ∈ C` with `g₁ p₀ < 0`, `g₂ p₀ < 0`, and `p` a solution of
`min L` on `{q ∈ C | g₁ q ≤ 0, g₂ q ≤ 0}`. Then there are multipliers `μ₁, μ₂ ≥ 0`, complementary
slack, such that `p` minimises `L + μ₁g₁ + μ₂g₂` over `C`. Proof: separate the convex set
`{(t, s₁, s₂) | ∃ q ∈ C, L q ≤ t, g₁ q ≤ s₁, g₂ q ≤ s₂}` from the open convex set
`{t < L p, s₁ < 0, s₂ < 0}` in `ℝ³` (`geometric_hahn_banach_open`). -/
theorem kkt_exists {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X} (hC : Convex ℝ C)
    {L g1 g2 : X → ℝ} (hL : ConvexOn ℝ C L) (hg1 : ConvexOn ℝ C g1) (hg2 : ConvexOn ℝ C g2)
    {p0 p : X} (hp0 : p0 ∈ C) (h01 : g1 p0 < 0) (h02 : g2 p0 < 0) (hp : p ∈ C)
    (hp1 : g1 p ≤ 0) (hp2 : g2 p ≤ 0) (hopt : ∀ q ∈ C, g1 q ≤ 0 → g2 q ≤ 0 → L p ≤ L q) :
    ∃ μ1 μ2 : ℝ, 0 ≤ μ1 ∧ 0 ≤ μ2 ∧ μ1 * g1 p = 0 ∧ μ2 * g2 p = 0 ∧
      ∀ q ∈ C, L p + μ1 * g1 p + μ2 * g2 p ≤ L q + μ1 * g1 q + μ2 * g2 q := by
  set A : Set (ℝ × ℝ × ℝ) := {z | ∃ q ∈ C, L q ≤ z.1 ∧ g1 q ≤ z.2.1 ∧ g2 q ≤ z.2.2} with hA
  set B : Set (ℝ × ℝ × ℝ) := {z | z.1 < L p ∧ z.2.1 < 0 ∧ z.2.2 < 0} with hB
  have hBopen : IsOpen B :=
    (isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt (continuous_fst.comp continuous_snd) continuous_const).inter
        (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const))
  have hBconv : Convex ℝ B := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx2, hx3⟩ := hx
    obtain ⟨hy1, hy2, hy3⟩ := hy
    have key : ∀ u v w : ℝ, u < w → v < w → a * u + b * v < w := by
      intro u v w hu hv
      rcases eq_or_lt_of_le ha with h | h
      · rw [← h, zero_add] at hab
        rw [← h, hab]; simp [hv]
      · have : a * u < a * w := mul_lt_mul_of_pos_left hu h
        have : b * v ≤ b * w := mul_le_mul_of_nonneg_left hv.le hb
        have : a * w + b * w = w := by rw [← add_mul, hab, one_mul]
        linarith
    refine ⟨?_, ?_, ?_⟩
    · simpa using key _ _ _ hx1 hy1
    · simpa using key _ _ _ hx2 hy2
    · simpa using key _ _ _ hx3 hy3
  have hAconv : Convex ℝ A := by
    intro x hx y hy a b ha hb hab
    obtain ⟨q, hq, hq1, hq2, hq3⟩ := hx
    obtain ⟨r, hr, hr1, hr2, hr3⟩ := hy
    refine ⟨a • q + b • r, hC hq hr ha hb hab, ?_, ?_, ?_⟩
    · have := hL.2 hq hr ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith
    · have := hg1.2 hq hr ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      nlinarith
    · have := hg2.2 hq hr ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
  have hdisj : Disjoint B A := by
    rw [Set.disjoint_left]
    rintro z ⟨hz1, hz2, hz3⟩ ⟨q, hq, hq1, hq2, hq3⟩
    have := hopt q hq (by linarith) (by linarith)
    linarith
  obtain ⟨f, u, hfB, hfA⟩ := geometric_hahn_banach_open hBconv hBopen hAconv hdisj
  set a0 := f (1, 0, 0)
  set a1 := f (0, 1, 0)
  set a2 := f (0, 0, 1)
  have hf : ∀ z, f z = z.1 * a0 + z.2.1 * a1 + z.2.2 * a2 := clm_triple f
  -- the value point of `p` lies in `A`, and so do all its upward translates
  have hup : ∀ c₀ c₁ c₂ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ → 0 ≤ c₂ →
      u ≤ (L p + c₀) * a0 + (g1 p + c₁) * a1 + (g2 p + c₂) * a2 := by
    intro c₀ c₁ c₂ h0 h1 h2
    have := hfA (L p + c₀, g1 p + c₁, g2 p + c₂) ⟨p, hp, by simp [h0], by simp [h1], by simp [h2]⟩
    rwa [hf] at this
  have ha0 : 0 ≤ a0 := nonneg_of_forall_le_add_mul (u := u)
    (v := L p * a0 + g1 p * a1 + g2 p * a2)
    (fun c hc => by have := hup c 0 0 hc le_rfl le_rfl; nlinarith [this])
  have ha1 : 0 ≤ a1 := nonneg_of_forall_le_add_mul (u := u)
    (v := L p * a0 + g1 p * a1 + g2 p * a2)
    (fun c hc => by have := hup 0 c 0 le_rfl hc le_rfl; nlinarith [this])
  have ha2 : 0 ≤ a2 := nonneg_of_forall_le_add_mul (u := u)
    (v := L p * a0 + g1 p * a1 + g2 p * a2)
    (fun c hc => by have := hup 0 0 c le_rfl le_rfl hc; nlinarith [this])
  -- the corner `(L p, 0, 0)` of `B`
  have hcorner : L p * a0 ≤ u := by
    by_contra h
    push Not at h
    set δ := (L p * a0 - u) / (2 * (a0 + a1 + a2 + 1)) with hδ
    have hden : 0 < 2 * (a0 + a1 + a2 + 1) := by linarith
    have hδpos : 0 < δ := div_pos (by linarith) hden
    have hmem : (L p - δ, -δ, -δ) ∈ B := ⟨by linarith, by linarith, by linarith⟩
    have := hfB _ hmem
    rw [hf] at this
    simp only at this
    have hδeq : δ * (2 * (a0 + a1 + a2 + 1)) = L p * a0 - u := by
      rw [hδ]; field_simp
    nlinarith
  -- the Lagrangian inequality with weight `a0`
  have hlag : ∀ q ∈ C, L p * a0 ≤ L q * a0 + g1 q * a1 + g2 q * a2 := by
    intro q hq
    have := hfA (L q, g1 q, g2 q) ⟨q, hq, le_rfl, le_rfl, le_rfl⟩
    rw [hf] at this
    simp only at this
    linarith
  -- Slater: `a0 > 0`
  have ha0pos : 0 < a0 := by
    rcases eq_or_lt_of_le ha0 with h | h
    · exfalso
      have h1 := hlag p0 hp0
      rw [← h] at h1
      simp only [mul_zero, zero_add] at h1
      have hz1 : a1 = 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha1 h01.le,
        mul_nonpos_of_nonneg_of_nonpos ha2 h02.le]
      have hz2 : a2 = 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos ha1 h01.le,
        mul_nonpos_of_nonneg_of_nonpos ha2 h02.le]
      have hmem : (L p - 1, -1, -1) ∈ B := ⟨by linarith, by norm_num, by norm_num⟩
      have h3 := hfB _ hmem
      have h4 := hup 0 0 0 le_rfl le_rfl le_rfl
      rw [hf, ← h, hz1, hz2] at h3
      rw [← h, hz1, hz2] at h4
      simp only [mul_zero, add_zero] at h3 h4
      linarith
    · exact h
  have hp' := hlag p hp
  have hx1 : a1 * g1 p = 0 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hp1 ha1,
    mul_nonpos_of_nonpos_of_nonneg hp2 ha2]
  have hx2 : a2 * g2 p = 0 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg hp1 ha1,
    mul_nonpos_of_nonpos_of_nonneg hp2 ha2]
  refine ⟨a1 / a0, a2 / a0, div_nonneg ha1 ha0, div_nonneg ha2 ha0, ?_, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, hx1, zero_div]
  · rw [div_mul_eq_mul_div, hx2, zero_div]
  · intro q hq
    have h := hlag q hq
    refine le_of_mul_le_mul_left ?_ ha0pos
    have e : ∀ x y z : ℝ, a0 * (x + a1 / a0 * y + a2 / a0 * z) = a0 * x + a1 * y + a2 * z := by
      intro x y z; field_simp
    rw [e, e]
    nlinarith

/-! ### Proposition 6.9: the constrained problem and its multipliers -/

/-- Woodford (2003), (4.18)–(4.19), p. 428 / (E.20)–(E.21): a policy `p ∈ C` (`C` = the policies
consistent with the structural equations) is feasible if `m₁ p ≥ 0` and `m₂ p ≤ K (m₁ p)²`,
where `m₁, m₂` are the discounted averages of `i` and `i²`. -/
def Feasible {X : Type*} (C : Set X) (m1 m2 : X → ℝ) (K : ℝ) (p : X) : Prop :=
  p ∈ C ∧ 0 ≤ m1 p ∧ m2 p ≤ K * m1 p ^ 2

/-- Woodford (2003), Proposition 6.9, p. 428: `p` minimises (4.20) subject to (4.18)–(4.19). -/
def IsConstrOpt {X : Type*} (C : Set X) (L m1 m2 : X → ℝ) (K : ℝ) (p : X) : Prop :=
  Feasible C m1 m2 K p ∧ ∀ q, Feasible C m1 m2 K q → L p ≤ L q

/-- Woodford (2003), App. E.5, p. 702: the constrained optimum also solves the problem with
the constraints `m₁ ≥ m̄₁`, `m₂ ≤ m̄₂` (`m̄ᵢ` its own moments), since any such policy satisfies
(E.20)–(E.21) (needs `K ≥ 0`). -/
theorem optimal_reformulated {X : Type*} {C : Set X} {L m1 m2 : X → ℝ} {K : ℝ} {p : X}
    (hK : 0 ≤ K) (hopt : IsConstrOpt C L m1 m2 K p) :
    ∀ q ∈ C, m1 p ≤ m1 q → m2 q ≤ m2 p → L p ≤ L q := by
  intro q hq h1 h2
  obtain ⟨⟨_, hp1, hp2⟩, hmin⟩ := hopt
  refine hmin q ⟨hq, le_trans hp1 h1, ?_⟩
  have : m1 p ^ 2 ≤ m1 q ^ 2 := pow_le_pow_left₀ hp1 h1 2
  nlinarith

/-- Woodford (2003), (E.23), p. 702: the multiplier form. With `C` convex, `L` convex, `m₁`
concave and `m₂` convex on `C` (true when the interest path is linear in the policy, see
`dAvg_affine`, `dAvg_sq_convex`), `K ≥ 0` and a Slater point `p₀ ∈ C` with `m₁ p₀ > m̄₁`,
`m₂ p₀ < m̄₂`, there are `μ₁, μ₂ ≥ 0` such that the optimum minimises
`L − μ₁ m₁ + μ₂ m₂` over `C`. -/
theorem prop_6_9_multipliers {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X}
    (hC : Convex ℝ C) {L m1 m2 : X → ℝ} {K : ℝ} (hL : ConvexOn ℝ C L) (hm1 : ConcaveOn ℝ C m1)
    (hm2 : ConvexOn ℝ C m2) (hK : 0 ≤ K) {p p0 : X} (hopt : IsConstrOpt C L m1 m2 K p)
    (hp0 : p0 ∈ C) (h01 : m1 p < m1 p0) (h02 : m2 p0 < m2 p) :
    ∃ μ1 μ2 : ℝ, 0 ≤ μ1 ∧ 0 ≤ μ2 ∧
      ∀ q ∈ C, L p - μ1 * m1 p + μ2 * m2 p ≤ L q - μ1 * m1 q + μ2 * m2 q := by
  have hg1 : ConvexOn ℝ C ((fun _ => m1 p) + -m1) := (convexOn_const _ hC).add hm1.neg
  have hg2 : ConvexOn ℝ C (m2 + fun _ => -m2 p) := hm2.add (convexOn_const _ hC)
  obtain ⟨μ1, μ2, hμ1, hμ2, -, -, hlag⟩ := kkt_exists hC hL hg1 hg2 hp0
    (by simp only [Pi.add_apply, Pi.neg_apply]; linarith)
    (by simp only [Pi.add_apply]; linarith) hopt.1.1
    (by simp) (by simp)
    (fun q hq h1 h2 => optimal_reformulated hK hopt q hq
      (by simp only [Pi.add_apply, Pi.neg_apply] at h1; linarith)
      (by simp only [Pi.add_apply] at h2; linarith))
  refine ⟨μ1, μ2, hμ1, hμ2, fun q hq => ?_⟩
  have := hlag q hq
  simp only [Pi.add_apply, Pi.neg_apply] at this
  linarith

/-! ### The envelope step (E.24) -/

/-- Woodford (2003), App. E.5, p. 702: the value function
`V(a₁, a₂) = inf {L q | q ∈ C, m₁ q ≥ a₁, m₂ q ≤ a₂}` of the reformulated problem. -/
noncomputable def valueFn {X : Type*} (C : Set X) (L m1 m2 : X → ℝ) (a : ℝ × ℝ) : ℝ :=
  sInf (L '' {q | q ∈ C ∧ a.1 ≤ m1 q ∧ m2 q ≤ a.2})

/-- The multipliers give an affine minorant of the value function: wherever the constraint set
is non-empty, `V(a) ≥ L p + μ₁(a₁ − m̄₁) − μ₂(a₂ − m̄₂)`. -/
theorem valueFn_ge_lag {X : Type*} {C : Set X} {L m1 m2 : X → ℝ} {p : X} {μ1 μ2 : ℝ}
    (hμ1 : 0 ≤ μ1) (hμ2 : 0 ≤ μ2)
    (hlag : ∀ q ∈ C, L p - μ1 * m1 p + μ2 * m2 p ≤ L q - μ1 * m1 q + μ2 * m2 q)
    {a : ℝ × ℝ} (hne : ∃ q ∈ C, a.1 ≤ m1 q ∧ m2 q ≤ a.2) :
    L p + μ1 * (a.1 - m1 p) - μ2 * (a.2 - m2 p) ≤ valueFn C L m1 m2 a := by
  obtain ⟨q0, hq0, hq01, hq02⟩ := hne
  refine le_csInf ⟨L q0, q0, ⟨hq0, hq01, hq02⟩, rfl⟩ ?_
  rintro b ⟨q, ⟨hq, hq1, hq2⟩, rfl⟩
  have := hlag q hq
  nlinarith [mul_le_mul_of_nonneg_left hq1 hμ1, mul_le_mul_of_nonneg_left hq2 hμ2]

/-- Along the constraint frontier: for `a₁ ≥ 0`, `a₂ ≤ K a₁²` every policy in the constraint
set of `V(a)` is feasible for the original problem, so `V(a) ≥ L p`. -/
theorem valueFn_ge_opt {X : Type*} {C : Set X} {L m1 m2 : X → ℝ} {K : ℝ} {p : X}
    (hK : 0 ≤ K) (hopt : IsConstrOpt C L m1 m2 K p) {a : ℝ × ℝ} (ha1 : 0 ≤ a.1)
    (ha2 : a.2 ≤ K * a.1 ^ 2) (hne : ∃ q ∈ C, a.1 ≤ m1 q ∧ m2 q ≤ a.2) :
    L p ≤ valueFn C L m1 m2 a := by
  obtain ⟨q0, hq0, hq01, hq02⟩ := hne
  refine le_csInf ⟨L q0, q0, ⟨hq0, hq01, hq02⟩, rfl⟩ ?_
  rintro b ⟨q, ⟨hq, hq1, hq2⟩, rfl⟩
  refine hopt.2 q ⟨hq, le_trans ha1 hq1, ?_⟩
  have : a.1 ^ 2 ≤ m1 q ^ 2 := pow_le_pow_left₀ ha1 hq1 2
  nlinarith

/-- At the optimum's own moments the value function equals the optimal loss. -/
theorem valueFn_at {X : Type*} {C : Set X} {L m1 m2 : X → ℝ} {K : ℝ} {p : X}
    (hK : 0 ≤ K) (hopt : IsConstrOpt C L m1 m2 K p) :
    valueFn C L m1 m2 (m1 p, m2 p) = L p := by
  refine IsLeast.csInf_eq ⟨⟨p, ⟨hopt.1.1, le_rfl, le_rfl⟩, rfl⟩, ?_⟩
  rintro b ⟨q, ⟨hq, hq1, hq2⟩, rfl⟩
  exact optimal_reformulated hK hopt q hq hq1 hq2

/-- Woodford (2003), eq. (E.24), p. 702: "`μ₁ = 2K m₁ μ₂` since `2K m₁` is the slope of the
frontier of the constraint set (E.21)". Precisely: if (E.21) binds at the optimum
(`m̄₂ = K m̄₁²`), (E.20) is slack (`m̄₁ > 0`), there is a Slater point, `(μ₁, μ₂) ≥ 0` satisfy
(E.23), and the value function `V` is (Fréchet) differentiable at `(m̄₁, m̄₂)`, then
`μ₁ = 2K m̄₁ μ₂`. (The derivative of `V` is `(μ₁, −μ₂)` and `V` is minimised at `m̄₁` along the
frontier `a₂ = K a₁²`.) -/
theorem envelope {X : Type*} {C : Set X} {L m1 m2 : X → ℝ} {K : ℝ} {p p0 : X} (hK : 0 ≤ K)
    (hopt : IsConstrOpt C L m1 m2 K p) (hbind : m2 p = K * m1 p ^ 2) (hpos : 0 < m1 p)
    (hp0 : p0 ∈ C) (h01 : m1 p < m1 p0) (h02 : m2 p0 < m2 p) {μ1 μ2 : ℝ} (hμ1 : 0 ≤ μ1)
    (hμ2 : 0 ≤ μ2)
    (hlag : ∀ q ∈ C, L p - μ1 * m1 p + μ2 * m2 p ≤ L q - μ1 * m1 q + μ2 * m2 q)
    {V' : ℝ × ℝ →L[ℝ] ℝ} (hV : HasFDerivAt (valueFn C L m1 m2) V' (m1 p, m2 p)) :
    μ1 = 2 * K * m1 p * μ2 := by
  set a1 := m1 p
  set a2 := m2 p
  -- near `(a₁, a₂)` the Slater point lies in the constraint set
  have hU : ∀ᶠ a in 𝓝 (a1, a2), ∃ q ∈ C, a.1 ≤ m1 q ∧ m2 q ≤ a.2 := by
    have hopen : IsOpen {a : ℝ × ℝ | a.1 < m1 p0 ∧ m2 p0 < a.2} :=
      (isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt continuous_const continuous_snd)
    filter_upwards [hopen.mem_nhds ⟨h01, h02⟩] with a ha
    exact ⟨p0, hp0, ha.1.le, ha.2.le⟩
  -- (B) the derivative of `V` in direction `(1, 2K a₁)` is `μ₁ − 2K a₁ μ₂`
  set γB : ℝ → ℝ × ℝ := fun t => (a1 + t, a2 + t * (2 * K * a1)) with hγBdef
  have hγB : HasDerivAt γB ((1 : ℝ), 2 * K * a1) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using HasDerivAt.const_add a1 (hasDerivAt_id (0 : ℝ))
    · simpa using HasDerivAt.const_add a2 (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ))
        (2 * K * a1))
  have hγB0 : γB 0 = (a1, a2) := by simp [hγBdef]
  have hB := hV.comp_hasDerivAt_of_eq 0 hγB hγB0.symm
  have hψ : HasDerivAt (fun t => valueFn C L m1 m2 (γB t) - (L p + t * (μ1 - μ2 * (2 * K * a1))))
      (V' ((1 : ℝ), 2 * K * a1) - (μ1 - μ2 * (2 * K * a1))) 0 := by
    refine HasDerivAt.sub hB ?_
    simpa using HasDerivAt.const_add (L p) (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ))
      (μ1 - μ2 * (2 * K * a1)))
  have hminB : IsLocalMin
      (fun t => valueFn C L m1 m2 (γB t) - (L p + t * (μ1 - μ2 * (2 * K * a1)))) 0 := by
    have hcont : Tendsto γB (𝓝 0) (𝓝 (a1, a2)) := by
      rw [← hγB0]; exact hγB.continuousAt.tendsto
    filter_upwards [hcont.eventually hU] with t ht
    have h1 := valueFn_ge_lag hμ1 hμ2 hlag ht
    have h0 : valueFn C L m1 m2 (γB 0) = L p := by rw [hγB0]; exact valueFn_at hK hopt
    simp only [hγBdef] at h1 ⊢
    simp only [hγBdef] at h0
    rw [h0]
    nlinarith
  have hzeroB := hminB.hasDerivAt_eq_zero hψ
  -- (A) along the frontier `a₂ = K a₁²` the value function is minimised at `a₁`
  set γA : ℝ → ℝ × ℝ := fun t => (a1 + t, K * (a1 + t) ^ 2) with hγAdef
  have hγA : HasDerivAt γA ((1 : ℝ), 2 * K * a1) 0 := by
    refine HasDerivAt.prodMk ?_ ?_
    · simpa using HasDerivAt.const_add a1 (hasDerivAt_id (0 : ℝ))
    · have := HasDerivAt.const_mul K (HasDerivAt.pow (HasDerivAt.const_add a1
        (hasDerivAt_id' (0 : ℝ))) 2)
      convert this using 1
      norm_num
      ring
  have hγA0 : γA 0 = (a1, a2) := by simp [hγAdef, hbind]
  have hA := hV.comp_hasDerivAt_of_eq 0 hγA hγA0.symm
  have hminA : IsLocalMin (fun t => valueFn C L m1 m2 (γA t)) 0 := by
    have hcont : Tendsto γA (𝓝 0) (𝓝 (a1, a2)) := by
      rw [← hγA0]; exact hγA.continuousAt.tendsto
    have hnn : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ a1 + t := by
      have : Set.Ioi (-a1) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds (by linarith)
      filter_upwards [this] with t ht
      simp only [Set.mem_Ioi] at ht
      linarith
    filter_upwards [hcont.eventually hU, hnn] with t ht htn
    have h1 := valueFn_ge_opt hK hopt (a := γA t) htn le_rfl ht
    have h0 : valueFn C L m1 m2 (γA 0) = L p := by rw [hγA0]; exact valueFn_at hK hopt
    simp only [hγAdef] at h1 h0 ⊢
    linarith
  have hzeroA := hminA.hasDerivAt_eq_zero hA
  rw [sub_eq_zero] at hzeroB
  rw [hzeroB] at hzeroA
  linarith

/-! ### When does the interest-rate penalty appear? -/

/-- Woodford (2003), p. 701 ("`λ̃_i > 0` iff (E.21) binds"), the binding half made precise: if
(E.20) is slack (`m̄₁ > 0`) and NO unconstrained minimiser of `L` over `C` satisfies
(E.20)–(E.21) (the sense of "binds" on p. 429: (4.19) is violated by the unconstrained
optimum), then (E.21) holds with equality at the constrained optimum. Needs `L` convex, `m₁`
affine and `m₂` convex on the convex set `C`. -/
theorem binds_of_unconstrained_infeasible {X : Type*} [AddCommGroup X] [Module ℝ X]
    {C : Set X} {L m1 m2 : X → ℝ} {K : ℝ} (hL : ConvexOn ℝ C L) (hm1 : ConvexOn ℝ C m1)
    (hm1' : ConcaveOn ℝ C m1) (hm2 : ConvexOn ℝ C m2) {p : X}
    (hopt : IsConstrOpt C L m1 m2 K p) (hpos : 0 < m1 p)
    (hno : ∀ q ∈ C, (∀ r ∈ C, L q ≤ L r) → ¬ Feasible C m1 m2 K q) :
    m2 p = K * m1 p ^ 2 := by
  obtain ⟨⟨hp, _, hp2⟩, hmin⟩ := hopt
  by_contra hne
  have hlt : m2 p < K * m1 p ^ 2 := lt_of_le_of_ne hp2 hne
  refine hno p hp (fun q hq => ?_) ⟨hp, hpos.le, hp2⟩
  by_contra hLq
  push Not at hLq
  -- small steps from `p` towards `q` stay feasible and lower the loss
  set A : ℝ → ℝ := fun t => (1 - t) * m1 p + t * m1 q
  set D : ℝ → ℝ := fun t => K * A t ^ 2 - ((1 - t) * m2 p + t * m2 q)
  have hA : Tendsto A (𝓝 0) (𝓝 (m1 p)) := by
    have : Continuous A := by fun_prop
    simpa [A] using this.tendsto 0
  have hD : Tendsto D (𝓝 0) (𝓝 (K * m1 p ^ 2 - m2 p)) := by
    have : Continuous D := by fun_prop
    simpa [D, A] using this.tendsto 0
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < A t ∧ 0 < D t ∧ t < 1 := by
    have h1 := hA.eventually (lt_mem_nhds hpos)
    have h2 := hD.eventually (lt_mem_nhds (by linarith : (0 : ℝ) < K * m1 p ^ 2 - m2 p))
    have h3 : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 := gt_mem_nhds (by norm_num)
    exact nhdsWithin_le_nhds (h1.and (h2.and h3))
  obtain ⟨t, ⟨hAt, hDt, ht1⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  replace ht0 : 0 < t := ht0
  have hab : (1 - t) + t = 1 := by ring
  have hpt : (1 - t) • p + t • q ∈ C := hm1.1 hp hq (by linarith) ht0.le hab
  have hm1eq : m1 ((1 - t) • p + t • q) = A t := by
    have h1 := hm1.2 hp hq (by linarith) ht0.le hab
    have h2 := hm1'.2 hp hq (by linarith) ht0.le hab
    simp only [smul_eq_mul] at h1 h2
    exact le_antisymm h1 h2
  have hm2le : m2 ((1 - t) • p + t • q) ≤ (1 - t) * m2 p + t * m2 q := by
    have := hm2.2 hp hq (by linarith) ht0.le hab
    simpa [smul_eq_mul] using this
  have hLle : L ((1 - t) • p + t • q) ≤ (1 - t) * L p + t * L q := by
    have := hL.2 hp hq (by linarith) ht0.le hab
    simpa [smul_eq_mul] using this
  have hfeas : Feasible C m1 m2 K ((1 - t) • p + t • q) := by
    refine ⟨hpt, by rw [hm1eq]; exact hAt.le, ?_⟩
    rw [hm1eq]
    simp only [D] at hDt
    linarith
  have := hmin _ hfeas
  nlinarith

/-- Woodford (2003), p. 701: "`λ̃_i = μ₂ > 0` if (E.21) binds", made precise: under the
hypotheses of `envelope` (differentiable value function, Slater point) and of
`binds_of_unconstrained_infeasible` (no unconstrained minimiser is feasible), EVERY multiplier
pair satisfying (E.23) has `μ₂ > 0`. -/
theorem mu2_pos {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X} {L m1 m2 : X → ℝ}
    {K : ℝ} (hK : 0 ≤ K) (hL : ConvexOn ℝ C L) (hm1 : ConvexOn ℝ C m1)
    (hm1' : ConcaveOn ℝ C m1) (hm2 : ConvexOn ℝ C m2) {p p0 : X}
    (hopt : IsConstrOpt C L m1 m2 K p) (hpos : 0 < m1 p)
    (hno : ∀ q ∈ C, (∀ r ∈ C, L q ≤ L r) → ¬ Feasible C m1 m2 K q)
    (hp0 : p0 ∈ C) (h01 : m1 p < m1 p0) (h02 : m2 p0 < m2 p) {μ1 μ2 : ℝ} (hμ1 : 0 ≤ μ1)
    (hμ2 : 0 ≤ μ2)
    (hlag : ∀ q ∈ C, L p - μ1 * m1 p + μ2 * m2 p ≤ L q - μ1 * m1 q + μ2 * m2 q)
    {V' : ℝ × ℝ →L[ℝ] ℝ} (hV : HasFDerivAt (valueFn C L m1 m2) V' (m1 p, m2 p)) :
    0 < μ2 := by
  have hbind := binds_of_unconstrained_infeasible hL hm1 hm1' hm2 hopt hpos hno
  have henv := envelope hK hopt hbind hpos hp0 h01 h02 hμ1 hμ2 hlag hV
  rcases eq_or_lt_of_le hμ2 with h | h
  · exfalso
    rw [← h, mul_zero] at henv
    refine hno p hopt.1.1 (fun r hr => ?_) hopt.1
    have := hlag r hr
    rw [henv, ← h] at this
    simpa using this
  · exact h

/-- Woodford (2003), p. 701, the other half: if some unconstrained minimiser of `L` over `C` is
feasible, then the constrained optimum is itself an unconstrained minimiser, i.e. `λ̃_i = 0`
(`μ₁ = μ₂ = 0`) is a valid choice in (E.23). -/
theorem zero_multiplier_of_feasible_min {X : Type*} {C : Set X} {L m1 m2 : X → ℝ} {K : ℝ}
    {p : X} (hopt : IsConstrOpt C L m1 m2 K p)
    (hq : ∃ q ∈ C, (∀ r ∈ C, L q ≤ L r) ∧ Feasible C m1 m2 K q) :
    ∀ r ∈ C, L p - 0 * m1 p + 0 * m2 p ≤ L r - 0 * m1 r + 0 * m2 r := by
  obtain ⟨q, hqC, hqmin, hqf⟩ := hq
  intro r hr
  simp only [zero_mul, sub_zero, add_zero]
  exact le_trans (hopt.2 q hqf) (hqmin r hr)

/-- Woodford (2003), p. 701 (survey item (e)): "a binding constraint" can carry a zero
multiplier, so "`λ̃_i > 0` iff (E.21) binds" is false if "binds" only means equality. Here
`L = 0`, `m₁ = 1`, `m₂ = 2`, `K = 2`: (E.21) holds with equality, yet `μ = 0` satisfies
(E.23). -/
theorem binding_zero_multiplier_case :
    IsConstrOpt (Set.univ : Set ℝ) (fun _ => 0) (fun _ => 1) (fun _ => 2) 2 0 ∧
      (2 : ℝ) = 2 * 1 ^ 2 ∧
      ∀ r ∈ (Set.univ : Set ℝ), (0 : ℝ) - 0 * 1 + 0 * 2 ≤ 0 - 0 * 1 + 0 * 2 := by
  refine ⟨⟨⟨Set.mem_univ _, by norm_num, by norm_num⟩, fun _ _ => le_rfl⟩, by norm_num,
    fun _ _ => le_rfl⟩

/-! ### The target rate `i**` -/

/-- Woodford (2003), App. E.5, p. 703: `i** = K m̄₁ − ī > 0` given `m̄₁ ≥ ī > 0` and `K > 1`. -/
theorem iStarStar_pos {K m1 ib : ℝ} (hK : 1 < K) (hm : ib ≤ m1) (hib : 0 < ib) :
    0 < K * m1 - ib := by nlinarith

/-- Woodford (2003), Prop. 6.9 (survey error 22): `K > 1` is needed for `i** > 0`; at `K = 1`
and `m̄₁ = ī` one gets `i** = 0`. -/
theorem iStarStar_K_one {ib : ℝ} : (1 : ℝ) * ib - ib = 0 := by ring

/-- Woodford (2003), Prop. 6.9: with only `K ≥ 1` the conclusion weakens to `i** ≥ 0`. -/
theorem iStarStar_nonneg {K m1 ib : ℝ} (hK : 1 ≤ K) (hm : ib ≤ m1) (hib : 0 ≤ ib) :
    0 ≤ K * m1 - ib := by nlinarith

/-- Woodford (2003), App. E.5: a Slater point for the reformulated problem forces positive
interest-rate variability at the optimum: by Jensen `m₂ ≥ m₁²` for every policy, so
`m̄₂ > m̄₁²`. -/
theorem slater_needs_variance {m1p m2p m1q m2q : ℝ} (hm1p : 0 ≤ m1p) (hJ : m1q ^ 2 ≤ m2q)
    (h1 : m1p < m1q) (h2 : m2q < m2p) : m1p ^ 2 < m2p := by nlinarith

/-! ### The decomposition argument: (E.20) never binds -/

/-- Woodford (2003), App. E.5, p. 701 (survey item (a)), made precise. Policies are pairs
`(d, s)` of a deterministic component and a stabilisation component (independently
specifiable); the loss separates, `L = L_d(d) + L_s(s)`; the deterministic part fixes
`m₁ = M(d)`, and `m₂ − m₁² = v(s)` depends on the stabilisation part only. If `d*` is the
unique minimiser of `L_d` (every `d ∈ C_d` with `L_d(d) ≤ L_d(d*)` is `d*`) and
`K ≥ 1`, every constrained optimum has `m̄₁ ≥ M(d*)`. With `M(d*) ≥ ī > 0` (Chapter 7) this
gives `m̄₁ > 0`: (E.20) does not bind. -/
theorem det_component_mean {D T : Type*} {CD : Set D} {CT : Set T} {Ld : D → ℝ}
    {Ls : T → ℝ} {M : D → ℝ} {v : T → ℝ} {K : ℝ} (hK : 1 ≤ K) {dstar : D} (hds : dstar ∈ CD)
    (huniq : ∀ d ∈ CD, Ld d ≤ Ld dstar → d = dstar)
    {z : D × T}
    (hopt : IsConstrOpt (CD ×ˢ CT) (fun w => Ld w.1 + Ls w.2) (fun w => M w.1)
      (fun w => M w.1 ^ 2 + v w.2) K z) :
    M dstar ≤ M z.1 := by
  obtain ⟨⟨hz, hz1, hz2⟩, hopt⟩ := hopt
  by_contra hlt
  push Not at hlt
  have hsq : M z.1 ^ 2 ≤ M dstar ^ 2 := pow_le_pow_left₀ hz1 hlt.le 2
  have hfeas : Feasible (CD ×ˢ CT) (fun w => M w.1) (fun w => M w.1 ^ 2 + v w.2) K
      (dstar, z.2) := by
    refine ⟨⟨hds, hz.2⟩, le_trans hz1 hlt.le, ?_⟩
    simp only at hz2 ⊢
    nlinarith
  have h1 := hopt _ hfeas
  simp only at h1
  have := huniq z.1 hz.1 (by linarith)
  rw [this] at hlt
  exact lt_irrefl _ hlt

/-! ### Concrete moments: the interest path is linear in the policy -/

/-- Woodford (2003), (4.18): if the interest-rate path is a linear function of the policy and
bounded on `C`, the discounted mean `m₁ = Ê[i]` is affine (convex and concave) on `C`. -/
theorem dAvg_affine {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X} (hC : Convex ℝ C)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (intr : X →ₗ[ℝ] (ℕ → S → ℝ))
    (hb : ∀ p ∈ C, BoundedProc (intr p)) (ω0 : S) :
    ConvexOn ℝ C (fun p => dAvg 𝔼 β (intr p) ω0) ∧
      ConcaveOn ℝ C (fun p => dAvg 𝔼 β (intr p) ω0) := by
  have heq : ∀ x ∈ C, ∀ y ∈ C, ∀ a b : ℝ, dAvg 𝔼 β (intr (a • x + b • y)) ω0 =
      a * dAvg 𝔼 β (intr x) ω0 + b * dAvg 𝔼 β (intr y) ω0 := by
    intro x hx y hy a b
    have h := dAvg_lincomb 𝔼 hβ0 hβ1 (hb x hx) (hb y hy) a b 0 ω0
    rw [add_zero] at h
    rw [← h]
    congr 1
    funext t ω
    simp [map_add, map_smul, smul_eq_mul]
  refine ⟨⟨hC, fun x hx y hy a b _ _ _ => ?_⟩, ⟨hC, fun x hx y hy a b _ _ _ => ?_⟩⟩
  · simp only [smul_eq_mul]; rw [heq x hx y hy]
  · simp only [smul_eq_mul]; rw [heq x hx y hy]

/-- Woodford (2003), (4.19): under the same hypotheses the discounted second moment
`m₂ = Ê[i²]` is convex on `C`. -/
theorem dAvg_sq_convex {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X} (hC : Convex ℝ C)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (intr : X →ₗ[ℝ] (ℕ → S → ℝ))
    (hb : ∀ p ∈ C, BoundedProc (intr p)) (ω0 : S) :
    ConvexOn ℝ C (fun p => dAvg 𝔼 β (fun t ω => intr p t ω ^ 2) ω0) := by
  refine ⟨hC, fun x hx y hy a b ha hb' hab => ?_⟩
  have hbx := hb x hx
  have hby := hb y hy
  have hxy := hb _ (hC hx hy ha hb' hab)
  have hpt : ∀ t ω, intr (a • x + b • y) t ω ^ 2 ≤
      a * intr x t ω ^ 2 + b * intr y t ω ^ 2 + 0 := by
    intro t ω
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_zero]
    have hb2 : b = 1 - a := by linarith
    rw [hb2]
    nlinarith [sq_nonneg (intr x t ω - intr y t ω), mul_nonneg ha (by linarith : 0 ≤ 1 - a)]
  have sx : BoundedProc (fun t ω => intr x t ω ^ 2) := bdd_sq hbx
  have sy : BoundedProc (fun t ω => intr y t ω ^ 2) := bdd_sq hby
  have sxy : BoundedProc (fun t ω => intr (a • x + b • y) t ω ^ 2) := bdd_sq hxy
  have := dAvg_mono 𝔼 hβ0 hβ1 sxy (boundedProc_lincomb sx sy a b 0) hpt ω0
  rw [dAvg_lincomb 𝔼 hβ0 hβ1 sx sy, add_zero] at this
  simpa [smul_eq_mul] using this

/-! ### Proposition 6.9 assembled -/

/-- Woodford (2003), Proposition 6.9, eq. (4.21), p. 428 (proof App. E.5, pp. 701–703), in full.
Policies form a convex set `C` in a real vector space; the interest path `i = intr p` is linear
in the policy and bounded on `C`; `m₁ = Ê[i]`, `m₂ = Ê[i²]`; the loss `L` (4.20) is convex. Let
`p` minimise `L` subject to (4.18)–(4.19) with `K > 1`. Assume (E.20) is slack with
`m̄₁ ≥ ī > 0` (`det_component_mean`), a Slater point for the reformulated constraints, that no
unconstrained minimiser of `L` satisfies (4.18)–(4.19) ((4.19) "binds"), and that the value
function is differentiable at `(m̄₁, m̄₂)`. Then there are multipliers `μ₁ ≥ 0`, `λ̃_i = μ₂ > 0`
with `μ₁ = 2K m̄₁ μ₂` such that `p` minimises, with no constraints but `C`,
`L̃ = L + λ̃_i Ê[(î − i**)²]`, `î = i − ī`, and `i** = K m̄₁ − ī > 0`. -/
theorem prop_6_9 {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X} (hC : Convex ℝ C)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (intr : X →ₗ[ℝ] (ℕ → S → ℝ))
    (hb : ∀ p ∈ C, BoundedProc (intr p)) (ω0 : S) {L : X → ℝ} (hL : ConvexOn ℝ C L)
    {K ib : ℝ} (hK : 1 < K) (hib : 0 < ib) {p p0 : X}
    (hopt : IsConstrOpt C L (fun q => dAvg 𝔼 β (intr q) ω0)
      (fun q => dAvg 𝔼 β (fun t ω => intr q t ω ^ 2) ω0) K p)
    (hm1 : ib ≤ dAvg 𝔼 β (intr p) ω0) (hp0 : p0 ∈ C)
    (h01 : dAvg 𝔼 β (intr p) ω0 < dAvg 𝔼 β (intr p0) ω0)
    (h02 : dAvg 𝔼 β (fun t ω => intr p0 t ω ^ 2) ω0 <
      dAvg 𝔼 β (fun t ω => intr p t ω ^ 2) ω0)
    (hno : ∀ q ∈ C, (∀ r ∈ C, L q ≤ L r) → ¬ Feasible C (fun q => dAvg 𝔼 β (intr q) ω0)
      (fun q => dAvg 𝔼 β (fun t ω => intr q t ω ^ 2) ω0) K q)
    {V' : ℝ × ℝ →L[ℝ] ℝ}
    (hV : HasFDerivAt (valueFn C L (fun q => dAvg 𝔼 β (intr q) ω0)
      (fun q => dAvg 𝔼 β (fun t ω => intr q t ω ^ 2) ω0)) V'
      (dAvg 𝔼 β (intr p) ω0, dAvg 𝔼 β (fun t ω => intr p t ω ^ 2) ω0)) :
    ∃ μ1 μ2 : ℝ, 0 ≤ μ1 ∧ 0 < μ2 ∧ μ1 = 2 * K * dAvg 𝔼 β (intr p) ω0 * μ2 ∧
      0 < K * dAvg 𝔼 β (intr p) ω0 - ib ∧
      ∀ q ∈ C, L p + μ2 * dAvg 𝔼 β
          (fun t ω => (intr p t ω - ib - (K * dAvg 𝔼 β (intr p) ω0 - ib)) ^ 2) ω0 ≤
        L q + μ2 * dAvg 𝔼 β
          (fun t ω => (intr q t ω - ib - (K * dAvg 𝔼 β (intr p) ω0 - ib)) ^ 2) ω0 := by
  obtain ⟨hm1c, hm1c'⟩ := dAvg_affine 𝔼 hC hβ0 hβ1 intr hb ω0
  have hm2c := dAvg_sq_convex 𝔼 hC hβ0 hβ1 intr hb ω0
  have hK0 : 0 ≤ K := by linarith
  have hpos : 0 < dAvg 𝔼 β (intr p) ω0 := lt_of_lt_of_le hib hm1
  obtain ⟨μ1, μ2, hμ1, hμ2, hlag⟩ :=
    prop_6_9_multipliers hC hL hm1c' hm2c hK0 hopt hp0 h01 h02
  have hμ2pos := mu2_pos hK0 hL hm1c hm1c' hm2c hopt hpos hno hp0 h01 h02 hμ1 hμ2 hlag hV
  have hbind := binds_of_unconstrained_infeasible hL hm1c hm1c' hm2c hopt hpos hno
  have henv := envelope hK0 hopt hbind hpos hp0 h01 h02 hμ1 hμ2 hlag hV
  refine ⟨μ1, μ2, hμ1, hμ2pos, henv, iStarStar_pos hK hm1 hib, fun q hq => ?_⟩
  -- (E.25): complete the square, with `μ₁/(2μ₂) = K m̄₁`
  have hc : μ1 / (2 * μ2) = K * dAvg 𝔼 β (intr p) ω0 := by
    rw [henv]; field_simp
  have hsq : ∀ r ∈ C, μ2 * dAvg 𝔼 β
      (fun t ω => (intr r t ω - ib - (K * dAvg 𝔼 β (intr p) ω0 - ib)) ^ 2) ω0 =
      -μ1 * dAvg 𝔼 β (intr r) ω0 + μ2 * dAvg 𝔼 β (fun t ω => intr r t ω ^ 2) ω0 +
        μ1 ^ 2 / (4 * μ2) := by
    intro r hr
    rw [dAvg_complete_square 𝔼 hβ0 hβ1 (hb r hr) hμ2pos.ne', hc]
    have : (fun t ω => (intr r t ω - ib - (K * dAvg 𝔼 β (intr p) ω0 - ib)) ^ 2) =
        fun t ω => (intr r t ω - K * dAvg 𝔼 β (intr p) ω0) ^ 2 := by
      funext t ω; ring
    rw [this]
    ring
  rw [hsq p hopt.1.1, hsq q hq]
  have := hlag q hq
  linarith

/-- Woodford (2003), Prop. 6.9, the slack case: if some unconstrained minimiser of the loss
satisfies (4.18)–(4.19), the constrained optimum minimises `L` itself over `C` (`λ̃_i = 0`). -/
theorem prop_6_9_slack {X : Type*} {C : Set X} {L m1 m2 : X → ℝ} {K : ℝ} {p : X}
    (hopt : IsConstrOpt C L m1 m2 K p)
    (hq : ∃ q ∈ C, (∀ r ∈ C, L q ≤ L r) ∧ Feasible C m1 m2 K q) : ∀ r ∈ C, L p ≤ L r := by
  intro r hr
  have := zero_multiplier_of_feasible_min hopt hq r hr
  simpa using this

/-! ### Both considerations together: (4.22) -/

/-- Woodford (2003), eq. (4.22), p. 429: `λ_i(î − i*)² + μ₂(î − i**)² = λ̂_i(î − î_tgt)² + const`
with `λ̂_i = λ_i + μ₂` and `î_tgt = (λ_i i* + μ₂ i**)/(λ_i + μ₂)`. -/
theorem loss_4_22 {li μ2 iS iSS ih : ℝ} (h : li + μ2 ≠ 0) :
    li * (ih - iS) ^ 2 + μ2 * (ih - iSS) ^ 2 =
      (li + μ2) * (ih - (li * iS + μ2 * iSS) / (li + μ2)) ^ 2 +
        li * μ2 * (iSS - iS) ^ 2 / (li + μ2) := by
  field_simp
  ring

/-- Woodford (2003), p. 429: the combined target `î_tgt` is intermediate between `i*` and `i**`. -/
theorem iHat_between {li μ2 iS iSS : ℝ} (hli : 0 ≤ li) (hμ : 0 ≤ μ2) (hsum : 0 < li + μ2)
    (hle : iS ≤ iSS) :
    iS ≤ (li * iS + μ2 * iSS) / (li + μ2) ∧ (li * iS + μ2 * iSS) / (li + μ2) ≤ iSS := by
  constructor
  · rw [le_div_iff₀ hsum]; nlinarith
  · rw [div_le_iff₀ hsum]; nlinarith

/-- Woodford (2003), p. 429: "`î` ... may have either sign": with `i* = −1 < 0 < 1 = i**` the
target is `1/2` for `(λ_i, μ₂) = (1, 3)` and `−1/2` for `(3, 1)`. -/
theorem iHat_either_sign :
    ((1 : ℝ) * (-1) + 3 * 1) / (1 + 3) = 1 / 2 ∧ ((3 : ℝ) * (-1) + 1 * 1) / (3 + 1) = -1 / 2 := by
  constructor <;> norm_num

end Woodford.StabilizationWelfare.ZLB
