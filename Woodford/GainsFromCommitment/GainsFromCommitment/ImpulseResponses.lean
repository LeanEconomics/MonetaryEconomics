/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.ForwardSolution
import GainsFromCommitment.SecondOrderRE
import GainsFromCommitment.ExpectationsFiniteTree
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Long-run expectations and impulse responses under optimal commitment

Woodford (2003), *Interest and Prices*, Chapter 7, §2.1, pp. 492–501 (Propositions 7.9 and 7.10,
eqs. (2.16)–(2.17), p. 501 and footnote 22), and Appendix F, §§F.2–F.3, pp. 710–713.

The optimal plan under commitment in the cost-push model is described (pp. 488–491) by the
first-order conditions (1.7) `π_t = φ_{t−1} − φ_t`, (1.8) `x_t = x* + (κ/λ) φ_t` and the solved
multiplier recursion (2.7)
`φ_t = μ₁ φ_{t−1} − (1 − μ₁)(λ/κ) x* − β⁻¹ ∑_j μ₂^{−j−1} E_t u_{t+j}`, for some initial
multiplier `φ_{t₀−1}` (zero for the `t₀`-optimal plan, other values for the timelessly optimal
plans of Propositions 7.6–7.8). Those propositions are proved in another module; here (2.7),
(1.7) and (1.8) are restated as the model equations (`Plan`). Dates are shifted so that Lean
date `0` is the economic date `t₀ − 1` (the date of the initial multiplier) and Lean date
`n` is `t₀ − 1 + n`; the expectation `E_n` is conditional on Lean-date-`n` information.

## Main results

* Roots of `βμ² − (1 + β + c)μ + 1 = 0` (`RootPair`, `rootPair_exists`, `rootPair_unique`,
  `rootPair_identity`): `0 < μ₁ < 1 < μ₂`, `μ₁μ₂ = β⁻¹`, `β(1 − μ₁)(μ₂ − 1) = c`.
* The restated model is consistent: `plan_exists` (every initial multiplier generates a plan),
  `plan_AS` (every plan satisfies the AS relation (2.1)), `plan_phi_bounded`.
* **Proposition 7.9, corrected (survey error E7).** `tendsto_E_x_iff`: the long-run expected
  output gap exists and equals `X` iff `E_t u_T → −κX`; `tendsto_E_pi_iff`: the long-run expected
  inflation rate equals `P` iff `E_t u_{T+1} − E_t u_T → (κ²/λ)P`, so (`tendsto_E_pi_zero_iff`)
  it converges at all iff it converges to `0` iff `E_t u_{T+1} − E_t u_T → 0`. Hence
  (`prop_7_9_limits`, `prop_7_9_limits_iff`) `lim E_t π_T = lim E_t x_T = 0` at every date and
  state **iff** `E_t u_T → 0`: the added hypothesis is necessary and sufficient. The printed
  proposition fails for `u ≡ ū ≠ 0` (`counterexample_const`: `E_t x_T → −ū/κ`) and for
  `u_t = (−1)ᵗ ū` (`counterexample_alternating`: `E_t π_T` does not converge).
* **Impulse responses (2.16)–(2.17), corrected (E4, E5, E6).** `rev_phi` (the corrected
  recursion of F.2 solved), `rev_x` ((2.17) with the factor `κ/λ`), `rev_pi` ((2.16) with first
  sum over `I_t[u_{t+m+j}]`). The printed versions are false: `not_printed_217`,
  `not_printed_216` (coin-flip economy), `not_printed_F2_recursion` (perfect foresight).
* **Proposition 7.10, corrected.** `price_plus_phi_const` (F.8); `tendsto_E_p_iff_u`,
  `tendsto_E_p_iff`: the long-run expected price level exists iff `E_t u_T` converges;
  `prop_7_10`: under `E_t u_T → 0` it equals `p_{t₀−1} + φ_{t₀−1} + (λ/κ)x*` at every date
  and state; `prop_7_10_target`: under the constraint (2.13) it equals `p̄`;
  `counterexample_7_10` (no long-run price level for `u_t = (−1)ᵗ ū`).
* **Page 501 and footnote 22 (γ = 1).** `gamma_one_reduction`: with full indexation the optimal
  inflation path is the optimal price-level path of the `γ = 0` economy (up to a constant);
  `lagApply`, `price_law_opt_gamma0`, `price_law_opt_gamma1`, `price_law_disc_gamma0`,
  `price_law_disc_gamma1` with `rootMultiplicity` 0, 1, 1, 2 at `z = 1`: the price level is
  stationary under the optimal plan with `γ = 0`, `I(1)` under optimal policy with `γ = 1`
  and `I(2)` under discretion with `γ = 1`.
-/

namespace Woodford.GainsFromCommitment.ImpulseResponses

open Filter Topology
open SecondOrderRE (mu1 mu2 mu1_pos mu1_lt_one one_lt_mu2 mu1_add_mu2 mu1_mul_mu2)

/-! ### Roots of the characteristic equation (1.11) -/

/-- Woodford (2003), eq. (1.11), p. 472, and p. 506: `μ₁ < μ₂` are the roots of
`βμ² − (1 + β + c)μ + 1 = 0` with `0 < μ₁ < 1 < μ₂` (in §2.1 `c = κ²/λ`; in §2.2
`c = βλₓσ²/λᵢ`). -/
def RootPair (β c μ1 μ2 : ℝ) : Prop :=
  0 < μ1 ∧ μ1 < 1 ∧ 1 < μ2 ∧ μ1 + μ2 = (1 + β + c) / β ∧ μ1 * μ2 = β⁻¹

/-- Woodford (2003), eq. (1.11), p. 472: the factorisation
`βμ² − (1 + β + c)μ + 1 = β(μ − μ₁)(μ − μ₂)` of the characteristic polynomial. -/
theorem rootPair_factor {β c μ1 μ2 : ℝ} (hβ : 0 < β) (h : RootPair β c μ1 μ2) (μ : ℝ) :
    β * μ ^ 2 - (1 + β + c) * μ + 1 = β * (μ - μ1) * (μ - μ2) := by
  obtain ⟨-, -, -, hs, hp⟩ := h
  have hβ0 : β ≠ 0 := hβ.ne'
  have hs' : β * (μ1 + μ2) = 1 + β + c := by rw [hs]; field_simp
  have hp' : β * (μ1 * μ2) = 1 := by rw [hp]; field_simp
  linear_combination μ * hs' - hp'

/-- Woodford (2003), eq. (1.11), p. 472: `μ₁` is a root of the characteristic polynomial. -/
theorem rootPair_root_lo {β c μ1 μ2 : ℝ} (hβ : 0 < β) (h : RootPair β c μ1 μ2) :
    β * μ1 ^ 2 - (1 + β + c) * μ1 + 1 = 0 := by
  rw [rootPair_factor hβ h]; ring

/-- Woodford (2003), eq. (1.11), p. 472: `μ₂` is a root of the characteristic polynomial. -/
theorem rootPair_root_hi {β c μ1 μ2 : ℝ} (hβ : 0 < β) (h : RootPair β c μ1 μ2) :
    β * μ2 ^ 2 - (1 + β + c) * μ2 + 1 = 0 := by
  rw [rootPair_factor hβ h]; ring

/-- Woodford (2003), survey §1 (used repeatedly in Ch. 7): `β(1 − μ₁)(μ₂ − 1) = c`, i.e.
`β(1 − μ₁)(1 − μ₂) = −c`. -/
theorem rootPair_identity {β c μ1 μ2 : ℝ} (hβ : 0 < β) (h : RootPair β c μ1 μ2) :
    β * (1 - μ1) * (μ2 - 1) = c := by
  have := rootPair_factor hβ h 1
  linarith

/-- Woodford (2003), eq. (1.11), p. 472 ("two real roots `0 < μ₁ < 1 < μ₂`"): for `β > 0` and
`c > 0` the explicit roots form a `RootPair`. -/
theorem rootPair_exists {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    RootPair β c (mu1 β c) (mu2 β c) :=
  ⟨mu1_pos hβ hc, mu1_lt_one hβ hc, one_lt_mu2 hβ hc, mu1_add_mu2 hβ, mu1_mul_mu2 hβ hc⟩

/-- Woodford (2003), eq. (1.11), p. 472: the root pair is unique (so `μ₁`, `μ₂` are well
defined by `0 < μ₁ < 1 < μ₂`). -/
theorem rootPair_unique {β c a b a' b' : ℝ} (hβ : 0 < β) (h : RootPair β c a b)
    (h' : RootPair β c a' b') : a = a' ∧ b = b' := by
  have ha := rootPair_root_lo hβ h
  rw [rootPair_factor hβ h'] at ha
  have hab : a = a' := by
    rcases mul_eq_zero.mp ha with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hβ.ne'
      · linarith
    · linarith [h.2.1, h'.2.2.1]
  refine ⟨hab, ?_⟩
  have hp := h.2.2.2.2
  have hp' := h'.2.2.2.2
  rw [hab] at hp
  have ha0 : a' ≠ 0 := h'.1.ne'
  exact mul_left_cancel₀ ha0 (hp.trans hp'.symm)

/-- Woodford (2003), eq. (1.11), p. 472: for `β, c > 0` a pair is a `RootPair` exactly when it is
the pair of explicit roots `(μ₁, μ₂)` of the shared `SecondOrderRE` module. -/
theorem rootPair_iff {β c a b : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    RootPair β c a b ↔ a = mu1 β c ∧ b = mu2 β c := by
  constructor
  · exact fun h => rootPair_unique hβ h (rootPair_exists hβ hc)
  · rintro ⟨rfl, rfl⟩
    exact rootPair_exists hβ hc

/-! ### Stable recursions and geometric tails of sequences -/

/-- Woodford (2003), App. F, p. 711 ("because `|μ₁| < 1`, (2.7) implies (F.7)"): a stable
recursion `a_{k+1} = μ a_k + h_k`, `|μ| < 1`, driven by `h_k → 0`, converges to `0`. -/
theorem tendsto_rec_zero {μ : ℝ} (hμ : |μ| < 1) {a h : ℕ → ℝ}
    (hrec : ∀ k, a (k + 1) = μ * a k + h k) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 : 0 < 1 - |μ| := by linarith
  set δ := ε * (1 - |μ|) / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hh δ hδ0
  have hbound : ∀ n, |a (N + n)| ≤ |μ| ^ n * |a N| + ε / 2 := by
    intro n
    induction n with
    | zero => simp; linarith
    | succ n ih =>
      have hhn : |h (N + n)| < δ := by
        have := hN (N + n) (Nat.le_add_right N n)
        rwa [Real.dist_eq, sub_zero] at this
      rw [← add_assoc, hrec (N + n)]
      calc |μ * a (N + n) + h (N + n)| ≤ |μ| * |a (N + n)| + |h (N + n)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ |μ| * (|μ| ^ n * |a N| + ε / 2) + δ := by
            gcongr
        _ = |μ| ^ (n + 1) * |a N| + ε / 2 := by rw [hδ]; ring
  have hpow : Tendsto (fun n : ℕ => |μ| ^ n * |a N|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg μ) hμ).mul_const |a N|
  obtain ⟨N', hN'⟩ := Metric.tendsto_atTop.mp hpow (ε / 2) (by positivity)
  refine ⟨N + N', fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h2 := hN' (N' + n) (Nat.le_add_right N' n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h2
  have h3 := hbound (N' + n)
  rw [Real.dist_eq, sub_zero, add_assoc]
  linarith

/-- Woodford (2003), App. F, p. 711: a stable recursion `a_{k+1} = μ a_k + h_k`, `|μ| < 1`, with
`h_k → H` converges to `H/(1 − μ)`. -/
theorem tendsto_rec {μ H : ℝ} (hμ : |μ| < 1) {a h : ℕ → ℝ}
    (hrec : ∀ k, a (k + 1) = μ * a k + h k) (hh : Tendsto h atTop (𝓝 H)) :
    Tendsto a atTop (𝓝 (H / (1 - μ))) := by
  have h1 : 1 - μ ≠ 0 := by
    intro h0
    have : μ = 1 := by linarith
    rw [this, abs_one] at hμ
    exact lt_irrefl _ hμ
  have hz := tendsto_rec_zero hμ (a := fun k => a k - H / (1 - μ)) (h := fun k => h k - H)
    (fun k => by
      rw [hrec k]
      field_simp
      ring)
    (by simpa using hh.sub_const H)
  simpa using hz.add_const (H / (1 - μ))

/-- Woodford (2003), App. F, p. 711 (the converse step): if `a_{k+1} = μ a_k + h_k` and
`a_k → A` then `h_k → (1 − μ)A`. -/
theorem tendsto_forcing_of_rec {μ A : ℝ} {a h : ℕ → ℝ} (hrec : ∀ k, a (k + 1) = μ * a k + h k)
    (ha : Tendsto a atTop (𝓝 A)) : Tendsto h atTop (𝓝 ((1 - μ) * A)) := by
  have hs : Tendsto (fun k => a (k + 1)) atTop (𝓝 A) := (tendsto_add_atTop_iff_nat 1).mpr ha
  have := hs.sub (ha.const_mul μ)
  refine this.congr' (Eventually.of_forall fun k => ?_) |>.trans (le_of_eq ?_)
  · rw [hrec k]; ring
  · congr 1; ring

/-- Woodford (2003), eq. (2.7), p. 489: the geometric tail `G_k = ∑_j qʲ v_{k+j}` of a sequence
(the `∑_j μ₂^{−j} E_t u_{T+j}` of (2.7) at a fixed information date). -/
noncomputable def geomTail (q : ℝ) (v : ℕ → ℝ) (k : ℕ) : ℝ := ∑' j, q ^ j * v (k + j)

/-- Woodford (2003), eq. (2.7), p. 489: the geometric tail of a bounded sequence is summable. -/
theorem geomTail_summable {q M : ℝ} (hq : |q| < 1) {v : ℕ → ℝ} (hv : ∀ k, |v k| ≤ M) (k : ℕ) :
    Summable (fun j => q ^ j * v (k + j)) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right M)
    (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hv (k + j)) (pow_nonneg (abs_nonneg q) j))

/-- Woodford (2003), eq. (2.7), p. 489: `G_k = v_k + q G_{k+1}`. -/
theorem geomTail_succ {q M : ℝ} (hq : |q| < 1) {v : ℕ → ℝ} (hv : ∀ k, |v k| ≤ M) (k : ℕ) :
    geomTail q v k = v k + q * geomTail q v (k + 1) := by
  unfold geomTail
  rw [(geomTail_summable hq hv k).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, add_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show k + (j + 1) = k + 1 + j by ring, pow_succ]
  ring

/-- Woodford (2003), App. F, p. 711: if `v_k → V` (and `v` is bounded) then
`∑_j qʲ v_{k+j} → V/(1 − q)` (Tannery's theorem). -/
theorem tendsto_geomTail {q M V : ℝ} (hq : |q| < 1) {v : ℕ → ℝ} (hv : ∀ k, |v k| ≤ M)
    (hV : Tendsto v atTop (𝓝 V)) : Tendsto (geomTail q v) atTop (𝓝 (V / (1 - q))) := by
  have hsum : ∑' j : ℕ, q ^ j * V = V / (1 - q) := by
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hq]; ring
  rw [← hsum]
  refine tendsto_tsum_of_dominated_convergence (bound := fun j => |q| ^ j * M)
    ((summable_geometric_of_lt_one (abs_nonneg q) hq).mul_right M) (fun j => ?_)
    (Eventually.of_forall fun k j => ?_)
  · have : Tendsto (fun k => v (k + j)) atTop (𝓝 V) := (tendsto_add_atTop_iff_nat j).mpr hV
    simpa [add_comm] using this.const_mul (q ^ j)
  · rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hv (k + j)) (pow_nonneg (abs_nonneg q) j)

/-- Woodford (2003), App. F, p. 711 (converse): if `∑_j qʲ v_{k+j} → L` then
`v_k → (1 − q)L`. -/
theorem tendsto_of_tendsto_geomTail {q M L : ℝ} (hq : |q| < 1) {v : ℕ → ℝ}
    (hv : ∀ k, |v k| ≤ M) (hL : Tendsto (geomTail q v) atTop (𝓝 L)) :
    Tendsto v atTop (𝓝 ((1 - q) * L)) := by
  have hs : Tendsto (fun k => geomTail q v (k + 1)) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat 1).mpr hL
  have := hL.sub (hs.const_mul q)
  refine this.congr' (Eventually.of_forall fun k => ?_) |>.trans (le_of_eq ?_)
  · rw [geomTail_succ hq hv k]; ring
  · congr 1; ring

/-- Woodford (2003), App. F, p. 711: geometric tails commute with first differences,
`G_{k+1} − G_k = ∑_j qʲ (v_{k+1+j} − v_{k+j})`. -/
theorem geomTail_sub {q M : ℝ} (hq : |q| < 1) {v : ℕ → ℝ} (hv : ∀ k, |v k| ≤ M) (k : ℕ) :
    geomTail q v (k + 1) - geomTail q v k = geomTail q (fun n => v (n + 1) - v n) k := by
  unfold geomTail
  rw [← (geomTail_summable hq hv (k + 1)).tsum_sub (geomTail_summable hq hv k)]
  refine tsum_congr fun j => ?_
  rw [show k + 1 + j = k + j + 1 by ring]
  ring

/-- Woodford (2003), App. F, p. 711: a bounded sequence whose first differences converge has
first differences converging to `0` (so `E_t π_T` can only converge to `0`). -/
theorem diff_limit_zero {M d : ℝ} {v : ℕ → ℝ} (hv : ∀ k, |v k| ≤ M)
    (hd : Tendsto (fun k => v (k + 1) - v k) atTop (𝓝 d)) : d = 0 := by
  by_contra hd0
  -- reduce to `d > 0` by symmetry
  have key : ∀ (w : ℕ → ℝ) (e : ℝ), 0 < e → (∀ k, |w k| ≤ M) →
      Tendsto (fun k => w (k + 1) - w k) atTop (𝓝 e) → False := by
    intro w e he hw hwe
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hwe (e / 2) (by positivity)
    have hgrow : ∀ n, w N + n * (e / 2) ≤ w (N + n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h1 := hN (N + n) (Nat.le_add_right N n)
        rw [Real.dist_eq, abs_lt] at h1
        rw [← add_assoc]
        push_cast
        linarith [h1.1]
    obtain ⟨n, hn⟩ := exists_nat_gt (4 * M / e)
    have h1 := hgrow n
    have h2 := (abs_le.mp (hw N)).1
    have h3 := (abs_le.mp (hw (N + n))).2
    have h4 : 4 * M < n * e := by rwa [div_lt_iff₀ he] at hn
    nlinarith
  rcases lt_or_gt_of_ne hd0 with h | h
  · exact key (fun k => -v k) (-d) (by linarith) (fun k => by rw [abs_neg]; exact hv k)
      (hd.neg.congr fun k => by ring)
  · exact key v d h hv hd

/-! ### The optimal plan: (1.7), (1.8) and (2.7) restated as model equations -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), eqs. (1.7), (1.8), p. 472, and (2.7), p. 489 (the solved multiplier
recursion of the `t₀`-optimal and of every timelessly optimal plan, Props. 7.6–7.8): with Lean
date `0` the economic date `t₀ − 1`,
`π_{t} = φ_{t−1} − φ_{t}`, `x_t = x* + (κ/λ) φ_t` and
`φ_t = μ₁ φ_{t−1} − (1 − μ₁)(λ/κ)x* − β⁻¹ μ₂⁻¹ ∑_j μ₂^{−j} E_t u_{t+j}` for `t ≥ t₀`. -/
def Plan (β κ lam xs μ1 μ2 : ℝ) (u π x φ : ℕ → Ω → ℝ) : Prop :=
  (∀ t, π (t + 1) = φ t - φ (t + 1)) ∧
    (∀ t, x (t + 1) = (fun _ => xs) + (κ / lam) • φ (t + 1)) ∧
    ∀ t, φ (t + 1) = μ1 • φ t - (fun _ => (1 - μ1) * (lam / κ) * xs) -
      (β⁻¹ * μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ u (t + 1)

/-- Woodford (2003), eq. (2.7), p. 489 ("this equation can be solved recursively for the
evolution of `{φ_t}` starting from any initial condition"): the recursion
`φ_{t+1} = μ₁ φ_t − C − g_{t+1}` from `φ₀`. -/
def multPath (μ1 C : ℝ) (g : ℕ → Ω → ℝ) (φ0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => φ0
  | t + 1 => μ1 • multPath μ1 C g φ0 t - (fun _ => C) - g (t + 1)

/-- Woodford (2003), p. 489: every initial multiplier `φ_{t₀−1}` generates a plan
(the restated model equations are consistent). -/
theorem plan_exists (β κ lam xs μ1 μ2 : ℝ) (u : ℕ → Ω → ℝ) (φ0 : Ω → ℝ) :
    ∃ π x φ : ℕ → Ω → ℝ, φ 0 = φ0 ∧ Plan 𝔼 β κ lam xs μ1 μ2 u π x φ := by
  set φ := multPath μ1 ((1 - μ1) * (lam / κ) * xs)
    (fun t => (β⁻¹ * μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ u t) φ0 with hφ
  refine ⟨fun t => φ (t - 1) - φ t, fun t => (fun _ => xs) + (κ / lam) • φ t, φ, rfl,
    fun t => ?_, fun t => rfl, fun t => rfl⟩
  simp

/-- Woodford (2003), p. 489: along a plan the multipliers are adapted (`φ_t` is known at `t`). -/
theorem plan_phi_adapted {β κ lam xs μ1 μ2 M : ℝ} (hμ2 : 1 < μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hφ0 : 𝔼.E 0 (φ 0) = φ 0) : 𝔼.Adapted φ := by
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  have hSa := ForwardSolution.forwardSeries_adapted_abs 𝔼 hq hu
  intro t
  induction t with
  | zero => exact hφ0
  | succ t ih =>
    rw [hP.2.2 t, map_sub, map_sub, map_smul, map_smul, 𝔼.const, hSa (t + 1),
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih]

/-- Woodford (2003), p. 489 ("unique bounded solutions for the paths of inflation and the output
gap"): with `|μ₁| < 1`, `μ₂ > 1`, bounded `u` and bounded `φ_{t₀−1}`, the multipliers of a plan
are bounded. -/
theorem plan_phi_bounded {β κ lam xs μ1 μ2 M B : ℝ} (hμ1 : |μ1| < 1) (hμ2 : 1 < μ2)
    {u π x φ : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hφ0 : ∀ ω, |φ 0 ω| ≤ B) : BoundedProc φ := by
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  obtain ⟨MS, hMS⟩ := ForwardSolution.forwardSeries_bounded_abs 𝔼 hq hu
  set H := |(1 - μ1) * (lam / κ) * xs| + |β⁻¹ * μ2⁻¹| * MS with hH
  have hpos : 0 < 1 - |μ1| := by linarith
  set K := max B (H / (1 - |μ1|)) with hK
  have hHK : H ≤ (1 - |μ1|) * K := by
    have : H / (1 - |μ1|) ≤ K := le_max_right _ _
    rw [div_le_iff₀ hpos] at this
    linarith
  refine ⟨K, fun t ω => ?_⟩
  induction t with
  | zero => exact (hφ0 ω).trans (le_max_left _ _)
  | succ t ih =>
    rw [hP.2.2 t]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : |β⁻¹ * μ2⁻¹ * 𝔼.forwardSeries μ2⁻¹ u (t + 1) ω| ≤ |β⁻¹ * μ2⁻¹| * MS := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hMS _ _) (abs_nonneg _)
    calc |μ1 * φ t ω - (1 - μ1) * (lam / κ) * xs - β⁻¹ * μ2⁻¹ * 𝔼.forwardSeries μ2⁻¹ u (t + 1) ω|
        ≤ |μ1| * |φ t ω| + |(1 - μ1) * (lam / κ) * xs| +
            |β⁻¹ * μ2⁻¹ * 𝔼.forwardSeries μ2⁻¹ u (t + 1) ω| := by
          rw [← abs_mul]
          exact (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans (by linarith)
      _ ≤ |μ1| * K + H := by
          rw [hH]; nlinarith [mul_le_mul_of_nonneg_left ih (abs_nonneg μ1)]
      _ ≤ K := by linarith

/-- Woodford (2003), eqs. (2.1), (2.6), (2.7), pp. 486–489: every plan satisfies the
aggregate-supply relation (2.1), `π_t = κ x_t + β E_t π_{t+1} + u_t`, at every date `t ≥ t₀`,
when `μ₁ < μ₂` are the roots of (1.11) with `c = κ²/λ` (so the restated equations describe
rational-expectations equilibria). -/
theorem plan_AS {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hua : 𝔼.Adapted u) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (hφ0 : 𝔼.E 0 (φ 0) = φ 0)
    (t : ℕ) : π (t + 1) = κ • x (t + 1) + β • 𝔼.E (t + 1) (π (t + 2)) + u (t + 1) := by
  have hμ2 : 1 < μ2 := hr.2.2.1
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  have hφa := plan_phi_adapted 𝔼 hμ2 hu hP hφ0
  have hS := ForwardSolution.forwardSeries_solves_abs 𝔼 hq hu hua (t + 1)
  have hE2 : 𝔼.E (t + 1) (φ (t + 2)) = μ1 • φ (t + 1) -
      (fun _ => (1 - μ1) * (lam / κ) * xs) -
      (β⁻¹ * μ2⁻¹) • 𝔼.E (t + 1) (𝔼.forwardSeries μ2⁻¹ u (t + 1 + 1)) := by
    rw [hP.2.2 (t + 1), map_sub, map_sub, map_smul, map_smul, 𝔼.const, hφa (t + 1)]
  rw [hP.1 t, show t + 2 = t + 1 + 1 by ring, hP.1 (t + 1), hP.2.1 t, map_sub, hφa (t + 1),
    ← show t + 2 = t + 1 + 1 by ring, hE2]
  funext ω
  have h1 := congrFun (hP.2.2 t) ω
  have h2 := congrFun hS ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  have hμ20 : μ2 ≠ 0 := by linarith
  have hid := rootPair_identity hβ hr
  obtain ⟨-, -, -, hs, hp⟩ := hr
  set P := φ t ω
  set Q := φ (t + 1) ω
  set S1 := 𝔼.forwardSeries μ2⁻¹ u (t + 1) ω
  set ES := 𝔼.E (t + 1) (𝔼.forwardSeries μ2⁻¹ u (t + 1 + 1)) ω
  set U := u (t + 1) ω
  have e1 : β * (β⁻¹ * μ2⁻¹) * ES = S1 - U := by
    rw [h2]; field_simp; ring
  have e2 : P = β * μ2 * Q + β * μ2 * ((1 - μ1) * (lam / κ) * xs) + S1 := by
    have hp' : β * μ2 * μ1 = 1 := by rw [mul_assoc, mul_comm μ2, hp]; field_simp
    have hK1 : β * μ2 * (β⁻¹ * μ2⁻¹) = 1 := by field_simp
    linear_combination (-(β * μ2)) * h1 - P * hp' + S1 * hK1
  have e3 : β * μ2 * ((1 - μ1) * (lam / κ) * xs) - β * ((1 - μ1) * (lam / κ) * xs) =
      κ * xs := by
    have : β * (1 - μ1) * (μ2 - 1) * (lam / κ) * xs = κ * xs := by
      rw [hid]; field_simp
    linear_combination this
  have e4 : κ * (κ / lam) = β * (μ1 + μ2) - 1 - β := by
    rw [hs]; field_simp; ring
  linear_combination e2 - e1 - Q * e4 + e3

/-! ### Forecasts of the multiplier at a fixed information date -/

/-- Woodford (2003), App. F, p. 711: for `s ≤ T`, `E_s ∑_j qʲ E_T u_{T+j} = ∑_j qʲ E_s u_{T+j}`
(law of iterated expectations inside the forward sum). -/
theorem E_forwardSeries {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) {s T : ℕ} (hsT : s ≤ T) (ω : Ω) :
    𝔼.E s (𝔼.forwardSeries q u T) ω = ∑' j, q ^ j * 𝔼.E s (u (T + j)) ω := by
  have hb : ∀ k ω', |q ^ k * 𝔼.E T (u (T + k)) ω'| ≤ q ^ k * M := by
    intro k ω'
    rw [abs_mul, abs_pow, abs_of_nonneg hq0]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu (T + k)) T ω') (pow_nonneg hq0 k)
  change 𝔼.E s (fun ω' => ∑' k, q ^ k * 𝔼.E T (u (T + k)) ω') ω = _
  rw [𝔼.E_tsum hq0 hq1 hb s ω]
  refine tsum_congr fun k => ?_
  change 𝔼.E s (q ^ k • 𝔼.E T (u (T + k))) ω = _
  rw [map_smul, 𝔼.tower hsT, Pi.smul_apply, smul_eq_mul]

/-- Woodford (2003), App. F, p. 711: the date-`s` forecast of a plan's multiplier obeys
`E_s φ_{T+1} = μ₁ E_s φ_T − (1 − μ₁)(λ/κ)x* − β⁻¹μ₂⁻¹ ∑_j μ₂^{−j} E_s u_{T+1+j}`
for `s ≤ T + 1`. -/
theorem E_phi_succ {β κ lam xs μ1 μ2 M : ℝ} (hμ2 : 1 < μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) {s T : ℕ}
    (hsT : s ≤ T + 1) (ω : Ω) :
    𝔼.E s (φ (T + 1)) ω = μ1 * 𝔼.E s (φ T) ω - (1 - μ1) * (lam / κ) * xs -
      β⁻¹ * μ2⁻¹ * ∑' j, μ2⁻¹ ^ j * 𝔼.E s (u (T + 1 + j)) ω := by
  have hq0 : 0 ≤ μ2⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
  rw [hP.2.2 T, map_sub, map_sub, map_smul, map_smul, 𝔼.const]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [E_forwardSeries 𝔼 hq0 hq1 hu hsT ω]

/-- Woodford (2003), App. F, p. 711: in `k`-indexing from the information date `s`, the forecast
`a_k = E_s φ_{s+k}` obeys `a_{k+1} = μ₁ a_k − C − β⁻¹μ₂⁻¹ G_{k+1}` where
`G_k = ∑_j μ₂^{−j} v_{k+j}` and `v_k = E_s u_{s+k}`. -/
theorem E_phi_rec {β κ lam xs μ1 μ2 M : ℝ} (hμ2 : 1 < μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (s : ℕ) (ω : Ω)
    (k : ℕ) : 𝔼.E s (φ (k + 1 + s)) ω = μ1 * 𝔼.E s (φ (k + s)) ω +
      (-((1 - μ1) * (lam / κ) * xs) -
        β⁻¹ * μ2⁻¹ * geomTail μ2⁻¹ (fun n => 𝔼.E s (u (n + s)) ω) (k + 1)) := by
  rw [show k + 1 + s = k + s + 1 by ring, E_phi_succ 𝔼 hμ2 hu hP (by omega) ω]
  unfold geomTail
  have : ∀ j, 𝔼.E s (u (k + s + 1 + j)) ω = 𝔼.E s (u (k + 1 + j + s)) ω := fun j => by
    rw [show k + s + 1 + j = k + 1 + j + s by ring]
  simp only [this]
  ring

/-! ### Proposition 7.9, corrected: long-run expectations (survey error E7) -/

/-- Woodford (2003), App. F, p. 711, the algebra behind (F.7): with `β(1 − μ₁)(μ₂ − 1) = κ²/λ`,
`(−C − β⁻¹μ₂⁻¹ V/(1 − μ₂⁻¹))/(1 − μ₁) = (λ/κ)(−V/κ − x*)`. -/
theorem limit_algebra {β κ lam xs μ1 μ2 V : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) :
    (-((1 - μ1) * (lam / κ) * xs) - β⁻¹ * μ2⁻¹ * (V / (1 - μ2⁻¹))) / (1 - μ1) =
      lam / κ * (-V / κ - xs) := by
  have hid := rootPair_identity hβ hr
  have h1 : 1 - μ1 ≠ 0 := by linarith [hr.2.1]
  have h2 : μ2 - 1 ≠ 0 := by linarith [hr.2.2.1]
  have hμ2 : μ2 ≠ 0 := by linarith [hr.2.2.1]
  have h3 : 1 - μ2⁻¹ = (μ2 - 1) / μ2 := by field_simp
  rw [h3, div_eq_iff h1]
  field_simp
  have hid' : β * (1 - μ1) * (μ2 - 1) * lam = κ ^ 2 := by rw [hid]; field_simp
  linear_combination V * hid'

/-- Woodford (2003), Prop. 7.9 and (F.7), p. 711, made exact: along any plan, the long-run
date-`s` forecast of the multiplier equals `(λ/κ)(−V/κ − x*)` **iff** the long-run date-`s`
forecast of the cost-push shock equals `V`. -/
theorem tendsto_E_phi_iff {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (s : ℕ) (ω : Ω) (V : ℝ) :
    Tendsto (fun T => 𝔼.E s (φ T) ω) atTop (𝓝 (lam / κ * (-V / κ - xs))) ↔
      Tendsto (fun T => 𝔼.E s (u T) ω) atTop (𝓝 V) := by
  have hμ2 : 1 < μ2 := hr.2.2.1
  have hμ1 : |μ1| < 1 := by rw [abs_of_pos hr.1]; exact hr.2.1
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  set v : ℕ → ℝ := fun n => 𝔼.E s (u (n + s)) ω with hv
  have hvb : ∀ k, |v k| ≤ M := fun k => 𝔼.abs_E_le (hu (k + s)) s ω
  set a : ℕ → ℝ := fun k => 𝔼.E s (φ (k + s)) ω with ha
  have hrec : ∀ k, a (k + 1) = μ1 * a k + (-((1 - μ1) * (lam / κ) * xs) -
      β⁻¹ * μ2⁻¹ * geomTail μ2⁻¹ v (k + 1)) :=
    E_phi_rec 𝔼 hμ2 hu hP s ω
  rw [← tendsto_add_atTop_iff_nat s, ← tendsto_add_atTop_iff_nat s (f := fun T => 𝔼.E s (u T) ω)]
  change Tendsto a atTop _ ↔ Tendsto v atTop _
  have hK : β⁻¹ * μ2⁻¹ ≠ 0 := by
    have : 0 < β⁻¹ * μ2⁻¹ := mul_pos (inv_pos.mpr hβ) (inv_pos.mpr (by linarith))
    exact this.ne'
  have h1 : 1 - μ1 ≠ 0 := by linarith [hr.2.1]
  have hq1 : 1 - μ2⁻¹ ≠ 0 := by
    have : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
    linarith
  have hlim := limit_algebra (xs := xs) (V := V) hβ hκ hlam hr
  have hμ21 : μ2 - 1 ≠ 0 := by linarith
  constructor
  · intro hL
    have hh := tendsto_forcing_of_rec hrec hL
    have hG : Tendsto (fun k => geomTail μ2⁻¹ v (k + 1)) atTop
        (𝓝 ((-((1 - μ1) * (lam / κ) * xs) - (1 - μ1) * (lam / κ * (-V / κ - xs))) /
          (β⁻¹ * μ2⁻¹))) := by
      have := (hh.const_sub (-((1 - μ1) * (lam / κ) * xs))).div_const (β⁻¹ * μ2⁻¹)
      refine this.congr (fun k => ?_)
      field_simp
      ring
    have hG' := (tendsto_add_atTop_iff_nat 1).mp hG
    have := tendsto_of_tendsto_geomTail hq hvb hG'
    convert this using 2
    rw [div_eq_iff h1] at hlim
    rw [show -((1 - μ1) * (lam / κ) * xs) - (1 - μ1) * (lam / κ * (-V / κ - xs)) =
      β⁻¹ * μ2⁻¹ * (V / (1 - μ2⁻¹)) by linarith [hlim]]
    field_simp
  · intro hV
    have hG := tendsto_geomTail hq hvb hV
    have hG1 := (((tendsto_add_atTop_iff_nat 1).mpr hG).const_mul (β⁻¹ * μ2⁻¹)).const_sub
      (-((1 - μ1) * (lam / κ) * xs))
    have := tendsto_rec hμ1 hrec hG1
    rwa [hlim] at this

/-- **Proposition 7.9 (output gap), corrected.** Woodford (2003), Prop. 7.9, p. 492, and (F.7):
along any plan (any initial multiplier, so for the `t₀`-optimal plan and for every timelessly
optimal plan), the long-run date-`s` forecast of the output gap is `X` **iff** the long-run
date-`s` forecast of the cost-push shock is `−κX`. In particular `lim_T E_t x_T = 0` iff
`lim_T E_t u_T = 0` (the hypothesis missing from the book, survey error E7). -/
theorem tendsto_E_x_iff {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (s : ℕ) (ω : Ω) (X : ℝ) :
    Tendsto (fun T => 𝔼.E s (x T) ω) atTop (𝓝 X) ↔
      Tendsto (fun T => 𝔼.E s (u T) ω) atTop (𝓝 (-κ * X)) := by
  rw [← tendsto_E_phi_iff 𝔼 hβ hκ hlam hr hu hP s ω (-κ * X)]
  have hx : ∀ T, 𝔼.E s (x (T + 1)) ω = xs + κ / lam * 𝔼.E s (φ (T + 1)) ω := fun T => by
    rw [hP.2.1 T, map_add, map_smul, 𝔼.const]; rfl
  rw [← tendsto_add_atTop_iff_nat 1, ← tendsto_add_atTop_iff_nat 1 (f := fun T => 𝔼.E s (φ T) ω)]
  simp only [hx]
  have hc : κ / lam ≠ 0 := div_ne_zero hκ hlam
  have hval : lam / κ * (-(-κ * X) / κ - xs) = (X - xs) / (κ / lam) := by
    field_simp
  rw [hval]
  constructor
  · intro h
    have := (h.sub_const xs).div_const (κ / lam)
    refine this.congr fun T => ?_
    field_simp; ring
  · intro h
    have := (h.const_mul (κ / lam)).const_add xs
    convert this using 2
    field_simp; ring

/-- **Proposition 7.9 (inflation), corrected.** Woodford (2003), Prop. 7.9, p. 492, and (F.7):
along any plan the long-run date-`s` forecast of inflation is `P` **iff** the forecast changes
`E_s u_{T+1} − E_s u_T` converge to `(κ²/λ)P`. -/
theorem tendsto_E_pi_iff {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (s : ℕ) (ω : Ω) (P : ℝ) :
    Tendsto (fun T => 𝔼.E s (π T) ω) atTop (𝓝 P) ↔
      Tendsto (fun T => 𝔼.E s (u (T + 1)) ω - 𝔼.E s (u T) ω) atTop (𝓝 (κ ^ 2 / lam * P)) := by
  have hμ2 : 1 < μ2 := hr.2.2.1
  have hμ1 : |μ1| < 1 := by rw [abs_of_pos hr.1]; exact hr.2.1
  have hq : |μ2⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]; exact inv_lt_one_of_one_lt₀ hμ2
  have hid := rootPair_identity hβ hr
  set v : ℕ → ℝ := fun n => 𝔼.E s (u (n + s)) ω with hv
  have hvb : ∀ k, |v k| ≤ M := fun k => 𝔼.abs_E_le (hu (k + s)) s ω
  have hdvb : ∀ k, |v (k + 1) - v k| ≤ M + M := fun k =>
    (abs_sub _ _).trans (add_le_add (hvb _) (hvb _))
  set a : ℕ → ℝ := fun k => 𝔼.E s (φ (k + s)) ω with ha
  set C := (1 - μ1) * (lam / κ) * xs
  set K := β⁻¹ * μ2⁻¹ with hKdef
  have hrec : ∀ k, a (k + 1) = μ1 * a k + (-C - K * geomTail μ2⁻¹ v (k + 1)) :=
    E_phi_rec 𝔼 hμ2 hu hP s ω
  set b : ℕ → ℝ := fun k => a (k + 1) - a k with hb
  set D : ℕ → ℝ := geomTail μ2⁻¹ (fun n => v (n + 1) - v n) with hD
  have hbrec : ∀ k, b (k + 1) = μ1 * b k + (-K * D (k + 1)) := by
    intro k
    simp only [hb, hD]
    rw [← geomTail_sub hq hvb (k + 1), hrec (k + 1), hrec k]
    ring
  have hpi : ∀ k, 𝔼.E s (π (k + (s + 1))) ω = -b k := by
    intro k
    rw [show k + (s + 1) = k + s + 1 by ring, hP.1 (k + s), map_sub]
    simp only [hb, ha, Pi.sub_apply]
    rw [show k + 1 + s = k + s + 1 by ring]
    ring
  rw [← tendsto_add_atTop_iff_nat (s + 1), ← tendsto_add_atTop_iff_nat s
    (f := fun T => 𝔼.E s (u (T + 1)) ω - 𝔼.E s (u T) ω)]
  simp only [hpi]
  have hfun : (fun n => 𝔼.E s (u (n + s + 1)) ω - 𝔼.E s (u (n + s)) ω) =
      fun k => v (k + 1) - v k := by
    funext k
    simp only [hv]
    rw [show k + 1 + s = k + s + 1 by ring]
  rw [hfun]
  have hK : K ≠ 0 := by
    have : 0 < K := mul_pos (inv_pos.mpr hβ) (inv_pos.mpr (by linarith))
    exact this.ne'
  have h1 : 1 - μ1 ≠ 0 := by linarith [hr.2.1]
  have hq1 : 1 - μ2⁻¹ ≠ 0 := by
    have : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
    linarith
  have hμ20 : μ2 ≠ 0 := by linarith
  have hμ21 : μ2 - 1 ≠ 0 := by linarith
  have hid' : β * (1 - μ1) * (μ2 - 1) * lam = κ ^ 2 := by rw [hid]; field_simp
  constructor
  · intro hL
    have hbL : Tendsto b atTop (𝓝 (-P)) := by simpa using hL.neg
    have hh := tendsto_forcing_of_rec hbrec hbL
    have hD1 : Tendsto (fun k => D (k + 1)) atTop (𝓝 ((1 - μ1) * P / K)) := by
      have := hh.neg.div_const K
      refine this.congr (fun k => ?_) |>.trans (le_of_eq ?_)
      · field_simp
      · congr 1; ring
    have := tendsto_of_tendsto_geomTail hq hdvb ((tendsto_add_atTop_iff_nat 1).mp hD1)
    convert this using 2
    rw [hKdef]
    field_simp
    linear_combination (-P) * hid'
  · intro hV
    have hG := tendsto_geomTail hq hdvb hV
    have hG1 : Tendsto (fun k => -K * D (k + 1)) atTop
        (𝓝 (-K * (κ ^ 2 / lam * P / (1 - μ2⁻¹)))) :=
      ((tendsto_add_atTop_iff_nat 1).mpr hG).const_mul (-K)
    have := tendsto_rec hμ1 hbrec hG1
    have hval : -K * (κ ^ 2 / lam * P / (1 - μ2⁻¹)) / (1 - μ1) = -P := by
      rw [div_eq_iff h1, hKdef]
      field_simp
      linear_combination P * hid'
    rw [hval] at this
    simpa using this.neg

/-- Woodford (2003), Prop. 7.9, p. 492: with bounded `u`, the long-run forecast of inflation can
only converge to `0`, and it does so iff `E_s u_{T+1} − E_s u_T → 0`. -/
theorem tendsto_E_pi_zero_iff {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0)
    (hlam : lam ≠ 0) (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (s : ℕ) (ω : Ω) :
    ((∃ P, Tendsto (fun T => 𝔼.E s (π T) ω) atTop (𝓝 P)) ↔
        Tendsto (fun T => 𝔼.E s (π T) ω) atTop (𝓝 0)) ∧
      (Tendsto (fun T => 𝔼.E s (π T) ω) atTop (𝓝 0) ↔
        Tendsto (fun T => 𝔼.E s (u (T + 1)) ω - 𝔼.E s (u T) ω) atTop (𝓝 0)) := by
  have h0 := tendsto_E_pi_iff 𝔼 hβ hκ hlam hr hu hP s ω 0
  rw [mul_zero] at h0
  refine ⟨⟨fun ⟨P, hP'⟩ => ?_, fun h => ⟨0, h⟩⟩, h0⟩
  have hd := (tendsto_E_pi_iff 𝔼 hβ hκ hlam hr hu hP s ω P).mp hP'
  have hz := diff_limit_zero (fun k => 𝔼.abs_E_le (hu k) s ω) hd
  have hc : κ ^ 2 / lam ≠ 0 := div_ne_zero (pow_ne_zero 2 hκ) hlam
  have : P = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hc
    · exact h
  rw [this] at hP'
  exact hP'

/-- **Proposition 7.9 (long-run limits), corrected.** Woodford (2003), Prop. 7.9, p. 492, and
App. F.2, (F.7), p. 711: if the cost-push forecasts die out, `lim_T E_t u_T = 0` at every date
and state (the hypothesis missing from the book, E7), then under any plan (the `t₀`-optimal one
and every timelessly optimal one) `lim_T E_t π_T = 0` and `lim_T E_t x_T = 0` at every date. -/
theorem prop_7_9_limits {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hdecay : ∀ s ω, Tendsto (fun T => 𝔼.E s (u T) ω) atTop (𝓝 0)) (s : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E s (π T) ω) atTop (𝓝 0) ∧
      Tendsto (fun T => 𝔼.E s (x T) ω) atTop (𝓝 0) := by
  refine ⟨(tendsto_E_pi_zero_iff 𝔼 hβ hκ hlam hr hu hP s ω).2.mpr ?_,
    (tendsto_E_x_iff 𝔼 hβ hκ hlam hr hu hP s ω 0).mpr (by simpa using hdecay s ω)⟩
  have h1 := (tendsto_add_atTop_iff_nat 1).mpr (hdecay s ω)
  simpa using h1.sub (hdecay s ω)

/-- Woodford (2003), Prop. 7.9, p. 492: the added hypothesis is also **necessary**: the long-run
limits `lim E_t π_T = lim E_t x_T = 0` hold at every date and state iff `E_t u_T → 0` at every
date and state. -/
theorem prop_7_9_limits_iff {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0)
    (hlam : lam ≠ 0) (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) :
    (∀ s ω, Tendsto (fun T => 𝔼.E s (π T) ω) atTop (𝓝 0) ∧
        Tendsto (fun T => 𝔼.E s (x T) ω) atTop (𝓝 0)) ↔
      ∀ s ω, Tendsto (fun T => 𝔼.E s (u T) ω) atTop (𝓝 0) := by
  refine ⟨fun h s ω => ?_, fun h s ω => prop_7_9_limits 𝔼 hβ hκ hlam hr hu hP h s ω⟩
  have := (tendsto_E_x_iff 𝔼 hβ hκ hlam hr hu hP s ω 0).mp (h s ω).2
  simpa using this

/-- Woodford (2003), Prop. 7.9, p. 492 (survey error E7, first counterexample): under perfect
foresight with a constant cost-push shock `u ≡ ū`, every plan has `E_t π_T → 0` but
`E_t x_T → −ū/κ`, so `lim E_t x_T ≠ 0` when `ū ≠ 0` (and plans exist, `plan_exists`). -/
theorem counterexample_const {β κ lam xs μ1 μ2 ub : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0)
    (hlam : lam ≠ 0) (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) (hub : ub ≠ 0)
    {π x φ : ℕ → Unit → ℝ}
    (hP : Plan perfectForesight β κ lam xs μ1 μ2 (fun _ _ => ub) π x φ) (s : ℕ) (ω : Unit) :
    Tendsto (fun T => perfectForesight.E s (π T) ω) atTop (𝓝 0) ∧
      Tendsto (fun T => perfectForesight.E s (x T) ω) atTop (𝓝 (-ub / κ)) ∧
      ¬ Tendsto (fun T => perfectForesight.E s (x T) ω) atTop (𝓝 0) := by
  have hu : ∀ t (ω : Unit), |(fun _ _ => ub : ℕ → Unit → ℝ) t ω| ≤ |ub| := fun _ _ => le_rfl
  have hconst : Tendsto (fun T => perfectForesight.E s ((fun _ _ => ub : ℕ → Unit → ℝ) T) ω)
      atTop (𝓝 ub) := tendsto_const_nhds
  have hx := (tendsto_E_x_iff perfectForesight hβ hκ hlam hr hu hP s ω (-ub / κ)).mpr
    (by convert hconst using 2; field_simp)
  refine ⟨(tendsto_E_pi_zero_iff perfectForesight hβ hκ hlam hr hu hP s ω).2.mpr
    (by simp), hx, fun h0 => ?_⟩
  have := tendsto_nhds_unique hx h0
  have : ub = 0 := by
    field_simp at this
    linarith
  exact hub this

/-- Woodford (2003), Prop. 7.9, p. 492 (survey error E7, second counterexample): under perfect
foresight with the bounded alternating shock `u_t = (−1)ᵗ ū`, `ū ≠ 0`, no plan has a long-run
expected inflation rate: `E_t π_T` does not converge (nor does `E_t x_T`). -/
theorem counterexample_alternating {β κ lam xs μ1 μ2 ub : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0)
    (hlam : lam ≠ 0) (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) (hub : ub ≠ 0)
    {π x φ : ℕ → Unit → ℝ}
    (hP : Plan perfectForesight β κ lam xs μ1 μ2 (fun t _ => (-1) ^ t * ub) π x φ) (s : ℕ)
    (ω : Unit) :
    (¬ ∃ P, Tendsto (fun T => perfectForesight.E s (π T) ω) atTop (𝓝 P)) ∧
      ¬ ∃ X, Tendsto (fun T => perfectForesight.E s (x T) ω) atTop (𝓝 X) := by
  have hu : ∀ t (ω : Unit), |(fun t _ => (-1) ^ t * ub : ℕ → Unit → ℝ) t ω| ≤ |ub| :=
    fun t _ => by simp [abs_mul]
  have hosc : ∀ L : ℝ, ¬ Tendsto (fun T : ℕ => (-1 : ℝ) ^ T * ub) atTop (𝓝 L) := by
    intro L hL
    have h2 := ((tendsto_add_atTop_iff_nat 1).mpr hL).add hL
    have hz : Tendsto (fun T : ℕ => (-1 : ℝ) ^ (T + 1) * ub + (-1) ^ T * ub) atTop (𝓝 0) :=
      tendsto_const_nhds.congr fun T => by ring
    have hL0 : L = 0 := by
      have := tendsto_nhds_unique h2 hz; linarith
    rw [hL0] at hL
    have habs := hL.abs
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_zero] at habs
    exact hub (abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds habs))
  refine ⟨fun ⟨P, hP'⟩ => ?_, fun ⟨X, hX⟩ => ?_⟩
  · have h0 := (tendsto_E_pi_zero_iff perfectForesight hβ hκ hlam hr hu hP s ω).1.mp ⟨P, hP'⟩
    have hd := (tendsto_E_pi_zero_iff perfectForesight hβ hκ hlam hr hu hP s ω).2.mp h0
    have : Tendsto (fun T : ℕ => (-1 : ℝ) ^ T * ((-2) * ub)) atTop (𝓝 0) :=
      hd.congr fun T => by
        change (-1 : ℝ) ^ (T + 1) * ub - (-1) ^ T * ub = _
        ring
    exact hosc 0 (by simpa using this.div_const (-2) |>.congr fun T => by field_simp)
  · exact hosc _ ((tendsto_E_x_iff perfectForesight hβ hκ hlam hr hu hP s ω X).mp hX)

/-! ### Impulse responses (2.16)–(2.17), corrected (survey errors E4, E5, E6) -/

/-- Woodford (2003), p. 492: the forecast revision `I_t[y] = E_t y − E_{t−1} y`, here at date
`t = s + 1`. -/
def rev (s : ℕ) (y : Ω → ℝ) : Ω → ℝ := 𝔼.E (s + 1) y - 𝔼.E s y

/-- Woodford (2003), eqs. (2.16)–(2.17), p. 492: the sum `∑_j μ₂^{−j−1} I_{s+1}[u_{n+j}]` of
revisions of cost-push forecasts. -/
noncomputable def revSum (μ2 : ℝ) (u : ℕ → Ω → ℝ) (s n : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, μ2⁻¹ ^ (j + 1) * rev 𝔼 s (u (n + j)) ω

/-- Woodford (2003), App. F, p. 711: for `n ≥ s + 1` the revision of a forward sum is the forward
sum of revisions, `I_{s+1}[∑_j qʲ E_n u_{n+j}] = ∑_j qʲ I_{s+1}[u_{n+j}]`. -/
theorem rev_forwardSeries {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) {s n : ℕ} (hsn : s + 1 ≤ n) (ω : Ω) :
    rev 𝔼 s (𝔼.forwardSeries q u n) ω = ∑' j, q ^ j * rev 𝔼 s (u (n + j)) ω := by
  have hsum : ∀ r, Summable (fun j => q ^ j * 𝔼.E r (u (n + j)) ω) := fun r =>
    Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right M) (fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hu _) _ ω) (pow_nonneg hq0 j))
  unfold rev
  rw [Pi.sub_apply, E_forwardSeries 𝔼 hq0 hq1 hu hsn ω,
    E_forwardSeries 𝔼 hq0 hq1 hu (by omega) ω, ← (hsum (s + 1)).tsum_sub (hsum s)]
  refine tsum_congr fun j => ?_
  rw [Pi.sub_apply]
  ring

/-- Woodford (2003), App. F, p. 711, the recursion for forecast revisions with the misprint
`E_t → I_t` corrected (survey error E6):
`I_{s+1}[φ_{n+1}] = μ₁ I_{s+1}[φ_n] − β⁻¹ ∑_j μ₂^{−j−1} I_{s+1}[u_{n+1+j}]` for `n ≥ s`. -/
theorem rev_phi_succ {β κ lam xs μ1 μ2 M : ℝ} (hμ2 : 1 < μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) {s n : ℕ} (hsn : s ≤ n)
    (ω : Ω) :
    rev 𝔼 s (φ (n + 1)) ω = μ1 * rev 𝔼 s (φ n) ω - β⁻¹ * revSum 𝔼 μ2 u s (n + 1) ω := by
  have hq0 : 0 ≤ μ2⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
  have hS := rev_forwardSeries 𝔼 hq0 hq1 hu (s := s) (n := n + 1) (by omega) ω
  have hR : revSum 𝔼 μ2 u s (n + 1) ω =
      μ2⁻¹ * ∑' j, μ2⁻¹ ^ j * rev 𝔼 s (u (n + 1 + j)) ω := by
    unfold revSum
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    ring
  have hlin : rev 𝔼 s (φ (n + 1)) ω = μ1 * rev 𝔼 s (φ n) ω -
      β⁻¹ * μ2⁻¹ * rev 𝔼 s (𝔼.forwardSeries μ2⁻¹ u (n + 1)) ω := by
    unfold rev
    rw [hP.2.2 n]
    simp only [map_sub, map_smul, 𝔼.const, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hlin, hS, hR]
  ring

/-- Woodford (2003), App. F, p. 711: `I_{s+1}[φ_s] = 0` (the multiplier is predetermined
relative to the date-`s+1` news). -/
theorem rev_phi_self {β κ lam xs μ1 μ2 M : ℝ} (hμ2 : 1 < μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hφ0 : 𝔼.E 0 (φ 0) = φ 0) (s : ℕ) : rev 𝔼 s (φ s) = 0 := by
  have hφa := plan_phi_adapted 𝔼 hμ2 hu hP hφ0
  unfold rev
  rw [ForwardSolution.E_of_known 𝔼 (Nat.le_succ s) (hφa s), hφa s, sub_self]

/-- **Forecast revisions of the multiplier** (Woodford (2003), App. F, p. 711, with E6
corrected): `I_{s+1}[φ_{s+1+m}] = −β⁻¹ ∑_{k=0}^m μ₁ᵏ ∑_j μ₂^{−j−1} I_{s+1}[u_{s+1+m−k+j}]`. -/
theorem rev_phi {β κ lam xs μ1 μ2 M : ℝ} (hμ2 : 1 < μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hφ0 : 𝔼.E 0 (φ 0) = φ 0) (s : ℕ) (ω : Ω) (m : ℕ) :
    rev 𝔼 s (φ (s + 1 + m)) ω =
      -β⁻¹ * ∑ k ∈ Finset.range (m + 1), μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m - k) ω := by
  induction m with
  | zero =>
    rw [add_zero, rev_phi_succ 𝔼 hμ2 hu hP le_rfl ω, rev_phi_self 𝔼 hμ2 hu hP hφ0 s]
    simp
  | succ m ih =>
    rw [show s + 1 + (m + 1) = s + 1 + m + 1 by ring,
      rev_phi_succ 𝔼 hμ2 hu hP (by omega) ω, ih,
      Finset.sum_range_succ' (fun k => μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m + 1 - k) ω) (m + 1)]
    have h : ∀ k ∈ Finset.range (m + 1),
        μ1 ^ (k + 1) * revSum 𝔼 μ2 u s (s + 1 + m + 1 - (k + 1)) ω =
          μ1 * (μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m - k) ω) := fun k _ => by
      rw [show s + 1 + m + 1 - (k + 1) = s + 1 + m - k by omega]
      ring
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.sub_zero]
    ring

/-- **Equation (2.17), corrected** (Woodford (2003), p. 493 and (F.6), p. 711; survey error E5,
the factor `κ/λ` is missing in the book): the impulse response of the output gap is
`I_t[x_{t+m}] = −(κ/λ) β⁻¹ ∑_{k=0}^m ∑_j μ₁ᵏ μ₂^{−j−1} I_t[u_{t+m−k+j}]`, `t = s + 1`. -/
theorem rev_x {β κ lam xs μ1 μ2 M : ℝ} (hμ2 : 1 < μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hφ0 : 𝔼.E 0 (φ 0) = φ 0) (s : ℕ) (ω : Ω) (m : ℕ) :
    rev 𝔼 s (x (s + 1 + m)) ω =
      -(κ / lam) * β⁻¹ *
        ∑ k ∈ Finset.range (m + 1), μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m - k) ω := by
  have h := hP.2.1 (s + m)
  rw [show s + m + 1 = s + 1 + m by ring] at h
  have hφ := rev_phi 𝔼 hμ2 hu hP hφ0 s ω m
  unfold rev at hφ ⊢
  rw [h]
  simp only [map_add, map_smul, 𝔼.const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at hφ ⊢
  linear_combination (κ / lam) * hφ

/-- **Equation (2.16), corrected** (Woodford (2003), p. 492 and (F.5), p. 711; survey error E4,
the first sum must run over `I_t[u_{t+m+j}]`): the impulse response of inflation is
`I_t[π_{t+m}] = β⁻¹ ∑_j μ₂^{−j−1} I_t[u_{t+m+j}]
  − β⁻¹(1 − μ₁) ∑_{k=1}^m ∑_j μ₁^{k−1} μ₂^{−j−1} I_t[u_{t+m−k+j}]`, `t = s + 1`. -/
theorem rev_pi {β κ lam xs μ1 μ2 M : ℝ} (hμ2 : 1 < μ2) {u π x φ : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hφ0 : 𝔼.E 0 (φ 0) = φ 0) (s : ℕ) (ω : Ω) (m : ℕ) :
    rev 𝔼 s (π (s + 1 + m)) ω = β⁻¹ * revSum 𝔼 μ2 u s (s + 1 + m) ω -
      β⁻¹ * (1 - μ1) *
        ∑ k ∈ Finset.range m, μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m - (k + 1)) ω := by
  have hπ : π (s + 1 + m) = φ (s + m) - φ (s + 1 + m) := by
    rw [show s + 1 + m = s + m + 1 by ring]; exact hP.1 (s + m)
  have hr : rev 𝔼 s (π (s + 1 + m)) ω = rev 𝔼 s (φ (s + m)) ω - rev 𝔼 s (φ (s + 1 + m)) ω := by
    rw [hπ]; unfold rev; simp only [map_sub, Pi.sub_apply]; ring
  rw [hr, rev_phi 𝔼 hμ2 hu hP hφ0 s ω m]
  cases m with
  | zero =>
    rw [add_zero, rev_phi_self 𝔼 hμ2 hu hP hφ0 s]
    simp
  | succ m =>
    rw [show s + (m + 1) = s + 1 + m by ring, rev_phi 𝔼 hμ2 hu hP hφ0 s ω m,
      Finset.sum_range_succ' (fun k => μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + (m + 1) - k) ω)
        (m + 1)]
    have h1 : ∀ k ∈ Finset.range (m + 1),
        μ1 ^ (k + 1) * revSum 𝔼 μ2 u s (s + 1 + (m + 1) - (k + 1)) ω =
          μ1 * (μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m - k) ω) := fun k _ => by
      rw [show s + 1 + (m + 1) - (k + 1) = s + 1 + m - k by omega]
      ring
    have h2 : ∀ k ∈ Finset.range (m + 1),
        μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + (m + 1) - (k + 1)) ω =
          μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m - k) ω := fun k _ => by
      rw [show s + 1 + (m + 1) - (k + 1) = s + 1 + m - k by omega]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.sub_zero]
    ring

/-- Woodford (2003), eq. (2.17), p. 493, as printed (without the factor `κ/λ`). -/
def Printed217 (β μ1 μ2 : ℝ) (u x : ℕ → Ω → ℝ) : Prop :=
  ∀ s m ω, rev 𝔼 s (x (s + 1 + m)) ω =
    -β⁻¹ * ∑ k ∈ Finset.range (m + 1), μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m - k) ω

/-- Woodford (2003), eq. (2.16), p. 492, as printed (first sum over `I_t[u_{t+j}]`). -/
def Printed216 (β μ1 μ2 : ℝ) (u π : ℕ → Ω → ℝ) : Prop :=
  ∀ s m ω, rev 𝔼 s (π (s + 1 + m)) ω = β⁻¹ * revSum 𝔼 μ2 u s (s + 1) ω -
    β⁻¹ * (1 - μ1) * ∑ k ∈ Finset.range m, μ1 ^ k * revSum 𝔼 μ2 u s (s + 1 + m - (k + 1)) ω

/-- Woodford (2003), App. F, p. 711, the recursion for `I_t[φ_{t+m}]` as printed, with
`E_t[u_{t+m+j}]` in place of `I_t[u_{t+m+j}]`. -/
def PrintedF2Rec (β μ1 μ2 : ℝ) (u φ : ℕ → Ω → ℝ) : Prop :=
  ∀ s m ω, rev 𝔼 s (φ (s + 1 + m)) ω = μ1 * rev 𝔼 s (φ (s + m)) ω -
    β⁻¹ * ∑' j, μ2⁻¹ ^ (j + 1) * 𝔼.E (s + 1) (u (s + 1 + m + j)) ω

/-- Woodford (2003), p. 63-style coin-flip economy (from `ExpectationsFiniteTree`): the mean-zero
shock `ε_t` (`±1` at dates 1 and 2) is bounded by `1`. -/
theorem coinShock_bdd (t : ℕ) (ω : Bool × Bool) : |ExpectationsFiniteTree.coinShock t ω| ≤ 1 := by
  unfold ExpectationsFiniteTree.coinShock
  split_ifs <;> simp

/-- Woodford (2003), App. F (coin-flip economy): the shock is adapted. -/
theorem coinShock_adapted :
    ExpectationsFiniteTree.coinSystem.Adapted ExpectationsFiniteTree.coinShock := by
  intro t
  funext ω
  exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
    ExpectationsFiniteTree.coinShock_measurable t h

/-- Woodford (2003), App. F (coin-flip economy): the date-1 news is the first flip,
`I_1[ε_1] = ε_1`. -/
theorem coin_rev_one :
    rev ExpectationsFiniteTree.coinSystem 0 (ExpectationsFiniteTree.coinShock 1) =
      ExpectationsFiniteTree.coinShock 1 := by
  unfold rev
  rw [coinShock_adapted 1, ExpectationsFiniteTree.coinShock_mean_zero 0, sub_zero]

/-- Woodford (2003), App. F (coin-flip economy): the date-1 news says nothing about later
shocks, `I_1[ε_n] = 0` for `n ≥ 2`. -/
theorem coin_rev_ge_two {n : ℕ} (hn : 2 ≤ n) :
    rev ExpectationsFiniteTree.coinSystem 0 (ExpectationsFiniteTree.coinShock n) = 0 := by
  unfold rev
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h
    have h1 := ExpectationsFiniteTree.coinShock_mean_zero 1
    rw [← ExpectationsFiniteTree.coinSystem.tower (Nat.zero_le 1), h1, map_zero, sub_zero]
  · have h0 : ExpectationsFiniteTree.coinShock n = 0 := by
      funext ω
      simp only [ExpectationsFiniteTree.coinShock, Pi.zero_apply]
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, ↓reduceIte]
    rw [h0, map_zero, map_zero, sub_zero]

/-- Woodford (2003), App. F (coin-flip economy): `∑_j μ₂^{−j−1} I_1[ε_{1+j}] = μ₂⁻¹ ε_1`. -/
theorem coin_revSum_one (μ2 : ℝ) (ω : Bool × Bool) :
    revSum ExpectationsFiniteTree.coinSystem μ2 ExpectationsFiniteTree.coinShock 0 1 ω =
      μ2⁻¹ * ExpectationsFiniteTree.coinShock 1 ω := by
  unfold revSum
  rw [tsum_eq_single 0 (fun j hj => by
    rw [coin_rev_ge_two (by omega)]; simp)]
  simp [coin_rev_one]

/-- Woodford (2003), App. F (coin-flip economy): `∑_j μ₂^{−j−1} I_1[ε_{2+j}] = 0`. -/
theorem coin_revSum_two (μ2 : ℝ) (ω : Bool × Bool) :
    revSum ExpectationsFiniteTree.coinSystem μ2 ExpectationsFiniteTree.coinShock 0 2 ω = 0 := by
  unfold revSum
  have : ∀ j, μ2⁻¹ ^ (j + 1) *
      rev ExpectationsFiniteTree.coinSystem 0 (ExpectationsFiniteTree.coinShock (2 + j)) ω = 0 :=
    fun j => by rw [coin_rev_ge_two (by omega)]; simp
  simp only [this, tsum_zero]

/-- **Survey error E5 confirmed** (Woodford (2003), (2.17), p. 493 and (F.6), p. 711): in the
coin-flip economy with cost-push shock `u = ε` (bounded, adapted, mean-zero, `E_t u_T → 0`), no
plan satisfies the printed formula when `κ ≠ λ`. -/
theorem not_printed_217 {β κ lam xs μ1 μ2 : ℝ} (hβ : 0 < β) (hμ2 : 1 < μ2) (hκl : κ ≠ lam)
    (hlam : lam ≠ 0) {π x φ : ℕ → Bool × Bool → ℝ}
    (hP : Plan ExpectationsFiniteTree.coinSystem β κ lam xs μ1 μ2
      ExpectationsFiniteTree.coinShock π x φ)
    (hφ0 : ExpectationsFiniteTree.coinSystem.E 0 (φ 0) = φ 0) :
    ¬ Printed217 ExpectationsFiniteTree.coinSystem β μ1 μ2 ExpectationsFiniteTree.coinShock x := by
  intro h
  have h1 := h 0 0 (true, true)
  have h2 := rev_x ExpectationsFiniteTree.coinSystem hμ2 coinShock_bdd hP hφ0 0 (true, true) 0
  rw [h2] at h1
  simp only [zero_add, add_zero, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
    Nat.sub_zero, coin_revSum_one] at h1
  have hc : ExpectationsFiniteTree.coinShock 1 (true, true) = 1 := by
    simp [ExpectationsFiniteTree.coinShock]
  rw [hc, mul_one] at h1
  have hμ0 : μ2⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have hβ0 : β⁻¹ ≠ 0 := inv_ne_zero hβ.ne'
  have : κ / lam = 1 := by
    have h3 : (κ / lam - 1) * (β⁻¹ * μ2⁻¹) = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 (mul_ne_zero hβ0 hμ0)
  rw [div_eq_one_iff_eq hlam] at this
  exact hκl this

/-- **Survey error E4 confirmed** (Woodford (2003), (2.16), p. 492 and (F.5), p. 711): in the
coin-flip economy no plan satisfies the printed formula (the response of `π_{t+1}` to a purely
transitory shock differs). -/
theorem not_printed_216 {β κ lam xs μ1 μ2 : ℝ} (hβ : 0 < β) (hμ2 : 1 < μ2)
    {π x φ : ℕ → Bool × Bool → ℝ}
    (hP : Plan ExpectationsFiniteTree.coinSystem β κ lam xs μ1 μ2
      ExpectationsFiniteTree.coinShock π x φ)
    (hφ0 : ExpectationsFiniteTree.coinSystem.E 0 (φ 0) = φ 0) :
    ¬ Printed216 ExpectationsFiniteTree.coinSystem β μ1 μ2 ExpectationsFiniteTree.coinShock π := by
  intro h
  have h1 := h 0 1 (true, true)
  have h2 := rev_pi ExpectationsFiniteTree.coinSystem hμ2 coinShock_bdd hP hφ0 0 (true, true) 1
  rw [h2] at h1
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul] at h1
  rw [show (1 + 1 - (0 + 1) : ℕ) = 1 by rfl, show (1 + 1 : ℕ) = 2 by rfl, coin_revSum_two,
    coin_revSum_one] at h1
  have hc : ExpectationsFiniteTree.coinShock 1 (true, true) = 1 := by
    simp [ExpectationsFiniteTree.coinShock]
  rw [hc, mul_one] at h1
  have hμ0 : μ2⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have hβ0 : β⁻¹ ≠ 0 := inv_ne_zero hβ.ne'
  exact mul_ne_zero hβ0 hμ0 (by linear_combination -h1)

/-- **Survey error E6 confirmed** (Woodford (2003), App. F, p. 711): under perfect foresight with a
constant shock `u ≡ ū ≠ 0` all forecast revisions vanish, so the printed recursion (with
`E_t[u_{t+m+j}]`) fails for every multiplier path. -/
theorem not_printed_F2_recursion {β μ1 μ2 ub : ℝ} (hβ : 0 < β) (hμ2 : 1 < μ2) (hub : ub ≠ 0)
    (φ : ℕ → Unit → ℝ) : ¬ PrintedF2Rec perfectForesight β μ1 μ2 (fun _ _ => ub) φ := by
  intro h
  have h1 := h 0 0 ()
  have hrev : ∀ y : Unit → ℝ, rev perfectForesight 0 y = 0 := fun y => by
    unfold rev; simp [perfectForesight]
  rw [hrev, hrev] at h1
  have hq0 : 0 ≤ μ2⁻¹ := inv_nonneg.mpr (by linarith)
  have hq1 : μ2⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ2
  have hs : ∑' j : ℕ, μ2⁻¹ ^ (j + 1) * perfectForesight.E (0 + 1)
      ((fun _ _ => ub : ℕ → Unit → ℝ) (0 + 1 + 0 + j)) () = μ2⁻¹ * ub * (1 - μ2⁻¹)⁻¹ := by
    have : ∀ j : ℕ, μ2⁻¹ ^ (j + 1) * perfectForesight.E (0 + 1)
        ((fun _ _ => ub : ℕ → Unit → ℝ) (0 + 1 + 0 + j)) () = μ2⁻¹ * ub * μ2⁻¹ ^ j :=
      fun j => by simp [perfectForesight]; ring
    simp only [this]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  rw [hs] at h1
  have hpos : 0 < μ2⁻¹ := inv_pos.mpr (by linarith)
  have hq' : 0 < 1 - μ2⁻¹ := by linarith
  have : β⁻¹ * (μ2⁻¹ * ub * (1 - μ2⁻¹)⁻¹) = 0 := by simp only [Pi.zero_apply] at h1; linarith
  rcases mul_eq_zero.mp this with h2 | h2
  · exact (inv_ne_zero hβ.ne') h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact hpos.ne' h4
      · exact hub h4
    · exact (inv_ne_zero hq'.ne') h3

/-! ### Proposition 7.10, corrected: the long-run expected price level -/

/-- Woodford (2003), (F.8), p. 712: with `p_t = p_{t−1} + π_t`, (1.7) says `p_t + φ_t` never
changes: `p_t + φ_t = p_{t₀−1} + φ_{t₀−1}` at every date. -/
theorem price_plus_phi_const {β κ lam xs μ1 μ2 : ℝ} {u π x φ p : ℕ → Ω → ℝ}
    (hp : ∀ t, p (t + 1) = p t + π (t + 1)) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) :
    ∀ t, p t + φ t = p 0 + φ 0 := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [hp t, hP.1 t, ← ih]
    abel

/-- Woodford (2003), (F.9), p. 712: `E_s p_T = (p_{t₀−1} + φ_{t₀−1}) − E_s φ_T`. -/
theorem E_p_eq {β κ lam xs μ1 μ2 : ℝ} {u π x φ p : ℕ → Ω → ℝ}
    (hp : ∀ t, p (t + 1) = p t + π (t + 1)) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hp0 : 𝔼.E 0 (p 0) = p 0) (hφ0 : 𝔼.E 0 (φ 0) = φ 0) (s T : ℕ) (ω : Ω) :
    𝔼.E s (p T) ω = p 0 ω + φ 0 ω - 𝔼.E s (φ T) ω := by
  have h := price_plus_phi_const 𝔼 hp hP T
  have hT : p T = (p 0 + φ 0) - φ T := by rw [← h]; abel
  have hk : 𝔼.E s (p 0 + φ 0) = p 0 + φ 0 := by
    rw [map_add, ForwardSolution.E_of_known 𝔼 (Nat.zero_le s) hp0,
      ForwardSolution.E_of_known 𝔼 (Nat.zero_le s) hφ0]
  rw [hT, map_sub, hk]
  rfl

/-- Woodford (2003), Prop. 7.10, p. 498, and (F.9), made exact: along any plan, the long-run
date-`s` forecast of the price level equals `p_{t₀−1} + φ_{t₀−1} + (λ/κ)(x* + V/κ)` **iff** the
long-run date-`s` forecast of the cost-push shock equals `V`. -/
theorem tendsto_E_p_iff_u {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ p : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (hp : ∀ t, p (t + 1) = p t + π (t + 1))
    (hp0 : 𝔼.E 0 (p 0) = p 0) (hφ0 : 𝔼.E 0 (φ 0) = φ 0) (s : ℕ) (ω : Ω) (V : ℝ) :
    Tendsto (fun T => 𝔼.E s (p T) ω) atTop (𝓝 (p 0 ω + φ 0 ω + lam / κ * (xs + V / κ))) ↔
      Tendsto (fun T => 𝔼.E s (u T) ω) atTop (𝓝 V) := by
  rw [← tendsto_E_phi_iff 𝔼 hβ hκ hlam hr hu hP s ω V]
  have hfun : (fun T => 𝔼.E s (p T) ω) = fun T => p 0 ω + φ 0 ω - 𝔼.E s (φ T) ω :=
    funext fun T => E_p_eq 𝔼 hp hP hp0 hφ0 s T ω
  rw [hfun]
  constructor
  · intro h
    have := (tendsto_const_nhds (x := p 0 ω + φ 0 ω)).sub h
    rw [show p 0 ω + φ 0 ω - (p 0 ω + φ 0 ω + lam / κ * (xs + V / κ)) =
      lam / κ * (-V / κ - xs) by ring] at this
    exact this.congr fun T => by ring
  · intro h
    have := (tendsto_const_nhds (x := p 0 ω + φ 0 ω)).sub h
    rwa [show p 0 ω + φ 0 ω - lam / κ * (-V / κ - xs) =
      p 0 ω + φ 0 ω + lam / κ * (xs + V / κ) by ring] at this

/-- Woodford (2003), Prop. 7.10, p. 498 (existence of `p∞`), made exact: along any plan the
long-run date-`s` forecast of the price level exists iff the long-run date-`s` forecast of the
cost-push shock exists. -/
theorem tendsto_E_p_iff {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ p : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (hp : ∀ t, p (t + 1) = p t + π (t + 1))
    (hp0 : 𝔼.E 0 (p 0) = p 0) (hφ0 : 𝔼.E 0 (φ 0) = φ 0) (s : ℕ) (ω : Ω) :
    (∃ pinf, Tendsto (fun T => 𝔼.E s (p T) ω) atTop (𝓝 pinf)) ↔
      ∃ V, Tendsto (fun T => 𝔼.E s (u T) ω) atTop (𝓝 V) := by
  constructor
  · rintro ⟨pinf, h⟩
    refine ⟨κ * (κ / lam * (pinf - (p 0 ω + φ 0 ω)) - xs), ?_⟩
    rw [← tendsto_E_p_iff_u 𝔼 hβ hκ hlam hr hu hP hp hp0 hφ0 s ω]
    convert h using 2
    field_simp
    ring
  · rintro ⟨V, h⟩
    exact ⟨_, (tendsto_E_p_iff_u 𝔼 hβ hκ hlam hr hu hP hp hp0 hφ0 s ω V).mpr h⟩

/-- **Proposition 7.10, corrected** (Woodford (2003), p. 498, App. F.3, pp. 712–713): if
`E_t u_T → 0` at every date and state (survey error E7), then under any plan (the `t₀`-optimal
one and every timelessly optimal one) the long-run expected price level exists and equals
`p∞ = p_{t₀−1} + φ_{t₀−1} + (λ/κ)x*`, the same at every date `s` whatever the history of
disturbances (it is known at the date of the initial multiplier). -/
theorem prop_7_10 {β κ lam xs μ1 μ2 M : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0) (hlam : lam ≠ 0)
    (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ p : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M)
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (hp : ∀ t, p (t + 1) = p t + π (t + 1))
    (hp0 : 𝔼.E 0 (p 0) = p 0) (hφ0 : 𝔼.E 0 (φ 0) = φ 0)
    (hdecay : ∀ s ω, Tendsto (fun T => 𝔼.E s (u T) ω) atTop (𝓝 0)) (s : ℕ) (ω : Ω) :
    Tendsto (fun T => 𝔼.E s (p T) ω) atTop (𝓝 (p 0 ω + φ 0 ω + lam / κ * xs)) := by
  have := (tendsto_E_p_iff_u 𝔼 hβ hκ hlam hr hu hP hp hp0 hφ0 s ω 0).mpr (hdecay s ω)
  simpa using this

/-- Woodford (2003), (F.2), p. 709: `π_{t₀} = (1 − μ₁)(φ_{t₀−1} + (λ/κ)x*) +
β⁻¹ ∑_j μ₂^{−j−1} E_{t₀} u_{t₀+j}`. -/
theorem pi_one_eq {β κ lam xs μ1 μ2 : ℝ} {u π x φ : ℕ → Ω → ℝ}
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (ω : Ω) :
    π 1 ω = (1 - μ1) * (φ 0 ω + lam / κ * xs) +
      β⁻¹ * μ2⁻¹ * 𝔼.forwardSeries μ2⁻¹ u 1 ω := by
  have h1 := congrFun (hP.1 0) ω
  have h2 := congrFun (hP.2.2 0) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zero_add] at h1 h2
  rw [h1, h2]
  ring

/-- **Proposition 7.10, the target case** (Woodford (2003), p. 498, App. F.3, p. 712): under the
initial constraint (2.13), `π_{t₀} = −(1 − μ₁)(p_{t₀−1} − p̄) + β⁻¹∑_j μ₂^{−j−1}E_{t₀}u_{t₀+j}`,
the initial multiplier is `φ_{t₀−1} = −(λ/κ)x* − (p_{t₀−1} − p̄)`, and if `E_t u_T → 0` the
long-run expected price level is the target `p̄` at every date and state. -/
theorem prop_7_10_target {β κ lam xs μ1 μ2 M pbar : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0)
    (hlam : lam ≠ 0) (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) {u π x φ p : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ)
    (hp : ∀ t, p (t + 1) = p t + π (t + 1)) (hp0 : 𝔼.E 0 (p 0) = p 0)
    (hφ0 : 𝔼.E 0 (φ 0) = φ 0)
    (h213 : ∀ ω, π 1 ω = -(1 - μ1) * (p 0 ω - pbar) + β⁻¹ * μ2⁻¹ * 𝔼.forwardSeries μ2⁻¹ u 1 ω) :
    (∀ ω, φ 0 ω = -(lam / κ * xs) - (p 0 ω - pbar)) ∧
      ((∀ s ω, Tendsto (fun T => 𝔼.E s (u T) ω) atTop (𝓝 0)) →
        ∀ s ω, Tendsto (fun T => 𝔼.E s (p T) ω) atTop (𝓝 pbar)) := by
  have h1 : 1 - μ1 ≠ 0 := by linarith [hr.2.1]
  have hφ : ∀ ω, φ 0 ω = -(lam / κ * xs) - (p 0 ω - pbar) := by
    intro ω
    have h := (pi_one_eq 𝔼 hP ω).symm.trans (h213 ω)
    have h' : (1 - μ1) * (φ 0 ω - (-(lam / κ * xs) - (p 0 ω - pbar))) = 0 := by
      linear_combination h
    rcases mul_eq_zero.mp h' with h2 | h2
    · exact absurd h2 h1
    · linarith
  refine ⟨hφ, fun hdecay s ω => ?_⟩
  have := prop_7_10 𝔼 hβ hκ hlam hr hu hP hp hp0 hφ0 hdecay s ω
  rwa [hφ ω, show p 0 ω + (-(lam / κ * xs) - (p 0 ω - pbar)) + lam / κ * xs = pbar by ring]
    at this

/-- Woodford (2003), App. F: the bounded alternating sequence `(−1)ᵗ ū`, `ū ≠ 0`, has no limit. -/
theorem alternating_not_tendsto {ub : ℝ} (hub : ub ≠ 0) (L : ℝ) :
    ¬ Tendsto (fun T : ℕ => (-1 : ℝ) ^ T * ub) atTop (𝓝 L) := by
  intro hL
  have h2 := ((tendsto_add_atTop_iff_nat 1).mpr hL).add hL
  have hz : Tendsto (fun T : ℕ => (-1 : ℝ) ^ (T + 1) * ub + (-1) ^ T * ub) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun T => by ring
  have hL0 : L = 0 := by
    have := tendsto_nhds_unique h2 hz; linarith
  rw [hL0] at hL
  have habs := hL.abs
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_zero] at habs
  exact hub (abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds habs))

/-- Woodford (2003), Prop. 7.10, p. 498 (survey error E7): under perfect foresight with
`u_t = (−1)ᵗ ū`, `ū ≠ 0`, no plan has a long-run expected price level. -/
theorem counterexample_7_10 {β κ lam xs μ1 μ2 ub : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0)
    (hlam : lam ≠ 0) (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) (hub : ub ≠ 0)
    {π x φ p : ℕ → Unit → ℝ}
    (hP : Plan perfectForesight β κ lam xs μ1 μ2 (fun t _ => (-1) ^ t * ub) π x φ)
    (hp : ∀ t, p (t + 1) = p t + π (t + 1)) (s : ℕ) (ω : Unit) :
    ¬ ∃ pinf, Tendsto (fun T => perfectForesight.E s (p T) ω) atTop (𝓝 pinf) := by
  have hu : ∀ t (ω : Unit), |(fun t _ => (-1) ^ t * ub : ℕ → Unit → ℝ) t ω| ≤ |ub| :=
    fun t _ => by simp [abs_mul]
  rw [tendsto_E_p_iff perfectForesight hβ hκ hlam hr hu hP hp rfl rfl s ω]
  rintro ⟨V, hV⟩
  exact alternating_not_tendsto hub V hV

/-- Woodford (2003), Prop. 7.10, p. 498 (survey error E7): under perfect foresight with a
constant shock `u ≡ ū ≠ 0` and the initial constraint (2.13), the long-run price level exists
but equals `p̄ + (λ/κ²)ū ≠ p̄`. -/
theorem counterexample_7_10_const {β κ lam xs μ1 μ2 ub pbar : ℝ} (hβ : 0 < β) (hκ : κ ≠ 0)
    (hlam : lam ≠ 0) (hr : RootPair β (κ ^ 2 / lam) μ1 μ2) (hub : ub ≠ 0)
    {π x φ p : ℕ → Unit → ℝ}
    (hP : Plan perfectForesight β κ lam xs μ1 μ2 (fun _ _ => ub) π x φ)
    (hp : ∀ t, p (t + 1) = p t + π (t + 1))
    (h213 : ∀ ω, π 1 ω = -(1 - μ1) * (p 0 ω - pbar) +
      β⁻¹ * μ2⁻¹ * perfectForesight.forwardSeries μ2⁻¹ (fun _ _ => ub) 1 ω) (s : ℕ) (ω : Unit) :
    Tendsto (fun T => perfectForesight.E s (p T) ω) atTop (𝓝 (pbar + lam / κ ^ 2 * ub)) ∧
      pbar + lam / κ ^ 2 * ub ≠ pbar := by
  have hu : ∀ t (ω : Unit), |(fun _ _ => ub : ℕ → Unit → ℝ) t ω| ≤ |ub| := fun _ _ => le_rfl
  have hφ := (prop_7_10_target perfectForesight (pbar := pbar) hβ hκ hlam hr hu hP hp rfl rfl
    h213).1 ω
  have h := (tendsto_E_p_iff_u perfectForesight hβ hκ hlam hr hu hP hp rfl rfl s ω ub).mpr
    tendsto_const_nhds
  refine ⟨?_, ?_⟩
  · rwa [hφ, show p 0 ω + (-(lam / κ * xs) - (p 0 ω - pbar)) + lam / κ * (xs + ub / κ) =
      pbar + lam / κ ^ 2 * ub by field_simp; ring] at h
  · intro h'
    have : lam / κ ^ 2 * ub = 0 := by linarith
    rcases mul_eq_zero.mp this with h2 | h2
    · exact div_ne_zero hlam (pow_ne_zero 2 hκ) h2
    · exact hub h2

/-! ### Page 501 and footnote 22: full indexation (γ = 1) and unit roots -/

/-- Woodford (2003), eq. (1.21), p. 480, and footnote 22, p. 501: quasi-differenced inflation
`π_t − γ π_{t−1}`. -/
def quasiDiff (γ : ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t => π t - γ • π (t - 1)

/-- Woodford (2003), p. 489: the multiplier path of a plan is determined by its initial value
(the recursion (2.7) does not involve `π` or `x`). -/
theorem plan_phi_unique {β κ lam xs μ1 μ2 : ℝ} {u π x φ π' x' φ' : ℕ → Ω → ℝ}
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (hP' : Plan 𝔼 β κ lam xs μ1 μ2 u π' x' φ')
    (h0 : φ 0 = φ' 0) : φ = φ' := by
  funext t
  induction t with
  | zero => exact h0
  | succ t ih => rw [hP.2.2 t, hP'.2.2 t, ih]

/-- **Footnote 22, p. 501** (Woodford (2003)): optimal policy with indexation `γ` is the plan of
Prop. 7.9 with `π_t` replaced by `π_t − γπ_{t−1}`. With `γ = 1`, the optimal inflation path is
the optimal price-level path of the `γ = 0` economy (same shocks, same initial multiplier), up to
the constant `π_{t₀−1} − p_{t₀−1}`. -/
theorem gamma_one_reduction {β κ lam xs μ1 μ2 : ℝ} {u π1 x1 φ1 π0 x0 φ0 p0 : ℕ → Ω → ℝ}
    (hP1 : Plan 𝔼 β κ lam xs μ1 μ2 u (quasiDiff 1 π1) x1 φ1)
    (hP0 : Plan 𝔼 β κ lam xs μ1 μ2 u π0 x0 φ0) (hφ : φ1 0 = φ0 0)
    (hp0 : ∀ t, p0 (t + 1) = p0 t + π0 (t + 1)) : ∀ t, π1 t - p0 t = π1 0 - p0 0 := by
  have hφe := plan_phi_unique 𝔼 hP1 hP0 hφ
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 := hP1.1 t
    simp only [quasiDiff, Nat.add_sub_cancel, one_smul] at h1
    rw [hp0 t, hP0.1 t, ← ih, hφe] at *
    have : π1 (t + 1) = π1 t + (φ0 t - φ0 (t + 1)) := by rw [← h1]; abel
    rw [this]
    abel

/-- Woodford (2003), p. 501: the lag polynomial `a(L)` applied to a process, `(a(L)y)_{t+N}`
`= ∑_{k ≤ N} a_k y_{t+N−k}` (`N` at least the degree of `a`). The order of integration of `y`
is the multiplicity of `z = 1` as a root of `a` when `a(L) y` is bounded (stationary). -/
noncomputable def lagApply (N : ℕ) (a : Polynomial ℝ) (y : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  ∑ k ∈ Finset.range (N + 1), a.coeff k • y (t + N - k)

/-- Woodford (2003), p. 501: `1 − X` has a simple root at `z = 1` (one unit root). -/
theorem rootMult_unit : (1 - Polynomial.X : Polynomial ℝ).rootMultiplicity 1 = 1 := by
  have : (1 - Polynomial.X : Polynomial ℝ) =
      Polynomial.C (-1) * (Polynomial.X - Polynomial.C 1) := by
    simp only [map_neg, map_one]; ring
  rw [this, Polynomial.rootMultiplicity_mul, Polynomial.rootMultiplicity_C,
    Polynomial.rootMultiplicity_X_sub_C_self, zero_add]
  exact mul_ne_zero (by simp) (Polynomial.X_sub_C_ne_zero 1)

/-- Woodford (2003), p. 501: `1 − μ₁X` (`μ₁ ≠ 1`) has no unit root. -/
theorem rootMult_stable {μ1 : ℝ} (hμ1 : μ1 ≠ 1) :
    (1 - Polynomial.C μ1 * Polynomial.X : Polynomial ℝ).rootMultiplicity 1 = 0 := by
  refine Polynomial.rootMultiplicity_eq_zero fun h => hμ1 ?_
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, mul_one] at h
  linarith

/-- Woodford (2003), p. 501: `(1 − X)(1 − μ₁X)` (`μ₁ ≠ 1`) has exactly one unit root. -/
theorem rootMult_one_unit {μ1 : ℝ} (hμ1 : μ1 ≠ 1) :
    ((1 - Polynomial.X) * (1 - Polynomial.C μ1 * Polynomial.X) : Polynomial ℝ).rootMultiplicity 1
      = 1 := by
  have h2 : (1 - Polynomial.C μ1 * Polynomial.X : Polynomial ℝ) ≠ 0 := fun h => by
    have := congrArg (Polynomial.eval 0) h
    simp at this
  have h1 : (1 - Polynomial.X : Polynomial ℝ) ≠ 0 := fun h => by
    have := congrArg (Polynomial.eval 0) h
    simp at this
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero h1 h2), rootMult_unit, rootMult_stable hμ1]

/-- Woodford (2003), p. 501: `(1 − X)²` has a double unit root. -/
theorem rootMult_two_units : ((1 - Polynomial.X) ^ 2 : Polynomial ℝ).rootMultiplicity 1 = 2 := by
  have : ((1 - Polynomial.X) ^ 2 : Polynomial ℝ) = (Polynomial.X - Polynomial.C 1) ^ 2 := by
    simp only [map_one]; ring
  rw [this, Polynomial.rootMultiplicity_X_sub_C_pow]

/-- Woodford (2003), p. 501 (optimal policy, `γ = 0`, the price level is stationary): along a
plan the price level obeys `(1 − μ₁L)p_{t+1} = (1 − μ₁)(p_{t₀−1} + φ_{t₀−1}) +
(1 − μ₁)(λ/κ)x* + β⁻¹μ₂⁻¹∑_j μ₂^{−j}E_{t+1}u_{t+1+j}`, whose lag polynomial has no unit root
(`rootMult_stable`); indeed `p_t = p_{t₀−1} + φ_{t₀−1} − φ_t` is bounded. -/
theorem price_law_opt_gamma0 {β κ lam xs μ1 μ2 : ℝ} {u π x φ p : ℕ → Ω → ℝ}
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u π x φ) (hp : ∀ t, p (t + 1) = p t + π (t + 1)) (t : ℕ) :
    lagApply 1 (1 - Polynomial.C μ1 * Polynomial.X) p t =
      (1 - μ1) • (p 0 + φ 0) + (fun _ => (1 - μ1) * (lam / κ) * xs) +
        (β⁻¹ * μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ u (t + 1) := by
  have hc := price_plus_phi_const 𝔼 hp hP
  have h0 : p t = (p 0 + φ 0) - φ t := by rw [← hc t]; abel
  have h1 : p (t + 1) = (p 0 + φ 0) - φ (t + 1) := by rw [← hc (t + 1)]; abel
  unfold lagApply
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul, Polynomial.coeff_X,
    Nat.sub_zero, Nat.add_sub_cancel]
  simp only [↓reduceIte, one_ne_zero, sub_zero, mul_zero, mul_one, zero_sub, one_smul,
    neg_smul]
  rw [h0, h1, hP.2.2 t]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 501 ("under optimal policy, the price is an integrated process of
order one" when `γ = 1`): along the `γ = 1` plan, `π_t + φ_t` is constant, and the price level
obeys `(1 − L)(1 − μ₁L)p_{t+2} = (1 − μ₁)(π_{t₀−1} + φ_{t₀−1}) + (1 − μ₁)(λ/κ)x* +
β⁻¹μ₂⁻¹∑_j μ₂^{−j}E_{t+2}u_{t+2+j}` (bounded forcing), whose lag polynomial has exactly one
unit root (`rootMult_one_unit`). -/
theorem price_law_opt_gamma1 {β κ lam xs μ1 μ2 : ℝ} {u π x φ p : ℕ → Ω → ℝ}
    (hP : Plan 𝔼 β κ lam xs μ1 μ2 u (quasiDiff 1 π) x φ) (hp : ∀ t, p (t + 1) = p t + π (t + 1))
    (t : ℕ) :
    (∀ n, π n + φ n = π 0 + φ 0) ∧
    lagApply 2 ((1 - Polynomial.X) * (1 - Polynomial.C μ1 * Polynomial.X)) p t =
      (1 - μ1) • (π 0 + φ 0) + (fun _ => (1 - μ1) * (lam / κ) * xs) +
        (β⁻¹ * μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ u (t + 2) := by
  have hc : ∀ n, π n + φ n = π 0 + φ 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have h1 := hP.1 n
      simp only [quasiDiff, Nat.add_sub_cancel, one_smul] at h1
      rw [← ih]
      have : π (n + 1) = π n + (φ n - φ (n + 1)) := by rw [← h1]; abel
      rw [this]; abel
  refine ⟨hc, ?_⟩
  have hpoly : ((1 - Polynomial.X) * (1 - Polynomial.C μ1 * Polynomial.X) : Polynomial ℝ) =
      1 - Polynomial.C (1 + μ1) * Polynomial.X + Polynomial.C μ1 * Polynomial.X ^ 2 := by
    simp only [map_add, map_one]; ring
  have h2 : π (t + 2) = (π 0 + φ 0) - φ (t + 2) := by rw [← hc (t + 2)]; abel
  have h1 : π (t + 1) = (π 0 + φ 0) - φ (t + 1) := by rw [← hc (t + 1)]; abel
  unfold lagApply
  rw [hpoly]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num
  have hp2 : p (t + 2) = p (t + 1) + π (t + 2) := hp (t + 1)
  have hφ2 : φ (t + 2) = μ1 • φ (t + 1) - (fun _ => (1 - μ1) * (lam / κ) * xs) -
      (β⁻¹ * μ2⁻¹) • 𝔼.forwardSeries μ2⁻¹ u (t + 2) := hP.2.2 (t + 1)
  rw [hp2, hp t, h2, h1, hφ2]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 501 (discretion, `γ = 0`: the price level is `I(1)`): `(1 − L)p_{t+1} =
π_{t+1}`, with bounded inflation under discretion (Prop. 7.5), and `1 − X` has one unit root
(`rootMult_unit`). -/
theorem price_law_disc_gamma0 {π p : ℕ → Ω → ℝ} (hp : ∀ t, p (t + 1) = p t + π (t + 1))
    (t : ℕ) : lagApply 1 (1 - Polynomial.X) p t = π (t + 1) := by
  unfold lagApply
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X]
  norm_num
  rw [hp t]
  abel

/-- Woodford (2003), p. 501 ("under discretion it is an integrated process of order two, since
there is a unit root in the inflation rate"): with `γ = 1`, if quasi-differenced inflation
`π_t − π_{t−1}` follows the bounded discretionary law `π^d` (Prop. 7.5), the price level obeys
`(1 − L)²p_{t+2} = π^d_{t+2}`, and `(1 − X)²` has a double unit root (`rootMult_two_units`). -/
theorem price_law_disc_gamma1 {π πd p : ℕ → Ω → ℝ} (hp : ∀ t, p (t + 1) = p t + π (t + 1))
    (hd : ∀ t, quasiDiff 1 π (t + 1) = πd (t + 1)) (t : ℕ) :
    lagApply 2 ((1 - Polynomial.X) ^ 2) p t = πd (t + 2) := by
  have hpoly : ((1 - Polynomial.X) ^ 2 : Polynomial ℝ) =
      1 - Polynomial.C 2 * Polynomial.X + Polynomial.X ^ 2 := by
    simp only [map_ofNat]; ring
  have h1 : π (t + 2) - π (t + 1) = πd (t + 2) := by
    have := hd (t + 1)
    simpa [quasiDiff] using this
  have hp2 : p (t + 2) = p (t + 1) + π (t + 2) := hp (t + 1)
  unfold lagApply
  rw [hpoly]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X, Polynomial.coeff_X_pow]
  norm_num
  rw [← h1, hp2, hp t]
  funext ω
  simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), eq. (2.3), p. 487 (and Prop. 7.5): the discretionary inflation law
`π_t = π̄ + a ∑_j (βa)ʲ E_t u_{t+j}`, `a = λ/(λ + κ²)`, is bounded (so it is a stationary forcing
term in `price_law_disc_gamma0`, `price_law_disc_gamma1`). -/
theorem disc_bounded {β κ lam M pibar : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hlam : 0 < lam)
    {u : ℕ → Ω → ℝ} (hu : ∀ t ω, |u t ω| ≤ M) :
    BoundedProc (fun t => (fun _ => pibar) +
      (lam / (lam + κ ^ 2)) • 𝔼.forwardSeries (β * (lam / (lam + κ ^ 2))) u t) := by
  have hκ : 0 ≤ κ ^ 2 := sq_nonneg κ
  have ha0 : 0 ≤ lam / (lam + κ ^ 2) := div_nonneg hlam.le (by linarith)
  have ha1 : lam / (lam + κ ^ 2) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  have hb0 : 0 ≤ β * (lam / (lam + κ ^ 2)) := mul_nonneg hβ0 ha0
  have hb1 : β * (lam / (lam + κ ^ 2)) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hβ0 ha1) hβ1
  obtain ⟨B, hB⟩ := 𝔼.forwardSeries_bounded hb0 hb1 hu
  refine ⟨|pibar| + B, fun t ω => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |pibar + lam / (lam + κ ^ 2) * 𝔼.forwardSeries (β * (lam / (lam + κ ^ 2))) u t ω|
      ≤ |pibar| + |lam / (lam + κ ^ 2)| * |𝔼.forwardSeries (β * (lam / (lam + κ ^ 2))) u t ω| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ |pibar| + 1 * B := by
        gcongr
        · rw [abs_of_nonneg ha0]; exact ha1
        · exact hB t ω
    _ = |pibar| + B := by ring

end Woodford.GainsFromCommitment.ImpulseResponses
