/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.TidyR6ForwardSunspots
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Nonlinear sunspots on a one-dimensional critical direction: the leading-coefficient criterion

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 632–634. When the operator (A.8) is
neither onto nor bounded below, the linearisation does not decide whether random sunspot
equilibria exist (`SunspotsNotOntoExamples.unit_root_undecided`). This module characterises the
answer by the higher-order terms for a **one-dimensional critical direction**: the scalar forward
system `E_t[x_{t+1} − g(x_t)] = 0` with `g'(0) = σ`, `σ = ±1` (the critical root `σ` on the unit
circle; (A.8) is `v_{t+1} − σ v_t`, neither one-to-one nor onto, range not closed).

## Main results

* `coin_sunspots_iff` (**the criterion, both directions**): write the two-step map as
  `g(g(x)) = x + c xᵐ + o(xᵐ)` with `c ≠ 0`, `m ≥ 2`. Random sunspot equilibria exist at every
  scale on the core coin tree **iff `c < 0` or `m` is even** (`CoinSunspots`).
* `comp_expansion`: if `g(x) = σx + c xᵏ + o(xᵏ)` then `g(g(x)) = x + c(σ + σᵏ)xᵏ + o(xᵏ)`.
* `unit_root_criterion` (`σ = 1`, `g(x) = x + c xᵏ + o(xᵏ)`): sunspots iff `c < 0` or `k` even;
  and for `c > 0`, `k` odd, the steady state is the only nearby equilibrium under **every**
  informationally closed expectation system (`unique_of_one_step`).
* `flip_root_criterion` (`σ = −1`, `g(x) = −x + c xᵏ + o(xᵏ)`, `k` odd): sunspots iff `c > 0`;
  for `c < 0` uniqueness under every informationally closed system.

## What the criterion cannot be weakened to

* `flip_even_undecided`: for `σ = −1` and `k` even the leading coefficient of `g` itself does not
  decide (`g₁ = −x + x²` has sunspots, `g₂ = −x + x² − 2x³` has none, same `σ, k, c`): the
  criterion must be stated for `g ∘ g`, whose order-`k` term cancels.
* `flat_undecided`: `c ≠ 0` (a finite-order nondegeneracy) cannot be dropped: `gm = x − f(x)` and
  `gp = x + f(x)` with `f` flat (`f(x) = e^{−1/x}` for `x > 0`, odd) are `C^∞`, have **identical
  derivatives of every order** at the steady state and the same operator (A.8) as
  `SunspotsNotOntoExamples.Gatt`, yet the
  first has random sunspots and the second has none under any informationally closed system. So
  no criterion in the Taylor jet decides the sunspot question in general.
-/

namespace Woodford.PriceLevelDetermination.TidyR6CriticalCriterion

open scoped Topology
open Asymptotics Filter
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic TidyR6ForwardSunspots
open LocalIFTSystems (Arg linOp)
open ExpectationsFiniteTree (coinSystem)

/-! ### Scalar systems -/

/-- Woodford (2003), App. A.3, p. 633 (tool): a scalar map acting on `ℝ¹`. -/
def lift (g : ℝ → ℝ) (v : Fin 1 → ℝ) : Fin 1 → ℝ := fun _ => g (v 0)

/-- Woodford (2003), App. A.3, p. 633 (tool): the sup norm on `ℝ¹` is the absolute value. -/
theorem norm_fin1 (v : Fin 1 → ℝ) : ‖v‖ = |v 0| := by
  have e : v = fun _ => v 0 := funext fun i => by fin_cases i; rfl
  rw [e, pi_norm_const, Real.norm_eq_abs]

/-- Woodford (2003), App. A.3, p. 633 (tool): lifting commutes with composition. -/
theorem lift_comp (g : ℝ → ℝ) : lift g ∘ lift g = lift (g ∘ g) := rfl

/-- Woodford (2003), App. A.3, pp. 632–634: **random sunspots at every scale on the coin tree**
for the scalar forward system `E_t[x_{t+1} − g(x_t)] = 0` (no disturbances, `x_{−1} = 0`):
for every `ε > 0` a bounded adapted equilibrium within `ε` of the steady state whose date-1
value differs across the first flip. -/
def CoinSunspots (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ x : SProcV (Fin 1) (Bool × Bool), SolvesSV coinSystem (Gfwd (lift g)) 0 x ∧
    ‖x‖ ≤ ε ∧ x (1, (true, true)) ≠ x (1, (false, true))

/-- Woodford (2003), App. A.3, p. 634 (tool): a scalar lower bound `|g z| ≥ |z| + κ|z|ᵐ` on
`|z| ≤ r` makes `g` repelling on annuli up to `r`. -/
theorem repelAnn_lift {g : ℝ → ℝ} {r κ : ℝ} {m : ℕ} (hκ : 0 < κ)
    (h : ∀ z, |z| ≤ r → |z| + κ * |z| ^ m ≤ |g z|) : RepelAnn (lift g) r := by
  intro B hB hBr
  refine ⟨κ * (B / 2) ^ m, by positivity, fun v hv1 hv2 => ?_⟩
  rw [norm_fin1] at hv1 hv2 ⊢
  rw [show ‖lift g v‖ = |g (v 0)| from norm_fin1 _]
  have h1 := h (v 0) (hv2.trans hBr)
  have h2 : (B / 2) ^ m ≤ |v 0| ^ m := pow_le_pow_left₀ (by positivity) hv1 m
  nlinarith

/-! ### Expansions -/

/-- Woodford (2003), App. A.3, p. 634 (tool): a little-o expansion as an explicit bound. -/
theorem bound_of_isLittleO {f : ℝ → ℝ} {k : ℕ} (h : f =o[𝓝 0] fun x => x ^ k) {η : ℝ}
    (hη : 0 < η) : ∃ δ > 0, ∀ x, |x| < δ → |f x| ≤ η * |x| ^ k := by
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.mp (h.def hη)
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have := hP (show dist x 0 < δ by rwa [dist_zero_right, Real.norm_eq_abs])
  simpa [Real.norm_eq_abs, abs_pow] using this

/-- Woodford (2003), App. A.3, p. 634 (tool): an expansion `g(x) = σx + c xᵏ + o(xᵏ)` with
`k ≥ 2` gives `g(0) = 0` and `g'(0) = σ`. -/
theorem hasDerivAt_of_expansion {g : ℝ → ℝ} {σ c : ℝ} {k : ℕ} (hk : 2 ≤ k)
    (hg : (fun x => g x - σ * x - c * x ^ k) =o[𝓝 0] fun x => x ^ k) :
    g 0 = 0 ∧ HasDerivAt g σ 0 := by
  have hk0 : k ≠ 0 := by omega
  have hg0 : g 0 = 0 := by
    have h := (hg.def one_pos).self_of_nhds
    simp only [mul_zero, sub_zero, zero_pow hk0, norm_zero] at h
    exact norm_le_zero_iff.mp h
  refine ⟨hg0, hasDerivAt_iff_isLittleO_nhds_zero.mpr ?_⟩
  have hpow : (fun x : ℝ => x ^ k) =o[𝓝 0] fun x => x := by
    have := isLittleO_pow_pow (𝕜 := ℝ) (show 1 < k by omega)
    simpa using this
  have h1 := (hg.trans hpow).add (hpow.const_mul_left c)
  refine h1.congr_left fun x => ?_
  simp only [zero_add, hg0, sub_zero, smul_eq_mul]
  ring

/-- Woodford (2003), App. A.3, p. 634 (tool): near the steady state a map with `g(0) = 0` and
`g'(0) = σ`, `σ² = 1`, satisfies `|z|/2 ≤ |g z| ≤ 2|z|`. -/
theorem near_lip {g : ℝ → ℝ} {σ : ℝ} (hσ : σ * σ = 1) (hg0 : g 0 = 0) (hd : HasDerivAt g σ 0) :
    ∃ δ > 0, ∀ z, |z| < δ → |z| / 2 ≤ |g z| ∧ |g z| ≤ 2 * |z| := by
  have h := hasDerivAt_iff_isLittleO_nhds_zero.mp hd
  have h' : (fun z => g z - σ * z) =o[𝓝 0] fun z => z ^ 1 := by
    refine (h.congr_left fun z => ?_).congr_right fun z => by rw [pow_one]
    simp only [zero_add, hg0, sub_zero, smul_eq_mul]
    ring
  obtain ⟨δ, hδ, hP⟩ := bound_of_isLittleO h' (show (0 : ℝ) < 1 / 2 by norm_num)
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have h1 := hP z hz
  rw [pow_one] at h1
  have h2 : |σ * z| = |z| := by rw [abs_mul, hs, one_mul]
  have h3 := abs_sub_abs_le_abs_sub (g z) (σ * z)
  have h4 := abs_sub_abs_le_abs_sub (σ * z) (g z)
  rw [abs_sub_comm] at h4
  constructor <;> linarith

/-- **The two-step expansion** (Woodford (2003), App. A.3, p. 634): if
`g(x) = σx + c xᵏ + o(xᵏ)` with `σ² = 1`, `k ≥ 2`, then
`g(g(x)) = x + c(σ + σᵏ)xᵏ + o(xᵏ)`: the coefficient is `2c` at a unit root (`σ = 1`), `−2c` at a
flip root (`σ = −1`) with `k` odd, and `0` at a flip root with `k` even. -/
theorem comp_expansion {g : ℝ → ℝ} {σ c : ℝ} {k : ℕ} (hσ : σ * σ = 1) (hk : 2 ≤ k)
    (hg : (fun x => g x - σ * x - c * x ^ k) =o[𝓝 0] fun x => x ^ k) :
    (fun x => g (g x) - x - c * (σ + σ ^ k) * x ^ k) =o[𝓝 0] fun x => x ^ k := by
  obtain ⟨hg0, hd⟩ := hasDerivAt_of_expansion hk hg
  set f : ℝ → ℝ := fun x => g x - σ * x - c * x ^ k with hf
  have ht : Tendsto g (𝓝 0) (𝓝 0) := by
    have := hd.continuousAt.tendsto
    rwa [hg0] at this
  have hgO : (fun x => g x) =O[𝓝 0] fun x => x := by
    have := hd.isBigO_sub
    simpa [hg0] using this
  have h1 : (fun x => f (g x)) =o[𝓝 0] fun x => x ^ k :=
    (hg.comp_tendsto ht).trans_isBigO (hgO.pow k)
  have hdiff : (fun x => g x - σ * x) =O[𝓝 0] fun x => x ^ k := by
    refine (hg.isBigO.add (isBigO_const_mul_self c (fun x : ℝ => x ^ k) (𝓝 0))).congr_left
      fun x => ?_
    simp only [hf]
    ring
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  have h2 : (fun x => g x ^ k - (σ * x) ^ k) =o[𝓝 0] fun x => x ^ k := by
    obtain ⟨C1, hC1, hB1⟩ := hdiff.exists_pos
    obtain ⟨C2, hC2, hB2⟩ := hgO.exists_pos
    have hO : (fun x => g x ^ k - (σ * x) ^ k) =O[𝓝 0] fun x => x ^ (2 * k - 1) := by
      refine IsBigO.of_bound (C1 * k * (max C2 1) ^ (k - 1)) ?_
      filter_upwards [hB1.bound, hB2.bound] with x hx1 hx2
      simp only [Real.norm_eq_abs, abs_pow] at hx1 hx2 ⊢
      have hab := abs_pow_sub_pow_le (a := g x) (b := σ * x) (n := k)
      have hM : max |g x| |σ * x| ≤ max C2 1 * |x| := by
        rw [abs_mul, hs, one_mul]
        refine max_le (hx2.trans ?_) ?_
        · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg x)
        · exact le_mul_of_one_le_left (abs_nonneg x) (le_max_right _ _)
      have hM' : max |g x| |σ * x| ^ (k - 1) ≤ (max C2 1 * |x|) ^ (k - 1) :=
        pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hM _
      have he : |x| ^ (2 * k - 1) = |x| ^ k * |x| ^ (k - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [he]
      calc |g x ^ k - (σ * x) ^ k| ≤ |g x - σ * x| * k * max |g x| |σ * x| ^ (k - 1) := hab
        _ ≤ (C1 * |x| ^ k) * k * (max C2 1 * |x|) ^ (k - 1) := by
            gcongr
        _ = C1 * k * max C2 1 ^ (k - 1) * (|x| ^ k * |x| ^ (k - 1)) := by
            rw [mul_pow]
            ring
    exact hO.trans_isLittleO (isLittleO_pow_pow (by omega))
  have e : (fun x => g (g x) - x - c * (σ + σ ^ k) * x ^ k) =
      fun x => σ * f x + c * (g x ^ k - (σ * x) ^ k) + f (g x) := by
    funext x
    simp only [hf, mul_pow]
    linear_combination x * hσ
  rw [e]
  exact ((hg.const_mul_left σ).add (h2.const_mul_left c)).add h1

/-- Woodford (2003), App. A.3, p. 634 (tool): an odd-order repelling expansion
`F(x) = x + a xᵐ + o(xᵐ)` with `a > 0`, `m` odd, gives `|F z| ≥ |z| + (a/2)|z|ᵐ` near `0`. -/
theorem lower_of_expansion {F : ℝ → ℝ} {a : ℝ} {m : ℕ} (ha : 0 < a) (hodd : Odd m)
    (h : (fun x => F x - x - a * x ^ m) =o[𝓝 0] fun x => x ^ m) :
    ∃ δ > 0, ∀ z, |z| < δ → |z| + a / 2 * |z| ^ m ≤ |F z| := by
  obtain ⟨δ, hδ, hP⟩ := bound_of_isLittleO h (half_pos ha)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have h1 := abs_le.mp (hP z hz)
  rcases le_or_gt 0 z with hz0 | hz0
  · have hza : |z| = z := abs_of_nonneg hz0
    have e : z ^ m = |z| ^ m := by rw [hza]
    rw [e] at h1
    have h2 : |z| + a / 2 * |z| ^ m ≤ F z := by linarith [h1.1]
    exact h2.trans (le_abs_self _)
  · have hza : |z| = -z := abs_of_neg hz0
    have e : z ^ m = -|z| ^ m := by
      rw [hza, Odd.neg_pow hodd, neg_neg]
    rw [e] at h1
    have h2 : F z ≤ -(|z| + a / 2 * |z| ^ m) := by linarith [h1.2]
    exact (le_neg.mp h2).trans (neg_le_abs _)

/-! ### The criterion on the coin tree -/

/-- Woodford (2003), App. A.3, p. 634 (tool): **the one-sided estimate.** If
`G(x) = x + c xᵐ + o(xᵐ)` with `m ≥ 2` and `c sᵐ⁺¹ < 0` for a sign `s`, then near `0` the side
`s·z > 0` is mapped into itself without increasing `|z|`: `0 < s G(z) ≤ s z`. -/
theorem side_estimate {G : ℝ → ℝ} {c s : ℝ} {m : ℕ} (hs : s * s = 1) (hm : 2 ≤ m)
    (hcs : c * s ^ (m + 1) < 0) (hG : (fun x => G x - x - c * x ^ m) =o[𝓝 0] fun x => x ^ m) :
    ∃ ρ > 0, ∀ z, 0 < s * z → s * z ≤ ρ → 0 < s * G z ∧ s * G z ≤ s * z := by
  set κ := -(c * s ^ (m + 1)) with hκdef
  have hκ : 0 < κ := by linarith
  obtain ⟨δ2, hδ2, hP⟩ := bound_of_isLittleO hG (half_pos hκ)
  have hsa : |s| = 1 := by nlinarith [abs_mul_abs_self s, abs_nonneg s]
  set ρ := min δ2 (min 1 (1 / (3 * κ))) / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hm0 : 0 < min δ2 (min 1 (1 / (3 * κ))) := by positivity
  have hρ2 : ρ < δ2 := by
    have := min_le_left δ2 (min 1 (1 / (3 * κ)))
    linarith
  have hρ3 : ρ ≤ 1 := by
    have := min_le_right δ2 (min 1 (1 / (3 * κ)))
    have := min_le_left (1 : ℝ) (1 / (3 * κ))
    linarith
  have hρ4 : 3 * κ * ρ ≤ 1 := by
    have := min_le_right δ2 (min 1 (1 / (3 * κ)))
    have := min_le_right (1 : ℝ) (1 / (3 * κ))
    have h5 : ρ ≤ 1 / (3 * κ) := by linarith
    rwa [le_div_iff₀ (by positivity), mul_comm] at h5
  refine ⟨ρ, hρ0, fun z hz1 hz2 => ?_⟩
  set w := s * z with hw
  have hzw : z = s * w := by rw [hw, ← mul_assoc, hs, one_mul]
  have habs : |z| = w := by rw [hzw, abs_mul, hsa, one_mul, abs_of_pos hz1]
  have hb := abs_le.mp (hP z (by rw [habs]; linarith))
  rw [habs] at hb
  have hzm : s * (c * z ^ m) = -κ * w ^ m := by
    rw [hzw, mul_pow, hκdef, pow_succ]
    ring
  have hwm : w ^ m ≤ w * w := by
    have h1 : w ^ m = w * w ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ hz1.le
    calc w ^ (m - 1) ≤ w ^ 1 := pow_le_pow_of_le_one hz1.le (by linarith) (by omega)
      _ = w := pow_one w
  have hwκ : 3 * κ * w ≤ 1 := by nlinarith
  have hpos : 0 ≤ w ^ m := by positivity
  have hsg : s * G z = w + s * (c * z ^ m) + s * (G z - z - c * z ^ m) := by
    rw [hw]
    ring
  have hsf : |s * (G z - z - c * z ^ m)| = |G z - z - c * z ^ m| := by
    rw [abs_mul, hsa, one_mul]
  have hsf' := abs_le.mp (show |s * (G z - z - c * z ^ m)| ≤ κ / 2 * w ^ m by
    rw [hsf]
    exact abs_le.mpr hb)
  rw [hzm] at hsg
  constructor
  · nlinarith
  · nlinarith

set_option maxHeartbeats 800000 in
-- the proof assembles the one-sided invariant set and the two date-1 values explicitly
/-- **Random sunspots from an attracting side** (Woodford (2003), App. A.3, pp. 632–634): if
`g(0) = 0`, `g'(0) = σ`, `σ² = 1`, and `g(g(x)) = x + c xᵐ + o(xᵐ)` with `m ≥ 2` and
`c sᵐ⁺¹ < 0` for a sign `s` (so `g ∘ g` pulls the side `s·x > 0` towards the steady state), then
the scalar forward system has random sunspots at every scale on the coin tree. -/
theorem coinSunspots_of_side {g : ℝ → ℝ} {σ c s : ℝ} {m : ℕ} (hσ : σ * σ = 1) (hg0 : g 0 = 0)
    (hd : HasDerivAt g σ 0) (hs : s * s = 1) (hm : 2 ≤ m) (hcs : c * s ^ (m + 1) < 0)
    (hG : (fun x => g (g x) - x - c * x ^ m) =o[𝓝 0] fun x => x ^ m) : CoinSunspots g := by
  intro ε hε
  obtain ⟨δ1, hδ1, hL⟩ := near_lip hσ hg0 hd
  obtain ⟨ρ1, hρ1, hside1⟩ := side_estimate hs hm hcs hG
  have hsa : |s| = 1 := by nlinarith [abs_mul_abs_self s, abs_nonneg s]
  set ρ := min δ1 ρ1 / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρδ : ρ < δ1 := by have := min_le_left δ1 ρ1; linarith
  have hρρ : ρ ≤ ρ1 := by have := min_le_right δ1 ρ1; linarith
  have hside : ∀ z, 0 < s * z → s * z ≤ ρ → 0 < s * g (g z) ∧ s * g (g z) ≤ s * z :=
    fun z h1 h2 => hside1 z h1 (h2.trans hρρ)
  set A : Set (Fin 1 → ℝ) := {v | 0 < s * v 0 ∧ s * v 0 ≤ ρ} with hA
  have hAnorm : ∀ v ∈ A, ‖v‖ = s * v 0 := by
    intro v hv
    rw [norm_fin1]
    have : |s * v 0| = |v 0| := by rw [abs_mul, hsa, one_mul]
    rw [← this, abs_of_pos hv.1]
  have hAinv : ∀ v ∈ A, lift g (lift g v) ∈ A ∧ ‖lift g (lift g v)‖ ≤ ‖v‖ := by
    intro v hv
    obtain ⟨h1, h2⟩ := hside (v 0) hv.1 hv.2
    have hmem : lift g (lift g v) ∈ A := ⟨h1, h2.trans hv.2⟩
    refine ⟨hmem, ?_⟩
    rw [hAnorm _ hmem, hAnorm _ hv]
    exact h2
  have hAL : ∀ v ∈ A, ‖lift g v‖ ≤ 2 * ‖v‖ := by
    intro v hv
    rw [norm_fin1, norm_fin1]
    have hv0 : |v 0| < δ1 := by
      have : |s * v 0| = |v 0| := by rw [abs_mul, hsa, one_mul]
      rw [← this, abs_of_pos hv.1]
      linarith [hv.2]
    exact (hL _ hv0).2
  -- the two date-1 values
  set w0 := min (2 / 3 * ρ) (ε / 3) with hw0
  have hw00 : 0 < w0 := lt_min (by positivity) (by positivity)
  set y : Fin 1 → ℝ := fun _ => s * w0 with hy
  have hsy : s * (s * w0) = w0 := by rw [← mul_assoc, hs, one_mul]
  have hw0ρ : w0 ≤ 2 / 3 * ρ := min_le_left _ _
  have hyA : y ∈ A := ⟨by change 0 < s * (s * w0); rw [hsy]; exact hw00,
    by change s * (s * w0) ≤ ρ; rw [hsy]; linarith⟩
  have hy0 : y 0 = s * w0 := rfl
  obtain ⟨hG1, hG2⟩ := hside (s * w0) (by rw [hsy]; exact hw00) (by rw [hsy]; linarith)
  rw [hsy] at hG2
  set Gy := g (g (s * w0)) with hGy
  have hy1 : (fun _ => (3 / 2 : ℝ) * Gy : Fin 1 → ℝ) ∈ A := by
    refine ⟨by simp only; nlinarith, ?_⟩
    simp only
    have := min_le_left (2 / 3 * ρ) (ε / 3)
    nlinarith
  have hy2 : (fun _ => (1 / 2 : ℝ) * Gy : Fin 1 → ℝ) ∈ A := by
    refine ⟨by simp only; nlinarith, ?_⟩
    simp only
    have := min_le_left (2 / 3 * ρ) (ε / 3)
    nlinarith
  have hGy0 : Gy ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hG1
    exact lt_irrefl _ hG1
  have hne : (fun _ => (3 / 2 : ℝ) * Gy : Fin 1 → ℝ) ≠ fun _ => (1 / 2 : ℝ) * Gy := by
    intro h
    have := congrFun h 0
    apply hGy0
    linarith
  have hc : lift g (lift g y) = (1 / 2 : ℝ) •
      ((fun _ => (3 / 2 : ℝ) * Gy : Fin 1 → ℝ) + fun _ => (1 / 2 : ℝ) * Gy) := by
    funext i
    simp only [lift, Pi.smul_apply, Pi.add_apply, smul_eq_mul, hy, hGy]
    ring
  obtain ⟨x, hx, hxn, hxr⟩ := coin_sunspot_of_pair (by norm_num : (1 : ℝ) ≤ 2) hAinv hAL hy1 hy2
    hne hc
  refine ⟨x, hx, hxn.trans ?_, hxr⟩
  have hyn : ‖y‖ = w0 := by rw [hAnorm _ hyA, hy0, hsy]
  have hly : ‖lift g y‖ ≤ 2 * w0 := by rw [← hyn]; exact hAL _ hyA
  have hn1 : ‖(fun _ => (3 / 2 : ℝ) * Gy : Fin 1 → ℝ)‖ ≤ 3 / 2 * w0 := by
    rw [hAnorm _ hy1]
    nlinarith
  have hn2 : ‖(fun _ => (1 / 2 : ℝ) * Gy : Fin 1 → ℝ)‖ ≤ 3 / 2 * w0 := by
    rw [hAnorm _ hy2]
    nlinarith
  have hwε : w0 ≤ ε / 3 := min_le_right _ _
  refine max_le (hly.trans (by linarith)) ?_
  have := max_le hn1 hn2
  nlinarith

/-- **No random sunspots when `g ∘ g` repels at odd order** (Woodford (2003), App. A.3,
pp. 632–634): if `g(0) = 0`, `g'(0) = σ`, `σ² = 1`, and `g(g(x)) = x + c xᵐ + o(xᵐ)` with
`c > 0` and `m` odd, the coin tree has no random sunspots near the steady state. -/
theorem not_coinSunspots_of_repel {g : ℝ → ℝ} {σ c : ℝ} {m : ℕ} (hσ : σ * σ = 1)
    (hg0 : g 0 = 0) (hd : HasDerivAt g σ 0) (hc : 0 < c) (hodd : Odd m)
    (hG : (fun x => g (g x) - x - c * x ^ m) =o[𝓝 0] fun x => x ^ m) : ¬ CoinSunspots g := by
  obtain ⟨δ1, hδ1, hL⟩ := near_lip hσ hg0 hd
  obtain ⟨δ2, hδ2, hP⟩ := lower_of_expansion hc hodd hG
  set r := min δ1 δ2 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < δ1 := by have := min_le_left δ1 δ2; linarith
  have hr2 : r < δ2 := by have := min_le_right δ1 δ2; linarith
  have hrep : RepelAnn (lift g ∘ lift g) r := by
    rw [lift_comp]
    exact repelAnn_lift (half_pos hc) fun z hz => hP z (by linarith)
  have hz : ∀ v : Fin 1 → ℝ, ‖v‖ ≤ r → lift g v = 0 → v = 0 := by
    intro v hv h0
    rw [norm_fin1] at hv
    have h1 := (hL (v 0) (by linarith)).1
    have h2 : g (v 0) = 0 := congrFun h0 0
    rw [h2, abs_zero] at h1
    funext i
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
    have : |v 0| ≤ 0 := by linarith
    exact abs_nonpos_iff.mp this
  exact no_coin_sunspot_of_two_step hr0 hrep hz

/-- **The leading-coefficient criterion on a one-dimensional critical direction** (Woodford
(2003), App. A.3, pp. 632–634; both directions): let `g(0) = 0`, `g'(0) = σ` with `σ = ±1`, and
`g(g(x)) = x + c xᵐ + o(xᵐ)` with `c ≠ 0`, `m ≥ 2`. Then the scalar forward system
`E_t[x_{t+1} − g(x_t)] = 0` has random sunspot equilibria at every scale on the coin tree **iff
`c < 0` or `m` is even**. -/
theorem coin_sunspots_iff {g : ℝ → ℝ} {σ c : ℝ} {m : ℕ} (hσ : σ * σ = 1) (hg0 : g 0 = 0)
    (hd : HasDerivAt g σ 0) (hm : 2 ≤ m) (hc : c ≠ 0)
    (hG : (fun x => g (g x) - x - c * x ^ m) =o[𝓝 0] fun x => x ^ m) :
    CoinSunspots g ↔ (c < 0 ∨ Even m) := by
  constructor
  · intro hsun
    by_contra hno
    push Not at hno
    obtain ⟨hc0, hev⟩ := hno
    have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hc)
    exact not_coinSunspots_of_repel hσ hg0 hd hcpos (Nat.not_even_iff_odd.mp hev) hG hsun
  · rintro (hneg | hev)
    · exact coinSunspots_of_side hσ hg0 hd (by norm_num : (1 : ℝ) * 1 = 1) hm
        (by rw [one_pow, mul_one]; exact hneg) hG
    · rcases lt_or_gt_of_ne hc with hneg | hpos
      · exact coinSunspots_of_side hσ hg0 hd (by norm_num : (1 : ℝ) * 1 = 1) hm
          (by rw [one_pow, mul_one]; exact hneg) hG
      · refine coinSunspots_of_side hσ hg0 hd (by norm_num : (-1 : ℝ) * -1 = 1) hm ?_ hG
        rw [hev.add_one.neg_one_pow]
        linarith

/-! ### One-step repulsion: uniqueness under every informationally closed system -/

/-- **No sunspots under any informationally closed expectation system** (Woodford (2003),
App. A.3, pp. 632–634): if `g(x) = σx + c xᵏ + o(xᵏ)` with `σ² = 1`, `k` odd and `σc > 0`
(`g` itself pushes away from the steady state), there is `r > 0` such that under **every**
informationally closed expectation system (perfect foresight, every finite tree) the steady state
is the only bounded adapted equilibrium within `r` of it, for every `(x_{−1}, e)`. -/
theorem unique_of_one_step {g : ℝ → ℝ} {σ c : ℝ} {k : ℕ} (hσ : σ * σ = 1) (hodd : Odd k)
    (hsc : 0 < σ * c) (hg : (fun x => g x - σ * x - c * x ^ k) =o[𝓝 0] fun x => x ^ k) :
    ∃ r > 0, ∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω), LocalIFTStochastic.Ops.InfoClosed 𝔼 →
      ∀ (u : ParS (Fin 1) ℝ Ω) (x : SProcV (Fin 1) Ω), SolvesSV 𝔼 (Gfwd (lift g)) u x →
        ‖x‖ ≤ r → x = 0 := by
  have hF : (fun x => σ * g x - x - (σ * c) * x ^ k) =o[𝓝 0] fun x => x ^ k := by
    refine (hg.const_mul_left σ).congr_left fun x => ?_
    linear_combination (-x) * hσ
  obtain ⟨δ, hδ, hP⟩ := lower_of_expansion hsc hodd hF
  have hs : |σ| = 1 := by nlinarith [abs_mul_abs_self σ, abs_nonneg σ]
  refine ⟨δ / 2, half_pos hδ, fun 𝔼 hcl u x hx hxr => ?_⟩
  refine unique_of_repelAnn hcl (repelAnn_lift (m := k) (half_pos hsc) fun z hz => ?_) hx hxr
  have := hP z (by linarith)
  rwa [abs_mul, hs, one_mul] at this

/-! ### The unit root and the flip root -/

/-- **Unit root: the criterion in the leading coefficient of `g`** (Woodford (2003), App. A.3,
pp. 632–634; both directions): for `E_t x_{t+1} = g(x_t)` with `g(x) = x + c xᵏ + o(xᵏ)`,
`c ≠ 0`, `k ≥ 2` (operator (A.8) `v_{t+1} − v_t`, as for `SunspotsNotOntoExamples.Gatt`): random
sunspots exist at every scale on the coin tree **iff `c < 0` or `k` is even**; and when `c > 0`,
`k` odd, the
steady state is the only nearby equilibrium under every informationally closed expectation
system. -/
theorem unit_root_criterion {g : ℝ → ℝ} {c : ℝ} {k : ℕ} (hk : 2 ≤ k) (hc : c ≠ 0)
    (hg : (fun x => g x - x - c * x ^ k) =o[𝓝 0] fun x => x ^ k) :
    (CoinSunspots g ↔ (c < 0 ∨ Even k)) ∧
    (0 < c → Odd k → ∃ r > 0, ∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω),
      LocalIFTStochastic.Ops.InfoClosed 𝔼 → ∀ (u : ParS (Fin 1) ℝ Ω) (x : SProcV (Fin 1) Ω),
        SolvesSV 𝔼 (Gfwd (lift g)) u x → ‖x‖ ≤ r → x = 0) := by
  have hg' : (fun x => g x - 1 * x - c * x ^ k) =o[𝓝 0] fun x => x ^ k := by
    simpa only [one_mul] using hg
  obtain ⟨hg0, hd⟩ := hasDerivAt_of_expansion hk hg'
  have hG := comp_expansion (by norm_num : (1 : ℝ) * 1 = 1) hk hg'
  simp only [one_pow] at hG
  refine ⟨?_, fun hc0 hodd => unique_of_one_step (by norm_num) hodd (by linarith) hg'⟩
  rw [coin_sunspots_iff (by norm_num) hg0 hd hk (by intro h; apply hc; linarith) hG]
  have e : c * (1 + 1) < 0 ↔ c < 0 := by constructor <;> intro h <;> linarith
  rw [e]

/-- **Flip root, odd order: the criterion with the opposite sign** (Woodford (2003), App. A.3,
pp. 632–634; both directions): for `g(x) = −x + c xᵏ + o(xᵏ)` with `k ≥ 2` odd, `c ≠ 0`
(operator (A.8) `v_{t+1} + v_t`, root `−1`): random sunspots exist at every scale on the coin
tree **iff `c > 0`**; when `c < 0` the steady state is the only nearby equilibrium under every
informationally closed expectation system. -/
theorem flip_root_criterion {g : ℝ → ℝ} {c : ℝ} {k : ℕ} (hk : 2 ≤ k) (hodd : Odd k)
    (hc : c ≠ 0) (hg : (fun x => g x + x - c * x ^ k) =o[𝓝 0] fun x => x ^ k) :
    (CoinSunspots g ↔ 0 < c) ∧
    (c < 0 → ∃ r > 0, ∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω),
      LocalIFTStochastic.Ops.InfoClosed 𝔼 → ∀ (u : ParS (Fin 1) ℝ Ω) (x : SProcV (Fin 1) Ω),
        SolvesSV 𝔼 (Gfwd (lift g)) u x → ‖x‖ ≤ r → x = 0) := by
  have hg' : (fun x => g x - (-1) * x - c * x ^ k) =o[𝓝 0] fun x => x ^ k := by
    refine hg.congr_left fun x => ?_
    ring
  obtain ⟨hg0, hd⟩ := hasDerivAt_of_expansion hk hg'
  have hG := comp_expansion (by norm_num : (-1 : ℝ) * -1 = 1) hk hg'
  simp only [hodd.neg_one_pow] at hG
  refine ⟨?_, fun hc0 => unique_of_one_step (by norm_num) hodd (by linarith) hg'⟩
  rw [coin_sunspots_iff (by norm_num) hg0 hd hk (by intro h; apply hc; linarith) hG]
  have hne : ¬ Even k := Nat.not_even_iff_odd.mpr hodd
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hne
  · intro h
    left
    linarith

/-- Woodford (2003), App. A.3, p. 632 (example): the flip-root map `g₁(x) = −x + x²`. -/
def gFlipA (x : ℝ) : ℝ := -x + x ^ 2

/-- Woodford (2003), App. A.3, p. 632 (example): the flip-root map `g₂(x) = −x + x² − 2x³`, with
the same `σ = −1`, `k = 2` and leading coefficient `c = 1` as `gFlipA`. -/
def gFlipB (x : ℝ) : ℝ := -x + x ^ 2 - 2 * x ^ 3

/-- **At a flip root of even order the leading coefficient of `g` does not decide** (Woodford
(2003), App. A.3, pp. 632–634; the criterion cannot be stated for `g` itself): `g₁ = −x + x²` and
`g₂ = −x + x² − 2x³` both have the expansion `−x + 1·x² + o(x²)`, yet `g₁` has random sunspots at
every scale on the coin tree (`g₁(g₁(x)) = x − 2x³ + x⁴`) and `g₂` has none
(`g₂(g₂(x)) = x + 2x³ + O(x⁴)`): the order-2 terms cancel in `g ∘ g`, whose leading coefficient
decides (`coin_sunspots_iff`). -/
theorem flip_even_undecided :
    ((fun x => gFlipA x - (-1) * x - 1 * x ^ 2) =o[𝓝 0] fun x => x ^ 2) ∧
    ((fun x => gFlipB x - (-1) * x - 1 * x ^ 2) =o[𝓝 0] fun x => x ^ 2) ∧
    CoinSunspots gFlipA ∧ ¬ CoinSunspots gFlipB := by
  have hA : (fun x => gFlipA x - (-1) * x - 1 * x ^ 2) =o[𝓝 0] fun x => x ^ 2 :=
    (isLittleO_zero (fun x : ℝ => x ^ 2) (𝓝 0)).congr_left fun x => by simp only [gFlipA]; ring
  have hB : (fun x => gFlipB x - (-1) * x - 1 * x ^ 2) =o[𝓝 0] fun x => x ^ 2 :=
    ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by norm_num)).const_mul_left (-2)).congr_left
      fun x => by simp only [gFlipB]; ring
  obtain ⟨hA0, hAd⟩ := hasDerivAt_of_expansion le_rfl hA
  obtain ⟨hB0, hBd⟩ := hasDerivAt_of_expansion le_rfl hB
  have hGA : (fun x => gFlipA (gFlipA x) - x - (-2) * x ^ 3) =o[𝓝 0] fun x => x ^ 3 :=
    (isLittleO_pow_pow (𝕜 := ℝ) (show 3 < 4 by norm_num)).congr_left
      fun x => by simp only [gFlipA]; ring
  have hp : ∀ j : ℕ, 3 < j → ∀ a : ℝ, (fun x : ℝ => a * x ^ j) =o[𝓝 0] fun x => x ^ 3 :=
    fun j hj a => (isLittleO_pow_pow (𝕜 := ℝ) hj).const_mul_left a
  have hGB : (fun x => gFlipB (gFlipB x) - x - 2 * x ^ 3) =o[𝓝 0] fun x => x ^ 3 := by
    have h := (((((hp 4 (by norm_num) (-1)).add (hp 5 (by norm_num) 14)).add
      (hp 6 (by norm_num) (-22))).add (hp 7 (by norm_num) 36)).add
      (hp 8 (by norm_num) (-24))).add (hp 9 (by norm_num) 16)
    refine h.congr_left fun x => ?_
    simp only [gFlipB]
    ring
  refine ⟨hA, hB, ?_, ?_⟩
  · exact (coin_sunspots_iff (by norm_num) hA0 hAd (by norm_num) (by norm_num) hGA).mpr
      (Or.inl (by norm_num))
  · exact not_coinSunspots_of_repel (by norm_num) hB0 hBd (by norm_num : (0 : ℝ) < 2)
      (by decide) hGB

/-! ### A flat perturbation: no criterion in the Taylor jet -/

/-- Woodford (2003), App. A.3, p. 632 (example): the flat odd function `f(x) = ψ(x) − ψ(−x)`,
with `ψ` Mathlib's `expNegInvGlue` (`ψ(x) = e^{−1/x}` for `x > 0`, `0` otherwise): all its
derivatives vanish at `0`, yet `f(x) > 0` for `x > 0`. -/
noncomputable def fl : ℝ → ℝ := expNegInvGlue - fun x => expNegInvGlue (-x)

/-- Woodford (2003), App. A.3, p. 632 (example): the attracting flat perturbation of the unit
root, `gm(x) = x − f(x)`. -/
noncomputable def gm (x : ℝ) : ℝ := x - fl x

/-- Woodford (2003), App. A.3, p. 632 (example): the repelling flat perturbation of the unit
root, `gp(x) = x + f(x)`. -/
noncomputable def gp (x : ℝ) : ℝ := x + fl x

/-- Woodford (2003), App. A.3, p. 632 (tool): `ψ(y) ≤ y` and `ψ(y) ≤ 2y²` for `y ≥ 0`. -/
theorem glue_le {y : ℝ} (hy : 0 ≤ y) : expNegInvGlue y ≤ y ∧ expNegInvGlue y ≤ 2 * y ^ 2 := by
  rcases hy.eq_or_lt with h0 | hpos
  · rw [← h0, expNegInvGlue.zero]
    norm_num
  have he : expNegInvGlue y = (Real.exp y⁻¹)⁻¹ := by
    simp only [expNegInvGlue, not_le.mpr hpos, ↓reduceIte, Real.exp_neg]
  have hi : 0 < y⁻¹ := inv_pos.mpr hpos
  rw [he]
  constructor
  · have h1 : y⁻¹ ≤ Real.exp y⁻¹ := by linarith [Real.add_one_le_exp y⁻¹]
    have := inv_anti₀ hi h1
    rwa [inv_inv] at this
  · have h1 : y⁻¹ ^ 2 / 2 ≤ Real.exp y⁻¹ := by
      have := Real.pow_div_factorial_le_exp y⁻¹ hi.le 2
      simpa using this
    have h2 : 0 < y⁻¹ ^ 2 / 2 := by positivity
    have := inv_anti₀ h2 h1
    have e : (y⁻¹ ^ 2 / 2)⁻¹ = 2 * y ^ 2 := by field_simp
    rwa [e] at this

/-- Woodford (2003), App. A.3, p. 632 (tool): `f(x) = ψ(x)` for `x ≥ 0` and `f(x) = −ψ(−x)` for
`x ≤ 0`. -/
theorem fl_cases (x : ℝ) : (0 ≤ x → fl x = expNegInvGlue x) ∧
    (x ≤ 0 → fl x = -expNegInvGlue (-x)) := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · change expNegInvGlue x - expNegInvGlue (-x) = _
    rw [expNegInvGlue.zero_of_nonpos (by linarith : -x ≤ 0), sub_zero]
  · change expNegInvGlue x - expNegInvGlue (-x) = _
    rw [expNegInvGlue.zero_of_nonpos hx, zero_sub]

/-- Woodford (2003), App. A.3, p. 632 (example): `|gp(x)| = |x| + ψ(|x|)` (repelling) and
`|gm(x)| ≤ |x|` (attracting), for every `x`. -/
theorem abs_gp_gm (x : ℝ) : |gp x| = |x| + expNegInvGlue |x| ∧ |gm x| ≤ |x| := by
  rcases le_or_gt 0 x with hx | hx
  · have h1 := (fl_cases x).1 hx
    have h2 := glue_le hx
    have h3 := expNegInvGlue.nonneg x
    rw [abs_of_nonneg hx]
    refine ⟨?_, ?_⟩
    · rw [gp, h1, abs_of_nonneg (by linarith)]
    · rw [gm, h1, abs_of_nonneg (by linarith)]
      linarith
  · have h1 := (fl_cases x).2 hx.le
    have h2 := glue_le (by linarith : 0 ≤ -x)
    have h3 := expNegInvGlue.nonneg (-x)
    rw [abs_of_neg hx]
    refine ⟨?_, ?_⟩
    · rw [gp, h1, abs_of_neg (by linarith)]
      ring
    · rw [gm, h1, abs_of_nonpos (by linarith)]
      linarith

/-- Woodford (2003), App. A.3, p. 632 (tool): `f` is `C^∞`. -/
theorem contDiff_fl (k : ℕ) : ContDiff ℝ k fl :=
  (expNegInvGlue.contDiff (n := k)).sub ((expNegInvGlue.contDiff (n := k)).comp contDiff_neg)

/-- Woodford (2003), App. A.3, p. 632 (tool): a `C^∞` function vanishing on an open set whose
closure contains `0` has all derivatives zero at `0`. -/
theorem flat_of_eqOn {F : ℝ → ℝ} (hF : ∀ k : ℕ, ContDiff ℝ k F) {S : Set ℝ} (hS : IsOpen S)
    (h0 : ∀ x ∈ S, F x = 0) (hcl : (0 : ℝ) ∈ closure S) (n : ℕ) :
    iteratedFDeriv ℝ n F 0 = 0 := by
  have hc : Continuous fun x => iteratedFDeriv ℝ n F x :=
    (hF n).continuous_iteratedFDeriv le_rfl
  have hsub : S ⊆ {x | iteratedFDeriv ℝ n F x = 0} := by
    intro x hx
    have hev : F =ᶠ[𝓝 x] fun _ => 0 := Filter.eventually_of_mem (hS.mem_nhds hx) h0
    have e := (hev.iteratedFDeriv ℝ n).eq_of_nhds
    change iteratedFDeriv ℝ n F x = 0
    rw [e, iteratedFDeriv_fun_zero]
    rfl
  exact (isClosed_eq hc continuous_const).closure_subset_iff.mpr hsub hcl

/-- Woodford (2003), App. A.3, p. 632 (example): **`f` is flat at `0`**: all its derivatives
vanish there. -/
theorem fl_flat (n : ℕ) : iteratedFDeriv ℝ n fl 0 = 0 := by
  have h1 : iteratedFDeriv ℝ n expNegInvGlue 0 = 0 :=
    flat_of_eqOn (fun k => expNegInvGlue.contDiff (n := k)) isOpen_Iio
      (fun x hx => expNegInvGlue.zero_of_nonpos (le_of_lt hx))
      (by rw [closure_Iio]; exact Set.mem_Iic.mpr le_rfl) n
  have h2 : iteratedFDeriv ℝ n (fun x => expNegInvGlue (-x)) 0 = 0 :=
    flat_of_eqOn (fun k => (expNegInvGlue.contDiff (n := k)).comp contDiff_neg) isOpen_Ioi
      (fun x hx => by
        have hx' : 0 < x := hx
        change expNegInvGlue (-x) = 0
        exact expNegInvGlue.zero_of_nonpos (by linarith))
      (by rw [closure_Ioi]; exact Set.mem_Ici.mpr le_rfl) n
  change iteratedFDeriv ℝ n (expNegInvGlue - fun x => expNegInvGlue (-x)) 0 = 0
  rw [iteratedFDeriv_sub_apply (f := expNegInvGlue) (g := fun x => expNegInvGlue (-x))
    ((expNegInvGlue.contDiff (n := n)).contDiffAt)
    (((expNegInvGlue.contDiff (n := n)).comp contDiff_neg).contDiffAt), h1, h2, sub_zero]

/-- Woodford (2003), App. A.3, p. 632 (tool): `f` has derivative `0` at `0` (`|f(x)| ≤ 2x²`). -/
theorem hasDerivAt_fl : HasDerivAt fl 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hf0 : fl 0 = 0 := by rw [(fl_cases 0).1 le_rfl, expNegInvGlue.zero]
  have hO : fl =O[𝓝 0] fun x => x ^ 2 := by
    refine IsBigO.of_bound 2 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq_abs]
    rcases le_or_gt 0 x with hx | hx
    · rw [(fl_cases x).1 hx, abs_of_nonneg (expNegInvGlue.nonneg x)]
      exact (glue_le hx).2
    · rw [(fl_cases x).2 hx.le, abs_neg, abs_of_nonneg (expNegInvGlue.nonneg _)]
      have := (glue_le (by linarith : 0 ≤ -x)).2
      rwa [neg_sq] at this
  have h := hO.trans_isLittleO (isLittleO_pow_pow (𝕜 := ℝ) (show 1 < 2 by norm_num))
  refine (h.congr_left fun x => ?_).congr_right fun x => pow_one x
  simp only [zero_add, hf0, sub_zero, smul_zero]

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (tool): for a scalar map with `g'(0) = σ`, the
derivative of `x_{t+1} − g(x_t)` at the steady state is `x_{t+1} − σ x_t`. -/
theorem fderiv_Gfwd_lift {g : ℝ → ℝ} {σ : ℝ} (hd : HasDerivAt g σ 0)
    (p : Arg (Fin 1) ℝ) :
    fderiv ℝ (Gfwd (lift g)) 0 p =
      fun _ => 0 * p.1 0 + (-σ) * p.2.1 0 + 1 * p.2.2.1 0 + 0 * p.2.2.2 := by
  have hB : HasFDerivAt (LocalIFTSystems.projB : Arg (Fin 1) ℝ → ℝ) LocalIFTSystems.projB 0 :=
    LocalIFTSystems.projB.hasFDerivAt
  have hC : HasFDerivAt (SunspotsNotOntoExamples.pC : Arg (Fin 1) ℝ → ℝ)
      SunspotsNotOntoExamples.pC 0 := SunspotsNotOntoExamples.pC.hasFDerivAt
  have hd' : HasDerivAt g σ (LocalIFTSystems.projB (0 : Arg (Fin 1) ℝ)) := by
    rw [map_zero]
    exact hd
  have hgB := hd'.comp_hasFDerivAt (0 : Arg (Fin 1) ℝ) hB
  have h : HasFDerivAt (Gfwd (lift g)) (ContinuousLinearMap.pi fun _ : Fin 1 =>
      SunspotsNotOntoExamples.pC - σ • LocalIFTSystems.projB) 0 := by
    refine hasFDerivAt_pi'' fun i => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact hC.sub hgB
  rw [h.fderiv]
  funext i
  simp [LocalIFTSystems.projB, SunspotsNotOntoExamples.pC]
  ring

/-- **A flat perturbation decides the opposite way: no criterion in the Taylor jet**
(Woodford (2003), App. A.3, pp. 632–634; the hypothesis `c ≠ 0` of `unit_root_criterion` cannot
be dropped): `gp(x) = x + f(x)` and `gm(x) = x − f(x)` with `f` flat are `C^∞`, have **equal
derivatives of every order** at the steady state and the **same operator (A.8)** as
`SunspotsNotOntoExamples.Gatt` (`v_{t+1} − v_t`), yet `gm` has random sunspots at every scale
on the coin tree while under every
informationally closed expectation system the steady state is the **only** bounded equilibrium
of `gp`, for every `(x_{−1}, e)`. -/
theorem flat_undecided :
    (∀ k : ℕ, ContDiff ℝ k gp ∧ ContDiff ℝ k gm) ∧
    (∀ n : ℕ, iteratedFDeriv ℝ n gp 0 = iteratedFDeriv ℝ n gm 0) ∧
    linOp (Gfwd (lift gp)) = linOp SunspotsNotOntoExamples.Gatt ∧
    linOp (Gfwd (lift gm)) = linOp SunspotsNotOntoExamples.Gatt ∧
    CoinSunspots gm ∧
    (∀ {Ω : Type*} (𝔼 : ExpectationSystem Ω), LocalIFTStochastic.Ops.InfoClosed 𝔼 →
      ∀ (u : ParS (Fin 1) ℝ Ω) (x : SProcV (Fin 1) Ω), SolvesSV 𝔼 (Gfwd (lift gp)) u x →
        x = 0) := by
  have hid : ∀ k : ℕ, ContDiff ℝ k fun x : ℝ => x := fun k => contDiff_id
  have hcp : ∀ k : ℕ, ContDiff ℝ k gp := fun k => (hid k).add (contDiff_fl k)
  have hcm : ∀ k : ℕ, ContDiff ℝ k gm := fun k => (hid k).sub (contDiff_fl k)
  have hf0 : fl 0 = 0 := by rw [(fl_cases 0).1 le_rfl, expNegInvGlue.zero]
  have hm0 : gm 0 = 0 := by rw [gm, hf0, sub_zero]
  have hpd : HasDerivAt gp 1 0 := by
    have := (hasDerivAt_id' (x := (0 : ℝ))).add hasDerivAt_fl
    rw [add_zero] at this
    exact this
  have hmd : HasDerivAt gm 1 0 := by
    have := (hasDerivAt_id' (x := (0 : ℝ))).sub hasDerivAt_fl
    rw [sub_zero] at this
    exact this
  have hlin : ∀ g : ℝ → ℝ, HasDerivAt g 1 0 →
      linOp (Gfwd (lift g)) = linOp SunspotsNotOntoExamples.Gatt := by
    intro g hd
    have hA := fun v t => SunspotsNotOntoExamples.linOp_of_fderiv
      (fun p => (fderiv_Gfwd_lift hd p)) v t
    have hR := SunspotsNotOntoExamples.linOp_Gatt_Grep.2
    refine ContinuousLinearMap.ext fun v => seq_ext fun t => ?_
    rw [hA, hR]
  refine ⟨fun k => ⟨hcp k, hcm k⟩, fun n => ?_, hlin gp hpd, hlin gm hmd, ?_, ?_⟩
  · change iteratedFDeriv ℝ n ((fun x : ℝ => x) + fl) 0 =
      iteratedFDeriv ℝ n ((fun x : ℝ => x) - fl) 0
    rw [iteratedFDeriv_add_apply ((hid n).contDiffAt) ((contDiff_fl n).contDiffAt),
      iteratedFDeriv_sub_apply ((hid n).contDiffAt) ((contDiff_fl n).contDiffAt), fl_flat,
      add_zero, sub_zero]
  · intro ε hε
    have hA : ∀ v ∈ (Set.univ : Set (Fin 1 → ℝ)),
        lift gm (lift gm v) ∈ Set.univ ∧ ‖lift gm (lift gm v)‖ ≤ ‖v‖ := by
      intro v _
      refine ⟨Set.mem_univ _, ?_⟩
      rw [norm_fin1, norm_fin1]
      exact (abs_gp_gm _).2.trans (abs_gp_gm _).2
    have hL : ∀ v ∈ (Set.univ : Set (Fin 1 → ℝ)), ‖lift gm v‖ ≤ 1 * ‖v‖ := by
      intro v _
      rw [norm_fin1, norm_fin1, one_mul]
      exact (abs_gp_gm _).2
    have hne : (fun _ => ε : Fin 1 → ℝ) ≠ fun _ => -ε := by
      intro h
      have := congrFun h 0
      linarith
    have hc : lift gm 0 = (1 / 2 : ℝ) • ((fun _ => ε : Fin 1 → ℝ) + fun _ => -ε) := by
      funext i
      simp [lift, hm0]
    obtain ⟨x, hx, hxn, hxr⟩ := coin_sunspot_of_pair le_rfl hA hL (Set.mem_univ _)
      (Set.mem_univ _) hne hc
    refine ⟨x, hx, hxn.trans ?_, hxr⟩
    rw [norm_zero, norm_fin1, norm_fin1, one_mul]
    simp only [abs_neg, max_self, abs_of_pos hε]
    exact max_le hε.le le_rfl
  · intro Ω 𝔼 hcl u x hx
    refine unique_of_repelAnn_global hcl (fun r B hB _ => ?_) hx
    refine ⟨expNegInvGlue (B / 2), expNegInvGlue.pos_of_pos (by positivity), fun v hv1 _ => ?_⟩
    rw [norm_fin1] at hv1 ⊢
    rw [show ‖lift gp v‖ = |gp (v 0)| from norm_fin1 _, (abs_gp_gm _).1]
    have := expNegInvGlue.monotone hv1
    linarith

end Woodford.PriceLevelDetermination.TidyR6CriticalCriterion
