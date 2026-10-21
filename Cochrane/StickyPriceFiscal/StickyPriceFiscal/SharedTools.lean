/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.ForwardSolution
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Shared tools for the sticky-price fiscal chapters

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5 (pp. 117–181): general lemmas
that several sections of Chapter 5 use, collected in one place (they were proved independently in
§5.4 (`SurplusProcess`, `ActivePassive`), §5.1.2 (`FiscalNK`) and §5.5 (`PolicyRules`)).

* The innovation operator `ΔE_{t+1} y = E_{t+1} y − E_t y` (`innov`, notation of (5.58), p. 147)
  and its algebra: `innov_apply`, `E_succ_of_adapted`, `innov_known`, `innov_succ`, `innov_add`,
  `innov_smul`, `innov_sub`, `abs_innov_le`, and AR(1) disturbances `E_ar1`, `innov_ar1`
  ((5.61)–(5.62)).
* The transversality condition `ρᵀ E_t x_{t+T} → 0` (`TVC`, p. 136 and p. 121).
* Scalar recursions (pp. 121, 137–138, 149): `bounded_of_rec` (a stable recursion
  `|x_{t+1}| ≤ c|x_t| + F` stays bounded), `summable_of_rec` and `tendsto_zero_of_rec`
  (`w_{k+1} = c w_k + f_k` with `|c| < 1` and summable `f` is summable).
-/

namespace Cochrane.StickyPriceFiscal.SharedTools

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The innovation operator -/

/-- Cochrane (2023), (5.58), p. 147 (notation `ΔE_{t+1}`): the date-`t+1` innovation
`ΔE_{t+1} y = E_{t+1} y − E_t y`. -/
def innov (t : ℕ) (y : Ω → ℝ) : Ω → ℝ := 𝔼.E (t + 1) y - 𝔼.E t y

/-- Cochrane (2023), (5.58), p. 147: pointwise, `ΔE_{t+1} y = E_{t+1} y − E_t y` (this is the
explicit form used in §§5.1–5.4). -/
theorem innov_apply (t : ℕ) (y : Ω → ℝ) (ω : Ω) :
    innov 𝔼 t y ω = 𝔼.E (t + 1) y ω - 𝔼.E t y ω := rfl

/-- Cochrane (2023), p. 148 (tool): an adapted variable is known one period later. -/
theorem E_succ_of_adapted {y : ℕ → Ω → ℝ} (hy : 𝔼.Adapted y) (t : ℕ) :
    𝔼.E (t + 1) (y t) = y t := by
  have := 𝔼.known (Nat.le_succ t) (y t)
  rwa [hy t] at this

/-- Cochrane (2023), p. 148 (tool): a variable known at date `t` has no date-`t+1` innovation. -/
theorem innov_known {y : ℕ → Ω → ℝ} (hy : 𝔼.Adapted y) (t : ℕ) : innov 𝔼 t (y t) = 0 := by
  simp only [innov, E_succ_of_adapted 𝔼 hy t, hy t, sub_self]

/-- Cochrane (2023), p. 148 (tool): the innovation of an adapted variable,
`ΔE_{t+1} y_{t+1} = y_{t+1} − E_t y_{t+1}`. -/
theorem innov_succ {y : ℕ → Ω → ℝ} (hy : 𝔼.Adapted y) (t : ℕ) :
    innov 𝔼 t (y (t + 1)) = y (t + 1) - 𝔼.E t (y (t + 1)) := by
  simp only [innov, hy (t + 1)]

/-- Cochrane (2023), p. 150 (tool): the innovation operator is additive. -/
theorem innov_add (t : ℕ) (a b : Ω → ℝ) : innov 𝔼 t (a + b) = innov 𝔼 t a + innov 𝔼 t b := by
  simp only [innov, map_add]
  abel

/-- Cochrane (2023), p. 150 (tool): the innovation operator is homogeneous. -/
theorem innov_smul (t : ℕ) (c : ℝ) (a : Ω → ℝ) : innov 𝔼 t (c • a) = c • innov 𝔼 t a := by
  simp only [innov, map_smul, smul_sub]

/-- Cochrane (2023), (3.20)–(3.22) (tool): the innovation operator respects subtraction. -/
theorem innov_sub (t : ℕ) (a b : Ω → ℝ) : innov 𝔼 t (a - b) = innov 𝔼 t a - innov 𝔼 t b := by
  simp only [innov, map_sub]
  abel

/-- Cochrane (2023), (3.20)–(3.22) (tool): innovations of a bounded variable are bounded by
twice the bound. -/
theorem abs_innov_le {M : ℝ} {y : Ω → ℝ} (hy : ∀ ω, |y ω| ≤ M) (t : ℕ) (ω : Ω) :
    |innov 𝔼 t y ω| ≤ 2 * M := by
  simp only [innov, Pi.sub_apply]
  have h1 := 𝔼.abs_E_le hy (t + 1) ω
  have h2 := 𝔼.abs_E_le hy t ω
  calc _ ≤ |𝔼.E (t + 1) y ω| + |𝔼.E t y ω| := abs_sub _ _
    _ ≤ 2 * M := by linarith

/-- Cochrane (2023), (5.61)–(5.62), p. 147 (tool): `E_t u_{t+1} = η u_t` for an AR(1)
disturbance driven by unpredictable shocks. -/
theorem E_ar1 {u e : ℕ → Ω → ℝ} {η : ℝ} (hu : 𝔼.Adapted u) (he : ∀ t, 𝔼.E t (e (t + 1)) = 0)
    (hl : ∀ t, u (t + 1) = η • u t + e (t + 1)) (t : ℕ) : 𝔼.E t (u (t + 1)) = η • u t := by
  rw [hl t, map_add, map_smul, hu t, he t, add_zero]

/-- Cochrane (2023), (5.61)–(5.62), p. 147 (tool): the innovation of an AR(1) disturbance is its
shock, `ΔE_{t+1} u_{t+1} = ε_{t+1}`. -/
theorem innov_ar1 {u e : ℕ → Ω → ℝ} {η : ℝ} (hu : 𝔼.Adapted u)
    (he : ∀ t, 𝔼.E t (e (t + 1)) = 0) (hl : ∀ t, u (t + 1) = η • u t + e (t + 1)) (t : ℕ) :
    innov 𝔼 t (u (t + 1)) = e (t + 1) := by
  rw [innov_succ 𝔼 hu, E_ar1 𝔼 hu he hl, hl t]
  abel

/-! ### The transversality condition -/

/-- Cochrane (2023), p. 136 and §5.4.2, p. 140 (the transversality condition): the discounted
forecast `ρᵀ E_t x_{t+T}` vanishes as `T → ∞`, at every date and state. -/
def TVC (ρ : ℝ) (x : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, Tendsto (fun T => ρ ^ T * 𝔼.E t (x (t + T)) ω) atTop (𝓝 0)

/-! ### Scalar recursions -/

/-- Cochrane (2023), pp. 137–138 (debt that does not explode): if
`|x_{t+1}| ≤ c |x_t| + F` with `0 ≤ c < 1` and `|x_0| ≤ V`, then `|x_t| ≤ V + F/(1 − c)`. -/
theorem bounded_of_rec {c F V : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hF : 0 ≤ F) {x : ℕ → ℝ}
    (hx0 : |x 0| ≤ V) (hx : ∀ t, |x (t + 1)| ≤ c * |x t| + F) (t : ℕ) :
    |x t| ≤ V + F / (1 - c) := by
  induction t with
  | zero =>
    have : 0 ≤ F / (1 - c) := div_nonneg hF (by linarith)
    linarith
  | succ t ih =>
    have hV : 0 ≤ V := (abs_nonneg _).trans hx0
    have key : c * (V + F / (1 - c)) + F ≤ V + F / (1 - c) := by
      have h1c : 0 < 1 - c := by linarith
      have : F = (1 - c) * (F / (1 - c)) := by field_simp
      nlinarith
    calc |x (t + 1)| ≤ c * |x t| + F := hx t
      _ ≤ c * (V + F / (1 - c)) + F := by gcongr
      _ ≤ V + F / (1 - c) := key

/-- Cochrane (2023), pp. 137–138 (convergence of the latent debt): if
`w_{k+1} = c w_k + f_k` with `|c| < 1` and `f` summable, then `w` is (absolutely) summable. -/
theorem summable_of_rec {c : ℝ} (hc : |c| < 1) {w f : ℕ → ℝ} (hf : Summable f)
    (hw : ∀ k, w (k + 1) = c * w k + f k) : Summable w := by
  have hfa : Summable (fun k => |f k|) := hf.abs
  set F := ∑' k, |f k| with hF
  have hc0 : 0 < 1 - |c| := by linarith
  have hpart : ∀ N, ∑ k ∈ Finset.range N, |w k| ≤ (|w 0| + F) / (1 - |c|) := by
    intro N
    have hS : ∑ k ∈ Finset.range (N + 1), |w k| ≤
        |w 0| + |c| * ∑ k ∈ Finset.range N, |w k| + ∑ k ∈ Finset.range N, |f k| := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm _ (|w 0|), add_assoc,
        ← Finset.sum_add_distrib]
      gcongr with k hk
      rw [hw k, ← abs_mul]
      exact abs_add_le _ _
    have hle : ∑ k ∈ Finset.range N, |w k| ≤ ∑ k ∈ Finset.range (N + 1), |w k| := by
      rw [Finset.sum_range_succ]
      linarith [abs_nonneg (w N)]
    have hFN : ∑ k ∈ Finset.range N, |f k| ≤ F :=
      hfa.sum_le_tsum (Finset.range N) (fun i _ => abs_nonneg _)
    have habs : 0 ≤ |c| := abs_nonneg c
    rw [le_div_iff₀ hc0]
    nlinarith
  exact (summable_of_sum_range_le (fun n => abs_nonneg _) hpart).of_abs

/-- Cochrane (2023), pp. 137–138: under the hypotheses of `summable_of_rec`, `w_k → 0`. -/
theorem tendsto_zero_of_rec {c : ℝ} (hc : |c| < 1) {w f : ℕ → ℝ} (hf : Summable f)
    (hw : ∀ k, w (k + 1) = c * w k + f k) : Tendsto w atTop (𝓝 0) :=
  (summable_of_rec hc hf hw).tendsto_atTop_zero

end Cochrane.StickyPriceFiscal.SharedTools
