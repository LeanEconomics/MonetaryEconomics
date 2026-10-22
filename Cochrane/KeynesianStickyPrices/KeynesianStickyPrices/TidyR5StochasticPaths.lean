/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TaylorDeterminacy

/-!
# The full-model paths of §17.4 under uncertainty: expected paths and news

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4, eqs.
(17.15)–(17.18), pp. 407–410, Figures 17.5–17.6, and p. 414 (reverse-engineered disturbances).

Figures 17.5–17.6 are drawn under perfect foresight after the announcement or shock. Here is
their content for an arbitrary `ExpectationSystem` (finite event trees included), with no
disturbances in the IS and Phillips curves, as in the figures.

## Expected paths and news

* `expected_pfEqm`: for every equilibrium of (17.15)–(17.17) (`FullModel.Model`), every date
  `s` and state `ω`, the expected paths `j ↦ (E_s i_{s+j}, E_s x_{s+j}, E_s π_{s+j})(ω)` form a
  perfect-foresight equilibrium (`FullModel.PFEqm`). With bounded rates and inflation the
  expected inflation path is therefore the figures' path for the expected rate path, started
  at `E_s π_s` (`expected_path`, through `FullModel.pf_eqm_iff`).
* `news_pfEqm`, `news_path`: the **news** `ΔE_{s+1} = E_{s+1} − E_s` about the whole future
  (`FiscalUnderpinnings.innov`) is itself a perfect-foresight equilibrium:
  `ΔE_{s+1} π_{s+1+j} = path(ΔE_{s+1} i_{s+1+·}, ΔE_{s+1} π_{s+1})(j)` and
  `ΔE_{s+1} x_{s+1+j} = (ΔE_{s+1} π_{s+1+j} − β ΔE_{s+1} π_{s+2+j})/κ`. So the figures are
  impulse responses: the response of expected inflation and output to news about the rate path,
  with the unexpected inflation `ΔE_{s+1} π_{s+1}` free.
* Figure 17.5 under uncertainty (`news_rise`): if the date-`(s+1)` news is a permanent rise of
  expected rates from horizon `T`, the news about inflation is `path(1{· ≥ T}, δ)` with
  `δ = ΔE_{s+1} π_{s+1}`; it converges to one, and at every horizon `j ≥ 1` exceeds the response
  `δ λ₁^{−j}` to the same unexpected inflation without rate news
  (`FullModel.rise_raises_inflation`).
  With `δ` equal to the two-sided value (`news_rise_twoSided`) the news response is exactly the
  solid line `FullModel.antPath`: positive, rising, below one, and output news is negative up
  to and including the date of the rise.

## Figure 17.6 under uncertainty: the equilibrium set

`Factored` is the stochastic form of the factorisation of (17.18), `λ₁ E_t π_{t+1} = π_t + σκ
F_t`, `F_t = ∑ λ₂ᵏ E_t i_{t+k}` (`ExpectationSystem.forwardSeries`). For bounded processes
(adapted rates) (17.18) holds iff `Factored` does (`eq1718_iff_factored`). Hence
(`innov_eqm_existsUnique`): for every bounded adapted rate process, every bounded initial
inflation `p` known at date 0 and **every** bounded adapted inflation-innovation process `δ`
(`E_t δ_{t+1} = 0`) there is exactly one bounded adapted equilibrium with `π_0 = p` and `π_{t+1}
− E_t π_{t+1} = δ_{t+1}` (`piInnov`). The single perfect-foresight jump of Fig. 17.6 becomes one
free innovation at every date: that is the multiplicity fiscal policy selects under uncertainty.

## Reverse-engineered disturbances (p. 414) under uncertainty

For each of these equilibria the disturbance `u = i − φπ` makes it the **unique** bounded
adapted equilibrium of the model with `i_t = φ π_t + u_t` whenever `φ` is in the determinacy
region (`reverse_engineer_innov`), and different innovation processes need different
disturbances for the same rate process (`reverse_engineer_innov_distinct`).

## What has no stochastic content

The statements on `ℤ` (the path anticipated from the infinite past, `FullModel.zPath`, and
FullModelTidy's equilibria on `ℤ`) need expectations at dates before 0; the core
`ExpectationSystem` is indexed by `ℕ`, and pre-announcement expectations "at the steady state"
are a statement about the date before the news, which in the innovation form above is simply
`E_s` itself. Every post-news claim of Figs. 17.5–17.6 is covered by `news_path`.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR5StochasticPaths

open Filter Topology FullModel FiscalUnderpinnings

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Small tools -/

/-- The news `ΔE_{t+1} y` of a variable bounded by `M` is bounded by `2M`. -/
theorem abs_innov_le {M : ℝ} {y : Ω → ℝ} (hy : ∀ ω, |y ω| ≤ M) (t : ℕ) (ω : Ω) :
    |innov 𝔼 t y ω| ≤ 2 * M := by
  unfold innov
  rw [Pi.sub_apply, two_mul]
  exact (abs_sub _ _).trans (add_le_add (𝔼.abs_E_le hy _ ω) (𝔼.abs_E_le hy _ ω))

/-- Cochrane (2023), eq. (5.5): the forward sum is linear, `F(c i) = c F(i)`. -/
theorem F_smul (q c : ℝ) (i : ℕ → ℝ) (t : ℕ) : F q (fun k => c * i k) t = c * F q i t := by
  unfold F
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by ring

/-- Cochrane (2023), p. 408: the path is homogeneous, `path(c i, c p) = c path(i, p)`. -/
theorem path_smul (σ β κ c : ℝ) (i : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    path σ β κ (fun k => c * i k) (c * p) j = c * path σ β κ i p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [path, F_smul, ih]
    ring

/-- Cochrane (2023), p. 410: with no rate news the path from `p` is `p λ₁^{−j}`. -/
theorem path_zero_rate (σ β κ p : ℝ) (j : ℕ) :
    path σ β κ (fun _ => 0) p j = p * (lam1 σ β κ)⁻¹ ^ j := by
  induction j with
  | zero => simp [path]
  | succ j ih =>
    have hF : F (lam2 σ β κ) (fun _ => (0 : ℝ)) j = 0 := by simp [F]
    simp only [path, hF, ih, pow_succ, mul_zero, add_zero, div_eq_mul_inv]
    ring

/-! ### Expected paths -/

/-- Cochrane (2023), §17.4, pp. 407–410, under uncertainty: for an equilibrium of
(17.15)–(17.17) without disturbances, the expected paths
`j ↦ (E_s i_{s+j}, E_s x_{s+j}, E_s π_{s+j})(ω)` form a perfect-foresight equilibrium. -/
theorem expected_pfEqm {σ β κ : ℝ} {i r x π : ℕ → Ω → ℝ} (h : Model 𝔼 σ β κ 0 0 i r x π)
    (s : ℕ) (ω : Ω) :
    PFEqm σ β κ (fun j => 𝔼.E s (i (s + j)) ω) (fun j => 𝔼.E s (x (s + j)) ω)
      (fun j => 𝔼.E s (π (s + j)) ω) := by
  obtain ⟨his, hf, hpc⟩ := h
  intro j
  have hle : s ≤ s + j := Nat.le_add_right s j
  have e1 := congrFun (congrArg (𝔼.E s) (his (s + j))) ω
  have e2 := congrFun (congrArg (𝔼.E s) (hf (s + j))) ω
  have e3 := congrFun (congrArg (𝔼.E s) (hpc (s + j))) ω
  simp only [map_add, map_sub, map_smul, 𝔼.tower hle, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply, add_zero] at e1 e2 e3
  have hs : s + (j + 1) = s + j + 1 := rfl
  simp only [hs]
  exact ⟨by linear_combination e1 + σ * e2, e3⟩

/-- Cochrane (2023), §17.4.1, p. 408, under uncertainty: with bounded rates and inflation,
expected inflation `E_s π_{s+j}` is the perfect-foresight path for the expected rate path
`E_s i_{s+·}` started at `E_s π_s`, and expected output is
`(E_s π_{s+j} − β E_s π_{s+j+1})/κ`. -/
theorem expected_path {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ 0 0 i r x π) (hi : ∀ t ω, |i t ω| ≤ M) (hπ : ∀ t ω, |π t ω| ≤ Mπ)
    (s : ℕ) (ω : Ω) :
    (fun j => 𝔼.E s (π (s + j)) ω) =
        path σ β κ (fun j => 𝔼.E s (i (s + j)) ω) (𝔼.E s (π s) ω) ∧
      ∀ j, 𝔼.E s (x (s + j)) ω = (𝔼.E s (π (s + j)) ω - β * 𝔼.E s (π (s + (j + 1))) ω) / κ := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  have hb : BoundedS fun j => 𝔼.E s (π (s + j)) ω := ⟨Mπ, fun j => 𝔼.abs_E_le (hπ _) s ω⟩
  obtain ⟨hx, hp⟩ := (pf_eqm_iff ha hκ hβ (fun j => 𝔼.abs_E_le (hi (s + j)) s ω) hb).mp
    (expected_pfEqm 𝔼 h s ω)
  exact ⟨hp, hx⟩

/-- Cochrane (2023), §17.4, under uncertainty: the date-`(s+1)` news about the whole future,
`j ↦ ΔE_{s+1}(i, x, π)_{s+1+j}`, is a perfect-foresight equilibrium. -/
theorem news_pfEqm {σ β κ : ℝ} {i r x π : ℕ → Ω → ℝ} (h : Model 𝔼 σ β κ 0 0 i r x π)
    (s : ℕ) (ω : Ω) :
    PFEqm σ β κ (fun j => innov 𝔼 s (i (s + 1 + j)) ω) (fun j => innov 𝔼 s (x (s + 1 + j)) ω)
      (fun j => innov 𝔼 s (π (s + 1 + j)) ω) := by
  intro j
  obtain ⟨a1, a2⟩ := expected_pfEqm 𝔼 h (s + 1) ω j
  obtain ⟨b1, b2⟩ := expected_pfEqm 𝔼 h s ω (j + 1)
  simp only at a1 a2 b1 b2
  rw [show s + (j + 1) = s + 1 + j by omega, show s + (j + 1 + 1) = s + 1 + (j + 1) by omega]
    at b1 b2
  simp only [innov, Pi.sub_apply]
  exact ⟨by linear_combination a1 - b1, by linear_combination a2 - b2⟩

/-- Cochrane (2023), Figs. 17.5–17.6 as impulse responses: with bounded rates and inflation,
the news about inflation is the perfect-foresight path for the news about rates, started at the
unexpected inflation `ΔE_{s+1} π_{s+1}`; the news about output is
`(ΔE_{s+1} π_{s+1+j} − β ΔE_{s+1} π_{s+2+j})/κ`. -/
theorem news_path {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ 0 0 i r x π) (hi : ∀ t ω, |i t ω| ≤ M) (hπ : ∀ t ω, |π t ω| ≤ Mπ)
    (s : ℕ) (ω : Ω) :
    (fun j => innov 𝔼 s (π (s + 1 + j)) ω) =
        path σ β κ (fun j => innov 𝔼 s (i (s + 1 + j)) ω) (innov 𝔼 s (π (s + 1)) ω) ∧
      ∀ j, innov 𝔼 s (x (s + 1 + j)) ω =
        (innov 𝔼 s (π (s + 1 + j)) ω - β * innov 𝔼 s (π (s + 1 + (j + 1))) ω) / κ := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  have hb : BoundedS fun j => innov 𝔼 s (π (s + 1 + j)) ω :=
    ⟨2 * Mπ, fun j => abs_innov_le 𝔼 (hπ _) s ω⟩
  obtain ⟨hx, hp⟩ := (pf_eqm_iff ha hκ hβ (fun j => abs_innov_le 𝔼 (hi (s + 1 + j)) s ω) hb).mp
    (news_pfEqm 𝔼 h s ω)
  exact ⟨hp, hx⟩

/-! ### Figure 17.5 under uncertainty -/

/-- Cochrane (2023), Fig. 17.5, p. 409, under uncertainty: if the date-`(s+1)` news is a
permanent rise of expected rates from horizon `T` (`ΔE_{s+1} i_{s+1+k} = 1{k ≥ T}`), the news
about inflation is `path(1{· ≥ T}, δ)`, `δ = ΔE_{s+1} π_{s+1}`; it converges to one; and at every
horizon `j ≥ 1` it exceeds `δ λ₁^{−j}`, the response to the same unexpected inflation with no
rate news. -/
theorem news_rise {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ 0 0 i r x π) (hi : ∀ t ω, |i t ω| ≤ M) (hπ : ∀ t ω, |π t ω| ≤ Mπ)
    (s : ℕ) (ω : Ω) (T : ℕ) (hnews : ∀ k, innov 𝔼 s (i (s + 1 + k)) ω = stepI T k) :
    (fun j => innov 𝔼 s (π (s + 1 + j)) ω) = path σ β κ (stepI T) (innov 𝔼 s (π (s + 1)) ω) ∧
      Tendsto (fun j => innov 𝔼 s (π (s + 1 + j)) ω) atTop (𝓝 1) ∧
      ∀ j, innov 𝔼 s (π (s + 1)) ω * (lam1 σ β κ)⁻¹ ^ (j + 1) <
        innov 𝔼 s (π (s + 1 + (j + 1))) ω := by
  have hp := (news_path 𝔼 ha hβ h hi hπ s ω).1
  have hn : (fun j => innov 𝔼 s (i (s + 1 + j)) ω) = stepI T := funext hnews
  rw [hn] at hp
  set δ := innov 𝔼 s (π (s + 1)) ω
  have hb := path_bounded ha hβ (stepI_bound T) δ
  refine ⟨hp, ?_, fun j => ?_⟩
  · rw [hp]
    exact tendsto_pi ha hβ (stepI_bound T) (stepI_tendsto T) hb
      ((second_iff_factor ha hβ (stepI_bound T) hb).mpr (path_factor ha hβ _ δ))
  · have e := congrFun hp (j + 1)
    rw [e, ← path_zero_rate σ β κ δ (j + 1)]
    exact rise_raises_inflation ha hβ T δ j

/-- Cochrane (2023), Fig. 17.5, p. 409, under uncertainty, solid line: if moreover the
unexpected inflation is the two-sided value `antPath T 0` (no expectational error beyond the
rate news), the news about inflation is `FullModel.antPath T` — positive, strictly increasing,
below one — and the news about output is negative at every horizon up to and including the
rise. -/
theorem news_rise_twoSided {σ β κ M Mπ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β)
    {i r x π : ℕ → Ω → ℝ} (h : Model 𝔼 σ β κ 0 0 i r x π) (hi : ∀ t ω, |i t ω| ≤ M)
    (hπ : ∀ t ω, |π t ω| ≤ Mπ) (s : ℕ) (ω : Ω) (T : ℕ)
    (hnews : ∀ k, innov 𝔼 s (i (s + 1 + k)) ω = stepI T k)
    (hδ : innov 𝔼 s (π (s + 1)) ω = antPath σ β κ T 0) :
    (fun j => innov 𝔼 s (π (s + 1 + j)) ω) = antPath σ β κ T ∧
      (∀ j, 0 < innov 𝔼 s (π (s + 1 + j)) ω ∧ innov 𝔼 s (π (s + 1 + j)) ω < 1) ∧
      StrictMono (fun j => innov 𝔼 s (π (s + 1 + j)) ω) ∧
      ∀ j, j ≤ T → innov 𝔼 s (x (s + 1 + j)) ω < 0 := by
  have ha := mul_pos hσ hκ
  have hp := (news_rise 𝔼 ha hβ h hi hπ s ω T hnews).1
  have hant : (fun j => innov 𝔼 s (π (s + 1 + j)) ω) = antPath σ β κ T := by
    rw [hp, hδ]
    rfl
  refine ⟨hant, fun j => ?_, ?_, fun j hj => ?_⟩
  · have e := congrFun hant j
    rw [e]
    exact ⟨antPath_pos ha hβ T j, antPath_lt_one ha hβ T j⟩
  · rw [hant]; exact antPath_strictMono ha hβ T
  · rw [(news_path 𝔼 ha hβ h hi hπ s ω).2 j]
    have e1 := congrFun hant j
    have e2 := congrFun hant (j + 1)
    rw [e1, e2]
    exact antPath_x_neg hσ hκ hβ hj

/-! ### Figure 17.6 under uncertainty: the equilibrium set -/

/-- Cochrane (2023), eq. (17.18), p. 408, under uncertainty and without disturbances:
`σκ i_t = −β E_t π_{t+2} + (1 + β + σκ) E_t π_{t+1} − π_t`. -/
def Eq1718 (σ β κ : ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, (σ * κ) • i t = -β • 𝔼.E t (π (t + 2)) + (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) - π t

/-- Cochrane (2023), eqs. (17.15)–(17.18), pp. 407–408: without disturbances and with
`κ ≠ 0`, the model holds iff `r_t = i_t − E_t π_{t+1}`, `x_t = (π_t − β E_t π_{t+1})/κ` and
(17.18) holds (`FullModel.eq_17_18_shocks`). -/
theorem model_iff_eq1718 {σ β κ : ℝ} (hκ : κ ≠ 0) (i r x π : ℕ → Ω → ℝ) :
    Model 𝔼 σ β κ 0 0 i r x π ↔ (r = fun t => i t - 𝔼.E t (π (t + 1))) ∧
      (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))) ∧ Eq1718 𝔼 σ β κ i π := by
  rw [eq_17_18_shocks 𝔼 hκ]
  simp only [Pi.zero_apply, map_zero, sub_zero, smul_zero, add_zero, Eq1718]

/-- Cochrane (2023), eq. (5.5), p. 119, and A1 §1.7, p. 570, under uncertainty: the factored
form `λ₁ E_t π_{t+1} = π_t + σκ F_t`, `F_t = ∑_{k≥0} λ₂ᵏ E_t i_{t+k}`. -/
def Factored (σ β κ : ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, lam1 σ β κ • 𝔼.E t (π (t + 1)) = π t + (σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t

/-- Cochrane (2023), eq. (5.5) and A1 §1.7, under uncertainty: for bounded adapted rates and
bounded inflation, (17.18) holds iff the factored form does (the `λ₂` factor solved forward with
`ExpectationSystem.forward_unique`). -/
theorem eq1718_iff_factored {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → Ω → ℝ}
    (hi : ∀ t ω, |i t ω| ≤ M) (hia : 𝔼.Adapted i) (hπ : ∀ t ω, |π t ω| ≤ Mπ) :
    Eq1718 𝔼 σ β κ i π ↔ Factored 𝔼 σ β κ i π := by
  have hsum := lam_sum σ β κ
  have hprod := lam_prod ha hβ
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl2 : |lam2 σ β κ| < 1 := by rw [abs_of_nonneg h20]; exact h21
  set l1 := lam1 σ β κ
  set l2 := lam2 σ β κ
  set Fs := 𝔼.forwardSeries l2 i
  set g : ℕ → Ω → ℝ := fun t => π t - l1 • 𝔼.E t (π (t + 1)) with hg
  set hh : ℕ → Ω → ℝ := fun t => (-(σ * κ)) • Fs t with hhh
  have key : ∀ t, g t - l2 • 𝔼.E t (g (t + 1)) =
      π t - (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) + β • 𝔼.E t (π (t + 2)) := by
    intro t
    simp only [hg, map_sub, map_smul, 𝔼.tower (Nat.le_succ t)]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hsum, ← hprod]
    ring
  have hsol : ∀ t, hh t = l2 • 𝔼.E t (hh (t + 1)) + (-(σ * κ)) • i t := by
    intro t
    have e : Fs t = l2 • 𝔼.E t (Fs (t + 1)) + i t := 𝔼.forwardSeries_solves h20 h21 hi hia t
    simp only [hhh, map_smul]
    rw [e]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hgb : BoundedProc g := ⟨Mπ + |l1| * Mπ, fun t ω => by
    simp only [hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hπ t ω) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hπ _) t ω) (abs_nonneg _)⟩
  have hhb : BoundedProc hh := by
    obtain ⟨K, hK⟩ := 𝔼.forwardSeries_bounded h20 h21 hi
    exact ⟨|σ * κ| * K, fun t ω => by
      simp only [hhh, Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hK t ω) (by positivity)⟩
  constructor
  · intro h
    have hgs : ∀ t, g t = l2 • 𝔼.E t (g (t + 1)) + (-(σ * κ)) • i t := by
      intro t
      have e1 := key t
      have e2 := h t
      funext ω
      have f1 := congrFun e1 ω
      have f2 := congrFun e2 ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul] at f1 f2 ⊢
      linear_combination f1 + f2
    have hgh := 𝔼.forward_unique hl2 hgs hsol hgb hhb
    intro t
    have e := congrFun hgh t
    funext ω
    have f := congrFun e ω
    simp only [hg, hhh, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f ⊢
    linear_combination -f
  · intro h t
    have hgh : g = hh := by
      funext t ω
      have f := congrFun (h t) ω
      simp only [hg, hhh, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at f ⊢
      linear_combination -f
    have e1 := key t
    have e2 := hsol t
    rw [← hgh] at e2
    funext ω
    have f1 := congrFun e1 ω
    have f2 := congrFun e2 ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_mul] at f1 f2 ⊢
    linear_combination f2 - f1

/-- Cochrane (2023), Fig. 17.6, p. 410, under uncertainty: the inflation process with initial
value `p` and inflation innovations `δ_{t+1}`,
`π_{t+1} = λ₁^{−1}(π_t + σκ F_t) + δ_{t+1}`. -/
noncomputable def piInnov (σ β κ : ℝ) (i : ℕ → Ω → ℝ) (p : Ω → ℝ) (δ : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => p
  | t + 1 => (lam1 σ β κ)⁻¹ • (piInnov σ β κ i p δ t +
      (σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t) + δ (t + 1)

/-- Cochrane (2023), Fig. 17.6, under uncertainty: `piInnov` is adapted, satisfies the factored
form, and its innovations are `δ`. -/
theorem piInnov_props {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → Ω → ℝ}
    (hi : ∀ t ω, |i t ω| ≤ M) {p : Ω → ℝ} (hp0 : 𝔼.E 0 p = p) {δ : ℕ → Ω → ℝ}
    (hδa : 𝔼.Adapted δ) (hδ0 : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    𝔼.Adapted (piInnov 𝔼 σ β κ i p δ) ∧ Factored 𝔼 σ β κ i (piInnov 𝔼 σ β κ i p δ) ∧
      ∀ t, piInnov 𝔼 σ β κ i p δ (t + 1) - 𝔼.E t (piInnov 𝔼 σ β κ i p δ (t + 1)) = δ (t + 1) := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have hFa := 𝔼.forwardSeries_adapted h20 h21 hi
  have had : 𝔼.Adapted (piInnov 𝔼 σ β κ i p δ) := by
    intro t
    induction t with
    | zero => exact hp0
    | succ t ih =>
      simp only [piInnov, map_add, map_smul]
      rw [ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hFa t), hδa (t + 1)]
  have hE : ∀ t, 𝔼.E t (piInnov 𝔼 σ β κ i p δ (t + 1)) = (lam1 σ β κ)⁻¹ •
      (piInnov 𝔼 σ β κ i p δ t + (σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t) := by
    intro t
    simp only [piInnov, map_add, map_smul]
    rw [had t, hFa t, hδ0 t, add_zero]
  refine ⟨had, fun t => ?_, fun t => ?_⟩
  · rw [hE t, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  · rw [hE t]
    simp only [piInnov]
    abel

/-- Cochrane (2023), Fig. 17.6, under uncertainty: `piInnov` is bounded for bounded `i`, `p`,
`δ`. -/
theorem piInnov_bounded {σ β κ M Mp Mδ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → Ω → ℝ}
    (hi : ∀ t ω, |i t ω| ≤ M) {p : Ω → ℝ} (hp : ∀ ω, |p ω| ≤ Mp) {δ : ℕ → Ω → ℝ}
    (hδ : ∀ t ω, |δ t ω| ≤ Mδ) :
    ∃ K, ∀ t ω, |piInnov 𝔼 σ β κ i p δ t ω| ≤ K := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hc0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr hl0.le
  have hc1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  obtain ⟨K, hK⟩ := 𝔼.forwardSeries_bounded h20 h21 hi
  set Fc := (lam1 σ β κ)⁻¹ * (σ * κ * max K 0) + max Mδ 0
  have hFc : 0 ≤ Fc := by positivity
  refine ⟨max Mp 0 + Fc / (1 - (lam1 σ β κ)⁻¹), fun t ω => ?_⟩
  refine bounded_of_rec (x := fun t => piInnov 𝔼 σ β κ i p δ t ω) hc0 hc1 hFc
    ((hp ω).trans (le_max_left _ _)) (fun t => ?_) t
  simp only [piInnov, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hc0]
  have h1 := abs_add_le (piInnov 𝔼 σ β κ i p δ t ω)
    (σ * κ * 𝔼.forwardSeries (lam2 σ β κ) i t ω)
  have h2 : |σ * κ * 𝔼.forwardSeries (lam2 σ β κ) i t ω| ≤ σ * κ * max K 0 := by
    rw [abs_mul, abs_of_pos ha]
    exact mul_le_mul_of_nonneg_left ((hK t ω).trans (le_max_left _ _)) ha.le
  have h3 := (hδ (t + 1) ω).trans (le_max_left Mδ 0)
  have h4 : (lam1 σ β κ)⁻¹ * |piInnov 𝔼 σ β κ i p δ t ω + σ * κ *
      𝔼.forwardSeries (lam2 σ β κ) i t ω| ≤ (lam1 σ β κ)⁻¹ * (|piInnov 𝔼 σ β κ i p δ t ω| +
      σ * κ * max K 0) := mul_le_mul_of_nonneg_left (h1.trans (by linarith)) hc0
  simp only [Fc]
  nlinarith

/-- Cochrane (2023), Fig. 17.6, p. 410 ("any of these jumps"), under uncertainty: for
`σκ > 0`, `β > 0`, every bounded adapted rate process `i`, every bounded initial inflation `p`
known at date 0, and **every** bounded adapted inflation-innovation process `δ`
(`E_t δ_{t+1} = 0`), there is exactly one bounded adapted equilibrium of (17.15)–(17.17) with
`π_0 = p` and `π_{t+1} − E_t π_{t+1} = δ_{t+1}`; it is `piInnov`. -/
theorem innov_eqm_existsUnique {σ β κ M Mp Mδ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    {i : ℕ → Ω → ℝ} (hi : ∀ t ω, |i t ω| ≤ M) (hia : 𝔼.Adapted i) {p : Ω → ℝ}
    (hp0 : 𝔼.E 0 p = p) (hp : ∀ ω, |p ω| ≤ Mp) {δ : ℕ → Ω → ℝ} (hδ : ∀ t ω, |δ t ω| ≤ Mδ)
    (hδa : 𝔼.Adapted δ) (hδ0 : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    ∃! π : ℕ → Ω → ℝ, 𝔼.Adapted π ∧ BoundedProc π ∧ π 0 = p ∧
      (∀ t, π (t + 1) - 𝔼.E t (π (t + 1)) = δ (t + 1)) ∧
      Model 𝔼 σ β κ 0 0 i (fun t => i t - 𝔼.E t (π (t + 1)))
        (fun t => κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))) π := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  obtain ⟨had, hfac, hinn⟩ := piInnov_props 𝔼 ha hβ hi hp0 hδa hδ0
  obtain ⟨K, hK⟩ := piInnov_bounded 𝔼 ha hβ hi hp hδ
  refine ⟨piInnov 𝔼 σ β κ i p δ, ⟨had, ⟨K, hK⟩, rfl, hinn, ?_⟩, ?_⟩
  · exact (model_iff_eq1718 𝔼 hκ _ _ _ _).mpr ⟨rfl, fun t => rfl,
      (eq1718_iff_factored 𝔼 ha hβ hi hia hK).mpr hfac⟩
  · rintro π' ⟨-, ⟨K', hK'⟩, h0, hin, hm⟩
    have hf' := (eq1718_iff_factored 𝔼 ha hβ hi hia hK').mp
      ((model_iff_eq1718 𝔼 hκ _ _ _ _).mp hm).2.2
    funext t
    induction t with
    | zero => exact h0
    | succ t ih =>
      have e1 : π' (t + 1) = 𝔼.E t (π' (t + 1)) + δ (t + 1) := by
        rw [← hin t]; abel
      have e2 : 𝔼.E t (π' (t + 1)) = (lam1 σ β κ)⁻¹ •
          (π' t + (σ * κ) • 𝔼.forwardSeries (lam2 σ β κ) i t) := by
        rw [← hf' t, smul_smul, inv_mul_cancel₀ hl0, one_smul]
      rw [e1, e2, ih]
      rfl

/-! ### Reverse-engineered disturbances under uncertainty -/

/-- Cochrane (2023), p. 414, under uncertainty: output along `piInnov`,
`x_t = (π_t − β E_t π_{t+1})/κ`. -/
noncomputable def xInnov (σ β κ : ℝ) (i : ℕ → Ω → ℝ) (p : Ω → ℝ) (δ : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun t => κ⁻¹ • (piInnov 𝔼 σ β κ i p δ t - β • 𝔼.E t (piInnov 𝔼 σ β κ i p δ (t + 1)))

/-- Cochrane (2023), p. 414 ("if fed these `{u_t}` paths, the model produces the given interest
rate and inflation paths"), under uncertainty: for every equilibrium `piInnov` of Fig. 17.6
(every initial inflation and every innovation process), the disturbance `u = i − φπ` makes it
the **unique** bounded adapted equilibrium of the model with `i_t = φ π_t + u_t`, whenever `φ`
is in the determinacy region. -/
theorem reverse_engineer_innov [Nonempty Ω] {σ β κ φ M Mp Mδ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ)
    (hβ : 0 < β) (hdet : TaylorDeterminacy.Determinate 𝔼 σ β κ φ 0) {i : ℕ → Ω → ℝ}
    (hi : ∀ t ω, |i t ω| ≤ M) (hia : 𝔼.Adapted i) {p : Ω → ℝ} (hp0 : 𝔼.E 0 p = p)
    (hp : ∀ ω, |p ω| ≤ Mp) {δ : ℕ → Ω → ℝ} (hδ : ∀ t ω, |δ t ω| ≤ Mδ) (hδa : 𝔼.Adapted δ)
    (hδ0 : ∀ t, 𝔼.E t (δ (t + 1)) = 0) {i' x' π' : ℕ → Ω → ℝ} (hx' : 𝔼.Adapted x')
    (hπ' : 𝔼.Adapted π') (hbx' : BoundedProc x') (hbπ' : BoundedProc π') :
    (OptimalPolicy.Starred 𝔼 σ β κ 0 0 i' x' π' ∧
        ∀ t, i' t = φ • π' t + (i t - φ • piInnov 𝔼 σ β κ i p δ t)) ↔
      i' = i ∧ x' = xInnov 𝔼 σ β κ i p δ ∧ π' = piInnov 𝔼 σ β κ i p δ := by
  have ha := mul_pos hσ hκ
  obtain ⟨had, hfac, -⟩ := piInnov_props 𝔼 ha hβ hi hp0 hδa hδ0
  obtain ⟨K, hK⟩ := piInnov_bounded 𝔼 ha hβ hi hp hδ
  have hm : Model 𝔼 σ β κ 0 0 i (fun t => i t - 𝔼.E t (piInnov 𝔼 σ β κ i p δ (t + 1)))
      (xInnov 𝔼 σ β κ i p δ) (piInnov 𝔼 σ β κ i p δ) :=
    (model_iff_eq1718 𝔼 hκ.ne' _ _ _ _).mpr ⟨rfl, fun t => rfl,
      (eq1718_iff_factored 𝔼 ha hβ hi hia hK).mpr hfac⟩
  have hs := (OptimalPolicy.starred_iff_model 𝔼 σ β κ 0 0 _ _ _).mpr hm
  have hxa : 𝔼.Adapted (xInnov 𝔼 σ β κ i p δ) := fun t => by
    simp only [xInnov, map_smul, map_sub, 𝔼.E_E_self, had t]
  have hxb : BoundedProc (xInnov 𝔼 σ β κ i p δ) := ⟨κ⁻¹ * (K + |β| * K), fun t ω => by
    simp only [xInnov, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hκ)]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hK t ω) ?_))
      (inv_pos.mpr hκ).le
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hK _) t ω) (abs_nonneg _)⟩
  exact TaylorDeterminacy.standard_rule_unique 𝔼 hdet hs hxa had hxb ⟨K, hK⟩ hx' hπ' hbx' hbπ'

/-- Cochrane (2023), p. 411 ("multiple disturbance paths `u_t` produce the same interest-rate
path"), under uncertainty: with `φ ≠ 0`, two equilibria of Fig. 17.6 with different
inflation innovations need different reverse-engineered disturbances `u = i − φπ`. -/
theorem reverse_engineer_innov_distinct {σ β κ φ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    (hφ : φ ≠ 0) {i : ℕ → Ω → ℝ} (hi : ∀ t ω, |i t ω| ≤ M) {p p' : Ω → ℝ} (hp0 : 𝔼.E 0 p = p)
    (hp0' : 𝔼.E 0 p' = p') {δ δ' : ℕ → Ω → ℝ} (hδa : 𝔼.Adapted δ) (hδa' : 𝔼.Adapted δ')
    (hδ0 : ∀ t, 𝔼.E t (δ (t + 1)) = 0) (hδ0' : ∀ t, 𝔼.E t (δ' (t + 1)) = 0)
    (hne : p ≠ p' ∨ ∃ t, δ (t + 1) ≠ δ' (t + 1)) :
    (fun t => i t - φ • piInnov 𝔼 σ β κ i p δ t) ≠
      (fun t => i t - φ • piInnov 𝔼 σ β κ i p' δ' t) := by
  intro h
  have hπ : piInnov 𝔼 σ β κ i p δ = piInnov 𝔼 σ β κ i p' δ' := by
    funext t
    have e := congrFun h t
    have e' : φ • piInnov 𝔼 σ β κ i p δ t = φ • piInnov 𝔼 σ β κ i p' δ' t := by
      have := congrArg (fun z => i t - z) e
      simpa using this
    exact smul_right_injective _ hφ e'
  rcases hne with hp | ⟨t, ht⟩
  · exact hp (congrFun hπ 0)
  · apply ht
    rw [← (piInnov_props 𝔼 ha hβ hi hp0 hδa hδ0).2.2 t,
      ← (piInnov_props 𝔼 ha hβ hi hp0' hδa' hδ0').2.2 t, hπ]

end Cochrane.KeynesianStickyPrices.TidyR5StochasticPaths
