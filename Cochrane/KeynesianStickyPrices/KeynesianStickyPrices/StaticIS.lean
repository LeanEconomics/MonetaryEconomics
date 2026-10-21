/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.SharedTools

/-!
# New vs. old Keynesian models: the static IS curve

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.1 "New vs. old
Keynesian models" and §17.2 "Responses to interest rate changes", pp. 397–401.

The model is the IS curve and Phillips curve (17.1)–(17.2) with a generic expected-inflation
process `πᵉ`; deleting `E_t x_{t+1}` gives the static IS model (17.3)–(17.4), whose single
equilibrium condition is (17.5) `π_t = −σκ i_t + (1 + σκ) πᵉ_t`.

* Adaptive expectations `πᵉ_t = π_{t−1}` (old Keynesian), (17.6): the solution is unique given
  `π_{−1}` (`adaptive_existsUnique`, "determinate"), but under a peg it spirals away:
  `π_t − ī = (1 + σκ)^{t+1}(π_{−1} − ī)` (`adaptive_peg`, `adaptive_peg_unbounded`).
* Rational expectations `πᵉ_t = E_t π_{t+1}` (new Keynesian), (17.7): the coefficient
  `1/(1 + σκ)` lies in `(0, 1)` ("stable"), but any expectational error is possible
  ("indeterminate"): `reFamily_solves`, `eq_reFamily`, `re_indeterminate`, `re_not_unique`.
* (17.8): the finite-start form `reFamily_closed`, and the infinite-past backward moving average
  (`eq_17_8`; converse `SharedTools.backward_series_solves`): every bounded solution has the
  form (17.8), and conversely.
* Figure 17.1 (`fig17_1_path`, `fig17_1_tendsto`, `fig17_1_less_sticky`) and Figure 17.2
  (`fig17_2_solves`, `fig17_2_strictMono`, `fig17_2_tendsto`, `fig17_2_less_sticky`,
  `fig17_2_frictionless_limit`, `fig17_2_dashed`), and the frictionless limit `κ → ∞` of (17.7)
  (`tendsto_coeff_17_7`).
* p. 401: a fully expected rate path brings no expectational errors (`no_surprise_of_known`);
  active fiscal policy, by fixing unexpected inflation, selects one equilibrium
  (`fiscal_selects`).

Everything is stated for an arbitrary `ExpectationSystem`, so it holds under perfect foresight
and under genuine uncertainty. Throughout, `σ, κ > 0` where needed.
-/

namespace Cochrane.KeynesianStickyPrices.StaticIS

open Filter Topology
open SharedTools (eq_backward_series)

variable {Ω : Type*}

/-! ### The model (17.1)–(17.5) -/

/-- Cochrane (2023), eqs. (17.1)–(17.2), pp. 397–398: the IS curve
`x_t = E_t x_{t+1} − σ(i_t − πᵉ_t)` and Phillips curve `π_t = πᵉ_t + κ x_t` with an expected
inflation process `πᵉ`. -/
def ISPhillips (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) (i πe x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = 𝔼.E t (x (t + 1)) ω - σ * (i t ω - πe t ω) ∧ π t ω = πe t ω + κ * x t ω

/-- Cochrane (2023), eqs. (17.1)–(17.2), pp. 397–398: eliminating output,
`π_t = (1 + σκ) πᵉ_t − σκ i_t + κ E_t x_{t+1}`. -/
theorem isPhillips_infl {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} {i πe x π : ℕ → Ω → ℝ}
    (h : ISPhillips 𝔼 σ κ i πe x π) (t : ℕ) (ω : Ω) :
    π t ω = (1 + σ * κ) * πe t ω - σ * κ * i t ω + κ * 𝔼.E t (x (t + 1)) ω := by
  obtain ⟨h1, h2⟩ := h t ω
  rw [h2, h1]; ring

/-- Cochrane (2023), eqs. (17.3)–(17.4), p. 398: the static IS curve `x_t = −σ(i_t − πᵉ_t)` and
the Phillips curve `π_t = πᵉ_t + κ x_t`. -/
def StaticModel (σ κ : ℝ) (i πe x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, x t ω = -σ * (i t ω - πe t ω) ∧ π t ω = πe t ω + κ * x t ω

/-- Cochrane (2023), p. 398: (17.3)–(17.4) are (17.1)–(17.2) with the `E_t x_{t+1}` term
deleted. -/
theorem isPhillips_iff_static_of_E_zero {𝔼 : ExpectationSystem Ω} {σ κ : ℝ}
    {i πe x π : ℕ → Ω → ℝ} (h0 : ∀ t, 𝔼.E t (x (t + 1)) = 0) :
    ISPhillips 𝔼 σ κ i πe x π ↔ StaticModel σ κ i πe x π := by
  unfold ISPhillips StaticModel
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  rw [h0 t, Pi.zero_apply]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨by rw [h1]; ring, h2⟩

/-- Cochrane (2023), eq. (17.5), p. 398: eliminating `x_t` from (17.3)–(17.4), the static model
holds iff output is given by (17.3) and `π_t = −σκ i_t + (1 + σκ) πᵉ_t`. -/
theorem staticModel_iff (σ κ : ℝ) (i πe x π : ℕ → Ω → ℝ) :
    StaticModel σ κ i πe x π ↔ (∀ t ω, x t ω = -σ * (i t ω - πe t ω)) ∧
      ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * πe t ω := by
  constructor
  · intro h
    refine ⟨fun t ω => (h t ω).1, fun t ω => ?_⟩
    obtain ⟨h1, h2⟩ := h t ω
    rw [h2, h1]; ring
  · rintro ⟨h1, h2⟩ t ω
    refine ⟨h1 t ω, ?_⟩
    rw [h2 t ω, h1 t ω]; ring

/-- Cochrane (2023), eq. (17.5), p. 398: an inflation process is part of an equilibrium of
(17.3)–(17.4) iff it satisfies the single equation (17.5). -/
theorem exists_static_iff_17_5 (σ κ : ℝ) (i πe π : ℕ → Ω → ℝ) :
    (∃ x, StaticModel σ κ i πe x π) ↔
      ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * πe t ω := by
  constructor
  · rintro ⟨x, hx⟩
    exact ((staticModel_iff σ κ i πe x π).mp hx).2
  · intro h
    exact ⟨fun t ω => -σ * (i t ω - πe t ω),
      (staticModel_iff σ κ i πe _ π).mpr ⟨fun _ _ => rfl, h⟩⟩

/-! ### Adaptive expectations (17.6) -/

/-- Cochrane (2023), p. 398: the lagged inflation process `π_{t−1}`, with initial value
`π_{−1}`; adaptive expectations set `πᵉ_t = π_{t−1}`. -/
def lagged (π0 : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => π t

/-- Cochrane (2023), eq. (17.6), p. 398: the adaptive-expectations equilibrium condition
`π_t = (1 + σκ) π_{t−1} − σκ i_t`, given `π_{−1}`. -/
def AdaptiveEq (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, π t ω = (1 + σ * κ) * lagged π0 π t ω - σ * κ * i t ω

/-- Cochrane (2023), eq. (17.6), p. 398: with `πᵉ_t = π_{t−1}` the static model (17.3)–(17.4)
reduces to (17.6). -/
theorem exists_static_adaptive_iff (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) :
    (∃ x, StaticModel σ κ i (lagged π0 π) x π) ↔ AdaptiveEq σ κ π0 i π := by
  rw [exists_static_iff_17_5]
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro h <;> rw [h] <;> ring

/-- Cochrane (2023), p. 398: (17.6) rearranged, `π_t − π_{t−1} = −σκ (i_t − π_{t−1})`: a higher
real rate brings inflation down. -/
theorem adaptive_change_iff (σ κ : ℝ) (π0 : Ω → ℝ) (i π : ℕ → Ω → ℝ) :
    AdaptiveEq σ κ π0 i π ↔ ∀ t ω,
      π t ω - lagged π0 π t ω = -(σ * κ) * (i t ω - lagged π0 π t ω) := by
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 399 (the old-Keynesian mechanism): with adaptive expectations a nominal
rate above lagged inflation (a high real rate) lowers output, and lower output lowers
inflation. -/
theorem adaptive_mechanism {σ κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) {π0 : Ω → ℝ}
    {i x π : ℕ → Ω → ℝ} (h : StaticModel σ κ i (lagged π0 π) x π) {t : ℕ} {ω : Ω}
    (hi : lagged π0 π t ω < i t ω) : x t ω < 0 ∧ π t ω < lagged π0 π t ω := by
  obtain ⟨h1, h2⟩ := h t ω
  have hx : x t ω < 0 := by rw [h1]; nlinarith
  exact ⟨hx, by rw [h2]; nlinarith⟩

/-- Cochrane (2023), eq. (17.6), p. 398: the solution of (17.6) built forward from `π_{−1}`. -/
def adaptivePath (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => (1 + σ * κ) * π0 ω - σ * κ * i 0 ω
  | t + 1 => fun ω => (1 + σ * κ) * adaptivePath σ κ π0 i t ω - σ * κ * i (t + 1) ω

/-- Cochrane (2023), eq. (17.6), p. 398: `adaptivePath` solves (17.6). -/
theorem adaptivePath_solves (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) :
    AdaptiveEq σ κ π0 i (adaptivePath σ κ π0 i) := by
  intro t ω
  cases t <;> rfl

/-- Cochrane (2023), p. 398, "There is only one equilibrium": two solutions of (17.6) with the
same `π_{−1}` coincide. -/
theorem adaptive_unique {σ κ : ℝ} {π0 : Ω → ℝ} {i π π' : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 i π) (h' : AdaptiveEq σ κ π0 i π') : π = π' := by
  funext t ω
  induction t with
  | zero => rw [h 0 ω, h' 0 ω]; rfl
  | succ t ih => rw [h (t + 1) ω, h' (t + 1) ω]; simp only [lagged]; rw [ih]

/-- Cochrane (2023), p. 398, "determinate": given `π_{−1}`, (17.6) has exactly one solution
(whatever the interest-rate path). -/
theorem adaptive_existsUnique (σ κ : ℝ) (π0 : Ω → ℝ) (i : ℕ → Ω → ℝ) :
    ∃! π, AdaptiveEq σ κ π0 i π :=
  ⟨_, adaptivePath_solves σ κ π0 i, fun _ h => adaptive_unique h (adaptivePath_solves σ κ π0 i)⟩

/-- Cochrane (2023), eq. (17.6), p. 398: under an interest-rate peg `i_t = ī`,
`π_t − ī = (1 + σκ)^{t+1} (π_{−1} − ī)`. -/
theorem adaptive_peg {σ κ ib : ℝ} {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) (t : ℕ) (ω : Ω) :
    π t ω = ib + (1 + σ * κ) ^ (t + 1) * (π0 ω - ib) := by
  induction t with
  | zero => rw [h 0 ω]; simp only [lagged]; ring
  | succ t ih => rw [h (t + 1) ω]; simp only [lagged]; rw [ih]; ring

/-- Cochrane (2023), p. 398, "unstable": under a peg, inflation spirals away from the peg,
`|π_t − ī| → ∞`, unless it starts exactly at the peg. -/
theorem adaptive_peg_unbounded {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) {ω : Ω} (hω : π0 ω ≠ ib) :
    Tendsto (fun t => |π t ω - ib|) atTop atTop := by
  have he : (fun t => |π t ω - ib|) = fun t => (1 + σ * κ) ^ (t + 1) * |π0 ω - ib| := by
    funext t
    rw [adaptive_peg h t ω, add_sub_cancel_left, abs_mul, abs_of_pos (by positivity)]
  rw [he]
  have hpos : 0 < |π0 ω - ib| := abs_pos.mpr (sub_ne_zero.mpr hω)
  refine Tendsto.atTop_mul_const hpos ?_
  exact (tendsto_pow_atTop_atTop_of_one_lt (by linarith)).comp (tendsto_add_atTop_nat 1)

/-- Cochrane (2023), p. 398: under a peg the adaptive solution is bounded iff inflation starts at
the peg, `π_{−1} = ī`. -/
theorem adaptive_peg_bounded_iff {σ κ ib : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ}
    {π : ℕ → Ω → ℝ} (h : AdaptiveEq σ κ π0 (fun _ _ => ib) π) (ω : Ω) :
    (∃ M, ∀ t, |π t ω| ≤ M) ↔ π0 ω = ib := by
  constructor
  · rintro ⟨M, hM⟩
    by_contra hne
    obtain ⟨t, ht⟩ := ((adaptive_peg_unbounded hσκ h hne).eventually_gt_atTop
      (M + |ib|)).exists
    have := abs_sub (π t ω) ib
    linarith [hM t]
  · intro he
    exact ⟨|ib|, fun t => by rw [adaptive_peg h t ω, he, sub_self, mul_zero, add_zero]⟩

/-- Cochrane (2023), p. 398: `i = π` is a steady state of the adaptive model. -/
theorem adaptive_steady_state (σ κ c : ℝ) :
    AdaptiveEq σ κ (fun (_ : Ω) => c) (fun _ _ => c) (fun _ _ => c) := by
  intro t ω
  cases t <;> simp only [lagged] <;> ring

/-! ### Rational expectations (17.7) -/

/-- Cochrane (2023), eqs. (17.5) and (17.7), p. 398: the rational-expectations equilibrium
condition `π_t = −σκ i_t + (1 + σκ) E_t π_{t+1}`, with `π` adapted. -/
def REModel (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) (i π : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * 𝔼.E t (π (t + 1)) ω

/-- Cochrane (2023), p. 398: the rational-expectations model is (17.3)–(17.4) with
`πᵉ_t = E_t π_{t+1}`. -/
theorem reModel_iff_static (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) (i π : ℕ → Ω → ℝ) :
    REModel 𝔼 σ κ i π ↔
      𝔼.Adapted π ∧ ∃ x, StaticModel σ κ i (fun t => 𝔼.E t (π (t + 1))) x π := by
  rw [exists_static_iff_17_5]; rfl

/-- Cochrane (2023), eq. (17.7), p. 398:
`E_t π_{t+1} = π_t/(1 + σκ) + σκ/(1 + σκ) · i_t`. -/
theorem reModel_iff_17_7 (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    (i π : ℕ → Ω → ℝ) :
    REModel 𝔼 σ κ i π ↔ 𝔼.Adapted π ∧ ∀ t ω,
      𝔼.E t (π (t + 1)) ω = 1 / (1 + σ * κ) * π t ω + σ * κ / (1 + σ * κ) * i t ω := by
  refine and_congr Iff.rfl (forall_congr' fun t => forall_congr' fun ω => ?_)
  constructor
  · intro e; rw [e]; field_simp; ring
  · intro e; rw [e]; field_simp; ring

/-- Cochrane (2023), p. 398: (17.7) rearranged, `E_t π_{t+1} − π_t = σκ (i_t − E_t π_{t+1})`:
a higher real rate raises subsequent expected inflation. -/
theorem re_change {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} {i π : ℕ → Ω → ℝ}
    (h : REModel 𝔼 σ κ i π) (t : ℕ) (ω : Ω) :
    𝔼.E t (π (t + 1)) ω - π t ω = σ * κ * (i t ω - 𝔼.E t (π (t + 1)) ω) := by
  rw [h.2 t ω]; ring

/-- Cochrane (2023), p. 398: with rational expectations a nominal rate above expected inflation
(a high real rate) raises expected inflation above current inflation. -/
theorem re_mechanism {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} (hσκ : 0 < σ * κ) {i π : ℕ → Ω → ℝ}
    (h : REModel 𝔼 σ κ i π) {t : ℕ} {ω : Ω} (hi : 𝔼.E t (π (t + 1)) ω < i t ω) :
    π t ω < 𝔼.E t (π (t + 1)) ω := by
  have := re_change h t ω
  nlinarith

/-- Cochrane (2023), p. 398, "The coefficient `1/(1 + σκ) < 1`": the coefficient of (17.7) lies
in `(0, 1)`, and the two coefficients sum to one. -/
theorem coeff_17_7 {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    0 < 1 / (1 + σ * κ) ∧ 1 / (1 + σ * κ) < 1 ∧ 0 < σ * κ / (1 + σ * κ) ∧
      1 / (1 + σ * κ) + σ * κ / (1 + σ * κ) = 1 := by
  have h1 : 0 < 1 + σ * κ := by linarith
  refine ⟨by positivity, by rw [div_lt_one h1]; linarith, by positivity, ?_⟩
  field_simp

/-- Cochrane (2023), p. 398: `i = π` is a steady state of the rational-expectations model. -/
theorem re_steady_state (𝔼 : ExpectationSystem Ω) (σ κ c : ℝ) :
    REModel 𝔼 σ κ (fun _ _ => c) (fun _ _ => c) := by
  refine ⟨fun t => 𝔼.const t c, fun t ω => ?_⟩
  rw [show (fun (_ : Ω) => c) = (fun _ => c) from rfl, 𝔼.const]; ring

/-- Cochrane (2023), eqs. (17.7)–(17.8), pp. 398–400: the backward recursion
`π_{t+1} = π_t/(1+σκ) + σκ/(1+σκ) · i_t + δ_{t+1}` from `π_0`, driven by expectational errors
`δ`. -/
noncomputable def reFamily (σ κ : ℝ) (π0 : Ω → ℝ) (i δ : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => (1 / (1 + σ * κ)) • reFamily σ κ π0 i δ t + (σ * κ / (1 + σ * κ)) • i t + δ (t + 1)

/-- Cochrane (2023), p. 400: the recursion defining `reFamily`. -/
theorem reFamily_succ (σ κ : ℝ) (π0 : Ω → ℝ) (i δ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    reFamily σ κ π0 i δ (t + 1) ω = 1 / (1 + σ * κ) * reFamily σ κ π0 i δ t ω +
      σ * κ / (1 + σ * κ) * i t ω + δ (t + 1) ω := rfl

/-- Cochrane (2023), p. 400: the family is adapted when `π_0`, `i` and `δ` are. -/
theorem reFamily_adapted (𝔼 : ExpectationSystem Ω) (σ κ : ℝ) {π0 : Ω → ℝ} {i δ : ℕ → Ω → ℝ}
    (hπ0 : 𝔼.E 0 π0 = π0) (hi : 𝔼.Adapted i) (hδ : 𝔼.Adapted δ) :
    𝔼.Adapted (reFamily σ κ π0 i δ) := by
  intro t
  induction t with
  | zero => exact hπ0
  | succ t ih =>
    change 𝔼.E (t + 1) ((1 / (1 + σ * κ)) • reFamily σ κ π0 i δ t +
      (σ * κ / (1 + σ * κ)) • i t + δ (t + 1)) = _
    rw [map_add, map_add, map_smul, map_smul, ← ih, ← hi t, 𝔼.known (Nat.le_succ t),
      𝔼.known (Nat.le_succ t), hδ (t + 1), ih, hi t]
    rfl

/-- Cochrane (2023), p. 398, "any value of unexpected inflation `ΔE_{t+1}π_{t+1}` is possible":
for every `π_0` known at date 0 and every adapted martingale-difference process `δ`, the
family is an equilibrium of (17.7) whose expectational errors are exactly `δ`. -/
theorem reFamily_solves (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    {π0 : Ω → ℝ} {i δ : ℕ → Ω → ℝ} (hπ0 : 𝔼.E 0 π0 = π0) (hi : 𝔼.Adapted i)
    (hδ : 𝔼.Adapted δ) (hmd : ∀ t, 𝔼.E t (δ (t + 1)) = 0) :
    REModel 𝔼 σ κ i (reFamily σ κ π0 i δ) ∧ ∀ t ω,
      reFamily σ κ π0 i δ (t + 1) ω - 𝔼.E t (reFamily σ κ π0 i δ (t + 1)) ω = δ (t + 1) ω := by
  have had := reFamily_adapted 𝔼 σ κ hπ0 hi hδ
  have hE : ∀ t, 𝔼.E t (reFamily σ κ π0 i δ (t + 1)) =
      (1 / (1 + σ * κ)) • reFamily σ κ π0 i δ t + (σ * κ / (1 + σ * κ)) • i t := by
    intro t
    change 𝔼.E t ((1 / (1 + σ * κ)) • reFamily σ κ π0 i δ t +
      (σ * κ / (1 + σ * κ)) • i t + δ (t + 1)) = _
    rw [map_add, map_add, map_smul, map_smul, had t, hi t, hmd t, add_zero]
  refine ⟨⟨had, fun t ω => ?_⟩, fun t ω => ?_⟩
  · rw [hE t]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · rw [hE t, reFamily_succ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), p. 400: the expectational errors `δ_{t+1} = π_{t+1} − E_t π_{t+1}` of a
process (set to zero at date 0). -/
def reErr (𝔼 : ExpectationSystem Ω) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => π (t + 1) - 𝔼.E t (π (t + 1))

/-- Cochrane (2023), p. 400: expectational errors of an adapted process are adapted and have
conditional mean zero. -/
theorem reErr_mds (𝔼 : ExpectationSystem Ω) {π : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) :
    𝔼.Adapted (reErr 𝔼 π) ∧ ∀ t, 𝔼.E t (reErr 𝔼 π (t + 1)) = 0 := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | zero => exact map_zero _
    | succ t => change 𝔼.E (t + 1) (π (t + 1) - 𝔼.E t (π (t + 1))) = _
                rw [map_sub, hπ (t + 1), 𝔼.known (Nat.le_succ t)]; rfl
  · change 𝔼.E t (π (t + 1) - 𝔼.E t (π (t + 1))) = 0
    rw [map_sub, 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), eqs. (17.7)–(17.8), p. 400: every equilibrium of (17.7) is a member of the
family, driven by its own expectational errors. -/
theorem eq_reFamily {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} (h : 1 + σ * κ ≠ 0) {i π : ℕ → Ω → ℝ}
    (hπ : REModel 𝔼 σ κ i π) : π = reFamily σ κ (π 0) i (reErr 𝔼 π) := by
  have h17 := ((reModel_iff_17_7 𝔼 h i π).mp hπ).2
  funext t ω
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [reFamily_succ, ← ih]
    change π (t + 1) ω = _ + (π (t + 1) ω - 𝔼.E t (π (t + 1)) ω)
    rw [h17 t ω]; ring

/-- Cochrane (2023), p. 400: with bounded `π_0`, `i` and `δ` and `σκ > 0`, the family is
bounded (the recursion is stable). -/
theorem reFamily_bounded {σ κ B Mi Mδ : ℝ} (hσκ : 0 < σ * κ) {π0 : Ω → ℝ} {i δ : ℕ → Ω → ℝ}
    (hπ0 : ∀ ω, |π0 ω| ≤ B) (hi : ∀ t ω, |i t ω| ≤ Mi) (hδ : ∀ t ω, |δ t ω| ≤ Mδ) :
    BoundedProc (reFamily σ κ π0 i δ) := by
  obtain ⟨ha0, ha1, hb0, hab⟩ := coeff_17_7 hσκ
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  have hb1 : b < 1 := by linarith
  set K := |B| + (|Mi| + |Mδ|) / (1 - a) with hK
  have h1a : 0 < 1 - a := by linarith
  have hKa : (1 - a) * K = (1 - a) * |B| + (|Mi| + |Mδ|) := by
    rw [hK]; field_simp
  refine ⟨K, fun t ω => ?_⟩
  induction t generalizing ω with
  | zero => exact (hπ0 ω).trans ((le_abs_self B).trans (by
      have : 0 ≤ (|Mi| + |Mδ|) / (1 - a) := by positivity
      linarith))
  | succ t ih =>
    rw [reFamily_succ]
    have e1 : |a * reFamily σ κ π0 i δ t ω| ≤ a * K := by
      rw [abs_mul, abs_of_pos ha0]; exact mul_le_mul_of_nonneg_left (ih ω) ha0.le
    have e2 : |b * i t ω| ≤ |Mi| := by
      rw [abs_mul, abs_of_pos hb0]
      calc b * |i t ω| ≤ 1 * |i t ω| := mul_le_mul_of_nonneg_right hb1.le (abs_nonneg _)
        _ ≤ |Mi| := by rw [one_mul]; exact (hi t ω).trans (le_abs_self _)
    have e3 : |δ (t + 1) ω| ≤ |Mδ| := (hδ (t + 1) ω).trans (le_abs_self _)
    have hB : 0 ≤ (1 - a) * |B| := mul_nonneg h1a.le (abs_nonneg _)
    calc |a * reFamily σ κ π0 i δ t ω + b * i t ω + δ (t + 1) ω|
        ≤ |a * reFamily σ κ π0 i δ t ω| + |b * i t ω| + |δ (t + 1) ω| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ a * K + |Mi| + |Mδ| := by linarith
      _ ≤ K := by linarith

/-- Cochrane (2023), p. 398, "Inflation is stable but indeterminate": for every bounded adapted
interest-rate path and every initial inflation `c`, there is a bounded equilibrium of (17.7)
with `π_0 = c`. -/
theorem re_indeterminate (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (hσκ : 0 < σ * κ)
    {i : ℕ → Ω → ℝ} (hib : BoundedProc i) (hi : 𝔼.Adapted i) (c : ℝ) :
    ∃ π, REModel 𝔼 σ κ i π ∧ BoundedProc π ∧ π 0 = fun _ => c := by
  obtain ⟨Mi, hMi⟩ := hib
  refine ⟨reFamily σ κ (fun _ => c) i 0,
    (reFamily_solves 𝔼 (by linarith) (𝔼.const 0 c) hi (fun t => map_zero _)
      (fun t => map_zero _)).1,
    reFamily_bounded hσκ (B := |c|) (fun _ => le_rfl) hMi (Mδ := 0) (fun _ _ => by simp), rfl⟩

/-- Cochrane (2023), p. 398: (17.7) never has a unique bounded equilibrium. -/
theorem re_not_unique (𝔼 : ExpectationSystem Ω) [Nonempty Ω] {σ κ : ℝ} (hσκ : 0 < σ * κ)
    {i : ℕ → Ω → ℝ} (hib : BoundedProc i) (hi : 𝔼.Adapted i) :
    ¬ ∃! π, REModel 𝔼 σ κ i π ∧ BoundedProc π := by
  rintro ⟨π, -, hu⟩
  obtain ⟨p0, h0, hb0, he0⟩ := re_indeterminate 𝔼 hσκ hib hi 0
  obtain ⟨p1, h1, hb1, he1⟩ := re_indeterminate 𝔼 hσκ hib hi 1
  have e := (hu p0 ⟨h0, hb0⟩).trans (hu p1 ⟨h1, hb1⟩).symm
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun e 0) ω
  rw [he0, he1] at this
  norm_num at this

/-- Cochrane (2023), eq. (17.8), p. 400 (finite-start form): with initial value `π_0`,
`π_{t+1} = aᵗ⁺¹ π_0 + b ∑_{j ≤ t} aʲ i_{t−j} + ∑_{j ≤ t} aʲ δ_{t+1−j}`, where `a = 1/(1+σκ)`
and `b = σκ/(1+σκ)`. -/
theorem reFamily_closed (σ κ : ℝ) (π0 : Ω → ℝ) (i δ : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    reFamily σ κ π0 i δ (t + 1) ω = (1 / (1 + σ * κ)) ^ (t + 1) * π0 ω +
      σ * κ / (1 + σ * κ) * ∑ j ∈ Finset.range (t + 1), (1 / (1 + σ * κ)) ^ j * i (t - j) ω +
      ∑ j ∈ Finset.range (t + 1), (1 / (1 + σ * κ)) ^ j * δ (t + 1 - j) ω := by
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  induction t with
  | zero =>
    rw [reFamily_succ]
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, pow_one,
      Nat.sub_zero]
    rfl
  | succ t ih =>
    rw [reFamily_succ, ih, Finset.sum_range_succ' (fun j => a ^ j * i (t + 1 - j) ω),
      Finset.sum_range_succ' (fun j => a ^ j * δ (t + 1 + 1 - j) ω)]
    simp only [Nat.add_sub_add_right, Nat.sub_zero, pow_zero, one_mul, pow_succ,
      Finset.mul_sum]
    have e1 : ∀ j, a ^ j * a * i (t - j) ω = a * (a ^ j * i (t - j) ω) := fun j => by ring
    have e2 : ∀ j, a ^ j * a * δ (t + 1 - j) ω = a * (a ^ j * δ (t + 1 - j) ω) := fun j => by
      ring
    simp only [e1, e2, ← Finset.mul_sum]
    ring

/-! ### (17.8) with an infinite past -/

/-- Cochrane (2023), eq. (17.8), p. 400: with an infinite past, every bounded path satisfying
`π_{t+1} = π_t/(1+σκ) + σκ/(1+σκ) · i_t + δ_{t+1}` for bounded `i`, `δ` is
`π_{t+1} = σκ/(1+σκ) ∑ (1+σκ)^{−j} i_{t−j} + ∑ (1+σκ)^{−j} δ_{t+1−j}`. The statement is
pathwise (one history `ω` at a time); `δ` is the expectational error `π_{t+1} − E_t π_{t+1}`. -/
theorem eq_17_8 {σ κ Mπ Mi Mδ : ℝ} (hσκ : 0 < σ * κ) {π i δ : ℤ → ℝ}
    (hπ : ∀ s, |π s| ≤ Mπ) (hi : ∀ s, |i s| ≤ Mi) (hδ : ∀ s, |δ s| ≤ Mδ)
    (h : ∀ s, π (s + 1) = 1 / (1 + σ * κ) * π s + σ * κ / (1 + σ * κ) * i s + δ (s + 1))
    (t : ℤ) :
    π (t + 1) = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) +
      ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * δ (t + 1 - j) := by
  obtain ⟨ha0, ha1, hb0, -⟩ := coeff_17_7 hσκ
  set a := 1 / (1 + σ * κ)
  set b := σ * κ / (1 + σ * κ)
  have haa : |a| < 1 := by rw [abs_of_pos ha0]; exact ha1
  set w : ℤ → ℝ := fun s => b * i (s - 1) + δ s with hw
  have hwb : ∀ s, |w s| ≤ b * |Mi| + |Mδ| := fun s => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ((hδ s).trans (le_abs_self _)))
    rw [abs_mul, abs_of_pos hb0]
    exact mul_le_mul_of_nonneg_left ((hi _).trans (le_abs_self _)) hb0.le
  have hrec : ∀ s, π (s + 1) = a * π s + w (s + 1) := fun s => by
    rw [h s, hw]; simp only [add_sub_cancel_right]; ring
  rw [eq_backward_series haa hπ hwb hrec (t + 1)]
  have hg := summable_geometric_of_lt_one (abs_nonneg a) haa
  have hsi : Summable fun j : ℕ => a ^ j * i (t - j) :=
    Summable.of_norm_bounded (hg.mul_right Mi) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hi _) (pow_nonneg (abs_nonneg a) j)
  have hsd : Summable fun j : ℕ => a ^ j * δ (t + 1 - j) :=
    Summable.of_norm_bounded (hg.mul_right Mδ) fun j => by
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hδ _) (pow_nonneg (abs_nonneg a) j)
  rw [← tsum_mul_left, ← (hsi.mul_left b).tsum_add hsd]
  refine tsum_congr fun j => ?_
  rw [hw]
  simp only [show t + 1 - (j : ℤ) - 1 = t - j by ring]
  ring

/-! ### Figures 17.1 and 17.2 -/

/-- Cochrane (2023), Figure 17.1, p. 399: in the adaptive model, a permanent rise of the rate
from 0 to 1 at date 0 (with `π_{−1} = 0`) gives `π_t = 1 − (1 + σκ)^{t+1}`. -/
theorem fig17_1_path {σ κ : ℝ} {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ (fun _ => 0) (fun _ _ => 1) π) (t : ℕ) (ω : Ω) :
    π t ω = 1 - (1 + σ * κ) ^ (t + 1) := by
  rw [adaptive_peg h t ω]; ring

/-- Cochrane (2023), Figure 17.1 and p. 399, "inflation spirals downward": after the permanent
rate rise inflation tends to `−∞`. -/
theorem fig17_1_tendsto {σ κ : ℝ} (hσκ : 0 < σ * κ) {π : ℕ → Ω → ℝ}
    (h : AdaptiveEq σ κ (fun _ => 0) (fun _ _ => 1) π) (ω : Ω) :
    Tendsto (fun t => π t ω) atTop atBot := by
  have he : (fun t => π t ω) = fun t => 1 - (1 + σ * κ) ^ (t + 1) := funext fun t =>
    fig17_1_path h t ω
  rw [he]
  have := (tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < 1 + σ * κ)).comp
    (tendsto_add_atTop_nat 1)
  exact tendsto_atBot_add_const_left _ 1 (tendsto_neg_atTop_atBot.comp this)

/-- Cochrane (2023), Figure 17.1 ("less sticky"): with a larger `κ` inflation falls faster,
at every date. -/
theorem fig17_1_less_sticky {σ κ₁ κ₂ : ℝ} (hσ : 0 < σ) (hκ₁ : 0 < κ₁) (hκ : κ₁ < κ₂) (t : ℕ) :
    1 - (1 + σ * κ₂) ^ (t + 1) < 1 - (1 + σ * κ₁) ^ (t + 1) := by
  have : (1 + σ * κ₁) ^ (t + 1) < (1 + σ * κ₂) ^ (t + 1) :=
    pow_lt_pow_left₀ (by nlinarith) (by nlinarith) (Nat.succ_ne_zero t)
  linarith

/-- Cochrane (2023), Figure 17.2, p. 400: the `δ = 0` response to a permanent rise of the rate
from 0 to 1 at date 0, `π_t = 1 − (1 + σκ)^{−t}`, is an equilibrium of (17.7) (deterministic,
hence adapted under any expectation system), starting at `π_0 = 0`. -/
theorem fig17_2_solves (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0) :
    REModel 𝔼 σ κ (fun _ _ => 1) (fun t _ => 1 - (1 / (1 + σ * κ)) ^ t) := by
  refine ⟨fun t => 𝔼.const t _, fun t ω => ?_⟩
  rw [𝔼.const]
  simp only [pow_succ]
  field_simp
  ring

/-- Cochrane (2023), Figure 17.2, p. 400, "the interest-rate rise eventually brings inflation up
to meet it": the `δ = 0` response rises strictly. -/
theorem fig17_2_strictMono {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    StrictMono fun t : ℕ => 1 - (1 / (1 + σ * κ)) ^ t := by
  obtain ⟨ha0, ha1, -, -⟩ := coeff_17_7 hσκ
  intro m n hmn
  have := pow_lt_pow_right_of_lt_one₀ ha0 ha1 hmn
  simp only
  linarith

/-- Cochrane (2023), Figure 17.2, p. 400: the `δ = 0` response converges to the new rate 1. -/
theorem fig17_2_tendsto {σ κ : ℝ} (hσκ : 0 < σ * κ) :
    Tendsto (fun t : ℕ => 1 - (1 / (1 + σ * κ)) ^ t) atTop (𝓝 1) := by
  obtain ⟨ha0, ha1, -, -⟩ := coeff_17_7 hσκ
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).const_sub (1 : ℝ)

/-- Cochrane (2023), Figure 17.2, p. 400, "less sticky": with a larger `κ` the response is
higher at every date `t ≥ 1` (the dynamics happen faster). -/
theorem fig17_2_less_sticky {σ κ₁ κ₂ : ℝ} (hσ : 0 < σ) (hκ₁ : 0 < κ₁) (hκ : κ₁ < κ₂) {t : ℕ}
    (ht : t ≠ 0) :
    1 - (1 / (1 + σ * κ₁)) ^ t < 1 - (1 / (1 + σ * κ₂)) ^ t := by
  have h1 : 0 < 1 + σ * κ₁ := by nlinarith
  have hlt : 1 / (1 + σ * κ₂) < 1 / (1 + σ * κ₁) :=
    one_div_lt_one_div_of_lt h1 (by nlinarith)
  have := pow_lt_pow_left₀ hlt (one_div_pos.mpr (by nlinarith)).le ht
  linarith

/-- Cochrane (2023), p. 400, "The model smoothly approaches the frictionless result, in which
`π_1 = 1` and stays there": as `κ → ∞` the response at every date `t ≥ 1` tends to 1. -/
theorem fig17_2_frictionless_limit {σ : ℝ} (hσ : 0 < σ) {t : ℕ} (ht : t ≠ 0) :
    Tendsto (fun κ : ℝ => 1 - (1 / (1 + σ * κ)) ^ t) atTop (𝓝 1) := by
  have h1 : Tendsto (fun κ : ℝ => 1 + σ * κ) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (Tendsto.const_mul_atTop hσ tendsto_id)
  have h2 : Tendsto (fun κ : ℝ => 1 / (1 + σ * κ)) atTop (𝓝 0) := by
    exact h1.inv_tendsto_atTop.congr fun κ => by simp [one_div]
  have h3 := (h2.pow t).const_sub (1 : ℝ)
  rwa [zero_pow ht, sub_zero] at h3

/-- Cochrane (2023), Figure 17.2, p. 400 (dashed lines): after the date-1 jump, every value
`π_1 = c` gives a path `π_{t+1} = 1 + (c − 1)(1+σκ)^{−t}` obeying the perfect-foresight
recursion of (17.7) from date 1 on, and every such path converges to 1. -/
theorem fig17_2_dashed {σ κ : ℝ} (hσκ : 0 < σ * κ) (c : ℝ) :
    (∀ t : ℕ, 1 + (c - 1) * (1 / (1 + σ * κ)) ^ (t + 1) =
      1 / (1 + σ * κ) * (1 + (c - 1) * (1 / (1 + σ * κ)) ^ t) + σ * κ / (1 + σ * κ) * 1) ∧
      Tendsto (fun t : ℕ => 1 + (c - 1) * (1 / (1 + σ * κ)) ^ t) atTop (𝓝 1) := by
  obtain ⟨ha0, ha1, -, -⟩ := coeff_17_7 hσκ
  refine ⟨fun t => ?_, ?_⟩
  · have : 1 + σ * κ ≠ 0 := by linarith
    rw [pow_succ]; field_simp; ring
  · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).const_mul (c - 1)).const_add
      (1 : ℝ)

/-- Cochrane (2023), p. 402 (the frictionless limit of (17.7)): as `κ → ∞` the coefficients
`1/(1+σκ)` and `σκ/(1+σκ)` of (17.7) tend to 0 and 1, giving the frictionless Fisher
relation `E_t π_{t+1} = i_t`. -/
theorem tendsto_coeff_17_7 {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun κ : ℝ => 1 / (1 + σ * κ)) atTop (𝓝 0) ∧
      Tendsto (fun κ : ℝ => σ * κ / (1 + σ * κ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun κ : ℝ => 1 + σ * κ) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (Tendsto.const_mul_atTop hσ tendsto_id)
  have h2 : Tendsto (fun κ : ℝ => 1 / (1 + σ * κ)) atTop (𝓝 0) := by
    exact h1.inv_tendsto_atTop.congr fun κ => by simp [one_div]
  refine ⟨h2, ?_⟩
  have h3 := h2.const_sub (1 : ℝ)
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with κ hκ
  have : 1 + σ * κ ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### Expected rises and fiscal selection (p. 401) -/

/-- Cochrane (2023), p. 401, "The response to an expected interest-rate rise is the same, only
that there can be no jump at time 1": if everything is known at the announcement date 0, all
later expectational errors are zero. -/
theorem no_surprise_of_known (𝔼 : ExpectationSystem Ω) {π : ℕ → Ω → ℝ}
    (hk : ∀ t, 𝔼.E 0 (π t) = π t) (t : ℕ) : π (t + 1) - 𝔼.E t (π (t + 1)) = 0 := by
  rw [← hk (t + 1), 𝔼.known (Nat.zero_le t), sub_self]

/-- Cochrane (2023), p. 401: in an equilibrium of (17.7) in which everything is known at the
announcement date 0, the path is pinned down by `π_0` (the only possible jump comes on the
announcement date). -/
theorem eq_reFamily_of_known {𝔼 : ExpectationSystem Ω} {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    {i π : ℕ → Ω → ℝ} (hπ : REModel 𝔼 σ κ i π) (hk : ∀ t, 𝔼.E 0 (π t) = π t) :
    π = reFamily σ κ (π 0) i 0 := by
  have he : reErr 𝔼 π = 0 := by
    funext t ω
    cases t with
    | zero => rfl
    | succ t => exact congrFun (no_surprise_of_known 𝔼 hk t) ω
  rw [← he]
  exact eq_reFamily h hπ

/-- Cochrane (2023), p. 401, "Active fiscal policy likewise selects one equilibrium": if fiscal
policy fixes unexpected inflation `ΔE_{t+1} π_{t+1} = −ε_{t+1}` (a fiscal shock `ε`, adapted with
mean zero) and inflation at date 0, the equilibrium of (17.7) is unique. -/
theorem fiscal_selects (𝔼 : ExpectationSystem Ω) {σ κ : ℝ} (h : 1 + σ * κ ≠ 0)
    {π0 : Ω → ℝ} {i ε : ℕ → Ω → ℝ} (hπ0 : 𝔼.E 0 π0 = π0) (hi : 𝔼.Adapted i)
    (hε : 𝔼.Adapted ε) (hmd : ∀ t, 𝔼.E t (ε (t + 1)) = 0) :
    ∃! π, REModel 𝔼 σ κ i π ∧ π 0 = π0 ∧ ∀ t, π (t + 1) - 𝔼.E t (π (t + 1)) = -ε (t + 1) := by
  have hnε : 𝔼.Adapted (-ε) := fun t => by rw [Pi.neg_apply, map_neg, hε t]
  have hmd' : ∀ t, 𝔼.E t ((-ε) (t + 1)) = 0 := fun t => by
    rw [Pi.neg_apply, map_neg, hmd t, neg_zero]
  obtain ⟨hs, herr⟩ := reFamily_solves 𝔼 h hπ0 hi hnε hmd'
  refine ⟨reFamily σ κ π0 i (-ε), ⟨hs, rfl, fun t => funext fun ω => herr t ω⟩, ?_⟩
  rintro π ⟨hπ, h0, hd⟩
  have h17 := ((reModel_iff_17_7 𝔼 h i π).mp hπ).2
  funext t ω
  induction t with
  | zero => rw [h0]; rfl
  | succ t ih =>
    rw [reFamily_succ, ← ih]
    have := congrFun (hd t) ω
    simp only [Pi.sub_apply, Pi.neg_apply] at this
    rw [h17 t ω] at this
    simp only [Pi.neg_apply]
    linarith

end Cochrane.KeynesianStickyPrices.StaticIS
