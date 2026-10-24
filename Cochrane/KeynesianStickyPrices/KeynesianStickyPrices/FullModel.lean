/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.SharedTools

/-!
# Full-model responses: inflation as a two-sided moving average of interest rates

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4 "Full-model
responses" and §17.4.1 "Interest rates and inflation", eqs. (17.15)–(17.18), pp. 407–410, with
Figures 17.5–17.6; the two-sided moving average is eq. (5.5), p. 119, and Online Appendix A1,
§1.7, pp. 569–571.

## The model

`Model` is (17.15)–(17.17) with IS and Phillips-curve disturbances, for an arbitrary
`ExpectationSystem`. Eliminating output and the real rate gives (17.18) (`eq_17_18`, with
disturbances `eq_17_18_shocks`): with `κ ≠ 0` the model holds iff `r_t = i_t − E_t π_{t+1}`,
`κ x_t = π_t − β E_t π_{t+1} − u_{π,t}` and
`σκ i_t = −β E_t π_{t+2} + (1 + β + σκ) E_t π_{t+1} − π_t + (u_{π,t} − E_t u_{π,t+1}) + κ u_{x,t}`.

## Perfect foresight: the two-sided solution

Under perfect foresight (sequences `ℕ → ℝ`, `pf_model_iff` links them to the
`perfectForesight` expectation system) the roots `λ₁ > 1 > λ₂ > 0` of
`λ² − (1 + β + σκ) λ + β` (restated from the Chapter 5 project `StickyPriceFiscal`) factor the
second-order equation (`second_iff_factor`): bounded inflation solves (17.18) iff
`λ₁ π_{t+1} = π_t + σκ F_t` with `F_t = ∑_{k≥0} λ₂ᵏ i_{t+k}`. Hence (`pf_existsUnique`) for
bounded `i` the bounded equilibria are exactly the paths `path p`, one for each initial inflation
`π_0 = p` — the single multiple-equilibrium jump of perfect foresight. The equilibrium with no
past surprises is the two-sided moving average (5.5),
`π_t = c [∑_{j<t} λ₁^{−j} i_{t−1−j} + λ₂ F_t]`, `c = σκ/(λ₁ − λ₂)` (`twoSided_eq`).
Long-run neutrality: if `i_t → ī` then every bounded equilibrium has `π_t → ī` and
`x_t → (1 − β) ī/κ` (`tendsto_pi`, `tendsto_x`).

## Figure 17.5 (permanent rise announced at date 0, effective from date `T`)

For the step `i_t = 1{t ≥ T}`: `F_step` (`F_t = λ₂^{T−t}/(1 − λ₂)`); the no-surprise equilibrium
`antPath` jumps at the announcement (`antPath_zero_pos`: "the δ₁ = 0 equilibrium
already had a little jump", p. 410), rises before the rate rises (`antPath_le_T`:
`π_t = c λ₂^{T−t+1}/(1 − λ₂)` for `t ≤ T`), is positive, strictly increasing, below one and
converges to one (`antPath_pos`, `antPath_strictMono`, `antPath_lt_one`,
`antPath_tendsto_one`). Output falls up to and including the date of the rise
(`antPath_x_neg`), because output is low exactly when inflation is rising faster than `1/β`
(`x_neg_iff`), and tends to `(1 − β)/κ ≥ 0` (`antPath_x_tendsto`). For **every** initial
inflation, an announced rise raises inflation at every date before (and after) the rise relative
to no rise (`rise_raises_inflation`); the response to a surprise rise joins the anticipated
response at the date of the rise (`dashed_joins_solid`). Fig. 17.6 (p. 410): every initial
jump, positive (A, B), zero (D) or negative (E), is an equilibrium and converges to one
(`fig17_6_any_jump`).

## Figure 17.5: the rise anticipated from the infinite past (ℤ-indexed paths)

On `ℤ` (`SecondZ`, `stepZ`), the permanent rise at date `T` known forever has exactly one
bounded perfect-foresight inflation path (`zPath_existsUnique`; uniqueness for every bounded rate
path, `secondZ_unique`), in closed form `zPath`: `π_t = c λ₂^{T−t+1}/(1 − λ₂)` for `t ≤ T`,
`π_t = 1 − (1 − c λ₂/(1 − λ₂)) λ₁^{−(t−T)}` for `t ≥ T`. It depends only on `t − T`
(`zPath_shift`). The no-surprise response announced at date 0 coincides with it from the
announcement on (`zPath_eq_antPath`, `antPath_eq_zPath_shift`), and as the announcement
recedes every response, whatever its initial jump, converges to it date by date
(`tendsto_zPath`).
-/

namespace Cochrane.KeynesianStickyPrices.FullModel

open Filter Topology
open SharedTools (tendsto_zero_of_stable fwd_sum_props fwd_sum_tendsto int_homog_zero)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The model (17.15)–(17.17) -/

/-- Cochrane (2023), eq. (17.15), p. 407: the IS curve `x_t = E_t x_{t+1} − σ r_t + u_{x,t}`. -/
def IS (σ : ℝ) (ux r x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • r t + ux t

/-- Cochrane (2023), eq. (17.16), p. 407: the Fisher equation `i_t = r_t + E_t π_{t+1}`. -/
def Fisher (i r π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, i t = r t + 𝔼.E t (π (t + 1))

/-- Cochrane (2023), eq. (17.17), p. 407: the Phillips curve
`π_t = β E_t π_{t+1} + κ x_t + u_{π,t}`. -/
def PC (β κ : ℝ) (uπ x π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = β • 𝔼.E t (π (t + 1)) + κ • x t + uπ t

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407: the full new-Keynesian model with IS and
Phillips-curve disturbances `u_x`, `u_π`. -/
def Model (σ β κ : ℝ) (ux uπ i r x π : ℕ → Ω → ℝ) : Prop :=
  IS 𝔼 σ ux r x ∧ Fisher 𝔼 i r π ∧ PC 𝔼 β κ uπ x π

/-- Cochrane (2023), eq. (17.16), p. 407: the Fisher equation defines the real rate,
`r_t = i_t − E_t π_{t+1}`. -/
theorem fisher_iff (i r π : ℕ → Ω → ℝ) :
    Fisher 𝔼 i r π ↔ r = fun t => i t - 𝔼.E t (π (t + 1)) := by
  constructor
  · intro h
    funext t
    rw [h t]
    abel
  · intro h t
    subst h
    exact (sub_add_cancel _ _).symm

/-- Cochrane (2023), eq. (17.18), p. 408, with the disturbances of (17.15)–(17.17) (the form
behind (17.27), p. 418): for `κ ≠ 0` (and any `σ`) the model holds iff the real rate is
`r_t = i_t − E_t π_{t+1}`, output is given by the Phillips curve, and
`σκ i_t = −β E_t π_{t+2} + (1 + β + σκ) E_t π_{t+1} − π_t + (u_{π,t} − E_t u_{π,t+1})
  + κ u_{x,t}`. -/
theorem eq_17_18_shocks {σ β κ : ℝ} (hκ : κ ≠ 0) {ux uπ i r x π : ℕ → Ω → ℝ} :
    Model 𝔼 σ β κ ux uπ i r x π ↔
      (r = fun t => i t - 𝔼.E t (π (t + 1))) ∧
      (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)) - uπ t)) ∧
      ∀ t, (σ * κ) • i t = -β • 𝔼.E t (π (t + 2)) + (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) -
        π t + (uπ t - 𝔼.E t (uπ (t + 1))) + κ • ux t := by
  have hkk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  constructor
  · rintro ⟨his, hf, hpc⟩
    have hr := (fisher_iff 𝔼 i r π).mp hf
    refine ⟨hr, fun t => ?_, fun t => ?_⟩
    · funext ω
      have h := congrFun (hpc t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h ⊢
      have hk : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ
      linear_combination (-κ⁻¹) * h - x t ω * hk
    · funext ω
      have h1 := congrFun (his t) ω
      have h2 := congrFun (hpc t) ω
      have h3 := congrFun (congrArg (𝔼.E t) (hpc (t + 1))) ω
      rw [map_add, map_add, map_smul, map_smul, 𝔼.tower (Nat.le_succ t)] at h3
      rw [hr] at h1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
        neg_mul] at h1 h2 h3 ⊢
      linear_combination κ * h1 + h2 - h3
  · rintro ⟨hr, hx, hsec⟩
    have hf : Fisher 𝔼 i r π := (fisher_iff 𝔼 i r π).mpr hr
    have hpc : PC 𝔼 β κ uπ x π := by
      intro t
      funext ω
      have h := congrFun (hx t) ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h ⊢
      rw [h]
      linear_combination (-(π t ω - β * 𝔼.E t (π (t + 1)) ω - uπ t ω)) * hkk
    refine ⟨fun t => ?_, hf, hpc⟩
    funext ω
    have h1 := congrFun (hsec t) ω
    have h2 := congrFun (hpc t) ω
    have h3 := congrFun (congrArg (𝔼.E t) (hpc (t + 1))) ω
    rw [map_add, map_add, map_smul, map_smul, 𝔼.tower (Nat.le_succ t)] at h3
    rw [hr]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      neg_mul] at h1 h2 h3 ⊢
    apply mul_left_cancel₀ hκ
    linear_combination -h2 + h3 + h1

/-- Cochrane (2023), eq. (17.18), p. 408: with no disturbances, eliminating `x_t` from
(17.15)–(17.17) gives `i_t = (1/(σκ)) [−β E_t π_{t+2} + (1 + β + σκ) E_t π_{t+1} − π_t]`. -/
theorem eq_17_18 {σ β κ : ℝ} (hσ : σ ≠ 0) (hκ : κ ≠ 0) {i r x π : ℕ → Ω → ℝ}
    (h : Model 𝔼 σ β κ 0 0 i r x π) (t : ℕ) :
    i t = (σ * κ)⁻¹ • (-β • 𝔼.E t (π (t + 2)) + (1 + β + σ * κ) • 𝔼.E t (π (t + 1)) - π t) := by
  have h3 := ((eq_17_18_shocks 𝔼 hκ).mp h).2.2 t
  simp only [Pi.zero_apply, map_zero, sub_zero, add_zero, smul_zero] at h3
  rw [← h3, smul_smul, inv_mul_cancel₀ (mul_ne_zero hσ hκ), one_smul]


/-! ### Perfect foresight -/

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, under perfect foresight and with no
disturbances (the setting of Figs. 17.5–17.7): `x_t = x_{t+1} − σ(i_t − π_{t+1})` and
`π_t = β π_{t+1} + κ x_t`, for sequences. -/
def PFEqm (σ β κ : ℝ) (i x π : ℕ → ℝ) : Prop :=
  ∀ t, x t = x (t + 1) - σ * (i t - π (t + 1)) ∧ π t = β * π (t + 1) + κ * x t

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407: `PFEqm` is the model under the
`perfectForesight` expectation system (with zero disturbances), the real rate being
`r_t = i_t − π_{t+1}`. -/
theorem pf_model_iff {σ β κ : ℝ} (i r x π : ℕ → ℝ) :
    Model perfectForesight σ β κ 0 0 (fun t _ => i t) (fun t _ => r t) (fun t _ => x t)
        (fun t _ => π t) ↔
      (∀ t, r t = i t - π (t + 1)) ∧ PFEqm σ β κ i x π := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun t => ?_, fun t => ⟨?_, ?_⟩⟩
    · have := congrFun (h2 t) ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply] at this
      linarith
    · have e1 := congrFun (h1 t) ()
      have e2 := congrFun (h2 t) ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
      rw [e1, show r t = i t - π (t + 1) by linarith]
      ring
    · have e3 := congrFun (h3 t) ()
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply] at e3
      linarith
  · rintro ⟨hr, h⟩
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩ <;> funext u <;>
      simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    · rw [hr t]
      linarith [(h t).1]
    · rw [hr t]
      ring
    · linarith [(h t).2]

/-- A real sequence is bounded. -/
def BoundedS (z : ℕ → ℝ) : Prop := ∃ M, ∀ t, |z t| ≤ M

/-- Cochrane (2023), eq. (17.18), p. 408, under perfect foresight:
`π_t − (1 + β + σκ) π_{t+1} + β π_{t+2} = −σκ i_t`. -/
def Second (σ β κ : ℝ) (i π : ℕ → ℝ) : Prop :=
  ∀ t, π t - (1 + β + σ * κ) * π (t + 1) + β * π (t + 2) = -(σ * κ) * i t

/-- Cochrane (2023), eq. (17.18), p. 408 (perfect foresight): for `κ ≠ 0`, `(x, π)` is an
equilibrium iff `x_t = (π_t − β π_{t+1})/κ` and inflation solves (17.18). -/
theorem pfEqm_iff_second {σ β κ : ℝ} (hκ : κ ≠ 0) (i x π : ℕ → ℝ) :
    PFEqm σ β κ i x π ↔ (∀ t, x t = (π t - β * π (t + 1)) / κ) ∧ Second σ β κ i π := by
  constructor
  · intro h
    refine ⟨fun t => ?_, fun t => ?_⟩
    · rw [eq_div_iff hκ]
      linarith [(h t).2]
    · obtain ⟨h1, h2⟩ := h t
      have h3 := (h (t + 1)).2
      linear_combination h2 - h3 + κ * h1
  · rintro ⟨hx, hs⟩ t
    refine ⟨?_, ?_⟩
    · rw [hx t, hx (t + 1)]
      field_simp
      linear_combination hs t
    · rw [hx t]
      field_simp
      ring

/-! ### The roots (restated from the Chapter 5 project `StickyPriceFiscal`) -/

/-- Cochrane (2023), eq. (5.6), p. 119 (restated from the Chapter 5 project): the larger root
`λ₁ = [(1 + β + σκ) + √((1 + β + σκ)² − 4β)]/2` of `λ² − (1 + β + σκ) λ + β`. -/
noncomputable def lam1 (σ β κ : ℝ) : ℝ :=
  (1 + β + σ * κ + Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119 (restated from the Chapter 5 project): the smaller root
`λ₂ = [(1 + β + σκ) − √((1 + β + σκ)² − 4β)]/2`. -/
noncomputable def lam2 (σ β κ : ℝ) : ℝ :=
  (1 + β + σ * κ - Real.sqrt ((1 + β + σ * κ) ^ 2 - 4 * β)) / 2

/-- Cochrane (2023), eq. (5.6), p. 119: the discriminant is positive when `σκ > 0`, `β > 0`. -/
theorem disc_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    0 < (1 + β + σ * κ) ^ 2 - 4 * β := by
  nlinarith [sq_nonneg (1 - β), sq_nonneg (σ * κ)]

/-- Cochrane (2023), A1 p. 570: `λ₁ + λ₂ = 1 + β + σκ`. -/
theorem lam_sum (σ β κ : ℝ) : lam1 σ β κ + lam2 σ β κ = 1 + β + σ * κ := by
  unfold lam1 lam2; ring

/-- Cochrane (2023), A1 p. 570: `λ₁ λ₂ = β`. -/
theorem lam_prod {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    lam1 σ β κ * lam2 σ β κ = β := by
  unfold lam1 lam2
  have h := Real.sq_sqrt (disc_pos ha hβ).le
  nlinarith [h]

/-- Cochrane (2023), A1 p. 570: `σκ = (λ₁ − 1)(1 − λ₂)`. -/
theorem sigma_kappa_eq {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    σ * κ = (lam1 σ β κ - 1) * (1 - lam2 σ β κ) := by
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  linear_combination -h1 + h2

/-- Cochrane (2023), eq. (5.6), p. 119: `λ₂ < λ₁`. -/
theorem lam2_lt_lam1 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    lam2 σ β κ < lam1 σ β κ := by
  unfold lam1 lam2
  have := Real.sqrt_pos.mpr (disc_pos ha hβ)
  linarith

/-- Cochrane (2023), p. 408: `λ₁ > 1`. -/
theorem one_lt_lam1 {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 1 < lam1 σ β κ := by
  by_contra hc
  push Not at hc
  have h := sigma_kappa_eq ha hβ
  have h2 := lam2_lt_lam1 ha hβ
  nlinarith

/-- Cochrane (2023), p. 408: `λ₂ < 1`. -/
theorem lam2_lt_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : lam2 σ β κ < 1 := by
  have h := sigma_kappa_eq ha hβ
  have h1 := one_lt_lam1 ha hβ
  by_contra hc
  push Not at hc
  nlinarith

/-- Cochrane (2023), p. 408: `λ₂ > 0`. -/
theorem lam2_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 0 < lam2 σ β κ := by
  have h := lam_prod ha hβ
  have h1 := one_lt_lam1 ha hβ
  by_contra hc
  push Not at hc
  nlinarith

/-! ### Forward sums of the interest rate -/

/-- Cochrane (2023), eq. (5.5), p. 119: the forward-solved factor `F_t = ∑_{k≥0} qᵏ i_{t+k}`. -/
noncomputable def F (q : ℝ) (i : ℕ → ℝ) (t : ℕ) : ℝ := ∑' k, q ^ k * i (t + k)

/-- The forward sum converges for bounded `i` and `0 ≤ q < 1`. -/
theorem F_summable {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℕ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℕ) : Summable (fun k => q ^ k * i (t + k)) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0 hq1).mul_right M)
    (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hq0]
  exact mul_le_mul_of_nonneg_left (hi (t + k)) (pow_nonneg hq0 k)

/-- The forward sum satisfies `F_t = i_t + q F_{t+1}` (from `SharedTools.fwd_sum_props`). -/
theorem F_rec {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℕ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℕ) : F q i t = i t + q * F q i (t + 1) :=
  (fwd_sum_props (by rwa [abs_of_nonneg hq0]) hi).1 t

/-- The forward sum is bounded by `M/(1 − q)` (from `SharedTools.fwd_sum_props`). -/
theorem F_bound {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℕ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (t : ℕ) : |F q i t| ≤ M / (1 - q) := by
  have h := (fwd_sum_props (by rwa [abs_of_nonneg hq0]) hi).2 t
  rwa [abs_of_nonneg hq0] at h

/-- A bounded solution of `d_t = q d_{t+1}` with `|q| < 1` vanishes. -/
theorem homog_zero {q : ℝ} (hq : |q| < 1) {d : ℕ → ℝ} (hd : ∀ t, d t = q * d (t + 1))
    (hb : BoundedS d) : d = 0 := by
  obtain ⟨M, hM⟩ := hb
  have hit : ∀ t k, d t = q ^ k * d (t + k) := by
    intro t k
    induction k with
    | zero => simp
    | succ k ih => rw [ih, hd (t + k), ← add_assoc, pow_succ]; ring
  funext t
  have hle : ∀ k, |d t| ≤ |q| ^ k * M := fun k => by
    rw [hit t k, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hM (t + k)) (pow_nonneg (abs_nonneg q) k)
  have hlim : Tendsto (fun k => |q| ^ k * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg q) hq).mul_const M
  have h0 : |d t| ≤ 0 := ge_of_tendsto' hlim hle
  simpa using h0

/-- The forward sum is the unique bounded solution of `G_t = i_t + q G_{t+1}`. -/
theorem F_unique {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i G : ℕ → ℝ} (hi : ∀ t, |i t| ≤ M)
    (hG : ∀ t, G t = i t + q * G (t + 1)) (hGb : BoundedS G) : G = F q i := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  obtain ⟨MG, hMG⟩ := hGb
  have h := homog_zero hq (d := fun t => G t - F q i t)
    (fun t => by rw [hG t, F_rec hq0 hq1 hi t]; ring)
    ⟨MG + M / (1 - q), fun t => (abs_sub _ _).trans (add_le_add (hMG t) (F_bound hq0 hq1 hi t))⟩
  funext t
  have := congrFun h t
  simp only [Pi.zero_apply] at this
  linarith


/-! ### Factoring the lag polynomial and the family of bounded equilibria -/

/-- Cochrane (2023), A1 §1.7, p. 570: the factorisation
`(π_t − λ₁ π_{t+1}) − λ₂ (π_{t+1} − λ₁ π_{t+2}) = π_t − (1 + β + σκ) π_{t+1} + β π_{t+2}`. -/
theorem factor_identity {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (π : ℕ → ℝ) (t : ℕ) :
    (π t - lam1 σ β κ * π (t + 1)) - lam2 σ β κ * (π (t + 1) - lam1 σ β κ * π (t + 2)) =
      π t - (1 + β + σ * κ) * π (t + 1) + β * π (t + 2) := by
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  linear_combination (-(π (t + 1))) * h1 + π (t + 2) * h2

/-- Cochrane (2023), eq. (5.5), p. 119, and A1 §1.7, p. 570 (perfect foresight): for bounded
`i` and bounded `π`, (17.18) holds iff `λ₁ π_{t+1} = π_t + σκ F_t`,
`F_t = ∑_{k≥0} λ₂ᵏ i_{t+k}` (the unstable factor solved forward, the stable one backward). -/
theorem second_iff_factor {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hπ : BoundedS π) :
    Second σ β κ i π ↔ ∀ t, lam1 σ β κ * π (t + 1) = π t + σ * κ * F (lam2 σ β κ) i t := by
  have hl0 := (lam2_pos ha hβ).le
  have hl1 := lam2_lt_one ha hβ
  constructor
  · intro hs
    obtain ⟨Mπ, hMπ⟩ := hπ
    have hq : |lam2 σ β κ| < 1 := by rw [abs_of_nonneg hl0]; exact hl1
    have hd := homog_zero hq
      (d := fun t => π t - lam1 σ β κ * π (t + 1) + σ * κ * F (lam2 σ β κ) i t)
      (fun t => by
        have e := hs t
        have f := F_rec hl0 hl1 hi t
        have fi := factor_identity ha hβ π t
        linear_combination fi + e + (σ * κ) * f)
      ⟨Mπ + |lam1 σ β κ| * Mπ + |σ * κ| * (M / (1 - lam2 σ β κ)), fun t => by
        have h1 := hMπ t
        have h2 := hMπ (t + 1)
        have h3 := F_bound hl0 hl1 hi t
        calc |π t - lam1 σ β κ * π (t + 1) + σ * κ * F (lam2 σ β κ) i t|
            ≤ |π t| + |lam1 σ β κ| * |π (t + 1)| + |σ * κ| * |F (lam2 σ β κ) i t| := by
              rw [← abs_mul, ← abs_mul]
              exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
          _ ≤ Mπ + |lam1 σ β κ| * Mπ + |σ * κ| * (M / (1 - lam2 σ β κ)) := by gcongr⟩
    intro t
    have := congrFun hd t
    simp only [Pi.zero_apply] at this
    linarith
  · intro hf t
    have e1 := hf t
    have e2 := hf (t + 1)
    have f := F_rec hl0 hl1 hi t
    have fi := factor_identity ha hβ π t
    linear_combination -fi - e1 + lam2 σ β κ * e2 - (σ * κ) * f

/-- Cochrane (2023), p. 408 and eq. (5.5): the perfect-foresight equilibrium path with initial
inflation `π_0 = p`, `π_{t+1} = (π_t + σκ F_t)/λ₁`. -/
noncomputable def path (σ β κ : ℝ) (i : ℕ → ℝ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | t + 1 => (path σ β κ i p t + σ * κ * F (lam2 σ β κ) i t) / lam1 σ β κ

/-- The path satisfies the factored equation `λ₁ π_{t+1} = π_t + σκ F_t`. -/
theorem path_factor {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (i : ℕ → ℝ) (p : ℝ) (t : ℕ) :
    lam1 σ β κ * path σ β κ i p (t + 1) = path σ β κ i p t + σ * κ * F (lam2 σ β κ) i t := by
  have h1 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  simp only [path]
  field_simp

/-- Cochrane (2023), pp. 137–138 (restated from the Chapter 5 project): if
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

/-- The path is bounded for bounded `i`. -/
theorem path_bounded {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (p : ℝ) : BoundedS (path σ β κ i p) := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hM : 0 ≤ M := (abs_nonneg _).trans (hi 0)
  have hc1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have h2p : 0 < 1 - lam2 σ β κ := by linarith
  have hnn : 0 ≤ (lam1 σ β κ)⁻¹ * (σ * κ * (M / (1 - lam2 σ β κ))) := by positivity
  refine ⟨|p| + (lam1 σ β κ)⁻¹ * (σ * κ * (M / (1 - lam2 σ β κ))) / (1 - (lam1 σ β κ)⁻¹),
    bounded_of_rec (inv_nonneg.mpr hl0.le) hc1 hnn le_rfl (fun t => ?_)⟩
  have hF := F_bound h20 h21 hi t
  simp only [path]
  rw [div_eq_inv_mul, abs_mul, abs_of_pos (inv_pos.mpr hl0), ← mul_add]
  gcongr
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos ha]
  gcongr

/-- Cochrane (2023), p. 408 and eq. (5.5) (perfect foresight): for bounded `i` and every
initial inflation `p`, there is exactly one bounded solution of (17.18) with `π_0 = p`. Bounded
equilibria are indexed by the single initial jump. -/
theorem pf_existsUnique {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (p : ℝ) :
    ∃! π : ℕ → ℝ, BoundedS π ∧ Second σ β κ i π ∧ π 0 = p := by
  refine ⟨path σ β κ i p, ⟨path_bounded ha hβ hi p,
    (second_iff_factor ha hβ hi (path_bounded ha hβ hi p)).mpr (path_factor ha hβ i p), rfl⟩,
    fun π ⟨hb, hs, h0⟩ => ?_⟩
  have hf := (second_iff_factor ha hβ hi hb).mp hs
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  funext t
  induction t with
  | zero => exact h0
  | succ t ih =>
    apply mul_left_cancel₀ hl0
    rw [hf t, path_factor ha hβ i p t, ih]

/-- Cochrane (2023), §17.4.1, p. 408 (perfect foresight): for `σκ > 0`, `κ ≠ 0`, `β > 0` and
bounded `i`, a bounded `(x, π)` is an equilibrium iff `x_t = (π_t − β π_{t+1})/κ` and `π` is the
path with initial value `π_0`. -/
theorem pf_eqm_iff {σ β κ M : ℝ} (ha : 0 < σ * κ) (hκ : κ ≠ 0) (hβ : 0 < β) {i x π : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hb : BoundedS π) :
    PFEqm σ β κ i x π ↔
      (∀ t, x t = (π t - β * π (t + 1)) / κ) ∧ π = path σ β κ i (π 0) := by
  rw [pfEqm_iff_second hκ]
  refine and_congr_right fun _ => ⟨fun hs => ?_, fun h => ?_⟩
  · obtain ⟨_, _, huniq⟩ := pf_existsUnique ha hβ hi (π 0)
    exact huniq π ⟨hb, hs, rfl⟩ ▸ (huniq _ ⟨path_bounded ha hβ hi _,
      (second_iff_factor ha hβ hi (path_bounded ha hβ hi _)).mpr (path_factor ha hβ i _),
      rfl⟩).symm
  · rw [h]
    exact (second_iff_factor ha hβ hi (path_bounded ha hβ hi _)).mpr (path_factor ha hβ i _)

/-! ### Long-run neutrality -/

/-- A stable recursion `y_{t+1} = q y_t + b_t`, `0 ≤ q < 1`, with `b_t → B` has
`y_t → B/(1 − q)` (from `SharedTools.tendsto_zero_of_stable`). -/
theorem tendsto_of_rec {q B : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {y b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 B)) (hy : ∀ t, y (t + 1) = q * y t + b t) :
    Tendsto y atTop (𝓝 (B / (1 - q))) := by
  have h1q : 1 - q ≠ 0 := by linarith
  have hq : |q| < 1 := by rwa [abs_of_nonneg hq0]
  have he := tendsto_zero_of_stable hq (x := fun t => y t - B / (1 - q))
    (f := fun t => b t - B) (fun t => by
      rw [hy t]
      field_simp
      ring) (by simpa using hb.sub_const B)
  simpa using he.add_const (B / (1 - q))

/-- If `i_t → ī` (bounded `i`), the forward sum `F_t = ∑ qᵏ i_{t+k}` tends to `ī/(1 − q)` (from
`SharedTools.fwd_sum_tendsto`). -/
theorem tendsto_F {q M ib : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hl : Tendsto i atTop (𝓝 ib)) :
    Tendsto (F q i) atTop (𝓝 (ib / (1 - q))) :=
  fwd_sum_tendsto (by rwa [abs_of_nonneg hq0]) hi hl

/-- Cochrane (2023), §17.4.1, p. 408 ("long-run impulse response = 1"; A1 p. 570): if the
interest rate converges, `i_t → ī`, then in **every** bounded perfect-foresight equilibrium
inflation converges to the same value, `π_t → ī`. -/
theorem tendsto_pi {σ β κ M ib : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hl : Tendsto i atTop (𝓝 ib)) (hb : BoundedS π)
    (hs : Second σ β κ i π) : Tendsto π atTop (𝓝 ib) := by
  have hf := (second_iff_factor ha hβ hi hb).mp hs
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hF := tendsto_F h20 h21 hi hl
  have hrec : ∀ t, π (t + 1) =
      (lam1 σ β κ)⁻¹ * π t + (lam1 σ β κ)⁻¹ * (σ * κ) * F (lam2 σ β κ) i t := fun t => by
    rw [mul_assoc, ← mul_add, ← hf t, ← mul_assoc, inv_mul_cancel₀ hl0.ne', one_mul]
  have h := tendsto_of_rec (inv_nonneg.mpr hl0.le) (inv_lt_one_of_one_lt₀ hl1)
    (hF.const_mul ((lam1 σ β κ)⁻¹ * (σ * κ))) hrec
  convert h using 2
  have hsk := sigma_kappa_eq ha hβ
  have h2 : 1 - lam2 σ β κ ≠ 0 := by linarith
  have h3 : lam1 σ β κ - 1 ≠ 0 := by linarith
  field_simp
  rw [mul_assoc ib σ κ, hsk]
  ring

/-- Cochrane (2023), §17.4.1, p. 408: correspondingly output converges to its long-run
Phillips-curve value, `x_t → (1 − β) ī/κ`. -/
theorem tendsto_x {σ β κ M ib : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i x π : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (hl : Tendsto i atTop (𝓝 ib)) (hb : BoundedS π)
    (hs : Second σ β κ i π) (hx : ∀ t, x t = (π t - β * π (t + 1)) / κ) :
    Tendsto x atTop (𝓝 ((1 - β) * ib / κ)) := by
  have hp := tendsto_pi ha hβ hi hl hb hs
  have hp1 := hp.comp (tendsto_add_atTop_nat 1)
  have h := (hp.sub (hp1.const_mul β)).div_const κ
  rw [show (ib - β * ib) / κ = (1 - β) * ib / κ by ring] at h
  refine h.congr fun t => ?_
  rw [hx t]
  rfl


/-! ### The two-sided moving average (5.5) -/

/-- Cochrane (2023), eq. (5.5), p. 119: the coefficient `c = σκ/(λ₁ − λ₂)`. -/
noncomputable def coef (σ β κ : ℝ) : ℝ := σ * κ / (lam1 σ β κ - lam2 σ β κ)

/-- Cochrane (2023), eq. (5.5), p. 119: `c (λ₁ − λ₂) = σκ`. -/
theorem coef_mul {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    coef σ β κ * (lam1 σ β κ - lam2 σ β κ) = σ * κ := by
  unfold coef
  exact div_mul_cancel₀ _ (sub_ne_zero.mpr (lam2_lt_lam1 ha hβ).ne')

/-- Cochrane (2023), eq. (5.5), p. 119: `c > 0`. -/
theorem coef_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) : 0 < coef σ β κ :=
  div_pos ha (sub_pos.mpr (lam2_lt_lam1 ha hβ))

/-- Cochrane (2023), eq. (5.5), p. 119 and §17.4.1, p. 408 (perfect foresight, no past
surprises): the two-sided moving average
`π_t = c [∑_{j<t} λ₁^{−j} i_{t−1−j} + λ₂ ∑_{k≥0} λ₂ᵏ i_{t+k}]`. -/
noncomputable def twoSided (σ β κ : ℝ) (i : ℕ → ℝ) (t : ℕ) : ℝ :=
  coef σ β κ * (∑ j ∈ Finset.range t, (lam1 σ β κ)⁻¹ ^ j * i (t - 1 - j) +
    lam2 σ β κ * F (lam2 σ β κ) i t)

/-- Cochrane (2023), eq. (5.5), p. 119: the two-sided moving average satisfies the factored
equation `λ₁ π_{t+1} = π_t + σκ F_t`. -/
theorem twoSided_factor {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) (t : ℕ) :
    lam1 σ β κ * twoSided σ β κ i (t + 1) = twoSided σ β κ i t + σ * κ * F (lam2 σ β κ) i t := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have hll : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have f := F_rec (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hi t
  have hc := coef_mul ha hβ
  have hs : ∑ j ∈ Finset.range (t + 1), (lam1 σ β κ)⁻¹ ^ j * i (t + 1 - 1 - j) =
      (lam1 σ β κ)⁻¹ * (∑ j ∈ Finset.range t, (lam1 σ β κ)⁻¹ ^ j * i (t - 1 - j)) + i t := by
    rw [Finset.sum_range_succ', Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show t + 1 - 1 - (j + 1) = t - 1 - j by omega, pow_succ]
      ring
    · simp
  unfold twoSided
  rw [hs]
  set S := ∑ j ∈ Finset.range t, (lam1 σ β κ)⁻¹ ^ j * i (t - 1 - j)
  linear_combination (coef σ β κ * S) * hll - (coef σ β κ * lam1 σ β κ) * f +
    F (lam2 σ β κ) i t * hc

/-- Cochrane (2023), eq. (5.5), p. 119 and §17.4.1, p. 408: the equilibrium path with initial
inflation `c λ₂ F_0` (no expectational error at the start) is the two-sided moving average. -/
theorem twoSided_eq {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i : ℕ → ℝ}
    (hi : ∀ t, |i t| ≤ M) :
    path σ β κ i (coef σ β κ * lam2 σ β κ * F (lam2 σ β κ) i 0) = twoSided σ β κ i := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  funext t
  induction t with
  | zero => simp [path, twoSided, mul_assoc]
  | succ t ih =>
    apply mul_left_cancel₀ hl0
    rw [path_factor ha hβ i _ t, ih, twoSided_factor ha hβ hi t]

/-! ### Figure 17.5: an announced permanent rise -/

/-- Cochrane (2023), Fig. 17.5, p. 408: the permanent rise `i_t = 1` from date `T` on, `0` before
(announced at date 0). -/
noncomputable def stepI (T t : ℕ) : ℝ := if T ≤ t then 1 else 0

/-- The step is bounded by one. -/
theorem stepI_bound (T t : ℕ) : |stepI T t| ≤ 1 := by
  unfold stepI
  split_ifs <;> norm_num

/-- Cochrane (2023), Fig. 17.5: the step tends to one. -/
theorem stepI_tendsto (T : ℕ) : Tendsto (stepI T) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop T] with t ht
  simp [stepI, ht]

/-- Cochrane (2023), Fig. 17.5: for the step, `F_t = ∑ qᵏ i_{t+k} = q^{T−t}/(1 − q)` (with
truncated subtraction: `1/(1 − q)` from date `T` on). -/
theorem F_step {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (T t : ℕ) :
    F q (stepI T) t = q ^ (T - t) / (1 - q) := by
  have h1q : 1 - q ≠ 0 := by linarith
  have h := F_unique hq0 hq1 (stepI_bound T) (G := fun t => q ^ (T - t) / (1 - q))
    (fun t => by
      simp only [stepI]
      split_ifs with h
      · rw [show T - t = 0 by omega, show T - (t + 1) = 0 by omega]
        field_simp
        ring
      · rw [show T - t = T - (t + 1) + 1 by omega, pow_succ]
        field_simp
        ring)
    ⟨1 / (1 - q), fun t => by
      rw [abs_of_nonneg (div_nonneg (pow_nonneg hq0 _) (by linarith))]
      exact div_le_div_of_nonneg_right (pow_le_one₀ hq0 hq1.le) (by linarith)⟩
  exact (congrFun h t).symm

/-- Cochrane (2023), Fig. 17.5, p. 409 and p. 410: the response to the announced rise with no
expectational error, the two-sided moving average (5.5) for the step (`antPath_twoSided`). -/
noncomputable def antPath (σ β κ : ℝ) (T : ℕ) : ℕ → ℝ :=
  path σ β κ (stepI T) (coef σ β κ * lam2 σ β κ * F (lam2 σ β κ) (stepI T) 0)

/-- Cochrane (2023), eq. (5.5) and Fig. 17.5: `antPath` is the two-sided moving average. -/
theorem antPath_twoSided {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    antPath σ β κ T = twoSided σ β κ (stepI T) :=
  twoSided_eq ha hβ (stepI_bound T)

/-- Cochrane (2023), Fig. 17.5: `antPath` is a bounded perfect-foresight equilibrium path. -/
theorem antPath_second {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    BoundedS (antPath σ β κ T) ∧ Second σ β κ (stepI T) (antPath σ β κ T) :=
  ⟨path_bounded ha hβ (stepI_bound T) _, (second_iff_factor ha hβ (stepI_bound T)
    (path_bounded ha hβ (stepI_bound T) _)).mpr (path_factor ha hβ _ _)⟩

/-- Cochrane (2023), Fig. 17.5, p. 409 ("inflation now rises before the interest rates rise"):
up to the date of the rise, `π_t = c λ₂^{T−t+1}/(1 − λ₂)` — positive and growing at rate
`1/λ₂` while the interest rate is still zero. -/
theorem antPath_le_T {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {T t : ℕ} (ht : t ≤ T) :
    antPath σ β κ T t = coef σ β κ * lam2 σ β κ ^ (T - t + 1) / (1 - lam2 σ β κ) := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have h1q : 1 - lam2 σ β κ ≠ 0 := by linarith
  have hc := coef_mul ha hβ
  induction t with
  | zero =>
    simp only [antPath, path, F_step h20 h21, Nat.sub_zero]
    rw [pow_succ]
    field_simp
  | succ t ih =>
    have ih' := ih (by omega)
    apply mul_left_cancel₀ hl0
    rw [antPath, path_factor ha hβ _ _ t, ← antPath, ih', F_step h20 h21,
      show T - t + 1 = T - (t + 1) + 1 + 1 by omega, show T - t = T - (t + 1) + 1 by omega]
    field_simp
    linear_combination (-(lam2 σ β κ ^ (T - (t + 1)) * lam2 σ β κ)) * hc

/-- Cochrane (2023), p. 410 ("the original δ₁ = 0 equilibrium already had a little jump in
inflation"): on the announcement date inflation jumps to `π_0 = c λ₂^{T+1}/(1 − λ₂) > 0`. -/
theorem antPath_zero_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    antPath σ β κ T 0 = coef σ β κ * lam2 σ β κ ^ (T + 1) / (1 - lam2 σ β κ) ∧
      0 < antPath σ β κ T 0 := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have h := antPath_le_T ha hβ (Nat.zero_le T)
  rw [Nat.sub_zero] at h
  refine ⟨h, ?_⟩
  rw [h]
  have := coef_pos ha hβ
  have : 0 < 1 - lam2 σ β κ := by linarith
  positivity

/-- Cochrane (2023), Fig. 17.5, p. 409: the no-surprise response rises monotonically. -/
theorem antPath_strictMono {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    StrictMono (antPath σ β κ T) := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hc := coef_mul ha hβ
  have hcp := coef_pos ha hβ
  have h1q : 0 < 1 - lam2 σ β κ := by linarith
  have hfac : ∀ t, lam1 σ β κ * antPath σ β κ T (t + 1) =
      antPath σ β κ T t + σ * κ * F (lam2 σ β κ) (stepI T) t := fun t => path_factor ha hβ _ _ t
  have hFm : ∀ t, F (lam2 σ β κ) (stepI T) t ≤ F (lam2 σ β κ) (stepI T) (t + 1) := fun t => by
    rw [F_step h2.le h21, F_step h2.le h21]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one h2.le h21.le (Nat.sub_le_sub_left (Nat.le_succ t) T)) (by linarith)
  have hF0 : 0 < F (lam2 σ β κ) (stepI T) 0 := by
    rw [F_step h2.le h21]
    positivity
  -- the increments are positive
  have hd : ∀ t, antPath σ β κ T t < antPath σ β κ T (t + 1) := by
    intro t
    induction t with
    | zero =>
      have e := hfac 0
      have h0 : antPath σ β κ T 0 = coef σ β κ * lam2 σ β κ * F (lam2 σ β κ) (stepI T) 0 := rfl
      -- `λ₁ (π₁ − π₀) = c λ₁ (1 − λ₂) F₀ > 0`
      have key : lam1 σ β κ * (antPath σ β κ T 1 - antPath σ β κ T 0) =
          coef σ β κ * lam1 σ β κ * (1 - lam2 σ β κ) * F (lam2 σ β κ) (stepI T) 0 := by
        rw [mul_sub, e, h0]
        linear_combination (-F (lam2 σ β κ) (stepI T) 0) * hc
      have : 0 < lam1 σ β κ * (antPath σ β κ T 1 - antPath σ β κ T 0) := by
        rw [key]; positivity
      have := (pos_iff_pos_of_mul_pos this).mp hl0
      linarith
    | succ t ih =>
      have e1 := hfac t
      have e2 := hfac (t + 1)
      have hm := hFm t
      have : 0 < lam1 σ β κ * (antPath σ β κ T (t + 2) - antPath σ β κ T (t + 1)) := by
        rw [mul_sub, e2, e1]
        nlinarith
      have := (pos_iff_pos_of_mul_pos this).mp hl0
      linarith
  exact strictMono_nat_of_lt_succ hd

/-- Cochrane (2023), Fig. 17.5, p. 408 ("long-run response 1"): the response converges to one. -/
theorem antPath_tendsto_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    Tendsto (antPath σ β κ T) atTop (𝓝 1) :=
  tendsto_pi ha hβ (stepI_bound T) (stepI_tendsto T) (antPath_second ha hβ T).1
    (antPath_second ha hβ T).2

/-- Cochrane (2023), Fig. 17.5: the response stays below the new interest rate, `π_t < 1`. -/
theorem antPath_lt_one {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T t : ℕ) :
    antPath σ β κ T t < 1 :=
  ((antPath_strictMono ha hβ T) (Nat.lt_succ_self t)).trans_le
    ((antPath_strictMono ha hβ T).monotone.ge_of_tendsto (antPath_tendsto_one ha hβ T) _)

/-- Cochrane (2023), Fig. 17.5, p. 409: inflation is positive at every date, in particular at
every date before the interest rate rises. -/
theorem antPath_pos {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T t : ℕ) :
    0 < antPath σ β κ T t :=
  (antPath_zero_pos ha hβ T).2.trans_le ((antPath_strictMono ha hβ T).monotone (Nat.zero_le t))

/-- Cochrane (2023), p. 409 ("output is low if inflation is low relative to expected future
inflation, i.e. if inflation is increasing"): with `x_t = (π_t − β π_{t+1})/κ` and `κ > 0`,
`x_t < 0` iff `π_t < β π_{t+1}`. -/
theorem x_neg_iff {β κ : ℝ} (hκ : 0 < κ) (π : ℕ → ℝ) (t : ℕ) :
    (π t - β * π (t + 1)) / κ < 0 ↔ π t < β * π (t + 1) := by
  rw [div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, hκ⟩

/-- Cochrane (2023), Fig. 17.5, p. 409 ("output declines"; "fully expected interest-rate rises
do lower output"): along the no-surprise response, output is negative at every date up to and
including the date of the rise. -/
theorem antPath_x_neg {σ β κ : ℝ} (hσ : 0 < σ) (hκ : 0 < κ) (hβ : 0 < β) {T t : ℕ}
    (ht : t ≤ T) :
    (antPath σ β κ T t - β * antPath σ β κ T (t + 1)) / κ < 0 := by
  have ha := mul_pos hσ hκ
  rw [x_neg_iff hκ]
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  have hc := coef_mul ha hβ
  have hcp := coef_pos ha hβ
  have hp := lam_prod ha hβ
  have h1q : 0 < 1 - lam2 σ β κ := by linarith
  have e : lam1 σ β κ * antPath σ β κ T (t + 1) =
      antPath σ β κ T t + σ * κ * F (lam2 σ β κ) (stepI T) t := path_factor ha hβ _ _ t
  rw [antPath_le_T ha hβ ht, F_step h2.le h21] at e
  -- `β π_{t+1} − π_t = λ₂ (λ₁ π_{t+1}) − π_t = c (λ₁ − 1) λ₂^{T−t+1}/(1 − λ₂)`
  have key : β * antPath σ β κ T (t + 1) - antPath σ β κ T t =
      coef σ β κ * (lam1 σ β κ - 1) * lam2 σ β κ ^ (T - t + 1) / (1 - lam2 σ β κ) := by
    have hb : β * antPath σ β κ T (t + 1) =
        lam2 σ β κ * (lam1 σ β κ * antPath σ β κ T (t + 1)) := by
      rw [← mul_assoc, mul_comm (lam2 σ β κ), hp]
    rw [hb, e, antPath_le_T ha hβ ht]
    field_simp
    linear_combination (-(lam2 σ β κ * lam2 σ β κ ^ (T - t))) * hc
  have : 0 < coef σ β κ * (lam1 σ β κ - 1) * lam2 σ β κ ^ (T - t + 1) / (1 - lam2 σ β κ) := by
    have : 0 < lam1 σ β κ - 1 := by linarith
    positivity
  linarith

/-- Cochrane (2023), Fig. 17.5: output converges to `(1 − β)/κ`, its long-run Phillips-curve
value (nonnegative, zero only for `β = 1`). -/
theorem antPath_x_tendsto {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) :
    Tendsto (fun t => (antPath σ β κ T t - β * antPath σ β κ T (t + 1)) / κ) atTop
      (𝓝 ((1 - β) / κ)) := by
  have h := tendsto_x ha hβ (stepI_bound T) (stepI_tendsto T) (antPath_second ha hβ T).1
    (antPath_second ha hβ T).2 (fun t => rfl)
  simpa using h

/-- Cochrane (2023), p. 409 ("expected future interest-rate rises increase inflation today"):
for **every** initial inflation `p`, the announced rise raises inflation at every date `t ≥ 1`
(before and after the rise) relative to the path with no rise and the same initial jump. -/
theorem rise_raises_inflation {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) (p : ℝ)
    (t : ℕ) : path σ β κ (fun _ => 0) p (t + 1) < path σ β κ (stepI T) p (t + 1) := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans (one_lt_lam1 ha hβ)
  have hF0 : ∀ s, F (lam2 σ β κ) (fun _ => (0 : ℝ)) s = 0 := fun s => by simp [F]
  have hFp : ∀ s, 0 < F (lam2 σ β κ) (stepI T) s := fun s => by
    rw [F_step h2.le h21]
    have : 0 < 1 - lam2 σ β κ := by linarith
    positivity
  have hle : ∀ s, path σ β κ (fun _ => 0) p s ≤ path σ β κ (stepI T) p s := by
    intro s
    induction s with
    | zero => exact le_rfl
    | succ s ih =>
      simp only [path, hF0, mul_zero, add_zero]
      gcongr
      nlinarith [hFp s]
  simp only [path, hF0, mul_zero, add_zero]
  gcongr
  nlinarith [hFp t, hle t]

/-- Cochrane (2023), Fig. 17.5, p. 409 ("the dashed line … joins the solid inflation curve"):
the no-surprise response to an unexpected rise at date `T` (announced at `T`, i.e. `antPath 0`
started at `T`) coincides from date `T` on with the response to the rise announced at date 0. -/
theorem dashed_joins_solid {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T s : ℕ) :
    antPath σ β κ T (T + s) = antPath σ β κ 0 s := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  induction s with
  | zero =>
    rw [add_zero, antPath_le_T ha hβ le_rfl, antPath_le_T ha hβ le_rfl, Nat.sub_self,
      Nat.sub_self]
  | succ s ih =>
    apply mul_left_cancel₀ hl0
    have e1 : lam1 σ β κ * antPath σ β κ T (T + s + 1) =
        antPath σ β κ T (T + s) + σ * κ * F (lam2 σ β κ) (stepI T) (T + s) :=
      path_factor ha hβ _ _ _
    have e2 : lam1 σ β κ * antPath σ β κ 0 (s + 1) =
        antPath σ β κ 0 s + σ * κ * F (lam2 σ β κ) (stepI 0) s := path_factor ha hβ _ _ _
    rw [← add_assoc, e1, e2, ih, F_step h2.le h21, F_step h2.le h21,
      show T - (T + s) = 0 by omega, Nat.zero_sub]

/-- Cochrane (2023), Fig. 17.6, pp. 409–410 (equilibria A–E): for an unexpected permanent rise
(`T = 0`), **every** initial inflation `p` — a super-neutral `π₁ = 1` (B), no jump (D), or a
negative jump (E) — gives a bounded equilibrium, and every one converges to the new interest
rate. -/
theorem fig17_6_any_jump {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (p : ℝ) :
    BoundedS (path σ β κ (stepI 0) p) ∧ Second σ β κ (stepI 0) (path σ β κ (stepI 0) p) ∧
      path σ β κ (stepI 0) p 0 = p ∧ Tendsto (path σ β κ (stepI 0) p) atTop (𝓝 1) := by
  have hb := path_bounded ha hβ (stepI_bound 0) p
  have hs := (second_iff_factor ha hβ (stepI_bound 0) hb).mpr (path_factor ha hβ _ p)
  exact ⟨hb, hs, rfl, tendsto_pi ha hβ (stepI_bound 0) (stepI_tendsto 0) hb hs⟩


/-! ### Figure 17.5: the rise anticipated from the infinite past (ℤ-indexed paths) -/

/-- Cochrane (2023), eq. (17.18), p. 408, under perfect foresight on the whole line `ℤ`:
`π_t − (1 + β + σκ) π_{t+1} + β π_{t+2} = −σκ i_t` for every date `t ∈ ℤ`. -/
def SecondZ (σ β κ : ℝ) (i π : ℤ → ℝ) : Prop :=
  ∀ t : ℤ, π t - (1 + β + σ * κ) * π (t + 1) + β * π (t + 2) = -(σ * κ) * i t

/-- A real ℤ-indexed sequence is bounded. -/
def BoundedZ (z : ℤ → ℝ) : Prop := ∃ M, ∀ t, |z t| ≤ M

/-- Cochrane (2023), Fig. 17.5, p. 409: the permanent rise `i_t = 1{t ≥ T}` on `ℤ`, known at
every date (anticipated from the infinite past). -/
noncomputable def stepZ (T t : ℤ) : ℝ := if T ≤ t then 1 else 0

/-- Cochrane (2023), eq. (5.5): `F_t = ∑_{k≥0} λ₂ᵏ i_{t+k}` for the ℤ-step, in closed form
`λ₂^{max(T−t,0)}/(1 − λ₂)`. -/
noncomputable def GZ (σ β κ : ℝ) (T t : ℤ) : ℝ :=
  lam2 σ β κ ^ (T - t).toNat / (1 - lam2 σ β κ)

/-- Cochrane (2023), Fig. 17.5, p. 409 (solid line): the response anticipated from the infinite
past, `π_t = c λ₂^{T−t+1}/(1 − λ₂)` for `t ≤ T` and
`π_t = 1 − (1 − c λ₂/(1 − λ₂)) λ₁^{−(t−T)}` for `t ≥ T`. -/
noncomputable def zPath (σ β κ : ℝ) (T t : ℤ) : ℝ :=
  if t ≤ T then coef σ β κ * lam2 σ β κ / (1 - lam2 σ β κ) * lam2 σ β κ ^ (T - t).toNat
  else 1 - (1 - coef σ β κ * lam2 σ β κ / (1 - lam2 σ β κ)) * (lam1 σ β κ)⁻¹ ^ (t - T).toNat

/-- The closed-form forward sum satisfies `G_t = i_t + λ₂ G_{t+1}`. -/
theorem GZ_rec {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T t : ℤ) :
    GZ σ β κ T t = stepZ T t + lam2 σ β κ * GZ σ β κ T (t + 1) := by
  have h1 : 1 - lam2 σ β κ ≠ 0 := by linarith [lam2_lt_one ha hβ]
  unfold GZ stepZ
  split_ifs with h
  · rw [show (T - t).toNat = 0 by omega, show (T - (t + 1)).toNat = 0 by omega]
    field_simp
    ring
  · rw [show (T - t).toNat = (T - (t + 1)).toNat + 1 by omega, pow_succ]
    field_simp
    ring

/-- Cochrane (2023), eq. (5.5) on `ℤ`: the anticipated response satisfies the factored equation
`λ₁ π_{t+1} = π_t + σκ F_t` at every date. -/
theorem zPath_factor {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T t : ℤ) :
    lam1 σ β κ * zPath σ β κ T (t + 1) = zPath σ β κ T t + σ * κ * GZ σ β κ T t := by
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have h1 : 1 - lam2 σ β κ ≠ 0 := by linarith
  have hc := coef_mul ha hβ
  have hsk := sigma_kappa_eq ha hβ
  have hll : lam1 σ β κ * (lam1 σ β κ)⁻¹ = 1 := mul_inv_cancel₀ hl0
  have hsk' : σ * κ * (1 / (1 - lam2 σ β κ)) = lam1 σ β κ - 1 := by
    rw [hsk]; field_simp
  set K := coef σ β κ * lam2 σ β κ / (1 - lam2 σ β κ) with hK
  unfold zPath GZ
  rw [← hK]
  by_cases hA : t + 1 ≤ T
  · have hA' : t ≤ T := by omega
    simp only [hA, hA', ↓reduceIte]
    rw [show (T - t).toNat = (T - (t + 1)).toNat + 1 by omega, pow_succ, hK]
    field_simp
    linear_combination (lam2 σ β κ * lam2 σ β κ ^ (T - (t + 1)).toNat) * hc
  · by_cases hB : t = T
    · subst hB
      simp only [hA, le_refl, ↓reduceIte]
      rw [show (t + 1 - t).toNat = 1 by omega, sub_self, Int.toNat_zero, pow_one, pow_zero,
        mul_one, hsk']
      linear_combination (-(1 - K)) * hll
    · have hB' : ¬ t ≤ T := by omega
      simp only [hA, hB', ↓reduceIte]
      rw [show (t + 1 - T).toNat = (t - T).toNat + 1 by omega,
        show (T - t).toNat = 0 by omega, pow_succ, pow_zero, hsk']
      linear_combination (-(1 - K) * (lam1 σ β κ)⁻¹ ^ (t - T).toNat) * hll

/-- Cochrane (2023), Fig. 17.5, p. 409: the anticipated response is bounded. -/
theorem zPath_bounded {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    BoundedZ (zPath σ β κ T) := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hμ0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (one_pos.trans hl1).le
  have hμ1 : (lam1 σ β κ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ hl1).le
  set K := coef σ β κ * lam2 σ β κ / (1 - lam2 σ β κ)
  refine ⟨|K| + 1 + |1 - K|, fun t => ?_⟩
  unfold zPath
  split_ifs
  · rw [abs_mul, abs_pow, abs_of_pos h2]
    have : lam2 σ β κ ^ (T - t).toNat ≤ 1 := pow_le_one₀ h2.le h21.le
    have := abs_nonneg K
    have := abs_nonneg (1 - K)
    nlinarith
  · refine (abs_sub _ _).trans ?_
    rw [abs_one, abs_mul, abs_pow, abs_of_nonneg hμ0]
    have : (lam1 σ β κ)⁻¹ ^ (t - T).toNat ≤ 1 := pow_le_one₀ hμ0 hμ1
    have := abs_nonneg K
    have := abs_nonneg (1 - K)
    nlinarith

/-- Cochrane (2023), Fig. 17.5, p. 409: the anticipated response solves (17.18) at every date of
`ℤ`. -/
theorem zPath_second {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    SecondZ σ β κ (stepZ T) (zPath σ β κ T) := by
  intro t
  have e1 := zPath_factor ha hβ T t
  have e2 := zPath_factor ha hβ T (t + 1)
  have f := GZ_rec ha hβ T t
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  rw [show t + 1 + 1 = t + 2 by ring] at e2
  linear_combination zPath σ β κ T (t + 1) * h1 - zPath σ β κ T (t + 2) * h2 - e1 +
    lam2 σ β κ * e2 - (σ * κ) * f

/-- Cochrane (2023), p. 408 and eq. (5.5) on `ℤ`: for any bounded interest-rate path there is
at most one bounded perfect-foresight inflation path on the whole line — with an infinite past
there is no free initial condition. -/
theorem secondZ_unique {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π π' : ℤ → ℝ}
    (hπ : SecondZ σ β κ i π) (hπ' : SecondZ σ β κ i π') (hb : BoundedZ π)
    (hb' : BoundedZ π') : π = π' := by
  have h20 := (lam2_pos ha hβ).le
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  obtain ⟨M, hM⟩ := hb
  obtain ⟨M', hM'⟩ := hb'
  set d : ℤ → ℝ := fun t => π t - π' t with hd
  have hdb : ∀ t, |d t| ≤ M + M' := fun t => (abs_sub _ _).trans (add_le_add (hM t) (hM' t))
  have h1 := lam_sum σ β κ
  have h2 := lam_prod ha hβ
  -- `w_t = d_t − λ₁ d_{t+1}` satisfies `w_t = λ₂ w_{t+1}`
  set w : ℤ → ℝ := fun t => d t - lam1 σ β κ * d (t + 1) with hw
  have hwrec : ∀ t, w t = lam2 σ β κ * w (t + 1) := fun t => by
    have a := hπ t
    have b := hπ' t
    simp only [hw, hd, show t + 1 + 1 = t + 2 by ring]
    linear_combination a - b - (π (t + 1) - π' (t + 1)) * h1 + (π (t + 2) - π' (t + 2)) * h2
  have hwb : ∀ t, |w t| ≤ M + M' + lam1 σ β κ * (M + M') := fun t => by
    refine (abs_sub _ _).trans (add_le_add (hdb t) ?_)
    rw [abs_mul, abs_of_pos hl0]
    exact mul_le_mul_of_nonneg_left (hdb (t + 1)) hl0.le
  -- `w` read backwards is a bounded solution of a stable recursion on `ℤ`, hence zero
  have hq2 : |lam2 σ β κ| < 1 := by rw [abs_of_nonneg h20]; exact h21
  have hwz := int_homog_zero hq2 (x := fun s => w (-s)) (fun s => hwb (-s)) (fun s => by
    rw [hwrec (-(s + 1)), show -(s + 1) + 1 = -s by ring])
  have hw0 : ∀ t, w t = 0 := fun t => by simpa using congrFun hwz (-t)
  -- then `d_{t+1} = λ₁⁻¹ d_t`, again a bounded solution of a stable recursion on `ℤ`
  have hdrec : ∀ s, d (s + 1) = (lam1 σ β κ)⁻¹ * d s := fun s => by
    have := hw0 s
    simp only [hw] at this
    field_simp
    linarith
  have hq : |(lam1 σ β κ)⁻¹| < 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr hl0.le)]; exact inv_lt_one_of_one_lt₀ hl1
  have hd0 := int_homog_zero hq hdb hdrec
  funext t
  have := congrFun hd0 t
  simp only [hd, Pi.zero_apply] at this
  linarith

/-- Cochrane (2023), Fig. 17.5, p. 409: for the permanent rise at date `T` anticipated from the
infinite past there is exactly one bounded perfect-foresight inflation path on `ℤ`, `zPath`. -/
theorem zPath_existsUnique {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    ∃! π : ℤ → ℝ, BoundedZ π ∧ SecondZ σ β κ (stepZ T) π :=
  ⟨zPath σ β κ T, ⟨zPath_bounded ha hβ T, zPath_second ha hβ T⟩,
    fun _ ⟨hb, hs⟩ => secondZ_unique ha hβ hs (zPath_second ha hβ T) hb (zPath_bounded ha hβ T)⟩

/-- The anticipated response depends only on the distance to the rise: shifting the rise date
and the date by `N` leaves it unchanged. -/
theorem zPath_shift (σ β κ : ℝ) (T t N : ℤ) :
    zPath σ β κ (T + N) (t + N) = zPath σ β κ T t := by
  unfold zPath
  rw [show T + N - (t + N) = T - t by ring, show t + N - (T + N) = t - T by ring]
  simp only [add_le_add_iff_right]

/-- Cochrane (2023), Fig. 17.5, pp. 409–410: the ℕ-indexed no-surprise response to the rise at
date `T` announced at date 0 (`antPath`, the two-sided moving average (5.5) with `δ = 0`)
coincides at every date `s ≥ 0` with the response anticipated from the infinite past. -/
theorem zPath_eq_antPath {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T s : ℕ) :
    zPath σ β κ T s = antPath σ β κ T s := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have h1 : 1 - lam2 σ β κ ≠ 0 := by linarith
  induction s with
  | zero =>
    rw [(antPath_zero_pos ha hβ T).1]
    unfold zPath
    have h0 : ((0 : ℕ) : ℤ) ≤ (T : ℤ) := by omega
    simp only [h0, ↓reduceIte]
    rw [show ((T : ℤ) - ((0 : ℕ) : ℤ)).toNat = T by omega, pow_succ]
    field_simp
  | succ s ih =>
    apply mul_left_cancel₀ hl0
    have e1 := zPath_factor ha hβ (T : ℤ) (s : ℤ)
    have e2 : lam1 σ β κ * antPath σ β κ T (s + 1) =
        antPath σ β κ T s + σ * κ * F (lam2 σ β κ) (stepI T) s := path_factor ha hβ _ _ _
    rw [show ((s + 1 : ℕ) : ℤ) = (s : ℤ) + 1 by push_cast; ring, e1, e2, ih,
      F_step h2.le h21]
    unfold GZ
    rw [show ((T : ℤ) - (s : ℤ)).toNat = T - s by omega]

/-- Cochrane (2023), Fig. 17.5: with the announcement at date `−N` (rise at date `T ≥ 0`), the
no-surprise response coincides after the announcement with the response anticipated from the
infinite past: `antPath (T + N) s = zPath T (s − N)`. -/
theorem antPath_eq_zPath_shift {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T N s : ℕ) :
    antPath σ β κ (T + N) s = zPath σ β κ T ((s : ℤ) - N) := by
  rw [← zPath_eq_antPath ha hβ, ← zPath_shift σ β κ T ((s : ℤ) - N) N]
  push_cast
  ring_nf

/-- Two paths for the same rate path differ by `(p − q) λ₁^{−n}`. -/
theorem path_sub_path (σ β κ : ℝ) (i : ℕ → ℝ) (p q : ℝ)
    (n : ℕ) : path σ β κ i p n - path σ β κ i q n = (p - q) * (lam1 σ β κ)⁻¹ ^ n := by
  induction n with
  | zero => simp [path]
  | succ n ih =>
    simp only [path]
    rw [pow_succ, ← mul_assoc, ← ih]
    ring

/-- Cochrane (2023), Fig. 17.5, p. 409: as the announcement recedes into the past, **every**
perfect-foresight response converges to the response anticipated from the infinite past. With
the announcement at date `−N`, a rise at date `T` and any initial jump `p` at the announcement,
inflation at a fixed date `t ∈ ℤ` tends to `zPath T t` as `N → ∞`. -/
theorem tendsto_zPath {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℕ) (p : ℝ) (t : ℤ) :
    Tendsto (fun N : ℕ => path σ β κ (stepI (T + N)) p (t + N).toNat) atTop
      (𝓝 (zPath σ β κ T t)) := by
  have h2 := lam2_pos ha hβ
  have h21 := lam2_lt_one ha hβ
  have hl1 := one_lt_lam1 ha hβ
  have hq0 : 0 ≤ (lam1 σ β κ)⁻¹ := inv_nonneg.mpr (one_pos.trans hl1).le
  have hq1 : (lam1 σ β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  -- the jump of the no-surprise response at the announcement vanishes
  have ha0 : Tendsto (fun N : ℕ => antPath σ β κ (T + N) 0) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => coef σ β κ * lam2 σ β κ ^ (T + N + 1) / (1 - lam2 σ β κ))
        atTop (𝓝 (coef σ β κ * 0 / (1 - lam2 σ β κ))) :=
      (((tendsto_pow_atTop_nhds_zero_of_lt_one h2.le h21).comp
        (tendsto_add_atTop_nat (T + 1))).const_mul _).div_const _ |>.congr fun N => by
          simp only [Function.comp_apply]
          ring_nf
    rw [mul_zero, zero_div] at this
    exact this.congr fun N => ((antPath_zero_pos ha hβ (T + N)).1).symm
  have hn : Tendsto (fun N : ℕ => (t + N).toNat) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b + (-t).toNat, fun N hN => by omega⟩
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hn
  have hlim := ((tendsto_const_nhds (x := p)).sub ha0).mul hpow
  rw [mul_zero] at hlim
  have h := hlim.const_add (zPath σ β κ T t)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (-t).toNat] with N hN
  have hs := path_sub_path σ β κ (stepI (T + N)) p (antPath σ β κ (T + N) 0) (t + N).toNat
  have he := antPath_eq_zPath_shift ha hβ T N (t + N).toNat
  rw [show (((t + N).toNat : ℕ) : ℤ) - (N : ℤ) = t by omega] at he
  have hd : path σ β κ (stepI (T + N)) (antPath σ β κ (T + N) 0) (t + N).toNat =
      antPath σ β κ (T + N) (t + N).toNat := rfl
  rw [hd, he] at hs
  simp only [Function.comp_apply]
  linarith

end Cochrane.KeynesianStickyPrices.FullModel
