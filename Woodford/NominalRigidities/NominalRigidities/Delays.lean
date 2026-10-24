/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.TwoSector
import NominalRigidities.Persistence
import NominalRigidities.ExpectationsFiniteTree

/-!
# Delayed effects of nominal disturbances on inflation

Woodford (2003), *Interest and Prices*, Chapter 3, §3, pp. 204–218: §3.1 staggered pricing with
delayed price changes (pp. 207–213) and §3.2 indexation to past inflation (pp. 213–218).

## The forward-looking NKPC, §3 opening (pp. 204–206)

* `nkpc_forward`, `nkpc_existsUnique`: (3.1) `π_t = κ ∑ βʲ E_t(Ŷ − Ŷⁿ)_{t+j}` is the unique bounded
  solution of (2.12) (any `ExpectationSystem`).
* `footnote_63`, `footnote_63_orthogonal`: `π_{t+1} − β⁻¹π_t = −β⁻¹κ(Ŷ_t − Ŷ_tⁿ) + e_{t+1}`,
  with a forecast error `e_{t+1}` that has `E_t e_{t+1} = 0` and is orthogonal to everything
  known at `t` (given the pull-out property).
* p. 206: `nkpc_mono` (inflation is an increasing function of expected gaps),
  `infl_precedes_output` (an anticipated output response moves inflation first) and
  `infl_peaks_no_later` (inflation is non-increasing once the gap response is; so it peaks no
  later than output), for impulse responses (`det_forward` links them to (2.12)).

## Delayed price changes, §3.1 (pp. 207–212)

* `delayed_from_foc`: (3.2) (and (3.7)) derived from the delayed linearised first-order
  condition and the Calvo law of motion, via the Chapter 3 Calvo block of `TwoSector`.
* `delayed_predetermined`: under (3.2) inflation is predetermined (`π_{t+d}` is known at `t`);
  `prices_predetermined`, `quasiDiff_predetermined`: predetermination of the price level and of
  quasi-differenced inflation from the law of motion.
* `delayed_forward`, `delayed_existsUnique`: `π_{t+d} = κ ∑ βʲ E_t(Ŷ − Ŷⁿ)_{t+d+j}`, the unique
  bounded solution; `delayed_depends_on_forecasts`: only forecasts made `d` periods earlier
  matter.
* `revision_zero_before_delay`, `revision_recursion`, `revision_irf`: a shock at date `s + 1`
  revises no inflation rate before `s + 1 + d`; the revisions obey the delayed impulse-response
  system `DelayIRF`.
* Impulse responses: `irf_unique` (bounded solutions of `DelayIRF` are unique, by a maximum
  principle), `irf_exists` / `irfP` (existence via the roots `0 < λ₁ < 1 < λ₂` of
  `βλ² − (1 + β + κ)λ + 1`), `nomIRF` (the nominal-GDP response to (3.3), `nomIRF_shift`).
* **Figure 3.12** (`fig_3_12`, `fig_3_12_stochastic`): with `s = d` the responses of the price
  level, inflation and output are exactly those of Figure 3.9 shifted right by `d` periods
  (`shift_solves`). **Figure 3.11** (`fig_3_11_contraction`): with `s ≥ 1` and `d = 0` output
  contracts on impact. `delayed_output_eq_nominal`: before date `d` output moves one-for-one
  with nominal GDP (Figures 3.12, 3.13).

## Indexation, §3.2 (pp. 213–218)

* `yun_iff`, `yun_vertical`: Yun's indexation to `π̄` and the vertical long-run Phillips curve.
* `hasDerivAt_eq_3_5`: the log-linearised price index (3.5); `indexed_law`,
  `indexed_relPrice`: the indexation rule (3.4) in the Calvo block; `eq_3_6_from_foc`: (3.6).
* `eq_3_6_forward`, `eq_3_6_unique`: `π_t = γπ_{t−1} + κ ∑ βʲ E_t(Ŷ − Ŷⁿ)_{t+j}`.
* `eq_3_6_iff_hybrid`, `fuhrer_moore`, `hybrid_weights_sum_one_iff`: the hybrid
  (Galí–Gertler) form and the Fuhrer–Moore case `β = γ = 1` (footnote 67).
* `eq_3_7_forward`: (3.7), delay and indexation together.

## Indexed impulse responses, Figures 3.14–3.16 and p. 217

* `cubicC`, `cubic_root_exists`, `index_factor`, `cubic_roots_location`: the characteristic
  polynomial `C(z) = (z − 1)(z − γ)(1 − βz) + κz²` has exactly one root outside the unit circle,
  a real `μ > 1/β`; the other two are the roots of a Schur–Cohn stable quadratic factor
  (`0 ≤ γ ≤ 1`, `0 < β < 1`, `κ > 0`).
* `IndexIRF`, `indexIRF_unique` (any delay), `indexIRF_exists`, `conv`, `conv_rec`,
  `indexIRF_shift`, `fig_3_15` (Figure 3.15 is Figure 3.14 shifted by `d`),
  `revision_index_irf` (revisions under (3.7) solve `IndexIRF`).
* `p217_contraction_general`, `p217_contraction`: p. 217 is **true** — with indexation and a
  lagged nominal-GDP response, output contracts on impact, for every `0 ≤ γ ≤ 1`.

## Independent disturbances on an event tree, (3.3)

* `shockTree`, `shockSystem`, `shockTree_independent`, `shock_revision_diff`, `treeEps`, `treeQ`,
  `treeGrowth`, `treeNom`, `treeNom_diff`, `fig_3_12_tree`: Figure 3.12 for the stochastic model
  with `q` independent of `ε`, without assuming the revision path.
* `TreeEq`, `treeEq_exists`, `treeEq_unique`, `fig_3_12_tree_equilibrium`, `treeNom_noq`,
  `treeNom_noq_bounded`: the tree economy has exactly one bounded adapted equilibrium, and it has
  the Figure 3.12 property (so `fig_3_12_tree` is not vacuous); helpers `Persistence.prev`, `dinfl`,
  `InflSol`, `inflSol_iff`, `inflSol_prefix`, `inflSol_exists`, `inflSol_unique`, `dinfl_add`,
  `dinfl_sub`, `dinfl_sum`, `sum_four`, `shock_E_pos`, `shock_E_zero`, `inflOf`, `inflOf_apply`,
  `treeEq_late`, `treeEq_zero`.
* `irf_exists_delay`, `indexIRF_exists_delay`, `irf_existsUnique_nom` (with `delayIRF_congr`,
  `indexIRF_congr`): bounded impulse responses exist, and are unique, for every delay `d` and
  every lag `s`, with and without indexation.
-/

namespace Woodford.NominalRigidities.Delays

open Filter Topology QuadraticRoots
open Persistence (prev prev_zero prev_succ)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (3.1): the forward solution of the New Keynesian Phillips curve -/

/-- Woodford (2003), eq. (3.1), p. 205: a bounded solution of (2.12)
`π_t = κ(Ŷ_t − Ŷ_tⁿ) + β E_t π_{t+1}` (bounded adapted gap, `0 ≤ β < 1`) is
`π_t = κ ∑_j βʲ E_t(Ŷ − Ŷⁿ)_{t+j}`. -/
theorem nkpc_forward {κ β Mg M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {π gap : ℕ → Ω → ℝ}
    (hg : ∀ t o, |gap t o| ≤ Mg) (hga : 𝔼.Adapted gap) (hπ : ∀ t o, |π t o| ≤ M)
    (h : ∀ t, π t = κ • gap t + β • 𝔼.E t (π (t + 1))) (t : ℕ) (o : Ω) :
    π t o = κ * ∑' j, β ^ j * 𝔼.E t (gap (t + j)) o := by
  have hu : ∀ t o, |(fun t => κ • gap t) t o| ≤ |κ| * Mg := fun t o => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg t o) (abs_nonneg κ)
  have hua : 𝔼.Adapted (fun t => κ • gap t) := fun t => by
    simp only [map_smul, hga t]
  have hs : ∀ t, π t = β • 𝔼.E t (π (t + 1)) + (fun t => κ • gap t) t := fun t => by
    rw [h t, add_comm]
  have := 𝔼.eq_forwardSeries hβ0 hβ1 hu hua hs ⟨M, hπ⟩
  rw [this]
  change ∑' k, β ^ k * 𝔼.E t (κ • gap (t + k)) o = _
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), (2.12) and (3.1), p. 205: for a bounded adapted gap and `0 ≤ β < 1` there is
exactly one bounded inflation process satisfying (2.12). -/
theorem nkpc_existsUnique {κ β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {gap : ℕ → Ω → ℝ}
    (hgb : BoundedProc gap) (hga : 𝔼.Adapted gap) :
    ∃! π : ℕ → Ω → ℝ, BoundedProc π ∧ ∀ t, π t = κ • gap t + β • 𝔼.E t (π (t + 1)) := by
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  obtain ⟨Mg, hg⟩ := hgb
  have hub : BoundedProc (fun t => κ • gap t) := ⟨|κ| * Mg, fun t o => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hg t o) (abs_nonneg κ)⟩
  have hua : 𝔼.Adapted (fun t => κ • gap t) := fun t => by simp only [map_smul, hga t]
  obtain ⟨z, ⟨hzb, hzs⟩, huniq⟩ := ForwardSolution.existsUnique_bounded 𝔼 hβ hub hua
  refine ⟨z, ⟨hzb, fun t => by rw [hzs t, add_comm]⟩, fun y ⟨hyb, hys⟩ => huniq y ⟨hyb, ?_⟩⟩
  intro t
  rw [hys t, add_comm]

/-- Woodford (2003), footnote 63, p. 205: (2.12) implies
`π_{t+1} − β⁻¹ π_t = −β⁻¹κ(Ŷ_t − Ŷ_tⁿ) + e_{t+1}`, `e_{t+1} = π_{t+1} − E_t π_{t+1}`, with
`E_t e_{t+1} = 0`. -/
theorem footnote_63 {κ β : ℝ} (hβ : β ≠ 0) {π gap : ℕ → Ω → ℝ}
    (h : ∀ t, π t = κ • gap t + β • 𝔼.E t (π (t + 1))) (t : ℕ) :
    π (t + 1) - β⁻¹ • π t = -(β⁻¹ * κ) • gap t + (π (t + 1) - 𝔼.E t (π (t + 1))) ∧
      𝔼.E t (π (t + 1) - 𝔼.E t (π (t + 1))) = 0 := by
  refine ⟨?_, by rw [map_sub, 𝔼.E_E_self, sub_self]⟩
  rw [h t]
  funext o
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Woodford (2003), footnote 63, p. 205: the forecast error is uncorrelated with all date-`t`
information: `E_t[X e_{t+1}] = 0` for every `X` known at `t` (given the pull-out property, which
holds under perfect foresight and on every finite event tree). -/
theorem footnote_63_orthogonal (hpo : 𝔼.PullOut) {X : Ω → ℝ} {t : ℕ} (hX : 𝔼.E t X = X)
    (π : ℕ → Ω → ℝ) : 𝔼.E t (X * (π (t + 1) - 𝔼.E t (π (t + 1)))) = 0 := by
  rw [hpo t X _ hX, map_sub, 𝔼.E_E_self, sub_self, mul_zero]

/-- Woodford (2003), p. 206: "the inflation response each quarter should be an increasing
function of the output responses that are expected in that quarter and later": for `κ ≥ 0` and
gaps `g₁ ≤ g₂`, `κ ∑ βʲ E_t g₁ ≤ κ ∑ βʲ E_t g₂`. -/
theorem nkpc_mono {κ β M1 M2 : ℝ} (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {g1 g2 : ℕ → Ω → ℝ} (hg1 : ∀ t o, |g1 t o| ≤ M1) (hg2 : ∀ t o, |g2 t o| ≤ M2)
    (hle : ∀ t, g1 t ≤ g2 t) (t : ℕ) (o : Ω) :
    κ * ∑' j, β ^ j * 𝔼.E t (g1 (t + j)) o ≤ κ * ∑' j, β ^ j * 𝔼.E t (g2 (t + j)) o := by
  refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun j => ?_)
    (𝔼.forwardSeries_summable hβ0 hβ1 hg1 t o) (𝔼.forwardSeries_summable hβ0 hβ1 hg2 t o)) hκ
  exact mul_le_mul_of_nonneg_left (𝔼.mono t (hle (t + j)) o) (pow_nonneg hβ0 j)

/-! ### Deterministic forward sums and impulse responses (p. 206) -/

/-- Woodford (2003), (3.1), p. 205, for a deterministic sequence (an impulse response):
`∑_j aʲ f_{k+j}`. -/
noncomputable def fwdSum (a : ℝ) (f : ℕ → ℝ) (k : ℕ) : ℝ := ∑' j, a ^ j * f (k + j)

/-- Woodford (2003), (3.1), p. 205: the deterministic forward sum converges for bounded `f`. -/
theorem fwdSum_summable {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → ℝ}
    (hf : ∀ k, |f k| ≤ M) (k : ℕ) : Summable (fun j => a ^ j * f (k + j)) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one ha0 ha1).mul_right M) fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hf _) (pow_nonneg ha0 j)

/-- Woodford (2003), (3.1), p. 205: the forward sum satisfies `F_k = f_k + a F_{k+1}`. -/
theorem fwdSum_rec {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → ℝ} (hf : ∀ k, |f k| ≤ M)
    (k : ℕ) : fwdSum a f k = f k + a * fwdSum a f (k + 1) := by
  unfold fwdSum
  rw [(fwdSum_summable ha0 ha1 hf k).tsum_eq_zero_add, pow_zero, one_mul, add_zero,
    ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show k + (j + 1) = k + 1 + j by omega]
  ring

/-- Woodford (2003), (3.1), p. 205: `|∑ aʲ f_{k+j}| ≤ M/(1 − a)`. -/
theorem fwdSum_abs_le {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → ℝ}
    (hf : ∀ k, |f k| ≤ M) (k : ℕ) : |fwdSum a f k| ≤ M / (1 - a) := by
  have hg : HasSum (fun j : ℕ => M * a ^ j) (M / (1 - a)) := by
    have := (hasSum_geometric_of_lt_one ha0 ha1).mul_left M
    simpa [div_eq_mul_inv] using this
  have := tsum_of_norm_bounded hg (f := fun j => a ^ j * f (k + j)) fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg ha0, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hf _) (pow_nonneg ha0 j)
  simpa [fwdSum, Real.norm_eq_abs] using this

/-- Woodford (2003), (3.1), p. 205: a nonnegative sequence that is positive at some date `K` has a
positive forward sum at every date `k ≤ K` (for `0 < a < 1`). -/
theorem fwdSum_pos {a M : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {f : ℕ → ℝ} (hf : ∀ k, |f k| ≤ M)
    (hnn : ∀ k, 0 ≤ f k) {k K : ℕ} (hkK : k ≤ K) (hK : 0 < f K) : 0 < fwdSum a f k := by
  refine (fwdSum_summable ha0.le ha1 hf k).tsum_pos (fun j => mul_nonneg (pow_nonneg ha0.le j)
    (hnn _)) (K - k) ?_
  rw [show k + (K - k) = K by omega]
  exact mul_pos (pow_pos ha0 _) hK

/-- Woodford (2003), (2.12) and (3.1), p. 205, for impulse responses: a bounded sequence with
`π_k = κ y_k + β π_{k+1}` (bounded `y`, `0 ≤ β < 1`) is `π_k = κ ∑ βʲ y_{k+j}`. -/
theorem det_forward {κ β M My : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {π y : ℕ → ℝ}
    (hπ : ∀ k, |π k| ≤ M) (hy : ∀ k, |y k| ≤ My) (h : ∀ k, π k = κ * y k + β * π (k + 1))
    (k : ℕ) : π k = κ * fwdSum β y k := by
  have := nkpc_forward perfectForesight (π := fun t _ => π t) (gap := fun t _ => y t)
    (κ := κ) hβ0 hβ1 (fun t _ => hy t) (fun _ => rfl) (fun t _ => hπ t)
    (fun t => funext fun _ => by
      change π t = κ * y t + β * π (t + 1)
      exact h t) k ()
  exact this

/-- Woodford (2003), p. 206 ("the effect on inflation should precede the effect on output,
insofar as the latter effect is predictable"): if the gap response `y ≥ 0` is positive at date
`K`, then inflation `π_k = κ ∑ βʲ y_{k+j}` is already positive at every `k ≤ K`, even where
`y_k = 0`. -/
theorem infl_precedes_output {κ β M : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) {y : ℕ → ℝ}
    (hy : ∀ k, |y k| ≤ M) (hnn : ∀ k, 0 ≤ y k) {k K : ℕ} (hkK : k ≤ K) (hK : 0 < y K) :
    0 < κ * fwdSum β y k :=
  mul_pos hκ (fwdSum_pos hβ0 hβ1 hy hnn hkK hK)

/-- Woodford (2003), p. 206 ("it should peak earlier than the effect on output"): if the gap
response is non-increasing from date `K` on, so is inflation `π_k = κ ∑ βʲ y_{k+j}`; hence
`π_k ≤ π_K` for all `k ≥ K` — inflation peaks no later than output. -/
theorem infl_peaks_no_later {κ β M : ℝ} (hκ : 0 ≤ κ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {y : ℕ → ℝ}
    (hy : ∀ k, |y k| ≤ M) {K : ℕ} (hdec : ∀ k, K ≤ k → y (k + 1) ≤ y k) :
    (∀ k, K ≤ k → κ * fwdSum β y (k + 1) ≤ κ * fwdSum β y k) ∧
      ∀ k, K ≤ k → κ * fwdSum β y k ≤ κ * fwdSum β y K := by
  have step : ∀ k, K ≤ k → κ * fwdSum β y (k + 1) ≤ κ * fwdSum β y k := by
    intro k hk
    refine mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum (fun j => ?_)
      (fwdSum_summable hβ0 hβ1 hy (k + 1)) (fwdSum_summable hβ0 hβ1 hy k)) hκ
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hβ0 j)
    rw [show k + 1 + j = k + j + 1 by omega]
    exact hdec (k + j) (by omega)
  refine ⟨step, fun k hk => ?_⟩
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (step k hk).trans ih

/-! ### §3.1: delayed price changes, (3.2) -/

/-- Woodford (2003), eq. (3.2), p. 208: the aggregate-supply relation with a delay `d`,
`π_{t+d} = κ E_t(Ŷ − Ŷⁿ)_{t+d} + β E_t π_{t+d+1}` for all `t` (dates `≥ d`). -/
def DelayedNKPC (κ β : ℝ) (d : ℕ) (π gap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π (t + d) = κ • 𝔼.E t (gap (t + d)) + β • 𝔼.E t (π (t + d + 1))

/-- Woodford (2003), p. 209: "the right-hand side of (3.2) consists entirely of terms that are a
function of period `t − d` information. Thus ... inflation `π_t` is a predetermined variable":
under (3.2), `E_t π_{t+d} = π_{t+d}`. -/
theorem delayed_predetermined {κ β : ℝ} {d : ℕ} {π gap : ℕ → Ω → ℝ}
    (h : DelayedNKPC 𝔼 κ β d π gap) (t : ℕ) : 𝔼.E t (π (t + d)) = π (t + d) := by
  rw [h t, map_add, map_smul, map_smul, 𝔼.E_E_self, 𝔼.E_E_self]

/-- Woodford (2003), p. 208 (the delayed Calvo model): if new prices for date `t + d + 1` are chosen
at `t + 1` (`p*_{t+d+1}` known at `t + 1`) and the price index follows
`log P_{t+d+1} = α(log P_{t+d} + γ π_{t+d}) + (1 − α) log p*_{t+d+1}` (with indexation `γ`,
`γ = 0` in §3.1), then from predetermined initial values the price level and inflation are
predetermined: `log P_{t+d}` and `π_{t+d}` are known at `t`. -/
theorem prices_predetermined {α γ : ℝ} {d : ℕ} {x π pstar : ℕ → Ω → ℝ}
    (hlaw : ∀ t, x (t + d + 1) = α • (x (t + d) + γ • π (t + d)) + (1 - α) • pstar (t + d + 1))
    (hπ : ∀ j, π (j + 1) = x (j + 1) - x j) (hp : ∀ t, 𝔼.E (t + 1) (pstar (t + d + 1)) =
      pstar (t + d + 1)) (hx0 : 𝔼.E 0 (x d) = x d) (hπ0 : 𝔼.E 0 (π d) = π d) (t : ℕ) :
    𝔼.E t (x (t + d)) = x (t + d) ∧ 𝔼.E t (π (t + d)) = π (t + d) := by
  induction t with
  | zero => simpa using ⟨hx0, hπ0⟩
  | succ t ih =>
    have hx1 : 𝔼.E (t + 1) (x (t + d)) = x (t + d) :=
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.1
    have hπ1 : 𝔼.E (t + 1) (π (t + d)) = π (t + d) :=
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih.2
    have hxn : 𝔼.E (t + 1) (x (t + 1 + d)) = x (t + 1 + d) := by
      rw [show t + 1 + d = t + d + 1 by omega, hlaw t, map_add, map_smul, map_smul, map_add,
        map_smul, hx1, hπ1, hp t]
    refine ⟨hxn, ?_⟩
    rw [show t + 1 + d = t + d + 1 by omega, hπ (t + d), map_sub, hx1]
    rw [show t + 1 + d = t + d + 1 by omega] at hxn
    rw [hxn]

/-- Woodford (2003), §3.2, (3.7), p. 217: if inflation is predetermined by `d = e + 1` periods and
`π_e` is known at date `0`, the quasi-differenced inflation `π_{t+d} − γ π_{t+d−1}` is also known
at `t`. -/
theorem quasiDiff_predetermined {γ : ℝ} {e : ℕ} {π : ℕ → Ω → ℝ}
    (hpre : ∀ t, 𝔼.E t (π (t + (e + 1))) = π (t + (e + 1))) (h0 : 𝔼.E 0 (π e) = π e) (t : ℕ) :
    𝔼.E t (π (t + (e + 1)) - γ • π (t + e)) = π (t + (e + 1)) - γ • π (t + e) := by
  have hlag : 𝔼.E t (π (t + e)) = π (t + e) := by
    cases t with
    | zero => simpa using h0
    | succ t =>
      have := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hpre t)
      rwa [show t + (e + 1) = t + 1 + e by omega] at this
  rw [map_sub, map_smul, hpre t, hlag]

/-- Woodford (2003), (3.2), p. 208 ("through a series of manipulations similar to those used in
the proof of Proposition 3.5"): suppose the reset price `Q_{t+d}` (relative to the index) that
takes effect at `t + d` is chosen at `t`, so that the linearised first-order condition (B.32)
holds with date-`t` expectations of the date-`(t + d + k)` variables, and the Calvo law of motion
`α ψ_{t+d} = (1 − α) Q_{t+d}` holds. If `ψ_{t+d}` is known at `t` (`prices_predetermined`), then
`ψ_{t+d} = ξ E_t m_{t+d} + β E_t ψ_{t+d+1}` — (3.2) for `ψ = π`, `ξ m = κ(Ŷ − Ŷⁿ)`; (3.7) for the
quasi-differenced `ψ = π − γπ_{−1}`. -/
theorem delayed_from_foc {α β ω θ Mψ Mm : ℝ} {d : ℕ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hA : 0 < 1 + ω * θ) {Q ψ m : ℕ → Ω → ℝ} (hψ : ∀ t o, |ψ t o| ≤ Mψ)
    (hm : ∀ t o, |m t o| ≤ Mm)
    (hfoc : ∀ t, TwoSector.LinFOC 𝔼 (α * β) (1 + ω * θ) (fun j => Q (j + d)) (fun j => ψ (j + d))
      (fun j => m (j + d)) t)
    (hlaw : ∀ t, α • ψ (t + d) = (1 - α) • Q (t + d))
    (hpre : ∀ t, 𝔼.E t (ψ (t + d)) = ψ (t + d)) (t : ℕ) :
    ψ (t + d) = calvoXi α β (ω * θ) • 𝔼.E t (m (t + d)) +
      β • 𝔼.E t (ψ (t + d + 1)) := by
  set Q' : ℕ → Ω → ℝ := fun j => 𝔼.E j (Q (j + d)) with hQ'
  set ψ' : ℕ → Ω → ℝ := fun j => 𝔼.E j (ψ (j + d)) with hψ'
  set m' : ℕ → Ω → ℝ := fun j => 𝔼.E j (m (j + d)) with hm'
  have hq0 : 0 ≤ α * β := by positivity
  have hq1 : α * β < 1 := by nlinarith
  have hψ'b : ∀ t o, |ψ' t o| ≤ Mψ := fun t o => 𝔼.abs_E_le (hψ (t + d)) t o
  have hm'b : ∀ t o, |m' t o| ≤ Mm := fun t o => 𝔼.abs_E_le (hm (t + d)) t o
  have hψ'a : 𝔼.Adapted ψ' := fun t => 𝔼.E_E_self t _
  have hm'a : 𝔼.Adapted m' := fun t => 𝔼.E_E_self t _
  -- the first-order condition in terms of the conditioned processes
  have hfoc' : ∀ t, TwoSector.LinFOC 𝔼 (α * β) (1 + ω * θ) Q' ψ' m' t := by
    intro t o
    have hsame : ∀ k, 𝔼.E t ((1 + ω * θ) • TwoSector.resetRel Q' ψ' t k - m' (t + k)) =
        𝔼.E t ((1 + ω * θ) • TwoSector.resetRel (fun j => Q (j + d)) (fun j => ψ (j + d)) t k -
          (fun j => m (j + d)) (t + k)) := by
      intro k
      simp only [TwoSector.resetRel, map_sub, map_smul, map_sum, hQ', hψ', hm', 𝔼.E_E_self,
        𝔼.tower (Nat.le_add_right t k)]
      rw [Finset.sum_congr rfl fun τ _ =>
        𝔼.tower (by omega : t ≤ t + τ + 1) (ψ (t + τ + 1 + d))]
    rw [← hfoc t o]
    exact tsum_congr fun k => by rw [hsame k]
  have hrel : ∀ t, Q' t = ((1 - α * β) / (1 + ω * θ)) • 𝔼.forwardSeries (α * β) m' t +
      TwoSector.tailSeries 𝔼 (α * β) ψ' t :=
    fun t => (TwoSector.linFOC_iff 𝔼 hq0 hq1 hA hψ'b hm'b t (𝔼.E_E_self t _)).mp (hfoc' t)
  have hlaw' : ∀ t, α • ψ' t = (1 - α) • Q' t := fun t => by
    simp only [hψ', hQ', ← map_smul, hlaw t]
  have hnk := ((TwoSector.relative_law_iff_nkpc 𝔼 hα0 hα1 hβ0 hβ1 hA hψ'b hψ'a hm'b hm'a).mp
    ⟨hrel, hlaw'⟩).1 t
  have hE1 : 𝔼.E t (ψ' (t + 1)) = 𝔼.E t (ψ (t + d + 1)) := by
    simp only [hψ', 𝔼.tower (Nat.le_succ t)]
    rw [show t + 1 + d = t + d + 1 by omega]
  rw [hE1] at hnk
  rw [← hpre t]
  exact hnk

/-- Woodford (2003), (3.2), p. 208: a bounded solution of (3.2) (bounded gap) satisfies
`π_{t+d} = κ ∑_j βʲ E_t(Ŷ − Ŷⁿ)_{t+d+j}`. -/
theorem delayed_forward {κ β Mg M : ℝ} {d : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {π gap : ℕ → Ω → ℝ} (hg : ∀ t o, |gap t o| ≤ Mg) (hπ : ∀ t o, |π t o| ≤ M)
    (h : DelayedNKPC 𝔼 κ β d π gap) (t : ℕ) (o : Ω) :
    π (t + d) o = κ * ∑' j, β ^ j * 𝔼.E t (gap (t + d + j)) o := by
  set u : ℕ → Ω → ℝ := fun j => κ • 𝔼.E j (gap (j + d)) with hu
  have hub : ∀ t o, |u t o| ≤ |κ| * Mg := fun t o => by
    simp only [hu, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hg _) t o) (abs_nonneg κ)
  have hua : 𝔼.Adapted u := fun t => by simp only [hu, map_smul, 𝔼.E_E_self]
  have hs : ∀ t, (fun j => π (j + d)) t = β • 𝔼.E t ((fun j => π (j + d)) (t + 1)) + u t := by
    intro t
    simp only [hu]
    rw [h t, add_comm, show t + 1 + d = t + d + 1 by omega]
  have := 𝔼.eq_forwardSeries hβ0 hβ1 hub hua hs ⟨M, fun t o => hπ (t + d) o⟩
  have h2 := congrFun (congrFun this t) o
  rw [h2]
  change ∑' k, β ^ k * 𝔼.E t (κ • 𝔼.E (t + k) (gap (t + k + d))) o = _
  rw [← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [map_smul, 𝔼.tower (Nat.le_add_right t j), Pi.smul_apply, smul_eq_mul,
    show t + j + d = t + d + j by omega]
  ring

/-- Woodford (2003), (3.2), p. 208: for a bounded gap there is exactly one bounded process
`z_t = π_{t+d}` solving (3.2). -/
theorem delayed_existsUnique {κ β : ℝ} {d : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {gap : ℕ → Ω → ℝ} (hgb : BoundedProc gap) :
    ∃! z : ℕ → Ω → ℝ, BoundedProc z ∧
      ∀ t, z t = κ • 𝔼.E t (gap (t + d)) + β • 𝔼.E t (z (t + 1)) := by
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  obtain ⟨Mg, hg⟩ := hgb
  set u : ℕ → Ω → ℝ := fun j => κ • 𝔼.E j (gap (j + d)) with hu
  have hub : BoundedProc u := ⟨|κ| * Mg, fun t o => by
    simp only [hu, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hg _) t o) (abs_nonneg κ)⟩
  have hua : 𝔼.Adapted u := fun t => by simp only [hu, map_smul, 𝔼.E_E_self]
  obtain ⟨z, ⟨hzb, hzs⟩, huniq⟩ := ForwardSolution.existsUnique_bounded 𝔼 hβ hub hua
  refine ⟨z, ⟨hzb, fun t => by rw [hzs t, add_comm]⟩, fun y ⟨hyb, hys⟩ => huniq y ⟨hyb, ?_⟩⟩
  intro t
  rw [hys t, add_comm]

/-- Woodford (2003), p. 209: "only fluctuations in `E_{t−d} Ŷ_tⁿ`, the forecastable component of
the natural rate of output, matter": two bounded gap processes with the same date-`t` forecasts
of all dates `t + d + j` give the same bounded inflation `π_{t+d}`. -/
theorem delayed_depends_on_forecasts {κ β Mg1 Mg2 M1 M2 : ℝ} {d : ℕ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) {π1 π2 g1 g2 : ℕ → Ω → ℝ} (hg1 : ∀ t o, |g1 t o| ≤ Mg1)
    (hg2 : ∀ t o, |g2 t o| ≤ Mg2) (hπ1 : ∀ t o, |π1 t o| ≤ M1) (hπ2 : ∀ t o, |π2 t o| ≤ M2)
    (h1 : DelayedNKPC 𝔼 κ β d π1 g1) (h2 : DelayedNKPC 𝔼 κ β d π2 g2)
    (hf : ∀ t j, 𝔼.E t (g1 (t + d + j)) = 𝔼.E t (g2 (t + d + j))) (t : ℕ) :
    π1 (t + d) = π2 (t + d) := by
  funext o
  rw [delayed_forward 𝔼 hβ0 hβ1 hg1 hπ1 h1 t o, delayed_forward 𝔼 hβ0 hβ1 hg2 hπ2 h2 t o]
  simp only [hf]

/-- Woodford (2003), p. 209: "a monetary policy shock in period `t` has no effect on inflation
before period `t + d`": under (3.2) (with inflation for the first `d` dates known at date `0`),
the news arriving at date `s + 1` does not revise `π_{s+1+k}` for `k < d`:
`E_{s+1} π_{s+1+k} = E_s π_{s+1+k}`. -/
theorem revision_zero_before_delay {κ β : ℝ} {d : ℕ} {π gap : ℕ → Ω → ℝ}
    (h : DelayedNKPC 𝔼 κ β d π gap) (hinit : ∀ k < d, 𝔼.E 0 (π k) = π k) (s k : ℕ)
    (hk : k < d) : 𝔼.E (s + 1) (π (s + 1 + k)) = 𝔼.E s (π (s + 1 + k)) := by
  have hknown : 𝔼.E s (π (s + 1 + k)) = π (s + 1 + k) := by
    by_cases hd : d ≤ s + 1 + k
    · obtain ⟨j, hj⟩ : ∃ j, s + 1 + k = j + d := ⟨s + 1 + k - d, by omega⟩
      rw [hj]
      exact ForwardSolution.E_of_known 𝔼 (by omega) (delayed_predetermined 𝔼 h j)
    · exact ForwardSolution.E_of_known 𝔼 (Nat.zero_le s) (hinit _ (by omega))
  rw [hknown, ForwardSolution.E_of_known 𝔼 (Nat.le_succ s) hknown]

/-- Woodford (2003), (3.2) and (2.16), pp. 189 and 211: for `k ≥ d` the revisions
`R x = E_{s+1} x − E_s x` obey `R π_{s+1+k} = κ R(Ŷ − Ŷⁿ)_{s+1+k} + β R π_{s+2+k}`. -/
theorem revision_recursion {κ β : ℝ} {d : ℕ} {π gap : ℕ → Ω → ℝ}
    (h : DelayedNKPC 𝔼 κ β d π gap) (s k : ℕ) (hk : d ≤ k) :
    𝔼.E (s + 1) (π (s + 1 + k)) - 𝔼.E s (π (s + 1 + k)) =
      κ • (𝔼.E (s + 1) (gap (s + 1 + k)) - 𝔼.E s (gap (s + 1 + k))) +
        β • (𝔼.E (s + 1) (π (s + 1 + k + 1)) - 𝔼.E s (π (s + 1 + k + 1))) := by
  obtain ⟨j, hj⟩ : ∃ j, s + 1 + k = j + d := ⟨s + 1 + k - d, by omega⟩
  have hsj : s + 1 ≤ j := by omega
  rw [hj, h j]
  simp only [map_add, map_smul, 𝔼.tower hsj, 𝔼.tower (by omega : s ≤ j)]
  rw [smul_sub, smul_sub]
  abel

/-! ### Impulse responses: the delayed system and its unique bounded solution -/

/-- Woodford (2003), (2.16)–(2.18), pp. 189–190, and (3.2), p. 208: the impulse-response system
with delay `d` for the lagged price-level response `P` (`P 0 = p̃_{−1} = 0`, `P (k + 1) = p̃_k`)
given the nominal-GDP response `n`: `p̃_k − p̃_{k−1} = 0` for `k < d` and
`p̃_k − p̃_{k−1} = κ(ñ_k − p̃_k) + β(p̃_{k+1} − p̃_k)` for `k ≥ d`. -/
def DelayIRF (κ β : ℝ) (d : ℕ) (n P : ℕ → ℝ) : Prop :=
  P 0 = 0 ∧ (∀ k, k < d → P (k + 1) = P k) ∧
    ∀ k, d ≤ k → P (k + 1) - P k = κ * (n k - P (k + 1)) + β * (P (k + 2) - P (k + 1))

/-- Woodford (2003), Figures 3.9–3.16: the system `DelayIRF` is linear, so the response to a shock
of size `c` is `c` times the unit response. -/
theorem irf_smul {κ β c : ℝ} {d : ℕ} {n P : ℕ → ℝ} (h : DelayIRF κ β d n P) :
    DelayIRF κ β d (fun k => c * n k) (fun k => c * P k) := by
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨by simp [h0], fun k hk => by simp [h1 k hk], fun k hk => ?_⟩
  have := h2 k hk
  linear_combination c * this

/-- Woodford (2003), (2.16)–(2.18), pp. 189–190 and (3.2): the impulse-response system has at most
one bounded solution (`κ > 0`, `β ≥ 0`), by a maximum principle: the difference `D` of two
solutions vanishes up to date `d` and obeys `(1 + β + κ) D_{k+1} = β D_{k+2} + D_k` after, so
`sup |D| ≤ (1 + β)/(1 + β + κ) · sup |D|`. -/
theorem irf_unique {κ β : ℝ} (hκ : 0 < κ) (hβ : 0 ≤ β) {d : ℕ} {n P P' : ℕ → ℝ}
    (h : DelayIRF κ β d n P) (h' : DelayIRF κ β d n P') (hb : ∃ M, ∀ k, |P k| ≤ M)
    (hb' : ∃ M, ∀ k, |P' k| ≤ M) : P = P' := by
  obtain ⟨M, hM⟩ := hb
  obtain ⟨M', hM'⟩ := hb'
  obtain ⟨h0, h1, h2⟩ := h
  obtain ⟨h0', h1', h2'⟩ := h'
  set D : ℕ → ℝ := fun k => P k - P' k with hD
  have hDle : ∀ j, j ≤ d → D j = 0 := by
    intro j hj
    induction j with
    | zero => simp [hD, h0, h0']
    | succ j ih =>
      simp only [hD] at ih ⊢
      rw [h1 j (by omega), h1' j (by omega)]
      exact ih (by omega)
  have hrec : ∀ k, d ≤ k → (1 + β + κ) * D (k + 1) = β * D (k + 2) + D k := by
    intro k hk
    have e := h2 k hk
    have e' := h2' k hk
    simp only [hD]
    linear_combination e - e'
  set B := M + M' with hB
  have hDB : ∀ j, |D j| ≤ B := fun j =>
    (abs_sub _ _).trans (add_le_add (hM j) (hM' j))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hDB 0)
  set c := (1 + β) / (1 + β + κ) with hc
  have hpos : 0 < 1 + β + κ := by linarith
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by rw [hc, div_lt_one hpos]; linarith
  have step : ∀ C, (∀ j, |D j| ≤ C) → ∀ j, |D j| ≤ c * C := by
    intro C hC j
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    by_cases hj : j ≤ d
    · rw [hDle j hj, abs_zero]; positivity
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hk : d ≤ k := by omega
      have e : D (k + 1) = (β * D (k + 2) + D k) / (1 + β + κ) := by
        rw [← hrec k hk]; field_simp
      rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos, hc, div_mul_eq_mul_div,
        div_mul_cancel₀ _ hpos.ne']
      calc |β * D (k + 2) + D k| ≤ β * C + C := by
            refine (abs_add_le _ _).trans (add_le_add ?_ (hC k))
            rw [abs_mul, abs_of_nonneg hβ]
            exact mul_le_mul_of_nonneg_left (hC _) hβ
        _ = (1 + β) * C := by ring
  have hiter : ∀ m : ℕ, ∀ j, |D j| ≤ c ^ m * B := by
    intro m
    induction m with
    | zero => simpa using hDB
    | succ m ih =>
      intro j
      have := step _ ih j
      rwa [pow_succ, mul_comm (c ^ m) c, mul_assoc]
  funext j
  have hlim : Tendsto (fun m : ℕ => c ^ m * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const B
  have h00 : |D j| ≤ 0 := ge_of_tendsto' hlim fun m => hiter m j
  have : D j = 0 := abs_nonpos_iff.mp h00
  simpa [hD, sub_eq_zero] using this

/-! ### The roots of `βλ² − (1 + β + κ)λ + 1`

The roots `λ₁ < λ₂` and their properties are those of `QuadraticRoots` (with `c = κ`). -/

/-- Woodford (2003), Propositions 3.6–3.7 (App. B.5–B.6) and Figure 3.9: the bounded solution of
`DelayIRF κ β 0 n` built from the roots: `p̃_k = λ₁ p̃_{k−1} + κλ₁ ∑_j (βλ₁)ʲ ñ_{k+j}`. -/
noncomputable def irfP (β κ : ℝ) (n : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => lam1 β κ * irfP β κ n k + κ * lam1 β κ * fwdSum (β * lam1 β κ) n k

/-- Woodford (2003), (2.16)–(2.18), pp. 189–190 and Figure 3.9: for bounded `n` the sequence
`irfP` is a bounded solution of the undelayed system (existence). -/
theorem irf_exists {β κ Mn : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) {n : ℕ → ℝ}
    (hn : ∀ k, |n k| ≤ Mn) :
    DelayIRF κ β 0 n (irfP β κ n) ∧ ∃ M, ∀ k, |irfP β κ n k| ≤ M := by
  obtain ⟨hl0, hl1, -, -⟩ := root_location hβ0 hβ1 hκ
  have hsum := beta_mul_sum (c := κ) hβ0
  have hprod := beta_mul_prod hβ0 hκ
  set l1 := lam1 β κ
  set l2 := lam2 β κ
  have ha0 : 0 ≤ β * l1 := by positivity
  have ha1 : β * l1 < 1 := by
    have : β * l1 < 1 * 1 := mul_lt_mul'' hβ1 hl1 hβ0.le hl0.le
    linarith
  have hrec := fwdSum_rec ha0 ha1 hn
  refine ⟨⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k), fun k _ => ?_⟩, ?_⟩
  · -- the second-order recursion from the factorisation `β(1 − λ₁L)(1 − λ₂L)`
    have e1 : irfP β κ n (k + 2) =
        l1 * irfP β κ n (k + 1) + κ * l1 * fwdSum (β * l1) n (k + 1) := rfl
    have e0 : irfP β κ n (k + 1) = l1 * irfP β κ n k + κ * l1 * fwdSum (β * l1) n k := rfl
    rw [e1, e0, hrec k]
    linear_combination (-(l1 * irfP β κ n k + κ * l1 * (n k + β * l1 *
      fwdSum (β * l1) n (k + 1)))) * hsum + (irfP β κ n k + κ * n k + κ * β * l1 *
      fwdSum (β * l1) n (k + 1)) * hprod
  · set W := κ * l1 * (Mn / (1 - β * l1)) with hW
    have hW0 : 0 ≤ W := by
      have : 0 ≤ Mn := (abs_nonneg _).trans (hn 0)
      have : 0 < 1 - β * l1 := by linarith
      positivity
    refine ⟨W / (1 - l1), fun k => ?_⟩
    induction k with
    | zero => simp only [irfP, abs_zero]; exact div_nonneg hW0 (by linarith)
    | succ k ih =>
      change |l1 * irfP β κ n k + κ * l1 * fwdSum (β * l1) n k| ≤ W / (1 - l1)
      have hF : |κ * l1 * fwdSum (β * l1) n k| ≤ W := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < κ * l1)]
        exact mul_le_mul_of_nonneg_left (fwdSum_abs_le ha0 ha1 hn k) (by positivity)
      have h1l : 0 < 1 - l1 := by linarith
      calc |l1 * irfP β κ n k + κ * l1 * fwdSum (β * l1) n k|
          ≤ l1 * (W / (1 - l1)) + W := by
            refine (abs_add_le _ _).trans (add_le_add ?_ hF)
            rw [abs_mul, abs_of_pos hl0]
            exact mul_le_mul_of_nonneg_left ih hl0.le
        _ = W / (1 - l1) := by field_simp; ring

/-- Woodford (2003), p. 211, Figures 3.11–3.12: under (3.2) with gap `Ŷ − Ŷⁿ = log Y − log P`
(the natural rate not revised by the monetary shock), `π_{j+1} = log P_{j+1} − log P_j` and an
adapted price level, the revisions caused by the news at date `s + 1` — of nominal GDP,
`ñ_k = R log Y_{s+1+k}`, and of the price level, `P_j = R log P_{s+j}` (so `P_0 = 0`) — solve the
delayed impulse-response system `DelayIRF κ β d ñ P` in every state. -/
theorem revision_irf {κ β : ℝ} {d s : ℕ} {π gap n p : ℕ → Ω → ℝ}
    (h : DelayedNKPC 𝔼 κ β d π gap) (hinit : ∀ k < d, 𝔼.E 0 (π k) = π k)
    (hgap : ∀ t, gap t = n t - p t) (hπp : ∀ j, π (j + 1) = p (j + 1) - p j)
    (hp : 𝔼.Adapted p) (o : Ω) :
    DelayIRF κ β d (fun k => (𝔼.E (s + 1) (n (s + 1 + k)) - 𝔼.E s (n (s + 1 + k))) o)
      (fun j => (𝔼.E (s + 1) (p (s + j)) - 𝔼.E s (p (s + j))) o) := by
  have hinc : ∀ k, (𝔼.E (s + 1) (p (s + (k + 1))) - 𝔼.E s (p (s + (k + 1)))) o -
      (𝔼.E (s + 1) (p (s + k)) - 𝔼.E s (p (s + k))) o =
      (𝔼.E (s + 1) (π (s + 1 + k)) - 𝔼.E s (π (s + 1 + k))) o := by
    intro k
    rw [show s + 1 + k = s + k + 1 by omega, hπp (s + k), show s + (k + 1) = s + k + 1 by omega]
    simp only [map_sub, Pi.sub_apply]
    ring
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ,
      A = fun j => (𝔼.E (s + 1) (p (s + j)) - 𝔼.E s (p (s + j))) o := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ,
      G = fun k => (𝔼.E (s + 1) (n (s + 1 + k)) - 𝔼.E s (n (s + 1 + k))) o := ⟨_, rfl⟩
  rw [← hA, ← hG]
  have hAk : ∀ k, A (k + 1) - A k =
      (𝔼.E (s + 1) (π (s + 1 + k)) - 𝔼.E s (π (s + 1 + k))) o := fun k => by
    rw [hA]; exact hinc k
  refine ⟨?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hA]
    simp only [add_zero, Pi.sub_apply]
    rw [ForwardSolution.E_of_known 𝔼 (Nat.le_succ s) (hp s), hp s, sub_self]
  · have h0 := revision_zero_before_delay 𝔼 h hinit s k hk
    have := hAk k
    rw [h0, sub_self, Pi.zero_apply] at this
    linarith
  · have hr := congrFun (revision_recursion 𝔼 h s k hk) o
    have h1 := hAk k
    have h2 := hAk (k + 1)
    have hA1 : A (k + 1) = (𝔼.E (s + 1) (p (s + 1 + k)) - 𝔼.E s (p (s + 1 + k))) o := by
      rw [hA]
      beta_reduce
      rw [show s + (k + 1) = s + 1 + k by omega]
    rw [show k + 1 + 1 = k + 2 from rfl, show s + 1 + (k + 1) = s + 1 + k + 1 by omega] at h2
    rw [hG]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hgap, map_sub]
      at hr h1 h2 hA1 ⊢
    linear_combination h1 + hr + κ * hA1 - β * h2

/-! ### The shift theorem (Figure 3.12) -/

/-- Woodford (2003), Figure 3.12, p. 211: the sequence `f` delayed by `d` periods (zero before). -/
noncomputable def shiftSeq (d : ℕ) (f : ℕ → ℝ) (k : ℕ) : ℝ := if k < d then 0 else f (k - d)

/-- Woodford (2003), Figure 3.12, p. 211: if `P` solves the undelayed system for the input `m`,
then `P` delayed by `d` periods solves the system with delay `d` for the input `m` delayed by `d`
periods. -/
theorem shift_solves {κ β : ℝ} {d : ℕ} {m P : ℕ → ℝ} (h : DelayIRF κ β 0 m P) :
    DelayIRF κ β d (shiftSeq d m) (fun j => if j ≤ d then 0 else P (j - d)) := by
  obtain ⟨h0, -, h2⟩ := h
  have e : ∀ i, (if d + i ≤ d then (0 : ℝ) else P (d + i - d)) = P i := by
    intro i
    rcases i with _ | i
    · simp [h0]
    · simp only [show ¬ (d + (i + 1) ≤ d) by omega, ↓reduceIte]
      congr 1; omega
  refine ⟨by simp, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [show k + 1 ≤ d by omega, show k ≤ d by omega, ↓reduceIte]
  · obtain ⟨j, rfl⟩ : ∃ j, k = d + j := ⟨k - d, by omega⟩
    have hj := h2 j (Nat.zero_le j)
    have hs : shiftSeq d m (d + j) = m j := by
      simp only [shiftSeq, show ¬ (d + j < d) by omega, ↓reduceIte]
      congr 1; omega
    simp only
    rw [show d + j + 1 = d + (j + 1) by omega, show d + j + 2 = d + (j + 2) by omega, e, e, e,
      hs]
    exact hj

/-- Woodford (2003), Figures 3.12–3.13, pp. 211–212: with a delay `d`, the price level does not
respond before date `d`, so output moves one-for-one with nominal GDP until then (and not at all
when nominal GDP is itself delayed by `s ≥ d`). -/
theorem delayed_output_eq_nominal {κ β : ℝ} {d : ℕ} {n P : ℕ → ℝ} (h : DelayIRF κ β d n P)
    (k : ℕ) (hk : k < d) : P (k + 1) = 0 ∧ n k - P (k + 1) = n k := by
  obtain ⟨h0, h1, -⟩ := h
  have : ∀ j, j ≤ d → P j = 0 := by
    intro j hj
    induction j with
    | zero => exact h0
    | succ j ih => rw [h1 j (by omega)]; exact ih (by omega)
  have hz := this (k + 1) (by omega)
  exact ⟨hz, by rw [hz, sub_zero]⟩

/-- Woodford (2003), eq. (3.3), p. 209 and (2.21), p. 191: the response of `log Y` (nominal GDP)
to an innovation of size `1 − ρ` whose effect is delayed `s` periods: `0` before `s`, then
`1 − ρ^{k−s+1}`. -/
noncomputable def nomIRF (ρ : ℝ) (s k : ℕ) : ℝ := if k < s then 0 else 1 - ρ ^ (k - s + 1)

/-- Woodford (2003), (3.3), p. 209: the growth rate of the nominal-GDP response is the AR(1)
response `0` before `s`, `(1 − ρ)ρ^{k−s}` from `s` on (`Δ log Y_t = ρ Δ log Y_{t−1} + ε_{t−s}`
with innovation `1 − ρ`); its level starts at `0` (for `s ≥ 1`) or `1 − ρ` (for `s = 0`). -/
theorem nomIRF_growth (ρ : ℝ) (s : ℕ) :
    nomIRF ρ s 0 = (if s = 0 then 1 - ρ else 0) ∧
      ∀ k, nomIRF ρ s (k + 1) - nomIRF ρ s k =
        if k + 1 < s then 0 else (1 - ρ) * ρ ^ (k + 1 - s) := by
  refine ⟨?_, fun k => ?_⟩
  · rcases Nat.eq_zero_or_pos s with hs | hs
    · simp [nomIRF, hs]
    · simp [nomIRF, hs, hs.ne']
  · unfold nomIRF
    by_cases h1 : k + 1 < s
    · simp [h1, show k < s by omega]
    · by_cases h2 : k < s
      · have : k + 1 = s := by omega
        simp [h2, this]
      · simp only [h1, h2, ↓reduceIte]
        rw [show k + 1 - s + 1 = (k - s + 1) + 1 by omega, show k + 1 - s = k - s + 1 by omega,
          pow_succ]
        ring

/-- Woodford (2003), (3.3), p. 209: the nominal-GDP response with lag `s` is the `s = 0` response
of (2.21) delayed by `s` periods. -/
theorem nomIRF_shift (ρ : ℝ) (s : ℕ) : nomIRF ρ s = shiftSeq s (nomIRF ρ 0) := by
  funext k
  unfold nomIRF shiftSeq
  by_cases h : k < s
  · simp [h]
  · simp [h]

/-- Woodford (2003), (2.21), p. 191: for `0 ≤ ρ < 1` the nominal-GDP response lies in `[0, 1]`
and equals `1 − ρ > 0` at date `s`. -/
theorem nomIRF_bounds {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (s : ℕ) :
    (∀ k, 0 ≤ nomIRF ρ s k ∧ nomIRF ρ s k ≤ 1) ∧ nomIRF ρ s s = 1 - ρ := by
  refine ⟨fun k => ?_, by simp [nomIRF]⟩
  unfold nomIRF
  by_cases h : k < s
  · simp [h]
  · simp only [h, ↓reduceIte]
    have h1 : ρ ^ (k - s + 1) ≤ 1 := pow_le_one₀ hρ0 hρ1.le
    have h2 : 0 ≤ ρ ^ (k - s + 1) := pow_nonneg hρ0 _
    constructor <;> linarith

/-- Woodford (2003), **Figure 3.12**, p. 211 ("the predicted responses of all variables are
exactly the same as in Figure 3.9, except that all the impulse-response functions are shifted
to the right by two quarters"): with nominal GDP delayed `s = d` periods and price changes
delayed `d` periods, the bounded impulse responses exist and are unique, and the price level,
inflation and output responses are those of the `s = d = 0` model (Figure 3.9) shifted right by
`d` periods. -/
theorem fig_3_12 {κ β ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (d : ℕ) :
    (∃ Pd : ℕ → ℝ, DelayIRF κ β d (nomIRF ρ d) Pd ∧ ∃ M, ∀ k, |Pd k| ≤ M) ∧
      ∀ Pd : ℕ → ℝ, DelayIRF κ β d (nomIRF ρ d) Pd → (∃ M, ∀ k, |Pd k| ≤ M) →
        ∀ k, Pd (k + 1) = shiftSeq d (fun j => irfP β κ (nomIRF ρ 0) (j + 1)) k ∧
          Pd (k + 1) - Pd k =
            shiftSeq d (fun j => irfP β κ (nomIRF ρ 0) (j + 1) - irfP β κ (nomIRF ρ 0) j) k ∧
          nomIRF ρ d k - Pd (k + 1) =
            shiftSeq d (fun j => nomIRF ρ 0 j - irfP β κ (nomIRF ρ 0) (j + 1)) k := by
  have hn : ∀ k, |nomIRF ρ 0 k| ≤ 1 := fun k => by
    have := (nomIRF_bounds hρ0 hρ1 0).1 k
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hP0, M0, hM0⟩ := irf_exists hβ0 hβ1 hκ hn
  set P0 := irfP β κ (nomIRF ρ 0)
  have hsol := shift_solves (d := d) hP0
  rw [← nomIRF_shift] at hsol
  set P' : ℕ → ℝ := fun j => if j ≤ d then 0 else P0 (j - d) with hP'
  have hbP' : ∃ M, ∀ k, |P' k| ≤ M := ⟨|M0|, fun k => by
    simp only [hP']
    split_ifs
    · simp
    · exact (hM0 _).trans (le_abs_self _)⟩
  refine ⟨⟨P', hsol, hbP'⟩, fun Pd hPd hbd k => ?_⟩
  have heq : Pd = P' := irf_unique hκ hβ0.le hPd hsol hbd hbP'
  subst heq
  have hlo : ∀ j, j ≤ d → P' j = 0 := fun j hj => by simp [hP', hj]
  have hhi : ∀ j, d ≤ j → P' j = P0 (j - d) := by
    intro j hj
    by_cases hjd : j ≤ d
    · have : j = d := by omega
      subst this
      simp [hP', hP0.1]
    · simp [hP', hjd]
  refine ⟨?_, ?_, ?_⟩
  · simp only [shiftSeq]
    by_cases hk : k < d
    · simp [hk, hlo (k + 1) (by omega)]
    · simp only [hk, ↓reduceIte]
      rw [hhi (k + 1) (by omega), show k + 1 - d = k - d + 1 by omega]
  · simp only [shiftSeq]
    by_cases hk : k < d
    · simp [hk, hlo (k + 1) (by omega), hlo k (by omega)]
    · simp only [hk, ↓reduceIte]
      rw [hhi (k + 1) (by omega), hhi k (by omega), show k + 1 - d = k - d + 1 by omega]
  · rw [nomIRF_shift ρ d]
    simp only [shiftSeq]
    by_cases hk : k < d
    · simp [hk, hlo (k + 1) (by omega)]
    · simp only [hk, ↓reduceIte]
      rw [hhi (k + 1) (by omega), show k + 1 - d = k - d + 1 by omega]

/-- Woodford (2003), Figure 3.12, p. 211, for the stochastic model: if (3.2) holds and the news at
date `s + 1` revises nominal GDP by `ε · nomIRF ρ d` (an innovation of size `ε(1 − ρ)` with lag
`d`), and the price-level revisions are bounded, then they are exactly `ε` times the Figure 3.9
response (the `s = d = 0` impulse response) shifted right by `d` periods. -/
theorem fig_3_12_stochastic {κ β ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {d s : ℕ} {π gap n p : ℕ → Ω → ℝ}
    (h : DelayedNKPC 𝔼 κ β d π gap) (hinit : ∀ k < d, 𝔼.E 0 (π k) = π k)
    (hgap : ∀ t, gap t = n t - p t) (hπp : ∀ j, π (j + 1) = p (j + 1) - p j)
    (hp : 𝔼.Adapted p) (ε : Ω → ℝ) (o : Ω)
    (hn : ∀ k, (𝔼.E (s + 1) (n (s + 1 + k)) - 𝔼.E s (n (s + 1 + k))) o = ε o * nomIRF ρ d k)
    (hb : ∃ M, ∀ j, |(𝔼.E (s + 1) (p (s + j)) - 𝔼.E s (p (s + j))) o| ≤ M) (k : ℕ) :
    (𝔼.E (s + 1) (p (s + 1 + k)) - 𝔼.E s (p (s + 1 + k))) o =
      ε o * shiftSeq d (fun j => irfP β κ (nomIRF ρ 0) (j + 1)) k := by
  have hrev := revision_irf 𝔼 (s := s) h hinit hgap hπp hp o
  rw [show (fun k => (𝔼.E (s + 1) (n (s + 1 + k)) - 𝔼.E s (n (s + 1 + k))) o) =
    fun k => ε o * nomIRF ρ d k from funext hn] at hrev
  obtain ⟨⟨P', hP', M', hM'⟩, hall⟩ := fig_3_12 hκ hβ0 hβ1 hρ0 hρ1 d
  have hsc := irf_smul (c := ε o) hP'
  have heq := irf_unique hκ hβ0.le hrev hsc hb ⟨|ε o| * |M'|, fun j => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hM' j).trans (le_abs_self _)) (abs_nonneg _)⟩
  have := congrFun heq (k + 1)
  rw [show s + 1 + k = s + (k + 1) by omega, this, (hall P' hP' ⟨M', hM'⟩ k).1]

/-- Woodford (2003), Figure 3.11, pp. 210–211: with `κ > 0`, `0 < β < 1`, a nonnegative bounded
nominal-GDP response that is positive at some date has a positive price response on impact,
`p̃_0 > 0` (prices rise in anticipation). -/
theorem irfP_one_pos {β κ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) {n : ℕ → ℝ}
    (hn : ∀ k, |n k| ≤ M) (hnn : ∀ k, 0 ≤ n k) {K : ℕ} (hK : 0 < n K) : 0 < irfP β κ n 1 := by
  obtain ⟨hl0, hl1, -, -⟩ := root_location hβ0 hβ1 hκ
  have ha1 : β * lam1 β κ < 1 := by
    have : β * lam1 β κ < 1 * 1 := mul_lt_mul'' hβ1 hl1 hβ0.le hl0.le
    linarith
  change 0 < lam1 β κ * 0 + κ * lam1 β κ * fwdSum (β * lam1 β κ) n 0
  rw [mul_zero, zero_add]
  exact mul_pos (mul_pos hκ hl0) (fwdSum_pos (mul_pos hβ0 hl0) ha1 hn hnn (Nat.zero_le K) hK)

/-- Woodford (2003), **Figure 3.11**, p. 210 ("a monetary disturbance that is expected to increase
nominal expenditure beginning two periods later should contract real activity in the short
run"): in the basic model (`d = 0`), if nominal GDP does not move on impact (`n_0 = 0`) but rises
later (`n ≥ 0`, `n_K > 0`), the bounded response has inflation `p̃_0 > 0` and output
`ñ_0 − p̃_0 < 0` on impact. -/
theorem fig_3_11_general {κ β M : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) {n P : ℕ → ℝ}
    (hn : ∀ k, |n k| ≤ M) (hnn : ∀ k, 0 ≤ n k) (hn0 : n 0 = 0) {K : ℕ} (hK : 0 < n K)
    (hP : DelayIRF κ β 0 n P) (hb : ∃ M, ∀ k, |P k| ≤ M) :
    0 < P 1 - P 0 ∧ n 0 - P 1 < 0 := by
  obtain ⟨hex, hbex⟩ := irf_exists hβ0 hβ1 hκ hn
  have heq := irf_unique hκ hβ0.le hP hex hb hbex
  have hpos := irfP_one_pos hβ0 hβ1 hκ hn hnn hK
  rw [heq, hn0]
  have h0 : irfP β κ n 0 = 0 := rfl
  constructor <;> linarith

/-- Woodford (2003), **Figure 3.11**, p. 210: for the nominal-GDP process (3.3) with lag `s ≥ 1`
(Figure 3.11: `s = 2`) and the basic Phillips curve (`d = 0`), output contracts on impact. -/
theorem fig_3_11_contraction {κ β ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {s : ℕ} (hs : 1 ≤ s) {P : ℕ → ℝ}
    (hP : DelayIRF κ β 0 (nomIRF ρ s) P) (hb : ∃ M, ∀ k, |P k| ≤ M) :
    0 < P 1 - P 0 ∧ nomIRF ρ s 0 - P 1 < 0 := by
  obtain ⟨hbd, hss⟩ := nomIRF_bounds hρ0 hρ1 s
  refine fig_3_11_general hκ hβ0 hβ1 (M := 1) (fun k => ?_) (fun k => (hbd k).1) ?_ (K := s)
    ?_ hP hb
  · rw [abs_le]; constructor <;> linarith [(hbd k).1, (hbd k).2]
  · simp [nomIRF, show 0 < s by omega]
  · rw [hss]; linarith

/-! ### §3.2: indexation to past inflation -/

/-- Woodford (2003), p. 213 (Yun 1996): with automatic indexation at the long-run rate `π̄`,
`π_t = (1 − β)π̄ + κ(Ŷ_t − Ŷ_tⁿ) + β E_t π_{t+1}` is (2.12) for `π − π̄`. -/
theorem yun_iff {κ β πbar : ℝ} {π gap : ℕ → Ω → ℝ} (t : ℕ) :
    π t = (1 - β) • (fun _ => πbar) + κ • gap t + β • 𝔼.E t (π (t + 1)) ↔
      π t - (fun _ => πbar) = κ • gap t + β • 𝔼.E t (π (t + 1) - fun _ => πbar) := by
  rw [map_sub, 𝔼.const]
  constructor <;> intro h <;> funext o <;> have := congrFun h o <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢ <;> linarith

/-- Woodford (2003), p. 213: Yun's relation implies a vertical long-run Phillips curve: in a
steady state with constant inflation `π` and gap `g`, `κ g = (1 − β)(π − π̄)`, so when the
indexation rate matches long-run inflation (`π̄ = π`) the long-run gap is zero whatever `π`;
without indexation (`π̄ = 0`) it would be `(1 − β)π/κ`. -/
theorem yun_vertical [Nonempty Ω] {κ β πbar πss g : ℝ}
    (h : (fun (_ : Ω) => πss) = (1 - β) • (fun _ => πbar) + κ • (fun _ => g) +
      β • 𝔼.E 0 (fun _ => πss)) :
    κ * g = (1 - β) * (πss - πbar) := by
  obtain ⟨o⟩ := ‹Nonempty Ω›
  have := congrFun h o
  rw [𝔼.const] at this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-- Woodford (2003), eq. (3.5), p. 215: the price index with indexation,
`P_t^{1−θ} = (1 − α)p*_t^{1−θ} + α(P_{t−1}(P_{t−1}/P_{t−2})^γ)^{1−θ}`, in logs has derivative
`(1 − α) log p*' + α(log P_{t−1}' + γ π_{t−1}')` at a common price: the log-linearised (3.5). -/
theorem hasDerivAt_eq_3_5 {θ α γ : ℝ} (hθ : θ ≠ 1) {a b c : ℝ → ℝ} {a' b' c' : ℝ}
    (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0) (hc : HasDerivAt c c' 0)
    (h0 : a 0 = b 0 + γ * c 0) :
    HasDerivAt (fun s => (1 - θ)⁻¹ * Real.log ((1 - α) * Real.exp ((1 - θ) * a s) +
      α * Real.exp ((1 - θ) * (b s + γ * c s)))) ((1 - α) * a' + α * (b' + γ * c')) 0 :=
  TwoSector.hasDerivAt_logCES2 hθ ha (HasDerivAt.add hb (hc.const_mul γ)) h0

/-- Woodford (2003), (3.4)–(3.5), p. 215: the linearised law of motion
`log P_{t+1} = α(log P_t + γπ_t) + (1 − α) log p*_{t+1}` is the Calvo law
`α ψ_{t+1} = (1 − α) Q_{t+1}` for quasi-differenced inflation `ψ_{t+1} = π_{t+1} − γπ_t` and the
relative reset price `Q_{t+1} = log p*_{t+1} − log P_{t+1}`. -/
theorem indexed_law {α γ x0 x1 π0 π1 ps : ℝ} (hlaw : x1 = α * (x0 + γ * π0) + (1 - α) * ps)
    (hπ : π1 = x1 - x0) : α * (π1 - γ * π0) = (1 - α) * (ps - x1) := by
  rw [hπ, hlaw]; ring

/-- Woodford (2003), (3.4), p. 214: a price reset at `t + 1` and indexed by (3.4) thereafter is
`log p* + γ(log P_{t+k} − log P_t)` at `t + 1 + k`; relative to the index it equals
`(log p* − log P_{t+1}) − ∑_{τ<k} (π_{t+τ+2} − γ π_{t+τ+1})`, the relative price `resetRel` of
the Calvo block with `ψ` the quasi-differenced inflation. -/
theorem indexed_relPrice {γ ps : ℝ} {x π : ℕ → ℝ} (hx : ∀ j, x (j + 1) = x j + π (j + 1))
    (t k : ℕ) :
    ps + γ * (x (t + k) - x t) - x (t + 1 + k) =
      (ps - x (t + 1)) - ∑ τ ∈ Finset.range k, (π (t + τ + 2) - γ * π (t + τ + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, show t + (k + 1) = t + k + 1 by omega,
      show t + 1 + (k + 1) = t + 1 + k + 1 by omega, hx (t + k), hx (t + 1 + k),
      show t + 1 + k + 1 = t + k + 2 by omega, show t + k + 1 = t + 1 + k by omega]
    linear_combination ih

/-- Woodford (2003), eq. (3.6), p. 215: `π_t − γπ_{t−1} = κ(Ŷ_t − Ŷ_tⁿ) + β E_t(π_{t+1} − γπ_t)`. -/
def IndexedNKPC (κ β γ : ℝ) (π : ℕ → Ω → ℝ) (pim1 : Ω → ℝ) (gap : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t - γ • prev pim1 π t = κ • gap t + β • 𝔼.E t (π (t + 1) - γ • π t)

/-- Woodford (2003), (3.6), p. 215 ("log-linearization of the first-order condition and of the
law of motion (3.5) ... yields"): the Calvo block (`TwoSector.relative_law_iff_nkpc`) with the
quasi-differenced inflation `ψ_t = π_t − γπ_{t−1}` — whose cumulated values give the relative
price of an indexed firm (`indexed_relPrice`) and which obeys `α ψ = (1 − α) Q`
(`indexed_law`) — gives `ψ_t = ξ m_t + β E_t ψ_{t+1}`, i.e. (3.6) with `κ(Ŷ − Ŷⁿ) = ξ m`. -/
theorem eq_3_6_from_foc {α β ω θ γ Mψ Mm : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hA : 0 < 1 + ω * θ) {Q π m : ℕ → Ω → ℝ} {pim1 : Ω → ℝ}
    (hψ : ∀ t o, |(π t - γ • prev pim1 π t) o| ≤ Mψ)
    (hψa : 𝔼.Adapted fun t => π t - γ • prev pim1 π t) (hm : ∀ t o, |m t o| ≤ Mm)
    (hma : 𝔼.Adapted m) (hQ : 𝔼.Adapted Q)
    (hfoc : ∀ t, TwoSector.LinFOC 𝔼 (α * β) (1 + ω * θ) Q
      (fun t => π t - γ • prev pim1 π t) m t)
    (hlaw : ∀ t, α • (π t - γ • prev pim1 π t) = (1 - α) • Q t) (t : ℕ) :
    π t - γ • prev pim1 π t =
      calvoXi α β (ω * θ) • m t + β • 𝔼.E t (π (t + 1) - γ • π t) := by
  have hq0 : 0 ≤ α * β := by positivity
  have hq1 : α * β < 1 := by nlinarith
  have hrel := fun t => (TwoSector.linFOC_iff 𝔼 hq0 hq1 hA hψ hm t (hQ t)).mp (hfoc t)
  exact ((TwoSector.relative_law_iff_nkpc 𝔼 hα0 hα1 hβ0 hβ1 hA hψ hψa hm hma).mp
    ⟨hrel, hlaw⟩).1 t

/-- Woodford (2003), p. 215: "it is still possible to solve (3.6) forward": for a bounded
quasi-differenced inflation and a bounded adapted gap,
`π_t = γπ_{t−1} + κ ∑_j βʲ E_t(Ŷ − Ŷⁿ)_{t+j}`. -/
theorem eq_3_6_forward {κ β γ Mg M : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {π gap : ℕ → Ω → ℝ}
    {pim1 : Ω → ℝ} (hg : ∀ t o, |gap t o| ≤ Mg) (hga : 𝔼.Adapted gap)
    (hψ : ∀ t o, |(π t - γ • prev pim1 π t) o| ≤ M) (h : IndexedNKPC 𝔼 κ β γ π pim1 gap)
    (t : ℕ) (o : Ω) :
    π t o = γ * prev pim1 π t o + κ * ∑' j, β ^ j * 𝔼.E t (gap (t + j)) o := by
  have := nkpc_forward 𝔼 (π := fun t => π t - γ • prev pim1 π t) hβ0 hβ1 hg hga hψ
    (fun t => h t) t o
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-- Woodford (2003), (3.6), p. 215: given the initial inflation `π_{−1}`, (3.6) has at most one
solution with bounded quasi-differenced inflation (so at most one bounded solution): the
quasi-difference is the unique bounded forward solution and `π_t = γπ_{t−1} + ψ_t` then pins down
`π` recursively. -/
theorem eq_3_6_unique {κ β γ M1 M2 : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {π1 π2 gap : ℕ → Ω → ℝ}
    {pim1 : Ω → ℝ} (h1 : IndexedNKPC 𝔼 κ β γ π1 pim1 gap) (h2 : IndexedNKPC 𝔼 κ β γ π2 pim1 gap)
    (hb1 : ∀ t o, |(π1 t - γ • prev pim1 π1 t) o| ≤ M1)
    (hb2 : ∀ t o, |(π2 t - γ • prev pim1 π2 t) o| ≤ M2) : π1 = π2 := by
  have hβ : |β| < 1 := by rw [abs_of_nonneg hβ0]; exact hβ1
  have hs : ∀ (π : ℕ → Ω → ℝ), IndexedNKPC 𝔼 κ β γ π pim1 gap → ∀ t,
      (fun t => π t - γ • prev pim1 π t) t =
        β • 𝔼.E t ((fun t => π t - γ • prev pim1 π t) (t + 1)) + κ • gap t := by
    intro π h t
    change π t - γ • prev pim1 π t =
      β • 𝔼.E t (π (t + 1) - γ • prev pim1 π (t + 1)) + κ • gap t
    rw [h t]
    exact add_comm _ _
  have hψ := 𝔼.forward_unique hβ (hs π1 h1) (hs π2 h2) ⟨M1, hb1⟩ ⟨M2, hb2⟩
  funext t
  induction t with
  | zero =>
    have := congrFun hψ 0
    simp only [prev] at this
    exact sub_left_inj.mp this
  | succ t ih =>
    have := congrFun hψ (t + 1)
    simp only [prev, ih] at this
    exact sub_left_inj.mp this

/-- Woodford (2003), pp. 216–217: for adapted inflation (and a known `π_{−1}`), (3.6) is the
hybrid Phillips curve `(1 + βγ)π_t = γπ_{t−1} + β E_t π_{t+1} + κ(Ŷ_t − Ŷ_tⁿ)` — the form of
Galí and Gertler (1999), with backward weight `γ/(1 + βγ)` and forward weight `β/(1 + βγ)`. -/
theorem eq_3_6_iff_hybrid {κ β γ : ℝ} {π gap : ℕ → Ω → ℝ} {pim1 : Ω → ℝ}
    (hπa : 𝔼.Adapted π) (t : ℕ) :
    (π t - γ • prev pim1 π t = κ • gap t + β • 𝔼.E t (π (t + 1) - γ • π t)) ↔
      (1 + β * γ) • π t = γ • prev pim1 π t + β • 𝔼.E t (π (t + 1)) + κ • gap t := by
  rw [map_sub, map_smul, hπa t]
  constructor <;> intro h <;> funext o <;> have := congrFun h o <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢ <;>
    linarith

/-- Woodford (2003), footnote 67, p. 216 (Fuhrer and Moore 1995): with `β = 1` and `γ = 1`, (3.6) is
`π_t = ½(π_{t−1} + E_t π_{t+1}) + (κ/2)(Ŷ_t − Ŷ_tⁿ)`. -/
theorem fuhrer_moore {κ : ℝ} {π gap : ℕ → Ω → ℝ} {pim1 : Ω → ℝ} (hπa : 𝔼.Adapted π)
    (t : ℕ) :
    (π t - (1 : ℝ) • prev pim1 π t =
        κ • gap t + (1 : ℝ) • 𝔼.E t (π (t + 1) - (1 : ℝ) • π t)) ↔
      π t = (1 / 2 : ℝ) • (prev pim1 π t + 𝔼.E t (π (t + 1))) + (κ / 2) • gap t := by
  rw [eq_3_6_iff_hybrid 𝔼 hπa t]
  constructor <;> intro h <;> funext o <;> have := congrFun h o <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢ <;> linarith

/-- Woodford (2003), pp. 216–217: the hybrid weights `γ/(1 + βγ)` and `β/(1 + βγ)` sum to one iff
`β = 1` or `γ = 1` (the "limiting case `β = 1`" in which the hybrid models coincide). -/
theorem hybrid_weights_sum_one_iff {β γ : ℝ} (h : 0 < 1 + β * γ) :
    γ / (1 + β * γ) + β / (1 + β * γ) = 1 ↔ (1 - β) * (1 - γ) = 0 := by
  rw [← add_div, div_eq_one_iff_eq h.ne']
  constructor <;> intro h' <;> linarith

/-- Woodford (2003), eq. (3.7), p. 217: with delay and indexation,
`π_{t+d} − γπ_{t+d−1} = κ E_t(Ŷ − Ŷⁿ)_{t+d} + β E_t(π_{t+d+1} − γπ_{t+d})`; a solution with
bounded quasi-differenced inflation (bounded gap) satisfies
`π_{t+d} = γπ_{t+d−1} + κ ∑_j βʲ E_t(Ŷ − Ŷⁿ)_{t+d+j}`, and `π_{t+d} − γπ_{t+d−1}` is known
at `t`. -/
theorem eq_3_7_forward {κ β γ Mg M : ℝ} {d : ℕ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {π gap : ℕ → Ω → ℝ} {pim1 : Ω → ℝ} (hg : ∀ t o, |gap t o| ≤ Mg)
    (hψ : ∀ t o, |(π t - γ • prev pim1 π t) o| ≤ M)
    (h : DelayedNKPC 𝔼 κ β d (fun t => π t - γ • prev pim1 π t) gap) (t : ℕ) (o : Ω) :
    π (t + d) o = γ * prev pim1 π (t + d) o + κ * ∑' j, β ^ j * 𝔼.E t (gap (t + d + j)) o ∧
      𝔼.E t (π (t + d) - γ • prev pim1 π (t + d)) = π (t + d) - γ • prev pim1 π (t + d) := by
  refine ⟨?_, delayed_predetermined 𝔼 h t⟩
  have := delayed_forward 𝔼 hβ0 hβ1 hg hψ h t o
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  linarith

/-! ### Indexation: the impulse-response system with `γ > 0` (Figures 3.14–3.16) -/

/-- Woodford (2003), (3.6), p. 215: quasi-differenced inflation of a lagged price-level response
`Q` (`Q_j = p̃_{j−2}`, so `Q_0 = p̃_{−2}`, `Q_1 = p̃_{−1}`):
`(p̃_k − p̃_{k−1}) − γ(p̃_{k−1} − p̃_{k−2})`. -/
def qdiff (γ : ℝ) (Q : ℕ → ℝ) (k : ℕ) : ℝ := (Q (k + 2) - Q (k + 1)) - γ * (Q (k + 1) - Q k)

/-- Woodford (2003), (3.6)–(3.7), pp. 215–217, Figures 3.14–3.16: the impulse-response system of
the indexed model with delay `d` for the nominal-GDP response `n`: no response before the shock
(`p̃_{−2} = p̃_{−1} = 0`), zero quasi-differenced inflation before date `d`, and
`ψ̃_k = κ(ñ_k − p̃_k) + β ψ̃_{k+1}` from `d` on. -/
def IndexIRF (κ β γ : ℝ) (d : ℕ) (n Q : ℕ → ℝ) : Prop :=
  Q 0 = 0 ∧ Q 1 = 0 ∧ (∀ k, k < d → qdiff γ Q k = 0) ∧
    ∀ k, d ≤ k → qdiff γ Q k = κ * (n k - Q (k + 2)) + β * qdiff γ Q (k + 1)

/-- Woodford (2003), (3.6), p. 215: the characteristic polynomial of the indexed system,
`C(z) = (z − 1)(z − γ)(1 − βz) + κz²` (for `Q_k = zᵏ`). -/
noncomputable def cubicC (β κ γ z : ℝ) : ℝ := (z - 1) * (z - γ) * (1 - β * z) + κ * z ^ 2

/-- Woodford (2003), (3.6), p. 215: `C(z) = −βz³ + c₂z² − c₁z + γ` with
`c₂ = 1 + β(1 + γ) + κ`, `c₁ = 1 + γ + βγ`. -/
theorem cubicC_expand (β κ γ z : ℝ) : cubicC β κ γ z =
    -β * z ^ 3 + (1 + β * (1 + γ) + κ) * z ^ 2 - (1 + γ + β * γ) * z + γ := by
  unfold cubicC; ring

/-- Woodford (2003), (3.6), p. 215: the indexed impulse-response equation at `k` is the
third-order recursion `−βQ_{k+3} + c₂Q_{k+2} − c₁Q_{k+1} + γQ_k = κ ñ_k`. -/
theorem qdiff_eq_iff (κ β γ : ℝ) (n Q : ℕ → ℝ) (k : ℕ) :
    qdiff γ Q k = κ * (n k - Q (k + 2)) + β * qdiff γ Q (k + 1) ↔
      -β * Q (k + 3) + (1 + β * (1 + γ) + κ) * Q (k + 2) - (1 + γ + β * γ) * Q (k + 1) +
        γ * Q k = κ * n k := by
  unfold qdiff
  rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), (3.6), Figure 3.14: for `0 < β < 1`, `κ > 0`, `0 ≤ γ ≤ 1` the characteristic
polynomial has a real root `μ > 1/β > 1` (intermediate value theorem: `C(1/β) = κ/β² > 0` and
`C(z) → −∞`). -/
theorem cubic_root_exists {β κ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hγ0 : 0 ≤ γ) :
    ∃ μ, 1 / β < μ ∧ cubicC β κ γ μ = 0 := by
  set c2 := 1 + β * (1 + γ) + κ with hc2
  set M := (c2 + γ + 1) / β with hM
  have hf1 : 0 < cubicC β κ γ (1 / β) := by
    unfold cubicC
    rw [show 1 - β * (1 / β) = 0 by field_simp; ring, mul_zero, zero_add]
    positivity
  have hβM : β * M = c2 + γ + 1 := by rw [hM]; field_simp
  have hM1 : 1 ≤ M := by
    rw [hM, le_div_iff₀ hβ0]
    have : 0 < κ + β * (1 + γ) := by positivity
    nlinarith
  have hfM : cubicC β κ γ M < 0 := by
    rw [cubicC_expand]
    have e : -β * M ^ 3 + c2 * M ^ 2 - (1 + γ + β * γ) * M + γ =
        -(γ + 1) * M ^ 2 - (1 + γ + β * γ) * M + γ := by
      rw [show -β * M ^ 3 = -(β * M) * M ^ 2 by ring, hβM]; ring
    rw [← hc2, e]
    have : 1 ≤ M ^ 2 := by nlinarith
    have : 0 < (1 + γ + β * γ) * M := by positivity
    nlinarith
  have hle : 1 / β ≤ M := by
    rw [hM, div_le_div_iff_of_pos_right hβ0]; nlinarith
  have hcont : ContinuousOn (cubicC β κ γ) (Set.Icc (1 / β) M) := by
    unfold cubicC; fun_prop
  obtain ⟨μ, hμ, hμ0⟩ := intermediate_value_Icc' hle hcont ⟨hfM.le, hf1.le⟩
  refine ⟨μ, lt_of_le_of_ne hμ.1 fun h => ?_, hμ0⟩
  rw [← h] at hμ0
  linarith

/-- Woodford (2003), (3.6), Figures 3.14–3.16 (**root location**): for `0 < β < 1`, `κ > 0`,
`0 ≤ γ ≤ 1` there are `μ > 1/β` and `a`, `b` with `C(z) = −β(z − μ)(z² − az + b)` (identically,
also as a recursion on sequences), and `z² − az + b` is Schur–Cohn stable. Hence the
characteristic polynomial has exactly one root outside the unit circle, `μ`, and two (real or
complex) roots strictly inside (`cubic_roots_location`). -/
theorem index_factor {β κ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) :
    ∃ μ a b : ℝ, 1 / β < μ ∧ 1 < μ ∧ cubicC β κ γ μ = 0 ∧ SchurStable a b ∧
      (∀ z : ℂ, (z - 1) * (z - γ) * (1 - β * z) + κ * z ^ 2 =
        -β * (z - μ) * (z ^ 2 - a * z + b)) ∧
      ∀ (Q : ℕ → ℝ) (k : ℕ), -β * Q (k + 3) + (1 + β * (1 + γ) + κ) * Q (k + 2) -
        (1 + γ + β * γ) * Q (k + 1) + γ * Q k =
          -β * ((Q (k + 3) - a * Q (k + 2) + b * Q (k + 1)) -
            μ * (Q (k + 2) - a * Q (k + 1) + b * Q k)) := by
  obtain ⟨μ, hμβ, hμ⟩ := cubic_root_exists hβ0 hβ1 hκ hγ0
  have hβμ : 1 < β * μ := by rwa [div_lt_iff₀ hβ0, mul_comm] at hμβ
  have hμ1 : 1 < μ := by nlinarith
  have hμ0 : μ ≠ 0 := by linarith
  set c2 := 1 + β * (1 + γ) + κ with hc2
  set c1 := 1 + γ + β * γ with hc1
  set a := c2 / β - μ with ha
  set b := γ / (β * μ) with hb
  have hE : -β * μ ^ 3 + c2 * μ ^ 2 - c1 * μ + γ = 0 := by rw [← cubicC_expand]; exact hμ
  have ha1 : β * a = c2 - β * μ := by rw [ha]; field_simp
  have hb2 : β * b * μ = γ := by rw [hb]; field_simp
  have hc1' : β * (b + a * μ) = c1 := by
    have : μ * (β * (b + a * μ)) = μ * c1 := by
      linear_combination hb2 + μ ^ 2 * ha1 + hE
    exact mul_left_cancel₀ hμ0 this
  have ha2 : β * (a + μ) = c2 := by linear_combination ha1
  -- the polynomial identity in real form
  have hpoly : ∀ z : ℝ, cubicC β κ γ z = -β * (z - μ) * (z ^ 2 - a * z + b) := by
    intro z
    rw [cubicC_expand]
    linear_combination (-z ^ 2) * ha2 + z * hc1' - hb2
  -- Schur–Cohn for the quadratic factor
  have hq1 : 0 < 1 - a + b := by
    have h := hpoly 1
    have hC1 : cubicC β κ γ 1 = κ := by unfold cubicC; ring
    rw [hC1] at h
    have hpos : 0 < β * (μ - 1) := by nlinarith
    nlinarith
  have hqm1 : 0 < 1 + a + b := by
    have h := hpoly (-1)
    have hCm1 : cubicC β κ γ (-1) = 2 * (1 + γ) * (1 + β) + κ := by unfold cubicC; ring
    rw [hCm1] at h
    have hpos : 0 < β * (1 + μ) := by nlinarith
    have : 0 < 2 * (1 + γ) * (1 + β) + κ := by positivity
    nlinarith
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hb1 : b < 1 := by
    rw [hb, div_lt_one (by positivity)]; linarith
  have hS : SchurStable a b := ⟨by rw [abs_lt]; constructor <;> linarith, by
    rw [abs_lt]; constructor <;> linarith⟩
  refine ⟨μ, a, b, hμβ, hμ1, hμ, hS, fun z => ?_, fun Q k => ?_⟩
  · have ha2' : (β : ℂ) * ((a : ℂ) + μ) = c2 := by exact_mod_cast ha2
    have hc1'' : (β : ℂ) * ((b : ℂ) + a * μ) = c1 := by exact_mod_cast hc1'
    have hb2' : (β : ℂ) * b * μ = γ := by exact_mod_cast hb2
    rw [hc2] at ha2'
    rw [hc1] at hc1''
    push_cast at ha2' hc1''
    linear_combination (-z ^ 2) * ha2' + z * hc1'' - hb2'
  · linear_combination -(Q (k + 2) * ha2) + Q (k + 1) * hc1' - Q k * hb2

/-- Woodford (2003), (3.6), Figures 3.14–3.16: every complex root of the characteristic
polynomial other than `μ > 1` lies strictly inside the unit circle. -/
theorem cubic_roots_location {β κ γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ μ : ℝ, 1 < μ ∧ cubicC β κ γ μ = 0 ∧
      ∀ z : ℂ, (z - 1) * (z - γ) * (1 - β * z) + κ * z ^ 2 = 0 → z = μ ∨ ‖z‖ < 1 := by
  obtain ⟨μ, a, b, -, hμ1, hμ, hS, hpoly, -⟩ := index_factor hβ0 hβ1 hκ hγ0 hγ1
  refine ⟨μ, hμ1, hμ, fun z hz => ?_⟩
  rw [hpoly] at hz
  have hβ' : (-β : ℂ) ≠ 0 := by
    rw [neg_ne_zero]; exact_mod_cast hβ0.ne'
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hβ'
    · exact Or.inl (sub_eq_zero.mp h')
  · right
    obtain ⟨hr1, hr2⟩ := (schurStable_iff_roots a b).mp hS
    have hfac : z ^ 2 - a * z + b = (z - root₁ a b) * (z - root₂ a b) := by
      have hs := root_sum a b
      have hp := root_prod a b
      linear_combination z * hs - hp
    rw [hfac] at h
    rcases mul_eq_zero.mp h with h' | h'
    · rw [sub_eq_zero.mp h']; exact hr1
    · rw [sub_eq_zero.mp h']; exact hr2

/-- Woodford (2003), Figures 3.14–3.16: the indexed impulse-response system has at most one
bounded solution (`0 < β < 1`, `κ > 0`, `0 ≤ γ ≤ 1`, any delay `d`): with
`D_k = Δ_{k+2} − aΔ_{k+1} + bΔ_k` for the difference `Δ` of two solutions, the unstable factor
gives `D_{k+1} = μ D_k`, so boundedness forces `D = 0`, and then the stable recursion from the
zero initial values forces `Δ = 0`. -/
theorem indexIRF_unique {κ β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) {d : ℕ} {n Q Q' : ℕ → ℝ} (h : IndexIRF κ β γ d n Q)
    (h' : IndexIRF κ β γ d n Q') (hb : ∃ M, ∀ k, |Q k| ≤ M) (hb' : ∃ M, ∀ k, |Q' k| ≤ M) :
    Q = Q' := by
  obtain ⟨μ, a, b, -, hμ1, -, -, -, hfac⟩ := index_factor hβ0 hβ1 hκ hγ0 hγ1
  obtain ⟨M, hM⟩ := hb
  obtain ⟨M', hM'⟩ := hb'
  obtain ⟨h0, h1, hlo, hhi⟩ := h
  obtain ⟨h0', h1', hlo', hhi'⟩ := h'
  set Δ : ℕ → ℝ := fun k => Q k - Q' k with hΔ
  -- zero up to date `d + 1`
  have hstart : ∀ j, j ≤ d → Δ j = 0 ∧ Δ (j + 1) = 0 := by
    intro j hj
    induction j with
    | zero => simp [hΔ, h0, h0', h1, h1']
    | succ j ih =>
      obtain ⟨e0, e1⟩ := ih (by omega)
      refine ⟨e1, ?_⟩
      have q1 := hlo j (by omega)
      have q2 := hlo' j (by omega)
      unfold qdiff at q1 q2
      simp only [hΔ] at e0 e1 ⊢
      rw [show j + 1 + 1 = j + 2 from rfl]
      linear_combination q1 - q2 + (1 + γ) * e1 - γ * e0
  -- the homogeneous third-order recursion from `d` on, and the unstable factor
  set D : ℕ → ℝ := fun k => Δ (k + 2) - a * Δ (k + 1) + b * Δ k with hD
  have hDrec : ∀ k, d ≤ k → D (k + 1) = μ * D k := by
    intro k hk
    have e := (qdiff_eq_iff κ β γ n Q k).mp (hhi k hk)
    have e' := (qdiff_eq_iff κ β γ n Q' k).mp (hhi' k hk)
    have hf := hfac Δ k
    simp only [hΔ] at hf
    have : -β * (D (k + 1) - μ * D k) = 0 := by
      simp only [hD, hΔ]
      rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl]
      linear_combination e - e' - hf
    have hβ' : -β ≠ 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hβ'
    linarith
  have hDb : ∀ k, |D k| ≤ (1 + |a| + |b|) * (M + M') := by
    intro k
    have hΔb : ∀ j, |Δ j| ≤ M + M' := fun j => (abs_sub _ _).trans (add_le_add (hM j) (hM' j))
    simp only [hD]
    calc |Δ (k + 2) - a * Δ (k + 1) + b * Δ k|
        ≤ |Δ (k + 2)| + |a| * |Δ (k + 1)| + |b| * |Δ k| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans ?_) ?_)
          · rw [abs_mul]
          · rw [abs_mul]
      _ ≤ (M + M') + |a| * (M + M') + |b| * (M + M') := by
          gcongr
          · exact hΔb _
          · exact hΔb _
          · exact hΔb _
      _ = (1 + |a| + |b|) * (M + M') := by ring
  have hDz : ∀ k, d ≤ k → D k = 0 := by
    intro k hk
    have hpow : ∀ m : ℕ, D (k + m) = μ ^ m * D k := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [← add_assoc, hDrec _ (by omega), ih, pow_succ]; ring
    set B := (1 + |a| + |b|) * (M + M')
    have hle : ∀ m : ℕ, |D k| ≤ (μ⁻¹) ^ m * B := by
      intro m
      have := hDb (k + m)
      rw [hpow m, abs_mul, abs_of_pos (pow_pos (by linarith) m)] at this
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos (by linarith) m), mul_comm]
      exact this
    have hlim : Tendsto (fun m : ℕ => (μ⁻¹) ^ m * B) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (by linarith))
        (inv_lt_one_of_one_lt₀ hμ1)).mul_const B
    exact abs_nonpos_iff.mp (ge_of_tendsto' hlim hle)
  -- the stable recursion propagates the zero initial values
  have hall : ∀ j, Δ (d + j) = 0 ∧ Δ (d + j + 1) = 0 := by
    intro j
    induction j with
    | zero => simpa using hstart d le_rfl
    | succ j ih =>
      refine ⟨by rw [← add_assoc]; exact ih.2, ?_⟩
      have := hDz (d + j) (by omega)
      simp only [hD] at this
      rw [show d + (j + 1) + 1 = d + j + 2 by omega]
      rw [ih.1, ih.2] at this
      linarith
  funext k
  have : Δ k = 0 := by
    by_cases hk : k ≤ d
    · exact (hstart k hk).1
    · have := (hall (k - d)).1
      rwa [show d + (k - d) = k by omega] at this
  simpa [hΔ, sub_eq_zero] using this

/-- Woodford (2003), Figures 3.14–3.16: the convolution `∑_{j ≤ k} h_j D_{k−j}`. -/
noncomputable def conv (h D : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1), h j * D (k - j)

/-- Woodford (2003), Figures 3.14–3.16: if `h` is the impulse response of
`x_k = a x_{k−1} − b x_{k−2}` (`h₀ = 1`, `h₁ = a`), the convolution solves
`x_{k+2} = a x_{k+1} − b x_k + D_{k+2}`. -/
theorem conv_rec {a b : ℝ} {h D : ℕ → ℝ} (hh : ∀ j, h (j + 2) = a * h (j + 1) - b * h j)
    (h0 : h 0 = 1) (h1 : h 1 = a) (k : ℕ) :
    conv h D (k + 2) = a * conv h D (k + 1) - b * conv h D k + D (k + 2) := by
  have e1 : conv h D (k + 2) = ∑ j ∈ Finset.range (k + 1), h (j + 2) * D (k - j) +
      h 1 * D (k + 1) + h 0 * D (k + 2) := by
    unfold conv
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    congr 2
    · exact Finset.sum_congr rfl fun j _ => by rw [show k + 2 - (j + 1 + 1) = k - j by omega]
  have e2 : conv h D (k + 1) = ∑ j ∈ Finset.range (k + 1), h (j + 1) * D (k - j) +
      h 0 * D (k + 1) := by
    unfold conv
    rw [Finset.sum_range_succ']
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [show k + 1 - (j + 1) = k - j by omega]
  have e3 : ∑ j ∈ Finset.range (k + 1), h (j + 2) * D (k - j) =
      a * ∑ j ∈ Finset.range (k + 1), h (j + 1) * D (k - j) - b * conv h D k := by
    unfold conv
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hh j]; ring
  rw [e1, e3, e2, h0, h1]
  ring

/-- Woodford (2003), Figure 3.14: existence of a bounded solution of the indexed system without
delay, for any bounded nominal-GDP response: `D_k = κ/(βμ) ∑ μ^{−j} ñ_{k+j}` (the unstable root
solved forward) and `Q_{k+2} = ∑_{j ≤ k} h_j D_{k−j}` (the stable factor solved backward). -/
theorem indexIRF_exists {κ β γ Mn : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) {n : ℕ → ℝ} (hn : ∀ k, |n k| ≤ Mn) :
    ∃ Q : ℕ → ℝ, IndexIRF κ β γ 0 n Q ∧ ∃ M, ∀ k, |Q k| ≤ M := by
  obtain ⟨μ, a, b, -, hμ1, -, hS, -, hfac⟩ := index_factor hβ0 hβ1 hκ hγ0 hγ1
  have hμ0 : 0 < μ := by linarith
  have hi0 : 0 ≤ μ⁻¹ := inv_nonneg.mpr hμ0.le
  have hi1 : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ1
  set Dq : ℕ → ℝ := fun k => κ / (β * μ) * fwdSum μ⁻¹ n k with hDq
  set h : ℕ → ℝ := chSeq a b with hh
  set Q : ℕ → ℝ := fun j => if j < 2 then 0 else conv h Dq (j - 2) with hQ
  have hhrec : ∀ j, h (j + 2) = a * h (j + 1) - b * h j := fun j => rfl
  have hQ2 : ∀ k, Q (k + 2) = conv h Dq k := fun k => by simp [hQ]
  have hrec : ∀ k, Q (k + 2) = a * Q (k + 1) - b * Q k + Dq k := by
    intro k
    rcases k with _ | _ | k
    · simp [hQ, conv, hh, chSeq]
    · simp [hQ, conv, hh, chSeq, Finset.sum_range_succ]; ring
    · rw [hQ2, hQ2, show k + 1 + 1 = (k + 1) + 1 from rfl, hQ2,
        conv_rec hhrec rfl rfl k]
  have hDrec : ∀ k, -β * (Dq (k + 1) - μ * Dq k) = κ * n k := by
    intro k
    simp only [hDq]
    rw [fwdSum_rec hi0 hi1 hn k]
    field_simp
    ring
  refine ⟨Q, ⟨by simp [hQ], by simp [hQ], fun k hk => absurd hk (Nat.not_lt_zero k),
    fun k _ => ?_⟩, ?_⟩
  · rw [qdiff_eq_iff, hfac Q k]
    have r1 := hrec k
    have r2 := hrec (k + 1)
    rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl] at r2
    rw [← hDrec k]
    linear_combination (-β) * r2 + (β * μ) * r1
  · -- boundedness via `|h_j| ≤ (j + 1) ρʲ`
    obtain ⟨hr1, hr2⟩ := (schurStable_iff_roots a b).mp hS
    set ρ := max ‖root₁ a b‖ ‖root₂ a b‖ with hρ
    have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
    have hρ1 : ρ < 1 := max_lt hr1 hr2
    have hsum : Summable (fun j : ℕ => ((j : ℝ) + 1) * ρ ^ j) := by
      have hρn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ1
      have := (summable_pow_mul_geometric_of_norm_lt_one 1 hρn).add
        (summable_geometric_of_lt_one hρ0 hρ1)
      exact this.congr fun j => by simp only [pow_one]; ring
    set W := κ / (β * μ) * (Mn / (1 - μ⁻¹)) with hW
    have hW0 : 0 ≤ W := by
      have : 0 ≤ Mn := (abs_nonneg _).trans (hn 0)
      have : 0 < 1 - μ⁻¹ := by linarith
      positivity
    have hDb : ∀ k, |Dq k| ≤ W := fun k => by
      simp only [hDq, abs_mul, abs_of_pos (by positivity : 0 < κ / (β * μ))]
      exact mul_le_mul_of_nonneg_left (fwdSum_abs_le hi0 hi1 hn k) (by positivity)
    refine ⟨W * ∑' j : ℕ, ((j : ℝ) + 1) * ρ ^ j, fun j => ?_⟩
    by_cases hj : j < 2
    · simp only [hQ, hj, ↓reduceIte, abs_zero]
      exact mul_nonneg hW0 (tsum_nonneg fun j => by positivity)
    · simp only [hQ, hj, ↓reduceIte]
      unfold conv
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range (j - 2 + 1), |h i * Dq (j - 2 - i)|
          ≤ ∑ i ∈ Finset.range (j - 2 + 1), W * (((i : ℝ) + 1) * ρ ^ i) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [abs_mul, mul_comm W]
            exact mul_le_mul (abs_chSeq_le a b i) (hDb _) (abs_nonneg _) (by positivity)
        _ = W * ∑ i ∈ Finset.range (j - 2 + 1), ((i : ℝ) + 1) * ρ ^ i := by
            rw [Finset.mul_sum]
        _ ≤ W * ∑' i : ℕ, ((i : ℝ) + 1) * ρ ^ i :=
            mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ fun i _ => by positivity) hW0

/-- Woodford (2003), Figures 3.15–3.16 (shift theorem with indexation): if `Q` solves the indexed
system without delay for the input `m`, then `Q` delayed by `d` periods solves the system with
delay `d` for the input `m` delayed by `d` periods. -/
theorem indexIRF_shift {κ β γ : ℝ} {d : ℕ} {m Q : ℕ → ℝ} (h : IndexIRF κ β γ 0 m Q) :
    IndexIRF κ β γ d (shiftSeq d m) (shiftSeq d Q) := by
  obtain ⟨h0, h1, -, h2⟩ := h
  have hlow : ∀ j, j ≤ d + 1 → shiftSeq d Q j = 0 := by
    intro j hj
    unfold shiftSeq
    by_cases hjd : j < d
    · simp [hjd]
    · simp only [hjd, ↓reduceIte]
      rcases (show j - d = 0 ∨ j - d = 1 by omega) with e | e <;> rw [e]
      · exact h0
      · exact h1
  have hhigh : ∀ j, shiftSeq d Q (d + j) = Q j := fun j => by
    simp only [shiftSeq, show ¬ (d + j < d) by omega, ↓reduceIte]
    congr 1; omega
  refine ⟨hlow 0 (by omega), hlow 1 (by omega), fun k hk => ?_, fun k hk => ?_⟩
  · unfold qdiff
    rw [hlow k (by omega), hlow (k + 1) (by omega), hlow (k + 2) (by omega)]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, k = d + j := ⟨k - d, by omega⟩
    have hs : shiftSeq d m (d + j) = m j := by
      simp only [shiftSeq, show ¬ (d + j < d) by omega, ↓reduceIte]
      congr 1; omega
    have e := h2 j (Nat.zero_le j)
    unfold qdiff at e ⊢
    have H : ∀ i, shiftSeq d Q (d + j + i) = Q (j + i) := fun i => by
      rw [show d + j + i = d + (j + i) by omega]; exact hhigh _
    rw [show d + j + 1 + 2 = d + j + 3 from rfl, show d + j + 1 + 1 = d + j + 2 from rfl,
      H 3, H 2, H 1, hhigh j, hs]
    rw [show j + 1 + 2 = j + 3 from rfl, show j + 1 + 1 = j + 2 from rfl] at e
    exact e

/-- Woodford (2003), **Figures 3.14–3.15**, pp. 215–218: with indexation `0 ≤ γ ≤ 1`, a bounded
response exists and is unique for every delay `d`; with nominal GDP delayed `s = d` periods it is
exactly the `s = d = 0` response (Figure 3.14) shifted right by `d` periods — Figure 3.15
(`γ = 1`, `s = d = 2`) is Figure 3.14 shifted by two quarters. -/
theorem fig_3_15 {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (d : ℕ) :
    ∃ Q0 : ℕ → ℝ, IndexIRF κ β γ 0 (nomIRF ρ 0) Q0 ∧ (∃ M, ∀ k, |Q0 k| ≤ M) ∧
      IndexIRF κ β γ d (nomIRF ρ d) (shiftSeq d Q0) ∧
      ∀ Qd : ℕ → ℝ, IndexIRF κ β γ d (nomIRF ρ d) Qd → (∃ M, ∀ k, |Qd k| ≤ M) →
        Qd = shiftSeq d Q0 ∧ ∀ k, Qd (k + 2) = shiftSeq d (fun j => Q0 (j + 2)) k := by
  have hn : ∀ k, |nomIRF ρ 0 k| ≤ 1 := fun k => by
    have := (nomIRF_bounds hρ0 hρ1 0).1 k
    rw [abs_le]; constructor <;> linarith
  obtain ⟨Q0, hQ0, M0, hM0⟩ := indexIRF_exists hβ0 hβ1 hκ hγ0 hγ1 hn
  have hsh := indexIRF_shift (d := d) hQ0
  rw [← nomIRF_shift] at hsh
  have hbsh : ∃ M, ∀ k, |shiftSeq d Q0 k| ≤ M := ⟨|M0|, fun k => by
    unfold shiftSeq
    split_ifs
    · simp
    · exact (hM0 _).trans (le_abs_self _)⟩
  refine ⟨Q0, hQ0, ⟨M0, hM0⟩, hsh, fun Qd hQd hbd => ?_⟩
  have heq := indexIRF_unique hβ0 hβ1 hκ hγ0 hγ1 hQd hsh hbd hbsh
  refine ⟨heq, fun k => ?_⟩
  rw [heq]
  unfold shiftSeq
  by_cases hk : k < d
  · simp only [hk, ↓reduceIte]
    by_cases hk2 : k + 2 < d
    · simp [hk2]
    · simp only [hk2, ↓reduceIte]
      rcases (show k + 2 - d = 0 ∨ k + 2 - d = 1 by omega) with e | e <;> rw [e]
      · exact hQ0.1
      · exact hQ0.2.1
  · simp only [hk, show ¬ (k + 2 < d) by omega, ↓reduceIte]
    congr 1; omega

/-- Woodford (2003), p. 217 ("the backward-looking indexation model retains one unfortunate
feature ... if a monetary disturbance increases nominal GDP only with a lag ... output should
initially contract"): **true** for every `0 ≤ γ ≤ 1`. Without delay (`d = 0`), if nominal GDP
does not move on impact (`ñ_0 = 0`) but rises later (`ñ ≥ 0`, `ñ_K > 0`), the bounded response
has inflation `p̃_0 > 0` and output `ñ_0 − p̃_0 < 0` on impact: the unstable-root combination
`D_0 = p̃_0` equals `κ/(βμ) ∑ μ^{−j} ñ_j > 0`. -/
theorem p217_contraction_general {κ β γ M : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {n Q : ℕ → ℝ} (hn : ∀ k, |n k| ≤ M) (hnn : ∀ k, 0 ≤ n k)
    (hn0 : n 0 = 0) {K : ℕ} (hK : 0 < n K) (hQ : IndexIRF κ β γ 0 n Q)
    (hb : ∃ M, ∀ k, |Q k| ≤ M) : 0 < Q 2 - Q 1 ∧ n 0 - Q 2 < 0 := by
  obtain ⟨μ, a, b, -, hμ1, -, -, -, hfac⟩ := index_factor hβ0 hβ1 hκ hγ0 hγ1
  obtain ⟨MQ, hMQ⟩ := hb
  obtain ⟨h0, h1, -, h2⟩ := hQ
  have hμ0 : 0 < μ := by linarith
  set D : ℕ → ℝ := fun k => Q (k + 2) - a * Q (k + 1) + b * Q k with hD
  have hDrec : ∀ k, D k = κ / (β * μ) * n k + μ⁻¹ * D (k + 1) := by
    intro k
    have e := (qdiff_eq_iff κ β γ n Q k).mp (h2 k (Nat.zero_le k))
    rw [hfac Q k] at e
    have e' : β * μ * D k = κ * n k + β * D (k + 1) := by
      simp only [hD]
      rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl]
      linear_combination e
    have hβμ : β * μ ≠ 0 := by positivity
    rw [show D k = (β * μ * D k) / (β * μ) by field_simp, e']
    field_simp
  have hDb : ∀ k, |D k| ≤ (1 + |a| + |b|) * MQ := by
    intro k
    simp only [hD]
    calc |Q (k + 2) - a * Q (k + 1) + b * Q k|
        ≤ |Q (k + 2)| + |a| * |Q (k + 1)| + |b| * |Q k| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans ?_) ?_)
          · rw [abs_mul]
          · rw [abs_mul]
      _ ≤ MQ + |a| * MQ + |b| * MQ := by
          gcongr
          · exact hMQ _
          · exact hMQ _
          · exact hMQ _
      _ = (1 + |a| + |b|) * MQ := by ring
  have hfw := det_forward (inv_nonneg.mpr hμ0.le) (inv_lt_one_of_one_lt₀ hμ1) hDb hn hDrec 0
  have hpos : 0 < fwdSum μ⁻¹ n 0 :=
    fwdSum_pos (inv_pos.mpr hμ0) (inv_lt_one_of_one_lt₀ hμ1) hn hnn (Nat.zero_le K) hK
  have hD0 : D 0 = Q 2 := by simp [hD, h0, h1]
  have hQ2 : 0 < Q 2 := by
    rw [← hD0, hfw]
    exact mul_pos (by positivity) hpos
  rw [h1, hn0]
  constructor <;> linarith

/-- Woodford (2003), p. 217 and Figure 3.14: for the nominal-GDP process (3.3) with lag `s ≥ 1`,
indexation `0 ≤ γ ≤ 1` and no price delay, output contracts on impact. -/
theorem p217_contraction {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {s : ℕ} (hs : 1 ≤ s) {Q : ℕ → ℝ}
    (hQ : IndexIRF κ β γ 0 (nomIRF ρ s) Q) (hb : ∃ M, ∀ k, |Q k| ≤ M) :
    0 < Q 2 - Q 1 ∧ nomIRF ρ s 0 - Q 2 < 0 := by
  obtain ⟨hbd, hss⟩ := nomIRF_bounds hρ0 hρ1 s
  refine p217_contraction_general hκ hβ0 hβ1 hγ0 hγ1 (M := 1) (fun k => ?_)
    (fun k => (hbd k).1) ?_ (K := s) ?_ hQ hb
  · rw [abs_le]; constructor <;> linarith [(hbd k).1, (hbd k).2]
  · simp [nomIRF, show 0 < s by omega]
  · rw [hss]; linarith

/-- Woodford (2003), (3.7), p. 217 and Figures 3.15–3.16: under (3.7) — (3.2) for the
quasi-differenced inflation `ψ_{j+2} = (log P_{j+2} − log P_{j+1}) − γ(log P_{j+1} − log P_j)` —
with gap `log Y − log P` and an adapted price level, the revisions caused by the news at date
`s + 2` (`R = E_{s+2} − E_{s+1}`) of nominal GDP and of the price level (`Q_j = R log P_{s+j}`)
solve the indexed impulse-response system `IndexIRF`. -/
theorem revision_index_irf {κ β γ : ℝ} {d s : ℕ} {ψ gap n p : ℕ → Ω → ℝ}
    (h : DelayedNKPC 𝔼 κ β d ψ gap) (hinit : ∀ k < d, 𝔼.E 0 (ψ k) = ψ k)
    (hgap : ∀ t, gap t = n t - p t)
    (hψ : ∀ j, ψ (j + 2) = (p (j + 2) - p (j + 1)) - γ • (p (j + 1) - p j))
    (hp : 𝔼.Adapted p) (o : Ω) :
    IndexIRF κ β γ d (fun k => (𝔼.E (s + 2) (n (s + 2 + k)) - 𝔼.E (s + 1) (n (s + 2 + k))) o)
      (fun j => (𝔼.E (s + 2) (p (s + j)) - 𝔼.E (s + 1) (p (s + j))) o) := by
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ,
      A = fun j => (𝔼.E (s + 2) (p (s + j)) - 𝔼.E (s + 1) (p (s + j))) o := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ,
      G = fun k => (𝔼.E (s + 2) (n (s + 2 + k)) - 𝔼.E (s + 1) (n (s + 2 + k))) o := ⟨_, rfl⟩
  rw [← hA, ← hG]
  have hknown : ∀ j, j ≤ 1 → A j = 0 := by
    intro j hj
    rw [hA]
    simp only [Pi.sub_apply]
    have h1 : 𝔼.E (s + 1) (p (s + j)) = p (s + j) :=
      ForwardSolution.E_of_known 𝔼 (by omega) (hp (s + j))
    rw [h1, ForwardSolution.E_of_known 𝔼 (by omega : s + 1 ≤ s + 2) h1, sub_self]
  have hq : ∀ k, qdiff γ A k =
      (𝔼.E (s + 1 + 1) (ψ (s + 1 + 1 + k)) - 𝔼.E (s + 1) (ψ (s + 1 + 1 + k))) o := by
    intro k
    rw [show s + 1 + 1 + k = s + k + 2 by omega, hψ (s + k), hA]
    unfold qdiff
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show s + (k + 2) = s + k + 2 by omega, show s + (k + 1) = s + k + 1 by omega]
    ring
  refine ⟨hknown 0 (by omega), hknown 1 (by omega), fun k hk => ?_, fun k hk => ?_⟩
  · rw [hq k, revision_zero_before_delay 𝔼 h hinit (s + 1) k hk, sub_self, Pi.zero_apply]
  · have hr := congrFun (revision_recursion 𝔼 h (s + 1) k hk) o
    have hq1 := hq (k + 1)
    rw [hq k, hq1]
    rw [show s + 1 + 1 + (k + 1) = s + 1 + 1 + k + 1 by omega]
    have hA2 : A (k + 2) = (𝔼.E (s + 1 + 1) (p (s + 1 + 1 + k)) -
        𝔼.E (s + 1) (p (s + 1 + 1 + k))) o := by
      rw [hA]; beta_reduce; rw [show s + (k + 2) = s + 1 + 1 + k by omega]
    have hGk : G k = (𝔼.E (s + 1 + 1) (n (s + 1 + 1 + k)) -
        𝔼.E (s + 1) (n (s + 1 + 1 + k))) o := by
      rw [hG]
    rw [hA2, hGk]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hgap, map_sub] at hr ⊢
    linear_combination hr

/-! ### Figure 3.12 on an event tree with independent shocks (eq. (3.3)) -/

/-- Woodford (2003), (3.3), p. 209: what is observed at date `t` in a two-coin tree; both coins
(the first drives the monetary shock `ε`, the second the other demand disturbance `q`) are
revealed at date 1. -/
def shockObs (t : ℕ) (ω : Bool × Bool) : Bool × Bool := if 1 ≤ t then ω else (false, false)

/-- Woodford (2003), (3.3), p. 209: the event tree with two fair, independent coins revealed at
date 1 (nothing known at date 0). -/
noncomputable def shockTree : ExpectationsFiniteTree.FiniteTree (Bool × Bool) where
  prob := fun _ => 1 / 4
  prob_pos := fun _ => by norm_num
  prob_sum := by simp
  info := fun t => Setoid.ker (shockObs t)
  refines := by
    intro s t hst a b h
    rw [Setoid.ker_def] at h ⊢
    simp only [shockObs] at h ⊢
    by_cases hs : 1 ≤ s
    · simpa [hs, le_trans hs hst] using h
    · simp [hs]

/-- Woodford (2003), (3.3), p. 209: the expectation system of `shockTree`. -/
noncomputable def shockSystem : ExpectationSystem (Bool × Bool) :=
  shockTree.toExpectationSystem

/-- Woodford (2003), (3.3), p. 209: the two coins are independent under the tree's probability:
`E[f(ε-coin) g(q-coin)] = E[f(ε-coin)] E[g(q-coin)]`. -/
theorem shockTree_independent (f g : Bool → ℝ) :
    ∑ ω : Bool × Bool, shockTree.prob ω * (f ω.1 * g ω.2) =
      (∑ ω : Bool × Bool, shockTree.prob ω * f ω.1) *
        (∑ ω : Bool × Bool, shockTree.prob ω * g ω.2) := by
  simp only [shockTree, Fintype.sum_prod_type, Fintype.univ_bool, Finset.sum_insert,
    Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton]
  ring

/-- Woodford (2003), (3.3), p. 209: on `shockTree` the revision `E_1 x − E_0 x` differs across
two states exactly as `x` itself does (date-0 forecasts are common to all states, date-1
information is complete). -/
theorem shock_revision_diff (x : Bool × Bool → ℝ) (ω ω' : Bool × Bool) :
    (shockSystem.E 1 x - shockSystem.E 0 x) ω - (shockSystem.E 1 x - shockSystem.E 0 x) ω' =
      x ω - x ω' := by
  have h1 : ∀ ω, shockSystem.E 1 x ω = x ω := fun ω => by
    rw [shockSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    refine shockTree.condE_of_const_on_cell fun ω'' h => ?_
    have : shockObs 1 ω'' = shockObs 1 ω := h
    simp only [shockObs, le_refl, ↓reduceIte] at this
    rw [this]
  have h0 : ∀ ω, shockSystem.E 0 x ω = ∑ ω'', shockTree.prob ω'' * x ω'' := fun ω => by
    rw [shockSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
    refine shockTree.condE_of_trivial (fun a b => ?_) x ω
    change shockObs 0 a = shockObs 0 b
    simp [shockObs]
  simp only [Pi.sub_apply, h1, h0]
  ring

/-- Woodford (2003), (3.3), p. 209: the monetary shock `ε_1 = (1 − ρ) e(first coin)` (at date 1
only). -/
noncomputable def treeEps (ρ : ℝ) (e : Bool → ℝ) (t : ℕ) (ω : Bool × Bool) : ℝ :=
  if t = 1 then (1 - ρ) * e ω.1 else 0

/-- Woodford (2003), (3.3), p. 209: the other disturbance `q_t = q(t, second coin)`, `q_0 = 0`. -/
noncomputable def treeQ (qf : ℕ → Bool → ℝ) (t : ℕ) (ω : Bool × Bool) : ℝ :=
  if t = 0 then 0 else qf t ω.2

/-- Woodford (2003), eq. (3.3), p. 209: nominal-GDP growth
`Δ log Y_t = ρ Δ log Y_{t−1} + ε_{t−s} + q_t` on the tree (zero before date 1). -/
noncomputable def treeGrowth (ρ : ℝ) (s : ℕ) (e : Bool → ℝ) (qf : ℕ → Bool → ℝ) :
    ℕ → Bool × Bool → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => ρ * treeGrowth ρ s e qf t ω + treeEps ρ e (t + 1 - s) ω + treeQ qf (t + 1) ω

/-- Woodford (2003), (3.3), p. 209: log nominal GDP on the tree, `log Y_0 = 0`. -/
noncomputable def treeNom (ρ : ℝ) (s : ℕ) (e : Bool → ℝ) (qf : ℕ → Bool → ℝ) :
    ℕ → Bool × Bool → ℝ
  | 0 => fun _ => 0
  | t + 1 => fun ω => treeNom ρ s e qf t ω + treeGrowth ρ s e qf (t + 1) ω

/-- Woodford (2003), (3.3), p. 209 and (2.21), p. 191: in two states with the same `q`-coin,
log nominal GDP at date `1 + k` differs by `(e − e′) · nomIRF ρ s k`: the response to the
monetary shock, unaffected by the independent disturbance `q`. -/
theorem treeNom_diff {ρ : ℝ} {s : ℕ} {e : Bool → ℝ} {qf : ℕ → Bool → ℝ} {ω ω' : Bool × Bool}
    (h2 : ω.2 = ω'.2) (k : ℕ) :
    treeNom ρ s e qf (k + 1) ω - treeNom ρ s e qf (k + 1) ω' =
        (e ω.1 - e ω'.1) * nomIRF ρ s k ∧
      treeGrowth ρ s e qf (k + 1) ω - treeGrowth ρ s e qf (k + 1) ω' =
        (e ω.1 - e ω'.1) * (if k + 1 < s + 1 then 0 else (1 - ρ) * ρ ^ (k - s)) := by
  have hq : ∀ t, treeQ qf t ω = treeQ qf t ω' := fun t => by simp [treeQ, h2]
  induction k with
  | zero =>
    have hg : treeGrowth ρ s e qf 1 ω - treeGrowth ρ s e qf 1 ω' =
        (e ω.1 - e ω'.1) * (if 0 + 1 < s + 1 then 0 else (1 - ρ) * ρ ^ (0 - s)) := by
      simp only [treeGrowth, mul_zero, zero_add, hq 1, treeEps]
      rcases Nat.eq_zero_or_pos s with hs | hs
      · simp [hs]; ring
      · simp [show 1 - s ≠ 1 by omega, show 0 < s by omega]
    refine ⟨?_, hg⟩
    simp only [treeNom, zero_add]
    rw [hg]
    rcases Nat.eq_zero_or_pos s with hs | hs
    · simp [hs, nomIRF]
    · simp [nomIRF, hs]
  | succ k ih =>
    have hg : treeGrowth ρ s e qf (k + 1 + 1) ω - treeGrowth ρ s e qf (k + 1 + 1) ω' =
        (e ω.1 - e ω'.1) * (if k + 1 + 1 < s + 1 then 0 else (1 - ρ) * ρ ^ (k + 1 - s)) := by
      have hstep : treeGrowth ρ s e qf (k + 1 + 1) ω - treeGrowth ρ s e qf (k + 1 + 1) ω' =
          ρ * (treeGrowth ρ s e qf (k + 1) ω - treeGrowth ρ s e qf (k + 1) ω') +
            (treeEps ρ e (k + 1 + 1 - s) ω - treeEps ρ e (k + 1 + 1 - s) ω') := by
        simp only [treeGrowth, hq (k + 1 + 1)]; ring
      rw [hstep, ih.2]
      unfold treeEps
      by_cases h1 : k + 1 < s
      · simp [show k + 1 < s + 1 by omega, show k + 1 + 1 < s + 1 by omega,
          show k + 1 + 1 - s ≠ 1 by omega]
      · by_cases h2' : k + 1 = s
        · subst h2'
          simp
          ring
        · simp only [show ¬ (k + 1 < s + 1) by omega, show ¬ (k + 1 + 1 < s + 1) by omega,
            show k + 1 + 1 - s ≠ 1 by omega, ↓reduceIte, sub_self, add_zero]
          rw [show k + 1 - s = (k - s) + 1 by omega, pow_succ]
          ring
    refine ⟨?_, hg⟩
    have hn : treeNom ρ s e qf (k + 1 + 1) ω - treeNom ρ s e qf (k + 1 + 1) ω' =
        (treeNom ρ s e qf (k + 1) ω - treeNom ρ s e qf (k + 1) ω') +
          (treeGrowth ρ s e qf (k + 1 + 1) ω - treeGrowth ρ s e qf (k + 1 + 1) ω') := by
      simp only [treeNom]; ring
    rw [hn, ih.1, hg]
    have hgr := (nomIRF_growth ρ s).2 k
    have e1 : nomIRF ρ s (k + 1) = nomIRF ρ s k +
        (if k + 1 < s then 0 else (1 - ρ) * ρ ^ (k + 1 - s)) := by linarith
    rw [e1]
    by_cases hks : k + 1 < s
    · simp [hks, show k + 1 + 1 < s + 1 by omega]
    · simp only [hks, show ¬ (k + 1 + 1 < s + 1) by omega, ↓reduceIte]
      ring

/-- Woodford (2003), Figure 3.12, p. 211, for the stochastic model (**finite event tree with
independent disturbances**): on `shockTree`, with nominal GDP following (3.3) with lag `d`
(`ε` from the first coin, an arbitrary disturbance `q` from the independent second coin), any
bounded adapted price level satisfying (3.2) with delay `d` responds to the monetary shock
exactly as Figure 3.9 shifted right by `d` periods: in two states that differ only in the
monetary coin, the date-1 revisions of `log P_{1+k}` (equivalently `log P_{1+k}` itself) differ
by `(e − e′)` times the shifted Figure 3.9 price response. No assumption is made on the revision
path: it is derived from (3.3).

In an abstract `ExpectationSystem` this cannot be stated without assuming the nominal-GDP
revisions (`fig_3_12_stochastic`): the axioms describe linear expectation operators only, with no
joint distribution, so "`q` independent of `ε`" — which is what makes the date-`s+1` news about
`q` separable from the monetary news — has no meaning there. -/
theorem fig_3_12_tree {κ β ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) {d : ℕ} {e : Bool → ℝ} {qf : ℕ → Bool → ℝ} {π p : ℕ → Bool × Bool → ℝ}
    (h : DelayedNKPC shockSystem κ β d π (fun t => treeNom ρ d e qf t - p t))
    (hinit : ∀ k < d, shockSystem.E 0 (π k) = π k) (hπp : ∀ j, π (j + 1) = p (j + 1) - p j)
    (hp : shockSystem.Adapted p) (hpb : BoundedProc p) {ω ω' : Bool × Bool} (h2 : ω.2 = ω'.2)
    (k : ℕ) :
    (shockSystem.E 1 (p (1 + k)) - shockSystem.E 0 (p (1 + k))) ω -
        (shockSystem.E 1 (p (1 + k)) - shockSystem.E 0 (p (1 + k))) ω' =
      (e ω.1 - e ω'.1) * shiftSeq d (fun j => irfP β κ (nomIRF ρ 0) (j + 1)) k ∧
    p (1 + k) ω - p (1 + k) ω' =
      (e ω.1 - e ω'.1) * shiftSeq d (fun j => irfP β κ (nomIRF ρ 0) (j + 1)) k := by
  set n := treeNom ρ d e qf
  have hr1 := revision_irf shockSystem (s := 0) h hinit (fun t => rfl) hπp hp ω
  have hr2 := revision_irf shockSystem (s := 0) h hinit (fun t => rfl) hπp hp ω'
  obtain ⟨hz1, hlo1, hhi1⟩ := hr1
  obtain ⟨hz2, hlo2, hhi2⟩ := hr2
  beta_reduce at hz1 hz2 hlo1 hlo2 hhi1 hhi2
  set c := e ω.1 - e ω'.1
  set P : ℕ → ℝ := fun j => (shockSystem.E (0 + 1) (p (0 + j)) - shockSystem.E 0 (p (0 + j))) ω -
    (shockSystem.E (0 + 1) (p (0 + j)) - shockSystem.E 0 (p (0 + j))) ω' with hP
  have hin : ∀ k, (shockSystem.E (0 + 1) (n (0 + 1 + k)) - shockSystem.E 0 (n (0 + 1 + k))) ω -
      (shockSystem.E (0 + 1) (n (0 + 1 + k)) - shockSystem.E 0 (n (0 + 1 + k))) ω' =
      c * nomIRF ρ d k := by
    intro k
    rw [shock_revision_diff, show 0 + 1 + k = k + 1 by omega]
    exact (treeNom_diff h2 k).1
  have hdiff : DelayIRF κ β d (fun k => c * nomIRF ρ d k) P := by
    refine ⟨by simp only [hP]; rw [hz1, hz2, sub_self], fun k hk => ?_, fun k hk => ?_⟩
    · simp only [hP]; linarith [hlo1 k hk, hlo2 k hk]
    · have e1 := hhi1 k hk
      have e2 := hhi2 k hk
      have ei := hin k
      simp only [hP]
      linear_combination e1 - e2 + κ * ei
  obtain ⟨⟨P', hP', M', hM'⟩, hall⟩ := fig_3_12 hκ hβ0 hβ1 hρ0 hρ1 d
  have hsc := irf_smul (c := c) hP'
  obtain ⟨Mp, hMp⟩ := hpb
  have hPb : ∃ M, ∀ j, |P j| ≤ M := ⟨4 * Mp, fun j => by
    simp only [hP, Pi.sub_apply]
    have a1 := shockSystem.abs_E_le (fun o => hMp (0 + j) o) (0 + 1) ω
    have a2 := shockSystem.abs_E_le (fun o => hMp (0 + j) o) 0 ω
    have a3 := shockSystem.abs_E_le (fun o => hMp (0 + j) o) (0 + 1) ω'
    have a4 := shockSystem.abs_E_le (fun o => hMp (0 + j) o) 0 ω'
    rw [abs_le] at a1 a2 a3 a4 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]⟩
  have heq := irf_unique hκ hβ0.le hdiff hsc hPb ⟨|c| * |M'|, fun j => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hM' j).trans (le_abs_self _)) (abs_nonneg _)⟩
  have hk := congrFun heq (k + 1)
  simp only [hP] at hk
  rw [(hall P' hP' ⟨M', hM'⟩ k).1] at hk
  rw [show (0 : ℕ) + 1 = 1 from rfl, show 0 + (k + 1) = 1 + k by omega] at hk
  refine ⟨hk, ?_⟩
  rw [← shock_revision_diff (p (1 + k)) ω ω']
  exact hk

/-! ### Existence for every delay (Figures 3.11–3.16) -/

/-- Woodford (2003), (3.2), p. 208: the delayed system uses the input only from date `d` on. -/
theorem delayIRF_congr {κ β : ℝ} {d : ℕ} {n1 n2 P : ℕ → ℝ} (hn : ∀ k, d ≤ k → n1 k = n2 k)
    (h : DelayIRF κ β d n1 P) : DelayIRF κ β d n2 P :=
  ⟨h.1, h.2.1, fun k hk => by rw [← hn k hk]; exact h.2.2 k hk⟩

/-- Woodford (2003), (3.2), p. 208 and Figures 3.11–3.13: for every delay `d ≥ 0` and every bounded
nominal-GDP response (in particular `nomIRF ρ s` for every lag `s`), the delayed impulse-response
system has a bounded solution: the undelayed solution for the input from date `d` on, delayed by
`d` periods. -/
theorem irf_exists_delay {β κ Mn : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (d : ℕ)
    {n : ℕ → ℝ} (hn : ∀ k, |n k| ≤ Mn) :
    ∃ P : ℕ → ℝ, DelayIRF κ β d n P ∧ ∃ M, ∀ k, |P k| ≤ M := by
  obtain ⟨hP0, M0, hM0⟩ := irf_exists hβ0 hβ1 hκ (n := fun j => n (d + j)) (fun k => hn _)
  refine ⟨_, delayIRF_congr (fun k hk => ?_) (shift_solves (d := d) hP0), |M0|, fun k => ?_⟩
  · simp only [shiftSeq, show ¬ (k < d) by omega, ↓reduceIte]
    congr 1; omega
  · split_ifs
    · simp
    · exact (hM0 _).trans (le_abs_self _)

/-- Woodford (2003), (3.7), p. 217: the indexed system uses the input only from date `d` on. -/
theorem indexIRF_congr {κ β γ : ℝ} {d : ℕ} {n1 n2 Q : ℕ → ℝ} (hn : ∀ k, d ≤ k → n1 k = n2 k)
    (h : IndexIRF κ β γ d n1 Q) : IndexIRF κ β γ d n2 Q :=
  ⟨h.1, h.2.1, h.2.2.1, fun k hk => by rw [← hn k hk]; exact h.2.2.2 k hk⟩

/-- Woodford (2003), (3.6)–(3.7), Figures 3.14–3.16: for every delay `d ≥ 0`, indexation
`0 ≤ γ ≤ 1` and every bounded nominal-GDP response (in particular `nomIRF ρ s` for every lag
`s`), the indexed impulse-response system has a bounded solution (unique by
`indexIRF_unique`). -/
theorem indexIRF_exists_delay {κ β γ Mn : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (d : ℕ) {n : ℕ → ℝ} (hn : ∀ k, |n k| ≤ Mn) :
    ∃ Q : ℕ → ℝ, IndexIRF κ β γ d n Q ∧ ∃ M, ∀ k, |Q k| ≤ M := by
  obtain ⟨Q0, hQ0, M0, hM0⟩ := indexIRF_exists hβ0 hβ1 hκ hγ0 hγ1 (n := fun j => n (d + j))
    (fun k => hn _)
  refine ⟨_, indexIRF_congr (fun k hk => ?_) (indexIRF_shift (d := d) hQ0), |M0|, fun k => ?_⟩
  · simp only [shiftSeq, show ¬ (k < d) by omega, ↓reduceIte]
    congr 1; omega
  · unfold shiftSeq
    split_ifs
    · simp
    · exact (hM0 _).trans (le_abs_self _)

/-- Woodford (2003), Figures 3.11–3.16: for every delay `d` and lag `s` the bounded impulse
responses to the nominal-GDP process (3.3) exist and are unique, without indexation and with
indexation `0 ≤ γ ≤ 1`. -/
theorem irf_existsUnique_nom {κ β γ ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (d s : ℕ) :
    (∃! P : ℕ → ℝ, DelayIRF κ β d (nomIRF ρ s) P ∧ ∃ M, ∀ k, |P k| ≤ M) ∧
      ∃! Q : ℕ → ℝ, IndexIRF κ β γ d (nomIRF ρ s) Q ∧ ∃ M, ∀ k, |Q k| ≤ M := by
  have hn : ∀ k, |nomIRF ρ s k| ≤ 1 := fun k => by
    have := (nomIRF_bounds hρ0 hρ1 s).1 k
    rw [abs_le]; constructor <;> linarith
  obtain ⟨P, hP, hbP⟩ := irf_exists_delay hβ0 hβ1 hκ d hn
  obtain ⟨Q, hQ, hbQ⟩ := indexIRF_exists_delay hβ0 hβ1 hκ hγ0 hγ1 d hn
  exact ⟨⟨P, ⟨hP, hbP⟩, fun P' ⟨hP', hbP'⟩ => irf_unique hκ hβ0.le hP' hP hbP' hbP⟩,
    ⟨Q, ⟨hQ, hbQ⟩, fun Q' ⟨hQ', hbQ'⟩ => indexIRF_unique hβ0 hβ1 hκ hγ0 hγ1 hQ' hQ hbQ' hbQ⟩⟩

/-! ### An equilibrium on the event tree -/

/-- Woodford (2003), (2.16), p. 189: inflation of a price path starting from `p_{−1} = 0`. -/
def dinfl (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => p 0
  | j + 1 => p (j + 1) - p j

/-- Woodford (2003), (2.16), p. 189: `prev 0 p (k + 1) − prev 0 p k = π_k`. -/
theorem prev_zero_diff (p : ℕ → ℝ) (k : ℕ) : prev 0 p (k + 1) - prev 0 p k = dinfl p k := by
  cases k <;> simp [prev, dinfl]

/-- Woodford (2003), (3.2), p. 208: a deterministic price path `p` (with `p_{−1} = 0`) solves the
delayed Phillips curve: zero inflation before `d`, and `π_k = κ(ñ_k − p_k) + βπ_{k+1}` from `d`. -/
def InflSol (κ β : ℝ) (d : ℕ) (n p : ℕ → ℝ) : Prop :=
  (∀ k, k < d → dinfl p k = 0) ∧ ∀ k, d ≤ k → dinfl p k = κ * (n k - p k) + β * dinfl p (k + 1)

/-- Woodford (2003), (3.2): `InflSol` is `DelayIRF` for the lagged price path. -/
theorem inflSol_iff {κ β : ℝ} {d : ℕ} {n p : ℕ → ℝ} :
    InflSol κ β d n p ↔ DelayIRF κ β d n (prev 0 p) := by
  have h2 : ∀ k, prev 0 p (k + 2) - prev 0 p (k + 1) = dinfl p (k + 1) :=
    fun k => prev_zero_diff p (k + 1)
  have h1 : ∀ k, prev 0 p (k + 1) = p k := fun k => rfl
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨rfl, fun k hk => ?_, fun k hk => ?_⟩
    · have := prev_zero_diff p k; rw [ha k hk] at this; linarith
    · rw [prev_zero_diff, h2, h1]; exact hb k hk
  · rintro ⟨-, ha, hb⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [← prev_zero_diff, ha k hk, sub_self]
    · have := hb k hk
      rw [prev_zero_diff, h2, h1] at this
      exact this

/-- Woodford (2003), (3.2): a solution of `InflSol` is zero before date `d`. -/
theorem inflSol_prefix {κ β : ℝ} {d : ℕ} {n p : ℕ → ℝ} (h : InflSol κ β d n p) :
    ∀ j, j < d → p j = 0 := by
  intro j hj
  induction j with
  | zero => have := h.1 0 hj; simpa [dinfl] using this
  | succ j ih =>
    have := h.1 (j + 1) hj
    simp only [dinfl] at this
    linarith [ih (by omega)]

/-- Woodford (2003), (3.2): bounded solutions of `InflSol` exist for bounded inputs. -/
theorem inflSol_exists {β κ Mn : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (d : ℕ)
    {n : ℕ → ℝ} (hn : ∀ k, |n k| ≤ Mn) :
    ∃ p : ℕ → ℝ, ∃ M, InflSol κ β d n p ∧ ∀ k, |p k| ≤ M := by
  obtain ⟨P, hP, M, hM⟩ := irf_exists_delay hβ0 hβ1 hκ d hn
  have hlag : prev 0 (fun j => P (j + 1)) = P := by
    funext j; cases j with
    | zero => exact hP.1.symm
    | succ j => rfl
  exact ⟨fun j => P (j + 1), M, inflSol_iff.mpr (by rw [hlag]; exact hP), fun k => hM _⟩

/-- Woodford (2003), (3.2): bounded solutions of `InflSol` are unique. -/
theorem inflSol_unique {β κ M1 M2 : ℝ} (hβ0 : 0 ≤ β) (hκ : 0 < κ) {d : ℕ} {n p1 p2 : ℕ → ℝ}
    (h1 : InflSol κ β d n p1) (h2 : InflSol κ β d n p2) (hb1 : ∀ k, |p1 k| ≤ M1)
    (hb2 : ∀ k, |p2 k| ≤ M2) : p1 = p2 := by
  have hl : ∀ (p : ℕ → ℝ) (M : ℝ), (∀ k, |p k| ≤ M) → ∃ M', ∀ k, |prev 0 p k| ≤ M' :=
    fun p M hb => ⟨|M|, fun k => by
      cases k with
      | zero => simp [prev]
      | succ k => exact (hb k).trans (le_abs_self _)⟩
  have := irf_unique hκ hβ0 (inflSol_iff.mp h1) (inflSol_iff.mp h2) (hl p1 M1 hb1)
    (hl p2 M2 hb2)
  funext j
  exact congrFun this (j + 1)

/-- Woodford (2003), (3.2): inflation of a sum of price paths. -/
theorem dinfl_add (p q : ℕ → ℝ) (k : ℕ) :
    dinfl (fun t => p t + q t) k = dinfl p k + dinfl q k := by
  rcases k with _ | k
  · rfl
  · simp only [dinfl]; ring

/-- Woodford (2003), (3.2): inflation of a difference of price paths. -/
theorem dinfl_sub (p q : ℕ → ℝ) (k : ℕ) :
    dinfl (fun t => p t - q t) k = dinfl p k - dinfl q k := by
  rcases k with _ | k
  · rfl
  · simp only [dinfl]; ring

/-- Woodford (2003), (3.2): inflation of a weighted sum of price paths. -/
theorem dinfl_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) (q : ι → ℕ → ℝ) (k : ℕ) :
    dinfl (fun t => ∑ i, w i * q i t) k = ∑ i, w i * dinfl (q i) k := by
  cases k with
  | zero => simp [dinfl]
  | succ k => simp only [dinfl, ← Finset.sum_sub_distrib, mul_sub]

/-- Woodford (2003), (3.2), p. 208 on `shockTree`: a sum over the four states. -/
theorem sum_four (f : Bool × Bool → ℝ) :
    ∑ ω, f ω = f (true, true) + f (true, false) + f (false, true) + f (false, false) := by
  simp only [Fintype.sum_prod_type, Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.sum_singleton]
  ring

/-- Woodford (2003), (3.3), p. 209: on `shockTree`, everything is known from date 1 on. -/
theorem shock_E_pos {t : ℕ} (ht : 1 ≤ t) (x : Bool × Bool → ℝ) : shockSystem.E t x = x := by
  funext ω
  rw [shockSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine shockTree.condE_of_const_on_cell fun ω'' h => ?_
  have : shockObs t ω'' = shockObs t ω := h
  simp only [shockObs, ht, ↓reduceIte] at this
  rw [this]

/-- Woodford (2003), (3.3), p. 209: on `shockTree`, `E_0` is the average over the four states. -/
theorem shock_E_zero (x : Bool × Bool → ℝ) (ω : Bool × Bool) :
    shockSystem.E 0 x ω = ∑ ω', (1 / 4 : ℝ) * x ω' := by
  rw [shockSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  refine shockTree.condE_of_trivial (fun a b => ?_) x ω
  change shockObs 0 a = shockObs 0 b
  simp [shockObs]

/-- Woodford (2003), (3.2), p. 208: inflation of a stochastic price path from `p_{−1} = 0`. -/
def inflOf {Ω' : Type*} (p : ℕ → Ω' → ℝ) : ℕ → Ω' → ℝ
  | 0 => p 0
  | j + 1 => p (j + 1) - p j

/-- Woodford (2003), (3.2): `inflOf` state by state is `dinfl`. -/
theorem inflOf_apply {Ω' : Type*} (p : ℕ → Ω' → ℝ) (k : ℕ) (ω : Ω') :
    inflOf p k ω = dinfl (fun t => p t ω) k := by
  cases k <;> rfl

/-- Woodford (2003), (3.2)–(3.3), pp. 208–209: an equilibrium price level on `shockTree`: (3.2)
with delay `d` and gap `log Y − log P` for the nominal GDP (3.3) with lag `d`, prices preset at
`p_{−1} = 0` before date `d` (zero inflation), adapted and bounded. -/
def TreeEq (κ β ρ : ℝ) (d : ℕ) (e : Bool → ℝ) (qf : ℕ → Bool → ℝ)
    (p : ℕ → Bool × Bool → ℝ) : Prop :=
  DelayedNKPC shockSystem κ β d (inflOf p) (fun t => treeNom ρ d e qf t - p t) ∧
    (∀ k, k < d → inflOf p k = 0) ∧ shockSystem.Adapted p ∧ BoundedProc p

/-- Woodford (2003), (3.2), p. 208 on `shockTree`: state by state, from date `d + 1` on (`E_t`
the identity), an equilibrium obeys `π_T = κ(log Y_T − p_T) + βπ_{T+1}`. -/
theorem treeEq_late {κ β ρ : ℝ} {d : ℕ} {e : Bool → ℝ} {qf : ℕ → Bool → ℝ}
    {p : ℕ → Bool × Bool → ℝ} (h : TreeEq κ β ρ d e qf p) (T : ℕ) (hT : d + 1 ≤ T)
    (ω : Bool × Bool) :
    dinfl (fun t => p t ω) T = κ * (treeNom ρ d e qf T ω - p T ω) +
      β * dinfl (fun t => p t ω) (T + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 + d := ⟨T - d - 1, by omega⟩
  have := congrFun (h.1 (t + 1)) ω
  rw [shock_E_pos (by omega), shock_E_pos (by omega)] at this
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, inflOf_apply] at this
  exact this

/-- Woodford (2003), (3.2), p. 208 on `shockTree`: at date 0 the delayed relation holds in
expectation: `π_d(ω) = κ(E_0 log Y_d − E_0 p_d) + β E_0 π_{d+1}`. -/
theorem treeEq_zero {κ β ρ : ℝ} {d : ℕ} {e : Bool → ℝ} {qf : ℕ → Bool → ℝ}
    {p : ℕ → Bool × Bool → ℝ} (h : TreeEq κ β ρ d e qf p) (ω : Bool × Bool) :
    dinfl (fun t => p t ω) d =
      κ * (∑ ω', (1 / 4 : ℝ) * (treeNom ρ d e qf d ω' - p d ω')) +
        β * ∑ ω', (1 / 4 : ℝ) * dinfl (fun t => p t ω') (d + 1) := by
  have := congrFun (h.1 0) ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add] at this
  rw [shock_E_zero, shock_E_zero] at this
  simp only [inflOf_apply, Pi.sub_apply] at this
  exact this

/-- Woodford (2003), (3.2)–(3.3), pp. 208–209 (**uniqueness** on the tree): there is at most one
equilibrium price level. The state average of the difference of two equilibria solves the
homogeneous delayed system (the date-0 relation holds in expectation), hence vanishes; then each
state's difference solves the homogeneous system with delay `d + 1`, hence vanishes. -/
theorem treeEq_unique {κ β ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) {d : ℕ} {e : Bool → ℝ}
    {qf : ℕ → Bool → ℝ} {p1 p2 : ℕ → Bool × Bool → ℝ} (h1 : TreeEq κ β ρ d e qf p1)
    (h2 : TreeEq κ β ρ d e qf p2) : p1 = p2 := by
  obtain ⟨M1, hM1⟩ := h1.2.2.2
  obtain ⟨M2, hM2⟩ := h2.2.2.2
  set δ : Bool × Bool → ℕ → ℝ := fun ω t => p1 t ω - p2 t ω with hδ
  set a : ℕ → ℝ := fun t => ∑ ω, (1 / 4 : ℝ) * δ ω t with ha
  have hdδ : ∀ ω k, dinfl (δ ω) k = dinfl (fun t => p1 t ω) k - dinfl (fun t => p2 t ω) k :=
    fun ω k => dinfl_sub _ _ k
  have hlow : ∀ ω k, k < d → dinfl (δ ω) k = 0 := fun ω k hk => by
    rw [hdδ, ← inflOf_apply, ← inflOf_apply, h1.2.1 k hk, h2.2.1 k hk]; simp
  have hlate : ∀ ω T, d + 1 ≤ T → dinfl (δ ω) T = κ * (0 - δ ω T) + β * dinfl (δ ω) (T + 1) :=
    fun ω T hT => by
      rw [hdδ, hdδ, treeEq_late h1 T hT, treeEq_late h2 T hT]; simp only [hδ]; ring
  have hat : ∀ ω, dinfl (δ ω) d = κ * (0 - a d) + β * dinfl a (d + 1) := by
    intro ω
    rw [hdδ, treeEq_zero h1, treeEq_zero h2, ha, dinfl_sum]
    simp only [hdδ]
    simp only [hδ, sum_four]
    ring
  have hsumc : ∀ c : ℝ, ∑ _ω : Bool × Bool, (1 / 4 : ℝ) * c = c := fun c => by
    rw [sum_four]; ring
  have hbδ : ∀ ω k, |δ ω k| ≤ M1 + M2 := fun ω k =>
    (abs_sub _ _).trans (add_le_add (hM1 k ω) (hM2 k ω))
  -- the average solves the homogeneous system with delay `d`
  have hasol : InflSol κ β d 0 a := by
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [ha, dinfl_sum]; simp [hlow _ k hk]
    · rcases Nat.eq_or_lt_of_le hk with rfl | hk'
      · rw [ha, dinfl_sum]
        simp only [hat, hsumc, Pi.zero_apply]
        rw [← ha]
      · rw [ha, dinfl_sum, dinfl_sum]
        simp only [hlate _ k hk', Pi.zero_apply]
        simp only [sum_four]; ring
  have hzero : InflSol κ β d 0 (fun _ => 0) :=
    ⟨fun k _ => by cases k <;> simp [dinfl], fun k _ => by cases k <;> simp [dinfl]⟩
  have ha0 : a = fun _ => 0 := inflSol_unique hβ0.le hκ hasol hzero (M1 := M1 + M2)
    (fun k => by
      simp only [ha]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ ω : Bool × Bool, |(1 / 4 : ℝ) * δ ω k| ≤ ∑ _ω : Bool × Bool, (1 / 4) * (M1 + M2) :=
            Finset.sum_le_sum fun ω _ => by
              rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
              exact mul_le_mul_of_nonneg_left (hbδ ω k) (by norm_num)
        _ = M1 + M2 := hsumc _) (M2 := 0) (fun _ => by simp)
  -- each state's difference solves the homogeneous system with delay `d + 1`
  have hstate : ∀ ω, δ ω = fun _ => 0 := by
    intro ω
    have hsol : InflSol κ β (d + 1) 0 (δ ω) := by
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
        · exact hlow ω k hk'
        · rw [hat, ha0]; simp [dinfl]
      · rw [hlate ω k hk]; simp
    have hzero' : InflSol κ β (d + 1) 0 (fun _ => 0) :=
      ⟨fun k _ => by cases k <;> simp [dinfl], fun k _ => by cases k <;> simp [dinfl]⟩
    exact inflSol_unique hβ0.le hκ hsol hzero' (hbδ ω) (M2 := 0) (fun _ => by simp)
  funext t ω
  have := congrFun (hstate ω) t
  simp only [hδ] at this
  linarith

/-- Woodford (2003), (3.2)–(3.3), pp. 208–209 (**existence** on the tree): if nominal GDP is
bounded, an equilibrium exists. Construction: the deterministic response `p̄` to the mean path
`E_0 log Y` (delay `d`), plus in each state the response `p̃_ω` to the state's deviation from the
mean with delay `d + 1` (set from date 1, when the coins are seen); the deviations average to
zero, so the date-0 relation holds in expectation. -/
theorem treeEq_exists {κ β ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1) {d : ℕ}
    {e : Bool → ℝ} {qf : ℕ → Bool → ℝ} (hn : ∃ M, ∀ t ω, |treeNom ρ d e qf t ω| ≤ M) :
    ∃ p, TreeEq κ β ρ d e qf p := by
  obtain ⟨Mn, hMn⟩ := hn
  set n := treeNom ρ d e qf with hndef
  set nbar : ℕ → ℝ := fun t => ∑ ω, (1 / 4 : ℝ) * n t ω with hnbar
  have hsumc : ∀ c : ℝ, ∑ _ω : Bool × Bool, (1 / 4 : ℝ) * c = c := fun c => by
    rw [sum_four]; ring
  have hnb : ∀ t, |nbar t| ≤ Mn := fun t => by
    simp only [hnbar]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ ω : Bool × Bool, |(1 / 4 : ℝ) * n t ω| ≤ ∑ _ω : Bool × Bool, (1 / 4) * Mn :=
          Finset.sum_le_sum fun ω _ => by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
            exact mul_le_mul_of_nonneg_left (hMn t ω) (by norm_num)
      _ = Mn := hsumc _
  obtain ⟨pbar, Mb, hpbar, hMb⟩ := inflSol_exists hβ0 hβ1 hκ d hnb
  have hdev : ∀ ω : Bool × Bool, ∃ q : ℕ → ℝ, ∃ M,
      InflSol κ β (d + 1) (fun k => n k ω - nbar k) q ∧ ∀ k, |q k| ≤ M := fun ω =>
    inflSol_exists hβ0 hβ1 hκ (d + 1) (fun k => (abs_sub _ _).trans
      (add_le_add (hMn k ω) (hnb k)))
  choose ptil Mt hptil using hdev
  -- the deviations average to zero
  set avg : ℕ → ℝ := fun t => ∑ ω, (1 / 4 : ℝ) * ptil ω t with havgdef
  have havg : avg = fun _ => 0 := by
    have hs : InflSol κ β (d + 1) (fun k => ∑ ω, (1 / 4 : ℝ) * (n k ω - nbar k)) avg := by
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rw [havgdef, dinfl_sum]; simp [(hptil _).1.1 k hk]
      · rw [havgdef, dinfl_sum, dinfl_sum]
        simp only [(hptil _).1.2 k hk]
        simp only [sum_four]; ring
    have hin : (fun k => ∑ ω, (1 / 4 : ℝ) * (n k ω - nbar k)) = fun _ => 0 := by
      funext k; simp only [hnbar, sum_four]; ring
    rw [hin] at hs
    have hzero : InflSol κ β (d + 1) (fun _ => 0) (fun _ => 0) :=
      ⟨fun k _ => by cases k <;> simp [dinfl], fun k _ => by cases k <;> simp [dinfl]⟩
    refine inflSol_unique hβ0.le hκ hs hzero (M1 := ∑ ω, |Mt ω|) (fun k => ?_)
      (M2 := 0) (fun _ => by simp)
    simp only [havgdef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have := ((hptil ω).2 k).trans (le_abs_self (Mt ω))
    nlinarith [abs_nonneg (ptil ω k)]
  have hpre : ∀ ω j, j ≤ d → ptil ω j = 0 := fun ω j hj =>
    inflSol_prefix (hptil ω).1 j (by omega)
  set p : ℕ → Bool × Bool → ℝ := fun t ω => pbar t + ptil ω t with hp
  have hdp : ∀ ω k, dinfl (fun t => p t ω) k = dinfl pbar k + dinfl (ptil ω) k :=
    fun ω k => dinfl_add _ _ k
  refine ⟨p, fun t => ?_, fun k hk => ?_, fun t => ?_, ?_⟩
  · -- (3.2) at every date
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, inflOf_apply]
    rcases t with _ | t
    · rw [shock_E_zero, shock_E_zero]
      simp only [inflOf_apply, Pi.sub_apply, zero_add, hdp]
      rw [(hptil ω).1.1 d (Nat.lt_succ_self d), hpbar.2 d le_rfl]
      have h1 : ∑ ω', (1 / 4 : ℝ) * (n d ω' - (pbar d + ptil ω' d)) = nbar d - pbar d := by
        simp only [hpre _ d le_rfl, hnbar, sum_four]; ring
      have h2 : ∑ ω', (1 / 4 : ℝ) * (dinfl pbar (d + 1) + dinfl (ptil ω') (d + 1)) =
          dinfl pbar (d + 1) := by
        have hz := congrFun havg (d + 1)
        simp only [havgdef, sum_four] at hz
        simp only [dinfl, hpre _ d le_rfl, sum_four]
        linear_combination hz
      rw [h1, h2]
      ring
    · rw [shock_E_pos (by omega), shock_E_pos (by omega)]
      simp only [inflOf_apply, Pi.sub_apply, hdp]
      rw [hpbar.2 _ (by omega), (hptil ω).1.2 _ (by omega)]
      simp only [hp]
      ring
  · funext ω
    rw [inflOf_apply, hdp, hpbar.1 k hk, (hptil ω).1.1 k (by omega)]
    simp
  · rcases t with _ | t
    · have hc : p 0 = fun _ => pbar 0 := funext fun ω => by
        simp only [hp, hpre ω 0 (Nat.zero_le d), add_zero]
      rw [hc, shockSystem.const]
    · exact shock_E_pos (by omega) _
  · refine ⟨|Mb| + ∑ ω, |Mt ω|, fun t ω => ?_⟩
    simp only [hp]
    refine (abs_add_le _ _).trans (add_le_add ((hMb t).trans (le_abs_self _)) ?_)
    refine ((hptil ω).2 t).trans ((le_abs_self _).trans ?_)
    exact Finset.single_le_sum (f := fun ω => |Mt ω|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ ω)

/-- Woodford (2003), (3.3), p. 209: without the other disturbance (`q ≡ 0`), log nominal GDP on
the tree is `log Y_{1+k} = e(first coin) · nomIRF ρ s k`, so it is bounded. -/
theorem treeNom_noq {ρ : ℝ} {s : ℕ} {e : Bool → ℝ} (ω : Bool × Bool) (k : ℕ) :
    treeNom ρ s e (fun _ _ => 0) (k + 1) ω = e ω.1 * nomIRF ρ s k := by
  have hq : ∀ t, treeQ (fun _ _ => (0 : ℝ)) t ω = 0 := fun t => by simp [treeQ]
  have hg : ∀ k, treeGrowth ρ s e (fun _ _ => 0) (k + 1) ω =
      e ω.1 * (if k + 1 < s + 1 then 0 else (1 - ρ) * ρ ^ (k - s)) ∧
      treeNom ρ s e (fun _ _ => 0) (k + 1) ω = e ω.1 * nomIRF ρ s k := by
    intro k
    induction k with
    | zero =>
      have hg0 : treeGrowth ρ s e (fun _ _ => 0) 1 ω =
          e ω.1 * (if 0 + 1 < s + 1 then 0 else (1 - ρ) * ρ ^ (0 - s)) := by
        simp only [treeGrowth, mul_zero, zero_add, hq 1, add_zero, treeEps]
        rcases Nat.eq_zero_or_pos s with hs | hs
        · simp [hs]; ring
        · simp [show 1 - s ≠ 1 by omega, show 0 < s by omega]
      refine ⟨hg0, ?_⟩
      simp only [treeNom, zero_add]
      rw [hg0]
      rcases Nat.eq_zero_or_pos s with hs | hs
      · simp [hs, nomIRF]
      · simp [nomIRF, hs]
    | succ k ih =>
      have hg1 : treeGrowth ρ s e (fun _ _ => 0) (k + 1 + 1) ω =
          e ω.1 * (if k + 1 + 1 < s + 1 then 0 else (1 - ρ) * ρ ^ (k + 1 - s)) := by
        have hstep : treeGrowth ρ s e (fun _ _ => 0) (k + 1 + 1) ω =
            ρ * treeGrowth ρ s e (fun _ _ => 0) (k + 1) ω + treeEps ρ e (k + 1 + 1 - s) ω := by
          simp only [treeGrowth, hq (k + 1 + 1), add_zero]
        rw [hstep, ih.1]
        unfold treeEps
        by_cases h1 : k + 1 < s
        · simp [show k + 1 < s + 1 by omega, show k + 1 + 1 < s + 1 by omega,
            show k + 1 + 1 - s ≠ 1 by omega]
        · by_cases h2' : k + 1 = s
          · subst h2'
            simp only [show k + 1 < k + 1 + 1 by omega, show k + 1 + 1 - (k + 1) = 1 by omega,
              lt_irrefl, Nat.sub_self, pow_zero, ↓reduceIte, mul_zero, zero_add]
            ring
          · simp only [show ¬ (k + 1 < s + 1) by omega, show ¬ (k + 1 + 1 < s + 1) by omega,
              show k + 1 + 1 - s ≠ 1 by omega, ↓reduceIte, add_zero]
            rw [show k + 1 - s = (k - s) + 1 by omega, pow_succ]
            ring
      refine ⟨hg1, ?_⟩
      have hn : treeNom ρ s e (fun _ _ => 0) (k + 1 + 1) ω =
          treeNom ρ s e (fun _ _ => 0) (k + 1) ω + treeGrowth ρ s e (fun _ _ => 0) (k + 1 + 1) ω :=
        rfl
      rw [hn, ih.2, hg1]
      have hgr := (nomIRF_growth ρ s).2 k
      have e1 : nomIRF ρ s (k + 1) = nomIRF ρ s k +
          (if k + 1 < s then 0 else (1 - ρ) * ρ ^ (k + 1 - s)) := by linarith
      rw [e1]
      by_cases hks : k + 1 < s
      · simp [hks, show k + 1 + 1 < s + 1 by omega]
      · simp only [hks, show ¬ (k + 1 + 1 < s + 1) by omega, ↓reduceIte]
        ring
  exact (hg k).2

/-- Woodford (2003), **Figure 3.12 on the event tree, complete**: with `q ≡ 0` (or any `q` keeping
nominal GDP bounded), the tree economy has exactly one equilibrium price level (bounded,
adapted, (3.2) with delay `d`, prices preset before `d`), and it has the Figure 3.12 property:
in states differing only in the monetary coin, the price responses differ by `(e − e′)` times
the Figure 3.9 response shifted right by `d`. -/
theorem fig_3_12_tree_equilibrium {κ β ρ : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {d : ℕ} {e : Bool → ℝ} {qf : ℕ → Bool → ℝ}
    (hn : ∃ M, ∀ t ω, |treeNom ρ d e qf t ω| ≤ M) :
    (∃! p, TreeEq κ β ρ d e qf p) ∧
      ∀ p, TreeEq κ β ρ d e qf p → ∀ ω ω' : Bool × Bool, ω.2 = ω'.2 → ∀ k,
        p (1 + k) ω - p (1 + k) ω' =
          (e ω.1 - e ω'.1) * shiftSeq d (fun j => irfP β κ (nomIRF ρ 0) (j + 1)) k := by
  obtain ⟨p, hp⟩ := treeEq_exists hκ hβ0 hβ1 hn
  refine ⟨⟨p, hp, fun p' hp' => treeEq_unique hκ hβ0 hp' hp⟩, fun p' hp' ω ω' h2 k => ?_⟩
  obtain ⟨hnk, hinit, hpa, hpb⟩ := hp'
  have hinit' : ∀ k < d, shockSystem.E 0 (inflOf p' k) = inflOf p' k := fun k hk => by
    rw [hinit k hk]; exact map_zero _
  exact (fig_3_12_tree hκ hβ0 hβ1 hρ0 hρ1 hnk hinit' (fun j => rfl) hpa hpb h2 k).2

/-- Woodford (2003), Figure 3.12 on the event tree: the equilibrium exists for the economy without
the other disturbance (`q ≡ 0`), so `fig_3_12_tree_equilibrium` applies to it (non-vacuous). -/
theorem treeNom_noq_bounded {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (s : ℕ) (e : Bool → ℝ) :
    ∃ M, ∀ t ω, |treeNom ρ s e (fun _ _ => 0) t ω| ≤ M := by
  refine ⟨|e true| + |e false|, fun t ω => ?_⟩
  rcases t with _ | k
  · simp only [treeNom, abs_zero]; positivity
  · rw [treeNom_noq ω k, abs_mul]
    obtain ⟨h0, h1⟩ := (nomIRF_bounds hρ0 hρ1 s).1 k
    have he : |e ω.1| ≤ |e true| + |e false| := by
      cases ω.1 <;> simp
    calc |e ω.1| * |nomIRF ρ s k| ≤ |e ω.1| * 1 := by
          gcongr; rw [abs_le]; constructor <;> linarith
      _ ≤ _ := by rw [mul_one]; exact he

end Woodford.NominalRigidities.Delays
