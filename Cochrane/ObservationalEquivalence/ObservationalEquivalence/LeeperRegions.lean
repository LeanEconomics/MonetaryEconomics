/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ObservationalEquivalence.NonIdentification

/-!
# The four Leeper regions

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 22, §22.3, eqs. (22.3)–(22.6),
p. 500, and §22.7, pp. 508–509 ("Inconsistent or undetermined regimes"); Chapter 23, eqs.
(23.1)–(23.4) and the remarks on pp. 512–513.

The unstarred Leeper (1991) model `i_t = E_t π_{t+1}`, `i_t = φπ_t + u_{i,t}`,
`s̃_{t+1} = γ v_t + u_{s,t+1}`, `ρ v_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}` (`LeeperEqm`, with the
`ρ` that (22.6) omits) and the inherited debt `ρ v_0 + π_0 = K`. Equilibrium criterion
(`Admissible`): adapted, bounded inflation, transversality condition for debt. Disturbances are
bounded and adapted.

## The four regions, with the corrected boundaries (survey error E12)

* (a) `region_a`: `|φ| > 1`, `0 < γ < 2`: exactly one admissible equilibrium.
* (b) `region_b`: `|φ| < 1`, `γ ≤ 0 ∨ γ ≥ 2` (the book: `γ = 0`): exactly one.
* (c) `region_c_iff`: `|φ| > 1`, `γ ≤ 0 ∨ γ ≥ 2` (both active): an equilibrium exists **iff** the
  date-0 restriction `π^m_0 + ρ v^f_0 = K` and the cross-restriction
  `ΔE_{t+1}π^m_{t+1} = (1 − γ)v^f_t − ρ v^f_{t+1} − u_{s,t+1}` hold, where `π^m` is the monetary
  forward solution and `v^f` the fiscal one. Generic non-existence: at most one `K` works
  (`region_c_unique_K`); with martingale-difference fiscal shocks no `K` works
  (`region_c_md_nonexistence`), e.g. on the coin-flip tree (`region_c_coin`).
* (d) `region_d`: `|φ| < 1`, `0 < γ < 2`: uncountably many admissible equilibria;
  `region_d_sunspot`: every bounded martingale-difference sunspot gives one, and on the coin-flip
  tree they are genuinely random (`region_d_coin`).
* The boundary `|φ| = 1` (`0 < γ < 2`): a continuum whenever the monetary equation has a bounded
  solution (`region_d_of_solution`, any `|φ| ≤ 1`), but no equilibrium at all for the bounded
  disturbance `u_{i,t} = −φ^{t+1}` (`region_d_unit_nonexistence`).
* Region (b) needs bounded inherited debt: `region_b_iff` (existence iff `K` bounded),
  `region_b_unbounded_K` (counterexample on `ℕ` with `fullInfo`).

## Remarks of pp. 512–513, made precise

* `tvc_passive` ("if `γ > 0` … any unexpected inflation is consistent with the transversality
  condition", corrected to `0 < γ < 2`): whatever the inflation path, debt from (23.4) satisfies
  the transversality condition.
* `active_fiscal_forced` ("if `γ = 0`, then only one value of unexpected inflation keeps debt from
  exploding", generalised to `|1 − γ| ≥ 1`): debt is the fiscal forward solution and unexpected
  inflation is pinned down, for every `φ`.
* `e19_starred_vs_unstarred` (survey error E19): both-active is determinate in the starred form
  but generically has no equilibrium in the unstarred form.

## Dependence on the equilibrium criterion

With "debt bounded" (Woodford/Leeper) instead of the transversality condition, in the starred
model: `uniqueB_iff` — unique iff `|φ| > 1` or `|1 − γ| > ρ`; the passive-fiscal range shrinks
from `0 < γ < 2` to `1 − ρ ≤ γ ≤ 1 + ρ`; `criterion_matters` gives a `γ` that is passive under
the transversality criterion and active under boundedness; `locallyRicardian_iff_gamma` links
the boundedness criterion to Woodford's locally Ricardian rules (`|1 − γ| < ρ`).

## The printed starred debt equation (16.21)–(16.22)

As printed (PDF p. 399), the starred debt equation uses the actual surplus. Then
`literal_gap`: the gap `v − v*` obeys `ρ d_{t+1} = d_t − ΔE_{t+1}(π − π*)_{t+1}` (no `γ`);
`literal_limit`: `ρᵀ E_t v_{t+T} → ((α − γ)/α)(v_t − v*_t)` for `0 < α < 2`; `literal_tvc_iff`:
the transversality condition holds iff `γ = α` or `v = v*`. So under the printed form fiscal
policy is passive iff `γ = α`, not for every `γ > 0`.
-/

namespace Cochrane.ObservationalEquivalence.LeeperRegions

open Filter Topology
open Cochrane.ObservationalEquivalence.Valuation Cochrane.ObservationalEquivalence.StarredModel
open Cochrane.ObservationalEquivalence.FiscalRec Cochrane.ObservationalEquivalence.Equivalence
open Cochrane.ObservationalEquivalence.ExpectationTools (fullInfo)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Building paths of the Leeper model -/

/-- Cochrane (2023), (23.1)–(23.4), p. 512: the path with inflation `π` and debt `v`, the
interest rate from the rule `i_t = φπ_t + u_{i,t}` and the surplus from
`s̃_{t+1} = γ v_t + u_{s,t+1}`, `s̃_0 = u_{s,0}`. -/
def mkPath (φ γ : ℝ) (ui us π v : ℕ → Ω → ℝ) : Outcome Ω where
  pi := π
  i := fun t => φ • π t + ui t
  v := v
  s := fun t => γ • lag v t + us t

/-- Cochrane (2023), (23.1)–(23.4), p. 512: a path is an equilibrium of the Leeper model when
expected inflation obeys `E_t π_{t+1} = φπ_t + u_{i,t}`, debt obeys (23.4)
`ρ v_{t+1} = (1 − γ)v_t − ΔE_{t+1}π_{t+1} − u_{s,t+1}`, and `ρ v_0 + π_0 = K`. -/
theorem mkPath_eqm {ρ φ γ : ℝ} {ui us π v : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hπ : ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t)
    (hv : ∀ t, ρ • v (t + 1) = (1 - γ) • v t - surprise 𝔼 π t - us (t + 1))
    (h0 : ρ • v 0 + π 0 = K) : LeeperEqm 𝔼 ρ φ γ ui us K (mkPath φ γ ui us π v) := by
  refine ⟨fun t => (hπ t).symm, fun t => rfl, ?_, fun t => rfl, fun t => ?_, h0⟩
  · change γ • (0 : Ω → ℝ) + us 0 = us 0
    rw [smul_zero, zero_add]
  · change ρ • v (t + 1) = v t + (φ • π t + ui t) - π (t + 1) - (γ • v t + us (t + 1))
    rw [hv t, surprise, hπ t, sub_smul, one_smul]
    abel

/-- Cochrane (2023), (23.1)–(23.4), p. 512: every equilibrium of the Leeper model is the path
built from its inflation and debt, and these obey the three conditions of `mkPath_eqm`. -/
theorem eq_mkPath {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) :
    x = mkPath φ γ ui us x.pi x.v ∧ (∀ t, 𝔼.E t (x.pi (t + 1)) = φ • x.pi t + ui t) ∧
      (∀ t, ρ • x.v (t + 1) = (1 - γ) • x.v t - surprise 𝔼 x.pi t - us (t + 1)) ∧
      ρ • x.v 0 + x.pi 0 = K := by
  refine ⟨outcome_ext rfl (funext fun t => hx.2.1 t) rfl (funext fun t => ?_),
    leeper_expected_inflation 𝔼 hx, eq23_4 𝔼 hx, hx.2.2.2.2.2⟩
  rcases t with _ | t
  · change x.s 0 = γ • (0 : Ω → ℝ) + us 0
    rw [smul_zero, zero_add, hx.2.2.1]
  · exact hx.2.2.2.1 t

/-- Cochrane (2023), (23.4), p. 512: debt generated by (23.4) from the inherited debt,
`v_0 = (K − π_0)/ρ`, `v_{t+1} = ((1 − γ)/ρ) v_t + ρ⁻¹(−ΔE_{t+1}π_{t+1} − u_{s,t+1})`. -/
noncomputable def vPath (ρ γ : ℝ) (us : ℕ → Ω → ℝ) (K : Ω → ℝ) (π : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  dRec ((1 - γ) / ρ) (fun t => ρ⁻¹ • (-surprise 𝔼 π t - us (t + 1))) (ρ⁻¹ • (K - π 0))

/-- Cochrane (2023), (23.4), p. 512: `vPath` obeys (23.4) and the date-0 condition, and any debt
path obeying them is `vPath` (`ρ ≠ 0`). -/
theorem vPath_spec {ρ γ : ℝ} (hρ : ρ ≠ 0) {us π : ℕ → Ω → ℝ} {K : Ω → ℝ} :
    (∀ t, ρ • vPath 𝔼 ρ γ us K π (t + 1) =
      (1 - γ) • vPath 𝔼 ρ γ us K π t - surprise 𝔼 π t - us (t + 1)) ∧
      ρ • vPath 𝔼 ρ γ us K π 0 + π 0 = K ∧
      ∀ v : ℕ → Ω → ℝ, (∀ t, ρ • v (t + 1) = (1 - γ) • v t - surprise 𝔼 π t - us (t + 1)) →
        ρ • v 0 + π 0 = K → v = vPath 𝔼 ρ γ us K π := by
  refine ⟨fun t => ?_, ?_, fun v hv h0 => ?_⟩
  · change ρ • (((1 - γ) / ρ) • vPath 𝔼 ρ γ us K π t +
      ρ⁻¹ • (-surprise 𝔼 π t - us (t + 1))) = _
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hρ, mul_inv_cancel₀ hρ, one_smul]
    abel
  · change ρ • (ρ⁻¹ • (K - π 0)) + π 0 = K
    rw [smul_smul, mul_inv_cancel₀ hρ, one_smul, sub_add_cancel]
  · have hrec : ∀ t, v (t + 1) = ((1 - γ) / ρ) • v t +
        ρ⁻¹ • (-surprise 𝔼 π t - us (t + 1)) := fun t => by
      have h := congrArg (fun z => ρ⁻¹ • z) (hv t)
      simp only [smul_smul, inv_mul_cancel₀ hρ, one_smul] at h
      rw [h]
      simp only [smul_sub, smul_neg, smul_smul, inv_mul_eq_div]
      abel
    have hv0 : v 0 = ρ⁻¹ • (K - π 0) := by
      rw [← h0, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hρ, one_smul]
    rw [eq_dRec hrec, hv0]
    rfl

/-- Cochrane (2023), (23.4), p. 512: `vPath` is adapted when inflation and `u_s` are adapted and
`K` is known at date 0. -/
theorem vPath_adapted {ρ γ : ℝ} {us π : ℕ → Ω → ℝ} {K : Ω → ℝ} (hK : 𝔼.E 0 K = K)
    (hπa : 𝔼.Adapted π) (husa : 𝔼.Adapted us) : 𝔼.Adapted (vPath 𝔼 ρ γ us K π) := by
  refine dRec_adapted_of_succ 𝔼 ?_ (fun t => ?_)
  · rw [map_smul, map_sub, hK, hπa 0]
  · rw [map_smul, map_sub, map_neg, surprise, map_sub, hπa (t + 1),
      ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (𝔼.E_E_self t _), husa (t + 1)]

/-! ### Passive fiscal policy: the transversality condition holds automatically -/

/-- Cochrane (2023), p. 513 ("if `γ > 0` the value of debt grows more slowly than the interest
rate, so any unexpected inflation `ΔE_{t+1}π_{t+1}` is consistent with the transversality
condition"; survey error E12: the exact range is `0 < γ < 2`): for `0 ≤ ρ < 1`, `|1 − γ| < 1`
and bounded `u_s`, any debt path obeying (23.4) — whatever the inflation path, bounded or not —
satisfies the transversality condition. -/
theorem tvc_passive {ρ γ M : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hγ : |1 - γ| < 1)
    {us π v : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (hv : ∀ t, ρ • v (t + 1) = (1 - γ) • v t - surprise 𝔼 π t - us (t + 1)) : TVC 𝔼 ρ v := by
  intro t ω
  refine tendsto_zero_of_stable_rec (q := 1 - γ) (r := ρ) (C := |M|)
    (w := fun T => -(ρ ^ T * 𝔼.E t (us (t + T + 1)) ω)) hγ hρ0 hρ1 (fun T => ?_) (fun T => ?_)
  · rw [abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hρ0 T), mul_comm]
    exact mul_le_mul_of_nonneg_right ((𝔼.abs_E_le (hus _) t ω).trans (le_abs_self M))
      (pow_nonneg hρ0 T)
  · have h := congrFun (congrArg (𝔼.E t) (hv (t + T))) ω
    rw [map_smul, map_sub, map_sub, map_smul, E_surprise_later 𝔼 π t T] at h
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero] at h
    rw [show t + (T + 1) = t + T + 1 by omega, pow_succ, mul_assoc, h]
    ring

/-! ### Monetary and fiscal forward solutions -/

/-- Cochrane (2023), (23.1)–(23.2), p. 512 (active money): the monetary forward solution
`π^m_t = −∑_{j ≥ 0} φ^{−j−1} E_t u_{i,t+j}` of `E_t π_{t+1} = φπ_t + u_{i,t}`. -/
noncomputable def piM (φ : ℝ) (ui : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries φ⁻¹ (fun t => (-φ⁻¹) • ui t)

/-- Cochrane (2023), (23.1)–(23.2), p. 512: for `|φ| > 1` and bounded adapted `u_i`, `π^m` is a
bounded adapted solution of `E_t π_{t+1} = φπ_t + u_{i,t}`, and it is the only bounded one. -/
theorem piM_spec {φ M : ℝ} (hφ : 1 < |φ|) {ui : ℕ → Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ M)
    (huia : 𝔼.Adapted ui) :
    (∀ t, 𝔼.E t (piM 𝔼 φ ui (t + 1)) = φ • piM 𝔼 φ ui t + ui t) ∧
      BoundedProc (piM 𝔼 φ ui) ∧ 𝔼.Adapted (piM 𝔼 φ ui) ∧
      ∀ π : ℕ → Ω → ℝ, BoundedProc π → (∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t) →
        π = piM 𝔼 φ ui := by
  have hφ0 : φ ≠ 0 := by
    intro h; rw [h, abs_zero] at hφ; linarith
  have ha : |φ⁻¹| < 1 := by rw [abs_inv]; exact inv_lt_one_of_one_lt₀ hφ
  have hf : ∀ t ω, |(fun t => (-φ⁻¹) • ui t) t ω| ≤ |φ⁻¹| * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hui t ω) (abs_nonneg _)
  have hfa : 𝔼.Adapted (fun t => (-φ⁻¹) • ui t) := fun t => by
    simp only [map_smul, huia t]
  have hconv : ∀ π : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t) ↔
      ForwardSolution.Solves 𝔼 φ⁻¹ (fun t => (-φ⁻¹) • ui t) π := by
    intro π
    refine forall_congr' fun t => ?_
    constructor
    · intro h
      rw [h]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · intro h
      rw [h]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  have hsol := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hf hfa
  refine ⟨(hconv _).mpr hsol, ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hf,
    ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hf, fun π hπb hπ => ?_⟩
  exact ForwardSolution.eq_forwardSeries_abs 𝔼 ha hf hfa ((hconv π).mp hπ) hπb

/-- Cochrane (2023), (23.3)–(23.4), p. 512 (active fiscal): the fiscal forward solution
`v^f_t = ∑_{j ≥ 0} ρʲ (1 − γ)^{−j−1} E_t u_{s,t+1+j}` of
`(1 − γ) v_t = ρ E_t v_{t+1} + E_t u_{s,t+1}`. -/
noncomputable def vF (ρ γ : ℝ) (us : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries (ρ / (1 - γ)) (fun t => (1 - γ)⁻¹ • 𝔼.E t (us (t + 1)))

/-- Cochrane (2023), (23.3)–(23.4), p. 512: for `0 < ρ < 1`, `|1 − γ| ≥ 1` and bounded `u_s`, `v^f`
is a bounded adapted solution of `(1 − γ) v_t = ρ E_t v_{t+1} + E_t u_{s,t+1}`. -/
theorem vF_spec {ρ γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 1 ≤ |1 - γ|)
    {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) :
    (∀ t, (1 - γ) • vF 𝔼 ρ γ us t = ρ • 𝔼.E t (vF 𝔼 ρ γ us (t + 1)) + 𝔼.E t (us (t + 1))) ∧
      BoundedProc (vF 𝔼 ρ γ us) ∧ 𝔼.Adapted (vF 𝔼 ρ γ us) ∧ |ρ / (1 - γ)| < 1 := by
  have hq0 : (1 - γ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hγ; linarith
  have ha : |ρ / (1 - γ)| < 1 := by
    rw [abs_div, abs_of_pos hρ0, div_lt_one (by linarith)]
    linarith
  have hf : ∀ t ω, |(fun t => (1 - γ)⁻¹ • 𝔼.E t (us (t + 1))) t ω| ≤ |(1 - γ)⁻¹| * M :=
    fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hus _) t ω) (abs_nonneg _)
  have hfa : 𝔼.Adapted (fun t => (1 - γ)⁻¹ • 𝔼.E t (us (t + 1))) := fun t => by
    simp only [map_smul, 𝔼.E_E_self]
  have hsol := ForwardSolution.forwardSeries_solves_abs 𝔼 ha hf hfa
  refine ⟨fun t => ?_, ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hf,
    ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hf, ha⟩
  have h := congrArg (fun z => (1 - γ) • z) (hsol t)
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hq0, one_smul,
    mul_div_cancel₀ _ hq0] at h
  exact h

/-- Cochrane (2023), (23.4), p. 512: in the Leeper model, taking `E_t` of (23.4),
`(1 − γ) v_t = ρ E_t v_{t+1} + E_t u_{s,t+1}` (adapted debt). -/
theorem leeper_debt_E {ρ φ γ : ℝ} {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (hva : 𝔼.Adapted x.v) (t : ℕ) :
    (1 - γ) • x.v t = ρ • 𝔼.E t (x.v (t + 1)) + 𝔼.E t (us (t + 1)) := by
  have h := congrArg (𝔼.E t) (eq23_4 𝔼 hx t)
  rw [map_smul, map_sub, map_sub, map_smul, hva t, E_surprise, sub_zero] at h
  rw [h]
  abel

/-- Cochrane (2023), p. 513 ("only one value of unexpected inflation keeps debt from exploding"):
for `|1 − γ| ≥ 1`, an adapted debt path with `(1 − γ) v_t = ρ E_t v_{t+1} + E_t u_{s,t+1}` that
satisfies the transversality condition is the fiscal forward solution `v^f`. -/
theorem eq_vF {ρ γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 1 ≤ |1 - γ|) {us v : ℕ → Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ M) (htvc : TVC 𝔼 ρ v)
    (hv : ∀ t, (1 - γ) • v t = ρ • 𝔼.E t (v (t + 1)) + 𝔼.E t (us (t + 1))) :
    v = vF 𝔼 ρ γ us := by
  have hq0 : (1 - γ) ≠ 0 := by
    intro h; rw [h, abs_zero] at hγ; linarith
  obtain ⟨hsol, ⟨B, hB⟩, -, ha⟩ := vF_spec 𝔼 hρ0 hρ1 hγ hus
  set a := ρ / (1 - γ) with ha_def
  set δ : ℕ → Ω → ℝ := fun t => v t - vF 𝔼 ρ γ us t with hδ_def
  have hδ : ∀ t, δ t = a • 𝔼.E t (δ (t + 1)) := by
    intro t
    have e : (1 - γ) • δ t = ρ • 𝔼.E t (δ (t + 1)) := by
      simp only [hδ_def, map_sub, smul_sub]
      rw [hv t, hsol t]
      abel
    have e2 := congrArg (fun z => (1 - γ)⁻¹ • z) e
    simp only [smul_smul, inv_mul_cancel₀ hq0, one_smul] at e2
    rw [e2, ha_def, div_eq_inv_mul]
  funext t ω
  have hit : ∀ k, δ t ω = a ^ k * 𝔼.E t (v (t + k)) ω - a ^ k * 𝔼.E t (vF 𝔼 ρ γ us (t + k)) ω :=
    fun k => by
      have := congrFun (𝔼.forward_iterate hδ t k) ω
      rw [this]
      simp only [hδ_def, map_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
  have h1 : Tendsto (fun k : ℕ => a ^ k * 𝔼.E t (v (t + k)) ω) atTop (𝓝 0) := by
    have hq1 : ∀ k : ℕ, |a ^ k * 𝔼.E t (v (t + k)) ω| ≤ |ρ ^ k * 𝔼.E t (v (t + k)) ω| := by
      intro k
      rw [ha_def, div_pow, abs_mul, abs_mul, abs_div]
      have hpos : 0 < |(1 - γ) ^ k| := abs_pos.mpr (pow_ne_zero k hq0)
      have hge : 1 ≤ |(1 - γ) ^ k| := by rw [abs_pow]; exact one_le_pow₀ hγ
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      exact le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hge
    have hT : Tendsto (fun k : ℕ => |ρ ^ k * 𝔼.E t (v (t + k)) ω|) atTop (𝓝 0) := by
      simpa using (htvc t ω).abs
    refine squeeze_zero_norm (fun k => ?_) hT
    rw [Real.norm_eq_abs]
    exact hq1 k
  have h2 : Tendsto (fun k : ℕ => a ^ k * 𝔼.E t (vF 𝔼 ρ γ us (t + k)) ω) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero_norm (a := fun k => |a| ^ k * B) (fun k => ?_) ?_
    · rw [sub_zero, norm_norm, Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hB _) t ω) (pow_nonneg (abs_nonneg a) k)
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const B
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  have h4 : Tendsto (fun _ : ℕ => δ t ω) atTop (𝓝 0) := h3.congr fun k => (hit k).symm
  have := tendsto_nhds_unique tendsto_const_nhds h4
  simpa [hδ_def, sub_eq_zero] using this

/-- Cochrane (2023), (23.4), p. 512: the unexpected inflation that the fiscal forward solution
requires, `ν^f_{t+1} = (1 − γ)v^f_t − ρ v^f_{t+1} − u_{s,t+1}`. -/
noncomputable def nuF (ρ γ : ℝ) (us : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (1 - γ) • vF 𝔼 ρ γ us t - ρ • vF 𝔼 ρ γ us (t + 1) - us (t + 1)

/-- Cochrane (2023), p. 513 ("if `γ = 0`, then only one value of unexpected inflation keeps debt
from exploding", generalised to `|1 − γ| ≥ 1`, any `φ`): in every admissible equilibrium of the
Leeper model, debt is the fiscal forward solution and unexpected inflation is `ν^f`. -/
theorem active_fiscal_forced {ρ φ γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hγ : 1 ≤ |1 - γ|)
    {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (hadm : Admissible 𝔼 ρ x) :
    x.v = vF 𝔼 ρ γ us ∧ ∀ t, surprise 𝔼 x.pi t = nuF 𝔼 ρ γ us t := by
  have hv := eq_vF 𝔼 hρ0 hρ1 hγ hus hadm.2.2.2 (leeper_debt_E 𝔼 hx hadm.2.1)
  refine ⟨hv, fun t => ?_⟩
  have h := eq23_4 𝔼 hx t
  rw [hv] at h
  rw [nuF, h]
  abel

/-! ### Region (a): active money, passive fiscal -/

/-- Cochrane (2023), §22.7, p. 508, and (23.1)–(23.4), p. 512 (active money): for `|φ| > 1`
(any `γ`) inflation in every admissible equilibrium is `π^m`, and the whole path is
`mkPath π^m (vPath π^m)`. -/
theorem active_money_forced {ρ φ γ Mi : ℝ} (hρ : ρ ≠ 0) (hφ : 1 < |φ|) {ui us : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi) (huia : 𝔼.Adapted ui) {x : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ γ ui us K x) (hadm : Admissible 𝔼 ρ x) :
    x = mkPath φ γ ui us (piM 𝔼 φ ui) (vPath 𝔼 ρ γ us K (piM 𝔼 φ ui)) := by
  obtain ⟨hxe, hπ, hv, h0⟩ := eq_mkPath 𝔼 hx
  have hpi : x.pi = piM 𝔼 φ ui := (piM_spec 𝔼 hφ hui huia).2.2.2 x.pi hadm.2.2.1 hπ
  rw [hpi] at hv h0
  have hvv := (vPath_spec 𝔼 hρ).2.2 x.v hv h0
  rw [hxe, hpi, hvv]

/-- Cochrane (2023), §22.3, p. 500, §22.7, p. 508, and (23.1)–(23.4), p. 512, region (a): for
`|φ| > 1` and `0 < γ < 2` the Leeper model has exactly one admissible equilibrium. -/
theorem region_a {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < |φ|)
    (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) :
    ∃! x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x := by
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  obtain ⟨hπ, hπb, hπa, -⟩ := piM_spec 𝔼 hφ hui huia
  obtain ⟨hv, h0, -⟩ := vPath_spec 𝔼 hρ0.ne' (γ := γ) (us := us) (K := K) (π := piM 𝔼 φ ui)
  refine ⟨mkPath φ γ ui us (piM 𝔼 φ ui) (vPath 𝔼 ρ γ us K (piM 𝔼 φ ui)),
    ⟨mkPath_eqm 𝔼 hπ hv h0, hπa, vPath_adapted 𝔼 hK hπa husa, hπb,
      tvc_passive 𝔼 hρ0.le hρ1 hγ' hus hv⟩, fun x hx => ?_⟩
  exact active_money_forced 𝔼 hρ0.ne' hφ hui huia hx.1 hx.2

/-! ### Region (b): active fiscal, passive money -/

/-- Cochrane (2023), (23.1)–(23.4), p. 512 (active fiscal): the inflation path
`π_0 = K − ρ v^f_0`, `π_{t+1} = φπ_t + u_{i,t} + ν^f_{t+1}`. -/
noncomputable def piB (ρ φ γ : ℝ) (ui us : ℕ → Ω → ℝ) (K : Ω → ℝ) : ℕ → Ω → ℝ :=
  dRec φ (fun t => ui t + nuF 𝔼 ρ γ us t) (K - ρ • vF 𝔼 ρ γ us 0)

/-- Cochrane (2023), §22.3, p. 500, §22.7, p. 508, and (23.1)–(23.4), p. 512, region (b) (the
book: `φ < 1, γ = 0`; survey error E12: `|φ| < 1` and `γ ≤ 0 ∨ γ ≥ 2`): exactly one admissible
equilibrium — the fiscal theory of the price level with an interest-rate rule (bounded `K`). -/
theorem region_b {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) (hKb : ∃ C, ∀ ω, |K ω| ≤ C) :
    ∃! x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x := by
  have hγ' : 1 ≤ |1 - γ| := (one_le_abs_one_sub_iff γ).mpr hγ
  obtain ⟨hsol, ⟨B, hB⟩, hFa, -⟩ := vF_spec 𝔼 hρ0 hρ1 hγ' hus
  set π := piB 𝔼 ρ φ γ ui us K with hπ_def
  have hnu0 : ∀ t, 𝔼.E t (nuF 𝔼 ρ γ us t) = 0 := fun t => by
    rw [nuF, map_sub, map_sub, map_smul, map_smul, hFa t, hsol t]
    abel
  have hπa : 𝔼.Adapted π := by
    refine dRec_adapted_of_succ 𝔼 ?_ (fun t => ?_)
    · rw [map_sub, map_smul, hK, hFa 0]
    · rw [map_add, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (huia t), nuF, map_sub,
        map_sub, map_smul, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hFa t),
        hFa (t + 1), husa (t + 1)]
  have hπE : ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t := fun t => by
    change 𝔼.E t (φ • π t + (ui t + nuF 𝔼 ρ γ us t)) = _
    rw [map_add, map_smul, map_add, hπa t, huia t, hnu0 t, add_zero]
  have hsur : ∀ t, surprise 𝔼 π t = nuF 𝔼 ρ γ us t := fun t => by
    rw [surprise, hπE t]
    change φ • π t + (ui t + nuF 𝔼 ρ γ us t) - (φ • π t + ui t) = _
    abel
  have hv : ∀ t, ρ • vF 𝔼 ρ γ us (t + 1) =
      (1 - γ) • vF 𝔼 ρ γ us t - surprise 𝔼 π t - us (t + 1) := fun t => by
    rw [hsur t, nuF]
    abel
  have h0 : ρ • vF 𝔼 ρ γ us 0 + π 0 = K := by
    change ρ • vF 𝔼 ρ γ us 0 + (K - ρ • vF 𝔼 ρ γ us 0) = K
    abel
  have hπb : BoundedProc π := by
    obtain ⟨C, hC⟩ := hKb
    refine ⟨(|C| + ρ * |B|) + (|Mi| + (|1 - γ| * |B| + ρ * |B| + |Ms|)) / (1 - |φ|),
      rec_bounded hφ (by positivity) (by positivity) (fun t ω => ?_) (fun t => rfl)
        (fun ω => ?_)⟩
    · have a1 := (hui t ω).trans (le_abs_self Mi)
      have a2 := (hB t ω).trans (le_abs_self B)
      have a3 := (hB (t + 1) ω).trans (le_abs_self B)
      have a4 := (hus (t + 1) ω).trans (le_abs_self Ms)
      simp only [Pi.add_apply, nuF, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add a1 ?_)
      refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) a4)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left a2 (abs_nonneg _)
      · rw [abs_mul, abs_of_pos hρ0]; exact mul_le_mul_of_nonneg_left a3 hρ0.le
    · change |K ω - ρ * vF 𝔼 ρ γ us 0 ω| ≤ _
      refine (abs_sub _ _).trans (add_le_add ((hC ω).trans (le_abs_self C)) ?_)
      rw [abs_mul, abs_of_pos hρ0]
      exact mul_le_mul_of_nonneg_left ((hB 0 ω).trans (le_abs_self B)) hρ0.le
  refine ⟨mkPath φ γ ui us π (vF 𝔼 ρ γ us), ⟨mkPath_eqm 𝔼 hπE hv h0, hπa, hFa, hπb,
    tvc_of_bounded 𝔼 (by rw [abs_of_pos hρ0]; exact hρ1) ⟨B, hB⟩⟩, fun x hx => ?_⟩
  obtain ⟨hvx, hsx⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ' hus hx.1 hx.2
  obtain ⟨hxe, hπx, -, h0x⟩ := eq_mkPath 𝔼 hx.1
  have hrec : ∀ t, x.pi (t + 1) = φ • x.pi t + (ui t + nuF 𝔼 ρ γ us t) := fun t => by
    have h1 := hsx t
    rw [surprise, hπx t] at h1
    rw [← h1]
    abel
  have hpi : x.pi = π := by
    change x.pi = dRec φ (fun t => ui t + nuF 𝔼 ρ γ us t) (K - ρ • vF 𝔼 ρ γ us 0)
    rw [eq_dRec hrec]
    congr 1
    rw [← h0x, hvx]
    abel
  rw [hxe, hpi, hvx]

/-! ### Region (c): both active -/

/-- Cochrane (2023), §22.7, p. 508 ("if `φ > 1` and `γ = 0` both policies are active … inflation
is overdetermined"), region (c) with `|φ| > 1`, `γ ≤ 0 ∨ γ ≥ 2`: an admissible equilibrium
exists iff the date-0 restriction `ρ v^f_0 + π^m_0 = K` and the cross-restriction
`ΔE_{t+1}π^m_{t+1} = ν^f_{t+1}` on the disturbances hold. -/
theorem region_c_iff {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < |φ|)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) :
    (∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) ↔
      (ρ • vF 𝔼 ρ γ us 0 + piM 𝔼 φ ui 0 = K ∧
        ∀ t, surprise 𝔼 (piM 𝔼 φ ui) t = nuF 𝔼 ρ γ us t) := by
  have hγ' : 1 ≤ |1 - γ| := (one_le_abs_one_sub_iff γ).mpr hγ
  obtain ⟨hπ, hπb, hπa, hπu⟩ := piM_spec 𝔼 hφ hui huia
  obtain ⟨-, ⟨B, hB⟩, hFa, -⟩ := vF_spec 𝔼 hρ0 hρ1 hγ' hus
  constructor
  · rintro ⟨x, hx, hadm⟩
    obtain ⟨hvx, hsx⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ' hus hx hadm
    have hpx : x.pi = piM 𝔼 φ ui := hπu x.pi hadm.2.2.1 (leeper_expected_inflation 𝔼 hx)
    refine ⟨?_, fun t => ?_⟩
    · rw [← hvx, ← hpx]; exact hx.2.2.2.2.2
    · rw [← hpx]; exact hsx t
  · rintro ⟨h0, hs⟩
    refine ⟨mkPath φ γ ui us (piM 𝔼 φ ui) (vF 𝔼 ρ γ us), mkPath_eqm 𝔼 hπ (fun t => ?_) h0,
      hπa, hFa, hπb, tvc_of_bounded 𝔼 (by rw [abs_of_pos hρ0]; exact hρ1) ⟨B, hB⟩⟩
    rw [hs t, nuF]
    abel

/-- Cochrane (2023), §22.7, p. 508 (generic non-existence in region (c)): for given
disturbances, at most one inherited debt `K` admits an admissible equilibrium. -/
theorem region_c_unique_K {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < |φ|)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {ui us : ℕ → Ω → ℝ} {K₁ K₂ : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms)
    (h₁ : ∃ x, LeeperEqm 𝔼 ρ φ γ ui us K₁ x ∧ Admissible 𝔼 ρ x)
    (h₂ : ∃ x, LeeperEqm 𝔼 ρ φ γ ui us K₂ x ∧ Admissible 𝔼 ρ x) : K₁ = K₂ := by
  rw [← ((region_c_iff 𝔼 hρ0 hρ1 hφ hγ hui huia hus).mp h₁).1,
    ← ((region_c_iff 𝔼 hρ0 hρ1 hφ hγ hui huia hus).mp h₂).1]

/-- Cochrane (2023), (23.1)–(23.4), p. 512: with zero monetary disturbance the monetary forward
solution is zero. -/
theorem piM_zero (φ : ℝ) : piM 𝔼 φ (0 : ℕ → Ω → ℝ) = 0 := by
  funext t ω
  simp [piM, ExpectationSystem.forwardSeries]

/-- Cochrane (2023), (23.3)–(23.4), p. 512: when fiscal disturbances are unforecastable
(`E_t u_{s,t+1} = 0`) the fiscal forward solution is zero. -/
theorem vF_zero_of_md {ρ γ : ℝ} {us : ℕ → Ω → ℝ} (hmd : ∀ t, 𝔼.E t (us (t + 1)) = 0) :
    vF 𝔼 ρ γ us = 0 := by
  funext t ω
  simp [vF, ExpectationSystem.forwardSeries, hmd]

/-- Cochrane (2023), §22.7, p. 508 (the cross-restriction fails under genuine uncertainty): in
region (c), with no monetary disturbance and unforecastable fiscal disturbances that are not
identically zero, no inherited debt `K` admits an admissible equilibrium. -/
theorem region_c_md_nonexistence {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < |φ|)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ Ms)
    (hmd : ∀ t, 𝔼.E t (us (t + 1)) = 0) (hne : ∃ t ω, us (t + 1) ω ≠ 0) (K : Ω → ℝ) :
    ¬ ∃ x, LeeperEqm 𝔼 ρ φ γ 0 us K x ∧ Admissible 𝔼 ρ x := by
  intro h
  have hz : ∀ t ω, |(0 : ℕ → Ω → ℝ) t ω| ≤ 0 := fun t ω => by simp
  obtain ⟨-, hs⟩ := (region_c_iff 𝔼 hρ0 hρ1 hφ hγ hz (fun t => by simp) hus).mp h
  obtain ⟨t, ω, hω⟩ := hne
  have h1 := congrFun (hs t) ω
  rw [piM_zero, nuF, vF_zero_of_md 𝔼 hmd] at h1
  simp only [surprise, Pi.zero_apply, map_zero, Pi.sub_apply, sub_self, smul_zero, zero_sub,
    zero_eq_neg] at h1
  exact hω h1

/-- Cochrane (2023), §22.7, p. 508, on the coin-flip tree: with `φ = 2`, `γ = 0`, no monetary
disturbance and the coin-flip fiscal shock `u_{s,t} = ±1`, there is no admissible equilibrium for
any inherited debt — both-active policy is inconsistent under genuine uncertainty. -/
theorem region_c_coin {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (K : Bool × Bool → ℝ) :
    ¬ ∃ x, LeeperEqm ExpectationsFiniteTree.coinSystem ρ 2 0 0 ExpectationsFiniteTree.coinShock
      K x ∧ Admissible ExpectationsFiniteTree.coinSystem ρ x := by
  obtain ⟨M, hM⟩ := coinShock_bounded
  refine region_c_md_nonexistence ExpectationsFiniteTree.coinSystem hρ0 hρ1 (by norm_num)
    (Or.inl le_rfl) hM ExpectationsFiniteTree.coinShock_mean_zero ⟨0, (true, true), ?_⟩ K
  simp [ExpectationsFiniteTree.coinShock]

/-- Cochrane (2023), §22.7, p. 508 (survey error E19, confirmed): with `φ > 1` and `γ = 0`, in the
starred form every consistent admissible target is the unique admissible equilibrium, while in
the unstarred form (zero disturbances) no admissible equilibrium exists for any nonzero
inherited debt. -/
theorem e19_starred_vs_unstarred {ρ φ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : 1 < φ) :
    (∀ tg : Outcome Ω, Consistent 𝔼 ρ tg → Admissible 𝔼 ρ tg →
      Eqm 𝔼 ρ φ 0 tg tg ∧ UniqueEqm 𝔼 ρ φ 0 tg) ∧
    ∀ K : Ω → ℝ, K ≠ 0 → ¬ ∃ x, LeeperEqm 𝔼 ρ φ 0 0 0 K x ∧ Admissible 𝔼 ρ x := by
  have hφ' : 1 < |φ| := by rw [abs_of_pos (by linarith)]; exact hφ
  refine ⟨fun tg hc htg => ⟨starred_eqm 𝔼 φ 0 hc, (unique_double_active 𝔼 hρ0.ne' hφ hc htg).2⟩,
    fun K hK h => hK ?_⟩
  have hz : ∀ t ω, |(0 : ℕ → Ω → ℝ) t ω| ≤ 0 := fun t ω => by simp
  obtain ⟨h0, -⟩ := (region_c_iff 𝔼 hρ0 hρ1 hφ' (Or.inl le_rfl) hz (fun t => by simp) hz).mp h
  rw [← h0, piM_zero, vF_zero_of_md 𝔼 (fun t => by simp)]
  simp

/-! ### Region (d): double passive -/

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) (`|φ| < 1`, `0 < γ < 2`, "we are back to
indeterminacy"): the admissible equilibria of the Leeper model form an uncountable set, indexed
by the date-0 inflation rate. -/
theorem region_d [Nonempty Ω] {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) :
    ¬ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x}.Countable := by
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  let f : ℝ → Outcome Ω := fun c =>
    mkPath φ γ ui us (dRec φ ui (fun _ => c)) (vPath 𝔼 ρ γ us K (dRec φ ui (fun _ => c)))
  have hmaps : Set.MapsTo f Set.univ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x} := by
    intro c _
    have hπa : 𝔼.Adapted (dRec φ ui (fun _ => c)) := dRec_adapted 𝔼 huia
    obtain ⟨hv, h0, -⟩ := vPath_spec 𝔼 hρ0.ne' (γ := γ) (us := us) (K := K)
      (π := dRec φ ui (fun _ => c))
    refine ⟨mkPath_eqm 𝔼 (fun t => ?_) hv h0, hπa, vPath_adapted 𝔼 hK hπa husa,
      ⟨|c| + |Mi| / (1 - |φ|), rec_bounded hφ (abs_nonneg c) (abs_nonneg Mi)
        (fun t ω => (hui t ω).trans (le_abs_self Mi)) (fun t => rfl) (fun ω => le_rfl)⟩,
      tvc_passive 𝔼 hρ0.le hρ1 hγ' hus hv⟩
    change 𝔼.E t (φ • dRec φ ui (fun _ => c) t + ui t) = _
    rw [map_add, map_smul, hπa t, huia t]
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrArg Outcome.pi h) 0) ω
    simpa [f, mkPath, dRec] using this
  intro hcount
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Cochrane (2023), p. 513 (survey error E12: "`γ > 0`" is not enough for passive fiscal policy):
with `γ = 3` the debt path and unexpected inflation of every admissible equilibrium are pinned
down (`v = v^f`, `ΔE_{t+1}π_{t+1} = ν^f_{t+1}`), whatever `φ`. -/
theorem gamma_three_active {ρ φ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {ui us : ℕ → Ω → ℝ}
    {K : Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M) {x y : Outcome Ω}
    (hx : LeeperEqm 𝔼 ρ φ 3 ui us K x) (hxa : Admissible 𝔼 ρ x)
    (hy : LeeperEqm 𝔼 ρ φ 3 ui us K y) (hya : Admissible 𝔼 ρ y) :
    x.v = y.v ∧ ∀ t, surprise 𝔼 x.pi t = surprise 𝔼 y.pi t := by
  have hγ : 1 ≤ |1 - (3 : ℝ)| := by norm_num
  obtain ⟨h1, h2⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ hus hx hxa
  obtain ⟨h3, h4⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ hus hy hya
  exact ⟨h1.trans h3.symm, fun t => (h2 t).trans (h4 t).symm⟩

/-! ### Region (d): genuinely random sunspots and the boundary `|φ| = 1` -/

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) with sunspots (`|φ| < 1`, `0 < γ < 2`): for
every bounded adapted martingale difference `ν` and every date-0 inflation `c`, the inflation path
`π_0 = c`, `π_{t+1} = φπ_t + u_{i,t} + ν_{t+1}` with debt from (23.4) is an admissible equilibrium
whose unexpected inflation is `ν`. -/
theorem region_d_sunspot {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : 0 < γ ∧ γ < 2) {ui us ν : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) (hνa : 𝔼.Adapted ν) (hνb : BoundedProc ν)
    (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) (c : ℝ) :
    LeeperEqm 𝔼 ρ φ γ ui us K (mkPath φ γ ui us (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c))
        (vPath 𝔼 ρ γ us K (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c)))) ∧
      Admissible 𝔼 ρ (mkPath φ γ ui us (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c))
        (vPath 𝔼 ρ γ us K (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c)))) ∧
      ∀ t, surprise 𝔼 (dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c)) t = ν (t + 1) := by
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  set π := dRec φ (fun t => ui t + ν (t + 1)) (fun _ => c) with hπ_def
  have hπa : 𝔼.Adapted π := dRec_adapted_of_succ 𝔼 (𝔼.const 0 c) (fun t => by
    rw [map_add, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (huia t), hνa (t + 1)])
  have hπE : ∀ t, 𝔼.E t (π (t + 1)) = φ • π t + ui t := fun t => by
    change 𝔼.E t (φ • π t + (ui t + ν (t + 1))) = _
    rw [map_add, map_smul, map_add, hπa t, huia t, hmd t, add_zero]
  obtain ⟨M, hM⟩ := hνb
  obtain ⟨hv, h0, -⟩ := vPath_spec 𝔼 hρ0.ne' (γ := γ) (us := us) (K := K) (π := π)
  refine ⟨mkPath_eqm 𝔼 hπE hv h0, ⟨hπa, vPath_adapted 𝔼 hK hπa husa,
    ⟨|c| + (|Mi| + |M|) / (1 - |φ|), rec_bounded hφ (abs_nonneg c) (by positivity)
      (fun t ω => (abs_add_le _ _).trans (add_le_add ((hui t ω).trans (le_abs_self Mi))
        ((hM (t + 1) ω).trans (le_abs_self M)))) (fun t => rfl) (fun ω => le_rfl)⟩,
    tvc_passive 𝔼 hρ0.le hρ1 hγ' hus hv⟩, fun t => ?_⟩
  rw [surprise, hπE t]
  change φ • π t + (ui t + ν (t + 1)) - (φ • π t + ui t) = _
  abel

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) on the coin-flip tree: for `|φ| < 1`,
`0 < γ < 2` and any bounded adapted disturbances, the Leeper model has an admissible equilibrium
whose date-1 unexpected inflation is the coin flip `±1` — a genuinely random sunspot
equilibrium. -/
theorem region_d_coin {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : 0 < γ ∧ γ < 2) {ui us : ℕ → Bool × Bool → ℝ} {K : Bool × Bool → ℝ}
    (hui : ∀ t ω, |ui t ω| ≤ Mi) (huia : ExpectationsFiniteTree.coinSystem.Adapted ui)
    (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : ExpectationsFiniteTree.coinSystem.Adapted us)
    (hK : ExpectationsFiniteTree.coinSystem.E 0 K = K) :
    ∃ x, LeeperEqm ExpectationsFiniteTree.coinSystem ρ φ γ ui us K x ∧
      Admissible ExpectationsFiniteTree.coinSystem ρ x ∧
      surprise ExpectationsFiniteTree.coinSystem x.pi 0 = ExpectationsFiniteTree.coinShock 1 := by
  obtain ⟨h1, h2, h3⟩ := region_d_sunspot ExpectationsFiniteTree.coinSystem hρ0 hρ1 hφ hγ hui
    huia hus husa hK coinShock_adapted coinShock_bounded
    ExpectationsFiniteTree.coinShock_mean_zero 0
  exact ⟨_, h1, h2, h3 0⟩

/-- Cochrane (2023), §22.7, pp. 508–509, region (d) extended to `|φ| ≤ 1` (in particular the
boundary `|φ| = 1`): if the monetary equation `E_t π_{t+1} = φπ_t + u_{i,t}` has one bounded
adapted solution, the admissible equilibria form an uncountable set (indexed by the date-0
jump `c`, `π_t = π̄_t + c φᵗ`). -/
theorem region_d_of_solution [Nonempty Ω] {ρ φ γ Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hφ : |φ| ≤ 1) (hγ : 0 < γ ∧ γ < 2) {ui us pb : ℕ → Ω → ℝ} {K : Ω → ℝ}
    (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us) (hK : 𝔼.E 0 K = K)
    (hpa : 𝔼.Adapted pb) (hpb : BoundedProc pb) (hpE : ∀ t, 𝔼.E t (pb (t + 1)) = φ • pb t + ui t) :
    ¬ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x}.Countable := by
  have hγ' : |1 - γ| < 1 := (abs_one_sub_lt_one_iff γ).mpr hγ
  obtain ⟨M, hM⟩ := hpb
  let g : ℝ → ℕ → Ω → ℝ := fun c t => pb t + fun _ => c * φ ^ t
  let f : ℝ → Outcome Ω := fun c => mkPath φ γ ui us (g c) (vPath 𝔼 ρ γ us K (g c))
  have hmaps : Set.MapsTo f Set.univ {x | LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x} := by
    intro c _
    have hga : 𝔼.Adapted (g c) := fun t => by
      change 𝔼.E t (pb t + fun _ => c * φ ^ t) = _
      rw [map_add, hpa t, 𝔼.const]
    have hgE : ∀ t, 𝔼.E t (g c (t + 1)) = φ • g c t + ui t := fun t => by
      change 𝔼.E t (pb (t + 1) + fun _ => c * φ ^ (t + 1)) = φ • (pb t + fun _ => c * φ ^ t) + ui t
      rw [map_add, hpE t, 𝔼.const]
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨hv, h0, -⟩ := vPath_spec 𝔼 hρ0.ne' (γ := γ) (us := us) (K := K) (π := g c)
    refine ⟨mkPath_eqm 𝔼 hgE hv h0, hga, vPath_adapted 𝔼 hK hga husa,
      ⟨M + |c|, fun t ω => ?_⟩, tvc_passive 𝔼 hρ0.le hρ1 hγ' hus hv⟩
    change |pb t ω + c * φ ^ t| ≤ M + |c|
    refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
    rw [abs_mul, abs_pow]
    exact mul_le_of_le_one_right (abs_nonneg c) (pow_le_one₀ (abs_nonneg φ) hφ)
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (congrArg Outcome.pi h) 0) ω
    simpa [f, g, mkPath] using this
  intro hcount
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Cochrane (2023), §22.7, p. 508 (the boundary `|φ| = 1`, including `φ = −1 < 1` that the book
counts as passive): with the bounded monetary disturbance `u_{i,t} = −φ^{t+1}` the Leeper model
has no admissible equilibrium at all, for every `γ`, `u_s` and `K`. So at `|φ| = 1` neither
determinacy nor indeterminacy holds in general: existence depends on `u_i`. -/
theorem region_d_unit_nonexistence [Nonempty Ω] {ρ φ γ : ℝ} (hφ : φ ^ 2 = 1)
    {us : ℕ → Ω → ℝ} {K : Ω → ℝ} :
    ¬ ∃ x, LeeperEqm 𝔼 ρ φ γ (fun t _ => -(φ * φ ^ t)) us K x ∧ Admissible 𝔼 ρ x := by
  rintro ⟨x, hx, hadm⟩
  have hπ := leeper_expected_inflation 𝔼 hx
  have hsol : ForwardSolution.Solves 𝔼 φ (fun t _ => 1 * φ ^ t) x.pi := by
    intro t
    have h := congrArg (fun z => φ • z) (hπ t)
    funext ω
    have h' := congrFun h ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul] at h' ⊢
    have hφ2 : φ * φ = 1 := by rw [← sq]; exact hφ
    linear_combination -h' - (x.pi t ω - φ ^ t) * hφ2
  exact ForwardSolution.no_bounded_solution_unit 𝔼 hφ one_ne_zero hsol hadm.2.2.1

/-! ### Region (b): the bounded inherited debt is necessary -/

/-- Cochrane (2023), §22.7, p. 508, region (b) without assuming `K` bounded: an admissible
equilibrium exists iff the inherited debt `K` is bounded (then it is unique, `region_b`), since
`π_0 = K − ρ v^f_0` is forced and must be bounded. -/
theorem region_b_iff {ρ φ γ Mi Ms : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| < 1)
    (hγ : γ ≤ 0 ∨ 2 ≤ γ) {ui us : ℕ → Ω → ℝ} {K : Ω → ℝ} (hui : ∀ t ω, |ui t ω| ≤ Mi)
    (huia : 𝔼.Adapted ui) (hus : ∀ t ω, |us t ω| ≤ Ms) (husa : 𝔼.Adapted us)
    (hK : 𝔼.E 0 K = K) :
    (∃ x, LeeperEqm 𝔼 ρ φ γ ui us K x ∧ Admissible 𝔼 ρ x) ↔ ∃ C, ∀ ω, |K ω| ≤ C := by
  have hγ' : 1 ≤ |1 - γ| := (one_le_abs_one_sub_iff γ).mpr hγ
  constructor
  · rintro ⟨x, hx, hadm⟩
    obtain ⟨hvx, -⟩ := active_fiscal_forced 𝔼 hρ0 hρ1 hγ' hus hx hadm
    obtain ⟨-, ⟨B, hB⟩, -, -⟩ := vF_spec 𝔼 hρ0 hρ1 hγ' hus
    obtain ⟨M, hM⟩ := hadm.2.2.1
    refine ⟨ρ * B + M, fun ω => ?_⟩
    have h0 := congrFun hx.2.2.2.2.2 ω
    rw [hvx] at h0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
    rw [← h0]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hM 0 ω))
    rw [abs_mul, abs_of_pos hρ0]
    exact mul_le_mul_of_nonneg_left (hB 0 ω) hρ0.le
  · intro hKb
    exact (region_b 𝔼 hρ0 hρ1 hφ hγ hui huia hus husa hK hKb).exists

/-- Cochrane (2023), §22.7, p. 508 (the bounded-`K` hypothesis of `region_b` is needed): with
states `ω ∈ ℕ`, full information and the unbounded inherited debt `K ω = ω`, region (b) (e.g.
`φ = 0`, `γ = 0`, no disturbances) has no admissible equilibrium. -/
theorem region_b_unbounded_K {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ¬ ∃ x, LeeperEqm (fullInfo ℕ) ρ 0 0 0 0 (fun ω => (ω : ℝ)) x ∧
      Admissible (fullInfo ℕ) ρ x := by
  intro h
  have hz : ∀ t ω, |(0 : ℕ → ℕ → ℝ) t ω| ≤ 0 := fun t ω => by simp
  obtain ⟨C, hC⟩ := (region_b_iff (fullInfo ℕ) hρ0 hρ1 (by norm_num) (Or.inl le_rfl) hz
    (fun t => rfl) hz (fun t => rfl) rfl).mp h
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC n
  rw [abs_of_nonneg (Nat.cast_nonneg n)] at this
  linarith

/-! ### Dependence on the equilibrium criterion: bounded debt -/

/-- Cochrane (2023), §22.7, p. 508 (the Woodford/Leeper criterion): inflation and debt adapted
and both bounded. -/
def AdmissibleB (x : Outcome Ω) : Prop :=
  𝔼.Adapted x.pi ∧ 𝔼.Adapted x.v ∧ BoundedProc x.pi ∧ BoundedProc x.v

/-- Cochrane (2023), §22.7, p. 508: the target is the unique equilibrium under the bounded-debt
criterion. -/
def UniqueEqmB (ρ φ γ : ℝ) (tg : Outcome Ω) : Prop :=
  ∀ x, Eqm 𝔼 ρ φ γ tg x → AdmissibleB 𝔼 x → x = tg

/-- Cochrane (2023), §22.1, p. 495: bounded debt satisfies the transversality condition, so the
bounded criterion is stronger. -/
theorem admissible_of_B {ρ : ℝ} (hρ : |ρ| < 1) {x : Outcome Ω} (h : AdmissibleB 𝔼 x) :
    Admissible 𝔼 ρ x :=
  ⟨h.1, h.2.1, h.2.2.1, tvc_of_bounded 𝔼 hρ h.2.2.2⟩

/-- Cochrane (2023), §22.7, p. 508 (and Woodford (2003), Prop. 4.11; survey "boundary depends on
the criterion"): under the bounded-debt criterion the target is the unique equilibrium iff
`|φ| > 1` or `|1 − γ| > ρ`, so the passive-fiscal range is `1 − ρ ≤ γ ≤ 1 + ρ` rather than
`0 < γ < 2`. -/
theorem uniqueB_iff [Nonempty Ω] {ρ φ γ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {tg : Outcome Ω}
    (hc : Consistent 𝔼 ρ tg) (htg : AdmissibleB 𝔼 tg) :
    UniqueEqmB 𝔼 ρ φ γ tg ↔ 1 < |φ| ∨ ρ < |1 - γ| := by
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  constructor
  · intro hu
    by_contra hcon
    simp only [not_or, not_lt] at hcon
    obtain ⟨hφ, hγ⟩ := hcon
    have hq : |(1 - γ) / ρ| ≤ 1 := by
      rw [abs_div, abs_of_pos hρ0, div_le_one hρ0]; exact hγ
    have hx := famPath_eqm 𝔼 hρ0.ne' hc (φ := φ) (γ := γ) 1
    have hB : AdmissibleB 𝔼 (famPath ρ φ γ tg 1) := by
      obtain ⟨hpa, hva, ⟨M, hM⟩, ⟨N, hN⟩⟩ := htg
      refine ⟨fun t => ?_, fun t => ?_, ⟨M + 1, fun t ω => ?_⟩, ⟨N + |1 / ρ|, fun t ω => ?_⟩⟩
      · change 𝔼.E t (tg.pi t + famE φ 1 t) = tg.pi t + famE φ 1 t
        rw [map_add, hpa t]
        congr 1
        exact 𝔼.const t _
      · change 𝔼.E t (tg.v t + famD ρ γ 1 t) = tg.v t + famD ρ γ 1 t
        rw [map_add, hva t]
        congr 1
        exact 𝔼.const t _
      · change |tg.pi t ω + 1 * φ ^ t| ≤ M + 1
        refine (abs_add_le _ _).trans (add_le_add (hM t ω) ?_)
        rw [one_mul, abs_pow]
        exact pow_le_one₀ (abs_nonneg φ) hφ
      · change |tg.v t ω + -(1 / ρ) * ((1 - γ) / ρ) ^ t| ≤ N + |1 / ρ|
        refine (abs_add_le _ _).trans (add_le_add (hN t ω) ?_)
        rw [abs_mul, abs_neg, abs_pow]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hq)
    have h1 := hu _ hx hB
    have h0 : famPath ρ φ γ tg 0 = tg := by
      rw [famPath]
      have e1 : famE φ 0 = (0 : ℕ → Ω → ℝ) := by funext t ω; simp [famE]
      have e2 : famD ρ γ 0 = (0 : ℕ → Ω → ℝ) := by funext t ω; simp [famD]
      rw [e1, e2, ofDev_zero]
    have := famPath_injective ρ φ γ tg (h1.trans h0.symm)
    norm_num at this
  · rintro (hφ | hγ) x hx hxB
    · exact unique_of_active_money 𝔼 hρ0.ne' hφ hc (admissible_of_B 𝔼 hρa htg) x hx
        (admissible_of_B 𝔼 hρa hxB)
    · obtain ⟨he, hd, h0⟩ := deviation_dynamics 𝔼 hc hx
      obtain ⟨hpa, hva, -, ⟨N, hN⟩⟩ := htg
      obtain ⟨-, hva', -, ⟨N', hN'⟩⟩ := hxB
      have hda : 𝔼.Adapted (fun t => x.v t - tg.v t) := fun t => by
        simp only [map_sub, hva t, hva' t]
      have hdb : BoundedProc (fun t => x.v t - tg.v t) := ⟨N' + N, fun t ω => by
        simp only [Pi.sub_apply]
        exact (abs_sub _ _).trans (add_le_add (hN' t ω) (hN t ω))⟩
      have hAR := isAR1_of_dyn 𝔼 (d := fun t => x.v t - tg.v t) hρ0.ne' hda hd
        (fun t => E_surprise 𝔼 _ t)
      have hgt : 1 < |(1 - γ) / ρ| := by
        rw [abs_div, abs_of_pos hρ0, one_lt_div hρ0]; exact hγ
      have d0 : (fun t => x.v t - tg.v t) = 0 := zero_of_E_succ_eq_smul 𝔼 hgt hdb hAR.2
      have e0 := e_zero_of_d_zero 𝔼 (e := fun t => x.pi t - tg.pi t) d0 he hd h0
      rw [eq_ofDev 𝔼 hx, e0, d0, ofDev_zero]

/-- Cochrane (2023), §22.7, p. 508, and pp. 512–513 (the regime boundary depends on the
criterion): for `|φ| ≤ 1` and `γ = (1 − ρ)/2 ∈ (0, 1 − ρ)`, fiscal policy is passive under the
transversality criterion (a continuum of equilibria) but active under the bounded-debt
criterion (the target is the unique equilibrium). -/
theorem criterion_matters [Nonempty Ω] {ρ φ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hφ : |φ| ≤ 1)
    {tg : Outcome Ω} (hc : Consistent 𝔼 ρ tg) (htg : AdmissibleB 𝔼 tg) :
    ¬ UniqueEqm 𝔼 ρ φ ((1 - ρ) / 2) tg ∧ UniqueEqmB 𝔼 ρ φ ((1 - ρ) / 2) tg := by
  have hρa : |ρ| < 1 := by rw [abs_of_pos hρ0]; exact hρ1
  have habs : |1 - (1 - ρ) / 2| = (1 + ρ) / 2 := by
    rw [abs_of_pos (by linarith)]; ring
  refine ⟨not_unique_of_passive 𝔼 hρ0.ne' hφ (by rw [habs]; linarith) hc
    (admissible_of_B 𝔼 hρa htg), (uniqueB_iff 𝔼 hρ0 hρ1 hc htg).mpr (Or.inr ?_)⟩
  rw [habs]
  linarith

/-- Woodford (2003), p. 313, in Cochrane's notation (Cochrane (2023), §22.7, p. 508): a fiscal
rule with debt feedback `γ` (Woodford's `τ_b`) and discount `ρ` (Woodford's `β`) is locally
Ricardian — keeps debt bounded — iff `|1 − γ| < ρ`. -/
theorem locallyRicardian_iff_gamma [Nonempty Ω] {ρ bb γ τg τπ τy τi : ℝ} (hρ : 0 < ρ) :
    LocallyRicardian Ω ρ bb γ τg τπ τy τi ↔ |1 - γ| < ρ := by
  rw [locallyRicardian_iff hρ, abs_mul, abs_inv, abs_of_pos hρ, inv_mul_lt_iff₀ hρ, mul_one]

/-! ### The printed (16.21)–(16.22): both debt equations use the actual surplus -/

/-- Cochrane (2023), (16.21)–(16.22), p. 373, and (22.1), p. 495, as printed (PDF p. 399): when the
starred debt equation `ρ v*_{t+1} = v*_t − ΔE_{t+1}π*_{t+1} − s̃_{t+1}` uses the *actual* surplus,
the gap `d = v − v*` obeys `ρ d_{t+1} = d_t − ΔE_{t+1}(π − π*)_{t+1}`: `γ` drops out. -/
theorem literal_gap {ρ : ℝ} {piS π vS v s : ℕ → Ω → ℝ}
    (hS : ∀ t, ρ • vS (t + 1) = vS t - surprise 𝔼 piS t - s (t + 1))
    (h : ∀ t, ρ • v (t + 1) = v t - surprise 𝔼 π t - s (t + 1)) (t : ℕ) :
    ρ • (v (t + 1) - vS (t + 1)) = (v t - vS t) - surprise 𝔼 (fun t => π t - piS t) t := by
  rw [smul_sub, h t, hS t]
  simp only [surprise, map_sub]
  abel

/-- Cochrane (2023), (16.21), p. 373, as printed, with
`s̃_{t+1} = α v*_t + γ(v_t − v*_t) + u_{s,t+1}`:
`ρ v*_{t+1} = (1 − α) v*_t − γ(v_t − v*_t) − ΔE_{t+1}π*_{t+1} − u_{s,t+1}`. -/
theorem literal_vS {ρ α γ : ℝ} {piS vS v s us : ℕ → Ω → ℝ}
    (hS : ∀ t, ρ • vS (t + 1) = vS t - surprise 𝔼 piS t - s (t + 1))
    (hs : ∀ t, s (t + 1) = α • vS t + γ • (v t - vS t) + us (t + 1)) (t : ℕ) :
    ρ • vS (t + 1) = (1 - α) • vS t - γ • (v t - vS t) - surprise 𝔼 piS t - us (t + 1) := by
  rw [hS t, hs t, sub_smul, one_smul]
  abel

/-- Cochrane (2023), (16.21)–(16.22), p. 373, as printed (coordinator note E6, confirmed): for
`0 < α < 2`, `ρᵀ E_t v_{t+T} → ((α − γ)/α)(v_t − v*_t)`. -/
theorem literal_limit {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : 0 < α ∧ α < 2)
    {piS π vS v us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (hda : 𝔼.Adapted (fun t => v t - vS t))
    (hgap : ∀ t, ρ • (v (t + 1) - vS (t + 1)) =
      (v t - vS t) - surprise 𝔼 (fun t => π t - piS t) t)
    (hvS : ∀ t, ρ • vS (t + 1) =
      (1 - α) • vS t - γ • (v t - vS t) - surprise 𝔼 piS t - us (t + 1)) (t : ℕ) (ω : Ω) :
    Tendsto (fun T : ℕ => ρ ^ T * 𝔼.E t (v (t + T)) ω) atTop
      (𝓝 ((α - γ) / α * (v t ω - vS t ω))) := by
  have hα0 : α ≠ 0 := hα.1.ne'
  have hq : |1 - α| < 1 := (abs_one_sub_lt_one_iff α).mpr hα
  set d : ℕ → Ω → ℝ := fun t => v t - vS t with hd_def
  have hAR : 𝔼.IsAR1 ((1 - 0) / ρ) d :=
    isAR1_of_dyn 𝔼 hρ0.ne' hda (fun t => by rw [sub_zero, one_smul]; exact hgap t)
      (fun t => E_surprise 𝔼 _ t)
  have hdE : ∀ T : ℕ, ρ ^ T * 𝔼.E t (d (t + T)) ω = d t ω := fun T => by
    rw [pow_mul_E_ar1 𝔼 hρ0.ne' hAR t T ω, sub_zero, one_pow, one_mul]
  set y : ℕ → ℝ := fun T => ρ ^ T * 𝔼.E t (vS (t + T)) ω with hy_def
  have hz : Tendsto (fun T => y T + γ / α * d t ω) atTop (𝓝 0) := by
    refine tendsto_zero_of_stable_rec (q := 1 - α) (r := ρ) (C := |M|)
      (w := fun T => -(ρ ^ T * 𝔼.E t (us (t + T + 1)) ω)) hq hρ0.le hρ1 (fun T => ?_)
      (fun T => ?_)
    · rw [abs_neg, abs_mul, abs_of_nonneg (pow_nonneg hρ0.le T), mul_comm]
      exact mul_le_mul_of_nonneg_right ((𝔼.abs_E_le (hus _) t ω).trans (le_abs_self M))
        (pow_nonneg hρ0.le T)
    · have h := congrFun (congrArg (𝔼.E t) (hvS (t + T))) ω
      rw [map_smul, map_sub, map_sub, map_sub, map_smul, map_smul,
        E_surprise_later 𝔼 piS t T] at h
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero] at h
      have h2 := hdE T
      simp only [hd_def] at h2
      simp only [hy_def]
      rw [show t + (T + 1) = t + T + 1 by omega, pow_succ, mul_assoc, h]
      field_simp
      linear_combination (-(γ * α)) * h2
  have hv : ∀ T : ℕ, ρ ^ T * 𝔼.E t (v (t + T)) ω =
      (y T + γ / α * d t ω) + (α - γ) / α * d t ω := fun T => by
    have h2 := hdE T
    simp only [hd_def, map_sub, Pi.sub_apply] at h2 ⊢
    simp only [hy_def]
    field_simp
    linear_combination α * h2
  simp_rw [hv]
  have := hz.add_const ((α - γ) / α * d t ω)
  rw [zero_add] at this
  exact this

/-- Cochrane (2023), (16.21)–(16.22), p. 373, and (22.1), p. 495, as printed: debt satisfies the
transversality condition iff `γ = α` or debt is on target at every date — fiscal policy is passive
**iff** `γ = α`, not for every `γ > 0` (nor for `0 < γ < 2`, the passive range of the unstarred
rule (23.3)). -/
theorem literal_tvc_iff {ρ α γ M : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hα : 0 < α ∧ α < 2)
    {piS π vS v us : ℕ → Ω → ℝ} (hus : ∀ t ω, |us t ω| ≤ M)
    (hda : 𝔼.Adapted (fun t => v t - vS t))
    (hgap : ∀ t, ρ • (v (t + 1) - vS (t + 1)) =
      (v t - vS t) - surprise 𝔼 (fun t => π t - piS t) t)
    (hvS : ∀ t, ρ • vS (t + 1) =
      (1 - α) • vS t - γ • (v t - vS t) - surprise 𝔼 piS t - us (t + 1)) :
    TVC 𝔼 ρ v ↔ γ = α ∨ v = vS := by
  have hlim := literal_limit 𝔼 hρ0 hρ1 hα hus hda hgap hvS
  constructor
  · intro htvc
    by_cases hγ : γ = α
    · exact Or.inl hγ
    · right
      funext t ω
      have h := tendsto_nhds_unique (hlim t ω) (htvc t ω)
      have hc : (α - γ) / α ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hγ)) hα.1.ne'
      have := (mul_eq_zero.mp h).resolve_left hc
      linarith
  · rintro (hγ | hv) t ω
    · have := hlim t ω
      rwa [hγ, sub_self, zero_div, zero_mul] at this
    · subst hv
      have := hlim t ω
      rwa [sub_self, mul_zero] at this

end Cochrane.ObservationalEquivalence.LeeperRegions
