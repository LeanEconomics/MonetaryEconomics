/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Generality.LogLinearIdentities
import Generality.ExpectationsFiniteTree
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# State variables: the simplest fiscal-theory model by undetermined coefficients

Cochrane (2023), *The Fiscal Theory of the Price Level*, Online Appendix A1.9.1, pp. 576–577.

The model (1.47)–(1.50): `i_t = E_t π_{t+1}`, `ρv_{t+1} = v_t + i_t − π_{t+1} − s_{t+1}`,
`i_t = u_{i,t}`, `s_t = u_{s,t}`, with AR(1) disturbances.

## Main results

* `Eqm` (the equilibrium conditions), `eqm_solves` (taking `E_t` of (1.48) gives the forward
  equation `v_t = ρ E_t v_{t+1} + E_t s_{t+1}`), `eqm_infl`.
* Existence and uniqueness with bounded debt: `vstar`, `vstar_apply`, `inflStar`, `msv_exists`,
  `msv_v_unique`, `msv_unique`, `msv_determinacy` (an equilibrium has bounded `v` iff `v` is the
  forward solution).
* Survey error E24: the general corrected formula `msv_infl_innov`
  (`π_{t+1} = i_t − ΔE_{t+1}∑_j ρʲ s_{t+1+j}`, minus, not plus); the AR(1) closed forms
  `vstar_ar1`, `msv_solution` (`v_t = η_s u_{s,t}/(1 − ρη_s)`,
  `π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)`), `msv_solution_is_eqm`; the printed sign fails:
  `msv_printed_not_eqm`, with a genuine-uncertainty case `msv_printed_fails_coin`.
* Undetermined coefficients (p. 577): `GuessOK`, `msv_coeffs_iff` (the guess works iff
  `A = [[1, 0], [0, η_s/(1−ρη_s)]]`, `B = [[0, −1/(1−ρη_s)], [0, 0]]`, under `ρ ≠ 0`,
  `ρη_i ≠ 1`, `ρη_s ≠ 1`), `msv_coeffs_printed_fails` (the printed `B_{πs} = +1/(1−ρη_s)`).
* The explosive root (restated from the Woodford Chapter 4 project, `Fiscal.lean`): `dRec`,
  `eq_dRec`, `abs_rec_le`, `rec_bounded`, `rec_unbounded`; `msv_debt_rec` (debt follows `dRec`
  with `γ = ρ⁻¹ > 1`), `msv_debt_not_bibo`, `msv_deviation_iterate` and
  `msv_deviation_explodes` (a non-fundamental debt path diverges like `ρ⁻ᵏ` in expectation).
-/

namespace Cochrane.Generality.MSV

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), A1 (1.47)–(1.50), p. 576: `(π, v)` is an equilibrium of the simplest model
given the disturbances `u_i = i` and `u_s = s`: both adapted, `i_t = E_t π_{t+1}` (1.47) and
`ρv_{t+1} = v_t + i_t − π_{t+1} − s_{t+1}` (1.48). -/
def Eqm (ρ : ℝ) (ui us infl v : ℕ → Ω → ℝ) : Prop :=
  𝔼.Adapted infl ∧ 𝔼.Adapted v ∧ (∀ t, 𝔼.E t (infl (t + 1)) = ui t) ∧
    ∀ t ω, ρ * v (t + 1) ω = v t ω + ui t ω - infl (t + 1) ω - us (t + 1) ω

/-- Cochrane (2023), A1 (1.47)–(1.48), p. 576: taking `E_t` of (1.48) and using (1.47) gives the
forward equation `v_t = ρ E_t v_{t+1} + E_t s_{t+1}`. -/
theorem eqm_solves {ρ : ℝ} {ui us infl v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui)
    (h : Eqm 𝔼 ρ ui us infl v) :
    ForwardSolution.Solves 𝔼 ρ (fun t => 𝔼.E t (us (t + 1))) v := by
  obtain ⟨-, hv, h47, h48⟩ := h
  intro t
  have hfun : ρ • v (t + 1) = v t + ui t - infl (t + 1) - us (t + 1) := by
    funext ω
    exact h48 t ω
  have hE := congrArg (𝔼.E t) hfun
  rw [map_smul, map_sub, map_sub, map_add, hv t, hui t, h47 t] at hE
  rw [hE]
  abel

/-- Cochrane (2023), A1 (1.48), p. 576: in an equilibrium, inflation is
`π_{t+1} = v_t + i_t − s_{t+1} − ρv_{t+1}`. -/
theorem eqm_infl {ρ : ℝ} {ui us infl v : ℕ → Ω → ℝ} (h : Eqm 𝔼 ρ ui us infl v) (t : ℕ)
    (ω : Ω) : infl (t + 1) ω = v t ω + ui t ω - us (t + 1) ω - ρ * v (t + 1) ω := by
  linarith [h.2.2.2 t ω]

/-- Cochrane (2023), A1 p. 576: the forward solution for debt,
`v*_t = ∑_{k≥0} ρᵏ E_t s_{t+1+k}`. -/
noncomputable def vstar (ρ : ℝ) (us : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  𝔼.forwardSeries ρ (fun t => 𝔼.E t (us (t + 1)))

/-- Cochrane (2023), A1 p. 576: `v*_t = ∑_k ρᵏ E_t s_{t+k+1}` (law of iterated expectations). -/
theorem vstar_apply (ρ : ℝ) (us : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    vstar 𝔼 ρ us t ω = ∑' k, ρ ^ k * 𝔼.E t (us (t + k + 1)) ω := by
  unfold vstar ExpectationSystem.forwardSeries
  refine tsum_congr fun k => ?_
  rw [𝔼.tower (Nat.le_add_right t k)]

/-- Cochrane (2023), A1 p. 576: the forcing `E_t s_{t+1}` is adapted and bounded by the bound
of `s`. -/
theorem forcing_ok {us : ℕ → Ω → ℝ} {K : ℝ} (hus : ∀ t ω, |us t ω| ≤ K) :
    𝔼.Adapted (fun t => 𝔼.E t (us (t + 1))) ∧ ∀ t ω, |𝔼.E t (us (t + 1)) ω| ≤ K :=
  ⟨fun t => 𝔼.E_E_self t _, fun t ω => 𝔼.abs_E_le (hus (t + 1)) t ω⟩

/-- Cochrane (2023), A1 p. 576: the equilibrium inflation built from the forward solution,
`π*_{t+1} = v*_t + i_t − s_{t+1} − ρv*_{t+1}` (`π*_0 = 0`; date-0 inflation is not determined by
the model). -/
noncomputable def inflStar (ρ : ℝ) (ui us : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | t + 1 => fun ω => vstar 𝔼 ρ us t ω + ui t ω - us (t + 1) ω - ρ * vstar 𝔼 ρ us (t + 1) ω

/-- Cochrane (2023), A1 p. 576 ("We know the answer already"): for bounded adapted
disturbances and `|ρ| < 1`, the forward solution and its inflation form a bounded equilibrium. -/
theorem msv_exists {ρ K : ℝ} (hρ : |ρ| < 1) {ui us : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui)
    (hus : 𝔼.Adapted us) (huib : BoundedProc ui) (husb : ∀ t ω, |us t ω| ≤ K) :
    Eqm 𝔼 ρ ui us (inflStar 𝔼 ρ ui us) (vstar 𝔼 ρ us) ∧ BoundedProc (vstar 𝔼 ρ us) ∧
      BoundedProc (inflStar 𝔼 ρ ui us) := by
  obtain ⟨hwa, hwb⟩ := forcing_ok 𝔼 husb
  have hsol := ForwardSolution.forwardSeries_solves_abs 𝔼 hρ hwb hwa
  have hva := ForwardSolution.forwardSeries_adapted_abs 𝔼 hρ hwb
  have hvb := ForwardSolution.forwardSeries_bounded_abs 𝔼 hρ hwb
  change ForwardSolution.Solves 𝔼 ρ _ (vstar 𝔼 ρ us) at hsol
  change 𝔼.Adapted (vstar 𝔼 ρ us) at hva
  change BoundedProc (vstar 𝔼 ρ us) at hvb
  refine ⟨⟨?_, hva, ?_, ?_⟩, hvb, ?_⟩
  · intro t
    rcases t with _ | t
    · exact map_zero _
    · have he : inflStar 𝔼 ρ ui us (t + 1) =
          vstar 𝔼 ρ us t + ui t - us (t + 1) - ρ • vstar 𝔼 ρ us (t + 1) := by
        funext ω
        rfl
      rw [he, map_sub, map_sub, map_add, map_smul, ForwardSolution.E_of_known 𝔼
        (Nat.le_succ t) (hva t), ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hui t),
        hus (t + 1), hva (t + 1)]
  · intro t
    have he : inflStar 𝔼 ρ ui us (t + 1) =
        vstar 𝔼 ρ us t + ui t - us (t + 1) - ρ • vstar 𝔼 ρ us (t + 1) := by
      funext ω
      rfl
    rw [he, map_sub, map_sub, map_add, map_smul, hva t, hui t, hsol t]
    beta_reduce
    abel
  · intro t ω
    change ρ * vstar 𝔼 ρ us (t + 1) ω = vstar 𝔼 ρ us t ω + ui t ω -
      (vstar 𝔼 ρ us t ω + ui t ω - us (t + 1) ω - ρ * vstar 𝔼 ρ us (t + 1) ω) - us (t + 1) ω
    ring
  · obtain ⟨Kv, hKv⟩ := hvb
    obtain ⟨Ki, hKi⟩ := huib
    refine ⟨|Kv| + |Ki| + |K| + |ρ| * |Kv|, fun t ω => ?_⟩
    rcases t with _ | t
    · change |(0 : ℝ)| ≤ _
      rw [abs_zero]
      positivity
    · change |vstar 𝔼 ρ us t ω + ui t ω - us (t + 1) ω - ρ * vstar 𝔼 ρ us (t + 1) ω| ≤ _
      have h1 := (hKv t ω).trans (le_abs_self Kv)
      have h2 := (hKi t ω).trans (le_abs_self Ki)
      have h3 := (husb (t + 1) ω).trans (le_abs_self K)
      have h4 : |ρ * vstar 𝔼 ρ us (t + 1) ω| ≤ |ρ| * |Kv| := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((hKv (t + 1) ω).trans (le_abs_self Kv))
          (abs_nonneg ρ)
      calc _ ≤ |vstar 𝔼 ρ us t ω + ui t ω - us (t + 1) ω| + |ρ * vstar 𝔼 ρ us (t + 1) ω| :=
            abs_sub _ _
        _ ≤ |vstar 𝔼 ρ us t ω + ui t ω| + |us (t + 1) ω| + |ρ * vstar 𝔼 ρ us (t + 1) ω| := by
            gcongr
            exact abs_sub _ _
        _ ≤ |vstar 𝔼 ρ us t ω| + |ui t ω| + |us (t + 1) ω| + |ρ * vstar 𝔼 ρ us (t + 1) ω| := by
            gcongr
            exact abs_add_le _ _
        _ ≤ _ := by linarith

/-- Cochrane (2023), A1 p. 576–577 (uniqueness): in any equilibrium with bounded debt, debt is
the forward solution `v = v*`. -/
theorem msv_v_unique {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui)
    (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) (hvb : BoundedProc v) :
    v = vstar 𝔼 ρ us := by
  obtain ⟨hwa, hwb⟩ := forcing_ok 𝔼 husb
  exact ForwardSolution.eq_forwardSeries_abs 𝔼 hρ hwb hwa (eqm_solves 𝔼 hui h) hvb

/-- Cochrane (2023), A1 p. 576–577: two equilibria with bounded debt have the same debt and the
same inflation `π_{t+1}` at every date. -/
theorem msv_unique {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl₁ v₁ infl₂ v₂ : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (husb : ∀ t ω, |us t ω| ≤ K) (h₁ : Eqm 𝔼 ρ ui us infl₁ v₁)
    (h₂ : Eqm 𝔼 ρ ui us infl₂ v₂) (hb₁ : BoundedProc v₁) (hb₂ : BoundedProc v₂) :
    v₁ = v₂ ∧ ∀ t, infl₁ (t + 1) = infl₂ (t + 1) := by
  have e₁ := msv_v_unique 𝔼 hρ hui husb h₁ hb₁
  have e₂ := msv_v_unique 𝔼 hρ hui husb h₂ hb₂
  refine ⟨e₁.trans e₂.symm, fun t => funext fun ω => ?_⟩
  rw [eqm_infl 𝔼 h₁, eqm_infl 𝔼 h₂, e₁, e₂]

/-- Cochrane (2023), A1 p. 577 ("Determinacy comes here from the assumption that `v_t` is a
time-invariant function of the state variables", made precise): an equilibrium has bounded debt
iff its debt is the forward solution. -/
theorem msv_determinacy {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) :
    BoundedProc v ↔ v = vstar 𝔼 ρ us := by
  refine ⟨msv_v_unique 𝔼 hρ hui husb h, fun he => ?_⟩
  rw [he]
  exact ForwardSolution.forwardSeries_bounded_abs 𝔼 hρ (forcing_ok 𝔼 husb).2

/-- Cochrane (2023), A1 p. 576 (survey E24, corrected): in any equilibrium with bounded debt,
`π_{t+1} = i_t − ΔE_{t+1} ∑_{j≥0} ρʲ s_{t+1+j}`, where the innovation is
`∑_j ρʲ E_{t+1}s_{t+1+j} − ∑_j ρʲ E_t s_{t+1+j}` (the book prints `+`). -/
theorem msv_infl_innov {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (hus : 𝔼.Adapted us) (husb : ∀ t ω, |us t ω| ≤ K)
    (h : Eqm 𝔼 ρ ui us infl v) (hvb : BoundedProc v) (t : ℕ) (ω : Ω) :
    infl (t + 1) ω = ui t ω - (∑' j, ρ ^ j * 𝔼.E (t + 1) (us (t + 1 + j)) ω -
      ∑' j, ρ ^ j * 𝔼.E t (us (t + 1 + j)) ω) := by
  have hv := msv_v_unique 𝔼 hρ hui husb h hvb
  have hsum : Summable fun j => ρ ^ j * 𝔼.E (t + 1) (us (t + 1 + j)) ω :=
    Summable.of_norm_bounded ((summable_geometric_of_abs_lt_one (by rwa [abs_abs])).mul_right K)
      fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (husb _) _ ω) (pow_nonneg (abs_nonneg _) j)
  have h1 : ∑' j, ρ ^ j * 𝔼.E (t + 1) (us (t + 1 + j)) ω =
      us (t + 1) ω + ρ * vstar 𝔼 ρ us (t + 1) ω := by
    rw [hsum.tsum_eq_zero_add, vstar_apply, ← tsum_mul_left, pow_zero, one_mul, add_zero,
      hus (t + 1)]
    congr 1
    refine tsum_congr fun k => ?_
    rw [pow_succ, show t + 1 + (k + 1) = t + 1 + k + 1 by omega]
    ring
  have h2 : ∑' j, ρ ^ j * 𝔼.E t (us (t + 1 + j)) ω = vstar 𝔼 ρ us t ω := by
    rw [vstar_apply]
    refine tsum_congr fun k => ?_
    rw [show t + 1 + k = t + k + 1 by omega]
  rw [h1, h2, eqm_infl 𝔼 h, hv]
  ring

/-- Cochrane (2023), A1 p. 576: with an AR(1) surplus `E_t s_{t+1} = η_s s_t`, `|ρη_s| < 1`, the
forward solution is `v*_t = η_s s_t/(1 − ρη_s)`. -/
theorem vstar_ar1 {ρ ηs : ℝ} (hρη : |ρ * ηs| < 1) {us : ℕ → Ω → ℝ} (har : 𝔼.IsAR1 ηs us)
    (t : ℕ) (ω : Ω) : vstar 𝔼 ρ us t ω = ηs / (1 - ρ * ηs) * us t ω := by
  rw [vstar_apply]
  have he : ∀ k, ρ ^ k * 𝔼.E t (us (t + k + 1)) ω = ηs * us t ω * (ρ * ηs) ^ k := by
    intro k
    rw [show t + k + 1 = t + (k + 1) by omega, 𝔼.ar1_iterate har, Pi.smul_apply, smul_eq_mul,
      mul_pow, pow_succ]
    ring
  rw [tsum_congr he, tsum_mul_left, tsum_geometric_of_abs_lt_one hρη, div_eq_mul_inv]
  ring

/-- Cochrane (2023), A1 p. 576 (survey E24, corrected closed forms): with AR(1) surpluses, in any
equilibrium with bounded debt, `v_t = η_s u_{s,t}/(1 − ρη_s)` and
`π_{t+1} = u_{i,t} − ε_{s,t+1}/(1 − ρη_s)`, `ε_{s,t+1} = u_{s,t+1} − η_s u_{s,t}`. -/
theorem msv_solution {ρ ηs K : ℝ} (hρ : |ρ| < 1) (hρη : |ρ * ηs| < 1)
    {ui us infl v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (har : 𝔼.IsAR1 ηs us)
    (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) (hvb : BoundedProc v) :
    (∀ t ω, v t ω = ηs / (1 - ρ * ηs) * us t ω) ∧
      ∀ t ω, infl (t + 1) ω = ui t ω - (us (t + 1) ω - ηs * us t ω) / (1 - ρ * ηs) := by
  have hv := msv_v_unique 𝔼 hρ hui husb h hvb
  have hvt : ∀ t ω, v t ω = ηs / (1 - ρ * ηs) * us t ω := fun t ω => by
    rw [hv, vstar_ar1 𝔼 hρη har]
  refine ⟨hvt, fun t ω => ?_⟩
  have hne : 1 - ρ * ηs ≠ 0 := by
    intro h0
    have : ρ * ηs = 1 := by linarith
    rw [this, abs_one] at hρη
    exact lt_irrefl _ hρη
  have hne2 : 1 - ηs * ρ ≠ 0 := by rwa [mul_comm]
  rw [eqm_infl 𝔼 h, hvt, hvt]
  field_simp
  ring

/-- Cochrane (2023), A1 p. 576: the corrected closed forms are an equilibrium (with bounded debt),
for bounded adapted `u_i` and bounded AR(1) `u_s`. -/
theorem msv_solution_is_eqm {ρ ηs K : ℝ} (hρ : |ρ| < 1) (hρη : |ρ * ηs| < 1)
    {ui us : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (huib : BoundedProc ui) (har : 𝔼.IsAR1 ηs us)
    (husb : ∀ t ω, |us t ω| ≤ K) :
    ∃ infl v : ℕ → Ω → ℝ, Eqm 𝔼 ρ ui us infl v ∧ BoundedProc v ∧
      (∀ t ω, v t ω = ηs / (1 - ρ * ηs) * us t ω) ∧
      ∀ t ω, infl (t + 1) ω = ui t ω - (us (t + 1) ω - ηs * us t ω) / (1 - ρ * ηs) := by
  obtain ⟨he, hvb, -⟩ := msv_exists 𝔼 hρ hui har.1 huib husb
  obtain ⟨h1, h2⟩ := msv_solution 𝔼 hρ hρη hui har husb he hvb
  exact ⟨_, _, he, hvb, h1, h2⟩

/-- Cochrane (2023), A1 p. 576 (survey E24): the printed `π_{t+1} = u_{i,t} + ε_{s,t+1}/(1 − ρη_s)`
is not the inflation of any equilibrium with bounded debt as soon as some surplus shock
`ε_{s,t+1}` is nonzero. -/
theorem msv_printed_not_eqm {ρ ηs K : ℝ} (hρ : |ρ| < 1) (hρη : |ρ * ηs| < 1)
    {ui us infl v : ℕ → Ω → ℝ} (hui : 𝔼.Adapted ui) (har : 𝔼.IsAR1 ηs us)
    (husb : ∀ t ω, |us t ω| ≤ K)
    (hprinted : ∀ t ω, infl (t + 1) ω = ui t ω + (us (t + 1) ω - ηs * us t ω) / (1 - ρ * ηs))
    (hshock : ∃ t ω, us (t + 1) ω - ηs * us t ω ≠ 0) :
    ¬ (Eqm 𝔼 ρ ui us infl v ∧ BoundedProc v) := by
  rintro ⟨h, hvb⟩
  obtain ⟨t, ω, hε⟩ := hshock
  have hc := (msv_solution 𝔼 hρ hρη hui har husb h hvb).2 t ω
  rw [hprinted t ω] at hc
  have hne : 1 - ρ * ηs ≠ 0 := by
    intro h0
    have : ρ * ηs = 1 := by linarith
    rw [this, abs_one] at hρη
    exact lt_irrefl _ hρη
  have : (us (t + 1) ω - ηs * us t ω) / (1 - ρ * ηs) = 0 := by linarith
  rcases div_eq_zero_iff.mp this with h0 | h0
  · exact hε h0
  · exact hne h0

/-- Cochrane (2023), A1 p. 576: the i.i.d. coin-flip surplus `u_s = coinAR1 0` is bounded by one. -/
theorem coin_bdd (t : ℕ) (ω : Bool × Bool) : |ExpectationsFiniteTree.coinAR1 0 t ω| ≤ 1 := by
  rcases t with _ | t
  · simp [ExpectationsFiniteTree.coinAR1]
  · simp only [ExpectationsFiniteTree.coinAR1, zero_mul, zero_add,
      ExpectationsFiniteTree.coinShock]
    split_ifs <;> norm_num

/-- Cochrane (2023), A1 p. 576 (survey E24, genuine-uncertainty instance): on the coin-flip tree
with `ρ = 1/2`, `u_i = 0` and i.i.d. surplus shocks `u_s = ε_s = ±1`, the corrected solution is a
bounded equilibrium, while no bounded-debt equilibrium has the printed inflation. -/
theorem msv_printed_fails_coin {infl v : ℕ → Bool × Bool → ℝ}
    (hprinted : ∀ t ω, infl (t + 1) ω = 0 + (ExpectationsFiniteTree.coinAR1 0 (t + 1) ω -
      0 * ExpectationsFiniteTree.coinAR1 0 t ω) / (1 - 1 / 2 * 0)) :
    (∃ infl' v' : ℕ → Bool × Bool → ℝ,
      Eqm ExpectationsFiniteTree.coinSystem (1 / 2) 0 (ExpectationsFiniteTree.coinAR1 0) infl' v'
        ∧ BoundedProc v') ∧
      ¬ (Eqm ExpectationsFiniteTree.coinSystem (1 / 2) 0 (ExpectationsFiniteTree.coinAR1 0)
        infl v ∧ BoundedProc v) := by
  have hρ : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  have hρη : |(1 / 2 : ℝ) * 0| < 1 := by norm_num
  have hui : ExpectationsFiniteTree.coinSystem.Adapted (0 : ℕ → Bool × Bool → ℝ) :=
    fun t => map_zero _
  have har := ExpectationsFiniteTree.coinAR1_isAR1 0
  refine ⟨?_, msv_printed_not_eqm _ hρ hρη hui har coin_bdd hprinted ⟨0, (true, true), ?_⟩⟩
  · obtain ⟨infl', v', he, hvb, -⟩ := msv_solution_is_eqm _ hρ hρη hui ⟨0, fun _ _ => by simp⟩
      har coin_bdd
    exact ⟨infl', v', he, hvb⟩
  · rw [(ExpectationsFiniteTree.coinAR1_nondegenerate 0).1]
    norm_num

/-! ### Undetermined coefficients (p. 577) -/

/-- Cochrane (2023), A1 p. 576–577: the guess `π_{t+1} = A_{πi}u_{i,t} + A_{πs}u_{s,t} +
B_{πi}ε_{i,t+1} + B_{πs}ε_{s,t+1}`, `v_t = A_{vi}u_{i,t} + A_{vs}u_{s,t} + B_{vi}ε_{i,t+1} +
B_{vs}ε_{s,t+1}` satisfies (1.47) (with `E_t ε_{t+1} = 0`) and (1.48) (with
`u_{t+1} = ηu_t + ε_{t+1}` and free date-`t+2` shocks) for all values of states and shocks. -/
def GuessOK (ρ ηi ηs aπi aπs bπi bπs avi avs bvi bvs : ℝ) : Prop :=
  (∀ ui us : ℝ, aπi * ui + aπs * us = ui) ∧
    ∀ ui us ei es ei' es' : ℝ,
      (aπi * ui + aπs * us + bπi * ei + bπs * es) - (avi * ui + avs * us + bvi * ei + bvs * es) =
        -ρ * (avi * (ηi * ui + ei) + avs * (ηs * us + es) + bvi * ei' + bvs * es') + ui -
          (ηs * us + es)

/-- Cochrane (2023), A1 p. 577 ("Solving, we find the right answer"), corrected (survey E24): the
guess works iff `A = [[1, 0], [0, η_s/(1−ρη_s)]]` and `B = [[0, −1/(1−ρη_s)], [0, 0]]`
(assuming `ρ ≠ 0`, `ρη_i ≠ 1`, `ρη_s ≠ 1`). -/
theorem msv_coeffs_iff {ρ ηi ηs aπi aπs bπi bπs avi avs bvi bvs : ℝ} (hρ : ρ ≠ 0)
    (hi : ρ * ηi ≠ 1) (hs : ρ * ηs ≠ 1) :
    GuessOK ρ ηi ηs aπi aπs bπi bπs avi avs bvi bvs ↔
      aπi = 1 ∧ aπs = 0 ∧ avi = 0 ∧ avs = ηs / (1 - ρ * ηs) ∧ bπi = 0 ∧
        bπs = -(1 / (1 - ρ * ηs)) ∧ bvi = 0 ∧ bvs = 0 := by
  have hs' : 1 - ρ * ηs ≠ 0 := fun h => hs (by linarith)
  have hi' : 1 - ρ * ηi ≠ 0 := fun h => hi (by linarith)
  constructor
  · rintro ⟨h1, h2⟩
    have a1 : aπi = 1 := by simpa using h1 1 0
    have a2 : aπs = 0 := by simpa using h1 0 1
    have d1 : bvi = 0 := by
      have := h2 0 0 0 0 1 0
      simp only [mul_zero, add_zero, sub_zero, zero_add, mul_one] at this
      rcases mul_eq_zero.mp (show ρ * bvi = 0 by linarith) with h | h
      · exact absurd h hρ
      · exact h
    have d2 : bvs = 0 := by
      have := h2 0 0 0 0 0 1
      simp only [mul_zero, add_zero, sub_zero, zero_add, mul_one] at this
      rcases mul_eq_zero.mp (show ρ * bvs = 0 by linarith) with h | h
      · exact absurd h hρ
      · exact h
    have c1 : avi = 0 := by
      have := h2 1 0 0 0 0 0
      simp only [mul_zero, add_zero, sub_zero, mul_one] at this
      rw [a1] at this
      have : avi * (1 - ρ * ηi) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hi'
    have c2 : avs = ηs / (1 - ρ * ηs) := by
      have := h2 0 1 0 0 0 0
      simp only [mul_zero, add_zero, mul_one, zero_add] at this
      rw [a2] at this
      rw [eq_div_iff hs']
      linarith
    have b1 : bπi = 0 := by
      have := h2 0 0 1 0 0 0
      simp only [mul_zero, add_zero, mul_one, zero_add] at this
      rw [c1, d1] at this
      linarith
    have b2 : bπs = -(1 / (1 - ρ * ηs)) := by
      have := h2 0 0 0 1 0 0
      simp only [mul_zero, add_zero, mul_one, zero_add] at this
      rw [c2, d2] at this
      field_simp
      field_simp at this
      linarith
    exact ⟨a1, a2, c1, c2, b1, b2, d1, d2⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ⟨fun ui us => by ring, fun ui us ei es ei' es' => ?_⟩
    field_simp
    ring

/-- Cochrane (2023), A1 p. 577 (survey E24): the printed coefficient `B_{πs} = +1/(1 − ρη_s)`
(with the other printed entries) fails the undetermined-coefficients conditions. -/
theorem msv_coeffs_printed_fails {ρ ηi ηs : ℝ} (hρ : ρ ≠ 0) (hi : ρ * ηi ≠ 1)
    (hs : ρ * ηs ≠ 1) :
    ¬ GuessOK ρ ηi ηs 1 0 0 (1 / (1 - ρ * ηs)) 0 (ηs / (1 - ρ * ηs)) 0 0 := by
  intro h
  have := ((msv_coeffs_iff hρ hi hs).mp h).2.2.2.2.2.1
  have hs' : 1 - ρ * ηs ≠ 0 := fun h => hs (by linarith)
  have h2 : 1 / (1 - ρ * ηs) = 0 := by linarith
  exact one_div_ne_zero hs' h2

/-! ### The explosive root (restated from the Woodford Chapter 4 project) -/

/-- Cochrane (2023), A1 (1.48), p. 576 (restated from the Woodford Chapter 4 project, (4.5)): the
path generated recursively from `d_0` and inputs `u_t`: `d_{t+1} = γ d_t + u_t`. -/
def dRec (γ : ℝ) (u : ℕ → Ω → ℝ) (d0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => d0
  | t + 1 => γ • dRec γ u d0 t + u t

/-- Cochrane (2023), A1 p. 576 (restated from the Woodford Chapter 4 project): a solution of
`d_{t+1} = γ d_t + u_t` is determined by `d_0`: it is `dRec`. -/
theorem eq_dRec {γ : ℝ} {u d : ℕ → Ω → ℝ} (hd : ∀ t, d (t + 1) = γ • d t + u t) :
    d = dRec γ u (d 0) := by
  funext t
  induction t with
  | zero => rfl
  | succ t ih => rw [hd t, ih]; rfl

/-- Cochrane (2023), A1 p. 577 (restated from the Woodford Chapter 2/4 projects): a stable
scalar recursion `x_{t+1} = λx_t + u_t`, `|λ| < 1`, with bounded inputs stays bounded. -/
theorem abs_rec_le {lam C B : ℝ} (hl : |lam| < 1) {u x : ℕ → ℝ} (hu : ∀ t, |u t| ≤ C)
    (hx0 : |x 0| ≤ B) (hx : ∀ t, x (t + 1) = lam * x t + u t) (t : ℕ) :
    |x t| ≤ max B (C / (1 - |lam|)) := by
  have h1 : 0 < 1 - |lam| := by linarith
  induction t with
  | zero => exact le_max_of_le_left hx0
  | succ t ih =>
    rw [hx t]
    set K := max B (C / (1 - |lam|))
    have hK : C ≤ (1 - |lam|) * K := by
      have := le_max_right B (C / (1 - |lam|))
      rw [div_le_iff₀ h1] at this
      linarith
    calc |lam * x t + u t| ≤ |lam| * |x t| + |u t| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |lam| * K + C := by gcongr; exact hu t
      _ ≤ K := by linarith

/-- Cochrane (2023), A1 p. 577 (restated from the Woodford Chapter 4 project): for `|γ| < 1` the
scalar recursion `d_{t+1} = γd_t + u_t` is bounded-input-bounded-state. -/
theorem rec_bounded {γ B U : ℝ} (hγ : |γ| < 1) {u d : ℕ → Ω → ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hu : ∀ t ω, |u t ω| ≤ U) (hd : ∀ t, d (t + 1) = γ • d t + u t) (h0 : ∀ ω, |d 0 ω| ≤ B) :
    ∀ t ω, |d t ω| ≤ B + U / (1 - |γ|) := by
  intro t ω
  have hq : 0 ≤ U / (1 - |γ|) := div_nonneg hU (by linarith)
  refine (abs_rec_le hγ (u := fun t => u t ω) (x := fun t => d t ω) (fun t => hu t ω) (h0 ω)
    (fun t => by simp [hd t]) t).trans ?_
  exact max_le (by linarith) (by linarith)

/-- Cochrane (2023), A1 p. 577 (restated from the Woodford Chapter 4 project): for `|γ| ≥ 1` the
scalar recursion is not bounded-input-bounded-state: with `s = sign γ` and inputs
`u_t = ε s^{t+1}`, the path from `d_0 = 0` satisfies `|d_t| ≥ εt`. -/
theorem rec_unbounded {γ ε : ℝ} (hγ : 1 ≤ |γ|) (hε : 0 ≤ ε) {d : ℕ → Ω → ℝ}
    (hd : ∀ t, d (t + 1) = γ • d t +
      fun _ => ε * (if 0 ≤ γ then (1 : ℝ) else -1) ^ (t + 1))
    (h0 : d 0 = 0) : ∀ t ω, ε * t ≤ |d t ω| := by
  set s : ℝ := if 0 ≤ γ then 1 else -1 with hs
  have hss : s * s = 1 := by rw [hs]; split_ifs <;> norm_num
  have hγs : γ = s * |γ| := by
    rw [hs]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  have key : ∀ t ω, ε * t ≤ s ^ t * d t ω := by
    intro t
    induction t with
    | zero => intro ω; simp [h0]
    | succ t ih =>
      intro ω
      rw [hd t]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e : s ^ (t + 1) * (γ * d t ω + ε * s ^ (t + 1)) = |γ| * (s ^ t * d t ω) + ε := by
        have h2 : s ^ (t + 1) * s ^ (t + 1) = 1 := by
          rw [← mul_pow, hss, one_pow]
        have h3 : γ * d t ω = s * |γ| * d t ω := by rw [← hγs]
        rw [h3]
        calc s ^ (t + 1) * (s * |γ| * d t ω + ε * s ^ (t + 1))
            = |γ| * (s ^ t * (s * s) * d t ω) + ε * (s ^ (t + 1) * s ^ (t + 1)) := by ring
          _ = _ := by rw [hss, h2]; ring
      rw [e]
      push_cast
      have := ih ω
      have ht : 0 ≤ ε * t := mul_nonneg hε (Nat.cast_nonneg t)
      nlinarith
  intro t ω
  have hst : |s ^ t| = 1 := by
    rw [abs_pow]
    have : |s| = 1 := by rw [hs]; split_ifs <;> norm_num
    rw [this, one_pow]
  calc ε * t ≤ s ^ t * d t ω := key t ω
    _ ≤ |s ^ t * d t ω| := le_abs_self _
    _ = |d t ω| := by rw [abs_mul, hst, one_mul]

/-- Cochrane (2023), A1 (1.48), p. 576: in any equilibrium, debt follows the recursion `dRec` with
the explosive root `γ = ρ⁻¹` and inputs `ρ⁻¹(i_t − π_{t+1} − s_{t+1})`. -/
theorem msv_debt_rec {ρ : ℝ} (hρ : ρ ≠ 0) {ui us infl v : ℕ → Ω → ℝ}
    (h : Eqm 𝔼 ρ ui us infl v) :
    v = dRec ρ⁻¹ (fun t ω => ρ⁻¹ * (ui t ω - infl (t + 1) ω - us (t + 1) ω)) (v 0) := by
  refine eq_dRec fun t => funext fun ω => ?_
  have := h.2.2.2 t ω
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  linarith

/-- Cochrane (2023), A1 p. 577: since `|ρ⁻¹| ≥ 1` for `0 < |ρ| ≤ 1`, the debt recursion
`d_{t+1} = ρ⁻¹d_t + u_t` is not bounded-input-bounded-state: bounded inputs can produce
`|d_t| ≥ εt`. Boundedness of debt is therefore a genuine restriction. -/
theorem msv_debt_not_bibo {ρ ε : ℝ} (hρ0 : ρ ≠ 0) (hρ : |ρ| ≤ 1) (hε : 0 ≤ ε)
    {d : ℕ → Ω → ℝ}
    (hd : ∀ t, d (t + 1) = ρ⁻¹ • d t +
      fun _ => ε * (if 0 ≤ ρ⁻¹ then (1 : ℝ) else -1) ^ (t + 1))
    (h0 : d 0 = 0) : ∀ t ω, ε * t ≤ |d t ω| := by
  have hγ : 1 ≤ |ρ⁻¹| := by
    rw [abs_inv]
    exact one_le_inv_iff₀.mpr ⟨abs_pos.mpr hρ0, hρ⟩
  exact rec_unbounded hγ hε hd h0

/-- Cochrane (2023), A1 p. 577: the deviation `d = v − v*` of an equilibrium debt path from the
forward solution obeys `d_s = ρᵏ E_s d_{s+k}`, i.e. `E_s d_{s+k} = ρ⁻ᵏ d_s`. -/
theorem msv_deviation_iterate {ρ K : ℝ} (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) (s k : ℕ) :
    v s - vstar 𝔼 ρ us s = ρ ^ k • 𝔼.E s (v (s + k) - vstar 𝔼 ρ us (s + k)) := by
  obtain ⟨hwa, hwb⟩ := forcing_ok 𝔼 husb
  have h1 := eqm_solves 𝔼 hui h
  have h2 := ForwardSolution.forwardSeries_solves_abs 𝔼 hρ hwb hwa
  have hd : ∀ t, (v - vstar 𝔼 ρ us) t = ρ • 𝔼.E t ((v - vstar 𝔼 ρ us) (t + 1)) := by
    intro t
    simp only [Pi.sub_apply, map_sub, smul_sub]
    rw [h1 t]
    unfold vstar
    rw [h2 t]
    abel
  exact 𝔼.forward_iterate hd s k

/-- Cochrane (2023), A1 p. 577 (the explosive root `ρ⁻¹`): if an equilibrium's debt differs from the
forward solution at some date and state, its expected deviation explodes,
`|E_s(v_{s+k} − v*_{s+k})| = |ρ|⁻ᵏ|v_s − v*_s| → ∞`. -/
theorem msv_deviation_explodes {ρ K : ℝ} (hρ0 : ρ ≠ 0) (hρ : |ρ| < 1) {ui us infl v : ℕ → Ω → ℝ}
    (hui : 𝔼.Adapted ui) (husb : ∀ t ω, |us t ω| ≤ K) (h : Eqm 𝔼 ρ ui us infl v) (s : ℕ)
    (ω : Ω) (hne : v s ω ≠ vstar 𝔼 ρ us s ω) :
    Tendsto (fun k => |𝔼.E s (v (s + k) - vstar 𝔼 ρ us (s + k)) ω|) atTop atTop := by
  have he : ∀ k, |𝔼.E s (v (s + k) - vstar 𝔼 ρ us (s + k)) ω| =
      |ρ⁻¹| ^ k * |v s ω - vstar 𝔼 ρ us s ω| := by
    intro k
    have h1 := congrFun (msv_deviation_iterate 𝔼 hρ hui husb h s k) ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, abs_mul, abs_pow, ← mul_assoc, ← mul_pow, abs_inv, inv_mul_cancel₀
      (abs_ne_zero.mpr hρ0), one_pow, one_mul]
  simp_rw [he]
  have hγ : 1 < |ρ⁻¹| := by
    rw [abs_inv]
    exact one_lt_inv_iff₀.mpr ⟨abs_pos.mpr hρ0, hρ⟩
  exact (tendsto_pow_atTop_atTop_of_one_lt hγ).atTop_mul_const (abs_pos.mpr (sub_ne_zero.mpr hne))

end Cochrane.Generality.MSV
