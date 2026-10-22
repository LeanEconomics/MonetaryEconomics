/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.InstrumentPath
import GainsFromCommitment.TargetingRule
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Composite disturbances with infinitely many shock types

Woodford (2003), *Interest and Prices*, Chapter 7, §4, eq. (4.3), pp. 520–521, and §5.1
(Proposition 7.15, p. 523).

`InstrumentPath.compositeShock` formalises (4.3) for finitely many types. The book allows "an
extremely large (not necessarily finite) number of different types of real disturbances"
(p. 521). Here the types are indexed by `ℕ`, with an absolutely summable family of weights.

## Main results

* `typeShock` (`u^j_t = ∑_k ψ_{jk} ε^j_{t−k}`) and `compositeInf` (`u_t = ∑_j u^j_t`), under
  `SummableFamily ψ` (`∑_j ∑_k |ψ_{jk}| < ∞`): well defined and bounded (`typeShock_bdd`,
  `compositeInf_summable`, `compositeInf_bdd`); every finite composite is one
  (`compositeShock_eq_inf`, `summableFamily_fin`), in particular the AR(1) process; if every shock
  is known from its date on, the composite is adapted (`compositeInf_adapted`).
* **Superposition** (pp. 520–521, "one can compute the response … to this particular type of
  shock"): the forward component of the optimal plan is the sum over types of the type-specific
  forward components (`fwdU_composite`), so along the optimal equilibrium of (5.1)
  `x_t = μ₁x_{t−1} − (κ/λ)∑_j F^j_t` and `π_t = (1 − μ₁)(λ/κ)x_{t−1} + ∑_j F^j_t`
  (`star_composite`).
* **Robust optimality for infinitely many types** (p. 521): for every summable family and every
  bounded shock histories, the target criterion (5.1) — with coefficients that do not depend on
  `ψ` — has exactly one bounded adapted equilibrium, and it solves the optimal-policy problem of
  Proposition 7.7 (`targeting_rule_composite`).
-/

namespace Woodford.GainsFromCommitment.TidyR5CompositeShocks

open Filter Topology

variable {Ω : Type*}

/-! ### Composite disturbances with countably many types -/

/-- Woodford (2003), eq. (4.3), p. 520: the contribution of shock type `j`,
`u^j_t = ∑_{k≥0} ψ_{jk} ε^j_{t−k}` (shock histories indexed by `ℤ`). -/
noncomputable def typeShock (ψ : ℕ → ℕ → ℝ) (ε : ℕ → ℤ → Ω → ℝ) (j : ℕ) (t : ℤ) : Ω → ℝ :=
  fun ω => ∑' k : ℕ, ψ j k * ε j (t - k) ω

/-- Woodford (2003), eq. (4.3), p. 520, with countably many types:
`u_t = ∑_j ∑_{k≥0} ψ_{jk} ε^j_{t−k}`. -/
noncomputable def compositeInf (ψ : ℕ → ℕ → ℝ) (ε : ℕ → ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ :=
  fun ω => ∑' j, typeShock ψ ε j t ω

/-- Woodford (2003), p. 521 ("not necessarily finite"): the weights form an absolutely summable
family, `∑_k |ψ_{jk}| < ∞` for each type and `∑_j ∑_k |ψ_{jk}| < ∞`. -/
def SummableFamily (ψ : ℕ → ℕ → ℝ) : Prop :=
  (∀ j, Summable fun k => |ψ j k|) ∧ Summable fun j => ∑' k, |ψ j k|

/-- Woodford (2003), eq. (4.3) (tool): each type's series converges absolutely. -/
theorem typeShock_summable {ψ : ℕ → ℕ → ℝ} {ε : ℕ → ℤ → Ω → ℝ} {M : ℝ}
    (hψ : SummableFamily ψ) (hε : ∀ j s ω, |ε j s ω| ≤ M) (j : ℕ) (t : ℤ) (ω : Ω) :
    Summable fun k : ℕ => ψ j k * ε j (t - k) ω :=
  Summable.of_norm_bounded ((hψ.1 j).mul_right M) fun k => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hε j _ ω) (abs_nonneg _)

/-- Woodford (2003), eq. (4.3): `|u^j_t| ≤ (∑_k |ψ_{jk}|) M` for shocks bounded by `M`. -/
theorem typeShock_bdd {ψ : ℕ → ℕ → ℝ} {ε : ℕ → ℤ → Ω → ℝ} {M : ℝ}
    (hψ : SummableFamily ψ) (hε : ∀ j s ω, |ε j s ω| ≤ M) (j : ℕ) (t : ℤ) (ω : Ω) :
    |typeShock ψ ε j t ω| ≤ (∑' k, |ψ j k|) * M := by
  have hg : HasSum (fun k => |ψ j k| * M) ((∑' k, |ψ j k|) * M) := (hψ.1 j).hasSum.mul_right M
  have := tsum_of_norm_bounded hg (f := fun k : ℕ => ψ j k * ε j (t - k) ω) (fun k => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hε j _ ω) (abs_nonneg _))
  rwa [Real.norm_eq_abs] at this

/-- Woodford (2003), eq. (4.3): the series over types converges absolutely. -/
theorem compositeInf_summable {ψ : ℕ → ℕ → ℝ} {ε : ℕ → ℤ → Ω → ℝ} {M : ℝ}
    (hψ : SummableFamily ψ) (hε : ∀ j s ω, |ε j s ω| ≤ M) (t : ℤ) (ω : Ω) :
    Summable fun j => typeShock ψ ε j t ω :=
  Summable.of_norm_bounded (hψ.2.mul_right M) fun j => by
    rw [Real.norm_eq_abs]
    exact typeShock_bdd hψ hε j t ω

/-- Woodford (2003), eq. (4.3): with countably many types the composite disturbance is bounded,
`|u_t| ≤ (∑_j ∑_k |ψ_{jk}|) M`. -/
theorem compositeInf_bdd {ψ : ℕ → ℕ → ℝ} {ε : ℕ → ℤ → Ω → ℝ} {M : ℝ}
    (hψ : SummableFamily ψ) (hε : ∀ j s ω, |ε j s ω| ≤ M) (t : ℤ) (ω : Ω) :
    |compositeInf ψ ε t ω| ≤ (∑' j, ∑' k, |ψ j k|) * M := by
  have hg : HasSum (fun j => (∑' k, |ψ j k|) * M) ((∑' j, ∑' k, |ψ j k|) * M) :=
    hψ.2.hasSum.mul_right M
  have := tsum_of_norm_bounded hg (f := fun j => typeShock ψ ε j t ω) (fun j => by
    rw [Real.norm_eq_abs]
    exact typeShock_bdd hψ hε j t ω)
  rwa [Real.norm_eq_abs] at this

/-- Woodford (2003), eq. (4.3) (tool): extending a finite family of weights by zero. -/
noncomputable def extendPsi {J : ℕ} (ψ : Fin J → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun j k => if h : j < J then ψ ⟨j, h⟩ k else 0

/-- Woodford (2003), eq. (4.3) (tool): extending a finite family of shocks by zero. -/
noncomputable def extendEps {J : ℕ} (ε : Fin J → ℤ → Ω → ℝ) : ℕ → ℤ → Ω → ℝ :=
  fun j s => if h : j < J then ε ⟨j, h⟩ s else 0

/-- Woodford (2003), eq. (4.3): a finite family of absolutely summable weights, extended by zero,
is a summable family. -/
theorem summableFamily_fin {J : ℕ} {ψ : Fin J → ℕ → ℝ} (hψ : ∀ j, Summable fun k => |ψ j k|) :
    SummableFamily (extendPsi ψ) := by
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : j < J
    · simpa [extendPsi, h] using hψ ⟨j, h⟩
    · simp [extendPsi, h]
  · refine summable_of_ne_finset_zero (s := Finset.range J) fun j hj => ?_
    have h : ¬ j < J := fun h => hj (Finset.mem_range.mpr h)
    simp [extendPsi, h]

/-- Woodford (2003), eq. (4.3): every finite composite (`InstrumentPath.compositeShock`, in
particular the AR(1) process, `InstrumentPath.ar1_as_composite`) is a composite with countably
many types. -/
theorem compositeShock_eq_inf {J : ℕ} (ψ : Fin J → ℕ → ℝ) (ε : Fin J → ℤ → Ω → ℝ) (t : ℤ) :
    InstrumentPath.compositeShock ψ ε t = compositeInf (extendPsi ψ) (extendEps ε) t := by
  funext ω
  unfold InstrumentPath.compositeShock compositeInf
  rw [tsum_eq_sum (s := Finset.range J) fun j hj => ?_]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => typeShock (extendPsi ψ) (extendEps ε) j t ω)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [typeShock, extendPsi, extendEps, j.isLt]
  · have h : ¬ j < J := fun h => hj (Finset.mem_range.mpr h)
    simp [typeShock, extendPsi, h]

/-- Woodford (2003), eq. (4.3) and p. 488 (adaptedness): if every shock `ε^j_s` is known at every
date `n ≥ s`, the composite disturbance `u_n` is known at date `n`, for any expectation system
(`E_n` commutes with the dominated series over types and over lags). -/
theorem compositeInf_adapted (𝔼 : ExpectationSystem Ω) {ψ : ℕ → ℕ → ℝ} {ε : ℕ → ℤ → Ω → ℝ}
    {M : ℝ} (hψ : SummableFamily ψ) (hε : ∀ j s ω, |ε j s ω| ≤ M)
    (hk : ∀ j (s : ℤ) (n : ℕ), s ≤ n → 𝔼.E n (ε j s) = ε j s) (n : ℕ) :
    𝔼.E n (compositeInf ψ ε n) = compositeInf ψ ε n := by
  have htype : ∀ j, 𝔼.E n (typeShock ψ ε j n) = typeShock ψ ε j n := by
    intro j
    funext ω
    have h := ForwardSolution.E_tsum_dom 𝔼 ((hψ.1 j).mul_right M)
      (f := fun k ω' => ψ j k * ε j ((n : ℤ) - k) ω') (fun k ω' => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hε j _ ω') (abs_nonneg _)) n ω
    change 𝔼.E n (fun ω' => ∑' k, ψ j k * ε j ((n : ℤ) - k) ω') ω = _
    rw [h]
    refine tsum_congr fun k => ?_
    have e : (fun ω' => ψ j k * ε j ((n : ℤ) - k) ω') = ψ j k • ε j ((n : ℤ) - k) := rfl
    rw [e, map_smul, hk j _ n (by omega)]
    rfl
  funext ω
  have h := ForwardSolution.E_tsum_dom 𝔼 (hψ.2.mul_right M)
    (f := fun j => typeShock ψ ε j n) (fun j ω' => typeShock_bdd hψ hε j n ω') n ω
  change 𝔼.E n (fun ω' => ∑' j, typeShock ψ ε j n ω') ω = _
  rw [h]
  exact tsum_congr fun j => by rw [htype j]


/-! ### Superposition and robust optimality of the target criterion -/

/-- **Superposition** (Woodford (2003), pp. 520–521): the forward component
`F_t = β⁻¹∑_i μ₂^{−i−1} E_t u_{t+i}` of the optimal plan for the composite disturbance is the
sum over shock types of the type-specific forward components (`κ, λ > 0`, `0 < β`). -/
theorem fwdU_composite (𝔼 : ExpectationSystem Ω) {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) {ψ : ℕ → ℕ → ℝ} {ε : ℕ → ℤ → Ω → ℝ} {M : ℝ} (hψ : SummableFamily ψ)
    (hε : ∀ j s ω, |ε j s ω| ≤ M) (t : ℕ) :
    TargetingRule.fwdU 𝔼 β κ lam (fun n => compositeInf ψ ε n) t =
      fun ω => ∑' j, TargetingRule.fwdU 𝔼 β κ lam (fun n => typeShock ψ ε j n) t ω := by
  funext ω
  rw [TargetingRule.fwdU_apply]
  simp_rw [TargetingRule.fwdU_apply]
  set m := SecondOrderRE.mu2 β (κ ^ 2 / lam) with hmdef
  have hm : 1 < m := SecondOrderRE.one_lt_mu2 hβ (by positivity)
  have hm0 : 0 < m := lt_trans one_pos hm
  have ha_eq : ∀ i : ℕ, (m ^ (i + 1))⁻¹ = m⁻¹ * (m⁻¹) ^ i := fun i => by
    rw [pow_succ, mul_inv, inv_pow]; ring
  have ha : Summable fun i : ℕ => (m ^ (i + 1))⁻¹ := by
    have := (summable_geometric_of_lt_one (inv_nonneg.mpr hm0.le)
      (inv_lt_one_of_one_lt₀ hm)).mul_left m⁻¹
    exact this.congr fun i => (ha_eq i).symm
  have ha0 : ∀ i : ℕ, 0 ≤ (m ^ (i + 1))⁻¹ := fun i => inv_nonneg.mpr (pow_nonneg hm0.le _)
  set e : ℕ → ℕ → ℝ := fun i j => 𝔼.E t (typeShock ψ ε j ((t + i : ℕ) : ℤ)) ω with he
  have heb : ∀ i j, |e i j| ≤ (∑' k, |ψ j k|) * M := fun i j =>
    𝔼.abs_E_le (fun ω' => typeShock_bdd hψ hε j _ ω') t ω
  have hE : ∀ i : ℕ, 𝔼.E t (compositeInf ψ ε ((t + i : ℕ) : ℤ)) ω = ∑' j, e i j := fun i =>
    ForwardSolution.E_tsum_dom 𝔼 (hψ.2.mul_right M)
      (f := fun j => typeShock ψ ε j ((t + i : ℕ) : ℤ)) (fun j ω' => typeShock_bdd hψ hε j _ ω')
      t ω
  simp_rw [hE]
  set g : ℕ → ℕ → ℝ := fun i j => (m ^ (i + 1))⁻¹ * e i j with hg
  have hgb : ∀ i j, ‖g i j‖ ≤ (m ^ (i + 1))⁻¹ * ((∑' k, |ψ j k|) * M) := fun i j => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 i)]
    exact mul_le_mul_of_nonneg_left (heb i j) (ha0 i)
  have hcs : Summable fun j => (∑' k, |ψ j k|) * M := hψ.2.mul_right M
  have hprod : Summable fun x : ℕ × ℕ => (m ^ (x.1 + 1))⁻¹ * ((∑' k, |ψ x.2 k|) * M) := by
    refine summable_mul_of_summable_norm (f := fun i : ℕ => (m ^ (i + 1))⁻¹)
      (g := fun j => (∑' k, |ψ j k|) * M) ?_ ?_
    · exact ha.congr fun i => by rw [Real.norm_eq_abs, abs_of_nonneg (ha0 i)]
    · exact (summable_abs_iff.mpr hcs).congr fun j => (Real.norm_eq_abs _).symm
  have hunc : Summable (Function.uncurry g) :=
    Summable.of_norm_bounded hprod fun x => hgb x.1 x.2
  have h1 : ∀ i, Summable (g i) := fun i =>
    Summable.of_norm_bounded (hcs.mul_left ((m ^ (i + 1))⁻¹)) fun j => hgb i j
  have h2 : ∀ j, Summable fun i => g i j := fun j =>
    Summable.of_norm_bounded (ha.mul_right ((∑' k, |ψ j k|) * M)) fun i => hgb i j
  have hswap := Summable.tsum_comm' hunc h1 h2
  have eL : (∑' i, (m ^ (i + 1))⁻¹ * ∑' j, e i j) = ∑' i, ∑' j, g i j :=
    tsum_congr fun i => by rw [← tsum_mul_left]
  rw [eL, ← hswap, ← tsum_mul_left]

/-- **The optimal equilibrium for a composite disturbance, type by type** (Woodford (2003),
pp. 520–521, (2.12) and (F.10)): along the equilibrium of the target criterion (5.1) for the
composite `u`, `x_t = μ₁x_{t−1} − (κ/λ)∑_j F^j_t` and
`π_t = (1 − μ₁)(λ/κ)x_{t−1} + ∑_j F^j_t`, with `F^j` the forward component of shock type `j`. -/
theorem star_composite (𝔼 : ExpectationSystem Ω) {β κ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hlam : 0 < lam) {ψ : ℕ → ℕ → ℝ} {ε : ℕ → ℤ → Ω → ℝ} {M : ℝ} (hψ : SummableFamily ψ)
    (hε : ∀ j s ω, |ε j s ω| ≤ M) (xm1 : Ω → ℝ) (t : ℕ) :
    TargetingRule.xStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n) t =
        SecondOrderRE.mu1 β (κ ^ 2 / lam) •
          Sequences.lagged xm1 (TargetingRule.xStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n))
            t -
          (κ / lam) • (fun ω => ∑' j, TargetingRule.fwdU 𝔼 β κ lam (fun n => typeShock ψ ε j n) t ω)
      ∧
      TargetingRule.piStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n) t =
        ((1 - SecondOrderRE.mu1 β (κ ^ 2 / lam)) * (lam / κ)) •
          Sequences.lagged xm1 (TargetingRule.xStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n))
            t +
          (fun ω => ∑' j, TargetingRule.fwdU 𝔼 β κ lam (fun n => typeShock ψ ε j n) t ω) := by
  rw [TargetingRule.xStar_eq, TargetingRule.piStar_eq 𝔼 hκ.ne' hlam.ne',
    fwdU_composite 𝔼 hβ hκ hlam hψ hε t]
  exact ⟨rfl, rfl⟩

/-- **Robust optimality of the target criterion for infinitely many shock types** (Woodford
(2003), p. 521, and Proposition 7.15, p. 523): for every absolutely summable family of weights
and every bounded shock histories known from their dates on, with the composite cost-push
disturbance (4.3), the target criterion (5.1) — whose coefficient `λ/κ` does not depend on the
weights — has exactly one bounded adapted equilibrium with (2.1), and that equilibrium solves the
optimal-policy problem of Proposition 7.7 (initial constraint (2.11)), for any target `x*`
(pull-out property assumed). -/
theorem targeting_rule_composite (𝔼 : ExpectationSystem Ω) (hpo : 𝔼.PullOut) {β κ lam : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hlam : 0 < lam) {ψ : ℕ → ℕ → ℝ}
    {ε : ℕ → ℤ → Ω → ℝ} {M : ℝ} (hψ : SummableFamily ψ) (hε : ∀ j s ω, |ε j s ω| ≤ M)
    (hk : ∀ j (s : ℤ) (n : ℕ), s ≤ n → 𝔼.E n (ε j s) = ε j s) {xm1 : Ω → ℝ} {K : ℝ}
    (hK : ∀ ω, |xm1 ω| ≤ K) (hm0 : 𝔼.E 0 xm1 = xm1) :
    (VarianceFrontier.AS 𝔼 β κ (fun n => compositeInf ψ ε n)
        (TargetingRule.piStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n))
        (TargetingRule.xStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n)) ∧
      TargetingRule.Crit lam κ xm1
        (TargetingRule.piStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n))
        (TargetingRule.xStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n))) ∧
    (∀ π x : ℕ → Ω → ℝ, VarianceFrontier.AS 𝔼 β κ (fun n => compositeInf ψ ε n) π x →
      TargetingRule.Crit lam κ xm1 π x → BoundedProc x → 𝔼.Adapted x →
      π = TargetingRule.piStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n) ∧
        x = TargetingRule.xStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n)) ∧
    ∀ xs : ℝ, TargetingRule.IsConstrainedOpt 𝔼 β κ lam xs (fun n => compositeInf ψ ε n)
      (TargetingRule.eq211 𝔼 β κ lam (fun n => compositeInf ψ ε n) xm1)
      (TargetingRule.piStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n))
      (TargetingRule.xStar 𝔼 β κ lam xm1 (fun n => compositeInf ψ ε n)) := by
  have hub : BoundedProc (fun n : ℕ => compositeInf ψ ε n) :=
    ⟨_, fun n ω => compositeInf_bdd hψ hε n ω⟩
  have hua : 𝔼.Adapted (fun n : ℕ => compositeInf ψ ε n) :=
    fun n => compositeInf_adapted 𝔼 hψ hε hk n
  obtain ⟨⟨hAS, hC, hpb, hxb, hpa, hxa⟩, huniq⟩ :=
    TargetingRule.prop_7_15 𝔼 hβ hκ hlam hub hua hK hm0
  exact ⟨⟨hAS, hC⟩, huniq, fun xs => TargetingRule.crit_isConstrainedOpt 𝔼 hβ hβ1 hκ hlam hpo
    xs hub hua hK hm0 hAS hC hpb hxb hpa hxa⟩

end Woodford.GainsFromCommitment.TidyR5CompositeShocks
