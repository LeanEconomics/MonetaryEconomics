/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NeoWicksellianFramework.InflationDeterminants
import NeoWicksellianFramework.Determinacy2Forward
import NeoWicksellianFramework.ExpectationsFiniteTree

/-!
# Inflation targeting rules

Woodford (2003), *Interest and Prices*, Chapter 4, §2.6, pp. 290–295. All equations hold for an
arbitrary `ExpectationSystem`.

## Main results

* **(2.40)** strict inflation targeting: `strict_targeting_iff` (the target forces `x_t = x̄` and
  `î_t = r̂ⁿ_t + π̄`), `strict_targeting_existsUnique` (determinate: exactly one solution, with no
  boundedness restriction needed); **(2.42)** as a commitment: `inflation_path_existsUnique`.
* **(2.41)** `E_t π_{t+k} = π̄` (`k ≥ 1`): `ForecastTarget`; `forecastTarget_consequences`
  (`E_t x_{t+k} = x̄`, `E_t î_{t+k} = E_t r̂ⁿ_{t+k} + π̄` in every equilibrium);
  `forecastTarget_iff` (the equilibria are exactly `π = π̄ + u` with `E_t u_{t+k} = 0`, `x` and `î`
  then determined); `forecastTarget_construct`; `forecastTarget_continuum` (a continuum
  `c ↦ π̄ + c u` of distinct bounded equilibria), `forecastTarget_not_countable`; examples
  `forecastTarget_indeterminate` (every expectation system: `u_t = c·1[t = 0]`) and
  `coin_forecastTarget_indeterminate` (a finite event tree with genuinely random `u`);
  with inflation inertia (2.36): `forecastTarget_construct_inertia`.
* The zero lower bound (pp. 291–292): `ZLB`, `zlb_iff_log`; strict targeting: an equilibrium
  respecting the bound exists iff `r̂ⁿ + π̄ ≥ î_lb` (`strict_targeting_zlb_iff`); (2.42) as a
  commitment: iff its implied rate (`impliedRate`) respects the bound (`inflation_path_zlb_iff`);
  (2.41): `π̄` must be high, `E_t r̂ⁿ_{t+k} + π̄ ≥ î_lb` (`forecastTarget_zlb_necessary`), and with
  slack there are uncountably many ZLB-respecting equilibria (`forecastTarget_zlb_not_countable`;
  with inflation inertia (2.36): `forecastTarget_inertia_zlb_not_countable`).
* **(2.43)**: `eq_243_iff`.
* **(2.44)**: `Rule244`, `rule244_iff` (given (2.43), `π_t = π̄ ⟺` (2.44) at date `t`),
  `rule244_iff_target`, `rule244_existsUnique` (the reaction function determines the unique
  equilibrium `π ≡ π̄`, for all parameter values).
* Coefficients: `rule244_phiPi`, `rule244_phiX`, `ForwardRuleCondition` ((2.11)),
  `rule244_taylorPrinciple` ((2.7)), `rule244_condition211` ((2.11), not proved in the book),
  `rule244_coefficients`.
-/

namespace Woodford.NeoWicksellianFramework.TargetingRules

open Woodford.NeoWicksellianFramework.InflationDeterminants
open BasicModel (IS112 NKPCurve xbar)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Strict inflation targeting (2.40) -/

/-- Woodford (2003), eq. (2.40), p. 290: the target criterion `π_t = π̄` at every date. -/
def StrictTarget (πbar : ℝ) (π : ℕ → Ω → ℝ) : Prop := ∀ t, π t = fun _ => πbar

/-- **Woodford (2003), p. 291.** Under (1.12), (1.13), the target criterion (2.40) holds iff
`π_t = π̄`, `x_t = x̄` and `î_t = r̂ⁿ_t + π̄` at every date. -/
theorem strict_targeting_iff {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    {π x i rn : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn) :
    StrictTarget πbar π ↔ (∀ t, π t = fun _ => πbar) ∧
      (∀ t, x t = fun _ => xbar β κ πbar) ∧ ∀ t, i t = rn t + fun _ => πbar := by
  constructor
  · intro h
    have hx : ∀ t, x t = fun _ => xbar β κ πbar := by
      intro t
      funext ω
      have := congrFun (has t) ω
      rw [h t, h (t + 1), 𝔼.const] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      unfold xbar
      field_simp
      linarith
    refine ⟨h, hx, fun t => ?_⟩
    funext ω
    have := congrFun (his t) ω
    rw [hx t, hx (t + 1), h (t + 1), 𝔼.const, 𝔼.const] at this
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    have h2 : σ * (i t ω - πbar - rn t ω) = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hσ
    · simp only [Pi.add_apply]
      linarith
  · exact fun h => h.1

/-- **Woodford (2003), p. 291 (determinacy of strict targeting).** Under (1.12), (1.13) and (2.40)
there is exactly one solution `(π, x, î)` — no boundedness restriction is needed — namely
`π ≡ π̄`, `x ≡ x̄`, `î = r̂ⁿ + π̄`. -/
theorem strict_targeting_existsUnique {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (rn : ℕ → Ω → ℝ) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      NKPCurve 𝔼 β κ p.1 p.2.1 ∧ IS112 𝔼 σ p.2.1 p.2.2 p.1 rn ∧ StrictTarget πbar p.1 := by
  refine ⟨(fun _ _ => πbar, fun _ _ => xbar β κ πbar, fun t => rn t + fun _ => πbar),
    ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩, ?_⟩
  · funext ω
    simp only [𝔼.const, Pi.add_apply, Pi.smul_apply, smul_eq_mul, xbar]
    field_simp
    ring
  · funext ω
    simp only [𝔼.const, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring
  · rintro ⟨π, x, i⟩ ⟨has, his, ht⟩
    dsimp only at has his ht
    obtain ⟨h1, h2, h3⟩ := (strict_targeting_iff 𝔼 hκ hσ has his).mp ht
    simp only [Prod.mk.injEq]
    exact ⟨funext h1, funext h2, funext h3⟩

/-- **Woodford (2003), eq. (2.42), p. 291 (as a commitment).** If policy commits to the path
`π_t = π̄ + u_t` for a given process `u`, (1.12)–(1.13) determine `x` and `î` uniquely:
`κ x_t = π_t − β E_t π_{t+1}` and `σ î_t = σ(r̂ⁿ_t + E_t π_{t+1}) + E_t x_{t+1} − x_t`. -/
theorem inflation_path_existsUnique {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (rn u : ℕ → Ω → ℝ) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      NKPCurve 𝔼 β κ p.1 p.2.1 ∧ IS112 𝔼 σ p.2.1 p.2.2 p.1 rn ∧
        ∀ t, p.1 t = (fun _ => πbar) + u t := by
  set π : ℕ → Ω → ℝ := fun t => (fun _ => πbar) + u t with hπ
  set x : ℕ → Ω → ℝ := fun t => κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1))) with hx
  set i : ℕ → Ω → ℝ := fun t => rn t + 𝔼.E t (π (t + 1)) +
    σ⁻¹ • (𝔼.E t (x (t + 1)) - x t) with hi
  refine ⟨(π, x, i), ⟨fun t => ?_, fun t => ?_, fun t => rfl⟩, ?_⟩
  · funext ω
    simp only [hx, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · funext ω
    simp only [hi, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · rintro ⟨π', x', i'⟩ ⟨has, his, hp⟩
    dsimp only at has his hp
    have e1 : π' = π := funext hp
    have e2 : x' = x := by
      funext t ω
      have := congrFun (has t) ω
      rw [e1] at this
      simp only [hx, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
      field_simp
      linarith
    have e3 : i' = i := by
      funext t ω
      have := congrFun (his t) ω
      rw [e1, e2] at this
      simp only [hi, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
      field_simp
      linarith
    rw [e1, e2, e3]

/-! ### Targeting a `k`-period-ahead forecast (2.41)–(2.42) -/

/-- Woodford (2003), eq. (2.41), p. 291: the target criterion `E_t π_{t+k} = π̄` at every date. -/
def ForecastTarget (k : ℕ) (πbar : ℝ) (π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, 𝔼.E t (π (t + k)) = fun _ => πbar

/-- Woodford (2003), p. 291: `u` is not forecastable `k` periods ahead, `E_t u_{t+k} = 0`. -/
def Unforecastable (k : ℕ) (u : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (u (t + k)) = 0

/-- **Woodford (2003), p. 291.** In every solution of (1.12), (1.13), (2.41):
`E_t x_{t+k} = x̄` and `E_t î_{t+k} = E_t r̂ⁿ_{t+k} + π̄` (for every horizon `k`; the book takes
`k ≥ 1`). -/
theorem forecastTarget_consequences {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {k : ℕ}
    {π x i rn : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn)
    (hT : ForecastTarget 𝔼 k πbar π) (t : ℕ) :
    𝔼.E t (x (t + k)) = (fun _ => xbar β κ πbar) ∧
      𝔼.E t (i (t + k)) = 𝔼.E t (rn (t + k)) + fun _ => πbar := by
  have hπ1 : ∀ s, 𝔼.E s (π (s + k + 1)) = fun _ => πbar := by
    intro s
    rw [← 𝔼.tower (Nat.le_succ s), show s + k + 1 = s + 1 + k by omega, hT (s + 1), 𝔼.const]
  have hle : t ≤ t + k := Nat.le_add_right t k
  have hx : ∀ s, 𝔼.E s (x (s + k)) = fun _ => xbar β κ πbar := by
    intro s
    have h := congrArg (𝔼.E s) (has (s + k))
    rw [map_add, map_smul, map_smul, 𝔼.tower (Nat.le_add_right s k), hπ1 s, hT s] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    unfold xbar
    field_simp
    linarith
  refine ⟨hx t, ?_⟩
  have hx1 : 𝔼.E t (x (t + k + 1)) = fun _ => xbar β κ πbar := by
    rw [← 𝔼.tower (Nat.le_succ t), show t + k + 1 = t + 1 + k by omega, hx (t + 1), 𝔼.const]
  have h := congrArg (𝔼.E t) (his (t + k))
  rw [map_sub, map_smul, map_sub, map_sub, 𝔼.tower hle, 𝔼.tower hle, hx t, hx1, hπ1 t] at h
  funext ω
  have := congrFun h ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [Pi.add_apply]
  have h2 : σ * (𝔼.E t (i (t + k)) ω - πbar - 𝔼.E t (rn (t + k)) ω) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hσ
  · linarith

/-- **Woodford (2003), (2.42), p. 291 (the construction).** For any `k`-step unforecastable `u`,
`π_t = π̄ + u_t`, `κ x_t = π_t − β E_t π_{t+1}`,
`σ î_t = σ(r̂ⁿ_t + E_t π_{t+1}) + E_t x_{t+1} − x_t`
solve (1.12), (1.13) and the target criterion (2.41). -/
theorem forecastTarget_construct {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {k : ℕ}
    (rn u : ℕ → Ω → ℝ) (hu : Unforecastable 𝔼 k u) :
    let π : ℕ → Ω → ℝ := fun t => (fun _ => πbar) + u t
    let x : ℕ → Ω → ℝ := fun t => κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))
    let i : ℕ → Ω → ℝ := fun t => rn t + 𝔼.E t (π (t + 1)) + σ⁻¹ • (𝔼.E t (x (t + 1)) - x t)
    NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ ForecastTarget 𝔼 k πbar π := by
  intro π x i
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω
    simp only [x, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · funext ω
    simp only [i, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · simp only [π, map_add, 𝔼.const, hu t, add_zero]

/-- Woodford (2003), (2.42), p. 291: the constructed equilibrium is adapted and bounded when `u`
and `r̂ⁿ` are. -/
theorem forecastTarget_construct_bounded {β σ κ πbar : ℝ} {rn u : ℕ → Ω → ℝ}
    (hua : 𝔼.Adapted u) (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hrb : BoundedProc rn) :
    let π : ℕ → Ω → ℝ := fun t => (fun _ => πbar) + u t
    let x : ℕ → Ω → ℝ := fun t => κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))
    let i : ℕ → Ω → ℝ := fun t => rn t + 𝔼.E t (π (t + 1)) + σ⁻¹ • (𝔼.E t (x (t + 1)) - x t)
    𝔼.Adapted π ∧ 𝔼.Adapted x ∧ 𝔼.Adapted i ∧ BoundedProc π ∧ BoundedProc x ∧
      BoundedProc i := by
  intro π x i
  obtain ⟨Mu, hMu⟩ := hub
  obtain ⟨Mr, hMr⟩ := hrb
  have hπa : 𝔼.Adapted π := fun t => by simp [π, map_add, 𝔼.const, hua t]
  have hxa : 𝔼.Adapted x := fun t => by
    simp only [x, map_smul, map_sub, hπa t, 𝔼.E_E_self]
  have hia : 𝔼.Adapted i := fun t => by
    simp only [i, map_add, map_smul, map_sub, hra t, 𝔼.E_E_self, hxa t]
  have hπb : ∀ t ω, |π t ω| ≤ |πbar| + Mu := fun t ω => by
    simp only [π, Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hMu t ω))
  have hEπ : ∀ s t ω, |𝔼.E s (π t) ω| ≤ |πbar| + Mu := fun s t ω => 𝔼.abs_E_le (hπb t) s ω
  have hxb : ∀ t ω, |x t ω| ≤ |κ⁻¹| * ((|πbar| + Mu) + |β| * (|πbar| + Mu)) := fun t ω => by
    simp only [x, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    gcongr
    refine (abs_sub _ _).trans (add_le_add (hπb t ω) ?_)
    rw [abs_mul]
    gcongr
    exact hEπ t (t + 1) ω
  have hEx : ∀ s t ω, |𝔼.E s (x t) ω| ≤ |κ⁻¹| * ((|πbar| + Mu) + |β| * (|πbar| + Mu)) :=
    fun s t ω => 𝔼.abs_E_le (hxb t) s ω
  refine ⟨hπa, hxa, hia, ⟨_, hπb⟩, ⟨_, hxb⟩, ⟨Mr + (|πbar| + Mu) +
    |σ⁻¹| * (2 * (|κ⁻¹| * ((|πbar| + Mu) + |β| * (|πbar| + Mu)))), fun t ω => ?_⟩⟩
  simp only [i, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (hMr t ω) (hEπ t (t + 1) ω))) ?_)
  rw [abs_mul]
  gcongr
  refine (abs_sub _ _).trans ?_
  have := hEx t (t + 1) ω
  have := hxb t ω
  linarith

/-- **Woodford (2003), pp. 291–292 (characterisation).** For `k ≥ 1`, `(π, x, î)` solves (1.12),
(1.13), (2.41) iff `u = π − π̄` is unforecastable `k` periods ahead and `x`, `î` are the values
determined by (1.13), (1.12). So the equilibria are in one-to-one correspondence with such `u`. -/
theorem forecastTarget_iff {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {k : ℕ}
    {π x i rn : ℕ → Ω → ℝ} :
    (NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ ForecastTarget 𝔼 k πbar π) ↔
      (Unforecastable 𝔼 k (fun t => π t - fun _ => πbar) ∧
        (∀ t, x t = κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))) ∧
          ∀ t, i t = rn t + 𝔼.E t (π (t + 1)) + σ⁻¹ • (𝔼.E t (x (t + 1)) - x t)) := by
  constructor
  · rintro ⟨has, his, hT⟩
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
    · rw [map_sub, hT t, 𝔼.const, sub_self]
    · funext ω
      have := congrFun (has t) ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
      field_simp
      linarith
    · funext ω
      have := congrFun (his t) ω
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
      field_simp
      linarith
  · rintro ⟨hu, hx, hi⟩
    refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
    · funext ω
      rw [hx t]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    · funext ω
      rw [hi t]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
    · have := hu t
      rw [map_sub, 𝔼.const, sub_eq_zero] at this
      exact this

/-- **Woodford (2003), pp. 291–292 (indeterminacy of (2.41)).** If some bounded adapted `u` with
`E_t u_{t+k} = 0` is not identically zero, the family `c ↦ π̄ + c u` (`c ∈ ℝ`) gives pairwise
distinct bounded adapted equilibria of (1.12), (1.13), (2.41). -/
theorem forecastTarget_continuum {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {k : ℕ}
    {rn u : ℕ → Ω → ℝ} (hu : Unforecastable 𝔼 k u) (hua : 𝔼.Adapted u)
    (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hrb : BoundedProc rn) {t₀ : ℕ} {ω₀ : Ω}
    (hne : u t₀ ω₀ ≠ 0) :
    ∀ c : ℝ, ∃ x i : ℕ → Ω → ℝ,
      NKPCurve 𝔼 β κ (fun t => (fun _ => πbar) + c • u t) x ∧
        IS112 𝔼 σ x i (fun t => (fun _ => πbar) + c • u t) rn ∧
        ForecastTarget 𝔼 k πbar (fun t => (fun _ => πbar) + c • u t) ∧
        𝔼.Adapted x ∧ 𝔼.Adapted i ∧ BoundedProc x ∧ BoundedProc i ∧
        𝔼.Adapted (fun t => (fun _ => πbar) + c • u t) ∧
        BoundedProc (fun t => (fun _ => πbar) + c • u t) ∧
        ∀ c' : ℝ, (fun t => (fun _ => πbar) + c' • u t) =
          (fun t => (fun _ => πbar) + c • u t) → c' = c := by
  intro c
  have hcu : Unforecastable 𝔼 k (fun t => c • u t) := fun t => by rw [map_smul, hu t, smul_zero]
  have hcua : 𝔼.Adapted (fun t => c • u t) := fun t => by rw [map_smul, hua t]
  have hcub : BoundedProc (fun t => c • u t) := by
    obtain ⟨M, hM⟩ := hub
    refine ⟨|c| * M, fun t ω => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)
  obtain ⟨has, his, hT⟩ := forecastTarget_construct 𝔼 (πbar := πbar) (β := β) hκ hσ rn _ hcu
  obtain ⟨hπa, hxa, hia, hπb, hxb, hib⟩ := forecastTarget_construct_bounded 𝔼 (πbar := πbar)
    (β := β) (κ := κ) (σ := σ) hcua hra hcub hrb
  refine ⟨_, _, has, his, hT, hxa, hia, hxb, hib, hπa, hπb, fun c' h => ?_⟩
  have := congrFun (congrFun h t₀) ω₀
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
  exact mul_right_cancel₀ hne this

/-- **Woodford (2003), p. 292.** Hence, if a non-trivial bounded adapted `u` with `E_t u_{t+k} = 0`
exists, the set of bounded adapted equilibrium inflation paths under (2.41) is uncountable. -/
theorem forecastTarget_not_countable {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {k : ℕ}
    {rn u : ℕ → Ω → ℝ} (hu : Unforecastable 𝔼 k u) (hua : 𝔼.Adapted u)
    (hra : 𝔼.Adapted rn) (hub : BoundedProc u) (hrb : BoundedProc rn) {t₀ : ℕ} {ω₀ : Ω}
    (hne : u t₀ ω₀ ≠ 0) :
    ¬ {π : ℕ → Ω → ℝ | ∃ x i, NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ ForecastTarget 𝔼 k πbar π ∧
      𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x}.Countable := by
  intro hcount
  have hC := forecastTarget_continuum 𝔼 (β := β) (σ := σ) (κ := κ) (πbar := πbar) hκ hσ hu hua
    hra hub hrb hne
  have hmaps : Set.MapsTo (fun c : ℝ => fun t => (fun _ => πbar) + c • u t) Set.univ
      {π : ℕ → Ω → ℝ | ∃ x i, NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ ForecastTarget 𝔼 k πbar π ∧
        𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x} := by
    intro c _
    obtain ⟨x, i, has, his, hT, hxa, -, hxb, -, hπa, hπb, -⟩ := hC c
    exact ⟨x, i, has, his, hT, hπa, hxa, hπb, hxb⟩
  have hinj : Set.InjOn (fun c : ℝ => fun t => (fun _ => πbar) + c • u t) Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hinj⟩ := hC c₂
    exact hinj c₁ h
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Woodford (2003), p. 291 (an unforecastable process in every expectation system): `u_t = c`
at `t = 0` and `0` afterwards satisfies `E_t u_{t+k} = 0` for `k ≥ 1`. -/
theorem initial_unforecastable {k : ℕ} (hk : 1 ≤ k) (c : ℝ) :
    Unforecastable 𝔼 k (fun t => if t = 0 then (fun _ => c) else 0) := by
  intro t
  have : ¬ (t = 0 ∧ k = 0) := by omega
  simp [this]

/-- **Woodford (2003), pp. 291–292 (indeterminacy for every expectation system).** For every
`ExpectationSystem` on a nonempty state space (perfect foresight included), every `k ≥ 1` and
every bounded adapted `r̂ⁿ`, the bounded adapted equilibria of (1.12), (1.13), (2.41) form an
uncountable set: the date-0 inflation rate is not pinned down. -/
theorem forecastTarget_indeterminate [Nonempty Ω] {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    {k : ℕ} (hk : 1 ≤ k) {rn : ℕ → Ω → ℝ} (hra : 𝔼.Adapted rn) (hrb : BoundedProc rn) :
    ¬ {π : ℕ → Ω → ℝ | ∃ x i, NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ ForecastTarget 𝔼 k πbar π ∧
      𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x}.Countable := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  refine forecastTarget_not_countable 𝔼 hκ hσ (initial_unforecastable 𝔼 hk 1) (fun t => ?_)
    hra ⟨1, fun t ω => ?_⟩ hrb (t₀ := 0) (ω₀ := ω₀) (by simp)
  · by_cases h : t = 0
    · simp [h, 𝔼.const]
    · simp [h]
  · by_cases h : t = 0 <;> simp [h]

/-- Woodford (2003), p. 291 (a genuinely random unforecastable process): in the two-coin event
tree, the mean-zero shock `ε_t` (`±1` at dates 1 and 2) satisfies `E_t ε_{t+k} = 0` for every
`k ≥ 1`. -/
theorem coinShock_unforecastable {k : ℕ} (hk : 1 ≤ k) :
    Unforecastable ExpectationsFiniteTree.coinSystem k ExpectationsFiniteTree.coinShock := by
  intro t
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [← ExpectationsFiniteTree.coinSystem.tower (Nat.le_add_right t m),
    show t + (m + 1) = t + m + 1 by omega, ExpectationsFiniteTree.coinShock_mean_zero,
    map_zero]

/-- Woodford (2003), p. 291: the coin-tree shock is adapted. -/
theorem coinShock_adapted :
    ExpectationsFiniteTree.coinSystem.Adapted ExpectationsFiniteTree.coinShock := by
  intro t
  funext ω
  rw [ExpectationsFiniteTree.coinSystem, ExpectationsFiniteTree.FiniteTree.toExpectationSystem_E]
  exact ExpectationsFiniteTree.coinTree.condE_of_const_on_cell fun ω' h =>
    ExpectationsFiniteTree.coinShock_measurable t h

/-- **Woodford (2003), pp. 291–292 (indeterminacy under genuine uncertainty).** In the two-coin
event tree, for every `k ≥ 1` the paths `π_t = π̄ + c ε_t` (`ε` the coin shock, random at dates
1 and 2) are equilibria of (1.12), (1.13), (2.41) for every `c ∈ ℝ` (with `r̂ⁿ = 0`), and the set
of bounded adapted equilibrium inflation paths is uncountable. -/
theorem coin_forecastTarget_indeterminate {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {k : ℕ}
    (hk : 1 ≤ k) :
    ¬ {π : ℕ → Bool × Bool → ℝ | ∃ x i, NKPCurve ExpectationsFiniteTree.coinSystem β κ π x ∧
      IS112 ExpectationsFiniteTree.coinSystem σ x i π 0 ∧
      ForecastTarget ExpectationsFiniteTree.coinSystem k πbar π ∧
      ExpectationsFiniteTree.coinSystem.Adapted π ∧ ExpectationsFiniteTree.coinSystem.Adapted x ∧
      BoundedProc π ∧ BoundedProc x}.Countable := by
  refine forecastTarget_not_countable ExpectationsFiniteTree.coinSystem hκ hσ
    (coinShock_unforecastable hk) coinShock_adapted (fun t => by simp) ⟨1, fun t ω => ?_⟩
    ⟨0, fun t ω => by simp⟩ (t₀ := 1) (ω₀ := (true, true))
    (by simp [ExpectationsFiniteTree.coinShock])
  unfold ExpectationsFiniteTree.coinShock
  split_ifs <;> simp

/-- **Woodford (2003), p. 292 (with inflation inertia (2.36)).** The indeterminacy of (2.41) does
not depend on the Phillips curve being purely forward-looking: for any `k`-step unforecastable
`u`, `π_t = π̄ + u_t`, `κ x_t = π_t − γ π_{t−1} − β E_t(π_{t+1} − γ π_t)` and the `î` given by
(1.12)
solve (1.12), (2.36), (2.41). -/
theorem forecastTarget_construct_inertia {β σ κ γ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {k : ℕ}
    (p0 : Ω → ℝ) (rn u : ℕ → Ω → ℝ) (hu : Unforecastable 𝔼 k u) :
    let π : ℕ → Ω → ℝ := fun t => (fun _ => πbar) + u t
    let x : ℕ → Ω → ℝ := fun t => κ⁻¹ • (π t - γ • lagPi p0 π t -
      β • 𝔼.E t (π (t + 1) - γ • π t))
    let i : ℕ → Ω → ℝ := fun t => rn t + 𝔼.E t (π (t + 1)) + σ⁻¹ • (𝔼.E t (x (t + 1)) - x t)
    ASInertia 𝔼 β κ γ p0 π x ∧ IS112 𝔼 σ x i π rn ∧ ForecastTarget 𝔼 k πbar π := by
  intro π x i
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · funext ω
    simp only [x, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · funext ω
    simp only [i, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  · simp only [π, map_add, 𝔼.const, hu t, add_zero]

/-! ### The zero lower bound (pp. 291–292) -/

/-- Woodford (2003), pp. 291–292: the zero lower bound in the log-linear variables,
`î_t ≥ î_lb` at every date and state (with `î_t = log((1 + i_t)/(1 + ī))` and the zero-inflation
steady state `1 + ī = β⁻¹`, `i_t ≥ 0` is `î_t ≥ log β`, see `zlb_iff_log`). -/
def ZLB (ilb : ℝ) (i : ℕ → Ω → ℝ) : Prop := ∀ t ω, ilb ≤ i t ω

omit 𝔼 in
/-- Woodford (2003), p. 291: with `1 + ī = β⁻¹`, the nominal rate `i > −1` is nonnegative iff
its log deviation `log((1 + i)β)` is at least `log β`. -/
theorem zlb_iff_log {β i : ℝ} (hβ : 0 < β) (hi : -1 < i) :
    0 ≤ i ↔ Real.log β ≤ Real.log ((1 + i) * β) := by
  rw [Real.log_mul (by linarith) hβ.ne', le_add_iff_nonneg_left, Real.log_nonneg_iff (by linarith)]
  constructor <;> intro h <;> linarith

/-- **Woodford (2003), p. 291 (strict targeting and the ZLB).** Under (1.12), (1.13), (2.40) an
equilibrium respecting the lower bound `î ≥ î_lb` exists iff `r̂ⁿ_t + π̄ ≥ î_lb` at every date and
state (and it is then unique, `strict_targeting_existsUnique`). -/
theorem strict_targeting_zlb_iff {β σ κ πbar ilb : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (rn : ℕ → Ω → ℝ) :
    (∃ π x i : ℕ → Ω → ℝ, NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ StrictTarget πbar π ∧
      ZLB ilb i) ↔
      ∀ t ω, ilb ≤ rn t ω + πbar := by
  constructor
  · rintro ⟨π, x, i, has, his, ht, hz⟩ t ω
    obtain ⟨-, -, h3⟩ := (strict_targeting_iff 𝔼 hκ hσ has his).mp ht
    have := hz t ω
    rw [h3 t] at this
    simpa using this
  · intro h
    obtain ⟨⟨π, x, i⟩, ⟨has, his, ht⟩, -⟩ :=
      strict_targeting_existsUnique 𝔼 (β := β) (πbar := πbar) hκ hσ rn
    dsimp only at has his ht
    refine ⟨π, x, i, has, his, ht, fun t ω => ?_⟩
    obtain ⟨-, -, h3⟩ := (strict_targeting_iff 𝔼 hκ hσ has his).mp ht
    have e := congrFun (h3 t) ω
    simp only [Pi.add_apply] at e
    rw [e]
    exact h t ω

/-- Woodford (2003), p. 291: the output gap implied by an inflation path through (1.13),
`x_t = κ⁻¹(π_t − β E_t π_{t+1})`. -/
noncomputable def impliedGap (β κ : ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => κ⁻¹ • (π t - β • 𝔼.E t (π (t + 1)))

/-- Woodford (2003), p. 291: the interest rate implied by an inflation path through (1.12),
(1.13), `î_t = r̂ⁿ_t + E_t π_{t+1} + σ⁻¹(E_t x_{t+1} − x_t)` with `x` from `impliedGap`. -/
noncomputable def impliedRate (β σ κ : ℝ) (rn π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t + 𝔼.E t (π (t + 1)) +
    σ⁻¹ • (𝔼.E t (impliedGap 𝔼 β κ π (t + 1)) - impliedGap 𝔼 β κ π t)

/-- **Woodford (2003), p. 291 ((2.42) as a commitment, with the ZLB).** The inflation path
`π = π̄ + u` can be achieved in an equilibrium of (1.12), (1.13) respecting `î ≥ î_lb` iff the
interest rate it implies (`impliedRate`) satisfies the bound; the equilibrium is then unique
(`inflation_path_existsUnique`). -/
theorem inflation_path_zlb_iff {β σ κ πbar ilb : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    (rn u : ℕ → Ω → ℝ) :
    (∃ π x i : ℕ → Ω → ℝ, NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧
      (∀ t, π t = (fun _ => πbar) + u t) ∧ ZLB ilb i) ↔
      ZLB ilb (impliedRate 𝔼 β σ κ rn (fun t => (fun _ => πbar) + u t)) := by
  obtain ⟨⟨π, x, i⟩, ⟨has, his, hp⟩, huniq⟩ :=
    inflation_path_existsUnique 𝔼 (β := β) (πbar := πbar) hκ hσ rn u
  dsimp only at has his hp
  have e1 : π = fun t => (fun _ => πbar) + u t := funext hp
  have e2 : x = impliedGap 𝔼 β κ π := by
    funext t ω
    have := congrFun (has t) ω
    simp only [impliedGap, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this ⊢
    field_simp
    linarith
  have hi : i = impliedRate 𝔼 β σ κ rn (fun t => (fun _ => πbar) + u t) := by
    funext t ω
    have := congrFun (his t) ω
    rw [← e1]
    simp only [impliedRate, ← e2, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul] at this ⊢
    field_simp
    linarith
  constructor
  · rintro ⟨π', x', i', has', his', hp', hz⟩
    have := huniq (π', x', i') ⟨has', his', hp'⟩
    simp only [Prod.mk.injEq] at this
    rw [← hi, ← this.2.2]
    exact hz
  · intro hz
    exact ⟨π, x, i, has, his, hp, by rw [hi]; exact hz⟩

/-- Woodford (2003), p. 291: the implied interest rate is affine in the inflation path:
for `π = π̄ + c u`, `î_t = r̂ⁿ_t + π̄ + c · î^u_t`, where `î^u` is the rate implied by `u` alone
(with `r̂ⁿ = 0`). -/
theorem impliedRate_affine (β σ κ πbar c : ℝ) (rn u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    impliedRate 𝔼 β σ κ rn (fun t => (fun _ => πbar) + c • u t) t ω =
      rn t ω + πbar + c * impliedRate 𝔼 β σ κ 0 u t ω := by
  simp only [impliedRate, impliedGap, map_add, map_sub, map_smul, 𝔼.const, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  ring

/-- Woodford (2003), p. 291: the rate implied by a bounded `u` (`|u| ≤ M`) is bounded by
`M + 2|σ⁻¹||κ⁻¹|(1 + |β|)M`. -/
theorem impliedRate_bound {β σ κ M : ℝ} {u : ℕ → Ω → ℝ} (hM : ∀ t ω, |u t ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    |impliedRate 𝔼 β σ κ 0 u t ω| ≤ M + |σ⁻¹| * (2 * (|κ⁻¹| * (M + |β| * M))) := by
  have hx : ∀ s ω', |impliedGap 𝔼 β κ u s ω'| ≤ |κ⁻¹| * (M + |β| * M) := fun s ω' => by
    simp only [impliedGap, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    gcongr
    refine (abs_sub _ _).trans (add_le_add (hM s ω') ?_)
    rw [abs_mul]
    gcongr
    exact 𝔼.abs_E_le (hM (s + 1)) s ω'
  simp only [impliedRate, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul,
    zero_add]
  refine (abs_add_le _ _).trans (add_le_add (𝔼.abs_E_le (hM (t + 1)) t ω) ?_)
  rw [abs_mul]
  gcongr
  refine (abs_sub _ _).trans ?_
  have := 𝔼.abs_E_le (hx (t + 1)) t ω
  have := hx t ω
  linarith

/-- **Woodford (2003), pp. 291–292 ("in the generic case ... an infinite number of processes
{u_t} in which the fluctuations are modest enough").** If `π̄` is high enough that the constant
equilibrium respects the bound with slack, `r̂ⁿ_t + π̄ ≥ î_lb + δ` (`δ > 0`), then for any
non-trivial bounded adapted `u` with `E_t u_{t+k} = 0` the equilibria `π = π̄ + c u` with `|c|`
small respect `î ≥ î_lb`: the set of bounded adapted equilibrium inflation paths of (2.41) that
respect the ZLB is uncountable. -/
theorem forecastTarget_zlb_not_countable {β σ κ πbar ilb δ : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    {k : ℕ} {rn u : ℕ → Ω → ℝ} (hu : Unforecastable 𝔼 k u) (hua : 𝔼.Adapted u)
    (hub : BoundedProc u) {t₀ : ℕ} {ω₀ : Ω} (hne : u t₀ ω₀ ≠ 0) (hδ : 0 < δ)
    (hslack : ∀ t ω, ilb + δ ≤ rn t ω + πbar) :
    ¬ {π : ℕ → Ω → ℝ | ∃ x i, NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ ForecastTarget 𝔼 k πbar π ∧
      𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x ∧ ZLB ilb i}.Countable := by
  obtain ⟨M, hM⟩ := hub
  set Mi := M + |σ⁻¹| * (2 * (|κ⁻¹| * (M + |β| * M))) with hMi
  have hMi0 : 0 ≤ Mi := (abs_nonneg _).trans (impliedRate_bound 𝔼 (σ := σ) (κ := κ) hM 0 ω₀)
  set r := δ / (Mi + 1) with hr
  have hr0 : 0 < r := by positivity
  intro hcount
  have hmaps : Set.MapsTo (fun c : ℝ => fun t => (fun _ => πbar) + c • u t) (Set.Ioo (-r) r)
      {π : ℕ → Ω → ℝ | ∃ x i, NKPCurve 𝔼 β κ π x ∧ IS112 𝔼 σ x i π rn ∧ ForecastTarget 𝔼 k πbar π ∧
        𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x ∧ ZLB ilb i} := by
    intro c hc
    have hcu : Unforecastable 𝔼 k (fun t => c • u t) := fun t => by
      rw [map_smul, hu t, smul_zero]
    have hcua : 𝔼.Adapted (fun t => c • u t) := fun t => by rw [map_smul, hua t]
    have hcub : BoundedProc (fun t => c • u t) := by
      refine ⟨|c| * M, fun t ω => ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)
    obtain ⟨has, his, hT⟩ := forecastTarget_construct 𝔼 (πbar := πbar) (β := β) hκ hσ rn _ hcu
    obtain ⟨hπa, hxa, -, hπb, hxb, -⟩ := forecastTarget_construct_bounded 𝔼 (πbar := πbar)
      (β := β) (κ := κ) (σ := σ) (rn := 0) hcua (fun t => by simp) hcub ⟨0, fun _ _ => by simp⟩
    refine ⟨impliedGap 𝔼 β κ (fun t => (fun _ => πbar) + c • u t),
      impliedRate 𝔼 β σ κ rn (fun t => (fun _ => πbar) + c • u t), has, his, hT, hπa, hxa, hπb,
      hxb, fun t ω => ?_⟩
    rw [impliedRate_affine]
    have hb := impliedRate_bound 𝔼 (σ := σ) (κ := κ) (β := β) hM t ω
    have hcv : |c * impliedRate 𝔼 β σ κ 0 u t ω| ≤ δ := by
      rw [abs_mul]
      have hc' : |c| ≤ r := by rw [abs_le]; exact ⟨hc.1.le, hc.2.le⟩
      calc |c| * |impliedRate 𝔼 β σ κ 0 u t ω| ≤ r * Mi := mul_le_mul hc' hb (abs_nonneg _) hr0.le
        _ ≤ δ := by
          rw [hr, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
    have := neg_abs_le (c * impliedRate 𝔼 β σ κ 0 u t ω)
    linarith [hslack t ω]
  have hinj : Set.InjOn (fun c : ℝ => fun t => (fun _ => πbar) + c • u t) (Set.Ioo (-r) r) := by
    intro c₁ _ c₂ _ h
    have := congrFun (congrFun h t₀) ω₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
    exact mul_right_cancel₀ hne this
  have := hmaps.countable_of_injOn hinj hcount
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real (by linarith : -r < r)] at this
  exact absurd Cardinal.aleph0_lt_continuum (not_lt.mpr this)

/-- Woodford (2003), p. 292: the output gap implied by an inflation path through (2.36),
`x_t = κ⁻¹(π_t − γπ_{t−1} − β E_t(π_{t+1} − γπ_t))`. -/
noncomputable def impliedGapG (β κ γ : ℝ) (p0 : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => κ⁻¹ • (π t - γ • lagPi p0 π t - β • 𝔼.E t (π (t + 1) - γ • π t))

/-- Woodford (2003), p. 292: the interest rate implied by an inflation path through (1.12),
(2.36), with `x` from `impliedGapG`. -/
noncomputable def impliedRateG (β σ κ γ : ℝ) (p0 : Ω → ℝ) (rn π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => rn t + 𝔼.E t (π (t + 1)) +
    σ⁻¹ • (𝔼.E t (impliedGapG 𝔼 β κ γ p0 π (t + 1)) - impliedGapG 𝔼 β κ γ p0 π t)

omit 𝔼 in
/-- Woodford (2003), (2.36), p. 292: with `π_{−1} = π̄`, lagged inflation of `π̄ + c u` is
`π̄ + c` times lagged `u` (with `u_{−1} = 0`). -/
theorem lagPi_affine (πbar c : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    lagPi (fun _ => πbar) (fun t => (fun _ => πbar) + c • u t) t ω = πbar + c * lagPi 0 u t ω := by
  cases t with
  | zero => simp [lagPi]
  | succ t => simp [lagPi_succ]

/-- Woodford (2003), p. 292: with `π_{−1} = π̄`, the gap implied through (2.36) by `π̄ + c u` is
`x̄ + c` times the gap implied by `u` (with `u_{−1} = 0`). -/
theorem impliedGapG_affine (β κ γ πbar c : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    impliedGapG 𝔼 β κ γ (fun _ => πbar) (fun t => (fun _ => πbar) + c • u t) t ω =
      κ⁻¹ * ((1 - γ) * (1 - β) * πbar) + c * impliedGapG 𝔼 β κ γ 0 u t ω := by
  simp only [impliedGapG, map_add, map_sub, map_smul, 𝔼.const, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, lagPi_affine]
  ring

/-- Woodford (2003), p. 292: with `π_{−1} = π̄`, the rate implied through (1.12), (2.36) by
`π̄ + c u` is `r̂ⁿ + π̄ + c` times the rate implied by `u` alone. -/
theorem impliedRateG_affine (β σ κ γ πbar c : ℝ) (rn u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    impliedRateG 𝔼 β σ κ γ (fun _ => πbar) rn (fun t => (fun _ => πbar) + c • u t) t ω =
      rn t ω + πbar + c * impliedRateG 𝔼 β σ κ γ 0 0 u t ω := by
  have hE : ∀ s, 𝔼.E t (impliedGapG 𝔼 β κ γ (fun _ => πbar)
      (fun t => (fun _ => πbar) + c • u t) s) =
      (fun _ => κ⁻¹ * ((1 - γ) * (1 - β) * πbar)) + c • 𝔼.E t (impliedGapG 𝔼 β κ γ 0 u s) := by
    intro s
    rw [show impliedGapG 𝔼 β κ γ (fun _ => πbar) (fun t => (fun _ => πbar) + c • u t) s =
      (fun _ => κ⁻¹ * ((1 - γ) * (1 - β) * πbar)) + c • impliedGapG 𝔼 β κ γ 0 u s from
        funext fun ω' => impliedGapG_affine 𝔼 β κ γ πbar c u s ω', map_add, map_smul, 𝔼.const]
  simp only [impliedRateG, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hE,
    impliedGapG_affine, map_add, map_smul, 𝔼.const, Pi.zero_apply]
  ring

/-- Woodford (2003), p. 292: a bounded `u` (`|u| ≤ M`, `M ≥ 0`) implies, through (2.36), a gap
bounded by `X = |κ⁻¹|(M + |γ|M + |β|(M + |γ|M))`. -/
theorem impliedGapG_bound {β κ γ M : ℝ} {u : ℕ → Ω → ℝ} (hM : ∀ t ω, |u t ω| ≤ M)
    (t : ℕ) (ω : Ω) :
    |impliedGapG 𝔼 β κ γ 0 u t ω| ≤ |κ⁻¹| * (M + |γ| * M + |β| * (M + |γ| * M)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ω)
  have hlag : |lagPi 0 u t ω| ≤ M := by
    cases t with
    | zero => simpa [lagPi] using hM0
    | succ t => exact hM t ω
  have hin : ∀ ω', |(u (t + 1) - γ • u t) ω'| ≤ M + |γ| * M := fun ω' => by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans (add_le_add (hM _ _) ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _ _) (abs_nonneg _)
  simp only [impliedGapG, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
  gcongr
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hM t ω) ?_)) ?_)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlag (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le hin t ω) (abs_nonneg _)

/-- **Woodford (2003), p. 292 (the ZLB with inflation inertia (2.36)).** With `π_{−1} = π̄` and
the same slack `r̂ⁿ_t + π̄ ≥ î_lb + δ`, every non-trivial bounded adapted `u` with
`E_t u_{t+k} = 0` gives, for all small `|c|`, an equilibrium `π = π̄ + c u` of (1.12), (2.36),
(2.41) respecting `î ≥ î_lb`; the set of such bounded adapted equilibrium paths is uncountable. -/
theorem forecastTarget_inertia_zlb_not_countable {β σ κ γ πbar ilb δ : ℝ} (hκ : κ ≠ 0)
    (hσ : σ ≠ 0) {k : ℕ} {rn u : ℕ → Ω → ℝ} (hu : Unforecastable 𝔼 k u) (hua : 𝔼.Adapted u)
    (hub : BoundedProc u) {t₀ : ℕ} {ω₀ : Ω} (hne : u t₀ ω₀ ≠ 0) (hδ : 0 < δ)
    (hslack : ∀ t ω, ilb + δ ≤ rn t ω + πbar) :
    ¬ {π : ℕ → Ω → ℝ | ∃ x i, ASInertia 𝔼 β κ γ (fun _ => πbar) π x ∧ IS112 𝔼 σ x i π rn ∧
      ForecastTarget 𝔼 k πbar π ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧ BoundedProc x ∧
        ZLB ilb i}.Countable := by
  obtain ⟨M, hM⟩ := hub
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ω₀)
  set X := |κ⁻¹| * (M + |γ| * M + |β| * (M + |γ| * M)) with hX
  have hX0 : 0 ≤ X := by positivity
  set Mi := M + |σ⁻¹| * (2 * X) with hMi
  have hMi0 : 0 ≤ Mi := by positivity
  have hib : ∀ t ω, |impliedRateG 𝔼 β σ κ γ 0 0 u t ω| ≤ Mi := fun t ω => by
    simp only [impliedRateG, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply,
      smul_eq_mul, zero_add]
    refine (abs_add_le _ _).trans (add_le_add (𝔼.abs_E_le (hM (t + 1)) t ω) ?_)
    rw [abs_mul]
    gcongr
    refine (abs_sub _ _).trans ?_
    have := 𝔼.abs_E_le (impliedGapG_bound 𝔼 (β := β) (κ := κ) (γ := γ) hM (t + 1)) t ω
    have := impliedGapG_bound 𝔼 (β := β) (κ := κ) (γ := γ) hM t ω
    linarith
  set r := δ / (Mi + 1) with hr
  have hr0 : 0 < r := by positivity
  intro hcount
  have hmaps : Set.MapsTo (fun c : ℝ => fun t => (fun _ => πbar) + c • u t) (Set.Ioo (-r) r)
      {π : ℕ → Ω → ℝ | ∃ x i, ASInertia 𝔼 β κ γ (fun _ => πbar) π x ∧ IS112 𝔼 σ x i π rn ∧
        ForecastTarget 𝔼 k πbar π ∧ 𝔼.Adapted π ∧ 𝔼.Adapted x ∧ BoundedProc π ∧
          BoundedProc x ∧ ZLB ilb i} := by
    intro c hc
    have hcu : Unforecastable 𝔼 k (fun t => c • u t) := fun t => by
      rw [map_smul, hu t, smul_zero]
    obtain ⟨has, his, hT⟩ := forecastTarget_construct_inertia 𝔼 (πbar := πbar) (β := β)
      (γ := γ) hκ hσ (fun _ => πbar) rn _ hcu
    have hπa : 𝔼.Adapted (fun t => (fun _ => πbar) + c • u t) := fun t => by
      simp only [map_add, map_smul, 𝔼.const, hua t]
    have hxa : 𝔼.Adapted (impliedGapG 𝔼 β κ γ (fun _ => πbar)
        (fun t => (fun _ => πbar) + c • u t)) := fun t => by
      have hl := lagPiGap_adapted 𝔼 (p0 := fun _ => πbar) (𝔼.const 0 πbar) πbar hπa t
      rw [map_sub, 𝔼.const, sub_left_inj] at hl
      simp only [impliedGapG, map_smul, map_sub, hπa t, hl, 𝔼.E_E_self]
    refine ⟨impliedGapG 𝔼 β κ γ (fun _ => πbar) (fun t => (fun _ => πbar) + c • u t),
      impliedRateG 𝔼 β σ κ γ (fun _ => πbar) rn (fun t => (fun _ => πbar) + c • u t),
      has, his, hT, hπa, hxa, ⟨|πbar| + |c| * M, fun t ω => ?_⟩,
      ⟨|κ⁻¹ * ((1 - γ) * (1 - β) * πbar)| + |c| * X, fun t ω => ?_⟩, fun t ω => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg c)
    · rw [impliedGapG_affine]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (impliedGapG_bound 𝔼 hM t ω) (abs_nonneg c)
    · rw [impliedRateG_affine]
      have hcv : |c * impliedRateG 𝔼 β σ κ γ 0 0 u t ω| ≤ δ := by
        rw [abs_mul]
        have hc' : |c| ≤ r := by rw [abs_le]; exact ⟨hc.1.le, hc.2.le⟩
        calc |c| * |impliedRateG 𝔼 β σ κ γ 0 0 u t ω| ≤ r * Mi :=
              mul_le_mul hc' (hib t ω) (abs_nonneg _) hr0.le
          _ ≤ δ := by
            rw [hr, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
      have := neg_abs_le (c * impliedRateG 𝔼 β σ κ γ 0 0 u t ω)
      linarith [hslack t ω]
  have hinj : Set.InjOn (fun c : ℝ => fun t => (fun _ => πbar) + c • u t) (Set.Ioo (-r) r) := by
    intro c₁ _ c₂ _ h
    have := congrFun (congrFun h t₀) ω₀
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_right_inj] at this
    exact mul_right_cancel₀ hne this
  have := hmaps.countable_of_injOn hinj hcount
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real (by linarith : -r < r)] at this
  exact absurd Cardinal.aleph0_lt_continuum (not_lt.mpr this)

/-- **Woodford (2003), p. 291 ("if π̄ is chosen high enough for there to be any equilibria
consistent with (2.41)").** In every equilibrium of (1.12), (1.13), (2.41) respecting
`î ≥ î_lb`, `E_t r̂ⁿ_{t+k} + π̄ ≥ î_lb` at every date and state: `π̄` must be high relative to the
forecastable part of the natural rate. -/
theorem forecastTarget_zlb_necessary {β σ κ πbar ilb : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {k : ℕ}
    {π x i rn : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn)
    (hT : ForecastTarget 𝔼 k πbar π) (hz : ZLB ilb i) (t : ℕ) (ω : Ω) :
    ilb ≤ 𝔼.E t (rn (t + k)) ω + πbar := by
  have h := (forecastTarget_consequences 𝔼 hκ hσ has his hT t).2
  have hm := 𝔼.mono t (show (fun _ => ilb) ≤ i (t + k) from fun ω' => hz (t + k) ω')
  rw [𝔼.const, h] at hm
  simpa using hm ω

/-! ### The implementing reaction function (2.43)–(2.44) -/

/-- **Woodford (2003), eq. (2.43), p. 293.** Given the IS relation (1.12), the Phillips curve
(1.13) at date `t` is equivalent to
`π_t = (β + κσ) E_t π_{t+1} + κ E_t x_{t+1} − κσ (î_t − r̂ⁿ_t)`. -/
theorem eq_243_iff {β σ κ : ℝ} {π x i rn : ℕ → Ω → ℝ} (his : IS112 𝔼 σ x i π rn) (t : ℕ) :
    π t = κ • x t + β • 𝔼.E t (π (t + 1)) ↔
      π t = (β + κ * σ) • 𝔼.E t (π (t + 1)) + κ • 𝔼.E t (x (t + 1)) -
        (κ * σ) • (i t - rn t) := by
  have h := his t
  constructor
  · intro has
    funext ω
    have a := congrFun has ω
    have b := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    rw [a, b]
    ring
  · intro h243
    funext ω
    have a := congrFun h243 ω
    have b := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    rw [a, b]
    ring

/-- Woodford (2003), eq. (2.44), p. 293: the reaction function implementing (2.40),
`î_t = r̂ⁿ_t + π̄ + (1 + β/(κσ))(E_t π_{t+1} − π̄) + σ⁻¹(E_t x_{t+1} − x̄)`. -/
def Rule244 (β σ κ πbar : ℝ) (π x i rn : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  i t = rn t + (fun _ => πbar) + (1 + β / (κ * σ)) • (𝔼.E t (π (t + 1)) - fun _ => πbar) +
    σ⁻¹ • (𝔼.E t (x (t + 1)) - fun _ => xbar β κ πbar)

/-- **Woodford (2003), (2.43)–(2.44), p. 293.** If (2.43) holds at date `t` (the central bank's
correct structural model), then `π_t = π̄` iff the interest rate obeys (2.44) at `t`. -/
theorem rule244_iff {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) {π x i rn : ℕ → Ω → ℝ}
    {t : ℕ} (h243 : π t = (β + κ * σ) • 𝔼.E t (π (t + 1)) + κ • 𝔼.E t (x (t + 1)) -
      (κ * σ) • (i t - rn t)) :
    π t = (fun _ => πbar) ↔ Rule244 𝔼 β σ κ πbar π x i rn t := by
  unfold Rule244
  constructor
  · intro hπ
    funext ω
    have a := congrFun h243 ω
    have b := congrFun hπ ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    unfold xbar
    rw [b] at a
    field_simp
    linear_combination a
  · intro hr
    funext ω
    have a := congrFun h243 ω
    have b := congrFun hr ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
    unfold xbar at b
    rw [a, b]
    field_simp
    ring

/-- **Woodford (2003), p. 294.** Given the structural equations (1.12), (1.13), the target
criterion (2.40) and the reaction function (2.44) are equivalent specifications of policy. -/
theorem rule244_iff_target {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0)
    {π x i rn : ℕ → Ω → ℝ} (has : NKPCurve 𝔼 β κ π x) (his : IS112 𝔼 σ x i π rn) :
    StrictTarget πbar π ↔ ∀ t, Rule244 𝔼 β σ κ πbar π x i rn t :=
  ⟨fun h t => (rule244_iff 𝔼 hκ hσ ((eq_243_iff 𝔼 his t).mp (has t))).mp (h t),
    fun h t => (rule244_iff 𝔼 hκ hσ ((eq_243_iff 𝔼 his t).mp (has t))).mpr (h t)⟩

/-- **Woodford (2003), p. 294 ("a unique stationary solution, the r.e.e. in which inflation
equals π̄ at all times").** Under (1.12), (1.13), (2.44) there is exactly one solution, for every
`β, κ, σ` with `κ, σ ≠ 0` and without any boundedness restriction: `π ≡ π̄`, `x ≡ x̄`,
`î = r̂ⁿ + π̄`. -/
theorem rule244_existsUnique {β σ κ πbar : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) (rn : ℕ → Ω → ℝ) :
    ∃! p : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ),
      NKPCurve 𝔼 β κ p.1 p.2.1 ∧ IS112 𝔼 σ p.2.1 p.2.2 p.1 rn ∧
        ∀ t, Rule244 𝔼 β σ κ πbar p.1 p.2.1 p.2.2 rn t := by
  obtain ⟨p, ⟨has, his, ht⟩, huniq⟩ := strict_targeting_existsUnique 𝔼 (β := β) (πbar := πbar)
    hκ hσ rn
  refine ⟨p, ⟨has, his, (rule244_iff_target 𝔼 hκ hσ has his).mp ht⟩, ?_⟩
  rintro q ⟨has', his', hr'⟩
  exact huniq q ⟨has', his', (rule244_iff_target 𝔼 hκ hσ has' his').mpr hr'⟩

/-! ### The coefficients of (2.44) -/

/-- Woodford (2003), p. 294: the inflation coefficient of (2.44), `φ_π = 1 + β/(κσ)`. -/
noncomputable def rule244_phiPi (β σ κ : ℝ) : ℝ := 1 + β / (κ * σ)

/-- Woodford (2003), p. 294: the output-gap coefficient of (2.44) in the units of (1.14) and
(2.10) (`φ_x (x − x̄)/4`), `φ_x = 4/σ`. -/
noncomputable def rule244_phiX (σ : ℝ) : ℝ := 4 / σ

/-- Woodford (2003), eq. (2.11), p. 257: the second determinacy condition for the forward-looking
rule (2.10), `φ_π < 1 + (1 + β)(φ_x + 8σ⁻¹)/(4κ)` (the bound `Determinacy2Forward.fwdUpper` of
Proposition 4.5). -/
def ForwardRuleCondition (β σ κ φπ φx : ℝ) : Prop := φπ < Determinacy2Forward.fwdUpper β σ κ φx

omit 𝔼 in
/-- **Woodford (2003), p. 294.** The coefficients of (2.44) satisfy `φ_π > 1`, `φ_x > 0` and the
Taylor principle (2.7): `φ_π + (1 − β)φ_x/(4κ) = 1 + 1/(κσ) > 1`. -/
theorem rule244_taylorPrinciple {β σ κ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) :
    1 < rule244_phiPi β σ κ ∧ 0 < rule244_phiX σ ∧
      TaylorPrinciple β κ (rule244_phiPi β σ κ) (rule244_phiX σ) := by
  unfold rule244_phiPi rule244_phiX TaylorPrinciple
  have hb : 0 < β / (κ * σ) := by positivity
  refine ⟨by linarith, by positivity, ?_⟩
  have e : 1 + β / (κ * σ) + (1 - β) * (4 / σ) / (4 * κ) = 1 + 1 / (κ * σ) := by
    field_simp
    ring
  rw [e]
  have : 0 < 1 / (κ * σ) := by positivity
  linarith

omit 𝔼 in
/-- **Woodford (2003), p. 294 (new: the book asserts only the Taylor principle).** The
coefficients of (2.44) also satisfy (2.11) for all parameter values `0 < β`, `κ, σ > 0`:
the right side of (2.11) is `1 + 3(1 + β)/(κσ) > 1 + β/(κσ)`. -/
theorem rule244_condition211 {β σ κ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) :
    ForwardRuleCondition β σ κ (rule244_phiPi β σ κ) (rule244_phiX σ) := by
  unfold ForwardRuleCondition Determinacy2Forward.fwdUpper rule244_phiPi rule244_phiX
  have e : 1 + (1 + β) / (4 * κ) * (4 / σ + 8 * σ⁻¹) = 1 + 3 * (1 + β) / (κ * σ) := by
    field_simp
    ring
  rw [e]
  have : β / (κ * σ) < 3 * (1 + β) / (κ * σ) := by
    apply div_lt_div_of_pos_right _ (by positivity)
    linarith
  linarith

omit 𝔼 in
/-- Woodford (2003), p. 294: both determinacy conditions (2.7) and (2.11) of Prop. 4.5 hold for
the coefficients of the reaction function (2.44), for all `β, κ, σ > 0`. (The rule (2.44)
responds to `E_t x_{t+1}` rather than `x_t`, so it is not literally of the form (2.10); its
determinacy is proved directly in `rule244_existsUnique`.) -/
theorem rule244_coefficients {β σ κ : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ) (hσ : 0 < σ) :
    TaylorPrinciple β κ (rule244_phiPi β σ κ) (rule244_phiX σ) ∧
      ForwardRuleCondition β σ κ (rule244_phiPi β σ κ) (rule244_phiX σ) :=
  ⟨(rule244_taylorPrinciple hβ0 hκ hσ).2.2, rule244_condition211 hβ0 hκ hσ⟩

end Woodford.NeoWicksellianFramework.TargetingRules
