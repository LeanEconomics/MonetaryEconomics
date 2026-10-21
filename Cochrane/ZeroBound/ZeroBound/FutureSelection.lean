/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ZeroBound.ZLBRule

/-!
# Selection by expected future policy

Cochrane (2023), Chapter 20, §20.2.1, pp. 471–472 ("the expectation of future
equilibrium-selection policy can select equilibria even when policy is currently or locally
passive"), and Chapter 24, pp. 522–524 (Davig and Leeper: "If an economy is currently in what
looks like a passive-fiscal regime, but people expect a switch to what looks like an
active-fiscal regime, then that future active fiscal policy selects equilibria").

Everything holds for an arbitrary `ExpectationSystem`, with a deterministic switch date `T`.

## Main results

* `switch_scalar`: the engine. `c_t y_t = d E_t y_{t+1} + f_t` with `c_t ≠ 0` before `T` and
  `c_t = c_A`, `|d| < |c_A|` from `T` on has exactly one bounded adapted solution for every
  bounded adapted `f`. `bounded_of_rec` is the boundedness lemma used for recursions that are
  contracting after `T`.
* Monetary switch (§20.2.1): the frictionless model `E_tπ_{t+1} = φ_tπ_t + u_t` with ANY nonzero
  `φ_t` before `T` (e.g. passive `|φ_t| < 1`) and active `|φ_A| > 1` from `T` on has a unique
  bounded equilibrium (`future_selection`). Without the switch, passive policy leaves
  uncountably many (`passive_forever_not_unique`); the hypothesis `φ_t ≠ 0` cannot be dropped
  (`zero_coefficient_not_unique`: a pure peg before `T` leaves `π₀` free).
* Fiscal switch (Ch. 24, Leeper model (23.1)–(23.4) with time-varying `φ_t`, `γ_t`):
  passive fiscal policy (`γ_t ≠ 1`, any `φ_t`) before `T` and active fiscal / passive money
  (`γ = 0`, `|φ_P| < 1`) from `T` on give a unique bounded equilibrium (`fiscal_switch_selects`),
  in which fiscal news moves inflation even while money is "active"
  (`fiscal_switch_unexpected_inflation`, and the explicit example
  `fiscal_switch_example`, where `φ₀ = 2` yet `π₀ = −2δ` for a post-switch surplus `δ`). Without
  the switch (active money forever) inflation does not depend on fiscal policy at all
  (`no_switch_fiscal_irrelevant`).
-/

namespace Cochrane.ZeroBound.FutureSelection

open Filter Topology
open Cochrane.ZeroBound

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ## Two general lemmas -/

omit 𝔼 in
/-- Cochrane (2023), §20.2.1, p. 472 (boundedness of the selected path): a recursion
`|x_{t+1}| ≤ c_t|x_t| + K_t` with `c_t = a < 1` and `K_t ≤ K` from date `T` on, started from a
bounded `x₀`, is bounded. -/
theorem bounded_of_rec {T : ℕ} {a B K : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {c Kt : ℕ → ℝ}
    (hc0 : ∀ t, 0 ≤ c t) (hcT : ∀ t, T ≤ t → c t = a) (hKT : ∀ t, T ≤ t → Kt t ≤ K)
    {x : ℕ → Ω → ℝ} (h0 : ∀ ω, |x 0 ω| ≤ B)
    (hrec : ∀ t ω, |x (t + 1) ω| ≤ c t * |x t ω| + Kt t) : BoundedProc x := by
  let b : ℕ → ℝ := fun t => Nat.rec B (fun t bt => c t * bt + Kt t) t
  have hbs : ∀ t, b (t + 1) = c t * b t + Kt t := fun t => rfl
  have hb : ∀ t ω, |x t ω| ≤ b t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      intro ω
      rw [hbs]
      have := mul_le_mul_of_nonneg_left (ih ω) (hc0 t)
      linarith [hrec t ω]
  set m := max (b T) (K / (1 - a))
  have hm : ∀ n, b (T + n) ≤ m := by
    intro n
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
      rw [← add_assoc, hbs, hcT _ (by omega)]
      have h1 := hKT (T + n) (by omega)
      have h2 : K / (1 - a) ≤ m := le_max_right _ _
      rw [div_le_iff₀ (by linarith)] at h2
      nlinarith [mul_le_mul_of_nonneg_left ih ha0]
  refine ⟨|m| + ∑ k ∈ Finset.range (T + 1), |b k|, fun t ω => (hb t ω).trans ?_⟩
  have hs : 0 ≤ ∑ k ∈ Finset.range (T + 1), |b k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_cases ht : t ≤ T
  · have := Finset.single_le_sum (f := fun k => |b k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
    linarith [le_abs_self (b t), abs_nonneg m]
  · have := hm (t - T)
    rw [show T + (t - T) = t by omega] at this
    linarith [le_abs_self m]

/-- Cochrane (2023), §20.2.1, p. 472, and Ch. 24, p. 523: the scalar switching equation
`c_t y_t = d E_t y_{t+1} + f_t`, with `c_t ≠ 0` before `T` and `c_t = c_A`, `|d| < |c_A|` from
`T` on, has exactly one bounded adapted solution for every bounded adapted `f`: forward
stability after the switch pins `y_T`, and the equation, solved backward, pins every earlier
date. -/
theorem switch_scalar {T : ℕ} {cA d : ℝ} {c : ℕ → ℝ} (hc : ∀ t, t < T → c t ≠ 0)
    (hcA : ∀ t, T ≤ t → c t = cA) (hd : |d| < |cA|) {f : ℕ → Ω → ℝ} (hfb : BoundedProc f)
    (hfa : 𝔼.Adapted f) :
    ∃! y : ℕ → Ω → ℝ, BoundedProc y ∧ 𝔼.Adapted y ∧
      ∀ t, c t • y t = d • 𝔼.E t (y (t + 1)) + f t := by
  set S := ZLBRule.shiftE 𝔼 T with hS
  set g : ℕ → Ω → ℝ := fun t => f (T + t) with hg
  obtain ⟨K, hK⟩ := hfb
  have hga : S.Adapted g := fun t => hfa (T + t)
  obtain ⟨hzs, hzb, hza, hzu⟩ :=
    ForwardSolution.scalar_existsUnique S hd (fun t ω => hK (T + t) ω) hga
  set z := ForwardSolution.scalarSol S cA d g with hz
  have hSE : ∀ t, S.E t = 𝔼.E (T + t) := fun t => rfl
  -- the backward part: `back k` is the value at date `T - k`
  let back : ℕ → Ω → ℝ := fun k => Nat.rec (z 0)
    (fun k bk => (c (T - (k + 1)))⁻¹ • (d • 𝔼.E (T - (k + 1)) bk + f (T - (k + 1)))) k
  have hback : ∀ k, back (k + 1) =
      (c (T - (k + 1)))⁻¹ • (d • 𝔼.E (T - (k + 1)) (back k) + f (T - (k + 1))) := fun k => rfl
  let y : ℕ → Ω → ℝ := fun t => if T ≤ t then z (t - T) else back (T - t)
  have hyT : ∀ t, T ≤ t → y t = z (t - T) := fun t ht => by simp [y, ht]
  have hyB : ∀ k, k ≤ T → y (T - k) = back k := by
    intro k hk
    by_cases h0 : k = 0
    · subst h0
      simp [y, back]
    · simp only [y, show ¬ T ≤ T - k by omega, ↓reduceIte, show T - (T - k) = k by omega]
  -- the equation after `T`
  have eqA : ∀ t, T ≤ t → c t • y t = d • 𝔼.E t (y (t + 1)) + f t := by
    intro t ht
    have h := hzs (t - T)
    rw [hSE, show T + (t - T) = t by omega] at h
    rw [hcA t ht, hyT t ht, hyT (t + 1) (by omega), show t + 1 - T = t - T + 1 by omega]
    simpa [hg, show T + (t - T) = t by omega] using h
  -- the equation before `T`
  have eqB : ∀ k, k < T → c (T - (k + 1)) • y (T - (k + 1)) =
      d • 𝔼.E (T - (k + 1)) (y (T - (k + 1) + 1)) + f (T - (k + 1)) := by
    intro k hk
    rw [hyB (k + 1) (by omega), show T - (k + 1) + 1 = T - k by omega, hyB k (by omega),
      hback, smul_smul, mul_inv_cancel₀ (hc _ (by omega)), one_smul]
  have eqAll : ∀ t, c t • y t = d • 𝔼.E t (y (t + 1)) + f t := by
    intro t
    by_cases ht : T ≤ t
    · exact eqA t ht
    · have := eqB (T - (t + 1)) (by omega)
      rwa [show T - (T - (t + 1) + 1) = t by omega] at this
  refine ⟨y, ⟨?_, ?_, eqAll⟩, ?_⟩
  · -- boundedness
    obtain ⟨Mz, hMz⟩ := hzb
    have hbk : ∀ k, ∃ B, ∀ ω, |back k ω| ≤ B := by
      intro k
      induction k with
      | zero => exact ⟨Mz, hMz 0⟩
      | succ k ih =>
        obtain ⟨B, hB⟩ := ih
        refine ⟨|(c (T - (k + 1)))⁻¹| * (|d| * B + K), fun ω => ?_⟩
        rw [hback]
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, abs_mul]
        gcongr
        refine (abs_add_le _ _).trans (add_le_add ?_ (hK _ ω))
        rw [abs_mul]
        gcongr
        exact 𝔼.abs_E_le hB _ ω
    choose B hB using hbk
    refine ⟨|Mz| + ∑ k ∈ Finset.range (T + 1), |B k|, fun t ω => ?_⟩
    have hs : 0 ≤ ∑ k ∈ Finset.range (T + 1), |B k| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    by_cases ht : T ≤ t
    · rw [hyT t ht]
      linarith [hMz (t - T) ω, le_abs_self Mz]
    · have e := hyB (T - t) (by omega)
      rw [show T - (T - t) = t by omega] at e
      rw [e]
      have := Finset.single_le_sum (f := fun k => |B k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (show T - t < T + 1 by omega))
      linarith [hB (T - t) ω, le_abs_self (B (T - t)), abs_nonneg Mz]
  · -- adaptedness
    intro t
    by_cases ht : T ≤ t
    · rw [hyT t ht]
      have := hza (t - T)
      rwa [hSE, show T + (t - T) = t by omega] at this
    · have e := hyB (T - t) (by omega)
      rw [show T - (T - t) = t by omega] at e
      rw [e]
      obtain ⟨k, hk⟩ : ∃ k, T - t = k + 1 := ⟨T - t - 1, by omega⟩
      rw [hk, hback, show T - (k + 1) = t by omega, map_smul, map_add, map_smul, 𝔼.E_E_self,
        hfa t]
  · -- uniqueness
    rintro y' ⟨hb', ha', he'⟩
    have hpost : (fun t => y' (T + t)) = z := by
      refine hzu _ (fun t => ?_) ?_
      · have := he' (T + t)
        rw [hcA _ (by omega), show T + t + 1 = T + (t + 1) by omega] at this
        exact this
      · obtain ⟨M, hM⟩ := hb'
        exact ⟨M, fun t ω => hM (T + t) ω⟩
    have hA : ∀ t, T ≤ t → y' t = y t := by
      intro t ht
      rw [hyT t ht, ← hpost]
      simp only [show T + (t - T) = t by omega]
    have hB' : ∀ k, k ≤ T → y' (T - k) = y (T - k) := by
      intro k
      induction k with
      | zero => exact fun _ => hA _ (by omega)
      | succ k ih =>
        intro hk
        have h1 := he' (T - (k + 1))
        have h2 := eqAll (T - (k + 1))
        rw [show T - (k + 1) + 1 = T - k by omega] at h1 h2
        rw [ih (by omega), ← h2] at h1
        exact smul_right_injective _ (hc _ (by omega)) h1
    funext t
    by_cases ht : T ≤ t
    · exact hA t ht
    · have := hB' (T - t) (by omega)
      rwa [show T - (T - t) = t by omega] at this

/-! ## The monetary switch (§20.2.1) -/

/-- Cochrane (2023), §20.2.1, p. 472 (frictionless version of the future-selection model):
the Fisher equation `i_t = E_tπ_{t+1}` and the rule `i_t = φ_tπ_t + u_t` give
`E_tπ_{t+1} = φ_tπ_t + u_t`, with a time-varying rule coefficient `φ_t`. -/
def RuleEq (φ : ℕ → ℝ) (u π : ℕ → Ω → ℝ) : Prop := ∀ t, 𝔼.E t (π (t + 1)) = φ t • π t + u t

/-- Cochrane (2023), §20.2.1, p. 472: `E_tπ_{t+1} = φ_tπ_t + u_t` is the scalar switching
equation `φ_t π_t = E_tπ_{t+1} − u_t`. -/
theorem ruleEq_iff (φ : ℕ → ℝ) (u π : ℕ → Ω → ℝ) :
    RuleEq 𝔼 φ u π ↔ ∀ t, φ t • π t = (1 : ℝ) • 𝔼.E t (π (t + 1)) + (-u t) := by
  refine forall_congr' fun t => ?_
  rw [one_smul]
  constructor <;> intro h <;> rw [h] <;> abel

/-- Cochrane (2023), §20.2.1, p. 472 ("the expectation of future equilibrium-selection policy
can select equilibria even when policy is currently … passive"): with any nonzero `φ_t` before
`T` (in particular passive, `|φ_t| < 1`) and an active `|φ_A| > 1` from `T` on, the model has
exactly one bounded adapted equilibrium for every bounded adapted disturbance, under any
`ExpectationSystem`. -/
theorem future_selection {T : ℕ} {φA : ℝ} {φ : ℕ → ℝ} (hP : ∀ t, t < T → φ t ≠ 0)
    (hA : ∀ t, T ≤ t → φ t = φA) (hφA : 1 < |φA|) {u : ℕ → Ω → ℝ} (hub : BoundedProc u)
    (hua : 𝔼.Adapted u) :
    ∃! π : ℕ → Ω → ℝ, BoundedProc π ∧ 𝔼.Adapted π ∧ RuleEq 𝔼 φ u π := by
  obtain ⟨M, hM⟩ := hub
  have h := switch_scalar 𝔼 (d := 1) hP hA (by rw [abs_one]; exact hφA) (f := fun t => -u t)
    ⟨M, fun t ω => by simpa using hM t ω⟩ (fun t => by rw [map_neg, hua t])
  simpa only [ruleEq_iff] using h

/-- Cochrane (2023), §20.2.1, p. 467 and p. 472 (contrast): without the future switch, a
passive rule `0 < |φ_P| < 1` at every date leaves uncountably many bounded equilibria. -/
theorem passive_forever_not_unique [Nonempty Ω] {φP : ℝ} (h0 : φP ≠ 0) (h1 : |φP| < 1)
    {u : ℕ → Ω → ℝ} (hub : BoundedProc u) (hua : 𝔼.Adapted u) :
    ¬ {π : ℕ → Ω → ℝ | BoundedProc π ∧ RuleEq 𝔼 (fun _ => φP) u π}.Countable := by
  have ha : 1 < |φP⁻¹| := by
    rw [abs_inv]
    exact one_lt_inv_iff₀.mpr ⟨abs_pos.mpr h0, h1⟩
  obtain ⟨Mu, hMu⟩ := hub
  have hub' : BoundedProc (fun t => -(φP⁻¹) • u t) :=
    ⟨|φP⁻¹| * Mu, fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_neg]
      exact mul_le_mul_of_nonneg_left (hMu t ω) (abs_nonneg _)⟩
  have hua' : 𝔼.Adapted (fun t => -(φP⁻¹) • u t) := fun t => by rw [map_smul, hua t]
  have hset : {π : ℕ → Ω → ℝ | BoundedProc π ∧ RuleEq 𝔼 (fun _ => φP) u π} =
      {π | BoundedProc π ∧ ForwardSolution.Solves 𝔼 φP⁻¹ (fun t => -(φP⁻¹) • u t) π} := by
    ext π
    simp only [Set.mem_ofPred_eq, RuleEq, ForwardSolution.Solves]
    refine and_congr_right fun _ => forall_congr' fun t => ?_
    constructor
    · intro h
      rw [h]
      ext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · intro h
      rw [h]
      ext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  rw [hset]
  exact (ForwardSolution.exists_bounded_of_one_lt 𝔼 ha hub' hua').2

/-- Cochrane (2023), §20.2.1, p. 472: the hypothesis `φ_t ≠ 0` before the switch cannot be
dropped. With a pure peg (`φ₀ = 0`) at date 0, an active rule from `T = 1` on and `u = 0`,
under perfect foresight, both `π ≡ 0` and the path with `π₀ = 1`, `π_t = 0` afterwards are
bounded equilibria: future policy does not pin down `π₀`. -/
theorem zero_coefficient_not_unique :
    ∃ π π' : ℕ → Unit → ℝ, π ≠ π' ∧ BoundedProc π ∧ BoundedProc π' ∧
      RuleEq perfectForesight (fun t => if t = 0 then 0 else 2) 0 π ∧
      RuleEq perfectForesight (fun t => if t = 0 then 0 else 2) 0 π' := by
  refine ⟨fun _ _ => 0, fun t _ => if t = 0 then 1 else 0, ?_, ⟨0, fun _ _ => by simp⟩,
    ⟨1, fun t _ => by dsimp only; split_ifs <;> norm_num⟩, fun t => ?_, fun t => ?_⟩
  · intro h
    have := congrFun (congrFun h 0) ()
    simp at this
  · funext ω
    rcases t with _ | t <;> simp [perfectForesight]
  · funext ω
    rcases t with _ | t <;> simp [perfectForesight]

/-! ## The fiscal switch (Chapter 24, Davig and Leeper) -/

/-- Cochrane (2023), eqs. (23.1)–(23.4), p. 512, with time-varying policy (Ch. 24, p. 522):
`i_t = E_tπ_{t+1}`, `i_t = φ_tπ_t + u_{i,t}`, `s̃_{t+1} = γ_tv_t + u_{s,t+1}`,
`ρv_{t+1} = v_t + i_t − π_{t+1} − s̃_{t+1}`, and the date-0 flow `ρv₀ = c₀ − π₀`, where
`c₀ = v_{−1} + i_{−1} − s̃₀` is known at date 0. -/
def LeeperEq (ρ : ℝ) (φ γ : ℕ → ℝ) (c0 : Ω → ℝ) (ui us π v : ℕ → Ω → ℝ) : Prop :=
  ρ • v 0 = c0 - π 0 ∧ ∀ t, 𝔼.E t (π (t + 1)) = φ t • π t + ui t ∧
    ρ • v (t + 1) = v t + (φ t • π t + ui t) - π (t + 1) - (γ t • v t + us (t + 1))

/-- Cochrane (2023), p. 512 (the substitution after (23.4)): taking `E_t` of the flow and using
the Fisher equation, `ρE_tv_{t+1} = (1 − γ_t)v_t − E_tu_{s,t+1}`. -/
theorem leeper_debt_eq {ρ : ℝ} {φ γ : ℕ → ℝ} {c0 : Ω → ℝ} {ui us π v : ℕ → Ω → ℝ}
    (hπa : 𝔼.Adapted π) (hva : 𝔼.Adapted v) (hui : 𝔼.Adapted ui)
    (h : LeeperEq 𝔼 ρ φ γ c0 ui us π v) (t : ℕ) :
    (1 - γ t) • v t = ρ • 𝔼.E t (v (t + 1)) + 𝔼.E t (us (t + 1)) := by
  obtain ⟨h1, h2⟩ := (h.2 t)
  have := congrArg (𝔼.E t) h2
  simp only [map_sub, map_add, map_smul, hva t, hπa t, hui t, h1] at this
  ext ω
  have e := congrFun this ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  linarith

/-- Cochrane (2023), Ch. 24, p. 523 (Davig and Leeper 2007): passive fiscal policy
(`γ_t ≠ 1`) together with ANY monetary rule (`φ_t`, e.g. active `φ_t > 1`) before `T`, and active
fiscal (`γ = 0`) / passive money (`|φ_P| < 1`) from `T` on: for `|ρ| < 1` and bounded adapted
disturbances there is exactly one bounded adapted equilibrium — "then we are in the
active-fiscal regime all along". -/
theorem fiscal_switch_selects {T : ℕ} {ρ φP : ℝ} {φ γ : ℕ → ℝ} (hρ : |ρ| < 1) (hφP : |φP| < 1)
    (hγ : ∀ t, t < T → γ t ≠ 1) (hγT : ∀ t, T ≤ t → γ t = 0) (hφT : ∀ t, T ≤ t → φ t = φP)
    {c0 : Ω → ℝ} (hc0 : 𝔼.E 0 c0 = c0) (hc0b : ∃ B, ∀ ω, |c0 ω| ≤ B)
    {ui us : ℕ → Ω → ℝ} (huib : BoundedProc ui) (huia : 𝔼.Adapted ui) (husb : BoundedProc us)
    (husa : 𝔼.Adapted us) :
    ∃! z : (ℕ → Ω → ℝ) × (ℕ → Ω → ℝ), BoundedProc z.1 ∧ BoundedProc z.2 ∧ 𝔼.Adapted z.1 ∧
      𝔼.Adapted z.2 ∧ LeeperEq 𝔼 ρ φ γ c0 ui us z.1 z.2 := by
  -- the debt equation
  obtain ⟨Ms, hMs⟩ := husb
  obtain ⟨Mi, hMi⟩ := huib
  obtain ⟨B0, hB0⟩ := hc0b
  have hfb : BoundedProc (fun t => 𝔼.E t (us (t + 1))) :=
    ⟨Ms, fun t ω => 𝔼.abs_E_le (hMs (t + 1)) t ω⟩
  have hfa : 𝔼.Adapted (fun t => 𝔼.E t (us (t + 1))) := fun t => 𝔼.E_E_self t _
  obtain ⟨v, ⟨⟨Mv, hMv⟩, hva, hveq⟩, hvu⟩ := switch_scalar 𝔼 (c := fun t => 1 - γ t) (cA := 1)
    (d := ρ) (fun t ht => sub_ne_zero.mpr (hγ t ht).symm)
    (fun t ht => by simp [hγT t ht]) (by rwa [abs_one]) hfb hfa
  -- inflation, recursively
  let π : ℕ → Ω → ℝ := fun t => Nat.rec (c0 - ρ • v 0)
    (fun t πt => (1 - γ t) • v t + φ t • πt + ui t - us (t + 1) - ρ • v (t + 1)) t
  have hπ0 : π 0 = c0 - ρ • v 0 := rfl
  have hπs : ∀ t, π (t + 1) = (1 - γ t) • v t + φ t • π t + ui t - us (t + 1) - ρ • v (t + 1) :=
    fun t => rfl
  have hπa : 𝔼.Adapted π := by
    intro t
    induction t with
    | zero => rw [hπ0, map_sub, map_smul, hc0, hva 0]
    | succ t ih =>
      have k1 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hva t)
      have k2 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih
      have k3 := ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (huia t)
      rw [hπs, map_sub, map_sub, map_add, map_add, map_smul, map_smul, map_smul, k1, k2, k3,
        husa, hva]
  have hsol : LeeperEq 𝔼 ρ φ γ c0 ui us π v := by
    refine ⟨by rw [hπ0]; abel, fun t => ⟨?_, ?_⟩⟩
    · have hv := hveq t
      rw [hπs, map_sub, map_sub, map_add, map_add, map_smul, map_smul, map_smul, hva t, hπa t,
        huia t]
      rw [hv]
      abel
    · rw [hπs]
      ext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hπb : BoundedProc π := by
    have hMv' : ∀ t ω, |v t ω| ≤ |Mv| := fun t ω => (hMv t ω).trans (le_abs_self _)
    have hMi' : ∀ t ω, |ui t ω| ≤ |Mi| := fun t ω => (hMi t ω).trans (le_abs_self _)
    have hMs' : ∀ t ω, |us t ω| ≤ |Ms| := fun t ω => (hMs t ω).trans (le_abs_self _)
    refine bounded_of_rec (T := T) (a := |φP|) (B := B0 + |ρ| * |Mv|)
      (K := |Mv| + |Mi| + |Ms| + |ρ| * |Mv|) (abs_nonneg _) hφP (c := fun t => |φ t|)
      (Kt := fun t => |1 - γ t| * |Mv| + |Mi| + |Ms| + |ρ| * |Mv|) (fun t => abs_nonneg _)
      (fun t ht => by simp [hφT t ht]) (fun t ht => by simp [hγT t ht]) (fun ω => ?_)
      (fun t ω => ?_)
    · rw [hπ0]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (abs_sub _ _).trans (add_le_add (hB0 ω) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMv' 0 ω) (abs_nonneg _)
    · rw [hπs]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have e1 := mul_le_mul_of_nonneg_left (hMv' t ω) (abs_nonneg (1 - γ t))
      have e2 := mul_le_mul_of_nonneg_left (hMv' (t + 1) ω) (abs_nonneg ρ)
      have a1 := abs_sub ((1 - γ t) * v t ω + φ t * π t ω + ui t ω - us (t + 1) ω)
        (ρ * v (t + 1) ω)
      have a2 := abs_sub ((1 - γ t) * v t ω + φ t * π t ω + ui t ω) (us (t + 1) ω)
      have a3 := abs_add_le ((1 - γ t) * v t ω + φ t * π t ω) (ui t ω)
      have a4 := abs_add_le ((1 - γ t) * v t ω) (φ t * π t ω)
      rw [abs_mul] at a1 a4
      rw [abs_mul] at a4
      linarith [hMi' t ω, hMs' (t + 1) ω]
  refine ⟨(π, v), ⟨hπb, ⟨Mv, hMv⟩, hπa, hva, hsol⟩, ?_⟩
  rintro ⟨π', v'⟩ ⟨hb1, hb2, ha1, ha2, hs'⟩
  have hv' : v' = v := hvu v' ⟨hb2, ha2, fun t => leeper_debt_eq 𝔼 ha1 ha2 huia hs' t⟩
  subst hv'
  have hπ' : ∀ t, π' t = π t := by
    intro t
    induction t with
    | zero =>
      have := hs'.1
      ext ω
      have e := congrFun this ω
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
      simp only [hπ0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linarith
    | succ t ih =>
      rw [hπs, ← ih]
      have := (hs'.2 t).2
      ext ω
      have h := congrFun this ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
      linarith
  exact Prod.ext (funext hπ') rfl

/-- Cochrane (2023), Ch. 24, pp. 523–524 ("The expected switch to active fiscal means that
fiscal shocks affect inflation immediately even in the locally-active money/passive fiscal
repayment regime"): in every equilibrium of the Leeper model, unexpected inflation is
`π_{t+1} − E_tπ_{t+1} = −ρ(v_{t+1} − E_tv_{t+1}) − (u_{s,t+1} − E_tu_{s,t+1})`. -/
theorem fiscal_switch_unexpected_inflation {ρ : ℝ} {φ γ : ℕ → ℝ} {c0 : Ω → ℝ}
    {ui us π v : ℕ → Ω → ℝ} (hπa : 𝔼.Adapted π) (hva : 𝔼.Adapted v) (hui : 𝔼.Adapted ui)
    (h : LeeperEq 𝔼 ρ φ γ c0 ui us π v) (t : ℕ) :
    π (t + 1) - 𝔼.E t (π (t + 1)) =
      -(ρ • (v (t + 1) - 𝔼.E t (v (t + 1)))) - (us (t + 1) - 𝔼.E t (us (t + 1))) := by
  have hd := leeper_debt_eq 𝔼 hπa hva hui h t
  obtain ⟨h1, h2⟩ := h.2 t
  rw [h1]
  ext ω
  have a := congrFun h2 ω
  have b := congrFun hd ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at a b ⊢
  linarith

/-- Cochrane (2023), Ch. 24, p. 523 (contrast): without the switch — the same active monetary
rule `|φ| > 1` at every date — inflation in a bounded equilibrium does not depend on fiscal
policy at all: two equilibria with the same monetary disturbance but different fiscal rules and
surplus disturbances have the same inflation. -/
theorem no_switch_fiscal_irrelevant {ρ φ : ℝ} (hφ : 1 < |φ|) {γ γ' : ℕ → ℝ} {c0 c0' : Ω → ℝ}
    {ui us us' π π' v v' : ℕ → Ω → ℝ} (huib : BoundedProc ui) (huia : 𝔼.Adapted ui)
    (hπb : BoundedProc π) (hπb' : BoundedProc π') (hπa : 𝔼.Adapted π) (hπa' : 𝔼.Adapted π')
    (h : LeeperEq 𝔼 ρ (fun _ => φ) γ c0 ui us π v)
    (h' : LeeperEq 𝔼 ρ (fun _ => φ) γ' c0' ui us' π' v') : π = π' := by
  obtain ⟨p, -, hpu⟩ := future_selection 𝔼 (T := 0) (φ := fun _ => φ) (φA := φ)
    (fun t ht => absurd ht (Nat.not_lt_zero t)) (fun _ _ => rfl) hφ huib huia
  rw [hpu π ⟨hπb, hπa, fun t => (h.2 t).1⟩, hpu π' ⟨hπb', hπa', fun t => (h'.2 t).1⟩]

/-- Cochrane (2023), Ch. 24, p. 523, worked example: perfect foresight, switch at `T = 1`,
active money `φ₀ = 2` and passive fiscal `γ₀ = 1/2` at date 0, then a peg (`φ = 0`) with active
fiscal (`γ = 0`), `ρ = 1/2`, `c₀ = 0`, `u_i = 0` and post-switch surpluses `u_{s,t} = δ`
(`t ≥ 1`). The unique bounded equilibrium has `π₀ = −2δ`, `π₁ = −4δ`, `π_t = 0` after: the
expected future surplus moves inflation at date 0, although money is active at date 0. -/
theorem fiscal_switch_example (δ : ℝ) :
    ∃! z : (ℕ → Unit → ℝ) × (ℕ → Unit → ℝ), BoundedProc z.1 ∧ BoundedProc z.2 ∧
      perfectForesight.Adapted z.1 ∧ perfectForesight.Adapted z.2 ∧
      LeeperEq perfectForesight (1 / 2) (fun t => if t = 0 then 2 else 0)
        (fun t => if t = 0 then 1 / 2 else 0) (fun _ => 0) 0 (fun t _ => if t = 0 then 0 else δ)
        z.1 z.2 ∧ z.1 0 () = -2 * δ ∧ z.1 1 () = -4 * δ := by
  have hex := fiscal_switch_selects perfectForesight (T := 1) (ρ := 1 / 2) (φP := 0)
    (φ := fun t => if t = 0 then 2 else 0) (γ := fun t => if t = 0 then 1 / 2 else 0)
    (by norm_num [abs_of_pos]) (by simp) (fun t ht => by simp [show t = 0 by omega])
    (fun t ht => by simp [show t ≠ 0 by omega]) (fun t ht => by simp [show t ≠ 0 by omega])
    (c0 := fun _ => 0) rfl ⟨0, fun _ => by simp⟩ (ui := 0) ⟨0, fun _ _ => by simp⟩
    (fun _ => rfl) (us := fun t _ => if t = 0 then 0 else δ)
    ⟨|δ|, fun t _ => by dsimp only; split_ifs <;> simp⟩ (fun _ => rfl)
  let πe : ℕ → Unit → ℝ := fun t _ => if t = 0 then -2 * δ else if t = 1 then -4 * δ else 0
  let ve : ℕ → Unit → ℝ := fun t _ => if t = 0 then 4 * δ else 2 * δ
  have hsol : LeeperEq perfectForesight (1 / 2) (fun t => if t = 0 then 2 else 0)
      (fun t => if t = 0 then 1 / 2 else 0) (fun _ => 0) 0 (fun t _ => if t = 0 then 0 else δ)
      πe ve := by
    refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
    · funext ω
      simp [πe, ve]
      ring
    · funext ω
      rcases t with _ | _ | t <;> (simp [perfectForesight, πe]; try ring)
    · funext ω
      rcases t with _ | _ | t <;> simp [πe, ve] <;> ring
  have hb1 : BoundedProc πe := ⟨4 * |δ|, fun t _ => by
    simp only [πe]
    split_ifs <;> (simp [abs_mul]; try linarith [abs_nonneg δ])⟩
  have hb2 : BoundedProc ve := ⟨4 * |δ|, fun t _ => by
    simp only [ve]
    split_ifs <;> (simp [abs_mul]; try linarith [abs_nonneg δ])⟩
  obtain ⟨z, hz, hzu⟩ := hex
  have hz' : z = (πe, ve) := (hzu (πe, ve) ⟨hb1, hb2, fun _ => rfl, fun _ => rfl, hsol⟩).symm
  refine ⟨z, ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2, ?_, ?_⟩, fun y hy => ?_⟩
  · rw [hz']
    simp [πe]
  · rw [hz']
    simp [πe]
  · exact hzu y ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1⟩

end Cochrane.ZeroBound.FutureSelection
