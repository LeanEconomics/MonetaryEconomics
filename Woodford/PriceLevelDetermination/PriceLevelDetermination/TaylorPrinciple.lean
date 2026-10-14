/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.Wicksell
import Mathlib.Analysis.Real.Cardinality

/-!
# The Taylor principle and determinacy

Woodford (2003), *Interest and Prices*, Chapter 2, §2.2, eqs. (2.4)–(2.7), Proposition 2.6,
footnote 25, pp. 90–94. The book gives no proof of Proposition 2.6 ("the proof follows exactly
the same lines" as Propositions 2.3 and 2.5); this module supplies one, for the log-linear
model, in both directions.

## Main results

* `fisher_iff_26`: (1.32) with the rule (2.5) substituted is (2.6),
  `φ_π π_t = E_t π_{t+1} + (r̂_t − ī_t)`.
* `inflation27` (2.7), `existsUnique_27`: for `|φ_π| > 1` (in particular `φ_π > 1`, the Taylor
  principle) and bounded `r̂ − ī`, (2.7) is the unique bounded solution.
* `prop_2_6_iff`: for every bounded adapted `{r̂, ī}` there is a unique bounded solution iff
  `|φ_π| > 1`; `prop_2_6`: within the book's `φ_π ≥ 0`, determinacy iff `φ_π > 1`.
* `indeterminate_lt_one`: for `0 ≤ φ_π < 1` (indeed `|φ_π| < 1`, including the exogenous-rate
  case `φ_π = 0`) every martingale difference `ν` gives a bounded sunspot solution
  (`sunspotInfl`) and the bounded solutions are uncountable; `one_no_bounded`, `one_not_unique`:
  at `φ_π = 1` a bounded solution may fail to exist, and is never unique when it exists.
* Footnote 25: `price_level_determined` — with `P_{−1}` predetermined, unique inflation pins
  down the price level.
* p. 92: `abs_infl_le` (`|π_t| ≤ sup|r̂ − ī|/(φ_π − 1)`), `infl_bound_antitone`; `oneOff_taylor`
  (a one-period gap shifts the price level permanently by `κ/φ_π`) versus `oneOff_wicksell`
  (under the Wicksellian rule the price level returns to target).
* p. 93: `regression_coefficient` — with `P̂` a stationary MA(∞) process and `ν = 0`, the
  population coefficient of a regression of `î = φ_p P̂` on `π = ΔP̂` (+ const) is `φ_p/2`.
-/

namespace Woodford.PriceLevelDetermination.TaylorPrinciple

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (2.5)–(2.7) -/

/-- Woodford (2003), eq. (2.6), p. 91: `φ_π π_t = E_t π_{t+1} + (r̂_t − ī_t)`. -/
def Eq26 (φπ : ℝ) (r ib π : ℕ → Ω → ℝ) : Prop :=
  ∀ t, φπ • π t = 𝔼.E t (π (t + 1)) + (r t - ib t)

/-- Woodford (2003), eqs. (1.32), (2.5), (2.6), pp. 79, 91: the Fisher equation
`î_t = r̂_t + E_t π_{t+1}` with the Taylor rule `î_t = ī_t + φ_π π_t` holds iff (2.6) holds. -/
theorem fisher_iff_26 (φπ : ℝ) (r ib π : ℕ → Ω → ℝ) :
    (∀ t, ib t + φπ • π t = r t + 𝔼.E t (π (t + 1))) ↔ Eq26 𝔼 φπ r ib π := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor <;> intro h <;> linarith

/-- Woodford (2003), eq. (2.7), p. 91: `π_t = ∑_{j ≥ 0} φ_π^{−(j+1)} E_t(r̂_{t+j} − ī_{t+j})`. -/
noncomputable def inflation27 (φπ : ℝ) (r ib : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' j, φπ⁻¹ ^ (j + 1) * 𝔼.E t (r (t + j) - ib (t + j)) ω

/-- Woodford (2003), eq. (2.6) and App. A, p. 636: for `φ_π ≠ 0`, (2.6) is (A.14) with
`a = φ_π⁻¹` and `u_t = φ_π⁻¹(r̂_t − ī_t)`. -/
theorem eq26_iff_solves {φπ : ℝ} (hφ : φπ ≠ 0) {r ib π : ℕ → Ω → ℝ} :
    Eq26 𝔼 φπ r ib π ↔ ForwardSolution.Solves 𝔼 φπ⁻¹ (fun t => φπ⁻¹ • (r t - ib t)) π := by
  refine forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp

/-- Woodford (2003), eq. (2.7), p. 91: (2.7) is the forward sum (A.16) of (2.6). -/
theorem inflation27_eq_forwardSeries (φπ : ℝ) (r ib : ℕ → Ω → ℝ) :
    inflation27 𝔼 φπ r ib = 𝔼.forwardSeries φπ⁻¹ (fun t => φπ⁻¹ • (r t - ib t)) := by
  funext t ω
  unfold inflation27 ExpectationSystem.forwardSeries
  refine tsum_congr fun j => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-- Woodford (2003), eq. (2.7) and Proposition 2.6, p. 91: for `|φ_π| > 1` and bounded adapted
`{r̂, ī}`, (2.7) is a bounded adapted solution of (2.6), and every bounded solution is (2.7). -/
theorem existsUnique_27 {φπ : ℝ} (hφ : 1 < |φπ|) {r ib : ℕ → Ω → ℝ} (hrb : BoundedProc r)
    (hib : BoundedProc ib) (hra : 𝔼.Adapted r) (hia : 𝔼.Adapted ib) :
    Eq26 𝔼 φπ r ib (inflation27 𝔼 φπ r ib) ∧ BoundedProc (inflation27 𝔼 φπ r ib) ∧
      𝔼.Adapted (inflation27 𝔼 φπ r ib) ∧
      ∀ π, BoundedProc π → Eq26 𝔼 φπ r ib π → π = inflation27 𝔼 φπ r ib := by
  obtain ⟨Mr, hr⟩ := hrb
  obtain ⟨Mi, hi⟩ := hib
  have hne : φπ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hφ
    linarith
  have ha : |φπ⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hφ
  have hu : ∀ t ω, |(fun t => φπ⁻¹ • (r t - ib t)) t ω| ≤ Mr + Mi := by
    intro t ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul]
    calc |φπ⁻¹| * |r t ω - ib t ω| ≤ 1 * |r t ω - ib t ω| := by gcongr
      _ ≤ Mr + Mi := by
        rw [one_mul]; exact (abs_sub _ _).trans (add_le_add (hr t ω) (hi t ω))
  have hua : 𝔼.Adapted (fun t => φπ⁻¹ • (r t - ib t)) := by
    intro t
    simp only [map_smul, map_sub, hra t, hia t]
  rw [inflation27_eq_forwardSeries]
  refine ⟨(eq26_iff_solves 𝔼 hne).mpr (ForwardSolution.forwardSeries_solves_abs 𝔼 ha hu hua),
    ForwardSolution.forwardSeries_bounded_abs 𝔼 ha hu,
    ForwardSolution.forwardSeries_adapted_abs 𝔼 ha hu, fun π hπb hπ => ?_⟩
  exact ForwardSolution.eq_forwardSeries_abs 𝔼 ha hu hua ((eq26_iff_solves 𝔼 hne).mp hπ) hπb

/-! ### Proposition 2.6 -/

/-- Woodford (2003), Proposition 2.6, p. 91 (log-linear, exact characterisation): (2.6) has a
unique bounded solution for every bounded adapted `{r̂, ī}` if and only if `|φ_π| > 1`. For
`|φ_π| ≤ 1` both `π ≡ 0` and `π_t = φ_πᵗ` solve (2.6) with `r̂ = ī = 0`. -/
theorem prop_2_6_iff [Nonempty Ω] (φπ : ℝ) :
    (∀ r ib : ℕ → Ω → ℝ, BoundedProc r → BoundedProc ib → 𝔼.Adapted r → 𝔼.Adapted ib →
      ∃! π, BoundedProc π ∧ Eq26 𝔼 φπ r ib π) ↔ 1 < |φπ| := by
  constructor
  · intro h
    by_contra hc
    have hc' : |φπ| ≤ 1 := not_lt.mp hc
    have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
    obtain ⟨π, -, hu⟩ := h 0 0 hzb hzb (fun t => map_zero _) (fun t => map_zero _)
    have e0 := hu 0 ⟨hzb, fun t => by simp⟩
    have e1 := hu (fun t _ => φπ ^ t) ⟨⟨1, fun t _ => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc'⟩, fun t => by
        rw [𝔼.const]
        funext ω
        simp [pow_succ]
        ring⟩
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have := congrFun (congrFun (e1.trans e0.symm) 0) ω
    simp at this
  · intro hφ r ib hrb hib hra hia
    obtain ⟨h1, h2, -, h4⟩ := existsUnique_27 𝔼 hφ hrb hib hra hia
    exact ⟨_, ⟨h2, h1⟩, fun π hπ => h4 π hπ.1 hπ.2⟩

/-- Woodford (2003), Proposition 2.6, p. 91: for a rule with `φ_π ≥ 0`, equilibrium is
determinate (a unique bounded solution for all bounded disturbances) if and only if the Taylor
principle `φ_π > 1` holds. -/
theorem prop_2_6 [Nonempty Ω] {φπ : ℝ} (hφ : 0 ≤ φπ) :
    (∀ r ib : ℕ → Ω → ℝ, BoundedProc r → BoundedProc ib → 𝔼.Adapted r → 𝔼.Adapted ib →
      ∃! π, BoundedProc π ∧ Eq26 𝔼 φπ r ib π) ↔ 1 < φπ := by
  rw [prop_2_6_iff, abs_of_nonneg hφ]

/-- Woodford (2003), App. A, p. 637 (the family (A.17) for (2.6)): `π_0` given and
`π_{t+1} = φ_π π_t − (r̂_t − ī_t) + ν_{t+1}`. -/
def sunspotInfl (φπ : ℝ) (r ib ν : ℕ → Ω → ℝ) (π0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => π0
  | t + 1 => φπ • sunspotInfl φπ r ib ν π0 t - (r t - ib t) + ν (t + 1)

/-- Woodford (2003), Proposition 2.6, p. 91 (indeterminacy): for any `φ_π`, any adapted `π_0`,
`r̂`, `ī`, `ν` with `E_t ν_{t+1} = 0`, `sunspotInfl` solves (2.6). -/
theorem sunspotInfl_solves {φπ : ℝ} {r ib ν : ℕ → Ω → ℝ} {π0 : Ω → ℝ} (h0 : 𝔼.E 0 π0 = π0)
    (hra : 𝔼.Adapted r) (hia : 𝔼.Adapted ib) (hνa : 𝔼.Adapted ν)
    (hmd : ∀ t, 𝔼.E t (ν (t + 1)) = 0) : Eq26 𝔼 φπ r ib (sunspotInfl φπ r ib ν π0) := by
  have had : 𝔼.Adapted (sunspotInfl φπ r ib ν π0) := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      simp only [sunspotInfl, map_add, map_sub, map_smul,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hra t),
        ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hia t), hνa (t + 1)]
  intro t
  simp only [sunspotInfl, map_add, map_sub, map_smul, had t, hra t, hia t, hmd t, add_zero]
  abel

/-- Woodford (2003), Proposition 2.6, p. 91: for `|φ_π| < 1` the family is bounded whenever
`π_0`, `r̂ − ī` and `ν` are. -/
theorem sunspotInfl_bounded {φπ B G Mν : ℝ} (hφ : |φπ| < 1) {r ib ν : ℕ → Ω → ℝ}
    {π0 : Ω → ℝ} (h0 : ∀ ω, |π0 ω| ≤ B) (hg : ∀ t ω, |r t ω - ib t ω| ≤ G)
    (hν : ∀ t ω, |ν t ω| ≤ Mν) : BoundedProc (sunspotInfl φπ r ib ν π0) := by
  set K := |B| + (|G| + |Mν|) / (1 - |φπ|) with hK
  have h1 : 0 < 1 - |φπ| := by linarith
  have hfrac : 0 ≤ (|G| + |Mν|) / (1 - |φπ|) := div_nonneg (by positivity) h1.le
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero => exact fun ω => (h0 ω).trans ((le_abs_self B).trans (by linarith))
  | succ t ih =>
    intro ω
    simp only [sunspotInfl, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have ha : |φπ * sunspotInfl φπ r ib ν π0 t ω| ≤ |φπ| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih ω) (abs_nonneg _)
    have hb := (hg t ω).trans (le_abs_self G)
    have hc := (hν (t + 1) ω).trans (le_abs_self Mν)
    have hKe : K * (1 - |φπ|) = |B| * (1 - |φπ|) + (|G| + |Mν|) := by
      rw [hK, add_mul, div_mul_cancel₀ _ h1.ne']
    have hB : 0 ≤ |B| * (1 - |φπ|) := mul_nonneg (abs_nonneg B) h1.le
    calc |φπ * sunspotInfl φπ r ib ν π0 t ω - (r t ω - ib t ω) + ν (t + 1) ω|
        ≤ |φπ * sunspotInfl φπ r ib ν π0 t ω - (r t ω - ib t ω)| + |ν (t + 1) ω| :=
          abs_add_le _ _
      _ ≤ |φπ * sunspotInfl φπ r ib ν π0 t ω| + |r t ω - ib t ω| + |ν (t + 1) ω| := by
          gcongr; exact abs_sub _ _
      _ ≤ K := by nlinarith

/-- Woodford (2003), Proposition 2.6, p. 91 ("if instead `0 ≤ φ_π < 1`, rational-expectations
equilibrium is indeterminate, as in Proposition 2.5"): for `|φ_π| < 1` (including `φ_π = 0`) and
bounded adapted `{r̂, ī}`, the bounded solutions of (2.6) are uncountably many. -/
theorem indeterminate_lt_one [Nonempty Ω] {φπ : ℝ} (hφ : |φπ| < 1) {r ib : ℕ → Ω → ℝ}
    (hrb : BoundedProc r) (hib : BoundedProc ib) (hra : 𝔼.Adapted r) (hia : 𝔼.Adapted ib) :
    ¬ {π | BoundedProc π ∧ Eq26 𝔼 φπ r ib π}.Countable := by
  obtain ⟨Mr, hr⟩ := hrb
  obtain ⟨Mi, hi⟩ := hib
  intro hcount
  let f : ℝ → ℕ → Ω → ℝ := fun c => sunspotInfl φπ r ib 0 (fun _ => c)
  have hmaps : Set.MapsTo f Set.univ {π | BoundedProc π ∧ Eq26 𝔼 φπ r ib π} := fun c _ =>
    ⟨sunspotInfl_bounded hφ (B := |c|) (fun _ => le_rfl)
      (fun t ω => (abs_sub _ _).trans (add_le_add (hr t ω) (hi t ω))) (Mν := 0)
      (fun _ _ => by simp),
      sunspotInfl_solves 𝔼 (𝔼.const 0 c) hra hia (fun t => map_zero _) (fun t => map_zero _)⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    exact congrFun (congrFun h 0) ω
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-- Woodford (2003), Proposition 2.6, p. 91 (the boundary `φ_π = 1`, not covered by the book's
statement): with a constant nonzero gap `r̂ − ī ≡ κ` there is no bounded solution. -/
theorem one_no_bounded [Nonempty Ω] {κ : ℝ} (hκ : κ ≠ 0) {r ib π : ℕ → Ω → ℝ}
    (hgap : ∀ t ω, r t ω - ib t ω = κ) (hπ : Eq26 𝔼 1 r ib π) : ¬ BoundedProc π := by
  have hs : ForwardSolution.Solves 𝔼 1 (fun t _ => κ * 1 ^ t) π := by
    intro t
    have h := (eq26_iff_solves 𝔼 one_ne_zero).mp hπ t
    rw [h]
    funext ω
    simp [hgap t ω]
  exact ForwardSolution.no_bounded_solution_unit 𝔼 (by norm_num) hκ hs

/-- Woodford (2003), Proposition 2.6, p. 91 (the boundary `φ_π = 1`): whenever a bounded
solution exists there are uncountably many. -/
theorem one_not_unique [Nonempty Ω] {r ib π : ℕ → Ω → ℝ} (hπ : Eq26 𝔼 1 r ib π)
    (hπb : BoundedProc π) :
    ¬ Set.Countable {π' | BoundedProc π' ∧ Eq26 𝔼 1 r ib π'} := by
  have hset : {π' | BoundedProc π' ∧ Eq26 𝔼 1 r ib π'} = {π' | BoundedProc π' ∧
      ForwardSolution.Solves 𝔼 (1 : ℝ)⁻¹ (fun t => (1 : ℝ)⁻¹ • (r t - ib t)) π'} := by
    ext π'
    simp only [Set.mem_ofPred_eq, eq26_iff_solves 𝔼 one_ne_zero]
  rw [hset]
  exact ForwardSolution.bounded_solutions_not_countable 𝔼 (by norm_num)
    ((eq26_iff_solves 𝔼 one_ne_zero).mp hπ) hπb

/-! ### Footnote 25: the price level is determined -/

/-- Woodford (2003), fn. 25, p. 91: the log price level `L_{t+1} = log P_t`, built from the
predetermined `L_0 = log P_{−1}` and inflation, `L_{t+1} = L_t + π_t`. -/
def logLevel (L0 : Ω → ℝ) (π : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => L0
  | t + 1 => logLevel L0 π t + π t

omit 𝔼 in
/-- Woodford (2003), fn. 25, p. 91: `log P_t = log P_{−1} + ∑_{s ≤ t} π_s`. -/
theorem logLevel_eq (L0 : Ω → ℝ) (π : ℕ → Ω → ℝ) (t : ℕ) :
    logLevel L0 π (t + 1) = L0 + ∑ s ∈ Finset.range (t + 1), π s := by
  induction t with
  | zero => simp [logLevel]
  | succ t ih =>
    rw [logLevel, ih, Finset.sum_range_succ _ (t + 1), add_assoc]

/-- Woodford (2003), fn. 25, p. 91: under the Taylor principle the price level, not just
inflation, is determined — two bounded equilibria with the same predetermined `P_{−1}` have the
same price level at every date. -/
theorem price_level_determined {φπ : ℝ} (hφ : 1 < |φπ|) {r ib π π' : ℕ → Ω → ℝ}
    (hrb : BoundedProc r) (hib : BoundedProc ib) (hra : 𝔼.Adapted r) (hia : 𝔼.Adapted ib)
    (hπb : BoundedProc π) (hπb' : BoundedProc π') (hπ : Eq26 𝔼 φπ r ib π)
    (hπ' : Eq26 𝔼 φπ r ib π') (L0 : Ω → ℝ) : logLevel L0 π = logLevel L0 π' := by
  obtain ⟨-, -, -, h4⟩ := existsUnique_27 𝔼 hφ hrb hib hra hia
  rw [h4 π hπb hπ, h4 π' hπb' hπ']

/-! ### p. 92: inflation variability and price-level drift -/

/-- Woodford (2003), p. 92 ("equilibrium inflation variability varies inversely with the
response elasticity `φ_π`"): for `φ_π > 1`, if `|r̂_t − ī_t| ≤ K` then every bounded solution of
(2.6) has `|π_t| ≤ K/(φ_π − 1)`. -/
theorem abs_infl_le {φπ K : ℝ} (hφ : 1 < φπ) {r ib π : ℕ → Ω → ℝ}
    (hK : ∀ t ω, |r t ω - ib t ω| ≤ K) (hπb : BoundedProc π) (hπ : Eq26 𝔼 φπ r ib π)
    (t : ℕ) (ω : Ω) : |π t ω| ≤ K / (φπ - 1) := by
  obtain ⟨M, hM⟩ := hπb
  have hφ0 : 0 < φπ := by linarith
  have hq0 : 0 < φπ⁻¹ := inv_pos.mpr hφ0
  have ha : |φπ⁻¹| < 1 := by rw [abs_of_pos hq0]; exact inv_lt_one_of_one_lt₀ hφ
  have hs := (eq26_iff_solves 𝔼 hφ0.ne').mp hπ
  have hu : ∀ t ω, |(fun t => φπ⁻¹ • (r t - ib t)) t ω| ≤ φπ⁻¹ * K := by
    intro t ω
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul, abs_of_pos hq0]
    exact mul_le_mul_of_nonneg_left (hK t ω) hq0.le
  have := Wicksell.abs_le_of_forward 𝔼 ha hs hM hu t ω
  rw [abs_of_pos hq0] at this
  have he : φπ⁻¹ * K / (1 - φπ⁻¹) = K / (φπ - 1) := by
    have h1 : 1 - φπ⁻¹ = (φπ - 1) * φπ⁻¹ := by
      have hinv : φπ * φπ⁻¹ = 1 := mul_inv_cancel₀ hφ0.ne'
      linear_combination (-1 : ℝ) * hinv
    rw [h1, div_eq_div_iff (mul_ne_zero (by linarith) hq0.ne') (by linarith)]
    ring
  rwa [he] at this

/-- Woodford (2003), p. 92: the bound `K/(φ_π − 1)` is antitone in `φ_π > 1`. -/
theorem infl_bound_antitone {K : ℝ} (hK : 0 ≤ K) :
    AntitoneOn (fun φπ : ℝ => K / (φπ - 1)) (Set.Ioi 1) := by
  intro x hx y _ hxy
  have hx' : 0 < x - 1 := by
    have := Set.mem_Ioi.mp hx
    linarith
  exact div_le_div_of_nonneg_left hK hx' (by linarith)

/-- Woodford (2003), p. 92 ("transitory fluctuations in the gap … permanently shift the absolute
level of prices"): with a one-period gap `r̂_0 − ī_0 = κ` (zero afterwards) and `φ_π > 1`, the
unique bounded equilibrium is `π_0 = κ/φ_π`, `π_t = 0` for `t ≥ 1`, so the log price level is
shifted permanently: `log P_t − log P_{−1} = κ/φ_π` for all `t ≥ 0`. -/
theorem oneOff_taylor {φπ κ : ℝ} (hφ : 1 < φπ) {r ib π : ℕ → Ω → ℝ} (hrb : BoundedProc r)
    (hib : BoundedProc ib) (hra : 𝔼.Adapted r) (hia : 𝔼.Adapted ib)
    (hgap0 : ∀ ω, r 0 ω - ib 0 ω = κ) (hgap : ∀ t ω, r (t + 1) ω - ib (t + 1) ω = 0)
    (hπb : BoundedProc π) (hπ : Eq26 𝔼 φπ r ib π) (L0 : Ω → ℝ) (t : ℕ) (ω : Ω) :
    logLevel L0 π (t + 1) ω - L0 ω = κ / φπ := by
  have hφ0 : φπ ≠ 0 := by linarith
  set π₀ : ℕ → Ω → ℝ := fun t _ => if t = 0 then κ / φπ else 0 with hπ₀
  have hsol : Eq26 𝔼 φπ r ib π₀ := by
    intro t
    rw [hπ₀]
    simp only [show t + 1 ≠ 0 by omega, ↓reduceIte, 𝔼.const]
    funext ω
    rcases t with _ | t
    · simp only [↓reduceIte, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, hgap0 ω]
      field_simp
      ring
    · simp only [show t + 1 ≠ 0 by omega, ↓reduceIte, Pi.smul_apply, Pi.add_apply,
        Pi.sub_apply, smul_eq_mul, hgap t ω]
      ring
  have hb : BoundedProc π₀ := ⟨|κ / φπ|, fun t ω => by
    rw [hπ₀]
    dsimp only
    split_ifs <;> simp⟩
  have habs : 1 < |φπ| := by rw [abs_of_pos (by linarith)]; exact hφ
  obtain ⟨-, -, -, h4⟩ := existsUnique_27 𝔼 habs hrb hib hra hia
  have he : π = π₀ := (h4 π hπb hπ).trans (h4 π₀ hb hsol).symm
  rw [he, logLevel_eq, Pi.add_apply, Finset.sum_apply, Finset.sum_range_succ']
  have hz : ∀ s ∈ Finset.range t, π₀ (s + 1) ω = 0 := fun s _ => by
    rw [hπ₀]
    simp
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_add]
  simp [hπ₀]

/-- Woodford (2003), p. 92 (contrast with the Wicksellian regime): with a constant target and the
same one-period gap `r̂_0 − ν_0 = κ` (zero afterwards), the bounded equilibrium of (1.36) is
`P̂_0 = κ/(1 + φ_p)` and `P̂_t = 0` for `t ≥ 1`: the price level returns to target. -/
theorem oneOff_wicksell {φp κ : ℝ} (hφ : 0 < φp) {r ν Ph : ℕ → Ω → ℝ} (hrb : BoundedProc r)
    (hνb : BoundedProc ν) (hra : 𝔼.Adapted r) (hνa : 𝔼.Adapted ν)
    (hgap0 : ∀ ω, r 0 ω - ν 0 ω = κ) (hgap : ∀ t ω, r (t + 1) ω - ν (t + 1) ω = 0)
    (hPb : BoundedProc Ph) (hP : Wicksell.Reduced 𝔼 φp r 0 ν Ph) :
    Ph = fun t _ => if t = 0 then κ / (1 + φp) else 0 := by
  have hne : (1 : ℝ) + φp ≠ 0 := by linarith
  have hzb : BoundedProc (0 : ℕ → Ω → ℝ) := ⟨0, fun _ _ => by simp⟩
  have e := (Wicksell.existsUnique_priceGap 𝔼 (Wicksell.one_lt_abs_of_pos hφ) hrb hzb hνb hra
    hνa).2.2.2
  have hsol : Wicksell.Reduced 𝔼 φp r 0 ν (fun t _ => if t = 0 then κ / (1 + φp) else 0) := by
    intro t
    simp only [show t + 1 ≠ 0 by omega, ↓reduceIte, 𝔼.const, Pi.zero_apply, map_zero]
    funext ω
    rcases t with _ | t
    · simp only [↓reduceIte, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
        Pi.zero_apply]
      have := hgap0 ω
      field_simp
      linarith
    · simp only [show t + 1 ≠ 0 by omega, ↓reduceIte, Pi.smul_apply, Pi.add_apply,
        Pi.sub_apply, smul_eq_mul, Pi.zero_apply, mul_zero]
      linarith [hgap t ω]
  have hb : BoundedProc (fun t (_ : Ω) => if t = 0 then κ / (1 + φp) else 0) :=
    ⟨|κ / (1 + φp)|, fun t ω => by dsimp only; split_ifs <;> simp⟩
  exact (e Ph hPb hP).trans (e _ hb hsol).symm

/-! ### p. 93: the regression coefficient `φ_p/2` -/

/-- Woodford (2003), p. 93: the MA(∞) coefficients of `ΔP̂_t = P̂_t − P̂_{t−1}` when
`P̂_t = ∑_j ψ_j ε_{t−j}`: `ψ_0`, then `ψ_{j+1} − ψ_j`. -/
def dpsi (ψ : ℕ → ℝ) : ℕ → ℝ
  | 0 => ψ 0
  | j + 1 => ψ (j + 1) - ψ j

/-- Woodford (2003), p. 93: the autocovariance `γ_k = ∑_j ψ_j ψ_{j+k}` of the stationary
`P̂_t = ∑_j ψ_j ε_{t−j}` (unit-variance white noise `ε`). -/
noncomputable def autocov (ψ : ℕ → ℝ) (k : ℕ) : ℝ := ∑' j, ψ j * ψ (j + k)

/-- Woodford (2003), p. 93: products of square-summable sequences are summable. -/
theorem summable_mul_of_sq {f g : ℕ → ℝ} (hf : Summable (fun j => f j ^ 2))
    (hg : Summable (fun j => g j ^ 2)) : Summable (fun j => f j * g j) := by
  refine Summable.of_norm_bounded ((hf.add hg).div_const 2) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|f j| - |g j|), sq_abs (f j), sq_abs (g j)]

/-- Woodford (2003), p. 93: `Cov(P̂_t, ΔP̂_t) = ∑_j ψ_j (ΔP̂)_j = γ₀ − γ₁`. -/
theorem cov_level_diff {ψ : ℕ → ℝ} (hψ : Summable (fun j => ψ j ^ 2)) :
    ∑' j, ψ j * dpsi ψ j = autocov ψ 0 - autocov ψ 1 := by
  have hs1 : Summable (fun j => ψ (j + 1) ^ 2) := (summable_nat_add_iff 1).mpr hψ
  have hs2 : Summable (fun j => ψ (j + 1) * ψ j) := summable_mul_of_sq hs1 hψ
  have hs3 : Summable (fun j => ψ j * ψ (j + 1)) := summable_mul_of_sq hψ hs1
  have hsum : Summable (fun j => ψ j * dpsi ψ j) := by
    refine (summable_nat_add_iff 1).mp ?_
    have : (fun j => ψ (j + 1) * dpsi ψ (j + 1)) =
        fun j => ψ (j + 1) ^ 2 - ψ (j + 1) * ψ j := by
      funext j
      simp only [dpsi]
      ring
    rw [this]
    exact hs1.sub hs2
  unfold autocov
  rw [hsum.tsum_eq_zero_add,
    (by simpa [sq] using hψ : Summable (fun j => ψ j * ψ (j + 0))).tsum_eq_zero_add]
  have h1 : ∑' j, ψ (j + 1) * dpsi ψ (j + 1) =
      ∑' j, ψ (j + 1) ^ 2 - ∑' j, ψ (j + 1) * ψ j := by
    rw [← hs1.tsum_sub hs2]
    refine tsum_congr fun j => ?_
    simp only [dpsi]
    ring
  have h2 : ∑' j, ψ (j + 1) * ψ (j + 1 + 0) = ∑' j, ψ (j + 1) ^ 2 :=
    tsum_congr fun j => by ring
  have h3 : ∑' j, ψ j * ψ (j + 1) = ∑' j, ψ (j + 1) * ψ j := tsum_congr fun j => by ring
  rw [h1, h2, h3]
  simp only [dpsi, add_zero]
  ring

/-- Woodford (2003), p. 93: `Var(ΔP̂_t) = ∑_j (ΔP̂)_j² = 2(γ₀ − γ₁)`. -/
theorem var_diff {ψ : ℕ → ℝ} (hψ : Summable (fun j => ψ j ^ 2)) :
    ∑' j, dpsi ψ j ^ 2 = 2 * (autocov ψ 0 - autocov ψ 1) := by
  have hs1 : Summable (fun j => ψ (j + 1) ^ 2) := (summable_nat_add_iff 1).mpr hψ
  have hs2 : Summable (fun j => ψ (j + 1) * ψ j) := summable_mul_of_sq hs1 hψ
  have hsum : Summable (fun j => dpsi ψ j ^ 2) := by
    refine (summable_nat_add_iff 1).mp ?_
    have : (fun j => dpsi ψ (j + 1) ^ 2) =
        fun j => ψ (j + 1) ^ 2 - 2 * (ψ (j + 1) * ψ j) + ψ j ^ 2 := by
      funext j
      simp only [dpsi]
      ring
    rw [this]
    exact (hs1.sub (hs2.mul_left 2)).add hψ
  have hc := cov_level_diff hψ
  have hsc : Summable (fun j => ψ j * dpsi ψ j) := by
    refine (summable_nat_add_iff 1).mp ?_
    have : (fun j => ψ (j + 1) * dpsi ψ (j + 1)) =
        fun j => ψ (j + 1) ^ 2 - ψ (j + 1) * ψ j := by
      funext j
      simp only [dpsi]
      ring
    rw [this]
    exact hs1.sub hs2
  -- (Δψ)_j² = 2 ψ_j (Δψ)_j − (ψ_j² − ψ_{j−1}²), and the telescoping part sums to zero
  have htel : ∑' j, dpsi ψ j ^ 2 = 2 * ∑' j, ψ j * dpsi ψ j -
      (∑' j, ψ j ^ 2 - ∑' j, ψ (j + 1) ^ 2 - ψ 0 ^ 2) := by
    rw [hsum.tsum_eq_zero_add, hsc.tsum_eq_zero_add, hψ.tsum_eq_zero_add]
    have : ∑' j, dpsi ψ (j + 1) ^ 2 =
        2 * ∑' j, ψ (j + 1) * dpsi ψ (j + 1) - ∑' j, ψ (j + 1) ^ 2 + ∑' j, ψ j ^ 2 := by
      have e1 : ∑' j, ψ (j + 1) * dpsi ψ (j + 1) =
          ∑' j, ψ (j + 1) ^ 2 - ∑' j, ψ (j + 1) * ψ j := by
        rw [← hs1.tsum_sub hs2]
        refine tsum_congr fun j => ?_
        simp only [dpsi]
        ring
      have e2 : ∑' j, dpsi ψ (j + 1) ^ 2 =
          ∑' j, ψ (j + 1) ^ 2 - 2 * ∑' j, ψ (j + 1) * ψ j + ∑' j, ψ j ^ 2 := by
        rw [← tsum_mul_left, ← hs1.tsum_sub (hs2.mul_left 2),
          ← (hs1.sub (hs2.mul_left 2)).tsum_add hψ]
        refine tsum_congr fun j => ?_
        simp only [dpsi]
        ring
      rw [e2, e1]
      ring
    rw [this, hψ.tsum_eq_zero_add]
    simp only [dpsi]
    ring
  rw [htel, hc, hψ.tsum_eq_zero_add]
  ring

/-- Woodford (2003), p. 93: if `ψ` is not identically zero then `Var(ΔP̂) > 0`, i.e. `γ₀ > γ₁`. -/
theorem var_diff_pos {ψ : ℕ → ℝ} (hψ : Summable (fun j => ψ j ^ 2)) (hne : ∃ j, ψ j ≠ 0) :
    0 < ∑' j, dpsi ψ j ^ 2 := by
  have hsum : Summable (fun j => dpsi ψ j ^ 2) := by
    have hs1 : Summable (fun j => ψ (j + 1) ^ 2) := (summable_nat_add_iff 1).mpr hψ
    have hs2 : Summable (fun j => ψ (j + 1) * ψ j) := summable_mul_of_sq hs1 hψ
    refine (summable_nat_add_iff 1).mp ?_
    have : (fun j => dpsi ψ (j + 1) ^ 2) =
        fun j => ψ (j + 1) ^ 2 - 2 * (ψ (j + 1) * ψ j) + ψ j ^ 2 := by
      funext j
      simp only [dpsi]
      ring
    rw [this]
    exact (hs1.sub (hs2.mul_left 2)).add hψ
  -- some increment is nonzero
  have hex : ∃ j, dpsi ψ j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply (show ¬ ∃ j, ψ j ≠ 0 from ?_) hne
    push Not
    intro j
    induction j with
    | zero => simpa [dpsi] using hall 0
    | succ j ih =>
      have := hall (j + 1)
      simp only [dpsi] at this
      linarith
  obtain ⟨j, hj⟩ := hex
  exact hsum.tsum_pos (fun _ => sq_nonneg _) j (by positivity)

/-- Woodford (2003), p. 93: under the Wicksellian rule with `ν = 0`, `î_t = φ_p P̂_t`, and with a
deterministic trend in `P*`, `π_t = ΔP̂_t + const`. For any stationary (MA(∞), square-summable,
not identically zero) `P̂`, the population coefficient of a regression of `î_t` on `π_t` is
`Cov(φ_p P̂_t, ΔP̂_t)/Var(ΔP̂_t) = φ_p/2`. -/
theorem regression_coefficient (φp : ℝ) {ψ : ℕ → ℝ} (hψ : Summable (fun j => ψ j ^ 2))
    (hne : ∃ j, ψ j ≠ 0) :
    (∑' j, (φp * ψ j) * dpsi ψ j) / ∑' j, dpsi ψ j ^ 2 = φp / 2 := by
  have hpos := var_diff_pos hψ hne
  have hcov : ∑' j, (φp * ψ j) * dpsi ψ j = φp * (autocov ψ 0 - autocov ψ 1) := by
    simp_rw [mul_assoc]
    rw [tsum_mul_left, cov_level_diff hψ]
  rw [hcov, var_diff hψ]
  have hd : autocov ψ 0 - autocov ψ 1 ≠ 0 := by
    intro h
    rw [var_diff hψ, h, mul_zero] at hpos
    exact lt_irrefl _ hpos
  field_simp

end Woodford.PriceLevelDetermination.TaylorPrinciple
