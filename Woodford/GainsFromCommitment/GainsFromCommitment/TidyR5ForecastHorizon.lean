/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.OptimalTaylor

/-!
# Forecast-based rules: the exact determinacy criterion for every horizon

Woodford (2003), *Interest and Prices*, Chapter 7, §3.2, eq. (3.13)–(3.14) and Proposition 7.13
(p. 516), footnotes 35–37.

The earlier formalisation (OptimalTaylor) proves Prop. 7.13 in the book's form (indeterminacy
for all horizons beyond an explicit critical value) and the exact criterion only for `k = 1`.
Here the exact criterion is proved for **every** horizon `k ≥ 1`.

## Main results

* A general theory of scalar expectational difference equations
  `∑_{j ≤ n+1} c_j E_t p_{t+j} = g_t` with `c_0 = 1` (`ScalarSolves`): for every bounded adapted
  `g` there is exactly one bounded adapted solution **iff** every complex root of
  `P(z) = ∑ c_j z^j` lies strictly outside the unit circle (`scalarDet_iff`). Sufficiency goes
  through the companion forward system (`companion`, `companion_eig`, Blanchard–Kahn restated
  from the Chapter 4 project); necessity through the bounded homogeneous solutions `Re λᵗ`.
* Under the forecast-based rule (3.13) with horizon `k ≥ 1`, an equilibrium is exactly a bounded
  adapted solution of the scalar equation with characteristic polynomial `OptimalTaylor.chiC` of
  Prop. 7.13 (`forecastEqm_iff_scalar`).
* **Prop. 7.13, exact for every horizon** (`forecast_determinate_iff`): under (3.13) with any
  `k ≥ 1` and any real `φ_π, φ_x`, equilibrium is determinate iff every root of
  `χ(λ) = (1 − λ)(1 − βλ) − κσλ + κσφ_π λᵏ + σφ_x λᵏ(1 − βλ)/4` has `|λ| > 1`; for the rule
  (3.14) consistent with the optimal noninertial plan this is `oni_forecast_determinate_iff`.
-/

namespace Woodford.GainsFromCommitment.TidyR5ForecastHorizon

open Filter Topology
open OptimalTaylor (rvMul rvMul_apply FSolves VAdapted VBounded fsolves_exists fsolves_unique
  pow_entry_bound chiC forecastRule ForecastEqm ModelDet indeterminate_of_root)
open Noninertial (AS IS)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### Scalar expectational difference equations -/

/-- Woodford (2003), Prop. 7.13, p. 516 (the reduced form of (3.13)): `p` solves the scalar
expectational equation `∑_{j ≤ n+1} c_j E_t p_{t+j} = g_t`, date by date and state by state. -/
def ScalarSolves (c : ℕ → ℝ) (n : ℕ) (g p : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, ∑ j ∈ Finset.range (n + 2), c j * 𝔼.E t (p (t + j)) ω = g t ω

/-- Woodford (2003), Prop. 7.13, p. 516 (determinacy of the reduced form): for every bounded
adapted `g` the scalar equation has exactly one bounded adapted solution. -/
def ScalarDet (c : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ g : ℕ → Ω → ℝ, BoundedProc g → 𝔼.Adapted g →
    ∃! p : ℕ → Ω → ℝ, BoundedProc p ∧ 𝔼.Adapted p ∧ ScalarSolves 𝔼 c n g p

/-- Woodford (2003), Prop. 7.13, p. 516 (the companion matrix of the reduced form): the state is
`(E_t p_t, E_t p_{t+1}, …, E_t p_{t+n})`; row `0` is `−(c_1, …, c_{n+1})`, row `m + 1` picks
coordinate `m`. -/
noncomputable def companion (c : ℕ → ℝ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if (i : ℕ) = 0 then -c ((j : ℕ) + 1) else if (j : ℕ) + 1 = i then 1 else 0

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (tool): row `0` of the companion system. -/
theorem companion_row_zero (c : ℕ → ℝ) (n : ℕ) (a : Fin (n + 1) → Ω → ℝ) (ω : Ω) :
    rvMul (companion c n) a 0 ω = -∑ j : Fin (n + 1), c ((j : ℕ) + 1) * a j ω := by
  rw [rvMul_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [companion]

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (tool): row `m + 1` of the companion system is coordinate `m`. -/
theorem companion_row_succ (c : ℕ → ℝ) (n : ℕ) (a : Fin (n + 1) → Ω → ℝ) (m : Fin n) (ω : Ω) :
    rvMul (companion c n) a m.succ ω = a m.castSucc ω := by
  rw [rvMul_apply, Finset.sum_eq_single m.castSucc]
  · simp [companion]
  · intro j _ hj
    have : (j : ℕ) ≠ (m : ℕ) := fun h => hj (Fin.ext (by simpa using h))
    simp [companion, this]
  · simp

/-- Woodford (2003), Prop. 7.13 (tool): the forcing of the companion system, `(g_t, 0, …, 0)`. -/
noncomputable def compForcing (n : ℕ) (g : ℕ → Ω → ℝ) : ℕ → Fin (n + 1) → Ω → ℝ :=
  fun t i => if (i : ℕ) = 0 then g t else 0

/-- Woodford (2003), Prop. 7.13 (tool): the stacked forecasts `(E_t p_{t+i})_{i ≤ n}`. -/
def stackP (n : ℕ) (p : ℕ → Ω → ℝ) : ℕ → Fin (n + 1) → Ω → ℝ :=
  fun t i => 𝔼.E t (p (t + i))

/-- Woodford (2003), Prop. 7.13 (tool): a scalar solution gives a solution of the companion
forward system. -/
theorem stackP_fsolves {c : ℕ → ℝ} (hc : c 0 = 1) {n : ℕ} {g p : ℕ → Ω → ℝ}
    (hp : 𝔼.Adapted p) (hs : ScalarSolves 𝔼 c n g p) :
    FSolves 𝔼 (companion c n) (compForcing n g) (stackP 𝔼 n p) := by
  intro t
  funext i ω
  have hT : ∀ x : Ω → ℝ, 𝔼.E t (𝔼.E (t + 1) x) = 𝔼.E t x := fun x => 𝔼.tower (Nat.le_succ t) x
  refine Fin.cases ?_ (fun m => ?_) i
  · simp only [Pi.add_apply, companion_row_zero, compForcing, Fin.val_zero, ↓reduceIte, stackP,
      hT, add_zero, hp t]
    have h := hs t ω
    rw [Finset.sum_range_succ', hc, add_zero, one_mul, hp t] at h
    have e : ∑ j : Fin (n + 1), c ((j : ℕ) + 1) * 𝔼.E t (p (t + 1 + (j : ℕ))) ω =
        ∑ j ∈ Finset.range (n + 1), c (j + 1) * 𝔼.E t (p (t + (j + 1))) ω := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => c (j + 1) * 𝔼.E t (p (t + (j + 1))) ω)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.add_right_comm t 1, add_assoc]
    rw [e]
    linarith
  · simp only [Pi.add_apply, companion_row_succ, compForcing, Fin.val_succ,
      Nat.add_one_ne_zero, ↓reduceIte, Fin.val_castSucc, stackP, hT, Pi.zero_apply]
    rw [add_zero, show t + 1 + (m : ℕ) = t + ((m : ℕ) + 1) by omega]

/-- Woodford (2003), Prop. 7.13 (tool): every adapted solution of the companion system is the
stack of the forecasts of its first coordinate. -/
theorem fsolves_stack {c : ℕ → ℝ} {n : ℕ} {g : ℕ → Ω → ℝ} {s : ℕ → Fin (n + 1) → Ω → ℝ}
    (hs : FSolves 𝔼 (companion c n) (compForcing n g) s) (has : VAdapted 𝔼 s) :
    ∀ (m : ℕ) (hm : m < n + 1) t, s t ⟨m, hm⟩ = 𝔼.E t (s (t + m) 0) := by
  intro m
  induction m with
  | zero => intro hm t; exact (has t _).symm
  | succ m ih =>
    intro hm t
    have hm' : m < n := by omega
    have h := congrFun (hs t) (Fin.succ ⟨m, hm'⟩)
    simp only [Pi.add_apply, compForcing, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte,
      add_zero] at h
    have h' : s t ⟨m + 1, hm⟩ = 𝔼.E t (s (t + 1) ⟨m, by omega⟩) := by
      have e : (⟨m + 1, hm⟩ : Fin (n + 1)) = Fin.succ ⟨m, hm'⟩ := rfl
      rw [e, h]
      funext ω
      rw [companion_row_succ]
      rfl
    rw [h', ih (by omega) (t + 1), 𝔼.tower (Nat.le_succ t), Nat.add_right_comm t 1, add_assoc]

/-- Woodford (2003), Prop. 7.13 (tool): the first coordinate of an adapted solution of the
companion system solves the scalar equation. -/
theorem scalar_of_fsolves {c : ℕ → ℝ} (hc : c 0 = 1) {n : ℕ} {g : ℕ → Ω → ℝ}
    {s : ℕ → Fin (n + 1) → Ω → ℝ} (hs : FSolves 𝔼 (companion c n) (compForcing n g) s)
    (has : VAdapted 𝔼 s) : ScalarSolves 𝔼 c n g (fun t => s t 0) := by
  intro t ω
  have hst := fsolves_stack 𝔼 hs has
  have h0 := congrFun (congrFun (hs t) 0) ω
  simp only [Pi.add_apply, companion_row_zero, compForcing, Fin.val_zero, ↓reduceIte] at h0
  rw [Finset.sum_range_succ', hc, one_mul, add_zero, has t 0]
  have e : ∑ j : Fin (n + 1), c ((j : ℕ) + 1) * 𝔼.E t (s (t + 1) j) ω =
      ∑ j ∈ Finset.range (n + 1), c (j + 1) * 𝔼.E t (s (t + (j + 1)) 0) ω := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => c (j + 1) * 𝔼.E t (s (t + (j + 1)) 0) ω)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hst j j.isLt (t + 1)
    simp only [Fin.eta] at this
    rw [this, 𝔼.tower (Nat.le_succ t), Nat.add_right_comm t 1, add_assoc]
  rw [e] at h0
  linarith

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (tool): if every root of `P(z) = ∑ c_j z^j` (`c_0 = 1`) lies
outside the closed unit disc, every complex eigenvalue of the companion matrix lies inside the
open unit disc (an eigenvalue `w ≠ 0` has `P(1/w) = 0`). -/
theorem companion_eig {c : ℕ → ℝ} (hc : c 0 = 1) {n : ℕ}
    (hroot : ∀ z : ℂ, ∑ j ∈ Finset.range (n + 2), (c j : ℂ) * z ^ j = 0 → 1 < ‖z‖) (w : ℂ)
    (hw : (Matrix.scalar (Fin (n + 1)) w - (companion c n).map Complex.ofReal).det = 0) :
    ‖w‖ < 1 := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hw
  have hrow : ∀ i, w * v i = ∑ j, ((companion c n i j : ℝ) : ℂ) * v j := by
    intro i
    have := congrFun hv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal,
      Pi.zero_apply] at this
    rw [sub_eq_zero] at this
    rw [this]
    simp [Matrix.mulVec, dotProduct]
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero]; exact one_pos
  have hsucc : ∀ m : Fin n, v m.castSucc = w * v m.succ := by
    intro m
    rw [hrow m.succ, Finset.sum_eq_single m.castSucc]
    · simp [companion]
    · intro j _ hj
      have : (j : ℕ) ≠ (m : ℕ) := fun h => hj (Fin.ext (by simpa using h))
      simp [companion, this]
    · simp
  have hpow : ∀ (m : ℕ) (hm : m < n + 1), v ⟨m, hm⟩ = w⁻¹ ^ m * v 0 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have h := hsucc ⟨m, by omega⟩
      have e1 : (Fin.castSucc ⟨m, by omega⟩ : Fin (n + 1)) = ⟨m, by omega⟩ := rfl
      have e2 : (Fin.succ ⟨m, by omega⟩ : Fin (n + 1)) = ⟨m + 1, hm⟩ := rfl
      rw [e1, e2, ih (by omega)] at h
      rw [pow_succ]
      field_simp
      linear_combination -h
  have hv00 : v 0 ≠ 0 := by
    intro h0
    apply hv0
    funext i
    have := hpow i i.isLt
    simp only [Fin.eta, h0, mul_zero] at this
    simpa using this
  have h0 := hrow 0
  have e : ∑ j, ((companion c n 0 j : ℝ) : ℂ) * v j =
      -(∑ j ∈ Finset.range (n + 1), (c (j + 1) : ℂ) * w⁻¹ ^ j) * v 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (c (j + 1) : ℂ) * w⁻¹ ^ j), neg_mul,
      Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show v j = v ⟨j, j.isLt⟩ from rfl, hpow j j.isLt]
    simp [companion]
    ring
  rw [e] at h0
  have hP : ∑ j ∈ Finset.range (n + 2), (c j : ℂ) * w⁻¹ ^ j = 0 := by
    rw [Finset.sum_range_succ', hc]
    have h1 : w + ∑ j ∈ Finset.range (n + 1), (c (j + 1) : ℂ) * w⁻¹ ^ j = 0 := by
      have := mul_right_cancel₀ hv00 (show w * v 0 = (-(∑ j ∈ Finset.range (n + 1),
        (c (j + 1) : ℂ) * w⁻¹ ^ j)) * v 0 from h0)
      linear_combination this
    have h2 : ∑ j ∈ Finset.range (n + 1), (c (j + 1) : ℂ) * w⁻¹ ^ (j + 1) =
        w⁻¹ * ∑ j ∈ Finset.range (n + 1), (c (j + 1) : ℂ) * w⁻¹ ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [h2]
    have h3 : w⁻¹ * w = 1 := inv_mul_cancel₀ hw0
    push_cast
    linear_combination w⁻¹ * h1 - h3
  have := hroot _ hP
  rw [norm_inv] at this
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [lt_inv_comm₀ one_pos hn, inv_one] at this
  exact this


/-- Woodford (2003), Prop. 7.13 (tool): the stacked forecasts of a bounded process are bounded. -/
theorem stackP_bounded {n : ℕ} {p : ℕ → Ω → ℝ} (hp : BoundedProc p) : VBounded (stackP 𝔼 n p) := by
  obtain ⟨M, hM⟩ := hp
  exact ⟨M, fun t i ω => 𝔼.abs_E_le (hM (t + i)) t ω⟩

/-- Woodford (2003), Prop. 7.13 (tool): the stacked forecasts are adapted. -/
theorem stackP_adapted (n : ℕ) (p : ℕ → Ω → ℝ) : VAdapted 𝔼 (stackP 𝔼 n p) :=
  fun t _ => 𝔼.E_E_self t _

/-- Woodford (2003), Prop. 7.13 (sufficiency): if every complex root of `P(z) = ∑ c_j z^j`
(`c_0 = 1`) has modulus `> 1`, the scalar equation has exactly one bounded adapted solution for
every bounded adapted forcing. -/
theorem scalarDet_of_roots {c : ℕ → ℝ} (hc : c 0 = 1) {n : ℕ}
    (hroot : ∀ z : ℂ, ∑ j ∈ Finset.range (n + 2), (c j : ℂ) * z ^ j = 0 → 1 < ‖z‖) :
    ScalarDet 𝔼 c n := by
  obtain ⟨Cb, ρ, -, hρ0, hρ1, hK⟩ := pow_entry_bound (companion c n) (companion_eig hc hroot)
  intro g hg hag
  obtain ⟨Mg, hMg⟩ := hg
  have hw : ∀ t i ω, |compForcing n g t i ω| ≤ |Mg| := by
    intro t i ω
    by_cases h : (i : ℕ) = 0
    · simp only [compForcing, h, ↓reduceIte]; exact (hMg t ω).trans (le_abs_self _)
    · simp [compForcing, h]
  have haw : VAdapted 𝔼 (compForcing n g) := by
    intro t i
    by_cases h : (i : ℕ) = 0
    · simp only [compForcing, h, ↓reduceIte]; exact hag t
    · simp only [compForcing, h, ↓reduceIte, map_zero]
  obtain ⟨s, hs, has, hbs⟩ := fsolves_exists 𝔼 hρ0.le hρ1 hK hw haw
  obtain ⟨Ms, hMs⟩ := hbs
  refine ⟨fun t => s t 0, ⟨⟨Ms, fun t ω => hMs t 0 ω⟩, fun t => has t 0,
    scalar_of_fsolves 𝔼 hc hs has⟩, fun q ⟨hqb, hqa, hqs⟩ => ?_⟩
  have h1 := stackP_fsolves 𝔼 hc hqa hqs
  have := fsolves_unique 𝔼 hρ0.le hρ1 hK h1 hs (stackP_adapted 𝔼 n q) has
    (stackP_bounded 𝔼 hqb) ⟨Ms, hMs⟩
  funext t ω
  have h2 := congrFun (congrFun (congrFun this t) 0) ω
  simpa [stackP, hqa t] using h2

/-- Woodford (2003), Prop. 7.13 (necessity): if `P` has a root `λ` with `|λ| ≤ 1`, then
`p_t = Re λᵗ` is a bounded adapted nonzero solution of the homogeneous equation, so the scalar
equation is not determinate. -/
theorem roots_of_scalarDet [Nonempty Ω] {c : ℕ → ℝ} {n : ℕ} (h : ScalarDet 𝔼 c n) :
    ∀ z : ℂ, ∑ j ∈ Finset.range (n + 2), (c j : ℂ) * z ^ j = 0 → 1 < ‖z‖ := by
  intro z hz
  by_contra hle
  push Not at hle
  have hE : ∀ t (a : ℝ) ω, 𝔼.E t (fun _ => a) ω = a := fun t a ω => by rw [𝔼.const]
  set p : ℕ → Ω → ℝ := fun t _ => (z ^ t).re with hp
  have hps : ScalarSolves 𝔼 c n 0 p := by
    intro t ω
    simp only [hp, hE, Pi.zero_apply]
    have e : ∑ j ∈ Finset.range (n + 2), c j * (z ^ (t + j)).re =
        (z ^ t * ∑ j ∈ Finset.range (n + 2), (c j : ℂ) * z ^ j).re := by
      rw [Finset.mul_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add, show z ^ t * ((c j : ℂ) * z ^ j) = (c j : ℂ) * (z ^ t * z ^ j) by ring,
        Complex.re_ofReal_mul]
    rw [e, hz, mul_zero, Complex.zero_re]
  have hzs : ScalarSolves 𝔼 c n 0 0 := by
    intro t ω
    simp
  obtain ⟨q, -, hq⟩ := h 0 ⟨0, fun _ _ => by simp⟩ (fun t => map_zero _)
  have hpb : BoundedProc p := ⟨1, fun t _ => (Complex.abs_re_le_norm _).trans
    (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hle)⟩
  have e1 := hq p ⟨hpb, fun t => 𝔼.const t _, hps⟩
  have e2 := hq 0 ⟨⟨0, fun _ _ => by simp⟩, fun t => map_zero _, hzs⟩
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have := congrFun (congrFun (e1.trans e2.symm) 0) ω
  simp [hp] at this

/-- **The exact determinacy criterion for scalar expectational equations** (Woodford (2003),
Prop. 7.13, p. 516, and App. C restated for one equation of any order): with `c_0 = 1`, the
equation `∑_{j ≤ n+1} c_j E_t p_{t+j} = g_t` has exactly one bounded adapted solution for every
bounded adapted `g` iff every complex root of `∑ c_j z^j` lies strictly outside the unit circle. -/
theorem scalarDet_iff [Nonempty Ω] {c : ℕ → ℝ} (hc : c 0 = 1) (n : ℕ) :
    ScalarDet 𝔼 c n ↔
      ∀ z : ℂ, ∑ j ∈ Finset.range (n + 2), (c j : ℂ) * z ^ j = 0 → 1 < ‖z‖ :=
  ⟨roots_of_scalarDet 𝔼, scalarDet_of_roots 𝔼 hc⟩

/-! ### The model under the forecast-based rule (3.13) -/

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13, p. 516: the coefficients `c_j` of `χ(λ) = ∑ c_j λʲ`,
`χ(λ) = 1 − (1 + β + κσ)λ + βλ² + (κσφ_π + σφ_x/4)λᵏ − (σβφ_x/4)λ^{k+1}`. -/
noncomputable def fcCoef (β κ σ φπ φx : ℝ) (k j : ℕ) : ℝ :=
  (if j = 0 then 1 else 0) + (if j = 1 then -(1 + β + κ * σ) else 0) + (if j = 2 then β else 0) +
    (if j = k then κ * σ * φπ + σ * φx / 4 else 0) + (if j = k + 1 then -(σ * β * φx / 4) else 0)

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (tool): `c_0 = 1` for every horizon `k ≥ 1`. -/
theorem fcCoef_zero {β κ σ φπ φx : ℝ} {k : ℕ} (hk : 1 ≤ k) : fcCoef β κ σ φπ φx k 0 = 1 := by
  have h1 : (0 : ℕ) ≠ k := by omega
  simp [fcCoef, h1]

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (tool): the coefficient sum, for a real sequence `a`. -/
theorem fcCoef_sum {β κ σ φπ φx : ℝ} {k : ℕ} (hk : 1 ≤ k) (a : ℕ → ℝ) :
    ∑ j ∈ Finset.range (k + 2), fcCoef β κ σ φπ φx k j * a j =
      a 0 - (1 + β + κ * σ) * a 1 + β * a 2 + (κ * σ * φπ + σ * φx / 4) * a k -
        σ * β * φx / 4 * a (k + 1) := by
  have h0 : 0 < k + 2 := by omega
  have h1 : 1 < k + 2 := by omega
  have h2 : 2 < k + 2 := by omega
  have h3 : k < k + 2 := by omega
  have h4 : k + 1 < k + 2 := by omega
  simp only [fcCoef, add_mul, ite_mul, zero_mul, one_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_range, h0, h1, h2, h3, h4, ↓reduceIte]
  ring

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (tool): `∑ c_j zʲ = χ(z)` over `ℂ`. -/
theorem fcCoef_chiC {β κ σ φπ φx : ℝ} {k : ℕ} (hk : 1 ≤ k) (z : ℂ) :
    ∑ j ∈ Finset.range (k + 2), (fcCoef β κ σ φπ φx k j : ℂ) * z ^ j =
      chiC β κ σ φπ φx k z := by
  have h0 : 0 < k + 2 := by omega
  have h1 : 1 < k + 2 := by omega
  have h2 : 2 < k + 2 := by omega
  have h3 : k < k + 2 := by omega
  have h4 : k + 1 < k + 2 := by omega
  simp only [fcCoef, Complex.ofReal_add, apply_ite Complex.ofReal, Complex.ofReal_zero,
    Complex.ofReal_one, add_mul, ite_mul, zero_mul, one_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_range, h0, h1, h2, h3, h4, ↓reduceIte]
  unfold chiC
  push_cast
  ring

omit 𝔼 in
/-- Woodford (2003), Prop. 7.13 (the forcing of the reduced form):
`g_t = u_t − E_t u_{t+1} + (σφ_x/4) E_t u_{t+k} + κσ(rⁿ_t − ī + π̄)`. -/
noncomputable def fcG {Ω' : Type*} (𝔼' : ExpectationSystem Ω') (σ κ φx ibar πbar : ℝ) (k : ℕ)
    (u rn : ℕ → Ω' → ℝ) : ℕ → Ω' → ℝ :=
  fun t ω => u t ω - 𝔼'.E t (u (t + 1)) ω + σ * φx / 4 * 𝔼'.E t (u (t + k)) ω +
    κ * σ * (rn t ω - ibar + πbar)

/-- Woodford (2003), (2.1) (tool): applying `E_t` to the aggregate-supply relation at `t + j`. -/
theorem AS_forecast {β κ : ℝ} {π x u : ℕ → Ω → ℝ} (hA : AS 𝔼 β κ π x u) (t j : ℕ) (ω : Ω) :
    𝔼.E t (π (t + j)) ω = κ * 𝔼.E t (x (t + j)) ω + β * 𝔼.E t (π (t + j + 1)) ω +
      𝔼.E t (u (t + j)) ω := by
  have h := congrArg (fun y => 𝔼.E t y ω) (hA (t + j))
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    𝔼.tower (Nat.le_add_right t j)] at h
  exact h

/-- **The reduced form of (3.13)** (Woodford (2003), p. 516, and Ch. 4, §2.2): with `κ ≠ 0`,
`k ≥ 1` and `κ x̄ = (1 − β) π̄`, adapted `(π, x)` is an equilibrium under the forecast-based rule
iff it satisfies (2.1) and `π − π̄` solves the scalar equation with characteristic polynomial
`χ` of Prop. 7.13 and forcing `fcG`. -/
theorem forecastEqm_iff_scalar {β σ κ ibar φπ φx πbar xbar : ℝ} (hκ : κ ≠ 0) {k : ℕ}
    (hk : 1 ≤ k) (hxb : κ * xbar = (1 - β) * πbar) {u rn π x : ℕ → Ω → ℝ}
    (hπa : 𝔼.Adapted π) (hxa : 𝔼.Adapted x) (hua : 𝔼.Adapted u) :
    ForecastEqm 𝔼 β σ κ ibar φπ φx πbar xbar k u rn π x ↔
      AS 𝔼 β κ π x u ∧ ScalarSolves 𝔼 (fcCoef β κ σ φπ φx k) k
        (fcG 𝔼 σ κ φx ibar πbar k u rn) (fun t ω => π t ω - πbar) := by
  have hE : ∀ t j ω, 𝔼.E t (fun ω' => π (t + j) ω' - πbar) ω = 𝔼.E t (π (t + j)) ω - πbar := by
    intro t j ω
    have e : (fun ω' => π (t + j) ω' - πbar) = π (t + j) - fun _ => πbar := rfl
    rw [e, map_sub, 𝔼.const]
    rfl
  unfold ForecastEqm ScalarSolves
  refine and_congr_right fun hA => ?_
  rw [OptimalTaylor.IS_iff]
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  rw [fcCoef_sum hk (fun j => 𝔼.E t (fun ω' => π (t + j) ω' - πbar) ω)]
  have hE0 : 𝔼.E t (fun ω' => π (t + 0) ω' - πbar) ω = π t ω - πbar := by
    rw [hE, add_zero, hπa t]
  rw [hE0, hE, hE, hE, hE]
  have a0 := AS_forecast 𝔼 hA t 0 ω
  have a1 := AS_forecast 𝔼 hA t 1 ω
  have ak := AS_forecast 𝔼 hA t k ω
  simp only [add_zero] at a0
  rw [hπa t, hxa t, hua t] at a0
  simp only [forecastRule, fcG]
  constructor
  · intro hI
    linear_combination κ * hI + a0 - a1 + σ * φx / 4 * ak + σ * φx / 4 * hxb
  · intro hS
    have : κ * (x t ω - (𝔼.E t (x (t + 1)) ω - σ * (ibar + φπ * (𝔼.E t (π (t + k)) ω - πbar) +
        φx * (𝔼.E t (x (t + k)) ω - xbar) / 4 - 𝔼.E t (π (t + 1)) ω - rn t ω))) = 0 := by
      linear_combination hS - a0 + a1 - σ * φx / 4 * ak - σ * φx / 4 * hxb
    linarith [(mul_eq_zero.mp this).resolve_left hκ]


/-! ### Proposition 7.13: the exact criterion for every horizon -/

/-- Woodford (2003), (3.13) (tool): the forcing `fcG` of bounded adapted disturbances is bounded
and adapted. -/
theorem fcG_bdd_adapted {σ κ φx ibar πbar : ℝ} {k : ℕ} {u rn : ℕ → Ω → ℝ} (hu : BoundedProc u)
    (hrn : BoundedProc rn) (hau : 𝔼.Adapted u) (harn : 𝔼.Adapted rn) :
    BoundedProc (fcG 𝔼 σ κ φx ibar πbar k u rn) ∧ 𝔼.Adapted (fcG 𝔼 σ κ φx ibar πbar k u rn) := by
  obtain ⟨M, hM⟩ := hu
  obtain ⟨N, hN⟩ := hrn
  refine ⟨⟨M + M + |σ * φx / 4| * M + |κ * σ| * (N + |ibar| + |πbar|), fun t ω => ?_⟩,
    fun t => ?_⟩
  · simp only [fcG]
    have h1 := hM t ω
    have h2 := 𝔼.abs_E_le (hM (t + 1)) t ω
    have h3 : |σ * φx / 4 * 𝔼.E t (u (t + k)) ω| ≤ |σ * φx / 4| * M := by
      rw [abs_mul]; gcongr; exact 𝔼.abs_E_le (hM (t + k)) t ω
    have h4 : |κ * σ * (rn t ω - ibar + πbar)| ≤ |κ * σ| * (N + |ibar| + |πbar|) := by
      rw [abs_mul]
      gcongr
      calc |rn t ω - ibar + πbar| ≤ |rn t ω - ibar| + |πbar| := abs_add_le _ _
        _ ≤ |rn t ω| + |ibar| + |πbar| := by gcongr; exact abs_sub _ _
        _ ≤ N + |ibar| + |πbar| := by gcongr; exact hN t ω
    calc _ ≤ |u t ω - 𝔼.E t (u (t + 1)) ω + σ * φx / 4 * 𝔼.E t (u (t + k)) ω| +
          |κ * σ * (rn t ω - ibar + πbar)| := abs_add_le _ _
      _ ≤ |u t ω - 𝔼.E t (u (t + 1)) ω| + |σ * φx / 4 * 𝔼.E t (u (t + k)) ω| +
          |κ * σ * (rn t ω - ibar + πbar)| := by gcongr; exact abs_add_le _ _
      _ ≤ |u t ω| + |𝔼.E t (u (t + 1)) ω| + |σ * φx / 4 * 𝔼.E t (u (t + k)) ω| +
          |κ * σ * (rn t ω - ibar + πbar)| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  · have e : fcG 𝔼 σ κ φx ibar πbar k u rn t = u t - 𝔼.E t (u (t + 1)) +
        (σ * φx / 4) • 𝔼.E t (u (t + k)) + (κ * σ) • rn t +
          (fun _ => κ * σ * (πbar - ibar)) := by
      funext ω
      simp only [fcG, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, map_add, map_add, map_add, map_sub, map_smul, map_smul, 𝔼.E_E_self, 𝔼.E_E_self,
      hau t, harn t, 𝔼.const]

/-- **Proposition 7.13, exact for every horizon** (Woodford (2003), p. 516; proof in Giannoni and
Woodford, only cited in the book): under the forecast-based rule (3.13) with any horizon `k ≥ 1`
and any real `φ_π, φ_x` (`κ ≠ 0`, `κ x̄ = (1 − β) π̄`), equilibrium is determinate — exactly one
bounded adapted equilibrium for every bounded adapted `(u, rⁿ)` — iff every complex root of
`χ(λ) = (1 − λ)(1 − βλ) − κσλ + κσφ_π λᵏ + σφ_x λᵏ(1 − βλ)/4` has `|λ| > 1`. -/
theorem forecast_determinate_iff [Nonempty Ω] {β σ κ ibar φπ φx πbar xbar : ℝ} (hκ : κ ≠ 0)
    {k : ℕ} (hk : 1 ≤ k) (hxb : κ * xbar = (1 - β) * πbar) :
    ModelDet 𝔼 (ForecastEqm 𝔼 β σ κ ibar φπ φx πbar xbar k) ↔
      ∀ z : ℂ, chiC β κ σ φπ φx k z = 0 → 1 < ‖z‖ := by
  constructor
  · intro hdet z hz
    by_contra hle
    push Not at hle
    have hE : ∀ t (a : ℝ) ω, 𝔼.E t (fun _ => a) ω = a := fun t a ω => by rw [𝔼.const]
    have heq : ForecastEqm 𝔼 β σ κ ibar φπ φx πbar xbar k (fun _ _ => 0)
        (fun _ _ => ibar - πbar) (fun _ _ => πbar) (fun _ _ => xbar) := by
      refine ⟨(OptimalTaylor.AS_iff 𝔼 _ _ _ _ _).mpr fun t ω => ?_,
        (OptimalTaylor.IS_iff 𝔼 _ _ _ _ _).mpr fun t ω => ?_⟩
      · rw [hE]; linear_combination -hxb
      · simp only [hE, forecastRule]; ring
    obtain ⟨π', x', h1, h2, h3, h4, h5, hne⟩ := indeterminate_of_root 𝔼 hκ hz hle heq
      ⟨|πbar|, fun _ _ => le_rfl⟩ ⟨|xbar|, fun _ _ => le_rfl⟩ (fun t => 𝔼.const t _)
      (fun t => 𝔼.const t _)
    obtain ⟨p, -, hpu⟩ := hdet (fun _ _ => 0) (fun _ _ => ibar - πbar) ⟨0, fun _ _ => by simp⟩
      ⟨|ibar - πbar|, fun _ _ => le_rfl⟩ (fun t => 𝔼.const t 0) (fun t => 𝔼.const t _)
    have e1 := hpu (π', x') ⟨h2, h3, h4, h5, h1⟩
    have e2 := hpu (fun _ _ => πbar, fun _ _ => xbar) ⟨⟨|πbar|, fun _ _ => le_rfl⟩,
      ⟨|xbar|, fun _ _ => le_rfl⟩, fun t => 𝔼.const t _, fun t => 𝔼.const t _, heq⟩
    exact hne (congrArg Prod.fst (e1.trans e2.symm))
  · intro hroot u rn hu hrn hau harn
    have hdet := scalarDet_of_roots 𝔼 (fcCoef_zero (β := β) (κ := κ) (σ := σ) (φπ := φπ)
      (φx := φx) hk) (n := k) (fun z hz => hroot z (by rwa [fcCoef_chiC hk] at hz))
    obtain ⟨hgb, hga⟩ := fcG_bdd_adapted 𝔼 (σ := σ) (κ := κ) (φx := φx) (ibar := ibar)
      (πbar := πbar) (k := k) hu hrn hau harn
    obtain ⟨p, ⟨hpb, hpa, hps⟩, hpu⟩ := hdet _ hgb hga
    set π : ℕ → Ω → ℝ := fun t ω => πbar + p t ω with hπ
    set x : ℕ → Ω → ℝ := fun t ω => (π t ω - β * 𝔼.E t (π (t + 1)) ω - u t ω) / κ with hx
    have hπa : 𝔼.Adapted π := by
      intro t
      have e : π t = (fun _ => πbar) + p t := rfl
      rw [e, map_add, 𝔼.const, hpa t]
    have hxa : 𝔼.Adapted x := by
      intro t
      have e : x t = κ⁻¹ • π t - (κ⁻¹ * β) • 𝔼.E t (π (t + 1)) - κ⁻¹ • u t := by
        funext ω
        simp only [hx, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [e, map_sub, map_sub, map_smul, map_smul, map_smul, hπa t, 𝔼.E_E_self, hau t]
    have hA : AS 𝔼 β κ π x u := by
      refine (OptimalTaylor.AS_iff 𝔼 _ _ _ _ _).mpr fun t ω => ?_
      simp only [hx]
      field_simp
      ring
    have hpπ : (fun t ω => π t ω - πbar) = p := by
      funext t ω; simp [hπ]
    have heq : ForecastEqm 𝔼 β σ κ ibar φπ φx πbar xbar k u rn π x := by
      rw [forecastEqm_iff_scalar 𝔼 hκ hk hxb hπa hxa hau, hpπ]
      exact ⟨hA, hps⟩
    have hπb : BoundedProc π := by
      obtain ⟨M, hM⟩ := hpb
      exact ⟨|πbar| + M, fun t ω => (abs_add_le _ _).trans (add_le_add le_rfl (hM t ω))⟩
    have hxbd : BoundedProc x := by
      obtain ⟨M, hM⟩ := hπb
      obtain ⟨N, hN⟩ := hu
      refine ⟨(M + |β| * M + N) / |κ|, fun t ω => ?_⟩
      simp only [hx]
      rw [abs_div]
      gcongr
      calc _ ≤ |π t ω - β * 𝔼.E t (π (t + 1)) ω| + |u t ω| := abs_sub _ _
        _ ≤ |π t ω| + |β * 𝔼.E t (π (t + 1)) ω| + |u t ω| := by gcongr; exact abs_sub _ _
        _ ≤ M + |β| * M + N := by
          rw [abs_mul]
          gcongr
          · exact hM t ω
          · exact 𝔼.abs_E_le (hM (t + 1)) t ω
          · exact hN t ω
    refine ⟨(π, x), ⟨hπb, hxbd, hπa, hxa, heq⟩, fun q ⟨hq1, hq2, hq3, hq4, hq5⟩ => ?_⟩
    obtain ⟨hqA, hqS⟩ := (forecastEqm_iff_scalar 𝔼 hκ hk hxb hq3 hq4 hau).mp hq5
    have hqb : BoundedProc (fun t ω => q.1 t ω - πbar) := by
      obtain ⟨M, hM⟩ := hq1
      exact ⟨M + |πbar|, fun t ω => (abs_sub _ _).trans (add_le_add (hM t ω) le_rfl)⟩
    have hqa : 𝔼.Adapted (fun t ω => q.1 t ω - πbar) := by
      intro t
      have e : (fun ω => q.1 t ω - πbar) = q.1 t - fun _ => πbar := rfl
      change 𝔼.E t (fun ω => q.1 t ω - πbar) = fun ω => q.1 t ω - πbar
      rw [e, map_sub, 𝔼.const, hq3 t]
    have hp' := hpu _ ⟨hqb, hqa, hqS⟩
    have h1 : q.1 = π := by
      funext t ω
      have := congrFun (congrFun hp' t) ω
      simp only [hπ]
      linarith
    have h2 : q.2 = x := by
      funext t ω
      have := (OptimalTaylor.AS_iff 𝔼 _ _ _ _ _).mp hqA t ω
      rw [h1] at this
      simp only [hx]
      field_simp
      linarith
    exact Prod.ext h1 h2

/-- **Proposition 7.13, exact, for the rule (3.14)** (Woodford (2003), p. 516): the forecast-based
rule with horizon `k ≥ 1` and coefficients `φ_y = ρ^{−k} φ̄_y`, `φ̄_y` from (3.12) — the rule
consistent with the optimal noninertial plan (`OptimalTaylor.forecast_rule_consistent`) — implies
determinacy iff every root of its characteristic function has modulus `> 1`. -/
theorem oni_forecast_determinate_iff [Nonempty Ω] {β κ σ lx li ρ ibar πbar xbar : ℝ}
    (hκ : κ ≠ 0) {k : ℕ} (hk : 1 ≤ k) (hxb : κ * xbar = (1 - β) * πbar) :
    ModelDet 𝔼 (ForecastEqm 𝔼 β σ κ ibar ((ρ ^ k)⁻¹ * OptimalTaylor.phiPiStar β κ σ li ρ)
      ((ρ ^ k)⁻¹ * OptimalTaylor.phiXStar β κ σ lx li ρ) πbar xbar k) ↔
      ∀ z : ℂ, chiC β κ σ ((ρ ^ k)⁻¹ * OptimalTaylor.phiPiStar β κ σ li ρ)
        ((ρ ^ k)⁻¹ * OptimalTaylor.phiXStar β κ σ lx li ρ) k z = 0 → 1 < ‖z‖ :=
  forecast_determinate_iff 𝔼 hκ hk hxb

end Woodford.GainsFromCommitment.TidyR5ForecastHorizon
