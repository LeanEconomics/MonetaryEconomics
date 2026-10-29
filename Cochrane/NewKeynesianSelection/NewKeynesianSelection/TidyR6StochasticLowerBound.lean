/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NewKeynesianSelection.LowerBound
import NewKeynesianSelection.ExpectationsFiniteTree

/-!
# The full nonlinear model of §16.8 under uncertainty

Cochrane (2023), Chapter 16, §16.8, pp. 377–380. The book simplifies "to perfect foresight
equilibria, so that initial inflation `Π₀` is the only indeterminacy" (p. 378). Here the
nonlinear model — the bond-pricing equation (16.25) for an arbitrary `ExpectationSystem`, the
rule (16.27) `1 + i_t = (1 + r)Φ(Π_t)` state by state, and the zero bound — is studied under
genuine uncertainty (`StochEq`).

## Main results

* `stochEq_dyn`, `stochEq_iff_dyn`: the stochastic (16.29) `E_t(1/Π_{t+1}) = 1/Φ(Π_t)`;
  `stochEq_iff_shock`: every equilibrium is `1/Π_{t+1} = 1/Φ(Π_t) + δ_{t+1}` with a sunspot
  `E_tδ_{t+1} = 0`.
* The zero bound: `zero_bound_iff_stoch` (`i_t ≥ 0` iff `E_t(1/Π_{t+1}) ≤ 1/β`); correction:
  `zero_bound_statewise_witness` — on the coin-flip tree an equilibrium at `i = 0` has
  `Π_1 = 2/3 < β = 1` in one state, so "the bound `i ≥ 0` means we cannot have `Π_{t+1} ≤ β`"
  (p. 379) holds only under perfect foresight.
* `const_stochEq_iff`, `continuum_of_stochEq`: every perfect-foresight path of Figure 16.2 is an
  equilibrium of every expectation system.
* `abs_E_le_E_abs`, `growth_zero`: the expectation-growth lemma (a nonnegative bounded process
  with `cD_t ≤ E_tD_{t+1}`, `c > 1`, is zero); `abs_sub_ge_of_hasDerivAt`,
  `abs_sub_le_of_hasDerivAt` (comparison of two functions through their derivatives).
* `target_unique_locally_bounded_stoch` (p. 378 under uncertainty): with `Φ′(Π*) > 1`, `Π*` is
  the unique equilibrium staying within `δ` of `Π*` in every state at every date — sunspots
  included, for every expectation system.
* `deflation_mean` (pp. 379–380 under uncertainty): in an equilibrium staying in `[Π_L, Π*]`
  where `Φ(Π) ≤ Π`, expected inverse inflation `E_0(1/Π_t)` rises monotonically and converges,
  and `∑ E_0[1/Φ(Π_t) − 1/Π_t] < ∞`.
-/

namespace Cochrane.NewKeynesianSelection.TidyR6StochasticLowerBound

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eqs. (16.25), (16.27), p. 378, and the zero bound, p. 379, under
uncertainty: an equilibrium of the nonlinear model is a positive adapted gross-inflation process
and an interest-rate process with the bond-pricing equation (16.25) at every date, the rule
`1 + i_t = (1 + r)Φ(Π_t)` and `i_t ≥ 0` in every state. -/
def StochEq (r : ℝ) (Φ : ℝ → ℝ) (infl i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, 0 < infl t ω) ∧ 𝔼.Adapted infl ∧ LowerBound.BondPricing 𝔼 r i infl ∧
    (∀ t ω, 1 + i t ω = (1 + r) * Φ (infl t ω)) ∧ ∀ t ω, 0 ≤ i t ω

/-- Cochrane (2023), eq. (16.29), p. 378, under uncertainty: in an equilibrium (`1 + r > 0`)
`E_t(1/Π_{t+1}) = 1/Φ(Π_t)` at every date. -/
theorem stochEq_dyn {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {infl i : ℕ → Ω → ℝ}
    (h : StochEq 𝔼 r Φ infl i) (t : ℕ) :
    𝔼.E t (fun ω => 1 / infl (t + 1) ω) = fun ω => 1 / Φ (infl t ω) := by
  funext ω
  have e := congrFun (h.2.2.1 t) ω
  simp only [Pi.smul_apply, smul_eq_mul] at e
  rw [h.2.2.2.1 t ω] at e
  have hΦ : 0 < Φ (infl t ω) := by
    have := h.2.2.2.2 t ω
    have h1 := h.2.2.2.1 t ω
    nlinarith
  rw [one_div, mul_inv] at e
  rw [one_div]
  exact (mul_left_cancel₀ (inv_ne_zero hr.ne') e).symm

/-- Cochrane (2023), eqs. (16.25)–(16.29), p. 378, under uncertainty: a positive adapted process
with `i` given by the rule and respecting the zero bound is an equilibrium iff
`E_t(1/Π_{t+1}) = 1/Φ(Π_t)` at every date. -/
theorem stochEq_iff_dyn {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {infl i : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < infl t ω) (had : 𝔼.Adapted infl)
    (hrule : ∀ t ω, 1 + i t ω = (1 + r) * Φ (infl t ω)) (hzb : ∀ t ω, 0 ≤ i t ω) :
    StochEq 𝔼 r Φ infl i ↔
      ∀ t, 𝔼.E t (fun ω => 1 / infl (t + 1) ω) = fun ω => 1 / Φ (infl t ω) := by
  refine ⟨fun h => stochEq_dyn 𝔼 hr h, fun h => ⟨hpos, had, fun t => ?_, hrule, hzb⟩⟩
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h t, hrule t ω]
  field_simp

/-- Cochrane (2023), eq. (16.5), p. 364, for the nonlinear model: the sunspot (expectational
error) of an equilibrium, `δ_{t+1} = 1/Π_{t+1} − E_t(1/Π_{t+1})`. -/
noncomputable def sunspotErr (infl : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (fun ω => 1 / infl (t + 1) ω) - 𝔼.E t (fun ω => 1 / infl (t + 1) ω)

/-- Cochrane (2023), eqs. (16.5) and (16.29), pp. 364 and 378: the sunspot is unforecastable,
`E_tδ_{t+1} = 0`. -/
theorem E_sunspotErr (infl : ℕ → Ω → ℝ) (t : ℕ) : 𝔼.E t (sunspotErr 𝔼 infl t) = 0 := by
  rw [sunspotErr, map_sub, 𝔼.E_E_self, sub_self]

/-- Cochrane (2023), eqs. (16.5) and (16.29), pp. 364 and 378, under uncertainty: a positive adapted
process with the rule and the zero bound, whose `1/Φ(Π_t)` is known at `t` (automatic on finite
trees, and on probability spaces by measurability as in
`TidyR6StochasticMeasurePatches.meas_stochEq1632_of_bond`, though no a.s. version of this lemma is
stated; `ExpectationSystem.PullOut`-type information hypothesis for an abstract expectation system),
is an equilibrium iff `1/Π_{t+1} = 1/Φ(Π_t) + δ_{t+1}` for some process `δ` with `E_tδ_{t+1} = 0`
(which is then `sunspotErr`). Initial inflation and the sunspot are the indeterminacy. -/
theorem stochEq_iff_shock {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {infl i : ℕ → Ω → ℝ}
    (hpos : ∀ t ω, 0 < infl t ω) (had : 𝔼.Adapted infl)
    (hrule : ∀ t ω, 1 + i t ω = (1 + r) * Φ (infl t ω)) (hzb : ∀ t ω, 0 ≤ i t ω)
    (hk : ∀ t, 𝔼.E t (fun ω => 1 / Φ (infl t ω)) = fun ω => 1 / Φ (infl t ω)) :
    StochEq 𝔼 r Φ infl i ↔ ∃ δ : ℕ → Ω → ℝ, (∀ t, 𝔼.E t (δ t) = 0) ∧
      ∀ t, (fun ω => 1 / infl (t + 1) ω) = (fun ω => 1 / Φ (infl t ω)) + δ t := by
  rw [stochEq_iff_dyn 𝔼 hr hpos had hrule hzb]
  constructor
  · intro h
    refine ⟨sunspotErr 𝔼 infl, E_sunspotErr 𝔼 infl, fun t => ?_⟩
    rw [sunspotErr, h t]
    abel
  · rintro ⟨δ, hδ, h⟩ t
    rw [h t, map_add, hδ t, add_zero, hk t]

/-! ## The zero bound under uncertainty -/

/-- Cochrane (2023), p. 379, under uncertainty: in an equilibrium (`1 + r > 0`) the zero bound
`i_t ≥ 0` holds iff `Φ(Π_t) ≥ β = 1/(1 + r)`, iff `E_t(1/Π_{t+1}) ≤ 1 + r = 1/β`: the bound
restricts the conditional mean of `1/Π_{t+1}`, not its value in each state. -/
theorem zero_bound_iff_stoch {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {infl i : ℕ → Ω → ℝ}
    (h : StochEq 𝔼 r Φ infl i) (t : ℕ) (ω : Ω) :
    (0 ≤ i t ω ↔ (1 + r)⁻¹ ≤ Φ (infl t ω)) ∧
      ((1 + r)⁻¹ ≤ Φ (infl t ω) ↔ 𝔼.E t (fun ω => 1 / infl (t + 1) ω) ω ≤ 1 + r) := by
  have hrule := h.2.2.2.1 t ω
  have hΦ : 0 < Φ (infl t ω) := by
    have := h.2.2.2.2 t ω
    nlinarith
  refine ⟨?_, ?_⟩
  · rw [inv_le_iff_one_le_mul₀' hr]
    constructor <;> intro h' <;> linarith
  · rw [stochEq_dyn 𝔼 hr h t]
    simp only
    rw [one_div, inv_le_comm₀ hΦ hr]

/-- Cochrane (2023), p. 379, "the bound `i ≥ 0` means we cannot have `Π_{t+1} ≤ β`", correction
under uncertainty. On the coin-flip tree with `r = 0` (`β = 1`) and the constant rule `Φ ≡ 1`,
the process `1/Π_{t+1} = 1 + ε_{t+1}/2` (`ε` the coin shock) and `i ≡ 0` is an equilibrium,
and in state `(true, true)` inflation is `Π_1 = 2/3 < β = 1` although `i_0 = 0 ≥ 0`. -/
theorem zero_bound_statewise_witness :
    StochEq ExpectationsFiniteTree.coinSystem 0 (fun _ => 1)
        (fun t ω => 1 / (1 + ExpectationsFiniteTree.coinShock t ω / 2)) (fun _ _ => 0) ∧
      1 / (1 + ExpectationsFiniteTree.coinShock 1 (true, true) / 2) < (1 + (0 : ℝ))⁻¹ := by
  open ExpectationsFiniteTree in
  have hb : ∀ t ω, |coinShock t ω| ≤ 1 := fun t ω => by
    unfold coinShock; split_ifs <;> simp
  have hpos : ∀ t ω, 0 < 1 + coinShock t ω / 2 := fun t ω => by
    have := hb t ω; have := neg_abs_le (coinShock t ω); linarith
  refine ⟨⟨fun t ω => by have := hpos t ω; positivity, fun t => ?_, fun t => ?_,
    fun t ω => by norm_num, fun t ω => le_rfl⟩, by norm_num [coinShock]⟩
  · funext ω
    rw [coinSystem, FiniteTree.toExpectationSystem_E]
    exact coinTree.condE_of_const_on_cell fun ω' h => by
      change 1 / (1 + coinShock t ω' / 2) = 1 / (1 + coinShock t ω / 2)
      rw [coinShock_measurable t h]
  · have e : (fun ω => 1 / (1 / (1 + coinShock (t + 1) ω / 2))) =
        (fun _ => (1 : ℝ)) + (1 / 2 : ℝ) • coinShock (t + 1) := by
      funext ω
      simp only [one_div_one_div, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [e, map_add, map_smul, coinSystem.const, coinShock_mean_zero]
    norm_num

/-! ## Perfect-foresight paths are equilibria of every expectation system -/

/-- Cochrane (2023), pp. 378–379 ("All of the paths graphed in Figure 16.2 are perfect-foresight
equilibria"), for every expectation system: a deterministic path is an equilibrium of `𝔼`
(`Ω` nonempty) iff it is a perfect-foresight equilibrium path: positive inflation, the zero
bound, `Π_{t+1} = β(1 + i_t)` and the rule. -/
theorem const_stochEq_iff [Nonempty Ω] {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ} {p j : ℕ → ℝ} :
    StochEq 𝔼 r Φ (fun t _ => p t) (fun t _ => j t) ↔
      (∀ t, 0 < p t) ∧ (∀ t, 0 ≤ j t) ∧ (∀ t, p (t + 1) = (1 + r)⁻¹ * (1 + j t)) ∧
        ∀ t, 1 + j t = (1 + r) * Φ (p t) := by
  obtain ⟨ω0⟩ := ‹Nonempty Ω›
  have hE : ∀ t (c : ℝ), 𝔼.E t (fun _ => c) = fun _ => c := fun t c => 𝔼.const t c
  constructor
  · rintro ⟨hpos, -, hbp, hrule, hzb⟩
    refine ⟨fun t => hpos t ω0, fun t => hzb t ω0, fun t => ?_, fun t => hrule t ω0⟩
    have e := congrFun (hbp t) ω0
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [hE] at e
    have h1 : 0 < 1 + j t := by linarith [hzb t ω0]
    have h2 := hpos (t + 1) ω0
    field_simp at e
    rw [eq_inv_mul_iff_mul_eq₀ hr.ne']
    linarith
  · rintro ⟨hpos, hzb, hfis, hrule⟩
    refine ⟨fun t _ => hpos t, fun t => hE t _, fun t => ?_, fun t _ => hrule t,
      fun t _ => hzb t⟩
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hE]
    have h1 : 0 < 1 + j t := by linarith [hzb t]
    rw [hfis t]
    field_simp

/-- Cochrane (2023), p. 379, "all of the paths … are … equilibria", under uncertainty: if the
rule respects the zero bound (`Φ ≥ β` on `(0, ∞)`), every `Π₀ > 0` starts an equilibrium of every
expectation system, the deterministic orbit `Π_t = Φ^[t](Π₀)`. -/
theorem continuum_of_stochEq [Nonempty Ω] {r : ℝ} (hr : 0 < 1 + r) {Φ : ℝ → ℝ}
    (hbd : ∀ x, 0 < x → (1 + r)⁻¹ ≤ Φ x) {Pi0 : ℝ} (hPi0 : 0 < Pi0) :
    StochEq 𝔼 r Φ (fun t _ => Φ^[t] Pi0) (fun t _ => (1 + r) * Φ (Φ^[t] Pi0) - 1) := by
  have hpos : ∀ t, 0 < Φ^[t] Pi0 := by
    intro t
    induction t with
    | zero => simpa using hPi0
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact lt_of_lt_of_le (inv_pos.mpr hr) (hbd _ ih)
  refine (const_stochEq_iff 𝔼 hr).mpr ⟨hpos, fun t => ?_, fun t => ?_, fun t => by ring⟩
  · have h1 := mul_le_mul_of_nonneg_left (hbd _ (hpos t)) hr.le
    rw [mul_inv_cancel₀ hr.ne'] at h1
    linarith
  · rw [Function.iterate_succ_apply']
    field_simp
    ring

/-! ## The expectation-growth lemma -/

/-- Cochrane (2023), §16.1, p. 364 (expectations of the deviation explode): `|E_t f| ≤ E_t|f|`. -/
theorem abs_E_le_E_abs (f : Ω → ℝ) (t : ℕ) (ω : Ω) :
    |𝔼.E t f ω| ≤ 𝔼.E t (fun ω' => |f ω'|) ω := by
  have h1 : f ≤ fun ω' => |f ω'| := fun ω' => le_abs_self _
  have h2 : -(fun ω' => |f ω'|) ≤ f := fun ω' => by
    simp only [Pi.neg_apply]; exact neg_abs_le _
  have e1 := 𝔼.mono t h1 ω
  have e2 := 𝔼.mono t h2 ω
  rw [map_neg] at e2
  simp only [Pi.neg_apply] at e2
  exact abs_le.mpr ⟨by linarith, e1⟩

/-- Cochrane (2023), §16.1, p. 364 and §16.8, p. 378 ("leads away"): if a nonnegative process
bounded by `B` satisfies `cD_t ≤ E_tD_{t+1}` with `c > 1`, then `c^{k+1}D_t ≤ E_tD_{t+k+1}` for
every `k`, and hence `D = 0`. (No adaptedness of `D` is needed.) -/
theorem growth_zero {D : ℕ → Ω → ℝ} {c B : ℝ} (hc : 1 < c) (hD0 : ∀ t ω, 0 ≤ D t ω)
    (hDB : ∀ t ω, D t ω ≤ B) (hg : ∀ t ω, c * D t ω ≤ 𝔼.E t (D (t + 1)) ω) :
    ∀ t ω, D t ω = 0 := by
  have hc0 : 0 < c := by linarith
  have hk : ∀ k t ω, c ^ (k + 1) * D t ω ≤ 𝔼.E t (D (t + (k + 1))) ω := by
    intro k
    induction k with
    | zero => intro t ω; simpa using hg t ω
    | succ k ih =>
      intro t ω
      have h1 : c • D (t + (k + 1)) ≤ 𝔼.E (t + (k + 1)) (D (t + (k + 1) + 1)) :=
        fun ω' => by simpa [smul_eq_mul] using hg (t + (k + 1)) ω'
      have h2 := 𝔼.mono t h1 ω
      rw [map_smul, 𝔼.tower (Nat.le_add_right t (k + 1))] at h2
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      calc c ^ (k + 1 + 1) * D t ω = c * (c ^ (k + 1) * D t ω) := by ring
        _ ≤ c * 𝔼.E t (D (t + (k + 1))) ω := mul_le_mul_of_nonneg_left (ih t ω) hc0.le
        _ ≤ 𝔼.E t (D (t + (k + 1) + 1)) ω := h2
        _ = 𝔼.E t (D (t + (k + 1 + 1))) ω := by rw [add_assoc]
  intro t ω
  by_contra hne
  have hpos : 0 < D t ω := lt_of_le_of_ne (hD0 t ω) (Ne.symm hne)
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (B / D t ω) hc
  have hEB : 𝔼.E t (D (t + (k + 1))) ω ≤ B := by
    have := 𝔼.mono t (fun ω' => hDB (t + (k + 1)) ω' : D (t + (k + 1)) ≤ fun _ => B) ω
    rwa [𝔼.const] at this
  have h1 := (hk k t ω).trans hEB
  have h2 : B < c ^ k * D t ω := by rwa [div_lt_iff₀ hpos] at hk'
  have h3 : c ^ k * D t ω ≤ c ^ (k + 1) * D t ω := by
    apply mul_le_mul_of_nonneg_right _ hpos.le
    exact pow_le_pow_right₀ hc.le (Nat.le_succ k)
  linarith

/-- Cochrane (2023), p. 378: comparison through derivatives. If `h′(p) = a`, `k′(p) = b`,
`c ≥ 0` and `c|b| < |a|`, then near `p`, `c|k(x) − k(p)| ≤ |h(x) − h(p)|`. -/
theorem abs_sub_ge_of_hasDerivAt {h k : ℝ → ℝ} {p a b c : ℝ} (hh : HasDerivAt h a p)
    (hk : HasDerivAt k b p) (hc : 0 ≤ c) (hab : c * |b| < |a|) :
    ∃ δ > 0, ∀ x, |x - p| < δ → c * |k x - k p| ≤ |h x - h p| := by
  set ε := (|a| - c * |b|) / (1 + c) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hh hk
  obtain ⟨δ1, hδ1, h1⟩ := Metric.eventually_nhds_iff.mp (hh hε0)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.eventually_nhds_iff.mp (hk hε0)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun x hx => ?_⟩
  have e1 := h1 (show dist x p < δ1 by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hx (min_le_left _ _))
  have e2 := h2 (show dist x p < δ2 by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hx (min_le_right _ _))
  simp only [Real.norm_eq_abs, smul_eq_mul] at e1 e2
  have f1 : |a| * |x - p| - ε * |x - p| ≤ |h x - h p| := by
    have := abs_sub_abs_le_abs_sub ((x - p) * a) (h x - h p - (x - p) * a)
    have e3 : |(x - p) * a| = |a| * |x - p| := by rw [abs_mul, mul_comm]
    have e4 : (x - p) * a - (h x - h p - (x - p) * a) = 2 * ((x - p) * a) - (h x - h p) := by ring
    have := abs_sub (h x - h p - (x - p) * a) ((x - p) * a)
    have e5 : h x - h p - (x - p) * a + (x - p) * a = h x - h p := by ring
    have := abs_add_le (h x - h p - (x - p) * a) ((x - p) * a)
    rw [e5, e3] at this
    have := abs_sub_abs_le_abs_sub ((x - p) * a) (-(h x - h p - (x - p) * a))
    rw [e3, abs_neg, show (x - p) * a - -(h x - h p - (x - p) * a) = h x - h p by ring] at this
    linarith
  have f2 : |k x - k p| ≤ |b| * |x - p| + ε * |x - p| := by
    have := abs_add_le (k x - k p - (x - p) * b) ((x - p) * b)
    rw [show k x - k p - (x - p) * b + (x - p) * b = k x - k p by ring, abs_mul,
      mul_comm |x - p|] at this
    linarith
  have key : c * (|b| * |x - p| + ε * |x - p|) ≤ |a| * |x - p| - ε * |x - p| := by
    have : c * (|b| + ε) ≤ |a| - ε := by
      rw [hε]; field_simp; nlinarith
    have hx0 := abs_nonneg (x - p)
    nlinarith
  calc c * |k x - k p| ≤ c * (|b| * |x - p| + ε * |x - p|) := mul_le_mul_of_nonneg_left f2 hc
    _ ≤ _ := key
    _ ≤ _ := f1

/-- Cochrane (2023), p. 379: comparison through derivatives, the other direction. If
`h′(p) = a`, `k′(p) = b`, `c ≥ 0` and `|a| < c|b|`, then near `p`,
`|h(x) − h(p)| ≤ c|k(x) − k(p)|`. -/
theorem abs_sub_le_of_hasDerivAt {h k : ℝ → ℝ} {p a b c : ℝ} (hh : HasDerivAt h a p)
    (hk : HasDerivAt k b p) (hc : 0 ≤ c) (hab : |a| < c * |b|) :
    ∃ δ > 0, ∀ x, |x - p| < δ → |h x - h p| ≤ c * |k x - k p| := by
  set ε := (c * |b| - |a|) / (1 + c) with hε
  have hε0 : 0 < ε := div_pos (by linarith) (by linarith)
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hh hk
  obtain ⟨δ1, hδ1, h1⟩ := Metric.eventually_nhds_iff.mp (hh hε0)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.eventually_nhds_iff.mp (hk hε0)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun x hx => ?_⟩
  have e1 := h1 (show dist x p < δ1 by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hx (min_le_left _ _))
  have e2 := h2 (show dist x p < δ2 by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hx (min_le_right _ _))
  simp only [Real.norm_eq_abs, smul_eq_mul] at e1 e2
  have f1 : |h x - h p| ≤ |a| * |x - p| + ε * |x - p| := by
    have := abs_add_le (h x - h p - (x - p) * a) ((x - p) * a)
    rw [show h x - h p - (x - p) * a + (x - p) * a = h x - h p by ring, abs_mul,
      mul_comm |x - p|] at this
    linarith
  have f2 : |b| * |x - p| - ε * |x - p| ≤ |k x - k p| := by
    have := abs_sub_abs_le_abs_sub ((x - p) * b) (-(k x - k p - (x - p) * b))
    rw [abs_mul, mul_comm |x - p|, abs_neg,
      show (x - p) * b - -(k x - k p - (x - p) * b) = k x - k p by ring] at this
    linarith
  have key : |a| * |x - p| + ε * |x - p| ≤ c * (|b| * |x - p| - ε * |x - p|) := by
    have : |a| + ε ≤ c * (|b| - ε) := by
      rw [hε]; field_simp; nlinarith
    have hx0 := abs_nonneg (x - p)
    nlinarith
  calc |h x - h p| ≤ _ := f1
    _ ≤ _ := key
    _ ≤ c * |k x - k p| := mul_le_mul_of_nonneg_left f2 hc

/-! ## Local uniqueness at the active steady state, under uncertainty -/

/-- Cochrane (2023), p. 378: the derivatives of `Π ↦ 1/Φ(Π)` and `Π ↦ 1/Π` at a steady state
`Π* > 0` with `Φ′(Π*) = d` are `−d/Π*²` and `−1/Π*²`. -/
theorem hasDerivAt_inv_pair {Φ : ℝ → ℝ} {Pis d : ℝ} (hPis : 0 < Pis) (hfix : Φ Pis = Pis)
    (hd : HasDerivAt Φ d Pis) :
    HasDerivAt (fun x => 1 / Φ x) (-d / Pis ^ 2) Pis ∧
      HasDerivAt (fun x : ℝ => 1 / x) (-1 / Pis ^ 2) Pis := by
  have h1 := hd.inv (by rw [hfix]; exact hPis.ne')
  have h2 := hasDerivAt_inv hPis.ne'
  refine ⟨?_, ?_⟩
  · simp only [one_div]
    convert h1 using 1
    rw [hfix]
  · simp only [one_div]
    convert h2 using 1
    ring

/-- Cochrane (2023), p. 378, "the equilibrium `Π*` is a unique 'locally bounded' equilibrium",
**under uncertainty**: if `Φ(Π*) = Π* > 0` and `Φ′(Π*) > 1`, there is `δ > 0` such that, for
any expectation system, every process with `E_t(1/Π_{t+1}) = 1/Φ(Π_t)` that stays within `δ`
of `Π*` in every state at every date is `Π_t ≡ Π*`. Sunspots cannot keep the economy near
`Π*`. -/
theorem target_unique_locally_bounded_stoch {Φ : ℝ → ℝ} {Pis d : ℝ} (hPis : 0 < Pis)
    (hfix : Φ Pis = Pis) (hd : HasDerivAt Φ d Pis) (hd1 : 1 < d) :
    ∃ δ > 0, ∀ infl : ℕ → Ω → ℝ,
      (∀ t, 𝔼.E t (fun ω => 1 / infl (t + 1) ω) = fun ω => 1 / Φ (infl t ω)) →
      (∀ t ω, |infl t ω - Pis| < δ) → ∀ t ω, infl t ω = Pis := by
  obtain ⟨hh, hk⟩ := hasDerivAt_inv_pair hPis hfix hd
  set c := (1 + d) / 2 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hP2 : 0 < Pis ^ 2 := by positivity
  have hab : c * |-1 / Pis ^ 2| < |-d / Pis ^ 2| := by
    rw [neg_div, neg_div, abs_neg, abs_neg, abs_of_pos (by positivity),
      abs_of_pos (div_pos (by linarith) hP2)]
    rw [← mul_div_assoc, mul_one]
    exact div_lt_div_of_pos_right (by rw [hc]; linarith) hP2
  obtain ⟨δ0, hδ0, hcmp⟩ := abs_sub_ge_of_hasDerivAt hh hk (by linarith) hab
  refine ⟨min δ0 (Pis / 2), lt_min hδ0 (by linarith), fun infl hdyn hnear => ?_⟩
  have hlow : ∀ t ω, Pis / 2 < infl t ω := fun t ω => by
    have := (abs_lt.mp ((hnear t ω).trans_le (min_le_right _ _))).1
    linarith
  set D : ℕ → Ω → ℝ := fun t ω => |1 / infl t ω - 1 / Pis| with hD
  have hDB : ∀ t ω, D t ω ≤ 2 / Pis + 1 / Pis := by
    intro t ω
    have hp := hlow t ω
    have h1 : 1 / infl t ω ≤ 2 / Pis := by
      rw [div_le_div_iff₀ (by linarith) hPis]; linarith
    have h2 : 0 < 1 / infl t ω := one_div_pos.mpr (by linarith)
    have h3 : 0 < 1 / Pis := one_div_pos.mpr hPis
    rw [abs_le]
    constructor <;> linarith
  have hg : ∀ t ω, c * D t ω ≤ 𝔼.E t (D (t + 1)) ω := by
    intro t ω
    have h1 := hcmp (infl t ω) ((hnear t ω).trans_le (min_le_left _ _))
    simp only [hfix] at h1
    have h2 : 1 / Φ (infl t ω) - 1 / Pis =
        𝔼.E t (fun ω' => 1 / infl (t + 1) ω' - 1 / Pis) ω := by
      have e : (fun ω' => 1 / infl (t + 1) ω' - 1 / Pis) =
          (fun ω' => 1 / infl (t + 1) ω') - fun _ => 1 / Pis := rfl
      rw [e, map_sub, 𝔼.const, hdyn t]
      rfl
    have h3 := abs_E_le_E_abs 𝔼 (fun ω' => 1 / infl (t + 1) ω' - 1 / Pis) t ω
    rw [← h2] at h3
    exact h1.trans h3
  have hz := growth_zero 𝔼 hc1 (fun t ω => abs_nonneg _) hDB hg
  intro t ω
  have := hz t ω
  simp only [abs_eq_zero, sub_eq_zero] at this
  have hp := hlow t ω
  rw [div_eq_div_iff (by linarith) hPis.ne'] at this
  linarith

/-! ## Deflations under uncertainty -/

/-- Cochrane (2023), pp. 379–380, "equilibria that start below `Π*` … trundle down gently to the
zero bound", under uncertainty: if an equilibrium (`E_t(1/Π_{t+1}) = 1/Φ(Π_t)`) stays in
`[Π_L, Π*]` (`Π_L > 0`) in every state, where `0 < Φ(Π) ≤ Π`, then expected inverse inflation
`E_0(1/Π_t)` is nondecreasing in `t` and converges, and the expected one-step gaps
`E_0[1/Φ(Π_t) − 1/Π_t]` are summable: in mean, the economy drifts towards the steady states. -/
theorem deflation_mean {Φ : ℝ → ℝ} {PL Pis : ℝ} (hPL : 0 < PL)
    (hbelow : ∀ x, PL ≤ x → x ≤ Pis → Φ x ≤ x) (hΦpos : ∀ x, PL ≤ x → x ≤ Pis → 0 < Φ x)
    {infl : ℕ → Ω → ℝ}
    (hdyn : ∀ t, 𝔼.E t (fun ω => 1 / infl (t + 1) ω) = fun ω => 1 / Φ (infl t ω))
    (hmem : ∀ t ω, PL ≤ infl t ω ∧ infl t ω ≤ Pis) (ω : Ω) :
    Monotone (fun t => 𝔼.E 0 (fun ω => 1 / infl t ω) ω) ∧
      (∃ L, Tendsto (fun t => 𝔼.E 0 (fun ω => 1 / infl t ω) ω) atTop (𝓝 L)) ∧
      Summable (fun t => 𝔼.E 0 (fun ω => 1 / Φ (infl t ω) - 1 / infl t ω) ω) := by
  have hstep : ∀ t, 𝔼.E 0 (fun ω => 1 / infl (t + 1) ω) ω =
      𝔼.E 0 (fun ω => 1 / Φ (infl t ω)) ω := by
    intro t
    rw [← 𝔼.tower (Nat.zero_le t), hdyn t]
  have hgap : ∀ t, 0 ≤ 𝔼.E 0 (fun ω => 1 / Φ (infl t ω) - 1 / infl t ω) ω := by
    intro t
    have h : (fun _ => (0 : ℝ)) ≤ fun ω => 1 / Φ (infl t ω) - 1 / infl t ω := fun ω' => by
      obtain ⟨h1, h2⟩ := hmem t ω'
      have := hbelow _ h1 h2
      have := hΦpos _ h1 h2
      simp only [sub_nonneg]
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have := 𝔼.mono 0 h ω
    rwa [𝔼.const] at this
  have hdiff : ∀ t, 𝔼.E 0 (fun ω => 1 / infl (t + 1) ω) ω - 𝔼.E 0 (fun ω => 1 / infl t ω) ω =
      𝔼.E 0 (fun ω => 1 / Φ (infl t ω) - 1 / infl t ω) ω := by
    intro t
    rw [hstep t]
    have e : (fun ω => 1 / Φ (infl t ω) - 1 / infl t ω) =
        (fun ω => 1 / Φ (infl t ω)) - fun ω => 1 / infl t ω := rfl
    rw [e, map_sub]
    rfl
  have hmono : Monotone (fun t => 𝔼.E 0 (fun ω => 1 / infl t ω) ω) :=
    monotone_nat_of_le_succ fun t => by linarith [hdiff t, hgap t]
  have hbdd : ∀ t, 𝔼.E 0 (fun ω => 1 / infl t ω) ω ≤ 1 / PL := by
    intro t
    have h : (fun ω => 1 / infl t ω) ≤ fun _ => 1 / PL := fun ω' =>
      one_div_le_one_div_of_le hPL (hmem t ω').1
    have := 𝔼.mono 0 h ω
    rwa [𝔼.const] at this
  refine ⟨hmono, ⟨_, tendsto_atTop_ciSup hmono ⟨1 / PL, by rintro _ ⟨t, rfl⟩; exact hbdd t⟩⟩, ?_⟩
  refine summable_of_sum_range_le hgap (c := 1 / PL - 𝔼.E 0 (fun ω => 1 / infl 0 ω) ω)
    fun n => ?_
  have htel : ∑ t ∈ Finset.range n, 𝔼.E 0 (fun ω => 1 / Φ (infl t ω) - 1 / infl t ω) ω =
      𝔼.E 0 (fun ω => 1 / infl n ω) ω - 𝔼.E 0 (fun ω => 1 / infl 0 ω) ω := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, ← hdiff n]; ring
  rw [htel]
  linarith [hbdd n]

end Cochrane.NewKeynesianSelection.TidyR6StochasticLowerBound
