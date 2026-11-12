/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.TidyR5QEUncertainty

/-!
# Quantitative easing reverse-engineered from reserves, under uncertainty

Cochrane (2023), §7.6.1, pp. 229–232, equation (7.23): "for a desired price-level path and a
choice of one of monetary `M` or QE purchases `B̃`, (7.23) gives us the other one". This module
treats the direction *given `M`, find `B̃`* under uncertainty. The QE purchases `B̃_0^{(j)}` are
chosen once, at date 0 (known at 0); reserves `M_{t−1}^{(t)}`, the price path and surpluses are
random.

Write `R_t = E_t ∑_k β^k s_{t+k} − M_{t−1}^{(t)}/P_t − V^T_t` for the value the QE bonds must carry
at `t` (`resid`, with `V^T_t` the value of Treasury debt) and
`c_t = (R_t − β E_t R_{t+1}) P_t` (`qeImplied`).

* `qe_split`: (7.23) at `t` holds iff the QE bonds are worth `R_t`.
* `qe_necessary`, `qe_unique`: if bounded date-0 purchases support the path, then
  `B̃_0^{(t)} = c_t` for every `t ≥ 1`: they are unique.
* `qe_sufficient`: conversely, if every `c_t` (`t ≥ 1`) is known at date 0, the purchases
  `B̃_0^{(t)} = c_t` satisfy (7.23) at every date `t ≥ 1`.
* `qe_exists_iff`: **the exact condition**: with bounded data and `1/P` bounded away from zero,
  bounded date-0 QE purchases supporting the path exist if and only if every `c_t` is known at
  date 0.
* `coin_no_qe`: **a date-0-fixed `B̃` cannot absorb later news**: with a coin-flip surplus shock at
  date 1, a deterministic desired price path and deterministic reserves, no bounded date-0 QE
  purchases exist.
-/

namespace Cochrane.LongTermDebtDynamics.TidyR5QEReverse

open Filter Topology MaturityStructure TidyR5QEUncertainty

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): the value the QE bonds must carry at
`t`, `R_t = E_t ∑_k β^k s_{t+k} − M_{t−1}^{(t)}/P_t − V^T_t`. -/
noncomputable def resid (β : ℝ) (VT Mr x s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => pvSurplus 𝔼 β s t ω - Mr t ω * x t ω - VT t ω

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): the implied QE purchases
`c_t = (R_t − β E_t R_{t+1})/(1/P_t)`. -/
noncomputable def qeImplied (β : ℝ) (VT Mr x s : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  (resid 𝔼 β VT Mr x s t - β • 𝔼.E t (resid 𝔼 β VT Mr x s (t + 1))) / x t

/-- Cochrane (2023), eq. (7.23), p. 230: given the value `V^T_t` of the Treasury's geometric debt,
the present-value relation at `t` holds iff the QE bonds are worth `R_t`,
`∑_k β^k B̃_0^{(t+k)} E_t(1/P_{t+k}) = R_t`. -/
theorem qe_split {β om B : ℝ} {b Mr x s VT : ℕ → Ω → ℝ}
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (t : ℕ) :
    QEPV 𝔼 β om B b Mr x s t ↔ ∀ ω, HasSum (fun k : ℕ => β ^ k * (b (t + k) ω *
      𝔼.E t (x (t + k)) ω)) (resid 𝔼 β VT Mr x s t ω) := by
  constructor
  · intro h ω
    refine ((h ω).sub (hT t ω)).congr_fun fun k => ?_
    ring
  · intro h ω
    have := (hT t ω).add (h ω)
    convert this using 1
    · funext k; ring
    · simp only [resid]; ring

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): **necessity.** If bounded QE
purchases fixed at date 0 satisfy (7.23) at every date `t ≥ 1` (with `|1/P| ≤ K_x`), then
`B̃_0^{(t+1)}/P_{t+1} = R_{t+1} − β E_{t+1} R_{t+2}`. -/
theorem qe_necessary (hpo : 𝔼.PullOut) {β om B Kx Kb : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {b Mr x s VT : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hxb : ∀ t ω, |x t ω| ≤ Kx)
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (hb0 : ∀ j, 𝔼.E 0 (b j) = b j) (hbb : ∀ j ω, |b j ω| ≤ Kb)
    (hpv : ∀ t, QEPV 𝔼 β om B b Mr x s (t + 1)) (t : ℕ) :
    b (t + 1) * x (t + 1) = resid 𝔼 β VT Mr x s (t + 1) -
      β • 𝔼.E (t + 1) (resid 𝔼 β VT Mr x s (t + 1 + 1)) := by
  have hq := fun v => (qe_split 𝔼 hT (v + 1)).mp (hpv v)
  have hbk : ∀ j v, 𝔼.E v (b j) = b j := fun j v => ForwardSolution.E_of_known 𝔼
    (Nat.zero_le v) (hb0 j)
  -- `E_{t+1} R_{t+2}` as a series
  set f : ℕ → Ω → ℝ := fun k ω' => β ^ k * (b (t + 1 + 1 + k) ω' *
    𝔼.E (t + 1 + 1) (x (t + 1 + 1 + k)) ω') with hf
  have hfb : ∀ k ω', |f k ω'| ≤ β ^ k * (Kb * Kx) := by
    intro k ω'
    rw [hf, abs_mul, abs_pow, abs_of_nonneg hβ0, abs_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (hbb _ ω') (𝔼.abs_E_le (hxb _) _ ω')
      (abs_nonneg _) ((abs_nonneg _).trans (hbb 0 ω'))) (pow_nonneg hβ0 k)
  have hRu1 : resid 𝔼 β VT Mr x s (t + 1 + 1) = fun ω' => ∑' k, f k ω' := by
    funext ω'; exact ((hq (t + 1)) ω').tsum_eq.symm
  have hEf : ∀ k, 𝔼.E (t + 1) (f k) = fun ω' => β ^ k * (b (t + 1 + 1 + k) ω' *
      𝔼.E (t + 1) (x (t + 1 + 1 + k)) ω') := by
    intro k
    rw [show f k = β ^ k • (b (t + 1 + 1 + k) * 𝔼.E (t + 1 + 1) (x (t + 1 + 1 + k))) from rfl,
      map_smul,
      hpo _ _ _ (hbk _ (t + 1)), 𝔼.tower (Nat.le_succ (t + 1))]
    rfl
  funext ω
  have hE := ForwardSolution.E_tsum_dom 𝔼 ((summable_geometric_of_lt_one hβ0 hβ1).mul_right
    (Kb * Kx)) hfb (t + 1) ω
  rw [← hRu1] at hE
  simp only [hEf] at hE
  have hS := (hq t) ω
  have h0 := hS.summable.tsum_eq_zero_add
  rw [hS.tsum_eq] at h0
  simp only [pow_zero, one_mul, add_zero, hx (t + 1)] at h0
  have hshift : ∑' k, β ^ (k + 1) * (b (t + 1 + (k + 1)) ω * 𝔼.E (t + 1) (x (t + 1 + (k + 1))) ω) =
      β * 𝔼.E (t + 1) (resid 𝔼 β VT Mr x s (t + 1 + 1)) ω := by
    rw [hE, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show t + 1 + (k + 1) = t + 1 + 1 + k by omega, pow_succ]
    ring
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): bounded QE purchases fixed at date 0
that support a path are unique: two of them agree at every maturity `t ≥ 1`. -/
theorem qe_unique (hpo : 𝔼.PullOut) {β om B Kx Kb Kb' : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {b b' Mr x s VT : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hxb : ∀ t ω, |x t ω| ≤ Kx)
    (hxpos : ∀ t ω, 0 < x t ω)
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (hb0 : ∀ j, 𝔼.E 0 (b j) = b j) (hbb : ∀ j ω, |b j ω| ≤ Kb)
    (hb0' : ∀ j, 𝔼.E 0 (b' j) = b' j) (hbb' : ∀ j ω, |b' j ω| ≤ Kb')
    (hpv : ∀ t, QEPV 𝔼 β om B b Mr x s (t + 1)) (hpv' : ∀ t, QEPV 𝔼 β om B b' Mr x s (t + 1))
    (t : ℕ) : b (t + 1) = b' (t + 1) := by
  have h1 := qe_necessary 𝔼 hpo hβ0 hβ1 hx hxb hT hb0 hbb hpv t
  have h2 := qe_necessary 𝔼 hpo hβ0 hβ1 hx hxb hT hb0' hbb' hpv' t
  funext ω
  have := congrFun (h1.trans h2.symm) ω
  simp only [Pi.mul_apply] at this
  exact mul_right_cancel₀ (hxpos _ ω).ne' this

/-- Cochrane (2023), eq. (7.23), p. 230 (under uncertainty): **sufficiency.** If `R` is adapted and
bounded and every implied purchase `c_t` (`t ≥ 1`) is known at date 0, then the purchases
`B̃_0^{(t)} = c_t` satisfy (7.23) at every date `t ≥ 1`. -/
theorem qe_sufficient (hpo : 𝔼.PullOut) {β om B KR : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {Mr x s VT : ℕ → Ω → ℝ} (hxpos : ∀ t ω, 0 < x t ω)
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (hRad : ∀ t, 𝔼.E t (resid 𝔼 β VT Mr x s t) = resid 𝔼 β VT Mr x s t)
    (hRb : ∀ t ω, |resid 𝔼 β VT Mr x s t ω| ≤ KR)
    (hc0 : ∀ t, 𝔼.E 0 (qeImplied 𝔼 β VT Mr x s (t + 1)) = qeImplied 𝔼 β VT Mr x s (t + 1))
    (t : ℕ) : QEPV 𝔼 β om B (qeImplied 𝔼 β VT Mr x s) Mr x s (t + 1) := by
  rw [qe_split 𝔼 hT]
  intro ω
  set u := t + 1 with hu
  set R := resid 𝔼 β VT Mr x s with hR
  set a : ℕ → ℝ := fun k => 𝔼.E u (R (u + k)) ω with ha
  have hcx : ∀ m, 1 ≤ m → qeImplied 𝔼 β VT Mr x s m * x m = R m - β • 𝔼.E m (R (m + 1)) := by
    intro m _
    funext ω'
    simp only [qeImplied, Pi.mul_apply, Pi.div_apply]
    exact div_mul_cancel₀ _ (hxpos m ω').ne'
  have hterm : ∀ k, β ^ k * (qeImplied 𝔼 β VT Mr x s (u + k) ω * 𝔼.E u (x (u + k)) ω) =
      β ^ k * a k - β ^ (k + 1) * a (k + 1) := by
    intro k
    have hk : 𝔼.E u (qeImplied 𝔼 β VT Mr x s (u + k)) = qeImplied 𝔼 β VT Mr x s (u + k) := by
      have := hc0 (t + k)
      rw [show t + k + 1 = u + k by omega] at this
      exact ForwardSolution.E_of_known 𝔼 (Nat.zero_le u) this
    have h1 := congrFun (hpo u _ (x (u + k)) hk) ω
    simp only [Pi.mul_apply] at h1
    rw [← h1, hcx (u + k) (by omega), map_sub, map_smul, 𝔼.tower (show u ≤ u + k by omega)]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
    rw [show u + k + 1 = u + (k + 1) by omega, pow_succ]
    ring
  have hsumm : Summable (fun k : ℕ => β ^ k * (qeImplied 𝔼 β VT Mr x s (u + k) ω *
      𝔼.E u (x (u + k)) ω)) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right
      (KR + β * KR)) fun k => ?_
    rw [hterm, Real.norm_eq_abs]
    have h1 : |a k| ≤ KR := 𝔼.abs_E_le (hRb _) u ω
    have h2 : |a (k + 1)| ≤ KR := 𝔼.abs_E_le (hRb _) u ω
    rw [pow_succ, show β ^ k * a k - β ^ k * β * a (k + 1) = β ^ k * (a k - β * a (k + 1)) by
      ring, abs_mul, abs_of_nonneg (pow_nonneg hβ0 k)]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (pow_nonneg hβ0 k)
    rw [abs_mul, abs_of_nonneg hβ0]
    exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hβ0)
  rw [hsumm.hasSum_iff_tendsto_nat]
  have hpart : ∀ N, ∑ k ∈ Finset.range N, β ^ k * (qeImplied 𝔼 β VT Mr x s (u + k) ω *
      𝔼.E u (x (u + k)) ω) = R u ω - β ^ N * a N := by
    intro N
    simp only [hterm]
    rw [Finset.sum_range_sub' (fun k => β ^ k * a k) N]
    simp only [ha, pow_zero, one_mul, add_zero, hRad u]
  simp only [hpart]
  have hlim : Tendsto (fun N : ℕ => β ^ N * a N) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (by simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const KR)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 N)]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hRb _) u ω) (pow_nonneg hβ0 N)
  simpa using (tendsto_const_nhds (x := R u ω)).sub hlim

/-- Cochrane (2023), §7.6.1, p. 230 (under uncertainty): **the exact condition for reverse
engineering QE from reserves.** With `1/P` adapted, bounded and bounded away from zero, and `R`
adapted and bounded, bounded QE purchases fixed at date 0 that satisfy (7.23) at every date
`t ≥ 1` exist if and only if every implied purchase `c_t` (`t ≥ 1`) is known at date 0. -/
theorem qe_exists_iff (hpo : 𝔼.PullOut) {β om B Kx KR xmin : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hxmin : 0 < xmin) {Mr x s VT : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (hxb : ∀ t ω, |x t ω| ≤ Kx) (hxlo : ∀ t ω, xmin ≤ x t ω)
    (hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * 𝔼.E t (x (t + k)) ω)) (VT t ω))
    (hRad : ∀ t, 𝔼.E t (resid 𝔼 β VT Mr x s t) = resid 𝔼 β VT Mr x s t)
    (hRb : ∀ t ω, |resid 𝔼 β VT Mr x s t ω| ≤ KR) :
    (∃ b : ℕ → Ω → ℝ, (∀ j, 𝔼.E 0 (b j) = b j) ∧ (∃ Kb, ∀ j ω, |b j ω| ≤ Kb) ∧
      ∀ t, QEPV 𝔼 β om B b Mr x s (t + 1)) ↔
      ∀ t, 𝔼.E 0 (qeImplied 𝔼 β VT Mr x s (t + 1)) = qeImplied 𝔼 β VT Mr x s (t + 1) := by
  have hxpos : ∀ t ω, 0 < x t ω := fun t ω => hxmin.trans_le (hxlo t ω)
  constructor
  · rintro ⟨b, hb0, ⟨Kb, hbb⟩, hpv⟩ t
    have h := qe_necessary 𝔼 hpo hβ0 hβ1 hx hxb hT hb0 hbb hpv t
    have hc : qeImplied 𝔼 β VT Mr x s (t + 1) = b (t + 1) := by
      funext ω
      have := congrFun h ω
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply] at this
      simp only [qeImplied, Pi.div_apply, Pi.sub_apply, Pi.smul_apply]
      rw [div_eq_iff (hxpos _ ω).ne', ← this]
    rw [hc]; exact hb0 _
  · intro hc0
    set b : ℕ → Ω → ℝ := fun j => if j = 0 then 0 else qeImplied 𝔼 β VT Mr x s j with hbdef
    refine ⟨b, fun j => ?_, ⟨(KR + β * KR) / xmin, fun j ω => ?_⟩, fun t ω => ?_⟩
    · rcases j with _ | j
      · simp only [hbdef, ↓reduceIte, map_zero]
      · simp only [hbdef, Nat.add_one_ne_zero, ↓reduceIte]; exact hc0 j
    · rcases j with _ | j
      · simp only [hbdef, ↓reduceIte, Pi.zero_apply, abs_zero]
        exact div_nonneg (add_nonneg ((abs_nonneg _).trans (hRb 0 ω))
          (mul_nonneg hβ0 ((abs_nonneg _).trans (hRb 0 ω)))) hxmin.le
      · simp only [hbdef, Nat.add_one_ne_zero, ↓reduceIte, qeImplied, Pi.div_apply,
          Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [abs_div, abs_of_pos (hxpos _ ω)]
        have hKR : 0 ≤ KR := (abs_nonneg _).trans (hRb 0 ω)
        have hK0 : 0 ≤ KR + β * KR := add_nonneg hKR (mul_nonneg hβ0 hKR)
        refine div_le_div₀ hK0 ?_ hxmin (hxlo _ ω)
        refine (abs_sub _ _).trans (add_le_add (hRb _ ω) ?_)
        rw [abs_mul, abs_of_nonneg hβ0]
        exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hRb _) _ ω) hβ0
    · have h := qe_sufficient 𝔼 hpo hβ0 hβ1 hxpos hT hRad hRb hc0 t ω
      convert h using 2 with k
      simp only [hbdef, show t + 1 + k ≠ 0 by omega, ↓reduceIte]

/-! ### A date-0 QE policy cannot absorb later news -/

/-- Cochrane (2023), §7.6.1 (illustration): in the coin-flip economy the present value of
surpluses from date 2 on is `1/(1−β)` in every state (the shock is at date 1). -/
theorem coin_pv_two {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ω : Bool × Bool) :
    pvSurplus ExpectationsFiniteTree.coinSystem β coinS 2 ω = 1 / (1 - β) := by
  have hterm : ∀ k, surplusTerm ExpectationsFiniteTree.coinSystem β coinS 2 k ω = β ^ k := by
    intro k
    have hf : coinS (2 + k) = fun _ => (1 : ℝ) := by
      funext ω'; simp [coinS, show ¬ (2 + k = 1) by omega]
    simp only [surplusTerm, hf, ExpectationsFiniteTree.coinSystem.const, mul_one]
  rw [pvSurplus]
  simp only [hterm]
  rw [tsum_geometric_of_lt_one hβ0 hβ1, one_div]

/-- Cochrane (2023), §7.6.1 (under uncertainty): **a date-0-fixed QE policy cannot absorb later
news.** In the coin-flip economy (`0 ≤ β < 1`, surplus shock at date 1), for any bounded
deterministic desired path `1/P_t = p_t`, deterministic reserves `M_{t−1}^{(t)} = m_t` and a
convergent Treasury value, no bounded QE purchases fixed at date 0 satisfy (7.23) at every
`t ≥ 1`. -/
theorem coin_no_qe {β om B Kx : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (p m vt : ℕ → ℝ)
    (hpb : ∀ t, |p t| ≤ Kx)
    (hvt : ∀ t, HasSum (fun k : ℕ => β ^ k * (om ^ k * B * p (t + k))) (vt t)) :
    ¬ ∃ b : ℕ → Bool × Bool → ℝ, (∀ j, ExpectationsFiniteTree.coinSystem.E 0 (b j) = b j) ∧
      (∃ Kb, ∀ j ω, |b j ω| ≤ Kb) ∧
      ∀ t, QEPV ExpectationsFiniteTree.coinSystem β om B b (fun t _ => m t) (fun t _ => p t)
        coinS (t + 1) := by
  rintro ⟨b, hb0, ⟨Kb, hbb⟩, hpv⟩
  have hc : ∀ (t : ℕ) (c : ℝ), ExpectationsFiniteTree.coinSystem.E t (fun _ => c) = fun _ => c :=
    fun t c => ExpectationsFiniteTree.coinSystem.const t c
  have hT : ∀ t ω, HasSum (fun k : ℕ => β ^ k * (om ^ k * B *
      ExpectationsFiniteTree.coinSystem.E t ((fun t _ => p t) (t + k)) ω)) (vt t) := by
    intro t ω
    simp only [hc]
    exact hvt t
  have h := qe_necessary ExpectationsFiniteTree.coinSystem
    (ExpectationsFiniteTree.finiteTree_pullOut ExpectationsFiniteTree.coinTree) hβ0 hβ1
    (x := fun t _ => p t)
    (VT := fun t _ => vt t) (fun t => hc t (p t)) (fun t _ => hpb t) hT hb0 hbb hpv 0
  -- the date-2 residual is a constant
  have hR2 : resid ExpectationsFiniteTree.coinSystem β (fun t _ => vt t) (fun t _ => m t)
      (fun t _ => p t) coinS 2 = fun _ => 1 / (1 - β) - m 2 * p 2 - vt 2 := by
    funext ω; simp only [resid, coin_pv_two hβ0 hβ1 ω]
  rw [hR2, hc] at h
  -- so `b_1 p_1 = 1/(1−β) + ε_1 − const`, which is not known at date 0
  have hfun : b 1 * (fun _ => p 1) = (fun _ => 1 / (1 - β) - m 1 * p 1 - vt 1 -
      β * (1 / (1 - β) - m 2 * p 2 - vt 2)) + ExpectationsFiniteTree.coinShock 1 := by
    rw [h]
    funext ω
    simp only [resid, coin_pv hβ0 hβ1 ω, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul]
    ring
  have hpo : ExpectationsFiniteTree.coinSystem.PullOut :=
    ExpectationsFiniteTree.finiteTree_pullOut ExpectationsFiniteTree.coinTree
  have hknown : ExpectationsFiniteTree.coinSystem.E 0 (b 1 * fun _ => p 1) =
      b 1 * fun _ => p 1 := by
    rw [mul_comm, hpo 0 _ _ (hc 0 (p 1)), hb0 1]
  have hE0 := ExpectationsFiniteTree.coinShock_mean_zero 0
  rw [zero_add] at hE0
  rw [hfun, map_add, hc, hE0] at hknown
  have := congrFun hknown (true, true)
  simp [ExpectationsFiniteTree.coinShock] at this

end Cochrane.LongTermDebtDynamics.TidyR5QEReverse
