/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.InflTargetPredetermined

/-!
# Reflections: the reaction function (4.1)

Woodford (2003), *Interest and Prices*, Chapter 8, §4.1, pp. 610–613: eq. (4.1), the reaction
function implementing the optimal target criterion (2.32) when spending and pricing decisions are
predetermined `d` periods in advance (`γ = 0`, footnote 51), compared with Ch. 7, eq. (5.5).

## Main results

* `rule41_eq_E_rule55`: the right-hand side of (4.1) is `E_{t−d}` applied to the right-hand side of
  Ch. 7 (5.5).
* `rule41_iff`: given (2.28) and (2.33) at date `t`, the reaction function (4.1) holds iff the
  target criterion (2.32) holds and the interest rate is forecastable `d` periods ahead (2.34).
* `rule41_unique`, `rule41_exists`: commitment to (4.1) determines a unique bounded equilibrium
  `(π, x, i)` given the history, and it exists for bounded shocks; `rule41_timelesslyOptimal`: its
  inflation/output paths are optimal from a timeless perspective (via §2.4).
-/

namespace Woodford.OptimalPolicyRules.Reflections

open Filter Topology
open InflTargetPredetermined (qd qd_apply AS IS Predet TC Eqm TimelesslyOptimal)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), Ch. 7, eq. (5.5), p. 530: the right-hand side of the expectations-based
reaction function, `rⁿ_t + κ/(σ(κ²+λ)) u_t + [1 + βκ/(σ(κ²+λ))] E_tπ_{t+1} + σ⁻¹E_t x_{t+1}
  − λ/(σ(κ²+λ)) x_{t−1}`. -/
noncomputable def rhs55 (β κ σ lam : ℝ) (rn u π x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  rn t + (κ / (σ * (κ ^ 2 + lam))) • u t
    + (1 + β * κ / (σ * (κ ^ 2 + lam))) • 𝔼.E t (π (t + 1)) + σ⁻¹ • 𝔼.E t (x (t + 1))
    - (lam / (σ * (κ ^ 2 + lam))) • x (t - 1)

/-- Woodford (2003), eq. (4.1), p. 612: the right-hand side of the reaction function with every term
conditioned on date-`(t − d)` information. -/
noncomputable def rhs41 (β κ σ lam : ℝ) (d : ℕ) (rn u π x : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  𝔼.E (t - d) (rn t) + (κ / (σ * (κ ^ 2 + lam))) • 𝔼.E (t - d) (u t)
    + (1 + β * κ / (σ * (κ ^ 2 + lam))) • 𝔼.E (t - d) (π (t + 1))
    + σ⁻¹ • 𝔼.E (t - d) (x (t + 1)) - (lam / (σ * (κ ^ 2 + lam))) • 𝔼.E (t - d) (x (t - 1))

/-- Woodford (2003), p. 612 (**(4.1) is `E_{t−d}` of Ch. 7 (5.5)**). -/
theorem rule41_eq_E_rule55 (β κ σ lam : ℝ) (d : ℕ) (rn u π x : ℕ → Ω → ℝ) (t : ℕ) :
    rhs41 𝔼 β κ σ lam d rn u π x t = 𝔼.E (t - d) (rhs55 𝔼 β κ σ lam rn u π x t) := by
  unfold rhs41 rhs55
  simp only [map_add, map_sub, map_smul, 𝔼.tower (Nat.sub_le t d)]

/-- Woodford (2003), p. 612 (**(4.1) implements (2.32)**): suppose (2.28) (with `γ = 0`) and (2.33)
hold at a date `t ≥ t0 + d` with the output gap predetermined and `σ, κ ≠ 0`, `κ² + λ ≠ 0`.
Then the reaction function (4.1) holds at `t` iff the target criterion (2.32) holds at `t` and the
interest rate is forecastable `d` periods ahead (2.34). -/
theorem rule41_iff {β κ σ lam : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hD : κ ^ 2 + lam ≠ 0) {d t0 : ℕ}
    {u rn π x i : ℕ → Ω → ℝ} (hAS : AS 𝔼 κ β 0 d t0 u π x) (hIS : IS 𝔼 σ d t0 rn π x i)
    (hPx : Predet 𝔼 d t0 x) {t : ℕ} (ht : t0 + d ≤ t)
    (hxm : 𝔼.E (t - d) (x (t - 1)) = x (t - 1)) :
    i t = rhs41 𝔼 β κ σ lam d rn u π x t ↔
      ((∀ ω, qd 0 π t ω + lam / κ * (x t ω - x (t - 1) ω) = 0) ∧ 𝔼.E (t - d) (i t) = i t) := by
  -- the identity `σ(κ² + λ)(E_{t−d} i_t − rhs₄₁) = −(κπ_t + λ(x_t − x_{t−1}))`
  have hx := hPx t ht
  have hA := congrFun (hAS t ht)
  have hI := congrFun (hIS t ht)
  have key : ∀ ω, σ * (κ ^ 2 + lam) * (𝔼.E (t - d) (i t) ω - rhs41 𝔼 β κ σ lam d rn u π x t ω)
      = -(κ * π t ω + lam * (x t ω - x (t - 1) ω)) := by
    intro ω
    have a := hA ω
    have b := hI ω
    have hq1 : qd 0 π (t + 1) = π (t + 1) := by funext ω'; simp [qd]
    rw [hx, hq1] at a
    simp only [qd_apply, zero_mul, sub_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a
    simp only [map_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at b
    simp only [rhs41, hxm, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have ha : σ * σ⁻¹ = 1 := mul_inv_cancel₀ hσ
    have hb : σ * (κ ^ 2 + lam) * (σ * (κ ^ 2 + lam))⁻¹ = 1 :=
      mul_inv_cancel₀ (mul_ne_zero hσ hD)
    simp only [div_eq_mul_inv]
    linear_combination (κ ^ 2 + lam) * b + κ * a
      - (κ * 𝔼.E (t - d) (u t) ω + β * κ * 𝔼.E (t - d) (π (t + 1)) ω - lam * x (t - 1) ω) * hb
      - (κ ^ 2 + lam) * 𝔼.E (t - d) (x (t + 1)) ω * ha
  have hR : 𝔼.E (t - d) (rhs41 𝔼 β κ σ lam d rn u π x t) = rhs41 𝔼 β κ σ lam d rn u π x t := by
    unfold rhs41
    simp only [map_add, map_sub, map_smul, 𝔼.E_E_self]
  have hsD : σ * (κ ^ 2 + lam) ≠ 0 := mul_ne_zero hσ hD
  constructor
  · intro h
    have hpre : 𝔼.E (t - d) (i t) = i t := by rw [h, hR]
    refine ⟨fun ω => ?_, hpre⟩
    have k := key ω
    rw [hpre, h, sub_self, mul_zero] at k
    simp only [qd_apply, zero_mul, sub_zero]
    field_simp
    linarith
  · rintro ⟨htc, hpre⟩
    funext ω
    have k := key ω
    have hc := htc ω
    simp only [qd_apply, zero_mul, sub_zero] at hc
    have : κ * π t ω + lam * (x t ω - x (t - 1) ω) = 0 := by
      field_simp at hc
      linarith
    rw [this, neg_zero, hpre] at k
    have := (mul_eq_zero.mp k).resolve_left hsD
    linarith

/-- Woodford (2003), p. 612: an equilibrium under the reaction function (4.1) — (2.28) with
`γ = 0`, (2.33), (4.1) at every `t ≥ t0 + d`, inflation and output predetermined. -/
def Eqm41 (β κ σ lam : ℝ) (d t0 : ℕ) (u rn π x i : ℕ → Ω → ℝ) : Prop :=
  AS 𝔼 κ β 0 d t0 u π x ∧ IS 𝔼 σ d t0 rn π x i ∧ Predet 𝔼 d t0 π ∧ Predet 𝔼 d t0 x ∧
    ∀ t, t0 + d ≤ t → i t = rhs41 𝔼 β κ σ lam d rn u π x t

/-- Woodford (2003), p. 612: in an equilibrium under (4.1) the target criterion (2.32) holds at
every date `t ≥ t0 + d` (with the history `x_{t0+d−1}` known at `t0`). -/
theorem eqm41_tc {β κ σ lam : ℝ} (hκ : κ ≠ 0) (hσ : σ ≠ 0) (hD : κ ^ 2 + lam ≠ 0) {d t0 : ℕ}
    {u rn π x i : ℕ → Ω → ℝ} (h : Eqm41 𝔼 β κ σ lam d t0 u rn π x i)
    (hxh : 𝔼.E t0 (x (t0 + d - 1)) = x (t0 + d - 1)) :
    TC 0 (lam / κ) d t0 π x ∧ ∀ t, t0 + d ≤ t → 𝔼.E (t - d) (i t) = i t := by
  obtain ⟨hAS, hIS, hPπ, hPx, h41⟩ := h
  have hxm : ∀ t, t0 + d ≤ t → 𝔼.E (t - d) (x (t - 1)) = x (t - 1) := by
    intro t ht
    rcases Nat.eq_or_lt_of_le ht with h0 | h0
    · subst h0
      rw [show t0 + d - d = t0 by omega]
      exact hxh
    · exact ForwardSolution.E_of_known 𝔼 (by omega) (hPx (t - 1) (by omega))
  refine ⟨fun t ht ω => ?_, fun t ht => ?_⟩
  · exact ((rule41_iff 𝔼 hκ hσ hD hAS hIS hPx ht (hxm t ht)).mp (h41 t ht)).1 ω
  · exact ((rule41_iff 𝔼 hκ hσ hD hAS hIS hPx ht (hxm t ht)).mp (h41 t ht)).2

/-- Woodford (2003), p. 612 (**determinacy under (4.1)**): two bounded equilibria under the
reaction function (4.1) with the same history coincide — inflation, output and the interest rate
— at every date `t ≥ t0 + d` (`0 < β`, `κ, λ > 0`, `σ ≠ 0`). -/
theorem rule41_unique {β κ σ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (hσ : σ ≠ 0)
    {d t0 : ℕ} {u rn π x i π' x' i' : ℕ → Ω → ℝ}
    (h : Eqm41 𝔼 β κ σ lam d t0 u rn π x i) (h' : Eqm41 𝔼 β κ σ lam d t0 u rn π' x' i')
    (hbx : BoundedProc x) (hbx' : BoundedProc x')
    (hx0 : x (t0 + d - 1) = x' (t0 + d - 1)) (hπ0 : π (t0 + d - 1) = π' (t0 + d - 1))
    (hxh : 𝔼.E t0 (x (t0 + d - 1)) = x (t0 + d - 1)) (s : ℕ) :
    π (t0 + d + s) = π' (t0 + d + s) ∧ x (t0 + d + s) = x' (t0 + d + s) ∧
      i (t0 + d + s) = i' (t0 + d + s) := by
  have hD : κ ^ 2 + lam ≠ 0 := by positivity
  have hxh' : 𝔼.E t0 (x' (t0 + d - 1)) = x' (t0 + d - 1) := by rw [← hx0]; exact hxh
  obtain ⟨tc, _⟩ := eqm41_tc 𝔼 hκ.ne' hσ hD h hxh
  obtain ⟨tc', _⟩ := eqm41_tc 𝔼 hκ.ne' hσ hD h' hxh'
  have e : Eqm 𝔼 κ β 0 (lam / κ) d t0 u π x := ⟨h.1, tc, h.2.2.2.1, h.2.2.1⟩
  have e' : Eqm 𝔼 κ β 0 (lam / κ) d t0 u π' x' := ⟨h'.1, tc', h'.2.2.2.1, h'.2.2.1⟩
  have hall : ∀ k, π (t0 + d + k) = π' (t0 + d + k) ∧ x (t0 + d + k) = x' (t0 + d + k) :=
    fun k => InflTargetPredetermined.eqm_unique 𝔼 hβ hκ (div_pos hlam hκ) e e' hbx hbx' hx0
      hπ0 k
  refine ⟨(hall s).1, (hall s).2, ?_⟩
  have ht : t0 + d ≤ t0 + d + s := by omega
  rw [h.2.2.2.2 _ ht, h'.2.2.2.2 _ ht]
  have hx1 : x (t0 + d + s - 1) = x' (t0 + d + s - 1) := by
    cases s with
    | zero => simpa using hx0
    | succ k => rw [show t0 + d + (k + 1) - 1 = t0 + d + k by omega]; exact (hall k).2
  unfold rhs41
  rw [show t0 + d + s + 1 = t0 + d + (s + 1) by omega, (hall (s + 1)).1, (hall (s + 1)).2, hx1]

/-- Woodford (2003), p. 612 (**existence under (4.1)**): for `0 < β`, `κ, λ > 0`, `σ ≠ 0`, bounded
shocks `u`, `rⁿ` and a history known at `t0`, there is a bounded equilibrium under the reaction
function (4.1). -/
theorem rule41_exists {β κ σ lam : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hlam : 0 < lam) (hσ : σ ≠ 0)
    {d t0 : ℕ} (ht0 : 1 ≤ t0) {u rn : ℕ → Ω → ℝ} (hu : BoundedProc u) (hrn : BoundedProc rn)
    {πh xh : Ω → ℝ} {K : ℝ} (hπK : ∀ ω, |πh ω| ≤ K) (hxK : ∀ ω, |xh ω| ≤ K)
    (hπh : 𝔼.E t0 πh = πh) (hxh : 𝔼.E t0 xh = xh) :
    ∃ π x i : ℕ → Ω → ℝ, Eqm41 𝔼 β κ σ lam d t0 u rn π x i ∧ BoundedProc π ∧ BoundedProc x ∧
      BoundedProc i ∧ π (t0 + d - 1) = πh ∧ x (t0 + d - 1) = xh := by
  have hD : κ ^ 2 + lam ≠ 0 := by positivity
  obtain ⟨π, x, ⟨hAS, hTC, hPx, hPπ⟩, hbπ, hbx, h1, h2⟩ :=
    InflTargetPredetermined.eqm_exists 𝔼 (d := d) hβ hκ (div_pos hlam hκ) le_rfl zero_le_one ht0
      hu hπK hxK hπh hxh
  -- the interest rate read off (2.33)
  set i : ℕ → Ω → ℝ := fun t => 𝔼.E (t - d) (rn t) + 𝔼.E (t - d) (π (t + 1))
    + σ⁻¹ • (𝔼.E (t - d) (x (t + 1)) - x t) with hi
  have hIS : IS 𝔼 σ d t0 rn π x i := by
    intro t ht
    simp only [hi, map_add, map_sub, map_smul, 𝔼.E_E_self, hPx t ht]
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hipre : ∀ t, t0 + d ≤ t → 𝔼.E (t - d) (i t) = i t := by
    intro t ht
    simp only [hi, map_add, map_sub, map_smul, 𝔼.E_E_self, hPx t ht]
  have hxm : ∀ t, t0 + d ≤ t → 𝔼.E (t - d) (x (t - 1)) = x (t - 1) := by
    intro t ht
    rcases Nat.eq_or_lt_of_le ht with h0 | h0
    · subst h0
      rw [show t0 + d - d = t0 by omega, h2]
      exact hxh
    · exact ForwardSolution.E_of_known 𝔼 (by omega) (hPx (t - 1) (by omega))
  refine ⟨π, x, i, ⟨hAS, hIS, hPπ, hPx, fun t ht => ?_⟩, hbπ, hbx, ?_, h1, h2⟩
  · exact ((rule41_iff 𝔼 hκ.ne' hσ hD hAS hIS hPx ht (hxm t ht)).mpr
      ⟨fun ω => hTC t ht ω, hipre t ht⟩)
  · obtain ⟨M1, hM1⟩ := hrn
    obtain ⟨M2, hM2⟩ := hbπ
    obtain ⟨M3, hM3⟩ := hbx
    refine ⟨M1 + M2 + |σ⁻¹| * (M3 + M3), fun t ω => ?_⟩
    simp only [hi, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have e1 := 𝔼.abs_E_le (hM1 t) (t - d) ω
    have e2 := 𝔼.abs_E_le (hM2 (t + 1)) (t - d) ω
    have e3 := 𝔼.abs_E_le (hM3 (t + 1)) (t - d) ω
    have e4 := hM3 t ω
    calc |𝔼.E (t - d) (rn t) ω + 𝔼.E (t - d) (π (t + 1)) ω
          + σ⁻¹ * (𝔼.E (t - d) (x (t + 1)) ω - x t ω)|
        ≤ |𝔼.E (t - d) (rn t) ω| + |𝔼.E (t - d) (π (t + 1)) ω|
          + |σ⁻¹ * (𝔼.E (t - d) (x (t + 1)) ω - x t ω)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ M1 + M2 + |σ⁻¹| * (M3 + M3) := by
        rw [abs_mul]
        exact add_le_add (add_le_add e1 e2)
          (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add e3 e4)) (abs_nonneg _))

/-- Woodford (2003), pp. 571–572, 612 (**(4.1) implements the optimal policy**): in an equilibrium
under the reaction function (4.1), the inflation and output paths are optimal from a timeless
perspective, and the interest rate satisfies (2.34). -/
theorem rule41_timelesslyOptimal {β κ σ lam xs : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hlam : 0 < lam) (hσ : σ ≠ 0) (hPO : 𝔼.PullOut) {d t0 : ℕ} (ht0 : 1 ≤ t0)
    {u rn π x i : ℕ → Ω → ℝ} (h : Eqm41 𝔼 β κ σ lam d t0 u rn π x i) (hbπ : BoundedProc π)
    (hbx : BoundedProc x) (hxh : 𝔼.E t0 (x (t0 + d - 1)) = x (t0 + d - 1)) :
    TimelesslyOptimal 𝔼 β κ 0 lam xs d t0 u π x ∧
      ∀ t, t0 + d ≤ t → 𝔼.E (t - d) (i t) = i t := by
  have hD : κ ^ 2 + lam ≠ 0 := by positivity
  obtain ⟨tc, hpre⟩ := eqm41_tc 𝔼 hκ.ne' hσ hD h hxh
  exact ⟨InflTargetPredetermined.eqm_timelesslyOptimal 𝔼 hβ0 hβ1 hκ.ne' hlam.le hPO ht0
    ⟨h.1, tc, h.2.2.2.1, h.2.2.1⟩ hbπ hbx, hpre⟩

end Woodford.OptimalPolicyRules.Reflections
