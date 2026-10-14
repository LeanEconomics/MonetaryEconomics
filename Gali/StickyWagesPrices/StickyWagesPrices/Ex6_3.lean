/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyWagesPrices.Expectations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Exercise 6.3: labour market institutions and long-run money non-neutrality

Galí (2015), Chapter 6, Exercise 6.3, pp. 196–197 (Blanchard and Summers 1986). A competitive
firm maximises `P_t Y_t − W_t N_t` with `Y_t = N_t^{1−α}`; labour supply is inelastic at one;
the goods market clears at `Y_t = M_t/P_t`; money follows `m_t = ρ_m m_{t−1} + ε_t`.

## The firm (exact)
* `hasDerivAt_profit`, `profit_le`, `labor_demand_iff`: for `0 ≤ α < 1`, `N > 0` maximises
  profit on `N > 0` iff `W = P (1 − α) N^{−α}` (necessity from the derivative, sufficiency from
  Bernoulli's inequality, i.e. concavity).
* `labor_demand_log`, `production_log`, `goods_log`: the three equations are exactly
  `w − p = log(1 − α) − α n`, `y = (1 − α) n`, `y = m − p` in logs, so the log-linear model
  `Static` is exact.
* `static_iff`: given the wage, `n = m − w + log(1 − α)`, `y = (1 − α) n`,
  `p = w − log(1 − α) + α n`.

## (a) Flexible competitive wages: `flexible_iff`
`n = 0` (inelastic supply at one), `y = 0`, `p = m`, `w − p = log(1 − α)`.

## (b) Wages set in advance, `E_{t−1} n_t = 0`
* `advance_iff`: the condition holds iff `w_t = ρ_m m_{t−1} + log(1 − α) (= E_{t−1} m_t + …)`.
* `advance_solution`: `n_t = m_t − E_{t−1} m_t = ε_t`, `y_t = (1 − α) ε_t`,
  `p_t = m_t − (1 − α) ε_t`, `w_t − p_t = log(1 − α) − α ε_t`, and
  `advance_no_persistence`: `E_t n_{t+k} = 0` for `k ≥ 1`.
* `advance_exists`: the equilibrium exists.

## (c) Union wage setting, `E_{t−1} n_t = n_{t−1}`
* `union_iff`: the condition holds iff `w_t = ρ_m m_{t−1} + log(1 − α) − n_{t−1}`.
* `union_solution`: `n_t = n_{t−1} + ε_t`, `y_t = y_{t−1} + (1 − α) ε_t` (unit root),
  `union_hysteresis`: `E_t n_{t+k} = n_t` for all `k` (shocks have permanent effects).
* `union_exists`: the equilibrium exists for any initial employment.

## (d)
Part (d) asks for a discussion of empirical relevance; it is not formalised.
-/

namespace Gali.StickyWagesPrices.Ex6_3

/-! ### The firm -/

/-- Galí (2015), Exercise 6.3, p. 196: the firm's profit `P N^{1−α} − W N`. -/
noncomputable def profit (P W α N : ℝ) : ℝ := P * N ^ (1 - α) - W * N

/-- Galí (2015), Exercise 6.3, p. 196: the marginal profit of labour is
`P (1 − α) N^{−α} − W`. -/
theorem hasDerivAt_profit (P W α : ℝ) {N : ℝ} (hN : 0 < N) :
    HasDerivAt (fun N' => profit P W α N') (P * ((1 - α) * N ^ (-α)) - W) N := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ (1 - α)) ((1 - α) * N ^ (1 - α - 1)) N :=
    Real.hasDerivAt_rpow_const (Or.inl hN.ne')
  have h2 := HasDerivAt.sub (h1.const_mul P) ((hasDerivAt_id N).const_mul W)
  rw [show 1 - α - 1 = -α by ring, mul_one] at h2
  exact h2

/-- Galí (2015), Exercise 6.3, p. 196 (**sufficiency**): if `W = P (1 − α) N^{−α}` then `N`
maximises profit over all `N' > 0` (Bernoulli's inequality, i.e. concavity of `N^{1−α}`). -/
theorem profit_le {P W α N N' : ℝ} (hP : 0 ≤ P) (hα0 : 0 ≤ α) (hα1 : α < 1) (hN : 0 < N)
    (hN' : 0 < N') (hW : W = P * ((1 - α) * N ^ (-α))) :
    profit P W α N' ≤ profit P W α N := by
  have hs : -1 ≤ N' / N - 1 := by
    have : 0 ≤ N' / N := by positivity
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hs (by linarith : 0 ≤ 1 - α)
    (by linarith : 1 - α ≤ 1)
  rw [show 1 + (N' / N - 1) = N' / N by ring, Real.div_rpow hN'.le hN.le] at hb
  have hX : N ^ (1 - α) = N * N ^ (-α) := by
    rw [sub_eq_add_neg, Real.rpow_add hN, Real.rpow_one]
  have hpos : 0 < N ^ (1 - α) := Real.rpow_pos_of_pos hN _
  rw [div_le_iff₀ hpos] at hb
  have key : N' ^ (1 - α) ≤ N * N ^ (-α) + (1 - α) * N ^ (-α) * (N' - N) := by
    calc N' ^ (1 - α) ≤ (1 + (1 - α) * (N' / N - 1)) * N ^ (1 - α) := hb
      _ = _ := by rw [hX]; field_simp
  unfold profit
  rw [hW, hX]
  nlinarith [mul_le_mul_of_nonneg_left key hP]

/-- Galí (2015), Exercise 6.3, p. 196 (**labour demand, necessary and sufficient**): for
`P > 0`, `0 ≤ α < 1`, `N > 0`, `N` maximises profit on `N > 0` iff
`W/P = (1 − α) N^{−α}`. -/
theorem labor_demand_iff {P W α N : ℝ} (hP : 0 < P) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hN : 0 < N) :
    IsMaxOn (fun N' => profit P W α N') (Set.Ioi 0) N ↔ W = P * ((1 - α) * N ^ (-α)) := by
  constructor
  · intro h
    have hz := (h.isLocalMax (Ioi_mem_nhds hN)).hasDerivAt_eq_zero (hasDerivAt_profit P W α hN)
    linarith
  · intro hW
    exact isMaxOn_iff.mpr fun N' hN' => profit_le hP.le hα0 hα1 hN hN' hW

/-- Galí (2015), Exercise 6.3, p. 196: labour demand in logs is exactly
`w − p = log(1 − α) − α n`. -/
theorem labor_demand_log {P W α N : ℝ} (hP : 0 < P) (hW : 0 < W) (hα1 : α < 1) (hN : 0 < N) :
    W = P * ((1 - α) * N ^ (-α)) ↔
      Real.log W - Real.log P = Real.log (1 - α) - α * Real.log N := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have hr : 0 < N ^ (-α) := Real.rpow_pos_of_pos hN _
  have hlog : Real.log (P * ((1 - α) * N ^ (-α))) =
      Real.log P + (Real.log (1 - α) - α * Real.log N) := by
    rw [Real.log_mul hP.ne' (by positivity), Real.log_mul h1.ne' hr.ne', Real.log_rpow hN]
    ring
  constructor
  · intro h
    rw [h, hlog]
    ring
  · intro h
    refine Real.log_injOn_pos (Set.mem_Ioi.mpr hW) (Set.mem_Ioi.mpr (by positivity)) ?_
    rw [hlog]
    linarith

/-- Galí (2015), Exercise 6.3, p. 196: the technology `Y = N^{1−α}` is exactly
`y = (1 − α) n` in logs. -/
theorem production_log {Y N α : ℝ} (hY : 0 < Y) (hN : 0 < N) :
    Y = N ^ (1 - α) ↔ Real.log Y = (1 - α) * Real.log N := by
  constructor
  · intro h
    rw [h, Real.log_rpow hN]
  · intro h
    refine Real.log_injOn_pos (Set.mem_Ioi.mpr hY)
      (Set.mem_Ioi.mpr (Real.rpow_pos_of_pos hN _)) ?_
    rw [h, Real.log_rpow hN]

/-- Galí (2015), Exercise 6.3, p. 196: goods market clearing `Y = M/P` is exactly
`y = m − p` in logs. -/
theorem goods_log {Y M P : ℝ} (hY : 0 < Y) (hM : 0 < M) (hP : 0 < P) :
    Y = M / P ↔ Real.log Y = Real.log M - Real.log P := by
  constructor
  · intro h
    rw [h, Real.log_div hM.ne' hP.ne']
  · intro h
    refine Real.log_injOn_pos (Set.mem_Ioi.mpr hY) (Set.mem_Ioi.mpr (by positivity)) ?_
    rw [h, Real.log_div hM.ne' hP.ne']

/-! ### The log-linear model -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), Exercise 6.3, p. 196: the (exact) log model given the wage: labour demand
`w − p = log(1 − α) − α n`, technology `y = (1 − α) n`, goods market `y = m − p`. -/
def Static (α : ℝ) (m n y p w : ℕ → Ω → ℝ) : Prop :=
  ∀ t, w t - p t = (fun _ => Real.log (1 - α)) - α • n t ∧ y t = (1 - α) • n t ∧
    y t = m t - p t

/-- Galí (2015), Exercise 6.3, p. 196: the static block solved given the wage,
`n = m − w + log(1 − α)`, `y = (1 − α) n`, `p = w − log(1 − α) + α n`. -/
theorem static_iff {α : ℝ} {m n y p w : ℕ → Ω → ℝ} :
    Static α m n y p w ↔ ∀ t, n t = m t - w t + (fun _ => Real.log (1 - α)) ∧
      y t = (1 - α) • n t ∧ p t = w t - (fun _ => Real.log (1 - α)) + α • n t := by
  refine forall_congr' fun t => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, ?_⟩ <;> funext ω <;>
    · have e1 := congrFun h1 ω
      have e2 := congrFun h2 ω
      have e3 := congrFun h3 ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
      linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, ?_⟩ <;> funext ω <;>
    · have e1 := congrFun h1 ω
      have e2 := congrFun h2 ω
      have e3 := congrFun h3 ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
      linarith

/-- Galí (2015), Exercise 6.3(a), p. 196 (**necessary and sufficient**): with flexible
competitive wages and labour supply inelastic at one (`n = log 1 = 0`), the equilibrium is
`n = 0`, `y = 0`, `p = m`, `w − p = log(1 − α)`. -/
theorem flexible_iff {α : ℝ} {m n y p w : ℕ → Ω → ℝ} :
    (Static α m n y p w ∧ ∀ t, n t = 0) ↔
      ∀ t, n t = 0 ∧ y t = 0 ∧ p t = m t ∧ w t - p t = fun _ => Real.log (1 - α) := by
  constructor
  · rintro ⟨hs, hn⟩ t
    obtain ⟨h1, h2, h3⟩ := hs t
    have hy : y t = 0 := by rw [h2, hn t, smul_zero]
    refine ⟨hn t, hy, ?_, ?_⟩
    · rw [hy] at h3
      exact (sub_eq_zero.mp h3.symm).symm
    · rw [h1, hn t, smul_zero, sub_zero]
  · intro h
    refine ⟨fun t => ⟨?_, ?_, ?_⟩, fun t => (h t).1⟩
    · rw [(h t).2.2.2, (h t).1, smul_zero, sub_zero]
    · rw [(h t).2.1, (h t).1, smul_zero]
    · rw [(h t).2.1, (h t).2.2.1, sub_self]

/-! ### (b) Wages set in advance -/

/-- Galí (2015), Exercise 6.3(b), p. 196 (**necessary and sufficient**): with a predetermined
wage, `E_{t−1} n_t = 0` holds iff `w_t = ρ_m m_{t−1} + log(1 − α)`. -/
theorem advance_iff {α ρm : ℝ} {m n y p w : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m)
    (hw : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) (hs : Static α m n y p w) :
    (∀ t, 𝔼.E t (n (t + 1)) = 0) ↔
      ∀ t, w (t + 1) = ρm • m t + fun _ => Real.log (1 - α) := by
  have hE : ∀ t, 𝔼.E t (n (t + 1)) = ρm • m t - w (t + 1) + fun _ => Real.log (1 - α) := by
    intro t
    rw [((static_iff (Ω := Ω)).mp hs (t + 1)).1, map_add, map_sub, hm.2 t, hw t, 𝔼.const]
  refine forall_congr' fun t => ?_
  rw [hE t]
  constructor
  · intro h
    funext ω
    have e := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e ⊢
    linarith
  · intro h
    rw [h]
    abel

/-- Galí (2015), Exercise 6.3(b), pp. 196–197: with wages set in advance so that
`E_{t−1} n_t = 0`: `n_t = m_t − E_{t−1} m_t = ε_t`, `y_t = (1 − α) ε_t`,
`p_t = m_t − (1 − α) ε_t`, and the real wage `w_t − p_t = log(1 − α) − α ε_t`. -/
theorem advance_solution {α ρm : ℝ} {m n y p w : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m)
    (hw : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) (hs : Static α m n y p w)
    (hn : ∀ t, 𝔼.E t (n (t + 1)) = 0) (t : ℕ) :
    n (t + 1) = m (t + 1) - 𝔼.E t (m (t + 1)) ∧ n (t + 1) = m (t + 1) - ρm • m t ∧
      y (t + 1) = (1 - α) • (m (t + 1) - ρm • m t) ∧
      p (t + 1) = m (t + 1) - (1 - α) • (m (t + 1) - ρm • m t) ∧
      w (t + 1) - p (t + 1) = (fun _ => Real.log (1 - α)) - α • (m (t + 1) - ρm • m t) := by
  have hwv := (advance_iff 𝔼 hm hw hs).mp hn t
  obtain ⟨h1, h2, h3⟩ := hs (t + 1)
  have hnv : n (t + 1) = m (t + 1) - ρm • m t := by
    rw [((static_iff (Ω := Ω)).mp hs (t + 1)).1, hwv]
    abel
  have hy : y (t + 1) = (1 - α) • (m (t + 1) - ρm • m t) := by rw [h2, hnv]
  refine ⟨by rw [hnv, hm.2 t], hnv, hy, ?_, by rw [h1, hnv]⟩
  rw [hy] at h3
  rw [h3]
  abel

/-- Galí (2015), Exercise 6.3(b), p. 197 (no persistence): with wages set in advance,
`E_t n_{t+k} = 0` for every `k ≥ 1`: a monetary shock affects employment for one period only. -/
theorem advance_no_persistence {n : ℕ → Ω → ℝ} (hn : ∀ t, 𝔼.E t (n (t + 1)) = 0) (t k : ℕ) :
    𝔼.E t (n (t + k + 1)) = 0 := by
  rw [← 𝔼.tower (Nat.le_add_right t k), hn (t + k), map_zero]

/-- Galí (2015), Exercise 6.3(b), p. 196: the wage set in advance,
`w_{t+1} = ρ_m m_t + log(1 − α)`, from an initial wage `w_0`. -/
noncomputable def wAdv (α ρm : ℝ) (m : ℕ → Ω → ℝ) (w0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => w0
  | t + 1 => ρm • m t + fun _ => Real.log (1 - α)

/-- Galí (2015), Exercise 6.3(b), p. 196 (**existence**): with `w = wAdv` and the static block
solved, the wage is predetermined and `E_{t−1} n_t = 0`. -/
theorem advance_exists {α ρm : ℝ} {m : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m) (w0 : Ω → ℝ) :
    let w := wAdv α ρm m w0
    let n := fun t => m t - w t + fun _ => Real.log (1 - α)
    Static α m n (fun t => (1 - α) • n t) (fun t => w t - (fun _ => Real.log (1 - α)) + α • n t)
        w ∧
      (∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) ∧ ∀ t, 𝔼.E t (n (t + 1)) = 0 := by
  intro w n
  have hwp : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1) := fun t => by
    simp only [w, wAdv]
    rw [map_add, map_smul, hm.1 t, 𝔼.const]
  refine ⟨(static_iff (Ω := Ω)).mpr fun t => ⟨rfl, rfl, rfl⟩, hwp, fun t => ?_⟩
  simp only [n]
  rw [map_add, map_sub, hwp t, hm.2 t, 𝔼.const]
  simp only [w, wAdv]
  abel

/-! ### (c) Union wage setting -/

/-- Galí (2015), Exercise 6.3(c), p. 197 (**necessary and sufficient**): with a predetermined
wage and adapted employment, `E_{t−1} n_t = n_{t−1}` iff
`w_t = ρ_m m_{t−1} + log(1 − α) − n_{t−1}`. -/
theorem union_iff {α ρm : ℝ} {m n y p w : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m)
    (hw : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) (hs : Static α m n y p w) :
    (∀ t, 𝔼.E t (n (t + 1)) = n t) ↔
      ∀ t, w (t + 1) = ρm • m t + (fun _ => Real.log (1 - α)) - n t := by
  have hE : ∀ t, 𝔼.E t (n (t + 1)) = ρm • m t - w (t + 1) + fun _ => Real.log (1 - α) := by
    intro t
    rw [((static_iff (Ω := Ω)).mp hs (t + 1)).1, map_add, map_sub, hm.2 t, hw t, 𝔼.const]
  refine forall_congr' fun t => ?_
  rw [hE t]
  constructor
  · intro h
    rw [← h]
    abel
  · intro h
    rw [h]
    abel

/-- Galí (2015), Exercise 6.3(c), p. 197: under union wage setting employment and output have
a unit root, `n_t = n_{t−1} + ε_t`, `y_t = y_{t−1} + (1 − α) ε_t`, with
`p_t = m_t − y_t` and real wage `w_t − p_t = log(1 − α) − α n_t`. -/
theorem union_solution {α ρm : ℝ} {m n y p w : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m)
    (hw : ∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) (hs : Static α m n y p w)
    (hn : ∀ t, 𝔼.E t (n (t + 1)) = n t) (t : ℕ) :
    n (t + 1) = n t + (m (t + 1) - ρm • m t) ∧
      y (t + 1) = y t + (1 - α) • (m (t + 1) - ρm • m t) ∧ p (t + 1) = m (t + 1) - y (t + 1) ∧
      w (t + 1) - p (t + 1) = (fun _ => Real.log (1 - α)) - α • n (t + 1) := by
  have hwv := (union_iff 𝔼 hm hw hs).mp hn t
  have hnv : n (t + 1) = n t + (m (t + 1) - ρm • m t) := by
    rw [((static_iff (Ω := Ω)).mp hs (t + 1)).1, hwv]
    abel
  obtain ⟨h1, h2, h3⟩ := hs (t + 1)
  refine ⟨hnv, ?_, by rw [h3]; abel, h1⟩
  rw [h2, (hs t).2.1, hnv, smul_add]

/-- Galí (2015), Exercise 6.3(c), p. 197 (**hysteresis**): under union wage setting
`E_t n_{t+k} = n_t` for every horizon `k`: the effect of a monetary shock on employment is
permanent. -/
theorem union_hysteresis {n : ℕ → Ω → ℝ} (hna : 𝔼.Adapted n)
    (hn : ∀ t, 𝔼.E t (n (t + 1)) = n t) (t k : ℕ) : 𝔼.E t (n (t + k)) = n t := by
  induction k with
  | zero => exact hna t
  | succ k ih =>
    rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t k), hn (t + k), ← ih]

/-- Galí (2015), Exercise 6.3(c), p. 197: employment under union wage setting,
`n_{t+1} = n_t + ε_{t+1}` from an initial level `n_0`. -/
def nUnion (ρm : ℝ) (m : ℕ → Ω → ℝ) (n0 : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => n0
  | t + 1 => nUnion ρm m n0 t + (m (t + 1) - ρm • m t)

/-- Galí (2015), Exercise 6.3(c), p. 197: union employment is adapted. -/
theorem nUnion_adapted {ρm : ℝ} {m : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m) {n0 : Ω → ℝ}
    (hn0 : 𝔼.E 0 n0 = n0) : 𝔼.Adapted (nUnion ρm m n0) := by
  intro t
  induction t with
  | zero => exact hn0
  | succ t ih =>
    simp only [nUnion]
    rw [map_add, map_sub, map_smul, hm.1 (t + 1), ← ih, ← hm.1 t, 𝔼.known (Nat.le_succ t),
      𝔼.known (Nat.le_succ t)]

/-- Galí (2015), Exercise 6.3(c), p. 197 (**existence**): for every initial employment level
known at date 0, the wage `w = m − n + log(1 − α)` with `n = nUnion` is predetermined, the
static block holds and `E_{t−1} n_t = n_{t−1}`. -/
theorem union_exists {α ρm : ℝ} {m : ℕ → Ω → ℝ} (hm : 𝔼.IsAR1 ρm m) {n0 : Ω → ℝ}
    (hn0 : 𝔼.E 0 n0 = n0) :
    let n := nUnion ρm m n0
    let w := fun t => m t - n t + fun _ => Real.log (1 - α)
    Static α m n (fun t => (1 - α) • n t) (fun t => w t - (fun _ => Real.log (1 - α)) + α • n t)
        w ∧
      (∀ t, 𝔼.E t (w (t + 1)) = w (t + 1)) ∧ ∀ t, 𝔼.E t (n (t + 1)) = n t := by
  intro n w
  have hna := nUnion_adapted 𝔼 hm hn0
  have hnE : ∀ t, 𝔼.E t (n (t + 1)) = n t := fun t => by
    simp only [n, nUnion]
    rw [map_add, map_sub, map_smul, hna t, hm.2 t, hm.1 t, sub_self, add_zero]
  refine ⟨(static_iff (Ω := Ω)).mpr fun t => ⟨by simp only [w]; abel, rfl, rfl⟩, fun t => ?_,
    hnE⟩
  have hw : w (t + 1) = ρm • m t - n t + fun _ => Real.log (1 - α) := by
    simp only [w, n, nUnion]
    abel
  rw [hw, map_add, map_sub, map_smul, hm.1 t, hna t, 𝔼.const]

end Gali.StickyWagesPrices.Ex6_3
