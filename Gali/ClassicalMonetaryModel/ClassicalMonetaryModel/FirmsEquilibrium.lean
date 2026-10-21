/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.Household

/-!
# Firms, equilibrium and monetary neutrality

Galí (2015), Chapter 2, §2.2–2.3 (pp. 22–24) and §2.4.4 (p. 30).

## Main results

* Eq. (14): `labour_demand_iff` (an interior `N` maximises profits iff `W/P = (1 − α)A N^{−α}`,
  `0 ≤ α < 1`), `labour_demand_unique` (for `0 < α < 1` the explicit `labourDemand` is the
  unique maximiser over `N ≥ 0`), `labour_demand_not_unique_alpha_zero` (at `α = 0` it is not
  unique). Eq. (15): `labour_demand_log_iff` (exact).
* Eqs. (16)–(19), (21): `staticBlock_iff` — for `D = σ(1 − α) + φ + α ≠ 0` the four static
  conditions (9), (15), (16), (17) hold iff `n = ψ_na a + ψ_n`, `y = ψ_ya a + ψ_y`, `c = y`,
  `ω = ψ_ωa a + ψ_ω`; `staticBlock_exists`, `staticBlock_unique`. `bigD_pos` (`σ > 0`) and the
  correction C2-1: `bigD_zero_counterexample`, `staticBlock_degenerate_no_solution`,
  `staticBlock_degenerate_many`. The static block is exactly log-linear:
  `levelsBlock_iff_log`, `levelsBlock_iff_explicit`.
* Comparative statics, p. 24: `psiYa_pos`, `psiWa_pos`, `psiNa_pos_iff`, `psiNa_eq_zero_iff`,
  `psiNa_neg_iff`, `sign_psiNa`; the real rate (correction C2-2): `rateCoeffA_neg_iff`,
  `rateCoeffA_rho_one`, `realRate_no_z_response`.
* Eq. (20): `realRate_of_euler`, `realRate_eq` (under any `ExpectationSystem`),
  `realRate_eq_pf` (exact, nonlinear, perfect foresight), `equilibrium_realRate`.
* Neutrality, p. 24: `Equilibrium`, `EquilibriumUnder` (any monetary policy, as a predicate on
  the nominal paths), `neutrality`, `neutrality_across_policies`, `equilibrium_of_allocation`
  (the real allocation with any nominal paths delivering the real rate is an equilibrium);
  in levels: `levels_neutrality`, `realBondPrice_neutral`.
* §2.4.4: `welfare_policy_invariant`, `welfare_limit_policy_invariant`.
-/

namespace Gali.ClassicalMonetaryModel.FirmsEquilibrium

open Filter Topology

/-! ### The firm's problem, eqs. (12)–(15) -/

/-- Galí (2015), eqs. (12)–(13), p. 22: profits `P A N^{1−α} − W N`. -/
noncomputable def profit (P W A α N : ℝ) : ℝ := P * (A * N ^ (1 - α)) - W * N

/-- Galí (2015), eq. (14), p. 23: the derivative of profits in `N > 0`,
`P (1 − α) A N^{−α} − W`. -/
theorem hasDerivAt_profit (P W A α : ℝ) {N : ℝ} (hN : 0 < N) :
    HasDerivAt (profit P W A α) (P * (A * ((1 - α) * N ^ (-α))) - W) N := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hN.ne')).const_mul A).const_mul P
  have h2 := h.sub ((hasDerivAt_id N).const_mul W)
  rw [show (1 : ℝ) - α - 1 = -α by ring, mul_one] at h2
  exact h2

/-- Galí (2015), eq. (14), p. 23 (**necessity**): an interior local profit maximum `N > 0`
satisfies `W/P = (1 − α) A N^{−α}` (`P > 0`). -/
theorem labour_demand_necessary {P W A α N : ℝ} (hP : 0 < P) (hN : 0 < N)
    (hloc : IsLocalMax (profit P W A α) N) : W / P = (1 - α) * A * N ^ (-α) := by
  have h := hloc.hasDerivAt_eq_zero (hasDerivAt_profit P W A α hN)
  field_simp
  linarith

/-- Galí (2015), eq. (14), p. 23 (**sufficiency**, by concavity for `0 ≤ α < 1`): if
`W/P = (1 − α) A N^{−α}` at `N > 0` (`P > 0`, `A ≥ 0`), then `N` maximises profits over all
`N' ≥ 0`. -/
theorem labour_demand_sufficient {P W A α N : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hP : 0 < P)
    (hA : 0 ≤ A) (hN : 0 < N) (hfoc : W / P = (1 - α) * A * N ^ (-α)) {N' : ℝ} (hN' : 0 ≤ N') :
    profit P W A α N' ≤ profit P W A α N := by
  have htan : N' ^ (1 - α) ≤ N ^ (1 - α) + (1 - α) * N ^ (-α) * (N' - N) := by
    refine Household.le_tangent (f := fun x => x ^ (1 - α))
      (f' := fun x => (1 - α) * x ^ (-α)) hN hN' ?_ (fun z hz => ?_) ?_
    · exact (Real.continuous_rpow_const (by linarith)).continuousOn
    · have := Real.hasDerivAt_rpow_const (x := z) (p := 1 - α) (Or.inl hz.ne')
      rwa [show (1 : ℝ) - α - 1 = -α by ring] at this
    · intro u hu v _ huv
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hu huv (by linarith))
        (by linarith)
  have hW : W = P * ((1 - α) * A * N ^ (-α)) := by
    rw [← hfoc]
    field_simp
  unfold profit
  have := mul_le_mul_of_nonneg_left htan (mul_nonneg hP.le hA)
  rw [hW]
  nlinarith

/-- Galí (2015), eq. (14), p. 23: for `0 ≤ α < 1`, `P > 0`, `A ≥ 0` and `N > 0`, `N` maximises
profits over `N' ≥ 0` iff `W/P = (1 − α) A N^{−α}`. -/
theorem labour_demand_iff {P W A α N : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hP : 0 < P)
    (hA : 0 ≤ A) (hN : 0 < N) :
    (∀ N', 0 ≤ N' → profit P W A α N' ≤ profit P W A α N) ↔
      W / P = (1 - α) * A * N ^ (-α) := by
  constructor
  · intro h
    refine labour_demand_necessary hP hN ?_
    filter_upwards [eventually_gt_nhds hN] with N' hN'
    exact h N' hN'.le
  · intro h N' hN'
    exact labour_demand_sufficient hα0 hα1 hP hA hN h hN'

/-- Galí (2015), eq. (14), p. 23: the labour demand `N* = ((1 − α) A P/W)^{1/α}`. -/
noncomputable def labourDemand (P W A α : ℝ) : ℝ := ((1 - α) * A * P / W) ^ α⁻¹

/-- Galí (2015), eq. (14), p. 23 (**uniqueness** for `0 < α < 1`): with `P, W, A > 0`, the
labour demand `N*` is positive, maximises profits over `N ≥ 0`, and is the only maximiser. -/
theorem labour_demand_unique {P W A α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hP : 0 < P)
    (hW : 0 < W) (hA : 0 < A) :
    0 < labourDemand P W A α ∧
      ∀ N, 0 ≤ N → ((∀ N', 0 ≤ N' → profit P W A α N' ≤ profit P W A α N) ↔
        N = labourDemand P W A α) := by
  set K := (1 - α) * A * P / W with hK
  have hK0 : 0 < K := by
    have : 0 < 1 - α := by linarith
    positivity
  have hNs : 0 < labourDemand P W A α := Real.rpow_pos_of_pos hK0 _
  -- the FOC holds at `N*`
  have hpow : labourDemand P W A α ^ (-α) = K⁻¹ := by
    unfold labourDemand
    rw [← hK, ← Real.rpow_mul hK0.le, show α⁻¹ * -α = -1 by field_simp, Real.rpow_neg_one]
  have hfoc : W / P = (1 - α) * A * labourDemand P W A α ^ (-α) := by
    rw [hpow, hK]
    have : (1 - α) ≠ 0 := by linarith
    field_simp
  have hmax := fun N' (hN' : 0 ≤ N') =>
    labour_demand_sufficient hα0.le hα1 hP hA.le hNs hfoc hN'
  refine ⟨hNs, fun N hN => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases hN.lt_or_eq with hN0 | hN0
    · have hf := (labour_demand_iff hα0.le hα1 hP hA.le hN0).1 h
      -- `N^{−α}` is injective
      have h1 : N ^ (-α) = labourDemand P W A α ^ (-α) := by
        have h2 : (1 - α) * A ≠ 0 := by
          have : 0 < 1 - α := by linarith
          positivity
        have := hf.symm.trans hfoc
        rw [mul_right_inj' h2] at this
        exact this
      have hα : -α ≠ 0 := by linarith
      rw [← Real.rpow_rpow_inv hN hα, h1, Real.rpow_rpow_inv hNs.le hα]
    · -- `N = 0` earns zero profit, `N*` earns a positive profit
      exfalso
      have h0 := h _ hNs.le
      rw [← hN0] at h0
      have hp0 : profit P W A α 0 = 0 := by
        simp [profit, Real.zero_rpow (show (1 : ℝ) - α ≠ 0 by linarith)]
      rw [hp0] at h0
      have hval : profit P W A α (labourDemand P W A α)
          = labourDemand P W A α * (W * α / (1 - α)) := by
        unfold profit
        have hs : labourDemand P W A α ^ (1 - α)
            = labourDemand P W A α * labourDemand P W A α ^ (-α) := by
          rw [sub_eq_add_neg, Real.rpow_add hNs, Real.rpow_one]
        rw [hs, hpow, hK]
        have : (1 - α) ≠ 0 := by linarith
        field_simp
        ring
      have : 0 < labourDemand P W A α * (W * α / (1 - α)) := by
        have : 0 < 1 - α := by linarith
        positivity
      linarith
  · rw [h]
    exact hmax

/-- Galí (2015), p. 23 (**non-uniqueness at `α = 0`**, so the book's uniqueness needs
`α > 0`): with constant returns and `W = P A`, profits are zero for every `N`, so every
`N ≥ 0` (e.g. `1` and `2`) maximises profits. -/
theorem labour_demand_not_unique_alpha_zero {P A : ℝ} :
    ∀ N N', profit P (P * A) A 0 N' ≤ profit P (P * A) A 0 N := by
  intro N N'
  simp [profit]
  ring_nf
  rfl

/-- Galí (2015), eq. (15), p. 23 (**exact**): for positive levels and `α < 1`,
`W/P = (1 − α) A N^{−α}` iff `w − p = a − α n + log(1 − α)` in logs. -/
theorem labour_demand_log_iff {W P A α N : ℝ} (hW : 0 < W) (hP : 0 < P) (hA : 0 < A)
    (hN : 0 < N) (hα : α < 1) :
    W / P = (1 - α) * A * N ^ (-α) ↔
      Real.log W - Real.log P = Real.log A - α * Real.log N + Real.log (1 - α) := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have hr : 0 < (1 - α) * A * N ^ (-α) := by
    have := Real.rpow_pos_of_pos hN (-α)
    positivity
  rw [← Real.log_injOn_pos.eq_iff (div_pos hW hP) hr, Real.log_div hW.ne' hP.ne',
    Real.log_mul (by positivity) (Real.rpow_pos_of_pos hN _).ne',
    Real.log_mul h1.ne' hA.ne', Real.log_rpow hN]
  constructor <;> intro h <;> linarith

/-! ### The equilibrium real block, eqs. (16)–(21) -/

/-- Galí (2015), p. 23: `D = σ(1 − α) + φ + α`, the denominator of every `ψ`. -/
def bigD (σ φ α : ℝ) : ℝ := σ * (1 - α) + φ + α

/-- Galí (2015), p. 23: `ψ_na = (1 − σ)/D`. -/
noncomputable def psiNa (σ φ α : ℝ) : ℝ := (1 - σ) / bigD σ φ α

/-- Galí (2015), p. 23: `ψ_n = log(1 − α)/D`. -/
noncomputable def psiN (σ φ α : ℝ) : ℝ := Real.log (1 - α) / bigD σ φ α

/-- Galí (2015), p. 23: `ψ_ya = (1 + φ)/D`. -/
noncomputable def psiYa (σ φ α : ℝ) : ℝ := (1 + φ) / bigD σ φ α

/-- Galí (2015), p. 23: `ψ_y = (1 − α) ψ_n`. -/
noncomputable def psiY (σ φ α : ℝ) : ℝ := (1 - α) * psiN σ φ α

/-- Galí (2015), p. 24: `ψ_ωa = (σ + φ)/D`. -/
noncomputable def psiWa (σ φ α : ℝ) : ℝ := (σ + φ) / bigD σ φ α

/-- Galí (2015), p. 24: `ψ_ω = (σ(1 − α) + φ) log(1 − α)/D`. -/
noncomputable def psiW (σ φ α : ℝ) : ℝ := (σ * (1 - α) + φ) * Real.log (1 - α) / bigD σ φ α

/-- Galí (2015), p. 23 (correction C2-1): `D > 0` for `σ > 0`, `φ ≥ 0`, `0 ≤ α < 1`. -/
theorem bigD_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    0 < bigD σ φ α := by
  unfold bigD
  have : 0 < σ * (1 - α) := mul_pos hσ (by linarith)
  linarith

/-- Galí (2015), p. 20 (correction C2-1): with the book's `σ ≥ 0`, `D` can vanish:
`σ = φ = α = 0` gives `D = 0`. -/
theorem bigD_zero_counterexample : bigD 0 0 0 = 0 := by norm_num [bigD]

/-- Galí (2015), eqs. (9), (15), (16), (17), pp. 21–23: the static equilibrium conditions at
one date and state, in logs: labour supply `ω = σ c + φ n`, labour demand
`ω = a − α n + log(1 − α)`, goods-market clearing `y = c`, and the production function
`y = a + (1 − α) n`. -/
def StaticBlock (σ φ α a y c n ω : ℝ) : Prop :=
  ω = σ * c + φ * n ∧ ω = a - α * n + Real.log (1 - α) ∧ y = c ∧ y = a + (1 - α) * n

/-- Galí (2015), eqs. (18), (19), (21), pp. 23–24 (**the unique solution**): if `D ≠ 0`, the
static block holds iff `n = ψ_na a + ψ_n`, `y = ψ_ya a + ψ_y`, `c = y` and
`ω = ψ_ωa a + ψ_ω`. -/
theorem staticBlock_iff {σ φ α a y c n ω : ℝ} (hD : bigD σ φ α ≠ 0) :
    StaticBlock σ φ α a y c n ω ↔
      n = psiNa σ φ α * a + psiN σ φ α ∧ y = psiYa σ φ α * a + psiY σ φ α ∧ c = y ∧
        ω = psiWa σ φ α * a + psiW σ φ α := by
  unfold psiY psiNa psiN psiYa psiWa psiW
  unfold bigD at hD ⊢
  have hk : (σ * (1 - α) + φ + α) * (σ * (1 - α) + φ + α)⁻¹ = 1 := mul_inv_cancel₀ hD
  simp only [div_eq_mul_inv]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hc : c = a + (1 - α) * n := h3.symm.trans h4
    have hn : n * (σ * (1 - α) + φ + α) = (1 - σ) * a + Real.log (1 - α) := by
      linear_combination h2 - h1 - σ * hc
    have hn' : n = (1 - σ) * (σ * (1 - α) + φ + α)⁻¹ * a
        + Real.log (1 - α) * (σ * (1 - α) + φ + α)⁻¹ := by
      linear_combination (σ * (1 - α) + φ + α)⁻¹ * hn - n * hk
    refine ⟨hn', ?_, h3.symm, ?_⟩
    · rw [h4, hn']
      linear_combination (-a) * hk
    · rw [h2, hn']
      linear_combination (-(a + Real.log (1 - α))) * hk
  · rintro ⟨hn, hy, hc, hω⟩
    refine ⟨?_, ?_, hc.symm, ?_⟩
    · rw [hω, hc, hy, hn]
      ring
    · rw [hω, hn]
      linear_combination (a + Real.log (1 - α)) * hk
    · rw [hy, hn]
      linear_combination a * hk

/-- Galí (2015), eqs. (18)–(21), pp. 23–24: for `D ≠ 0` the static block has a solution. -/
theorem staticBlock_exists {σ φ α : ℝ} (hD : bigD σ φ α ≠ 0) (a : ℝ) :
    StaticBlock σ φ α a (psiYa σ φ α * a + psiY σ φ α) (psiYa σ φ α * a + psiY σ φ α)
      (psiNa σ φ α * a + psiN σ φ α) (psiWa σ φ α * a + psiW σ φ α) :=
  (staticBlock_iff hD).2 ⟨rfl, rfl, rfl, rfl⟩

/-- Galí (2015), eqs. (18)–(21), pp. 23–24: for `D ≠ 0` the static block has at most one
solution. -/
theorem staticBlock_unique {σ φ α a y c n ω y' c' n' ω' : ℝ} (hD : bigD σ φ α ≠ 0)
    (h : StaticBlock σ φ α a y c n ω) (h' : StaticBlock σ φ α a y' c' n' ω') :
    y = y' ∧ c = c' ∧ n = n' ∧ ω = ω' := by
  obtain ⟨hn, hy, hc, hω⟩ := (staticBlock_iff hD).1 h
  obtain ⟨hn', hy', hc', hω'⟩ := (staticBlock_iff hD).1 h'
  refine ⟨by rw [hy, hy'], by rw [hc, hc', hy, hy'], by rw [hn, hn'], by rw [hω, hω']⟩

/-- Galí (2015), p. 20 (correction C2-1, **failure at `D = 0`**): with `σ = φ = α = 0` the
static block has no solution when `a ≠ 0` ... -/
theorem staticBlock_degenerate_no_solution {a y c n ω : ℝ} (ha : a ≠ 0) :
    ¬ StaticBlock 0 0 0 a y c n ω := by
  rintro ⟨h1, h2, -, -⟩
  simp only [zero_mul, add_zero, sub_zero, Real.log_one] at h1 h2
  exact ha (h2.symm.trans h1)

/-- Galí (2015), p. 20 (correction C2-1, **failure at `D = 0`**): ... and infinitely many
solutions when `a = 0`: every `n` gives one. -/
theorem staticBlock_degenerate_many (n : ℝ) : StaticBlock 0 0 0 0 n n n 0 := by
  refine ⟨by ring, ?_, rfl, by ring⟩
  simp

/-- Galí (2015), eqs. (7), (12), (14), (16), p. 21–23, in levels: labour supply
`W/P = C^σ N^φ`, labour demand `W/P = (1 − α) A N^{−α}`, `Y = C` and `Y = A N^{1−α}`, with the
real wage `w = W/P`. -/
def LevelsBlock (σ φ α A Y C N w : ℝ) : Prop :=
  w = C ^ σ * N ^ φ ∧ w = (1 - α) * A * N ^ (-α) ∧ Y = C ∧ Y = A * N ^ (1 - α)

/-- Galí (2015), pp. 21–23 (**the static block is exactly log-linear**): for positive levels
and `α < 1`, the conditions in levels hold iff their logs satisfy `StaticBlock`; no
approximation is involved. -/
theorem levelsBlock_iff_log {σ φ α A Y C N w : ℝ} (hα : α < 1) (hA : 0 < A) (hY : 0 < Y)
    (hC : 0 < C) (hN : 0 < N) (hw : 0 < w) :
    LevelsBlock σ φ α A Y C N w ↔ StaticBlock σ φ α (Real.log A) (Real.log Y) (Real.log C)
      (Real.log N) (Real.log w) := by
  have h1 : (0 : ℝ) < 1 - α := by linarith
  have hs : 0 < C ^ σ * N ^ φ := mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hN _)
  have hd : 0 < (1 - α) * A * N ^ (-α) := by
    have := Real.rpow_pos_of_pos hN (-α)
    positivity
  have hp : 0 < A * N ^ (1 - α) := mul_pos hA (Real.rpow_pos_of_pos hN _)
  unfold LevelsBlock StaticBlock
  rw [← Real.log_injOn_pos.eq_iff hw hs, ← Real.log_injOn_pos.eq_iff hw hd,
    ← Real.log_injOn_pos.eq_iff hY hC, ← Real.log_injOn_pos.eq_iff hY hp,
    Real.log_mul (Real.rpow_pos_of_pos hC _).ne' (Real.rpow_pos_of_pos hN _).ne',
    Real.log_rpow hC, Real.log_rpow hN,
    Real.log_mul (by positivity) (Real.rpow_pos_of_pos hN _).ne', Real.log_mul h1.ne' hA.ne',
    Real.log_rpow hN, Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN]
  constructor
  · rintro ⟨e1, e2, e3, e4⟩
    exact ⟨e1, by linarith, e3, by linarith⟩
  · rintro ⟨e1, e2, e3, e4⟩
    exact ⟨e1, by linarith, e3, by linarith⟩

/-- Galí (2015), eqs. (18)–(21), pp. 23–24, in levels (**exact**): for `D ≠ 0`, `α < 1` and
`A > 0`, the levels block has the unique positive solution
`N = exp(ψ_na a + ψ_n)`, `Y = C = exp(ψ_ya a + ψ_y)`, `W/P = exp(ψ_ωa a + ψ_ω)`, `a = log A`. -/
theorem levelsBlock_iff_explicit {σ φ α A Y C N w : ℝ} (hD : bigD σ φ α ≠ 0) (hα : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hC : 0 < C) (hN : 0 < N) (hw : 0 < w) :
    LevelsBlock σ φ α A Y C N w ↔
      N = Real.exp (psiNa σ φ α * Real.log A + psiN σ φ α) ∧
      Y = Real.exp (psiYa σ φ α * Real.log A + psiY σ φ α) ∧ C = Y ∧
      w = Real.exp (psiWa σ φ α * Real.log A + psiW σ φ α) := by
  have key : ∀ {u x : ℝ}, 0 < u → (Real.log u = x ↔ u = Real.exp x) := fun hu =>
    ⟨fun h => by rw [← h, Real.exp_log hu], fun h => by rw [h, Real.log_exp]⟩
  rw [levelsBlock_iff_log hα hA hY hC hN hw, staticBlock_iff hD, key hN, key hY, key hw,
    Real.log_injOn_pos.eq_iff hC hY]

/-! ### Comparative statics, p. 24 -/

/-- Galí (2015), p. 24: output always rises with technology, `ψ_ya > 0` (`D > 0`, `φ ≥ 0`). -/
theorem psiYa_pos {σ φ α : ℝ} (hφ : 0 ≤ φ) (hD : 0 < bigD σ φ α) : 0 < psiYa σ φ α :=
  div_pos (by linarith) hD

/-- Galí (2015), p. 24: the real wage rises with technology, `ψ_ωa > 0` (`σ > 0`, `φ ≥ 0`,
`D > 0`). -/
theorem psiWa_pos {σ φ α : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hD : 0 < bigD σ φ α) :
    0 < psiWa σ φ α :=
  div_pos (by linarith) hD

/-- Galí (2015), p. 24: employment rises with technology iff `σ < 1`. -/
theorem psiNa_pos_iff {σ φ α : ℝ} (hD : 0 < bigD σ φ α) : 0 < psiNa σ φ α ↔ σ < 1 := by
  unfold psiNa
  rw [div_pos_iff_of_pos_right hD]
  constructor <;> intro h <;> linarith

/-- Galí (2015), p. 24: employment is unchanged by technology iff `σ = 1` (log utility). -/
theorem psiNa_eq_zero_iff {σ φ α : ℝ} (hD : 0 < bigD σ φ α) : psiNa σ φ α = 0 ↔ σ = 1 := by
  unfold psiNa
  rw [div_eq_zero_iff, or_iff_left hD.ne', sub_eq_zero, eq_comm]

/-- Galí (2015), p. 24: employment falls with technology iff `σ > 1`. -/
theorem psiNa_neg_iff {σ φ α : ℝ} (hD : 0 < bigD σ φ α) : psiNa σ φ α < 0 ↔ 1 < σ := by
  unfold psiNa
  rw [div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h
    right
    exact ⟨by linarith, hD⟩

/-- Galí (2015), p. 24: `sign ψ_na = sign(1 − σ)`. -/
theorem sign_psiNa {σ φ α : ℝ} (hD : 0 < bigD σ φ α) :
    SignType.sign (psiNa σ φ α) = SignType.sign (1 - σ) := by
  rcases lt_trichotomy σ 1 with h | h | h
  · rw [sign_pos ((psiNa_pos_iff hD).2 h), sign_pos (by linarith)]
  · rw [(psiNa_eq_zero_iff hD).2 h, h, sub_self, sign_zero]
  · rw [sign_neg ((psiNa_neg_iff hD).2 h), sign_neg (by linarith)]

/-- Galí (2015), eq. (20), p. 23: the coefficient `−σ(1 − ρ_a)ψ_ya` of `a_t` in the real
interest rate. -/
noncomputable def rateCoeffA (σ φ α ρa : ℝ) : ℝ := -(σ * (1 - ρa) * psiYa σ φ α)

/-- Galí (2015), p. 24 (correction C2-2): with `σ > 0`, `φ ≥ 0`, `D > 0` and `ρ_a ≤ 1`, the real
rate falls after a positive technology shock iff `ρ_a < 1`. -/
theorem rateCoeffA_neg_iff {σ φ α ρa : ℝ} (hσ : 0 < σ) (hφ : 0 ≤ φ) (hD : 0 < bigD σ φ α)
    (hρ : ρa ≤ 1) : rateCoeffA σ φ α ρa < 0 ↔ ρa < 1 := by
  unfold rateCoeffA
  have hy := psiYa_pos hφ hD
  constructor
  · intro h
    by_contra h'
    have : ρa = 1 := le_antisymm hρ (not_lt.1 h')
    rw [this] at h
    simp at h
  · intro h
    have : 0 < σ * (1 - ρa) * psiYa σ φ α := mul_pos (mul_pos hσ (by linarith)) hy
    linarith

/-- Galí (2015), p. 24 (correction C2-2, **counterexample** to the unqualified claim): with a
random-walk technology, `ρ_a = 1`, the real rate does not respond to technology at all. -/
theorem rateCoeffA_rho_one (σ φ α : ℝ) : rateCoeffA σ φ α 1 = 0 := by
  simp [rateCoeffA]

/-- Galí (2015), p. 24 (correction C2-2): with `ρ_z ≤ 1`, the real rate rises with the
preference shifter, coefficient `1 − ρ_z > 0`, iff `ρ_z < 1`. -/
theorem rateCoeffZ_pos_iff {ρz : ℝ} : 0 < 1 - ρz ↔ ρz < 1 := sub_pos

/-! ### The real interest rate, eq. (20) -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Galí (2015), eq. (20), first line, p. 23: with goods-market clearing `c = y` and `σ ≠ 0`,
the log-linear Euler equation (10) gives the real rate
`r_t ≡ i_t − E_t π_{t+1} = ρ + (1 − ρ_z) z_t + σ (E_t y_{t+1} − y_t)`. -/
theorem realRate_of_euler {σ ρ ρz : ℝ} (hσ : σ ≠ 0) {y i infl z : ℕ → Ω → ℝ}
    (heu : Household.EulerLogLinear 𝔼 σ ρ ρz y i infl z) (t : ℕ) :
    i t - 𝔼.E t (infl (t + 1)) = (fun _ => ρ) + (1 - ρz) • z t
      + σ • (𝔼.E t (y (t + 1)) - y t) := by
  have h := heu t
  funext ω
  have e := congrFun h ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  field_simp at e
  linear_combination e

/-- Galí (2015), eq. (20), p. 23: with output `y_t = ψ_ya a_t + ψ_y` and an AR(1) technology
(`E_t a_{t+1} = ρ_a a_t`), the real rate is `r_t = ρ + (1 − ρ_z) z_t − σ(1 − ρ_a) ψ_ya a_t`. -/
theorem realRate_eq {σ φ α ρ ρz ρa : ℝ} (hσ : σ ≠ 0) {y i infl z a : ℕ → Ω → ℝ}
    (heu : Household.EulerLogLinear 𝔼 σ ρ ρz y i infl z)
    (hy : ∀ t, y t = psiYa σ φ α • a t + fun _ => psiY σ φ α) (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    i t - 𝔼.E t (infl (t + 1)) = (fun _ => ρ) + (1 - ρz) • z t
      + rateCoeffA σ φ α ρa • a t := by
  rw [realRate_of_euler 𝔼 hσ heu t, hy (t + 1), hy t, map_add, map_smul, ha.2 t, 𝔼.const]
  funext ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, rateCoeffA]
  ring

/-- Galí (2015), eq. (20), p. 23 (**exact under perfect foresight**): if the nonlinear Euler
equation (8) holds at every date (with `Q = e^{−i}`, `β = e^{−ρ}`, `C = Y = e^y`, `P = e^p`,
`Z = e^z`), output is `y_t = ψ_ya a_t + ψ_y`, and `a_{t+1} = ρ_a a_t`, `z_{t+1} = ρ_z z_t`, then
the real rate `i_t − (p_{t+1} − p_t)` equals `ρ + (1 − ρ_z) z_t − σ(1 − ρ_a)ψ_ya a_t` exactly. -/
theorem realRate_eq_pf {σ φ α ρ ρz ρa : ℝ} {i y p z a : ℕ → Unit → ℝ}
    (heul : ∀ t, Household.EulerEq perfectForesight (Real.exp (-ρ)) σ
      (fun t ω => Real.exp (-i t ω)) (fun t ω => Real.exp (y t ω))
      (fun t ω => Real.exp (p t ω)) (fun t ω => Real.exp (z t ω)) t)
    (hy : ∀ t ω, y t ω = psiYa σ φ α * a t ω + psiY σ φ α)
    (ha : ∀ t ω, a (t + 1) ω = ρa * a t ω) (hz : ∀ t ω, z (t + 1) ω = ρz * z t ω)
    (t : ℕ) (ω : Unit) :
    i t ω - (p (t + 1) ω - p t ω) = ρ + (1 - ρz) * z t ω + rateCoeffA σ φ α ρa * a t ω := by
  have h := (Household.pf_eulerEq_iff σ ρ i y p z t).1 (heul t) ω
  rw [hy (t + 1), hy t, ha, hz] at h
  unfold rateCoeffA
  linear_combination h

/-! ### Equilibrium and neutrality, p. 24 -/

/-- Galí (2015), §2.3, pp. 22–24: an equilibrium of the (log-linear) classical economy given
technology `a` and preferences `z`: the static block (9), (15)–(17) at every date and state,
the Euler equation (10), and the definition of the real rate `r_t = i_t − E_t π_{t+1}`.
Monetary policy enters only through the nominal variables `i`, `infl`. -/
def Equilibrium (σ φ α ρ ρz : ℝ) (a z y c n ω r i infl : ℕ → Ω → ℝ) : Prop :=
  (∀ t s, StaticBlock σ φ α (a t s) (y t s) (c t s) (n t s) (ω t s)) ∧
    Household.EulerLogLinear 𝔼 σ ρ ρz c i infl z ∧
    ∀ t, r t = i t - 𝔼.E t (infl (t + 1))

/-- Galí (2015), §2.3–2.4, pp. 22–30: an equilibrium under a monetary policy. A policy is any
condition on the nominal paths (interest rate `i`, inflation `infl`, money `m`, prices `p`):
an interest-rate rule, a money-supply rule, or an exogenous path. Money demand (11) and
`π_{t+1} = p_{t+1} − p_t` are imposed as well. -/
def EquilibriumUnder (σ φ α ρ ρz η : ℝ)
    (policy : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    (a z y c n ω r i infl m p : ℕ → Ω → ℝ) : Prop :=
  Equilibrium 𝔼 σ φ α ρ ρz a z y c n ω r i infl ∧ Household.MoneyDemand η m p c i ∧
    (∀ t, infl (t + 1) = p (t + 1) - p t) ∧ policy i infl m p

/-- Galí (2015), eqs. (18)–(21), pp. 23–24: in every equilibrium (`D ≠ 0`) the real allocation
is `n = ψ_na a + ψ_n`, `y = c = ψ_ya a + ψ_y`, `ω = ψ_ωa a + ψ_ω`, whatever the nominal
variables. -/
theorem equilibrium_allocation {σ φ α ρ ρz : ℝ} (hD : bigD σ φ α ≠ 0)
    {a z y c n ω r i infl : ℕ → Ω → ℝ} (h : Equilibrium 𝔼 σ φ α ρ ρz a z y c n ω r i infl)
    (t : ℕ) (s : Ω) :
    n t s = psiNa σ φ α * a t s + psiN σ φ α ∧ y t s = psiYa σ φ α * a t s + psiY σ φ α ∧
      c t s = y t s ∧ ω t s = psiWa σ φ α * a t s + psiW σ φ α :=
  (staticBlock_iff hD).1 (h.1 t s)

/-- Galí (2015), p. 24 (**neutrality**): for `σ ≠ 0` and `D ≠ 0`, any two equilibria with the
same technology and preference shocks have identical output, consumption, employment, real
wage and real interest rate, whatever their nominal interest rates and inflation. -/
theorem neutrality {σ φ α ρ ρz : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    {a z y c n ω r i infl y' c' n' ω' r' i' infl' : ℕ → Ω → ℝ}
    (h : Equilibrium 𝔼 σ φ α ρ ρz a z y c n ω r i infl)
    (h' : Equilibrium 𝔼 σ φ α ρ ρz a z y' c' n' ω' r' i' infl') :
    y = y' ∧ c = c' ∧ n = n' ∧ ω = ω' ∧ r = r' := by
  have hst : ∀ t s, y t s = y' t s ∧ c t s = c' t s ∧ n t s = n' t s ∧ ω t s = ω' t s :=
    fun t s => staticBlock_unique hD (h.1 t s) (h'.1 t s)
  have hy : y = y' := funext fun t => funext fun s => (hst t s).1
  have hc : c = c' := funext fun t => funext fun s => (hst t s).2.1
  refine ⟨hy, hc, funext fun t => funext fun s => (hst t s).2.2.1,
    funext fun t => funext fun s => (hst t s).2.2.2, ?_⟩
  funext t
  rw [h.2.2 t, h'.2.2 t, realRate_of_euler 𝔼 hσ h.2.1 t, realRate_of_euler 𝔼 hσ h'.2.1 t, hc]

/-- Galí (2015), p. 24 (**neutrality across policies**): the real allocation and the real rate
are the same in an equilibrium under any monetary policy `policy₁` and in one under any other
policy `policy₂`. -/
theorem neutrality_across_policies {σ φ α ρ ρz η : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    (policy₁ policy₂ : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    {a z y c n ω r i infl m p y' c' n' ω' r' i' infl' m' p' : ℕ → Ω → ℝ}
    (h : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₁ a z y c n ω r i infl m p)
    (h' : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₂ a z y' c' n' ω' r' i' infl' m' p') :
    y = y' ∧ c = c' ∧ n = n' ∧ ω = ω' ∧ r = r' :=
  neutrality 𝔼 hσ hD h.1 h'.1

/-- Galí (2015), eq. (20), p. 23: in every equilibrium with an AR(1) technology the real rate
is `r_t = ρ + (1 − ρ_z) z_t − σ(1 − ρ_a)ψ_ya a_t`, independent of monetary policy. -/
theorem equilibrium_realRate {σ φ α ρ ρz ρa : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    {a z y c n ω r i infl : ℕ → Ω → ℝ} (h : Equilibrium 𝔼 σ φ α ρ ρz a z y c n ω r i infl)
    (ha : 𝔼.IsAR1 ρa a) (t : ℕ) :
    r t = (fun _ => ρ) + (1 - ρz) • z t + rateCoeffA σ φ α ρa • a t := by
  have hcy : c = y := funext fun t => funext fun s => (equilibrium_allocation 𝔼 hD h t s).2.2.1
  have hy : ∀ t, y t = psiYa σ φ α • a t + fun _ => psiY σ φ α := fun t => by
    funext s
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (equilibrium_allocation 𝔼 hD h t s).2.1
  have heu := h.2.1
  rw [hcy] at heu
  rw [h.2.2 t]
  exact realRate_eq 𝔼 hσ heu hy ha t

/-- Galí (2015), §2.3, in levels and under uncertainty (**exact neutrality of the static
block**): two positive allocations satisfying the levels block (7), (12), (14), (16) at a date
and state with the same technology `A` coincide (`D ≠ 0`, `α < 1`). -/
theorem levels_neutrality {σ φ α A Y C N w Y' C' N' w' : ℝ} (hD : bigD σ φ α ≠ 0) (hα : α < 1)
    (hA : 0 < A) (hY : 0 < Y) (hC : 0 < C) (hN : 0 < N) (hw : 0 < w) (hY' : 0 < Y')
    (hC' : 0 < C') (hN' : 0 < N') (hw' : 0 < w') (h : LevelsBlock σ φ α A Y C N w)
    (h' : LevelsBlock σ φ α A Y' C' N' w') : Y = Y' ∧ C = C' ∧ N = N' ∧ w = w' := by
  obtain ⟨e1, e2, e3, e4⟩ := (levelsBlock_iff_explicit hD hα hA hY hC hN hw).1 h
  obtain ⟨f1, f2, f3, f4⟩ := (levelsBlock_iff_explicit hD hα hA hY' hC' hN' hw').1 h'
  exact ⟨by rw [e2, f2], by rw [e3, f3, e2, f2], by rw [e1, f1], by rw [e4, f4]⟩

/-- Galí (2015), eq. (8), p. 21: the price of a one-period real (consumption-indexed) bond at
node `ω`, `β E_t[(C_{t+1}/C_t)^{−σ} Z_{t+1}/Z_t]`; its log is minus the real interest rate of
the nonlinear model. -/
noncomputable def realBondPrice (β σ : ℝ) (C Z : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  β * 𝔼.E t (fun ω' => (C (t + 1) ω' / C t ω) ^ (-σ) * (Z (t + 1) ω' / Z t ω)) ω

/-- Galí (2015), p. 24 (**exact neutrality of the real rate**, nonlinear model under
uncertainty): if two equilibria satisfy the levels block at every date and state with the same
technology, their real bond prices coincide at every node, whatever the nominal bond prices
and price levels. -/
theorem realBondPrice_neutral {σ φ α β : ℝ} (hD : bigD σ φ α ≠ 0) (hα : α < 1)
    {A Z Y C N w Y' C' N' w' : ℕ → Ω → ℝ} (hA : ∀ t s, 0 < A t s)
    (hpos : ∀ t s, 0 < Y t s ∧ 0 < C t s ∧ 0 < N t s ∧ 0 < w t s)
    (hpos' : ∀ t s, 0 < Y' t s ∧ 0 < C' t s ∧ 0 < N' t s ∧ 0 < w' t s)
    (h : ∀ t s, LevelsBlock σ φ α (A t s) (Y t s) (C t s) (N t s) (w t s))
    (h' : ∀ t s, LevelsBlock σ φ α (A t s) (Y' t s) (C' t s) (N' t s) (w' t s)) (t : ℕ) (s : Ω) :
    realBondPrice 𝔼 β σ C Z t s = realBondPrice 𝔼 β σ C' Z t s := by
  have hC : C = C' := funext fun t => funext fun s =>
    (levels_neutrality hD hα (hA t s) (hpos t s).1 (hpos t s).2.1 (hpos t s).2.2.1
      (hpos t s).2.2.2 (hpos' t s).1 (hpos' t s).2.1 (hpos' t s).2.2.1 (hpos' t s).2.2.2
      (h t s) (h' t s)).2.1
  rw [hC]

/-! ### Welfare, §2.4.4 -/

/-- Galí (2015), eq. (1), p. 18, and §2.4.4, p. 30: expected discounted utility up to date `T`
as of date 0, `E_0 ∑_{t<T} β^t U(e^{c_t}, e^{n_t}; e^{z_t})`, of a (log) allocation. -/
noncomputable def welfare (β σ φ : ℝ) (c n z : ℕ → Ω → ℝ) (T : ℕ) : Ω → ℝ :=
  𝔼.E 0 (fun s => ∑ t ∈ Finset.range T, β ^ t *
    Household.periodUtility σ φ (Real.exp (c t s)) (Real.exp (n t s)) (Real.exp (z t s)))

/-- Galí (2015), §2.4.4, p. 30 (**all policies are welfare-equivalent**): for `σ ≠ 0`, `D ≠ 0`,
two equilibria under any two monetary policies give the same expected discounted utility at
every horizon `T`. -/
theorem welfare_policy_invariant {σ φ α ρ ρz η β : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    (policy₁ policy₂ : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    {a z y c n ω r i infl m p y' c' n' ω' r' i' infl' m' p' : ℕ → Ω → ℝ}
    (h : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₁ a z y c n ω r i infl m p)
    (h' : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₂ a z y' c' n' ω' r' i' infl' m' p') (T : ℕ) :
    welfare 𝔼 β σ φ c n z T = welfare 𝔼 β σ φ c' n' z T := by
  obtain ⟨-, hc, hn, -, -⟩ := neutrality_across_policies 𝔼 hσ hD policy₁ policy₂ h h'
  rw [hc, hn]

/-- Galí (2015), §2.4.4, p. 30: no policy rule is better than any other. If expected
discounted utility converges (to `W` and `W'`) under two policies, then `W = W'`. -/
theorem welfare_limit_policy_invariant {σ φ α ρ ρz η β : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    (policy₁ policy₂ : (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → (ℕ → Ω → ℝ) → Prop)
    {a z y c n ω r i infl m p y' c' n' ω' r' i' infl' m' p' : ℕ → Ω → ℝ}
    (h : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₁ a z y c n ω r i infl m p)
    (h' : EquilibriumUnder 𝔼 σ φ α ρ ρz η policy₂ a z y' c' n' ω' r' i' infl' m' p') {s : Ω}
    {W W' : ℝ} (hW : Tendsto (fun T => welfare 𝔼 β σ φ c n z T s) atTop (𝓝 W))
    (hW' : Tendsto (fun T => welfare 𝔼 β σ φ c' n' z T s) atTop (𝓝 W')) : W = W' := by
  have he : (fun T => welfare 𝔼 β σ φ c n z T s) = fun T => welfare 𝔼 β σ φ c' n' z T s :=
    funext fun T => by rw [welfare_policy_invariant 𝔼 hσ hD policy₁ policy₂ h h' T]
  rw [he] at hW
  exact tendsto_nhds_unique hW hW'

/-- Galí (2015), p. 24 (correction C2-2, **counterexample**): with a random-walk preference
shifter, `ρ_z = 1`, the equilibrium real rate does not respond to `z_t` at all:
`r_t = ρ − σ(1 − ρ_a)ψ_ya a_t`. -/
theorem realRate_no_z_response {σ φ α ρ ρa : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    {a z y c n ω r i infl : ℕ → Ω → ℝ} (h : Equilibrium 𝔼 σ φ α ρ 1 a z y c n ω r i infl)
    (ha : 𝔼.IsAR1 ρa a) (t : ℕ) : r t = (fun _ => ρ) + rateCoeffA σ φ α ρa • a t := by
  rw [equilibrium_realRate 𝔼 hσ hD h ha t, sub_self, zero_smul, add_zero]

/-- Galí (2015), pp. 23–24: conversely, the allocation of (18)–(21) together with any nominal
paths `i`, `π` that deliver the real rate `ρ + (1 − ρ_z) z_t + σ(E_t y_{t+1} − y_t)` is an
equilibrium (`σ ≠ 0`, `D ≠ 0`): monetary policy can choose nominal paths freely subject to
this one restriction. -/
theorem equilibrium_of_allocation {σ φ α ρ ρz : ℝ} (hσ : σ ≠ 0) (hD : bigD σ φ α ≠ 0)
    {a z y n ω r i infl : ℕ → Ω → ℝ}
    (hn : ∀ t s, n t s = psiNa σ φ α * a t s + psiN σ φ α)
    (hy : ∀ t s, y t s = psiYa σ φ α * a t s + psiY σ φ α)
    (hω : ∀ t s, ω t s = psiWa σ φ α * a t s + psiW σ φ α)
    (hr : ∀ t, r t = i t - 𝔼.E t (infl (t + 1)))
    (hi : ∀ t, i t - 𝔼.E t (infl (t + 1)) = (fun _ => ρ) + (1 - ρz) • z t
      + σ • (𝔼.E t (y (t + 1)) - y t)) :
    Equilibrium 𝔼 σ φ α ρ ρz a z y y n ω r i infl := by
  refine ⟨fun t s => (staticBlock_iff hD).2 ⟨hn t s, hy t s, rfl, hω t s⟩, fun t => ?_, hr⟩
  funext s
  have e := congrFun (hi t) s
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  field_simp
  linear_combination e

end Gali.ClassicalMonetaryModel.FirmsEquilibrium
