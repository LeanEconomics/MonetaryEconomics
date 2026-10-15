/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Calvo

/-!
# The New Keynesian Phillips curve

Woodford (2003), *Interest and Prices*, Chapter 3, §2.2 (pp. 187–188), Proposition 3.5, and
Appendix B.4 (pp. 661–662, its proof).

The model is the log-linear Calvo model of the `Calvo` module: the index recursion (2.5) and the
pricing condition (2.6) (each proved there to be the exact derivative of the nonlinear
condition at the zero-inflation steady state), for an arbitrary `ExpectationSystem`, with the
price index indexed so that `P (t + 1) = log P_t` (known at `t`). Inflation is
`π_t = log P_t − log P_{t−1}` and `x_t = Ŷ_t − Ŷⁿ_t` is the output gap.

## Main results

* `interchange_sums` (B.4, the first display): for bounded `y` and `0 ≤ a < 1`,
  `(1 − a) ∑_j aʲ ∑_{i<j} y_i = ∑_i a^{i+1} y_i`, proved as an interchange of a double series that
  converges absolutely (`summable_double`).
* `eq26_iff_resetGap`: in the class of bounded inflation and output gaps, (2.6) is equivalent to
  `p̂*_t = ∑_j (αβ)ʲ E_t[αβ π_{t+j+1} + (1 − αβ) ζ x_{t+j}]`, which by the tower property is the
  forward solution of (B.17) (`resetGap_rec`).
* `inflation_eq_resetGap`: (2.5) gives `π_t = (1 − α)/α · p̂*_t`.
* `prop35`: **Proposition 3.5** — given (2.5), (2.6) holds iff the New Keynesian Phillips curve
  `π_t = κ x_t + β E_t π_{t+1}` with `κ = (1 − α)(1 − αβ)ζ/α` holds (both directions).
* `nkpc_iff_eq214`: (2.14) `π_t = ξ ŝ_t + β E_t π_{t+1}`; `kappa_baseline`: `κ = (ω + σ⁻¹)ξ`.
* `forecastable_gap_iff`: `E_{t−j} x_t = 0` iff `E_{t−j} π_t = β E_{t−j} π_{t+1}`.
* comparative statics of `κ`: increasing in `ζ` (`kappa_strictMono_zeta`), decreasing in `α`
  (`kappa_strictAntiOn_alpha`), decreasing in `θ` (`kappaBase_strictAntiOn_theta`), and in `ω`
  increasing iff `θσ⁻¹ < 1`, decreasing iff `θσ⁻¹ > 1`, constant iff `θσ⁻¹ = 1`
  (`kappaBase_omega_diff`, `kappaBase_strictMonoOn_omega`, `kappaBase_strictAntiOn_omega`,
  `kappaBase_const_omega`), with derivatives `hasDerivAt_kappaBase_omega`,
  `hasDerivAt_kappaBase_theta`; limits `tendsto_kappa_alpha_one`, `tendsto_kappa_alpha_zero`.
-/

namespace Woodford.NominalRigidities.NKPC

open Filter Topology Woodford.NominalRigidities.Calvo
open Woodford.NominalRigidities.QuadraticRoots (kappa kappa_pos)

/-! ### The interchange of sums in B.4 -/

/-- Woodford (2003), App. B.4, p. 662 (**absolute convergence of the double series**): for
`|y_i| ≤ M` and `0 ≤ a < 1`, the double series `∑_{(j,i), i<j} aʲ y_i` converges absolutely. -/
theorem summable_double {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ M) :
    Summable (Function.uncurry fun j i : ℕ => if i < j then a ^ j * y i else 0) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hy 0)
  set g : ℕ × ℕ → ℝ := fun p => if p.2 < p.1 then M * a ^ p.1 else 0 with hg
  have hg0 : 0 ≤ g := fun p => by
    simp only [hg, Pi.zero_apply]; split_ifs <;> positivity
  have hrow : ∀ j, ∑' i, g (j, i) = j * (M * a ^ j) := by
    intro j
    rw [tsum_eq_sum (s := Finset.range j) (fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [hg, not_lt.mpr hi])]
    rw [Finset.sum_congr rfl (fun i hi => by
      simp only [Finset.mem_range] at hi; simp [hg, hi] : ∀ i ∈ Finset.range j,
        g (j, i) = M * a ^ j)]
    simp
  have hgs : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun j => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := Finset.range j) (fun i hi => by
        simp only [Finset.mem_range, not_lt] at hi
        simp [hg, not_lt.mpr hi])
    · simp_rw [hrow]
      exact ((summable_nat_mul_geom ha0 ha1).mul_left M).congr fun j => by ring
  refine Summable.of_norm_bounded hgs (fun p => ?_)
  obtain ⟨j, i⟩ := p
  simp only [Function.uncurry_apply_pair, hg, Real.norm_eq_abs]
  split_ifs
  · rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 j), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hy i) (pow_nonneg ha0 j)
  · simp

/-- Woodford (2003), App. B.4, p. 662 (**the interchange of sums**): for `|y_i| ≤ M` and
`0 ≤ a < 1`, `(1 − a) ∑_{j ≥ 0} aʲ ∑_{i<j} y_i = ∑_{i ≥ 0} a^{i+1} y_i` (with
`y_i = E_t π_{t+1+i}` this is
`(1 − αβ) ∑_T (αβ)^{T−t} ∑_{s=t+1}^T π_s = ∑_T (αβ)^{T−t} αβ π_{T+1}`), and the left-hand series
converges. -/
theorem interchange_sums {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ M) :
    Summable (fun j => a ^ j * ∑ i ∈ Finset.range j, y i) ∧
      (1 - a) * ∑' j, a ^ j * ∑ i ∈ Finset.range j, y i = ∑' i, a ^ (i + 1) * y i := by
  set f : ℕ → ℕ → ℝ := fun j i => if i < j then a ^ j * y i else 0 with hf
  have hsum := summable_double ha0 ha1 hy
  have hrowval : ∀ j, ∑' i, f j i = a ^ j * ∑ i ∈ Finset.range j, y i := by
    intro j
    rw [tsum_eq_sum (s := Finset.range j) (fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [hf, not_lt.mpr hi]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [hf, hi]
  have hrow : ∀ j, Summable (f j) := fun j =>
    summable_of_ne_finset_zero (s := Finset.range j) (fun i hi => by
      simp only [Finset.mem_range, not_lt] at hi
      simp [hf, not_lt.mpr hi])
  have h1a : 1 - a ≠ 0 := by linarith
  have hcol : ∀ i, HasSum (fun j => f j i) (a ^ (i + 1) * (1 - a)⁻¹ * y i) := by
    intro i
    have hz : ∑ j ∈ Finset.range (i + 1), f j i = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [Finset.mem_range] at hj
      simp [hf, show ¬ i < j by omega]
    have h' : HasSum (fun k => f (k + (i + 1)) i) (a ^ (i + 1) * (1 - a)⁻¹ * y i) := by
      have := (hasSum_geometric_of_lt_one ha0 ha1).mul_left (a ^ (i + 1) * y i)
      convert this using 1
      · funext k
        simp only [hf, show i < k + (i + 1) by omega, ↓reduceIte]
        rw [show k + (i + 1) = (i + 1) + k by omega, pow_add]
        ring
      · ring
    have := (hasSum_nat_add_iff (f := fun j => f j i) (i + 1)).mp h'
    rwa [hz, add_zero] at this
  have hcomm := hsum.tsum_comm' hrow (fun i => (hcol i).summable)
  have hS : Summable (fun j => a ^ j * ∑ i ∈ Finset.range j, y i) := by
    refine Summable.of_norm_bounded ((summable_nat_mul_geom ha0 ha1).mul_left M) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 j)]
    have : |∑ i ∈ Finset.range j, y i| ≤ j * M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range j, |y i| ≤ ∑ _i ∈ Finset.range j, M :=
            Finset.sum_le_sum fun i _ => hy i
        _ = j * M := by simp
    calc a ^ j * |∑ i ∈ Finset.range j, y i| ≤ a ^ j * (j * M) :=
          mul_le_mul_of_nonneg_left this (pow_nonneg ha0 j)
      _ = M * (j * a ^ j) := by ring
  refine ⟨hS, ?_⟩
  simp_rw [← hrowval]
  rw [← hcomm, tsum_congr fun i => (hcol i).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  field_simp

/-! ### Proposition 3.5 -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), §2.2, p. 187: inflation `π_t = log P_t − log P_{t−1}`, in the indexing
`P (t + 1) = log P_t`. -/
def infl (P : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => P (t + 1) ω - P t ω

/-- Woodford (2003), eq. (2.12), p. 187 (**the New Keynesian Phillips curve**):
`π_t = κ x_t + β E_t π_{t+1}` at every date. -/
def NKPCurve (β κ : ℝ) (π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t = κ • x t + β • 𝔼.E t (π (t + 1))

/-- Woodford (2003), App. B.4, p. 662: the expected change in the price index is the sum of
expected inflation, `E_t log P_{t+j} − log P_t = ∑_{i<j} E_t π_{t+1+i}`. -/
theorem E_price_change {P : ℕ → Ω → ℝ} (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (t j : ℕ)
    (ω : Ω) :
    𝔼.E t (P (t + j + 1)) ω - P (t + 1) ω
      = ∑ i ∈ Finset.range j, 𝔼.E t (infl P (t + 1 + i)) ω := by
  induction j with
  | zero => simp [hpre t]
  | succ j ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : infl P (t + 1 + j) = P (t + (j + 1) + 1) - P (t + j + 1) := by
      funext ω'
      simp only [infl, Pi.sub_apply]
      rw [show t + 1 + j + 1 = t + (j + 1) + 1 by omega, show t + 1 + j = t + j + 1 by omega]
    rw [e, map_sub, Pi.sub_apply]
    ring

/-- Woodford (2003), App. B.4, p. 662 (**(2.6) in terms of inflation**): in the class of bounded
inflation and output gaps, (2.6) holds iff the log relative reset price
`p̂*_t = log p*_t − log P_t` equals `∑_j (αβ)ʲ E_t[αβ π_{t+j+1} + (1 − αβ) ζ x_{t+j}]`. -/
theorem eq26_iff_resetGap {α β ζ : ℝ} (hab0 : 0 ≤ α * β) (hab1 : α * β < 1)
    {P pstar x : ℕ → Ω → ℝ} (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1))
    (hps : ∀ t, 𝔼.E t (pstar t) = pstar t) {Mπ Mx : ℝ}
    (hπ : ∀ t ω, |infl P t ω| ≤ Mπ) (hx : ∀ t ω, |x t ω| ≤ Mx) :
    Eq26 𝔼 α β P pstar (fun T ω => ζ * x T ω) ↔
      ∀ t ω, pstar t ω - P (t + 1) ω = ∑' j, (α * β) ^ j *
        (α * β * 𝔼.E t (infl P (t + j + 1)) ω + (1 - α * β) * (ζ * 𝔼.E t (x (t + j)) ω)) := by
  set a := α * β
  have hg := summable_geometric_of_lt_one hab0 hab1
  have h1a : 1 - a ≠ 0 := by linarith
  -- the summand of (2.6)
  have hsummand : ∀ t j ω, 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - ζ * x (t + j) ω') ω
      = (pstar t ω - P (t + 1) ω) - ∑ i ∈ Finset.range j, 𝔼.E t (infl P (t + 1 + i)) ω
        - ζ * 𝔼.E t (x (t + j)) ω := by
    intro t j ω
    have hf : (fun ω' => pstar t ω' - P (t + j + 1) ω' - ζ * x (t + j) ω')
        = pstar t - P (t + j + 1) - ζ • x (t + j) := by
      funext ω'; simp [smul_eq_mul]
    rw [hf, map_sub, map_sub, map_smul, hps t]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have := E_price_change 𝔼 hpre t j ω
    linarith
  have hEπ : ∀ t i ω, |𝔼.E t (infl P (t + 1 + i)) ω| ≤ Mπ := fun t i ω =>
    𝔼.abs_E_le (hπ (t + 1 + i)) t ω
  have hEx : ∀ t j ω, |ζ * 𝔼.E t (x (t + j)) ω| ≤ |ζ| * Mx := fun t j ω => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hx (t + j)) t ω) (abs_nonneg ζ)
  have key : ∀ t ω,
      Summable (fun j => a ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω'
        - ζ * x (t + j) ω') ω) ∧
      ∑' j, a ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω' - ζ * x (t + j) ω') ω
        = (1 - a)⁻¹ * ((pstar t ω - P (t + 1) ω) - ∑' j, a ^ j *
          (a * 𝔼.E t (infl P (t + j + 1)) ω + (1 - a) * (ζ * 𝔼.E t (x (t + j)) ω))) := by
    intro t ω
    obtain ⟨hS, hI⟩ := interchange_sums hab0 hab1 (hEπ t · ω)
    have hX : Summable (fun j => a ^ j * (ζ * 𝔼.E t (x (t + j)) ω)) :=
      Summable.of_norm_bounded (hg.mul_right (|ζ| * Mx)) (fun j => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hab0 j)]
        exact mul_le_mul_of_nonneg_left (hEx t j ω) (pow_nonneg hab0 j))
    have hY : Summable (fun i => a ^ (i + 1) * 𝔼.E t (infl P (t + 1 + i)) ω) :=
      Summable.of_norm_bounded ((hg.mul_left a).mul_right Mπ) (fun i => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hab0 _)]
        calc a ^ (i + 1) * |𝔼.E t (infl P (t + 1 + i)) ω| ≤ a ^ (i + 1) * Mπ :=
              mul_le_mul_of_nonneg_left (hEπ t i ω) (pow_nonneg hab0 _)
          _ = a * a ^ i * Mπ := by ring)
    have hsplit : ∀ j, a ^ j * 𝔼.E t (fun ω' => pstar t ω' - P (t + j + 1) ω'
        - ζ * x (t + j) ω') ω = a ^ j * (pstar t ω - P (t + 1) ω)
          - a ^ j * ∑ i ∈ Finset.range j, 𝔼.E t (infl P (t + 1 + i)) ω
          - a ^ j * (ζ * 𝔼.E t (x (t + j)) ω) := by
      intro j; rw [hsummand]; ring
    have hS26 := ((hg.mul_right (pstar t ω - P (t + 1) ω)).sub hS).sub hX
    refine ⟨hS26.congr fun j => (hsplit j).symm, ?_⟩
    simp_rw [hsplit]
    rw [Summable.tsum_sub ((hg.mul_right _).sub hS) hX,
      Summable.tsum_sub (hg.mul_right _) hS, tsum_mul_right, tsum_geometric_of_lt_one hab0 hab1]
    have hI' : ∑' j, a ^ j * ∑ i ∈ Finset.range j, 𝔼.E t (infl P (t + 1 + i)) ω
        = (1 - a)⁻¹ * ∑' i, a ^ (i + 1) * 𝔼.E t (infl P (t + 1 + i)) ω := by
      rw [← hI]; field_simp
    have hR : ∑' j, a ^ j * (a * 𝔼.E t (infl P (t + j + 1)) ω
        + (1 - a) * (ζ * 𝔼.E t (x (t + j)) ω))
        = ∑' i, a ^ (i + 1) * 𝔼.E t (infl P (t + 1 + i)) ω
          + (1 - a) * ∑' j, a ^ j * (ζ * 𝔼.E t (x (t + j)) ω) := by
      rw [← tsum_mul_left, ← hY.tsum_add (hX.mul_left (1 - a))]
      refine tsum_congr fun j => ?_
      rw [show t + j + 1 = t + 1 + j by omega, pow_succ]
      ring
    rw [hI', hR]
    field_simp
    ring_nf
  constructor
  · intro h t ω
    obtain ⟨-, h0⟩ := h t ω
    rw [(key t ω).2] at h0
    have := (mul_eq_zero.mp h0).resolve_left (inv_ne_zero h1a)
    linarith
  · intro h t ω
    refine ⟨(key t ω).1, ?_⟩
    rw [(key t ω).2, h t ω, sub_self, mul_zero]

/-- Woodford (2003), App. B.4, p. 662: the forcing term of (B.17),
`u_t = αβ E_t π_{t+1} + (1 − αβ) ζ x_t`. -/
def resetForcing (a ζ : ℝ) (P x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => a • 𝔼.E t (infl P (t + 1)) + ((1 - a) * ζ) • x t

/-- Woodford (2003), App. B.4, p. 662 (**the recursive form via the tower property**): the forward
sum of (B.4) is `forwardSeries` of the forcing `u`, because `E_t u_{t+j} = αβ E_t π_{t+j+1} +
(1 − αβ)ζ E_t x_{t+j}` by the law of iterated expectations; hence it solves
`p̂*_t = αβ E_t p̂*_{t+1} + u_t` ((B.17)). -/
theorem resetGap_rec {a ζ : ℝ} (P x : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    ∑' j, a ^ j * (a * 𝔼.E t (infl P (t + j + 1)) ω + (1 - a) * (ζ * 𝔼.E t (x (t + j)) ω))
      = 𝔼.forwardSeries a (resetForcing 𝔼 a ζ P x) t ω := by
  refine tsum_congr fun j => ?_
  simp only [resetForcing, map_add, map_smul, 𝔼.tower (Nat.le_add_right t j), Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Woodford (2003), App. B.4, p. 662: `u` is adapted. -/
theorem resetForcing_adapted (a ζ : ℝ) {P x : ℕ → Ω → ℝ} (hxa : 𝔼.Adapted x) :
    𝔼.Adapted (resetForcing 𝔼 a ζ P x) := by
  intro t
  simp only [resetForcing, map_add, map_smul, 𝔼.E_E_self, hxa t]

/-- Woodford (2003), App. B.4, p. 662: `u` is bounded when inflation and the gap are. -/
theorem resetForcing_bounded {a ζ Mπ Mx : ℝ} {P x : ℕ → Ω → ℝ}
    (hπ : ∀ t ω, |infl P t ω| ≤ Mπ) (hx : ∀ t ω, |x t ω| ≤ Mx) :
    ∀ t ω, |resetForcing 𝔼 a ζ P x t ω| ≤ |a| * Mπ + |(1 - a) * ζ| * Mx := by
  intro t ω
  simp only [resetForcing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (hπ (t + 1)) t ω) (abs_nonneg a)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hx t ω) (abs_nonneg _)

omit 𝔼 in
/-- Woodford (2003), App. B.4, p. 662: (2.5) makes inflation proportional to the log relative
reset price, `π_t = (1 − α)/α · p̂*_t`, i.e. `p̂*_t = α/(1 − α) · π_t`. -/
theorem inflation_eq_resetGap {α : ℝ} (hα1 : α < 1) {P pstar : ℕ → Ω → ℝ}
    (h25 : Eq25 α P pstar) (t : ℕ) (ω : Ω) :
    pstar t ω - P (t + 1) ω = α / (1 - α) * infl P t ω := by
  have h1a : 1 - α ≠ 0 := by linarith
  rw [congrFun (pstar_of_eq25 hα1 h25 t) ω]
  simp only [infl]
  field_simp
  ring

omit 𝔼 in
/-- Woodford (2003), App. B.4, p. 662 (the final substitution): with `q = α/(1 − α) π`,
`q_t = αβ E q_{t+1} + αβ Eπ_{t+1} + (1 − αβ)ζ x_t` iff `π_t = κ x_t + β Eπ_{t+1}`. -/
theorem B17_iff_nkpc {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (π0 Eπ1 x : ℝ) :
    α / (1 - α) * π0 = α * β * (α / (1 - α) * Eπ1) + (α * β * Eπ1 + (1 - α * β) * ζ * x) ↔
      π0 = kappa α β ζ * x + β * Eπ1 := by
  have h1a : 1 - α ≠ 0 := by linarith
  have key : α / (1 - α) * π0 - (α * β * (α / (1 - α) * Eπ1) + (α * β * Eπ1
      + (1 - α * β) * ζ * x)) = α / (1 - α) * (π0 - (kappa α β ζ * x + β * Eπ1)) := by
    unfold kappa
    field_simp
    ring
  have hc : α / (1 - α) ≠ 0 := div_ne_zero hα0.ne' h1a
  constructor
  · intro h
    have h0 : α / (1 - α) * (π0 - (kappa α β ζ * x + β * Eπ1)) = 0 := by rw [← key, h, sub_self]
    have := (mul_eq_zero.mp h0).resolve_left hc
    linarith
  · intro h
    have : α / (1 - α) * (π0 - (kappa α β ζ * x + β * Eπ1)) = 0 := by rw [h, sub_self, mul_zero]
    rw [← key] at this
    linarith

/-- Woodford (2003), **Proposition 3.5** (p. 187; App. B.4, pp. 661–662): let `0 < α < 1`,
`0 < β < 1`, let the price index be predetermined (`log P_t` known at `t`) with bounded inflation,
the output gap `x` adapted and bounded, and let (2.5) hold. Then the pricing condition (2.6)
(with `ζ(Ŷ_T − Ŷⁿ_T) = ζ x_T`) holds **if and only if** inflation and the gap satisfy the New
Keynesian Phillips curve (2.12) `π_t = κ x_t + β E_t π_{t+1}`, `κ = (1 − α)(1 − αβ)ζ/α`
(2.13). -/
theorem prop35 {α β ζ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {P pstar x : ℕ → Ω → ℝ} (hPa : ∀ t, 𝔼.E t (P t) = P t)
    (hpre : ∀ t, 𝔼.E t (P (t + 1)) = P (t + 1)) (hπ : BoundedIncr P) (hxa : 𝔼.Adapted x)
    (hxb : BoundedProc x) (h25 : Eq25 α P pstar) :
    Eq26 𝔼 α β P pstar (fun T ω => ζ * x T ω) ↔ NKPCurve 𝔼 β (kappa α β ζ) (infl P) x := by
  obtain ⟨Mπ, hMπ⟩ := hπ
  obtain ⟨Mx, hMx⟩ := hxb
  have hab0 : 0 ≤ α * β := (mul_pos hα0 hβ0).le
  have hab1 : α * β < 1 := by nlinarith
  have hπb : ∀ t ω, |infl P t ω| ≤ Mπ := hMπ
  have h1a : 1 - α ≠ 0 := by linarith
  -- `p*` is known at `t`
  have hps : ∀ t, 𝔼.E t (pstar t) = pstar t := by
    intro t
    rw [pstar_of_eq25 hα1 h25 t]
    have : (fun ω => (P (t + 1) ω - α * P t ω) / (1 - α))
        = (1 - α)⁻¹ • (P (t + 1) - α • P t) := by
      funext ω; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; field_simp
    rw [this, map_smul, map_sub, map_smul, hpre t, hPa t]
  have hiff := eq26_iff_resetGap 𝔼 (ζ := ζ) hab0 hab1 hpre hps hπb hMx
  have hπa : ∀ t, 𝔼.E t (infl P t) = infl P t := by
    intro t
    have : infl P t = P (t + 1) - P t := rfl
    rw [this, map_sub, hpre t, hPa t]
  set u := resetForcing 𝔼 (α * β) ζ P x
  have hub := resetForcing_bounded 𝔼 (a := α * β) (ζ := ζ) hπb hMx
  have hua := resetForcing_adapted 𝔼 (P := P) (α * β) ζ hxa
  -- the reset gap `q = α/(1−α) π`
  set q : ℕ → Ω → ℝ := fun t ω => α / (1 - α) * infl P t ω with hq
  have hqE : ∀ t ω, 𝔼.E t (q (t + 1)) ω = α / (1 - α) * 𝔼.E t (infl P (t + 1)) ω := by
    intro t ω
    have : q (t + 1) = (α / (1 - α)) • infl P (t + 1) := rfl
    rw [this, map_smul]; rfl
  have hstep : ∀ t ω, (q t ω = α * β * 𝔼.E t (q (t + 1)) ω + u t ω) ↔
      infl P t ω = kappa α β ζ * x t ω + β * 𝔼.E t (infl P (t + 1)) ω := by
    intro t ω
    rw [hqE]
    simp only [hq, u, resetForcing, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← B17_iff_nkpc hα0 hα1]
  rw [hiff]
  constructor
  · intro h t
    funext ω
    have hq_eq : q = 𝔼.forwardSeries (α * β) u := by
      funext t' ω'
      rw [← resetGap_rec 𝔼 P x t' ω', ← h t' ω', inflation_eq_resetGap hα1 h25 t' ω']
    have hsol := congrFun (𝔼.forwardSeries_solves hab0 hab1 hub hua t) ω
    rw [← hq_eq] at hsol
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsol ⊢
    exact (hstep t ω).mp hsol
  · intro h t ω
    have hqsol : ∀ t, q t = (α * β) • 𝔼.E t (q (t + 1)) + u t := by
      intro t
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (hstep t ω).mpr ?_
      have := congrFun (h t) ω
      simpa [smul_eq_mul] using this
    have hqb : BoundedProc q := ⟨|α / (1 - α)| * Mπ, fun t ω => by
      simp only [hq, abs_mul]
      exact mul_le_mul_of_nonneg_left (hπb t ω) (abs_nonneg _)⟩
    have hq_eq := 𝔼.eq_forwardSeries hab0 hab1 hub hua hqsol hqb
    rw [resetGap_rec 𝔼 P x t ω, ← hq_eq, inflation_eq_resetGap hα1 h25 t ω]

/-! ### (2.14), the baseline slope and forecastable gaps -/

omit 𝔼 in
/-- Woodford (2003), eq. (2.14), p. 188: if `ζ x_t = (1 + ω̃θ)⁻¹ ŝ_t` (real marginal cost), then
`κ x_t = ξ ŝ_t` with `ξ` of (2.11). -/
theorem kappa_gap_eq_xi_s {α β ζ w x shat : ℝ} (hα0 : 0 < α) (hw : 1 + w ≠ 0)
    (h : ζ * x = (1 + w)⁻¹ * shat) :
    kappa α β ζ * x = QuadraticRoots.calvoXi α β w * shat := by
  unfold kappa QuadraticRoots.calvoXi
  have hα : α ≠ 0 := hα0.ne'
  rw [show (1 - α) * (1 - α * β) * ζ / α * x = (1 - α) * (1 - α * β) / α * (ζ * x) by ring, h]
  field_simp

/-- Woodford (2003), eq. (2.14), p. 188: when `ζ(Ŷ_t − Ŷⁿ_t) = (1 + ω̃θ)⁻¹ ŝ_t` at every date, the
NKPC (2.12) is equivalent to `π_t = ξ ŝ_t + β E_t π_{t+1}`. -/
theorem nkpc_iff_eq214 {α β ζ w : ℝ} (hα0 : 0 < α) (hw : 1 + w ≠ 0) {π x shat : ℕ → Ω → ℝ}
    (h : ∀ t ω, ζ * x t ω = (1 + w)⁻¹ * shat t ω) :
    NKPCurve 𝔼 β (kappa α β ζ) π x ↔ NKPCurve 𝔼 β (QuadraticRoots.calvoXi α β w) π shat := by
  have hk : ∀ t, kappa α β ζ • x t = QuadraticRoots.calvoXi α β w • shat t := by
    intro t; funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    exact kappa_gap_eq_xi_s hα0 hw (h t ω)
  simp only [NKPCurve, hk]

omit 𝔼 in
/-- Woodford (2003), p. 187 (the baseline model): with `ζ = (ω + σ⁻¹)/(1 + ωθ)`,
`κ = (ω + σ⁻¹)ξ = (1 − α)(1 − αβ)(ω + σ⁻¹)/(α(1 + ωθ))`, `ξ` of (2.11) with `ω̃ = ω`. -/
theorem kappa_baseline (α β ω σinv θ : ℝ) :
    kappa α β ((ω + σinv) / (1 + ω * θ)) = (ω + σinv) * QuadraticRoots.calvoXi α β (ω * θ) := by
  simp only [kappa, QuadraticRoots.calvoXi, div_eq_mul_inv, mul_inv]
  ring

/-- Woodford (2003), p. 188 ("nonzero values of `Ŷ_t − Ŷⁿ_t` can be forecasted at some earlier date
`t − j`; this simply requires that `E_{t−j}π_t` not equal `βE_{t−j}π_{t+1}`"): under the NKPC with
`κ ≠ 0`, for `s ≤ t`, `E_s x_t = 0` iff `E_s π_t = β E_s π_{t+1}`. -/
theorem forecastable_gap_iff {β κ : ℝ} (hκ : κ ≠ 0) {π x : ℕ → Ω → ℝ}
    (h : NKPCurve 𝔼 β κ π x) {s t : ℕ} (hst : s ≤ t) :
    𝔼.E s (x t) = 0 ↔ 𝔼.E s (π t) = β • 𝔼.E s (π (t + 1)) := by
  have hE : 𝔼.E s (π t) = κ • 𝔼.E s (x t) + β • 𝔼.E s (π (t + 1)) := by
    conv_lhs => rw [h t]
    rw [map_add, map_smul, map_smul, 𝔼.tower hst]
  rw [hE]
  constructor
  · intro h0; rw [h0, smul_zero, zero_add]
  · intro h1
    have : κ • 𝔼.E s (x t) = 0 := by
      have := congrArg (· - β • 𝔼.E s (π (t + 1))) h1
      simpa using this
    exact (smul_eq_zero.mp this).resolve_left hκ

/-! ### Comparative statics of `κ` -/

/-- Woodford (2003), p. 188 ("the short-run Phillips curve is flatter … the smaller the value of
`ζ`"): `κ` is strictly increasing in `ζ`. -/
theorem kappa_strictMono_zeta {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1) :
    StrictMono (fun ζ => kappa α β ζ) := by
  intro ζ₁ ζ₂ h
  have hk : 0 < (1 - α) * (1 - α * β) / α :=
    div_pos (mul_pos (by linarith) (by nlinarith)) hα0
  simp only [kappa]
  rw [show (1 - α) * (1 - α * β) * ζ₁ / α = (1 - α) * (1 - α * β) / α * ζ₁ by ring,
    show (1 - α) * (1 - α * β) * ζ₂ / α = (1 - α) * (1 - α * β) / α * ζ₂ by ring]
  exact mul_lt_mul_of_pos_left h hk

/-- Woodford (2003), p. 188 ("It is also flatter as `α` is larger"): for `β ≤ 1` and
`ζ > 0`, `κ` is strictly decreasing in `α ∈ (0, 1)`. -/
theorem kappa_strictAntiOn_alpha {β ζ : ℝ} (hβ1 : β ≤ 1) (hζ : 0 < ζ) :
    StrictAntiOn (fun α => kappa α β ζ) (Set.Ioo 0 1) := by
  intro α₁ h₁ α₂ h₂ h
  obtain ⟨h₁0, h₁1⟩ := h₁
  obtain ⟨h₂0, h₂1⟩ := h₂
  simp only [kappa]
  have e : ∀ α, α ≠ 0 → (1 - α) * (1 - α * β) * ζ / α = ζ * (α⁻¹ - (1 + β) + α * β) := by
    intro α hα; field_simp; ring
  rw [e α₁ h₁0.ne', e α₂ h₂0.ne']
  refine mul_lt_mul_of_pos_left ?_ hζ
  have hinv : α₂⁻¹ - α₁⁻¹ = -(α₂ - α₁) / (α₁ * α₂) := by field_simp; ring
  have hprod : α₁ * α₂ < 1 := by nlinarith
  have hpos : 0 < α₁ * α₂ := mul_pos h₁0 h₂0
  have hd : 0 < α₂ - α₁ := by linarith
  have : (α₂ - α₁) * β < (α₂ - α₁) / (α₁ * α₂) := by
    rw [lt_div_iff₀ hpos]
    have h1 : (α₂ - α₁) * β * (α₁ * α₂) ≤ (α₂ - α₁) * (α₁ * α₂) := by
      have := mul_le_mul_of_nonneg_left hβ1 hd.le
      nlinarith
    have h2 : (α₂ - α₁) * (α₁ * α₂) < α₂ - α₁ := by nlinarith
    linarith
  have : α₂⁻¹ - α₁⁻¹ + (α₂ - α₁) * β < 0 := by
    rw [hinv, neg_div]; linarith
  nlinarith

/-- Woodford (2003), p. 187 (the baseline slope): `κ(ω, θ) = (1 − α)(1 − αβ)(ω + σ⁻¹)/(α(1 + ωθ))`.
-/
noncomputable def kappaBase (α β σinv ω θ : ℝ) : ℝ :=
  (1 - α) * (1 - α * β) / α * ((ω + σinv) / (1 + ω * θ))

/-- Woodford (2003), p. 187: the effect of `ω` on the baseline slope,
`κ(ω₂) − κ(ω₁) = (1 − α)(1 − αβ)/α · (ω₂ − ω₁)(1 − θσ⁻¹)/((1 + ω₁θ)(1 + ω₂θ))`. -/
theorem kappaBase_omega_diff {α : ℝ} (hα : α ≠ 0) (β σinv θ : ℝ) {ω₁ ω₂ : ℝ} (h₁ : 1 + ω₁ * θ ≠ 0)
    (h₂ : 1 + ω₂ * θ ≠ 0) :
    kappaBase α β σinv ω₂ θ - kappaBase α β σinv ω₁ θ
      = (1 - α) * (1 - α * β) / α *
        ((ω₂ - ω₁) * (1 - θ * σinv) / ((1 + ω₁ * θ) * (1 + ω₂ * θ))) := by
  have h₁' : 1 + θ * ω₁ ≠ 0 := by rwa [mul_comm]
  have h₂' : 1 + θ * ω₂ ≠ 0 := by rwa [mul_comm]
  unfold kappaBase
  field_simp
  ring

/-- Woodford (2003), p. 187 (comparative statics in `ω`): with `θ ≥ 0`, `0 < α < 1`, `β < 1`, the
baseline `κ` is strictly increasing in `ω ≥ 0` when `θσ⁻¹ < 1`. -/
theorem kappaBase_strictMonoOn_omega {α β σinv θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hθ : 0 ≤ θ) (hlt : θ * σinv < 1) :
    StrictMonoOn (fun ω => kappaBase α β σinv ω θ) (Set.Ici 0) := by
  intro ω₁ h₁ ω₂ h₂ h
  simp only [Set.mem_Ici] at h₁ h₂
  have d₁ : 0 < 1 + ω₁ * θ := by nlinarith
  have d₂ : 0 < 1 + ω₂ * θ := by nlinarith
  have hk : 0 < (1 - α) * (1 - α * β) / α := div_pos (mul_pos (by linarith) (by nlinarith)) hα0
  have := kappaBase_omega_diff hα0.ne' β σinv θ d₁.ne' d₂.ne'
  have hpos : 0 < (ω₂ - ω₁) * (1 - θ * σinv) / ((1 + ω₁ * θ) * (1 + ω₂ * θ)) :=
    div_pos (mul_pos (by linarith) (by linarith)) (mul_pos d₁ d₂)
  have := mul_pos hk hpos
  simp only
  linarith

/-- Woodford (2003), p. 187 (comparative statics in `ω`): the baseline `κ` is strictly decreasing
in `ω ≥ 0` when `θσ⁻¹ > 1`. -/
theorem kappaBase_strictAntiOn_omega {α β σinv θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hθ : 0 ≤ θ) (hgt : 1 < θ * σinv) :
    StrictAntiOn (fun ω => kappaBase α β σinv ω θ) (Set.Ici 0) := by
  intro ω₁ h₁ ω₂ h₂ h
  simp only [Set.mem_Ici] at h₁ h₂
  have d₁ : 0 < 1 + ω₁ * θ := by nlinarith
  have d₂ : 0 < 1 + ω₂ * θ := by nlinarith
  have hk : 0 < (1 - α) * (1 - α * β) / α := div_pos (mul_pos (by linarith) (by nlinarith)) hα0
  have := kappaBase_omega_diff hα0.ne' β σinv θ d₁.ne' d₂.ne'
  have hneg : (ω₂ - ω₁) * (1 - θ * σinv) / ((1 + ω₁ * θ) * (1 + ω₂ * θ)) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by linarith) (by linarith)) (mul_pos d₁ d₂)
  have := mul_neg_of_pos_of_neg hk hneg
  simp only
  linarith

/-- Woodford (2003), p. 187: when `θσ⁻¹ = 1` the baseline `κ` does not depend on `ω ≥ 0`. -/
theorem kappaBase_const_omega {α β σinv θ : ℝ} (hα0 : 0 < α) (hθ : 0 ≤ θ) (heq : θ * σinv = 1)
    {ω₁ ω₂ : ℝ} (h₁ : 0 ≤ ω₁) (h₂ : 0 ≤ ω₂) :
    kappaBase α β σinv ω₁ θ = kappaBase α β σinv ω₂ θ := by
  have d₁ : 0 < 1 + ω₁ * θ := by nlinarith
  have d₂ : 0 < 1 + ω₂ * θ := by nlinarith
  have := kappaBase_omega_diff hα0.ne' β σinv θ d₁.ne' d₂.ne'
  rw [heq, sub_self, mul_zero, zero_div, mul_zero, sub_eq_zero] at this
  exact this.symm

/-- Woodford (2003), p. 187: the derivative of the baseline `κ` in `ω`,
`(1 − α)(1 − αβ)/α · (1 − θσ⁻¹)/(1 + ωθ)²`. -/
theorem hasDerivAt_kappaBase_omega (α β σinv θ : ℝ) {ω : ℝ} (hω : 1 + ω * θ ≠ 0) :
    HasDerivAt (fun v => kappaBase α β σinv v θ)
      ((1 - α) * (1 - α * β) / α * ((1 - θ * σinv) / (1 + ω * θ) ^ 2)) ω := by
  have h1 : HasDerivAt (fun v : ℝ => v + σinv) 1 ω := (hasDerivAt_id ω).add_const σinv
  have h2 : HasDerivAt (fun v : ℝ => 1 + v * θ) θ ω := by
    simpa using ((hasDerivAt_id ω).mul_const θ).const_add 1
  have h3 := (h1.div h2 hω).const_mul ((1 - α) * (1 - α * β) / α)
  refine h3.congr_deriv ?_
  field_simp
  ring

/-- Woodford (2003), p. 187: the derivative of the baseline `κ` in `θ`,
`−(1 − α)(1 − αβ)/α · ω(ω + σ⁻¹)/(1 + ωθ)²`. -/
theorem hasDerivAt_kappaBase_theta (α β σinv ω : ℝ) {θ : ℝ} (hθ : 1 + ω * θ ≠ 0) :
    HasDerivAt (fun v => kappaBase α β σinv ω v)
      (-((1 - α) * (1 - α * β) / α * (ω * (ω + σinv) / (1 + ω * θ) ^ 2))) θ := by
  have h2 : HasDerivAt (fun v : ℝ => 1 + ω * v) ω θ := by
    simpa using ((hasDerivAt_id θ).const_mul ω).const_add 1
  have h3 := ((hasDerivAt_const θ (ω + σinv)).div h2 hθ).const_mul
    ((1 - α) * (1 - α * β) / α)
  refine h3.congr_deriv ?_
  field_simp
  ring

/-- Woodford (2003), p. 187: with `ω > 0` and `ω + σ⁻¹ > 0`, the baseline `κ` is strictly
decreasing in `θ ≥ 0` (more substitutable goods mean more strategic complementarity). -/
theorem kappaBase_strictAntiOn_theta {α β σinv ω : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hω : 0 < ω) (hωσ : 0 < ω + σinv) :
    StrictAntiOn (fun θ => kappaBase α β σinv ω θ) (Set.Ici 0) := by
  intro θ₁ h₁ θ₂ h₂ h
  simp only [Set.mem_Ici] at h₁ h₂
  have d₁ : 0 < 1 + ω * θ₁ := by nlinarith
  have d₂ : 0 < 1 + ω * θ₂ := by nlinarith
  have hk : 0 < (1 - α) * (1 - α * β) / α := div_pos (mul_pos (by linarith) (by nlinarith)) hα0
  simp only [kappaBase]
  refine mul_lt_mul_of_pos_left ?_ hk
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith [mul_pos (mul_pos hωσ hω) (sub_pos.mpr h)]

/-- Woodford (2003), p. 188: prices become completely rigid as `α → 1⁻`, and `κ → 0`. -/
theorem tendsto_kappa_alpha_one (β ζ : ℝ) :
    Tendsto (fun α => kappa α β ζ) (𝓝[<] 1) (𝓝 0) := by
  have hc : ContinuousAt (fun α => kappa α β ζ) 1 := by
    unfold kappa
    exact ((continuousAt_const.sub continuousAt_id).mul (continuousAt_const.sub
      (continuousAt_id.mul continuousAt_const))).mul continuousAt_const |>.div continuousAt_id
      one_ne_zero
  have h := hc.tendsto
  simp only [kappa, sub_self, zero_mul, zero_div] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- Woodford (2003), p. 188: as prices become fully flexible (`α → 0⁺`), `κ → ∞` (`ζ > 0`). -/
theorem tendsto_kappa_alpha_zero {β ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun α => kappa α β ζ) (𝓝[>] 0) atTop := by
  have hnum : Tendsto (fun α : ℝ => (1 - α) * (1 - α * β) * ζ) (𝓝[>] 0) (𝓝 ζ) := by
    have : ContinuousAt (fun α : ℝ => (1 - α) * (1 - α * β) * ζ) 0 := by fun_prop
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun α : ℝ => α⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have := hnum.pos_mul_atTop hζ hinv
  refine this.congr fun α => ?_
  simp only [kappa, div_eq_mul_inv]

end Woodford.NominalRigidities.NKPC
