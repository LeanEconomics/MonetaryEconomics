/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.ForwardSolution
import NominalRigidities.QuadraticRoots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Persistent real effects of nominal disturbances

Woodford (2003), *Interest and Prices*, Chapter 3, §2.3, pp. 188–197, and Appendix B.5,
pp. 662–664 (Proposition 3.6).

## Main results

* The characteristic polynomial (2.19)/(B.20) `βλ² − (1 + β + κ)λ + 1`: its roots
  `0 < λ₁ < 1 < β⁻¹ < λ₂` (`root_location`), Vieta, `κ = β(1 − λ₁)(λ₂ − 1)` (`kappa_eq`), the
  lag factorisation `A(L) = β(1 − λ₁L)(1 − λ₂L)` (`lagPoly_factor`).
* Impulse responses (2.16)–(2.18), generalised to any nominal-spending response `Ỹ` (B.24):
  `IRFEq`; all solutions `irfEq_iff_exists`; uniqueness among bounded sequences
  `irfEq_bounded_unique` and the unbounded continuum outside `irfEq_unbounded_family`; the
  forward solution of `(1 − λ₁L)p̃` as a genuine `HasSum` (`irf_forward_hasSum`).
* **Proposition 3.6**: `prop_3_6` (terminal condition (2.17)), `prop_3_6_bounded`,
  `prop_3_6_all_solutions`, along the book's route (`forward_sum_one`, `z_eq_of_bounded`,
  `first_order_solution`), and the shape claims `y36_zero`, `y36_decay`, `p36_rise`.
* The stochastic model for an arbitrary `ExpectationSystem`: (2.12) in price-level form
  `NKPC`; existence and uniqueness in the linear-growth class (`nkpc_existsUnique`) and in the
  bounded-output-gap class (`nkpc_existsUnique_gap`); a continuum of explosive solutions outside
  it (`nkpc_not_unique`, `nkpc_solutions_not_countable`); impulse responses as responses of the
  stochastic equilibrium to date-`s` news (`shock_response`, `shock_response_expect`, the exact
  derivative `shock_hasDerivAt`, and `prop_3_6_stochastic`).
* The New Classical comparison: `ncpc_iff`, `ncpc_shock_gap` (output moves only on impact).
* Comparative statics (p. 192): `lam1_strictAnti`, `lam1_tendsto_zero_atTop`,
  `lam1_tendsto_one`, `lam1_strictMono_alpha`, `lam1_strictAnti_zeta`.
* The contract multiplier (pp. 193–194): `charPoly_alpha` (`P(α) = (1 − α)(1 − αβ)(1 − ζ)`),
  `alpha_lt_lam_iff` (`λ > α ⟺ ζ < 1`), `alpha_eq_lam_iff`, `lam_lt_alpha_iff`,
  `rpow_halfLife`, `contractMult_eq`, `contractMult_gt_one_iff`.
* (2.20) as a genuine continuous-time limit: `ct_limit` (`log λ⁻¹/Δ → n`),
  `contractMult_tendsto`, `div_ctRoot_eq_cmLimit`, `cmLimit_gt_one_iff`,
  `cmLimit_tendsto_atTop` (`→ ζ^{−1/2}` as `a* → ∞`), `cmLimit_eq_iff`.
* The numbers quoted on pp. 191 and 195–196 (`lam1_fig37`, `zeta_for_twenty`, `zeta_for_144`,
  `cmLimit_010`, `cmLimit_015`, `half_lives_55_68`, `sync_half_life`, `frac_changed_028`).

The solution class of App. B.5 ("the unique solution satisfying the terminal condition") is
made precise in two ways: bounded impulse responses (equivalently `p̃_k → 1`), and, for the
stochastic model, expected log prices of at most linear growth (`LinGrowth`), which contains
every solution with a stationary output gap.
-/

namespace Woodford.NominalRigidities.Persistence

open Filter Topology QuadraticRoots

/-! ### The characteristic polynomial (2.19) and its roots

The polynomial, its roots and their general properties are those of
`Woodford.NominalRigidities.QuadraticRoots` (with `c = κ`); the book-facing statements of
App. B.5 are restated here from that module. -/

/-- Woodford (2003), App. B.5, p. 663 (Vieta): `λ₁ λ₂ = β⁻¹` (restated from
`QuadraticRoots.lam1_mul_lam2`). -/
theorem lam1_mul_lam2 {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    lam1 β κ * lam2 β κ = β⁻¹ :=
  QuadraticRoots.lam1_mul_lam2 hβ hκ

/-- Woodford (2003), App. B.5, p. 663: `0 < λ₁ < 1 < β⁻¹ < λ₂` (for `0 < β < 1`, `κ > 0`;
restated from `QuadraticRoots.root_location`). -/
theorem root_location {β κ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) :
    0 < lam1 β κ ∧ lam1 β κ < 1 ∧ 1 < β⁻¹ ∧ β⁻¹ < lam2 β κ :=
  QuadraticRoots.root_location hβ hβ1 hκ

/-- Woodford (2003), App. B.5, p. 663: `κ = β (1 − λ₁)(λ₂ − 1)` (from `P(1) = −κ`). -/
theorem kappa_eq {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    κ = β * (1 - lam1 β κ) * (lam2 β κ - 1) := by
  have h := charPoly_one β κ
  rw [charPoly_factor hβ hκ] at h
  linarith

/-- Woodford (2003), App. B.5, p. 663: the lag polynomial `A(L) = L² − (1 + β + κ)L + β`
factors as `β (1 − λ₁ L)(1 − λ₂ L)` (restated from `QuadraticRoots.lagPoly_factor`). -/
theorem lagPoly_factor {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (L : ℝ) :
    L ^ 2 - (1 + β + κ) * L + β = β * (1 - lam1 β κ * L) * (1 - lam2 β κ * L) :=
  QuadraticRoots.lagPoly_factor hβ hκ L

/-- Woodford (2003), App. B.5, p. 663: `κ / (β λ₂) = (1 − λ₁)(1 − λ₂⁻¹)`, the coefficient of the
forward solution. -/
theorem kappa_div_eq {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    κ / (β * lam2 β κ) = (1 - lam1 β κ) * (1 - (lam2 β κ)⁻¹) := by
  have h2 : lam2 β κ ≠ 0 := by linarith [(lam1_lt_one_lt_lam2 hβ hκ).2]
  have hk := kappa_eq hβ hκ
  set l1 := lam1 β κ
  set l2 := lam2 β κ
  rw [hk]
  field_simp

/-! ### Impulse-response sequences: (2.16)–(2.18) and their generalisation (B.24) -/

/-- Woodford (2003), (2.18), p. 190, p. 189, and §4, pp. 223–235: the lag of a sequence with a
given date-`(−1)` value, `prev x₋₁ x 0 = x₋₁` and `prev x₋₁ x (k + 1) = x k`. With `x₋₁ = 0` it is
the lagged impulse response `p̃_{k−1}` of (2.18) (`p̃_{−1} = 0`); with `x₋₁ = log P_{−1}` it is the
lagged log price level of p. 189. -/
def prev {X : Type*} (x0 : X) (x : ℕ → X) : ℕ → X
  | 0 => x0
  | k + 1 => x k

/-- Woodford (2003), (2.18), p. 190, and p. 189: `prev x₋₁ x 0 = x₋₁`. -/
@[simp] theorem prev_zero {X : Type*} (x0 : X) (x : ℕ → X) : prev x0 x 0 = x0 := rfl

/-- Woodford (2003), (2.16), p. 189: `prev x₋₁ x (k + 1) = x k`. -/
@[simp] theorem prev_succ {X : Type*} (x0 : X) (x : ℕ → X) (k : ℕ) :
    prev x0 x (k + 1) = x k := rfl

/-- Woodford (2003), (2.16): the lag operator is linear. -/
theorem prev_add_smul (p h : ℕ → ℝ) (c : ℝ) (k : ℕ) :
    prev 0 (fun j => p j + c * h j) k = prev 0 p k + c * prev 0 h k := by
  cases k <;> simp

/-- Woodford (2003), (2.16) p. 189 with (2.18) p. 190, for a general response `Ỹ_k` of expected
nominal spending (`Ỹ_k = 1` in (2.16), `Ỹ_k = 1 − ρ^{k+1}` in (B.24) p. 665):
`p̃_k − p̃_{k−1} = κ (Ỹ_k − p̃_k) + β (p̃_{k+1} − p̃_k)` for all `k ≥ 0`, with `p̃_{−1} = 0`. -/
def IRFEq (β κ : ℝ) (Y p : ℕ → ℝ) : Prop :=
  ∀ k, p k - prev 0 p k = κ * (Y k - p k) + β * (p (k + 1) - p k)

/-- Woodford (2003), (B.21) p. 663 and (B.24) p. 665: (2.16) is the lag-polynomial equation
`A(L) p̃_{k+1} = p̃_{k−1} − (1 + β + κ) p̃_k + β p̃_{k+1} = −κ Ỹ_k`. -/
theorem irfEq_iff_lag (β κ : ℝ) (Y p : ℕ → ℝ) :
    IRFEq β κ Y p ↔ ∀ k, prev 0 p k - (1 + β + κ) * p k + β * p (k + 1) = -κ * Y k := by
  refine forall_congr' fun k => ?_
  constructor <;> intro h <;> linarith

/-- Woodford (2003), (2.16): given `p̃_{−1} = 0`, a solution is determined by `p̃_0`. -/
theorem irfEq_ext {β κ : ℝ} (hβ : β ≠ 0) {Y p q : ℕ → ℝ} (hp : IRFEq β κ Y p)
    (hq : IRFEq β κ Y q) (h0 : p 0 = q 0) : p = q := by
  have key : ∀ k, p k = q k ∧ p (k + 1) = q (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨h0, ?_⟩
      have a := hp 0
      have b := hq 0
      simp only [prev_zero] at a b
      rw [h0] at a
      have : β * (p 1 - q 1) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hβ
      · linarith
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have a := hp (k + 1)
      have b := hq (k + 1)
      simp only [prev_succ] at a b
      rw [ih.1, ih.2] at a
      have : β * (p (k + 1 + 1) - q (k + 1 + 1)) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hβ
      · linarith
  funext k
  exact (key k).1

/-- Woodford (2003), App. B.5: the homogeneous solution `λ₂^{k+1} − λ₁^{k+1}` of (2.16)
(it vanishes at `k = −1`). -/
noncomputable def hom (β κ : ℝ) (k : ℕ) : ℝ := lam2 β κ ^ (k + 1) - lam1 β κ ^ (k + 1)

/-- Woodford (2003), App. B.5: the lag of the homogeneous solution, `λ₂^k − λ₁^k`. -/
theorem prev_hom (β κ : ℝ) (k : ℕ) : prev 0 (hom β κ) k = lam2 β κ ^ k - lam1 β κ ^ k := by
  cases k <;> simp [hom]

/-- Woodford (2003), App. B.5: `λ₂^{k+1} − λ₁^{k+1}` solves the homogeneous version of (2.16)
(`Ỹ = 0`) together with `p̃_{−1} = 0`. -/
theorem hom_irfEq {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    IRFEq β κ (fun _ => 0) (hom β κ) := by
  intro k
  have r1 := charPoly_lam1 hβ hκ
  have r2 := charPoly_lam2 hβ hκ
  unfold charPoly at r1 r2
  rw [prev_hom]
  unfold hom
  linear_combination (-(lam2 β κ ^ k)) * r2 + lam1 β κ ^ k * r1

/-- Woodford (2003), (2.16): solutions are stable under adding multiples of a homogeneous
solution. -/
theorem irfEq_add_smul {β κ : ℝ} {Y p h : ℕ → ℝ} (hp : IRFEq β κ Y p)
    (hh : IRFEq β κ (fun _ => 0) h) (c : ℝ) : IRFEq β κ Y (fun k => p k + c * h k) := by
  intro k
  have a := hp k
  have b := hh k
  rw [prev_add_smul]
  linear_combination a + c * b

/-- Woodford (2003), App. B.5: `hom 0 = λ₂ − λ₁ ≠ 0`. -/
theorem hom_zero_ne {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) : hom β κ 0 ≠ 0 := by
  have := lam1_lt_lam2 hβ hκ
  unfold hom
  simp only [zero_add, pow_one]
  linarith

/-- Woodford (2003), (2.16)–(2.18): **all** solutions. Given one solution `p₀` of (2.16) with
`p̃_{−1} = 0`, the solutions are exactly `p₀ + c (λ₂^{k+1} − λ₁^{k+1})`, `c ∈ ℝ`. -/
theorem irfEq_iff_exists {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {Y p₀ p : ℕ → ℝ}
    (hp₀ : IRFEq β κ Y p₀) :
    IRFEq β κ Y p ↔ ∃ c : ℝ, p = fun k => p₀ k + c * hom β κ k := by
  constructor
  · intro hp
    refine ⟨(p 0 - p₀ 0) / hom β κ 0, irfEq_ext hβ.ne' hp
      (irfEq_add_smul hp₀ (hom_irfEq hβ hκ) _) ?_⟩
    have := hom_zero_ne hβ hκ
    field_simp
    ring
  · rintro ⟨c, rfl⟩
    exact irfEq_add_smul hp₀ (hom_irfEq hβ hκ) c

/-- Woodford (2003), App. B.5: every non-zero multiple of the homogeneous solution is
unbounded (it grows like `λ₂^k`, `λ₂ > 1`). -/
theorem hom_unbounded {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {c : ℝ} (hc : c ≠ 0) :
    ¬ ∃ M, ∀ k, |c * hom β κ k| ≤ M := by
  rintro ⟨M, hM⟩
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have h1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have h0 := lam1_pos hβ hκ
  have hc0 : 0 < |c| := abs_pos.2 hc
  obtain ⟨n, hn⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt h2).eventually_gt_atTop (M / |c| + 1)).exists
  have hpow : lam2 β κ ^ n ≤ lam2 β κ ^ (n + 1) := pow_le_pow_right₀ h2.le (Nat.le_succ n)
  have hl1 : lam1 β κ ^ (n + 1) ≤ 1 := pow_le_one₀ h0.le h1.le
  have hM' := hM n
  rw [abs_mul] at hM'
  have hh : M / |c| < hom β κ n := by unfold hom; linarith
  have hpos : 0 < hom β κ n := by
    have : 1 < lam2 β κ ^ (n + 1) := one_lt_pow₀ h2 (by omega)
    unfold hom; linarith
  rw [abs_of_pos hpos] at hM'
  have : M < |c| * hom β κ n := by
    rw [div_lt_iff₀ hc0] at hh; linarith
  linarith

/-- Woodford (2003), (2.17): a convergent sequence is bounded. -/
theorem bounded_of_tendsto {p : ℕ → ℝ} {L : ℝ} (h : Tendsto p atTop (𝓝 L)) :
    ∃ M, ∀ k, |p k| ≤ M := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto p h)
  exact ⟨C, fun k => hC (p k) ⟨k, rfl⟩⟩

/-- Woodford (2003), App. B.5, p. 663 ("the unique solution satisfying the terminal condition"):
two bounded solutions of the generalised (2.16) with `p̃_{−1} = 0` coincide. -/
theorem irfEq_bounded_unique {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {Y p q : ℕ → ℝ}
    (hp : IRFEq β κ Y p) (hq : IRFEq β κ Y q) (hpb : ∃ M, ∀ k, |p k| ≤ M)
    (hqb : ∃ M, ∀ k, |q k| ≤ M) : p = q := by
  obtain ⟨c, hc⟩ := (irfEq_iff_exists hβ hκ hp).1 hq
  by_cases h0 : c = 0
  · rw [hc, h0]; funext k; simp
  · exfalso
    obtain ⟨M₁, hM₁⟩ := hpb
    obtain ⟨M₂, hM₂⟩ := hqb
    refine hom_unbounded hβ hκ h0 ⟨M₂ + M₁, fun k => ?_⟩
    have e : c * hom β κ k = q k - p k := by rw [hc]; ring
    rw [e]
    exact (abs_sub _ _).trans (add_le_add (hM₂ k) (hM₁ k))

/-- Woodford (2003), App. B.5: **non-uniqueness outside the class**. Next to a bounded solution
`p₀`, every `p₀ + c (λ₂^{k+1} − λ₁^{k+1})` with `c ≠ 0` also solves (2.16) with `p̃_{−1} = 0`,
but is unbounded. -/
theorem irfEq_unbounded_family {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {Y p₀ : ℕ → ℝ}
    (hp₀ : IRFEq β κ Y p₀) (hb : ∃ M, ∀ k, |p₀ k| ≤ M) {c : ℝ} (hc : c ≠ 0) :
    IRFEq β κ Y (fun k => p₀ k + c * hom β κ k) ∧
      ¬ ∃ M, ∀ k, |p₀ k + c * hom β κ k| ≤ M := by
  refine ⟨irfEq_add_smul hp₀ (hom_irfEq hβ hκ) c, ?_⟩
  rintro ⟨M, hM⟩
  obtain ⟨M₀, hM₀⟩ := hb
  refine hom_unbounded hβ hκ hc ⟨M + M₀, fun k => ?_⟩
  have e : c * hom β κ k = (p₀ k + c * hom β κ k) - p₀ k := by ring
  rw [e]
  exact (abs_sub _ _).trans (add_le_add (hM k) (hM₀ k))

/-! ### Forward solution of a first-order equation for sequences -/

/-- Woodford (2003), App. B.5, p. 663 ("the same method as in the proof of Proposition 3.4"):
a bounded sequence with `z_k = a z_{k+1} + u_k`, `|a| < 1`, bounded `u`, is the forward sum
`z_k = ∑_{j ≥ 0} aʲ u_{k+j}` (as a genuine `HasSum`). -/
theorem seq_forward_hasSum {a : ℝ} (ha : |a| < 1) {u z : ℕ → ℝ} {Mu Mz : ℝ}
    (hu : ∀ k, |u k| ≤ Mu) (hz : ∀ k, |z k| ≤ Mz) (h : ∀ k, z k = a * z (k + 1) + u k)
    (k : ℕ) : HasSum (fun j => a ^ j * u (k + j)) (z k) := by
  have iter : ∀ n, z k = a ^ n * z (k + n) + ∑ j ∈ Finset.range n, a ^ j * u (k + j) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, h (k + n), Finset.sum_range_succ, show k + (n + 1) = k + n + 1 by omega]
      ring
  have hsum : Summable (fun j => a ^ j * u (k + j)) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_right Mu) (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hu (k + j)) (pow_nonneg (abs_nonneg a) j)
  refine hsum.hasSum_iff_tendsto_nat.2 ?_
  have hlim : Tendsto (fun n => a ^ n * z (k + n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n => ?_)
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).mul_const Mz)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hz (k + n)) (pow_nonneg (abs_nonneg a) n)
  have e : (fun n => ∑ j ∈ Finset.range n, a ^ j * u (k + j)) =
      fun n => z k - a ^ n * z (k + n) := by
    funext n; rw [iter n]; ring
  rw [e]
  simpa using (tendsto_const_nhds (x := z k)).sub hlim

/-! ### The forward solution of (2.16): `(1 − λ₁L) p̃_k` -/

/-- Woodford (2003), App. B.5, p. 663: with `z_k ≡ (1 − λ₁ L) p̃_k = p̃_k − λ₁ p̃_{k−1}`, the
generalised (2.16) becomes the first-order forward equation `z_k = λ₂⁻¹ z_{k+1} + κ/(βλ₂) Ỹ_k`. -/
theorem irf_z_forward_eq {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {Y p : ℕ → ℝ}
    (hp : IRFEq β κ Y p) (k : ℕ) :
    p k - lam1 β κ * prev 0 p k =
      (lam2 β κ)⁻¹ * (p (k + 1) - lam1 β κ * prev 0 p (k + 1)) +
        κ / (β * lam2 β κ) * Y k := by
  have e1 := beta_mul_sum (c := κ) hβ
  have e2 := beta_mul_prod hβ hκ
  have hk := hp k
  have h2 : lam2 β κ ≠ 0 := by linarith [(lam1_lt_one_lt_lam2 hβ hκ).2]
  have key : β * lam2 β κ * (p k - lam1 β κ * prev 0 p k) =
      β * (p (k + 1) - lam1 β κ * p k) + κ * Y k := by
    linear_combination hk + p k * e1 - prev 0 p k * e2
  rw [prev_succ]
  have hne : β * lam2 β κ ≠ 0 := mul_ne_zero hβ.ne' h2
  calc p k - lam1 β κ * prev 0 p k
      = β * lam2 β κ * (p k - lam1 β κ * prev 0 p k) / (β * lam2 β κ) := by field_simp
    _ = _ := by rw [key]; field_simp

/-- Woodford (2003), App. B.5, p. 663: for a bounded solution of the generalised (2.16) (and
bounded `Ỹ`), `(1 − λ₁L) p̃_k = β⁻¹λ₂⁻¹κ ∑_{j ≥ 0} λ₂^{−j} Ỹ_{k+j}`, as a genuine `HasSum`. -/
theorem irf_forward_hasSum {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {Y p : ℕ → ℝ} {MY Mp : ℝ}
    (hY : ∀ k, |Y k| ≤ MY) (hp : IRFEq β κ Y p) (hpb : ∀ k, |p k| ≤ Mp) (k : ℕ) :
    HasSum (fun j => (lam2 β κ)⁻¹ ^ j * (κ / (β * lam2 β κ) * Y (k + j)))
      (p k - lam1 β κ * prev 0 p k) := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have h0 := lam1_pos hβ hκ
  have ha : |(lam2 β κ)⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.2 (by linarith))]
    exact inv_lt_one_of_one_lt₀ h2
  have hMp : 0 ≤ Mp := (abs_nonneg _).trans (hpb 0)
  have hprev : ∀ k, |prev 0 p k| ≤ Mp := by
    intro k; cases k with
    | zero => simpa using hMp
    | succ k => exact hpb k
  refine seq_forward_hasSum ha (Mu := |κ / (β * lam2 β κ)| * MY)
    (Mz := Mp + lam1 β κ * Mp) (fun j => ?_) (fun j => ?_) (irf_z_forward_eq hβ hκ hp) k
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hY j) (abs_nonneg _)
  · calc |p j - lam1 β κ * prev 0 p j| ≤ |p j| + |lam1 β κ * prev 0 p j| := abs_sub _ _
      _ ≤ Mp + lam1 β κ * Mp := by
        rw [abs_mul, abs_of_pos h0]
        exact add_le_add (hpb j) (mul_le_mul_of_nonneg_left (hprev j) h0.le)

/-- Woodford (2003), App. B.5, pp. 663–664: given `(1 − λ₁L)p̃_k = z_k`, the price response is the
backward sum `p̃_k = ∑_{i ≤ k} λ₁ⁱ z_{k−i}` (initial condition `p̃_{−1} = 0`). -/
theorem backward_sum {l : ℝ} {p z : ℕ → ℝ} (h : ∀ k, p k - l * prev 0 p k = z k) (k : ℕ) :
    p k = ∑ i ∈ Finset.range (k + 1), l ^ i * z (k - i) := by
  induction k with
  | zero =>
    have := h 0
    simp only [prev_zero, mul_zero, sub_zero] at this
    simp [this]
  | succ k ih =>
    have hk := h (k + 1)
    rw [prev_succ, ih] at hk
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero]
    have : ∀ i ∈ Finset.range (k + 1), l ^ (i + 1) * z (k + 1 - (i + 1)) =
        l * (l ^ i * z (k - i)) := fun i _ => by
      rw [show k + 1 - (i + 1) = k - i by omega, pow_succ]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    linarith

/-! ### Proposition 3.6 (deterministic impulse responses) -/

/-- Woodford (2003), Prop. 3.6, p. 190 and (B.18), p. 663: `p̃_k = 1 − λ^{k+1}`. -/
noncomputable def p36 (β κ : ℝ) (k : ℕ) : ℝ := 1 - lam1 β κ ^ (k + 1)

/-- Woodford (2003), Prop. 3.6, p. 190 and (B.19), p. 663: `ỹ_k = λ^{k+1}`. -/
noncomputable def y36 (β κ : ℝ) (k : ℕ) : ℝ := lam1 β κ ^ (k + 1)

/-- Woodford (2003), (B.18): the lag of `p̃`, `p̃_{k−1} = 1 − λ^k` (also at `k = 0`). -/
theorem prev_p36 (β κ : ℝ) (k : ℕ) : prev 0 (p36 β κ) k = 1 - lam1 β κ ^ k := by
  cases k <;> simp [p36]

/-- Woodford (2003), Prop. 3.6: `p̃_k = 1 − λ^{k+1}` solves (2.16) with `p̃_{−1} = 0`. -/
theorem p36_irfEq {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    IRFEq β κ (fun _ => 1) (p36 β κ) := by
  intro k
  have r1 := charPoly_lam1 hβ hκ
  unfold charPoly at r1
  rw [prev_p36]
  unfold p36
  linear_combination (lam1 β κ ^ k) * r1

/-- Woodford (2003), App. B.5, pp. 663–664: the forward sum
`β⁻¹λ₂⁻¹κ ∑_{j ≥ 0} λ₂^{−j}` converges to `1 − λ₁`. -/
theorem forward_sum_one {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    HasSum (fun j : ℕ => (lam2 β κ)⁻¹ ^ j * (κ / (β * lam2 β κ) * 1)) (1 - lam1 β κ) := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have ha0 : 0 ≤ (lam2 β κ)⁻¹ := inv_nonneg.2 (by linarith)
  have ha1 : (lam2 β κ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
  have hg := (hasSum_geometric_of_lt_one ha0 ha1).mul_right (κ / (β * lam2 β κ) * 1)
  convert hg using 1
  rw [kappa_div_eq hβ hκ]
  have : 1 - (lam2 β κ)⁻¹ ≠ 0 := by linarith
  have : lam2 β κ - 1 ≠ 0 := by linarith
  field_simp

/-- Woodford (2003), App. B.5, p. 664: the two printed evaluations of the forward sum,
`β⁻¹λ₂⁻¹κ (1 − λ₂⁻¹)⁻¹ = β⁻¹κ/(λ₂ − 1) = 1 − λ₁`. -/
theorem forward_value_eq {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    β⁻¹ * (lam2 β κ)⁻¹ * κ * (1 - (lam2 β κ)⁻¹)⁻¹ = β⁻¹ * κ / (lam2 β κ - 1) ∧
      β⁻¹ * κ / (lam2 β κ - 1) = 1 - lam1 β κ := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have h20 : lam2 β κ ≠ 0 := by linarith
  have h21 : lam2 β κ - 1 ≠ 0 := by linarith
  have hk := kappa_eq hβ hκ
  constructor
  · have : 1 - (lam2 β κ)⁻¹ = (lam2 β κ - 1) / lam2 β κ := by field_simp
    rw [this]
    field_simp
  · set l1 := lam1 β κ
    set l2 := lam2 β κ
    rw [hk]
    field_simp

/-- Woodford (2003), App. B.5, p. 664: for every bounded solution of (2.16) with `p̃_{−1} = 0`,
`z_k = (1 − λ₁L) p̃_k` is the constant `1 − λ₁`. -/
theorem z_eq_of_bounded {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {p : ℕ → ℝ}
    (hp : IRFEq β κ (fun _ => 1) p) (hb : ∃ M, ∀ k, |p k| ≤ M) (k : ℕ) :
    p k - lam1 β κ * prev 0 p k = 1 - lam1 β κ := by
  obtain ⟨M, hM⟩ := hb
  exact (irf_forward_hasSum hβ hκ (MY := 1) (fun _ => by simp) hp hM k).unique
    (forward_sum_one hβ hκ)

/-- Woodford (2003), App. B.5, p. 664: the first-order recursion
`p̃_k = λ₁ p̃_{k−1} + (1 − λ₁)` with `p̃_{−1} = 0` has the solution `p̃_k = 1 − λ₁^{k+1}`. -/
theorem first_order_solution {l : ℝ} {p : ℕ → ℝ} (h : ∀ k, p k = l * prev 0 p k + (1 - l))
    (k : ℕ) : p k = 1 - l ^ (k + 1) := by
  induction k with
  | zero => rw [h 0]; simp
  | succ k ih => rw [h (k + 1), prev_succ, ih]; ring

/-- **Proposition 3.6** (Woodford 2003, p. 190; App. B.5, pp. 662–664), uniqueness half, along
the book's route: any bounded solution of (2.16) with `p̃_{−1} = 0` is `p̃_k = 1 − λ^{k+1}`. -/
theorem prop_3_6_unique {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {p : ℕ → ℝ}
    (hp : IRFEq β κ (fun _ => 1) p) (hb : ∃ M, ∀ k, |p k| ≤ M) : p = p36 β κ := by
  funext k
  exact first_order_solution (fun j => by linarith [z_eq_of_bounded hβ hκ hp hb j]) k

/-- Woodford (2003), Prop. 3.6: `p̃_k = 1 − λ^{k+1} → 1`, the terminal condition (2.17). -/
theorem p36_tendsto {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    Tendsto (p36 β κ) atTop (𝓝 1) := by
  have h0 := lam1_pos hβ hκ
  have h1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have : Tendsto (fun k : ℕ => lam1 β κ ^ (k + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun k : ℕ => 1 - lam1 β κ ^ (k + 1)) atTop (𝓝 1)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this

/-- **Proposition 3.6** (Woodford 2003, p. 190) in full: among sequences satisfying (2.16) and
the initial condition (2.18) `p̃_{−1} = 0`, exactly one satisfies the terminal condition (2.17)
`p̃_k → 1`, namely `p̃_k = 1 − λ^{k+1}`. -/
theorem prop_3_6 {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (p : ℕ → ℝ) :
    (IRFEq β κ (fun _ => 1) p ∧ Tendsto p atTop (𝓝 1)) ↔ p = p36 β κ := by
  constructor
  · rintro ⟨hp, ht⟩
    exact prop_3_6_unique hβ hκ hp (bounded_of_tendsto ht)
  · rintro rfl
    exact ⟨p36_irfEq hβ hκ, p36_tendsto hβ hκ⟩

/-- Woodford (2003), Prop. 3.6: the same uniqueness holds in the larger class of bounded
sequences. -/
theorem prop_3_6_bounded {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (p : ℕ → ℝ) :
    (IRFEq β κ (fun _ => 1) p ∧ ∃ M, ∀ k, |p k| ≤ M) ↔ p = p36 β κ := by
  constructor
  · rintro ⟨hp, hb⟩
    exact prop_3_6_unique hβ hκ hp hb
  · rintro rfl
    exact ⟨p36_irfEq hβ hκ, bounded_of_tendsto (p36_tendsto hβ hκ)⟩

/-- Woodford (2003), Prop. 3.6, non-uniqueness without the terminal condition: the solutions of
(2.16) with `p̃_{−1} = 0` are exactly `1 − λ₁^{k+1} + c (λ₂^{k+1} − λ₁^{k+1})`, `c ∈ ℝ`; for
`c ≠ 0` they are unbounded, so violate (2.17). -/
theorem prop_3_6_all_solutions {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (p : ℕ → ℝ) :
    (IRFEq β κ (fun _ => 1) p ↔ ∃ c : ℝ, p = fun k => p36 β κ k + c * hom β κ k) ∧
      ∀ c : ℝ, c ≠ 0 → ¬ Tendsto (fun k => p36 β κ k + c * hom β κ k) atTop (𝓝 1) := by
  refine ⟨irfEq_iff_exists hβ hκ (p36_irfEq hβ hκ), fun c hc ht => ?_⟩
  exact (irfEq_unbounded_family hβ hκ (p36_irfEq hβ hκ)
    (bounded_of_tendsto (p36_tendsto hβ hκ)) hc).2 (bounded_of_tendsto ht)

/-- Woodford (2003), (B.19), p. 664: with `p̃_k + ỹ_k = 1` (from `log 𝒴 = log P + log Y`), the
output response is `ỹ_k = 1 − p̃_k = λ^{k+1}`. -/
theorem y36_eq (β κ : ℝ) (k : ℕ) : y36 β κ k = 1 - p36 β κ k := by
  unfold y36 p36; ring

/-- Woodford (2003), p. 191: output rises on impact by `ỹ_0 = λ`, less than proportionally to
the unit increase in nominal spending: `0 < ỹ_0 = λ < 1`. -/
theorem y36_zero {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    y36 β κ 0 = lam1 β κ ∧ 0 < y36 β κ 0 ∧ y36 β κ 0 < 1 := by
  have h0 := lam1_pos hβ hκ
  have h1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have e : y36 β κ 0 = lam1 β κ := by simp [y36]
  rw [e]
  exact ⟨rfl, h0, h1⟩

/-- Woodford (2003), p. 191: output then decays monotonically back to its original level:
`ỹ_k > 0`, `ỹ` strictly decreasing, `ỹ_k → 0`. -/
theorem y36_decay {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    (∀ k, 0 < y36 β κ k) ∧ StrictAnti (y36 β κ) ∧ Tendsto (y36 β κ) atTop (𝓝 0) := by
  have h0 := lam1_pos hβ hκ
  have h1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  refine ⟨fun k => pow_pos h0 _, ?_, ?_⟩
  · refine strictAnti_nat_of_succ_lt fun k => ?_
    unfold y36
    exact pow_lt_pow_right_of_lt_one₀ h0 h1 (by omega)
  · exact (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).comp (tendsto_add_atTop_nat 1)

/-- Woodford (2003), p. 191: the log price level rises monotonically towards the new long-run
level: `p̃` is strictly increasing with `0 < p̃_k < 1`. -/
theorem p36_rise {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    StrictMono (p36 β κ) ∧ ∀ k, 0 < p36 β κ k ∧ p36 β κ k < 1 := by
  obtain ⟨hpos, hanti, -⟩ := y36_decay hβ hκ
  have h1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have h0 := lam1_pos hβ hκ
  refine ⟨fun a b hab => ?_, fun k => ⟨?_, ?_⟩⟩
  · have := hanti hab
    rw [y36_eq, y36_eq] at this
    linarith
  · unfold p36
    have : lam1 β κ ^ (k + 1) < 1 := pow_lt_one₀ h0.le h1 (by omega)
    linarith
  · have := hpos k
    rw [y36_eq] at this
    linarith

/-! ### The stochastic model: (2.12) in price-level form, for any expectation system -/

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (2.12), p. 187, written as on p. 189 with the identities
`π_t ≡ log P_t − log P_{t−1}` and `Ŷ_t − Ŷ_tⁿ = log 𝒴_t − log P_t − log Y_tⁿ = x_t − log P_t`,
where `x_t ≡ log 𝒴_t − log Y_tⁿ` (log nominal spending net of log natural output):
`π_t = κ (x_t − log P_t) + β E_t π_{t+1}` at every date `t ≥ 0`. -/
def NKPC (β κ : ℝ) (pm1 : Ω → ℝ) (x p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t - prev pm1 p t = κ • (x t - p t) + β • 𝔼.E t (p (t + 1) - prev pm1 p (t + 1))

/-- Woodford (2003), App. B.3, pp. 660–661 and App. B.5, p. 663: the solution class. Expected
future log prices grow at most linearly, `|E_t log P_{t+j}| ≤ A + B (t + j)` (the precise
form of "`log P` difference-stationary"; it contains every solution with a stationary
(bounded) output gap, `linGrowth_of_gap`). -/
def LinGrowth (p : ℕ → Ω → ℝ) : Prop :=
  ∃ A B : ℝ, ∀ t j ω, |𝔼.E t (p (t + j)) ω| ≤ A + B * ((t : ℝ) + j)

/-- Woodford (2003), App. B.5, (B.21): for adapted `log P`, (2.12) is the second-order equation
`β E_t log P_{t+1} − (1 + β + κ) log P_t + log P_{t−1} = −κ x_t`. -/
theorem nkpc_iff_second_order {β κ : ℝ} {pm1 : Ω → ℝ} {x p : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p) :
    NKPC 𝔼 β κ pm1 x p ↔
      ∀ t, β • 𝔼.E t (p (t + 1)) - (1 + β + κ) • p t + prev pm1 p t = (-κ) • x t := by
  refine forall_congr' fun t => ?_
  rw [prev_succ, map_sub, hpa t]
  constructor
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  · intro h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith

omit 𝔼 in
/-- Woodford (2003), p. 189: the lagged price level is linear in the path. -/
theorem prev_sub (pm1 : Ω → ℝ) (p q : ℕ → Ω → ℝ) (t : ℕ) :
    prev pm1 p t - prev pm1 q t = prev 0 (fun s => p s - q s) t := by
  cases t <;> simp

/-- Woodford (2003), p. 189: the lagged price level is known at `t` when the price process is
adapted and the inherited level is known at date 0. -/
theorem prev_adapted {pm1 : Ω → ℝ} {p : ℕ → Ω → ℝ} (hpm1 : 𝔼.E 0 pm1 = pm1)
    (hpa : 𝔼.Adapted p) (t : ℕ) : 𝔼.E t (prev pm1 p t) = prev pm1 p t := by
  cases t with
  | zero => exact hpm1
  | succ t => exact ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) (hpa t)

/-- Woodford (2003), App. B.3, pp. 660–661 (the argument used again in App. B.5): **uniqueness**.
Two adapted solutions of (2.12) with the same inherited price level, both in the
linear-growth class, coincide. With `e_t = d_t − λ₁ d_{t−1}` for the difference `d`,
`E_t e_{t+j} = λ₂^j e_t`, which is incompatible with linear growth unless `e = 0`. -/
theorem nkpc_unique {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ} {x p q : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ pm1 x p) (hq : NKPC 𝔼 β κ pm1 x q) (hpa : 𝔼.Adapted p)
    (hqa : 𝔼.Adapted q) (hpg : LinGrowth 𝔼 p) (hqg : LinGrowth 𝔼 q) : p = q := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have h0 := lam1_pos hβ hκ
  have e1 := beta_mul_sum (c := κ) hβ
  have e2 := beta_mul_prod hβ hκ
  have h20 : lam2 β κ ≠ 0 := by linarith
  set l1 := lam1 β κ
  set l2 := lam2 β κ
  set d : ℕ → Ω → ℝ := fun t => p t - q t with hd
  have hda : 𝔼.Adapted d := fun t => by simp only [hd, map_sub, hpa t, hqa t]
  have hp2 := (nkpc_iff_second_order 𝔼 hpa).1 hp
  have hq2 := (nkpc_iff_second_order 𝔼 hqa).1 hq
  have hhom : ∀ t ω, β * 𝔼.E t (d (t + 1)) ω - (1 + β + κ) * d t ω + prev 0 d t ω = 0 := by
    intro t ω
    have a := congrFun (hp2 t) ω
    have b := congrFun (hq2 t) ω
    have c := congrFun (prev_sub pm1 p q t) ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a b c
    have hE : 𝔼.E t (d (t + 1)) ω = 𝔼.E t (p (t + 1)) ω - 𝔼.E t (q (t + 1)) ω := by
      simp [hd, map_sub]
    rw [hE, ← c]
    simp only [hd, Pi.sub_apply]
    linarith
  set e : ℕ → Ω → ℝ := fun t => d t - l1 • prev 0 d t with he
  have hEe' : ∀ t s ω, 𝔼.E t (e (s + 1)) ω = 𝔼.E t (d (s + 1)) ω - l1 * 𝔼.E t (d s) ω := by
    intro t s ω
    simp only [he, prev_succ, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hEe : ∀ t ω, 𝔼.E t (e (t + 1)) ω = 𝔼.E t (d (t + 1)) ω - l1 * d t ω := by
    intro t ω
    rw [hEe', hda t]
  have hrec : ∀ t, e t = l2⁻¹ • 𝔼.E t (e (t + 1)) := by
    intro t
    funext ω
    have hh := hhom t ω
    have key : β * (l2 * (d t ω - l1 * prev 0 d t ω)) =
        β * (𝔼.E t (d (t + 1)) ω - l1 * d t ω) := by
      linear_combination d t ω * e1 - prev 0 d t ω * e2 - hh
    have key' := mul_left_cancel₀ hβ.ne' key
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hEe t ω, ← key']
    simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨A₁, B₁, hb₁⟩ := hpg
  obtain ⟨A₂, B₂, hb₂⟩ := hqg
  set A := |A₁| + |A₂|
  set B := |B₁| + |B₂|
  have hdb : ∀ t j ω, |𝔼.E t (d (t + j)) ω| ≤ A + B * ((t : ℝ) + j) := by
    intro t j ω
    have hE : 𝔼.E t (d (t + j)) ω = 𝔼.E t (p (t + j)) ω - 𝔼.E t (q (t + j)) ω := by
      simp [hd, map_sub]
    rw [hE]
    have u₁ := hb₁ t j ω
    have u₂ := hb₂ t j ω
    have ht : (0 : ℝ) ≤ (t : ℝ) + j := by positivity
    have v₁ : B₁ * ((t : ℝ) + j) ≤ |B₁| * ((t : ℝ) + j) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) ht
    have v₂ : B₂ * ((t : ℝ) + j) ≤ |B₂| * ((t : ℝ) + j) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) ht
    calc |𝔼.E t (p (t + j)) ω - 𝔼.E t (q (t + j)) ω|
        ≤ |𝔼.E t (p (t + j)) ω| + |𝔼.E t (q (t + j)) ω| := abs_sub _ _
      _ ≤ A + B * ((t : ℝ) + j) := by
        simp only [A, B]; nlinarith [le_abs_self A₁, le_abs_self A₂]
  have he0 : ∀ t ω, e t ω = 0 := by
    intro t ω
    have hr : |l2⁻¹| < 1 := by
      rw [abs_of_pos (inv_pos.2 (by linarith))]; exact inv_lt_one_of_one_lt₀ h2
    set r := l2⁻¹ with hrdef
    have hr0 : 0 ≤ r := inv_nonneg.2 (by linarith)
    have hbound : ∀ k : ℕ, |e t ω| ≤
        r * (1 + l1) * ((A + B * ((t : ℝ) + 1)) * r ^ k + B * ((k : ℝ) * r ^ k)) := by
      intro k
      have hit := congrFun (𝔼.forward_iterate hrec t (k + 1)) ω
      simp only [Pi.smul_apply, smul_eq_mul] at hit
      rw [hit, show t + (k + 1) = t + k + 1 by omega, hEe']
      have b1 := hdb t (k + 1) ω
      have b2 := hdb t k ω
      rw [show t + (k + 1) = t + k + 1 by omega] at b1
      push_cast at b1 b2
      have hB : 0 ≤ B := by positivity
      have hA : 0 ≤ A + B * ((t : ℝ) + k) := (abs_nonneg _).trans b2
      rw [abs_mul, abs_pow, abs_of_nonneg hr0]
      have hsub : |𝔼.E t (d (t + k + 1)) ω - l1 * 𝔼.E t (d (t + k)) ω| ≤
          (1 + l1) * (A + B * ((t : ℝ) + 1) + B * k) := by
        calc |𝔼.E t (d (t + k + 1)) ω - l1 * 𝔼.E t (d (t + k)) ω|
            ≤ |𝔼.E t (d (t + k + 1)) ω| + |l1 * 𝔼.E t (d (t + k)) ω| := abs_sub _ _
          _ ≤ (A + B * ((t : ℝ) + (k + 1))) + l1 * (A + B * ((t : ℝ) + k)) := by
            rw [abs_mul, abs_of_pos h0]
            exact add_le_add b1 (mul_le_mul_of_nonneg_left b2 h0.le)
          _ ≤ (1 + l1) * (A + B * ((t : ℝ) + 1) + B * k) := by nlinarith
      calc r ^ (k + 1) * |𝔼.E t (d (t + k + 1)) ω - l1 * 𝔼.E t (d (t + k)) ω|
          ≤ r ^ (k + 1) * ((1 + l1) * (A + B * ((t : ℝ) + 1) + B * k)) :=
            mul_le_mul_of_nonneg_left hsub (pow_nonneg hr0 _)
        _ = _ := by ring
    have hlim : Tendsto (fun k : ℕ =>
        r * (1 + l1) * ((A + B * ((t : ℝ) + 1)) * r ^ k + B * ((k : ℝ) * r ^ k))) atTop
        (𝓝 0) := by
      have t1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 (by rwa [abs_of_nonneg hr0] at hr))
      have t2 := tendsto_self_mul_const_pow_of_abs_lt_one hr
      simpa using ((t1.const_mul (A + B * ((t : ℝ) + 1))).add (t2.const_mul B)).const_mul
        (r * (1 + l1))
    have := ge_of_tendsto' hlim hbound
    exact abs_nonpos_iff.1 this
  have hd0 : ∀ t, d t = 0 := by
    intro t
    induction t with
    | zero =>
      funext ω
      have := he0 0 ω
      simpa [he] using this
    | succ t ih =>
      funext ω
      have := he0 (t + 1) ω
      simp only [he, prev_succ, ih, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        mul_zero, sub_zero] at this
      simpa using this
  funext t ω
  have := congrFun (hd0 t) ω
  simp only [hd, Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

omit 𝔼 in
/-- Woodford (2003), p. 189: forcing with increments bounded by `M` grows at most linearly,
`|x_s| ≤ |B₀| + s|M|`. -/
theorem abs_le_of_increments {x : ℕ → Ω → ℝ} {M B₀ : ℝ}
    (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) (hx0 : ∀ ω, |x 0 ω| ≤ B₀) (s : ℕ) (ω : Ω) :
    |x s ω| ≤ |B₀| + s * |M| := by
  induction s with
  | zero => simpa using (hx0 ω).trans (le_abs_self _)
  | succ s ih =>
    have h1 : |x (s + 1) ω| ≤ |x (s + 1) ω - x s ω| + |x s ω| := by
      have := abs_add_le (x (s + 1) ω - x s ω) (x s ω)
      simpa using this
    have h2 := (hx s ω).trans (le_abs_self M)
    push_cast
    linarith

/-- Woodford (2003), p. 190 ("deviations of output from trend are stationary") and App. B.3,
p. 661: when nominal spending (net of natural output) has bounded increments, every price
process with a bounded output gap `x_t − log P_t` is in the linear-growth class. -/
theorem linGrowth_of_gap {x p : ℕ → Ω → ℝ} {M B₀ : ℝ}
    (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) (hx0 : ∀ ω, |x 0 ω| ≤ B₀)
    (hg : BoundedProc (fun t => x t - p t)) : LinGrowth 𝔼 p := by
  obtain ⟨K, hK⟩ := hg
  refine ⟨|B₀| + K, |M|, fun t j ω => ?_⟩
  have e : p (t + j) = x (t + j) - (x (t + j) - p (t + j)) := by abel
  rw [e, map_sub, Pi.sub_apply]
  have b1 : |𝔼.E t (x (t + j)) ω| ≤ |B₀| + ((t + j : ℕ) : ℝ) * |M| :=
    𝔼.abs_E_le (fun ω' => abs_le_of_increments hx hx0 (t + j) ω') t ω
  have b2 : |𝔼.E t (x (t + j) - p (t + j)) ω| ≤ K := 𝔼.abs_E_le (fun ω' => hK (t + j) ω') t ω
  push_cast at b1
  calc |𝔼.E t (x (t + j)) ω - 𝔼.E t (x (t + j) - p (t + j)) ω|
      ≤ |𝔼.E t (x (t + j)) ω| + |𝔼.E t (x (t + j) - p (t + j)) ω| := abs_sub _ _
    _ ≤ |B₀| + K + |M| * ((t : ℝ) + j) := by nlinarith

/-! ### Existence: the forward solution of App. B.5 -/

omit 𝔼 in
/-- Woodford (2003), App. B.5, p. 664: the equilibrium price recursion
`log P_t = λ₁ log P_{t−1} + (1 − λ₁) x_t + v_t`, `v` the forward part. -/
def eqmPrice (l : ℝ) (pm1 : Ω → ℝ) (x v : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => l • pm1 + (1 - l) • x 0 + v 0
  | t + 1 => l • eqmPrice l pm1 x v t + (1 - l) • x (t + 1) + v (t + 1)

omit 𝔼 in
/-- Woodford (2003), App. B.5, p. 664: the recursion in lag form. -/
theorem eqmPrice_eq (l : ℝ) (pm1 : Ω → ℝ) (x v : ℕ → Ω → ℝ) (t : ℕ) :
    eqmPrice l pm1 x v t = l • prev pm1 (eqmPrice l pm1 x v) t + (1 - l) • x t + v t := by
  cases t <;> rfl

/-- Woodford (2003), App. B.5, p. 663: the forcing of the forward part,
`λ₂⁻¹(1 − λ₁) E_t (x_{t+1} − x_t)` (expected nominal-spending growth). -/
noncomputable def fwdForcing (β κ : ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => ((lam2 β κ)⁻¹ * (1 - lam1 β κ)) • 𝔼.E t (x (t + 1) - x t)

/-- Woodford (2003), App. B.5, pp. 663–664: the equilibrium price process,
`log P_t = λ₁ log P_{t−1} + (1 − λ₁) x_t + v_t` with
`v_t = ∑_{j ≥ 0} λ₂^{−j} E_t[λ₂⁻¹(1 − λ₁)(x_{t+j+1} − x_{t+j})]`. -/
noncomputable def eqmP (β κ : ℝ) (pm1 : Ω → ℝ) (x : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  eqmPrice (lam1 β κ) pm1 x (𝔼.forwardSeries (lam2 β κ)⁻¹ (fwdForcing 𝔼 β κ x))

/-- Woodford (2003), App. B.5: the forcing of the forward part is bounded. -/
theorem fwdForcing_bound {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {x : ℕ → Ω → ℝ} {M : ℝ}
    (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |fwdForcing 𝔼 β κ x t ω| ≤ ((lam2 β κ)⁻¹ * (1 - lam1 β κ)) * M := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have h1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have hc : 0 ≤ (lam2 β κ)⁻¹ * (1 - lam1 β κ) :=
    mul_nonneg (inv_nonneg.2 (by linarith)) (by linarith)
  simp only [fwdForcing, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => hx t ω') t ω) hc

/-- Woodford (2003), App. B.5: the forcing of the forward part is adapted. -/
theorem fwdForcing_adapted (β κ : ℝ) (x : ℕ → Ω → ℝ) : 𝔼.Adapted (fwdForcing 𝔼 β κ x) := by
  intro t
  simp only [fwdForcing, map_smul, 𝔼.E_E_self]

/-- Woodford (2003), App. B.5: the equilibrium price process is adapted. -/
theorem eqmP_adapted {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ} {x : ℕ → Ω → ℝ}
    {M : ℝ} (hpm1 : 𝔼.E 0 pm1 = pm1) (hxa : 𝔼.Adapted x)
    (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) : 𝔼.Adapted (eqmP 𝔼 β κ pm1 x) := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have hva := 𝔼.forwardSeries_adapted (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ lam2 β κ))
    (inv_lt_one_of_one_lt₀ h2) (fwdForcing_bound 𝔼 hβ hκ hx)
  intro t
  induction t with
  | zero =>
    simp only [eqmP, eqmPrice, map_add, map_smul, hpm1, hxa 0, hva 0]
  | succ t ih =>
    simp only [eqmP, eqmPrice] at ih ⊢
    rw [map_add, map_add, map_smul, map_smul, ForwardSolution.E_of_known 𝔼 (Nat.le_succ t) ih,
      hxa (t + 1), hva (t + 1)]

/-- Woodford (2003), App. B.5, pp. 663–664: **existence**. The forward-solution price process
solves (2.12). -/
theorem eqmP_nkpc {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ} {x : ℕ → Ω → ℝ}
    {M : ℝ} (hpm1 : 𝔼.E 0 pm1 = pm1) (hxa : 𝔼.Adapted x)
    (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) : NKPC 𝔼 β κ pm1 x (eqmP 𝔼 β κ pm1 x) := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have e1 := beta_mul_sum (c := κ) hβ
  have e2 := beta_mul_prod hβ hκ
  have hk := kappa_eq hβ hκ
  have hpa := eqmP_adapted 𝔼 hβ hκ hpm1 hxa hx
  have hv := 𝔼.forwardSeries_solves (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ lam2 β κ))
    (inv_lt_one_of_one_lt₀ h2) (fwdForcing_bound 𝔼 hβ hκ hx) (fwdForcing_adapted 𝔼 β κ x)
  rw [nkpc_iff_second_order 𝔼 hpa]
  intro t
  funext ω
  have h20 : lam2 β κ ≠ 0 := by linarith
  set v := 𝔼.forwardSeries (lam2 β κ)⁻¹ (fwdForcing 𝔼 β κ x)
  set P := eqmP 𝔼 β κ pm1 x
  have f3 : P t ω = lam1 β κ * prev pm1 P t ω + (1 - lam1 β κ) * x t ω + v t ω := by
    have := congrFun (eqmPrice_eq (lam1 β κ) pm1 x v t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have f1 : 𝔼.E t (P (t + 1)) ω =
      lam1 β κ * P t ω + (1 - lam1 β κ) * 𝔼.E t (x (t + 1)) ω + 𝔼.E t (v (t + 1)) ω := by
    have e : P (t + 1) = lam1 β κ • P t + (1 - lam1 β κ) • x (t + 1) + v (t + 1) := rfl
    rw [e]
    simp only [map_add, map_smul, hpa t, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have f2 : lam2 β κ * v t ω =
      𝔼.E t (v (t + 1)) ω + (1 - lam1 β κ) * (𝔼.E t (x (t + 1)) ω - x t ω) := by
    have := congrFun (hv t) ω
    simp only [fwdForcing, map_sub, hxa t, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.sub_apply] at this
    rw [this]
    field_simp
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination β * f1 - β * f2 - β * lam2 β κ * f3 + P t ω * e1 -
    prev pm1 P t ω * e2 + x t ω * hk

/-- Woodford (2003), p. 190: the forward-solution equilibrium has a stationary (bounded) output
gap `x_t − log P_t`. -/
theorem eqmP_gap_bounded {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ} {x : ℕ → Ω → ℝ}
    {M B₀ B₁ : ℝ} (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) (hx0 : ∀ ω, |x 0 ω| ≤ B₀)
    (hpm : ∀ ω, |pm1 ω| ≤ B₁) : BoundedProc (fun t => x t - eqmP 𝔼 β κ pm1 x t) := by
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have h1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  have h0 := lam1_pos hβ hκ
  obtain ⟨V, hV⟩ := 𝔼.forwardSeries_bounded
    (inv_nonneg.2 (by linarith : (0 : ℝ) ≤ lam2 β κ)) (inv_lt_one_of_one_lt₀ h2)
    (fwdForcing_bound 𝔼 hβ hκ hx)
  set l1 := lam1 β κ
  set v := 𝔼.forwardSeries (lam2 β κ)⁻¹ (fwdForcing 𝔼 β κ x)
  set P := eqmP 𝔼 β κ pm1 x
  set W := (l1 * |M| + |V|) / (1 - l1)
  have hl : 1 - l1 ≠ 0 := by linarith
  have hW : (1 - l1) * W = l1 * |M| + |V| := by
    simp only [W]; field_simp
  have hW0 : 0 ≤ W := div_nonneg (by positivity) (by linarith)
  set K := l1 * (|B₀| + |B₁|) + |V| + W
  have hR : 0 ≤ l1 * (|B₀| + |B₁|) + |V| := by positivity
  have hK : l1 * |M| + |V| ≤ (1 - l1) * K := by
    have : (1 - l1) * K = (1 - l1) * (l1 * (|B₀| + |B₁|) + |V|) + (1 - l1) * W := by ring
    rw [this, hW]
    nlinarith
  have hvb : ∀ t ω, |v t ω| ≤ |V| := fun t ω => (hV t ω).trans (le_abs_self V)
  have gform : ∀ t ω, x t ω - P t ω = l1 * (x t ω - prev pm1 P t ω) - v t ω := by
    intro t ω
    have := congrFun (eqmPrice_eq l1 pm1 x v t) ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    have f : P t ω = l1 * prev pm1 P t ω + (1 - l1) * x t ω + v t ω := this
    rw [f]
    ring
  refine ⟨K, fun t => ?_⟩
  induction t with
  | zero =>
    intro ω
    change |x 0 ω - P 0 ω| ≤ K
    rw [gform]
    simp only [prev_zero]
    calc |l1 * (x 0 ω - pm1 ω) - v 0 ω| ≤ |l1 * (x 0 ω - pm1 ω)| + |v 0 ω| := abs_sub _ _
      _ ≤ l1 * (|B₀| + |B₁|) + |V| := by
        rw [abs_mul, abs_of_pos h0]
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ h0.le) (hvb 0 ω)
        exact (abs_sub _ _).trans (add_le_add ((hx0 ω).trans (le_abs_self _))
          ((hpm ω).trans (le_abs_self _)))
      _ ≤ K := by simp only [K]; linarith
  | succ t ih =>
    intro ω
    have ih' : ∀ ω, |x t ω - P t ω| ≤ K := ih
    change |x (t + 1) ω - P (t + 1) ω| ≤ K
    rw [gform]
    simp only [prev_succ]
    have e : x (t + 1) ω - P t ω = (x (t + 1) ω - x t ω) + (x t ω - P t ω) := by ring
    rw [e]
    calc |l1 * ((x (t + 1) ω - x t ω) + (x t ω - P t ω)) - v (t + 1) ω|
        ≤ |l1 * ((x (t + 1) ω - x t ω) + (x t ω - P t ω))| + |v (t + 1) ω| := abs_sub _ _
      _ ≤ l1 * (|M| + K) + |V| := by
        rw [abs_mul, abs_of_pos h0]
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ h0.le) (hvb (t + 1) ω)
        exact (abs_add_le _ _).trans (add_le_add ((hx t ω).trans (le_abs_self _)) (ih' ω))
      _ ≤ K := by nlinarith

/-- Woodford (2003), App. B.5: the forward-solution equilibrium belongs to the
linear-growth class. -/
theorem eqmP_linGrowth {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ} {x : ℕ → Ω → ℝ}
    {M B₀ B₁ : ℝ} (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) (hx0 : ∀ ω, |x 0 ω| ≤ B₀)
    (hpm : ∀ ω, |pm1 ω| ≤ B₁) : LinGrowth 𝔼 (eqmP 𝔼 β κ pm1 x) :=
  linGrowth_of_gap 𝔼 hx hx0 (eqmP_gap_bounded 𝔼 hβ hκ hx hx0 hpm)

/-- Woodford (2003), §2.3 pp. 188–190 and App. B.5: **existence and uniqueness** of the
equilibrium for an arbitrary expectation system. If nominal spending net of natural output
is adapted with bounded increments (as under (2.15) with bounded shocks), (2.12) has exactly
one adapted solution in the linear-growth class. -/
theorem nkpc_existsUnique {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ}
    {x : ℕ → Ω → ℝ} {M B₀ B₁ : ℝ} (hpm1 : 𝔼.E 0 pm1 = pm1) (hxa : 𝔼.Adapted x)
    (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) (hx0 : ∀ ω, |x 0 ω| ≤ B₀)
    (hpm : ∀ ω, |pm1 ω| ≤ B₁) :
    ∃! p, 𝔼.Adapted p ∧ NKPC 𝔼 β κ pm1 x p ∧ LinGrowth 𝔼 p :=
  ⟨eqmP 𝔼 β κ pm1 x, ⟨eqmP_adapted 𝔼 hβ hκ hpm1 hxa hx, eqmP_nkpc 𝔼 hβ hκ hpm1 hxa hx,
    eqmP_linGrowth 𝔼 hβ hκ hx hx0 hpm⟩, fun _ hq => nkpc_unique 𝔼 hβ hκ hq.2.1
      (eqmP_nkpc 𝔼 hβ hκ hpm1 hxa hx) hq.1 (eqmP_adapted 𝔼 hβ hκ hpm1 hxa hx) hq.2.2
      (eqmP_linGrowth 𝔼 hβ hκ hx hx0 hpm)⟩

/-- Woodford (2003), p. 190: the same equilibrium is the unique one with a stationary
(bounded) output gap. -/
theorem nkpc_existsUnique_gap {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ}
    {x : ℕ → Ω → ℝ} {M B₀ B₁ : ℝ} (hpm1 : 𝔼.E 0 pm1 = pm1) (hxa : 𝔼.Adapted x)
    (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M) (hx0 : ∀ ω, |x 0 ω| ≤ B₀)
    (hpm : ∀ ω, |pm1 ω| ≤ B₁) :
    ∃! p, 𝔼.Adapted p ∧ NKPC 𝔼 β κ pm1 x p ∧ BoundedProc (fun t => x t - p t) :=
  ⟨eqmP 𝔼 β κ pm1 x, ⟨eqmP_adapted 𝔼 hβ hκ hpm1 hxa hx, eqmP_nkpc 𝔼 hβ hκ hpm1 hxa hx,
    eqmP_gap_bounded 𝔼 hβ hκ hx hx0 hpm⟩, fun _ hq => nkpc_unique 𝔼 hβ hκ hq.2.1
      (eqmP_nkpc 𝔼 hβ hκ hpm1 hxa hx) hq.1 (eqmP_adapted 𝔼 hβ hκ hpm1 hxa hx)
      (linGrowth_of_gap 𝔼 hx hx0 hq.2.2) (eqmP_linGrowth 𝔼 hβ hκ hx hx0 hpm)⟩

/-! ### Non-uniqueness outside the solution class -/

/-- Woodford (2003), App. B.3, p. 661 (used again in App. B.5): adding the deterministic path
`c (λ₂^{t+1} − λ₁^{t+1})` to an adapted solution of (2.12) gives another adapted solution
(with the same inherited price level). -/
theorem nkpc_add_hom {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ} {x p : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ pm1 x p) (hpa : 𝔼.Adapted p) (c : ℝ) :
    NKPC 𝔼 β κ pm1 x (fun t => p t + fun _ => c * hom β κ t) ∧
      𝔼.Adapted (fun t => p t + fun _ => c * hom β κ t) := by
  refine ⟨fun t => ?_, fun t => by simp only [map_add, hpa t, 𝔼.const]⟩
  have hl : prev pm1 (fun t => p t + fun _ => c * hom β κ t) t =
      prev pm1 p t + fun _ => c * prev 0 (hom β κ) t := by
    cases t with
    | zero => funext ω; simp
    | succ t => rfl
  have hsplit : (p (t + 1) + fun _ => c * hom β κ (t + 1)) - (p t + fun _ => c * hom β κ t) =
      (p (t + 1) - p t) + fun _ => c * hom β κ (t + 1) - c * hom β κ t := by
    funext ω; simp only [Pi.add_apply, Pi.sub_apply]; ring
  have a := hp t
  have b := hom_irfEq hβ hκ t
  simp only [prev_succ] at a ⊢
  rw [hl, hsplit, map_add, 𝔼.const]
  funext ω
  have a' := congrFun a ω
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at a' ⊢
  linear_combination a' + c * b

/-- Woodford (2003), App. B.3, p. 661 and App. B.5: **non-uniqueness outside the class**. Next to
the equilibrium `p` in the linear-growth class, every `p + c (λ₂^{t+1} − λ₁^{t+1})`, `c ≠ 0`,
is another adapted solution of (2.12); none of them is in the linear-growth class
(expected prices explode like `λ₂^j`), and (for spending with bounded increments) their
output gaps are unbounded. -/
theorem nkpc_not_unique [Nonempty Ω] {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ}
    {x p : ℕ → Ω → ℝ} {M B₀ : ℝ} (hx : ∀ t ω, |x (t + 1) ω - x t ω| ≤ M)
    (hx0 : ∀ ω, |x 0 ω| ≤ B₀) (hp : NKPC 𝔼 β κ pm1 x p) (hpa : 𝔼.Adapted p)
    (hpg : LinGrowth 𝔼 p) {c : ℝ} (hc : c ≠ 0) :
    NKPC 𝔼 β κ pm1 x (fun t => p t + fun _ => c * hom β κ t) ∧
      𝔼.Adapted (fun t => p t + fun _ => c * hom β κ t) ∧
      ¬ LinGrowth 𝔼 (fun t => p t + fun _ => c * hom β κ t) ∧
      ¬ BoundedProc (fun t => x t - (p t + fun _ => c * hom β κ t)) := by
  obtain ⟨h1, h2⟩ := nkpc_add_hom 𝔼 hβ hκ hp hpa c
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hnot : ¬ LinGrowth 𝔼 (fun t => p t + fun _ => c * hom β κ t) := by
    intro hg
    have := nkpc_unique 𝔼 hβ hκ h1 hp h2 hpa hg hpg
    have e := congrFun (congrFun this 0) ω
    simp only [Pi.add_apply, add_eq_left, mul_eq_zero] at e
    rcases e with e | e
    · exact hc e
    · exact hom_zero_ne hβ hκ e
  exact ⟨h1, h2, hnot, fun hb => hnot (linGrowth_of_gap 𝔼 hx hx0 hb)⟩

/-- Woodford (2003), App. B.3, p. 661: without the growth restriction there is a continuum of
adapted solutions of (2.12): the solution set is uncountable as soon as it is nonempty. -/
theorem nkpc_solutions_not_countable [Nonempty Ω] {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    {pm1 : Ω → ℝ} {x p : ℕ → Ω → ℝ} (hp : NKPC 𝔼 β κ pm1 x p) (hpa : 𝔼.Adapted p) :
    ¬ {q | 𝔼.Adapted q ∧ NKPC 𝔼 β κ pm1 x q}.Countable := by
  intro hcount
  let f : ℝ → ℕ → Ω → ℝ := fun c t => p t + fun _ => c * hom β κ t
  have hmaps : Set.MapsTo f Set.univ {q | 𝔼.Adapted q ∧ NKPC 𝔼 β κ pm1 x q} := by
    intro c _
    obtain ⟨h1, h2⟩ := nkpc_add_hom 𝔼 hβ hκ hp hpa c
    exact ⟨h2, h1⟩
  have hinj : Set.InjOn f Set.univ := by
    intro c₁ _ c₂ _ h
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    have e := congrFun (congrFun h 0) ω
    simp only [f, Pi.add_apply, add_right_inj] at e
    exact mul_right_cancel₀ (hom_zero_ne hβ hκ) e
  exact Cardinal.not_countable_real (hmaps.countable_of_injOn hinj hcount)

/-! ### Impulse responses as responses of the stochastic equilibrium -/

omit 𝔼 in
/-- Woodford (2003), pp. 189–190: the path `f(r − s) ε` from date `s` on (zero before) by which
a date-`s` news shock `ε` moves a process; `f = Ỹ` for nominal spending, `f = p̃` for prices. -/
def shockPath (s : ℕ) (f : ℕ → ℝ) (ε : Ω → ℝ) (r : ℕ) : Ω → ℝ :=
  if s ≤ r then f (r - s) • ε else 0

omit 𝔼 in
/-- Woodford (2003), (2.18), p. 190: the lag of a shock path, `p̃_{r−s−1} ε` (zero up to `s`). -/
theorem prev_shockPath (s : ℕ) (f : ℕ → ℝ) (ε : Ω → ℝ) (r : ℕ) :
    prev 0 (shockPath s f ε) r = if s ≤ r then prev 0 f (r - s) • ε else 0 := by
  cases r with
  | zero =>
    by_cases h : s ≤ 0
    · have : s = 0 := by omega
      subst this
      simp
    · simp [h]
  | succ r =>
    rw [prev_succ]
    by_cases h : s ≤ r
    · have h1 : s ≤ r + 1 := by omega
      simp only [shockPath, h, h1, ↓reduceIte]
      rw [show r + 1 - s = r - s + 1 by omega, prev_succ]
    · by_cases h' : s = r + 1
      · subst h'
        simp [shockPath]
      · have h1 : ¬ s ≤ r + 1 := by omega
        simp only [shockPath, h, h1, ↓reduceIte]

/-- Woodford (2003), pp. 189–190: **the impulse response is the response of the stochastic
equilibrium.** If `p̃` solves the generalised (2.16) (with `p̃_{−1} = 0`) for the nominal-spending
response `Ỹ`, then for a news shock `ε` revealed at date `s` (known at `s`, unforecastable
before `s`: `E_r ε = 0` for `r < s`), the path `p̃_{r−s} ε` solves (2.12) with forcing
`Ỹ_{r−s} ε` and inherited price level `0`. -/
theorem shock_nkpc {β κ : ℝ} {Y pt : ℕ → ℝ} (hirf : IRFEq β κ Y pt) {s : ℕ} {ε : Ω → ℝ}
    (hεs : 𝔼.E s ε = ε) (hunf : ∀ r < s, 𝔼.E r ε = 0) :
    NKPC 𝔼 β κ 0 (shockPath s Y ε) (shockPath s pt ε) := by
  intro r
  rw [prev_shockPath, prev_succ]
  by_cases h : s ≤ r
  · have h1 : s ≤ r + 1 := by omega
    simp only [shockPath, h, h1, ↓reduceIte]
    have hE : 𝔼.E r (pt (r - s + 1) • ε - pt (r - s) • ε) = (pt (r - s + 1) - pt (r - s)) • ε := by
      rw [← sub_smul, map_smul, ForwardSolution.E_of_known 𝔼 h hεs]
    rw [show r + 1 - s = r - s + 1 by omega, hE]
    funext ω
    have := hirf (r - s)
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ε ω * this
  · simp only [shockPath, h, ↓reduceIte, sub_zero, smul_zero, zero_add]
    by_cases h1 : s ≤ r + 1
    · simp only [h1, ↓reduceIte, map_smul, hunf r (by omega), smul_zero]
    · simp only [h1, ↓reduceIte, map_zero, smul_zero]

/-- Woodford (2003), p. 189: a shock path is adapted. -/
theorem shock_adapted {s : ℕ} {f : ℕ → ℝ} {ε : Ω → ℝ} (hεs : 𝔼.E s ε = ε) :
    𝔼.Adapted (shockPath s f ε) := by
  intro r
  by_cases h : s ≤ r
  · simp only [shockPath, h, ↓reduceIte, map_smul, ForwardSolution.E_of_known 𝔼 h hεs]
  · simp only [shockPath, h, ↓reduceIte, map_zero]

omit 𝔼 in
/-- Woodford (2003), p. 190: a shock path with bounded `f` and bounded `ε` is bounded. -/
theorem shock_bounded {s : ℕ} {f : ℕ → ℝ} {ε : Ω → ℝ} (hf : ∃ M, ∀ k, |f k| ≤ M)
    (hε : ∃ M, ∀ ω, |ε ω| ≤ M) : BoundedProc (shockPath s f ε) := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Me, hMe⟩ := hε
  refine ⟨|Mf| * |Me|, fun r ω => ?_⟩
  by_cases h : s ≤ r
  · simp only [shockPath, h, ↓reduceIte, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul ((hMf _).trans (le_abs_self _)) ((hMe ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  · simp only [shockPath, h, ↓reduceIte, Pi.zero_apply, abs_zero]
    positivity

/-- Woodford (2003), App. B.5: a bounded process is in the linear-growth class. -/
theorem linGrowth_of_bounded {p : ℕ → Ω → ℝ} (hp : BoundedProc p) : LinGrowth 𝔼 p := by
  obtain ⟨M, hM⟩ := hp
  exact ⟨M, 0, fun t j ω => by simpa using 𝔼.abs_E_le (fun ω' => hM (t + j) ω') t ω⟩

/-- Woodford (2003), App. B.5: the linear-growth class is stable under adding a multiple of a
bounded process. -/
theorem linGrowth_add_smul {p P : ℕ → Ω → ℝ} (hp : LinGrowth 𝔼 p) (hP : BoundedProc P)
    (c : ℝ) : LinGrowth 𝔼 (fun t => p t + c • P t) := by
  obtain ⟨A, B, hAB⟩ := hp
  obtain ⟨M, hM⟩ := hP
  refine ⟨A + |c| * M, B, fun t j ω => ?_⟩
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := hAB t j ω
  have h2 : |𝔼.E t (P (t + j)) ω| ≤ M := 𝔼.abs_E_le (fun ω' => hM (t + j) ω') t ω
  calc |𝔼.E t (p (t + j)) ω + c * 𝔼.E t (P (t + j)) ω|
      ≤ |𝔼.E t (p (t + j)) ω| + |c| * |𝔼.E t (P (t + j)) ω| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ A + B * ((t : ℝ) + j) + |c| * M := by
        nlinarith [mul_le_mul_of_nonneg_left h2 (abs_nonneg c)]
    _ = A + |c| * M + B * ((t : ℝ) + j) := by ring

/-- Woodford (2003), p. 189: (2.12) is linear, so equilibria superpose: the response to the
forcing `x + c δ` is `p + c P`. -/
theorem nkpc_add_smul {β κ : ℝ} {pm1 : Ω → ℝ} {x p δ P : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ pm1 x p) (hP : NKPC 𝔼 β κ 0 δ P) (c : ℝ) :
    NKPC 𝔼 β κ pm1 (fun t => x t + c • δ t) (fun t => p t + c • P t) := by
  intro t
  have hl : prev pm1 (fun t => p t + c • P t) t = prev pm1 p t + c • prev 0 P t := by
    cases t with
    | zero => simp
    | succ t => rfl
  have a := hp t
  have b := hP t
  simp only [prev_succ] at a b ⊢
  rw [hl]
  funext ω
  have a' := congrFun a ω
  have b' := congrFun b ω
  simp only [map_add, map_sub, map_smul, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul] at a' b' ⊢
  linear_combination a' + c * b'

/-- Woodford (2003), pp. 189–190, (2.16)–(2.18) and App. B.5, in stochastic form: if `p` is the
equilibrium (adapted, linear growth) for the forcing `x`, then the unique equilibrium in that
solution class for the forcing `x + c Ỹ_{r−s} ε` shocked by date-`s` news `c ε` is
`p + c p̃_{r−s} ε`,
where `p̃` is the bounded solution of the generalised (2.16). -/
theorem shock_response {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ} {x p : ℕ → Ω → ℝ}
    (hp : NKPC 𝔼 β κ pm1 x p) (hpa : 𝔼.Adapted p) (hpg : LinGrowth 𝔼 p) {Y pt : ℕ → ℝ}
    (hirf : IRFEq β κ Y pt) (hptb : ∃ M, ∀ k, |pt k| ≤ M) {s : ℕ} {ε : Ω → ℝ}
    (hεs : 𝔼.E s ε = ε) (hunf : ∀ r < s, 𝔼.E r ε = 0) (hεb : ∃ M, ∀ ω, |ε ω| ≤ M) (c : ℝ)
    {q : ℕ → Ω → ℝ} (hq : NKPC 𝔼 β κ pm1 (fun t => x t + c • shockPath s Y ε t) q)
    (hqa : 𝔼.Adapted q) (hqg : LinGrowth 𝔼 q) :
    q = fun t => p t + c • shockPath s pt ε t := by
  refine nkpc_unique 𝔼 hβ hκ hq (nkpc_add_smul 𝔼 hp (shock_nkpc 𝔼 hirf hεs hunf) c) hqa
    (fun t => ?_) hqg (linGrowth_add_smul 𝔼 hpg (shock_bounded hptb hεb) c)
  simp only [map_add, map_smul, hpa t, shock_adapted 𝔼 hεs t]

/-- Woodford (2003), p. 189: `p̃_k = ∂E_t log P_{t+k}/∂ε_t`. In the shocked equilibrium the
date-`s` expectation of `log P_{s+k}` moves by exactly `c p̃_k ε`, and expectations held before
`s` do not move at all. -/
theorem shock_response_expect {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ}
    {x p : ℕ → Ω → ℝ} (hp : NKPC 𝔼 β κ pm1 x p) (hpa : 𝔼.Adapted p) (hpg : LinGrowth 𝔼 p)
    {Y pt : ℕ → ℝ} (hirf : IRFEq β κ Y pt) (hptb : ∃ M, ∀ k, |pt k| ≤ M) {s : ℕ}
    {ε : Ω → ℝ} (hεs : 𝔼.E s ε = ε) (hunf : ∀ r < s, 𝔼.E r ε = 0)
    (hεb : ∃ M, ∀ ω, |ε ω| ≤ M) (c : ℝ) {q : ℕ → Ω → ℝ}
    (hq : NKPC 𝔼 β κ pm1 (fun t => x t + c • shockPath s Y ε t) q) (hqa : 𝔼.Adapted q)
    (hqg : LinGrowth 𝔼 q) :
    (∀ k, 𝔼.E s (q (s + k)) = 𝔼.E s (p (s + k)) + (c * pt k) • ε) ∧
      (∀ r < s, ∀ j, 𝔼.E r (q j) = 𝔼.E r (p j)) ∧
      (∀ k, 𝔼.E s (x (s + k) + c • shockPath s Y ε (s + k) - q (s + k)) =
        𝔼.E s (x (s + k) - p (s + k)) + (c * (Y k - pt k)) • ε) := by
  have hqe := shock_response 𝔼 hβ hκ hp hpa hpg hirf hptb hεs hunf hεb c hq hqa hqg
  subst hqe
  have hs : ∀ (f : ℕ → ℝ) k, shockPath s f ε (s + k) = f k • ε := fun f k => by
    simp [shockPath]
  refine ⟨fun k => ?_, fun r hr j => ?_, fun k => ?_⟩
  · rw [map_add, map_smul, hs, map_smul, hεs, smul_smul]
  · rw [map_add, map_smul]
    by_cases h : s ≤ j
    · simp [shockPath, h, map_smul, hunf r hr]
    · simp [shockPath, h]
  · simp only [hs]
    have e : x (s + k) + c • Y k • ε - (p (s + k) + c • pt k • ε) =
        (x (s + k) - p (s + k)) + (c * (Y k - pt k)) • ε := by
      funext ω; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, map_add, map_smul, hεs]

/-- Woodford (2003), p. 189: the impulse response as an exact derivative. Along the family of
economies shocked by `c ε` (`c ∈ ℝ`), whose equilibria are `q c`,
`∂/∂c E_s log P_{s+k} = p̃_k ε`. -/
theorem shock_hasDerivAt {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ}
    {x p : ℕ → Ω → ℝ} (hp : NKPC 𝔼 β κ pm1 x p) (hpa : 𝔼.Adapted p) (hpg : LinGrowth 𝔼 p)
    {Y pt : ℕ → ℝ} (hirf : IRFEq β κ Y pt) (hptb : ∃ M, ∀ k, |pt k| ≤ M) {s : ℕ}
    {ε : Ω → ℝ} (hεs : 𝔼.E s ε = ε) (hunf : ∀ r < s, 𝔼.E r ε = 0)
    (hεb : ∃ M, ∀ ω, |ε ω| ≤ M) {q : ℝ → ℕ → Ω → ℝ}
    (hq : ∀ c, NKPC 𝔼 β κ pm1 (fun t => x t + c • shockPath s Y ε t) (q c))
    (hqa : ∀ c, 𝔼.Adapted (q c)) (hqg : ∀ c, LinGrowth 𝔼 (q c)) (k : ℕ) (ω : Ω) (c₀ : ℝ) :
    HasDerivAt (fun c => 𝔼.E s (q c (s + k)) ω) (pt k * ε ω) c₀ := by
  have e : (fun c => 𝔼.E s (q c (s + k)) ω) = fun c => 𝔼.E s (p (s + k)) ω + c * (pt k * ε ω) := by
    funext c
    have := congrFun ((shock_response_expect 𝔼 hβ hκ hp hpa hpg hirf hptb hεs hunf hεb c (hq c)
      (hqa c) (hqg c)).1 k) ω
    rw [this]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e]
  simpa using ((hasDerivAt_id c₀).mul_const (pt k * ε ω)).const_add (𝔼.E s (p (s + k)) ω)

/-- **Proposition 3.6** (Woodford 2003, p. 190) for an arbitrary expectation system: after a
date-`s` permanent increase `c ε` in nominal spending (forcing `x + c 1_{r ≥ s} ε`), the
equilibrium date-`s` expectation of `log P_{s+k}` rises by `c (1 − λ^{k+1}) ε`, that of
`log Y_{s+k}` (relative to `Yⁿ`) by `c λ^{k+1} ε`, and expected nominal spending by `c ε`. -/
theorem prop_3_6_stochastic {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) {pm1 : Ω → ℝ}
    {x p : ℕ → Ω → ℝ} (hp : NKPC 𝔼 β κ pm1 x p) (hpa : 𝔼.Adapted p) (hpg : LinGrowth 𝔼 p)
    {s : ℕ} {ε : Ω → ℝ} (hεs : 𝔼.E s ε = ε) (hunf : ∀ r < s, 𝔼.E r ε = 0)
    (hεb : ∃ M, ∀ ω, |ε ω| ≤ M) (c : ℝ) {q : ℕ → Ω → ℝ}
    (hq : NKPC 𝔼 β κ pm1 (fun t => x t + c • shockPath s (fun _ => 1) ε t) q)
    (hqa : 𝔼.Adapted q) (hqg : LinGrowth 𝔼 q) (k : ℕ) :
    𝔼.E s (shockPath s (fun _ => 1) ε (s + k)) = ε ∧
      𝔼.E s (q (s + k)) = 𝔼.E s (p (s + k)) + (c * (1 - lam1 β κ ^ (k + 1))) • ε ∧
      𝔼.E s (x (s + k) + c • shockPath s (fun _ => 1) ε (s + k) - q (s + k)) =
        𝔼.E s (x (s + k) - p (s + k)) + (c * lam1 β κ ^ (k + 1)) • ε := by
  have hb : ∃ M, ∀ k, |p36 β κ k| ≤ M := bounded_of_tendsto (p36_tendsto hβ hκ)
  obtain ⟨h1, -, h3⟩ := shock_response_expect 𝔼 hβ hκ hp hpa hpg (p36_irfEq hβ hκ) hb hεs hunf
    hεb c hq hqa hqg
  refine ⟨by simp [shockPath, hεs], h1 k, ?_⟩
  rw [h3 k]
  simp only [p36]
  congr 2
  ring

/-! ### Comparison with the predetermined-price (New Classical) model -/

/-- Woodford (2003), (1.32), p. 159: the New Classical Phillips curve
`π_t = κ (Ŷ_t − Ŷ_tⁿ) + E_{t−1} π_t`, in the price-level form of p. 189
(`x_t = log 𝒴_t − log Y_tⁿ`), for dates `t + 1 ≥ 1`. -/
def NCPC (κ : ℝ) (x p : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p (t + 1) - p t = κ • (x (t + 1) - p (t + 1)) + 𝔼.E t (p (t + 1) - p t)

/-- Woodford (2003), (1.32)–(1.33), p. 160: for adapted `log P`, (1.32) holds iff
`(1 + κ) log P_{t+1} = κ x_{t+1} + E_t x_{t+1}`; equivalently the output gap is
`x_{t+1} − log P_{t+1} = (1 + κ)⁻¹ (x_{t+1} − E_t x_{t+1})`, the unforecastable part only. -/
theorem ncpc_iff {κ : ℝ} (hκ : 0 < κ) {x p : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p) :
    NCPC 𝔼 κ x p ↔ ∀ t, x (t + 1) - p (t + 1) = (1 + κ)⁻¹ • (x (t + 1) - 𝔼.E t (x (t + 1))) := by
  have h1 : (1 + κ) ≠ 0 := by linarith
  refine forall_congr' fun t => ?_
  have hpt : 𝔼.E t (p t) = p t := hpa t
  constructor
  · intro h
    have hE := congrArg (𝔼.E t) h
    rw [map_add, map_smul, 𝔼.E_E_self, eq_comm, add_eq_right, map_sub, smul_eq_zero] at hE
    have hEp : 𝔼.E t (p (t + 1)) = 𝔼.E t (x (t + 1)) := by
      rcases hE with hE | hE
      · exact absurd hE hκ.ne'
      · exact (sub_eq_zero.1 hE).symm
    rw [map_sub, hEp, hpt] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp
    linarith
  · intro h
    have hEp : 𝔼.E t (p (t + 1)) = 𝔼.E t (x (t + 1)) := by
      have := congrArg (𝔼.E t) h
      rw [map_smul, map_sub, map_sub, 𝔼.E_E_self, sub_self, smul_zero, sub_eq_zero] at this
      exact this.symm
    rw [map_sub, hEp, hpt]
    funext ω
    have := congrFun h ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp at this
    linarith

/-- Woodford (2003), p. 160 and p. 200: **no persistence under predetermined prices.** In the New
Classical model, a date-`s` news shock `c ε` to nominal spending with response path `Ỹ` moves
the output gap at date `s` by `c Ỹ_0 ε/(1 + κ)` and at every other date by nothing. -/
theorem ncpc_shock_gap {κ : ℝ} (hκ : 0 < κ) {x p q : ℕ → Ω → ℝ} {Y : ℕ → ℝ} {s : ℕ}
    (hs : 1 ≤ s) {ε : Ω → ℝ} (hεs : 𝔼.E s ε = ε) (hunf : ∀ r < s, 𝔼.E r ε = 0) (c : ℝ)
    (hp : NCPC 𝔼 κ x p) (hpa : 𝔼.Adapted p)
    (hq : NCPC 𝔼 κ (fun t => x t + c • shockPath s Y ε t) q) (hqa : 𝔼.Adapted q) (t : ℕ) :
    (x (t + 1) + c • shockPath s Y ε (t + 1) - q (t + 1)) - (x (t + 1) - p (t + 1)) =
      if t + 1 = s then (c * Y 0 / (1 + κ)) • ε else 0 := by
  rw [(ncpc_iff 𝔼 hκ hqa).1 hq t, (ncpc_iff 𝔼 hκ hpa).1 hp t]
  simp only [map_add, map_smul]
  by_cases h : s ≤ t + 1
  · by_cases h' : t + 1 = s
    · subst h'
      simp only [shockPath, le_refl, ↓reduceIte, Nat.sub_self, map_smul, hunf t (by omega)]
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      field_simp
      ring
    · have hst : s ≤ t := by omega
      simp only [shockPath, h, ↓reduceIte, map_smul, ForwardSolution.E_of_known 𝔼 hst hεs, h']
      funext ω
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      ring
  · have h' : t + 1 ≠ s := by omega
    simp only [shockPath, h, ↓reduceIte, map_zero, smul_zero, add_zero, h']
    funext ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring

/-- Woodford (2003), pp. 160 and 189–191: the deterministic comparison for the shock of
Proposition 3.6. The predetermined-price model gives the output response
`(1/(1 + κ), 0, 0, …)`, the Calvo model `λ^{k+1} > 0` at every horizon. -/
theorem nc_vs_calvo {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    (∀ k, 0 < y36 β κ k) ∧ 0 < 1 / (1 + κ) ∧ 1 / (1 + κ) < 1 := by
  refine ⟨(y36_decay hβ hκ).1, by positivity, ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

/-! ### Comparative statics of the persistence root (p. 192) -/

/-- Woodford (2003), p. 192: "the smaller root of `P(λ)` varies inversely with the size of `κ`":
`λ₁` is strictly decreasing in `κ`. -/
theorem lam1_strictAnti {β : ℝ} (hβ : 0 < β) {κ κ' : ℝ} (hκ : 0 < κ) (hκκ' : κ < κ') :
    lam1 β κ' < lam1 β κ :=
  QuadraticRoots.lam1_strictAntiOn hβ hκ (hκ.trans hκκ') hκκ'

/-- Woodford (2003), p. 192: `0 < λ₁ < 2/(1 + β + κ)`. -/
theorem lam1_lt_two_div {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) :
    lam1 β κ < 2 / (1 + β + κ) := by
  have hp := beta_mul_prod hβ hκ
  have h0 := lam1_pos hβ hκ
  have hl2 : (1 + β + κ) / (2 * β) < lam2 β κ := by
    unfold lam2
    have := Real.sqrt_pos.2 (charDisc_pos hβ hκ)
    exact div_lt_div_of_pos_right (by linarith) (by linarith)
  rw [lt_div_iff₀ (by linarith)]
  have h2 : (1 + β + κ) < 2 * β * lam2 β κ := by
    rw [div_lt_iff₀ (by linarith)] at hl2
    linarith
  nlinarith

/-- Woodford (2003), p. 192: `λ₁ → 0` "in the case of very large `κ`". -/
theorem lam1_tendsto_zero_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun κ => lam1 β κ) atTop (𝓝 0) :=
  tendsto_lam1_atTop hβ

/-- Woodford (2003), p. 192: `λ₁ → 1` "for `κ` near zero" (here `0 < β < 1`). -/
theorem lam1_tendsto_one {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun κ => lam1 β κ) (𝓝[>] 0) (𝓝 1) :=
  tendsto_lam1_zero hβ hβ1.le

/-- Woodford (2003), p. 192: "for any value of `α`, the value of `κ` can be made arbitrarily
small, or arbitrarily large, through assignment of an appropriate value to `ζ`": every
`K > 0` is `κ(α, β, ζ)` for some `ζ > 0`. -/
theorem kappaCalvo_surj {α β K : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hK : 0 < K) : ∃ ζ, 0 < ζ ∧ kappa α β ζ = K := by
  have h1 : 0 < 1 - α * β := by nlinarith
  have h2 : 0 < 1 - α := by linarith
  refine ⟨K * α / ((1 - α) * (1 - α * β)), by positivity, ?_⟩
  unfold kappa
  field_simp

/-- Woodford (2003), p. 192: `κ` is strictly decreasing in `α` (less frequent price changes
flatten the Phillips curve). -/
theorem kappaCalvo_strictAnti_alpha {β ζ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hζ : 0 < ζ)
    {α α' : ℝ} (hα : 0 < α) (hαα' : α < α') (hα' : α' < 1) :
    kappa α' β ζ < kappa α β ζ := by
  unfold kappa
  have hα'0 : 0 < α' := hα.trans hαα'
  rw [div_lt_div_iff₀ hα'0 hα]
  have hprod : α * α' < 1 := by nlinarith
  have key : (1 - α') * (1 - α' * β) * α - (1 - α) * (1 - α * β) * α' =
      -(α' - α) * (1 - α * α' * β) := by ring
  have : 0 < 1 - α * α' * β := by nlinarith
  nlinarith [mul_pos (sub_pos.2 hαα') this]

/-- Woodford (2003), p. 192: persistence `λ` increases with `α` (fixed `ζ`). -/
theorem lam1_strictMono_alpha {β ζ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hζ : 0 < ζ)
    {α α' : ℝ} (hα : 0 < α) (hαα' : α < α') (hα' : α' < 1) :
    lam1 β (kappa α β ζ) < lam1 β (kappa α' β ζ) :=
  lam1_strictAnti hβ (kappa_pos (hα.trans hαα') hα' hβ1 hζ)
    (kappaCalvo_strictAnti_alpha hβ hβ1 hζ hα hαα' hα')

/-- Woodford (2003), p. 192: persistence `λ` decreases with `ζ` (stronger strategic
complementarity, smaller `ζ`, means more persistence). -/
theorem lam1_strictAnti_zeta {α β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    {ζ ζ' : ℝ} (hζ : 0 < ζ) (hζζ' : ζ < ζ') :
    lam1 β (kappa α β ζ') < lam1 β (kappa α β ζ) := by
  refine lam1_strictAnti hβ (kappa_pos hα hα1 hβ1 hζ) ?_
  unfold kappa
  have : 0 < 1 - α * β := by nlinarith
  have : 0 < 1 - α := by linarith
  apply div_lt_div_of_pos_right _ hα
  exact mul_lt_mul_of_pos_left hζζ' (by positivity)

/-! ### The contract multiplier: `λ > α ⟺ ζ < 1` (p. 193) -/

/-- Woodford (2003), p. 193: `P(α) = (1 − α)(1 − αβ)(1 − ζ)` when `κ` is given by (2.13). -/
theorem charPoly_alpha {α β ζ : ℝ} (hα : α ≠ 0) :
    charPoly β (kappa α β ζ) α = (1 - α) * (1 - α * β) * (1 - ζ) := by
  unfold charPoly kappa
  field_simp
  ring

/-- Woodford (2003), p. 193: **`λ > α` if and only if `ζ < 1`** (strategic complementarity). -/
theorem alpha_lt_lam_iff {α β ζ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hζ : 0 < ζ) : α < lam1 β (kappa α β ζ) ↔ ζ < 1 := by
  have hκ := kappa_pos hα hα1 hβ1 hζ
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have hpos : 0 < (1 - α) * (1 - α * β) := mul_pos (by linarith) (by nlinarith)
  have e := charPoly_alpha (β := β) (ζ := ζ) hα.ne'
  constructor
  · intro h
    have := (charPoly_pos_iff_outside hβ hκ α).2 (Or.inl h)
    rw [e] at this
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    have : 0 < charPoly β (kappa α β ζ) α := by rw [e]; nlinarith
    rcases (charPoly_pos_iff_outside hβ hκ α).1 this with h' | h'
    · exact h'
    · linarith

/-- Woodford (2003), p. 193: `λ = α` exactly when `ζ = 1`. -/
theorem alpha_eq_lam_iff {α β ζ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hζ : 0 < ζ) : lam1 β (kappa α β ζ) = α ↔ ζ = 1 := by
  have hκ := kappa_pos hα hα1 hβ1 hζ
  have h2 := (lam1_lt_one_lt_lam2 hβ hκ).2
  have hpos : 0 < (1 - α) * (1 - α * β) := mul_pos (by linarith) (by nlinarith)
  have e := charPoly_alpha (β := β) (ζ := ζ) hα.ne'
  constructor
  · intro h
    have := charPoly_lam1 hβ hκ
    rw [h, e] at this
    rcases mul_eq_zero.1 this with h' | h'
    · linarith
    · linarith
  · intro h
    have : charPoly β (kappa α β ζ) α = 0 := by rw [e, h]; ring
    rcases (charPoly_eq_zero_iff hβ hκ α).1 this with h' | h'
    · exact h'.symm
    · linarith

/-- Woodford (2003), p. 193: in the case of strategic substitutes (`ζ > 1`) there is even less
persistence than the mechanical one: `λ < α ⟺ ζ > 1`. -/
theorem lam_lt_alpha_iff {α β ζ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1)
    (hζ : 0 < ζ) : lam1 β (kappa α β ζ) < α ↔ 1 < ζ := by
  have h1 := alpha_lt_lam_iff hα hα1 hβ hβ1 hζ
  have h2 := alpha_eq_lam_iff hα hα1 hβ hβ1 hζ
  constructor
  · intro h
    rcases lt_trichotomy ζ 1 with hz | hz | hz
    · linarith [h1.2 hz]
    · linarith [h2.2 hz]
    · exact hz
  · intro h
    rcases lt_trichotomy (lam1 β (kappa α β ζ)) α with hl | hl | hl
    · exact hl
    · linarith [h2.1 hl]
    · linarith [h1.1 hl]

/-- Woodford (2003), p. 194: the half-life `log 2 / log r⁻¹` of a geometric decay `r^t`. -/
noncomputable def halfLife (r : ℝ) : ℝ := Real.log 2 / Real.log r⁻¹

/-- Woodford (2003), p. 194: after `halfLife r` periods, `r^t` has fallen to one half. -/
theorem rpow_halfLife {r : ℝ} (hr : 0 < r) (hr1 : r < 1) : r ^ halfLife r = 1 / 2 := by
  have hl : 0 < Real.log r⁻¹ := Real.log_pos ((one_lt_inv₀ hr).2 hr1)
  rw [Real.rpow_def_of_pos hr, halfLife, Real.log_inv]
  have : Real.log r * (Real.log 2 / -Real.log r) = -Real.log 2 := by
    rw [Real.log_inv] at hl
    have : Real.log r ≠ 0 := by linarith
    field_simp
  rw [this, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- Woodford (2003), p. 191: "the closer `λ` is to one, the longer the time it takes for real
activity to return": the half-life is strictly increasing in the decay factor. -/
theorem halfLife_strictMonoOn : StrictMonoOn halfLife (Set.Ioo 0 1) := by
  intro r hr r' hr' hrr'
  have hl : 0 < Real.log r'⁻¹ := Real.log_pos ((one_lt_inv₀ hr'.1).2 hr'.2)
  have hlt : Real.log r'⁻¹ < Real.log r⁻¹ :=
    Real.log_lt_log (inv_pos.2 hr'.1) ((inv_lt_inv₀ hr'.1 hr.1).2 hrr')
  unfold halfLife
  exact div_lt_div_of_pos_left (Real.log_pos (by norm_num)) hl hlt

/-- Woodford (2003), p. 194: the contract multiplier `log α⁻¹ / log λ⁻¹` of Chari, Kehoe and
McGrattan (2000), the ratio of the staggered to the synchronized half-life. -/
noncomputable def contractMult (α l : ℝ) : ℝ := Real.log α⁻¹ / Real.log l⁻¹

/-- Woodford (2003), p. 194: the contract multiplier is the ratio of half-lives
`(log 2/log λ⁻¹)/(log 2/log α⁻¹)`. -/
theorem contractMult_eq {α l : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    halfLife l / halfLife α = contractMult α l := by
  have ha : 0 < Real.log α⁻¹ := Real.log_pos ((one_lt_inv₀ hα).2 hα1)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold halfLife contractMult
  rw [div_div_div_cancel_left' _ _ h2.ne']

/-- Woodford (2003), p. 194: "the multiplier is greater than one if and only if `ζ < 1`". -/
theorem contractMult_gt_one_iff {α β ζ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β)
    (hβ1 : β < 1) (hζ : 0 < ζ) : 1 < contractMult α (lam1 β (kappa α β ζ)) ↔ ζ < 1 := by
  have hκ := kappa_pos hα hα1 hβ1 hζ
  have hl0 := lam1_pos hβ hκ
  have hl1 := (lam1_lt_one_lt_lam2 hβ hκ).1
  set l := lam1 β (kappa α β ζ)
  have hll : 0 < Real.log l⁻¹ := Real.log_pos ((one_lt_inv₀ hl0).2 hl1)
  rw [← alpha_lt_lam_iff hα hα1 hβ hβ1 hζ, contractMult, one_lt_div hll]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : Real.log α⁻¹ ≤ Real.log l⁻¹ :=
      Real.log_le_log (inv_pos.2 hα) ((inv_le_inv₀ hα hl0).2 hc)
    linarith
  · intro h
    exact Real.log_lt_log (inv_pos.2 hl0) ((inv_lt_inv₀ hl0 hα).2 h)

/-! ### The continuous-time limit (2.20) (p. 194 and footnote 50) -/

/-- Woodford (2003), fn. 50, p. 194: the second-order remainder `(eˣ − 1 − x)/x²` used to expand
the characteristic polynomial (2.19) in powers of the period length. -/
noncomputable def expQuad (x : ℝ) : ℝ := (Real.exp x - 1 - x) / x ^ 2

/-- Woodford (2003), fn. 50: `eˣ − 1 = x + x² · expQuad x` for `x ≠ 0`. -/
theorem exp_sub_one_eq {x : ℝ} (hx : x ≠ 0) : Real.exp x - 1 = x + x ^ 2 * expQuad x := by
  unfold expQuad
  field_simp
  ring

/-- Woodford (2003), fn. 50: `|expQuad x − 1/2| ≤ |x|` for `0 < |x| ≤ 1` (Taylor bound). -/
theorem abs_expQuad_sub_half {x : ℝ} (hx : x ≠ 0) (hx1 : |x| ≤ 1) :
    |expQuad x - 1 / 2| ≤ |x| := by
  have hb := Real.exp_bound hx1 (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at hb
  norm_num at hb
  have hx2 : 0 < x ^ 2 := by positivity
  have e : expQuad x - 1 / 2 = (Real.exp x - (1 + x + x ^ 2 / 2)) / x ^ 2 := by
    unfold expQuad
    field_simp
    ring
  rw [e, abs_div, abs_of_pos hx2, div_le_iff₀ hx2]
  have h3 : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs, mul_comm]
  have hx0 : 0 ≤ |x| ^ 3 := by positivity
  nlinarith

/-- Woodford (2003), fn. 50: `(eˣ − 1 − x)/x² → 1/2` as `x → 0`. -/
theorem tendsto_expQuad : Tendsto expQuad (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 ε, lt_min one_pos hε, fun x hx hdist => ?_⟩
  rw [Real.dist_eq, sub_zero] at hdist
  rw [Real.dist_eq]
  have hx0 : x ≠ 0 := hx
  calc |expQuad x - 1 / 2| ≤ |x| := abs_expQuad_sub_half hx0 (hdist.le.trans (min_le_left _ _))
    _ < ε := hdist.trans_le (min_le_right _ _)

/-- Woodford (2003), fn. 50: `(1 − e^{−u})/u → 1` as `u → 0`. -/
theorem tendsto_one_sub_exp_neg_div :
    Tendsto (fun u => (1 - Real.exp (-u)) / u) (𝓝[≠] 0) (𝓝 1) := by
  have hd : HasDerivAt (fun x => Real.exp (-x)) (-1) 0 := by
    have := (hasDerivAt_neg (0 : ℝ)).exp
    simpa using this
  have h := hd.tendsto_slope_zero.neg
  have e : (fun u => (1 - Real.exp (-u)) / u) =
      fun t => -(t⁻¹ • (Real.exp (-(0 + t)) - Real.exp (-0))) := by
    funext t
    simp only [zero_add, neg_zero, Real.exp_zero, smul_eq_mul]
    ring
  rw [e]
  simpa using h

/-- Woodford (2003), fn. 50: if `x(Δ) = e^{−r(Δ)Δ}` with `r(Δ) → c > 0`, then
`(1 − x(Δ))/Δ → c` as the period length `Δ ↓ 0`. -/
theorem tendsto_rate {r : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (hr : Tendsto r (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun Δ => (1 - Real.exp (-(r Δ * Δ))) / Δ) (𝓝[>] 0) (𝓝 c) := by
  have hpos : ∀ᶠ Δ in 𝓝[>] (0 : ℝ), 0 < r Δ ∧ 0 < Δ :=
    (hr.eventually (lt_mem_nhds hc)).and self_mem_nhdsWithin
  have hu : Tendsto (fun Δ => r Δ * Δ) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun Δ : ℝ => Δ) (𝓝[>] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using hr.mul this
    · filter_upwards [hpos] with Δ h
      exact (mul_pos h.1 h.2).ne'
  have hlim := hr.mul (tendsto_one_sub_exp_neg_div.comp hu)
  rw [mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hpos] with Δ h
  simp only [Function.comp]
  have : r Δ ≠ 0 := h.1.ne'
  have : Δ ≠ 0 := h.2.ne'
  field_simp

/-- Woodford (2003), fn. 50: `b Δ → 0` through non-zero values when `b ≠ 0`. -/
theorem tendsto_mul_nhdsNE {b : ℝ} (hb : b ≠ 0) :
    Tendsto (fun Δ : ℝ => b * Δ) (𝓝[>] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun Δ : ℝ => Δ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa using this.const_mul b
  · filter_upwards [self_mem_nhdsWithin] with Δ h
    exact mul_ne_zero hb (ne_of_gt h)

/-- Woodford (2003), fn. 50: the characteristic polynomial (2.19) evaluated at `λ = e^{−bΔ}` and
divided by `λ`: `(e^{bΔ} − 1) + β (e^{−bΔ} − 1)` (which must equal `κ`). -/
noncomputable def ctN (b Δ β : ℝ) : ℝ := (Real.exp (b * Δ) - 1) + β * (Real.exp (-(b * Δ)) - 1)

/-- Woodford (2003), fn. 50: with `λ = e^{−mΔ}`, (2.19) reads
`(e^{mΔ} − 1) + β(e^{−mΔ} − 1) = κ`. -/
theorem ctN_lam1 {β κ Δ : ℝ} (hβ : 0 < β) (hκ : 0 < κ) (hΔ : 0 < Δ) :
    ctN (Real.log (lam1 β κ)⁻¹ / Δ) Δ β = κ := by
  have h0 := lam1_pos hβ hκ
  have hr := charPoly_lam1 hβ hκ
  unfold charPoly at hr
  unfold ctN
  rw [div_mul_cancel₀ _ hΔ.ne', Real.exp_log (inv_pos.2 h0), Real.log_inv, neg_neg,
    Real.exp_log h0]
  field_simp
  linear_combination hr

/-- Woodford (2003), fn. 50: for `0 ≤ β ≤ 1` and `Δ > 0`, `ctN` is monotone in the rate `b ≥ 0`. -/
theorem ctN_mono {β Δ b₁ b₂ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hΔ : 0 < Δ) (hb₁ : 0 ≤ b₁)
    (h12 : b₁ ≤ b₂) : ctN b₁ Δ β ≤ ctN b₂ Δ β := by
  unfold ctN
  rw [Real.exp_neg, Real.exp_neg]
  set A := Real.exp (b₁ * Δ)
  set B := Real.exp (b₂ * Δ)
  have hA : 1 ≤ A := Real.one_le_exp (mul_nonneg hb₁ hΔ.le)
  have hAB : A ≤ B := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h12 hΔ.le)
  have hA0 : A ≠ 0 := (Real.exp_pos _).ne'
  have hB0 : B ≠ 0 := (Real.exp_pos _).ne'
  have hd : A⁻¹ - B⁻¹ = (B - A) / (A * B) := by field_simp
  have hAB1 : 1 ≤ A * B := by nlinarith
  have hle : (B - A) / (A * B) ≤ B - A := div_le_self (by linarith) hAB1
  have hnn : 0 ≤ (B - A) / (A * B) := div_nonneg (by linarith) (by positivity)
  have : β * (A⁻¹ - B⁻¹) ≤ B - A := by
    rw [hd]; nlinarith
  nlinarith

/-- Woodford (2003), fn. 50: `ctN(b, Δ, β(Δ))/Δ² → b² + ρ b` when `(1 − β(Δ))/Δ → ρ` and
`β(Δ) → 1`. -/
theorem ctN_tendsto {b ρ : ℝ} (hb : b ≠ 0) {β : ℝ → ℝ}
    (h1β : Tendsto (fun Δ => (1 - β Δ) / Δ) (𝓝[>] 0) (𝓝 ρ))
    (hβ1 : Tendsto β (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun Δ => ctN b Δ (β Δ) / Δ ^ 2) (𝓝[>] 0) (𝓝 (b ^ 2 + ρ * b)) := by
  have hq1 := tendsto_expQuad.comp (tendsto_mul_nhdsNE hb)
  have hq2 := tendsto_expQuad.comp (tendsto_mul_nhdsNE (neg_ne_zero.2 hb))
  have hlim := (h1β.const_mul b).add ((hq1.add (hβ1.mul hq2)).const_mul (b ^ 2))
  have hv : b * ρ + b ^ 2 * (1 / 2 + 1 * (1 / 2)) = b ^ 2 + ρ * b := by ring
  rw [hv] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  have hΔ0 : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ
  have hbΔ : b * Δ ≠ 0 := mul_ne_zero hb hΔ0
  simp only [Function.comp]
  unfold ctN
  rw [exp_sub_one_eq hbΔ, show -(b * Δ) = -b * Δ by ring,
    exp_sub_one_eq (mul_ne_zero (neg_ne_zero.2 hb) hΔ0)]
  field_simp
  ring

/-- Woodford (2003), fn. 50: the positive root `n` of `n² + ρ n − a(a + ρ)ζ = 0`. -/
noncomputable def ctRoot (a ρ ζ : ℝ) : ℝ := (-ρ + √(ρ ^ 2 + 4 * a * (a + ρ) * ζ)) / 2

/-- Woodford (2003), fn. 50: `n² + ρ n = a (a + ρ) ζ`. -/
theorem ctRoot_eq {a ρ ζ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hζ : 0 < ζ) :
    ctRoot a ρ ζ ^ 2 + ρ * ctRoot a ρ ζ = a * (a + ρ) * ζ := by
  have hD : 0 ≤ ρ ^ 2 + 4 * a * (a + ρ) * ζ := by positivity
  have hs := Real.sq_sqrt hD
  unfold ctRoot
  linear_combination hs / 4

/-- Woodford (2003), fn. 50: `n > 0`. -/
theorem ctRoot_pos {a ρ ζ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hζ : 0 < ζ) : 0 < ctRoot a ρ ζ := by
  unfold ctRoot
  have : ρ < √(ρ ^ 2 + 4 * a * (a + ρ) * ζ) := by
    rw [Real.lt_sqrt hρ.le]
    have : 0 < 4 * a * (a + ρ) * ζ := by positivity
    linarith
  linarith

/-- **Woodford (2003), fn. 50, p. 194: the continuous-time limit.** Fix `ζ > 0` and let `α`, `β`
depend on the period length `Δ` with `log α⁻¹/Δ → a > 0` and `log β⁻¹/Δ → ρ > 0`. Then
`log λ⁻¹/Δ → n`, the positive root of `n² + ρ n = a (a + ρ) ζ`. -/
theorem ct_limit {a ρ ζ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hζ : 0 < ζ) {α β : ℝ → ℝ}
    (hab : ∀ Δ, 0 < Δ → 0 < α Δ ∧ α Δ < 1 ∧ 0 < β Δ ∧ β Δ < 1)
    (hαlim : Tendsto (fun Δ => Real.log (α Δ)⁻¹ / Δ) (𝓝[>] 0) (𝓝 a))
    (hβlim : Tendsto (fun Δ => Real.log (β Δ)⁻¹ / Δ) (𝓝[>] 0) (𝓝 ρ)) :
    Tendsto (fun Δ => Real.log (lam1 (β Δ) (kappa (α Δ) (β Δ) ζ))⁻¹ / Δ) (𝓝[>] 0)
      (𝓝 (ctRoot a ρ ζ)) := by
  set l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hpos : ∀ᶠ Δ in l, 0 < Δ := self_mem_nhdsWithin
  -- `x = exp(−(log x⁻¹/Δ)·Δ)` for `x > 0`, `Δ > 0`
  have hrepr : ∀ x Δ : ℝ, 0 < x → 0 < Δ → x = Real.exp (-(Real.log x⁻¹ / Δ * Δ)) := by
    intro x Δ hx hΔ
    rw [div_mul_cancel₀ _ hΔ.ne', Real.log_inv, neg_neg, Real.exp_log hx]
  have h1α : Tendsto (fun Δ => (1 - α Δ) / Δ) l (𝓝 a) := by
    refine (tendsto_rate ha hαlim).congr' ?_
    filter_upwards [hpos] with Δ hΔ
    rw [← hrepr _ _ (hab Δ hΔ).1 hΔ]
  have h1β : Tendsto (fun Δ => (1 - β Δ) / Δ) l (𝓝 ρ) := by
    refine (tendsto_rate hρ hβlim).congr' ?_
    filter_upwards [hpos] with Δ hΔ
    rw [← hrepr _ _ (hab Δ hΔ).2.2.1 hΔ]
  have h1αβ : Tendsto (fun Δ => (1 - α Δ * β Δ) / Δ) l (𝓝 (a + ρ)) := by
    refine (tendsto_rate (add_pos ha hρ) (hαlim.add hβlim)).congr' ?_
    filter_upwards [hpos] with Δ hΔ
    have e : Real.exp (-((Real.log (α Δ)⁻¹ / Δ + Real.log (β Δ)⁻¹ / Δ) * Δ)) =
        α Δ * β Δ := by
      rw [add_mul, div_mul_cancel₀ _ hΔ.ne', div_mul_cancel₀ _ hΔ.ne', Real.log_inv,
        Real.log_inv, neg_add, neg_neg, neg_neg, Real.exp_add, Real.exp_log (hab Δ hΔ).1,
        Real.exp_log (hab Δ hΔ).2.2.1]
    rw [e]
  have hid : Tendsto (fun Δ : ℝ => Δ) l (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hconv : ∀ {x : ℝ → ℝ} {c : ℝ}, Tendsto (fun Δ => (1 - x Δ) / Δ) l (𝓝 c) →
      Tendsto x l (𝓝 1) := by
    intro x c hx
    have := tendsto_const_nhds (x := (1 : ℝ)).sub (hid.mul hx)
    rw [zero_mul, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hpos] with Δ hΔ
    field_simp
    ring
  have hα1 := hconv h1α
  have hβ1 := hconv h1β
  -- the limit of `κ/Δ²`
  have hG : Tendsto (fun Δ => kappa (α Δ) (β Δ) ζ / Δ ^ 2) l (𝓝 (a * (a + ρ) * ζ)) := by
    have := ((h1α.mul h1αβ).mul_const ζ).div hα1 one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [hpos] with Δ hΔ
    have : α Δ ≠ 0 := (hab Δ hΔ).1.ne'
    have : Δ ≠ 0 := hΔ.ne'
    simp only [Pi.div_apply]
    unfold kappa
    field_simp
  set n := ctRoot a ρ ζ
  have hn := ctRoot_eq ha hρ hζ
  have hn0 := ctRoot_pos ha hρ hζ
  set m : ℝ → ℝ := fun Δ => Real.log (lam1 (β Δ) (kappa (α Δ) (β Δ) ζ))⁻¹ / Δ
  have hkey : ∀ Δ, 0 < Δ → ctN (m Δ) Δ (β Δ) = kappa (α Δ) (β Δ) ζ ∧ 0 < m Δ := by
    intro Δ hΔ
    obtain ⟨hα0, hα1', hβ0, hβ1'⟩ := hab Δ hΔ
    have hκ := kappa_pos hα0 hα1' hβ1' hζ
    refine ⟨ctN_lam1 hβ0 hκ hΔ, div_pos (Real.log_pos ?_) hΔ⟩
    exact (one_lt_inv₀ (lam1_pos hβ0 hκ)).2 (lam1_lt_one_lt_lam2 hβ0 hκ).1
  rw [tendsto_order]
  constructor
  · intro b hb
    by_cases hb0 : b ≤ 0
    · filter_upwards [hpos] with Δ hΔ
      exact lt_of_le_of_lt hb0 (hkey Δ hΔ).2
    push Not at hb0
    have hlt : b ^ 2 + ρ * b < a * (a + ρ) * ζ := by rw [← hn]; nlinarith
    filter_upwards [(ctN_tendsto hb0.ne' h1β hβ1).eventually_lt hG hlt, hpos] with Δ h hΔ
    by_contra hc
    push Not at hc
    obtain ⟨hk, hm⟩ := hkey Δ hΔ
    have hmono := ctN_mono (hab Δ hΔ).2.2.1.le (hab Δ hΔ).2.2.2.le hΔ hm.le hc
    rw [hk] at hmono
    have : ctN b Δ (β Δ) < kappa (α Δ) (β Δ) ζ := by
      rwa [div_lt_div_iff_of_pos_right (by positivity)] at h
    linarith
  · intro b hb
    have hb0 : 0 < b := hn0.trans hb
    have hlt : a * (a + ρ) * ζ < b ^ 2 + ρ * b := by rw [← hn]; nlinarith
    filter_upwards [hG.eventually_lt (ctN_tendsto hb0.ne' h1β hβ1) hlt, hpos] with Δ h hΔ
    by_contra hc
    push Not at hc
    obtain ⟨hk, -⟩ := hkey Δ hΔ
    have hmono := ctN_mono (hab Δ hΔ).2.2.1.le (hab Δ hΔ).2.2.2.le hΔ hb0.le hc
    rw [hk] at hmono
    have : kappa (α Δ) (β Δ) ζ < ctN b Δ (β Δ) := by
      rwa [div_lt_div_iff_of_pos_right (by positivity)] at h
    linarith

/-- Woodford (2003), eq. (2.20), p. 194: the continuous-time contract multiplier
`2a*/([4a*(a* + 1)ζ + 1]^{1/2} − 1)`, `a*` the ratio of the rate of price adjustment to the rate
of time preference. -/
noncomputable def cmLimit (A ζ : ℝ) : ℝ := 2 * A / (√(4 * A * (A + 1) * ζ + 1) - 1)

/-- Woodford (2003), (2.20): the square root in (2.20) exceeds one. -/
theorem one_lt_sqrt_cm {A ζ : ℝ} (hA : 0 < A) (hζ : 0 < ζ) : 1 < √(4 * A * (A + 1) * ζ + 1) := by
  rw [Real.lt_sqrt zero_le_one]
  have : 0 < 4 * A * (A + 1) * ζ := by positivity
  linarith

/-- Woodford (2003), fn. 50: "the multiplier (2.20) is then equal to `a/n`". -/
theorem div_ctRoot_eq_cmLimit {a ρ ζ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hζ : 0 < ζ) :
    a / ctRoot a ρ ζ = cmLimit (a / ρ) ζ := by
  have hs : √(ρ ^ 2 + 4 * a * (a + ρ) * ζ) = ρ * √(4 * (a / ρ) * (a / ρ + 1) * ζ + 1) := by
    rw [← Real.sqrt_sq hρ.le, ← Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ.le]
    congr 1
    field_simp
    ring
  have h1 := one_lt_sqrt_cm (div_pos ha hρ) hζ
  unfold ctRoot cmLimit
  rw [hs]
  have : √(4 * (a / ρ) * (a / ρ + 1) * ζ + 1) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Woodford (2003), (2.20), p. 194: the contract multiplier in the continuous-time limit.**
Under the hypotheses of `ct_limit`, `log α⁻¹ / log λ⁻¹ → a/n = 2a*/([4a*(a* + 1)ζ + 1]^{1/2} − 1)`
with `a* = a/ρ`, a genuine limit as the period length `Δ ↓ 0`. -/
theorem contractMult_tendsto {a ρ ζ : ℝ} (ha : 0 < a) (hρ : 0 < ρ) (hζ : 0 < ζ) {α β : ℝ → ℝ}
    (hab : ∀ Δ, 0 < Δ → 0 < α Δ ∧ α Δ < 1 ∧ 0 < β Δ ∧ β Δ < 1)
    (hαlim : Tendsto (fun Δ => Real.log (α Δ)⁻¹ / Δ) (𝓝[>] 0) (𝓝 a))
    (hβlim : Tendsto (fun Δ => Real.log (β Δ)⁻¹ / Δ) (𝓝[>] 0) (𝓝 ρ)) :
    Tendsto (fun Δ => contractMult (α Δ) (lam1 (β Δ) (kappa (α Δ) (β Δ) ζ))) (𝓝[>] 0)
      (𝓝 (cmLimit (a / ρ) ζ)) := by
  rw [← div_ctRoot_eq_cmLimit ha hρ hζ]
  have h := hαlim.div (ct_limit ha hρ hζ hab hαlim hβlim) (ctRoot_pos ha hρ hζ).ne'
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with Δ hΔ
  have hΔ0 : (Δ : ℝ) ≠ 0 := ne_of_gt hΔ
  simp only [Pi.div_apply]
  unfold contractMult
  field_simp

/-- Woodford (2003), p. 194: in the continuous-time limit too, the multiplier exceeds one iff
`ζ < 1`. -/
theorem cmLimit_gt_one_iff {A ζ : ℝ} (hA : 0 < A) (hζ : 0 < ζ) : 1 < cmLimit A ζ ↔ ζ < 1 := by
  have h1 := one_lt_sqrt_cm hA hζ
  unfold cmLimit
  rw [one_lt_div (by linarith)]
  constructor
  · intro h
    have h' : √(4 * A * (A + 1) * ζ + 1) < 2 * A + 1 := by linarith
    rw [Real.sqrt_lt' (by linarith)] at h'
    have hpos : 0 < 4 * A * (A + 1) := by positivity
    have : 4 * A * (A + 1) * ζ < 4 * A * (A + 1) * 1 := by nlinarith
    exact lt_of_mul_lt_mul_left this hpos.le
  · intro h
    have : √(4 * A * (A + 1) * ζ + 1) < 2 * A + 1 := by
      rw [Real.sqrt_lt' (by linarith)]
      nlinarith [mul_pos (mul_pos hA (by linarith : (0 : ℝ) < A + 1)) (sub_pos.2 h)]
    linarith

/-- Woodford (2003), p. 196: (2.20) is strictly decreasing in `ζ`. -/
theorem cmLimit_strictAnti {A : ℝ} (hA : 0 < A) {ζ ζ' : ℝ} (hζ : 0 < ζ) (hζζ' : ζ < ζ') :
    cmLimit A ζ' < cmLimit A ζ := by
  have h1 := one_lt_sqrt_cm hA hζ
  have hlt : √(4 * A * (A + 1) * ζ + 1) < √(4 * A * (A + 1) * ζ' + 1) := by
    apply Real.sqrt_lt_sqrt (by positivity)
    have : 0 < 4 * A * (A + 1) := by positivity
    nlinarith
  unfold cmLimit
  exact div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)

/-- Woodford (2003), p. 195: the value of `ζ` required for a given multiplier `M` in (2.20),
`ζ = ((1 + 2a*/M)² − 1)/(4a*(a* + 1))`. -/
noncomputable def zetaFor (A M : ℝ) : ℝ := ((1 + 2 * A / M) ^ 2 - 1) / (4 * A * (A + 1))

/-- Woodford (2003), pp. 195–196: `zetaFor a* M` delivers the multiplier `M` in (2.20), and is the
only such `ζ > 0`. -/
theorem cmLimit_eq_iff {A M ζ : ℝ} (hA : 0 < A) (hM : 0 < M) (hζ : 0 < ζ) :
    cmLimit A ζ = M ↔ ζ = zetaFor A M := by
  have hz0 : 0 < zetaFor A M := by
    unfold zetaFor
    have : 1 < 1 + 2 * A / M := by have := div_pos (mul_pos two_pos hA) hM; linarith
    have : 1 < (1 + 2 * A / M) ^ 2 := by nlinarith
    exact div_pos (by linarith) (by positivity)
  have hval : cmLimit A (zetaFor A M) = M := by
    unfold cmLimit zetaFor
    have e : 4 * A * (A + 1) * (((1 + 2 * A / M) ^ 2 - 1) / (4 * A * (A + 1))) + 1 =
        (1 + 2 * A / M) ^ 2 := by field_simp; ring
    have hp : 0 ≤ 1 + 2 * A / M := by positivity
    rw [e, Real.sqrt_sq hp]
    field_simp
    ring
  constructor
  · intro h
    rcases lt_trichotomy ζ (zetaFor A M) with h' | h' | h'
    · have := cmLimit_strictAnti hA hζ h'; linarith
    · exact h'
    · have := cmLimit_strictAnti hA hz0 h'; linarith
  · rintro rfl
    exact hval

/-- Woodford (2003), p. 194: "in the case that `a* ≫ 1`, this is approximately `ζ^{−1/2}`,
regardless of the size of `a*`": (2.20) tends to `ζ^{−1/2}` as `a* → ∞`. -/
theorem cmLimit_tendsto_atTop {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun A => cmLimit A ζ) atTop (𝓝 (1 / √ζ)) := by
  have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hg : Tendsto (fun A : ℝ => 4 * ζ + 4 * ζ * A⁻¹ + (A⁻¹) ^ 2) atTop (𝓝 (4 * ζ)) := by
    simpa using (tendsto_const_nhds.add (hinv.const_mul (4 * ζ))).add (hinv.pow 2)
  have hd : Tendsto (fun A : ℝ => √(4 * ζ + 4 * ζ * A⁻¹ + (A⁻¹) ^ 2) - A⁻¹) atTop
      (𝓝 (2 * √ζ)) := by
    have h4 : √(4 * ζ) = 2 * √ζ := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq two_pos.le]
    simpa [h4] using hg.sqrt.sub hinv
  have hs0 : 0 < √ζ := Real.sqrt_pos.2 hζ
  have h := (tendsto_const_nhds (x := (2 : ℝ))).div hd (by positivity)
  rw [show 2 / (2 * √ζ) = 1 / √ζ by field_simp] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with A hA
  simp only [Pi.div_apply]
  unfold cmLimit
  set g := 4 * ζ + 4 * ζ * A⁻¹ + A⁻¹ ^ 2
  have hs : √(4 * A * (A + 1) * ζ + 1) = A * √g := by
    rw [← Real.sqrt_sq hA.le, ← Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le]
    congr 1
    simp only [g]
    field_simp
  have h1 := one_lt_sqrt_cm hA hζ
  rw [hs] at h1 ⊢
  have e : A * √g - 1 = A * (√g - A⁻¹) := by field_simp
  have hpos : 0 < √g - A⁻¹ := by
    have h2 : 0 < A * (√g - A⁻¹) := by rw [← e]; linarith
    exact pos_of_mul_pos_right h2 hA.le
  rw [e]
  field_simp

/-! ### The numbers quoted in the text (pp. 191, 195–196) -/

/-- Woodford (2003), Fig. 3.7, p. 191 (`β = .99`, `κ = .024`): the persistence root is
`λ ≈ 0.8605`. -/
theorem lam1_fig37 : 0.8605 < lam1 0.99 0.024 ∧ lam1 0.99 0.024 < 0.8606 := by
  unfold lam1 charDisc
  have h1 : (0.3101 : ℝ) < √((1 + 0.99 + 0.024) ^ 2 - 4 * 0.99) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √((1 + 0.99 + 0.024) ^ 2 - 4 * 0.99) < (0.3102 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; linarith
  · rw [div_lt_iff₀ (by norm_num)]; linarith

/-- Woodford (2003), p. 195: Chari et al.'s required multiplier, a ten-quarter half-life over a
half-quarter synchronized half-life, is twenty. -/
theorem chari_required_multiplier : (10 : ℝ) / (1 / 2) = 20 := by norm_num

/-- Woodford (2003), p. 195 and fn. 51: with `a* = 33` a multiplier of twenty requires
`ζ ≈ 0.004` (exactly `17.49/4488 ≈ 0.0039`). -/
theorem zeta_for_twenty : 0.0038 < zetaFor 33 20 ∧ zetaFor 33 20 < 0.0040 := by
  unfold zetaFor; norm_num

/-- Woodford (2003), fn. 51: conversely `ζ = 0.004` gives a multiplier of about `19.7 ≈ 20`. -/
theorem cmLimit_0004 : 19.6 < cmLimit 33 0.004 ∧ cmLimit 33 0.004 < 19.8 := by
  unfold cmLimit
  have h1 : (4.353 : ℝ) < √(4 * 33 * (33 + 1) * 0.004 + 1) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √(4 * 33 * (33 + 1) * 0.004 + 1) < (4.354 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- Woodford (2003), p. 196: a VAR half-life of 3 quarters over a synchronized half-life of
2.08 quarters requires a multiplier of only `1.44`. -/
theorem required_multiplier_144 : 1.44 < (3 : ℝ) / 2.08 ∧ (3 : ℝ) / 2.08 < 1.45 := by
  norm_num

/-- Woodford (2003), p. 196: with `a* = 33` the multiplier `1.44` requires only `ζ ≈ 0.49`. -/
theorem zeta_for_144 : 0.488 < zetaFor 33 1.44 ∧ zetaFor 33 1.44 < 0.489 := by
  unfold zetaFor; norm_num

/-- Woodford (2003), p. 196: `ζ = 0.10` gives a multiplier of about `3.3`. -/
theorem cmLimit_010 : 3.26 < cmLimit 33 0.10 ∧ cmLimit 33 0.10 < 3.27 := by
  unfold cmLimit
  have h1 : (21.2 : ℝ) < √(4 * 33 * (33 + 1) * 0.10 + 1) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √(4 * 33 * (33 + 1) * 0.10 + 1) < (21.21 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- Woodford (2003), p. 196: `ζ = 0.15` gives a multiplier of about `2.6`. -/
theorem cmLimit_015 : 2.64 < cmLimit 33 0.15 ∧ cmLimit 33 0.15 < 2.65 := by
  unfold cmLimit
  have h1 : (25.96 : ℝ) < √(4 * 33 * (33 + 1) * 0.15 + 1) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : √(4 * 33 * (33 + 1) * 0.15 + 1) < (25.97 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- Woodford (2003), p. 196: with the synchronized half-life `2.08`, these multipliers give output
half-lives between `5.5` and `6.8` quarters. -/
theorem half_lives_55_68 :
    5.49 < 2.08 * cmLimit 33 0.15 ∧ 2.08 * cmLimit 33 0.15 < 5.52 ∧
      6.78 < 2.08 * cmLimit 33 0.10 ∧ 2.08 * cmLimit 33 0.10 < 6.81 := by
  obtain ⟨a1, a2⟩ := cmLimit_015
  obtain ⟨b1, b2⟩ := cmLimit_010
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Woodford (2003), p. 196: the synchronized half-life `log 2 / a` is `2.08` quarters for the
rate `a = 1/3` per quarter (an average price duration of 9 months), but `2.10` for the rounded
rate `a = 0.33` quoted in the text and footnote 54. -/
theorem sync_half_life :
    (2.079 < Real.log 2 / (1 / 3) ∧ Real.log 2 / (1 / 3) < 2.080) ∧
      (2.100 < Real.log 2 / 0.33 ∧ Real.log 2 / 0.33 < 2.101) := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [lt_div_iff₀ (by norm_num)]; norm_num at h1 ⊢; linarith
  · rw [div_lt_iff₀ (by norm_num)]; norm_num at h2 ⊢; linarith
  · rw [lt_div_iff₀ (by norm_num)]; norm_num at h1 ⊢; linarith
  · rw [div_lt_iff₀ (by norm_num)]; norm_num at h2 ⊢; linarith

/-- Woodford (2003), fn. 55, p. 196: integrating the continuous-time model with `a = 0.33`, the
fraction of prices changed each quarter is `1 − e^{−a} ≈ 0.28`. -/
theorem frac_changed_028 : 0.28 < 1 - Real.exp (-0.33) ∧ 1 - Real.exp (-0.33) < 0.29 := by
  have hx : |(-0.33 : ℝ)| ≤ 1 := by norm_num [abs_of_neg]
  have hb := Real.exp_bound hx (n := 4) (by norm_num)
  have hs : ∑ m ∈ Finset.range 4, (-0.33 : ℝ) ^ m / (m.factorial : ℝ) = 0.7184605 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  rw [hs] at hb
  norm_num [abs_of_neg] at hb
  rw [abs_le] at hb
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> linarith

end Woodford.NominalRigidities.Persistence
