/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.Calvo
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The two-sector model with sectoral asymmetries (Proposition 3.8)

Woodford (2003), *Interest and Prices*, Chapter 3, §2.5, pp. 200–204, and Appendix B, §B.7,
pp. 666–669.

## The Calvo block (used for (2.25)–(2.26), (B.31)–(B.33), and reused by `Delays`)

* `linFOC_iff`: the log-linearised first-order condition (B.32) — in which the firm's relative
  price at `t + k` is its reset price less the cumulated sectoral inflation — is equivalent to the
  relative-price form `Q_t = c ∑ qᵏ E_t m_{t+k} + ∑_{k ≥ 1} qᵏ E_t ψ_{t+k}`, `q = α_j β`,
  `c = (1 − α_j β)/(1 + ωθ)`; the double series is reordered by summation by parts.
* `level_iff_relative`: the level form (2.25) — with the coefficient `(1 − α_j β)`, see E9 — is
  equivalent to the relative form.
* `relative_law_iff_nkpc`: the relative form together with the Calvo law of motion (2.26) is
  equivalent to the sectoral inflation equation (B.33) `ψ_t = ξ m_t + β E_t ψ_{t+1}` together
  with `Q_t = α/(1 − α) ψ_t` (both directions, bounded processes, any `ExpectationSystem`).

## Proposition 3.8

* `sector_inflation`: (B.33), the corrected (B.30) and the sectoral demands give
  `π_j = ξ_j(ω + σ⁻¹)(Ŷ − Ŷⁿ) − ξ_j(1 + ωη)(p̂_j − p̂_jⁿ) + β E_t π_{j,t+1}`;
* `prop_3_8`: (B.27) / (2.27) for both sectors with the printed `κ_j`, `γ_j`;
  `prop_3_8_full`: the same derived from the linearised first-order conditions (B.32) and the
  Calvo law of motion; signs `kappa_pos`, `gamma1_pos`, `gamma2_neg`;
  `natural_relPrice` (the formula for `p̂_Rⁿ` on p. 204) and `natural_relPrice_eq_div`
  (`p̂_Rⁿ = p̂_2ⁿ/n_1`, p. 669); `relPrice_identity` (2.28).
* Aggregation: `gamma_weighted_sum`, `gamma_weighted_sum_eq_zero_iff` (`n₁γ₁ + n₂γ₂ = 0` iff
  `α₁ = α₂`), `aggregate_nkpc` (equal stickiness recovers (2.12)),
  `aggregate_compatible` (then stabilising the gap and aggregate inflation coincide), and
  `incompatible_of_unequal` (unequal stickiness: both can be stabilised only if the natural
  relative price never moves).

## Exact derivatives (the log-linearisations)

* `hasDerivAt_logCES2`: the Calvo price index (2.1)/(2.23) in logs has derivative
  `(1 − α) a' + α b'` at a common price — (2.26), and (3.5) of §3.2.
* `relPrice_index_linear`: the linearised nested price index `n₁p̂₁ + n₂p̂₂ = 0`,
  `n₁φ̂₁ + n₂φ̂₂ = 0` (needs `η ≠ 1`); `log_sectorDemand` (B.29) is exactly log-linear.
* `ces_aggregate_of_demands`, `ces_expenditure`, `ces_common_price`, `lowerNest_const`:
  the nested CES (2.22)–(2.23) identities and normalisations.
* `profit_gradient`: the derivative of the sectoral profit function is
  `(1 − θ) Y_j P_j^θ p^{−θ−1} (p − μ P s^j)`; `printed_B28_not_derivative` (E7).
* `realMC_B30`: the corrected (B.30) with `1/η` as an exact derivative;
  `printed_B30_fails` and `printed_display_iff` (E6).
* `bracket_hasDerivAt`, `summand_hasDerivAt`, `linearised_FOC`: (B.31) ⇒ (B.32) as the derivative
  of the (infinite) first-order condition at the zero-inflation steady state.

## Additions

* `nestedIndex_tendsto_cobbDouglas`, `nestedAgg_tendsto_cobbDouglas`: footnote 61, the
  Cobb–Douglas limit `η → 1` of (2.22)–(2.23), from `DixitStiglitz.tendsto_cobbDouglas`.
* `E_tsum_of_dominated`, `E_tsum_polyGeom`: `E_t` commutes with series dominated by a summable
  sequence, e.g. `qᵏ(C + Dk)`; `linFOC_iff_E_outside`: (B.32) with `E_t` outside the sum;
  `linearised_FOC_uncertain`, `linearised_FOC_B32_uncertain`: (B.31) ⇒ (B.32) under uncertainty
  (finite state space).

## Corrections (all confirmed)

* E6: (B.30) and the display after (B.33) print `η` where `1/η` is needed.
* E7: (B.28) prints the bracket `p − μ s^j`; it is `p − μ P s^j`.
* E8: p. 204 prints `ξ₁ = ξ₂` hence `n₁ξ₁ + n₂ξ₂ = 0`; the correct statement is
  `n₁γ₁ + n₂γ₂ = 0` (`printed_E8_false`: `n₁ξ₁ + n₂ξ₂ = ξ > 0`).
* E9: (2.25) prints `(1 − αβ)`; it is `(1 − α_j β)` (`printed_2_25_fails`).
* E30: the profit function on p. 202 uses the per-good demand index `Y_j/n_j`, not the sectoral
  total (B.29) (`revenue_per_good`); harmless after taking logs (`logdev_normalisation`).
-/

namespace Woodford.NominalRigidities.TwoSector

open Filter Topology
open QuadraticRoots (calvoXi calvoXi_pos)
open DixitStiglitz (finPriceIndex finAgg tendsto_cobbDouglas fin_demand_attains)
open DixitStiglitz.Nested (upperIndex upperIndex_eq)

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The Calvo block

The Calvo slope (B.33) `ξ_j = (1 − α_j)(1 − α_j β)/(α_j (1 + ωθ))` is
`QuadraticRoots.calvoXi α_j β (ωθ)`. -/

/-- Woodford (2003), (B.32), p. 668: the tail `∑_{k ≥ 0} q^{k+1} E_t ψ_{t+k+1}` of expected future
(quasi-differenced) inflation. -/
noncomputable def tailSeries (q : ℝ) (ψ : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun o => ∑' k, q ^ (k + 1) * 𝔼.E t (ψ (t + k + 1)) o

/-- Woodford (2003), (B.32), p. 668: the tail series is the forward series less its first term. -/
theorem tailSeries_eq {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {ψ : ℕ → Ω → ℝ}
    (hψ : ∀ t o, |ψ t o| ≤ M) (hψa : 𝔼.Adapted ψ) (t : ℕ) :
    tailSeries 𝔼 q ψ t = 𝔼.forwardSeries q ψ t - ψ t := by
  funext o
  have hs := 𝔼.forwardSeries_summable hq0 hq1 hψ t o
  have h0 : 𝔼.E t (ψ t) o = ψ t o := by rw [hψa t]
  change _ = ∑' k, q ^ k * 𝔼.E t (ψ (t + k)) o - ψ t o
  rw [hs.tsum_eq_zero_add, pow_zero, one_mul, add_zero, h0, add_sub_cancel_left]
  rfl

/-- Woodford (2003), (B.32), p. 668: the relative price at date `t + k` of a firm that reset its
price at `t`, `Q_t − ∑_{τ < k} ψ_{t+τ+1}` (reset price relative to the sector index at `t`, less
the cumulated sectoral (quasi-differenced) inflation since). -/
def resetRel (Q ψ : ℕ → Ω → ℝ) (t k : ℕ) : Ω → ℝ :=
  Q t - ∑ τ ∈ Finset.range k, ψ (t + τ + 1)

/-- Woodford (2003), (B.32), p. 668: the log-linearised first-order condition at date `t`,
`∑_k qᵏ E_t[(1 + ωθ) r_{t,k} − m_{t+k}] = 0`, where `m_T` is the (sectoral) real marginal cost gap
`ŝ_T − p̂_T` and `(1 + ωθ) r` collects the firm's relative price and the own-output effect
`−ωθ r` on its marginal cost (`foc_summand_rewrite`). -/
def LinFOC (q A : ℝ) (Q ψ m : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ o, ∑' k, q ^ k * 𝔼.E t (A • resetRel Q ψ t k - m (t + k)) o = 0

/-- Woodford (2003), (B.32), p. 668 (summation by parts): for bounded `ψ`,
`∑_k qᵏ ∑_{τ<k} E_t ψ_{t+τ+1} = (1 − q)⁻¹ ∑_k q^{k+1} E_t ψ_{t+k+1}`. -/
theorem hasSum_cumulated {q M : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {ψ : ℕ → Ω → ℝ}
    (hψ : ∀ t o, |ψ t o| ≤ M) (t : ℕ) (o : Ω) :
    HasSum (fun k => q ^ k * ∑ τ ∈ Finset.range k, 𝔼.E t (ψ (t + τ + 1)) o)
      (tailSeries 𝔼 q ψ t o / (1 - q)) := by
  set X : ℕ → ℝ := fun k => ∑ τ ∈ Finset.range k, 𝔼.E t (ψ (t + τ + 1)) o with hX
  have hinc : ∀ k, X (k + 1) - X k = 𝔼.E t (ψ (t + k + 1)) o := fun k => by
    simp only [hX, Finset.sum_range_succ, add_sub_cancel_left]
  have hb : ∀ k, |X (k + 1) - X k| ≤ M := fun k => by
    rw [hinc]; exact 𝔼.abs_E_le (hψ _) t o
  obtain ⟨hs1, -, hval⟩ := ForwardSolution.tsum_weights_by_parts hq0 hq1 X hb
  have hq : (1 - q) ≠ 0 := by linarith
  have hX0 : X 0 = 0 := by simp [hX]
  have htail : ∑' k, q ^ (k + 1) * (X (k + 1) - X k) = tailSeries 𝔼 q ψ t o := by
    unfold tailSeries
    exact tsum_congr fun k => by rw [hinc]
  rw [hX0, zero_add, htail] at hval
  have h := (hs1.div_const (1 - q)).hasSum
  rw [tsum_div_const, hval] at h
  convert h using 1
  funext k
  simp only [hX]
  field_simp

/-- Woodford (2003), (B.32), p. 668: the log-linearised first-order condition (B.32) holds at `t`
iff `Q_t = c ∑ qᵏ E_t m_{t+k} + ∑_{k ≥ 0} q^{k+1} E_t ψ_{t+k+1}` with `c = (1 − q)/A`
(reset price known at `t`; `ψ`, `m` bounded). -/
theorem linFOC_iff {q A Mψ Mm : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hA : 0 < A)
    {Q ψ m : ℕ → Ω → ℝ} (hψ : ∀ t o, |ψ t o| ≤ Mψ) (hm : ∀ t o, |m t o| ≤ Mm) (t : ℕ)
    (hQ : 𝔼.E t (Q t) = Q t) :
    LinFOC 𝔼 q A Q ψ m t ↔
      Q t = ((1 - q) / A) • 𝔼.forwardSeries q m t + tailSeries 𝔼 q ψ t := by
  have key : ∀ o, ∑' k, q ^ k * 𝔼.E t (A • resetRel Q ψ t k - m (t + k)) o =
      A * Q t o / (1 - q) - A * (tailSeries 𝔼 q ψ t o / (1 - q)) -
        𝔼.forwardSeries q m t o := by
    intro o
    have hterm : ∀ k, q ^ k * 𝔼.E t (A • resetRel Q ψ t k - m (t + k)) o =
        q ^ k * (A * Q t o) - A * (q ^ k * ∑ τ ∈ Finset.range k, 𝔼.E t (ψ (t + τ + 1)) o) -
          q ^ k * 𝔼.E t (m (t + k)) o := by
      intro k
      have hE : 𝔼.E t (A • resetRel Q ψ t k - m (t + k)) o =
          A * (Q t o - ∑ τ ∈ Finset.range k, 𝔼.E t (ψ (t + τ + 1)) o) -
            𝔼.E t (m (t + k)) o := by
        simp only [resetRel, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_apply, hQ]
      rw [hE]; ring
    have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_right (A * Q t o)
    have hcum := (hasSum_cumulated 𝔼 hq0 hq1 hψ t o).mul_left A
    have hF := (𝔼.forwardSeries_summable hq0 hq1 hm t o).hasSum
    have hall := (hgeo.sub hcum).sub hF
    rw [funext hterm, hall.tsum_eq]
    change _ = A * Q t o / (1 - q) - A * (tailSeries 𝔼 q ψ t o / (1 - q)) -
      ∑' k, q ^ k * 𝔼.E t (m (t + k)) o
    rw [inv_mul_eq_div, mul_comm, ← mul_div_assoc, mul_comm (Q t o)]
  have hq : (1 - q) ≠ 0 := by linarith
  constructor
  · intro h
    funext o
    have := h o
    rw [key o] at this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp at this ⊢
    linarith
  · intro h o
    rw [key o, h]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-- Woodford (2003), (2.26) and (B.33), p. 668: the Calvo law of motion `α ψ_t = (1 − α) Q_t`
together with the relative-price form of the first-order condition is equivalent to the sectoral
inflation equation `ψ_t = ξ m_t + β E_t ψ_{t+1}` together with `Q_t = α/(1 − α) ψ_t`
(bounded adapted `ψ`, `m`; any `ExpectationSystem`). -/
theorem relative_law_iff_nkpc {α β ω θ Mψ Mm : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hA : 0 < 1 + ω * θ) {Q ψ m : ℕ → Ω → ℝ} (hψ : ∀ t o, |ψ t o| ≤ Mψ)
    (hψa : 𝔼.Adapted ψ) (hm : ∀ t o, |m t o| ≤ Mm) (hma : 𝔼.Adapted m) :
    ((∀ t, Q t = ((1 - α * β) / (1 + ω * θ)) • 𝔼.forwardSeries (α * β) m t +
        tailSeries 𝔼 (α * β) ψ t) ∧ ∀ t, α • ψ t = (1 - α) • Q t) ↔
      ((∀ t, ψ t = calvoXi α β (ω * θ) • m t + β • 𝔼.E t (ψ (t + 1))) ∧
        ∀ t, Q t = (α / (1 - α)) • ψ t) := by
  set q := α * β with hqdef
  set c := (1 - α * β) / (1 + ω * θ) with hc
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by nlinarith
  have h1α : (1 - α) ≠ 0 := by linarith
  have hα : α ≠ 0 := hα0.ne'
  have hAne : 1 + ω * θ ≠ 0 := hA.ne'
  -- the forward recursions of the two forward series
  have hFm := 𝔼.forwardSeries_solves hq0 hq1 hm hma
  have hFψ := 𝔼.forwardSeries_solves hq0 hq1 hψ hψa
  have htail := tailSeries_eq 𝔼 hq0 hq1 hψ hψa
  -- the relative form rewritten recursively, pointwise
  set R : ℕ → Ω → ℝ := fun t => c • 𝔼.forwardSeries q m t + tailSeries 𝔼 q ψ t with hR
  have hRrec : ∀ t o, R t o = c * m t o + q * 𝔼.E t (R (t + 1)) o + q * 𝔼.E t (ψ (t + 1)) o := by
    intro t o
    have e1 := congrFun (hFm t) o
    have e2 := congrFun (hFψ t) o
    have hR1 : R (t + 1) = c • 𝔼.forwardSeries q m (t + 1) + 𝔼.forwardSeries q ψ (t + 1) -
        ψ (t + 1) := by
      simp only [hR, htail]; abel
    have hE : 𝔼.E t (R (t + 1)) o = c * 𝔼.E t (𝔼.forwardSeries q m (t + 1)) o +
        𝔼.E t (𝔼.forwardSeries q ψ (t + 1)) o - 𝔼.E t (ψ (t + 1)) o := by
      rw [hR1]; simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2
    have lhs : R t o = c * 𝔼.forwardSeries q m t o + (𝔼.forwardSeries q ψ t o - ψ t o) := by
      simp only [hR, htail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [lhs, hE, e1, e2]
    ring
  have hRb : BoundedProc R := by
    obtain ⟨B1, hB1⟩ := 𝔼.forwardSeries_bounded hq0 hq1 hm
    obtain ⟨B2, hB2⟩ := 𝔼.forwardSeries_bounded hq0 hq1 hψ
    refine ⟨|c| * B1 + B2 + Mψ, fun t o => ?_⟩
    simp only [hR, htail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    calc |c * 𝔼.forwardSeries q m t o + (𝔼.forwardSeries q ψ t o - ψ t o)|
        ≤ |c * 𝔼.forwardSeries q m t o| + (|𝔼.forwardSeries q ψ t o| + |ψ t o|) :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ ≤ |c| * B1 + (B2 + Mψ) := by
          rw [abs_mul]
          gcongr
          · exact hB1 t o
          · exact hB2 t o
          · exact hψ t o
      _ = |c| * B1 + B2 + Mψ := by ring
  have hξc : (α / (1 - α)) * calvoXi α β (ω * θ) = c := by
    simp only [calvoXi, hc]; field_simp
  have hβq : (α / (1 - α)) * β = q * (α / (1 - α) + 1) := by
    simp only [hqdef]; field_simp; ring
  constructor
  · rintro ⟨hrel, hlaw⟩
    have hQψ : ∀ t, Q t = (α / (1 - α)) • ψ t := fun t => by
      funext o
      have := congrFun (hlaw t) o
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      field_simp
      linarith
    refine ⟨fun t => ?_, hQψ⟩
    funext o
    have hQR : ∀ t, Q t = R t := fun t => hrel t
    have h1 := hRrec t o
    rw [← hQR t, ← hQR (t + 1), hQψ t, hQψ (t + 1)] at h1
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_smul] at h1 ⊢
    have h2 : ψ t o = (1 - α) / α * (α / (1 - α) * ψ t o) := by field_simp
    rw [h2, h1]
    simp only [calvoXi, hqdef, hc]
    field_simp
    ring
  · rintro ⟨hnk, hQψ⟩
    refine ⟨fun t => ?_, fun t => ?_⟩
    · -- uniqueness of the bounded solution of `z_t = q E_t z_{t+1} + u_t`
      have hsolQ : ∀ t, Q t = q • 𝔼.E t (Q (t + 1)) +
          (fun o => c * m t o + q * 𝔼.E t (ψ (t + 1)) o) := by
        intro t
        funext o
        rw [hQψ t, hQψ (t + 1)]
        have := congrFun (hnk t) o
        simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, map_smul] at this ⊢
        rw [this, mul_add, ← mul_assoc, hξc, ← mul_assoc, hβq]
        ring
      have hsolR : ∀ t, R t = q • 𝔼.E t (R (t + 1)) +
          (fun o => c * m t o + q * 𝔼.E t (ψ (t + 1)) o) := by
        intro t
        funext o
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [hRrec t o]
        ring
      have hQb : BoundedProc Q := by
        refine ⟨|α / (1 - α)| * Mψ, fun t o => ?_⟩
        rw [hQψ t, Pi.smul_apply, smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hψ t o) (abs_nonneg _)
      have habs : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
      have := 𝔼.forward_unique habs hsolQ hsolR hQb hRb
      exact congrFun this t
    · funext o
      rw [hQψ t]
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp

/-! ### The level form (2.25) and error E9 -/

/-- Woodford (2003), eq. (2.25), p. 202, with the coefficient `(1 − α_j β)` (error E9: the book
prints `(1 − αβ)`): `log p*_t = (1 − α_j β)/(1 + ωθ) ∑ (α_j β)ᵏ E_t[log μ + log S_{t+k} +
ωθ log P_{t+k}]`, `S` nominal marginal cost and `P` the sectoral price index. -/
def Eq225 (α β ω θ lmu : ℝ) (pstar x lS : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  pstar t = ((1 - α * β) / (1 + ω * θ)) •
    fun o => ∑' k, (α * β) ^ k * 𝔼.E t ((fun _ => lmu) + lS (t + k) + (ω * θ) • x (t + k)) o

/-- Woodford (2003), (2.25), p. 202: `E_t log P_{t+k} = log P_t + ∑_{τ<k} E_t π_{t+τ+1}` for an
adapted price level. -/
theorem E_level {x ψ : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x) (hxψ : ∀ T, x (T + 1) = x T + ψ (T + 1))
    (t k : ℕ) :
    𝔼.E t (x (t + k)) = x t + ∑ τ ∈ Finset.range k, 𝔼.E t (ψ (t + τ + 1)) := by
  induction k with
  | zero => simp [hx t]
  | succ k ih =>
    rw [← add_assoc, hxψ, map_add, ih, Finset.sum_range_succ, add_assoc]

/-- Woodford (2003), (2.25), p. 202 and (B.32), p. 668: the level form (2.25) holds at `t` iff
the relative reset price satisfies `log p*_t − log P_t = c ∑ qᵏ E_t m_{t+k} +
∑ q^{k+1} E_t π_{t+k+1}`, where `m_T = log μ + log S_T − log P_T` (bounded inflation and `m`). -/
theorem level_iff_relative {α β ω θ lmu Mψ Mm : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hA : 0 < 1 + ω * θ) {pstar x lS ψ m : ℕ → Ω → ℝ} (hx : 𝔼.Adapted x)
    (hxψ : ∀ T, x (T + 1) = x T + ψ (T + 1)) (hψ : ∀ t o, |ψ t o| ≤ Mψ)
    (hm : ∀ t o, |m t o| ≤ Mm) (hmdef : ∀ T, m T = (fun _ => lmu) + lS T - x T) (t : ℕ) :
    Eq225 𝔼 α β ω θ lmu pstar x lS t ↔
      pstar t - x t = ((1 - α * β) / (1 + ω * θ)) • 𝔼.forwardSeries (α * β) m t +
        tailSeries 𝔼 (α * β) ψ t := by
  set q := α * β with hqdef
  set A := 1 + ω * θ with hAdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by nlinarith
  have hq : (1 - q) ≠ 0 := by linarith
  have hsum : ∀ o, HasSum
      (fun k => q ^ k * 𝔼.E t ((fun _ => lmu) + lS (t + k) + (ω * θ) • x (t + k)) o)
      (𝔼.forwardSeries q m t o + A * x t o / (1 - q) +
        A * (tailSeries 𝔼 q ψ t o / (1 - q))) := by
    intro o
    have hterm : ∀ k, q ^ k * 𝔼.E t ((fun _ => lmu) + lS (t + k) + (ω * θ) • x (t + k)) o =
        q ^ k * 𝔼.E t (m (t + k)) o + q ^ k * (A * x t o) +
          A * (q ^ k * ∑ τ ∈ Finset.range k, 𝔼.E t (ψ (t + τ + 1)) o) := by
      intro k
      have harg : (fun _ => lmu) + lS (t + k) + (ω * θ) • x (t + k) =
          m (t + k) + A • x (t + k) := by
        rw [hmdef, hAdef, add_smul, one_smul]; abel
      rw [harg, map_add, map_smul, E_level 𝔼 hx hxψ]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      ring
    rw [funext hterm]
    have hF := (𝔼.forwardSeries_summable hq0 hq1 hm t o).hasSum
    have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_right (A * x t o)
    have hcum := (hasSum_cumulated 𝔼 hq0 hq1 hψ t o).mul_left A
    convert (hF.add hgeo).add hcum using 1
    simp only [ExpectationSystem.forwardSeries]
    field_simp
  have key : ∀ o, (((1 - q) / A) • fun o =>
      ∑' k, q ^ k * 𝔼.E t ((fun _ => lmu) + lS (t + k) + (ω * θ) • x (t + k)) o) o =
      (1 - q) / A * 𝔼.forwardSeries q m t o + x t o + tailSeries 𝔼 q ψ t o := by
    intro o
    rw [Pi.smul_apply, smul_eq_mul, (hsum o).tsum_eq]
    field_simp
  constructor
  · intro h
    funext o
    have := congrFun h o
    rw [key o] at this
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · intro h
    funext o
    have := congrFun h o
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [key o]
    linarith

/-- Woodford (2003), (2.25), p. 202 (error E9): with the printed coefficient `(1 − α'β)`,
`α' ≠ α_j`, the formula fails at the zero-inflation steady state `log P_t = log p*_t = x̄ ≠ 0`,
`m ≡ 0`, where the corrected (2.25) holds: the printed right-hand side is
`x̄ (1 − α'β)/(1 − α_j β) ≠ x̄`. -/
theorem printed_2_25_fails [Nonempty Ω] {αj α' β ω θ lmu xbar : ℝ} (hαj0 : 0 < αj)
    (hαj1 : αj < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hA : 0 < 1 + ω * θ) (hne : α' ≠ αj)
    (hx : xbar ≠ 0) (t : ℕ) :
    Eq225 𝔼 αj β ω θ lmu (fun _ _ => xbar) (fun _ _ => xbar) (fun _ _ => xbar - lmu) t ∧
      (fun (_ : Ω) => xbar) ≠ ((1 - α' * β) / (1 + ω * θ)) • fun o => ∑' k, (αj * β) ^ k *
        𝔼.E t ((fun _ => lmu) + (fun _ => xbar - lmu) + (ω * θ) • fun _ => xbar) o := by
  set q := αj * β with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by nlinarith
  have hq : (1 - q) ≠ 0 := by linarith
  have harg : ((fun _ => lmu) + (fun _ => xbar - lmu) + (ω * θ) • fun _ => xbar :
      Ω → ℝ) = fun _ => (1 + ω * θ) * xbar := by
    funext o; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hval : ∀ o, ∑' k, q ^ k * 𝔼.E t ((fun _ => lmu) + (fun _ => xbar - lmu) +
      (ω * θ) • fun _ => xbar) o = (1 + ω * θ) * xbar / (1 - q) := by
    intro o
    rw [harg, 𝔼.const, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1]
    field_simp
  refine ⟨?_, fun h => ?_⟩
  · funext o
    change xbar = (1 - q) / (1 + ω * θ) * ∑' k, q ^ k * 𝔼.E t ((fun _ => lmu) +
      (fun _ => xbar - lmu) + (ω * θ) • fun _ => xbar) o
    rw [hval o]
    field_simp
  · obtain ⟨o⟩ := ‹Nonempty Ω›
    have h1 : xbar = (1 - α' * β) / (1 + ω * θ) * ∑' k, q ^ k * 𝔼.E t ((fun _ => lmu) +
        (fun _ => xbar - lmu) + (ω * θ) • fun _ => xbar) o := congrFun h o
    rw [hval o] at h1
    have h2 : xbar * (1 - q) = (1 - α' * β) * xbar := by
      calc xbar * (1 - q) = (1 - α' * β) / (1 + ω * θ) * ((1 + ω * θ) * xbar / (1 - q)) *
            (1 - q) := by rw [← h1]
        _ = _ := by field_simp
    have h3 : (α' - αj) * β * xbar = 0 := by rw [hqdef] at h2; linear_combination h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · exact hne (by linarith)
      · linarith
    · exact hx h4

/-! ### Proposition 3.8 -/

/-- Woodford (2003), Proposition 3.8, eq. (2.27), p. 203 and (B.27), p. 666:
`κ_j = (1 − α_j)(1 − α_j β)/α_j · (ω + σ⁻¹)/(1 + ωθ)`. -/
noncomputable def kappaJ (α β ω θ σ : ℝ) : ℝ :=
  (1 - α) * (1 - α * β) / α * ((ω + σ⁻¹) / (1 + ω * θ))

/-- Woodford (2003), Proposition 3.8, p. 203: `γ₁ = n₂ (1 − α₁)(1 − α₁β)/α₁ · (1 + ωη)/(1 + ωθ)`
with `n₂ = 1 − n₁`. -/
noncomputable def gamma1 (n1 α1 β ω θ η : ℝ) : ℝ :=
  (1 - n1) * ((1 - α1) * (1 - α1 * β) / α1) * ((1 + ω * η) / (1 + ω * θ))

/-- Woodford (2003), Proposition 3.8, p. 203:
`γ₂ = −n₁ (1 − α₂)(1 − α₂β)/α₂ · (1 + ωη)/(1 + ωθ)`. -/
noncomputable def gamma2 (n1 α2 β ω θ η : ℝ) : ℝ :=
  -n1 * ((1 - α2) * (1 - α2 * β) / α2) * ((1 + ω * η) / (1 + ω * θ))

/-- Woodford (2003), Proposition 3.8, p. 203: `κ_j = ξ_j (ω + σ⁻¹)`. -/
theorem kappaJ_eq {α β ω θ σ : ℝ} (hα : α ≠ 0) (hA : 1 + ω * θ ≠ 0) :
    kappaJ α β ω θ σ = calvoXi α β (ω * θ) * (ω + σ⁻¹) := by
  simp only [kappaJ, calvoXi]; field_simp

/-- Woodford (2003), App. B.7, p. 669: `γ₁ = n₂ ξ₁ (1 + ωη)`. -/
theorem gamma1_eq {n1 α1 β ω θ η : ℝ} (hα : α1 ≠ 0) (hA : 1 + ω * θ ≠ 0) :
    gamma1 n1 α1 β ω θ η = (1 - n1) * calvoXi α1 β (ω * θ) * (1 + ω * η) := by
  simp only [gamma1, calvoXi]; field_simp

/-- Woodford (2003), App. B.7, p. 669: `γ₂ = −n₁ ξ₂ (1 + ωη)`. -/
theorem gamma2_eq {n1 α2 β ω θ η : ℝ} (hα : α2 ≠ 0) (hA : 1 + ω * θ ≠ 0) :
    gamma2 n1 α2 β ω θ η = -n1 * calvoXi α2 β (ω * θ) * (1 + ω * η) := by
  simp only [gamma2, calvoXi]; field_simp

/-- Woodford (2003), Proposition 3.8, p. 203: `κ_j > 0` (given `ω + σ⁻¹ > 0`). -/
theorem kappa_pos {α β ω θ σ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ1 : β < 1)
    (hA : 0 < 1 + ω * θ) (hωσ : 0 < ω + σ⁻¹) : 0 < kappaJ α β ω θ σ := by
  rw [kappaJ_eq hα0.ne' hA.ne']
  exact mul_pos (calvoXi_pos hα0 hα1 hβ1 hA) hωσ

/-- Woodford (2003), Proposition 3.8, p. 203: `γ₁ > 0` (given `0 < n₁ < 1`, `1 + ωη > 0`). -/
theorem gamma1_pos {n1 α1 β ω θ η : ℝ} (hn1 : n1 < 1) (hα0 : 0 < α1) (hα1 : α1 < 1)
    (hβ1 : β < 1) (hA : 0 < 1 + ω * θ) (hη : 0 < 1 + ω * η) :
    0 < gamma1 n1 α1 β ω θ η := by
  rw [gamma1_eq hα0.ne' hA.ne']
  have := calvoXi_pos hα0 hα1 hβ1 hA
  have : 0 < 1 - n1 := by linarith
  positivity

/-- Woodford (2003), Proposition 3.8, p. 203: `γ₂ < 0` (given `0 < n₁`, `1 + ωη > 0`). -/
theorem gamma2_neg {n1 α2 β ω θ η : ℝ} (hn0 : 0 < n1) (hα0 : 0 < α2) (hα1 : α2 < 1)
    (hβ1 : β < 1) (hA : 0 < 1 + ω * θ) (hη : 0 < 1 + ω * η) :
    gamma2 n1 α2 β ω θ η < 0 := by
  rw [gamma2_eq hα0.ne' hA.ne']
  have := calvoXi_pos hα0 hα1 hβ1 hA
  have : 0 < n1 * calvoXi α2 β (ω * θ) * (1 + ω * η) := by positivity
  linarith

/-- Woodford (2003), App. B.7, p. 669 (the display after (B.33), with (B.30) corrected, E6):
`ŝ_j − p̂_j = (ω + σ⁻¹)(Ŷ − Ŷⁿ) − (1 + ωη)(p̂_j − p̂_jⁿ)`, from
`ŝ_j = ω(Ŷ_j − Ŷ_jⁿ) + σ⁻¹(Ŷ − Ŷⁿ) + p̂_jⁿ` and the demands `Ŷ_j = φ̂_j + Ŷ − η p̂_j`,
`Ŷ_jⁿ = φ̂_j + Ŷⁿ − η p̂_jⁿ`. -/
theorem realMC_gap {ω σ η s p pn Y Yn Yj Yjn φ : ℝ}
    (hB30 : s = ω * (Yj - Yjn) + σ⁻¹ * (Y - Yn) + pn) (hd : Yj = φ + Y - η * p)
    (hdn : Yjn = φ + Yn - η * pn) :
    s - p = (ω + σ⁻¹) * (Y - Yn) - (1 + ω * η) * (p - pn) := by
  rw [hB30, hd, hdn]; ring

/-- Woodford (2003), App. B.7, pp. 668–669: substituting the real-marginal-cost display into
(B.33): `π_j = ξ_j(ω + σ⁻¹)(Ŷ − Ŷⁿ) − ξ_j(1 + ωη)(p̂_j − p̂_jⁿ) + β E_t π_{j,t+1}`. -/
theorem sector_inflation {ξ β ω σ η : ℝ} {π s p pn Y Yn Yj Yjn φ : ℕ → Ω → ℝ}
    (hB33 : ∀ t, π t = ξ • (s t - p t) + β • 𝔼.E t (π (t + 1)))
    (hB30 : ∀ t o, s t o = ω * (Yj t o - Yjn t o) + σ⁻¹ * (Y t o - Yn t o) + pn t o)
    (hd : ∀ t o, Yj t o = φ t o + Y t o - η * p t o)
    (hdn : ∀ t o, Yjn t o = φ t o + Yn t o - η * pn t o) (t : ℕ) :
    π t = (ξ * (ω + σ⁻¹)) • (Y t - Yn t) - (ξ * (1 + ω * η)) • (p t - pn t) +
      β • 𝔼.E t (π (t + 1)) := by
  funext o
  have h := congrFun (hB33 t) o
  have hg := realMC_gap (hB30 t o) (hd t o) (hdn t o)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  rw [h, hg]; ring

/-- Woodford (2003), App. B.7, p. 669: with `n₁ p̂₁ + n₂ p̂₂ = 0` (`n₂ = 1 − n₁`), the sectoral
relative prices are `p̂₁ = −n₂ p̂_R`, `p̂₂ = n₁ p̂_R`, where `p̂_R = p̂₂ − p̂₁`. -/
theorem relPrices_of_index {n1 p1 p2 : ℝ} (h : n1 * p1 + (1 - n1) * p2 = 0) :
    p1 = -(1 - n1) * (p2 - p1) ∧ p2 = n1 * (p2 - p1) := by
  constructor <;> linear_combination h

/-- Woodford (2003), **Proposition 3.8**, eq. (2.27), p. 203 and (B.27), p. 666: from the
sectoral inflation equations (B.33), the corrected (B.30), the sectoral demands (B.29) and the
linearised price index (`n₁p̂₁ + n₂p̂₂ = 0`, actual and natural), each sector's inflation obeys
`π_j = κ_j(Ŷ − Ŷⁿ) + γ_j(p̂_R − p̂_Rⁿ) + β E_t π_{j,t+1}` with the printed `κ_j`, `γ_j`. -/
theorem prop_3_8 {n1 α1 α2 β ω θ σ η : ℝ} (hα1 : α1 ≠ 0) (hα2 : α2 ≠ 0) (hA : 1 + ω * θ ≠ 0)
    {π1 π2 s1 s2 p1 p2 p1n p2n Y Yn Y1 Y2 Y1n Y2n φ1 φ2 : ℕ → Ω → ℝ}
    (hB33a : ∀ t, π1 t = calvoXi α1 β (ω * θ) • (s1 t - p1 t) + β • 𝔼.E t (π1 (t + 1)))
    (hB33b : ∀ t, π2 t = calvoXi α2 β (ω * θ) • (s2 t - p2 t) + β • 𝔼.E t (π2 (t + 1)))
    (hB30a : ∀ t o, s1 t o = ω * (Y1 t o - Y1n t o) + σ⁻¹ * (Y t o - Yn t o) + p1n t o)
    (hB30b : ∀ t o, s2 t o = ω * (Y2 t o - Y2n t o) + σ⁻¹ * (Y t o - Yn t o) + p2n t o)
    (hda : ∀ t o, Y1 t o = φ1 t o + Y t o - η * p1 t o)
    (hdb : ∀ t o, Y2 t o = φ2 t o + Y t o - η * p2 t o)
    (hdna : ∀ t o, Y1n t o = φ1 t o + Yn t o - η * p1n t o)
    (hdnb : ∀ t o, Y2n t o = φ2 t o + Yn t o - η * p2n t o)
    (hidx : ∀ t o, n1 * p1 t o + (1 - n1) * p2 t o = 0)
    (hidxn : ∀ t o, n1 * p1n t o + (1 - n1) * p2n t o = 0) (t : ℕ) :
    π1 t = kappaJ α1 β ω θ σ • (Y t - Yn t) +
        gamma1 n1 α1 β ω θ η • ((p2 t - p1 t) - (p2n t - p1n t)) + β • 𝔼.E t (π1 (t + 1)) ∧
      π2 t = kappaJ α2 β ω θ σ • (Y t - Yn t) +
        gamma2 n1 α2 β ω θ η • ((p2 t - p1 t) - (p2n t - p1n t)) + β • 𝔼.E t (π2 (t + 1)) := by
  have e1 := sector_inflation 𝔼 hB33a hB30a hda hdna t
  have e2 := sector_inflation 𝔼 hB33b hB30b hdb hdnb t
  rw [kappaJ_eq hα1 hA, kappaJ_eq hα2 hA, gamma1_eq hα1 hA, gamma2_eq hα2 hA]
  constructor
  · rw [e1]; funext o
    have h1 := hidx t o
    have h2 := hidxn t o
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (calvoXi α1 β (ω * θ) * (1 + ω * η)) * (h2 - h1)
  · rw [e2]; funext o
    have h1 := hidx t o
    have h2 := hidxn t o
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (calvoXi α2 β (ω * θ) * (1 + ω * η)) * (h2 - h1)

/-- Woodford (2003), **Proposition 3.8** derived in full (App. B.7, pp. 667–669): for each sector
the linearised first-order condition (B.32) of the price-setters (reset price `Q_j` relative to
the sectoral index, known when set) and the Calvo law of motion (2.26) `α_j π_j = (1 − α_j) Q_j`
imply (B.33) (via `linFOC_iff` and `relative_law_iff_nkpc`); together with the corrected (B.30),
(B.29) and the linearised price index this gives (B.27) for both sectors. -/
theorem prop_3_8_full {n1 α1 α2 β ω θ σ η M1 M2 K1 K2 : ℝ} (ha10 : 0 < α1) (ha11 : α1 < 1)
    (ha20 : 0 < α2) (ha21 : α2 < 1) (hβ0 : 0 < β) (hβ1 : β < 1) (hA : 0 < 1 + ω * θ)
    {Q1 Q2 π1 π2 s1 s2 p1 p2 p1n p2n Y Yn Y1 Y2 Y1n Y2n φ1 φ2 : ℕ → Ω → ℝ}
    (hfoc1 : ∀ t, LinFOC 𝔼 (α1 * β) (1 + ω * θ) Q1 π1 (fun T => s1 T - p1 T) t)
    (hfoc2 : ∀ t, LinFOC 𝔼 (α2 * β) (1 + ω * θ) Q2 π2 (fun T => s2 T - p2 T) t)
    (hQ1 : 𝔼.Adapted Q1) (hQ2 : 𝔼.Adapted Q2)
    (hlaw1 : ∀ t, α1 • π1 t = (1 - α1) • Q1 t) (hlaw2 : ∀ t, α2 • π2 t = (1 - α2) • Q2 t)
    (hπ1 : ∀ t o, |π1 t o| ≤ M1) (hπ2 : ∀ t o, |π2 t o| ≤ M2)
    (hπ1a : 𝔼.Adapted π1) (hπ2a : 𝔼.Adapted π2)
    (hm1 : ∀ t o, |s1 t o - p1 t o| ≤ K1) (hm2 : ∀ t o, |s2 t o - p2 t o| ≤ K2)
    (hm1a : 𝔼.Adapted (fun T => s1 T - p1 T)) (hm2a : 𝔼.Adapted (fun T => s2 T - p2 T))
    (hB30a : ∀ t o, s1 t o = ω * (Y1 t o - Y1n t o) + σ⁻¹ * (Y t o - Yn t o) + p1n t o)
    (hB30b : ∀ t o, s2 t o = ω * (Y2 t o - Y2n t o) + σ⁻¹ * (Y t o - Yn t o) + p2n t o)
    (hda : ∀ t o, Y1 t o = φ1 t o + Y t o - η * p1 t o)
    (hdb : ∀ t o, Y2 t o = φ2 t o + Y t o - η * p2 t o)
    (hdna : ∀ t o, Y1n t o = φ1 t o + Yn t o - η * p1n t o)
    (hdnb : ∀ t o, Y2n t o = φ2 t o + Yn t o - η * p2n t o)
    (hidx : ∀ t o, n1 * p1 t o + (1 - n1) * p2 t o = 0)
    (hidxn : ∀ t o, n1 * p1n t o + (1 - n1) * p2n t o = 0) (t : ℕ) :
    π1 t = kappaJ α1 β ω θ σ • (Y t - Yn t) +
        gamma1 n1 α1 β ω θ η • ((p2 t - p1 t) - (p2n t - p1n t)) + β • 𝔼.E t (π1 (t + 1)) ∧
      π2 t = kappaJ α2 β ω θ σ • (Y t - Yn t) +
        gamma2 n1 α2 β ω θ η • ((p2 t - p1 t) - (p2n t - p1n t)) + β • 𝔼.E t (π2 (t + 1)) := by
  have hm1' : ∀ t o, |(fun T => s1 T - p1 T) t o| ≤ K1 := fun t o => by
    simpa using hm1 t o
  have hm2' : ∀ t o, |(fun T => s2 T - p2 T) t o| ≤ K2 := fun t o => by
    simpa using hm2 t o
  have hq10 : 0 ≤ α1 * β := by positivity
  have hq11 : α1 * β < 1 := by nlinarith
  have hq20 : 0 ≤ α2 * β := by positivity
  have hq21 : α2 * β < 1 := by nlinarith
  have hrel1 : ∀ t, Q1 t = ((1 - α1 * β) / (1 + ω * θ)) •
      𝔼.forwardSeries (α1 * β) (fun T => s1 T - p1 T) t + tailSeries 𝔼 (α1 * β) π1 t :=
    fun t => (linFOC_iff 𝔼 hq10 hq11 hA hπ1 hm1' t (hQ1 t)).mp (hfoc1 t)
  have hrel2 : ∀ t, Q2 t = ((1 - α2 * β) / (1 + ω * θ)) •
      𝔼.forwardSeries (α2 * β) (fun T => s2 T - p2 T) t + tailSeries 𝔼 (α2 * β) π2 t :=
    fun t => (linFOC_iff 𝔼 hq20 hq21 hA hπ2 hm2' t (hQ2 t)).mp (hfoc2 t)
  have hn1 := ((relative_law_iff_nkpc 𝔼 ha10 ha11 hβ0 hβ1 hA hπ1 hπ1a hm1' hm1a).mp
    ⟨hrel1, hlaw1⟩).1
  have hn2 := ((relative_law_iff_nkpc 𝔼 ha20 ha21 hβ0 hβ1 hA hπ2 hπ2a hm2' hm2a).mp
    ⟨hrel2, hlaw2⟩).1
  exact prop_3_8 𝔼 ha10.ne' ha20.ne' hA.ne' hn1 hn2 hB30a hB30b hda hdb hdna hdnb hidx hidxn t

/-- Woodford (2003), p. 204: the natural relative price
`p̂_Rⁿ = (1/η)[(φ̂₂ − φ̂₁) − (Ŷ₂ⁿ − Ŷ₁ⁿ)]` (from the natural sectoral demands). -/
theorem natural_relPrice {η p1n p2n φ1 φ2 Yn Y1n Y2n : ℝ} (hη : η ≠ 0)
    (hdna : Y1n = φ1 + Yn - η * p1n) (hdnb : Y2n = φ2 + Yn - η * p2n) :
    p2n - p1n = (1 / η) * ((φ2 - φ1) - (Y2n - Y1n)) := by
  rw [hdna, hdnb]; field_simp; ring

/-- Woodford (2003), App. B.7, p. 669: `p̂_Rⁿ = n₁⁻¹ p̂₂ⁿ` (from `n₁p̂₁ⁿ + n₂p̂₂ⁿ = 0`). -/
theorem natural_relPrice_eq_div {n1 p1n p2n : ℝ} (hn : n1 ≠ 0)
    (h : n1 * p1n + (1 - n1) * p2n = 0) : p2n - p1n = p2n / n1 := by
  field_simp; linear_combination -h

/-- Woodford (2003), eq. (2.28), p. 204: `p̂_{R,t} = p̂_{R,t−1} + π_{2t} − π_{1t}`, where
`p̂_R = log P₂ − log P₁` and `π_j = log P_{j,t} − log P_{j,t−1}` (an identity). -/
theorem relPrice_identity (lP1 lP2 : ℕ → Ω → ℝ) (t : ℕ) :
    lP2 (t + 1) - lP1 (t + 1) =
      (lP2 t - lP1 t) + (lP2 (t + 1) - lP2 t) - (lP1 (t + 1) - lP1 t) := by
  abel

/-- Woodford (2003), p. 204: when `n₁p̂₁ + n₂p̂₂ = 0` with `p̂_j = log P_j − log P`, the aggregate
log price is the size-weighted average `log P = n₁ log P₁ + n₂ log P₂`, so aggregate inflation
is `π = n₁π₁ + n₂π₂`. -/
theorem aggregate_price {n1 lP lP1 lP2 : ℝ} (h : n1 * (lP1 - lP) + (1 - n1) * (lP2 - lP) = 0) :
    lP = n1 * lP1 + (1 - n1) * lP2 := by
  linear_combination -h

/-- Woodford (2003), p. 204 (with error E8 corrected): the size-weighted sum of the relative-price
coefficients is `n₁γ₁ + n₂γ₂ = n₁n₂ (1 + ωη)/(1 + ωθ) · (g(α₁) − g(α₂))`,
`g(α) = (1 − α)(1 − αβ)/α`. -/
theorem gamma_weighted_sum (n1 α1 α2 β ω θ η : ℝ) :
    n1 * gamma1 n1 α1 β ω θ η + (1 - n1) * gamma2 n1 α2 β ω θ η =
      n1 * (1 - n1) * ((1 + ω * η) / (1 + ω * θ)) *
        ((1 - α1) * (1 - α1 * β) / α1 - (1 - α2) * (1 - α2 * β) / α2) := by
  simp only [gamma1, gamma2]; ring

/-- Woodford (2003), p. 188 and p. 204: `g(α) = (1 − α)(1 − αβ)/α` is strictly decreasing on
`(0, 1)`, as `g(a) − g(b) = (b − a)(1 − abβ)/(ab)`. -/
theorem calvoSlope_strictAnti {a b β : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) : (1 - b) * (1 - b * β) / b < (1 - a) * (1 - a * β) / a := by
  have hb0 : 0 < b := by linarith
  rw [div_lt_div_iff₀ hb0 ha]
  have : 0 < (b - a) * (1 - a * b * β) := by
    apply mul_pos (by linarith)
    have : a * b < 1 := by nlinarith
    nlinarith
  nlinarith

/-- Woodford (2003), p. 204 (error E8 corrected): for `0 < n₁ < 1` and `1 + ωη > 0`,
`n₁γ₁ + n₂γ₂ = 0` **iff** `α₁ = α₂` (equal price stickiness). -/
theorem gamma_weighted_sum_eq_zero_iff {n1 α1 α2 β ω θ η : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1)
    (ha10 : 0 < α1) (ha11 : α1 < 1) (ha20 : 0 < α2) (ha21 : α2 < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hA : 0 < 1 + ω * θ) (hη : 0 < 1 + ω * η) :
    n1 * gamma1 n1 α1 β ω θ η + (1 - n1) * gamma2 n1 α2 β ω θ η = 0 ↔ α1 = α2 := by
  rw [gamma_weighted_sum]
  have hc : n1 * (1 - n1) * ((1 + ω * η) / (1 + ω * θ)) ≠ 0 := by
    have : 0 < 1 - n1 := by linarith
    positivity
  rw [mul_eq_zero, or_iff_right hc, sub_eq_zero]
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd h (calvoSlope_strictAnti ha10 hlt ha21 hβ0 hβ1).ne'
    · exact absurd h (calvoSlope_strictAnti ha20 hlt ha11 hβ0 hβ1).ne
  · rintro rfl; rfl

/-- Woodford (2003), p. 204 (error E8): the printed statement "`ξ₁ = ξ₂`, hence
`n₁ξ₁ + n₂ξ₂ = 0`" is false: with equal stickiness `n₁ξ₁ + n₂ξ₂ = ξ₁ > 0`. -/
theorem printed_E8_false {n1 α β ω θ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hβ1 : β < 1) (hA : 0 < 1 + ω * θ) :
    n1 * calvoXi α β (ω * θ) + (1 - n1) * calvoXi α β (ω * θ) ≠ 0 := by
  have := calvoXi_pos hα0 hα1 hβ1 hA
  ring_nf
  exact this.ne'

/-- Woodford (2003), p. 204: with equally sticky prices (`α₁ = α₂ = α`) the size-weighted
average `π = n₁π₁ + n₂π₂` of (2.27) is the one-sector New Keynesian Phillips curve (2.12),
`π_t = κ(Ŷ_t − Ŷ_tⁿ) + β E_t π_{t+1}`, `κ = ξ(ω + σ⁻¹)`. -/
theorem aggregate_nkpc {n1 α β ω θ σ η : ℝ} {π1 π2 Y Yn x xn : ℕ → Ω → ℝ}
    (h1 : ∀ t, π1 t = kappaJ α β ω θ σ • (Y t - Yn t) + gamma1 n1 α β ω θ η • (x t - xn t) +
      β • 𝔼.E t (π1 (t + 1)))
    (h2 : ∀ t, π2 t = kappaJ α β ω θ σ • (Y t - Yn t) + gamma2 n1 α β ω θ η • (x t - xn t) +
      β • 𝔼.E t (π2 (t + 1))) (t : ℕ) :
    n1 • π1 t + (1 - n1) • π2 t = kappaJ α β ω θ σ • (Y t - Yn t) +
      β • 𝔼.E t (n1 • π1 (t + 1) + (1 - n1) • π2 (t + 1)) := by
  have hz : n1 * gamma1 n1 α β ω θ η + (1 - n1) * gamma2 n1 α β ω θ η = 0 := by
    rw [gamma_weighted_sum]; ring
  funext o
  have e1 := congrFun (h1 t) o
  have e2 := congrFun (h2 t) o
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_smul]
    at e1 e2 ⊢
  rw [e1, e2]
  linear_combination (x t o - xn t o) * hz

/-- Woodford (2003), p. 204: under (2.12) (`κ > 0`, `0 < β < 1`, bounded inflation), stabilising
the output gap and stabilising aggregate inflation are the same policy: `Ŷ ≡ Ŷⁿ ⟺ π ≡ 0`. -/
theorem aggregate_compatible {κ β M : ℝ} (hκ : 0 < κ) (hβ0 : 0 < β) (hβ1 : β < 1)
    {π gap : ℕ → Ω → ℝ} (hπb : ∀ t o, |π t o| ≤ M)
    (h : ∀ t, π t = κ • gap t + β • 𝔼.E t (π (t + 1))) :
    (∀ t, gap t = 0) ↔ ∀ t, π t = 0 := by
  constructor
  · intro hg
    have hβ : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
    have h1 : ∀ t, π t = β • 𝔼.E t (π (t + 1)) + 0 := fun t => by
      rw [h t, hg t, smul_zero, zero_add, add_zero]
    have h2 : ∀ t, (0 : ℕ → Ω → ℝ) t = β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
      simp
    have := 𝔼.forward_unique hβ h1 h2 ⟨M, hπb⟩ ⟨0, fun _ _ => by simp⟩
    exact fun t => congrFun this t
  · intro hp t
    have := h t
    rw [hp t, hp (t + 1), map_zero, smul_zero, add_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left hκ.ne'

/-- Woodford (2003), p. 204 ("if prices are not equally sticky ... it ceases to be true that the
same policy can simultaneously stabilize the aggregate output gap and the overall inflation
rate"): with `α₁ ≠ α₂`, if the gap is zero and aggregate inflation `n₁π₁ + n₂π₂` is zero at all
dates (bounded sectoral inflation obeying (2.27) and (2.28)), the natural relative price `p̂_Rⁿ`
never changes. So whenever `p̂_Rⁿ` moves, the two goals conflict. -/
theorem incompatible_of_unequal {n1 α1 α2 β ω θ σ η M1 M2 : ℝ} (hn0 : 0 < n1) (hn1 : n1 < 1)
    (ha10 : 0 < α1) (ha11 : α1 < 1) (ha20 : 0 < α2) (ha21 : α2 < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hA : 0 < 1 + ω * θ) (hη : 0 < 1 + ω * η) (hne : α1 ≠ α2)
    {π1 π2 gap x xn : ℕ → Ω → ℝ}
    (h1 : ∀ t, π1 t = kappaJ α1 β ω θ σ • gap t + gamma1 n1 α1 β ω θ η • (x t - xn t) +
      β • 𝔼.E t (π1 (t + 1)))
    (h2 : ∀ t, π2 t = kappaJ α2 β ω θ σ • gap t + gamma2 n1 α2 β ω θ η • (x t - xn t) +
      β • 𝔼.E t (π2 (t + 1)))
    (h228 : ∀ t, x (t + 1) = x t + π2 (t + 1) - π1 (t + 1))
    (hb1 : ∀ t o, |π1 t o| ≤ M1) (hb2 : ∀ t o, |π2 t o| ≤ M2)
    (hgap : ∀ t, gap t = 0) (hagg : ∀ t, n1 • π1 t + (1 - n1) • π2 t = 0) :
    ∀ t, xn (t + 1) = xn t := by
  set G := n1 * gamma1 n1 α1 β ω θ η + (1 - n1) * gamma2 n1 α2 β ω θ η with hG
  have hG0 : G ≠ 0 := fun h =>
    hne ((gamma_weighted_sum_eq_zero_iff hn0 hn1 ha10 ha11 ha20 ha21 hβ0 hβ1 hA hη).mp h)
  -- the relative price stays at its natural value
  have hx : ∀ t, x t = xn t := by
    intro t
    funext o
    have e1 := congrFun (h1 t) o
    have e2 := congrFun (h2 t) o
    have ea := congrFun (hagg t) o
    have ef : 𝔼.E t (n1 • π1 (t + 1) + (1 - n1) • π2 (t + 1)) o = 0 := by
      rw [hagg (t + 1), map_zero]; rfl
    rw [hgap t] at e1 e2
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      map_add, map_smul] at e1 e2 ea ef
    have : G * (x t o - xn t o) = 0 := by
      rw [hG]; linear_combination ea - n1 * e1 - (1 - n1) * e2 - β * ef
    have := (mul_eq_zero.mp this).resolve_left hG0
    linarith
  -- then each sector's inflation solves `π = β E π'` and is bounded, hence zero
  have hβ : |β| < 1 := by rw [abs_of_pos hβ0]; exact hβ1
  have hz : ∀ t, (0 : ℕ → Ω → ℝ) t = β • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := fun t => by
    simp
  have hπ1 : π1 = 0 := by
    refine 𝔼.forward_unique hβ (fun t => ?_) hz ⟨M1, hb1⟩ ⟨0, fun _ _ => by simp⟩
    rw [h1 t, hgap t, hx t, sub_self]; simp
  have hπ2 : π2 = 0 := by
    refine 𝔼.forward_unique hβ (fun t => ?_) hz ⟨M2, hb2⟩ ⟨0, fun _ _ => by simp⟩
    rw [h2 t, hgap t, hx t, sub_self]; simp
  intro t
  rw [← hx (t + 1), ← hx t, h228 t, hπ1, hπ2]
  simp

/-! ### Nested CES aggregation (2.22)–(2.23)

The upper level of the two-sector model is the finite CES aggregate of `DixitStiglitz` with weights
`w_j = n_j φ_j`: the price index is `finPriceIndex ![w₁, w₂] ![P₁, P₂] η` and the aggregator (2.22)
is `DixitStiglitz.Nested.upperIndex ![w₁, w₂] η ![C₁, C₂]`. -/

/-- Woodford (2003), p. 201: the two-sector price index is
`P = (w₁P₁^{1−η} + w₂P₂^{1−η})^{1/(1−η)}`. -/
theorem finPriceIndex_two (w1 w2 P1 P2 η : ℝ) :
    finPriceIndex ![w1, w2] ![P1, P2] η =
      (w1 * P1 ^ (1 - η) + w2 * P2 ^ (1 - η)) ^ (1 - η)⁻¹ := by
  simp [finPriceIndex, Fin.sum_univ_two, one_div]

/-- Woodford (2003), eq. (2.22), p. 200: the two-sector aggregator is
`C = (w₁^{1/η} C₁^{(η−1)/η} + w₂^{1/η} C₂^{(η−1)/η})^{η/(η−1)}`. -/
theorem upperIndex_two (w1 w2 C1 C2 η : ℝ) :
    upperIndex ![w1, w2] η ![C1, C2] =
      (w1 ^ η⁻¹ * C1 ^ ((η - 1) / η) + w2 ^ η⁻¹ * C2 ^ ((η - 1) / η)) ^ (η / (η - 1)) := by
  simp [upperIndex, Fin.sum_univ_two, one_div]

/-- Woodford (2003), p. 201: relative prices satisfy `w₁(P₁/P)^{1−η} + w₂(P₂/P)^{1−η} = 1`,
equivalently `∑ w_j exp((1 − η) log(P_j/P)) = 1` (the form used in `relPrice_index_linear`). -/
theorem relPrice_sum {η w1 w2 P1 P2 : ℝ} (hη : η ≠ 1) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hP1 : 0 < P1) (hP2 : 0 < P2) :
    w1 * (P1 / finPriceIndex ![w1, w2] ![P1, P2] η) ^ (1 - η) +
        w2 * (P2 / finPriceIndex ![w1, w2] ![P1, P2] η) ^ (1 - η) = 1 ∧
      w1 * Real.exp ((1 - η) * Real.log (P1 / finPriceIndex ![w1, w2] ![P1, P2] η)) +
        w2 * Real.exp ((1 - η) * Real.log (P2 / finPriceIndex ![w1, w2] ![P1, P2] η)) = 1 := by
  have h1η : (1 - η) ≠ 0 := sub_ne_zero.mpr (Ne.symm hη)
  have hSpos : 0 < w1 * P1 ^ (1 - η) + w2 * P2 ^ (1 - η) := by positivity
  rw [finPriceIndex_two]
  have hPpos : 0 < (w1 * P1 ^ (1 - η) + w2 * P2 ^ (1 - η)) ^ (1 - η)⁻¹ :=
    Real.rpow_pos_of_pos hSpos _
  have hPS : ((w1 * P1 ^ (1 - η) + w2 * P2 ^ (1 - η)) ^ (1 - η)⁻¹) ^ (1 - η) =
      w1 * P1 ^ (1 - η) + w2 * P2 ^ (1 - η) := Real.rpow_inv_rpow hSpos.le h1η
  set P := (w1 * P1 ^ (1 - η) + w2 * P2 ^ (1 - η)) ^ (1 - η)⁻¹
  have first : w1 * (P1 / P) ^ (1 - η) + w2 * (P2 / P) ^ (1 - η) = 1 := by
    rw [Real.div_rpow hP1.le hPpos.le, Real.div_rpow hP2.le hPpos.le, hPS]
    field_simp
  refine ⟨first, ?_⟩
  have e : ∀ x : ℝ, 0 < x → Real.exp ((1 - η) * Real.log x) = x ^ (1 - η) := fun x hx => by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  rw [e _ (div_pos hP1 hPpos), e _ (div_pos hP2 hPpos)]
  exact first

/-- Woodford (2003), pp. 200–201: the sectoral demands `C_j = n_j φ_j C (P_j/P)^{−η}` deliver
exactly the aggregate `C` under (2.22) (`η > 0`, `η ≠ 1`; the two-sector case of
`DixitStiglitz.fin_demand_attains`). -/
theorem ces_aggregate_of_demands {η w1 w2 P1 P2 C : ℝ} (hη0 : 0 < η) (hη : η ≠ 1)
    (hw1 : 0 < w1) (hw2 : 0 < w2) (hP1 : 0 < P1) (hP2 : 0 < P2) (hC : 0 < C) :
    upperIndex ![w1, w2] η ![w1 * C * (P1 / finPriceIndex ![w1, w2] ![P1, P2] η) ^ (-η),
      w2 * C * (P2 / finPriceIndex ![w1, w2] ![P1, P2] η) ^ (-η)] = C := by
  have ha : ∀ j, 0 < (![w1, w2] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hw1, hw2]
  have hq : ∀ j, 0 < (![P1, P2] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hP1, hP2]
  have hd := (fin_demand_attains hη0 hη ha hq hC).1
  set P := finPriceIndex ![w1, w2] ![P1, P2] η with hPdef
  have hPpos : 0 < P := by
    rw [hPdef, finPriceIndex_two]; exact Real.rpow_pos_of_pos (by positivity) _
  have hC1 : 0 ≤ w1 * C * (P1 / P) ^ (-η) :=
    mul_nonneg (mul_nonneg hw1.le hC.le) (Real.rpow_nonneg (div_pos hP1 hPpos).le _)
  have hC2 : 0 ≤ w2 * C * (P2 / P) ^ (-η) :=
    mul_nonneg (mul_nonneg hw2.le hC.le) (Real.rpow_nonneg (div_pos hP2 hPpos).le _)
  rw [upperIndex_eq hη0 ha (fun j => by fin_cases j <;> simp [hC1, hC2])]
  convert hd using 2
  funext j
  fin_cases j <;> simp <;> field_simp

/-- Woodford (2003), p. 201: total expenditure on the sectoral demands is `P₁C₁ + P₂C₂ = P C`. -/
theorem ces_expenditure {η w1 w2 P1 P2 C : ℝ} (hη : η ≠ 1) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hP1 : 0 < P1) (hP2 : 0 < P2) :
    P1 * (w1 * C * (P1 / finPriceIndex ![w1, w2] ![P1, P2] η) ^ (-η)) +
        P2 * (w2 * C * (P2 / finPriceIndex ![w1, w2] ![P1, P2] η) ^ (-η)) =
      finPriceIndex ![w1, w2] ![P1, P2] η * C := by
  set P := finPriceIndex ![w1, w2] ![P1, P2] η with hPdef
  have hPpos : 0 < P := by
    rw [hPdef, finPriceIndex_two]; exact Real.rpow_pos_of_pos (by positivity) _
  have hsum := (relPrice_sum hη hw1 hw2 hP1 hP2).1
  rw [← hPdef] at hsum
  have hx : ∀ x : ℝ, 0 < x → x ^ (1 - η) = x * x ^ (-η) := fun x hx => by
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [hx _ (div_pos hP1 hPpos), hx _ (div_pos hP2 hPpos)] at hsum
  have e : P1 * (w1 * C * (P1 / P) ^ (-η)) + P2 * (w2 * C * (P2 / P) ^ (-η)) =
      P * C * (w1 * (P1 / P * (P1 / P) ^ (-η)) + w2 * (P2 / P * (P2 / P) ^ (-η))) := by
    field_simp
  rw [e, hsum, mul_one]

/-- Woodford (2003), p. 201 (normalisation): at a common price `p` for all goods (and
`n₁φ₁ + n₂φ₂ = 1`) the price index is `P = p` and sectoral demands are `C_j = n_j φ_j C`, i.e.
`c(i) = C_j/n_j = φ_j C` for each good. -/
theorem ces_common_price {η n1 φ1 φ2 p C : ℝ} (hη : η ≠ 1) (hp : 0 < p)
    (hφ : n1 * φ1 + (1 - n1) * φ2 = 1) (hn : n1 ≠ 0) :
    finPriceIndex ![n1 * φ1, (1 - n1) * φ2] ![p, p] η = p ∧
      (n1 * φ1) * C * (p / finPriceIndex ![n1 * φ1, (1 - n1) * φ2] ![p, p] η) ^ (-η) / n1 =
        φ1 * C := by
  have h1η : (1 - η) ≠ 0 := sub_ne_zero.mpr (Ne.symm hη)
  have hP : finPriceIndex ![n1 * φ1, (1 - n1) * φ2] ![p, p] η = p := by
    rw [finPriceIndex_two, ← add_mul, hφ, one_mul, Real.rpow_rpow_inv hp.le h1η]
  refine ⟨hP, ?_⟩
  rw [hP, div_self hp.ne', Real.one_rpow]
  field_simp

/-- Woodford (2003), eq. (2.23), p. 201 (normalisation): at a common price `p` the sectoral
indices `P_j = (n_j⁻¹ ∫_{N_j} p^{1−θ} di)^{1/(1−θ)}` equal `p`, for `N₁ = [0, n₁]` and
`N₂ = (n₁, 1]`. -/
theorem lowerNest_const {θ n1 p : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n1) (hn1 : n1 < 1) (hp : 0 < p) :
    (n1⁻¹ * ∫ _ in Set.Icc 0 n1, p ^ (1 - θ)) ^ (1 - θ)⁻¹ = p ∧
      ((1 - n1)⁻¹ * ∫ _ in Set.Ioc n1 1, p ^ (1 - θ)) ^ (1 - θ)⁻¹ = p := by
  have h1θ : (1 - θ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
  have hn2 : (1 - n1) ≠ 0 := by linarith
  constructor
  · rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le hn0.le, smul_eq_mul,
      sub_zero, ← mul_assoc, inv_mul_cancel₀ hn0.ne', one_mul, Real.rpow_rpow_inv hp.le h1θ]
  · rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc, smul_eq_mul,
      max_eq_left (by linarith), ← mul_assoc, inv_mul_cancel₀ hn2, one_mul,
      Real.rpow_rpow_inv hp.le h1θ]

/-! ### Log-linearisations as exact derivatives -/

/-- Woodford (2003), eq. (2.26), p. 202 (and (2.1)/(2.5), (3.5) p. 215): the Calvo index in logs,
`(1 − θ)⁻¹ log((1 − α)e^{(1−θ)a} + α e^{(1−θ)b})`, has derivative `(1 − α)a' + αb'` along any
path through a point where `a = b` (all prices equal); the chain rule applied to the exact
derivative (2.5) of `Calvo.hasFDerivAt_logIndexFn`. -/
theorem hasDerivAt_logCES2 {θ w : ℝ} (hθ : θ ≠ 1) {a b : ℝ → ℝ} {a' b' : ℝ}
    (ha : HasDerivAt a a' 0) (hb : HasDerivAt b b' 0) (hab : a 0 = b 0) :
    HasDerivAt (fun s => (1 - θ)⁻¹ * Real.log ((1 - w) * Real.exp ((1 - θ) * a s) +
      w * Real.exp ((1 - θ) * b s))) ((1 - w) * a' + w * b') 0 := by
  have hγ : HasDerivAt (fun s => (a s, b s)) (a', b') 0 := ha.prodMk hb
  have hF := Calvo.hasFDerivAt_logIndexFn w hθ (b 0)
  have hγ0 : (fun s => (a s, b s)) 0 = (b 0, b 0) := by simp [hab]
  rw [← hγ0] at hF
  have h := hF.comp_hasDerivAt (0 : ℝ) hγ
  have hd : ((1 - w) • ContinuousLinearMap.fst ℝ ℝ ℝ + w • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (a', b') = (1 - w) * a' + w * b' := by simp [smul_eq_mul]
  rw [hd] at h
  exact h

/-- Woodford (2003), pp. 201, 204 and 669: differentiating the relative-price form of the price
index, `∑ n_j φ_j(s) e^{(1−η) r_j(s)} = 1` (`r_j = log(P_j/P)`, `n₁φ₁ + n₂φ₂ ≡ 1`), at the
symmetric steady state (`φ_j = 1`, `r_j = 0`) gives `n₁φ̂₁ + n₂φ̂₂ = 0` and, for `η ≠ 1`,
`n₁p̂₁ + n₂p̂₂ = 0`. -/
theorem relPrice_index_linear {η n1 : ℝ} (hη : η ≠ 1) {φ1 φ2 r1 r2 : ℝ → ℝ}
    {φ1' φ2' r1' r2' : ℝ} (hφ1 : HasDerivAt φ1 φ1' 0) (hφ2 : HasDerivAt φ2 φ2' 0)
    (hr1 : HasDerivAt r1 r1' 0) (hr2 : HasDerivAt r2 r2' 0) (h10 : r1 0 = 0) (h20 : r2 0 = 0)
    (hφ10 : φ1 0 = 1) (hφ20 : φ2 0 = 1) (hsum : ∀ s, n1 * φ1 s + (1 - n1) * φ2 s = 1)
    (hidx : ∀ s, n1 * φ1 s * Real.exp ((1 - η) * r1 s) +
      (1 - n1) * φ2 s * Real.exp ((1 - η) * r2 s) = 1) :
    n1 * φ1' + (1 - n1) * φ2' = 0 ∧ n1 * r1' + (1 - n1) * r2' = 0 := by
  have h1η : (1 - η) ≠ 0 := sub_ne_zero.mpr (Ne.symm hη)
  have d1 : HasDerivAt (fun s => n1 * φ1 s + (1 - n1) * φ2 s) (n1 * φ1' + (1 - n1) * φ2') 0 :=
    HasDerivAt.add (hφ1.const_mul n1) (hφ2.const_mul (1 - n1))
  have e1 : (fun s => n1 * φ1 s + (1 - n1) * φ2 s) = fun _ => (1 : ℝ) := funext hsum
  rw [e1] at d1
  have u1 := d1.unique (hasDerivAt_const 0 (1 : ℝ))
  have d2 : HasDerivAt (fun s => n1 * φ1 s * Real.exp ((1 - η) * r1 s) +
      (1 - n1) * φ2 s * Real.exp ((1 - η) * r2 s))
      (n1 * φ1' * Real.exp ((1 - η) * r1 0) + n1 * φ1 0 * (Real.exp ((1 - η) * r1 0) *
        ((1 - η) * r1')) + ((1 - n1) * φ2' * Real.exp ((1 - η) * r2 0) +
        (1 - n1) * φ2 0 * (Real.exp ((1 - η) * r2 0) * ((1 - η) * r2')))) 0 :=
    HasDerivAt.add (HasDerivAt.mul (hφ1.const_mul n1) ((hr1.const_mul (1 - η)).exp))
      (HasDerivAt.mul (hφ2.const_mul (1 - n1)) ((hr2.const_mul (1 - η)).exp))
  have e2 : (fun s => n1 * φ1 s * Real.exp ((1 - η) * r1 s) +
      (1 - n1) * φ2 s * Real.exp ((1 - η) * r2 s)) = fun _ => (1 : ℝ) := funext hidx
  rw [e2] at d2
  have u2 := d2.unique (hasDerivAt_const 0 (1 : ℝ))
  rw [h10, h20, hφ10, hφ20, mul_zero, Real.exp_zero] at u2
  refine ⟨u1, ?_⟩
  have : (1 - η) * (n1 * r1' + (1 - n1) * r2') = 0 := by linear_combination u2 - u1
  exact (mul_eq_zero.mp this).resolve_left h1η

/-- Woodford (2003), eq. (B.29), p. 667: `Y_j = n_j φ_j Y (P_j/P)^{−η}` is exactly log-linear:
`log Y_j = log n_j + log φ_j + log Y − η log(P_j/P)`. -/
theorem log_sectorDemand {η n φ Y x : ℝ} (hn : 0 < n) (hφ : 0 < φ) (hY : 0 < Y) (hx : 0 < x) :
    Real.log (n * φ * Y * x ^ (-η)) =
      Real.log n + Real.log φ + Real.log Y - η * Real.log x := by
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hY.ne',
    Real.log_mul hn.ne' hφ.ne', Real.log_rpow hx]
  ring

/-- Woodford (2003), App. B.7, p. 668: differentiating (B.29) in logs along a path gives
`Ŷ_j = φ̂_j + Ŷ − η p̂_j` (the constant `log n_j` drops out). -/
theorem sectorDemand_linear {η c : ℝ} {lY lφ lYagg lx : ℝ → ℝ} {Yh φh Ygh xh : ℝ}
    (hφ : HasDerivAt lφ φh 0) (hY : HasDerivAt lYagg Ygh 0) (hx : HasDerivAt lx xh 0)
    (hYj : HasDerivAt lY Yh 0) (hdem : ∀ s, lY s = c + lφ s + lYagg s - η * lx s) :
    Yh = φh + Ygh - η * xh := by
  have d : HasDerivAt (fun s => c + lφ s + lYagg s - η * lx s) (φh + Ygh - η * xh) 0 :=
    HasDerivAt.sub (HasDerivAt.add (hφ.const_add c) hY) (hx.const_mul η)
  have e : (fun s => c + lφ s + lYagg s - η * lx s) = lY := (funext hdem).symm
  rw [e] at d
  exact hYj.unique d

/-! ### The profit gradient (B.28) and error E7; normalisation E30 -/

/-- Woodford (2003), eq. (B.28), p. 667 (corrected, error E7): the derivative of the sectoral
profit function `Π(p) = Y_j P_j^θ p^{1−θ} − w f⁻¹(Y_j P_j^θ p^{−θ}/A_j)` is
`(1 − θ) Y_j P_j^θ p^{−θ−1} (p − μ P s)`, `μ = θ/(θ − 1)`, where `s = w/(P A_j f')` is real
marginal cost (nominal marginal cost `w/(A_j f')` is `P s`). -/
theorem profit_gradient {θ Yj Pj A w P fp p : ℝ} {finv : ℝ → ℝ} (hθ : 1 < θ) (hp : 0 < p)
    (hA : A ≠ 0) (hP : P ≠ 0) (hfp : fp ≠ 0)
    (hf : HasDerivAt finv fp⁻¹ (Yj * Pj ^ θ * p ^ (-θ) / A)) :
    HasDerivAt (fun x => Yj * Pj ^ θ * x ^ (1 - θ) - w * finv (Yj * Pj ^ θ * x ^ (-θ) / A))
      ((1 - θ) * Yj * Pj ^ θ * p ^ (-θ - 1) * (p - θ / (θ - 1) * P * (w / (P * A * fp)))) p := by
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have h1 := (Real.hasDerivAt_rpow_const (p := 1 - θ) (Or.inl hp.ne')).const_mul (Yj * Pj ^ θ)
  have h2 := ((Real.hasDerivAt_rpow_const (p := -θ) (Or.inl hp.ne')).const_mul
    (Yj * Pj ^ θ)).div_const A
  have h3 : HasDerivAt (fun x => w * finv (Yj * Pj ^ θ * x ^ (-θ) / A))
      (w * (fp⁻¹ * (Yj * Pj ^ θ * (-θ * p ^ (-θ - 1)) / A))) p := (hf.comp p h2).const_mul w
  have h13 : HasDerivAt (fun x => Yj * Pj ^ θ * x ^ (1 - θ) - w * finv (Yj * Pj ^ θ * x ^ (-θ) / A))
      (Yj * Pj ^ θ * ((1 - θ) * p ^ (1 - θ - 1)) -
        w * (fp⁻¹ * (Yj * Pj ^ θ * (-θ * p ^ (-θ - 1)) / A))) p := HasDerivAt.sub h1 h3
  convert h13 using 1
  have e1 : p ^ (1 - θ - 1) = p ^ (-θ - 1) * p := by
    rw [show (1 : ℝ) - θ - 1 = -θ - 1 + 1 by ring, Real.rpow_add_one hp.ne']
  rw [e1]
  field_simp
  ring

/-- Woodford (2003), eq. (B.28), p. 667 (error E7): the printed bracket `p − μ s^j` (nominal price
less a real cost) is not the profit gradient: whenever `P ≠ 1` (and `Y_j`, `P_j`, `w ≠ 0`) the
printed expression differs from the derivative `profit_gradient`. -/
theorem printed_B28_not_derivative {θ Yj Pj A w P fp p : ℝ} {finv : ℝ → ℝ} (hθ : 1 < θ)
    (hp : 0 < p) (hPj : 0 < Pj) (hYj : Yj ≠ 0) (hw : w ≠ 0) (hA : A ≠ 0) (hP : P ≠ 0)
    (hP1 : P ≠ 1) (hfp : fp ≠ 0) (hf : HasDerivAt finv fp⁻¹ (Yj * Pj ^ θ * p ^ (-θ) / A)) :
    ¬ HasDerivAt (fun x => Yj * Pj ^ θ * x ^ (1 - θ) - w * finv (Yj * Pj ^ θ * x ^ (-θ) / A))
      ((1 - θ) * Yj * Pj ^ θ * p ^ (-θ - 1) * (p - θ / (θ - 1) * (w / (P * A * fp)))) p := by
  intro h
  have hu := h.unique (profit_gradient hθ hp hA hP hfp hf)
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hz : (1 - θ) * Yj * Pj ^ θ * p ^ (-θ - 1) * (θ / (θ - 1)) * (w / (P * A * fp)) *
      (P - 1) = 0 := by linear_combination hu
  have hne : (1 - θ) * Yj * Pj ^ θ * p ^ (-θ - 1) * (θ / (θ - 1)) * (w / (P * A * fp)) *
      (P - 1) ≠ 0 := by
    have h1θ : (1 - θ) ≠ 0 := by linarith
    have hθ0 : θ ≠ 0 := by linarith
    have hPj' : Pj ^ θ ≠ 0 := (Real.rpow_pos_of_pos hPj _).ne'
    have hp' : p ^ (-θ - 1) ≠ 0 := (Real.rpow_pos_of_pos hp _).ne'
    have hP1' : P - 1 ≠ 0 := sub_ne_zero.mpr hP1
    have : w / (P * A * fp) ≠ 0 := div_ne_zero hw (mul_ne_zero (mul_ne_zero hP hA) hfp)
    have : θ / (θ - 1) ≠ 0 := div_ne_zero hθ0 hθ1
    positivity
  exact hne hz

/-- Woodford (2003), p. 201 and p. 202 (error E30): revenue from good `i` in sector `j` with
demand `c(i) = n_j⁻¹ C_j (p/P_j)^{−θ}` is `(C_j/n_j) P_j^θ p^{1−θ}`: the profit function on
p. 202 is right with the per-good index `Y_j = C_j/n_j`; read with the sectoral total (B.29) it
overstates revenue by the factor `n_j⁻¹`. -/
theorem revenue_per_good {θ n Cj Pj p : ℝ} (hn : n ≠ 0) (hPj : 0 < Pj) (hp : 0 < p) :
    p * (n⁻¹ * Cj * (p / Pj) ^ (-θ)) = Cj / n * Pj ^ θ * p ^ (1 - θ) ∧
      Cj * Pj ^ θ * p ^ (1 - θ) = n⁻¹ * (n * (Cj / n * Pj ^ θ * p ^ (1 - θ))) * n := by
  refine ⟨?_, by field_simp⟩
  rw [Real.div_rpow hp.le hPj.le, Real.rpow_neg hPj.le, sub_eq_add_neg, Real.rpow_add hp,
    Real.rpow_one]
  field_simp

/-- Woodford (2003), App. B.7, p. 667 (error E30 is harmless after logs): adding the constant
`log n_j` does not change a log deviation. -/
theorem logdev_normalisation {c f' : ℝ} {f : ℝ → ℝ} :
    HasDerivAt (fun s => c + f s) f' 0 ↔ HasDerivAt f f' 0 :=
  hasDerivAt_const_add_iff c

/-! ### Real marginal cost (B.30) and error E6 -/

/-- Woodford (2003), (1.15) and (B.30), p. 667: the linear map
`(ŷ, Ŷ, ε) ↦ ω ŷ + σ⁻¹ Ŷ + d ε`, the derivative of log real marginal cost in sector `j` with
respect to own output, aggregate output and the sector's disturbance. -/
noncomputable def mcDeriv (ω σinv d : ℝ) : ℝ × ℝ × ℝ →L[ℝ] ℝ :=
  ω • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) +
    σinv • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
    d • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Woodford (2003), (B.30), p. 667: along a path `s ↦ (log y(s), log Y(s), s)` through the steady
state, log real marginal cost has derivative `ω ŷ + σ⁻¹ Ŷ + d`. -/
theorem hasDerivAt_mc_path {ω σinv d abar bbar : ℝ} {g : ℝ × ℝ × ℝ → ℝ}
    (hg : HasFDerivAt g (mcDeriv ω σinv d) (abar, bbar, 0)) {u v : ℝ → ℝ} {u' v' : ℝ}
    (hu : HasDerivAt u u' 0) (hv : HasDerivAt v v' 0) (hu0 : u 0 = abar) (hv0 : v 0 = bbar) :
    HasDerivAt (fun s => g (u s, v s, s)) (ω * u' + σinv * v' + d) 0 := by
  have hp : HasDerivAt (fun s => (u s, v s, s)) (u', v', 1) 0 :=
    hu.prodMk (hv.prodMk (hasDerivAt_id 0))
  rw [← hu0, ← hv0] at hg
  have := hg.comp_hasDerivAt (0 : ℝ) hp
  convert this using 1 <;> first | rfl | simp [mcDeriv]

/-- Woodford (2003), eq. (B.30), p. 667, **corrected** (error E6): with the sectoral natural rates
defined by `log μ + log s^j(Y_jⁿ, Yⁿ; ξ̃) = log(P_j/P)ⁿ` and the natural demand
`log Y_jⁿ = log φ_j + log Yⁿ − η log(P_j/P)ⁿ` (p. 667), log real marginal cost of a firm in sector
`j` has the exact derivative `ω(ŷ − Ŷ_jⁿ) + σ⁻¹(Ŷ − Ŷⁿ) + (1/η)(φ̂_j + Ŷⁿ − Ŷ_jⁿ)`, and
`p̂_jⁿ = (1/η)(φ̂_j + Ŷⁿ − Ŷ_jⁿ)`. -/
theorem realMC_B30 {ω σinv d η lmu abar bbar : ℝ} (hη : η ≠ 0) {g : ℝ × ℝ × ℝ → ℝ}
    (hg : HasFDerivAt g (mcDeriv ω σinv d) (abar, bbar, 0)) {an bn rn lφ a b : ℝ → ℝ}
    {Yjn Yn pjn φh yh Yh : ℝ} (han : HasDerivAt an Yjn 0) (hbn : HasDerivAt bn Yn 0)
    (hrn : HasDerivAt rn pjn 0) (hlφ : HasDerivAt lφ φh 0) (ha : HasDerivAt a yh 0)
    (hb : HasDerivAt b Yh 0) (han0 : an 0 = abar) (hbn0 : bn 0 = bbar) (ha0 : a 0 = abar)
    (hb0 : b 0 = bbar) (hN1 : ∀ s, lmu + g (an s, bn s, s) = rn s)
    (hN2 : ∀ s, an s = lφ s + bn s - η * rn s) :
    HasDerivAt (fun s => g (a s, b s, s))
        (ω * (yh - Yjn) + σinv * (Yh - Yn) + (1 / η) * (φh + Yn - Yjn)) 0 ∧
      pjn = (1 / η) * (φh + Yn - Yjn) := by
  have dn : HasDerivAt (fun s => lmu + g (an s, bn s, s)) (ω * Yjn + σinv * Yn + d) 0 :=
    (hasDerivAt_mc_path hg han hbn han0 hbn0).const_add lmu
  have e1 : (fun s => lmu + g (an s, bn s, s)) = rn := funext hN1
  rw [e1] at dn
  have u1 := hrn.unique dn
  have d2 : HasDerivAt (fun s => lφ s + bn s - η * rn s) (φh + Yn - η * pjn) 0 :=
    HasDerivAt.sub (HasDerivAt.add hlφ hbn) (hrn.const_mul η)
  have e2 : (fun s => lφ s + bn s - η * rn s) = an := (funext hN2).symm
  rw [e2] at d2
  have u2 := han.unique d2
  have hp : pjn = (1 / η) * (φh + Yn - Yjn) := by
    rw [u2]; field_simp; ring
  refine ⟨?_, hp⟩
  convert hasDerivAt_mc_path hg ha hb ha0 hb0 using 1
  rw [← hp, u1]
  ring

/-- Woodford (2003), (B.30), p. 667 (error E6): the printed coefficient `η` on
`φ̂_j + Ŷⁿ − Ŷ_jⁿ` is wrong. Example: `ω = σ⁻¹ = 1`, `d = 0`, `η = 2`, `log μ = 0`, a pure
taste shift `φ̂_j = 1` with `Ŷⁿ = 0`; then `Ŷ_jⁿ = p̂_jⁿ = 1/3`, and at the steady-state
allocation `ŷ = Ŷ = 0` real marginal cost does not move (derivative `0`), while the printed
formula gives `ω(0 − 1/3) + σ⁻¹·0 + 2(1 + 0 − 1/3) = 1`. -/
theorem printed_B30_fails :
    (∀ s : ℝ, 0 + (fun z : ℝ × ℝ × ℝ => z.1 + z.2.1) (s / 3, 0, s) = s / 3) ∧
      (∀ s : ℝ, s / 3 = s + 0 - 2 * (s / 3)) ∧
      HasFDerivAt (fun z : ℝ × ℝ × ℝ => z.1 + z.2.1) (mcDeriv 1 1 0) (0, 0, 0) ∧
      HasDerivAt (fun s : ℝ => (fun z : ℝ × ℝ × ℝ => z.1 + z.2.1) (0, 0, s)) 0 0 ∧
      (1 : ℝ) * (0 - 1 / 3) + 1 * (0 - 0) + 2 * (1 + 0 - 1 / 3) = 1 := by
  refine ⟨fun s => by simp, fun s => by ring, ?_, ?_, by norm_num⟩
  · have : (fun z : ℝ × ℝ × ℝ => z.1 + z.2.1) = mcDeriv 1 1 0 := by
      funext z; simp [mcDeriv]
    rw [this]
    exact (mcDeriv 1 1 0).hasFDerivAt
  · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)

/-- Woodford (2003), App. B.7, pp. 668–669 (error E6): with the printed (B.30) — coefficient `η`
on `φ̂_j + Ŷⁿ − Ŷ_jⁿ` — and the demands, the stated display
`ŝ_j − p̂_j = (ω + σ⁻¹)(Ŷ − Ŷⁿ) − (1 + ωη)(p̂_j − p̂_jⁿ)` holds iff `(η² − 1) p̂_jⁿ = 0`; it
therefore fails whenever `η ≠ 1` and the natural relative price moves. -/
theorem printed_display_iff {ω σ η s p pn Y Yn Yj Yjn φ : ℝ}
    (hB30 : s = ω * (Yj - Yjn) + σ⁻¹ * (Y - Yn) + η * (φ + Yn - Yjn))
    (hd : Yj = φ + Y - η * p) (hdn : Yjn = φ + Yn - η * pn) :
    s - p = (ω + σ⁻¹) * (Y - Yn) - (1 + ω * η) * (p - pn) ↔ (η ^ 2 - 1) * pn = 0 := by
  rw [hB30, hd, hdn]
  constructor <;> intro h <;> linear_combination h

/-! ### The first-order condition (B.31) linearised: (B.32) -/

/-- Woodford (2003), (B.31)–(B.32), p. 668: at a steady state where the bracket
`p − μ P s` of the profit gradient vanishes, its derivative along a path is
`p̄ (p̂ − P̂ − ŝ)` (all variables in logs). -/
theorem bracket_hasDerivAt {μ : ℝ} {lp lP lS : ℝ → ℝ} {lp' lP' lS' : ℝ}
    (hp : HasDerivAt lp lp' 0) (hP : HasDerivAt lP lP' 0) (hS : HasDerivAt lS lS' 0)
    (hss : Real.exp (lp 0) = μ * Real.exp (lP 0) * Real.exp (lS 0)) :
    HasDerivAt (fun s => Real.exp (lp s) - μ * Real.exp (lP s) * Real.exp (lS s))
      (Real.exp (lp 0) * (lp' - lP' - lS')) 0 := by
  convert hp.exp.sub ((hP.exp.const_mul μ).mul hS.exp) using 1
  rw [hss]; ring

/-- Woodford (2003), (B.31), p. 668: a summand `W(s) B(s)` of the first-order condition whose
bracket `B` vanishes at the steady state has derivative `W(0) B'(0)` there (variations of the
discount factor and of the prefactor drop out). -/
theorem summand_hasDerivAt {W B : ℝ → ℝ} {W' B' : ℝ} (hW : HasDerivAt W W' 0)
    (hB : HasDerivAt B B' 0) (hB0 : B 0 = 0) :
    HasDerivAt (fun s => W s * B s) (W 0 * B') 0 := by
  convert hW.mul hB using 1
  rw [hB0]; ring

/-- Woodford (2003), (B.31) ⇒ (B.32), p. 668: if the (infinite-horizon) first-order condition
`∑_k g_k(s) = 0` holds for all perturbations `s` near the steady state, with termwise
derivatives dominated by a summable sequence, then the derivative series vanishes:
`∑_k g_k'(0) = 0`. -/
theorem linearised_FOC {r : ℝ} (hr : 0 < r) {g g' : ℕ → ℝ → ℝ} {u : ℕ → ℝ} (hu : Summable u)
    (hg : ∀ k y, y ∈ Metric.ball (0 : ℝ) r → HasDerivAt (g k) (g' k y) y)
    (hg' : ∀ k y, y ∈ Metric.ball (0 : ℝ) r → ‖g' k y‖ ≤ u k)
    (hg0 : Summable fun k => g k 0) (hfoc : ∀ y ∈ Metric.ball (0 : ℝ) r, ∑' k, g k y = 0) :
    ∑' k, g' k 0 = 0 := by
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) r := Metric.mem_ball_self hr
  have hd := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℝ) r).isPreconnected hg hg' h0 hg0 h0
  have heq : (fun z => ∑' k, g k z) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hr) fun y hy => hfoc y hy
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq)

/-- Woodford (2003), (B.32), p. 668: the linearised first-order condition. If the `k`-th summand
of (B.31) is `W_k(s)(p_k(s) − μ P_{t+k}(s) s_k(s))` with steady-state weight
`W_k(0) = c (αβ)ᵏ` (Calvo survival `αᵏ` times the steady-state discount factor `βᵏ`), a common
steady-state price `p̄`, and the bracket vanishing at the steady state, then
`∑_k (αβ)ᵏ (p̂_k − P̂_{t+k} − ŝ_k) = 0`. -/
theorem linearised_FOC_B32 {r c pbar α β μ : ℝ} (hr : 0 < r) (hc : c ≠ 0) (hpbar : pbar ≠ 0)
    {W g' : ℕ → ℝ → ℝ} {lp lP lS : ℕ → ℝ → ℝ} {W' lp' lP' lS' u : ℕ → ℝ} (hu : Summable u)
    (hg : ∀ k y, y ∈ Metric.ball (0 : ℝ) r → HasDerivAt
      (fun s => W k s * (Real.exp (lp k s) - μ * Real.exp (lP k s) * Real.exp (lS k s)))
      (g' k y) y)
    (hg' : ∀ k y, y ∈ Metric.ball (0 : ℝ) r → ‖g' k y‖ ≤ u k)
    (hW : ∀ k, HasDerivAt (W k) (W' k) 0) (hp : ∀ k, HasDerivAt (lp k) (lp' k) 0)
    (hP : ∀ k, HasDerivAt (lP k) (lP' k) 0) (hS : ∀ k, HasDerivAt (lS k) (lS' k) 0)
    (hW0 : ∀ k, W k 0 = c * (α * β) ^ k) (hp0 : ∀ k, Real.exp (lp k 0) = pbar)
    (hss : ∀ k, Real.exp (lp k 0) = μ * Real.exp (lP k 0) * Real.exp (lS k 0))
    (hfoc : ∀ y ∈ Metric.ball (0 : ℝ) r, ∑' k,
      W k y * (Real.exp (lp k y) - μ * Real.exp (lP k y) * Real.exp (lS k y)) = 0) :
    ∑' k, (α * β) ^ k * (lp' k - lP' k - lS' k) = 0 := by
  have hB0 : ∀ k, Real.exp (lp k 0) - μ * Real.exp (lP k 0) * Real.exp (lS k 0) = 0 :=
    fun k => by rw [hss k]; ring
  have hval : ∀ k, g' k 0 = c * pbar * ((α * β) ^ k * (lp' k - lP' k - lS' k)) := by
    intro k
    have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) r := Metric.mem_ball_self hr
    have d := summand_hasDerivAt (hW k) (bracket_hasDerivAt (hp k) (hP k) (hS k) (hss k))
      (hB0 k)
    rw [(hg k 0 h0).unique d, hW0 k, hp0 k]
    ring
  have hg0 : Summable fun k =>
      W k 0 * (Real.exp (lp k 0) - μ * Real.exp (lP k 0) * Real.exp (lS k 0)) := by
    simp only [hB0, mul_zero]; exact summable_zero
  have hsum := linearised_FOC hr hu hg hg' hg0 hfoc
  rw [tsum_congr hval, tsum_mul_left] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero hc hpbar)

/-- Woodford (2003), App. B.7, p. 668 (display after (B.32)): firm-level real marginal cost
`ŝ_{t,T} = ŝ_T − ωθ r` when own output is `ŷ_i = Ŷ_j − θ r` (`r` the firm's price relative to
its sector) and `ŝ` is linear in own output with slope `ω`. -/
theorem firm_mc {ω θ rest Yj r : ℝ} :
    ω * (Yj - θ * r) + rest = (ω * Yj + rest) - ω * θ * r := by ring

/-- Woodford (2003), (B.32), p. 668: a summand `p̂ − P̂ − ŝ(i)` of the linearised first-order
condition, with `p̂ − P̂ = r + p̂_j` and `ŝ(i) = ŝ_j − ωθ r`, equals `(1 + ωθ) r − (ŝ_j − p̂_j)`,
the summand of `LinFOC`. -/
theorem foc_summand_rewrite {ω θ r pj sj : ℝ} :
    (r + pj) - (sj - ω * θ * r) = (1 + ω * θ) * r - (sj - pj) := by ring

/-! ### The Cobb–Douglas limit `η → 1` (footnote 61) -/

/-- Woodford (2003), footnote 61, p. 201 (**the Cobb–Douglas limit of the price index**): as
`η → 1` the price index `(w₁P₁^{1−η} + w₂P₂^{1−η})^{1/(1−η)}` (`w₁ + w₂ = 1`) converges to
`P₁^{w₁} P₂^{w₂}`, the price index of the Cobb–Douglas aggregator (the two-sector case of
`DixitStiglitz.tendsto_cobbDouglas`). -/
theorem nestedIndex_tendsto_cobbDouglas {w1 w2 P1 P2 : ℝ} (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hw : w1 + w2 = 1) (hP1 : 0 < P1) (hP2 : 0 < P2) :
    Tendsto (fun η => finPriceIndex ![w1, w2] ![P1, P2] η) (𝓝[≠] 1) (𝓝 (P1 ^ w1 * P2 ^ w2)) := by
  have ha : ∀ j, 0 < (![w1, w2] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hw1, hw2]
  have hq : ∀ j, 0 < (![P1, P2] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hP1, hP2]
  simpa [Fin.prod_univ_two] using
    (tendsto_cobbDouglas ha (by simp [Fin.sum_univ_two, hw]) hq hq).2

/-- Woodford (2003), footnote 61, p. 201 (**the Cobb–Douglas limit of the aggregator**): as
`η → 1` the aggregator (2.22) `(w₁^{1/η}C₁^{(η−1)/η} + w₂^{1/η}C₂^{(η−1)/η})^{η/(η−1)}`
(`w₁ + w₂ = 1`) converges to `(C₁/w₁)^{w₁}(C₂/w₂)^{w₂}` (the two-sector case of
`DixitStiglitz.tendsto_cobbDouglas`). -/
theorem nestedAgg_tendsto_cobbDouglas {w1 w2 C1 C2 : ℝ} (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hw : w1 + w2 = 1) (hC1 : 0 < C1) (hC2 : 0 < C2) :
    Tendsto (fun η => upperIndex ![w1, w2] η ![C1, C2]) (𝓝[≠] 1)
      (𝓝 ((C1 / w1) ^ w1 * (C2 / w2) ^ w2)) := by
  have ha : ∀ j, 0 < (![w1, w2] : Fin 2 → ℝ) j := fun j => by fin_cases j <;> simp [hw1, hw2]
  have hx : ∀ j, 0 < (![C1 / w1, C2 / w2] : Fin 2 → ℝ) j := fun j => by
    fin_cases j <;> simp [div_pos hC1 hw1, div_pos hC2 hw2]
  have h := (tendsto_cobbDouglas ha (by simp [Fin.sum_univ_two, hw]) hx hx).1
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at h
  refine h.congr' ?_
  have hpos : ∀ᶠ η in 𝓝[≠] (1 : ℝ), 0 < η :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hpos] with η hη
  rw [upperIndex_eq hη ha (fun j => by fin_cases j <;> simp [hC1.le, hC2.le])]
  congr 1
  funext j
  fin_cases j <;> simp

/-! ### (B.31) ⇒ (B.32) under uncertainty -/

/-- Woodford (2003), (B.32), p. 668: `E_t` commutes with a series whose terms are dominated,
uniformly in the state, by a summable sequence (restated from `ForwardSolution.E_tsum_dom`,
which extends the core `E_tsum`, where geometric domination is needed). -/
theorem E_tsum_of_dominated {u : ℕ → ℝ} (hu : Summable u) {f : ℕ → Ω → ℝ}
    (hf : ∀ k o, |f k o| ≤ u k) (t : ℕ) (o : Ω) :
    𝔼.E t (fun o' => ∑' k, f k o') o = ∑' k, 𝔼.E t (f k) o :=
  ForwardSolution.E_tsum_dom 𝔼 hu hf t o

/-- Woodford (2003), (B.32), p. 668: `E_t` commutes with a series dominated by
`qᵏ (C + D k)`, `0 ≤ q < 1` (polynomially weighted geometric domination). -/
theorem E_tsum_polyGeom {q C D : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {f : ℕ → Ω → ℝ}
    (hf : ∀ k o, |f k o| ≤ q ^ k * (C + D * k)) (t : ℕ) (o : Ω) :
    𝔼.E t (fun o' => ∑' k, f k o') o = ∑' k, 𝔼.E t (f k) o := by
  have hq : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1
  have h1 := (summable_geometric_of_lt_one hq0 hq1).mul_left C
  have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1 hq).mul_left D
  refine E_tsum_of_dominated 𝔼 ((h1.add h2).congr fun k => ?_) hf t o
  simp only [pow_one]
  ring

/-- Woodford (2003), (B.32), p. 668, with the expectation outside the sum as printed:
`E_t ∑_k qᵏ[(1 + ωθ) r_{t,k} − m_{t+k}] = 0` is equivalent to `LinFOC` (expectation inside),
for bounded `Q`, `ψ`, `m`: the summands grow at most linearly in `k` (the relative price
cumulates bounded inflation), so `E_tsum_polyGeom` applies. -/
theorem linFOC_iff_E_outside {q A MQ Mψ Mm : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hA : 0 ≤ A)
    {Q ψ m : ℕ → Ω → ℝ} (hQ : ∀ t o, |Q t o| ≤ MQ) (hψ : ∀ t o, |ψ t o| ≤ Mψ)
    (hm : ∀ t o, |m t o| ≤ Mm) (t : ℕ) :
    (∀ o, 𝔼.E t (fun o' => ∑' k, q ^ k * (A • resetRel Q ψ t k - m (t + k)) o') o = 0) ↔
      LinFOC 𝔼 q A Q ψ m t := by
  have hbound : ∀ k o, |q ^ k * (A • resetRel Q ψ t k - m (t + k)) o| ≤
      q ^ k * ((A * MQ + Mm) + A * Mψ * k) := by
    intro k o
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hq0 k)
    simp only [resetRel, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    have hs : |∑ τ ∈ Finset.range k, ψ (t + τ + 1) o| ≤ k * Mψ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ τ ∈ Finset.range k, |ψ (t + τ + 1) o| ≤ ∑ _τ ∈ Finset.range k, Mψ :=
            Finset.sum_le_sum fun τ _ => hψ _ o
        _ = k * Mψ := by simp
    calc |A * (Q t o - ∑ τ ∈ Finset.range k, ψ (t + τ + 1) o) - m (t + k) o|
        ≤ A * (|Q t o| + |∑ τ ∈ Finset.range k, ψ (t + τ + 1) o|) + |m (t + k) o| := by
          refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
          rw [abs_mul, abs_of_nonneg hA]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) hA
      _ ≤ A * (MQ + k * Mψ) + Mm := by
          gcongr
          · exact hQ t o
          · exact hm _ o
      _ = (A * MQ + Mm) + A * Mψ * k := by ring
  have hcomm := fun o => E_tsum_polyGeom 𝔼 hq0 hq1 hbound t o
  have hsame : ∀ o, ∑' k, 𝔼.E t (fun o' => q ^ k * (A • resetRel Q ψ t k - m (t + k)) o') o =
      ∑' k, q ^ k * 𝔼.E t (A • resetRel Q ψ t k - m (t + k)) o := fun o =>
    tsum_congr fun k => by
      rw [show (fun o' => q ^ k * (A • resetRel Q ψ t k - m (t + k)) o') =
        q ^ k • (A • resetRel Q ψ t k - m (t + k)) from rfl, map_smul, Pi.smul_apply,
        smul_eq_mul]
  constructor
  · intro h o
    rw [← hsame o, ← hcomm o]; exact h o
  · intro h o
    rw [hcomm o, hsame o]; exact h o

/-- Woodford (2003), (B.31) ⇒ (B.32), p. 668, **under uncertainty** (finite state space): if the
first-order condition `E_t ∑_k g_k(s) = 0` holds for all perturbations `s` near `0`, and in every
state the summands have derivatives dominated by a summable sequence (uniformly in the state),
then `E_t ∑_k g_k'(0) = 0`. -/
theorem linearised_FOC_uncertain [Finite Ω] {r : ℝ} (hr : 0 < r) {g g' : ℕ → ℝ → Ω → ℝ}
    {u : ℕ → ℝ} (hu : Summable u) (t : ℕ)
    (hg : ∀ k y o, y ∈ Metric.ball (0 : ℝ) r → HasDerivAt (fun s => g k s o) (g' k y o) y)
    (hg' : ∀ k y o, y ∈ Metric.ball (0 : ℝ) r → ‖g' k y o‖ ≤ u k)
    (hg0 : ∀ o, Summable fun k => g k 0 o)
    (hfoc : ∀ y ∈ Metric.ball (0 : ℝ) r, 𝔼.E t (fun o => ∑' k, g k y o) = 0) :
    𝔼.E t (fun o => ∑' k, g' k 0 o) = 0 := by
  have := Fintype.ofFinite Ω
  have h0 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) r := Metric.mem_ball_self hr
  have hstate : ∀ o, HasDerivAt (fun s => ∑' k, g k s o) (∑' k, g' k 0 o) 0 := fun o =>
    hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
      (convex_ball (0 : ℝ) r).isPreconnected (fun k y hy => hg k y o hy)
      (fun k y hy => hg' k y o hy) h0 (hg0 o) h0
  have hF : HasDerivAt (fun s => fun o => ∑' k, g k s o) (fun o => ∑' k, g' k 0 o) 0 :=
    hasDerivAt_pi.mpr hstate
  have hL := (LinearMap.toContinuousLinearMap (𝔼.E t)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hF
  have heq : (⇑(LinearMap.toContinuousLinearMap (𝔼.E t)) ∘
      fun s => fun o => ∑' k, g k s o) =ᶠ[𝓝 0] fun _ => (0 : Ω → ℝ) :=
    Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds 0 hr) fun y hy => by
      simpa using hfoc y hy
  have := hL.unique ((hasDerivAt_const (0 : ℝ) (0 : Ω → ℝ)).congr_of_eventuallyEq heq)
  simpa using this

/-- Woodford (2003), (B.32), p. 668, **under uncertainty**: with the steady-state weights
`W_k(0) = c(αβ)ᵏ` and steady-state price `p̄` common to all states, the linearised condition is
`∑_k (αβ)ᵏ E_t(p̂_k − P̂_{t+k} − ŝ_k) = 0` (the derivative series has terms growing at most
linearly, `|p̂_k − P̂_{t+k} − ŝ_k| ≤ C + Dk`, so `E_t` moves inside the sum). -/
theorem linearised_FOC_B32_uncertain [Finite Ω] {r c pbar α β C D : ℝ} (hr : 0 < r)
    (hc : c ≠ 0) (hpbar : pbar ≠ 0) (hq0 : 0 ≤ α * β) (hq1 : α * β < 1) (t : ℕ)
    {g' : ℕ → ℝ → Ω → ℝ} {g : ℕ → ℝ → Ω → ℝ} {x : ℕ → Ω → ℝ} {u : ℕ → ℝ} (hu : Summable u)
    (hg : ∀ k y o, y ∈ Metric.ball (0 : ℝ) r → HasDerivAt (fun s => g k s o) (g' k y o) y)
    (hg' : ∀ k y o, y ∈ Metric.ball (0 : ℝ) r → ‖g' k y o‖ ≤ u k)
    (hg0 : ∀ o, Summable fun k => g k 0 o)
    (hfoc : ∀ y ∈ Metric.ball (0 : ℝ) r, 𝔼.E t (fun o => ∑' k, g k y o) = 0)
    (hval : ∀ k o, g' k 0 o = c * pbar * ((α * β) ^ k * x k o))
    (hx : ∀ k o, |x k o| ≤ C + D * k) :
    ∀ o, ∑' k, (α * β) ^ k * 𝔼.E t (x k) o = 0 := by
  have h := linearised_FOC_uncertain 𝔼 hr hu t hg hg' hg0 hfoc
  have hfun : (fun o => ∑' k, g' k 0 o) =
      (c * pbar) • fun o => ∑' k, (α * β) ^ k * x k o := by
    funext o
    simp only [hval, Pi.smul_apply, smul_eq_mul, tsum_mul_left]
  rw [hfun, map_smul] at h
  intro o
  have h1 := congrFun h o
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  have h2 := (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hc hpbar)
  have hb : ∀ k o, |(α * β) ^ k * x k o| ≤ (α * β) ^ k * (C + D * k) := fun k o => by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 k)]
    exact mul_le_mul_of_nonneg_left (hx k o) (pow_nonneg hq0 k)
  rw [E_tsum_polyGeom 𝔼 hq0 hq1 hb t o] at h2
  rw [← h2]
  refine tsum_congr fun k => ?_
  rw [show (fun o => (α * β) ^ k * x k o) = (α * β) ^ k • x k from rfl, map_smul,
    Pi.smul_apply, smul_eq_mul]

end Woodford.NominalRigidities.TwoSector
