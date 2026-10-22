/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.TidyR5Prop34Uncertainty
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Galí–Gertler hybrid model and indexation (3.6)

Woodford (2003), *Interest and Prices*, Chapter 3, §3.2, pp. 216–217. The book compares the
indexation model (3.6) with "the generalization of the Calvo model proposed by Gali and Gertler
(1999)": prices are fixed for Calvo intervals, but a fraction of adjusters use a backward-looking
rule of thumb. It claims that "in the limiting case `β = 1`, the two models have identical
implications" and that "relation (3.6) for any given value of `γ` can be obtained from the
Gali-Gertler model through an appropriate choice of the fraction of backward-looking
pricesetters".

## The Galí–Gertler model

Log price index `p_t = θ p_{t−1} + (1 − θ) x_t` (`θ` the probability of not adjusting, the book's
`α`), adjusters' average price `x_t = (1 − ϖ) p^f_t + ϖ p^b_t` (`ϖ` the backward-looking share),
rule of thumb `p^b_t = x_{t−1} + π_{t−1}`, and forward-looking optimal price
`p^f_t = (1 − βθ) ∑_k (βθ)ᵏ E_t[mc_{t+k} + p_{t+k}]`.

* `pf_rec_of_forward`: the forward sum gives the recursive form (no growth restriction, through
  `TidyR5Prop34Uncertainty.E_hasSum`).
* `gg_hybrid_iff`: for every expectation system, the recursive optimal-price condition is
  equivalent to the hybrid Phillips curve `π_t = γ_b π_{t−1} + γ_f E_t π_{t+1} + λ mc_t` with
  `φ = θ + ϖ(1 − θ(1 − β))`, `γ_b = ϖ/φ`, `γ_f = βθ/φ`, `λ = (1 − ϖ)(1 − θ)(1 − βθ)/φ`
  (the Galí–Gertler formulas).

## The book's claims

The hybrid form of (3.6) is `π_t = γ/(1 + βγ) π_{t−1} + β/(1 + βγ) E_t π_{t+1} + …`
(`Delays.eq_3_6_iff_hybrid`).

* `gg_weights_match_iff`: for `0 ≤ γ ≤ 1` and `0 < β ≤ 1`, some Galí–Gertler model (any Calvo
  parameter `θ ∈ (0, 1)` and share `ϖ ∈ [0, 1)`) has exactly the lag and lead weights of (3.6) iff
  `γ = 0` or `β = 1`. So the second claim holds in the limiting case `β = 1` only: for `β < 1`
  and `γ > 0` no choice of the backward-looking share reproduces (3.6).
* `gg_same_theta_slope`: at `β = 1` with the same Calvo parameter (`ϖ = θγ`), the weights match
  but the slope on marginal cost is `(1 − θγ)` times that of (3.6).
* `gg_identical_beta_one`: at `β = 1`, for every `γ ∈ [0, 1]` and every target slope `s > 0`
  there are `θ' ∈ (0, 1)` and `ϖ = θ'γ` reproducing (3.6) exactly (weights and slope) — the first
  claim, made precise: identical implications require re-choosing the Calvo parameter as well.
-/

namespace Woodford.NominalRigidities.TidyR5GaliGertler

open Filter Topology

/-- Woodford (2003), p. 217 (Galí–Gertler 1999): `φ = θ + ϖ(1 − θ(1 − β))`. -/
noncomputable def ggPhi (θ β ϖ : ℝ) : ℝ := θ + ϖ * (1 - θ * (1 - β))

/-- Woodford (2003), p. 217 (Galí–Gertler 1999): the backward weight `γ_b = ϖ/φ`. -/
noncomputable def ggBack (θ β ϖ : ℝ) : ℝ := ϖ / ggPhi θ β ϖ

/-- Woodford (2003), p. 217 (Galí–Gertler 1999): the forward weight `γ_f = βθ/φ`. -/
noncomputable def ggFwd (θ β ϖ : ℝ) : ℝ := β * θ / ggPhi θ β ϖ

/-- Woodford (2003), p. 217 (Galí–Gertler 1999): the slope `λ = (1 − ϖ)(1 − θ)(1 − βθ)/φ`. -/
noncomputable def ggSlope (θ β ϖ : ℝ) : ℝ := (1 - ϖ) * (1 - θ) * (1 - β * θ) / ggPhi θ β ϖ

/-- Woodford (2003), p. 217: `φ > 0` for `0 < θ < 1`, `β ≥ 0`, `ϖ ≥ 0`. -/
theorem ggPhi_pos {θ β ϖ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hβ0 : 0 ≤ β)
    (hϖ : 0 ≤ ϖ) : 0 < ggPhi θ β ϖ := by
  unfold ggPhi
  have : 0 ≤ 1 - θ * (1 - β) := by nlinarith
  nlinarith

/-- Woodford (2003), p. 217 (the Galí–Gertler algebra): with `K = (1 − θ)(1 − ϖ)`, writing
`p^f_t = p_{t−1} + (π_t − ϖ π_{t−1})/K` and `E_t p^f_{t+1} = p_t + (E_t π_{t+1} − ϖ π_t)/K`, the
optimal-price recursion `p^f_t = (1 − βθ)(mc_t + p_t) + βθ E_t p^f_{t+1}` holds iff
`π_t = γ_b π_{t−1} + γ_f E_t π_{t+1} + λ mc_t`. -/
theorem gg_algebra {θ β ϖ : ℝ} (hθ1 : θ ≠ 1) (hϖ1 : ϖ ≠ 1) (hφ : ggPhi θ β ϖ ≠ 0)
    (p0 p1 π1 π2 Eπ3 mc : ℝ) (hπ2 : π2 = p1 - p0) :
    p0 + (π2 - ϖ * π1) / ((1 - θ) * (1 - ϖ)) = (1 - β * θ) * (mc + p1)
        + β * θ * (p1 + (Eπ3 - ϖ * π2) / ((1 - θ) * (1 - ϖ))) ↔
      π2 = ggBack θ β ϖ * π1 + ggFwd θ β ϖ * Eπ3 + ggSlope θ β ϖ * mc := by
  have hK : (1 - θ) * (1 - ϖ) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (Ne.symm hθ1))
    (sub_ne_zero.mpr (Ne.symm hϖ1))
  unfold ggBack ggFwd ggSlope
  have key : (π2 - (ϖ / ggPhi θ β ϖ * π1 + β * θ / ggPhi θ β ϖ * Eπ3
      + (1 - ϖ) * (1 - θ) * (1 - β * θ) / ggPhi θ β ϖ * mc)) * ggPhi θ β ϖ
      = (p0 + (π2 - ϖ * π1) / ((1 - θ) * (1 - ϖ)) - ((1 - β * θ) * (mc + p1)
        + β * θ * (p1 + (Eπ3 - ϖ * π2) / ((1 - θ) * (1 - ϖ))))) * ((1 - θ) * (1 - ϖ)) := by
    subst hπ2
    unfold ggPhi at hφ ⊢
    field_simp
    ring
  constructor
  · intro h
    rw [sub_eq_zero.mpr h, zero_mul] at key
    have := (mul_eq_zero.mp key).resolve_right hφ
    linarith
  · intro h
    rw [sub_eq_zero.mpr h, zero_mul] at key
    have := (mul_eq_zero.mp key.symm).resolve_right hK
    linarith

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 217 (Galí–Gertler 1999, the forward-looking price): if
`p^f_t = (1 − βθ) ∑_k (βθ)ᵏ E_t[mc_{t+k} + p_{t+k}]` with the sum converging at every state and
date, and `mc + p` is adapted, then `p^f_t = (1 − βθ)(mc_t + p_t) + βθ E_t p^f_{t+1}`. -/
theorem pf_rec_of_forward {θ β : ℝ} {pf mcp : ℕ → Ω → ℝ} (hmcp : 𝔼.Adapted mcp)
    (hs : ∀ t ω, Summable (fun k => (β * θ) ^ k * 𝔼.E t (mcp (t + k)) ω))
    (hpf : ∀ t ω, pf t ω = (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (mcp (t + k)) ω) (t : ℕ)
    (ω : Ω) : pf t ω = (1 - β * θ) * mcp t ω + β * θ * 𝔼.E t (pf (t + 1)) ω := by
  set f : ℕ → Ω → ℝ := fun k => (β * θ) ^ k • 𝔼.E (t + 1) (mcp (t + 1 + k))
  have hF : pf (t + 1) = (1 - β * θ) • fun ω' => ∑' k, f k ω' := by
    funext ω'
    rw [hpf (t + 1) ω']
    rfl
  have hsum : ∀ ω', HasSum (fun k => f k ω') (∑' k, f k ω') := fun ω' => (hs (t + 1) ω').hasSum
  have hint := TidyR5Prop34Uncertainty.E_hasSum 𝔼 hsum t ω
  have hterm : ∀ k, 𝔼.E t (f k) ω = (β * θ) ^ k * 𝔼.E t (mcp (t + 1 + k)) ω := by
    intro k
    simp only [f]
    rw [map_smul, 𝔼.tower (Nat.le_succ t)]
    rfl
  have hE : 𝔼.E t (pf (t + 1)) ω = (1 - β * θ) * ∑' k, (β * θ) ^ k * 𝔼.E t (mcp (t + 1 + k)) ω := by
    rw [hF, map_smul, Pi.smul_apply, smul_eq_mul, hint.tsum_eq.symm]
    simp_rw [hterm]
  rw [hE, hpf t ω, (hs t ω).tsum_eq_zero_add]
  have htail : ∑' k, (β * θ) ^ (k + 1) * 𝔼.E t (mcp (t + (k + 1))) ω
      = β * θ * ∑' k, (β * θ) ^ k * 𝔼.E t (mcp (t + 1 + k)) ω := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring
  rw [htail, pow_zero, one_mul, add_zero, congrFun (hmcp t) ω]
  ring

/-- Woodford (2003), pp. 216–217 (**the Galí–Gertler hybrid Phillips curve, for every
expectation system**). Let `0 ≤ θ < 1`, `ϖ ≠ 1`, `φ ≠ 0`, the price level `p` adapted, and
`p_{t+1} = θ p_t + (1 − θ) x_{t+1}`, `x_t = (1 − ϖ) p^f_t + ϖ p^b_t`,
`p^b_{t+2} = x_{t+1} + π_{t+1}` with `π_{t+1} = p_{t+1} − p_t`. Then at every date `t + 2` the
optimal-price recursion `p^f = (1 − βθ)(mc + p) + βθ E p^f_{+1}` holds iff
`π_{t+2} = γ_b π_{t+1} + γ_f E_{t+2} π_{t+3} + λ mc_{t+2}`. -/
theorem gg_hybrid_iff {θ β ϖ : ℝ} (hθ1 : θ ≠ 1) (hϖ1 : ϖ ≠ 1) (hφ : ggPhi θ β ϖ ≠ 0)
    {p x pf pb mc : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p)
    (hp : ∀ t ω, p (t + 1) ω = θ * p t ω + (1 - θ) * x (t + 1) ω)
    (hx : ∀ t ω, x t ω = (1 - ϖ) * pf t ω + ϖ * pb t ω)
    (hb : ∀ t ω, pb (t + 2) ω = x (t + 1) ω + (p (t + 1) ω - p t ω)) (t : ℕ) (ω : Ω) :
    pf (t + 2) ω = (1 - β * θ) * (mc (t + 2) ω + p (t + 2) ω)
        + β * θ * 𝔼.E (t + 2) (pf (t + 3)) ω
      ↔ p (t + 2) ω - p (t + 1) ω = ggBack θ β ϖ * (p (t + 1) ω - p t ω)
        + ggFwd θ β ϖ * (𝔼.E (t + 2) (p (t + 3)) ω - p (t + 2) ω)
        + ggSlope θ β ϖ * mc (t + 2) ω := by
  have h1θ : (1 : ℝ) - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have h1ϖ : (1 : ℝ) - ϖ ≠ 0 := sub_ne_zero.mpr (Ne.symm hϖ1)
  -- `x` from the index, `p^f` from `x` and `p^b`
  have hxs : ∀ s ω', x (s + 1) ω' = (p (s + 1) ω' - θ * p s ω') / (1 - θ) := by
    intro s ω'
    rw [hp s ω']
    field_simp
    ring
  have hpf : ∀ s ω', pf (s + 2) ω' = p (s + 1) ω'
      + ((p (s + 2) ω' - p (s + 1) ω') - ϖ * (p (s + 1) ω' - p s ω')) / ((1 - θ) * (1 - ϖ)) := by
    intro s ω'
    have e1 : x (s + 2) ω' * (1 - θ) = p (s + 2) ω' - θ * p (s + 1) ω' := by
      have := hp (s + 1) ω'
      rw [show s + 1 + 1 = s + 2 by omega] at this
      linear_combination -this
    have e0 : x (s + 1) ω' * (1 - θ) = p (s + 1) ω' - θ * p s ω' := by
      linear_combination -(hp s ω')
    have hx2 := hx (s + 2) ω'
    rw [hb s ω'] at hx2
    have hK : pf (s + 2) ω' * ((1 - θ) * (1 - ϖ)) = p (s + 1) ω' * ((1 - θ) * (1 - ϖ))
        + ((p (s + 2) ω' - p (s + 1) ω') - ϖ * (p (s + 1) ω' - p s ω')) := by
      linear_combination (-1 + θ) * hx2 + e1 - ϖ * e0
    field_simp
    linear_combination hK
  -- the forecast of `p^f_{t+3}`
  have hEpf : 𝔼.E (t + 2) (pf (t + 3)) ω = p (t + 2) ω
      + ((𝔼.E (t + 2) (p (t + 3)) ω - p (t + 2) ω) - ϖ * (p (t + 2) ω - p (t + 1) ω))
        / ((1 - θ) * (1 - ϖ)) := by
    have hfun : pf (t + 3) = p (t + 2)
        + ((1 - θ) * (1 - ϖ))⁻¹ • (p (t + 3) - p (t + 2) - ϖ • (p (t + 2) - p (t + 1))) := by
      funext ω'
      rw [hpf (t + 1) ω']
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
    have hk : 𝔼.E (t + 2) (p (t + 1)) = p (t + 1) := by
      rw [← hpa (t + 1), 𝔼.known (by omega)]
    rw [hfun, map_add, map_smul, map_sub, map_sub, map_smul, map_sub, hpa (t + 2), hk]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
  rw [hpf t ω, hEpf]
  exact gg_algebra hθ1 hϖ1 hφ (p (t + 1) ω) (p (t + 2) ω) (p (t + 1) ω - p t ω)
    (p (t + 2) ω - p (t + 1) ω) (𝔼.E (t + 2) (p (t + 3)) ω - p (t + 2) ω) (mc (t + 2) ω) rfl

/-! ### The book's comparison with indexation (3.6) -/

/-- Woodford (2003), pp. 216–217 (**when can Galí–Gertler reproduce the weights of (3.6)?**):
for `0 ≤ γ ≤ 1` and `0 < β ≤ 1`, there are a Calvo parameter `θ ∈ (0, 1)` and a backward share
`ϖ ∈ [0, 1)` with `γ_b = γ/(1 + βγ)` and `γ_f = β/(1 + βγ)` iff `γ = 0` or `β = 1`. -/
theorem gg_weights_match_iff {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) :
    (∃ θ ϖ : ℝ, 0 < θ ∧ θ < 1 ∧ 0 ≤ ϖ ∧ ϖ < 1 ∧ ggBack θ β ϖ = γ / (1 + β * γ) ∧
      ggFwd θ β ϖ = β / (1 + β * γ)) ↔ (γ = 0 ∨ β = 1) := by
  have hd : 0 < 1 + β * γ := by nlinarith
  constructor
  · rintro ⟨θ, ϖ, hθ0, hθ1, hϖ0, -, hb, hf⟩
    have hφ := ggPhi_pos hθ0 hθ1 hβ0.le hϖ0
    unfold ggBack at hb
    unfold ggFwd at hf
    rw [div_eq_div_iff hφ.ne' hd.ne'] at hb hf
    have hφeq : θ * (1 + β * γ) = ggPhi θ β ϖ := by
      have : β * (θ * (1 + β * γ) - ggPhi θ β ϖ) = 0 := by linear_combination hf
      have := (mul_eq_zero.mp this).resolve_left hβ0.ne'
      linarith
    have hϖ : ϖ = θ * γ := by
      have : (ϖ - θ * γ) * (1 + β * γ) = 0 := by linear_combination hb - γ * hφeq
      have := (mul_eq_zero.mp this).resolve_right hd.ne'
      linarith
    unfold ggPhi at hφeq
    rw [hϖ] at hφeq
    have key : θ * γ * (1 - θ) * (1 - β) = 0 := by linear_combination -hφeq
    rcases mul_eq_zero.mp key with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · linarith
        · exact Or.inl h''
      · linarith
    · right; linarith
  · rintro (h | h)
    · refine ⟨1 / 2, 0, by norm_num, by norm_num, le_rfl, by norm_num, ?_, ?_⟩
      · simp [ggBack, h]
      · simp only [ggFwd, ggPhi, h]
        norm_num
    · refine ⟨1 / 2, γ / 2, by norm_num, by norm_num, by linarith, by linarith, ?_, ?_⟩
      · simp only [ggBack, ggPhi, h]
        field_simp
        ring
      · simp only [ggFwd, ggPhi, h]
        field_simp
        ring

/-- Woodford (2003), p. 217: at `β = 1` with `ϖ = θγ`, `φ = θ(1 + γ)`. -/
theorem ggPhi_beta_one (θ γ : ℝ) : ggPhi θ 1 (θ * γ) = θ * (1 + γ) := by
  unfold ggPhi
  ring

/-- Woodford (2003), p. 217 (**same Calvo parameter, `β = 1`**): with `ϖ = θγ` the Galí–Gertler
weights are `γ/(1 + γ)` and `1/(1 + γ)` — those of (3.6) at `β = 1` — but the slope on marginal
cost is `(1 − θγ)` times the slope `(1 − θ)²/(θ(1 + γ))` of (3.6) (Calvo, no strategic
complementarity, at `β = 1`), so the two coincide only for `γ = 0`. -/
theorem gg_same_theta_slope {θ γ : ℝ} (hθ0 : 0 < θ) (hγ0 : 0 ≤ γ) :
    ggBack θ 1 (θ * γ) = γ / (1 + γ) ∧ ggFwd θ 1 (θ * γ) = 1 / (1 + γ) ∧
      ggSlope θ 1 (θ * γ) = (1 - θ * γ) * ((1 - θ) ^ 2 / θ / (1 + γ)) := by
  have hγ : (1 : ℝ) + γ ≠ 0 := by linarith
  have hθ : θ ≠ 0 := hθ0.ne'
  have hφ := ggPhi_beta_one θ γ
  refine ⟨?_, ?_, ?_⟩
  · rw [ggBack, hφ]; field_simp
  · rw [ggFwd, hφ]; field_simp
  · rw [ggSlope, hφ]; field_simp

/-- Woodford (2003), p. 217: the Galí–Gertler slope at `β = 1` with `ϖ = θγ`, times `1 + γ`:
`(1 − θγ)(1 − θ)²/θ`. -/
noncomputable def slopeFn (γ θ : ℝ) : ℝ := (1 - θ * γ) * (1 - θ) ^ 2 / θ

/-- Woodford (2003), p. 217 (**"in the limiting case `β = 1`, the two models have identical
implications", made precise**): at `β = 1`, for every `γ ∈ [0, 1]` and every slope `s > 0` of
(3.6) on marginal cost (in hybrid form `s/(1 + γ)`), there is a Galí–Gertler model — Calvo
parameter `θ' ∈ (0, 1)` and backward share `ϖ = θ'γ ∈ [0, 1)` — with exactly the weights and the
slope of (3.6). -/
theorem gg_identical_beta_one {γ s : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : 0 < s) :
    ∃ θ' : ℝ, 0 < θ' ∧ θ' < 1 ∧ 0 ≤ θ' * γ ∧ θ' * γ < 1 ∧
      ggBack θ' 1 (θ' * γ) = γ / (1 + γ) ∧ ggFwd θ' 1 (θ' * γ) = 1 / (1 + γ) ∧
      ggSlope θ' 1 (θ' * γ) = s / (1 + γ) := by
  -- the endpoints for the intermediate value theorem
  set a := min (1 / 2) (1 / (8 * (s + 1))) with ha
  set b := max (1 / 2) (1 - min (1 / 2) (s / 4)) with hb
  have ha0 : 0 < a := lt_min (by norm_num) (by positivity)
  have ha2 : a ≤ 1 / 2 := min_le_left _ _
  have ha8 : a ≤ 1 / (8 * (s + 1)) := min_le_right _ _
  have hmin0 : 0 < min (1 / 2 : ℝ) (s / 4) := lt_min (by norm_num) (by positivity)
  have hb2 : 1 / 2 ≤ b := le_max_left _ _
  have hb1 : b < 1 := max_lt (by norm_num) (by linarith)
  have hab : a ≤ b := by linarith
  have hfa : s ≤ slopeFn γ a := by
    unfold slopeFn
    have h1 : 1 / 2 ≤ 1 - a * γ := by nlinarith
    have h2 : 1 / 4 ≤ (1 - a) ^ 2 := by nlinarith
    have h3 : 8 * (s + 1) * a ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at ha8
      linarith
    rw [le_div_iff₀ ha0]
    nlinarith
  have hfb : slopeFn γ b ≤ s := by
    unfold slopeFn
    have hb0 : 0 < b := by linarith
    have h1 : 1 - b * γ ≤ 1 := by nlinarith
    have h1' : 0 ≤ 1 - b * γ := by nlinarith
    have hm : 1 - b ≤ min (1 / 2 : ℝ) (s / 4) := by
      have := le_max_right (1 / 2 : ℝ) (1 - min (1 / 2) (s / 4))
      linarith
    have hm1 : 1 - b ≤ 1 / 2 := hm.trans (min_le_left _ _)
    have hm2 : 1 - b ≤ s / 4 := hm.trans (min_le_right _ _)
    have h0 : 0 ≤ 1 - b := by linarith
    rw [div_le_iff₀ hb0]
    have hsq : (1 - b) ^ 2 ≤ s / 8 := by nlinarith
    nlinarith
  have hcont : ContinuousOn (slopeFn γ) (Set.Icc a b) := by
    refine ContinuousOn.div (by fun_prop) continuousOn_id fun x hx => ?_
    exact (lt_of_lt_of_le ha0 hx.1).ne'
  obtain ⟨θ', hθ', hval⟩ := intermediate_value_Icc' hab hcont ⟨hfb, hfa⟩
  have hθ0 : 0 < θ' := lt_of_lt_of_le ha0 hθ'.1
  have hθ1 : θ' < 1 := lt_of_le_of_lt hθ'.2 hb1
  have hγ : (1 : ℝ) + γ ≠ 0 := by linarith
  have hθ : θ' ≠ 0 := hθ0.ne'
  have hφ := ggPhi_beta_one θ' γ
  refine ⟨θ', hθ0, hθ1, mul_nonneg hθ0.le hγ0, by nlinarith, ?_, ?_, ?_⟩
  · rw [ggBack, hφ]; field_simp
  · rw [ggFwd, hφ]; field_simp
  · rw [← hval, ggSlope, hφ, slopeFn]; field_simp

end Woodford.NominalRigidities.TidyR5GaliGertler
