/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import AssetsRulesBalanceSheets.FiscalRules

/-!
# A fiscal rule with inflation and interest rates

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 9 "Better rules", §9.3.4
"A fiscal rule with inflation and interest rates", eqs. (9.15)–(9.16), pp. 269–270.

Monetary policy follows `i_t = θ_{iπ} π_t + u_t` with `u_t = η u_{t−1} + ε_t`; with flexible prices
and a constant real rate `i_t = E_t π_{t+1}`, so (9.15) `E_t π_{t+1} = θ_{iπ} π_t + u_t`. Fiscal
policy sets `s_t = s_{0,t} + θ_{sπ} π_t`, and only indexed debt is outstanding, so
`b_{t−1} = E_t ∑ⱼ βʲ (s_{0,t+j} + θ_{sπ} π_{t+j})`.

Lean date `t` carries the real debt `b t` outstanding at the start of date `t` (book `b_{t−1}`).
Expected present values are sums of conditional expectations `∑ⱼ βʲ E_t x_{t+j}`.

## Main results

* `eq_9_15`; `E_pi_iterate`: `E_t π_{t+j} = θʲ π_t + fⱼ u_t` with `fⱼ = ∑_{k<j} θ^{j−1−k} ηᵏ`;
  `coefSeq_closed`: `(θ − η) fⱼ = θʲ − ηʲ`.
* `tsum_coefSeq`: `∑ⱼ βʲ fⱼ = β/((1 − βθ)(1 − βη))`, for `|βθ| < 1`, `|βη| < 1`.
* `eq_9_16`: the valuation equation becomes
  `b_{t−1} = θ_{sπ}/(1 − βθ_{iπ}) π_t + βθ_{sπ}/((1 − βθ_{iπ})(1 − βη)) u_t + E_t ∑ βʲ s_{0,t+j}`.
* `pi_determined`, `pi_eq`: with `θ_{sπ} ≠ 0` inflation is determined at each date;
  `pi_not_determined_without_surplus_response`: with `θ_{sπ} = 0` it is not;
  `rate_rule_essential`: without the interest-rate rule the valuation equation alone does not
  pin down the inflation path.
* `eq_theta_i_zero`: the `θ_{iπ} = 0` case, with the book's typo corrected (`b_t` → `b_{t−1}`,
  error E9.3).
-/

namespace Cochrane.AssetsRulesBalanceSheets.FiscalTaylor

open Filter Topology

/-- Cochrane (2023), (9.16), p. 270: the coefficients `f₀ = 0`, `f_{j+1} = θ fⱼ + ηʲ`, so that
`fⱼ = ∑_{k<j} θ^{j−1−k} ηᵏ = (θʲ − ηʲ)/(θ − η)`. -/
def coefSeq (θ η : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => θ * coefSeq θ η j + η ^ j

/-- Cochrane (2023), (9.16), p. 270: `(θ − η) fⱼ = θʲ − ηʲ`. -/
theorem coefSeq_closed (θ η : ℝ) (j : ℕ) : (θ - η) * coefSeq θ η j = θ ^ j - η ^ j := by
  induction j with
  | zero => simp [coefSeq]
  | succ j ih =>
    simp only [coefSeq]
    rw [pow_succ, pow_succ]
    linear_combination θ * ih

/-- Cochrane (2023), (9.16), p. 270: with `m ≥ |θ|, |η|`, `m > 0`, `|fⱼ| m ≤ j mʲ`. -/
theorem abs_coefSeq_le {θ η m : ℝ} (hθ : |θ| ≤ m) (hη : |η| ≤ m) (hm : 0 < m) (j : ℕ) :
    |coefSeq θ η j| * m ≤ j * m ^ j := by
  induction j with
  | zero => simp [coefSeq]
  | succ j ih =>
    simp only [coefSeq]
    have h1 : |θ * coefSeq θ η j + η ^ j| ≤ m * |coefSeq θ η j| + m ^ j := by
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
      · rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) hη j
    calc |θ * coefSeq θ η j + η ^ j| * m ≤ (m * |coefSeq θ η j| + m ^ j) * m :=
          mul_le_mul_of_nonneg_right h1 hm.le
      _ = m * (|coefSeq θ η j| * m) + m ^ (j + 1) := by ring
      _ ≤ m * (j * m ^ j) + m ^ (j + 1) := by gcongr
      _ = ((j + 1 : ℕ) : ℝ) * m ^ (j + 1) := by push_cast; ring

/-- Cochrane (2023), (9.16), p. 270: for `0 ≤ β < 1`, `|βθ| < 1` and `|βη| < 1` the series
`∑ βʲ fⱼ` converges absolutely. -/
theorem summable_coefSeq {β θ η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θ| < 1)
    (hη : |β * η| < 1) : Summable (fun j => β ^ j * coefSeq θ η j) := by
  set m := max (max |θ| |η|) 1 with hm_def
  have hm : 0 < m := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hθm : |θ| ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have hηm : |η| ≤ m := (le_max_right _ _).trans (le_max_left _ _)
  have hβm : β * m < 1 := by
    rw [hm_def, mul_max_of_nonneg _ _ hβ0, mul_max_of_nonneg _ _ hβ0, mul_one]
    rw [abs_mul, abs_of_nonneg hβ0] at hθ hη
    exact max_lt (max_lt hθ hη) hβ1
  have hβm0 : 0 ≤ β * m := mul_nonneg hβ0 hm.le
  have hg : Summable (fun j : ℕ => ((j : ℝ) ^ 1 * (β * m) ^ j) * m⁻¹) :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := β * m)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hβm0]; exact hβm)).mul_right _
  refine Summable.of_norm_bounded hg (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 j), pow_one, mul_pow]
  have h := abs_coefSeq_le hθm hηm hm j
  have h2 : |coefSeq θ η j| ≤ j * m ^ j * m⁻¹ := by
    rw [le_mul_inv_iff₀ hm]
    exact h
  calc β ^ j * |coefSeq θ η j| ≤ β ^ j * (j * m ^ j * m⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hβ0 j)
    _ = _ := by ring

/-- Cochrane (2023), (9.16), p. 270 (the double geometric sum):
`∑ⱼ βʲ fⱼ = β/((1 − βθ)(1 − βη))`. -/
theorem tsum_coefSeq {β θ η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θ| < 1)
    (hη : |β * η| < 1) : ∑' j, β ^ j * coefSeq θ η j = β / ((1 - β * θ) * (1 - β * η)) := by
  have hs := summable_coefSeq hβ0 hβ1 hθ hη
  have hgη := summable_geometric_of_abs_lt_one hη
  have h1θ : 1 - β * θ ≠ 0 := by
    have := (abs_lt.mp hθ).2
    linarith
  have h1η : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hη).2
    linarith
  have hrec : ∑' j, β ^ j * coefSeq θ η j =
      β * θ * ∑' j, β ^ j * coefSeq θ η j + β * (1 - β * η)⁻¹ := by
    conv_lhs => rw [hs.tsum_eq_zero_add]
    simp only [pow_zero, coefSeq, mul_zero, zero_add]
    have hsplit : (fun j => β ^ (j + 1) * (θ * coefSeq θ η j + η ^ j)) =
        fun j => β * θ * (β ^ j * coefSeq θ η j) + β * (β * η) ^ j := by
      funext j
      rw [mul_pow]
      ring
    rw [hsplit, (hs.mul_left (β * θ)).tsum_add (hgη.mul_left β), tsum_mul_left, tsum_mul_left,
      tsum_geometric_of_abs_lt_one hη]
  set F := ∑' j, β ^ j * coefSeq θ η j
  have h2 : F * (1 - β * θ) = β * (1 - β * η)⁻¹ := by linear_combination hrec
  rw [eq_div_iff (mul_ne_zero h1θ h1η)]
  calc F * ((1 - β * θ) * (1 - β * η)) = (F * (1 - β * θ)) * (1 - β * η) := by ring
    _ = β * (1 - β * η)⁻¹ * (1 - β * η) := by rw [h2]
    _ = β := by field_simp

/-- Cochrane (2023), (9.16), p. 270: `∑ⱼ (βθ)ʲ = 1/(1 − βθ)`. -/
theorem tsum_theta {β θ : ℝ} (hθ : |β * θ| < 1) :
    ∑' j, β ^ j * θ ^ j = 1 / (1 - β * θ) := by
  simp_rw [← mul_pow]
  rw [tsum_geometric_of_abs_lt_one hθ, one_div]

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), eq. (9.15), p. 270: the rule `i_t = θ_{iπ} π_t + u_t` with `i_t = E_t π_{t+1}`
gives `E_t π_{t+1} = θ_{iπ} π_t + u_t`. -/
theorem eq_9_15 {θ : ℝ} {π u i : ℕ → Ω → ℝ} (hrule : ∀ t, i t = θ • π t + u t)
    (hfisher : ∀ t, i t = 𝔼.E t (π (t + 1))) (t : ℕ) :
    𝔼.E t (π (t + 1)) = θ • π t + u t := by
  rw [← hfisher t, hrule t]

/-- Cochrane (2023), §9.3.4, p. 270 ("using (9.15) to eliminate expected future inflation"):
`E_t π_{t+j} = θʲ π_t + fⱼ u_t` for an AR(1) disturbance `u` with persistence `η`. -/
theorem E_pi_iterate {θ η : ℝ} {π u : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.IsAR1 η u)
    (h915 : ∀ t, 𝔼.E t (π (t + 1)) = θ • π t + u t) (t j : ℕ) :
    𝔼.E t (π (t + j)) = θ ^ j • π t + coefSeq θ η j • u t := by
  induction j with
  | zero => simp [coefSeq, hπ t]
  | succ j ih =>
    rw [← add_assoc, ← 𝔼.tower (Nat.le_add_right t j), h915 (t + j), map_add, map_smul, ih,
      𝔼.ar1_iterate hu t j, smul_add, smul_smul, smul_smul, coefSeq, pow_succ]
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), eq. (9.16), p. 270: substituting (9.15) into the valuation equation
`b_{t−1} = ∑ⱼ βʲ E_t (s_{0,t+j} + θ_{sπ} π_{t+j})` gives
`b_{t−1} = θ_{sπ}/(1 − βθ_{iπ}) π_t + βθ_{sπ}/((1 − βθ_{iπ})(1 − βη)) u_t + ∑ⱼ βʲ E_t s_{0,t+j}`
(convergence requires `|βθ_{iπ}| < 1` and `|βη| < 1`). -/
theorem eq_9_16 {β θi θs η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θi| < 1)
    (hη : |β * η| < 1) {π u s0 b : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.IsAR1 η u)
    (h915 : ∀ t, 𝔼.E t (π (t + 1)) = θi • π t + u t)
    (hs0 : ∀ t ω, Summable (fun j => β ^ j * 𝔼.E t (s0 (t + j)) ω))
    (hval : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω) (t : ℕ) (ω : Ω) :
    b t ω = θs / (1 - β * θi) * π t ω +
      β * θs / ((1 - β * θi) * (1 - β * η)) * u t ω + ∑' j, β ^ j * 𝔼.E t (s0 (t + j)) ω := by
  have hterm : ∀ j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω =
      β ^ j * 𝔼.E t (s0 (t + j)) ω + (θs * π t ω) * (β ^ j * θi ^ j) +
        (θs * u t ω) * (β ^ j * coefSeq θi η j) := by
    intro j
    rw [map_add, map_smul, E_pi_iterate 𝔼 hπ hu h915 t j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hgθ : Summable (fun j => β ^ j * θi ^ j) := by
    simp_rw [← mul_pow]
    exact summable_geometric_of_abs_lt_one hθ
  have hsf := summable_coefSeq hβ0 hβ1 hθ hη
  have h1θ : 1 - β * θi ≠ 0 := by
    have := (abs_lt.mp hθ).2
    linarith
  have h1η : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hη).2
    linarith
  rw [hval t ω, tsum_congr hterm, ((hs0 t ω).add (hgθ.mul_left _)).tsum_add (hsf.mul_left _),
    (hs0 t ω).tsum_add (hgθ.mul_left _), tsum_mul_left, tsum_mul_left, tsum_theta hθ,
    tsum_coefSeq hβ0 hβ1 hθ hη]
  field_simp
  ring

/-- Cochrane (2023), §9.3.4, p. 270 ("this equation now determines inflation at each date"):
with `θ_{sπ} ≠ 0`, inflation is given explicitly by the predetermined real debt, the monetary
disturbance and the present value of `s₀`. -/
theorem pi_eq {β θi θs η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θi| < 1)
    (hη : |β * η| < 1) (hθs : θs ≠ 0) {π u s0 b : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hu : 𝔼.IsAR1 η u) (h915 : ∀ t, 𝔼.E t (π (t + 1)) = θi • π t + u t)
    (hs0 : ∀ t ω, Summable (fun j => β ^ j * 𝔼.E t (s0 (t + j)) ω))
    (hval : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω) (t : ℕ) (ω : Ω) :
    π t ω = (1 - β * θi) / θs * (b t ω - ∑' j, β ^ j * 𝔼.E t (s0 (t + j)) ω) -
      β / (1 - β * η) * u t ω := by
  have h := eq_9_16 𝔼 hβ0 hβ1 hθ hη hπ hu h915 hs0 hval t ω
  have h1θ : 1 - β * θi ≠ 0 := by
    have := (abs_lt.mp hθ).2
    linarith
  have h1η : 1 - β * η ≠ 0 := by
    have := (abs_lt.mp hη).2
    linarith
  rw [h]
  field_simp
  ring

/-- Cochrane (2023), §9.3.4, p. 270: with `θ_{sπ} ≠ 0` inflation is determined — two inflation
processes satisfying (9.15) and the valuation equation with the same debt, disturbance and `s₀`
coincide. -/
theorem pi_determined {β θi θs η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hθ : |β * θi| < 1)
    (hη : |β * η| < 1) (hθs : θs ≠ 0) {π π' u s0 b : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π)
    (hπ' : 𝔼.Adapted π') (hu : 𝔼.IsAR1 η u) (h915 : ∀ t, 𝔼.E t (π (t + 1)) = θi • π t + u t)
    (h915' : ∀ t, 𝔼.E t (π' (t + 1)) = θi • π' t + u t)
    (hs0 : ∀ t ω, Summable (fun j => β ^ j * 𝔼.E t (s0 (t + j)) ω))
    (hval : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω)
    (hval' : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π' (t + j)) ω) : π = π' := by
  funext t ω
  rw [pi_eq 𝔼 hβ0 hβ1 hθ hη hθs hπ hu h915 hs0 hval t ω,
    pi_eq 𝔼 hβ0 hβ1 hθ hη hθs hπ' hu h915' hs0 hval' t ω]

/-- Cochrane (2023), §9.3.4, p. 270 ("without this response, `π_t` drops from the equation"):
with `θ_{sπ} = 0`, under perfect foresight with `u = 0`, `s₀ = 0`, `b = 0`, both `π ≡ 0` and
`π_t = θ_{iπ}ᵗ` satisfy (9.15) and the valuation equation. -/
theorem pi_not_determined_without_surplus_response {β θi : ℝ} :
    ∃ π π' : ℕ → Unit → ℝ,
      (∀ t, perfectForesight.E t (π (t + 1)) = θi • π t + 0) ∧
      (∀ t, perfectForesight.E t (π' (t + 1)) = θi • π' t + 0) ∧
      (∀ t ω, (0 : ℝ) = ∑' j, β ^ j * perfectForesight.E t (0 + (0 : ℝ) • π (t + j)) ω) ∧
      (∀ t ω, (0 : ℝ) = ∑' j, β ^ j * perfectForesight.E t (0 + (0 : ℝ) • π' (t + j)) ω) ∧
      π ≠ π' := by
  refine ⟨fun _ _ => 0, fun t _ => θi ^ t, fun t => ?_, fun t => ?_, fun t ω => ?_, fun t ω => ?_,
    ?_⟩
  · funext ω
    simp [perfectForesight]
  · funext ω
    simp only [perfectForesight, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply, add_zero]
    ring
  · simp [perfectForesight]
  · simp [perfectForesight]
  · intro h
    have := congrFun (congrFun h 0) ()
    simp at this

/-- Cochrane (2023), §9.3.4, p. 270 ("an interest-rate target is essential"): without the
interest-rate rule (9.15), the valuation equation with `θ_{sπ} ≠ 0` only pins down the
`β`-weighted sum of inflation. Under perfect foresight with `s₀ = 0` and `b_{−1} = 0`, both
`π ≡ 0` and `π = (β/2, −1/2, 0, …)` satisfy the date-0 valuation, with different `π_0`. -/
theorem rate_rule_essential {β : ℝ} (hβ : β ≠ 0) (θs : ℝ) :
    ∃ π π' : ℕ → ℝ, HasSum (fun j => β ^ j * (0 + θs * π j)) 0 ∧
      HasSum (fun j => β ^ j * (0 + θs * π' j)) 0 ∧ π 0 ≠ π' 0 := by
  refine ⟨fun _ => 0, FiscalRules.hyperplaneShift β, by simp, ?_, ?_⟩
  · have := (FiscalRules.hasSum_hyperplaneShift β).mul_left θs
    rw [mul_zero] at this
    refine this.congr_fun fun j => ?_
    ring
  · simp only [FiscalRules.hyperplaneShift, ↓reduceIte]
    intro h
    exact hβ (by linarith)

/-- Cochrane (2023), §9.3.4, p. 270, the `θ_{iπ} = 0` case (typo corrected, error E9.3: the book
writes `b_t` on the left, it is `b_{t−1}`, Lean `b t`): with `i_t = u_t`,
`b_{t−1} = θ_{sπ} π_t + βθ_{sπ}/(1 − βη) i_t + ∑ⱼ βʲ E_t s_{0,t+j}`. -/
theorem eq_theta_i_zero {β θs η : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hη : |β * η| < 1)
    {π u i s0 b : ℕ → Ω → ℝ} (hπ : 𝔼.Adapted π) (hu : 𝔼.IsAR1 η u)
    (hrule : ∀ t, i t = (0 : ℝ) • π t + u t) (hfisher : ∀ t, i t = 𝔼.E t (π (t + 1)))
    (hs0 : ∀ t ω, Summable (fun j => β ^ j * 𝔼.E t (s0 (t + j)) ω))
    (hval : ∀ t ω, b t ω = ∑' j, β ^ j * 𝔼.E t (s0 (t + j) + θs • π (t + j)) ω) (t : ℕ) (ω : Ω) :
    b t ω = θs * π t ω + β * θs / (1 - β * η) * i t ω + ∑' j, β ^ j * 𝔼.E t (s0 (t + j)) ω := by
  have h915 := eq_9_15 𝔼 hrule hfisher
  have h := eq_9_16 𝔼 hβ0 hβ1 (by simp) hη hπ hu h915 hs0 hval t ω
  have hi : i t ω = u t ω := by
    rw [hrule t]
    simp
  rw [h, hi]
  simp

end Cochrane.AssetsRulesBalanceSheets.FiscalTaylor
