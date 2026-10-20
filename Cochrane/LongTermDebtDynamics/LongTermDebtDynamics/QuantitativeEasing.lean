/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LongTermDebtDynamics.PolicyConstraints

/-!
# Quantitative easing and friends

Cochrane (2023), §7.6, pp. 229–234, equations (7.22)–(7.24).

The Treasury keeps a geometric maturity structure `B_{t−1}^{(t+j)} = ω^j B`; the central bank buys
or sells long-term bonds once at date 0, `B̃_0^{(j)}` (held to maturity), and issues one-period
reserves `M_{t−1}^{(t)}`. As in the book the path after the date-0 shock is perfect foresight
(price levels are real numbers `P_j > 0`); the maturity-structure irrelevance result of §7.6.2 is
proved for an arbitrary expectation system.

## Main results

* `steady_state` — (7.22): `∑_j β^j ω^j B/P = B/(P(1−βω)) = s/(1−β)`, and the steady-state price
  level `steady_price`.
* `pv_iff_723` — (7.23): with (7.22), the present-value relation at `t` is equivalent to
  `M_{t−1}^{(t)} P/(B P_t) + ∑_{j≥t} β^{j−t}(ω^{j−t} + B̃_0^{(j)}/B) P/P_j = 1/(1−βω)`.
* `reserves_unique`, `reserves_formula`: reverse engineering: given the price path and the QE
  purchases, (7.23) determines the reserves uniquely ("All M" when `B̃ = 0`).
* `qe_unique`: given the price path and the reserves, the QE purchases are unique;
  `qe_exists`: they exist (explicit formula) when the residual's tail series converge (e.g. bounded,
  `qe_residual_summable`); `qe_exists_necessary`, `qe_counterexample`: existence requires
  `β^N R_{t+N} → 0` and fails for reserves making `R_t = β^{−t}` (`solve_tail*`).
* `pv_iff_724` — (7.24): the same relation written with bond prices `Q_t^{(j)} = β^{j−t} P_t/P_j`.
* `Irrelevance.maturity_irrelevance`: (§7.6.2) any two debt policies with the same nominal market
value at
  each date satisfy the same present-value relations, under uncertainty.
* `strong_qe`: (p. 233) with `B_0^{(j)} = P_j s_j`, scaling the supply by `λ` scales `P_j` by `λ`
  and the bond price `Q_0^{(j)}` by `1/λ`: a 1% *decrease* in supply *raises* the bond price by
  about 1% (the book says it lowers it).
-/

namespace Cochrane.LongTermDebtDynamics.QuantitativeEasing

open Filter Topology MaturityStructure

/-- Cochrane (2023), eq. (7.22), p. 230: the steady state with a geometric maturity structure,
`∑_j β^j ω^j B/P = B/(P(1−βω))`, for `0 ≤ βω < 1`. -/
theorem steady_state {β ω B P : ℝ} (h0 : 0 ≤ β * ω) (h1 : β * ω < 1) :
    HasSum (fun j : ℕ => β ^ j * (ω ^ j * B / P)) (B / (P * (1 - β * ω))) := by
  have := (hasSum_geometric_of_lt_one h0 h1).mul_right (B / P)
  convert this using 1
  · funext j; rw [mul_pow]; ring
  · rw [div_mul_eq_div_div, div_eq_mul_inv, mul_comm]

/-- Cochrane (2023), eq. (7.22), p. 230: the steady-state price level solves
`B/(P(1−βω)) = s/(1−β)`, i.e. `P = B(1−β)/(s(1−βω))`. -/
theorem steady_price {β ω B P s : ℝ} (h1 : β * ω < 1) (hβ : β < 1) (hP : 0 < P) (hs : s ≠ 0) :
    B / (P * (1 - β * ω)) = s / (1 - β) ↔ P = B * (1 - β) / (s * (1 - β * ω)) := by
  have h2 : 1 - β * ω ≠ 0 := by linarith
  have h3 : 1 - β ≠ 0 := by linarith
  rw [div_eq_div_iff (mul_ne_zero hP.ne' h2) h3, eq_div_iff (mul_ne_zero hs h2)]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), §7.6.1, p. 230: the present-value relation at `t ≥ 1` with Treasury debt
`ω^{j−t} B`, QE bonds `B̃_0^{(j)} = b j` and reserves `M_{t−1}^{(t)} = Mr t` (perfect foresight):
`M_{t−1}^{(t)}/P_t + ∑_{j≥t} β^{j−t}(ω^{j−t}B + B̃_0^{(j)})/P_j = s/(1−β)`. -/
def QEPresentValue (β ω B s : ℝ) (b Mr P : ℕ → ℝ) (t : ℕ) : Prop :=
  HasSum (fun k : ℕ => β ^ k * ((ω ^ k * B + b (t + k)) / P (t + k))) (s / (1 - β) - Mr t / P t)

/-- Cochrane (2023), eq. (7.23), p. 230: the normalised present-value relation
`M_{t−1}^{(t)} P/(B P_t) + ∑_{j≥t} β^{j−t}(ω^{j−t} + B̃_0^{(j)}/B) P/P_j = 1/(1−βω)`. -/
def Eq723 (β ω B Pss : ℝ) (b Mr P : ℕ → ℝ) (t : ℕ) : Prop :=
  HasSum (fun k : ℕ => β ^ k * ((ω ^ k + b (t + k) / B) * Pss / P (t + k)))
    (1 / (1 - β * ω) - Mr t * Pss / (B * P t))

/-- Cochrane (2023), eq. (7.23), p. 230: **using the steady state (7.22), the present-value
relation is equivalent to (7.23).** -/
theorem pv_iff_723 {β ω B s Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) (h1 : β * ω < 1)
    (hss : B / (Pss * (1 - β * ω)) = s / (1 - β)) {b Mr P : ℕ → ℝ} (t : ℕ) :
    QEPresentValue β ω B s b Mr P t ↔ Eq723 β ω B Pss b Mr P t := by
  have hc : Pss / B ≠ 0 := div_ne_zero hP.ne' hB.ne'
  unfold QEPresentValue Eq723
  rw [← hasSum_mul_left_iff hc]
  have h2 : 1 - β * ω ≠ 0 := by linarith
  have hfun : (fun k : ℕ => Pss / B * (β ^ k * ((ω ^ k * B + b (t + k)) / P (t + k)))) =
      fun k : ℕ => β ^ k * ((ω ^ k + b (t + k) / B) * Pss / P (t + k)) := by
    funext k
    field_simp
  have hval : Pss / B * (s / (1 - β) - Mr t / P t) = 1 / (1 - β * ω) - Mr t * Pss / (B * P t) := by
    rw [← hss]
    field_simp
  rw [hfun, hval]

/-- Cochrane (2023), §7.6.1, p. 230 (reverse engineering): given the price path and the QE
purchases (with a convergent series `S_t = ∑_k β^k (ω^k + B̃/B) P/P_{t+k}`), (7.23) holds exactly
for
the reserves `M_{t−1}^{(t)} = (B P_t / P)(1/(1−βω) − S_t)`, and for no others. -/
theorem reserves_formula {β ω B Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) {b Mr P : ℕ → ℝ}
    (hPt : ∀ t, 0 < P t) (t : ℕ) {S : ℝ}
    (hS : HasSum (fun k : ℕ => β ^ k * ((ω ^ k + b (t + k) / B) * Pss / P (t + k))) S) :
    Eq723 β ω B Pss b Mr P t ↔ Mr t = B * P t / Pss * (1 / (1 - β * ω) - S) := by
  unfold Eq723
  constructor
  · intro h
    have := h.unique hS
    have hPt' := (hPt t).ne'
    field_simp at this ⊢
    rw [mul_sub, mul_one_div]
    linarith
  · intro h
    convert hS using 1
    rw [h]
    have hPt' := (hPt t).ne'
    field_simp
    ring

/-- Cochrane (2023), §7.6.1, p. 230: the reserves supporting a price path with given QE purchases
are unique. -/
theorem reserves_unique {β ω B Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) {b Mr Mr' P : ℕ → ℝ}
    (hPt : ∀ t, 0 < P t) (t : ℕ) (h : Eq723 β ω B Pss b Mr P t)
    (h' : Eq723 β ω B Pss b Mr' P t) : Mr t = Mr' t := by
  have := h.unique h'
  have hPt' := (hPt t).ne'
  have hc : Pss / (B * P t) ≠ 0 := div_ne_zero hP.ne' (mul_ne_zero hB.ne' hPt')
  have : Mr t * (Pss / (B * P t)) = Mr' t * (Pss / (B * P t)) := by
    rw [mul_div_assoc', mul_div_assoc']; linarith
  exact mul_right_cancel₀ hc this

/-- Cochrane (2023), §7.6.1, p. 230 ("All M"): with no QE purchases, (7.23) determines the
reserves `M_{t−1}^{(t)} = (B P_t/P)(1/(1−βω) − ∑_k (βω)^k P/P_{t+k})`. -/
theorem all_M {β ω B Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) {Mr P : ℕ → ℝ}
    (hPt : ∀ t, 0 < P t) (t : ℕ) {S : ℝ}
    (hS : HasSum (fun k : ℕ => (β * ω) ^ k * (Pss / P (t + k))) S) :
    Eq723 β ω B Pss (fun _ => 0) Mr P t ↔ Mr t = B * P t / Pss * (1 / (1 - β * ω) - S) := by
  refine reserves_formula hB hP hPt t ?_
  convert hS using 1
  funext k
  rw [mul_pow]
  simp only [zero_div, add_zero]
  ring

/-- Cochrane (2023), §7.6.1, p. 230 (reverse engineering, the other direction): given the price
path and the reserves, the QE purchases satisfying (7.23) at every date `t ≥ 1` are unique. -/
theorem qe_unique {β ω B Pss : ℝ} (hB : 0 < B) {b b' Mr P : ℕ → ℝ} (hPt : ∀ t, 0 < P t)
    (h : ∀ t, Eq723 β ω B Pss b Mr P (t + 1)) (h' : ∀ t, Eq723 β ω B Pss b' Mr P (t + 1))
    (hPss : Pss ≠ 0) (t : ℕ) : b (t + 1) = b' (t + 1) := by
  -- `g_j = (b_j − b'_j) P/(B P_j)` has `∑_k β^k g_{t+k} = 0` at every `t ≥ 1`
  set g : ℕ → ℝ := fun j => (b j - b' j) / B * Pss / P j with hg
  have hG : ∀ t, HasSum (fun k : ℕ => β ^ k * g (t + 1 + k)) 0 := by
    intro t
    have := (h t).sub (h' t)
    rw [sub_self] at this
    convert this using 1
    funext k
    simp only [hg]
    ring
  have hrec := (hasSum_nat_add_iff' 1).mpr (hG t)
  simp only [Finset.sum_range_one, pow_zero, one_mul, add_zero, zero_sub] at hrec
  have h2 : HasSum (fun k : ℕ => β ^ (k + 1) * g (t + 1 + (k + 1))) 0 := by
    have := (hG (t + 1)).mul_left β
    rw [mul_zero] at this
    convert this using 1
    funext k
    rw [pow_succ, show t + 1 + (k + 1) = t + 1 + 1 + k by omega]
    ring
  have hg0 : g (t + 1) = 0 := by
    have := hrec.unique h2
    linarith
  simp only [hg] at hg0
  have hPt' := (hPt (t + 1)).ne'
  rcases mul_eq_zero.mp (div_eq_zero_iff.mp hg0 |>.resolve_right hPt') with h0 | h0
  · rcases div_eq_zero_iff.mp h0 with h00 | h00
    · linarith
    · exact absurd h00 hB.ne'
  · exact absurd h0 hPss

/-- Cochrane (2023), §7.6.1, p. 230 (solving `∑_k β^k c_{t+k} = R_t` for `c`): if every tail
series `∑_k β^k R_{t+k}` converges, then `c_t = R_t − β R_{t+1}` solves it at every date. -/
theorem solve_tail {β : ℝ} {R : ℕ → ℝ} (hR : ∀ t, Summable (fun k : ℕ => β ^ k * R (t + k)))
    (t : ℕ) : HasSum (fun k : ℕ => β ^ k * (R (t + k) - β * R (t + k + 1))) (R t) := by
  have h1 := (hR t).hasSum
  have h2 := ((hR (t + 1)).hasSum).mul_left β
  have hsplit := (hR t).tsum_eq_zero_add
  simp only [pow_zero, one_mul, add_zero] at hsplit
  convert h1.sub h2 using 1
  · funext k
    rw [show t + 1 + k = t + k + 1 by omega]
    ring
  · have : ∑' k : ℕ, β ^ (k + 1) * R (t + (k + 1)) =
        β * ∑' k : ℕ, β ^ k * R (t + 1 + k) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      rw [pow_succ, show t + (k + 1) = t + 1 + k by omega]
      ring
    rw [hsplit, this]
    ring

/-- Cochrane (2023), §7.6.1, p. 230: conversely, a solution of `∑_k β^k c_{t+k} = R_t` at every
date is unique, `c_t = R_t − β R_{t+1}`, and it exists only if `β^N R_{t+N} → 0`. -/
theorem solve_tail_necessary {β : ℝ} {R c : ℕ → ℝ}
    (hc : ∀ t, HasSum (fun k : ℕ => β ^ k * c (t + k)) (R t)) (t : ℕ) :
    c t = R t - β * R (t + 1) ∧ Tendsto (fun N : ℕ => β ^ N * R (t + N)) atTop (𝓝 0) := by
  have hrec : ∀ u, R u = c u + β * R (u + 1) := by
    intro u
    have h := (hasSum_nat_add_iff' 1).mpr (hc u)
    simp only [Finset.sum_range_one, pow_zero, one_mul, add_zero] at h
    have h2 := (hc (u + 1)).mul_left β
    have : (fun k : ℕ => β ^ (k + 1) * c (u + (k + 1))) =
        fun k : ℕ => β * (β ^ k * c (u + 1 + k)) := by
      funext k; rw [pow_succ, show u + (k + 1) = u + 1 + k by omega]; ring
    rw [this] at h
    have := h.unique h2
    linarith
  refine ⟨by linarith [hrec t], ?_⟩
  have hpart : ∀ N, ∑ k ∈ Finset.range N, β ^ k * c (t + k) = R t - β ^ N * R (t + N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hrec (t + N), pow_succ, show t + (N + 1) = t + N + 1 by
        omega]
      ring
  have hlim := (hc t).tendsto_sum_nat
  simp only [hpart] at hlim
  have := (tendsto_const_nhds (x := R t)).sub hlim
  simpa using this

/-- Cochrane (2023), §7.6.1, p. 230: the condition `β^N R_{t+N} → 0` cannot be dropped: for
`0 < β < 1` and `R_t = β^{−t}` no sequence `c` has `∑_k β^k c_{t+k} = R_t` at every date. -/
theorem solve_tail_counterexample {β : ℝ} (hβ0 : 0 < β) :
    ¬ ∃ c : ℕ → ℝ, ∀ t, HasSum (fun k : ℕ => β ^ k * c (t + k)) ((β ^ t)⁻¹) := by
  rintro ⟨c, hc⟩
  have h := (solve_tail_necessary (R := fun t => (β ^ t)⁻¹) hc 0).2
  have : (fun N : ℕ => β ^ N * (fun t => (β ^ t)⁻¹) (0 + N)) = fun _ => 1 := by
    funext N; simp [mul_inv_cancel₀ (pow_ne_zero N hβ0.ne')]
  rw [this] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- Cochrane (2023), §7.6.1, p. 230: the residual that the QE purchases must finance in (7.23),
`R_t = 1/(1−βω) − M_{t−1}^{(t)} P/(B P_t) − ∑_k (βω)^k P/P_{t+k}` (`T t` is the Treasury series). -/
noncomputable def qeResidual (β ω B Pss : ℝ) (Mr P T : ℕ → ℝ) (t : ℕ) : ℝ :=
  1 / (1 - β * ω) - Mr t * Pss / (B * P t) - T t

/-- Cochrane (2023), §7.6.1, p. 230 (reverse engineering, existence): given the price path and
the reserves, if the tail series of the residual converge (e.g. the residual is bounded,
`qe_residual_summable`), the QE purchases
`B̃_0^{(j)} = B (R_j − β R_{j+1}) P_j / P` satisfy (7.23) at every date. -/
theorem qe_exists {β ω B Pss : ℝ} (hB : 0 < B) (hP : 0 < Pss) {Mr P T : ℕ → ℝ}
    (hPt : ∀ t, 0 < P t)
    (hT : ∀ t, HasSum (fun k : ℕ => β ^ k * (ω ^ k * Pss / P (t + k))) (T t))
    (hR : ∀ t, Summable (fun k : ℕ => β ^ k * qeResidual β ω B Pss Mr P T (t + k))) (t : ℕ) :
    Eq723 β ω B Pss (fun j => B * (qeResidual β ω B Pss Mr P T j -
      β * qeResidual β ω B Pss Mr P T (j + 1)) * P j / Pss) Mr P t := by
  unfold Eq723
  have h := (hT t).add (solve_tail hR t)
  convert h using 1
  · funext k
    have hPk := (hPt (t + k)).ne'
    field_simp
  · simp only [qeResidual]
    ring

/-- Cochrane (2023), §7.6.1, p. 230: a bounded residual has convergent tail series (`0 ≤ β < 1`),
so under the book's bounded paths the QE purchases exist. -/
theorem qe_residual_summable {β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {R : ℕ → ℝ}
    (hK : ∀ t, |R t| ≤ K) (t : ℕ) : Summable (fun k : ℕ => β ^ k * R (t + k)) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
    exact mul_le_mul_of_nonneg_left (hK _) (pow_nonneg hβ0 k)

/-- Cochrane (2023), §7.6.1, p. 230: conversely, if QE purchases satisfying (7.23) at every date
exist, then `β^N R_{t+N} → 0`; with reserves making `R_t = β^{−t}` (possible for any price path,
`qe_counterexample`) no QE policy supports the path. -/
theorem qe_exists_necessary {β ω B Pss : ℝ} {b Mr P T : ℕ → ℝ}
    (hT : ∀ t, HasSum (fun k : ℕ => β ^ k * (ω ^ k * Pss / P (t + k))) (T t))
    (hb : ∀ t, Eq723 β ω B Pss b Mr P t) (t : ℕ) :
    Tendsto (fun N : ℕ => β ^ N * qeResidual β ω B Pss Mr P T (t + N)) atTop (𝓝 0) := by
  refine (solve_tail_necessary (c := fun j => b j / B * Pss / P j) (fun u => ?_) t).2
  have := (hb u).sub (hT u)
  convert this using 1
  · funext k
    ring
  · simp only [qeResidual]

/-- Cochrane (2023), §7.6.1, p. 230: **existence can fail.** For `0 < β < 1` and any positive price
path, the reserves `M_{t−1}^{(t)} = (1/(1−βω) − T_t − β^{−t}) B P_t / P` allow no QE purchases
satisfying (7.23) at every date. -/
theorem qe_counterexample {β ω B Pss : ℝ} (hβ0 : 0 < β) (hB : 0 < B) (hP : 0 < Pss)
    {P T : ℕ → ℝ} (hPt : ∀ t, 0 < P t)
    (hT : ∀ t, HasSum (fun k : ℕ => β ^ k * (ω ^ k * Pss / P (t + k))) (T t)) :
    ¬ ∃ b : ℕ → ℝ, ∀ t, Eq723 β ω B Pss b
      (fun t => (1 / (1 - β * ω) - T t - (β ^ t)⁻¹) * B * P t / Pss) P t := by
  rintro ⟨b, hb⟩
  have h := qe_exists_necessary hT hb 0
  have hres : ∀ N, qeResidual β ω B Pss
      (fun t => (1 / (1 - β * ω) - T t - (β ^ t)⁻¹) * B * P t / Pss) P T (0 + N) =
      (β ^ N)⁻¹ := by
    intro N
    simp only [qeResidual, zero_add]
    have := (hPt N).ne'
    field_simp
    ring
  simp only [hres] at h
  have : (fun N : ℕ => β ^ N * (β ^ N)⁻¹) = fun _ => 1 := by
    funext N; exact mul_inv_cancel₀ (pow_ne_zero N hβ0.ne')
  rw [this] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- Cochrane (2023), eq. (7.24), p. 232: with perfect-foresight bond prices
`Q_t^{(j)} = β^{j−t} P_t/P_j`, the present-value relation reads
`(M_{t−1}^{(t)} + ∑_{j≥t}(Bω^{j−t} + B̃_0^{(j)}) Q_t^{(j)})/P_t = B/((1−βω)P)`. -/
theorem pv_iff_724 {β ω B s Pss : ℝ} (hss : B / (Pss * (1 - β * ω)) = s / (1 - β))
    {b Mr P : ℕ → ℝ} (hPt : ∀ t, 0 < P t) (t : ℕ) :
    QEPresentValue β ω B s b Mr P t ↔
      HasSum (fun k : ℕ => (ω ^ k * B + b (t + k)) * (β ^ k * P t / P (t + k)) / P t)
        (B / ((1 - β * ω) * Pss) - Mr t / P t) := by
  unfold QEPresentValue
  have hPt' := (hPt t).ne'
  have hfun : (fun k : ℕ => (ω ^ k * B + b (t + k)) * (β ^ k * P t / P (t + k)) / P t) =
      fun k : ℕ => β ^ k * ((ω ^ k * B + b (t + k)) / P (t + k)) := by
    funext k
    field_simp
  rw [hfun, show B / ((1 - β * ω) * Pss) = s / (1 - β) by rw [← hss, mul_comm]]

/-! ### Maturity structure is irrelevant (§7.6.2) -/

namespace Irrelevance

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Cochrane (2023), §7.6.2, p. 232: **only the total market value of debt matters.** Two debt
policies with the same nominal market value `∑_j Q_t^{(t+j)} B_{t−1}^{(t+j)}` at date `t` satisfy
the
present-value relation at `t` for exactly the same price levels. -/
theorem maturity_irrelevance (hpo : 𝔼.PullOut) {β : ℝ} {D D' : ℕ → ℕ → Ω → ℝ}
    {P x s : ℕ → Ω → ℝ} (hP : 𝔼.Adapted P) (hPx : ∀ t ω, P t ω * x t ω = 1) (t : ℕ)
    {N : Ω → ℝ} (hN : ∀ ω, HasSum (fun j => bondPrice 𝔼 β P x t j ω * D t (t + j) ω) (N ω))
    (hN' : ∀ ω, HasSum (fun j => bondPrice 𝔼 β P x t j ω * D' t (t + j) ω) (N ω)) :
    PresentValue 𝔼 β D x s t ↔ PresentValue 𝔼 β D' x s t := by
  have hreal : ∀ (E : ℕ → ℕ → Ω → ℝ) ω, HasSum (fun j => bondPrice 𝔼 β P x t j ω *
      E t (t + j) ω) (N ω) → HasSum (fun j => debtTerm 𝔼 β E x t j ω) (x t ω * N ω) := by
    intro E ω h
    have := h.mul_left (x t ω)
    convert this using 1
    funext j
    rw [bondPrice_eq 𝔼 hpo hP, debtTerm]
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    linear_combination (-(β ^ j * E t (t + j) ω * 𝔼.E t (x (t + j)) ω)) * hPx t ω
  constructor
  · intro h ω
    refine ⟨(h ω).1, ?_⟩
    rw [← ((hreal D ω (hN ω)).unique (h ω).2)]
    exact hreal D' ω (hN' ω)
  · intro h ω
    refine ⟨(h ω).1, ?_⟩
    rw [← ((hreal D' ω (hN' ω)).unique (h ω).2)]
    exact hreal D ω (hN ω)

end Irrelevance

/-- Cochrane (2023), p. 233 (strong QE): with `B_0^{(j)} = P_j s_j` and `Q_0^{(j)} = β^j P_0/P_j`
(`P_0` fixed), scaling the supply by `λ > 0` scales `P_j` by `λ` and `Q_0^{(j)}` by `1/λ`. So a 1%
decrease in supply (`λ = 0.99`) lowers `P_j` by 1% and *raises* the bond price by about 1%
(`1/0.99 − 1 ∈ (1.01%, 1.02%)`); the book's "decrease in bond price" has the wrong sign. -/
theorem strong_qe {β P0 sj B lam : ℝ} (j : ℕ) (hs : sj ≠ 0) (hB : B ≠ 0) (hl : lam ≠ 0) :
    lam * B / sj = lam * (B / sj) ∧
      β ^ j * P0 / (lam * B / sj) = (β ^ j * P0 / (B / sj)) / lam ∧
      (0.0101 : ℝ) < 1 / 0.99 - 1 ∧ (1 / 0.99 - 1 : ℝ) < 0.0102 := by
  refine ⟨by ring, ?_, by norm_num, by norm_num⟩
  field_simp

end Cochrane.LongTermDebtDynamics.QuantitativeEasing
