/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.ResetPrice
import BasicNewKeynesianModel.PriceDuration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Marginal cost and the optimal reset price

Galí (2015), Chapter 3, §3.3 (pp. 58–60).

## Main results

* `eq14_exact`: the exact aggregate employment identity
  `(1 − α) n_t = y_t − a_t + d_t`, with `d_t` the price-dispersion term; `eq14`:
  equation (14) when `d_t = 0` (the dispersion term is studied elsewhere);
  `dispersion_symmetric`: `d_t = 0` when all prices are equal.
* `log_marginal_cost`: firm marginal cost `ψ = w − (a − α n + log(1 − α))`.
* `average_marginal_cost`, `log_aggregate_first_order`: average marginal cost
  across price cohorts, `ψ_t = w_t − (a_t − α n_t + log(1 − α))`, exactly in the
  cohort average of employment and to first order in `n_t`.
* `eq15`: `ψ_{t+k|t} = ψ_{t+k} − (αε/(1 − α))(p*_t − p_{t+k})`.
* `Theta_pos`, `Theta_le_one`, `Theta_eq_one_iff`: `Θ ∈ (0, 1]`, `Θ = 1 ↔ α = 0`.
* `pstar_formula`: `p*_t = (1 − βθ) ∑ₖ (βθ)ᵏ E_t[p_{t+k} − Θ μ̂_{t+k}]`.
* `eq16`, `eq16_unique`, `eq16_of_eq11`: the recursive form (16) and the
  uniqueness of its bounded solution.
-/

namespace Gali.BasicNewKeynesianModel.MarginalCost

open Filter Topology

/-! ### Aggregate employment, eq. (14) -/

/-- Aggregate employment `N_t = ∫ (Y_t(i)/A_t)^{1/(1−α)} di` with
`Y_t(i) = (P_t(i)/P_t)^{−ε} Y_t` (Galí (2015), p. 59, using (5), (1) and goods
market clearing), for a continuum of firms `ι` with measure `ν`. -/
noncomputable def employment {ι : Type*} [MeasurableSpace ι] (ν : MeasureTheory.Measure ι)
    (α ε Y A P : ℝ) (p : ι → ℝ) : ℝ :=
  ∫ i, ((p i / P) ^ (-ε) * Y / A) ^ (1 / (1 - α)) ∂ν

/-- The price-dispersion term `d_t = (1 − α) log ∫ (P_t(i)/P_t)^{−ε/(1−α)} di`
(Galí (2015), p. 59). -/
noncomputable def dispersion {ι : Type*} [MeasurableSpace ι] (ν : MeasureTheory.Measure ι)
    (α ε P : ℝ) (p : ι → ℝ) : ℝ :=
  (1 - α) * Real.log (∫ i, (p i / P) ^ (-ε / (1 - α)) ∂ν)

/-- **The exact employment identity** (Galí (2015), p. 59):
`(1 − α) n_t = y_t − a_t + d_t`. -/
theorem eq14_exact {ι : Type*} [MeasurableSpace ι] (ν : MeasureTheory.Measure ι)
    {α ε Y A P : ℝ} (hα : α < 1) (hY : 0 < Y) (hA : 0 < A) (hP : 0 < P) {p : ι → ℝ}
    (hp : ∀ i, 0 < p i) (hD : 0 < ∫ i, (p i / P) ^ (-ε / (1 - α)) ∂ν) :
    (1 - α) * Real.log (employment ν α ε Y A P p)
      = Real.log Y - Real.log A + dispersion ν α ε P p := by
  have h1 : 1 - α ≠ 0 := by linarith
  have hint : (fun i => ((p i / P) ^ (-ε) * Y / A) ^ (1 / (1 - α)))
      = fun i => (p i / P) ^ (-ε / (1 - α)) * (Y / A) ^ (1 / (1 - α)) := by
    funext i
    have hpi : 0 ≤ p i / P := (div_pos (hp i) hP).le
    rw [mul_div_assoc, Real.mul_rpow (Real.rpow_nonneg hpi _) (div_pos hY hA).le,
      ← Real.rpow_mul hpi]
    congr 2
    ring
  have hc : 0 < (Y / A) ^ (1 / (1 - α)) := Real.rpow_pos_of_pos (div_pos hY hA) _
  unfold employment dispersion
  rw [hint, MeasureTheory.integral_mul_const, Real.log_mul hD.ne' hc.ne',
    Real.log_rpow (div_pos hY hA), Real.log_div hY.ne' hA.ne']
  field_simp
  ring

/-- With equal prices across firms and a probability measure of firms, there is no
dispersion: `d_t = 0` (Galí (2015), p. 59, the symmetric case). -/
theorem dispersion_symmetric {ι : Type*} [MeasurableSpace ι] (ν : MeasureTheory.Measure ι)
    [MeasureTheory.IsProbabilityMeasure ν] {α ε P : ℝ} (hP : 0 < P) :
    dispersion ν α ε P (fun _ => P) = 0 := by
  simp [dispersion, div_self hP.ne']

/-- **Equation (14)** (Galí (2015), p. 59): with no price dispersion (`d_t = 0`,
true to first order around the zero-inflation steady state),
`n_t = (y_t − a_t)/(1 − α)`. -/
theorem eq14 {α n y a d : ℝ} (hα : α < 1) (h : (1 - α) * n = y - a + d) (hd : d = 0) :
    n = (y - a) / (1 - α) := by
  have h1 : 1 - α ≠ 0 := by linarith
  rw [hd, add_zero] at h
  field_simp
  linarith

/-! ### Marginal cost -/

/-- The production function (5) in logs (Galí (2015), p. 55):
`log(A N^{1−α}) = a + (1 − α) n`. -/
theorem log_production {α A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    Real.log (A * N ^ (1 - α)) = Real.log A + (1 - α) * Real.log N := by
  rw [Real.log_mul hA.ne' (Real.rpow_pos_of_pos hN _).ne', Real.log_rpow hN]

/-- **Firm marginal cost** (Galí (2015), p. 59 and fn. 3): nominal marginal cost
`Ψ = W / MPN` with `MPN = (1 − α) A N^{−α}`, so in logs
`ψ = w − (a − α n + log(1 − α))`. -/
theorem log_marginal_cost {α W A N : ℝ} (hα : α < 1) (hW : 0 < W) (hA : 0 < A)
    (hN : 0 < N) :
    Real.log (W / ((1 - α) * A * N ^ (-α)))
      = Real.log W - (Real.log A - α * Real.log N + Real.log (1 - α)) := by
  have h1 : 0 < 1 - α := by linarith
  rw [Real.log_div hW.ne' (by positivity), Real.log_mul (by positivity)
    (Real.rpow_pos_of_pos hN _).ne', Real.log_mul h1.ne' hA.ne', Real.log_rpow hN]
  ring

/-- The demand schedule (9) with goods-market clearing (12) in logs (Galí (2015),
p. 60): `log((P*/P)^{−ε} C) = −ε (p* − p) + c`. -/
theorem log_demand {ε Ps P C : ℝ} (hPs : 0 < Ps) (hP : 0 < P) (hC : 0 < C) :
    Real.log ((Ps / P) ^ (-ε) * C) = -ε * (Real.log Ps - Real.log P) + Real.log C := by
  rw [Real.log_mul (Real.rpow_pos_of_pos (div_pos hPs hP) _).ne' hC.ne',
    Real.log_rpow (div_pos hPs hP), Real.log_div hPs.ne' hP.ne']

/-- **Average marginal cost across price cohorts** (Galí (2015), p. 60): with
cohort weights `(1 − θ)θᵏ`, the average of `ψ_{t|t−k} = w − (a − α n_{t|t−k} +
log(1 − α))` is `w − (a − α n̄ + log(1 − α))`, where `n̄` is the cohort average of
log employment. -/
theorem average_marginal_cost {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (w a α : ℝ)
    {n : ℕ → ℝ} (hn : Summable fun k => durationProb θ k * n k) :
    ∑' k, durationProb θ k * (w - (a - α * n k + Real.log (1 - α)))
      = w - (a - α * ∑' k, durationProb θ k * n k + Real.log (1 - α)) := by
  have hd : Summable fun k => durationProb θ k :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left (1 - θ)
  have h : ∀ k, durationProb θ k * (w - (a - α * n k + Real.log (1 - α)))
      = durationProb θ k * (w - a - Real.log (1 - α)) + α * (durationProb θ k * n k) := by
    intro k; ring
  simp_rw [h]
  rw [Summable.tsum_add (hd.mul_right _) (hn.mul_left α), tsum_mul_right, tsum_mul_left,
    survival_sum hθ0 hθ1]
  ring

/-- **Log of aggregate employment equals average log employment to first order**
(Galí (2015), p. 60, "holds up to a first order approximation about a symmetric
equilibrium"). Perturbing cohort log employment `n_{t|t−k} = n̄ + s n̂ₖ` around a
symmetric point, `log ∑ (1 − θ)θᵏ e^{n_{t|t−k}} − ∑ (1 − θ)θᵏ n_{t|t−k}` vanishes
together with its derivative at `s = 0`. -/
theorem log_aggregate_first_order {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (nbar : ℝ)
    {nhat : ℕ → ℝ} {B : ℝ} (hB : ∀ k, |nhat k| ≤ B) :
    (Real.log (∑' k, durationProb θ k * Real.exp (nbar + 0 * nhat k))
        - ∑' k, durationProb θ k * (nbar + 0 * nhat k) = 0) ∧
    HasDerivAt (fun s => Real.log (∑' k, durationProb θ k * Real.exp (nbar + s * nhat k))
        - ∑' k, durationProb θ k * (nbar + s * nhat k)) 0 0 := by
  have hd : Summable fun k => durationProb θ k :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left (1 - θ)
  have hd0 : ∀ k, 0 ≤ durationProb θ k := fun k => durationProb_nonneg hθ0 hθ1.le k
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hS : Summable fun k => durationProb θ k * nhat k := by
    refine Summable.of_norm_bounded (hd.mul_right B) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd0 k)]
    exact mul_le_mul_of_nonneg_left (hB k) (hd0 k)
  have hsum1 : ∑' k, durationProb θ k = 1 := survival_sum hθ0 hθ1
  have hval : ∑' k, durationProb θ k * Real.exp (nbar + 0 * nhat k) = Real.exp nbar := by
    simp only [zero_mul, add_zero]
    rw [tsum_mul_right, hsum1, one_mul]
  have hlin : ∀ s, ∑' k, durationProb θ k * (nbar + s * nhat k)
      = nbar + s * ∑' k, durationProb θ k * nhat k := by
    intro s
    have : ∀ k, durationProb θ k * (nbar + s * nhat k)
        = durationProb θ k * nbar + s * (durationProb θ k * nhat k) := fun k => by ring
    simp_rw [this]
    rw [Summable.tsum_add (hd.mul_right _) (hS.mul_left s), tsum_mul_right, tsum_mul_left,
      hsum1, one_mul]
  refine ⟨by rw [hval, Real.log_exp, hlin, zero_mul, add_zero, sub_self], ?_⟩
  -- derivative of the aggregate
  have hD := hasDerivAt_tsum_of_isPreconnected
    (u := fun k => durationProb θ k * (B * Real.exp (|nbar| + B)))
    (g := fun k s => durationProb θ k * Real.exp (nbar + s * nhat k))
    (g' := fun k s => durationProb θ k * (nhat k * Real.exp (nbar + s * nhat k)))
    (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
    (hd.mul_right _) isOpen_Ioo isPreconnected_Ioo
    (fun k s _ => by
      have h1 : HasDerivAt (fun s => nbar + s * nhat k) (nhat k) s := by
        simpa using ((hasDerivAt_id s).mul_const (nhat k)).const_add nbar
      have h2 := (Real.hasDerivAt_exp _).comp s h1
      refine (h2.const_mul (durationProb θ k)).congr_deriv ?_
      ring)
    (fun k s hs => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd0 k), abs_mul,
        abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul_of_nonneg_left (mul_le_mul (hB k) ?_ (Real.exp_pos _).le hB0)
        (hd0 k)
      rw [Real.exp_le_exp]
      have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
      calc nbar + s * nhat k ≤ |nbar| + |s * nhat k| := add_le_add (le_abs_self _)
            (le_abs_self _)
        _ = |nbar| + |s| * |nhat k| := by rw [abs_mul]
        _ ≤ |nbar| + 1 * B := by
            have := mul_le_mul hs1 (hB k) (abs_nonneg _) zero_le_one
            linarith
        _ = |nbar| + B := by ring)
    ⟨by norm_num, by norm_num⟩
    (by
      simp only [zero_mul, add_zero]
      exact hd.mul_right _)
    ⟨by norm_num, by norm_num⟩
  have hpos : (∑' k, durationProb θ k * Real.exp (nbar + 0 * nhat k)) ≠ 0 := by
    rw [hval]; exact (Real.exp_pos _).ne'
  have hlog := hD.log hpos
  have hlinD : HasDerivAt (fun s => ∑' k, durationProb θ k * (nbar + s * nhat k))
      (∑' k, durationProb θ k * nhat k) 0 := by
    simp_rw [hlin]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (∑' k, durationProb θ k * nhat k)).const_add
      nbar
  refine (HasDerivAt.sub hlog hlinD).congr_deriv ?_
  rw [hval]
  simp only [zero_mul, add_zero]
  have : ∀ k, durationProb θ k * (nhat k * Real.exp nbar)
      = Real.exp nbar * (durationProb θ k * nhat k) := fun k => by ring
  simp_rw [this]
  rw [tsum_mul_left]
  field_simp
  ring

/-- **Equation (15)** (Galí (2015), p. 60). With firm and average marginal cost
`ψ = w − (a − α n + log(1 − α))`, the firm production function in logs
`y_{t+k|t} = a + (1 − α) n_{t+k|t}`, the aggregate relation (14)
`(1 − α) n = y − a`, demand (9) in logs and goods-market clearing (12):
`ψ_{t+k|t} = ψ_{t+k} + α(n_{t+k|t} − n_{t+k})
          = ψ_{t+k} + (α/(1 − α))(y_{t+k|t} − y_{t+k})
          = ψ_{t+k} − (αε/(1 − α))(p*_t − p_{t+k})`. -/
theorem eq15 {α ε w a ni n yi y ps p c ψi ψ : ℝ} (hα : α < 1)
    (hψi : ψi = w - (a - α * ni + Real.log (1 - α)))
    (hψ : ψ = w - (a - α * n + Real.log (1 - α)))
    (hyi : yi = a + (1 - α) * ni) (hy : (1 - α) * n = y - a)
    (hdem : yi = -ε * (ps - p) + c) (hc : c = y) :
    ψi = ψ + α * (ni - n) ∧ ψi = ψ + α / (1 - α) * (yi - y) ∧
      ψi = ψ - α * ε / (1 - α) * (ps - p) := by
  have h1 : 1 - α ≠ 0 := by linarith
  have e1 : ψi = ψ + α * (ni - n) := by rw [hψi, hψ]; ring
  have hn : ni - n = (yi - y) / (1 - α) := by
    field_simp
    linarith
  refine ⟨e1, ?_, ?_⟩
  · rw [e1, hn]; ring
  · rw [e1, hn, hdem, hc]
    field_simp
    ring

/-- Under constant returns (`α = 0`) firm-specific and average marginal cost
coincide, `ψ_{t+k|t} = ψ_{t+k}` (Galí (2015), p. 60). -/
theorem eq15_crs {ε w a ni n yi y ps p c ψi ψ : ℝ}
    (hψi : ψi = w - (a - 0 * ni + Real.log (1 - 0)))
    (hψ : ψ = w - (a - 0 * n + Real.log (1 - 0)))
    (hyi : yi = a + (1 - 0) * ni) (hy : (1 - 0) * n = y - a)
    (hdem : yi = -ε * (ps - p) + c) (hc : c = y) : ψi = ψ := by
  have := (eq15 (α := 0) (by norm_num) hψi hψ hyi hy hdem hc).2.2
  simpa using this

/-! ### The optimal reset price -/

/-- `Θ = (1 − α)/(1 − α + αε)` (Galí (2015), p. 60). -/
noncomputable def Theta (α ε : ℝ) : ℝ := (1 - α) / (1 - α + α * ε)

/-- `Θ > 0` (Galí (2015), p. 60). -/
theorem Theta_pos {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) : 0 < Theta α ε :=
  div_pos (by linarith) (by nlinarith)

/-- `Θ ≤ 1` (Galí (2015), p. 60). -/
theorem Theta_le_one {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) : Theta α ε ≤ 1 := by
  unfold Theta
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- `Θ = 1` exactly under constant returns, `α = 0` (Galí (2015), p. 61). -/
theorem Theta_eq_one_iff {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) :
    Theta α ε = 1 ↔ α = 0 := by
  unfold Theta
  rw [div_eq_one_iff_eq (by nlinarith)]
  constructor
  · intro h
    have : α * ε = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hε.ne'
  · intro h; rw [h]; ring

/-- `Θ (1 + αε/(1 − α)) = 1`: `Θ` is the inverse of one plus the strategic
complementarity coefficient of (15) (Galí (2015), p. 60). -/
theorem Theta_mul {α ε : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hε : 0 < ε) :
    Theta α ε * (1 + α * ε / (1 - α)) = 1 := by
  unfold Theta
  have h1 : 1 - α ≠ 0 := by linarith
  have h2 : 1 - α + α * ε ≠ 0 := by nlinarith
  field_simp

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- The markup gap `μ̂_t = μ_t − μ`, with average markup `μ_t = p_t − ψ_t`
(Galí (2015), p. 60). -/
def markupGap (μ : ℝ) (p ψ : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ := p t - ψ t - fun _ => μ

/-- A discounted affine sum: `∑ aᵏ (c + d₁ fₖ + d₂ gₖ)` (Galí (2015), p. 60). -/
theorem tsum_geom_affine {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f g : ℕ → ℝ}
    (hf : Summable fun k => a ^ k * f k) (hg : Summable fun k => a ^ k * g k) (c d₁ d₂ : ℝ) :
    ∑' k, a ^ k * (c + d₁ * f k + d₂ * g k)
      = c * (1 - a)⁻¹ + d₁ * ∑' k, a ^ k * f k + d₂ * ∑' k, a ^ k * g k := by
  have hgeo := summable_geometric_of_lt_one ha0 ha1
  have h : ∀ k, a ^ k * (c + d₁ * f k + d₂ * g k)
      = (a ^ k * c + d₁ * (a ^ k * f k)) + d₂ * (a ^ k * g k) := fun k => by ring
  simp_rw [h]
  rw [Summable.tsum_add ((hgeo.mul_right c).add (hf.mul_left d₁)) (hg.mul_left d₂),
    Summable.tsum_add (hgeo.mul_right c) (hf.mul_left d₁), tsum_mul_right, tsum_mul_left,
    tsum_mul_left, tsum_geometric_of_lt_one ha0 ha1]
  ring

/-- **The optimal reset price in terms of markup gaps** (Galí (2015), p. 60).
Substituting (15), `ψ_{t+k|t} = ψ_{t+k} − (αε/(1 − α))(p*_t − p_{t+k})`, into (11),
`p*_t = μ + (1 − βθ) ∑ₖ (βθ)ᵏ E_t ψ_{t+k|t}`, gives
`p*_t = (1 − βθ) ∑ₖ (βθ)ᵏ E_t[p_{t+k} − Θ μ̂_{t+k}]`. Here `a = βθ ∈ [0, 1)`. -/
theorem pstar_formula {a α ε μ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 < ε) {pstar p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (t : ℕ)
    (hpa : 𝔼.E t (pstar t) = pstar t)
    (h11 : pstar t = (fun _ => μ) + (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun s => ψ s - (α * ε / (1 - α)) • (pstar t - p s)) t) :
    pstar t = (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun s => p s - Theta α ε • markupGap μ p ψ s) t := by
  have ha : |a| < 1 := by rwa [abs_of_nonneg ha0]
  set κ := α * ε / (1 - α) with hκ
  set Θ := Theta α ε with hΘ
  have hΘκ : Θ * (1 + κ) = 1 := Theta_mul hα0 hα1 hε
  funext ω
  set X := pstar t ω with hX
  set A : ℕ → ℝ := fun k => 𝔼.E t (ψ (t + k)) ω with hA
  set B : ℕ → ℝ := fun k => 𝔼.E t (p (t + k)) ω with hB
  have hsA : Summable fun k => a ^ k * A k :=
    ResetPrice.summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hψ t (t + k) ω') ω
  have hsB : Summable fun k => a ^ k * B k :=
    ResetPrice.summable_geometric_bounded ha (fun k ω' => 𝔼.bounded_E hp t (t + k) ω') ω
  have hE1 : ∀ k, 𝔼.E t (ψ (t + k) - κ • (pstar t - p (t + k))) ω
      = -κ * X + 1 * A k + κ * B k := by
    intro k
    simp only [map_sub, map_smul, hpa, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hA, hB, hX]
    ring
  have hE2 : ∀ k, 𝔼.E t (p (t + k) - Θ • markupGap μ p ψ (t + k)) ω
      = Θ * μ + Θ * A k + (1 - Θ) * B k := by
    intro k
    simp only [markupGap, map_sub, map_smul, 𝔼.const, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hA, hB]
    ring
  have h11ω := congrFun h11 ω
  simp only [ResetPrice.forwardSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hE1] at h11ω
  rw [tsum_geom_affine ha0 ha1 hsA hsB] at h11ω
  simp only [ResetPrice.forwardSum, Pi.smul_apply, smul_eq_mul, hE2]
  rw [tsum_geom_affine ha0 ha1 hsA hsB]
  have hd : 1 - a ≠ 0 := by linarith
  set SA := ∑' k, a ^ k * A k
  set SB := ∑' k, a ^ k * B k
  have e1 : (1 - a) * (-κ * X * (1 - a)⁻¹ + 1 * SA + κ * SB)
      = -κ * X + (1 - a) * SA + κ * (1 - a) * SB := by
    field_simp
  have e2 : (1 - a) * (Θ * μ * (1 - a)⁻¹ + Θ * SA + (1 - Θ) * SB)
      = Θ * μ + Θ * (1 - a) * SA + (1 - Θ) * (1 - a) * SB := by
    field_simp
  rw [e2]
  have h' : X = μ + (-κ * X + (1 - a) * SA + κ * (1 - a) * SB) := by
    rw [← e1]; exact h11ω
  linear_combination Θ * h' - (X - (1 - a) * SB) * hΘκ

/-- The forcing process of (16), `x_t = p_t − Θ μ̂_t`, is bounded when `p` and `ψ` are
(Galí (2015), p. 60). -/
theorem forcing_bounded {α ε μ : ℝ} {p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (t : ℕ) (ω : Ω) :
    |(p t - Theta α ε • markupGap μ p ψ t) ω| ≤ M + |Theta α ε| * (M + M + |μ|) := by
  simp only [markupGap, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  refine (abs_sub _ _).trans (add_le_add (hp t ω) ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add (hp t ω) (hψ t ω)))
    le_rfl)

/-- The forcing process of (16) is adapted when `p` and `ψ` are
(Galí (2015), p. 60). -/
theorem forcing_adapted {α ε μ : ℝ} {p ψ : ℕ → Ω → ℝ} (hpa : 𝔼.Adapted p)
    (hψa : 𝔼.Adapted ψ) : 𝔼.Adapted fun t => p t - Theta α ε • markupGap μ p ψ t := by
  intro t
  simp only [markupGap, map_sub, map_smul, hpa t, hψa t, 𝔼.const]

/-- **Equation (16)** (Galí (2015), p. 60): the reset price
`p*_t = (1 − βθ) ∑ₖ (βθ)ᵏ E_t[p_{t+k} − Θ μ̂_{t+k}]` satisfies
`p*_t = βθ E_t p*_{t+1} + (1 − βθ)(p_t − Θ μ̂_t)`. -/
theorem eq16 {a α ε μ : ℝ} (ha : |a| < 1) {p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (hpa : 𝔼.Adapted p)
    (hψa : 𝔼.Adapted ψ) (t : ℕ) :
    (1 - a) • ResetPrice.forwardSum 𝔼 a (fun s => p s - Theta α ε • markupGap μ p ψ s) t
      = a • 𝔼.E t ((1 - a) • ResetPrice.forwardSum 𝔼 a
          (fun s => p s - Theta α ε • markupGap μ p ψ s) (t + 1))
        + (1 - a) • (p t - Theta α ε • markupGap μ p ψ t) :=
  ResetPrice.normForward_rec 𝔼 ha (forcing_bounded hp hψ) (forcing_adapted 𝔼 hpa hψa) t

/-- **Uniqueness for (16)** (Galí (2015), p. 60): the series for `p*` is the only
bounded process satisfying `p*_t = βθ E_t p*_{t+1} + (1 − βθ)(p_t − Θ μ̂_t)`. -/
theorem eq16_unique {a α ε μ : ℝ} (ha : |a| < 1) {p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (hpa : 𝔼.Adapted p)
    (hψa : 𝔼.Adapted ψ) {S : ℕ → Ω → ℝ} (hS : BoundedProc S)
    (hrec : ∀ t, S t = a • 𝔼.E t (S (t + 1))
      + (1 - a) • (p t - Theta α ε • markupGap μ p ψ t)) :
    S = fun t => (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun s => p s - Theta α ε • markupGap μ p ψ s) t :=
  ResetPrice.normForward_unique 𝔼 ha (forcing_bounded hp hψ) (forcing_adapted 𝔼 hpa hψa) hS
    hrec

/-- **From (11) and (15) to (16)** (Galí (2015), p. 60): if the reset price obeys
the log-linear rule (11) with firm-specific marginal cost (15) at every date, then
it obeys the recursion (16) at every date. -/
theorem eq16_of_eq11 {a α ε μ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hα0 : 0 ≤ α)
    (hα1 : α < 1) (hε : 0 < ε) {pstar p ψ : ℕ → Ω → ℝ} {M : ℝ}
    (hp : ∀ t ω, |p t ω| ≤ M) (hψ : ∀ t ω, |ψ t ω| ≤ M) (hpa : 𝔼.Adapted p)
    (hψa : 𝔼.Adapted ψ) (hsa : 𝔼.Adapted pstar)
    (h11 : ∀ t, pstar t = (fun _ => μ) + (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun s => ψ s - (α * ε / (1 - α)) • (pstar t - p s)) t) (t : ℕ) :
    pstar t = a • 𝔼.E t (pstar (t + 1)) + (1 - a) • (p t - Theta α ε • markupGap μ p ψ t) := by
  have ha : |a| < 1 := by rwa [abs_of_nonneg ha0]
  have hf : ∀ s, pstar s = (1 - a) • ResetPrice.forwardSum 𝔼 a
      (fun r => p r - Theta α ε • markupGap μ p ψ r) s := fun s =>
    pstar_formula 𝔼 ha0 ha1 hα0 hα1 hε hp hψ s (hsa s) (h11 s)
  rw [hf t, hf (t + 1)]
  exact eq16 𝔼 ha hp hψ hpa hψa t

end Gali.BasicNewKeynesianModel.MarginalCost
