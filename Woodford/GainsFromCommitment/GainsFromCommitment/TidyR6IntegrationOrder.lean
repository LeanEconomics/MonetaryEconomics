/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GainsFromCommitment.ExpectationsMeasureIID

/-!
# Orders of integration as properties of stochastic processes

Woodford (2003), *Interest and Prices*, Chapter 7, §2.1, p. 501: "Under optimal policy, the price
is an integrated process of order one, while under discretion it is an integrated process of order
two, since there is a unit root in the inflation rate" (with full indexation, `γ = 1`), and the
price level is stationary under optimal policy with `γ = 0`.

ImpulseResponses formalised these as root multiplicities at `z = 1` of lag polynomials. Here
"integrated of order `d`" is the genuine time-series notion on a probability space:

* `CovStationary μ y`: every y_t is square-integrable, the mean is constant and
  `Cov(y_t, y_{t+h})` does not depend on `t` (weak, or covariance, stationarity);
* `diffN d y`: the `d`-th forward difference `Δᵈy` (`(Δy)_t = y_{t+1} − y_t`);
* `IntegratedOfOrder μ d y`: `Δᵈy` is covariance stationary and `Δᵏy` is not for any `k < d`
  (the order of integration is the least number of differences that makes the process
  stationary). `I(1)` with `d = 1` is a unit-root process.

This module develops the general notions and the moment calculus for processes that are finite
linear combinations of i.i.d. fair-coin shocks (`lin`); the price-level applications are in
TidyR6IntegrationPolicy.

## Main results

* `CovStationary`, `diffN`, `IntegratedOfOrder`; `covStationary_congr_ae`,
  `integratedOfOrder_congr_ae` (only the a.e. class matters).
* `integral_coord`, `integral_coord_mul` (the coins are orthonormal in `L²`), `memLp_lin`,
  `integral_lin`, `cov_lin` (`Cov(y_t, y_r) = ∑_j b_{t,j}b_{r,j}`), `covStationary_lin_iff`,
  `not_covStationary_of_var_ne`.
-/

namespace Woodford.GainsFromCommitment.TidyR6IntegrationOrder

open MeasureTheory ProbabilityTheory Filter Topology
open ExpectationsMeasureIID

/-! ### Covariance stationarity and orders of integration -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Woodford (2003), p. 501 (time-series background): the covariance
`Cov(X, Y) = ∫ (X − EX)(Y − EY) dμ`. -/
noncomputable def cov (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - ∫ ω', X ω' ∂μ) * (Y ω - ∫ ω', Y ω' ∂μ) ∂μ

/-- Woodford (2003), p. 501 ("stationary"): a process is **covariance stationary** if every
y_t is square-integrable, its mean does not depend on `t`, and `Cov(y_t, y_{t+h})` depends on
the lag `h` only. -/
def CovStationary (μ : Measure Ω) (y : ℕ → Ω → ℝ) : Prop :=
  (∀ t, MemLp (y t) 2 μ) ∧ (∀ t, ∫ ω, y t ω ∂μ = ∫ ω, y 0 ω ∂μ) ∧
    ∀ t h, cov μ (y t) (y (t + h)) = cov μ (y 0) (y h)

/-- Woodford (2003), p. 501: the forward difference `(Δy)_t = y_{t+1} − y_t`. -/
def diff (y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun t ω => y (t + 1) ω - y t ω

/-- Woodford (2003), p. 501: the `d`-th difference `Δᵈy`. -/
def diffN : ℕ → (ℕ → Ω → ℝ) → ℕ → Ω → ℝ
  | 0, y => y
  | d + 1, y => diff (diffN d y)

/-- Woodford (2003), p. 501 (**integrated of order `d`**): `Δᵈy` is covariance stationary and no
lower difference `Δᵏy`, `k < d`, is. `I(0)` is covariance stationarity; `I(1)` is a unit-root
process (non-stationary, with a stationary first difference). -/
def IntegratedOfOrder (μ : Measure Ω) (d : ℕ) (y : ℕ → Ω → ℝ) : Prop :=
  CovStationary μ (diffN d y) ∧ ∀ k < d, ¬ CovStationary μ (diffN k y)

/-- Woodford (2003), p. 501: changing each y_t on a null set changes neither the moments nor
square-integrability. -/
theorem covStationary_congr_ae {μ : Measure Ω} {y z : ℕ → Ω → ℝ}
    (h : ∀ t, y t =ᵐ[μ] z t) : CovStationary μ y ↔ CovStationary μ z := by
  have hi : ∀ t, ∫ ω, y t ω ∂μ = ∫ ω, z t ω ∂μ := fun t => integral_congr_ae (h t)
  have hc : ∀ s t, cov μ (y s) (y t) = cov μ (z s) (z t) := fun s t => by
    unfold cov
    rw [hi s, hi t]
    refine integral_congr_ae ?_
    filter_upwards [h s, h t] with ω h1 h2
    rw [h1, h2]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun t => (h1 t).ae_eq (h t), fun t => by rw [← hi, ← hi]; exact h2 t,
      fun t k => by rw [← hc, ← hc]; exact h3 t k⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun t => (h1 t).ae_eq (h t).symm, fun t => by rw [hi, hi]; exact h2 t,
      fun t k => by rw [hc, hc]; exact h3 t k⟩

/-- Woodford (2003), p. 501: differences of a.e.-equal processes are a.e. equal. -/
theorem diffN_congr_ae {μ : Measure Ω} {y z : ℕ → Ω → ℝ} (h : ∀ t, y t =ᵐ[μ] z t) (d : ℕ) :
    ∀ t, diffN d y t =ᵐ[μ] diffN d z t := by
  induction d with
  | zero => exact h
  | succ d ih =>
    intro t
    filter_upwards [ih t, ih (t + 1)] with ω h1 h2
    simp only [diffN, diff, h1, h2]

/-- Woodford (2003), p. 501: the order of integration depends only on the a.e. class of the
process. -/
theorem integratedOfOrder_congr_ae {μ : Measure Ω} {y z : ℕ → Ω → ℝ} (h : ∀ t, y t =ᵐ[μ] z t)
    (d : ℕ) : IntegratedOfOrder μ d y ↔ IntegratedOfOrder μ d z := by
  unfold IntegratedOfOrder
  rw [covStationary_congr_ae (diffN_congr_ae h d)]
  exact and_congr_right fun _ => forall₂_congr fun k _ => by
    rw [covStationary_congr_ae (diffN_congr_ae h k)]

/-- Woodford (2003), p. 501: a process whose variance at some date differs from its variance at
date `0` is not covariance stationary. -/
theorem not_covStationary_of_var_ne {μ : Measure Ω} {y : ℕ → Ω → ℝ} {t : ℕ}
    (h : cov μ (y t) (y t) ≠ cov μ (y 0) (y 0)) : ¬ CovStationary μ y := by
  rintro ⟨-, -, h3⟩
  exact h (by simpa using h3 t 0)

/-! ### Linear combinations of i.i.d. fair coins -/

/-- Woodford (2003), p. 501 (the probability space): the i.i.d. fair-coin economy `ν^ℕ` on
`ℕ → ℝ` (`ExpectationsMeasureIID.coin`). -/
noncomputable abbrev Pc : Measure (ℕ → ℝ) := (iidSystem coin).μ

/-- Woodford (2003), p. 501: the coins are bounded by one almost surely. -/
theorem coord_bdd (j : ℕ) : ∀ᵐ ω ∂Pc, |ω j| ≤ 1 := shock_ae_bdd coin coin_bdd j

/-- Woodford (2003), p. 501: each coin is integrable. -/
theorem coord_integrable (j : ℕ) : Integrable (fun ω : ℕ → ℝ => ω j) Pc :=
  Integrable.of_bound (measurable_pi_apply j).aestronglyMeasurable 1
    ((coord_bdd j).mono fun ω h => by rwa [Real.norm_eq_abs])

/-- Woodford (2003), p. 501: products of two coins are integrable. -/
theorem coord_mul_integrable (i j : ℕ) : Integrable (fun ω : ℕ → ℝ => ω i * ω j) Pc :=
  Integrable.of_bound ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable 1
    ((coord_bdd i).mp ((coord_bdd j).mono fun ω h2 h1 => by
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [abs_nonneg (ω i), abs_nonneg (ω j)]))

/-- Woodford (2003), p. 501: each coin has mean zero. -/
theorem integral_coord (j : ℕ) : ∫ ω, ω j ∂Pc = 0 := by
  have := integral_shock_fun coin j (f := id) measurable_id
  simp only [id] at this
  rw [this, coin_mean]

/-- Woodford (2003), p. 501: the coins are orthonormal, `E[εᵢεⱼ] = 1` if `i = j` and `0`
otherwise (independence and mean zero). -/
theorem integral_coord_mul (i j : ℕ) :
    ∫ ω, ω i * ω j ∂Pc = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h
    have := integral_shock_fun coin i (f := fun x => x ^ 2) (measurable_id.pow_const 2)
    rw [← coin_var, ← this]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  · have hind : IndepFun (fun ω : ℕ → ℝ => ω i) (fun ω : ℕ → ℝ => ω j) Pc :=
      (iIndepFun_infinitePi (P := fun _ => (coin : Measure ℝ)) (X := fun _ => id)
        (fun _ => measurable_id)).indepFun h
    have := hind.integral_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, integral_coord, zero_mul]

/-- Woodford (2003), p. 501: a process that is, at each date, a constant plus a finite linear
combination of the coins, `y_t = a_t + ∑_{j < n_t} b_{t,j} ε_j`. -/
noncomputable def lin (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (n : ℕ → ℕ) : ℕ → (ℕ → ℝ) → ℝ :=
  fun t ω => a t + ∑ j ∈ Finset.range (n t), b t j * ω j

/-- Woodford (2003), p. 501: such a process is square-integrable. -/
theorem memLp_lin (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (t : ℕ) :
    MemLp (lin a b n t) 2 Pc := by
  have hc : ∀ j, MemLp (fun ω : ℕ → ℝ => ω j) 2 Pc := fun j =>
    MemLp.of_bound (measurable_pi_apply j).aestronglyMeasurable 1
      ((coord_bdd j).mono fun ω h => by rwa [Real.norm_eq_abs])
  unfold lin
  refine (memLp_const (a t)).add ?_
  have := memLp_finsetSum' (Finset.range (n t)) (fun j _ => (hc j).const_mul (b t j))
  convert this using 1
  funext ω
  simp [Finset.sum_apply]

/-- Woodford (2003), p. 501: the linear-combination part is integrable. -/
theorem integrable_sum (b : ℕ → ℝ) (m : ℕ) :
    Integrable (fun ω : ℕ → ℝ => ∑ j ∈ Finset.range m, b j * ω j) Pc :=
  integrable_finsetSum _ fun j _ => (coord_integrable j).const_mul (b j)

/-- Woodford (2003), p. 501: the mean of y_t is a_t. -/
theorem integral_lin (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (t : ℕ) :
    ∫ ω, lin a b n t ω ∂Pc = a t := by
  unfold lin
  rw [integral_add (integrable_const _) (integrable_sum _ _), integral_const,
    integral_finsetSum _ fun j _ => (coord_integrable j).const_mul (b t j)]
  simp [integral_const_mul, integral_coord]

/-- Woodford (2003), p. 501: `E[(∑ bᵢεᵢ)(∑ cⱼεⱼ)] = ∑_{j < min(m, k)} bⱼcⱼ`. -/
theorem integral_sum_mul_sum (b c : ℕ → ℝ) (m k : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range m, b i * ω i) * (∑ j ∈ Finset.range k, c j * ω j) ∂Pc =
      ∑ j ∈ Finset.range (min m k), b j * c j := by
  have e : (fun ω : ℕ → ℝ => (∑ i ∈ Finset.range m, b i * ω i) *
      (∑ j ∈ Finset.range k, c j * ω j)) =
      fun ω => ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range k, (b i * c j) * (ω i * ω j) := by
    funext ω
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (coord_mul_integrable i j).const_mul _]
  simp_rw [integral_finsetSum _ fun j _ => (coord_mul_integrable _ j).const_mul _,
    integral_const_mul, integral_coord_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
  simp only [Finset.sum_ite_eq, Finset.mem_Ico]
  rw [Finset.range_eq_Ico, ← Finset.sum_filter]
  congr 1
  ext j
  simp [lt_min_iff]

/-- Woodford (2003), p. 501: `Cov(y_t, y_r) = ∑_{j < min(n_t, n_r)} b_{t,j} b_{r,j}`. -/
theorem cov_lin (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (t r : ℕ) :
    cov Pc (lin a b n t) (lin a b n r) =
      ∑ j ∈ Finset.range (min (n t) (n r)), b t j * b r j := by
  unfold cov
  rw [integral_lin, integral_lin]
  simp only [lin, add_sub_cancel_left]
  exact integral_sum_mul_sum (b t) (b r) (n t) (n r)

/-- Woodford (2003), p. 501: covariance stationarity of a linear coin process in terms of its
coefficients. -/
theorem covStationary_lin_iff (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (n : ℕ → ℕ) :
    CovStationary Pc (lin a b n) ↔ (∀ t, a t = a 0) ∧
      ∀ t h, ∑ j ∈ Finset.range (min (n t) (n (t + h))), b t j * b (t + h) j =
        ∑ j ∈ Finset.range (min (n 0) (n h)), b 0 j * b h j := by
  unfold CovStationary
  simp only [integral_lin, cov_lin]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨memLp_lin a b n, h.1, h.2⟩⟩

end Woodford.GainsFromCommitment.TidyR6IntegrationOrder
