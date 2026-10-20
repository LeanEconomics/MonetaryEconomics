/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.CTSimple
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# S-shaped surpluses in continuous time

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.7.2, pp. 167–169,
(5.97)–(5.104).

The surplus process is `s = αv* + u` (5.97), `dv* = (rv* − s)dt + β_s dε` (5.98, written with
the `dt` and `dε` terms separated: the printed `(rv* + β_s dε − s)dt` mixes them, survey E48),
`du = −ηu dt + dε` (5.99, the printed `+ηu dt` is a sign error, E45: the book's own solution
`u_t = ∫ e^{−ητ} dε_{t−τ}` decays). The impulse response to a shock `dε = e₀` at date `0` (an
"MIT shock", perfect foresight afterwards) is computed exactly; the integrals in (5.101) run
over past shocks `dε_{t−τ}` (the printed `dε_{t+τ}` is E46).

## Main results

* `ct_surplus_irf`, `ct_surplus_irf_exists`: the response is
  `s_t = e₀[(η+r)/(η+r−α) e^{−ηt} − (α/(η+r−α) − αβ_s) e^{−(α−r)t}]` (5.100)–(5.101);
  `operator_5_100`, `operator_derivation`: the operator identities (5.100), (5.102)–(5.104) as
  rational-function identities.
* Hansen–Sargent in continuous time for exponential-sum responses: `hs_pv` (the date-`t`
  present value is the response of `(L(D) − L(r))/(r − D)`, `hs_operator`), `hs_innovation`
  (the time-`0` present value is `L(r)`).
* `surplus_L_r` / `ct_pv_irf`: `L(r) = ∫_0^∞ e^{−rt}s_t dt = +β_s` (the printed `L(r) = −β_s` is
  E47; `printed_L_r_wrong`), equal to the jump of `v*` (`ct_vstar_tvc`, `ct_pv_eq_vstar`);
  `ct_fully_repaid`: `β_s = 0` iff the surplus response has zero present value.
* `ct_s_shape`: one sign change when `0 < α − r < η` and the second coefficient is positive.
* `printed_599_wrong`: the printed (5.99) is inconsistent with the book's AR(1) solution.
-/

namespace Cochrane.StickyPriceFiscal.CTSurplus

open Filter Topology MeasureTheory Cochrane.StickyPriceFiscal.CTSimple

/-! ## Exponential-sum responses and Hansen–Sargent -/

/-- Cochrane (2023), §5.7.2, p. 168: the impulse response `Σ_k c_k e^{−d_k t}` of the operator
`L(D) D ε` with `L(D) = Σ_k c_k/(D + d_k)` (each `1/(D + d) Dε = ∫_0^∞ e^{−dτ} dε_{t−τ}` responds
to a unit shock at `0` with `e^{−dt}`). -/
noncomputable def expSum {n : ℕ} (c d : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, c k * Real.exp (-(d k * t))

/-- Cochrane (2023), §5.7.2, p. 168: the lag operator `L(z) = Σ_k c_k/(z + d_k)` as a rational
function. -/
noncomputable def lagOp {n : ℕ} (c d : Fin n → ℝ) (z : ℝ) : ℝ :=
  ∑ k, c k / (z + d k)

/-- Cochrane (2023), p. 168: **Hansen–Sargent in continuous time** (exponential-sum class): if
`r + d_k > 0` for all `k`, the present value at date `t`, `∫_0^∞ e^{−rτ} s_{t+τ} dτ`, of the
response `s = Σ c_k e^{−d_k t}` exists and is the response `Σ (c_k/(r + d_k)) e^{−d_k t}` of the
operator `(L(D) − L(r))/(r − D)` (see `hs_operator`). -/
theorem hs_pv {n : ℕ} (c d : Fin n → ℝ) {r : ℝ} (h : ∀ k, 0 < r + d k) (t : ℝ) :
    IntegrableOn (fun τ => Real.exp (-(r * τ)) * expSum c d (t + τ)) (Set.Ioi 0) ∧
      ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * expSum c d (t + τ) =
        expSum (fun k => c k / (r + d k)) d t := by
  have hterm : ∀ k τ, Real.exp (-(r * τ)) * (c k * Real.exp (-(d k * (t + τ)))) =
      c k * Real.exp (-(d k * t)) * Real.exp (-((r + d k) * τ)) := by
    intro k τ
    rw [mul_left_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hfun : (fun τ => Real.exp (-(r * τ)) * expSum c d (t + τ)) =
      fun τ => ∑ k, c k * Real.exp (-(d k * t)) * Real.exp (-((r + d k) * τ)) := by
    funext τ
    rw [expSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hterm k τ
  have hint : ∀ k ∈ (Finset.univ : Finset (Fin n)), IntegrableOn
      (fun τ => c k * Real.exp (-(d k * t)) * Real.exp (-((r + d k) * τ))) (Set.Ioi 0) :=
    fun k _ => (integrableOn_exp_Ioi (h k)).const_mul _
  rw [hfun]
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint, expSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_exp_Ioi (h k)]
  ring

/-- Cochrane (2023), p. 168: the operator identity behind Hansen–Sargent,
`(L(z) − L(r))/(r − z) = Σ_k (c_k/(r + d_k))/(z + d_k)` (away from the poles, `z ≠ r`). -/
theorem hs_operator {n : ℕ} (c d : Fin n → ℝ) {r z : ℝ} (h : ∀ k, r + d k ≠ 0)
    (hz : ∀ k, z + d k ≠ 0) (hzr : z ≠ r) :
    (lagOp c d z - lagOp c d r) / (r - z) = lagOp (fun k => c k / (r + d k)) d z := by
  have hrz : r - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzr)
  rw [lagOp, lagOp, lagOp, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := h k
  have := hz k
  field_simp
  ring

/-- Cochrane (2023), p. 168: **the present-value innovation is `L(r)`**: the time-`0` present
value of the response `Σ c_k e^{−d_k t}` is `Σ c_k/(r + d_k) = L(r)`. -/
theorem hs_innovation {n : ℕ} (c d : Fin n → ℝ) {r : ℝ} (h : ∀ k, 0 < r + d k) :
    ∫ τ in Set.Ioi 0, Real.exp (-(r * τ)) * expSum c d τ = lagOp c d r := by
  have := (hs_pv c d h 0).2
  simp only [zero_add] at this
  rw [this, expSum, lagOp]
  simp

/-! ## The surplus response (5.100)–(5.101) -/

/-- Cochrane (2023), (5.101), p. 168: the response of the surplus to a unit shock at date `0`,
`(η+r)/(η+r−α) e^{−ηt} − (α/(η+r−α) − αβ_s) e^{−(α−r)t}`. -/
noncomputable def surplusIRF (r α η βs t : ℝ) : ℝ :=
  (η + r) / (η + r - α) * Real.exp (-(η * t)) -
    (α / (η + r - α) - α * βs) * Real.exp (-((α - r) * t))

/-- Cochrane (2023), (5.98) and (5.101): the response of the state variable `v*` to a unit shock,
`β_s e^{−(α−r)t} + (e^{−ηt} − e^{−(α−r)t})/(η + r − α)`. -/
noncomputable def vstarIRF (r α η βs t : ℝ) : ℝ :=
  βs * Real.exp (-((α - r) * t)) +
    (Real.exp (-(η * t)) - Real.exp (-((α - r) * t))) / (η + r - α)

/-- Cochrane (2023), (5.101), p. 168: the surplus response is the two-term exponential sum with
coefficients `((η+r)/(η+r−α), −(α/(η+r−α) − αβ_s))` and rates `(η, α − r)`. -/
theorem surplusIRF_eq_expSum (r α η βs t : ℝ) :
    surplusIRF r α η βs t =
      expSum ![(η + r) / (η + r - α), -(α / (η + r - α) - α * βs)] ![η, α - r] t := by
  simp [surplusIRF, expSum, Fin.sum_univ_two]
  ring

/-- Cochrane (2023), (5.97), p. 167: along the response, `s = αv* + u` with `u = e^{−ηt}`. -/
theorem surplusIRF_eq (r α η βs t : ℝ) (h : η + r - α ≠ 0) :
    surplusIRF r α η βs t = α * vstarIRF r α η βs t + Real.exp (-(η * t)) := by
  simp only [surplusIRF, vstarIRF]
  field_simp
  ring

/-- Cochrane (2023), (5.98), p. 167: the `v*` response solves `dv*/dt = rv* − s` with
`s = αv* + e^{−ηt}`. -/
theorem vstarIRF_hasDerivAt (r α η βs t : ℝ) (h : η + r - α ≠ 0) :
    HasDerivAt (vstarIRF r α η βs)
      (r * vstarIRF r α η βs t - (α * vstarIRF r α η βs t + Real.exp (-(η * t)))) t := by
  have hd := ((hasDerivAt_expNeg (α - r) t).const_mul βs).add
    (((hasDerivAt_expNeg η t).sub (hasDerivAt_expNeg (α - r) t)).div_const (η + r - α))
  refine hd.congr_deriv ?_
  simp only [vstarIRF]
  field_simp
  ring

/-- Cochrane (2023), (5.97)–(5.99) after an MIT shock `dε = e₀` at date `0`: `u` and `v*` are
continuous on `[0, ∞)`, `u` jumps to `e₀` and `v*` to `β_s e₀` at `0` (the `dε` terms), then
`du/dt = −ηu` (corrected (5.99), E45) and `dv*/dt = rv* − s` (5.98 with the `dt` part only,
E48) on `(0, ∞)`, with `s = αv* + u` (5.97). -/
def IsSurplusResponse (r α η βs e0 : ℝ) (u vstar s : ℝ → ℝ) : Prop :=
  ContinuousOn u (Set.Ici 0) ∧ ContinuousOn vstar (Set.Ici 0) ∧ u 0 = e0 ∧
    vstar 0 = βs * e0 ∧ (∀ t, 0 ≤ t → s t = α * vstar t + u t) ∧
      ∀ t, 0 < t → HasDerivAt u (-η * u t) t ∧ HasDerivAt vstar (r * vstar t - s t) t

/-- Cochrane (2023), (5.100)–(5.101), p. 168: **the surplus impulse response.** If
`η + r − α ≠ 0`, every response to the shock `e₀` is `u_t = e₀e^{−ηt}`,
`v*_t = e₀ v*IRF(t)` and `s_t = e₀[(η+r)/(η+r−α) e^{−ηt} − (α/(η+r−α) − αβ_s) e^{−(α−r)t}]`. -/
theorem ct_surplus_irf {r α η βs e0 : ℝ} {u vstar s : ℝ → ℝ} (h : η + r - α ≠ 0)
    (hR : IsSurplusResponse r α η βs e0 u vstar s) (t : ℝ) (ht : 0 ≤ t) :
    u t = e0 * Real.exp (-(η * t)) ∧ vstar t = e0 * vstarIRF r α η βs t ∧
      s t = e0 * surplusIRF r α η βs t := by
  obtain ⟨huc, hvc, hu0, hv0, hs, hd⟩ := hR
  have hu : ∀ τ, 0 ≤ τ → u τ = e0 * Real.exp (-(η * τ)) := fun τ hτ => by
    rw [decay_unique huc (fun x hx => (hd x hx).1) τ hτ, hu0]
    ring
  have hw := decay_unique (b := α - r) (w := fun x => vstar x - e0 * vstarIRF r α η βs x)
    (hvc.sub (continuous_iff_continuousAt.2 fun x =>
      ((vstarIRF_hasDerivAt r α η βs x h).const_mul e0).continuousAt).continuousOn)
    (fun x hx => ((hd x hx).2.sub ((vstarIRF_hasDerivAt r α η βs x h).const_mul e0)).congr_deriv
      (by rw [hs x hx.le, hu x hx.le]; ring)) t ht
  have hV0 : vstarIRF r α η βs 0 = βs := by simp [vstarIRF]
  simp only [hv0, hV0] at hw
  have hvt : vstar t = e0 * vstarIRF r α η βs t := by linarith
  refine ⟨hu t ht, hvt, ?_⟩
  rw [hs t ht, hvt, hu t ht, surplusIRF_eq r α η βs t h]
  ring

/-- Cochrane (2023), (5.97)–(5.101): **the response exists**: `u = e₀e^{−ηt}`,
`v* = e₀ v*IRF`, `s = αv* + u` satisfy (5.97)–(5.99) after the shock. -/
theorem ct_surplus_irf_exists (r α η βs e0 : ℝ) (h : η + r - α ≠ 0) :
    IsSurplusResponse r α η βs e0 (fun t => e0 * Real.exp (-(η * t)))
      (fun t => e0 * vstarIRF r α η βs t)
      (fun t => α * (e0 * vstarIRF r α η βs t) + e0 * Real.exp (-(η * t))) := by
  have hcv : Continuous fun t => e0 * vstarIRF r α η βs t :=
    continuous_iff_continuousAt.2 fun x =>
      ((vstarIRF_hasDerivAt r α η βs x h).const_mul e0).continuousAt
  refine ⟨by fun_prop, hcv.continuousOn, by simp, by simp [vstarIRF]; ring,
    fun _ _ => rfl, fun t _ => ⟨((hasDerivAt_expNeg η t).const_mul e0).congr_deriv (by ring),
      ((vstarIRF_hasDerivAt r α η βs t h).const_mul e0).congr_deriv (by ring)⟩⟩

/-- Cochrane (2023), p. 168: at the shock date the surplus response is `1 + αβ_s` (per unit
shock). -/
theorem surplusIRF_zero {r α η βs : ℝ} (h : η + r - α ≠ 0) :
    surplusIRF r α η βs 0 = 1 + α * βs := by
  simp only [surplusIRF, mul_zero, neg_zero, Real.exp_zero, mul_one]
  field_simp
  ring

/-! ## Operator identities (5.100), (5.102)–(5.104) -/

/-- Cochrane (2023), (5.102)–(5.104) and p. 169: **the operator derivation**: with
`u = Dε/(η + D)` and `v* = −(−β_s Dε + u)/(D + α − r)`, `s = αv* + u` has transfer function
`(1 − α/(D + α − r))/(η + D) + αβ_s/(D + α − r) = (D − r)/((D + α − r)(D + η)) + αβ_s/(D + α − r)`
(as rational functions of `z`, away from the poles). -/
theorem operator_derivation {r α η βs z : ℝ} (h1 : z + (α - r) ≠ 0) (h2 : η + z ≠ 0) :
    α * (-(1 / (z + (α - r))) * (-βs + 1 / (η + z))) + 1 / (η + z) =
      (z - r) / (z + (α - r)) * (1 / (z + η)) + α * βs / (z + (α - r)) := by
  have h2' : z + η ≠ 0 := by rwa [add_comm]
  field_simp
  ring

/-- Cochrane (2023), (5.100), p. 168: **the partial fractions**:
`(z − r)/((z + α − r)(z + η)) + αβ_s/(z + α − r)
  = (η+r)/(η+r−α) · 1/(η + z) − (α/(η+r−α) − αβ_s) · 1/((α − r) + z)`. -/
theorem operator_5_100 {r α η βs z : ℝ} (h1 : z + (α - r) ≠ 0) (h2 : η + z ≠ 0)
    (h3 : η + r - α ≠ 0) :
    (z - r) / (z + (α - r)) * (1 / (z + η)) + α * βs / (z + (α - r)) =
      (η + r) / (η + r - α) * (1 / (η + z)) -
        (α / (η + r - α) - α * βs) * (1 / ((α - r) + z)) := by
  have h2' : z + η ≠ 0 := by rwa [add_comm]
  have h1' : (α - r) + z ≠ 0 := by rwa [add_comm]
  field_simp
  ring

/-- Cochrane (2023), p. 168: the lag operator of the surplus response,
`L(z) = (η+r)/(η+r−α)/(z + η) − (α/(η+r−α) − αβ_s)/(z + α − r)`. -/
noncomputable def surplusL (r α η βs z : ℝ) : ℝ :=
  lagOp ![(η + r) / (η + r - α), -(α / (η + r - α) - α * βs)] ![η, α - r] z

/-- Cochrane (2023), p. 168 (survey E47): **`L(r) = +β_s`** (for `α ≠ 0`, `η + r ≠ 0`,
`η + r − α ≠ 0`). The book prints `L(r) = −β_s`; with its second sign slip
(`−Δ(1/P)/(1/P) = −L(r)dε`) the price-level line `Δ(1/P)/(1/P) = β_s dε` is nevertheless
right. -/
theorem surplus_L_r {r α η βs : ℝ} (hα : α ≠ 0) (h1 : η + r ≠ 0) (h3 : η + r - α ≠ 0) :
    surplusL r α η βs r = βs := by
  simp only [surplusL, lagOp, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : r + (α - r) = α := by ring
  rw [this, show r + η = η + r by ring]
  field_simp
  ring

/-- Cochrane (2023), p. 168 (E47): the printed `L(r) = −β_s` holds only when `β_s = 0`. -/
theorem printed_L_r_wrong {r α η βs : ℝ} (hα : α ≠ 0) (h1 : η + r ≠ 0) (h3 : η + r - α ≠ 0) :
    surplusL r α η βs r = -βs ↔ βs = 0 := by
  rw [surplus_L_r hα h1 h3]
  constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 168: **the present value of the surplus response is `β_s`** (per unit
shock): for `α > 0` and `r + η > 0`,
`∫_0^∞ e^{−rt} s_t dt = L(r) = β_s` (integrable). -/
theorem ct_pv_irf {r α η βs : ℝ} (hα : 0 < α) (hη : 0 < r + η) (h3 : η + r - α ≠ 0) :
    IntegrableOn (fun t => Real.exp (-(r * t)) * surplusIRF r α η βs t) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * surplusIRF r α η βs t = βs := by
  have hk : ∀ k, 0 < r + (![η, α - r] : Fin 2 → ℝ) k := by
    intro k
    fin_cases k
    · simpa using hη
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith
  have hfun : (fun t => Real.exp (-(r * t)) * surplusIRF r α η βs t) = fun t =>
      Real.exp (-(r * t)) *
        expSum ![(η + r) / (η + r - α), -(α / (η + r - α) - α * βs)] ![η, α - r] (0 + t) := by
    funext t
    rw [zero_add, surplusIRF_eq_expSum]
  rw [hfun]
  refine ⟨(hs_pv _ _ hk 0).1, ?_⟩
  simp only [zero_add]
  rw [hs_innovation _ _ hk]
  exact surplus_L_r hα.ne' (by linarith) h3

/-- Cochrane (2023), (5.98), p. 167: the `v*` response satisfies the transversality condition
`e^{−rT}v*_T → 0` (for `α > 0`, `r + η > 0`). -/
theorem ct_vstar_tvc {r α η βs : ℝ} (hα : 0 < α) (hη : 0 < r + η) :
    Tendsto (fun T => Real.exp (-(r * T)) * vstarIRF r α η βs T) atTop (𝓝 0) := by
  have e1 : Tendsto (fun T => Real.exp (-(α * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hα)
  have e2 : Tendsto (fun T => Real.exp (-((r + η) * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hη)
  have := (e1.const_mul βs).add ((e2.sub e1).div_const (η + r - α))
  simp only [mul_zero, sub_self, zero_div, add_zero] at this
  refine this.congr fun T => ?_
  have a1 : Real.exp (-(α * T)) = Real.exp (-(r * T)) * Real.exp (-((α - r) * T)) := by
    rw [← Real.exp_add]; ring_nf
  have a2 : Real.exp (-((r + η) * T)) = Real.exp (-(r * T)) * Real.exp (-(η * T)) := by
    rw [← Real.exp_add]; ring_nf
  rw [a1, a2, vstarIRF]
  ring

/-- Cochrane (2023), pp. 167–168: **the jump of `v*` is the present value of surpluses**: along
the response to `e₀`, the transversality condition holds and
`v*_0 = β_s e₀ = ∫_0^∞ e^{−rt} s_t dt`. In the flexible-price model `v* = B/P` with `B`
predetermined, so `Δ(1/P)/(1/P) = +L(r) dε = β_s dε` (the book's line, after its two
compensating sign slips, E47). -/
theorem ct_pv_eq_vstar {r α η βs e0 : ℝ} {u vstar s : ℝ → ℝ} (hα : 0 < α) (hη : 0 < r + η)
    (h3 : η + r - α ≠ 0) (hR : IsSurplusResponse r α η βs e0 u vstar s) :
    Tendsto (fun T => Real.exp (-(r * T)) * vstar T) atTop (𝓝 0) ∧
      vstar 0 = ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * s t ∧ vstar 0 = βs * e0 := by
  have hirf := ct_surplus_irf h3 hR
  have hpv := ct_pv_irf (βs := βs) hα hη h3
  have htvc : Tendsto (fun T => Real.exp (-(r * T)) * vstar T) atTop (𝓝 0) := by
    have := (ct_vstar_tvc (βs := βs) hα hη).const_mul e0
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with T hT
    rw [(hirf T hT).2.1]
    ring
  refine ⟨htvc, ?_, hR.2.2.2.1⟩
  have heq : ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * s t =
      e0 * ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * surplusIRF r α η βs t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : (0 : ℝ) < t) => ?_
    simp only [(hirf t ht.le).2.2]
    ring
  rw [heq, hpv.2, hR.2.2.2.1]
  ring

/-- Cochrane (2023), p. 168: **"with `β_s = 0`, deficits are fully repaid"**: the present value
of the surplus response is zero iff `β_s = 0`. -/
theorem ct_fully_repaid {r α η βs : ℝ} (hα : 0 < α) (hη : 0 < r + η) (h3 : η + r - α ≠ 0) :
    ∫ t in Set.Ioi 0, Real.exp (-(r * t)) * surplusIRF r α η βs t = 0 ↔ βs = 0 := by
  rw [(ct_pv_irf hα hη h3).2]

/-! ## The s-shape (p. 168) -/

/-- Cochrane (2023), p. 168: **the s-shaped response has a single sign change.** If
`α > 0` and `α − r < η` (the book's `η ≫ α − r > 0`: the first term decays faster) and the
second coefficient `B = α/(η+r−α) − αβ_s` is positive, then with `A = (η+r)/(η+r−α) > 0` and
`T = log(A/B)/(η − (α − r))`, the surplus response is positive exactly before `T` and negative
exactly after `T`. -/
theorem ct_s_shape {r α η βs : ℝ} (hα : 0 < α) (hηa : α - r < η)
    (hB : 0 < α / (η + r - α) - α * βs) (t : ℝ) :
    (0 < surplusIRF r α η βs t ↔
        t < Real.log ((η + r) / (η + r - α) / (α / (η + r - α) - α * βs)) / (η - (α - r))) ∧
      (surplusIRF r α η βs t < 0 ↔
        Real.log ((η + r) / (η + r - α) / (α / (η + r - α) - α * βs)) / (η - (α - r)) < t) := by
  set A := (η + r) / (η + r - α) with hAdef
  set B := α / (η + r - α) - α * βs
  have hd : 0 < η + r - α := by linarith
  have hA : 0 < A := by rw [hAdef]; exact div_pos (by linarith) hd
  have hk : 0 < η - (α - r) := by linarith
  have hpA := mul_pos hA (Real.exp_pos (-(η * t)))
  have hpB := mul_pos hB (Real.exp_pos (-((α - r) * t)))
  have hlog : Real.log (A * Real.exp (-(η * t))) - Real.log (B * Real.exp (-((α - r) * t))) =
      Real.log (A / B) - (η - (α - r)) * t := by
    rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_mul hB.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_exp, Real.log_div hA.ne' hB.ne']
    ring
  have hs : surplusIRF r α η βs t = A * Real.exp (-(η * t)) - B * Real.exp (-((α - r) * t)) :=
    rfl
  rw [hs, lt_div_iff₀ hk, div_lt_iff₀ hk, sub_pos, sub_neg]
  constructor
  · rw [← Real.log_lt_log_iff hpB hpA]
    constructor <;> intro h <;> linarith
  · rw [← Real.log_lt_log_iff hpA hpB]
    constructor <;> intro h <;> linarith

/-- Cochrane (2023), p. 168: the s-shaped response dies off, `s_t → 0`, for `α > r`, `η > 0`. -/
theorem surplusIRF_tendsto {r α η βs : ℝ} (ha : 0 < α - r) (hη : 0 < η) :
    Tendsto (surplusIRF r α η βs) atTop (𝓝 0) := by
  have e1 : Tendsto (fun T => Real.exp (-(η * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hη)
  have e2 : Tendsto (fun T => Real.exp (-((α - r) * T))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop ha)
  have := (e1.const_mul ((η + r) / (η + r - α))).sub (e2.const_mul (α / (η + r - α) - α * βs))
  simp only [mul_zero, sub_zero] at this
  exact this

/-- Cochrane (2023), (5.99), p. 167 (survey E45): the printed `du = ηu dt + dε` is inconsistent
with the book's own solution `u_t = ∫_0^∞ e^{−ητ} dε_{t−τ}`: for `η ≠ 0` and a nonzero shock,
`e₀e^{−ηt}` does not satisfy `du/dt = ηu` at any date. -/
theorem printed_599_wrong {η e0 : ℝ} (hη : η ≠ 0) (he : e0 ≠ 0) (t : ℝ) :
    ¬ HasDerivAt (fun x => e0 * Real.exp (-(η * x))) (η * (e0 * Real.exp (-(η * t)))) t := by
  intro h
  have h2 := (hasDerivAt_expNeg η t).const_mul e0
  have := h.unique h2
  have hp := Real.exp_pos (-(η * t))
  have : 2 * η * e0 * Real.exp (-(η * t)) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · norm_num at h4
      · exact hη h4
    · exact he h3
  · exact hp.ne' h1

end Cochrane.StickyPriceFiscal.CTSurplus
