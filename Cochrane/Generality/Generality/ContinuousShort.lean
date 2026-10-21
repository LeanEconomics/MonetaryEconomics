/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Continuous time with short-term debt

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 3, §3.6 (box p. 71) and §3.6.1,
pp. 71–74, and Online Appendix A1.4, pp. 564–565.

All paths are deterministic (perfect foresight) functions `ℝ → ℝ`. From a date `t` on, the real
value of government debt `V = B/P` obeys the flow identity (3.30) `V' = (i − π)V − s` with
`π = P'/P`, which we derive from the nominal flow (3.29) `B' = iB − Ps`. Writing `r = i − π` and
`D(t, τ) = exp(−∫_t^τ r)` we prove, for a real rate continuous on `[t, ∞)` and an absolutely
integrable discounted surplus stream `D(t, ·)s`:

* the finite-horizon identity `D(t,T)V(T) = V(t) − ∫_t^T D(t,τ)s(τ)dτ`;
* the valuation equation (3.31) `V(t) = ∫_t^∞ D(t,τ)s(τ)dτ` holds **iff** the transversality
  condition `D(t,T)V(T) → 0` holds;
* the present-value path solves the flow identity and the transversality condition (existence),
  every solution of the flow identity is the present value plus a bubble `c/D(t,·)`, and the
  bubble vanishes iff the transversality condition holds (uniqueness);
* the price level is determined, `P(t) = B(t)/∫D s`, there is no positive price level when the
  present value of surpluses is not positive, and news about surpluses moves the price level by
  the ratio of present values (jumps);
* the discount factor `Λ` with `Λ'/Λ = −r` gives `Λ(τ)/Λ(t) = D(t,τ)`; the A1 (1.26) identities;
  the "work up or down" chains of A1.4 for `Λ` and for the ex-post return `W` (3.32)–(3.33),
  including the closed form `W(t)/W(0) = exp(∫_0^t i)P(0)/P(t)`;
* the constant-rate special case of p. 74 and the constant-surplus value `s/r`.

Price levels may jump at the initial date `t`: all paths are only required to be continuous on
`[t, ∞)` and differentiable on `(t, ∞)`.
-/

namespace Cochrane.Generality.ContinuousShort

open MeasureTheory Filter Topology

/-! ## Cumulated rates and the discount function -/

/-- Cochrane (2023), §3.6.1, p. 74: the cumulated rate `∫_t^τ r(u) du`. -/
noncomputable def cumRate (r : ℝ → ℝ) (t τ : ℝ) : ℝ := ∫ u in t..τ, r u

/-- Cochrane (2023), §3.6.1, p. 74: the discount function `D(t, τ) = exp(−∫_t^τ r)`, i.e. the
risk-neutral `Λ_τ/Λ_t` with instantaneous real rate `r`. -/
noncomputable def disc (r : ℝ → ℝ) (t τ : ℝ) : ℝ := Real.exp (-cumRate r t τ)

/-- Cochrane (2023), eq. (3.30), p. 73: the real value `V` obeys the flow identity
`V' = rV − s` on `[t, ∞)`: continuous on `[t, ∞)` (it may jump at `t` from earlier values) and
differentiable on `(t, ∞)`. -/
def FlowOn (r s V : ℝ → ℝ) (t : ℝ) : Prop :=
  ContinuousOn V (Set.Ici t) ∧ ∀ τ, t < τ → HasDerivAt V (r τ * V τ - s τ) τ

/-- Cochrane (2023), §3.6.1 and A1.4, p. 564: the transversality condition
`lim_{T→∞} D(t,T)V(T) = 0`. -/
def TVC (r V : ℝ → ℝ) (t : ℝ) : Prop :=
  Tendsto (fun T => disc r t T * V T) atTop (𝓝 0)

/-- Cochrane (2023), eq. (3.31), p. 73: the present value `∫_t^∞ D(t,τ)s(τ)dτ` of surpluses. -/
noncomputable def pv (r s : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in Set.Ioi t, disc r t τ * s τ

/-- Cochrane (2023), eq. (3.31), p. 73: the discounted surplus stream is (absolutely) integrable on
`(t, ∞)`, so that the present value is a genuine improper integral. -/
def PVIntegrable (r s : ℝ → ℝ) (t : ℝ) : Prop :=
  IntegrableOn (fun τ => disc r t τ * s τ) (Set.Ioi t)

/-- Cochrane (2023), §3.6.1: a function continuous on `[t, ∞)` is interval integrable on every
`[a, b]` with `t ≤ a`. -/
lemma intervalIntegrable_of_ici {f : ℝ → ℝ} {t a b : ℝ} (hf : ContinuousOn f (Set.Ici t))
    (ha : t ≤ a) (hb : t ≤ b) : IntervalIntegrable f volume a b := by
  apply ContinuousOn.intervalIntegrable
  refine hf.mono fun x hx => ?_
  rcases Set.mem_uIcc.1 hx with h | h
  · exact le_trans ha h.1
  · exact le_trans hb h.1

/-- Cochrane (2023), §3.6.1: the cumulated rate is differentiable on `(t, ∞)` with derivative
`r`. -/
lemma hasDerivAt_cumRate {r : ℝ → ℝ} {t τ : ℝ} (hr : ContinuousOn r (Set.Ici t)) (hτ : t < τ) :
    HasDerivAt (cumRate r t) (r τ) τ := by
  have hopen : ContinuousOn r (Set.Ioi t) := hr.mono Set.Ioi_subset_Ici_self
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_of_ici hr le_rfl hτ.le)
    (hopen.stronglyMeasurableAtFilter isOpen_Ioi τ hτ)
    (hr.continuousAt (Ici_mem_nhds hτ))

/-- Cochrane (2023), §3.6.1: the cumulated rate is continuous on `[t, ∞)`. -/
lemma continuousOn_cumRate {r : ℝ → ℝ} {t : ℝ} (hr : ContinuousOn r (Set.Ici t)) :
    ContinuousOn (cumRate r t) (Set.Ici t) := by
  intro x hx
  have hx' : t ≤ x := hx
  have h1 : ContinuousOn (cumRate r t) (Set.uIcc t (x + 1)) :=
    intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_of_ici hr le_rfl (by linarith)) Set.left_mem_uIcc
  have hmem : x ∈ Set.uIcc t (x + 1) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨hx', by linarith⟩
  refine (h1 x hmem).mono_of_mem_nhdsWithin ?_
  rw [Set.uIcc_of_le (by linarith)]
  have : Set.Ici t ∩ Set.Iic (x + 1) ∈ 𝓝[Set.Ici t] x :=
    inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  simpa [Set.Ici_inter_Iic] using this

/-- Cochrane (2023), §3.6.1: `∫_t^t r = 0`. -/
@[simp] lemma cumRate_self (r : ℝ → ℝ) (t : ℝ) : cumRate r t t = 0 := by
  simp [cumRate]

/-- Cochrane (2023), §3.6.1: cumulated rates add over adjacent intervals. -/
lemma cumRate_add {r : ℝ → ℝ} {t a b : ℝ} (hr : ContinuousOn r (Set.Ici t)) (ha : t ≤ a)
    (hab : a ≤ b) : cumRate r t a + cumRate r a b = cumRate r t b :=
  intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_of_ici hr le_rfl ha)
    (intervalIntegrable_of_ici hr ha (ha.trans hab))

/-- Cochrane (2023), p. 74: with a constant rate `c`, `∫_t^τ c = c(τ − t)`. -/
lemma cumRate_const (c t τ : ℝ) : cumRate (fun _ => c) t τ = c * (τ - t) := by
  simp [cumRate, mul_comm]

/-- Cochrane (2023), §3.6.1: the discount function is positive. -/
lemma disc_pos (r : ℝ → ℝ) (t τ : ℝ) : 0 < disc r t τ := Real.exp_pos _

/-- Cochrane (2023), §3.6.1: `D(t, t) = 1`. -/
@[simp] lemma disc_self (r : ℝ → ℝ) (t : ℝ) : disc r t t = 1 := by
  simp [disc]

/-- Cochrane (2023), §3.6.1: the discount function is multiplicative,
`D(t,a)D(a,b) = D(t,b)` (`Λ_a/Λ_t · Λ_b/Λ_a = Λ_b/Λ_t`). -/
lemma disc_mul {r : ℝ → ℝ} {t a b : ℝ} (hr : ContinuousOn r (Set.Ici t)) (ha : t ≤ a)
    (hab : a ≤ b) : disc r t a * disc r a b = disc r t b := by
  rw [disc, disc, disc, ← Real.exp_add, ← cumRate_add hr ha hab, neg_add]

/-- Cochrane (2023), §3.6.1: `D(a, b) = D(t, b)/D(t, a)` for `t ≤ a ≤ b`. -/
lemma disc_eq_div {r : ℝ → ℝ} {t a b : ℝ} (hr : ContinuousOn r (Set.Ici t)) (ha : t ≤ a)
    (hab : a ≤ b) : disc r a b = disc r t b / disc r t a := by
  rw [← disc_mul hr ha hab]
  field_simp [(disc_pos r t a).ne']

/-- Cochrane (2023), p. 74: with a constant real rate, `Λ_τ/Λ_t = e^{−r(τ−t)}`. -/
lemma disc_const (c t τ : ℝ) : disc (fun _ => c) t τ = Real.exp (-(c * (τ - t))) := by
  rw [disc, cumRate_const]

/-- Cochrane (2023), §3.6.1: `d/dτ D(t,τ) = −r(τ)D(t,τ)` on `(t, ∞)`. -/
lemma hasDerivAt_disc {r : ℝ → ℝ} {t τ : ℝ} (hr : ContinuousOn r (Set.Ici t)) (hτ : t < τ) :
    HasDerivAt (disc r t) (-(r τ) * disc r t τ) τ := by
  have h := ((hasDerivAt_cumRate hr hτ).neg).exp
  have e : (fun x => Real.exp ((-cumRate r t) x)) = disc r t := rfl
  rw [e] at h
  convert h using 1
  simp only [disc, Pi.neg_apply]
  ring

/-- Cochrane (2023), §3.6.1: the discount function is continuous on `[t, ∞)`. -/
lemma continuousOn_disc {r : ℝ → ℝ} {t : ℝ} (hr : ContinuousOn r (Set.Ici t)) :
    ContinuousOn (disc r t) (Set.Ici t) :=
  Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hr).neg

/-- Cochrane (2023), §3.6.1: a function continuous on `[t, ∞)` with zero derivative on `(t, ∞)`
is constant on `[t, ∞)` (via the fundamental theorem of calculus). -/
lemma eq_of_hasDerivAt_zero {f : ℝ → ℝ} {t : ℝ} (hc : ContinuousOn f (Set.Ici t))
    (hd : ∀ τ, t < τ → HasDerivAt f 0 τ) {τ : ℝ} (hτ : t ≤ τ) : f τ = f t := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ
    (hc.mono Set.Icc_subset_Ici_self) (fun x hx => hd x hx.1) intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at h
  linarith

/-- Cochrane (2023), §3.6.1–§3.6.3, pp. 74–78: translating dates or maturities,
`∫_0^∞ f(x + j)dj = ∫_x^∞ f(u)du`. -/
theorem integral_Ioi_shift (f : ℝ → ℝ) (x : ℝ) :
    ∫ j in Set.Ioi 0, f (x + j) = ∫ u in Set.Ioi x, f u := by
  have hE : MeasurableEmbedding (fun j : ℝ => x + j) :=
    (Homeomorph.addLeft x).isClosedEmbedding.measurableEmbedding
  have h := hE.setIntegral_map (μ := volume) f (Set.Ioi x)
  rw [Measure.IsAddLeftInvariant.map_add_left_eq_self] at h
  rw [h]
  congr 1
  ext j
  simp

/-! ## The valuation equation (3.31) and the transversality condition -/

variable {r s V : ℝ → ℝ} {t : ℝ}

/-- Cochrane (2023), A1.4, p. 564: along the flow identity (3.30),
`d/dτ [D(t,τ)V(τ)] = −D(t,τ)s(τ)` ("`d(Λ_t B_t/P_t) = −s_tΛ_t dt`"). -/
theorem hasDerivAt_disc_mul (hr : ContinuousOn r (Set.Ici t)) (hV : FlowOn r s V t) {τ : ℝ}
    (hτ : t < τ) : HasDerivAt (fun x => disc r t x * V x) (-(disc r t τ * s τ)) τ := by
  have h := (hasDerivAt_disc hr hτ).mul (hV.2 τ hτ)
  convert h using 1
  ring

/-- Cochrane (2023), A1.4, p. 564: the finite-horizon present-value identity
`D(t,T)V(T) = V(t) − ∫_t^T D(t,τ)s(τ)dτ`, obtained by integrating (3.30) on `[t, T]`. -/
theorem pv_finite (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) {T : ℝ} (hT : t ≤ T) :
    disc r t T * V T = V t - ∫ τ in t..T, disc r t τ * s τ := by
  have hc : ContinuousOn (fun x => disc r t x * V x) (Set.Icc t T) :=
    ((continuousOn_disc hr).mul hV.1).mono Set.Icc_subset_Ici_self
  have hint : IntervalIntegrable (fun x => -(disc r t x * s x)) volume t T :=
    intervalIntegrable_of_ici (((continuousOn_disc hr).mul hs).neg) le_rfl hT
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hc
    (fun x hx => hasDerivAt_disc_mul hr hV hx.1) hint
  rw [intervalIntegral.integral_neg, disc_self, one_mul] at h
  linarith

/-- Cochrane (2023), eq. (3.31) and A1.4: along any solution of the flow identity, the
discounted terminal value converges, `D(t,T)V(T) → V(t) − ∫_t^∞ D(t,τ)s(τ)dτ`. -/
theorem tendsto_disc_mul (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) :
    Tendsto (fun T => disc r t T * V T) atTop (𝓝 (V t - pv r s t)) := by
  have h := (intervalIntegral_tendsto_integral_Ioi t hI tendsto_id).const_sub (V t)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop t] with T hT
  rw [pv_finite hr hs hV hT]
  rfl

/-- Cochrane (2023), eq. (3.31), p. 73, and A1.4, pp. 564–565 ("work up or down"): along the flow
identity (3.30), the valuation equation `V(t) = ∫_t^∞ D(t,τ)s(τ)dτ` holds **iff** the
transversality condition `D(t,T)V(T) → 0` holds. -/
theorem valuation_iff_tvc (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) : V t = pv r s t ↔ TVC r V t := by
  have h := tendsto_disc_mul hr hs hV hI
  constructor
  · intro he
    rw [he, sub_self] at h
    exact h
  · intro htvc
    have := tendsto_nhds_unique h htvc
    linarith

/-- Cochrane (2023), §3.6.1: absolute integrability of the discounted surpluses from `t` implies
it from every later date `a ≥ t`. -/
theorem pvIntegrable_of_le (hr : ContinuousOn r (Set.Ici t)) (hI : PVIntegrable r s t) {a : ℝ}
    (ha : t ≤ a) : PVIntegrable r s a := by
  have h : IntegrableOn (fun τ => disc r t τ * s τ / disc r t a) (Set.Ioi a) :=
    (hI.mono_set (Set.Ioi_subset_Ioi ha)).div_const _
  refine h.congr_fun (fun τ hτ => ?_) measurableSet_Ioi
  rw [disc_eq_div hr ha (le_of_lt hτ)]
  ring

/-- Cochrane (2023), §3.6.1: the present value at a later date `a ≥ t`,
`∫_a^∞ D(a,τ)s = (∫_t^∞ D(t,τ)s − ∫_t^a D(t,τ)s)/D(t,a)`. -/
theorem pv_eq_of_le (hr : ContinuousOn r (Set.Ici t)) (hI : PVIntegrable r s t) {a : ℝ}
    (ha : t ≤ a) : pv r s a = (pv r s t - ∫ τ in t..a, disc r t τ * s τ) / disc r t a := by
  have h1 : pv r s a = (∫ τ in Set.Ioi a, disc r t τ * s τ) / disc r t a := by
    rw [pv, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    rw [disc_eq_div hr ha (le_of_lt hτ)]
    ring
  rw [h1, ← intervalIntegral.integral_Ioi_sub_Ioi hI ha, pv]
  ring

/-- Cochrane (2023), §3.6.1: the closed form of the present-value path,
`pv(τ) = exp(∫_t^τ r)·(pv(t) − ∫_t^τ D(t,u)s(u)du)` on `[t, ∞)`. -/
theorem pv_eqOn_closed (hr : ContinuousOn r (Set.Ici t)) (hI : PVIntegrable r s t) :
    Set.EqOn (pv r s) (fun τ => Real.exp (cumRate r t τ) *
      (pv r s t - cumRate (fun u => disc r t u * s u) t τ)) (Set.Ici t) := by
  intro τ hτ
  rw [pv_eq_of_le hr hI hτ, disc, Real.exp_neg, div_inv_eq_mul, mul_comm]
  rfl

/-- Cochrane (2023), eq. (3.31), existence: the present-value path `τ ↦ ∫_τ^∞ D(τ,u)s(u)du`
solves the flow identity (3.30) on `[t, ∞)`. -/
theorem flowOn_pv (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable r s t) : FlowOn r s (pv r s) t := by
  have hDs : ContinuousOn (fun u => disc r t u * s u) (Set.Ici t) := (continuousOn_disc hr).mul hs
  have hE := pv_eqOn_closed hr hI
  refine ⟨?_, fun τ hτ => ?_⟩
  · refine ContinuousOn.congr ?_ hE
    exact (Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hr)).mul
      (continuousOn_const.sub (continuousOn_cumRate hDs))
  · have h1 : HasDerivAt (fun x => Real.exp (cumRate r t x)) (Real.exp (cumRate r t τ) * r τ) τ :=
      (hasDerivAt_cumRate hr hτ).exp
    have h2 := h1.mul ((hasDerivAt_cumRate hDs hτ).const_sub (pv r s t))
    have hev : pv r s =ᶠ[𝓝 τ] (fun τ => Real.exp (cumRate r t τ) *
        (pv r s t - cumRate (fun u => disc r t u * s u) t τ)) := by
      filter_upwards [Ioi_mem_nhds hτ] with x hx
      exact hE (Set.mem_Ici.2 (le_of_lt hx))
    refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [hE (Set.mem_Ici.2 (le_of_lt hτ))]
    have hED : Real.exp (cumRate r t τ) * disc r t τ = 1 := by
      rw [disc, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linear_combination (-(s τ)) * hED

/-- Cochrane (2023), eq. (3.31), existence: the present-value path satisfies the transversality
condition. -/
theorem tvc_pv (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable r s t) : TVC r (pv r s) t := by
  have h := tendsto_disc_mul hr hs (flowOn_pv hr hs hI) hI
  rwa [sub_self] at h

/-- Cochrane (2023), §3.6.1: a solution of the flow identity on `[t, ∞)` also solves it on
`[a, ∞)` for every `a ≥ t`. -/
theorem FlowOn.mono (hV : FlowOn r s V t) {a : ℝ} (ha : t ≤ a) : FlowOn r s V a :=
  ⟨hV.1.mono (Set.Ici_subset_Ici.2 ha), fun τ hτ => hV.2 τ (lt_of_le_of_lt ha hτ)⟩

/-- Cochrane (2023), §3.6.1: the transversality condition at `t` implies it at every later date
`a ≥ t` (`D(a,T) = D(t,T)/D(t,a)`). -/
theorem TVC.mono (hr : ContinuousOn r (Set.Ici t)) (hT : TVC r V t) {a : ℝ} (ha : t ≤ a) :
    TVC r V a := by
  have h := hT.div_const (disc r t a)
  rw [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  rw [disc_eq_div hr ha hT]
  ring

/-- Cochrane (2023), eq. (3.31), p. 73, uniqueness: every solution of the flow identity (3.30)
that satisfies the transversality condition equals the present value of surpluses at every date
`τ ≥ t`, `V(τ) = ∫_τ^∞ D(τ,u)s(u)du`. -/
theorem eqOn_pv_of_tvc (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hT : TVC r V t) (hI : PVIntegrable r s t) :
    Set.EqOn V (pv r s) (Set.Ici t) := by
  intro a ha
  have ha' : t ≤ a := ha
  exact (valuation_iff_tvc (hr.mono (Set.Ici_subset_Ici.2 ha'))
    (hs.mono (Set.Ici_subset_Ici.2 ha')) (hV.mono ha') (pvIntegrable_of_le hr hI ha')).2
    (hT.mono hr ha')

/-- Cochrane (2023), eqs. (3.30)–(3.31), existence and uniqueness: the present-value path solves
the flow identity with the transversality condition, and any two such solutions coincide on
`[t, ∞)`. -/
theorem exists_unique_flow_tvc (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) :
    (FlowOn r s (pv r s) t ∧ TVC r (pv r s) t) ∧
      ∀ V₁ V₂ : ℝ → ℝ, FlowOn r s V₁ t → TVC r V₁ t → FlowOn r s V₂ t → TVC r V₂ t →
        Set.EqOn V₁ V₂ (Set.Ici t) := by
  refine ⟨⟨flowOn_pv hr hs hI, tvc_pv hr hs hI⟩, fun V₁ V₂ h1 t1 h2 t2 τ hτ => ?_⟩
  rw [eqOn_pv_of_tvc hr hs h1 t1 hI hτ, eqOn_pv_of_tvc hr hs h2 t2 hI hτ]

/-- Cochrane (2023), §3.6.1, A1.4: every solution of the flow identity is the present value plus
a "bubble" growing at the real rate: `V(τ) = pv(τ) + (V(t) − pv(t))/D(t,τ)` on `[t, ∞)`. -/
theorem flow_general_solution (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hV : FlowOn r s V t) (hI : PVIntegrable r s t) {τ : ℝ}
    (hτ : t ≤ τ) : V τ = pv r s τ + (V t - pv r s t) / disc r t τ := by
  have h1 := pv_finite hr hs hV hτ
  rw [pv_eq_of_le hr hI hτ]
  have hD := (disc_pos r t τ).ne'
  field_simp
  linarith

/-- Cochrane (2023), §3.6.1: the bubble paths `pv + c·exp(∫_t^· r)` solve the flow identity
(3.30) for every constant `c`. -/
theorem flowOn_bubble (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable r s t) (c : ℝ) :
    FlowOn r s (fun τ => pv r s τ + c * Real.exp (cumRate r t τ)) t := by
  have hP := flowOn_pv hr hs hI
  refine ⟨hP.1.add (continuousOn_const.mul
    (Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hr))), fun τ hτ => ?_⟩
  have h := (hP.2 τ hτ).add (((hasDerivAt_cumRate hr hτ).exp).const_mul c)
  convert h using 1
  ring

/-- Cochrane (2023), A1.4 and A1.5 (cf. E23): a bubble path satisfies the transversality
condition iff the bubble is zero. -/
theorem tvc_bubble_iff (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hI : PVIntegrable r s t) (c : ℝ) :
    TVC r (fun τ => pv r s τ + c * Real.exp (cumRate r t τ)) t ↔ c = 0 := by
  have hP := tvc_pv hr hs hI
  have h : Tendsto (fun T => disc r t T * (pv r s T + c * Real.exp (cumRate r t T))) atTop
      (𝓝 c) := by
    have h2 := hP.add_const c
    rw [zero_add] at h2
    refine h2.congr' (Eventually.of_forall fun T => ?_)
    have hED : disc r t T * Real.exp (cumRate r t T) = 1 := by
      rw [disc, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linear_combination (-c) * hED
  constructor
  · intro htvc
    exact tendsto_nhds_unique h htvc
  · rintro rfl
    exact h

/-- Cochrane (2023), eq. (3.31), uniqueness: a solution of the flow identity satisfies the
transversality condition iff it coincides with the present-value path on `[t, ∞)`. -/
theorem tvc_iff_eqOn_pv (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) :
    TVC r V t ↔ Set.EqOn V (pv r s) (Set.Ici t) := by
  refine ⟨fun hT => eqOn_pv_of_tvc hr hs hV hT hI, fun h => ?_⟩
  exact (valuation_iff_tvc hr hs hV hI).1 (h (Set.mem_Ici.2 le_rfl))

/-- Cochrane (2023), A1.4, p. 564 ("work … down"): a path equal to the present value of
surpluses at every date `τ ≥ t` solves the flow identity (3.30) and the transversality
condition. -/
theorem flowOn_tvc_of_eqOn_pv (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t)
    (h : Set.EqOn V (pv r s) (Set.Ici t)) : FlowOn r s V t ∧ TVC r V t := by
  have hP := flowOn_pv hr hs hI
  refine ⟨⟨hP.1.congr h, fun τ hτ => ?_⟩, ?_⟩
  · have hev : V =ᶠ[𝓝 τ] pv r s := by
      filter_upwards [Ioi_mem_nhds hτ] with x hx
      exact h (Set.mem_Ici.2 (le_of_lt hx))
    rw [h (Set.mem_Ici.2 (le_of_lt hτ))]
    exact (hP.2 τ hτ).congr_of_eventuallyEq hev
  · refine (tvc_pv hr hs hI).congr' ?_
    filter_upwards [eventually_ge_atTop t] with T hT
    rw [h (Set.mem_Ici.2 hT)]

/-- Cochrane (2023), eqs. (3.30)–(3.31) and A1.4, pp. 564–565 (the flow and present-value
relations are equivalent, "work either up or down"): a path equals the present value of surpluses
at every date `τ ≥ t` iff it solves the flow identity (3.30) with the transversality
condition. -/
theorem eqOn_pv_iff_flowOn_tvc (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) :
    Set.EqOn V (pv r s) (Set.Ici t) ↔ FlowOn r s V t ∧ TVC r V t :=
  ⟨flowOn_tvc_of_eqOn_pv hr hs hI, fun h => eqOn_pv_of_tvc hr hs h.1 h.2 hI⟩

/-! ## Price-level determination and jumps -/

/-- Cochrane (2023), eq. (3.31), p. 73: price-level determination. Given predetermined nominal
debt `B(t) ≠ 0` and a nonzero present value of surpluses, a price level `P(t)` is consistent with
a path of real debt solving the flow identity (3.30) and the transversality condition with
`V(t) = B(t)/P(t)` **iff** `P(t) = B(t)/∫_t^∞ D(t,τ)s(τ)dτ`. -/
theorem price_level_determined (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) {B0 P0 : ℝ} (hB : B0 ≠ 0)
    (hpv : pv r s t ≠ 0) :
    (∃ V : ℝ → ℝ, FlowOn r s V t ∧ TVC r V t ∧ V t = B0 / P0) ↔ P0 = B0 / pv r s t := by
  constructor
  · rintro ⟨V, hV, hT, hVt⟩
    have h := (valuation_iff_tvc hr hs hV hI).2 hT
    rw [hVt] at h
    have hP0 : P0 ≠ 0 := by
      rintro rfl
      rw [div_zero] at h
      exact hpv h.symm
    field_simp
    rw [← h]
    field_simp
  · intro hP
    refine ⟨pv r s, flowOn_pv hr hs hI, tvc_pv hr hs hI, ?_⟩
    rw [hP]
    field_simp

/-- Cochrane (2023), eq. (3.31): with positive nominal debt and a positive present value of
surpluses the equilibrium price level `B(t)/∫D s` is positive. -/
theorem price_level_pos {B0 : ℝ} (hB : 0 < B0) (hpv : 0 < pv r s t) : 0 < B0 / pv r s t :=
  div_pos hB hpv

/-- Cochrane (2023), eq. (3.31): with positive nominal debt and a nonpositive present value of
surpluses there is no positive price level consistent with the flow identity and the
transversality condition. -/
theorem no_positive_price_level (hr : ContinuousOn r (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable r s t) {B0 : ℝ} (hB : 0 < B0)
    (hpv : pv r s t ≤ 0) :
    ¬ ∃ P0 : ℝ, 0 < P0 ∧ ∃ V : ℝ → ℝ, FlowOn r s V t ∧ TVC r V t ∧ V t = B0 / P0 := by
  rintro ⟨P0, hP0, V, hV, hT, hVt⟩
  have h := (valuation_iff_tvc hr hs hV hI).2 hT
  have : 0 < B0 / P0 := div_pos hB hP0
  linarith

/-- Cochrane (2023), §3.6.1, p. 73 ("a diffusion or jump on the right-hand side … shows up in a
diffusion or jump in the price level"): nominal debt `B(t)` is predetermined, so news that changes
the real rates and surpluses from `(r₁, s₁)` to `(r₂, s₂)` moves the price level at `t` by the
ratio of present values, `P₂(t)/P₁(t) = pv₁/pv₂`. -/
theorem price_jump_ratio {r₁ s₁ r₂ s₂ : ℝ → ℝ} (hr₁ : ContinuousOn r₁ (Set.Ici t))
    (hs₁ : ContinuousOn s₁ (Set.Ici t)) (hI₁ : PVIntegrable r₁ s₁ t)
    (hr₂ : ContinuousOn r₂ (Set.Ici t)) (hs₂ : ContinuousOn s₂ (Set.Ici t))
    (hI₂ : PVIntegrable r₂ s₂ t) {B0 P₁ P₂ : ℝ} (hB : B0 ≠ 0) (hpv₁ : pv r₁ s₁ t ≠ 0)
    (hpv₂ : pv r₂ s₂ t ≠ 0)
    (h₁ : ∃ V : ℝ → ℝ, FlowOn r₁ s₁ V t ∧ TVC r₁ V t ∧ V t = B0 / P₁)
    (h₂ : ∃ V : ℝ → ℝ, FlowOn r₂ s₂ V t ∧ TVC r₂ V t ∧ V t = B0 / P₂) :
    P₂ / P₁ = pv r₁ s₁ t / pv r₂ s₂ t := by
  rw [(price_level_determined hr₁ hs₁ hI₁ hB hpv₁).1 h₁,
    (price_level_determined hr₂ hs₂ hI₂ hB hpv₂).1 h₂]
  field_simp

/-! ## The nominal flow (3.29) and the real flow (3.30) -/

/-- Cochrane (2023), eqs. (3.29)–(3.30), p. 73: the nominal flow `B' = iB − Ps` implies the real
flow `V' = (i − π)V − s` for `V = B/P`, `π = P'/P` (quotient rule). -/
theorem hasDerivAt_real_of_nominal {i s B P : ℝ → ℝ} {dP τ : ℝ}
    (hB : HasDerivAt B (i τ * B τ - P τ * s τ) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => B x / P x) ((i τ - dP / P τ) * (B τ / P τ) - s τ) τ := by
  convert hB.div hP hP0 using 1
  field_simp
  ring

/-- Cochrane (2023), eqs. (3.29)–(3.30), p. 73, converse: the real flow for `V = B/P` implies
the nominal flow `B' = iB − Ps`. -/
theorem hasDerivAt_nominal_of_real {i s B P : ℝ → ℝ} {dP τ : ℝ}
    (hV : HasDerivAt (fun x => B x / P x) ((i τ - dP / P τ) * (B τ / P τ) - s τ) τ)
    (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt B (i τ * B τ - P τ * s τ) τ := by
  have h := hV.mul hP
  have hev : B =ᶠ[𝓝 τ] fun x => B x / P x * P x := by
    filter_upwards [hP.continuousAt.eventually_ne hP0] with x hx
    field_simp
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  field_simp
  ring

/-- Cochrane (2023), p. 73: the ex-post real return on short-term debt,
`dR = i dt + d(1/P)/(1/P)`, equals `(i − π)dt`: `(1/P)' = −π·(1/P)`. -/
theorem hasDerivAt_inv_price {P : ℝ → ℝ} {dP τ : ℝ} (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => 1 / P x) (-(dP / P τ) * (1 / P τ)) τ := by
  have h := (hasDerivAt_const τ (1 : ℝ)).div hP hP0
  convert h using 1
  field_simp
  ring

/-- Cochrane (2023), eqs. (3.29)–(3.30), p. 73: nominal paths `B, P` (continuous on `[t, ∞)`, `P`
positive, the price level free to jump at `t`) obeying the nominal flow (3.29) on `(t, ∞)` give a
real value `B/P` obeying the flow identity (3.30) with real rate `i − P'/P`. -/
theorem flowOn_of_nominal {i s B P dP : ℝ → ℝ} (hBc : ContinuousOn B (Set.Ici t))
    (hPc : ContinuousOn P (Set.Ici t)) (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hB : ∀ τ, t < τ → HasDerivAt B (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) :
    FlowOn (fun τ => i τ - dP τ / P τ) s (fun τ => B τ / P τ) t :=
  ⟨hBc.div hPc fun x hx => (hPpos x hx).ne', fun τ hτ =>
    hasDerivAt_real_of_nominal (hB τ hτ) (hP τ hτ) (hPpos τ hτ.le).ne'⟩

/-- Cochrane (2023), eqs. (3.29)–(3.31): with nominal paths obeying (3.29), the transversality
condition on `B/P` and nonzero debt and present value, the price level at `t` is
`P(t) = B(t)/∫_t^∞ D(t,τ)s(τ)dτ` with `D` built from the real rate `i − π`. -/
theorem price_level_of_nominal {i s B P dP : ℝ → ℝ}
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hBc : ContinuousOn B (Set.Ici t)) (hPc : ContinuousOn P (Set.Ici t))
    (hPpos : ∀ τ, t ≤ τ → 0 < P τ)
    (hB : ∀ τ, t < τ → HasDerivAt B (i τ * B τ - P τ * s τ) τ)
    (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ)
    (hT : TVC (fun τ => i τ - dP τ / P τ) (fun τ => B τ / P τ) t) (hB0 : B t ≠ 0)
    (hpv : pv (fun τ => i τ - dP τ / P τ) s t ≠ 0) :
    P t = B t / pv (fun τ => i τ - dP τ / P τ) s t :=
  (price_level_determined hr hs hI hB0 hpv).1
    ⟨_, flowOn_of_nominal hBc hPc hPpos hB hP, hT, rfl⟩

/-- Cochrane (2023), eqs. (3.29) and (3.31), A1.4, pp. 564–565: for a positive price path
differentiable on `(t, ∞)` (free to jump at `t`) and a nominal debt path continuous on
`[t, ∞)`, the valuation equation `B(τ)/P(τ) = ∫_τ^∞ D(τ,u)s(u)du` at every date `τ ≥ t` holds
iff the nominal flow (3.29) `B' = iB − Ps` holds on `(t, ∞)` together with the transversality
condition, where `D` discounts at the real rate `i − P'/P`. -/
theorem nominal_pv_iff_flow {i s B P dP : ℝ → ℝ}
    (hr : ContinuousOn (fun τ => i τ - dP τ / P τ) (Set.Ici t))
    (hs : ContinuousOn s (Set.Ici t)) (hI : PVIntegrable (fun τ => i τ - dP τ / P τ) s t)
    (hBc : ContinuousOn B (Set.Ici t)) (hPc : ContinuousOn P (Set.Ici t))
    (hPpos : ∀ τ, t ≤ τ → 0 < P τ) (hP : ∀ τ, t < τ → HasDerivAt P (dP τ) τ) :
    Set.EqOn (fun τ => B τ / P τ) (pv (fun τ => i τ - dP τ / P τ) s) (Set.Ici t) ↔
      (∀ τ, t < τ → HasDerivAt B (i τ * B τ - P τ * s τ) τ) ∧
        TVC (fun τ => i τ - dP τ / P τ) (fun τ => B τ / P τ) t := by
  rw [eqOn_pv_iff_flowOn_tvc hr hs hI]
  constructor
  · rintro ⟨hF, hT⟩
    exact ⟨fun τ hτ => hasDerivAt_nominal_of_real (hF.2 τ hτ) (hP τ hτ) (hPpos τ hτ.le).ne', hT⟩
  · rintro ⟨hB, hT⟩
    exact ⟨flowOn_of_nominal hBc hPc hPpos hB hP, hT⟩

/-! ## Discount factors, A1 (1.26), and the A1.4 chains -/

/-- Cochrane (2023), §3.6.1, p. 74, and A1 (1.26), p. 564: a (deterministic) discount factor with
`Λ'/Λ = −r` on `(t, ∞)` satisfies `Λ(τ)/Λ(t) = exp(−∫_t^τ r)`, i.e. `Λ(τ) = Λ(t)D(t,τ)`. -/
theorem discountFactor_eq (hr : ContinuousOn r (Set.Ici t)) {Λ : ℝ → ℝ}
    (hΛc : ContinuousOn Λ (Set.Ici t)) (hΛ : ∀ τ, t < τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    {τ : ℝ} (hτ : t ≤ τ) : Λ τ = Λ t * disc r t τ := by
  have hc : ContinuousOn (fun x => Λ x * Real.exp (cumRate r t x)) (Set.Ici t) :=
    hΛc.mul (Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hr))
  have hd : ∀ x, t < x → HasDerivAt (fun x => Λ x * Real.exp (cumRate r t x)) 0 x := by
    intro x hx
    convert (hΛ x hx).mul (hasDerivAt_cumRate hr hx).exp using 1
    ring
  have h := eq_of_hasDerivAt_zero hc hd hτ
  rw [cumRate_self, Real.exp_zero, mul_one] at h
  rw [← h, disc, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- Cochrane (2023), A1 (1.26), first line, p. 564: `r = −Λ'/Λ` is the same statement as
`Λ' = −rΛ` (for `Λ ≠ 0`). -/
theorem rate_eq_neg_logDeriv {Λ0 dΛ r0 : ℝ} (hΛ : Λ0 ≠ 0) : r0 = -(dΛ / Λ0) ↔ dΛ = -r0 * Λ0 := by
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    rw [h]
    field_simp

/-- Cochrane (2023), A1 (1.26), second line, p. 564: with `Λ' = −(i − π)Λ` and `π = P'/P`, the
nominal discount factor `Λ/P` satisfies `(Λ/P)' = −i·(Λ/P)`. -/
theorem hasDerivAt_nominal_discount {i Λ P : ℝ → ℝ} {dP τ : ℝ}
    (hΛ : HasDerivAt Λ (-(i τ - dP / P τ) * Λ τ) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0) :
    HasDerivAt (fun x => Λ x / P x) (-(i τ) * (Λ τ / P τ)) τ := by
  convert hΛ.div hP hP0 using 1
  field_simp
  ring

/-- Cochrane (2023), A1 (1.26), third line, p. 564 ("a few lines of algebra starting from
(3.33)"): with `W' = (i − π)W` and `π = P'/P`, `(1/(PW))' = −i·(1/(PW))`. -/
theorem hasDerivAt_inv_PW {i W P : ℝ → ℝ} {dP τ : ℝ}
    (hW : HasDerivAt W ((i τ - dP / P τ) * W τ) τ) (hP : HasDerivAt P dP τ) (hP0 : P τ ≠ 0)
    (hW0 : W τ ≠ 0) :
    HasDerivAt (fun x => 1 / (P x * W x)) (-(i τ) * (1 / (P τ * W τ))) τ := by
  have h := (hasDerivAt_const τ (1 : ℝ)).div (hP.mul hW) (mul_ne_zero hP0 hW0)
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- Cochrane (2023), A1.4, pp. 564–565 ("work either up or down"), discount-factor chain: with
`Λ' = −rΛ` and `Λ ≠ 0`, the flow `V' = rV − s` holds iff `d(ΛV) = −Λs`. -/
theorem flow_iff_Lambda {Λ : ℝ → ℝ} {τ : ℝ} (hΛ : HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hΛ0 : Λ τ ≠ 0) :
    HasDerivAt V (r τ * V τ - s τ) τ ↔
      HasDerivAt (fun x => Λ x * V x) (-(Λ τ * s τ)) τ := by
  constructor
  · intro hV
    convert hΛ.mul hV using 1
    ring
  · intro h
    have hq := h.div hΛ hΛ0
    have hev : V =ᶠ[𝓝 τ] fun x => Λ x * V x / Λ x := by
      filter_upwards [hΛ.continuousAt.eventually_ne hΛ0] with x hx
      field_simp
    refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp
    ring

/-- Cochrane (2023), A1.4, pp. 564–565, nominal discount-factor chain: with
`Λ' = −(i − π)Λ`, `π = P'/P`, the nominal flow (3.29) `B' = iB − Ps` holds iff
`d(Λ B/P) = −Λ s`. -/
theorem nominal_flow_iff_Lambda {i s B P Λ : ℝ → ℝ} {dP τ : ℝ}
    (hΛ : HasDerivAt Λ (-(i τ - dP / P τ) * Λ τ) τ) (hΛ0 : Λ τ ≠ 0) (hP : HasDerivAt P dP τ)
    (hP0 : P τ ≠ 0) :
    HasDerivAt B (i τ * B τ - P τ * s τ) τ ↔
      HasDerivAt (fun x => Λ x * (B x / P x)) (-(Λ τ * s τ)) τ := by
  rw [← flow_iff_Lambda (r := fun τ => i τ - dP / P τ) (V := fun x => B x / P x) hΛ hΛ0]
  exact ⟨fun h => hasDerivAt_real_of_nominal h hP hP0,
    fun h => hasDerivAt_nominal_of_real h hP hP0⟩

/-- Cochrane (2023), A1.4, p. 565, ex-post return chain: with `W' = rW` and `W ≠ 0`, the flow
`V' = rV − s` holds iff `d(V/W) = −s/W`. -/
theorem flow_iff_W {W : ℝ → ℝ} {τ : ℝ} (hW : HasDerivAt W (r τ * W τ) τ) (hW0 : W τ ≠ 0) :
    HasDerivAt V (r τ * V τ - s τ) τ ↔ HasDerivAt (fun x => V x / W x) (-(s τ / W τ)) τ := by
  constructor
  · intro hV
    convert hV.div hW hW0 using 1
    field_simp
    ring
  · intro h
    have hq := h.mul hW
    have hev : V =ᶠ[𝓝 τ] fun x => V x / W x * W x := by
      filter_upwards [hW.continuousAt.eventually_ne hW0] with x hx
      field_simp
    refine (hq.congr_of_eventuallyEq hev).congr_deriv ?_
    field_simp
    ring

/-- Cochrane (2023), A1.4, p. 565, nominal ex-post return chain: with `W' = (i − π)W`,
`π = P'/P`, the nominal flow (3.29) holds iff `d((B/P)/W) = −s/W`. -/
theorem nominal_flow_iff_W {i s B P W : ℝ → ℝ} {dP τ : ℝ}
    (hW : HasDerivAt W ((i τ - dP / P τ) * W τ) τ) (hW0 : W τ ≠ 0) (hP : HasDerivAt P dP τ)
    (hP0 : P τ ≠ 0) :
    HasDerivAt B (i τ * B τ - P τ * s τ) τ ↔
      HasDerivAt (fun x => B x / P x / W x) (-(s τ / W τ)) τ := by
  rw [← flow_iff_W (r := fun τ => i τ - dP / P τ) (V := fun x => B x / P x) hW hW0]
  exact ⟨fun h => hasDerivAt_real_of_nominal h hP hP0,
    fun h => hasDerivAt_nominal_of_real h hP hP0⟩

/-! ## The ex-post return `W` (3.32)–(3.33) -/

/-- Cochrane (2023), eq. (3.33), p. 74: the cumulative ex-post real return on government debt,
`W' = (i − π)W` with `π = P'/P`, has the closed form `W(τ)/W(t₀) = exp(∫_{t₀}^τ i)·P(t₀)/P(τ)`
(both paths continuous on `[t₀, ∞)`, so the price level may jump at `t₀`). -/
theorem W_closed_form {i P W dP : ℝ → ℝ} {t₀ : ℝ} (hi : ContinuousOn i (Set.Ici t₀))
    (hPc : ContinuousOn P (Set.Ici t₀)) (hWc : ContinuousOn W (Set.Ici t₀))
    (hP : ∀ τ, t₀ < τ → HasDerivAt P (dP τ) τ)
    (hW : ∀ τ, t₀ < τ → HasDerivAt W ((i τ - dP τ / P τ) * W τ) τ)
    (hP0 : ∀ τ, t₀ ≤ τ → P τ ≠ 0) (hW0 : W t₀ ≠ 0) {τ : ℝ} (hτ : t₀ ≤ τ) :
    W τ / W t₀ = Real.exp (cumRate i t₀ τ) * P t₀ / P τ := by
  have hc : ContinuousOn (fun x => W x * P x * Real.exp (-cumRate i t₀ x)) (Set.Ici t₀) :=
    (hWc.mul hPc).mul (Real.continuous_exp.comp_continuousOn (continuousOn_cumRate hi).neg)
  have hd : ∀ x, t₀ < x →
      HasDerivAt (fun x => W x * P x * Real.exp (-cumRate i t₀ x)) 0 x := by
    intro x hx
    have hPx := hP0 x hx.le
    convert ((hW x hx).mul (hP x hx)).mul (hasDerivAt_cumRate hi hx).neg.exp using 1
    simp only [Pi.mul_apply, Pi.neg_apply]
    field_simp
    ring
  have h := eq_of_hasDerivAt_zero hc hd hτ
  rw [cumRate_self, neg_zero, Real.exp_zero, mul_one] at h
  have hPτ := hP0 τ hτ
  have hE : Real.exp (-cumRate i t₀ τ) * Real.exp (cumRate i t₀ τ) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  field_simp
  linear_combination (Real.exp (cumRate i t₀ τ)) * h - W τ * P τ * hE

/-- Cochrane (2023), eqs. (3.32)–(3.33): discounting at the ex-post return is discounting at the
real rate: if `W' = rW` on `(t, ∞)` with `W` continuous and nonzero on `[t, ∞)`, then
`W(t)/W(τ) = D(t,τ)`. -/
theorem disc_eq_W_ratio (hr : ContinuousOn r (Set.Ici t)) {W : ℝ → ℝ}
    (hWc : ContinuousOn W (Set.Ici t)) (hW : ∀ τ, t < τ → HasDerivAt W (r τ * W τ) τ)
    (hW0 : ∀ τ, t ≤ τ → W τ ≠ 0) {τ : ℝ} (hτ : t ≤ τ) : disc r t τ = W t / W τ := by
  have hc : ContinuousOn (fun x => W x * disc r t x) (Set.Ici t) := hWc.mul (continuousOn_disc hr)
  have hd : ∀ x, t < x → HasDerivAt (fun x => W x * disc r t x) 0 x := by
    intro x hx
    convert (hW x hx).mul (hasDerivAt_disc hr hx) using 1
    ring
  have h := eq_of_hasDerivAt_zero hc hd hτ
  rw [disc_self, mul_one] at h
  have := hW0 τ hτ
  field_simp
  linarith

/-- Cochrane (2023), eq. (3.32), p. 74, and A1.4, p. 565: discounting at the ex-post return `W`
(`W' = rW`, `W ≠ 0`), along the flow identity, `V(t)/W(t) = ∫_t^∞ s(τ)/W(τ)dτ` holds iff
`V(T)/W(T) → 0`. -/
theorem valuation_W_iff (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) {W : ℝ → ℝ}
    (hWc : ContinuousOn W (Set.Ici t)) (hW : ∀ τ, t < τ → HasDerivAt W (r τ * W τ) τ)
    (hW0 : ∀ τ, t ≤ τ → W τ ≠ 0) :
    V t / W t = ∫ τ in Set.Ioi t, s τ / W τ ↔ Tendsto (fun T => V T / W T) atTop (𝓝 0) := by
  have hWt := hW0 t le_rfl
  have hint : ∫ τ in Set.Ioi t, s τ / W τ = pv r s t / W t := by
    rw [pv, ← integral_div]
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    have hWτ := hW0 τ (le_of_lt hτ)
    rw [disc_eq_W_ratio hr hWc hW hW0 (le_of_lt hτ)]
    field_simp
  have hlim : Tendsto (fun T => V T / W T) atTop (𝓝 0) ↔ TVC r V t := by
    have hcongr : (fun T => V T / W T) =ᶠ[atTop] fun T => disc r t T * V T / W t := by
      filter_upwards [eventually_ge_atTop t] with T hT
      have hWT := hW0 T hT
      rw [disc_eq_W_ratio hr hWc hW hW0 hT]
      field_simp
    rw [tendsto_congr' hcongr, TVC]
    constructor
    · intro h
      have h2 := h.mul_const (W t)
      rw [zero_mul] at h2
      refine h2.congr (fun T => ?_)
      field_simp
    · intro h
      have h2 := h.div_const (W t)
      rwa [zero_div] at h2
  rw [hint, hlim, ← valuation_iff_tvc hr hs hV hI]
  constructor
  · intro h
    field_simp at h
    exact h
  · intro h
    rw [h]

/-- Cochrane (2023), eq. (3.31) with a generic discount factor (box p. 71, eq. (3.31) p. 73):
with `Λ' = −rΛ`, `Λ > 0`, along the flow identity, `V(t) = ∫_t^∞ (Λ(τ)/Λ(t))s(τ)dτ` holds iff
`Λ(T)V(T) → 0`. -/
theorem valuation_Lambda_iff (hr : ContinuousOn r (Set.Ici t)) (hs : ContinuousOn s (Set.Ici t))
    (hV : FlowOn r s V t) (hI : PVIntegrable r s t) {Λ : ℝ → ℝ}
    (hΛc : ContinuousOn Λ (Set.Ici t)) (hΛ : ∀ τ, t < τ → HasDerivAt Λ (-(r τ) * Λ τ) τ)
    (hΛ0 : Λ t ≠ 0) :
    V t = ∫ τ in Set.Ioi t, Λ τ / Λ t * s τ ↔ Tendsto (fun T => Λ T * V T) atTop (𝓝 0) := by
  have hint : ∫ τ in Set.Ioi t, Λ τ / Λ t * s τ = pv r s t := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    rw [discountFactor_eq hr hΛc hΛ (le_of_lt hτ)]
    field_simp
  have hlim : Tendsto (fun T => Λ T * V T) atTop (𝓝 0) ↔ TVC r V t := by
    have hcongr : (fun T => Λ T * V T) =ᶠ[atTop] fun T => Λ t * (disc r t T * V T) := by
      filter_upwards [eventually_ge_atTop t] with T hT
      rw [discountFactor_eq hr hΛc hΛ hT]
      ring
    rw [tendsto_congr' hcongr, TVC]
    constructor
    · intro h
      have h2 := h.const_mul (Λ t)⁻¹
      rw [mul_zero] at h2
      refine h2.congr (fun T => ?_)
      field_simp
    · intro h
      have h2 := h.const_mul (Λ t)
      rwa [mul_zero] at h2
  rw [hint, hlim, valuation_iff_tvc hr hs hV hI]

/-! ## Constant real rate (p. 74) -/

/-- Cochrane (2023), p. 74: with a constant real rate `c`, the present value is
`∫_t^∞ e^{−c(τ−t)}s(τ)dτ`. -/
theorem pv_const_rate (c : ℝ) (s : ℝ → ℝ) (t : ℝ) :
    pv (fun _ => c) s t = ∫ τ in Set.Ioi t, Real.exp (-(c * (τ - t))) * s τ := by
  simp only [pv, disc_const]

/-- Cochrane (2023), p. 74: with a constant real rate `c > 0` a constant surplus `s₀` is
integrably discounted. -/
theorem pvIntegrable_const {c : ℝ} (hc : 0 < c) (s₀ t : ℝ) :
    PVIntegrable (fun _ => c) (fun _ => s₀) t := by
  have h : IntegrableOn (fun τ => s₀ * Real.exp (c * t) * Real.exp (-c * τ)) (Set.Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul _
  refine h.congr_fun (fun τ _ => ?_) measurableSet_Ioi
  simp only [disc_const]
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

/-- Cochrane (2023), p. 74 and A1 (1.17): with a constant real rate `c > 0` and a constant
surplus `s₀`, the present value of surpluses is `s₀/c`. -/
theorem pv_const_const {c : ℝ} (hc : 0 < c) (s₀ t : ℝ) :
    pv (fun _ => c) (fun _ => s₀) t = s₀ / c := by
  have h1 : pv (fun _ => c) (fun _ => s₀) t =
      ∫ τ in Set.Ioi t, s₀ * Real.exp (c * t) * Real.exp (-c * τ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ _ => ?_)
    simp only [disc_const]
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [h1, integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  have hE : Real.exp (c * t) * Real.exp (-(c * t)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  simp only [neg_mul]
  field_simp
  linear_combination s₀ * hE

/-- Cochrane (2023), p. 74: with a constant real rate `c > 0` and constant surplus `s₀`, the
unique solution of the flow identity with the transversality condition is the constant
`V = s₀/c`, so `B(t)/P(t) = s₀/c`. -/
theorem value_const_const {c : ℝ} (hc : 0 < c) {s₀ : ℝ}
    (hV : FlowOn (fun _ => c) (fun _ => s₀) V t) (hT : TVC (fun _ => c) V t) {τ : ℝ}
    (hτ : t ≤ τ) : V τ = s₀ / c := by
  rw [eqOn_pv_of_tvc continuousOn_const continuousOn_const hV hT (pvIntegrable_const hc s₀ t) hτ,
    pv_const_const hc]

end Cochrane.Generality.ContinuousShort
