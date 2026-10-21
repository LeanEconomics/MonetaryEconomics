/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OpenEconomy.RiskSharing
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Uncovered interest parity and the terms of trade

Galí (2015), Chapter 8, §8.1.1.3, pp. 231–232: the exact UIP condition, eqs. (18), (19),
(20), fn. 5 and the closing remark of p. 232.

## Main results

* `uip_exact` (p. 231): from the bond-pricing equations `Q_t = E_t{Q_{t,t+1}}` and
  `ℰ_t Q*_t = E_t{Q_{t,t+1} ℰ_{t+1}}`, `E_t{Q_{t,t+1}[e^{i_t} − e^{i*_t} ℰ_{t+1}/ℰ_t]} = 0`.
* `uip_node_iff`, `uipGap_zero`, `hasFDerivAt_uipGap` (eq. (18) as an **exact derivative**):
  at a node with finitely many successor states, the exact condition is equivalent to
  `i − i* = G(q̂, Δe)` with `G` an explicit function of the SDF deviations `q̂_j` and the
  depreciations `Δe_j`; `G(0) = 0` and `DG(0)(dq̂, dΔe) = Σ_j ξ_j dΔe_j = E_t{dΔe}`, i.e.
  `i = i* + E_tΔe_{t+1}` to first order — the second-moment (risk-premium) terms are what the
  first-order approximation drops. `uipGap_const`: with no exchange-rate risk it is exact.
* `tot_difference` (eq. (19)): (14) and (18) give
  `s_t = (i*_t − E_tπ*_{t+1}) − (i_t − E_tπ_{H,t+1}) + E_t s_{t+1}`.
* `tot_forward` (eq. (20)): given `lim_T E_t s_T = 0` (**stated as a hypothesis**, see
  `forward_iff`), the partial sums of `E_t[(i*_{t+k} − π*_{t+k+1}) − (i_{t+k} − π_{H,t+k+1})]`
  converge to `s_t`; `forward_iff`: given (19), the representation holds iff the limit
  condition does; `forward_counterexample`: without it (20) fails.
* `tot_difference_of_eulers` (p. 232): (19) follows from the domestic Euler equation (11), the
  world Euler equation, risk sharing (17), the CPI identity (13) and `E_t z_{t+1} = ρ_z z_t`.
-/

namespace Gali.OpenEconomy.UIP

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The exact UIP condition -/

/-- Galí (2015), p. 231 (**exact UIP**): if the domestic bond price is
`e^{−i_t} = E_t{Q_{t,t+1}}` and the foreign-currency bond satisfies
`ℰ_t e^{−i*_t} = E_t{Q_{t,t+1} ℰ_{t+1}}`, and `e^{i_t}`, `e^{i*_t}/ℰ_t` are known at `t`, then
`E_t{Q_{t,t+1}[e^{i_t} − e^{i*_t} ℰ_{t+1}/ℰ_t]} = 0`. -/
theorem uip_exact (hpull : 𝔼.PullOut) {Q i is Ex : ℕ → Ω → ℝ} (t : ℕ)
    (hEx : ∀ ω, 0 < Ex t ω)
    (hdom : ∀ ω, Real.exp (-(i t ω)) = 𝔼.E t (Q t) ω)
    (hfor : ∀ ω, Ex t ω * Real.exp (-(is t ω)) = 𝔼.E t (Q t * Ex (t + 1)) ω)
    (hk1 : 𝔼.E t (fun ω => Real.exp (i t ω)) = fun ω => Real.exp (i t ω))
    (hk2 : 𝔼.E t (fun ω => Real.exp (is t ω) / Ex t ω) = fun ω => Real.exp (is t ω) / Ex t ω) :
    𝔼.E t (fun ω => Q t ω * (Real.exp (i t ω) - Real.exp (is t ω) * Ex (t + 1) ω / Ex t ω))
      = 0 := by
  have hfun : (fun ω => Q t ω * (Real.exp (i t ω) - Real.exp (is t ω) * Ex (t + 1) ω / Ex t ω))
      = (fun ω => Real.exp (i t ω)) * Q t
        - (fun ω => Real.exp (is t ω) / Ex t ω) * (Q t * Ex (t + 1)) := by
    funext ω
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring
  rw [hfun, map_sub, hpull t _ _ hk1, hpull t _ _ hk2]
  funext ω
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.zero_apply]
  rw [← hdom ω, ← hfor ω, ← Real.exp_add]
  have := hEx ω
  field_simp
  rw [← Real.exp_add]
  simp

/-! ### Eq. (18) as an exact derivative at a node -/

variable {ι : Type*} [Fintype ι]

/-- Galí (2015), eq. (18), p. 232: the exact interest differential at a node,
`G(q̂, Δe) = log Σ_j ξ_j e^{q̂_j + Δe_j} − log Σ_j ξ_j e^{q̂_j}`, where `Q_{t,t+1}(j) = Q̄ e^{q̂_j}`
and `Δe_j = log(ℰ_{t+1}(j)/ℰ_t)`. -/
noncomputable def uipGap (ξ : ι → ℝ) (x : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  Real.log (∑ j, ξ j * Real.exp (x.1 j + x.2 j)) - Real.log (∑ j, ξ j * Real.exp (x.1 j))

/-- Galí (2015), p. 231–232: at a node with successor probabilities `ξ_j > 0`, the exact UIP
condition `Σ_j ξ_j Q_j (e^{i} − e^{i*} e^{Δe_j}) = 0` (with `Q_j = Q̄ e^{q̂_j}`, `Q̄ > 0`) holds
**iff** `i − i* = G(q̂, Δe)`. -/
theorem uip_node_iff [Nonempty ι] {ξ : ι → ℝ} (hξ : ∀ j, 0 < ξ j) {Qbar i is : ℝ}
    (hQ : 0 < Qbar) (q de : ι → ℝ) :
    ∑ j, ξ j * (Qbar * Real.exp (q j) * (Real.exp i - Real.exp is * Real.exp (de j))) = 0 ↔
      i - is = uipGap ξ (q, de) := by
  have hA : 0 < ∑ j, ξ j * Real.exp (q j) :=
    Finset.sum_pos (fun j _ => mul_pos (hξ j) (Real.exp_pos _)) Finset.univ_nonempty
  have hB : 0 < ∑ j, ξ j * Real.exp (q j + de j) :=
    Finset.sum_pos (fun j _ => mul_pos (hξ j) (Real.exp_pos _)) Finset.univ_nonempty
  have hsum : ∑ j, ξ j * (Qbar * Real.exp (q j) * (Real.exp i - Real.exp is * Real.exp (de j)))
      = Qbar * (Real.exp i * ∑ j, ξ j * Real.exp (q j)
        - Real.exp is * ∑ j, ξ j * Real.exp (q j + de j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.exp_add]
    ring
  rw [hsum, uipGap]
  simp only
  constructor
  · intro h
    have h1 : Real.exp i * ∑ j, ξ j * Real.exp (q j)
        = Real.exp is * ∑ j, ξ j * Real.exp (q j + de j) := by
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h hQ.ne'
      · linarith
    have h2 := congrArg Real.log h1
    rw [Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_mul (Real.exp_pos _).ne' hB.ne',
      Real.log_exp, Real.log_exp] at h2
    linarith
  · intro h
    have h1 : Real.exp i * ∑ j, ξ j * Real.exp (q j)
        = Real.exp is * ∑ j, ξ j * Real.exp (q j + de j) := by
      have h3 : i + Real.log (∑ j, ξ j * Real.exp (q j))
          = is + Real.log (∑ j, ξ j * Real.exp (q j + de j)) := by linarith
      have h4 := congrArg Real.exp h3
      rwa [Real.exp_add, Real.exp_add, Real.exp_log hA, Real.exp_log hB] at h4
    rw [h1, sub_self, mul_zero]

/-- Galí (2015), eq. (18), p. 232: at the deterministic steady state (`q̂ = 0`, `Δe = 0`) the
interest differential is zero, `G(0) = 0` (probabilities summing to one). -/
theorem uipGap_zero {ξ : ι → ℝ} (hsum : ∑ j, ξ j = 1) : uipGap ξ 0 = 0 := by
  simp [uipGap, hsum]

/-- Galí (2015), eq. (18), p. 232, with **no exchange-rate risk** (`Δe_j = d` in every state):
`G(q̂, Δe) = d`, so `i = i* + Δe_{t+1}` holds exactly whatever the SDF. -/
theorem uipGap_const [Nonempty ι] {ξ : ι → ℝ} (hξ : ∀ j, 0 < ξ j) (q : ι → ℝ) (d : ℝ) :
    uipGap ξ (q, fun _ => d) = d := by
  have hA : 0 < ∑ j, ξ j * Real.exp (q j) :=
    Finset.sum_pos (fun j _ => mul_pos (hξ j) (Real.exp_pos _)) Finset.univ_nonempty
  have : ∑ j, ξ j * Real.exp (q j + d) = Real.exp d * ∑ j, ξ j * Real.exp (q j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.exp_add]; ring
  simp only [uipGap]
  rw [this, Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp]
  ring

/-- Galí (2015), eq. (18): the expectation functional `(dq̂, dΔe) ↦ Σ_j ξ_j dΔe_j`
(`E_t` of the depreciation perturbation) as a continuous linear map. -/
noncomputable def expectDe (ξ : ι → ℝ) : (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ :=
  ∑ j, ξ j • ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))

/-- Galí (2015), eq. (18): `expectDe ξ (dq̂, dΔe) = Σ_j ξ_j dΔe_j`. -/
theorem expectDe_apply (ξ : ι → ℝ) (v : (ι → ℝ) × (ι → ℝ)) :
    expectDe ξ v = ∑ j, ξ j * v.2 j := by
  simp [expectDe]

/-- Galí (2015), eq. (18), p. 232 (**log-linear UIP as an exact derivative**): at the
deterministic steady state the interest differential `G` has Fréchet derivative
`(dq̂, dΔe) ↦ Σ_j ξ_j dΔe_j = E_t{dΔe_{t+1}}`: to first order `i_t = i*_t + E_tΔe_{t+1}`, the
SDF perturbation `dq̂` dropping out. -/
theorem hasFDerivAt_uipGap {ξ : ι → ℝ} (hsum : ∑ j, ξ j = 1) :
    HasFDerivAt (uipGap ξ) (expectDe ξ) 0 := by
  classical
  set p1 : ι → (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ := fun j =>
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))
  set p2 : ι → (ι → ℝ) × (ι → ℝ) →L[ℝ] ℝ := fun j =>
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))
  have hB : HasFDerivAt (fun x : (ι → ℝ) × (ι → ℝ) => ∑ j, ξ j * Real.exp (x.1 j + x.2 j))
      (∑ j, ξ j • (Real.exp (0 + 0) • (p1 j + p2 j))) 0 := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have h := ((((p1 j).hasFDerivAt (x := 0)).add
      ((p2 j).hasFDerivAt (x := 0))).exp).const_mul (ξ j)
    simpa [p1, p2] using h
  have hA : HasFDerivAt (fun x : (ι → ℝ) × (ι → ℝ) => ∑ j, ξ j * Real.exp (x.1 j))
      (∑ j, ξ j • (Real.exp 0 • p1 j)) 0 := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have h := (((p1 j).hasFDerivAt (x := 0)).exp).const_mul (ξ j)
    simpa [p1] using h
  have hB0 : (∑ j, ξ j * Real.exp ((0 : (ι → ℝ) × (ι → ℝ)).1 j + (0 : (ι → ℝ) × (ι → ℝ)).2 j))
      = 1 := by simp [hsum]
  have hA0 : (∑ j, ξ j * Real.exp ((0 : (ι → ℝ) × (ι → ℝ)).1 j)) = 1 := by simp [hsum]
  have hlogB := hB.log (by rw [hB0]; exact one_ne_zero)
  have hlogA := hA.log (by rw [hA0]; exact one_ne_zero)
  rw [hB0, inv_one, one_smul] at hlogB
  rw [hA0, inv_one, one_smul] at hlogA
  have hd := hlogB.sub hlogA
  refine hd.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [expectDe, Real.exp_zero, add_zero, one_smul, _root_.sub_apply, p1, p2]
  simp only [FunLike.coe_sum, Finset.sum_apply, _root_.smul_apply,
    _root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply,
    smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ### Eqs. (19) and (20) -/

/-- Galí (2015), eq. (19), p. 232: combining the law of one price (14),
`s_t = e_t + p*_t − p_{H,t}`, with UIP (18), `i_t = i*_t + E_t e_{t+1} − e_t`, gives
`s_t = (i*_t − E_tπ*_{t+1}) − (i_t − E_tπ_{H,t+1}) + E_t s_{t+1}`
(with `p*`, `p_H` known at `t`). -/
theorem tot_difference {s e ps pH i is : ℕ → Ω → ℝ} (t : ℕ)
    (h14 : ∀ t ω, s t ω = e t ω + ps t ω - pH t ω)
    (h18 : ∀ ω, i t ω = is t ω + (𝔼.E t (e (t + 1)) ω - e t ω))
    (hps : 𝔼.E t (ps t) = ps t) (hpH : 𝔼.E t (pH t) = pH t) (ω : Ω) :
    s t ω = (is t ω - 𝔼.E t (ps (t + 1) - ps t) ω) - (i t ω - 𝔼.E t (pH (t + 1) - pH t) ω)
      + 𝔼.E t (s (t + 1)) ω := by
  have hs1 : s (t + 1) = e (t + 1) + ps (t + 1) - pH (t + 1) := funext fun ω => h14 (t + 1) ω
  rw [hs1]
  simp only [map_sub, map_add, hps, hpH, Pi.add_apply, Pi.sub_apply]
  rw [h14 t ω, h18 ω]
  ring

/-- Galí (2015), (20), p. 232: iterating `s_t = d_t + E_t s_{t+1}` forward,
`s_t = Σ_{k<T} E_t d_{t+k} + E_t s_{t+T}` for every horizon `T`. -/
theorem forward_partial {s d : ℕ → Ω → ℝ} (hs : ∀ t, s t = d t + 𝔼.E t (s (t + 1)))
    (hadapt : ∀ t, 𝔼.E t (s t) = s t) (t T : ℕ) :
    s t = ∑ k ∈ Finset.range T, 𝔼.E t (d (t + k)) + 𝔼.E t (s (t + T)) := by
  induction T with
  | zero => simp [hadapt t]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [hs (t + T), map_add, 𝔼.tower (Nat.le_add_right t T), ← add_assoc]

/-- Galí (2015), eq. (20) and fn. 5, p. 232: given (19) in the form `s_t = d_t + E_t s_{t+1}`,
the forward representation `s_t = lim_T Σ_{k<T} E_t d_{t+k}` holds **iff**
`lim_T E_t s_T = 0`. -/
theorem forward_iff {s d : ℕ → Ω → ℝ} (hs : ∀ t, s t = d t + 𝔼.E t (s (t + 1)))
    (hadapt : ∀ t, 𝔼.E t (s t) = s t) (t : ℕ) (ω : Ω) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (d (t + k)) ω) atTop (𝓝 (s t ω)) ↔
      Tendsto (fun T => 𝔼.E t (s T) ω) atTop (𝓝 0) := by
  have hp : ∀ T, ∑ k ∈ Finset.range T, 𝔼.E t (d (t + k)) ω
      = s t ω - 𝔼.E t (s (t + T)) ω := fun T => by
    have := congrFun (forward_partial 𝔼 hs hadapt t T) ω
    simp only [Pi.add_apply] at this
    rw [Finset.sum_apply] at this
    linarith
  simp_rw [hp]
  have hshift : Tendsto (fun T => 𝔼.E t (s T) ω) atTop (𝓝 0) ↔
      Tendsto (fun T => 𝔼.E t (s (t + T)) ω) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat t]
    simp only [add_comm]
  rw [hshift]
  constructor
  · intro h
    have := (tendsto_const_nhds (x := s t ω)).sub h
    simpa using this
  · intro h
    have := (tendsto_const_nhds (x := s t ω)).sub h
    simpa using this

/-- Galí (2015), eq. (20), p. 232 (**forward solution**): under (14), (18) and the
**hypothesis** `lim_{T→∞} E_t s_T = 0` (fn. 5; not derived), the terms of trade equal the
limit of the partial sums of expected real-rate differentials,
`s_t = lim_T Σ_{k<T} E_t[(i*_{t+k} − π*_{t+k+1}) − (i_{t+k} − π_{H,t+k+1})]`.
(The book writes `E_t Σ_k`; the statement is the sum of conditional expectations, which needs
no interchange of `E_t` and an infinite sum.) -/
theorem tot_forward {s e ps pH i is : ℕ → Ω → ℝ}
    (h14 : ∀ t ω, s t ω = e t ω + ps t ω - pH t ω)
    (h18 : ∀ t ω, i t ω = is t ω + (𝔼.E t (e (t + 1)) ω - e t ω))
    (hps : ∀ t, 𝔼.E t (ps t) = ps t) (hpH : ∀ t, 𝔼.E t (pH t) = pH t)
    (hs : ∀ t, 𝔼.E t (s t) = s t) (t : ℕ) (ω : Ω)
    (hlim : Tendsto (fun T => 𝔼.E t (s T) ω) atTop (𝓝 0)) :
    Tendsto (fun T => ∑ k ∈ Finset.range T, 𝔼.E t (fun ω' =>
        (is (t + k) ω' - (ps (t + k + 1) ω' - ps (t + k) ω'))
          - (i (t + k) ω' - (pH (t + k + 1) ω' - pH (t + k) ω'))) ω)
      atTop (𝓝 (s t ω)) := by
  set d : ℕ → Ω → ℝ := fun u ω' => (is u ω' - 𝔼.E u (ps (u + 1) - ps u) ω')
    - (i u ω' - 𝔼.E u (pH (u + 1) - pH u) ω') with hd
  have hrec : ∀ u, s u = d u + 𝔼.E u (s (u + 1)) := fun u => by
    funext ω'
    rw [Pi.add_apply, tot_difference 𝔼 u h14 (h18 u) (hps u) (hpH u) ω']
  have hEd : ∀ k, 𝔼.E t (d (t + k)) = 𝔼.E t (fun ω' =>
      (is (t + k) ω' - (ps (t + k + 1) ω' - ps (t + k) ω'))
        - (i (t + k) ω' - (pH (t + k + 1) ω' - pH (t + k) ω'))) := by
    intro k
    have hle : t ≤ t + k := Nat.le_add_right t k
    have e1 : d (t + k) = is (t + k) - 𝔼.E (t + k) (ps (t + k + 1) - ps (t + k))
        - (i (t + k) - 𝔼.E (t + k) (pH (t + k + 1) - pH (t + k))) := rfl
    have e2 : (fun ω' => (is (t + k) ω' - (ps (t + k + 1) ω' - ps (t + k) ω'))
        - (i (t + k) ω' - (pH (t + k + 1) ω' - pH (t + k) ω')))
        = is (t + k) - (ps (t + k + 1) - ps (t + k))
          - (i (t + k) - (pH (t + k + 1) - pH (t + k))) := rfl
    rw [e1, e2]
    simp only [map_sub, 𝔼.tower hle]
  have := (forward_iff 𝔼 hrec hs t ω).2 hlim
  simpa only [hEd] using this

/-- Galí (2015), eq. (20) and fn. 5: **the limit hypothesis cannot be dropped**. Under perfect
foresight `s ≡ 1`, `d ≡ 0` satisfies `s_t = d_t + E_t s_{t+1}`, yet the forward sums (all zero)
do not converge to `s_0 = 1`. -/
theorem forward_counterexample :
    (∀ t, (fun _ _ => (1 : ℝ)) t = (fun _ _ => (0 : ℝ)) t +
        perfectForesight.E t ((fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) (t + 1))) ∧
      ¬ Tendsto (fun T => ∑ k ∈ Finset.range T,
          perfectForesight.E 0 ((fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) (0 + k)) ()) atTop
        (𝓝 1) := by
  refine ⟨fun t => by funext ω; simp [perfectForesight], fun h => ?_⟩
  have h0 : Tendsto (fun T => ∑ k ∈ Finset.range T,
      perfectForesight.E 0 ((fun (_ : ℕ) (_ : Unit) => (0 : ℝ)) (0 + k)) ()) atTop (𝓝 0) := by
    simp [perfectForesight]
  exact one_ne_zero (tendsto_nhds_unique h h0)

/-! ### Eq. (19) is not an independent equilibrium condition (p. 232) -/

/-- Galí (2015), p. 232: **(19) is implied by** the domestic Euler equation (11) (with CPI
inflation), the world Euler equation, the risk-sharing condition (17), the CPI identity (13)
and the AR(1) law `E_t z_{t+1} = ρ_z z_t` (`σ ≠ 0`; `s` known at `t`). -/
theorem tot_difference_of_eulers {σ υ ρ ρz : ℝ} (hσ : σ ≠ 0)
    {c ys z s i is p pH ps : ℕ → Ω → ℝ} (t : ℕ)
    (h11 : ∀ ω, c t ω = 𝔼.E t (c (t + 1)) ω
      - 1 / σ * (i t ω - 𝔼.E t (p (t + 1) - p t) ω - ρ) + (1 - ρz) / σ * z t ω)
    (hW : ∀ ω, ys t ω = 𝔼.E t (ys (t + 1)) ω
      - 1 / σ * (is t ω - 𝔼.E t (ps (t + 1) - ps t) ω - ρ))
    (h17 : ∀ u ω, c u ω = ys u ω + 1 / σ * z u ω + (1 - υ) / σ * s u ω)
    (h13 : ∀ ω, p (t + 1) ω - p t ω = (pH (t + 1) ω - pH t ω) + υ * (s (t + 1) ω - s t ω))
    (hz : 𝔼.E t (z (t + 1)) = ρz • z t) (hs : 𝔼.E t (s t) = s t) (ω : Ω) :
    s t ω = (is t ω - 𝔼.E t (ps (t + 1) - ps t) ω) - (i t ω - 𝔼.E t (pH (t + 1) - pH t) ω)
      + 𝔼.E t (s (t + 1)) ω := by
  have hc1 : c (t + 1) = ys (t + 1) + (1 / σ) • z (t + 1) + ((1 - υ) / σ) • s (t + 1) :=
    funext fun ω => by simp [h17 (t + 1) ω, smul_eq_mul]
  have hp1 : p (t + 1) - p t = (pH (t + 1) - pH t) + υ • (s (t + 1) - s t) :=
    funext fun ω => by simp [h13 ω, smul_eq_mul]
  have e4 : 𝔼.E t (c (t + 1)) ω = 𝔼.E t (ys (t + 1)) ω + 1 / σ * 𝔼.E t (z (t + 1)) ω
      + (1 - υ) / σ * 𝔼.E t (s (t + 1)) ω := by
    rw [hc1, map_add, map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  have e6 : 𝔼.E t (p (t + 1) - p t) ω = 𝔼.E t (pH (t + 1) - pH t) ω
      + υ * (𝔼.E t (s (t + 1)) ω - s t ω) := by
    rw [hp1, map_add, map_smul, map_sub (𝔼.E t) (s (t + 1)) (s t), hs]
    simp [smul_eq_mul]
  have e5 : 𝔼.E t (z (t + 1)) ω = ρz * z t ω := by rw [hz]; simp [smul_eq_mul]
  have e1 := h11 ω
  have e2 := hW ω
  have e3 := h17 t ω
  linear_combination (norm := skip) σ * e1 - σ * e2 - σ * e3 + σ * e4 + e5 + e6
  field_simp
  ring

end Gali.OpenEconomy.UIP
