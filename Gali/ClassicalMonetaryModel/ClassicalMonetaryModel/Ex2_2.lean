/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.Expectations

/-!
# Exercise 2.2: alternative interest rules for the classical economy

Galí (2015), Chapter 2, Exercise 2.2, pp. 46–47. Output `y_t` and the real rate
`r_t ≡ i_t − E_t π_{t+1} = ρ + σ E_t Δy_{t+1}` are determined independently of monetary policy
(§2.3, pp. 23–24), so they are taken as exogenous bounded adapted processes. The equilibrium
conditions used are the Fisher equation `i_t = r_t + E_t π_{t+1}` (`Fisher`, in price form
`i_t = r_t + E_t p_{t+1} − p_t`, `FisherP`) and the money demand
`m_t − p_t = y_t − η i_t + ε^m_t`.

## a. Strict inflation targeting

* (i) `strictIT_solves`: under `i_t = r_t + π* + φ_π(π_t − π*)` the path `π_t ≡ π*` is an
  equilibrium; `strictIT_unique`: for `|φ_π| > 1` it is the only bounded one, so this rule
  guarantees full stabilisation. The plain rule `i_t = r_t + π*` (`φ_π = 0`) does not:
  `strictIT_not_unique` gives a second bounded equilibrium whenever `|φ_π| ≤ 1`, and
  `strictIT_sunspot` shows that `π* + ξ` is an equilibrium for every martingale-difference `ξ`
  when `φ_π = 0`.
* (ii) `strictIT_money_growth`: the money growth this requires,
  `Δm_t = π* + Δy_t − η Δr_t + Δε^m_t`.
* (iii) `constMoneyGrowth_inflation`: under `Δm_t = π*`,
  `π_t = π* − Δy_t + η Δi_t − Δε^m_t`; `constMoneyGrowth_not_stabilising`: unless
  `y − η r + ε^m` happens to be constant over time, inflation is not stabilised.

## b. Price-level targeting

* (i) Rule `i_t = ρ + π* + φ_p (p_t − p*_t)`, `p*_t = p*_0 + π* t`, `φ_p > 0`.
  `plEquilibrium_iff`: in terms of `p̂_t = p_t − p*_t` the equilibrium is
  `p̂_t = (1 + φ_p)^{−1} E_t p̂_{t+1} + (1 + φ_p)^{−1} r̂_t`, `r̂_t = r_t − ρ`.
  `plEquilibrium_unique_iff`: among price paths with `p − p*` bounded the equilibrium is
  unique, `p̂_t = ∑_{k ≥ 0} (1 + φ_p)^{−(k+1)} E_t r̂_{t+k}`; `plEquilibrium_exists`: it exists.
  `pl_ar1`: for AR(1) `r̂`, `p̂_t = r̂_t/(1 + φ_p − ρ_r)`.
  `hint_constant_target_unbounded` (erratum C2-7): the hint's `p_t − p*` with a constant `p*`
  is unbounded when `π* ≠ 0`; the deviation must be taken from the time-varying `p*_t`.
* (ii) Money rule `Δm_t = π*`, `m_0 = p*_0`, so `m_t = p*_t` (`moneyPath_eq_pstar`).
  `moneyEquilibrium_iff`: `p̂_t = (η/(1+η)) E_t p̂_{t+1} + u_t` with
  `u_t = (η(r_t + π*) − y_t − ε^m_t)/(1 + η)`; `moneyEquilibrium_unique_iff`,
  `moneyEquilibrium_exists`: the unique equilibrium is the forward series (`η ≥ 0`).
* (iii) `moneyRule_as_interestRule`: money market clearing with `m_t = p*_t` is exactly the
  interest rule `i_t = ψ (p_t − p*_t) + u_t` with `ψ = 1/η`, `u_t = (y_t + ε^m_t)/η`;
  `moneyEquilibrium_iff_interestRule`: the two regimes have the same equilibria.
* (iv) is a verbal discussion and is not formalised.
-/

namespace Gali.ClassicalMonetaryModel.Ex2_2

open Filter Topology

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### General lemmas -/

/-- Galí (2015), p. 25 (expectations of a known constant): `E_t (x − c) = E_t x − c`. -/
theorem E_sub_const (t : ℕ) (x : Ω → ℝ) (c : ℝ) :
    𝔼.E t (fun ω => x ω - c) = fun ω => 𝔼.E t x ω - c := by
  have h : (fun ω => x ω - c) = x - fun _ => c := rfl
  rw [h, map_sub, 𝔼.const]
  rfl

/-- Galí (2015), (25) p. 27 and (28) p. 29: the forward series of a bounded adapted forcing
process is itself adapted (it is known at the date it refers to). -/
theorem forwardSeries_adapted {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {u : ℕ → Ω → ℝ}
    (hu : ∀ t ω, |u t ω| ≤ M) (hadapt : 𝔼.Adapted u) : 𝔼.Adapted (𝔼.forwardSeries a u) := by
  intro t
  have h := 𝔼.forwardSeries_solves ha0 ha1 hu hadapt t
  conv_lhs => rw [h]
  rw [map_add, map_smul, 𝔼.E_E_self, hadapt t, ← h]

/-- Galí (2015), (25) p. 27: the forward series of `a u` is
`∑_{k ≥ 0} a^{k+1} E_t u_{t+k}`. -/
theorem forwardSeries_smul_apply (a : ℝ) (u : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun t => a • u t) t ω = ∑' k, a ^ (k + 1) * 𝔼.E t (u (t + k)) ω := by
  unfold ExpectationSystem.forwardSeries
  refine tsum_congr fun k => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, pow_succ]
  ring

/-! ### a. Strict inflation targeting -/

/-- Galí (2015), Exercise 2.2, p. 46: the Fisher equation `i_t = r_t + E_t π_{t+1}`
(definition of the real rate). -/
def Fisher (r i infl : ℕ → Ω → ℝ) : Prop := ∀ t, i t = r t + 𝔼.E t (infl (t + 1))

/-- Galí (2015), Exercise 2.2(a)(i), p. 46: the strict inflation-targeting rule
`i_t = r_t + π* + φ_π (π_t − π*)`. -/
def StrictITRule (φπ πstar : ℝ) (r i infl : ℕ → Ω → ℝ) : Prop :=
  ∀ t ω, i t ω = r t ω + πstar + φπ * (infl t ω - πstar)

/-- Galí (2015), Exercise 2.2(a)(i), p. 46: under the rule `i_t = r_t + π* + φ_π(π_t − π*)`
the constant path `π_t = π*`, `i_t = r_t + π*` is an equilibrium (for every `φ_π`). -/
theorem strictIT_solves (φπ πstar : ℝ) (r : ℕ → Ω → ℝ) :
    Fisher 𝔼 r (fun t ω => r t ω + πstar) (fun _ _ => πstar) ∧
      StrictITRule φπ πstar r (fun t ω => r t ω + πstar) (fun _ _ => πstar) := by
  refine ⟨fun t => ?_, fun t ω => by ring⟩
  rw [𝔼.const]
  rfl

/-- Galí (2015), Exercise 2.2(a)(i), p. 46 (**full stabilisation**): with `|φ_π| > 1` every
bounded equilibrium under the rule `i_t = r_t + π* + φ_π(π_t − π*)` has `π_t = π*`. -/
theorem strictIT_unique {φπ πstar : ℝ} (hφ : 1 < |φπ|) {r i infl : ℕ → Ω → ℝ}
    (hfis : Fisher 𝔼 r i infl) (hrule : StrictITRule φπ πstar r i infl)
    (hb : BoundedProc infl) : ∀ t ω, infl t ω = πstar := by
  have hφ0 : φπ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hφ
    linarith
  set z : ℕ → Ω → ℝ := fun t ω => infl t ω - πstar with hz
  have hzeq : ∀ t, z t = φπ⁻¹ • 𝔼.E t (z (t + 1)) + 0 := by
    intro t
    funext ω
    have h1 := congrFun (hfis t) ω
    have h2 := hrule t ω
    have hE : 𝔼.E t (z (t + 1)) ω = 𝔼.E t (infl (t + 1)) ω - πstar :=
      congrFun (E_sub_const 𝔼 t (infl (t + 1)) πstar) ω
    change infl t ω - πstar = φπ⁻¹ * 𝔼.E t (z (t + 1)) ω + 0
    rw [hE]
    simp only [Pi.add_apply] at h1
    field_simp
    linarith
  have h0 : ∀ t, (0 : ℕ → Ω → ℝ) t = φπ⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 := by
    intro t
    simp
  have ha : |φπ⁻¹| < 1 := by
    rw [abs_inv]
    exact inv_lt_one_of_one_lt₀ hφ
  obtain ⟨M, hM⟩ := hb
  have hzb : BoundedProc z := ⟨M + |πstar|, fun t ω => (abs_sub _ _).trans (by linarith [hM t ω])⟩
  have := 𝔼.forward_unique ha hzeq h0 hzb ⟨0, fun t ω => by simp⟩
  intro t ω
  have h := congrFun (congrFun this t) ω
  simp only [hz, Pi.zero_apply] at h
  linarith

/-- Galí (2015), Exercise 2.2(a)(i), p. 46 (**the rule `i_t = r_t + π*` does not guarantee
stabilisation**): for `|φ_π| ≤ 1` the deterministic path `π_t = π* + φ_πᵗ` is a second bounded
equilibrium, different from `π_t ≡ π*`. -/
theorem strictIT_not_unique [Nonempty Ω] {φπ : ℝ} (hφ : |φπ| ≤ 1) (πstar : ℝ)
    (r : ℕ → Ω → ℝ) :
    Fisher 𝔼 r (fun t ω => r t ω + πstar + φπ * φπ ^ t) (fun t _ => πstar + φπ ^ t) ∧
      StrictITRule φπ πstar r (fun t ω => r t ω + πstar + φπ * φπ ^ t)
        (fun t _ => πstar + φπ ^ t) ∧
      BoundedProc (fun t (_ : Ω) => πstar + φπ ^ t) ∧
      𝔼.Adapted (fun t (_ : Ω) => πstar + φπ ^ t) ∧
      (fun t (_ : Ω) => πstar + φπ ^ t) ≠ fun _ _ => πstar := by
  refine ⟨fun t => ?_, fun t ω => by ring, ⟨|πstar| + 1, fun t ω => ?_⟩,
    fun t => 𝔼.const t _, fun h => ?_⟩
  · rw [𝔼.const]
    funext ω
    simp only [Pi.add_apply]
    ring
  · refine (abs_add_le _ _).trans ?_
    rw [abs_pow]
    linarith [pow_le_one₀ (abs_nonneg φπ) hφ (n := t)]
  · have := congrFun (congrFun h 0) (Classical.arbitrary Ω)
    simp at this

/-- Galí (2015), Exercise 2.2(a)(i) and §2.4.1, pp. 25–26 (**sunspots** under
`i_t = r_t + π*`): for every bounded adapted `ξ` with `E_t ξ_{t+1} = 0`, the path
`π_t = π* + ξ_t` is an equilibrium of the rule with `φ_π = 0`. -/
theorem strictIT_sunspot (πstar : ℝ) (r ξ : ℕ → Ω → ℝ) (hξ : ∀ t, 𝔼.E t (ξ (t + 1)) = 0) :
    Fisher 𝔼 r (fun t ω => r t ω + πstar) (fun t ω => πstar + ξ t ω) ∧
      StrictITRule 0 πstar r (fun t ω => r t ω + πstar) (fun t ω => πstar + ξ t ω) := by
  refine ⟨fun t => ?_, fun t ω => by ring⟩
  have h : (fun ω => πstar + ξ (t + 1) ω) = (fun _ => πstar) + ξ (t + 1) := rfl
  change (fun ω => r t ω + πstar) = r t + 𝔼.E t (fun ω => πstar + ξ (t + 1) ω)
  rw [h, map_add, 𝔼.const, hξ t]
  funext ω
  simp

/-- Galí (2015), Exercise 2.2(a)(ii), p. 46: with `π_t ≡ π*` (so `p_{t+1} = p_t + π*`) and
`i_t = r_t + π*`, money demand `m_t = p_t + y_t − η i_t + ε^m_t` implies
`Δm_{t+1} = π* + Δy_{t+1} − η Δr_{t+1} + Δε^m_{t+1}`. -/
theorem strictIT_money_growth {η πstar : ℝ} {r y ε p m i : ℕ → Ω → ℝ}
    (hp : ∀ t ω, p (t + 1) ω = p t ω + πstar) (hi : ∀ t ω, i t ω = r t ω + πstar)
    (hmd : ∀ t ω, m t ω - p t ω = y t ω - η * i t ω + ε t ω) (t : ℕ) (ω : Ω) :
    m (t + 1) ω - m t ω = πstar + (y (t + 1) ω - y t ω) - η * (r (t + 1) ω - r t ω)
      + (ε (t + 1) ω - ε t ω) := by
  have h1 := hmd t ω
  have h2 := hmd (t + 1) ω
  rw [hi] at h1 h2
  rw [hp] at h2
  linarith

/-- Galí (2015), Exercise 2.2(a)(iii), p. 46: under constant money growth `Δm_t = π*`, money
demand gives `π_{t+1} = π* − Δy_{t+1} + η Δi_{t+1} − Δε^m_{t+1}`, where
`π_{t+1} = p_{t+1} − p_t`. -/
theorem constMoneyGrowth_inflation {η πstar : ℝ} {y ε p m i : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m (t + 1) ω - m t ω = πstar)
    (hmd : ∀ t ω, m t ω - p t ω = y t ω - η * i t ω + ε t ω) (t : ℕ) (ω : Ω) :
    p (t + 1) ω - p t ω = πstar - (y (t + 1) ω - y t ω) + η * (i (t + 1) ω - i t ω)
      - (ε (t + 1) ω - ε t ω) := by
  have h1 := hmd t ω
  have h2 := hmd (t + 1) ω
  have h3 := hm t ω
  linarith

/-- Galí (2015), Exercise 2.2(a)(iii), p. 46 (**why constant money growth fails**): if under
`Δm_t = π*` inflation were constant at `π*` (with the Fisher equation, so `i_t = r_t + π*`),
then `y_t − η r_t + ε^m_t` would be constant over time. Hence whenever
`Δy_{t+1} − η Δr_{t+1} + Δε^m_{t+1} ≠ 0` at some date and state, inflation is not stabilised. -/
theorem constMoneyGrowth_not_stabilising {η πstar : ℝ} {r y ε p m i : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m (t + 1) ω - m t ω = πstar)
    (hmd : ∀ t ω, m t ω - p t ω = y t ω - η * i t ω + ε t ω)
    (hfis : ∀ t ω, i t ω = r t ω + 𝔼.E t (fun ω' => p (t + 1) ω' - p t ω') ω)
    {t : ℕ} {ω : Ω}
    (hshock : (y (t + 1) ω - y t ω) - η * (r (t + 1) ω - r t ω) + (ε (t + 1) ω - ε t ω) ≠ 0) :
    ¬ ∀ s ω', p (s + 1) ω' - p s ω' = πstar := by
  intro hπ
  have hi : ∀ s ω', i s ω' = r s ω' + πstar := by
    intro s ω'
    rw [hfis s ω']
    have : (fun ω' => p (s + 1) ω' - p s ω') = fun _ => πstar := funext fun ω' => hπ s ω'
    rw [this, 𝔼.const]
  have h := constMoneyGrowth_inflation hm hmd t ω
  rw [hπ t ω, hi, hi] at h
  apply hshock
  linarith

/-! ### b(i). Price-level targeting through an interest rule -/

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: the price-level target `p*_t = p*_0 + π* t`. -/
def pstar (p0 πstar : ℝ) (t : ℕ) : ℝ := p0 + πstar * t

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: the target grows at rate `π*`. -/
theorem pstar_succ (p0 πstar : ℝ) (t : ℕ) :
    pstar p0 πstar (t + 1) = pstar p0 πstar t + πstar := by
  simp only [pstar]
  push_cast
  ring

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: the deviation of the price level from target,
`p̂_t = p_t − p*_t`. -/
def devPL (p0 πstar : ℝ) (p : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => p t ω - pstar p0 πstar t

/-- Galí (2015), Exercise 2.2, p. 46: the Fisher equation in price form,
`i_t = r_t + E_t p_{t+1} − p_t`. -/
def FisherP (r p i : ℕ → Ω → ℝ) : Prop := ∀ t, i t = r t + 𝔼.E t (p (t + 1)) - p t

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: equilibrium under the price-level rule
`i_t = ρ + π* + φ_p (p_t − p*_t)`. -/
def PLEquilibrium (φp ρ πstar p0 : ℝ) (r p i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, i t ω = ρ + πstar + φp * devPL p0 πstar p t ω) ∧ FisherP 𝔼 r p i

/-- Galí (2015), Exercise 2.2(b)(i), p. 47: `E_t p̂_{t+1} = E_t p_{t+1} − p*_{t+1}`. -/
theorem E_devPL (p0 πstar : ℝ) (p : ℕ → Ω → ℝ) (t s : ℕ) (ω : Ω) :
    𝔼.E t (devPL p0 πstar p s) ω = 𝔼.E t (p s) ω - pstar p0 πstar s := by
  have := congrFun (E_sub_const 𝔼 t (p s) (pstar p0 πstar s)) ω
  exact this

/-- Galí (2015), Exercise 2.2(b)(i), p. 47 (**reduced form**): for `φ_p > −1`, the equilibrium
conditions under the price-level rule are equivalent to the rule together with
`p̂_t = (1 + φ_p)^{−1} E_t p̂_{t+1} + (1 + φ_p)^{−1} (r_t − ρ)`. -/
theorem plEquilibrium_iff {φp ρ πstar p0 : ℝ} (hφ : 0 < 1 + φp) (r p i : ℕ → Ω → ℝ) :
    PLEquilibrium 𝔼 φp ρ πstar p0 r p i ↔
      (∀ t ω, i t ω = ρ + πstar + φp * devPL p0 πstar p t ω) ∧
      ∀ t, devPL p0 πstar p t = (1 + φp)⁻¹ • 𝔼.E t (devPL p0 πstar p (t + 1))
        + (1 + φp)⁻¹ • fun ω => r t ω - ρ := by
  unfold PLEquilibrium FisherP
  refine and_congr_right fun hrule => forall_congr' fun t => ?_
  rw [funext_iff, funext_iff]
  refine forall_congr' fun ω => ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, E_devPL, pstar_succ]
  rw [hrule t ω]
  simp only [devPL]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- Galí (2015), Exercise 2.2(b)(i), p. 47 (**the unique equilibrium price level**): for
`φ_p > 0`, bounded adapted `r̂_t = r_t − ρ`, and an adapted price path with `p − p*` bounded,
the economy is in equilibrium iff `i` follows the rule and
`p_t − p*_t = ∑_{k ≥ 0} (1 + φ_p)^{−(k+1)} E_t r̂_{t+k}`. -/
theorem plEquilibrium_unique_iff {φp ρ πstar p0 M : ℝ} (hφ : 0 < φp) {r p i : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω - ρ| ≤ M) (hra : 𝔼.Adapted r) (hpb : BoundedProc (devPL p0 πstar p)) :
    PLEquilibrium 𝔼 φp ρ πstar p0 r p i ↔
      (∀ t ω, i t ω = ρ + πstar + φp * devPL p0 πstar p t ω) ∧
      ∀ t ω, devPL p0 πstar p t ω
        = ∑' k, ((1 + φp)⁻¹) ^ (k + 1) * 𝔼.E t (fun ω' => r (t + k) ω' - ρ) ω := by
  set a := (1 + φp)⁻¹ with ha
  have h1 : 0 < 1 + φp := by linarith
  have ha0 : 0 ≤ a := inv_nonneg.2 h1.le
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  set rh : ℕ → Ω → ℝ := fun t ω => r t ω - ρ with hrh
  have hrha : 𝔼.Adapted rh := fun t => by
    rw [hrh]
    simp only
    rw [E_sub_const, hra t]
  have hu : ∀ t ω, |(fun t => a • rh t) t ω| ≤ a * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hr t ω) ha0
  have hua : 𝔼.Adapted (fun t => a • rh t) := fun t => by rw [map_smul, hrha t]
  rw [plEquilibrium_iff 𝔼 h1]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h t ω
    have heq := 𝔼.eq_forwardSeries ha0 ha1 hu hua h hpb
    rw [heq, forwardSeries_smul_apply]
  · intro h t
    have heq : devPL p0 πstar p = 𝔼.forwardSeries a (fun t => a • rh t) := by
      funext s ω
      rw [h s ω, forwardSeries_smul_apply]
    rw [heq]
    exact 𝔼.forwardSeries_solves ha0 ha1 hu hua t

/-- Galí (2015), Exercise 2.2(b)(i), p. 47 (**existence**): for `φ_p > 0` and bounded adapted
`r̂`, the price path `p_t = p*_t + ∑_{k ≥ 0} (1 + φ_p)^{−(k+1)} E_t r̂_{t+k}` with `i` given by
the rule is an equilibrium, adapted, with `p − p*` bounded. -/
theorem plEquilibrium_exists {φp ρ πstar p0 M : ℝ} (hφ : 0 < φp) {r : ℕ → Ω → ℝ}
    (hr : ∀ t ω, |r t ω - ρ| ≤ M) (hra : 𝔼.Adapted r) :
    ∃ p i : ℕ → Ω → ℝ, PLEquilibrium 𝔼 φp ρ πstar p0 r p i ∧ 𝔼.Adapted p ∧ 𝔼.Adapted i ∧
      BoundedProc (devPL p0 πstar p) := by
  set a := (1 + φp)⁻¹ with ha
  have h1 : 0 < 1 + φp := by linarith
  have ha0 : 0 ≤ a := inv_nonneg.2 h1.le
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  set rh : ℕ → Ω → ℝ := fun t ω => r t ω - ρ with hrh
  have hrha : 𝔼.Adapted rh := fun t => by
    rw [hrh]
    simp only
    rw [E_sub_const, hra t]
  have hu : ∀ t ω, |(fun t => a • rh t) t ω| ≤ a * M := fun t ω => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (hr t ω) ha0
  have hua : 𝔼.Adapted (fun t => a • rh t) := fun t => by rw [map_smul, hrha t]
  set F := 𝔼.forwardSeries a (fun t => a • rh t) with hF
  have hFa := forwardSeries_adapted 𝔼 ha0 ha1 hu hua
  set p : ℕ → Ω → ℝ := fun t ω => pstar p0 πstar t + F t ω with hp
  have hdev : devPL p0 πstar p = F := by
    funext t ω
    simp [devPL, hp]
  refine ⟨p, fun t ω => ρ + πstar + φp * devPL p0 πstar p t ω, ?_, ?_, ?_, ?_⟩
  · rw [plEquilibrium_iff 𝔼 h1]
    refine ⟨fun t ω => rfl, fun t => ?_⟩
    rw [hdev]
    exact 𝔼.forwardSeries_solves ha0 ha1 hu hua t
  · intro t
    have : p t = (fun _ => pstar p0 πstar t) + F t := rfl
    rw [this, map_add, 𝔼.const, hFa t]
  · intro t
    have : (fun ω => ρ + πstar + φp * devPL p0 πstar p t ω)
        = (fun _ => ρ + πstar) + φp • F t := by
      funext ω
      simp [hdev]
    change 𝔼.E t (fun ω => ρ + πstar + φp * devPL p0 πstar p t ω)
      = fun ω => ρ + πstar + φp * devPL p0 πstar p t ω
    rw [this, map_add, map_smul, 𝔼.const, hFa t]
  · rw [hdev]
    exact 𝔼.forwardSeries_bounded ha0 ha1 hu

/-- Galí (2015), Exercise 2.2(b)(i), p. 47 (**AR(1) real rate**): if `r̂_t = r_t − ρ` is a
bounded AR(1) process with persistence `ρ_r`, `|ρ_r| ≤ 1`, the unique bounded equilibrium
deviation from target is `p̂_t = r̂_t/(1 + φ_p − ρ_r)`. -/
theorem pl_ar1 {φp ρ πstar p0 ρr : ℝ} (hφ : 0 < φp) (hρr : |ρr| ≤ 1) {r p i : ℕ → Ω → ℝ}
    (har : 𝔼.IsAR1 ρr (fun t ω => r t ω - ρ)) (hrb : BoundedProc fun t ω => r t ω - ρ)
    (hpb : BoundedProc (devPL p0 πstar p)) (heq : PLEquilibrium 𝔼 φp ρ πstar p0 r p i)
    (t : ℕ) (ω : Ω) :
    devPL p0 πstar p t ω = (r t ω - ρ) / (1 + φp - ρr) := by
  set a := (1 + φp)⁻¹ with ha
  have h1 : 0 < 1 + φp := by linarith
  have ha0 : 0 ≤ a := inv_nonneg.2 h1.le
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hρ1 : ρr ≤ 1 := (le_abs_self ρr).trans hρr
  have hden : 0 < 1 + φp - ρr := by linarith
  set rh : ℕ → Ω → ℝ := fun t ω => r t ω - ρ with hrh
  have har' : 𝔼.IsAR1 ρr (fun t => a • rh t) :=
    ⟨fun t => by rw [map_smul, har.1 t], fun t => by rw [map_smul, har.2 t, smul_comm]⟩
  have h1a : 1 - a * ρr ≠ 0 := by
    have : 1 - a * ρr = (1 + φp - ρr) / (1 + φp) := by
      rw [ha]
      field_simp
    rw [this]
    exact (div_pos hden h1).ne'
  have hsol := 𝔼.forward_ar1_solves h1a har'
  have h2 := ((plEquilibrium_iff 𝔼 h1 r p i).1 heq).2
  obtain ⟨M, hM⟩ := hrb
  have hb2 : BoundedProc fun t => (1 - a * ρr)⁻¹ • (fun t => a • rh t) t :=
    ⟨|(1 - a * ρr)⁻¹| * (a * M), fun t ω => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ha0]
      gcongr
      exact hM t ω⟩
  have hu := 𝔼.forward_unique (u := fun t => a • rh t) (by rwa [abs_of_nonneg ha0]) h2
    hsol hpb hb2
  rw [hu]
  simp only [Pi.smul_apply, smul_eq_mul, hrh, ha]
  field_simp

/-- Galí (2015), Exercise 2.2(b)(i), p. 47, erratum C2-7: the hint's deviation `p_t − p*`
from a *constant* `p* = p*_0` is unbounded whenever `π* ≠ 0` and `p − p*_t` is bounded, so it
cannot serve as the stationary variable of the forward solution; the deviation must be taken
from the time-varying target `p*_t = p*_0 + π* t` (1st-edition leftover, see survey §6). -/
theorem hint_constant_target_unbounded [Nonempty Ω] {πstar p0 : ℝ} (hπ : πstar ≠ 0)
    {p : ℕ → Ω → ℝ} (hpb : BoundedProc (devPL p0 πstar p)) :
    ¬ BoundedProc (fun t ω => p t ω - p0) := by
  rintro ⟨K, hK⟩
  obtain ⟨M, hM⟩ := hpb
  obtain ⟨n, hn⟩ := exists_nat_gt ((K + M) / |πstar|)
  have hpos : 0 < |πstar| := abs_pos.2 hπ
  set ω := Classical.arbitrary Ω
  have h1 := hK n ω
  have h2 := hM n ω
  simp only [devPL, pstar] at h2
  have e : πstar * n = (p n ω - p0) - (p n ω - (p0 + πstar * n)) := by ring
  have h3 : |πstar * n| ≤ K + M := by
    rw [e]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  rw [abs_mul, Nat.abs_cast] at h3
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

/-! ### b(ii)–(iii). The money-supply rule -/

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47: `Δm_t = π*` with `m_0 = p*_0` gives `m_t = p*_t`. -/
theorem moneyPath_eq_pstar {p0 πstar : ℝ} {m : ℕ → Ω → ℝ} (h0 : ∀ ω, m 0 ω = p0)
    (hm : ∀ t ω, m (t + 1) ω - m t ω = πstar) : ∀ t ω, m t ω = pstar p0 πstar t := by
  intro t ω
  induction t with
  | zero => simp [h0, pstar]
  | succ t ih =>
    rw [pstar_succ, ← ih]
    linarith [hm t ω]

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47: equilibrium under a money-supply rule: money
market clearing `m_t − p_t = y_t − η i_t + ε^m_t` and the Fisher equation. -/
def MoneyEquilibrium (η : ℝ) (y ε r m p i : ℕ → Ω → ℝ) : Prop :=
  (∀ t ω, m t ω - p t ω = y t ω - η * i t ω + ε t ω) ∧ FisherP 𝔼 r p i

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47: the forcing term
`u_t = (η (r_t + π*) − y_t − ε^m_t)/(1 + η)` of the price-level equation. -/
noncomputable def moneyForcing (η πstar : ℝ) (y ε r : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => (η * (r t ω + πstar) - y t ω - ε t ω) / (1 + η)

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47 (**reduced form**): with `m_t = p*_t` and `η ≥ 0`,
the equilibrium conditions are equivalent to the Fisher equation together with
`p̂_t = (η/(1 + η)) E_t p̂_{t+1} + u_t`. -/
theorem moneyEquilibrium_iff {η p0 πstar : ℝ} (hη : 0 ≤ η) {y ε r m p i : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m t ω = pstar p0 πstar t) :
    MoneyEquilibrium 𝔼 η y ε r m p i ↔ FisherP 𝔼 r p i ∧
      ∀ t, devPL p0 πstar p t = (η / (1 + η)) • 𝔼.E t (devPL p0 πstar p (t + 1))
        + moneyForcing η πstar y ε r t := by
  unfold MoneyEquilibrium
  rw [and_comm]
  refine and_congr_right fun hfis => ?_
  have h1 : 0 < 1 + η := by linarith
  constructor
  · intro hmd t
    funext ω
    have h2 := hmd t ω
    have h3 := congrFun (hfis t) ω
    simp only [Pi.add_apply, Pi.sub_apply] at h3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, E_devPL, pstar_succ, moneyForcing,
      devPL]
    rw [hm, h3] at h2
    field_simp
    linarith
  · intro hd t ω
    have h2 := congrFun (hd t) ω
    have h3 := congrFun (hfis t) ω
    simp only [Pi.add_apply, Pi.sub_apply] at h3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, E_devPL, pstar_succ, moneyForcing,
      devPL] at h2
    rw [hm, h3]
    field_simp at h2
    linarith

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47 (**the unique equilibrium price level under the
money rule**): for `η ≥ 0`, bounded adapted `y`, `ε^m`, `r`, and an adapted price path with
`p − p*` bounded, the economy is in equilibrium iff the Fisher equation holds and
`p_t − p*_t = ∑_{k ≥ 0} (η/(1+η))ᵏ E_t u_{t+k}`. -/
theorem moneyEquilibrium_unique_iff {η p0 πstar M : ℝ} (hη : 0 ≤ η)
    {y ε r m p i : ℕ → Ω → ℝ} (hm : ∀ t ω, m t ω = pstar p0 πstar t)
    (hu : ∀ t ω, |moneyForcing η πstar y ε r t ω| ≤ M)
    (hua : 𝔼.Adapted (moneyForcing η πstar y ε r)) (hpb : BoundedProc (devPL p0 πstar p)) :
    MoneyEquilibrium 𝔼 η y ε r m p i ↔ FisherP 𝔼 r p i ∧
      devPL p0 πstar p = 𝔼.forwardSeries (η / (1 + η)) (moneyForcing η πstar y ε r) := by
  have h1 : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ η / (1 + η) := div_nonneg hη h1.le
  have ha1 : η / (1 + η) < 1 := (div_lt_one h1).2 (by linarith)
  rw [moneyEquilibrium_iff 𝔼 hη hm]
  refine and_congr_right fun _ => ⟨fun h => 𝔼.eq_forwardSeries ha0 ha1 hu hua h hpb,
    fun h t => ?_⟩
  rw [h]
  exact 𝔼.forwardSeries_solves ha0 ha1 hu hua t

/-- Galí (2015), Exercise 2.2(b)(ii), p. 47 (**existence**): with `m_t = p*_t`, `η ≥ 0` and
bounded adapted forcing, `p_t = p*_t + ∑_{k ≥ 0} (η/(1+η))ᵏ E_t u_{t+k}` and `i` from the
Fisher equation form an equilibrium with `p` adapted and `p − p*` bounded. -/
theorem moneyEquilibrium_exists {η p0 πstar M : ℝ} (hη : 0 ≤ η) {y ε r m : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m t ω = pstar p0 πstar t) (hu : ∀ t ω, |moneyForcing η πstar y ε r t ω| ≤ M)
    (hua : 𝔼.Adapted (moneyForcing η πstar y ε r)) :
    ∃ p i : ℕ → Ω → ℝ, MoneyEquilibrium 𝔼 η y ε r m p i ∧ 𝔼.Adapted p ∧
      BoundedProc (devPL p0 πstar p) := by
  have h1 : 0 < 1 + η := by linarith
  have ha0 : 0 ≤ η / (1 + η) := div_nonneg hη h1.le
  have ha1 : η / (1 + η) < 1 := (div_lt_one h1).2 (by linarith)
  set F := 𝔼.forwardSeries (η / (1 + η)) (moneyForcing η πstar y ε r) with hF
  have hFa := forwardSeries_adapted 𝔼 ha0 ha1 hu hua
  set p : ℕ → Ω → ℝ := fun t ω => pstar p0 πstar t + F t ω with hp
  have hdev : devPL p0 πstar p = F := by
    funext t ω
    simp [devPL, hp]
  refine ⟨p, fun t => r t + 𝔼.E t (p (t + 1)) - p t, ?_, ?_, ?_⟩
  · rw [moneyEquilibrium_iff 𝔼 hη hm]
    refine ⟨fun t => rfl, fun t => ?_⟩
    rw [hdev]
    exact 𝔼.forwardSeries_solves ha0 ha1 hu hua t
  · intro t
    have : p t = (fun _ => pstar p0 πstar t) + F t := rfl
    rw [this, map_add, 𝔼.const, hFa t]
  · rw [hdev]
    exact 𝔼.forwardSeries_bounded ha0 ha1 hu

/-- Galí (2015), Exercise 2.2(b)(iii), p. 47: with `m_t = p*_t` and `η > 0`, money market
clearing `m_t − p_t = y_t − η i_t + ε^m_t` is exactly the price-level interest rule
`i_t = ψ (p_t − p*_t) + u_t` with `ψ = 1/η` and `u_t = (y_t + ε^m_t)/η`. -/
theorem moneyRule_as_interestRule {η p0 πstar : ℝ} (hη : 0 < η) {y ε m p i : ℕ → Ω → ℝ}
    (hm : ∀ t ω, m t ω = pstar p0 πstar t) (t : ℕ) (ω : Ω) :
    m t ω - p t ω = y t ω - η * i t ω + ε t ω ↔
      i t ω = η⁻¹ * devPL p0 πstar p t ω + (y t ω + ε t ω) / η := by
  rw [hm, devPL]
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Galí (2015), Exercise 2.2(b)(iii), p. 47: the money-supply regime (`Δm_t = π*`,
`m_0 = p*_0`) and the interest rule `i_t = (1/η)(p_t − p*_t) + (y_t + ε^m_t)/η` have exactly the
same equilibria. -/
theorem moneyEquilibrium_iff_interestRule {η p0 πstar : ℝ} (hη : 0 < η)
    {y ε r m p i : ℕ → Ω → ℝ} (hm0 : ∀ ω, m 0 ω = p0)
    (hm : ∀ t ω, m (t + 1) ω - m t ω = πstar) :
    MoneyEquilibrium 𝔼 η y ε r m p i ↔
      (∀ t ω, i t ω = η⁻¹ * devPL p0 πstar p t ω + (y t ω + ε t ω) / η) ∧ FisherP 𝔼 r p i := by
  have hmp := moneyPath_eq_pstar hm0 hm
  unfold MoneyEquilibrium
  exact and_congr_left fun _ => forall_congr' fun t => forall_congr' fun ω =>
    moneyRule_as_interestRule hη hmp t ω

end Gali.ClassicalMonetaryModel.Ex2_2
