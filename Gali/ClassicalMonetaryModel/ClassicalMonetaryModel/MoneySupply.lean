/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import ClassicalMonetaryModel.InterestRules

/-!
# An exogenous path for the money supply in the classical model

Galí (2015), Chapter 2, §2.4.3, pp. 28–30. The real block (the real rate `r_t` and output
`y_t`) is exogenous to monetary policy (§2.3) and is taken here as given bounded adapted
processes. The money supply `m_t` is set exogenously by the central bank. All statements
hold for an arbitrary `ExpectationSystem` (perfect foresight or genuine uncertainty).

## Main results

* `eq27_of_model`: money demand (11) with `c_t = y_t` (16) and the Fisherian equation (22)
  imply the price-level equation (27), `p_t = η/(1+η) E_t p_{t+1} + m_t/(1+η) + u_t`, for
  `η ≥ 0`; `fisher_of_eq27` is the converse for `η > 0`.
* `eq28_unique`: for bounded adapted `m`, `u` and `η ≥ 0`, the forward solution (28) is the
  unique bounded solution of (27): the price level is always determined.
* `eq29_unique`: with a (possibly non-stationary) money supply whose growth `Δm_t` is bounded,
  (29) `p_t = m_t + ∑_{k≥1} (η/(1+η))ᵏ E_t Δm_{t+k} + ū_t` is the unique solution of (27) with
  `p_t − m_t` bounded (fn. 8: via `p̃_t = p_t − m_t`, `eq27_iff_tilde`).
* `interest_rate_29`: the p. 29 interest-rate expression.
* AR(1) money growth, p. 30: `ar1_money_equilibrium` —
  `p_t = m_t + ηρ_m/(1+η(1−ρ_m)) Δm_t` and `i_t = ρ_m/(1+η(1−ρ_m)) Δm_t`;
  `ar1_series29` evaluates the series in (29); `hasDerivAt_priceImpactM` etc. give the
  impact responses; `price_overshoots_iff` (overshooting iff `η ρ_m > 0`) and
  `no_liquidity_effect_iff` (the nominal rate rises iff `ρ_m > 0`).
-/

namespace Gali.ClassicalMonetaryModel.MoneySupply

open InterestRules

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### The price-level equation (27) -/

/-- Galí (2015), eq. (11), p. 22, with goods-market clearing `c_t = y_t` (16):
the money demand `m_t − p_t = y_t − η i_t`. -/
def MoneyDemand (η : ℝ) (m p y i : ℕ → Ω → ℝ) : Prop := ∀ t, m t - p t = y t - η • i t

/-- Galí (2015), p. 27: inflation is the change in the (log) price level,
`π_{t+1} = p_{t+1} − p_t`. -/
def InflationId (p infl : ℕ → Ω → ℝ) : Prop := ∀ t, infl (t + 1) = p (t + 1) - p t

/-- Galí (2015), p. 29: the forcing `u_t ≡ (1 + η)^{−1}(η r_t − y_t)` of (27). -/
noncomputable def uDef (η : ℝ) (r y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (1 + η)⁻¹ • (η • r t - y t)

/-- Galí (2015), eq. (27), p. 29: `p_t = η/(1+η) E_t{p_{t+1}} + (1+η)^{−1} m_t + u_t`. -/
def Eq27 (η : ℝ) (p m u : ℕ → Ω → ℝ) : Prop :=
  ∀ t, p t = (η / (1 + η)) • 𝔼.E t (p (t + 1)) + ((1 + η)⁻¹ • m t + u t)

/-- Galí (2015), eq. (27), p. 29 (derivation): for `η ≥ 0`, money demand (11) with (16), the
Fisherian equation (22) and `π_{t+1} = p_{t+1} − p_t` (adapted `p`) imply (27). -/
theorem eq27_of_model {η : ℝ} (hη : 0 ≤ η) {m p y i infl r : ℕ → Ω → ℝ}
    (hmd : MoneyDemand η m p y i) (hF : Fisher 𝔼 i infl r) (hid : InflationId p infl)
    (hp : 𝔼.Adapted p) : Eq27 𝔼 η p m (uDef η r y) := by
  intro t
  have hF' : i t = 𝔼.E t (p (t + 1)) - p t + r t := by rw [hF t, hid t, map_sub, hp t]
  funext ω
  have h1 := congrFun hF' ω
  have h2 := congrFun (hmd t) ω
  simp only [uDef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  have hne : (1 + η) ≠ 0 := by linarith
  have key : (1 + η) * p t ω = η * 𝔼.E t (p (t + 1)) ω + m t ω + (η * r t ω - y t ω) := by
    linear_combination (-1 : ℝ) * h2 + η * h1
  have hpe : p t ω = (1 + η)⁻¹ * ((1 + η) * p t ω) := by field_simp
  rw [hpe, key]
  ring

/-- Galí (2015), eq. (27), p. 29 (converse): for `η > 0`, if the price level satisfies (27)
and the nominal rate clears the money market (11), the Fisherian equation (22) holds. -/
theorem fisher_of_eq27 {η : ℝ} (hη : 0 < η) {m p y i infl r : ℕ → Ω → ℝ}
    (h27 : Eq27 𝔼 η p m (uDef η r y)) (hmd : MoneyDemand η m p y i)
    (hid : InflationId p infl) (hp : 𝔼.Adapted p) : Fisher 𝔼 i infl r := by
  intro t
  rw [hid t, map_sub, hp t]
  funext ω
  have h1 := congrFun (h27 t) ω
  have h2 := congrFun (hmd t) ω
  simp only [uDef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  have hne : (1 + η) ≠ 0 := by linarith
  have key : (1 + η) * p t ω = η * 𝔼.E t (p (t + 1)) ω + m t ω + (η * r t ω - y t ω) := by
    rw [h1]
    field_simp
    ring
  have h3 : η * i t ω = η * (𝔼.E t (p (t + 1)) ω - p t ω + r t ω) := by
    linear_combination h2 + key
  exact mul_left_cancel₀ hη.ne' h3

/-! ### The forward solution (28) -/

/-- Galí (2015), (28) p. 29: the forward series is additive, `∑ aᵏ E_t(c m_{t+k} + u_{t+k})
= c ∑ aᵏ E_t m_{t+k} + ∑ aᵏ E_t u_{t+k}`, for bounded `m`, `u` and `0 ≤ a < 1`. -/
theorem forwardSeries_smul_add {a c M₁ M₂ : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {m u : ℕ → Ω → ℝ} (hm : ∀ t ω, |m t ω| ≤ M₁) (hu : ∀ t ω, |u t ω| ≤ M₂) (t : ℕ) (ω : Ω) :
    𝔼.forwardSeries a (fun s => c • m s + u s) t ω =
      c * 𝔼.forwardSeries a m t ω + 𝔼.forwardSeries a u t ω := by
  have h1 := (𝔼.forwardSeries_summable ha0 ha1 hm t ω).mul_left c
  have h2 := 𝔼.forwardSeries_summable ha0 ha1 hu t ω
  change ∑' k, a ^ k * 𝔼.E t (c • m (t + k) + u (t + k)) ω =
    c * ∑' k, a ^ k * 𝔼.E t (m (t + k)) ω + ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω
  rw [← tsum_mul_left, ← h1.tsum_add h2]
  refine tsum_congr fun k => ?_
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (28), p. 29: `p_t = (1+η)^{−1} ∑_{k≥0} (η/(1+η))ᵏ E_t{m_{t+k}} + ū_t`,
`ū_t = ∑_{k≥0} (η/(1+η))ᵏ E_t{u_{t+k}}`. -/
noncomputable def fwd28 (η : ℝ) (m u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => (1 + η)⁻¹ * 𝔼.forwardSeries (η / (1 + η)) m t ω +
    𝔼.forwardSeries (η / (1 + η)) u t ω

/-- Galí (2015), eq. (27), p. 29: `0 ≤ η/(1+η) < 1` for `η ≥ 0`. -/
theorem coef_bounds {η : ℝ} (hη : 0 ≤ η) : 0 ≤ η / (1 + η) ∧ η / (1 + η) < 1 :=
  ⟨div_nonneg hη (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

/-- Galí (2015), eq. (28), p. 29 (**the price level is determined**): for `η ≥ 0` and bounded
adapted `m`, `u`, the forward solution (28) converges, is bounded and adapted, solves (27),
and is the unique bounded solution of (27). -/
theorem eq28_unique {η : ℝ} (hη : 0 ≤ η) {m u : ℕ → Ω → ℝ} (hmb : BoundedProc m)
    (hma : 𝔼.Adapted m) (hub : BoundedProc u) (hua : 𝔼.Adapted u) :
    Eq27 𝔼 η (fwd28 𝔼 η m u) m u ∧ BoundedProc (fwd28 𝔼 η m u) ∧
      𝔼.Adapted (fwd28 𝔼 η m u) ∧
      ∀ p, Eq27 𝔼 η p m u → BoundedProc p → p = fwd28 𝔼 η m u := by
  obtain ⟨ha0, ha1⟩ := coef_bounds hη
  obtain ⟨M₁, hM₁⟩ := hmb
  obtain ⟨M₂, hM₂⟩ := hub
  have hc : 0 < (1 + η)⁻¹ := inv_pos.mpr (by linarith)
  set w : ℕ → Ω → ℝ := fun s => (1 + η)⁻¹ • m s + u s with hw
  have hwb : ∀ t ω, |w t ω| ≤ (1 + η)⁻¹ * M₁ + M₂ := fun t ω => by
    simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hM₂ t ω))
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hM₁ t ω) hc.le
  have hwa : 𝔼.Adapted w := fun t => by
    simp only [hw, map_add, map_smul, hma t, hua t]
  have hfs : fwd28 𝔼 η m u = 𝔼.forwardSeries (η / (1 + η)) w := by
    funext t ω
    rw [hw, forwardSeries_smul_add 𝔼 ha0 ha1 hM₁ hM₂]
    rfl
  rw [hfs]
  exact ⟨𝔼.forwardSeries_solves ha0 ha1 hwb hwa, 𝔼.forwardSeries_bounded ha0 ha1 hwb,
    forwardSeries_adapted 𝔼 ha0 ha1 hwb,
    fun p hp hpb => 𝔼.eq_forwardSeries ha0 ha1 hwb hwa hp hpb⟩

/-! ### The money-growth representation (29) and fn. 8 -/

/-- Galí (2015), fn. 8, p. 29: the forcing `η/(1+η) E_t{Δm_{t+1}} + u_t` of the equation for
`p̃_t = p_t − m_t`. -/
noncomputable def w29 (η : ℝ) (dm u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (η / (1 + η)) • 𝔼.E t (dm (t + 1)) + u t

/-- Galí (2015), fn. 8, p. 29: with `m_{t+1} = m_t + Δm_{t+1}` (adapted `m`), (27) is
equivalent to `p̃_t = η/(1+η) E_t{p̃_{t+1}} + η/(1+η) E_t{Δm_{t+1}} + u_t`, `p̃ = p − m`. -/
theorem eq27_iff_tilde {η : ℝ} (hη : 0 ≤ η) {p m dm u : ℕ → Ω → ℝ}
    (hdm : ∀ t, m (t + 1) = m t + dm (t + 1)) (hma : 𝔼.Adapted m) :
    Eq27 𝔼 η p m u ↔
      ∀ t, p t - m t = (η / (1 + η)) • 𝔼.E t (p (t + 1) - m (t + 1)) + w29 𝔼 η dm u t := by
  have hne : (1 + η) ≠ 0 := by linarith
  have hid : (1 + η)⁻¹ = 1 - η / (1 + η) := by
    field_simp
    ring
  have hEm : ∀ t, 𝔼.E t (m (t + 1)) = m t + 𝔼.E t (dm (t + 1)) := fun t => by
    rw [hdm t, map_add, hma t]
  constructor
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hEm t) ω
    simp only [w29, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [hid] at h1
    rw [h2]
    linear_combination h1
  · intro h t
    funext ω
    have h1 := congrFun (h t) ω
    have h2 := congrFun (hEm t) ω
    simp only [w29, map_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    rw [h2] at h1
    rw [hid]
    linear_combination h1

/-- Galí (2015), eq. (29), p. 29:
`p_t = m_t + ∑_{k≥1} (η/(1+η))ᵏ E_t{Δm_{t+k}} + ū_t` (the sum written from `k + 1`). -/
noncomputable def fwd29 (η : ℝ) (m dm u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => m t ω + ∑' k, (η / (1 + η)) ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω +
    𝔼.forwardSeries (η / (1 + η)) u t ω

/-- Galí (2015), fn. 8, p. 29: (29) is `m_t` plus the forward solution of the `p̃` equation. -/
theorem fwd29_eq {η : ℝ} (hη : 0 ≤ η) {m dm u : ℕ → Ω → ℝ} (hdmb : BoundedProc dm)
    (hub : BoundedProc u) (t : ℕ) :
    fwd29 𝔼 η m dm u t = m t + 𝔼.forwardSeries (η / (1 + η)) (w29 𝔼 η dm u) t := by
  obtain ⟨ha0, ha1⟩ := coef_bounds hη
  obtain ⟨M₁, hM₁⟩ := hdmb
  obtain ⟨M₂, hM₂⟩ := hub
  funext ω
  set a := η / (1 + η) with ha
  have h1 : Summable (fun k => a ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω) := by
    refine ((𝔼.forwardSeries_summable ha0 ha1 (u := fun s => dm (s + 1))
      (fun s ω' => hM₁ (s + 1) ω') t ω).mul_left a).congr fun k => ?_
    ring
  have h2 := 𝔼.forwardSeries_summable ha0 ha1 hM₂ t ω
  simp only [fwd29, Pi.add_apply]
  rw [add_assoc]
  congr 1
  change _ = ∑' k, a ^ k * 𝔼.E t (w29 𝔼 η dm u (t + k)) ω
  change ∑' k, a ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω +
    ∑' k, a ^ k * 𝔼.E t (u (t + k)) ω = _
  rw [← h1.tsum_add h2]
  refine tsum_congr fun k => ?_
  simp only [w29, map_add, map_smul, 𝔼.tower (Nat.le_add_right t k), Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Galí (2015), eq. (29) and fn. 8, p. 29 (**existence and uniqueness with a non-stationary
money supply**): for `η ≥ 0`, adapted `m` with bounded growth `Δm` and bounded
adapted `u`, (29) solves (27), `p_t − m_t` is bounded, `p` is adapted, and (29) is the unique
solution of (27) with `p_t − m_t` bounded. -/
theorem eq29_unique {η : ℝ} (hη : 0 ≤ η) {m dm u : ℕ → Ω → ℝ}
    (hdm : ∀ t, m (t + 1) = m t + dm (t + 1)) (hma : 𝔼.Adapted m) (hdmb : BoundedProc dm)
    (hub : BoundedProc u) (hua : 𝔼.Adapted u) :
    Eq27 𝔼 η (fwd29 𝔼 η m dm u) m u ∧ BoundedProc (fun t => fwd29 𝔼 η m dm u t - m t) ∧
      𝔼.Adapted (fwd29 𝔼 η m dm u) ∧
      ∀ p, Eq27 𝔼 η p m u → BoundedProc (fun t => p t - m t) → p = fwd29 𝔼 η m dm u := by
  obtain ⟨ha0, ha1⟩ := coef_bounds hη
  have hfeq := fwd29_eq 𝔼 (m := m) hη hdmb hub
  obtain ⟨M₁, hM₁⟩ := hdmb
  obtain ⟨M₂, hM₂⟩ := hub
  set a := η / (1 + η) with ha
  have hwb : ∀ t ω, |w29 𝔼 η dm u t ω| ≤ M₁ + M₂ := fun t ω => by
    simp only [w29, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans (add_le_add ?_ (hM₂ t ω))
    rw [abs_mul, abs_of_nonneg ha0]
    calc a * |𝔼.E t (dm (t + 1)) ω| ≤ 1 * M₁ :=
          mul_le_mul ha1.le (𝔼.abs_E_le (hM₁ (t + 1)) t ω) (abs_nonneg _) zero_le_one
      _ = M₁ := one_mul _
  have hwa : 𝔼.Adapted (w29 𝔼 η dm u) := fun t => by
    simp only [w29, map_add, map_smul, 𝔼.E_E_self, hua t]
  have htil : (fun t => fwd29 𝔼 η m dm u t - m t) = 𝔼.forwardSeries a (w29 𝔼 η dm u) := by
    funext t
    rw [hfeq t, add_sub_cancel_left]
  refine ⟨(eq27_iff_tilde 𝔼 hη hdm hma).mpr fun t => ?_, ?_, fun t => ?_, fun p hp hpb => ?_⟩
  · have h := congrFun htil
    rw [h t, h (t + 1)]
    exact 𝔼.forwardSeries_solves ha0 ha1 hwb hwa t
  · rw [htil]
    exact 𝔼.forwardSeries_bounded ha0 ha1 hwb
  · rw [hfeq t, map_add, hma t, forwardSeries_adapted 𝔼 ha0 ha1 hwb t]
  · have hz := (eq27_iff_tilde 𝔼 hη hdm hma).mp hp
    have he := 𝔼.eq_forwardSeries (z := fun t => p t - m t) ha0 ha1 hwb hwa hz hpb
    funext t
    rw [hfeq t, ← congrFun he t, add_sub_cancel]

/-- Galí (2015), p. 29 (the nominal rate under a money rule): for `η > 0`, money demand (11)
gives `i_t = η^{−1}(y_t − (m_t − p_t))`, and with (29)
`i_t = η^{−1} ∑_{k≥1} (η/(1+η))ᵏ E_t{Δm_{t+k}} + u''_t`, `u''_t = η^{−1}(ū_t + y_t)`. -/
theorem interest_rate_29 {η : ℝ} (hη : 0 < η) {m dm u p y i : ℕ → Ω → ℝ}
    (hmd : MoneyDemand η m p y i) (hp : p = fwd29 𝔼 η m dm u) (t : ℕ) (ω : Ω) :
    i t ω = η⁻¹ * (y t ω - (m t ω - p t ω)) ∧
      i t ω = η⁻¹ * ∑' k, (η / (1 + η)) ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω +
        η⁻¹ * (𝔼.forwardSeries (η / (1 + η)) u t ω + y t ω) := by
  have h2 := congrFun (hmd t) ω
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h2
  have hi : i t ω = η⁻¹ * (y t ω - (m t ω - p t ω)) := by
    rw [h2]
    field_simp
    ring
  refine ⟨hi, ?_⟩
  rw [hi, hp]
  simp only [fwd29]
  ring

/-! ### AR(1) money growth, p. 30 -/

/-- Galí (2015), p. 30: for AR(1) money growth with persistence `ρ_m`, `|ρ_m| ≤ 1`, the series
in (29) sums to `ηρ_m/(1+η(1−ρ_m)) Δm_t`. -/
theorem ar1_series29 {η ρ : ℝ} (hη : 0 ≤ η) (hρ : |ρ| ≤ 1) {dm : ℕ → Ω → ℝ}
    (hu : 𝔼.IsAR1 ρ dm) (t : ℕ) (ω : Ω) :
    HasSum (fun k => (η / (1 + η)) ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω)
      (η * ρ / (1 + η * (1 - ρ)) * dm t ω) := by
  obtain ⟨ha0, ha1⟩ := coef_bounds hη
  set a := η / (1 + η) with ha
  have hq : |a * ρ| < 1 := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc a * |ρ| ≤ a * 1 := mul_le_mul_of_nonneg_left hρ ha0
      _ < 1 := by linarith
  have hg := (hasSum_geometric_of_abs_lt_one hq).mul_left (a * ρ * dm t ω)
  have hf : (fun k => a ^ (k + 1) * 𝔼.E t (dm (t + k + 1)) ω) =
      fun k => a * ρ * dm t ω * (a * ρ) ^ k := by
    funext k
    have h := congrFun (𝔼.ar1_iterate hu t (k + 1)) ω
    rw [← add_assoc] at h
    simp only [Pi.smul_apply, smul_eq_mul] at h
    rw [h]
    ring
  rw [hf]
  have hne : (1 + η) ≠ 0 := by linarith
  have hne2 : 1 + η * (1 - ρ) ≠ 0 := by
    have := le_abs_self ρ
    nlinarith
  have hne3 : 1 + η - η * ρ ≠ 0 := fun h => hne2 (by linarith)
  convert hg using 1
  rw [ha]
  field_simp
  ring

/-- Galí (2015), p. 30 (**AR(1) money growth**): with no real shocks (`r_t = y_t = 0`),
`η ≥ 0` and money growth `Δm` a bounded AR(1) with `|ρ_m| ≤ 1`, in every equilibrium
(money demand (11), Fisher (22), adapted `p` with `p_t − m_t` bounded)
`p_t = m_t + ηρ_m/(1+η(1−ρ_m)) Δm_t` and `i_t = ρ_m/(1+η(1−ρ_m)) Δm_t`. -/
theorem ar1_money_equilibrium {η ρ : ℝ} (hη : 0 ≤ η) (hρ : |ρ| ≤ 1)
    {m dm p i infl : ℕ → Ω → ℝ} (hdm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hma : 𝔼.Adapted m) (hu : 𝔼.IsAR1 ρ dm) (hdmb : BoundedProc dm)
    (hmd : MoneyDemand η m p 0 i) (hF : Fisher 𝔼 i infl 0) (hid : InflationId p infl)
    (hp : 𝔼.Adapted p) (hpb : BoundedProc (fun t => p t - m t)) :
    (∀ t, p t = m t + (η * ρ / (1 + η * (1 - ρ))) • dm t) ∧
      ∀ t, i t = (ρ / (1 + η * (1 - ρ))) • dm t := by
  have hne : (1 + η) ≠ 0 := by linarith
  have hD : 0 < 1 + η * (1 - ρ) := by
    have := le_abs_self ρ
    nlinarith
  set c := η * ρ / (1 + η * (1 - ρ)) with hc
  have h0 : uDef η (0 : ℕ → Ω → ℝ) 0 = 0 := by
    funext t ω
    simp [uDef]
  have h27 : Eq27 𝔼 η p m 0 := by
    have := eq27_of_model 𝔼 hη hmd hF hid hp
    rwa [h0] at this
  obtain ⟨-, -, -, huniq⟩ := eq29_unique 𝔼 (u := 0) hη hdm hma hdmb ⟨0, fun t ω => by simp⟩
    (fun t => by simp)
  set q : ℕ → Ω → ℝ := fun t => m t + c • dm t with hq
  have hq27 : Eq27 𝔼 η q m 0 := by
    refine (eq27_iff_tilde 𝔼 hη hdm hma).mpr fun t => ?_
    funext ω
    have h1 := congrFun (hu.2 t) ω
    simp only [hq, w29, map_sub, map_add, map_smul, hdm t, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
    rw [h1, hc]
    field_simp
    ring
  have hqb : BoundedProc (fun t => q t - m t) := by
    obtain ⟨M, hM⟩ := hdmb
    refine ⟨|c| * M, fun t ω => ?_⟩
    simp only [hq, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t ω) (abs_nonneg _)
  have hpq : p = q := (huniq p h27 hpb).trans (huniq q hq27 hqb).symm
  refine ⟨fun t => by rw [hpq], fun t => ?_⟩
  rw [hF t, hid t, hpq]
  funext ω
  have h1 := congrFun (hu.2 t) ω
  have h2 := congrFun (hu.1 t) ω
  simp only [hq, hdm t, map_sub, map_add, map_smul, hma t, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 h2 ⊢
  rw [h1, h2, hc]
  field_simp
  ring

/-- Galí (2015), p. 30: the price level `p_t = m_t + ηρ_m/(1+η(1−ρ_m)) Δm_t` as a function of
the date-`t` money-growth innovation `ε^m_t`, with `Δm_t = ρ_m Δm_{t−1} + ε^m_t` and
`m_t = m_{t−1} + Δm_t`. -/
noncomputable def priceImpactM (η ρ mprev dmprev ε : ℝ) : ℝ :=
  mprev + (ρ * dmprev + ε) + η * ρ / (1 + η * (1 - ρ)) * (ρ * dmprev + ε)

/-- Galí (2015), p. 30: the money supply `m_t = m_{t−1} + Δm_t` as a function of `ε^m_t`. -/
def moneyImpactM (ρ mprev dmprev ε : ℝ) : ℝ := mprev + (ρ * dmprev + ε)

/-- Galí (2015), p. 30: the nominal rate `i_t = ρ_m/(1+η(1−ρ_m)) Δm_t` as a function of
`ε^m_t`. -/
noncomputable def rateImpactM (η ρ dmprev ε : ℝ) : ℝ :=
  ρ / (1 + η * (1 - ρ)) * (ρ * dmprev + ε)

/-- Galí (2015), p. 30: in the AR(1) equilibrium, the date-`t+1` price level, money supply and
nominal rate are the impact maps evaluated at `ε^m_{t+1} = Δm_{t+1} − ρ_m Δm_t`, everything
else (`m_t`, `Δm_t`) being predetermined. -/
theorem impact_representationM {η ρ : ℝ} {m dm p i : ℕ → Ω → ℝ}
    (hdm : ∀ t, m (t + 1) = m t + dm (t + 1))
    (hp : ∀ t, p t = m t + (η * ρ / (1 + η * (1 - ρ))) • dm t)
    (hi : ∀ t, i t = (ρ / (1 + η * (1 - ρ))) • dm t) (t : ℕ) (ω : Ω) :
    p (t + 1) ω = priceImpactM η ρ (m t ω) (dm t ω) (dm (t + 1) ω - ρ * dm t ω) ∧
      m (t + 1) ω = moneyImpactM ρ (m t ω) (dm t ω) (dm (t + 1) ω - ρ * dm t ω) ∧
      i (t + 1) ω = rateImpactM η ρ (dm t ω) (dm (t + 1) ω - ρ * dm t ω) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hp (t + 1), hdm t]
    simp only [priceImpactM, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [hdm t]
    simp only [moneyImpactM, Pi.add_apply]
    ring
  · rw [hi (t + 1)]
    simp only [rateImpactM, Pi.smul_apply, smul_eq_mul]
    ring

/-- Galí (2015), p. 30: `∂p_t/∂ε^m_t = 1 + ηρ_m/(1+η(1−ρ_m))`. -/
theorem hasDerivAt_priceImpactM (η ρ mprev dmprev ε : ℝ) :
    HasDerivAt (priceImpactM η ρ mprev dmprev) (1 + η * ρ / (1 + η * (1 - ρ))) ε := by
  have h : priceImpactM η ρ mprev dmprev =
      fun e => priceImpactM η ρ mprev dmprev 0 + (1 + η * ρ / (1 + η * (1 - ρ))) * e := by
    funext e
    unfold priceImpactM
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 30: `∂m_t/∂ε^m_t = 1`. -/
theorem hasDerivAt_moneyImpactM (ρ mprev dmprev ε : ℝ) :
    HasDerivAt (moneyImpactM ρ mprev dmprev) 1 ε := by
  have h : moneyImpactM ρ mprev dmprev = fun e => moneyImpactM ρ mprev dmprev 0 + 1 * e := by
    funext e
    unfold moneyImpactM
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 30: `∂i_t/∂ε^m_t = ρ_m/(1+η(1−ρ_m))`. -/
theorem hasDerivAt_rateImpactM (η ρ dmprev ε : ℝ) :
    HasDerivAt (rateImpactM η ρ dmprev) (ρ / (1 + η * (1 - ρ))) ε := by
  have h : rateImpactM η ρ dmprev =
      fun e => rateImpactM η ρ dmprev 0 + ρ / (1 + η * (1 - ρ)) * e := by
    funext e
    unfold rateImpactM
    ring
  rw [h]
  exact hasDerivAt_affine _ _ _

/-- Galí (2015), p. 30 (**price overshooting**): for `η ≥ 0` and `ρ_m ≤ 1`, the price level
responds more than one-for-one to a money-growth shock (`∂p_t/∂ε^m_t > 1 = ∂m_t/∂ε^m_t`)
iff `η ρ_m > 0`; in particular whenever `η > 0` and `ρ_m > 0`. -/
theorem price_overshoots_iff {η ρ : ℝ} (hη : 0 ≤ η) (hρ : ρ ≤ 1) :
    1 < 1 + η * ρ / (1 + η * (1 - ρ)) ↔ 0 < η * ρ := by
  have hD : 0 < 1 + η * (1 - ρ) := by nlinarith
  rw [lt_add_iff_pos_right, div_pos_iff_of_pos_right hD]

/-- Galí (2015), p. 30: overshooting in the empirically relevant case `η > 0`, `0 < ρ_m ≤ 1`. -/
theorem price_overshoots {η ρ : ℝ} (hη : 0 < η) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1) :
    1 < 1 + η * ρ / (1 + η * (1 - ρ)) :=
  (price_overshoots_iff hη.le hρ).mpr (mul_pos hη hρ0)

/-- Galí (2015), p. 30 (**no liquidity effect**): for `η ≥ 0` and `ρ_m ≤ 1`, the nominal rate
rises after a money-growth expansion (`∂i_t/∂ε^m_t > 0`) iff `ρ_m > 0`. -/
theorem no_liquidity_effect_iff {η ρ : ℝ} (hη : 0 ≤ η) (hρ : ρ ≤ 1) :
    0 < ρ / (1 + η * (1 - ρ)) ↔ 0 < ρ := by
  have hD : 0 < 1 + η * (1 - ρ) := by nlinarith
  exact div_pos_iff_of_pos_right hD

end Gali.ClassicalMonetaryModel.MoneySupply
