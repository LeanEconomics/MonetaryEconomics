/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.Equilibrium

/-!
# Transversality in terms of total government liabilities (Propositions 2.2 and 2.2′)

Woodford (2003), *Interest and Prices*, Chapter 2, Proposition 2.2, p. 72, and Appendix A.2,
pp. 628–629 (including Proposition 2.2′ for the economy with transactions frictions of §3).

Total government liabilities at the end of period `t` are inferred from the identity (p. 628)
`D_t = M^s_t + E_t[Q_{t,t+1}(W^s_{t+1} − (1 + i^m_t)M^s_t)]`, i.e. money plus the value
`B^s_t = E_t[Q_{t,t+1}A^s_{t+1}]` of bonds (`debt_eq_money_add_bonds`).

## Main results

* `beta_E_mu_W`: under (1.20), `β E_t[μ_{t+1}W_{t+1}] = μ_t E_t[Q_{t,t+1}W_{t+1}]`.
* `debt_eq`: `D_t = E_t[Q_{t,t+1}W^s_{t+1}] + Δ_tM^s_t`.
* `tvc_identity`: the A.2 identity `β E_t[μ_{T+1}W^s_{T+1}] = E_t[μ_T D_T]` for `T ≥ t`.
* `prop_2_2`: (1.22) ⟺ (1.24) given (1.15), (1.20), (1.21). Hypothesis (1.23) of the printed
  proposition is not needed (survey E17).
* `tvc_identity_frictions`, `prop_2_2'`: with transactions frictions, (3.3) and (3.4),
  `β E_t[μ_{T+1}W_{T+1}] = E_t[μ_T D_T] − E_t[u_m M_T/P_T]` and (1.22) ⟺ (A.3).
-/

namespace Woodford.PriceLevelDetermination.Transversality

open Filter Topology AssetPricing IntertemporalBudget Equilibrium

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), p. 628: total government liabilities
`D_t ≡ M^s_t + E_t[Q_{t,t+1}(W^s_{t+1} − (1 + i^m_t)M^s_t)]`. -/
noncomputable def debt (q im Ms Ws : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  Ms t + 𝔼.E t (q t * (Ws (t + 1) - fun ω => (1 + im t ω) * Ms t ω))

/-- Woodford (2003), p. 72 and p. 628: if `W^s_{t+1} = (1+i^m_t)M^s_t + A^s_{t+1}` and bonds are
priced by (1.4), `B^s_t = E_t[Q_{t,t+1}A^s_{t+1}]`, then `D_t = M^s_t + B^s_t`. -/
theorem debt_eq_money_add_bonds {q im Ms Ws As Bs : ℕ → Ω → ℝ} {t : ℕ}
    (h13 : Ws (t + 1) = fun ω => (1 + im t ω) * Ms t ω + As (t + 1) ω)
    (h14 : Bs t = 𝔼.E t (q t * As (t + 1))) : debt 𝔼 q im Ms Ws t = Ms t + Bs t := by
  have h : Ws (t + 1) - (fun ω => (1 + im t ω) * Ms t ω) = As (t + 1) := by
    rw [h13]
    funext ω
    simp
  rw [debt, h, h14]

/-- Woodford (2003), p. 628 (A.2) with (1.5): `D_t = E_t[Q_{t,t+1}W^s_{t+1}] + Δ_tM^s_t`. -/
theorem debt_eq (hP : 𝔼.PullOut) {q i im Ms Ws : ℕ → Ω → ℝ} {t : ℕ}
    (h15 : 𝔼.E t (q t) = fun ω => (1 + i t ω)⁻¹) (hi : ∀ ω, 0 < 1 + i t ω)
    (him : 𝔼.E t (im t) = im t) (hMs : 𝔼.E t (Ms t) = Ms t) :
    debt 𝔼 q im Ms Ws t = 𝔼.E t (q t * Ws (t + 1)) + delta i im t * Ms t := by
  have hk : 𝔼.E t (fun ω => (1 + im t ω) * Ms t ω) = fun ω => (1 + im t ω) * Ms t ω :=
    known_mul 𝔼 hP (known_one_add 𝔼 him) hMs
  rw [debt, mul_sub, map_sub, E_q_riskless 𝔼 hP h15 hk]
  funext ω
  have := (hi ω).ne'
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, delta]
  field_simp
  ring

/-- Woodford (2003), p. 629 (A.2): under the equilibrium discount factor (1.20) and `μ_t` known at
`t`, `β E_t[μ_{t+1}W_{t+1}] = μ_t E_t[Q_{t,t+1}W_{t+1}]`. -/
theorem beta_E_mu_W (hP : 𝔼.PullOut) {β : ℝ} {lam P q : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω)
    {t : ℕ} (hmu : 𝔼.E t (mu lam P t) = mu lam P t) (W : Ω → ℝ) :
    β • 𝔼.E t (mu lam P (t + 1) * W) = mu lam P t * 𝔼.E t (q t * W) := by
  have h : β • (mu lam P (t + 1) * W) = mu lam P t * (q t * W) := by
    rw [q_eq_mu heu hlam hPpos t]
    funext ω
    have := (mu_pos hlam hPpos t ω).ne'
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    field_simp
  rw [← ExpectationSystem.E_smul, h, hP t _ _ hmu]

/-- Woodford (2003), p. 629 (A.2): in the cashless economy, with (1.15), (1.20) and (1.21),
`β E_t[μ_{T+1}W^s_{T+1}] = E_t[μ_T D_T]` for every `T ≥ t`. -/
theorem tvc_identity (hP : 𝔼.PullOut) {β : ℝ} {lam P q i im Ms Ws : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hfis : FisherEq 𝔼 β lam P i) (h115 : ∀ t, i t = im t)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 0 < 1 + i t ω)
    (hmu : 𝔼.Adapted (mu lam P)) (him : 𝔼.Adapted im) (hMs : 𝔼.Adapted Ms)
    {t T : ℕ} (hT : t ≤ T) :
    β • 𝔼.E t (mu lam P (T + 1) * Ws (T + 1)) =
      𝔼.E t (mu lam P T * debt 𝔼 q im Ms Ws T) := by
  have h15 := E_q_of_euler_fisher 𝔼 heu hfis
  have hD : debt 𝔼 q im Ms Ws T = 𝔼.E T (q T * Ws (T + 1)) := by
    rw [debt_eq 𝔼 hP (h15 T) (hi T) (him T) (hMs T)]
    funext ω
    simp [delta, h115 T]
  have hstep := beta_E_mu_W 𝔼 hP heu hlam hPpos (hmu T) (Ws (T + 1))
  rw [hD, ← hstep, ExpectationSystem.E_smul, 𝔼.tower hT]

/-- Woodford (2003), p. 72: `u_c(Y_T; ξ_T)X_T/P_T = μ_T X_T`. -/
theorem lam_mul_div_eq (lam P X : ℕ → Ω → ℝ) (T : ℕ) :
    (fun ω' => lam T ω' * X T ω' / P T ω') = mu lam P T * X T := by
  funext ω'
  simp only [mu, Pi.mul_apply]
  ring

/-- Woodford (2003), Proposition 2.2, p. 72, proof A.2, pp. 628–629: let assets be priced by
(1.20) and let the processes satisfy (1.15) and (1.21). Then the transversality condition (1.22)
on household wealth holds iff the transversality condition (1.24) on total government liabilities
`D_t` holds. (The printed hypothesis (1.23) is not needed: survey E17.) -/
theorem prop_2_2 (hP : 𝔼.PullOut) {β : ℝ} {lam P q i im Ms Ws : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hfis : FisherEq 𝔼 β lam P i) (h115 : ∀ t, i t = im t)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 0 < 1 + i t ω)
    (hmu : 𝔼.Adapted (mu lam P)) (him : 𝔼.Adapted im) (hMs : 𝔼.Adapted Ms) :
    TVCWealth 𝔼 β lam P Ws ↔ TVCDebt 𝔼 β lam P (debt 𝔼 q im Ms Ws) := by
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  apply tendsto_congr'
  filter_upwards [eventually_ge_atTop t] with T hT
  have h := congrFun (tvc_identity 𝔼 hP heu hfis h115 hlam hPpos hi hmu him hMs (Ws := Ws) hT) ω
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [lam_mul_div_eq, lam_mul_div_eq, pow_succ, mul_assoc, h]

/-- Woodford (2003), p. 629 (A.2, frictions): with transactions frictions, `λ_t` and `u_{m,t}`
the marginal utilities of consumption and real balances along the path, (1.20), (1.21) and (3.3)
`u_{m,t} = λ_tΔ_t` give `β E_t[μ_{T+1}W^s_{T+1}] = E_t[μ_T D_T] − E_t[u_{m,T}M^s_T/P_T]`
for `T ≥ t`. -/
theorem tvc_identity_frictions (hP : 𝔼.PullOut) {β : ℝ} {lam um P q i im Ms Ws : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hfis : FisherEq 𝔼 β lam P i)
    (h33 : ∀ t ω, um t ω = lam t ω * delta i im t ω)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 0 < 1 + i t ω)
    (hmu : 𝔼.Adapted (mu lam P)) (him : 𝔼.Adapted im) (hMs : 𝔼.Adapted Ms)
    {t T : ℕ} (hT : t ≤ T) :
    β • 𝔼.E t (mu lam P (T + 1) * Ws (T + 1)) =
      𝔼.E t (mu lam P T * debt 𝔼 q im Ms Ws T) -
        𝔼.E t (fun ω => um T ω * Ms T ω / P T ω) := by
  have h15 := E_q_of_euler_fisher 𝔼 heu hfis
  have hD := debt_eq 𝔼 hP (h15 T) (hi T) (him T) (hMs T) (Ws := Ws)
  have hstep := beta_E_mu_W 𝔼 hP heu hlam hPpos (hmu T) (Ws (T + 1))
  have hsplit : mu lam P T * debt 𝔼 q im Ms Ws T =
      mu lam P T * 𝔼.E T (q T * Ws (T + 1)) + fun ω => um T ω * Ms T ω / P T ω := by
    rw [hD]
    funext ω
    simp only [Pi.add_apply, Pi.mul_apply, mu, h33]
    ring
  rw [hsplit, map_add, ← hstep, ExpectationSystem.E_smul, 𝔼.tower hT, add_sub_cancel_right]

/-- Woodford (2003), Proposition 2.2′, p. 629: in the economy with transactions frictions, let
assets be priced by (1.20) and let the processes satisfy (1.21), (3.3) `u_m/u_c = Δ` and (3.4)
`∑_{T ≥ t} β^T E_t[u_c Y_T + u_m M^s_T/P_T] < ∞`, with `Y, M^s ≥ 0` and (1.11). Then (1.22)
holds iff (A.3) `lim_T β^T E_t[u_c D_T/P_T] = 0`. -/
theorem prop_2_2' (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β)
    {lam um P q i im Ms Ws Y : ℕ → Ω → ℝ}
    (heu : EulerSDF β lam P q) (hfis : FisherEq 𝔼 β lam P i)
    (h33 : ∀ t ω, um t ω = lam t ω * delta i im t ω)
    (h34 : ∀ t ω, Summable fun n => β ^ (t + n) *
      𝔼.E t (fun ω' => lam (t + n) ω' * Y (t + n) ω' +
        um (t + n) ω' * Ms (t + n) ω' / P (t + n) ω') ω)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (hi : ∀ t ω, 0 < 1 + i t ω)
    (h111 : ∀ t ω, im t ω ≤ i t ω) (hY : ∀ t ω, 0 ≤ Y t ω) (hMs0 : ∀ t ω, 0 ≤ Ms t ω)
    (hmu : 𝔼.Adapted (mu lam P)) (him : 𝔼.Adapted im) (hMs : 𝔼.Adapted Ms) :
    TVCWealth 𝔼 β lam P Ws ↔ TVCDebt 𝔼 β lam P (debt 𝔼 q im Ms Ws) := by
  refine forall_congr' fun t => forall_congr' fun ω => ?_
  -- the money-services term vanishes in the limit, by (3.4)
  set v : ℕ → ℝ := fun T => β ^ T * 𝔼.E t (fun ω' => um T ω' * Ms T ω' / P T ω') ω with hv
  have hum0 : ∀ T ω', 0 ≤ um T ω' * Ms T ω' / P T ω' := fun T ω' => by
    rw [h33]
    exact div_nonneg (mul_nonneg (mul_nonneg (hlam T ω').le
      ((delta_nonneg_iff (hi T ω')).mpr (h111 T ω'))) (hMs0 T ω')) (hPpos T ω').le
  have hv0 : Tendsto v atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat t]
    have hlim := (h34 t ω).tendsto_atTop_zero
    refine squeeze_zero (fun n => mul_nonneg (pow_nonneg hβ.le _) (E_nonneg 𝔼 (hum0 _) ω))
      (fun n => ?_) hlim
    simp only [hv, add_comm n t]
    refine mul_le_mul_of_nonneg_left (𝔼.mono t (fun ω' => ?_) ω) (pow_nonneg hβ.le _)
    have := mul_nonneg (hlam (t + n) ω').le (hY (t + n) ω')
    linarith
  rw [← tendsto_add_atTop_iff_nat 1]
  have hev : (fun T => β ^ (T + 1) * 𝔼.E t (fun ω' => lam (T + 1) ω' * Ws (T + 1) ω' /
      P (T + 1) ω') ω) =ᶠ[atTop]
      fun T => β ^ T * 𝔼.E t (fun ω' => lam T ω' * debt 𝔼 q im Ms Ws T ω' / P T ω') ω - v T := by
    filter_upwards [eventually_ge_atTop t] with T hT
    have h := congrFun
      (tvc_identity_frictions 𝔼 hP heu hfis h33 hlam hPpos hi hmu him hMs (Ws := Ws) hT) ω
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h
    rw [lam_mul_div_eq, lam_mul_div_eq, pow_succ, mul_assoc, h]
    simp only [hv]
    ring
  rw [tendsto_congr' hev]
  constructor
  · intro h
    simpa using h.add hv0
  · intro h
    simpa using h.sub hv0

end Woodford.PriceLevelDetermination.Transversality
