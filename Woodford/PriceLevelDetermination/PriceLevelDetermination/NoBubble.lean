/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.Transversality

/-!
# Money as a pure bubble: no equilibrium when no interest is paid on money (Proposition 2.4)

Woodford (2003), *Interest and Prices*, Chapter 2, Proposition 2.4, p. 82, and Appendix A.5,
pp. 637–638.

Suppose the monetary base is bounded below, `M^s_t ≥ M̲ > 0`, government debt is nonnegative,
`D_t ≥ M^s_t`, and `i^m_t = 0`. Then (1.15) forces `i_t = 0`, (1.21) becomes
`β E_t[μ_{t+1}] = μ_t` with `μ_t = u_c(Y_t; ξ_t)/P_t`, and by iteration
`β^T E_t μ_T = β^t μ_t`, so `β^T E_t[μ_T D_T] ≥ M̲ β^t μ_t > 0` for all `T ≥ t`, contradicting the
transversality condition (1.24). Hence no rational-expectations equilibrium exists.

## Main results

* `beta_E_mu_succ`, `beta_pow_E_mu`: `β E_t μ_{t+1} = μ_t` and `β^T E_t μ_T = β^t μ_t` (`T ≥ t`).
* `tvcDebt_lower_bound`: `β^T E_t[u_c D_T/P_T] ≥ M̲ β^t μ_t` for all `T ≥ t`.
* `prop_2_4`: (1.24) fails; `not_tvcWealth`: so does (1.22) (via Proposition 2.2);
  `no_REE`: there is no rational-expectations equilibrium price level.
* `fisher_deflation_path`: the hypotheses are not vacuous: under perfect foresight with constant
  marginal utility, the deflationary path `P_t = β^t` satisfies (1.15) and (1.21) with
  `i = i^m = 0`; it is only the transversality condition that rules it out.
-/

namespace Woodford.PriceLevelDetermination.NoBubble

open Filter Topology AssetPricing Equilibrium Transversality

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), A.5, p. 638: with `i^m = 0`, (1.15) and (1.21) give
`β E_t[u_c(Y_{t+1}; ξ_{t+1})/P_{t+1}] = u_c(Y_t; ξ_t)/P_t`. -/
theorem beta_E_mu_succ (hP : 𝔼.PullOut) {β : ℝ} {lam P i im : ℕ → Ω → ℝ}
    (hfis : FisherEq 𝔼 β lam P i) (h115 : ∀ t, i t = im t) (him0 : ∀ t, im t = 0)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω)
    (hmuinv : ∀ t, 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹) (t : ℕ) :
    β • 𝔼.E t (mu lam P (t + 1)) = mu lam P t := by
  set q : ℕ → Ω → ℝ := fun s ω => β * (lam (s + 1) ω / lam s ω) * (P s ω / P (s + 1) ω)
  have heu : EulerSDF β lam P q := fun _ => rfl
  have h15 := E_q_of_euler_fisher 𝔼 heu hfis t
  have h := (E_q_eq_iff_mu 𝔼 hP heu hlam hPpos (hmuinv t)).mp h15
  funext ω
  have := h ω
  rw [h115 t, him0 t] at this
  simpa using this

/-- Woodford (2003), A.5, p. 638 (by iteration, using the law of iterated expectations):
`β^{t+n} E_t[μ_{t+n}] = β^t μ_t`. -/
theorem beta_pow_E_mu (hP : 𝔼.PullOut) {β : ℝ} {lam P i im : ℕ → Ω → ℝ}
    (hfis : FisherEq 𝔼 β lam P i) (h115 : ∀ t, i t = im t) (him0 : ∀ t, im t = 0)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (hmu : 𝔼.Adapted (mu lam P))
    (hmuinv : ∀ t, 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹)
    (t n : ℕ) : β ^ (t + n) • 𝔼.E t (mu lam P (t + n)) = β ^ t • mu lam P t := by
  induction n with
  | zero => simp only [add_zero, hmu t]
  | succ n ih =>
    have hs := beta_E_mu_succ 𝔼 hP hfis h115 him0 hlam hPpos hmuinv (t + n)
    calc β ^ (t + (n + 1)) • 𝔼.E t (mu lam P (t + (n + 1)))
        = β ^ (t + n) • 𝔼.E t (β • 𝔼.E (t + n) (mu lam P (t + n + 1))) := by
          rw [ExpectationSystem.E_smul, 𝔼.tower (Nat.le_add_right t n), smul_smul, ← pow_succ,
            ← add_assoc]
      _ = β ^ t • mu lam P t := by rw [hs, ih]

/-- Woodford (2003), A.5, p. 638: with `D_T ≥ M^s_T ≥ M̲`,
`β^T E_t[u_c(Y_T; ξ_T)D_T/P_T] ≥ M̲ β^t u_c(Y_t; ξ_t)/P_t` for every `T ≥ t`. -/
theorem tvcDebt_lower_bound (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β)
    {lam P i im Ms D : ℕ → Ω → ℝ} {Mlow : ℝ}
    (hfis : FisherEq 𝔼 β lam P i) (h115 : ∀ t, i t = im t) (him0 : ∀ t, im t = 0)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (hmu : 𝔼.Adapted (mu lam P))
    (hmuinv : ∀ t, 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹)
    (hMs : ∀ t ω, Mlow ≤ Ms t ω) (hD : ∀ t ω, Ms t ω ≤ D t ω) {t T : ℕ} (hT : t ≤ T)
    (ω : Ω) :
    Mlow * (β ^ t * mu lam P t ω) ≤
      β ^ T * 𝔼.E t (fun ω' => lam T ω' * D T ω' / P T ω') ω := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
  have hit := congrFun (beta_pow_E_mu 𝔼 hP hfis h115 him0 hlam hPpos hmu hmuinv t n) ω
  simp only [Pi.smul_apply, smul_eq_mul] at hit
  have hle : Mlow • mu lam P (t + n) ≤ fun ω' => lam (t + n) ω' * D (t + n) ω' / P (t + n) ω' :=
    fun ω' => by
      simp only [Pi.smul_apply, smul_eq_mul, mu]
      rw [mul_div_right_comm, mul_comm]
      exact mul_le_mul_of_nonneg_left ((hMs _ ω').trans (hD _ ω'))
        (div_pos (hlam _ ω') (hPpos _ ω')).le
  have hE := 𝔼.mono t hle ω
  rw [ExpectationSystem.E_smul, Pi.smul_apply, smul_eq_mul] at hE
  rw [← hit]
  have := mul_le_mul_of_nonneg_left hE (pow_pos hβ (t + n)).le
  linarith

/-- Woodford (2003), Proposition 2.4, p. 82, proof A.5, pp. 637–638: if the monetary base is
bounded below by `M̲ > 0`, government debt is nonnegative (`D_t ≥ M^s_t`) and `i^m_t = 0`, then no
price process satisfying (1.15) and (1.21) satisfies the transversality condition (1.24). -/
theorem prop_2_4 [Nonempty Ω] (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β)
    {lam P i im Ms D : ℕ → Ω → ℝ} {Mlow : ℝ} (hMlow : 0 < Mlow)
    (hfis : FisherEq 𝔼 β lam P i) (h115 : ∀ t, i t = im t) (him0 : ∀ t, im t = 0)
    (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω) (hmu : 𝔼.Adapted (mu lam P))
    (hmuinv : ∀ t, 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹)
    (hMs : ∀ t ω, Mlow ≤ Ms t ω) (hD : ∀ t ω, Ms t ω ≤ D t ω) :
    ¬ TVCDebt 𝔼 β lam P D := by
  intro htvc
  obtain ⟨ω⟩ := ‹Nonempty Ω›
  have hpos : 0 < Mlow * (β ^ 0 * mu lam P 0 ω) :=
    mul_pos hMlow (mul_pos (pow_pos hβ 0) (mu_pos hlam hPpos 0 ω))
  have hle : Mlow * (β ^ 0 * mu lam P 0 ω) ≤ 0 :=
    ge_of_tendsto (htvc 0 ω) (Filter.Eventually.of_forall fun T =>
      tvcDebt_lower_bound 𝔼 hP hβ hfis h115 him0 hlam hPpos hmu hmuinv hMs hD (Nat.zero_le T) ω)
  linarith

/-- Woodford (2003), Proposition 2.4 with Proposition 2.2, pp. 72, 82 and 638: under the same
policy, the household transversality condition (1.22) also fails, for total liabilities given by
the identity of p. 628 and bounded below by the monetary base. -/
theorem not_tvcWealth [Nonempty Ω] (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β)
    {lam P q i im Ms Ws : ℕ → Ω → ℝ} {Mlow : ℝ} (hMlow : 0 < Mlow)
    (heu : EulerSDF β lam P q) (hfis : FisherEq 𝔼 β lam P i) (h115 : ∀ t, i t = im t)
    (him0 : ∀ t, im t = 0) (hlam : ∀ t ω, 0 < lam t ω) (hPpos : ∀ t ω, 0 < P t ω)
    (hmu : 𝔼.Adapted (mu lam P))
    (hmuinv : ∀ t, 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹)
    (hMsad : 𝔼.Adapted Ms) (hMs : ∀ t ω, Mlow ≤ Ms t ω)
    (hD : ∀ t ω, Ms t ω ≤ debt 𝔼 q im Ms Ws t ω) :
    ¬ TVCWealth 𝔼 β lam P Ws := by
  have him : 𝔼.Adapted im := fun t => by rw [him0 t, map_zero]
  have hi : ∀ t ω, 0 < 1 + i t ω := fun t ω => by simp [h115 t, him0 t]
  rw [prop_2_2 𝔼 hP heu hfis h115 hlam hPpos hi hmu him hMsad]
  exact prop_2_4 𝔼 hP hβ hMlow hfis h115 him0 hlam hPpos hmu hmuinv hMs hD

/-- Woodford (2003), Proposition 2.4, p. 82: under a regime with `M^s_t ≥ M̲ > 0`, `D_t ≥ M^s_t`
and `i^m_t = 0`, there is no rational-expectations equilibrium (Definition, p. 72) for any price
process whose marginal utility of nominal wealth `μ_t` (and its inverse) is known at `t`. -/
theorem no_REE [Nonempty Ω] (hP : 𝔼.PullOut) {β : ℝ} (hβ : 0 < β)
    {lam im Ms Ws D Y : ℕ → Ω → ℝ} {Mlow : ℝ} (hMlow : 0 < Mlow) (him0 : ∀ t, im t = 0)
    (hlam : ∀ t ω, 0 < lam t ω) (hMs : ∀ t ω, Mlow ≤ Ms t ω) (hD : ∀ t ω, Ms t ω ≤ D t ω)
    (P i : ℕ → Ω → ℝ) (hmu : 𝔼.Adapted (mu lam P))
    (hmuinv : ∀ t, 𝔼.E t (fun ω => (mu lam P t ω)⁻¹) = fun ω => (mu lam P t ω)⁻¹) :
    ¬ REE 𝔼 β lam P i im Ws D Y := fun h =>
  prop_2_4 𝔼 hP hβ hMlow h.fisher h.zeroSpread him0 hlam h.pricePos hmu hmuinv hMs hD
    h.tvcDebt

/-- Woodford (2003), A.5, p. 638 (the hypotheses of `prop_2_4` are not vacuous): under perfect
foresight with constant marginal utility `λ = 1`, the deflation `P_t = β^t` satisfies the Fisher
equation (1.21) with `i = i^m = 0`, i.e. (1.15) and (1.21) hold; only the transversality
condition (1.24) excludes it. -/
theorem fisher_deflation_path {β : ℝ} (hβ : 0 < β) :
    FisherEq perfectForesight β (fun _ _ => 1) (fun t _ => β ^ t) (fun _ _ => 0) := by
  intro t ω
  change 1 + 0 = β⁻¹ * (1 / 1 * (β ^ t / β ^ (t + 1)))⁻¹
  have := hβ.ne'
  rw [pow_succ]
  field_simp
  norm_num

end Woodford.PriceLevelDetermination.NoBubble
