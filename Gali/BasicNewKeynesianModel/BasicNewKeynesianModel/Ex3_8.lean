/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import BasicNewKeynesianModel.Ex3_5

/-!
# Exercise 3.8: a New Keynesian economy with linear utility

Galí (2015), Chapter 3, Exercise 3.8, p. 96. Period utility
`U(C, N) = C − N^{1+φ}/(1 + φ)`, technology `Y = A N`, constant desired markup,
Calvo pricing, perfectly competitive labour market.

* (a) `natural_levels`, `natural_logs`: `nⁿ = (a − μ)/φ` and
  `yⁿ = ((1 + φ) a − μ)/φ`; `natural_employment_strictMono`: natural employment
  rises with technology (the claim illustrated by the diagram of (b)).
* (b) is a labour-market diagram; it is not formalised.
* (c) `euler_real_rate`: with constant marginal utility the Euler equation
  pins the expected real return at `1/β` at every date, i.e. `r = ρ`;
  `hasDerivAt_euler_path`: its exact linearisation is `i_t = ρ + E_t π_{t+1}`.
* (d) `natural_allocation_replicated`: under `i_t = ρ + φ_π π_t` with
  `φ_π > 1`, `π = ỹ = 0` (the natural allocation) with `i = ρ` is an
  equilibrium and it is the unique bounded one.
-/

namespace Gali.BasicNewKeynesianModel.Ex3_8

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-! ### (a) Natural employment and output -/

/-- **Natural employment and output in levels** (Galí (2015), Ex. 3.8(a), p. 96):
with flexible prices `P = M W/A`, labour supply `W/P = N^φ` (the marginal rate of
substitution with linear utility) and `Y = A N`: `φ log N = log A − log M` and
`φ log Y = (1 + φ) log A − log M`, exactly. -/
theorem natural_levels {φ M P W A Y Nl : ℝ} (hφ : 0 < φ) (hM : 0 < M) (hP : 0 < P)
    (hA : 0 < A) (hN : 0 < Nl) (hflex : P = M * (W / A)) (hls : W / P = Nl ^ φ)
    (hy : Y = A * Nl) :
    Real.log Nl = (Real.log A - Real.log M) / φ ∧
      Real.log Y = ((1 + φ) * Real.log A - Real.log M) / φ := by
  have hWA : 0 < W / A := pos_of_mul_pos_right (hflex ▸ hP) hM.le
  have hW0 : 0 < W := by
    have := mul_pos hWA hA
    rwa [div_mul_cancel₀ W hA.ne'] at this
  have hW : W / P = A / M := by
    rw [hflex]; field_simp
  rw [hW] at hls
  have h1 := congrArg Real.log hls
  rw [Real.log_div hA.ne' hM.ne', Real.log_rpow hN] at h1
  have hn : Real.log Nl = (Real.log A - Real.log M) / φ := by
    rw [eq_div_iff hφ.ne']; linarith
  refine ⟨hn, ?_⟩
  rw [hy, Real.log_mul hA.ne' hN.ne', hn]
  field_simp
  ring

/-- **Natural employment and output in logs** (Galí (2015), Ex. 3.8(a), p. 96):
flexible prices `p = μ + w − a`, labour supply `w − p = φ n` and `y = a + n` give
`nⁿ = (a − μ)/φ` and `yⁿ = ((1 + φ) a − μ)/φ`. -/
theorem natural_logs {φ μ p w a y n : ℝ} (hφ : φ ≠ 0) (hflex : p = μ + (w - a))
    (hls : w - p = φ * n) (hy : y = a + n) :
    n = (a - μ) / φ ∧ y = ((1 + φ) * a - μ) / φ := by
  have hn : n = (a - μ) / φ := by
    rw [eq_div_iff hφ]; linarith
  refine ⟨hn, ?_⟩
  rw [hy, hn]
  field_simp
  ring

/-- **Natural employment always rises with technology** (Galí (2015),
Ex. 3.8(b), p. 96): `a ↦ (a − μ)/φ` is strictly increasing for `φ > 0`, because
with linear utility there is no wealth effect on labour supply. -/
theorem natural_employment_strictMono {φ : ℝ} (hφ : 0 < φ) (μ : ℝ) :
    StrictMono fun a : ℝ => (a - μ) / φ := by
  intro a b hab
  exact div_lt_div_of_pos_right (by linarith) hφ

/-! ### (c) The Euler equation and the real interest rate -/

/-- **A constant real interest rate** (Galí (2015), Ex. 3.8(c), p. 96). With
linear utility the marginal utility of consumption is `1` at every date, so the
Euler equation for a nominal bond reads
`1 = β (1 + i_t) E_t[P_t/P_{t+1}]`. Hence the expected gross real return is
`(1 + i_t) E_t[P_t/P_{t+1}] = 1/β` at every date, and its log is `ρ = −log β`,
whatever the path of consumption. -/
theorem euler_real_rate {β : ℝ} (hβ : 0 < β) {i P : ℕ → Ω → ℝ}
    (heuler : ∀ t ω, 1 = β * (1 + i t ω) * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω)
    (t : ℕ) (ω : Ω) :
    (1 + i t ω) * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω = 1 / β ∧
      Real.log ((1 + i t ω) * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω) = -Real.log β := by
  have h := heuler t ω
  have hR : (1 + i t ω) * 𝔼.E t (fun ω' => P t ω' / P (t + 1) ω') ω = 1 / β := by
    rw [eq_div_iff hβ.ne']; linarith
  refine ⟨hR, ?_⟩
  rw [hR, one_div, Real.log_inv]

/-- **Exact linearisation of the Euler equation** (Galí (2015), Ex. 3.8(c),
p. 96). Write `1 + i_t = exp(i_t)`, `P_t/P_{t+1} = exp(−π_{t+1})` and
`β = e^{−ρ}`, and perturb the steady state `i = ρ`, `π = 0` along
`i_t = ρ + s î`, `π_{t+1} = s π̂` with `π̂` bounded. The Euler residual
`β e^{i_t} E_t[e^{−π_{t+1}}]` has derivative `î − E_t π̂` at `s = 0`, so to first
order `i_t = ρ + E_t π_{t+1}`: the real rate `i_t − E_t π_{t+1}` equals `ρ`. -/
theorem hasDerivAt_euler_path {ρ B ihat : ℝ} {πhat : Ω → ℝ} (hπ : ∀ ω, |πhat ω| ≤ B)
    (t : ℕ) (ω : Ω) :
    HasDerivAt (fun s => Real.exp (-ρ) * Real.exp (ρ + s * ihat) *
        𝔼.E t (fun ω' => Real.exp (s * -πhat ω')) ω)
      (ihat - 𝔼.E t πhat ω) 0 := by
  have hg := Ex3_5.hasDerivAt_E_exp 𝔼 (g := fun ω' => -πhat ω') (B := B)
    (fun ω' => by rw [abs_neg]; exact hπ ω') t ω 0
  have he : HasDerivAt (fun s : ℝ => Real.exp (ρ + s * ihat)) (Real.exp (ρ + 0 * ihat) * ihat) 0 :=
    by simpa using ((((hasDerivAt_id (0 : ℝ)).mul_const ihat).const_add ρ).exp)
  have h := (he.const_mul (Real.exp (-ρ))).mul hg
  refine h.congr_deriv ?_
  have h1 : 𝔼.E t (fun ω' => Real.exp (0 * -πhat ω')) ω = 1 := by
    simp only [zero_mul, Real.exp_zero]
    rw [𝔼.const]
  have h2 : 𝔼.E t (fun ω' => -πhat ω' * Real.exp (0 * -πhat ω')) ω = -𝔼.E t πhat ω := by
    simp only [zero_mul, Real.exp_zero, mul_one]
    rw [show (fun ω' => -πhat ω') = -πhat from rfl, map_neg, Pi.neg_apply]
  have h3 : Real.exp (-ρ) * Real.exp ρ = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [h1, h2, zero_mul, add_zero]
  linear_combination (ihat - 𝔼.E t πhat ω) * h3

/-! ### (d) An interest-rate rule that replicates the natural allocation -/

/-- **The rule `i = ρ + φ_π π` replicates the natural allocation** (Galí (2015),
Ex. 3.8(d), p. 96). The equilibrium conditions are the linearised Euler
equation `i_t = ρ + E_t π_{t+1}` (part (c)) and the NKPC
`π_t = β E_t π_{t+1} + κ ỹ_t` with `κ > 0`. Under the rule
`i_t = ρ + φ_π π_t`, `φ_π > 1` (finite coefficients, observables only):
(i) `π = ỹ = 0`, `i = ρ` is an equilibrium; (ii) every equilibrium with bounded
adapted inflation has `π = 0` and `ỹ = 0`, so `y = yⁿ`, and `i = ρ`. The
reason: Euler and the rule give `π_t = φ_π⁻¹ E_t π_{t+1}`, whose only bounded
solution is zero. -/
theorem natural_allocation_replicated {ρ β κ φπ : ℝ} (hκ : 0 < κ) (hφ : 1 < φπ) :
    ((∀ t : ℕ, (fun _ => ρ) = ((fun _ => ρ) + 𝔼.E t (0 : Ω → ℝ) : Ω → ℝ)) ∧
      (∀ t : ℕ, (0 : Ω → ℝ) = β • 𝔼.E t 0 + κ • (0 : Ω → ℝ)) ∧
      ((fun _ => ρ) : Ω → ℝ) = (fun _ => ρ) + φπ • (0 : Ω → ℝ)) ∧
    ∀ ytil infl i : ℕ → Ω → ℝ,
      (∀ t, i t = (fun _ => ρ) + 𝔼.E t (infl (t + 1))) →
      (∀ t, infl t = β • 𝔼.E t (infl (t + 1)) + κ • ytil t) →
      (∀ t, i t = (fun _ => ρ) + φπ • infl t) →
      BoundedProc infl → ∀ t, infl t = 0 ∧ ytil t = 0 ∧ i t = fun _ => ρ := by
  refine ⟨⟨fun t => by simp, fun t => by simp, by simp⟩, ?_⟩
  intro ytil infl i heuler hpc hrule hb
  have hφ0 : φπ ≠ 0 := by linarith
  have hfwd : ∀ t, infl t = φπ⁻¹ • 𝔼.E t (infl (t + 1)) + 0 := by
    intro t
    have h := (heuler t).symm.trans (hrule t)
    have h' : 𝔼.E t (infl (t + 1)) = φπ • infl t := add_left_cancel h
    rw [h', smul_smul, inv_mul_cancel₀ hφ0, one_smul, add_zero]
  have hzero : ∀ t, (0 : ℕ → Ω → ℝ) t = φπ⁻¹ • 𝔼.E t ((0 : ℕ → Ω → ℝ) (t + 1)) + 0 :=
    fun t => by simp
  have ha : |φπ⁻¹| < 1 := by
    rw [abs_inv, abs_of_pos (by linarith)]
    exact inv_lt_one_of_one_lt₀ hφ
  have h0 := 𝔼.forward_unique ha hfwd hzero hb ⟨0, fun t ω => by simp⟩
  intro t
  have hi : infl t = 0 := congrFun h0 t
  have hi1 : infl (t + 1) = 0 := congrFun h0 (t + 1)
  have hy : ytil t = 0 := by
    have h := hpc t
    rw [hi, hi1, map_zero, smul_zero, zero_add] at h
    have : κ • ytil t = 0 := h.symm
    exact (smul_eq_zero.mp this).resolve_left hκ.ne'
  refine ⟨hi, hy, ?_⟩
  rw [hrule t, hi, smul_zero, add_zero]

end Gali.BasicNewKeynesianModel.Ex3_8
