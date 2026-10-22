/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergBoundary
import StabilizationWelfare.NonlinearRotembergRamseyDegenerate

/-!
# The Taylor-principle boundary: the linearisation does not decide determinacy

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.3 (p. 254) and Appendix A.3
(pp. 632–634), for the exact Rotemberg model of `NonlinearRotemberg` under perfect foresight with
no disturbances. On the boundary `κ(φ_π − 1) + (1 − β)φ_y = 0` (with `φ_y ≥ 0`) the linearised
model has a unit root (`NonlinearRotembergBoundary.boundary_linear_kernel`).

Two exact Rotemberg economies are built that differ only in a nonlinear interest-rate rule
`î = Ψ(ŷ, π)`. Both rules have the same linearisation as the boundary Taylor rule
`φ_π π + φ_y ŷ` (`ruleA_linear`, `ruleB_sub_ruleA`), so the two economies have IDENTICAL
linearisations, but opposite answers:

* **`modelA_continuum`**: with `Ψ_A = π + k ε(ŷ, π)` (`k = −φ_y/(θm(σ+ω))`, `ε` the pricing
  steady-state residual), every point of the pricing steady-state curve is an exact steady state:
  a continuum of perfect-foresight equilibria through the steady state (non-uniqueness).
* **`modelB_unique`**: with `Ψ_B = Ψ_A + χ L³` (`χ > 0`, `L = σĉ + π − kβG`), the exact recursion
  `L_{t+1} = L_t + χL_t³` (`modelB_L_rec`) forces `L ≡ 0` on bounded paths, and on `L = 0` inflation
  expands by a factor `> 1` each period: the steady state is the ONLY perfect-foresight equilibrium
  that stays within `r` of it.

What stays open is the answer for the LINEAR boundary Taylor rule itself: it depends on the
second-order (transcritical) coefficient of the centre-manifold dynamics, which is not formalised.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergBoundaryPair

open Filter Topology
open NonlinearRotemberg
open NonlinearRotembergLinks (wedge hasDerivAt_wedge)
open NonlinearRotembergBoundary (small_remainder fderiv_Qmap_apply fderiv_Nmap_apply sss ssY
  corner_steady sss_zero)
open NonlinearRotembergRamseyDegenerate (geom_bounded_zero)

variable {p : Par}

/-! ## The rules -/

/-- Consumption from the resource constraint, `ĉ*(ŷ, π) = ŷ + log(C/Y)`. -/
noncomputable def mstar (p : Par) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![z 0, z 1, z 0 + Real.log (wedge p.ψ (z 1))]

/-- Woodford (2003), Ch. 3 fn. 44: the pricing steady-state residual `(1−β)G − H`. -/
noncomputable def eps (p : Par) (z : Fin 3 → ℝ) : ℝ := (Qmap p (0, z) + Nmap p (0, z)) 1

/-- The rule coefficient `k = −φ_y/(θm(σ+ω))`. -/
noncomputable def kc (p : Par) : ℝ := -p.φy / (p.θ * p.m * (p.σ + p.ω))

/-- The conserved quantity of model A, `L = σĉ + π − kβG`. -/
noncomputable def Lf (p : Par) (z : Fin 3 → ℝ) : ℝ := p.σ * z 2 + z 1 - kc p * p.β * Gadj p z

/-- Woodford (2003), Prop. 4.3: rule A, `Ψ_A = π + k ε(ŷ, π, ĉ*)`. -/
noncomputable def ruleA (p : Par) (z : Fin 3 → ℝ) : ℝ := z 1 + kc p * eps p (mstar p z)

/-- Woodford (2003), Prop. 4.3: rule B, `Ψ_B = Ψ_A + χ L(ŷ, π, ĉ*)³`. -/
noncomputable def ruleB (p : Par) (χ : ℝ) (z : Fin 3 → ℝ) : ℝ :=
  ruleA p z + χ * Lf p (mstar p z) ^ 3

/-- Woodford (2003), Ch. 4 (2.7)–(2.8) with the rule `î = Ψ(ŷ, π)` (**exact perfect-foresight
equilibrium, no disturbances**): the Euler equation, the pricing condition and the resource
constraint at every date. -/
def PFR (p : Par) (Ψ : (Fin 3 → ℝ) → ℝ) (z : ℕ → Fin 3 → ℝ) : Prop :=
  ∀ t, Real.exp (-(Ψ (z t) + p.σ * z t 2)) = Real.exp (-(p.σ * z (t + 1) 2) - z (t + 1) 1) ∧
    Qmap p (0, z t) 1 + Nmap p (0, z (t + 1)) 1 = 0 ∧ Qmap p (0, z t) 2 = 0

/-! ## Remainders -/

/-- The scalar remainder of `log(C/Y)` at zero inflation: `|log w(π)| ≤ η|π|` near `0`. -/
theorem rem_logw (ψ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ π : ℝ, |π| < ρ → |Real.log (wedge ψ π)| ≤ η * |π| := by
  have hw0 : wedge ψ 0 = 1 := by simp [wedge]
  have hd : HasDerivAt (fun π => Real.log (wedge ψ π)) 0 0 := by
    have := (hasDerivAt_wedge ψ 0).log (by rw [hw0]; norm_num)
    simpa [hw0] using this
  obtain ⟨ρ, hρ, h⟩ := small_remainder hd.differentiableAt hη
  refine ⟨ρ, hρ, fun π hπ => ?_⟩
  have h1 := h π (by simpa using hπ)
  have hf : fderiv ℝ (fun π => Real.log (wedge ψ π)) 0 π = 0 := by
    rw [hd.hasFDerivAt.fderiv]; simp
  rw [hf, hw0, Real.log_one, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h1
  exact h1

/-- The one-point remainders of `Q` and `N` at the steady state, in the states. -/
theorem rem_QN {η : ℝ} (hη : 0 < η) : ∃ ρ > 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ →
    ‖Qmap p (0, z) - Qmap p 0 - DQ0 p z‖ ≤ η * ‖z‖ ∧
      ‖Nmap p (0, z) - Nmap p 0 - DN0 p z‖ ≤ η * ‖z‖ := by
  obtain ⟨ρ1, hρ1, h1⟩ := small_remainder
    ((contDiff_Qmap (p := p) (n := 1)).differentiable one_ne_zero 0) hη
  obtain ⟨ρ2, hρ2, h2⟩ := small_remainder
    ((contDiff_Nmap (p := p) (n := 1)).differentiable one_ne_zero 0) hη
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun z hz => ?_⟩
  have hn : ‖((0 : Fin 3 → ℝ), z)‖ = ‖z‖ := by simp [Prod.norm_def]
  have a := h1 (0, z) (by rw [hn]; exact hz.trans_le (min_le_left _ _))
  have b := h2 (0, z) (by rw [hn]; exact hz.trans_le (min_le_right _ _))
  rw [fderiv_Qmap_apply, hn] at a
  rw [fderiv_Nmap_apply, hn] at b
  have e : DQe p 0 = 0 := by funext i; fin_cases i <;> simp [DQe]
  rw [e, zero_add] at a
  exact ⟨a, b⟩

/-! ## Same linearisation -/

/-- Woodford (2003), Prop. 4.3 (**rule A is the boundary Taylor rule to first order**): on the
boundary, `|Ψ_A(z) − (φ_π π + φ_y ŷ)| ≤ η‖z‖` near the steady state, for every `η > 0`. -/
theorem ruleA_linear (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) {η : ℝ}
    (hη : 0 < η) : ∃ ρ > 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ →
      |ruleA p z - (p.φ * z 1 + p.φy * z 0)| ≤ η * ‖z‖ := by
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hk := hp.κ_mul
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm0 : p.m ≠ 0 := hp.m_pos.ne'
  have hs0 : p.σ + p.ω ≠ 0 := hs.ne'
  have hψ0 : p.ψ ≠ 0 := hp.ψ_pos.ne'
  have hθmσ : 0 < p.θ * p.m * p.σ := mul_pos hθm hp.σ_pos
  set A := |kc p| + 1
  have hA : 0 < A := by positivity
  have hA1 : 0 < 4 * A * (1 + p.θ * p.m * p.σ) := by positivity
  set η1 := η / (4 * A * (1 + p.θ * p.m * p.σ))
  have hη1 : 0 < η1 := div_pos hη hA1
  obtain ⟨ρ1, hρ1, hQN⟩ := rem_QN (p := p) hη1
  obtain ⟨ρ2, hρ2, hw⟩ := rem_logw p.ψ (by positivity : (0 : ℝ) < min η1 1)
  refine ⟨min (ρ1 / 2) ρ2, lt_min (by positivity) hρ2, fun z hz => ?_⟩
  have hz1 : |z 1| ≤ ‖z‖ := by simpa using norm_le_pi_norm z 1
  have hz0 : |z 0| ≤ ‖z‖ := by simpa using norm_le_pi_norm z 0
  have hzn := norm_nonneg z
  have hlog := hw (z 1) (lt_of_le_of_lt hz1 (hz.trans_le (min_le_right _ _)))
  set lw := Real.log (wedge p.ψ (z 1))
  have hlw : |lw| ≤ η1 * ‖z‖ := hlog.trans (mul_le_mul (min_le_left _ _) hz1 (abs_nonneg _)
    hη1.le)
  have hlw1 : |lw| ≤ ‖z‖ := hlog.trans (by
    have := mul_le_mul (min_le_right η1 1) hz1 (abs_nonneg _) zero_le_one; linarith)
  have hm : ‖mstar p z‖ ≤ 2 * ‖z‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    fin_cases i <;> simp only [mstar, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Real.norm_eq_abs]
    · linarith
    · linarith
    · exact (abs_add_le _ _).trans (by linarith)
  have hmlt : ‖mstar p z‖ < ρ1 := by
    have := hz.trans_le (min_le_left _ _); linarith
  obtain ⟨hq, hn⟩ := hQN _ hmlt
  have hss := steadyState_zero (p := p)
  -- the residual of `ε` at `m = mstar z`
  have he : |eps p (mstar p z) - (DQ0 p (mstar p z) 1 + DN0 p (mstar p z) 1)| ≤
      2 * η1 * ‖mstar p z‖ := by
    have e : eps p (mstar p z) - (DQ0 p (mstar p z) 1 + DN0 p (mstar p z) 1) =
        (Qmap p (0, mstar p z) - Qmap p 0 - DQ0 p (mstar p z)) 1 +
          (Nmap p (0, mstar p z) - Nmap p 0 - DN0 p (mstar p z)) 1 := by
      have h1 := congrFun hss 1
      simp only [Pi.add_apply, Pi.zero_apply] at h1
      simp only [eps, Pi.add_apply, Pi.sub_apply]
      rw [show (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) = (0, 0) from rfl]
      linarith
    rw [e]
    have a1 := (norm_le_pi_norm _ 1).trans hq
    have a2 := (norm_le_pi_norm _ 1).trans hn
    rw [Real.norm_eq_abs] at a1 a2
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ η1 * ‖mstar p z‖ + η1 * ‖mstar p z‖ := add_le_add a1 a2
      _ = _ := by ring
  -- the linear part
  have hlin : DQ0 p (mstar p z) 1 + DN0 p (mstar p z) 1 =
      (1 - p.β) * p.ψ * z 1 - p.θ * p.m * (p.σ + p.ω) * z 0 - p.θ * p.m * p.σ * lw := by
    simp only [DQ0, DN0, mstar, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val, lw]
    ring
  have hφ : p.φ = 1 + kc p * ((1 - p.β) * p.ψ) := by
    have hκ0 := hp.κ_pos.ne'
    unfold kc
    rw [← hk]
    field_simp
    linear_combination hb
  have hφy : p.φy = -(kc p * (p.θ * p.m * (p.σ + p.ω))) := by
    unfold kc; field_simp
  have key : ruleA p z - (p.φ * z 1 + p.φy * z 0) =
      kc p * (eps p (mstar p z) - (DQ0 p (mstar p z) 1 + DN0 p (mstar p z) 1)) -
        kc p * (p.θ * p.m * p.σ * lw) := by
    rw [hlin, hφ, hφy]; unfold ruleA; ring
  rw [key]
  have hkA : |kc p| ≤ A := by simp only [A]; linarith
  calc _ ≤ |kc p * (eps p (mstar p z) - (DQ0 p (mstar p z) 1 + DN0 p (mstar p z) 1))| +
        |kc p * (p.θ * p.m * p.σ * lw)| := abs_sub _ _
    _ ≤ A * (2 * η1 * (2 * ‖z‖)) + A * (p.θ * p.m * p.σ * (η1 * ‖z‖)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hθmσ]
        have := abs_nonneg lw
        gcongr
        · exact he.trans (by gcongr)
    _ ≤ η * ‖z‖ := by
        have e : A * (2 * η1 * (2 * ‖z‖)) + A * (p.θ * p.m * p.σ * (η1 * ‖z‖)) =
            η1 * (4 * A * (1 + p.θ * p.m * p.σ)) * ‖z‖ - A * (p.θ * p.m * p.σ) * (3 * η1) *
              ‖z‖ := by ring
        have e2 : η1 * (4 * A * (1 + p.θ * p.m * p.σ)) = η := by
          simp only [η1]; field_simp
        rw [e, e2]
        have : 0 ≤ A * (p.θ * p.m * p.σ) * (3 * η1) * ‖z‖ :=
          mul_nonneg (mul_nonneg (mul_nonneg hA.le hθmσ.le) (by positivity)) hzn
        linarith

/-! ## Model A: a continuum of steady states -/

/-- The corner parameters `φ_π = 1`, `φ_y = 0` with the other parameters of `p`. -/
def corner (p : Par) : Par := { p with φ := 1, φy := 0 }

/-- The corner parameters satisfy the maintained restrictions. -/
theorem corner_basic (hp : p.Basic) : (corner p).Basic :=
  ⟨hp.β_pos, hp.β_lt_one, hp.one_lt_θ, hp.ω_nonneg, hp.σ_pos, hp.ψ_pos, hp.m_pos, zero_le_one,
    le_rfl⟩

/-- Woodford (2003), Prop. 4.3 and Ch. 4 (2.7) (**model A has a continuum of exact steady states,
hence of perfect-foresight equilibria**): for every `π` with `C/Y > 0` and
`1 + (1−β)ψ(e^π − 1)e^π/(θm) > 0`, the constant path at `sss π` is an exact perfect-foresight
equilibrium of the economy with rule `Ψ_A`. -/
theorem modelA_steady (hp : p.Basic) (π : ℝ) (hw : 0 < wedge p.ψ π)
    (hk : 0 < 1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m)) :
    PFR p (ruleA p) (fun _ => sss p π) := by
  have h := corner_steady (corner_basic hp) rfl rfl π hw hk
  have h1 : Qmap p (0, sss p π) 1 + Nmap p (0, sss p π) 1 = 0 := congrFun h 1
  have h2 : Qmap p (0, sss p π) 2 + Nmap p (0, sss p π) 2 = 0 := congrFun h 2
  have hN2 : Nmap p (0, sss p π) 2 = 0 := by simp [Nmap]
  have hms : mstar p (sss p π) = sss p π := by
    funext i; fin_cases i <;> simp [mstar, sss]
  intro t
  refine ⟨?_, h1, by rw [hN2, add_zero] at h2; exact h2⟩
  have hr : ruleA p (sss p π) = π := by
    unfold ruleA eps; rw [hms, Pi.add_apply, h1, mul_zero, add_zero]; simp [sss]
  rw [hr]; congr 1; simp [sss]; ring

/-- Woodford (2003), Prop. 4.3 (**model A: non-uniqueness**): there is `ρ > 0` such that every
`|π| < ρ` gives an exact perfect-foresight equilibrium `sss π` of the rule-`Ψ_A` economy,
distinct `π` give distinct equilibria, and for every `r > 0` one with `π ≠ 0` lies within `r` of
the steady state. -/
theorem modelA_continuum (hp : p.Basic) :
    ∃ ρ > 0, (∀ π, |π| < ρ → PFR p (ruleA p) (fun _ => sss p π)) ∧
      (∀ π π', sss p π = sss p π' → π = π') ∧
      ∀ r > 0, ∃ π, π ≠ 0 ∧ |π| < ρ ∧ ‖sss p π‖ ≤ r := by
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hc1 : Continuous fun π : ℝ => wedge p.ψ π := by unfold wedge; fun_prop
  have hc2 : Continuous fun π : ℝ =>
      1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m) := by fun_prop
  have hev : ∀ᶠ π in 𝓝 (0 : ℝ), 0 < wedge p.ψ π ∧
      0 < 1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m) := by
    refine (hc1.continuousAt.eventually (lt_mem_nhds ?_)).and
      (hc2.continuousAt.eventually (lt_mem_nhds ?_))
    · simp [wedge]
    · simp
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨ρ', -, -, hsmall⟩ := NonlinearRotembergBoundary.corner_continuum (corner_basic hp) rfl rfl
  refine ⟨ρ, hρ, fun π hπ => ?_, fun π π' h => ?_, fun r hr => ?_⟩
  · have hpos := hball (by simpa [Real.dist_eq] using hπ)
    exact modelA_steady hp π hpos.1 hpos.2
  · have := congrFun h 1
    simpa [sss] using this
  · -- continuity of `sss` at zero
    have hcont : ContinuousAt (sss p) 0 := by
      have h1 : ContinuousAt (ssY p) 0 := by
        unfold ssY
        refine ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) _
        · exact (hc2.continuousAt).log (by simp)
        · exact (hc1.continuousAt.log (by simp [wedge])).const_mul _
      refine continuousAt_pi.2 fun i => ?_
      fin_cases i
      · exact h1
      · exact continuousAt_id
      · exact h1.add (hc1.continuousAt.log (by simp [wedge]))
    have ht : Tendsto (sss p) (𝓝 0) (𝓝 0) := by
      have := hcont.tendsto; rwa [sss_zero] at this
    have h1 : ∀ᶠ π in 𝓝 (0 : ℝ), ‖sss p π‖ ≤ r ∧ |π| < ρ :=
      (ht.eventually (Metric.closedBall_mem_nhds 0 hr)).and
        (Metric.ball_mem_nhds 0 hρ) |>.mono fun π h => ⟨by simpa using h.1, by simpa using h.2⟩
    have h2 : ∀ᶠ π in 𝓝[≠] (0 : ℝ), (‖sss p π‖ ≤ r ∧ |π| < ρ) ∧ π ∈ ({0}ᶜ : Set ℝ) :=
      (h1.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨π, hπ, hne⟩ := h2.exists
    exact ⟨π, hne, hπ.2, hπ.1⟩


/-! ## Model B -/

/-- `|G(z) − ψπ| ≤ η‖z‖/β` and the pricing remainder near the steady state. -/
theorem rem_G (hp : p.Basic) {η : ℝ} (hη : 0 < η) : ∃ ρ > 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ →
    |Gadj p z - p.ψ * z 1| ≤ η / p.β * ‖z‖ ∧
      |Gadj p z - Hmc p 0 z - (p.ψ * z 1 - p.θ * p.m * (p.ω * z 0 + p.σ * z 2))| ≤ η * ‖z‖ := by
  obtain ⟨ρ, hρ, h⟩ := rem_QN (p := p) hη
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  obtain ⟨hq, hn⟩ := h z hz
  have hβ := hp.β_pos
  have a1 := (norm_le_pi_norm _ 1).trans hq
  have a2 := (norm_le_pi_norm _ 1).trans hn
  rw [Real.norm_eq_abs] at a1 a2
  have q0 : Qmap p 0 1 = 0 := by simp [Qmap, Gadj, Hmc]
  have n0 : Nmap p 0 1 = 0 := by simp [Nmap, Gadj]
  simp only [Pi.sub_apply] at a1 a2
  rw [show (0 : (Fin 3 → ℝ) × (Fin 3 → ℝ)) = (0, 0) from rfl] at a1 a2
  have q0' : Qmap p (0, 0) 1 = 0 := q0
  have n0' : Nmap p (0, 0) 1 = 0 := n0
  rw [q0', sub_zero] at a1
  rw [n0', sub_zero] at a2
  simp only [Qmap, Nmap, DQ0, DN0, Matrix.cons_val_one, Matrix.cons_val_zero] at a1 a2
  refine ⟨?_, a1⟩
  have : |-(p.β * Gadj p z) - -(p.β * p.ψ * z 1)| = p.β * |Gadj p z - p.ψ * z 1| := by
    rw [show -(p.β * Gadj p z) - -(p.β * p.ψ * z 1) = -(p.β * (Gadj p z - p.ψ * z 1)) by ring,
      abs_neg, abs_mul, abs_of_pos hβ]
  rw [this] at a2
  calc |Gadj p z - p.ψ * z 1| = p.β * |Gadj p z - p.ψ * z 1| / p.β := by field_simp
    _ ≤ η * ‖z‖ / p.β := by gcongr
    _ = η / p.β * ‖z‖ := by ring

/-- Woodford (2003), Prop. 4.3 (**rules A and B have the same linearisation**): for every `η > 0`,
`|Ψ_B(z) − Ψ_A(z)| ≤ η‖z‖` near the steady state. -/
theorem ruleB_sub_ruleA (hp : p.Basic) (χ : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ → |ruleB p χ z - ruleA p z| ≤ η * ‖z‖ := by
  have hβ := hp.β_pos
  have hσ := hp.σ_pos
  obtain ⟨ρ1, hρ1, hG⟩ := rem_G hp one_pos
  obtain ⟨ρ2, hρ2, hw⟩ := rem_logw p.ψ one_pos
  set CL := 2 * p.σ + 1 + |kc p| * p.β * (p.ψ + 2 / p.β)
  have hCL : 0 ≤ CL := by have := hp.ψ_pos; positivity
  set ρ := min (min (ρ1 / 2) ρ2) (min 1 (η / (|χ| * CL ^ 3 + 1)))
  have hρ : 0 < ρ := lt_min (lt_min (by positivity) hρ2) (lt_min one_pos (by positivity))
  refine ⟨ρ, hρ, fun z hz => ?_⟩
  have hzn := norm_nonneg z
  have hz1 : |z 1| ≤ ‖z‖ := by simpa using norm_le_pi_norm z 1
  have hz0 : |z 0| ≤ ‖z‖ := by simpa using norm_le_pi_norm z 0
  have hρρ : ρ ≤ min (ρ1 / 2) ρ2 := min_le_left _ _
  have hlog := hw (z 1) (lt_of_le_of_lt hz1 (hz.trans_le (hρρ.trans (min_le_right _ _))))
  set lw := Real.log (wedge p.ψ (z 1))
  have hlw : |lw| ≤ ‖z‖ := by linarith
  have hm : ‖mstar p z‖ ≤ 2 * ‖z‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    fin_cases i <;> simp only [mstar, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Real.norm_eq_abs]
    · linarith
    · linarith
    · exact (abs_add_le _ _).trans (by linarith)
  have hmlt : ‖mstar p z‖ < ρ1 := by
    have := hz.trans_le (hρρ.trans (min_le_left _ _)); linarith
  have hGm := (hG _ hmlt).1
  have hL : |Lf p (mstar p z)| ≤ CL * ‖z‖ := by
    have m1 : |mstar p z 1| ≤ ‖z‖ := by simpa [mstar] using hz1
    have m2 : |mstar p z 2| ≤ 2 * ‖z‖ := by
      simp only [mstar, Matrix.cons_val]; exact (abs_add_le _ _).trans (by linarith)
    have hg : |Gadj p (mstar p z)| ≤ (p.ψ + 2 / p.β) * ‖z‖ := by
      have := abs_sub_abs_le_abs_sub (Gadj p (mstar p z)) (p.ψ * mstar p z 1)
      rw [abs_mul, abs_of_pos hp.ψ_pos] at this
      have h2 : 1 / p.β * ‖mstar p z‖ ≤ 2 / p.β * ‖z‖ := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hβ]; linarith
      nlinarith [hp.ψ_pos]
    unfold Lf
    calc _ ≤ |p.σ * mstar p z 2| + |mstar p z 1| + |kc p * p.β * Gadj p (mstar p z)| := by
          refine (abs_sub _ _).trans ?_
          exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ p.σ * (2 * ‖z‖) + ‖z‖ + |kc p| * p.β * ((p.ψ + 2 / p.β) * ‖z‖) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos hβ]
          gcongr
      _ = CL * ‖z‖ := by simp only [CL]; ring
  have hz1' : ‖z‖ ≤ 1 := by
    have := hz.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hzη : ‖z‖ ≤ η / (|χ| * CL ^ 3 + 1) := by
    have := hz.trans_le ((min_le_right _ _).trans (min_le_right _ _)); linarith
  unfold ruleB
  rw [add_sub_cancel_left, abs_mul, abs_pow]
  have hL3 : |Lf p (mstar p z)| ^ 3 ≤ (CL * ‖z‖) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hL 3
  have e1 : |χ| * (CL * ‖z‖) ^ 3 = (|χ| * CL ^ 3) * ‖z‖ ^ 2 * ‖z‖ := by ring
  have e2 : ‖z‖ ^ 2 ≤ ‖z‖ := by nlinarith
  have e3 : (|χ| * CL ^ 3) * ‖z‖ ≤ η := by
    have h := mul_le_mul_of_nonneg_left hzη (by positivity : 0 ≤ |χ| * CL ^ 3 + 1)
    rw [mul_div_cancel₀ _ (by positivity)] at h
    nlinarith [mul_nonneg (abs_nonneg χ) (pow_nonneg hCL 3)]
  calc |χ| * |Lf p (mstar p z)| ^ 3 ≤ |χ| * (CL * ‖z‖) ^ 3 :=
        mul_le_mul_of_nonneg_left hL3 (abs_nonneg _)
    _ = (|χ| * CL ^ 3) * ‖z‖ ^ 2 * ‖z‖ := e1
    _ ≤ (|χ| * CL ^ 3) * ‖z‖ * ‖z‖ := by gcongr
    _ ≤ η * ‖z‖ := by gcongr

/-- The resource constraint gives `ĉ = ŷ + log(C/Y)` with `C/Y > 0`, so `ĉ* = ĉ`. -/
theorem resource_mstar {z : Fin 3 → ℝ} (h : Qmap p (0, z) 2 = 0) :
    0 < wedge p.ψ (z 1) ∧ mstar p z = z := by
  simp only [Qmap, Matrix.cons_val] at h
  have hw : wedge p.ψ (z 1) = Real.exp (z 2 - z 0) := by
    unfold wedge; rw [Real.exp_sub]; field_simp; linarith
  refine ⟨by rw [hw]; exact Real.exp_pos _, ?_⟩
  funext i
  fin_cases i <;> simp [mstar, hw]

/-- Woodford (2003), Prop. 4.3 (**the exact recursion of model B**): along every exact
perfect-foresight equilibrium of the rule-`Ψ_B` economy, `L_{t+1} = L_t + χL_t³`. -/
theorem modelB_L_rec (χ : ℝ) {z : ℕ → Fin 3 → ℝ} (hz : PFR p (ruleB p χ) z) (t : ℕ) :
    Lf p (z (t + 1)) = Lf p (z t) + χ * Lf p (z t) ^ 3 := by
  obtain ⟨he, hpr, hres⟩ := hz t
  have hm := (resource_mstar hres).2
  have he' := Real.exp_injective he
  have hpr' : Gadj p (z t) - Hmc p 0 (z t) - p.β * Gadj p (z (t + 1)) = 0 := by
    simp only [Qmap, Nmap, Matrix.cons_val_one, Matrix.cons_val_zero] at hpr; linarith
  have heps : eps p (z t) = p.β * (Gadj p (z (t + 1)) - Gadj p (z t)) := by
    simp only [eps, Pi.add_apply, Qmap, Nmap, Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith
  simp only [ruleB, ruleA, hm, heps] at he'
  set L0 := Lf p (z t) with hL0
  have e1 : Lf p (z (t + 1)) = p.σ * z (t + 1) 2 + z (t + 1) 1 - kc p * p.β * Gadj p (z (t + 1)) :=
    rfl
  have e0 : L0 = p.σ * z t 2 + z t 1 - kc p * p.β * Gadj p (z t) := rfl
  rw [e1]
  linear_combination he' - e0

set_option maxHeartbeats 4000000 in
-- the expansion argument has many nonlinear estimates
/-- Woodford (2003), Prop. 4.3 (**model B: the steady state is the only equilibrium near it**):
for `χ > 0` there is `r > 0` such that every exact perfect-foresight equilibrium of the
rule-`Ψ_B` economy with `‖z_t‖ ≤ r` at every date is the steady state. -/
theorem modelB_unique (hp : p.Basic) {χ : ℝ} (hχ : 0 < χ) :
    ∃ r > 0, ∀ z : ℕ → Fin 3 → ℝ, (∀ t, ‖z t‖ ≤ r) → PFR p (ruleB p χ) z → ∀ t, z t = 0 := by
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hσ := hp.σ_pos
  have hψ := hp.ψ_pos
  have hs : 0 < p.σ + p.ω := by linarith [hp.ω_nonneg]
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hk0 : kc p ≤ 0 := by
    unfold kc; exact div_nonpos_of_nonpos_of_nonneg (by linarith [hp.φy_nonneg]) (by positivity)
  set kk := |kc p|
  have hkk : kc p = -kk := by simp only [kk]; rw [abs_of_nonpos hk0]; ring
  set α' := 1 + kk * p.β * p.ψ
  have hα : 1 ≤ α' := by have : 0 ≤ kk * p.β * p.ψ := by positivity
                         simp only [α']; linarith
  set D := p.θ * p.m * (p.σ + p.ω)
  have hD : 0 < D := mul_pos hθm hs
  set μ0 := (p.ψ + D * α' / p.σ) / (p.β * p.ψ)
  have hμ0 : 1 / p.β ≤ μ0 := by
    simp only [μ0]; rw [div_le_div_iff₀ hβ (by positivity)]
    have : 0 ≤ D * α' / p.σ := by positivity
    nlinarith
  have hμ1 : 1 < μ0 := lt_of_lt_of_le (by rw [lt_div_iff₀ hβ]; linarith) hμ0
  set q := (1 + μ0) / 2
  have hq : 1 < q := by simp only [q]; linarith
  set c1 := α' / p.σ + 2
  set c2 := (kk + p.σ) / p.σ
  set Cz := 2 * c1
  set c3 := D * (kk + p.σ) / p.σ + p.θ * p.m * p.σ + 1
  have hc1 : 0 < c1 := by positivity
  have hc2 : 0 < c2 := by positivity
  have hc3 : 0 < c3 := by positivity
  set δ0 := (μ0 - 1) / (4 * (1 + μ0))
  have hδ0 : 0 < δ0 := by simp only [δ0]; apply div_pos <;> linarith
  set η := min (min 1 (1 / (2 * c2))) (δ0 * (p.β * p.ψ) / (c3 * Cz))
  have hη : 0 < η := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hη1 : η ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hηc2 : c2 * η ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left (show η ≤ 1 / (2 * c2) from
      (min_le_left _ _).trans (min_le_right _ _)) hc2.le
    rw [show c2 * (1 / (2 * c2)) = 1 / 2 by field_simp] at h; exact h
  have hηδ : c3 * η * Cz / (p.β * p.ψ) ≤ δ0 := by
    have h := min_le_right (min 1 (1 / (2 * c2))) (δ0 * (p.β * p.ψ) / (c3 * Cz))
    rw [div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at h
    nlinarith
  obtain ⟨ρ1, hρ1, hG⟩ := rem_G hp hη
  obtain ⟨ρ2, hρ2, hw⟩ := rem_logw p.ψ hη
  set r := min (ρ1 / 2) (ρ2 / 2)
  have hr0 : 0 < r := by positivity
  refine ⟨r, hr0, fun z hzB hz => ?_⟩
  have hzr : ∀ t, ‖z t‖ < ρ1 := fun t => by
    have := hzB t; have := min_le_left (ρ1 / 2) (ρ2 / 2); linarith
  have hzr2 : ∀ t, |z t 1| < ρ2 := fun t => by
    have := (show |z t 1| ≤ ‖z t‖ by simpa using norm_le_pi_norm (z t) 1).trans (hzB t)
    have := min_le_right (ρ1 / 2) (ρ2 / 2); linarith
  -- `L ≡ 0`
  have hLb : ∀ t, |Lf p (z t)| ≤ (p.σ + 1 + kk * p.β * (p.ψ + η / p.β)) * r := fun t => by
    have h1 := (hG _ (hzr t)).1
    have n0 : |z t 2| ≤ ‖z t‖ := by simpa using norm_le_pi_norm (z t) 2
    have n1 : |z t 1| ≤ ‖z t‖ := by simpa using norm_le_pi_norm (z t) 1
    have hg : |Gadj p (z t)| ≤ (p.ψ + η / p.β) * ‖z t‖ := by
      have := abs_sub_abs_le_abs_sub (Gadj p (z t)) (p.ψ * z t 1)
      rw [abs_mul, abs_of_pos hψ] at this
      nlinarith
    unfold Lf
    calc _ ≤ |p.σ * z t 2| + |z t 1| + |kc p * p.β * Gadj p (z t)| := by
          refine (abs_sub _ _).trans ?_
          exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ p.σ * ‖z t‖ + ‖z t‖ + kk * p.β * ((p.ψ + η / p.β) * ‖z t‖) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos hβ]
          gcongr
      _ = (p.σ + 1 + kk * p.β * (p.ψ + η / p.β)) * ‖z t‖ := by ring
      _ ≤ _ := by gcongr; exact hzB t
  have hL0 : ∀ s, Lf p (z s) = 0 := by
    intro s
    by_contra hne
    set a := Lf p (z s)
    set ρq := 1 + χ * a ^ 2
    have hρq : 1 < ρq := by
      have : 0 < a ^ 2 := by positivity
      simp only [ρq]; nlinarith
    have hgrow : ∀ n : ℕ, |a| ≤ |Lf p (z (s + n))| ∧ ρq ^ n * |a| ≤ |Lf p (z (s + n))| := by
      intro n
      induction n with
      | zero => simp only [add_zero, pow_zero, one_mul]; exact ⟨le_rfl, le_rfl⟩
      | succ n ih =>
        have hrec := modelB_L_rec χ hz (s + n)
        have e : Lf p (z (s + (n + 1))) = Lf p (z (s + n)) * (1 + χ * Lf p (z (s + n)) ^ 2) := by
          rw [show s + (n + 1) = s + n + 1 by ring, hrec]; ring
        have hfac : ρq ≤ 1 + χ * Lf p (z (s + n)) ^ 2 := by
          simp only [ρq]
          have : a ^ 2 ≤ Lf p (z (s + n)) ^ 2 := by
            rw [← sq_abs a, ← sq_abs (Lf p (z (s + n)))]
            exact pow_le_pow_left₀ (abs_nonneg _) ih.1 2
          nlinarith
        rw [e, abs_mul, abs_of_pos (by positivity : 0 < 1 + χ * Lf p (z (s + n)) ^ 2)]
        constructor
        · nlinarith [abs_nonneg (Lf p (z (s + n)))]
        · rw [pow_succ]
          nlinarith [abs_nonneg (Lf p (z (s + n))), abs_nonneg a,
            pow_nonneg (by linarith : (0:ℝ) ≤ ρq) n]
    have := geom_bounded_zero (r := ρq) (a := a) (by rw [abs_of_pos (by linarith)]; exact hρq)
      (C := (p.σ + 1 + kk * p.β * (p.ψ + η / p.β)) * r) fun n => by
        rw [abs_mul, abs_pow, abs_of_pos (by linarith)]
        exact (hgrow n).2.trans (hLb (s + n))
    exact hne this
  -- the norm is controlled by inflation
  have hnorm : ∀ t, ‖z t‖ ≤ Cz * |z t 1| := fun t => by
    obtain ⟨hwp, hm⟩ := resource_mstar (hz t).2.2
    have hz2 : z t 2 = z t 0 + Real.log (wedge p.ψ (z t 1)) := by
      have := congrFun hm 2; simp only [mstar, Matrix.cons_val] at this; linarith
    have hlw := hw (z t 1) (hzr2 t)
    have h1 := (hG _ (hzr t)).1
    have hL := hL0 t
    unfold Lf at hL
    have n1 : |z t 1| ≤ ‖z t‖ := by simpa using norm_le_pi_norm (z t) 1
    have he : |p.σ * z t 0 + α' * z t 1| ≤ (kk + p.σ) * η * ‖z t‖ := by
      have e : p.σ * z t 0 + α' * z t 1 =
          kc p * p.β * (Gadj p (z t) - p.ψ * z t 1) - p.σ * Real.log (wedge p.ψ (z t 1)) := by
        rw [hkk] at hL ⊢; simp only [α']; rw [hz2] at hL; linarith
      rw [e]
      calc _ ≤ |kc p * p.β * (Gadj p (z t) - p.ψ * z t 1)| +
            |p.σ * Real.log (wedge p.ψ (z t 1))| := abs_sub _ _
        _ ≤ kk * p.β * (η / p.β * ‖z t‖) + p.σ * (η * |z t 1|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos hσ]
            gcongr
        _ ≤ (kk + p.σ) * η * ‖z t‖ := by
            have : kk * p.β * (η / p.β * ‖z t‖) = kk * η * ‖z t‖ := by field_simp
            rw [this]
            have h := mul_le_mul_of_nonneg_left n1 (mul_nonneg hσ.le hη.le)
            have e1 : p.σ * (η * |z t 1|) = p.σ * η * |z t 1| := by ring
            have e2 : (kk + p.σ) * η * ‖z t‖ = kk * η * ‖z t‖ + p.σ * η * ‖z t‖ := by ring
            linarith
    have hz0 : |z t 0| ≤ c1 * |z t 1| + c2 * η * ‖z t‖ := by
      have hσz : p.σ * |z t 0| ≤ α' * |z t 1| + (kk + p.σ) * η * ‖z t‖ := by
        have h := abs_sub (p.σ * z t 0 + α' * z t 1) (α' * z t 1)
        rw [add_sub_cancel_right, abs_mul, abs_mul, abs_of_pos hσ,
          abs_of_pos (by linarith : (0:ℝ) < α')] at h
        linarith
      have h2 : |z t 0| ≤ (α' * |z t 1| + (kk + p.σ) * η * ‖z t‖) / p.σ := by
        rw [le_div_iff₀ hσ]; linarith
      have e : (α' * |z t 1| + (kk + p.σ) * η * ‖z t‖) / p.σ =
          α' / p.σ * |z t 1| + (kk + p.σ) / p.σ * η * ‖z t‖ := by ring
      have := abs_nonneg (z t 1)
      simp only [c1, c2]
      linarith
    have hz0' : |z t 0| ≤ α' / p.σ * |z t 1| + c2 * η * ‖z t‖ := by
      have hσz : p.σ * |z t 0| ≤ α' * |z t 1| + (kk + p.σ) * η * ‖z t‖ := by
        have h := abs_sub (p.σ * z t 0 + α' * z t 1) (α' * z t 1)
        rw [add_sub_cancel_right, abs_mul, abs_mul, abs_of_pos hσ,
          abs_of_pos (by linarith : (0:ℝ) < α')] at h
        linarith
      have h2 : |z t 0| ≤ (α' * |z t 1| + (kk + p.σ) * η * ‖z t‖) / p.σ := by
        rw [le_div_iff₀ hσ]; linarith
      have e : (α' * |z t 1| + (kk + p.σ) * η * ‖z t‖) / p.σ =
          α' / p.σ * |z t 1| + (kk + p.σ) / p.σ * η * ‖z t‖ := by ring
      simp only [c2]
      linarith
    have hz2b : |z t 2| ≤ c1 * |z t 1| + c2 * η * ‖z t‖ := by
      rw [hz2]
      have : |Real.log (wedge p.ψ (z t 1))| ≤ |z t 1| :=
        hlw.trans (mul_le_of_le_one_left (abs_nonneg _) hη1)
      have h3 : c1 * |z t 1| + c2 * η * ‖z t‖ - |z t 0| ≥ 0 := by linarith
      calc _ ≤ |z t 0| + |Real.log (wedge p.ψ (z t 1))| := abs_add_le _ _
        _ ≤ (α' / p.σ + 1) * |z t 1| + c2 * η * ‖z t‖ + |z t 1| := by
            have := abs_nonneg (z t 1); linarith
        _ = c1 * |z t 1| + c2 * η * ‖z t‖ := by simp only [c1]; ring
    have hall : ‖z t‖ ≤ c1 * |z t 1| + c2 * η * ‖z t‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      fin_cases i
      · exact hz0
      · have : |z t 1| ≤ c1 * |z t 1| := by
          have : 1 ≤ c1 := by
            simp only [c1]; have := div_nonneg (by linarith : (0:ℝ) ≤ α') hσ.le; linarith
          nlinarith [abs_nonneg (z t 1)]
        have : 0 ≤ c2 * η * ‖z t‖ := by positivity
        simp only [Fin.mk_one]; linarith
      · exact hz2b
    have : c2 * η * ‖z t‖ ≤ ‖z t‖ / 2 := by nlinarith [norm_nonneg (z t)]
    simp only [Cz]; linarith
  -- inflation expands
  have hexp : ∀ t, q * |z t 1| ≤ |z (t + 1) 1| := fun t => by
    obtain ⟨-, hpr, hres⟩ := hz t
    obtain ⟨hwp, hm⟩ := resource_mstar hres
    have hz2 : z t 2 = z t 0 + Real.log (wedge p.ψ (z t 1)) := by
      have := congrFun hm 2; simp only [mstar, Matrix.cons_val] at this; linarith
    have hlw := hw (z t 1) (hzr2 t)
    have hpr' : Gadj p (z t) - Hmc p 0 (z t) - p.β * Gadj p (z (t + 1)) = 0 := by
      simp only [Qmap, Nmap, Matrix.cons_val_one, Matrix.cons_val_zero] at hpr; linarith
    have a1 := (hG _ (hzr t)).2
    have a2 := (hG _ (hzr (t + 1))).1
    have hL := hL0 t
    unfold Lf at hL
    -- `e = σŷ + α'π` is small
    set e := p.σ * z t 0 + α' * z t 1
    have he : |e| ≤ (kk + p.σ) * η * ‖z t‖ := by
      have n1 : |z t 1| ≤ ‖z t‖ := by simpa using norm_le_pi_norm (z t) 1
      have h1 := (hG _ (hzr t)).1
      have ee : e = kc p * p.β * (Gadj p (z t) - p.ψ * z t 1) -
          p.σ * Real.log (wedge p.ψ (z t 1)) := by
        simp only [e]; rw [hkk] at hL ⊢; simp only [α']; rw [hz2] at hL; linarith
      rw [ee]
      calc _ ≤ |kc p * p.β * (Gadj p (z t) - p.ψ * z t 1)| +
            |p.σ * Real.log (wedge p.ψ (z t 1))| := abs_sub _ _
        _ ≤ kk * p.β * (η / p.β * ‖z t‖) + p.σ * (η * |z t 1|) := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos hβ, abs_of_pos hσ]
            gcongr
        _ ≤ (kk + p.σ) * η * ‖z t‖ := by
            have : kk * p.β * (η / p.β * ‖z t‖) = kk * η * ‖z t‖ := by field_simp
            rw [this]
            have h := mul_le_mul_of_nonneg_left n1 (mul_nonneg hσ.le hη.le)
            have e1 : p.σ * (η * |z t 1|) = p.σ * η * |z t 1| := by ring
            have e2 : (kk + p.σ) * η * ‖z t‖ = kk * η * ‖z t‖ + p.σ * η * ‖z t‖ := by ring
            linarith
    have key : p.β * p.ψ * z (t + 1) 1 - p.β * p.ψ * μ0 * z t 1 =
        (Gadj p (z t) - Hmc p 0 (z t) - (p.ψ * z t 1 - p.θ * p.m * (p.ω * z t 0 + p.σ * z t 2)))
          - p.β * (Gadj p (z (t + 1)) - p.ψ * z (t + 1) 1) - D * e / p.σ -
            p.θ * p.m * p.σ * Real.log (wedge p.ψ (z t 1)) := by
      simp only [μ0, e, D]
      rw [hz2]
      field_simp
      linear_combination (norm := ring_nf) -p.σ * hpr'
    have bnd : |p.β * p.ψ * z (t + 1) 1 - p.β * p.ψ * μ0 * z t 1| ≤
        c3 * η * (‖z t‖ + ‖z (t + 1)‖) := by
      rw [key]
      have n1 : |z t 1| ≤ ‖z t‖ := by simpa using norm_le_pi_norm (z t) 1
      have b1 := abs_sub _ _ |>.trans (add_le_add (abs_sub _ _ |>.trans (add_le_add
        (abs_sub _ _ |>.trans (add_le_add a1 (le_refl |p.β * (Gadj p (z (t + 1)) -
          p.ψ * z (t + 1) 1)|))) (le_refl |D * e / p.σ|))) (le_refl |p.θ * p.m * p.σ *
            Real.log (wedge p.ψ (z t 1))|))
      have b2 : |p.β * (Gadj p (z (t + 1)) - p.ψ * z (t + 1) 1)| ≤ η * ‖z (t + 1)‖ := by
        rw [abs_mul, abs_of_pos hβ]
        calc _ ≤ p.β * (η / p.β * ‖z (t + 1)‖) := by gcongr
          _ = η * ‖z (t + 1)‖ := by field_simp
      have b3 : |D * e / p.σ| ≤ D * (kk + p.σ) / p.σ * η * ‖z t‖ := by
        rw [abs_div, abs_mul, abs_of_pos hD, abs_of_pos hσ]
        calc _ ≤ D * ((kk + p.σ) * η * ‖z t‖) / p.σ := by gcongr
          _ = _ := by ring
      have b4 : |p.θ * p.m * p.σ * Real.log (wedge p.ψ (z t 1))| ≤
          p.θ * p.m * p.σ * η * ‖z t‖ := by
        rw [abs_mul, abs_of_pos (mul_pos hθm hσ)]
        calc _ ≤ p.θ * p.m * p.σ * (η * |z t 1|) := by gcongr
          _ ≤ _ := by
            have := mul_le_mul_of_nonneg_left n1 (mul_nonneg (mul_pos hθm hσ).le hη.le)
            linarith
      have n0 := norm_nonneg (z t)
      have n1' := norm_nonneg (z (t + 1))
      have hc31 : 1 ≤ c3 := by
        simp only [c3]
        have : 0 ≤ D * (kk + p.σ) / p.σ := by positivity
        have : 0 ≤ p.θ * p.m * p.σ := (mul_pos hθm hσ).le
        linarith
      have e1 : c3 * η * (‖z t‖ + ‖z (t + 1)‖) = (D * (kk + p.σ) / p.σ * η * ‖z t‖ +
          p.θ * p.m * p.σ * η * ‖z t‖ + η * ‖z t‖) + c3 * η * ‖z (t + 1)‖ := by
        simp only [c3]; ring
      have e2 : η * ‖z (t + 1)‖ ≤ c3 * η * ‖z (t + 1)‖ := by
        have := mul_le_mul_of_nonneg_right hc31 (mul_nonneg hη.le n1')
        linarith
      rw [e1]
      linarith
    have nb := hnorm t
    have nb1 := hnorm (t + 1)
    have hδ : c3 * η * (‖z t‖ + ‖z (t + 1)‖) ≤
        δ0 * (p.β * p.ψ) * (|z t 1| + |z (t + 1) 1|) := by
      have h := mul_le_mul_of_nonneg_right hηδ (by positivity : (0 : ℝ) ≤ p.β * p.ψ)
      rw [div_mul_cancel₀ _ (by positivity)] at h
      calc _ ≤ c3 * η * (Cz * |z t 1| + Cz * |z (t + 1) 1|) := by gcongr
        _ = c3 * η * Cz * (|z t 1| + |z (t + 1) 1|) := by ring
        _ ≤ _ := by gcongr
    have hlow := abs_sub_abs_le_abs_sub (p.β * p.ψ * μ0 * z t 1) (p.β * p.ψ * z (t + 1) 1)
    rw [abs_sub_comm (p.β * p.ψ * μ0 * z t 1)] at hlow
    rw [abs_mul (p.β * p.ψ * μ0) (z t 1), abs_mul (p.β * p.ψ) (z (t + 1) 1),
      abs_of_pos (by positivity : (0:ℝ) < p.β * p.ψ * μ0),
      abs_of_pos (by positivity : (0:ℝ) < p.β * p.ψ)] at hlow
    have hbp : 0 < p.β * p.ψ := by positivity
    -- `(μ0 − δ0)|z_t| ≤ (1 + δ0)|z_{t+1}|`
    have hineq : (μ0 - δ0) * |z t 1| ≤ (1 + δ0) * |z (t + 1) 1| := by
      have h := hlow.trans (bnd.trans hδ)
      have : p.β * p.ψ * ((μ0 - δ0) * |z t 1| - (1 + δ0) * |z (t + 1) 1|) ≤ 0 := by nlinarith
      nlinarith
    have hqq : q * (1 + δ0) ≤ μ0 - δ0 := by
      simp only [q, δ0]
      rw [show (1 + μ0) / 2 * (1 + (μ0 - 1) / (4 * (1 + μ0))) = (1 + μ0) / 2 + (μ0 - 1) / 8 by
        field_simp; ring]
      have : (μ0 - 1) / (4 * (1 + μ0)) ≤ (μ0 - 1) / 4 := by
        apply div_le_div_of_nonneg_left (by linarith) (by norm_num); nlinarith
      nlinarith
    have h1 : 0 < 1 + δ0 := by linarith
    have := mul_le_mul_of_nonneg_right hqq (abs_nonneg (z t 1))
    nlinarith
  -- conclude
  have hpi : ∀ s, z s 1 = 0 := fun s => by
    refine geom_bounded_zero (r := q) (a := z s 1) (by rw [abs_of_pos (by linarith)]; exact hq)
      (C := r) fun n => ?_
    have hg : q ^ n * |z s 1| ≤ |z (s + n) 1| := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, show s + (n + 1) = s + n + 1 by ring]
        have := hexp (s + n)
        nlinarith [abs_nonneg (z s 1), pow_nonneg (by linarith : (0:ℝ) ≤ q) n]
    rw [abs_mul, abs_pow, abs_of_pos (by linarith)]
    exact hg.trans ((show |z (s + n) 1| ≤ ‖z (s + n)‖ by
      simpa using norm_le_pi_norm (z (s + n)) 1).trans
      (hzB _))
  intro t
  have := hnorm t
  rw [hpi t, abs_zero, mul_zero] at this
  exact norm_le_zero_iff.1 this

end Woodford.StabilizationWelfare.NonlinearRotembergBoundaryPair
