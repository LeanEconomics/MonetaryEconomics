/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergBoundaryPair
import StabilizationWelfare.NonlinearRotembergCentreTools

/-!
# The linear boundary Taylor rule: exact centre and expanding coordinates

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.3 (p. 254) and Appendix A.3
(pp. 632–634), for the exact Rotemberg model of `NonlinearRotemberg` under the LINEAR rule
`1 + i_t = β⁻¹Π_t^{φ_π}(Y_t/Ȳ)^{φ_y}e^{ν}` with a constant interest-rate disturbance `ν`, on the
boundary `κ(φ_π − 1) + (1 − β)φ_y = 0` of the Taylor principle.

With `x = (ŷ, π, ĉ)`, `G` the adjustment term (`Gadj`), `H` the marginal-cost term (`Hmc`) and
`Θ = θm(σ+ω) = κψ`, two EXACT coordinates turn every perfect-foresight equilibrium into an explicit
planar recursion (`exact_rec`):

* the centre coordinate `L = σĉ + π − kβG` (`NonlinearRotembergBoundaryPair.Lf`,
  `k = −φ_y/Θ`): `L_{t+1} = L_t + D(x_t) + ν`;
* the expanding coordinate `V = ψΘ(σĉ + π) − (σ(1−β)ψ + Θ)G` (`Vf`):
  `V_{t+1} = μV_t + E(x_t) + ψΘν`, `μ = (σ + φ_y + φ_πκ)/(σβ) > 1` (`one_lt_mu`);

where `D` (`Dfun`) and `E` (`Efun`) are explicit functions of the CURRENT state whose linear parts
vanish on the resource manifold `C = Y(1 − (ψ/2)(Π − 1)²)` exactly on the boundary. Hence
(`rem_DE`) `|D|, |E| ≤ η‖x‖` near the steady state for every `η > 0`, and (`norm_le_LV`)
`‖x‖ ≤ K(|L| + |V|)` on the resource manifold. Conversely (`pf_of_rec`) a sequence on the resource
manifold whose `σĉ + π` and `G` follow the forward recursions is an equilibrium.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergCentreLocal

open Filter Topology
open NonlinearRotemberg
open NonlinearRotembergLinks (wedge)
open NonlinearRotembergBoundaryPair (Lf kc rem_G rem_logw resource_mstar mstar)

variable {p : Par}

/-! ## Constants and coordinates -/

/-- Woodford (2003), Ch. 3, fn. 44: `Θ = θm(σ + ω) = κψ`. -/
noncomputable def Th (p : Par) : ℝ := p.θ * p.m * (p.σ + p.ω)

/-- Woodford (2003), Prop. 4.3: the expanding root `μ = (σ + φ_y + φ_πκ)/(σβ)` of the boundary
IS–AS block (the other root is `1`). -/
noncomputable def mu (p : Par) : ℝ := (p.σ + p.φy + p.φ * p.κ) / (p.σ * p.β)

/-- Woodford (2003), App. A.3: The coefficient `σ(1−β)ψ + Θ` of `G` in the expanding coordinate. -/
noncomputable def cE (p : Par) : ℝ := p.σ * (1 - p.β) * p.ψ + Th p

/-- Woodford (2003), Prop. 4.3: the constant interest-rate disturbance `e = (ν, 0, 0)`. -/
def ev (ν : ℝ) : Fin 3 → ℝ := ![ν, 0, 0]

/-- Woodford (2003), Prop. 4.3: the expanding coordinate `V = ψΘ(σĉ + π) − (σ(1−β)ψ + Θ)G`. -/
noncomputable def Vf (p : Par) (z : Fin 3 → ℝ) : ℝ :=
  p.ψ * Th p * (p.σ * z 2 + z 1) - cE p * Gadj p z

/-- Woodford (2003), Prop. 4.3: the drift of the centre coordinate,
`D(x) = (φ_π − 1)π + φ_yŷ − k((1−β)G − H)`. -/
noncomputable def Dfun (p : Par) (z : Fin 3 → ℝ) : ℝ :=
  (p.φ - 1) * z 1 + p.φy * z 0 - kc p * ((1 - p.β) * Gadj p z - Hmc p 0 z)

/-- Woodford (2003), Prop. 4.3: the nonlinear part of the expanding coordinate's recursion,
`E(x) = ψΘ(φ_ππ + φ_yŷ + σĉ) − (σ(1−β)ψ + Θ)(G − H)/β − μV(x)`. -/
noncomputable def Efun (p : Par) (z : Fin 3 → ℝ) : ℝ :=
  p.ψ * Th p * (p.φ * z 1 + p.φy * z 0 + p.σ * z 2) - cE p * (Gadj p z - Hmc p 0 z) / p.β -
    mu p * Vf p z

/-- Woodford (2003), Ch. 4 (2.7)–(2.8) with the linear rule and a constant disturbance `ν`
(**exact perfect-foresight equilibrium**): `Q(e, x_t) + N(e, x_{t+1}) = 0` at every date. -/
def PFEq (p : Par) (ν : ℝ) (z : ℕ → Fin 3 → ℝ) : Prop :=
  ∀ t, Qmap p (ev ν, z t) + Nmap p (ev ν, z (t + 1)) = 0

/-- Woodford (2003), Ch. 3, fn. 44: the resource constraint `e^{ĉ} = e^{ŷ}(1 − (ψ/2)(e^π − 1)²)`. -/
def Res (p : Par) (z : Fin 3 → ℝ) : Prop := Qmap p (0, z) 2 = 0

/-! ## Signs -/

/-- Woodford (2003), App. A.3: `Θ > 0`. -/
theorem Th_pos (hp : p.Basic) : 0 < Th p := by
  have : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  unfold Th; have := hp.σ_pos; have := hp.ω_nonneg; positivity

/-- Woodford (2003), App. A.3: `κψ = Θ`. -/
theorem κψ (hp : p.Basic) : p.κ * p.ψ = Th p := by rw [hp.κ_mul]; rfl

/-- Woodford (2003), App. A.3: `k ≤ 0`. -/
theorem kc_nonpos (hp : p.Basic) : kc p ≤ 0 := by
  unfold kc
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [hp.φy_nonneg]) (Th_pos hp).le

/-- Woodford (2003), App. A.3: `kΘ = −φ_y`. -/
theorem kc_mul_Th (hp : p.Basic) : kc p * Th p = -p.φy := by
  unfold kc; exact div_mul_cancel₀ _ (Th_pos hp).ne'

/-- Woodford (2003), App. A.3: `σ(1−β)ψ + Θ > 0`. -/
theorem cE_pos (hp : p.Basic) : 0 < cE p := by
  unfold cE
  have := Th_pos hp; have := hp.σ_pos; have := hp.ψ_pos
  have : 0 < 1 - p.β := by linarith [hp.β_lt_one]
  positivity

/-- Woodford (2003), Prop. 4.3: on the boundary with `φ_y ≥ 0`, `μ > 1`. -/
theorem one_lt_mu (hp : p.Basic) : 1 < mu p := by
  unfold mu
  have h := hp.β_lt_one; have := hp.β_pos; have := hp.σ_pos
  rw [lt_div_iff₀ (by positivity)]
  have : 0 ≤ p.φ * p.κ := mul_nonneg hp.φ_nonneg hp.κ_pos.le
  have : p.σ * p.β < p.σ := by nlinarith
  linarith [hp.φy_nonneg]

/-- Woodford (2003), App. A.3: On the boundary, `φ_π − 1 + φ_y(1−β)ψ/Θ = 0`. -/
theorem boundary_Th (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) :
    (p.φ - 1) * Th p + p.φy * ((1 - p.β) * p.ψ) = 0 := by
  rw [← κψ hp]; linear_combination p.ψ * hb

/-! ## The exact recursion -/

/-- Woodford (2003), App. A.3: `H(e, x) = H(0, x)` for `e = (ν, 0, 0)`. -/
theorem Hmc_ev (ν : ℝ) (z : Fin 3 → ℝ) : Hmc p (ev ν) z = Hmc p 0 z := by
  simp [Hmc, ev]

/-- Woodford (2003), Ch. 4 (2.7)–(2.8) (**the three conditions of an equilibrium date**):
`σĉ′ + π′ = φ_ππ + φ_yŷ + ν + σĉ`, `βG(x′) = G(x) − H(x)`, and the resource constraint. -/
theorem pf_components {ν : ℝ} {z : ℕ → Fin 3 → ℝ} (hz : PFEq p ν z) (t : ℕ) :
    p.σ * z (t + 1) 2 + z (t + 1) 1 =
        p.φ * z t 1 + p.φy * z t 0 + ν + p.σ * z t 2 ∧
      p.β * Gadj p (z (t + 1)) = Gadj p (z t) - Hmc p 0 (z t) ∧ Res p (z t) := by
  have h0 := congrFun (hz t) 0
  have h1 := congrFun (hz t) 1
  have h2 := congrFun (hz t) 2
  have hH : Hmc p ![ν, 0, 0] (z t) = Hmc p 0 (z t) := Hmc_ev ν (z t)
  simp only [Qmap, Nmap, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, ev] at h0 h1 h2
  refine ⟨?_, by linarith, ?_⟩
  · have := Real.exp_injective (show Real.exp (-(p.φ * z t 1 + p.φy * z t 0 + ν +
        p.σ * z t 2)) = Real.exp (-(p.σ * z (t + 1) 2) - z (t + 1) 1) by linarith)
    linarith
  · simp only [Res, Qmap, Matrix.cons_val]; linarith

/-- Woodford (2003), Prop. 4.3 (**the exact planar recursion**): along every exact
perfect-foresight equilibrium, `L_{t+1} = L_t + D(x_t) + ν` and `V_{t+1} = μV_t + E(x_t) + ψΘν`. -/
theorem exact_rec (hp : p.Basic) {ν : ℝ} {z : ℕ → Fin 3 → ℝ} (hz : PFEq p ν z) (t : ℕ) :
    Lf p (z (t + 1)) = Lf p (z t) + Dfun p (z t) + ν ∧
      Vf p (z (t + 1)) = mu p * Vf p (z t) + Efun p (z t) + p.ψ * Th p * ν := by
  obtain ⟨h0, h1, -⟩ := pf_components hz t
  have hβ := hp.β_pos.ne'
  refine ⟨?_, ?_⟩
  · simp only [Lf, Dfun]
    linear_combination h0 - kc p * h1
  · have hG : Gadj p (z (t + 1)) = (Gadj p (z t) - Hmc p 0 (z t)) / p.β := by
      field_simp; linarith
    simp only [Vf, Efun]
    rw [hG]
    linear_combination p.ψ * Th p * h0

/-- Woodford (2003), Ch. 4 (2.7)–(2.8) (**the converse**): a sequence on the resource manifold with
`σĉ_{t+1} + π_{t+1} = φ_ππ_t + φ_yŷ_t + ν + σĉ_t` and `βG(x_{t+1}) = G(x_t) − H(x_t)` is an exact
perfect-foresight equilibrium. -/
theorem pf_of_rec {ν : ℝ} {z : ℕ → Fin 3 → ℝ} (hres : ∀ t, Res p (z t))
    (h0 : ∀ t, p.σ * z (t + 1) 2 + z (t + 1) 1 = p.φ * z t 1 + p.φy * z t 0 + ν + p.σ * z t 2)
    (h1 : ∀ t, p.β * Gadj p (z (t + 1)) = Gadj p (z t) - Hmc p 0 (z t)) : PFEq p ν z := by
  intro t
  funext i
  fin_cases i
  · simp only [Qmap, Nmap, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero, ev,
      Fin.zero_eta]
    rw [show -(p.σ * z (t + 1) 2) - z (t + 1) 1 =
      -(p.φ * z t 1 + p.φy * z t 0 + ν + p.σ * z t 2) by linarith [h0 t]]
    ring
  · have hH : Hmc p ![ν, 0, 0] (z t) = Hmc p 0 (z t) := Hmc_ev ν (z t)
    simp only [Qmap, Nmap, Pi.add_apply, Pi.zero_apply, Matrix.cons_val_one,
      Matrix.cons_val_zero, ev, Fin.mk_one]
    linarith [h1 t]
  · have := hres t
    simp only [Res, Qmap, Matrix.cons_val] at this
    simp only [Qmap, Nmap, Pi.add_apply, Pi.zero_apply, Matrix.cons_val, Fin.reduceFinMk]
    linarith

/-! ## First-order remainders on the resource manifold -/

/-- Woodford (2003), App. A.3: On the resource manifold `ĉ = ŷ + log(C/Y)`. -/
theorem res_c {z : Fin 3 → ℝ} (h : Res p z) : z 2 = z 0 + Real.log (wedge p.ψ (z 1)) := by
  have := congrFun (resource_mstar (p := p) h).2 2
  simpa [mstar] using this.symm

/-- Woodford (2003), Prop. 4.3 (**the linear part of `D` vanishes on the boundary up to
`ĉ − ŷ`**): `D`'s linearisation is `φ_yσ(ŷ − ĉ)/(σ + ω)`. -/
theorem Dlin_eq (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (z : Fin 3 → ℝ) :
    (p.φ - 1) * z 1 + p.φy * z 0 - kc p * ((p.ψ * z 1 - p.θ * p.m * (p.ω * z 0 + p.σ * z 2)) -
      p.β * (p.ψ * z 1)) = p.φy * p.σ / (p.σ + p.ω) * (z 0 - z 2) := by
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hT := (Th_pos hp).ne'
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm : p.m ≠ 0 := hp.m_pos.ne'
  have hbT := boundary_Th hp hb
  have key : (p.φ - 1) * z 1 + p.φy * z 0 - kc p * ((p.ψ * z 1 - p.θ * p.m * (p.ω * z 0 +
      p.σ * z 2)) - p.β * (p.ψ * z 1)) - p.φy * p.σ / (p.σ + p.ω) * (z 0 - z 2) =
      z 1 / Th p * ((p.φ - 1) * Th p + p.φy * ((1 - p.β) * p.ψ)) := by
    unfold Th at hT ⊢
    unfold kc
    field_simp
    ring
  rw [hbT, mul_zero] at key
  linarith

/-- Woodford (2003), Prop. 4.3: the coefficient `γ_E = ψΘσ + (σ(1−β)ψ + Θ)θmσ/β − μψΘσ` of
`ĉ − ŷ` in `E`'s linearisation. -/
noncomputable def gE (p : Par) : ℝ :=
  p.ψ * Th p * p.σ + cE p * (p.θ * p.m) * p.σ / p.β - mu p * p.ψ * Th p * p.σ

/-- Woodford (2003), Prop. 4.3 (**the linear part of `E` vanishes on the boundary up to
`ĉ − ŷ`**): `E`'s linearisation is `γ_E(ĉ − ŷ)`. -/
theorem Elin_eq (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (z : Fin 3 → ℝ) :
    p.ψ * Th p * (p.φ * z 1 + p.φy * z 0 + p.σ * z 2) -
        cE p * (p.ψ * z 1 - p.θ * p.m * (p.ω * z 0 + p.σ * z 2)) / p.β -
      mu p * (p.ψ * Th p * (p.σ * z 2 + z 1) - cE p * (p.ψ * z 1)) = gE p * (z 2 - z 0) := by
  have hβ := hp.β_pos.ne'
  have hσ := hp.σ_pos.ne'
  have hψ := hp.ψ_pos.ne'
  have hbT := boundary_Th hp hb
  have key : p.ψ * Th p * (p.φ * z 1 + p.φy * z 0 + p.σ * z 2) -
        cE p * (p.ψ * z 1 - p.θ * p.m * (p.ω * z 0 + p.σ * z 2)) / p.β -
      mu p * (p.ψ * Th p * (p.σ * z 2 + z 1) - cE p * (p.ψ * z 1)) - gE p * (z 2 - z 0) =
      (p.ψ * z 1 - Th p * z 0) / p.β * ((p.φ - 1) * Th p + p.φy * ((1 - p.β) * p.ψ)) := by
    unfold gE mu cE Par.κ
    unfold Th
    field_simp
    ring
  rw [hbT, mul_zero] at key
  linarith

/-- Woodford (2003), App. A.3: `|x_i| ≤ ‖x‖`. -/
theorem abs_le_norm (z : Fin 3 → ℝ) (i : Fin 3) : |z i| ≤ ‖z‖ := by
  simpa using norm_le_pi_norm z i

/-- Woodford (2003), Prop. 4.3 and App. A.3 (**the nonlinear terms are small**): for every
`η > 0` there is `ρ > 0` with `|D(x)| ≤ η‖x‖` and `|E(x)| ≤ η‖x‖` for every `x` on the resource
manifold with `‖x‖ < ρ`. -/
theorem rem_DE (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) {η : ℝ}
    (hη : 0 < η) : ∃ ρ > 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ → Res p z →
      |Dfun p z| ≤ η * ‖z‖ ∧ |Efun p z| ≤ η * ‖z‖ := by
  have hβ := hp.β_pos
  have hs : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hcE := cE_pos hp
  have hmu : 0 < mu p := lt_trans one_pos (one_lt_mu hp)
  set A := 2 * |kc p| + p.φy * p.σ / (p.σ + p.ω) + cE p / p.β + mu p * cE p / p.β + |gE p|
    with hA
  have hA0 : 0 ≤ A := by
    have := hp.φy_nonneg; have := hp.σ_pos; positivity
  set η' := η / (A + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  have hAη : A * η' ≤ η := by
    rw [hη', mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨ρ1, hρ1, hG⟩ := rem_G hp hη'0
  obtain ⟨ρ2, hρ2, hw⟩ := rem_logw p.ψ hη'0
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun z hz hres => ?_⟩
  have hzn := norm_nonneg z
  obtain ⟨g1, g2⟩ := hG z (hz.trans_le (min_le_left _ _))
  have hz1 := abs_le_norm z 1
  have hlw := hw (z 1) (lt_of_le_of_lt hz1 (hz.trans_le (min_le_right _ _)))
  have hc := res_c hres
  set lw := Real.log (wedge p.ψ (z 1))
  have hlw' : |lw| ≤ η' * ‖z‖ := hlw.trans (mul_le_mul_of_nonneg_left hz1 hη'0.le)
  have hG1 : |Gadj p z - p.ψ * z 1| ≤ η' / p.β * ‖z‖ := g1
  have hG2 := g2
  set lin := p.ψ * z 1 - p.θ * p.m * (p.ω * z 0 + p.σ * z 2)
  have hDl := Dlin_eq hp hb z
  have hEl := Elin_eq hp hb z
  have eβ : p.β * (η' / p.β * ‖z‖) = η' * ‖z‖ := by field_simp
  refine ⟨?_, ?_⟩
  · have e : Dfun p z = (p.φ - 1) * z 1 + p.φy * z 0 - kc p * (lin - p.β * (p.ψ * z 1)) -
        kc p * ((Gadj p z - Hmc p 0 z - lin) - p.β * (Gadj p z - p.ψ * z 1)) := by
      simp only [Dfun, lin]; ring
    rw [e, hDl, show z 0 - z 2 = -lw by rw [hc]; ring]
    have t1 : |p.φy * p.σ / (p.σ + p.ω) * -lw| ≤ p.φy * p.σ / (p.σ + p.ω) * (η' * ‖z‖) := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by have := hp.φy_nonneg; have := hp.σ_pos; positivity)]
      exact mul_le_mul_of_nonneg_left hlw' (by have := hp.φy_nonneg; have := hp.σ_pos; positivity)
    have t2 : |kc p * ((Gadj p z - Hmc p 0 z - lin) - p.β * (Gadj p z - p.ψ * z 1))| ≤
        |kc p| * (2 * (η' * ‖z‖)) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc _ ≤ |Gadj p z - Hmc p 0 z - lin| + |p.β * (Gadj p z - p.ψ * z 1)| := abs_sub _ _
        _ ≤ η' * ‖z‖ + p.β * (η' / p.β * ‖z‖) := by
            rw [abs_mul, abs_of_pos hβ]
            exact add_le_add hG2 (mul_le_mul_of_nonneg_left hG1 hβ.le)
        _ = 2 * (η' * ‖z‖) := by rw [eβ]; ring
    have hsum : |p.φy * p.σ / (p.σ + p.ω) * -lw - kc p * ((Gadj p z - Hmc p 0 z - lin) -
        p.β * (Gadj p z - p.ψ * z 1))| ≤ |p.φy * p.σ / (p.σ + p.ω) * -lw| +
        |kc p * ((Gadj p z - Hmc p 0 z - lin) - p.β * (Gadj p z - p.ψ * z 1))| := abs_sub _ _
    have hAe : A * η' * ‖z‖ = p.φy * p.σ / (p.σ + p.ω) * (η' * ‖z‖) +
        |kc p| * (2 * (η' * ‖z‖)) +
        (cE p / p.β + mu p * cE p / p.β + |gE p|) * (η' * ‖z‖) := by
      simp only [hA]; ring
    have h0 : 0 ≤ (cE p / p.β + mu p * cE p / p.β + |gE p|) * (η' * ‖z‖) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hAη hzn
    linarith
  · have e : Efun p z = (p.ψ * Th p * (p.φ * z 1 + p.φy * z 0 + p.σ * z 2) -
        cE p * lin / p.β - mu p * (p.ψ * Th p * (p.σ * z 2 + z 1) - cE p * (p.ψ * z 1))) -
        cE p * (Gadj p z - Hmc p 0 z - lin) / p.β + mu p * cE p * (Gadj p z - p.ψ * z 1) := by
      simp only [Efun, Vf, lin]; ring
    rw [e, hEl, show z 2 - z 0 = lw by rw [hc]; ring]
    have t1 : |gE p * lw| ≤ |gE p| * (η' * ‖z‖) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hlw' (abs_nonneg _)
    have t2 : |cE p * (Gadj p z - Hmc p 0 z - lin) / p.β| ≤ cE p / p.β * (η' * ‖z‖) := by
      rw [abs_div, abs_mul, abs_of_pos hcE, abs_of_pos hβ, mul_div_right_comm]
      exact mul_le_mul_of_nonneg_left hG2 (by positivity)
    have t3 : |mu p * cE p * (Gadj p z - p.ψ * z 1)| ≤ mu p * cE p / p.β * (η' * ‖z‖) := by
      rw [abs_mul, abs_of_pos (mul_pos hmu hcE)]
      calc mu p * cE p * |Gadj p z - p.ψ * z 1| ≤ mu p * cE p * (η' / p.β * ‖z‖) :=
            mul_le_mul_of_nonneg_left hG1 (by positivity)
        _ = mu p * cE p / p.β * (η' * ‖z‖) := by ring
    have hsum : |gE p * lw - cE p * (Gadj p z - Hmc p 0 z - lin) / p.β +
        mu p * cE p * (Gadj p z - p.ψ * z 1)| ≤ |gE p * lw| +
        |cE p * (Gadj p z - Hmc p 0 z - lin) / p.β| + |mu p * cE p * (Gadj p z - p.ψ * z 1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    have hAe : A * η' * ‖z‖ = (2 * |kc p| + p.φy * p.σ / (p.σ + p.ω)) * (η' * ‖z‖) +
        |gE p| * (η' * ‖z‖) + cE p / p.β * (η' * ‖z‖) + mu p * cE p / p.β * (η' * ‖z‖) := by
      simp only [hA]; ring
    have h0 : 0 ≤ (2 * |kc p| + p.φy * p.σ / (p.σ + p.ω)) * (η' * ‖z‖) := by
      have := hp.φy_nonneg; have := hp.σ_pos; positivity
    have h1 := mul_le_mul_of_nonneg_right hAη hzn
    linarith

/-- Woodford (2003), App. A.3: The linear part of `L` on the resource manifold, `σŷ + (1 − kβψ)π`.
-/
noncomputable def Ll (p : Par) (z : Fin 3 → ℝ) : ℝ := p.σ * z 0 + (1 - kc p * p.β * p.ψ) * z 1

/-- Woodford (2003), App. A.3: The linear part of `V` on the resource manifold, `ψΘσŷ − σ(1−β)ψ²π`.
-/
noncomputable def Vl (p : Par) (z : Fin 3 → ℝ) : ℝ :=
  p.ψ * Th p * p.σ * z 0 - p.σ * (1 - p.β) * p.ψ ^ 2 * z 1

/-- Woodford (2003), App. A.3: `Γ = σ(1−β)ψ + (1 − kβψ)Θ > 0`. -/
noncomputable def Gam (p : Par) : ℝ := p.σ * (1 - p.β) * p.ψ + (1 - kc p * p.β * p.ψ) * Th p

/-- Woodford (2003), App. A.3: `1 − kβψ ≥ 1`. -/
theorem one_le_a12 (hp : p.Basic) : 1 ≤ 1 - kc p * p.β * p.ψ := by
  have := kc_nonpos hp
  have : kc p * p.β * p.ψ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg this hp.β_pos.le) hp.ψ_pos.le
  linarith

/-- Woodford (2003), App. A.3: `Γ > 0`. -/
theorem Gam_pos (hp : p.Basic) : 0 < Gam p := by
  unfold Gam
  have := one_le_a12 hp; have := Th_pos hp; have := hp.σ_pos; have := hp.ψ_pos
  have : 0 < 1 - p.β := by linarith [hp.β_lt_one]
  positivity

/-- Woodford (2003), Prop. 4.3 (**inverting the linear coordinates**):
`σψΓŷ = σ(1−β)ψ²L_l + (1 − kβψ)V_l` and `ψΓπ = ψΘL_l − V_l`. -/
theorem lin_inv (z : Fin 3 → ℝ) :
    p.σ * p.ψ * Gam p * z 0 = p.σ * (1 - p.β) * p.ψ ^ 2 * Ll p z + (1 - kc p * p.β * p.ψ) * Vl p z ∧
      p.ψ * Gam p * z 1 = p.ψ * Th p * Ll p z - Vl p z := by
  constructor <;> (simp only [Gam, Ll, Vl]; ring)

/-- Woodford (2003), Prop. 4.3 (**the exact coordinates are their linear parts up to `η‖x‖`**):
for every `η > 0`, near the steady state on the resource manifold, `|L − L_l| ≤ η‖x‖` and
`|V − V_l| ≤ η‖x‖`. -/
theorem rem_LV (hp : p.Basic) {η : ℝ} (hη : 0 < η) : ∃ ρ > 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ →
    Res p z → |Lf p z - Ll p z| ≤ η * ‖z‖ ∧ |Vf p z - Vl p z| ≤ η * ‖z‖ := by
  have hβ := hp.β_pos
  have hσ := hp.σ_pos
  have hcE := cE_pos hp
  have hT := Th_pos hp
  have hψ := hp.ψ_pos
  set A := p.σ + |kc p| + p.ψ * Th p * p.σ + cE p / p.β with hA
  have hA0 : 0 ≤ A := by positivity
  set η' := η / (A + 1) with hη'
  have hη'0 : 0 < η' := by positivity
  have hAη : A * η' ≤ η := by
    rw [hη', mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨ρ1, hρ1, hG⟩ := rem_G hp hη'0
  obtain ⟨ρ2, hρ2, hw⟩ := rem_logw p.ψ hη'0
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, fun z hz hres => ?_⟩
  have hzn := norm_nonneg z
  have g1 := (hG z (hz.trans_le (min_le_left _ _))).1
  have hz1 := abs_le_norm z 1
  have hlw := hw (z 1) (lt_of_le_of_lt hz1 (hz.trans_le (min_le_right _ _)))
  have hc := res_c hres
  set lw := Real.log (wedge p.ψ (z 1))
  have hlw' : |lw| ≤ η' * ‖z‖ := hlw.trans (mul_le_mul_of_nonneg_left hz1 hη'0.le)
  refine ⟨?_, ?_⟩
  · have e : Lf p z - Ll p z = p.σ * lw - kc p * p.β * (Gadj p z - p.ψ * z 1) := by
      simp only [Lf, Ll, hc]; ring
    rw [e]
    calc _ ≤ |p.σ * lw| + |kc p * p.β * (Gadj p z - p.ψ * z 1)| := abs_sub _ _
      _ ≤ p.σ * (η' * ‖z‖) + |kc p| * p.β * (η' / p.β * ‖z‖) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos hβ]
          exact add_le_add (mul_le_mul_of_nonneg_left hlw' hσ.le)
            (mul_le_mul_of_nonneg_left g1 (by positivity))
      _ = (p.σ + |kc p|) * (η' * ‖z‖) := by field_simp
      _ ≤ A * η' * ‖z‖ := by
          have : 0 ≤ (p.ψ * Th p * p.σ + cE p / p.β) * (η' * ‖z‖) := by positivity
          simp only [hA]; nlinarith
      _ ≤ η * ‖z‖ := mul_le_mul_of_nonneg_right hAη hzn
  · have e : Vf p z - Vl p z = p.ψ * Th p * p.σ * lw - cE p * (Gadj p z - p.ψ * z 1) := by
      simp only [Vf, Vl, hc, cE]; ring
    rw [e]
    calc _ ≤ |p.ψ * Th p * p.σ * lw| + |cE p * (Gadj p z - p.ψ * z 1)| := abs_sub _ _
      _ ≤ p.ψ * Th p * p.σ * (η' * ‖z‖) + cE p * (η' / p.β * ‖z‖) := by
          rw [abs_mul (p.ψ * Th p * p.σ), abs_mul (cE p),
            abs_of_pos (by positivity : 0 < p.ψ * Th p * p.σ), abs_of_pos hcE]
          exact add_le_add (mul_le_mul_of_nonneg_left hlw' (by positivity))
            (mul_le_mul_of_nonneg_left g1 hcE.le)
      _ = (p.ψ * Th p * p.σ + cE p / p.β) * (η' * ‖z‖) := by ring
      _ ≤ A * η' * ‖z‖ := by
          have : 0 ≤ (p.σ + |kc p|) * (η' * ‖z‖) := by positivity
          simp only [hA]; nlinarith
      _ ≤ η * ‖z‖ := mul_le_mul_of_nonneg_right hAη hzn

/-- Woodford (2003), App. A.3: The constant `K₀ = 2((σ(1−β)ψ² + 1 − kβψ)/(σψΓ) + (ψΘ + 1)/(ψΓ))` of
the linear inversion. -/
noncomputable def K0 (p : Par) : ℝ :=
  2 * ((p.σ * (1 - p.β) * p.ψ ^ 2 + (1 - kc p * p.β * p.ψ)) / (p.σ * p.ψ * Gam p) +
    (p.ψ * Th p + 1) / (p.ψ * Gam p))

/-- Woodford (2003), App. A.3: `K₀ > 0`. -/
theorem K0_pos (hp : p.Basic) : 0 < K0 p := by
  unfold K0
  have := one_le_a12 hp; have := Th_pos hp; have := hp.σ_pos; have := hp.ψ_pos
  have := Gam_pos hp
  have : 0 < 1 - p.β := by linarith [hp.β_lt_one]
  positivity

/-- Woodford (2003), Prop. 4.3 (**the linear coordinates control the state**): on the resource
manifold with `|log(C/Y)| ≤ |π|`, `‖x‖ ≤ K₀(|L_l| + |V_l|)`. -/
theorem norm_le_lin (hp : p.Basic) {z : Fin 3 → ℝ} (hres : Res p z)
    (hlw : |Real.log (wedge p.ψ (z 1))| ≤ |z 1|) : ‖z‖ ≤ K0 p * (|Ll p z| + |Vl p z|) := by
  obtain ⟨e0, e1⟩ := lin_inv (p := p) z
  have hG := Gam_pos hp
  have hσ := hp.σ_pos
  have hψ := hp.ψ_pos
  have hT := Th_pos hp
  have ha := one_le_a12 hp
  have hβ : 0 < 1 - p.β := by linarith [hp.β_lt_one]
  set S := |Ll p z| + |Vl p z|
  have hS : 0 ≤ S := by positivity
  have hy : |z 0| ≤ (p.σ * (1 - p.β) * p.ψ ^ 2 + (1 - kc p * p.β * p.ψ)) /
      (p.σ * p.ψ * Gam p) * S := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : |p.σ * p.ψ * Gam p * z 0| ≤
        p.σ * (1 - p.β) * p.ψ ^ 2 * |Ll p z| + (1 - kc p * p.β * p.ψ) * |Vl p z| := by
      rw [e0]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;>
        (refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _); rw [abs_of_nonneg (by positivity)])
    rw [abs_mul, abs_of_pos (by positivity : 0 < p.σ * p.ψ * Gam p)] at this
    have h1 : p.σ * (1 - p.β) * p.ψ ^ 2 * |Ll p z| ≤ p.σ * (1 - p.β) * p.ψ ^ 2 * S :=
      mul_le_mul_of_nonneg_left (by simp only [S]; linarith [abs_nonneg (Vl p z)]) (by positivity)
    have h2 : (1 - kc p * p.β * p.ψ) * |Vl p z| ≤ (1 - kc p * p.β * p.ψ) * S :=
      mul_le_mul_of_nonneg_left (by simp only [S]; linarith [abs_nonneg (Ll p z)]) (by positivity)
    nlinarith
  have hπ : |z 1| ≤ (p.ψ * Th p + 1) / (p.ψ * Gam p) * S := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : |p.ψ * Gam p * z 1| ≤ p.ψ * Th p * |Ll p z| + |Vl p z| := by
      rw [e1]
      refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
      rw [abs_mul, abs_of_pos (by positivity : 0 < p.ψ * Th p)]
    rw [abs_mul, abs_of_pos (by positivity : 0 < p.ψ * Gam p)] at this
    have h1 : p.ψ * Th p * |Ll p z| ≤ p.ψ * Th p * S :=
      mul_le_mul_of_nonneg_left (by simp only [S]; linarith [abs_nonneg (Vl p z)]) (by positivity)
    have h2 : |Vl p z| ≤ S := by simp only [S]; linarith [abs_nonneg (Ll p z)]
    nlinarith
  have hc : |z 2| ≤ |z 0| + |z 1| := by
    rw [res_c hres]; exact (abs_add_le _ _).trans (by linarith)
  have hcy : 0 ≤ (p.σ * (1 - p.β) * p.ψ ^ 2 + (1 - kc p * p.β * p.ψ)) /
      (p.σ * p.ψ * Gam p) * S := by positivity
  have hcπ : 0 ≤ (p.ψ * Th p + 1) / (p.ψ * Gam p) * S := by positivity
  refine (pi_norm_le_iff_of_nonneg (by have := K0_pos hp; positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hK : K0 p * S = 2 * ((p.σ * (1 - p.β) * p.ψ ^ 2 + (1 - kc p * p.β * p.ψ)) /
      (p.σ * p.ψ * Gam p) * S) + 2 * ((p.ψ * Th p + 1) / (p.ψ * Gam p) * S) := by
    simp only [K0]; ring
  rw [hK]
  fin_cases i
  · simp only [Fin.zero_eta]; linarith
  · simp only [Fin.mk_one]; linarith
  · simp only [Fin.reduceFinMk]; linarith

/-- Woodford (2003), Prop. 4.3 (**the exact coordinates control the state**): there are `ρ > 0`
and `K > 0` with `‖x‖ ≤ K(|L(x)| + |V(x)|)` for every `x` on the resource manifold with
`‖x‖ < ρ`. -/
theorem norm_le_LV (hp : p.Basic) : ∃ ρ > 0, ∃ K > 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ → Res p z →
    ‖z‖ ≤ K * (|Lf p z| + |Vf p z|) := by
  have hK0 := K0_pos hp
  obtain ⟨ρ1, hρ1, hLV⟩ := rem_LV hp (by positivity : (0 : ℝ) < 1 / (4 * K0 p))
  obtain ⟨ρ2, hρ2, hw⟩ := rem_logw p.ψ one_pos
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, 2 * K0 p, by positivity, fun z hz hres => ?_⟩
  obtain ⟨h1, h2⟩ := hLV z (hz.trans_le (min_le_left _ _)) hres
  have hz1 := abs_le_norm z 1
  have hlw := hw (z 1) (lt_of_le_of_lt hz1 (hz.trans_le (min_le_right _ _)))
  rw [one_mul] at hlw
  have hn := norm_le_lin hp hres hlw
  have a1 : |Ll p z| ≤ |Lf p z| + 1 / (4 * K0 p) * ‖z‖ := by
    have := abs_sub_abs_le_abs_sub (Ll p z) (Lf p z)
    rw [abs_sub_comm] at this; linarith
  have a2 : |Vl p z| ≤ |Vf p z| + 1 / (4 * K0 p) * ‖z‖ := by
    have := abs_sub_abs_le_abs_sub (Vl p z) (Vf p z)
    rw [abs_sub_comm] at this; linarith
  have e : K0 p * (1 / (4 * K0 p) * ‖z‖ + 1 / (4 * K0 p) * ‖z‖) = ‖z‖ / 2 := by
    field_simp; ring
  have : ‖z‖ ≤ K0 p * (|Lf p z| + |Vf p z|) + ‖z‖ / 2 := by
    calc ‖z‖ ≤ K0 p * (|Ll p z| + |Vl p z|) := hn
      _ ≤ K0 p * ((|Lf p z| + 1 / (4 * K0 p) * ‖z‖) + (|Vf p z| + 1 / (4 * K0 p) * ‖z‖)) := by
          gcongr
      _ = K0 p * (|Lf p z| + |Vf p z|) + K0 p * (1 / (4 * K0 p) * ‖z‖ +
          1 / (4 * K0 p) * ‖z‖) := by ring
      _ = _ := by rw [e]
  linarith

/-- Woodford (2003), Prop. 4.3: near the steady state `|L(x)| ≤ K‖x‖` and `|V(x)| ≤ K‖x‖`. -/
theorem LV_le_norm (hp : p.Basic) : ∃ ρ > 0, ∃ K > 0, ∀ z : Fin 3 → ℝ, ‖z‖ < ρ →
    |Lf p z| ≤ K * ‖z‖ ∧ |Vf p z| ≤ K * ‖z‖ := by
  obtain ⟨ρ1, hρ1, hG⟩ := rem_G hp one_pos
  have hβ := hp.β_pos
  have hσ := hp.σ_pos
  have hψ := hp.ψ_pos
  have hcE := cE_pos hp
  have hT := Th_pos hp
  set K := (p.σ + 1 + |kc p| * p.β * (p.ψ + 1 / p.β)) +
    (p.ψ * Th p * (p.σ + 1) + cE p * (p.ψ + 1 / p.β))
  refine ⟨ρ1, hρ1, K + 1, by positivity, fun z hz => ?_⟩
  have g1 := (hG z hz).1
  have hzn := norm_nonneg z
  have hz1 := abs_le_norm z 1
  have hz2 := abs_le_norm z 2
  have hGb : |Gadj p z| ≤ (p.ψ + 1 / p.β) * ‖z‖ := by
    have := abs_sub_abs_le_abs_sub (Gadj p z) (p.ψ * z 1)
    rw [abs_mul, abs_of_pos hψ] at this
    nlinarith
  have hL : |Lf p z| ≤ (p.σ + 1 + |kc p| * p.β * (p.ψ + 1 / p.β)) * ‖z‖ := by
    unfold Lf
    calc _ ≤ |p.σ * z 2| + |z 1| + |kc p * p.β * Gadj p z| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ p.σ * ‖z‖ + ‖z‖ + |kc p| * p.β * ((p.ψ + 1 / p.β) * ‖z‖) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hσ, abs_of_pos hβ]
          gcongr
      _ = _ := by ring
  have hV : |Vf p z| ≤ (p.ψ * Th p * (p.σ + 1) + cE p * (p.ψ + 1 / p.β)) * ‖z‖ := by
    unfold Vf
    calc _ ≤ |p.ψ * Th p * (p.σ * z 2 + z 1)| + |cE p * Gadj p z| := abs_sub _ _
      _ ≤ p.ψ * Th p * (p.σ * ‖z‖ + ‖z‖) + cE p * ((p.ψ + 1 / p.β) * ‖z‖) := by
          rw [abs_mul (p.ψ * Th p), abs_mul (cE p), abs_of_pos (by positivity : 0 < p.ψ * Th p),
            abs_of_pos hcE]
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity))
            (mul_le_mul_of_nonneg_left hGb hcE.le)
          refine (abs_add_le _ _).trans (add_le_add ?_ hz1)
          rw [abs_mul, abs_of_pos hσ]; exact mul_le_mul_of_nonneg_left hz2 hσ.le
      _ = _ := by ring
  have h0 : 0 ≤ (p.σ + 1 + |kc p| * p.β * (p.ψ + 1 / p.β)) := by positivity
  have h0' : 0 ≤ (p.ψ * Th p * (p.σ + 1) + cE p * (p.ψ + 1 / p.β)) := by positivity
  constructor <;> nlinarith

end Woodford.StabilizationWelfare.NonlinearRotembergCentreLocal
