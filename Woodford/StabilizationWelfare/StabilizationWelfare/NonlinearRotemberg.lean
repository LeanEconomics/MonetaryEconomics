/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovGeneral

/-!
# The exact nonlinear Rotemberg (1982) model: equations, linearisation, Taylor principle

Woodford (2003), *Interest and Prices*, Chapter 3, §2.2, footnote 44 (p. 188: "the same form of
aggregate supply relation, up to the log-linear approximation, is implied by a model with convex
costs of price adjustment, as shown by Rotemberg (1987)") and footnote 28 (p. 177); Chapter 4,
§2.2 (the Taylor principle, Proposition 4.3, (2.7), p. 254); Chapter 6, §1 (pp. 383–392) and
Appendix A.3 (local determinacy by the implicit function theorem). The pricing model is
Rotemberg (1982), "Sticky prices in the United States", *Journal of Political Economy*.

The book only mentions the Rotemberg model; this module states it exactly in the book's notation
(Ch. 3: utility `u(C) − v(y)`, `ω` the elasticity of real marginal cost with respect to own
output, `σ` the inverse intertemporal elasticity; Ch. 4: the interest-rate rule):

* households: CRRA `u(C) = C^{1−σ}/(1−σ)`, disutility of supplying output
  `v(y) = λ_v y^{1+ω} e^{−(1+ω)a}/(1+ω)`; real marginal cost
  `mc = v_y/u_c = λ_v Y^ω C^σ e^{μ−(1+ω)a}`
  (`a` technology, `μ` a cost-push/markup shock);
* Dixit–Stiglitz goods with elasticity `θ > 1`, a production subsidy `τ`, and Rotemberg's
  quadratic adjustment cost `(ψ/2)(Π_t − 1)² Y_t` (`ψ` is Rotemberg's `φ`; `φ` is kept for the
  rule); the steady-state real marginal cost is `m = (1+τ)(θ−1)/θ`, so `Φ = 1 − m` is the
  steady-state distortion;
* the exact symmetric pricing condition
  `ψ(Π_t − 1)Π_t = θ(mc_t − m) + β E_t[(C_{t+1}/C_t)^{−σ}(Y_{t+1}/Y_t) ψ(Π_{t+1} − 1)Π_{t+1}]`
  (`(1+τ)(1−θ) = −θm`);
* the resource constraint `C_t = Y_t(1 − (ψ/2)(Π_t − 1)²)` (no price dispersion state);
* the Euler equation with the rule `1 + i_t = β⁻¹ Π_t^{φ_π}(Y_t/Ȳ)^{φ_y} e^{ν_t}` substituted.

In log deviations `x = (ŷ, π, ĉ)` (`ŷ = log(Y/Ȳ)`, `π = log Π`, `ĉ = log(C/Ȳ)`) and disturbances
`e = (ν, a, μ)` the conditions at a state are `Q(e, x) + E_t N(e′, x′) = 0` (`Qmap`, `Nmap`), with
the pricing condition multiplied by the date-`t` known factor `e^{ŷ − σĉ}`.

## Main results

* `steadyState_zero`: `x = 0` (zero inflation, `Y = C = Ȳ`) solves the conditions without
  disturbances, for EVERY parameter vector.
* `fderiv_Qmap_inr`, `fderiv_Nmap_inr`: the exact derivatives at the steady state are `DQ0`,
  `DN0`; the linearisation is the IS curve, `ĉ = ŷ` and the NKPC `π = κ ŷ + β E π′` with the
  **Rotemberg slope** `κ = θ m (σ + ω)/ψ` (`= (θ−1)(σ+ω)/ψ` without subsidy) (`lin_nkpc`).
* `schurStable_Arot_iff`: the IS–AS block `u = A E u′ + b` is Schur stable **iff** the Taylor
  principle `κ(φ_π − 1) + (1 − β)φ_y > 0` holds in the Rotemberg slope.
* `linSol_spec`, `Lop_injective`, `norm_linSol_le`, `linSol_Lop`: the linearised operator is a
  bijection of bounded functions of ANY state space with ANY Markov operator, with an inverse bound
  depending only on the parameters.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotemberg

open Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovLinks NonlinearNKMarkovGeneral

/-! ## Parameters -/

/-- Woodford (2003), Ch. 3 §2 and Ch. 4 §2.2, with Rotemberg (1982) pricing: the discount factor
`β`, the inverse intertemporal elasticity `σ` (`σ⁻¹` in the book), the elasticity `ω` of real
marginal cost, the elasticity of substitution `θ`, Rotemberg's adjustment-cost parameter `ψ`, the
steady-state real marginal cost `m = (1+τ)(θ−1)/θ` (`Φ = 1 − m`), and the rule coefficients. -/
structure Par where
  /-- The discount factor. -/
  β : ℝ
  /-- The inverse of the intertemporal elasticity of substitution. -/
  σ : ℝ
  /-- The elasticity of real marginal cost with respect to own output. -/
  ω : ℝ
  /-- The elasticity of substitution between goods. -/
  θ : ℝ
  /-- Rotemberg's quadratic adjustment-cost parameter. -/
  ψ : ℝ
  /-- The steady-state real marginal cost `(1+τ)(θ−1)/θ`. -/
  m : ℝ
  /-- The response of the interest rate to inflation. -/
  φ : ℝ
  /-- The response of the interest rate to output. -/
  φy : ℝ

namespace Par

variable (p : Par)

/-- Rotemberg (1982) in Woodford's notation (Ch. 3, fn. 44, p. 188): the slope of the linearised
pricing condition, `κ = θ m (σ + ω)/ψ`; without a subsidy (`m = (θ−1)/θ`) it is `(θ−1)(σ+ω)/ψ`. -/
noncomputable def κ : ℝ := p.θ * p.m * (p.σ + p.ω) / p.ψ

/-- Woodford (2003), Proposition 4.3: the determinant `σ + φ_y + φ_π κ` of the current block. -/
noncomputable def dd : ℝ := p.σ + p.φy + p.φ * p.κ

/-- Woodford (2003), Ch. 3–4: the maintained parameter restrictions, without the Taylor
principle. -/
structure Basic where
  β_pos : 0 < p.β
  β_lt_one : p.β < 1
  one_lt_θ : 1 < p.θ
  ω_nonneg : 0 ≤ p.ω
  σ_pos : 0 < p.σ
  ψ_pos : 0 < p.ψ
  m_pos : 0 < p.m
  φ_nonneg : 0 ≤ p.φ
  φy_nonneg : 0 ≤ p.φy

/-- Woodford (2003), Proposition 4.3, (2.7), p. 254, in the Rotemberg slope: the maintained
restrictions together with the Taylor principle `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
structure Std where
  basic : p.Basic
  taylor : 0 < p.κ * (p.φ - 1) + (1 - p.β) * p.φy

variable {p}

/-- Woodford (2003), Ch. 3: the Rotemberg slope is positive. -/
theorem Basic.κ_pos (hp : p.Basic) : 0 < p.κ := by
  unfold κ
  have := hp.ω_nonneg; have := hp.σ_pos; have := hp.ψ_pos; have := hp.m_pos
  have : 0 < p.θ := by linarith [hp.one_lt_θ]
  have : 0 < p.σ + p.ω := by linarith
  positivity

/-- Woodford (2003), Proposition 4.3: `σ + φ_y + φ_π κ > 0`. -/
theorem Basic.dd_pos (hp : p.Basic) : 0 < p.dd := by
  unfold dd
  have := mul_nonneg hp.φ_nonneg hp.κ_pos.le
  linarith [hp.σ_pos, hp.φy_nonneg]

/-- Woodford (2003), Ch. 3: `κψ = θm(σ + ω)`. -/
theorem Basic.κ_mul (hp : p.Basic) : p.κ * p.ψ = p.θ * p.m * (p.σ + p.ω) := by
  unfold κ; field_simp [hp.ψ_pos.ne']

end Par

/-! ## The Rotemberg–Calvo first-order equivalence map -/

/-- Woodford (2003), Ch. 3, (2.19) and fn. 44 (**the slopes coincide exactly on the equivalence
map**): for `0 < α < 1` the Rotemberg slope `θm(σ+ω)/ψ` equals the Calvo slope
`(1−α)(1−αβ)/α · (ω+σ)/(1+ωθ)` iff `ψ = θ m α (1 + ωθ)/((1 − α)(1 − αβ))`. -/
theorem κ_eq_calvo_iff {p : Par} (hp : p.Basic) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    p.κ = Moments.calvoKappa α p.β p.ω p.θ p.σ ↔
      p.ψ = p.θ * p.m * α * (1 + p.ω * p.θ) / ((1 - α) * (1 - α * p.β)) := by
  have h1 : 0 < 1 - α := by linarith
  have h2 : 0 < 1 - α * p.β := by nlinarith [hp.β_lt_one, hp.β_pos]
  have h3 : 0 < 1 + p.ω * p.θ := by
    have := mul_nonneg hp.ω_nonneg (by linarith [hp.one_lt_θ] : (0 : ℝ) ≤ p.θ); linarith
  have h4 : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hψ := hp.ψ_pos
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  have hm := hp.m_pos
  unfold Par.κ Moments.calvoKappa
  constructor
  · intro h
    have e : p.θ * p.m * (p.σ + p.ω) * (α * (1 + p.ω * p.θ)) =
        p.ψ * ((1 - α) * (1 - α * p.β)) * (p.σ + p.ω) := by
      rw [div_eq_iff hψ.ne'] at h; rw [h]; field_simp; ring
    rw [eq_div_iff (by positivity)]
    have e2 : (p.ψ * ((1 - α) * (1 - α * p.β))) * (p.σ + p.ω) =
        (p.θ * p.m * α * (1 + p.ω * p.θ)) * (p.σ + p.ω) := by linear_combination -e
    exact mul_right_cancel₀ h4.ne' e2
  · intro h
    rw [h]
    field_simp
    ring

/-- Woodford (2003), Ch. 3, (2.19): the Calvo slope is strictly decreasing in the Calvo
probability `α` on `(0, 1)`. -/
theorem calvoKappa_strictAntiOn {β ω θ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hωσ : 0 < ω + σ)
    (hc : 0 < 1 + ω * θ) :
    StrictAntiOn (fun α => Moments.calvoKappa α β ω θ σ) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  simp only [Moments.calvoKappa]
  refine mul_lt_mul_of_pos_right ?_ (div_pos hωσ hc)
  have ha0 := ha.1; have hb0 := hb.1; have hb1 := hb.2
  rw [div_lt_div_iff₀ hb0 ha0]
  have h1 : 0 < 1 - b * β := by nlinarith
  have h2 : (1 - b) * (1 - b * β) * a < (1 - a) * (1 - a * β) * b := by
    nlinarith [mul_pos (sub_pos.2 hab) h1, mul_pos ha0 hb0, mul_pos (mul_pos ha0 hb0) hβ0,
      mul_pos (sub_pos.2 hab) hβ0]
  linarith

/-- Woodford (2003), Ch. 3, (2.19) and fn. 44 (**the equivalence map is a bijection**): for
every Rotemberg slope `k > 0` there is exactly one Calvo probability `α ∈ (0, 1)` with the same
slope. -/
theorem existsUnique_calvo_alpha {β ω θ σ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hωσ : 0 < ω + σ)
    (hc : 0 < 1 + ω * θ) {k : ℝ} (hk : 0 < k) :
    ∃! α, α ∈ Set.Ioo (0 : ℝ) 1 ∧ Moments.calvoKappa α β ω θ σ = k := by
  set C := (ω + σ) / (1 + ω * θ) with hC
  have hC0 : 0 < C := div_pos hωσ hc
  set g := fun α => Moments.calvoKappa α β ω θ σ with hg
  have hgα : ∀ α, g α = (1 - α) * (1 - α * β) / α * C := fun α => rfl
  -- a small `a` with `g a > k` and `b` near one with `g b < k`
  set a := min (1 / 4) ((1 - β) * C / (2 * (k + 1))) with ha
  have hβ' : 0 < 1 - β := by linarith
  have ha0 : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 / 4 := min_le_left _ _
  have hga : k < g a := by
    rw [hgα]
    have h1 : 1 / 2 ≤ 1 - a := by linarith
    have h2 : 1 - β ≤ 1 - a * β := by nlinarith
    have h3 : a ≤ (1 - β) * C / (2 * (k + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h3
    rw [div_mul_eq_mul_div, lt_div_iff₀ ha0]
    have h4 : (1 - β) * C / 2 ≤ (1 - a) * (1 - a * β) * C := by
      have : 0 < 1 - β := by linarith
      have : (1 / 2) * (1 - β) ≤ (1 - a) * (1 - a * β) := mul_le_mul h1 h2 this.le (by linarith)
      nlinarith
    nlinarith
  set b := 1 - min (1 / 2) (k / (4 * C)) with hb
  have hb0 : 1 / 2 ≤ b := by have := min_le_left (1 / 2 : ℝ) (k / (4 * C)); linarith
  have hb1 : b < 1 := by
    have : 0 < min (1 / 2 : ℝ) (k / (4 * C)) := lt_min (by norm_num) (by positivity)
    linarith
  have hgb : g b < k := by
    rw [hgα]
    have hb0' : 0 < b := by linarith
    have h1 : 1 - b ≤ k / (4 * C) := by have := min_le_right (1 / 2 : ℝ) (k / (4 * C)); linarith
    have h2 : 1 - b * β ≤ 1 := by nlinarith
    have h3 : 0 < 1 - b * β := by nlinarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ hb0']
    rw [le_div_iff₀ (by positivity)] at h1
    have h4 : (1 - b) * C * (1 - b * β) ≤ (1 - b) * C * 1 :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (by linarith) hC0.le)
    have h5 : k * (1 / 2) ≤ k * b := mul_le_mul_of_nonneg_left hb0 hk.le
    nlinarith
  have hab : a < b := by linarith
  have hcont : ContinuousOn g (Set.Icc a b) := by
    refine ContinuousOn.mul (ContinuousOn.div (by fun_prop) continuousOn_id fun x hx => ?_)
      continuousOn_const
    exact (lt_of_lt_of_le ha0 hx.1).ne'
  obtain ⟨α, hαI, hα⟩ := intermediate_value_Icc' hab.le hcont ⟨hgb.le, hga.le⟩
  have hsub : Set.Icc a b ⊆ Set.Ioo 0 1 := fun x hx =>
    ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
  refine ⟨α, ⟨hsub hαI, hα⟩, fun α' ⟨hα'I, hα'⟩ => ?_⟩
  have hα2 : Moments.calvoKappa α β ω θ σ = k := hα
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := calvoKappa_strictAntiOn hβ0 hβ1 hωσ hc hα'I (hsub hαI) h
    simp only at this; rw [hα', hα2] at this; exact lt_irrefl _ this
  · have := calvoKappa_strictAntiOn hβ0 hβ1 hωσ hc (hsub hαI) hα'I h
    simp only at this; rw [hα', hα2] at this; exact lt_irrefl _ this

/-! ## The IS–AS block and the Taylor principle in the Rotemberg slope -/

/-- Woodford (2003), Ch. 4, (2.7)–(2.8) in Markov form, Rotemberg slope: the matrix `A = B₀⁻¹B₁`
of the IS–AS block `u = A M u + b`, `u = (ĉ, π)`:
`A = (σ + φ_y + φ_π κ)⁻¹ [[σ, 1 − φ_π β], [κσ, κ + β(σ + φ_y)]]`. -/
noncomputable def Arot (p : Par) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![p.σ / p.dd, (1 - p.φ * p.β) / p.dd; p.κ * p.σ / p.dd, (p.κ + p.β * (p.σ + p.φy)) / p.dd]

variable {p : Par}

/-- Woodford (2003), Proposition 4.3, p. 254, in the Rotemberg slope (**the Taylor principle is
EXACTLY Schur stability of the IS–AS block**): under the maintained restrictions, both
eigenvalues of `A` lie inside the unit circle iff `κ(φ_π − 1) + (1 − β)φ_y > 0`. -/
theorem schurStable_Arot_iff (hp : p.Basic) :
    SchurStable (tr2 (Arot p)) (det2 (Arot p)) ↔ 0 < p.κ * (p.φ - 1) + (1 - p.β) * p.φy := by
  have hd := hp.dd_pos
  have hdet : det2 (Arot p) = p.σ * p.β / p.dd := by
    simp only [det2, Arot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    unfold Par.dd
    ring
  have htr : tr2 (Arot p) = (p.σ + p.κ + p.β * (p.σ + p.φy)) / p.dd := by
    simp only [tr2, Arot, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    field_simp
    ring
  have hσβ : 0 < p.σ * p.β := mul_pos hp.σ_pos hp.β_pos
  have hlt : p.σ * p.β < p.dd := by
    unfold Par.dd
    nlinarith [mul_nonneg hp.φ_nonneg hp.κ_pos.le, hp.φy_nonneg, hp.σ_pos, hp.β_lt_one]
  have hT : 0 < (p.σ + p.κ + p.β * (p.σ + p.φy)) / p.dd := by
    have := hp.κ_pos; have := hp.φy_nonneg; have := hp.σ_pos; have := hp.β_pos
    positivity
  rw [hdet, htr]
  unfold SchurStable
  rw [abs_of_pos (div_pos hσβ hd), abs_of_pos hT, div_lt_one hd, div_lt_iff₀ hd, add_mul,
    one_mul, div_mul_cancel₀ _ hd.ne']
  unfold Par.dd
  constructor
  · rintro ⟨-, h⟩; nlinarith
  · intro h; exact ⟨by unfold Par.dd at hlt; exact hlt, by nlinarith⟩

/-- Woodford (2003), App. A.3: a Schur-stable `2 × 2` matrix has `∑ₖ mnorm(Aᵏ) < ∞`. -/
theorem summable_of_schur {A : Matrix (Fin 2) (Fin 2) ℝ} (h : SchurStable (tr2 A) (det2 A)) :
    Summable fun k => mnorm (A ^ k) := by
  have ht : Tendsto (fun n => mnorm (A ^ n)) atTop (𝓝 0) := by
    have h' : ∀ i j : Fin 2, Tendsto (fun n => |(A ^ n) i j|) atTop (𝓝 0) := fun i j => by
      simpa using (tendsto_pow_entry h i j).abs
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun j _ => h' i j
    simpa [mnorm] using this
  obtain ⟨N, hN⟩ :=
    (ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
  exact summable_mnorm_pow (hN (N + 1) (Nat.le_succ N)) (Nat.succ_pos N)

/-- Woodford (2003), Proposition 4.3: under the Taylor principle `∑ mnorm(Aᵏ) < ∞`. -/
theorem summable_Arot (hp : p.Std) : Summable fun k => mnorm (Arot p ^ k) :=
  summable_of_schur ((schurStable_Arot_iff hp.basic).2 hp.taylor)

/-! ## The exact equilibrium conditions -/

/-- Rotemberg (1982) (**the adjustment term**, times the known factor `e^{ŷ − σĉ}`):
`G(x) = ψ e^{ŷ − σĉ}(Π − 1)Π` with `Π = e^π`. -/
noncomputable def Gadj (p : Par) (x : Fin 3 → ℝ) : ℝ :=
  p.ψ * (Real.exp (x 0 - p.σ * x 2) * ((Real.exp (x 1) - 1) * Real.exp (x 1)))

/-- Rotemberg (1982) (**the marginal-cost term**, times `e^{ŷ − σĉ}`):
`H(e, x) = θ m (e^{(1+ω)ŷ + μ − (1+ω)a} − e^{ŷ − σĉ}) = e^{ŷ−σĉ}·θ(mc − m)`. -/
noncomputable def Hmc (p : Par) (e x : Fin 3 → ℝ) : ℝ :=
  p.θ * p.m * (Real.exp ((1 + p.ω) * x 0 + e 2 - (1 + p.ω) * e 1) - Real.exp (x 0 - p.σ * x 2))

/-- Woodford (2003), Ch. 4 (2.7)–(2.8) and Rotemberg (1982) (**the exact conditions, current-date
part**). With `e = (ν, a, μ)` and `x = (ŷ, π, ĉ)`:
* Euler + rule: `−exp(−(φ_π π + φ_y ŷ + ν + σĉ))`;
* pricing: `G(x) − H(e, x)`;
* resource constraint: `e^{ĉ} − e^{ŷ}(1 − (ψ/2)(e^π − 1)²)`. -/
noncomputable def Qmap (p : Par) (q : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  ![-Real.exp (-(p.φ * q.2 1 + p.φy * q.2 0 + q.1 0 + p.σ * q.2 2)),
    Gadj p q.2 - Hmc p q.1 q.2,
    Real.exp (q.2 2) - Real.exp (q.2 0) * (1 - p.ψ / 2 * (Real.exp (q.2 1) - 1) ^ 2)]

/-- Woodford (2003), Ch. 4 and Rotemberg (1982) (**the part inside `E_t`**), at next period's
state: `exp(−σĉ′ − π′)` (Euler) and `−βG(x′)` (pricing). -/
noncomputable def Nmap (p : Par) (q : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  ![Real.exp (-(p.σ * q.2 2) - q.2 1), -(p.β * Gadj p q.2), 0]

/-- Woodford (2003), App. A.3: `Q` is `C^∞`. -/
theorem contDiff_Qmap {n : WithTop ℕ∞} : ContDiff ℝ n (Qmap p) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Qmap, Gadj, Hmc, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop

/-- Woodford (2003), App. A.3: `N` is `C^∞`. -/
theorem contDiff_Nmap {n : WithTop ℕ∞} : ContDiff ℝ n (Nmap p) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp only [Nmap, Gadj, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] <;> fun_prop

/-- Woodford (2003), Ch. 3 §2 with Rotemberg pricing (**the zero-inflation steady state**):
`x = 0` (`Π = 1`, `Y = C = Ȳ`) solves the conditions without disturbances, for EVERY parameter
vector: `Q(0, 0) + N(0, 0) = 0`. -/
theorem steadyState_zero : Qmap p (0, 0) + Nmap p (0, 0) = 0 := by
  funext i
  fin_cases i <;> simp [Qmap, Nmap, Gadj, Hmc]

/-- The linearisation of `Q` in `x` at the steady state. -/
noncomputable def DQ0 (p : Par) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![p.φy * v 0 + p.φ * v 1 + p.σ * v 2, p.ψ * v 1 - p.θ * p.m * (p.ω * v 0 + p.σ * v 2),
    v 2 - v 0]

/-- The linearisation of `N` in `x` at the steady state. -/
noncomputable def DN0 (p : Par) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-(p.σ * v 2) - v 1, -(p.β * p.ψ * v 1), 0]

/-- The linearisation of `Q` in the disturbances (`N` does not depend on them). -/
noncomputable def DQe (p : Par) (e : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![e 0, -(p.θ * p.m * (e 2 - (1 + p.ω) * e 1)), 0]

/-- The adjustment term as a difference of exponentials. -/
theorem Gadj_eq (x : Fin 3 → ℝ) : Gadj p x =
    p.ψ * (Real.exp (x 0 - p.σ * x 2 + 2 * x 1) - Real.exp (x 0 - p.σ * x 2 + x 1)) := by
  unfold Gadj
  rw [two_mul, Real.exp_add, Real.exp_add, Real.exp_add]
  ring

/-- `t ↦ exp(tc)` has derivative `c` at `0`. -/
theorem hasDerivAt_exp_line1 (c : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (t * c)) c 0 := by
  have h := hasDerivAt_exp_line c 1
  simpa using h

/-- Woodford (2003), App. A.3: the derivative of `Q` along `t ↦ (0, tw)` at the steady state. -/
theorem hasDerivAt_Qmap_line (w : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => Qmap p (0, t • w) i) (DQ0 p w i) 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := hasDerivAt_exp_line (-(p.φ * w 1 + p.φy * w 0 + p.σ * w 2)) (-1)
    refine (h.congr_deriv (by simp [DQ0]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring_nf
  · have h := ((hasDerivAt_exp_line (w 0 - p.σ * w 2 + 2 * w 1) p.ψ).sub
      (hasDerivAt_exp_line (w 0 - p.σ * w 2 + w 1) p.ψ)).sub
      ((hasDerivAt_exp_line ((1 + p.ω) * w 0) (p.θ * p.m)).sub
        (hasDerivAt_exp_line (w 0 - p.σ * w 2) (p.θ * p.m)))
    refine (h.congr_deriv (by simp [DQ0]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Gadj_eq, Hmc, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      Pi.sub_apply]
    ring_nf
  · have h1 := hasDerivAt_exp_line1 (w 2)
    have h2 := hasDerivAt_exp_line1 (w 0)
    have h3 := ((hasDerivAt_exp_line1 (w 1)).sub_const 1).pow 2
    have h4 := (h3.const_mul (p.ψ / 2)).const_sub 1
    have h := h1.sub (h2.mul h4)
    refine (h.congr_deriv (by simp [DQ0])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply]

/-- Woodford (2003), App. A.3: the derivative of `N` along `t ↦ (0, tw)` at the steady state. -/
theorem hasDerivAt_Nmap_line (w : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => Nmap p (0, t • w) i) (DN0 p w i) 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := hasDerivAt_exp_line (-(p.σ * w 2) - w 1) 1
    refine (h.congr_deriv (by simp [DN0])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul]
    ring_nf
  · have h := (hasDerivAt_exp_line (w 0 - p.σ * w 2 + 2 * w 1) (-(p.β * p.ψ))).sub
      (hasDerivAt_exp_line (w 0 - p.σ * w 2 + w 1) (-(p.β * p.ψ)))
    refine (h.congr_deriv (by simp [DN0]; ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Nmap, Matrix.cons_val, Gadj_eq, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring_nf
  · simp only [Nmap, DN0, Matrix.cons_val, Fin.isValue]
    exact hasDerivAt_const _ _

/-- Woodford (2003), App. A.3: the derivative of `Q` along `t ↦ (te, 0)` at the steady state. -/
theorem hasDerivAt_Qmap_eps (e : Fin 3 → ℝ) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => Qmap p (t • e, 0) i) (DQe p e i) 0 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · have h := hasDerivAt_exp_line (-(e 0)) (-1)
    refine (h.congr_deriv (by simp [DQe])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring_nf
  · have h := (hasDerivAt_exp_line 0 (p.θ * p.m)).sub
      (hasDerivAt_exp_line (e 2 - (1 + p.ω) * e 1) (p.θ * p.m))
    refine (h.congr_deriv (by simp [DQe])).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [Qmap, Matrix.cons_val, Gadj, Hmc, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simp
    ring_nf
  · simp only [Qmap, DQe, Matrix.cons_val, Pi.zero_apply]
    simp only [Real.exp_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, one_mul]
    exact hasDerivAt_const _ _

/-- Woodford (2003), App. A.3: the partial derivative of `Q` in `x` at the steady state is `DQ`. -/
theorem fderiv_Qmap_inr (v : Fin 3 → ℝ) : fderiv ℝ (Qmap p) (0, 0) (0, v) = DQ0 p v := by
  have hd : HasFDerivAt (Qmap p) (fderiv ℝ (Qmap p) (0, 0)) (0, 0) :=
    ((contDiff_Qmap (p := p) (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 3 → ℝ), t • v)) ((0 : Fin 3 → ℝ), v) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : Fin 3 → ℝ)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Qmap_line v i)

/-- Woodford (2003), App. A.3: the partial derivative of `N` in `x` at the steady state is `DN`. -/
theorem fderiv_Nmap_inr (v : Fin 3 → ℝ) : fderiv ℝ (Nmap p) (0, 0) (0, v) = DN0 p v := by
  have hd : HasFDerivAt (Nmap p) (fderiv ℝ (Nmap p) (0, 0)) (0, 0) :=
    ((contDiff_Nmap (p := p) (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => ((0 : Fin 3 → ℝ), t • v)) ((0 : Fin 3 → ℝ), v) 0 := by
    have := (hasDerivAt_const (0 : ℝ) (0 : Fin 3 → ℝ)).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const v)
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Nmap_line v i)

/-- Woodford (2003), App. A.3: the partial derivative of `Q` in the disturbances is `DQe`. -/
theorem fderiv_Qmap_inl (e : Fin 3 → ℝ) : fderiv ℝ (Qmap p) (0, 0) (e, 0) = DQe p e := by
  have hd : HasFDerivAt (Qmap p) (fderiv ℝ (Qmap p) (0, 0)) (0, 0) :=
    ((contDiff_Qmap (p := p) (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => (t • e, (0 : Fin 3 → ℝ))) (e, (0 : Fin 3 → ℝ)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).prodMk
      (hasDerivAt_const (0 : ℝ) (0 : Fin 3 → ℝ))
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact hc.unique (hasDerivAt_pi.2 fun i => hasDerivAt_Qmap_eps e i)

/-- Woodford (2003), App. A.3: `N` does not depend on the disturbances, so its partial
derivative in them vanishes. -/
theorem fderiv_Nmap_inl (e : Fin 3 → ℝ) : fderiv ℝ (Nmap p) (0, 0) (e, 0) = 0 := by
  have hd : HasFDerivAt (Nmap p) (fderiv ℝ (Nmap p) (0, 0)) (0, 0) :=
    ((contDiff_Nmap (p := p) (n := 1)).differentiable one_ne_zero).differentiableAt.hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => (t • e, (0 : Fin 3 → ℝ))) (e, (0 : Fin 3 → ℝ)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).prodMk
      (hasDerivAt_const (0 : ℝ) (0 : Fin 3 → ℝ))
    simpa using this
  have hc := hd.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  refine hc.unique ?_
  have : (fun t : ℝ => Nmap p (t • e, 0)) = fun _ => Nmap p (0, 0) := by
    funext t; simp [Nmap]
  change HasDerivAt (fun t : ℝ => Nmap p (t • e, 0)) 0 0
  rw [this]
  exact hasDerivAt_const _ _

/-! ## The linearised operator and its inverse -/

variable {X : Type*}

/-- Woodford (2003), App. A.3, (A.12) in Markov form: `(L v)(x) = DQ v(x) + M[DN v](x)`. -/
noncomputable def Lop (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v : X → Fin 3 → ℝ) :
    X → Fin 3 → ℝ :=
  fun x => DQ0 p (v x) + Mv M (fun x' => DN0 p (v x')) x

/-- Woodford (2003), (A.12) with Rotemberg pricing: the three components of `L`: the linearised
IS curve with the rule, the linearised pricing condition and the linearised resource
constraint. -/
theorem Lop_apply (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v : X → Fin 3 → ℝ) (x : X) :
    Lop p M v x 0 = p.φy * v x 0 + p.φ * v x 1 + p.σ * v x 2 - p.σ * M (fun x' => v x' 2) x -
        M (fun x' => v x' 1) x ∧
    Lop p M v x 1 = p.ψ * v x 1 - p.θ * p.m * (p.ω * v x 0 + p.σ * v x 2) -
        p.β * p.ψ * M (fun x' => v x' 1) x ∧
    Lop p M v x 2 = v x 2 - v x 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have h := M_lin M (-p.σ) (-1) (fun x' => v x' 2) (fun x' => v x' 1) x
    have e : (fun x' => -p.σ * v x' 2 + -1 * v x' 1) = fun x' => -(p.σ * v x' 2) - v x' 1 := by
      funext; ring
    rw [e] at h
    simp only [Lop, DN0, DQ0, Mv, Pi.add_apply, Matrix.cons_val_zero]
    rw [h]; ring
  · have h := M_lin M (-(p.β * p.ψ)) 0 (fun x' => v x' 1) (fun x' => v x' 1) x
    have e : (fun x' => -(p.β * p.ψ) * v x' 1 + 0 * v x' 1) =
        fun x' => -(p.β * p.ψ * v x' 1) := by
      funext; ring
    rw [e] at h
    simp only [Lop, DN0, DQ0, Mv, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h]; ring
  · have h0 : M (fun _ => (0 : ℝ)) x = 0 := by
      have : (fun _ : X => (0 : ℝ)) = 0 := rfl
      rw [this, map_zero]; rfl
    simp only [Lop, DN0, DQ0, Mv, Pi.add_apply]
    simp only [show (2 : Fin 3) = Fin.succ 1 from rfl, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [h0, add_zero]

/-- Woodford (2003), Ch. 3 fn. 44 with Ch. 4 (2.7) (**the linearised model is the IS curve plus
the NKPC with the Rotemberg slope**): if `L v = 0` then, state by state, `ĉ = ŷ`,
`(σ + φ_y)ŷ + φ_π π = σ E ŷ′ + E π′` and `π = κ ŷ + β E π′`. -/
theorem lin_nkpc (hp : p.Basic) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) {v : X → Fin 3 → ℝ}
    (hv : Lop p M v = 0) (x : X) :
    v x 2 = v x 0 ∧
    (p.σ + p.φy) * v x 0 + p.φ * v x 1 =
      p.σ * M (fun x' => v x' 0) x + M (fun x' => v x' 1) x ∧
    v x 1 = p.κ * v x 0 + p.β * M (fun x' => v x' 1) x := by
  have z : ∀ x' i, Lop p M v x' i = 0 := fun x' i => by rw [hv]; rfl
  have e2 : ∀ x', v x' 2 = v x' 0 := fun x' => by
    have := z x' 2; rw [(Lop_apply (p := p) M v x').2.2] at this; linarith
  have hfun : (fun x' => v x' 2) = fun x' => v x' 0 := funext e2
  obtain ⟨h0, h1, -⟩ := Lop_apply (p := p) M v x
  have z0 := z x 0
  have z1 := z x 1
  rw [h0, hfun, e2 x] at z0
  rw [h1, e2 x] at z1
  have hk := hp.κ_mul
  have hψ := hp.ψ_pos
  refine ⟨e2 x, by linarith, ?_⟩
  have : p.ψ * (v x 1 - p.κ * v x 0 - p.β * M (fun x' => v x' 1) x) = 0 := by
    linear_combination z1 - v x 0 * hk
  have := (mul_eq_zero.1 this).resolve_left hψ.ne'
  linarith

/-- Woodford (2003), App. A.3 (**forward stability**): if `mnorm(Aᵏ) → 0`, a bounded solution of
`u = A M u` on any state space with any Markov operator vanishes. -/
theorem homog_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Tendsto (fun k => mnorm (A ^ k)) atTop (𝓝 0)) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)}
    (hM : IsMarkov M) {u : X → Fin n → ℝ} {U : ℝ} (hu : ∀ x, ‖u x‖ ≤ U)
    (heq : ∀ x, u x = A.mulVec (Mv M u x)) (x : X) : u x = 0 := by
  have hU : 0 ≤ U := (norm_nonneg _).trans (hu x)
  have heq' : ∀ x, u x = A.mulVec (Mv M u x) + (fun _ => (0 : Fin n → ℝ)) x := fun x => by
    simpa using heq x
  have hz : ∀ k, (Mv M)^[k] (fun _ => (0 : Fin n → ℝ)) = fun _ => 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, Mv_zero, ih]
  have hb : ∀ m, ‖u x‖ ≤ mnorm (A ^ m) * U := fun m => by
    rw [iterate_eq M A heq' m x]
    simp only [hz, Matrix.mulVec_zero, Finset.sum_const_zero, zero_add]
    exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (iter_norm_le hM m hU hu x)
      (mnorm_nonneg _))
  have hl : Tendsto (fun m => mnorm (A ^ m) * U) atTop (𝓝 0) := by
    simpa using hA.mul_const U
  exact norm_le_zero_iff.1 (ge_of_tendsto' hl hb)

/-- The forcing `g₀ = r₀ + φ_y r₂` of the IS equation in `(ĉ, π)`. -/
noncomputable def gR0 (p : Par) (r : X → Fin 3 → ℝ) (x : X) : ℝ := r x 0 + p.φy * r x 2

/-- The forcing `g₁ = (r₁ − θmω r₂)/ψ` of the NKPC in `(ĉ, π)`. -/
noncomputable def gR1 (p : Par) (r : X → Fin 3 → ℝ) (x : X) : ℝ :=
  (r x 1 - p.θ * p.m * p.ω * r x 2) / p.ψ

/-- The forcing `b = B₀⁻¹ g` of the IS–AS block. -/
noncomputable def bR (p : Par) (r : X → Fin 3 → ℝ) : X → Fin 2 → ℝ :=
  fun x => ![(gR0 p r x - p.φ * gR1 p r x) / p.dd,
    (p.κ * gR0 p r x + (p.σ + p.φy) * gR1 p r x) / p.dd]

/-- The IS–AS block `(ĉ, π)` solving `u = AMu + b` forward. -/
noncomputable def uR (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 3 → ℝ) :
    X → Fin 2 → ℝ :=
  fwdSol (Arot p) M (bR p r)

/-- Woodford (2003), App. A.3, (A.13) with Rotemberg pricing (**the inverse of the linearised
operator**): `(ĉ, π)` from the IS–AS block, `ŷ = ĉ − r₂` from the resource constraint. -/
noncomputable def linSol (p : Par) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 3 → ℝ) :
    X → Fin 3 → ℝ :=
  fun x => ![uR p M r x 0 - r x 2, uR p M r x 1, uR p M r x 0]

/-- The constant of the forcing bound `‖b‖ ≤ c_b ‖r‖`. -/
noncomputable def cb (p : Par) : ℝ :=
  ((1 + p.φy) * (1 + p.κ) + (p.φ + p.σ + p.φy) * ((1 + p.θ * p.m * p.ω) / p.ψ)) / p.dd

/-- The constant `K = (∑ mnorm(Aᵏ)) c_b + 1` of the inverse bound `‖L⁻¹r‖ ≤ K‖r‖`. -/
noncomputable def KL (p : Par) : ℝ := (∑' k, mnorm (Arot p ^ k)) * cb p + 1

/-- The forcing constant is nonnegative. -/
theorem cb_nonneg (hp : p.Basic) : 0 ≤ cb p := by
  unfold cb
  have := hp.κ_pos; have := hp.φy_nonneg; have := hp.φ_nonneg; have := hp.σ_pos
  have := hp.ψ_pos; have := hp.dd_pos; have := hp.m_pos; have := hp.ω_nonneg
  have : 0 < p.θ := by linarith [hp.one_lt_θ]
  positivity

/-- The inverse constant is positive. -/
theorem KL_pos (hp : p.Basic) : 0 < KL p := by
  unfold KL
  have h0 : 0 ≤ ∑' k, mnorm (Arot p ^ k) := tsum_nonneg fun k => mnorm_nonneg _
  have := mul_nonneg h0 (cb_nonneg hp)
  linarith

/-- Woodford (2003), App. A.3: the forcing of the IS–AS block is bounded by `c_b ‖r‖`. -/
theorem norm_bR_le (hp : p.Basic) {r : X → Fin 3 → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hr : ∀ x, ‖r x‖ ≤ a) (x : X) : ‖bR p r x‖ ≤ cb p * a := by
  have hrc : ∀ i, |r x i| ≤ a := fun i => by
    have := norm_le_pi_norm (r x) i; rw [Real.norm_eq_abs] at this; exact this.trans (hr x)
  have hd := hp.dd_pos
  have hψ := hp.ψ_pos
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  have hc0 : 0 ≤ p.θ * p.m * p.ω := mul_nonneg (mul_nonneg hθ.le hp.m_pos.le) hp.ω_nonneg
  have h0 : |gR0 p r x| ≤ (1 + p.φy) * a := by
    unfold gR0
    calc |r x 0 + p.φy * r x 2| ≤ |r x 0| + |p.φy * r x 2| := abs_add_le _ _
      _ = |r x 0| + p.φy * |r x 2| := by rw [abs_mul, abs_of_nonneg hp.φy_nonneg]
      _ ≤ a + p.φy * a := add_le_add (hrc 0) (mul_le_mul_of_nonneg_left (hrc 2) hp.φy_nonneg)
      _ = _ := by ring
  have h1 : |gR1 p r x| ≤ (1 + p.θ * p.m * p.ω) / p.ψ * a := by
    unfold gR1
    rw [abs_div, abs_of_pos hψ, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hψ]
    calc |r x 1 - p.θ * p.m * p.ω * r x 2| ≤ |r x 1| + |p.θ * p.m * p.ω * r x 2| := abs_sub _ _
      _ = |r x 1| + p.θ * p.m * p.ω * |r x 2| := by rw [abs_mul, abs_of_nonneg hc0]
      _ ≤ a + p.θ * p.m * p.ω * a := add_le_add (hrc 1) (mul_le_mul_of_nonneg_left (hrc 2) hc0)
      _ = _ := by ring
  have hG1 : 0 ≤ (1 + p.θ * p.m * p.ω) / p.ψ := by positivity
  have hκ := hp.κ_pos
  have e : cb p * a * p.dd =
      ((1 + p.φy) * (1 + p.κ) + (p.φ + p.σ + p.φy) * ((1 + p.θ * p.m * p.ω) / p.ψ)) * a := by
    unfold cb; field_simp
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (cb_nonneg hp) ha)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · simp only [bR, Fin.zero_eta, Matrix.cons_val_zero]
    rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, e]
    calc |gR0 p r x - p.φ * gR1 p r x| ≤ |gR0 p r x| + |p.φ * gR1 p r x| := abs_sub _ _
      _ = |gR0 p r x| + p.φ * |gR1 p r x| := by rw [abs_mul, abs_of_nonneg hp.φ_nonneg]
      _ ≤ (1 + p.φy) * a + p.φ * ((1 + p.θ * p.m * p.ω) / p.ψ * a) :=
          add_le_add h0 (mul_le_mul_of_nonneg_left h1 hp.φ_nonneg)
      _ ≤ _ := by
          have := hp.σ_pos; have := hp.φy_nonneg
          nlinarith [mul_nonneg (mul_nonneg hκ.le (by linarith : (0 : ℝ) ≤ 1 + p.φy)) ha,
            mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ p.σ + p.φy) hG1) ha]
  · simp only [bR, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [abs_div, abs_of_pos hd, div_le_iff₀ hd, e]
    have hs : 0 ≤ p.σ + p.φy := by linarith [hp.σ_pos, hp.φy_nonneg]
    calc |p.κ * gR0 p r x + (p.σ + p.φy) * gR1 p r x| ≤
          |p.κ * gR0 p r x| + |(p.σ + p.φy) * gR1 p r x| := abs_add_le _ _
      _ = p.κ * |gR0 p r x| + (p.σ + p.φy) * |gR1 p r x| := by
          rw [abs_mul, abs_mul, abs_of_pos hκ, abs_of_nonneg hs]
      _ ≤ p.κ * ((1 + p.φy) * a) + (p.σ + p.φy) * ((1 + p.θ * p.m * p.ω) / p.ψ * a) :=
          add_le_add (mul_le_mul_of_nonneg_left h0 hκ.le) (mul_le_mul_of_nonneg_left h1 hs)
      _ ≤ _ := by
          have := hp.φy_nonneg
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + p.φy) ha,
            mul_nonneg (mul_nonneg hp.φ_nonneg hG1) ha]

/-- Woodford (2003), App. A.3, (A.12)–(A.13) with Rotemberg pricing (**the IS–AS block solves the
linearised model**): if `u = (ĉ, π)` solves `u = A M u + b(r)` then
`v = (ĉ − r₂, π, ĉ)` solves `L v = r`. -/
theorem Lop_block (hb : p.Basic) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (r : X → Fin 3 → ℝ)
    (u : X → Fin 2 → ℝ) (hu : ∀ x, u x = (Arot p).mulVec (Mv M u x) + bR p r x) :
    Lop p M (fun x => ![u x 0 - r x 2, u x 1, u x 0]) = r := by
  set w : X → Fin 3 → ℝ := fun x => ![u x 0 - r x 2, u x 1, u x 0] with hw
  funext x
  have hd := hb.dd_pos
  have hψ := hb.ψ_pos
  have hA0 : ∀ y : Fin 2 → ℝ, (Arot p).mulVec y 0 =
      p.σ / p.dd * y 0 + (1 - p.φ * p.β) / p.dd * y 1 := fun y => by
    simp [Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hA1 : ∀ y : Fin 2 → ℝ, (Arot p).mulVec y 1 =
      p.κ * p.σ / p.dd * y 0 + (p.κ + p.β * (p.σ + p.φy)) / p.dd * y 1 := fun y => by
    simp [Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h0 : u x 0 = p.σ / p.dd * Mv M (u) x 0 +
      (1 - p.φ * p.β) / p.dd * Mv M (u) x 1 +
      (gR0 p r x - p.φ * gR1 p r x) / p.dd := by
    have := congrFun (hu x) 0
    rw [Pi.add_apply, hA0] at this
    rw [this]; rfl
  have h1 : u x 1 = p.κ * p.σ / p.dd * Mv M (u) x 0 +
      (p.κ + p.β * (p.σ + p.φy)) / p.dd * Mv M (u) x 1 +
      (p.κ * gR0 p r x + (p.σ + p.φy) * gR1 p r x) / p.dd := by
    have := congrFun (hu x) 1
    rw [Pi.add_apply, hA1] at this
    rw [this]; rfl
  have m2 : M (fun x' => w x' 2) x = Mv M (u) x 0 := rfl
  have m1 : M (fun x' => w x' 1) x = Mv M (u) x 1 := rfl
  have s0 : w x 0 = u x 0 - r x 2 := rfl
  have s1 : w x 1 = u x 1 := rfl
  have s2 : w x 2 = u x 0 := rfl
  obtain ⟨l0, l1, l2⟩ := Lop_apply (p := p) M (w) x
  funext i
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [l0, m2, m1, s0, s1, s2, h0, h1]
    unfold gR0 gR1
    field_simp
    unfold Par.dd
    ring
  · simp only [Fin.mk_one]
    rw [l1, m1, s0, s1, s2]
    rw [show p.θ * p.m * (p.ω * (u x 0 - r x 2) + p.σ * u x 0) =
      p.κ * p.ψ * u x 0 - p.θ * p.m * p.ω * r x 2 by rw [hb.κ_mul]; ring]
    rw [h0, h1]
    unfold gR0 gR1
    field_simp
    unfold Par.dd
    ring
  · simp only [Fin.reduceFinMk]
    rw [l2, s0, s2]
    ring

/-- Woodford (2003), App. A.3, (A.12)–(A.13) with Rotemberg pricing (**the linearised operator is
ONTO bounded functions, for any Markov operator, with a uniform inverse bound**): for bounded `r`,
`‖linSol r‖ ≤ K sup‖r‖` and `L(linSol r) = r`. -/
theorem linSol_spec (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {r : X → Fin 3 → ℝ} {a : ℝ} (ha : 0 ≤ a) (hr : ∀ x, ‖r x‖ ≤ a) :
    (∀ x, ‖linSol p M r x‖ ≤ KL p * a) ∧ Lop p M (linSol p M r) = r := by
  have hb := hp.basic
  obtain ⟨hub, hrec⟩ := fwdSol_spec (summable_Arot hp) hM (mul_nonneg (cb_nonneg hb) ha)
    (norm_bR_le hb ha hr)
  have hrc : ∀ x i, |r x i| ≤ a := fun x i => by
    have := norm_le_pi_norm (r x) i; rw [Real.norm_eq_abs] at this; exact this.trans (hr x)
  set S := ∑' k, mnorm (Arot p ^ k) with hS
  have huc : ∀ x i, |uR p M r x i| ≤ S * (cb p * a) := fun x i => by
    have := norm_le_pi_norm (uR p M r x) i; rw [Real.norm_eq_abs] at this
    exact this.trans (hub x)
  refine ⟨fun x => ?_, ?_⟩
  · have hK : S * (cb p * a) + a = KL p * a := by unfold KL; ring
    have hSa : 0 ≤ S * (cb p * a) :=
      mul_nonneg (tsum_nonneg fun k => mnorm_nonneg _) (mul_nonneg (cb_nonneg hb) ha)
    refine (pi_norm_le_iff_of_nonneg (by rw [← hK]; linarith)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← hK]
    fin_cases i
    · simp only [linSol, Fin.zero_eta, Matrix.cons_val_zero]
      exact (abs_sub _ _).trans (add_le_add (huc x 0) (hrc x 2))
    · simp only [linSol, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith [huc x 1]
    · simp only [linSol, Fin.reduceFinMk, Matrix.cons_val]
      linarith [huc x 0]
  · exact Lop_block hb M r (uR p M r) hrec

/-- Woodford (2003), App. A.3 and Proposition 4.3 (**the a-priori injectivity, uniform over
Markov operators**): under the Taylor principle a bounded `v` with `L v = 0` vanishes. -/
theorem Lop_injective (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {v : X → Fin 3 → ℝ} {V : ℝ} (hv : ∀ x, ‖v x‖ ≤ V) (h0 : Lop p M v = 0) : v = 0 := by
  have hb := hp.basic
  have hd := hb.dd_pos
  have hψ := hb.ψ_pos
  set u : X → Fin 2 → ℝ := fun x => ![v x 2, v x 1] with hu
  have hl := fun x => lin_nkpc hb M h0 x
  have hfun : (fun x' => v x' 2) = fun x' => v x' 0 := funext fun x' => (hl x').1
  have huB : ∀ x, ‖u x‖ ≤ V := fun x => by
    refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hv x))).2 fun i => ?_
    fin_cases i
    · simpa [hu] using norm_le_pi_norm (v x) 2 |>.trans (hv x)
    · simpa [hu] using norm_le_pi_norm (v x) 1 |>.trans (hv x)
  have heq : ∀ x, u x = (Arot p).mulVec (Mv M u x) := fun x => by
    obtain ⟨e2, e0, e1⟩ := hl x
    have mu0 : Mv M u x 0 = M (fun x' => v x' 0) x := by
      change M (fun x' => v x' 2) x = _; rw [hfun]
    have mu1 : Mv M u x 1 = M (fun x' => v x' 1) x := rfl
    funext i
    fin_cases i
    · simp only [hu, Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.zero_eta] at mu0 mu1 ⊢
      rw [mu0, mu1, e2]
      field_simp
      unfold Par.dd
      linear_combination e0 - p.φ * e1
    · simp only [hu, Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Fin.mk_one] at mu0 mu1 ⊢
      rw [mu0, mu1]
      field_simp
      unfold Par.dd
      linear_combination p.κ * e0 + (p.σ + p.φy) * e1
  have hz := homog_zero (summable_Arot hp).tendsto_atTop_zero hM huB heq
  funext x i
  have h2 : v x 2 = 0 := by have := congrFun (hz x) 0; simpa [hu] using this
  have h1 : v x 1 = 0 := by have := congrFun (hz x) 1; simpa [hu] using this
  have e2 := (hl x).1
  fin_cases i
  · simp only [Fin.zero_eta, Pi.zero_apply]; linarith
  · exact h1
  · exact h2

/-- Woodford (2003), Proposition 4.3, Rotemberg slope: if `L v = 0` then `u = (ĉ, π)` solves the
homogeneous IS–AS block `u = A M u` (any Markov operator). -/
theorem homog_block (hb : p.Basic) (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) {v : X → Fin 3 → ℝ}
    (h0 : Lop p M v = 0) :
    ∀ x, (fun x => (![v x 2, v x 1] : Fin 2 → ℝ)) x =
      (Arot p).mulVec (Mv M (fun x => (![v x 2, v x 1] : Fin 2 → ℝ)) x) := by
  have hd := hb.dd_pos
  set u : X → Fin 2 → ℝ := fun x => ![v x 2, v x 1] with hu
  have hl := fun x => lin_nkpc hb M h0 x
  have hfun : (fun x' => v x' 2) = fun x' => v x' 0 := funext fun x' => (hl x').1
  intro x
  obtain ⟨e2, e0, e1⟩ := hl x
  have mu0 : Mv M u x 0 = M (fun x' => v x' 0) x := by
    change M (fun x' => v x' 2) x = _; rw [hfun]
  have mu1 : Mv M u x 1 = M (fun x' => v x' 1) x := rfl
  funext i
  fin_cases i
  · simp only [hu, Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.zero_eta] at mu0 mu1 ⊢
    rw [mu0, mu1, e2]
    field_simp
    unfold Par.dd
    linear_combination e0 - p.φ * e1
  · simp only [hu, Arot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.mk_one] at mu0 mu1 ⊢
    rw [mu0, mu1]
    field_simp
    unfold Par.dd
    linear_combination p.κ * e0 + (p.σ + p.φy) * e1

/-- Woodford (2003), App. A.3: the linearised operator is additive in differences. -/
theorem Lop_sub (M : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (v w : X → Fin 3 → ℝ) :
    Lop p M (fun x => v x - w x) = fun x => Lop p M v x - Lop p M w x := by
  have hq : ∀ a b, DQ0 p (a - b) = DQ0 p a - DQ0 p b := fun a b => by
    funext i; fin_cases i <;> simp [DQ0] <;> ring
  have hn : ∀ a b, DN0 p (a - b) = DN0 p a - DN0 p b := fun a b => by
    funext i; fin_cases i <;> simp [DN0] <;> ring
  funext x
  simp only [Lop, hq]
  have := congrFun (Mv_sub M (fun x' => DN0 p (v x')) (fun x' => DN0 p (w x'))) x
  simp only [← hn] at this
  rw [this]; abel

/-- Woodford (2003), App. A.3: `linSol` inverts `L` on bounded functions, `linSol(Lv) = v`. -/
theorem linSol_Lop (hp : p.Std) {M : (X → ℝ) →ₗ[ℝ] (X → ℝ)} (hM : IsMarkov M)
    {v : X → Fin 3 → ℝ} {a : ℝ} (hLv : ∀ x, ‖Lop p M v x‖ ≤ a) {V : ℝ}
    (hv : ∀ x, ‖v x‖ ≤ V) : linSol p M (Lop p M v) = v := by
  by_cases hX : Nonempty X
  swap
  · funext x; exact absurd ⟨x⟩ hX
  obtain ⟨x0⟩ := hX
  have ha : 0 ≤ a := (norm_nonneg _).trans (hLv x0)
  obtain ⟨hB, hL⟩ := linSol_spec hp hM ha hLv
  have hd : (fun x => linSol p M (Lop p M v) x - v x) = 0 := by
    refine Lop_injective hp hM (V := KL p * a + V) (fun x => (norm_sub_le _ _).trans
      (add_le_add (hB x) (hv x))) ?_
    rw [Lop_sub, hL]; funext x; simp
  funext x
  exact sub_eq_zero.1 (congrFun hd x)

end Woodford.StabilizationWelfare.NonlinearRotemberg
