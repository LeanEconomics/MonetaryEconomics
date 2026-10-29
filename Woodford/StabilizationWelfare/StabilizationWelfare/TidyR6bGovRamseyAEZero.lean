/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6bGovRamseyZero
import StabilizationWelfare.TidyR6bGovRamseyAE

/-!
# The Ramsey equilibrium with purchases when `H = 0`, on a filtered probability space

Woodford (2003), *Interest and Prices*, Chapter 6, §5 (`s_C < 1`), Chapter 7, §1–2, and
Appendix A.3.

The a.s. inverse of `TidyR6bGovRamseyAE` is rebuilt for the case `H = A_uG − γ_G = 0`, where
inflation comes from the targeting rule and output from the NKPC (`TidyR6bGovRamseyZero`):
`pivAZ`, `yvAZ`, `LinvRAZ`, the uniform bounds, **`LRAX_LinvRAZ`**, **`LRAX_injZ`**,
**`adb_LinvRAZ`**, and

* **`gov_ramsey_existence_ae_zero`**: if `s_C > 0`, `H = 0` and `A_uG ≠ 0`, on every filtered
  probability space the TRUE Ramsey conditions with purchases have an adapted solution within
  `r`, a.s. unique among adapted solutions within `r`.
-/

namespace Woodford.StabilizationWelfare.TidyR6bGovRamseyAEZero

universe u

open MeasureTheory Filter Topology
open NonlinearNKMarkov hiding M_lin
open NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree ExpectationsMeasure NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted
open NonlinearNKMarkovRamseyAE TidyR6bGovRamsey TidyR6bGovRamseyTree TidyR6bGovRamseyAE

variable {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- Woodford (2003), Ch. 7: with `H = 0`, inflation from the targeting rule, `π = F/(A_uGθ)`. -/
noncomputable def pivAZ (p : Par) (R : RPar) (_γ : ℝ) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) :
    ℝ :=
  FtvA p R r t ω / (R.Au * Gw p R * p.θ)

/-- Woodford (2003), (2.19) of Ch. 3: with `H = 0`, output from the NKPC. -/
noncomputable def yvAZ (p : Par) (R : RPar) (γ : ℝ) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) :
    ℝ :=
  1 / p.κ * (1 * (1 * pivAZ p R γ r t ω + -p.β * Ms E (pivAZ p R γ r) t ω) +
    -1 * gvA E p r t ω)

/-- Woodford (2003), App. A.3: inflation is `NonlinearNKMarkovRamseyAE.AdB` when `H = 0`. -/
theorem adb_pivAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (_hH0 : R.Au * Gw p R - γ = 0)
    (_hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → RHyp E r A →
        AdB E (pivAZ p R γ r) c A := by
  obtain ⟨c, hc, hb⟩ := adb_fvA R hp
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  refine ⟨|1 / p.θ| * c + |0| * 0, by positivity, fun E r A hA0 hr => ?_⟩
  refine (adb_lin2 E (hb E r A hA0 hr) (adb_zero E A) (1 / p.θ) 0).congr E fun t ω => ?_
  simp only [pivAZ, fvA, zero_mul, add_zero]
  field_simp

/-- Woodford (2003), App. A.3: output is `NonlinearNKMarkovRamseyAE.AdB` when `H = 0`. -/
theorem adb_yvAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (hH0 : R.Au * Gw p R - γ = 0)
    (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → RHyp E r A →
        AdB E (yvAZ E p R γ r) c A := by
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivAZ R hp γ hH0 hAG
  obtain ⟨cg, hcg, hg⟩ := adb_gvA p
  refine ⟨|1 / p.κ| * (|1| * (|1| * cπ + |-p.β| * cπ) + |-1| * cg) + |0| * 0, by positivity,
    fun E r A hA hr => ?_⟩
  refine (adb_lin2 E (adb_lin2 E (adb_lin2 E (hπ E r A hA hr) (adb_Ms E (hπ E r A hA hr)) 1
    (-p.β)) (hg E r A hA hr) 1 (-1)) (adb_zero E A) (1 / p.κ) 0).congr E fun t ω => ?_
  simp only [yvAZ]; ring

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `F̂`. -/
noncomputable def FvAZ (p : Par) (R : RPar) (γ : ℝ) (r : ℕ → Ω → Fin 9 → ℝ) : ℕ → Ω → ℝ :=
  fwdSA E (p.α * p.β) (fun t ω => 1 * ((1 - p.α * p.β) * (1 - p.σ) * yvAZ E p R γ r t ω +
    p.α * p.β * (p.θ - 1) * Ms E (pivAZ p R γ r) t ω) + 1 * r t ω 5)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, the relative price. -/
noncomputable def xvAZ (p : Par) (R : RPar) (γ : ℝ) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) :
    ℝ :=
  (p.α * (p.θ - 1) * pivAZ p R γ r t ω - r t ω 7) / ((1 - p.α) * (p.θ - 1))

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₁`. -/
noncomputable def l1vAZ (p : Par) (R : RPar) (γ : ℝ) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) :
    ℝ :=
  (r t ω 0 + (R.Au * Gw p R - γ) * yvAZ E p R γ r t ω + (1 - R.Φ) * R.Au * DvA p r t ω +
    (1 - p.α * p.β) * (1 + p.ω) * MuvA p R r t ω) / ((1 - p.α * p.β) * (p.σ + p.ω))

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₄`. -/
noncomputable def l4vAZ (p : Par) (R : RPar) (γ : ℝ) (r : ℕ → Ω → Fin 9 → ℝ) : ℕ → Ω → ℝ :=
  fwdSA E (p.α * p.β) (fun t ω => 1 * ((1 - R.Φ) * R.Au * yvAZ E p R γ r t ω +
    p.α * p.β * ramseyLam p R 3 * aE p * Ms E (pivAZ p R γ r) t ω) + 1 * r t ω 4)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₃`. -/
noncomputable def l3vAZ (p : Par) (R : RPar) (γ : ℝ) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) :
    ℝ :=
  (r t ω 2 - (l1vAZ E p R γ r t ω + ramseyLam p R 0 * FvAZ E p R γ r t ω -
    p.α * (lagS (l1vAZ E p R γ r) t ω + ramseyLam p R 0 * ((p.θ - 1) * pivAZ p R γ r t ω +
      FvAZ E p R γ r t ω))) + (1 - p.α) * (aE p / p.c0) * (l4vAZ E p R γ r t ω -
        ramseyLam p R 3 * aE p * xvAZ p R γ r t ω)) / ((1 - p.α) * ((p.θ - 1) / p.c0)) +
  ramseyLam p R 2 * (p.θ - 1) * xvAZ p R γ r t ω

/-- Woodford (2003), Ch. 7 and App. A.3 (**the a.s. inverse in the case `H = 0`**). -/
noncomputable def LinvRAZ (p : Par) (R : RPar) (γ : ℝ) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) :
    Fin 9 → ℝ :=
  ![yvAZ E p R γ r t ω, pivAZ p R γ r t ω, FvAZ E p R γ r t ω,
    FvAZ E p R γ r t ω + p.c0 * xvAZ p R γ r t ω, DvA p r t ω, l1vAZ E p R γ r t ω,
    MuvA p R r t ω - l1vAZ E p R γ r t ω, l3vAZ E p R γ r t ω, l4vAZ E p R γ r t ω]

/-- Woodford (2003), App. A.3: `F̂` is `NonlinearNKMarkovRamseyAE.AdB` and solves its forward
equation a.s. -/
theorem adb_FvAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (FvAZ E p R γ r) c A ∧ ∀ t, FvAZ E p R γ r t =ᵐ[E.μ]
        fun ω => p.α * p.β * Ms E (FvAZ E p R γ r) t ω + (1 * ((1 - p.α * p.β) * (1 - p.σ) *
          yvAZ E p R γ r t ω + p.α * p.β * (p.θ - 1) * Ms E (pivAZ p R γ r) t ω) +
          1 * r t ω 5) := by
  obtain ⟨cy, hcy, hy⟩ := adb_yvAZ R hp γ hH0 hAG
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivAZ R hp γ hH0 hAG
  set k1 := (1 - p.α * p.β) * (1 - p.σ)
  set k2 := p.α * p.β * (p.θ - 1)
  refine ⟨Sg (p.α * p.β) * (|1| * (|k1| * cy + |k2| * cπ) + |1| * 1), by
    have := Sg_nonneg (p.α * p.β); positivity, fun E r A hA hr => ?_⟩
  exact adb_fwd E (abs_ab hp) (by positivity) hA (adb_lin2 E (adb_lin2 E (hy E r A hA hr)
    (adb_Ms E (hπ E r A hA hr)) k1 k2) (hr 5) 1 1)

/-- Woodford (2003), App. A.3: `λ̂₄` is `NonlinearNKMarkovRamseyAE.AdB` and solves its forward
equation a.s. -/
theorem adb_l4vAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (l4vAZ E p R γ r) c A ∧ ∀ t, l4vAZ E p R γ r t =ᵐ[E.μ]
        fun ω => p.α * p.β * Ms E (l4vAZ E p R γ r) t ω + (1 * ((1 - R.Φ) * R.Au *
          yvAZ E p R γ r t ω + p.α * p.β * ramseyLam p R 3 * aE p * Ms E (pivAZ p R γ r) t ω) +
            1 * r t ω 4) := by
  obtain ⟨cy, hcy, hy⟩ := adb_yvAZ R hp γ hH0 hAG
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivAZ R hp γ hH0 hAG
  set k1 := (1 - R.Φ) * R.Au
  set k2 := p.α * p.β * ramseyLam p R 3 * aE p
  refine ⟨Sg (p.α * p.β) * (|1| * (|k1| * cy + |k2| * cπ) + |1| * 1), by
    have := Sg_nonneg (p.α * p.β); positivity, fun E r A hA hr => ?_⟩
  exact adb_fwd E (abs_ab hp) (by positivity) hA (adb_lin2 E (adb_lin2 E (hy E r A hA hr)
    (adb_Ms E (hπ E r A hA hr)) k1 k2) (hr 4) 1 1)

/-- Woodford (2003), App. A.3: the relative price is `NonlinearNKMarkovRamseyAE.AdB`. -/
theorem adb_xvAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (xvAZ p R γ r) c A := by
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivAZ R hp γ hH0 hAG
  set k := 1 / ((1 - p.α) * (p.θ - 1))
  refine ⟨|k * (p.α * (p.θ - 1))| * cπ + |-k| * 1, by positivity, fun E r A hA hr => ?_⟩
  refine (adb_lin2 E (hπ E r A hA hr) (hr 7) (k * (p.α * (p.θ - 1))) (-k)).congr E
    fun t ω => ?_
  simp only [xvAZ, k]; ring

/-- Woodford (2003), App. A.3: `λ̂₁` is `NonlinearNKMarkovRamseyAE.AdB`. -/
theorem adb_l1vAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (l1vAZ E p R γ r) c A := by
  obtain ⟨cy, hcy, hy⟩ := adb_yvAZ R hp γ hH0 hAG
  obtain ⟨cD, hcD, hD⟩ := adb_DvA hp
  obtain ⟨cM, hcM, hM⟩ := adb_MuvA R hp
  set k := 1 / ((1 - p.α * p.β) * (p.σ + p.ω))
  set c1 := |k| * 1 + |k * (R.Au * Gw p R - γ)| * cy
  set c2 := |k * ((1 - R.Φ) * R.Au)| * cD + |k * ((1 - p.α * p.β) * (1 + p.ω))| * cM
  refine ⟨|1| * c1 + |1| * c2, by positivity, fun E r A hA hr => ?_⟩
  refine (adb_lin2 E (adb_lin2 E (hr 0) (hy E r A hA hr) k (k * (R.Au * Gw p R - γ)))
    (adb_lin2 E (hD E r A hA hr) (hM E r A hA hr) (k * ((1 - R.Φ) * R.Au))
      (k * ((1 - p.α * p.β) * (1 + p.ω)))) 1 1).congr E fun t ω => ?_
  simp only [l1vAZ, k]; ring

/-- Woodford (2003), App. A.3: `λ̂₃` is `NonlinearNKMarkovRamseyAE.AdB`. -/
theorem adb_l3vAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (l3vAZ E p R γ r) c A := by
  obtain ⟨c1, hc1, h1⟩ := adb_l1vAZ R hp γ hH0 hAG
  obtain ⟨cF, hcF, hF⟩ := adb_FvAZ R hp γ hH0 hAG
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivAZ R hp γ hH0 hAG
  obtain ⟨c4, hc4, h4⟩ := adb_l4vAZ R hp γ hH0 hAG
  obtain ⟨cx, hcx, hx⟩ := adb_xvAZ R hp γ hH0 hAG
  set k := 1 / ((1 - p.α) * ((p.θ - 1) / p.c0))
  set L0 := ramseyLam p R 0
  set ka := (1 - p.α) * (aE p / p.c0)
  set La := ramseyLam p R 3 * aE p
  set Lb := ramseyLam p R 2 * (p.θ - 1)
  set d1 := |1| * 1 + |-1| * (|1| * c1 + |L0| * cF)
  set d2 := |1| * c1 + |L0| * (|p.θ - 1| * cπ + |1| * cF)
  set d3 := |1| * c4 + |-La| * cx
  refine ⟨|k| * (|1| * (|1| * d1 + |p.α| * d2) + |ka| * d3) + |Lb| * cx, by positivity,
    fun E r A hA hr => ?_⟩
  have hl1 := h1 E r A hA hr
  have hFF := (hF E r A hA hr).1
  have e1 := adb_lin2 E (hr 2) (adb_lin2 E hl1 hFF 1 L0) 1 (-1)
  have e2 := adb_lin2 E (adb_lag E (by positivity) hl1)
    (adb_lin2 E (hπ E r A hA hr) hFF (p.θ - 1) 1) 1 L0
  have e3 := adb_lin2 E (h4 E r A hA hr).1 (hx E r A hA hr) 1 (-La)
  refine (adb_lin2 E (adb_lin2 E (adb_lin2 E e1 e2 1 p.α) e3 1 ka) (hx E r A hA hr) k
    Lb).congr E fun t ω => ?_
  simp only [l3vAZ, k, L0, ka, La, Lb]
  field_simp
  ring

/-! ## The inverse is a right inverse almost surely -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r` a.s.**): for every adapted, a.s.
bounded forcing on every filtered probability space, the constructed process solves the
linearised Ramsey system a.s. at every date. -/
theorem LRAX_LinvRAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0)
    (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ) (hA : 0 ≤ A) (hr : RHyp E r A) (t : ℕ) :
    LRAX E p R γ (LinvRAZ E p R γ r) t =ᵐ[E.μ] r t := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hκ := hp.κ_pos.ne'
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  obtain ⟨_, _, hF⟩ := adb_FvAZ R hp γ hH0 hAG
  obtain ⟨_, _, h4⟩ := adb_l4vAZ R hp γ hH0 hAG
  obtain ⟨_, _, hy⟩ := adb_yvAZ R hp γ hH0 hAG
  obtain ⟨_, _, hπ⟩ := adb_pivAZ R hp γ hH0 hAG
  obtain ⟨_, _, hx⟩ := adb_xvAZ R hp γ hH0 hAG
  have hY := hy E r A hA hr
  have hP := hπ E r A hA hr
  have EF := (hF E r A hA hr).2
  have E4 := (h4 E r A hA hr).2
  have hX := hx E r A hA hr
  set v := LinvRAZ E p R γ r with hvdef
  set y := yvAZ E p R γ r
  set π := pivAZ p R γ r
  set D := DvA p r
  set μ := MuvA p R r
  have ED : ∀ s ω, D s ω = p.α * lagS D s ω + (aE p / (p.θ - 1) * r s ω 7 + 1 * r s ω 8) :=
    fun s ω => bwdS_eq _ _ s ω
  have EM : ∀ s ω, μ s ω = p.α * lagS μ s ω + (1 * (1 * r s ω 2 + 1 * r s ω 3) +
      -(ramseyLam p R 0 * p.c0 / (p.θ - 1)) * r s ω 7) := fun s ω => bwdS_eq _ _ s ω
  have E7 : ∀ s ω, p.α * (p.θ - 1) * π s ω - (1 - p.α) * (p.θ - 1) * xvAZ p R γ r s ω =
      r s ω 7 := fun s ω => by simp only [xvAZ, π]; field_simp; ring
  have Et : ∀ s ω, R.Au * Gw p R * p.θ * π s ω = FtvA p R r s ω := fun s ω => by
    simp only [π, pivAZ]; field_simp; exact mul_div_cancel_left₀ _ hAG
  have Epc : ∀ᵐ ω ∂E.μ, π t ω = p.κ * y t ω + p.β * Ms E π t ω + gvA E p r t ω :=
    Eventually.of_forall fun ω => by simp only [y, yvAZ]; field_simp; ring
  -- the component functions of `v`
  have v0 : (fun s ω => v s ω 0) = y := by funext s ω; simp [hvdef, LinvRAZ, y]
  have v1 : (fun s ω => v s ω 1) = π := by funext s ω; simp [hvdef, LinvRAZ, π]
  have v2 : (fun s ω => v s ω 2) = FvAZ E p R γ r := by funext s ω; simp [hvdef, LinvRAZ]
  have v3 : (fun s ω => v s ω 3) =
      fun s ω => 1 * FvAZ E p R γ r s ω + p.c0 * xvAZ p R γ r s ω := by
    funext s ω; simp [hvdef, LinvRAZ]
  have v4 : (fun s ω => v s ω 4) = D := by funext s ω; simp [hvdef, LinvRAZ, D]
  have v5 : (fun s ω => v s ω 5) = l1vAZ E p R γ r := by funext s ω; simp [hvdef, LinvRAZ]
  have v6 : (fun s ω => v s ω 6) = fun s ω => 1 * μ s ω + -1 * l1vAZ E p R γ r s ω := by
    funext s ω; simp [hvdef, LinvRAZ, μ]; ring
  have v7 : (fun s ω => v s ω 7) = l3vAZ E p R γ r := by funext s ω; simp [hvdef, LinvRAZ]
  have v8 : (fun s ω => v s ω 8) = l4vAZ E p R γ r := by funext s ω; simp [hvdef, LinvRAZ]
  have hl : ∀ s ω k, lagvS v s ω k = lagS (fun s' ω' => v s' ω' k) s ω := fun _ _ _ => rfl
  have hm : ∀ s ω k, MvA E v s ω k = Ms E (fun s' ω' => v s' ω' k) s ω := fun _ _ _ => rfl
  have hvx : ∀ s ω k, v s ω k = (fun s' ω' => v s' ω' k) s ω := fun _ _ _ => rfl
  have E0 : ∀ s ω, -((R.Au * Gw p R - γ) * y s ω) - (1 - R.Φ) * R.Au * D s ω +
      (1 - p.α * p.β) * (p.σ + p.ω) * l1vAZ E p R γ r s ω -
        (1 - p.α * p.β) * (1 + p.ω) * μ s ω = r s ω 0 := fun s ω => by
    simp only [l1vAZ, y, D, μ]; field_simp; ring
  set Rr : ℕ → Ω → Fin 9 → ℝ :=
    fun s ω => DQrX p R γ (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω) with hRr
  have c7 : ∀ s ω, Rr s ω 7 = r s ω 7 := fun s ω => by
    change (DQrX p R γ (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) 7 = r s ω 7
    rw [red_xX, hvx s ω 1, hvx s ω 2, hvx s ω 3, v1, v2, v3]
    simp only
    rw [← E7 s ω]; field_simp; ring
  have c8 : ∀ s ω, Rr s ω 8 = r s ω 8 := fun s ω => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl s ω 4, hvx s ω 1, hvx s ω 2, hvx s ω 3, hvx s ω 4, v1, v2, v3, v4]
    simp only
    linear_combination (norm := (field_simp; ring)) ED s ω - aE p / (p.θ - 1) * E7 s ω
  have c5 : ∀ᵐ ω ∂E.μ, Rr t ω 5 = r t ω 5 := by
    filter_upwards [EF t] with ω h
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm t ω 1, hm t ω 2, hvx t ω 0, hvx t ω 2, v0, v1, v2]
    linear_combination h
  have c4 : ∀ᵐ ω ∂E.μ, Rr t ω 4 = r t ω 4 := by
    filter_upwards [E4 t] with ω h
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm t ω 1, hm t ω 8, hvx t ω 0, hvx t ω 8, v0, v1, v8]
    linear_combination h
  have c0 : ∀ s ω, Rr s ω 0 = r s ω 0 := fun s ω => by
    change (DQrX p R γ (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) 0 = r s ω 0
    rw [← red_l1X R hp γ, hvx s ω 0, hvx s ω 4, hvx s ω 5, hvx s ω 6, v0, v4, v5, v6]
    simp only
    linear_combination E0 s ω
  have c2 : ∀ s ω, Rr s ω 2 = r s ω 2 := fun s ω => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl s ω 5, hvx s ω 1, hvx s ω 2, hvx s ω 3, hvx s ω 5, hvx s ω 7, hvx s ω 8, v1, v2, v3,
      v5, v7, v8]
    simp only [l3vAZ]
    field_simp
    ring
  have hlag56 : ∀ s ω, lagS (fun s' ω' => 1 * μ s' ω' + -1 * l1vAZ E p R γ r s' ω') s ω =
      lagS μ s ω - lagS (l1vAZ E p R γ r) s ω := fun s ω => by
    cases s <;> simp [lagS]; ring
  have c3 : ∀ s ω, Rr s ω 3 = r s ω 3 := fun s ω => by
    have h := red_muX R hp γ (lagvS v s ω) (v s ω) (MvA E v s ω)
    rw [hl s ω 5, hl s ω 6, hvx s ω 5, hvx s ω 6, v5, v6, hlag56] at h
    simp only at h
    have h2 := c2 s ω
    have h7 := c7 s ω
    simp only [hRr] at h2 h7 ⊢
    rw [h2, h7] at h
    linear_combination (-1 : ℝ) * h + EM s ω
  have hm7 : Ms E (fun s ω => r s ω 7) t =ᵐ[E.μ] fun ω => p.α * (p.θ - 1) * Ms E π t ω -
      (1 - p.α) * (p.θ - 1) * ((1 * Ms E (FvAZ E p R γ r) t ω + p.c0 * Ms E (xvAZ p R γ r) t ω -
        Ms E (FvAZ E p R γ r) t ω) / p.c0) := by
    have e : (fun s ω => r s ω 7) = fun s ω => (p.α * (p.θ - 1)) * π s ω +
        (-(1 - p.α) * (p.θ - 1)) * xvAZ p R γ r s ω := by
      funext s ω; rw [← E7 s ω]; ring
    rw [e]
    filter_upwards [Ms_lin2 E hP hX (p.α * (p.θ - 1)) (-(1 - p.α) * (p.θ - 1)) t] with ω h
    rw [h]; field_simp; ring
  have c6 : ∀ᵐ ω ∂E.μ, Rr t ω 6 = r t ω 6 := by
    have hFF := (hF E r A hA hr).1
    filter_upwards [hm7, Epc, Ms_lin2 E hFF hX 1 p.c0 t, c5] with ω hm7' hg hlin h5
    have h := red_pcX R hp γ (lagvS v t ω) (v t ω) (MvA E v t ω)
    have h7 := c7 t ω
    simp only [hRr] at h5 h7 ⊢
    rw [h5, h7, hm t ω 1, hm t ω 2, hm t ω 3, hvx t ω 0, hvx t ω 1, v0, v1, v2, v3, hlin,
      ← hm7'] at h
    simp only [gvA] at hg
    have hk : (1 - p.α) / (p.c0 * p.α) ≠ 0 := div_ne_zero h1α (mul_ne_zero hc0 hα)
    have key : (1 - p.α) / (p.c0 * p.α) *
        ((DQrX p R γ (lagvS v t ω) (v t ω) + DNr p R (MvA E v t ω)) 6 - r t ω 6) = 0 := by
      linear_combination hg - h
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  have c1 : ∀ s ω, Rr s ω 1 = r s ω 1 := fun s ω => by
    have h0m : -((R.Au * Gw p R - γ) * lagvS v s ω 0) - (1 - R.Φ) * R.Au * lagvS v s ω 4 +
        (1 - p.α * p.β) * (p.σ + p.ω) * lagvS v s ω 5 -
          (1 - p.α * p.β) * (1 + p.ω) * (lagvS v s ω 5 + lagvS v s ω 6) =
            lagS (fun s' ω' => r s' ω' 0) s ω := by
      cases s with
      | zero => simp [lagvS, lagS]
      | succ s =>
        have := c0 s ω
        change (DQrX p R γ (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) 0 = r s ω 0 at this
        rw [← red_l1X R hp γ] at this
        exact this
    have h := red_targetX R hp γ (lagvS v s ω) (v s ω) (MvA E v s ω) _ h0m
    have h2 := c2 s ω
    have h7 := c7 s ω
    have h0 := c0 s ω
    simp only [hRr] at h2 h7 h0 ⊢
    rw [h2, h7, h0, hl s ω 0, hl s ω 4, hl s ω 5, hl s ω 6, hvx s ω 0, hvx s ω 1, hvx s ω 4,
      hvx s ω 5, hvx s ω 6, v0, v1, v4, v5, v6, hlag56] at h
    simp only at h
    have hF := Et s ω
    simp only [FtvA] at hF
    have hk : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hab hωσ) (div_ne_zero h1α (mul_ne_zero hα hc0))
    have key : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) *
        ((DQrX p R γ (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) 1 - r s ω 1) = 0 := by
      linear_combination h - hF - (y s ω - lagS y s ω) * hH0
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  filter_upwards [c4, c5, c6] with ω h4' h5' h6'
  funext i
  fin_cases i
  exacts [c0 t ω, c1 t ω, c2 t ω, c3 t ω, h4', h5', h6', c7 t ω, c8 t ω]

/-! ## Injectivity on adapted processes -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**injectivity on adapted processes, a.s.**): an adapted,
a.s. bounded solution of the homogeneous linearised Ramsey system with zero initial lag is `0`
a.s. at every date. -/
theorem LRAX_injZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0)
    (v : ℕ → Ω → Fin 9 → ℝ) (B : ℝ) (_hB : 0 ≤ B) (hv : RHyp E v B)
    (h0 : ∀ t, LRAX E p R γ v t =ᵐ[E.μ] 0) (t : ℕ) : v t =ᵐ[E.μ] 0 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hκ := hp.κ_pos.ne'
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  have hRk : ∀ s, ∀ᵐ ω ∂E.μ, ∀ k,
      (DQrX p R γ (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) k = 0 := fun s => by
    filter_upwards [h0 s] with ω h k
    exact congrFun h k
  set c : Fin 9 → ℕ → Ω → ℝ := fun k s ω => v s ω k with hc
  have hl : ∀ s ω k, lagvS v s ω k = lagS (c k) s ω := fun _ _ _ => rfl
  have hm : ∀ s ω k, MvA E v s ω k = Ms E (c k) s ω := fun _ _ _ => rfl
  have hvx : ∀ s ω k, v s ω k = c k s ω := fun _ _ _ => rfl
  -- the predetermined block
  have hD : ∀ s, c 4 s =ᵐ[E.μ] 0 := zero_of_eq_lagS E (c := p.α) fun s => by
    filter_upwards [hRk s] with ω h
    have := red_DX R hp γ (lagvS v s ω) (v s ω) (MvA E v s ω)
    rw [h 7, h 8, hl] at this; simpa using this
  have hμ : ∀ s, (fun ω => c 5 s ω + c 6 s ω) =ᵐ[E.μ] 0 := zero_of_eq_lagS E (c := p.α)
    (g := fun s ω => c 5 s ω + c 6 s ω) fun s => by
      filter_upwards [hRk s] with ω h
      have := red_muX R hp γ (lagvS v s ω) (v s ω) (MvA E v s ω)
      rw [h 2, h 3, h 7, hl, hl] at this
      have e : lagS (fun s ω => c 5 s ω + c 6 s ω) s ω = lagS (c 5) s ω + lagS (c 6) s ω := by
        cases s <;> simp [lagS]
      simp only [e]; simpa using this
  have hDl : ∀ s, lagS (c 4) s =ᵐ[E.μ] 0 := lagS_zero E hD
  have hμl : ∀ s, (fun ω => lagS (c 5) s ω + lagS (c 6) s ω) =ᵐ[E.μ] 0 := fun s => by
    cases s with
    | zero => exact Eventually.of_forall fun ω => by simp [lagS]
    | succ s => exact hμ s
  -- the expected price-index residual vanishes
  have h7z : ∀ s, (fun ω => p.α * (p.θ - 1) * c 1 s ω - (1 - p.α) * (p.θ - 1) *
      ((c 3 s ω - c 2 s ω) / p.c0)) =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [hRk s] with ω h
    simp only [Pi.zero_apply]
    rw [← h 7, red_xX]
  have hm7 : ∀ s, ∀ᵐ ω ∂E.μ, p.α * (p.θ - 1) * Ms E (c 1) s ω - (1 - p.α) * (p.θ - 1) *
      ((Ms E (c 3) s ω - Ms E (c 2) s ω) / p.c0) = 0 := fun s => by
    have e : (fun s' ω => p.α * (p.θ - 1) * c 1 s' ω - (1 - p.α) * (p.θ - 1) *
        ((c 3 s' ω - c 2 s' ω) / p.c0)) = fun s' ω => (p.α * (p.θ - 1)) * c 1 s' ω +
          (-(1 - p.α) * (p.θ - 1) / p.c0) * (1 * c 3 s' ω + -1 * c 2 s' ω) := by
      funext s' ω; field_simp; ring
    have hz := Ms_zero E (f := fun s' ω => p.α * (p.θ - 1) * c 1 s' ω - (1 - p.α) * (p.θ - 1) *
      ((c 3 s' ω - c 2 s' ω) / p.c0)) (t := s) (h7z (s + 1))
    rw [e] at hz
    filter_upwards [hz, Ms_lin2 E (hv 1) (adb_lin2 E (hv 3) (hv 2) 1 (-1)) (p.α * (p.θ - 1))
      (-(1 - p.α) * (p.θ - 1) / p.c0) s, Ms_lin2 E (hv 3) (hv 2) 1 (-1) s] with ω h1 h2 h3
    rw [h2, h3] at h1
    simp only [Pi.zero_apply] at h1
    linear_combination (norm := (field_simp; ring)) h1
  -- the output condition at the parent
  have h0m : ∀ s, ∀ᵐ ω ∂E.μ, -((R.Au * Gw p R - γ) * lagvS v s ω 0) -
      (1 - R.Φ) * R.Au * lagvS v s ω 4 + (1 - p.α * p.β) * (p.σ + p.ω) * lagvS v s ω 5 -
        (1 - p.α * p.β) * (1 + p.ω) * (lagvS v s ω 5 + lagvS v s ω 6) = 0 := fun s => by
    cases s with
    | zero => exact Eventually.of_forall fun ω => by simp [lagvS, lagS]
    | succ s =>
      filter_upwards [hRk s] with ω h
      have := red_l1X R hp γ (lagvS v s ω) (v s ω) (MvA E v s ω)
      rw [h 0] at this; exact this
  have hcs : ∀ s, ∀ᵐ ω ∂E.μ, _ := fun s => by
    filter_upwards [hRk s, h0m s, hm7 s] with ω h1 h2 h3
    exact commitment_systemX R hp γ (lagvS v s ω) (v s ω) (MvA E v s ω) (funext h1) h2 h3
  have hπ0 : ∀ s, c 1 s =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [hcs s, hDl s, hμl s] with ω h1 h2 h3
    obtain ⟨-, -, -, h4⟩ := h1
    rw [hl, hl, hl, hl] at h4
    simp only [Pi.zero_apply] at h2 h3
    rw [h2, h3] at h4
    simp only [mul_zero, add_zero, sub_zero] at h4
    have h5 : R.Au * Gw p R * p.θ * c 1 s ω = 0 := by
      simp only [hc]
      linear_combination h4 - (v s ω 0 - lagS (c 0) s ω) * hH0
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd h (mul_ne_zero hAG hθ0)
    · simpa using h
  have hy0 : ∀ s, c 0 s =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [hcs s, hπ0 s, Ms_zero E (hπ0 (s + 1))] with ω h h2 h3
    obtain ⟨-, -, h4, -⟩ := h
    rw [hm] at h4
    simp only [Pi.zero_apply] at h2 h3
    have h5 : p.κ * c 0 s ω = 0 := by
      simp only [hc] at h2 h3 h4 ⊢
      linear_combination -h4 + h2 - p.β * h3
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd h hκ
    · simpa using h
  have hF0 : ∀ s, c 2 s =ᵐ[E.μ] 0 := by
    refine zero_of_eq_cMs E (abs_ab hp) (g := c 2) (B := 1 * B) (hv 2).2 fun s => ?_
    filter_upwards [hRk s, hy0 s, Ms_zero E (t := s) (hπ0 (s + 1))] with ω h h1 h2
    have := h 5
    simp only [DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val, hm] at this
    simp only [Pi.zero_apply] at h1 h2
    rw [hvx, hvx] at this
    rw [h1, h2] at this
    linear_combination this
  have hK0 : ∀ s, c 3 s =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [h7z s, hπ0 s, hF0 s] with ω h h1 h2
    simp only [Pi.zero_apply] at h h1 h2 ⊢
    rw [h1, h2] at h
    have h3 : (1 - p.α) * (p.θ - 1) / p.c0 * c 3 s ω = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (div_ne_zero (mul_ne_zero h1α hθ) hc0)
    · exact h
  have hl10 : ∀ s, c 5 s =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [hRk s, hy0 s, hD s, hμ s] with ω h h1 h2 h3
    have := red_l1X R hp γ (lagvS v s ω) (v s ω) (MvA E v s ω)
    rw [h 0, hvx, hvx, hvx, hvx] at this
    simp only [Pi.zero_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3] at this
    have h4 : (1 - p.α * p.β) * (p.σ + p.ω) * c 5 s ω = 0 := by linear_combination this
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h (mul_ne_zero hab hωσ)
    · exact h
  have hl20 : ∀ s, c 6 s =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [hμ s, hl10 s] with ω h1 h2
    simp only [Pi.zero_apply] at h1 h2 ⊢
    linarith
  have hl40 : ∀ s, c 8 s =ᵐ[E.μ] 0 := by
    refine zero_of_eq_cMs E (abs_ab hp) (g := c 8) (B := 1 * B) (hv 8).2 fun s => ?_
    filter_upwards [hRk s, hy0 s, Ms_zero E (t := s) (hπ0 (s + 1))] with ω h h1 h2
    have := h 4
    simp only [DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val, hm] at this
    simp only [Pi.zero_apply] at h1 h2
    rw [hvx, hvx] at this
    rw [h1, h2] at this
    linear_combination this
  have hl30 : ∀ s, c 7 s =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [hRk s, hπ0 s, hF0 s, hK0 s, hl10 s, hl40 s, lagS_zero E hl10 s] with ω h
      h1 h2 h3 h4 h5 h6
    have := h 2
    simp only [DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val, hl] at this
    simp only [Pi.zero_apply] at h1 h2 h3 h4 h5 h6
    rw [hvx, hvx, hvx, hvx, hvx, hvx] at this
    rw [h1, h2, h3, h4, h5, h6] at this
    have h7 : (1 - p.α) * ((p.θ - 1) / p.c0) * c 7 s ω = 0 := by linear_combination this
    rcases mul_eq_zero.1 h7 with h | h
    · exact absurd h (mul_ne_zero h1α (div_ne_zero hθ hc0))
    · exact h
  filter_upwards [hy0 t, hπ0 t, hF0 t, hK0 t, hD t, hl10 t, hl20 t, hl30 t, hl40 t] with ω
    h0 h1 h2 h3 h4 h5 h6 h7 h8
  funext k
  fin_cases k
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]

/-! ## The uniform bound, linearity and the left inverse -/

/-- Woodford (2003), App. A.3 (**the uniform a.s. bound on the inverse**): every component of
`L⁻¹r` is adapted with `|·| ≤ K·A` a.s., with `K` depending only on the parameters. -/
theorem adb_LinvRAZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ K, 0 ≤ K ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → ∀ k, AdB E (fun t ω => LinvRAZ E p R γ r t ω k) K A := by
  obtain ⟨c0, h0, b0⟩ := adb_yvAZ R hp γ hH0 hAG
  obtain ⟨c1, h1, b1⟩ := adb_pivAZ R hp γ hH0 hAG
  obtain ⟨c2, h2, b2⟩ := adb_FvAZ R hp γ hH0 hAG
  obtain ⟨cx, hx, bx⟩ := adb_xvAZ R hp γ hH0 hAG
  obtain ⟨c4, h4, b4⟩ := adb_DvA hp
  obtain ⟨c5, h5, b5⟩ := adb_l1vAZ R hp γ hH0 hAG
  obtain ⟨cμ, hμ, bμ⟩ := adb_MuvA R hp
  obtain ⟨c7, h7, b7⟩ := adb_l3vAZ R hp γ hH0 hAG
  obtain ⟨c8, h8, b8⟩ := adb_l4vAZ R hp γ hH0 hAG
  set K := c0 + c1 + c2 + (|1| * c2 + |p.c0| * cx) + c4 + c5 + (|1| * cμ + |-1| * c5) + c7 +
    c8 with hK
  refine ⟨K, by positivity, fun E r A hA hr k => ?_⟩
  have hle : ∀ c, 0 ≤ c → c ≤ K → ∀ f, AdB E f c A → AdB E f K A := fun c _ hcK f hf =>
    hf.mono E hcK hA
  have hs3 : 0 ≤ |1| * c2 + |p.c0| * cx := by positivity
  have hs6 : 0 ≤ |1| * cμ + |-1| * c5 := by positivity
  fin_cases k
  · exact hle _ h0 (by rw [hK]; linarith) _ ((b0 E r A hA hr).congr E fun t ω => by simp [LinvRAZ])
  · exact hle _ h1 (by rw [hK]; linarith) _ ((b1 E r A hA hr).congr E fun t ω => by simp [LinvRAZ])
  · exact hle _ h2 (by rw [hK]; linarith) _ (((b2 E r A hA hr).1).congr E fun t ω => by
      simp [LinvRAZ])
  · exact hle _ (by positivity) (by rw [hK]; linarith) _
      ((adb_lin2 E (b2 E r A hA hr).1 (bx E r A hA hr) 1 p.c0).congr E
        fun t ω => by simp [LinvRAZ])
  · exact hle _ h4 (by rw [hK]; linarith) _ ((b4 E r A hA hr).congr E fun t ω => by simp [LinvRAZ])
  · exact hle _ h5 (by rw [hK]; linarith) _ ((b5 E r A hA hr).congr E fun t ω => by simp [LinvRAZ])
  · exact hle _ (by positivity) (by rw [hK]; linarith) _
      ((adb_lin2 E (bμ E r A hA hr) (b5 E r A hA hr) 1 (-1)).congr E
        fun t ω => by simp [LinvRAZ]; ring)
  · exact hle _ h7 (by rw [hK]; linarith) _ ((b7 E r A hA hr).congr E fun t ω => by simp [LinvRAZ])
  · exact hle _ h8 (by rw [hK]; linarith) _ (((b8 E r A hA hr).1).congr E fun t ω => by
      simp [LinvRAZ])


/-! ## Existence and uniqueness when `H = 0`, almost surely -/

open TidyR6bRamseyNewtonAE NonlinearNKMarkovRamseyAEIFT in
/-- Woodford (2003), Ch. 7 and App. A.3 (**the three a.s. properties of the inverse when
`H = 0`**). -/
theorem invBoundA_zero {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hH0 : Hy p R sC = 0) (hAG : R.Au * Gw p R ≠ 0) :
    InvBoundA (QdG p R sC) (Nd p R)
      (fun {Ω : Type u} [MeasurableSpace Ω] E r => LinvRAZ E p R (gamG p R sC) r) := by
  have hH0' : R.Au * Gw p R - gamG p R sC = 0 := hH0
  have hLG : ∀ {Ω : Type u} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (v : ℕ → Ω → Fin 9 → ℝ) (t : ℕ), LGA E (QdG p R sC) (Nd p R) v t =
        LRAX E p R (gamG p R sC) v t := fun E v t => by
    funext ω
    simp only [LGA, LRAX, fderiv_QdG R hp hs, fderiv_Nd]
  obtain ⟨K, hK0, hK⟩ := adb_LinvRAZ R hp (gamG p R sC) hH0' hAG
  refine ⟨⟨K, hK0, fun E r A hA hr k => (hK E r A hA hr k).rescale E⟩,
    fun E r A hA hr t => ?_, fun E v B hB hv h0 t => ?_⟩
  · rw [hLG]; exact LRAX_LinvRAZ E R hp (gamG p R sC) hH0' hAG r A hA hr t
  · exact LRAX_injZ E R hp (gamG p R sC) hH0' hAG v B hB hv (fun s => by rw [← hLG]; exact h0 s) t

open TidyR6bRamseyNewtonAE NonlinearNKMarkovRamseyAEIFT in
/-- **Woodford (2003), Ch. 6, §5 and Ch. 7, §1–2 (EXISTENCE, ADAPTEDNESS AND A.S. UNIQUENESS of
the timeless Ramsey equilibrium with government purchases on a general filtered probability
space).** If `s_C > 0`, `H = 0` and `A_uG ≠ 0`, there are `r, δ > 0` such that on every filtered
probability space, for adapted disturbances `e = (ν, ĉ, τ̂, q, μ̂ʷ, Ĝ)` and an
`𝓕₀`-measurable predetermined initial value `d` with `‖e_t‖, ‖d‖ ≤ δ` a.s., the TRUE Ramsey
conditions with consumption `Y − G` hold a.s. at every date for an adapted `z` with `‖z_t‖ ≤ r`
a.s., and every adapted solution within `r` is a.s. equal to it. -/
theorem gov_ramsey_existence_ae_zero {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hH0 : Hy p R sC = 0) (hAG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ∀ (Ω : Type u) [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)
      (e : ℕ → Ω → Fin 6 → ℝ) (d : Ω → Fin 9 → ℝ), AdA E e → Bd E e δ →
        AEStronglyMeasurable[E.𝓕 0] d E.μ → (∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δ) →
        ∃ z : ℕ → Ω → Fin 9 → ℝ, (AdA E z ∧ Bd E z r ∧
          ∀ t, PhiTrueA E p R sC e d z t =ᵐ[E.μ] 0) ∧
          ∀ z' : ℕ → Ω → Fin 9 → ℝ, AdA E z' → Bd E z' r →
            (∀ t, PhiTrueA E p R sC e d z' t =ᵐ[E.μ] 0) → ∀ t, z' t =ᵐ[E.μ] z t := by
  have hQ : ContDiff ℝ 1 (QdG p R sC) := contDiff_QdG p R sC
  obtain ⟨r0, hr0, δ0, hδ0, C, hC, hN⟩ := newton_ae.{u} hQ (contDiff_Nd p R)
    (QdG_Nd_zero R hp hs) (invBoundA_zero R hp hs hH0 hAG)
  set τ0 := sC / 4 / C with hτ0
  have hτ0p : 0 < τ0 := by positivity
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 (hQ.continuous.continuousAt (x := 0))
    τ0 hτ0p
  set r := min r0 (sC / 4) with hr
  have hrp : 0 < r := lt_min hr0 (by positivity)
  refine ⟨r, hrp, min δ0 (min (δQ / 2) (sC / 4)), lt_min hδ0 (lt_min (by positivity)
    (by positivity)), fun Ω _ E e d he heb hd hdb => ?_⟩
  have he0 : Bd E e δ0 := fun t => by
    filter_upwards [heb t] with ω h; exact h.trans (min_le_left _ _)
  have hd0 : ∀ᵐ ω ∂E.μ, ‖d ω‖ ≤ δ0 := by
    filter_upwards [hdb] with ω h; exact h.trans (min_le_left _ _)
  have heS : Bd E e (sC / 4) := fun t => by
    filter_upwards [heb t] with ω h; exact h.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨z, ⟨hzA, hzB, hz0⟩, huniq, hsmall⟩ := hN Ω E e d he he0 hd hd0
  have hb : Bd E (PhiGA E (QdG p R sC) (Nd p R) e d fun _ _ => 0) τ0 := fun t => by
    have hss := QdG_Nd_zero R hp hs
    filter_upwards [heb t, hdb] with ω h1 h3
    have e1 : PhiGA E (QdG p R sC) (Nd p R) e d (fun _ _ => 0) t ω =
        QdG p R sC (e t ω, lagIA (fun _ _ => 0) d t ω, 0) - QdG p R sC 0 := by
      simp only [PhiGA, MvA_const]
      rw [eq_neg_of_add_eq_zero_right hss]
      abel
    rw [e1, ← dist_eq_norm]
    refine (hQc ?_).le
    rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
    have hl : ‖lagIA (fun _ _ => (0 : Fin 9 → ℝ)) d t ω‖ ≤ δQ / 2 := by
      cases t with
      | zero => exact h3.trans ((min_le_right _ _).trans (min_le_left _ _))
      | succ t => simp only [lagIA, norm_zero]; positivity
    have h0 : ‖(0 : Fin 9 → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
    exact lt_of_le_of_lt (max_le (h1.trans ((min_le_right _ _).trans (min_le_left _ _)))
      (max_le hl h0)) (by linarith)
  have hzS : Bd E z (sC / 4) := fun t => by
    filter_upwards [hsmall τ0 hτ0p.le hb t] with ω h
    rwa [hτ0, mul_div_cancel₀ _ hC.ne'] at h
  refine ⟨z, ⟨hzA, fun t => ?_, fun t => ?_⟩, fun z' hz'A hz'B hz' => ?_⟩
  · filter_upwards [hzB t, hzS t] with ω h1 h2 using le_min h1 h2
  · filter_upwards [PhiTrueA_ae E R hs heS hzS t, hz0 t] with ω h1 h2
    rw [h1, h2]
  · have hz'S : Bd E z' (sC / 4) := fun t => by
      filter_upwards [hz'B t] with ω h using h.trans (min_le_right _ _)
    refine huniq z' hz'A (fun t => by
      filter_upwards [hz'B t] with ω h using h.trans (min_le_left _ _)) fun t => ?_
    filter_upwards [PhiTrueA_ae E R hs heS hz'S t, hz' t] with ω h1 h2
    rw [← h1, h2]

end Woodford.StabilizationWelfare.TidyR6bGovRamseyAEZero
