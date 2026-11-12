/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR6bGovRamseyIFT

/-!
# The Ramsey problem with purchases when the output weight vanishes (`H = 0`)

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (the targeting rule), Chapter 6, §5
(government purchases), and Appendix A.3.

With purchases the output weight of the targeting rule is `H = A_uG − γ_G`
(`TidyR6bGovRamsey.Hy`). When `H = 0` but `A_uG ≠ 0` (possible for `s_C < 1` and `Φ > 0`), the
targeting rule `H(ŷ − ŷ₋) + A_uGθπ = F` pins down INFLATION directly, `π = F/(A_uGθ)`, and the
NKPC then gives output, `ŷ = (π − βE π′ − g)/κ`: the commitment system has no second-order
dynamics at all, and the linearised operator is still invertible.

* `yvZ`, `pivZ` and the rest of the inverse `LinvRZ` (restated from `TidyR6bGovRamseyTree` with the
  algebraic `π`, `ŷ`), the uniform bounds, **`LRX_LinvRZ`**, **`LRX_injZ`**, **`LinvRZ_bound`**.
* **`invBound_zero`**, **`gov_ramsey_existence_zero`**: if `s_C > 0`, `H = 0` and `A_uG ≠ 0`, the
  exact Ramsey conditions with purchases have a solution within `r`, unique within `r`, on every
  event tree.
-/

namespace Woodford.StabilizationWelfare.TidyR6bGovRamseyZero

universe u

open Filter Topology
open NonlinearNKMarkov hiding M_lin
open NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree NonlinearNKMarkovRamseyIFT TidyR6bGovRamsey TidyR6bGovRamseyTree
open TidyR6bRamseyNewton

variable {X : Type*} (T : LagTree X)

/-- Woodford (2003), Ch. 7: with `H = 0`, inflation from the targeting rule, `π = F/(A_uGθ)`. -/
noncomputable def pivZ (p : Par) (R : RPar) (_γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  Ftv T p R r x / (R.Au * Gw p R * p.θ)

/-- Woodford (2003), (2.19) of Ch. 3: with `H = 0`, output from the NKPC,
`ŷ = (π − βE π′ − g)/κ`. -/
noncomputable def yvZ (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (pivZ T p R γ r x - p.β * T.M (pivZ T p R γ r) x - gv T p r x) / p.κ

/-- Woodford (2003), App. A.3: a bound on inflation when `H = 0` (from
`NonlinearNKMarkovRamseyTree.bd_fv`). -/
theorem bd_pivZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (_hH0 : R.Au * Gw p R - γ = 0)
    (_hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
      (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
        ∀ y, |pivZ T p R γ r y| ≤ c * A := by
  obtain ⟨c, hc, hb⟩ := bd_fv R hp
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  refine ⟨|1 / p.θ| * c, by positivity, fun T r A hA0 hr y => ?_⟩
  have e : pivZ T p R γ r y = 1 / p.θ * fv T p R r y := by
    simp only [pivZ, fv]; field_simp
  rw [e, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb T r A hA0 hr y) (abs_nonneg _)

/-- Woodford (2003), App. A.3: a bound on output when `H = 0`. -/
theorem bd_yvZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ) (hH0 : R.Au * Gw p R - γ = 0)
    (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
      (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
        ∀ y, |yvZ T p R γ r y| ≤ c * A := by
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivZ R hp γ hH0 hAG
  obtain ⟨cg, hcg, hg⟩ := bd_gv (p := p)
  refine ⟨|1 / p.κ| * (|1| * (|1| * cπ + |-p.β| * cπ) + |-1| * cg), by positivity,
    fun T r A hA hr y => ?_⟩
  have h := lb2 (lb2 (hπ T r A hA hr) (lbM T (hπ T r A hA hr)) 1 (-p.β)) (hg T r A hA hr) 1 (-1)
  have e := lb2 (g := fun _ => (0 : ℝ)) (cg := 0) h (fun _ => by simp) (1 / p.κ) 0 y
  convert e using 2
  · simp only [yvZ]; ring
  · ring

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse when `H = 0`, `F̂` forward with root `αβ`. -/
noncomputable def FvZ (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) : X → ℝ :=
  fwdS T (p.α * p.β) (fun x => (1 - p.α * p.β) * (1 - p.σ) * yvZ T p R γ r x +
    p.α * p.β * (p.θ - 1) * T.M (pivZ T p R γ r) x + r x 5)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, the relative price `x̂` from the price
index. -/
noncomputable def xvZ (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (p.α * (p.θ - 1) * pivZ T p R γ r x - r x 7) / ((1 - p.α) * (p.θ - 1))

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₁` from the output condition
(`TidyR6bGovRamseyTree.red_l1X`).
-/
noncomputable def l1vZ (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (r x 0 + (R.Au * Gw p R - γ) * yvZ T p R γ r x + (1 - R.Φ) * R.Au * Dv T p r x +
    (1 - p.α * p.β) * (1 + p.ω) * Muv T p R r x) / ((1 - p.α * p.β) * (p.σ + p.ω))

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₄` forward with root `αβ`. -/
noncomputable def l4vZ (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) : X → ℝ :=
  fwdS T (p.α * p.β) (fun x => (1 - R.Φ) * R.Au * yvZ T p R γ r x +
    p.α * p.β * ramseyLam p R 3 * aE p * T.M (pivZ T p R γ r) x + r x 4)

/-- Woodford (2003), Ch. 7 and App. A.3: the inverse, `λ̂₃` from the `F̂` condition. -/
noncomputable def l3vZ (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : ℝ :=
  (r x 2 - (l1vZ T p R γ r x + ramseyLam p R 0 * FvZ T p R γ r x -
    p.α * (lag0 T (l1vZ T p R γ r) x +
    ramseyLam p R 0 * ((p.θ - 1) * pivZ T p R γ r x + FvZ T p R γ r x))) +
    (1 - p.α) * (aE p / p.c0) * (l4vZ T p R γ r x - ramseyLam p R 3 * aE p * xvZ T p R γ r x)) /
      ((1 - p.α) * ((p.θ - 1) / p.c0)) + ramseyLam p R 2 * (p.θ - 1) * xvZ T p R γ r x

/-- Woodford (2003), Ch. 7 and App. A.3 (**the inverse when `H = 0`**). -/
noncomputable def LinvRZ (p : Par) (R : RPar) (γ : ℝ) (r : X → Fin 9 → ℝ) (x : X) : Fin 9 → ℝ :=
  ![yvZ T p R γ r x, pivZ T p R γ r x, FvZ T p R γ r x, FvZ T p R γ r x + p.c0 * xvZ T p R γ r x,
    Dv T p r x, l1vZ T p R γ r x, Muv T p R r x - l1vZ T p R γ r x, l3vZ T p R γ r x,
    l4vZ T p R γ r x]

/-- Woodford (2003), App. A.3: a bound on `F̂` when `H = 0`, and its forward equation. -/
theorem bd_FvZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧
      ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |FvZ T p R γ r y| ≤ c * A) ∧ ∀ y, FvZ T p R γ r y = p.α * p.β * T.M (FvZ T p R γ r) y +
        ((1 - p.α * p.β) * (1 - p.σ) * yvZ T p R γ r y +
          p.α * p.β * (p.θ - 1) * T.M (pivZ T p R γ r) y + r y 5) := by
  obtain ⟨cy, hcy, hy⟩ := bd_yvZ R hp γ hH0 hAG
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivZ R hp γ hH0 hAG
  set k1 := (1 - p.α * p.β) * (1 - p.σ)
  set k2 := p.α * p.β * (p.θ - 1)
  set ci := |1| * (|k1| * cy + |k2| * cπ) + |1| * 1
  refine ⟨Sg (p.α * p.β) * ci, by have := Sg_nonneg (p.α * p.β); positivity,
    fun T r A hA hr => ?_⟩
  have hin := lb2 (lb2 (hy T r A hA hr) (lbM T (hπ T r A hA hr)) k1 k2)
    (f := fun y => k1 * yvZ T p R γ r y + k2 * T.M (pivZ T p R γ r) y) (g := fun y => r y 5)
    (cg := 1) (fun y => by simpa using hr y 5) 1 1
  obtain ⟨h1, h2⟩ := fwdS_spec T (abs_ab hp) (A := ci * A) (by positivity)
    (f := fun y => k1 * yvZ T p R γ r y + k2 * T.M (pivZ T p R γ r) y + r y 5) (fun y => by
      convert hin y using 2; ring)
  exact ⟨fun y => (h1 y).trans (le_of_eq (by ring)), h2⟩

/-- Woodford (2003), App. A.3: a bound on `λ̂₄`, and its forward equation. -/
theorem bd_l4vZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧
      ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |l4vZ T p R γ r y| ≤ c * A) ∧ ∀ y, l4vZ T p R γ r y =
        p.α * p.β * T.M (l4vZ T p R γ r) y +
        ((1 - R.Φ) * R.Au * yvZ T p R γ r y +
          p.α * p.β * ramseyLam p R 3 * aE p * T.M (pivZ T p R γ r) y + r y 4) := by
  obtain ⟨cy, hcy, hy⟩ := bd_yvZ R hp γ hH0 hAG
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivZ R hp γ hH0 hAG
  set k1 := (1 - R.Φ) * R.Au
  set k2 := p.α * p.β * ramseyLam p R 3 * aE p
  set ci := |1| * (|k1| * cy + |k2| * cπ) + |1| * 1
  refine ⟨Sg (p.α * p.β) * ci, by have := Sg_nonneg (p.α * p.β); positivity,
    fun T r A hA hr => ?_⟩
  have hin := lb2 (lb2 (hy T r A hA hr) (lbM T (hπ T r A hA hr)) k1 k2)
    (f := fun y => k1 * yvZ T p R γ r y + k2 * T.M (pivZ T p R γ r) y) (g := fun y => r y 4)
    (cg := 1) (fun y => by simpa using hr y 4) 1 1
  obtain ⟨h1, h2⟩ := fwdS_spec T (abs_ab hp) (A := ci * A) (by positivity)
    (f := fun y => k1 * yvZ T p R γ r y + k2 * T.M (pivZ T p R γ r) y + r y 4) (fun y => by
      convert hin y using 2; ring)
  exact ⟨fun y => (h1 y).trans (le_of_eq (by ring)), h2⟩

/-- Woodford (2003), App. A.3: a bound on the relative price `x̂`. -/
theorem bd_xvZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧
      ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |xvZ T p R γ r y| ≤ c * A := by
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivZ R hp γ hH0 hAG
  set k := 1 / ((1 - p.α) * (p.θ - 1))
  refine ⟨|k * (p.α * (p.θ - 1))| * cπ + |-k| * 1, by positivity, fun T r A hA hr y => ?_⟩
  have := lb2 (hπ T r A hA hr) (g := fun y => r y 7) (cg := 1)
    (fun y => by simpa using hr y 7) (k * (p.α * (p.θ - 1))) (-k) y
  convert this using 2
  simp only [xvZ, k]; ring

/-- Woodford (2003), App. A.3: a bound on `λ̂₁`. -/
theorem bd_l1vZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧
      ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |l1vZ T p R γ r y| ≤ c * A := by
  obtain ⟨cy, hcy, hy⟩ := bd_yvZ R hp γ hH0 hAG
  obtain ⟨cD, hcD, hD⟩ := bd_Dv hp
  obtain ⟨cM, hcM, hM⟩ := bd_Muv R hp
  set k := 1 / ((1 - p.α * p.β) * (p.σ + p.ω))
  set c1 := |k| * 1 + |k * (R.Au * Gw p R - γ)| * cy
  set c2 := |k * ((1 - R.Φ) * R.Au)| * cD + |k * ((1 - p.α * p.β) * (1 + p.ω))| * cM
  refine ⟨|1| * c1 + |1| * c2, by positivity, fun T r A hA hr y => ?_⟩
  have e1 := lb2 (f := fun y => r y 0) (cf := 1) (fun y => by simpa using hr y 0)
    (hy T r A hA hr) k (k * (R.Au * Gw p R - γ))
  have e2 := lb2 (hD T r A hA hr) (hM T r A hA hr) (k * ((1 - R.Φ) * R.Au))
    (k * ((1 - p.α * p.β) * (1 + p.ω)))
  have := lb2 e1 e2 1 1 y
  convert this using 2
  simp only [l1vZ, k]; ring

/-- Woodford (2003), App. A.3: a bound on `λ̂₃`. -/
theorem bd_l3vZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ c, 0 ≤ c ∧
      ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      ∀ y, |l3vZ T p R γ r y| ≤ c * A := by
  obtain ⟨c1, hc1, h1⟩ := bd_l1vZ R hp γ hH0 hAG
  obtain ⟨cF, hcF, hF⟩ := bd_FvZ R hp γ hH0 hAG
  obtain ⟨cπ, hcπ, hπ⟩ := bd_pivZ R hp γ hH0 hAG
  obtain ⟨c4, hc4, h4⟩ := bd_l4vZ R hp γ hH0 hAG
  obtain ⟨cx, hcx, hx⟩ := bd_xvZ R hp γ hH0 hAG
  set k := 1 / ((1 - p.α) * ((p.θ - 1) / p.c0))
  set L0 := ramseyLam p R 0
  set ka := (1 - p.α) * (aE p / p.c0)
  set La := ramseyLam p R 3 * aE p
  set Lb := ramseyLam p R 2 * (p.θ - 1)
  set d1 := |1| * 1 + |-1| * (|1| * c1 + |L0| * cF)
  set d2 := |1| * c1 + |L0| * (|p.θ - 1| * cπ + |1| * cF)
  set d3 := |1| * c4 + |-La| * cx
  refine ⟨|k| * (|1| * (|1| * d1 + |p.α| * d2) + |ka| * d3) + |Lb| * cx, by positivity,
    fun T r A hA hr y => ?_⟩
  have hl1 := h1 T r A hA hr
  have hFF := (hF T r A hA hr).1
  have e1 := lb2 (f := fun y => r y 2) (cf := 1) (fun y => by simpa using hr y 2)
    (lb2 hl1 hFF 1 L0) 1 (-1)
  have e2 := lb2 (lbLag T (by positivity) hl1) (lb2 (hπ T r A hA hr) hFF (p.θ - 1) 1) 1 L0
  have e12 := lb2 e1 e2 1 p.α
  have e3 := lb2 (h4 T r A hA hr).1 (hx T r A hA hr) 1 (-La)
  have e123 := lb2 e12 e3 1 ka
  have := lb2 e123 (hx T r A hA hr) k Lb y
  convert this using 2
  simp only [l3vZ, k, L0, ka, La, Lb]
  field_simp
  ring

/-! ## The inverse is a right inverse -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r`**): for every bounded forcing `r` on
every event tree, the constructed process solves the linearised Ramsey system. -/
theorem LRX_LinvRZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0)
    (r : X → Fin 9 → ℝ) (A : ℝ) (hA : 0 ≤ A) (hr : ∀ y k, |r y k| ≤ A) :
    LRX T p R γ (LinvRZ T p R γ r) = r := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hκ := hp.κ_pos.ne'
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  obtain ⟨_, _, hF⟩ := bd_FvZ R hp γ hH0 hAG
  obtain ⟨_, _, h4⟩ := bd_l4vZ R hp γ hH0 hAG
  have EF := (hF T r A hA hr).2
  have E4 := (h4 T r A hA hr).2
  set v := LinvRZ T p R γ r with hvdef
  set y := yvZ T p R γ r
  set π := pivZ T p R γ r
  set D := Dv T p r
  set μ := Muv T p R r
  -- the scalar equations
  have ED : ∀ x, D x = p.α * lag0 T D x + (aE p / (p.θ - 1) * r x 7 + r x 8) := fun x =>
    bwd_eq T _ _ x
  have EM : ∀ x, μ x = p.α * lag0 T μ x +
      (r x 2 + r x 3 - ramseyLam p R 0 * p.c0 / (p.θ - 1) * r x 7) := fun x => bwd_eq T _ _ x
  have E7 : ∀ x, p.α * (p.θ - 1) * π x - (1 - p.α) * (p.θ - 1) * xvZ T p R γ r x = r x 7 :=
    fun x => by simp only [xvZ, π]; field_simp; ring
  have Et : ∀ x, R.Au * Gw p R * p.θ * π x = Ftv T p R r x := fun x => by
    simp only [π, pivZ]; field_simp; exact mul_div_cancel_left₀ _ hAG
  have Epc : ∀ x, π x = p.κ * y x + p.β * T.M π x + gv T p r x := fun x => by
    simp only [y, yvZ]; field_simp; ring
  -- the component functions of `v`
  have v0 : (fun z => v z 0) = y := by funext z; simp [hvdef, LinvRZ, y]
  have v1 : (fun z => v z 1) = π := by funext z; simp [hvdef, LinvRZ, π]
  have v2 : (fun z => v z 2) = FvZ T p R γ r := by funext z; simp [hvdef, LinvRZ]
  have v3 : (fun z => v z 3) = fun z => 1 * FvZ T p R γ r z + p.c0 * xvZ T p R γ r z := by
    funext z; simp [hvdef, LinvRZ]
  have v4 : (fun z => v z 4) = D := by funext z; simp [hvdef, LinvRZ, D]
  have v5 : (fun z => v z 5) = l1vZ T p R γ r := by funext z; simp [hvdef, LinvRZ]
  have v6 : (fun z => v z 6) = fun z => 1 * μ z + -1 * l1vZ T p R γ r z := by
    funext z; simp [hvdef, LinvRZ, μ]; ring
  have v7 : (fun z => v z 7) = l3vZ T p R γ r := by funext z; simp [hvdef, LinvRZ]
  have v8 : (fun z => v z 8) = l4vZ T p R γ r := by funext z; simp [hvdef, LinvRZ]
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  have hvx : ∀ x k, v x k = (fun z => v z k) x := fun _ _ => rfl
  have E0 : ∀ x, -((R.Au * Gw p R - γ) * y x) - (1 - R.Φ) * R.Au * D x +
      (1 - p.α * p.β) * (p.σ + p.ω) * l1vZ T p R γ r x -
        (1 - p.α * p.β) * (1 + p.ω) * μ x = r x 0 := fun x => by
    simp only [l1vZ, y, D, μ]; field_simp; ring
  -- the nine components
  set Rr : X → Fin 9 → ℝ := fun x => DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x) with hRr
  have c7 : ∀ x, Rr x 7 = r x 7 := fun x => by
    change (DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x)) 7 = r x 7
    rw [red_xX, hvx x 1, hvx x 2, hvx x 3, v1, v2, v3]
    simp only
    rw [← E7 x]; field_simp; ring
  have c8 : ∀ x, Rr x 8 = r x 8 := fun x => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl x 4, hvx x 1, hvx x 2, hvx x 3, hvx x 4, v1, v2, v3, v4]
    simp only
    linear_combination (norm := (field_simp; ring)) ED x - aE p / (p.θ - 1) * E7 x
  have c5 : ∀ x, Rr x 5 = r x 5 := fun x => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm x 1, hm x 2, hvx x 0, hvx x 2, v0, v1, v2]
    linear_combination EF x
  have c4 : ∀ x, Rr x 4 = r x 4 := fun x => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm x 1, hm x 8, hvx x 0, hvx x 8, v0, v1, v8]
    linear_combination E4 x
  have c0 : ∀ x, Rr x 0 = r x 0 := fun x => by
    change (DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x)) 0 = r x 0
    rw [← red_l1X R hp γ, hvx x 0, hvx x 4, hvx x 5, hvx x 6, v0, v4, v5, v6]
    simp only
    linear_combination E0 x
  have c2 : ∀ x, Rr x 2 = r x 2 := fun x => by
    simp only [hRr, DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl x 5, hvx x 1, hvx x 2, hvx x 3, hvx x 5, hvx x 7, hvx x 8, v1, v2, v3, v5, v7, v8]
    simp only [l3vZ]
    field_simp
    ring
  have c3 : ∀ x, Rr x 3 = r x 3 := fun x => by
    have h := red_muX R hp γ (lagv T v x) (v x) (Mv T.M v x)
    rw [hl x 5, hl x 6, hvx x 5, hvx x 6, v5, v6, lag0_lin] at h
    simp only at h
    have h2 := c2 x
    have h7 := c7 x
    simp only [hRr] at h2 h7 ⊢
    rw [h2, h7] at h
    linear_combination (-1 : ℝ) * h + EM x
  have c6 : ∀ x, Rr x 6 = r x 6 := fun x => by
    have h := red_pcX R hp γ (lagv T v x) (v x) (Mv T.M v x)
    have h5 := c5 x
    have h7 := c7 x
    simp only [hRr] at h5 h7 ⊢
    rw [h5, h7, hm x 1, hm x 2, hm x 3, hvx x 0, hvx x 1, v0, v1, v2, v3, M_lin] at h
    have hm7 : p.α * (p.θ - 1) * T.M π x - (1 - p.α) * (p.θ - 1) *
        ((1 * T.M (FvZ T p R γ r) x + p.c0 * T.M (xvZ T p R γ r) x -
          T.M (FvZ T p R γ r) x) / p.c0) =
          T.M (fun z => r z 7) x := by
      have e : (fun z => r z 7) = fun z => (p.α * (p.θ - 1)) * π z +
          (-(1 - p.α) * (p.θ - 1)) * xvZ T p R γ r z := by
        funext z; rw [← E7 z]; ring
      rw [e, M_lin]; field_simp; ring
    rw [hm7] at h
    have hg := Epc x
    simp only [gv] at hg
    have hk : (1 - p.α) / (p.c0 * p.α) ≠ 0 := div_ne_zero h1α (mul_ne_zero hc0 hα)
    have key : (1 - p.α) / (p.c0 * p.α) * (Rr x 6 - r x 6) = 0 := by
      simp only [hRr]
      linear_combination hg - h
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  have c1 : ∀ x, Rr x 1 = r x 1 := fun x => by
    have h0m : -((R.Au * Gw p R - γ) * lagv T v x 0) - (1 - R.Φ) * R.Au * lagv T v x 4 +
        (1 - p.α * p.β) * (p.σ + p.ω) * lagv T v x 5 -
          (1 - p.α * p.β) * (1 + p.ω) * (lagv T v x 5 + lagv T v x 6) =
            lag0 T (fun z => r z 0) x := by
      simp only [lagv, lag0]
      split_ifs
      · ring
      · have := c0 (T.par x)
        change (DQrX p R γ (lagv T v (T.par x)) (v (T.par x)) +
          DNr p R (Mv T.M v (T.par x))) 0 = r (T.par x) 0 at this
        rw [← red_l1X R hp γ] at this
        exact this
    have h := red_targetX R hp γ (lagv T v x) (v x) (Mv T.M v x) _ h0m
    have h2 := c2 x
    have h7 := c7 x
    have h0 := c0 x
    simp only [hRr] at h2 h7 h0 ⊢
    rw [h2, h7, h0, hl x 0, hl x 4, hl x 5, hl x 6, hvx x 0, hvx x 1, hvx x 4, hvx x 5,
      hvx x 6, v0, v1, v4, v5, v6, lag0_lin] at h
    simp only at h
    have hF := Et x
    simp only [Ftv] at hF
    have hk : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hab hωσ) (div_ne_zero h1α (mul_ne_zero hα hc0))
    have key : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) *
        (Rr x 1 - r x 1) = 0 := by
      simp only [hRr]
      linear_combination h - hF - (y x - lag0 T y x) * hH0
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  funext x i
  fin_cases i
  exacts [c0 x, c1 x, c2 x, c3 x, c4 x, c5 x, c6 x, c7 x, c8 x]


/-- Woodford (2003), Ch. 7 and App. A.3 (**injectivity: the a-priori bound with predetermined
variables**): on every event tree, a bounded solution of the homogeneous linearised Ramsey
system with zero initial lag is zero. -/
theorem LRX_injZ {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0)
    (v : X → Fin 9 → ℝ) (B : ℝ) (hB : ∀ x k, |v x k| ≤ B) (h0 : LRX T p R γ v = 0) : v = 0 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hκ := hp.κ_pos.ne'
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  have hR : ∀ x, DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x) = 0 := fun x =>
    congrFun h0 x
  have hRk : ∀ x k, (DQrX p R γ (lagv T v x) (v x) + DNr p R (Mv T.M v x)) k = 0 := fun x k => by
    rw [hR x]; rfl
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  -- the predetermined block
  have hD : ∀ x, v x 4 = 0 := zero_of_eq_lag T (c := p.α) fun x => by
    have := red_DX R hp γ (lagv T v x) (v x) (Mv T.M v x)
    rw [hRk, hRk, hl] at this; simpa using this
  have hμ : ∀ x, v x 5 + v x 6 = 0 := zero_of_eq_lag T (c := p.α) (g := fun z => v z 5 + v z 6)
    fun x => by
      have := red_muX R hp γ (lagv T v x) (v x) (Mv T.M v x)
      rw [hRk, hRk, hRk, hl, hl] at this
      have e := lag0_lin T 1 1 (fun z => v z 5) (fun z => v z 6) x
      simp only [one_mul] at e
      simp only [e]; linarith
  have hDf : (fun z => v z 4) = fun _ => 0 := funext hD
  have hμf : (fun z => v z 5 + v z 6) = fun _ => 0 := funext hμ
  -- the expected price-index residual vanishes
  have h7f : (fun z => p.α * (p.θ - 1) * v z 1 - (1 - p.α) * (p.θ - 1) * ((v z 3 - v z 2) /
      p.c0)) = fun _ => 0 := by
    funext z
    rw [← red_xX R γ (lagv T v z) (v z) (Mv T.M v z)]
    exact hRk z 7
  have hm7 : ∀ x, p.α * (p.θ - 1) * Mv T.M v x 1 - (1 - p.α) * (p.θ - 1) *
      ((Mv T.M v x 3 - Mv T.M v x 2) / p.c0) = 0 := fun x => by
    have e : (fun z => p.α * (p.θ - 1) * v z 1 - (1 - p.α) * (p.θ - 1) * ((v z 3 - v z 2) /
        p.c0)) = fun z => (p.α * (p.θ - 1)) * v z 1 + (-(1 - p.α) * (p.θ - 1) / p.c0) *
          (1 * v z 3 + -1 * v z 2) := by funext z; field_simp; ring
    have := congrFun (congrArg T.M h7f) x
    rw [e, M_lin, M_lin, M_const] at this
    rw [hm, hm, hm]
    simp only at this
    linear_combination (norm := (field_simp; ring)) this
  -- the output condition at the parent
  have h0m : ∀ x, -((R.Au * Gw p R - γ) * lagv T v x 0) - (1 - R.Φ) * R.Au * lagv T v x 4 +
      (1 - p.α * p.β) * (p.σ + p.ω) * lagv T v x 5 -
        (1 - p.α * p.β) * (1 + p.ω) * (lagv T v x 5 + lagv T v x 6) = 0 := fun x => by
    simp only [lagv, lag0]
    split_ifs
    · ring
    · have := red_l1X R hp γ (lagv T v (T.par x)) (v (T.par x)) (Mv T.M v (T.par x))
      rw [hRk] at this; exact this
  have hcs := fun x => commitment_systemX R hp γ (lagv T v x) (v x) (Mv T.M v x) (hR x) (h0m x)
    (hm7 x)
  -- the commitment block
  set y : X → ℝ := fun z => v z 0 with hy
  set π : X → ℝ := fun z => v z 1 with hπ
  have hπ0 : ∀ x, v x 1 = 0 := fun x => by
    obtain ⟨-, -, -, h4⟩ := hcs x
    rw [hl, hl, hl, hl, hDf, lag0_zero] at h4
    have e := lag0_lin T 1 1 (fun z => v z 5) (fun z => v z 6) x
    simp only [one_mul] at e
    rw [← e, hμf, lag0_zero] at h4
    simp only [mul_zero, add_zero, sub_zero] at h4
    have h5 : R.Au * Gw p R * p.θ * π x = 0 := by
      linear_combination h4 - (y x - lag0 T y x) * hH0
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd h (mul_ne_zero hAG hθ0)
    · exact h
  have hπf0' : π = fun _ => 0 := funext hπ0
  have hy0 : ∀ x, v x 0 = 0 := fun x => by
    obtain ⟨-, -, h3, -⟩ := hcs x
    rw [hm] at h3
    have hM0 : T.M (fun z => v z 1) x = 0 := by
      rw [show (fun z => v z 1) = π from rfl, hπf0', M_const]
    rw [hM0, hπ0 x] at h3
    have : p.κ * v x 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hκ
    · exact h
  have hπf0 : (fun z => v z 1) = fun _ => 0 := funext hπ0
  have hF0 : ∀ x, v x 2 = 0 := by
    refine zero_of_eq_cM T (abs_ab hp) (A := B) (g := fun z => v z 2) (fun x => hB x 2)
      fun x => ?_
    have := hRk x 5
    simp only [DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val, hm, hπf0, M_const, hy0] at this
    linear_combination this
  have hK0 : ∀ x, v x 3 = 0 := fun x => by
    have := hRk x 7
    rw [red_xX, hπ0, hF0] at this
    have h2 : (1 - p.α) * (p.θ - 1) / p.c0 * v x 3 = 0 := by linear_combination -this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (div_ne_zero (mul_ne_zero h1α hθ) hc0)
    · exact h
  have hl10 : ∀ x, v x 5 = 0 := fun x => by
    have := red_l1X R hp γ (lagv T v x) (v x) (Mv T.M v x)
    rw [hRk, hy0, hD, hμ] at this
    have h2 : (1 - p.α * p.β) * (p.σ + p.ω) * v x 5 = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_ne_zero hab hωσ)
    · exact h
  have hl20 : ∀ x, v x 6 = 0 := fun x => by linarith [hμ x, hl10 x]
  have hl40 : ∀ x, v x 8 = 0 := by
    refine zero_of_eq_cM T (abs_ab hp) (A := B) (g := fun z => v z 8) (fun x => hB x 8)
      fun x => ?_
    have := hRk x 4
    simp only [DQrX, DQr, DNr, Pi.add_apply, Matrix.cons_val, hm, hπf0, M_const, hy0] at this
    linear_combination this
  have hl30 : ∀ x, v x 7 = 0 := fun x => by
    have := hRk x 2
    simp only [DQrX, DQr, Pi.add_apply, Matrix.cons_val, hl, lag0_zero, hπ0, hF0, hK0, hl10,
      hl40, DNr] at this
    have h2 : (1 - p.α) * ((p.θ - 1) / p.c0) * v x 7 = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_ne_zero h1α (div_ne_zero hθ hc0))
    · exact h
  funext x k
  fin_cases k
  exacts [hy0 x, hπ0 x, hF0 x, hK0 x, hD x, hl10 x, hl20 x, hl30 x, hl40 x]

/-- Woodford (2003), App. A.3 (**the uniform bound on the inverse**): `‖L⁻¹r‖ ≤ K‖r‖` with `K`
depending only on the parameters, for every event tree. -/
theorem LinvRZ_bound {p : Par} (R : RPar) (hp : p.Std) (γ : ℝ)
    (hH0 : R.Au * Gw p R - γ = 0) (hAG : R.Au * Gw p R ≠ 0) : ∃ K, 0 ≤ K ∧ ∀ {Y : Type*}
    (T : LagTree Y) (r : Y → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → (∀ y, ‖r y‖ ≤ A) →
      ∀ y, ‖LinvRZ T p R γ r y‖ ≤ K * A := by
  obtain ⟨c0, h0, b0⟩ := bd_yvZ R hp γ hH0 hAG
  obtain ⟨c1, h1, b1⟩ := bd_pivZ R hp γ hH0 hAG
  obtain ⟨c2, h2, b2⟩ := bd_FvZ R hp γ hH0 hAG
  obtain ⟨cx, hx, bx⟩ := bd_xvZ R hp γ hH0 hAG
  obtain ⟨c4, h4, b4⟩ := bd_Dv hp
  obtain ⟨c5, h5, b5⟩ := bd_l1vZ R hp γ hH0 hAG
  obtain ⟨cμ, hμ, bμ⟩ := bd_Muv R hp
  obtain ⟨c7, h7, b7⟩ := bd_l3vZ R hp γ hH0 hAG
  obtain ⟨c8, h8, b8⟩ := bd_l4vZ R hp γ hH0 hAG
  set K := c0 + c1 + c2 + (c2 + |p.c0| * cx) + c4 + c5 + (cμ + c5) + c7 + c8 with hK
  refine ⟨K, by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ y k, |r y k| ≤ A := fun y k => by
    have := (norm_le_pi_norm (r y) k).trans (hr y); rwa [Real.norm_eq_abs] at this
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hc : ∀ c, 0 ≤ c → c * A ≤ K * A → ∀ t : ℝ, |t| ≤ c * A → |t| ≤ K * A :=
    fun c _ hcK t ht => ht.trans hcK
  have hKA : ∀ c, c ≤ K → c * A ≤ K * A := fun c hcK => mul_le_mul_of_nonneg_right hcK hA
  fin_cases i <;> simp only [LinvRZ, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
    Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact (b0 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact (b1 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact ((b2 T r A hA hr').1 y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · have e := lb2 (b2 T r A hA hr').1 (bx T r A hA hr') 1 p.c0 y
    simp only [one_mul, abs_one] at e
    exact e.trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact (b4 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact (b5 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · have e := lb2 (bμ T r A hA hr') (b5 T r A hA hr') 1 (-1) y
    simp only [one_mul, abs_one, abs_neg, neg_one_mul, ← sub_eq_add_neg] at e
    exact e.trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact (b7 T r A hA hr' y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))
  · exact ((b8 T r A hA hr').1 y).trans (hKA _ (by rw [hK]; nlinarith [abs_nonneg p.c0]))


/-! ## Existence and uniqueness when `H = 0` -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**the three properties of the inverse when `H = 0`**). -/
theorem invBound_zero {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hH0 : Hy p R sC = 0) (hAG : R.Au * Gw p R ≠ 0) :
    InvBound (QdG p R sC) (Nd p R)
      (fun {Y : Type u} (T : LagTree Y) r => LinvRZ T p R (gamG p R sC) r) := by
  have hH0' : R.Au * Gw p R - gamG p R sC = 0 := hH0
  obtain ⟨K, hK0, hK⟩ := LinvRZ_bound R hp (gamG p R sC) hH0' hAG
  refine ⟨⟨K, hK0, fun T r A hA hr y => hK T r A hA hr y⟩, fun T r A hA hr => ?_,
    fun T v B hB h0 => ?_⟩
  · funext x
    rw [TidyR6bGovRamseyIFT.LG_QdG R hp hs]
    exact congrFun (LRX_LinvRZ T R hp (gamG p R sC) hH0' hAG r A hA hr) x
  · refine LRX_injZ T R hp (gamG p R sC) hH0' hAG v B hB ?_
    funext x
    rw [← TidyR6bGovRamseyIFT.LG_QdG R hp hs]
    exact congrFun h0 x

/-- **Woodford (2003), Ch. 6, §5 and Ch. 7, §1–2 (EXISTENCE AND UNIQUENESS with purchases when
the output weight vanishes, on every event tree).** If `s_C > 0`, `H = A_uG − γ_G = 0` and
`A_uG ≠ 0`, there are `r, δ > 0` such that on every event tree, for all disturbances and initial
lags with `‖e‖, ‖d‖ ≤ δ`, the TRUE Ramsey conditions with purchases have a solution within `r`,
and it is the only one within `r`. -/
theorem gov_ramsey_existence_zero {p : Par} (R : RPar) (hp : p.Std) {sC : ℝ} (hs : 0 < sC)
    (hH0 : Hy p R sC = 0) (hAG : R.Au * Gw p R ≠ 0) :
    ∃ r > 0, ∃ δ > 0, ∀ {Y : Type u} (T : LagTree Y) (e : Y → Fin 6 → ℝ) (d : Y → Fin 9 → ℝ),
      (∀ y, ‖e y‖ ≤ δ) → (∀ y, ‖d y‖ ≤ δ) →
        ∃ z : Y → Fin 9 → ℝ, ((∀ y, ‖z y‖ ≤ r) ∧ TidyR6bGovRamseyIFT.PhiTrue T p R sC e d z = 0) ∧
          ∀ z' : Y → Fin 9 → ℝ, (∀ y, ‖z' y‖ ≤ r) →
            TidyR6bGovRamseyIFT.PhiTrue T p R sC e d z' = 0 → z' = z := by
  have hQ : ContDiff ℝ 1 (QdG p R sC) := contDiff_QdG p R sC
  obtain ⟨r0, hr0, δ0, hδ0, C, hC, hN⟩ := newton_tree.{u} hQ (contDiff_Nd p R)
    (QdG_Nd_zero R hp hs) (invBound_zero R hp hs hH0 hAG)
  set τ0 := sC / 4 / C with hτ0
  have hτ0p : 0 < τ0 := by positivity
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1 (hQ.continuous.continuousAt (x := 0))
    τ0 hτ0p
  set r := min r0 (sC / 4) with hr
  have hrp : 0 < r := lt_min hr0 (by positivity)
  refine ⟨r, hrp, min δ0 (min (δQ / 2) (sC / 4)), lt_min hδ0 (lt_min (by positivity)
    (by positivity)), fun {Y} T e d he hd => ?_⟩
  have he0 : ∀ y, ‖e y‖ ≤ δ0 := fun y => (he y).trans (min_le_left _ _)
  have hd0 : ∀ y, ‖d y‖ ≤ δ0 := fun y => (hd y).trans (min_le_left _ _)
  have heS : ∀ y, ‖e y‖ ≤ sC / 4 :=
    fun y => (he y).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨z, ⟨hzB, hz0⟩, huniq, hsmall, -⟩ := hN T e d he0 hd0
  have hb : ∀ y, ‖PhiG T (QdG p R sC) (Nd p R) e d (fun _ => 0) y‖ ≤ τ0 := fun y => by
    have e1 : PhiG T (QdG p R sC) (Nd p R) e d (fun _ => 0) y =
        QdG p R sC (e y, lagI T (fun _ => 0) d y, 0) - QdG p R sC 0 := by
      simp only [PhiG, Mv_const T.markov]
      rw [eq_neg_of_add_eq_zero_right (QdG_Nd_zero R hp hs)]
      abel
    rw [e1, ← dist_eq_norm]
    refine (hQc ?_).le
    rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
    have hl : ‖lagI T (fun _ => (0 : Fin 9 → ℝ)) d y‖ ≤ δQ / 2 := by
      unfold lagI; split_ifs
      · exact (hd y).trans ((min_le_right _ _).trans (min_le_left _ _))
      · rw [norm_zero]; positivity
    have h0' : ‖(0 : Fin 9 → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
    exact lt_of_le_of_lt (max_le ((he y).trans ((min_le_right _ _).trans (min_le_left _ _)))
      (max_le hl h0')) (by linarith)
  have hzS : ∀ y, ‖z y‖ ≤ sC / 4 := fun y => by
    have := hsmall τ0 hτ0p.le hb y
    rwa [hτ0, mul_div_cancel₀ _ hC.ne'] at this
  refine ⟨z, ⟨fun y => le_min (hzB y) (hzS y), ?_⟩, fun z' hz'B hz' => ?_⟩
  · rw [TidyR6bGovRamseyIFT.PhiTrue_eq T R hs heS hzS]; exact hz0
  · have hz'S : ∀ y, ‖z' y‖ ≤ sC / 4 := fun y => (hz'B y).trans (min_le_right _ _)
    refine huniq z' (fun y => (hz'B y).trans (min_le_left _ _)) ?_
    rw [← TidyR6bGovRamseyIFT.PhiTrue_eq T R hs heS hz'S]; exact hz'

end Woodford.StabilizationWelfare.TidyR6bGovRamseyZero
