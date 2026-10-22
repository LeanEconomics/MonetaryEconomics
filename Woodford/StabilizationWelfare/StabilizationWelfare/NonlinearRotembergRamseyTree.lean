/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyLin
import StabilizationWelfare.NonlinearNKMarkovRamseyTree

/-!
# The linearised Rotemberg Ramsey operator on an event tree: inverse and a-priori bound

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (the timeless commitment equilibrium with
the predetermined multiplier `λ_{t−1}`) and Appendix A.3, for the Rotemberg Ramsey conditions of
`NonlinearRotembergRamseyLin`. The event trees (`NonlinearNKMarkovRamseyTree.LagTree`), the lag,
the backward and forward scalar solutions are reused from the Calvo modules.

* `LR`: the linearised operator `v ↦ DQr(lag v, v) + DNr(Mv)` with zero initial lag.
* `LinvR`: its inverse. The multiplier `λ̂` solves `βMλ − (1 + β + κθ_R)λ + lag λ = −h` through
  the factorisation `(βM − βz₂)(1 − z₁ lag)` with `0 < z₁ < 1 < z₂` (`zR_props`); consumption
  from the combined conditions, output from the resource constraint, inflation from the
  inflation condition, `γ̂` from the consumption condition.
* **`LR_LinvR`**, **`LR_inj`**, **`LinvR_LR`**, **`LinvR_sub`**, **`LinvR_bound`**: the inverse
  with a bound `K` depending only on the parameters, uniformly over event trees.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyTree

open Filter Topology
open NonlinearNKMarkov (Mv IsMarkov mnorm Mv_norm_le)
open NonlinearNKMarkovRamseyTree (LagTree lag0 M_lag0 lag0_lin abs_lag0_le bwd bwd_eq abs_bwd_le
  zero_of_eq_lag M_lin M_const zero_of_eq_cM fwdS Sg Sg_nonneg fwdS_spec lagv lb2 lbM lbLag
  norm_lagv_le lag0_zero)
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin

variable {p : Par}

/-! ## The roots -/

/-- The coefficient `c = κθ_R` of the commitment polynomial. -/
noncomputable def cR (p : Par) : ℝ := p.κ * thR p

/-- Woodford (2003), Ch. 7: the stable root `z₁` of `βz² − (1+β+κθ_R)z + 1`. -/
noncomputable def z1R (p : Par) : ℝ :=
  ((1 + p.β + cR p) - Real.sqrt ((1 + p.β + cR p) ^ 2 - 4 * p.β)) / (2 * p.β)

/-- Woodford (2003), Ch. 7: the unstable root `z₂`. -/
noncomputable def z2R (p : Par) : ℝ :=
  ((1 + p.β + cR p) + Real.sqrt ((1 + p.β + cR p) ^ 2 - 4 * p.β)) / (2 * p.β)

/-- `c = κθ_R > 0` when `G > 0`. -/
theorem cR_pos (hp : p.Basic) (hG : 0 < Gw p) : 0 < cR p := by
  have hθ : 0 < p.θ := by linarith [hp.one_lt_θ]
  have : 0 < thR p := by
    unfold thR; have := hp.m_pos; have := hp.σ_pos; have := hp.ω_nonneg; positivity
  exact mul_pos hp.κ_pos this

/-- Woodford (2003), Ch. 7 (**the root condition**): `0 < z₁ < 1 < z₂`, `βz₁z₂ = 1`,
`β(z₁ + z₂) = 1 + β + κθ_R`. -/
theorem zR_props (hp : p.Basic) (hG : 0 < Gw p) :
    0 < z1R p ∧ z1R p < 1 ∧ 1 < z2R p ∧ p.β * z1R p * z2R p = 1 ∧
      p.β * (z1R p + z2R p) = 1 + p.β + cR p := by
  have hβ0 := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hc := cR_pos hp hG
  unfold z1R z2R
  set c := cR p
  set A := 1 + p.β + c with hA
  set D := A ^ 2 - 4 * p.β with hD
  have hDpos : (1 - p.β + c) ^ 2 < D := by rw [hD, hA]; nlinarith
  have hD0 : 0 < D := lt_of_le_of_lt (sq_nonneg _) hDpos
  set q := Real.sqrt D with hq
  have hqq : q * q = D := Real.mul_self_sqrt hD0.le
  have hq1 : 1 - p.β + c < q := by rw [hq]; exact Real.lt_sqrt_of_sq_lt hDpos
  have hqA : q < A := by
    rw [hq, Real.sqrt_lt' (by linarith)]; rw [hD]; nlinarith
  refine ⟨by apply div_pos <;> linarith, by rw [div_lt_one (by linarith)]; linarith,
    by rw [one_lt_div (by linarith)]; linarith, by field_simp; nlinarith, by field_simp; ring⟩

/-- `|1/z₂| < 1`. -/
theorem abs_inv_z2R (hp : p.Basic) (hG : 0 < Gw p) : |1 / z2R p| < 1 := by
  obtain ⟨-, -, h, -⟩ := zR_props hp hG
  rw [abs_of_pos (by positivity), div_lt_one (by linarith)]; exact h

/-! ## The operator and its inverse -/

variable {X : Type*} (T : LagTree X)

/-- Woodford (2003), Ch. 7 and App. A.3 (**the linearised Rotemberg Ramsey operator with a
lag**): `(Lv)(x) = DQr(v(par x), v(x)) + DNr((Mv)(x))`, zero lag at the roots. -/
noncomputable def LR (p : Par) (v : X → Fin 5 → ℝ) (x : X) : Fin 5 → ℝ :=
  DQr p (lagv T v x) (v x) + DNr p (Mv T.M v x)

/-- `aR = θm(σ+ω)/G`: consumption falls by `aR` per unit of the multiplier. -/
noncomputable def aR (p : Par) : ℝ := p.θ * p.m * (p.σ + p.ω) / Gw p

/-- The coefficient of `ŷ − ĉ` in the combined conditions (`red_lam`). -/
noncomputable def cR4 (p : Par) : ℝ :=
  -(p.m * (1 + p.ω)) - lamb p * (p.θ * p.m * (p.ω ^ 2 + 2 * p.ω + p.σ)) + gamb p

/-- The inverse, the forcing of consumption: `ĉ = −aR λ̂ + s`. -/
noncomputable def sv (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (cR4 p * r x 4 - r x 0 - r x 2) / Gw p

/-- The inverse, the forcing of `(1+β+c)λ − lag λ − βMλ = h`. -/
noncomputable def hv (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  gamb p / p.ψ * (r x 3 + p.θ * p.m * p.ω * r x 4 + p.θ * p.m * (p.σ + p.ω) * sv p r x) +
    (r x 1 - p.β * T.M (fun y => r y 1) x) / p.ψ

/-- The inverse, the forward factor `U = λ − z₁ lag λ`. -/
noncomputable def uv (p : Par) (r : X → Fin 5 → ℝ) : X → ℝ :=
  fwdS T (1 / z2R p) (fun x => hv T p r x / (p.β * z2R p))

/-- The inverse, the multiplier `λ̂ = z₁ lag λ̂ + U`. -/
noncomputable def lv (p : Par) (r : X → Fin 5 → ℝ) : X → ℝ := bwd T (z1R p) (uv T p r)

/-- The inverse, consumption. -/
noncomputable def cv (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ := -(aR p * lv T p r x) + sv p r x

/-- The inverse, output from the resource constraint. -/
noncomputable def yv (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ := cv T p r x + r x 4

/-- The inverse, inflation from the inflation condition. -/
noncomputable def piv (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (lv T p r x - lag0 T (lv T p r) x) / gamb p - r x 1 / (gamb p * p.ψ)

/-- The inverse, the resource multiplier from the consumption condition. -/
noncomputable def gv (p : Par) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (1 - p.σ) * cv T p r x - lv T p r x * (p.θ * p.m * p.σ) -
    lamb p * (p.θ * p.m * p.σ * (yv T p r x - p.σ * cv T p r x)) - gamb p * cv T p r x - r x 2

/-- Woodford (2003), Ch. 7 and App. A.3 (**the inverse of the linearised Rotemberg Ramsey
operator**). -/
noncomputable def LinvR (p : Par) (r : X → Fin 5 → ℝ) (x : X) : Fin 5 → ℝ :=
  ![yv T p r x, piv T p r x, cv T p r x, lv T p r x, gv T p r x]

/-! ## Uniform bounds -/

/-- Woodford (2003), App. A.3: the consumption forcing is bounded, uniformly over event trees. -/
theorem bd_sv (hG : 0 < Gw p) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*}
    (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) → ∀ y, |sv p r y| ≤ c * A := by
  refine ⟨(|cR4 p| + 2) / Gw p, by positivity, fun r A hA hr y => ?_⟩
  unfold sv
  rw [abs_div, abs_of_pos hG, div_le_iff₀ hG]
  have h1 : |cR4 p * r y 4| ≤ |cR4 p| * A := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr y 4) (abs_nonneg _)
  calc |cR4 p * r y 4 - r y 0 - r y 2| ≤ |cR4 p * r y 4| + |r y 0| + |r y 2| := by
        refine (abs_sub _ _).trans ?_
        exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ |cR4 p| * A + A + A := by linarith [hr y 0, hr y 2]
    _ = (|cR4 p| + 2) / Gw p * A * Gw p := by field_simp; ring

/-- Woodford (2003), App. A.3: the forcing of the multiplier equation is bounded. -/
theorem bd_hv (hp : p.Basic) (hG : 0 < Gw p) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) → ∀ y, |hv T p r y| ≤ c * A := by
  obtain ⟨cs, hcs, hs⟩ := bd_sv hG
  have hψ := hp.ψ_pos
  set k1 := gamb p / p.ψ
  set k3 := p.θ * p.m * p.ω
  set k4 := p.θ * p.m * (p.σ + p.ω)
  refine ⟨|k1| * (|1| * (|1| * 1 + |k3| * 1) + |k4| * cs) + |1 / p.ψ| * (|1| * 1 + |-p.β| * 1),
    by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ k y, |r y k| ≤ 1 * A := fun k y => by simpa using hr y k
  have e1 := lb2 (f := fun y => 1 * r y 3 + k3 * r y 4) (g := sv p r) (cf := |1| * 1 + |k3| * 1)
    (lb2 (hr' 3) (hr' 4) 1 k3) (hs r A hA hr) 1 k4
  have e2 := lb2 (f := fun y => r y 1) (g := T.M fun y => r y 1) (hr' 1)
    (lbM T (hr' 1)) 1 (-p.β)
  have := lb2 e1 e2 k1 (1 / p.ψ) y
  convert this using 2
  simp only [hv, k1, k3, k4]; field_simp; ring

/-- Woodford (2003), App. A.3: the multiplier part of the inverse is bounded. -/
theorem bd_lv (hp : p.Basic) (hG : 0 < Gw p) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) →
      (∀ y, |uv T p r y| ≤ c * A) ∧ ∀ y, |lv T p r y| ≤ c / (1 - z1R p) * A := by
  obtain ⟨ch, hch, hh⟩ := bd_hv hp hG
  obtain ⟨hz10, hz11, hz21, -, -⟩ := zR_props hp hG
  have hβ := hp.β_pos
  have hz2 : 0 < p.β * z2R p := mul_pos hβ (by linarith)
  set k := 1 / (p.β * z2R p)
  have hk : 0 ≤ k := by positivity
  refine ⟨Sg (1 / z2R p) * (k * ch), mul_nonneg (Sg_nonneg _) (by positivity),
    fun T r A hA hr => ?_⟩
  have hf : ∀ y, |hv T p r y / (p.β * z2R p)| ≤ k * ch * A := fun y => by
    rw [abs_div, abs_of_pos hz2, div_le_iff₀ hz2]
    calc |hv T p r y| ≤ ch * A := hh T r A hA hr y
      _ = k * ch * A * (p.β * z2R p) := by simp only [k]; field_simp
  obtain ⟨hU, -⟩ := fwdS_spec T (abs_inv_z2R hp hG) (by positivity) hf
  have hU' : ∀ y, |uv T p r y| ≤ Sg (1 / z2R p) * (k * ch) * A := fun y => by
    have := hU y; rw [← mul_assoc] at this; exact this
  refine ⟨hU', fun y => ?_⟩
  have := abs_bwd_le T hz10.le hz11 (mul_nonneg (mul_nonneg (Sg_nonneg _) (by positivity)) hA)
    hU' y
  calc |lv T p r y| ≤ _ := this
    _ = _ := by ring

/-- Woodford (2003), App. A.3: all components of the inverse are bounded, uniformly over event
trees. -/
theorem bd_all (hp : p.Basic) (hG : 0 < Gw p) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) → ∀ y,
      |lv T p r y| ≤ c * A ∧ |cv T p r y| ≤ c * A ∧ |yv T p r y| ≤ c * A ∧
        |piv T p r y| ≤ c * A ∧ |gv T p r y| ≤ c * A := by
  obtain ⟨cl0, hcl0, hl⟩ := bd_lv hp hG
  obtain ⟨cs, hcs, hs⟩ := bd_sv hG
  obtain ⟨hz10, hz11, -, -, -⟩ := zR_props hp hG
  set cl := cl0 / (1 - z1R p)
  have hcl : 0 ≤ cl := div_nonneg hcl0 (by linarith)
  have hψ := hp.ψ_pos
  have hgb : 0 < gamb p := by
    unfold gamb
    have := hp.m_pos; have := hp.σ_pos; have := hp.ω_nonneg
    have : 0 < p.σ + p.ω := by linarith
    positivity
  set cc := |-aR p| * cl + |1| * cs
  set cy := |1| * cc + |1| * 1
  set cp := |1 / gamb p| * (|1| * cl + |-1| * cl) + |-(1 / (gamb p * p.ψ))| * 1
  set k1 := 1 - p.σ - gamb p + lamb p * (p.θ * p.m * p.σ) * p.σ
  set k2 := -(p.θ * p.m * p.σ)
  set k3 := -(lamb p * (p.θ * p.m * p.σ))
  set cg := |1| * (|k1| * cc + |k2| * cl) + |1| * (|k3| * cy + |-1| * 1)
  refine ⟨cl + cc + cy + cp + cg, by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ k y, |r y k| ≤ 1 * A := fun k y => by simpa using hr y k
  have hL := (hl T r A hA hr).2
  have hC : ∀ y, |cv T p r y| ≤ cc * A := fun y => by
    have := lb2 hL (hs r A hA hr) (-aR p) 1 y
    convert this using 2; simp only [cv]; ring
  have hY : ∀ y, |yv T p r y| ≤ cy * A := fun y => by
    have := lb2 hC (hr' 4) 1 1 y
    convert this using 2; simp only [yv]; ring
  have hP : ∀ y, |piv T p r y| ≤ cp * A := fun y => by
    have := lb2 (lb2 hL (lbLag T (by positivity) hL) 1 (-1)) (hr' 1) (1 / gamb p)
      (-(1 / (gamb p * p.ψ))) y
    convert this using 2; simp only [piv]; field_simp; ring
  have hGv : ∀ y, |gv T p r y| ≤ cg * A := fun y => by
    have := lb2 (lb2 hC hL k1 k2) (lb2 hY (hr' 2) k3 (-1)) 1 1 y
    convert this using 2; simp only [gv, k1, k2, k3]; ring
  have hA' : ∀ c, c ≤ cl + cc + cy + cp + cg → c * A ≤ (cl + cc + cy + cp + cg) * A :=
    fun c hc => mul_le_mul_of_nonneg_right hc hA
  have hcc : 0 ≤ cc := by positivity
  have hcy : 0 ≤ cy := by positivity
  have hcp : 0 ≤ cp := by positivity
  have hcg : 0 ≤ cg := by positivity
  exact ⟨(hL y).trans (hA' _ (by linarith)), (hC y).trans (hA' _ (by linarith)),
    (hY y).trans (hA' _ (by linarith)), (hP y).trans (hA' _ (by linarith)),
    (hGv y).trans (hA' _ (by linarith))⟩

/-! ## The inverse is a right inverse -/

/-- `G aR = θm(σ+ω)`. -/
theorem Gw_aR (hG : 0 < Gw p) : Gw p * aR p = p.θ * p.m * (p.σ + p.ω) := by
  unfold aR; field_simp

/-- `γ̄ θm(σ+ω) aR / ψ = κθ_R`. -/
theorem gamb_aR (hp : p.Basic) (hG : 0 < Gw p) :
    gamb p * (p.θ * p.m * (p.σ + p.ω)) * aR p / p.ψ = cR p := by
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hψ := hp.ψ_pos.ne'
  unfold cR thR aR gamb Par.κ
  field_simp

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r`**): for every bounded forcing on every
event tree, the constructed process solves the linearised Rotemberg Ramsey system. -/
theorem LR_LinvR (hp : p.Basic) (hG : 0 < Gw p) (r : X → Fin 5 → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hr : ∀ y k, |r y k| ≤ A) : LR T p (LinvR T p r) = r := by
  obtain ⟨ch, hch, hh⟩ := bd_hv hp hG
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := zR_props hp hG
  have hβ := hp.β_pos
  have hz2 : 0 < p.β * z2R p := mul_pos hβ (by linarith)
  have hψ := hp.ψ_pos
  have hgb : 0 < gamb p := by
    unfold gamb
    have := hp.m_pos; have := hp.σ_pos; have := hp.ω_nonneg
    have : 0 < p.σ + p.ω := by linarith
    positivity
  have hf : ∀ y, |hv T p r y / (p.β * z2R p)| ≤ (1 / (p.β * z2R p) * ch) * A := fun y => by
    rw [abs_div, abs_of_pos hz2, div_le_iff₀ hz2]
    calc |hv T p r y| ≤ ch * A := hh T r A hA hr y
      _ = 1 / (p.β * z2R p) * ch * A * (p.β * z2R p) := by field_simp
  obtain ⟨-, EU⟩ := fwdS_spec T (abs_inv_z2R hp hG) (by positivity) hf
  have EU' : ∀ x, uv T p r x = 1 / z2R p * T.M (uv T p r) x + hv T p r x / (p.β * z2R p) := EU
  have EL : ∀ x, lv T p r x = z1R p * lag0 T (lv T p r) x + uv T p r x := fun x => bwd_eq T _ _ x
  have EMU : ∀ x, T.M (uv T p r) x = T.M (lv T p r) x - z1R p * lv T p r x := fun x => by
    have e : uv T p r = fun x => 1 * lv T p r x + -z1R p * lag0 T (lv T p r) x := by
      funext x; rw [EL x]; ring
    rw [e, M_lin, M_lag0]; ring
  -- the multiplier equation
  have key : ∀ x, (1 + p.β + cR p) * lv T p r x - lag0 T (lv T p r) x -
      p.β * T.M (lv T p r) x = hv T p r x := fun x => by
    have h1 := EU' x
    rw [EMU x] at h1
    have hux : uv T p r x = lv T p r x - z1R p * lag0 T (lv T p r) x := by rw [EL x]; ring
    rw [hux] at h1
    have h2 : p.β * z2R p * (lv T p r x - z1R p * lag0 T (lv T p r) x) =
        p.β * (T.M (lv T p r) x - z1R p * lv T p r x) + hv T p r x := by
      rw [h1]; field_simp
    linear_combination h2 - (lv T p r x) * hzs + (lag0 T (lv T p r) x) * hzz
  have hl : ∀ x k, lagv T (LinvR T p r) x k = lag0 T (fun z => LinvR T p r z k) x :=
    fun _ _ => rfl
  have hm : ∀ x k, Mv T.M (LinvR T p r) x k = T.M (fun z => LinvR T p r z k) x := fun _ _ => rfl
  have v0 : ∀ x, LinvR T p r x 0 = yv T p r x := fun x => rfl
  have v1 : ∀ x, LinvR T p r x 1 = piv T p r x := fun x => rfl
  have v2 : ∀ x, LinvR T p r x 2 = cv T p r x := fun x => rfl
  have v3 : ∀ x, LinvR T p r x 3 = lv T p r x := fun x => rfl
  have v4 : ∀ x, LinvR T p r x 4 = gv T p r x := fun x => rfl
  have f1 : (fun z => LinvR T p r z 1) = piv T p r := funext v1
  have f3 : (fun z => LinvR T p r z 3) = lv T p r := funext v3
  have hMpi : ∀ x, T.M (piv T p r) x = (T.M (lv T p r) x - lv T p r x) / gamb p -
      T.M (fun y => r y 1) x / (gamb p * p.ψ) := fun x => by
    have e : piv T p r = fun y => (1 / gamb p) * (1 * lv T p r y + -1 * lag0 T (lv T p r) y) +
        (-(1 / (gamb p * p.ψ))) * r y 1 := by
      funext y; simp only [piv]; ring
    rw [e, M_lin, M_lin, M_lag0]; ring
  have hsv : ∀ x, Gw p * sv p r x = cR4 p * r x 4 - r x 0 - r x 2 := fun x => by
    unfold sv; field_simp
  have hGa := Gw_aR hG
  have hgA := gamb_aR hp hG
  funext x i
  fin_cases i
  · have h02 := red_lam hp (lagv T (LinvR T p r) x) (LinvR T p r x)
    have hc2 : DQr p (lagv T (LinvR T p r) x) (LinvR T p r x) 2 = r x 2 := by
      simp only [DQr, Matrix.cons_val]
      rw [v0, v2, v3, v4]
      simp only [gv]; ring
    simp only [LR, Fin.zero_eta, Pi.add_apply, DNr, Matrix.cons_val_zero, add_zero]
    rw [v0, v2, v3, hc2] at h02
    have hyc : yv T p r x - cv T p r x = r x 4 := by simp only [yv]; ring
    rw [hyc] at h02
    have hcv : cv T p r x = -(aR p * lv T p r x) + sv p r x := rfl
    rw [hcv] at h02
    have hsv' := hsv x
    unfold cR4 at hsv'
    linear_combination h02 + (lv T p r x) * hGa - hsv'
  · simp only [LR, Fin.mk_one, Pi.add_apply, DNr, DQr, Matrix.cons_val_one,
      Matrix.cons_val_zero, add_zero]
    rw [hl x 3, v1, v3, f3]
    simp only [piv]
    field_simp
    ring
  · simp only [LR, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, add_zero]
    rw [v0, v2, v3, v4]
    simp only [gv]; ring
  · simp only [LR, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val]
    rw [hm x 1, v0, v1, v2, f1, hMpi x]
    have hk := key x
    have hcv : cv T p r x = -(aR p * lv T p r x) + sv p r x := rfl
    have hyv : yv T p r x = cv T p r x + r x 4 := rfl
    have hpv : piv T p r x = (lv T p r x - lag0 T (lv T p r) x) / gamb p -
        r x 1 / (gamb p * p.ψ) := rfl
    have hhv : hv T p r x = gamb p / p.ψ * (r x 3 + p.θ * p.m * p.ω * r x 4 +
        p.θ * p.m * (p.σ + p.ω) * sv p r x) +
        (r x 1 - p.β * T.M (fun y => r y 1) x) / p.ψ := rfl
    rw [hyv, hcv, hpv]
    rw [hhv, ← hgA] at hk
    have hgb' := hgb.ne'
    have hψ' := hψ.ne'
    field_simp at hk ⊢
    linear_combination hk
  · simp only [LR, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, add_zero]
    rw [v0, v2]
    simp only [yv]; ring

/-- Woodford (2003), Ch. 7 and App. A.3 (**injectivity: the a-priori bound with a predetermined
multiplier**): on every event tree, a bounded solution of the homogeneous linearised Rotemberg
Ramsey system with zero initial lag is zero. -/
theorem LR_inj (hp : p.Basic) (hG : 0 < Gw p) (v : X → Fin 5 → ℝ) (B : ℝ)
    (hB : ∀ x k, |v x k| ≤ B) (h0 : LR T p v = 0) : v = 0 := by
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := zR_props hp hG
  have hβ := hp.β_pos
  have hψ := hp.ψ_pos
  have hgb : 0 < gamb p := by
    unfold gamb
    have := hp.m_pos; have := hp.σ_pos; have := hp.ω_nonneg
    have : 0 < p.σ + p.ω := by linarith
    positivity
  have hRk : ∀ x k, (DQr p (lagv T v x) (v x) + DNr p (Mv T.M v x)) k = 0 := fun x k => by
    have := congrFun (congrFun h0 x) k; exact this
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  have e4 : ∀ x, v x 0 = v x 2 := fun x => by
    have := hRk x 4
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val, add_zero] at this
    linarith
  have e1 : ∀ x, v x 1 = (v x 3 - lag0 T (fun z => v z 3) x) / gamb p := fun x => by
    have := hRk x 1
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val_one, Matrix.cons_val_zero,
      add_zero] at this
    rw [hl] at this
    field_simp
    have : p.ψ * (v x 1 * gamb p - (v x 3 - lag0 T (fun z => v z 3) x)) = 0 := by
      linear_combination -this
    have := (mul_eq_zero.1 this).resolve_left hψ.ne'
    linarith
  have e02 : ∀ x, v x 2 = -(aR p * v x 3) := fun x => by
    have h02 := red_lam hp (lagv T v x) (v x)
    have c0 := hRk x 0
    have c2 := hRk x 2
    simp only [Pi.add_apply, DNr, Matrix.cons_val_zero, Matrix.cons_val, add_zero] at c0 c2
    rw [c0, c2, e4 x, sub_self, mul_zero, add_zero] at h02
    have hGa := Gw_aR hG
    unfold aR
    field_simp
    linear_combination h02
  set L : X → ℝ := fun z => v z 3 with hLdef
  have hv1f : (fun z => v z 1) = fun z => (1 / gamb p) * (1 * L z + -1 * lag0 T L z) := by
    funext z; rw [e1 z]; ring
  have hMv1 : ∀ x, T.M (fun z => v z 1) x = (T.M L x - L x) / gamb p := fun x => by
    rw [hv1f]
    have := M_lin T (1 / gamb p) 0 (fun z => 1 * L z + -1 * lag0 T L z) (fun _ => 0)
    simp only [zero_mul, add_zero] at this
    rw [this, M_lin, M_lag0]; ring
  have key : ∀ x, (1 + p.β + cR p) * L x - lag0 T L x - p.β * T.M L x = 0 := fun x => by
    have c3 := hRk x 3
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val] at c3
    rw [hm, hMv1 x, e1 x, e4 x, e02 x] at c3
    have hgA := gamb_aR hp hG
    rw [← hgA]
    have hgb' := hgb.ne'
    have hψ' := hψ.ne'
    field_simp at c3 ⊢
    linear_combination c3
  have hLB : ∀ x, |L x| ≤ B := fun x => hB x 3
  have hlB : ∀ x, |lag0 T L x| ≤ |B| :=
    abs_lag0_le T (abs_nonneg B) fun x => (hLB x).trans (le_abs_self B)
  have hu : ∀ x, L x - z1R p * lag0 T L x = 0 := by
    refine zero_of_eq_cM T (abs_inv_z2R hp hG) (A := |B| + z1R p * |B|)
      (g := fun z => L z - z1R p * lag0 T L z) (fun x => ?_) (fun x => ?_)
    · refine (abs_sub _ _).trans (add_le_add ((hLB x).trans (le_abs_self B)) ?_)
      rw [abs_mul, abs_of_pos hz10]
      exact mul_le_mul_of_nonneg_left (hlB x) hz10.le
    · have e : (fun z => L z - z1R p * lag0 T L z) = fun z => 1 * L z + -z1R p * lag0 T L z := by
        funext z; ring
      rw [e, M_lin, M_lag0]
      simp only
      have hz2 : z2R p ≠ 0 := by linarith
      have hq : p.β * (z2R p * (L x - z1R p * lag0 T L x) - (T.M L x - z1R p * L x)) = 0 := by
        linear_combination key x + (L x) * hzs - (lag0 T L x) * hzz
      have hq2 := (mul_eq_zero.1 hq).resolve_left hβ.ne'
      field_simp
      linarith
  have hL0 : ∀ x, L x = 0 := zero_of_eq_lag T (c := z1R p) (g := L) fun x => by linarith [hu x]
  have hLf : L = fun _ => 0 := funext hL0
  have h3 : ∀ x, v x 3 = 0 := hL0
  have h2 : ∀ x, v x 2 = 0 := fun x => by rw [e02 x, h3 x, mul_zero, neg_zero]
  have h0' : ∀ x, v x 0 = 0 := fun x => by rw [e4 x, h2 x]
  have h1 : ∀ x, v x 1 = 0 := fun x => by
    rw [e1 x]
    have : lag0 T (fun z => v z 3) x = 0 := by
      change lag0 T L x = 0; rw [hLf, lag0_zero]
    rw [this, h3 x]; simp
  have h4 : ∀ x, v x 4 = 0 := fun x => by
    have c2 := hRk x 2
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val, add_zero] at c2
    rw [h0' x, h2 x, h3 x] at c2
    linarith
  funext x k
  fin_cases k
  exacts [h0' x, h1 x, h2 x, h3 x, h4 x]

/-! ## Linearity, the left inverse and the uniform bound -/

/-- Woodford (2003), Ch. 7: the linearisation as one linear map of
`(lag, current, expected lead)`. -/
noncomputable def DLin (p : Par) :
    ((Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ)) →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun q := DQr p q.1 q.2.1 + DNr p q.2.2
  map_add' q q' := by
    funext i; fin_cases i <;> simp [DQr, DNr] <;> ring
  map_smul' c q := by
    funext i; fin_cases i <;> simp [DQr, DNr] <;> ring

/-- The linearisation is bounded. -/
theorem norm_DLin_le (p : Par) (um u n : Fin 5 → ℝ) {B : ℝ}
    (h1 : ‖um‖ ≤ B) (h2 : ‖u‖ ≤ B) (h3 : ‖n‖ ≤ B) :
    ‖DQr p um u + DNr p n‖ ≤ ‖LinearMap.toContinuousLinearMap (DLin p)‖ * B := by
  have := (LinearMap.toContinuousLinearMap (DLin p)).le_opNorm (um, u, n)
  refine this.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  simp only [Prod.norm_def]
  exact max_le h1 (max_le h2 h3)

/-- The linearised operator is bounded. -/
theorem norm_LR_le (p : Par) {v : X → Fin 5 → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖v x‖ ≤ B) (x : X) :
    ‖LR T p v x‖ ≤ ‖LinearMap.toContinuousLinearMap (DLin p)‖ * B :=
  norm_DLin_le p _ _ _ (norm_lagv_le T hB0 hB x) (hB x) (Mv_norm_le T.markov hB0 hB x)

/-- The linearised operator is subtractive. -/
theorem LR_sub (p : Par) (v w : X → Fin 5 → ℝ) (x : X) :
    LR T p (fun y => v y - w y) x = LR T p v x - LR T p w x := by
  have hl : lagv T (fun y => v y - w y) x = lagv T v x - lagv T w x := by
    funext i
    have := lag0_lin T 1 (-1) (fun y => v y i) (fun y => w y i) x
    simp only [lagv, Pi.sub_apply]
    convert this using 2 <;> [funext y; skip] <;> ring
  have hm := congrFun (NonlinearNKMarkovLinks.Mv_sub T.M v w) x
  have e := (DLin p).map_sub (lagv T v x, v x, Mv T.M v x) (lagv T w x, w x, Mv T.M w x)
  simp only [DLin, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_sub_mk] at e
  simp only [LR, hl, hm]
  exact e

/-- Woodford (2003), App. A.3 (**the uniform bound on the inverse**): `‖L⁻¹r‖ ≤ K‖r‖` with `K`
depending only on the parameters, for every event tree. -/
theorem LinvR_bound (hp : p.Basic) (hG : 0 < Gw p) : ∃ K, 0 ≤ K ∧ ∀ {Y : Type*}
    (T : LagTree Y) (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y, ‖r y‖ ≤ A) →
      ∀ y, ‖LinvR T p r y‖ ≤ K * A := by
  obtain ⟨c, hc, hb⟩ := bd_all hp hG
  refine ⟨c, hc, fun T r A hA hr y => ?_⟩
  have hr' : ∀ y k, |r y k| ≤ A := fun y k => by
    have := (norm_le_pi_norm (r y) k).trans (hr y); rwa [Real.norm_eq_abs] at this
  obtain ⟨b3, b2, b0, b1, b4⟩ := hb T r A hA hr' y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  exacts [b0, b1, b2, b3, b4]

/-- Woodford (2003), App. A.3 (**the left inverse**): `L⁻¹(Lv) = v` for bounded `v`. -/
theorem LinvR_LR (hp : p.Basic) (hG : 0 < Gw p) {v : X → Fin 5 → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, ‖v x‖ ≤ B) : LinvR T p (LR T p v) = v := by
  obtain ⟨K, hK0, hK⟩ := LinvR_bound hp hG
  set CL := ‖LinearMap.toContinuousLinearMap (DLin p)‖
  have hLB : ∀ x, ‖LR T p v x‖ ≤ CL * B := norm_LR_le T p hB0 hB
  have hLB' : ∀ x k, |LR T p v x k| ≤ CL * B := fun x k => by
    have := (norm_le_pi_norm (LR T p v x) k).trans (hLB x); rwa [Real.norm_eq_abs] at this
  have hw := LR_LinvR T hp hG (LR T p v) (CL * B) (by positivity) hLB'
  have hbd := hK T (LR T p v) (CL * B) (by positivity) hLB
  have hz := LR_inj T hp hG (fun x => v x - LinvR T p (LR T p v) x) (B + K * (CL * B))
    (fun x k => by
      have := (norm_le_pi_norm (v x - LinvR T p (LR T p v) x) k).trans
        ((norm_sub_le _ _).trans (add_le_add (hB x) (hbd x)))
      rwa [Real.norm_eq_abs] at this)
    (by funext x; rw [LR_sub, hw, sub_self]; rfl)
  funext x
  have := congrFun hz x
  simp only [Pi.zero_apply] at this
  exact (sub_eq_zero.1 this).symm

/-- Woodford (2003), App. A.3: the inverse is subtractive on bounded forcings. -/
theorem LinvR_sub (hp : p.Basic) (hG : 0 < Gw p) {r r' : X → Fin 5 → ℝ} {A A' : ℝ}
    (hA : 0 ≤ A) (hA' : 0 ≤ A') (hr : ∀ x, ‖r x‖ ≤ A) (hr' : ∀ x, ‖r' x‖ ≤ A') :
    LinvR T p (fun x => r x - r' x) = fun x => LinvR T p r x - LinvR T p r' x := by
  obtain ⟨K, hK0, hK⟩ := LinvR_bound hp hG
  have hc : ∀ {s : X → Fin 5 → ℝ} {S : ℝ}, (∀ x, ‖s x‖ ≤ S) → ∀ x k, |s x k| ≤ S :=
    fun hs x k => by
      have := (norm_le_pi_norm _ k).trans (hs x); rwa [Real.norm_eq_abs] at this
  have hw := LR_LinvR T hp hG r A hA (hc hr)
  have hw' := LR_LinvR T hp hG r' A' hA' (hc hr')
  have hB : ∀ x, ‖LinvR T p r x - LinvR T p r' x‖ ≤ K * A + K * A' := fun x =>
    (norm_sub_le _ _).trans (add_le_add (hK T r A hA hr x) (hK T r' A' hA' hr' x))
  have e := LinvR_LR T hp hG (by positivity) hB
  rw [← e]
  congr 1
  funext x
  rw [LR_sub, hw, hw']

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyTree
