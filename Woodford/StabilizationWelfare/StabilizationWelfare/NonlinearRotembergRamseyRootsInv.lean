/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyDegenerate

/-!
# The linearised Rotemberg Ramsey operator for any root configuration `|z_s| < 1 < |z_u|`

Woodford (2003), *Interest and Prices*, Chapter 7, (1.20), pp. 475–476, and Appendix A.3. The
inverse `NonlinearRotembergRamseyTree.LinvR` uses the roots `0 < z₁ < 1 < z₂` that exist when
`G > 0`. Here the same construction is carried out for ANY pair of roots of
`βz² − (1 + β + κθ_R)z + 1` with `|z_s| < 1 < |z_u|` and `G ≠ 0` (`RootsH`); in particular for
`G < 0` and `κθ_R < −2(1 + β)`, where the stable root is negative (`rootsH_neg`).

* `LinvN`: the inverse, with `λ̂ = bwd z_s (fwdS (1/z_u) (h/(βz_u)))`.
* **`LR_LinvN`**, **`LR_injN`**, **`LinvN_bound`**: right inverse, injectivity on bounded
  processes, and a uniform bound, on every event tree.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyRootsInv

open Filter Topology
open NonlinearNKMarkov (Mv IsMarkov mnorm Mv_norm_le)
open NonlinearNKMarkovRamseyTree (LagTree lag0 M_lag0 lag0_lin abs_lag0_le bwd bwd_eq
  zero_of_eq_lag M_lin M_const zero_of_eq_cM fwdS Sg Sg_nonneg fwdS_spec lagv lb2 lbM lbLag
  norm_lagv_le lag0_zero)
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyTree (LR sv hv aR cR cR4 cR_pos LR_sub norm_LR_le DLin)
open NonlinearRotembergRamseyAE (gamb_pos)
open NonlinearRotembergRamseyDegenerate (cG cG_eq cG_neg)

variable {p : Par}

/-! ## Root hypotheses -/

/-- Woodford (2003), Ch. 7, (1.20): a stable and an unstable root of the commitment polynomial,
`|z_s| < 1 < |z_u|`, `βz_sz_u = 1`, `β(z_s + z_u) = 1 + β + κθ_R`, with `G ≠ 0`. -/
structure RootsH (p : Par) (zs zu : ℝ) : Prop where
  G_ne : Gw p ≠ 0
  s_lt : |zs| < 1
  u_gt : 1 < |zu|
  prod : p.β * zs * zu = 1
  sum : p.β * (zs + zu) = 1 + p.β + cR p

/-- Woodford (2003), Ch. 7, (1.20) with `G < 0` (**the determinate negative-`G` case**): if
`κθ_R < −2(1 + β)`, the roots `z_s ∈ (−1, 0)`, `z_u < −1` satisfy `RootsH`. -/
theorem rootsH_neg (hp : p.Basic) (hG : Gw p < 0) (hc : cG p < -(2 * (1 + p.β))) :
    ∃ zs zu, -1 < zs ∧ zs < 0 ∧ RootsH p zs zu := by
  have hβ := hp.β_pos
  have hβ1 := hp.β_lt_one
  have hcR : cR p = cG p := by rw [cG_eq hp hG.ne]; rfl
  obtain ⟨s, hsdef⟩ : ∃ s, s = 1 + p.β + cG p := ⟨_, rfl⟩
  have hs : s < -(1 + p.β) := by linarith
  have hD0 : 4 * p.β ≤ s ^ 2 := by nlinarith
  obtain ⟨D, hDdef⟩ : ∃ D, D = Real.sqrt (s ^ 2 - 4 * p.β) := ⟨_, rfl⟩
  have hD2 : D ^ 2 = s ^ 2 - 4 * p.β := by rw [hDdef]; exact Real.sq_sqrt (by linarith)
  have hDnn : 0 ≤ D := by rw [hDdef]; exact Real.sqrt_nonneg _
  obtain ⟨z1, hz1d⟩ : ∃ z, z = (s + D) / (2 * p.β) := ⟨_, rfl⟩
  obtain ⟨z2, hz2d⟩ : ∃ z, z = (s - D) / (2 * p.β) := ⟨_, rfl⟩
  have h1 : p.β * z1 * z2 = 1 := by rw [hz1d, hz2d]; field_simp; linear_combination -hD2
  have h2 : p.β * (z1 + z2) = s := by rw [hz1d, hz2d]; field_simp; ring
  have hle : z2 ≤ z1 := by
    rw [hz1d, hz2d]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hprod : (z1 + 1) * (z2 + 1) < 0 := by
    have e : p.β * ((z1 + 1) * (z2 + 1)) = 1 + p.β + s := by linear_combination h1 + h2
    have hneg : 1 + p.β + s < 0 := by linarith
    by_contra hh; push Not at hh
    nlinarith
  have hz1 : -1 < z1 := by by_contra hh; push Not at hh; nlinarith
  have hz2 : z2 < -1 := by by_contra hh; push Not at hh; nlinarith
  have hz10 : z1 < 0 := by
    by_contra hh; push Not at hh
    have : z1 * z2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hh (by linarith)
    nlinarith
  refine ⟨z1, z2, hz1, hz10, ⟨hG.ne, ?_, ?_, h1, by rw [h2, hsdef, hcR]⟩⟩
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_of_neg (by linarith)]; linarith

/-- Woodford (2003), Ch. 7: the `G > 0` roots satisfy `RootsH`. -/
theorem rootsH_pos (hp : p.Basic) (hG : 0 < Gw p) :
    RootsH p (NonlinearRotembergRamseyTree.z1R p) (NonlinearRotembergRamseyTree.z2R p) := by
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := NonlinearRotembergRamseyTree.zR_props hp hG
  exact ⟨hG.ne', by rw [abs_lt]; constructor <;> linarith,
    by rw [abs_of_pos (by linarith)]; exact hz21, hzz, hzs⟩

/-! ## A backward bound for signed coefficients -/

variable {X : Type*} (T : LagTree X)

/-- `|bwd c f| ≤ A/(1 − |c|)` for `|c| < 1`. -/
theorem abs_bwd_le' {c : ℝ} (hc : |c| < 1) {f : X → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A) (x : X) : |bwd T c f x| ≤ A / (1 - |c|) := by
  have hc0 : 0 ≤ |c| := abs_nonneg c
  unfold bwd
  calc _ ≤ ∑ j ∈ Finset.range (T.depth x + 1), |c| ^ j * A := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (hf _) (pow_nonneg hc0 j)
    _ = A * ∑ j ∈ Finset.range (T.depth x + 1), |c| ^ j := by rw [Finset.mul_sum]; ring_nf
    _ ≤ A * (1 - |c|)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        rw [← tsum_geometric_of_lt_one hc0 hc]
        exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hc0 j)
          (summable_geometric_of_lt_one hc0 hc)
    _ = A / (1 - |c|) := by ring

/-! ## The inverse -/

/-- The inverse, the forward factor `U = λ − z_s lag λ`. -/
noncomputable def uvN (p : Par) (zu : ℝ) (r : X → Fin 5 → ℝ) : X → ℝ :=
  fwdS T (1 / zu) (fun x => hv T p r x / (p.β * zu))

/-- The inverse, the multiplier `λ̂ = z_s lag λ̂ + U`. -/
noncomputable def lvN (p : Par) (zs zu : ℝ) (r : X → Fin 5 → ℝ) : X → ℝ :=
  bwd T zs (uvN T p zu r)

/-- The inverse, consumption. -/
noncomputable def cvN (p : Par) (zs zu : ℝ) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  -(aR p * lvN T p zs zu r x) + sv p r x

/-- The inverse, output. -/
noncomputable def yvN (p : Par) (zs zu : ℝ) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  cvN T p zs zu r x + r x 4

/-- The inverse, inflation. -/
noncomputable def pivN (p : Par) (zs zu : ℝ) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (lvN T p zs zu r x - lag0 T (lvN T p zs zu r) x) / gamb p - r x 1 / (gamb p * p.ψ)

/-- The inverse, the resource multiplier. -/
noncomputable def gvN (p : Par) (zs zu : ℝ) (r : X → Fin 5 → ℝ) (x : X) : ℝ :=
  (1 - p.σ) * cvN T p zs zu r x - lvN T p zs zu r x * (p.θ * p.m * p.σ) -
    lamb p * (p.θ * p.m * p.σ * (yvN T p zs zu r x - p.σ * cvN T p zs zu r x)) -
      gamb p * cvN T p zs zu r x - r x 2

/-- Woodford (2003), Ch. 7 and App. A.3 (**the inverse for any root configuration**). -/
noncomputable def LinvN (p : Par) (zs zu : ℝ) (r : X → Fin 5 → ℝ) (x : X) : Fin 5 → ℝ :=
  ![yvN T p zs zu r x, pivN T p zs zu r x, cvN T p zs zu r x, lvN T p zs zu r x,
    gvN T p zs zu r x]

/-! ## Algebra with `G ≠ 0` -/

/-- `G aR = θm(σ+ω)`. -/
theorem Gw_aR' (hG : Gw p ≠ 0) : Gw p * aR p = p.θ * p.m * (p.σ + p.ω) := by
  unfold aR; field_simp

/-- `γ̄ θm(σ+ω) aR / ψ = κθ_R`. -/
theorem gamb_aR' (hp : p.Basic) (hG : Gw p ≠ 0) :
    gamb p * (p.θ * p.m * (p.σ + p.ω)) * aR p / p.ψ = cR p := by
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  have hψ := hp.ψ_pos.ne'
  unfold cR thR aR gamb Par.κ
  field_simp

/-! ## Uniform bounds -/

/-- The consumption forcing is bounded when `G ≠ 0`. -/
theorem bd_svN (hG : Gw p ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*}
    (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) → ∀ y, |sv p r y| ≤ c * A := by
  have hG0 : 0 < |Gw p| := abs_pos.2 hG
  refine ⟨(|cR4 p| + 2) / |Gw p|, by positivity, fun r A hA hr y => ?_⟩
  unfold sv
  rw [abs_div, div_le_iff₀ hG0]
  have h1 : |cR4 p * r y 4| ≤ |cR4 p| * A := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr y 4) (abs_nonneg _)
  calc |cR4 p * r y 4 - r y 0 - r y 2| ≤ |cR4 p * r y 4| + |r y 0| + |r y 2| := by
        refine (abs_sub _ _).trans ?_
        exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ |cR4 p| * A + A + A := by linarith [hr y 0, hr y 2]
    _ = (|cR4 p| + 2) / |Gw p| * A * |Gw p| := by field_simp; ring

/-- The forcing of the multiplier equation is bounded when `G ≠ 0`. -/
theorem bd_hvN (hp : p.Basic) (hG : Gw p ≠ 0) : ∃ c, 0 ≤ c ∧ ∀ {Y : Type*} (T : LagTree Y)
    (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y k, |r y k| ≤ A) → ∀ y, |hv T p r y| ≤ c * A := by
  obtain ⟨cs, hcs, hs⟩ := bd_svN hG
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

/-- The multiplier part of the inverse is bounded. -/
theorem bd_lvN (hp : p.Basic) {zs zu : ℝ} (hR : RootsH p zs zu) : ∃ c, 0 ≤ c ∧
    ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y k, |r y k| ≤ A) → ∀ y, |lvN T p zs zu r y| ≤ c * A := by
  obtain ⟨ch, hch, hh⟩ := bd_hvN hp hR.G_ne
  have hβ := hp.β_pos
  have hu0 : zu ≠ 0 := by intro h; have := hR.u_gt; rw [h, abs_zero] at this; linarith
  have hbz : 0 < |p.β * zu| := abs_pos.2 (mul_ne_zero hβ.ne' hu0)
  have hiu : |1 / zu| < 1 := by
    rw [abs_div, abs_one, div_lt_one (by linarith [hR.u_gt])]; exact hR.u_gt
  set k := 1 / |p.β * zu|
  have hk : 0 ≤ k := by positivity
  have hs1 : 0 < 1 - |zs| := by linarith [hR.s_lt]
  refine ⟨Sg (1 / zu) * (k * ch) / (1 - |zs|), by
    have := Sg_nonneg (1 / zu); positivity, fun T r A hA hr y => ?_⟩
  have hf : ∀ y, |hv T p r y / (p.β * zu)| ≤ k * ch * A := fun y => by
    rw [abs_div, div_le_iff₀ hbz]
    calc |hv T p r y| ≤ ch * A := hh T r A hA hr y
      _ = k * ch * A * |p.β * zu| := by simp only [k]; field_simp
  obtain ⟨hU, -⟩ := fwdS_spec T hiu (by positivity) hf
  have hU' : ∀ y, |uvN T p zu r y| ≤ Sg (1 / zu) * (k * ch) * A := fun y => by
    have := hU y; rw [← mul_assoc] at this; exact this
  have := abs_bwd_le' T hR.s_lt (mul_nonneg (mul_nonneg (Sg_nonneg _) (by positivity)) hA) hU' y
  calc |lvN T p zs zu r y| ≤ _ := this
    _ = _ := by ring

/-- All components of the inverse are bounded, uniformly over event trees. -/
theorem bd_allN (hp : p.Basic) {zs zu : ℝ} (hR : RootsH p zs zu) : ∃ c, 0 ≤ c ∧
    ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y k, |r y k| ≤ A) → ∀ y,
      |lvN T p zs zu r y| ≤ c * A ∧ |cvN T p zs zu r y| ≤ c * A ∧ |yvN T p zs zu r y| ≤ c * A ∧
        |pivN T p zs zu r y| ≤ c * A ∧ |gvN T p zs zu r y| ≤ c * A := by
  obtain ⟨cl, hcl, hl⟩ := bd_lvN hp hR
  obtain ⟨cs, hcs, hs⟩ := bd_svN hR.G_ne
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  set cc := |-aR p| * cl + |1| * cs
  set cy := |1| * cc + |1| * 1
  set cp := |1 / gamb p| * (|1| * cl + |-1| * cl) + |-(1 / (gamb p * p.ψ))| * 1
  set k1 := 1 - p.σ - gamb p + lamb p * (p.θ * p.m * p.σ) * p.σ
  set k2 := -(p.θ * p.m * p.σ)
  set k3 := -(lamb p * (p.θ * p.m * p.σ))
  set cg := |1| * (|k1| * cc + |k2| * cl) + |1| * (|k3| * cy + |-1| * 1)
  refine ⟨cl + cc + cy + cp + cg, by positivity, fun T r A hA hr y => ?_⟩
  have hr' : ∀ k y, |r y k| ≤ 1 * A := fun k y => by simpa using hr y k
  have hL := hl T r A hA hr
  have hC : ∀ y, |cvN T p zs zu r y| ≤ cc * A := fun y => by
    have := lb2 hL (hs r A hA hr) (-aR p) 1 y
    convert this using 2; simp only [cvN]; ring
  have hY : ∀ y, |yvN T p zs zu r y| ≤ cy * A := fun y => by
    have := lb2 hC (hr' 4) 1 1 y
    convert this using 2; simp only [yvN]; ring
  have hP : ∀ y, |pivN T p zs zu r y| ≤ cp * A := fun y => by
    have := lb2 (lb2 hL (lbLag T (by positivity) hL) 1 (-1)) (hr' 1) (1 / gamb p)
      (-(1 / (gamb p * p.ψ))) y
    convert this using 2; simp only [pivN]; field_simp; ring
  have hGv : ∀ y, |gvN T p zs zu r y| ≤ cg * A := fun y => by
    have := lb2 (lb2 hC hL k1 k2) (lb2 hY (hr' 2) k3 (-1)) 1 1 y
    convert this using 2; simp only [gvN, k1, k2, k3]; ring
  have hA' : ∀ c, c ≤ cl + cc + cy + cp + cg → c * A ≤ (cl + cc + cy + cp + cg) * A :=
    fun c hc => mul_le_mul_of_nonneg_right hc hA
  have hcc : 0 ≤ cc := by positivity
  have hcy : 0 ≤ cy := by positivity
  have hcp : 0 ≤ cp := by positivity
  have hcg : 0 ≤ cg := by positivity
  exact ⟨(hL y).trans (hA' _ (by linarith)), (hC y).trans (hA' _ (by linarith)),
    (hY y).trans (hA' _ (by linarith)), (hP y).trans (hA' _ (by linarith)),
    (hGv y).trans (hA' _ (by linarith))⟩

/-- Woodford (2003), App. A.3 (**the uniform bound on the inverse**). -/
theorem LinvN_bound (hp : p.Basic) {zs zu : ℝ} (hR : RootsH p zs zu) : ∃ K, 0 ≤ K ∧
    ∀ {Y : Type*} (T : LagTree Y) (r : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A → (∀ y, ‖r y‖ ≤ A) →
      ∀ y, ‖LinvN T p zs zu r y‖ ≤ K * A := by
  obtain ⟨c, hc, hb⟩ := bd_allN hp hR
  refine ⟨c, hc, fun T r A hA hr y => ?_⟩
  have hr' : ∀ y k, |r y k| ≤ A := fun y k => by
    have := (norm_le_pi_norm (r y) k).trans (hr y); rwa [Real.norm_eq_abs] at this
  obtain ⟨b3, b2, b0, b1, b4⟩ := hb T r A hA hr' y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  exacts [b0, b1, b2, b3, b4]

/-! ## Right inverse and injectivity -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r` for any root configuration**). -/
theorem LR_LinvN (hp : p.Basic) {zs zu : ℝ} (hR : RootsH p zs zu) (r : X → Fin 5 → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hr : ∀ y k, |r y k| ≤ A) : LR T p (LinvN T p zs zu r) = r := by
  obtain ⟨ch, hch, hh⟩ := bd_hvN hp hR.G_ne
  have hzz := hR.prod
  have hzs := hR.sum
  have hβ := hp.β_pos
  have hu0 : zu ≠ 0 := by intro h; have := hR.u_gt; rw [h, abs_zero] at this; linarith
  have hbz : p.β * zu ≠ 0 := mul_ne_zero hβ.ne' hu0
  have hbz' : 0 < |p.β * zu| := abs_pos.2 hbz
  have hiu : |1 / zu| < 1 := by
    rw [abs_div, abs_one, div_lt_one (by linarith [hR.u_gt])]; exact hR.u_gt
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hf : ∀ y, |hv T p r y / (p.β * zu)| ≤ (1 / |p.β * zu| * ch) * A := fun y => by
    rw [abs_div, div_le_iff₀ hbz']
    calc |hv T p r y| ≤ ch * A := hh T r A hA hr y
      _ = 1 / |p.β * zu| * ch * A * |p.β * zu| := by field_simp
  obtain ⟨-, EU⟩ := fwdS_spec T hiu (by positivity) hf
  set L := lvN T p zs zu r
  set U := uvN T p zu r
  have EU' : ∀ x, U x = 1 / zu * T.M U x + hv T p r x / (p.β * zu) := EU
  have EL : ∀ x, L x = zs * lag0 T L x + U x := fun x => bwd_eq T _ _ x
  have EMU : ∀ x, T.M U x = T.M L x - zs * L x := fun x => by
    have e : U = fun x => 1 * L x + -zs * lag0 T L x := by funext x; rw [EL x]; ring
    rw [e, M_lin, M_lag0]; ring
  have key : ∀ x, (1 + p.β + cR p) * L x - lag0 T L x - p.β * T.M L x = hv T p r x := fun x => by
    have h1 := EU' x
    rw [EMU x] at h1
    have hux : U x = L x - zs * lag0 T L x := by rw [EL x]; ring
    rw [hux] at h1
    have h2 : p.β * zu * (L x - zs * lag0 T L x) =
        p.β * (T.M L x - zs * L x) + hv T p r x := by
      rw [h1]; field_simp
    linear_combination h2 - (L x) * hzs + (lag0 T L x) * hzz
  set v := LinvN T p zs zu r with hvdef
  have hl : ∀ x k, lagv T v x k = lag0 T (fun z => v z k) x := fun _ _ => rfl
  have hm : ∀ x k, Mv T.M v x k = T.M (fun z => v z k) x := fun _ _ => rfl
  have v0 : ∀ x, v x 0 = yvN T p zs zu r x := fun x => rfl
  have v1 : ∀ x, v x 1 = pivN T p zs zu r x := fun x => rfl
  have v2 : ∀ x, v x 2 = cvN T p zs zu r x := fun x => rfl
  have v3 : ∀ x, v x 3 = L x := fun x => rfl
  have v4 : ∀ x, v x 4 = gvN T p zs zu r x := fun x => rfl
  have f1 : (fun z => v z 1) = pivN T p zs zu r := funext v1
  have f3 : (fun z => v z 3) = L := funext v3
  have hMpi : ∀ x, T.M (pivN T p zs zu r) x = (T.M L x - L x) / gamb p -
      T.M (fun y => r y 1) x / (gamb p * p.ψ) := fun x => by
    have e : pivN T p zs zu r = fun y => (1 / gamb p) * (1 * L y + -1 * lag0 T L y) +
        (-(1 / (gamb p * p.ψ))) * r y 1 := by
      funext y; simp only [pivN, L]; ring
    rw [e, M_lin, M_lin, M_lag0]; ring
  have hsv : ∀ x, Gw p * sv p r x = cR4 p * r x 4 - r x 0 - r x 2 := fun x => by
    have := hR.G_ne
    unfold sv; field_simp
  have hGa := Gw_aR' hR.G_ne
  have hgA := gamb_aR' hp hR.G_ne
  funext x i
  fin_cases i
  · have h02 := red_lam hp (lagv T v x) (v x)
    have hc2 : DQr p (lagv T v x) (v x) 2 = r x 2 := by
      simp only [DQr, Matrix.cons_val]
      rw [v0, v2, v3, v4]
      simp only [gvN, L]; ring
    simp only [LR, Fin.zero_eta, Pi.add_apply, DNr, Matrix.cons_val_zero, add_zero]
    rw [v0, v2, v3, hc2] at h02
    have hyc : yvN T p zs zu r x - cvN T p zs zu r x = r x 4 := by simp only [yvN]; ring
    rw [hyc] at h02
    have hcv : cvN T p zs zu r x = -(aR p * L x) + sv p r x := rfl
    rw [hcv] at h02
    have hsv' := hsv x
    unfold cR4 at hsv'
    linear_combination h02 + (L x) * hGa - hsv'
  · simp only [LR, Fin.mk_one, Pi.add_apply, DNr, DQr, Matrix.cons_val_one,
      Matrix.cons_val_zero, add_zero]
    rw [hl x 3, v1, v3, f3]
    simp only [pivN, L]
    field_simp
    ring
  · simp only [LR, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, add_zero]
    rw [v0, v2, v3, v4]
    simp only [gvN, L]; ring
  · simp only [LR, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val]
    rw [hm x 1, v0, v1, v2, f1, hMpi x]
    have hk := key x
    have hcv : cvN T p zs zu r x = -(aR p * L x) + sv p r x := rfl
    have hyv : yvN T p zs zu r x = cvN T p zs zu r x + r x 4 := rfl
    have hpv : pivN T p zs zu r x = (L x - lag0 T L x) / gamb p -
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
    simp only [yvN]; ring

/-- Woodford (2003), Ch. 7 and App. A.3 (**injectivity for any root configuration**): a bounded
solution of the homogeneous linearised Rotemberg Ramsey system with zero initial lag is zero. -/
theorem LR_injN (hp : p.Basic) {zs zu : ℝ} (hR : RootsH p zs zu) (v : X → Fin 5 → ℝ) (B : ℝ)
    (hB : ∀ x k, |v x k| ≤ B) (h0 : LR T p v = 0) : v = 0 := by
  have hzz := hR.prod
  have hzs := hR.sum
  have hβ := hp.β_pos
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hG := hR.G_ne
  have hu0 : zu ≠ 0 := by intro h; have := hR.u_gt; rw [h, abs_zero] at this; linarith
  have hiu : |1 / zu| < 1 := by
    rw [abs_div, abs_one, div_lt_one (by linarith [hR.u_gt])]; exact hR.u_gt
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
    have hgA := gamb_aR' hp hG
    rw [← hgA]
    have hgb' := hgb.ne'
    have hψ' := hψ.ne'
    field_simp at c3 ⊢
    linear_combination c3
  have hLB : ∀ x, |L x| ≤ B := fun x => hB x 3
  have hlB : ∀ x, |lag0 T L x| ≤ |B| :=
    abs_lag0_le T (abs_nonneg B) fun x => (hLB x).trans (le_abs_self B)
  have hu : ∀ x, L x - zs * lag0 T L x = 0 := by
    refine zero_of_eq_cM T hiu (A := |B| + |zs| * |B|)
      (g := fun z => L z - zs * lag0 T L z) (fun x => ?_) (fun x => ?_)
    · refine (abs_sub _ _).trans (add_le_add ((hLB x).trans (le_abs_self B)) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hlB x) (abs_nonneg _)
    · have e : (fun z => L z - zs * lag0 T L z) = fun z => 1 * L z + -zs * lag0 T L z := by
        funext z; ring
      rw [e, M_lin, M_lag0]
      simp only
      have hq : p.β * (zu * (L x - zs * lag0 T L x) - (T.M L x - zs * L x)) = 0 := by
        linear_combination key x + (L x) * hzs - (lag0 T L x) * hzz
      have hq2 := (mul_eq_zero.1 hq).resolve_left hβ.ne'
      field_simp
      linarith
  have hL0 : ∀ x, L x = 0 := zero_of_eq_lag T (c := zs) (g := L) fun x => by linarith [hu x]
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

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyRootsInv
