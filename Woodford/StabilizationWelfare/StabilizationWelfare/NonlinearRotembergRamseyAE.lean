/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyTree
import StabilizationWelfare.NonlinearNKMarkovRamseyAE

/-!
# The linearised Rotemberg Ramsey operator on a filtered probability space (almost surely)

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (the timeless Ramsey plan with the
predetermined multiplier `λ_{t−1}`) and Appendix A.3, for the Rotemberg Ramsey conditions. The
a.s. calculus of adapted, essentially bounded processes (`lagS`, `bwdS`, `fwdSA`, the class
`AdB`, `Ms_lag`, `zero_of_eq_cMs`, `zero_of_eq_lagS`) is reused from
`NonlinearNKMarkovRamseyAE` (Calvo).

* `LRA` (the linearised operator), `LinvRA` (its inverse, the reduction of
  `NonlinearRotembergRamseyTree` in a.s. form), `adb_LinvRA` (uniform bounds);
* **`LRA_LinvRA`** (`L(L⁻¹r) = r` a.s.), **`LRA_inj`** (an adapted bounded solution of `Lv = 0`
  vanishes a.s.), `LinvRA_LRA`, `LinvRA_sub`, `LRA_sub`, `rhyp_LRA`, `rhyp_LinvRA`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyAE

open MeasureTheory Filter Topology
open NonlinearNKMarkov (mnorm)
open NonlinearNKMarkovAE (MvA Ms Gd Bd MvA_sub aesm_vec)
open NonlinearNKMarkovAEAdapted (aesmSub_vec)
open NonlinearNKMarkovRamseyAE (lagS bwdS bwdS_eq AdB AdB.aesm AdB.int adb_lin2 AdB.congr
  AdB.mono adb_Ms adb_lag adb_bwd fwdSA adb_fwd Ms_lag Ms_lin2 zero_of_eq_cMs zero_of_eq_lagS
  lagvS AdB.rescale lagS_zero)
open NonlinearNKMarkovRamseyTree (Sg Sg_nonneg)
open ExpectationsMeasure
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyTree

variable {p : Par} {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- Woodford (2003), App. A.3: every component adapted with the a.s. bound `|·| ≤ A`. -/
def RHyp (r : ℕ → Ω → Fin 5 → ℝ) (A : ℝ) : Prop := ∀ k, AdB E (fun t ω => r t ω k) 1 A

/-- Woodford (2003), Ch. 7 and App. A.3 (**the linearised Rotemberg Ramsey operator, a.s.
form**): `(Lv)_t = DQr(v_{t−1}, v_t) + DNr(E_t v_{t+1})`, zero lag at date `0`. -/
noncomputable def LRA (p : Par) (v : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : Fin 5 → ℝ :=
  DQr p (lagvS v t ω) (v t ω) + DNr p (MvA E v t ω)

/-- The inverse, the consumption forcing (pointwise). -/
noncomputable def svA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (cR4 p * r t ω 4 - r t ω 0 - r t ω 2) / Gw p

/-- The inverse, the forcing of the multiplier equation. -/
noncomputable def hvA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  gamb p / p.ψ * (r t ω 3 + p.θ * p.m * p.ω * r t ω 4 + p.θ * p.m * (p.σ + p.ω) * svA p r t ω) +
    (r t ω 1 - p.β * Ms E (fun s ω => r s ω 1) t ω) / p.ψ

/-- The inverse, the forward factor. -/
noncomputable def uvA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) : ℕ → Ω → ℝ :=
  fwdSA E (1 / z2R p) (fun t ω => hvA E p r t ω / (p.β * z2R p))

/-- The inverse, the multiplier. -/
noncomputable def lvA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) : ℕ → Ω → ℝ :=
  bwdS (z1R p) (uvA E p r)

/-- The inverse, consumption. -/
noncomputable def cvA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  -(aR p * lvA E p r t ω) + svA p r t ω

/-- The inverse, output. -/
noncomputable def yvA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  cvA E p r t ω + r t ω 4

/-- The inverse, inflation. -/
noncomputable def pivA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (lvA E p r t ω - lagS (lvA E p r) t ω) / gamb p - r t ω 1 / (gamb p * p.ψ)

/-- The inverse, the resource multiplier. -/
noncomputable def gvA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (1 - p.σ) * cvA E p r t ω - lvA E p r t ω * (p.θ * p.m * p.σ) -
    lamb p * (p.θ * p.m * p.σ * (yvA E p r t ω - p.σ * cvA E p r t ω)) - gamb p * cvA E p r t ω -
      r t ω 2

/-- Woodford (2003), Ch. 7 and App. A.3 (**the inverse, a.s. form**). -/
noncomputable def LinvRA (p : Par) (r : ℕ → Ω → Fin 5 → ℝ) (t : ℕ) (ω : Ω) : Fin 5 → ℝ :=
  ![yvA E p r t ω, pivA E p r t ω, cvA E p r t ω, lvA E p r t ω, gvA E p r t ω]

/-- `γ̄ > 0`. -/
theorem gamb_pos (hp : p.Basic) : 0 < gamb p := by
  unfold gamb
  have := hp.m_pos; have := hp.σ_pos; have := hp.ω_nonneg
  have : 0 < p.σ + p.ω := by linarith
  positivity

/-! ## Uniform bounds -/

/-- Woodford (2003), App. A.3 (**uniform a.s. bounds on the inverse**): every component is
adapted with an a.s. bound `c·A`, `c` depending only on the parameters. -/
theorem adb_all (hp : p.Basic) (hG : 0 < Gw p) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 5 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A →
        AdB E (uvA E p r) c A ∧ AdB E (lvA E p r) c A ∧ AdB E (cvA E p r) c A ∧
          AdB E (yvA E p r) c A ∧ AdB E (pivA E p r) c A ∧ AdB E (gvA E p r) c A ∧
          AdB E (svA p r) c A ∧ AdB E (hvA E p r) c A := by
  obtain ⟨hz10, hz11, hz21, -, -⟩ := zR_props hp hG
  have hβ := hp.β_pos
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hz2 : 0 < p.β * z2R p := mul_pos hβ (by linarith)
  -- the constants
  set cs := |cR4 p / Gw p| * 1 + |-1 / Gw p| * (|1| * 1 + |1| * 1)
  set k1 := gamb p / p.ψ
  set ch := |k1| * (|1| * (|1| * 1 + |p.θ * p.m * p.ω| * 1) + |p.θ * p.m * (p.σ + p.ω)| * cs) +
    |1 / p.ψ| * (|1| * 1 + |-p.β| * 1)
  set chz := |1 / (p.β * z2R p)| * ch + |0| * ch
  set cu := Sg (1 / z2R p) * chz
  set cl := cu / (1 - z1R p)
  set cc := |-aR p| * cl + |1| * cs
  set cy := |1| * cc + |1| * 1
  set cp := |1 / gamb p| * (|1| * cl + |-1| * cl) + |-(1 / (gamb p * p.ψ))| * 1
  set kk1 := 1 - p.σ - gamb p + lamb p * (p.θ * p.m * p.σ) * p.σ
  set kk2 := -(p.θ * p.m * p.σ)
  set kk3 := -(lamb p * (p.θ * p.m * p.σ))
  set cg := |1| * (|kk1| * cc + |kk2| * cl) + |1| * (|kk3| * cy + |-1| * 1)
  have hcs : 0 ≤ cs := by positivity
  have hch : 0 ≤ ch := by positivity
  have hchz : 0 ≤ chz := by positivity
  have hcu : 0 ≤ cu := mul_nonneg (Sg_nonneg _) hchz
  have hcl : 0 ≤ cl := div_nonneg hcu (by linarith)
  have hcc : 0 ≤ cc := by positivity
  have hcy : 0 ≤ cy := by positivity
  have hcp : 0 ≤ cp := by positivity
  have hcg : 0 ≤ cg := by positivity
  set K := cs + ch + cu + cl + cc + cy + cp + cg
  refine ⟨K, by positivity, fun E r A hA hr => ?_⟩
  have hK : ∀ c, 0 ≤ c → c ≤ K → ∀ f, AdB E f c A → AdB E f K A := fun c _ hcK f hf =>
    hf.mono E hcK hA
  have Hs : AdB E (svA p r) cs A := by
    have := adb_lin2 E (hr 4) (adb_lin2 E (hr 0) (hr 2) 1 1) (cR4 p / Gw p) (-1 / Gw p)
    refine this.congr E fun t ω => ?_
    simp only [svA]; field_simp; ring
  have Hh : AdB E (hvA E p r) ch A := by
    have e1 := adb_lin2 E (adb_lin2 E (hr 3) (hr 4) 1 (p.θ * p.m * p.ω)) Hs 1
      (p.θ * p.m * (p.σ + p.ω))
    have e2 := adb_lin2 E (hr 1) (adb_Ms E (hr 1)) 1 (-p.β)
    refine (adb_lin2 E e1 e2 k1 (1 / p.ψ)).congr E fun t ω => ?_
    simp only [hvA, k1]; field_simp; ring
  have Hhz : AdB E (fun t ω => hvA E p r t ω / (p.β * z2R p)) chz A :=
    (adb_lin2 E Hh Hh (1 / (p.β * z2R p)) 0).congr E fun t ω => by ring
  obtain ⟨Hu, -⟩ := adb_fwd E (abs_inv_z2R hp hG) hchz hA Hhz
  have Hl : AdB E (lvA E p r) cl A := adb_bwd E hz10.le hz11 hcu hA Hu
  have Hc : AdB E (cvA E p r) cc A :=
    (adb_lin2 E Hl Hs (-aR p) 1).congr E fun t ω => by simp only [cvA]; ring
  have Hy : AdB E (yvA E p r) cy A :=
    (adb_lin2 E Hc (hr 4) 1 1).congr E fun t ω => by simp only [yvA]; ring
  have Hp : AdB E (pivA E p r) cp A :=
    (adb_lin2 E (adb_lin2 E Hl (adb_lag E (by positivity) Hl) 1 (-1)) (hr 1) (1 / gamb p)
      (-(1 / (gamb p * p.ψ)))).congr E fun t ω => by simp only [pivA]; field_simp; ring
  have Hg : AdB E (gvA E p r) cg A :=
    (adb_lin2 E (adb_lin2 E Hc Hl kk1 kk2) (adb_lin2 E Hy (hr 2) kk3 (-1)) 1 1).congr E
      fun t ω => by simp only [gvA, kk1, kk2, kk3]; ring
  exact ⟨hK _ hcu (by linarith) _ Hu, hK _ hcl (by linarith) _ Hl, hK _ hcc (by linarith) _ Hc,
    hK _ hcy (by linarith) _ Hy, hK _ hcp (by linarith) _ Hp, hK _ hcg (by linarith) _ Hg,
    hK _ hcs (by linarith) _ Hs, hK _ hch (by linarith) _ Hh⟩

/-! ## The inverse is an a.s. right inverse -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r` a.s.**): for every adapted, a.s. bounded
forcing on every filtered probability space. -/
theorem LRA_LinvRA (hp : p.Basic) (hG : 0 < Gw p) (r : ℕ → Ω → Fin 5 → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hr : RHyp E r A) (t : ℕ) : LRA E p (LinvRA E p r) t =ᵐ[E.μ] r t := by
  obtain ⟨c, hc, hb⟩ := adb_all hp hG
  obtain ⟨Hu, Hl, -, -, -, -, -, Hh⟩ := hb E r A hA hr
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := zR_props hp hG
  have hβ := hp.β_pos
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hz2 : 0 < p.β * z2R p := mul_pos hβ (by linarith)
  have hHz : AdB E (fun t ω => hvA E p r t ω / (p.β * z2R p)) (|1 / (p.β * z2R p)| * c + |0| * c)
      A := (adb_lin2 E Hh Hh (1 / (p.β * z2R p)) 0).congr E fun t ω => by ring
  obtain ⟨-, EU⟩ := adb_fwd E (abs_inv_z2R hp hG) (by positivity) hA hHz
  have EU' : ∀ s, uvA E p r s =ᵐ[E.μ] fun ω => 1 / z2R p * Ms E (uvA E p r) s ω +
      hvA E p r s ω / (p.β * z2R p) := EU
  have EL : ∀ s ω, lvA E p r s ω = z1R p * lagS (lvA E p r) s ω + uvA E p r s ω :=
    fun s ω => bwdS_eq _ _ s ω
  have EMU : Ms E (uvA E p r) t =ᵐ[E.μ] fun ω => Ms E (lvA E p r) t ω - z1R p * lvA E p r t ω := by
    have e : uvA E p r = fun s ω => 1 * lvA E p r s ω + -z1R p * lagS (lvA E p r) s ω := by
      funext s ω; rw [EL s ω]; ring
    rw [e]
    filter_upwards [Ms_lin2 E Hl (adb_lag E (by positivity) Hl) 1 (-z1R p) t, Ms_lag E Hl t]
      with ω h1 h2
    rw [h1, h2]; ring
  have key : ∀ᵐ ω ∂E.μ, (1 + p.β + cR p) * lvA E p r t ω - lagS (lvA E p r) t ω -
      p.β * Ms E (lvA E p r) t ω = hvA E p r t ω := by
    filter_upwards [EU' t, EMU] with ω h1 h2
    rw [h2] at h1
    have hux : uvA E p r t ω = lvA E p r t ω - z1R p * lagS (lvA E p r) t ω := by
      rw [EL t ω]; ring
    rw [hux] at h1
    have h3 : p.β * z2R p * (lvA E p r t ω - z1R p * lagS (lvA E p r) t ω) =
        p.β * (Ms E (lvA E p r) t ω - z1R p * lvA E p r t ω) + hvA E p r t ω := by
      rw [h1]; field_simp
    linear_combination h3 - (lvA E p r t ω) * hzs + (lagS (lvA E p r) t ω) * hzz
  have EMpi : Ms E (pivA E p r) t =ᵐ[E.μ] fun ω => (Ms E (lvA E p r) t ω - lvA E p r t ω) /
      gamb p - Ms E (fun s ω => r s ω 1) t ω / (gamb p * p.ψ) := by
    have e : pivA E p r = fun s ω => (1 / gamb p) * (1 * lvA E p r s ω +
        -1 * lagS (lvA E p r) s ω) + (-(1 / (gamb p * p.ψ))) * r s ω 1 := by
      funext s ω; simp only [pivA]; ring
    rw [e]
    filter_upwards [Ms_lin2 E (adb_lin2 E Hl (adb_lag E (by positivity) Hl) 1 (-1)) (hr 1)
      (1 / gamb p) (-(1 / (gamb p * p.ψ))) t,
      Ms_lin2 E Hl (adb_lag E (by positivity) Hl) 1 (-1) t, Ms_lag E Hl t] with ω h1 h2 h3
    rw [h1, h2, h3]; ring
  have hsv : ∀ ω, Gw p * svA p r t ω = cR4 p * r t ω 4 - r t ω 0 - r t ω 2 := fun ω => by
    unfold svA; field_simp
  have hGa := Gw_aR hG
  have hgA := gamb_aR hp hG
  filter_upwards [key, EMpi] with ω hk hMp
  have v0 : LinvRA E p r t ω 0 = yvA E p r t ω := rfl
  have v1 : LinvRA E p r t ω 1 = pivA E p r t ω := rfl
  have v2 : LinvRA E p r t ω 2 = cvA E p r t ω := rfl
  have v3 : LinvRA E p r t ω 3 = lvA E p r t ω := rfl
  have v4 : LinvRA E p r t ω 4 = gvA E p r t ω := rfl
  have l3 : lagvS (LinvRA E p r) t ω 3 = lagS (lvA E p r) t ω := rfl
  have m1 : MvA E (LinvRA E p r) t ω 1 = Ms E (pivA E p r) t ω := rfl
  have hcv : cvA E p r t ω = -(aR p * lvA E p r t ω) + svA p r t ω := rfl
  have hyv : yvA E p r t ω = cvA E p r t ω + r t ω 4 := rfl
  have hpv : pivA E p r t ω = (lvA E p r t ω - lagS (lvA E p r) t ω) / gamb p -
      r t ω 1 / (gamb p * p.ψ) := rfl
  have hhv : hvA E p r t ω = gamb p / p.ψ * (r t ω 3 + p.θ * p.m * p.ω * r t ω 4 +
      p.θ * p.m * (p.σ + p.ω) * svA p r t ω) +
      (r t ω 1 - p.β * Ms E (fun s ω => r s ω 1) t ω) / p.ψ := rfl
  funext i
  fin_cases i
  · have h02 := red_lam hp (lagvS (LinvRA E p r) t ω) (LinvRA E p r t ω)
    have hc2 : DQr p (lagvS (LinvRA E p r) t ω) (LinvRA E p r t ω) 2 = r t ω 2 := by
      simp only [DQr, Matrix.cons_val]
      rw [v0, v2, v3, v4]
      simp only [gvA]; ring
    simp only [LRA, Fin.zero_eta, Pi.add_apply, DNr, Matrix.cons_val_zero, add_zero]
    rw [v0, v2, v3, hc2] at h02
    have hyc : yvA E p r t ω - cvA E p r t ω = r t ω 4 := by rw [hyv]; ring
    rw [hyc, hcv] at h02
    have hsv' := hsv ω
    unfold cR4 at hsv'
    linear_combination h02 + (lvA E p r t ω) * hGa - hsv'
  · simp only [LRA, Fin.mk_one, Pi.add_apply, DNr, DQr, Matrix.cons_val_one,
      Matrix.cons_val_zero, add_zero]
    rw [l3, v1, v3, hpv]
    have hgb' := hgb.ne'
    have hψ' := hψ.ne'
    field_simp
    ring
  · simp only [LRA, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, add_zero]
    rw [v0, v2, v3, v4]
    simp only [gvA]; ring
  · simp only [LRA, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val]
    rw [m1, v0, v1, v2, hMp, hyv, hcv, hpv]
    rw [hhv, ← hgA] at hk
    have hgb' := hgb.ne'
    have hψ' := hψ.ne'
    field_simp at hk ⊢
    linear_combination hk
  · simp only [LRA, Fin.reduceFinMk, Pi.add_apply, DNr, DQr, Matrix.cons_val, add_zero]
    rw [v0, v2, hyv]; ring

/-! ## Injectivity on adapted processes -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**the a.s. a-priori bound with a predetermined
multiplier**): an adapted, a.s. bounded solution of the homogeneous linearised Rotemberg Ramsey
system with zero initial lag vanishes a.s. at every date. -/
theorem LRA_inj (hp : p.Basic) (hG : 0 < Gw p) (v : ℕ → Ω → Fin 5 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hv : RHyp E v B) (h0 : ∀ t, LRA E p v t =ᵐ[E.μ] 0) (t : ℕ) : v t =ᵐ[E.μ] 0 := by
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := zR_props hp hG
  have hβ := hp.β_pos
  have hψ := hp.ψ_pos
  have hgb := gamb_pos hp
  have hRk : ∀ s, ∀ᵐ ω ∂E.μ, ∀ k,
      (DQr p (lagvS v s ω) (v s ω) + DNr p (MvA E v s ω)) k = 0 := fun s => by
    filter_upwards [h0 s] with ω h k
    exact congrFun h k
  set c : Fin 5 → ℕ → Ω → ℝ := fun k s ω => v s ω k with hc
  have hl : ∀ s ω k, lagvS v s ω k = lagS (c k) s ω := fun _ _ _ => rfl
  have hm : ∀ s ω k, MvA E v s ω k = Ms E (c k) s ω := fun _ _ _ => rfl
  have hvx : ∀ s ω k, v s ω k = c k s ω := fun _ _ _ => rfl
  have e4 : ∀ s, ∀ᵐ ω ∂E.μ, c 0 s ω = c 2 s ω := fun s => by
    filter_upwards [hRk s] with ω h
    have := h 4
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val, add_zero] at this
    rw [hvx, hvx] at this; linarith
  have e1 : ∀ s, ∀ᵐ ω ∂E.μ, c 1 s ω = (c 3 s ω - lagS (c 3) s ω) / gamb p := fun s => by
    filter_upwards [hRk s] with ω h
    have := h 1
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val_one, Matrix.cons_val_zero,
      add_zero] at this
    rw [hl, hvx, hvx] at this
    field_simp
    have : p.ψ * (c 1 s ω * gamb p - (c 3 s ω - lagS (c 3) s ω)) = 0 := by
      linear_combination -this
    have := (mul_eq_zero.1 this).resolve_left hψ.ne'
    linarith
  have e02 : ∀ s, ∀ᵐ ω ∂E.μ, c 2 s ω = -(aR p * c 3 s ω) := fun s => by
    filter_upwards [hRk s, e4 s] with ω h h4
    have h02 := red_lam hp (lagvS v s ω) (v s ω)
    have c0 := h 0
    have c2 := h 2
    simp only [Pi.add_apply, DNr, Matrix.cons_val_zero, Matrix.cons_val, add_zero] at c0 c2
    rw [c0, c2, hvx, hvx, hvx, h4, sub_self, mul_zero, add_zero] at h02
    unfold aR
    field_simp
    linear_combination h02
  -- the forecast of inflation
  have hMv1 : ∀ s, Ms E (c 1) s =ᵐ[E.μ] fun ω => (Ms E (c 3) s ω - c 3 s ω) / gamb p := by
    intro s
    have hcongr : c 1 (s + 1) =ᵐ[E.μ]
        (fun ω => (1 / gamb p) * (1 * c 3 (s + 1) ω + -1 * lagS (c 3) (s + 1) ω)) := by
      filter_upwards [e1 (s + 1)] with ω h; rw [h]; ring
    have h1 : Ms E (c 1) s =ᵐ[E.μ] Ms E (fun s ω => (1 / gamb p) * (1 * c 3 s ω +
        -1 * lagS (c 3) s ω)) s := E.E_congr hcongr s
    filter_upwards [h1, Ms_lin2 E (adb_lin2 E (hv 3) (adb_lag E (by positivity) (hv 3)) 1 (-1))
      (hv 3) (1 / gamb p) 0 s, Ms_lin2 E (hv 3) (adb_lag E (by positivity) (hv 3)) 1 (-1) s,
      Ms_lag E (hv 3) s] with ω a1 a2 a3 a4
    have e5 : Ms E (fun s ω => (1 / gamb p) * (1 * c 3 s ω + -1 * lagS (c 3) s ω)) s ω =
        Ms E (fun s ω => (1 / gamb p) * (1 * c 3 s ω + -1 * lagS (c 3) s ω) + 0 * c 3 s ω) s ω :=
      by simp only [zero_mul, add_zero]
    rw [a1, e5, a2, a3, a4]; ring
  have key : ∀ s, ∀ᵐ ω ∂E.μ, (1 + p.β + cR p) * c 3 s ω - lagS (c 3) s ω -
      p.β * Ms E (c 3) s ω = 0 := fun s => by
    filter_upwards [hRk s, hMv1 s, e1 s, e4 s, e02 s] with ω h hM h1 h4 h02
    have c3 := h 3
    simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val] at c3
    rw [hm, hvx, hvx, hvx, hM, h1, h4, h02] at c3
    have hgA := gamb_aR hp hG
    rw [← hgA]
    have hgb' := hgb.ne'
    have hψ' := hψ.ne'
    field_simp at c3 ⊢
    linear_combination c3
  set U : ℕ → Ω → ℝ := fun s ω => c 3 s ω - z1R p * lagS (c 3) s ω with hU
  have hUb : AdB E U (|1| * 1 + |-z1R p| * 1) B :=
    (adb_lin2 E (hv 3) (adb_lag E (by positivity) (hv 3)) 1 (-z1R p)).congr E
      fun s ω => by simp only [hU]; ring
  have hU0 : ∀ s, U s =ᵐ[E.μ] 0 := by
    refine zero_of_eq_cMs E (abs_inv_z2R hp hG) (B := (|1| * 1 + |-z1R p| * 1) * B) hUb.2
      fun s => ?_
    have hMU : Ms E U s =ᵐ[E.μ] fun ω => Ms E (c 3) s ω - z1R p * c 3 s ω := by
      have e : U = fun s ω => 1 * c 3 s ω + -z1R p * lagS (c 3) s ω := by
        funext s ω; simp only [hU]; ring
      rw [e]
      filter_upwards [Ms_lin2 E (hv 3) (adb_lag E (by positivity) (hv 3)) 1 (-z1R p) s,
        Ms_lag E (hv 3) s] with ω a1 a2
      rw [a1, a2]; ring
    filter_upwards [hMU, key s] with ω a1 a2
    rw [a1]
    have hz2 : z2R p ≠ 0 := by linarith
    have hq : p.β * (z2R p * (c 3 s ω - z1R p * lagS (c 3) s ω) -
        (Ms E (c 3) s ω - z1R p * c 3 s ω)) = 0 := by
      linear_combination a2 + (c 3 s ω) * hzs - (lagS (c 3) s ω) * hzz
    have hq2 := (mul_eq_zero.1 hq).resolve_left hβ.ne'
    simp only [hU]
    field_simp
    linarith
  have hL0 : ∀ s, c 3 s =ᵐ[E.μ] 0 := zero_of_eq_lagS E (c := z1R p) fun s => by
    filter_upwards [hU0 s] with ω h
    simp only [hU, Pi.zero_apply] at h
    linarith
  have hlag0 : ∀ s, lagS (c 3) s =ᵐ[E.μ] 0 := lagS_zero E hL0
  filter_upwards [hL0 t, hlag0 t, e1 t, e4 t, e02 t, hRk t] with ω a3 al a1 a4 a02 h
  simp only [Pi.zero_apply] at a3 al
  have b2 : c 2 t ω = 0 := by rw [a02, a3, mul_zero, neg_zero]
  have b0 : c 0 t ω = 0 := by rw [a4, b2]
  have b1 : c 1 t ω = 0 := by rw [a1, a3, al]; simp
  have c2 := h 2
  simp only [Pi.add_apply, DQr, DNr, Matrix.cons_val, add_zero] at c2
  rw [hvx, hvx, hvx, hvx, b0, b2, a3] at c2
  have b4 : c 4 t ω = 0 := by linarith
  funext k
  fin_cases k
  exacts [b0, b1, b2, a3, b4]

/-! ## The uniform bound, linearity and the left inverse -/

/-- Sup-norm bounds from componentwise bounds. -/
theorem norm_of_rhyp {v : ℕ → Ω → Fin 5 → ℝ} {A : ℝ} (hA : 0 ≤ A) (hv : RHyp E v A) (t : ℕ) :
    ∀ᵐ ω ∂E.μ, ‖v t ω‖ ≤ A := by
  filter_upwards [ae_all_iff.2 fun k => (hv k).2 t] with ω h
  refine (pi_norm_le_iff_of_nonneg hA).2 fun k => ?_
  rw [Real.norm_eq_abs]; simpa using h k

/-- Woodford (2003), App. A.3: the linearised operator maps adapted bounded processes to adapted
bounded processes, `|(Lv)_t| ≤ ‖DLin‖·B`. -/
theorem rhyp_LRA {v : ℕ → Ω → Fin 5 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : RHyp E v B) :
    RHyp E (LRA E p v) (‖LinearMap.toContinuousLinearMap (DLin p)‖ * B) := by
  have hl : ∀ k, AdB E (fun t ω => lagvS v t ω k) 1 B := fun k =>
    adb_lag E (by positivity) (hv k)
  have hm : ∀ k, AdB E (fun t ω => MvA E v t ω k) 1 B := fun k => adb_Ms E (hv k)
  intro k
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hq : AEStronglyMeasurable[E.𝓕 t] (fun ω => (lagvS v t ω, v t ω, MvA E v t ω)) E.μ :=
      (aesmSub_vec fun i => (hl i).1 t).prodMk
        ((aesmSub_vec fun i => (hv i).1 t).prodMk (aesmSub_vec fun i => (hm i).1 t))
    have hc : Continuous fun q : (Fin 5 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ) => DLin p q k :=
      (continuous_apply k).comp (DLin p).continuous_of_finiteDimensional
    have e : (fun ω => LRA E p v t ω k) =
        fun ω => DLin p (lagvS v t ω, v t ω, MvA E v t ω) k := rfl
    change AEStronglyMeasurable[E.𝓕 t] (fun ω => LRA E p v t ω k) E.μ
    rw [e]
    exact hc.comp_aestronglyMeasurable hq
  · filter_upwards [norm_of_rhyp E hB hl t, norm_of_rhyp E hB hv t, norm_of_rhyp E hB hm t]
      with ω h1 h2 h3
    have := (norm_le_pi_norm (LRA E p v t ω) k).trans (norm_DLin_le p _ _ _ h1 h2 h3)
    rw [Real.norm_eq_abs] at this
    simpa using this

/-- Woodford (2003), App. A.3: the linearised operator is a.s. subtractive. -/
theorem LRA_sub {v w : ℕ → Ω → Fin 5 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : RHyp E v B) (hw : RHyp E w B) (t : ℕ) :
    LRA E p (fun s ω => v s ω - w s ω) t =ᵐ[E.μ] fun ω => LRA E p v t ω - LRA E p w t ω := by
  have hG : ∀ {u : ℕ → Ω → Fin 5 → ℝ}, RHyp E u B → Gd E u := fun hu s =>
    aesm_vec E fun k => (hu k).aesm E s
  filter_upwards [MvA_sub E (hG hv) (hG hw) (fun s => norm_of_rhyp E hB hv s)
    (fun s => norm_of_rhyp E hB hw s) t] with ω hm
  have hl : lagvS (fun s ω => v s ω - w s ω) t ω = lagvS v t ω - lagvS w t ω := by
    funext i; cases t <;> simp [lagvS, lagS]
  have e := (DLin p).map_sub (lagvS v t ω, v t ω, MvA E v t ω) (lagvS w t ω, w t ω, MvA E w t ω)
  simp only [DLin, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_sub_mk] at e
  simp only [LRA, hl, hm]
  exact e

/-- `RHyp` with a larger bound. -/
theorem rhyp_mono {v : ℕ → Ω → Fin 5 → ℝ} {A A' : ℝ} (hv : RHyp E v A) (h : A ≤ A') :
    RHyp E v A' := fun k =>
  ⟨(hv k).1, fun t => by filter_upwards [(hv k).2 t] with ω hω; linarith⟩

/-- Differences of `RHyp` processes. -/
theorem rhyp_sub {v w : ℕ → Ω → Fin 5 → ℝ} {A : ℝ} (hv : RHyp E v A) (hw : RHyp E w A) :
    RHyp E (fun t ω => v t ω - w t ω) (2 * A) := fun k => by
  have := (adb_lin2 E (hv k) (hw k) 1 (-1)).rescale E
  refine ⟨fun t => ?_, fun t => ?_⟩
  · exact ((hv k).1 t).sub ((hw k).1 t)
  · filter_upwards [this.2 t] with ω hω
    simp only [abs_one, abs_neg, one_mul, neg_mul, ← sub_eq_add_neg] at hω
    simp only [Pi.sub_apply]
    linarith

/-- The inverse of an `RHyp` forcing is `RHyp` with the uniform constant. -/
theorem rhyp_LinvRA (hp : p.Basic) (hG : 0 < Gw p) : ∃ K, 0 ≤ K ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 5 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → RHyp E (LinvRA E p r) (K * A) := by
  obtain ⟨c, hc, hb⟩ := adb_all hp hG
  refine ⟨c, hc, fun E r A hA hr k => ?_⟩
  obtain ⟨-, Hl, Hc, Hy, Hp, Hg, -, -⟩ := hb E r A hA hr
  fin_cases k
  · exact (Hy.congr E fun t ω => rfl).rescale E
  · exact (Hp.congr E fun t ω => rfl).rescale E
  · exact (Hc.congr E fun t ω => rfl).rescale E
  · exact (Hl.congr E fun t ω => rfl).rescale E
  · exact (Hg.congr E fun t ω => rfl).rescale E

/-- Woodford (2003), App. A.3 (**the left inverse a.s.**): `L⁻¹(Lv) = v` a.s. for adapted,
a.s. bounded `v`. -/
theorem LinvRA_LRA {p : Par} (hp : p.Basic) (hG : 0 < Gw p)
    {v : ℕ → Ω → Fin 5 → ℝ} {B : ℝ} (hB : 0 ≤ B) (hv : RHyp E v B) (t : ℕ) :
    LinvRA E p (LRA E p v) t =ᵐ[E.μ] v t := by
  obtain ⟨K, hK, hKr⟩ := rhyp_LinvRA hp hG
  set CL := ‖LinearMap.toContinuousLinearMap (DLin p)‖
  have hL := rhyp_LRA E (p := p) hB hv
  have hw := hKr E _ _ (by positivity) hL
  set M := B + K * (CL * B)
  have hKC : 0 ≤ K * (CL * B) := by positivity
  have hvM := rhyp_mono E hv (show B ≤ M by linarith)
  have hwM := rhyp_mono E hw (show K * (CL * B) ≤ M by linarith)
  have hd := rhyp_sub E hvM hwM
  have hz := LRA_inj E hp hG (fun s ω => v s ω - LinvRA E p (LRA E p v) s ω) (2 * M)
    (by positivity) hd (fun s => by
      filter_upwards [LRA_sub E (by positivity) hvM hwM s,
        LRA_LinvRA E hp hG (LRA E p v) _ (by positivity) hL s] with ω h1 h2
      rw [h1, h2, sub_self]; rfl) t
  filter_upwards [hz] with ω h
  exact (sub_eq_zero.1 (by simpa using h)).symm

/-- Woodford (2003), App. A.3: the inverse is a.s. subtractive. -/
theorem LinvRA_sub {p : Par} (hp : p.Basic) (hG : 0 < Gw p)
    {r r' : ℕ → Ω → Fin 5 → ℝ} {A : ℝ} (hA : 0 ≤ A) (hr : RHyp E r A) (hr' : RHyp E r' A)
    (t : ℕ) : LinvRA E p (fun s ω => r s ω - r' s ω) t =ᵐ[E.μ]
      fun ω => LinvRA E p r t ω - LinvRA E p r' t ω := by
  obtain ⟨K, hK, hKr⟩ := rhyp_LinvRA hp hG
  have hrd := rhyp_sub E hr hr'
  have w1 := hKr E _ _ (by positivity) hrd
  have w2 := hKr E _ _ hA hr
  have w3 := hKr E _ _ hA hr'
  set M := K * (2 * A) + K * A
  have hKA : 0 ≤ K * A := by positivity
  have hK2A : 0 ≤ K * (2 * A) := by positivity
  have h1M := rhyp_mono E w1 (show K * (2 * A) ≤ M by linarith)
  have h2M := rhyp_mono E w2 (show K * A ≤ M by linarith)
  have h3M := rhyp_mono E w3 (show K * A ≤ M by linarith)
  have h23 := rhyp_sub E h2M h3M
  have h1M' := rhyp_mono E h1M (show M ≤ 2 * M by linarith)
  have hz := LRA_inj E hp hG (fun s ω => LinvRA E p (fun s ω => r s ω - r' s ω) s ω -
    (LinvRA E p r s ω - LinvRA E p r' s ω)) (2 * (2 * M)) (by positivity)
    (rhyp_sub E h1M' h23) (fun s => by
      filter_upwards [LRA_sub E (by positivity) h1M' h23 s, LRA_sub E (by positivity) h2M
        h3M s, LRA_LinvRA E hp hG _ _ (by positivity) hrd s,
        LRA_LinvRA E hp hG _ _ hA hr s, LRA_LinvRA E hp hG _ _ hA hr' s] with ω e1 e2 e3 e4 e5
      rw [e1, e2, e3, e4, e5]
      simp) t
  filter_upwards [hz] with ω h
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.1 h

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyAE
