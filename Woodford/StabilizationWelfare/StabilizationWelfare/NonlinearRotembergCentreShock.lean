/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergCentre

/-!
# The linear Taylor rule on the boundary: small constant interest-rate disturbances

Woodford (2003), *Interest and Prices*, Chapter 4, Proposition 4.3 (p. 254) and Appendix A.3, for
the exact Rotemberg model under the linear boundary rule with a CONSTANT interest-rate disturbance
`ν` (`1 + i_t = β⁻¹Π_t^{φ_π}(Y_t/Ȳ)^{φ_y}e^{ν}`), under perfect foresight. With `s = sign S`
(`NonlinearRotembergCentre`):

* **`shock_nonexist`**: there are `δ > 0` and `ν₀ > 0` such that for every `ν` with
  `0 < sν < ν₀` NO exact equilibrium stays within `δ` of the zero-inflation steady state at every
  date (the centre coordinate drifts by at least `sν/2` per period).
* **`shock_steady`**: for every `r > 0` there is `ν₀ > 0` such that for every `ν` with
  `0 < −sν < ν₀` there are two exact steady-state equilibria within `r` of the zero-inflation
  steady state, one with `π > 0` and one with `π < 0` (the double root splits).

So small-disturbance equilibria near the steady state exist for one sign of `ν` and fail to
exist for the other; in particular no equilibrium selection is continuous in `ν` at `ν = 0`
from both sides. Steady states with disturbance `ν` are exactly the `π` with `ν_s(π) = ν`,
`ν_s(π) = (1 − φ_π)π − φ_yŷ_s(π)` (`nus`, `steady_eq`), `ν_s′(0) = 0`,
`ν_s″(0) = −φ_yψS/((θm)²(σ + ω))` (`J_nus`).
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergCentreShock

open Filter Topology
open NonlinearRotemberg NonlinearRotembergJets NonlinearRotembergCentreLocal
open NonlinearRotembergCentreSecond NonlinearRotembergCentreTools NonlinearRotembergCentre
open NonlinearRotembergLinks (wedge)
open NonlinearRotembergBoundary (ssY sss corner_steady)
open NonlinearRotembergBoundaryPair (Lf kc corner corner_basic)
open NonlinearRotembergTrendWelfare (KR J_YR)

variable {p : Par}

/-! ## No equilibrium for one sign of the disturbance -/

set_option maxHeartbeats 1000000 in
-- the drift estimate
/-- Woodford (2003), Prop. 4.3 and App. A.3 (**no small-disturbance equilibrium on one side**):
with `s = ±1` and `sq > 0`, there are `δ > 0` and `ν₀ > 0` such that for every constant
disturbance with `0 < sν < ν₀`, no exact perfect-foresight equilibrium has `‖x_t‖ ≤ δ` at every
date. -/
theorem shock_nonexist (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) {s : ℝ}
    (hs : s = 1 ∨ s = -1) (hsq : 0 < s * qc p) :
    ∃ δ > 0, ∃ ν0 > 0, ∀ ν, 0 < s * ν → s * ν < ν0 → ∀ z : ℕ → Fin 3 → ℝ, PFEq p ν z →
      ¬ ∀ t, ‖z t‖ ≤ δ := by
  obtain ⟨δ1, hδ1, Λ, hΛ, K, hK, M, hM, η, hη, C, hC, hΛ1, hCΛ, h1, h2, -, -, hest⟩ :=
    setup hp hb hs hsq
  obtain ⟨ρ', hρ', K', hK', hLV⟩ := LV_le_norm hp
  have has := abs_s hs
  have hss := s_sq hs
  set A := C * M * (1 + 2 * Λ) with hA
  have hA0 : 0 ≤ A := by positivity
  set δ := min (min δ1 (ρ' / 2)) (1 / (4 * (A + 1) * K')) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hδ1 (by positivity)) (by positivity)
  refine ⟨δ, hδ0, 1 / (4 * (C * M ^ 2 + 1)), by positivity, fun ν hν hνs z hz hzb => ?_⟩
  have hzδ : ∀ t, ‖z t‖ ≤ δ1 := fun t =>
    (hzb t).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hzρ : ∀ t, ‖z t‖ < ρ' := fun t => by
    have := (hzb t).trans ((min_le_left _ _).trans (min_le_right _ _)); linarith
  have hres : ∀ t, Res p (z t) := fun t => (pf_components hz t).2.2
  set L : ℕ → ℝ := fun t => Lf p (z t) with hLdef
  set V : ℕ → ℝ := fun t => Vf p (z t) with hVdef
  have hrec := fun t => exact_rec hp hz t
  have hE := fun t => (hest (z t) (hzδ t) (hres t))
  have hVb : ∀ t, |V t| ≤ K' * δ := fun t =>
    ((hLV (z t) (hzρ t)).2).trans (mul_le_mul_of_nonneg_left (hzb t) hK'.le)
  have hLb : ∀ t, |L t| ≤ K' * δ := fun t =>
    ((hLV (z t) (hzρ t)).1).trans (mul_le_mul_of_nonneg_left (hzb t) hK'.le)
  have hνabs : |ν| = s * ν := by
    have : |s * ν| = |ν| := by rw [abs_mul, has, one_mul]
    rw [← this, abs_of_pos hν]
  have hcone : ∀ t, |V t| ≤ Λ * |L t| + M * |ν| := fun t =>
    cone_bound (c := p.ψ * Th p) (L := L) (V := V)
      (D := fun t => Dfun p (z t)) (E := fun t => Efun p (z t)) (one_lt_mu hp) hΛ hM hη h1 h2
      (fun t => by simp only [hLdef]; rw [(hrec t).1])
      (fun t => by simp only [hVdef]; rw [(hrec t).2])
      (fun t => (hE t).1) (fun t => (hE t).2.1) hVb t
  have hKδ : A * (K' * δ) ≤ 1 / 4 := by
    have h' : δ ≤ 1 / (4 * (A + 1) * K') := min_le_right _ _
    calc A * (K' * δ) ≤ (A + 1) * K' * δ := by nlinarith [mul_nonneg hK'.le hδ0.le]
      _ ≤ (A + 1) * K' * (1 / (4 * (A + 1) * K')) := by gcongr
      _ = 1 / 4 := by field_simp
  have hνM : C * M ^ 2 * |ν| ≤ 1 / 4 := by
    rw [hνabs]
    have h' : s * ν < 1 / (4 * (C * M ^ 2 + 1)) := hνs
    rw [lt_div_iff₀ (by positivity)] at h'
    nlinarith [mul_nonneg hC (sq_nonneg M)]
  -- the drift of `sL`
  have hdrift : ∀ t, s * L t + s * ν / 2 ≤ s * L (t + 1) := by
    intro t
    have hq := (hE t).2.2.1
    have hc := hcone t
    have hLt := hLb t
    have hb1 : C * |V t| * (|L t| + |V t|) ≤
        C * (Λ * |L t| + M * |ν|) * ((1 + Λ) * |L t| + M * |ν|) := by
      have : |L t| + |V t| ≤ (1 + Λ) * |L t| + M * |ν| := by linarith
      gcongr
    have hb2 : C * (Λ * |L t| + M * |ν|) * ((1 + Λ) * |L t| + M * |ν|) =
        C * Λ * (1 + Λ) * L t ^ 2 + A * |ν| * |L t| + C * M ^ 2 * |ν| * |ν| := by
      rw [← sq_abs (L t), hA]; ring
    have hb3 : C * Λ * (1 + Λ) * L t ^ 2 ≤ s * qc p / 4 * L t ^ 2 :=
      mul_le_mul_of_nonneg_right hCΛ (sq_nonneg _)
    have hb4 : A * |ν| * |L t| ≤ |ν| / 4 := by
      have := mul_le_mul_of_nonneg_left hLt (mul_nonneg hA0 (abs_nonneg ν))
      nlinarith [abs_nonneg ν]
    have hb5 : C * M ^ 2 * |ν| * |ν| ≤ |ν| / 4 := by
      have := mul_le_mul_of_nonneg_right hνM (abs_nonneg ν); linarith
    have hsL : s * L (t + 1) = s * L t + s * Dfun p (z t) + s * ν := by
      simp only [hLdef]; rw [(hrec t).1]; ring
    have : 0 ≤ s * qc p / 2 * L t ^ 2 := by positivity
    rw [hsL, ← hνabs]
    nlinarith
  have hsLb : ∀ t, |s * L t| ≤ K' * δ := fun t => by rw [abs_mul, has, one_mul]; exact hLb t
  exact centre_drift_unbounded (L := fun t => s * L t) (by linarith) hdrift hsLb

/-! ## Steady states for the other sign -/

/-- Woodford (2003), Ch. 4 (2.7) and Ch. 3 fn. 44: the disturbance that makes inflation `π` a
steady state, `ν_s(π) = (1 − φ_π)π − φ_yŷ_s(π)`. -/
noncomputable def nus (p : Par) (π : ℝ) : ℝ := (1 - p.φ) * π - p.φy * ssY p π

/-- Woodford (2003), Ch. 4 (2.7) (**every steady state of the pricing block is an equilibrium for
its own disturbance**): if `C/Y > 0` and `1 + (1−β)ψ(e^π − 1)e^π/(θm) > 0` at `π`, the constant
path at `sss π` is an exact perfect-foresight equilibrium with the disturbance `ν = ν_s(π)`. -/
theorem steady_eq (hp : p.Basic) (π : ℝ) (hw : 0 < wedge p.ψ π)
    (hk : 0 < 1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m)) :
    PFEq p (nus p π) (fun _ => sss p π) := by
  have hc := corner_steady (corner_basic hp) rfl rfl π hw hk
  have h1 := congrFun hc 1
  simp only [Qmap, Nmap, Pi.add_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
    Pi.zero_apply] at h1
  have h1' : Gadj p (sss p π) - Hmc p 0 (sss p π) + -(p.β * Gadj p (sss p π)) = 0 := h1
  refine pf_of_rec (fun _ => ?_) (fun _ => ?_) (fun _ => by linarith)
  · simp only [Res, Qmap, sss, Matrix.cons_val]
    rw [Real.exp_add, Real.exp_log hw]; simp only [wedge]; ring
  · simp only [sss, nus, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring

/-- Woodford (2003), Ch. 4 (2.7) (**the double root, as a jet**): on the boundary `ν_s′(0) = 0`
and `ν_s″(0) = −φ_y(3K − K² + σψ)/(σ + ω)`, `K = (1−β)ψ/(θm)`. -/
theorem J_nus (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0) :
    J2 (nus p) 0 (-(p.φy * ((3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω)))) := by
  have hbT := boundary_Th hp hb
  have hT := (Th_pos hp).ne'
  have hθm : p.θ * p.m ≠ 0 := (mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos).ne'
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  refine J2_eq (J2_sub (J2_const_mul (1 - p.φ) J2_id) (J2_const_mul p.φy (J_YR hp))) ?_ (by ring)
  have e : KR p / (p.σ + p.ω) = (1 - p.β) * p.ψ / Th p := by
    unfold KR Th; field_simp
  rw [e]
  field_simp
  linear_combination (-1) * hbT

/-- Woodford (2003), App. A.3: `ν_s″(0) = −φ_yψS/((θm)²(σ + ω))`. -/
theorem nus2_eq (hp : p.Basic) :
    -(p.φy * ((3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω))) =
      -(p.φy * p.ψ * Sc p / ((p.θ * p.m) ^ 2 * (p.σ + p.ω))) := by
  have hθ : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hm : p.m ≠ 0 := hp.m_pos.ne'
  have hs : p.σ + p.ω ≠ 0 := by linarith [hp.σ_pos, hp.ω_nonneg]
  unfold KR Sc
  field_simp
  ring

set_option maxHeartbeats 1000000 in
-- the intermediate-value arguments on both sides
/-- Woodford (2003), Prop. 4.3 and Ch. 4 (2.7) (**small-disturbance equilibria for the other
sign**): with `φ_y > 0`, `s = ±1` and `sS > 0`, for every `r > 0` there is `ν₀ > 0` such that for
every constant disturbance with `0 < −sν < ν₀` there are two exact steady-state equilibria within
`r` of the zero-inflation steady state, with inflation `π₊ > 0` and `π₋ < 0`. -/
theorem shock_steady (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (hφy : 0 < p.φy) {s : ℝ} (hs : s = 1 ∨ s = -1) (hsS : 0 < s * Sc p) :
    ∀ r > 0, ∃ ν0 > 0, ∀ ν, 0 < -(s * ν) → -(s * ν) < ν0 → ∃ πp πm : ℝ, 0 < πp ∧ πm < 0 ∧
      PFEq p ν (fun _ => sss p πp) ∧ PFEq p ν (fun _ => sss p πm) ∧
      ‖sss p πp‖ ≤ r ∧ ‖sss p πm‖ ≤ r := by
  intro r hr
  have has := abs_s hs
  have hss := s_sq hs
  have hθm : 0 < p.θ * p.m := mul_pos (by linarith [hp.one_lt_θ]) hp.m_pos
  have hsω : 0 < p.σ + p.ω := by linarith [hp.σ_pos, hp.ω_nonneg]
  set n2 := -(p.φy * ((3 * KR p - KR p ^ 2 + p.σ * p.ψ) / (p.σ + p.ω))) with hn2
  have hsn2 : s * n2 < 0 := by
    rw [hn2, nus2_eq hp]
    have : 0 < p.φy * p.ψ / ((p.θ * p.m) ^ 2 * (p.σ + p.ω)) := by have := hp.ψ_pos; positivity
    have e : s * -(p.φy * p.ψ * Sc p / ((p.θ * p.m) ^ 2 * (p.σ + p.ω))) =
        -(p.φy * p.ψ / ((p.θ * p.m) ^ 2 * (p.σ + p.ω)) * (s * Sc p)) := by ring
    rw [e]; nlinarith
  set a := -(s * n2) / 4 with ha
  have ha0 : 0 < a := by linarith
  have hnus0 : nus p 0 = 0 := by simp [nus, ssY, wedge]
  obtain ⟨ρ1, hρ1, hpe⟩ := peano2 (J_nus hp hb) hnus0 ha0
  -- continuity and the positivity conditions near zero
  have hwc : Continuous (wedge p.ψ) := by unfold wedge; fun_prop
  have hkc : Continuous fun π : ℝ =>
      1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m) := by fun_prop
  have hev : ∀ᶠ π in 𝓝 (0 : ℝ), 0 < wedge p.ψ π ∧
      0 < 1 + (1 - p.β) * p.ψ * ((Real.exp π - 1) * Real.exp π) / (p.θ * p.m) :=
    (hwc.continuousAt.eventually (lt_mem_nhds (by simp [wedge]))).and
      (hkc.continuousAt.eventually (lt_mem_nhds (by simp)))
  have hsssc : ContinuousAt (sss p) 0 := by
    have h1 : ContinuousAt (ssY p) 0 := by
      unfold ssY
      refine ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) _
      · exact (hkc.continuousAt).log (by simp)
      · exact (hwc.continuousAt.log (by simp [wedge])).const_mul _
    refine continuousAt_pi.2 fun i => ?_
    fin_cases i
    · exact h1
    · exact continuousAt_id
    · exact h1.add (hwc.continuousAt.log (by simp [wedge]))
  have hsss0 : sss p 0 = 0 := NonlinearRotembergBoundary.sss_zero
  have hev2 : ∀ᶠ π in 𝓝 (0 : ℝ), ‖sss p π‖ ≤ r := by
    have := hsssc.tendsto; rw [hsss0] at this
    exact (this.eventually (Metric.closedBall_mem_nhds 0 hr)).mono fun π h => by
      simpa using h
  obtain ⟨ρ2, hρ2, hball⟩ := Metric.eventually_nhds_iff.1 (hev.and hev2)
  set π1 := min ρ1 ρ2 / 2 with hπ1
  have hπ10 : 0 < π1 := by positivity
  have hπ1ρ : ∀ π, |π| ≤ π1 → |π| < ρ1 ∧ dist π 0 < ρ2 := fun π hπ => by
    have := min_le_left ρ1 ρ2; have := min_le_right ρ1 ρ2
    refine ⟨by linarith, by rw [Real.dist_eq, sub_zero]; linarith⟩
  -- the bounds `−3a π² ≤ sν_s(π) ≤ −aπ²` for `|π| ≤ π₁`
  have hsn : ∀ π, |π| ≤ π1 → s * nus p π ≤ -(a * π ^ 2) := fun π hπ => by
    have h := hpe π (hπ1ρ π hπ).1
    have h' : |s * nus p π - s * n2 / 2 * π ^ 2| ≤ a * π ^ 2 := by
      have e : s * nus p π - s * n2 / 2 * π ^ 2 = s * (nus p π - n2 / 2 * π ^ 2) := by ring
      rw [e, abs_mul, has, one_mul]; exact h
    have e2 : s * n2 / 2 * π ^ 2 = -(2 * a) * π ^ 2 := by rw [ha]; ring
    rw [e2] at h'
    have := le_abs_self (s * nus p π - -(2 * a) * π ^ 2)
    nlinarith
  refine ⟨a * π1 ^ 2, by positivity, fun ν hν hνs => ?_⟩
  have hcont : ContinuousOn (fun π => s * nus p π) (Set.Icc (-π1) π1) := by
    have h1 : ContinuousOn (ssY p) (Set.Icc (-π1) π1) := by
      intro π hπ
      have hπ' : |π| ≤ π1 := abs_le.2 hπ
      have hpos := hball (hπ1ρ π hπ').2
      unfold ssY
      refine ContinuousAt.continuousWithinAt (ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) _)
      · exact (hkc.continuousAt).log hpos.1.2.ne'
      · exact (hwc.continuousAt.log hpos.1.1.ne').const_mul _
    exact (continuousOn_const.mul ((continuousOn_const.mul continuousOn_id).sub
      (continuousOn_const.mul h1)))
  have hend : s * nus p π1 < s * ν := by
    have := hsn π1 (by rw [abs_of_pos hπ10])
    linarith
  have hend' : s * nus p (-π1) < s * ν := by
    have := hsn (-π1) (by rw [abs_neg, abs_of_pos hπ10])
    have e : (-π1) ^ 2 = π1 ^ 2 := by ring
    rw [e] at this; linarith
  have hmid : s * ν < s * nus p 0 := by rw [hnus0, mul_zero]; linarith
  -- the intermediate value theorem on `[0, π₁]` and `[−π₁, 0]`
  obtain ⟨πp, hπpI, hπp⟩ := intermediate_value_Icc' hπ10.le
    (hcont.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩) ⟨hend.le, hmid.le⟩
  obtain ⟨πm, hπmI, hπm⟩ := intermediate_value_Icc (by linarith : -π1 ≤ 0)
    (hcont.mono fun x hx => ⟨hx.1, by linarith [hx.2]⟩) ⟨hend'.le, hmid.le⟩
  simp only at hπp hπm
  have hnz : ∀ π, s * nus p π = s * ν → nus p π = ν := fun π h => by
    have := congrArg (fun x => s * x) h
    simp only [← mul_assoc, hss, one_mul] at this
    exact this
  have hp0 : πp ≠ 0 := by
    intro h; rw [h, hnus0, mul_zero] at hπp; linarith
  have hm0 : πm ≠ 0 := by
    intro h; rw [h, hnus0, mul_zero] at hπm; linarith
  have hπpa : |πp| ≤ π1 := abs_le.2 ⟨by linarith [hπpI.1], hπpI.2⟩
  have hπma : |πm| ≤ π1 := abs_le.2 ⟨hπmI.1, by linarith [hπmI.2]⟩
  have hbp := hball (hπ1ρ πp hπpa).2
  have hbm := hball (hπ1ρ πm hπma).2
  refine ⟨πp, πm, lt_of_le_of_ne hπpI.1 (Ne.symm hp0), lt_of_le_of_ne hπmI.2 hm0, ?_, ?_,
    hbp.2, hbm.2⟩
  · have := steady_eq hp πp hbp.1.1 hbp.1.2
    rwa [hnz πp hπp] at this
  · have := steady_eq hp πm hbm.1.1 hbm.1.2
    rwa [hnz πm hπm] at this

/-- Woodford (2003), App. A.3: `PFEq p 0` is the perfect-foresight equilibrium notion of
`NonlinearRotembergIndet`
(`Q(0, x_t) + N(0, x_{t+1}) = 0`). -/
theorem pfeq_zero_iff (z : ℕ → Fin 3 → ℝ) :
    PFEq p 0 z ↔ ∀ t, Qmap p (0, z t) + Nmap p (0, z (t + 1)) = 0 := by
  have e : ev 0 = 0 := by funext i; fin_cases i <;> simp [ev]
  simp only [PFEq, e]

/-- Woodford (2003), Prop. 4.3 and Ch. 4 (2.7) (**small disturbances, `S > 0`**): with `φ_y > 0`
on the boundary, if `S > 0` then (1) for some `δ, ν₀ > 0` no exact equilibrium stays within `δ`
of the steady state when `0 < ν < ν₀` (a small contractionary interest-rate disturbance), and
(2) for every `r > 0` and every small `ν < 0` there are two steady-state equilibria within `r`,
one inflationary and one deflationary. -/
theorem shock_pos (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (hφy : 0 < p.φy) (hS : 0 < Sc p) :
    (∃ δ > 0, ∃ ν0 > 0, ∀ ν, 0 < ν → ν < ν0 → ∀ z : ℕ → Fin 3 → ℝ, PFEq p ν z →
      ¬ ∀ t, ‖z t‖ ≤ δ) ∧
    ∀ r > 0, ∃ ν0 > 0, ∀ ν, ν < 0 → -ν < ν0 → ∃ πp πm : ℝ, 0 < πp ∧ πm < 0 ∧
      PFEq p ν (fun _ => sss p πp) ∧ PFEq p ν (fun _ => sss p πm) ∧
      ‖sss p πp‖ ≤ r ∧ ‖sss p πm‖ ≤ r := by
  have hs : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1 := Or.inl rfl
  have hsq : 0 < 1 * qc p := by rw [one_mul]; exact ((q_pos_iff hp hφy).1).2 hS
  refine ⟨?_, fun r hr => ?_⟩
  · obtain ⟨δ, hδ, ν0, hν0, h⟩ := shock_nonexist hp hb hs hsq
    exact ⟨δ, hδ, ν0, hν0, fun ν h1 h2 => h ν (by linarith) (by linarith)⟩
  · obtain ⟨ν0, hν0, h⟩ := shock_steady hp hb hφy hs (by linarith) r hr
    exact ⟨ν0, hν0, fun ν h1 h2 => h ν (by linarith) (by linarith)⟩

/-- Woodford (2003), Prop. 4.3 and Ch. 4 (2.7) (**small disturbances, `S < 0`**): the mirror
image of `shock_pos`: no equilibrium near the steady state for small `ν < 0`, two steady-state
equilibria (`π > 0` and `π < 0`) for small `ν > 0`. -/
theorem shock_neg (hp : p.Basic) (hb : p.κ * (p.φ - 1) + (1 - p.β) * p.φy = 0)
    (hφy : 0 < p.φy) (hS : Sc p < 0) :
    (∃ δ > 0, ∃ ν0 > 0, ∀ ν, ν < 0 → -ν < ν0 → ∀ z : ℕ → Fin 3 → ℝ, PFEq p ν z →
      ¬ ∀ t, ‖z t‖ ≤ δ) ∧
    ∀ r > 0, ∃ ν0 > 0, ∀ ν, 0 < ν → ν < ν0 → ∃ πp πm : ℝ, 0 < πp ∧ πm < 0 ∧
      PFEq p ν (fun _ => sss p πp) ∧ PFEq p ν (fun _ => sss p πm) ∧
      ‖sss p πp‖ ≤ r ∧ ‖sss p πm‖ ≤ r := by
  have hs : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  have hsq : 0 < -1 * qc p := by have := ((q_pos_iff hp hφy).2).2 hS; linarith
  refine ⟨?_, fun r hr => ?_⟩
  · obtain ⟨δ, hδ, ν0, hν0, h⟩ := shock_nonexist hp hb hs hsq
    exact ⟨δ, hδ, ν0, hν0, fun ν h1 h2 => h ν (by linarith) (by linarith)⟩
  · obtain ⟨ν0, hν0, h⟩ := shock_steady hp hb hφy hs (by linarith) r hr
    exact ⟨ν0, hν0, fun ν h1 h2 => h ν (by linarith) (by linarith)⟩

end Woodford.StabilizationWelfare.NonlinearRotembergCentreShock
