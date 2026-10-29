/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.BridgeExtensions
import StabilizationWelfare.TidyR5CommitLQ

/-!
# The first-order limit of the second-order aggregate-supply relation (5.4)

Woodford (2003), *Interest and Prices*, Chapter 6, §5, eqs. (5.4) and (5.11), pp. 457–461
(Benigno–Woodford), and footnote 71.

`TidyR5RamseySOC.lq_sufficiency615` compares a feasible family `B` with the commitment family
through the first-order components of `B`, and assumed that they satisfy the LINEAR AS relation
`π = κx + βE_tπ′ + u`. Here this is DERIVED: for ANY family of exact Calvo equilibria
(`LargeDistortions.CalvoModel.CalvoAS` for every amplitude) whose variables are of first order
uniformly in date and state, and whose inflation, output and disturbances have first-order
components (`X − εX₁ = O(ε²)`), the first-order components satisfy the linearised AS relation
with Woodford's natural rate (`first_order_AS`) and hence, in the welfare-relevant gap, the AS
relation with the cost-push term (5.11) (`first_order_NKPCu`).

The proof takes the exact one-period second-order AS relation
(`LargeDistortions.second_order_AS`) and its expansion in output and disturbances
(`LargeDistortions.as_expand`): `π − κ(Ŷ − Ŷⁿ) − βE_tπ′` equals a sum of quadratic terms and the
weight-three remainder (`as_residual`), hence is `O(ε²)` uniformly; dividing by `ε`
(`zero_of_uniform`) gives the relation between first-order components.
-/

namespace Woodford.StabilizationWelfare.TidyR6aAS

open Filter Topology Asymptotics
open BridgeExtensions

variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

/-- Woodford (2003), (5.4): the natural rate is linear in the disturbances. -/
theorem YnA_sub_mul (ω σ sC c G cb q muw tau G1 cb1 q1 muw1 tau1 : ℝ) :
    LargeDistortions.YnA ω σ sC (G - c * G1) (cb - c * cb1) (q - c * q1) (muw - c * muw1)
        (tau - c * tau1) =
      LargeDistortions.YnA ω σ sC G cb q muw tau -
        c * LargeDistortions.YnA ω σ sC G1 cb1 q1 muw1 tau1 := by
  unfold LargeDistortions.YnA
  ring

/-- Woodford (2003), (5.4) (**the AS residual as quadratic terms plus the weight-three
remainder**): along an exact Calvo equilibrium,
`π_t − κ(Ŷ_t − Ŷⁿ_t) − βE_tπ_{t+1} = −Q_t + βE_tQ_{t+1} + (μ_y/2)Ŷ_t² − δ_tŶ_t + tip_t
 + (βθ(1+ω)/2)E_tπ_{t+1}² + remAS_t` with `Q = (θ−1)π²/(2(1−α)) + π(K̂ + F̂)/2`. -/
theorem as_residual {α β θ ω σ sC : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ : θ ≠ 1)
    (hν : 1 + ω * θ ≠ 0) (hs : sC ≠ 0) (hc : ω + σ ≠ 0)
    {infl xr F K f k Y G cb q muw tau : ℕ → Ω → ℝ}
    (hM : LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb q muw tau)
    (t : ℕ) (z : Ω) :
    infl t z - Moments.calvoKappa α β ω θ σ *
        (Y t z - LargeDistortions.YnA ω σ sC (G t z) (cb t z) (q t z) (muw t z) (tau t z)) -
        β * 𝔼.E t (infl (t + 1)) z =
      -((θ - 1) / (2 * (1 - α)) * infl t z ^ 2 + infl t z * ((K t z + F t z) / 2)) +
        β * 𝔼.E t (fun z' => (θ - 1) / (2 * (1 - α)) * infl (t + 1) z' ^ 2 +
          infl (t + 1) z' * ((K (t + 1) z' + F (t + 1) z') / 2)) z +
        (LargeDistortions.muY α β θ ω σ sC / 2 * Y t z ^ 2 -
          LargeDistortions.deltaA α β θ ω σ sC (G t z) (cb t z) (q t z) (muw t z) (tau t z) *
            Y t z +
          LargeDistortions.tipASA α β θ ω σ sC (G t z) (cb t z) (q t z) (muw t z) (tau t z)) +
        β * (θ * (1 + ω)) / 2 * 𝔼.E t (fun z' => infl (t + 1) z' ^ 2) z +
        LargeDistortions.remAS 𝔼 α β θ ω σ sC infl xr F K f k Y G cb tau t z := by
  have h1 := congrFun (LargeDistortions.second_order_AS 𝔼 hα0 hα1 hθ hν hM.priceIndex
    hM.resetPrice hM.recF hM.recK t) z
  have h2 := LargeDistortions.as_expand (α := α) (β := β) (θ := θ) hs hc (Y t z) (G t z)
    (cb t z) (q t z) (muw t z) (tau t z)
  have hV : LargeDistortions.Vp α θ infl F K (t + 1) = infl (t + 1) + fun z' =>
      (θ - 1) / (2 * (1 - α)) * infl (t + 1) z' ^ 2 +
        infl (t + 1) z' * ((K (t + 1) z' + F (t + 1) z') / 2) := by
    funext z'
    simp only [LargeDistortions.Vp, LargeDistortions.VA, Pi.add_apply]
    ring
  rw [hV, map_add] at h1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, LargeDistortions.Vp,
    LargeDistortions.VA, hM.costK t z, hM.revF t z, LargeDistortions.fhatIso] at h1
  simp only [LargeDistortions.remAS]
  linear_combination h1 + h2

variable {A : Type*} {l : Filter A} {e : A → ℝ}

/-- Woodford (2003), §5 (**dividing by the amplitude**): if `ε D_t(ω) = O(ε²)` uniformly in
`(t, ω)` along a filter on which `ε → 0` and `ε ≠ 0` frequently, then `D = 0`. -/
theorem zero_of_uniform (he : Tendsto e l (𝓝 0)) (hne : ∃ᶠ a in l, e a ≠ 0)
    {D : ℕ → Ω → ℝ} (h : UProc l (fun a t z => e a * D t z) fun a => e a ^ 2) (t : ℕ) (z : Ω) :
    D t z = 0 := by
  by_contra hD
  have hpos : 0 < |D t z| := abs_pos.2 hD
  obtain ⟨C, hC⟩ := uniform_bound (f := fun p : A × (ℕ × Ω) => e p.1 * D p.2.1 p.2.2)
    (g := fun a => e a ^ 2) h
  have hη : 0 < |D t z| / (|C| + 1) := by positivity
  have hsmall : ∀ᶠ a in l, |e a| < |D t z| / (|C| + 1) := by
    have := he (Metric.ball_mem_nhds 0 hη)
    filter_upwards [this] with a ha
    simpa [Real.dist_eq] using ha
  obtain ⟨a, hea, hCa, hsa⟩ := (hne.and_eventually (hC.and hsmall)).exists
  have k := hCa (t, z)
  simp only [abs_mul, abs_pow] at k
  have hea' : 0 < |e a| := abs_pos.2 hea
  have k2 : |D t z| ≤ |C| * |e a| := by
    have : |e a| * |D t z| ≤ |e a| * (|C| * |e a|) := by
      calc |e a| * |D t z| ≤ C * |e a| ^ 2 := k
        _ ≤ |C| * |e a| ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ = |e a| * (|C| * |e a|) := by ring
    exact le_of_mul_le_mul_left this hea'
  have k3 : |C| * |e a| < |D t z| := by
    calc |C| * |e a| ≤ |C| * (|D t z| / (|C| + 1)) :=
          mul_le_mul_of_nonneg_left hsa.le (abs_nonneg C)
      _ < |D t z| := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  linarith

/-- **Woodford (2003), (5.4) to first order (hypothesis (b) of the LQ sufficiency argument,
DERIVED).** Let `ε → 0` along `l` with `ε ≠ 0` frequently. For a family of exact Calvo
equilibria (`LargeDistortions.CalvoModel.CalvoAS` at every amplitude) with `x̂, F̂, K̂, f̂, k̂` of
first order and inflation, output and disturbances with bounded first-order components
(`X − εX₁ = O(ε²)`), all uniformly in date and state, the first-order components satisfy the
linearised AS relation
`π₁ = κ(Ŷ₁ − Ŷⁿ₁) + βE_tπ₁′` with Woodford's natural rate `Ŷⁿ = YnA`. -/
theorem first_order_AS {α β θ ω σ sC : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ : θ ≠ 1)
    (hν : 1 + ω * θ ≠ 0) (hs : sC ≠ 0) (hc : ω + σ ≠ 0) (he : Tendsto e l (𝓝 0))
    (hne : ∃ᶠ a in l, e a ≠ 0) {infl xr F K f k Y G cb q muw tau : A → ℕ → Ω → ℝ}
    (hM : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC (infl a) (xr a) (F a) (K a)
      (f a) (k a) (Y a) (G a) (cb a) (q a) (muw a) (tau a))
    {infl1 Y1 G1 cb1 q1 muw1 tau1 : ℕ → Ω → ℝ} (hi1 : BoundedProc infl1)
    (hY1 : BoundedProc Y1) (hG1 : BoundedProc G1) (hcb1 : BoundedProc cb1)
    (hq1 : BoundedProc q1) (hm1 : BoundedProc muw1) (ht1 : BoundedProc tau1)
    (hid : UProc l (fun a t z => infl a t z - e a * infl1 t z) fun a => e a ^ 2)
    (hYd : UProc l (fun a t z => Y a t z - e a * Y1 t z) fun a => e a ^ 2)
    (hGd : UProc l (fun a t z => G a t z - e a * G1 t z) fun a => e a ^ 2)
    (hcbd : UProc l (fun a t z => cb a t z - e a * cb1 t z) fun a => e a ^ 2)
    (hqd : UProc l (fun a t z => q a t z - e a * q1 t z) fun a => e a ^ 2)
    (hmd : UProc l (fun a t z => muw a t z - e a * muw1 t z) fun a => e a ^ 2)
    (htd : UProc l (fun a t z => tau a t z - e a * tau1 t z) fun a => e a ^ 2)
    (hxr : UProc l xr fun a => e a ^ 1) (hF : UProc l F fun a => e a ^ 1)
    (hK : UProc l K fun a => e a ^ 1) (hf : UProc l f fun a => e a ^ 1)
    (hk : UProc l k fun a => e a ^ 1) :
    CostPush.ASNatural 𝔼 (Moments.calvoKappa α β ω θ σ) β infl1 Y1
      (fun t z => LargeDistortions.YnA ω σ sC (G1 t z) (cb1 t z) (q1 t z) (muw1 t z)
        (tau1 t z)) := by
  have hsl := tendsto_amp (J := ℕ × Ω) he
  set κ := Moments.calvoKappa α β ω θ σ with hκ
  have hi := first_order_o he hi1 hid
  have hY := first_order_o he hY1 hYd
  have hG := first_order_o he hG1 hGd
  have hcb := first_order_o he hcb1 hcbd
  have hq := first_order_o he hq1 hqd
  have hm := first_order_o he hm1 hmd
  have ht := first_order_o he ht1 htd
  -- conversions
  have cv : ∀ (X : A → ℕ → Ω → ℝ) (n : ℕ), UProc l X (fun a => e a ^ n) →
      (fun p : A × (ℕ × Ω) => X p.1 p.2.1 p.2.2) =O[l ×ˢ ⊤] fun p => e p.1 ^ n :=
    fun _ _ h => h
  -- the quadratic piece `Q`
  have hQ : UProc l (fun a t z => (θ - 1) / (2 * (1 - α)) * infl a t z ^ 2 +
      infl a t z * ((K a t z + F a t z) / 2)) fun a => e a ^ 2 := by
    have h1 := (o_mul (cv _ _ hi) (cv _ _ hi) (by norm_num : 1 + 1 = 2)).const_mul_left
      ((θ - 1) / (2 * (1 - α)))
    have hS : (fun p : A × (ℕ × Ω) => (K p.1 p.2.1 p.2.2 + F p.1 p.2.1 p.2.2) / 2)
        =O[l ×ˢ ⊤] fun p => e p.1 ^ 1 :=
      ((cv _ _ hK).add (cv _ _ hF)).const_mul_left (1 / 2) |>.congr_left fun p => by ring
    have h2 := o_mul (cv _ _ hi) hS rfl
    exact (h1.add h2).congr_left fun p => by ring
  have hQE := condE_o 𝔼 hQ
  -- `μ_y Ŷ²/2 − δŶ + tip`
  have hlin : ∀ (c1 c2 c3 c4 c5 : ℝ), UProc l (fun a t z => c1 * G a t z + c2 * cb a t z +
      c3 * q a t z + c4 * muw a t z + c5 * tau a t z) fun a => e a ^ 1 := fun c1 c2 c3 c4 c5 =>
    (((((cv _ _ hG).const_mul_left c1).add ((cv _ _ hcb).const_mul_left c2)).add
      ((cv _ _ hq).const_mul_left c3)).add ((cv _ _ hm).const_mul_left c4)).add
      ((cv _ _ ht).const_mul_left c5)
  have hdel : UProc l (fun a t z => LargeDistortions.deltaA α β θ ω σ sC (G a t z) (cb a t z)
      (q a t z) (muw a t z) (tau a t z)) fun a => e a ^ 1 := by
    refine (hlin (-(Moments.calvoXi α β ω θ * (σ / sC - (1 - σ) * σ)))
      (Moments.calvoXi α β ω θ * ((1 - σ) * σ * sC)) (Moments.calvoXi α β ω θ * ((1 + ω) * ω))
      (-(Moments.calvoXi α β ω θ * (1 + ω))) (Moments.calvoXi α β ω θ * (1 - σ))).congr_left
      fun p => ?_
    simp only [LargeDistortions.deltaA]
    ring
  have hP2 : UProc l (fun a t z => LargeDistortions.muY α β θ ω σ sC / 2 * Y a t z ^ 2 -
      LargeDistortions.deltaA α β θ ω σ sC (G a t z) (cb a t z) (q a t z) (muw a t z)
        (tau a t z) * Y a t z +
      LargeDistortions.tipASA α β θ ω σ sC (G a t z) (cb a t z) (q a t z) (muw a t z)
        (tau a t z)) fun a => e a ^ 2 := by
    have h1 := (o_mul (cv _ _ hY) (cv _ _ hY) (by norm_num : 1 + 1 = 2)).const_mul_left
      (LargeDistortions.muY α β θ ω σ sC / 2)
    have h2 := o_mul (cv _ _ hdel) (cv _ _ hY) rfl
    have hA1 := hlin 0 0 (-ω) 1 0
    have hA2 := hlin σ (σ * sC) 0 0 1
    have h3 := ((o_mul (cv _ _ hG) (cv _ _ hG) (by norm_num : 1 + 1 = 2)).const_mul_left
      (-(σ / (2 * sC)))).add
      (((o_mul (cv _ _ hA1) (cv _ _ hA1) (by norm_num : 1 + 1 = 2)).sub
        (o_mul (cv _ _ hA2) (cv _ _ hA2) (by norm_num : 1 + 1 = 2))).const_mul_left (1 / 2))
    have h3' := h3.const_mul_left (Moments.calvoXi α β ω θ)
    refine ((h1.sub h2).add h3').congr_left fun p => ?_
    simp only [LargeDistortions.tipASA]
    ring
  have hsq : UProc l (fun a t z => infl a t z ^ 2) fun a => e a ^ 2 :=
    (o_mul (cv _ _ hi) (cv _ _ hi) (by norm_num : 1 + 1 = 2)).congr_left fun p => by ring
  have hsqE := condE_o 𝔼 hsq
  have hrem := o_weaken hsl (by norm_num : 2 ≤ 3)
    (remAS_o 𝔼 he α β θ ω σ sC hi hxr hF hK hf hk hY hG hcb ht)
  -- the AS residual is `O(ε²)`
  have hR : UProc l (fun a t z => infl a t z - κ * (Y a t z - LargeDistortions.YnA ω σ sC
      (G a t z) (cb a t z) (q a t z) (muw a t z) (tau a t z)) - β * 𝔼.E t (infl a (t + 1)) z)
      fun a => e a ^ 2 := by
    refine ((((cv _ _ hQ).neg_left.add ((cv _ _ hQE).const_mul_left β)).add (cv _ _ hP2)).add
      ((cv _ _ hsqE).const_mul_left (β * (θ * (1 + ω)) / 2))).add hrem |>.congr_left fun p => ?_
    exact (as_residual 𝔼 hα0 hα1 hθ hν hs hc (hM p.1) p.2.1 p.2.2).symm
  -- the first-order difference
  set D : ℕ → Ω → ℝ := fun t z => infl1 t z - κ * (Y1 t z - LargeDistortions.YnA ω σ sC (G1 t z)
    (cb1 t z) (q1 t z) (muw1 t z) (tau1 t z)) - β * 𝔼.E t (infl1 (t + 1)) z with hDdef
  have hYn : UProc l (fun a t z => LargeDistortions.YnA ω σ sC (G a t z) (cb a t z) (q a t z)
      (muw a t z) (tau a t z) - e a * LargeDistortions.YnA ω σ sC (G1 t z) (cb1 t z) (q1 t z)
        (muw1 t z) (tau1 t z)) fun a => e a ^ 2 := by
    refine (((((cv _ _ hGd).const_mul_left (σ / (ω + σ))).add
      ((cv _ _ hcbd).const_mul_left (σ * sC / (ω + σ)))).add
      ((cv _ _ hqd).const_mul_left (ω / (ω + σ)))).add
      ((cv _ _ hmd).const_mul_left (-(1 / (ω + σ))))).add
      ((cv _ _ htd).const_mul_left (1 / (ω + σ))) |>.congr_left fun p => ?_
    simp only [LargeDistortions.YnA]
    field_simp
    ring
  have hEd := condE_o 𝔼 hid
  have hDO : UProc l (fun a t z => e a * D t z) fun a => e a ^ 2 := by
    refine (((hR.sub (cv _ _ hid)).add ((cv _ _ hYd).const_mul_left κ)).sub
      ((cv _ _ hYn).const_mul_left κ)).add ((cv _ _ hEd).const_mul_left β) |>.congr_left
        fun p => ?_
    have hEl : 𝔼.E p.2.1 (fun z => infl p.1 (p.2.1 + 1) z - e p.1 * infl1 (p.2.1 + 1) z)
        p.2.2 = 𝔼.E p.2.1 (infl p.1 (p.2.1 + 1)) p.2.2 -
          e p.1 * 𝔼.E p.2.1 (infl1 (p.2.1 + 1)) p.2.2 := by
      have e1 : (fun z => infl p.1 (p.2.1 + 1) z - e p.1 * infl1 (p.2.1 + 1) z) =
          infl p.1 (p.2.1 + 1) - e p.1 • infl1 (p.2.1 + 1) := by
        funext z; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [e1, map_sub, map_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hDdef]
    rw [hEl]
    ring
  intro t
  funext z
  have h0 := zero_of_uniform he hne hDO t z
  simp only [hDdef] at h0
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  linarith

/-- **Woodford (2003), (5.11) and footnote 71 (hypothesis (b) of
`TidyR5RamseySOC.lq_sufficiency615`, DERIVED).** Under the hypotheses of `first_order_AS`, the
first-order components satisfy `π₁ = κx₁ + βE_tπ₁′ + u` in the welfare-relevant gap
`x₁ = Ŷ₁ − Ŷ*₁` (`LargeDistortions.YstarA`) with the cost-push term
`u = κ(Ŷ*₁ − Ŷⁿ₁)` (`LargeDistortions.costPush511`), for every distortion `Φ`. -/
theorem first_order_NKPCu {α β θ ω σ sC Φ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hθ : θ ≠ 1)
    (hν : 1 + ω * θ ≠ 0) (hs : sC ≠ 0) (hc : ω + σ ≠ 0) (he : Tendsto e l (𝓝 0))
    (hne : ∃ᶠ a in l, e a ≠ 0) {infl xr F K f k Y G cb q muw tau : A → ℕ → Ω → ℝ}
    (hM : ∀ a, LargeDistortions.CalvoModel.CalvoAS 𝔼 α β θ ω σ sC (infl a) (xr a) (F a) (K a)
      (f a) (k a) (Y a) (G a) (cb a) (q a) (muw a) (tau a))
    {infl1 Y1 G1 cb1 q1 muw1 tau1 : ℕ → Ω → ℝ} (hi1 : BoundedProc infl1)
    (hY1 : BoundedProc Y1) (hG1 : BoundedProc G1) (hcb1 : BoundedProc cb1)
    (hq1 : BoundedProc q1) (hm1 : BoundedProc muw1) (ht1 : BoundedProc tau1)
    (hid : UProc l (fun a t z => infl a t z - e a * infl1 t z) fun a => e a ^ 2)
    (hYd : UProc l (fun a t z => Y a t z - e a * Y1 t z) fun a => e a ^ 2)
    (hGd : UProc l (fun a t z => G a t z - e a * G1 t z) fun a => e a ^ 2)
    (hcbd : UProc l (fun a t z => cb a t z - e a * cb1 t z) fun a => e a ^ 2)
    (hqd : UProc l (fun a t z => q a t z - e a * q1 t z) fun a => e a ^ 2)
    (hmd : UProc l (fun a t z => muw a t z - e a * muw1 t z) fun a => e a ^ 2)
    (htd : UProc l (fun a t z => tau a t z - e a * tau1 t z) fun a => e a ^ 2)
    (hxr : UProc l xr fun a => e a ^ 1) (hF : UProc l F fun a => e a ^ 1)
    (hK : UProc l K fun a => e a ^ 1) (hf : UProc l f fun a => e a ^ 1)
    (hk : UProc l k fun a => e a ^ 1) :
    TidyR5CommitLQ.NKPCu 𝔼 (Moments.calvoKappa α β ω θ σ) β
      (fun t z => LargeDistortions.costPush511 α β θ ω σ sC Φ (G1 t z) (cb1 t z) (q1 t z)
        (muw1 t z) (tau1 t z)) infl1
      (fun t z => Y1 t z - LargeDistortions.YstarA α β θ ω σ sC Φ (G1 t z) (cb1 t z) (q1 t z)
        (muw1 t z) (tau1 t z)) :=
  (LargeDistortions.as_gap_511 𝔼 (Φ := Φ)).1 (first_order_AS 𝔼 hα0 hα1 hθ hν hs hc he hne hM
    hi1 hY1 hG1 hcb1 hq1 hm1 ht1 hid hYd hGd hcbd hqd hmd htd hxr hF hK hf hk)

end Woodford.StabilizationWelfare.TidyR6aAS
