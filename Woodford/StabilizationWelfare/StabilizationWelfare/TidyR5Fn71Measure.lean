/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.TidyR5CommitLQ
import StabilizationWelfare.ExpectationsMeasure

/-!
# Footnote 71 on a general filtered probability space

Woodford (2003), *Interest and Prices*, Chapter 7, §5.1 and footnote 71 (complete stabilisation
of `log P_t + φx_t` is the optimal commitment when `λ = κφ`), with the cost-push AS relation
(4.38), p. 451.

`TidyR5CommitLQ.fn71_optimal` proves the claim for a core `ExpectationSystem` with the pull-out
property. Here the claim is proved on EVERY filtered probability space
(`ExpectationsMeasure.MeasExpectationSystem`, Mathlib's `condExp`), with every relation holding
almost surely:

* `mV`, `mX`, `mPi`: the plan `x_t = zx_{t−1} + v_t`, `π_t = −φ(x_t − x_{t−1})`, with `v` the
  forward solution `∑ (βz)ᵏE_t[−zu_{t+k}/φ]`
  (`ExpectationsMeasure.MeasExpectationSystem.forwardSol`).
* `mV_props`, `mX_props`, `mPi_props`: bounded, adapted.
* **`mfn71_AS`**: the plan satisfies `π_t = κx_t + βE_tπ_{t+1} + u_t` almost surely.
* **`mfn71_gap`**: for every bounded a.e.-measurable `(π′, x′)` satisfying the AS relation a.s.,
  almost surely `E₀L′ = E₀L + E₀∑βᵗ[(π′ − π)² + κφ(x′ − x)²] + 2φx_{−1}E₀(π′₀ − π₀)`.
* **`mfn71_optimal`** (`x_{−1} = 0`, date-0 optimality, a.s. in the date-0 information) and
  **`mfn71_timeless_optimal`** (any `x_{−1}`, competitors with the same `π₀`).
-/

namespace Woodford.StabilizationWelfare.TidyR5Fn71Measure

open MeasureTheory Filter Topology
open Sequences TidyR5CommitLQ
open ExpectationsMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : ExpectationsMeasure.MeasExpectationSystem Ω)

/-! ## The plan -/

/-- Woodford (2003), footnote 71: the forward component
`v_t = ∑ (βz)ᵏ E_t[−zu_{t+k}/φ]`, `z` the stable root with `c = κ/φ`. -/
noncomputable def mV (β κ φ : ℝ) (u : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  S.forwardSol (β * zRoot β (κ / φ)) (fun t ω => -(zRoot β (κ / φ) * u t ω / φ))

/-- Woodford (2003), footnote 71: the output gap `x_t = zx_{t−1} + v_t` with given `x_{−1}`. -/
noncomputable def mX (β κ φ : ℝ) (u : ℕ → Ω → ℝ) (xm1 : ℝ) : ℕ → Ω → ℝ
  | 0 => fun ω => zRoot β (κ / φ) * xm1 + mV S β κ φ u 0 ω
  | t + 1 => fun ω => zRoot β (κ / φ) * mX β κ φ u xm1 t ω + mV S β κ φ u (t + 1) ω

/-- Woodford (2003), footnote 71: inflation from the targeting rule `π_t = −φ(x_t − x_{t−1})`. -/
noncomputable def mPi (β κ φ : ℝ) (u : ℕ → Ω → ℝ) (xm1 : ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => -(φ * (mX S β κ φ u xm1 t ω - lagP (fun _ => xm1) (mX S β κ φ u xm1) t ω))

/-- Woodford (2003), (4.38), p. 451, almost surely: `π_t = κx_t + βE_tπ_{t+1} + u_t`. -/
def ASu (κ β : ℝ) (u π x : ℕ → Ω → ℝ) : Prop :=
  ∀ t, π t =ᵐ[S.μ] fun ω => κ * x t ω + β * S.E t (π (t + 1)) ω + u t ω

/-- Woodford (2003), (3.3): the date-0 conditional expected loss
`E₀∑βᵗ[π_t² + λx_t²]`. -/
noncomputable def ELoss0 (β lam : ℝ) (π x : ℕ → Ω → ℝ) : Ω → ℝ :=
  S.E 0 (fun ω => ∑' t, β ^ t * (π t ω ^ 2 + lam * x t ω ^ 2))

/-- Woodford (2003), footnote 71: `x_t = zx_{t−1} + v_t` at every date. -/
theorem mX_rec (β κ φ : ℝ) (u : ℕ → Ω → ℝ) (xm1 : ℝ) (t : ℕ) (ω : Ω) :
    mX S β κ φ u xm1 t ω = zRoot β (κ / φ) * lagP (fun _ => xm1) (mX S β κ φ u xm1) t ω +
      mV S β κ φ u t ω := by
  cases t <;> rfl

/-- Woodford (2003), footnote 71: for an a.e.-bounded adapted `u` the forward component is
a.e.-bounded, adapted and solves `v_t = βzE_tv_{t+1} − zu_t/φ` almost surely. -/
theorem mV_props {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u) :
    S.BddProc (mV S β κ φ u) ∧ StronglyAdapted S.𝓕 (mV S β κ φ u) ∧
      S.Solves (β * zRoot β (κ / φ)) (fun t ω => -(zRoot β (κ / φ) * u t ω / φ))
        (mV S β κ φ u) := by
  obtain ⟨hz0, hz1, -⟩ := zRoot_props hβ0 hβ1 (div_pos hκ hφ)
  have ha : |β * zRoot β (κ / φ)| < 1 := by
    rw [abs_of_pos (by positivity)]; nlinarith
  have hw : ∀ t, ∀ᵐ ω ∂S.μ, |-(zRoot β (κ / φ) * u t ω / φ)| ≤ zRoot β (κ / φ) * M / φ :=
    fun t => (hu t).mono fun ω h => by
      rw [abs_neg, abs_div, abs_mul, abs_of_pos hz0, abs_of_pos hφ]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h hz0.le) hφ.le
  have hwa : StronglyAdapted S.𝓕 (fun t ω => -(zRoot β (κ / φ) * u t ω / φ)) := fun t => by
    have e : (fun ω => -(zRoot β (κ / φ) * u t ω / φ)) =
        fun ω => (-(zRoot β (κ / φ) / φ)) * u t ω := by funext ω; ring
    change StronglyMeasurable[S.𝓕 t] (fun ω => -(zRoot β (κ / φ) * u t ω / φ))
    rw [e]
    exact StronglyMeasurable.const_mul (hua t) _
  exact ⟨S.forwardSol_bdd ha hw, S.forwardSol_adapted _ _, S.forwardSol_solves ha hwa hw⟩

/-- Woodford (2003), footnote 71: the output gap of the plan is adapted and a.e.-bounded. -/
theorem mX_props {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u)
    (xm1 : ℝ) :
    StronglyAdapted S.𝓕 (mX S β κ φ u xm1) ∧ S.BddProc (mX S β κ φ u xm1) := by
  obtain ⟨hz0, hz1, -⟩ := zRoot_props hβ0 hβ1 (div_pos hκ hφ)
  obtain ⟨⟨V, hV⟩, hVa, -⟩ := mV_props S hβ0 hβ1 hκ hφ hu hua
  set z := zRoot β (κ / φ) with hz
  refine ⟨fun t => ?_, ?_⟩
  · induction t with
    | zero => exact stronglyMeasurable_const.add (hVa 0)
    | succ t ih =>
      exact ((ih.mono (S.𝓕.mono (Nat.le_succ t))).const_mul z).add (hVa (t + 1))
  · set B := |xm1| + |V| / (1 - z) with hB
    have h1z : 0 < 1 - z := by linarith
    have hVB : ∀ t, ∀ᵐ ω ∂S.μ, |mV S β κ φ u t ω| ≤ |V| := fun t =>
      (hV t).mono fun ω h => h.trans (le_abs_self V)
    have hle : |V| ≤ |V| / (1 - z) := le_div_self (abs_nonneg _) h1z (by linarith)
    refine ⟨B, fun t => ?_⟩
    induction t with
    | zero =>
      filter_upwards [hVB 0] with ω h
      change |z * xm1 + mV S β κ φ u 0 ω| ≤ B
      calc _ ≤ |z * xm1| + |mV S β κ φ u 0 ω| := abs_add_le _ _
        _ ≤ |xm1| + |V| := by
            rw [abs_mul, abs_of_pos hz0]
            exact add_le_add (by nlinarith [abs_nonneg xm1]) h
        _ ≤ B := by simp only [hB]; linarith
    | succ t ih =>
      filter_upwards [ih, hVB (t + 1)] with ω h h'
      change |z * mX S β κ φ u xm1 t ω + mV S β κ φ u (t + 1) ω| ≤ B
      have key : |V| / (1 - z) = z * (|V| / (1 - z)) + |V| := by field_simp; ring
      calc _ ≤ |z * mX S β κ φ u xm1 t ω| + |mV S β κ φ u (t + 1) ω| := abs_add_le _ _
        _ ≤ z * B + |V| := by
            rw [abs_mul, abs_of_pos hz0]
            exact add_le_add (mul_le_mul_of_nonneg_left h hz0.le) h'
        _ ≤ B := by simp only [hB]; nlinarith [abs_nonneg xm1]

/-- Woodford (2003), footnote 71: inflation of the plan is adapted and a.e.-bounded. -/
theorem mPi_props {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u)
    (xm1 : ℝ) :
    StronglyAdapted S.𝓕 (mPi S β κ φ u xm1) ∧ S.BddProc (mPi S β κ φ u xm1) := by
  obtain ⟨hXa, B, hB⟩ := mX_props S hβ0 hβ1 hκ hφ hu hua xm1
  have hlag : ∀ t, StronglyMeasurable[S.𝓕 t]
      (lagP (fun _ => xm1) (mX S β κ φ u xm1) t) := fun t => by
    cases t with
    | zero => exact stronglyMeasurable_const
    | succ t => exact (hXa t).mono (S.𝓕.mono (Nat.le_succ t))
  refine ⟨fun t => ((hXa t).sub (hlag t)).const_mul φ |>.neg, |φ| * (|B| + |xm1|) + |φ| * |B|,
    fun t => ?_⟩
  have hlB : ∀ᵐ ω ∂S.μ, |lagP (fun _ => xm1) (mX S β κ φ u xm1) t ω| ≤ |B| + |xm1| := by
    rcases t with _ | t
    · refine Eventually.of_forall fun ω => ?_
      simp only [lagP]; linarith [abs_nonneg B]
    · refine (hB t).mono fun ω h => ?_
      simp only [lagP]; linarith [le_abs_self B, abs_nonneg xm1]
  filter_upwards [hB t, hlB] with ω h1 h2
  simp only [mPi, abs_neg, abs_mul]
  have := abs_sub (mX S β κ φ u xm1 t ω) (lagP (fun _ => xm1) (mX S β κ φ u xm1) t ω)
  have h3 : |mX S β κ φ u xm1 t ω| ≤ |B| := h1.trans (le_abs_self B)
  nlinarith [abs_nonneg φ]

/-- **Woodford (2003), footnote 71 and (4.38) (the plan is an equilibrium, almost surely).**
For `0 < β < 1`, `κ, φ > 0` and an a.e.-bounded adapted cost-push process `u`, the plan
satisfies `π_t = κx_t + βE_tπ_{t+1} + u_t` almost surely at every date. -/
theorem mfn71_AS {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u)
    (xm1 : ℝ) : ASu S κ β u (mPi S β κ φ u xm1) (mX S β κ φ u xm1) := by
  obtain ⟨hz0, hz1, hzq⟩ := zRoot_props hβ0 hβ1 (div_pos hκ hφ)
  obtain ⟨⟨V, hV⟩, hVa, hVs⟩ := mV_props S hβ0 hβ1 hκ hφ hu hua
  obtain ⟨hXa, B, hB⟩ := mX_props S hβ0 hβ1 hκ hφ hu hua xm1
  set z := zRoot β (κ / φ) with hz
  intro t
  have hXi : ∀ s, Integrable (mX S β κ φ u xm1 s) S.μ := fun s =>
    MeasExpectationSystem.BddRV.integrable ⟨((hXa s).mono (S.𝓕.le s)).aestronglyMeasurable, B, hB s⟩
  have hVi : ∀ s, Integrable (mV S β κ φ u s) S.μ := fun s =>
    MeasExpectationSystem.BddRV.integrable ⟨((hVa s).mono (S.𝓕.le s)).aestronglyMeasurable, V, hV s⟩
  have hX1 : mX S β κ φ u xm1 (t + 1) = z • mX S β κ φ u xm1 t + mV S β κ φ u (t + 1) := rfl
  have hP1 : mPi S β κ φ u xm1 (t + 1) =
      (-φ) • mX S β κ φ u xm1 (t + 1) + φ • mX S β κ φ u xm1 t := by
    funext ω'; simp only [mPi, lagP, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hEX : S.E t (mX S β κ φ u xm1 t) = mX S β κ φ u xm1 t :=
    S.E_of_stronglyMeasurable (hXa t) (hXi t)
  have hEX1 : S.E t (mX S β κ φ u xm1 (t + 1)) =ᵐ[S.μ]
      z • mX S β κ φ u xm1 t + S.E t (mV S β κ φ u (t + 1)) := by
    rw [hX1]
    filter_upwards [S.E_add ((hXi t).smul z) (hVi (t + 1)) t,
      S.E_smul z (mX S β κ φ u xm1 t) t] with ω h1 h2
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, hEX, Pi.add_apply, Pi.smul_apply]
  have hEP : S.E t (mPi S β κ φ u xm1 (t + 1)) =ᵐ[S.μ] fun ω =>
      -φ * (z * mX S β κ φ u xm1 t ω + S.E t (mV S β κ φ u (t + 1)) ω) +
        φ * mX S β κ φ u xm1 t ω := by
    rw [hP1]
    filter_upwards [S.E_add ((hXi (t + 1)).smul (-φ)) ((hXi t).smul φ) t,
      S.E_smul (-φ) (mX S β κ φ u xm1 (t + 1)) t, S.E_smul φ (mX S β κ φ u xm1 t) t, hEX1]
      with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, hEX]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  filter_upwards [hEP, hVs t] with ω h1 hv
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv
  have hx := mX_rec S β κ φ u xm1 t ω
  rw [h1]
  simp only [mPi]
  set X := mX S β κ φ u xm1 t ω
  set Lg := lagP (fun _ => xm1) (mX S β κ φ u xm1) t ω
  set Vt := mV S β κ φ u t ω
  set EV := S.E t (mV S β κ φ u (t + 1)) ω
  have hzne : z ≠ 0 := hz0.ne'
  have hφne : φ ≠ 0 := hφ.ne'
  have hL : Lg = (X - Vt) / z := by rw [hx]; field_simp; ring
  have key : -(φ * (X - Lg)) - (κ * X + β * (-φ * (z * X + EV) + φ * X) + u t ω) =
      φ * X / z * (β * z ^ 2 - (1 + β + κ / φ) * z + 1) := by
    rw [hL, hv]; field_simp; ring
  rw [hzq, mul_zero] at key
  linarith

/-- **Woodford (2003), footnote 71 and Ch. 7 (the gap identity on a filtered probability
space).** For every a.e.-measurable, a.e.-bounded `(π′, x′)` satisfying the AS relation with the
same cost-push process almost surely, almost surely
`E₀L′ = E₀L + E₀∑βᵗ[(π′_t − π_t)² + κφ(x′_t − x_t)²] + 2φx_{−1}E₀(π′₀ − π₀)`. -/
theorem mfn71_gap {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u)
    (xm1 : ℝ) {π' x' : ℕ → Ω → ℝ} (hπm : ∀ t, AEStronglyMeasurable (π' t) S.μ)
    (hxm : ∀ t, AEStronglyMeasurable (x' t) S.μ) (hπb : S.BddProc π') (hxb : S.BddProc x')
    (hAS' : ASu S κ β u π' x') :
    ∀ᵐ ω ∂S.μ, ELoss0 S β (κ * φ) π' x' ω = ELoss0 S β (κ * φ) (mPi S β κ φ u xm1)
        (mX S β κ φ u xm1) ω +
      S.E 0 (fun ω' => ∑' t, β ^ t * ((π' t ω' - mPi S β κ φ u xm1 t ω') ^ 2 +
        κ * φ * (x' t ω' - mX S β κ φ u xm1 t ω') ^ 2)) ω +
      2 * (φ * xm1 * S.E 0 (fun ω' => π' 0 ω' - mPi S β κ φ u xm1 0 ω') ω) := by
  obtain ⟨hPa, Bp, hBp⟩ := mPi_props S hβ0 hβ1 hκ hφ hu hua xm1
  obtain ⟨hXa, Bx, hBx⟩ := mX_props S hβ0 hβ1 hκ hφ hu hua xm1
  obtain ⟨Np, hNp⟩ := hπb
  obtain ⟨Nx, hNx⟩ := hxb
  have hAS := mfn71_AS S hβ0 hβ1 hκ hφ hu hua xm1
  set π := mPi S β κ φ u xm1 with hπdef
  set x := mX S β κ φ u xm1 with hxdef
  set lam := κ * φ with hlam
  set A := |Bp| + |Bx| + |Np| + |Nx| + |xm1| with hA
  have hA0 : 0 ≤ A := by positivity
  have bπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ A := fun t => (hBp t).mono fun ω h => h.trans (by
    simp only [hA]; linarith [le_abs_self Bp, abs_nonneg Bx, abs_nonneg Np, abs_nonneg Nx,
      abs_nonneg xm1])
  have bx : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ A := fun t => (hBx t).mono fun ω h => h.trans (by
    simp only [hA]; linarith [le_abs_self Bx, abs_nonneg Bp, abs_nonneg Np, abs_nonneg Nx,
      abs_nonneg xm1])
  have bπ' : ∀ t, ∀ᵐ ω ∂S.μ, |π' t ω| ≤ A := fun t => (hNp t).mono fun ω h => h.trans (by
    simp only [hA]; linarith [le_abs_self Np, abs_nonneg Bx, abs_nonneg Bp, abs_nonneg Nx,
      abs_nonneg xm1])
  have bx' : ∀ t, ∀ᵐ ω ∂S.μ, |x' t ω| ≤ A := fun t => (hNx t).mono fun ω h => h.trans (by
    simp only [hA]; linarith [le_abs_self Nx, abs_nonneg Bx, abs_nonneg Np, abs_nonneg Bp,
      abs_nonneg xm1])
  have mπ : ∀ t, AEStronglyMeasurable (π t) S.μ := fun t =>
    ((hPa t).mono (S.𝓕.le t)).aestronglyMeasurable
  have mx : ∀ t, AEStronglyMeasurable (x t) S.μ := fun t =>
    ((hXa t).mono (S.𝓕.le t)).aestronglyMeasurable
  have hI : ∀ (f : Ω → ℝ) (C : ℝ), AEStronglyMeasurable f S.μ → (∀ᵐ ω ∂S.μ, |f ω| ≤ C) →
      Integrable f S.μ := fun f C hm hb => MeasExpectationSystem.BddRV.integrable ⟨hm, C, hb⟩
  -- the pieces
  set dπ : ℕ → Ω → ℝ := fun t ω => π' t ω - π t ω with hdπ
  set lμ : ℕ → Ω → ℝ := lagP (fun _ => φ * xm1) (fun t ω => φ * x t ω) with hlμ
  have mdπ : ∀ t, AEStronglyMeasurable (dπ t) S.μ := fun t => (hπm t).sub (mπ t)
  have bdπ : ∀ t, ∀ᵐ ω ∂S.μ, |dπ t ω| ≤ 2 * A := fun t => by
    filter_upwards [bπ t, bπ' t] with ω h1 h2
    exact (abs_sub _ _).trans (by linarith)
  have idπ : ∀ t, Integrable (dπ t) S.μ := fun t => hI _ _ (mdπ t) (bdπ t)
  have blμ : ∀ t, ∀ᵐ ω ∂S.μ, |lμ t ω| ≤ |φ| * A := fun t => by
    rcases t with _ | t
    · refine Eventually.of_forall fun ω => ?_
      simp only [hlμ, lagP, abs_mul]
      have hx1 : |xm1| ≤ A := by
        have := abs_nonneg Bp; have := abs_nonneg Bx; have := abs_nonneg Np
        have := abs_nonneg Nx; simp only [hA]; linarith
      exact mul_le_mul_of_nonneg_left hx1 (abs_nonneg φ)
    · refine (bx t).mono fun ω h => ?_
      simp only [hlμ, lagP, abs_mul]
      exact mul_le_mul_of_nonneg_left h (abs_nonneg φ)
  have mlμ : ∀ t, AEStronglyMeasurable (lμ t) S.μ := fun t => by
    rcases t with _ | t
    · exact aestronglyMeasurable_const
    · exact (mx t).const_mul φ
  -- the AS relation in differences
  have hdAS : ∀ t, ∀ᵐ ω ∂S.μ, dπ t ω = κ * (x' t ω - x t ω) + β * S.E t (dπ (t + 1)) ω := by
    intro t
    filter_upwards [hAS t, hAS' t, S.E_sub (hI _ _ (hπm (t + 1)) (bπ' (t + 1)))
      (hI _ _ (mπ (t + 1)) (bπ (t + 1))) t] with ω e1 e2 e3
    have e3' : S.E t (dπ (t + 1)) ω = S.E t (π' (t + 1)) ω - S.E t (π (t + 1)) ω := by
      have e : dπ (t + 1) = π' (t + 1) - π (t + 1) := rfl
      rw [e, e3, Pi.sub_apply]
    simp only [hdπ]
    rw [e3', e1, e2]
    ring
  -- the period identity, almost surely
  have hfoc : ∀ t ω, π t ω + φ * x t ω - lμ t ω = 0 := fun t ω => by
    rcases t with _ | t <;> simp only [hπdef, hxdef, hlμ, mPi, lagP] <;> ring
  set Lp : ℕ → Ω → ℝ := fun t ω => π' t ω ^ 2 + lam * x' t ω ^ 2 with hLp
  set Lq : ℕ → Ω → ℝ := fun t ω => π t ω ^ 2 + lam * x t ω ^ 2 with hLq
  set Dd : ℕ → Ω → ℝ := fun t ω => (π' t ω - π t ω) ^ 2 + lam * (x' t ω - x t ω) ^ 2 with hDd
  set C : ℕ → Ω → ℝ := fun t ω => lμ t ω * dπ t ω with hC
  set Cr : ℕ → Ω → ℝ := fun t ω => (φ * x t ω) * S.E t (dπ (t + 1)) ω with hCr
  have hper : ∀ t, Lp t =ᵐ[S.μ] Lq t + Dd t + ((2 : ℝ) • C t - (2 * β) • Cr t) := by
    intro t
    filter_upwards [hdAS t] with ω a
    have f1 := hfoc t ω
    simp only [hLp, hLq, hDd, hC, hCr, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hdπ] at a ⊢
    linear_combination (2 * (π' t ω - π t ω)) * f1 - 2 * (φ * x t ω) * a
  -- bounds and integrability
  set BL := A ^ 2 + |lam| * A ^ 2 with hBL
  have bsq : ∀ (p y : ℕ → Ω → ℝ) (Bp By : ℝ), (∀ t, ∀ᵐ ω ∂S.μ, |p t ω| ≤ Bp) →
      (∀ t, ∀ᵐ ω ∂S.μ, |y t ω| ≤ By) → ∀ t, ∀ᵐ ω ∂S.μ,
        |p t ω ^ 2 + lam * y t ω ^ 2| ≤ Bp ^ 2 + |lam| * By ^ 2 := fun p y Bp By hp hy t => by
    filter_upwards [hp t, hy t] with ω h1 h2
    have e1 : p t ω ^ 2 ≤ Bp ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have e2 : y t ω ^ 2 ≤ By ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    calc _ ≤ |p t ω ^ 2| + |lam * y t ω ^ 2| := abs_add_le _ _
      _ = p t ω ^ 2 + |lam| * y t ω ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg (p t ω)), abs_mul, abs_of_nonneg (sq_nonneg (y t ω))]
      _ ≤ _ := add_le_add e1 (mul_le_mul_of_nonneg_left e2 (abs_nonneg _))
  have bLp := bsq π' x' A A bπ' bx'
  have bLq := bsq π x A A bπ bx
  have bdx : ∀ t, ∀ᵐ ω ∂S.μ, |(fun s ω => x' s ω - x s ω) t ω| ≤ 2 * A := fun t => by
    filter_upwards [bx t, bx' t] with ω h1 h2
    exact (abs_sub _ _).trans (by linarith)
  have bDd := bsq dπ (fun s ω => x' s ω - x s ω) (2 * A) (2 * A) bdπ bdx
  have mLp : ∀ t, AEStronglyMeasurable (Lp t) S.μ := fun t =>
    ((hπm t).pow 2).add (((hxm t).pow 2).const_mul lam)
  have mLq : ∀ t, AEStronglyMeasurable (Lq t) S.μ := fun t =>
    ((mπ t).pow 2).add (((mx t).pow 2).const_mul lam)
  have mDd : ∀ t, AEStronglyMeasurable (Dd t) S.μ := fun t =>
    ((mdπ t).pow 2).add ((((hxm t).sub (mx t)).pow 2).const_mul lam)
  have bC : ∀ t, ∀ᵐ ω ∂S.μ, |C t ω| ≤ |φ| * A * (2 * A) := fun t => by
    filter_upwards [blμ t, bdπ t] with ω h1 h2
    simp only [hC, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have mC : ∀ t, AEStronglyMeasurable (C t) S.μ := fun t => (mlμ t).mul (mdπ t)
  have bCr : ∀ t, ∀ᵐ ω ∂S.μ, |Cr t ω| ≤ |φ| * A * (2 * A) := fun t => by
    filter_upwards [bx t, S.abs_E_le (bdπ (t + 1)) t] with ω h1 h2
    simp only [hCr, abs_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg φ)) h2 (abs_nonneg _)
      (by positivity)
  have mCr : ∀ t, AEStronglyMeasurable (Cr t) S.μ := fun t =>
    ((mx t).const_mul φ).mul ((S.stronglyMeasurable_E t _).mono (S.𝓕.le t)).aestronglyMeasurable
  have iLp := fun t => hI _ _ (mLp t) (bLp t)
  have iLq := fun t => hI _ _ (mLq t) (bLq t)
  have iDd := fun t => hI _ _ (mDd t) (bDd t)
  have iC := fun t => hI _ _ (mC t) (bC t)
  have iCr := fun t => hI _ _ (mCr t) (bCr t)
  -- the cross term
  set K : ℕ → Ω → ℝ := fun t => S.E 0 (C t) with hK
  have hcross : ∀ t, S.E 0 (Cr t) =ᵐ[S.μ] K (t + 1) := by
    intro t
    have hsm : StronglyMeasurable[S.𝓕 t] (fun ω => φ * x t ω) := (hXa t).const_mul φ
    have hb : ∀ᵐ ω ∂S.μ, |(fun ω => φ * x t ω) ω| ≤ |φ| * A :=
      (bx t).mono fun ω h => by
        simp only [abs_mul]; exact mul_le_mul_of_nonneg_left h (abs_nonneg φ)
    have hpo := S.E_pullOut hsm hb (idπ (t + 1))
    have e1 : Cr t = (fun ω => φ * x t ω) * S.E t (dπ (t + 1)) := rfl
    have e2 : C (t + 1) = (fun ω => φ * x t ω) * dπ (t + 1) := rfl
    rw [e1]
    filter_upwards [S.E_congr hpo.symm 0, S.E_tower (Nat.zero_le t)
      ((fun ω => φ * x t ω) * dπ (t + 1))] with ω h1 h2
    rw [h1, h2]
    rfl
  -- the period identity under `E₀`
  have hE0 : ∀ t, ∀ᵐ ω ∂S.μ, S.E 0 (Lp t) ω =
      (S.E 0 (Lq t) ω + S.E 0 (Dd t) ω) + (2 * K t ω - β * (2 * K (t + 1) ω)) := by
    intro t
    filter_upwards [S.E_congr (hper t) 0, S.E_add ((iLq t).add (iDd t))
      (((iC t).smul (2 : ℝ)).sub ((iCr t).smul (2 * β))) 0, S.E_add (iLq t) (iDd t) 0,
      S.E_sub ((iC t).smul (2 : ℝ)) ((iCr t).smul (2 * β)) 0, S.E_smul (2 : ℝ) (C t) 0,
      S.E_smul (2 * β) (Cr t) 0, hcross t] with ω h1 h2 h3 h4 h5 h6 h7
    rw [h1, h2, Pi.add_apply, h3, Pi.add_apply, h4, Pi.sub_apply, h5, h6, Pi.smul_apply,
      Pi.smul_apply, smul_eq_mul, smul_eq_mul, h7]
    ring
  -- the series under `E₀`
  have hser : ∀ (L : ℕ → Ω → ℝ) (BB : ℝ), (∀ t, AEStronglyMeasurable (L t) S.μ) →
      (∀ t, ∀ᵐ ω ∂S.μ, |L t ω| ≤ BB) → ∀ᵐ ω ∂S.μ,
        HasSum (fun t => β ^ t * S.E 0 (L t) ω) (S.E 0 (fun ω' => ∑' t, β ^ t * L t ω') ω) := by
    intro L BB hm hb
    have hc : Summable (fun k => β ^ k * BB) :=
      (summable_geometric_of_lt_one hβ0.le hβ1).mul_right BB
    have hf : ∀ k, ∀ᵐ ω ∂S.μ, |(fun ω => β ^ k * L k ω) ω| ≤ β ^ k * BB := fun k =>
      (hb k).mono fun ω h => by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0.le k)]
        exact mul_le_mul_of_nonneg_left h (pow_nonneg hβ0.le k)
    have hs := S.E_hasSum hc (fun k => (hm k).const_mul _) hf 0
    filter_upwards [hs, ae_all_iff.2 fun k => S.E_smul (β ^ k) (L k) 0] with ω h1 h2
    refine h1.congr_fun fun k => ?_
    have e : (fun ω => β ^ k * L k ω) = β ^ k • L k := rfl
    rw [e, h2 k, Pi.smul_apply, smul_eq_mul]
  have sLp := hser Lp _ mLp bLp
  have sLq := hser Lq _ mLq bLq
  have sDd := hser Dd _ mDd bDd
  -- bounds along the dates
  have bE : ∀ (L : ℕ → Ω → ℝ) (BB : ℝ), (∀ t, ∀ᵐ ω ∂S.μ, |L t ω| ≤ BB) →
      ∀ᵐ ω ∂S.μ, ∀ t, |S.E 0 (L t) ω| ≤ BB := fun L BB hb =>
    ae_all_iff.2 fun t => S.abs_E_le (hb t) 0
  have hK0 : K 0 =ᵐ[S.μ] fun ω => φ * xm1 * S.E 0 (fun ω' => π' 0 ω' - π 0 ω') ω := by
    have e : C 0 = (φ * xm1) • dπ 0 := by
      funext ω; simp only [hC, hlμ, lagP, Pi.smul_apply, smul_eq_mul]
    filter_upwards [S.E_smul (φ * xm1) (dπ 0) 0] with ω h
    rw [hK]
    simp only
    rw [e, h, Pi.smul_apply, smul_eq_mul]
  filter_upwards [sLp, sLq, sDd, ae_all_iff.2 hE0, bE Lq _ bLq, bE Dd _ bDd, bE C _ bC, hK0]
    with ω h1 h2 h3 h4 h5 h6 h7 h8
  have hG : Bdd (fun t => S.E 0 (Lq t) ω + S.E 0 (Dd t) ω) :=
    ⟨_, fun t => (abs_add_le _ _).trans (add_le_add (h5 t) (h6 t))⟩
  have hKb : Bdd (fun t => 2 * K t ω) :=
    ⟨2 * (|φ| * A * (2 * A)), fun t => by
      rw [abs_mul, abs_two]; exact mul_le_mul_of_nonneg_left (h7 t) (by norm_num)⟩
  have hT := tsum_telescope_add hβ0.le hβ1 hG hKb (fun t => h4 t)
  have hq1 : Bdd (fun t => S.E 0 (Lq t) ω) := ⟨_, h5⟩
  have hq2 : Bdd (fun t => S.E 0 (Dd t) ω) := ⟨_, h6⟩
  unfold ELoss0
  rw [← h1.tsum_eq, ← h2.tsum_eq, ← h3.tsum_eq, hT]
  have e : ∑' t, β ^ t * (S.E 0 (Lq t) ω + S.E 0 (Dd t) ω) =
      ∑' t, β ^ t * S.E 0 (Lq t) ω + ∑' t, β ^ t * S.E 0 (Dd t) ω := by
    rw [← (hq1.summable hβ0.le hβ1).tsum_add (hq2.summable hβ0.le hβ1)]
    exact tsum_congr fun t => by ring
  rw [e, h8]

/-- **Woodford (2003), footnote 71 and Ch. 7, §5.1 (complete stabilisation of `log P_t + φx_t`
is the date-0 optimal policy for `λ = κφ`, on any filtered probability space).** With
`x_{−1} = 0`, the plan minimises `E₀∑βᵗ[π_t² + κφx_t²]` almost surely among ALL a.e.-measurable,
a.e.-bounded processes satisfying the AS relation (4.38) almost surely, and the excess loss is
`E₀∑βᵗ[(π′ − π)² + κφ(x′ − x)²] ≥ 0`. -/
theorem mfn71_optimal {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ) (hφ : 0 < φ)
    {u : ℕ → Ω → ℝ} (hu : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M) (hua : StronglyAdapted S.𝓕 u)
    {π' x' : ℕ → Ω → ℝ} (hπm : ∀ t, AEStronglyMeasurable (π' t) S.μ)
    (hxm : ∀ t, AEStronglyMeasurable (x' t) S.μ) (hπb : S.BddProc π') (hxb : S.BddProc x')
    (hAS' : ASu S κ β u π' x') :
    ∀ᵐ ω ∂S.μ, ELoss0 S β (κ * φ) (mPi S β κ φ u 0) (mX S β κ φ u 0) ω ≤
      ELoss0 S β (κ * φ) π' x' ω := by
  have hg := mfn71_gap S hβ0 hβ1 hκ hφ hu hua 0 hπm hxm hπb hxb hAS'
  have hnn : (fun _ : Ω => (0 : ℝ)) ≤ fun ω' => ∑' t, β ^ t *
      ((π' t ω' - mPi S β κ φ u 0 t ω') ^ 2 + κ * φ * (x' t ω' - mX S β κ φ u 0 t ω') ^ 2) :=
    fun ω' => tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0.le t) (by positivity)
  have h0 := condExp_nonneg (m := S.𝓕 0) (μ := S.μ) (Eventually.of_forall hnn)
  filter_upwards [hg, h0] with ω h1 h2
  rw [h1]
  simp only [Pi.zero_apply] at h2
  nlinarith

/-- **Woodford (2003), footnote 71 and Ch. 7, §1 (optimality from a timeless perspective, on any
filtered probability space).** For any `x_{−1}`, the plan minimises the expected discounted loss
almost surely among all a.e.-measurable, a.e.-bounded processes satisfying the AS relation
almost surely and the initial commitment `π′₀ = π₀` almost surely. -/
theorem mfn71_timeless_optimal {β κ φ M : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hκ : 0 < κ)
    (hφ : 0 < φ) {u : ℕ → Ω → ℝ} (hu : ∀ t, ∀ᵐ ω ∂S.μ, |u t ω| ≤ M)
    (hua : StronglyAdapted S.𝓕 u) (xm1 : ℝ) {π' x' : ℕ → Ω → ℝ}
    (hπm : ∀ t, AEStronglyMeasurable (π' t) S.μ) (hxm : ∀ t, AEStronglyMeasurable (x' t) S.μ)
    (hπb : S.BddProc π') (hxb : S.BddProc x') (hAS' : ASu S κ β u π' x')
    (h0' : π' 0 =ᵐ[S.μ] mPi S β κ φ u xm1 0) :
    ∀ᵐ ω ∂S.μ, ELoss0 S β (κ * φ) (mPi S β κ φ u xm1) (mX S β κ φ u xm1) ω ≤
      ELoss0 S β (κ * φ) π' x' ω := by
  have hg := mfn71_gap S hβ0 hβ1 hκ hφ hu hua xm1 hπm hxm hπb hxb hAS'
  have hnn : (fun _ : Ω => (0 : ℝ)) ≤ fun ω' => ∑' t, β ^ t *
      ((π' t ω' - mPi S β κ φ u xm1 t ω') ^ 2 +
        κ * φ * (x' t ω' - mX S β κ φ u xm1 t ω') ^ 2) :=
    fun ω' => tsum_nonneg fun t => mul_nonneg (pow_nonneg hβ0.le t) (by positivity)
  have hnn0 := condExp_nonneg (m := S.𝓕 0) (μ := S.μ) (Eventually.of_forall hnn)
  have hz : (fun ω' => π' 0 ω' - mPi S β κ φ u xm1 0 ω') =ᵐ[S.μ] 0 :=
    h0'.mono fun ω h => by simp only [Pi.zero_apply, h, sub_self]
  have hz0 : S.E 0 (fun ω' => π' 0 ω' - mPi S β κ φ u xm1 0 ω') =ᵐ[S.μ] 0 := by
    filter_upwards [S.E_congr hz 0] with ω h
    rw [h, S.E_zero]
  filter_upwards [hg, hnn0, hz0] with ω h1 h2 h3
  rw [h1, h3]
  simp only [Pi.zero_apply] at h2 ⊢
  nlinarith

end Woodford.StabilizationWelfare.TidyR5Fn71Measure
