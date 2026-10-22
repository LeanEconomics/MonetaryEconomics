/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearNKMarkovAEAdapted
import StabilizationWelfare.NonlinearNKMarkovRamseyTree

/-!
# The linearised Ramsey operator on a filtered probability space (almost-sure form)

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (the timeless Ramsey plan with the
predetermined `Δ_{−1}, λ_{−1}`), Chapter 6, §5, and Appendix A.3.

`NonlinearNKMarkovRamseyTree` inverts the linearised Ramsey operator with a lag on an event tree,
where `M(f ∘ par) = f` holds exactly. On a general filtered probability space
(`ExpectationsMeasure.MeasExpectationSystem`, Mathlib's `condExp`) the expectation is linear
only almost surely, and `E_t[f_t] = f_t` only for ADAPTED `f`. This module redoes the inverse
in almost-sure form on adapted, essentially bounded processes.

* `lagS` (the lag in time, `0` at date `0`), `bwdS` (backward solution), `fwdSA` (forward
  solution of `g = cE_t g_{t+1} + f`, from `NonlinearNKMarkovAE.fwdSolA`), and the class `AdB`
  of adapted processes with an a.s. bound `c·A`, closed under linear combinations (`adb_lin2`),
  forecasts (`adb_Ms`), lags (`adb_lag`), backward (`adb_bwd`) and forward (`adb_fwd`)
  solutions; `Ms_lag` (`E_t[lag f]_{t+1} = f_t` a.s. for adapted `f`).
* `zero_of_eq_cMs` and `zero_of_eq_lagS`: the a.s. uniqueness of the forward and backward
  recursions.
* `LRA` (the linearised operator), `LinvRA` (its inverse, built by the reduction of
  `NonlinearNKMarkovRamseyLin` exactly as on event trees), the uniform bounds `adb_*`,
  **`LRA_LinvRA`** (`L(L⁻¹r) = r` a.s.), **`LRA_inj`** (an adapted bounded solution of `Lv = 0`
  is `0` a.s.: the a-priori bound with predetermined variables), `LinvRA_LRA`, `LinvRA_sub`,
  `LRA_sub`, `rhyp_LRA`, `rhyp_LinvRA`.
-/

namespace Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyAE

open MeasureTheory Filter Topology
open NonlinearNKMarkov NonlinearNKMarkovGeneral NonlinearNKMarkovRamsey NonlinearNKMarkovRamseyLin
open NonlinearNKMarkovRamseyTree ExpectationsMeasure NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted

/-! ## Scalar processes: lags, backward and forward solutions -/

/-- Woodford (2003), Ch. 7: the lag of a process, `0` at date `0` (zero initial deviation). -/
def lagS {Ω : Type*} (f : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | t + 1 => f t

/-- Woodford (2003), Ch. 7: the backward solution `∑_{j ≤ t} cʲ f_{t−j}` of `g = c·lag g + f`. -/
noncomputable def bwdS {Ω : Type*} (c : ℝ) (f : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range (t + 1), c ^ j * f (t - j) ω

/-- The backward recursion (pointwise). -/
theorem bwdS_eq {Ω : Type*} (c : ℝ) (f : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) :
    bwdS c f t ω = c * lagS (bwdS c f) t ω + f t ω := by
  cases t with
  | zero => simp [bwdS, lagS]
  | succ t =>
    simp only [bwdS, lagS]
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.sub_zero]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ, show t + 1 - (j + 1) = t - j by omega]
    ring

/-- A sub-σ-algebra a.s. measurable function is a.s. measurable. -/
theorem aesm_of_sub {X : Type*} {m m0 : MeasurableSpace X} (hm : m ≤ m0) {μ : Measure[m0] X}
    {f : X → ℝ} (hf : AEStronglyMeasurable[m] f μ) : AEStronglyMeasurable[m0] f μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.mono hm, hf.ae_eq_mk⟩

variable {Ω : Type*} [MeasurableSpace Ω] (E : MeasExpectationSystem Ω)

/-- Woodford (2003), App. A.3: an adapted process with the a.s. bound `|f_t| ≤ c·A`. -/
def AdB (f : ℕ → Ω → ℝ) (c A : ℝ) : Prop :=
  (∀ t, AEStronglyMeasurable[E.𝓕 t] (f t) E.μ) ∧ ∀ t, ∀ᵐ ω ∂E.μ, |f t ω| ≤ c * A

/-- `AdB` is a.s. measurable. -/
theorem AdB.aesm {f : ℕ → Ω → ℝ} {c A : ℝ} (h : AdB E f c A) (t : ℕ) :
    AEStronglyMeasurable (f t) E.μ := aesm_of_sub (E.𝓕.le t) (h.1 t)

/-- `AdB` is integrable. -/
theorem AdB.int {f : ℕ → Ω → ℝ} {c A : ℝ} (h : AdB E f c A) (t : ℕ) : Integrable (f t) E.μ :=
  integrable_of E (h.aesm E t) (h.2 t)

/-- Two-term combinations of `AdB` processes. -/
theorem adb_lin2 {f g : ℕ → Ω → ℝ} {cf cg A : ℝ} (hf : AdB E f cf A) (hg : AdB E g cg A)
    (k1 k2 : ℝ) : AdB E (fun t ω => k1 * f t ω + k2 * g t ω) (|k1| * cf + |k2| * cg) A := by
  refine ⟨fun t => ((hf.1 t).const_mul k1).add ((hg.1 t).const_mul k2), fun t => ?_⟩
  filter_upwards [hf.2 t, hg.2 t] with ω h1 h2
  have e1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg k1)
  have e2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg k2)
  calc _ ≤ |k1 * f t ω| + |k2 * g t ω| := abs_add_le _ _
    _ = |k1| * |f t ω| + |k2| * |g t ω| := by rw [abs_mul, abs_mul]
    _ ≤ _ := by nlinarith

/-- `AdB` up to a pointwise identity. -/
theorem AdB.congr {f g : ℕ → Ω → ℝ} {c A : ℝ} (h : AdB E f c A) (e : ∀ t ω, g t ω = f t ω) :
    AdB E g c A := by
  have : g = f := funext fun t => funext fun ω => e t ω
  rw [this]; exact h

/-- `AdB` with a larger constant. -/
theorem AdB.mono {f : ℕ → Ω → ℝ} {c c' A : ℝ} (h : AdB E f c A) (hc : c ≤ c') (hA : 0 ≤ A) :
    AdB E f c' A :=
  ⟨h.1, fun t => by
    filter_upwards [h.2 t] with ω hω; exact hω.trans (mul_le_mul_of_nonneg_right hc hA)⟩

/-- Woodford (2003), (A.11): forecasts of `AdB` processes are `AdB`. -/
theorem adb_Ms {f : ℕ → Ω → ℝ} {c A : ℝ} (h : AdB E f c A) : AdB E (Ms E f) c A :=
  ⟨fun t => (E.stronglyMeasurable_E t _).aestronglyMeasurable, fun t => E.abs_E_le (h.2 (t + 1)) t⟩

/-- Lags of `AdB` processes are `AdB`. -/
theorem adb_lag {f : ℕ → Ω → ℝ} {c A : ℝ} (h0 : 0 ≤ c * A) (h : AdB E f c A) :
    AdB E (lagS f) c A := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · cases t with
    | zero => exact aestronglyMeasurable_const
    | succ t =>
      have := h.1 t
      exact ⟨this.mk _, this.stronglyMeasurable_mk.mono (E.𝓕.mono (Nat.le_succ t)),
        this.ae_eq_mk⟩
  · cases t with
    | zero => exact Eventually.of_forall fun _ => by simpa [lagS] using h0
    | succ t => exact h.2 t

/-- Woodford (2003), Ch. 7: backward solutions of `AdB` processes are `AdB`. -/
theorem adb_bwd {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) {f : ℕ → Ω → ℝ} {cf A : ℝ} (hcf : 0 ≤ cf)
    (hA : 0 ≤ A) (h : AdB E f cf A) : AdB E (bwdS c f) (cf / (1 - c)) A := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hj : ∀ j ∈ Finset.range (t + 1), AEStronglyMeasurable[E.𝓕 t]
        (fun ω => c ^ j * f (t - j) ω) E.μ := fun j _ => by
      have := h.1 (t - j)
      have h' : AEStronglyMeasurable[E.𝓕 t] (f (t - j)) E.μ :=
        ⟨this.mk _, this.stronglyMeasurable_mk.mono (E.𝓕.mono (Nat.sub_le t j)), this.ae_eq_mk⟩
      exact h'.const_mul _
    have key : ∀ s : Finset ℕ, (∀ j ∈ s, AEStronglyMeasurable[E.𝓕 t]
        (fun ω => c ^ j * f (t - j) ω) E.μ) →
        AEStronglyMeasurable[E.𝓕 t] (fun ω => ∑ j ∈ s, c ^ j * f (t - j) ω) E.μ := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simpa using (aestronglyMeasurable_const (b := (0 : ℝ)))
      | insert a s ha ih =>
        intro hs
        simp only [Finset.sum_insert ha]
        exact (hs a (Finset.mem_insert_self a s)).add
          (ih fun j hj => hs j (Finset.mem_insert_of_mem hj))
    exact key _ hj
  · filter_upwards [ae_all_iff.2 h.2] with ω hω
    unfold bwdS
    calc _ ≤ ∑ j ∈ Finset.range (t + 1), c ^ j * (cf * A) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (pow_nonneg hc0 j)]
          exact mul_le_mul_of_nonneg_left (hω _) (pow_nonneg hc0 j)
      _ = (cf * A) * ∑ j ∈ Finset.range (t + 1), c ^ j := by rw [Finset.mul_sum]; ring_nf
      _ ≤ (cf * A) * (1 - c)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← tsum_geometric_of_lt_one hc0 hc1]
          exact Summable.sum_le_tsum _ (fun j _ => pow_nonneg hc0 j)
            (summable_geometric_of_lt_one hc0 hc1)
      _ = cf / (1 - c) * A := by ring

/-- Woodford (2003), (A.13) a.s. for a scalar: the forward solution of `g = cE_t g_{t+1} + f`. -/
noncomputable def fwdSA (c : ℝ) (f : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  fwdSolA E !![c] (fun s ω => ![f s ω]) t ω 0

/-- Woodford (2003), (A.13) a.s.: the forward solution is `AdB` and solves
`g_t = cE_t g_{t+1} + f_t` a.s. -/
theorem adb_fwd {c : ℝ} (hc : |c| < 1) {f : ℕ → Ω → ℝ} {cf A : ℝ} (hcf : 0 ≤ cf) (hA : 0 ≤ A)
    (h : AdB E f cf A) :
    AdB E (fwdSA E c f) (Sg c * cf) A ∧
      ∀ t, fwdSA E c f t =ᵐ[E.μ] fun ω => c * Ms E (fwdSA E c f) t ω + f t ω := by
  set b : ℕ → Ω → Fin 1 → ℝ := fun s ω => ![f s ω] with hb
  have hbG : Gd E b := fun t => aesm_vec E fun i => by fin_cases i; exact h.aesm E t
  have hbB : Bd E b (cf * A) := fun t => by
    filter_upwards [h.2 t] with ω hω
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    fin_cases i; simpa [hb] using hω
  have hbA : AdA E b := fun t => aesmSub_vec fun i => by fin_cases i; exact h.1 t
  obtain ⟨-, h2, h3⟩ := fwdSolA_spec E (summable_c hc) hbG (by positivity) hbB
  have hA' := adA_fwdSolA E (summable_c hc) (by positivity) hbB hbA
  refine ⟨⟨fun t => (continuous_apply 0).comp_aestronglyMeasurable (hA' t), fun t => ?_⟩,
    fun t => ?_⟩
  · filter_upwards [h2 t] with ω hω
    have := (norm_le_pi_norm (fwdSolA E !![c] b t ω) 0).trans hω
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_of_eq (by unfold Sg; ring))
  · filter_upwards [h3 t] with ω hω
    have := congrFun hω 0
    simp only [Matrix.cons_mulVec, dotProduct, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, Matrix.cons_val_fin_one, Finset.sum_singleton,
      Pi.add_apply] at this
    exact this

/-- Woodford (2003), App. A.3: `E_t[(lag f)_{t+1}] = f_t` a.s. for adapted integrable `f`. -/
theorem Ms_lag {f : ℕ → Ω → ℝ} {c A : ℝ} (h : AdB E f c A) (t : ℕ) :
    Ms E (lagS f) t =ᵐ[E.μ] f t :=
  E.E_of_aestronglyMeasurable (h.1 t) (h.int E t)

/-- Two-term a.s. linearity of the forecast. -/
theorem Ms_lin2 {f g : ℕ → Ω → ℝ} {cf cg A : ℝ} (hf : AdB E f cf A) (hg : AdB E g cg A)
    (a b : ℝ) (t : ℕ) : Ms E (fun s ω => a * f s ω + b * g s ω) t =ᵐ[E.μ]
      fun ω => a * Ms E f t ω + b * Ms E g t ω :=
  E_lin2 E (hf.int E (t + 1)) (hg.int E (t + 1)) a b t

/-- Woodford (2003), App. A.3: a bounded solution of `g_t = cE_t g_{t+1}` a.s. with `|c| < 1` is
`0` a.s. -/
theorem zero_of_eq_cMs {c : ℝ} (hc : |c| < 1) {g : ℕ → Ω → ℝ} {B : ℝ}
    (hB : ∀ t, ∀ᵐ ω ∂E.μ, |g t ω| ≤ B) (h : ∀ t, g t =ᵐ[E.μ] fun ω => c * Ms E g t ω)
    (t : ℕ) : g t =ᵐ[E.μ] 0 := by
  have hn : ∀ n : ℕ, ∀ t, ∀ᵐ ω ∂E.μ, |g t ω| ≤ |c| ^ n * B := by
    intro n
    induction n with
    | zero => intro t; simpa using hB t
    | succ n ih =>
      intro t
      filter_upwards [h t, E.abs_E_le (ih (t + 1)) t] with ω h1 h2
      rw [h1, abs_mul, pow_succ, mul_comm (|c| ^ n) |c|, mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg c)
  have ht : Tendsto (fun n : ℕ => |c| ^ n * B) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg c) hc).mul_const B
  filter_upwards [ae_all_iff.2 fun n => hn n t] with ω hω
  exact abs_nonpos_iff.1 (ge_of_tendsto' ht hω)

/-- Woodford (2003), App. A.3: if `g_t = c·(lag g)_t` a.s. at every date then `g = 0` a.s. -/
theorem zero_of_eq_lagS {c : ℝ} {g : ℕ → Ω → ℝ} (h : ∀ t, g t =ᵐ[E.μ] fun ω => c * lagS g t ω)
    (t : ℕ) : g t =ᵐ[E.μ] 0 := by
  induction t with
  | zero => filter_upwards [h 0] with ω hω; simpa [lagS] using hω
  | succ t ih =>
    filter_upwards [h (t + 1), ih] with ω h1 h2
    rw [h1]; simp only [lagS, Pi.zero_apply] at h2 ⊢; rw [h2, mul_zero]

/-! ## The inverse of the linearised operator, almost surely -/

/-- Woodford (2003), Ch. 7: the lagged vector process, `0` at date `0`. -/
def lagvS {n : ℕ} (v : ℕ → Ω → Fin n → ℝ) (t : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => lagS (fun s ω' => v s ω' i) t ω

/-- Woodford (2003), Ch. 7 and App. A.3 (**the linearised Ramsey operator, a.s. form**):
`(Lv)_t = DQr(v_{t−1}, v_t) + DNr(E_t v_{t+1})`, zero lag at date `0`. -/
noncomputable def LRA (p : Par) (R : RPar) (v : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : Fin 9 → ℝ :=
  DQr p R (lagvS v t ω) (v t ω) + DNr p R (MvA E v t ω)

/-- The inverse, dispersion (`red_D`). -/
noncomputable def DvA (p : Par) (r : ℕ → Ω → Fin 9 → ℝ) : ℕ → Ω → ℝ :=
  bwdS p.α (fun t ω => aE p / (p.θ - 1) * r t ω 7 + 1 * r t ω 8)

/-- The inverse, summed multiplier (`red_mu`). -/
noncomputable def MuvA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) : ℕ → Ω → ℝ :=
  bwdS p.α (fun t ω => 1 * (1 * r t ω 2 + 1 * r t ω 3) +
    -(ramseyLam p R 0 * p.c0 / (p.θ - 1)) * r t ω 7)

/-- The inverse, NKPC forcing (`red_pc`). -/
noncomputable def gvA (p : Par) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (1 - p.α) / (p.c0 * p.α) * (r t ω 6 - r t ω 5) +
    (r t ω 7 - p.α * p.β * Ms E (fun s ω' => r s ω' 7) t ω) / (p.α * (p.θ - 1))

/-- The inverse, targeting-rule forcing times `A_uG` (`red_target`). -/
noncomputable def FtvA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (1 - p.α * p.β) * (p.σ + p.ω) * (-((1 - p.α) * aE p / p.c0 *
    (lagS (MuvA p R r) t ω + ramseyLam p R 3 * lagS (DvA p r) t ω)) -
    (p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) / (p.θ - 1) * r t ω 7 + r t ω 2 -
    (1 - p.α) / (p.α * p.c0) * r t ω 1) - (r t ω 0 - lagS (fun s ω' => r s ω' 0) t ω) -
  (1 - R.Φ) * R.Au * (DvA p r t ω - lagS (DvA p r) t ω) -
  (1 - p.α * p.β) * (1 + p.ω) * (MuvA p R r t ω - lagS (MuvA p R r) t ω)

/-- The inverse, `f = F/(A_uG)`: `ŷ − ŷ₋ + θπ = f`. -/
noncomputable def fvA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  FtvA p R r t ω / (R.Au * Gw p R)

/-- The inverse, forcing of `βE_t y_{t+1} − (1+β+κθ)y_t + y_{t−1} = h_t`. -/
noncomputable def hvA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  p.θ * gvA E p r t ω + p.β * Ms E (fvA p R r) t ω - fvA p R r t ω

/-- The inverse, the forward factor `u = y − z₁ lag y`. -/
noncomputable def uvA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) : ℕ → Ω → ℝ :=
  fwdSA E (1 / z2 p) (fun t ω => -(1 / (p.β * z2 p)) * hvA E p R r t ω + 0 * 0)

/-- The inverse, output `y = z₁ lag y + u`. -/
noncomputable def yvA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) : ℕ → Ω → ℝ :=
  bwdS (z1 p) (uvA E p R r)

/-- The inverse, inflation `π = (f − y + lag y)/θ`. -/
noncomputable def pivA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (fvA p R r t ω - yvA E p R r t ω + lagS (yvA E p R r) t ω) / p.θ

/-- The inverse, `F̂` forward with root `αβ`. -/
noncomputable def FvA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) : ℕ → Ω → ℝ :=
  fwdSA E (p.α * p.β) (fun t ω => 1 * ((1 - p.α * p.β) * (1 - p.σ) * yvA E p R r t ω +
    p.α * p.β * (p.θ - 1) * Ms E (pivA E p R r) t ω) + 1 * r t ω 5)

/-- The inverse, the relative price `x̂`. -/
noncomputable def xvA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (p.α * (p.θ - 1) * pivA E p R r t ω - r t ω 7) / ((1 - p.α) * (p.θ - 1))

/-- The inverse, `λ̂₁` from the output condition. -/
noncomputable def l1vA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (r t ω 0 + R.Au * Gw p R * yvA E p R r t ω + (1 - R.Φ) * R.Au * DvA p r t ω +
    (1 - p.α * p.β) * (1 + p.ω) * MuvA p R r t ω) / ((1 - p.α * p.β) * (p.σ + p.ω))

/-- The inverse, `λ̂₄` forward with root `αβ`. -/
noncomputable def l4vA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) : ℕ → Ω → ℝ :=
  fwdSA E (p.α * p.β) (fun t ω => 1 * ((1 - R.Φ) * R.Au * yvA E p R r t ω +
    p.α * p.β * ramseyLam p R 3 * aE p * Ms E (pivA E p R r) t ω) + 1 * r t ω 4)

/-- The inverse, `λ̂₃` from the `F̂` condition. -/
noncomputable def l3vA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  (r t ω 2 - (l1vA E p R r t ω + ramseyLam p R 0 * FvA E p R r t ω -
    p.α * (lagS (l1vA E p R r) t ω + ramseyLam p R 0 * ((p.θ - 1) * pivA E p R r t ω +
      FvA E p R r t ω))) + (1 - p.α) * (aE p / p.c0) * (l4vA E p R r t ω -
        ramseyLam p R 3 * aE p * xvA E p R r t ω)) / ((1 - p.α) * ((p.θ - 1) / p.c0)) +
  ramseyLam p R 2 * (p.θ - 1) * xvA E p R r t ω

/-- Woodford (2003), Ch. 7 and App. A.3 (**the inverse of the linearised Ramsey operator,
a.s.**). -/
noncomputable def LinvRA (p : Par) (R : RPar) (r : ℕ → Ω → Fin 9 → ℝ) (t : ℕ) (ω : Ω) :
    Fin 9 → ℝ :=
  ![yvA E p R r t ω, pivA E p R r t ω, FvA E p R r t ω,
    FvA E p R r t ω + p.c0 * xvA E p R r t ω, DvA p r t ω, l1vA E p R r t ω,
    MuvA p R r t ω - l1vA E p R r t ω, l3vA E p R r t ω, l4vA E p R r t ω]

/-! ## Uniform a.s. bounds and adaptedness of the inverse -/

/-- Woodford (2003), App. A.3: every component of the forcing is adapted with `|r_t| ≤ A` a.s. -/
def RHyp (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ) : Prop := ∀ k, AdB E (fun t ω => r t ω k) 1 A

/-- The zero process. -/
theorem adb_zero (A : ℝ) : AdB E (fun _ _ => (0 : ℝ)) 0 A :=
  ⟨fun _ => aestronglyMeasurable_const, fun _ => Eventually.of_forall fun _ => by simp⟩

/-- Woodford (2003), App. A.3: the dispersion part of the inverse is `AdB`, uniformly. -/
theorem adb_DvA {p : Par} (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
    (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → RHyp E r A →
      AdB E (DvA p r) c A := by
  have h1 : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  refine ⟨(|aE p / (p.θ - 1)| * 1 + |1| * 1) / (1 - p.α), by positivity,
    fun E r A hA hr => ?_⟩
  exact adb_bwd E hp.α_pos.le hp.α_lt_one (by positivity) hA
    (adb_lin2 E (hr 7) (hr 8) (aE p / (p.θ - 1)) 1)

/-- Woodford (2003), App. A.3: the summed-multiplier part of the inverse is `AdB`. -/
theorem adb_MuvA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (MuvA p R r) c A := by
  have h1 : 0 < 1 - p.α := by linarith [hp.α_lt_one]
  set k := ramseyLam p R 0 * p.c0 / (p.θ - 1)
  refine ⟨(|1| * (|1| * 1 + |1| * 1) + |-k| * 1) / (1 - p.α), by positivity,
    fun E r A hA hr => ?_⟩
  exact adb_bwd E hp.α_pos.le hp.α_lt_one (by positivity) hA
    (adb_lin2 E (adb_lin2 E (hr 2) (hr 3) 1 1) (hr 7) 1 (-k))

/-- Woodford (2003), App. A.3: the NKPC forcing is `AdB`. -/
theorem adb_gvA (p : Par) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
    (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ), 0 ≤ A → RHyp E r A →
      AdB E (gvA E p r) c A := by
  set k1 := (1 - p.α) / (p.c0 * p.α)
  set k2 := 1 / (p.α * (p.θ - 1))
  refine ⟨|k1| * (|1| * 1 + |-1| * 1) + |k2| * (|1| * 1 + |-(p.α * p.β)| * 1), by positivity,
    fun E r A hA hr => ?_⟩
  refine (adb_lin2 E (adb_lin2 E (hr 6) (hr 5) 1 (-1))
    (adb_lin2 E (hr 7) (adb_Ms E (hr 7)) 1 (-(p.α * p.β))) k1 k2).congr E fun t ω => ?_
  simp only [gvA, k1, k2]; ring

/-- Woodford (2003), App. A.3: the targeting-rule forcing is `AdB`. -/
theorem adb_fvA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (fvA p R r) c A := by
  obtain ⟨cD, hcD, hD⟩ := adb_DvA hp
  obtain ⟨cM, hcM, hM⟩ := adb_MuvA R hp
  set s := (1 - p.α * p.β) * (p.σ + p.ω)
  set k0 := (1 - p.α) * aE p / p.c0
  set k7 := (p.c0 * ramseyLam p R 0 - aE p * ramseyLam p R 3) / (p.θ - 1)
  set k1 := (1 - p.α) / (p.α * p.c0)
  set Av := (1 - R.Φ) * R.Au
  set s2 := (1 - p.α * p.β) * (1 + p.ω)
  set c1 := |-k0| * (|1| * cM + |ramseyLam p R 3| * cD) + |-k7| * 1
  set c2 := |1| * c1 + |1| * (|1| * 1 + |-k1| * 1)
  set c3 := |1| * (|1| * 1 + |-1| * 1) + |Av| * (|1| * cD + |-1| * cD)
  set c4 := |s| * c2 + |-1| * (|1| * c3 + |s2| * (|1| * cM + |-1| * cM))
  refine ⟨|1 / (R.Au * Gw p R)| * c4 + |0| * 0, by positivity, fun E r A hA hr => ?_⟩
  have hDl := adb_lag E (by positivity) (hD E r A hA hr)
  have hMl := adb_lag E (by positivity) (hM E r A hA hr)
  have e1 := adb_lin2 E (adb_lin2 E hMl hDl 1 (ramseyLam p R 3)) (hr 7) (-k0) (-k7)
  have e2 := adb_lin2 E e1 (adb_lin2 E (hr 2) (hr 1) 1 (-k1)) 1 1
  have e3 := adb_lin2 E (hr 0) (adb_lag E (by positivity) (hr 0)) 1 (-1)
  have e4 := adb_lin2 E e3 (adb_lin2 E (hD E r A hA hr) hDl 1 (-1)) 1 Av
  have e5 := adb_lin2 E e4 (adb_lin2 E (hM E r A hA hr) hMl 1 (-1)) 1 s2
  have e6 := adb_lin2 E e2 e5 s (-1)
  refine (adb_lin2 E e6 (adb_zero E A) (1 / (R.Au * Gw p R)) 0).congr E fun t ω => ?_
  simp only [fvA, FtvA, s, k0, k7, k1, Av, s2]
  ring

/-- Woodford (2003), App. A.3: the forcing of the second-order output equation is `AdB`. -/
theorem adb_hvA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (hvA E p R r) c A := by
  obtain ⟨cg, hcg, hg⟩ := adb_gvA p
  obtain ⟨cf, hcf, hf⟩ := adb_fvA R hp
  refine ⟨|1| * (|p.θ| * cg + |p.β| * cf) + |-1| * cf, by positivity, fun E r A hA hr => ?_⟩
  refine (adb_lin2 E (adb_lin2 E (hg E r A hA hr) (adb_Ms E (hf E r A hA hr)) p.θ p.β)
    (hf E r A hA hr) 1 (-1)).congr E fun t ω => ?_
  simp only [hvA]; ring

/-- Woodford (2003), App. A.3: the forward factor `u` is `AdB` and solves
`u_t = (1/z₂)E_t u_{t+1} − h_t/(βz₂)` a.s. -/
theorem adb_uvA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (uvA E p R r) c A ∧ ∀ t, uvA E p R r t =ᵐ[E.μ]
        fun ω => 1 / z2 p * Ms E (uvA E p R r) t ω +
          (-(1 / (p.β * z2 p)) * hvA E p R r t ω + 0 * 0) := by
  obtain ⟨ch, hch, hh⟩ := adb_hvA R hp
  refine ⟨Sg (1 / z2 p) * (|-(1 / (p.β * z2 p))| * ch + |0| * 0), by
    have := Sg_nonneg (1 / z2 p); positivity, fun E r A hA hr => ?_⟩
  exact adb_fwd E (abs_inv_z2 hp) (by positivity) hA
    (adb_lin2 E (hh E r A hA hr) (adb_zero E A) (-(1 / (p.β * z2 p))) 0)

/-- Woodford (2003), App. A.3: output is `AdB`. -/
theorem adb_yvA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (yvA E p R r) c A := by
  obtain ⟨cu, hcu, hu⟩ := adb_uvA R hp
  obtain ⟨hz0, hz1, -, -, -⟩ := z_props hp
  have h1 : 0 < 1 - z1 p := by linarith
  exact ⟨cu / (1 - z1 p), by positivity, fun E r A hA hr =>
    adb_bwd E hz0.le hz1 hcu hA (hu E r A hA hr).1⟩

/-- Woodford (2003), App. A.3: inflation is `AdB`. -/
theorem adb_pivA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (pivA E p R r) c A := by
  obtain ⟨cf, hcf, hf⟩ := adb_fvA R hp
  obtain ⟨cy, hcy, hy⟩ := adb_yvA R hp
  refine ⟨|1 / p.θ| * (|1| * (|1| * cf + |-1| * cy) + |1| * cy) + |0| * 0, by positivity,
    fun E r A hA hr => ?_⟩
  have hY := hy E r A hA hr
  refine (adb_lin2 E (adb_lin2 E (adb_lin2 E (hf E r A hA hr) hY 1 (-1))
    (adb_lag E (by positivity) hY) 1 1) (adb_zero E A) (1 / p.θ) 0).congr E fun t ω => ?_
  simp only [pivA]; ring

/-- Woodford (2003), App. A.3: `F̂` is `AdB` and solves its forward equation a.s. -/
theorem adb_FvA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (FvA E p R r) c A ∧ ∀ t, FvA E p R r t =ᵐ[E.μ]
        fun ω => p.α * p.β * Ms E (FvA E p R r) t ω + (1 * ((1 - p.α * p.β) * (1 - p.σ) *
          yvA E p R r t ω + p.α * p.β * (p.θ - 1) * Ms E (pivA E p R r) t ω) + 1 * r t ω 5) := by
  obtain ⟨cy, hcy, hy⟩ := adb_yvA R hp
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivA R hp
  set k1 := (1 - p.α * p.β) * (1 - p.σ)
  set k2 := p.α * p.β * (p.θ - 1)
  refine ⟨Sg (p.α * p.β) * (|1| * (|k1| * cy + |k2| * cπ) + |1| * 1), by
    have := Sg_nonneg (p.α * p.β); positivity, fun E r A hA hr => ?_⟩
  exact adb_fwd E (abs_ab hp) (by positivity) hA (adb_lin2 E (adb_lin2 E (hy E r A hA hr)
    (adb_Ms E (hπ E r A hA hr)) k1 k2) (hr 5) 1 1)

/-- Woodford (2003), App. A.3: `λ̂₄` is `AdB` and solves its forward equation a.s. -/
theorem adb_l4vA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (l4vA E p R r) c A ∧ ∀ t, l4vA E p R r t =ᵐ[E.μ]
        fun ω => p.α * p.β * Ms E (l4vA E p R r) t ω + (1 * ((1 - R.Φ) * R.Au *
          yvA E p R r t ω + p.α * p.β * ramseyLam p R 3 * aE p * Ms E (pivA E p R r) t ω) +
            1 * r t ω 4) := by
  obtain ⟨cy, hcy, hy⟩ := adb_yvA R hp
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivA R hp
  set k1 := (1 - R.Φ) * R.Au
  set k2 := p.α * p.β * ramseyLam p R 3 * aE p
  refine ⟨Sg (p.α * p.β) * (|1| * (|k1| * cy + |k2| * cπ) + |1| * 1), by
    have := Sg_nonneg (p.α * p.β); positivity, fun E r A hA hr => ?_⟩
  exact adb_fwd E (abs_ab hp) (by positivity) hA (adb_lin2 E (adb_lin2 E (hy E r A hA hr)
    (adb_Ms E (hπ E r A hA hr)) k1 k2) (hr 4) 1 1)

/-- Woodford (2003), App. A.3: the relative price is `AdB`. -/
theorem adb_xvA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (xvA E p R r) c A := by
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivA R hp
  set k := 1 / ((1 - p.α) * (p.θ - 1))
  refine ⟨|k * (p.α * (p.θ - 1))| * cπ + |-k| * 1, by positivity, fun E r A hA hr => ?_⟩
  refine (adb_lin2 E (hπ E r A hA hr) (hr 7) (k * (p.α * (p.θ - 1))) (-k)).congr E
    fun t ω => ?_
  simp only [xvA, k]; ring

/-- Woodford (2003), App. A.3: `λ̂₁` is `AdB`. -/
theorem adb_l1vA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (l1vA E p R r) c A := by
  obtain ⟨cy, hcy, hy⟩ := adb_yvA R hp
  obtain ⟨cD, hcD, hD⟩ := adb_DvA hp
  obtain ⟨cM, hcM, hM⟩ := adb_MuvA R hp
  set k := 1 / ((1 - p.α * p.β) * (p.σ + p.ω))
  set c1 := |k| * 1 + |k * (R.Au * Gw p R)| * cy
  set c2 := |k * ((1 - R.Φ) * R.Au)| * cD + |k * ((1 - p.α * p.β) * (1 + p.ω))| * cM
  refine ⟨|1| * c1 + |1| * c2, by positivity, fun E r A hA hr => ?_⟩
  refine (adb_lin2 E (adb_lin2 E (hr 0) (hy E r A hA hr) k (k * (R.Au * Gw p R)))
    (adb_lin2 E (hD E r A hA hr) (hM E r A hA hr) (k * ((1 - R.Φ) * R.Au))
      (k * ((1 - p.α * p.β) * (1 + p.ω)))) 1 1).congr E fun t ω => ?_
  simp only [l1vA, k]; ring

/-- Woodford (2003), App. A.3: `λ̂₃` is `AdB`. -/
theorem adb_l3vA {p : Par} (R : RPar) (hp : p.Std) : ∃ c, 0 ≤ c ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → AdB E (l3vA E p R r) c A := by
  obtain ⟨c1, hc1, h1⟩ := adb_l1vA R hp
  obtain ⟨cF, hcF, hF⟩ := adb_FvA R hp
  obtain ⟨cπ, hcπ, hπ⟩ := adb_pivA R hp
  obtain ⟨c4, hc4, h4⟩ := adb_l4vA R hp
  obtain ⟨cx, hcx, hx⟩ := adb_xvA R hp
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
  simp only [l3vA, k, L0, ka, La, Lb]
  field_simp
  ring

/-! ## The inverse is a right inverse almost surely -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**`L(L⁻¹r) = r` a.s.**): for every adapted, a.s.
bounded forcing on every filtered probability space, the constructed process solves the
linearised Ramsey system a.s. at every date. -/
theorem LRA_LinvRA {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ) (hA : 0 ≤ A) (hr : RHyp E r A) (t : ℕ) :
    LRA E p R (LinvRA E p R r) t =ᵐ[E.μ] r t := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := z_props hp
  have hz2 : z2 p ≠ 0 := by linarith
  obtain ⟨_, _, hu⟩ := adb_uvA R hp
  obtain ⟨_, _, hF⟩ := adb_FvA R hp
  obtain ⟨_, _, h4⟩ := adb_l4vA R hp
  obtain ⟨_, _, hy⟩ := adb_yvA R hp
  obtain ⟨_, _, hπ⟩ := adb_pivA R hp
  obtain ⟨_, _, hf⟩ := adb_fvA R hp
  obtain ⟨_, _, hx⟩ := adb_xvA R hp
  have hY := hy E r A hA hr
  have hP := hπ E r A hA hr
  have hFf := hf E r A hA hr
  have Eu := (hu E r A hA hr).2
  have EF := (hF E r A hA hr).2
  have E4 := (h4 E r A hA hr).2
  have hX := hx E r A hA hr
  set v := LinvRA E p R r with hvdef
  set y := yvA E p R r
  set π := pivA E p R r
  set D := DvA p r
  set μ := MuvA p R r
  set f := fvA p R r
  have ED : ∀ s ω, D s ω = p.α * lagS D s ω + (aE p / (p.θ - 1) * r s ω 7 + 1 * r s ω 8) :=
    fun s ω => bwdS_eq _ _ s ω
  have EM : ∀ s ω, μ s ω = p.α * lagS μ s ω + (1 * (1 * r s ω 2 + 1 * r s ω 3) +
      -(ramseyLam p R 0 * p.c0 / (p.θ - 1)) * r s ω 7) := fun s ω => bwdS_eq _ _ s ω
  have Ey : ∀ s ω, y s ω = z1 p * lagS y s ω + uvA E p R r s ω := fun s ω => bwdS_eq _ _ s ω
  have E7 : ∀ s ω, p.α * (p.θ - 1) * π s ω - (1 - p.α) * (p.θ - 1) * xvA E p R r s ω =
      r s ω 7 := fun s ω => by simp only [xvA, π]; field_simp; ring
  have Et : ∀ s ω, y s ω - lagS y s ω + p.θ * π s ω = f s ω := fun s ω => by
    simp only [π, pivA]; field_simp; ring
  have EMy : Ms E (uvA E p R r) t =ᵐ[E.μ] fun ω => Ms E y t ω - z1 p * y t ω := by
    have e : uvA E p R r = fun s ω => 1 * y s ω + -z1 p * lagS y s ω := by
      funext s ω; rw [Ey s ω]; ring
    rw [e]
    filter_upwards [Ms_lin2 E hY (adb_lag E (by positivity) hY) 1 (-z1 p) t, Ms_lag E hY t]
      with ω h1 h2
    rw [h1, h2]; ring
  have EMπ : Ms E π t =ᵐ[E.μ] fun ω => (Ms E f t ω - Ms E y t ω + y t ω) / p.θ := by
    have e : π = fun s ω => (1 / p.θ) * (1 * f s ω + -1 * y s ω) + (1 / p.θ) * lagS y s ω := by
      funext s ω; simp only [π, pivA]; ring
    rw [e]
    filter_upwards [Ms_lin2 E (adb_lin2 E hFf hY 1 (-1)) (adb_lag E (by positivity) hY)
      (1 / p.θ) (1 / p.θ) t, Ms_lin2 E hFf hY 1 (-1) t, Ms_lag E hY t] with ω h1 h2 h3
    rw [h1, h2, h3]; field_simp; ring
  have Epc : ∀ᵐ ω ∂E.μ, π t ω = p.κ * y t ω + p.β * Ms E π t ω + gvA E p r t ω := by
    filter_upwards [Eu t, EMy, EMπ] with ω h1 h2 h3
    have hhv : hvA E p R r t ω = p.θ * gvA E p r t ω + p.β * Ms E f t ω - f t ω := rfl
    have hux : uvA E p R r t ω = y t ω - z1 p * lagS y t ω := by rw [Ey t ω]; ring
    rw [h3]
    have ht := Et t ω
    have key : p.β * Ms E y t ω - (1 + p.β + p.κ * p.θ) * y t ω + lagS y t ω =
        hvA E p R r t ω := by
      rw [h2, hux] at h1
      linear_combination (norm := (field_simp; ring)) (-(p.β * z2 p)) * h1 + y t ω * hzs -
        lagS y t ω * hzz
    rw [hhv] at key
    linear_combination (norm := (field_simp; ring)) (1 / p.θ) * ht + (1 / p.θ) * key
  -- the component functions of `v`
  have v0 : (fun s ω => v s ω 0) = y := by funext s ω; simp [hvdef, LinvRA, y]
  have v1 : (fun s ω => v s ω 1) = π := by funext s ω; simp [hvdef, LinvRA, π]
  have v2 : (fun s ω => v s ω 2) = FvA E p R r := by funext s ω; simp [hvdef, LinvRA]
  have v3 : (fun s ω => v s ω 3) = fun s ω => 1 * FvA E p R r s ω + p.c0 * xvA E p R r s ω := by
    funext s ω; simp [hvdef, LinvRA]
  have v4 : (fun s ω => v s ω 4) = D := by funext s ω; simp [hvdef, LinvRA, D]
  have v5 : (fun s ω => v s ω 5) = l1vA E p R r := by funext s ω; simp [hvdef, LinvRA]
  have v6 : (fun s ω => v s ω 6) = fun s ω => 1 * μ s ω + -1 * l1vA E p R r s ω := by
    funext s ω; simp [hvdef, LinvRA, μ]; ring
  have v7 : (fun s ω => v s ω 7) = l3vA E p R r := by funext s ω; simp [hvdef, LinvRA]
  have v8 : (fun s ω => v s ω 8) = l4vA E p R r := by funext s ω; simp [hvdef, LinvRA]
  have hl : ∀ s ω k, lagvS v s ω k = lagS (fun s' ω' => v s' ω' k) s ω := fun _ _ _ => rfl
  have hm : ∀ s ω k, MvA E v s ω k = Ms E (fun s' ω' => v s' ω' k) s ω := fun _ _ _ => rfl
  have hvx : ∀ s ω k, v s ω k = (fun s' ω' => v s' ω' k) s ω := fun _ _ _ => rfl
  have E0 : ∀ s ω, -(R.Au * Gw p R * y s ω) - (1 - R.Φ) * R.Au * D s ω +
      (1 - p.α * p.β) * (p.σ + p.ω) * l1vA E p R r s ω -
        (1 - p.α * p.β) * (1 + p.ω) * μ s ω = r s ω 0 := fun s ω => by
    simp only [l1vA, y, D, μ]; field_simp; ring
  set Rr : ℕ → Ω → Fin 9 → ℝ :=
    fun s ω => DQr p R (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω) with hRr
  have c7 : ∀ s ω, Rr s ω 7 = r s ω 7 := fun s ω => by
    change (DQr p R (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) 7 = r s ω 7
    rw [red_x, hvx s ω 1, hvx s ω 2, hvx s ω 3, v1, v2, v3]
    simp only
    rw [← E7 s ω]; field_simp; ring
  have c8 : ∀ s ω, Rr s ω 8 = r s ω 8 := fun s ω => by
    simp only [hRr, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl s ω 4, hvx s ω 1, hvx s ω 2, hvx s ω 3, hvx s ω 4, v1, v2, v3, v4]
    simp only
    linear_combination (norm := (field_simp; ring)) ED s ω - aE p / (p.θ - 1) * E7 s ω
  have c5 : ∀ᵐ ω ∂E.μ, Rr t ω 5 = r t ω 5 := by
    filter_upwards [EF t] with ω h
    simp only [hRr, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm t ω 1, hm t ω 2, hvx t ω 0, hvx t ω 2, v0, v1, v2]
    linear_combination h
  have c4 : ∀ᵐ ω ∂E.μ, Rr t ω 4 = r t ω 4 := by
    filter_upwards [E4 t] with ω h
    simp only [hRr, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hm t ω 1, hm t ω 8, hvx t ω 0, hvx t ω 8, v0, v1, v8]
    linear_combination h
  have c0 : ∀ s ω, Rr s ω 0 = r s ω 0 := fun s ω => by
    change (DQr p R (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) 0 = r s ω 0
    rw [← red_l1 R hp, hvx s ω 0, hvx s ω 4, hvx s ω 5, hvx s ω 6, v0, v4, v5, v6]
    simp only
    linear_combination E0 s ω
  have c2 : ∀ s ω, Rr s ω 2 = r s ω 2 := fun s ω => by
    simp only [hRr, DQr, DNr, Pi.add_apply, Matrix.cons_val]
    rw [hl s ω 5, hvx s ω 1, hvx s ω 2, hvx s ω 3, hvx s ω 5, hvx s ω 7, hvx s ω 8, v1, v2, v3,
      v5, v7, v8]
    simp only [l3vA]
    field_simp
    ring
  have hlag56 : ∀ s ω, lagS (fun s' ω' => 1 * μ s' ω' + -1 * l1vA E p R r s' ω') s ω =
      lagS μ s ω - lagS (l1vA E p R r) s ω := fun s ω => by
    cases s <;> simp [lagS]; ring
  have c3 : ∀ s ω, Rr s ω 3 = r s ω 3 := fun s ω => by
    have h := red_mu R hp (lagvS v s ω) (v s ω) (MvA E v s ω)
    rw [hl s ω 5, hl s ω 6, hvx s ω 5, hvx s ω 6, v5, v6, hlag56] at h
    simp only at h
    have h2 := c2 s ω
    have h7 := c7 s ω
    simp only [hRr] at h2 h7 ⊢
    rw [h2, h7] at h
    linear_combination (-1 : ℝ) * h + EM s ω
  have hm7 : Ms E (fun s ω => r s ω 7) t =ᵐ[E.μ] fun ω => p.α * (p.θ - 1) * Ms E π t ω -
      (1 - p.α) * (p.θ - 1) * ((1 * Ms E (FvA E p R r) t ω + p.c0 * Ms E (xvA E p R r) t ω -
        Ms E (FvA E p R r) t ω) / p.c0) := by
    have e : (fun s ω => r s ω 7) = fun s ω => (p.α * (p.θ - 1)) * π s ω +
        (-(1 - p.α) * (p.θ - 1)) * xvA E p R r s ω := by
      funext s ω; rw [← E7 s ω]; ring
    rw [e]
    filter_upwards [Ms_lin2 E hP hX (p.α * (p.θ - 1)) (-(1 - p.α) * (p.θ - 1)) t] with ω h
    rw [h]; field_simp; ring
  have c6 : ∀ᵐ ω ∂E.μ, Rr t ω 6 = r t ω 6 := by
    have hFF := (hF E r A hA hr).1
    filter_upwards [hm7, Epc, Ms_lin2 E hFF hX 1 p.c0 t, c5] with ω hm7' hg hlin h5
    have h := red_pc R hp (lagvS v t ω) (v t ω) (MvA E v t ω)
    have h7 := c7 t ω
    simp only [hRr] at h5 h7 ⊢
    rw [h5, h7, hm t ω 1, hm t ω 2, hm t ω 3, hvx t ω 0, hvx t ω 1, v0, v1, v2, v3, hlin,
      ← hm7'] at h
    simp only [gvA] at hg
    have hk : (1 - p.α) / (p.c0 * p.α) ≠ 0 := div_ne_zero h1α (mul_ne_zero hc0 hα)
    have key : (1 - p.α) / (p.c0 * p.α) *
        ((DQr p R (lagvS v t ω) (v t ω) + DNr p R (MvA E v t ω)) 6 - r t ω 6) = 0 := by
      linear_combination hg - h
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  have c1 : ∀ s ω, Rr s ω 1 = r s ω 1 := fun s ω => by
    have h0m : -(R.Au * Gw p R * lagvS v s ω 0) - (1 - R.Φ) * R.Au * lagvS v s ω 4 +
        (1 - p.α * p.β) * (p.σ + p.ω) * lagvS v s ω 5 -
          (1 - p.α * p.β) * (1 + p.ω) * (lagvS v s ω 5 + lagvS v s ω 6) =
            lagS (fun s' ω' => r s' ω' 0) s ω := by
      cases s with
      | zero => simp [lagvS, lagS]
      | succ s =>
        have := c0 s ω
        change (DQr p R (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) 0 = r s ω 0 at this
        rw [← red_l1 R hp] at this
        exact this
    have h := red_target R hp (lagvS v s ω) (v s ω) (MvA E v s ω) _ h0m
    have h2 := c2 s ω
    have h7 := c7 s ω
    have h0 := c0 s ω
    simp only [hRr] at h2 h7 h0 ⊢
    rw [h2, h7, h0, hl s ω 0, hl s ω 4, hl s ω 5, hl s ω 6, hvx s ω 0, hvx s ω 1, hvx s ω 4,
      hvx s ω 5, hvx s ω 6, v0, v1, v4, v5, v6, hlag56] at h
    simp only at h
    have ht := Et s ω
    have hF : R.Au * Gw p R * f s ω = FtvA p R r s ω := by
      rw [show f s ω = FtvA p R r s ω / (R.Au * Gw p R) from rfl, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hG
    simp only [FtvA] at hF
    have hk : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hab hωσ) (div_ne_zero h1α (mul_ne_zero hα hc0))
    have key : (1 - p.α * p.β) * (p.σ + p.ω) * ((1 - p.α) / (p.α * p.c0)) *
        ((DQr p R (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) 1 - r s ω 1) = 0 := by
      linear_combination h - R.Au * Gw p R * ht - hF
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' hk
    · linarith
  filter_upwards [c4, c5, c6] with ω h4' h5' h6'
  funext i
  fin_cases i
  exacts [c0 t ω, c1 t ω, c2 t ω, c3 t ω, h4', h5', h6', c7 t ω, c8 t ω]

/-! ## Injectivity on adapted processes -/

/-- The forecast of an a.s. zero process is a.s. zero. -/
theorem Ms_zero {f : ℕ → Ω → ℝ} {t : ℕ} (h : f (t + 1) =ᵐ[E.μ] 0) : Ms E f t =ᵐ[E.μ] 0 := by
  have := E.E_congr h t
  rw [E.E_zero] at this; exact this

/-- The lag of an a.s. zero process is a.s. zero. -/
theorem lagS_zero {f : ℕ → Ω → ℝ} (h : ∀ t, f t =ᵐ[E.μ] 0) (t : ℕ) : lagS f t =ᵐ[E.μ] 0 := by
  cases t with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ t => exact h t

/-- Woodford (2003), Ch. 7 and App. A.3 (**injectivity on adapted processes, a.s.**): an adapted,
a.s. bounded solution of the homogeneous linearised Ramsey system with zero initial lag is `0`
a.s. at every date. -/
theorem LRA_inj {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    (v : ℕ → Ω → Fin 9 → ℝ) (B : ℝ) (hB : 0 ≤ B) (hv : RHyp E v B)
    (h0 : ∀ t, LRA E p R v t =ᵐ[E.μ] 0) (t : ℕ) : v t =ᵐ[E.μ] 0 := by
  have hθ : p.θ - 1 ≠ 0 := by linarith [hp.one_lt_θ]
  have hθ0 : p.θ ≠ 0 := by linarith [hp.one_lt_θ]
  have hc0 := hp.c0_pos.ne'
  have hα := hp.α_pos.ne'
  have h1α : 1 - p.α ≠ 0 := by linarith [hp.α_lt_one]
  have hab : 1 - p.α * p.β ≠ 0 := by linarith [hp.ab_lt_one]
  have hωσ : p.σ + p.ω ≠ 0 := by linarith [hp.ω_nonneg, hp.σ_pos]
  have hβ := hp.β_pos.ne'
  obtain ⟨hz10, hz11, hz21, hzz, hzs⟩ := z_props hp
  have hz2 : z2 p ≠ 0 := by linarith
  have hRk : ∀ s, ∀ᵐ ω ∂E.μ, ∀ k,
      (DQr p R (lagvS v s ω) (v s ω) + DNr p R (MvA E v s ω)) k = 0 := fun s => by
    filter_upwards [h0 s] with ω h k
    exact congrFun h k
  set c : Fin 9 → ℕ → Ω → ℝ := fun k s ω => v s ω k with hc
  have hl : ∀ s ω k, lagvS v s ω k = lagS (c k) s ω := fun _ _ _ => rfl
  have hm : ∀ s ω k, MvA E v s ω k = Ms E (c k) s ω := fun _ _ _ => rfl
  have hvx : ∀ s ω k, v s ω k = c k s ω := fun _ _ _ => rfl
  -- the predetermined block
  have hD : ∀ s, c 4 s =ᵐ[E.μ] 0 := zero_of_eq_lagS E (c := p.α) fun s => by
    filter_upwards [hRk s] with ω h
    have := red_D R hp (lagvS v s ω) (v s ω) (MvA E v s ω)
    rw [h 7, h 8, hl] at this; simpa using this
  have hμ : ∀ s, (fun ω => c 5 s ω + c 6 s ω) =ᵐ[E.μ] 0 := zero_of_eq_lagS E (c := p.α)
    (g := fun s ω => c 5 s ω + c 6 s ω) fun s => by
      filter_upwards [hRk s] with ω h
      have := red_mu R hp (lagvS v s ω) (v s ω) (MvA E v s ω)
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
    rw [← h 7, red_x]
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
  have h0m : ∀ s, ∀ᵐ ω ∂E.μ, -(R.Au * Gw p R * lagvS v s ω 0) -
      (1 - R.Φ) * R.Au * lagvS v s ω 4 + (1 - p.α * p.β) * (p.σ + p.ω) * lagvS v s ω 5 -
        (1 - p.α * p.β) * (1 + p.ω) * (lagvS v s ω 5 + lagvS v s ω 6) = 0 := fun s => by
    cases s with
    | zero => exact Eventually.of_forall fun ω => by simp [lagvS, lagS]
    | succ s =>
      filter_upwards [hRk s] with ω h
      have := red_l1 R hp (lagvS v s ω) (v s ω) (MvA E v s ω)
      rw [h 0] at this; exact this
  have hcs : ∀ s, ∀ᵐ ω ∂E.μ, _ := fun s => by
    filter_upwards [hRk s, h0m s, hm7 s] with ω h1 h2 h3
    exact commitment_system R hp (lagvS v s ω) (v s ω) (MvA E v s ω) (funext h1) h2 h3
  have Et : ∀ s, ∀ᵐ ω ∂E.μ, c 0 s ω - lagS (c 0) s ω + p.θ * c 1 s ω = 0 := fun s => by
    filter_upwards [hcs s, hDl s, hμl s] with ω h1 h2 h3
    obtain ⟨-, -, -, h4⟩ := h1
    rw [hl, hl, hl, hl] at h4
    simp only [Pi.zero_apply] at h2 h3
    rw [h2, h3] at h4
    simp only [mul_zero, add_zero, sub_zero] at h4
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hG
    · simp only [hc]; linarith
  have Epc : ∀ s, ∀ᵐ ω ∂E.μ, c 1 s ω = p.κ * c 0 s ω + p.β * Ms E (c 1) s ω := fun s => by
    filter_upwards [hcs s] with ω h
    obtain ⟨-, -, h3, -⟩ := h
    rw [hm] at h3; exact h3
  have hMπ : ∀ s, Ms E (c 1) s =ᵐ[E.μ] fun ω => (-1 / p.θ) * (Ms E (c 0) s ω - c 0 s ω) :=
    fun s => by
      have hπe : c 1 (s + 1) =ᵐ[E.μ] fun ω => (-1 / p.θ) * c 0 (s + 1) ω +
          (1 / p.θ) * lagS (c 0) (s + 1) ω := by
        filter_upwards [Et (s + 1)] with ω h
        field_simp; linarith
      have h1 : Ms E (c 1) s =ᵐ[E.μ] Ms E (fun s' ω => (-1 / p.θ) * c 0 s' ω +
          (1 / p.θ) * lagS (c 0) s' ω) s := E.E_congr hπe s
      filter_upwards [h1, Ms_lin2 E (hv 0) (adb_lag E (by positivity) (hv 0)) (-1 / p.θ)
        (1 / p.θ) s, Ms_lag E (hv 0) s] with ω h2 h3 h4
      rw [h2, h3, h4]; ring
  have key : ∀ s, ∀ᵐ ω ∂E.μ,
      p.β * Ms E (c 0) s ω - (1 + p.β + p.κ * p.θ) * c 0 s ω + lagS (c 0) s ω = 0 := fun s => by
    filter_upwards [Epc s, hMπ s, Et s] with ω h1 h2 h3
    rw [h2] at h1
    linear_combination (norm := (field_simp; ring)) p.θ * h1 - h3
  -- the stable factorisation
  have hu : ∀ s, (fun ω => c 0 s ω - z1 p * lagS (c 0) s ω) =ᵐ[E.μ] 0 := by
    have hU := adb_lin2 E (hv 0) (adb_lag E (by positivity) (hv 0)) 1 (-z1 p)
    have hz := zero_of_eq_cMs E (abs_inv_z2 hp) (g := fun s ω => 1 * c 0 s ω + -z1 p *
      lagS (c 0) s ω) (B := (|1| * 1 + |-z1 p| * 1) * B) hU.2 (fun s => by
        filter_upwards [Ms_lin2 E (hv 0) (adb_lag E (by positivity) (hv 0)) 1 (-z1 p) s,
          Ms_lag E (hv 0) s, key s] with ω h1 h2 h3
        rw [h1, h2]
        linear_combination (norm := (field_simp; ring)) (-1 / (p.β * z2 p)) * h3 +
          (c 0 s ω / (p.β * z2 p)) * hzs - (lagS (c 0) s ω / (p.β * z2 p)) * hzz)
    intro s
    filter_upwards [hz s] with ω h
    simp only [Pi.zero_apply] at h ⊢
    linarith
  have hy0 : ∀ s, c 0 s =ᵐ[E.μ] 0 := zero_of_eq_lagS E (c := z1 p) fun s => by
    filter_upwards [hu s] with ω h
    simp only [Pi.zero_apply] at h
    linarith
  have hπ0 : ∀ s, c 1 s =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [Et s, hy0 s, lagS_zero E hy0 s] with ω h1 h2 h3
    simp only [Pi.zero_apply] at h2 h3 ⊢
    rw [h2, h3] at h1
    have h4 : p.θ * c 1 s ω = 0 := by linarith
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd h hθ0
    · exact h
  have hF0 : ∀ s, c 2 s =ᵐ[E.μ] 0 := by
    refine zero_of_eq_cMs E (abs_ab hp) (g := c 2) (B := 1 * B) (hv 2).2 fun s => ?_
    filter_upwards [hRk s, hy0 s, Ms_zero E (t := s) (hπ0 (s + 1))] with ω h h1 h2
    have := h 5
    simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, hm] at this
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
    have := red_l1 R hp (lagvS v s ω) (v s ω) (MvA E v s ω)
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
    simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, hm] at this
    simp only [Pi.zero_apply] at h1 h2
    rw [hvx, hvx] at this
    rw [h1, h2] at this
    linear_combination this
  have hl30 : ∀ s, c 7 s =ᵐ[E.μ] 0 := fun s => by
    filter_upwards [hRk s, hπ0 s, hF0 s, hK0 s, hl10 s, hl40 s, lagS_zero E hl10 s] with ω h
      h1 h2 h3 h4 h5 h6
    have := h 2
    simp only [DQr, DNr, Pi.add_apply, Matrix.cons_val, hl] at this
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
theorem adb_LinvRA {p : Par} (R : RPar) (hp : p.Std) : ∃ K, 0 ≤ K ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → ∀ k, AdB E (fun t ω => LinvRA E p R r t ω k) K A := by
  obtain ⟨c0, h0, b0⟩ := adb_yvA R hp
  obtain ⟨c1, h1, b1⟩ := adb_pivA R hp
  obtain ⟨c2, h2, b2⟩ := adb_FvA R hp
  obtain ⟨cx, hx, bx⟩ := adb_xvA R hp
  obtain ⟨c4, h4, b4⟩ := adb_DvA hp
  obtain ⟨c5, h5, b5⟩ := adb_l1vA R hp
  obtain ⟨cμ, hμ, bμ⟩ := adb_MuvA R hp
  obtain ⟨c7, h7, b7⟩ := adb_l3vA R hp
  obtain ⟨c8, h8, b8⟩ := adb_l4vA R hp
  set K := c0 + c1 + c2 + (|1| * c2 + |p.c0| * cx) + c4 + c5 + (|1| * cμ + |-1| * c5) + c7 +
    c8 with hK
  refine ⟨K, by positivity, fun E r A hA hr k => ?_⟩
  have hle : ∀ c, 0 ≤ c → c ≤ K → ∀ f, AdB E f c A → AdB E f K A := fun c _ hcK f hf =>
    hf.mono E hcK hA
  have hs3 : 0 ≤ |1| * c2 + |p.c0| * cx := by positivity
  have hs6 : 0 ≤ |1| * cμ + |-1| * c5 := by positivity
  fin_cases k
  · exact hle _ h0 (by rw [hK]; linarith) _ ((b0 E r A hA hr).congr E fun t ω => by simp [LinvRA])
  · exact hle _ h1 (by rw [hK]; linarith) _ ((b1 E r A hA hr).congr E fun t ω => by simp [LinvRA])
  · exact hle _ h2 (by rw [hK]; linarith) _ (((b2 E r A hA hr).1).congr E fun t ω => by
      simp [LinvRA])
  · exact hle _ (by positivity) (by rw [hK]; linarith) _
      ((adb_lin2 E (b2 E r A hA hr).1 (bx E r A hA hr) 1 p.c0).congr E
        fun t ω => by simp [LinvRA])
  · exact hle _ h4 (by rw [hK]; linarith) _ ((b4 E r A hA hr).congr E fun t ω => by simp [LinvRA])
  · exact hle _ h5 (by rw [hK]; linarith) _ ((b5 E r A hA hr).congr E fun t ω => by simp [LinvRA])
  · exact hle _ (by positivity) (by rw [hK]; linarith) _
      ((adb_lin2 E (bμ E r A hA hr) (b5 E r A hA hr) 1 (-1)).congr E
        fun t ω => by simp [LinvRA]; ring)
  · exact hle _ h7 (by rw [hK]; linarith) _ ((b7 E r A hA hr).congr E fun t ω => by simp [LinvRA])
  · exact hle _ h8 (by rw [hK]; linarith) _ (((b8 E r A hA hr).1).congr E fun t ω => by
      simp [LinvRA])

/-- Rescaling the constant of `AdB` into the bound. -/
theorem AdB.rescale {f : ℕ → Ω → ℝ} {c A : ℝ} (h : AdB E f c A) : AdB E f 1 (c * A) :=
  ⟨h.1, fun t => by filter_upwards [h.2 t] with ω hω; simpa using hω⟩

/-- Sup-norm bounds from componentwise bounds. -/
theorem norm_of_rhyp {v : ℕ → Ω → Fin 9 → ℝ} {A : ℝ} (hA : 0 ≤ A) (hv : RHyp E v A) (t : ℕ) :
    ∀ᵐ ω ∂E.μ, ‖v t ω‖ ≤ A := by
  filter_upwards [ae_all_iff.2 fun k => (hv k).2 t] with ω h
  refine (pi_norm_le_iff_of_nonneg hA).2 fun k => ?_
  rw [Real.norm_eq_abs]; simpa using h k

/-- Woodford (2003), App. A.3: the linearised operator maps adapted bounded processes to adapted
bounded processes, `|(Lv)_t| ≤ ‖DLin‖·B`. -/
theorem rhyp_LRA {p : Par} (R : RPar) {v : ℕ → Ω → Fin 9 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : RHyp E v B) :
    RHyp E (LRA E p R v) (‖LinearMap.toContinuousLinearMap (DLin p R)‖ * B) := by
  have hl : ∀ k, AdB E (fun t ω => lagvS v t ω k) 1 B := fun k =>
    adb_lag E (by positivity) (hv k)
  have hm : ∀ k, AdB E (fun t ω => MvA E v t ω k) 1 B := fun k => adb_Ms E (hv k)
  intro k
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have hq : AEStronglyMeasurable[E.𝓕 t] (fun ω => (lagvS v t ω, v t ω, MvA E v t ω)) E.μ :=
      (aesmSub_vec fun i => (hl i).1 t).prodMk
        ((aesmSub_vec fun i => (hv i).1 t).prodMk (aesmSub_vec fun i => (hm i).1 t))
    have hc : Continuous fun q : (Fin 9 → ℝ) × (Fin 9 → ℝ) × (Fin 9 → ℝ) => DLin p R q k :=
      (continuous_apply k).comp (DLin p R).continuous_of_finiteDimensional
    have e : (fun ω => LRA E p R v t ω k) =
        fun ω => DLin p R (lagvS v t ω, v t ω, MvA E v t ω) k := rfl
    change AEStronglyMeasurable[E.𝓕 t] (fun ω => LRA E p R v t ω k) E.μ
    rw [e]
    exact hc.comp_aestronglyMeasurable hq
  · filter_upwards [norm_of_rhyp E hB hl t, norm_of_rhyp E hB hv t, norm_of_rhyp E hB hm t]
      with ω h1 h2 h3
    have := (norm_le_pi_norm (LRA E p R v t ω) k).trans (norm_DLin_le p R _ _ _ h1 h2 h3)
    rw [Real.norm_eq_abs] at this
    simpa using this

/-- Woodford (2003), App. A.3: the linearised operator is a.s. subtractive. -/
theorem LRA_sub {p : Par} (R : RPar) {v w : ℕ → Ω → Fin 9 → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hv : RHyp E v B) (hw : RHyp E w B) (t : ℕ) :
    LRA E p R (fun s ω => v s ω - w s ω) t =ᵐ[E.μ] fun ω => LRA E p R v t ω - LRA E p R w t ω := by
  have hG : ∀ {u : ℕ → Ω → Fin 9 → ℝ}, RHyp E u B → Gd E u := fun hu s =>
    aesm_vec E fun k => (hu k).aesm E s
  filter_upwards [MvA_sub E (hG hv) (hG hw) (fun s => norm_of_rhyp E hB hv s)
    (fun s => norm_of_rhyp E hB hw s) t] with ω hm
  have hl : lagvS (fun s ω => v s ω - w s ω) t ω = lagvS v t ω - lagvS w t ω := by
    funext i; cases t <;> simp [lagvS, lagS]
  have e := (DLin p R).map_sub (lagvS v t ω, v t ω, MvA E v t ω) (lagvS w t ω, w t ω, MvA E w t ω)
  simp only [DLin, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_sub_mk] at e
  simp only [LRA, hl, hm]
  exact e

/-- `RHyp` with a larger bound. -/
theorem rhyp_mono {v : ℕ → Ω → Fin 9 → ℝ} {A A' : ℝ} (hv : RHyp E v A) (h : A ≤ A') :
    RHyp E v A' := fun k =>
  ⟨(hv k).1, fun t => by filter_upwards [(hv k).2 t] with ω hω; linarith⟩

/-- Differences of `RHyp` processes. -/
theorem rhyp_sub {v w : ℕ → Ω → Fin 9 → ℝ} {A : ℝ} (hv : RHyp E v A) (hw : RHyp E w A) :
    RHyp E (fun t ω => v t ω - w t ω) (2 * A) := fun k => by
  have := (adb_lin2 E (hv k) (hw k) 1 (-1)).rescale E
  refine ⟨fun t => ?_, fun t => ?_⟩
  · exact ((hv k).1 t).sub ((hw k).1 t)
  · filter_upwards [this.2 t] with ω hω
    simp only [abs_one, abs_neg, one_mul, neg_mul, ← sub_eq_add_neg] at hω
    simp only [Pi.sub_apply]
    linarith

/-- The inverse of an `RHyp` forcing is `RHyp` with the uniform constant. -/
theorem rhyp_LinvRA {p : Par} (R : RPar) (hp : p.Std) : ∃ K, 0 ≤ K ∧ ∀ {Ω : Type*}
    [MeasurableSpace Ω] (E : MeasExpectationSystem Ω) (r : ℕ → Ω → Fin 9 → ℝ) (A : ℝ),
      0 ≤ A → RHyp E r A → RHyp E (LinvRA E p R r) (K * A) := by
  obtain ⟨K, hK, h⟩ := adb_LinvRA R hp
  exact ⟨K, hK, fun E r A hA hr k => (h E r A hA hr k).rescale E⟩

/-- Woodford (2003), App. A.3 (**the left inverse a.s.**): `L⁻¹(Lv) = v` a.s. for adapted,
a.s. bounded `v`. -/
theorem LinvRA_LRA {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    {v : ℕ → Ω → Fin 9 → ℝ} {B : ℝ} (hB : 0 ≤ B) (hv : RHyp E v B) (t : ℕ) :
    LinvRA E p R (LRA E p R v) t =ᵐ[E.μ] v t := by
  obtain ⟨K, hK, hKr⟩ := rhyp_LinvRA R hp
  set CL := ‖LinearMap.toContinuousLinearMap (DLin p R)‖
  have hL := rhyp_LRA E (p := p) R hB hv
  have hw := hKr E _ _ (by positivity) hL
  set M := B + K * (CL * B)
  have hKC : 0 ≤ K * (CL * B) := by positivity
  have hvM := rhyp_mono E hv (show B ≤ M by linarith)
  have hwM := rhyp_mono E hw (show K * (CL * B) ≤ M by linarith)
  have hd := rhyp_sub E hvM hwM
  have hz := LRA_inj E R hp hG (fun s ω => v s ω - LinvRA E p R (LRA E p R v) s ω) (2 * M)
    (by positivity) hd (fun s => by
      filter_upwards [LRA_sub E R (by positivity) hvM hwM s,
        LRA_LinvRA E R hp hG (LRA E p R v) _ (by positivity) hL s] with ω h1 h2
      rw [h1, h2, sub_self]; rfl) t
  filter_upwards [hz] with ω h
  exact (sub_eq_zero.1 (by simpa using h)).symm

/-- Woodford (2003), App. A.3: the inverse is a.s. subtractive. -/
theorem LinvRA_sub {p : Par} (R : RPar) (hp : p.Std) (hG : R.Au * Gw p R ≠ 0)
    {r r' : ℕ → Ω → Fin 9 → ℝ} {A : ℝ} (hA : 0 ≤ A) (hr : RHyp E r A) (hr' : RHyp E r' A)
    (t : ℕ) : LinvRA E p R (fun s ω => r s ω - r' s ω) t =ᵐ[E.μ]
      fun ω => LinvRA E p R r t ω - LinvRA E p R r' t ω := by
  obtain ⟨K, hK, hKr⟩ := rhyp_LinvRA R hp
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
  have hz := LRA_inj E R hp hG (fun s ω => LinvRA E p R (fun s ω => r s ω - r' s ω) s ω -
    (LinvRA E p R r s ω - LinvRA E p R r' s ω)) (2 * (2 * M)) (by positivity)
    (rhyp_sub E h1M' h23) (fun s => by
      filter_upwards [LRA_sub E R (by positivity) h1M' h23 s, LRA_sub E R (by positivity) h2M
        h3M s, LRA_LinvRA E R hp hG _ _ (by positivity) hrd s,
        LRA_LinvRA E R hp hG _ _ hA hr s, LRA_LinvRA E R hp hG _ _ hA hr' s] with ω e1 e2 e3 e4 e5
      rw [e1, e2, e3, e4, e5]
      simp) t
  filter_upwards [hz] with ω h
  simp only [Pi.zero_apply] at h
  exact sub_eq_zero.1 h

end Woodford.StabilizationWelfare.NonlinearNKMarkovRamseyAE
