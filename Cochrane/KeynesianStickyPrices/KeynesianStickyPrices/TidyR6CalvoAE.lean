/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6CalvoBound

/-!
# The Calvo Phillips curve under almost-sure bounds

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, eq. (17.17), p. 407, and
Chapter 5, §5.1, p. 118 ("a random probability of being allowed to change price").

TidyR6CalvoPC proves `calvo_iff_PC` with output gap and inflation bounded by `L` **everywhere**,
reset prices bounded everywhere and the Calvo index holding at every state. Every object in the
statement (the reset objective, conditional expectations, the Phillips curve) only sees its
arguments up to null sets, so these hypotheses can be weakened to **almost-sure** ones.

## The clipping argument

At each date the event `good_t` = {`|x_t| ≤ L`, `|π_t| ≤ L`, `|r_t| ≤ Lr`, index at `t`} is
`𝓕_t`-measurable (`goodSet_meas`). The clipped processes (`clip`) equal the originals on
`good_t` and are `0` off it; the zero triple satisfies all the everywhere hypotheses
(`clip_bounded`, `clip_index`), and the clipped processes are still adapted (`clip_adapted`).
Since each `good_t` has full measure, the clipped and original processes agree at **all** dates
outside one null set (`ae_clip_eq`), and every object of the Calvo problem transfers
(`aW_bW_eq` … `calvoRem_congr`, `resetOpt_congr`, `pcm_congr`).

## Main results

* `calvo_iff_PC_ae`: `TidyR6CalvoPC.calvo_iff_PC` with almost-sure bounds and an almost-sure index.
* `calvoRem_abs_le_ae`: `TidyR6CalvoBound.calvoRem_abs_le` under the same almost-sure hypotheses.
* `unbounded_solves`: the uniform bound **cannot simply be dropped**: for `0 < δ < 1`,
  `G_t = δ^{−t}` is a nonzero, unbounded solution of the reset-gap equation
  `G_t = δE_tG_{t+1}`, so the sufficiency step (the bounded forward solution of that equation is
  zero, `MeasExpectationSystem.forward_unique`) fails without boundedness.

## Where boundedness is used, and why integrability is not enough

The uniform (a.s.) bound `L` with `δe^{ηL} < 1` is used for three things: (i) pathwise
convergence and integrability of the discounted weights `W_A = ∑ δᵏa_{t,k}`,
`W_B = ∑ δᵏb_{t,k}`, which contain `e^{η(p_{t+k} − p_t)}`, an exponential of a **sum** of
inflation rates (integrability of each `π_t` does not make `E e^{η∑π}` finite, and then `F_t`,
`K_t` and the optimal reset price are not defined); (ii) boundedness of `f_t`, `k_t` and the reset
gap, which is what makes the gap equation's solution unique (`unbounded_solves` shows that
uniqueness genuinely needs it); (iii) integrability of the index remainder. A hypothesis of mere
integrability therefore does not suffice for the statement; almost-sure bounds do.

The aggregation of the reset prices into the price index over a continuum of firms (a law of
large numbers across firms, TidyR6CalvoReset's `cohort` recursion) stays out of scope: the index
is assumed, here almost surely.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6CalvoAE

open MeasureTheory ProbabilityTheory Filter Topology TidyR5ExpectationsMeasure
open TidyR6HouseholdMeasure TidyR6CalvoReset TidyR6EulerIS TidyR6RotembergPC TidyR6CalvoPC
open TidyR6CalvoBound

variable {Ω : Type*} [MeasurableSpace Ω] {S : MeasExpectationSystem Ω}

/-! ### Clipping -/

/-- Cochrane (2023), p. 118 and p. 421: the closed set of admissible values
`|x| ≤ L`, `|π| ≤ L`, `|r| ≤ Lr`, `αe^{(ε−1)π} + (1 − α)e^{(1−ε)r} = 1`. -/
def goodK (p : CalvoPar) (L Lr : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {v | |v.1| ≤ L ∧ |v.2.1| ≤ L ∧ |v.2.2| ≤ Lr ∧
    p.α * Real.exp ((p.ε - 1) * v.2.1) + (1 - p.α) * Real.exp ((1 - p.ε) * v.2.2) = 1}

/-- Cochrane (2023), p. 118: the event `good_t` that the date-`t` values are admissible. -/
def goodSet (p : CalvoPar) (L Lr : ℝ) (x π r : ℕ → Ω → ℝ) (t : ℕ) : Set Ω :=
  (fun ω => (x t ω, π t ω, r t ω)) ⁻¹' goodK p L Lr

/-- Cochrane (2023), p. 118: a process clipped to zero off the events `G t`. -/
noncomputable def clip (G : ℕ → Set Ω) (y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t => (G t).indicator (y t)

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: membership in `good_t`. -/
theorem mem_goodSet {p : CalvoPar} {L Lr : ℝ} {x π r : ℕ → Ω → ℝ} {t : ℕ} {ω : Ω} :
    ω ∈ goodSet p L Lr x π r t ↔ |x t ω| ≤ L ∧ |π t ω| ≤ L ∧ |r t ω| ≤ Lr ∧
      p.α * Real.exp ((p.ε - 1) * π t ω) + (1 - p.α) * Real.exp ((1 - p.ε) * r t ω) = 1 :=
  Iff.rfl

/-- Cochrane (2023), p. 118: the admissible values form a closed set. -/
theorem goodK_closed (p : CalvoPar) (L Lr : ℝ) : IsClosed (goodK p L Lr) := by
  have c1 : Continuous fun v : ℝ × ℝ × ℝ => |v.1| := by fun_prop
  have c2 : Continuous fun v : ℝ × ℝ × ℝ => |v.2.1| := by fun_prop
  have c3 : Continuous fun v : ℝ × ℝ × ℝ => |v.2.2| := by fun_prop
  have c4 : Continuous fun v : ℝ × ℝ × ℝ =>
      p.α * Real.exp ((p.ε - 1) * v.2.1) + (1 - p.α) * Real.exp ((1 - p.ε) * v.2.2) := by
    fun_prop
  exact (isClosed_le c1 continuous_const).inter ((isClosed_le c2 continuous_const).inter
    ((isClosed_le c3 continuous_const).inter (isClosed_eq c4 continuous_const)))

/-- Cochrane (2023), p. 118: `good_t` is known at `t`. -/
theorem goodSet_meas {p : CalvoPar} {L Lr : ℝ} {x π r : ℕ → Ω → ℝ}
    (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (hr : StronglyAdapted S.𝓕 r)
    (t : ℕ) : MeasurableSet[S.𝓕 t] (goodSet p L Lr x π r t) :=
  ((hx t).measurable.prodMk ((hπ t).measurable.prodMk (hr t).measurable))
    (goodK_closed p L Lr).measurableSet

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: clipped output gap and inflation are bounded by `L` everywhere. -/
theorem clip_bounded {p : CalvoPar} {L Lr : ℝ} (hL : 0 ≤ L) {x π r : ℕ → Ω → ℝ} :
    Bounded (clip (goodSet p L Lr x π r) x) (clip (goodSet p L Lr x π r) π) L := by
  refine ⟨hL, fun t ω => ?_⟩
  by_cases hω : ω ∈ goodSet p L Lr x π r t
  · simp only [clip, Set.indicator_of_mem hω]
    exact ⟨hω.1, hω.2.1⟩
  · simp only [clip, Set.indicator_of_notMem hω, abs_zero]
    exact ⟨hL, hL⟩

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 421: clipped reset prices are bounded by `|Lr|` everywhere. -/
theorem clip_r_bound {p : CalvoPar} {L Lr : ℝ} {x π r : ℕ → Ω → ℝ} (s : ℕ) (ω : Ω) :
    |clip (goodSet p L Lr x π r) r s ω| ≤ |Lr| := by
  by_cases hω : ω ∈ goodSet p L Lr x π r s
  · simp only [clip, Set.indicator_of_mem hω]
    exact hω.2.2.1.trans (le_abs_self Lr)
  · simp only [clip, Set.indicator_of_notMem hω, abs_zero]
    exact abs_nonneg _

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 421: the clipped processes satisfy the Calvo index at every state (the
zero triple does). -/
theorem clip_index {p : CalvoPar} {L Lr : ℝ} {x π r : ℕ → Ω → ℝ} :
    Index p (clip (goodSet p L Lr x π r) π) (clip (goodSet p L Lr x π r) r) := by
  intro t ω
  by_cases hω : ω ∈ goodSet p L Lr x π r t
  · simp only [clip, Set.indicator_of_mem hω]
    exact hω.2.2.2
  · simp only [clip, Set.indicator_of_notMem hω, mul_zero, Real.exp_zero, mul_one]
    ring

/-- Cochrane (2023), p. 118: clipping to events known at each date preserves adaptedness. -/
theorem clip_adapted {G : ℕ → Set Ω} (hG : ∀ t, MeasurableSet[S.𝓕 t] (G t))
    {y : ℕ → Ω → ℝ} (hy : StronglyAdapted S.𝓕 y) : StronglyAdapted S.𝓕 (clip G y) :=
  fun t => (hy t).indicator (hG t)

/-- Cochrane (2023), p. 118: if the bounds and the index hold almost surely at every date, the
clipped processes equal the originals at **all** dates outside one null set. -/
theorem ae_clip_eq {p : CalvoPar} {L Lr : ℝ} {x π r : ℕ → Ω → ℝ}
    (hg : ∀ t, ∀ᵐ ω ∂S.μ, ω ∈ goodSet p L Lr x π r t) :
    ∀ᵐ ω ∂S.μ, ∀ t, clip (goodSet p L Lr x π r) x t ω = x t ω ∧
      clip (goodSet p L Lr x π r) π t ω = π t ω ∧ clip (goodSet p L Lr x π r) r t ω = r t ω := by
  filter_upwards [ae_all_iff.2 hg] with ω hω t
  simp only [clip, Set.indicator_of_mem (hω t), and_self]

/-! ### Transfer along processes that agree almost surely at all dates -/

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), p. 118: the weights depend on the path only through its values. -/
theorem aW_bW_eq {p : CalvoPar} {x π x' π' : ℕ → Ω → ℝ} {ω : Ω} (hx : ∀ t, x' t ω = x t ω)
    (hπ : ∀ t, π' t ω = π t ω) (t k : ℕ) :
    aW p x' π' t k ω = aW p x π t k ω ∧ bW p x' π' t k ω = bW p x π t k ω := by
  simp only [aW, bW, cumπ, hx, hπ, and_self]

/-- Cochrane (2023), p. 118: the discounted weights agree almost surely. -/
theorem wA_wB_congr {p : CalvoPar} {x π x' π' : ℕ → Ω → ℝ}
    (hE : ∀ᵐ ω ∂S.μ, ∀ t, x' t ω = x t ω ∧ π' t ω = π t ω) (t : ℕ) :
    wA p x' π' t =ᵐ[S.μ] wA p x π t ∧ wB p x' π' t =ᵐ[S.μ] wB p x π t := by
  constructor
  · filter_upwards [hE] with ω h
    simp only [wA, (aW_bW_eq (fun s => (h s).1) (fun s => (h s).2) t _).1]
  · filter_upwards [hE] with ω h
    simp only [wB, (aW_bW_eq (fun s => (h s).1) (fun s => (h s).2) t _).2]

/-- Cochrane (2023), p. 118: `f_t` and `k_t` agree almost surely. -/
theorem fc_kc_congr {p : CalvoPar} {x π x' π' : ℕ → Ω → ℝ}
    (hE : ∀ᵐ ω ∂S.μ, ∀ t, x' t ω = x t ω ∧ π' t ω = π t ω) (t : ℕ) :
    fc S p x' π' t =ᵐ[S.μ] fc S p x π t ∧ kc S p x' π' t =ᵐ[S.μ] kc S p x π t := by
  constructor
  · filter_upwards [S.E_congr (wA_wB_congr (p := p) hE t).1 t] with ω h
    simp only [fc, Fc, h]
  · filter_upwards [S.E_congr (wA_wB_congr (p := p) hE t).2 t] with ω h
    simp only [kc, Kc, h]

/-- Cochrane (2023), eq. (17.17), p. 407: the Calvo disturbance agrees almost surely. -/
theorem calvoRem_congr {p : CalvoPar} {x π r x' π' r' : ℕ → Ω → ℝ}
    (hE : ∀ᵐ ω ∂S.μ, ∀ t, x' t ω = x t ω ∧ π' t ω = π t ω ∧ r' t ω = r t ω) (t : ℕ) :
    calvoRem S p x' π' r' t =ᵐ[S.μ] calvoRem S p x π r t := by
  have hE2 : ∀ᵐ ω ∂S.μ, ∀ t, x' t ω = x t ω ∧ π' t ω = π t ω :=
    hE.mono fun ω h t => ⟨(h t).1, (h t).2.1⟩
  have hRI : ∀ s, RI p π' r' s =ᵐ[S.μ] RI p π r s := fun s => by
    filter_upwards [hE] with ω h
    simp only [RI, (h s).2.1, (h s).2.2]
  have eF : S.E t (fun ω => (p.ε - 1) * π' (t + 1) ω + fc S p x' π' (t + 1) ω) =ᵐ[S.μ]
      S.E t (fun ω => (p.ε - 1) * π (t + 1) ω + fc S p x π (t + 1) ω) := by
    refine S.E_congr ?_ t
    filter_upwards [hE, (fc_kc_congr (p := p) hE2 (t + 1)).1] with ω h1 h2
    rw [(h1 (t + 1)).2.1, h2]
  have eK : S.E t (fun ω => p.η * π' (t + 1) ω + kc S p x' π' (t + 1) ω) =ᵐ[S.μ]
      S.E t (fun ω => p.η * π (t + 1) ω + kc S p x π (t + 1) ω) := by
    refine S.E_congr ?_ t
    filter_upwards [hE, (fc_kc_congr (p := p) hE2 (t + 1)).2] with ω h1 h2
    rw [(h1 (t + 1)).2.1, h2]
  filter_upwards [hE, (fc_kc_congr (p := p) hE2 t).1, (fc_kc_congr (p := p) hE2 t).2, eF, eK,
    S.E_congr (hRI (t + 1)) t, hRI t] with ω h0 h1 h2 h3 h4 h5 h6
  simp only [calvoRem, RF, RK, (h0 t).1, h1, h2, h3, h4, h5, h6]

/-- Cochrane (2023), p. 118: optimal resetting at `t` transfers between processes that agree
almost surely (both reset prices known at `t`). -/
theorem resetOpt_congr {p : CalvoPar} {x π r x' π' r' : ℕ → Ω → ℝ}
    (hE : ∀ᵐ ω ∂S.μ, ∀ t, x' t ω = x t ω ∧ π' t ω = π t ω ∧ r' t ω = r t ω) {t : ℕ}
    (hr : StronglyMeasurable[S.𝓕 t] (r t)) (hr' : StronglyMeasurable[S.𝓕 t] (r' t)) :
    ResetOpt S t p.δ p.ε p.η (aW p x' π' t) (bW p x' π' t) (r' t) ↔
      ResetOpt S t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t) := by
  have hobj : ∀ q : Ω → ℝ, ∀ q' : Ω → ℝ, q' =ᵐ[S.μ] q →
      resetObj S p.δ p.ε p.η (aW p x' π' t) (bW p x' π' t) q' =
        resetObj S p.δ p.ε p.η (aW p x π t) (bW p x π t) q := fun q q' hq => by
    refine integral_congr_ae ?_
    filter_upwards [hE, hq] with ω h hqω
    have e := aW_bW_eq (p := p) (fun s => (h s).1) (fun s => (h s).2.1) t
    simp only [(e _).1, (e _).2, hqω]
  have hrr : r' t =ᵐ[S.μ] r t := hE.mono fun ω h => (h t).2.2
  have hbdd : BddAt S (r' t) ↔ BddAt S (r t) := by
    constructor
    · rintro ⟨M, hM⟩
      exact ⟨M, (hM.and hrr).mono fun ω h => h.2 ▸ h.1⟩
    · rintro ⟨M, hM⟩
      exact ⟨M, (hM.and hrr).mono fun ω h => h.2.symm ▸ h.1⟩
  constructor
  · rintro ⟨-, hb, hopt⟩
    refine ⟨hr, hbdd.1 hb, fun q hq hqb => ?_⟩
    rw [← hobj q q EventuallyEq.rfl, ← hobj (r t) (r' t) hrr]
    exact hopt q hq hqb
  · rintro ⟨-, hb, hopt⟩
    refine ⟨hr', hbdd.2 hb, fun q hq hqb => ?_⟩
    rw [hobj q q EventuallyEq.rfl, hobj (r t) (r' t) hrr]
    exact hopt q hq hqb

/-- Cochrane (2023), eq. (17.17), p. 407: the Phillips curve with the Calvo disturbance at `t`
transfers between processes that agree almost surely. -/
theorem pcm_congr {p : CalvoPar} {x π r x' π' r' : ℕ → Ω → ℝ}
    (hE : ∀ᵐ ω ∂S.μ, ∀ t, x' t ω = x t ω ∧ π' t ω = π t ω ∧ r' t ω = r t ω) (t : ℕ) :
    PCM S p.β p.κ (calvoRem S p x' π' r') x' π' t ↔ PCM S p.β p.κ (calvoRem S p x π r) x π t := by
  have hπ1 : S.E t (π' (t + 1)) =ᵐ[S.μ] S.E t (π (t + 1)) :=
    S.E_congr (hE.mono fun ω h => (h (t + 1)).2.1) t
  have hrhs : p.β • S.E t (π' (t + 1)) + p.κ • x' t + calvoRem S p x' π' r' t =ᵐ[S.μ]
      p.β • S.E t (π (t + 1)) + p.κ • x t + calvoRem S p x π r t := by
    filter_upwards [hE, hπ1, calvoRem_congr (p := p) hE t] with ω h h1 h2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2, (h t).1]
  have hπt : π' t =ᵐ[S.μ] π t := hE.mono fun ω h => (h t).2.1
  unfold PCM
  constructor
  · intro h'
    exact hπt.symm.trans (h'.trans hrhs)
  · intro h'
    exact hπt.trans (h'.trans hrhs.symm)

/-! ### The Phillips curve under almost-sure hypotheses -/

/-- Cochrane (2023), eq. (17.17), p. 407, **the Calvo Phillips curve under almost-sure
bounds**: with valid parameters, output gap and inflation bounded by `L` **almost surely** at
every date (`L ≥ 0`, `δe^{ηL} < 1`), reset prices bounded by `Lr` almost surely, all three
adapted, and the Calvo index holding **almost surely** at every date, resetting optimally at every
date is equivalent to (17.17) at every date with slope `κ` and the disturbance `calvoRem`. -/
theorem calvo_iff_PC_ae {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L Lr : ℝ}
    (hL : 0 ≤ L) (hρ : p.δ * Real.exp (p.η * L) < 1)
    (hxπ : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L) (hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Lr)
    (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (hr : StronglyAdapted S.𝓕 r)
    (hI : ∀ t, ∀ᵐ ω ∂S.μ,
      p.α * Real.exp ((p.ε - 1) * π t ω) + (1 - p.α) * Real.exp ((1 - p.ε) * r t ω) = 1) :
    (∀ t, ResetOpt S t p.δ p.ε p.η (aW p x π t) (bW p x π t) (r t)) ↔
      ∀ t, PCM S p.β p.κ (calvoRem S p x π r) x π t := by
  set G := goodSet p L Lr x π r with hG
  have hg : ∀ t, ∀ᵐ ω ∂S.μ, ω ∈ G t := fun t => by
    filter_upwards [hxπ t, hrb t, hI t] with ω h1 h2 h3
    exact ⟨h1.1, h1.2, h2, h3⟩
  have hGm : ∀ t, MeasurableSet[S.𝓕 t] (G t) := goodSet_meas hx hπ hr
  have hE := ae_clip_eq hg
  have hcx := clip_adapted hGm hx
  have hcπ := clip_adapted hGm hπ
  have hcr := clip_adapted hGm hr
  have hmain := calvo_iff_PC h (clip_bounded hL) hρ hcx hcπ hcr clip_r_bound clip_index
  simp only [← fun t => resetOpt_congr (p := p) hE (hr t) (hcr t),
    ← fun t => pcm_congr (p := p) hE t]
  exact hmain

/-- Cochrane (2023), eq. (17.17), p. 407: **the explicit quadratic bound under almost-sure
hypotheses**: with `Small p L`, output gap and inflation bounded by `L` almost surely, adapted
variables and the Calvo index almost surely at every date, `|u_{π,t}| ≤ calvoC·L²` almost
surely. -/
theorem calvoRem_abs_le_ae {p : CalvoPar} (h : p.Valid) {x π r : ℕ → Ω → ℝ} {L : ℝ}
    (hs : Small p L) (hxπ : ∀ t, ∀ᵐ ω ∂S.μ, |x t ω| ≤ L ∧ |π t ω| ≤ L)
    (hx : StronglyAdapted S.𝓕 x) (hπ : StronglyAdapted S.𝓕 π) (hr : StronglyAdapted S.𝓕 r)
    (hI : ∀ t, ∀ᵐ ω ∂S.μ,
      p.α * Real.exp ((p.ε - 1) * π t ω) + (1 - p.α) * Real.exp ((1 - p.ε) * r t ω) = 1)
    (t : ℕ) : ∀ᵐ ω ∂S.μ, |calvoRem S p x π r t ω| ≤ calvoC p * L ^ 2 := by
  have hrb : ∀ t, ∀ᵐ ω ∂S.μ, |r t ω| ≤ Kr p * L := fun t => by
    filter_upwards [hxπ t, hI t] with ω h1 h2
    have hKf := Kf_nonneg h
    have hεL : (p.ε - 1) * L ≤ 1 := by nlinarith [hs.2.2.1, hs.1]
    exact r_abs_le_pt h.1 h.2.1 h.2.2.2.2.1 h1.2 hεL hs.2.2.2.2 h2
  set G := goodSet p L (Kr p * L) x π r with hG
  have hg : ∀ t, ∀ᵐ ω ∂S.μ, ω ∈ G t := fun t => by
    filter_upwards [hxπ t, hrb t, hI t] with ω h1 h2 h3
    exact ⟨h1.1, h1.2, h2, h3⟩
  have hGm : ∀ t, MeasurableSet[S.𝓕 t] (G t) := goodSet_meas hx hπ hr
  have hE := ae_clip_eq hg
  filter_upwards [calvoRem_congr hE t, calvoRem_abs_le h (clip_bounded hs.1) hs
    (clip_adapted hGm hx) (clip_adapted hGm hπ) clip_index t] with ω h1 h2
  rwa [← h1]

/-! ### Boundedness cannot be dropped -/

/-- Cochrane (2023), p. 118: **an unbounded solution of the reset-gap equation**: for
`0 < δ < 1`, `G_t = δ^{−t}` solves `G_t = δE_tG_{t+1}`, is nonzero, and is not essentially
bounded. So the uniqueness step behind `TidyR6CalvoPC.calvo_iff_PC` (a bounded solution of this
equation is zero) has no unbounded analogue. -/
theorem unbounded_solves {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    S.Solves δ 0 (fun t (_ : Ω) => δ⁻¹ ^ t) ∧ (∀ t (_ : Ω), δ⁻¹ ^ t ≠ (0 : ℝ)) ∧
      ¬ S.BddProc (fun t (_ : Ω) => δ⁻¹ ^ t) := by
  refine ⟨fun t => Eventually.of_forall fun ω => ?_, fun t ω => by positivity, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, add_zero]
    rw [show (fun _ : Ω => δ⁻¹ ^ (t + 1)) = fun _ => δ⁻¹ ^ (t + 1) from rfl, S.E_const, pow_succ]
    field_simp
  · rintro ⟨M, hM⟩
    have h1 : 1 < δ⁻¹ := one_lt_inv_iff₀.2 ⟨hδ, hδ1⟩
    obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop M).exists
    obtain ⟨ω, hω⟩ := (hM t).exists
    rw [abs_of_pos (by positivity)] at hω
    linarith

end Cochrane.KeynesianStickyPrices.TidyR6CalvoAE
