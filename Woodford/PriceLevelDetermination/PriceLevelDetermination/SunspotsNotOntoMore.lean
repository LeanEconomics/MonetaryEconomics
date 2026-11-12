/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.SunspotsNotOntoExamples

/-!
# Sunspots when (A.8) is not onto: the remaining two shapes of (A.8)

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 632–634. `SunspotsBoundedBelow` and
`SunspotsNotOntoExamples` settle the sunspot question when (A.8) is onto or bounded below, and
show that a unit root or a singular pencil leaves it undecided. This module treats the two
remaining shapes of (A.8), each with a pair of `C^∞` two-dimensional systems with the **same**
linearisation and opposite answers (so neither shape is decided by the linearisation).

## (A.8) one-to-one with a non-closed range

`Hdamp` and `Hgrow` (`x_t` forward-looking, `y_t` its cumulated sum):
`E_t x_{t+1} = x_t(1 − y_t²)` resp. `x_t + x_t³`, and `y_t = y_{t−1} + x_t`. Their common (A.8)
is one-to-one (`injective_linOp_H`: a constant `x` makes `y` grow linearly) but not bounded
below (`not_boundedBelow_linOp_H`), so its range is not closed (`not_isClosed_range_linOp_H`).
`Hdamp_random_sunspot`: random sunspots at every scale on the coin tree (the damping
`x_t y_t²` brings `x` back to zero before `y` grows: `y³ + 3x(1 − y²)` does not increase);
`Hgrow_unique`: under informational closure the steady state is the only equilibrium.

## (A.8) Fredholm, neither one-to-one nor onto

`Fsun` and `Fnone`: `E_t x_{t+1} = x_t/2` and `y_t = 2y_{t−1}` resp. `y_t = 2y_{t−1} + x_t²`.
Their common (A.8) is Fredholm: its kernel is the line spanned by `((1/2)ᵗ, 0)`
(`ker_linOp_F`) and its range is the kernel of the nonzero continuous functional
`w ↦ Σ_s 2^{−(s+1)} w_{s,2}` (`range_linOp_F`), hence closed of codimension one.
`Fsun_random_sunspot`: random sunspots (the `x` block alone); `Fnone_unique`: under
informational closure only the steady state (the unstable `y` block, forced by `x_t² ≥ 0`, can
stay bounded only if `x ≡ 0`).

Summaries: `injective_nonclosed_undecided`, `fredholm_linOp_F`, `fredholm_undecided`. So for every
shape of (A.8) other than "onto" or "bounded below" the sunspot question is decided by the
higher-order terms.
-/

namespace Woodford.PriceLevelDetermination.SunspotsNotOntoMore

open scoped Topology Matrix
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic SunspotsBoundedBelow
open SunspotsNotOntoExamples (known_comp)
open LocalIFTSystems (Arg linOp linOp_apply d1 d2 d3 M1 M2 M3)

/-! ### Tools -/

/-- Woodford (2003), App. A.3, p. 633 (tool): coordinate `j` of `x_{t−1}`. -/
noncomputable def prL (j : Fin 2) : Arg (Fin 2) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ) × ℝ))

/-- Woodford (2003), App. A.3, p. 633 (tool): coordinate `j` of `x_t`. -/
noncomputable def prN (j : Fin 2) : Arg (Fin 2) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ) × ℝ)))

/-- Woodford (2003), App. A.3, p. 633 (tool): coordinate `j` of `x_{t+1}`. -/
noncomputable def prF (j : Fin 2) : Arg (Fin 2) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ).comp
    ((ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ((Fin 2 → ℝ) × (Fin 2 → ℝ) × ℝ))))

/-- Woodford (2003), App. A.3, p. 634 (tool): the odd two-branch process on the coin tree,
`x_0 = 0`, `x_{t+1} = ±P_t` after first flip heads/tails. -/
noncomputable def brProc2 (P : ℕ → Fin 2 → ℝ) {M : ℝ} (hM : ∀ n, ‖P n‖ ≤ M) :
    SProcV (Fin 2) (Bool × Bool) :=
  LocalIFTStochastic.mkB (fun p => if p.2.1 then lagV 0 P p.1 else -lagV 0 P p.1)
    ⟨max M 0, fun p => by
      obtain ⟨t, ω⟩ := p
      have h : ‖lagV 0 P t‖ ≤ max M 0 := by
        cases t with
        | zero => simp
        | succ t => exact (hM t).trans (le_max_left _ _)
      split_ifs
      · exact h
      · rwa [norm_neg]⟩

/-- Woodford (2003), App. A.3, p. 634 (tool): the two-branch process is within `M` of the steady
state. -/
theorem norm_brProc2_le {P : ℕ → Fin 2 → ℝ} {M : ℝ} (hM : ∀ n, ‖P n‖ ≤ M) (hM0 : 0 ≤ M) :
    ‖brProc2 P hM‖ ≤ M := by
  refine LocalIFTStochastic.norm_le_of_forall hM0 fun p => ?_
  obtain ⟨t, ω⟩ := p
  have h : ‖lagV 0 P t‖ ≤ M := by
    cases t with
    | zero => simpa using hM0
    | succ t => exact hM t
  change ‖(if ω.1 then lagV 0 P t else -lagV 0 P t)‖ ≤ M
  split_ifs
  · exact h
  · rwa [norm_neg]

/-- Woodford (2003), App. A.3, p. 634 (tool): **an odd condition is solved by the two-branch
process on the coin tree** when the heads branch solves it from date 1 on (the date-0 condition
averages to zero by oddness). -/
theorem solvesSV_brProc2 {H : Arg (Fin 2) ℝ → (Fin 2 → ℝ)} (hodd : ∀ q, H (-q) = -H q)
    {P : ℕ → Fin 2 → ℝ} {M : ℝ} (hM : ∀ n, ‖P n‖ ≤ M)
    (hstep : ∀ n, H (lagV 0 P n, P n, P (n + 1), 0) = 0) :
    SolvesSV ExpectationsFiniteTree.coinSystem H 0 (brProc2 P hM) := by
  have hv : ∀ t ω, brProc2 P hM (t, ω) = if ω.1 then lagV 0 P t else -lagV 0 P t :=
    fun _ _ => rfl
  refine ⟨fun t i => ?_, fun t i => ?_⟩
  · cases t with
    | zero =>
      have h0 : toP (brProc2 P hM) 0 i = fun _ => 0 := by
        funext ω
        change (if ω.1 then lagV 0 P 0 else -lagV 0 P 0) i = 0
        split_ifs <;> simp
      rw [h0]
      exact ExpectationsFiniteTree.coinSystem.const 0 0
    | succ t =>
      have h1 : toP (brProc2 P hM) (t + 1) i =
          fun ω => (fun b : Bool => (if b then P t else -P t) i) ω.1 := by
        funext ω
        change (if ω.1 then lagV 0 P (t + 1) else -lagV 0 P (t + 1)) i = _
        rfl
      rw [h1]
      exact LocalIFTStochasticModels.coin_known_fst t (fun b : Bool => (if b then P t else -P t) i)
  · cases t with
    | zero =>
      have hf : (fun ω => H (ptS ((0 : ParS (Fin 2) ℝ (Bool × Bool)), brProc2 P hM) (0, ω)) i) =
          fun ω => (if ω.1 then H (0, 0, P 0, 0) i else -H (0, 0, P 0, 0) i) := by
        funext ω
        have e : ptS ((0 : ParS (Fin 2) ℝ (Bool × Bool)), brProc2 P hM) (0, ω) =
            if ω.1 then ((0, 0, P 0, 0) : Arg (Fin 2) ℝ)
            else -((0, 0, P 0, 0) : Arg (Fin 2) ℝ) := by
          obtain ⟨b, b'⟩ := ω
          cases b <;> simp [ptS, hv]
        rw [e]
        split_ifs
        · rfl
        · rw [hodd]
          rfl
      rw [hf]
      funext ω
      rw [LocalIFTStochasticModels.coin_E0]
      simp
    | succ n =>
      have hf : (fun ω => H (ptS ((0 : ParS (Fin 2) ℝ (Bool × Bool)), brProc2 P hM)
          (n + 1, ω)) i) = 0 := by
        funext ω
        have e : ptS ((0 : ParS (Fin 2) ℝ (Bool × Bool)), brProc2 P hM) (n + 1, ω) =
            if ω.1 then ((lagV 0 P n, P n, P (n + 1), 0) : Arg (Fin 2) ℝ)
            else -((lagV 0 P n, P n, P (n + 1), 0) : Arg (Fin 2) ℝ) := by
          obtain ⟨b, b'⟩ := ω
          cases n <;> cases b <;> simp [ptS, hv]
        rw [e]
        split_ifs
        · rw [hstep n]
          rfl
        · rw [hodd, hstep n]
          simp
      rw [hf]
      exact map_zero _

/-! ### (A.8) one-to-one with non-closed range: `Hdamp` and `Hgrow` -/

/-- Woodford (2003), App. A.3, p. 632 (example): `E_t x_{t+1} = x_t (1 − y_t²)`,
`y_t = y_{t−1} + x_t`. -/
def Hdamp (p : Arg (Fin 2) ℝ) : Fin 2 → ℝ :=
  ![p.2.2.1 0 - p.2.1 0 + p.2.1 0 * p.2.1 1 ^ 2, p.2.1 1 - p.1 1 - p.2.1 0]

/-- Woodford (2003), App. A.3, p. 632 (example): `E_t x_{t+1} = x_t + x_t³`,
`y_t = y_{t−1} + x_t`. -/
def Hgrow (p : Arg (Fin 2) ℝ) : Fin 2 → ℝ :=
  ![p.2.2.1 0 - p.2.1 0 - p.2.1 0 ^ 3, p.2.1 1 - p.1 1 - p.2.1 0]

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (example): the common linear part
`(x_{t+1} − x_t, y_t − y_{t−1} − x_t)`. -/
noncomputable def LH : Arg (Fin 2) ℝ →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k => ![prF 0 - prN 0, prN 1 - prL 1 - prN 0] k

/-- Woodford (2003), App. A.3, p. 632 (example): **`Hdamp` and `Hgrow` have the same derivative**
`LH` at the steady state, and are `C^∞`. -/
theorem hasFDerivAt_H : HasFDerivAt Hdamp LH 0 ∧ HasFDerivAt Hgrow LH 0 ∧
    (∀ k : ℕ, ContDiff ℝ k Hdamp ∧ ContDiff ℝ k Hgrow) := by
  have hL : ∀ j, HasFDerivAt (prL j : Arg (Fin 2) ℝ → ℝ) (prL j) 0 := fun j => (prL j).hasFDerivAt
  have hN : ∀ j, HasFDerivAt (prN j : Arg (Fin 2) ℝ → ℝ) (prN j) 0 := fun j => (prN j).hasFDerivAt
  have hF : ∀ j, HasFDerivAt (prF j : Arg (Fin 2) ℝ → ℝ) (prF j) 0 := fun j => (prF j).hasFDerivAt
  refine ⟨hasFDerivAt_pi'' fun i => ?_, hasFDerivAt_pi'' fun i => ?_, fun k => ⟨?_, ?_⟩⟩
  · fin_cases i
    · have h := ((hF 0).sub (hN 0)).add ((hN 0).mul ((hN 1).pow 2))
      refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp [LH, prN]
    · have h := ((hN 1).sub (hL 1)).sub (hN 0)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp [LH]
  · fin_cases i
    · have h := ((hF 0).sub (hN 0)).sub ((hN 0).pow 3)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp [LH, prN]
    · have h := ((hN 1).sub (hL 1)).sub (hN 0)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp [LH]
  · refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · exact (((prF 0).contDiff.sub (prN 0).contDiff).add
        ((prN 0).contDiff.mul ((prN 1).contDiff.pow 2)) :)
    · exact (((prN 1).contDiff.sub (prL 1).contDiff).sub (prN 0).contDiff :)
  · refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · exact (((prF 0).contDiff.sub (prN 0).contDiff).sub ((prN 0).contDiff.pow 3) :)
    · exact (((prN 1).contDiff.sub (prL 1).contDiff).sub (prN 0).contDiff :)

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (example): **the common operator (A.8)**,
`v ↦ (v_{t+1,x} − v_{t,x}, v_{t,y} − v_{t−1,y} − v_{t,x})`. -/
theorem linOp_H : linOp Hdamp = linOp Hgrow ∧ ∀ (v : SeqV (Fin 2)) (t : ℕ),
    linOp Hdamp v t = ![v (t + 1) 0 - v t 0, v t 1 - lagV 0 (fun s => v s) t 1 - v t 0] := by
  obtain ⟨h1, h2, -⟩ := hasFDerivAt_H
  refine ⟨?_, fun v t => ?_⟩
  · simp only [linOp, M1, M2, M3, d1, d2, d3, h1.fderiv, h2.fderiv]
  · rw [linOp_apply]
    simp only [d1, d2, d3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, h1.fderiv]
    funext i
    fin_cases i <;> simp [LH, prL, prN, prF] <;> ring

/-- Woodford (2003), App. A.3, p. 632 (example): **the common (A.8) is one-to-one** (a constant
`x` makes `y_t = (t + 1)x` unbounded). -/
theorem injective_linOp_H : Function.Injective (linOp Hdamp) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have h : ∀ t, v (t + 1) 0 = v t 0 ∧ v t 1 = lagV 0 (fun s => v s) t 1 + v t 0 := by
    intro t
    have e := linOp_H.2 v t
    rw [hv] at e
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    simp at e0 e1
    exact ⟨by linarith, by linarith⟩
  have hx : ∀ t, v t 0 = v 0 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [(h t).1, ih]
  have hy : ∀ t : ℕ, v t 1 = (t + 1) * v 0 0 := by
    intro t
    induction t with
    | zero => simp [(h 0).2, hx]
    | succ t ih =>
      rw [(h (t + 1)).2, lagV_succ, ih, hx (t + 1)]
      push_cast
      ring
  have hc : v 0 0 = 0 := by
    by_contra hne
    have hpos : 0 < |v 0 0| := abs_pos.mpr hne
    obtain ⟨t, ht⟩ := exists_nat_gt (‖v‖ / |v 0 0|)
    have hb : |v t 1| ≤ ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ 1).trans (LocalIFT.norm_seq_apply_le _ _)
    rw [hy, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < t + 1)] at hb
    rw [div_lt_iff₀ hpos] at ht
    nlinarith [abs_nonneg (v 0 0)]
  refine seq_ext fun t => funext fun i => ?_
  fin_cases i
  · simpa [hc] using hx t
  · simpa [hc] using hy t

/-- Woodford (2003), App. A.3, p. 632 (example): **the common (A.8) is not bounded below**
(the path `x = 1/N` for `N` periods, `y` its cumulated sum, has norm `1` and image of norm
`1/N`). -/
theorem not_boundedBelow_linOp_H : ¬ BoundedBelow (linOp Hdamp) := by
  rintro ⟨C, hC0, hC⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (C + 1)
  have hN0 : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hN0
  set z : ℕ → Fin 2 → ℝ := fun t => ![if t < N then 1 / (N : ℝ) else 0,
    (min (t + 1) N : ℕ) / (N : ℝ)] with hz
  have hzb : LinearSystems.BoundedSeq z := ⟨1, fun t i => by
    fin_cases i
    · change |(if t < N then 1 / (N : ℝ) else 0)| ≤ 1
      split_ifs
      · rw [abs_of_pos (by positivity)]
        exact (div_le_one hN0).mpr (by linarith)
      · simp
    · change |((min (t + 1) N : ℕ) : ℝ) / N| ≤ 1
      rw [abs_of_nonneg (by positivity), div_le_one hN0]
      exact_mod_cast min_le_right _ _⟩
  set v := toSeqV z hzb with hv
  have hvN : 1 ≤ ‖v‖ := by
    have h := (norm_le_pi_norm (v (N - 1)) 1).trans (LocalIFT.norm_seq_apply_le v (N - 1))
    have e : v (N - 1) 1 = 1 := by
      change ((min (N - 1 + 1) N : ℕ) : ℝ) / N = 1
      have : N - 1 + 1 = N := Nat.sub_add_cancel (by exact_mod_cast hN0)
      rw [this, min_self]
      field_simp
    rw [e, norm_one] at h
    exact h
  have himg : ‖linOp Hdamp v‖ ≤ 1 / N := by
    refine LocalIFT.norm_seq_le (by positivity) fun t =>
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [linOp_H.2, Real.norm_eq_abs]
    fin_cases i
    · change |(if t + 1 < N then 1 / (N : ℝ) else 0) - (if t < N then 1 / (N : ℝ) else 0)| ≤ _
      split_ifs <;> simp [abs_of_pos, hN0]
    · change |((min (t + 1) N : ℕ) : ℝ) / N - lagV 0 (fun s => z s) t 1 -
        (if t < N then 1 / (N : ℝ) else 0)| ≤ _
      cases t with
      | zero =>
        rw [show min (0 + 1) N = 1 by omega]
        simp only [lagV_zero, Pi.zero_apply, hNpos, ↓reduceIte, Nat.cast_one, sub_zero, sub_self,
          abs_zero]
        positivity
      | succ t =>
        simp only [lagV_succ, hz, Matrix.cons_val_one, Matrix.cons_val_zero]
        by_cases htN : t + 1 < N
        · simp only [htN, ↓reduceIte]
          rw [min_eq_left (by omega : t + 1 + 1 ≤ N), min_eq_left (by omega : t + 1 ≤ N)]
          push_cast
          rw [div_sub_div_same, div_sub_div_same, show (t : ℝ) + 1 + 1 - (t + 1) - 1 = 0 by ring,
            zero_div, abs_zero]
          positivity
        · simp only [htN, ↓reduceIte]
          rw [min_eq_right (by omega : N ≤ t + 1 + 1), min_eq_right (by omega : N ≤ t + 1)]
          simp only [sub_self, abs_zero]
          positivity
  have h := hC v
  have : C * ‖linOp Hdamp v‖ ≤ C * (1 / N) := mul_le_mul_of_nonneg_left himg hC0
  have hlt : C * (1 / N) < 1 := by
    rw [mul_one_div, div_lt_one hN0]
    linarith
  linarith

/-- Woodford (2003), App. A.3, p. 632 (example): **the common (A.8) has a non-closed range**
(one-to-one and not bounded below, `boundedBelow_iff`). -/
theorem not_isClosed_range_linOp_H : ¬ IsClosed (Set.range (linOp Hdamp)) := fun hcl =>
  not_boundedBelow_linOp_H ((boundedBelow_iff _).mpr ⟨injective_linOp_H, hcl⟩)

/-- Woodford (2003), App. A.3, p. 634 (example): the damped deterministic continuation
`(x, y) ↦ (x(1 − y²), y + x(1 − y²))` from `(a, a)`. -/
noncomputable def dampXY (a : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, a)
  | n + 1 => ((dampXY a n).1 * (1 - (dampXY a n).2 ^ 2),
      (dampXY a n).2 + (dampXY a n).1 * (1 - (dampXY a n).2 ^ 2))

/-- Woodford (2003), App. A.3, p. 634 (example): **the damped path stays small**: for
`0 < a ≤ 1/64`, `0 ≤ x_n ≤ a`, `0 ≤ y_n ≤ 1/2` and `y_n³ + 3x_n(1 − y_n²) ≤ a³ + 3a` (this
quantity does not increase along the path). -/
theorem dampXY_bound {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1 / 64) (n : ℕ) :
    0 ≤ (dampXY a n).1 ∧ (dampXY a n).1 ≤ a ∧ 0 ≤ (dampXY a n).2 ∧ (dampXY a n).2 ≤ 1 / 2 ∧
      (dampXY a n).2 ^ 3 + 3 * ((dampXY a n).1 * (1 - (dampXY a n).2 ^ 2)) ≤ a ^ 3 + 3 * a := by
  induction n with
  | zero =>
    simp only [dampXY]
    refine ⟨ha0.le, le_rfl, ha0.le, by linarith, ?_⟩
    nlinarith [sq_nonneg a]
  | succ n ih =>
    obtain ⟨hx0, hxa, hy0, hy2, hK⟩ := ih
    set X := (dampXY a n).1 with hX
    set Y := (dampXY a n).2 with hY
    have hX' : (dampXY a (n + 1)).1 = X * (1 - Y ^ 2) := rfl
    have hY' : (dampXY a (n + 1)).2 = Y + X * (1 - Y ^ 2) := rfl
    rw [hX', hY']
    set X' := X * (1 - Y ^ 2) with hXd
    have hY2 : Y ^ 2 ≤ 1 / 4 := by nlinarith
    have hX'0 : 0 ≤ X' := mul_nonneg hx0 (by linarith)
    have hX'a : X' ≤ X := by nlinarith [sq_nonneg Y]
    set Y' := Y + X' with hYd
    have hY'1 : Y' ≤ 1 := by linarith
    have hY'0 : 0 ≤ Y' := by linarith
    -- the step: `Y'³ − Y³ ≤ 3 X' Y'²`
    have hstep : Y' ^ 3 + 3 * (X' * (1 - Y' ^ 2)) ≤ Y ^ 3 + 3 * X' := by
      have e : Y' ^ 3 - Y ^ 3 = X' * (Y' ^ 2 + Y' * Y + Y ^ 2) := by rw [hYd]; ring
      have h1 : Y' * Y ≤ Y' ^ 2 := by nlinarith
      have h2 : Y ^ 2 ≤ Y' ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) hX'0]
    have hK' : Y' ^ 3 + 3 * (X' * (1 - Y' ^ 2)) ≤ a ^ 3 + 3 * a := hstep.trans hK
    have hY'3 : Y' ^ 3 ≤ 1 / 16 := by
      have : 0 ≤ 3 * (X' * (1 - Y' ^ 2)) := by
        have : Y' ^ 2 ≤ 1 := by nlinarith
        nlinarith
      nlinarith [pow_le_pow_left₀ ha0.le ha 3]
    refine ⟨hX'0, hX'a.trans hxa, hY'0, ?_, hK'⟩
    by_contra hc
    push Not at hc
    have := pow_lt_pow_left₀ hc (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num at this
    linarith

/-- Woodford (2003), App. A.3, p. 634 (example): `Hdamp` is odd. -/
theorem Hdamp_odd (q : Arg (Fin 2) ℝ) : Hdamp (-q) = -Hdamp q := by
  funext i
  fin_cases i <;> simp [Hdamp] <;> ring

/-- **Random sunspots with (A.8) one-to-one and non-closed range** (Woodford (2003), App. A.3,
pp. 632–634, example): for `Hdamp`, on the coin tree, for every `ε > 0` there is a bounded
adapted equilibrium with no shocks and `x_{−1} = 0`, within `ε` of the steady state, whose date-1
value differs across the first flip (`x_1 = ±a`, then the damped continuation). -/
theorem Hdamp_random_sunspot {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV (Fin 2) (Bool × Bool), SolvesSV ExpectationsFiniteTree.coinSystem Hdamp 0 x ∧
      ‖x‖ ≤ ε ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  set a := min (min ε (ε ^ 3 / 4)) (1 / 64) with ha
  have ha0 : 0 < a := lt_min (lt_min hε (by positivity)) (by norm_num)
  have ha64 : a ≤ 1 / 64 := min_le_right _ _
  have haε : a ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
  have haε3 : a ≤ ε ^ 3 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  set P : ℕ → Fin 2 → ℝ := fun n => ![(dampXY a n).1, (dampXY a n).2] with hP
  have hb := dampXY_bound ha0 ha64
  have hYε : ∀ n, (dampXY a n).2 ≤ ε := by
    intro n
    obtain ⟨hx0, -, hy0, hy2, hK⟩ := hb n
    have h1 : 0 ≤ 3 * ((dampXY a n).1 * (1 - (dampXY a n).2 ^ 2)) := by
      have : (dampXY a n).2 ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have h3 : (dampXY a n).2 ^ 3 ≤ ε ^ 3 := by
      have : a ^ 3 ≤ a := by nlinarith [pow_le_pow_left₀ ha0.le ha64 2]
      nlinarith
    exact (pow_le_pow_iff_left₀ hy0 hε.le (by norm_num : (3 : ℕ) ≠ 0)).mp h3
  have hM : ∀ n, ‖P n‖ ≤ ε := fun n => by
    obtain ⟨hx0, hxa, hy0, -, -⟩ := hb n
    refine (pi_norm_le_iff_of_nonneg hε.le).mpr fun i => ?_
    fin_cases i
    · simp [hP, abs_of_nonneg hx0, hxa.trans haε]
    · simp [hP, abs_of_nonneg hy0, hYε n]
  refine ⟨brProc2 P hM, solvesSV_brProc2 Hdamp_odd hM fun n => ?_, norm_brProc2_le hM hε.le,
    fun h => ?_⟩
  · funext i
    fin_cases i
    · simp [Hdamp, hP, dampXY]
      ring
    · cases n with
      | zero => simp [Hdamp, hP, dampXY]
      | succ n => simp [Hdamp, hP, dampXY]
  · have := congrFun h 0
    change (dampXY a 0).1 = -(dampXY a 0).1 at this
    simp only [dampXY] at this
    linarith

/-- **No sunspots with the same (A.8)** (Woodford (2003), App. A.3, pp. 632–634, example): under
informational closure, the only bounded adapted equilibrium of `Hgrow` with `x_{−1} = 0` and no
shocks is the steady state (`E_t x_{t+1} = x_t + x_t³` forces `x = 0`, then `y = 0`). -/
theorem Hgrow_unique {Ω : Type*} {𝔼 : ExpectationSystem Ω}
    (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {x : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 Hgrow 0 x) : x = 0 := by
  have hE : ∀ t, 𝔼.E t (toP x (t + 1) 0) = fun ω => toP x t 0 ω + toP x t 0 ω ^ 3 := by
    intro t
    have h := hx.2 t 0
    have hf : (fun ω => Hgrow (ptS ((0 : ParS (Fin 2) ℝ Ω), x) (t, ω)) 0) =
        toP x (t + 1) 0 - toP x t 0 - fun ω => toP x t 0 ω ^ 3 := rfl
    rw [hf, map_sub, map_sub, hx.1 t 0, known_comp hcl (hx.1 t 0) (fun z => z ^ 3)] at h
    funext ω
    have := congrFun h ω
    simp only [Pi.sub_apply, Pi.zero_apply] at this
    linarith
  have hz : ∀ p : ℕ × Ω, x p 0 = 0 := by
    refine eq_zero_of_push (fun p : ℕ × Ω => x p 0) ⟨‖x‖, fun p => abs_apply_le x p.1 p.2 0⟩
      one_pos fun B hB p => ?_
    obtain ⟨t, ω⟩ := p
    have hb := 𝔼.abs_E_le (fun ω' => hB (t + 1, ω')) t ω
    change |𝔼.E t (toP x (t + 1) 0) ω| ≤ B at hb
    rw [hE] at hb
    change |x (t, ω) 0 + x (t, ω) 0 ^ 3| ≤ B at hb
    have e : |x (t, ω) 0 + x (t, ω) 0 ^ 3| = |x (t, ω) 0| + |x (t, ω) 0| ^ 3 := by
      rw [show x (t, ω) 0 + x (t, ω) 0 ^ 3 = x (t, ω) 0 * (1 + x (t, ω) 0 ^ 2) by ring, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 1 + x (t, ω) 0 ^ 2), ← sq_abs]
      ring
    change |x (t, ω) 0| ^ 3 ≤ 1 * (B - |x (t, ω) 0|)
    linarith
  have hy : ∀ t ω, x (t, ω) 1 = 0 := by
    intro t
    induction t with
    | zero =>
      intro ω
      have h := congrFun (hx.2 0 1) ω
      have hf : (fun ω => Hgrow (ptS ((0 : ParS (Fin 2) ℝ Ω), x) (0, ω)) 1) =
          toP x 0 1 - toP x 0 0 := by
        funext ω
        simp [Hgrow, ptS, toP]
      rw [hf, map_sub, hx.1 0 1, hx.1 0 0] at h
      have := hz (0, ω)
      simp only [Pi.sub_apply, Pi.zero_apply] at h
      change x (0, ω) 1 - x (0, ω) 0 = 0 at h
      linarith
    | succ t ih =>
      intro ω
      have h := congrFun (hx.2 (t + 1) 1) ω
      have hf : (fun ω => Hgrow (ptS ((0 : ParS (Fin 2) ℝ Ω), x) (t + 1, ω)) 1) =
          toP x (t + 1) 1 - toP x t 1 - toP x (t + 1) 0 := rfl
      have hk : 𝔼.E (t + 1) (toP x t 1) = toP x t 1 := by
        conv_lhs => rw [← hx.1 t 1]
        rw [𝔼.known (Nat.le_succ t), hx.1 t 1]
      rw [hf, map_sub, map_sub, hx.1 (t + 1) 1, hx.1 (t + 1) 0, hk] at h
      have := hz (t + 1, ω)
      simp only [Pi.sub_apply, Pi.zero_apply] at h
      change x (t + 1, ω) 1 - x (t, ω) 1 - x (t + 1, ω) 0 = 0 at h
      linarith [ih ω]
  ext ⟨t, ω⟩ i
  fin_cases i
  · exact hz (t, ω)
  · exact hy t ω

/-- **(A.8) one-to-one with non-closed range does not decide the sunspot question** (Woodford
(2003), App. A.3, pp. 632–634, correction): `Hdamp` and `Hgrow` have the same (A.8), one-to-one
with non-closed range; the first has random sunspots at every scale on the coin tree, the second
only the steady state there. -/
theorem injective_nonclosed_undecided :
    linOp Hdamp = linOp Hgrow ∧ Function.Injective (linOp Hdamp) ∧
      ¬ IsClosed (Set.range (linOp Hdamp)) ∧
      (∀ ε > 0, ∃ x : SProcV (Fin 2) (Bool × Bool),
        SolvesSV ExpectationsFiniteTree.coinSystem Hdamp 0 x ∧ ‖x‖ ≤ ε ∧
          x (1, (true, true)) ≠ x (1, (false, true))) ∧
      ∀ x : SProcV (Fin 2) (Bool × Bool),
        SolvesSV ExpectationsFiniteTree.coinSystem Hgrow 0 x → x = 0 :=
  ⟨linOp_H.1, injective_linOp_H, not_isClosed_range_linOp_H, fun _ hε => Hdamp_random_sunspot hε,
    fun _ hx => Hgrow_unique (LocalIFTStochastic.finiteTree_infoClosed _) hx⟩

/-! ### (A.8) Fredholm, neither one-to-one nor onto: `Fsun` and `Fnone` -/

/-- Woodford (2003), App. A.3, p. 632 (example): `E_t x_{t+1} = x_t/2`, `y_t = 2y_{t−1}`. -/
noncomputable def Fsun (p : Arg (Fin 2) ℝ) : Fin 2 → ℝ :=
  ![p.2.2.1 0 - p.2.1 0 * (1 / 2), p.2.1 1 - 2 * p.1 1]

/-- Woodford (2003), App. A.3, p. 632 (example): `E_t x_{t+1} = x_t/2`, `y_t = 2y_{t−1} + x_t²`. -/
noncomputable def Fnone (p : Arg (Fin 2) ℝ) : Fin 2 → ℝ :=
  ![p.2.2.1 0 - p.2.1 0 * (1 / 2), p.2.1 1 - 2 * p.1 1 - p.2.1 0 ^ 2]

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (example): the common linear part
`(x_{t+1} − x_t/2, y_t − 2y_{t−1})`. -/
noncomputable def LF : Arg (Fin 2) ℝ →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi fun k => ![prF 0 - (1 / 2 : ℝ) • prN 0, prN 1 - (2 : ℝ) • prL 1] k

/-- Woodford (2003), App. A.3, p. 632 (example): **`Fsun` and `Fnone` have the same derivative**
`LF` at the steady state, and are `C^∞`. -/
theorem hasFDerivAt_F : HasFDerivAt Fsun LF 0 ∧ HasFDerivAt Fnone LF 0 ∧
    (∀ k : ℕ, ContDiff ℝ k Fsun ∧ ContDiff ℝ k Fnone) := by
  have hL : ∀ j, HasFDerivAt (prL j : Arg (Fin 2) ℝ → ℝ) (prL j) 0 := fun j => (prL j).hasFDerivAt
  have hN : ∀ j, HasFDerivAt (prN j : Arg (Fin 2) ℝ → ℝ) (prN j) 0 := fun j => (prN j).hasFDerivAt
  have hF : ∀ j, HasFDerivAt (prF j : Arg (Fin 2) ℝ → ℝ) (prF j) 0 := fun j => (prF j).hasFDerivAt
  refine ⟨hasFDerivAt_pi'' fun i => ?_, hasFDerivAt_pi'' fun i => ?_, fun k => ⟨?_, ?_⟩⟩
  · fin_cases i
    · have h := (hF 0).sub (HasFDerivAt.mul_const (hN 0) (1 / 2))
      refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp [LF]
    · have h := (hN 1).sub ((hL 1).const_mul 2)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp [LF]
  · fin_cases i
    · have h := (hF 0).sub (HasFDerivAt.mul_const (hN 0) (1 / 2))
      refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp [LF]
    · have h := ((hN 1).sub ((hL 1).const_mul 2)).sub ((hN 0).pow 2)
      refine h.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp [LF, prN]
  · refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · exact (((prF 0).contDiff.sub ((prN 0).contDiff.mul contDiff_const)) :)
    · exact (((prN 1).contDiff.sub (contDiff_const.mul (prL 1).contDiff)) :)
  · refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · exact (((prF 0).contDiff.sub ((prN 0).contDiff.mul contDiff_const)) :)
    · exact ((((prN 1).contDiff.sub (contDiff_const.mul (prL 1).contDiff)).sub
        ((prN 0).contDiff.pow 2)) :)

/-- Woodford (2003), App. A.3, eq. (A.8), p. 632 (example): **the common operator (A.8)**,
`v ↦ (v_{t+1,x} − v_{t,x}/2, v_{t,y} − 2 v_{t−1,y})`. -/
theorem linOp_F : linOp Fsun = linOp Fnone ∧ ∀ (v : SeqV (Fin 2)) (t : ℕ),
    linOp Fsun v t = ![v (t + 1) 0 - v t 0 / 2, v t 1 - 2 * lagV 0 (fun s => v s) t 1] := by
  obtain ⟨h1, h2, -⟩ := hasFDerivAt_F
  refine ⟨?_, fun v t => ?_⟩
  · simp only [linOp, M1, M2, M3, d1, d2, d3, h1.fderiv, h2.fderiv]
  · rw [linOp_apply]
    simp only [d1, d2, d3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, h1.fderiv]
    funext i
    fin_cases i <;> simp [LF, prL, prN, prF] <;> ring

/-- Woodford (2003), App. A.3, p. 632 (example): the kernel direction `((1/2)ᵗ, 0)`. -/
noncomputable def kF : SeqV (Fin 2) :=
  toSeqV (fun t => ![(1 / 2 : ℝ) ^ t, 0]) ⟨1, fun t i => by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    · simp⟩

/-- Woodford (2003), App. A.3, p. 632 (example): **the kernel of the common (A.8) is the line
spanned by `((1/2)ᵗ, 0)`**, which is nonzero; so (A.8) is not one-to-one. -/
theorem ker_linOp_F : kF ≠ 0 ∧ ∀ v : SeqV (Fin 2), linOp Fsun v = 0 ↔ v = v 0 0 • kF := by
  refine ⟨fun h => ?_, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · have := congrFun (congrArg (fun w : SeqV (Fin 2) => w 0) h) 0
    change ((1 / 2 : ℝ) ^ 0) = 0 at this
    norm_num at this
  · have h : ∀ t, v (t + 1) 0 = v t 0 / 2 ∧ v t 1 = 2 * lagV 0 (fun s => v s) t 1 := by
      intro t
      have e := linOp_F.2 v t
      rw [hv] at e
      have e0 := congrFun e 0
      have e1 := congrFun e 1
      simp at e0 e1
      exact ⟨by linarith, by linarith⟩
    have hx : ∀ t, v t 0 = v 0 0 * (1 / 2) ^ t := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [(h t).1, ih, pow_succ]; ring
    have hy : ∀ t, v t 1 = 0 := by
      intro t
      induction t with
      | zero => simpa using (h 0).2
      | succ t ih => rw [(h (t + 1)).2, lagV_succ, ih, mul_zero]
    refine seq_ext fun t => funext fun i => ?_
    fin_cases i
    · change v t 0 = v 0 0 * (1 / 2) ^ t
      exact hx t
    · change v t 1 = v 0 0 * 0
      rw [hy t, mul_zero]
  · rw [hv, map_smul]
    have : linOp Fsun kF = 0 := by
      refine seq_ext fun t => ?_
      rw [linOp_F.2]
      funext i
      fin_cases i
      · change (1 / 2 : ℝ) ^ (t + 1) - (1 / 2) ^ t / 2 = 0
        ring
      · change (0 : ℝ) - 2 * lagV 0 (fun s => kF s) t 1 = 0
        cases t <;> simp [kF]
    rw [this, smul_zero]

/-- Woodford (2003), App. A.3, p. 632 (tool): a bounded sequence weighted by `2^{−(k+1)}` is
summable, with sum bounded by the bound. -/
theorem geom_sum (c : ℕ → ℝ) {B : ℝ} (hc : ∀ k, |c k| ≤ B) :
    Summable (fun k => (1 / 2 : ℝ) ^ (k + 1) * c k) ∧
      |∑' k, (1 / 2 : ℝ) ^ (k + 1) * c k| ≤ B := by
  have hg : Summable (fun k : ℕ => B * (1 / 2 : ℝ) ^ (k + 1)) :=
    (summable_geometric_two.mul_right (1 / 2)).mul_left B |>.congr fun k => by ring
  have hb : ∀ k, ‖(1 / 2 : ℝ) ^ (k + 1) * c k‖ ≤ B * (1 / 2 : ℝ) ^ (k + 1) := fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right (hc k) (by positivity)
  have hs := Summable.of_norm_bounded hg hb
  refine ⟨hs, ?_⟩
  have h1 : ∑' k : ℕ, B * (1 / 2 : ℝ) ^ (k + 1) = B := by
    rw [tsum_mul_left]
    have : ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1) = 1 := by
      simp_rw [pow_succ]
      rw [tsum_mul_right, tsum_geometric_two]
      norm_num
    rw [this, mul_one]
  rw [← Real.norm_eq_abs, ← h1]
  exact (norm_tsum_le_tsum_norm hs.norm).trans (hs.norm.tsum_le_tsum hb hg)

/-- Woodford (2003), App. A.3, p. 632 (tool): coordinates of a bounded sequence are bounded by
its norm. -/
theorem abs_apply_le_seq (w : SeqV (Fin 2)) (s : ℕ) (j : Fin 2) : |w s j| ≤ ‖w‖ := by
  rw [← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ j).trans (LocalIFT.norm_seq_apply_le _ _)

/-- Woodford (2003), App. A.3, p. 632 (example): the functional `w ↦ Σ_s 2^{−(s+1)} w_{s,y}`. -/
noncomputable def phiF : SeqV (Fin 2) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun w => ∑' s, (1 / 2 : ℝ) ^ (s + 1) * w s 1
      map_add' := fun w w' => by
        have h1 := (geom_sum (fun s => w s 1) (fun s =>
          (abs_apply_le_seq w s 1))).1
        have h2 := (geom_sum (fun s => w' s 1) (fun s =>
          (abs_apply_le_seq w' s 1))).1
        rw [← h1.tsum_add h2]
        congr 1
        funext s
        simp only [lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := fun c w => by
        rw [RingHom.id_apply, smul_eq_mul, ← tsum_mul_left]
        congr 1
        funext s
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        ring }
    1 (fun w => by
      rw [one_mul, Real.norm_eq_abs]
      exact (geom_sum (fun s => w s 1) (fun s => abs_apply_le_seq w s 1)).2)

/-- Woodford (2003), App. A.3, p. 632 (tool): the `x` coordinate of the common (A.8). -/
theorem linOp_F_x (v : SeqV (Fin 2)) (s : ℕ) : linOp Fsun v s 0 = v (s + 1) 0 - v s 0 / 2 := by
  rw [linOp_F.2]
  rfl

/-- Woodford (2003), App. A.3, p. 632 (tool): the `y` coordinate of the common (A.8). -/
theorem linOp_F_y (v : SeqV (Fin 2)) (s : ℕ) :
    linOp Fsun v s 1 = v s 1 - 2 * lagV 0 (fun r => v r) s 1 := by
  rw [linOp_F.2]
  rfl

/-- Woodford (2003), App. A.3, p. 632 (example): the `x` part of the preimage,
`x_0 = 0`, `x_{t+1} = x_t/2 + w_{t,x}`. -/
noncomputable def xsF (w : SeqV (Fin 2)) : ℕ → ℝ
  | 0 => 0
  | t + 1 => xsF w t / 2 + w t 0

/-- Woodford (2003), App. A.3, p. 632 (example): `|x_t| ≤ 2‖w‖`. -/
theorem abs_xsF_le (w : SeqV (Fin 2)) (t : ℕ) : |xsF w t| ≤ 2 * ‖w‖ := by
  induction t with
  | zero => simp [xsF]
  | succ t ih =>
    have h := abs_apply_le_seq w t 0
    simp only [xsF]
    rw [abs_le] at ih h ⊢
    constructor <;> linarith [ih.1, ih.2, h.1, h.2]

/-- Woodford (2003), App. A.3, p. 632 (example): the `y` part of the preimage, the forward sum
`y_t = −Σ_k 2^{−(k+1)} w_{t+1+k,y}`. -/
noncomputable def ysF (w : SeqV (Fin 2)) (t : ℕ) : ℝ :=
  -∑' k, (1 / 2 : ℝ) ^ (k + 1) * w (t + 1 + k) 1

/-- Woodford (2003), App. A.3, p. 632 (tool): splitting off the first term of the forward sum. -/
theorem fwd_split (w : SeqV (Fin 2)) (t : ℕ) :
    ∑' k, (1 / 2 : ℝ) ^ (k + 1) * w (t + k) 1 =
      1 / 2 * w t 1 + 1 / 2 * ∑' k, (1 / 2 : ℝ) ^ (k + 1) * w (t + 1 + k) 1 := by
  have hs := (geom_sum (fun k => w (t + k) 1) fun k => abs_apply_le_seq w _ 1).1
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  congr 1
  · simp
  · congr 1
    funext k
    rw [show t + (k + 1) = t + 1 + k by omega, pow_succ]
    ring

/-- **The range of the common (A.8) is the kernel of `phiF`** (Woodford (2003), App. A.3, p. 632,
example): a forcing has a bounded solution iff `Σ_s 2^{−(s+1)} w_{s,y} = 0` (the unstable `y`
block, solved forwards, must meet `y_{−1} = 0`). -/
theorem range_linOp_F (w : SeqV (Fin 2)) : w ∈ Set.range (linOp Fsun) ↔ phiF w = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    set f : ℕ → ℝ := fun s => (1 / 2 : ℝ) ^ (s + 1) * linOp Fsun v s 1 with hf
    have hs : Summable f :=
      (geom_sum (fun s => linOp Fsun v s 1) fun s => abs_apply_le_seq _ s 1).1
    have hpart : ∀ N, ∑ s ∈ Finset.range N, f s = (1 / 2) ^ N * lagV 0 (fun r => v r) N 1 := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, ih, hf]
        simp only [linOp_F_y, lagV_succ]
        ring
    have hlag : ∀ N, |lagV 0 (fun r => v r) N 1| ≤ ‖v‖ := fun N => by
      cases N with
      | zero => simp
      | succ N => exact abs_apply_le_seq v N 1
    have ht2 : Filter.Tendsto (fun N => ∑ s ∈ Finset.range N, f s) Filter.atTop (𝓝 0) := by
      have hg : Filter.Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N * ‖v‖) Filter.atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).mul_const ‖v‖
      refine squeeze_zero_norm (fun N => ?_) hg
      rw [hpart, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hlag N) (by positivity)
    change ∑' s, f s = 0
    exact tendsto_nhds_unique hs.tendsto_sum_tsum_nat ht2
  · intro hφ
    have hφ' : ∑' s, (1 / 2 : ℝ) ^ (s + 1) * w s 1 = 0 := hφ
    have hyb : ∀ t, |ysF w t| ≤ ‖w‖ := fun t => by
      rw [ysF, abs_neg]
      exact (geom_sum (fun k => w (t + 1 + k) 1) fun k => abs_apply_le_seq w _ 1).2
    have hb : LinearSystems.BoundedSeq (fun t => ![xsF w t, ysF w t]) := ⟨2 * ‖w‖, fun t i => by
      fin_cases i
      · exact abs_xsF_le w t
      · exact (hyb t).trans (by linarith [norm_nonneg w])⟩
    refine ⟨toSeqV _ hb, seq_ext fun t => funext fun i => ?_⟩
    fin_cases i
    · change linOp Fsun (toSeqV _ hb) t 0 = w t 0
      rw [linOp_F_x]
      change xsF w (t + 1) - xsF w t / 2 = w t 0
      simp only [xsF]
      ring
    · change linOp Fsun (toSeqV _ hb) t 1 = w t 1
      rw [linOp_F_y]
      cases t with
      | zero =>
        change ysF w 0 - 2 * 0 = w 0 1
        have h := fwd_split w 0
        simp only [zero_add] at h
        rw [hφ'] at h
        rw [ysF]
        linarith
      | succ t =>
        change ysF w (t + 1) - 2 * ysF w t = w (t + 1) 1
        have h := fwd_split w (t + 1)
        rw [ysF, ysF]
        linarith

/-- **The common (A.8) is Fredholm, neither one-to-one nor onto** (Woodford (2003), App. A.3,
p. 632, example): its kernel is the line spanned by `kF ≠ 0`, its range is the kernel of the
continuous functional `phiF ≠ 0` (closed, codimension one). -/
theorem fredholm_linOp_F :
    ¬ Function.Injective (linOp Fsun) ∧ ¬ Function.Surjective (linOp Fsun) ∧
      IsClosed (Set.range (linOp Fsun)) ∧ phiF ≠ 0 ∧ kF ≠ 0 ∧
      (∀ v, linOp Fsun v = 0 ↔ v = v 0 0 • kF) ∧
      ∀ w, w ∈ Set.range (linOp Fsun) ↔ phiF w = 0 := by
  have he : LinearSystems.BoundedSeq
      (fun t => if t = 0 then ![(0 : ℝ), 1] else 0) := ⟨1, fun t i => by
    change |(if t = 0 then ![(0 : ℝ), 1] else 0) i| ≤ 1
    split_ifs
    · fin_cases i <;> simp
    · simp⟩
  have hφe : phiF (toSeqV _ he) = 1 / 2 := by
    change ∑' s, (1 / 2 : ℝ) ^ (s + 1) * (if s = 0 then ![(0 : ℝ), 1] else 0) 1 = 1 / 2
    rw [tsum_eq_single 0 (fun k hk => by simp [hk])]
    simp
  have hrange : Set.range (linOp Fsun) = phiF ⁻¹' {0} :=
    Set.ext fun w => (range_linOp_F w).trans (by simp)
  have hk : kF = kF 0 0 • kF := by
    rw [show kF 0 0 = 1 by change (1 / 2 : ℝ) ^ 0 = 1; simp, one_smul]
  refine ⟨fun hinj => ker_linOp_F.1 (hinj (by rw [map_zero]; exact (ker_linOp_F.2 kF).mpr hk)),
    fun hs => ?_, ?_, fun h0 => ?_, ker_linOp_F.1, ker_linOp_F.2, range_linOp_F⟩
  · have h := (range_linOp_F (toSeqV _ he)).mp (hs _)
    rw [hφe] at h
    norm_num at h
  · rw [hrange]
    exact isClosed_singleton.preimage phiF.continuous
  · rw [h0] at hφe
    norm_num at hφe

/-- Woodford (2003), App. A.3, p. 634 (example): `Fsun` is odd. -/
theorem Fsun_odd (q : Arg (Fin 2) ℝ) : Fsun (-q) = -Fsun q := by
  funext i
  fin_cases i <;> simp [Fsun] <;> ring

/-- **Random sunspots with a Fredholm (A.8)** (Woodford (2003), App. A.3, pp. 632–634, example):
for `Fsun`, on the coin tree, for every `ε > 0`, `x_1 = ±ε`, `x_{t+1} = x_t/2`, `y = 0` is a
bounded adapted equilibrium with no shocks, within `ε`, differing across the first flip. -/
theorem Fsun_random_sunspot {ε : ℝ} (hε : 0 < ε) :
    ∃ x : SProcV (Fin 2) (Bool × Bool), SolvesSV ExpectationsFiniteTree.coinSystem Fsun 0 x ∧
      ‖x‖ ≤ ε ∧ x (1, (true, true)) ≠ x (1, (false, true)) := by
  set P : ℕ → Fin 2 → ℝ := fun n => ![ε * (1 / 2) ^ n, 0] with hP
  have hM : ∀ n, ‖P n‖ ≤ ε := fun n => by
    refine (pi_norm_le_iff_of_nonneg hε.le).mpr fun i => ?_
    fin_cases i
    · simp only [hP, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_right hε.le (pow_le_one₀ (by norm_num) (by norm_num))
    · simp [hP, hε.le]
  refine ⟨brProc2 P hM, solvesSV_brProc2 Fsun_odd hM fun n => ?_, norm_brProc2_le hM hε.le,
    fun h => ?_⟩
  · funext i
    fin_cases i
    · simp [Fsun, hP]
      ring
    · cases n <;> simp [Fsun, hP]
  · have := congrFun h 0
    change ε * (1 / 2) ^ 0 = -(ε * (1 / 2) ^ 0) at this
    linarith

/-- **No sunspots with the same Fredholm (A.8)** (Woodford (2003), App. A.3, pp. 632–634,
example): under informational closure, the only bounded adapted equilibrium of `Fnone` with
`x_{−1} = 0` and no shocks is the steady state (`y_t = 2y_{t−1} + x_t² ≥ 2^k x_{t−k}²`). -/
theorem Fnone_unique {Ω : Type*} {𝔼 : ExpectationSystem Ω}
    (hcl : LocalIFTStochastic.Ops.InfoClosed 𝔼) {x : SProcV (Fin 2) Ω}
    (hx : SolvesSV 𝔼 Fnone 0 x) : x = 0 := by
  have hpt : ∀ t ω, x (t, ω) 1 = 2 * lagV 0 (fun s => x (s, ω)) t 1 + x (t, ω) 0 ^ 2 := by
    intro t ω
    have h := hx.2 t 1
    have hlag : 𝔼.E t (fun ω => lagV 0 (fun s => x (s, ω)) t 1) =
        fun ω => lagV 0 (fun s => x (s, ω)) t 1 := by
      cases t with
      | zero => exact 𝔼.const 0 _
      | succ s =>
        change 𝔼.E (s + 1) (toP x s 1) = toP x s 1
        conv_lhs => rw [← hx.1 s 1]
        rw [𝔼.known (Nat.le_succ s), hx.1 s 1]
    have hf : (fun ω => Fnone (ptS ((0 : ParS (Fin 2) ℝ Ω), x) (t, ω)) 1) =
        toP x t 1 - (2 : ℝ) • (fun ω => lagV 0 (fun s => x (s, ω)) t 1) -
          fun ω => toP x t 0 ω ^ 2 := by
      funext ω
      cases t <;> rfl
    have hk := known_comp hcl (hx.1 t 0) (fun z => z ^ 2)
    rw [hf, map_sub, map_sub, map_smul, hx.1 t 1, hlag, hk] at h
    have := congrFun h ω
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    change x (t, ω) 1 - _ - x (t, ω) 0 ^ 2 = 0 at this
    linarith
  have key : ∀ ω, (∀ t, x (t, ω) 0 = 0) ∧ ∀ t, x (t, ω) 1 = 0 := by
    intro ω
    set Y : ℕ → ℝ := fun t => x (t, ω) 1 with hY
    set X : ℕ → ℝ := fun t => x (t, ω) 0 with hX
    have hrec : ∀ t, Y (t + 1) = 2 * Y t + X (t + 1) ^ 2 := fun t => hpt (t + 1) ω
    have h0 : Y 0 = X 0 ^ 2 := by simpa using hpt 0 ω
    have hpos : ∀ t, 0 ≤ Y t := by
      intro t
      induction t with
      | zero => rw [h0]; positivity
      | succ t ih => rw [hrec]; positivity
    have hXY : ∀ t, X t ^ 2 ≤ Y t := by
      intro t
      cases t with
      | zero => rw [h0]
      | succ t => rw [hrec]; linarith [hpos t]
    have hgrow : ∀ t k, 2 ^ k * Y t ≤ Y (t + k) := by
      intro t k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [← add_assoc, hrec, pow_succ]
        nlinarith [sq_nonneg (X (t + k + 1))]
    have hYb : ∀ t, Y t ≤ ‖x‖ := fun t => (le_abs_self _).trans (abs_apply_le x t ω 1)
    have hXz : ∀ t, X t = 0 := by
      intro t
      by_contra hne
      have hp : 0 < X t ^ 2 := by positivity
      obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x‖ / X t ^ 2) (by norm_num : (1 : ℝ) < 2)
      rw [div_lt_iff₀ hp] at hk
      have := hgrow t k
      have := hYb (t + k)
      nlinarith [hXY t, pow_pos (by norm_num : (0 : ℝ) < 2) k]
    refine ⟨hXz, fun t => ?_⟩
    induction t with
    | zero => change Y 0 = 0; rw [h0, hXz 0]; ring
    | succ t ih =>
      change Y (t + 1) = 0
      rw [hrec, hXz (t + 1), show Y t = 0 from ih]
      ring
  ext ⟨t, ω⟩ i
  fin_cases i
  · exact (key ω).1 t
  · exact (key ω).2 t

/-- **A Fredholm (A.8) that is neither one-to-one nor onto does not decide the sunspot question**
(Woodford (2003), App. A.3, pp. 632–634, correction): `Fsun` and `Fnone` have the same (A.8)
(Fredholm: one-dimensional kernel, closed range of codimension one); the first has random
sunspots at every scale on the coin tree, the second only the steady state there. -/
theorem fredholm_undecided :
    linOp Fsun = linOp Fnone ∧ ¬ Function.Injective (linOp Fsun) ∧
      ¬ Function.Surjective (linOp Fsun) ∧ IsClosed (Set.range (linOp Fsun)) ∧
      (∀ ε > 0, ∃ x : SProcV (Fin 2) (Bool × Bool),
        SolvesSV ExpectationsFiniteTree.coinSystem Fsun 0 x ∧ ‖x‖ ≤ ε ∧
          x (1, (true, true)) ≠ x (1, (false, true))) ∧
      ∀ x : SProcV (Fin 2) (Bool × Bool),
        SolvesSV ExpectationsFiniteTree.coinSystem Fnone 0 x → x = 0 := by
  obtain ⟨h1, h2, h3, -⟩ := fredholm_linOp_F
  exact ⟨linOp_F.1, h1, h2, h3, fun _ hε => Fsun_random_sunspot hε,
    fun _ hx => Fnone_unique (LocalIFTStochastic.finiteTree_infoClosed _) hx⟩

end Woodford.PriceLevelDetermination.SunspotsNotOntoMore
