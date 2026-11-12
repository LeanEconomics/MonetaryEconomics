/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.NonlinearRotembergRamseyAEIFT
import StabilizationWelfare.NonlinearRotembergRamseyMarkov
import StabilizationWelfare.NonlinearNKMarkovRamseyAR1

/-!
# The Markov representation of the a.s. Rotemberg Ramsey equilibrium with an AR(1) of any law

Woodford (2003), *Interest and Prices*, Chapter 7, §1–2 (the timeless Ramsey plan as a
time-invariant function of the predetermined multiplier and the exogenous state), Chapter 6, §1,
and Appendix A.3, for the exact Rotemberg Ramsey conditions; the construction of
`NonlinearNKMarkovRamseyAR1` (Calvo), restated for the Rotemberg system.

The Markov policy is built on an event tree whose roots are all pairs
`(d, x) ∈ {‖d‖ ≤ δ} × [−B̄, B̄]` (initial lag, initial AR(1) state) and whose branches are the
innovation histories, with the transition expectation the Hahn–Banach extension of `∫ · dν`
(`arTree`). On it `MeasV`/`MN` (measurability in `(root, innovations)`) passes through the
expectation, the lag, the backward and forward solutions, hence through the Rotemberg inverse
(`measV_LinvR`) and the Newton map (`tree_sol`); `shift_eq` identifies a solution at a node with
the solution of another tree at the root `(lag, state)`, and `tree_root_congr` shows the
dependence on the lag only through `λ̂_{t−1}`.

* **`ramsey_ar1_markov`**: on the i.i.d. product space of ANY bounded innovation law, the adapted,
  a.s. unique Rotemberg Ramsey equilibrium is `z_t = G(z_{t−1}, x_t)` a.s. with one measurable
  `G`, depending on `z_{t−1}` only through `λ̂_{t−1}`.
-/

namespace Woodford.StabilizationWelfare.NonlinearRotembergRamseyAR1

open MeasureTheory ProbabilityTheory Filter Topology
open NonlinearNKMarkov (Mv IsMarkov Mv_norm_le mnorm mnorm_nonneg iter_norm_le norm_mulVec_le)
open NonlinearNKMarkovGeneral (ARState fwdSol)
open NonlinearNKMarkovRamseyTree (LagTree lag0 bwd bwd_eq fwdS fwdS_spec lagv lb2 lbM norm_lagv_le
  summable_c)
open NonlinearNKMarkovRamseyIFT (remainder_gen)
open NonlinearNKMarkovAR1Markov
open NonlinearNKMarkovRamseyAR1 (ofFn_snoc ofFn_init measurable_snoc' measurable_init' ΛR ΛR_spec
  ΛR_const innov ofFn_innov_succ measurable_innov)
open NonlinearRotemberg NonlinearRotembergRamsey NonlinearRotembergRamseyLin
open NonlinearRotembergRamseyTree NonlinearRotembergRamseyIFT
open NonlinearRotembergRamseyMarkov (Qd_congr)

/-! ## The event tree of all initial conditions -/

/-- Woodford (2003), Ch. 7: the roots, an initial lag `‖d‖ ≤ δ` and an initial AR(1) state. -/
abbrev Root (δ Bx : ℝ) : Type := {d : Fin 5 → ℝ // ‖d‖ ≤ δ} × ARState Bx

/-- Woodford (2003), Ch. 7: the nodes, a root and a history of innovations. -/
abbrev Node (δ Bx : ℝ) : Type := Root δ Bx × List ℝ

/-- Woodford (2003), Ch. 6, §1: the transition expectation, a sup-bounded linear extension of
`∫ · dν` to all functions of the innovation. -/
noncomputable def ΛR (ν : ProbabilityMeasure ℝ) : (ℝ → ℝ) →ₗ[ℝ] ℝ :=
  Classical.choose (hbExt (ν : Measure ℝ))

/-- The defining properties of `ΛR`. -/
theorem ΛR_spec (ν : ProbabilityMeasure ℝ) :
    (∀ f : ℝ → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) → ΛR ν f = ∫ x, f x ∂(ν : Measure ℝ)) ∧
      ∀ (h : ℝ → ℝ) (C : ℝ), (∀ x, |h x| ≤ C) → |ΛR ν h| ≤ C :=
  Classical.choose_spec (hbExt (ν : Measure ℝ))

/-- Woodford (2003), Ch. 6, §1: the expectation of next-period values on the tree. -/
noncomputable def treeM (ν : ProbabilityMeasure ℝ) (δ Bx : ℝ) :
    (Node δ Bx → ℝ) →ₗ[ℝ] (Node δ Bx → ℝ) where
  toFun h x := ΛR ν (fun e => h (x.1, x.2 ++ [e]))
  map_add' h k := funext fun x => map_add (ΛR ν) (fun e => h (x.1, x.2 ++ [e]))
    (fun e => k (x.1, x.2 ++ [e]))
  map_smul' c h := funext fun x => map_smul (ΛR ν) c (fun e => h (x.1, x.2 ++ [e]))

/-- `ΛR` of a constant. -/
theorem ΛR_const (ν : ProbabilityMeasure ℝ) (c : ℝ) : ΛR ν (fun _ => c) = c := by
  rw [(ΛR_spec ν).1 _ measurable_const ⟨|c|, fun _ => le_rfl⟩, integral_const, probReal_univ,
    one_smul]

/-- Woodford (2003), Ch. 7 and App. A.3 (**the AR(1) event tree of all initial conditions**). -/
noncomputable def arTree (ν : ProbabilityMeasure ℝ) (δ Bx : ℝ) : LagTree (Node δ Bx) where
  M := treeM ν δ Bx
  markov := ⟨funext fun x => ΛR_const ν 1, fun h C hC x => (ΛR_spec ν).2 _ C fun e => hC _⟩
  par x := (x.1, x.2.dropLast)
  depth x := x.2.length
  depth_par x hx := by simp only [List.length_dropLast]; omega
  M_par f := funext fun x => by
    change ΛR ν (fun e => f (x.1, (x.2 ++ [e]).dropLast)) = f x
    simp only [List.dropLast_concat]
    exact ΛR_const ν _
  M_root f g h := funext fun x => by
    change ΛR ν (fun e => f (x.1, x.2 ++ [e])) = ΛR ν (fun e => g (x.1, x.2 ++ [e]))
    congr 1
    funext e
    exact h _ (by simp)

/-- Woodford (2003), Ch. 6, §1: the AR(1) state at a node, `x_{t+1} = ρx_t + e_{t+1}`
(projected on `[−B̄, B̄]`). -/
noncomputable def stateN (ρ Bx : ℝ) (hB : 0 ≤ Bx) {δ : ℝ} (x : Node δ Bx) : ARState Bx :=
  x.2.foldl (fun s e => arSucc ρ Bx hB s e) x.1.2

/-- The state after one more innovation. -/
theorem stateN_snoc (ρ Bx : ℝ) (hB : 0 ≤ Bx) {δ : ℝ} (q : Root δ Bx) (l : List ℝ) (e : ℝ) :
    stateN ρ Bx hB (q, l ++ [e]) = arSucc ρ Bx hB (stateN ρ Bx hB (q, l)) e := by
  simp [stateN, List.foldl_append]

/-! ## Measurability on the tree -/

variable {δ Bx : ℝ}

/-- Woodford (2003), App. A.3: a vector function of the nodes measurable in
`(root, innovations)` at every date. -/
def MeasV {k : ℕ} (z : Node δ Bx → Fin k → ℝ) : Prop :=
  ∀ n, Measurable (fun w : Root δ Bx × (Fin n → ℝ) => z (w.1, List.ofFn w.2))

/-- Components of `MeasV` functions. -/
theorem MeasV.comp {k : ℕ} {z : Node δ Bx → Fin k → ℝ} (hz : MeasV z) (i : Fin k) :
    MeasV (fun x => ![z x i]) := fun n =>
  measurable_pi_iff.2 fun j => by fin_cases j; exact (measurable_pi_apply i).comp (hz n)

/-- `MeasV` from components. -/
theorem measV_of {k : ℕ} {z : Node δ Bx → Fin k → ℝ}
    (h : ∀ i, MeasV (fun x => ![z x i])) : MeasV z := fun n =>
  measurable_pi_iff.2 fun i => (measurable_pi_apply 0).comp (h i n)

/-- The innovation slice of a `MeasV` function is measurable. -/
theorem MeasV.slice {k : ℕ} {z : Node δ Bx → Fin k → ℝ} (hz : MeasV z) (x : Node δ Bx) :
    Measurable (fun e => z (x.1, x.2 ++ [e])) := by
  have e1 : ∀ e : ℝ, x.2 ++ [e] = List.ofFn (Fin.snoc x.2.get e : Fin (x.2.length + 1) → ℝ) :=
    fun e => by rw [ofFn_snoc, List.ofFn_get]
  simp only [e1]
  exact (hz (x.2.length + 1)).comp (measurable_const.prodMk
    ((measurable_snoc' _).comp (measurable_const.prodMk measurable_id)))

/-- Woodford (2003), App. A.3: the tree expectation of a bounded `MeasV` function is `MeasV`. -/
theorem measV_Mv (ν : ProbabilityMeasure ℝ) {k : ℕ} {h : Node δ Bx → Fin k → ℝ} (hh : MeasV h)
    {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) : MeasV (Mv (treeM ν δ Bx) h) := by
  refine measV_of fun i n => measurable_pi_iff.2 fun j => ?_
  fin_cases j
  have hci : ∀ x, |h x i| ≤ C := fun x => by
    have := (norm_le_pi_norm (h x) i).trans (hC x); rwa [Real.norm_eq_abs] at this
  have e : (fun w : Root δ Bx × (Fin n → ℝ) => (![Mv (treeM ν δ Bx) h (w.1, List.ofFn w.2) i] :
      Fin 1 → ℝ) ⟨0, by norm_num⟩) = fun w => ∫ e, h (w.1, List.ofFn (Fin.snoc w.2 e)) i
        ∂(ν : Measure ℝ) := by
    funext w
    simp only [Fin.zero_eta, Matrix.cons_val_zero, Mv]
    change ΛR ν (fun e => h (w.1, List.ofFn w.2 ++ [e]) i) = _
    have hm : Measurable (fun e => h (w.1, List.ofFn w.2 ++ [e]) i) :=
      (measurable_pi_apply i).comp (hh.slice (w.1, List.ofFn w.2))
    rw [(ΛR_spec ν).1 _ hm ⟨C, fun e => hci _⟩]
    simp only [ofFn_snoc]
  rw [e]
  have hF : Measurable (fun p : (Root δ Bx × (Fin n → ℝ)) × ℝ =>
      h (p.1.1, List.ofFn (Fin.snoc p.1.2 p.2 : Fin (n + 1) → ℝ)) i) :=
    (measurable_pi_apply i).comp ((hh (n + 1)).comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snoc' n).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))))
  exact hF.stronglyMeasurable.integral_prod_right'.measurable

/-- Woodford (2003), Ch. 7: the lag preserves `MeasV`. -/
theorem measV_lag0 (ν : ProbabilityMeasure ℝ) {f : Node δ Bx → ℝ} (hf : MeasV fun x => ![f x]) :
    MeasV fun x => ![lag0 (arTree ν δ Bx) f x] := by
  intro n
  cases n with
  | zero =>
    have e : (fun w : Root δ Bx × (Fin 0 → ℝ) =>
        (![lag0 (arTree ν δ Bx) f (w.1, List.ofFn w.2)] : Fin 1 → ℝ)) = fun _ => ![0] := by
      funext w; simp [lag0, arTree]
    rw [e]; exact measurable_const
  | succ m =>
    have e : (fun w : Root δ Bx × (Fin (m + 1) → ℝ) =>
        (![lag0 (arTree ν δ Bx) f (w.1, List.ofFn w.2)] : Fin 1 → ℝ)) =
          fun w => ![f (w.1, List.ofFn (Fin.init w.2))] := by
      funext w; simp [lag0, arTree, ofFn_init]
    rw [e]
    exact (hf m).comp (measurable_fst.prodMk ((measurable_init' m).comp measurable_snd))

/-- Woodford (2003), Ch. 7: backward solutions preserve `MeasV`. -/
theorem measV_bwd (ν : ProbabilityMeasure ℝ) (c : ℝ) {f : Node δ Bx → ℝ}
    (hf : MeasV fun x => ![f x]) : MeasV fun x => ![bwd (arTree ν δ Bx) c f x] := by
  intro n
  induction n with
  | zero =>
    have e : (fun w : Root δ Bx × (Fin 0 → ℝ) =>
        (![bwd (arTree ν δ Bx) c f (w.1, List.ofFn w.2)] : Fin 1 → ℝ)) =
          fun w => ![f (w.1, List.ofFn w.2)] := by
      funext w; simp [bwd, arTree]
    rw [e]; exact hf 0
  | succ m ih =>
    have e : (fun w : Root δ Bx × (Fin (m + 1) → ℝ) =>
        (![bwd (arTree ν δ Bx) c f (w.1, List.ofFn w.2)] : Fin 1 → ℝ)) =
          fun w => ![c * bwd (arTree ν δ Bx) c f (w.1, List.ofFn (Fin.init w.2)) +
            f (w.1, List.ofFn w.2)] := by
      funext w
      rw [bwd_eq]
      simp [lag0, arTree, ofFn_init]
    rw [e]
    refine measurable_pi_iff.2 fun j => ?_
    fin_cases j
    simp only [Fin.zero_eta, Matrix.cons_val_zero]
    exact (((measurable_pi_apply 0).comp (ih.comp (measurable_fst.prodMk
      ((measurable_init' m).comp measurable_snd)))).const_mul c).add
      ((measurable_pi_apply 0).comp (hf (m + 1)))

/-- Woodford (2003), (A.13): forward solutions of bounded `MeasV` functions are `MeasV`. -/
theorem measV_fwdSol (ν : ProbabilityMeasure ℝ) {k : ℕ} {B : Matrix (Fin k) (Fin k) ℝ}
    (hB : Summable fun j => mnorm (B ^ j)) {b : Node δ Bx → Fin k → ℝ} (hb : MeasV b)
    {C : ℝ} (hC : ∀ x, ‖b x‖ ≤ C) : MeasV (fwdSol B (treeM ν δ Bx) b) := by
  have hC0 : ∀ x, ‖b x‖ ≤ max C 0 := fun x => (hC x).trans (le_max_left _ _)
  have hit : ∀ j, MeasV ((Mv (treeM ν δ Bx))^[j] b) := by
    intro j
    induction j with
    | zero => exact hb
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact measV_Mv ν ih (iter_norm_le (arTree ν δ Bx).markov j (le_max_right _ _) hC0)
  intro n
  refine measurable_of_tendsto_metrizable (f := fun N w => ∑ j ∈ Finset.range N,
    (B ^ j).mulVec ((Mv (treeM ν δ Bx))^[j] b (w.1, List.ofFn w.2)))
    (fun N => Finset.measurable_fun_sum _ fun j _ =>
      (Matrix.mulVecLin (B ^ j)).continuous_of_finiteDimensional.measurable.comp (hit j n))
    (tendsto_pi_nhds.2 fun w => ?_)
  exact (Summable.of_norm_bounded (hB.mul_right (max C 0)) fun j => (norm_mulVec_le _ _).trans
    (mul_le_mul_of_nonneg_left (iter_norm_le (arTree ν δ Bx).markov j (le_max_right _ _) hC0 _)
      (mnorm_nonneg _))).hasSum.tendsto_sum_nat

/-- A scalar function measurable at every date. -/
def MN (f : Node δ Bx → ℝ) : Prop := MeasV fun x => ![f x]

/-- `MN` as plain measurability at each date. -/
theorem MN.meas {f : Node δ Bx → ℝ} (hf : MN f) (n : ℕ) :
    Measurable (fun w : Root δ Bx × (Fin n → ℝ) => f (w.1, List.ofFn w.2)) :=
  (measurable_pi_apply 0).comp (hf n)

/-- `MN` from plain measurability at each date. -/
theorem MN.of {f : Node δ Bx → ℝ}
    (h : ∀ n, Measurable (fun w : Root δ Bx × (Fin n → ℝ) => f (w.1, List.ofFn w.2))) : MN f :=
  fun n => measurable_pi_iff.2 fun j => by fin_cases j; exact h n

/-- `MN` up to a pointwise identity. -/
theorem MN.congr {f g : Node δ Bx → ℝ} (hf : MN f) (e : ∀ x, g x = f x) : MN g := by
  have : g = f := funext e
  rw [this]; exact hf

/-- Two-term combinations preserve `MN`. -/
theorem mn_lin2 {f g : Node δ Bx → ℝ} (hf : MN f) (hg : MN g) (a b : ℝ) :
    MN (fun x => a * f x + b * g x) :=
  MN.of fun n => ((hf.meas n).const_mul a).add ((hg.meas n).const_mul b)

/-- Components of a `MeasV` vector are `MN`. -/
theorem mn_comp {k : ℕ} {z : Node δ Bx → Fin k → ℝ} (hz : MeasV z) (i : Fin k) :
    MN (fun x => z x i) := hz.comp i

/-- The tree expectation of a bounded `MN` function is `MN`. -/
theorem mn_M (ν : ProbabilityMeasure ℝ) {f : Node δ Bx → ℝ} (hf : MN f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : MN ((arTree ν δ Bx).M f) := by
  have h := measV_Mv ν hf (C := C) fun x => (pi_norm_le_iff_of_nonneg
    ((abs_nonneg _).trans (hC x))).2 fun i => by fin_cases i; simpa using hC x
  exact MN.of fun n => (measurable_pi_apply 0).comp (h n)

/-- The lag preserves `MN`. -/
theorem mn_lag (ν : ProbabilityMeasure ℝ) {f : Node δ Bx → ℝ} (hf : MN f) :
    MN (lag0 (arTree ν δ Bx) f) := measV_lag0 ν hf

/-- Backward solutions preserve `MN`. -/
theorem mn_bwd (ν : ProbabilityMeasure ℝ) (c : ℝ) {f : Node δ Bx → ℝ} (hf : MN f) :
    MN (bwd (arTree ν δ Bx) c f) := measV_bwd ν c hf

/-- Forward solutions of bounded `MN` functions are `MN`. -/
theorem mn_fwdS (ν : ProbabilityMeasure ℝ) {c : ℝ} (hc : |c| < 1) {f : Node δ Bx → ℝ}
    (hf : MN f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : MN (fwdS (arTree ν δ Bx) c f) := by
  have hb : ∀ x, ‖(![f x] : Fin 1 → ℝ)‖ ≤ C := fun x => (pi_norm_le_iff_of_nonneg
    ((abs_nonneg _).trans (hC x))).2 fun i => by fin_cases i; simpa using hC x
  have h := measV_fwdSol ν (summable_c hc) hf hb
  exact MN.of fun n => (measurable_pi_apply 0).comp (h n)

/-- Woodford (2003), App. A.3: the inverse of the linearised Rotemberg Ramsey operator preserves
measurability on the AR(1) tree (for bounded forcings). -/
theorem measV_LinvR (ν : ProbabilityMeasure ℝ) {p : Par} (hp : p.Basic) (hG : 0 < Gw p)
    {r : Node δ Bx → Fin 5 → ℝ} (hr : MeasV r) {A : ℝ} (hA : 0 ≤ A)
    (hrb : ∀ y k, |r y k| ≤ A) : MeasV (LinvR (arTree ν δ Bx) p r) := by
  set T := arTree ν δ Bx
  have hc : ∀ k, MN (fun x => r x k) := fun k => mn_comp hr k
  obtain ⟨ch, -, bh⟩ := bd_hv hp hG
  have hr1M : MN (T.M fun y => r y 1) := mn_M ν (hc 1) (hrb · 1)
  have hs : MN (sv p r) := (mn_lin2 (mn_lin2 (hc 4) (hc 0) (cR4 p) (-1)) (hc 2) (1 / Gw p)
    (-(1 / Gw p))).congr fun x => by simp only [sv]; field_simp; ring
  have hh : MN (hv T p r) := by
    have e1 := mn_lin2 (mn_lin2 (hc 3) (hc 4) 1 (p.θ * p.m * p.ω)) hs 1 (p.θ * p.m * (p.σ + p.ω))
    have e2 := mn_lin2 (hc 1) hr1M 1 (-p.β)
    exact (mn_lin2 e1 e2 (gamb p / p.ψ) (1 / p.ψ)).congr fun x => by simp only [hv]; ring
  have hu : MN (uv T p r) := by
    have hin : MN (fun x => hv T p r x / (p.β * z2R p)) :=
      (mn_lin2 hh hh (1 / (p.β * z2R p)) 0).congr fun x => by ring
    have hbin : ∀ x, |hv T p r x / (p.β * z2R p)| ≤ |1 / (p.β * z2R p)| * (ch * A) :=
      fun x => by
        rw [div_eq_mul_one_div, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (bh T r A hA hrb x) (abs_nonneg _)
    exact mn_fwdS ν (abs_inv_z2R hp hG) hin hbin
  have hl : MN (lv T p r) := mn_bwd ν _ hu
  have hll := mn_lag ν hl
  have hcv : MN (cv T p r) := (mn_lin2 hl hs (-aR p) 1).congr fun x => by simp only [cv]; ring
  have hyv : MN (yv T p r) := (mn_lin2 hcv (hc 4) 1 1).congr fun x => by simp only [yv]; ring
  have hpiv : MN (piv T p r) := (mn_lin2 (mn_lin2 hl hll 1 (-1)) (hc 1) (1 / gamb p)
    (-(1 / (gamb p * p.ψ)))).congr fun x => by simp only [piv]; ring
  have hgv : MN (gv T p r) := by
    have e1 := mn_lin2 hcv hl (1 - p.σ - gamb p + lamb p * (p.θ * p.m * p.σ) * p.σ)
      (-(p.θ * p.m * p.σ))
    have e2 := mn_lin2 hyv (hc 2) (-(lamb p * (p.θ * p.m * p.σ))) (-1)
    exact (mn_lin2 e1 e2 1 1).congr fun x => by simp only [gv]; ring
  refine measV_of fun i => ?_
  fin_cases i
  · exact hyv.congr fun x => by simp [LinvR]
  · exact hpiv.congr fun x => by simp [LinvR]
  · exact hcv.congr fun x => by simp [LinvR]
  · exact hl.congr fun x => by simp [LinvR]
  · exact hgv.congr fun x => by simp [LinvR]

/-! ## Existence with an invariant on event trees -/

/-- Woodford (2003), Ch. 7 and App. A.3 (**`ramsey_existence` with an invariant**): the
Newton–Picard solution lies in every set of processes containing `0`, invariant under the Newton
map on the ball of radius `r` and closed under pointwise limits of sequences in that ball. -/
theorem ramsey_existence_inv {p : Par} (hp : p.Basic) (hG : 0 < Gw p) :
    ∃ r > 0, ∃ δ > 0, ∃ C > 0, ∀ {Y : Type*} (T : LagTree Y) (e : Y → Fin 3 → ℝ)
      (d : Y → Fin 5 → ℝ), (∀ y, ‖e y‖ ≤ δ) → (∀ y, ‖d y‖ ≤ δ) →
        ∃ z : Y → Fin 5 → ℝ, ((∀ y, ‖z y‖ ≤ r) ∧ PhiR T p e d z = 0) ∧
          (∀ z' : Y → Fin 5 → ℝ, (∀ y, ‖z' y‖ ≤ r) → PhiR T p e d z' = 0 → z' = z) ∧
          (∀ τ', 0 ≤ τ' → (∀ y, ‖PhiR T p e d (fun _ => 0) y‖ ≤ τ') → ∀ y, ‖z y‖ ≤ C * τ') ∧
          ∀ A : (Y → Fin 5 → ℝ) → Prop, A (fun _ => 0) →
            (∀ w, (∀ y, ‖w y‖ ≤ r) → A w → A (fun x => w x - LinvR T p (PhiR T p e d w) x)) →
            (∀ (ws : ℕ → Y → Fin 5 → ℝ) (w : Y → Fin 5 → ℝ), (∀ n, A (ws n)) →
              (∀ n y, ‖ws n y‖ ≤ r) → (∀ x, Tendsto (fun n => ws n x) atTop (𝓝 (w x))) → A w) →
            A z := by
  obtain ⟨K, hK0, hK⟩ := LinvR_bound hp hG
  set K' := K + 1 with hK'
  have hK'0 : 0 < K' := by linarith
  set η := 1 / (8 * K') with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨ρQ, hρQ, hQ⟩ := remainder_gen (contDiff_Qd (n := 1) p) hη0
  obtain ⟨ρN, hρN, hN⟩ := remainder_gen (g := fun q : (Fin 3 → ℝ) × (Fin 5 → ℝ) => Nd p q.2)
    ((contDiff_Nd (n := 1) p).comp contDiff_snd) hη0
  set r := min ρQ ρN with hr
  have hr0 : 0 < r := lt_min hρQ hρN
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 3 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ))
    r).exists_bound_of_continuousOn ((contDiff_Qd (n := 0) p).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin 5 → ℝ) r).exists_bound_of_continuousOn
    ((contDiff_Nd (n := 0) p).continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self hr0.le))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr0.le))
  set τ := r / (2 * K') with hτ
  have hτ0 : 0 < τ := by positivity
  obtain ⟨δQ, hδQ, hQc⟩ := Metric.continuousAt_iff.1
    ((contDiff_Qd (n := 0) p).continuous.continuousAt (x := 0)) τ hτ0
  refine ⟨r, hr0, min r (δQ / 2), lt_min hr0 (by positivity), 2 * K', by positivity,
    fun {Y} T e d he hd => ?_⟩
  have hKK : ∀ (s : Y → Fin 5 → ℝ) (A : ℝ), 0 ≤ A →
      (∀ y, ‖s y‖ ≤ A) → ∀ y, ‖LinvR T p s y‖ ≤ K' * A := fun s A hA hs y =>
    (hK T s A hA hs y).trans (mul_le_mul_of_nonneg_right (by linarith) hA)
  have heR : ∀ y, ‖e y‖ ≤ r := fun y => (he y).trans (min_le_left _ _)
  have hdR : ∀ y, ‖d y‖ ≤ r := fun y => (hd y).trans (min_le_left _ _)
  have hlag : ∀ z : Y → Fin 5 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖lagI T z d x‖ ≤ r := fun z hz x => by
    unfold lagI; split_ifs
    · exact hdR x
    · exact hz _
  have hin : ∀ z : Y → Fin 5 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x,
      (e x, lagI T z d x, z x) ∈ Metric.closedBall (0 : (Fin 3 → ℝ) × (Fin 5 → ℝ) ×
        (Fin 5 → ℝ)) r := fun z hz x => by
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    exact max_le (heR x) (max_le (hlag z hz x) (hz x))
  have hPhiB : ∀ z : Y → Fin 5 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖PhiR T p e d z x‖ ≤ CQ + CN :=
    fun z hz x => (norm_add_le _ _).trans (add_le_add (hCQ _ (hin z hz x))
      (Mv_norm_le T.markov hCN0 (fun y => hCN _ (by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hz y)) x))
  -- the Newton map
  set Tm : (Y → Fin 5 → ℝ) → (Y → Fin 5 → ℝ) :=
    fun Z x => Z x - LinvR T p (PhiR T p e d Z) x with hTm
  have hcontr : ∀ z z' : Y → Fin 5 → ℝ, (∀ y, ‖z y‖ ≤ r) → (∀ y, ‖z' y‖ ≤ r) → ∀ D,
      (∀ y, ‖z y - z' y‖ ≤ D) → ∀ x, ‖Tm z x - Tm z' x‖ ≤ D / 2 := by
    intro z z' hz hz' D hD x
    have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD x)
    set CL := ‖LinearMap.toContinuousLinearMap (DLin p)‖
    have hLz : ∀ y, ‖LR T p (fun y => z y - z' y) y‖ ≤ CL * D :=
      norm_LR_le T p hD0 hD
    have hdPhi : ∀ y, ‖PhiR T p e d z y - PhiR T p e d z' y‖ ≤ (CQ + CN) + (CQ + CN) :=
      fun y => (norm_sub_le _ _).trans (add_le_add (hPhiB z hz y) (hPhiB z' hz' y))
    -- the remainder
    have hrem : ∀ y, ‖(PhiR T p e d z y - PhiR T p e d z' y) -
        LR T p (fun y => z y - z' y) y‖ ≤ η * D + η * D := by
      intro y
      have hl := lagv_sub_lagI T z z' d y
      have hu1 : ‖(lagI T z d y, z y)‖ ≤ ρQ := by
        rw [Prod.norm_def]
        exact max_le ((hlag z hz y).trans (min_le_left _ _)) ((hz y).trans (min_le_left _ _))
      have hu2 : ‖(lagI T z' d y, z' y)‖ ≤ ρQ := by
        rw [Prod.norm_def]
        exact max_le ((hlag z' hz' y).trans (min_le_left _ _)) ((hz' y).trans (min_le_left _ _))
      have hq := hQ (e y) (lagI T z d y, z y) (lagI T z' d y, z' y)
        ((heR y).trans (min_le_left _ _)) hu1 hu2
      rw [Prod.mk_sub_mk, show fderiv ℝ (Qd p) ((0 : Fin 3 → ℝ),
        (0 : (Fin 5 → ℝ) × (Fin 5 → ℝ))) = fderiv ℝ (Qd p) 0 from rfl, fderiv_Qd] at hq
      have hqD : ‖(lagI T z d y, z y) - (lagI T z' d y, z' y)‖ ≤ D := by
        rw [Prod.mk_sub_mk, Prod.norm_def, ← hl]
        exact max_le (norm_lagv_le T hD0 hD y) (hD y)
      have hnB : ∀ y', ‖Nd p (z y') - Nd p (z' y') - DNr p (z y' - z' y')‖ ≤ η * D :=
        fun y' => by
          have h := hN 0 (z y') (z' y') (by rw [norm_zero]; exact hρN.le)
            ((hz y').trans (min_le_right _ _))
            ((hz' y').trans (min_le_right _ _))
          rw [fderiv_Nd_snd] at h
          exact h.trans (mul_le_mul_of_nonneg_left (hD y') hη0.le)
      have hMv := Mv_norm_le T.markov (by positivity) hnB y
      have e1 : Mv T.M (fun y' => Nd p (z y') - Nd p (z' y') - DNr p (z y' - z' y')) y =
          Mv T.M (fun y' => Nd p (z y')) y - Mv T.M (fun y' => Nd p (z' y')) y -
            DNr p (Mv T.M (fun y' => z y' - z' y') y) := by
        rw [NonlinearNKMarkovLinks.Mv_sub, NonlinearNKMarkovLinks.Mv_sub]
        simp only
        rw [Mv_DNr]
      rw [e1] at hMv
      have e2 : (PhiR T p e d z y - PhiR T p e d z' y) - LR T p (fun y => z y - z' y) y =
          (Qd p (e y, lagI T z d y, z y) - Qd p (e y, lagI T z' d y, z' y) -
            DQr p (lagI T z d y - lagI T z' d y) (z y - z' y)) +
          (Mv T.M (fun y' => Nd p (z y')) y - Mv T.M (fun y' => Nd p (z' y')) y -
            DNr p (Mv T.M (fun y' => z y' - z' y') y)) := by
        simp only [PhiR, LR, hl]
        abel
      rw [e2]
      exact (norm_add_le _ _).trans (add_le_add (hq.trans
        (mul_le_mul_of_nonneg_left hqD hη0.le)) hMv)
    have hs1 := LinvR_sub T hp hG (r := PhiR T p e d z) (r' := PhiR T p e d z')
      (A := CQ + CN) (A' := CQ + CN) (by positivity)
      (by positivity) (hPhiB z hz) (hPhiB z' hz')
    have hs2 := LinvR_sub T hp hG (A := (CQ + CN) + (CQ + CN)) (A' := CL * D)
      (by positivity) (by positivity) hdPhi hLz
    have hLL := LinvR_LR T hp hG hD0 hD
    have key : Tm z x - Tm z' x = -LinvR T p (fun y => (PhiR T p e d z y -
        PhiR T p e d z' y) - LR T p (fun y => z y - z' y) y) x := by
      rw [hs2]
      simp only [hTm]
      rw [hs1, hLL]
      funext i
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    rw [key, norm_neg]
    calc _ ≤ K' * (η * D + η * D) := hKK _ _ (by positivity) hrem x
      _ = D / 4 := by rw [hη]; field_simp; ring
      _ ≤ D / 2 := by linarith
  -- `T 0` is small
  have hT0 : ∀ x, ‖Tm (fun _ => 0) x‖ ≤ r / 2 := by
    intro x
    have hb : ∀ y, ‖PhiR T p e d (fun _ => 0) y‖ ≤ τ := fun y => by
      have hss := Qd_Nd_zero hp
      have e1 : PhiR T p e d (fun _ => 0) y =
          Qd p (e y, lagI T (fun _ => 0) d y, 0) - Qd p 0 := by
        simp only [PhiR, Mv_const']
        rw [eq_neg_of_add_eq_zero_right hss]
        abel
      rw [e1, ← dist_eq_norm]
      refine (hQc ?_).le
      rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
      have hl : ‖lagI T (fun _ => (0 : Fin 5 → ℝ)) d y‖ ≤ δQ / 2 := by
        unfold lagI; split_ifs
        · exact (hd y).trans (min_le_right _ _)
        · rw [norm_zero]; positivity
      have h0 : ‖(0 : Fin 5 → ℝ)‖ ≤ δQ / 2 := by rw [norm_zero]; positivity
      exact lt_of_le_of_lt (max_le ((he y).trans (min_le_right _ _)) (max_le hl h0))
        (by linarith)
    have h := hKK _ τ hτ0.le hb x
    simp only [hTm, zero_sub, norm_neg]
    calc _ ≤ K' * τ := h
      _ = r / 2 := by rw [hτ]; field_simp
  have hball : ∀ z : Y → Fin 5 → ℝ, (∀ y, ‖z y‖ ≤ r) → ∀ x, ‖Tm z x‖ ≤ r := by
    intro z hz x
    have h1 := hcontr z (fun _ => 0) hz (fun y => by simp [hr0.le]) r
      (fun y => by simpa using hz y) x
    calc ‖Tm z x‖ ≤ ‖Tm z x - Tm (fun _ => 0) x‖ + ‖Tm (fun _ => 0) x‖ := by
          have := norm_add_le (Tm z x - Tm (fun _ => 0) x) (Tm (fun _ => 0) x); simpa using this
      _ ≤ r / 2 + r / 2 := add_le_add h1 (hT0 x)
      _ = r := by ring
  -- Picard iteration
  set zs : ℕ → Y → Fin 5 → ℝ := fun n => Tm^[n] (fun _ => 0) with hzs
  have hzsB : ∀ n x, ‖zs n x‖ ≤ r := by
    intro n
    induction n with
    | zero => intro x; simp [hzs, hr0.le]
    | succ n ih =>
      intro x
      simp only [hzs, Function.iterate_succ_apply']
      exact hball _ ih x
  have hstep : ∀ n x, ‖zs n x - zs (n + 1) x‖ ≤ r / 2 / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      simp only [hzs, Function.iterate_zero, id, pow_zero, div_one]
      rw [norm_sub_rev]; simpa using hT0 x
    | succ n ih =>
      intro x
      have h := hcontr (zs (n + 1)) (zs n) (hzsB _) (hzsB _) (r / 2 / 2 ^ n)
        (fun x => by rw [norm_sub_rev]; exact ih x) x
      have e1 : zs (n + 1 + 1) = Tm (zs (n + 1)) := by
        simp only [hzs, Function.iterate_succ_apply']
      have e2 : zs (n + 1) = Tm (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e1, norm_sub_rev]
      conv_lhs => rw [show zs (n + 1) x = Tm (zs n) x from congrFun e2 x]
      calc _ ≤ r / 2 / 2 ^ n / 2 := h
        _ = r / 2 / 2 ^ (n + 1) := by rw [pow_succ]; ring
  have hcau : ∀ x, CauchySeq fun n => zs n x := fun x =>
    cauchySeq_of_le_geometric_two (C := r) fun n => by rw [dist_eq_norm]; exact hstep n x
  choose z hz using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hzdist : ∀ n x, ‖zs n x - z x‖ ≤ r / 2 ^ n := fun n x => by
    have := dist_le_of_le_geometric_two_of_tendsto (C := r) (f := fun n => zs n x)
      (fun n => by rw [dist_eq_norm]; exact hstep n x) (hz x) n
    rwa [dist_eq_norm] at this
  have hzB : ∀ x, ‖z x‖ ≤ r := fun x => le_of_tendsto' ((hz x).norm) fun n => hzsB n x
  have hfix : Tm z = z := by
    funext x
    have hlim : Tendsto (fun n => zs (n + 1) x) atTop (𝓝 (Tm z x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hg : Tendsto (fun n : ℕ => r / 2 ^ n / 2) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (r / 2)
        simp only [mul_zero] at this
        refine this.congr fun n => ?_
        rw [one_div, inv_pow]; field_simp
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hg
      have e : zs (n + 1) = Tm (zs n) := by simp only [hzs, Function.iterate_succ_apply']
      rw [e, norm_sub_rev]
      exact hcontr z (zs n) hzB (hzsB n) (r / 2 ^ n) (fun x => by
        rw [norm_sub_rev]; exact hzdist n x) x
    exact tendsto_nhds_unique hlim ((hz x).comp (tendsto_add_atTop_nat 1))
  -- fixed points of `Tm` in the ball are exactly the solutions
  have hsol : ∀ w : Y → Fin 5 → ℝ, (∀ y, ‖w y‖ ≤ r) →
      (Tm w = w ↔ PhiR T p e d w = 0) := by
    intro w hw
    have hr' : ∀ y k, |PhiR T p e d w y k| ≤ CQ + CN := fun y k => by
      have := (norm_le_pi_norm _ k).trans (hPhiB w hw y); rwa [Real.norm_eq_abs] at this
    have hRL := LR_LinvR T hp hG (PhiR T p e d w) (CQ + CN) (by positivity) hr'
    constructor
    · intro h
      have hl : LinvR T p (PhiR T p e d w) = fun _ => 0 := by
        funext x
        have := congrFun h x
        simp only [hTm] at this
        have := congrArg (fun v => w x - v) this
        simp only [sub_sub_cancel, sub_self] at this
        exact this
      rw [← hRL, hl]
      funext x; exact LR_zero T p x
    · intro h
      have h0 : LinvR T p (PhiR T p e d w) = fun _ => 0 := by
        rw [h]
        have := LinvR_LR T hp hG (v := fun _ => (0 : Fin 5 → ℝ)) le_rfl (fun _ => by simp)
        have e : LR T p (fun _ => (0 : Fin 5 → ℝ)) = 0 := funext fun x => LR_zero T p x
        rw [e] at this
        exact this
      funext x
      simp only [hTm, h0, sub_zero]
  have hsmall : ∀ τ', 0 ≤ τ' → (∀ y, ‖PhiR T p e d (fun _ => 0) y‖ ≤ τ') →
      ∀ y, ‖z y‖ ≤ 2 * K' * τ' := by
    intro τ' hτ' hb
    have hT0' : ∀ x, ‖Tm (fun _ => 0) x‖ ≤ K' * τ' := fun x => by
      have h := hKK _ τ' hτ' hb x
      simp only [hTm, zero_sub, norm_neg]
      exact h
    have hn : ∀ n : ℕ, ∀ y, ‖z y‖ ≤ r / 2 ^ n + 2 * K' * τ' := by
      intro n
      induction n with
      | zero => intro y; have := hzB y; have : 0 ≤ 2 * K' * τ' := by positivity
                simp only [pow_zero, div_one]; linarith
      | succ n ih =>
        intro y
        have h := hcontr z (fun _ => 0) hzB (fun y => by simp [hr0.le]) _
          (fun y => by simpa using ih y) y
        rw [hfix] at h
        calc ‖z y‖ ≤ ‖z y - Tm (fun _ => 0) y‖ + ‖Tm (fun _ => 0) y‖ := by
              have := norm_add_le (z y - Tm (fun _ => 0) y) (Tm (fun _ => 0) y); simpa using this
          _ ≤ (r / 2 ^ n + 2 * K' * τ') / 2 + K' * τ' := add_le_add h (hT0' y)
          _ = r / 2 ^ (n + 1) + 2 * K' * τ' := by rw [pow_succ]; ring
    intro y
    have ht : Tendsto (fun n : ℕ => r / 2 ^ n + 2 * K' * τ') atTop (𝓝 (0 + 2 * K' * τ')) := by
      refine Tendsto.add ?_ tendsto_const_nhds
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      rw [one_div, inv_pow]; field_simp
    have := ge_of_tendsto' ht fun n => hn n y
    simpa using this
  have hinv : ∀ A : (Y → Fin 5 → ℝ) → Prop, A (fun _ => 0) →
      (∀ w, (∀ y, ‖w y‖ ≤ r) → A w → A (fun x => w x - LinvR T p (PhiR T p e d w) x)) →
      (∀ (ws : ℕ → Y → Fin 5 → ℝ) (w : Y → Fin 5 → ℝ), (∀ n, A (ws n)) →
        (∀ n y, ‖ws n y‖ ≤ r) → (∀ x, Tendsto (fun n => ws n x) atTop (𝓝 (w x))) → A w) →
      A z := by
    intro A hA0 hAT hAlim
    have hzsA : ∀ n, A (zs n) := by
      intro n
      induction n with
      | zero => simpa [hzs] using hA0
      | succ n ih =>
        have e : zs (n + 1) = Tm (zs n) := by simp only [hzs, Function.iterate_succ_apply']
        rw [e]; exact hAT _ (hzsB n) ih
    exact hAlim zs z hzsA hzsB hz
  refine ⟨z, ⟨hzB, (hsol z hzB).1 hfix⟩, fun z' hz'B hz' => ?_, hsmall, hinv⟩
  have hfix' := (hsol z' hz'B).2 hz'
  have hD : ∀ n : ℕ, ∀ x, ‖z' x - z x‖ ≤ 2 * r / 2 ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      have := (norm_sub_le (z' x) (z x)).trans (add_le_add (hz'B x) (hzB x))
      simp only [pow_zero, div_one]; linarith
    | succ n ih =>
      intro x
      have h := hcontr z' z hz'B hzB _ ih x
      rw [hfix, hfix'] at h
      exact h.trans (le_of_eq (by rw [pow_succ]; ring))
  funext x
  have ht : Tendsto (fun n : ℕ => 2 * r / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * r)
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow]; field_simp
  have := ge_of_tendsto' ht fun n => hD n x
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-! ## The Ramsey conditions on the AR(1) tree -/

/-- The Ramsey residual on the AR(1) tree, written out. -/
theorem PhiR_ar (ν : ProbabilityMeasure ℝ) {p : Par} (e : Node δ Bx → Fin 3 → ℝ)
    (d w : Node δ Bx → Fin 5 → ℝ) (x : Node δ Bx) :
    PhiR (arTree ν δ Bx) p e d w x =
      Qd p (e x, (if x.2.length = 0 then d x else w (x.1, x.2.dropLast)), w x) +
        fun i => ΛR ν (fun ε => Nd p (w (x.1, x.2 ++ [ε])) i) := by
  funext i
  simp only [PhiR, lagI, arTree, treeM, Mv, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

/-- The AR(1) state along appended innovations. -/
theorem stateN_append (ρ Bx : ℝ) (hB : 0 ≤ Bx) {δ δ' : ℝ} (x0 : Node δ Bx) (q : Root δ' Bx)
    (hq : q.2 = stateN ρ Bx hB x0) (l : List ℝ) :
    stateN ρ Bx hB (q, l) = stateN ρ Bx hB (x0.1, x0.2 ++ l) := by
  simp [stateN, List.foldl_append, hq]

/-- The AR(1) state is measurable in `(root, innovations)`. -/
theorem measurable_stateN (ρ Bx : ℝ) (hB : 0 ≤ Bx) (n : ℕ) :
    Measurable (fun w : Root δ Bx × (Fin n → ℝ) => (stateN ρ Bx hB (w.1, List.ofFn w.2) : ℝ)) := by
  induction n with
  | zero =>
    have e : (fun w : Root δ Bx × (Fin 0 → ℝ) => (stateN ρ Bx hB (w.1, List.ofFn w.2) : ℝ)) =
        fun w => (w.1.2 : ℝ) := by funext w; simp [stateN]
    rw [e]
    exact continuous_subtype_val.measurable.comp (measurable_snd.comp measurable_fst)
  | succ m ih =>
    have e : (fun w : Root δ Bx × (Fin (m + 1) → ℝ) => (stateN ρ Bx hB (w.1, List.ofFn w.2) : ℝ))
        = fun w => (arSucc ρ Bx hB (stateN ρ Bx hB (w.1, List.ofFn (Fin.init w.2)))
          (w.2 (Fin.last m)) : ℝ) := by
      funext w
      have : List.ofFn w.2 = List.ofFn (Fin.init w.2) ++ [w.2 (Fin.last m)] := by
        rw [← ofFn_snoc, Fin.snoc_init_self]
      rw [this, stateN_snoc]
    rw [e]
    have hs : Measurable (fun w : Root δ Bx × (Fin (m + 1) → ℝ) =>
        stateN ρ Bx hB (w.1, List.ofFn (Fin.init w.2))) := by
      refine Measurable.subtype_mk ?_
      exact ih.comp (measurable_fst.prodMk ((measurable_init' m).comp measurable_snd))
    exact continuous_subtype_val.measurable.comp ((continuous_arSucc ρ Bx hB).measurable.comp
      (hs.prodMk ((measurable_pi_apply _).comp measurable_snd)))

/-- Woodford (2003), Ch. 6, §1: the disturbances on the tree, `e = x·c`. -/
noncomputable def eN (ρ Bx : ℝ) (hB : 0 ≤ Bx) {δ : ℝ} (c : Fin 3 → ℝ) (x : Node δ Bx) :
    Fin 3 → ℝ := (stateN ρ Bx hB x : ℝ) • c

/-- Woodford (2003), Ch. 7: the initial lag on the tree is the root's `d`. -/
def dN {δ : ℝ} (x : Node δ Bx) : Fin 5 → ℝ := (x.1.1 : Fin 5 → ℝ)

/-- Woodford (2003), Ch. 7 and App. A.3 (**the shift argument**): a bounded solution `w₂` on one
AR(1) tree agrees at every node `x₀` (whose lag lies in the root ball of another tree) with the
unique solution `W₁` of the other tree at the root `(lag w₂(x₀), x(x₀))`. -/
theorem shift_eq (ν : ProbabilityMeasure ℝ) (ρ : ℝ) (hB : 0 ≤ Bx) {p : Par}
    {δ1 δ2 : ℝ} (c : Fin 3 → ℝ) (r : ℝ) (W1 : Node δ1 Bx → Fin 5 → ℝ)
    (hW1B : ∀ y, ‖W1 y‖ ≤ r)
    (hW1u : ∀ z' : Node δ1 Bx → Fin 5 → ℝ, (∀ y, ‖z' y‖ ≤ r) →
      PhiR (arTree ν δ1 Bx) p (eN ρ Bx hB c) dN z' = 0 → z' = W1)
    (w2 : Node δ2 Bx → Fin 5 → ℝ) (hw2B : ∀ y, ‖w2 y‖ ≤ r)
    (hw2E : PhiR (arTree ν δ2 Bx) p (eN ρ Bx hB c) dN w2 = 0) (hW1E :
      PhiR (arTree ν δ1 Bx) p (eN ρ Bx hB c) dN W1 = 0)
    (x0 : Node δ2 Bx) (h : ‖lagI (arTree ν δ2 Bx) w2 dN x0‖ ≤ δ1) :
    w2 x0 = W1 ((⟨lagI (arTree ν δ2 Bx) w2 dN x0, h⟩, stateN ρ Bx hB x0), []) := by
  classical
  set qs : Root δ1 Bx := (⟨lagI (arTree ν δ2 Bx) w2 dN x0, h⟩, stateN ρ Bx hB x0) with hqs
  set w' : Node δ1 Bx → Fin 5 → ℝ := fun y =>
    if y.1 = qs then w2 (x0.1, x0.2 ++ y.2) else W1 y with hw'
  have hw'B : ∀ y, ‖w' y‖ ≤ r := fun y => by
    simp only [hw']; split_ifs
    · exact hw2B _
    · exact hW1B _
  have hw'E : PhiR (arTree ν δ1 Bx) p (eN ρ Bx hB c) dN w' = 0 := by
    funext y
    rw [PhiR_ar]
    by_cases hy : y.1 = qs
    · have hz' := congrFun hw2E (x0.1, x0.2 ++ y.2)
      rw [PhiR_ar] at hz'
      simp only [Pi.zero_apply] at hz'
      rw [Pi.zero_apply, ← hz']
      have hst : stateN ρ Bx hB y = stateN ρ Bx hB (x0.1, x0.2 ++ y.2) :=
        stateN_append ρ Bx hB x0 y.1 (by rw [hy]) y.2
      have hcur : w' y = w2 (x0.1, x0.2 ++ y.2) := by simp [hw', hy]
      have hch : ∀ ε, w' (y.1, y.2 ++ [ε]) = w2 (x0.1, x0.2 ++ y.2 ++ [ε]) := fun ε => by
        simp [hw', hy, List.append_assoc]
      have hlag : (if y.2.length = 0 then dN y else w' (y.1, y.2.dropLast)) =
          (if (x0.2 ++ y.2).length = 0 then dN (x0.1, x0.2 ++ y.2) else
            w2 (x0.1, (x0.2 ++ y.2).dropLast)) := by
        by_cases hl : y.2 = []
        · have hd : dN y = lagI (arTree ν δ2 Bx) w2 dN x0 := by simp [dN, hy, hqs]
          simp only [hl, List.length_nil, ↓reduceIte, List.append_nil, hd]
          simp only [lagI, arTree, dN]
          by_cases h0 : x0.2.length = 0 <;> simp [h0]
        · have h1 : (x0.2 ++ y.2).length ≠ 0 := by simp [hl]
          have h2 : y.2.length ≠ 0 := by simpa using hl
          simp only [h1, h2, ↓reduceIte]
          simp [hw', hy, List.dropLast_append_of_ne_nil hl]
      simp only [eN, hst, hcur, hch, hlag]
    · have hW' := congrFun hW1E y
      rw [PhiR_ar] at hW'
      simp only [Pi.zero_apply] at hW'
      rw [Pi.zero_apply, ← hW']
      have hcur : w' y = W1 y := by simp [hw', hy]
      have hch : ∀ ε, w' (y.1, y.2 ++ [ε]) = W1 (y.1, y.2 ++ [ε]) := fun ε => by
        simp [hw', hy]
      have hpar : w' (y.1, y.2.dropLast) = W1 (y.1, y.2.dropLast) := by simp [hw', hy]
      simp only [hcur, hch, hpar]
  have := congrFun (hW1u w' hw'B hw'E) (qs, [])
  simp only [hw', ↓reduceIte, List.append_nil] at this
  exact this

/-- The lag with the root's initial value preserves `MeasV`. -/
theorem measV_lagI (ν : ProbabilityMeasure ℝ) {w : Node δ Bx → Fin 5 → ℝ} (hw : MeasV w) :
    MeasV (lagI (arTree ν δ Bx) w dN) := by
  intro n
  cases n with
  | zero =>
    have e : (fun v : Root δ Bx × (Fin 0 → ℝ) => lagI (arTree ν δ Bx) w dN (v.1, List.ofFn v.2))
        = fun v => (v.1.1 : Fin 5 → ℝ) := by
      funext v; simp [lagI, arTree, dN]
    rw [e]; exact continuous_subtype_val.measurable.comp (measurable_fst.comp measurable_fst)
  | succ m =>
    have e : (fun v : Root δ Bx × (Fin (m + 1) → ℝ) =>
        lagI (arTree ν δ Bx) w dN (v.1, List.ofFn v.2)) =
          fun v => w (v.1, List.ofFn (Fin.init v.2)) := by
      funext v; simp [lagI, arTree, ofFn_init]
    rw [e]
    exact (hw m).comp (measurable_fst.prodMk ((measurable_init' m).comp measurable_snd))

/-- The disturbances on the tree are `MeasV`. -/
theorem measV_eN (ρ : ℝ) (hB : 0 ≤ Bx) (c : Fin 3 → ℝ) : MeasV (δ := δ) (eN ρ Bx hB c) :=
  fun n => (measurable_stateN ρ Bx hB n).smul_const c

/-- Woodford (2003), Ch. 7 and App. A.3 (**the measurable Ramsey solution on the AR(1) tree**):
uniform radii such that on every AR(1) tree with roots `‖d‖ ≤ δ_r ≤ δ` and `B̄‖c‖ ≤ δ` the
unique Ramsey solution within `r` exists, satisfies the smallness bound, and is measurable in
`(root, innovations)` at every date. -/
theorem tree_sol {p : Par} (hp : p.Basic) (hG : 0 < Gw p) :
    ∃ r > 0, ∃ δ > 0, ∃ C > 0, ∀ (ν : ProbabilityMeasure ℝ) (ρ Bx : ℝ) (hB : 0 ≤ Bx)
      (δr : ℝ) (c : Fin 3 → ℝ), δr ≤ δ → Bx * ‖c‖ ≤ δ →
        ∃ W : Node δr Bx → Fin 5 → ℝ,
          ((∀ y, ‖W y‖ ≤ r) ∧ PhiR (arTree ν δr Bx) p (eN ρ Bx hB c) dN W = 0) ∧
          (∀ z' : Node δr Bx → Fin 5 → ℝ, (∀ y, ‖z' y‖ ≤ r) →
            PhiR (arTree ν δr Bx) p (eN ρ Bx hB c) dN z' = 0 → z' = W) ∧
          (∀ τ', 0 ≤ τ' → (∀ y, ‖PhiR (arTree ν δr Bx) p (eN ρ Bx hB c) dN
            (fun _ => 0) y‖ ≤ τ') → ∀ y, ‖W y‖ ≤ C * τ') ∧ MeasV W := by
  obtain ⟨r, hr, δ, hδ, C, hC, hex⟩ := ramsey_existence_inv hp hG
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall (0 : (Fin 3 → ℝ) × (Fin 5 → ℝ) × (Fin 5 → ℝ))
    (r + δ)).exists_bound_of_continuousOn ((contDiff_Qd (n := 0) p).continuous.continuousOn)
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin 5 → ℝ) r).exists_bound_of_continuousOn
    ((contDiff_Nd (n := 0) p).continuous.continuousOn)
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hCQ 0 (Metric.mem_closedBall_self (by positivity)))
  have hCN0 : 0 ≤ CN := (norm_nonneg _).trans (hCN 0 (Metric.mem_closedBall_self hr.le))
  refine ⟨r, hr, δ, hδ, C, hC, fun ν ρ Bx hB δr c hδr hc => ?_⟩
  set T := arTree ν δr Bx
  have he : ∀ y : Node δr Bx, ‖eN ρ Bx hB c y‖ ≤ δ := fun y => by
    simp only [eN, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (stateN ρ Bx hB y).2 (norm_nonneg c)).trans hc
  have hd : ∀ y : Node δr Bx, ‖dN y‖ ≤ δ := fun y => y.1.1.2.trans hδr
  obtain ⟨W, hWE, hWu, hWs, hWinv⟩ := hex T _ _ he hd
  refine ⟨W, hWE, hWu, hWs, hWinv MeasV (fun n => measurable_const) (fun w hw hwm => ?_)
    (fun ws w hws _ hlim n => measurable_of_tendsto_metrizable (fun m => hws m n)
      (tendsto_pi_nhds.2 fun v => hlim _))⟩
  -- the Newton step preserves measurability
  have hlagB : ∀ y, ‖lagI T w dN y‖ ≤ r + δ := fun y => by
    unfold lagI; split_ifs
    · exact (hd y).trans (by linarith)
    · exact (hw _).trans (by linarith)
  have hNB : ∀ y, ‖Nd p (w y)‖ ≤ CN := fun y =>
    hCN _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hw y)
  have hPB : ∀ y, ‖PhiR T p (eN ρ Bx hB c) dN w y‖ ≤ CQ + CN := fun y => by
    refine (norm_add_le _ _).trans (add_le_add (hCQ _ ?_) (Mv_norm_le T.markov hCN0 hNB y))
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
    exact max_le ((he y).trans (by linarith)) (max_le (hlagB y) ((hw y).trans (by linarith)))
  have hPm : MeasV (PhiR T p (eN ρ Bx hB c) dN w) := by
    intro n
    have h1 : Measurable (fun v : Root δr Bx × (Fin n → ℝ) =>
        Qd p (eN ρ Bx hB c (v.1, List.ofFn v.2), lagI T w dN (v.1, List.ofFn v.2),
          w (v.1, List.ofFn v.2))) :=
      (contDiff_Qd (n := 0) p).continuous.measurable.comp ((measV_eN ρ hB c n).prodMk
        ((measV_lagI ν hwm n).prodMk (hwm n)))
    have h2 := measV_Mv ν (h := fun y => Nd p (w y))
      (fun n => (contDiff_Nd (n := 0) p).continuous.measurable.comp (hwm n)) hNB n
    exact h1.add h2
  have hL := measV_LinvR ν hp hG hPm (A := CQ + CN) (by positivity) fun y k => by
    have := (norm_le_pi_norm _ k).trans (hPB y); rwa [Real.norm_eq_abs] at this
  exact fun n => (hwm n).sub (hL n)

/-- Woodford (2003), Ch. 7 (**the policy depends on the lag only through `λ̂_{t−1}`**): on the
AR(1) tree, the unique solution at two roots with the same state and initial lags agreeing in
component 3 (the multiplier) coincides. -/
theorem tree_root_congr (ν : ProbabilityMeasure ℝ) (ρ : ℝ) (hB : 0 ≤ Bx) {p : Par}
    {δ1 : ℝ} (c : Fin 3 → ℝ) (r : ℝ) (W1 : Node δ1 Bx → Fin 5 → ℝ)
    (hW1B : ∀ y, ‖W1 y‖ ≤ r)
    (hW1u : ∀ z' : Node δ1 Bx → Fin 5 → ℝ, (∀ y, ‖z' y‖ ≤ r) →
      PhiR (arTree ν δ1 Bx) p (eN ρ Bx hB c) dN z' = 0 → z' = W1)
    (hW1E : PhiR (arTree ν δ1 Bx) p (eN ρ Bx hB c) dN W1 = 0) (q q' : Root δ1 Bx)
    (hs : q.2 = q'.2) (h3 : q.1.1 3 = q'.1.1 3) : W1 (q', []) = W1 (q, []) := by
  classical
  set w' : Node δ1 Bx → Fin 5 → ℝ := fun y => if y.1 = q' then W1 (q, y.2) else W1 y with hw'
  have hw'B : ∀ y, ‖w' y‖ ≤ r := fun y => by
    simp only [hw']; split_ifs
    · exact hW1B _
    · exact hW1B _
  have hw'E : PhiR (arTree ν δ1 Bx) p (eN ρ Bx hB c) dN w' = 0 := by
    funext y
    rw [PhiR_ar, Pi.zero_apply]
    by_cases hy : y.1 = q'
    · have hz' := congrFun hW1E (q, y.2)
      rw [PhiR_ar] at hz'
      simp only [Pi.zero_apply] at hz'
      rw [← hz']
      have hst : stateN ρ Bx hB y = stateN ρ Bx hB (q, y.2) := by
        simp [stateN, hy, hs]
      have hcur : w' y = W1 (q, y.2) := by simp [hw', hy]
      have hch : ∀ ε, w' (y.1, y.2 ++ [ε]) = W1 (q, y.2 ++ [ε]) := fun ε => by simp [hw', hy]
      have hpar : w' (y.1, y.2.dropLast) = W1 (q, y.2.dropLast) := by simp [hw', hy]
      simp only [eN, hst, hcur, hch, hpar]
      by_cases hl : y.2.length = 0
      · simp only [hl, ↓reduceIte]
        have hdy : dN y = (q'.1.1 : Fin 5 → ℝ) := by simp [dN, hy]
        rw [hdy, Qd_congr _ _ h3.symm]
        rfl
      · simp only [hl, ↓reduceIte]
    · have hW' := congrFun hW1E y
      rw [PhiR_ar] at hW'
      simp only [Pi.zero_apply] at hW'
      rw [← hW']
      have hcur : w' y = W1 y := by simp [hw', hy]
      have hch : ∀ ε, w' (y.1, y.2 ++ [ε]) = W1 (y.1, y.2 ++ [ε]) := fun ε => by simp [hw', hy]
      have hpar : w' (y.1, y.2.dropLast) = W1 (y.1, y.2.dropLast) := by simp [hw', hy]
      simp only [hcur, hch, hpar]
  have := congrFun (hW1u w' hw'B hw'E) (q', [])
  simp only [hw', ↓reduceIte] at this
  exact this.symm

/-! ## The Markov representation on the i.i.d. probability space -/

open ExpectationsMeasure ExpectationsMeasureIID NonlinearNKMarkovAE NonlinearNKMarkovAEAdapted
open NonlinearRotembergRamseyAEIFT

/-- Woodford (2003), Ch. 7, §1–2, Ch. 6, §1 and App. A.3 (**THE MARKOV REPRESENTATION OF THE
A.S. ROTEMBERG RAMSEY EQUILIBRIUM WITH AN AR(1) OF ANY BOUNDED LAW**): if `G > 0`, there are
`r, δ > 0` such that for every innovation law `ν` with `|ε| ≤ B` a.s., every `|ρ| < 1`, every
`c` with `B‖c‖/(1−|ρ|) ≤ δ` and every predetermined initial value `‖d₀‖ ≤ δ`, on the i.i.d.
product space with `x_t = ρx_{t−1} + ε_t` and `e_t = x_t c` there is ONE measurable
`G : ℝ⁵ × ℝ → ℝ⁵`, independent of the date and depending on the lag only through
`λ̂_{t−1}`, and an adapted solution `z` of the exact Ramsey
conditions with `‖z_t‖ ≤ r` a.s. such that `z_t = G(z_{t−1}, x_t)` a.s. (`z_{−1} = d₀`), and every
adapted solution within `r` is a.s. equal to `z`. -/
theorem ramsey_ar1_markov {p : Par} (hp : p.Basic) (hG : 0 < Gw p) :
    ∃ r > 0, ∃ δ > 0, ∀ (ν : ProbabilityMeasure ℝ) (B ρ : ℝ), |ρ| < 1 →
      (∀ᵐ x ∂(ν : Measure ℝ), |x| ≤ B) → ∀ c : Fin 3 → ℝ, B / (1 - |ρ|) * ‖c‖ ≤ δ →
        ∀ d0 : Fin 5 → ℝ, ‖d0‖ ≤ δ →
          ∃ G : (Fin 5 → ℝ) → ℝ → Fin 5 → ℝ, Measurable (fun q : (Fin 5 → ℝ) × ℝ => G q.1 q.2) ∧
          (∀ d d' : Fin 5 → ℝ, ‖d‖ ≤ δ → ‖d'‖ ≤ δ → d 3 = d' 3 → ∀ x, G d x = G d' x) ∧
          ∃ z : ℕ → (ℕ → ℝ) → Fin 5 → ℝ,
            (AdA (iidSystem ν) z ∧ Bd (iidSystem ν) z r ∧ ∀ t,
              PhiRA (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) (fun _ => d0) z t
                =ᵐ[(iidSystem ν).μ] 0) ∧
            (∀ t, ∀ᵐ ω ∂(iidSystem ν).μ,
              z t ω = G (lagIA z (fun _ => d0) t ω) (ar1 ρ t ω)) ∧
            ∀ z' : ℕ → (ℕ → ℝ) → Fin 5 → ℝ, AdA (iidSystem ν) z' → Bd (iidSystem ν) z' r →
              (∀ t, PhiRA (iidSystem ν) p (fun t ω => ar1 ρ t ω • c) (fun _ => d0) z' t
                =ᵐ[(iidSystem ν).μ] 0) → ∀ t, z' t =ᵐ[(iidSystem ν).μ] z t := by
  classical
  obtain ⟨rt, hrt, δt, hδt, Ct, hCt, htree⟩ := tree_sol hp hG
  obtain ⟨ra, hra, δa, hδa, hae⟩ := ramsey_existence_ae hp hG
  set s0 := min δt ra with hs0
  have hs00 : 0 < s0 := lt_min hδt hra
  set τ' := s0 / Ct with hτ'
  have hτ'0 : 0 < τ' := by positivity
  obtain ⟨ρc, hρc, hQc⟩ := Metric.continuousAt_iff.1
    ((contDiff_Qd (n := 0) p).continuous.continuousAt (x := 0)) τ' hτ'0
  obtain ⟨CN, hCN⟩ := (isCompact_closedBall (0 : Fin 5 → ℝ) rt).exists_bound_of_continuousOn
    ((contDiff_Nd (n := 0) p).continuous.continuousOn)
  set δ := min (min δt (ρc / 2)) δa with hδ
  have hδ0 : 0 < δ := lt_min (lt_min hδt (by positivity)) hδa
  have hδt' : δ ≤ δt := (min_le_left _ _).trans (min_le_left _ _)
  have hδc : δ ≤ ρc / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδa' : δ ≤ δa := min_le_right _ _
  refine ⟨ra, hra, δ, hδ0, fun ν B ρ hρ hB c hc d0 hd0 => ?_⟩
  obtain ⟨x₀, hx₀⟩ := hB.exists
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hx₀
  have h1ρ : 0 < 1 - |ρ| := by linarith
  set Bx := B / (1 - |ρ|) with hBx
  have hBx0 : 0 ≤ Bx := div_nonneg hB0 h1ρ.le
  -- the two trees
  obtain ⟨W1, ⟨hW1B, hW1E⟩, hW1u, -, hW1m⟩ := htree ν ρ Bx hBx0 δt c le_rfl (hc.trans hδt')
  obtain ⟨W2, ⟨hW2B, hW2E⟩, -, hW2s, hW2m⟩ := htree ν ρ Bx hBx0 δ c hδt' (hc.trans hδt')
  have hW2small : ∀ y, ‖W2 y‖ ≤ s0 := by
    have hb : ∀ y, ‖PhiR (arTree ν δ Bx) p (eN ρ Bx hBx0 c) dN (fun _ => 0) y‖ ≤ τ' := by
      intro y
      have hss := Qd_Nd_zero hp
      have e1 : PhiR (arTree ν δ Bx) p (eN ρ Bx hBx0 c) dN (fun _ => 0) y =
          Qd p (eN ρ Bx hBx0 c y, lagI (arTree ν δ Bx) (fun _ => 0) dN y, 0) - Qd p 0 := by
        simp only [PhiR, Mv_const']
        rw [eq_neg_of_add_eq_zero_right hss]
        abel
      rw [e1, ← dist_eq_norm]
      refine (hQc ?_).le
      rw [dist_zero_right, Prod.norm_def, Prod.norm_def]
      have he : ‖eN ρ Bx hBx0 c y‖ ≤ ρc / 2 := by
        simp only [eN, norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (stateN ρ Bx hBx0 y).2 (norm_nonneg c)).trans
          (hc.trans hδc)
      have hl : ‖lagI (arTree ν δ Bx) (fun _ => (0 : Fin 5 → ℝ)) dN y‖ ≤ ρc / 2 := by
        unfold lagI; split_ifs
        · exact y.1.1.2.trans hδc
        · rw [norm_zero]; positivity
      have h0 : ‖(0 : Fin 5 → ℝ)‖ ≤ ρc / 2 := by rw [norm_zero]; positivity
      exact lt_of_le_of_lt (max_le he (max_le hl h0)) (by linarith)
    intro y
    exact (hW2s τ' hτ'0.le hb y).trans (le_of_eq (by rw [hτ']; field_simp))
  -- the policy function
  obtain ⟨cb, hcb⟩ : ∃ cb : (Fin 5 → ℝ) → Fin 5 → ℝ,
      cb = fun d => if ‖d‖ ≤ δt then d else 0 := ⟨_, rfl⟩
  have hcbB : ∀ d, ‖cb d‖ ≤ δt := fun d => by
    rw [hcb]; dsimp only; split_ifs with h
    · exact h
    · rw [norm_zero]; exact hδt.le
  have hcbm : Measurable cb := by
    rw [hcb]
    exact Measurable.ite (measurableSet_le continuous_norm.measurable measurable_const)
      measurable_id measurable_const
  obtain ⟨rt1, hrt1⟩ : ∃ rt1 : (Fin 5 → ℝ) × ℝ → Root δt Bx,
      rt1 = fun q => (⟨cb q.1, hcbB q.1⟩, clampX Bx hBx0 q.2) := ⟨_, rfl⟩
  have hrt1m : Measurable rt1 := by
    rw [hrt1]
    exact ((hcbm.comp measurable_fst).subtype_mk).prodMk
      ((continuous_clampX Bx hBx0).measurable.comp measurable_snd)
  obtain ⟨G, hGdef⟩ : ∃ G : (Fin 5 → ℝ) → ℝ → Fin 5 → ℝ,
      G = fun d x => W1 (rt1 (d, x), []) := ⟨_, rfl⟩
  have hGm : Measurable (fun q : (Fin 5 → ℝ) × ℝ => G q.1 q.2) := by
    have h0 := (hW1m 0).comp (hrt1m.prodMk (measurable_const (a := (Fin.elim0 : Fin 0 → ℝ))))
    have e : (fun q : (Fin 5 → ℝ) × ℝ => G q.1 q.2) = fun q =>
        W1 ((rt1 q, (Fin.elim0 : Fin 0 → ℝ)).1, List.ofFn (rt1 q, (Fin.elim0 : Fin 0 → ℝ)).2) := by
      funext q; rw [hGdef]; rfl
    rw [e]; exact h0
  -- the process along the tree of `W₂`
  set E := iidSystem ν with hE
  set root2 : (ℕ → ℝ) → Root δ Bx := fun ω => (⟨d0, hd0⟩, clampX Bx hBx0 (ω 0)) with hroot2
  set node : ℕ → (ℕ → ℝ) → Node δ Bx := fun t ω => (root2 ω, List.ofFn (innov t ω)) with hnode
  set z : ℕ → (ℕ → ℝ) → Fin 5 → ℝ := fun t ω => W2 (node t ω) with hz
  have hroot2m : ∀ t, Measurable[E.𝓕 t] root2 := fun t => by
    let _ := E.𝓕 t
    exact measurable_const.prodMk ((continuous_clampX Bx hBx0).measurable.comp
      (measurable_shock ν (Nat.zero_le t)))
  have hWv : ∀ t, Measurable[E.𝓕 t] (fun ω => (root2 ω, innov t ω)) := fun t => by
    let _ := E.𝓕 t
    exact (hroot2m t).prodMk (measurable_innov ν t)
  have hzm : ∀ t, Measurable[E.𝓕 t] (z t) := fun t => (hW2m t).comp (hWv t)
  have hzA : AdA E z := fun t => by
    let _ := E.𝓕 t
    exact (hzm t).aestronglyMeasurable
  have hzB : Bd E z ra := fun t => Eventually.of_forall fun ω =>
    (hW2small _).trans (min_le_right _ _)
  -- the state along the path
  have har : ∀ t, ∀ᵐ ω ∂E.μ, |ar1 ρ t ω| ≤ Bx := fun t => ar1_bdd (ν := ν) hρ hB t
  have hstate : ∀ t, ∀ᵐ ω ∂E.μ, (stateN ρ Bx hBx0 (node t ω) : ℝ) = ar1 ρ t ω := fun t => by
    filter_upwards [ae_all_iff.2 har] with ω h
    induction t with
    | zero =>
      have h0 : |ω 0| ≤ Bx := h 0
      simp only [hnode, hroot2, stateN, List.ofFn_zero, List.foldl_nil]
      exact clampX_of hBx0 h0
    | succ t ih =>
      have e : node (t + 1) ω = ((node t ω).1, (node t ω).2 ++ [ω (t + 1)]) := by
        simp only [hnode, ofFn_innov_succ]
      rw [e, stateN_snoc]
      simp only [arSucc, ih]
      have h1 : |ρ * ar1 ρ t ω + ω (t + 1)| ≤ Bx := h (t + 1)
      rw [clampX_of hBx0 h1]
      rfl
  -- the lag of the process is the tree lag
  have hlag : ∀ t ω, lagI (arTree ν δ Bx) W2 dN (node t ω) = lagIA z (fun _ => d0) t ω := by
    intro t ω
    cases t with
    | zero => simp [lagI, arTree, hnode, dN, lagIA, hroot2]
    | succ t =>
      have e : node (t + 1) ω = ((node t ω).1, (node t ω).2 ++ [ω (t + 1)]) := by
        simp only [hnode, ofFn_innov_succ]
      rw [e]
      simp [lagI, arTree, lagIA, hz]
  -- the forecasts are the tree expectations
  have hNB : ∀ y, ‖Nd p (W2 y)‖ ≤ CN := fun y =>
    hCN _ (by rw [Metric.mem_closedBall, dist_zero_right]; exact hW2B y)
  have hfc : ∀ t (i : Fin 5), E.E t (fun ω' => Nd p (z (t + 1) ω') i) =ᵐ[E.μ]
      fun ω => ΛR ν (fun ε => Nd p (W2 ((node t ω).1, (node t ω).2 ++ [ε])) i) := by
    intro t i
    set F : (Root δ Bx × (Fin t → ℝ)) × ℝ → ℝ := fun q =>
      Nd p (W2 (q.1.1, List.ofFn (Fin.snoc q.1.2 q.2 : Fin (t + 1) → ℝ))) i with hF
    have hFm : Measurable F := (measurable_pi_apply i).comp
      ((contDiff_Nd (n := 0) p).continuous.measurable.comp ((hW2m (t + 1)).comp
        ((measurable_fst.comp measurable_fst).prodMk ((measurable_snoc' t).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))))
    have hFb : ∀ q, |F q| ≤ CN := fun q => by
      have := (norm_le_pi_norm _ i).trans (hNB (q.1.1, List.ofFn (Fin.snoc q.1.2 q.2 :
        Fin (t + 1) → ℝ)))
      rwa [Real.norm_eq_abs] at this
    have hY : Measurable fun ω : ℕ → ℝ => ω (t + 1) := measurable_pi_apply (t + 1)
    have hind : Indep (MeasurableSpace.comap (fun ω : ℕ → ℝ => ω (t + 1)) inferInstance)
        (E.𝓕 t) E.μ :=
      indep_of_indep_of_le_left (indep_future ν t)
        (measurable_future_fun t measurable_id).comap_le
    have hfr := freeze (μ := E.μ) (E.𝓕.le t) (hWv t) hY hind hFm hFb
    have hlaw : E.μ.map (fun ω : ℕ → ℝ => ω (t + 1)) = (ν : Measure ℝ) :=
      Measure.infinitePi_map_eval _ (t + 1)
    have e1 : (fun ω' => Nd p (z (t + 1) ω') i) =
        fun ω' => F ((root2 ω', innov t ω'), ω' (t + 1)) := by
      funext ω'
      simp only [hF, hz, hnode, ofFn_snoc, ofFn_innov_succ]
    rw [e1]
    filter_upwards [hfr] with ω h
    refine h.trans ?_
    rw [hlaw]
    have hm : Measurable (fun ε => Nd p (W2 ((node t ω).1, (node t ω).2 ++ [ε])) i) :=
      (measurable_pi_apply i).comp ((contDiff_Nd (n := 0) p).continuous.measurable.comp
        (hW2m.slice (node t ω)))
    rw [(ΛR_spec ν).1 _ hm ⟨CN, fun ε => by
      have := (norm_le_pi_norm _ i).trans (hNB ((node t ω).1, (node t ω).2 ++ [ε]))
      rwa [Real.norm_eq_abs] at this⟩]
    simp only [hF, ofFn_snoc, hnode]
  -- the process solves the Ramsey conditions a.s.
  have hzE : ∀ t, PhiRA E p (fun t ω => ar1 ρ t ω • c) (fun _ => d0) z t =ᵐ[E.μ] 0 := by
    intro t
    filter_upwards [hstate t, ae_all_iff.2 (hfc t)] with ω hs hf
    have hT := congrFun hW2E (node t ω)
    rw [PhiR_ar] at hT
    simp only [Pi.zero_apply] at hT ⊢
    have hl := hlag t ω
    simp only [lagI, arTree] at hl
    have hm : MvA E (fun s ω' => Nd p (z s ω')) t ω =
        fun i => ΛR ν (fun ε => Nd p (W2 ((node t ω).1, (node t ω).2 ++ [ε])) i) :=
      funext fun i => hf i
    have he : ar1 ρ t ω • c = eN ρ Bx hBx0 c (node t ω) := by simp only [eN, hs]
    simp only [PhiRA, hm, he]
    rw [← hl]
    exact hT
  -- the Markov representation
  have hzG : ∀ t, ∀ᵐ ω ∂E.μ, z t ω = G (lagIA z (fun _ => d0) t ω) (ar1 ρ t ω) := by
    intro t
    filter_upwards [hstate t] with ω hs
    have hlB : ‖lagI (arTree ν δ Bx) W2 dN (node t ω)‖ ≤ δt := by
      unfold lagI; split_ifs
      · exact (node t ω).1.1.2.trans hδt'
      · exact (hW2small _).trans (min_le_left _ _)
    have hsh := shift_eq ν ρ hBx0 c rt W1 hW1B hW1u W2 hW2B hW2E hW1E (node t ω) hlB
    have hroot : ((⟨lagI (arTree ν δ Bx) W2 dN (node t ω), hlB⟩,
        stateN ρ Bx hBx0 (node t ω)) : Root δt Bx) =
          rt1 (lagIA z (fun _ => d0) t ω, ar1 ρ t ω) := by
      rw [hrt1]
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change lagI (arTree ν δ Bx) W2 dN (node t ω) = cb (lagIA z (fun _ => d0) t ω)
        rw [← hlag t ω, hcb]
        simp only [hlB, ↓reduceIte]
      · change (stateN ρ Bx hBx0 (node t ω) : ℝ) = (clampX Bx hBx0 (ar1 ρ t ω) : ℝ)
        rw [← hs, clampX_of hBx0 (stateN ρ Bx hBx0 (node t ω)).2]
    rw [hz]
    simp only
    rw [hsh, hGdef]
    simp only
    rw [hroot]
  -- uniqueness among adapted solutions
  have heA : AdA E (fun t ω => ar1 ρ t ω • c) := fun t => by
    let _ := E.𝓕 t
    exact ((ar1_adapted ν ρ t).measurable.smul_const c).aestronglyMeasurable
  have heB : Bd E (fun t ω => ar1 ρ t ω • c) δa := fun t => by
    filter_upwards [har t] with ω hω
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hω (norm_nonneg c)).trans (hc.trans hδa')
  obtain ⟨zA, -, huA⟩ := hae (ℕ → ℝ) E (fun t ω => ar1 ρ t ω • c) (fun _ => d0) heA heB
    aestronglyMeasurable_const (Eventually.of_forall fun _ => hd0.trans hδa')
  have hGc : ∀ d d' : Fin 5 → ℝ, ‖d‖ ≤ δ → ‖d'‖ ≤ δ → d 3 = d' 3 → ∀ x, G d x = G d' x := by
    intro d d' hd hd' h3 x
    have hcd : cb d = d := by rw [hcb]; simp only [hd.trans hδt', ↓reduceIte]
    have hcd' : cb d' = d' := by rw [hcb]; simp only [hd'.trans hδt', ↓reduceIte]
    rw [hGdef]
    simp only
    refine (tree_root_congr ν ρ hBx0 c rt W1 hW1B hW1u hW1E (rt1 (d', x)) (rt1 (d, x))
      (by rw [hrt1]) ?_)
    rw [hrt1]; simp only [hcd, hcd', h3]
  refine ⟨G, hGm, hGc, z, ⟨hzA, hzB, hzE⟩, hzG, fun z' hz'A hz'B hz' t => ?_⟩
  filter_upwards [huA z' hz'A hz'B hz' t, huA z hzA hzB hzE t] with ω h1 h2
  rw [h1, h2]

end Woodford.StabilizationWelfare.NonlinearRotembergRamseyAR1
