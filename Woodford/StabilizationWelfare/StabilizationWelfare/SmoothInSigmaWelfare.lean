/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StabilizationWelfare.SmoothInSigma
import StabilizationWelfare.BridgeCore
import StabilizationWelfare.BridgeExtensions

/-!
# Layer B along the equilibrium policy: smoothness in the amplitude `ε`, discharged

Woodford (2003), *Interest and Prices*, Chapter 6, §1–§2 (pp. 383–405), Proposition 6.1
(p. 394) and Appendix E.1–E.3 (pp. 692–698).

`BridgeCore` proves Proposition 6.1 in Layer B for ANY family of cross-sections with
`ŷ(ε) − ε y₁ = O(ε²)` (uniformly in the date for discounted welfare), and `BridgeExtensions`
assumes first-order variables `O(ε)` and remainders `O(ε²)` uniformly in the date and state
(`UProc`). Here these hypotheses are PROVED for the equilibrium of any model in the class of
`SmoothInSigma` along the family of amplitude `ε` (initial state `ε x₀₁`, every innovation
scaled by `ε`, `famP`), and the `O(ε³)` welfare remainder follows.

## Main results

* `taylor_one_isBigO`: a `C²` curve into a normed space is `φ(0) + ε φ′(0) + O(ε²)`.
* `family_nodes`, `family_readout`: `ψ(ε)_n = ȳ + ε y₁_n + O(ε²)` with ONE constant for every
  node; `bridge_hypothesis`: the exact hypothesis of `BridgeCore.Econ.prop61_bridge` at each
  node; `uproc_first_order`, `uproc_second_order`: the `UProc` hypotheses of
  `BridgeExtensions` (the book's "bounded fluctuations", here a theorem).
* Proposition 6.1 along the equilibrium: `prop61_node` (each date and state), `prop61_nodes`
  (uniformly over the tree), `prop61_expected_date` (expected utility at date `t` over the
  `|J|ᵗ` histories), `prop61_discounted` (expected discounted utility, genuine `tsum`s),
  `prop61_discounted_ranking` (policies ranked by the discounted expected first-order loss),
  and from primitives `prop61_of_primitives` (`f` of class `C²`) and
  `prop61_of_primitives_local` (`f` of class `C²` near the steady state).

The cross-section of log outputs is read off the decision vector by a linear map `R` and the
disturbances off the state by a linear map `S`; the economy is `BridgeCore.Econ` (the
primitives `ũ`, `ṽ` of §2.1 with a finite weighted set of goods).
-/

namespace Woodford.StabilizationWelfare.SmoothInSigmaWelfare

open Filter Topology Asymptotics
open SmoothInSigma (Bd Model mkBd constBd constBd_apply norm_apply_le pbar)

/-! ## First-order Taylor bound for a `C²` curve in a Banach space -/

/-- Woodford (2003), (2.10), p. 394 (**a `C²` family has a first-order expansion with an
`O(ε²)` remainder**): for a curve `φ : ℝ → V` into any normed space that is `C²` at `0`,
`φ(ε) − φ(0) − ε φ′(0) = O(ε²)`. -/
theorem taylor_one_isBigO {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : ℝ → V}
    (hφ : ContDiffAt ℝ 2 φ 0) :
    (fun ε => φ ε - φ 0 - ε • deriv φ 0) =O[𝓝 0] fun ε => ε ^ 2 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ φ) 0 := hφ.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hL⟩ := h1.exists_lipschitzOnWith
  have hd : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ φ s :=
    (hφ.eventually (by simp)).mono fun s hs => hs.differentiableAt (by norm_num)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht hd)
  have h0t : (0 : ℝ) ∈ t := mem_of_mem_nhds ht
  refine IsBigO.of_bound K ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with ε hε
  have hεδ : |ε| < δ := by simpa [Real.dist_eq] using hε
  have hsub : Metric.closedBall (0 : ℝ) |ε| ⊆ Metric.ball 0 δ :=
    Metric.closedBall_subset_ball hεδ
  have hεmem : ε ∈ Metric.closedBall (0 : ℝ) |ε| := by simp
  have key := (convex_closedBall (0 : ℝ) |ε|).norm_image_sub_le_of_norm_fderiv_le' (f := φ)
    (φ := fderiv ℝ φ 0) (C := K * |ε|) (fun z hz => (hball (hsub hz)).2)
    (fun z hz => by
      have hzt : z ∈ t := (hball (hsub hz)).1
      have := hL.dist_le_mul z hzt 0 h0t
      rw [dist_eq_norm] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
      simpa [Real.dist_eq] using hz)
    (Metric.mem_closedBall_self (abs_nonneg ε)) hεmem
  rw [sub_zero] at key
  have hlin : fderiv ℝ φ 0 ε = ε • deriv φ 0 := by
    rw [← fderiv_apply_one_eq_deriv, ← map_smul, smul_eq_mul, mul_one]
  rw [hlin] at key
  refine key.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq]
  ring


/-! ## The equilibrium family of amplitude `ε`, uniformly over the event tree -/

variable {J Y Z X E : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), §2.1, p. 394 (**the one-parameter family of economies**): amplitude `ε`
scales the initial exogenous state (`x₀ = ε x₀₁`) and every innovation (`σ = ε`), starting
from the steady-state lagged decision `ȳ`. -/
def famP (ybar : Y) (x01 : X) (ε : ℝ) : Y × X × ℝ := (ybar, ε • x01, ε)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), §2.1: at `ε = 0` the family is the deterministic steady state. -/
theorem famP_zero (ybar : Y) (x01 : X) : famP ybar x01 0 = pbar ybar := by
  simp [famP, pbar]

/-- Woodford (2003), §2.1: the family is affine in `ε`, with direction `(0, x₀₁, 1)`. -/
theorem hasDerivAt_famP (ybar : Y) (x01 : X) (ε : ℝ) :
    HasDerivAt (famP ybar x01) (0, x01, 1) ε := by
  have h : HasDerivAt (fun ε : ℝ => ε • x01) x01 ε := by
    simpa using (hasDerivAt_id ε).smul_const x01
  exact (hasDerivAt_const ε ybar).prodMk (h.prodMk (hasDerivAt_id ε))

/-- Woodford (2003), (2.10), p. 394, uniformly over dates and states (**the equilibrium family is
`ȳ + ε y₁ + O(ε²)` uniformly on the event tree**): if the local equilibrium `ψ` is `C²` at
`p̄` (e.g. `SmoothInSigma.Model.exists_smooth_solution` with `f` of class `C²`), then along the
amplitude family, with `y₁ = Dψ(p̄)(0, x₀₁, 1)`, one constant `C` bounds the remainder at every
node: `‖ψ(ε)_n − ȳ − ε y₁_n‖ ≤ C ε²` for all small `ε`. -/
theorem family_nodes [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
    {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar)) (x01 : X) :
    ∃ C, ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ n, ‖ψ (famP ybar x01 ε) n - ybar -
      ε • fderiv ℝ ψ (pbar ybar) (0, x01, 1) n‖ ≤ C * ε ^ 2 := by
  have hfam : ContDiffAt ℝ 2 (famP ybar x01) 0 := by
    unfold famP
    fun_prop
  have hψ2' : ContDiffAt ℝ 2 ψ (famP ybar x01 0) := by rw [famP_zero]; exact hψ2
  have hc : ContDiffAt ℝ 2 (fun ε => ψ (famP ybar x01 ε)) 0 := hψ2'.comp 0 hfam
  have hd : HasFDerivAt ψ (fderiv ℝ ψ (pbar ybar)) (famP ybar x01 0) := by
    rw [famP_zero]
    exact (hψ2.differentiableAt (by norm_num)).hasFDerivAt
  have hder : deriv (fun ε => ψ (famP ybar x01 ε)) 0 = fderiv ℝ ψ (pbar ybar) (0, x01, 1) :=
    (hd.comp_hasDerivAt 0 (hasDerivAt_famP ybar x01 0)).deriv
  obtain ⟨C, hC⟩ := (taylor_one_isBigO hc).bound
  refine ⟨C, ?_⟩
  filter_upwards [hC] with ε hε n
  rw [hder, famP_zero, hbase, norm_pow, Real.norm_eq_abs, sq_abs] at hε
  refine le_trans ?_ hε
  have := norm_apply_le (ψ (famP ybar x01 ε) - constBd ybar -
    ε • fderiv ℝ ψ (pbar ybar) (0, x01, 1)) n
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, constBd_apply] at this
  exact this

/-! ## Uniform orders in the date and the state (`BridgeExtensions.UProc`)

`BridgeExtensions` states every infinite-horizon result under the hypothesis that each
first-order variable is `O(ε)`, and each second-order remainder `O(ε²)`, UNIFORMLY in the date
and the state (`UProc`), and notes that this is not implied by smoothness at each date. For the
equilibrium of a model in the class of `SmoothInSigma` it is a theorem: the implicit
function theorem on `ℓ∞` makes the family smooth as a map into bounded processes. Here a state is an
infinite path `ω : ℕ → J` of innovations and the date-`t` node is its first `t` entries. -/

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Woodford (2003), §2, p. 394: the date-`t` node of an infinite path of innovations. -/
def pathNode (ω : ℕ → J) (t : ℕ) : List J := List.ofFn fun i : Fin t => ω i

/-- Woodford (2003), §2, p. 394 (**uniform second-order remainder, from primitives**): for any
linear readout `R`, `R(ψ(ε)_t − ȳ) − ε R(y₁_t) = O(ε²)` uniformly in the date and the state —
the second-order `UProc` hypothesis of `BridgeExtensions`. -/
theorem uproc_second_order [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (R : Y →L[ℝ] F) (x01 : X) :
    BridgeExtensions.UProc (𝓝 (0 : ℝ)) (fun ε t (ω : ℕ → J) =>
      R (ψ (famP ybar x01 ε) (pathNode ω t) - ybar) -
        ε • R (fderiv ℝ ψ (pbar ybar) (0, x01, 1) (pathNode ω t))) fun ε => ε ^ 2 := by
  obtain ⟨C, hC⟩ := family_nodes hbase hψ2 x01
  refine IsBigO.of_bound (‖R‖ * C) ((hC.prod_inl ⊤).mono fun q hq => ?_)
  beta_reduce
  rw [← map_smul, ← map_sub, norm_pow, Real.norm_eq_abs, sq_abs, mul_assoc]
  exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hq _) (norm_nonneg _))

/-- Woodford (2003), §2, p. 394 (**bounded fluctuations, from primitives**): for any linear
readout `R`, the deviation `R(ψ(ε)_t − ȳ)` is `O(ε)` uniformly in the date and the state — the
first-order `UProc` hypothesis of `BridgeExtensions`. -/
theorem uproc_first_order [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (R : Y →L[ℝ] F) (x01 : X) :
    BridgeExtensions.UProc (𝓝 (0 : ℝ)) (fun ε t (ω : ℕ → J) =>
      R (ψ (famP ybar x01 ε) (pathNode ω t) - ybar)) fun ε => ε ^ 1 := by
  obtain ⟨C, hC⟩ := family_nodes hbase hψ2 x01
  set v := fderiv ℝ ψ (pbar ybar) (0, x01, 1) with hv
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with ε hε
    have := Metric.mem_ball.1 hε
    rw [Real.dist_eq, sub_zero] at this
    exact this.le
  refine IsBigO.of_bound (‖R‖ * (|C| + ‖v‖)) (((hC.and h1).prod_inl ⊤).mono fun q hq => ?_)
  obtain ⟨hq1, hq2⟩ := hq
  have hn : ‖ψ (famP ybar x01 q.1) (pathNode q.2.2 q.2.1) - ybar‖ ≤ (|C| + ‖v‖) * |q.1| := by
    have e : ψ (famP ybar x01 q.1) (pathNode q.2.2 q.2.1) - ybar =
        (ψ (famP ybar x01 q.1) (pathNode q.2.2 q.2.1) - ybar -
          q.1 • v (pathNode q.2.2 q.2.1)) + q.1 • v (pathNode q.2.2 q.2.1) := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h3 : C * q.1 ^ 2 ≤ |C| * |q.1| := by
      rw [← sq_abs]
      calc C * |q.1| ^ 2 ≤ |C| * |q.1| ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C)
            (sq_nonneg _)
        _ ≤ |C| * |q.1| := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
          nlinarith [abs_nonneg q.1]
    have h4 : ‖q.1 • v (pathNode q.2.2 q.2.1)‖ ≤ ‖v‖ * |q.1| := by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (norm_apply_le v _) (abs_nonneg _)
    nlinarith [hq1 (pathNode q.2.2 q.2.1)]
  beta_reduce
  rw [pow_one, Real.norm_eq_abs, mul_assoc]
  exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _))

/-! ## Proposition 6.1 along the equilibrium policy -/

variable {ι : Type} [Fintype ι] {Ξ : Type} [NormedAddCommGroup Ξ] [NormedSpace ℝ Ξ]

omit [Fintype ι] in
/-- Woodford (2003), §2.1, p. 393: the cross-section of log outputs at node `n` along the
amplitude family, `ŷ_n(ε) = R(ψ(ε)_n − ȳ)`, read off the decision vector by a linear map `R`
(e.g. the coordinates of the log outputs when the model is written in logs). -/
noncomputable def yhat (ψ : Y × X × ℝ → Bd (List J) Y) (R : Y →L[ℝ] (ι → ℝ)) (ybar : Y)
    (x01 : X) (n : List J) (ε : ℝ) : ι → ℝ :=
  R (ψ (famP ybar x01 ε) n - ybar)

omit [Fintype ι] in
/-- Woodford (2003), (2.10), p. 394: the first-order solution for the cross-section at node `n`,
`y₁_n = R(Dψ(p̄)(0, x₀₁, 1)_n)`. -/
noncomputable def yone (ψ : Y × X × ℝ → Bd (List J) Y) (R : Y →L[ℝ] (ι → ℝ)) (ybar : Y)
    (x01 : X) (n : List J) : ι → ℝ :=
  R (fderiv ℝ ψ (pbar ybar) (0, x01, 1) n)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), §2.1, p. 393: the disturbance vector `ξ₁` at node `n` per unit of amplitude,
`ξ₁_n = S(x_n)` along the state path from `x₀₁` with unit innovations. -/
def xione (M : Model J Y Z X E) (S : X →L[ℝ] Ξ) (x01 : X) (n : List J) : Ξ :=
  S (M.stateAt x01 1 n)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), §2.1: along the amplitude family the disturbances are exactly `ε ξ₁_n`
(the state is linear in `(x₀, σ)`). -/
theorem disturbance_eq (M : Model J Y Z X E) (S : X →L[ℝ] Ξ) (x01 : X) (ε : ℝ) (n : List J) :
    S (M.stateAt (ε • x01) ε n) = ε • xione M S x01 n := by
  rw [xione, ← map_smul, ← M.stateAt_smul, mul_one]

/-- Woodford (2003), (2.10), p. 394, uniformly over dates and states (**the smoothness hypothesis
of Layer B, discharged**): `ŷ_n(ε) − ε y₁_n = O(ε²)` uniformly over all nodes of the event
tree, i.e. along `⊤ ×ˢ 𝓝 0`. -/
theorem family_readout [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
    {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (R : Y →L[ℝ] (ι → ℝ)) (x01 : X) :
    (fun q : List J × ℝ => yhat ψ R ybar x01 q.1 q.2 - q.2 • yone ψ R ybar x01 q.1) =O[
      (⊤ : Filter (List J)) ×ˢ 𝓝 0] fun q => q.2 ^ 2 := by
  obtain ⟨C, hC⟩ := family_nodes hbase hψ2 x01
  refine IsBigO.of_bound (‖R‖ * C) ((hC.prod_inr ⊤).mono fun q hq => ?_)
  have e : yhat ψ R ybar x01 q.1 q.2 - q.2 • yone ψ R ybar x01 q.1 =
      R (ψ (famP ybar x01 q.2) q.1 - ybar - q.2 • fderiv ℝ ψ (pbar ybar) (0, x01, 1) q.1) := by
    simp only [yhat, yone, map_sub, map_smul]
  rw [e, norm_pow, Real.norm_eq_abs, sq_abs, mul_assoc]
  exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hq q.1) (norm_nonneg _))

/-- Woodford (2003), (2.10), p. 394 (**the exact hypothesis of `BridgeCore.Econ.prop61_bridge`,
discharged at every node**): at a fixed node `n`, `ŷ_n(ε) − ε y₁_n = O(ε²)` as `ε → 0`. -/
theorem bridge_hypothesis [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
    {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (R : Y →L[ℝ] (ι → ℝ)) (x01 : X) (n : List J) :
    (fun ε => yhat ψ R ybar x01 n ε - ε • yone ψ R ybar x01 n) =O[𝓝 0] fun ε => ε ^ 2 := by
  obtain ⟨C, hC⟩ := (family_readout hbase hψ2 R x01).bound
  refine IsBigO.of_bound C ?_
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 hC
  rw [eventually_top] at hpa
  filter_upwards [hpb] with ε hε
  exact hab (hpa n) hε


omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), §2.1: the per-unit disturbances are bounded uniformly over the tree,
`‖ξ₁_n‖ ≤ ‖S‖ (‖x₀₁‖ + K/(1 − ‖Λ‖))`. -/
theorem norm_xione_le [Fintype J] {M : Model J Y Z X E} (hM : M.Std) (S : X →L[ℝ] Ξ) (x01 : X)
    (n : List J) : ‖xione M S x01 n‖ ≤ ‖S‖ * (‖x01‖ + M.shockBound / (1 - ‖M.Λ‖)) := by
  refine (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  simpa using SmoothInSigma.Model.norm_stateAt_le hM x01 1 n

/-- Woodford (2003), (2.10), p. 394: the first-order cross-section is bounded uniformly over the
tree, `‖y₁_n‖ ≤ ‖R‖ ‖Dψ(p̄)(0, x₀₁, 1)‖`. -/
theorem norm_yone_le (ψ : Y × X × ℝ → Bd (List J) Y) (R : Y →L[ℝ] (ι → ℝ)) (ybar : Y)
    (x01 : X) (n : List J) :
    ‖yone ψ R ybar x01 n‖ ≤ ‖R‖ * ‖fderiv ℝ ψ (pbar ybar) (0, x01, 1)‖ :=
  (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_apply_le _ n) (norm_nonneg _))

/-- Woodford (2003), **Proposition 6.1, eq. (2.10), p. 394 (Layer B along the equilibrium
policy, uniformly over all dates and states)**. Let the economy's equilibrium be the local
equilibrium `ψ` of a model in the class of `SmoothInSigma` (`C²` at the steady state, as
`exists_smooth_solution` provides for `f` of class `C²` under determinacy), let the cross-section
of log outputs be `ŷ = R(y − ȳ)` and the disturbances `ξ = S x`. Then along the amplitude family,
at every node `n` of the event tree, actual period utility satisfies
`U_n(ε) = tipState(ε ξ₁_n) − (ε²/2) Ȳ u_c L(y₁_n, ξ₁_n) + O(ε³)`, with ONE constant for all
nodes (`⊤ ×ˢ 𝓝 0`). No smoothness of the family is assumed: it is proved. -/
theorem prop61_nodes [Fintype J] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
    {M : Model J Y Z X E} (hM : M.Std) {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (x01 : X) {Ec : BridgeCore.Econ Ξ ι}
    (hEc : Ec.Std) (heff : Ec.vy = Ec.uc) (hden : Ec.sig + Ec.omg ≠ 0) :
    (fun q : List J × ℝ => Ec.Ustate (yhat ψ R ybar x01 q.1 q.2) (S (M.stateAt (q.2 • x01) q.2 q.1))
      - (Ec.tipState (q.2 • xione M S x01 q.1) + q.2 ^ 2 / 2 *
        (-(Ec.Yb * Ec.uc * Ec.lossB (yone ψ R ybar x01 q.1) (xione M S x01 q.1))))) =O[
      (⊤ : Filter (List J)) ×ˢ 𝓝 0] fun q => q.2 ^ 3 := by
  have hs : Tendsto (fun q : List J × ℝ => q.2) ((⊤ : Filter (List J)) ×ˢ 𝓝 0) (𝓝 0) :=
    tendsto_snd
  have h1 : (fun q : List J × ℝ => yone ψ R ybar x01 q.1) =O[(⊤ : Filter (List J)) ×ˢ 𝓝 0]
      fun _ => (1 : ℝ) :=
    IsBigO.of_bound (‖R‖ * ‖fderiv ℝ ψ (pbar ybar) (0, x01, 1)‖) (Eventually.of_forall fun q => by
      rw [norm_one, mul_one]
      exact norm_yone_le ψ R ybar x01 q.1)
  have hξ1 : (fun q : List J × ℝ => xione M S x01 q.1) =O[(⊤ : Filter (List J)) ×ˢ 𝓝 0]
      fun _ => (1 : ℝ) :=
    IsBigO.of_bound (‖S‖ * (‖x01‖ + M.shockBound / (1 - ‖M.Λ‖)))
      (Eventually.of_forall fun q => by
        rw [norm_one, mul_one]
        exact norm_xione_le hM S x01 q.1)
  refine (BridgeCore.Econ.prop61_family (s := fun q : List J × ℝ => q.2) hEc heff hden hs
    (family_readout hbase hψ2 R x01) h1 hξ1).congr_left fun q => ?_
  rw [disturbance_eq]

/-- Woodford (2003), **Proposition 6.1, eq. (2.10), p. 394 (Layer B at a node, the one-parameter
form `BridgeCore.Econ.prop61_bridge`, with its smoothness hypothesis discharged)**: at any fixed
date-and-state `n`,
`U_n(ε) = tipState(ε ξ₁_n) − (ε²/2) Ȳ u_c L(y₁_n, ξ₁_n) + O(ε³)`. -/
theorem prop61_node [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] {M : Model J Y Z X E}
    {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (x01 : X) {Ec : BridgeCore.Econ Ξ ι}
    (hEc : Ec.Std) (heff : Ec.vy = Ec.uc) (hden : Ec.sig + Ec.omg ≠ 0) (n : List J) :
    (fun ε => Ec.Ustate (yhat ψ R ybar x01 n ε) (S (M.stateAt (ε • x01) ε n)) -
      (Ec.tipState (ε • xione M S x01 n) + ε ^ 2 / 2 *
        (-(Ec.Yb * Ec.uc * Ec.lossB (yone ψ R ybar x01 n) (xione M S x01 n))))) =O[𝓝 0]
      fun ε => ε ^ 3 := by
  refine (BridgeCore.Econ.prop61_bridge hEc heff hden (xione M S x01 n)
    (bridge_hypothesis hbase hψ2 R x01 n)).congr_left fun ε => ?_
  rw [disturbance_eq]

/-! ## Expected and discounted welfare over the event tree -/

variable [Fintype J]

/-- Woodford (2003), §1, p. 385 (expected utility): the probability of a date-`t` history
`ω = (j_0, …, j_{t−1})`, `∏_i π_{j_i}`. -/
def pathProb (M : Model J Y Z X E) {t : ℕ} (ω : Fin t → J) : ℝ := ∏ i, M.prob (ω i)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), §1: path probabilities are nonnegative. -/
theorem pathProb_nonneg {M : Model J Y Z X E} (hM : M.Std) {t : ℕ} (ω : Fin t → J) :
    0 ≤ pathProb M ω :=
  Finset.prod_nonneg fun i _ => hM.prob_nonneg (ω i)

omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] in
/-- Woodford (2003), §1: the date-`t` path probabilities sum to one. -/
theorem sum_pathProb {M : Model J Y Z X E} (hM : M.Std) (t : ℕ) :
    ∑ ω : Fin t → J, pathProb M ω = 1 := by
  classical
  unfold pathProb
  rw [← Fintype.prod_sum (fun (_ : Fin t) j => M.prob j), hM.prob_sum, Finset.prod_const_one]

omit [Fintype J] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Woodford (2003), App. E.2, p. 695 (an enumeration of the tree): every node is hit by a map
`ℕ → List J`, so bounds stated for sequences transfer to the tree. -/
theorem exists_enum_nodes [Finite J] : ∃ e : ℕ → List J, ∀ n, ∃ t, e t = n := by
  have := Fintype.ofFinite J
  let _ := Fintype.toEncodable J
  exact ⟨fun t => (Encodable.decode t).getD [], fun n => ⟨Encodable.encode n, by
    simp [Encodable.encodek]⟩⟩

omit [Fintype J] in
/-- Woodford (2003), App. E.2, p. 695: a remainder that is `O(εᵏ)` uniformly over the tree has
one constant `C` with `‖f_n(ε)‖ ≤ C |ε|ᵏ` for all nodes and all small `ε`. -/
theorem bound_of_nodes {V : Type} [Norm V] {f : List J × ℝ → V} {k : ℕ}
    (h : f =O[(⊤ : Filter (List J)) ×ˢ 𝓝 0] fun q => q.2 ^ k) :
    ∃ C, ∀ᶠ ε in 𝓝 0, ∀ n, ‖f (n, ε)‖ ≤ C * |ε| ^ k := by
  obtain ⟨C, hC⟩ := h.bound
  refine ⟨C, ?_⟩
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := Filter.eventually_prod_iff.1 hC
  rw [eventually_top] at hpa
  filter_upwards [hpb] with ε hε n
  have := hab (hpa n) hε
  rwa [norm_pow, Real.norm_eq_abs] at this

/-- Woodford (2003), §1, p. 385: expected period-`t` utility along the amplitude family,
`E₀ U_t(ε) = ∑_{histories ω of length t} π(ω) U_{n(ω)}(ε)`. -/
noncomputable def expU (Ec : BridgeCore.Econ Ξ ι) (M : Model J Y Z X E)
    (ψ : Y × X × ℝ → Bd (List J) Y) (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (ybar : Y) (x01 : X)
    (t : ℕ) (ε : ℝ) : ℝ :=
  ∑ ω : Fin t → J, pathProb M ω * Ec.Ustate (yhat ψ R ybar x01 (List.ofFn ω) ε)
    (S (M.stateAt (ε • x01) ε (List.ofFn ω)))

/-- Woodford (2003), (2.10): the expected period-`t` terms independent of policy,
`E₀ tipState(ε ξ₁)`. -/
noncomputable def expT (Ec : BridgeCore.Econ Ξ ι) (M : Model J Y Z X E) (S : X →L[ℝ] Ξ)
    (x01 : X) (t : ℕ) (ε : ℝ) : ℝ :=
  ∑ ω : Fin t → J, pathProb M ω * Ec.tipState (ε • xione M S x01 (List.ofFn ω))

/-- Woodford (2003), (2.10)–(2.11): the expected period-`t` loss of the first-order solution,
`E₀ L(y₁, ξ₁)`. -/
noncomputable def expL (Ec : BridgeCore.Econ Ξ ι) (M : Model J Y Z X E)
    (ψ : Y × X × ℝ → Bd (List J) Y) (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (ybar : Y) (x01 : X)
    (t : ℕ) : ℝ :=
  ∑ ω : Fin t → J, pathProb M ω * Ec.lossB (yone ψ R ybar x01 (List.ofFn ω))
    (xione M S x01 (List.ofFn ω))

/-- Woodford (2003), (2.10)–(2.11) and survey error 25 (**Proposition 6.1 for expected discounted
welfare along the equilibrium policy, Layer B**): with the equilibrium of a model in the class of
`SmoothInSigma` (`ψ` `C²` at the steady state; no smoothness hypothesis on the family) and
`0 ≤ β < 1`,
`∑ βᵗ E₀U_t(ε) = ∑ βᵗ E₀ tipState(ε ξ₁) − (ε²/2) Ȳu_c ∑ βᵗ E₀ L(y₁, ξ₁) + O(ε³)`
(genuine `tsum`s of bounded sequences). -/
theorem prop61_discounted [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
    {M : Model J Y Z X E} (hM : M.Std) {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (x01 : X) {Ec : BridgeCore.Econ Ξ ι}
    (hEc : Ec.Std) (heff : Ec.vy = Ec.uc) (hden : Ec.sig + Ec.omg ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    (fun ε => ∑' t, β ^ t * expU Ec M ψ R S ybar x01 t ε - (∑' t, β ^ t * expT Ec M S x01 t ε +
      ε ^ 2 / 2 * (-(Ec.Yb * Ec.uc * ∑' t, β ^ t * expL Ec M ψ R S ybar x01 t)))) =O[𝓝 0]
      fun ε => ε ^ 3 := by
  obtain ⟨e, he⟩ := exists_enum_nodes (J := J)
  set k := Ec.Yb * Ec.uc with hk
  -- the period remainder, uniformly over nodes
  obtain ⟨C, hC⟩ := bound_of_nodes (prop61_nodes hM hbase hψ2 R S x01 hEc heff hden)
  -- the t.i.p., uniformly over nodes
  have hξe : ∃ C, ∀ t, ‖xione M S x01 (e t)‖ ≤ C :=
    ⟨_, fun t => norm_xione_le hM S x01 (e t)⟩
  obtain ⟨CT, hCT⟩ := (BridgeCore.isBigO_unif_iff (f := fun t ε => Ec.tipState
    (ε • xione M S x01 (e t))) (g := fun _ => (1 : ℝ))).1 (BridgeCore.Econ.tipState_unif hξe)
  -- the loss, uniformly over nodes
  have hye : ∃ C, ∀ t, ‖yone ψ R ybar x01 (e t)‖ ≤ C :=
    ⟨_, fun t => norm_yone_le ψ R ybar x01 (e t)⟩
  obtain ⟨CL, hCL⟩ := BridgeCore.Econ.lossB_bounded hEc hye hξe
  refine BridgeCore.discounted_bridge (U := expU Ec M ψ R S ybar x01)
    (T := expT Ec M S x01) (L := expL Ec M ψ R S ybar x01) hβ0 hβ1 ?_ ?_ ?_
  · refine (BridgeCore.isBigO_unif_iff (f := fun t ε => expU Ec M ψ R S ybar x01 t ε -
      (expT Ec M S x01 t ε + ε ^ 2 / 2 * (-(k * expL Ec M ψ R S ybar x01 t))))
      (g := fun ε => ε ^ 3)).2 ⟨C, ?_⟩
    filter_upwards [hC] with ε hε t
    have e1 : expU Ec M ψ R S ybar x01 t ε - (expT Ec M S x01 t ε +
        ε ^ 2 / 2 * (-(k * expL Ec M ψ R S ybar x01 t))) =
        ∑ ω : Fin t → J, pathProb M ω * (Ec.Ustate (yhat ψ R ybar x01 (List.ofFn ω) ε)
          (S (M.stateAt (ε • x01) ε (List.ofFn ω))) -
          (Ec.tipState (ε • xione M S x01 (List.ofFn ω)) + ε ^ 2 / 2 *
            (-(k * Ec.lossB (yone ψ R ybar x01 (List.ofFn ω))
              (xione M S x01 (List.ofFn ω)))))) := by
      simp only [expU, expT, expL, mul_sub, mul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 2
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun ω _ => by ring
    rw [e1, norm_pow, Real.norm_eq_abs]
    calc ‖∑ ω : Fin t → J, pathProb M ω * _‖ ≤ ∑ ω : Fin t → J, pathProb M ω * (C * |ε| ^ 3) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun ω _ => by
            rw [norm_mul, Real.norm_of_nonneg (pathProb_nonneg hM ω)]
            exact mul_le_mul_of_nonneg_left (hε _) (pathProb_nonneg hM ω))
      _ = C * |ε| ^ 3 := by rw [← Finset.sum_mul, sum_pathProb hM, one_mul]
  · refine (BridgeCore.isBigO_unif_iff (f := fun t ε => expT Ec M S x01 t ε)
      (g := fun _ => (1 : ℝ))).2 ⟨CT, ?_⟩
    filter_upwards [hCT] with ε hε t
    calc ‖expT Ec M S x01 t ε‖ ≤ ∑ ω : Fin t → J, pathProb M ω * (CT * ‖(1 : ℝ)‖) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun ω _ => by
            rw [norm_mul, Real.norm_of_nonneg (pathProb_nonneg hM ω)]
            refine mul_le_mul_of_nonneg_left ?_ (pathProb_nonneg hM ω)
            obtain ⟨s, hs⟩ := he (List.ofFn ω)
            have := hε s
            rwa [hs] at this)
      _ = CT * ‖(1 : ℝ)‖ := by rw [← Finset.sum_mul, sum_pathProb hM, one_mul]
  · refine ⟨CL, fun t => ?_⟩
    calc |expL Ec M ψ R S ybar x01 t| ≤ ∑ ω : Fin t → J, pathProb M ω * CL := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ => ?_)
          rw [abs_mul, abs_of_nonneg (pathProb_nonneg hM ω)]
          refine mul_le_mul_of_nonneg_left ?_ (pathProb_nonneg hM ω)
          obtain ⟨s, hs⟩ := he (List.ofFn ω)
          have := hCL s
          rwa [hs] at this
      _ = CL := by rw [← Finset.sum_mul, sum_pathProb hM, one_mul]


omit [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype ι] in
/-- Woodford (2003), (2.10): the expected terms independent of policy depend only on the
exogenous structure (the probabilities and the state's law of motion), not on the policy. -/
theorem expT_congr {MA MB : Model J Y Z X E} (hprob : MA.prob = MB.prob)
    (hst : ∀ x σ n, MA.stateAt x σ n = MB.stateAt x σ n) (Ec : BridgeCore.Econ Ξ ι)
    (S : X →L[ℝ] Ξ) (x01 : X) : expT Ec MA S x01 = expT Ec MB S x01 := by
  funext t ε
  simp only [expT, pathProb, xione, hprob, hst]

/-- Woodford (2003), §2.1, pp. 394–396 (**the welfare ranking of policies, from primitives**):
two policies, i.e. two models in the class with the same exogenous structure (probabilities and
state dynamics), the same steady state and the same readouts; if the discounted expected
first-order loss of `A` is smaller, `A` gives strictly higher discounted expected utility for
all small amplitudes `ε > 0`. -/
theorem prop61_discounted_ranking [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
    {MA MB : Model J Y Z X E} (hMA : MA.Std) (hMB : MB.Std) (hprob : MA.prob = MB.prob)
    (hst : ∀ x σ n, MA.stateAt x σ n = MB.stateAt x σ n)
    {ψA ψB : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hA : ψA (pbar ybar) = constBd ybar) (hA2 : ContDiffAt ℝ 2 ψA (pbar ybar))
    (hB : ψB (pbar ybar) = constBd ybar) (hB2 : ContDiffAt ℝ 2 ψB (pbar ybar))
    (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (x01 : X) {Ec : BridgeCore.Econ Ξ ι}
    (hEc : Ec.Std) (heff : Ec.vy = Ec.uc) (hden : Ec.sig + Ec.omg ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1)
    (hL : ∑' t, β ^ t * expL Ec MA ψA R S ybar x01 t < ∑' t, β ^ t * expL Ec MB ψB R S ybar x01 t) :
    ∀ᶠ ε in 𝓝[>] 0, ∑' t, β ^ t * expU Ec MB ψB R S ybar x01 t ε <
      ∑' t, β ^ t * expU Ec MA ψA R S ybar x01 t ε := by
  have hBd := prop61_discounted hMB hB hB2 R S x01 hEc heff hden hβ0 hβ1
  rw [← expT_congr hprob hst Ec S x01] at hBd
  exact BridgeCore.ranking_of_tip (mul_pos hEc.Yb_pos hEc.uc_pos)
    (prop61_discounted hMA hA hA2 R S x01 hEc heff hden hβ0 hβ1) hBd hL

/-- Woodford (2003), §1, p. 385, and Proposition 6.1 (**expected utility at a date `t`, Layer B
along the equilibrium policy**): over the `|J|ᵗ` date-`t` histories with their probabilities,
`E₀U_t(ε) = E₀ tipState(ε ξ₁) − (ε²/2) Ȳu_c E₀ L(y₁, ξ₁) + O(ε³)`
(`BridgeCore.Econ.prop61_expected` with its smoothness hypothesis discharged). -/
theorem prop61_expected_date [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
    {M : Model J Y Z X E} {ψ : Y × X × ℝ → Bd (List J) Y} {ybar : Y}
    (hbase : ψ (pbar ybar) = constBd ybar) (hψ2 : ContDiffAt ℝ 2 ψ (pbar ybar))
    (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (x01 : X) {Ec : BridgeCore.Econ Ξ ι}
    (hEc : Ec.Std) (heff : Ec.vy = Ec.uc) (hden : Ec.sig + Ec.omg ≠ 0) (t : ℕ) :
    (fun ε => OneParamTaylor.expect (pathProb M (t := t)) (fun ω => Ec.Ustate
        (yhat ψ R ybar x01 (List.ofFn ω) ε) (S (M.stateAt (ε • x01) ε (List.ofFn ω)))) -
      (OneParamTaylor.expect (pathProb M (t := t))
          (fun ω => Ec.tipState (ε • xione M S x01 (List.ofFn ω))) + ε ^ 2 / 2 *
        (-(Ec.Yb * Ec.uc * OneParamTaylor.expect (pathProb M (t := t))
          (fun ω => Ec.lossB (yone ψ R ybar x01 (List.ofFn ω)) (xione M S x01 (List.ofFn ω)))))))
      =O[𝓝 0] fun ε => ε ^ 3 := by
  refine (BridgeCore.Econ.prop61_expected hEc heff hden (pathProb M (t := t))
    (yh := fun ω ε => yhat ψ R ybar x01 (List.ofFn ω) ε)
    (y1 := fun ω => yone ψ R ybar x01 (List.ofFn ω)) (fun ω => xione M S x01 (List.ofFn ω))
    (fun ω => bridge_hypothesis hbase hψ2 R x01 (List.ofFn ω))).congr_left fun ε => ?_
  simp only [disturbance_eq]

/-- Woodford (2003), **Proposition 6.1 (Layer B) from primitives**: for a model in the class of
`SmoothInSigma` with `f` of class `C²`, a steady state and determinacy (the linearised operator
invertible on `ℓ∞`), there is a local equilibrium `ψ`, `C²` at the steady state, and along it
discounted expected utility has the second-order expansion of Proposition 6.1 with an `O(ε³)`
remainder — no smoothness of the family in `ε` is assumed. -/
theorem prop61_of_primitives [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E] {M : Model J Y Z X E}
    (hM : M.Std) (hf : ContDiff ℝ 2 M.f) {ybar : Y}
    (hss : M.f (SmoothInSigma.zbar ybar) = 0) (hdet : (M.linOp hM ybar).IsInvertible)
    (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (x01 : X) {Ec : BridgeCore.Econ Ξ ι}
    (hEc : Ec.Std) (heff : Ec.vy = Ec.uc) (hden : Ec.sig + Ec.omg ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    ∃ ψ : Y × X × ℝ → Bd (List J) Y, M.LocalSol ybar ψ ∧ ContDiffAt ℝ 2 ψ (pbar ybar) ∧
      (fun ε => ∑' t, β ^ t * expU Ec M ψ R S ybar x01 t ε - (∑' t, β ^ t * expT Ec M S x01 t ε +
        ε ^ 2 / 2 * (-(Ec.Yb * Ec.uc * ∑' t, β ^ t * expL Ec M ψ R S ybar x01 t)))) =O[𝓝 0]
        fun ε => ε ^ 3 := by
  obtain ⟨ψ, hψ, hc⟩ := SmoothInSigma.Model.exists_smooth_solution hM (k := 2) (by norm_num) hf
    hss hdet
  exact ⟨ψ, hψ, hc, prop61_discounted hM hψ.base hc R S x01 hEc heff hden hβ0 hβ1⟩

/-- Woodford (2003), **Proposition 6.1 (Layer B) from primitives, `f` smooth only near the
steady state**: as `prop61_of_primitives`, assuming only that `f` is `C²` at `z̄`. -/
theorem prop61_of_primitives_local [FiniteDimensional ℝ Y] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E]
    {M : Model J Y Z X E} (hM : M.Std) {ybar : Y}
    (hf : ContDiffAt ℝ 2 M.f (SmoothInSigma.zbar ybar))
    (hss : M.f (SmoothInSigma.zbar ybar) = 0) (hdet : (M.linOp hM ybar).IsInvertible)
    (R : Y →L[ℝ] (ι → ℝ)) (S : X →L[ℝ] Ξ) (x01 : X) {Ec : BridgeCore.Econ Ξ ι}
    (hEc : Ec.Std) (heff : Ec.vy = Ec.uc) (hden : Ec.sig + Ec.omg ≠ 0) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) :
    ∃ ψ : Y × X × ℝ → Bd (List J) Y, M.LocalSol ybar ψ ∧ ContDiffAt ℝ 2 ψ (pbar ybar) ∧
      (fun ε => ∑' t, β ^ t * expU Ec M ψ R S ybar x01 t ε - (∑' t, β ^ t * expT Ec M S x01 t ε +
        ε ^ 2 / 2 * (-(Ec.Yb * Ec.uc * ∑' t, β ^ t * expL Ec M ψ R S ybar x01 t)))) =O[𝓝 0]
        fun ε => ε ^ 3 := by
  obtain ⟨ψ, hψ, hc⟩ := SmoothInSigma.Model.exists_smooth_solution_local hM (k := 2)
    (by norm_num) (by exact_mod_cast hf) hss hdet
  exact ⟨ψ, hψ, hc, prop61_discounted hM hψ.base hc R S x01 hEc heff hden hβ0 hβ1⟩

end Woodford.StabilizationWelfare.SmoothInSigmaWelfare
