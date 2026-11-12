/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import PriceLevelDetermination.LocalIFTSystemsStochasticSunspots
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Sunspots when (A.8) is not onto: the bounded-below criterion

Woodford (2003), *Interest and Prices*, Appendix A.3, pp. 632–634 (indeterminacy of
`E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0`). `LocalIFTSystemsStochasticSunspots` proves that genuinely
random equilibria exist near the steady state when the operator (A.8) of the linearisation is
onto but not one-to-one. This module treats the case where (A.8) is **not onto**.

## Main results

* `BoundedBelow`, `boundedBelow_iff`: `‖v‖ ≤ C ‖L v‖`, equivalently `L` one-to-one with closed
  range (Banach); `boundedBelow_of_isUnit`.
* `opS_boundedBelow` (**the linear transfer**): if the perfect-foresight operator (A.8) is
  bounded below with constant `C`, the stochastic operator (A.12) is bounded below on adapted
  processes, for every expectation system, with constant `C (1 + 2C‖f₃‖)`. The proof projects an
  adapted solution on date-`k` forecasts (`phi_identity`); the innovations
  `x_{k+1} − E_k x_{k+1}` are first bounded by the perfect-foresight problem they solve
  (`innov_bound`). `sysOp_boundedBelow_of_opS` is the converse.
* `unique_of_boundedBelow` (**nonlinear local uniqueness**): if `G` is `C¹` near the steady state
  and (A.8) is bounded below (one-to-one with closed range — onto or not), then for every
  expectation system there is `ε > 0` such that for every `(x_{−1}, e)` with `‖(x_{−1}, e)‖ < ε`
  there is **at most one** bounded adapted equilibrium within `ε` of the steady state.
  `no_sunspot_of_boundedBelow`: in particular there are no sunspot equilibria (random or
  deterministic) near the steady state.
* `sunspot_iff_of_surjective`: when (A.8) is onto, random sunspot equilibria near the steady
  state exist (on the coin tree, at every scale) **iff** (A.8) is not one-to-one.
* `eq_zero_of_push`: the elementary supremum argument behind the non-existence results of
  `SunspotsNotOntoExamples` and `InertialBoundary`.

So the linearisation decides the sunspot question exactly when (A.8) is onto or bounded below;
`SunspotsNotOntoExamples` shows that in the remaining cases it may not decide it.
-/

namespace Woodford.PriceLevelDetermination.SunspotsBoundedBelow

open scoped Topology Matrix
open LinearSystems LinearSystemsStochastic LocalIFTSystemsStochastic SystemsBK.GeneralBKForward
open LocalIFTSystems (Arg linOp M1 M2 M3 cutoff cutoff_eq contDiff_cutoff
  exists_ball_contDiffAt lin_cutoff)

/-! ### Bounded-below operators -/

/-- Woodford (2003), App. A.3, p. 632: a continuous linear map is **bounded below** when
`‖v‖ ≤ C ‖L v‖` for some `C ≥ 0` (for Banach spaces: one-to-one with closed range,
`boundedBelow_iff`). -/
def BoundedBelow {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (L : V →L[ℝ] W) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖v‖ ≤ C * ‖L v‖

/-- Woodford (2003), App. A.3, p. 632: between Banach spaces, **bounded below ⟺ one-to-one with
closed range** (open mapping theorem). -/
theorem boundedBelow_iff {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace V] [CompleteSpace W]
    (L : V →L[ℝ] W) : BoundedBelow L ↔ Function.Injective L ∧ IsClosed (Set.range L) := by
  constructor
  · rintro ⟨C, hC0, hC⟩
    have hinj : Function.Injective L := by
      intro a b hab
      have h := hC (a - b)
      rw [map_sub, hab, sub_self, norm_zero, mul_zero] at h
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
    refine ⟨hinj, (L.isClosed_range_iff_antilipschitz_of_injective hinj).mpr
      ⟨Real.toNNReal C, L.antilipschitz_of_bound fun v => ?_⟩⟩
    rw [Real.coe_toNNReal C hC0]
    exact hC v
  · rintro ⟨hinj, hcl⟩
    obtain ⟨K, hK⟩ := L.antilipschitz_of_injective_of_isClosed_range hinj hcl
    refine ⟨K, K.2, fun v => ?_⟩
    have h := hK.le_mul_dist v 0
    rwa [map_zero, dist_zero_right, dist_zero_right] at h

/-- Woodford (2003), App. A.3, p. 632: an invertible operator is bounded below. -/
theorem boundedBelow_of_isUnit {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : V →L[ℝ] V} (h : IsUnit L) : BoundedBelow L := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨‖(↑u⁻¹ : V →L[ℝ] V)‖, norm_nonneg _, fun v => ?_⟩
  have e : (↑u⁻¹ : V →L[ℝ] V) ((u : V →L[ℝ] V) v) = v := by
    change ((↑u⁻¹ * ↑u : V →L[ℝ] V)) v = v
    rw [Units.inv_mul]
    rfl
  calc ‖v‖ = ‖(↑u⁻¹ : V →L[ℝ] V) ((u : V →L[ℝ] V) v)‖ := by rw [e]
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

/-! ### The supremum argument -/

/-- Woodford (2003), App. A.3, p. 634 (tool, the "push" argument): if a bounded family satisfies
`|a_j|³ ≤ K (B − |a_j|)` for **every** uniform bound `B` of `|a|`, it vanishes (look at an index
where `|a_j|` is within `δ` of the supremum). -/
theorem eq_zero_of_push {J : Type*} (a : J → ℝ) (hb : ∃ B, ∀ j, |a j| ≤ B) {K : ℝ} (hK : 0 < K)
    (h : ∀ B, (∀ j, |a j| ≤ B) → ∀ j, |a j| ^ 3 ≤ K * (B - |a j|)) (j : J) : a j = 0 := by
  by_contra hne
  have hpos : 0 < |a j| := abs_pos.mpr hne
  obtain ⟨B, hB⟩ := hb
  have hbdd : BddAbove (Set.range fun k => |a k|) := ⟨B, by rintro _ ⟨k, rfl⟩; exact hB k⟩
  set S := ⨆ k, |a k| with hS
  have hle : ∀ k, |a k| ≤ S := fun k => le_ciSup hbdd k
  have hSpos : 0 < S := hpos.trans_le (hle j)
  set δ := min (S / 2) (S ^ 3 / (8 * K)) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have : Nonempty J := ⟨j⟩
  obtain ⟨k, hk⟩ := exists_lt_of_lt_ciSup (show S - δ < S by linarith)
  have h1 := h S hle k
  have hk2 : S / 2 ≤ |a k| := by
    have := min_le_left (S / 2) (S ^ 3 / (8 * K))
    linarith
  have h3 : S ^ 3 / 8 ≤ |a k| ^ 3 := by
    have := pow_le_pow_left₀ (by positivity) hk2 3
    have e : (S / 2) ^ 3 = S ^ 3 / 8 := by ring
    linarith
  have h4 : K * (S - |a k|) < K * δ := mul_lt_mul_of_pos_left (by linarith) hK
  have h5 : K * δ ≤ S ^ 3 / 8 := by
    calc K * δ ≤ K * (S ^ 3 / (8 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le
      _ = S ^ 3 / 8 := by field_simp
  linarith

/-! ### The linear transfer: perfect foresight bounded below ⟹ uncertainty bounded below -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : Type*} (𝔼 : ExpectationSystem Ω)

omit [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): a linear functional of random variables commutes
with a constant matrix. -/
theorem phi_mv (Φ : (Ω → ℝ) →ₗ[ℝ] ℝ) (M : Matrix ι ι ℝ) (b : ι → Ω → ℝ) (i : ι) :
    Φ (mv M b i) = (M *ᵥ fun j => Φ (b j)) i := by
  simp only [mv, map_sum, map_smul, Matrix.mulVec, dotProduct, smul_eq_mul]

/-- Woodford (2003), App. A.3, p. 634 (**projection identity**): for an adapted `x` with
`z = (A.12) x` and any linear functional `Φ` of date-`·` random variables, the sequence
`s ↦ Φ(x_s)` satisfies the perfect-foresight equations with forcing `Φ(z_t)` plus the
forecast-error term `f₃ Φ(x_{t+1} − E_t x_{t+1})`. -/
theorem phi_identity (f₁ f₂ f₃ : Matrix ι ι ℝ) (x : SProcV ι Ω) (hx : AdaptedV 𝔼 (toP x))
    (Φ : (Ω → ℝ) →ₗ[ℝ] ℝ) (t : ℕ) :
    f₁ *ᵥ (fun i => Φ (lagP 0 (toP x) t i)) + f₂ *ᵥ (fun i => Φ (toP x t i)) +
      f₃ *ᵥ (fun i => Φ (toP x (t + 1) i)) =
    (fun i => Φ (toP (opS 𝔼 f₁ f₂ f₃ x) t i)) +
      f₃ *ᵥ (fun i => Φ (toP x (t + 1) i - 𝔼.E t (toP x (t + 1) i))) := by
  have hz : (fun i => Φ (toP (opS 𝔼 f₁ f₂ f₃ x) t i)) =
      f₁ *ᵥ (fun i => Φ (lagP 0 (toP x) t i)) + f₂ *ᵥ (fun i => Φ (toP x t i)) +
        f₃ *ᵥ (fun i => Φ (𝔼.E t (toP x (t + 1) i))) := by
    rw [toP_opS_of_adapted 𝔼 f₁ f₂ f₃ x hx t]
    funext i
    simp only [Pi.add_apply, map_add]
    rw [phi_mv, phi_mv, phi_mv]
  have hs : (fun i => Φ (toP x (t + 1) i - 𝔼.E t (toP x (t + 1) i))) =
      (fun i => Φ (toP x (t + 1) i)) - fun i => Φ (𝔼.E t (toP x (t + 1) i)) := by
    funext i
    simp only [map_sub, Pi.sub_apply]
  rw [hz, hs, Matrix.mulVec_sub]
  abel

/-- Woodford (2003), App. A.3, p. 632 (tool): a bounded-below perfect-foresight operator bounds
every bounded solution of the perfect-foresight equations by its forcing. -/
theorem pf_bound {f₁ f₂ f₃ : Matrix ι ι ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖v‖ ≤ C * ‖sysOp f₁ f₂ f₃ v‖) {y : ℕ → ι → ℝ} (hy : LinearSystems.BoundedSeq y)
    {R : ℝ} (hR : 0 ≤ R) (h : ∀ s, ‖f₁ *ᵥ lagV 0 y s + f₂ *ᵥ y s + f₃ *ᵥ y (s + 1)‖ ≤ R) (s : ℕ) :
    ‖y s‖ ≤ C * R := by
  set Y := toSeqV y hy with hY
  have hn : ‖sysOp f₁ f₂ f₃ Y‖ ≤ R := LocalIFT.norm_seq_le hR fun t => by
    rw [sysOp_apply]
    exact h t
  calc ‖y s‖ = ‖Y s‖ := rfl
    _ ≤ ‖Y‖ := LocalIFT.norm_seq_apply_le Y s
    _ ≤ C * ‖sysOp f₁ f₂ f₃ Y‖ := hC Y
    _ ≤ C * R := mul_le_mul_of_nonneg_left hn hC0

omit [Fintype ι] [DecidableEq ι] in
/-- Woodford (2003), App. A.3, p. 634 (tool): `|E_{k+1} y − E_k y| ≤ 2M` when `|y| ≤ M`. -/
theorem abs_innov_le {y : Ω → ℝ} {M : ℝ} (hy : ∀ ω, |y ω| ≤ M) (k : ℕ) (ω : Ω) :
    |𝔼.E (k + 1) y ω - 𝔼.E k y ω| ≤ 2 * M := by
  have h1 := abs_le.mp (𝔼.abs_E_le hy (k + 1) ω)
  have h2 := abs_le.mp (𝔼.abs_E_le hy k ω)
  exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- Woodford (2003), App. A.3, p. 634: **the forecast errors are pinned down**: if (A.8) is
bounded below with constant `C`, every adapted `x` has innovations
`|x_{k+1} − E_k x_{k+1}| ≤ 2C ‖(A.12) x‖` (the innovation path `E_{k+1} x_{k+1+s} − E_k x_{k+1+s}`
solves the perfect-foresight equations with zero initial condition and forcing
`E_{k+1} z − E_k z`). -/
theorem innov_bound {f₁ f₂ f₃ : Matrix ι ι ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖v‖ ≤ C * ‖sysOp f₁ f₂ f₃ v‖) (x : SProcV ι Ω) (hx : AdaptedV 𝔼 (toP x))
    (k : ℕ) (i : ι) (ω : Ω) :
    |toP x (k + 1) i ω - 𝔼.E k (toP x (k + 1) i) ω| ≤ C * (2 * ‖opS 𝔼 f₁ f₂ f₃ x‖) := by
  set B := ‖opS 𝔼 f₁ f₂ f₃ x‖ with hB
  set Φ : (Ω → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj ω).comp (𝔼.E (k + 1) - 𝔼.E k) with hΦ
  have hΦa : ∀ y, Φ y = 𝔼.E (k + 1) y ω - 𝔼.E k y ω := fun y => rfl
  set e : ℕ → ι → ℝ := fun s i => Φ (toP x (k + 1 + s) i) with he
  have heb : LinearSystems.BoundedSeq e := ⟨2 * ‖x‖, fun s i => by
    change |Φ (toP x (k + 1 + s) i)| ≤ 2 * ‖x‖
    rw [hΦa]
    exact abs_innov_le 𝔼 (fun ω' => abs_apply_le x _ ω' i) k ω⟩
  have hknown : ∀ i, 𝔼.E (k + 1) (toP x k i) = toP x k i := fun i => by
    rw [← hx k i, 𝔼.known (Nat.le_succ k)]
  have hlag : ∀ s, lagV 0 e s = fun i => Φ (lagP 0 (toP x) (k + 1 + s) i) := by
    intro s
    cases s with
    | zero =>
      funext i
      change (0 : ι → ℝ) i = Φ (toP x k i)
      rw [hΦa, hknown i, hx k i, sub_self]
      rfl
    | succ s => rfl
  have heta : ∀ s, (fun i => Φ (toP x (k + 1 + s + 1) i -
      𝔼.E (k + 1 + s) (toP x (k + 1 + s + 1) i))) = 0 := by
    intro s
    funext i
    rw [hΦa, map_sub, map_sub, 𝔼.tower (by omega : k + 1 ≤ k + 1 + s),
      𝔼.tower (by omega : k ≤ k + 1 + s)]
    simp
  have hR : ∀ s, ‖f₁ *ᵥ lagV 0 e s + f₂ *ᵥ e s + f₃ *ᵥ e (s + 1)‖ ≤ 2 * B := by
    intro s
    have hid := phi_identity 𝔼 f₁ f₂ f₃ x hx Φ (k + 1 + s)
    rw [heta s, Matrix.mulVec_zero, add_zero] at hid
    rw [hlag s]
    change ‖f₁ *ᵥ (fun i => Φ (lagP 0 (toP x) (k + 1 + s) i)) +
      f₂ *ᵥ (fun i => Φ (toP x (k + 1 + s) i)) +
      f₃ *ᵥ (fun i => Φ (toP x (k + 1 + s + 1) i))‖ ≤ 2 * B
    rw [hid]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
    rw [Real.norm_eq_abs, hΦa]
    exact abs_innov_le 𝔼 (fun ω' => abs_apply_le _ _ ω' i) k ω
  have h0 := pf_bound hC0 hC heb (by positivity) hR 0
  have hcomp : |e 0 i| ≤ ‖e 0‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (e 0) i
  have he0 : e 0 i = toP x (k + 1) i ω - 𝔼.E k (toP x (k + 1) i) ω := by
    change Φ (toP x (k + 1) i) = _
    rw [hΦa, hx (k + 1) i]
  rw [← he0]
  exact hcomp.trans h0

/-- **Linear transfer** (Woodford (2003), App. A.3, pp. 632–634): if the perfect-foresight
operator (A.8) `x ↦ f₁ x_{t−1} + f₂ x_t + f₃ x_{t+1}` is bounded below with constant `C`, then
for **every** expectation system the stochastic operator (A.12) is bounded below on adapted
processes: `‖x‖ ≤ C (1 + 2C‖f₃‖) ‖(A.12) x‖`. (Project on date-`k` forecasts `s ↦ E_k x_s(ω)`;
the forecast errors that appear are bounded by `innov_bound`.) -/
theorem opS_boundedBelow {f₁ f₂ f₃ : Matrix ι ι ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, ‖v‖ ≤ C * ‖sysOp f₁ f₂ f₃ v‖) (x : SProcV ι Ω) (hx : AdaptedV 𝔼 (toP x)) :
    ‖x‖ ≤ C * ((1 + ‖mclm f₃‖ * (2 * C)) * ‖opS 𝔼 f₁ f₂ f₃ x‖) := by
  set B := ‖opS 𝔼 f₁ f₂ f₃ x‖ with hB
  have hB0 : 0 ≤ B := norm_nonneg _
  refine LocalIFTStochastic.norm_le_of_forall (by positivity) fun p => ?_
  obtain ⟨k, ω⟩ := p
  set Φ : (Ω → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj ω).comp (𝔼.E k) with hΦ
  have hΦa : ∀ y, Φ y = 𝔼.E k y ω := fun y => rfl
  set y : ℕ → ι → ℝ := fun s i => Φ (toP x s i) with hy
  have hyb : LinearSystems.BoundedSeq y := ⟨‖x‖, fun s i => by
    change |Φ (toP x s i)| ≤ ‖x‖
    rw [hΦa]
    exact 𝔼.abs_E_le (fun ω' => abs_apply_le x _ ω' i) k ω⟩
  have hlag : ∀ s, lagV 0 y s = fun i => Φ (lagP 0 (toP x) s i) := by
    intro s
    cases s with
    | zero =>
      funext i
      change (0 : ι → ℝ) i = Φ (fun _ => 0)
      rw [hΦa, 𝔼.const]
      rfl
    | succ s => rfl
  have hR : ∀ s, ‖f₁ *ᵥ lagV 0 y s + f₂ *ᵥ y s + f₃ *ᵥ y (s + 1)‖ ≤
      (1 + ‖mclm f₃‖ * (2 * C)) * B := by
    intro s
    rw [hlag s]
    change ‖f₁ *ᵥ (fun i => Φ (lagP 0 (toP x) s i)) + f₂ *ᵥ (fun i => Φ (toP x s i)) +
      f₃ *ᵥ (fun i => Φ (toP x (s + 1) i))‖ ≤ _
    rw [phi_identity 𝔼 f₁ f₂ f₃ x hx Φ s]
    have h1 : ‖(fun i => Φ (toP (opS 𝔼 f₁ f₂ f₃ x) s i) : ι → ℝ)‖ ≤ B :=
      (pi_norm_le_iff_of_nonneg hB0).mpr fun i => by
        rw [Real.norm_eq_abs, hΦa]
        exact 𝔼.abs_E_le (fun ω' => abs_apply_le _ _ ω' i) k ω
    have h2 : ‖(fun i => Φ (toP x (s + 1) i - 𝔼.E s (toP x (s + 1) i)) : ι → ℝ)‖ ≤
        C * (2 * B) := (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => by
      rw [Real.norm_eq_abs, hΦa]
      exact 𝔼.abs_E_le (fun ω' => innov_bound 𝔼 hC0 hC x hx s i ω') k ω
    have h3 : ‖f₃ *ᵥ (fun i => Φ (toP x (s + 1) i - 𝔼.E s (toP x (s + 1) i)))‖ ≤
        ‖mclm f₃‖ * (C * (2 * B)) := by
      rw [← mclm_apply]
      exact ((mclm f₃).le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ B + ‖mclm f₃‖ * (C * (2 * B)) := add_le_add h1 h3
      _ = (1 + ‖mclm f₃‖ * (2 * C)) * B := by ring
  have hk := pf_bound hC0 hC hyb (by positivity) hR k
  have hyk : y k = x (k, ω) := by
    funext i
    change Φ (toP x k i) = _
    rw [hΦa]
    exact congrFun (hx k i) ω
  rw [← hyk]
  exact hk

/-- Woodford (2003), App. A.3, p. 634: **the converse transfer**: on a nonempty state space, if
(A.12) is bounded below on adapted processes, so is (A.8) (embed deterministic paths). -/
theorem sysOp_boundedBelow_of_opS [Nonempty Ω] {f₁ f₂ f₃ : Matrix ι ι ℝ} {C : ℝ}
    (hC : ∀ x : SProcV ι Ω, AdaptedV 𝔼 (toP x) → ‖x‖ ≤ C * ‖opS 𝔼 f₁ f₂ f₃ x‖)
    (v : SeqV ι) : ‖v‖ ≤ C * ‖sysOp f₁ f₂ f₃ v‖ := by
  have hX := hC (embG (ι → ℝ) v) (adaptedV_embG 𝔼 v)
  have he : opS 𝔼 f₁ f₂ f₃ (embG (Ω := Ω) (ι → ℝ) v) = embG (ι → ℝ) (sysOp f₁ f₂ f₃ v) := by
    apply toP_injective
    funext t i ω
    change toP (opS 𝔼 f₁ f₂ f₃ (embG (ι → ℝ) v)) t i ω = sysOp f₁ f₂ f₃ v t i
    rw [toP_opS_of_adapted 𝔼 f₁ f₂ f₃ _ (adaptedV_embG 𝔼 v) t, toP_embG, sysOp_apply]
    have hl : lagP 0 (fun t i (_ : Ω) => v t i) t = fun i _ => lagV 0 (fun s => v s) t i := by
      cases t <;> rfl
    have hE : (fun i => 𝔼.E t (fun (_ : Ω) => v (t + 1) i)) = fun i _ => v (t + 1) i := by
      funext i
      exact 𝔼.const t _
    rw [hl, hE, mv_cst, mv_cst, mv_cst]
    rfl
  rwa [he, norm_embG, norm_embG] at hX

/-- Woodford (2003), App. A.3, pp. 632–634: on a nonempty state space, **(A.12) is bounded below
on adapted processes iff (A.8) is bounded below**. -/
theorem opS_boundedBelow_iff [Nonempty Ω] (f₁ f₂ f₃ : Matrix ι ι ℝ) :
    (∃ C, 0 ≤ C ∧ ∀ x : SProcV ι Ω, AdaptedV 𝔼 (toP x) → ‖x‖ ≤ C * ‖opS 𝔼 f₁ f₂ f₃ x‖) ↔
      BoundedBelow (sysOp f₁ f₂ f₃) := by
  constructor
  · rintro ⟨C, hC0, hC⟩
    exact ⟨C, hC0, sysOp_boundedBelow_of_opS 𝔼 hC⟩
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C * (1 + ‖mclm f₃‖ * (2 * C)), by positivity, fun x hx => ?_⟩
    rw [mul_assoc]
    exact opS_boundedBelow 𝔼 hC0 hC x hx

/-! ### Nonlinear local uniqueness when (A.8) is bounded below -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local uniqueness without surjectivity** (Woodford (2003), App. A.3, pp. 632–634): if `G` is
`C¹` near the steady state and the operator (A.8) of its linearisation is bounded below
(one-to-one with closed range, `boundedBelow_iff`; it need **not** be onto), then for every
expectation system there is `ε > 0` such that for every initial condition and disturbance
process with `‖(x_{−1}, e)‖ < ε` the conditions `E_t[G(x_{t−1}, x_t, x_{t+1}, e_t)] = 0` have
**at most one** bounded adapted solution within `ε` of the steady state. -/
theorem unique_of_boundedBelow {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0)
    (hbb : BoundedBelow (linOp G)) :
    ∃ ε > 0, ∀ (u : ParS ι E Ω) (x y : SProcV ι Ω), ‖u‖ < ε → ‖x‖ < ε → ‖y‖ < ε →
      SolvesSV 𝔼 G u x → SolvesSV 𝔼 G u y → x = y := by
  obtain ⟨r, hr, hball⟩ := exists_ball_contDiffAt hG
  set F := cutoff G r hr with hFdef
  have hF1 : ContDiff ℝ 1 F := contDiff_cutoff hr hball
  obtain ⟨hlo, -, -⟩ := lin_cutoff G hr
  obtain ⟨C, hC0, hC⟩ := hbb
  have hCF : ∀ v, ‖v‖ ≤ C * ‖sysOp (M1 F) (M2 F) (M3 F) v‖ := by
    intro v
    have h := hC v
    rw [← hlo] at h
    exact h
  set K := C * (1 + ‖mclm (M3 F)‖ * (2 * C)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hstrict := hasStrictFDerivAt_eqMapS 𝔼 hF1 0
  rw [eqDS_zero 𝔼 hF1] at hstrict
  have hlit := (hasStrictFDerivAt_iff_isLittleO.mp hstrict).def
    (by positivity : (0 : ℝ) < 1 / (2 * (K + 1)))
  obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff.mp hlit
  refine ⟨min ρ (r / 4), lt_min hρ (by positivity), fun u x y hu hx hy hsx hsy => ?_⟩
  have hu4 : ‖u‖ ≤ r / 4 := (hu.trans_le (min_le_right _ _)).le
  have hx4 : ‖x‖ ≤ r / 4 := (hx.trans_le (min_le_right _ _)).le
  have hy4 : ‖y‖ ≤ r / 4 := (hy.trans_le (min_le_right _ _)).le
  have hzx : eqMapS 𝔼 F hF1.continuous (u, x) = 0 :=
    (eqMapS_eq_zero_iff 𝔼 F hF1.continuous u x).mpr
      ((solvesSV_cutoff_iff 𝔼 hr hu4 hx4).mpr hsx)
  have hzy : eqMapS 𝔼 F hF1.continuous (u, y) = 0 :=
    (eqMapS_eq_zero_iff 𝔼 F hF1.continuous u y).mpr
      ((solvesSV_cutoff_iff 𝔼 hr hu4 hy4).mpr hsy)
  have hd : dist (((u, x), (u, y)) : (ParS ι E Ω × SProcV ι Ω) × (ParS ι E Ω × SProcV ι Ω))
      (0, 0) < ρ := by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right, Prod.norm_def, Prod.norm_def]
    have h1 : ‖u‖ < ρ := hu.trans_le (min_le_left _ _)
    have h2 : ‖x‖ < ρ := hx.trans_le (min_le_left _ _)
    have h3 : ‖y‖ < ρ := hy.trans_le (min_le_left _ _)
    exact max_lt (max_lt h1 h2) (max_lt h1 h3)
  have hest := hρP hd
  simp only [hzx, hzy, sub_zero, zero_sub, norm_neg] at hest
  have hdiff : ((u, x) : ParS ι E Ω × SProcV ι Ω) - (u, y) = (0, x - y) := by
    rw [Prod.mk_sub_mk, sub_self]
  rw [hdiff] at hest
  have hD : eqD0S 𝔼 F ((0 : ParS ι E Ω), x - y) = linOpS 𝔼 F (x - y) := by
    simp [eqD0S]
  rw [hD, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at hest
  have had : AdaptedV 𝔼 (toP (x - y)) := by
    intro t i
    rw [toP_sub]
    change 𝔼.E t (toP x t i - toP y t i) = toP x t i - toP y t i
    rw [map_sub, hsx.1 t i, hsy.1 t i]
  have htr := opS_boundedBelow 𝔼 hC0 hCF (x - y) had
  change ‖x - y‖ ≤ C * ((1 + ‖mclm (M3 F)‖ * (2 * C)) * ‖linOpS 𝔼 F (x - y)‖) at htr
  rw [← mul_assoc, ← hK] at htr
  have hK1 : K * (1 / (2 * (K + 1))) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hle : ‖x - y‖ ≤ 1 / 2 * ‖x - y‖ := by
    calc ‖x - y‖ ≤ K * ‖linOpS 𝔼 F (x - y)‖ := htr
      _ ≤ K * (1 / (2 * (K + 1)) * ‖x - y‖) := mul_le_mul_of_nonneg_left hest hK0
      _ = (K * (1 / (2 * (K + 1)))) * ‖x - y‖ := by ring
      _ ≤ 1 / 2 * ‖x - y‖ := mul_le_mul_of_nonneg_right hK1 (norm_nonneg _)
  have h0 : ‖x - y‖ = 0 := by linarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- **No sunspots when (A.8) is bounded below** (Woodford (2003), App. A.3, pp. 632–634): under
the hypotheses of `unique_of_boundedBelow` and `G(0) = 0`, for every expectation system the
steady state is the only bounded adapted equilibrium within `ε` of it when `x_{−1} = x̄` and
there are no disturbances — no sunspot equilibria, random or deterministic. -/
theorem no_sunspot_of_boundedBelow {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0)
    (h0 : G 0 = 0) (hbb : BoundedBelow (linOp G)) :
    ∃ ε > 0, ∀ x : SProcV ι Ω, ‖x‖ < ε → SolvesSV 𝔼 G 0 x → x = 0 := by
  obtain ⟨ε, hε, h⟩ := unique_of_boundedBelow 𝔼 hG hbb
  exact ⟨ε, hε, fun x hx hs => h 0 x 0 (by rwa [norm_zero]) hx (by rwa [norm_zero]) hs
    (solvesSV_zero 𝔼 h0)⟩

/-- **When (A.8) is onto, the linearisation decides the sunspot question exactly** (Woodford
(2003), App. A.3, pp. 632–634): for `G` `C¹` near the steady state with `G(0) = 0` and (A.8)
onto, the exact model has bounded adapted equilibria on the core coin tree at every scale whose
date-1 value differs across the first flip **iff** (A.8) is not one-to-one. -/
theorem sunspot_iff_of_surjective {G : Arg ι E → (ι → ℝ)} (hG : ContDiffAt ℝ 1 G 0)
    (h0 : G 0 = 0) (hs : Function.Surjective (linOp G)) :
    (∀ ε > 0, ∃ x : SProcV ι (Bool × Bool),
      SolvesSV ExpectationsFiniteTree.coinSystem G 0 x ∧ ‖x‖ ≤ ε ∧
        x (1, (true, true)) ≠ x (1, (false, true))) ↔ ¬ Function.Injective (linOp G) := by
  constructor
  · intro hsun hinj
    have hU : IsUnit (linOp G) := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hs⟩
    obtain ⟨ε, hε, hno⟩ := no_sunspot_of_boundedBelow ExpectationsFiniteTree.coinSystem hG h0
      (boundedBelow_of_isUnit hU)
    obtain ⟨x, hx, hxn, hxr⟩ := hsun (ε / 2) (by positivity)
    have h := hno x (by linarith) hx
    rw [h] at hxr
    exact hxr rfl
  · intro hni ε hε
    obtain ⟨x, hx, hxn, -, hxr⟩ :=
      LocalIFTSystemsStochasticSunspots.random_sunspot_nonlinear hG h0 hs hni hε
    exact ⟨x, hx, hxn, hxr⟩

end Woodford.PriceLevelDetermination.SunspotsBoundedBelow
