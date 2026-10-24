/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.GeneralSetup
import OptimalPolicyRules.ExpectationTools
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Lagrangian, first-order conditions and their sufficiency

Woodford (2003), *Interest and Prices*, Chapter 8, Sections 1.1 and 1.4 (pp. 540–553), with
footnote 8 (p. 542).

## Main results

* `lagrangian_gap`: Lagrangian sufficiency for the general LQ problem with linear expectational
  constraints, under an arbitrary `ExpectationSystem` with the pull-out property. If a bounded
  plan `y*` and bounded multipliers `φ` (with `M_t` known at `t`) satisfy the constraints (1.1)
  and the FOC (1.9), then for every other bounded feasible plan `y` with the same initial
  multiplier term, `J(y) − J(y*) = ∑ β^k E_{t₀} ½ (T d)' W (T d)` (exactly), `d = y − y*`.
* `optimalSubjectTo_of_focSystem`, `t0Optimal_of_focSystem`: (1.9) with (1.6), resp. (1.8),
  characterises timeless, resp. `t₀`-optimal plans (p. 541); `…_perfectForesight` are the
  deterministic versions.
* `targets_eq_of_optimal`: uniqueness of the optimal target path (strict convexity, `W ≻ 0`).
* `foc_iff_split`: the split of (1.9) into (1.18) and (1.19) (p. 552).
* `Assumption81`, `affine_comb_focSystem`, `eq110_separable`, `eq110_additive`,
  `eq110_homogeneous`: Assumption 8.1 and the affine structure (1.10) of the implied
  `Ẽ z_{t₀}`.
* `restated_timeless`, `timeless_restated`: the equivalence of the Definition (1.5)–(1.6) with
  the restatement (1.11)–(1.12) via initial multipliers under Assumption 8.1 (the direction that
  needs the necessity of the FOC is proved under an explicit attainability hypothesis).
* `pencil_det_pairing`, `pencil_root_pairing`: fn 8 — roots of the FOC system pair as
  `μ ↔ (βμ)⁻¹`, as a determinant identity.
* `fn8_counterexample`: the "exactly half of the roots have modulus less than `β^{-1/2}`" claim
  needs no root on `|μ| = β^{-1/2}` (survey E19).
* `exists_conj_closed_sub`, `card_even_of_conj_closed_nonreal`, `exists_almost_conj_closed_sub`:
  the combinatorial selection claim of p. 552 (Assumption 8.2).
-/

namespace Woodford.OptimalPolicyRules.GeneralFOC

open Matrix Filter Topology GeneralSetup
open ExpectationTools (Faithful)

variable {Ω : Type*}

/-! ### Elementary bounds -/

/-- Woodford (2003), fn 6, p. 539 (bounded plans): a constant matrix maps uniformly bounded
vectors to uniformly bounded vectors. -/
theorem exists_bound_mulVec {κ ι : Type*} [Finite κ] [Fintype ι] (A : Matrix κ ι ℝ) (M : ℝ) :
    ∃ K, ∀ v : ι → ℝ, (∀ i, |v i| ≤ M) → ∀ a, |(A *ᵥ v) a| ≤ K := by
  cases nonempty_fintype κ
  refine ⟨(∑ a, ∑ i, |A a i|) * max M 0, fun v hv a => ?_⟩
  have hrow : ∑ i, |A a i| ≤ ∑ a, ∑ i, |A a i| :=
    Finset.single_le_sum (f := fun a => ∑ i, |A a i|)
      (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ a)
  calc |(A *ᵥ v) a| = |∑ i, A a i * v i| := rfl
    _ ≤ ∑ i, |A a i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |A a i| * max M 0 := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((hv i).trans (le_max_left _ _)) (abs_nonneg _)
    _ = (∑ i, |A a i|) * max M 0 := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow (le_max_right _ _)

/-- Woodford (2003), fn 6, p. 539 (bounded plans): a bound for a dot product. -/
theorem abs_dotProduct_le {ι : Type*} [Fintype ι] {u w : ι → ℝ} {Mu Mw : ℝ}
    (hu : ∀ i, |u i| ≤ Mu) (hw : ∀ i, |w i| ≤ Mw) :
    |u ⬝ᵥ w| ≤ Fintype.card ι * (Mu * Mw) := by
  calc |u ⬝ᵥ w| = |∑ i, u i * w i| := rfl
    _ ≤ ∑ i, |u i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, Mu * Mw := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hu i) (hw i) (abs_nonneg _) ((abs_nonneg _).trans (hu i))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-! ### The loss and the objective in abstract form -/

variable {ρ₁ ρ₂ ν ιτ : Type*}

/-- Woodford (2003), eq. (1.3), p. 537: the quadratic form `½ w' W w`. -/
noncomputable def quad [Fintype ιτ] (W : Matrix ιτ ιτ ℝ) (w : ιτ → ℝ) : ℝ :=
  (1 / 2) * (w ⬝ᵥ (W *ᵥ w))

/-- Woodford (2003), eqs. (1.3)–(1.4), p. 537: the period loss `½ (Tv − τ*)' W (Tv − τ*)`. -/
noncomputable def lossFn [Fintype ιτ] [Fintype ν] (Tm : Matrix ιτ ν ℝ) (W : Matrix ιτ ιτ ℝ)
    (τs : ιτ → ℝ) (v : ν → ℝ) : ℝ :=
  quad W (Tm *ᵥ v - τs)

/-- Woodford (2003), eq. (1.2), p. 537: the discounted expected loss
`E_{t₀} ∑_{k} β^k L(y_{t₀+k})`. -/
noncomputable def Jfn [Fintype ιτ] [Fintype ν] (𝔼 : ExpectationSystem Ω) (β : ℝ)
    (Tm : Matrix ιτ ν ℝ) (W : Matrix ιτ ιτ ℝ) (τs : ιτ → ℝ) (t0 : ℕ) (y : ℕ → Ω → ν → ℝ) :
    Ω → ℝ :=
  𝔼.E t0 (fun ω => ∑' k, β ^ k * lossFn Tm W τs (y (t0 + k) ω))

/-- Woodford (2003), (1.3): the period loss of bounded vectors is bounded. -/
theorem exists_bound_lossFn [Fintype ιτ] [Fintype ν] (Tm : Matrix ιτ ν ℝ)
    (W : Matrix ιτ ιτ ℝ) (τs : ιτ → ℝ) (M : ℝ) :
    ∃ K, ∀ v : ν → ℝ, (∀ i, |v i| ≤ M) → |lossFn Tm W τs v| ≤ K := by
  obtain ⟨K1, hK1⟩ := exists_bound_mulVec Tm M
  obtain ⟨K3, hK3⟩ := exists_bound_mulVec W (K1 + ∑ b, |τs b|)
  refine ⟨(1 / 2) * (Fintype.card ιτ * ((K1 + ∑ b, |τs b|) * K3)), fun v hv => ?_⟩
  have hw : ∀ a, |(Tm *ᵥ v - τs) a| ≤ K1 + ∑ b, |τs b| := fun a => by
    have h1 := hK1 v hv a
    have h2 : |τs a| ≤ ∑ b, |τs b| :=
      Finset.single_le_sum (f := fun b => |τs b|) (fun b _ => abs_nonneg _) (Finset.mem_univ a)
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hd := abs_dotProduct_le hw (hK3 _ hw)
  unfold lossFn quad
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left hd (by norm_num)

/-! ### First-order conditions (1.9) -/

/-- Woodford (2003), eq. (1.9), p. 541: the first-order conditions
`Ã' E_t φ_{t+1} + T' W (τ_t − τ*) − β⁻¹ Ĩ' φ_t = 0` for all `t ≥ t₀`. -/
def FOC [Fintype ιτ] [Fintype ν] [Fintype ρ₁] [Fintype ρ₂] (𝔼 : ExpectationSystem Ω)
    (Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ) (Tm : Matrix ιτ ν ℝ) (W : Matrix ιτ ιτ ℝ) (τs : ιτ → ℝ)
    (β : ℝ) (t0 : ℕ) (y : ℕ → Ω → ν → ℝ) (φ : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ) : Prop :=
  ∀ t, t0 ≤ t → ∀ ω, Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω + Tmᵀ *ᵥ (W *ᵥ (Tm *ᵥ y t ω - τs)) -
    β⁻¹ • (Itilᵀ *ᵥ φ t ω) = 0

/-- Woodford (2003), p. 540: the multipliers `M_t` on the expectational constraints (the
`ρ₂`-block of `φ_{t+1}`) are measurable with respect to date-`t` information. -/
def MultiplierMeas (𝔼 : ExpectationSystem Ω) (φ : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ) : Prop :=
  ∀ t r, 𝔼.E t (fun ω => φ (t + 1) ω (Sum.inr r)) = fun ω => φ (t + 1) ω (Sum.inr r)

/-- Woodford (2003), eq. (1.7), p. 540: the date-`t` term of the Lagrangian,
`L(y_t) + p' Ã y_t − β⁻¹ q' Ĩ y_t`, with `p = E_t φ_{t+1}` and `q = φ_t`. -/
noncomputable def periodLagrangian [Fintype ιτ] [Fintype ν] [Fintype ρ₁] [Fintype ρ₂]
    (Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ) (Tm : Matrix ιτ ν ℝ) (W : Matrix ιτ ιτ ℝ) (τs : ιτ → ℝ)
    (β : ℝ) (p q : ρ₁ ⊕ ρ₂ → ℝ) (v : ν → ℝ) : ℝ :=
  lossFn Tm W τs v + p ⬝ᵥ (Atil *ᵥ v) - β⁻¹ * (q ⬝ᵥ (Itil *ᵥ v))

/-- Woodford (2003), eq. (1.7), p. 540: the Lagrangian
`E_{t₀} ∑_{k} β^k [L(y_t) + φ_{t+1}' Ã y_t − β⁻¹ φ_t' Ĩ y_t]`, `t = t₀ + k`. -/
noncomputable def lagrangian [Fintype ιτ] [Fintype ν] [Fintype ρ₁] [Fintype ρ₂]
    (𝔼 : ExpectationSystem Ω) (Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ) (Tm : Matrix ιτ ν ℝ)
    (W : Matrix ιτ ιτ ℝ) (τs : ιτ → ℝ) (β : ℝ) (t0 : ℕ) (y : ℕ → Ω → ν → ℝ)
    (φ : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ) : Ω → ℝ :=
  𝔼.E t0 (fun ω => ∑' k, β ^ k *
    periodLagrangian Atil Itil Tm W τs β (φ (t0 + k + 1) ω) (φ (t0 + k) ω) (y (t0 + k) ω))

/-- Woodford (2003), p. 553: `(A' x) · d = x · (A d)`. -/
theorem transpose_mulVec_dot {κ ι : Type*} [Fintype κ] [Fintype ι] (A : Matrix κ ι ℝ)
    (x : κ → ℝ) (d : ι → ℝ) : (Aᵀ *ᵥ x) ⬝ᵥ d = x ⬝ᵥ (A *ᵥ d) := by
  rw [mulVec_transpose, dotProduct_mulVec]

/-- Woodford (2003), eq. (1.3): exact second-order expansion of the period loss,
`L(v + h) = L(v) + [T' W (T v − τ*)]' h + ½ (T h)' W (T h)` (`W` symmetric). -/
theorem lossFn_add [Fintype ιτ] [Fintype ν] (Tm : Matrix ιτ ν ℝ) {W : Matrix ιτ ιτ ℝ}
    (hW : Wᵀ = W) (τs : ιτ → ℝ) (v h : ν → ℝ) :
    lossFn Tm W τs (v + h) =
      lossFn Tm W τs v + (Tmᵀ *ᵥ (W *ᵥ (Tm *ᵥ v - τs))) ⬝ᵥ h + quad W (Tm *ᵥ h) := by
  unfold lossFn quad
  set u := Tm *ᵥ v - τs with hu
  set w := Tm *ᵥ h with hw
  have h1 : Tm *ᵥ (v + h) - τs = u + w := by
    rw [mulVec_add, hu, hw]
    abel
  have hsym : u ⬝ᵥ (W *ᵥ w) = w ⬝ᵥ (W *ᵥ u) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]
  have h2 : (Tmᵀ *ᵥ (W *ᵥ u)) ⬝ᵥ h = w ⬝ᵥ (W *ᵥ u) := by
    rw [transpose_mulVec_dot, dotProduct_comm]
  rw [h1, h2, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym]
  ring

/-- Woodford (2003), eqs. (1.7) and (1.9), pp. 540–541: (1.9) is the first-order condition of
the Lagrangian — exactly, the period Lagrangian satisfies
`ℒ(v + h) = ℒ(v) + g' h + ½ (T h)' W (T h)` with `g` the left side of (1.9). -/
theorem periodLagrangian_add [Fintype ιτ] [Fintype ν] [Fintype ρ₁] [Fintype ρ₂]
    (Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ) (Tm : Matrix ιτ ν ℝ) {W : Matrix ιτ ιτ ℝ}
    (hW : Wᵀ = W) (τs : ιτ → ℝ) (β : ℝ) (p q : ρ₁ ⊕ ρ₂ → ℝ) (v h : ν → ℝ) :
    periodLagrangian Atil Itil Tm W τs β p q (v + h) =
      periodLagrangian Atil Itil Tm W τs β p q v +
        (Atilᵀ *ᵥ p + Tmᵀ *ᵥ (W *ᵥ (Tm *ᵥ v - τs)) - β⁻¹ • (Itilᵀ *ᵥ q)) ⬝ᵥ h +
        quad W (Tm *ᵥ h) := by
  unfold periodLagrangian
  rw [lossFn_add Tm hW, sub_dotProduct, add_dotProduct, smul_dotProduct, mulVec_add, mulVec_add,
    dotProduct_add, dotProduct_add, smul_eq_mul]
  simp only [transpose_mulVec_dot]
  ring

/-- Woodford (2003), (1.9): at a point where the FOC holds, the loss difference is the
quadratic term plus multiplier terms,
`L(y) − L(y*) = ½ (T d)' W (T d) + β⁻¹ q' Ĩ d − p' Ã d`, `d = y − y*`. -/
theorem lossFn_sub_of_foc [Fintype ιτ] [Fintype ν] [Fintype ρ₁] [Fintype ρ₂]
    {Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ} {Tm : Matrix ιτ ν ℝ} {W : Matrix ιτ ιτ ℝ}
    (hW : Wᵀ = W) {τs : ιτ → ℝ} {β : ℝ} {p q : ρ₁ ⊕ ρ₂ → ℝ} {ys : ν → ℝ}
    (hfoc : Atilᵀ *ᵥ p + Tmᵀ *ᵥ (W *ᵥ (Tm *ᵥ ys - τs)) - β⁻¹ • (Itilᵀ *ᵥ q) = 0)
    (y : ν → ℝ) :
    lossFn Tm W τs y - lossFn Tm W τs ys =
      quad W (Tm *ᵥ (y - ys)) + β⁻¹ * (q ⬝ᵥ (Itil *ᵥ (y - ys))) - p ⬝ᵥ (Atil *ᵥ (y - ys)) := by
  have hg : Tmᵀ *ᵥ (W *ᵥ (Tm *ᵥ ys - τs)) = β⁻¹ • (Itilᵀ *ᵥ q) - Atilᵀ *ᵥ p := by
    rw [← sub_eq_zero, ← hfoc]
    abel
  have hy : y = ys + (y - ys) := by abel
  conv_lhs => rw [hy, lossFn_add Tm hW, hg]
  rw [sub_dotProduct, smul_dotProduct, transpose_mulVec_dot, transpose_mulVec_dot, smul_eq_mul]
  ring

/-! ### Lagrangian sufficiency -/

/-- Woodford (2003), p. 541 (the transversality condition is automatic for bounded plans):
summation by parts, `∑_k β^k (β⁻¹ e_k − e_{k+1}) = β⁻¹ e_0` for bounded `e`, `0 < β < 1`. -/
theorem hasSum_telescope {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {e : ℕ → ℝ} {M : ℝ}
    (he : ∀ k, |e k| ≤ M) :
    HasSum (fun k => β ^ k * (β⁻¹ * e k - e (k + 1))) (β⁻¹ * e 0) := by
  have hsum : Summable (fun k => β ^ k * (β⁻¹ * e k - e (k + 1))) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right (β⁻¹ * M + M)) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_pos hβ0 k).le
    calc |β⁻¹ * e k - e (k + 1)| ≤ |β⁻¹ * e k| + |e (k + 1)| := abs_sub _ _
      _ ≤ β⁻¹ * M + M := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hβ0)]
        exact add_le_add (mul_le_mul_of_nonneg_left (he k) (inv_pos.mpr hβ0).le) (he (k + 1))
  rw [hsum.hasSum_iff_tendsto_nat]
  set g : ℕ → ℝ := fun k => β ^ k * β⁻¹ * e k with hg
  have hpart : ∀ n, ∑ i ∈ Finset.range n, β ^ i * (β⁻¹ * e i - e (i + 1)) = g 0 - g n := by
    intro n
    rw [← Finset.sum_range_sub' g n]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg, pow_succ]
    field_simp
  simp_rw [hpart]
  have hg0 : g 0 = β⁻¹ * e 0 := by simp [hg]
  rw [hg0]
  have hgn : Tendsto g atTop (𝓝 0) := by
    have hb : Tendsto (fun n : ℕ => β ^ n * (β⁻¹ * |M|)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (β⁻¹ * |M|)
    refine squeeze_zero_norm (fun n => ?_) hb
    rw [Real.norm_eq_abs, hg]
    simp only
    rw [abs_mul, abs_mul, abs_of_pos (pow_pos hβ0 n), abs_of_pos (inv_pos.mpr hβ0), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ((he n).trans (le_abs_self M)) (inv_pos.mpr hβ0).le)
      (pow_pos hβ0 n).le
  simpa using (tendsto_const_nhds (x := β⁻¹ * e 0)).sub hgn

/-- Woodford (2003), p. 540: the conditional-expectation step of the sufficiency argument. For
two plans satisfying the same constraints (1.1), with `d = y − y*` and `M_t` known at `t`,
`E_t [φ_{t+1}' Ĩ d_{t+1}] = (E_t φ_{t+1})' Ã d_t` (pull-out and the law of iterated
expectations). -/
theorem E_next_multiplier_term [Fintype ν] [Fintype ρ₁] [Fintype ρ₂]
    {𝔼 : ExpectationSystem Ω} (hpull : 𝔼.PullOut) {Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ}
    {cf : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ} {t0 : ℕ} {y ys : ℕ → Ω → ν → ℝ}
    (hy : ConstraintsHold 𝔼 Atil Itil cf t0 y) (hys : ConstraintsHold 𝔼 Atil Itil cf t0 ys)
    (hay : AdaptedV 𝔼 y) (hays : AdaptedV 𝔼 ys) {φ : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ}
    (hmφ : MultiplierMeas 𝔼 φ) {t : ℕ} (ht : t0 ≤ t) :
    𝔼.E t (fun ω => φ (t + 1) ω ⬝ᵥ (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω))) =
      fun ω => EV 𝔼 t (φ (t + 1)) ω ⬝ᵥ (Atil *ᵥ (y t ω - ys t ω)) := by
  -- the date-`t` vector `Ã d_t` is known at `t`
  have hAd : ∀ r, 𝔼.E t (fun ω => (Atil *ᵥ (y t ω - ys t ω)) r) =
      fun ω => (Atil *ᵥ (y t ω - ys t ω)) r := by
    intro r
    have h := E_sum_mul 𝔼 t (Atil r) (fun i ω => y t ω i - ys t ω i)
    have hE : ∀ i, 𝔼.E t (fun ω => y t ω i - ys t ω i) = fun ω => y t ω i - ys t ω i := by
      intro i
      have : (fun ω => y t ω i - ys t ω i) = (fun ω => y t ω i) - fun ω => ys t ω i := rfl
      rw [this, map_sub, hay t i, hays t i]
    simp only [hE] at h
    simpa [mulVec, dotProduct] using h
  -- the `ρ₁` rows hold exactly
  have hD1 : ∀ r ω, (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) (Sum.inl r) =
      (Atil *ᵥ (y t ω - ys t ω)) (Sum.inl r) := by
    intro r ω
    have h1 := (hy t ht ω).1 r
    have h2 := (hys t ht ω).1 r
    simp only [mulVec_sub, Pi.sub_apply]
    linarith
  -- the `ρ₂` rows hold in conditional expectation
  have hD2 : ∀ r, 𝔼.E t (fun ω => (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) (Sum.inr r)) =
      fun ω => (Atil *ᵥ (y t ω - ys t ω)) (Sum.inr r) := by
    intro r
    funext ω
    have h1 := (hy t ht ω).2 r
    have h2 := (hys t ht ω).2 r
    have hsplit : (fun ω => (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) (Sum.inr r)) =
        (fun ω => (Itil *ᵥ y (t + 1) ω) (Sum.inr r)) -
          fun ω => (Itil *ᵥ ys (t + 1) ω) (Sum.inr r) := by
      funext ω
      simp [mulVec_sub]
    rw [hsplit, map_sub]
    simp only [EV] at h1 h2
    simp only [Pi.sub_apply, mulVec_sub]
    linarith
  -- assemble
  have hsum : (fun ω => φ (t + 1) ω ⬝ᵥ (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω))) =
      ∑ r : ρ₁ ⊕ ρ₂, fun ω => φ (t + 1) ω r * (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) r := by
    funext ω
    simp [dotProduct, Finset.sum_apply]
  have hl : ∀ r, 𝔼.E t (fun ω => φ (t + 1) ω (Sum.inl r) *
      (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) (Sum.inl r)) =
      fun ω => 𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inl r)) ω *
        (Atil *ᵥ (y t ω - ys t ω)) (Sum.inl r) := by
    intro r
    have hfun : (fun ω => φ (t + 1) ω (Sum.inl r) *
        (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) (Sum.inl r)) =
        (fun ω => (Atil *ᵥ (y t ω - ys t ω)) (Sum.inl r)) *
          fun ω => φ (t + 1) ω (Sum.inl r) := by
      funext ω
      simp only [Pi.mul_apply, hD1, mul_comm]
    rw [hfun, hpull t _ _ (hAd _)]
    funext ω
    simp [mul_comm]
  have hr : ∀ r, 𝔼.E t (fun ω => φ (t + 1) ω (Sum.inr r) *
      (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) (Sum.inr r)) =
      fun ω => 𝔼.E t (fun ω' => φ (t + 1) ω' (Sum.inr r)) ω *
        (Atil *ᵥ (y t ω - ys t ω)) (Sum.inr r) := by
    intro r
    have hfun : (fun ω => φ (t + 1) ω (Sum.inr r) *
        (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) (Sum.inr r)) =
        (fun ω => φ (t + 1) ω (Sum.inr r)) *
          fun ω => (Itil *ᵥ (y (t + 1) ω - ys (t + 1) ω)) (Sum.inr r) := rfl
    rw [hfun, hpull t _ _ (hmφ t r), hD2, hmφ t r]
    rfl
  rw [hsum, map_sum, Fintype.sum_sum_type]
  simp only [hl, hr]
  funext ω
  simp [Finset.sum_apply, dotProduct, Fintype.sum_sum_type, EV]

/-- Woodford (2003), p. 541 and survey §4.4: **Lagrangian sufficiency, exact form.** Let `y*`
and multipliers `φ` be bounded, with `M_t` known at `t`, `y*` satisfying the constraints (1.1)
and the FOC (1.9) for `t ≥ t₀`. Let `y` be any bounded adapted plan satisfying the same
constraints, with the same initial multiplier term `φ_{t₀}' Ĩ (y_{t₀} − y*_{t₀}) = 0`. Then,
under any expectation system with the pull-out property,
`J(y) − J(y*) = ∑_k β^k E_{t₀} ½ (T d_{t₀+k})' W (T d_{t₀+k})`, `d = y − y*` (`W` symmetric). -/
theorem lagrangian_gap [Fintype ιτ] [Fintype ν] [Fintype ρ₁] [Fintype ρ₂]
    {𝔼 : ExpectationSystem Ω} (hpull : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ} {Tm : Matrix ιτ ν ℝ} {W : Matrix ιτ ιτ ℝ} (hW : Wᵀ = W)
    {τs : ιτ → ℝ} {cf : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ} {t0 : ℕ} {y ys : ℕ → Ω → ν → ℝ}
    {φ : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ}
    (hy : ConstraintsHold 𝔼 Atil Itil cf t0 y) (hys : ConstraintsHold 𝔼 Atil Itil cf t0 ys)
    (hay : AdaptedV 𝔼 y) (hays : AdaptedV 𝔼 ys) (hby : BoundedV y) (hbys : BoundedV ys)
    (hbφ : BoundedV φ) (hmφ : MultiplierMeas 𝔼 φ) (hfoc : FOC 𝔼 Atil Itil Tm W τs β t0 ys φ)
    (hinit : ∀ ω, φ t0 ω ⬝ᵥ (Itil *ᵥ (y t0 ω - ys t0 ω)) = 0) (ω : Ω) :
    HasSum (fun k => β ^ k *
        𝔼.E t0 (fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω)
      (Jfn 𝔼 β Tm W τs t0 y ω - Jfn 𝔼 β Tm W τs t0 ys ω) := by
  obtain ⟨My, hMy⟩ := hby
  obtain ⟨Mys, hMys⟩ := hbys
  obtain ⟨Mφ, hMφ⟩ := hbφ
  obtain ⟨Ky, hKy⟩ := exists_bound_lossFn Tm W τs My
  obtain ⟨Kys, hKys⟩ := exists_bound_lossFn Tm W τs Mys
  -- `J` as a series of expectations
  have hJ : ∀ (z : ℕ → Ω → ν → ℝ) (K : ℝ), (∀ t ω, |lossFn Tm W τs (z t ω)| ≤ K) →
      HasSum (fun k => β ^ k * 𝔼.E t0 (fun ω' => lossFn Tm W τs (z (t0 + k) ω')) ω)
        (Jfn 𝔼 β Tm W τs t0 z ω) := by
    intro z K hK
    have hb : ∀ k ω', |β ^ k * lossFn Tm W τs (z (t0 + k) ω')| ≤ β ^ k * K := fun k ω' => by
      rw [abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (hK _ _) (pow_pos hβ0 k).le
    have hEt := 𝔼.E_tsum hβ0.le hβ1 hb t0 ω
    have hterm : ∀ k, 𝔼.E t0 (fun ω' => β ^ k * lossFn Tm W τs (z (t0 + k) ω')) ω =
        β ^ k * 𝔼.E t0 (fun ω' => lossFn Tm W τs (z (t0 + k) ω')) ω := by
      intro k
      have : (fun ω' => β ^ k * lossFn Tm W τs (z (t0 + k) ω')) =
          β ^ k • fun ω' => lossFn Tm W τs (z (t0 + k) ω') := rfl
      rw [this, map_smul]
      rfl
    have hsumm : Summable (fun k => β ^ k *
        𝔼.E t0 (fun ω' => lossFn Tm W τs (z (t0 + k) ω')) ω) := by
      refine Summable.of_norm_bounded
        ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right K) (fun k => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hβ0 k)]
      exact mul_le_mul_of_nonneg_left (𝔼.abs_E_le (fun ω' => hK _ ω') t0 ω) (pow_pos hβ0 k).le
    unfold Jfn
    rw [hEt]
    simp_rw [hterm]
    exact hsumm.hasSum
  have hJy := hJ y Ky (fun t ω' => hKy _ (hMy t ω'))
  have hJys := hJ ys Kys (fun t ω' => hKys _ (hMys t ω'))
  -- the multiplier terms `a_s = φ_s' Ĩ d_s` and their expectations `e_s`
  set a : ℕ → Ω → ℝ := fun s ω' => φ s ω' ⬝ᵥ (Itil *ᵥ (y s ω' - ys s ω')) with ha
  set e : ℕ → ℝ := fun s => 𝔼.E t0 (a s) ω with he
  obtain ⟨KI, hKI⟩ := exists_bound_mulVec Itil (My + Mys)
  have hab : ∀ s ω', |a s ω'| ≤ Fintype.card (ρ₁ ⊕ ρ₂) * (Mφ * KI) := by
    intro s ω'
    have hd : ∀ i, |(y s ω' - ys s ω') i| ≤ My + Mys := fun i =>
      (abs_sub _ _).trans (add_le_add (hMy s ω' i) (hMys s ω' i))
    exact abs_dotProduct_le (hMφ s ω') (hKI _ hd)
  have heb : ∀ k, |e (t0 + k)| ≤ Fintype.card (ρ₁ ⊕ ρ₂) * (Mφ * KI) := fun k =>
    𝔼.abs_E_le (hab (t0 + k)) t0 ω
  have he0 : e t0 = 0 := by
    have : a t0 = 0 := by
      funext ω'
      exact hinit ω'
    simp only [he, this, map_zero, Pi.zero_apply]
  -- the per-period identity
  have hkey : ∀ k, β ^ k * 𝔼.E t0 (fun ω' => lossFn Tm W τs (y (t0 + k) ω')) ω -
      β ^ k * 𝔼.E t0 (fun ω' => lossFn Tm W τs (ys (t0 + k) ω')) ω -
      β ^ k * (β⁻¹ * e (t0 + k) - e (t0 + (k + 1))) =
      β ^ k * 𝔼.E t0 (fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω := by
    intro k
    have ht : t0 ≤ t0 + k := Nat.le_add_right _ _
    have hpt : (fun ω' => lossFn Tm W τs (y (t0 + k) ω')) =
        (fun ω' => lossFn Tm W τs (ys (t0 + k) ω')) +
          (fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) + β⁻¹ • a (t0 + k) -
          fun ω' => EV 𝔼 (t0 + k) (φ (t0 + k + 1)) ω' ⬝ᵥ
            (Atil *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω')) := by
      funext ω'
      have := lossFn_sub_of_foc hW (hfoc (t0 + k) ht ω') (y (t0 + k) ω')
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
      linarith
    have hnext := E_next_multiplier_term hpull hy hys hay hays hmφ ht
    have hE : 𝔼.E t0 (fun ω' => EV 𝔼 (t0 + k) (φ (t0 + k + 1)) ω' ⬝ᵥ
        (Atil *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) = 𝔼.E t0 (a (t0 + (k + 1))) := by
      rw [← hnext, 𝔼.tower ht]
      rfl
    have h1 := congrFun (congrArg (𝔼.E t0) hpt) ω
    rw [map_sub, map_add, map_add, map_smul, hE] at h1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    simp only [he]
    rw [h1]
    ring
  have htel := hasSum_telescope hβ0 hβ1 (e := fun k => e (t0 + k)) heb
  simp only [Nat.add_zero, he0, mul_zero] at htel
  have hfin := (hJy.sub hJys).sub htel
  rw [sub_zero] at hfin
  refine hfin.congr_fun ?_
  intro k
  exact (hkey k).symm

/-- Woodford (2003), (1.3): `½ w' W w ≥ 0` for positive semidefinite `W`. -/
theorem quad_nonneg [Fintype ιτ] {W : Matrix ιτ ιτ ℝ} (hW : W.PosSemidef) (w : ιτ → ℝ) :
    0 ≤ quad W w := by
  unfold quad
  have := hW.dotProduct_mulVec_nonneg w
  rw [star_trivial] at this
  positivity

/-- Woodford (2003), p. 541 and survey §4.4: **Lagrangian sufficiency.** Under the hypotheses of
`lagrangian_gap` with `W ⪰ 0`, the FOC plan `y*` has no larger discounted expected loss than any
other bounded feasible plan `y`: `J(y*) ≤ J(y)`, state by state. -/
theorem lagrangian_sufficiency [Fintype ιτ] [Fintype ν] [Fintype ρ₁] [Fintype ρ₂]
    {𝔼 : ExpectationSystem Ω} (hpull : 𝔼.PullOut) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ} {Tm : Matrix ιτ ν ℝ} {W : Matrix ιτ ιτ ℝ}
    (hW : W.PosSemidef) {τs : ιτ → ℝ} {cf : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ} {t0 : ℕ}
    {y ys : ℕ → Ω → ν → ℝ} {φ : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ}
    (hy : ConstraintsHold 𝔼 Atil Itil cf t0 y) (hys : ConstraintsHold 𝔼 Atil Itil cf t0 ys)
    (hay : AdaptedV 𝔼 y) (hays : AdaptedV 𝔼 ys) (hby : BoundedV y) (hbys : BoundedV ys)
    (hbφ : BoundedV φ) (hmφ : MultiplierMeas 𝔼 φ) (hfoc : FOC 𝔼 Atil Itil Tm W τs β t0 ys φ)
    (hinit : ∀ ω, φ t0 ω ⬝ᵥ (Itil *ᵥ (y t0 ω - ys t0 ω)) = 0) (ω : Ω) :
    Jfn 𝔼 β Tm W τs t0 ys ω ≤ Jfn 𝔼 β Tm W τs t0 y ω := by
  have hWt : Wᵀ = W := by
    have := hW.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hg := lagrangian_gap hpull hβ0 hβ1 hWt hy hys hay hays hby hbys hbφ hmφ hfoc hinit ω
  have hnn : ∀ k, 0 ≤ β ^ k *
      𝔼.E t0 (fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω'))) ω := by
    intro k
    refine mul_nonneg (pow_pos hβ0 k).le ?_
    have hm := 𝔼.mono t0 (x := 0)
      (y := fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω')))
      (fun ω' => quad_nonneg hW _)
    have := hm ω
    simpa using this
  linarith [hg.nonneg hnn]

/-- Woodford (2003), p. 541 and fn 8 (uniqueness of the optimum): under `W ≻ 0` and a faithful
expectation system, a bounded feasible plan with the same discounted loss as the FOC plan has
the same target path, `T y_t = T y*_t` for all `t ≥ t₀` (strict convexity). -/
theorem targets_eq_of_J_eq [Fintype ιτ] [Fintype ν] [Fintype ρ₁] [Fintype ρ₂]
    {𝔼 : ExpectationSystem Ω} (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    {Atil Itil : Matrix (ρ₁ ⊕ ρ₂) ν ℝ} {Tm : Matrix ιτ ν ℝ} {W : Matrix ιτ ιτ ℝ}
    (hW : W.PosDef) {τs : ιτ → ℝ} {cf : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ} {t0 : ℕ}
    {y ys : ℕ → Ω → ν → ℝ} {φ : ℕ → Ω → ρ₁ ⊕ ρ₂ → ℝ}
    (hy : ConstraintsHold 𝔼 Atil Itil cf t0 y) (hys : ConstraintsHold 𝔼 Atil Itil cf t0 ys)
    (hay : AdaptedV 𝔼 y) (hays : AdaptedV 𝔼 ys) (hby : BoundedV y) (hbys : BoundedV ys)
    (hbφ : BoundedV φ) (hmφ : MultiplierMeas 𝔼 φ) (hfoc : FOC 𝔼 Atil Itil Tm W τs β t0 ys φ)
    (hinit : ∀ ω, φ t0 ω ⬝ᵥ (Itil *ᵥ (y t0 ω - ys t0 ω)) = 0)
    (hJ : ∀ ω, Jfn 𝔼 β Tm W τs t0 y ω = Jfn 𝔼 β Tm W τs t0 ys ω) :
    ∀ t, t0 ≤ t → ∀ ω, Tm *ᵥ y t ω = Tm *ᵥ ys t ω := by
  have hWt : Wᵀ = W := by
    have := hW.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  intro t ht ω
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  set q : Ω → ℝ := fun ω' => quad W (Tm *ᵥ (y (t0 + k) ω' - ys (t0 + k) ω')) with hq
  have hq0 : 0 ≤ q := fun ω' => quad_nonneg hW.posSemidef _
  have hEq : 𝔼.E t0 q = 0 := by
    funext ω'
    have hg := lagrangian_gap hpull hβ0 hβ1 hWt hy hys hay hays hby hbys hbφ hmφ hfoc hinit ω'
    rw [hJ ω', sub_self] at hg
    have hnn : ∀ j, 0 ≤ β ^ j *
        𝔼.E t0 (fun ω'' => quad W (Tm *ᵥ (y (t0 + j) ω'' - ys (t0 + j) ω''))) ω' := by
      intro j
      refine mul_nonneg (pow_pos hβ0 j).le ?_
      have := 𝔼.mono t0 (x := 0)
        (y := fun ω'' => quad W (Tm *ᵥ (y (t0 + j) ω'' - ys (t0 + j) ω'')))
        (fun ω'' => quad_nonneg hW.posSemidef _) ω'
      simpa using this
    have hz := congrFun ((hasSum_zero_iff_of_nonneg hnn).mp hg) k
    simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff', hβ0.ne', ne_eq, false_and,
      false_or] at hz
    simpa [hq] using hz
  have hq' := congrFun (hfaith t0 q hq0 hEq) ω
  simp only [hq, Pi.zero_apply, quad, mul_eq_zero, one_div, inv_eq_zero,
    OfNat.ofNat_ne_zero, false_or] at hq'
  by_contra hne
  have hne' : Tm *ᵥ (y (t0 + k) ω - ys (t0 + k) ω) ≠ 0 := by
    rw [mulVec_sub]
    exact sub_ne_zero.mpr hne
  have hpos := hW.dotProduct_mulVec_pos hne'
  rw [star_trivial] at hpos
  linarith

/-! ### The general LQ problem: FOC system, optimality, the split (1.18)–(1.19) -/

namespace LQ

variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-- Woodford (2003), p. 540: the multipliers `M_{t-1}` (on the expectational rows) inside
`φ_t = (ξ_t, M_{t-1})`. -/
def Mpart (v : ιZ ⊕ ιz → ℝ) : ιz → ℝ := fun r => v (Sum.inr r)

/-- Woodford (2003), eq. (1.9), p. 541, for the LQ problem `P`. -/
def PFOC (P : GeneralSetup.LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  FOC 𝔼 P.sys.Atil P.sys.Itil P.T P.W P.τstar P.β t0 y φ

/-- Woodford (2003), pp. 541–542: the system (1.1) + (1.9) with initial conditions `Z_{t₀} = Z₀`
and `M_{t₀-1} = M₀`, in bounded processes, with `M_t` known at `t`. -/
def FOCSystem (P : GeneralSetup.LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω)
    (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ : ℕ → Ω → ιZ ⊕ ιz → ℝ) : Prop :=
  P.Feasible 𝔼 c t0 Z0 y ∧ BoundedV φ ∧ MultiplierMeas 𝔼 φ ∧ (∀ ω, Mpart (φ t0 ω) = M0 ω) ∧
    PFOC P 𝔼 t0 y φ

omit [DecidableEq ιZ] in
/-- Woodford (2003), eqs. (1.2)–(1.3): the LQ objective is the abstract one. -/
theorem J_eq (P : GeneralSetup.LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) :
    P.J 𝔼 t0 y = Jfn 𝔼 P.β P.T P.W P.τstar t0 y := rfl

/-- Woodford (2003), p. 541: the date-`t₀` multiplier term vanishes when the two plans share
`Z_{t₀}` and `Ẽ z_{t₀}`. -/
theorem Itil_init_eq_zero (S : LinearRESystem ιZ ιz)
    {y ys : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {t0 : ℕ} {ω : Ω}
    (hZ : Zpart (y t0 ω) = Zpart (ys t0 ω))
    (hE : S.Et *ᵥ zpart (y t0 ω) = S.Et *ᵥ zpart (ys t0 ω)) :
    S.Itil *ᵥ (y t0 ω - ys t0 ω) = 0 := by
  rw [mulVec_sub, S.Itil_mulVec, S.Itil_mulVec, hZ, hE, sub_self]

/-- Woodford (2003), p. 541: "any bounded processes consistent with the initial conditions `Z_{t₀}`
and (1.6) [that] satisfy (1.1) and (1.9) for each `t ≥ t₀` conform to the second part of the
definition of optimality from a timeless perspective": a solution of the FOC system is optimal
subject to its own initial constraint `Ẽ z_{t₀} = ē`, under any expectation system with the
pull-out property. -/
theorem optimalSubjectTo_of_focSystem (P : GeneralSetup.LQProblem ιZ ιz ιτ)
    {𝔼 : ExpectationSystem Ω} (hpull : 𝔼.PullOut) {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ}
    {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : FOCSystem P 𝔼 c t0 Z0 M0 y φ) :
    P.OptimalSubjectTo 𝔼 c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y := by
  obtain ⟨hfe, hbφ, hmφ, -, hfoc⟩ := h
  refine ⟨hfe, fun _ => rfl, fun y' hy' he' ω => ?_⟩
  rw [J_eq, J_eq]
  refine lagrangian_sufficiency hpull P.β_pos P.β_lt_one P.W_posDef.posSemidef
    ((structural_iff P.sys 𝔼 c t0 y').mp hy'.1) ((structural_iff P.sys 𝔼 c t0 y).mp hfe.1)
    hy'.2.2.2 hfe.2.2.2 hy'.2.2.1 hfe.2.2.1 hbφ hmφ hfoc (fun ω' => ?_) ω
  rw [Itil_init_eq_zero P.sys ((hy'.2.1 ω').trans (hfe.2.1 ω').symm) (he' ω'), dotProduct_zero]

/-- Woodford (2003), p. 541, (1.8): a bounded solution of (1.1) + (1.9) with `M_{t₀-1} = 0` is
the `t₀`-optimal plan, under any expectation system with the pull-out property. -/
theorem t0Optimal_of_focSystem (P : GeneralSetup.LQProblem ιZ ιz ιτ)
    {𝔼 : ExpectationSystem Ω} (hpull : 𝔼.PullOut) {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ}
    {Z0 : Ω → ιZ → ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h : FOCSystem P 𝔼 c t0 Z0 0 y φ) : P.T0Optimal 𝔼 c t0 Z0 y := by
  obtain ⟨hfe, hbφ, hmφ, hM0, hfoc⟩ := h
  refine ⟨hfe, fun y' hy' ω => ?_⟩
  rw [J_eq, J_eq]
  refine lagrangian_sufficiency hpull P.β_pos P.β_lt_one P.W_posDef.posSemidef
    ((structural_iff P.sys 𝔼 c t0 y').mp hy'.1) ((structural_iff P.sys 𝔼 c t0 y).mp hfe.1)
    hy'.2.2.2 hfe.2.2.2 hy'.2.2.1 hfe.2.2.1 hbφ hmφ hfoc (fun ω' => ?_) ω
  have hZ : Zpart (y' t0 ω') - Zpart (y t0 ω') = 0 := by
    rw [hy'.2.1 ω', hfe.2.1 ω', sub_self]
  have hM : ∀ r, φ t0 ω' (Sum.inr r) = 0 := fun r => congrFun (hM0 ω') r
  rw [mulVec_sub, P.sys.Itil_mulVec, P.sys.Itil_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Pi.sub_apply, Sum.elim_inl, Sum.elim_inr, hM,
    zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_eq_zero fun r _ => ?_
  have := congrFun hZ r
  simp only [Pi.sub_apply, Pi.zero_apply] at this
  rw [this, mul_zero]

/-- Woodford (2003), p. 541, deterministic case: under perfect foresight a bounded solution of
(1.1) + (1.9) is optimal subject to its initial constraint (1.6). -/
theorem optimalSubjectTo_of_focSystem_perfectForesight (P : GeneralSetup.LQProblem ιZ ιz ιτ)
    {c : ℕ → Unit → ιz → ℝ} {t0 : ℕ} {Z0 : Unit → ιZ → ℝ} {M0 : Unit → ιz → ℝ}
    {y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Unit → ιZ ⊕ ιz → ℝ}
    (h : FOCSystem P perfectForesight c t0 Z0 M0 y φ) :
    P.OptimalSubjectTo perfectForesight c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) y :=
  optimalSubjectTo_of_focSystem P perfectForesight_pullOut h

/-- Woodford (2003), p. 541, (1.8), deterministic case: under perfect foresight a bounded
solution of (1.1) + (1.9) with `M_{t₀-1} = 0` is the `t₀`-optimal plan. -/
theorem t0Optimal_of_focSystem_perfectForesight (P : GeneralSetup.LQProblem ιZ ιz ιτ)
    {c : ℕ → Unit → ιz → ℝ} {t0 : ℕ} {Z0 : Unit → ιZ → ℝ}
    {y : ℕ → Unit → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Unit → ιZ ⊕ ιz → ℝ}
    (h : FOCSystem P perfectForesight c t0 Z0 0 y φ) : P.T0Optimal perfectForesight c t0 Z0 y :=
  t0Optimal_of_focSystem P perfectForesight_pullOut h

/-- Woodford (2003), p. 541 and fn 7 (uniqueness): if the FOC plan `y*` and another plan `y` are
both optimal subject to the same initial constraint, they have the same target path for all
`t ≥ t₀` (faithful expectations, `W ≻ 0`). -/
theorem targets_eq_of_optimal (P : GeneralSetup.LQProblem ιZ ιz ιτ)
    {𝔼 : ExpectationSystem Ω} (hpull : 𝔼.PullOut) (hfaith : Faithful 𝔼)
    {c : ℕ → Ω → ιz → ℝ} {t0 : ℕ} {Z0 : Ω → ιZ → ℝ} {M0 : Ω → ιz → ℝ}
    {ys y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (hs : FOCSystem P 𝔼 c t0 Z0 M0 ys φ)
    (hy : P.OptimalSubjectTo 𝔼 c t0 Z0 (fun ω => P.sys.Et *ᵥ zpart (ys t0 ω)) y) :
    ∀ t, t0 ≤ t → ∀ ω, P.T *ᵥ y t ω = P.T *ᵥ ys t ω := by
  have hopt := optimalSubjectTo_of_focSystem P hpull hs
  obtain ⟨hfe, hbφ, hmφ, -, hfoc⟩ := hs
  refine targets_eq_of_J_eq hpull hfaith P.β_pos P.β_lt_one P.W_posDef
    ((structural_iff P.sys 𝔼 c t0 y).mp hy.1.1) ((structural_iff P.sys 𝔼 c t0 ys).mp hfe.1)
    hy.1.2.2.2 hfe.2.2.2 hy.1.2.2.1 hfe.2.2.1 hbφ hmφ hfoc (fun ω' => ?_) (fun ω => ?_)
  · rw [Itil_init_eq_zero P.sys ((hy.1.2.1 ω').trans (hfe.2.1 ω').symm) (hy.2.1 ω'),
      dotProduct_zero]
  · exact le_antisymm (hy.2.2 ys hfe (fun _ => rfl) ω) (hopt.2.2 y hy.1 hy.2.1 ω)

omit [DecidableEq ιZ] in
/-- Woodford (2003), p. 552: block form of `Ã' p`. -/
theorem Atil_transpose_mulVec (S : LinearRESystem ιZ ιz) (p : ιZ ⊕ ιz → ℝ) :
    S.Atilᵀ *ᵥ p = Sum.elim (S.Ahatᵀ *ᵥ p) (fun _ => S.B2 ⬝ᵥ Mpart p) := by
  funext x
  rcases x with x | x
  · simp [LinearRESystem.Atil, mulVec, dotProduct]
  · simp [LinearRESystem.Atil, LinearRESystem.Bvec, mulVec, dotProduct, Mpart]

/-- Woodford (2003), p. 552: block form of `Ĩ' q`. -/
theorem Itil_transpose_mulVec (S : LinearRESystem ιZ ιz) (q : ιZ ⊕ ιz → ℝ) :
    S.Itilᵀ *ᵥ q = Sum.elim (S.Ihatᵀ *ᵥ q) 0 := by
  funext x
  rcases x with x | x
  · simp [LinearRESystem.Itil, mulVec, dotProduct]
  · simp [LinearRESystem.Itil, mulVec, dotProduct]

omit [DecidableEq ιZ] [Fintype ιZ] in
/-- Woodford (2003), p. 553: block form of `T' w` with `T = [T̃ T_i]`. -/
theorem T_transpose_mulVec (P : GeneralSetup.LQProblem ιZ ιz ιτ) (w : ιτ → ℝ) :
    P.Tᵀ *ᵥ w = Sum.elim (P.Ttilᵀ *ᵥ w) (fun _ => P.Ti ⬝ᵥ w) := by
  funext x
  rcases x with x | x
  · simp [GeneralSetup.LQProblem.T, mulVec, dotProduct]
  · simp [GeneralSetup.LQProblem.T, mulVec, dotProduct, mul_comm]

/-- Woodford (2003), eqs. (1.18)–(1.19), p. 552: with `M_t` known at `t`, the FOC (1.9) at
date `t` splits into `A' E_t φ_{t+1} + T̃' W (τ_t − τ*) − β⁻¹ Î' φ_t = 0` (1.18) and
`B₂' M_t + T_i' W (τ_t − τ*) = 0` (1.19). -/
theorem foc_iff_split (P : GeneralSetup.LQProblem ιZ ιz ιτ) {𝔼 : ExpectationSystem Ω}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (hmφ : MultiplierMeas 𝔼 φ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (t : ℕ) (ω : Ω) :
    P.sys.Atilᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω + P.Tᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) -
        P.β⁻¹ • (P.sys.Itilᵀ *ᵥ φ t ω) = 0 ↔
      (P.sys.Ahatᵀ *ᵥ EV 𝔼 t (φ (t + 1)) ω + P.Ttilᵀ *ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) -
        P.β⁻¹ • (P.sys.Ihatᵀ *ᵥ φ t ω) = 0) ∧
      P.sys.B2 ⬝ᵥ Mpart (φ (t + 1) ω) + P.Ti ⬝ᵥ (P.W *ᵥ (P.T *ᵥ y t ω - P.τstar)) = 0 := by
  have hM : Mpart (EV 𝔼 t (φ (t + 1)) ω) = Mpart (φ (t + 1) ω) := by
    funext r
    exact congrFun (hmφ t r) ω
  rw [Atil_transpose_mulVec, Itil_transpose_mulVec, T_transpose_mulVec, hM]
  constructor
  · intro h
    refine ⟨funext fun r => ?_, ?_⟩
    · have := congrFun h (Sum.inl r)
      simpa using this
    · have := congrFun h (Sum.inr ())
      simpa using this
  · rintro ⟨h1, h2⟩
    funext x
    rcases x with x | x
    · have := congrFun h1 x
      simpa using this
    · simpa using h2

/-! ### Assumption 8.1 and the affine structure (1.10) -/

/-- Woodford (2003), Assumption 8.1, p. 541 (existence part): for bounded adapted disturbances
and initial conditions `Z_{t₀}`, `M_{t₀-1}` known at `t₀`, (1.1) + (1.9) has a bounded solution. -/
def FOCSolvable (P : GeneralSetup.LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ), BoundedV c → AdaptedV 𝔼 c →
    KnownV 𝔼 t0 Z0 → KnownV 𝔼 t0 M0 → ∃ y φ, FOCSystem P 𝔼 c t0 Z0 M0 y φ

/-- Woodford (2003), Assumption 8.1, p. 541 (uniqueness part): the bounded solution of
(1.1) + (1.9) is unique for `t ≥ t₀`. -/
def FOCUnique (P : GeneralSetup.LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ) :
    Prop :=
  ∀ (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) (M0 : Ω → ιz → ℝ)
    (y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) (φ φ' : ℕ → Ω → ιZ ⊕ ιz → ℝ),
    FOCSystem P 𝔼 c t0 Z0 M0 y φ → FOCSystem P 𝔼 c t0 Z0 M0 y' φ' →
      ∀ t, t0 ≤ t → y t = y' t ∧ φ t = φ' t

variable (P : GeneralSetup.LQProblem ιZ ιz ιτ) (𝔼 : ExpectationSystem Ω) (t0 : ℕ)

/-- Woodford (2003), Assumption 8.1, p. 541: for any bounded disturbance processes and any
initial conditions `Z_{t₀}` and `M_{t₀-1}`, (1.1) + (1.9) has a unique bounded solution. -/
structure Assumption81 where
  solvable : FOCSolvable P 𝔼 t0
  unique : FOCUnique P 𝔼 t0

variable {P 𝔼 t0}

/-- Woodford (2003), p. 541: under Assumption 8.1 there exists a bounded `t₀`-optimal plan
(the solution with `M_{t₀-1} = 0`, (1.8)). -/
theorem exists_t0Optimal (hA : Assumption81 P 𝔼 t0) (hpull : 𝔼.PullOut)
    {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c) (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ}
    (hZ0 : KnownV 𝔼 t0 Z0) : ∃ y, P.T0Optimal 𝔼 c t0 Z0 y := by
  have hM : KnownV 𝔼 t0 (0 : Ω → ιz → ℝ) := fun _ => 𝔼.const t0 0
  obtain ⟨y, φ, h⟩ := hA.solvable c Z0 0 hbc hac hZ0 hM
  exact ⟨y, t0Optimal_of_focSystem P hpull h⟩

/-- Woodford (2003), p. 542, (1.10): an affine combination `w₁ x¹ + w₂ x² + w₃ x³` of three
vector processes. -/
def comb3 {ι : Type*} (w1 w2 w3 : ℝ) (x1 x2 x3 : ℕ → Ω → ι → ℝ) : ℕ → Ω → ι → ℝ :=
  fun t ω => w1 • x1 t ω + w2 • x2 t ω + w3 • x3 t ω

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 542: `E_t` is linear on affine combinations. -/
theorem E_comb3 (t : ℕ) (w1 w2 w3 : ℝ) (f1 f2 f3 : Ω → ℝ) :
    𝔼.E t (fun ω => w1 * f1 ω + w2 * f2 ω + w3 * f3 ω) =
      fun ω => w1 * 𝔼.E t f1 ω + w2 * 𝔼.E t f2 ω + w3 * 𝔼.E t f3 ω := by
  have h : (fun ω => w1 * f1 ω + w2 * f2 ω + w3 * f3 ω) = w1 • f1 + w2 • f2 + w3 • f3 := rfl
  rw [h, map_add, map_add, map_smul, map_smul, map_smul]
  rfl

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 542: `E_t` is linear on affine combinations of random vectors. -/
theorem EV_comb3 {ι : Type*} (t : ℕ) (w1 w2 w3 : ℝ) (a b d : Ω → ι → ℝ) :
    EV 𝔼 t (fun ω => w1 • a ω + w2 • b ω + w3 • d ω) =
      fun ω => w1 • EV 𝔼 t a ω + w2 • EV 𝔼 t b ω + w3 • EV 𝔼 t d ω := by
  funext ω i
  have := congrFun (E_comb3 (𝔼 := 𝔼) t w1 w2 w3 (fun ω => a ω i) (fun ω => b ω i)
    (fun ω => d ω i)) ω
  simpa [EV] using this

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 542: affine combinations of bounded processes are bounded. -/
theorem boundedV_comb3 {ι : Type*} (w1 w2 w3 : ℝ) {x1 x2 x3 : ℕ → Ω → ι → ℝ}
    (h1 : BoundedV x1) (h2 : BoundedV x2) (h3 : BoundedV x3) :
    BoundedV (comb3 w1 w2 w3 x1 x2 x3) := by
  obtain ⟨M1, hM1⟩ := h1
  obtain ⟨M2, hM2⟩ := h2
  obtain ⟨M3, hM3⟩ := h3
  refine ⟨|w1| * M1 + |w2| * M2 + |w3| * M3, fun t ω i => ?_⟩
  simp only [comb3, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |w1 * x1 t ω i + w2 * x2 t ω i + w3 * x3 t ω i|
      ≤ |w1 * x1 t ω i| + |w2 * x2 t ω i| + |w3 * x3 t ω i| := abs_add_three _ _ _
    _ ≤ _ := by
      rw [abs_mul, abs_mul, abs_mul]
      gcongr
      · exact hM1 t ω i
      · exact hM2 t ω i
      · exact hM3 t ω i

/-- Woodford (2003), p. 542, (1.10): the system (1.1) + (1.9) is affine. An affine combination
(weights summing to one) of solutions is the solution for the combined disturbances and initial
conditions. -/
theorem affine_comb_focSystem {w1 w2 w3 : ℝ} (hw : w1 + w2 + w3 = 1)
    {c1 c2 c3 : ℕ → Ω → ιz → ℝ} {Z1 Z2 Z3 : Ω → ιZ → ℝ} {M1 M2 M3 : Ω → ιz → ℝ}
    {y1 y2 y3 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ} {φ1 φ2 φ3 : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h1 : FOCSystem P 𝔼 c1 t0 Z1 M1 y1 φ1) (h2 : FOCSystem P 𝔼 c2 t0 Z2 M2 y2 φ2)
    (h3 : FOCSystem P 𝔼 c3 t0 Z3 M3 y3 φ3) :
    FOCSystem P 𝔼 (comb3 w1 w2 w3 c1 c2 c3) t0 (fun ω => w1 • Z1 ω + w2 • Z2 ω + w3 • Z3 ω)
      (fun ω => w1 • M1 ω + w2 • M2 ω + w3 • M3 ω) (comb3 w1 w2 w3 y1 y2 y3)
      (comb3 w1 w2 w3 φ1 φ2 φ3) := by
  obtain ⟨⟨hs1, hZ1, hb1, ha1⟩, hbφ1, hm1, hM1, hf1⟩ := h1
  obtain ⟨⟨hs2, hZ2, hb2, ha2⟩, hbφ2, hm2, hM2, hf2⟩ := h2
  obtain ⟨⟨hs3, hZ3, hb3, ha3⟩, hbφ3, hm3, hM3, hf3⟩ := h3
  have hZp : ∀ (u v x : (ιZ ⊕ ιz) ⊕ Unit → ℝ),
      Zpart (w1 • u + w2 • v + w3 • x) = w1 • Zpart u + w2 • Zpart v + w3 • Zpart x := by
    intro u v x
    rfl
  have hzp : ∀ (u v x : (ιZ ⊕ ιz) ⊕ Unit → ℝ),
      zpart (w1 • u + w2 • v + w3 • x) = w1 • zpart u + w2 • zpart v + w3 • zpart x := by
    intro u v x
    rfl
  have hip : ∀ (u v x : (ιZ ⊕ ιz) ⊕ Unit → ℝ),
      ipart (w1 • u + w2 • v + w3 • x) = w1 * ipart u + w2 * ipart v + w3 * ipart x := by
    intro u v x
    rfl
  refine ⟨⟨fun t ht ω => ⟨?_, ?_⟩, fun ω => ?_, boundedV_comb3 w1 w2 w3 hb1 hb2 hb3, fun t i => ?_⟩,
    boundedV_comb3 w1 w2 w3 hbφ1 hbφ2 hbφ3, fun t r => ?_, fun ω => ?_, fun t ht ω => ?_⟩
  · simp only [comb3, hZp, hzp, (hs1 t ht ω).1, (hs2 t ht ω).1, (hs3 t ht ω).1, mulVec_add,
      mulVec_smul, smul_add]
    abel
  · have hE : EV 𝔼 t (fun ω' => zpart (comb3 w1 w2 w3 y1 y2 y3 (t + 1) ω')) =
        fun ω' => w1 • EV 𝔼 t (fun ω'' => zpart (y1 (t + 1) ω'')) ω' +
          w2 • EV 𝔼 t (fun ω'' => zpart (y2 (t + 1) ω'')) ω' +
          w3 • EV 𝔼 t (fun ω'' => zpart (y3 (t + 1) ω'')) ω' := by
      simp only [comb3, hzp]
      exact EV_comb3 t w1 w2 w3 _ _ _
    rw [hE]
    simp only [mulVec_add, mulVec_smul, (hs1 t ht ω).2, (hs2 t ht ω).2, (hs3 t ht ω).2, comb3,
      hZp, hzp, hip, smul_add, add_smul, mul_smul]
    abel
  · simp only [comb3, hZp, hZ1, hZ2, hZ3]
  · have := E_comb3 (𝔼 := 𝔼) t w1 w2 w3 (fun ω => y1 t ω i) (fun ω => y2 t ω i)
      (fun ω => y3 t ω i)
    rw [ha1 t i, ha2 t i, ha3 t i] at this
    simpa [comb3] using this
  · have := E_comb3 (𝔼 := 𝔼) t w1 w2 w3 (fun ω => φ1 (t + 1) ω (Sum.inr r))
      (fun ω => φ2 (t + 1) ω (Sum.inr r)) (fun ω => φ3 (t + 1) ω (Sum.inr r))
    rw [hm1 t r, hm2 t r, hm3 t r] at this
    simpa [comb3] using this
  · change Mpart _ = w1 • M1 ω + w2 • M2 ω + w3 • M3 ω
    rw [← hM1 ω, ← hM2 ω, ← hM3 ω]
    rfl
  · have hE : EV 𝔼 t (comb3 w1 w2 w3 φ1 φ2 φ3 (t + 1)) =
        fun ω' => w1 • EV 𝔼 t (φ1 (t + 1)) ω' + w2 • EV 𝔼 t (φ2 (t + 1)) ω' +
          w3 • EV 𝔼 t (φ3 (t + 1)) ω' := EV_comb3 t w1 w2 w3 _ _ _
    have e1 := hf1 t ht ω
    have e2 := hf2 t ht ω
    have e3 := hf3 t ht ω
    obtain rfl : w3 = 1 - w1 - w2 := by linarith
    rw [hE]
    simp only [comb3, mulVec_add, mulVec_smul, mulVec_sub] at e1 e2 e3 ⊢
    have hτ : P.τstar = w1 • P.τstar + w2 • P.τstar + (1 - w1 - w2) • P.τstar := by module
    rw [hτ]
    simp only [mulVec_add, mulVec_smul, smul_add] at e1 e2 e3 ⊢
    linear_combination (norm := module) w1 • e1 + w2 • e2 + (1 - w1 - w2) • e3

/-- Woodford (2003), eq. (1.10), p. 542: under Assumption 8.1 (uniqueness) the effect of the
initial multipliers `M_{t₀-1}` on `Ẽ z_{t₀}` does not depend on the disturbances or on `Z_{t₀}`:
`e(c, Z, M) − e(c, Z, M') = e(c', Z', M) − e(c', Z', M')`, i.e. `Ẽ z_{t₀}` is additively
separable in `M_{t₀-1}`. -/
theorem eq110_separable (hU : FOCUnique P 𝔼 t0) {c c' : ℕ → Ω → ιz → ℝ} {Z Z' : Ω → ιZ → ℝ}
    {M M' : Ω → ιz → ℝ} {y1 y2 y3 y4 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ1 φ2 φ3 φ4 : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h1 : FOCSystem P 𝔼 c t0 Z M y1 φ1) (h2 : FOCSystem P 𝔼 c t0 Z M' y2 φ2)
    (h3 : FOCSystem P 𝔼 c' t0 Z' M y3 φ3) (h4 : FOCSystem P 𝔼 c' t0 Z' M' y4 φ4) (ω : Ω) :
    P.sys.Et *ᵥ zpart (y1 t0 ω) - P.sys.Et *ᵥ zpart (y2 t0 ω) =
      P.sys.Et *ᵥ zpart (y3 t0 ω) - P.sys.Et *ᵥ zpart (y4 t0 ω) := by
  have hc := affine_comb_focSystem (w1 := 1) (w2 := -1) (w3 := 1) (by ring) h1 h2 h4
  have e1 : comb3 1 (-1) 1 c c c' = c' := by
    funext t ω
    simp [comb3]
  have e2 : (fun ω => (1 : ℝ) • Z ω + (-1 : ℝ) • Z ω + (1 : ℝ) • Z' ω) = Z' := by
    funext ω
    simp
  have e3 : (fun ω => (1 : ℝ) • M ω + (-1 : ℝ) • M' ω + (1 : ℝ) • M' ω) = M := by
    funext ω
    simp
  rw [e1, e2, e3] at hc
  obtain ⟨hy, -⟩ := hU c' Z' M _ _ _ _ hc h3 t0 le_rfl
  have hz := congrArg (fun v => P.sys.Et *ᵥ zpart (v ω)) hy
  simp only [comb3] at hz
  have hzp : zpart ((1 : ℝ) • y1 t0 ω + (-1 : ℝ) • y2 t0 ω + (1 : ℝ) • y4 t0 ω) =
      zpart (y1 t0 ω) - zpart (y2 t0 ω) + zpart (y4 t0 ω) := by
    funext r
    simp [zpart]
    ring
  rw [hzp, mulVec_add, mulVec_sub] at hz
  rw [← hz]
  abel

/-- Woodford (2003), eq. (1.10), p. 542: under Assumption 8.1 (uniqueness) the map
`M ↦ e(M) − e(0)` (`e = Ẽ z_{t₀}` of the solution) is additive. -/
theorem eq110_additive (hU : FOCUnique P 𝔼 t0) {c : ℕ → Ω → ιz → ℝ} {Z : Ω → ιZ → ℝ}
    {M1 M2 : Ω → ιz → ℝ} {y1 y2 y0 y12 : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ1 φ2 φ0 φ12 : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h1 : FOCSystem P 𝔼 c t0 Z M1 y1 φ1) (h2 : FOCSystem P 𝔼 c t0 Z M2 y2 φ2)
    (h0 : FOCSystem P 𝔼 c t0 Z 0 y0 φ0) (h12 : FOCSystem P 𝔼 c t0 Z (M1 + M2) y12 φ12)
    (ω : Ω) :
    P.sys.Et *ᵥ zpart (y12 t0 ω) - P.sys.Et *ᵥ zpart (y0 t0 ω) =
      (P.sys.Et *ᵥ zpart (y1 t0 ω) - P.sys.Et *ᵥ zpart (y0 t0 ω)) +
        (P.sys.Et *ᵥ zpart (y2 t0 ω) - P.sys.Et *ᵥ zpart (y0 t0 ω)) := by
  have hc := affine_comb_focSystem (w1 := 1) (w2 := 1) (w3 := -1) (by ring) h1 h2 h0
  have e1 : comb3 1 1 (-1) c c c = c := by
    funext t ω
    simp [comb3]
  have e2 : (fun ω => (1 : ℝ) • Z ω + (1 : ℝ) • Z ω + (-1 : ℝ) • Z ω) = Z := by
    funext ω
    simp
  have e3 : (fun ω => (1 : ℝ) • M1 ω + (1 : ℝ) • M2 ω + (-1 : ℝ) • (0 : Ω → ιz → ℝ) ω) =
      M1 + M2 := by
    funext ω
    simp
  rw [e1, e2, e3] at hc
  obtain ⟨hy, -⟩ := hU c Z (M1 + M2) _ _ _ _ hc h12 t0 le_rfl
  have hz := congrArg (fun v => P.sys.Et *ᵥ zpart (v ω)) hy
  simp only [comb3] at hz
  have hzp : zpart ((1 : ℝ) • y1 t0 ω + (1 : ℝ) • y2 t0 ω + (-1 : ℝ) • y0 t0 ω) =
      zpart (y1 t0 ω) + zpart (y2 t0 ω) - zpart (y0 t0 ω) := by
    funext r
    simp [zpart]
    ring
  rw [hzp, mulVec_sub, mulVec_add] at hz
  rw [← hz]
  abel

/-- Woodford (2003), eq. (1.10), p. 542: under Assumption 8.1 (uniqueness) the map
`M ↦ e(M) − e(0)` is homogeneous, `e(aM) − e(0) = a (e(M) − e(0))`; with `eq110_additive` it is
linear: `Ẽ z_{t₀} = e(c, Z, 0) + e_M M_{t₀-1}`. -/
theorem eq110_homogeneous (hU : FOCUnique P 𝔼 t0) {c : ℕ → Ω → ιz → ℝ} {Z : Ω → ιZ → ℝ}
    {M : Ω → ιz → ℝ} (a : ℝ) {y1 y0 ya : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ1 φ0 φa : ℕ → Ω → ιZ ⊕ ιz → ℝ}
    (h1 : FOCSystem P 𝔼 c t0 Z M y1 φ1) (h0 : FOCSystem P 𝔼 c t0 Z 0 y0 φ0)
    (ha : FOCSystem P 𝔼 c t0 Z (a • M) ya φa) (ω : Ω) :
    P.sys.Et *ᵥ zpart (ya t0 ω) - P.sys.Et *ᵥ zpart (y0 t0 ω) =
      a • (P.sys.Et *ᵥ zpart (y1 t0 ω) - P.sys.Et *ᵥ zpart (y0 t0 ω)) := by
  have hc := affine_comb_focSystem (w1 := a) (w2 := 1 - a) (w3 := 0) (by ring) h1 h0 h0
  have e1 : comb3 a (1 - a) 0 c c c = c := by
    funext t ω
    simp only [comb3]
    module
  have e2 : (fun ω => a • Z ω + (1 - a) • Z ω + (0 : ℝ) • Z ω) = Z := by
    funext ω
    module
  have e3 : (fun ω => a • M ω + (1 - a) • (0 : Ω → ιz → ℝ) ω + (0 : ℝ) • (0 : Ω → ιz → ℝ) ω) =
      a • M := by
    funext ω
    simp
  rw [e1, e2, e3] at hc
  obtain ⟨hy, -⟩ := hU c Z (a • M) _ _ _ _ hc ha t0 le_rfl
  have hz := congrArg (fun v => P.sys.Et *ᵥ zpart (v ω)) hy
  simp only [comb3] at hz
  have hzp : zpart (a • y1 t0 ω + (1 - a) • y0 t0 ω + (0 : ℝ) • y0 t0 ω) =
      zpart (y0 t0 ω) + a • (zpart (y1 t0 ω) - zpart (y0 t0 ω)) := by
    funext r
    simp [zpart]
    ring
  rw [hzp, mulVec_add, mulVec_smul, mulVec_sub] at hz
  rw [← hz]
  abel

/-! ### Timeless optimality restated via initial multipliers (1.11)–(1.12) -/

/-- Woodford (2003), the restated Definition, p. 543, (1.11)–(1.12): (1) `z_t = f⁰ + F X̄_t`;
(2) `y` is the bounded solution of (1.1) + (1.9) with `Z_{t₀}` and initial multipliers
(3) `M_{t₀-1} = g⁰ + G X̄_{t₀}` (1.11). -/
def RestatedTimeless {κ : Type*} [Fintype κ] (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ)
    (Xbar : ℕ → Ω → κ → ℝ) (f0 : ιz → ℝ) (F : Matrix ιz κ ℝ) (g0 : ιz → ℝ) (G : Matrix ιz κ ℝ)
    (y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ) : Prop :=
  (∀ t, t0 ≤ t → ∀ ω, zpart (y t ω) = f0 + F *ᵥ Xbar t ω) ∧
    ∃ φ, FOCSystem P 𝔼 c t0 Z0 (fun ω => g0 + G *ᵥ Xbar t0 ω) y φ

/-- Woodford (2003), eq. (1.12), p. 543: in the restated form, `Ẽ z_t` coincides at every date
with `Ẽ` times the right side of (1.5). -/
theorem restated_eq112 {κ : Type*} [Fintype κ] {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ}
    {Xbar : ℕ → Ω → κ → ℝ} {f0 : ιz → ℝ} {F : Matrix ιz κ ℝ} {g0 : ιz → ℝ}
    {G : Matrix ιz κ ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (h : RestatedTimeless (P := P) (𝔼 := 𝔼) (t0 := t0) c Z0 Xbar f0 F g0 G y) :
    ∀ t, t0 ≤ t → ∀ ω, P.sys.Et *ᵥ zpart (y t ω) = P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t ω) :=
  fun t ht ω => by rw [h.1 t ht ω]

/-- Woodford (2003), pp. 542–543: the restated definition implies the original one — a plan
satisfying (1.5), solving (1.1) + (1.9) with initial multipliers (1.11), is optimal from a
timeless perspective (Lagrangian sufficiency; any expectation system with pull-out). -/
theorem restated_timeless (hpull : 𝔼.PullOut) {κ : Type*} [Fintype κ]
    {c : ℕ → Ω → ιz → ℝ} {Z0 : Ω → ιZ → ℝ} {Xbar : ℕ → Ω → κ → ℝ} {f0 : ιz → ℝ}
    {F : Matrix ιz κ ℝ} {g0 : ιz → ℝ} {G : Matrix ιz κ ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (h : RestatedTimeless (P := P) (𝔼 := 𝔼) (t0 := t0) c Z0 Xbar f0 F g0 G y) :
    P.TimelesslyOptimalPlan 𝔼 c t0 Z0 Xbar f0 F y := by
  obtain ⟨h1, φ, hs⟩ := h
  refine ⟨h1, ?_⟩
  have hopt := optimalSubjectTo_of_focSystem P hpull hs
  have he : (fun ω => P.sys.Et *ᵥ zpart (y t0 ω)) =
      fun ω => P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t0 ω) := by
    funext ω
    rw [h1 t0 le_rfl ω]
  rwa [he] at hopt

/-- Woodford (2003), p. 543: the identifiability condition under which two feasible plans with
the same target path from `t₀` on coincide from `t₀` on (needed to pass from "same loss" to
"same plan"; the targets alone are pinned down by strict convexity, `targets_eq_of_optimal`). -/
def TargetIdentifiable (c : ℕ → Ω → ιz → ℝ) (Z0 : Ω → ιZ → ℝ) : Prop :=
  ∀ y y' : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ, P.Feasible 𝔼 c t0 Z0 y → P.Feasible 𝔼 c t0 Z0 y' →
    (∀ t, t0 ≤ t → ∀ ω, P.T *ᵥ y t ω = P.T *ᵥ y' t ω) → ∀ t, t0 ≤ t → y t = y' t

/-- Woodford (2003), pp. 542–543: the original definition implies the restated one. Let `y` be
optimal from a timeless perspective (1.5)–(1.6). Under Assumption 8.1, if the constraint value
`ē = Ẽ (f⁰ + F X̄_{t₀})` is attained by the FOC solution for initial multipliers `M₀` (Woodford's
(1.10) with `ē` in the range of `e(·)` — in the book this is the unproved necessity of the
FOC), then `y` has the target path of that solution; if the targets identify the plan, `y` is
that solution, i.e. condition (2) of the restated definition holds with `M_{t₀-1} = M₀`. -/
theorem timeless_restated (hA : Assumption81 P 𝔼 t0) (hpull : 𝔼.PullOut)
    (hfaith : Faithful 𝔼) {κ : Type*} [Fintype κ] {c : ℕ → Ω → ιz → ℝ} (hbc : BoundedV c)
    (hac : AdaptedV 𝔼 c) {Z0 : Ω → ιZ → ℝ} {Xbar : ℕ → Ω → κ → ℝ} {f0 : ιz → ℝ}
    {F : Matrix ιz κ ℝ} {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    (hy : P.TimelesslyOptimalPlan 𝔼 c t0 Z0 Xbar f0 F y) {M0 : Ω → ιz → ℝ}
    (hM0 : KnownV 𝔼 t0 M0)
    (hattain : ∀ yM φM, FOCSystem P 𝔼 c t0 Z0 M0 yM φM →
      ∀ ω, P.sys.Et *ᵥ zpart (yM t0 ω) = P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t0 ω)) :
    (∃ yM φM, FOCSystem P 𝔼 c t0 Z0 M0 yM φM ∧
      ∀ t, t0 ≤ t → ∀ ω, P.T *ᵥ y t ω = P.T *ᵥ yM t ω) ∧
    (TargetIdentifiable (P := P) (𝔼 := 𝔼) (t0 := t0) c Z0 →
      ∃ φ, FOCSystem P 𝔼 c t0 Z0 M0 y φ) := by
  have hfe := hy.2.1
  have hZ0 : KnownV 𝔼 t0 Z0 := by
    intro i
    have h := hfe.2.2.2 t0 (Sum.inl (Sum.inl i))
    have hz : (fun ω => Z0 ω i) = fun ω => y t0 ω (Sum.inl (Sum.inl i)) := by
      funext ω
      rw [← hfe.2.1 ω]
      rfl
    rw [hz]
    exact h
  obtain ⟨yM, φM, hs⟩ := hA.solvable c Z0 M0 hbc hac hZ0 hM0
  have he : (fun ω => P.sys.Et *ᵥ (f0 + F *ᵥ Xbar t0 ω)) =
      fun ω => P.sys.Et *ᵥ zpart (yM t0 ω) := by
    funext ω
    rw [hattain yM φM hs ω]
  have hopt := hy.2
  rw [he] at hopt
  have htar := targets_eq_of_optimal P hpull hfaith hs hopt
  refine ⟨⟨yM, φM, hs, htar⟩, fun hid => ⟨φM, ?_⟩⟩
  have heq := hid y yM hfe hs.1 htar
  obtain ⟨_, hbφ, hmφ, hM, hfoc⟩ := hs
  refine ⟨hfe, hbφ, hmφ, hM, fun t ht ω => ?_⟩
  have := hfoc t ht ω
  rwa [← heq t ht] at this

end LQ

/-! ### Footnote 8: the reciprocal pairing of the characteristic roots -/

namespace Pencil

variable {K : Type*} [Field K] {ρ ν : Type*} [Fintype ρ] [Fintype ν] [DecidableEq ρ]
  [DecidableEq ν]

/-- Woodford (2003), fn 8, p. 542: the matrix pencil of the system (1.1) + (1.9) (disturbances
and targets set to zero). Trying `y_t = μ^t ȳ`, `φ_t = μ^t φ̄` gives
`[Q, μÃ' − β⁻¹Ĩ'; Ã − μĨ, 0] (ȳ, φ̄) = 0` with `Q = T' W T`; the characteristic equation is
`det = 0`. -/
def pencil (Atil Itil : Matrix ρ ν K) (Q : Matrix ν ν K) (β μ : K) :
    Matrix (ν ⊕ ρ) (ν ⊕ ρ) K :=
  fromBlocks Q (μ • Atilᵀ - β⁻¹ • Itilᵀ) (Atil - μ • Itil) 0

/-- Woodford (2003), fn 8, p. 542: the pencil at `(βμ)⁻¹` is a diagonal rescaling of the
transpose of the pencil at `μ` (`Q` symmetric, `μ ≠ 0`). -/
theorem pencil_inv_eq (Atil Itil : Matrix ρ ν K) {Q : Matrix ν ν K} (hQ : Qᵀ = Q) (β : K)
    {μ : K} (hμ : μ ≠ 0) :
    pencil Atil Itil Q β (β * μ)⁻¹ =
      fromBlocks 1 0 0 (μ⁻¹ • (1 : Matrix ρ ρ K)) * (pencil Atil Itil Q β μ)ᵀ *
        fromBlocks 1 0 0 ((β * μ)⁻¹ • (1 : Matrix ρ ρ K)) := by
  unfold pencil
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Matrix.mul_zero, transpose_zero, hQ, Matrix.smul_mul, Matrix.mul_smul, transpose_sub,
    transpose_smul, transpose_transpose, smul_zero]
  congr 1
  · rw [smul_sub, smul_smul, mul_inv, mul_assoc, inv_mul_cancel₀ hμ, mul_one]
  · rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul, mul_inv, mul_comm]

/-- Woodford (2003), fn 8, p. 542: the determinant identity behind the root pairing,
`det P((βμ)⁻¹) = μ^{-n} (βμ)^{-n} det P(μ)` (`n` = number of structural equations). -/
theorem pencil_det_pairing (Atil Itil : Matrix ρ ν K) {Q : Matrix ν ν K} (hQ : Qᵀ = Q) (β : K)
    {μ : K} (hμ : μ ≠ 0) :
    (pencil Atil Itil Q β (β * μ)⁻¹).det =
      μ⁻¹ ^ Fintype.card ρ * (β * μ)⁻¹ ^ Fintype.card ρ * (pencil Atil Itil Q β μ).det := by
  rw [pencil_inv_eq Atil Itil hQ β hμ, det_mul, det_mul, det_transpose, det_fromBlocks_zero₂₁,
    det_fromBlocks_zero₂₁, det_one, det_smul, det_smul, det_one]
  ring

/-- Woodford (2003), fn 8, p. 542: "for every root `μᵢ`, `β⁻¹ μᵢ⁻¹` is also a root" (nonzero
roots, `β ≠ 0`, `Q` symmetric). -/
theorem pencil_root_pairing (Atil Itil : Matrix ρ ν K) {Q : Matrix ν ν K} (hQ : Qᵀ = Q) {β : K}
    (hβ : β ≠ 0) {μ : K} (hμ : μ ≠ 0) :
    (pencil Atil Itil Q β μ).det = 0 ↔ (pencil Atil Itil Q β (β * μ)⁻¹).det = 0 := by
  rw [pencil_det_pairing Atil Itil hQ β hμ]
  have h1 : μ⁻¹ ^ Fintype.card ρ ≠ 0 := pow_ne_zero _ (inv_ne_zero hμ)
  have h2 : (β * μ)⁻¹ ^ Fintype.card ρ ≠ 0 := pow_ne_zero _ (inv_ne_zero (mul_ne_zero hβ hμ))
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (mul_ne_zero h1 h2)
    · exact h'

/-- Woodford (2003), fn 8, p. 542: the pairing `μ ↦ (βμ)⁻¹` maps roots inside the circle
`|μ| = β^{-1/2}` strictly outside it (`β‖μ‖² < 1 ⇒ β‖(βμ)⁻¹‖² > 1`). -/
theorem pair_outside {β : ℝ} (hβ : 0 < β) {μ : ℂ} (hμ : μ ≠ 0) (h : β * ‖μ‖ ^ 2 < 1) :
    1 < β * ‖((β : ℂ) * μ)⁻¹‖ ^ 2 := by
  have hn : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
  have hx : 0 < β * ‖μ‖ ^ 2 := by positivity
  have : β * (β * ‖μ‖)⁻¹ ^ 2 = (β * ‖μ‖ ^ 2)⁻¹ := by
    field_simp
  rw [this]
  exact (one_lt_inv₀ hx).mpr h

/-- Woodford (2003), fn 8, p. 542: the pairing maps the circle `|μ| = β^{-1/2}` to itself. -/
theorem pair_on_circle {β : ℝ} (hβ : 0 < β) {μ : ℂ} (h : β * ‖μ‖ ^ 2 = 1) :
    β * ‖((β : ℂ) * μ)⁻¹‖ ^ 2 = 1 := by
  have hμ : μ ≠ 0 := by
    rintro rfl
    simp at h
  have hn : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
  have : β * (β * ‖μ‖)⁻¹ ^ 2 = (β * ‖μ‖ ^ 2)⁻¹ := by
    field_simp
  rw [this, h, inv_one]

/-- Woodford (2003), fn 8: the `Ã` matrix of the counterexample — one forward-looking variable
`z`, no predetermined variable, structural equation `E_t z_{t+1} = a z_t + i_t` (so `Ẽ = 1`,
`A₂₂ = a ≠ 0`, `B₂ = 1 ≠ 0`), variables ordered `(z, i)`. -/
def fn8Atil (a : ℂ) : Matrix (Fin 1) (Fin 2) ℂ := !![a, 1]

/-- Woodford (2003), fn 8: `Ĩ = [Ẽ 0] = [1 0]` for the counterexample. -/
def fn8Itil : Matrix (Fin 1) (Fin 2) ℂ := !![1, 0]

/-- Woodford (2003), fn 8: `Q = T' W T` for the counterexample, whose only target is the
instrument (`τ_t = i_t`, `W = 1 ≻ 0`). -/
def fn8Q : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

/-- Woodford (2003), fn 8, p. 542 (survey E19): **"exactly half of the roots have modulus less
than `β^{-1/2}`" is false without a genericity condition.** In the counterexample with
`a = β^{-1/2}` the characteristic function is `det P(μ) = a (μ − a)²`, a double root ON the
circle `|μ| = β^{-1/2}`: no root has modulus less than `β^{-1/2}`. The correct statement
(`pencil_root_pairing`, `pair_outside`) needs no root on the circle. -/
theorem fn8_counterexample {β : ℝ} (hβ : 0 < β) :
    let a : ℂ := ((Real.sqrt β)⁻¹ : ℝ)
    (∀ μ : ℂ, (pencil (fn8Atil a) fn8Itil fn8Q (β : ℂ) μ).det = a * (μ - a) ^ 2) ∧
    (∀ μ : ℂ, (pencil (fn8Atil a) fn8Itil fn8Q (β : ℂ) μ).det = 0 ↔ μ = a) ∧
    β * ‖a‖ ^ 2 = 1 ∧
    ¬ ∃ μ : ℂ, (pencil (fn8Atil a) fn8Itil fn8Q (β : ℂ) μ).det = 0 ∧ β * ‖μ‖ ^ 2 < 1 := by
  intro a
  have hs : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have ha2 : a ^ 2 = (β : ℂ)⁻¹ := by
    simp only [a]
    push_cast
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt hβ.le]
  have ha0 : a ≠ 0 := by
    simp only [a]
    exact_mod_cast (inv_pos.mpr hs).ne'
  have hdet : ∀ μ : ℂ, (pencil (fn8Atil a) fn8Itil fn8Q (β : ℂ) μ).det = a * (μ - a) ^ 2 := by
    intro μ
    rw [← Matrix.det_reindex_self finSumFinEquiv, Matrix.det_fin_three]
    simp [pencil, fn8Atil, fn8Itil, fn8Q, finSumFinEquiv, Fin.addCases, ← ha2]
    ring
  have hnorm : β * ‖a‖ ^ 2 = 1 := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), inv_pow,
      Real.sq_sqrt hβ.le]
    field_simp
  have hroot : ∀ μ : ℂ, (pencil (fn8Atil a) fn8Itil fn8Q (β : ℂ) μ).det = 0 ↔ μ = a := by
    intro μ
    rw [hdet μ]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h ha0
      · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
    · rintro rfl
      simp
  refine ⟨hdet, hroot, hnorm, ?_⟩
  rintro ⟨μ, hμ, hlt⟩
  rw [(hroot μ).mp hμ, hnorm] at hlt
  exact lt_irrefl _ hlt

end Pencil

/-! ### The selection claim of p. 552 (Assumption 8.2) -/

namespace Selection

open ComplexConjugate

/-- Woodford (2003), p. 552: a multiset of roots is closed under complex conjugation (with
multiplicity), as the roots of a real polynomial are. -/
def ConjClosed (S : Multiset ℂ) : Prop := S.map (starRingEnd ℂ) = S

/-- Woodford (2003), p. 552: conjugation is injective. -/
theorem conj_injective : Function.Injective (starRingEnd ℂ) :=
  (starRingEnd ℂ).injective

/-- Woodford (2003), p. 552: in a conjugation-closed multiset the conjugate of a member is a
member. -/
theorem ConjClosed.conj_mem {S : Multiset ℂ} (hS : ConjClosed S) {μ : ℂ} (h : μ ∈ S) :
    conj μ ∈ S := by
  rw [← hS]
  exact Multiset.mem_map_of_mem _ h

/-- Woodford (2003), p. 552: removing a conjugate pair preserves closure. -/
theorem ConjClosed.erase_pair {S : Multiset ℂ} (hS : ConjClosed S) (μ : ℂ) :
    ConjClosed ((S.erase μ).erase (conj μ)) := by
  unfold ConjClosed
  rw [Multiset.map_erase _ conj_injective, Multiset.map_erase _ conj_injective, hS,
    Complex.conj_conj, Multiset.erase_comm]

/-- Woodford (2003), p. 552: a conjugation-closed multiset of non-real roots has even
cardinality (complex roots come in pairs). -/
theorem card_even_of_conj_closed_nonreal :
    ∀ (n : ℕ) (S : Multiset ℂ), Multiset.card S = n → ConjClosed S →
      (∀ μ ∈ S, conj μ ≠ μ) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS hnr
    rcases Multiset.empty_or_exists_mem S with h0 | ⟨μ, hμ⟩
    · subst h0
      simp at hn
      simp [← hn]
    · have hc : conj μ ∈ S.erase μ := Multiset.mem_erase_of_ne (hnr μ hμ) |>.mpr (hS.conj_mem hμ)
      have hcard : Multiset.card ((S.erase μ).erase (conj μ)) + 2 = n := by
        have h1 := Multiset.card_erase_add_one hc
        have h2 := Multiset.card_erase_add_one hμ
        omega
      have he := ih _ (by omega) _ rfl (hS.erase_pair μ) (fun ν hν =>
        hnr ν (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hν)))
      rw [← hcard]
      exact he.add (by norm_num)

/-- Woodford (2003), p. 552: "it is necessarily possible to choose a set of roots with property
(i) [real roots and complete conjugate pairs]" of any size `m ≤ |S|`, unless all roots are
non-real and `m` is odd. -/
theorem exists_conj_closed_sub :
    ∀ (m : ℕ) (S : Multiset ℂ), ConjClosed S → m ≤ Multiset.card S →
      (Even m ∨ ∃ μ ∈ S, conj μ = μ) →
      ∃ T ≤ S, ConjClosed T ∧ Multiset.card T = m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hS hm hcond
    by_cases hall : ∀ μ ∈ S, conj μ = μ
    · refine ⟨(S.toList.take m : Multiset ℂ), ?_, ?_, ?_⟩
      · conv_rhs => rw [← Multiset.coe_toList S]
        exact Multiset.coe_le.mpr (List.take_sublist _ _).subperm
      · unfold ConjClosed
        have hsub : ∀ x ∈ (S.toList.take m : Multiset ℂ), x ∈ S := fun x hx =>
          Multiset.mem_toList.mp (List.mem_of_mem_take (Multiset.mem_coe.mp hx))
        rw [Multiset.map_congr rfl (fun x hx => hall x (hsub x hx)), Multiset.map_id']
      · simp only [Multiset.coe_card, List.length_take, Multiset.length_toList]
        omega
    · push Not at hall
      obtain ⟨μ, hμ, hne⟩ := hall
      rcases m with _ | _ | m
      · exact ⟨0, Multiset.zero_le _, by simp [ConjClosed], rfl⟩
      · rcases hcond with he | ⟨ν, hν, hreal⟩
        · exact absurd he (by decide)
        · refine ⟨{ν}, Multiset.singleton_le.mpr hν, ?_, rfl⟩
          simp [ConjClosed, hreal]
      · have hc : conj μ ∈ S.erase μ := Multiset.mem_erase_of_ne hne |>.mpr (hS.conj_mem hμ)
        set S' := (S.erase μ).erase (conj μ) with hS'
        have hcard : Multiset.card S' + 2 = Multiset.card S := by
          have h1 := Multiset.card_erase_add_one hc
          have h2 := Multiset.card_erase_add_one hμ
          rw [hS']
          omega
        have hcond' : Even m ∨ ∃ ν ∈ S', conj ν = ν := by
          rcases hcond with he | ⟨ν, hν, hreal⟩
          · left
            rwa [show m + 1 + 1 = m + 2 by ring, Nat.even_add, iff_true_intro even_two,
              iff_true] at he
          · right
            refine ⟨ν, ?_, hreal⟩
            have h1 : ν ≠ μ := by
              rintro rfl
              exact hne hreal
            have h2 : ν ≠ conj μ := by
              rintro rfl
              apply hne
              rw [Complex.conj_conj] at hreal
              rw [← hreal]
            exact Multiset.mem_erase_of_ne h2 |>.mpr (Multiset.mem_erase_of_ne h1 |>.mpr hν)
        obtain ⟨T, hT, hTc, hTm⟩ := ih m (by omega) S' (hS.erase_pair μ) (by omega) hcond'
        refine ⟨μ ::ₘ conj μ ::ₘ T, ?_, ?_, ?_⟩
        · calc μ ::ₘ conj μ ::ₘ T ≤ μ ::ₘ conj μ ::ₘ S' :=
                Multiset.cons_le_cons _ (Multiset.cons_le_cons _ hT)
            _ = S := by rw [hS', Multiset.cons_erase hc, Multiset.cons_erase hμ]
        · unfold ConjClosed at hTc ⊢
          rw [Multiset.map_cons, Multiset.map_cons, hTc, Complex.conj_conj, Multiset.cons_swap]
        · simp [hTm]

/-- Woodford (2003), p. 552: when all available roots are non-real and `m` is odd, no selection
with property (i) exists (so the exception in the text is genuine). -/
theorem no_conj_closed_sub_of_odd {S : Multiset ℂ} (hnr : ∀ μ ∈ S, conj μ ≠ μ) {m : ℕ}
    (hm : ¬ Even m) : ¬ ∃ T ≤ S, ConjClosed T ∧ Multiset.card T = m := by
  rintro ⟨T, hT, hTc, rfl⟩
  exact hm (card_even_of_conj_closed_nonreal _ T rfl hTc
    (fun μ hμ => hnr μ (Multiset.mem_of_le hT hμ)))

/-- Woodford (2003), p. 552: "even in this case, it is necessarily possible to choose a set of
`n_Z` roots in which there is only one complex root such that the complex conjugate is not also
in the set": every `m ≤ |S|` admits a selection `T ≤ S` that is conjugation-closed or a
conjugation-closed multiset plus one root. -/
theorem exists_almost_conj_closed_sub {S : Multiset ℂ} (hS : ConjClosed S) {m : ℕ}
    (hm : m ≤ Multiset.card S) :
    ∃ T ≤ S, Multiset.card T = m ∧
      ∃ T', ConjClosed T' ∧ (T = T' ∨ ∃ μ, T = μ ::ₘ T') := by
  by_cases hcond : Even m ∨ ∃ μ ∈ S, conj μ = μ
  · obtain ⟨T, hT, hTc, hTm⟩ := exists_conj_closed_sub m S hS hm hcond
    exact ⟨T, hT, hTm, T, hTc, Or.inl rfl⟩
  · push Not at hcond
    obtain ⟨hodd, -⟩ := hcond
    obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hodd
    obtain ⟨T', hT', hT'c, hT'm⟩ :=
      exists_conj_closed_sub (2 * k) S hS (by omega) (Or.inl (even_two_mul k))
    have hpos : 0 < Multiset.card (S - T') := by
      rw [Multiset.card_sub hT']
      omega
    obtain ⟨μ, hμ⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
    refine ⟨μ ::ₘ T', ?_, ?_, T', hT'c, Or.inr ⟨μ, rfl⟩⟩
    · calc μ ::ₘ T' = {μ} + T' := (Multiset.singleton_add μ T').symm
        _ ≤ (S - T') + T' := add_le_add_left (Multiset.singleton_le.mpr hμ) _
        _ = S := Multiset.sub_add_cancel hT'
    · simp [hT'm, hk]

end Selection

end Woodford.OptimalPolicyRules.GeneralFOC
