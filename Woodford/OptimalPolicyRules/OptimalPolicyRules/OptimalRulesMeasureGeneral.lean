/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import OptimalPolicyRules.OptimalRulesMeasureKernel

/-!
# Assumption 8.1 for arbitrary bounded adapted disturbances

Woodford (2003), *Interest and Prices*, Chapter 8, Assumption 8.1 (p. 541) on a filtered
probability space with Mathlib's conditional expectation, for **every** bounded adapted
disturbance process `c_t` (not only the VAR disturbances of `OptimalRulesMeasureMarkov`).

## The forward–backward solution theory

Under the perfect-foresight Assumption 8.1, the deterministic solution map has an absolutely
summable kernel (`OptimalRulesMeasureKernel.kernel_hasSum`): from the state `n = (Z, M)` and the
forcing path `g`, `y_0(n, g) = y_0(n, 0) + ∑_k K_k g_k`, and the next state is
`N(n, g) = N(n, 0) + ∑_k K^N_k g_k` with `N(n, 0) = h + H n` (`Hgen`). The **candidate** on a
probability space is built from the conditional forecasts `ĝ_t = (E_t c_{t+k})_k`:

* the forward (jump) part: `E_t ∑_k K_k c_{t+k}` — a conditional expectation of a realised,
  absolutely convergent series (`Rser`), equal a.s. to `∑_k K_k E_t c_{t+k}`
  (`rser_spec`, dominated convergence);
* the backward (predetermined) part: the state recursion `X_{t+1} = h + H X_t +
  E_t ∑_k K^N_k c_{t+k}` from `X_{t₀} = (Z_{t₀}, M_{t₀−1})` (`Xs`).

## Main results

* `gen_solves`: if the forecast-driven state `Xs` is essentially bounded, the candidate
  `(ygen, φgen)` solves (1.1) + (1.9) with genuine conditional expectations.
* `m_exists_iff`: **the exact condition** — for a bounded adapted disturbance and bounded initial
  conditions (`Z_{t₀}` known at `t₀`, `M_{t₀−1}` known at `t₀ − 1`), a bounded solution exists
  **iff** the forecast-driven state is essentially bounded; when it exists it is a.s. unique
  (`OptimalRulesMeasureForecast.m_focUnique_of_pf`) and equals the candidate.
* `m_assumption81MB_of_powDecay`: if `H` is geometrically stable, the (corrected) measure
  Assumption 8.1 holds on **every** filtered probability space for **every** bounded adapted
  disturbance.
* `powBdd_Hgen`: the perfect-foresight Assumption 8.1 makes `H` power-bounded;
  `powDecay_of_powBdd_noUnit`, `m_assumption81MB_of_noUnit`: under the **root condition** (no
  eigenvalue of `H` on the unit circle) `H` is geometrically stable and the measure
  Assumption 8.1 holds for every bounded adapted disturbance.
* `m_prop82_general`: Proposition 8.2 (commitment to (1.23) determines exactly one bounded
  equilibrium, the optimal one) for every bounded adapted disturbance, under the same conditions.
* `xs_bdd_unit`: on the one-point probability space the exact condition always holds (link with
  the core perfect-foresight Assumption 8.1).
-/

namespace Woodford.OptimalPolicyRules.OptimalRulesMeasureGeneral

open MeasureTheory Filter Topology Matrix GeneralSetup GeneralFOC GeneralFOC.LQ
open ExpectationsMeasure OptimalRulesMeasure OptimalRulesMeasureMarkov OptimalRulesMeasureForecast
  OptimalRulesMeasureKernel

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ιZ ιz ιτ : Type*} [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ]
  [DecidableEq ιz]

/-! ### Realised forward series and their conditional expectations -/

omit [MeasurableSpace Ω] [Fintype ιZ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1 (the forward part): the realised series `∑_k L_k c_{s+k}(ω)` for a
kernel `L`. -/
noncomputable def Rser {κ : Type*} (L : ℕ → Matrix κ ιz ℝ)
    (c : ℕ → Ω → ιz → ℝ) (s : ℕ) (ω : Ω) : κ → ℝ :=
  fun a => ∑' k, (L k *ᵥ c (s + k) ω) a

omit [Fintype ιZ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1 (tool): for an absolutely summable kernel and a bounded adapted
disturbance, the realised series converges a.s., is essentially bounded and integrable, and
`E_t` passes through it: `E_t ∑_k L_k c_{s+k} = ∑_k L_k E_t c_{s+k}` a.s. -/
theorem rser_spec {κ : Type*} [Finite κ] {L : ℕ → Matrix κ ιz ℝ}
    (hL : ∀ a i, Summable fun k => |L k a i|) {S : MeasExpectationSystem Ω}
    {c : ℕ → Ω → ιz → ℝ} (hcb : MBoundedV S c) (hca : MAdaptedV S c) :
    ∃ KR, ∀ s, (∀ a, Integrable (fun ω => Rser L c s ω a) S.μ) ∧
      (∀ᵐ ω ∂S.μ, ∀ a, |Rser L c s ω a| ≤ KR) ∧
      ∀ t a, ∀ᵐ ω ∂S.μ, HasSum (fun k => (L k *ᵥ EVm S t (c (s + k)) ω) a)
        (EVm S t (Rser L c s) ω a) := by
  have := Fintype.ofFinite κ
  obtain ⟨Kc, hKc⟩ := hcb
  set Kc' := max Kc 0 with hKc'
  have hci := integrable_of_adapted ⟨Kc, hKc⟩ hca
  set b : κ → ℕ → ℝ := fun a k => ∑ j, |L k a j| * Kc' with hb
  have hbs : ∀ a, Summable (b a) := fun a => summable_sum fun j _ => (hL a j).mul_right _
  refine ⟨∑ a, ∑' k, b a k, fun s => ?_⟩
  have hbd : ∀ k a, ∀ᵐ ω ∂S.μ, |(L k *ᵥ c (s + k) ω) a| ≤ b a k := fun k a => by
    filter_upwards [hKc (s + k)] with ω h
    exact OptimalRulesMeasureKernel.abs_mulVec_le (L k) (v := c (s + k) ω) (B := Kc')
      (fun j => (h j).trans (le_max_left _ _)) a
  have hm : ∀ k a, AEStronglyMeasurable (fun ω => (L k *ᵥ c (s + k) ω) a) S.μ := fun k a =>
    (integrable_mulVec _ (hci (s + k)) a).aestronglyMeasurable
  have hsum : ∀ a, ∀ᵐ ω ∂S.μ, HasSum (fun k => (L k *ᵥ c (s + k) ω) a) (Rser L c s ω a) := by
    intro a
    filter_upwards [ae_all_iff.2 fun k => hbd k a] with ω h
    exact (Summable.of_norm_bounded (hbs a) fun k => by
      rw [Real.norm_eq_abs]
      exact h k).hasSum
  have hbR : ∀ a, ∀ᵐ ω ∂S.μ, |Rser L c s ω a| ≤ ∑' k, b a k := fun a => by
    filter_upwards [ae_all_iff.2 fun k => hbd k a, hsum a] with ω h hs
    rw [← Real.norm_eq_abs]
    exact tsum_of_norm_bounded (hbs a).hasSum (fun k => by rw [Real.norm_eq_abs]; exact h k)
      |>.trans_eq' (by rw [hs.tsum_eq])
  have hbR' : ∀ a, ∑' k, b a k ≤ ∑ a, ∑' k, b a k := fun a =>
    Finset.single_le_sum (f := fun a => ∑' k, b a k)
      (fun a _ => tsum_nonneg fun k => Finset.sum_nonneg fun j _ =>
        mul_nonneg (abs_nonneg _) (le_max_right _ _)) (Finset.mem_univ a)
  have hRm : ∀ a, AEStronglyMeasurable (fun ω => Rser L c s ω a) S.μ := fun a =>
    aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N ω => ∑ k ∈ Finset.range N, (L k *ᵥ c (s + k) ω) a)
      (fun N => Finset.aestronglyMeasurable_fun_sum _ fun k _ => hm k a)
      ((hsum a).mono fun ω h => h.tendsto_sum_nat)
  refine ⟨fun a => integrable_of_bound (hRm a) (hbR a), ?_, fun t a => ?_⟩
  · filter_upwards [ae_all_iff.2 hbR] with ω h a
    exact (h a).trans (hbR' a)
  · have hE := S.E_hasSum (hbs a) (hm · a) (fun k => hbd k a) t
    have hk : ∀ k, S.E t (fun ω => (L k *ᵥ c (s + k) ω) a) =ᵐ[S.μ]
        fun ω => (L k *ᵥ EVm S t (c (s + k)) ω) a := fun k => by
      filter_upwards [EVm_mulVec S t (L k) (hci (s + k))] with ω e
      exact congrFun e a
    filter_upwards [hE, ae_all_iff.2 hk] with ω h1 h2
    have hR : (fun ω' => Rser L c s ω' a) = fun ω' => ∑' k, (L k *ᵥ c (s + k) ω') a := rfl
    change HasSum _ (S.E t (fun ω' => Rser L c s ω' a) ω)
    rw [hR]
    exact h1.congr_fun fun k => (h2 k).symm

/-! ### The next-state kernel and the affine parts -/

variable {P : LQProblem ιZ ιz ιτ} (hA81 : Assumption81 P perfectForesight 0)

/-- Woodford (2003), p. 539: the kernel of the next state `(Z_1, M_0)`: rows `Z` from the date-1
plan kernel, rows `M` from the date-1 multiplier kernel. -/
noncomputable def KN (k : ℕ) : Matrix (ιZ ⊕ ιz) ιz ℝ :=
  Matrix.of fun a i => Sum.elim (fun j => KY hA81 1 k (Sum.inl (Sum.inl j)) i)
    (fun r => KΦ hA81 1 k (Sum.inr r) i) a

/-- Woodford (2003), p. 539: the next-state kernel is absolutely summable. -/
theorem KN_summable : ∀ a i, Summable fun k => |KN hA81 k a i| := by
  intro a i
  rcases a with j | r
  · exact (kernel_summable hA81 1).1 _ i
  · exact (kernel_summable hA81 1).2 _ i

/-- Woodford (2003), p. 539: **the next state as a kernel series**,
`N(n, g) = N(n, 0) + ∑_k K^N_k g_k`. -/
theorem nextS_hasSum (n : ιZ ⊕ ιz → ℝ) {g : ℕ → ιz → ℝ} (hg : BddSeq g) :
    HasSum (fun k => KN hA81 k *ᵥ g k) (nextS hA81 n g - nextS hA81 n 0) := by
  obtain ⟨hY, hΦ⟩ := kernel_hasSum hA81 1 n hg
  rw [Pi.hasSum] at hY hΦ ⊢
  intro a
  rcases a with j | r
  · exact hY (Sum.inl (Sum.inl j))
  · exact hΦ (Sum.inr r)

/-- Woodford (2003), p. 539: with zero forcing the next state is affine in the state,
`N(n, 0) = h + H n`. -/
theorem nextS_affine : ∃ (h : ιZ ⊕ ιz → ℝ) (H : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ),
    ∀ n, nextS hA81 n 0 = h + H *ᵥ n := by
  obtain ⟨y1, B1, p1, G1, h1⟩ := sol0_affine hA81 1
  refine OptimalRulesMeasureMarkov.exists_affine_matrix (fun n => nextS hA81 n 0)
    fun w1 w2 w3 x1 x2 x3 hw => ?_
  funext a
  rcases a with j | r
  · simp only [nextS, Sum.elim_inl, Zpart, (h1 _).1, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mulVec_add, mulVec_smul]
    have : w3 = 1 - w1 - w2 := by linarith
    subst this
    ring
  · simp only [nextS, Sum.elim_inr, Mpart, (h1 _).2, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      mulVec_add, mulVec_smul]
    have : w3 = 1 - w1 - w2 := by linarith
    subst this
    ring

/-- Woodford (2003), p. 539: the intercept `h` of the state transition with zero forcing. -/
noncomputable def hgen : ιZ ⊕ ιz → ℝ := Classical.choose (nextS_affine hA81)

/-- Woodford (2003), p. 539: **the matrix `H` of the endogenous state transition**,
`(Z_{t+1}, M_t) = h + H (Z_t, M_{t−1})` with zero forcing (the general counterpart of
`OptimalRulesMeasureMarkov.Hn`). -/
noncomputable def Hgen : Matrix (ιZ ⊕ ιz) (ιZ ⊕ ιz) ℝ :=
  Classical.choose (Classical.choose_spec (nextS_affine hA81))

/-- Woodford (2003), p. 539: `N(n, 0) = h + H n`. -/
theorem hgen_spec (n : ιZ ⊕ ιz → ℝ) : nextS hA81 n 0 = hgen hA81 + Hgen hA81 *ᵥ n :=
  Classical.choose_spec (Classical.choose_spec (nextS_affine hA81)) n

/-! ### The candidate solution on a probability space -/

variable (S : MeasExpectationSystem Ω) (c : ℕ → Ω → ιz → ℝ) (t0 : ℕ) (Z0 : Ω → ιZ → ℝ)
  (M0 : Ω → ιz → ℝ)

/-- Woodford (2003), p. 539: **the forecast-driven state** `X_{t₀+k} = (Z_{t₀+k}, M_{t₀+k−1})`:
`X_{t₀} = (Z_{t₀}, M_{t₀−1})`, `X_{t+1} = N(X_t, 0) + E_t ∑_j K^N_j c_{t+j}`. -/
noncomputable def Xs : ℕ → Ω → ιZ ⊕ ιz → ℝ
  | 0 => fun ω => Sum.elim (Z0 ω) (M0 ω)
  | k + 1 => fun ω => nextS hA81 (Xs k ω) 0 + EVm S (t0 + k) (Rser (KN hA81) c (t0 + k)) ω

/-- Woodford (2003), (1.5): **the candidate plan** `y_t = y_0(X_t, 0) + E_t ∑_k K_k c_{t+k}`
for `t ≥ t₀`. -/
noncomputable def ygen : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ :=
  fun t ω => if t0 ≤ t then solY hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) 0 0 +
    EVm S t (Rser (KY hA81 0) c t) ω else 0

/-- Woodford (2003), (1.17): **the candidate multipliers**: `ξ_t` from the kernel, `M_{t−1}` from
the state, for `t ≥ t₀`. -/
noncomputable def φgen : ℕ → Ω → ιZ ⊕ ιz → ℝ :=
  fun t ω => if t0 ≤ t then
    Sum.elim (fun j => solΦ hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) 0 0 (Sum.inl j) +
      EVm S t (Rser (KΦ hA81 0) c t) ω (Sum.inl j))
      (fun r => Xs hA81 S c t0 Z0 M0 (t - t0) ω (Sum.inr r)) else 0

/-! ### Measurability and the a.s. identities -/

variable {S c t0 Z0 M0}

/-- Woodford (2003), p. 540: the forecast-driven state is known at the right dates — `X_{t₀}` at
`t₀`, and `X_{t₀+k+1}` (which contains `M_{t₀+k}`) already at `t₀ + k`. -/
theorem Xs_known (hZk : MKnownV S t0 Z0) (hMk : MKnownV S (t0 - 1) M0) :
    MKnownV S t0 (Xs hA81 S c t0 Z0 M0 0) ∧
      ∀ k, MKnownV S (t0 + k) (Xs hA81 S c t0 Z0 M0 (k + 1)) := by
  have h0 : MKnownV S t0 (Xs hA81 S c t0 Z0 M0 0) := by
    intro i
    rcases i with j | r
    · exact hZk j
    · exact (hMk r).mono (S.𝓕.mono (Nat.sub_le t0 1))
  refine ⟨h0, fun k => ?_⟩
  induction k with
  | zero =>
    intro i
    have : (fun ω => Xs hA81 S c t0 Z0 M0 (0 + 1) ω i) = fun ω =>
        (hgen hA81 + Hgen hA81 *ᵥ Xs hA81 S c t0 Z0 M0 0 ω +
          EVm S (t0 + 0) (Rser (KN hA81) c (t0 + 0)) ω) i := by
      funext ω
      simp only [Xs]
      rw [hgen_spec]
    rw [this]
    exact sm_comp₂ h0 (fun a => S.stronglyMeasurable_E _ _)
      (g := fun p : (ιZ ⊕ ιz → ℝ) × (ιZ ⊕ ιz → ℝ) => (hgen hA81 + Hgen hA81 *ᵥ p.1 + p.2) i)
      (by fun_prop)
  | succ k ih =>
    intro i
    have : (fun ω => Xs hA81 S c t0 Z0 M0 (k + 1 + 1) ω i) = fun ω =>
        (hgen hA81 + Hgen hA81 *ᵥ Xs hA81 S c t0 Z0 M0 (k + 1) ω +
          EVm S (t0 + (k + 1)) (Rser (KN hA81) c (t0 + (k + 1))) ω) i := by
      funext ω
      simp only [Xs]
      rw [hgen_spec]
    rw [this]
    exact sm_comp₂ (fun j => (ih j).mono (S.𝓕.mono (show t0 + k ≤ t0 + (k + 1) by omega)))
      (fun a => S.stronglyMeasurable_E _ _)
      (g := fun p : (ιZ ⊕ ιz → ℝ) × (ιZ ⊕ ιz → ℝ) => (hgen hA81 + Hgen hA81 *ᵥ p.1 + p.2) i)
      (by fun_prop)

/-- Woodford (2003), p. 540: `X_{t₀+k}` is known at `t₀ + k`. -/
theorem Xs_known' (hZk : MKnownV S t0 Z0) (hMk : MKnownV S (t0 - 1) M0) (k : ℕ) :
    MKnownV S (t0 + k) (Xs hA81 S c t0 Z0 M0 k) := by
  rcases k with _ | k
  · exact (Xs_known hA81 hZk hMk).1
  · exact fun i => ((Xs_known hA81 hZk hMk).2 k i).mono (S.𝓕.mono (by omega))

/-- Woodford (2003), p. 540 (tool): the date-`t` forecast path of the disturbance,
`k ↦ E_t c_{t+k}(ω)`. -/
noncomputable def chat (S : MeasExpectationSystem Ω) (c : ℕ → Ω → ιz → ℝ) (t : ℕ) (ω : Ω) :
    ℕ → ιz → ℝ :=
  fun k => EVm S t (c (t + k)) ω

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), fn 6: the forecast path of a bounded disturbance is a.s. bounded by the same
bound. -/
theorem chat_bdd [Countable ιz] {Kc : ℝ} (hKc : ∀ t, ∀ᵐ ω ∂S.μ, ∀ i, |c t ω i| ≤ Kc) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ∀ k i, |chat S c t ω k i| ≤ Kc :=
  ae_all_iff.2 fun k => ae_all_iff.2 fun i => S.abs_E_le ((hKc (t + k)).mono fun _ h => h i) t

/-- Woodford (2003), (1.5), (1.17), p. 539, a.s. at `t ≥ t₀`: **the candidate is the
perfect-foresight solution of the current state and forecast path** — `y_t`, `φ_t` are the
date-0 values and `X_{t+1}` the next state of the deterministic solution from
`(X_t, (E_t c_{t+k})_k)` (kernel series and `E_t` through the realised series). -/
theorem gen_now (hcb : MBoundedV S c) (hca : MAdaptedV S c) {t : ℕ} (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ, BddSeq (chat S c t ω) ∧
      ygen hA81 S c t0 Z0 M0 t ω =
        solY hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) (chat S c t ω) 0 ∧
      φgen hA81 S c t0 Z0 M0 t ω =
        solΦ hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) (chat S c t ω) 0 ∧
      Xs hA81 S c t0 Z0 M0 (t + 1 - t0) ω =
        nextS hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) (chat S c t ω) := by
  obtain ⟨Kc, hKc⟩ := hcb
  obtain ⟨_, hRY⟩ := rser_spec (kernel_summable hA81 0).1 ⟨Kc, hKc⟩ hca
  obtain ⟨_, hRΦ⟩ := rser_spec (kernel_summable hA81 0).2 ⟨Kc, hKc⟩ hca
  obtain ⟨_, hRN⟩ := rser_spec (KN_summable hA81) ⟨Kc, hKc⟩ hca
  filter_upwards [chat_bdd hKc t, ae_all_iff.2 fun a => (hRY t).2.2 t a,
    ae_all_iff.2 fun a => (hRΦ t).2.2 t a, ae_all_iff.2 fun a => (hRN t).2.2 t a]
    with ω hc eY eΦ eN
  set X := Xs hA81 S c t0 Z0 M0 (t - t0) ω with hX
  have hg : BddSeq (chat S c t ω) := ⟨Kc, hc⟩
  have cY : EVm S t (Rser (KY hA81 0) c t) ω =
      solY hA81 X (chat S c t ω) 0 - solY hA81 X 0 0 :=
    funext fun a => (eY a).unique ((Pi.hasSum.mp (kernel_hasSum hA81 0 X hg).1) a)
  have cΦ : EVm S t (Rser (KΦ hA81 0) c t) ω =
      solΦ hA81 X (chat S c t ω) 0 - solΦ hA81 X 0 0 :=
    funext fun a => (eΦ a).unique ((Pi.hasSum.mp (kernel_hasSum hA81 0 X hg).2) a)
  have cN : EVm S t (Rser (KN hA81) c t) ω = nextS hA81 X (chat S c t ω) - nextS hA81 X 0 :=
    funext fun a => (eN a).unique ((Pi.hasSum.mp (nextS_hasSum hA81 X hg)) a)
  have hM := (sol_spec hA81 X hg).2.2.2.1 ()
  refine ⟨hg, ?_, ?_, ?_⟩
  · simp only [ygen, ht, ↓reduceIte]
    rw [← hX, cY]
    abel
  · funext a
    rcases a with j | r
    · simp only [φgen, ht, ↓reduceIte, Sum.elim_inl]
      rw [← hX, cΦ]
      simp only [Pi.sub_apply]
      abel
    · simp only [φgen, ht, ↓reduceIte, Sum.elim_inr]
      rw [← hX]
      exact (congrFun hM r).symm
  · have e : t + 1 - t0 = (t - t0) + 1 := by omega
    rw [e]
    simp only [Xs]
    rw [← hX, show t0 + (t - t0) = t by omega, cN]
    abel

/-- Woodford (2003), pp. 539–541, a.s. at `t ≥ t₀`: **the conditional forecasts of next period's
candidate are the date-1 values of the perfect-foresight solution** from `(X_t, (E_t c_{t+k})_k)`
(law of iterated expectations, `E_t` through the realised series, time invariance
`OptimalRulesMeasureKernel.sol_shift`). Requires the state to be essentially bounded. -/
theorem gen_next (hcb : MBoundedV S c) (hca : MAdaptedV S c) (hZk : MKnownV S t0 Z0)
    (hMk : MKnownV S (t0 - 1) M0)
    (hXb : ∃ K, ∀ k, ∀ᵐ ω ∂S.μ, ∀ i, |Xs hA81 S c t0 Z0 M0 k ω i| ≤ K) {t : ℕ}
    (ht : t0 ≤ t) :
    ∀ᵐ ω ∂S.μ,
      EVm S t (ygen hA81 S c t0 Z0 M0 (t + 1)) ω =
        solY hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) (chat S c t ω) 1 ∧
      EVm S t (φgen hA81 S c t0 Z0 M0 (t + 1)) ω =
        solΦ hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) (chat S c t ω) 1 := by
  obtain ⟨Kc, hKc⟩ := hcb
  obtain ⟨KX, hKX⟩ := hXb
  obtain ⟨y0, By, p0, Bp, h0⟩ := sol0_affine hA81 0
  obtain ⟨_, hRY⟩ := rser_spec (kernel_summable hA81 0).1 ⟨Kc, hKc⟩ hca
  obtain ⟨_, hRΦ⟩ := rser_spec (kernel_summable hA81 0).2 ⟨Kc, hKc⟩ hca
  set X' := Xs hA81 S c t0 Z0 M0 (t + 1 - t0) with hX'
  have hX'k : MKnownV S t X' := by
    have := (Xs_known hA81 (c := c) hZk hMk).2 (t - t0)
    rwa [show t0 + (t - t0) = t by omega, show t - t0 + 1 = t + 1 - t0 by omega] at this
  have hX'i : ∀ i, Integrable (fun ω => X' ω i) S.μ := fun i =>
    integrable_of_bound ((hX'k i).mono (S.𝓕.le t)).aestronglyMeasurable
      ((hKX _).mono fun ω h => h i)
  have hky : MKnownV S t (fun ω => y0 + By *ᵥ X' ω) := fun i =>
    sm_comp hX'k (g := fun v => (y0 + By *ᵥ v) i) (by fun_prop)
  have hiy : ∀ i, Integrable (fun ω => (y0 + By *ᵥ X' ω) i) S.μ := fun i =>
    (integrable_const _).add (integrable_mulVec By hX'i i)
  have hkp : MKnownV S t (fun ω => p0 + Bp *ᵥ X' ω) := fun i =>
    sm_comp hX'k (g := fun v => (p0 + Bp *ᵥ v) i) (by fun_prop)
  have hip : ∀ i, Integrable (fun ω => (p0 + Bp *ᵥ X' ω) i) S.μ := fun i =>
    (integrable_const _).add (integrable_mulVec Bp hX'i i)
  have hy1 : ygen hA81 S c t0 Z0 M0 (t + 1) = fun ω =>
      (y0 + By *ᵥ X' ω) + EVm S (t + 1) (Rser (KY hA81 0) c (t + 1)) ω := by
    funext ω
    simp only [ygen, show t0 ≤ t + 1 by omega, ↓reduceIte, (h0 _).1, hX']
  have hEy : ∀ᵐ ω ∂S.μ, EVm S t (ygen hA81 S c t0 Z0 M0 (t + 1)) ω =
      (y0 + By *ᵥ X' ω) + EVm S t (Rser (KY hA81 0) c (t + 1)) ω := by
    rw [hy1]
    filter_upwards [EVm_add S t (x := fun ω => y0 + By *ᵥ X' ω)
      (x' := EVm S (t + 1) (Rser (KY hA81 0) c (t + 1))) hiy (fun i => S.integrable_E (t + 1) _),
      EVm_tower S (Nat.le_succ t) (Rser (KY hA81 0) c (t + 1))] with ω e1 e2
    rw [e1, e2, EVm_of_known S hky hiy]
  have hEp : ∀ᵐ ω ∂S.μ, EVm S t (fun ω => (p0 + Bp *ᵥ X' ω) +
      EVm S (t + 1) (Rser (KΦ hA81 0) c (t + 1)) ω) ω =
      (p0 + Bp *ᵥ X' ω) + EVm S t (Rser (KΦ hA81 0) c (t + 1)) ω := by
    filter_upwards [EVm_add S t (x := fun ω => p0 + Bp *ᵥ X' ω)
      (x' := EVm S (t + 1) (Rser (KΦ hA81 0) c (t + 1))) hip (fun i => S.integrable_E (t + 1) _),
      EVm_tower S (Nat.le_succ t) (Rser (KΦ hA81 0) c (t + 1))] with ω e1 e2
    rw [e1, e2, EVm_of_known S hkp hip]
  have hX'E : EVm S t X' = X' := EVm_of_known S hX'k hX'i
  filter_upwards [gen_now hA81 ⟨Kc, hKc⟩ hca ht, chat_bdd hKc t,
    ae_all_iff.2 fun a => (hRY (t + 1)).2.2 t a, ae_all_iff.2 fun a => (hRΦ (t + 1)).2.2 t a,
    hEy, hEp] with ω hnow hc eY eΦ fY fΦ
  obtain ⟨hg, -, -, hD⟩ := hnow
  set X := Xs hA81 S c t0 Z0 M0 (t - t0) ω with hX
  set g1 : ℕ → ιz → ℝ := fun k => chat S c t ω (k + 1) with hg1
  have hg1b : BddSeq g1 := ⟨Kc, fun k i => hc (k + 1) i⟩
  have hidx : ∀ k, (fun j => EVm S t (c (t + 1 + j)) ω) k = g1 k := fun k => by
    simp only [hg1, chat]
    rw [show t + (k + 1) = t + 1 + k by omega]
  have cY : EVm S t (Rser (KY hA81 0) c (t + 1)) ω =
      solY hA81 (X' ω) g1 0 - solY hA81 (X' ω) 0 0 := by
    funext a
    refine (eY a).unique ?_
    have := (Pi.hasSum.mp (kernel_hasSum hA81 0 (X' ω) hg1b).1) a
    refine this.congr_fun fun k => ?_
    rw [← hidx k]
  have cΦ : EVm S t (Rser (KΦ hA81 0) c (t + 1)) ω =
      solΦ hA81 (X' ω) g1 0 - solΦ hA81 (X' ω) 0 0 := by
    funext a
    refine (eΦ a).unique ?_
    have := (Pi.hasSum.mp (kernel_hasSum hA81 0 (X' ω) hg1b).2) a
    refine this.congr_fun fun k => ?_
    rw [← hidx k]
  have hsh := sol_shift hA81 X hg 0
  have hX'n : X' ω = nextS hA81 X (chat S c t ω) := hD
  refine ⟨?_, ?_⟩
  · rw [fY, cY, ← (h0 _).1, hsh.1, ← hX'n]
    abel
  · funext a
    rcases a with j | r
    · have hfun : (fun ω' => φgen hA81 S c t0 Z0 M0 (t + 1) ω' (Sum.inl j)) = fun ω' =>
          ((p0 + Bp *ᵥ X' ω') + EVm S (t + 1) (Rser (KΦ hA81 0) c (t + 1)) ω') (Sum.inl j) := by
        funext ω'
        simp only [φgen, show t0 ≤ t + 1 by omega, ↓reduceIte, Sum.elim_inl, (h0 _).2, hX',
          Pi.add_apply]
      change S.E t (fun ω' => φgen hA81 S c t0 Z0 M0 (t + 1) ω' (Sum.inl j)) ω = _
      rw [hfun]
      have := congrFun fΦ (Sum.inl j)
      simp only [EVm] at this
      rw [this, cΦ, ← (h0 _).2, hsh.2, ← hX'n]
      simp only [Pi.add_apply, Pi.sub_apply]
      abel
    · have hfun : (fun ω' => φgen hA81 S c t0 Z0 M0 (t + 1) ω' (Sum.inr r)) =
          fun ω' => X' ω' (Sum.inr r) := by
        funext ω'
        simp only [φgen, show t0 ≤ t + 1 by omega, ↓reduceIte, Sum.elim_inr, hX']
      change S.E t (fun ω' => φgen hA81 S c t0 Z0 M0 (t + 1) ω' (Sum.inr r)) ω = _
      rw [hfun]
      have h1 : S.E t (fun ω' => X' ω' (Sum.inr r)) ω = X' ω (Sum.inr r) :=
        congrFun (congrFun hX'E ω) (Sum.inr r)
      rw [h1, hX'n, hsh.2]
      have hM := (sol_spec hA81 (nextS hA81 X (chat S c t ω)) (bddSeq_shift hg)).2.2.2.1 ()
      exact (congrFun hM r).symm

/-! ### Existence -/

/-- Woodford (2003), **Assumption 8.1 (existence)**, p. 541, for an arbitrary bounded adapted
disturbance: **if the forecast-driven state `X_t` is essentially bounded, the candidate
`(ygen, φgen)` is a bounded solution of (1.1) + (1.9)** with genuine conditional expectations,
`Z_{t₀}` and `M_{t₀−1}` as initial conditions. -/
theorem gen_solves (hcb : MBoundedV S c) (hca : MAdaptedV S c) (hZk : MKnownV S t0 Z0)
    (hMk : MKnownV S (t0 - 1) M0)
    (hXb : ∃ K, ∀ k, ∀ᵐ ω ∂S.μ, ∀ i, |Xs hA81 S c t0 Z0 M0 k ω i| ≤ K) :
    MFOCSystem S P c t0 Z0 M0 (ygen hA81 S c t0 Z0 M0) (φgen hA81 S c t0 Z0 M0) := by
  obtain ⟨y0, By, p0, Bp, h0⟩ := sol0_affine hA81 0
  have hXb' := hXb
  obtain ⟨KX, hKX⟩ := hXb'
  have hcb' := hcb
  obtain ⟨Kc, hKc⟩ := hcb'
  have hci := integrable_of_adapted hcb hca
  obtain ⟨KRY, hRY⟩ := rser_spec (kernel_summable hA81 0).1 hcb hca
  obtain ⟨KRΦ, hRΦ⟩ := rser_spec (kernel_summable hA81 0).2 hcb hca
  have hEY : ∀ t, ∀ᵐ ω ∂S.μ, ∀ a, |EVm S t (Rser (KY hA81 0) c t) ω a| ≤ KRY := fun t =>
    ae_all_iff.2 fun a => S.abs_E_le ((hRY t).2.1.mono fun _ h => h a) t
  have hEΦ : ∀ t, ∀ᵐ ω ∂S.μ, ∀ a, |EVm S t (Rser (KΦ hA81 0) c t) ω a| ≤ KRΦ := fun t =>
    ae_all_iff.2 fun a => S.abs_E_le ((hRΦ t).2.1.mono fun _ h => h a) t
  obtain ⟨KBy, hKBy⟩ := exists_bound_mulVec By KX
  obtain ⟨KBp, hKBp⟩ := exists_bound_mulVec Bp KX
  have hXk := Xs_known' hA81 (c := c) hZk hMk
  have hXk1 := (Xs_known hA81 (c := c) hZk hMk).2
  have hyfun : ∀ t, t0 ≤ t → ygen hA81 S c t0 Z0 M0 t = fun ω =>
      y0 + By *ᵥ Xs hA81 S c t0 Z0 M0 (t - t0) ω + EVm S t (Rser (KY hA81 0) c t) ω := by
    intro t ht
    funext ω
    simp only [ygen, ht, ↓reduceIte, (h0 _).1]
  have hXkt : ∀ t, t0 ≤ t → MKnownV S t (Xs hA81 S c t0 Z0 M0 (t - t0)) := fun t ht => by
    have := hXk (t - t0)
    rwa [show t0 + (t - t0) = t by omega] at this
  set Ky := ∑ a, |y0 a| + KBy + KRY with hKy
  set Kp := ∑ a, |p0 a| + KBp + KRΦ with hKp
  refine ⟨⟨fun t ht => ⟨?_, ?_⟩, ?_, ⟨max Ky 0, fun t => ?_⟩, fun t i => ?_⟩,
    ⟨max (max Kp KX) 0, fun t => ?_⟩, fun t i => ?_, fun t r => ?_,
    Eventually.of_forall fun ω => ?_, fun t ht => ?_⟩
  · -- predetermined rows
    filter_upwards [gen_now hA81 (Z0 := Z0) (M0 := M0) hcb hca ht,
      gen_now hA81 (Z0 := Z0) (M0 := M0) hcb hca (show t0 ≤ t + 1 by omega)] with ω h h1
    obtain ⟨hg, hy, -, hD⟩ := h
    obtain ⟨hg1, hy1, -, -⟩ := h1
    have hZ1 := (sol_spec hA81 (Xs hA81 S c t0 Z0 M0 (t + 1 - t0) ω) hg1).1.2.1 ()
    have hrow := ((sol_spec hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) hg).1.1 0 le_rfl ()).1
    rw [hy1, hy]
    change Zpart (solY hA81 (Xs hA81 S c t0 Z0 M0 (t + 1 - t0) ω) (chat S c (t + 1) ω) 0) = _
    rw [hZ1]
    change (fun j => Xs hA81 S c t0 Z0 M0 (t + 1 - t0) ω (Sum.inl j)) = _
    rw [hD]
    exact hrow
  · -- expectational rows
    filter_upwards [gen_now hA81 (Z0 := Z0) (M0 := M0) hcb hca ht,
      gen_next hA81 hcb hca hZk hMk hXb ht] with ω h hn
    obtain ⟨hg, hy, -, -⟩ := h
    have hrow := ((sol_spec hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) hg).1.1 0 le_rfl ()).2
    change P.sys.Et *ᵥ zpart (EVm S t (ygen hA81 S c t0 Z0 M0 (t + 1)) ω) = _
    rw [hn.1, hy]
    have hc0 : chat S c t ω 0 = c t ω := by
      simp only [chat, Nat.add_zero]
      exact congrFun (EVm_of_known S (hca t) (hci t)) ω
    rw [← hc0]
    exact hrow
  · -- initial predetermined variables
    filter_upwards [gen_now hA81 (Z0 := Z0) (M0 := M0) hcb hca (le_refl t0)] with ω h
    obtain ⟨hg, hy, -, -⟩ := h
    rw [hy]
    have hZ := (sol_spec hA81 (Xs hA81 S c t0 Z0 M0 (t0 - t0) ω) hg).1.2.1 ()
    change Zpart (solY hA81 (Xs hA81 S c t0 Z0 M0 (t0 - t0) ω) (chat S c t0 ω) 0) = _
    rw [hZ, Nat.sub_self]
    rfl
  · -- bounded plan
    by_cases ht : t0 ≤ t
    · filter_upwards [hKX (t - t0), hEY t] with ω h1 h2 i
      rw [hyfun t ht]
      simp only [Pi.add_apply]
      refine ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_
        (hKBy _ h1 i))) (h2 i))).trans (le_max_left _ _)
      exact Finset.single_le_sum (f := fun a => |y0 a|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)
    · refine Eventually.of_forall fun ω i => ?_
      simp only [ygen, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact le_max_right _ _
  · -- adapted plan
    by_cases ht : t0 ≤ t
    · rw [hyfun t ht]
      exact sm_comp₂ (hXkt t ht) (fun a => S.stronglyMeasurable_E t _)
        (g := fun p : (ιZ ⊕ ιz → ℝ) × ((ιZ ⊕ ιz) ⊕ Unit → ℝ) => (y0 + By *ᵥ p.1 + p.2) i)
        (by fun_prop)
    · have : (fun ω => ygen hA81 S c t0 Z0 M0 t ω i) = fun _ => 0 := by
        funext ω
        simp only [ygen, ht, ↓reduceIte, Pi.zero_apply]
      rw [this]
      exact stronglyMeasurable_const
  · -- bounded multipliers
    by_cases ht : t0 ≤ t
    · filter_upwards [hKX (t - t0), hEΦ t] with ω h1 h2 i
      rcases i with j | r
      · simp only [φgen, ht, ↓reduceIte, Sum.elim_inl, (h0 _).2, Pi.add_apply]
        refine (((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_
          (hKBp _ h1 _))) (h2 _))).trans (le_max_left _ _)).trans (le_max_left _ _)
        exact Finset.single_le_sum (f := fun a => |p0 a|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ _)
      · simp only [φgen, ht, ↓reduceIte, Sum.elim_inr]
        exact ((h1 _).trans (le_max_right _ _)).trans (le_max_left _ _)
    · refine Eventually.of_forall fun ω i => ?_
      simp only [φgen, ht, ↓reduceIte, Pi.zero_apply, abs_zero]
      exact le_max_right _ _
  · -- measurable multipliers
    by_cases ht : t0 ≤ t
    · rcases i with j | r
      · have : (fun ω => φgen hA81 S c t0 Z0 M0 t ω (Sum.inl j)) = fun ω =>
            (p0 + Bp *ᵥ Xs hA81 S c t0 Z0 M0 (t - t0) ω +
              EVm S t (Rser (KΦ hA81 0) c t) ω) (Sum.inl j) := by
          funext ω
          simp only [φgen, ht, ↓reduceIte, Sum.elim_inl, (h0 _).2, Pi.add_apply]
        rw [this]
        exact ((sm_comp₂ (hXkt t ht) (fun a => S.stronglyMeasurable_E t _)
          (g := fun p : (ιZ ⊕ ιz → ℝ) × (ιZ ⊕ ιz → ℝ) => (p0 + Bp *ᵥ p.1 + p.2) (Sum.inl j))
          (by fun_prop)).mono (S.𝓕.le t)).aestronglyMeasurable
      · have : (fun ω => φgen hA81 S c t0 Z0 M0 t ω (Sum.inr r)) =
            fun ω => Xs hA81 S c t0 Z0 M0 (t - t0) ω (Sum.inr r) := by
          funext ω
          simp only [φgen, ht, ↓reduceIte, Sum.elim_inr]
        rw [this]
        exact ((hXkt t ht _).mono (S.𝓕.le t)).aestronglyMeasurable
    · have : (fun ω => φgen hA81 S c t0 Z0 M0 t ω i) = fun _ => 0 := by
        funext ω
        simp only [φgen, ht, ↓reduceIte, Pi.zero_apply]
      rw [this]
      exact aestronglyMeasurable_const
  · -- `M_t` known at `t`
    by_cases ht : t0 ≤ t
    · have : (fun ω => φgen hA81 S c t0 Z0 M0 (t + 1) ω (Sum.inr r)) =
          fun ω => Xs hA81 S c t0 Z0 M0 (t - t0 + 1) ω (Sum.inr r) := by
        funext ω
        simp only [φgen, show t0 ≤ t + 1 by omega, ↓reduceIte, Sum.elim_inr,
          show t + 1 - t0 = t - t0 + 1 by omega]
      rw [this]
      have := hXk1 (t - t0) (Sum.inr r)
      rwa [show t0 + (t - t0) = t by omega] at this
    · by_cases ht1 : t + 1 = t0
      · have : (fun ω => φgen hA81 S c t0 Z0 M0 (t + 1) ω (Sum.inr r)) =
            fun ω => M0 ω r := by
          funext ω
          simp only [φgen, ht1, le_refl, ↓reduceIte, Sum.elim_inr, Nat.sub_self, Xs]
        rw [this]
        have := hMk r
        rwa [show t0 - 1 = t by omega] at this
      · have : (fun ω => φgen hA81 S c t0 Z0 M0 (t + 1) ω (Sum.inr r)) = fun _ => 0 := by
          funext ω
          simp only [φgen, show ¬ t0 ≤ t + 1 by omega, ↓reduceIte, Pi.zero_apply]
        rw [this]
        exact stronglyMeasurable_const
  · -- initial multipliers
    funext r
    simp only [φgen, le_refl, ↓reduceIte, Mpart, Sum.elim_inr, Nat.sub_self, Xs]
  · -- (1.9)
    filter_upwards [gen_now hA81 (Z0 := Z0) (M0 := M0) hcb hca ht,
      gen_next hA81 hcb hca hZk hMk hXb ht] with ω h hn
    obtain ⟨hg, hy, hφ, -⟩ := h
    have hf := (sol_spec hA81 (Xs hA81 S c t0 Z0 M0 (t - t0) ω) hg).2.2.2.2 0 le_rfl ()
    rw [hn.2, hy, hφ]
    exact hf

/-- Woodford (2003), pp. 538–541 (the state of any solution): along every bounded solution, a.s.
at every date `t₀ + k`, the state `(Z_t, E_t M_{t−1})` equals the forecast-driven state `X_{t₀+k}`
(forecast paths are perfect-foresight solutions, `OptimalRulesMeasureForecast.fc_focSystem`, and
the next state is the kernel series). -/
theorem state_eq_of_sol (hcb : MBoundedV S c) (hca : MAdaptedV S c)
    (hMk : MKnownV S (t0 - 1) M0) {y : ℕ → Ω → (ιZ ⊕ ιz) ⊕ Unit → ℝ}
    {φ : ℕ → Ω → ιZ ⊕ ιz → ℝ} (h : MFOCSystem S P c t0 Z0 M0 y φ) :
    ∀ k, ∀ᵐ ω ∂S.μ, Sum.elim (Zpart (y (t0 + k) ω)) (Mpart (EVm S (t0 + k) (φ (t0 + k)) ω)) =
      Xs hA81 S c t0 Z0 M0 k ω := by
  have hcb' := hcb
  obtain ⟨Kc, hKc⟩ := hcb'
  obtain ⟨_, hRN⟩ := rser_spec (KN_summable hA81) hcb hca
  have hyi := integrable_of_adapted h.1.2.2.1 h.1.2.2.2
  obtain ⟨Kφ, hKφ⟩ := h.2.1
  have hφi : ∀ t i, Integrable (fun ω => φ t ω i) S.μ := fun t i =>
    integrable_of_bound (h.2.2.1 t i) ((hKφ t).mono fun ω hh => hh i)
  intro k
  induction k with
  | zero =>
    have hM : ∀ r, S.E t0 (fun ω => φ t0 ω (Sum.inr r)) =ᵐ[S.μ] fun ω => M0 ω r := by
      intro r
      have he : (fun ω => φ t0 ω (Sum.inr r)) =ᵐ[S.μ] fun ω => M0 ω r :=
        h.2.2.2.2.1.mono fun ω e => congrFun e r
      have hmi : Integrable (fun ω => M0 ω r) S.μ := (hφi t0 (Sum.inr r)).congr he
      exact (S.E_congr he t0).trans (by
        rw [S.E_of_stronglyMeasurable ((hMk r).mono (S.𝓕.mono (Nat.sub_le t0 1))) hmi])
    filter_upwards [h.1.2.1, ae_all_iff.2 hM] with ω e1 e2
    rw [Nat.add_zero]
    simp only [Xs]
    rw [e1]
    congr 1
    funext r
    exact e2 r
  | succ k ih =>
    set t := t0 + k with htdef
    have ht : t0 ≤ t := Nat.le_add_right t0 k
    -- `Z_{t+1}` is a.s. its own forecast at `t`
    have hZf : ∀ᵐ ω ∂S.μ, Zpart (EVm S t (y (t + 1)) ω) = Zpart (y (t + 1) ω) := by
      have hk : MKnownV S t (fun ω => P.sys.A11 *ᵥ Zpart (y t ω) + P.sys.A12 *ᵥ zpart (y t ω)) :=
        fun j => sm_comp (h.1.2.2.2 t)
          (g := fun v => (P.sys.A11 *ᵥ Zpart v + P.sys.A12 *ᵥ zpart v) j)
          (by unfold Zpart zpart; fun_prop)
      have hi : ∀ j, Integrable (fun ω => (P.sys.A11 *ᵥ Zpart (y t ω) +
          P.sys.A12 *ᵥ zpart (y t ω)) j) S.μ := fun j =>
        (integrable_mulVec _ (fun i => hyi t _) j).add (integrable_mulVec _ (fun i => hyi t _) j)
      filter_upwards [EVm_congr S t (x := fun ω => Zpart (y (t + 1) ω)) (h.1.1 t ht).1,
        (h.1.1 t ht).1] with ω e1 e2
      change EVm S t (fun ω => Zpart (y (t + 1) ω)) ω = _
      rw [e1, EVm_of_known S hk hi, e2]
    filter_upwards [ih, fc_focSystem P h ht, chat_bdd hKc t,
      ae_all_iff.2 fun a => (hRN t).2.2 t a, hZf] with ω e hf hc eN eZ
    have hg : BddSeq (chat S c t ω) := ⟨Kc, hc⟩
    set st := Sum.elim (Zpart (y t ω)) (Mpart (EVm S t (φ t) ω)) with hst
    have hpf : PFSol P st (chat S c t ω) (fun k _ => EVm S t (y (t + k)) ω)
        (fun k _ => EVm S t (φ (t + k)) ω) := hf
    have hu := sol_unique hA81 hg hpf 1
    have cN : EVm S t (Rser (KN hA81) c t) ω = nextS hA81 st (chat S c t ω) - nextS hA81 st 0 :=
      funext fun a => (eN a).unique ((Pi.hasSum.mp (nextS_hasSum hA81 st hg)) a)
    rw [show t0 + (k + 1) = t + 1 by omega]
    simp only [Xs]
    rw [← htdef, ← e, cN, add_sub_cancel]
    funext a
    rcases a with j | r
    · simp only [Sum.elim_inl, nextS]
      rw [← eZ, ← hu.1]
    · simp only [Sum.elim_inr, nextS]
      rw [mpart_EVm_of_le h.2.1 h.2.2.1 h.2.2.2.1 (Nat.le_succ t),
        ← mpart_EVm_of_le h.2.1 h.2.2.1 h.2.2.2.1 le_rfl, ← hu.2]

/-- Woodford (2003), **Assumption 8.1, p. 541 — the exact condition**: for every bounded adapted
disturbance, every `Z_{t₀}` known at `t₀` and every `M_{t₀−1}` known at `t₀ − 1`, (1.1) + (1.9) has
a bounded solution on the probability space **iff the forecast-driven state `X_t` (`Xs`) is
essentially bounded**; the solution is then a.s. unique (`m_focUnique_of_pf`). -/
theorem m_exists_iff (hcb : MBoundedV S c) (hca : MAdaptedV S c) (hZk : MKnownV S t0 Z0)
    (hMk : MKnownV S (t0 - 1) M0) :
    (∃ y φ, MFOCSystem S P c t0 Z0 M0 y φ) ↔
      ∃ K, ∀ k, ∀ᵐ ω ∂S.μ, ∀ i, |Xs hA81 S c t0 Z0 M0 k ω i| ≤ K := by
  refine ⟨fun ⟨y, φ, h⟩ => ?_, fun hX => ⟨_, _, gen_solves hA81 hcb hca hZk hMk hX⟩⟩
  obtain ⟨Ky, hKy⟩ := h.1.2.2.1
  obtain ⟨Kφ, hKφ⟩ := h.2.1
  refine ⟨max Ky Kφ, fun k => ?_⟩
  have hE : ∀ᵐ ω ∂S.μ, ∀ r, |EVm S (t0 + k) (φ (t0 + k)) ω (Sum.inr r)| ≤ Kφ :=
    ae_all_iff.2 fun r => S.abs_E_le ((hKφ (t0 + k)).mono fun ω hh => hh _) _
  filter_upwards [state_eq_of_sol hA81 hcb hca hMk h k, hKy (t0 + k), hE] with ω e h1 h2 i
  rw [← e]
  rcases i with j | r
  · exact (h1 _).trans (le_max_left _ _)
  · exact (h2 r).trans (le_max_right _ _)

/-! ### Sufficient conditions: geometric stability and the root condition -/

/-- Woodford (2003), p. 539 and App. G.1, (G.5): **if `H` is geometrically stable, the
forecast-driven state is essentially bounded** for every bounded adapted disturbance and bounded
initial conditions. -/
theorem xs_bdd_of_powDecay (hstab : PencilSplit.PowDecay (Hgen hA81)) (hcb : MBoundedV S c)
    (hca : MAdaptedV S c) (hZb : MBoundedRV S Z0) (hMb : MBoundedRV S M0) :
    ∃ K, ∀ k, ∀ᵐ ω ∂S.μ, ∀ i, |Xs hA81 S c t0 Z0 M0 k ω i| ≤ K := by
  obtain ⟨KZ, hKZ⟩ := hZb
  obtain ⟨KM, hKM⟩ := hMb
  obtain ⟨KRN, hRN⟩ := rser_spec (KN_summable hA81) hcb hca
  have hEN : ∀ t, ∀ᵐ ω ∂S.μ, ∀ a, |EVm S t (Rser (KN hA81) c t) ω a| ≤ KRN := fun t =>
    ae_all_iff.2 fun a => S.abs_E_le ((hRN t).2.1.mono fun _ h => h a) t
  obtain ⟨K, hK⟩ := bounded_rec hstab (max KZ KM) (∑ i, |hgen hA81 i| + KRN)
  refine ⟨K, fun k => ?_⟩
  filter_upwards [hKZ, hKM, ae_all_iff.2 fun j => hEN (t0 + j)] with ω h1 h2 h3
  refine hK (fun k => Xs hA81 S c t0 Z0 M0 k ω)
    (fun k => hgen hA81 + EVm S (t0 + k) (Rser (KN hA81) c (t0 + k)) ω) ?_ ?_ ?_ k
  · intro i
    rcases i with j | r
    · exact (h1 j).trans (le_max_left _ _)
    · exact (h2 r).trans (le_max_right _ _)
  · intro k i
    refine (abs_add_le _ _).trans (add_le_add ?_ (h3 k i))
    exact Finset.single_le_sum (f := fun i => |hgen hA81 i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)
  · intro k
    simp only [Xs]
    rw [hgen_spec]
    abel

variable (S t0)

/-- Woodford (2003), **Assumption 8.1 (existence)**, p. 541, **for every bounded adapted
disturbance on every filtered probability space**, when `H` is geometrically stable: the
candidate solves (1.1) + (1.9). -/
theorem m_focSolvableMB_of_powDecay (hstab : PencilSplit.PowDecay (Hgen hA81)) :
    MFOCSolvableMB S P t0 := by
  intro c Z0 M0 hcb hca hZk hZb hMb hMk
  exact ⟨_, _, gen_solves hA81 hcb hca hZk hMk (xs_bdd_of_powDecay hA81 hstab hcb hca hZb hMb)⟩

/-- Woodford (2003), **Assumption 8.1**, p. 541 (bounded initial conditions, predetermined initial
multiplier), **on every filtered probability space, for every bounded adapted disturbance**: from
the perfect-foresight Assumption 8.1 and geometric stability of `H` (existence) — uniqueness needs
only the perfect-foresight assumption. -/
theorem m_assumption81MB_of_powDecay (hstab : PencilSplit.PowDecay (Hgen hA81)) :
    MAssumption81MB S P t0 :=
  ⟨m_focSolvableMB_of_powDecay hA81 S t0 hstab, m_focUnique_of_pf hA81.unique S t0⟩

variable {S t0}

/-- Woodford (2003), p. 539 (tool): along the perfect-foresight solution with zero forcing, the
date-`k` values are the date-0 values from the `k`-th iterate of the zero-forcing state map. -/
theorem iter_sol (k : ℕ) (n : ιZ ⊕ ιz → ℝ) :
    solY hA81 n 0 k = solY hA81 ((fun m => nextS hA81 m 0)^[k] n) 0 0 ∧
      solΦ hA81 n 0 k = solΦ hA81 ((fun m => nextS hA81 m 0)^[k] n) 0 0 := by
  induction k generalizing n with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    have hs := sol_shift hA81 n (bddSeq_zero (ι := ιz)) k
    have h0 : (fun j => (0 : ℕ → ιz → ℝ) (j + 1)) = 0 := rfl
    rw [h0] at hs
    rw [hs.1, hs.2, (ih _).1, (ih _).2, Function.iterate_succ_apply]
    exact ⟨rfl, rfl⟩

/-- Woodford (2003), App. G.1 (tool): a state is recovered from the date-0 values of its own
solution (`Z_0 = Z`, `M_{−1} = M`). -/
theorem state_of_sol (n : ιZ ⊕ ιz → ℝ) {g : ℕ → ιz → ℝ} (hg : BddSeq g) :
    n = Sum.elim (Zpart (solY hA81 n g 0)) (Mpart (solΦ hA81 n g 0)) := by
  have hZ := (sol_spec hA81 n hg).1.2.1 ()
  have hM := (sol_spec hA81 n hg).2.2.2.1 ()
  funext a
  rcases a with j | r
  · exact (congrFun hZ j).symm
  · exact (congrFun hM r).symm

/-- Woodford (2003), Assumption 8.1, p. 541: **the perfect-foresight Assumption 8.1 makes `H`
power-bounded** (`OptimalRulesMeasureMarkov.PowBdd`): the zero-forcing solution from every state is
bounded, and its states are the iterates `h + H(…)`. -/
theorem powBdd_Hgen : OptimalRulesMeasureMarkov.PowBdd (Hgen hA81) := by
  set f : (ιZ ⊕ ιz → ℝ) → ιZ ⊕ ιz → ℝ := fun m => nextS hA81 m 0 with hf
  have hb : ∀ n, ∃ M, ∀ k i, |f^[k] n i| ≤ M := by
    intro n
    obtain ⟨M, hM⟩ := sol_bdd hA81 n (bddSeq_zero (ι := ιz))
    refine ⟨M, fun k i => ?_⟩
    rw [state_of_sol hA81 (f^[k] n) (bddSeq_zero (ι := ιz)), ← (iter_sol hA81 k n).1,
      ← (iter_sol hA81 k n).2]
    rcases i with j | r
    · exact (hM k).1 _
    · exact (hM k).2 _
  have hdiff : ∀ k n, f^[k] n - f^[k] 0 = Hgen hA81 ^ k *ᵥ n := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [hf]
      rw [hgen_spec, hgen_spec]
      have := ih n
      rw [pow_succ', ← mulVec_mulVec, ← this, mulVec_sub]
      abel
  choose Mf hMf using hb
  refine ⟨∑ j, |Mf (Pi.single j 1)| + |Mf 0|, fun k i j => ?_⟩
  have h1 : (Hgen hA81 ^ k) i j = (f^[k] (Pi.single j 1) - f^[k] 0) i := by
    rw [hdiff, mulVec_single_one]
    rfl
  rw [h1, Pi.sub_apply]
  refine (abs_sub _ _).trans (add_le_add ?_ ((hMf 0 k i).trans (le_abs_self _)))
  exact ((hMf _ k i).trans (le_abs_self _)).trans
    (Finset.single_le_sum (f := fun j => |Mf (Pi.single j 1)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j))

omit [Fintype ιZ] [Fintype ιz] [Fintype ιτ] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), App. G.1 (tool): **a power-bounded real matrix with no eigenvalue on the unit
circle has geometrically decaying powers** (eigenvalues of a power-bounded matrix lie in the
closed unit disc; Gelfand's formula, `PencilSplit.powDecay_of_eig`). -/
theorem powDecay_of_powBdd_noUnit {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℝ}
    (hb : OptimalRulesMeasureMarkov.PowBdd H)
    (hu : ∀ w : ℂ, ‖w‖ = 1 → (Matrix.scalar ι w - H.map Complex.ofReal).det ≠ 0) :
    PencilSplit.PowDecay H := by
  refine PencilSplit.powDecay_of_eig H fun w hw => ?_
  by_contra hlt
  push Not at hlt
  rcases eq_or_lt_of_le hlt with h1 | h1
  · exact hu w h1.symm hw
  obtain ⟨K, hK⟩ := hb
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hw
  set Hc := H.map Complex.ofReal with hHc
  have hHv : Hc *ᵥ v = w • v := by
    rw [sub_mulVec] at hv
    have hs : Matrix.scalar ι w *ᵥ v = w • v := by
      rw [Matrix.scalar_apply]
      funext i
      rw [mulVec_diagonal]
      simp
    rw [hs] at hv
    exact (sub_eq_zero.mp hv).symm
  have hpow : ∀ k, Hc ^ k *ᵥ v = w ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hHv, smul_smul, pow_succ', mul_comm]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hvi : 0 < ‖v i‖ := norm_pos_iff.mpr hi
  set C := ∑ j, |K| * ‖v j‖ with hC
  have hbound : ∀ k, ‖w‖ ^ k * ‖v i‖ ≤ C := by
    intro k
    have e := congrFun (hpow k) i
    have hmap : Hc ^ k = (H ^ k).map Complex.ofReal := by
      rw [hHc]
      exact (Matrix.map_pow H Complex.ofRealHom k).symm
    rw [hmap] at e
    have : ‖w ^ k • v i‖ ≤ C := by
      rw [← Pi.smul_apply, ← e]
      calc ‖((H ^ k).map Complex.ofReal *ᵥ v) i‖
          = ‖∑ j, ((H ^ k) i j : ℂ) * v j‖ := rfl
        _ ≤ ∑ j, ‖((H ^ k) i j : ℂ) * v j‖ := norm_sum_le _ _
        _ ≤ C := Finset.sum_le_sum fun j _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right ((hK k i j).trans (le_abs_self _)) (norm_nonneg _)
    rwa [norm_smul, norm_pow] at this
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (C / ‖v i‖) h1
  have := hbound k
  rw [div_lt_iff₀ hvi] at hk
  linarith

/-- Woodford (2003), Assumption 8.1, p. 541, **under the root condition**: if `H` has no
eigenvalue on the unit circle, it is geometrically stable (it is power-bounded by the
perfect-foresight Assumption 8.1, `powBdd_Hgen`). -/
theorem powDecay_Hgen_of_noUnit
    (hu : ∀ w : ℂ, ‖w‖ = 1 → (Matrix.scalar (ιZ ⊕ ιz) w - (Hgen hA81).map Complex.ofReal).det ≠ 0) :
    PencilSplit.PowDecay (Hgen hA81) :=
  powDecay_of_powBdd_noUnit (powBdd_Hgen hA81) hu

variable (S t0)

/-- Woodford (2003), **Assumption 8.1**, p. 541, **from the perfect-foresight Assumption 8.1 and
the root condition** (no eigenvalue of `H` on the unit circle): it holds on every filtered
probability space, for every bounded adapted disturbance (bounded initial conditions, predetermined
initial multiplier). -/
theorem m_assumption81MB_of_noUnit
    (hu : ∀ w : ℂ, ‖w‖ = 1 → (Matrix.scalar (ιZ ⊕ ιz) w - (Hgen hA81).map Complex.ofReal).det ≠ 0) :
    MAssumption81MB S P t0 :=
  m_assumption81MB_of_powDecay hA81 S t0 (powDecay_Hgen_of_noUnit hA81 hu)

/-! ### Proposition 8.2 for every disturbance -/

/-- Woodford (2003), **Proposition 8.2**, p. 555, **for every bounded adapted disturbance on every
filtered probability space**: under the perfect-foresight Assumption 8.1, geometric stability of
`H` (e.g. the root condition, `powDecay_Hgen_of_noUnit`), a deflating split with Assumption 8.5
and a consistent bounded adapted history, commitment to the target criterion (1.23) determines
exactly one bounded equilibrium a.s., and it is the solution of (1.1) + (1.9) (hence optimal,
`OptimalRulesMeasure.m_optimalSubjectTo_of_focSystem`). -/
theorem m_prop82_general (hstab : PencilSplit.PowDecay (Hgen hA81))
    (Dsp : PencilSplit.DeflatingSplit P.sys P.β)
    (h85 : TargetCriterion.Krylov.Assumption85b (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2)
    {D : ℕ} (hD : D + 1 ≤ t0)
    (hB : ∀ i c, (Adjugate.Bpoly (PencilSplit.Λmat P.sys P.β Dsp.J) i c).natDegree ≤ D)
    (hα : (Adjugate.alpha (PencilSplit.Λmat P.sys P.β Dsp.J)).natDegree ≤ D)
    {Mh qh : ℕ → Ω → ιz → ℝ} {vh : ℕ → Ω → ℝ}
    (hhist : HistoryOKm S (PencilSplit.Λmat P.sys P.β Dsp.J) P.sys.B2 t0 D Mh qh vh)
    (hMhb : MBoundedV S Mh) (hMhk : MAdaptedV S Mh) (hqhb : MBoundedV S qh)
    (hvhb : ∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |vh t ω| ≤ K) (hcb : MBoundedV S c) (hca : MAdaptedV S c)
    (hZk : MKnownV S t0 Z0) (hZb : MBoundedRV S Z0) :
    ∃ y, MFeasible S P c t0 Z0 y ∧ MCriterion P Dsp S D t0 qh vh y ∧
      (∀ y', MFeasible S P c t0 Z0 y' → MCriterion P Dsp S D t0 qh vh y' →
        ∀ t, t0 ≤ t → y' t =ᵐ[S.μ] y t) ∧
      ∃ φ, MFOCSystem S P c t0 Z0 (Mh (t0 - 1)) y φ := by
  have hMb : MBoundedRV S (Mh (t0 - 1)) := by
    obtain ⟨K, hK⟩ := hMhb
    exact ⟨K, hK (t0 - 1)⟩
  have hM0 : ∀ r, AEStronglyMeasurable[S.𝓕 t0] (fun ω => Mh (t0 - 1) ω r) S.μ := fun r =>
    ((hMhk (t0 - 1) r).mono (S.𝓕.mono (Nat.sub_le t0 1))).aestronglyMeasurable
  obtain ⟨y, φ, hsol⟩ := m_focSolvableMB_of_powDecay hA81 S t0 hstab c Z0 (Mh (t0 - 1)) hcb hca
    hZk hZb hMb (hMhk (t0 - 1))
  refine ⟨y, hsol.1, m_criterion P Dsp hD hB hα hhist hsol hM0, fun y' hy' hc' t ht => ?_,
    φ, hsol⟩
  exact OptimalRulesMeasureConverse.m_criterion_eq_foc (m_focUnique_of_pf hA81.unique S t0) h85
    hD hB hα hhist hMhb hMhk hqhb hvhb hsol hy' hc' t ht


/-! ### Link with the core: perfect foresight -/

omit [Fintype ιZ] [Fintype ιz] [DecidableEq ιZ] [DecidableEq ιz] in
/-- Woodford (2003), p. 540 (tool): on the one-point probability space every random vector is
known at every date. -/
theorem unit_known {ι : Type*} (t : ℕ) (x : Unit → ι → ℝ) : MKnownV Bridge.unitSystem t x :=
  fun i => stronglyMeasurable_const' fun a b => by rcases a; rcases b; rfl

/-- Woodford (2003), Assumption 8.1, p. 541 (link with the core): **on the one-point probability
space (perfect foresight) the exact condition always holds** — the forecast-driven state is
bounded for every bounded disturbance path and all initial conditions, because the core
perfect-foresight Assumption 8.1 provides a solution (`Bridge.unit_mFOCSystem_iff`). So the
measure-theoretic existence theory reduces to the core statement there. -/
theorem xs_bdd_unit (c : ℕ → Unit → ιz → ℝ) (hcb : BoundedV c) (Z0 : Unit → ιZ → ℝ)
    (M0 : Unit → ιz → ℝ) :
    ∃ K, ∀ k, ∀ᵐ ω ∂Bridge.unitSystem.μ, ∀ i, |Xs hA81 Bridge.unitSystem c 0 Z0 M0 k ω i| ≤ K := by
  obtain ⟨y, φ, h⟩ := hA81.solvable c Z0 M0 hcb (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨Kc, hKc⟩ := hcb
  refine (m_exists_iff hA81 (S := Bridge.unitSystem) ⟨Kc, fun t => Eventually.of_forall
    fun ω i => hKc t ω i⟩ (fun t => unit_known t (c t)) (unit_known 0 Z0)
    (unit_known (0 - 1) M0)).mp ⟨y, φ, (Bridge.unit_mFOCSystem_iff P c 0 Z0 M0 y φ).mpr h⟩

end Woodford.OptimalPolicyRules.OptimalRulesMeasureGeneral
