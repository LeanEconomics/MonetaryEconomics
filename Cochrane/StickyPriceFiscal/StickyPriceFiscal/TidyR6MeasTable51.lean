/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceFiscal.TidyR6MeasFiscalNK

/-!
# Table 5.1's exact statements in a probability model

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 5, §5.5, Table 5.1, p. 153, with
the identities (3.20)–(3.22) (Ch. 3, p. 65) behind its three panels, and the exact claims of
§§5.5.2–5.5.3 (pp. 150–155) that Table 5.1 reports, restated with **measure-theoretic
expectations** (`ExpectationsMeasure.MeasExpectationSystem`, a.e. equations). `PolicyRules`
proves them for the abstract `ExpectationSystem` only; the numerical entries
(`PolicyRules.lamS_bookRules`,
`PolicyRules.table51_fiscal_yesRule_etaS`, …) involve no expectations and are unchanged.

## Main results

* Innovation calculus a.e.: `minnov_smul`, `minnov_sub`, `minnov_add`, `minnov_known`,
  `mabs_innov_le`, `minnov_tsum` (the innovation passes through a geometrically dominated
  series).
* (3.18)–(3.19): `mpv_identity` (bounded debt is the present value of surpluses less returns,
  a.e.), `minnov_pv_next`.
* **(3.20) `midentity_320`, (3.21) `midentity_321`, (3.22) `midentity_322`** (the three panels of
  Table 5.1), `mpv_surplus_innov_zero` (p. 152).
* §§5.5.2–5.5.3: `mfiscal_ar1` (after fiscal shocks only, `x = gπ` and `E_t π_{t+1} = λ_s π_t`),
  `munexpected_output`, `mno_inflation_of_betaS_zero`, `mbonds_zero_noRule`,
  **`mfiscal_shock_sums`** ((5.75): the `ω`-weighted inflation news is `−β_s/(1 − ωλ_s) ε_s` and
  the `ρ`-discounted disturbance news is `ε_s/(1 − ρη_s)`), `mbetaS_of_ratio` ((5.80)).
-/

namespace Cochrane.StickyPriceFiscal.TidyR6MeasTable51

open MeasureTheory Filter Topology ExpectationsMeasure PolicyRules PolicyRulesMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : MeasExpectationSystem Ω)

/-! ### Innovation calculus -/

/-- Cochrane (2023), eq. (2.13), p. 30 (tool): `ΔE_{t+1}(a x) = a ΔE_{t+1} x` a.e. -/
theorem minnov_smul (a : ℝ) (x : Ω → ℝ) (t : ℕ) :
    S.innov t (a • x) =ᵐ[S.μ] a • S.innov t x := by
  filter_upwards [S.E_smul a x (t + 1), S.E_smul a x t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, e1, e2]
  ring

/-- Cochrane (2023), eq. (2.13), p. 30 (tool): `ΔE_{t+1}(x − y) = ΔE_{t+1}x − ΔE_{t+1}y` a.e. -/
theorem minnov_sub {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.innov t (x - y) =ᵐ[S.μ] S.innov t x - S.innov t y := by
  filter_upwards [S.E_sub hx hy (t + 1), S.E_sub hx hy t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, e1, e2]
  ring

/-- Cochrane (2023), eq. (2.13), p. 30 (tool): `ΔE_{t+1}(x + y) = ΔE_{t+1}x + ΔE_{t+1}y` a.e. -/
theorem minnov_add {x y : Ω → ℝ} (hx : Integrable x S.μ) (hy : Integrable y S.μ) (t : ℕ) :
    S.innov t (x + y) =ᵐ[S.μ] S.innov t x + S.innov t y := by
  filter_upwards [S.E_add hx hy (t + 1), S.E_add hx hy t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply, Pi.add_apply, e1, e2]
  ring

/-- Cochrane (2023), eq. (2.13), p. 30 (tool): what is known at `t` has no news,
`ΔE_{t+1} x = 0`. -/
theorem minnov_known {t : ℕ} {x : Ω → ℝ} (hx : StronglyMeasurable[S.𝓕 t] x)
    (hi : Integrable x S.μ) : S.innov t x = 0 := by
  simp only [MeasExpectationSystem.innov, S.E_of_stronglyMeasurable hx hi,
    S.E_of_stronglyMeasurable (hx.mono (S.𝓕.mono (Nat.le_succ t))) hi, sub_self]

/-- Cochrane (2023), eq. (2.13), p. 30 (tool): `|ΔE_{t+1} x| ≤ 2M` a.e. when `|x| ≤ M` a.e. -/
theorem mabs_innov_le {x : Ω → ℝ} {M : ℝ} (hx : ∀ᵐ ω ∂S.μ, |x ω| ≤ M) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, |S.innov t x ω| ≤ 2 * M := by
  filter_upwards [S.abs_E_le hx (t + 1), S.abs_E_le hx t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply]
  linarith [abs_sub (S.E (t + 1) x ω) (S.E t x ω)]

/-- Cochrane (2023), (3.20)–(3.22) (tool), **in a probability model**: the innovation commutes
with a geometrically dominated series, `ΔE_{t+1} ∑_k f_k = ∑_k ΔE_{t+1} f_k` a.e. -/
theorem minnov_tsum {a M : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : ℕ → Ω → ℝ}
    (hm : ∀ k, AEStronglyMeasurable (f k) S.μ) (hf : ∀ k, ∀ᵐ ω ∂S.μ, |f k ω| ≤ a ^ k * M)
    (t : ℕ) :
    S.innov t (fun ω => ∑' k, f k ω) =ᵐ[S.μ] fun ω => ∑' k, S.innov t (f k) ω := by
  have hc : Summable fun k => a ^ k * M := (summable_geometric_of_lt_one ha0 ha1).mul_right M
  filter_upwards [S.E_hasSum hc hm hf (t + 1), S.E_hasSum hc hm hf t] with ω e1 e2
  simp only [MeasExpectationSystem.innov, Pi.sub_apply]
  rw [e1.tsum_eq.symm, e2.tsum_eq.symm, ← e1.summable.tsum_sub e2.summable]

/-! ### (3.18)–(3.19): the present-value identity -/

/-- Cochrane (2023), (3.18)–(3.19), pp. 63–64, **in a probability model**: if
`ρ v_{t+1} = v_t + r_{t+1} − s_{t+1}` a.e. with bounded `v`, `r`, `s` and `0 ≤ ρ < 1`, then a.e.
`v_t = ∑_j ρʲ (s_{t+1+j} − r_{t+1+j})`. -/
theorem mpv_identity {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v r s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + r (t + 1) - s (t + 1)) (hbv : S.BddProc v)
    (hbs : S.BddProc s) (hbr : S.BddProc r) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, v t ω = ∑' j, ρ ^ j * (s (t + 1 + j) ω - r (t + 1 + j) ω) := by
  obtain ⟨Mv, hMv⟩ := hbv
  obtain ⟨Ms, hMs⟩ := hbs
  obtain ⟨Mr, hMr⟩ := hbr
  filter_upwards [ae_all_iff.2 hflow, ae_all_iff.2 hMv, ae_all_iff.2 hMs, ae_all_iff.2 hMr]
    with ω hfl hv hs hr
  have hsum : Summable fun j => ρ ^ j * (s (t + 1 + j) ω - r (t + 1 + j) ω) := by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_right (Ms + Mr))
      (fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 j)]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add (hs _) (hr _)))
      (pow_nonneg hρ0 j)
  have hpart : ∀ N, ∑ j ∈ Finset.range N, ρ ^ j * (s (t + 1 + j) ω - r (t + 1 + j) ω) =
      v t ω - ρ ^ N * v (t + N) ω := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have e := hfl (t + N)
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e
      rw [show t + (N + 1) = t + N + 1 by ring, show t + 1 + N = t + N + 1 by ring, pow_succ]
      linear_combination (ρ ^ N) * e
  have hlim : Tendsto (fun N => v t ω - ρ ^ N * v (t + N) ω) atTop (𝓝 (v t ω)) := by
    have h0 : Tendsto (fun N => ρ ^ N * v (t + N) ω) atTop (𝓝 0) := by
      have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const Mv
      rw [zero_mul] at hg
      refine squeeze_zero_norm (fun N => ?_) hg
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 N)]
      exact mul_le_mul_of_nonneg_left (hv _) (pow_nonneg hρ0 N)
    simpa using tendsto_const_nhds.sub h0
  have h1 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h1
  exact tendsto_nhds_unique hlim h1

/-- Cochrane (2023), (3.20)–(3.22) (tool), **in a probability model**: the news about next
period's debt is the discounted news about later surpluses less returns,
`ΔE_{t+1} v_{t+1} = ∑_j ρʲ (ΔE_{t+1} s_{t+2+j} − ΔE_{t+1} r_{t+2+j})` a.e. -/
theorem minnov_pv_next {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v r s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + r (t + 1) - s (t + 1)) (hbv : S.BddProc v)
    (hsa : StronglyAdapted S.𝓕 s) (hbs : S.BddProc s) (hra : StronglyAdapted S.𝓕 r)
    (hbr : S.BddProc r) (t : ℕ) :
    S.innov t (v (t + 1)) =ᵐ[S.μ] fun ω => ∑' j, ρ ^ j *
      (S.innov t (s (t + 1 + 1 + j)) ω - S.innov t (r (t + 1 + 1 + j)) ω) := by
  have hpv := mpv_identity S hρ0 hρ1 hflow hbv hbs hbr (t + 1)
  have hsi := int_of S hsa hbs
  have hri := int_of S hra hbr
  obtain ⟨Ms, hMs⟩ := hbs
  obtain ⟨Mr, hMr⟩ := hbr
  set f : ℕ → Ω → ℝ := fun j => ρ ^ j • (s (t + 1 + 1 + j) - r (t + 1 + 1 + j))
  have hfm : ∀ j, AEStronglyMeasurable (f j) S.μ := fun j =>
    ((((hsa (t + 1 + 1 + j)).mono (S.𝓕.le _)).sub ((hra (t + 1 + 1 + j)).mono
      (S.𝓕.le _))).const_smul (ρ ^ j)).aestronglyMeasurable
  have hfb : ∀ j, ∀ᵐ ω ∂S.μ, |f j ω| ≤ ρ ^ j * (Ms + Mr) := fun j => by
    filter_upwards [hMs (t + 1 + 1 + j), hMr (t + 1 + 1 + j)] with ω h1 h2
    simp only [f, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (pow_nonneg hρ0 j)]
    exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (pow_nonneg hρ0 j)
  have hv : v (t + 1) =ᵐ[S.μ] fun ω => ∑' j, f j ω := by
    filter_upwards [hpv] with ω e
    rw [e]
    rfl
  have hfj : ∀ j, S.innov t (f j) =ᵐ[S.μ] fun ω => ρ ^ j *
      (S.innov t (s (t + 1 + 1 + j)) ω - S.innov t (r (t + 1 + 1 + j)) ω) := fun j => by
    filter_upwards [minnov_smul S (ρ ^ j) (s (t + 1 + 1 + j) - r (t + 1 + 1 + j)) t,
      minnov_sub S (hsi (t + 1 + 1 + j)) (hri (t + 1 + 1 + j)) t] with ω e1 e2
    rw [e1, Pi.smul_apply, e2]
    rfl
  filter_upwards [S.E_congr hv (t + 1), S.E_congr hv t, minnov_tsum S hρ0 hρ1 hfm hfb t,
    ae_all_iff.2 hfj] with ω e1 e2 e3 e4
  have e0 : S.innov t (v (t + 1)) ω = S.innov t (fun ω => ∑' j, f j ω) ω := by
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, e1, e2]
  rw [e0, e3]
  exact tsum_congr fun j => e4 j

/-- Cochrane (2023), (3.21) (tool): the bond return `r^n` of a bounded adapted bond price is
adapted and bounded. -/
theorem rnSeq_adaptedM {w : ℝ} {q : ℕ → Ω → ℝ} (hqa : StronglyAdapted S.𝓕 q)
    (hqb : S.BddProc q) :
    StronglyAdapted S.𝓕 (rnSeq w q) ∧ S.BddProc (rnSeq w q) := by
  obtain ⟨M, hM⟩ := hqb
  refine ⟨fun t => ?_, ⟨|w| * M + M, fun t => ?_⟩⟩
  · cases t with
    | zero => exact stronglyMeasurable_zero
    | succ t => exact ((hqa (t + 1)).const_smul w).sub ((hqa t).mono (S.𝓕.mono (Nat.le_succ t)))
  · have hM0 : ∀ᵐ ω ∂S.μ, 0 ≤ M := (hM 0).mono fun ω h => (abs_nonneg _).trans h
    cases t with
    | zero =>
      filter_upwards [hM0] with ω h
      simp only [rnSeq, Pi.zero_apply, abs_zero]
      positivity
    | succ t =>
      filter_upwards [hM (t + 1), hM t] with ω h1 h2
      change |w * q (t + 1) ω - q t ω| ≤ _
      refine (abs_sub _ _).trans (add_le_add ?_ h2)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- **Identity (3.20)** in a probability model (Cochrane (2023), p. 65; Table 5.1, second panel,
p. 153): for bounded adapted `v, q, π, s̃` with the flow (5.71)
`ρ v_{t+1} = v_t + r_{t+1} − s̃_{t+1}` a.e. (`r = r^n − π`, `0 ≤ ρ < 1`), a.e.
`ΔE π_{t+1} − ΔE r^n_{t+1} = −∑_{j≥0} ρʲ ΔE s̃_{t+1+j} + ∑_{j≥1} ρʲ ΔE r_{t+1+j}`. -/
theorem midentity_320 {ρ w : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v q p s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + rSeq w q p (t + 1) - s (t + 1))
    (hva : StronglyAdapted S.𝓕 v) (hqa : StronglyAdapted S.𝓕 q) (hpa : StronglyAdapted S.𝓕 p)
    (hsa : StronglyAdapted S.𝓕 s) (hbv : S.BddProc v) (hbq : S.BddProc q) (hbp : S.BddProc p)
    (hbs : S.BddProc s) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, S.innov t (p (t + 1)) ω - S.innov t (rnSeq w q (t + 1)) ω =
      -(∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω) +
        ∑' j, ρ ^ (j + 1) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω := by
  obtain ⟨hrna, hrnb⟩ := rnSeq_adaptedM S (w := w) hqa hbq
  have hra : StronglyAdapted S.𝓕 (rSeq w q p) := fun t => (hrna t).sub (hpa t)
  have hbr : S.BddProc (rSeq w q p) := mbdd_sub S hrnb hbp
  have hIv := minnov_pv_next S hρ0 hρ1 hflow hbv hsa hbs hra hbr t
  have hvi := int_of S hva hbv
  have hsi := int_of S hsa hbs
  have hri := int_of S hra hbr
  have hpi := int_of S hpa hbp
  have hrni := int_of S hrna hrnb
  obtain ⟨Ms, hMs⟩ := hbs
  obtain ⟨Mr, hMr⟩ := hbr
  have hfl : S.innov t (ρ • v (t + 1)) =ᵐ[S.μ]
      S.innov t (v t + rSeq w q p (t + 1) - s (t + 1)) := by
    filter_upwards [S.E_congr (hflow t) (t + 1), S.E_congr (hflow t) t] with ω e1 e2
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, e1, e2]
  filter_upwards [hIv, hfl, minnov_smul S ρ (v (t + 1)) t,
    minnov_sub S ((hvi t).add (hri (t + 1))) (hsi (t + 1)) t, minnov_add S (hvi t) (hri (t + 1)) t,
    minnov_sub S (hrni (t + 1)) (hpi (t + 1)) t,
    ae_all_iff.2 fun k => mabs_innov_le S (hMs k) t,
    ae_all_iff.2 fun k => mabs_innov_le S (hMr k) t] with ω hI e1 e2 e3 e4 er hbs' hbr'
  rw [e2, e3, Pi.sub_apply, e4, Pi.add_apply, minnov_known S (hva t) (hvi t)] at e1
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_add] at e1
  rw [hI] at e1
  have erω : S.innov t (rSeq w q p (t + 1)) ω =
      S.innov t (rnSeq w q (t + 1)) ω - S.innov t (p (t + 1)) ω := by
    have := er
    simp only [Pi.sub_apply] at this
    exact this
  set a : ℕ → ℝ := fun j => S.innov t (s (t + 1 + 1 + j)) ω with ha
  set b : ℕ → ℝ := fun j => S.innov t (rSeq w q p (t + 1 + 1 + j)) ω with hb
  have hgeom : ∀ {g : ℕ → ℝ} {M : ℝ}, (∀ k, |g k| ≤ M) → Summable fun j => ρ ^ j * g j :=
    fun {g} {M} hg => Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hρ0 hρ1).mul_right M) (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hρ0 k)]
        exact mul_le_mul_of_nonneg_left (hg k) (pow_nonneg hρ0 k))
  have hsa' : Summable fun j => ρ ^ j * a j := hgeom fun k => hbs' _
  have hsb' : Summable fun j => ρ ^ j * b j := hgeom fun k => hbr' _
  have hsum0 : Summable fun j => ρ ^ j * S.innov t (s (t + 1 + j)) ω := hgeom fun k => hbs' _
  have e3' : ∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω =
      S.innov t (s (t + 1)) ω + ∑' j, ρ ^ (j + 1) * a j := by
    rw [hsum0.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero, ha]
    congr 1
    refine tsum_congr fun j => ?_
    rw [show t + 1 + (j + 1) = t + 1 + 1 + j by ring]
  have e4' : ρ * ∑' j, ρ ^ j * (a j - b j) =
      ∑' j, ρ ^ (j + 1) * a j - ∑' j, ρ ^ (j + 1) * b j := by
    have h1 : Summable fun j => ρ ^ (j + 1) * a j := (hsa'.mul_left ρ).congr (fun j => by ring)
    have h2 : Summable fun j => ρ ^ (j + 1) * b j := (hsb'.mul_left ρ).congr (fun j => by ring)
    rw [← h1.tsum_sub h2, ← tsum_mul_left]
    exact tsum_congr fun j => by ring
  have e5 : ∑' j, ρ ^ (j + 1) * b j =
      ∑' j, ρ ^ (j + 1) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω := by
    refine tsum_congr fun j => ?_
    rw [show t + 1 + (j + 1) = t + 1 + 1 + j by ring]
  rw [e3', ← e5]
  linarith

/-- Cochrane (2023) (tool): `ΔE_{t+1} 0 = 0`. -/
theorem minnov_zero (t : ℕ) : S.innov t (0 : Ω → ℝ) = 0 := by
  simp [MeasExpectationSystem.innov, S.E_zero]

/-- **Identity (3.21)** in a probability model (Cochrane (2023), p. 65; Table 5.1, third panel,
p. 153): for a bounded adapted bond price `q` and bounded adapted `π` (`0 ≤ ω < 1`), with
`r^n_{t+1} = ω q_{t+1} − q_t` and `r = r^n − π`, a.e.
`ΔE r^n_{t+1} = −∑_{j≥1} ωʲ ΔE r_{t+1+j} − ∑_{j≥1} ωʲ ΔE π_{t+1+j}`. -/
theorem midentity_321 {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) {q p : ℕ → Ω → ℝ}
    (hqa : StronglyAdapted S.𝓕 q) (hpa : StronglyAdapted S.𝓕 p) (hbq : S.BddProc q)
    (hbp : S.BddProc p) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, S.innov t (rnSeq w q (t + 1)) ω =
      -(∑' j, w ^ (j + 1) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω) -
        ∑' j, w ^ (j + 1) * S.innov t (p (t + 1 + (j + 1))) ω := by
  obtain ⟨hrna, hrnb⟩ := rnSeq_adaptedM S (w := w) hqa hbq
  have hra : StronglyAdapted S.𝓕 (rSeq w q p) := fun t => (hrna t).sub (hpa t)
  have hbr : S.BddProc (rSeq w q p) := mbdd_sub S hrnb hbp
  have hflow : ∀ t, w • q (t + 1) =ᵐ[S.μ] q t + rnSeq w q (t + 1) - (0 : ℕ → Ω → ℝ) (t + 1) :=
    fun t => Eventually.of_forall fun ω => by
      simp only [rnSeq, Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul]
      ring
  have hIq := minnov_pv_next S hw0 hw1 hflow hbq (fun t => stronglyMeasurable_zero) (mbdd_zero S)
    hrna hrnb t
  have hqi := int_of S hqa hbq
  have hpi := int_of S hpa hbp
  have hri := int_of S hra hbr
  obtain ⟨Mp, hMp⟩ := hbp
  obtain ⟨Mr, hMr⟩ := hbr
  have hsplit : ∀ k, S.innov t (rnSeq w q k) =ᵐ[S.μ] S.innov t (rSeq w q p k) + S.innov t (p k) :=
    fun k => by
      have e : rnSeq w q k = rSeq w q p k + p k := by simp [rSeq]
      rw [e]
      exact minnov_add S (hri k) (hpi k) t
  filter_upwards [hIq, minnov_sub S ((hqi (t + 1)).smul w) (hqi t) t,
    minnov_smul S w (q (t + 1)) t, ae_all_iff.2 hsplit,
    ae_all_iff.2 fun k => mabs_innov_le S (hMp k) t,
    ae_all_iff.2 fun k => mabs_innov_le S (hMr k) t] with ω e1 e2 e3 e4 hbp' hbr'
  have hrn : S.innov t (rnSeq w q (t + 1)) ω = w * S.innov t (q (t + 1)) ω := by
    change S.innov t (w • q (t + 1) - q t) ω = _
    rw [e2, Pi.sub_apply, e3, minnov_known S (hqa t) (hqi t)]
    simp
  rw [hrn, e1]
  simp only [minnov_zero, Pi.zero_apply, zero_sub]
  have hgeom : ∀ {g : ℕ → ℝ} {M : ℝ}, (∀ k, |g k| ≤ M) → Summable fun j => w ^ j * g j :=
    fun {g} {M} hg => Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hw0 hw1).mul_right M) (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hw0 k)]
        exact mul_le_mul_of_nonneg_left (hg k) (pow_nonneg hw0 k))
  have hsa : Summable fun j => w ^ j * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω :=
    hgeom fun k => hbr' _
  have hsb : Summable fun j => w ^ j * S.innov t (p (t + 1 + (j + 1))) ω :=
    hgeom fun k => hbp' _
  have h1 : Summable fun j => w ^ (j + 1) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω :=
    (hsa.mul_left w).congr (fun j => by ring)
  have h2 : Summable fun j => w ^ (j + 1) * S.innov t (p (t + 1 + (j + 1))) ω :=
    (hsb.mul_left w).congr (fun j => by ring)
  rw [← tsum_mul_left, ← tsum_neg, ← h1.neg.tsum_sub h2]
  refine tsum_congr fun j => ?_
  have e := e4 (t + 1 + 1 + j)
  simp only [Pi.add_apply] at e
  rw [show t + 1 + (j + 1) = t + 1 + 1 + j by ring, e]
  ring

/-- **Identity (3.22)** in a probability model (Cochrane (2023), p. 65; Table 5.1, first panel,
p. 153): under the hypotheses of (3.20) and (3.21) (`0 ≤ ω < 1`), a.e.
`∑_{j≥0} ωʲ ΔE π_{t+1+j} = −∑_{j≥0} ρʲ ΔE s̃_{t+1+j} + ∑_{j≥1} (ρʲ − ωʲ) ΔE r_{t+1+j}`. -/
theorem midentity_322 {ρ w : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    {v q p s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + rSeq w q p (t + 1) - s (t + 1))
    (hva : StronglyAdapted S.𝓕 v) (hqa : StronglyAdapted S.𝓕 q) (hpa : StronglyAdapted S.𝓕 p)
    (hsa : StronglyAdapted S.𝓕 s) (hbv : S.BddProc v) (hbq : S.BddProc q) (hbp : S.BddProc p)
    (hbs : S.BddProc s) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ∑' j, w ^ j * S.innov t (p (t + 1 + j)) ω =
      -(∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω) +
        ∑' j, (ρ ^ (j + 1) - w ^ (j + 1)) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω := by
  obtain ⟨hrna, hrnb⟩ := rnSeq_adaptedM S (w := w) hqa hbq
  have hbr : S.BddProc (rSeq w q p) := mbdd_sub S hrnb hbp
  obtain ⟨Mp, hMp⟩ := hbp
  obtain ⟨Mr, hMr⟩ := hbr
  filter_upwards [midentity_320 S hρ0 hρ1 hflow hva hqa hpa hsa hbv hbq ⟨Mp, hMp⟩ hbs t,
    midentity_321 S hw0 hw1 hqa hpa hbq ⟨Mp, hMp⟩ t,
    ae_all_iff.2 fun k => mabs_innov_le S (hMp k) t,
    ae_all_iff.2 fun k => mabs_innov_le S (hMr k) t] with ω e20 e21 hbp' hbr'
  have hgeom : ∀ {a : ℝ}, 0 ≤ a → a < 1 → ∀ {g : ℕ → ℝ} {M : ℝ}, (∀ k, |g k| ≤ M) →
      Summable fun j => a ^ j * g j :=
    fun {a} ha0 ha1 {g} {M} hg => Summable.of_norm_bounded
      ((summable_geometric_of_lt_one ha0 ha1).mul_right M) (fun k => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ha0 k)]
        exact mul_le_mul_of_nonneg_left (hg k) (pow_nonneg ha0 k))
  have hsp : Summable fun j => w ^ j * S.innov t (p (t + 1 + j)) ω := hgeom hw0 hw1 fun k => hbp' _
  have hsr1 : Summable fun j => ρ ^ (j + 1) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω :=
    ((hgeom hρ0 hρ1 (g := fun j => S.innov t (rSeq w q p (t + 1 + (j + 1))) ω)
      fun k => hbr' _).mul_left ρ).congr fun j => by ring
  have hsr2 : Summable fun j => w ^ (j + 1) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω :=
    ((hgeom hw0 hw1 (g := fun j => S.innov t (rSeq w q p (t + 1 + (j + 1))) ω)
      fun k => hbr' _).mul_left w).congr fun j => by ring
  have e5 : ∑' j, (ρ ^ (j + 1) - w ^ (j + 1)) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω =
      ∑' j, ρ ^ (j + 1) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω -
        ∑' j, w ^ (j + 1) * S.innov t (rSeq w q p (t + 1 + (j + 1))) ω := by
    rw [← hsr1.tsum_sub hsr2]
    exact tsum_congr fun j => by ring
  rw [hsp.tsum_eq_zero_add, e5]
  simp only [pow_zero, one_mul, add_zero]
  linarith

/-- Cochrane (2023), §5.5.2, p. 152 ("the discounted sum of all future surpluses would be exactly
zero"), **in a probability model**: if inflation and the bond price do not move, (3.20) forces the
discounted surplus news to vanish a.e. -/
theorem mpv_surplus_innov_zero {ρ w : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {v s : ℕ → Ω → ℝ}
    (hflow : ∀ t, ρ • v (t + 1) =ᵐ[S.μ] v t + rSeq w 0 0 (t + 1) - s (t + 1))
    (hva : StronglyAdapted S.𝓕 v) (hsa : StronglyAdapted S.𝓕 s) (hbv : S.BddProc v)
    (hbs : S.BddProc s) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, ∑' j, ρ ^ j * S.innov t (s (t + 1 + j)) ω = 0 := by
  have hz : StronglyAdapted S.𝓕 (0 : ℕ → Ω → ℝ) := fun t => stronglyMeasurable_zero
  filter_upwards [midentity_320 S hρ0 hρ1 hflow hva hz hz hsa hbv (mbdd_zero S) (mbdd_zero S) hbs t]
    with ω e
  have hr : ∀ k, rSeq w (0 : ℕ → Ω → ℝ) 0 k = 0 := by
    intro k
    cases k with
    | zero => simp [rSeq, rnSeq]
    | succ k => simp [rSeq, rnSeq]
  have hrn : rnSeq w (0 : ℕ → Ω → ℝ) (t + 1) = 0 := by simp [rnSeq]
  simp only [hr, hrn, minnov_zero, Pi.zero_apply, mul_zero, tsum_zero, sub_self] at e
  linarith

/-! ### §§5.5.2–5.5.3: the claims behind Table 5.1 -/

/-- Cochrane (2023), §§5.5.2–5.5.3, pp. 152 and 155 ("Inflation then decays with an AR(1)
pattern"), **in a probability model**: after fiscal shocks only (`ε_i = u_i = 0`), in every
bounded adapted solution of the block, `x_t = g π_t` and `E_t π_{t+1} = λ_s π_t` a.e. -/
theorem mfiscal_ar1 {P : Params} (hP : Standard P) (hpass : Passive P) (hηi : |P.etaI| < 1)
    {es us : ℕ → Ω → ℝ} (hsh : MShocks S P 0 es 0 us) {x p : ℕ → Ω → ℝ}
    (h : MBlock S P 0 es 0 x p) :
    (∀ t, x t =ᵐ[S.μ] gain P • p t) ∧ ∀ t, S.E t (p (t + 1)) =ᵐ[S.μ] lamS P • p t := by
  obtain ⟨-, hU, -, -, hsum, hprod⟩ := roots_passive hP hpass
  obtain ⟨h1, h2⟩ := mclosed S hP hU hsum hprod hηi hsh h
  obtain ⟨-, -, -, hxa, hpa, hxb, hpb⟩ := h
  have hsh' := hsh
  obtain ⟨hea, hesa, -, -, heb, hesb, -, -, -, -, -, -⟩ := hsh'
  refine ⟨fun t => ?_, fun t => ?_⟩
  · filter_upwards [h1 t] with ω e
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, sub_zero] at e
    exact e
  · have hp' : p (t + 1) =ᵐ[S.μ] lamS P • p t + xi P 0 es (t + 1) := by
      filter_upwards [h2 t] with ω e
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero,
        add_zero] at e ⊢
      exact e
    exact E_of_pred S hp' ((hpa t).const_smul _) ((int_of S hpa hpb t).smul _)
      (int_of S (xi_adaptedM S hea hesa) (xi_bddM S heb hesb) (t + 1)) (E_xiM S hsh t)

/-- Cochrane (2023), §5.5, p. 148 ("(5.51)–(5.52) then determine unexpected output"), **in a
probability model**: unexpected output is `g` times unexpected inflation less `σ/(λ_u − η_i)`
times the monetary shock, a.e. -/
theorem munexpected_output {P : Params} (hP : Standard P) (hpass : Passive P)
    (hηi : |P.etaI| < 1) {ei es ui us : ℕ → Ω → ℝ} (hsh : MShocks S P ei es ui us)
    {x p : ℕ → Ω → ℝ} (h : MBlock S P ei es ui x p) (t : ℕ) :
    S.innov t (x (t + 1)) =ᵐ[S.μ]
      gain P • S.innov t (p (t + 1)) - (P.sigma / (lamU P - P.etaI)) • ei (t + 1) := by
  obtain ⟨-, hU, -, -, hsum, hprod⟩ := roots_passive hP hpass
  obtain ⟨h1, -⟩ := mclosed S hP hU hsum hprod hηi hsh h
  obtain ⟨-, -, -, -, hpa, -, hpb⟩ := h
  have hsh' := hsh
  obtain ⟨hea, -, hua, -, heb, -, hub, -, hei, -, hul, -⟩ := hsh'
  have hpi := int_of S hpa hpb
  have hui := int_of S hua hub
  set c := P.sigma / (lamU P - P.etaI)
  have hx : x (t + 1) =ᵐ[S.μ] gain P • p (t + 1) - c • ui (t + 1) := h1 (t + 1)
  filter_upwards [S.E_congr hx (t + 1), S.E_congr hx t,
    minnov_sub S ((hpi (t + 1)).smul (gain P)) ((hui (t + 1)).smul c) t,
    minnov_smul S (gain P) (p (t + 1)) t, minnov_smul S c (ui (t + 1)) t,
    E_ar1M S hua hub hea heb hei hul t] with ω e1 e2 e3 e4 e5 e6
  have e0 : S.innov t (x (t + 1)) ω = S.innov t (gain P • p (t + 1) - c • ui (t + 1)) ω := by
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, e1, e2]
  rw [e0, e3, Pi.sub_apply, e4, e5]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MeasExpectationSystem.innov,
    E_self S hua hub (t + 1)]
  rw [e6, hul t]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Cochrane (2023), §5.5.2, p. 152 ("With `β_s = 0` … there would be no inflation"), **in a
probability model**: with no monetary disturbance, `β_s = 0` and `π_0 = 0`, inflation and output
are zero a.e. at every date in every equilibrium. -/
theorem mno_inflation_of_betaS_zero {P : Params} (hP : Standard P) (hpass : Passive P)
    (hηi : |P.etaI| < 1) (hβs : P.betaS = 0) {es us : ℕ → Ω → ℝ} (hsh : MShocks S P 0 es 0 us)
    {v0 : ℝ} {x p q v : ℕ → Ω → ℝ} (h : MRedEquil S P 0 es 0 us 0 v0 x p q v) :
    ∀ t, p t =ᵐ[S.μ] 0 ∧ x t =ᵐ[S.μ] 0 := by
  obtain ⟨⟨h64, h65, h68, -, -⟩, hxa, hpa, -, -, hxb, hpb, -, -, hp0, -⟩ := h
  have hblk : MBlock S P 0 es 0 x p := ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩
  obtain ⟨-, hU, -, -, hsum, hprod⟩ := roots_passive hP hpass
  obtain ⟨h1, h2⟩ := mclosed S hP hU hsum hprod hηi hsh hblk
  have hpz : ∀ t, p t =ᵐ[S.μ] 0 := by
    intro t
    induction t with
    | zero => exact hp0
    | succ t ih =>
      filter_upwards [h2 t, ih] with ω e1 e2
      rw [e1]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, xi_succ, hβs,
        Pi.sub_apply, Pi.neg_apply] at e2 ⊢
      rw [e2]
      ring
  intro t
  refine ⟨hpz t, ?_⟩
  filter_upwards [h1 t, hpz t] with ω e1 e2
  rw [e1]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at e2 ⊢
  rw [e2]
  ring

/-- Cochrane (2023), §5.5.2, p. 152 ("With neither monetary policy shock nor rule, the interest
rate … and long-term nominal bond return do not move"), **in a probability model**: with
`θ_iπ = θ_ix = 0`, `|ω| < 1` and no monetary disturbance, `q = 0` and `r^n = 0` a.e. -/
theorem mbonds_zero_noRule {P : Params} (hθπ : P.thIpi = 0) (hθx : P.thIx = 0)
    (hω : |P.omega| < 1) {es us : ℕ → Ω → ℝ} {p0 v0 : ℝ} {x p q v : ℕ → Ω → ℝ}
    (h : MRedEquil S P 0 es 0 us p0 v0 x p q v) :
    ∀ t, q t =ᵐ[S.μ] 0 ∧ rnNext P q t =ᵐ[S.μ] 0 := by
  obtain ⟨⟨-, -, -, -, h72⟩, -, -, hqa, -, -, -, hqb, -, -, -⟩ := h
  have hqs := (meq572_iff S hqa hqb).mp h72
  have hz : S.Solves P.omega (fun t => -iRule P x p (0 : ℕ → Ω → ℝ) t) (0 : ℕ → Ω → ℝ) :=
    fun t => Eventually.of_forall fun ω => by
      simp [iRule, hθπ, hθx, S.E_zero]
  have hq0 := S.forward_unique hω hqs hz
    (fun t => ((hqa t).mono (S.𝓕.le t)).aestronglyMeasurable)
    (fun t => aestronglyMeasurable_const) hqb (mbdd_zero S)
  intro t
  refine ⟨hq0 t, ?_⟩
  filter_upwards [hq0 t, hq0 (t + 1)] with ω e1 e2
  simp only [rnNext, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
  rw [e1, e2]
  ring

/-- Cochrane (2023), (5.75), p. 151 and Table 5.1 (the deficit-shock responses), **in a
probability model**: after fiscal shocks only, a.e. the news about `ω`-weighted inflation is
`−β_s/(1 − ωλ_s) ε_{s,t+1}` and the news about the `ρ`-discounted fiscal disturbance is
`ε_{s,t+1}/(1 − ρη_s)`. -/
theorem mfiscal_shock_sums {P : Params} (hP : Standard P) (hpass : Passive P)
    (hηi : |P.etaI| < 1) (hω0 : 0 ≤ P.omega) (hω1 : P.omega < 1) (hρ0 : 0 ≤ P.rho)
    (hρ1 : P.rho < 1) (hηs : |P.etaS| < 1) {es us : ℕ → Ω → ℝ} (hsh : MShocks S P 0 es 0 us)
    {p0 v0 : ℝ} {x p q v : ℕ → Ω → ℝ} (h : MRedEquil S P 0 es 0 us p0 v0 x p q v) (t : ℕ) :
    (S.innov t (fun ω => ∑' j, P.omega ^ j * p (t + 1 + j) ω) =ᵐ[S.μ]
        (-(P.betaS / (1 - P.omega * lamS P))) • es (t + 1)) ∧
      S.innov t (fun ω => ∑' j, P.rho ^ j * us (t + 1 + j) ω) =ᵐ[S.μ]
        (1 - P.rho * P.etaS)⁻¹ • es (t + 1) := by
  obtain ⟨⟨h64, h65, h68, -, -⟩, hxa, hpa, -, -, hxb, hpb, -, -, -, -⟩ := h
  have hblk : MBlock S P 0 es 0 x p := ⟨h64, h65, h68, hxa, hpa, hxb, hpb⟩
  obtain ⟨-, hEp⟩ := mfiscal_ar1 S hP hpass hηi hsh hblk
  have hsh' := hsh
  obtain ⟨-, hesa, -, husa, -, hesb, -, husb, -, hes, -, husl⟩ := hsh'
  obtain ⟨-, -, hl1, hl2, -, -⟩ := roots_passive hP hpass
  have hlam : |lamS P| < 1 := abs_lt.mpr ⟨hl1, hl2⟩
  have hwlam : |P.omega * lamS P| < 1 := by
    rw [abs_mul, abs_of_nonneg hω0]
    nlinarith [abs_nonneg (lamS P)]
  have hρη : |P.rho * P.etaS| < 1 := by
    rw [abs_mul, abs_of_nonneg hρ0]
    nlinarith [abs_nonneg P.etaS]
  have hpi := int_of S hpa hpb
  have hui := int_of S husa husb
  -- AR(1) forecasts: `E_s y_{s+k} = λᵏ y_s`
  have hEus : ∀ s, S.E s (us (s + 1)) =ᵐ[S.μ] P.etaS • us s := fun s => by
    filter_upwards [E_ar1M S husa husb hesa hesb hes husl s] with ω e
    rw [e]
    rfl
  have hEpk := fun s => TidyR6MeasFiscalNK.E_iter S hpa hpi hEp s
  have hEuk := fun s => TidyR6MeasFiscalNK.E_iter S husa hui hEus s
  -- the news of a weighted AR(1) sum
  have key : ∀ {y : ℕ → Ω → ℝ} {l a : ℝ}, StronglyAdapted S.𝓕 y → S.BddProc y →
      (∀ s k, S.E s (y (s + k)) =ᵐ[S.μ] l ^ k • y s) → 0 ≤ a → a < 1 → |a * l| < 1 →
      S.innov t (fun ω => ∑' j, a ^ j * y (t + 1 + j) ω) =ᵐ[S.μ]
        fun ω => (1 - a * l)⁻¹ * (y (t + 1) ω - l * y t ω) := by
    intro y l a hya hyb hyk ha0 ha1 hal
    obtain ⟨M, hM⟩ := hyb
    have hm : ∀ j, AEStronglyMeasurable (fun ω => a ^ j * y (t + 1 + j) ω) S.μ := fun j =>
      (((hya (t + 1 + j)).mono (S.𝓕.le _)).const_mul _).aestronglyMeasurable
    have hb : ∀ j, ∀ᵐ ω ∂S.μ, |a ^ j * y (t + 1 + j) ω| ≤ a ^ j * M := fun j => by
      filter_upwards [hM (t + 1 + j)] with ω e
      rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 j)]
      exact mul_le_mul_of_nonneg_left e (pow_nonneg ha0 j)
    have hinj : ∀ j, ∀ᵐ ω ∂S.μ, S.innov t (fun ω => a ^ j * y (t + 1 + j) ω) ω =
        (a * l) ^ j * (y (t + 1) ω - l * y t ω) := fun j => by
      filter_upwards [minnov_smul S (a ^ j) (y (t + 1 + j)) t, hyk (t + 1) j,
        hyk t (j + 1)] with ω e1 e2 e3
      have e1' : S.innov t (fun ω => a ^ j * y (t + 1 + j) ω) ω =
          a ^ j * S.innov t (y (t + 1 + j)) ω := e1
      rw [e1']
      simp only [MeasExpectationSystem.innov, Pi.sub_apply]
      rw [e2, show t + 1 + j = t + (j + 1) by ring, e3]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    filter_upwards [minnov_tsum S ha0 ha1 hm hb t, ae_all_iff.2 hinj] with ω e1 e2
    rw [e1]
    simp_rw [e2]
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hal]
  constructor
  · filter_upwards [key hpa hpb hEpk hω0 hω1 hwlam, h68 t, hEp t] with ω e1 e2 e3
    rw [e1]
    simp only [MeasExpectationSystem.innov, Pi.sub_apply, E_self S hpa hpb (t + 1), e3] at e2
    simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply, Pi.zero_apply,
      mul_zero, sub_zero] at e2 ⊢
    have hne : 1 - P.omega * lamS P ≠ 0 := by
      have := (abs_lt.mp hwlam).2
      linarith
    rw [e2]
    field_simp
  · filter_upwards [key husa husb hEuk hρ0 hρ1 hρη] with ω e1
    rw [e1, husl t]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), (5.75), p. 151 and (5.80), p. 154, **in a probability model**: at every state
where the fiscal shock is nonzero and the `ω`-weighted inflation news is `−0.4` times the
discounted disturbance news, `β_s = 0.4 (1 − ωλ_s)/(1 − ρη_s)`. -/
theorem mbetaS_of_ratio {P : Params} (hP : Standard P) (hpass : Passive P)
    (hηi : |P.etaI| < 1) (hω0 : 0 ≤ P.omega) (hω1 : P.omega < 1) (hρ0 : 0 ≤ P.rho)
    (hρ1 : P.rho < 1) (hηs : |P.etaS| < 1) {es us : ℕ → Ω → ℝ} (hsh : MShocks S P 0 es 0 us)
    {p0 v0 : ℝ} {x p q v : ℕ → Ω → ℝ} (h : MRedEquil S P 0 es 0 us p0 v0 x p q v) (t : ℕ) :
    ∀ᵐ ω ∂S.μ, es (t + 1) ω ≠ 0 →
      S.innov t (fun ω => ∑' j, P.omega ^ j * p (t + 1 + j) ω) ω =
        -(0.4 * S.innov t (fun ω => ∑' j, P.rho ^ j * us (t + 1 + j) ω) ω) →
      P.betaS = 0.4 * (1 - P.omega * lamS P) / (1 - P.rho * P.etaS) := by
  obtain ⟨h1, h2⟩ := mfiscal_shock_sums S hP hpass hηi hω0 hω1 hρ0 hρ1 hηs hsh h t
  obtain ⟨-, -, hl1, hl2, -, -⟩ := roots_passive hP hpass
  have hne1 : 1 - P.omega * lamS P ≠ 0 := by
    have : P.omega * lamS P < 1 := by nlinarith
    linarith
  have hne2 : 1 - P.rho * P.etaS ≠ 0 := by
    have : P.rho * P.etaS < 1 := by nlinarith [(abs_lt.mp hηs).2, (abs_lt.mp hηs).1]
    linarith
  filter_upwards [h1, h2] with ω e1 e2 hε hratio
  rw [e1, e2] at hratio
  simp only [Pi.smul_apply, smul_eq_mul] at hratio
  field_simp at hratio ⊢
  linarith

end Cochrane.StickyPriceFiscal.TidyR6MeasTable51
