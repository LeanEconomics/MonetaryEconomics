/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6ZExpectations
import KeynesianStickyPrices.PersistenceFreedom
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# (17.8) and the inverse of (17.14) with an infinite past under uncertainty

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.2, eqs. (17.7)–(17.8),
pp. 399–400, and §17.3, eq. (17.14), p. 405.

`StaticIS.eq_17_8` and `PersistenceFreedom.corrected_inverse` are pathwise statements on `ℤ`.
Here the rational-expectations model (17.7), `π_t = −σκ i_t + (1 + σκ) E_t π_{t+1}`, holds almost
surely at every date `t ∈ ℤ` on a probability space with a ℤ-indexed filtration
(`TidyR6ZExpectations.ZMeasExpectationSystem`, `REModelZ`). Write `a = 1/(1 + σκ)`,
`b = σκ/(1 + σκ)` and `δ_{t+1} = π_{t+1} − E_t π_{t+1}` (`err π t`), the expectational error.

## (17.8) under uncertainty: the equilibria are indexed by their expectational errors

* `rec_ae`: `π_{t+1} = a π_t + b i_t + δ_{t+1}` a.s.; `err_mds`: `δ` is a martingale difference
  sequence, `E_t δ_{t+1} = 0`, `δ_{t+1}` known at `t + 1`.
* **`eq_17_8_ae`**: every essentially bounded equilibrium is almost surely, at every date,
  `π_{t+1} = b ∑ aʲ i_{t−j} + ∑ aʲ δ_{t+1−j}`.
* **`piB_equilibrium`** (existence): for every essentially bounded adapted rate process and every
  essentially bounded martingale difference sequence `d` (`d_t` known at `t + 1`,
  `E_t d_t = 0`), the backward moving average `piB` is an adapted, essentially bounded
  equilibrium whose expectational errors are `d`. **`eq_piB`** (uniqueness): every essentially
  bounded equilibrium with expectational errors `d` equals `piB` a.s. at every date
  (`unique_of_err`). So the bounded equilibria on ℤ are exactly the bounded martingale
  difference sequences — the multiplicity of `StaticIS.re_not_unique` survives the infinite past.

## The role of the remote past (`t → −∞`)

* `remote_family`: for every integrable `c` known at every date (the remote past,
  `TidyR6ZExpectations.ZMeasExpectationSystem.remote`), `π_t + aᵗ c` is again an equilibrium with
  the same expectational errors; `remote_family_bdd_future`: it is bounded on `t ≥ 0`.
* `remote_converse`: every equilibrium with the same errors (only integrable) has this form,
  `π'_t − π_t = aᵗ (π'_0 − π_0)` with `π'_0 − π_0` known at every date, however early.
* `remote_family_bdd_iff`: `π_t + aᵗ c` is bounded on all of ℤ iff `c = 0` a.s. So uniqueness
  given the errors **needs the bound as `t → −∞`**: boundedness on `t ≥ 0` alone leaves a
  remote-past family (`remote_one_solves`: `c = 1` always qualifies).
* `finite_start_ae`, `tendsto_initial_term`: from any start `t − k`,
  `π_t = aᵏ π_{t−k} + ∑_{j<k} aʲ (b i_{t−1−j} + δ_{t−j})` (the ℕ-indexed news form started at
  `s = t − k`), and the initial term vanishes as `s → −∞`: the infinite-past formula is the
  limit of the finite-start ones.

## The inverse of (17.14) under uncertainty

* **`corrected_inverse_ae`**: almost surely at every date
  `E_t π_{t+1} = b ∑ aʲ i_{t−j} + ∑ a^{j+1} δ_{t−j}`.
* **`printed_inverse_iff`**: the printed inverse `E_t π_{t+1} = b ∑ aʲ i_{t−j}` holds a.s. at
  every date iff every expectational error is zero a.s.; under genuine uncertainty with any
  nonzero error it fails (`printed_inverse_fails`).

## The abstract ℤ system

`REModelZA` (for `TidyR6ZExpectations.ZExpectationSystem`) restricts at every date `s` to the
ℕ-indexed `StaticIS.REModel` of the restricted core system (`reModelZA_restrict`), and every
bounded equilibrium is (17.8) state by state (`eq_17_8_abstract`).
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6ZStaticIS

open MeasureTheory Filter Topology TidyR6ZExpectations ZMeasExpectationSystem

variable {Ω : Type*} [MeasurableSpace Ω] (S : ZMeasExpectationSystem Ω)

/-! ### A shift of backward sums -/

/-- Cochrane (2023), eq. (17.8), p. 400: for `|a| < 1` and bounded `f`, the backward sum satisfies
`∑ aʲ f_{t−j} = f_t + a ∑ aʲ f_{t−1−j}`.
Compare `SharedTools.backward_iterate` and `SharedTools.eq_backward_series`. -/
theorem backward_shift {a M : ℝ} (ha : |a| < 1) {f : ℤ → ℝ} (hf : ∀ s, |f s| ≤ M) (t : ℤ) :
    ∑' j : ℕ, a ^ j * f (t - j) = f t + a * ∑' j : ℕ, a ^ j * f (t - 1 - j) := by
  have hs : Summable fun j : ℕ => a ^ j * f (t - j) :=
    TidyR5ExpectationsMeasure.MeasExpectationSystem.summable_geom_mul ha fun j => hf (t - j)
  rw [hs.tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  congr 1
  refine tsum_congr fun j => ?_
  rw [pow_succ, show t - ((j + 1 : ℕ) : ℤ) = t - 1 - j by push_cast; ring]
  ring

/-! ### The model on ℤ -/

/-- Cochrane (2023), eq. (17.7), p. 399, on ℤ under uncertainty: inflation is adapted and
`π_t = −σκ i_t + (1 + σκ) E_t π_{t+1}` almost surely at every date `t ∈ ℤ`.
ℤ-indexed version of `StaticIS.REModel` under uncertainty. -/
def REModelZ (σ κ : ℝ) (i π : ℤ → Ω → ℝ) : Prop :=
  StronglyAdapted S.𝓕 π ∧
    ∀ t, π t =ᵐ[S.μ] (-(σ * κ)) • i t + (1 + σ * κ) • S.E t (π (t + 1))

/-- Cochrane (2023), eq. (17.8), p. 400: the expectational error
`δ_{t+1} = π_{t+1} − E_t π_{t+1}`.
ℤ-indexed version of `StaticIS.reErr`. -/
noncomputable def err (π : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ := π (t + 1) - S.E t (π (t + 1))

/-- Cochrane (2023), eq. (17.7), p. 399: in equilibrium `E_t π_{t+1} = a π_t + b i_t` a.s. -/
theorem E_next {σ κ : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ} (h : REModelZ S σ κ i π) (t : ℤ) :
    S.E t (π (t + 1)) =ᵐ[S.μ]
      (1 / (1 + σ * κ)) • π t + (σ * κ / (1 + σ * κ)) • i t := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  filter_upwards [h.2 t] with ω e
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  field_simp
  linarith

/-- Cochrane (2023), eq. (17.8), p. 400: `π_{t+1} = a π_t + b i_t + δ_{t+1}` a.s. -/
theorem rec_ae {σ κ : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ} (h : REModelZ S σ κ i π) (t : ℤ) :
    ∀ᵐ ω ∂S.μ, π (t + 1) ω =
      1 / (1 + σ * κ) * π t ω + σ * κ / (1 + σ * κ) * i t ω + err S π t ω := by
  filter_upwards [E_next S hσκ h t] with ω e
  simp only [err, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  rw [e]
  ring

/-- Cochrane (2023), eq. (17.8), p. 400: the expectational errors of an adapted, essentially
bounded inflation process form a martingale difference sequence: `δ_{t+1}` is known at `t + 1`
and `E_t δ_{t+1} = 0` a.s.
ℤ-indexed version of `StaticIS.reErr_mds`. -/
theorem err_mds {Mπ : ℝ} {π : ℤ → Ω → ℝ} (ha : StronglyAdapted S.𝓕 π)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (t : ℤ) :
    StronglyMeasurable[S.𝓕 (t + 1)] (err S π t) ∧ S.E t (err S π t) =ᵐ[S.μ] 0 := by
  have hi : Integrable (π (t + 1)) S.μ := S.integrable_of_bdd (ha (t + 1)) (hπ (t + 1))
  refine ⟨(ha (t + 1)).sub ((S.stronglyMeasurable_E t _).mono
    (S.𝓕.mono (Int.le_add_one le_rfl))), ?_⟩
  filter_upwards [S.E_sub hi (S.integrable_E t (π (t + 1))) t] with ω e
  rw [err, e, Pi.sub_apply, S.E_E_self, sub_self, Pi.zero_apply]

/-- Cochrane (2023), eq. (17.8): the expectational errors of an essentially bounded process are
essentially bounded by `2Mπ`.
As `TidyR5StochasticPaths.abs_innov_le`. -/
theorem err_bdd {Mπ : ℝ} {π : ℤ → Ω → ℝ} (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (t : ℤ) :
    ∀ᵐ ω ∂S.μ, |err S π t ω| ≤ 2 * Mπ := by
  filter_upwards [hπ (t + 1), S.abs_E_le (hπ (t + 1)) t] with ω e1 e2
  simp only [err, Pi.sub_apply]
  exact (abs_sub _ _).trans (by linarith)

/-- **(17.8) under uncertainty with an infinite past** (Cochrane (2023), eq. (17.8), p. 400): for
`σκ > 0`, every equilibrium of (17.7) on ℤ with essentially bounded inflation and rates is almost
surely, at every date, `π_{t+1} = b ∑_{j≥0} aʲ i_{t−j} + ∑_{j≥0} aʲ δ_{t+1−j}` with its own
expectational errors `δ`.
ℤ-indexed, almost-sure version of `StaticIS.eq_17_8`. -/
theorem eq_17_8_ae {σ κ Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ Mi) :
    ∀ᵐ ω ∂S.μ, ∀ t, π (t + 1) ω =
      σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) ω +
        ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * err S π (t - j) ω := by
  filter_upwards [ae_all_iff.2 (rec_ae S hσκ h), ae_all_iff.2 hπ, ae_all_iff.2 hi,
    ae_all_iff.2 (err_bdd S hπ)] with ω hr hbπ hbi hbe t
  have e := StaticIS.eq_17_8 hσκ (π := fun s => π s ω) (i := fun s => i s ω)
    (δ := fun s => err S π (s - 1) ω) hbπ hbi (fun s => hbe (s - 1))
    (fun s => by simpa only [add_sub_cancel_right] using hr s) t
  rw [e]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + 1 - (j : ℤ) - 1 = t - j by ring]

/-! ### Existence and uniqueness given the expectational errors -/

/-- Cochrane (2023), eq. (17.8), p. 400: the backward moving average with rates `i` and
expectational errors `d` (`d_t` the error of date `t + 1`),
`π_t = b ∑ aʲ i_{t−1−j} + ∑ aʲ d_{t−1−j}`. -/
noncomputable def piB (σ κ : ℝ) (i d : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ := fun ω =>
  σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - 1 - j) ω +
    ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * d (t - 1 - j) ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (17.8): the backward moving average satisfies
`π_{t+1} = a π_t + b i_t + d_t` wherever the rates and errors are bounded. -/
theorem piB_rec {σ κ Mi Md : ℝ} (hσκ : 0 < σ * κ) {i d : ℤ → Ω → ℝ} {ω : Ω}
    (hi : ∀ s, |i s ω| ≤ Mi) (hd : ∀ s, |d s ω| ≤ Md) (t : ℤ) :
    piB σ κ i d (t + 1) ω =
      1 / (1 + σ * κ) * piB σ κ i d t ω + σ * κ / (1 + σ * κ) * i t ω + d t ω := by
  obtain ⟨ha0, ha1, -, -⟩ := StaticIS.coeff_17_7 hσκ
  have haa : |1 / (1 + σ * κ)| < 1 := by rw [abs_of_pos ha0]; exact ha1
  have e1 := backward_shift haa (f := fun s => i s ω) hi t
  have e2 := backward_shift haa (f := fun s => d s ω) hd t
  simp only [piB, add_sub_cancel_right]
  rw [e1, e2]
  ring

/-- Cochrane (2023), eq. (17.8): the backward moving average is adapted when the rates are
adapted and `d_t` is known at `t + 1`. -/
theorem piB_adapted (σ κ : ℝ) {i d : ℤ → Ω → ℝ} (hia : StronglyAdapted S.𝓕 i)
    (hdm : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (d t)) :
    StronglyAdapted S.𝓕 (piB σ κ i d) := by
  intro t
  have h1 : ∀ j : ℕ, StronglyMeasurable[S.𝓕 t]
      (fun ω => (1 / (1 + σ * κ)) ^ j * i (t - 1 - j) ω) := fun j =>
    ((hia (t - 1 - j)).mono (S.𝓕.mono (by omega))).const_mul _
  have h2 : ∀ j : ℕ, StronglyMeasurable[S.𝓕 t]
      (fun ω => (1 / (1 + σ * κ)) ^ j * d (t - 1 - j) ω) := fun j =>
    ((hdm (t - 1 - j)).mono (S.𝓕.mono (by omega))).const_mul _
  have s1 : StronglyMeasurable[S.𝓕 t]
      (fun ω => ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - 1 - j) ω) := by
    let _ : MeasurableSpace Ω := S.𝓕 t
    exact StronglyMeasurable.tsum h1
  have s2 : StronglyMeasurable[S.𝓕 t]
      (fun ω => ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * d (t - 1 - j) ω) := by
    let _ : MeasurableSpace Ω := S.𝓕 t
    exact StronglyMeasurable.tsum h2
  exact (s1.const_mul _).add s2

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (17.8): the backward moving average is bounded by
`(b|Mi| + |Md|)/(1 − a)` wherever the rates and errors are bounded. -/
theorem piB_bound {σ κ Mi Md : ℝ} (hσκ : 0 < σ * κ) {i d : ℤ → Ω → ℝ} {ω : Ω}
    (hi : ∀ s, |i s ω| ≤ Mi) (hd : ∀ s, |d s ω| ≤ Md) (t : ℤ) :
    |piB σ κ i d t ω| ≤
      (σ * κ / (1 + σ * κ) * |Mi| + |Md|) / (1 - |1 / (1 + σ * κ)|) := by
  obtain ⟨ha0, ha1, hb0, -⟩ := StaticIS.coeff_17_7 hσκ
  have haa : |1 / (1 + σ * κ)| < 1 := by rw [abs_of_pos ha0]; exact ha1
  have hpos : 0 < 1 - |1 / (1 + σ * κ)| := by linarith
  have b1 := TidyR5ExpectationsMeasure.MeasExpectationSystem.abs_tsum_geom_mul_le haa
    (x := fun j : ℕ => i (t - 1 - j) ω) fun j => hi _
  have b2 := TidyR5ExpectationsMeasure.MeasExpectationSystem.abs_tsum_geom_mul_le haa
    (x := fun j : ℕ => d (t - 1 - j) ω) fun j => hd _
  have hMi : Mi / (1 - |1 / (1 + σ * κ)|) ≤ |Mi| / (1 - |1 / (1 + σ * κ)|) :=
    div_le_div_of_nonneg_right (le_abs_self Mi) hpos.le
  have hMd : Md / (1 - |1 / (1 + σ * κ)|) ≤ |Md| / (1 - |1 / (1 + σ * κ)|) :=
    div_le_div_of_nonneg_right (le_abs_self Md) hpos.le
  have hX := b1.trans hMi
  have hY := b2.trans hMd
  unfold piB
  calc _ ≤ |σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - 1 - j) ω| +
        |∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * d (t - 1 - j) ω| := abs_add_le _ _
    _ = σ * κ / (1 + σ * κ) * |∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - 1 - j) ω| +
        |∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * d (t - 1 - j) ω| := by
      rw [abs_mul, abs_of_pos hb0]
    _ ≤ σ * κ / (1 + σ * κ) * (|Mi| / (1 - |1 / (1 + σ * κ)|)) +
        |Md| / (1 - |1 / (1 + σ * κ)|) := by gcongr
    _ = _ := by ring

/-- **Existence on ℤ under uncertainty** (Cochrane (2023), eq. (17.8), p. 400): for `σκ > 0`,
essentially bounded adapted rates and every essentially bounded martingale difference sequence
`d` (`d_t` known at `t + 1`, `E_t d_t = 0` a.s.), the backward moving average `piB` is an
adapted, essentially bounded equilibrium of (17.7) on ℤ whose expectational errors are `d`.
Compare `SharedTools.backward_series_solves`. -/
theorem piB_equilibrium {σ κ Mi Md : ℝ} (hσκ : 0 < σ * κ) {i d : ℤ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ Mi)
    (hdm : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (d t)) (hd : ∀ t, ∀ᵐ ω ∂S.μ, |d t ω| ≤ Md)
    (hd0 : ∀ t, S.E t (d t) =ᵐ[S.μ] 0) :
    REModelZ S σ κ i (piB σ κ i d) ∧ (∀ t, err S (piB σ κ i d) t =ᵐ[S.μ] d t) ∧
      ∀ t, ∀ᵐ ω ∂S.μ, |piB σ κ i d t ω| ≤
        (σ * κ / (1 + σ * κ) * |Mi| + |Md|) / (1 - |1 / (1 + σ * κ)|) := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  set a := 1 / (1 + σ * κ) with ha
  set b := σ * κ / (1 + σ * κ) with hb
  set P := piB σ κ i d with hP
  have had := piB_adapted S σ κ hia hdm
  have hall : ∀ᵐ ω ∂S.μ, (∀ s, |i s ω| ≤ Mi) ∧ ∀ s, |d s ω| ≤ Md :=
    (ae_all_iff.2 hi).and (ae_all_iff.2 hd)
  have hbd : ∀ t, ∀ᵐ ω ∂S.μ, |P t ω| ≤ (b * |Mi| + |Md|) / (1 - |a|) := fun t =>
    hall.mono fun ω h => piB_bound hσκ h.1 h.2 t
  have hrec : ∀ t, P (t + 1) =ᵐ[S.μ] (a • P t + b • i t) + d t := fun t =>
    hall.mono fun ω h => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact piB_rec hσκ h.1 h.2 t
  have hPi : ∀ t, Integrable (P t) S.μ := fun t => S.integrable_of_bdd (had t) (hbd t)
  have hii : ∀ t, Integrable (i t) S.μ := fun t => S.integrable_of_bdd (hia t) (hi t)
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => S.integrable_of_bdd (hdm t) (hd t)
  have hE : ∀ t, S.E t (P (t + 1)) =ᵐ[S.μ] a • P t + b • i t := by
    intro t
    have hX : StronglyMeasurable[S.𝓕 t] (a • P t + b • i t) :=
      ((had t).const_smul a).add ((hia t).const_smul b)
    have hXi : Integrable (a • P t + b • i t) S.μ := ((hPi t).smul a).add ((hii t).smul b)
    filter_upwards [S.E_congr (hrec t) t, S.E_add hXi (hdi t) t, hd0 t] with ω e1 e2 e3
    rw [e1, e2, Pi.add_apply, S.E_of_stronglyMeasurable hX hXi, e3, Pi.zero_apply, add_zero]
  refine ⟨⟨had, fun t => ?_⟩, fun t => ?_, hbd⟩
  · filter_upwards [hE t] with ω e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e, ha, hb]
    field_simp
    ring
  · filter_upwards [hE t, hrec t] with ω e1 e2
    simp only [err, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2]
    ring

/-- **Uniqueness given the errors** (Cochrane (2023), eq. (17.8), p. 400): every equilibrium of
(17.7) on ℤ with essentially bounded inflation and rates, whose expectational errors are `d` a.s.,
equals the backward moving average `piB` a.s. at every date. -/
theorem eq_piB {σ κ Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {i π d : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ Mi) (herr : ∀ t, err S π t =ᵐ[S.μ] d t) :
    ∀ᵐ ω ∂S.μ, ∀ t, π t ω = piB σ κ i d t ω := by
  filter_upwards [eq_17_8_ae S hσκ h hπ hi, ae_all_iff.2 herr] with ω e he t
  have e1 := e (t - 1)
  rw [sub_add_cancel] at e1
  rw [e1, piB]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t - 1 - (j : ℤ) = t - 1 - j from rfl, he]

/-- Cochrane (2023), eq. (17.8), p. 400: two essentially bounded equilibria of (17.7) on ℤ with
the same rates and the same expectational errors are almost surely equal at every date. -/
theorem unique_of_err {σ κ Mπ Mπ' Mi : ℝ} (hσκ : 0 < σ * κ) {i π π' : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) (h' : REModelZ S σ κ i π') (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hπ' : ∀ t, ∀ᵐ ω ∂S.μ, |π' t ω| ≤ Mπ') (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ Mi)
    (herr : ∀ t, err S π' t =ᵐ[S.μ] err S π t) :
    ∀ᵐ ω ∂S.μ, ∀ t, π' t ω = π t ω := by
  filter_upwards [eq_piB S hσκ h hπ hi (fun t => EventuallyEq.rfl),
    eq_piB S hσκ h' hπ' hi herr] with ω e e' t
  rw [e, e']

/-! ### The remote past -/

/-- Cochrane (2023), eq. (17.8), p. 400 (the role of `t → −∞`): for every integrable `c` known at
every date (the remote past), `π_t + aᵗ c` is again an equilibrium of (17.7) on ℤ with the same
expectational errors. -/
theorem remote_family {σ κ Mπ : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ} {c : Ω → ℝ}
    (h : REModelZ S σ κ i π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hc : ∀ t, StronglyMeasurable[S.𝓕 t] c) (hci : Integrable c S.μ) :
    REModelZ S σ κ i (fun t => π t + (1 / (1 + σ * κ)) ^ t • c) ∧
      ∀ t, err S (fun t => π t + (1 / (1 + σ * κ)) ^ t • c) t =ᵐ[S.μ] err S π t := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  have ha0 : 1 / (1 + σ * κ) ≠ 0 := by positivity
  have hEc : ∀ t s : ℤ, S.E t ((1 / (1 + σ * κ)) ^ s • c) = (1 / (1 + σ * κ)) ^ s • c :=
    fun t s => S.E_of_stronglyMeasurable ((hc t).const_smul _) (hci.smul _)
  have hπi : ∀ t, Integrable (π t) S.μ := fun t => S.integrable_of_bdd (h.1 t) (hπ t)
  refine ⟨⟨fun t => (h.1 t).add ((hc t).const_smul _), fun t => ?_⟩, fun t => ?_⟩
  · filter_upwards [h.2 t, S.E_add (hπi (t + 1)) (hci.smul ((1 / (1 + σ * κ)) ^ (t + 1))) t]
      with ω e1 e2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e2, hEc, Pi.smul_apply, smul_eq_mul, e1, zpow_add_one₀ ha0]
    field_simp
    ring
  · filter_upwards [S.E_add (hπi (t + 1)) (hci.smul ((1 / (1 + σ * κ)) ^ (t + 1))) t]
      with ω e
    simp only [err, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e, hEc, Pi.smul_apply, smul_eq_mul]
    ring

/-- Cochrane (2023), eq. (17.8): the remote-past family is bounded on the future, `t ≥ 0`, by
`Mπ + C` when `|c| ≤ C`. -/
theorem remote_family_bdd_future {σ κ Mπ C : ℝ} (hσκ : 0 < σ * κ) {π : ℤ → Ω → ℝ}
    {c : Ω → ℝ} (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (hcC : ∀ᵐ ω ∂S.μ, |c ω| ≤ C) {t : ℤ}
    (ht : 0 ≤ t) : ∀ᵐ ω ∂S.μ, |π t ω + (1 / (1 + σ * κ)) ^ t * c ω| ≤ Mπ + C := by
  obtain ⟨ha0, ha1, -, -⟩ := StaticIS.coeff_17_7 hσκ
  have hp : (1 / (1 + σ * κ)) ^ t ≤ 1 := by
    lift t to ℕ using ht
    rw [zpow_natCast]
    exact pow_le_one₀ ha0.le ha1.le
  filter_upwards [hπ t, hcC] with ω e1 e2
  refine (abs_add_le _ _).trans (add_le_add e1 ?_)
  rw [abs_mul, abs_of_pos (zpow_pos ha0 t)]
  calc (1 / (1 + σ * κ)) ^ t * |c ω| ≤ 1 * |c ω| :=
        mul_le_mul_of_nonneg_right hp (abs_nonneg _)
    _ ≤ C := by rw [one_mul]; exact e2

/-- Cochrane (2023), eq. (17.8), p. 400 (**the bound at `−∞` pins the equilibrium down**): for
essentially bounded `π`, the remote-past family `π_t + aᵗ c` is essentially bounded on all of ℤ
iff `c = 0` a.s. -/
theorem remote_family_bdd_iff {σ κ Mπ : ℝ} (hσκ : 0 < σ * κ) {π : ℤ → Ω → ℝ} {c : Ω → ℝ}
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) :
    (∃ M, ∀ t, ∀ᵐ ω ∂S.μ, |π t ω + (1 / (1 + σ * κ)) ^ t * c ω| ≤ M) ↔ c =ᵐ[S.μ] 0 := by
  constructor
  · rintro ⟨M, hM⟩
    have hk : ∀ n : ℕ, ∀ᵐ ω ∂S.μ, (1 + σ * κ) ^ n * |c ω| ≤ M + Mπ := by
      intro n
      filter_upwards [hM (-(n : ℤ)), hπ (-(n : ℤ))] with ω e1 e2
      have hz : (1 / (1 + σ * κ)) ^ (-(n : ℤ)) = (1 + σ * κ) ^ n := by
        rw [one_div, inv_zpow, zpow_neg, inv_inv, zpow_natCast]
      rw [hz] at e1
      have h3 : |(1 + σ * κ) ^ n * c ω| ≤ M + Mπ := by
        have := abs_sub (π (-(n : ℤ)) ω + (1 + σ * κ) ^ n * c ω) (π (-(n : ℤ)) ω)
        rw [add_sub_cancel_left] at this
        linarith
      rwa [abs_mul, abs_of_pos (by positivity)] at h3
    filter_upwards [ae_all_iff.2 hk] with ω e
    by_contra hne
    have hc0 : 0 < |c ω| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((M + Mπ) / |c ω| + 1) (by linarith :
      1 < 1 + σ * κ)
    have := e n
    rw [← le_div_iff₀ hc0] at this
    linarith
  · intro hc
    obtain ⟨Mπ', hM⟩ : ∃ M, ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ M := ⟨Mπ, hπ⟩
    refine ⟨Mπ', fun t => ?_⟩
    filter_upwards [hM t, hc] with ω e1 e2
    rw [e2, Pi.zero_apply, mul_zero, add_zero]
    exact e1

/-- Cochrane (2023), eq. (17.8), p. 400: a constant is known at every date, so `π_t + aᵗ` is
always a second equilibrium with the same errors, bounded on `t ≥ 0` but not on ℤ: without the
bound at `−∞`, uniqueness fails under any filtration. -/
theorem remote_one_solves {σ κ Mπ : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) :
    REModelZ S σ κ i (fun t => π t + (1 / (1 + σ * κ)) ^ t • fun _ => (1 : ℝ)) ∧
      (∀ t, 0 ≤ t → ∀ᵐ ω ∂S.μ, |π t ω + (1 / (1 + σ * κ)) ^ t * 1| ≤ Mπ + 1) ∧
      ¬ ∃ M, ∀ t, ∀ᵐ ω ∂S.μ, |π t ω + (1 / (1 + σ * κ)) ^ t * 1| ≤ M := by
  refine ⟨(remote_family S hσκ h hπ (fun t => stronglyMeasurable_const)
    (integrable_const 1)).1, fun t ht => remote_family_bdd_future S hσκ hπ
    (c := fun _ => 1) (Eventually.of_forall fun _ => by simp) ht, fun hb => ?_⟩
  have := (remote_family_bdd_iff S hσκ (c := fun _ => (1 : ℝ)) hπ).mp hb
  have h0 : (S.μ : Measure Ω) Set.univ = 0 := by
    have : ∀ᵐ ω ∂S.μ, False := this.mono fun ω h => by simp at h
    rw [ae_iff] at this
    simp at this
  simp at h0

/-- Cochrane (2023), eq. (17.8), p. 400 (**the remote past is all that is left**): if `π` and
`π'` are equilibria of (17.7) on ℤ with the same expectational errors (no bound assumed on `π'`,
only integrability), then `π'_t − π_t = aᵗ (π'_0 − π_0)` a.s. at every date, and
`π'_0 − π_0` is known at every date, however early: `E_t (π'_0 − π_0) = π'_0 − π_0` a.s. -/
theorem remote_converse {σ κ : ℝ} (hσκ : 0 < σ * κ) {i π π' : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) (h' : REModelZ S σ κ i π') (hπi : ∀ t, Integrable (π t) S.μ)
    (hπi' : ∀ t, Integrable (π' t) S.μ) (herr : ∀ t, err S π' t =ᵐ[S.μ] err S π t) :
    (∀ t, π' t - π t =ᵐ[S.μ] (1 / (1 + σ * κ)) ^ t • (π' 0 - π 0)) ∧
      ∀ t, S.E t (π' 0 - π 0) =ᵐ[S.μ] π' 0 - π 0 := by
  have ha0 : 1 / (1 + σ * κ) ≠ 0 := (StaticIS.coeff_17_7 hσκ).1.ne'
  set a := 1 / (1 + σ * κ) with ha
  set D : ℤ → Ω → ℝ := fun t => π' t - π t with hD
  have hstep : ∀ t, D (t + 1) =ᵐ[S.μ] a • D t := by
    intro t
    filter_upwards [rec_ae S hσκ h t, rec_ae S hσκ h' t, herr t] with ω e1 e2 e3
    simp only [hD, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, e3]
    ring
  have hall : ∀ t, D t =ᵐ[S.μ] a ^ t • D 0 := by
    intro t
    induction t using Int.induction_on with
    | zero => simp
    | succ n ih =>
      filter_upwards [hstep n, ih] with ω e1 e2
      simp only [Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
      rw [e1, e2, zpow_add_one₀ ha0]
      ring
    | pred n ih =>
      filter_upwards [hstep (-(n : ℤ) - 1), ih] with ω e1 e2
      simp only [Pi.smul_apply, smul_eq_mul, sub_add_cancel] at e1 e2 ⊢
      rw [e2] at e1
      rw [zpow_sub_one₀ ha0]
      field_simp
      linarith
  refine ⟨hall, fun t => ?_⟩
  have hDm : StronglyMeasurable[S.𝓕 t] (D t) := (h'.1 t).sub (h.1 t)
  have hDi : Integrable (D t) S.μ := (hπi' t).sub (hπi t)
  have h0 : D 0 =ᵐ[S.μ] a ^ (-t) • D t := by
    filter_upwards [hall t] with ω e
    simp only [Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e, ← mul_assoc, ← zpow_add₀ ha0, neg_add_cancel, zpow_zero, one_mul]
  have hX : StronglyMeasurable[S.𝓕 t] (a ^ (-t) • D t) := hDm.const_smul _
  filter_upwards [S.E_congr h0 t, h0] with ω e1 e2
  change S.E t (D 0) ω = D 0 ω
  rw [e1, S.E_of_stronglyMeasurable hX (hDi.smul _), e2]

/-- Cochrane (2023), eq. (17.8), p. 400, and the ℕ-indexed finite-start form (`StaticIS.reFamily`):
almost surely, from every start `t − k`,
`π_t = aᵏ π_{t−k} + ∑_{j<k} aʲ (b i_{t−1−j} + δ_{t−j})`. -/
theorem finite_start_ae {σ κ : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) :
    ∀ᵐ ω ∂S.μ, ∀ t (k : ℕ), π t ω = (1 / (1 + σ * κ)) ^ k * π (t - k) ω +
      ∑ j ∈ Finset.range k, (1 / (1 + σ * κ)) ^ j *
        (σ * κ / (1 + σ * κ) * i (t - 1 - j) ω + err S π (t - 1 - j) ω) := by
  filter_upwards [ae_all_iff.2 (rec_ae S hσκ h)] with ω hr t k
  have e := SharedTools.backward_iterate (a := 1 / (1 + σ * κ)) (x := fun s => π s ω)
    (w := fun s => σ * κ / (1 + σ * κ) * i (s - 1) ω + err S π (s - 1) ω)
    (fun s => by simp only [add_sub_cancel_right]; rw [hr s]; ring) t k
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show t - (j : ℤ) - 1 = t - 1 - j by ring]

/-- Cochrane (2023), eq. (17.8), p. 400: for essentially bounded inflation, the initial-condition
term `aᵏ π_{t−k}` of the finite-start form vanishes almost surely as the start recedes,
`k → ∞`. -/
theorem tendsto_initial_term {σ κ Mπ : ℝ} (hσκ : 0 < σ * κ) {π : ℤ → Ω → ℝ}
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) :
    ∀ᵐ ω ∂S.μ, ∀ t, Tendsto (fun k : ℕ => (1 / (1 + σ * κ)) ^ k * π (t - k) ω) atTop (𝓝 0) := by
  obtain ⟨ha0, ha1, -, -⟩ := StaticIS.coeff_17_7 hσκ
  filter_upwards [ae_all_iff.2 hπ] with ω hb t
  refine squeeze_zero_norm (a := fun k : ℕ => (1 / (1 + σ * κ)) ^ k * Mπ) (fun k => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos ha0 k)]
    exact mul_le_mul_of_nonneg_left (hb _) (pow_nonneg ha0.le k)
  · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1).mul_const Mπ

/-! ### The inverse of (17.14) -/

/-- **The corrected inverse of (17.14) under uncertainty** (Cochrane (2023), eq. (17.14), p. 405;
survey error E8): for an equilibrium of (17.7) on ℤ with essentially bounded inflation and rates,
almost surely at every date
`E_t π_{t+1} = b ∑ aʲ i_{t−j} + ∑ a^{j+1} δ_{t−j}`, `δ_{t−j} = π_{t−j} − E_{t−j−1} π_{t−j}`.
Almost-sure version of `PersistenceFreedom.corrected_inverse`. -/
theorem corrected_inverse_ae {σ κ Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ Mi) :
    ∀ᵐ ω ∂S.μ, ∀ t, S.E t (π (t + 1)) ω =
      σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) ω +
        ∑' j : ℕ, (1 / (1 + σ * κ)) ^ (j + 1) * err S π (t - j - 1) ω := by
  filter_upwards [ae_all_iff.2 (E_next S hσκ h), ae_all_iff.2 hπ, ae_all_iff.2 hi,
    ae_all_iff.2 fun t => S.abs_E_le (hπ (t + 1)) t] with ω hE hbπ hbi hbe t
  have e := PersistenceFreedom.corrected_inverse hσκ (e := fun s => S.E s (π (s + 1)) ω)
    (π := fun s => π s ω) (i := fun s => i s ω) hbe hbπ hbi
    (fun s => by
      have := hE s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this) t
  rw [e]
  congr 1
  refine tsum_congr fun j => ?_
  simp only [err, Pi.sub_apply, sub_add_cancel]

/-- Cochrane (2023), eq. (17.14), p. 405: the expectational-error sums
`S_t = ∑ a^{j+1} δ_{t−j}` satisfy `S_{t+1} = a δ_{t+1} + a S_t` wherever the errors are bounded. -/
theorem errSum_shift {a M : ℝ} (ha : |a| < 1) {e : ℤ → ℝ} (he : ∀ s, |e s| ≤ M) (t : ℤ) :
    ∑' j : ℕ, a ^ (j + 1) * e (t + 1 - j - 1) =
      a * e t + a * ∑' j : ℕ, a ^ (j + 1) * e (t - j - 1) := by
  have h := backward_shift ha (f := fun s => a * e s) (M := |a| * M)
    (fun s => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (he s) (abs_nonneg a)) t
  have l : ∀ u : ℤ, ∑' j : ℕ, a ^ (j + 1) * e (u - j) = ∑' j : ℕ, a ^ j * (a * e (u - j)) :=
    fun u => tsum_congr fun j => by ring
  have l2 : ∑' j : ℕ, a ^ (j + 1) * e (t + 1 - j - 1) = ∑' j : ℕ, a ^ (j + 1) * e (t - j) :=
    tsum_congr fun j => by rw [show t + 1 - (j : ℤ) - 1 = t - j by ring]
  have l3 : ∑' j : ℕ, a ^ (j + 1) * e (t - j - 1) = ∑' j : ℕ, a ^ j * (a * e (t - 1 - j)) :=
    tsum_congr fun j => by rw [show t - (j : ℤ) - 1 = t - 1 - j by ring]; ring
  rw [l2, l t, h, l3]

/-- **The printed inverse of (17.14) under uncertainty** (Cochrane (2023), eq. (17.14), p. 405):
for an equilibrium of (17.7) on ℤ with essentially bounded inflation and rates, the printed
inverse `E_t π_{t+1} = b ∑ aʲ i_{t−j}` holds almost surely at every date iff every expectational
error is zero almost surely.
Strengthens `PersistenceFreedom.printed_inverse_of_no_surprise`. -/
theorem printed_inverse_iff {σ κ Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ Mi) :
    (∀ᵐ ω ∂S.μ, ∀ t, S.E t (π (t + 1)) ω =
      σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) ω) ↔
      ∀ t, err S π t =ᵐ[S.μ] 0 := by
  obtain ⟨ha0, ha1, -, -⟩ := StaticIS.coeff_17_7 hσκ
  have haa : |1 / (1 + σ * κ)| < 1 := by rw [abs_of_pos ha0]; exact ha1
  constructor
  · intro hp
    have hz : ∀ᵐ ω ∂S.μ, ∀ t,
        ∑' j : ℕ, (1 / (1 + σ * κ)) ^ (j + 1) * err S π (t - j - 1) ω = 0 := by
      filter_upwards [hp, corrected_inverse_ae S hσκ h hπ hi] with ω e1 e2 t
      have := (e1 t).symm.trans (e2 t)
      linarith
    have hall : ∀ᵐ ω ∂S.μ, ∀ t, err S π t ω = 0 := by
      filter_upwards [hz, ae_all_iff.2 (err_bdd S hπ)] with ω hz hb t
      have e := errSum_shift haa (e := fun s => err S π s ω) hb t
      have z1 := hz (t + 1)
      rw [hz t, mul_zero, add_zero] at e
      rw [z1] at e
      have := mul_eq_zero.mp e.symm
      rcases this with h0 | h0
      · exact absurd h0 ha0.ne'
      · exact h0
    exact fun t => hall.mono fun ω h => h t
  · intro herr
    filter_upwards [corrected_inverse_ae S hσκ h hπ hi, ae_all_iff.2 herr] with ω e he t
    rw [e t]
    have : ∀ j : ℕ, (1 / (1 + σ * κ)) ^ (j + 1) * err S π (t - j - 1) ω = 0 := fun j => by
      rw [he, Pi.zero_apply, mul_zero]
    rw [tsum_congr this, tsum_zero, add_zero]

/-- Cochrane (2023), eq. (17.14), p. 405 (survey error E8, under uncertainty): if some
expectational error is nonzero with positive probability, the printed inverse fails with positive
probability at some date.
Almost-sure version of `PersistenceFreedom.printed_inverse_false`. -/
theorem printed_inverse_fails {σ κ Mπ Mi : ℝ} (hσκ : 0 < σ * κ) {i π : ℤ → Ω → ℝ}
    (h : REModelZ S σ κ i π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ Mi) {s : ℤ} (hs : ¬ err S π s =ᵐ[S.μ] 0) :
    ¬ ∀ᵐ ω ∂S.μ, ∀ t, S.E t (π (t + 1)) ω =
      σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) ω :=
  fun hp => hs ((printed_inverse_iff S hσκ h hπ hi).mp hp s)

/-! ### The abstract ℤ-indexed system -/

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (17.7), p. 399, for an abstract ℤ-indexed expectation system:
`π` adapted and `π_t = −σκ i_t + (1 + σκ) E_t π_{t+1}` state by state at every `t ∈ ℤ`. -/
def REModelZA (𝔼 : ZExpectationSystem Ω) (σ κ : ℝ) (i π : ℤ → Ω → ℝ) : Prop :=
  𝔼.Adapted π ∧ ∀ t ω, π t ω = -(σ * κ) * i t ω + (1 + σ * κ) * 𝔼.E t (π (t + 1)) ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (17.7): an equilibrium on ℤ restricts, from every date `s`, to an
equilibrium `StaticIS.REModel` of the restricted core system — so the ℕ-indexed results of
StaticIS apply to the dates `t ≥ s`. -/
theorem reModelZA_restrict {𝔼 : ZExpectationSystem Ω} {σ κ : ℝ} {i π : ℤ → Ω → ℝ}
    (h : REModelZA 𝔼 σ κ i π) (s : ℤ) :
    StaticIS.REModel (𝔼.restrict s) σ κ (fun n => i (s + n)) (fun n => π (s + n)) := by
  refine ⟨𝔼.restrict_adapted h.1 s, fun n ω => ?_⟩
  have e : s + ((n + 1 : ℕ) : ℤ) = s + n + 1 := by push_cast; ring
  change π (s + n) ω = -(σ * κ) * i (s + n) ω + (1 + σ * κ) * 𝔼.E (s + n) (π (s + ↑(n + 1))) ω
  rw [e]
  exact h.2 (s + n) ω

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eq. (17.8), p. 400, for an abstract ℤ-indexed system: every bounded
equilibrium is, state by state, `π_{t+1} = b ∑ aʲ i_{t−j} + ∑ aʲ δ_{t+1−j}` with
`δ_{s+1} = π_{s+1} − E_s π_{s+1}`.
ℤ-indexed version of `StaticIS.eq_17_8`. -/
theorem eq_17_8_abstract {𝔼 : ZExpectationSystem Ω} {σ κ Mπ Mi : ℝ} (hσκ : 0 < σ * κ)
    {i π : ℤ → Ω → ℝ} (h : REModelZA 𝔼 σ κ i π) (hπ : ∀ t ω, |π t ω| ≤ Mπ)
    (hi : ∀ t ω, |i t ω| ≤ Mi) (t : ℤ) (ω : Ω) :
    π (t + 1) ω = σ * κ / (1 + σ * κ) * ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j * i (t - j) ω +
      ∑' j : ℕ, (1 / (1 + σ * κ)) ^ j *
        (π (t - j + 1) ω - 𝔼.E (t - j) (π (t - j + 1)) ω) := by
  have h1 : 1 + σ * κ ≠ 0 := by linarith
  have hE : ∀ s, |𝔼.E s (π (s + 1)) ω| ≤ Mπ := fun s => 𝔼.abs_E_le (hπ (s + 1)) s ω
  have e := StaticIS.eq_17_8 hσκ (π := fun s => π s ω) (i := fun s => i s ω)
    (δ := fun s => π s ω - 𝔼.E (s - 1) (π s) ω) (Mδ := Mπ + Mπ) (hπ · ω) (hi · ω)
    (fun s => by
      refine (abs_sub _ _).trans (add_le_add (hπ s ω) ?_)
      have := hE (s - 1)
      rwa [sub_add_cancel] at this)
    (fun s => by
      simp only [add_sub_cancel_right]
      have := h.2 s ω
      field_simp
      linarith) t
  rw [e]
  congr 1
  refine tsum_congr fun j => ?_
  rw [show t + 1 - (j : ℤ) = t - j + 1 by ring, add_sub_cancel_right]

end Cochrane.KeynesianStickyPrices.TidyR6ZStaticIS
