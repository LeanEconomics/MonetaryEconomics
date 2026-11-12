/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import KeynesianStickyPrices.TidyR6ZStaticIS
import KeynesianStickyPrices.TidyR5InnovEqmMeasure
import KeynesianStickyPrices.FullModelTidy

/-!
# The full model on ℤ under uncertainty: bounded equilibria and the anticipated rise

Cochrane (2023), *The Fiscal Theory of the Price Level*, Chapter 17, §17.4.1, eqs.
(17.15)–(17.18), pp. 407–409, Figures 17.5–17.6, with eq. (5.5), p. 119.

FullModel and FullModelTidy proved, under perfect foresight on ℤ, that (17.18) has exactly one
bounded solution for every bounded rate path (`FullModelTidy.secondZ_existsUnique`), the
anticipated rise of Figure 17.5 being `FullModel.zPath`. Here the model (17.15)–(17.17) holds
almost surely at every date `t ∈ ℤ` on a probability space with a ℤ-indexed filtration
(`ModelZM`; TidyR6ZExpectations).

## The link with the ℕ-indexed news form

`modelZM_restrict`: an equilibrium on ℤ restricted to the dates `t ≥ s` is an equilibrium
`TidyR5StochasticPathsMeasure.ModelM` of the restricted system; hence (`news_path_Z`) its news
about the future is a perfect-foresight path, and (`restrict_eq_piM`) from date `s` on it is the
ℕ-indexed equilibrium `TidyR5InnovEqmMeasure.piM` started at `π_s` with its own innovations.
For the abstract ℤ-indexed system, `ModelZA` restricts to `FullModel.Model` (`modelZA_restrict`).

## Bounded equilibria on ℤ: existence and a.s. uniqueness given the innovations

With `F_t = E_t ∑ λ₂ᵏ i_{t+k}` (`TidyR6ZExpectations.ZMeasExpectationSystem.FZ`) and
`δ_{t+1} = π_{t+1} − E_t π_{t+1}` (`errZ`):

* `factoredZ`: `λ₁ E_t π_{t+1} = π_t + σκ F_t` a.s. at every date (obtained from the ℕ result
  through the restriction); `recZ`: `π_{t+1} = λ₁⁻¹(π_t + σκF_t) + δ_{t+1}`.
* **`eq_piZM`** (uniqueness): every essentially bounded equilibrium is almost surely, at every date,
  `π_t = ∑_{j≥0} λ₁^{−j}(λ₁⁻¹σκ F_{t−1−j} + δ_{t−j})` (`piZM`) with its own innovations;
  the stable root is solved backward over the infinite past, which is where the bound as
  `t → −∞` is used.
* **`piZM_equilibrium`** (existence): for every essentially bounded adapted rate process and every
  essentially bounded martingale difference sequence `d`, `piZM` is an adapted, essentially
  bounded equilibrium (with output and the real rate) whose innovations are `d`.
* `eqm_unique_given_innov`: two essentially bounded equilibria with the same rates and the same
  innovations agree a.s. in inflation, output and the real rate at every date.

So the bounded equilibria on ℤ are exactly the bounded martingale difference sequences, as on ℕ
(Figure 17.6) — but on ℤ there is no initial inflation to choose.

## Deterministic rate paths and Figure 17.5 (`zPath`)

For a bounded deterministic rate path `ī`:

* `det_representation`: every bounded equilibrium is
  `π_t = piZ(ī)_t + ∑ λ₁^{−j} δ_{t−j}` a.s. (`FullModelTidy.piZ` the perfect-foresight path);
  `det_eq_piZ_iff`: it is the perfect-foresight path a.s. iff all its innovations vanish;
  `pf_is_equilibrium`: the perfect-foresight path is an equilibrium under every filtration;
  `det_expected`: `E_s π_{s+j} = piZ_{s+j} + λ₁^{−j}(π_s − piZ_s)`.
* **`det_unique_iff_noNews`**: the perfect-foresight path is the only bounded equilibrium (a.s.)
  iff the filtration carries no news (`NoNews`: every bounded variable known at `t + 1` is a.s.
  its date-`t` forecast). The ℤ statement `FullModel.zPath_existsUnique` therefore **fails under
  genuine uncertainty**: on the coin space (`coinSystem`, a fair coin revealed at date 1)
  there is a second bounded equilibrium (`zPath_not_unique_coin`). The corrected statements are
  `zPath_representation` (every bounded equilibrium is `zPath + ∑ λ₁^{−j} δ_{t−j}`),
  `zPath_iff_no_innov`, `zPath_is_equilibrium` and `zPath_unique_iff_noNews`.
-/

namespace Cochrane.KeynesianStickyPrices.TidyR6ZFullModel

open MeasureTheory Filter Topology FullModel TidyR6ZExpectations ZMeasExpectationSystem
open TidyR5ExpectationsMeasure TidyR5StochasticPathsMeasure TidyR5InnovEqmMeasure

variable {Ω : Type*} [MeasurableSpace Ω] (S : ZMeasExpectationSystem Ω)

/-! ### The model on ℤ and its restrictions -/

/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, on ℤ under uncertainty, without disturbances:
`x_t = E_t x_{t+1} − σ r_t`, `i_t = r_t + E_t π_{t+1}`, `π_t = β E_t π_{t+1} + κ x_t` almost
surely at every date `t ∈ ℤ`, all variables integrable.
ℤ-indexed version of `TidyR5StochasticPathsMeasure.ModelM`. -/
def ModelZM (σ β κ : ℝ) (i r x π : ℤ → Ω → ℝ) : Prop :=
  (∀ t, Integrable (i t) S.μ ∧ Integrable (r t) S.μ ∧ Integrable (x t) S.μ ∧
    Integrable (π t) S.μ) ∧
  ∀ t, x t =ᵐ[S.μ] S.E t (x (t + 1)) - σ • r t ∧ i t =ᵐ[S.μ] r t + S.E t (π (t + 1)) ∧
    π t =ᵐ[S.μ] β • S.E t (π (t + 1)) + κ • x t

/-- Cochrane (2023), §17.4, p. 409: the innovation `δ_{t+1} = π_{t+1} − E_t π_{t+1}`. -/
noncomputable def errZ (π : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ := π (t + 1) - S.E t (π (t + 1))

/-- Cochrane (2023), §17.4, p. 409: the innovations of an essentially bounded process are
essentially bounded by `2Mπ`.
As `TidyR5StochasticPaths.abs_innov_le` and `TidyR6ZStaticIS.err_bdd`. -/
theorem errZ_bdd {Mπ : ℝ} {π : ℤ → Ω → ℝ} (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (t : ℤ) :
    ∀ᵐ ω ∂S.μ, |errZ S π t ω| ≤ Mπ + Mπ := by
  filter_upwards [hπ (t + 1), S.abs_E_le (hπ (t + 1)) t] with ω e1 e2
  simp only [errZ, Pi.sub_apply]
  exact (abs_sub _ _).trans (add_le_add e1 e2)

/-- Cochrane (2023), §17.4, pp. 407–410: an equilibrium on ℤ restricted to the dates `t ≥ s` is an
equilibrium of the ℕ-indexed restricted system (`TidyR5StochasticPathsMeasure.ModelM`). -/
theorem modelZM_restrict {σ β κ : ℝ} {i r x π : ℤ → Ω → ℝ} (h : ModelZM S σ β κ i r x π)
    (s : ℤ) :
    ModelM (S.restrict s) σ β κ (fun n => i (s + n)) (fun n => r (s + n))
      (fun n => x (s + n)) (fun n => π (s + n)) := by
  refine ⟨fun n => h.1 (s + n), fun n => ?_⟩
  have e : s + ((n + 1 : ℕ) : ℤ) = s + n + 1 := by push_cast; ring
  simp only [restrict_E, restrict_μ, e]
  exact h.2 (s + n)

/-- Cochrane (2023), Figs. 17.5–17.6 as impulse responses, on ℤ: almost surely the date-`(s+1)`
news about the whole future is the perfect-foresight path for the rate news started at the
unexpected inflation (TidyR5StochasticPathsMeasure.news_path_ae through the restriction). -/
theorem news_path_Z {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π : ℤ → Ω → ℝ}
    (h : ModelZM S σ β κ i r x π) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s : ℤ) :
    ∀ᵐ ω ∂S.μ, (fun j : ℕ => S.innov s (π (s + 1 + j)) ω) =
      path σ β κ (fun j : ℕ => S.innov s (i (s + 1 + j)) ω) (S.innov s (π (s + 1)) ω) := by
  have hn := news_path_ae (S.restrict s) ha hβ (modelZM_restrict S h s)
    (fun n => hi (s + n)) (fun n => hπ (s + n)) 0
  filter_upwards [hn] with ω e
  have e1 := e.1
  simp only [MeasExpectationSystem.innov, restrict_E, Pi.sub_apply, Nat.cast_zero, add_zero,
    zero_add, Nat.cast_add, Nat.cast_one] at e1
  simp only [ZMeasExpectationSystem.innov, Pi.sub_apply]
  convert e1 using 3 <;> ring_nf

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), eqs. (17.15)–(17.17), p. 407, for an abstract ℤ-indexed expectation system
(`TidyR6ZExpectations.ZExpectationSystem`), with disturbances `u_x`, `u_π`, state by state at
every date `t ∈ ℤ`. -/
def ModelZA (𝔼 : ZExpectationSystem Ω) (σ β κ : ℝ) (ux uπ i r x π : ℤ → Ω → ℝ) : Prop :=
  ∀ t, x t = 𝔼.E t (x (t + 1)) - σ • r t + ux t ∧ i t = r t + 𝔼.E t (π (t + 1)) ∧
    π t = β • 𝔼.E t (π (t + 1)) + κ • x t + uπ t

omit [MeasurableSpace Ω] in
/-- Cochrane (2023), §17.4, pp. 407–410: an equilibrium of an abstract ℤ-indexed system restricts,
from every date `s`, to an equilibrium `FullModel.Model` of the restricted core system, so the
ℕ-indexed expected-path and news results of TidyR5StochasticPaths apply to the dates `t ≥ s`. -/
theorem modelZA_restrict {𝔼 : ZExpectationSystem Ω} {σ β κ : ℝ} {ux uπ i r x π : ℤ → Ω → ℝ}
    (h : ModelZA 𝔼 σ β κ ux uπ i r x π) (s : ℤ) :
    Model (𝔼.restrict s) σ β κ (fun n => ux (s + n)) (fun n => uπ (s + n))
      (fun n => i (s + n)) (fun n => r (s + n)) (fun n => x (s + n)) (fun n => π (s + n)) := by
  have e : ∀ n : ℕ, s + ((n + 1 : ℕ) : ℤ) = s + n + 1 := fun n => by push_cast; ring
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;>
    simp only [ZExpectationSystem.restrict_E, e]
  · exact (h (s + n)).1
  · exact (h (s + n)).2.1
  · exact (h (s + n)).2.2

/-! ### The factored form -/

/-- Cochrane (2023), eq. (17.18), p. 408, and A1 §1.7, on ℤ: for essentially bounded adapted rates
and essentially bounded inflation, every equilibrium satisfies `λ₁ E_t π_{t+1} = π_t + σκ F_t`
a.s. at every date.
ℤ-indexed version of `TidyR5InnovEqmMeasure.factoredM_of_eq1718`. -/
theorem factoredZ {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π : ℤ → Ω → ℝ}
    (h : ModelZM S σ β κ i r x π) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (t : ℤ) :
    lam1 σ β κ • S.E t (π (t + 1)) =ᵐ[S.μ] π t + (σ * κ) • S.FZ (lam2 σ β κ) i t := by
  have hR := modelZM_restrict S h t
  have hf := factoredM_of_eq1718 (S.restrict t) ha hβ (S.restrict_adapted hia t)
    (fun n => hi (t + n)) (fun n => (h.1 (t + n)).2.2.2) (fun n => hπ (t + n))
    (eq1718_of_modelM (S.restrict t) hR) 0
  have e := S.FZ_eq_restrict (lam2 σ β κ) i t 0
  rw [Nat.cast_zero, add_zero] at e
  rw [e]
  simpa only [restrict_E, restrict_μ, Nat.cast_zero, add_zero, zero_add, Nat.cast_one] using hf

/-- Cochrane (2023), eq. (17.18), p. 408, on ℤ: the factored form a.s. at every date implies
(17.18) a.s. at every date (adapted essentially bounded rates, integrable inflation).
ℤ-indexed version of `TidyR5InnovEqmMeasure.eq1718_of_factoredM`. -/
theorem eq1718Z_of_factored {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i π : ℤ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hπi : ∀ t, Integrable (π t) S.μ)
    (h : ∀ t, lam1 σ β κ • S.E t (π (t + 1)) =ᵐ[S.μ] π t + (σ * κ) • S.FZ (lam2 σ β κ) i t)
    (t : ℤ) :
    (σ * κ) • i t =ᵐ[S.μ]
      -β • S.E t (π (t + 2)) + (1 + β + σ * κ) • S.E t (π (t + 1)) - π t := by
  have hF : FactoredM (S.restrict t) σ β κ (fun n => i (t + n)) (fun n => π (t + n)) := by
    intro n
    have e := S.FZ_eq_restrict (lam2 σ β κ) i t n
    have e1 : t + ((n + 1 : ℕ) : ℤ) = t + n + 1 := by push_cast; ring
    simp only [restrict_E, restrict_μ, e1, ← e]
    exact h (t + n)
  have h18 := eq1718_of_factoredM (S.restrict t) ha hβ (S.restrict_adapted hia t)
    (fun n => hi (t + n)) (fun n => hπi (t + n)) hF 0
  simpa only [restrict_E, restrict_μ, Nat.cast_zero, add_zero, zero_add, Nat.cast_ofNat,
    Nat.cast_one] using h18

/-- Cochrane (2023), §17.4.1, on ℤ: every equilibrium satisfies
`π_{t+1} = λ₁⁻¹ π_t + λ₁⁻¹σκ F_t + δ_{t+1}` a.s. -/
theorem recZ {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π : ℤ → Ω → ℝ}
    (h : ModelZM S σ β κ i r x π) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (t : ℤ) :
    ∀ᵐ ω ∂S.μ, π (t + 1) ω = (lam1 σ β κ)⁻¹ * π t ω +
      (lam1 σ β κ)⁻¹ * (σ * κ) * S.FZ (lam2 σ β κ) i t ω + errZ S π t ω := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  filter_upwards [factoredZ S ha hβ h hia hi hπ t] with ω e
  simp only [errZ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
  have : S.E t (π (t + 1)) ω = (lam1 σ β κ)⁻¹ * (π t ω + σ * κ * S.FZ (lam2 σ β κ) i t ω) := by
    rw [← e]; field_simp
  rw [this]
  ring

/-! ### Uniqueness given the innovations -/

/-- Cochrane (2023), §17.4.1, eq. (5.5) on ℤ: inflation with rates `i` and innovations `d`
(`d_t` the innovation of date `t + 1`), the stable root solved backward over the infinite past,
`π_t = ∑_{j≥0} λ₁^{−j}(λ₁⁻¹σκ F_{t−1−j} + d_{t−1−j})`.
Stochastic ℤ-indexed version of `FullModelTidy.piZ` and `TidyR5InnovEqmMeasure.piM`. -/
noncomputable def piZM (σ β κ : ℝ) (i d : ℤ → Ω → ℝ) (t : ℤ) : Ω → ℝ := fun ω =>
  ∑' j : ℕ, (lam1 σ β κ)⁻¹ ^ j *
    ((lam1 σ β κ)⁻¹ * (σ * κ) * S.FZ (lam2 σ β κ) i (t - 1 - j) ω + d (t - 1 - j) ω)

/-- Cochrane (2023), §17.4.1: the stable root is in `(0, 1)` as a coefficient, `|λ₁⁻¹| < 1`, and
`|λ₂| < 1`.
Restates `FullModel.one_lt_lam1` and `FullModel.lam2_lt_one`. -/
theorem roots_abs {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) :
    |(lam1 σ β κ)⁻¹| < 1 ∧ |lam2 σ β κ| < 1 := by
  have hl1 := one_lt_lam1 ha hβ
  have hl0 : 0 < lam1 σ β κ := one_pos.trans hl1
  refine ⟨?_, ?_⟩
  · rw [abs_of_pos (inv_pos.mpr hl0)]; exact inv_lt_one_of_one_lt₀ hl1
  · rw [abs_of_pos (lam2_pos ha hβ)]; exact lam2_lt_one ha hβ

/-- **Uniqueness on ℤ given the innovations** (Cochrane (2023), §17.4.1, pp. 408–410): every
equilibrium on ℤ with essentially bounded adapted rates and essentially bounded inflation, whose
innovations are `d` a.s., is almost surely `piZM` at every date.
ℤ-indexed version of `FullModelTidy.eq_piZ`. Compare `TidyR5InnovEqmMeasure.eq_piM`. -/
theorem eq_piZM {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i r x π d : ℤ → Ω → ℝ}
    (h : ModelZM S σ β κ i r x π) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hd : ∀ t, errZ S π t =ᵐ[S.μ] d t) :
    ∀ᵐ ω ∂S.μ, ∀ t, π t ω = piZM S σ β κ i d t ω := by
  obtain ⟨hl, hq⟩ := roots_abs ha hβ
  set a := (lam1 σ β κ)⁻¹ with haa
  set F := S.FZ (lam2 σ β κ) i with hFdef
  filter_upwards [ae_all_iff.2 (recZ S ha hβ h hia hi hπ), ae_all_iff.2 hπ,
    ae_all_iff.2 (S.FZ_bdd hq hi), ae_all_iff.2 (fun t => S.abs_E_le (hπ (t + 1)) t),
    ae_all_iff.2 hπ |>.mono fun ω h' t => h' (t + 1), ae_all_iff.2 hd] with
    ω hr hb hF hE hb1 hdd t
  have hw : ∀ s, |a * (σ * κ) * F (s - 1) ω + errZ S π (s - 1) ω| ≤
      |a * (σ * κ)| * (M / (1 - |lam2 σ β κ|)) + (Mπ + Mπ) := fun s => by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF _) (abs_nonneg _)
    · simp only [errZ, Pi.sub_apply]
      refine (abs_sub _ _).trans (add_le_add (hb1 _) (hE _))
  have e := SharedTools.eq_backward_series hl (x := fun s => π s ω)
    (w := fun s => a * (σ * κ) * F (s - 1) ω + errZ S π (s - 1) ω) hb hw
    (fun s => by simp only [add_sub_cancel_right]; rw [hr s]; ring) t
  rw [e]
  refine tsum_congr fun j => ?_
  rw [show t - (j : ℤ) - 1 = t - 1 - j by ring, hdd]

/-! ### Existence -/

/-- Cochrane (2023), §17.4.1: `piZM` satisfies `π_{t+1} = λ₁⁻¹ π_t + λ₁⁻¹σκ F_t + d_t` wherever
`F` and `d` are bounded. -/
theorem piZM_rec {σ β κ KF Md : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i d : ℤ → Ω → ℝ} {ω : Ω}
    (hF : ∀ s, |S.FZ (lam2 σ β κ) i s ω| ≤ KF) (hd : ∀ s, |d s ω| ≤ Md) (t : ℤ) :
    piZM S σ β κ i d (t + 1) ω = (lam1 σ β κ)⁻¹ * piZM S σ β κ i d t ω +
      (lam1 σ β κ)⁻¹ * (σ * κ) * S.FZ (lam2 σ β κ) i t ω + d t ω := by
  obtain ⟨hl, -⟩ := roots_abs ha hβ
  have hw : ∀ s, |(lam1 σ β κ)⁻¹ * (σ * κ) * S.FZ (lam2 σ β κ) i s ω + d s ω| ≤
      |(lam1 σ β κ)⁻¹ * (σ * κ)| * KF + Md := fun s => by
    refine (abs_add_le _ _).trans (add_le_add ?_ (hd s))
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF _) (abs_nonneg _)
  have e := TidyR6ZStaticIS.backward_shift hl
    (f := fun s => (lam1 σ β κ)⁻¹ * (σ * κ) * S.FZ (lam2 σ β κ) i s ω + d s ω) hw t
  simp only [piZM, add_sub_cancel_right]
  rw [e]
  ring

/-- Cochrane (2023), §17.4.1: `piZM` is adapted when `d_t` is known at `t + 1`. -/
theorem piZM_adapted (σ β κ : ℝ) {i d : ℤ → Ω → ℝ}
    (hdm : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (d t)) :
    StronglyAdapted S.𝓕 (piZM S σ β κ i d) := by
  intro t
  have h1 : ∀ j : ℕ, StronglyMeasurable[S.𝓕 t] (fun ω => (lam1 σ β κ)⁻¹ ^ j *
      ((lam1 σ β κ)⁻¹ * (σ * κ) * S.FZ (lam2 σ β κ) i (t - 1 - j) ω + d (t - 1 - j) ω)) :=
    fun j => ((((S.FZ_adapted _ i (t - 1 - j)).mono (S.𝓕.mono (by omega))).const_mul _).add
      ((hdm (t - 1 - j)).mono (S.𝓕.mono (by omega)))).const_mul _
  let _ : MeasurableSpace Ω := S.𝓕 t
  exact StronglyMeasurable.tsum h1

/-- Cochrane (2023), §17.4.1: `piZM` is bounded wherever `F` and `d` are. -/
theorem piZM_bound {σ β κ KF Md : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i d : ℤ → Ω → ℝ} {ω : Ω}
    (hF : ∀ s, |S.FZ (lam2 σ β κ) i s ω| ≤ KF) (hd : ∀ s, |d s ω| ≤ Md) (t : ℤ) :
    |piZM S σ β κ i d t ω| ≤
      (|(lam1 σ β κ)⁻¹ * (σ * κ)| * KF + Md) / (1 - |(lam1 σ β κ)⁻¹|) := by
  obtain ⟨hl, -⟩ := roots_abs ha hβ
  exact TidyR5ExpectationsMeasure.MeasExpectationSystem.abs_tsum_geom_mul_le hl fun j => by
    refine (abs_add_le _ _).trans (add_le_add ?_ (hd _))
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF _) (abs_nonneg _)

/-- **Existence on ℤ under uncertainty** (Cochrane (2023), §17.4.1, Fig. 17.6, pp. 408–410): for
`σκ > 0`, `β > 0`, essentially bounded adapted rates and every essentially bounded martingale
difference sequence `d` (`d_t` known at `t + 1`, `E_t d_t = 0` a.s.), `piZM` is adapted,
essentially bounded, has innovations `d`, satisfies the factored form and, with
`r_t = i_t − E_t π_{t+1}` and `x_t = (π_t − β E_t π_{t+1})/κ`, is an equilibrium on ℤ.
ℤ-indexed version of `TidyR5InnovEqmMeasure.piM_equilibrium`. -/
theorem piZM_equilibrium {σ β κ M Md : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {i d : ℤ → Ω → ℝ}
    (hia : StronglyAdapted S.𝓕 i) (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M)
    (hdm : ∀ t, StronglyMeasurable[S.𝓕 (t + 1)] (d t)) (hd : ∀ t, ∀ᵐ ω ∂S.μ, |d t ω| ≤ Md)
    (hd0 : ∀ t, S.E t (d t) =ᵐ[S.μ] 0) :
    StronglyAdapted S.𝓕 (piZM S σ β κ i d) ∧
      (∃ K, ∀ t, ∀ᵐ ω ∂S.μ, |piZM S σ β κ i d t ω| ≤ K) ∧
      (∀ t, errZ S (piZM S σ β κ i d) t =ᵐ[S.μ] d t) ∧
      (∀ t, lam1 σ β κ • S.E t (piZM S σ β κ i d (t + 1)) =ᵐ[S.μ]
        piZM S σ β κ i d t + (σ * κ) • S.FZ (lam2 σ β κ) i t) ∧
      ModelZM S σ β κ i (fun t => i t - S.E t (piZM S σ β κ i d (t + 1)))
        (fun t => κ⁻¹ • (piZM S σ β κ i d t - β • S.E t (piZM S σ β κ i d (t + 1))))
        (piZM S σ β κ i d) := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  obtain ⟨hl, hq⟩ := roots_abs ha hβ
  set P := piZM S σ β κ i d with hP
  set F := S.FZ (lam2 σ β κ) i with hFdef
  set a := (lam1 σ β κ)⁻¹ with haa
  set KF := M / (1 - |lam2 σ β κ|)
  have had := piZM_adapted S σ β κ (i := i) hdm
  have hall : ∀ᵐ ω ∂S.μ, (∀ s, |F s ω| ≤ KF) ∧ ∀ s, |d s ω| ≤ Md :=
    (ae_all_iff.2 (S.FZ_bdd hq hi)).and (ae_all_iff.2 hd)
  set K := (|a * (σ * κ)| * KF + Md) / (1 - |a|)
  have hbd : ∀ t, ∀ᵐ ω ∂S.μ, |P t ω| ≤ K := fun t =>
    hall.mono fun ω h => piZM_bound S ha hβ h.1 h.2 t
  have hrec : ∀ t, P (t + 1) =ᵐ[S.μ] (a • P t + (a * (σ * κ)) • F t) + d t := fun t =>
    hall.mono fun ω h => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact piZM_rec S ha hβ h.1 h.2 t
  have hPi : ∀ t, Integrable (P t) S.μ := fun t => S.integrable_of_bdd (had t) (hbd t)
  have hdi : ∀ t, Integrable (d t) S.μ := fun t => S.integrable_of_bdd (hdm t) (hd t)
  have hFi : ∀ t, Integrable (F t) S.μ := fun t => S.integrable_E t _
  have hiI : ∀ t, Integrable (i t) S.μ := fun t => S.integrable_of_bdd (hia t) (hi t)
  have hE : ∀ t, S.E t (P (t + 1)) =ᵐ[S.μ] a • P t + (a * (σ * κ)) • F t := by
    intro t
    have hX : StronglyMeasurable[S.𝓕 t] (a • P t + (a * (σ * κ)) • F t) :=
      ((had t).const_smul a).add ((S.FZ_adapted _ i t).const_smul _)
    have hXi : Integrable (a • P t + (a * (σ * κ)) • F t) S.μ :=
      ((hPi t).smul a).add ((hFi t).smul _)
    filter_upwards [S.E_congr (hrec t) t, S.E_add hXi (hdi t) t, hd0 t] with ω e1 e2 e3
    rw [e1, e2, Pi.add_apply, S.E_of_stronglyMeasurable hX hXi, e3, Pi.zero_apply, add_zero]
  have hfac : ∀ t, lam1 σ β κ • S.E t (P (t + 1)) =ᵐ[S.μ] P t + (σ * κ) • F t := by
    intro t
    filter_upwards [hE t] with ω e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e, haa]
    field_simp
  have hinn : ∀ t, errZ S P t =ᵐ[S.μ] d t := by
    intro t
    filter_upwards [hE t, hrec t] with ω e1 e2
    simp only [errZ, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2]
    ring
  have h18 := eq1718Z_of_factored S ha hβ hia hi hPi hfac
  refine ⟨had, ⟨K, hbd⟩, hinn, hfac, fun t => ⟨hiI t, (hiI t).sub (S.integrable_E _ _),
    ((hPi t).sub ((S.integrable_E _ _).smul _)).smul _, hPi t⟩, fun t => ⟨?_, ?_, ?_⟩⟩
  · filter_upwards [h18 t, S.E_smul κ⁻¹ (P (t + 1) - β • S.E (t + 1) (P (t + 1 + 1))) t,
      S.E_sub (hPi (t + 1)) ((S.integrable_E (t + 1) (P (t + 1 + 1))).smul β) t,
      S.E_smul β (S.E (t + 1) (P (t + 1 + 1))) t,
      S.E_tower (Int.le_add_one le_rfl) (P (t + 1 + 1))] with ω e a1 b c d'
    have hk : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e a1 b c ⊢
    rw [a1, b, c, d']
    rw [show t + 2 = t + 1 + 1 by ring] at e
    linear_combination κ⁻¹ * e - (σ * i t ω - σ * S.E t (P (t + 1)) ω) * hk
  · exact Eventually.of_forall fun ω => by simp
  · refine Eventually.of_forall fun ω => ?_
    have hk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination -(P t ω - β * S.E t (P (t + 1)) ω) * hk

/-- Cochrane (2023), §17.4.1, p. 408: in equilibrium, output is determined by inflation,
`x_t = (π_t − β E_t π_{t+1})/κ`, and the real rate by the rate and inflation, a.s. -/
theorem x_r_of_model {σ β κ : ℝ} (hκ : κ ≠ 0) {i r x π : ℤ → Ω → ℝ}
    (h : ModelZM S σ β κ i r x π) (t : ℤ) :
    x t =ᵐ[S.μ] κ⁻¹ • (π t - β • S.E t (π (t + 1))) ∧
      r t =ᵐ[S.μ] i t - S.E t (π (t + 1)) := by
  obtain ⟨-, h2, h3⟩ := h.2 t
  refine ⟨?_, ?_⟩
  · filter_upwards [h3] with ω e
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
    rw [e]
    field_simp
    ring
  · filter_upwards [h2] with ω e
    simp only [Pi.add_apply, Pi.sub_apply] at e ⊢
    linarith

/-- **The bounded equilibrium on ℤ given its innovations is a.s. unique** (Cochrane (2023),
§17.4.1, p. 408, under uncertainty): two equilibria with the same essentially bounded adapted
rates, essentially bounded inflation and the same innovations agree a.s. in inflation, output and
the real rate at every date.
ℤ-indexed version of `TidyR5StochasticPaths.innov_eqm_existsUnique`. -/
theorem eqm_unique_given_innov {σ β κ M Mπ Mπ' : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    {i r x π r' x' π' : ℤ → Ω → ℝ} (h : ModelZM S σ β κ i r x π)
    (h' : ModelZM S σ β κ i r' x' π') (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (hπ' : ∀ t, ∀ᵐ ω ∂S.μ, |π' t ω| ≤ Mπ') (hd : ∀ t, errZ S π' t =ᵐ[S.μ] errZ S π t) :
    ∀ t, π' t =ᵐ[S.μ] π t ∧ x' t =ᵐ[S.μ] x t ∧ r' t =ᵐ[S.μ] r t := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  have hpp : ∀ᵐ ω ∂S.μ, ∀ t, π' t ω = π t ω := by
    filter_upwards [eq_piZM S ha hβ h hia hi hπ (fun t => EventuallyEq.rfl),
      eq_piZM S ha hβ h' hia hi hπ' hd] with ω e e' t
    rw [e, e']
  have hp : ∀ t, π' t =ᵐ[S.μ] π t := fun t => hpp.mono fun ω h => h t
  intro t
  obtain ⟨hx, hr⟩ := x_r_of_model S hκ h t
  obtain ⟨hx', hr'⟩ := x_r_of_model S hκ h' t
  have hEE := S.E_congr (hp (t + 1)) t
  refine ⟨hp t, ?_, ?_⟩
  · filter_upwards [hx, hx', hp t, hEE] with ω e1 e2 e3 e4
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [e1, e2, e3, e4]
  · filter_upwards [hr, hr', hEE] with ω e1 e2 e4
    simp only [Pi.sub_apply] at e1 e2 ⊢
    rw [e1, e2, e4]

/-- Cochrane (2023), Fig. 17.6, p. 410, the link with the ℕ-indexed form: from every date `s`, an
equilibrium on ℤ is a.s. the ℕ-indexed equilibrium `TidyR5InnovEqmMeasure.piM` of the restricted
system started at `π_s` with its own innovations. -/
theorem restrict_eq_piM {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β)
    {i r x π : ℤ → Ω → ℝ} (h : ModelZM S σ β κ i r x π) (hia : StronglyAdapted S.𝓕 i)
    (hi : ∀ t, ∀ᵐ ω ∂S.μ, |i t ω| ≤ M) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) (s : ℤ) (n : ℕ) :
    π (s + n) =ᵐ[S.μ] piM (S.restrict s) σ β κ (fun m => i (s + m)) (π s)
      (fun m => errZ S π (s + m - 1)) n := by
  have h1 := eq_piM (S.restrict s) ha hβ (S.restrict_adapted hia s) (fun m => hi (s + m))
    (p := π s) (δ := fun m => errZ S π (s + m - 1)) (modelZM_restrict S h s)
    (fun m => hπ (s + m)) (by simp only [Nat.cast_zero, add_zero]; exact EventuallyEq.rfl)
    (fun m => by
      have e : s + ((m + 1 : ℕ) : ℤ) = s + m + 1 := by push_cast; ring
      simp only [restrict_E, restrict_μ, e, add_sub_cancel_right]
      exact EventuallyEq.rfl) n
  exact h1

/-! ### Deterministic rate paths -/

/-- Cochrane (2023), eq. (5.5), p. 119: for a deterministic rate path the forward sum is the
perfect-foresight forward sum `FullModelTidy.FZ`, at every state. -/
theorem FZ_det (q : ℝ) (ib : ℤ → ℝ) (t : ℤ) :
    S.FZ q (fun s _ => ib s) t = fun _ => FullModelTidy.FZ q ib t :=
  S.E_const t _

/-- Cochrane (2023), eq. (5.5) on ℤ: the perfect-foresight path is the backward sum
`piZ_t = ∑ λ₁^{−j} λ₁⁻¹σκ F_{t−1−j}` of its factored form.
Compare `FullModelTidy.piZ` and `FullModelTidy.piZ_factor`. -/
theorem piZ_backward {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {ib : ℤ → ℝ}
    (hib : ∀ t, |ib t| ≤ M) (t : ℤ) :
    FullModelTidy.piZ σ β κ ib t = ∑' j : ℕ, (lam1 σ β κ)⁻¹ ^ j *
      ((lam1 σ β κ)⁻¹ * (σ * κ) * FullModelTidy.FZ (lam2 σ β κ) ib (t - 1 - j)) := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  obtain ⟨hl, -⟩ := roots_abs ha hβ
  obtain ⟨Mp, hMp⟩ := FullModelTidy.piZ_bounded ha hβ hib
  have hF := FullModelTidy.FZ_bound (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib
  have hw : ∀ s, |(lam1 σ β κ)⁻¹ * (σ * κ) * FullModelTidy.FZ (lam2 σ β κ) ib (s - 1)| ≤
      |(lam1 σ β κ)⁻¹ * (σ * κ)| * (M / (1 - lam2 σ β κ)) := fun s => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF _) (abs_nonneg _)
  have e := SharedTools.eq_backward_series hl (x := FullModelTidy.piZ σ β κ ib) hMp hw
    (fun s => by
      have f := FullModelTidy.piZ_factor ha hβ hib s
      simp only [add_sub_cancel_right]
      field_simp
      linear_combination f) t
  rw [e]
  refine tsum_congr fun j => ?_
  rw [show t - (j : ℤ) - 1 = t - 1 - j by ring]

/-- **Every bounded equilibrium for a deterministic rate path** (Cochrane (2023), §17.4.1,
pp. 408–409, under uncertainty on ℤ): for a bounded deterministic rate path `ī`, every
essentially bounded equilibrium is a.s., at every date, the perfect-foresight path plus the
backward sum of its innovations, `π_t = piZ(ī)_t + ∑ λ₁^{−j} δ_{t−j}`. -/
theorem det_representation {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {ib : ℤ → ℝ}
    (hib : ∀ t, |ib t| ≤ M) {r x π : ℤ → Ω → ℝ}
    (h : ModelZM S σ β κ (fun t _ => ib t) r x π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) :
    ∀ᵐ ω ∂S.μ, ∀ t, π t ω = FullModelTidy.piZ σ β κ ib t +
      ∑' j : ℕ, (lam1 σ β κ)⁻¹ ^ j * errZ S π (t - 1 - j) ω := by
  obtain ⟨hl, -⟩ := roots_abs ha hβ
  have hia : StronglyAdapted S.𝓕 (fun t (_ : Ω) => ib t) := fun t => stronglyMeasurable_const
  have hi : ∀ t, ∀ᵐ ω ∂S.μ, |(fun t (_ : Ω) => ib t) t ω| ≤ M :=
    fun t => Eventually.of_forall fun _ => hib t
  have hF := FullModelTidy.FZ_bound (lam2_pos ha hβ).le (lam2_lt_one ha hβ) hib
  filter_upwards [eq_piZM S ha hβ h hia hi hπ (fun t => EventuallyEq.rfl),
    ae_all_iff.2 (errZ_bdd S hπ)] with ω e hb t
  rw [e t, piZM, piZ_backward ha hβ hib t]
  simp only [FZ_det]
  have s1 : Summable fun j : ℕ => (lam1 σ β κ)⁻¹ ^ j *
      ((lam1 σ β κ)⁻¹ * (σ * κ) * FullModelTidy.FZ (lam2 σ β κ) ib (t - 1 - j)) :=
    TidyR5ExpectationsMeasure.MeasExpectationSystem.summable_geom_mul hl fun j => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hF _) (abs_nonneg _)
  have s2 : Summable fun j : ℕ => (lam1 σ β κ)⁻¹ ^ j * errZ S π (t - 1 - j) ω :=
    TidyR5ExpectationsMeasure.MeasExpectationSystem.summable_geom_mul hl fun j => hb _
  rw [← s1.tsum_add s2]
  refine tsum_congr fun j => ?_
  ring

/-- Cochrane (2023), §17.4.1 under uncertainty: for a bounded deterministic rate path, an
essentially bounded equilibrium is a.s. the perfect-foresight path at every date iff all its
innovations vanish a.s. -/
theorem det_eq_piZ_iff {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {ib : ℤ → ℝ}
    (hib : ∀ t, |ib t| ≤ M) {r x π : ℤ → Ω → ℝ}
    (h : ModelZM S σ β κ (fun t _ => ib t) r x π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) :
    (∀ t, π t =ᵐ[S.μ] fun _ => FullModelTidy.piZ σ β κ ib t) ↔ ∀ t, errZ S π t =ᵐ[S.μ] 0 := by
  constructor
  · intro hp t
    filter_upwards [hp (t + 1), S.E_congr (hp (t + 1)) t] with ω e1 e2
    simp only [errZ, Pi.sub_apply, Pi.zero_apply]
    rw [e1, e2, S.E_const]
    ring
  · intro he t
    filter_upwards [det_representation S ha hβ hib h hπ, ae_all_iff.2 he] with ω e1 e2
    rw [e1 t]
    have : ∀ j : ℕ, (lam1 σ β κ)⁻¹ ^ j * errZ S π (t - 1 - j) ω = 0 := fun j => by
      rw [e2, Pi.zero_apply, mul_zero]
    rw [tsum_congr this, tsum_zero, add_zero]

/-- Cochrane (2023), §17.4.1, pp. 408–409: for a bounded deterministic rate path, the
perfect-foresight path, with `r_t = ī_t − piZ_{t+1}` and `x_t = (piZ_t − β piZ_{t+1})/κ`, is an
equilibrium on ℤ under **every** filtration (existence).
The existence half of `FullModelTidy.eqmZ_existsUnique`, under every filtration. -/
theorem pf_is_equilibrium {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {ib : ℤ → ℝ}
    (hib : ∀ t, |ib t| ≤ M) :
    ModelZM S σ β κ (fun t _ => ib t)
      (fun t _ => ib t - FullModelTidy.piZ σ β κ ib (t + 1))
      (fun t _ => (FullModelTidy.piZ σ β κ ib t - β * FullModelTidy.piZ σ β κ ib (t + 1)) / κ)
      (fun t _ => FullModelTidy.piZ σ β κ ib t) := by
  have hκ : κ ≠ 0 := by rintro rfl; simp at ha
  have hpf := (FullModelTidy.pfEqmZ_iff_secondZ hκ ib
    (fun t => (FullModelTidy.piZ σ β κ ib t - β * FullModelTidy.piZ σ β κ ib (t + 1)) / κ)
    (FullModelTidy.piZ σ β κ ib)).mpr ⟨fun _ => rfl, FullModelTidy.piZ_second ha hβ hib⟩
  refine ⟨fun t => ⟨integrable_const _, integrable_const _, integrable_const _,
    integrable_const _⟩, fun t => ⟨?_, ?_, ?_⟩⟩ <;>
  refine Eventually.of_forall fun ω => ?_ <;>
  simp only [S.E_const, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · exact (hpf t).1
  · ring
  · exact (hpf t).2

/-- Cochrane (2023), §17.4.1, Fig. 17.5 under uncertainty (expected paths): for a bounded
deterministic rate path, every essentially bounded equilibrium has, a.s.,
`E_s π_{s+j} = piZ_{s+j} + λ₁^{−j}(π_s − piZ_s)`: forecasts return to the perfect-foresight path
at the rate of the stable root.
Compare `TidyR5StochasticPaths.expected_path`. -/
theorem det_expected {σ β κ M Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {ib : ℤ → ℝ}
    (hib : ∀ t, |ib t| ≤ M) {r x π : ℤ → Ω → ℝ}
    (h : ModelZM S σ β κ (fun t _ => ib t) r x π) (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ)
    (s : ℤ) (j : ℕ) :
    ∀ᵐ ω ∂S.μ, S.E s (π (s + j)) ω = FullModelTidy.piZ σ β κ ib (s + j) +
      (lam1 σ β κ)⁻¹ ^ j * (π s ω - FullModelTidy.piZ σ β κ ib s) := by
  have hl0 : lam1 σ β κ ≠ 0 := (one_pos.trans (one_lt_lam1 ha hβ)).ne'
  have hia : StronglyAdapted S.𝓕 (fun t (_ : Ω) => ib t) := fun t => stronglyMeasurable_const
  have hi : ∀ t, ∀ᵐ ω ∂S.μ, |(fun t (_ : Ω) => ib t) t ω| ≤ M :=
    fun t => Eventually.of_forall fun _ => hib t
  have hπi : ∀ t, Integrable (π t) S.μ := fun t => (h.1 t).2.2.2
  -- `π_s` itself is a.s. its own date-`s` forecast
  have hself : ∀ t, S.E t (π t) =ᵐ[S.μ] π t := by
    intro t
    have hf := factoredZ S ha hβ h hia hi hπ t
    have hG : StronglyMeasurable[S.𝓕 t]
        (lam1 σ β κ • S.E t (π (t + 1)) - (σ * κ) • S.FZ (lam2 σ β κ) (fun t _ => ib t) t) :=
      ((S.stronglyMeasurable_E t _).const_smul _).sub ((S.FZ_adapted _ _ t).const_smul _)
    have hGi : Integrable (lam1 σ β κ • S.E t (π (t + 1)) -
        (σ * κ) • S.FZ (lam2 σ β κ) (fun t _ => ib t) t) S.μ :=
      ((S.integrable_E t _).smul _).sub ((S.integrable_E t _).smul _)
    have hπG : π t =ᵐ[S.μ] lam1 σ β κ • S.E t (π (t + 1)) -
        (σ * κ) • S.FZ (lam2 σ β κ) (fun t _ => ib t) t := by
      filter_upwards [hf] with ω e
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      rw [e]
      ring
    filter_upwards [S.E_congr hπG t, hπG] with ω e1 e2
    rw [e1, S.E_of_stronglyMeasurable hG hGi, ← e2]
  induction j with
  | zero =>
    filter_upwards [hself s] with ω e
    simp only [Nat.cast_zero, add_zero, pow_zero, one_mul] at e ⊢
    rw [e]
    ring
  | succ j ih =>
    have hf := factoredZ S ha hβ h hia hi hπ (s + j)
    have hfz := FullModelTidy.piZ_factor ha hβ hib (s + j)
    have hle : s ≤ s + j := by omega
    have hEsum : S.E s ((lam1 σ β κ)⁻¹ • (π (s + j) +
        (σ * κ) • S.FZ (lam2 σ β κ) (fun t _ => ib t) (s + j))) =ᵐ[S.μ]
        (lam1 σ β κ)⁻¹ • (S.E s (π (s + j)) +
          (σ * κ) • fun _ => FullModelTidy.FZ (lam2 σ β κ) ib (s + j)) := by
      rw [FZ_det]
      filter_upwards [S.E_smul (lam1 σ β κ)⁻¹ (π (s + j) +
          (σ * κ) • fun _ => FullModelTidy.FZ (lam2 σ β κ) ib (s + j)) s,
        S.E_add (hπi (s + j)) ((integrable_const _).smul (σ * κ)) s] with ω e1 e2
      rw [e1, Pi.smul_apply, e2, Pi.add_apply, Pi.smul_apply, Pi.add_apply]
      congr 2
      rw [show ((σ * κ) • fun _ : Ω => FullModelTidy.FZ (lam2 σ β κ) ib (s + j)) =
        fun _ => (σ * κ) * FullModelTidy.FZ (lam2 σ β κ) ib (s + j) from rfl, S.E_const]
    have hnext : S.E (s + j) (π (s + j + 1)) =ᵐ[S.μ] (lam1 σ β κ)⁻¹ • (π (s + j) +
        (σ * κ) • S.FZ (lam2 σ β κ) (fun t _ => ib t) (s + j)) := by
      filter_upwards [hf] with ω e
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      rw [← e]
      field_simp
    filter_upwards [S.E_tower hle (π (s + j + 1)), S.E_congr hnext s, hEsum, ih] with
      ω e1 e2 e3 e4
    have ec : s + ((j + 1 : ℕ) : ℤ) = s + j + 1 := by push_cast; ring
    rw [ec, ← e1, e2, e3]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e4]
    have hz : FullModelTidy.piZ σ β κ ib (s + j + 1) = (lam1 σ β κ)⁻¹ *
        (FullModelTidy.piZ σ β κ ib (s + j) +
          σ * κ * FullModelTidy.FZ (lam2 σ β κ) ib (s + j)) := by
      rw [← hfz]; field_simp
    rw [hz, pow_succ]
    ring

/-! ### No news: when the perfect-foresight path is the only equilibrium -/

/-- Cochrane (2023), §17.4.1 (what uniqueness on ℤ requires under uncertainty): the filtration
carries **no news** — every essentially bounded variable known at `t + 1` is a.s. its date-`t`
forecast. -/
def NoNews : Prop :=
  ∀ t (η : Ω → ℝ), StronglyMeasurable[S.𝓕 (t + 1)] η → (∃ C, ∀ᵐ ω ∂S.μ, |η ω| ≤ C) →
    η =ᵐ[S.μ] S.E t η

/-- **Uniqueness on ℤ under uncertainty holds iff there is no news** (Cochrane (2023), §17.4.1,
pp. 408–409; the perfect-foresight claim `FullModelTidy.secondZ_existsUnique` /
`FullModel.zPath_existsUnique` read under uncertainty): for a bounded deterministic rate path,
every essentially bounded equilibrium is a.s. the perfect-foresight path at every date iff the
filtration carries no news. -/
theorem det_unique_iff_noNews {σ β κ M : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) {ib : ℤ → ℝ}
    (hib : ∀ t, |ib t| ≤ M) :
    (∀ (r x π : ℤ → Ω → ℝ), ModelZM S σ β κ (fun t _ => ib t) r x π →
      (∃ Mπ, ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) →
        ∀ t, π t =ᵐ[S.μ] fun _ => FullModelTidy.piZ σ β κ ib t) ↔ NoNews S := by
  have hia : StronglyAdapted S.𝓕 (fun t (_ : Ω) => ib t) := fun t => stronglyMeasurable_const
  have hi : ∀ t, ∀ᵐ ω ∂S.μ, |(fun t (_ : Ω) => ib t) t ω| ≤ M :=
    fun t => Eventually.of_forall fun _ => hib t
  constructor
  · intro hu t η hη ⟨C, hC⟩
    by_contra hne
    set d : ℤ → Ω → ℝ := fun s => if s = t then η - S.E t η else 0 with hd
    have hdm : ∀ s, StronglyMeasurable[S.𝓕 (s + 1)] (d s) := by
      intro s
      by_cases hs : s = t
      · subst hs
        simp only [hd, ↓reduceIte]
        exact hη.sub ((S.stronglyMeasurable_E s η).mono (S.𝓕.mono (Int.le_add_one le_rfl)))
      · simp only [hd, hs, ↓reduceIte]
        exact stronglyMeasurable_const
    have hdb : ∀ s, ∀ᵐ ω ∂S.μ, |d s ω| ≤ C + C := by
      intro s
      by_cases hs : s = t
      · filter_upwards [hC, S.abs_E_le hC t] with ω e1 e2
        simp only [hd, hs, ↓reduceIte, Pi.sub_apply]
        exact (abs_sub _ _).trans (add_le_add e1 e2)
      · filter_upwards [hC] with ω e1
        simp only [hd, hs, ↓reduceIte, Pi.zero_apply, abs_zero]
        linarith [(abs_nonneg (η ω)).trans e1]
    have hηi : Integrable η S.μ := S.integrable_of_bdd hη hC
    have hd0 : ∀ s, S.E s (d s) =ᵐ[S.μ] 0 := by
      intro s
      by_cases hs : s = t
      · subst hs
        simp only [hd, ↓reduceIte]
        filter_upwards [S.E_sub hηi (S.integrable_E s η) s] with ω e
        rw [e, Pi.sub_apply, S.E_E_self, sub_self, Pi.zero_apply]
      · simp only [hd, hs, ↓reduceIte]
        exact Eventually.of_forall fun ω => by
          rw [show (0 : Ω → ℝ) = fun _ => 0 from rfl, S.E_const]
    obtain ⟨-, ⟨K, hK⟩, hinn, -, hmod⟩ := piZM_equilibrium S ha hβ hia hi hdm hdb hd0
    have hp := hu _ _ _ hmod ⟨K, hK⟩
    have h0 := (det_eq_piZ_iff S ha hβ hib hmod hK).mp hp t
    apply hne
    filter_upwards [hinn t, h0] with ω e1 e2
    have : d t ω = 0 := by rw [← e1, e2, Pi.zero_apply]
    simp only [hd, ↓reduceIte, Pi.sub_apply] at this
    linarith
  · intro hn r x π h ⟨Mπ, hπ⟩
    refine (det_eq_piZ_iff S ha hβ hib h hπ).mpr fun t => ?_
    -- the innovation is a.s. a bounded variable known at `t + 1` with zero forecast
    have hf := factoredZ S ha hβ h hia hi hπ (t + 1)
    set G : Ω → ℝ := lam1 σ β κ • S.E (t + 1) (π (t + 1 + 1)) -
      (σ * κ) • S.FZ (lam2 σ β κ) (fun t _ => ib t) (t + 1) with hG
    have hGm : StronglyMeasurable[S.𝓕 (t + 1)] G :=
      ((S.stronglyMeasurable_E _ _).const_smul _).sub ((S.FZ_adapted _ _ _).const_smul _)
    have hπG : π (t + 1) =ᵐ[S.μ] G := by
      filter_upwards [hf] with ω e
      simp only [hG, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e ⊢
      rw [e]
      ring
    have hGb : ∀ᵐ ω ∂S.μ, |G ω| ≤ Mπ := by
      filter_upwards [hπ (t + 1), hπG] with ω e1 e2
      rw [← e2]; exact e1
    have hGE := hn t G hGm ⟨Mπ, hGb⟩
    filter_upwards [hπG, S.E_congr hπG t, hGE] with ω e1 e2 e3
    simp only [errZ, Pi.sub_apply, Pi.zero_apply]
    rw [e1, e2, ← e3, sub_self]

/-! ### Figure 17.5: the rise anticipated from the infinite past -/

/-- Cochrane (2023), Fig. 17.5, p. 409, under uncertainty on ℤ: for the permanent rise
`i_t = 1{t ≥ T}` known forever, every essentially bounded equilibrium is a.s.
`π_t = zPath_t + ∑ λ₁^{−j} δ_{t−j}`. -/
theorem zPath_representation {σ β κ Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ)
    {r x π : ℤ → Ω → ℝ} (h : ModelZM S σ β κ (fun t _ => FullModel.stepZ T t) r x π)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) :
    ∀ᵐ ω ∂S.μ, ∀ t, π t ω = FullModel.zPath σ β κ T t +
      ∑' j : ℕ, (lam1 σ β κ)⁻¹ ^ j * errZ S π (t - 1 - j) ω := by
  have hs : ∀ t, |FullModel.stepZ T t| ≤ 1 := fun t => by
    unfold FullModel.stepZ; split_ifs <;> simp
  rw [FullModelTidy.zPath_eq_piZ ha hβ T]
  exact det_representation S ha hβ hs h hπ

/-- Cochrane (2023), Fig. 17.5, p. 409, under uncertainty: a bounded equilibrium for the
anticipated rise is a.s. `zPath` at every date iff all its innovations vanish. -/
theorem zPath_iff_no_innov {σ β κ Mπ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ)
    {r x π : ℤ → Ω → ℝ} (h : ModelZM S σ β κ (fun t _ => FullModel.stepZ T t) r x π)
    (hπ : ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) :
    (∀ t, π t =ᵐ[S.μ] fun _ => FullModel.zPath σ β κ T t) ↔ ∀ t, errZ S π t =ᵐ[S.μ] 0 := by
  have hs : ∀ t, |FullModel.stepZ T t| ≤ 1 := fun t => by
    unfold FullModel.stepZ; split_ifs <;> simp
  rw [FullModelTidy.zPath_eq_piZ ha hβ T]
  exact det_eq_piZ_iff S ha hβ hs h hπ

/-- Cochrane (2023), Fig. 17.5, p. 409: `zPath`, with its output and real rate, is an equilibrium
on ℤ under every filtration.
The existence half of `FullModel.zPath_existsUnique`, under every filtration. -/
theorem zPath_is_equilibrium {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    ModelZM S σ β κ (fun t _ => FullModel.stepZ T t)
      (fun t _ => FullModel.stepZ T t - FullModel.zPath σ β κ T (t + 1))
      (fun t _ => (FullModel.zPath σ β κ T t - β * FullModel.zPath σ β κ T (t + 1)) / κ)
      (fun t _ => FullModel.zPath σ β κ T t) := by
  have hs : ∀ t, |FullModel.stepZ T t| ≤ 1 := fun t => by
    unfold FullModel.stepZ; split_ifs <;> simp
  rw [FullModelTidy.zPath_eq_piZ ha hβ T]
  exact pf_is_equilibrium S ha hβ hs

/-- **`FullModel.zPath_existsUnique` under uncertainty, corrected** (Cochrane (2023), Fig. 17.5,
p. 409): `zPath` is the only essentially bounded equilibrium for the rise anticipated from the
infinite past (a.s., at every date) iff the filtration carries no news. -/
theorem zPath_unique_iff_noNews {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    (∀ (r x π : ℤ → Ω → ℝ), ModelZM S σ β κ (fun t _ => FullModel.stepZ T t) r x π →
      (∃ Mπ, ∀ t, ∀ᵐ ω ∂S.μ, |π t ω| ≤ Mπ) →
        ∀ t, π t =ᵐ[S.μ] fun _ => FullModel.zPath σ β κ T t) ↔ NoNews S := by
  have hs : ∀ t, |FullModel.stepZ T t| ≤ 1 := fun t => by
    unfold FullModel.stepZ; split_ifs <;> simp
  rw [FullModelTidy.zPath_eq_piZ ha hβ T]
  exact det_unique_iff_noNews S ha hβ hs

/-! ### The coin: a genuine counterexample -/

/-- Cochrane (2023), Fig. 17.5 (a counterexample space): the fair coin on `Bool`.
Not `TidyR5ExpectationsMeasureIID.coinMeasure`, which lives on `ℝ`. -/
noncomputable def coinMeasure : Measure Bool :=
  (1 / 2 : ENNReal) • Measure.dirac true + (1 / 2 : ENNReal) • Measure.dirac false

/-- Cochrane (2023), Fig. 17.5 (the counterexample space): the coin is a probability measure. -/
theorem coinMeasure_univ : coinMeasure Set.univ = 1 := by
  simp [coinMeasure, ENNReal.inv_two_add_inv_two]

/-- Cochrane (2023), Fig. 17.5 (the counterexample space): each face has positive mass. -/
theorem coinMeasure_singleton (b : Bool) : coinMeasure {b} ≠ 0 := by
  cases b <;> simp [coinMeasure]

/-- Cochrane (2023), Fig. 17.5 (a counterexample filtration): nothing is known up to date 0, the
coin is revealed at date 1. -/
def coinFiltration : Filtration ℤ (inferInstance : MeasurableSpace Bool) where
  seq := fun t => if t ≤ 0 then ⊥ else inferInstance
  mono' := fun s t hst => by
    beta_reduce
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact bot_le
    · omega
    · exact le_rfl
  le' := fun t => by
    split_ifs
    · exact bot_le
    · exact le_rfl

/-- Cochrane (2023), Fig. 17.5: the ℤ-indexed coin system.
A different object from `ExpectationsFiniteTree.coinSystem`. -/
noncomputable def coinSystem : ZMeasExpectationSystem Bool :=
  ⟨⟨coinMeasure, ⟨coinMeasure_univ⟩⟩, coinFiltration⟩

/-- Cochrane (2023), Fig. 17.5: the coin system carries news — the coin `±1` is known at date 1
but is not a.s. its date-0 forecast. -/
theorem coin_news : ¬ NoNews coinSystem := by
  intro hn
  set η : Bool → ℝ := fun b => if b then 1 else -1 with hη
  have hm : StronglyMeasurable[coinSystem.𝓕 (0 + 1)] η := by
    have e : coinSystem.𝓕 (0 + 1) = (inferInstance : MeasurableSpace Bool) := by
      change (if (0 + 1 : ℤ) ≤ 0 then ⊥ else (inferInstance : MeasurableSpace Bool)) = _
      simp
    rw [e]
    exact Measurable.stronglyMeasurable (Measurable.of_discrete)
  have h := hn 0 η hm ⟨1, Eventually.of_forall fun b => by cases b <;> simp [hη]⟩
  have hbot : coinSystem.𝓕 0 = ⊥ := by
    change (if (0 : ℤ) ≤ 0 then ⊥ else (inferInstance : MeasurableSpace Bool)) = _
    simp
  obtain ⟨c, hc⟩ := (stronglyMeasurable_bot_iff (f := coinSystem.E 0 η)).mp
    (hbot ▸ coinSystem.stronglyMeasurable_E 0 η)
  rw [hc] at h
  have hb : ∀ b : Bool, η b = c := by
    intro b
    by_contra hne
    have hsub : ({b} : Set Bool) ⊆ {ω | η ω ≠ c} := fun ω hω => by
      rw [Set.mem_singleton_iff] at hω; subst hω; exact hne
    have h0 := measure_mono_null hsub (ae_iff.mp h)
    exact coinMeasure_singleton b h0
  have h1 := hb true
  have h2 := hb false
  simp only [hη] at h1 h2
  norm_num at h1 h2
  linarith

/-- **`FullModel.zPath_existsUnique` is false under uncertainty** (Cochrane (2023), Fig. 17.5,
p. 409): on the coin system there is an essentially bounded equilibrium on ℤ for the rise
anticipated from the infinite past which is not a.s. `zPath` (the unexpected inflation of the
coin, propagated forward at `λ₁^{−j}`). -/
theorem zPath_not_unique_coin {σ β κ : ℝ} (ha : 0 < σ * κ) (hβ : 0 < β) (T : ℤ) :
    ∃ r x π : ℤ → Bool → ℝ, ModelZM coinSystem σ β κ (fun t _ => FullModel.stepZ T t) r x π ∧
      (∃ Mπ, ∀ t, ∀ᵐ ω ∂coinSystem.μ, |π t ω| ≤ Mπ) ∧
      ¬ ∀ t, π t =ᵐ[coinSystem.μ] fun _ => FullModel.zPath σ β κ T t := by
  by_contra hall
  push Not at hall
  exact coin_news ((zPath_unique_iff_noNews coinSystem ha hβ T).mp
    fun r x π h hb => hall r x π h hb)

end Cochrane.KeynesianStickyPrices.TidyR6ZFullModel
